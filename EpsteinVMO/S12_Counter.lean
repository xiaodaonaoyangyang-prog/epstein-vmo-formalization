import EpsteinVMO.Defs
import EpsteinVMO.S02_Prelim
import EpsteinVMO.S10_Sharp
import EpsteinVMO.S11_HalfPlane
import TakhtajanTeo.Ch2.S1_UnivalentFunctions

/-!
# §12 Counterexamples and limits of the method

Source: `sec12-counter.tex`.

## Section-local conventions

* `ℂ̂ = OnePoint ℂ`; Möbius maps are the action of `GL (Fin 2) ℂ` on `OnePoint ℂ`
  (`Mathlib.Topology.Compactification.OnePoint.ProjectiveLine`).
* The Ahlfors–Weill point `p♮ ∈ ℂ̂` is `awPoint Ω p`.
* The spacing `δ(p, w) = d(B_p, B*_w)` uses `hdistSets` of `S02_Prelim`; `d(q, S)` is `hdistSet`.
* `Pφ = φ''/φ'` is `TakhtajanTeo.Ch2.preSchwarzian`.
* The surface `S ≅ ℍ²` of §12.2 is modelled by `𝔻` with the Poincaré metric `4|dz|²/(1-|z|²)²`,
  `o = 0`; its Laplacian is `((1-|z|²)²/4) Δ`.
* Examples are existence statements with the claimed properties.
* Example `ex:nonrect` (listed in the assignment) is in `sec09-ambient.tex:988` and is already
  stated as `ex_nonrect` in `S09_Ambient` (w4); `ex:power` is in §7 (w3, with its `SQS` claim in
  `S11_HalfPlane.ex_power_sqs`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-! ## Ahlfors–Weill points -/

/-- Definition 12.1 `def:aw-point`, `sec12-counter.tex:39`: the other endpoint `p♮` of the normal
geodesic `γ_p`: `p♮ = p + 1/A(p)` if `A(p) ≠ 0`, `p♮ = ∞` if `A(p) = 0`. -/
def awPoint (Ω : Set ℂ) (p : ℂ) : OnePoint ℂ :=
  if logDensityDz Ω p = 0 then OnePoint.infty else ((p + 1 / logDensityDz Ω p : ℂ) : OnePoint ℂ)

/-- The right half-plane `ℍ_r = {Re z > 0}`. -/
def rightHalf : Set ℂ := {z | 0 < z.re}

/-- The image `M(Ω) ⊆ ℂ` of `Ω` under a Möbius map `M` with `M(Ω) ⊆ ℂ`. -/
def mobImage (M : GL (Fin 2) ℂ) (Ω : Set ℂ) : Set ℂ :=
  {z : ℂ | ∃ p ∈ Ω, M • (p : OnePoint ℂ) = (z : OnePoint ℂ)}

/-- The osculating Möbius map (12.?) `eq:osculating`:
`M_ζ(z) = φ(ζ) + φ'(ζ)(z - ζ)/(1 - ½ Pφ(ζ)(z - ζ))`. -/
def oscMob (φ : ℂ → ℂ) (ζ z : ℂ) : ℂ :=
  φ ζ + deriv φ ζ * (z - ζ) / (1 - (1 / 2) * TakhtajanTeo.Ch2.preSchwarzian φ ζ * (z - ζ))

open scoped Classical in
/-- (12.1) `eq:aw-natural`, `sec12-counter.tex:51`: `M(p)♮ = M(p♮)` for a Möbius map `M` with
`M(Ω) ⊆ ℂ`.  (Stated for every domain conformally equivalent to `𝔻`; the paper's setting is a
Jordan domain.) -/
theorem eq_aw_natural {Ω : Set ℂ} (hΩ : ∃ φ : ℂ → ℂ, IsConformalOnto φ unitDisc Ω) (M : GL (Fin 2) ℂ)
    (hM : ∀ p ∈ Ω, M • (p : OnePoint ℂ) ≠ OnePoint.infty) {p : ℂ} (hp : p ∈ Ω) {z₀ : ℂ}
    (hz₀ : M • (p : OnePoint ℂ) = (z₀ : OnePoint ℂ)) :
    awPoint (mobImage M Ω) z₀ = M • awPoint Ω p := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
    have h := M.det_ne_zero
    rwa [Matrix.det_fin_two] at h
  have hden : ∀ w ∈ Ω, M 1 0 * w + M 1 1 ≠ 0 := by
    intro w hw h
    have h' := hM w hw
    rw [OnePoint.smul_some_eq_ite, if_pos h] at h'
    exact h' rfl
  have himg : mobImage M Ω =
      (fun v => (M 0 0 * v + M 0 1) / (M 1 0 * v + M 1 1)) '' Ω := by
    ext z
    constructor
    · rintro ⟨q, hq, hqz⟩
      rw [OnePoint.smul_some_eq_ite, if_neg (hden q hq)] at hqz
      exact ⟨q, hq, OnePoint.coe_injective hqz⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, by rw [OnePoint.smul_some_eq_ite, if_neg (hden q hq)]⟩
  have hz0 : z₀ = (M 0 0 * p + M 0 1) / (M 1 0 * p + M 1 1) := by
    rw [OnePoint.smul_some_eq_ite, if_neg (hden p hp)] at hz₀
    exact (OnePoint.coe_injective hz₀).symm
  have hN := s02_mobius_natural_A hΩ hdet hden hp
  rw [← himg, ← hz0] at hN
  have hg := hden p hp
  have hT1 : (M 0 0 * M 1 1 - M 0 1 * M 1 0) / (M 1 0 * p + M 1 1) ^ 2 ≠ 0 :=
    div_ne_zero hdet (pow_ne_zero 2 hg)
  have hA'e : logDensityDz (mobImage M Ω) z₀ =
      (logDensityDz Ω p + M 1 0 / (M 1 0 * p + M 1 1)) /
        ((M 0 0 * M 1 1 - M 0 1 * M 1 0) / (M 1 0 * p + M 1 1) ^ 2) := by
    rw [eq_div_iff hT1, hN]
  unfold awPoint
  by_cases hA : logDensityDz Ω p = 0
  · rw [if_pos hA, OnePoint.smul_infty_eq_ite]
    by_cases hc : M 1 0 = 0
    · have h0 : logDensityDz (mobImage M Ω) z₀ = 0 := by
        rw [hA'e, hA, hc]
        simp
      rw [if_pos h0, if_pos hc]
    · have h0 : logDensityDz (mobImage M Ω) z₀ ≠ 0 := by
        rw [hA'e, hA, zero_add]
        exact div_ne_zero (div_ne_zero hc hg) hT1
      rw [if_neg h0, if_neg hc]
      congr 1
      rw [hA'e, hA, zero_add, hz0]
      generalize hgg : M 1 0 * p + M 1 1 = g at hg ⊢
      field_simp
      rw [← hgg]
      ring
  · rw [if_neg hA, OnePoint.smul_some_eq_ite]
    have hK : logDensityDz Ω p * (M 1 0 * p + M 1 1) + M 1 0 =
        logDensityDz Ω p * (M 1 0 * (p + 1 / logDensityDz Ω p) + M 1 1) := by
      field_simp
      ring
    have hsum : logDensityDz Ω p + M 1 0 / (M 1 0 * p + M 1 1) =
        (logDensityDz Ω p * (M 1 0 * p + M 1 1) + M 1 0) / (M 1 0 * p + M 1 1) := by
      field_simp
    by_cases hq : M 1 0 * (p + 1 / logDensityDz Ω p) + M 1 1 = 0
    · have h0 : logDensityDz (mobImage M Ω) z₀ = 0 := by
        rw [hA'e, hsum, hK, hq, mul_zero, zero_div, zero_div]
      rw [if_pos h0, if_pos hq]
    · have hK0 : logDensityDz Ω p * (M 1 0 * p + M 1 1) + M 1 0 ≠ 0 := by
        rw [hK]
        exact mul_ne_zero hA hq
      have h0 : logDensityDz (mobImage M Ω) z₀ ≠ 0 := by
        rw [hA'e, hsum]
        exact div_ne_zero (div_ne_zero hK0 hg) hT1
      have hq' : M 1 0 * (p + 1 / logDensityDz Ω p) + M 1 1 =
          (logDensityDz Ω p * (M 1 0 * p + M 1 1) + M 1 0) / logDensityDz Ω p := by
        rw [hK]
        field_simp
      rw [if_neg h0, if_neg hq]
      congr 1
      rw [hA'e, hsum, hz0, hq']
      generalize hgg : M 1 0 * p + M 1 1 = g at hg hK0 ⊢
      generalize hKK : logDensityDz Ω p * g + M 1 0 = K at hK0 ⊢
      field_simp
      rw [← hKK, ← hgg]
      ring

/-- Helper for `lem_aw_point_jet`: the `2`-jet at `ζ` of `b + A(z-ζ)/(1-c(z-ζ))` is `(b, A, 2Ac)`. -/
theorem mob_jet (b A c ζ : ℂ) :
    (fun z => b + A * (z - ζ) / (1 - c * (z - ζ))) ζ = b ∧
      deriv (fun z => b + A * (z - ζ) / (1 - c * (z - ζ))) ζ = A ∧
      deriv (deriv (fun z => b + A * (z - ζ) / (1 - c * (z - ζ)))) ζ = 2 * A * c := by
  have hg : ∀ z, HasDerivAt (fun z => 1 - c * (z - ζ)) (-c) z := fun z => by
    simpa using (((hasDerivAt_id z).sub_const ζ).const_mul c).const_sub 1
  have hD : ∀ z, 1 - c * (z - ζ) ≠ 0 →
      HasDerivAt (fun z => b + A * (z - ζ) / (1 - c * (z - ζ))) (A / (1 - c * (z - ζ)) ^ 2) z := by
    intro z hz
    have hf : HasDerivAt (fun z => A * (z - ζ)) A z := by
      simpa using ((hasDerivAt_id z).sub_const ζ).const_mul A
    convert (hf.div (hg z) hz).const_add b using 1
    field_simp
    ring
  have h1 : (1 : ℂ) - c * (ζ - ζ) ≠ 0 := by simp
  have hev : ∀ᶠ z in 𝓝 ζ, 1 - c * (z - ζ) ≠ 0 :=
    (by fun_prop : Continuous fun z : ℂ => 1 - c * (z - ζ)).continuousAt.eventually_ne h1
  have hderiv : deriv (fun z => b + A * (z - ζ) / (1 - c * (z - ζ))) =ᶠ[𝓝 ζ]
      fun z => A / (1 - c * (z - ζ)) ^ 2 := hev.mono fun z hz => (hD z hz).deriv
  refine ⟨by simp, by simpa using (hD ζ h1).deriv, ?_⟩
  rw [hderiv.deriv_eq]
  have h2 : HasDerivAt (fun z => A / (1 - c * (z - ζ)) ^ 2) _ ζ :=
    (hasDerivAt_const ζ A).div ((hg ζ).pow 2) (pow_ne_zero 2 h1)
  rw [h2.deriv]
  simp
  ring

/-- Lemma 12.2 `lem:aw-point`, `sec12-counter.tex:68`, first claim: `M_ζ` has the `2`-jet of `φ`
at `ζ` (for `φ` holomorphic near `ζ` with `φ'(ζ) ≠ 0`). -/
theorem lem_aw_point_jet {φ : ℂ → ℂ} {ζ : ℂ} (hφ : AnalyticAt ℂ φ ζ) (h0 : deriv φ ζ ≠ 0) :
    oscMob φ ζ ζ = φ ζ ∧ deriv (oscMob φ ζ) ζ = deriv φ ζ ∧
      deriv (deriv (oscMob φ ζ)) ζ = deriv (deriv φ) ζ := by
  obtain ⟨e0, e1, e2⟩ := mob_jet (φ ζ) (deriv φ ζ) ((1 / 2) * TakhtajanTeo.Ch2.preSchwarzian φ ζ) ζ
  refine ⟨e0, e1, ?_⟩
  change deriv (deriv (fun z => φ ζ + deriv φ ζ * (z - ζ) /
    (1 - (1 / 2) * TakhtajanTeo.Ch2.preSchwarzian φ ζ * (z - ζ)))) ζ = _
  rw [e2, TakhtajanTeo.Ch2.preSchwarzian]
  field_simp

/-- Helper for `eq_A_transform_uhp`/`_rhp`: pulling back `eq:A-transform` along a Möbius map
`M : 𝔻 → B` onto `B`. -/
theorem s12_A_mobius_pullback {Ω B : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ B Ω)
    (hB : IsOpen B) {α β γ δ : ℂ} (hdet : α * δ - β * γ ≠ 0)
    (hden : ∀ v ∈ unitDisc, γ * v + δ ≠ 0)
    (hMB : (fun v => (α * v + β) / (γ * v + δ)) '' unitDisc = B) {w : ℂ} (hw : w ∈ unitDisc) :
    logDensityDz Ω (φ ((α * w + β) / (γ * w + δ))) * deriv φ ((α * w + β) / (γ * w + δ)) *
        ((α * δ - β * γ) / (γ * w + δ) ^ 2) =
      conj w / ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) -
        (deriv (deriv φ) ((α * w + β) / (γ * w + δ)) * ((α * δ - β * γ) / (γ * w + δ) ^ 2) /
          (2 * deriv φ ((α * w + β) / (γ * w + δ))) - γ / (γ * w + δ)) := by
  set M : ℂ → ℂ := fun v => (α * v + β) / (γ * v + δ) with hMdef
  rw [show (α * w + β) / (γ * w + δ) = M w from rfl]
  have hMm : MapsTo M unitDisc B := fun v hv => hMB ▸ mem_image_of_mem M hv
  have hMd : DifferentiableOn ℂ M unitDisc := fun v hv =>
    ((hasDerivAt_mobius (a := α) (b := β) (hden v hv)).differentiableAt).differentiableWithinAt
  have hMi : InjOn M unitDisc := by
    intro v₁ h₁ v₂ h₂ he
    have hd₁ := hden v₁ h₁
    have hd₂ := hden v₂ h₂
    simp only [hMdef] at he
    rw [div_eq_div_iff hd₁ hd₂] at he
    have : (α * δ - β * γ) * (v₁ - v₂) = 0 := by linear_combination he
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hdet
    · exact sub_eq_zero.mp h
  have hF : IsConformalOnto (φ ∘ M) unitDisc Ω :=
    ⟨hφ.1.comp hMd hMm, hφ.2.1.comp hMi hMm, by rw [Set.image_comp, hMB, hφ.2.2]⟩
  have hI := s02_logDensityDz_mul_deriv hF hw
  have hd := hden w hw
  have hMw : M w ∈ B := hMm hw
  have hφA : AnalyticAt ℂ φ (M w) := hφ.1.analyticAt (hB.mem_nhds hMw)
  have hφ' : deriv φ (M w) ≠ 0 := deriv_ne_zero_of_injOn hB hφ.1 hφ.2.1 hMw
  have hT1 : (α * δ - β * γ) / (γ * w + δ) ^ 2 ≠ 0 := div_ne_zero hdet (pow_ne_zero 2 hd)
  have hloc : deriv (φ ∘ M) =ᶠ[𝓝 w]
      fun v => deriv φ (M v) * ((α * δ - β * γ) / (γ * v + δ) ^ 2) := by
    filter_upwards [isOpen_ball.mem_nhds hw] with v hv
    have hφv : DifferentiableAt ℂ φ (M v) := hφ.1.differentiableAt (hB.mem_nhds (hMm hv))
    exact (hφv.hasDerivAt.comp v (hasDerivAt_mobius (a := α) (b := β) (hden v hv))).deriv
  have h1 : deriv (φ ∘ M) w = deriv φ (M w) * ((α * δ - β * γ) / (γ * w + δ) ^ 2) :=
    hloc.self_of_nhds
  have hl : HasDerivAt (fun v => γ * v + δ) γ w := by
    simpa using ((hasDerivAt_id w).const_mul γ).add_const δ
  have hg : HasDerivAt (fun v => (γ * v + δ) ^ 2) (2 * (γ * w + δ) * γ) w := by
    convert hl.mul hl using 1 <;> (try funext v) <;> (try simp only [Pi.mul_apply]) <;> ring
  have hT2 : HasDerivAt (fun v => (α * δ - β * γ) / (γ * v + δ) ^ 2)
      ((0 * (γ * w + δ) ^ 2 - (α * δ - β * γ) * (2 * (γ * w + δ) * γ)) / ((γ * w + δ) ^ 2) ^ 2)
      w :=
    (hasDerivAt_const w (α * δ - β * γ)).div hg (pow_ne_zero 2 hd)
  have hprod : HasDerivAt (fun v => deriv φ (M v) * ((α * δ - β * γ) / (γ * v + δ) ^ 2))
      (deriv (deriv φ) (M w) * ((α * δ - β * γ) / (γ * w + δ) ^ 2) *
          ((α * δ - β * γ) / (γ * w + δ) ^ 2) +
        deriv φ (M w) * ((0 * (γ * w + δ) ^ 2 - (α * δ - β * γ) * (2 * (γ * w + δ) * γ)) /
          ((γ * w + δ) ^ 2) ^ 2)) w :=
    (hφA.deriv.differentiableAt.hasDerivAt.comp w
      (hasDerivAt_mobius (a := α) (b := β) hd)).mul hT2
  have h2 := hprod.deriv
  rw [← hloc.deriv_eq] at h2
  rw [h1, h2] at hI
  change logDensityDz Ω (φ (M w)) * _ = _ at hI
  rw [mul_assoc, hI]
  clear_value M
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hrc : ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    exact_mod_cast this.ne'
  field_simp
  ring

/-- Helper: the Cayley preimage `(z - i)/(z + i) ∈ 𝔻` of `z ∈ ℍ`. -/
theorem s12_uhp_pre {z : ℂ} (hz : z ∈ upperHalf) :
    (z - I) / (z + I) ∈ unitDisc ∧
      (I * ((z - I) / (z + I)) + I) / ((-1 : ℂ) * ((z - I) / (z + I)) + 1) = z := by
  have hy : 0 < z.im := hz
  have hzI : z + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  refine ⟨?_, ?_⟩
  · refine mem_ball_zero_iff.mpr ?_
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hzI),
      ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp
    nlinarith
  · have h1 : (-1 : ℂ) * ((z - I) / (z + I)) + 1 = 2 * I / (z + I) := by
      field_simp
      ring
    rw [h1, div_eq_iff (div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hzI)]
    field_simp
    ring

/-- Helper: the preimage `(z - 1)/(z + 1) ∈ 𝔻` of `z ∈ ℍ_r`. -/
theorem s12_rhp_pre {z : ℂ} (hz : z ∈ rightHalf) :
    (z - 1) / (z + 1) ∈ unitDisc ∧
      ((1 : ℂ) * ((z - 1) / (z + 1)) + 1) / ((-1 : ℂ) * ((z - 1) / (z + 1)) + 1) = z := by
  have hx : 0 < z.re := hz
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  refine ⟨?_, ?_⟩
  · refine mem_ball_zero_iff.mpr ?_
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hz1),
      ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp
    nlinarith
  · have h1 : (-1 : ℂ) * ((z - 1) / (z + 1)) + 1 = 2 / (z + 1) := by
      field_simp
      ring
    rw [h1, div_eq_iff (div_ne_zero two_ne_zero hz1)]
    field_simp
    ring

/-- Helper: the Cayley-type map `v ↦ (v + 1)/(1 - v)` has positive real part on `𝔻`. -/
theorem s12_rhp_re (a : ℂ) :
    (((1 : ℂ) * a + 1) / ((-1 : ℂ) * a + 1)).re = (1 - normSq a) / normSq (1 - a) := by
  rw [Complex.div_re]
  simp [Complex.normSq_apply]
  ring

/-- (12.?) `eq:A-transform`, `sec12-counter.tex:99`, `B = 𝔻`:
`A(φ(z)) φ'(z) = A_𝔻(z) - φ''(z)/(2φ'(z))` with `A_𝔻(z) = z̄/(1-|z|²)`. -/
theorem eq_A_transform_disk {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) :
    logDensityDz Ω (φ z) * deriv φ z =
      conj z / ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) - deriv (deriv φ) z / (2 * deriv φ z) := by
  exact s02_logDensityDz_mul_deriv hφ hz

/-- (12.?) `eq:A-transform`, `sec12-counter.tex:99`, `B = ℍ`: `A_ℍ(z) = i/(2 Im z)`. -/
theorem eq_A_transform_uhp {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ upperHalf Ω) {z : ℂ}
    (hz : z ∈ upperHalf) :
    logDensityDz Ω (φ z) * deriv φ z = I / (2 * z.im) - deriv (deriv φ) z / (2 * deriv φ z) := by
  have hy : 0 < z.im := hz
  have hzI : z + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hcI : conj z - I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hcz : conj z - z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hyc : (z.im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hden : ∀ v ∈ unitDisc, (-1 : ℂ) * v + 1 ≠ 0 := by
    intro v hv h
    have : v = 1 := by linear_combination -h
    have hv1 := mem_ball_zero_iff.mp hv
    rw [this, norm_one] at hv1
    exact lt_irrefl _ hv1
  have hMB : (fun v => (I * v + I) / ((-1 : ℂ) * v + 1)) '' unitDisc = upperHalf := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      have : (I * v + I) / ((-1 : ℂ) * v + 1) = I * (1 + v) / (1 - v) := by
        congr 1 <;> ring
      show 0 < ((I * v + I) / ((-1 : ℂ) * v + 1)).im
      rw [this]
      exact s02_cayley_im_pos hv
    · intro hu
      obtain ⟨h1, h2⟩ := s12_uhp_pre hu
      exact ⟨_, h1, h2⟩
  have hBo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hdet : I * 1 - I * (-1) ≠ 0 := by
    rw [show I * 1 - I * (-1) = 2 * I by ring]
    exact mul_ne_zero two_ne_zero I_ne_zero
  obtain ⟨hw, hMw⟩ := s12_uhp_pre hz
  have E := s12_A_mobius_pullback hφ hBo hdet hden hMB hw
  rw [hMw] at E
  set w := (z - I) / (z + I) with hwdef
  have hc : conj w = (conj z + I) / (conj z - I) := by
    rw [hwdef, map_div₀, map_sub, map_add, conj_I]
    ring
  have hr : ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) = 2 * I * (conj z - z) / ((z + I) * (conj z - I)) := by
    rw [show ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) = 1 - w * conj w by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring, hc, hwdef]
    field_simp
    ring
  have h1w : (-1 : ℂ) * w + 1 = 2 * I / (z + I) := by
    rw [hwdef]
    field_simp
    ring
  have hT1 : (I * 1 - I * (-1)) / ((-1 : ℂ) * w + 1) ^ 2 ≠ 0 :=
    div_ne_zero hdet (pow_ne_zero 2 (hden w hw))
  have key : conj w / ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) + -1 / ((-1 : ℂ) * w + 1) =
      I / (2 * z.im) * ((I * 1 - I * (-1)) / ((-1 : ℂ) * w + 1) ^ 2) := by
    have hzc : z - conj z ≠ 0 := fun h => hcz (by linear_combination -h)
    have hI3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
    have hI4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, I_sq]; norm_num
    rw [hr, hc, h1w, Complex.im_eq_sub_conj]
    field_simp
    ring_nf
    simp only [I_sq, hI3, hI4]
    ring
  apply mul_right_cancel₀ hT1
  rw [E]
  linear_combination key

/-- (12.?) `eq:A-transform`, `sec12-counter.tex:99`, `B = ℍ_r`: `A_{ℍ_r}(z) = -1/(2 Re z)`. -/
theorem eq_A_transform_rhp {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ rightHalf Ω) {z : ℂ}
    (hz : z ∈ rightHalf) :
    logDensityDz Ω (φ z) * deriv φ z = -1 / (2 * z.re) - deriv (deriv φ) z / (2 * deriv φ z) := by
  have hx : 0 < z.re := hz
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hc1 : conj z + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcz : z + conj z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hxc : (z.re : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hden : ∀ v ∈ unitDisc, (-1 : ℂ) * v + 1 ≠ 0 := by
    intro v hv h
    have : v = 1 := by linear_combination -h
    have hv1 := mem_ball_zero_iff.mp hv
    rw [this, norm_one] at hv1
    exact lt_irrefl _ hv1
  have hMB : (fun v => ((1 : ℂ) * v + 1) / ((-1 : ℂ) * v + 1)) '' unitDisc = rightHalf := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      show 0 < (((1 : ℂ) * v + 1) / ((-1 : ℂ) * v + 1)).re
      rw [s12_rhp_re]
      have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
      have hn : normSq v < 1 := normSq_lt_one_iff.mpr hv1
      have hA : (1 : ℂ) - v ≠ 0 := by
        intro h
        have : v = 1 := (sub_eq_zero.mp h).symm
        rw [this, norm_one] at hv1
        exact lt_irrefl _ hv1
      exact div_pos (by linarith) (normSq_pos.mpr hA)
    · intro hu
      obtain ⟨h1, h2⟩ := s12_rhp_pre hu
      exact ⟨_, h1, h2⟩
  have hBo : IsOpen rightHalf := isOpen_lt continuous_const Complex.continuous_re
  have hdet : (1 : ℂ) * 1 - 1 * (-1) ≠ 0 := by norm_num
  obtain ⟨hw, hMw⟩ := s12_rhp_pre hz
  have E := s12_A_mobius_pullback hφ hBo hdet hden hMB hw
  rw [hMw] at E
  set w := (z - 1) / (z + 1) with hwdef
  have hc : conj w = (conj z - 1) / (conj z + 1) := by
    rw [hwdef, map_div₀, map_sub, map_add, map_one]
  have hr : ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) = 2 * (z + conj z) / ((z + 1) * (conj z + 1)) := by
    rw [show ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) = 1 - w * conj w by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring, hc, hwdef]
    field_simp
    ring
  have h1w : (-1 : ℂ) * w + 1 = 2 / (z + 1) := by
    rw [hwdef]
    field_simp
    ring
  have hT1 : ((1 : ℂ) * 1 - 1 * (-1)) / ((-1 : ℂ) * w + 1) ^ 2 ≠ 0 :=
    div_ne_zero hdet (pow_ne_zero 2 (hden w hw))
  have key : conj w / ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) + -1 / ((-1 : ℂ) * w + 1) =
      -1 / (2 * z.re) * (((1 : ℂ) * 1 - 1 * (-1)) / ((-1 : ℂ) * w + 1) ^ 2) := by
    rw [hr, hc, h1w, Complex.re_eq_add_conj]
    field_simp
    ring
  apply mul_right_cancel₀ hT1
  rw [E]
  linear_combination key

/-- Helper: `p♮` from `A(p) φ₁ = 1/e - P/2`. -/
theorem s12_awPoint_cases {Ω : Set ℂ} {p φ1 e P : ℂ} (hφ1 : φ1 ≠ 0) (he : e ≠ 0)
    (hA : logDensityDz Ω p * φ1 = 1 / e - P / 2) :
    (1 - (1 / 2) * P * e ≠ 0 →
      awPoint Ω p = ((p + φ1 * e / (1 - (1 / 2) * P * e) : ℂ) : OnePoint ℂ)) ∧
    (1 - (1 / 2) * P * e = 0 → awPoint Ω p = OnePoint.infty) := by
  have hA' : logDensityDz Ω p * φ1 = (1 - (1 / 2) * P * e) / e := by
    rw [hA]
    field_simp
  constructor
  · intro hD
    have hA0 : logDensityDz Ω p ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hA'
      exact div_ne_zero hD he hA'.symm
    have hAe : logDensityDz Ω p = (1 - (1 / 2) * P * e) / e / φ1 := by
      rw [eq_div_iff hφ1, hA']
    unfold awPoint
    rw [if_neg hA0, hAe]
    congr 2
    field_simp
  · intro hD
    have h0 : logDensityDz Ω p = 0 := by
      rw [hD, zero_div] at hA'
      exact (mul_eq_zero.mp hA').resolve_right hφ1
    unfold awPoint
    rw [if_pos h0]

/-- Helper: `p♮` from `A(p) φ₁ = -P/2` (the case `ζ♮ = ∞`). -/
theorem s12_awPoint_cases0 {Ω : Set ℂ} {p φ1 P : ℂ} (hφ1 : φ1 ≠ 0)
    (hA : logDensityDz Ω p * φ1 = -(P / 2)) :
    (P ≠ 0 → awPoint Ω p = ((p - φ1 / ((1 / 2) * P) : ℂ) : OnePoint ℂ)) ∧
    (P = 0 → awPoint Ω p = OnePoint.infty) := by
  constructor
  · intro hP
    have hA0 : logDensityDz Ω p ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hA
      exact hP (by linear_combination 2 * hA)
    have hAe : logDensityDz Ω p = -(P / 2) / φ1 := by
      rw [eq_div_iff hφ1, hA]
    unfold awPoint
    rw [if_neg hA0, hAe]
    congr 2
    field_simp
    ring
  · intro hP
    have h0 : logDensityDz Ω p = 0 := by
      rw [hP, zero_div, neg_zero] at hA
      exact (mul_eq_zero.mp hA).resolve_right hφ1
    unfold awPoint
    rw [if_pos h0]

/-- Lemma 12.2 `lem:aw-point`, `sec12-counter.tex:68`, `B = 𝔻`: `p♮ = M_ζ(ζ♮)`, `ζ♮ = 1/ζ̄`
(with `0♮ = ∞`).  For `ζ ≠ 0`: (12.?) `eq:aw-point` when the denominator does not vanish, `∞`
otherwise.  For `ζ = 0`: `p♮ = M_0(∞) = φ(0) - φ'(0)/c`, `c = ½ Pφ(0)`, if `c ≠ 0`, else `∞`. -/
theorem lem_aw_point_disk {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc Ω) {ζ : ℂ}
    (hζ : ζ ∈ unitDisc) :
    (ζ ≠ 0 → 1 - (1 / 2) * TakhtajanTeo.Ch2.preSchwarzian φ ζ * ((conj ζ)⁻¹ - ζ) ≠ 0 →
      awPoint Ω (φ ζ) = (oscMob φ ζ (conj ζ)⁻¹ : OnePoint ℂ)) ∧
    (ζ ≠ 0 → 1 - (1 / 2) * TakhtajanTeo.Ch2.preSchwarzian φ ζ * ((conj ζ)⁻¹ - ζ) = 0 →
      awPoint Ω (φ ζ) = OnePoint.infty) ∧
    (ζ = 0 → TakhtajanTeo.Ch2.preSchwarzian φ 0 ≠ 0 →
      awPoint Ω (φ 0) = ((φ 0 - deriv φ 0 / ((1 / 2) * TakhtajanTeo.Ch2.preSchwarzian φ 0) : ℂ) :
        OnePoint ℂ)) ∧
    (ζ = 0 → TakhtajanTeo.Ch2.preSchwarzian φ 0 = 0 → awPoint Ω (φ 0) = OnePoint.infty) := by
  have hφ' : deriv φ ζ ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hφ.1 hφ.2.1 hζ
  have E := eq_A_transform_disk hφ hζ
  have hz1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have hr : (0 : ℝ) < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hrc : ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) = 1 - ζ * conj ζ := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hr0 : (1 : ℂ) - ζ * conj ζ ≠ 0 := by
    rw [← hrc]
    exact_mod_cast hr.ne'
  have H : ζ ≠ 0 →
      (1 - (1 / 2) * TakhtajanTeo.Ch2.preSchwarzian φ ζ * ((conj ζ)⁻¹ - ζ) ≠ 0 →
        awPoint Ω (φ ζ) = (oscMob φ ζ (conj ζ)⁻¹ : OnePoint ℂ)) ∧
      (1 - (1 / 2) * TakhtajanTeo.Ch2.preSchwarzian φ ζ * ((conj ζ)⁻¹ - ζ) = 0 →
        awPoint Ω (φ ζ) = OnePoint.infty) := by
    intro h0
    have hc0 : conj ζ ≠ 0 := (map_ne_zero _).mpr h0
    have he : (conj ζ)⁻¹ - ζ = (1 - ζ * conj ζ) / conj ζ := by
      field_simp
    have he0 : (conj ζ)⁻¹ - ζ ≠ 0 := by
      rw [he]
      exact div_ne_zero hr0 hc0
    have hA : logDensityDz Ω (φ ζ) * deriv φ ζ =
        1 / ((conj ζ)⁻¹ - ζ) - TakhtajanTeo.Ch2.preSchwarzian φ ζ / 2 := by
      rw [E, he, hrc, one_div_div]
      unfold TakhtajanTeo.Ch2.preSchwarzian
      ring
    unfold oscMob
    exact s12_awPoint_cases hφ' he0 hA
  refine ⟨fun h0 => (H h0).1, fun h0 => (H h0).2, fun h0 => ?_, fun h0 => ?_⟩
  all_goals
    subst h0
    have hA : logDensityDz Ω (φ 0) * deriv φ 0 = -(TakhtajanTeo.Ch2.preSchwarzian φ 0 / 2) := by
      rw [E, map_zero, zero_div, zero_sub]
      unfold TakhtajanTeo.Ch2.preSchwarzian
      ring
  · exact (s12_awPoint_cases0 hφ' hA).1
  · exact (s12_awPoint_cases0 hφ' hA).2

/-- Lemma 12.2 `lem:aw-point`, `sec12-counter.tex:68`, `B = ℍ`, `ζ♮ = ζ̄`. -/
theorem lem_aw_point_uhp {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ upperHalf Ω) {ζ : ℂ}
    (hζ : ζ ∈ upperHalf) :
    (1 - (1 / 2) * TakhtajanTeo.Ch2.preSchwarzian φ ζ * (conj ζ - ζ) ≠ 0 →
      awPoint Ω (φ ζ) = (oscMob φ ζ (conj ζ) : OnePoint ℂ)) ∧
    (1 - (1 / 2) * TakhtajanTeo.Ch2.preSchwarzian φ ζ * (conj ζ - ζ) = 0 →
      awPoint Ω (φ ζ) = OnePoint.infty) := by
  have hy : 0 < ζ.im := hζ
  have hBo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hφ' : deriv φ ζ ≠ 0 := deriv_ne_zero_of_injOn hBo hφ.1 hφ.2.1 hζ
  have E := eq_A_transform_uhp hφ hζ
  have hyc : (ζ.im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hcz : conj ζ - ζ = -2 * I * ζ.im := by
    rw [Complex.im_eq_sub_conj]
    field_simp
    ring
  have he0 : conj ζ - ζ ≠ 0 := by
    rw [hcz]
    exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hyc
  have hinv : 1 / (conj ζ - ζ) = I / (2 * ζ.im) := by
    rw [hcz, div_eq_div_iff (by rw [← hcz]; exact he0) (mul_ne_zero two_ne_zero hyc)]
    linear_combination (2 * (ζ.im : ℂ)) * I_sq
  have hA : logDensityDz Ω (φ ζ) * deriv φ ζ =
      1 / (conj ζ - ζ) - TakhtajanTeo.Ch2.preSchwarzian φ ζ / 2 := by
    rw [E, hinv]
    unfold TakhtajanTeo.Ch2.preSchwarzian
    ring
  unfold oscMob
  exact s12_awPoint_cases hφ' he0 hA

/-- Lemma 12.2 `lem:aw-point`, `sec12-counter.tex:68`, `B = ℍ_r`, `ζ♮ = -ζ̄`. -/
theorem lem_aw_point_rhp {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ rightHalf Ω) {ζ : ℂ}
    (hζ : ζ ∈ rightHalf) :
    (1 - (1 / 2) * TakhtajanTeo.Ch2.preSchwarzian φ ζ * (-conj ζ - ζ) ≠ 0 →
      awPoint Ω (φ ζ) = (oscMob φ ζ (-conj ζ) : OnePoint ℂ)) ∧
    (1 - (1 / 2) * TakhtajanTeo.Ch2.preSchwarzian φ ζ * (-conj ζ - ζ) = 0 →
      awPoint Ω (φ ζ) = OnePoint.infty) := by
  have hx : 0 < ζ.re := hζ
  have hBo : IsOpen rightHalf := isOpen_lt continuous_const Complex.continuous_re
  have hφ' : deriv φ ζ ≠ 0 := deriv_ne_zero_of_injOn hBo hφ.1 hφ.2.1 hζ
  have E := eq_A_transform_rhp hφ hζ
  have hxc : (ζ.re : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hcz : -conj ζ - ζ = -(2 * ζ.re) := by
    rw [Complex.re_eq_add_conj]
    ring
  have he0 : -conj ζ - ζ ≠ 0 := by
    rw [hcz]
    exact neg_ne_zero.mpr (mul_ne_zero two_ne_zero hxc)
  have hinv : 1 / (-conj ζ - ζ) = -1 / (2 * ζ.re) := by
    rw [hcz]
    field_simp
  have hA : logDensityDz Ω (φ ζ) * deriv φ ζ =
      1 / (-conj ζ - ζ) - TakhtajanTeo.Ch2.preSchwarzian φ ζ / 2 := by
    rw [E, hinv]
    unfold TakhtajanTeo.Ch2.preSchwarzian
    ring
  unfold oscMob
  exact s12_awPoint_cases hφ' he0 hA

/-! ## Horoball spacing -/

/-- `δ(p, w) = d(B_p, B*_w)`, the distance between the horoballs at `p ∈ Ω` and `w ∈ Ωs`. -/
def horoSpacing (Ω Ωs : Set ℂ) (p w : ℂ) : ℝ := hdistSets (horoball Ω p) (horoball Ωs w)

/-- Lemma 12.3(a) `lem:spacing`, (12.?) `eq:spacing`, `sec12-counter.tex:153`: for a Jordan curve
through `∞` that is not a circle, `δ(p, w) = log(|p - w|² λ(p) λ*(w)/4) > 0`. -/
theorem lem_spacing_a {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) (hline : ¬ IsLinePair Ω Ωs)
    {p w : ℂ} (hp : p ∈ Ω) (hw : w ∈ Ωs) :
    horoSpacing Ω Ωs p w =
        Real.log (‖p - w‖ ^ 2 * poincareDensity Ω p * poincareDensity Ωs w / 4) ∧
      0 < horoSpacing Ω Ωs p w := by
  obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at hΓ hp
  obtain ⟨gt, hg, hg0⟩ := s02_riemannMap_at (s02_jordanPair_symm hΓ) hw
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hc := (prop_separation_c hΓ hf hg h0 h0).2.1
  have hlf := eq_lambda_f hf h0
  have hlg := eq_lambda_f hg h0
  rw [hf0] at hc hlf
  rw [hg0] at hc hlg
  have hpos := ((prop_separation_b hΓ hline).1 p hp w hw).2
  refine ⟨?_, hpos⟩
  unfold horoSpacing
  rw [hc]
  congr 1
  have hdf : ‖deriv f 0‖ ≠ 0 := norm_ne_zero_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 h0)
  have hdg : ‖deriv gt 0‖ ≠ 0 := norm_ne_zero_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 h0)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    div_one, mul_one] at hlf hlg ⊢
  have e1 : poincareDensity Ω p = 2 / ‖deriv f 0‖ := by field_simp; linarith
  have e2 : poincareDensity Ωs w = 2 / ‖deriv gt 0‖ := by field_simp; linarith
  rw [e1, e2]
  field_simp
  ring

/-- Helper (B1) for Lemma 12.3(b): along the normal geodesic `γ_p` from `p` to `p♮ = p'`,
`Φ*_{E(p,τ)}(p') = e^{δ(p,p') - τ}` (direct from the `normalGeod` formula and (12.?) `eq:spacing`). -/
theorem s12_sb_phi {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) (hline : ¬ IsLinePair Ω Ωs)
    {p p' : ℂ} (hp : p ∈ Ω) (hp' : p' ∈ Ωs) (haw : awPoint Ω p = (p' : OnePoint ℂ)) (τ : ℝ) :
    horoPhi Ωs (normalGeod Ω p τ) p' = Real.exp (horoSpacing Ω Ωs p p' - τ) := by
  have hΩ := s02_jordanPair_riemannMap hΓ
  have hΩs := s02_jordanPair_riemannMap (s02_jordanPair_symm hΓ)
  have hl := s02_poincareDensity_pos hΩ hp
  have hls := s02_poincareDensity_pos hΩs hp'
  have hA0 : logDensityDz Ω p ≠ 0 := by
    intro h
    unfold awPoint at haw
    rw [if_pos h] at haw
    exact OnePoint.infty_ne_coe _ haw
  have hpp : p' = p + 1 / logDensityDz Ω p := by
    unfold awPoint at haw
    rw [if_neg hA0] at haw
    exact (OnePoint.coe_injective haw).symm
  rw [(lem_spacing_a hΓ hline hp hp').1]
  unfold horoPhi normalGeod
  dsimp only
  rw [hpp]
  set A := logDensityDz Ω p with hA
  set lam := poincareDensity Ω p with hlam
  set lams := poincareDensity Ωs (p + 1 / A) with hlams
  have hls' : 0 < lams := by rw [hlams, ← hpp]; exact hls
  set a := ‖A‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hA0
  set E := Real.exp (-τ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set h := lam * E / 2 with hh
  have hh0 : 0 < h := by positivity
  have hinv : 1 / A = conj A * (((a ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [one_div, Complex.inv_def, Complex.normSq_eq_norm_sq]
  have hdiff : p + conj A / ((a ^ 2 + h ^ 2 : ℝ) : ℂ) - (p + 1 / A) =
      conj A * (((a ^ 2 + h ^ 2)⁻¹ - (a ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [hinv]
    push_cast
    ring
  have hn : ‖p + conj A / ((a ^ 2 + h ^ 2 : ℝ) : ℂ) - (p + 1 / A)‖ =
      a * ((a ^ 2)⁻¹ - (a ^ 2 + h ^ 2)⁻¹) := by
    rw [hdiff, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by
        have : (a ^ 2 + h ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
        linarith)]
    ring
  have hpw : ‖p - (p + 1 / A)‖ = a⁻¹ := by
    rw [show p - (p + 1 / A) = -(1 / A) by ring, norm_neg, norm_div, norm_one, one_div]
  rw [hn, hpw, Real.exp_sub, Real.exp_log (by positivity), div_eq_mul_inv (b := Real.exp τ),
    ← Real.exp_neg, ← hE]
  have hlE : lam * E = 2 * h := by rw [hh]; ring
  have ha2 : a ^ 2 ≠ 0 := by positivity
  have hD : a ^ 2 + h ^ 2 ≠ 0 := by positivity
  field_simp
  linear_combination (-2 * lams * h * (a ^ 2 + h ^ 2)) * hlE

/-- Lemma 12.3(b) `lem:spacing`, `sec12-counter.tex:157`: if `p♮ ∈ Ωs`, then
`E(p, τ) ∈ B*_{p♮} ⇔ τ ≥ δ(p, p♮)`, `d(X(p), B*_{p♮}) = δ(p, p♮)`,
`γ_p ∩ 𝒩 ⊆ {E(p, τ) : 0 < τ < δ(p, p♮)}` and `d(X(p), U*) ≤ δ(p, p♮)`. -/
theorem lem_spacing_b {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) (hline : ¬ IsLinePair Ω Ωs)
    {p p' : ℂ} (hp : p ∈ Ω) (hp' : p' ∈ Ωs) (haw : awPoint Ω p = (p' : OnePoint ℂ)) :
    (∀ τ : ℝ, normalGeod Ω p τ ∈ horoball Ωs p' ↔ horoSpacing Ω Ωs p p' ≤ τ) ∧
      hdistSet (epstein Ω p) (horoball Ωs p') = horoSpacing Ω Ωs p p' ∧
      gap Ω Ωs ∩ range (normalGeod Ω p) ⊆ normalGeod Ω p '' Ioo 0 (horoSpacing Ω Ωs p p') ∧
      hdistSet (epstein Ω p) (horoUnion Ωs) ≤ horoSpacing Ω Ωs p p' := by
  have hΩ := s02_jordanPair_riemannMap hΓ
  have hΩs := s02_jordanPair_riemannMap (s02_jordanPair_symm hΓ)
  have hl := s02_poincareDensity_pos hΩ hp
  have hδ := (lem_spacing_a hΓ hline hp hp').2
  have hE : ∀ τ : ℝ, normalGeod Ω p τ ∈ UHS := s02_normalGeod_pos Ω p hl
  have h1 : ∀ τ : ℝ, normalGeod Ω p τ ∈ horoball Ωs p' ↔ horoSpacing Ω Ωs p p' ≤ τ := by
    intro τ
    show (normalGeod Ω p τ ∈ UHS ∧ horoPhi Ωs (normalGeod Ω p τ) p' ≤ 1) ↔ _
    rw [s12_sb_phi hΓ hline hp hp' haw τ, Real.exp_le_one_iff, sub_nonpos]
    exact ⟨fun h => h.2, fun h => ⟨hE τ, h⟩⟩
  have h2 : hdistSet (epstein Ω p) (horoball Ωs p') = horoSpacing Ω Ωs p p' := by
    rw [← s02_normalGeod_zero Ω p hl]
    have hnot : normalGeod Ω p 0 ∉ horoball Ωs p' := fun h => by
      have := (h1 0).1 h
      linarith
    rw [(lem_busemann_nearest hΩs hp' (hE 0) hnot).1, s12_sb_phi hΓ hline hp hp' haw 0, sub_zero,
      Real.log_exp]
  refine ⟨h1, h2, ?_, ?_⟩
  · rintro q ⟨⟨-, hq⟩, τ, rfl⟩
    refine ⟨τ, ⟨?_, ?_⟩, rfl⟩
    · by_contra hτ
      push_neg at hτ
      refine hq (Or.inl (mem_iUnion₂.mpr ⟨p, hp, hE τ, ?_⟩))
      rw [s02_horoPhi_normalGeod Ω p hl τ]
      exact Real.exp_le_one_iff.mpr hτ
    · by_contra hτ
      push_neg at hτ
      exact hq (Or.inr (mem_iUnion₂.mpr ⟨p', hp', (h1 τ).2 hτ⟩))
  · rw [← h2]
    have hX : epstein Ω p ∈ UHS := s02_normalGeod_zero Ω p hl ▸ hE 0
    refine csInf_le_csInf ⟨0, ?_⟩ ⟨_, mem_image_of_mem _ ((h1 _).2 le_rfl)⟩
      (image_mono (subset_biUnion_of_mem (u := fun w => horoball Ωs w) hp'))
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨w, -, hqw⟩ := mem_iUnion₂.mp hq
    have h2' : 0 < q.2 := hqw.1
    have h2X : 0 < (epstein Ω p).2 := hX
    unfold hdist coshDist
    refine Real.arcosh_nonneg ?_
    have : 0 ≤ (‖(epstein Ω p).1 - q.1‖ ^ 2 + ((epstein Ω p).2 - q.2) ^ 2) /
      (2 * (epstein Ω p).2 * q.2) := by positivity
    linarith

/-! ## A sector -/

/-- The sector `Ω = {r e^{iφ} : r > 0, 0 < φ < 9π/5}` of Proposition `prop:sector`. -/
def sectorΩ : Set ℂ :=
  (fun q : ℝ × ℝ => (q.1 : ℂ) * exp ((q.2 : ℂ) * I)) '' (Ioi 0 ×ˢ Ioo 0 (9 * π / 5))

/-- The complementary sector `Ωs = {r e^{iφ} : r > 0, -π/5 < φ < 0}`. -/
def sectorΩs : Set ℂ :=
  (fun q : ℝ × ℝ => (q.1 : ℂ) * exp ((q.2 : ℂ) * I)) '' (Ioi 0 ×ˢ Ioo (-(π / 5)) 0)

/-- The curvature integral `𝓘(p) = ∫_Ω k_p² s² dâ`. -/
def curvKernelInt (Ω : Set ℂ) (p : ℂ) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (intrKernel Ω p w ^ 2) ∂curvMass Ω

/-- Helper: `hpPowerExt α (r e^{iψ}) = r^α e^{i hpPowerAngle α ψ}` for `r > 0`, `ψ ∈ [0, 2π)`. -/
theorem s12_sec_eval {α r ψ : ℝ} (hr : 0 < r) (h0 : 0 ≤ ψ) (h2 : ψ < 2 * π) :
    hpPowerExt α ((r : ℂ) * exp ((ψ : ℂ) * I)) =
      ((r ^ α : ℝ) : ℂ) * exp ((hpPowerAngle α ψ : ℂ) * I) := by
  have hn : ‖(r : ℂ) * exp ((ψ : ℂ) * I)‖ = r := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
  unfold hpPowerExt
  rw [hn, s11_pow_angle_of hr h0 h2]

/-- Helper: `Im (r e^{iψ}) = r sin ψ`. -/
theorem s12_sec_polar_im (r ψ : ℝ) : ((r : ℂ) * exp ((ψ : ℂ) * I)).im = r * Real.sin ψ := by
  rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- Helper: `Im z = |z| sin (hpAngle z)`. -/
theorem s12_sec_im (z : ℂ) : z.im = ‖z‖ * Real.sin (hpAngle z) := by
  conv_lhs => rw [← s11_pow_polar z]
  exact s12_sec_polar_im _ _

/-- Helper: the sector pair is not a line pair (`Ω` is not convex: `±i ∈ Ω`, `0 ∉ Ω`). -/
theorem s12_sec_not_line : ¬ IsLinePair sectorΩ sectorΩs := by
  rintro ⟨a, b, -, hΩ, -⟩
  have hpi := Real.pi_pos
  set u : ℂ := exp (((π / 2 : ℝ) : ℂ) * I) with hu
  have h1 : ((1 : ℝ) : ℂ) * u ∈ sectorΩ := ⟨(1, π / 2), ⟨mem_Ioi.mpr one_pos, by linarith, by linarith⟩, rfl⟩
  have h2 : ((1 : ℝ) : ℂ) * exp (((3 * π / 2 : ℝ) : ℂ) * I) ∈ sectorΩ :=
    ⟨(1, 3 * π / 2), ⟨mem_Ioi.mpr one_pos, by linarith, by linarith⟩, rfl⟩
  have he : exp (((3 * π / 2 : ℝ) : ℂ) * I) = -u := by
    rw [show ((3 * π / 2 : ℝ) : ℂ) * I = ((π / 2 : ℝ) : ℂ) * I + π * I by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have h0 : (0 : ℂ) ∈ sectorΩ := by
    rw [he] at h2
    rw [hΩ] at h1 h2 ⊢
    simp only [mem_setOf_eq, ofReal_one, one_mul, mul_zero, Complex.zero_im, zero_add, Complex.add_im, mul_neg,
      Complex.neg_im] at h1 h2 ⊢
    linarith
  obtain ⟨⟨r, φ⟩, ⟨hr, -⟩, h⟩ := h0
  exact mul_ne_zero (ofReal_ne_zero.mpr (show (0 : ℝ) < r from hr).ne') (exp_ne_zero _) h

/-- Proposition 12.4(a) `prop:sector`, `sec12-counter.tex:240`: `Γ = ∂Ω ∪ {∞}` is a
`9`-quasicircle; the map `T = hpPowerExt (9/5)` is `9`-quasiconformal, `T(ℍ) = Ω`,
`T(𝕃) = Ωs`. -/
theorem prop_sector_a :
    IsKQC (hpPowerExt (9 / 5)) univ 9 ∧ hpPowerExt (9 / 5) '' univ = univ ∧
      hpPowerExt (9 / 5) '' upperHalf = sectorΩ ∧ hpPowerExt (9 / 5) '' lowerHalf = sectorΩs ∧
      IsKQuasiPair sectorΩ sectorΩs 9 := by
  have hpi := Real.pi_pos
  obtain ⟨hK, hU, -, -⟩ := rem_hp_infinity_iii (α := 9 / 5) (by norm_num) (by norm_num)
  rw [show (9 / 5 : ℝ) / (2 - 9 / 5) = 9 by norm_num] at hK
  have hup : hpPowerExt (9 / 5) '' upperHalf = sectorΩ := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have him : 0 < z.im := hz
      have hz0 : z ≠ 0 := fun h => by rw [h, zero_im] at him; exact lt_irrefl _ him
      have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      obtain ⟨h0, h2⟩ := s11_pow_angle_mem z
      rw [s12_sec_im] at him
      have hs : 0 < Real.sin (hpAngle z) := by
        by_contra h
        push_neg at h
        nlinarith [mul_nonneg hr.le (neg_nonneg.mpr h)]
      have hlt : hpAngle z < π := by
        by_contra hge
        push_neg at hge
        have h' : 0 ≤ Real.sin (hpAngle z - π) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
        rw [Real.sin_sub_pi] at h'
        linarith
      have hpos : 0 < hpAngle z := by
        rcases h0.lt_or_eq with h | h
        · exact h
        · rw [← h, Real.sin_zero] at hs
          exact absurd hs (lt_irrefl _)
      refine ⟨(‖z‖ ^ (9 / 5 : ℝ), 9 / 5 * hpAngle z),
        ⟨Real.rpow_pos_of_pos hr _, by linarith, by linarith⟩, ?_⟩
      dsimp only
      unfold hpPowerExt hpPowerAngle
      rw [if_pos hlt.le]
    · rintro ⟨⟨s, φ⟩, ⟨hs, hφ⟩, rfl⟩
      have hs' : 0 < s := hs
      have hφ0 : 0 < φ := hφ.1
      have hφ1 : φ < 9 * π / 5 := hφ.2
      have hr : 0 < s ^ (9 / 5 : ℝ)⁻¹ := Real.rpow_pos_of_pos hs' _
      refine ⟨((s ^ (9 / 5 : ℝ)⁻¹ : ℝ) : ℂ) * exp (((5 / 9 * φ : ℝ) : ℂ) * I), ?_, ?_⟩
      · show 0 < (((s ^ (9 / 5 : ℝ)⁻¹ : ℝ) : ℂ) * exp (((5 / 9 * φ : ℝ) : ℂ) * I)).im
        rw [s12_sec_polar_im]
        exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
      · rw [s12_sec_eval hr (by linarith) (by linarith),
          Real.rpow_inv_rpow hs'.le (by norm_num)]
        dsimp only
        unfold hpPowerAngle
        rw [if_pos (by linarith), show 9 / 5 * (5 / 9 * φ) = φ by ring]
  have hlo : hpPowerExt (9 / 5) '' lowerHalf = sectorΩs := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have him : z.im < 0 := hz
      have hz0 : z ≠ 0 := fun h => by rw [h, zero_im] at him; exact lt_irrefl _ him
      have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      obtain ⟨h0, h2⟩ := s11_pow_angle_mem z
      rw [s12_sec_im] at him
      have hgt : π < hpAngle z := by
        by_contra hle
        push_neg at hle
        have h' : 0 ≤ Real.sin (hpAngle z) := Real.sin_nonneg_of_nonneg_of_le_pi h0 hle
        nlinarith [mul_nonneg hr.le h']
      refine ⟨(‖z‖ ^ (9 / 5 : ℝ), 9 / 5 * π + (2 - 9 / 5) * (hpAngle z - π) - 2 * π),
        ⟨Real.rpow_pos_of_pos hr _, by linarith, by linarith⟩, ?_⟩
      dsimp only
      unfold hpPowerExt hpPowerAngle
      rw [if_neg (not_le.mpr hgt)]
      congr 1
      exact (s11_pow_exp_period (by ring)).symm
    · rintro ⟨⟨s, φ⟩, ⟨hs, hφ⟩, rfl⟩
      have hs' : 0 < s := hs
      have hφ0 : -(π / 5) < φ := hφ.1
      have hφ1 : φ < 0 := hφ.2
      have hr : 0 < s ^ (9 / 5 : ℝ)⁻¹ := Real.rpow_pos_of_pos hs' _
      refine ⟨((s ^ (9 / 5 : ℝ)⁻¹ : ℝ) : ℂ) * exp (((2 * π + 5 * φ : ℝ) : ℂ) * I), ?_, ?_⟩
      · show (((s ^ (9 / 5 : ℝ)⁻¹ : ℝ) : ℂ) * exp (((2 * π + 5 * φ : ℝ) : ℂ) * I)).im < 0
        rw [s12_sec_polar_im]
        have h' : 0 < Real.sin (2 * π + 5 * φ - π) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
        rw [Real.sin_sub_pi] at h'
        nlinarith
      · rw [s12_sec_eval hr (by linarith) (by linarith),
          Real.rpow_inv_rpow hs'.le (by norm_num)]
        dsimp only
        unfold hpPowerAngle
        rw [if_neg (by linarith)]
        congr 1
        exact s11_pow_exp_period (by ring)
  exact ⟨hK, hU, hup, hlo, ⟨hpPowerExt (9 / 5), hK, hU, hup, hlo⟩⟩

/-- Helper (C1) for Proposition 12.4(b): the sector curve is a Jordan curve through `∞`
(`T = hpPowerExt (9/5)` with its continuous inverse, `T(ℍ) = Ω`, `T(𝕃) = Ω*`). -/
theorem s12_sec_jordan : IsJordanPair sectorΩ sectorΩs := by
  obtain ⟨g, hgc, hl, hr⟩ := s11_pow_inverse (α := 9 / 5) (by norm_num) (by norm_num)
  obtain ⟨-, -, hup, hlo, -⟩ := prop_sector_a
  exact ⟨⟨⟨hpPowerExt (9 / 5), g, hl, hr⟩, s11_pow_continuous (by norm_num), hgc⟩, hup, hlo⟩

/-- Helper (C2) for Proposition 12.4(b), `sec12-counter.tex:283–297`: for `0 < θ < π`, the
Ahlfors–Weill point of `e^{iαθ} = φ(e^{iθ})`, `φ(ζ) = ζ^α`, `α = 9/5`, is `e^{iψ(θ)}` with
`ψ(θ) = αθ - 2 arg(cos θ + iα sin θ)` (Lemma 12.2 with `Pφ(ζ) = (α-1)/ζ`). -/
theorem s12_sec_aw {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    awPoint sectorΩ (exp (((9 / 5 * θ : ℝ) : ℂ) * I)) =
      ((exp ((((9 / 5) * θ - 2 * arg ((Real.cos θ : ℂ) + I * ((9 / 5 * Real.sin θ : ℝ) : ℂ)) : ℝ) :
        ℂ) * I) : ℂ) : OnePoint ℂ) := by
  have hpi := Real.pi_pos
  set a : ℂ := ((9 / 5 : ℝ) : ℂ) with ha
  have ha0 : a ≠ 0 := by rw [ha]; norm_num
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  obtain ⟨hEq, -⟩ := s11_pow_upper (α := 9 / 5) (by norm_num) (by norm_num)
  obtain ⟨g, -, hl, -⟩ := s11_pow_inverse (α := 9 / 5) (by norm_num) (by norm_num)
  obtain ⟨-, -, hup, -, -⟩ := prop_sector_a
  have hsl : ∀ z ∈ upperHalf, z ∈ slitPlane := fun z hz =>
    Complex.mem_slitPlane_iff.mpr (Or.inr (show (0 : ℝ) < z.im from hz).ne')
  have hφ : IsConformalOnto (fun z : ℂ => z ^ a) upperHalf sectorΩ := by
    refine ⟨fun z hz => (Complex.hasStrictDerivAt_cpow_const (c := a)
      (hsl z hz)).hasDerivAt.differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro z hz w hw hzw
      have hzw' : z ^ a = w ^ a := hzw
      have := congrArg g (((hEq hz).trans hzw').trans (hEq hw).symm)
      rwa [hl z, hl w] at this
    · rw [← hup]
      exact (image_congr hEq).symm
  set c := Real.cos θ with hc
  set s := Real.sin θ with hsdef
  set ζ : ℂ := exp ((θ : ℂ) * I) with hζdef
  have hζe : ζ = (c : ℂ) + (s : ℂ) * I := by
    rw [hζdef, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hζU : ζ ∈ upperHalf := by
    show 0 < ζ.im
    rw [hζe]
    simpa using hs
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hzz : ζ * conj ζ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζdef, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hinv : ζ⁻¹ = conj ζ := inv_eq_of_mul_eq_one_right hzz
  have hconj : conj ζ = (c : ℂ) - (s : ℂ) * I := by
    rw [hζe]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hcz0 : conj ζ ≠ 0 := (map_ne_zero _).mpr hζ0
  have hlog : Complex.log ζ = (θ : ℂ) * I :=
    Complex.log_exp (by simp; linarith) (by simp; linarith)
  have hpow : ζ ^ a = exp (((9 / 5 * θ : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hζ0, hlog, ha]
    congr 1
    push_cast
    ring
  have hd1 : deriv (fun z : ℂ => z ^ a) ζ = a * (ζ ^ a / ζ) := by
    rw [(Complex.hasStrictDerivAt_cpow_const (c := a) (hsl ζ hζU)).hasDerivAt.deriv,
      Complex.cpow_sub _ _ hζ0, Complex.cpow_one]
  have hev : deriv (fun z : ℂ => z ^ a) =ᶠ[𝓝 ζ] fun z => a * z ^ (a - 1) :=
    Filter.eventually_of_mem (isOpen_upperHalf.mem_nhds hζU) fun z hz =>
      (Complex.hasStrictDerivAt_cpow_const (c := a) (hsl z hz)).hasDerivAt.deriv
  have hd2 : deriv (deriv fun z : ℂ => z ^ a) ζ = a * ((a - 1) * (ζ ^ a / ζ / ζ)) := by
    rw [hev.deriv_eq, ((Complex.hasStrictDerivAt_cpow_const (c := a - 1)
      (hsl ζ hζU)).hasDerivAt.const_mul a).deriv, Complex.cpow_sub _ _ hζ0,
      Complex.cpow_sub _ _ hζ0, Complex.cpow_one]
  have hE0 : ζ ^ a ≠ 0 := by rw [hpow]; exact Complex.exp_ne_zero _
  have hP : TakhtajanTeo.Ch2.preSchwarzian (fun z : ℂ => z ^ a) ζ = (a - 1) * conj ζ := by
    unfold TakhtajanTeo.Ch2.preSchwarzian
    rw [hd1, hd2, ← hinv]
    field_simp
  set w : ℂ := (c : ℂ) + I * ((9 / 5 * s : ℝ) : ℂ) with hwdef
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hwdef] at this
    linarith
  have hcs : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by
    rw [hc, hsdef]
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  have hD : 1 - 1 / 2 * ((a - 1) * conj ζ) * (conj ζ - ζ) = conj ζ * w := by
    rw [hconj, hζe, hwdef, ha]
    push_cast
    linear_combination (-1 : ℂ) * hcs + (s : ℂ) ^ 2 * Complex.I_sq
  have hlin : w + a * (conj ζ - ζ) = conj w := by
    rw [hconj, hζe, hwdef, ha]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hw' := Complex.norm_mul_exp_arg_mul_I w
  have hcw : conj w = ((‖w‖ : ℝ) : ℂ) * exp (-((arg w : ℂ) * I)) := by
    conv_lhs => rw [← hw']
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    ring_nf
  have hratio : conj w / w = exp (((-2 * arg w : ℝ) : ℂ) * I) := by
    rw [div_eq_iff hw0, hcw]
    conv_rhs => enter [2]; rw [← hw']
    rw [show exp (((-2 * arg w : ℝ) : ℂ) * I) * (((‖w‖ : ℝ) : ℂ) * exp ((arg w : ℂ) * I)) =
      ((‖w‖ : ℝ) : ℂ) * (exp (((-2 * arg w : ℝ) : ℂ) * I) * exp ((arg w : ℂ) * I)) by ring,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hDne : 1 - 1 / 2 * TakhtajanTeo.Ch2.preSchwarzian (fun z : ℂ => z ^ a) ζ * (conj ζ - ζ) ≠ 0 := by
    rw [hP, hD]
    exact mul_ne_zero hcz0 hw0
  have key := (lem_aw_point_uhp hφ hζU).1 hDne
  rw [hpow] at key
  rw [key]
  congr 1
  unfold oscMob
  rw [hP, hD, hd1]
  show ζ ^ a + a * (ζ ^ a / ζ) * (conj ζ - ζ) / (conj ζ * w) = _
  rw [show (((9 / 5) * θ - 2 * arg w : ℝ) : ℂ) * I =
      ((9 / 5 * θ : ℝ) : ℂ) * I + ((-2 * arg w : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_add, ← hpow, ← hratio, ← hlin]
  rw [div_eq_mul_inv (ζ ^ a) ζ, hinv]
  field_simp

/-- Helper (C3) for Proposition 12.4(b): the boundary angle `ψ` is continuous on `(0, π)`, negative
at `π/2` and positive at `3π/4`. -/
theorem s12_sec_psi :
    let ψ := fun θ : ℝ => 9/5 * θ - 2 * arg ((Real.cos θ : ℂ) + I * ((9/5 * Real.sin θ : ℝ) : ℂ))
    ContinuousOn ψ (Ioo 0 π) ∧ ψ (π/2) < 0 ∧ 0 < ψ (3*π/4) := by
  intro ψ
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, ?_⟩
  · intro θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have hsl : (Real.cos θ : ℂ) + I * ((9/5 * Real.sin θ : ℝ) : ℂ) ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      right
      simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add]
      positivity
    have hc : Continuous fun t : ℝ => (Real.cos t : ℂ) + I * ((9/5 * Real.sin t : ℝ) : ℂ) := by
      fun_prop
    refine ContinuousAt.continuousWithinAt ?_
    show ContinuousAt (fun θ : ℝ => 9/5 * θ -
      2 * arg ((Real.cos θ : ℂ) + I * ((9/5 * Real.sin θ : ℝ) : ℂ))) θ
    exact (continuousAt_id.const_mul _).sub
      (((continuousAt_arg hsl).comp (f := fun t : ℝ =>
        (Real.cos t : ℂ) + I * ((9/5 * Real.sin t : ℝ) : ℂ)) hc.continuousAt).const_mul _)
  · show 9/5 * (π/2) - 2 * arg ((Real.cos (π/2) : ℂ) + I * ((9/5 * Real.sin (π/2) : ℝ) : ℂ)) < 0
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two,
      show ((0 : ℝ) : ℂ) + I * ((9/5 * 1 : ℝ) : ℂ) = ((9/5 : ℝ) : ℂ) * I by push_cast; ring,
      arg_real_mul _ (by norm_num), arg_I]
    linarith
  · show 0 < 9/5 * (3*π/4) -
      2 * arg ((Real.cos (3*π/4) : ℂ) + I * ((9/5 * Real.sin (3*π/4) : ℝ) : ℂ))
    have hc : Real.cos (3*π/4) = -(√2/2) := by
      rw [show 3*π/4 = π - π/4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]
    have hs : Real.sin (3*π/4) = √2/2 := by
      rw [show 3*π/4 = π - π/4 by ring, Real.sin_pi_sub, Real.sin_pi_div_four]
    set w : ℂ := (Real.cos (3*π/4) : ℂ) + I * ((9/5 * Real.sin (3*π/4) : ℝ) : ℂ) with hw
    have hk0 : 0 < √2/2 := by positivity
    have hre : w.re = -(√2/2) := by
      rw [hw]
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero,
        add_zero, hc]
    have him : w.im = 9/5 * (√2/2) := by
      rw [hw]
      simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add, hs]
    have hπ1 : π/2 < arg w := by
      by_contra h
      push_neg at h
      rcases arg_le_pi_div_two_iff.mp h with h | h
      · linarith
      · linarith
    have hπ2 : arg w < π := arg_lt_pi_iff.mpr (Or.inr (by rw [him]; positivity))
    have htan : Real.tan (arg w - π) = -(9/5) := by
      rw [Real.tan_periodic.sub_eq, tan_arg, hre, him, div_neg, mul_div_assoc,
        div_self hk0.ne', mul_one]
    have hu : arg w - π = -Real.arctan (9/5) := by
      rw [← Real.arctan_neg, ← htan, Real.arctan_tan (by linarith) (by linarith)]
    have hadd := Real.arctan_add (x := 1) (y := 2/7) (by norm_num)
    rw [Real.arctan_one] at hadd
    norm_num at hadd
    have h27 : 3*π/40 < Real.arctan (2/7) := by
      have hy0 : 0 < 3*π/40 := by positivity
      have hy1 : 3*π/40 < π/2 := by linarith
      have hyb : 3*π/40 < 0.24 := by linarith [Real.pi_lt_d2]
      rw [← Real.arctan_tan (by linarith) hy1, Real.arctan_lt_arctan_iff]
      have hcos := Real.one_sub_sq_div_two_le_cos (x := 3*π/40)
      have hsin := Real.sin_le hy0.le
      have hcp : 0 < Real.cos (3*π/40) := by nlinarith
      rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcp]
      nlinarith
    linarith

/-- Helper (C4) for Proposition 12.4(b): the least zero `θ₀ ∈ [π/2, 3π/4]` of `ψ`, approached from
the left by angles with `ψ ∈ (-π/5, 0)`. -/
theorem s12_sec_seq :
    let ψ := fun θ : ℝ => 9/5 * θ - 2 * arg ((Real.cos θ : ℂ) + I * ((9/5 * Real.sin θ : ℝ) : ℂ))
    ∃ (θ : ℕ → ℝ) (θ₀ : ℝ), θ₀ ∈ Icc (π/2) (3*π/4) ∧ ψ θ₀ = 0 ∧
      (∀ j, θ j ∈ Ioo (π/2) θ₀ ∧ -(π/5) < ψ (θ j) ∧ ψ (θ j) < 0) ∧
      Tendsto θ atTop (𝓝 θ₀) := by
  intro ψ
  obtain ⟨hcont, h1, h2⟩ := s12_sec_psi
  have hpi := Real.pi_pos
  have hsub : Icc (π/2) (3*π/4) ⊆ Ioo 0 π :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcI : ContinuousOn ψ (Icc (π/2) (3*π/4)) := hcont.mono hsub
  have hab : π/2 ≤ 3*π/4 := by linarith
  set Z := Icc (π/2) (3*π/4) ∩ ψ ⁻¹' {0} with hZ
  have hZc : IsClosed Z := hcI.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZne : Z.Nonempty := by
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hab hcI ⟨h1.le, h2.le⟩
    exact ⟨c, hc, hc0⟩
  have hZb : BddBelow Z := ⟨π/2, fun x hx => hx.1.1⟩
  have hθ₀ : sInf Z ∈ Z := hZc.csInf_mem hZne hZb
  set θ₀ := sInf Z with hθ₀def
  have hθ₀0 : ψ θ₀ = 0 := hθ₀.2
  have hlt : π/2 < θ₀ := by
    refine lt_of_le_of_ne hθ₀.1.1 fun h => ?_
    rw [← h] at hθ₀0
    exact (ne_of_lt h1) hθ₀0
  have hneg : ∀ t ∈ Ico (π/2) θ₀, ψ t < 0 := by
    intro t ht
    by_contra hge
    push_neg at hge
    have htI : t ≤ 3*π/4 := ht.2.le.trans hθ₀.1.2
    obtain ⟨c, hc, hc0⟩ :=
      intermediate_value_Icc ht.1 (hcI.mono (Icc_subset_Icc le_rfl htI)) ⟨h1.le, hge⟩
    have : θ₀ ≤ c := csInf_le hZb ⟨⟨hc.1, hc.2.trans htI⟩, hc0⟩
    linarith [hc.2, ht.2]
  have hca : ContinuousAt ψ θ₀ := hcont.continuousAt (isOpen_Ioo.mem_nhds (hsub hθ₀.1))
  have hev : ∀ᶠ t in 𝓝 θ₀, -(π/5) < ψ t :=
    hca.eventually (lt_mem_nhds (by rw [hθ₀0]; linarith))
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp hev
  set d := min (ε/2) ((θ₀ - π/2)/2) with hd
  have hd0 : 0 < d := lt_min (by linarith) (by linarith)
  have hd1 : d ≤ ε/2 := min_le_left _ _
  have hd2 : d ≤ (θ₀ - π/2)/2 := min_le_right _ _
  refine ⟨fun j => θ₀ - d * (1 / ((j : ℝ) + 1)), θ₀, hθ₀.1, hθ₀0, fun j => ?_, ?_⟩
  · have hj0 : 0 < 1 / ((j : ℝ) + 1) := by positivity
    have hj1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hdj0 : 0 < d * (1 / ((j : ℝ) + 1)) := mul_pos hd0 hj0
    have hdj1 : d * (1 / ((j : ℝ) + 1)) ≤ d := mul_le_of_le_one_right hd0.le hj1
    have hmem : θ₀ - d * (1 / ((j : ℝ) + 1)) ∈ Ioo (π/2) θ₀ := ⟨by linarith, by linarith⟩
    refine ⟨hmem, hεb ?_, hneg _ ⟨hmem.1.le, hmem.2⟩⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul d)

/-- Proposition 12.4(b) `prop:sector`, `sec12-counter.tex:241`: there are `p_j ∈ Ω` with
`p_j♮ ∈ Ωs`, `p_j → p₀ ∈ Ω`, `p_j♮ → 1 ∈ Γ` and `δ(p_j, p_j♮) → ∞`. -/
theorem prop_sector_b :
    ∃ (p p' : ℕ → ℂ) (p₀ : ℂ), p₀ ∈ sectorΩ ∧
      (∀ j, p j ∈ sectorΩ ∧ p' j ∈ sectorΩs ∧ awPoint sectorΩ (p j) = (p' j : OnePoint ℂ)) ∧
      Tendsto p atTop (𝓝 p₀) ∧ Tendsto p' atTop (𝓝 1) ∧
      Tendsto (fun j => horoSpacing sectorΩ sectorΩs (p j) (p' j)) atTop atTop := by
  obtain ⟨θ, θ₀, hθ₀, hψ0, hθ, hlim⟩ := s12_sec_seq
  obtain ⟨hcont, -, -⟩ := s12_sec_psi
  set ψ := fun θ : ℝ => 9/5 * θ - 2 * arg ((Real.cos θ : ℂ) + I * ((9/5 * Real.sin θ : ℝ) : ℂ))
    with hψ
  have hpi := Real.pi_pos
  have hΓ := s12_sec_jordan
  have hmΩ : ∀ φ : ℝ, φ ∈ Ioo 0 (9 * π / 5) → exp ((φ : ℂ) * I) ∈ sectorΩ :=
    fun φ hφ => ⟨(1, φ), ⟨mem_Ioi.mpr one_pos, hφ⟩, by simp⟩
  have hmΩs : ∀ φ : ℝ, φ ∈ Ioo (-(π / 5)) 0 → exp ((φ : ℂ) * I) ∈ sectorΩs :=
    fun φ hφ => ⟨(1, φ), ⟨mem_Ioi.mpr one_pos, hφ⟩, by simp⟩
  have h0Ω : (0 : ℂ) ∉ sectorΩ := by
    rintro ⟨⟨r, φ⟩, ⟨hr, -⟩, h⟩
    have := congrArg norm h
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      norm_zero, abs_of_pos (mem_Ioi.mp hr)] at this
    exact (ne_of_gt (mem_Ioi.mp hr)) this
  have h1Ωs : (1 : ℂ) ∉ sectorΩs := by
    rintro ⟨⟨r, φ⟩, ⟨hr, hφ⟩, h⟩
    have := congrArg Complex.im h
    rw [s12_sec_polar_im, one_im] at this
    have := mul_neg_of_pos_of_neg (mem_Ioi.mp hr)
      (Real.sin_neg_of_neg_of_neg_pi_lt hφ.2 (by linarith [hφ.1]))
    linarith
  have hlow : ∀ {Ω Ωs : Set ℂ}, IsJordanPair Ω Ωs → ∀ {q c : ℂ}, q ∈ Ω → c ∉ Ω →
      1 / (2 * ‖q - c‖) ≤ poincareDensity Ω q := by
    intro Ω Ωs hΓ q c hq hc
    obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at hΓ hq
    have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
    obtain ⟨-, h2, h3, -⟩ := lem_koebe_a hf h0
    rw [hf0] at h2 h3
    have hdf : deriv f 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 h0
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      one_mul] at h2
    have hd0 : 0 < infDist q Ωᶜ := by
      have := norm_pos_iff.mpr hdf
      linarith
    have hdle : infDist q Ωᶜ ≤ ‖q - c‖ := by
      rw [← dist_eq_norm]
      exact infDist_le_dist_of_mem hc
    exact le_trans (one_div_le_one_div_of_le (by positivity) (by linarith)) h3
  set p : ℕ → ℂ := fun j => exp (((9/5 * θ j : ℝ) : ℂ) * I) with hp
  set p' : ℕ → ℂ := fun j => exp (((ψ (θ j) : ℝ) : ℂ) * I) with hp'
  set p₀ : ℂ := exp (((9/5 * θ₀ : ℝ) : ℂ) * I) with hp₀
  have hpm : ∀ j, p j ∈ sectorΩ := fun j =>
    hmΩ _ ⟨by linarith [(hθ j).1.1], by linarith [(hθ j).1.2, hθ₀.2]⟩
  have hp'm : ∀ j, p' j ∈ sectorΩs := fun j => hmΩs _ ⟨(hθ j).2.1, (hθ j).2.2⟩
  have hcE : Continuous fun t : ℝ => exp ((t : ℂ) * I) := by fun_prop
  have hplim : Tendsto p atTop (𝓝 p₀) :=
    (hcE.tendsto _).comp (((continuous_const.mul continuous_id).tendsto θ₀).comp hlim)
  have hψc : ContinuousAt ψ θ₀ :=
    hcont.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith [hθ₀.1], by linarith [hθ₀.2]⟩)
  have hp'lim : Tendsto p' atTop (𝓝 1) := by
    have h := (hcE.tendsto _).comp (hψc.tendsto.comp hlim)
    have h1 : exp (((ψ θ₀ : ℝ) : ℂ) * I) = 1 := by rw [hψ0]; simp
    rw [h1] at h
    exact h
  have hp₀1 : p₀ ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hp₀, exp_ofReal_mul_I_re, one_re] at hre
    have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 9/5 * θ₀) (by linarith [hθ₀.1])
      (by linarith [hθ₀.2])
    linarith
  refine ⟨p, p', p₀, hmΩ _ ⟨by linarith [hθ₀.1], by linarith [hθ₀.2]⟩, fun j =>
    ⟨hpm j, hp'm j, s12_sec_aw (by linarith [(hθ j).1.1]) (by linarith [(hθ j).1.2, hθ₀.2])⟩,
    hplim, hp'lim, ?_⟩
  -- `δ → ∞`
  have hsp : ∀ j, horoSpacing sectorΩ sectorΩs (p j) (p' j) =
      Real.log (‖p j - p' j‖ ^ 2 * poincareDensity sectorΩ (p j) *
        poincareDensity sectorΩs (p' j) / 4) :=
    fun j => (lem_spacing_a hΓ s12_sec_not_line (hpm j) (hp'm j)).1
  have hne : ∀ j, 0 < ‖p' j - 1‖ := fun j =>
    norm_pos_iff.mpr (sub_ne_zero.mpr fun h => h1Ωs (h ▸ hp'm j))
  have hden : Tendsto (fun j => ‖p' j - 1‖) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall hne⟩
    simpa using (hp'lim.sub_const 1).norm
  have hnum : Tendsto (fun j => ‖p j - p' j‖ ^ 2 / 16) atTop (𝓝 (‖p₀ - 1‖ ^ 2 / 16)) :=
    (((hplim.sub hp'lim).norm).pow 2).div_const 16
  have hC : 0 < ‖p₀ - 1‖ ^ 2 / 16 := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hp₀1)
    positivity
  have hg : Tendsto (fun j => (‖p' j - 1‖)⁻¹ * (‖p j - p' j‖ ^ 2 / 16)) atTop atTop :=
    hden.inv_tendsto_nhdsGT_zero.atTop_mul_pos hC hnum
  have hQ : Tendsto (fun j => ‖p j - p' j‖ ^ 2 * poincareDensity sectorΩ (p j) *
      poincareDensity sectorΩs (p' j) / 4) atTop atTop := by
    refine tendsto_atTop_mono (fun j => ?_) hg
    have hl1 : 1 / 2 ≤ poincareDensity sectorΩ (p j) := by
      have := hlow hΓ (hpm j) h0Ω
      rwa [sub_zero, hp, norm_exp_ofReal_mul_I, mul_one] at this
    have hl2 := hlow (s02_jordanPair_symm hΓ) (hp'm j) h1Ωs
    have hn := hne j
    calc (‖p' j - 1‖)⁻¹ * (‖p j - p' j‖ ^ 2 / 16)
        = ‖p j - p' j‖ ^ 2 * (1 / 2) * (1 / (2 * ‖p' j - 1‖)) / 4 := by
          field_simp
          ring
      _ ≤ _ := by
          refine (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).mpr ?_
          exact mul_le_mul (mul_le_mul_of_nonneg_left hl1 (sq_nonneg _)) hl2 (by positivity)
            (mul_nonneg (sq_nonneg _) (le_trans (by norm_num) hl1))
  exact (Real.tendsto_log_atTop.comp hQ).congr fun j => (hsp j).symm

/-- Helper: a Riemann map of `Ω` sending `0` to a prescribed point `p ∈ Ω`. -/
theorem s12_riemann_at {Ω : Set ℂ} (hΩ : ∃ φ : ℂ → ℂ, IsConformalOnto φ unitDisc Ω) {p : ℂ}
    (hp : p ∈ Ω) : ∃ F : ℂ → ℂ, IsConformalOnto F unitDisc Ω ∧ F 0 = p := by
  obtain ⟨φ, hφ⟩ := hΩ
  rw [← hφ.2.2] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  have hna : ‖-a‖ < 1 := by rw [norm_neg]; exact mem_ball_zero_iff.mp ha
  exact ⟨φ ∘ blaschke (-a), hφ.comp (isConformalOnto_blaschke hna), by simp⟩

/-- Helper: Kraus–Nehari in pulled-back form, `¼|S F|²(1-|z|²)² ≤ (9/4) · 4/(1-|z|²)²`. -/
theorem s12_nehari_disk {Ω : Set ℂ} {F : ℂ → ℂ} (hF : IsConformalOnto F unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) :
    ENNReal.ofReal (‖schwarzian F z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4) ≤
      (9 / 4 : ℝ≥0∞) * ENNReal.ofReal (4 / (1 - ‖z‖ ^ 2) ^ 2) := by
  have hN := (eq_nehari ⟨F, hF⟩ (hF.2.2 ▸ mem_image_of_mem F hz)).2
  rw [eq_s_disk hF hz] at hN
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have h94 : (9 / 4 : ℝ≥0∞) = ENNReal.ofReal (9 / 4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [h94, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  set t := ‖schwarzian F z‖
  set r := 1 - ‖z‖ ^ 2
  have ht : 0 ≤ t := norm_nonneg _
  have h1 : t * r ^ 2 ≤ 6 := by linarith
  rw [show 9 / 4 * (4 / r ^ 2) = 9 / r ^ 2 by field_simp, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg ht (sq_nonneg r), mul_le_mul h1 h1 (by positivity) (by norm_num)]

/-- Helper: `∫ κ(d_ρ(p,·)) dm_Ω ≤ (9/4) ∫_𝔻 κ(d(0,·)) dâ` (the content of `rem:sector-scope`(ii)). -/
theorem s12_curvMass_radial_le {Ω : Set ℂ} (hΩ : ∃ φ : ℂ → ℂ, IsConformalOnto φ unitDisc Ω)
    {κ : ℝ → ℝ≥0∞} (hκ : Measurable κ) {p : ℂ} (hp : p ∈ Ω) :
    ∫⁻ w, κ (poincareDist Ω p w) ∂curvMass Ω ≤
      (9 / 4 : ℝ≥0∞) * ∫⁻ z in unitDisc,
        κ (diskDist 0 z) * ENNReal.ofReal (4 / (1 - ‖z‖ ^ 2) ^ 2) := by
  classical
  obtain ⟨F, hF, rfl⟩ := s12_riemann_at hΩ hp
  set g := Function.invFunOn F unitDisc with hgdef
  have hfc : ContinuousOn F unitDisc := hF.1.continuousOn
  have hH : IsHomeomorphOnto F unitDisc (F '' unitDisc) :=
    qcl_f_isHomeomorphOnto_of_injOn isOpen_ball hfc hF.2.1
  have hgc : ContinuousOn g Ω := by
    rw [hgdef, ← hF.2.2]
    exact hH.2.2.2
  have hΩm : MeasurableSet Ω := by
    rw [← hF.2.2]
    exact measurableSet_ball.image_of_continuousOn_injOn hfc hF.2.1
  have hleft : ∀ z ∈ unitDisc, g (F z) = z := fun z hz => hF.2.1.leftInvOn_invFunOn hz
  set G : ℂ → ℂ := Ω.piecewise g 0 with hGdef
  have hGm : Measurable G := ContinuousOn.measurable_piecewise hgc continuousOn_const hΩm
  have hdm : Measurable fun z : ℂ => diskDist 0 z := by
    unfold diskDist Real.arcosh diskCoshDist; fun_prop
  set ψ : ℂ → ℝ≥0∞ := fun w => κ (diskDist 0 (G w)) with hψdef
  have hψm : Measurable ψ := hκ.comp (hdm.comp hGm)
  have hψf : ∀ z ∈ unitDisc, ψ (F z) = κ (diskDist 0 z) := by
    intro z hz
    have hFz : F z ∈ Ω := hF.2.2 ▸ mem_image_of_mem F hz
    simp only [hψdef, hGdef, Set.piecewise_eq_of_mem _ _ _ hFz, hleft z hz]
  have hK : ∀ w ∈ Ω, κ (poincareDist Ω (F 0) w) = ψ w := by
    intro w hw
    rw [← hF.2.2] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [hψf z hz, subsec_poincare_dist hF (mem_ball_self one_pos) hz]
  have hae : ∀ᵐ w ∂curvMass Ω, κ (poincareDist Ω (F 0) w) = ψ w := by
    have h1 : ∀ᵐ w ∂(volume.restrict Ω), w ∈ Ω := ae_restrict_mem hΩm
    have h2 : ∀ᵐ w ∂curvMass Ω, w ∈ Ω := (withDensity_absolutelyContinuous _ _).ae_le h1
    filter_upwards [h2] with w hw
    exact hK w hw
  rw [lintegral_congr_ae hae, eq_pullback_mass_a hF hψm,
    ← lintegral_const_mul' _ _ (ENNReal.div_ne_top (by simp) (by simp))]
  refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
  rw [hψf z hz]
  calc κ (diskDist 0 z) * ENNReal.ofReal (‖schwarzian F z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4)
      ≤ κ (diskDist 0 z) * ((9 / 4 : ℝ≥0∞) * ENNReal.ofReal (4 / (1 - ‖z‖ ^ 2) ^ 2)) :=
        by gcongr; exact s12_nehari_disk hF hz
    _ = _ := by ring

/-- Proposition 12.4(c) `prop:sector`, `sec12-counter.tex:244`, first part: `𝓘(p) ≤ 9π` (stated
for every domain conformally equivalent to `𝔻`, which covers both components of every Jordan
curve). -/
theorem prop_sector_c {Ω : Set ℂ} (hΩ : ∃ φ : ℂ → ℂ, IsConformalOnto φ unitDisc Ω) {p : ℂ} (hp : p ∈ Ω) :
    curvKernelInt Ω p ≤ ENNReal.ofReal (9 * π) := by
  set κ : ℝ → ℝ≥0∞ := fun d => ENNReal.ofReal ((((Real.cosh (d / 2))⁻¹) ^ 2) ^ 2) with hκdef
  have hκ : Measurable κ := by fun_prop
  have h1 : curvKernelInt Ω p = ∫⁻ w, κ (poincareDist Ω p w) ∂curvMass Ω := rfl
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hpt : ∀ z ∈ unitDisc,
      κ (diskDist 0 z) * ENNReal.ofReal (4 / (1 - ‖z‖ ^ 2) ^ 2) = ENNReal.ofReal 4 := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hr : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hk := s02_intrKernel_eq (isConformalOnto_id unitDisc) h0 hz
    have hd := subsec_poincare_dist (isConformalOnto_id unitDisc) h0 hz
    simp only [id_eq] at hk hd
    rw [show (1 - ‖(0 : ℂ)‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - conj 0 * z‖ ^ 2 = 1 - ‖z‖ ^ 2 by simp]
      at hk
    unfold intrKernel at hk
    rw [hd] at hk
    simp only [hκdef]
    rw [hk, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hvol : volume unitDisc = ENNReal.ofReal π := by
    rw [show unitDisc = ball (0 : ℂ) 1 from rfl, Complex.volume_ball]
    simp [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have h94 : (9 / 4 : ℝ≥0∞) = ENNReal.ofReal (9 / 4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [h1]
  calc ∫⁻ w, κ (poincareDist Ω p w) ∂curvMass Ω
      ≤ (9 / 4 : ℝ≥0∞) * ∫⁻ z in unitDisc,
          κ (diskDist 0 z) * ENNReal.ofReal (4 / (1 - ‖z‖ ^ 2) ^ 2) :=
        s12_curvMass_radial_le hΩ hκ hp
    _ = (9 / 4 : ℝ≥0∞) * (ENNReal.ofReal 4 * volume unitDisc) := by
        rw [setLIntegral_congr_fun (s := unitDisc) measurableSet_ball hpt, setLIntegral_const]
    _ = ENNReal.ofReal (9 * π) := by
        rw [hvol, h94, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring


/-- Proposition 12.4(c) `prop:sector`, `sec12-counter.tex:250`, consequence: on the sector curve
there is no `C < ∞` with `δ(p, p♮) ≤ C (𝓘(p) + 𝓘*(p♮))` for all `p ∈ Ω` with `p♮ ∈ Ωs`. -/
theorem prop_sector_c_noconst :
    ¬ ∃ C : ℝ≥0, ∀ p ∈ sectorΩ, ∀ p' ∈ sectorΩs, awPoint sectorΩ p = (p' : OnePoint ℂ) →
      ENNReal.ofReal (horoSpacing sectorΩ sectorΩs p p') ≤
        C * (curvKernelInt sectorΩ p + curvKernelInt sectorΩs p') := by
  rintro ⟨C, hC⟩
  obtain ⟨p, p', -, -, hj, -, -, hδ⟩ := prop_sector_b
  have hΓ := s12_sec_jordan
  have hb : ∀ j, horoSpacing sectorΩ sectorΩs (p j) (p' j) ≤ (C : ℝ) * (9 * π + 9 * π) := by
    intro j
    obtain ⟨h1, h2, h3⟩ := hj j
    have hle := (hC _ h1 _ h2 h3).trans (mul_le_mul_right (add_le_add
      (prop_sector_c (s02_jordanPair_riemannMap hΓ) h1)
      (prop_sector_c (s02_jordanPair_riemannMap (s02_jordanPair_symm hΓ)) h2)) _)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul C.coe_nonneg] at hle
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  obtain ⟨j, hj'⟩ := (hδ.eventually_gt_atTop ((C : ℝ) * (9 * π + 9 * π))).exists
  exact absurd (hb j) (not_le.mpr hj')

/-- Helper (D0) for Proposition 12.4(d): pulling a Riemann map of `M(Ω)` back by
`N = M⁻¹ : w ↦ p' + 1/(w + 1/(p - p'))` gives a Riemann map of `Ω` at `p`. -/
theorem s12_sd_pull {Ω : Set ℂ} {p p' : ℂ} (hp : p ∈ Ω) (hp' : p' ∉ Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc ((fun z => 1 / (z - p') - 1 / (p - p')) '' Ω))
    (hf0 : f 0 = 0) :
    let N := fun w : ℂ => p' + 1 / (w + 1 / (p - p'))
    IsConformalOnto (N ∘ f) unitDisc Ω ∧ (N ∘ f) 0 = p ∧
      deriv (N ∘ f) 0 = -(p - p') ^ 2 * deriv f 0 ∧
      deriv (deriv (N ∘ f)) 0 =
        -(p - p') ^ 2 * deriv (deriv f) 0 + 2 * (p - p') ^ 3 * deriv f 0 ^ 2 := by
  intro N
  have hpp : p - p' ≠ 0 := sub_ne_zero.mpr fun h => hp' (h ▸ hp)
  set c : ℂ := 1 / (p - p') with hc
  have hc0 : c ≠ 0 := one_div_ne_zero hpp
  have hNM : ∀ q : ℂ, q ≠ p' → N (1 / (q - p') - c) = q := by
    intro q hq
    have hq' : q - p' ≠ 0 := sub_ne_zero.mpr hq
    show p' + 1 / (1 / (q - p') - c + c) = q
    rw [sub_add_cancel, one_div_one_div]
    ring
  have hval : ∀ z ∈ unitDisc, f z + c ≠ 0 ∧ N (f z) ∈ Ω := by
    intro z hz
    have : f z ∈ f '' unitDisc := mem_image_of_mem f hz
    rw [hf.2.2] at this
    obtain ⟨q, hq, hqz⟩ := this
    have hqp : q ≠ p' := fun h => hp' (h ▸ hq)
    rw [← hqz]
    refine ⟨?_, by rw [hNM q hqp]; exact hq⟩
    show 1 / (q - p') - c + c ≠ 0
    rw [sub_add_cancel]
    exact one_div_ne_zero (sub_ne_zero.mpr hqp)
  have hNd : ∀ w : ℂ, w + c ≠ 0 → HasDerivAt N (-1 / (w + c) ^ 2) w := by
    intro w hw
    have e : N = fun x => p' + (x + c)⁻¹ := by
      funext x
      show p' + 1 / (x + 1 / (p - p')) = p' + (x + c)⁻¹
      rw [hc]
      simp only [one_div]
    rw [e]
    exact (((hasDerivAt_id' w).add_const c).inv hw).const_add p'
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hfd : ∀ z ∈ unitDisc, HasDerivAt f (deriv f z) z := fun z hz =>
    (hf.1.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hcomp : ∀ z ∈ unitDisc, HasDerivAt (N ∘ f) (-1 / (f z + c) ^ 2 * deriv f z) z :=
    fun z hz => (hNd (f z) (hval z hz).1).comp z (hfd z hz)
  refine ⟨⟨fun z hz => (hcomp z hz).differentiableAt.differentiableWithinAt, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro z₁ hz₁ z₂ hz₂ h
    have h' : 1 / (f z₁ + c) = 1 / (f z₂ + c) := add_left_cancel h
    rw [one_div, one_div, inv_inj, add_left_inj] at h'
    exact hf.2.1 hz₁ hz₂ h'
  · refine Subset.antisymm ?_ fun q hq => ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact (hval z hz).2
    · have hqp : q ≠ p' := fun h => hp' (h ▸ hq)
      have : 1 / (q - p') - c ∈ f '' unitDisc := by
        rw [hf.2.2]; exact ⟨q, hq, rfl⟩
      obtain ⟨z, hz, hzq⟩ := this
      exact ⟨z, hz, by show N (f z) = q; rw [hzq, hNM q hqp]⟩
  · show p' + 1 / (f 0 + c) = p
    rw [hf0, zero_add, hc, one_div_one_div]
    ring
  · rw [(hcomp 0 h0).deriv, hf0, zero_add, hc]
    field_simp
  · have hev : deriv (N ∘ f) =ᶠ[𝓝 0] fun z => -deriv f z / (f z + c) ^ 2 :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds h0) fun z hz => by
        rw [(hcomp z hz).deriv]; ring
    have hf' : HasDerivAt (deriv f) (deriv (deriv f) 0) 0 :=
      ((hf.1.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    have hden : HasDerivAt (fun z => (f z + c) ^ 2)
        (((2 : ℕ) : ℂ) * (f 0 + c) ^ (2 - 1) * deriv f 0) 0 :=
      ((hfd 0 h0).add_const c).pow 2
    have hq : HasDerivAt (fun z => -deriv f z / (f z + c) ^ 2)
        ((-deriv (deriv f) 0 * (f 0 + c) ^ 2 - -deriv f 0 *
          (((2 : ℕ) : ℂ) * (f 0 + c) ^ (2 - 1) * deriv f 0)) / ((f 0 + c) ^ 2) ^ 2) 0 :=
      hf'.neg.div hden (pow_ne_zero 2 (hval 0 h0).1)
    rw [hev.deriv_eq, hq.deriv, hf0, zero_add, hc]
    norm_num
    field_simp

/-- Helper (D2) for Proposition 12.4(d): if `p♮ = p'`, the Riemann map `f` of `M(Ω)` with
`f(0) = M(p) = 0` has `f''(0) = 0`. -/
theorem s12_sd_fpp {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {p p' : ℂ} (hp : p ∈ Ω)
    (hp' : p' ∈ Ωs) (haw : awPoint Ω p = (p' : OnePoint ℂ)) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc ((fun z => 1 / (z - p') - 1 / (p - p')) '' Ω))
    (hf0 : f 0 = 0) : deriv (deriv f) 0 = 0 := by
  have hp'Ω : p' ∉ Ω := fun h => Set.disjoint_left.mp (s02_jordanPair_disjoint hΓ) h hp'
  have hpp : p - p' ≠ 0 := sub_ne_zero.mpr fun h => hp'Ω (h ▸ hp)
  obtain ⟨hφ, hφ0, hd1, hd2⟩ := s12_sd_pull hp hp'Ω hf hf0
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have ha : deriv f 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 h0
  have hA : logDensityDz Ω p = -1 / (p - p') := by
    unfold awPoint at haw
    split_ifs at haw with hA0
    · exact absurd haw (OnePoint.infty_ne_coe _)
    have h1 : p + 1 / logDensityDz Ω p = p' := OnePoint.coe_injective haw
    have h2 : 1 / logDensityDz Ω p = -(p - p') := by linear_combination h1
    rw [← one_div_one_div (logDensityDz Ω p), h2, one_div_neg_eq_neg_one_div, neg_div]
  have h := eq_A_transform_disk hφ h0
  rw [hφ0, hA, hd1, hd2] at h
  simp only [map_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero, Complex.ofReal_one, div_one, zero_sub] at h
  have hd : (p - p') ^ 2 ≠ 0 := pow_ne_zero 2 hpp
  field_simp at h
  linear_combination h

/-- Helper: `𝔻* ∈ cocompact ℂ`, so `cocompact ℂ ⊓ 𝓟 𝔻* = cocompact ℂ`. -/
theorem s12_sd_cocompact : cocompact ℂ ⊓ 𝓟 unitDiscExterior = cocompact ℂ := by
  refine inf_eq_left.mpr (le_principal_iff.mpr (mem_cocompact.mpr ⟨closedBall 0 1,
    isCompact_closedBall 0 1, fun z hz => ?_⟩))
  have : ¬ ‖z‖ ≤ 1 := by simpa using hz
  exact lt_of_not_ge this

/-- Helper (D1) for Proposition 12.4(d): `(f/f'(0), g/f'(0))` is a normalized disjoint pair. -/
theorem s12_sd_normal {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {p p' : ℂ} (hp : p ∈ Ω)
    (hp' : p' ∈ Ωs) {f g : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc ((fun z => 1 / (z - p') - 1 / (p - p')) '' Ω))
    (hf0 : f 0 = 0)
    (hg : IsConformalOnto g unitDiscExterior
      ((fun z => 1 / (z - p') - 1 / (p - p')) '' (Ωs \ {p'})))
    (hginf : Tendsto g (cocompact ℂ ⊓ 𝓟 unitDiscExterior) (cocompact ℂ)) :
    deriv f 0 ≠ 0 ∧ TakhtajanTeo.Ch2.IsNormalizedDisjointPair (fun z => f z / deriv f 0)
      (fun z => g z / deriv f 0) := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have ha : deriv f 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 h0
  set a := deriv f 0 with hadef
  have hdiv : ∀ {x y : ℂ}, x / a = y / a → x = y := fun h => (div_left_inj' ha).mp h
  refine ⟨ha, hf.1.div_const a, fun z₁ hz₁ z₂ hz₂ h => hf.2.1 hz₁ hz₂ (hdiv h),
    by simp [hf0], ?_, ⟨hg.1.div_const a, fun z₁ hz₁ z₂ hz₂ h => hg.2.1 hz₁ hz₂ (hdiv h), ?_⟩, ?_⟩
  · rw [deriv_div_const, ← hadef, div_self ha]
  · rw [s12_sd_cocompact] at hginf
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded] at hginf ⊢
    simp only [norm_div]
    exact hginf.atTop_div_const (norm_pos_iff.mpr ha)
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, h⟩
    have e := hdiv h
    have h1 : f z₁ ∈ f '' unitDisc := mem_image_of_mem f hz₁
    have h2 : g z₂ ∈ g '' unitDiscExterior := mem_image_of_mem g hz₂
    rw [hf.2.2] at h1
    rw [hg.2.2] at h2
    obtain ⟨q₁, hq₁, e₁⟩ := h1
    obtain ⟨q₂, ⟨hq₂, hq₂'⟩, e₂⟩ := h2
    have hq : 1 / (q₂ - p') = 1 / (q₁ - p') := by
      have := e₂.trans (e.trans e₁.symm)
      simpa using this
    rw [one_div, one_div, inv_inj, sub_left_inj] at hq
    exact Set.disjoint_left.mp (s02_jordanPair_disjoint hΓ) hq₁ (hq ▸ hq₂)

/-- Helper (D3) for Proposition 12.4(d): pushing `g` at `∞` to a Riemann map `h` of `Ωs` at `p'`,
`h u = p' + u / (a b e^{φ(u)} + u/(p - p'))`, with `|h'(0)| = 1/(|a| |G'(∞)|)`. -/
theorem s12_sd_push {Ωs : Set ℂ} {p p' : ℂ} (hp : p ∉ Ωs) (hp' : p' ∈ Ωs) {g : ℂ → ℂ}
    (hg : IsConformalOnto g unitDiscExterior
      ((fun z => 1 / (z - p') - 1 / (p - p')) '' (Ωs \ {p'})))
    {a : ℂ} (ha : a ≠ 0) {F : ℂ → ℂ}
    (hpair : TakhtajanTeo.Ch2.IsNormalizedDisjointPair F (fun z => g z / a)) :
    ∃ h : ℂ → ℂ, IsConformalOnto h unitDisc Ωs ∧ h 0 = p' ∧
      ‖deriv h 0‖ = 1 / (‖a‖ * ‖TakhtajanTeo.derivAtInfty (fun z => g z / a)‖) := by
  obtain ⟨φ, hs, hgφ⟩ := TakhtajanTeo.Ch2.r22_g_series hpair
  obtain ⟨hexp, -, -, -, -⟩ := (TakhtajanTeo.Ch2.grunsky_spec hpair).1
  set b := TakhtajanTeo.derivAtInfty (fun z => g z / a) with hb
  have hb0 : b ≠ 0 := by rw [← hexp]; exact Complex.exp_ne_zero _
  have hφd := TakhtajanTeo.Ch2.differentiableOn_of_powerSeries hs
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hφ0 : φ 0 = 0 := by
    have hz : (fun n : ℕ => (if n = 0 then (0 : ℂ) else
        -TakhtajanTeo.Ch2.grunsky F (fun z => g z / a) (n : ℤ) 0) * (0 : ℂ) ^ n) = fun _ => 0 := by
      funext n
      rcases n with _ | n <;> simp
    have := hs 0 h0
    rw [hz] at this
    exact this.unique hasSum_zero
  set c : ℂ := 1 / (p - p') with hc
  have hinvE : ∀ u ∈ unitDisc, u ≠ 0 → u⁻¹ ∈ unitDiscExterior := by
    intro u hu hu0
    show 1 < ‖u⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hu0)).mpr (mem_ball_zero_iff.mp hu)
  have hgv : ∀ z ∈ unitDiscExterior, ∃ q ∈ Ωs, q ≠ p' ∧ g z = 1 / (q - p') - c := by
    intro z hz
    have : g z ∈ g '' unitDiscExterior := mem_image_of_mem g hz
    rw [hg.2.2] at this
    obtain ⟨q, ⟨hq, hq'⟩, e⟩ := this
    exact ⟨q, hq, hq', e.symm⟩
  have hgc : ∀ z ∈ unitDiscExterior, g z + c ≠ 0 := by
    intro z hz
    obtain ⟨q, -, hq', e⟩ := hgv z hz
    rw [e, sub_add_cancel]
    exact one_div_ne_zero (sub_ne_zero.mpr hq')
  have hgN : ∀ z ∈ unitDiscExterior, p' + 1 / (g z + c) ∈ Ωs ∧ p' + 1 / (g z + c) ≠ p' := by
    intro z hz
    obtain ⟨q, hq, hq', e⟩ := hgv z hz
    rw [e, sub_add_cancel, one_div_one_div, add_sub_cancel]
    exact ⟨hq, hq'⟩
  set D : ℂ → ℂ := fun u => a * b * exp (φ u) + c * u with hD
  have hDu : ∀ u ∈ unitDisc, u ≠ 0 → D u = u * (g u⁻¹ + c) := by
    intro u hu hu0
    have e := hgφ u hu hu0
    rw [div_eq_iff ha] at e
    show a * b * exp (φ u) + c * u = u * (g u⁻¹ + c)
    rw [e]
    field_simp
  have hD0 : ∀ u ∈ unitDisc, D u ≠ 0 := by
    intro u hu
    by_cases hu0 : u = 0
    · rw [hu0]
      show a * b * exp (φ 0) + c * 0 ≠ 0
      rw [hφ0, Complex.exp_zero, mul_zero, add_zero, mul_one]
      exact mul_ne_zero ha hb0
    · rw [hDu u hu hu0]
      exact mul_ne_zero hu0 (hgc _ (hinvE u hu hu0))
  set h : ℂ → ℂ := fun u => p' + u / D u with hh
  have hhN : ∀ u ∈ unitDisc, u ≠ 0 → h u = p' + 1 / (g u⁻¹ + c) := by
    intro u hu hu0
    show p' + u / D u = _
    rw [hDu u hu hu0, div_mul_cancel_left₀ hu0, one_div]
  have hDd : DifferentiableOn ℂ D unitDisc :=
    ((differentiableOn_const _).mul hφd.cexp).add ((differentiableOn_const _).mul differentiableOn_id)
  have hh0 : h 0 = p' := by show p' + 0 / D 0 = p'; rw [zero_div, add_zero]
  refine ⟨h, ⟨(differentiableOn_const _).add (differentiableOn_id.div hDd hD0), ?_, ?_⟩, hh0, ?_⟩
  · intro u₁ hu₁ u₂ hu₂ e
    by_cases h₁ : u₁ = 0 <;> by_cases h₂ : u₂ = 0
    · rw [h₁, h₂]
    · exact absurd (hh0 ▸ h₁ ▸ e).symm (hhN u₂ hu₂ h₂ ▸ (hgN _ (hinvE u₂ hu₂ h₂)).2)
    · exact absurd (hh0 ▸ h₂ ▸ e) (hhN u₁ hu₁ h₁ ▸ (hgN _ (hinvE u₁ hu₁ h₁)).2)
    · rw [hhN u₁ hu₁ h₁, hhN u₂ hu₂ h₂, add_right_inj, one_div, one_div, inv_inj,
        add_left_inj] at e
      exact inv_injective (hg.2.1 (hinvE u₁ hu₁ h₁) (hinvE u₂ hu₂ h₂) e)
  · refine Subset.antisymm ?_ fun q hq => ?_
    · rintro _ ⟨u, hu, rfl⟩
      by_cases hu0 : u = 0
      · rw [hu0, hh0]; exact hp'
      · rw [hhN u hu hu0]; exact (hgN _ (hinvE u hu hu0)).1
    · by_cases hqp : q = p'
      · exact ⟨0, h0, hqp ▸ hh0⟩
      · have : 1 / (q - p') - c ∈ g '' unitDiscExterior := by
          rw [hg.2.2]; exact ⟨q, ⟨hq, hqp⟩, rfl⟩
        obtain ⟨z, hz, hzq⟩ := this
        have hz1 : 1 < ‖z‖ := hz
        have hz0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at hz1; linarith
        have hu : z⁻¹ ∈ unitDisc :=
          mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1)
        refine ⟨z⁻¹, hu, ?_⟩
        rw [hhN _ hu (inv_ne_zero hz0), inv_inv, hzq, sub_add_cancel, one_div_one_div]
        ring
  · have hDh : HasDerivAt D (deriv D 0) 0 :=
      (hDd.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    have hq : HasDerivAt (fun u => u / D u) ((1 * D 0 - 0 * deriv D 0) / D 0 ^ 2) 0 :=
      (hasDerivAt_id' 0).div hDh (hD0 0 h0)
    have hq' : HasDerivAt h ((1 * D 0 - 0 * deriv D 0) / D 0 ^ 2) 0 := hq.const_add p'
    have hD0' : D 0 = a * b := by
      show a * b * exp (φ 0) + c * 0 = a * b
      rw [hφ0, Complex.exp_zero, mul_zero, add_zero, mul_one]
    rw [hq'.deriv, hD0', one_mul, zero_mul, sub_zero, sq, div_mul_cancel_right₀ (mul_ne_zero ha hb0),
      norm_inv, norm_mul, one_div]

/-- Helper (D4) for Proposition 12.4(d): the complement of `F𝔻 ∪ G𝔻*` is Lebesgue-null (the sector
curve lies on two real lines, and `z ↦ M(z)/a` is differentiable off `p'`). -/
theorem s12_sd_null {p p' : ℂ} (hp : p ∈ sectorΩ) (hp' : p' ∈ sectorΩs) {f g : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc ((fun z => 1 / (z - p') - 1 / (p - p')) '' sectorΩ))
    (hg : IsConformalOnto g unitDiscExterior
      ((fun z => 1 / (z - p') - 1 / (p - p')) '' (sectorΩs \ {p'})))
    {a : ℂ} (ha : a ≠ 0) :
    volume (((fun z => f z / a) '' unitDisc ∪ (fun z => g z / a) '' unitDiscExterior)ᶜ) = 0 := by
  set c : ℂ := 1 / (p - p') with hc
  set K : Set ℂ := (sectorΩ ∪ sectorΩs)ᶜ with hK
  have hp'K : p' ∉ K := fun h => h (Or.inr hp')
  have hspan : ∀ v : ℂ, v ≠ 0 → Submodule.span ℝ {v} ≠ ⊤ := by
    intro v hv htop
    have hI : I * v ∈ Submodule.span ℝ {v} := htop ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hI
    rw [Complex.real_smul] at hr
    have h1 := congrArg Complex.im (mul_right_cancel₀ hv hr)
    simp at h1
  have hpol : ∀ z : ℂ, (‖z‖ : ℂ) * exp ((arg z : ℂ) * I) = z := Complex.norm_mul_exp_arg_mul_I
  have hpi := Real.pi_pos
  have hKsub : K ⊆ (Submodule.span ℝ {(1 : ℂ)} : Set ℂ) ∪
      (Submodule.span ℝ {exp (((-(π / 5) : ℝ) : ℂ) * I)} : Set ℂ) := by
    intro z hz
    simp only [hK, mem_compl_iff, mem_union, not_or] at hz
    obtain ⟨hzΩ, hzΩs⟩ := hz
    by_cases hz0 : z = 0
    · left; rw [hz0]; exact Submodule.zero_mem _
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have harg1 := Complex.neg_pi_lt_arg z
    have harg2 := Complex.arg_le_pi z
    rcases lt_trichotomy (arg z) 0 with hneg | hzero | hpos
    · rcases lt_trichotomy (arg z) (-(π / 5)) with h1 | h2 | h3
      · refine (hzΩ ⟨(‖z‖, arg z + 2 * π), ⟨hr, by linarith, by linarith⟩, ?_⟩).elim
        show (‖z‖ : ℂ) * exp (((arg z + 2 * π : ℝ) : ℂ) * I) = z
        push_cast
        rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
        exact hpol z
      · right
        exact Submodule.mem_span_singleton.mpr ⟨‖z‖, by rw [Complex.real_smul, ← h2]; exact hpol z⟩
      · exact (hzΩs ⟨(‖z‖, arg z), ⟨hr, h3, hneg⟩, hpol z⟩).elim
    · left
      refine Submodule.mem_span_singleton.mpr ⟨‖z‖, ?_⟩
      have h := hpol z
      rw [hzero] at h
      rw [Complex.real_smul, mul_one]
      simpa using h
    · exact (hzΩ ⟨(‖z‖, arg z), ⟨hr, hpos, by linarith⟩, hpol z⟩).elim
  have hKnull : volume K = 0 :=
    measure_mono_null hKsub (measure_union_null
      (Measure.addHaar_submodule _ _ (hspan 1 one_ne_zero))
      (Measure.addHaar_submodule _ _ (hspan _ (Complex.exp_ne_zero _))))
  set Φ : ℂ → ℂ := fun z => (1 / (z - p') - c) / a with hΦ
  have hΦd : DifferentiableOn ℝ Φ K := by
    intro z hz
    have hzp : z - p' ≠ 0 := sub_ne_zero.mpr fun h => hp'K (h ▸ hz)
    exact ((((differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const p') hzp).sub_const
      c).div_const a).restrictScalars ℝ |>.differentiableWithinAt
  have hΦnull : volume (Φ '' K) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hΦd hKnull
  refine measure_mono_null (fun w hw => ?_) (measure_union_null hΦnull (measure_singleton (-c / a)))
  by_cases hwc : a * w + c = 0
  · refine Or.inr (mem_singleton_iff.mpr ?_)
    field_simp
    linear_combination hwc
  refine Or.inl ?_
  set z := p' + 1 / (a * w + c) with hz
  have hzp : z - p' ≠ 0 := by rw [hz, add_sub_cancel_left]; exact one_div_ne_zero hwc
  have hΦz : 1 / (z - p') - c = a * w := by
    rw [hz, add_sub_cancel_left, one_div_one_div, add_sub_cancel_right]
  have hwa : a * w / a = w := by field_simp
  refine ⟨z, fun hzU => hw ?_, by show (1 / (z - p') - c) / a = w; rw [hΦz, hwa]⟩
  rcases hzU with hzΩ | hzΩs
  · have : 1 / (z - p') - c ∈ f '' unitDisc := by rw [hf.2.2]; exact ⟨z, hzΩ, rfl⟩
    obtain ⟨u, hu, hue⟩ := this
    exact Or.inl ⟨u, hu, by show f u / a = w; rw [hue, hΦz, hwa]⟩
  · have hzp' : z ≠ p' := sub_ne_zero.mp hzp
    have : 1 / (z - p') - c ∈ g '' unitDiscExterior := by
      rw [hg.2.2]; exact ⟨z, ⟨hzΩs, hzp'⟩, rfl⟩
    obtain ⟨u, hu, hue⟩ := this
    exact Or.inr ⟨u, hu, by show g u / a = w; rw [hue, hΦz, hwa]⟩

/-- Helper (D5 core): for a power series `φ` on `𝔻` with `Σ n|c_n|² < ∞`,
`∫⁻_𝔻 |φ'|² = π Σ n|c_n|²` (as a lintegral). -/
theorem s12_sd_lint_core {φ : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => c n * z ^ n) (φ z))
    (hsum : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖c (j + 1)‖ ^ 2)) :
    ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv φ z‖ ^ 2) =
      ENNReal.ofReal (π * ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖c (j + 1)‖ ^ 2) := by
  have hs' : ∀ z ∈ unitDisc,
      HasSum (fun n : ℕ => (c (n + 1) * ((n + 1 : ℕ) : ℂ)) * z ^ n) (deriv φ z) :=
    fun z hz => TakhtajanTeo.Ch2.faber_powerSeries_deriv hs hz
  have hterm : ∀ n : ℕ, π * ‖c (n + 1) * ((n + 1 : ℕ) : ℂ)‖ ^ 2 / ((n : ℝ) + 1) =
      π * (((n + 1 : ℕ) : ℝ) * ‖c (n + 1)‖ ^ 2) := by
    intro n
    rw [norm_mul, mul_pow, Complex.norm_natCast]
    push_cast
    field_simp
  have hsumm : Summable (fun n : ℕ => π * ‖c (n + 1) * ((n + 1 : ℕ) : ℂ)‖ ^ 2 / ((n : ℝ) + 1)) := by
    simp_rw [hterm]; exact hsum.mul_left π
  have hmem := TakhtajanTeo.Ch2.bergman_mem_A21_of_coeff hs' hsumm
  have hint : IntegrableOn (fun z => ‖deriv φ z‖ ^ 2) unitDisc := by
    refine ⟨(hmem.1.continuousOn.norm.pow 2).aestronglyMeasurable measurableSet_ball, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity)]
    have h := TakhtajanTeo.Ch2.a21_sq_lintegral_ne_top hmem
    refine lt_of_le_of_lt (le_of_eq ?_) h.lt_top
    apply lintegral_congr
    intro η
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rfl
  rw [← TakhtajanTeo.Ch2.r22_area_series hs hsum,
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => by positivity)]

/-- Helper (D5, `𝔻` side) for Proposition 12.4(d): `∫⁻_𝔻 |F'/F - 1/z|² = π Σ n|b_{-n,0}|²`. -/
theorem s12_sd_lint_f {F G : ℂ → ℂ} (h : TakhtajanTeo.Ch2.IsNormalizedDisjointPair F G)
    (hsum : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
      ‖TakhtajanTeo.Ch2.grunsky F G (-((j : ℤ) + 1)) 0‖ ^ 2)) :
    ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv F z / F z - 1 / z‖ ^ 2) =
      ENNReal.ofReal (π * ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) *
        ‖TakhtajanTeo.Ch2.grunsky F G (-((j : ℤ) + 1)) 0‖ ^ 2) := by
  obtain ⟨φ, hs, hf⟩ := TakhtajanTeo.Ch2.r22_f_series h
  have hφ := TakhtajanTeo.Ch2.differentiableOn_of_powerSeries hs
  have hnorm : ∀ j : ℕ, ‖(if j + 1 = 0 then (0 : ℂ) else
      -TakhtajanTeo.Ch2.grunsky F G (-((j + 1 : ℕ) : ℤ)) 0)‖ =
      ‖TakhtajanTeo.Ch2.grunsky F G (-((j : ℤ) + 1)) 0‖ := fun j => by
    rw [if_neg (Nat.succ_ne_zero j), norm_neg]
    push_cast
    rfl
  have hsum' : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
      ‖(if j + 1 = 0 then (0 : ℂ) else
        -TakhtajanTeo.Ch2.grunsky F G (-((j + 1 : ℕ) : ℤ)) 0)‖ ^ 2) := by
    simp_rw [hnorm]; exact hsum
  have hcore := s12_sd_lint_core hs hsum'
  simp_rw [hnorm] at hcore
  rw [← hcore]
  refine setLIntegral_congr_fun_ae measurableSet_ball ?_
  filter_upwards [(Set.countable_singleton (0 : ℂ)).ae_notMem volume] with z hz0 hz
  have hz0' : z ≠ 0 := hz0
  have hφd : DifferentiableAt ℂ φ z := hφ.differentiableAt (isOpen_ball.mem_nhds hz)
  have hfz : F z = z * Complex.exp (φ z) := hf z hz
  have hev : F =ᶠ[𝓝 z] fun w => w * Complex.exp (φ w) :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) (fun w hw => hf w hw)
  have h2 : HasDerivAt (fun w => w * Complex.exp (φ w))
      (1 * Complex.exp (φ z) + z * (Complex.exp (φ z) * deriv φ z)) z :=
    (hasDerivAt_id' z).mul hφd.hasDerivAt.cexp
  have hder : deriv F z = Complex.exp (φ z) * (1 + z * deriv φ z) := by
    rw [hev.deriv_eq, h2.deriv]; ring
  have hexp : Complex.exp (φ z) ≠ 0 := Complex.exp_ne_zero _
  have : deriv F z / F z - 1 / z = deriv φ z := by
    rw [hder, hfz]
    field_simp
    ring
  rw [this]

/-- Helper (D5, `𝔻*` side) for Proposition 12.4(d): `∫⁻_{𝔻*} |G'/G - 1/z|² = π Σ n|b_{n,0}|²`. -/
theorem s12_sd_lint_g {F G : ℂ → ℂ} (h : TakhtajanTeo.Ch2.IsNormalizedDisjointPair F G)
    (hsum : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
      ‖TakhtajanTeo.Ch2.grunsky F G ((j : ℤ) + 1) 0‖ ^ 2)) :
    ∫⁻ z in unitDiscExterior, ENNReal.ofReal (‖deriv G z / G z - 1 / z‖ ^ 2) =
      ENNReal.ofReal (π * ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) *
        ‖TakhtajanTeo.Ch2.grunsky F G ((j : ℤ) + 1) 0‖ ^ 2) := by
  obtain ⟨hexp, -, -, -, -⟩ := (TakhtajanTeo.Ch2.grunsky_spec h).1
  have hβ : TakhtajanTeo.derivAtInfty G ≠ 0 := by rw [← hexp]; exact Complex.exp_ne_zero _
  obtain ⟨φ, hs, hg⟩ := TakhtajanTeo.Ch2.r22_g_series h
  have hφ := TakhtajanTeo.Ch2.differentiableOn_of_powerSeries hs
  have hnorm : ∀ j : ℕ, ‖(if j + 1 = 0 then (0 : ℂ) else
      -TakhtajanTeo.Ch2.grunsky F G ((j + 1 : ℕ) : ℤ) 0)‖ =
      ‖TakhtajanTeo.Ch2.grunsky F G ((j : ℤ) + 1) 0‖ := fun j => by
    rw [if_neg (Nat.succ_ne_zero j), norm_neg]
    push_cast
    rfl
  have hsum' : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
      ‖(if j + 1 = 0 then (0 : ℂ) else
        -TakhtajanTeo.Ch2.grunsky F G ((j + 1 : ℕ) : ℤ) 0)‖ ^ 2) := by
    simp_rw [hnorm]; exact hsum
  have hcore := s12_sd_lint_core hs hsum'
  simp_rw [hnorm] at hcore
  rw [← hcore]
  have hDm : MeasurableSet (unitDisc \ {0}) := measurableSet_ball.diff (measurableSet_singleton 0)
  have himg : (fun u : ℂ => u⁻¹) '' (unitDisc \ {0}) = unitDiscExterior := by
    ext z
    constructor
    · rintro ⟨u, ⟨hu, hu0⟩, rfl⟩
      have hu0' : u ≠ 0 := hu0
      have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0'
      show 1 < ‖u⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ hpos).mpr (mem_ball_zero_iff.mp hu)
    · intro hz
      have hz1 : 1 < ‖z‖ := hz
      have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hz1; linarith
      exact ⟨z⁻¹, ⟨mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1),
        inv_ne_zero hz0⟩, inv_inv z⟩
  have hdiff : ∀ u ∈ unitDisc \ {0}, DifferentiableAt ℂ (fun w : ℂ => w⁻¹) u :=
    fun u hu => by exact differentiableAt_inv_iff.mpr hu.2
  rw [← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hDm
    (f' := fun u => fderiv ℝ (fun w : ℂ => w⁻¹) u)
    (fun u hu => ((hdiff u hu).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt)
    (fun a _ b _ hab => by simpa using hab)]
  have hae : (unitDisc \ {0} : Set ℂ) =ᵐ[volume] unitDisc :=
    diff_null_ae_eq_self (measure_singleton 0)
  rw [setLIntegral_congr hae.symm]
  refine setLIntegral_congr_fun hDm (fun u hu => ?_)
  obtain ⟨hu, hu0⟩ := hu
  have hu0' : u ≠ 0 := hu0
  have hgu := hg u hu hu0'
  have hder := TakhtajanTeo.Ch2.r22_g_deriv hφ hg hu hu0'
  have hexp' : Complex.exp (φ u) ≠ 0 := Complex.exp_ne_zero _
  have hC : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) u := hdiff u ⟨hu, hu0⟩
  have hdet : (fderiv ℝ (fun w : ℂ => w⁻¹) u).det = ‖deriv (fun w : ℂ => w⁻¹) u‖ ^ 2 := by
    have h1 := det_fderiv_eq_jacobian (hC.restrictScalars ℝ)
    rw [jacobian, (cauchyRiemann_iff.1 hC).2, dz_eq_deriv hC, norm_zero] at h1
    rw [ContinuousLinearMap.det, h1]
    ring
  have hval : deriv G u⁻¹ / G u⁻¹ - 1 / u⁻¹ = -(u ^ 2 * deriv φ u) := by
    rw [hder, hgu]
    field_simp
    ring
  rw [hdet, deriv_inv, hval, abs_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [norm_neg, norm_mul, norm_pow, norm_inv]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0'
  field_simp

/-- Proposition 12.4(d) `prop:sector`, (12.?) `eq:sector-dirichlet`, `sec12-counter.tex:253`: for
`p ∈ Ω` with `p♮ = p' ∈ Ωs`, `M(z) = 1/(z - p') - 1/(p - p')`, and conformal
`f : 𝔻 → M(Ω)`, `g : 𝔻* → M(Ωs)` with `f(0) = 0`, `g(∞) = ∞`: `f''(0) = 0` and
`∫_𝔻 |f'/f - 1/z|² + ∫_{𝔻*} |g'/g - 1/z|² = 2π δ(p, p♮)`.  (The paper states it along the
sequence of (b), for which the right side tends to `∞`; the proof applies to every such pair.) -/
theorem prop_sector_d {p p' : ℂ} (hp : p ∈ sectorΩ) (hp' : p' ∈ sectorΩs)
    (haw : awPoint sectorΩ p = (p' : OnePoint ℂ)) {f g : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc ((fun z => 1 / (z - p') - 1 / (p - p')) '' sectorΩ))
    (hf0 : f 0 = 0)
    (hg : IsConformalOnto g unitDiscExterior
      ((fun z => 1 / (z - p') - 1 / (p - p')) '' (sectorΩs \ {p'})))
    (hginf : Tendsto g (cocompact ℂ ⊓ 𝓟 unitDiscExterior) (cocompact ℂ)) :
    deriv (deriv f) 0 = 0 ∧
      (∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv f z / f z - 1 / z‖ ^ 2)) +
          ∫⁻ z in unitDiscExterior, ENNReal.ofReal (‖deriv g z / g z - 1 / z‖ ^ 2) =
        ENNReal.ofReal (2 * π * horoSpacing sectorΩ sectorΩs p p') := by
  have hΓ := s12_sec_jordan
  have hdisj := s02_jordanPair_disjoint hΓ
  have hp'Ω : p' ∉ sectorΩ := fun h => Set.disjoint_left.mp hdisj h hp'
  have hpΩs : p ∉ sectorΩs := fun h => Set.disjoint_left.mp hdisj hp h
  have hpp : p - p' ≠ 0 := sub_ne_zero.mpr fun h => hp'Ω (h ▸ hp)
  obtain ⟨ha, hpair⟩ := s12_sd_normal hΓ hp hp' hf hf0 hg hginf
  refine ⟨s12_sd_fpp hΓ hp hp' haw hf hf0, ?_⟩
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  -- the frame identity `δ = log |G'(∞)|`
  obtain ⟨hφ, hφ0, hd1, -⟩ := s12_sd_pull hp hp'Ω hf hf0
  obtain ⟨h, hh, hh0, hhd⟩ := s12_sd_push hpΩs hp' hg ha hpair
  set a := deriv f 0 with hadef
  set b := TakhtajanTeo.derivAtInfty (fun z => g z / a) with hb
  have hb0 : b ≠ 0 := by
    obtain ⟨hexp, -, -, -, -⟩ := (TakhtajanTeo.Ch2.grunsky_spec hpair).1
    rw [hb, ← hexp]; exact Complex.exp_ne_zero _
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnb : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have hnd : 0 < ‖p - p'‖ := norm_pos_iff.mpr hpp
  have hlam : poincareDensity sectorΩ p = 2 / (‖p - p'‖ ^ 2 * ‖a‖) := by
    have e := eq_lambda_f hφ h0
    rw [hφ0, hd1, norm_mul, norm_neg, norm_pow] at e
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      div_one] at e
    field_simp
    linarith
  have hlams : poincareDensity sectorΩs p' = 2 * (‖a‖ * ‖b‖) := by
    have e := eq_lambda_f hh h0
    rw [hh0, hhd] at e
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      div_one] at e
    field_simp at e
    linarith
  have hδ : horoSpacing sectorΩ sectorΩs p p' = Real.log ‖b‖ := by
    rw [(lem_spacing_a hΓ s12_sec_not_line hp hp').1, hlam, hlams]
    congr 1
    field_simp
    norm_num
  -- scale invariance of the integrands
  have hFf : ∀ z, deriv (fun w => f w / a) z / (f z / a) = deriv f z / f z := fun z => by
    rw [deriv_div_const, div_div_div_cancel_right₀ ha]
  have hGg : ∀ z, deriv (fun w => g w / a) z / (g z / a) = deriv g z / g z := fun z => by
    rw [deriv_div_const, div_div_div_cancel_right₀ ha]
  have hnull := s12_sd_null hp hp' hf hg ha
  obtain ⟨hs1, hs2, hsum⟩ := TakhtajanTeo.Ch2.r22_sum hpair hnull
  have hIf := s12_sd_lint_f hpair hs1
  have hIg := s12_sd_lint_g hpair hs2
  simp only [hFf, hGg] at hIf hIg
  rw [hIf, hIg, ← ENNReal.ofReal_add
    (mul_nonneg Real.pi_pos.le (tsum_nonneg fun j => by positivity))
    (mul_nonneg Real.pi_pos.le (tsum_nonneg fun j => by positivity)), ← mul_add, hsum,
    Real.log_pow, hδ]
  congr 1
  push_cast
  ring

/-- Remark `rem:sector-scope`(i), `sec12-counter.tex:354` (via Lemma `lem:width`): for the sector
curve, `d(X(p), U*)` is bounded on `Ω`. -/
theorem rem_sector_scope_i :
    ∃ D : ℝ, ∀ p ∈ sectorΩ, hdistSet (epstein sectorΩ p) (horoUnion sectorΩs) ≤ D := by
  -- Lemma `lem:width` with `K = 9` (Proposition `prop:sector`(a))
  obtain ⟨D, hD⟩ := lem_width 9
  exact ⟨D, (hD sectorΩ sectorΩs prop_sector_a.2.2.2.2 s12_sec_not_line).2.1⟩

/-- Remark `rem:sector-scope`(ii), `sec12-counter.tex:364`: for every Borel `κ ≥ 0` on `[0, ∞)`,
`∫_Ω κ(d_ρ(p, ·)) s² dâ ≤ (9/4) c_κ`, `c_κ = ∫_{ℍ²} κ(d(o, ·)) dâ` (computed in `𝔻`, `o = 0`). -/
theorem rem_sector_scope_ii {Ω : Set ℂ} (hΩ : ∃ φ : ℂ → ℂ, IsConformalOnto φ unitDisc Ω)
    {κ : ℝ → ℝ≥0∞} (hκ : Measurable κ) {p : ℂ} (hp : p ∈ Ω) :
    ∫⁻ w, κ (poincareDist Ω p w) ∂curvMass Ω ≤
      (9 / 4 : ℝ≥0∞) * ∫⁻ z in unitDisc,
        κ (diskDist 0 z) * ENNReal.ofReal (4 / (1 - ‖z‖ ^ 2) ^ 2) := by
  exact s12_curvMass_radial_le hΩ hκ hp


/-- Helper: the two components of a Jordan pair are disjoint. -/
theorem s12_scope_disj {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {x : ℂ} (hx : x ∈ Ωs) :
    x ∉ Ω := by
  obtain ⟨Φ, rfl, rfl⟩ := hΓ
  rintro ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hba⟩ := hx
  have hab : b = a := Φ.injective hba
  subst hab
  have h1 : (0 : ℝ) < b.im := ha
  have h2 : b.im < 0 := hb
  linarith

/-- Helper: undoing the frame `M(z) = 1/(z - w) - c` by `M⁻¹(u) = (w u + w c + 1)/(u + c)`: if
`φ : U → M(S)` is conformal (`w ∉ S`), then `M⁻¹ ∘ φ : U → S` is conformal and has the same
Schwarzian. -/
theorem s12_scope_conj {S U : Set ℂ} {w c : ℂ} (hU : IsOpen U) (hwS : w ∉ S) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ U ((fun z => 1 / (z - w) - c) '' S)) :
    IsConformalOnto (fun z => (w * φ z + (w * c + 1)) / (1 * φ z + c)) U S ∧
      ∀ z ∈ U, schwarzian (fun z => (w * φ z + (w * c + 1)) / (1 * φ z + c)) z =
        schwarzian φ z := by
  have hpre : ∀ z ∈ U, ∃ y ∈ S, φ z = 1 / (y - w) - c := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hφ.2.2 ▸ mem_image_of_mem φ hz
    exact ⟨y, hy, hyz.symm⟩
  have hval : ∀ z ∈ U, ∀ y ∈ S, φ z = 1 / (y - w) - c →
      (w * φ z + (w * c + 1)) / (1 * φ z + c) = y ∧ 1 * φ z + c ≠ 0 := by
    intro z _ y hy hyz
    have hyw : y - w ≠ 0 := sub_ne_zero.mpr fun h => hwS (h ▸ hy)
    have h1 : 1 * (1 / (y - w) - c) + c = 1 / (y - w) := by ring
    have h2 : w * (1 / (y - w) - c) + (w * c + 1) = y / (y - w) := by
      field_simp <;> ring
    rw [hyz, h1, h2]
    exact ⟨by field_simp, one_div_ne_zero hyw⟩
  have hden : ∀ z ∈ U, 1 * φ z + c ≠ 0 := fun z hz => by
    obtain ⟨y, hy, hyz⟩ := hpre z hz
    exact (hval z hz y hy hyz).2
  refine ⟨⟨fun z hz => ?_, fun a ha b hb hab => ?_, ?_⟩, fun z hz => ?_⟩
  · have hd := hφ.1 z hz
    exact ((hd.const_mul w).add_const _).div ((hd.const_mul 1).add_const c) (hden z hz)
  · obtain ⟨ya, hya, hyaz⟩ := hpre a ha
    obtain ⟨yb, hyb, hybz⟩ := hpre b hb
    have e1 := (hval a ha ya hya hyaz).1
    have e2 := (hval b hb yb hyb hybz).1
    have hy : ya = yb := by rw [← e1, ← e2]; exact hab
    exact hφ.2.1 ha hb (by rw [hyaz, hybz, hy])
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y', hy', hyz⟩ := hpre z hz
      have hv := (hval z hz y' hy' hyz).1
      simp only [hv]
      exact hy'
    · intro hy
      have hm : (fun z => 1 / (z - w) - c) y ∈ φ '' U := hφ.2.2 ▸ mem_image_of_mem _ hy
      obtain ⟨z, hz, hzy⟩ := hm
      exact ⟨z, hz, (hval z hz y hy hzy).1⟩
  · exact schwarzian_mobius_comp_analytic (hφ.1.analyticAt (hU.mem_nhds hz))
      (deriv_ne_zero_of_injOn hU hφ.1 hφ.2.1 hz)
      (by rw [show w * c - (w * c + 1) * 1 = -1 by ring]; norm_num)

/-- Helper: `𝓘(p) = ¼ ∫_𝔻 (1-|z|²)⁴ |S F|² dA` for a conformal `F : 𝔻 → Ω` with `F(0) = p`
(`k_p(F z) = 1 - |z|²`, and the weight `¼ |S F|² (1-|z|²)²` of `eq_pullback_mass_a`). -/
theorem s12_scope_pull {Ω : Set ℂ} {F : ℂ → ℂ} (hF : IsConformalOnto F unitDisc Ω) {p : ℂ}
    (hF0 : F 0 = p) :
    curvKernelInt Ω p = (1 / 4 : ℝ≥0∞) * ∫⁻ z in unitDisc,
      ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 4 * ‖schwarzian F z‖ ^ 2) := by
  classical
  subst hF0
  have hU : IsOpen unitDisc := isOpen_ball
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hΩm : MeasurableSet Ω := by
    rw [← hF.2.2]
    exact hD.image_of_continuousOn_injOn hF.1.continuousOn hF.2.1
  set G : ℂ → ℂ := Ω.piecewise (Function.invFunOn F unitDisc) 0 with hGdef
  have hGm : Measurable G :=
    ContinuousOn.measurable_piecewise (hF.symm hU).1.continuousOn continuousOn_const hΩm
  have hleft : ∀ z ∈ unitDisc, G (F z) = z := by
    intro z hz
    have hFz : F z ∈ Ω := hF.2.2 ▸ mem_image_of_mem F hz
    simp only [hGdef, Set.piecewise_eq_of_mem _ _ _ hFz]
    exact hF.2.1.leftInvOn_invFunOn hz
  set ψ : ℂ → ℝ≥0∞ := fun v => ENNReal.ofReal ((1 - ‖G v‖ ^ 2) ^ 2) with hψdef
  have hψm : Measurable ψ := by simp only [hψdef]; fun_prop
  have hk : ∀ z ∈ unitDisc, intrKernel Ω (F 0) (F z) = 1 - ‖z‖ ^ 2 := by
    intro z hz
    rw [s02_intrKernel_eq hF (mem_ball_self one_pos) hz]
    simp
  have hψF : ∀ z ∈ unitDisc, ψ (F z) = ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2) := by
    intro z hz
    simp only [hψdef, hleft z hz]
  have hae : ∀ᵐ v ∂curvMass Ω, ENNReal.ofReal (intrKernel Ω (F 0) v ^ 2) = ψ v := by
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩm)]
      with v hv
    rw [← hF.2.2] at hv
    obtain ⟨z, hz, rfl⟩ := hv
    rw [hψF z hz, hk z hz]
  have h4 : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [curvKernelInt, lintegral_congr_ae hae, eq_pullback_mass_a hF hψm,
    ← lintegral_const_mul' _ _ (ENNReal.div_ne_top (by simp) (by simp))]
  refine setLIntegral_congr_fun hD (fun z hz => ?_)
  rw [hψF z hz, ← ENNReal.ofReal_mul (by positivity), h4, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- Helper: `z ↦ 1/z` maps `𝔻*` onto the punctured disc. -/
theorem s12_scope_inv_image :
    (fun z : ℂ => z⁻¹) '' unitDiscExterior = ball (0 : ℂ) 1 \ {0} := by
  ext ζ
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz1 : 1 < ‖z‖ := hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
    refine ⟨?_, inv_ne_zero hz0⟩
    rw [mem_ball_zero_iff, norm_inv]
    exact inv_lt_one_of_one_lt₀ hz1
  · rintro ⟨hζ, hζ0⟩
    refine ⟨ζ⁻¹, ?_, inv_inv ζ⟩
    show 1 < ‖ζ⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hζ0)).mpr (mem_ball_zero_iff.mp hζ)

/-- Helper: `ζ ↦ 1/ζ` is a conformal map of the punctured disc onto `𝔻*`. -/
theorem s12_scope_inv_conf :
    IsConformalOnto (fun ζ : ℂ => ζ⁻¹) (ball (0 : ℂ) 1 \ {0}) unitDiscExterior := by
  refine ⟨fun ζ hζ => (differentiableAt_inv hζ.2).differentiableWithinAt,
    fun a _ b _ h => inv_injective h, ?_⟩
  rw [← s12_scope_inv_image, image_image]
  simp

/-- Helper: `S(g ∘ (1/·))(ζ) = S g(1/ζ) · (-ζ⁻²)²` on the punctured disc. -/
theorem s12_scope_schw_inv {g : ℂ → ℂ} {V : Set ℂ} (hg : IsConformalOnto g unitDiscExterior V)
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1 \ {0}) :
    schwarzian (fun ζ => g ζ⁻¹) ζ = schwarzian g ζ⁻¹ * (-(ζ ^ 2)⁻¹) ^ 2 := by
  have hζ0 : ζ ≠ 0 := hζ.2
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hz : ζ⁻¹ ∈ unitDiscExterior := s12_scope_inv_conf.mapsTo hζ
  have hiA : AnalyticAt ℂ (fun u : ℂ => u⁻¹) ζ := analyticAt_inv hζ0
  have hid : deriv (fun u : ℂ => u⁻¹) ζ = -(ζ ^ 2)⁻¹ := deriv_inv
  have hi' : deriv (fun u : ℂ => u⁻¹) ζ ≠ 0 := by rw [hid]; simpa using hζ0
  have hgA : AnalyticAt ℂ g ζ⁻¹ := hg.1.analyticAt (hO.mem_nhds hz)
  have hg0 : deriv g ζ⁻¹ ≠ 0 := deriv_ne_zero_of_injOn hO hg.1 hg.2.1 hz
  have hS : schwarzian (fun u : ℂ => u⁻¹) ζ = 0 := by
    have := schwarzian_mobius (a := 0) (b := 1) (c := 1) (d := 0) (by norm_num) ζ
    simpa using this
  have h := eq19_1_chain_rule hiA hi' hgA hg0
  rw [hS, add_zero, hid] at h
  exact h

/-- Helper: `M⁻¹(u) = (w u + b)/(u + e) → w` as `u → ∞`. -/
theorem s12_scope_minv_lim (w b e : ℂ) :
    Tendsto (fun u : ℂ => (w * u + b) / (1 * u + e)) (Bornology.cobounded ℂ) (𝓝 w) := by
  have h1 : Tendsto (fun t : ℂ => (w + b * t) / (1 + e * t)) (𝓝 0) (𝓝 w) := by
    have hc : ContinuousAt (fun t : ℂ => (w + b * t) / (1 + e * t)) 0 :=
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div
        (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) (by simp)
    simpa using hc.tendsto
  refine (h1.comp tendsto_inv₀_cobounded).congr' ?_
  have hne : ∀ᶠ u in Bornology.cobounded ℂ, u ≠ 0 := by
    rw [Metric.cobounded_eq_cocompact]
    exact isCompact_singleton.compl_mem_cocompact
  filter_upwards [hne] with u hu
  simp only [Function.comp]
  rw [← mul_div_mul_right (w * u + b) (1 * u + e) (inv_ne_zero hu)]
  congr 1 <;> field_simp <;> ring

/-- Helper (removable singularity): if `G` is conformal from the punctured disc onto `S ∖ {w}`
and `G → w` at `0`, then filling in `G(0) = w` gives a conformal map `𝔻 → S`.  The branch
`ζ = 0` is the value of the removable singularity, not a junk value. -/
theorem s12_scope_fill {G : ℂ → ℂ} {S : Set ℂ} {w : ℂ} (hw : w ∈ S)
    (hG : IsConformalOnto G (ball (0 : ℂ) 1 \ {0}) (S \ {w}))
    (hlim : Tendsto G (𝓝[≠] 0) (𝓝 w)) :
    IsConformalOnto (fun ζ => if ζ = 0 then w else G ζ) unitDisc S := by
  have hPo : IsOpen (ball (0 : ℂ) 1 \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hHG : ∀ ζ : ℂ, ζ ≠ 0 → (fun ζ => if ζ = 0 then w else G ζ) =ᶠ[𝓝 ζ] G := fun ζ hζ =>
    Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds hζ) fun y hy => if_neg hy
  have hGmem : ∀ ζ ∈ ball (0 : ℂ) 1 \ {0}, G ζ ∈ S \ {w} := fun ζ hζ =>
    hG.2.2 ▸ mem_image_of_mem G hζ
  refine ⟨?_, ?_, ?_⟩
  · refine (differentiableOn_compl_singleton_and_continuousAt_iff
      (ball_mem_nhds (0 : ℂ) one_pos)).mp ⟨fun ζ hζ => ?_, ?_⟩
    · exact ((hG.1.differentiableAt (hPo.mem_nhds hζ)).congr_of_eventuallyEq
        (hHG ζ hζ.2)).differentiableWithinAt
    · rw [← continuousWithinAt_compl_self, ContinuousWithinAt, if_pos rfl]
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ζ hζ
      exact (if_neg hζ).symm
  · intro a ha b hb hab
    by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0
    · rw [ha0, hb0]
    · simp only [if_pos ha0, if_neg hb0] at hab
      exact absurd hab.symm (hGmem b ⟨hb, hb0⟩).2
    · simp only [if_neg ha0, if_pos hb0] at hab
      exact absurd hab (hGmem a ⟨ha, ha0⟩).2
    · simp only [if_neg ha0, if_neg hb0] at hab
      exact hG.2.1 ⟨ha, ha0⟩ ⟨hb, hb0⟩ hab
  · ext y
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      by_cases h0 : ζ = 0
      · simp only [if_pos h0]
        exact hw
      · simp only [if_neg h0]
        exact (hGmem ζ ⟨hζ, h0⟩).1
    · intro hy
      by_cases hyw : y = w
      · exact ⟨0, mem_ball_self one_pos, by simp [hyw]⟩
      · have hm : y ∈ G '' (ball (0 : ℂ) 1 \ {0}) := hG.2.2 ▸ ⟨hy, hyw⟩
        obtain ⟨ζ, hζ, rfl⟩ := hm
        exact ⟨ζ, hζ.1, if_neg hζ.2⟩

/-- Helper: the inversion change of variables
`∫_{𝔻∖0} φ dA = ∫_{𝔻*} |z|⁻⁴ φ(1/z) dA(z)` (as `|−z⁻²|²`). -/
theorem s12_scope_cov (φ : ℂ → ℝ≥0∞) :
    ∫⁻ ζ in ball (0 : ℂ) 1 \ {0}, φ ζ =
      ∫⁻ z in unitDiscExterior, ENNReal.ofReal (‖-(z ^ 2)⁻¹‖ ^ 2) * φ z⁻¹ := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hder : ∀ z ∈ unitDiscExterior, HasFDerivWithinAt (fun u : ℂ => u⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z ^ 2)⁻¹)).restrictScalars ℝ)
      unitDiscExterior z := by
    intro z hz
    have hz1 : (1 : ℝ) < ‖z‖ := hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
    exact ((hasDerivAt_inv hz0).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [← s12_scope_inv_image, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    hO.measurableSet hder (fun a _ b _ h => inv_injective h)]
  refine setLIntegral_congr_fun hO.measurableSet fun z _ => ?_
  rw [s02_pullback_det, abs_of_nonneg (by positivity)]

/-- Remark `rem:sector-scope`(iii), `sec12-counter.tex:372–384`: in the frame
`M(z) = 1/(z - w) - 1/(p - w)` (`p ∈ Ω`, `w ∈ Ωs`), with conformal `f : 𝔻 → M(Ω)`, `f(0) = 0`,
and `g : 𝔻* → M(Ωs)`, `g(∞) = ∞`:
`𝓘(p) = ¼ ∫_𝔻 (1-|z|²)⁴ |S f|² dA` and `𝓘*(w) = ¼ ∫_{𝔻*} (|z|²-1)⁴ |z|⁻⁴ |S g|² dA`. -/
theorem rem_sector_scope_iii {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {p w : ℂ} (hp : p ∈ Ω)
    (hw : w ∈ Ωs) {f g : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc ((fun z => 1 / (z - w) - 1 / (p - w)) '' Ω)) (hf0 : f 0 = 0)
    (hg : IsConformalOnto g unitDiscExterior ((fun z => 1 / (z - w) - 1 / (p - w)) '' (Ωs \ {w})))
    (hginf : Tendsto g (cocompact ℂ ⊓ 𝓟 unitDiscExterior) (cocompact ℂ)) :
    curvKernelInt Ω p =
        (1 / 4 : ℝ≥0∞) * ∫⁻ z in unitDisc,
          ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 4 * ‖schwarzian f z‖ ^ 2) ∧
      curvKernelInt Ωs w =
        (1 / 4 : ℝ≥0∞) * ∫⁻ z in unitDiscExterior,
          ENNReal.ofReal ((‖z‖ ^ 2 - 1) ^ 4 / ‖z‖ ^ 4 * ‖schwarzian g z‖ ^ 2) := by
  have hwΩ : w ∉ Ω := s12_scope_disj hΓ hw
  have hpw : p - w ≠ 0 := sub_ne_zero.mpr fun h => hwΩ (h ▸ hp)
  constructor
  · -- `F = M⁻¹ ∘ f : 𝔻 → Ω`, `F(0) = p`, `S F = S f`
    obtain ⟨hF, hFS⟩ := s12_scope_conj isOpen_ball hwΩ hf
    have hF0 : (w * f 0 + (w * (1 / (p - w)) + 1)) / (1 * f 0 + 1 / (p - w)) = p := by
      rw [hf0]
      field_simp
      ring
    rw [s12_scope_pull hF hF0]
    congr 1
    exact setLIntegral_congr_fun measurableSet_ball fun z hz => by rw [hFS z hz]
  · -- `H = M⁻¹ ∘ g ∘ (1/·)` on the punctured disc, filled in by `H(0) = w`
    have hPo : IsOpen (ball (0 : ℂ) 1 \ {0}) := isOpen_ball.sdiff isClosed_singleton
    have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
    have hφ : IsConformalOnto (fun ζ : ℂ => g ζ⁻¹) (ball (0 : ℂ) 1 \ {0})
        ((fun z => 1 / (z - w) - 1 / (p - w)) '' (Ωs \ {w})) := hg.comp s12_scope_inv_conf
    obtain ⟨hG, hGS⟩ := s12_scope_conj hPo (fun h : w ∈ Ωs \ {w} => h.2 rfl) hφ
    set G : ℂ → ℂ := fun ζ => (w * g ζ⁻¹ + (w * (1 / (p - w)) + 1)) / (1 * g ζ⁻¹ + 1 / (p - w))
      with hGdef
    have hlim : Tendsto G (𝓝[≠] 0) (𝓝 w) := by
      have hinv : Tendsto (fun ζ : ℂ => ζ⁻¹) (𝓝[≠] 0) (cocompact ℂ ⊓ 𝓟 unitDiscExterior) := by
        refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩
        · rw [← Metric.cobounded_eq_cocompact]
          exact tendsto_inv₀_nhdsNE_zero
        · filter_upwards [inter_mem_nhdsWithin ({0}ᶜ : Set ℂ) (ball_mem_nhds (0 : ℂ) one_pos)]
            with ζ hζ
          exact s12_scope_inv_conf.mapsTo ⟨hζ.2, hζ.1⟩
      have hg' : Tendsto g (cocompact ℂ ⊓ 𝓟 unitDiscExterior) (Bornology.cobounded ℂ) := by
        rw [Metric.cobounded_eq_cocompact]
        exact hginf
      exact (s12_scope_minv_lim w (w * (1 / (p - w)) + 1) (1 / (p - w))).comp (hg'.comp hinv)
    have hH := s12_scope_fill hw hG hlim
    have hHS : ∀ ζ ∈ ball (0 : ℂ) 1 \ {0},
        schwarzian (fun ζ => if ζ = 0 then w else G ζ) ζ =
          schwarzian g ζ⁻¹ * (-(ζ ^ 2)⁻¹) ^ 2 := by
      intro ζ hζ
      rw [schwarzian_congr (g := G), hGS ζ hζ, s12_scope_schw_inv hg hζ]
      exact (Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds hζ.2)
        fun y hy => if_neg hy).filter_mono nhdsWithin_le_nhds
    rw [s12_scope_pull hH (by simp)]
    congr 1
    have hnull : (ball (0 : ℂ) 1 \ {0} : Set ℂ) =ᵐ[volume] ball (0 : ℂ) 1 :=
      sdiff_null_ae_eq_self (measure_singleton 0)
    calc ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 4 *
            ‖schwarzian (fun ζ => if ζ = 0 then w else G ζ) z‖ ^ 2)
        = ∫⁻ ζ in ball (0 : ℂ) 1 \ {0}, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) ^ 4 *
            ‖schwarzian (fun ζ => if ζ = 0 then w else G ζ) ζ‖ ^ 2) :=
          (setLIntegral_congr hnull).symm
      _ = ∫⁻ ζ in ball (0 : ℂ) 1 \ {0}, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) ^ 4 *
            ‖schwarzian g ζ⁻¹ * (-(ζ ^ 2)⁻¹) ^ 2‖ ^ 2) :=
          setLIntegral_congr_fun hPo.measurableSet fun ζ hζ => by rw [hHS ζ hζ]
      _ = ∫⁻ z in unitDiscExterior, ENNReal.ofReal (‖-(z ^ 2)⁻¹‖ ^ 2) *
            ENNReal.ofReal ((1 - ‖z⁻¹‖ ^ 2) ^ 4 *
              ‖schwarzian g z⁻¹⁻¹ * (-((z⁻¹) ^ 2)⁻¹) ^ 2‖ ^ 2) :=
          s12_scope_cov _
      _ = ∫⁻ z in unitDiscExterior,
            ENNReal.ofReal ((‖z‖ ^ 2 - 1) ^ 4 / ‖z‖ ^ 4 * ‖schwarzian g z‖ ^ 2) := by
          refine setLIntegral_congr_fun hO.measurableSet fun z hz => ?_
          have hz1 : (1 : ℝ) < ‖z‖ := hz
          have hr : ‖z‖ ≠ 0 := (by linarith : (0 : ℝ) < ‖z‖).ne'
          rw [inv_inv, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          simp only [norm_mul, norm_pow, norm_neg, norm_inv]
          field_simp

/-! ## The linearized inequality (Remark `rem:linear-spacing`) -/

/-- The polynomial `u(z) = Σ_{n=2}^{N} a_n z^{n+1}`. -/
def linPoly (N : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑ n ∈ Finset.Icc 2 N, a n * z ^ (n + 1)

/-- `𝒟(f) = ∫_𝔻 |f'/f - 1/z|² dA`. -/
def dirichletDefect (f : ℂ → ℂ) : ℝ := ∫ z in unitDisc, ‖deriv f z / f z - 1 / z‖ ^ 2

/-- `𝓘(f) = ¼ ∫_𝔻 (1-|z|²)⁴ |S f|² dA`. -/
def interiorCurvInt (f : ℂ → ℂ) : ℝ :=
  (1 / 4) * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 4 * ‖schwarzian f z‖ ^ 2

/-- Remark `rem:linear-spacing`, `sec12-counter.tex:398`: if `|ε| sup_{𝔻̄} |u'| < 1`, then
`f_ε = z + ε u` is univalent on `𝔻̄`. -/
theorem rem_linear_spacing_univalent (N : ℕ) (a : ℕ → ℂ) {ε : ℂ}
    (hε : ∀ z ∈ closedBall (0 : ℂ) 1, ‖ε‖ * ‖deriv (linPoly N a) z‖ < 1) :
    InjOn (fun z => z + ε * linPoly N a z) (closedBall 0 1) := by
  have hu : ContDiff ℂ 1 (linPoly N a) := by
    unfold linPoly
    exact ContDiff.sum fun n _ => by fun_prop
  have hdiff : Differentiable ℂ (linPoly N a) := hu.differentiable (by norm_num)
  have hcont : Continuous (deriv (linPoly N a)) := hu.continuous_deriv le_rfl
  obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn
    (nonempty_closedBall.mpr zero_le_one) (by fun_prop : Continuous fun z =>
      ‖ε‖ * ‖deriv (linPoly N a) z‖).continuousOn
  set M := ‖ε‖ * ‖deriv (linPoly N a) z₀‖ with hM
  have hM1 : M < 1 := hε z₀ hz₀
  intro z hz w hw hzw
  simp only at hzw
  have hb : ‖ε * linPoly N a z - ε * linPoly N a w‖ ≤ M * ‖z - w‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le (f := fun z => ε * linPoly N a z)
      (fun x _ => (hdiff x).const_mul ε) (fun x hx => ?_) (convex_closedBall 0 1) hw hz
    rw [deriv_const_mul _ (hdiff x), norm_mul]
    exact hmax hx
  have he : z - w = ε * linPoly N a w - ε * linPoly N a z := by linear_combination hzw
  have h1 : ‖z - w‖ ≤ M * ‖z - w‖ :=
    calc ‖z - w‖ = ‖ε * linPoly N a z - ε * linPoly N a w‖ := by rw [he, norm_sub_rev]
      _ ≤ M * ‖z - w‖ := hb
  have h0 : ‖z - w‖ = 0 := by
    have := norm_nonneg (z - w)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

theorem s12_radial_one (k : ℕ) :
    ∫ r in (0 : ℝ)..1, r * r ^ (2 * k) = 1 / (2 * (k : ℝ) + 2) := by
  have h : (fun r : ℝ => r * r ^ (2 * k)) = fun r => r ^ (2 * k + 1) := by
    funext r
    ring
  rw [h, integral_pow]
  push_cast
  rw [one_pow, zero_pow (by omega)]
  ring

theorem s12_radial_four (k : ℕ) :
    ∫ r in (0 : ℝ)..1, r * (1 - r ^ 2) ^ 4 * r ^ (2 * k) =
      12 / (((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) * ((k : ℝ) + 4) * ((k : ℝ) + 5)) := by
  have hi (j : ℕ) : IntervalIntegrable (fun r : ℝ => r ^ j) volume 0 1 :=
    (continuous_pow j).intervalIntegrable _ _
  have hpoly : (fun r : ℝ => r * (1 - r ^ 2) ^ 4 * r ^ (2 * k)) = fun r =>
      r ^ (2 * k + 1) - 4 * r ^ (2 * k + 3) + 6 * r ^ (2 * k + 5) - 4 * r ^ (2 * k + 7) +
        r ^ (2 * k + 9) := by
    funext r
    simp only [pow_add]
    ring
  rw [hpoly, intervalIntegral.integral_add ((((hi _).sub ((hi _).const_mul 4)).add
      ((hi _).const_mul 6)).sub ((hi _).const_mul 4)) (hi _),
    intervalIntegral.integral_sub (((hi _).sub ((hi _).const_mul 4)).add ((hi _).const_mul 6))
      ((hi _).const_mul 4),
    intervalIntegral.integral_add ((hi _).sub ((hi _).const_mul 4)) ((hi _).const_mul 6),
    intervalIntegral.integral_sub (hi _) ((hi _).const_mul 4),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  simp only [integral_pow, one_pow, ne_eq, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
    not_false_eq_true, zero_pow, sub_zero]
  push_cast
  field_simp
  ring

theorem s12_monoSum_norm_le (s : Finset ℕ) (c : ℕ → ℂ) (e : ℕ → ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖∑ n ∈ s, c n * z ^ e n‖ ≤ ∑ n ∈ s, ‖c n‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

theorem s12_hasDerivAt_monoSum (s : Finset ℕ) (c c' : ℕ → ℂ) (e e' : ℕ → ℕ) (z : ℂ)
    (h : ∀ n ∈ s, c n * ((e n : ℂ) * z ^ (e n - 1)) = c' n * z ^ e' n) :
    HasDerivAt (fun w => ∑ n ∈ s, c n * w ^ e n) (∑ n ∈ s, c' n * z ^ e' n) z :=
  (HasDerivAt.fun_sum fun n _ => (hasDerivAt_pow (e n) z).const_mul (c n)).congr_deriv
    (Finset.sum_congr rfl h)

/-- Helper: `|e²|x|²/|1+ey|² - e²|x|²| ≤ 10 K³ |e|³`. -/
theorem s12_ratio_bound {x y : ℂ} {K e : ℝ} (hK : 0 ≤ K) (hx : ‖x‖ ≤ K) (hy : ‖y‖ ≤ K)
    (he : |e| * K ≤ 1 / 2) :
    |e ^ 2 * ‖x‖ ^ 2 / ‖1 + (e : ℂ) * y‖ ^ 2 - e ^ 2 * ‖x‖ ^ 2| ≤ 10 * K ^ 3 * |e| ^ 3 := by
  have hey : ‖(e : ℂ) * y‖ ≤ |e| * K := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg e)
  obtain ⟨t, ht⟩ : ∃ t, t = ‖1 + (e : ℂ) * y‖ := ⟨_, rfl⟩
  rw [← ht]
  have htb : |t - 1| ≤ |e| * K := by
    have := abs_norm_sub_norm_le (1 + (e : ℂ) * y) 1
    rw [norm_one, add_sub_cancel_left, ← ht] at this
    linarith
  have ht1 : 1 / 2 ≤ t := by linarith [(abs_le.mp htb).1]
  have ht2 : t ≤ 3 / 2 := by linarith [(abs_le.mp htb).2]
  have htp : 0 < t := by linarith
  have ht0 : 0 < t ^ 2 := by positivity
  have ht14 : 1 / 4 ≤ t ^ 2 := by nlinarith
  have e1 : e ^ 2 * ‖x‖ ^ 2 / t ^ 2 - e ^ 2 * ‖x‖ ^ 2 =
      e ^ 2 * ‖x‖ ^ 2 * ((1 - t ^ 2) / t ^ 2) := by
    field_simp
  have hek : 0 ≤ |e| * K := mul_nonneg (abs_nonneg e) hK
  rw [e1, abs_mul, abs_of_nonneg (by positivity), abs_div, abs_of_pos ht0]
  have h1 : |1 - t ^ 2| ≤ 5 / 2 * (|e| * K) := by
    rw [show 1 - t ^ 2 = -((t - 1) * (1 + t)) by ring, abs_neg, abs_mul,
      abs_of_pos (by linarith : (0 : ℝ) < 1 + t)]
    calc |t - 1| * (1 + t) ≤ (|e| * K) * (5 / 2) :=
          mul_le_mul htb (by linarith) (by linarith) hek
      _ = 5 / 2 * (|e| * K) := by ring
  have h2 : |1 - t ^ 2| / t ^ 2 ≤ 10 * (|e| * K) := by
    rw [div_le_iff₀ ht0]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht14) hek]
  have h3 : e ^ 2 * ‖x‖ ^ 2 ≤ |e| ^ 2 * K ^ 2 := by
    rw [sq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2) (sq_nonneg _)
  calc e ^ 2 * ‖x‖ ^ 2 * (|1 - t ^ 2| / t ^ 2) ≤ |e| ^ 2 * K ^ 2 * (10 * (|e| * K)) :=
        mul_le_mul h3 h2 (by positivity) (by positivity)
    _ = 10 * K ^ 3 * |e| ^ 3 := by ring

/-- Helper: `|S|² = e²|u₃|² + O(e³)` for `S = e u₃/(1+e u₁) - (3/2)(e u₂)²/(1+e u₁)²`. -/
theorem s12_schw_bound {u1 u2 u3 : ℂ} {K e : ℝ} (hK : 0 ≤ K) (h1 : ‖u1‖ ≤ K) (h2 : ‖u2‖ ≤ K)
    (h3 : ‖u3‖ ≤ K) (he : |e| * K ≤ 1 / 2) :
    |‖(e : ℂ) * u3 / (1 + (e : ℂ) * u1) - 3 / 2 * ((e : ℂ) * u2) ^ 2 / (1 + (e : ℂ) * u1) ^ 2‖ ^ 2
      - e ^ 2 * ‖u3‖ ^ 2| ≤ 48 * K ^ 3 * |e| ^ 3 := by
  have hne : ‖(e : ℂ)‖ = |e| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hek : 0 ≤ |e| * K := mul_nonneg (abs_nonneg e) hK
  have hd : 1 / 2 ≤ ‖1 + (e : ℂ) * u1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-((e : ℂ) * u1))
    rw [sub_neg_eq_add, norm_neg, norm_one, norm_mul, hne] at h
    nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg e)]
  have hd0 : 1 + (e : ℂ) * u1 ≠ 0 := fun h => by
    rw [h, norm_zero] at hd
    norm_num at hd
  have hn32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
    rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hsq : e ^ 2 * K ^ 2 = (|e| * K) ^ 2 := by rw [mul_pow, sq_abs]
  have hid : (e : ℂ) * u3 / (1 + (e : ℂ) * u1) - 3 / 2 * ((e : ℂ) * u2) ^ 2 / (1 + (e : ℂ) * u1) ^ 2
      - (e : ℂ) * u3 = -((e : ℂ) ^ 2 * u3 * u1) / (1 + (e : ℂ) * u1) -
        3 / 2 * ((e : ℂ) * u2) ^ 2 / (1 + (e : ℂ) * u1) ^ 2 := by
    field_simp
    ring
  have hA : ‖-((e : ℂ) ^ 2 * u3 * u1) / (1 + (e : ℂ) * u1)‖ ≤ 2 * (e ^ 2 * K ^ 2) := by
    rw [norm_div, norm_neg, norm_mul, norm_mul, norm_pow, hne, sq_abs,
      div_le_iff₀ (by linarith)]
    have h31 : ‖u3‖ * ‖u1‖ ≤ K * K := mul_le_mul h3 h1 (norm_nonneg _) hK
    have := mul_le_mul_of_nonneg_left h31 (sq_nonneg e)
    nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ e ^ 2 * K ^ 2)]
  have hB : ‖3 / 2 * ((e : ℂ) * u2) ^ 2 / (1 + (e : ℂ) * u1) ^ 2‖ ≤ 6 * (e ^ 2 * K ^ 2) := by
    rw [norm_div, norm_mul, hn32, norm_pow, norm_pow, norm_mul, hne,
      div_le_iff₀ (by have : 0 < ‖1 + (e : ℂ) * u1‖ := by linarith
                      positivity)]
    have h22 : ‖u2‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have hd2 : 1 / 4 ≤ ‖1 + (e : ℂ) * u1‖ ^ 2 := by nlinarith
    rw [mul_pow, sq_abs]
    nlinarith [mul_le_mul_of_nonneg_left h22 (sq_nonneg e),
      mul_le_mul_of_nonneg_left hd2 (by positivity : (0 : ℝ) ≤ e ^ 2 * K ^ 2)]
  have hR : ‖(e : ℂ) * u3 / (1 + (e : ℂ) * u1) - 3 / 2 * ((e : ℂ) * u2) ^ 2 /
      (1 + (e : ℂ) * u1) ^ 2 - (e : ℂ) * u3‖ ≤ 8 * (e ^ 2 * K ^ 2) := by
    rw [hid]
    refine (norm_sub_le _ _).trans ?_
    linarith
  obtain ⟨A, hAd⟩ : ∃ A, A = ‖(e : ℂ) * u3 / (1 + (e : ℂ) * u1) - 3 / 2 * ((e : ℂ) * u2) ^ 2 /
      (1 + (e : ℂ) * u1) ^ 2‖ := ⟨_, rfl⟩
  have hab : |A - ‖(e : ℂ) * u3‖| ≤ 8 * (e ^ 2 * K ^ 2) := by
    rw [hAd]
    exact (abs_norm_sub_norm_le _ _).trans hR
  have hb : ‖(e : ℂ) * u3‖ = |e| * ‖u3‖ := by rw [norm_mul, hne]
  rw [← hAd, show e ^ 2 * ‖u3‖ ^ 2 = ‖(e : ℂ) * u3‖ ^ 2 by rw [hb, mul_pow, sq_abs]]
  have hbK : ‖(e : ℂ) * u3‖ ≤ |e| * K := by
    rw [hb]
    exact mul_le_mul_of_nonneg_left h3 (abs_nonneg e)
  have hA0 : 0 ≤ A := by rw [hAd]; exact norm_nonneg _
  have hsmall : 8 * (e ^ 2 * K ^ 2) ≤ 4 * (|e| * K) := by
    rw [hsq]
    nlinarith
  rw [show A ^ 2 - ‖(e : ℂ) * u3‖ ^ 2 = (A - ‖(e : ℂ) * u3‖) * (A + ‖(e : ℂ) * u3‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg hA0 (norm_nonneg _))]
  have hapb : A + ‖(e : ℂ) * u3‖ ≤ 6 * (|e| * K) := by
    have := (abs_le.mp hab).2
    linarith
  calc |A - ‖(e : ℂ) * u3‖| * (A + ‖(e : ℂ) * u3‖) ≤ (8 * (e ^ 2 * K ^ 2)) * (6 * (|e| * K)) :=
        mul_le_mul hab hapb (add_nonneg hA0 (norm_nonneg _)) (by positivity)
    _ = 48 * K ^ 3 * |e| ^ 3 := by rw [← sq_abs e]; ring

/-- Remark `rem:linear-spacing`, `sec12-counter.tex:411–426`: `𝒟(f_ε) = ε² 𝒟₂ + O(ε³)` and
`𝓘(f_ε) = ε² 𝓘₂ + O(ε³)`, with `𝒟₂ = π Σ n |a_n|²` and
`𝓘₂ = 6π Σ n(n²-1)/((n+2)(n+3)) |a_n|²`. -/
theorem rem_linear_spacing_expansion (N : ℕ) (a : ℕ → ℂ) :
    (fun ε : ℝ => dirichletDefect (fun z => z + ε * linPoly N a z) -
        ε ^ 2 * (π * ∑ n ∈ Finset.Icc 2 N, (n : ℝ) * ‖a n‖ ^ 2)) =O[𝓝 0] (fun ε => ε ^ 3) ∧
      (fun ε : ℝ => interiorCurvInt (fun z => z + ε * linPoly N a z) -
        ε ^ 2 * (6 * π * ∑ n ∈ Finset.Icc 2 N,
          (n : ℝ) * ((n : ℝ) ^ 2 - 1) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) * ‖a n‖ ^ 2))
        =O[𝓝 0] (fun ε => ε ^ 3) := by
  set s := Finset.Icc 2 N with hs
  have hs2 : ∀ n ∈ s, 2 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  set cq : ℕ → ℂ := fun n => a n * ((n : ℝ) : ℂ) with hcq
  set c1 : ℕ → ℂ := fun n => a n * (((n : ℝ) + 1 : ℝ) : ℂ) with hc1
  set c2 : ℕ → ℂ := fun n => a n * ((((n : ℝ) + 1) * n : ℝ) : ℂ) with hc2
  set c3 : ℕ → ℂ := fun n => a n * ((((n : ℝ) + 1) * n * ((n : ℝ) - 1) : ℝ) : ℂ) with hc3
  set v : ℂ → ℂ := fun z => ∑ n ∈ s, a n * z ^ n with hv
  set q : ℂ → ℂ := fun z => ∑ n ∈ s, cq n * z ^ (n - 1) with hq
  set u1 : ℂ → ℂ := fun z => ∑ n ∈ s, c1 n * z ^ n with hu1
  set u2 : ℂ → ℂ := fun z => ∑ n ∈ s, c2 n * z ^ (n - 1) with hu2
  set u3 : ℂ → ℂ := fun z => ∑ n ∈ s, c3 n * z ^ (n - 2) with hu3
  -- derivatives
  have hd0 : ∀ z, HasDerivAt (linPoly N a) (u1 z) z := fun z =>
    s12_hasDerivAt_monoSum s a c1 (fun n => n + 1) (fun n => n) z fun n _ => by
      simp only [hc1, Nat.add_sub_cancel]
      push_cast
      ring
  have hd1 : ∀ z, HasDerivAt u1 (u2 z) z := fun z =>
    s12_hasDerivAt_monoSum s c1 c2 (fun n => n) (fun n => n - 1) z fun n _ => by
      simp only [hc1, hc2]
      push_cast
      ring
  have hd2 : ∀ z, HasDerivAt u2 (u3 z) z := fun z =>
    s12_hasDerivAt_monoSum s c2 c3 (fun n => n - 1) (fun n => n - 2) z fun n hn => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := hs2 n hn; omega⟩
      simp only [hc2, hc3, show m + 2 - 1 - 1 = m by omega, show m + 2 - 2 = m by omega,
        show m + 2 - 1 = m + 1 by omega, Nat.add_sub_cancel]
      push_cast
      ring
  have hlin : ∀ z, linPoly N a z = z * v z := fun z => by
    simp only [linPoly, hv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hu1v : ∀ z, u1 z = v z + z * q z := fun z => by
    simp only [hu1, hv, hq, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := hs2 n hn; omega⟩
    simp only [hc1, hcq, show m + 2 - 1 = m + 1 by omega]
    push_cast
    ring
  -- continuity and bounds
  have hvc : Continuous v := by
    simp only [hv]
    exact continuous_finsetSum _ fun n _ => by fun_prop
  have hqc : Continuous q := by
    simp only [hq]
    exact continuous_finsetSum _ fun n _ => by fun_prop
  have hu1c : Continuous u1 := by
    simp only [hu1]
    exact continuous_finsetSum _ fun n _ => by fun_prop
  have hu2c : Continuous u2 := by
    simp only [hu2]
    exact continuous_finsetSum _ fun n _ => by fun_prop
  have hu3c : Continuous u3 := by
    simp only [hu3]
    exact continuous_finsetSum _ fun n _ => by fun_prop
  have hS0 : ∀ c : ℕ → ℂ, 0 ≤ ∑ n ∈ s, ‖c n‖ := fun c => Finset.sum_nonneg fun n _ => norm_nonneg _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∑ n ∈ s, ‖a n‖ + ∑ n ∈ s, ‖cq n‖ + ∑ n ∈ s, ‖c1 n‖ +
      ∑ n ∈ s, ‖c2 n‖ + ∑ n ∈ s, ‖c3 n‖ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by linarith [hS0 a, hS0 cq, hS0 c1, hS0 c2, hS0 c3]
  have hvK : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖v z‖ ≤ K := fun z hz =>
    (s12_monoSum_norm_le s a (fun n => n) hz).trans
      (by linarith [hS0 a, hS0 cq, hS0 c1, hS0 c2, hS0 c3])
  have hqK : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖q z‖ ≤ K := fun z hz =>
    (s12_monoSum_norm_le s cq (fun n => n - 1) hz).trans
      (by linarith [hS0 a, hS0 cq, hS0 c1, hS0 c2, hS0 c3])
  have hu1K : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖u1 z‖ ≤ K := fun z hz =>
    (s12_monoSum_norm_le s c1 (fun n => n) hz).trans
      (by linarith [hS0 a, hS0 cq, hS0 c1, hS0 c2, hS0 c3])
  have hu2K : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖u2 z‖ ≤ K := fun z hz =>
    (s12_monoSum_norm_le s c2 (fun n => n - 1) hz).trans
      (by linarith [hS0 a, hS0 cq, hS0 c1, hS0 c2, hS0 c3])
  have hu3K : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖u3 z‖ ≤ K := fun z hz =>
    (s12_monoSum_norm_le s c3 (fun n => n - 2) hz).trans
      (by linarith [hS0 a, hS0 cq, hS0 c1, hS0 c2, hS0 c3])
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, |ε| * K ≤ 1 / 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / (2 * K + 1) by positivity)]
      with ε hε
    rw [mem_ball, Real.dist_eq, sub_zero] at hε
    have h1 := mul_le_mul_of_nonneg_right hε.le hK0
    have h2 : 1 / (2 * K + 1) * K ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hcont : ∀ g : ℂ → ℝ, ContinuousOn g (closedBall 0 1) → IntegrableOn g unitDisc :=
    fun g hg => (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1) hg).mono_set
      ball_subset_closedBall
  have hnear : ∀ (ε : ℝ) (w : ℂ), |ε| * K ≤ 1 / 2 → ‖w‖ ≤ K → 1 / 2 ≤ ‖1 + (ε : ℂ) * w‖ :=
    fun ε w hε hw => by
      have h1 : ‖(ε : ℂ) * w‖ ≤ |ε| * K := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hw (abs_nonneg ε)
      have h2 := norm_sub_norm_le (1 : ℂ) (-((ε : ℂ) * w))
      rw [sub_neg_eq_add, norm_neg, norm_one] at h2
      linarith
  set V : ℝ := (volume : Measure ℂ).real unitDisc with hV
  -- Parseval
  have hinj1 : InjOn (fun n : ℕ => n - 1) s := fun x hx y hy h => by
    have := hs2 x hx
    have := hs2 y hy
    simp only at h
    omega
  have hinj2 : InjOn (fun n : ℕ => n - 2) s := fun x hx y hy h => by
    have := hs2 x hx
    have := hs2 y hy
    simp only at h
    omega
  have hqP : ∫ z in unitDisc, ‖q z‖ ^ 2 = π * ∑ n ∈ s, (n : ℝ) * ‖a n‖ ^ 2 := by
    have h := s12_disc_parseval (fun _ => 1) continuous_const s (fun n => n - 1) hinj1 cq q
      (fun z => rfl)
    beta_reduce at h
    simp only [one_mul, mul_one] at h
    rw [h, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := hs2 n hn; omega⟩
    rw [show m + 2 - 1 = m + 1 by omega, s12_radial_one]
    simp only [hcq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    push_cast
    rw [abs_of_nonneg (by positivity)]
    field_simp
    ring
  have hu3P : (1 / 4) * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 4 * ‖u3 z‖ ^ 2 =
      6 * π * ∑ n ∈ s,
        (n : ℝ) * ((n : ℝ) ^ 2 - 1) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) * ‖a n‖ ^ 2 := by
    have h := s12_disc_parseval (fun r => (1 - r ^ 2) ^ 4) (by fun_prop) s (fun n => n - 2)
      hinj2 c3 u3 (fun z => rfl)
    beta_reduce at h
    rw [h, ← mul_assoc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := hs2 n hn; omega⟩
    rw [show m + 2 - 2 = m by omega, s12_radial_four]
    simp only [hc3, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) + 1),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ)),
      abs_of_nonneg (by push_cast; linarith : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) - 1)]
    push_cast
    field_simp
    ring
  refine ⟨Asymptotics.IsBigO.of_bound (10 * K ^ 3 * V) ?_,
    Asymptotics.IsBigO.of_bound (12 * K ^ 3 * V) ?_⟩
  · filter_upwards [hev] with ε hε
    set f : ℂ → ℂ := fun z => z + (ε : ℂ) * linPoly N a z with hfdef
    have hfd : ∀ z, HasDerivAt f (1 + (ε : ℂ) * u1 z) z := fun z =>
      (hasDerivAt_id' z).add ((hd0 z).const_mul (ε : ℂ))
    set G : ℂ → ℝ := fun z => ε ^ 2 * ‖q z‖ ^ 2 / ‖1 + (ε : ℂ) * v z‖ ^ 2 with hG
    have hq0 : q 0 = 0 := by
      simp only [hq]
      exact Finset.sum_eq_zero fun n hn => by
        rw [zero_pow (by have := hs2 n hn; omega), mul_zero]
    have hint : EqOn (fun z => ‖deriv f z / f z - 1 / z‖ ^ 2) G unitDisc := by
      intro z hz
      show ‖deriv f z / f z - 1 / z‖ ^ 2 = G z
      have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
      have hd : 1 + (ε : ℂ) * v z ≠ 0 := fun h => by
        have := hnear ε (v z) hε (hvK z hz1)
        rw [h, norm_zero] at this
        norm_num at this
      by_cases hz0 : z = 0
      · subst hz0
        have : f 0 = 0 := by simp [hfdef, hlin]
        simp [hG, this, hq0]
      · rw [(hfd z).deriv]
        have hfz : f z = z * (1 + (ε : ℂ) * v z) := by
          simp only [hfdef, hlin]
          ring
        have e : (1 + (ε : ℂ) * u1 z) / f z - 1 / z = (ε : ℂ) * q z / (1 + (ε : ℂ) * v z) := by
          rw [hfz, hu1v]
          field_simp
          ring
        simp only [hG]
        rw [e, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, div_pow, mul_pow, sq_abs]
    have hGi : IntegrableOn G unitDisc := by
      refine hcont G (ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_)
      have := hnear ε (v z) hε (hvK z (mem_closedBall_zero_iff.mp hz))
      exact (pow_pos (by linarith) 2).ne'
    have hqi : IntegrableOn (fun z => ‖q z‖ ^ 2) unitDisc := hcont _ (by fun_prop)
    have hbd : ∀ z ∈ unitDisc, ‖G z - ε ^ 2 * ‖q z‖ ^ 2‖ ≤ 10 * K ^ 3 * |ε| ^ 3 := fun z hz => by
      have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
      rw [Real.norm_eq_abs]
      exact s12_ratio_bound hK0 (hqK z hz1) (hvK z hz1) hε
    calc _ = ‖∫ z in unitDisc, (G z - ε ^ 2 * ‖q z‖ ^ 2)‖ := by
          rw [integral_sub hGi (hqi.const_mul _), integral_const_mul, hqP]
          unfold dirichletDefect
          rw [setIntegral_congr_fun (s := unitDisc) measurableSet_ball hint]
      _ ≤ 10 * K ^ 3 * |ε| ^ 3 * V := norm_setIntegral_le_of_norm_le_const measure_ball_lt_top hbd
      _ = 10 * K ^ 3 * V * ‖ε ^ 3‖ := by
          rw [Real.norm_eq_abs, abs_pow]
          ring
  · filter_upwards [hev] with ε hε
    set f : ℂ → ℂ := fun z => z + (ε : ℂ) * linPoly N a z with hfdef
    have hfd : ∀ z, HasDerivAt f (1 + (ε : ℂ) * u1 z) z := fun z =>
      (hasDerivAt_id' z).add ((hd0 z).const_mul (ε : ℂ))
    set S : ℂ → ℂ := fun z => (ε : ℂ) * u3 z / (1 + (ε : ℂ) * u1 z) -
      3 / 2 * ((ε : ℂ) * u2 z) ^ 2 / (1 + (ε : ℂ) * u1 z) ^ 2 with hS
    have hD1 : deriv f = fun w => 1 + (ε : ℂ) * u1 w := funext fun w => (hfd w).deriv
    have hD2 : deriv (deriv f) = fun w => (ε : ℂ) * u2 w := by
      rw [hD1]
      funext w
      exact (((hd1 w).const_mul (ε : ℂ)).const_add 1).deriv
    have hdz : ∀ z : ℂ, ‖z‖ ≤ 1 → 1 + (ε : ℂ) * u1 z ≠ 0 := fun z hz h => by
      have := hnear ε (u1 z) hε (hu1K z hz)
      rw [h, norm_zero] at this
      norm_num at this
    have hschw : ∀ z : ℂ, ‖z‖ ≤ 1 → schwarzian f z = S z := fun z hz => by
      have han : AnalyticAt ℂ f z :=
        DifferentiableOn.analyticAt (s := univ)
          (fun w _ => (hfd w).differentiableAt.differentiableWithinAt) univ_mem
      rw [schwarzian_of_analyticAt han]
      unfold schwarzianHol
      rw [hD2, hD1]
      beta_reduce
      have hder : HasDerivAt (fun w => (ε : ℂ) * u2 w / (1 + (ε : ℂ) * u1 w))
          (((ε : ℂ) * u3 z * (1 + (ε : ℂ) * u1 z) - (ε : ℂ) * u2 z * ((ε : ℂ) * u2 z)) /
            (1 + (ε : ℂ) * u1 z) ^ 2) z :=
        ((hd2 z).const_mul (ε : ℂ)).div (((hd1 z).const_mul (ε : ℂ)).const_add 1) (hdz z hz)
      rw [hder.deriv]
      have := hdz z hz
      simp only [hS]
      field_simp
      ring
    have hcongr : EqOn (fun z => (1 - ‖z‖ ^ 2) ^ 4 * ‖schwarzian f z‖ ^ 2)
        (fun z => (1 - ‖z‖ ^ 2) ^ 4 * ‖S z‖ ^ 2) unitDisc := fun z hz => by
      show (1 - ‖z‖ ^ 2) ^ 4 * ‖schwarzian f z‖ ^ 2 = (1 - ‖z‖ ^ 2) ^ 4 * ‖S z‖ ^ 2
      rw [hschw z (mem_ball_zero_iff.mp hz).le]
    have hu3i : IntegrableOn (fun z => (1 - ‖z‖ ^ 2) ^ 4 * ‖u3 z‖ ^ 2) unitDisc :=
      hcont _ (by fun_prop)
    have hSi : IntegrableOn (fun z => (1 - ‖z‖ ^ 2) ^ 4 * ‖S z‖ ^ 2) unitDisc := by
      refine hcont _ ((by fun_prop : Continuous fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 4).continuousOn.mul ?_)
      refine (ContinuousOn.norm ?_).pow 2
      have hd : ∀ z ∈ closedBall (0 : ℂ) 1, 1 + (ε : ℂ) * u1 z ≠ 0 := fun z hz =>
        hdz z (mem_closedBall_zero_iff.mp hz)
      simp only [hS]
      exact ContinuousOn.sub (ContinuousOn.div (by fun_prop) (by fun_prop) hd)
        (ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => pow_ne_zero 2 (hd z hz))
    have hbd : ∀ z ∈ unitDisc, ‖(1 - ‖z‖ ^ 2) ^ 4 * ‖S z‖ ^ 2 -
        ε ^ 2 * ((1 - ‖z‖ ^ 2) ^ 4 * ‖u3 z‖ ^ 2)‖ ≤ 48 * K ^ 3 * |ε| ^ 3 := fun z hz => by
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have hw : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have hw0 : 0 ≤ (1 - ‖z‖ ^ 2) ^ 4 := by positivity
      have hw1 : (1 - ‖z‖ ^ 2) ^ 4 ≤ 1 := pow_le_one₀ hw (by nlinarith [norm_nonneg z])
      have hb := s12_schw_bound hK0 (hu1K z hz1.le) (hu2K z hz1.le) (hu3K z hz1.le) hε
      rw [show (1 - ‖z‖ ^ 2) ^ 4 * ‖S z‖ ^ 2 - ε ^ 2 * ((1 - ‖z‖ ^ 2) ^ 4 * ‖u3 z‖ ^ 2) =
          (1 - ‖z‖ ^ 2) ^ 4 * (‖S z‖ ^ 2 - ε ^ 2 * ‖u3 z‖ ^ 2) by ring, norm_mul,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw0]
      calc (1 - ‖z‖ ^ 2) ^ 4 * |‖S z‖ ^ 2 - ε ^ 2 * ‖u3 z‖ ^ 2|
          ≤ 1 * |‖S z‖ ^ 2 - ε ^ 2 * ‖u3 z‖ ^ 2| := mul_le_mul_of_nonneg_right hw1 (abs_nonneg _)
        _ ≤ 48 * K ^ 3 * |ε| ^ 3 := by
          rw [one_mul]
          exact hb
    calc _ = ‖(1 / 4) * ∫ z in unitDisc, ((1 - ‖z‖ ^ 2) ^ 4 * ‖S z‖ ^ 2 -
          ε ^ 2 * ((1 - ‖z‖ ^ 2) ^ 4 * ‖u3 z‖ ^ 2))‖ := by
          rw [integral_sub hSi (hu3i.const_mul _), integral_const_mul, ← hu3P]
          unfold interiorCurvInt
          rw [setIntegral_congr_fun (s := unitDisc) measurableSet_ball hcongr]
          congr 1
          ring
      _ ≤ (1 / 4) * (48 * K ^ 3 * |ε| ^ 3 * V) := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
          exact mul_le_mul_of_nonneg_left
            (norm_setIntegral_le_of_norm_le_const measure_ball_lt_top hbd) (by norm_num)
      _ = 12 * K ^ 3 * V * ‖ε ^ 3‖ := by
          rw [Real.norm_eq_abs, abs_pow]
          ring

/-- Remark `rem:linear-spacing`, `sec12-counter.tex:428–436`: `𝒟₂ ≤ (10/9) 𝓘₂`, with equality
exactly when `u = a₂ z³` (so the constant is optimal). -/
theorem rem_linear_spacing_ineq (N : ℕ) (a : ℕ → ℂ) :
    π * ∑ n ∈ Finset.Icc 2 N, (n : ℝ) * ‖a n‖ ^ 2 ≤
        10 / 9 * (6 * π * ∑ n ∈ Finset.Icc 2 N,
          (n : ℝ) * ((n : ℝ) ^ 2 - 1) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) * ‖a n‖ ^ 2) ∧
      (π * ∑ n ∈ Finset.Icc 2 N, (n : ℝ) * ‖a n‖ ^ 2 =
          10 / 9 * (6 * π * ∑ n ∈ Finset.Icc 2 N,
            (n : ℝ) * ((n : ℝ) ^ 2 - 1) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) * ‖a n‖ ^ 2) ↔
        ∀ n ∈ Finset.Icc 3 N, a n = 0) := by
  set D : ℕ → ℝ := fun n => 10 / 9 * (6 * π * ((n : ℝ) * ((n : ℝ) ^ 2 - 1) /
    (((n : ℝ) + 2) * ((n : ℝ) + 3)) * ‖a n‖ ^ 2)) - π * ((n : ℝ) * ‖a n‖ ^ 2) with hD
  have hDe : ∀ n : ℕ, D n = π * ‖a n‖ ^ 2 *
      ((n : ℝ) * ((n : ℝ) - 2) * (17 * (n : ℝ) + 19) / (3 * (((n : ℝ) + 2) * ((n : ℝ) + 3)))) := by
    intro n
    simp only [hD]
    field_simp
    ring
  have hsum : 10 / 9 * (6 * π * ∑ n ∈ Finset.Icc 2 N,
      (n : ℝ) * ((n : ℝ) ^ 2 - 1) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) * ‖a n‖ ^ 2) -
      π * ∑ n ∈ Finset.Icc 2 N, (n : ℝ) * ‖a n‖ ^ 2 = ∑ n ∈ Finset.Icc 2 N, D n := by
    simp only [hD, Finset.mul_sum, Finset.sum_sub_distrib]
  have hnn : ∀ n ∈ Finset.Icc 2 N, 0 ≤ D n := by
    intro n hn
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [hDe]
    have : 0 ≤ (n : ℝ) * ((n : ℝ) - 2) * (17 * (n : ℝ) + 19) := by
      apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    positivity
  refine ⟨?_, ?_⟩
  · have := Finset.sum_nonneg hnn
    linarith
  · constructor
    · intro heq n hn
      have h0 : ∑ n ∈ Finset.Icc 2 N, D n = 0 := by linarith
      have hn2 : n ∈ Finset.Icc 2 N := by
        rw [Finset.mem_Icc] at hn ⊢; omega
      have hDn := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 n hn2
      have h3 : (3 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [hDe] at hDn
      have hpos : 0 < (n : ℝ) * ((n : ℝ) - 2) * (17 * (n : ℝ) + 19) /
          (3 * (((n : ℝ) + 2) * ((n : ℝ) + 3))) := by
        apply div_pos _ (by positivity)
        apply mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      have : ‖a n‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp hDn with h | h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' Real.pi_ne_zero
          · exact h'
        · exact absurd h hpos.ne'
      simpa using this
    · intro hz
      have h0 : ∑ n ∈ Finset.Icc 2 N, D n = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        rw [hDe]
        rcases eq_or_ne n 2 with rfl | hne
        · norm_num
        · have : n ∈ Finset.Icc 3 N := by
            rw [Finset.mem_Icc] at hn ⊢; omega
          simp [hz n this]
      linarith

/-! ## Perturbations of the operator -/

/-! The hyperbolic area `diskHypArea` and the Laplace–Beltrami operator `hypLaplacianDisk` of `𝔻`
are those of `S10_Sharp`. -/

/-- The kernel `k_q = sech²(d(q, ·)/2)` of `𝔻`. -/
def diskKernelSq (q z : ℂ) : ℝ := ((Real.cosh (diskDist q z / 2))⁻¹) ^ 2

/-- The Frobenius coefficients of Proposition 12.5, Step 1 (`sec12-counter.tex`):
`c₀ = 1`, `c_{k+1} = c_k (2k+1)(β+k) / ((k+1)(2β+2k+1))`.
Junk: the denominator vanishes only at `β = -k - 1/2` (Lean then gives `0`); only `β ∈ (1,2)`
is used. -/
def s12_pt_coeff (β : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => s12_pt_coeff β k * ((2 * k + 1) * (β + k)) / ((k + 1) * (2 * β + 2 * k + 1))

/-- The radial profile `v(r) = Σ_k c_k e^{-(β+2k) r} = x^β Θ(x²)`, `x = e^{-r}`, of
Proposition 12.5, Step 1.
Junk: for `r ≤ 0` the series diverges (`c_k ≍ 1/k`) and the `tsum` is `0`; it is only
evaluated at `r ≥ 1`. -/
def s12_pt_v (β r : ℝ) : ℝ := ∑' k : ℕ, s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r)

/-- Helper (P1) for Proposition 12.5: `0 < c_{k+1} ≤ c_k ≤ 1`. -/
theorem s12_pt_coeff_bounds {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    0 < s12_pt_coeff β k ∧ s12_pt_coeff β (k + 1) ≤ s12_pt_coeff β k ∧ s12_pt_coeff β k ≤ 1 := by
  have hstep : ∀ k : ℕ, 0 < s12_pt_coeff β k →
      0 < s12_pt_coeff β (k + 1) ∧ s12_pt_coeff β (k + 1) ≤ s12_pt_coeff β k := by
    intro k hk
    have hd : 0 < ((k : ℝ) + 1) * (2 * β + 2 * k + 1) := by positivity
    have e : s12_pt_coeff β (k + 1) =
        s12_pt_coeff β k * ((2 * k + 1) * (β + k)) / ((k + 1) * (2 * β + 2 * k + 1)) := rfl
    rw [e]
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hd]
    have : (2 * (k : ℝ) + 1) * (β + k) ≤ (k + 1) * (2 * β + 2 * k + 1) := by nlinarith
    exact mul_le_mul_of_nonneg_left this hk.le
  induction k with
  | zero =>
    have h0 : s12_pt_coeff β 0 = 1 := rfl
    exact ⟨by rw [h0]; exact one_pos, (hstep 0 (by rw [h0]; exact one_pos)).2, h0.le⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := hstep n ih.1
    exact ⟨h1, (hstep (n + 1) h1).2, h2.trans ih.2.2⟩

/-- Helper for Proposition 12.5: `Σ_k (β+2k)^J e^{-(β+2k)s} < ∞` for `s > 0`. -/
theorem s12_pt_summ {β : ℝ} (hβ : 0 < β) (J : ℕ) {s : ℝ} (hs : 0 < s) :
    Summable (fun k : ℕ => (β + 2 * k) ^ J * Real.exp (-(β + 2 * k) * s)) := by
  have h1 := (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul J (by positivity : 0 < 2 * s))
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (h1.mul_left ((β + 2) ^ J * Real.exp (2 * s)))
  show _ ≤ (β + 2) ^ J * Real.exp (2 * s) *
    (((k + 1 : ℕ) : ℝ) ^ J * Real.exp (-(2 * s) * ((k + 1 : ℕ) : ℝ)))
  push_cast
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have hb : β + 2 * k ≤ (β + 2) * (k + 1) := by nlinarith
  have hp : (β + 2 * k) ^ J ≤ ((β + 2) * (k + 1)) ^ J := pow_le_pow_left₀ (by positivity) hb J
  have he : Real.exp (-(β + 2 * k) * s) ≤ Real.exp (2 * s) * Real.exp (-(2 * s) * (k + 1)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_pos hβ hs]
  calc (β + 2 * k) ^ J * Real.exp (-(β + 2 * k) * s)
      ≤ ((β + 2) * (k + 1)) ^ J * (Real.exp (2 * s) * Real.exp (-(2 * s) * (k + 1))) :=
        mul_le_mul hp he (by positivity) (by positivity)
    _ = (β + 2) ^ J * Real.exp (2 * s) * ((k + 1) ^ J * Real.exp (-(2 * s) * (k + 1))) := by
        rw [mul_pow]; ring

/-- Helper for Proposition 12.5: `Σ_k (β+2k)^J c_k e^{-(β+2k)r} < ∞` for `r > 0`. -/
theorem s12_pt_fsumm {β : ℝ} (hβ : 0 < β) (J : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable (fun k : ℕ => (β + 2 * k) ^ J * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (s12_pt_summ hβ J hr)
  · have := (s12_pt_coeff_bounds hβ k).1
    positivity
  · have hc := s12_pt_coeff_bounds hβ k
    have h0 : 0 ≤ (β + 2 * (k : ℝ)) ^ J := by positivity
    calc (β + 2 * k) ^ J * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r)
        ≤ (β + 2 * k) ^ J * 1 * Real.exp (-(β + 2 * k) * r) := by
          gcongr; exact hc.2.2
      _ = _ := by ring

/-- Helper (P2) for Proposition 12.5: the derivative family of `v`. -/
theorem s12_pt_v_hasDerivAt {β : ℝ} (hβ : 0 < β) (j : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r => ∑' k : ℕ, (-(β + 2 * k)) ^ j * s12_pt_coeff β k *
        Real.exp (-(β + 2 * k) * r))
      (∑' k : ℕ, (-(β + 2 * k)) ^ (j + 1) * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r)) r := by
  have hc := s12_pt_coeff_bounds hβ
  have hr2 : 0 < r / 2 := by positivity
  have hnorm : ∀ (J : ℕ) (k : ℕ) (y : ℝ),
      ‖(-(β + 2 * k)) ^ J * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * y)‖ =
        (β + 2 * k) ^ J * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * y) := by
    intro J k y
    have ha : 0 < β + 2 * (k : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_of_pos ha,
      abs_of_pos (hc k).1, abs_of_pos (Real.exp_pos _)]
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun k r => (-(β + 2 * k)) ^ j * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r))
    (g' := fun k r => (-(β + 2 * k)) ^ (j + 1) * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r))
    (u := fun k : ℕ => (β + 2 * k) ^ (j + 1) * Real.exp (-(β + 2 * k) * (r / 2)))
    (t := Ioi (r / 2)) (y₀ := r) (s12_pt_summ hβ (j + 1) hr2) isOpen_Ioi isPreconnected_Ioi
    ?_ ?_ ?_ ?_ ?_
  · intro k y _
    have h := (((hasDerivAt_id' y).const_mul (-(β + 2 * k))).exp).const_mul
      ((-(β + 2 * k)) ^ j * s12_pt_coeff β k)
    convert h using 1
    ring
  · intro k y hy
    rw [hnorm]
    have ha : 0 < β + 2 * (k : ℝ) := by positivity
    have hy' : r / 2 < y := hy
    calc (β + 2 * k) ^ (j + 1) * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * y)
        ≤ (β + 2 * k) ^ (j + 1) * 1 * Real.exp (-(β + 2 * k) * (r / 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (hc k).2.2 (by positivity))
            (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  · show r / 2 < r
    linarith
  · refine Summable.of_norm_bounded (s12_pt_fsumm hβ j hr) (fun k => (hnorm j k r).le)
  · show r / 2 < r
    linarith

/-- Helper (P3) for Proposition 12.5: `v ∈ C^∞(0, ∞)`. -/
theorem s12_pt_v_contDiffOn {β : ℝ} (hβ : 0 < β) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (s12_pt_v β) (Ioi 0) := by
  set V : ℕ → ℝ → ℝ := fun j r => ∑' k : ℕ, (-(β + 2 * k)) ^ j * s12_pt_coeff β k *
    Real.exp (-(β + 2 * k) * r) with hV
  have hd : ∀ j, ∀ r ∈ Ioi (0 : ℝ), HasDerivAt (V j) (V (j + 1) r) r :=
    fun j r hr => s12_pt_v_hasDerivAt hβ j hr
  have key : ∀ n : ℕ, ∀ j, ContDiffOn ℝ n (V j) (Ioi 0) := by
    intro n
    induction n with
    | zero =>
      intro j
      exact contDiffOn_zero.mpr fun r hr => (hd j r hr).continuousAt.continuousWithinAt
    | succ n ih =>
      intro j
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨fun r hr => (hd j r hr).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact (ih (j + 1)).congr fun r hr => (hd j r hr).deriv
  have h0 : s12_pt_v β = V 0 := by
    funext r
    simp only [s12_pt_v, hV, pow_zero, one_mul]
  rw [h0]
  exact contDiffOn_infty.mpr fun n => key n 0

/-- Helper (P4) for Proposition 12.5: `sinh r · v'' + cosh r · v' = β(β-1) sinh r · v`
(the radial ODE `v'' + coth r v' = κ v`), by comparing the coefficients of `e^{-(β+2k-1)r}`. -/
theorem s12_pt_v_ode {β : ℝ} (hβ : 0 < β) {r : ℝ} (hr : 0 < r) :
    Real.sinh r * (∑' k : ℕ, (-(β + 2 * k)) ^ 2 * s12_pt_coeff β k *
        Real.exp (-(β + 2 * k) * r)) +
      Real.cosh r * (∑' k : ℕ, (-(β + 2 * k)) ^ 1 * s12_pt_coeff β k *
        Real.exp (-(β + 2 * k) * r)) =
      β * (β - 1) * Real.sinh r * s12_pt_v β r := by
  set f : ℕ → ℕ → ℝ := fun J k =>
    (β + 2 * k) ^ J * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r) with hf
  have hS : ∀ J, Summable (f J) := fun J => s12_pt_fsumm hβ J hr
  have e2 : (fun k : ℕ => (-(β + 2 * k)) ^ 2 * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r)) =
      f 2 := by
    funext k; simp only [hf]; ring
  have e1 : (fun k : ℕ => (-(β + 2 * k)) ^ 1 * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r)) =
      fun k => -f 1 k := by
    funext k; simp only [hf]; ring
  have e0 : s12_pt_v β r = ∑' k, f 0 k := by
    simp only [s12_pt_v, hf, pow_zero, one_mul]
  rw [e2, e1, e0, tsum_neg]
  set A : ℕ → ℝ := fun k => Real.exp r * (f 2 k - f 1 k - β * (β - 1) * f 0 k) with hA
  set B : ℕ → ℝ := fun k => Real.exp (-r) * (f 2 k + f 1 k - β * (β - 1) * f 0 k) with hB
  have hAs : HasSum A (Real.exp r *
      (∑' k, f 2 k - ∑' k, f 1 k - β * (β - 1) * ∑' k, f 0 k)) :=
    (((hS 2).hasSum.sub (hS 1).hasSum).sub ((hS 0).hasSum.mul_left (β * (β - 1)))).mul_left _
  have hBs : HasSum B (Real.exp (-r) *
      (∑' k, f 2 k + ∑' k, f 1 k - β * (β - 1) * ∑' k, f 0 k)) :=
    (((hS 2).hasSum.add (hS 1).hasSum).sub ((hS 0).hasSum.mul_left (β * (β - 1)))).mul_left _
  have hc0 : s12_pt_coeff β 0 = 1 := rfl
  have hA0 : A 0 = 0 := by
    simp only [hA, hf, Nat.cast_zero, hc0]
    ring
  have hAB : ∀ k : ℕ, A (k + 1) = B k := by
    intro k
    have hd : ((k : ℝ) + 1) * (2 * β + 2 * k + 1) ≠ 0 := by positivity
    have hcs : s12_pt_coeff β (k + 1) =
        s12_pt_coeff β k * ((2 * k + 1) * (β + k)) / ((k + 1) * (2 * β + 2 * k + 1)) := rfl
    have hex1 : Real.exp r * Real.exp (-(β + 2 * ((k + 1 : ℕ) : ℝ)) * r) =
        Real.exp (-(β + 2 * k + 1) * r) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have hex2 : Real.exp (-r) * Real.exp (-(β + 2 * (k : ℝ)) * r) =
        Real.exp (-(β + 2 * k + 1) * r) := by
      rw [← Real.exp_add]; ring_nf
    have L : A (k + 1) = s12_pt_coeff β (k + 1) * ((β + 2 * ((k + 1 : ℕ) : ℝ)) ^ 2 -
        (β + 2 * ((k + 1 : ℕ) : ℝ)) - β * (β - 1)) *
        (Real.exp r * Real.exp (-(β + 2 * ((k + 1 : ℕ) : ℝ)) * r)) := by
      simp only [hA, hf]; ring
    have R : B k = s12_pt_coeff β k * ((β + 2 * (k : ℝ)) ^ 2 + (β + 2 * k) - β * (β - 1)) *
        (Real.exp (-r) * Real.exp (-(β + 2 * (k : ℝ)) * r)) := by
      simp only [hB, hf]; ring
    rw [L, R, hex1, hex2, hcs]
    push_cast
    field_simp
    ring
  have hsum : HasSum B (Real.exp r *
      (∑' k, f 2 k - ∑' k, f 1 k - β * (β - 1) * ∑' k, f 0 k)) := by
    have h := (hasSum_nat_add_iff' 1).mpr hAs
    simp only [Finset.sum_range_one, hA0, sub_zero] at h
    exact (funext hAB : (fun k => A (k + 1)) = B) ▸ h
  have E := hsum.unique hBs
  rw [Real.sinh_eq, Real.cosh_eq]
  linear_combination (1 / 2) * E

/-- Helper (P5) for Proposition 12.5: `e^{-βr} ≤ v(r)`, `v'(r) < 0`, and
`v(r) ≤ e^{-βr}/(1 - e^{-2})` for `r ≥ 1`. -/
theorem s12_pt_v_bounds {β : ℝ} (hβ : 0 < β) {r : ℝ} (hr : 0 < r) :
    Real.exp (-β * r) ≤ s12_pt_v β r ∧
      (∑' k : ℕ, (-(β + 2 * k)) ^ 1 * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r)) < 0 ∧
      (1 ≤ r → s12_pt_v β r ≤ Real.exp (-β * r) / (1 - Real.exp (-2))) := by
  have hc := s12_pt_coeff_bounds hβ
  have hc0 : s12_pt_coeff β 0 = 1 := rfl
  have hS0 := s12_pt_fsumm hβ 0 hr
  have hS1 := s12_pt_fsumm hβ 1 hr
  simp only [pow_zero, one_mul] at hS0
  have hnn : ∀ (J : ℕ) (k : ℕ),
      0 ≤ (β + 2 * (k : ℝ)) ^ J * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r) := fun J k => by
    have := (hc k).1; positivity
  refine ⟨?_, ?_, fun h1 => ?_⟩
  · have h := hS0.le_tsum 0 (fun k _ => by simpa using hnn 0 k)
    simpa [hc0, s12_pt_v] using h
  · have e1 : (fun k : ℕ => (-(β + 2 * k)) ^ 1 * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r)) =
        fun k => -((β + 2 * k) ^ 1 * s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r)) := by
      funext k; ring
    rw [e1, tsum_neg, neg_lt_zero]
    refine hS1.tsum_pos (fun k => hnn 1 k) 0 ?_
    simp only [Nat.cast_zero, mul_zero, add_zero, pow_one, hc0, mul_one]
    exact mul_pos hβ (Real.exp_pos _)
  · have hq0 : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
    have hq1 : Real.exp (-2) < 1 := by
      calc Real.exp (-2) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
        _ = 1 := Real.exp_zero
    have hg : Summable (fun k : ℕ => Real.exp (-β * r) * Real.exp (-2) ^ k) :=
      (summable_geometric_of_lt_one hq0 hq1).mul_left _
    have hle : ∀ k : ℕ, s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r) ≤
        Real.exp (-β * r) * Real.exp (-2) ^ k := by
      intro k
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      calc s12_pt_coeff β k * Real.exp (-(β + 2 * k) * r)
          ≤ 1 * Real.exp (-(β + 2 * k) * r) := by gcongr; exact (hc k).2.2
        _ ≤ Real.exp (-β * r + k * -2) := by
          rw [one_mul]
          apply Real.exp_le_exp.mpr
          have hk : (0 : ℝ) ≤ k := k.cast_nonneg
          nlinarith
    have h := hS0.tsum_le_tsum hle hg
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1] at h
    exact h


/-- Helper (P6) for Proposition 12.5: a smooth nonincreasing cut-off `χ` (`= 1` on `(-∞, m]`,
`= 0` on `[3m/2, ∞)`) and its primitive `ψ = ∫₀ χ`. -/
theorem s12_pt_cutoff {m : ℝ} (hm : 0 < m) :
    ∃ ψ χ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ s, HasDerivAt ψ (χ s) s) ∧
      Antitone χ ∧ (∀ s, 0 ≤ χ s ∧ χ s ≤ 1) ∧ (∀ s ≤ m, χ s = 1) ∧
      (∀ s, 3 * m / 2 ≤ s → χ s = 0) ∧ (∀ s ≤ m, ψ s = s) ∧
      (∀ s, 0 ≤ s → s * χ s ≤ ψ s) ∧ (∀ s, 0 < s → min s m ≤ ψ s) := by
  set χ : ℝ → ℝ := fun s => 1 - Real.smoothTransition (2 * (s - m) / m) with hχ
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul (contDiff_id.sub contDiff_const)).div_const m :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun s : ℝ => 2 * (s - m) / m)))
  have hχc : Continuous χ := hχs.continuous
  set ψ : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, χ t with hψ
  have hd : ∀ s, HasDerivAt ψ (χ s) s := fun s => (hχc.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hdψ : deriv ψ = χ := funext fun s => (hd s).deriv
  have hψs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ :=
    contDiff_infty_iff_deriv.mpr ⟨fun s => (hd s).differentiableAt, hdψ ▸ hχs⟩
  have hanti : Antitone χ := by
    intro a b hab
    have : 2 * (a - m) / m ≤ 2 * (b - m) / m := by
      apply div_le_div_of_nonneg_right _ hm.le; linarith
    simp only [hχ]
    linarith [Real.smoothTransition.monotone this]
  have hbd : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1 := fun s => by
    simp only [hχ]
    constructor
    · linarith [Real.smoothTransition.le_one (2 * (s - m) / m)]
    · linarith [Real.smoothTransition.nonneg (2 * (s - m) / m)]
  have h1 : ∀ s ≤ m, χ s = 1 := fun s hs => by
    simp only [hχ]
    rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hm.le)]
    ring
  have h0 : ∀ s, 3 * m / 2 ≤ s → χ s = 0 := fun s hs => by
    simp only [hχ]
    rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hm]; linarith)]
    ring
  have hid : ∀ s ≤ m, ψ s = s := fun s hs => by
    simp only [hψ]
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun t ht => h1 t ?_)]
    · simp
    · rcases Set.mem_uIcc.mp ht with h | h
      · linarith [h.2]
      · linarith [h.2, hm]
  have hmono : Monotone ψ :=
    monotone_of_deriv_nonneg (fun s => (hd s).differentiableAt) fun s => by
      rw [hdψ]; exact (hbd s).1
  refine ⟨ψ, χ, hψs, hχs, hd, hanti, hbd, h1, h0, hid, fun s hs => ?_, fun s hs => ?_⟩
  · have h := intervalIntegral.integral_mono_on hs
      (intervalIntegrable_const (μ := volume) (c := χ s))
      (hχc.intervalIntegrable (μ := volume) 0 s) (fun t ht => hanti ht.2)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using h
  · rcases le_or_gt s m with h | h
    · rw [min_eq_left h, hid s h]
    · rw [min_eq_right h.le, ← hid m le_rfl]
      exact hmono h.le

/-- Helper (P7) for Proposition 12.5: the radial Laplacian in the distance variable,
`Δ_ρ Φ(d(0,·)) = Φ'' + coth r Φ'` off the centre (Lemma 10.6 (b) with `Φ ∘ arcosh`). -/
theorem s12_pt_radial_lap {Φ Φ₁ Φ₂ : ℝ → ℝ} (h₁ : ∀ r, 0 < r → HasDerivAt Φ (Φ₁ r) r)
    (h₂ : ∀ r, 0 < r → HasDerivAt Φ₁ (Φ₂ r) r) (hc : ContinuousOn Φ₂ (Ioi 0)) {z : ℂ}
    (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    hypLaplacianDisk (fun w => Φ (diskDist 0 w)) z =
      Φ₂ (diskDist 0 z) +
        Real.cosh (diskDist 0 z) / Real.sinh (diskDist 0 z) * Φ₁ (diskDist 0 z) := by
  have hO : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  have hd1 : ∀ x ∈ Ioi (0 : ℝ), deriv Φ x = Φ₁ x := fun x hx => (h₁ x hx).deriv
  have hF₁ : ContDiffOn ℝ 1 Φ₁ (Ioi 0) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hO]
    refine ⟨fun x hx => (h₂ x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (contDiffOn_zero.mpr hc).congr fun x hx => (h₂ x hx).deriv
  have hF : ContDiffOn ℝ 2 Φ (Ioi 0) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hO]
    exact ⟨fun x hx => (h₁ x hx).differentiableAt.differentiableWithinAt, by simp,
      hF₁.congr hd1⟩
  set G : ℝ → ℝ := fun x => Φ (Real.arcosh x) with hG
  have hGs : ContDiffOn ℝ 2 G (Ioi 1) :=
    hF.comp Real.contDiffOn_arcosh fun x hx => Real.arcosh_pos hx
  -- the derivatives of `G` on `(1, ∞)`
  set S : ℝ → ℝ := fun x => (√(x ^ 2 - 1))⁻¹ with hS
  set G₁ : ℝ → ℝ := fun x => Φ₁ (Real.arcosh x) * S x with hG₁
  have hsq : ∀ x ∈ Ioi (1 : ℝ), 0 < √(x ^ 2 - 1) := fun x hx => by
    have : (1 : ℝ) < x := hx
    exact Real.sqrt_pos.mpr (by nlinarith)
  have hdG : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt G (G₁ x) x := fun x hx =>
    (h₁ _ (Real.arcosh_pos hx)).comp x (Real.hasDerivAt_arcosh hx)
  have hdS : ∀ x ∈ Ioi (1 : ℝ),
      HasDerivAt S (-(2 * x / (2 * √(x ^ 2 - 1))) / √(x ^ 2 - 1) ^ 2) x := fun x hx => by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).sub_const 1
    have hx1 : (1 : ℝ) < x := hx
    have hne : x ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < x ^ 2 - 1).ne'
    exact (h1.sqrt hne).inv (hsq x hx).ne'
  have hdG₁ : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt G₁
      (Φ₂ (Real.arcosh x) * S x * S x +
        Φ₁ (Real.arcosh x) * (-(2 * x / (2 * √(x ^ 2 - 1))) / √(x ^ 2 - 1) ^ 2)) x :=
    fun x hx => ((h₂ _ (Real.arcosh_pos hx)).comp x (Real.hasDerivAt_arcosh hx)).mul (hdS x hx)
  -- the centre and the value of `cosh d`
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set C := diskCoshDist 0 z with hC
  have hC1 : 1 < C := by
    have h1z : 0 < 1 - ‖z‖ ^ 2 := by nlinarith
    simp only [hC, diskCoshDist, norm_zero, zero_sub, norm_neg]
    have : 0 < 2 * ‖z‖ ^ 2 / ((1 - 0 ^ 2) * (1 - ‖z‖ ^ 2)) := by positivity
    linarith
  have hCm : C ∈ Ioi (1 : ℝ) := hC1
  have hlap := lem_plane_green_b G hGs 0 (mem_ball_self one_pos) z hz hz0
  have hdd1 : deriv G C = G₁ C := (hdG C hCm).deriv
  have hdd2 : deriv (deriv G) C = Φ₂ (Real.arcosh C) * S C * S C +
      Φ₁ (Real.arcosh C) * (-(2 * C / (2 * √(C ^ 2 - 1))) / √(C ^ 2 - 1) ^ 2) := by
    have hev : deriv G =ᶠ[𝓝 C] G₁ := by
      filter_upwards [isOpen_Ioi.mem_nhds hCm] with y hy
      exact (hdG y hy).deriv
    rw [hev.deriv_eq]
    exact (hdG₁ C hCm).deriv
  show hypLaplacianDisk (fun w => G (diskCoshDist 0 w)) z = _
  rw [hlap, hdd1, hdd2]
  have hdist : diskDist 0 z = Real.arcosh C := rfl
  rw [hdist, Real.cosh_arcosh hC1.le, Real.sinh_arcosh hC1.le]
  have hs := hsq C hCm
  have hs2 : √(C ^ 2 - 1) ^ 2 = C ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  simp only [hG₁, hS]
  set s := √(C ^ 2 - 1) with hsdef
  rw [show C ^ 2 - 1 = s ^ 2 from hs2.symm]
  field_simp
  ring


/-- Helper for Proposition 12.5: `cosh d(0, w) = 1 + 2|w|²/(1 - |w|²)`, continuity and
smoothness of `d(0, ·)`, and the hyperbolic balls `{d(0, ·) ≤ R}` lie in Euclidean balls `ρ < 1`. -/
theorem s12_pt_dist :
    (∀ w : ℂ, diskCoshDist 0 w = 1 + 2 * ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2)) ∧
      ContinuousOn (diskDist 0) unitDisc ∧ diskDist 0 0 = 0 ∧
      (∀ z ∈ unitDisc, z ≠ 0 →
        1 < diskCoshDist 0 z ∧ ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (diskDist 0) z) ∧
      ∀ R : ℝ, ∃ ρ : ℝ, ρ < 1 ∧ ∀ w ∈ unitDisc, diskDist 0 w ≤ R → ‖w‖ ≤ ρ := by
  have hC : ∀ w : ℂ, diskCoshDist 0 w = 1 + 2 * ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2) := fun w => by
    unfold diskCoshDist
    rw [zero_sub, norm_neg, norm_zero]
    ring
  have hpos : ∀ w ∈ unitDisc, 0 < 1 - ‖w‖ ^ 2 := fun w hw => by
    have := mem_ball_zero_iff.mp hw
    nlinarith [norm_nonneg w]
  have hge : ∀ w ∈ unitDisc, 1 ≤ diskCoshDist 0 w := fun w hw => by
    rw [hC]
    have := hpos w hw
    have : 0 ≤ 2 * ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2) := by positivity
    linarith
  have hcd : ∀ z ∈ unitDisc, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (diskCoshDist 0) z := by
    intro z hz
    rw [show diskCoshDist 0 = fun w : ℂ => 1 + 2 * ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2) from funext hC]
    exact contDiffAt_const.add ((contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt).div
      (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt) (hpos z hz).ne')
  refine ⟨hC, ?_, ?_, fun z hz hz0 => ?_, fun R => ?_⟩
  · show ContinuousOn (Real.arcosh ∘ diskCoshDist 0) unitDisc
    exact Real.continuousOn_arcosh.comp (fun z hz => (hcd z hz).continuousAt.continuousWithinAt)
      fun z hz => hge z hz
  · show Real.arcosh (diskCoshDist 0 0) = 0
    have : diskCoshDist 0 0 = 1 := by rw [hC]; simp
    rw [this]
    exact Real.arcosh_zero
  · have h1 : 1 < diskCoshDist 0 z := by
      rw [hC]
      have := hpos z hz
      have : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have : 0 < 2 * ‖z‖ ^ 2 / (1 - ‖z‖ ^ 2) := by positivity
      linarith
    exact ⟨h1, (Real.contDiffAt_arcosh h1).comp z (hcd z hz)⟩
  · set K := Real.cosh R with hK
    have hK1 : 1 ≤ K := Real.one_le_cosh R
    refine ⟨√((K - 1) / (K + 1)), ?_, fun w hw hd => ?_⟩
    · have : (K - 1) / (K + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
      calc √((K - 1) / (K + 1)) < √1 := Real.sqrt_lt_sqrt (by positivity) this
        _ = 1 := Real.sqrt_one
    · have hp := hpos w hw
      have hd0 : 0 ≤ diskDist 0 w := Real.arcosh_nonneg (hge w hw)
      have hcw : diskCoshDist 0 w ≤ K := by
        have h := (Real.cosh_le_cosh (x := diskDist 0 w) (y := R)).mpr (by
          rw [abs_of_nonneg hd0, abs_of_nonneg (hd0.trans hd)]; exact hd)
        rwa [show diskDist 0 w = Real.arcosh (diskCoshDist 0 w) from rfl,
          Real.cosh_arcosh (hge w hw)] at h
      rw [hC, ← le_sub_iff_add_le', div_le_iff₀ hp] at hcw
      have h2 : ‖w‖ ^ 2 ≤ (K - 1) / (K + 1) := by
        rw [le_div_iff₀ (by linarith)]; nlinarith
      have := Real.abs_le_sqrt h2
      rwa [abs_of_nonneg (norm_nonneg w)] at this

/-- Helper (P8) for Proposition 12.5: the construction of `u = ψ(v(max(d, 1)))` and
`F = (κ - Δ_ρ) u ∈ C_c^∞(𝔻)` (Steps 2–3 of the proof), `κ = β(β - 1)`. -/
theorem s12_pt_build {β : ℝ} (hβ1 : 1 < β) (hβ2 : β < 2) :
    ∃ (u F : ℂ → ℝ) (r₁ : ℝ), 1 < r₁ ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u unitDisc ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ unitDisc ∧
      (∀ z ∈ unitDisc, β * (β - 1) * u z - hypLaplacianDisk u z = F z) ∧ (∀ z, 0 ≤ F z) ∧
      F 0 ≠ 0 ∧ (∀ z ∈ unitDisc, 0 < u z) ∧
      (∀ z ∈ unitDisc, F z ≠ 0 → diskDist 0 z ≤ r₁) ∧
      (∀ z ∈ unitDisc, 1 ≤ diskDist 0 z → u z ≤ s12_pt_v β (diskDist 0 z)) ∧
      (∀ z ∈ unitDisc, r₁ ≤ diskDist 0 z → u z = s12_pt_v β (diskDist 0 z)) := by
  have hβ : 0 < β := by linarith
  have hκ : 0 < β * (β - 1) := by nlinarith
  set κ := β * (β - 1) with hκdef
  set v := s12_pt_v β with hvdef
  set V1 : ℝ → ℝ := fun r => ∑' k : ℕ, (-(β + 2 * k)) ^ 1 * s12_pt_coeff β k *
    Real.exp (-(β + 2 * k) * r) with hV1def
  set V2 : ℝ → ℝ := fun r => ∑' k : ℕ, (-(β + 2 * k)) ^ 2 * s12_pt_coeff β k *
    Real.exp (-(β + 2 * k) * r) with hV2def
  have hv0 : (fun r => ∑' k : ℕ, (-(β + 2 * k)) ^ 0 * s12_pt_coeff β k *
      Real.exp (-(β + 2 * k) * r)) = v := by
    funext r; simp only [hvdef, s12_pt_v, pow_zero, one_mul]
  have hv1 : ∀ r, 0 < r → HasDerivAt v (V1 r) r := fun r hr => by
    have h := s12_pt_v_hasDerivAt hβ 0 hr
    rw [hv0] at h
    exact h
  have hV1 : ∀ r, 0 < r → HasDerivAt V1 (V2 r) r := fun r hr => s12_pt_v_hasDerivAt hβ 1 hr
  have hvs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ioi 0) := s12_pt_v_contDiffOn hβ
  have hV1s : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V1 (Ioi 0) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp hvs).2.congr
      fun r hr => (hv1 r hr).deriv.symm
  have hV2c : ContinuousOn V2 (Ioi 0) :=
    (((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp hV1s).2.congr
      fun r hr => (hV1 r hr).deriv.symm).continuousOn
  have hvc : ContinuousOn v (Ioi 0) := hvs.continuousOn
  have hV1c : ContinuousOn V1 (Ioi 0) := hV1s.continuousOn
  have hvpos : ∀ r, 0 < r → 0 < v r := fun r hr =>
    (Real.exp_pos _).trans_le (s12_pt_v_bounds hβ hr).1
  have hvanti : ∀ a b, 0 < a → a ≤ b → v b ≤ v a := by
    have h := antitoneOn_of_deriv_nonpos (convex_Ioi (0 : ℝ)) hvc
      (fun r hr => (hv1 r (by rwa [interior_Ioi] at hr)).differentiableAt.differentiableWithinAt)
      (fun r hr => by
        have hr' : 0 < r := by rwa [interior_Ioi] at hr
        rw [(hv1 r hr').deriv]; exact (s12_pt_v_bounds hβ hr').2.1.le)
    exact fun a b ha hab => h ha (lt_of_lt_of_le ha hab) hab
  -- the threshold `m = v(1)/2` and the cut-off
  set m := v 1 / 2 with hmdef
  have hm : 0 < m := by have := hvpos 1 one_pos; positivity
  have hv1m : v 1 = 2 * m := by rw [hmdef]; ring
  obtain ⟨ψ, χ, hψs, hχs, hd, hanti, hbd, h1, h0, hid, hle, hmin⟩ := s12_pt_cutoff hm
  have hχd := contDiff_infty_iff_deriv.mp hχs
  have hψc : ∀ s, 3 * m / 2 ≤ s → ψ s = ψ (3 * m / 2) := by
    intro s hs
    rcases hs.lt_or_eq with h | h
    · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope ψ χ h hψs.continuous.continuousOn
        (fun x _ => hd x)
      rw [h0 c hc.1.le, eq_comm, div_eq_zero_iff] at hc'
      rcases hc' with h' | h'
      · linarith
      · exact absurd h' (by linarith)
    · rw [h]
  have hχ'0 : ∀ s, s < m ∨ 3 * m / 2 < s → deriv χ s = 0 := by
    rintro s (h | h)
    · have e : χ =ᶠ[𝓝 s] fun _ => 1 := by
        filter_upwards [Iio_mem_nhds h] with t ht; exact h1 t (le_of_lt ht)
      rw [e.deriv_eq, deriv_const]
    · have e : χ =ᶠ[𝓝 s] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds h] with t ht; exact h0 t (le_of_lt ht)
      rw [e.deriv_eq, deriv_const]
  have hψle : ∀ s, 0 ≤ s → ψ s ≤ s := by
    have hg : ∀ s, HasDerivAt (fun s => s - ψ s) (1 - χ s) s := fun s =>
      (hasDerivAt_id' s).sub (hd s)
    have hmono : Monotone fun s => s - ψ s :=
      monotone_of_deriv_nonneg (fun s => (hg s).differentiableAt) fun s => by
        rw [(hg s).deriv]; linarith [(hbd s).2]
    intro s hs
    have h := hmono hs
    simp only at h
    rw [hid 0 hm.le] at h
    linarith
  -- the radius `r₁`
  obtain ⟨r₁, hr₁1, hr₁m⟩ : ∃ r₁ : ℝ, 1 < r₁ ∧ v r₁ < m := by
    have ht : Tendsto (fun r : ℝ => Real.exp (-β * r) / (1 - Real.exp (-2))) atTop (𝓝 0) := by
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hβ)).div_const (1 - Real.exp (-2))
      rw [zero_div] at h
      refine h.congr fun r => ?_
      simp only [Function.comp, id]
      ring_nf
    obtain ⟨r, hr, hr2⟩ := ((ht.eventually (gt_mem_nhds hm)).and (eventually_ge_atTop 2)).exists
    exact ⟨r, by linarith, lt_of_le_of_lt ((s12_pt_v_bounds hβ (by linarith)).2.2 (by linarith)) hr⟩
  have hvr₁ : ∀ r, r₁ ≤ r → v r < m := fun r hr =>
    lt_of_le_of_lt (hvanti r₁ r (by linarith) hr) hr₁m
  -- the distance
  obtain ⟨-, hdc, hd00, hdS, hball⟩ := s12_pt_dist
  obtain ⟨ρ₁, hρ₁, hρ₁b⟩ := hball r₁
  set d : ℂ → ℝ := diskDist 0 with hddef
  have hd0 : ∀ z ∈ unitDisc, 0 ≤ d z := fun z hz =>
    s02_diskDist_nonneg (mem_ball_self one_pos) hz
  -- the witnesses
  set H : ℝ → ℝ := fun r => κ * (ψ (v r) - v r * χ (v r)) - deriv χ (v r) * V1 r ^ 2 with hHdef
  set u : ℂ → ℝ := fun z => ψ (v (max (d z) 1)) with hudef
  set F : ℂ → ℝ := fun z => if ‖z‖ < 1 then H (max (d z) 1) else 0 with hFdef
  have hHA : ∀ r, 0 < r → 3 * m / 2 < v r → H r = κ * ψ (3 * m / 2) := fun r _ h => by
    simp only [hHdef]
    rw [hψc _ h.le, h0 _ h.le, hχ'0 _ (Or.inr h)]
    ring
  have hHz : ∀ r, r₁ ≤ r → H r = 0 := fun r hr => by
    have h := hvr₁ r hr
    simp only [hHdef]
    rw [hid _ h.le, h1 _ h.le, hχ'0 _ (Or.inl h)]
    ring
  have hRc : ContinuousOn (fun z => v (max (d z) 1)) unitDisc :=
    hvc.comp ((show ContinuousOn d unitDisc from hdc).sup (continuousOn_const (c := (1 : ℝ)))) fun z _ =>
      show (0 : ℝ) < max (d z) 1 from lt_of_lt_of_le one_pos (le_max_right _ _)
  -- the two regions
  have hA : ∀ z ∈ unitDisc, 3 * m / 2 < v (max (d z) 1) →
      ∀ᶠ w in 𝓝 z, w ∈ unitDisc ∧ 3 * m / 2 < v (max (d w) 1) := fun z hz h =>
    Filter.Eventually.and (isOpen_ball.mem_nhds hz : ∀ᶠ w in 𝓝 z, w ∈ unitDisc)
      ((hRc.continuousAt (isOpen_ball.mem_nhds hz)).eventually (lt_mem_nhds h))
  have hB : ∀ z ∈ unitDisc, ¬ 3 * m / 2 < v (max (d z) 1) →
      1 < d z ∧ z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, w ∈ unitDisc ∧ 1 < d w := by
    intro z hz h
    have h1z : 1 < d z := by
      by_contra hle
      rw [max_eq_right (not_lt.mp hle), hv1m] at h
      exact h (by linarith)
    have hz0 : z ≠ 0 := by
      rintro rfl; rw [hd00] at h1z; linarith
    exact ⟨h1z, hz0, Filter.Eventually.and (isOpen_ball.mem_nhds hz : ∀ᶠ w in 𝓝 z, w ∈ unitDisc)
      (((show ContinuousOn d unitDisc from hdc).continuousAt (isOpen_ball.mem_nhds hz)).eventually (lt_mem_nhds h1z))⟩
  -- smoothness of the radial pieces
  have hΦs : ∀ r, 0 < r → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r => ψ (v r)) r :=
    fun r hr => hψs.contDiffAt.comp r (hvs.contDiffAt (Ioi_mem_nhds hr))
  have hHs : ∀ r, 0 < r → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H r := fun r hr => by
    have hv := hvs.contDiffAt (Ioi_mem_nhds hr)
    have hw := hV1s.contDiffAt (Ioi_mem_nhds hr)
    exact (contDiffAt_const.mul ((hΦs r hr).sub (hv.mul (hχs.contDiffAt.comp r hv)))).sub
      ((hχd.2.contDiffAt.comp r hv).mul (hw.pow 2))
  -- `u` is smooth
  have hus : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u unitDisc := by
    intro z hz
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hz' : 3 * m / 2 < v (max (d z) 1)
    · refine (contDiffAt_const (c := ψ (3 * m / 2))).congr_of_eventuallyEq ?_
      filter_upwards [hA z hz hz'] with w hw
      exact hψc _ hw.2.le
    · obtain ⟨h1z, hz0, hev⟩ := hB z hz hz'
      refine ((hΦs (d z) (by linarith)).comp z (hdS z hz hz0).2).congr_of_eventuallyEq ?_
      filter_upwards [hev] with w hw
      simp only [hudef, Function.comp, max_eq_left hw.2.le]
  -- `F` vanishes off the closed ball of radius `ρ₁`
  have hFz : ∀ w : ℂ, ρ₁ < ‖w‖ → F w = 0 := by
    intro w hw
    simp only [hFdef]
    split_ifs with h
    · have hdw : r₁ < d w := by
        by_contra hle
        exact absurd (hρ₁b w (mem_ball_zero_iff.mpr h) (not_lt.mp hle)) (not_le.mpr hw)
      rw [max_eq_left (by linarith)]
      exact hHz _ hdw.le
    · rfl
  have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    refine contDiff_iff_contDiffAt.mpr fun z => ?_
    by_cases hz : ‖z‖ < 1
    · have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr hz
      have hev : F =ᶠ[𝓝 z] fun w => H (max (d w) 1) := by
        filter_upwards [isOpen_ball.mem_nhds hzD] with w hw
        simp only [hFdef, if_pos (mem_ball_zero_iff.mp hw)]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      by_cases hz' : 3 * m / 2 < v (max (d z) 1)
      · refine (contDiffAt_const (c := κ * ψ (3 * m / 2))).congr_of_eventuallyEq ?_
        filter_upwards [hA z hzD hz'] with w hw
        exact hHA _ (lt_of_lt_of_le one_pos (le_max_right _ _)) hw.2
      · obtain ⟨h1z, hz0, hev'⟩ := hB z hzD hz'
        refine ((hHs (d z) (by linarith)).comp z (hdS z hzD hz0).2).congr_of_eventuallyEq ?_
        filter_upwards [hev'] with w hw
        simp only [Function.comp, max_eq_left hw.2.le]
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      have : {w : ℂ | ρ₁ < ‖w‖} ∈ 𝓝 z :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds (by
          show ρ₁ < ‖z‖; linarith [not_lt.mp hz])
      filter_upwards [this] with w hw
      exact hFz w hw
  have hFsupp : tsupport F ⊆ closedBall 0 ρ₁ :=
    closure_minimal (fun w hw => mem_closedBall_zero_iff.mpr
      (le_of_not_gt fun h => hw (hFz w h))) isClosed_closedBall
  -- the equation
  have hpde : ∀ z ∈ unitDisc, κ * u z - hypLaplacianDisk u z = F z := by
    intro z hz
    have hFz' : F z = H (max (d z) 1) := by
      simp only [hFdef, if_pos (mem_ball_zero_iff.mp hz)]
    rw [hFz']
    by_cases hz' : 3 * m / 2 < v (max (d z) 1)
    · have hev : u =ᶠ[𝓝 z] fun _ => ψ (3 * m / 2) := by
        filter_upwards [hA z hz hz'] with w hw
        exact hψc _ hw.2.le
      rw [s10_hypLaplacianDisk_congr hev, hHA _ (lt_of_lt_of_le one_pos (le_max_right _ _)) hz',
        show u z = ψ (3 * m / 2) from hψc _ hz'.le]
      simp [hypLaplacianDisk]
    · obtain ⟨h1z, hz0, hev'⟩ := hB z hz hz'
      have hev : u =ᶠ[𝓝 z] fun w => ψ (v (d w)) := by
        filter_upwards [hev'] with w hw
        simp only [hudef, max_eq_left hw.2.le]
      have hr : 0 < d z := by linarith
      have hlap := s12_pt_radial_lap (Φ := fun r => ψ (v r)) (Φ₁ := fun r => χ (v r) * V1 r)
        (Φ₂ := fun r => deriv χ (v r) * V1 r * V1 r + χ (v r) * V2 r)
        (fun r hr => (hd (v r)).comp r (hv1 r hr))
        (fun r hr => ((hχd.1 (v r)).hasDerivAt.comp r (hv1 r hr)).mul (hV1 r hr))
        (((hχd.2.continuous.comp_continuousOn hvc).mul hV1c).mul hV1c |>.add
          ((hχs.continuous.comp_continuousOn hvc).mul hV2c)) hz hz0
      have hlap' : hypLaplacianDisk (fun w => ψ (v (d w))) z =
          deriv χ (v (d z)) * V1 (d z) * V1 (d z) + χ (v (d z)) * V2 (d z) +
            Real.cosh (d z) / Real.sinh (d z) * (χ (v (d z)) * V1 (d z)) := hlap
      rw [s10_hypLaplacianDisk_congr hev, hlap', max_eq_left h1z.le]
      simp only [hudef, max_eq_left h1z.le]
      have hode := s12_pt_v_ode hβ hr
      have hsh : 0 < Real.sinh (d z) := Real.sinh_pos_iff.mpr hr
      have hode' : V2 (d z) + Real.cosh (d z) / Real.sinh (d z) * V1 (d z) = κ * v (d z) := by
        field_simp
        linear_combination hode
      simp only [hHdef]
      linear_combination (-χ (v (d z))) * hode'
  refine ⟨u, F, r₁, hr₁1, hus, hFs, HasCompactSupport.intro (isCompact_closedBall 0 ρ₁)
    (fun w hw => hFz w (lt_of_not_ge fun h => hw (mem_closedBall_zero_iff.mpr h))),
    hFsupp.trans (closedBall_subset_ball hρ₁), hpde, fun z => ?_, ?_, fun z hz => ?_,
    fun z hz hFne => ?_, fun z hz h1z => ?_, fun z hz hr => ?_⟩
  · simp only [hFdef]
    split_ifs with h
    · have hV : 0 < v (max (d z) 1) := hvpos _ (lt_of_lt_of_le one_pos (le_max_right _ _))
      have e1 := mul_nonneg hκ.le (sub_nonneg.mpr (hle _ hV.le))
      have e2 := mul_nonpos_of_nonpos_of_nonneg (hanti.deriv_nonpos (x := v (max (d z) 1)))
        (sq_nonneg (V1 (max (d z) 1)))
      simp only [hHdef]
      linarith
    · exact le_rfl
  · have hF0 : F 0 = H 1 := by
      simp only [hFdef, norm_zero, zero_lt_one, if_true, hd00, max_eq_right zero_le_one]
    rw [hF0, hHA 1 one_pos (by rw [hv1m]; linarith)]
    have := hmin (3 * m / 2) (by positivity)
    have : 0 < ψ (3 * m / 2) := lt_of_lt_of_le (lt_min (by positivity) hm) this
    exact (mul_pos hκ this).ne'
  · have hV : 0 < v (max (d z) 1) := hvpos _ (lt_of_lt_of_le one_pos (le_max_right _ _))
    exact lt_of_lt_of_le (lt_min hV hm) (hmin _ hV)
  · by_contra hlt
    apply hFne
    simp only [hFdef, if_pos (mem_ball_zero_iff.mp hz)]
    rw [max_eq_left (by linarith [not_le.mp hlt])]
    exact hHz _ (not_le.mp hlt).le
  · simp only [hudef, max_eq_left h1z]
    exact hψle _ (hvpos _ (by linarith)).le
  · simp only [hudef, max_eq_left (by linarith : 1 ≤ d z)]
    exact hid _ (hvr₁ _ hr).le


/-- Helper (P9) for Proposition 12.5: the maximum principle for `κ - Δ_ρ` (`κ > 0`) on `𝔻` for
functions decaying at the boundary (Step 4 of the proof). -/
theorem s12_pt_unique {κ : ℝ} (hκ : 0 < κ) {w : ℂ → ℝ} (hw : ContDiffOn ℝ 2 w unitDisc)
    (hpde : ∀ z ∈ unitDisc, κ * w z - hypLaplacianDisk w z = 0)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z ∈ unitDisc, R ≤ diskDist 0 z → |w z| ≤ ε) :
    ∀ z ∈ unitDisc, w z = 0 := by
  obtain ⟨-, -, -, -, hball⟩ := s12_pt_dist
  have key : ∀ w : ℂ → ℝ, ContDiffOn ℝ 2 w unitDisc →
      (∀ z ∈ unitDisc, κ * w z - hypLaplacianDisk w z = 0) →
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z ∈ unitDisc, R ≤ diskDist 0 z → |w z| ≤ ε) →
      ∀ z ∈ unitDisc, w z ≤ 0 := by
    intro w hw hpde hdec z₀ hz₀
    by_contra hpos
    push_neg at hpos
    obtain ⟨R, hR⟩ := hdec (w z₀ / 2) (by linarith)
    obtain ⟨ρ, hρ1, hρ⟩ := hball R
    have hz₀R : diskDist 0 z₀ ≤ R := by
      by_contra h
      have := hR z₀ hz₀ (not_le.mp h).le
      rw [abs_le] at this
      linarith [this.2]
    have hKD : closedBall (0 : ℂ) ρ ⊆ unitDisc := closedBall_subset_ball hρ1
    have hz₀K : z₀ ∈ closedBall (0 : ℂ) ρ := mem_closedBall_zero_iff.mpr (hρ z₀ hz₀ hz₀R)
    obtain ⟨z₁, hz₁K, hmax⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_isMaxOn ⟨z₀, hz₀K⟩
      (hw.continuousOn.mono hKD)
    have hz₁ : z₁ ∈ unitDisc := hKD hz₁K
    have h01 : w z₀ ≤ w z₁ := hmax hz₀K
    have hloc : IsLocalMax w z₁ := by
      filter_upwards [isOpen_ball.mem_nhds hz₁] with y hy
      by_cases hyK : y ∈ closedBall (0 : ℂ) ρ
      · exact hmax hyK
      · have hd : R ≤ diskDist 0 y := by
          by_contra h
          exact hyK (mem_closedBall_zero_iff.mpr (hρ y hy (not_le.mp h).le))
        have := hR y hy hd
        rw [abs_le] at this
        linarith [this.2]
    have hc : ContDiffAt ℝ 2 w z₁ := hw.contDiffAt (isOpen_ball.mem_nhds hz₁)
    have hlap : Laplacian.laplacian w z₁ ≤ 0 := by
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
      beta_reduce
      rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith [s05_second_nonpos hc hloc 1, s05_second_nonpos hc hloc I]
    have hh : hypLaplacianDisk w z₁ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hlap
    have := hpde z₁ hz₁
    nlinarith
  intro z hz
  have h1 := key w hw hpde hdec z hz
  have h2 := key (fun y => -w y) hw.neg (fun y hy => by
      have e : hypLaplacianDisk (fun y => -w y) y = -hypLaplacianDisk w y := by
        simp only [hypLaplacianDisk]
        rw [show (fun y => -w y) = -w from rfl, InnerProductSpace.laplacian_neg]
        simp
      show κ * -w y - hypLaplacianDisk (fun y => -w y) y = 0
      rw [e]
      linarith [hpde y hy])
    (fun ε hε => by
      obtain ⟨R, hR⟩ := hdec ε hε
      exact ⟨R, fun y hy hd => by
        show |-w y| ≤ ε
        rw [abs_neg]
        exact hR y hy hd⟩) z hz
  have h2' : -w z ≤ 0 := h2
  linarith

/-- Helper (P10) for Proposition 12.5: the kernel bound `∫ k_q² F ≤ 16 e^{2r₁} ‖F‖₁ e^{-2r(q)}`
for `F ≥ 0` supported in `{r ≤ r₁}` (Step 5 of the proof). -/
theorem s12_pt_kernel {F : ℂ → ℝ} (hFc : Continuous F) (hF0 : ∀ z, 0 ≤ F z)
    (hFs : HasCompactSupport F) (hsub : tsupport F ⊆ unitDisc) {r₁ : ℝ}
    (hr : ∀ z ∈ unitDisc, F z ≠ 0 → diskDist 0 z ≤ r₁) {q : ℂ} (hq : q ∈ unitDisc) :
    ∫⁻ z in unitDisc, ENNReal.ofReal (diskKernelSq q z ^ 2 * F z) ∂diskHypArea ≤
      ENNReal.ofReal (16 * Real.exp (2 * r₁) * (∫ z, F z ∂diskHypArea) *
        Real.exp (-2 * diskDist 0 q)) := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  set A := 16 * Real.exp (2 * r₁) * Real.exp (-2 * diskDist 0 q) with hA
  have hA0 : 0 ≤ A := by positivity
  have hpt : ∀ z ∈ unitDisc, ENNReal.ofReal (diskKernelSq q z ^ 2 * F z) ≤
      ENNReal.ofReal A * ENNReal.ofReal (F z) := by
    intro z hz
    rw [← ENNReal.ofReal_mul hA0]
    apply ENNReal.ofReal_le_ofReal
    by_cases hFz : F z = 0
    · rw [hFz]; simp
    have hdz := hr z hz hFz
    have hqz : 0 ≤ diskDist q z := s02_diskDist_nonneg hq hz
    have hk : diskKernelSq q z ≤ 4 * Real.exp (-diskDist q z) := (eq_kernel_exp hqz).2
    have hk0 : 0 ≤ diskKernelSq q z := by unfold diskKernelSq; positivity
    have htri := s02_diskDist_triangle h0 hz hq
    rw [s02_diskDist_comm hz hq] at htri
    have hk2 : diskKernelSq q z ^ 2 ≤ A := by
      calc diskKernelSq q z ^ 2 ≤ (4 * Real.exp (-diskDist q z)) ^ 2 :=
            pow_le_pow_left₀ hk0 hk 2
        _ = 16 * Real.exp (-2 * diskDist q z) := by
            rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; ring_nf
        _ ≤ A := by
            rw [hA, mul_assoc, ← Real.exp_add]
            gcongr
            linarith
    exact mul_le_mul_of_nonneg_right hk2 (hF0 z)
  have hint : Integrable F diskHypArea := by
    obtain ⟨ρ, hρ0, hρ1, hρK⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ tsupport F ⊆ closedBall 0 ρ := by
      rcases (tsupport F).eq_empty_or_nonempty with h | h
      · exact ⟨0, le_rfl, one_pos, by simp [h]⟩
      · obtain ⟨z₀, hz₀, hmax⟩ := hFs.isCompact.exists_isMaxOn h continuous_norm.continuousOn
        exact ⟨‖z₀‖, norm_nonneg _, mem_ball_zero_iff.mp (hsub hz₀), fun z hz =>
          mem_closedBall_zero_iff.mpr (hmax hz)⟩
    obtain ⟨C, hC⟩ := hFc.bounded_above_of_compact_support hFs
    have hfin : diskHypArea (closedBall 0 ρ) ≠ ∞ := by
      have hρ2 : 0 < 1 - ρ ^ 2 := by nlinarith
      rw [diskHypArea, withDensity_apply _ measurableSet_closedBall]
      refine ne_of_lt (lt_of_le_of_lt (setLIntegral_mono
        (g := fun _ => ENNReal.ofReal ((2 / (1 - ρ ^ 2)) ^ 2)) measurable_const
        fun z hz => ?_) ?_)
      · apply ENNReal.ofReal_le_ofReal
        have hz' : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.mp hz
        have h1 : 1 - ρ ^ 2 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
        have h2 : 2 / (1 - ‖z‖ ^ 2) ≤ 2 / (1 - ρ ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) hρ2 h1
        have h3 : 0 ≤ 2 / (1 - ‖z‖ ^ 2) := div_nonneg (by norm_num) (by linarith)
        exact pow_le_pow_left₀ h3 h2 2
      · rw [setLIntegral_const]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [Measure.restrict_apply measurableSet_closedBall]
        exact lt_of_le_of_lt (measure_mono inter_subset_left) measure_closedBall_lt_top
    refine (integrableOn_iff_integrable_of_support_subset
      ((subset_tsupport F).trans hρK)).mp ?_
    exact Measure.integrableOn_of_bounded hfin hFc.aestronglyMeasurable (M := C)
      (Eventually.of_forall fun z => hC z)
  have hmeasF : Measurable fun z => ENNReal.ofReal (F z) := hFc.measurable.ennreal_ofReal
  calc ∫⁻ z in unitDisc, ENNReal.ofReal (diskKernelSq q z ^ 2 * F z) ∂diskHypArea
      ≤ ∫⁻ z in unitDisc, ENNReal.ofReal A * ENNReal.ofReal (F z) ∂diskHypArea :=
        setLIntegral_mono (measurable_const.mul hmeasF) hpt
    _ = ENNReal.ofReal A * ∫⁻ z in unitDisc, ENNReal.ofReal (F z) ∂diskHypArea :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal A * ∫⁻ z, ENNReal.ofReal (F z) ∂diskHypArea := by
        gcongr; exact Measure.restrict_le_self
    _ = ENNReal.ofReal A * ENNReal.ofReal (∫ z, F z ∂diskHypArea) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hF0)]
    _ = _ := by
        rw [← ENNReal.ofReal_mul hA0]
        congr 1
        rw [hA]
        ring

/-- Proposition 12.5 `prop:perturbation`, `sec12-counter.tex:466`: for `0 < κ < 2` and
`β = ½(1 + √(1+4κ))` (so `1 < β < 2`, `β(β-1) = κ`) there are `u ∈ C^∞(S)`, `F ∈ C_c^∞(S)` and
`r₁ > 1` with (a) `(κ - Δ)u = F`, `F ≥ 0`, `F ≢ 0`; (b) `u > 0`, `u → 0` at infinity, and `u` is
the only `C²` solution tending to `0`; (c) `∫ k_q² F dâ ≤ 16 e^{2r₁} ‖F‖₁ e^{-2r(q)}` and
`u(q) ≥ e^{-β r(q)}` for `r(q) ≥ r₁`.  Here `S = 𝔻`, `o = 0`, `r = d(0, ·)`. -/
theorem prop_perturbation {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) :
    let β := (1 + Real.sqrt (1 + 4 * κ)) / 2
    (1 < β ∧ β < 2 ∧ β * (β - 1) = κ) ∧
    ∃ (u F : ℂ → ℝ) (r₁ : ℝ), 1 < r₁ ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u unitDisc ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ unitDisc ∧
      (∀ z ∈ unitDisc, κ * u z - hypLaplacianDisk u z = F z) ∧ (∀ z, 0 ≤ F z) ∧
      (∃ z ∈ unitDisc, F z ≠ 0) ∧
      (∀ z ∈ unitDisc, 0 < u z) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z ∈ unitDisc, R ≤ diskDist 0 z → |u z| ≤ ε) ∧
      (∀ v : ℂ → ℝ, ContDiffOn ℝ 2 v unitDisc →
        (∀ z ∈ unitDisc, κ * v z - hypLaplacianDisk v z = F z) →
        (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z ∈ unitDisc, R ≤ diskDist 0 z → |v z| ≤ ε) →
        EqOn v u unitDisc) ∧
      (∀ q ∈ unitDisc,
        ∫⁻ z in unitDisc, ENNReal.ofReal (diskKernelSq q z ^ 2 * F z) ∂diskHypArea ≤
          ENNReal.ofReal (16 * Real.exp (2 * r₁) * (∫ z, F z ∂diskHypArea) *
            Real.exp (-2 * diskDist 0 q))) ∧
      ∀ q ∈ unitDisc, r₁ ≤ diskDist 0 q → Real.exp (-β * diskDist 0 q) ≤ u q := by
  intro β
  -- the exponent `β`
  have hs1 : 1 < Real.sqrt (1 + 4 * κ) := (Real.lt_sqrt (by norm_num)).mpr (by linarith)
  have hs3 : Real.sqrt (1 + 4 * κ) < 3 := (Real.sqrt_lt' (by norm_num)).mpr (by linarith)
  have hss : Real.sqrt (1 + 4 * κ) ^ 2 = 1 + 4 * κ := Real.sq_sqrt (by linarith)
  have hβ1 : 1 < β := by show 1 < (1 + Real.sqrt (1 + 4 * κ)) / 2; linarith
  have hβ2 : β < 2 := by show (1 + Real.sqrt (1 + 4 * κ)) / 2 < 2; linarith
  have hβκ : β * (β - 1) = κ := by
    show (1 + Real.sqrt (1 + 4 * κ)) / 2 * ((1 + Real.sqrt (1 + 4 * κ)) / 2 - 1) = κ
    linear_combination hss / 4
  have hβ : 0 < β := by linarith
  refine ⟨⟨hβ1, hβ2, hβκ⟩, ?_⟩
  obtain ⟨u, F, r₁, hr₁, hus, hFs, hcs, hts, hpde, hF0, hF00, hupos, hFr, -, huv⟩ :=
    s12_pt_build hβ1 hβ2
  rw [hβκ] at hpde
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hq2 : 0 < 1 - Real.exp (-2) := by
    have : Real.exp (-2) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
    rw [Real.exp_zero] at this
    linarith
  -- decay of `u`
  have hudec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z ∈ unitDisc, R ≤ diskDist 0 z → |u z| ≤ ε := by
    intro ε hε
    have ht : Tendsto (fun r : ℝ => Real.exp (-β * r) / (1 - Real.exp (-2))) atTop (𝓝 0) := by
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hβ)).div_const (1 - Real.exp (-2))
      rw [zero_div] at h
      refine h.congr fun r => ?_
      simp only [Function.comp, id]
      ring_nf
    obtain ⟨R, hR, hRr⟩ := ((ht.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop r₁)).exists
    refine ⟨R, fun z hz hd => ?_⟩
    have hdz : r₁ ≤ diskDist 0 z := hRr.trans hd
    rw [huv z hz hdz, abs_of_pos ((Real.exp_pos _).trans_le
      (s12_pt_v_bounds hβ (by linarith)).1)]
    calc s12_pt_v β (diskDist 0 z) ≤ Real.exp (-β * diskDist 0 z) / (1 - Real.exp (-2)) :=
          (s12_pt_v_bounds hβ (by linarith)).2.2 (by linarith)
      _ ≤ Real.exp (-β * R) / (1 - Real.exp (-2)) :=
          div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) hq2.le
      _ ≤ ε := hR.le
  refine ⟨u, F, r₁, hr₁, hus, hFs, hcs, hts, hpde, hF0, ⟨0, h0, hF00⟩, hupos, hudec,
    fun v hv hvp hvd => ?_, fun q hq => s12_pt_kernel hFs.continuous hF0 hcs hts hFr hq,
    fun q hq hd => ?_⟩
  · -- uniqueness
    have hu2 : ContDiffOn ℝ 2 u unitDisc :=
      by exact_mod_cast contDiffOn_infty.mp hus 2
    have hw := s12_pt_unique (w := fun z => v z - u z) hκ (hv.sub hu2) (fun z hz => by
        have hc1 : ContDiffAt ℝ 2 v z := hv.contDiffAt (isOpen_ball.mem_nhds hz)
        have hc2 : ContDiffAt ℝ 2 u z := hu2.contDiffAt (isOpen_ball.mem_nhds hz)
        have e : hypLaplacianDisk (fun z => v z - u z) z =
            hypLaplacianDisk v z - hypLaplacianDisk u z := by
          simp only [hypLaplacianDisk]
          rw [show (fun z => v z - u z) = v - u from rfl, hc1.laplacian_sub hc2]
          ring
        rw [e]
        linarith [hvp z hz, hpde z hz])
      (fun ε hε => by
        obtain ⟨R₁, hR₁⟩ := hvd (ε / 2) (by linarith)
        obtain ⟨R₂, hR₂⟩ := hudec (ε / 2) (by linarith)
        refine ⟨max R₁ R₂, fun z hz hd => ?_⟩
        have h1 := hR₁ z hz ((le_max_left _ _).trans hd)
        have h2 := hR₂ z hz ((le_max_right _ _).trans hd)
        calc |v z - u z| ≤ |v z| + |u z| := abs_sub _ _
          _ ≤ ε := by linarith)
    intro z hz
    have h : v z - u z = 0 := hw z hz
    linarith
  · -- the lower bound
    rw [huv q hq hd]
    exact (s12_pt_v_bounds hβ (by linarith)).1

/-- Remark `rem:perturbation`(i), `sec12-counter.tex:565–575`, the precise consequence for the
operators `κ - Δ_ρ` on `Ω = 𝔻`: for each `ε' ∈ (0, 1/8]`, with `κ = 2 - ε'`, there are a source
`0 ≤ F ∈ C_c^∞(𝔻)` and the decaying solution `u` of `(κ - Δ)u = F` for which no constant `C` gives
`u(q) ≤ C ∫ k_q² (κ - Δ)u dâ` for all `q`.  (The `ε'`-admissibility of `κ - Δ_ρ` refers to
`eq:operator`/`eq:admissible` of §5 and is not restated here.) -/
theorem rem_perturbation_i {ε' : ℝ} (hε : 0 < ε') (hε' : ε' ≤ 1 / 8) :
    ∃ u F : ℂ → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u unitDisc ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ unitDisc ∧
      (∀ z, 0 ≤ F z) ∧ (∀ z ∈ unitDisc, (2 - ε') * u z - hypLaplacianDisk u z = F z) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z ∈ unitDisc, R ≤ diskDist 0 z → |u z| ≤ ε) ∧
      ∀ C : ℝ, ∃ q ∈ unitDisc,
        ENNReal.ofReal C * ∫⁻ z in unitDisc, ENNReal.ofReal (diskKernelSq q z ^ 2 * F z) ∂diskHypArea <
          ENNReal.ofReal (u q) := by
  have h := prop_perturbation (κ := 2 - ε') (by linarith) (by linarith)
  obtain ⟨⟨hβ1, hβ2, -⟩, u, F, r₁, hr₁, hus, hFs, hcs, hts, hpde, hF0, -, hupos, hudec, -,
    hker, hlow⟩ := h
  set β := (1 + Real.sqrt (1 + 4 * (2 - ε'))) / 2 with hβdef
  refine ⟨u, F, hus, hFs, hcs, hts, hF0, hpde, hudec, fun C => ?_⟩
  set I := ∫ z, F z ∂diskHypArea with hI
  have hI0 : 0 ≤ I := integral_nonneg hF0
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set A := 16 * Real.exp (2 * r₁) * I with hA
  have hA0 : 0 ≤ A := by positivity
  have h2β : 0 < 2 - β := by linarith
  set R := max r₁ (C' * A / (2 - β)) with hR
  have hRr : r₁ ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := by linarith
  -- a point `q` with `d(0, q) = R`
  obtain ⟨hC, -, -, -, -⟩ := s12_pt_dist
  set K := Real.cosh R with hK
  have hK1 : 1 ≤ K := Real.one_le_cosh R
  set t := Real.sqrt ((K - 1) / (K + 1)) with ht
  have ht2 : t ^ 2 = (K - 1) / (K + 1) := Real.sq_sqrt (div_nonneg (by linarith) (by linarith))
  have ht1 : t < 1 := by
    have : (K - 1) / (K + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    calc t < Real.sqrt 1 := Real.sqrt_lt_sqrt (div_nonneg (by linarith) (by linarith)) this
      _ = 1 := Real.sqrt_one
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  set q : ℂ := (t : ℂ) with hq
  have hqn : ‖q‖ = t := by rw [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hqD : q ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hqn]; exact ht1)
  have hdq : diskDist 0 q = R := by
    have hcq : diskCoshDist 0 q = K := by
      rw [hC, hqn, ht2]
      field_simp
      ring
    show Real.arcosh (diskCoshDist 0 q) = R
    rw [hcq, hK, Real.arcosh_cosh hR0]
  refine ⟨q, hqD, ?_⟩
  have hkq := hker q hqD
  rw [hdq] at hkq
  have hlq := hlow q hqD (by rw [hdq]; exact hRr)
  rw [hdq] at hlq
  -- the real inequality `C' A e^{-2R} < e^{-βR}`
  have hkey : C' * (16 * Real.exp (2 * r₁) * I * Real.exp (-2 * R)) < Real.exp (-β * R) := by
    have hle : C' * A ≤ R * (2 - β) := (div_le_iff₀ h2β).mp (le_max_right _ _)
    have h1 : C' * A < Real.exp ((2 - β) * R) := by
      have := Real.add_one_le_exp ((2 - β) * R)
      nlinarith
    calc C' * (16 * Real.exp (2 * r₁) * I * Real.exp (-2 * R)) = C' * A * Real.exp (-2 * R) := by
          rw [hA]; ring
      _ < Real.exp ((2 - β) * R) * Real.exp (-2 * R) :=
          mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
      _ = Real.exp (-β * R) := by rw [← Real.exp_add]; ring_nf
  calc ENNReal.ofReal C * ∫⁻ z in unitDisc, ENNReal.ofReal (diskKernelSq q z ^ 2 * F z) ∂diskHypArea
      ≤ ENNReal.ofReal C' * ENNReal.ofReal (16 * Real.exp (2 * r₁) * I * Real.exp (-2 * R)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hkq
    _ = ENNReal.ofReal (C' * (16 * Real.exp (2 * r₁) * I * Real.exp (-2 * R))) :=
        (ENNReal.ofReal_mul hC'0).symm
    _ < ENNReal.ofReal (Real.exp (-β * R)) :=
        (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mpr hkey
    _ ≤ ENNReal.ofReal (u q) := ENNReal.ofReal_le_ofReal hlq

/-! ## A cusp at infinity -/

/-- `g(w) = -w² - log(1 + w)` (principal branch) of Proposition `prop:cusp`. -/
def cuspMap (w : ℂ) : ℂ := -w ^ 2 - Complex.log (1 + w)

/-- The extension (12.?) `eq:mw-extension` of [MW, (1.6)]:
`ĥ(z) = h(z*) + 2 Re z h'(z*)/(1 - Re z Ph(z*))`, `z* = -z̄`. -/
def mwExt (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  h (-conj z) + (2 * z.re) * deriv h (-conj z) /
    (1 - z.re * TakhtajanTeo.Ch2.preSchwarzian h (-conj z))

/-- Helper: `s(φ(z)) = (Re z)² |S φ(z)|` for a conformal `φ : ℍ_r → Ω`. -/
theorem s12_schwarzNorm_rhp {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ rightHalf Ω) {z : ℂ}
    (hz : z ∈ rightHalf) :
    schwarzNorm Ω (φ z) = z.re ^ 2 * ‖schwarzian φ z‖ := by
  have hx : 0 < z.re := hz
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hden : ∀ v ∈ unitDisc, (-1 : ℂ) * v + 1 ≠ 0 := by
    intro v hv h
    have : v = 1 := by linear_combination -h
    have hv1 := mem_ball_zero_iff.mp hv
    rw [this, norm_one] at hv1
    exact lt_irrefl _ hv1
  set M : ℂ → ℂ := fun v => ((1 : ℂ) * v + 1) / ((-1 : ℂ) * v + 1) with hMdef
  have hMB : M '' unitDisc = rightHalf := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      show 0 < (((1 : ℂ) * v + 1) / ((-1 : ℂ) * v + 1)).re
      rw [s12_rhp_re]
      have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
      have hn : normSq v < 1 := normSq_lt_one_iff.mpr hv1
      have hA : (1 : ℂ) - v ≠ 0 := by
        intro h
        have : v = 1 := (sub_eq_zero.mp h).symm
        rw [this, norm_one] at hv1
        exact lt_irrefl _ hv1
      exact div_pos (by linarith) (normSq_pos.mpr hA)
    · intro hu
      obtain ⟨h1, h2⟩ := s12_rhp_pre hu
      exact ⟨_, h1, h2⟩
  have hBo : IsOpen rightHalf := isOpen_lt continuous_const Complex.continuous_re
  have hdet : (1 : ℂ) * 1 - 1 * (-1) ≠ 0 := by norm_num
  have hMm : MapsTo M unitDisc rightHalf := fun v hv => hMB ▸ mem_image_of_mem M hv
  have hMd : DifferentiableOn ℂ M unitDisc := fun v hv =>
    ((hasDerivAt_mobius (a := 1) (b := 1) (hden v hv)).differentiableAt).differentiableWithinAt
  have hMi : InjOn M unitDisc := by
    intro v₁ h₁ v₂ h₂ he
    have hd₁ := hden v₁ h₁
    have hd₂ := hden v₂ h₂
    simp only [hMdef] at he
    rw [div_eq_div_iff hd₁ hd₂] at he
    have : ((1 : ℂ) * 1 - 1 * (-1)) * (v₁ - v₂) = 0 := by linear_combination he
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hdet
    · exact sub_eq_zero.mp h
  have hF : IsConformalOnto (φ ∘ M) unitDisc Ω :=
    ⟨hφ.1.comp hMd hMm, hφ.2.1.comp hMi hMm, by rw [Set.image_comp, hMB, hφ.2.2]⟩
  obtain ⟨hw, hMw⟩ := s12_rhp_pre hz
  set w := (z - 1) / (z + 1) with hwdef
  have hMw' : M w = z := hMw
  have hd := hden w hw
  have hMA : AnalyticAt ℂ M w := hMd.analyticAt (isOpen_ball.mem_nhds hw)
  have hDM : deriv M w = ((1 : ℂ) * 1 - 1 * (-1)) / ((-1 : ℂ) * w + 1) ^ 2 :=
    (hasDerivAt_mobius (a := 1) (b := 1) hd).deriv
  have hM' : deriv M w ≠ 0 := by rw [hDM]; exact div_ne_zero hdet (pow_ne_zero 2 hd)
  have hφA : AnalyticAt ℂ φ (M w) := hφ.1.analyticAt (hBo.mem_nhds (hMm hw))
  have hφ' : deriv φ (M w) ≠ 0 := deriv_ne_zero_of_injOn hBo hφ.1 hφ.2.1 (hMm hw)
  have hchain := eq19_1_chain_rule hMA hM' hφA hφ'
  rw [schwarzian_mobius hdet w, add_zero, hMw'] at hchain
  have hs := eq_s_disk hF hw
  rw [Function.comp_apply, hMw', hchain] at hs
  have h1w : (-1 : ℂ) * w + 1 = 2 / (z + 1) := by rw [hwdef]; field_simp; ring
  have hD2 : ((1 : ℂ) * 1 - 1 * (-1)) / (2 / (z + 1)) ^ 2 = (z + 1) ^ 2 / 2 := by
    field_simp
    ring
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hs, norm_mul, norm_pow, hDM, h1w, hD2, norm_div, norm_pow, h2, Complex.sq_norm (z := w),
    hwdef, Complex.normSq_div]
  have hp : 0 < normSq (z + 1) := normSq_pos.mpr hz1
  have hpq : normSq (z + 1) - normSq (z - 1) = 4 * z.re := by
    simp only [normSq_apply, add_re, add_im, sub_re, sub_im, one_re, one_im]
    ring
  have h3 : 1 - normSq (z - 1) / normSq (z + 1) = 4 * z.re / normSq (z + 1) := by
    rw [← hpq]
    field_simp
  rw [h3, ← Complex.sq_norm] at *
  have hp' : 0 < ‖z + 1‖ := norm_pos_iff.mpr hz1
  field_simp
  ring

/-- Helper: `1 + w ∈ slitPlane` for `Re w > -1`. -/
theorem s12_cusp_slit {w : ℂ} (hw : -1 < w.re) : 1 + w ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))

theorem s12_cusp_hasDerivAt {w : ℂ} (hw : -1 < w.re) :
    HasDerivAt cuspMap (-(2 * w) - 1 / (1 + w)) w := by
  have h1 : HasDerivAt (fun v : ℂ => 1 + v) 1 w := (hasDerivAt_id w).const_add 1
  have h2 := h1.clog (s12_cusp_slit hw)
  have h3 : HasDerivAt (fun v : ℂ => v ^ 2) (2 * w) w := by simpa using hasDerivAt_pow 2 w
  exact h3.neg.sub h2

theorem s12_cusp_g1_hasDerivAt {w : ℂ} (hw : 1 + w ≠ 0) :
    HasDerivAt (fun v : ℂ => -(2 * v) - 1 / (1 + v)) (-2 + 1 / (1 + w) ^ 2) w := by
  have h1 : HasDerivAt (fun v : ℂ => 1 + v) 1 w := (hasDerivAt_id w).const_add 1
  have h2 := (hasDerivAt_const w (1 : ℂ)).div h1 hw
  have h3 : HasDerivAt (fun v : ℂ => 2 * v) 2 w := by
    simpa using (hasDerivAt_id w).const_mul (2 : ℂ)
  convert h3.neg.sub h2 using 1
  field_simp
  ring

theorem s12_cusp_g2_hasDerivAt {w : ℂ} (hw : 1 + w ≠ 0) :
    HasDerivAt (fun v : ℂ => -2 + 1 / (1 + v) ^ 2) (-2 / (1 + w) ^ 3) w := by
  have h1 : HasDerivAt (fun v : ℂ => (1 + v) ^ 2) (2 * (1 + w)) w := by
    have := ((hasDerivAt_id w).const_add (1 : ℂ)).mul ((hasDerivAt_id w).const_add (1 : ℂ))
    convert this using 1
    · funext v
      simp [sq]
    · simp
      ring
  have h2 := (hasDerivAt_const w (1 : ℂ)).div h1 (pow_ne_zero 2 hw)
  convert (hasDerivAt_const w (-2 : ℂ)).add h2 using 1
  field_simp
  ring

/-- Helper: the Schwarzian of `g` on `{Re w ≥ 0}`, with `g' = -2w - 1/(1+w)`. -/
theorem s12_cusp_schwarzian {w : ℂ} (hw : 0 ≤ w.re) (h1 : -(2 * w) - 1 / (1 + w) ≠ 0) :
    schwarzian cuspMap w =
      (-2 / (1 + w) ^ 3) / (-(2 * w) - 1 / (1 + w)) -
        3 / 2 * ((-2 + 1 / (1 + w) ^ 2) / (-(2 * w) - 1 / (1 + w))) ^ 2 := by
  have hUo : IsOpen {v : ℂ | -1 < v.re} := isOpen_lt continuous_const Complex.continuous_re
  have hwU : w ∈ {v : ℂ | -1 < v.re} := show -1 < w.re by linarith
  have hne : ∀ v ∈ {v : ℂ | -1 < v.re}, 1 + v ≠ 0 := by
    intro v hv h
    have h' := congrArg Complex.re h
    have hv' : -1 < v.re := hv
    simp at h'
    linarith
  have hD1 : ∀ v ∈ {v : ℂ | -1 < v.re}, deriv cuspMap v = -(2 * v) - 1 / (1 + v) :=
    fun v hv => (s12_cusp_hasDerivAt hv).deriv
  have hE1 : deriv cuspMap =ᶠ[𝓝 w] fun v => -(2 * v) - 1 / (1 + v) :=
    eventually_of_mem (hUo.mem_nhds hwU) hD1
  have hD2 : ∀ v ∈ {v : ℂ | -1 < v.re}, deriv (deriv cuspMap) v = -2 + 1 / (1 + v) ^ 2 := by
    intro v hv
    have hE : deriv cuspMap =ᶠ[𝓝 v] fun v => -(2 * v) - 1 / (1 + v) :=
      eventually_of_mem (hUo.mem_nhds hv) hD1
    rw [hE.deriv_eq]
    exact (s12_cusp_g1_hasDerivAt (hne v hv)).deriv
  have hE2 : deriv (deriv cuspMap) =ᶠ[𝓝 w] fun v => -2 + 1 / (1 + v) ^ 2 :=
    eventually_of_mem (hUo.mem_nhds hwU) hD2
  have hA : AnalyticAt ℂ cuspMap w := by
    have hd : DifferentiableOn ℂ cuspMap {v : ℂ | -1 < v.re} := fun v hv =>
      (s12_cusp_hasDerivAt hv).differentiableAt.differentiableWithinAt
    exact hd.analyticAt (hUo.mem_nhds hwU)
  rw [schwarzian_of_analyticAt hA]
  unfold schwarzianHol
  have hq : (fun v => deriv (deriv cuspMap) v / deriv cuspMap v) =ᶠ[𝓝 w]
      fun v => (-2 + 1 / (1 + v) ^ 2) / (-(2 * v) - 1 / (1 + v)) := by
    filter_upwards [hE1, hE2] with v h1 h2
    rw [h1, h2]
  have hdv : HasDerivAt (fun v => (-2 + 1 / (1 + v) ^ 2) / (-(2 * v) - 1 / (1 + v))) _ w :=
    (s12_cusp_g2_hasDerivAt (hne w hwU)).div (s12_cusp_g1_hasDerivAt (hne w hwU)) h1
  rw [hq.deriv_eq, hE1.self_of_nhds, hE2.self_of_nhds, hdv.deriv]
  have := hne w hwU
  beta_reduce
  field_simp
  ring

theorem s12_cusp_g1_norm {w : ℂ} (hw : 0 ≤ w.re) : 1 / 4 ≤ ‖-(2 * w) - 1 / (1 + w)‖ := by
  have hu : 1 ≤ (1 + w).re := by simp; linarith
  have hun : 1 ≤ ‖1 + w‖ := hu.trans (Complex.re_le_norm _)
  have hu0 : 1 + w ≠ 0 := fun h => by rw [h, norm_zero] at hun; norm_num at hun
  rcases le_or_gt ‖w‖ 1 with hw1 | hw1
  · have hns0 : 0 < normSq (1 + w) := normSq_pos.mpr hu0
    have hns : normSq (1 + w) ≤ 4 := by
      have h1 : ‖1 + w‖ ≤ 2 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (1 + w)]
    have hre : (-(2 * w) - 1 / (1 + w)).re = -(2 * w.re) - (1 + w).re / normSq (1 + w) := by
      rw [sub_re, neg_re, one_div, inv_re]
      simp
    have h1 : 1 / 4 ≤ 1 / normSq (1 + w) := one_div_le_one_div_of_le hns0 hns
    have h2 : 1 / normSq (1 + w) ≤ (1 + w).re / normSq (1 + w) :=
      div_le_div_of_nonneg_right hu hns0.le
    have h3 := Complex.abs_re_le_norm (-(2 * w) - 1 / (1 + w))
    have h4 := neg_le_abs (-(2 * w) - 1 / (1 + w)).re
    rw [hre] at h3 h4
    linarith
  · have h1 : ‖-(2 * w)‖ = 2 * ‖w‖ := by rw [norm_neg, norm_mul]; simp
    have h2 : ‖1 / (1 + w)‖ ≤ 1 := by
      rw [norm_div, norm_one, div_le_one (by linarith)]
      exact hun
    have h3 := norm_sub_norm_le (-(2 * w)) (1 / (1 + w))
    linarith

theorem s12_cusp_schwarzian_le {w : ℂ} (hw : 0 ≤ w.re) : ‖schwarzian cuspMap w‖ ≤ 224 := by
  have hg1 := s12_cusp_g1_norm hw
  have hg1' : -(2 * w) - 1 / (1 + w) ≠ 0 := fun h => by
    rw [h, norm_zero] at hg1
    norm_num at hg1
  rw [s12_cusp_schwarzian hw hg1']
  have hu : 1 ≤ (1 + w).re := by simp; linarith
  have hun : 1 ≤ ‖1 + w‖ := hu.trans (Complex.re_le_norm _)
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hn32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
    rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
    norm_num
  have hg3 : ‖-2 / (1 + w) ^ 3‖ ≤ 2 := by
    rw [norm_div, norm_pow, norm_neg, hn2]
    have : 1 ≤ ‖1 + w‖ ^ 3 := one_le_pow₀ hun
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hg2 : ‖-2 + 1 / (1 + w) ^ 2‖ ≤ 3 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_div, norm_one, norm_pow, hn2]
    have : 1 ≤ ‖1 + w‖ ^ 2 := one_le_pow₀ hun
    have : 1 / ‖1 + w‖ ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact this
    linarith
  set A := ‖-(2 * w) - 1 / (1 + w)‖ with hA
  calc ‖-2 / (1 + w) ^ 3 / (-(2 * w) - 1 / (1 + w)) -
        3 / 2 * ((-2 + 1 / (1 + w) ^ 2) / (-(2 * w) - 1 / (1 + w))) ^ 2‖
      ≤ ‖-2 / (1 + w) ^ 3 / (-(2 * w) - 1 / (1 + w))‖ +
        ‖3 / 2 * ((-2 + 1 / (1 + w) ^ 2) / (-(2 * w) - 1 / (1 + w))) ^ 2‖ := norm_sub_le _ _
    _ = ‖-2 / (1 + w) ^ 3‖ / A + 3 / 2 * (‖-2 + 1 / (1 + w) ^ 2‖ / A) ^ 2 := by
        have e1 : ‖-2 / (1 + w) ^ 3 / (-(2 * w) - 1 / (1 + w))‖ = ‖-2 / (1 + w) ^ 3‖ / A :=
          norm_div _ _
        have e2 : ‖3 / 2 * ((-2 + 1 / (1 + w) ^ 2) / (-(2 * w) - 1 / (1 + w))) ^ 2‖ =
            3 / 2 * (‖-2 + 1 / (1 + w) ^ 2‖ / A) ^ 2 := by
          rw [norm_mul, hn32, norm_pow, norm_div]
        rw [e1, e2]
    _ ≤ 2 / (1 / 4) + 3 / 2 * (3 / (1 / 4)) ^ 2 := by gcongr
    _ = 224 := by norm_num

/-- Helper: `g` is injective on `{Re w ≥ 0}` (Noshiro–Warschawski for `log(1+w)`). -/
theorem s12_cusp_injOn : InjOn cuspMap {w | 0 ≤ w.re} := by
  intro w1 hw1 w2 hw2 heq
  have h1 : (0 : ℝ) ≤ w1.re := hw1
  have h2 : (0 : ℝ) ≤ w2.re := hw2
  by_contra hne
  set d := w1 - w2 with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hne
  have hpath : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ (w2 + (t : ℂ) * d).re := by
    intro t ht0 ht1
    have : (w2 + (t : ℂ) * d).re = (1 - t) * w2.re + t * w1.re := by simp [hd]; ring
    rw [this]
    nlinarith
  set F : ℝ → ℝ := fun t => (Complex.log (1 + (w2 + (t : ℂ) * d)) * conj d).re with hF
  set F' : ℝ → ℝ := fun t => (d / (1 + (w2 + (t : ℂ) * d)) * conj d).re with hF'
  have hder : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → HasDerivAt F (F' t) t := by
    intro t ht0 ht1
    have hin : HasDerivAt (fun z : ℂ => 1 + (w2 + z * d)) d (t : ℂ) := by
      simpa using (((hasDerivAt_id (t : ℂ)).mul_const d).const_add w2).const_add (1 : ℂ)
    have hl := (hin.clog (s12_cusp_slit (by linarith [hpath t ht0 ht1]))).mul_const (conj d)
    exact hl.real_of_complex
  have hcont : ContinuousOn F (Icc 0 1) := fun t ht =>
    (hder t ht.1 ht.2).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcv⟩ := exists_hasDerivAt_eq_slope F F' zero_lt_one hcont
    fun t ht => hder t ht.1.le ht.2.le
  have hpos : 0 < F' c := by
    have hu : 0 < (1 + (w2 + (c : ℂ) * d)).re := by
      have := hpath c hc.1.le hc.2.le
      simp only [add_re, one_re] at this ⊢
      linarith
    have hu0 : 1 + (w2 + (c : ℂ) * d) ≠ 0 := fun h => by rw [h] at hu; simp at hu
    have he : d / (1 + (w2 + (c : ℂ) * d)) * conj d =
        ((normSq d : ℝ) : ℂ) * (1 + (w2 + (c : ℂ) * d))⁻¹ := by
      rw [← Complex.mul_conj]
      field_simp
    show 0 < (d / (1 + (w2 + (c : ℂ) * d)) * conj d).re
    rw [he, Complex.re_ofReal_mul, inv_re]
    exact mul_pos (normSq_pos.mpr hd0) (div_pos hu (normSq_pos.mpr hu0))
  have hlog : Complex.log (1 + w1) - Complex.log (1 + w2) = -((w1 + w2) * d) := by
    unfold cuspMap at heq
    rw [hd]
    linear_combination -heq
  have hF1 : F 1 = (Complex.log (1 + w1) * conj d).re := by
    simp only [hF]
    rw [show w2 + ((1 : ℝ) : ℂ) * d = w1 by rw [hd]; push_cast; ring]
  have hF0 : F 0 = (Complex.log (1 + w2) * conj d).re := by
    simp only [hF]
    rw [show w2 + ((0 : ℝ) : ℂ) * d = w2 by push_cast; ring]
  have hdiff : F 1 - F 0 = -((w1 + w2).re * normSq d) := by
    rw [hF1, hF0, ← sub_re, ← sub_mul, hlog,
      show -((w1 + w2) * d) * conj d = -((w1 + w2) * (d * conj d)) by ring, Complex.mul_conj]
    simp
  rw [sub_zero, div_one, hdiff] at hcv
  have : 0 ≤ (w1 + w2).re * normSq d := mul_nonneg (by simp; linarith) (normSq_nonneg d)
  linarith

theorem s12_cusp_conformal : IsConformalOnto cuspMap rightHalf (cuspMap '' rightHalf) :=
  ⟨fun v hv => (s12_cusp_hasDerivAt (by have : 0 < v.re := hv; linarith)).differentiableAt
      |>.differentiableWithinAt,
    s12_cusp_injOn.mono fun v (hv : 0 < v.re) => show 0 ≤ v.re from hv.le, rfl⟩

/-- Helper: `‖log u‖ ≤ ‖u‖ + π` for `‖u‖ ≥ 1`. -/
theorem s12_norm_log_le {u : ℂ} (hu : 1 ≤ ‖u‖) : ‖Complex.log u‖ ≤ ‖u‖ + π := by
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.log_re, Complex.log_im]
  have h1 : 0 ≤ Real.log ‖u‖ := Real.log_nonneg hu
  have h2 := Real.log_le_sub_one_of_pos (by linarith : 0 < ‖u‖)
  have h3 := Complex.abs_arg_le_pi u
  rw [abs_of_nonneg h1]
  linarith

/-- Helper: `|g(w)| ≥ |w|² - |w| - 1 - π` on `{Re w ≥ 0}`. -/
theorem s12_cusp_norm_ge {w : ℂ} (hw : 0 ≤ w.re) : ‖w‖ ^ 2 - ‖w‖ - 1 - π ≤ ‖cuspMap w‖ := by
  have hu : 1 ≤ ‖1 + w‖ := (show (1 : ℝ) ≤ (1 + w).re by simp; linarith).trans (re_le_norm _)
  have hl := s12_norm_log_le hu
  have hn : ‖1 + w‖ ≤ 1 + ‖w‖ := (norm_add_le _ _).trans (by rw [norm_one])
  have h1 : ‖-w ^ 2‖ = ‖w‖ ^ 2 := by rw [norm_neg, norm_pow]
  have h2 := norm_sub_norm_le (-w ^ 2) (Complex.log (1 + w))
  unfold cuspMap
  linarith

/-- Helper: on the imaginary axis, `Re g(iy) ≥ 0` and `|Im g(iy)| < π/2`. -/
theorem s12_cusp_axis_mem (y : ℝ) :
    0 ≤ (cuspMap ((y : ℂ) * I)).re ∧ |(cuspMap ((y : ℂ) * I)).im| < π / 2 := by
  have hsq : ((y : ℂ) * I) ^ 2 = -((y ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]
    push_cast
    ring
  have hn : ‖1 + (y : ℂ) * I‖ = √(1 + y ^ 2) := by
    rw [show (1 : ℂ) + (y : ℂ) * I = ((1 : ℝ) : ℂ) + (y : ℂ) * I by push_cast; ring,
      Complex.norm_add_mul_I, one_pow]
  constructor
  · have hre : (cuspMap ((y : ℂ) * I)).re = y ^ 2 - Real.log ‖1 + (y : ℂ) * I‖ := by
      unfold cuspMap
      rw [hsq, sub_re, neg_re, neg_re, ofReal_re, Complex.log_re]
      ring
    rw [hre, hn]
    have h1 : Real.log √(1 + y ^ 2) ≤ √(1 + y ^ 2) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : √(1 + y ^ 2) ≤ 1 + y ^ 2 / 2 := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · nlinarith [sq_nonneg (y ^ 2)]
    nlinarith [sq_nonneg y]
  · unfold cuspMap
    rw [hsq, sub_im, neg_im, neg_im, ofReal_im, Complex.log_im]
    simp only [neg_zero, zero_sub, abs_neg]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp))

/-- Proposition 12.6(a), last claim: `{Re ζ < 0} ∪ {|Im ζ| ≥ π/2} ⊆ Ω = g(ℍ_r)`. -/
theorem s12_cusp_image_contains :
    {ζ : ℂ | ζ.re < 0} ∪ {ζ : ℂ | π / 2 ≤ |ζ.im|} ⊆ cuspMap '' rightHalf := by
  have hBo : IsOpen rightHalf := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ cuspMap rightHalf := s12_cusp_conformal.1
  have hΩo : IsOpen (cuspMap '' rightHalf) := by
    rcases (hd.analyticOnNhd hBo).is_constant_or_isOpen
      (convex_halfSpace_re_gt 0).isPreconnected with ⟨c, hc⟩ | h
    · exfalso
      have h1 : cuspMap 1 = cuspMap 2 := by
        rw [hc 1 (show (0 : ℝ) < (1 : ℂ).re by simp), hc 2 (show (0 : ℝ) < (2 : ℂ).re by simp)]
      have := s12_cusp_injOn (show (0 : ℝ) ≤ (1 : ℂ).re by simp)
        (show (0 : ℝ) ≤ (2 : ℂ).re by simp) h1
      norm_num at this
    · exact h rightHalf subset_rfl hBo
  -- the closure of `Ω` adds only points of `g(iℝ)` (`g` is proper)
  have hcl : ∀ ζ ∈ closure (cuspMap '' rightHalf),
      ζ ∈ cuspMap '' rightHalf ∨ ∃ y : ℝ, cuspMap ((y : ℂ) * I) = ζ := by
    intro ζ hζ
    set R : ℝ := ‖ζ‖ + 6 with hR
    have hK : IsCompact ({w : ℂ | 0 ≤ w.re} ∩ closedBall 0 R) :=
      (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const Complex.continuous_re)
    have hgc : ContinuousOn cuspMap ({w : ℂ | 0 ≤ w.re} ∩ closedBall 0 R) := fun w hw => by
      have : (0 : ℝ) ≤ w.re := hw.1
      exact (s12_cusp_hasDerivAt (by linarith)).continuousAt.continuousWithinAt
    have hKc : IsClosed (cuspMap '' ({w : ℂ | 0 ≤ w.re} ∩ closedBall 0 R)) :=
      (hK.image_of_continuousOn hgc).isClosed
    have hmem : ζ ∈ cuspMap '' ({w : ℂ | 0 ≤ w.re} ∩ closedBall 0 R) := by
      refine hKc.closure_subset (Metric.mem_closure_iff.mpr fun ε hε => ?_)
      obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp hζ (min ε 1) (lt_min hε one_pos)
      obtain ⟨w, hw, rfl⟩ := hb
      have hw0 : (0 : ℝ) < w.re := hw
      refine ⟨cuspMap w, ⟨w, ⟨hw0.le, ?_⟩, rfl⟩, lt_of_lt_of_le hdist (min_le_left _ _)⟩
      rw [mem_closedBall, dist_zero_right]
      by_contra hgt
      rw [not_le] at hgt
      have h1 := s12_cusp_norm_ge hw0.le
      have h2 : dist ζ (cuspMap w) < 1 := lt_of_lt_of_le hdist (min_le_right _ _)
      rw [dist_eq_norm] at h2
      have h3 := norm_sub_norm_le (cuspMap w) ζ
      rw [norm_sub_rev] at h3
      have h4 : 5 * ‖w‖ ≤ ‖w‖ ^ 2 - ‖w‖ := by
        nlinarith [mul_nonneg (norm_nonneg w) (by linarith [norm_nonneg ζ] : 0 ≤ ‖w‖ - 6)]
      have h5 := Real.pi_le_four
      nlinarith [norm_nonneg ζ]
    obtain ⟨w, ⟨hw0, _⟩, rfl⟩ := hmem
    rcases (show (0 : ℝ) ≤ w.re from hw0).lt_or_eq with hlt | heq
    · exact Or.inl ⟨w, hlt, rfl⟩
    · refine Or.inr ⟨w.im, congrArg cuspMap (Complex.ext (by simp [← heq]) (by simp))⟩
  -- `S` is connected and avoids `g(iℝ)`
  have hS : IsPreconnected ({ζ : ℂ | ζ.re < 0} ∪ {ζ : ℂ | π / 2 ≤ |ζ.im|}) := by
    have e : {ζ : ℂ | π / 2 ≤ |ζ.im|} = {ζ : ℂ | π / 2 ≤ ζ.im} ∪ {ζ : ℂ | ζ.im ≤ -(π / 2)} := by
      ext ζ
      rw [Set.mem_union]
      show π / 2 ≤ |ζ.im| ↔ π / 2 ≤ ζ.im ∨ ζ.im ≤ -(π / 2)
      rw [le_abs']
      tauto
    have hπ := Real.pi_pos
    rw [e, ← union_assoc]
    refine IsPreconnected.union' ⟨⟨-1, -π⟩, Or.inl (show (-1 : ℝ) < 0 by norm_num),
      show -π ≤ -(π / 2) by linarith⟩ ?_ (convex_halfSpace_im_le _).isPreconnected
    exact IsPreconnected.union' ⟨⟨-1, π⟩, show (-1 : ℝ) < 0 by norm_num,
      show π / 2 ≤ π by linarith⟩ (convex_halfSpace_re_lt 0).isPreconnected
      (convex_halfSpace_im_ge _).isPreconnected
  have hsplit : {ζ : ℂ | ζ.re < 0} ∪ {ζ : ℂ | π / 2 ≤ |ζ.im|} ⊆
      cuspMap '' rightHalf ∪ (closure (cuspMap '' rightHalf))ᶜ := by
    intro ζ hζ
    by_cases hc : ζ ∈ closure (cuspMap '' rightHalf)
    · rcases hcl ζ hc with h | ⟨y, rfl⟩
      · exact Or.inl h
      · exfalso
        obtain ⟨h1, h2⟩ := s12_cusp_axis_mem y
        rcases hζ with h | h
        · exact absurd (show (cuspMap ((y : ℂ) * I)).re < 0 from h) (not_lt.mpr h1)
        · exact absurd (show π / 2 ≤ |(cuspMap ((y : ℂ) * I)).im| from h) (not_le.mpr h2)
    · exact Or.inr hc
  have hne : (({ζ : ℂ | ζ.re < 0} ∪ {ζ : ℂ | π / 2 ≤ |ζ.im|}) ∩ cuspMap '' rightHalf).Nonempty := by
    refine ⟨cuspMap 1, Or.inl ?_, ⟨1, show (0 : ℝ) < (1 : ℂ).re by simp, rfl⟩⟩
    have : (cuspMap 1).re = -1 - Real.log 2 := by
      unfold cuspMap
      rw [sub_re, Complex.log_re]
      norm_num
    show (cuspMap 1).re < 0
    rw [this]
    linarith [Real.log_pos one_lt_two]
  exact IsPreconnected.subset_left_of_subset_union hΩo isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left subset_closure) hsplit hne hS

theorem s12_cusp_deriv {w : ℂ} (hw : -1 < w.re) : deriv cuspMap w = -(2 * w) - 1 / (1 + w) :=
  (s12_cusp_hasDerivAt hw).deriv

theorem s12_cusp_deriv2 {w : ℂ} (hw : -1 < w.re) :
    deriv (deriv cuspMap) w = -2 + 1 / (1 + w) ^ 2 := by
  have hUo : IsOpen {v : ℂ | -1 < v.re} := isOpen_lt continuous_const Complex.continuous_re
  have hE : deriv cuspMap =ᶠ[𝓝 w] fun v => -(2 * v) - 1 / (1 + v) :=
    eventually_of_mem (hUo.mem_nhds hw) fun v hv => s12_cusp_deriv hv
  rw [hE.deriv_eq]
  have : 1 + w ≠ 0 := fun h => by
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  exact (s12_cusp_g1_hasDerivAt this).deriv

/-- Helper: for `t > 0` and large `y`, the denominator of `ĝ(-t+iy)` is nonzero, `ĝ(-t+iy)` is the
osculating point, and `|Im ĝ(-t+iy)| ≥ π/2`. -/
theorem s12_cusp_e_key {t : ℝ} (ht : 0 < t) : ∃ yt : ℝ, 0 < yt ∧ ∀ y : ℝ, yt ≤ y →
    1 - (-t) * TakhtajanTeo.Ch2.preSchwarzian cuspMap ⟨t, y⟩ ≠ 0 ∧
    awPoint (cuspMap '' rightHalf) (cuspMap ⟨t, y⟩) = (mwExt cuspMap ⟨-t, y⟩ : OnePoint ℂ) ∧
    mwExt cuspMap ⟨-t, y⟩ ∈ cuspMap '' rightHalf := by
  set cR : ℝ := |4 * t ^ 2 + 2| + |4 * t - 2| + |1 - 2 * t - 2 * t ^ 2| with hcR
  set cD : ℝ := |2 * t - 2| + 1 + t with hcD
  have hcR0 : 0 ≤ cR := by positivity
  have hcD0 : 0 ≤ cD := by positivity
  have hπ := Real.pi_pos
  refine ⟨cD + 2 * t * cR + (3 * π / 2 + 1) / (2 * t) + 1, by positivity, fun y hy => ?_⟩
  have hq0 : 0 ≤ (3 * π / 2 + 1) / (2 * t) := by positivity
  have hy1 : cD ≤ y := by nlinarith
  have hy2 : 2 * t * cR ≤ y := by nlinarith
  have hy3 : 3 * π / 2 + 1 ≤ 2 * t * y := by
    have h : (3 * π / 2 + 1) / (2 * t) ≤ y := by nlinarith
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * t)).mp h
    linarith
  have hypos : 0 < y := by nlinarith
  set w : ℂ := ⟨t, y⟩ with hwdef
  have hwr : w.re = t := rfl
  have hwi : w.im = y := rfl
  have hwR : w ∈ rightHalf := show 0 < w.re from ht
  have hw1 : -1 < w.re := by rw [hwr]; linarith
  have hg1ne : -(2 * w) - 1 / (1 + w) ≠ 0 := fun h => by
    have := s12_cusp_g1_norm (show 0 ≤ w.re by rw [hwr]; exact ht.le)
    rw [h, norm_zero] at this
    norm_num at this
  have hPg : TakhtajanTeo.Ch2.preSchwarzian cuspMap w =
      (-2 + 1 / (1 + w) ^ 2) / (-(2 * w) - 1 / (1 + w)) := by
    unfold TakhtajanTeo.Ch2.preSchwarzian
    rw [s12_cusp_deriv hw1, s12_cusp_deriv2 hw1]
  have hdw := s12_cusp_deriv hw1
  have hcw : -conj w - w = -(2 * (t : ℂ)) := by
    apply Complex.ext <;> simp [hwr, hwi]
    ring
  have hmw : -conj (⟨-t, y⟩ : ℂ) = w := Complex.ext (by simp [hwr]) (by simp [hwi])
  have hlogim : (cuspMap w).im = -(2 * t * y) - arg (1 + w) := by
    unfold cuspMap
    simp only [sub_im, neg_im, Complex.log_im, sq, mul_im, hwr, hwi]
    ring
  -- pass to `u = 1 + w`
  set u : ℂ := 1 + w with hudef
  have hur : u.re = 1 + t := by simp [hudef, hwr]
  have hui : u.im = y := by simp [hudef, hwi]
  have hu1 : 1 ≤ ‖u‖ := (show (1 : ℝ) ≤ u.re by rw [hur]; linarith).trans (re_le_norm _)
  have huy : y ≤ ‖u‖ := by
    have := abs_im_le_norm u
    rw [hui] at this
    linarith [le_abs_self y]
  have hu0 : u ≠ 0 := fun h => by rw [h, norm_zero] at hu1; norm_num at hu1
  set P : ℂ := 2 * u ^ 2 - 2 * u + 1 with hPdef
  have hg1P : -(2 * w) - 1 / u = -P / u := by
    rw [hPdef, show w = u - 1 by rw [hudef]; ring]
    field_simp
    ring
  have hP0 : P ≠ 0 := fun h => by
    rw [hg1P, h, neg_zero, zero_div] at hg1ne
    exact hg1ne rfl
  have hg2P : -2 + 1 / u ^ 2 = (1 - 2 * u ^ 2) / u ^ 2 := by
    field_simp
    ring
  set D : ℂ := 2 * u ^ 3 + ((2 * t - 2 : ℝ) : ℂ) * u ^ 2 + u - (t : ℂ) with hD
  set R : ℂ := ((4 * t ^ 2 + 2 : ℝ) : ℂ) * u ^ 2 + ((4 * t - 2 : ℝ) : ℂ) * u +
    ((1 - 2 * t - 2 * t ^ 2 : ℝ) : ℂ) with hR
  have hDP : D = u * P + t * (2 * u ^ 2 - 1) := by
    rw [hD, hPdef]
    push_cast
    ring
  have hP2 : P ^ 2 = D * (2 * u - 2 - 2 * t) + R := by
    rw [hD, hR, hPdef]
    push_cast
    ring
  have hn2 : 1 ≤ ‖u‖ ^ 2 := one_le_pow₀ hu1
  have hn12 : ‖u‖ ≤ ‖u‖ ^ 2 := by nlinarith
  have hDge : ‖u‖ ^ 3 ≤ ‖D‖ := by
    have hQ : ‖((2 * t - 2 : ℝ) : ℂ) * u ^ 2 + u - (t : ℂ)‖ ≤ cD * ‖u‖ ^ 2 := by
      have e1 := norm_sub_le (((2 * t - 2 : ℝ) : ℂ) * u ^ 2 + u) (t : ℂ)
      have e2 := norm_add_le (((2 * t - 2 : ℝ) : ℂ) * u ^ 2) u
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at e2
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at e1
      have e3 := mul_le_mul_of_nonneg_left hn2 ht.le
      rw [hcD]
      nlinarith [abs_nonneg (2 * t - 2)]
    have h2 : ‖(2 : ℂ) * u ^ 3‖ = 2 * ‖u‖ ^ 3 := by rw [norm_mul, norm_pow]; simp
    have h3 := norm_sub_norm_le ((2 : ℂ) * u ^ 3)
      (-(((2 * t - 2 : ℝ) : ℂ) * u ^ 2 + u - (t : ℂ)))
    rw [norm_neg, sub_neg_eq_add] at h3
    have h4 : D = 2 * u ^ 3 + (((2 * t - 2 : ℝ) : ℂ) * u ^ 2 + u - (t : ℂ)) := by
      rw [hD]
      ring
    rw [h4]
    have h5 : cD * ‖u‖ ^ 2 ≤ ‖u‖ * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hy1.trans huy) (by positivity)
    nlinarith
  have hD0 : D ≠ 0 := fun h => by
    rw [h, norm_zero] at hDge
    have : 0 < ‖u‖ ^ 3 := by positivity
    linarith
  have hRle : ‖R‖ ≤ cR * ‖u‖ ^ 2 := by
    refine (norm_add₃_le).trans ?_
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [abs_nonneg (4 * t - 2), abs_nonneg (1 - 2 * t - 2 * t ^ 2),
      abs_nonneg (4 * t ^ 2 + 2)]
  -- the denominator
  have hden : 1 - (-(t : ℂ)) * TakhtajanTeo.Ch2.preSchwarzian cuspMap w = D / (u * P) := by
    rw [hPg, hg1P, hg2P, hDP]
    field_simp
    ring
  have hden0 : 1 - (-(t : ℂ)) * TakhtajanTeo.Ch2.preSchwarzian cuspMap w ≠ 0 := by
    rw [hden]
    exact div_ne_zero hD0 (mul_ne_zero hu0 hP0)
  -- `ĝ(-t+iy)` equals the osculating point
  have hosc : oscMob cuspMap w (-conj w) = mwExt cuspMap ⟨-t, y⟩ := by
    unfold oscMob mwExt
    rw [hmw, hcw]
    push_cast
    ring_nf
  have hosc_ne : 1 - (1 / 2) * TakhtajanTeo.Ch2.preSchwarzian cuspMap w * (-conj w - w) ≠ 0 := by
    rw [hcw]
    convert hden0 using 1
    ring
  -- the value of `ĝ(-t+iy)`
  have hV : mwExt cuspMap ⟨-t, y⟩ = cuspMap w +
      (4 * (t : ℂ) * u - 4 * t - 4 * t ^ 2) + 2 * t * R / D := by
    unfold mwExt
    rw [hmw, show ((⟨-t, y⟩ : ℂ).re : ℂ) = -(t : ℂ) by simp, hdw, hden, hg1P]
    calc cuspMap w + 2 * -(t : ℂ) * (-P / u) / (D / (u * P)) = cuspMap w + 2 * t * P ^ 2 / D := by
          field_simp
      _ = cuspMap w + 2 * t * (D * (2 * u - 2 - 2 * t) + R) / D := by rw [hP2]
      _ = _ := by
          field_simp
          ring
  have hIm : (mwExt cuspMap ⟨-t, y⟩).im = 2 * t * y - arg u + (2 * t * R / D).im := by
    rw [hV, add_im, add_im, hlogim]
    simp only [sub_im, mul_im, mul_re, ofReal_re, ofReal_im, hur, hui, re_ofNat, im_ofNat, sq]
    ring
  have hsmall : |(2 * t * R / D).im| ≤ 1 := by
    refine (abs_im_le_norm _).trans ?_
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, div_le_one (by positivity)]
    have hpos : 0 < ‖u‖ := by linarith
    calc 2 * t * ‖R‖ ≤ 2 * t * (cR * ‖u‖ ^ 2) := by gcongr
      _ = (2 * t * cR) * ‖u‖ ^ 2 := by ring
      _ ≤ ‖u‖ * ‖u‖ ^ 2 := by gcongr; linarith
      _ = ‖u‖ ^ 3 := by ring
      _ ≤ ‖D‖ := hDge
  have harg := Complex.abs_arg_le_pi u
  have hbig : π / 2 ≤ |(mwExt cuspMap ⟨-t, y⟩).im| := by
    rw [hIm]
    refine le_trans ?_ (le_abs_self _)
    have h1 := neg_abs_le (2 * t * R / D).im
    have h2 := le_abs_self (arg u)
    linarith
  refine ⟨hden0, ?_, s12_cusp_image_contains (Or.inr hbig)⟩
  rw [((lem_aw_point_rhp s12_cusp_conformal hwR).1 hosc_ne), hosc]

/-- Helper: the values of `g` on the imaginary axis. -/
theorem s12_cusp_axis (y : ℝ) : cuspMap ((y : ℂ) * I) =
    ((y ^ 2 - Real.log (1 + y ^ 2) / 2 : ℝ) : ℂ) - I * (Real.arctan y : ℂ) := by
  have hsq : ((y : ℂ) * I) ^ 2 = -((y ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]
    push_cast
    ring
  have hn : ‖1 + (y : ℂ) * I‖ = √(1 + y ^ 2) := by
    have := norm_add_mul_I 1 y
    rw [one_pow] at this
    simpa using this
  have hre : (Complex.log (1 + (y : ℂ) * I)).re = Real.log (1 + y ^ 2) / 2 := by
    rw [Complex.log_re, hn, Real.log_sqrt (by positivity)]
  have him : (Complex.log (1 + (y : ℂ) * I)).im = Real.arctan y := by
    rw [Complex.log_im, Complex.arg_of_re_nonneg (by simp), hn, Real.arctan_eq_arcsin]
    simp
  unfold cuspMap
  rw [hsq]
  apply Complex.ext
  · rw [sub_re, neg_re, neg_re, ofReal_re, hre, sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_re,
      ofReal_im]
    ring
  · rw [sub_im, neg_im, neg_im, ofReal_im, him, sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
      ofReal_im]
    ring

/-- Helper: the image of a closed set under a continuous map with linear growth is closed. -/
theorem s12_isClosed_image {f : ℂ → ℂ} {S : Set ℂ} (hS : IsClosed S) (hf : ContinuousOn f S)
    {A B : ℝ} (hA : 0 ≤ A) (hb : ∀ w ∈ S, ‖w‖ ≤ A * ‖f w‖ + B) : IsClosed (f '' S) := by
  refine isClosed_of_closure_subset fun ζ hζ => ?_
  set R : ℝ := A * (‖ζ‖ + 1) + B with hR
  have hK : IsCompact (S ∩ closedBall 0 R) := (isCompact_closedBall 0 R).inter_left hS
  have hKc : IsClosed (f '' (S ∩ closedBall 0 R)) :=
    (hK.image_of_continuousOn (hf.mono inter_subset_left)).isClosed
  have hmem : ζ ∈ f '' (S ∩ closedBall 0 R) := by
    refine hKc.closure_subset (Metric.mem_closure_iff.mpr fun ε hε => ?_)
    obtain ⟨b, hb', hdist⟩ := Metric.mem_closure_iff.mp hζ (min ε 1) (lt_min hε one_pos)
    obtain ⟨w, hw, rfl⟩ := hb'
    refine ⟨f w, ⟨w, ⟨hw, ?_⟩, rfl⟩, lt_of_lt_of_le hdist (min_le_left _ _)⟩
    rw [mem_closedBall, dist_zero_right]
    have h2 : dist ζ (f w) < 1 := lt_of_lt_of_le hdist (min_le_right _ _)
    rw [dist_eq_norm] at h2
    have h3 := norm_sub_norm_le (f w) ζ
    rw [norm_sub_rev] at h3
    have := mul_le_mul_of_nonneg_left (show ‖f w‖ ≤ ‖ζ‖ + 1 by linarith) hA
    linarith [hb w hw]
  exact image_mono inter_subset_left hmem

/-- Helper: a connected set meeting `g(ℍ_r)` and avoiding `g(iℝ)` lies in `g(ℍ_r)`. -/
theorem s12_cusp_sub_image {S : Set ℂ} (hS : IsPreconnected S)
    (hne : (S ∩ cuspMap '' rightHalf).Nonempty) (hav : ∀ y : ℝ, cuspMap ((y : ℂ) * I) ∉ S) :
    S ⊆ cuspMap '' rightHalf := by
  have hBo : IsOpen rightHalf := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ cuspMap rightHalf := s12_cusp_conformal.1
  have hΩo : IsOpen (cuspMap '' rightHalf) := by
    rcases (hd.analyticOnNhd hBo).is_constant_or_isOpen
      (convex_halfSpace_re_gt 0).isPreconnected with ⟨c, hc⟩ | h
    · exfalso
      have h1 : cuspMap 1 = cuspMap 2 := by
        rw [hc 1 (show (0 : ℝ) < (1 : ℂ).re by simp), hc 2 (show (0 : ℝ) < (2 : ℂ).re by simp)]
      have := s12_cusp_injOn (show (0 : ℝ) ≤ (1 : ℂ).re by simp)
        (show (0 : ℝ) ≤ (2 : ℂ).re by simp) h1
      norm_num at this
    · exact h rightHalf subset_rfl hBo
  have hcl : ∀ ζ ∈ closure (cuspMap '' rightHalf),
      ζ ∈ cuspMap '' rightHalf ∨ ∃ y : ℝ, cuspMap ((y : ℂ) * I) = ζ := by
    intro ζ hζ
    set R : ℝ := ‖ζ‖ + 6 with hR
    have hK : IsCompact ({w : ℂ | 0 ≤ w.re} ∩ closedBall 0 R) :=
      (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const Complex.continuous_re)
    have hgc : ContinuousOn cuspMap ({w : ℂ | 0 ≤ w.re} ∩ closedBall 0 R) := fun w hw => by
      have : (0 : ℝ) ≤ w.re := hw.1
      exact (s12_cusp_hasDerivAt (by linarith)).continuousAt.continuousWithinAt
    have hKc : IsClosed (cuspMap '' ({w : ℂ | 0 ≤ w.re} ∩ closedBall 0 R)) :=
      (hK.image_of_continuousOn hgc).isClosed
    have hmem : ζ ∈ cuspMap '' ({w : ℂ | 0 ≤ w.re} ∩ closedBall 0 R) := by
      refine hKc.closure_subset (Metric.mem_closure_iff.mpr fun ε hε => ?_)
      obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp hζ (min ε 1) (lt_min hε one_pos)
      obtain ⟨w, hw, rfl⟩ := hb
      have hw0 : (0 : ℝ) < w.re := hw
      refine ⟨cuspMap w, ⟨w, ⟨hw0.le, ?_⟩, rfl⟩, lt_of_lt_of_le hdist (min_le_left _ _)⟩
      rw [mem_closedBall, dist_zero_right]
      by_contra hgt
      rw [not_le] at hgt
      have h1 := s12_cusp_norm_ge hw0.le
      have h2 : dist ζ (cuspMap w) < 1 := lt_of_lt_of_le hdist (min_le_right _ _)
      rw [dist_eq_norm] at h2
      have h3 := norm_sub_norm_le (cuspMap w) ζ
      rw [norm_sub_rev] at h3
      have h4 : 5 * ‖w‖ ≤ ‖w‖ ^ 2 - ‖w‖ := by
        nlinarith [mul_nonneg (norm_nonneg w) (by linarith [norm_nonneg ζ] : 0 ≤ ‖w‖ - 6)]
      have h5 := Real.pi_le_four
      nlinarith [norm_nonneg ζ]
    obtain ⟨w, ⟨hw0, _⟩, rfl⟩ := hmem
    rcases (show (0 : ℝ) ≤ w.re from hw0).lt_or_eq with hlt | heq
    · exact Or.inl ⟨w, hlt, rfl⟩
    · refine Or.inr ⟨w.im, congrArg cuspMap (Complex.ext (by simp [← heq]) (by simp))⟩
  have hsplit : S ⊆ cuspMap '' rightHalf ∪ (closure (cuspMap '' rightHalf))ᶜ := by
    intro ζ hζ
    by_cases hc : ζ ∈ closure (cuspMap '' rightHalf)
    · rcases hcl ζ hc with h | ⟨y, rfl⟩
      · exact Or.inl h
      · exact absurd hζ (hav y)
    · exact Or.inr hc
  exact IsPreconnected.subset_left_of_subset_union hΩo isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left subset_closure) hsplit hne hS

/-- Helper: `(g(ℍ_r), Ω*)` is a Jordan pair with curve `g(iℝ)`; `F = g` on `ℍ_r` and
`F(u + iy) = g(iy) - u` on `Re ≤ 0`. -/
theorem s12_cusp_jordan : ∃ Ωs : Set ℂ, IsJordanPair (cuspMap '' rightHalf) Ωs ∧
    curveOf (cuspMap '' rightHalf) Ωs = cuspMap '' {w | w.re = 0} := by
  have hπ := Real.pi_pos
  have hca : ∀ y : ℝ, ContinuousAt cuspMap ((y : ℂ) * I) := fun y =>
    (s12_cusp_hasDerivAt (by simp)).continuousAt
  have hgc : ContinuousOn cuspMap {w : ℂ | 0 ≤ w.re} := fun w hw =>
    (s12_cusp_hasDerivAt (by have : (0 : ℝ) ≤ w.re := hw; linarith)).continuousAt.continuousWithinAt
  have hax_re : ∀ y : ℝ, (cuspMap ((y : ℂ) * I)).re = y ^ 2 - Real.log (1 + y ^ 2) / 2 :=
    fun y => by
      rw [s12_cusp_axis]
      simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
      ring
  have hax_im : ∀ y : ℝ, (cuspMap ((y : ℂ) * I)).im = -Real.arctan y := fun y => by
    rw [s12_cusp_axis]
    simp only [sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re]
    ring
  have hax_ge : ∀ y : ℝ, y ^ 2 / 2 ≤ (cuspMap ((y : ℂ) * I)).re := fun y => by
    rw [hax_re]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + y ^ 2 by positivity)
    linarith
  -- the parametrisation `P(u + iy) = g(iy) - u` of the region right of `g(iℝ)`
  set P : ℂ → ℂ := fun w => cuspMap ((w.im : ℂ) * I) - (w.re : ℂ) with hPdef
  have hPc : Continuous P := by
    refine continuous_iff_continuousAt.mpr fun w => ?_
    refine ContinuousAt.sub ?_ (by fun_prop)
    exact ContinuousAt.comp (g := cuspMap) (hca w.im) (by fun_prop)
  have hPre : ∀ w, (P w).re = (cuspMap ((w.im : ℂ) * I)).re - w.re := fun w => by simp [hPdef]
  have hPim : ∀ w, (P w).im = -Real.arctan w.im := fun w => by simp [hPdef, hax_im]
  have hPg : ∀ w : ℂ, w.re = 0 → P w = cuspMap w := fun w hw => by
    have e : w = (w.im : ℂ) * I := Complex.ext (by simp [hw]) (by simp)
    simp only [hPdef, hw, ofReal_zero, sub_zero]
    rw [← e]
  have hPb : ∀ w : ℂ, w.re ≤ 0 → ‖w‖ ≤ ‖P w‖ + 1 / 2 := fun w hw => by
    have h1 := norm_le_abs_re_add_abs_im w
    have h2 := re_le_norm (P w)
    rw [hPre] at h2
    have h3 := hax_ge w.im
    have h4 : |w.im| ≤ w.im ^ 2 / 2 + 1 / 2 := by
      nlinarith [sq_nonneg (|w.im| - 1), sq_abs w.im]
    rw [abs_of_nonpos hw] at h1
    linarith
  have hPinj : Function.Injective P := by
    intro a b hab
    have him : a.im = b.im := by
      have := congrArg Complex.im hab
      rw [hPim, hPim, neg_inj] at this
      exact Real.arctan_strictMono.injective this
    have hre := congrArg Complex.re hab
    rw [hPre, hPre, him] at hre
    exact Complex.ext (by linarith) him
  set h : ℂ → ℝ := fun ζ => (cuspMap (((-Real.tan ζ.im : ℝ) : ℂ) * I)).re with hhdef
  have hh0 : ∀ ζ, 0 ≤ h ζ := fun ζ => (div_nonneg (sq_nonneg _) two_pos.le).trans (hax_ge _)
  have hPstrip : ∀ w, |(P w).im| < π / 2 := fun w => by
    rw [hPim, abs_neg, abs_lt]
    exact ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hhP : ∀ w, h (P w) = (P w).re + w.re := fun w => by
    simp only [hhdef, hPim, Real.tan_neg, neg_neg, Real.tan_arctan]
    rw [hPre]
    ring
  have hPsurj : ∀ ζ : ℂ, |ζ.im| < π / 2 → P ⟨h ζ - ζ.re, -Real.tan ζ.im⟩ = ζ := by
    intro ζ hζ
    rw [abs_lt] at hζ
    apply Complex.ext
    · rw [hPre]
      simp [hhdef]
    · rw [hPim]
      show -Real.arctan (-Real.tan ζ.im) = ζ.im
      rw [Real.arctan_neg, neg_neg, Real.arctan_tan hζ.1 hζ.2]
  -- `D` = the closed region right of `g(iℝ)`, `R` its interior
  set D : Set ℂ := {ζ | |ζ.im| < π / 2 ∧ h ζ ≤ ζ.re} with hDdef
  set R : Set ℂ := {ζ | |ζ.im| < π / 2 ∧ h ζ < ζ.re} with hRdef
  have hPD : ∀ w, P w ∈ D ↔ w.re ≤ 0 := fun w => by
    simp only [hDdef, mem_ofPred_eq, hhP]
    constructor
    · rintro ⟨_, h1⟩
      linarith
    · intro h1
      exact ⟨hPstrip w, by linarith⟩
  have hDP : ∀ ζ ∈ D, ∃ w : ℂ, w.re ≤ 0 ∧ P w = ζ := fun ζ hζ =>
    ⟨_, show h ζ - ζ.re ≤ 0 by linarith [hζ.2], hPsurj ζ hζ.1⟩
  have hD_re : ∀ ζ ∈ D, 0 ≤ ζ.re := fun ζ hζ => (hh0 ζ).trans hζ.2
  have hΓD : ∀ y : ℝ, cuspMap ((y : ℂ) * I) ∈ D := fun y => by
    rw [← hPg _ (by simp)]
    exact (hPD _).mpr (by simp)
  have hDeq : D = P '' {w | w.re ≤ 0} := by
    ext ζ
    constructor
    · intro hζ
      obtain ⟨w, hw, rfl⟩ := hDP ζ hζ
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact (hPD w).mpr hw
  have hDc : IsClosed D := by
    rw [hDeq]
    refine s12_isClosed_image (isClosed_le Complex.continuous_re continuous_const)
      hPc.continuousOn (A := 2) (B := 1) (by norm_num) fun w hw => ?_
    have := hPb w hw
    linarith [norm_nonneg (P w)]
  have hRo : IsOpen R := by
    have hSo : IsOpen {ζ : ℂ | |ζ.im| < π / 2} :=
      isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    have hhc : ContinuousOn (fun ζ : ℂ => (h ζ, ζ.re)) {ζ : ℂ | |ζ.im| < π / 2} := by
      intro ζ hζ
      have hζ' := abs_lt.mp (show |ζ.im| < π / 2 from hζ)
      have htan : ContinuousAt (fun ζ : ℂ => Real.tan ζ.im) ζ :=
        (Real.continuousOn_tan_Ioo.continuousAt (Ioo_mem_nhds hζ'.1 hζ'.2)).comp
          Complex.continuous_im.continuousAt
      have hin : ContinuousAt (fun ζ : ℂ => (((-Real.tan ζ.im : ℝ)) : ℂ) * I) ζ :=
        (Complex.continuous_ofReal.continuousAt.comp htan.neg).mul continuousAt_const
      have hhζ : ContinuousAt h ζ :=
        Complex.continuous_re.continuousAt.comp
          (ContinuousAt.comp (g := cuspMap) (hca _) hin)
      exact (hhζ.prodMk Complex.continuous_re.continuousAt).continuousWithinAt
    have := hhc.isOpen_inter_preimage hSo (isOpen_lt continuous_fst continuous_snd)
    exact this
  have hRD : R ⊆ D := fun ζ hζ => ⟨hζ.1, hζ.2.le⟩
  have hg1 : (cuspMap 1).re < 0 := by
    have : (cuspMap 1).re = -1 - Real.log 2 := by
      unfold cuspMap
      rw [sub_re, Complex.log_re]
      norm_num
    rw [this]
    linarith [Real.log_pos one_lt_two]
  have h1D : cuspMap 1 ∉ D := fun hm => absurd (hD_re _ hm) (not_le.mpr hg1)
  have h1R : (1 : ℂ) ∈ rightHalf := show (0 : ℝ) < (1 : ℂ).re by simp
  -- `g(ℍ_r) ⊆ Dᶜ`
  have hsub : cuspMap '' rightHalf ⊆ Dᶜ ∪ R := by
    rintro _ ⟨w, hw, rfl⟩
    by_cases hm : cuspMap w ∈ D
    · right
      refine ⟨hm.1, lt_of_le_of_ne hm.2 fun heq => ?_⟩
      obtain ⟨v, -, hPv⟩ := hDP _ hm
      have hv0 : v.re = 0 := by
        have := hhP v
        rw [hPv, ← heq] at this
        linarith
      have e : cuspMap w = cuspMap ((v.im : ℂ) * I) := by
        rw [← hPv]
        simp [hPdef, hv0]
      have := s12_cusp_injOn (show 0 ≤ w.re from (hw : 0 < w.re).le)
        (show 0 ≤ ((v.im : ℂ) * I).re by simp) e
      have h2 := congrArg Complex.re this
      have h3 : 0 < w.re := hw
      simp at h2
      linarith
    · exact Or.inl hm
  have hgconn : IsPreconnected (cuspMap '' rightHalf) :=
    (convex_halfSpace_re_gt 0).isPreconnected.image _
      (hgc.mono fun w hw => (show 0 < w.re from hw).le)
  have hgD : cuspMap '' rightHalf ⊆ Dᶜ :=
    IsPreconnected.subset_left_of_subset_union hDc.isOpen_compl hRo
      (disjoint_compl_left.mono_right hRD) hsub ⟨cuspMap 1, ⟨1, h1R, rfl⟩, h1D⟩ hgconn
  -- `Dᶜ ⊆ g(ℍ_r)`
  have hDcconn : IsPreconnected Dᶜ := by
    refine isPreconnected_of_forall (-1) fun ζ hζ => ?_
    set T₂ : Set ℂ := {p | p.im ≤ ζ.im} ∩ {p | ζ.im ≤ p.im} ∩ {p | p.re ≤ ζ.re} with hT₂
    have hneg : {p : ℂ | p.re < 0} ⊆ Dᶜ := fun p hp hpD =>
      absurd (hD_re p hpD) (not_le.mpr hp)
    have hT₂D : T₂ ⊆ Dᶜ := by
      rintro p ⟨⟨h1, h2⟩, h3⟩ hpD
      have h3' : p.re ≤ ζ.re := h3
      have hpi : p.im = ζ.im := le_antisymm h1 h2
      apply hζ
      have e : h p = h ζ := by simp only [hhdef, hpi]
      refine ⟨by rw [← hpi]; exact hpD.1, ?_⟩
      have := hpD.2
      rw [e] at this
      linarith
    refine ⟨{p : ℂ | p.re < 0} ∪ T₂, union_subset hneg hT₂D,
      Or.inl (show (-1 : ℂ).re < 0 by norm_num),
      Or.inr ⟨⟨show ζ.im ≤ ζ.im from le_rfl, show ζ.im ≤ ζ.im from le_rfl⟩,
        show ζ.re ≤ ζ.re from le_rfl⟩, ?_⟩
    refine IsPreconnected.union ⟨min ζ.re (-1), ζ.im⟩
      (show min ζ.re (-1) < 0 from min_lt_of_right_lt (by norm_num))
      ⟨⟨show ζ.im ≤ ζ.im from le_rfl, show ζ.im ≤ ζ.im from le_rfl⟩,
        show min ζ.re (-1) ≤ ζ.re from min_le_left _ _⟩ (convex_halfSpace_re_lt 0).isPreconnected ?_
    exact (((convex_halfSpace_im_le _).inter (convex_halfSpace_im_ge _)).inter
      (convex_halfSpace_re_le _)).isPreconnected
  have hDg : Dᶜ ⊆ cuspMap '' rightHalf :=
    s12_cusp_sub_image hDcconn ⟨cuspMap 1, h1D, 1, h1R, rfl⟩ fun y hy => hy (hΓD y)
  -- the global homeomorphism
  set F₀ : ℂ → ℂ := fun w => if w.re ≤ 0 then P w else cuspMap w with hF₀
  have hF₀c : Continuous F₀ :=
    continuous_if_le Complex.continuous_re continuous_const hPc.continuousOn hgc hPg
  have hF₀b : ∀ w, ‖w‖ ≤ 2 * ‖F₀ w‖ + 13 := by
    intro w
    by_cases hw : w.re ≤ 0
    · have e : F₀ w = P w := by simp only [hF₀, hw, ↓reduceIte]
      rw [e]
      have := hPb w hw
      linarith [norm_nonneg (P w)]
    · have e : F₀ w = cuspMap w := by simp only [hF₀, hw, ↓reduceIte]
      rw [e]
      have h1 := s12_cusp_norm_ge (show 0 ≤ w.re by linarith [not_le.mp hw])
      have := Real.pi_le_four
      nlinarith [norm_nonneg w]
  have key : ∀ a b : ℂ, a.re ≤ 0 → ¬ b.re ≤ 0 → P a ≠ cuspMap b := fun a b ha hb heq =>
    hgD ⟨b, show 0 < b.re from not_le.mp hb, rfl⟩ (heq ▸ (hPD a).mpr ha)
  have hF₀inj : Function.Injective F₀ := by
    intro a b hab
    by_cases ha : a.re ≤ 0 <;> by_cases hb : b.re ≤ 0
    · simp only [hF₀, ha, hb, ↓reduceIte] at hab
      exact hPinj hab
    · simp only [hF₀, ha, hb, ↓reduceIte] at hab
      exact absurd hab (key a b ha hb)
    · simp only [hF₀, ha, hb, ↓reduceIte] at hab
      exact absurd hab.symm (key b a hb ha)
    · simp only [hF₀, ha, hb, ↓reduceIte] at hab
      exact s12_cusp_injOn (show 0 ≤ a.re by linarith [not_le.mp ha])
        (show 0 ≤ b.re by linarith [not_le.mp hb]) hab
  have hF₀surj : Function.Surjective F₀ := by
    intro ζ
    by_cases hζ : ζ ∈ D
    · obtain ⟨w, hw, rfl⟩ := hDP ζ hζ
      exact ⟨w, by simp only [hF₀, hw, ↓reduceIte]⟩
    · obtain ⟨w, hw, rfl⟩ := hDg hζ
      have hw' : ¬ w.re ≤ 0 := not_le.mpr hw
      exact ⟨w, by simp only [hF₀, hw', ↓reduceIte]⟩
  have hF₀cl : IsClosedMap F₀ := fun S hS =>
    s12_isClosed_image hS hF₀c.continuousOn (by norm_num : (0 : ℝ) ≤ 2) fun w _ => hF₀b w
  set H : ℂ ≃ₜ ℂ := (Equiv.ofBijective F₀ ⟨hF₀inj, hF₀surj⟩).toHomeomorphOfContinuousClosed
    hF₀c hF₀cl with hHdef
  have hcoe : (H : ℂ → ℂ) = F₀ := rfl
  have hHR : H '' rightHalf = cuspMap '' rightHalf := by
    rw [hcoe]
    exact image_congr fun w hw => by
      have : ¬ w.re ≤ 0 := not_le.mpr hw
      simp only [hF₀, this, ↓reduceIte]
  -- the rotation `z ↦ -iz : ℍ → ℍ_r`
  set M : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (-I) (by simp) with hMdef
  have hMc : (M : ℂ → ℂ) = fun z => -I * z := rfl
  have hII : ∀ w : ℂ, -I * (I * w) = w := fun w => by
    rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
  have hMu : M '' upperHalf = rightHalf := by
    ext w
    rw [hMc]
    constructor
    · rintro ⟨z, hz, rfl⟩
      show 0 < (-I * z).re
      have hz' : 0 < z.im := hz
      simpa using hz'
    · intro hw
      have hw' : 0 < w.re := hw
      have hIw : 0 < (I * w).im := by simpa using hw'
      exact ⟨I * w, hIw, hII w⟩
  have hMl : M '' lowerHalf = {w : ℂ | w.re < 0} := by
    ext w
    rw [hMc]
    constructor
    · rintro ⟨z, hz, rfl⟩
      show (-I * z).re < 0
      have hz' : z.im < 0 := hz
      simpa using hz'
    · intro hw
      exact ⟨I * w, show (I * w).im < 0 by simpa using hw, hII w⟩
  have hFimg : ∀ A : Set ℂ, (M.trans H) '' A = H '' (M '' A) := fun A => by
    rw [image_image]
    rfl
  refine ⟨H '' {w | w.re < 0}, ⟨M.trans H, ?_, ?_⟩, ?_⟩
  · rw [hFimg, hMu, hHR]
  · rw [hFimg, hMl]
  · unfold curveOf
    rw [← hHR, ← image_union, ← image_compl_eq H.bijective]
    have e : (rightHalf ∪ {w : ℂ | w.re < 0})ᶜ = {w : ℂ | w.re = 0} := by
      ext w
      simp only [rightHalf, mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        exact le_antisymm h1 h2
      · intro h
        exact ⟨h.le, h.ge⟩
    rw [e, hcoe]
    exact image_congr fun w hw => by
      have hw' : w.re ≤ 0 := (show w.re = 0 from hw).le
      simp only [hF₀, hw', ↓reduceIte]
      exact hPg w hw

/-- Proposition 12.6(a) `prop:cusp`, `sec12-counter.tex:635`, with (12.?) `eq:cusp-boundary`:
`g` is injective on `{Re w ≥ 0}`, `g(w) → ∞` as `w → ∞`, `Ω = g(ℍ_r)` is a Jordan domain through
`∞` with boundary `g(iℝ)`, an analytic arc (`g' ≠ 0` on `iℝ`), and
`{Re ζ < 0} ∪ {|Im ζ| ≥ π/2} ⊆ Ω`. -/
theorem prop_cusp_a :
    InjOn cuspMap {w | 0 ≤ w.re} ∧
      Tendsto cuspMap (cocompact ℂ ⊓ 𝓟 {w | 0 ≤ w.re}) (cocompact ℂ) ∧
      (∃ Ωs : Set ℂ, IsJordanPair (cuspMap '' rightHalf) Ωs ∧
        curveOf (cuspMap '' rightHalf) Ωs = cuspMap '' {w | w.re = 0}) ∧
      (∀ y : ℝ, AnalyticAt ℂ cuspMap ((y : ℂ) * I) ∧ deriv cuspMap ((y : ℂ) * I) ≠ 0) ∧
      (∀ y : ℝ, cuspMap ((y : ℂ) * I) =
        ((y ^ 2 - Real.log (1 + y ^ 2) / 2 : ℝ) : ℂ) - I * (Real.arctan y : ℂ)) ∧
      {ζ : ℂ | ζ.re < 0} ∪ {ζ : ℂ | π / 2 ≤ |ζ.im|} ⊆ cuspMap '' rightHalf := by
  refine ⟨s12_cusp_injOn, ?_, s12_cusp_jordan, fun y => ?_, s12_cusp_axis,
    s12_cusp_image_contains⟩
  · have hl : Tendsto (fun w : ℂ => (‖w‖ + -13) / 2) (cocompact ℂ ⊓ 𝓟 {w | 0 ≤ w.re}) atTop :=
      (tendsto_atTop_add_const_right _ (-13)
        (tendsto_norm_cocompact_atTop.mono_left inf_le_left)).atTop_div_const (by norm_num)
    have key : Tendsto (fun w => ‖cuspMap w‖) (cocompact ℂ ⊓ 𝓟 {w | 0 ≤ w.re}) atTop := by
      refine tendsto_atTop_mono' _ ?_ hl
      refine eventually_inf_principal.mpr (Eventually.of_forall fun w (hw : 0 ≤ w.re) => ?_)
      have h1 := s12_cusp_norm_ge hw
      have := Real.pi_le_four
      show (‖w‖ + -13) / 2 ≤ ‖cuspMap w‖
      nlinarith [norm_nonneg w]
    have : Tendsto cuspMap (cocompact ℂ ⊓ 𝓟 {w | 0 ≤ w.re}) (comap norm atTop) :=
      tendsto_comap_iff.mpr key
    rwa [comap_norm_atTop, Metric.cobounded_eq_cocompact] at this
  · have hw1 : -1 < ((y : ℂ) * I).re := by simp
    refine ⟨?_, ?_⟩
    · have hUo : IsOpen {v : ℂ | -1 < v.re} := isOpen_lt continuous_const Complex.continuous_re
      exact DifferentiableOn.analyticAt
        (fun v hv => (s12_cusp_hasDerivAt hv).differentiableAt.differentiableWithinAt)
        (hUo.mem_nhds hw1)
    · rw [s12_cusp_deriv hw1]
      intro h
      have := s12_cusp_g1_norm (show 0 ≤ ((y : ℂ) * I).re by simp)
      rw [h, norm_zero] at this
      norm_num at this

/-- Proposition 12.6(b) `prop:cusp`, `sec12-counter.tex:641`: `𝖬 = sup_{Re w ≥ 0} |S g| < ∞`,
`s(g(w)) = (Re w)² |S g(w)| ≤ 𝖬 (Re w)²`, and the collar condition (12.?) `eq:mw-collar` holds. -/
theorem prop_cusp_b :
    ∃ M : ℝ, (∀ w : ℂ, 0 ≤ w.re → ‖schwarzian cuspMap w‖ ≤ M) ∧
      (∀ w ∈ rightHalf, schwarzNorm (cuspMap '' rightHalf) (cuspMap w) =
        w.re ^ 2 * ‖schwarzian cuspMap w‖) ∧
      (∀ w ∈ rightHalf, schwarzNorm (cuspMap '' rightHalf) (cuspMap w) ≤ M * w.re ^ 2) ∧
      Tendsto (fun t : ℝ => ⨆ (z : ℂ) (_ : z ∈ rightHalf) (_ : z.re ≤ t),
        ENNReal.ofReal (2 * schwarzNorm (cuspMap '' rightHalf) (cuspMap z))) (𝓝[>] 0) (𝓝 0) := by
  have hs : ∀ w ∈ rightHalf, schwarzNorm (cuspMap '' rightHalf) (cuspMap w) =
      w.re ^ 2 * ‖schwarzian cuspMap w‖ := fun w hw => s12_schwarzNorm_rhp s12_cusp_conformal hw
  have hle : ∀ w ∈ rightHalf, schwarzNorm (cuspMap '' rightHalf) (cuspMap w) ≤ 224 * w.re ^ 2 := by
    intro w hw
    rw [hs w hw]
    have := s12_cusp_schwarzian_le (le_of_lt hw)
    nlinarith [sq_nonneg w.re]
  refine ⟨224, fun w hw => s12_cusp_schwarzian_le hw, hs, hle, ?_⟩
  have hup : Tendsto (fun t : ℝ => ENNReal.ofReal (2 * (224 * t ^ 2))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => ENNReal.ofReal (2 * (224 * t ^ 2)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    have h := hc.tendsto 0
    rw [show ENNReal.ofReal (2 * (224 * (0 : ℝ) ^ 2)) = 0 by simp] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le)
    fun t => ?_
  refine iSup_le fun z => iSup_le fun hz => iSup_le fun hzt => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := hle z hz
  have hz0 : 0 < z.re := hz
  have h2 : z.re ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hz0.le hzt 2
  nlinarith

/-- Proposition 12.6(c) `prop:cusp`, `sec12-counter.tex:643`: for no `R > 0` is `g` uniformly
continuous on `{w ∈ ℍ_r : |w| > R}`; so condition (A) of [MW, Thm 1.2] fails. -/
theorem prop_cusp_c (R : ℝ) :
    ¬ UniformContinuousOn cuspMap {w | w ∈ rightHalf ∧ R < ‖w‖} := by
  intro hU
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp hU 1 one_pos
  have hc : ∀ t : ℝ, 0 ≤ t → cuspMap t = ((-t ^ 2 - Real.log (1 + t) : ℝ) : ℂ) := by
    intro t ht
    unfold cuspMap
    rw [show (1 : ℂ) + t = ((1 + t : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by linarith)]
    push_cast
    ring
  set x : ℝ := |R| + 1 + 1 / δ with hx
  have hRa := le_abs_self R
  have hδx : 0 < 1 / δ := by positivity
  have hx0 : 0 < x := by positivity
  set y : ℝ := x + δ / 2 with hy
  have hy0 : 0 < y := by positivity
  have hmem : ∀ t : ℝ, 0 < t → R < t → (t : ℂ) ∈ {w | w ∈ rightHalf ∧ R < ‖w‖} := by
    intro t ht hRt
    refine ⟨show 0 < (t : ℂ).re by simpa using ht, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact hRt
  have hd : dist (x : ℂ) (y : ℂ) < δ := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have key := h x (hmem x hx0 (by linarith)) y (hmem y hy0 (by linarith)) hd
  rw [hc x hx0.le, hc y hy0.le, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_lt] at key
  have hlog : Real.log (1 + x) ≤ Real.log (1 + y) := Real.log_le_log (by linarith) (by linarith)
  have h1 : 1 ≤ δ * x := by
    have : δ * (1 / δ) = 1 := by field_simp
    nlinarith [abs_nonneg R]
  nlinarith [key.1]

/-- Helper: `|g(iy)| ≥ y² - |y|`. -/
theorem s12_cusp_axis_norm_ge (y : ℝ) : y ^ 2 - |y| ≤ ‖cuspMap ((y : ℂ) * I)‖ := by
  have hre : (cuspMap ((y : ℂ) * I)).re = y ^ 2 - Real.log ‖1 + (y : ℂ) * I‖ := by
    have hsq : ((y : ℂ) * I) ^ 2 = -((y ^ 2 : ℝ) : ℂ) := by
      rw [mul_pow, I_sq]
      push_cast
      ring
    unfold cuspMap
    rw [hsq, sub_re, neg_re, neg_re, ofReal_re, Complex.log_re]
    ring
  have hn : ‖1 + (y : ℂ) * I‖ ≤ 1 + |y| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one]
  have hpos : 0 < ‖1 + (y : ℂ) * I‖ := by
    refine lt_of_lt_of_le one_pos ((?_ : (1 : ℝ) ≤ (1 + (y : ℂ) * I).re).trans (re_le_norm _))
    simp
  have hlog := Real.log_le_sub_one_of_pos hpos
  have := re_le_norm (cuspMap ((y : ℂ) * I))
  linarith

/-- Helper: `|g(-iy) - g(iy)| ≤ 2π`. -/
theorem s12_cusp_axis_diff_le (y : ℝ) :
    ‖cuspMap (((-y : ℝ) : ℂ) * I) - cuspMap ((y : ℂ) * I)‖ ≤ 2 * π := by
  have e : cuspMap (((-y : ℝ) : ℂ) * I) - cuspMap ((y : ℂ) * I) =
      Complex.log (1 + (y : ℂ) * I) - Complex.log (1 + ((-y : ℝ) : ℂ) * I) := by
    unfold cuspMap
    push_cast
    ring
  have hc : 1 + ((-y : ℝ) : ℂ) * I = conj (1 + (y : ℂ) * I) := by
    rw [map_add, map_one, map_mul, conj_ofReal, conj_I]
    push_cast
    ring
  rw [e]
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  have hr : (Complex.log (1 + (y : ℂ) * I) - Complex.log (1 + ((-y : ℝ) : ℂ) * I)).re = 0 := by
    rw [sub_re, Complex.log_re, Complex.log_re, hc, Complex.norm_conj, sub_self]
  rw [hr, abs_zero, zero_add, sub_im, Complex.log_im, Complex.log_im]
  have h1 := Complex.abs_arg_le_pi (1 + (y : ℂ) * I)
  have h2 := Complex.abs_arg_le_pi (1 + ((-y : ℝ) : ℂ) * I)
  have := abs_sub (arg (1 + (y : ℂ) * I)) (arg (1 + ((-y : ℝ) : ℂ) * I))
  linarith

/-- Proposition 12.6(d) `prop:cusp`, `sec12-counter.tex:645`: `Γ` is not a quasicircle. -/
theorem prop_cusp_d (Ωs : Set ℂ) (K : ℝ) : ¬ IsKQuasiPair (cuspMap '' rightHalf) Ωs K := by
  rintro ⟨F, hF, hs, hΩ, hΩs⟩
  have hh : IsHomeomorphOnto F univ univ := by
    have h := hF.2.2.1
    rwa [hs] at h
  set G := Function.invFunOn F univ with hGdef
  have hGc : Continuous G := continuousOn_univ.mp hh.2.2.2
  have hFG : ∀ z, F (G z) = z := fun z =>
    Function.invFunOn_eq (show ∃ a ∈ univ, F a = z from by
      have hz : z ∈ F '' univ := by rw [hs]; exact mem_univ z
      obtain ⟨a, ha, h⟩ := hz
      exact ⟨a, ha, h⟩)
  have hGF : ∀ x, G (F x) = x := fun x => hh.2.1.leftInvOn_invFunOn (mem_univ x)
  have hΩG : ∀ a, a ∈ cuspMap '' rightHalf ↔ 0 < (G a).im := by
    intro a
    rw [← hΩ]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hGF]
      exact hx
    · intro ha
      exact ⟨G a, ha, hFG a⟩
  have hca : ∀ y : ℝ, ContinuousAt cuspMap ((y : ℂ) * I) := fun y =>
    (s12_cusp_hasDerivAt (by simp)).continuousAt
  -- the imaginary axis is mapped into `F(ℝ)`
  have him : ∀ y : ℝ, (G (cuspMap ((y : ℂ) * I))).im = 0 := by
    intro y
    have hlim : Tendsto (fun ε : ℝ => (G (cuspMap ((ε : ℂ) + (y : ℂ) * I))).im) (𝓝[>] 0)
        (𝓝 (G (cuspMap ((y : ℂ) * I))).im) := by
      have hc : ContinuousAt (fun ε : ℝ => (G (cuspMap ((ε : ℂ) + (y : ℂ) * I))).im) 0 := by
        have h0 : ((0 : ℝ) : ℂ) + (y : ℂ) * I = (y : ℂ) * I := by simp
        refine Complex.continuous_im.continuousAt.comp (hGc.continuousAt.comp ?_)
        refine ContinuousAt.comp (g := cuspMap) ?_ (by fun_prop)
        rw [h0]
        exact hca y
      have := hc.tendsto
      simp only [ofReal_zero, zero_add] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < (G (cuspMap ((ε : ℂ) + (y : ℂ) * I))).im :=
      eventually_nhdsWithin_of_forall fun (ε : ℝ) (hε : ε ∈ Ioi (0 : ℝ)) =>
        (hΩG _).mp ⟨_, show 0 < ((ε : ℂ) + (y : ℂ) * I).re by simpa using mem_Ioi.mp hε, rfl⟩
    have hge : 0 ≤ (G (cuspMap ((y : ℂ) * I))).im := ge_of_tendsto hlim (hev.mono fun ε h => h.le)
    refine le_antisymm (not_lt.mp fun hlt => ?_) hge
    obtain ⟨v, hv, hgv⟩ := (hΩG _).mpr hlt
    have := s12_cusp_injOn (show 0 ≤ v.re from (hv : 0 < v.re).le)
      (show 0 ≤ ((y : ℂ) * I).re by simp) hgv
    have h2 : v.re = ((y : ℂ) * I).re := by rw [this]
    have h3 : (0 : ℝ) < v.re := hv
    simp at h2
    linarith
  set T : ℝ → ℝ := fun y => (G (cuspMap ((y : ℂ) * I))).re with hT
  have hTc : Continuous T := by
    refine Complex.continuous_re.comp (hGc.comp (continuous_iff_continuousAt.mpr fun y => ?_))
    exact ContinuousAt.comp (g := cuspMap) (hca y) (by fun_prop)
  have hGT : ∀ y : ℝ, G (cuspMap ((y : ℂ) * I)) = (T y : ℂ) := fun y =>
    Complex.ext (by simp [hT]) (by simp [him y])
  have hFT : ∀ y : ℝ, F (T y) = cuspMap ((y : ℂ) * I) := fun y => by rw [← hGT, hFG]
  have hTi : Function.Injective T := by
    intro a b hab
    have h1 : cuspMap ((a : ℂ) * I) = cuspMap ((b : ℂ) * I) := by
      rw [← hFT a, ← hFT b, hab]
    have h2 := s12_cusp_injOn (show 0 ≤ ((a : ℂ) * I).re by simp)
      (show 0 ≤ ((b : ℂ) * I).re by simp) h1
    have := congrArg Complex.im h2
    simpa using this
  -- the three points `g(-iy₀), g(0) = 0, g(iy₀)`
  have hlam : 1 ≤ lambdaInv K := td_one_le_lambdaInv hF.2.1
  set y₀ : ℝ := π * lambdaInv K + 2 with hy₀
  have hy0 : 0 < y₀ := by positivity
  have hg0 : cuspMap (((0 : ℝ) : ℂ) * I) = 0 := by simp [cuspMap]
  have hA := s12_cusp_axis_norm_ge y₀
  have hD := s12_cusp_axis_diff_le y₀
  rw [abs_of_pos hy0] at hA
  have hB := norm_nonneg (cuspMap (((-y₀ : ℝ) : ℂ) * I))
  have hlarge : 2 * π * lambdaInv K < y₀ ^ 2 - y₀ := by
    have hπ := Real.pi_pos
    nlinarith [mul_pos hπ (zero_lt_one.trans_le hlam)]
  have hlam0 : 0 ≤ lambdaInv K := zero_le_one.trans hlam
  rcases hTc.strictMono_of_inj hTi with hm | hm
  · have h3 := thm16_1_three_point hF hs (hm (show -y₀ < 0 by linarith)) (hm hy0)
    rw [hFT, hFT, hFT, hg0, sub_zero, zero_sub, norm_neg] at h3
    have := mul_le_mul_of_nonneg_left hD hlam0
    nlinarith
  · have h3 := thm16_1_three_point hF hs (hm hy0) (hm (show -y₀ < 0 by linarith))
    rw [hFT, hFT, hFT, hg0, sub_zero, zero_sub, norm_neg, norm_sub_rev] at h3
    have := mul_le_mul_of_nonneg_left hD hlam0
    nlinarith

/-- Proposition 12.6(e) `prop:cusp`, `sec12-counter.tex:646`: for every `t > 0` there is `y_t > 0`
such that for `y ≥ y_t` and `z = -t + iy` the denominator of (12.?) `eq:mw-extension` does not
vanish and `ĝ(z) = g(t+iy)♮ ∈ Ω`; consequently `ĝ` is not injective on any strip
`{Re z > -τ}`. -/
theorem prop_cusp_e :
    (∀ t : ℝ, 0 < t → ∃ yt : ℝ, 0 < yt ∧ ∀ y : ℝ, yt ≤ y →
      1 - (-t) * TakhtajanTeo.Ch2.preSchwarzian cuspMap ⟨t, y⟩ ≠ 0 ∧
      awPoint (cuspMap '' rightHalf) (cuspMap ⟨t, y⟩) = (mwExt cuspMap ⟨-t, y⟩ : OnePoint ℂ) ∧
      mwExt cuspMap ⟨-t, y⟩ ∈ cuspMap '' rightHalf) ∧
    ∀ τ : ℝ, 0 < τ → ∃ z : ℂ, -τ < z.re ∧ z.re < 0 ∧ ∃ v ∈ rightHalf, mwExt cuspMap z = cuspMap v := by
  refine ⟨fun t ht => s12_cusp_e_key ht, fun τ hτ => ?_⟩
  obtain ⟨yt, _, h⟩ := s12_cusp_e_key (half_pos hτ)
  obtain ⟨_, _, v, hv, hgv⟩ := h yt le_rfl
  exact ⟨⟨-(τ / 2), yt⟩, show -τ < -(τ / 2) by linarith, show -(τ / 2) < 0 by linarith,
    v, hv, hgv.symm⟩

end EpsteinVMO
