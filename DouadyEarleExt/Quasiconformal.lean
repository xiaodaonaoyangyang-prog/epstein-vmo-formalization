/-
# Quasiconformal extensions, and dependence on the Beltrami coefficient
(Sections 5 and 6)

* Wirtinger derivatives and the complex dilatation
                                        — `wirtZ`, `wirtZbar`, `complexDilatation`
* `K`-quasiconformality, and the coefficient `K(φ)`
                                        — `IsKQuasiconformalOn`, `HasQCExtension`, `qcCoeff`
* Theorem 2 (Φ is quasiconformal, Lipschitz in the α/β sense of (5.1))
                                        — `theorem2_lipschitz`
* The Beltrami equation, `f^μ`, `φ^μ`, and `σ : M → M`
                                        — `IsBeltramiCoeff`, `beltramiSolution_existsUnique`,
                                          `sigmaMap`
* Proposition 3 (continuity of `σ`)    — `sigmaMap_uniformlyContinuousOn`
* Lemma 4 and its Corollary (conformal naturality of `σ`)
                                        — `lemma4_conj_iff`, `sigmaMap_naturality`

Proved in full here: the vanishing of the complex dilatation of a holomorphic
map (`wirtZbar_eq_zero`, `isKQuasiconformalOn_one_of_holomorphic`), the
elementary properties of `K(φ)` (`isKQuasiconformalOn_mono`, `one_le_qcCoeff`,
`qcCoeff_le`), the Wirtinger chain rules and the transformation law (6.5) for
the complex dilatation (`complexDilatation_comp_left`,
`complexDilatation_comp_right`), and the direction `⇐` of Lemma 4 under
explicit regularity hypotheses (`dilatation_transform_of_conj`,
`actsOn_of_conj`).

The `α`/`β` of (5.1) were first transcribed with `‖dΦ(1)‖ ∓ ‖dΦ(i)‖` in place
of `|Φ_z| ∓ |Φ_z̄|`, which made Theorem 2 **false** — see
`theorem2_lipschitz_naive_false`, whose counterexample is `φ = id`.  The
definitions have been corrected and Theorem 2 is now proved from its `α` half,
the `β` half being derived from quasiconformality.  Conversely
`theorem2_quasiconformal` recovers quasiconformality of `Φ` from (5.1) by pure
algebra: the dilatation is bounded by `(b-a)/(b+a)`, the ratio of the two
constants.

Formula (6.2), `E(φ^μ) = f^{σ(μ)}`, is proved from the uniqueness half of the
measurable Riemann mapping theorem, the work being to check that `E(φ^μ)` is a
normalized Beltrami solution for `σ(μ)`.

`σ` lands in `M` again (`sigmaMap_isBeltramiCoeff`): measurability is free, and
the bound is one application of `theorem2_quasiconformal` to `φ^μ`, whose
quasiconformal extension is `f^μ` itself (`hasQCExtension_beltramiBoundary`).

`beltramiSolution_existsUnique` (Ahlfors–Bers), which the paper cites, is proved
here with no `sorry`, in `DouadyEarleExt.AhlforsBers`, from the measurable
Riemann mapping theorem for the plane in the companion development
`lizhong_quasiconformal_teichmuller`.  Its statement had to be **corrected
twice** first.

*The uniqueness clause as first written was false*, since `IsBeltramiSolution`
builds in no regularity and the Beltrami equation is vacuous wherever the
differential degenerates (`beltramiSolution_existsUnique_false_of_degenerate`).
Uniqueness was then restricted to competitors with `f_z ≠ 0` throughout `D`.

*That repair was itself false.*  A nonvanishing `f_z` at every point of `D` is
differentiability at every point, and for a general measurable `μ` no solution
is differentiable everywhere — Ahlfors–Bers produces a Sobolev homeomorphism,
differentiable a.e.  The radial cube `c(z) = z²z̄` makes this concrete: it is
the solution for its own dilatation, it is smooth, and `c_z(0) = 0`, so for
`μ(c)` there is no everywhere nondegenerate solution at all
(`no_nondegenerate_solution_cubeMap`).  The Beltrami equation and the
nondegeneracy are therefore now stated **almost everywhere**, and uniqueness is
asserted against competitors that are differentiable throughout `D`.
-/
import Mathlib
import DouadyEarle.Extension
import DouadyEarleExt.AhlforsBers

open MeasureTheory Real Set Complex

noncomputable section

/-! ## Wirtinger derivatives and quasiconformality -/

/-- The Wirtinger derivative `∂F/∂z`. -/
def wirtZ (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ F z 1 - Complex.I * fderiv ℝ F z Complex.I) / 2

/-- The Wirtinger derivative `∂F/∂z̄`. -/
def wirtZbar (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ F z 1 + Complex.I * fderiv ℝ F z Complex.I) / 2

/-- The complex dilatation `μ(F) = F_z̄ / F_z`. -/
def complexDilatation (F : ℂ → ℂ) (z : ℂ) : ℂ := wirtZbar F z / wirtZ F z

/-- `F` is `K`-quasiconformal on `s`: `‖μ(F)‖ ≤ (K-1)/(K+1)` throughout `s`. -/
def IsKQuasiconformalOn (F : ℂ → ℂ) (s : Set ℂ) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ z ∈ s, ‖complexDilatation F z‖ ≤ (K - 1) / (K + 1)

/-- `φ : S¹ → S¹` admits a `K`-quasiconformal extension to `D̄`. -/
def HasQCExtension (φ : Circle → Circle) (K : ℝ) : Prop :=
  ∃ F : ℂ → ℂ, ContinuousOn F (Metric.closedBall (0:ℂ) 1) ∧
    Set.BijOn F (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1) ∧
    IsKQuasiconformalOn F (Metric.ball (0:ℂ) 1) K ∧
    ∀ ζ : Circle, F (ζ : ℂ) = (φ ζ : ℂ)

/-- The coefficient of quasiconformality `K(φ)` of formula (9.3). -/
def qcCoeff (φ : Circle → Circle) : ℝ := sInf {K : ℝ | 1 ≤ K ∧ HasQCExtension φ K}

/-! ### Conformal maps have vanishing complex dilatation

Section 6 opens by recalling that the complex dilatation `μ(f) = f_z̄/f_z` is
the basic invariant of a quasiconformal map.  The two facts below are the
baseline of that theory: a holomorphic map has `f_z = f'` and `f_z̄ = 0`, so it
has vanishing dilatation and is `1`-quasiconformal.  In particular every
element of the group `G₊` of Section 1 is `1`-quasiconformal. -/

/-- The real derivative of a `ℂ`-differentiable map is `ℂ`-linear:
`dF(i) = i · dF(1)`. -/
theorem fderiv_real_I_of_differentiableAt (F : ℂ → ℂ) (z : ℂ) (h : DifferentiableAt ℂ F z) :
    (fderiv ℝ F z) Complex.I = Complex.I * (fderiv ℝ F z) 1 := by
  rw [h.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [show (Complex.I : ℂ) = Complex.I • (1:ℂ) by simp, map_smul]
  simp

/-- For a holomorphic map, `F_z` is the complex derivative. -/
theorem wirtZ_eq_deriv (F : ℂ → ℂ) (z : ℂ) (h : DifferentiableAt ℂ F z) :
    wirtZ F z = deriv F z := by
  rw [wirtZ, fderiv_real_I_of_differentiableAt F z h, h.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', fderiv_apply_one_eq_deriv]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

/-- **Cauchy–Riemann**: a holomorphic map satisfies `F_z̄ = 0`. -/
theorem wirtZbar_eq_zero (F : ℂ → ℂ) (z : ℂ) (h : DifferentiableAt ℂ F z) :
    wirtZbar F z = 0 := by
  rw [wirtZbar, fderiv_real_I_of_differentiableAt F z h, ← mul_assoc, Complex.I_mul_I]
  ring

/-- A holomorphic map has vanishing complex dilatation. -/
theorem complexDilatation_eq_zero (F : ℂ → ℂ) (z : ℂ) (h : DifferentiableAt ℂ F z) :
    complexDilatation F z = 0 := by
  rw [complexDilatation, wirtZbar_eq_zero F z h, zero_div]

/-- A map holomorphic on `s` is `1`-quasiconformal on `s`. -/
theorem isKQuasiconformalOn_one_of_holomorphic (F : ℂ → ℂ) (s : Set ℂ)
    (h : ∀ z ∈ s, DifferentiableAt ℂ F z) : IsKQuasiconformalOn F s 1 := by
  refine ⟨le_refl 1, fun z hz => ?_⟩
  rw [complexDilatation_eq_zero F z (h z hz)]
  norm_num

/-! ### The Wirtinger chain rules

The proof of Lemma 4 rests on how the complex dilatation transforms under
pre- and postcomposition with a conformal map.  Writing an `ℝ`-linear map
`L : ℂ → ℂ` as `L w = p·w + q·w̄` (`clm_apply_eq_wirt`), the chain rule gives
`(F ∘ g)_z = F_z(g)·g'` and `(F ∘ g)_z̄ = F_z̄(g)·conj g'` for `g` holomorphic,
and `(h ∘ F)_z = h'(F)·F_z`, `(h ∘ F)_z̄ = h'(F)·F_z̄` for `h` holomorphic. -/

theorem fderiv_real_apply_of_holomorphic (h : ℂ → ℂ) (w u : ℂ) (hh : DifferentiableAt ℂ h w) :
    (fderiv ℝ h w) u = deriv h w * u := by
  have hmap := (fderiv ℂ h w).map_smul u (1:ℂ)
  simp only [smul_eq_mul, mul_one] at hmap
  rw [hh.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [hmap, fderiv_apply_one_eq_deriv, mul_comm]

theorem wirtZ_comp_right (F g : ℂ → ℂ) (z : ℂ) (hg : DifferentiableAt ℂ g z)
    (hF : DifferentiableAt ℝ F (g z)) :
    wirtZ (F ∘ g) z = wirtZ F (g z) * deriv g z := by
  have hgR : DifferentiableAt ℝ g z := hg.restrictScalars ℝ
  rw [wirtZ, fderiv_comp z hF hgR]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [fderiv_real_apply_of_holomorphic g z 1 hg, fderiv_real_apply_of_holomorphic g z Complex.I hg,
    clm_apply_eq_wirt (fderiv ℝ F (g z)) (deriv g z * 1),
    clm_apply_eq_wirt (fderiv ℝ F (g z)) (deriv g z * Complex.I)]
  simp only [wirtZ, star_mul, Complex.star_def, Complex.conj_I, mul_one]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem wirtZbar_comp_right (F g : ℂ → ℂ) (z : ℂ) (hg : DifferentiableAt ℂ g z)
    (hF : DifferentiableAt ℝ F (g z)) :
    wirtZbar (F ∘ g) z = wirtZbar F (g z) * star (deriv g z) := by
  have hgR : DifferentiableAt ℝ g z := hg.restrictScalars ℝ
  rw [wirtZbar, fderiv_comp z hF hgR]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [fderiv_real_apply_of_holomorphic g z 1 hg, fderiv_real_apply_of_holomorphic g z Complex.I hg,
    clm_apply_eq_wirt (fderiv ℝ F (g z)) (deriv g z * 1),
    clm_apply_eq_wirt (fderiv ℝ F (g z)) (deriv g z * Complex.I)]
  simp only [wirtZbar, star_mul, Complex.star_def, Complex.conj_I, mul_one]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem wirtZ_comp_left (h F : ℂ → ℂ) (z : ℂ) (hF : DifferentiableAt ℝ F z)
    (hh : DifferentiableAt ℂ h (F z)) :
    wirtZ (h ∘ F) z = deriv h (F z) * wirtZ F z := by
  have hhR : DifferentiableAt ℝ h (F z) := hh.restrictScalars ℝ
  rw [wirtZ, fderiv_comp z hhR hF]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [fderiv_real_apply_of_holomorphic h (F z) _ hh, fderiv_real_apply_of_holomorphic h (F z) _ hh,
    wirtZ]
  ring

theorem wirtZbar_comp_left (h F : ℂ → ℂ) (z : ℂ) (hF : DifferentiableAt ℝ F z)
    (hh : DifferentiableAt ℂ h (F z)) :
    wirtZbar (h ∘ F) z = deriv h (F z) * wirtZbar F z := by
  have hhR : DifferentiableAt ℝ h (F z) := hh.restrictScalars ℝ
  rw [wirtZbar, fderiv_comp z hhR hF]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [fderiv_real_apply_of_holomorphic h (F z) _ hh, fderiv_real_apply_of_holomorphic h (F z) _ hh,
    wirtZbar]
  ring

/-- Postcomposition with a conformal map leaves the complex dilatation
unchanged; precomposition twists it by `conj g'/g'`.  This pair of identities
is formula (6.5). -/
theorem complexDilatation_comp_right (F g : ℂ → ℂ) (z : ℂ) (hg : DifferentiableAt ℂ g z)
    (hF : DifferentiableAt ℝ F (g z)) :
    complexDilatation (F ∘ g) z
      = complexDilatation F (g z) * (star (deriv g z) / deriv g z) := by
  rw [complexDilatation, wirtZ_comp_right F g z hg hF, wirtZbar_comp_right F g z hg hF,
    complexDilatation, div_mul_div_comm]

theorem complexDilatation_comp_left (h F : ℂ → ℂ) (z : ℂ) (hF : DifferentiableAt ℝ F z)
    (hh : DifferentiableAt ℂ h (F z)) (hd : deriv h (F z) ≠ 0) :
    complexDilatation (h ∘ F) z = complexDilatation F z := by
  rw [complexDilatation, wirtZ_comp_left h F z hF hh, wirtZbar_comp_left h F z hF hh,
    mul_div_mul_left _ _ hd, complexDilatation]

/-! ### Conjugating the values, and the orientation of a conjugacy

`complexDilatation_comp_left` says a holomorphic postcomposition leaves the
dilatation alone.  Its mirror image — postcomposing with `star` — is what
decides the *orientation* question left open in Lemma 4, and it is elementary:
conjugation swaps the two Wirtinger derivatives and conjugates them. -/

theorem fderiv_star_comp_apply {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z) (v : ℂ) :
    (fderiv ℝ (fun w => star (F w)) z) v = star ((fderiv ℝ F z) v) := by
  rw [(hF.hasFDerivAt.star).fderiv]
  simp

theorem differentiableAt_star_comp {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z) :
    DifferentiableAt ℝ (fun w => star (F w)) z :=
  hF.hasFDerivAt.star.differentiableAt

/-- The mirror of `wirtZ_comp_left`. -/
theorem wirtZ_star_comp (F : ℂ → ℂ) (z : ℂ) (hF : DifferentiableAt ℝ F z) :
    wirtZ (fun w => star (F w)) z = star (wirtZbar F z) := by
  rw [wirtZ, wirtZbar, fderiv_star_comp_apply hF, fderiv_star_comp_apply hF]
  rw [star_div₀, star_add, star_mul]
  simp only [Complex.star_def, Complex.conj_I, map_ofNat]
  ring

theorem wirtZbar_star_comp (F : ℂ → ℂ) (z : ℂ) (hF : DifferentiableAt ℝ F z) :
    wirtZbar (fun w => star (F w)) z = star (wirtZ F z) := by
  rw [wirtZbar, wirtZ, fderiv_star_comp_apply hF, fderiv_star_comp_apply hF]
  rw [star_div₀, star_sub, star_mul]
  simp only [Complex.star_def, Complex.conj_I, map_ofNat]
  ring

theorem wirtZ_eq_of_eventuallyEq {A B : ℂ → ℂ} {z : ℂ} (heq : A =ᶠ[nhds z] B) :
    wirtZ A z = wirtZ B z := by
  unfold wirtZ; rw [heq.fderiv_eq]

theorem wirtZbar_eq_of_eventuallyEq {A B : ℂ → ℂ} {z : ℂ} (heq : A =ᶠ[nhds z] B) :
    wirtZbar A z = wirtZbar B z := by
  unfold wirtZbar; rw [heq.fderiv_eq]

/-- **The orientation gap, closed.**  An orientation-reversing element of `G`
cannot conjugate one map of dilatation `< 1` into another.

Suppose `Fν ∘ g = h ∘ Fμ` with `h(w) = H(w̄)`, `H ∈ G₊`.  Conjugation swaps the
two Wirtinger derivatives, so the two chain rules read
`|Fν_z||g'| = |H'||Fμ_z̄|` and `|Fν_z̄||g'| = |H'||Fμ_z|`.  The first quantity is
then strictly below `|H'||Fμ_z|`, which the second says equals `|Fν_z̄||g'|`,
which is strictly below `|Fν_z||g'|` — the first quantity again.

This is what `lemma4_conj_iff` used to list as a missing input, described there
as needing "the dilatation of an antiholomorphic postcomposition, the mirror
image of `complexDilatation_comp_left`".  That mirror is `wirtZ_star_comp`. -/
theorem isDiskAutPlus_of_conj (g h Fμ Fν : ℂ → ℂ)
    (hg : IsDiskAutPlus g) (hh : IsDiskAut h)
    (hFμd : DifferentiableAt ℝ Fμ 0) (hFνd : DifferentiableAt ℝ Fν (g 0))
    (hFμ0 : ‖Fμ 0‖ < 1)
    (hμnd : ‖wirtZbar Fμ 0‖ < ‖wirtZ Fμ 0‖)
    (hνnd : ‖wirtZbar Fν (g 0)‖ < ‖wirtZ Fν (g 0)‖)
    (hconj : ∀ z : ℂ, ‖z‖ ≤ 1 → Fν (g z) = h (Fμ z)) :
    IsDiskAutPlus h := by
  rcases hh with hp | hm
  · exact hp
  exfalso
  set H : ℂ → ℂ := fun z => h (star z) with hHdef
  have hhz : ∀ z : ℂ, h z = H (star z) := by
    intro z; rw [hHdef]; simp
  have hz0 : ‖(0:ℂ)‖ < 1 := by norm_num
  have hgd : DifferentiableAt ℂ g 0 := isDiskAutPlus_differentiableAt g hg 0 hz0
  have hg' : deriv g 0 ≠ 0 := deriv_isDiskAutPlus_ne_zero g hg (le_of_lt hz0)
  have hsF : ‖star (Fμ 0)‖ < 1 := by rwa [norm_star]
  have hHd : DifferentiableAt ℂ H (star (Fμ 0)) :=
    isDiskAutPlus_differentiableAt H hm _ hsF
  have hH' : deriv H (star (Fμ 0)) ≠ 0 := deriv_isDiskAutPlus_ne_zero H hm hsF.le
  have hsFd : DifferentiableAt ℝ (fun w => star (Fμ w)) 0 := differentiableAt_star_comp hFμd
  have heq : (Fν ∘ g) =ᶠ[nhds (0:ℂ)] (H ∘ (fun w => star (Fμ w))) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz0)] with w hw
    show Fν (g w) = H (star (Fμ w))
    rw [← hhz (Fμ w)]
    exact hconj w (le_of_lt (mem_ball_zero_iff.1 hw))
  have hwZ := wirtZ_eq_of_eventuallyEq heq
  have hwZb := wirtZbar_eq_of_eventuallyEq heq
  rw [wirtZ_comp_right Fν g 0 hgd hFνd,
    wirtZ_comp_left H (fun w => star (Fμ w)) 0 hsFd (by simpa using hHd),
    wirtZ_star_comp Fμ 0 hFμd] at hwZ
  rw [wirtZbar_comp_right Fν g 0 hgd hFνd,
    wirtZbar_comp_left H (fun w => star (Fμ w)) 0 hsFd (by simpa using hHd),
    wirtZbar_star_comp Fμ 0 hFμd] at hwZb
  have e1 : ‖wirtZ Fν (g 0)‖ * ‖deriv g 0‖
      = ‖deriv H (star (Fμ 0))‖ * ‖wirtZbar Fμ 0‖ := by
    have h := congrArg norm hwZ
    simpa [norm_mul, norm_star] using h
  have e2 : ‖wirtZbar Fν (g 0)‖ * ‖deriv g 0‖
      = ‖deriv H (star (Fμ 0))‖ * ‖wirtZ Fμ 0‖ := by
    have h := congrArg norm hwZb
    simpa [norm_mul, norm_star] using h
  have hgpos : 0 < ‖deriv g 0‖ := norm_pos_iff.2 hg'
  have hHpos : 0 < ‖deriv H (star (Fμ 0))‖ := norm_pos_iff.2 hH'
  nlinarith [hμnd, hνnd, hgpos, hHpos, e1, e2]

/-! ### `K(φ)` is a genuine infimum

The bound `(K-1)/(K+1)` on the dilatation increases with `K`, so
`K`-quasiconformality is monotone in `K`; hence the set of admissible `K` in
formula (9.3) is an interval bounded below by `1`, and `K(φ)` lies between `1`
and every admissible `K`. -/

theorem isKQuasiconformalOn_mono (F : ℂ → ℂ) (s : Set ℂ) (K K' : ℝ) (hKK' : K ≤ K')
    (h : IsKQuasiconformalOn F s K) : IsKQuasiconformalOn F s K' := by
  obtain ⟨hK, hbd⟩ := h
  refine ⟨hK.trans hKK', fun z hz => (hbd z hz).trans ?_⟩
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem one_le_qcCoeff (φ : Circle → Circle) (K : ℝ) (hK : 1 ≤ K) (h : HasQCExtension φ K) :
    1 ≤ qcCoeff φ := by
  refine le_csInf ⟨K, hK, h⟩ ?_
  rintro b ⟨hb, -⟩
  exact hb

theorem qcCoeff_le (φ : Circle → Circle) (K : ℝ) (hK : 1 ≤ K) (h : HasQCExtension φ K) :
    qcCoeff φ ≤ K :=
  csInf_le ⟨1, fun _ hb => hb.1⟩ ⟨hK, h⟩

/-- The complex dilatation of any map is measurable: `fderiv` is. -/
theorem measurable_complexDilatation (F : ℂ → ℂ) : Measurable (complexDilatation F) := by
  have h1 : Measurable fun z : ℂ => (fderiv ℝ F z) 1 :=
    measurable_fderiv_apply_const (𝕜 := ℝ) (f := F) 1
  have h2 : Measurable fun z : ℂ => (fderiv ℝ F z) Complex.I :=
    measurable_fderiv_apply_const (𝕜 := ℝ) (f := F) Complex.I
  unfold complexDilatation wirtZ wirtZbar
  exact ((h1.add (measurable_const.mul h2)).div measurable_const).div
    ((h1.sub (measurable_const.mul h2)).div measurable_const)

/-- `∂id/∂z = 1`. -/
theorem wirtZ_id (z : ℂ) : wirtZ id z = 1 := by
  have h : fderiv ℝ (id : ℂ → ℂ) z = ContinuousLinearMap.id ℝ ℂ := fderiv_id
  rw [wirtZ, h]
  simp only [ContinuousLinearMap.coe_id', id_eq]
  rw [Complex.I_mul_I]
  ring

/-- A map admitting a quasiconformal extension is continuous: the extension is
continuous on `D̄`, and `S¹ ⊆ D̄`. -/
theorem continuous_of_hasQCExtension (φ : Circle → Circle) (K : ℝ) (h : HasQCExtension φ K) :
    Continuous φ := by
  obtain ⟨F, hFc, -, -, hbdry⟩ := h
  have hmaps : ∀ ζ : Circle, ((ζ : ℂ)) ∈ Metric.closedBall (0:ℂ) 1 := by
    intro ζ; simp
  have hcomp : Continuous fun ζ : Circle => F ((ζ : ℂ)) :=
    hFc.comp_continuous continuous_subtype_val hmaps
  have heq : (fun ζ : Circle => F ((ζ : ℂ))) = fun ζ : Circle => ((φ ζ : Circle) : ℂ) := by
    funext ζ; exact hbdry ζ
  rw [heq] at hcomp
  exact continuous_induced_rng.2 hcomp

/-! ## Theorem 2 -/

/-- `id` has the identity as a `1`-quasiconformal extension. -/
theorem hasQCExtension_id : HasQCExtension (id : Circle → Circle) 1 :=
  ⟨id, continuousOn_id, Set.bijOn_id _,
    isKQuasiconformalOn_one_of_holomorphic id _ (fun _ _ => differentiable_id.differentiableAt),
    fun _ => rfl⟩

/-! ### The naive reading of (5.1) is false

`α` and `β` measure the least and greatest stretch of `dΦ` in the Poincaré
metric.  For an `ℝ`-linear `L w = p w + q w̄` those are `|p| - |q|` and
`|p| + |q|`, *not* `‖L 1‖ ∓ ‖L i‖`: since `L 1 = p + q` and `L i = i(p - q)`,
the latter pair is `|p+q| ∓ |p-q|`, a different quantity.

The distinction is not academic, and it is the same one recorded in the
docstring of `extension_jacobian_ne_zero`: for holomorphic `F` the two norms
`‖dF(1)‖` and `‖dF(i)‖` always agree (`norm_fderiv_one_eq_norm_fderiv_I`), so
the naive `α` vanishes identically wherever `Φ` is conformal.  It vanishes in
particular for `φ = id`, where `Φ = id` — and `id` has a `1`-quasiconformal
extension, so no positive lower bound `a` can exist.  Note this needs no
hypothesis at all beyond `extension_id`: the counterexample is the identity. -/
theorem theorem2_lipschitz_naive_false :
    ¬ (∀ K : ℝ, 1 ≤ K → ∃ a : ℝ, 0 < a ∧
        ∀ φ : Circle → Circle, Function.Bijective φ → HasQCExtension φ K →
          ∀ z : ℂ, ‖z‖ < 1 →
            a ≤ ((‖(fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) 1‖ -
                ‖(fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) Complex.I‖) /
              (1 - ‖extension φ z‖ ^ 2)) * (1 - ‖z‖ ^ 2)) := by
  intro h
  obtain ⟨a, ha, hall⟩ := h 1 le_rfl
  have hz : ‖(0:ℂ)‖ < 1 := by simp
  have hkey := hall id Function.bijective_id hasQCExtension_id 0 hz
  rw [fderiv_extension_id hz] at hkey
  simp at hkey
  linarith

/-- The functions `α(φ)`, `β(φ)` of Section 5, measuring the distortion of
`Φ = E(φ)` of the Poincaré metric relative to that of `D`: the least and
greatest stretch of `dΦ`, which are `|Φ_z| - |Φ_z̄|` and `|Φ_z| + |Φ_z̄|`.

Phrased with the Wirtinger derivatives for the reason recorded above and in
`extension_jacobian_ne_zero`; see `theorem2_lipschitz_naive_false`. -/
def alphaFn (φ : Circle → Circle) (z : ℂ) : ℝ :=
  ((‖wirtZ (extension φ) z‖ - ‖wirtZbar (extension φ) z‖) / (1 - ‖extension φ z‖ ^ 2)) *
    (1 - ‖z‖ ^ 2)

def betaFn (φ : Circle → Circle) (z : ℂ) : ℝ :=
  ((‖wirtZ (extension φ) z‖ + ‖wirtZbar (extension φ) z‖) / (1 - ‖extension φ z‖ ^ 2)) *
    (1 - ‖z‖ ^ 2)

theorem wirtZ_extension_id {z : ℂ} (hz : ‖z‖ < 1) : wirtZ (extension id) z = 1 := by
  rw [wirtZ, fderiv_extension_id hz]
  simp only [ContinuousLinearMap.coe_id', id_eq]
  rw [Complex.I_mul_I]; ring

theorem wirtZbar_extension_id {z : ℂ} (hz : ‖z‖ < 1) : wirtZbar (extension id) z = 0 := by
  rw [wirtZbar, fderiv_extension_id hz]
  simp only [ContinuousLinearMap.coe_id', id_eq]
  rw [Complex.I_mul_I]; ring

/-- The corrected `α` and `β` both take the value `1` at the identity, as they
must: `E(id) = id` is an isometry of the Poincaré metric.  The naive versions
gave `0` and `2` instead — the first of which is what makes
`theorem2_lipschitz_naive_false` true. -/
theorem alphaFn_id {z : ℂ} (hz : ‖z‖ < 1) : alphaFn id z = 1 := by
  have hne : (1:ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
  rw [alphaFn, wirtZ_extension_id hz, wirtZbar_extension_id hz, extension_id z hz]
  simp only [norm_one, norm_zero, sub_zero]
  field_simp

theorem betaFn_id {z : ℂ} (hz : ‖z‖ < 1) : betaFn id z = 1 := by
  have hne : (1:ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
  rw [betaFn, wirtZ_extension_id hz, wirtZbar_extension_id hz, extension_id z hz]
  simp only [norm_one, norm_zero, add_zero]
  field_simp

/-- `α ≤ β` needs no hypothesis on `φ` beyond `Φ(z) ∈ D`, so the middle
conjunct of (5.1) is free. -/
theorem alphaFn_le_betaFn (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) : alphaFn φ z ≤ betaFn φ z := by
  have hΦ : ‖extension φ z‖ < 1 := extension_mem_disk φ hφ hφc z hz
  have hD : (0:ℝ) < 1 - ‖extension φ z‖ ^ 2 := by nlinarith [norm_nonneg (extension φ z)]
  have hE : (0:ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [alphaFn, betaFn]
  have hq : (0:ℝ) ≤ ‖wirtZbar (extension φ) z‖ := norm_nonneg _
  have hstep : (‖wirtZ (extension φ) z‖ - ‖wirtZbar (extension φ) z‖)
        / (1 - ‖extension φ z‖ ^ 2)
      ≤ (‖wirtZ (extension φ) z‖ + ‖wirtZbar (extension φ) z‖)
        / (1 - ‖extension φ z‖ ^ 2) :=
    (div_le_div_iff_of_pos_right hD).mpr (by linarith)
  exact mul_le_mul_of_nonneg_right hstep hE.le

/-- Quasiconformality of `Φ` bounds `β` by `α`: the ratio `β/α` is exactly the
pointwise dilatation ratio `(1+|μ|)/(1-|μ|)`.

The hypothesis `hjac` — the Jacobian statement of Theorem 1 — cannot be
dropped.  `complexDilatation` is `Φ_z̄ / Φ_z`, so where `Φ_z = 0` Lean's
`x / 0 = 0` makes the dilatation bound hold vacuously while `β ≤ Lα` is false
unless `Φ_z̄` also vanishes. -/
theorem betaFn_le_of_dilatation (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) (k : ℝ) (hk1 : k < 1)
    (hjac : ‖wirtZbar (extension φ) z‖ < ‖wirtZ (extension φ) z‖)
    (hdil : ‖complexDilatation (extension φ) z‖ ≤ k) :
    betaFn φ z ≤ ((1 + k) / (1 - k)) * alphaFn φ z := by
  have hΦ : ‖extension φ z‖ < 1 := extension_mem_disk φ hφ hφc z hz
  have hD : (0:ℝ) < 1 - ‖extension φ z‖ ^ 2 := by nlinarith [norm_nonneg (extension φ z)]
  have hE : (0:ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hp : (0:ℝ) < ‖wirtZ (extension φ) z‖ := lt_of_le_of_lt (norm_nonneg _) hjac
  have hqp : ‖wirtZbar (extension φ) z‖ ≤ k * ‖wirtZ (extension φ) z‖ := by
    rw [complexDilatation, norm_div, div_le_iff₀ hp] at hdil
    linarith
  have hnum : ‖wirtZ (extension φ) z‖ + ‖wirtZbar (extension φ) z‖
      ≤ ((1 + k) / (1 - k)) * (‖wirtZ (extension φ) z‖ - ‖wirtZbar (extension φ) z‖) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith
  rw [alphaFn, betaFn]
  have hstep : (‖wirtZ (extension φ) z‖ + ‖wirtZbar (extension φ) z‖)
        / (1 - ‖extension φ z‖ ^ 2)
      ≤ ((1 + k) / (1 - k)) *
        ((‖wirtZ (extension φ) z‖ - ‖wirtZbar (extension φ) z‖)
          / (1 - ‖extension φ z‖ ^ 2)) := by
    rw [mul_div_assoc'] at *
    exact (div_le_div_iff_of_pos_right hD).mpr hnum
  calc (‖wirtZ (extension φ) z‖ + ‖wirtZbar (extension φ) z‖) / (1 - ‖extension φ z‖ ^ 2) *
        (1 - ‖z‖ ^ 2)
      ≤ ((1 + k) / (1 - k)) *
        ((‖wirtZ (extension φ) z‖ - ‖wirtZbar (extension φ) z‖)
          / (1 - ‖extension φ z‖ ^ 2)) * (1 - ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hstep hE.le
    _ = ((1 + k) / (1 - k)) *
        ((‖wirtZ (extension φ) z‖ - ‖wirtZbar (extension φ) z‖)
          / (1 - ‖extension φ z‖ ^ 2) * (1 - ‖z‖ ^ 2)) := by ring

/-- **Theorem 2**: if `φ` has a `K`-quasiconformal extension, then `Φ = E(φ)`
and `Φ⁻¹` are Lipschitz continuous in the Poincaré metric on `D` — equivalently
(inequality (5.1)) `α(φ)` and `β(φ)` are bounded between two positive
constants depending only on `K`.

Only the `α` half is taken as input.  `halpha` is Douady–Earle's Section 5
estimate: the least Poincaré stretch of `Φ` stays in a fixed compact subinterval
of `(0, ∞)` depending only on `K`.  That is the substance of Theorem 2 and it is
not proved here.

The `β` half is *derived*, and that derivation is the point: `α ≤ β` is free
(`alphaFn_le_betaFn`), and `β ≤ ((1+k)/(1-k))·α` because `Φ` is quasiconformal
(`betaFn_le_of_dilatation`), so a bound on `α` above propagates to `β`.  The two
remaining inputs are the statements of Theorem 1 (`hjac`, the nonvanishing
Jacobian) and of `theorem2_quasiconformal` (`hqc`, that `Φ` has dilatation
bounded away from `1` by a constant depending only on `K`).

`_hK` is kept for fidelity to the paper's statement but is redundant here:
`HasQCExtension` carries `1 ≤ K` inside `IsKQuasiconformalOn`. -/
theorem theorem2_lipschitz (K : ℝ) (_hK : 1 ≤ K)
    (hjac : ∀ φ : Circle → Circle, Function.Bijective φ → HasQCExtension φ K →
      ∀ z : ℂ, ‖z‖ < 1 → ‖wirtZbar (extension φ) z‖ < ‖wirtZ (extension φ) z‖)
    (hqc : ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      ∀ φ : Circle → Circle, Function.Bijective φ → HasQCExtension φ K →
        ∀ z : ℂ, ‖z‖ < 1 → ‖complexDilatation (extension φ) z‖ ≤ k)
    (halpha : ∃ a₀ c₀ : ℝ, 0 < a₀ ∧
      ∀ φ : Circle → Circle, Function.Bijective φ → HasQCExtension φ K →
        ∀ z : ℂ, ‖z‖ < 1 → a₀ ≤ alphaFn φ z ∧ alphaFn φ z ≤ c₀) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ φ : Circle → Circle, Function.Bijective φ → HasQCExtension φ K →
        ∀ z : ℂ, ‖z‖ < 1 → a ≤ alphaFn φ z ∧ alphaFn φ z ≤ betaFn φ z ∧ betaFn φ z ≤ b := by
  obtain ⟨k, hk0, hk1, hk⟩ := hqc
  obtain ⟨a₀, c₀, ha₀, hab⟩ := halpha
  have hL : (0:ℝ) ≤ (1 + k) / (1 - k) := by positivity
  refine ⟨a₀, max a₀ (((1 + k) / (1 - k)) * c₀), ha₀, le_max_left _ _, ?_⟩
  intro φ hφ hKφ z hz
  have hφc : Continuous φ := continuous_of_hasQCExtension φ K hKφ
  obtain ⟨hlo, hhi⟩ := hab φ hφ hKφ z hz
  refine ⟨hlo, alphaFn_le_betaFn φ hφ hφc z hz, ?_⟩
  have hb := betaFn_le_of_dilatation φ hφ hφc z hz k hk1 (hjac φ hφ hKφ z hz)
    (hk φ hφ hKφ z hz)
  exact hb.trans ((mul_le_mul_of_nonneg_left hhi hL).trans (le_max_right _ _))

/-- **Theorem 2**, second half: "in particular `Φ` is quasiconformal".

This is the genuine consequence of (5.1), and it is pure algebra.  Write
`P = |Φ_z|`, `Q = |Φ_z̄|`, and `C = (1-|z|²)/(1-|Φ(z)|²) > 0`, so that
`α = (P-Q)C` and `β = (P+Q)C`.  Then:

* `a ≤ α` with `a > 0` forces `P > Q`, hence `Φ_z ≠ 0` — so the dilatation is
  a genuine quotient here and not Lean's `x/0 = 0`;
* multiplying `a ≤ (P-Q)C` by `P+Q` and `(P+Q)C ≤ b` by `P-Q` and chaining
  gives `a(P+Q) ≤ b(P-Q)`, i.e. `Q/P ≤ (b-a)/(b+a)`;
* and `(b-a)/(b+a)` is exactly `(K'-1)/(K'+1)` for `K' = b/a`.

So `K' = b/a` works, and the ratio of the two constants in (5.1) *is* the
bound on the dilatation.

`h51` is stated as the literal conclusion of `theorem2_lipschitz`, so the two
compose.  Note the two theorems run in opposite directions and neither is
circular: `theorem2_lipschitz` derives the `β` half of (5.1) from
quasiconformality plus two-sided control of `α`, while this one recovers
quasiconformality from the `β` half.  Given control of `α` the two are
interchangeable — which is why Douady–Earle can present (5.1) and
quasiconformality of `Φ` as the same statement. -/
theorem theorem2_quasiconformal (φ : Circle → Circle) (hφ : Function.Bijective φ) (K : ℝ)
    (hK : HasQCExtension φ K)
    (h51 : ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ ψ : Circle → Circle, Function.Bijective ψ → HasQCExtension ψ K →
        ∀ z : ℂ, ‖z‖ < 1 → a ≤ alphaFn ψ z ∧ alphaFn ψ z ≤ betaFn ψ z ∧ betaFn ψ z ≤ b) :
    ∃ K' : ℝ, IsKQuasiconformalOn (extension φ) (Metric.ball (0:ℂ) 1) K' := by
  obtain ⟨a, b, ha, hab, h⟩ := h51
  refine ⟨b / a, (one_le_div ha).2 hab, fun z hz => ?_⟩
  have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  obtain ⟨hlo, -, hhi⟩ := h φ hφ hK z hz1
  have hΦ : ‖extension φ z‖ < 1 :=
    extension_mem_disk φ hφ (continuous_of_hasQCExtension φ K hK) z hz1
  have hD : (0:ℝ) < 1 - ‖extension φ z‖ ^ 2 := by nlinarith [norm_nonneg (extension φ z)]
  have hE : (0:ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [alphaFn, div_mul_eq_mul_div, le_div_iff₀ hD] at hlo
  rw [betaFn, div_mul_eq_mul_div, div_le_iff₀ hD] at hhi
  set P := ‖wirtZ (extension φ) z‖ with hP
  set Q := ‖wirtZbar (extension φ) z‖ with hQ
  have hQ0 : (0:ℝ) ≤ Q := norm_nonneg _
  have hPQ : Q < P := by nlinarith
  have hP0 : (0:ℝ) < P := lt_of_le_of_lt hQ0 hPQ
  have hkey : a * (P + Q) ≤ b * (P - Q) := by nlinarith
  have hdil : ‖complexDilatation (extension φ) z‖ = Q / P := by
    rw [complexDilatation, norm_div]
  rw [hdil]
  have hba : (0:ℝ) < b + a := by linarith
  have hrw : (b / a - 1) / (b / a + 1) = (b - a) / (b + a) := by field_simp
  rw [hrw, div_le_div_iff₀ hP0 hba]
  nlinarith

/-! ## Section 6: dependence on `μ` -/

/-- A point of `M`, the open unit ball of `L^∞(D, ℂ)`: a bounded measurable
Beltrami coefficient with `‖μ‖_∞ < 1`. -/
def IsBeltramiCoeff (μ : ℂ → ℂ) : Prop :=
  Measurable μ ∧ ∃ k : ℝ, k < 1 ∧ ∀ z : ℂ, ‖z‖ < 1 → ‖μ z‖ ≤ k

/-- `f` is a normalized solution of the Beltrami equation for `μ`: a
homeomorphism of `D̄` fixing `1, i, -1` with `f_z̄ = μ f_z` in `D`. -/
def IsBeltramiSolution (μ f : ℂ → ℂ) : Prop :=
  ContinuousOn f (Metric.closedBall (0:ℂ) 1) ∧
    Set.BijOn f (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1) ∧
    f 1 = 1 ∧ f Complex.I = Complex.I ∧ f (-1) = -1 ∧
    (∀ z : ℂ, ‖z‖ < 1 → wirtZbar f z = μ z * wirtZ f z) ∧
    ∀ ζ : Circle, ‖f (ζ : ℂ)‖ = 1

/-- The same, with the Beltrami equation only **almost everywhere**.

This is the class the measurable Riemann mapping theorem actually produces, and
the everywhere version above is *not* available: for a general measurable `μ`
the solution is a Sobolev homeomorphism, differentiable a.e. but not
everywhere.  `Cube.cubeMap` is the concrete witness — see
`no_nondegenerate_solution_cubeMap`. -/
def IsBeltramiSolutionAE (μ f : ℂ → ℂ) : Prop :=
  ContinuousOn f (Metric.closedBall (0:ℂ) 1) ∧
    Set.BijOn f (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1) ∧
    f 1 = 1 ∧ f Complex.I = Complex.I ∧ f (-1) = -1 ∧
    (∀ᵐ z : ℂ, ‖z‖ < 1 → wirtZbar f z = μ z * wirtZ f z) ∧
    ∀ ζ : Circle, ‖f (ζ : ℂ)‖ = 1

theorem IsBeltramiSolution.ae {μ f : ℂ → ℂ} (h : IsBeltramiSolution μ f) :
    IsBeltramiSolutionAE μ f :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    Filter.Eventually.of_forall h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Uniqueness of the solution can only be asserted on `D̄`: every condition in
`IsBeltramiSolution` constrains `f` on the closed disk alone, so a solution can
always be altered off `D̄`.  Hence the `∃!` form of the Riemann mapping theorem
below would be false — this is why `beltramiSolution_existsUnique` states
uniqueness as `Set.EqOn ... (closedBall 0 1)`. -/
theorem beltramiSolution_not_unique (μ : ℂ → ℂ) (h : ∃ f : ℂ → ℂ, IsBeltramiSolution μ f) :
    ¬ ∃! f : ℂ → ℂ, IsBeltramiSolution μ f := by
  obtain ⟨f, hf⟩ := h
  rintro ⟨u, -, huniq⟩
  set g : ℂ → ℂ := fun z => if ‖z‖ ≤ 1 then f z else f z + 1 with hg
  have hagree : Set.EqOn g f (Metric.closedBall (0:ℂ) 1) := by
    intro z hz
    simp only [hg]
    rw [ite_eq_left (by simpa using hz)]
  have hnhds : ∀ z : ℂ, ‖z‖ < 1 → g =ᶠ[nhds z] f := by
    intro z hz
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
    exact hagree (Metric.ball_subset_closedBall hw)
  have hgsol : IsBeltramiSolution μ g := by
    obtain ⟨hc, hb, h1, hI, hn, hbel, hbd⟩ := hf
    refine ⟨hc.congr hagree, hb.congr hagree.symm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hagree (by simp)]; exact h1
    · rw [hagree (by simp)]; exact hI
    · rw [hagree (by simp)]; exact hn
    · intro z hz
      unfold wirtZbar wirtZ
      rw [(hnhds z hz).fderiv_eq]
      exact hbel z hz
    · intro ζ
      rw [hagree (by simp)]; exact hbd ζ
  have h2 : g 2 ≠ f 2 := by
    simp only [hg]
    rw [ite_eq_right (by norm_num)]
    simp
  exact h2 (by rw [huniq g hgsol, huniq f hf])

/-! ### `IsBeltramiSolution` carries no regularity, and the uniqueness clause
needs some

The Beltrami condition is stated with the `fderiv`-based Wirtinger derivatives.
Wherever `f` fails to be differentiable Lean's `fderiv` is `0`, so both
`f_z` and `f_z̄` are `0` and the equation reads `0 = μ·0` — it holds for *every*
`μ`.  The same happens wherever `f` is differentiable with vanishing
differential.  So `IsBeltramiSolution μ f` constrains `f` only on the set where
its differential is nonzero, and says nothing at all elsewhere.

This is exactly the gap that the classical hypothesis closes: Ahlfors–Bers
requires `f ∈ W^{1,2}_loc` (equivalently, absolute continuity on lines), which
rules out solutions whose differential degenerates on a large set.  Sobolev
regularity is not available here, so the uniqueness clause below is restricted
to competitors that are *differentiable throughout* `D` — a class in which
uniqueness does hold (by Gehring's metric characterisation of
quasiconformality, everywhere differentiability plus a dilatation bound gives
`W^{1,2}_loc`), and a class the maps this development applies uniqueness to
belong to, being real-analytic on `D` (`wirtZ_extension_ne_zero`,
`differentiableAt_of_wirtZ_ne_zero`).

Note which side of the statement this restriction lives on.  It is a hypothesis
on the *competitor*, not a claim about `f^μ`: `f^μ` itself is **not**
differentiable everywhere in general, which is what
`no_nondegenerate_solution_cubeMap` shows. -/

theorem wirtZ_eq_zero_of_fderiv_eq_zero {f : ℂ → ℂ} {z : ℂ} (h : fderiv ℝ f z = 0) :
    wirtZ f z = 0 := by
  rw [wirtZ, h]; simp

theorem wirtZbar_eq_zero_of_fderiv_eq_zero {f : ℂ → ℂ} {z : ℂ} (h : fderiv ℝ f z = 0) :
    wirtZbar f z = 0 := by
  rw [wirtZbar, h]; simp

/-- Where the differential vanishes, the Beltrami equation says nothing: it
holds for *every* `μ`. -/
theorem beltramiEq_of_fderiv_eq_zero (μ : ℂ → ℂ) {f : ℂ → ℂ} {z : ℂ}
    (h : fderiv ℝ f z = 0) : wirtZbar f z = μ z * wirtZ f z := by
  rw [wirtZ_eq_zero_of_fderiv_eq_zero h, wirtZbar_eq_zero_of_fderiv_eq_zero h, mul_zero]

theorem beltramiEq_of_not_differentiableAt (μ : ℂ → ℂ) {f : ℂ → ℂ} {z : ℂ}
    (h : ¬ DifferentiableAt ℝ f z) : wirtZbar f z = μ z * wirtZ f z :=
  beltramiEq_of_fderiv_eq_zero μ (fderiv_zero_of_not_differentiableAt h)

/-- The contrapositive is a free source of regularity: a nonvanishing `f_z`
*is* differentiability, since `fderiv` of a non-differentiable map is `0`. -/
theorem differentiableAt_of_wirtZ_ne_zero {f : ℂ → ℂ} {z : ℂ} (h : wirtZ f z ≠ 0) :
    DifferentiableAt ℝ f z := by
  by_contra hcon
  exact h (wirtZ_eq_zero_of_fderiv_eq_zero (fderiv_zero_of_not_differentiableAt hcon))

/-- `HasQCExtension` is blind to degeneracy: a homeomorphism of `D̄` whose
differential vanishes throughout `D` counts as a `1`-quasiconformal extension
of its own boundary map.

The reason is the junk value again.  `complexDilatation` is `F_z̄ / F_z`, so
where the differential vanishes it is `0 / 0 = 0` and *every* dilatation bound
holds vacuously.  Consequently `HasQCExtension φ K` places no lower bound at
all on `F_z`, and the extension it hands over cannot be used where
nondegeneracy is needed — see `teichSet1_subset_teichSpace_one`, which routes
around this by using `E(φ)` instead. -/
theorem hasQCExtension_of_degenerate (φ : Circle → Circle) (F : ℂ → ℂ)
    (hcont : ContinuousOn F (Metric.closedBall (0:ℂ) 1))
    (hbij : Set.BijOn F (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1))
    (hb : ∀ ζ : Circle, F (ζ : ℂ) = (φ ζ : ℂ))
    (hdeg : ∀ z : ℂ, ‖z‖ < 1 → fderiv ℝ F z = 0) :
    HasQCExtension φ 1 := by
  refine ⟨F, hcont, hbij, ⟨le_refl 1, fun z hz => ?_⟩, hb⟩
  have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  rw [complexDilatation, wirtZ_eq_zero_of_fderiv_eq_zero (hdeg z hz1),
    wirtZbar_eq_zero_of_fderiv_eq_zero (hdeg z hz1)]
  norm_num

/-! ### Nondegeneracy forces the open disk into the open disk

The half of "a solution is a homeomorphism of `D̄`" that *is* provable here.
If `F_z` never vanishes then, by the Beltrami equation with `‖μ‖ ≤ k < 1`, also
`|F_z̄| < |F_z|`, so the real differential of `F` is invertible at every interior
point.  Were `‖F z‖ = 1` for some `z ∈ D`, pushing from `z` along the direction
the differential sends to `F z` would take the modulus past `1`, contradicting
`F(D) ⊆ D̄`.  No invariance of domain is used — only a first-order expansion. -/

/-- If `F` maps the open disk into the closed disk and has, at an interior
point `z`, a derivative whose image contains `F z`, then `‖F z‖ < 1`: pushing
along that direction increases the modulus past `1`. -/
theorem norm_lt_one_of_hasFDerivAt {F : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} {z v : ℂ}
    (hz : ‖z‖ < 1) (hmaps : ∀ u : ℂ, ‖u‖ < 1 → ‖F u‖ ≤ 1)
    (hL : HasFDerivAt F L z) (hv : L v = F z) (hFz : F z ≠ 0) : ‖F z‖ < 1 := by
  rcases lt_or_eq_of_le (hmaps z hz) with hlt | heq
  · exact hlt
  exfalso
  have hv0 : v ≠ 0 := by
    intro hcon; rw [hcon, map_zero] at hv; exact hFz hv.symm
  have hvn : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hL
  have hc : (0:ℝ) < 1 / (2 * ‖v‖) := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hL hc)
  set t : ℝ := min (δ / (2 * ‖v‖)) ((1 - ‖z‖) / (2 * ‖v‖)) with ht
  have ht0 : 0 < t := by
    refine lt_min ?_ ?_
    · positivity
    · have : (0:ℝ) < 1 - ‖z‖ := by linarith
      positivity
  have hkey1 : (δ / (2 * ‖v‖)) * ‖v‖ = δ / 2 := by field_simp
  have hkey2 : ((1 - ‖z‖) / (2 * ‖v‖)) * ‖v‖ = (1 - ‖z‖) / 2 := by field_simp
  have htv1 : t * ‖v‖ < δ := by
    have h1 : t * ‖v‖ ≤ (δ / (2 * ‖v‖)) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hvn.le
    rw [hkey1] at h1; linarith
  have htv2 : t * ‖v‖ < 1 - ‖z‖ := by
    have h1 : t * ‖v‖ ≤ ((1 - ‖z‖) / (2 * ‖v‖)) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hvn.le
    rw [hkey2] at h1; linarith
  set u : ℂ := z + (t : ℂ) * v with hu
  have hnu : ‖u - z‖ = t * ‖v‖ := by
    rw [hu, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
  have hudist : dist u z < δ := by rw [dist_eq_norm, hnu]; exact htv1
  have hu1 : ‖u‖ < 1 := by
    calc ‖u‖ ≤ ‖z‖ + ‖(t : ℂ) * v‖ := by rw [hu]; exact norm_add_le _ _
      _ = ‖z‖ + t * ‖v‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      _ < 1 := by linarith
  have herr := hball hudist
  rw [hnu] at herr
  have hE : ‖F u - F z - L (u - z)‖ ≤ t / 2 := by
    refine herr.trans (le_of_eq ?_)
    field_simp
  have hLu : L (u - z) = (t : ℂ) * F z := by
    rw [hu, add_sub_cancel_left,
      show ((t : ℂ) * v) = (t : ℝ) • v by simp [Complex.real_smul], map_smul, hv]
    simp [Complex.real_smul]
  have hsplit : ((1 + (t : ℂ)) * F z) = F u - (F u - F z - L (u - z)) := by
    rw [hLu]; ring
  have hnn : ‖(1 + (t : ℂ)) * F z‖ = (1 + t) * ‖F z‖ := by
    rw [norm_mul]
    congr 1
    rw [show (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hb : ‖(1 + (t : ℂ)) * F z‖ ≤ ‖F u‖ + ‖F u - F z - L (u - z)‖ := by
    rw [hsplit]; exact norm_sub_le _ _
  rw [hnn, heq] at hb
  have hFu := hmaps u hu1
  linarith

theorem exists_fderiv_preimage {F : ℂ → ℂ} {z : ℂ}
    (hlt : ‖wirtZbar F z‖ < ‖wirtZ F z‖) (w : ℂ) :
    ∃ v : ℂ, (fderiv ℝ F z) v = w := by
  set p := wirtZ F z with hp
  set q := wirtZbar F z with hq
  have hD : (0:ℝ) < ‖p‖ ^ 2 - ‖q‖ ^ 2 := by nlinarith [norm_nonneg q, norm_nonneg p]
  have hDne : ((‖p‖ ^ 2 - ‖q‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hD)
  have hpp : p * star p = ((‖p‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hqq : q * star q = ((‖q‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine ⟨(star p * w - q * star w) / ((‖p‖ ^ 2 - ‖q‖ ^ 2 : ℝ) : ℂ), ?_⟩
  have key : (fderiv ℝ F z) ((star p * w - q * star w) / ((‖p‖ ^ 2 - ‖q‖ ^ 2 : ℝ) : ℂ))
      = p * ((star p * w - q * star w) / ((‖p‖ ^ 2 - ‖q‖ ^ 2 : ℝ) : ℂ))
        + q * star ((star p * w - q * star w) / ((‖p‖ ^ 2 - ‖q‖ ^ 2 : ℝ) : ℂ)) :=
    clm_apply_eq_wirt _ _
  rw [key]
  have hs : star ((star p * w - q * star w) / ((‖p‖ ^ 2 - ‖q‖ ^ 2 : ℝ) : ℂ))
      = (p * star w - star q * w) / ((‖p‖ ^ 2 - ‖q‖ ^ 2 : ℝ) : ℂ) := by
    rw [star_div₀, star_sub, star_mul, star_mul, star_star, star_star]
    congr 1
    · ring
    · simp
  rw [hs]
  field_simp
  push_cast [← hpp, ← hqq]
  ring

theorem norm_lt_one_of_beltrami {F μ : ℂ → ℂ} {k : ℝ} (hk : k < 1)
    (hkb : ∀ z : ℂ, ‖z‖ < 1 → ‖μ z‖ ≤ k)
    (hmaps : ∀ u : ℂ, ‖u‖ < 1 → ‖F u‖ ≤ 1)
    (hbel : ∀ z : ℂ, ‖z‖ < 1 → wirtZbar F z = μ z * wirtZ F z)
    (hnd : ∀ z : ℂ, ‖z‖ < 1 → wirtZ F z ≠ 0)
    {z : ℂ} (hz : ‖z‖ < 1) : ‖F z‖ < 1 := by
  rcases eq_or_ne (F z) 0 with h0 | h0
  · rw [h0]; simp
  have hp : 0 < ‖wirtZ F z‖ := norm_pos_iff.mpr (hnd z hz)
  have hlt : ‖wirtZbar F z‖ < ‖wirtZ F z‖ := by
    rw [hbel z hz, norm_mul]
    nlinarith [hkb z hz, norm_nonneg (μ z)]
  have hdiff : DifferentiableAt ℝ F z := by
    by_contra hcon
    exact (hnd z hz) (wirtZ_eq_zero_of_fderiv_eq_zero (fderiv_zero_of_not_differentiableAt hcon))
  obtain ⟨v, hv⟩ := exists_fderiv_preimage hlt (F z)
  exact norm_lt_one_of_hasFDerivAt hz hmaps hdiff.hasFDerivAt hv h0

/-- The phenomenon is not hypothetical.  `f z = z‖z‖` is continuous and
injective on `D̄`, yet `df(0) = 0`, so at `0` its Beltrami coefficient is
completely unconstrained. -/
theorem hasFDerivAt_mul_norm :
    HasFDerivAt (fun z : ℂ => z * (‖z‖ : ℂ)) (0 : ℂ →L[ℝ] ℂ) (0 : ℂ) := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hc] with z hz
  have hzc : ‖z‖ < c := by simpa using hz
  have hrw : (fun z : ℂ => z * (‖z‖ : ℂ)) z - (fun z : ℂ => z * (‖z‖ : ℂ)) 0
      - (0 : ℂ →L[ℝ] ℂ) (z - 0) = z * (‖z‖ : ℂ) := by simp
  rw [hrw]
  have hnorm : ‖z * (‖z‖ : ℂ)‖ = ‖z‖ * ‖z‖ := by simp
  rw [hnorm, sub_zero]
  exact mul_le_mul_of_nonneg_right hzc.le (norm_nonneg z)

theorem fderiv_mul_norm_zero : fderiv ℝ (fun z : ℂ => z * (‖z‖ : ℂ)) 0 = 0 :=
  hasFDerivAt_mul_norm.fderiv

theorem injOn_mul_norm : Set.InjOn (fun z : ℂ => z * (‖z‖ : ℂ)) (Metric.closedBall (0:ℂ) 1) := by
  intro z₁ _ z₂ _ h
  simp only at h
  have hn : ‖z₁‖ * ‖z₁‖ = ‖z₂‖ * ‖z₂‖ := by
    have := congrArg norm h
    simpa using this
  have hz : ‖z₁‖ = ‖z₂‖ := by nlinarith [norm_nonneg z₁, norm_nonneg z₂]
  rcases eq_or_ne ‖z₁‖ 0 with h0 | h0
  · rw [norm_eq_zero] at h0
    have h0' : ‖z₂‖ = 0 := by rw [← hz, h0, norm_zero]
    rw [norm_eq_zero] at h0'
    rw [h0, h0']
  · have hne : ((‖z₁‖ : ℂ)) ≠ 0 := by simpa using h0
    rw [hz] at h
    exact mul_right_cancel₀ (by simpa [← hz] using hne) h

theorem beltramiEq_mul_norm_zero (μ : ℂ → ℂ) :
    wirtZbar (fun z : ℂ => z * (‖z‖ : ℂ)) 0 = μ 0 * wirtZ (fun z : ℂ => z * (‖z‖ : ℂ)) 0 :=
  beltramiEq_of_fderiv_eq_zero μ fderiv_mul_norm_zero

theorem isBeltramiCoeff_zero : IsBeltramiCoeff (fun _ : ℂ => (0:ℂ)) :=
  ⟨measurable_const, 0, by norm_num, fun z _ => by simp⟩

theorem isBeltramiSolution_zero_id : IsBeltramiSolution (fun _ => 0) id := by
  refine ⟨continuousOn_id, Set.bijOn_id _, rfl, rfl, rfl, fun z _ => ?_, fun ζ => by simp⟩
  rw [wirtZbar_eq_zero id z differentiable_id.differentiableAt, zero_mul]

/-- Without a regularity restriction the uniqueness clause is false.  Any
normalized homeomorphism of `D̄` whose differential degenerates throughout `D`
is a "solution" for `μ = 0` alongside the identity, and the two disagree.

Whether such a map exists is precisely the question `W^{1,2}` regularity
settles in the classical theory; this development neither constructs one nor
excludes one, which is the point — the definition as written does nothing to
rule it out.

This theorem is conditional in that sense.  The *unconditional* counterexample
is `no_nondegenerate_solution_cubeMap`, which refutes not this uniqueness clause
but the existence clause of the repair that followed it: for `μ(c)` with
`c(z) = z²z̄` there is no everywhere nondegenerate solution at all. -/
theorem beltramiSolution_existsUnique_false_of_degenerate (f : ℂ → ℂ)
    (hcont : ContinuousOn f (Metric.closedBall (0:ℂ) 1))
    (hbij : Set.BijOn f (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1))
    (h1 : f 1 = 1) (hI : f Complex.I = Complex.I) (hm : f (-1) = -1)
    (hdeg : ∀ z : ℂ, ‖z‖ < 1 → fderiv ℝ f z = 0)
    (hbd : ∀ ζ : Circle, ‖f (ζ : ℂ)‖ = 1)
    (hne : ∃ z ∈ Metric.closedBall (0:ℂ) 1, f z ≠ z) :
    ¬ (∃ g : ℂ → ℂ, IsBeltramiSolution (fun _ => 0) g ∧
        ∀ h : ℂ → ℂ, IsBeltramiSolution (fun _ => 0) h →
          Set.EqOn h g (Metric.closedBall (0:ℂ) 1)) := by
  rintro ⟨g, -, huniq⟩
  obtain ⟨z, hz, hfz⟩ := hne
  have hfsol : IsBeltramiSolution (fun _ => 0) f :=
    ⟨hcont, hbij, h1, hI, hm,
      fun w hw => beltramiEq_of_fderiv_eq_zero (fun _ => 0) (hdeg w hw), hbd⟩
  exact hfz ((huniq f hfsol hz).trans (huniq id isBeltramiSolution_zero_id hz).symm)

/-! ### The nondegeneracy clause was unsatisfiable

The previous repair of the measurable Riemann mapping theorem restricted
uniqueness to competitors with `f_z ≠ 0` at every point of `D`, and asserted
that `f^μ` itself is such a competitor.  The second half of that is false.

A nonvanishing `f_z` at every point *is* differentiability at every point, by
`differentiableAt_of_wirtZ_ne_zero`.  For a general measurable `μ` no solution
of the Beltrami equation is differentiable everywhere — the solution is a
Sobolev homeomorphism, differentiable only almost everywhere — and the failure
is visible in the simplest possible example.

Take the **radial cube** `c(z) = z²z̄ = z|z|²`, a polynomial in `z` and `z̄`.
Radially it is `r ↦ r³`, so it is a homeomorphism of `D̄` onto `D̄` fixing
`1, i, -1` and carrying `S¹` onto `S¹`.  Its Wirtinger derivatives are

    c_z = 2z z̄ = 2|z|²,      c_z̄ = z²,

so its dilatation is `μ(c)(z) = z/(2z̄)`, of modulus `1/2` off the origin and
`0` at it: a perfectly good Beltrami coefficient.  And `c_z(0) = 0`.

`c` is therefore a normalized solution for `μ(c)` which is smooth, satisfies the
Beltrami equation at *every* point of `D`, and is degenerate at exactly one
point.  Since it is smooth it is admitted by the corrected uniqueness clause,
so it *is* the solution — and an everywhere nondegenerate one would have to
agree with it on `D̄`, hence have vanishing derivative at the origin.  That is
`no_nondegenerate_solution_cubeMap`, and it is what forces the equation and the
nondegeneracy in `beltramiSolution_existsUnique` down to "almost everywhere". -/

namespace Cube

/-- `c(z) = z²z̄ = z|z|²`, the radial cube. -/
def cubeMap (z : ℂ) : ℂ := z ^ 2 * star z

theorem cubeMap_eq (z : ℂ) : cubeMap z = ((‖z‖ ^ 2 : ℝ) : ℂ) * z := by
  rw [cubeMap, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp
  ring

theorem norm_cubeMap (z : ℂ) : ‖cubeMap z‖ = ‖z‖ ^ 3 := by
  rw [cubeMap_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  ring

theorem continuous_cubeMap : Continuous cubeMap := by
  unfold cubeMap; fun_prop

/-- The real differential of `c` at `z`: `v ↦ 2|z|² v + z² v̄`. -/
def cubeDeriv (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (2 * z * star z) • (ContinuousLinearMap.id ℝ ℂ)
    + (z ^ 2) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)

theorem hasFDerivAt_cubeMap (z : ℂ) : HasFDerivAt cubeMap (cubeDeriv z) z := by
  have h1 : HasFDerivAt (fun w : ℂ => w ^ 2) ((2 * z) • (ContinuousLinearMap.id ℝ ℂ)) z := by
    have := ((hasDerivAt_pow 2 z).hasFDerivAt).restrictScalars ℝ
    refine this.congr_fderiv ?_
    ext v
    simp [mul_comm]
  have h2 : HasFDerivAt (fun w : ℂ => star w)
      (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) z := by
    refine (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).hasFDerivAt (x := z)).congr_of_eventuallyEq ?_
    filter_upwards with w
    simp
  have h := h1.mul h2
  refine h.congr_fderiv ?_
  ext v
  simp [cubeDeriv]
  ring

theorem differentiable_cubeMap : Differentiable ℝ cubeMap :=
  fun z => (hasFDerivAt_cubeMap z).differentiableAt

theorem wirtZ_cubeMap (z : ℂ) : wirtZ cubeMap z = 2 * z * star z := by
  rw [wirtZ, (hasFDerivAt_cubeMap z).fderiv]
  simp only [cubeDeriv, add_apply, smul_apply,
    ContinuousLinearMap.coe_id', id_eq, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, map_one, Complex.conj_I]
  linear_combination (z ^ 2 / 2 - z * star z) * Complex.I_mul_I

theorem wirtZbar_cubeMap (z : ℂ) : wirtZbar cubeMap z = z ^ 2 := by
  rw [wirtZbar, (hasFDerivAt_cubeMap z).fderiv]
  simp only [cubeDeriv, add_apply, smul_apply,
    ContinuousLinearMap.coe_id', id_eq, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, map_one, Complex.conj_I]
  linear_combination (z * star z - z ^ 2 / 2) * Complex.I_mul_I

/-- **`c` is degenerate exactly at the origin.** -/
theorem wirtZ_cubeMap_zero : wirtZ cubeMap 0 = 0 := by
  rw [wirtZ_cubeMap]; ring

theorem wirtZ_cubeMap_ne_zero {z : ℂ} (hz : z ≠ 0) : wirtZ cubeMap z ≠ 0 := by
  rw [wirtZ_cubeMap]
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨⟨two_ne_zero, hz⟩, star_ne_zero.2 hz⟩

theorem cubeMap_zero : cubeMap 0 = 0 := by simp [cubeMap]

theorem cubeMap_one : cubeMap 1 = 1 := by simp [cubeMap]

theorem cubeMap_I : cubeMap Complex.I = Complex.I := by
  simp [cubeMap, Complex.conj_I]

theorem cubeMap_neg_one : cubeMap (-1) = -1 := by simp [cubeMap]

theorem cubeMap_injOn : Set.InjOn cubeMap (Metric.closedBall (0:ℂ) 1) := by
  intro z _ w _ h
  have hn : ‖z‖ ^ 3 = ‖w‖ ^ 3 := by rw [← norm_cubeMap, ← norm_cubeMap, h]
  have hnz : ‖z‖ = ‖w‖ :=
    le_antisymm (le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg w) (le_of_eq hn))
      (le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg z) (le_of_eq hn.symm))
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [norm_zero] at hnz
    exact (norm_eq_zero.1 hnz.symm).symm
  · rw [cubeMap_eq, cubeMap_eq, ← hnz] at h
    have hne : ((‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    exact mul_left_cancel₀ hne h

theorem cubeMap_mapsTo :
    Set.MapsTo cubeMap (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1) := by
  intro z hz
  have h : ‖z‖ ≤ 1 := by simpa using hz
  have hc : ‖cubeMap z‖ ≤ 1 := by
    rw [norm_cubeMap]
    exact pow_le_one₀ (norm_nonneg z) h
  simpa using hc

theorem cubeMap_surjOn :
    Set.SurjOn cubeMap (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1) := by
  intro w hw
  have hw1 : ‖w‖ ≤ 1 := by simpa using hw
  rcases eq_or_ne w 0 with rfl | hw0
  · exact ⟨0, by simp, cubeMap_zero⟩
  set t : ℝ := ‖w‖ ^ ((1:ℝ)/3) with ht
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have htpos : 0 < t := Real.rpow_pos_of_pos hwpos _
  have ht3 : t ^ 3 = ‖w‖ := by
    rw [ht, ← Real.rpow_natCast (‖w‖ ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul (norm_nonneg w)]
    norm_num
  have ht1 : t ≤ 1 := Real.rpow_le_one (norm_nonneg w) hw1 (by norm_num)
  have hnz : ‖((t / ‖w‖ : ℝ) : ℂ) * w‖ = t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos htpos hwpos), div_mul_cancel₀ _ hwpos.ne']
  refine ⟨((t / ‖w‖ : ℝ) : ℂ) * w, ?_, ?_⟩
  · simp only [Metric.mem_closedBall, dist_zero_right, hnz]
    exact ht1
  · have hval : cubeMap (((t / ‖w‖ : ℝ) : ℂ) * w) = (((t ^ 3 / ‖w‖ : ℝ)) : ℂ) * w := by
      rw [cubeMap_eq, hnz]
      push_cast
      field_simp
    rw [hval, ht3, div_self hwpos.ne']
    simp

theorem cubeMap_bijOn :
    Set.BijOn cubeMap (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1) :=
  ⟨cubeMap_mapsTo, cubeMap_injOn, cubeMap_surjOn⟩

theorem norm_cubeMap_circle (ζ : Circle) : ‖cubeMap (ζ : ℂ)‖ = 1 := by
  rw [norm_cubeMap, Circle.norm_coe]; norm_num

/-- The Beltrami coefficient of the radial cube: `μ(z) = z/(2z̄)` off the
origin, of modulus `1/2`. -/
theorem norm_complexDilatation_cubeMap (z : ℂ) : ‖complexDilatation cubeMap z‖ ≤ 1/2 := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [complexDilatation, wirtZ_cubeMap_zero, div_zero, norm_zero]; norm_num
  · have hp : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [complexDilatation, wirtZ_cubeMap, wirtZbar_cubeMap, norm_div, norm_mul, norm_mul,
      norm_star, Complex.norm_pow, show ‖(2:ℂ)‖ = 2 by norm_num,
      div_le_iff₀ (by positivity : (0:ℝ) < 2 * ‖z‖ * ‖z‖)]
    nlinarith [hp]

theorem isBeltramiCoeff_cubeMap : IsBeltramiCoeff (complexDilatation cubeMap) :=
  ⟨measurable_complexDilatation cubeMap, 1/2, by norm_num,
    fun z _ => norm_complexDilatation_cubeMap z⟩

/-- **The radial cube is a normalized solution of its own Beltrami equation**,
degenerate at the origin. -/
theorem isBeltramiSolution_cubeMap :
    IsBeltramiSolution (complexDilatation cubeMap) cubeMap := by
  refine ⟨continuous_cubeMap.continuousOn, cubeMap_bijOn, cubeMap_one, cubeMap_I,
    cubeMap_neg_one, fun z _ => ?_, norm_cubeMap_circle⟩
  rcases eq_or_ne z 0 with rfl | hz
  · rw [wirtZ_cubeMap_zero, wirtZbar_cubeMap, mul_zero]
    norm_num
  · rw [complexDilatation, div_mul_cancel₀ _ (wirtZ_cubeMap_ne_zero hz)]

end Cube

/-- **There is no everywhere nondegenerate solution for `μ(c)`.**

Given uniqueness against competitors differentiable throughout `D` — which is
the clause `beltramiSolution_existsUnique` now carries — the radial cube and any
everywhere nondegenerate solution would both agree with `F` on `D̄`, hence with
each other; but `D̄` is a neighbourhood of `0`, so their differentials at `0`
agree, and the cube's vanishes.

The uniqueness clause is taken as a hypothesis rather than read off
`beltramiSolution_existsUnique`, so that this theorem is free of `sorryAx`:
what it shows is that *no* correct form of the measurable Riemann mapping
theorem can also assert everywhere nondegeneracy. -/
theorem no_nondegenerate_solution_cubeMap (F : ℂ → ℂ)
    (huniq : ∀ g : ℂ → ℂ, IsBeltramiSolution (complexDilatation Cube.cubeMap) g →
      (∀ z : ℂ, ‖z‖ < 1 → DifferentiableAt ℝ g z) →
      Set.EqOn g F (Metric.closedBall (0:ℂ) 1)) :
    ¬ ∃ f : ℂ → ℂ, IsBeltramiSolution (complexDilatation Cube.cubeMap) f ∧
        ∀ z : ℂ, ‖z‖ < 1 → wirtZ f z ≠ 0 := by
  rintro ⟨f, hf, hnd⟩
  have h1 := huniq f hf (fun z hz => differentiableAt_of_wirtZ_ne_zero (hnd z hz))
  have h2 := huniq Cube.cubeMap Cube.isBeltramiSolution_cubeMap
    (fun z _ => Cube.differentiable_cubeMap z)
  have heq : Set.EqOn f Cube.cubeMap (Metric.closedBall (0:ℂ) 1) :=
    fun x hx => (h1 hx).trans (h2 hx).symm
  have hnhds : f =ᶠ[nhds (0:ℂ)] Cube.cubeMap := by
    filter_upwards [Metric.closedBall_mem_nhds (0:ℂ) one_pos] with x hx
    exact heq hx
  have hw : wirtZ f 0 = wirtZ Cube.cubeMap 0 := by
    unfold wirtZ
    rw [hnhds.fderiv_eq]
  rw [Cube.wirtZ_cubeMap_zero] at hw
  exact hnd 0 (by norm_num) hw

/-- **Measurable Riemann Mapping Theorem** (Ahlfors–Bers): for `μ ∈ M` there is a
quasiconformal homeomorphism `f^μ` of `D̄` fixing `1, i, -1` and solving the
Beltrami equation `f_z̄ = μ f_z` almost everywhere in `D`, unique on `D̄`.

The paper cites this rather than proving it.  **It is proved here**, with no
`sorry`: `AhlforsBers.exists_closedDisc_solution` derives it from the
measurable Riemann mapping theorem for the plane in the companion development
`lizhong_quasiconformal_teichmuller` (`LiZhongQC.thm13_7_normalized_existence`,
itself axiom-clean).  Extend `μ` by `0` off `D` and take the plane solution
`χ`; a Riemann map of the Jordan domain `χ(D)`, extended to the boundary by
Carathéodory's theorem, gives a self-map of `D̄` with dilatation `μ`; a rotation
and a Cayley-conjugated affine map then normalize it at `1, i, -1`, the
orientation of the boundary map coming from a single point of positive
Jacobian.  The clauses beyond existence:

* the bound `‖μ(f^μ)‖ ≤ k` holds at *every* point of `D`: at points of
  differentiability it is Li Zhong's pointwise inequality for `K`-q.c. maps
  (`ac_t_dilatation_of_differentiableAt`), elsewhere `complexDilatation` is the
  junk value `0/0 = 0`; and it holds for *every* admissible `k`, because the plane
  solution does not depend on the bound used to produce it;
* nondegeneracy a.e. is `J > 0` a.e. (`thm9_6_cor2_jacobian_pos`);
* uniqueness: a competitor differentiable throughout `D` has, by the area
  formula, `L²` partials, and is absolutely continuous on almost every line, so
  it is an `L²` generalized solution (`AhlforsBers.isGenSolution_of_differentiable`);
  by the similarity principle it differs from `f^μ` by a conformal automorphism
  of `D` fixing `1, i, -1`, which is the identity.

The last clause, quasiconformality in Li Zhong's geometric sense
(`LiZhongQC.IsKQC`), is what makes the choice behind `beltramiSolution`
usable.  Without it the other clauses do not pin `f^μ` down: for
`μ = ½ · 1_{0}` no competitor differentiable throughout `D` exists, so the
uniqueness clause is vacuous, and a Cantor-type homeomorphism that is conformal
almost everywhere but not quasiconformal meets every other clause.  Lemma 4 and
Proposition 3 are unprovable against such a specification.  The project's own
`IsKQuasiconformalOn` would not do: it is only a pointwise bound, which that
homeomorphism also satisfies.

**The statement was corrected twice** before it could be proved.  The first
repair was the uniqueness clause: as originally written it was false whenever a
degenerate solution exists (`beltramiSolution_existsUnique_false_of_degenerate`),
because `IsBeltramiSolution` builds in no regularity.  Uniqueness was then
restricted to competitors with `f_z ≠ 0` throughout `D`.

That repair was itself wrong, and this is the second.  A nonvanishing `f_z` at
*every* point of `D` forces `f` to be differentiable at every point, and for a
general measurable `μ` no solution is: the solution is a Sobolev homeomorphism,
differentiable only a.e.  `no_nondegenerate_solution_cubeMap` makes this
concrete — for `μ = μ(c)` with `c(z) = z²z̄` there is *no* everywhere
nondegenerate solution at all, so the previous statement asserted the existence
of something that does not exist.

So the Beltrami equation and the nondegeneracy are **almost everywhere**, and
uniqueness is asserted against competitors that are differentiable throughout
`D` — a class in which uniqueness does hold (proved as above), and the class
every competitor in this development lies in: they are all real-analytic on
`D`.

Three pointwise facts are part of the statement, because they are true of
`f^μ` and are what the rest of the development consumes:

* `f^μ(D) ⊆ D` — `f^μ` is a homeomorphism of `D̄` carrying `S¹` onto `S¹`;
* `‖μ(f^μ)‖ ≤ k` at *every* point of `D`;
* the boundary values are unimodular. -/
theorem beltramiSolution_existsUnique (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    ∃ f : ℂ → ℂ, IsBeltramiSolutionAE μ f ∧
      (∀ z : ℂ, ‖z‖ < 1 → ‖f z‖ < 1) ∧
      (∀ k : ℝ, (∀ z : ℂ, ‖z‖ < 1 → ‖μ z‖ ≤ k) →
        ∀ z : ℂ, ‖z‖ < 1 → ‖complexDilatation f z‖ ≤ k) ∧
      (∀ᵐ z : ℂ, ‖z‖ < 1 → wirtZ f z ≠ 0) ∧
      (∀ g : ℂ → ℂ, IsBeltramiSolution μ g →
        (∀ z : ℂ, ‖z‖ < 1 → DifferentiableAt ℝ g z) →
        Set.EqOn g f (Metric.closedBall (0:ℂ) 1)) ∧
      (∃ K : ℝ, LiZhongQC.IsKQC f LiZhongQC.unitDisc K) := by
  obtain ⟨hμm, k, hk, hkb⟩ := hμ
  have hk₀ : 0 ≤ k := (norm_nonneg _).trans (hkb 0 (by simp))
  obtain ⟨f, hc, hb, h1, hI, hm1, hS, hD, hae, hpt, hK, huniq⟩ :=
    AhlforsBers.exists_closedDisc_solution hk₀ hk hμm hkb
  refine ⟨f, ⟨hc, hb, h1, hI, hm1, ?_, fun ζ => hS ζ (Circle.norm_coe ζ)⟩, hD,
    fun k' hk' z hz => hpt k' hk' z hz, ?_, ?_, hK⟩
  · filter_upwards [hae] with z hz hz1 using (hz hz1).1
  · filter_upwards [hae] with z hz hz1 using (hz hz1).2
  · rintro g ⟨hgc, hgb, hg1, hgI, hgm1, hgeq, hgS⟩ hgd
    exact huniq g hgc hgb hg1 hgI hgm1
      (fun z hz => hgS ⟨z, mem_sphere_zero_iff_norm.2 hz⟩) hgd hgeq

private theorem beltramiSolution_aux (μ : ℂ → ℂ) :
    ∃ f : ℂ → ℂ, IsBeltramiCoeff μ → (IsBeltramiSolutionAE μ f ∧
      (∀ z : ℂ, ‖z‖ < 1 → ‖f z‖ < 1) ∧
      (∀ k : ℝ, (∀ z : ℂ, ‖z‖ < 1 → ‖μ z‖ ≤ k) →
        ∀ z : ℂ, ‖z‖ < 1 → ‖complexDilatation f z‖ ≤ k) ∧
      (∀ᵐ z : ℂ, ‖z‖ < 1 → wirtZ f z ≠ 0) ∧
      (∀ g : ℂ → ℂ, IsBeltramiSolution μ g →
        (∀ z : ℂ, ‖z‖ < 1 → DifferentiableAt ℝ g z) →
        Set.EqOn g f (Metric.closedBall (0:ℂ) 1)) ∧
      (∃ K : ℝ, LiZhongQC.IsKQC f LiZhongQC.unitDisc K)) := by
  by_cases h : IsBeltramiCoeff μ
  · obtain ⟨f, hf⟩ := beltramiSolution_existsUnique μ h
    exact ⟨f, fun _ => hf⟩
  · exact ⟨id, fun h' => absurd h' h⟩

/-- `f^μ`, the normalized quasiconformal solution of the Beltrami equation. -/
def beltramiSolution (μ : ℂ → ℂ) : ℂ → ℂ := Classical.choose (beltramiSolution_aux μ)

/-- `f^μ` is a normalized solution. -/
theorem beltramiSolution_spec (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    IsBeltramiSolutionAE μ (beltramiSolution μ) :=
  (Classical.choose_spec (beltramiSolution_aux μ) hμ).1

/-- `f^μ` maps `D` into `D`.  Part of "`f^μ` is a homeomorphism of `D̄`", read
off `beltramiSolution_existsUnique` rather than derived here: the old derivation
ran on nondegeneracy at every point of `D`, which is not available. -/
theorem beltramiSolution_mem_disk (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) {z : ℂ}
    (hz : ‖z‖ < 1) : ‖beltramiSolution μ z‖ < 1 :=
  (Classical.choose_spec (beltramiSolution_aux μ) hμ).2.1 z hz

/-- The dilatation bound, at *every* point of `D`: where `f^μ` is
differentiable this is the Beltrami equation, and where it is not it is the
junk value `0/0 = 0`. -/
theorem beltramiSolution_norm_complexDilatation_le (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ)
    (k : ℝ) (hkb : ∀ z : ℂ, ‖z‖ < 1 → ‖μ z‖ ≤ k) :
    ∀ z : ℂ, ‖z‖ < 1 → ‖complexDilatation (beltramiSolution μ) z‖ ≤ k :=
  (Classical.choose_spec (beltramiSolution_aux μ) hμ).2.2.1 k hkb

/-- `f^μ` is nondegenerate almost everywhere in `D`.  It cannot be asserted at
every point; see `no_nondegenerate_solution_cubeMap`. -/
theorem beltramiSolution_wirtZ_ne_zero_ae (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    ∀ᵐ z : ℂ, ‖z‖ < 1 → wirtZ (beltramiSolution μ) z ≠ 0 :=
  (Classical.choose_spec (beltramiSolution_aux μ) hμ).2.2.2.1

/-- Any normalized solution that is *differentiable throughout* `D` and
satisfies the Beltrami equation there agrees with `f^μ` on `D̄`.  Some
regularity hypothesis is unavoidable — without one the clause is refuted by
`beltramiSolution_existsUnique_false_of_degenerate` — and this one is what
every competitor in this development satisfies, being real-analytic on `D`. -/
theorem beltramiSolution_eqOn (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) (g : ℂ → ℂ)
    (hg : IsBeltramiSolution μ g) (hgd : ∀ z : ℂ, ‖z‖ < 1 → DifferentiableAt ℝ g z) :
    Set.EqOn g (beltramiSolution μ) (Metric.closedBall (0:ℂ) 1) :=
  (Classical.choose_spec (beltramiSolution_aux μ) hμ).2.2.2.2.1 g hg hgd

/-- `f^μ` is quasiconformal on `D`. -/
theorem beltramiSolution_isKQC (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    ∃ K : ℝ, LiZhongQC.IsKQC (beltramiSolution μ) LiZhongQC.unitDisc K :=
  (Classical.choose_spec (beltramiSolution_aux μ) hμ).2.2.2.2.2

/-- Accessor: `f^μ` is continuous on `D̄`. -/
theorem beltramiSolution_continuousOn (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    ContinuousOn (beltramiSolution μ) (Metric.closedBall (0:ℂ) 1) :=
  (beltramiSolution_spec μ hμ).1

/-- Accessor: `f^μ` maps `D̄` bijectively onto itself. -/
theorem beltramiSolution_bijOn (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    Set.BijOn (beltramiSolution μ) (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1) :=
  (beltramiSolution_spec μ hμ).2.1

/-- Accessor: `f^μ` fixes `1`. -/
theorem beltramiSolution_one (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    beltramiSolution μ 1 = 1 :=
  (beltramiSolution_spec μ hμ).2.2.1

/-- Accessor: `f^μ` fixes `i`. -/
theorem beltramiSolution_I (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    beltramiSolution μ Complex.I = Complex.I :=
  (beltramiSolution_spec μ hμ).2.2.2.1

/-- Accessor: `f^μ` fixes `-1`. -/
theorem beltramiSolution_neg_one (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    beltramiSolution μ (-1) = -1 :=
  (beltramiSolution_spec μ hμ).2.2.2.2.1

/-- Accessor: `f^μ` satisfies the Beltrami equation almost everywhere in `D`. -/
theorem beltramiSolution_beltramiEq_ae (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    ∀ᵐ z : ℂ, ‖z‖ < 1 → wirtZbar (beltramiSolution μ) z = μ z * wirtZ (beltramiSolution μ) z :=
  (beltramiSolution_spec μ hμ).2.2.2.2.2.1

/-- `f^μ` is `K`-quasiconformal with `K = (1+k)/(1-k)`: its complex dilatation
is `μ` wherever `f_z ≠ 0`, and `0` (hence harmless) where `f_z = 0`. -/
theorem beltramiSolution_isKQuasiconformalOn (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ)
    {k : ℝ} (hk : k < 1) (hkb : ∀ z : ℂ, ‖z‖ < 1 → ‖μ z‖ ≤ k) :
    IsKQuasiconformalOn (beltramiSolution μ) (Metric.ball (0:ℂ) 1) ((1 + k) / (1 - k)) := by
  have hk0 : 0 ≤ k := le_trans (norm_nonneg _) (hkb 0 (by simp))
  have h1k : 0 < 1 - k := by linarith
  refine ⟨by rw [le_div_iff₀ h1k]; linarith, fun z hz => ?_⟩
  have hzb : ‖z‖ < 1 := by simpa using hz
  have hbound : ((1 + k) / (1 - k) - 1) / ((1 + k) / (1 - k) + 1) = k := by
    field_simp
    ring
  rw [hbound]
  exact beltramiSolution_norm_complexDilatation_le μ hμ k hkb z hzb

/-- Where `f^μ` satisfies the equation with `f_z ≠ 0`, its complex dilatation is
`μ`.  The equation is now a hypothesis rather than an accessor, because it holds
only almost everywhere. -/
theorem complexDilatation_beltramiSolution (μ : ℂ → ℂ) (z : ℂ)
    (heq : wirtZbar (beltramiSolution μ) z = μ z * wirtZ (beltramiSolution μ) z)
    (hne : wirtZ (beltramiSolution μ) z ≠ 0) :
    complexDilatation (beltramiSolution μ) z = μ z := by
  rw [complexDilatation, heq, mul_div_assoc, div_self hne, mul_one]

/-- The regularity of `f^μ` that Lemma 4 consumes, packaged: at the point `z`
the Beltrami equation holds and `f^μ_z ≠ 0`.  It holds almost everywhere
(`beltramiSolution_beltramiEq_ae`, `beltramiSolution_wirtZ_ne_zero_ae`) and, as
`no_nondegenerate_solution_cubeMap` shows, cannot be asserted everywhere. -/
def BeltramiRegular (μ : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 →
    wirtZbar (beltramiSolution μ) z = μ z * wirtZ (beltramiSolution μ) z ∧
      wirtZ (beltramiSolution μ) z ≠ 0

theorem differentiableAt_beltramiSolution {μ : ℂ → ℂ} (hreg : BeltramiRegular μ) {z : ℂ}
    (hz : ‖z‖ < 1) : DifferentiableAt ℝ (beltramiSolution μ) z :=
  differentiableAt_of_wirtZ_ne_zero (hreg z hz).2

theorem norm_wirtZbar_lt_norm_wirtZ_beltramiSolution {μ : ℂ → ℂ} (hμ : IsBeltramiCoeff μ)
    (hreg : BeltramiRegular μ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖wirtZbar (beltramiSolution μ) z‖ < ‖wirtZ (beltramiSolution μ) z‖ := by
  obtain ⟨k, hk, hkb⟩ := hμ.2
  have hp : 0 < ‖wirtZ (beltramiSolution μ) z‖ := norm_pos_iff.2 (hreg z hz).2
  rw [(hreg z hz).1, norm_mul]
  nlinarith [hkb z hz, norm_nonneg (μ z)]

/-- Accessor: `f^μ` is unimodular on `S¹`.

This was previously an anonymous `by sorry` *inside the definition* of
`beltramiBoundary`, which made that definition — and hence `sigmaMap` and
everything said about it — depend on `sorryAx` invisibly.  It is now a clause
of `IsBeltramiSolution`, and so part of what `beltramiSolution_existsUnique`
proves, where `f^μ` is a homeomorphism of `D̄` *onto* `D̄` and
therefore carries `S¹` onto `S¹`.

The interior half — that a solution maps the open disk into the open disk —
used to be *proved* here, from nondegeneracy alone and with no appeal to
invariance of domain (`norm_lt_one_of_beltrami`).  That derivation needed
`f^μ_z ≠ 0` at every point of `D`, which is exactly what
`no_nondegenerate_solution_cubeMap` rules out, so it is now read off
`beltramiSolution_existsUnique` alongside the boundary half, as
`beltramiSolution_mem_disk`.  `norm_lt_one_of_beltrami`
remains, and still applies to the maps that *are* everywhere nondegenerate —
`E(φ)` among them. -/
theorem beltramiSolution_mem_sphere (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) (ζ : Circle) :
    beltramiSolution μ (ζ : ℂ) ∈ Submonoid.unitSphere ℂ :=
  mem_sphere_zero_iff_norm.2 ((beltramiSolution_spec μ hμ).2.2.2.2.2.2 ζ)

open Classical in
/-- `φ^μ`, the boundary values of `f^μ`, as a self-map of `S¹`.  The junk value
`1` is taken where `f^μ` is not unimodular; `beltramiBoundary_coe` says that
never happens for `μ ∈ M`. -/
def beltramiBoundary (μ : ℂ → ℂ) : Circle → Circle :=
  fun ζ =>
    if h : beltramiSolution μ (ζ : ℂ) ∈ Submonoid.unitSphere ℂ then
      ⟨beltramiSolution μ (ζ : ℂ), h⟩
    else 1

theorem beltramiBoundary_coe (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) (ζ : Circle) :
    ((beltramiBoundary μ ζ : Circle) : ℂ) = beltramiSolution μ (ζ : ℂ) := by
  simp only [beltramiBoundary, beltramiSolution_mem_sphere μ hμ ζ, ↓reduceDIte]

/-! ### `φ^μ` is a homeomorphism of `S¹`

Injectivity and continuity of `φ^μ` follow from `f^μ` being an injective
continuous self-map of `D̄`.  *Surjectivity* does not: it needs `f^μ` to carry
`S¹` **onto** `S¹`, and the preimage of a boundary point could a priori be an
interior point.  Ruling that out is the same invariance-of-domain step that
blocks `beltramiSolution_mem_sphere`, so surjectivity is carried as an explicit
hypothesis below rather than proved. -/

theorem beltramiBoundary_injective (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    Function.Injective (beltramiBoundary μ) := by
  intro ζ₁ ζ₂ h
  have h1 : beltramiSolution μ (ζ₁ : ℂ) = beltramiSolution μ (ζ₂ : ℂ) := by
    rw [← beltramiBoundary_coe μ hμ ζ₁, ← beltramiBoundary_coe μ hμ ζ₂, h]
  have hbij := (beltramiSolution_spec μ hμ).2.1
  exact Subtype.ext (hbij.injOn (by simp) (by simp) h1)

theorem beltramiBoundary_continuous (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    Continuous (beltramiBoundary μ) := by
  have hf := (beltramiSolution_spec μ hμ).1
  have hmaps : ∀ ζ : Circle, ((ζ : ℂ)) ∈ Metric.closedBall (0:ℂ) 1 := fun ζ => by simp
  have hcomp : Continuous fun ζ : Circle => beltramiSolution μ ((ζ : ℂ)) :=
    hf.comp_continuous continuous_subtype_val hmaps
  have heq : (fun ζ : Circle => beltramiSolution μ ((ζ : ℂ)))
      = fun ζ : Circle => ((beltramiBoundary μ ζ : Circle) : ℂ) := by
    funext ζ; exact (beltramiBoundary_coe μ hμ ζ).symm
  rw [heq] at hcomp
  exact continuous_induced_rng.2 hcomp

/-- `i`, as an element of `Circle`. -/
def circI : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.2 (by simp)⟩

/-- `-1`, as an element of `Circle`. -/
def circNegOne : Circle := ⟨-1, mem_sphere_zero_iff_norm.2 (by simp)⟩

/-! `E(φ^μ)` inherits the normalization of `f^μ` at `1, i, -1`, because on `S¹`
the extension *is* its boundary map. -/

theorem extension_beltramiBoundary_one (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    extension (beltramiBoundary μ) 1 = 1 := by
  have h := extension_eq_boundary (beltramiBoundary μ) 1
  rw [Circle.coe_one] at h
  rw [h, beltramiBoundary_coe μ hμ 1, Circle.coe_one]
  exact (beltramiSolution_spec μ hμ).2.2.1

theorem extension_beltramiBoundary_I (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    extension (beltramiBoundary μ) Complex.I = Complex.I := by
  have h := extension_eq_boundary (beltramiBoundary μ) circI
  rw [show ((circI : Circle) : ℂ) = Complex.I from rfl] at h
  rw [h, beltramiBoundary_coe μ hμ circI, show ((circI : Circle) : ℂ) = Complex.I from rfl]
  exact (beltramiSolution_spec μ hμ).2.2.2.1

theorem extension_beltramiBoundary_neg_one (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    extension (beltramiBoundary μ) (-1) = -1 := by
  have h := extension_eq_boundary (beltramiBoundary μ) circNegOne
  rw [show ((circNegOne : Circle) : ℂ) = -1 from rfl] at h
  rw [h, beltramiBoundary_coe μ hμ circNegOne, show ((circNegOne : Circle) : ℂ) = -1 from rfl]
  exact (beltramiSolution_spec μ hμ).2.2.2.2.1

/-- `extension_jacobian_ne_zero` restated in Wirtinger form: the two sides
there are `2‖Φ_z̄‖` and `2‖Φ_z‖`.

Theorem 1 gives only `≠`, and only `≠` is true of every homeomorphism of the
circle: `E(ζ ↦ ζ⁻¹) = conj` has `Φ_z = 0` and `Φ_z̄ = 1`
(`extension_jacobian_ne_zero_false`).  The strict form, which is what Sections
6 and 7 need, is `norm_wirtZbar_lt_norm_wirtZ_extension` below. -/
theorem norm_wirtZbar_ne_norm_wirtZ_extension (φ : Circle → Circle)
    (hφ : Function.Bijective φ) (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖wirtZbar (extension φ) z‖ ≠ ‖wirtZ (extension φ) z‖ := by
  have h := extension_jacobian_ne_zero φ hφ hφc z hz
  rw [wirtZ, wirtZbar, norm_div, norm_div]
  simp only [Complex.norm_ofNat]
  intro hc
  exact h (by linarith)

/-- `extension_jacobian_pos` restated in Wirtinger form.  `hor` is the
orientation hypothesis the strict inequality needs; see
`extension_jacobian_ne_zero_false` for what happens without it. -/
theorem norm_wirtZbar_lt_norm_wirtZ_extension (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (hor : HasIncreasingLift φ) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖wirtZbar (extension φ) z‖ < ‖wirtZ (extension φ) z‖ := by
  have h := extension_jacobian_pos φ hφ hφc hor z hz
  rw [wirtZ, wirtZbar, norm_div, norm_div]
  simp only [Complex.norm_ofNat]
  exact div_lt_div_of_pos_right h (by norm_num)

/-- `Φ_z ≠ 0`.  This is where orientation is genuinely needed and not merely
convenient: a nonzero Jacobian allows `Φ_z = 0` (with `Φ_z̄ ≠ 0`), and
`E(ζ ↦ ζ⁻¹) = conj` is exactly that case.  Every use of this lemma below is a
place where `μ = Φ_z̄/Φ_z` has to be a genuine quotient. -/
theorem wirtZ_extension_ne_zero (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (hor : HasIncreasingLift φ) (z : ℂ) (hz : ‖z‖ < 1) :
    wirtZ (extension φ) z ≠ 0 := by
  intro hcon
  have h := norm_wirtZbar_lt_norm_wirtZ_extension φ hφ hφc hor z hz
  rw [hcon, norm_zero] at h
  exact absurd h (not_lt.2 (norm_nonneg _))

/-- Real differentiability of `Φ` on `D` is *not* a separate input: `Φ` is
real-analytic there (`extension_analyticOn_disk`).

This used to be routed through `Φ_z ≠ 0` and the junk value of `fderiv` at a
non-differentiable point.  That route needs orientation, and this one does
not — which is why it is the one taken now. -/
theorem differentiableAt_extension (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) : DifferentiableAt ℝ (extension φ) z :=
  (Metric.isOpen_ball.analyticOn_iff_analyticOnNhd.mp
    (extension_analyticOn_disk φ hφ hφc) z (by simpa using hz)).differentiableAt

/-- The Corollary to Proposition 2 in Wirtinger form: `φ ↦ (Φ_z(0), Φ_z̄(0))` is
continuous on the homeomorphisms.  `extension_derivative_continuous` is the same
statement written with `dΦ(1)` and `dΦ(i)`, which is all `Extension.lean` can
say, `wirtZ` being defined here; the two differ by the invertible linear change
`(a, b) ↦ ((a - i b)/2, (a + i b)/2)`. -/
theorem continuousOn_wirt_extension_zero :
    ContinuousOn (fun φ : C(Circle, Circle) =>
        (wirtZ (extension φ) 0, wirtZbar (extension φ) 0))
      {φ : C(Circle, Circle) | Function.Bijective φ} := by
  have hL : Continuous (fun p : ℂ × ℂ =>
      ((p.1 - Complex.I * p.2) / 2, (p.1 + Complex.I * p.2) / 2)) := by fun_prop
  exact hL.comp_continuousOn extension_derivative_continuous

/-! ### `φ ↦ μ(E(φ))`, continuously

`sigmaMap` is `complexDilatation (extension (beltramiBoundary μ))`, so the
continuity Lemma 5(b) asks for is continuity of `φ ↦ μ(E(φ))` in `φ`.  As a map
into `ℂ → ℂ` that is pointwise continuity, one `z` at a time, and the disk
splits from its complement:

* inside `D` the quotient `Φ_z̄/Φ_z` is continuous in `φ` because both Wirtinger
  derivatives are (`extension_derivative_continuousOn`, the Corollary to
  Proposition 2 moved off the origin) and the denominator does not vanish
  (`wirtZ_extension_ne_zero`) — the one place orientation is spent;
* on and outside `S¹` it is the constant `0`, for junk-value reasons that have
  nothing to do with `φ`. -/

/-- Off the open disk the dilatation of `E(φ)` is the constant `0`, for every
`φ` whatsoever.

Outside `D̄` that is because `E(φ)` is the junk value `0` on a neighbourhood.
*On* `S¹` it is the junk value of `fderiv`: `E(φ)` has modulus `1` on the
sphere and `0` just outside it, so it is not even continuous there, let alone
differentiable, and `fderiv` of a non-differentiable map is `0` by
convention. -/
theorem complexDilatation_extension_of_one_le (φ : Circle → Circle) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    complexDilatation (extension φ) z = 0 := by
  have hfd : fderiv ℝ (extension φ) z = 0 := by
    rcases eq_or_lt_of_le hz with heq | hlt
    · -- `‖z‖ = 1`: `E(φ)` jumps to `0` immediately outside the sphere
      have hz1 : ‖z‖ = 1 := heq.symm
      refine fderiv_zero_of_not_differentiableAt (fun hdiff => ?_)
      set ζ : Circle := ⟨z, mem_sphere_zero_iff_norm.2 hz1⟩ with hζ
      have hnorm : ‖extension φ z‖ = 1 := by
        rw [show z = (ζ : ℂ) from rfl, extension_eq_boundary φ ζ]
        exact Circle.norm_coe _
      have hc : ContinuousAt (extension φ) z := hdiff.continuousAt
      have hlim : Filter.Tendsto (fun t : ℝ => ((t : ℂ) * z))
          (nhdsWithin 1 (Set.Ioi 1)) (nhds z) := by
        have hcont : Continuous (fun t : ℝ => ((t : ℂ) * z)) := by fun_prop
        have hcw : Filter.Tendsto (fun t : ℝ => ((t : ℂ) * z))
            (nhdsWithin 1 (Set.Ioi 1)) (nhds (((1:ℝ) : ℂ) * z)) := hcont.continuousWithinAt
        simpa using hcw
      have h2 : Filter.Tendsto (fun t : ℝ => extension φ ((t : ℂ) * z))
          (nhdsWithin 1 (Set.Ioi 1)) (nhds (extension φ z)) := hc.tendsto.comp hlim
      have h3 : (fun t : ℝ => extension φ ((t : ℂ) * z))
          =ᶠ[nhdsWithin 1 (Set.Ioi 1)] fun _ => (0 : ℂ) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        refine extension_eq_zero_of_one_lt φ _ ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (lt_trans one_pos ht), hz1, mul_one]
        exact ht
      have h4 := h2.congr' h3
      have h5 := tendsto_nhds_unique h4 tendsto_const_nhds
      rw [h5] at hnorm
      simp at hnorm
    · -- `1 < ‖z‖`: `E(φ)` vanishes on a neighbourhood
      have hev : extension φ =ᶠ[nhds z] fun _ => (0 : ℂ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hlt] with w hw
        exact extension_eq_zero_of_one_lt φ w hw
      rw [hev.fderiv_eq]
      simp
  simp [complexDilatation, wirtZ, hfd]

/-- **Continuity of `φ ↦ μ(E(φ))(z)` inside the disk.**  Numerator and
denominator are continuous in `φ` by the Corollary to Proposition 2
(`extension_derivative_continuousOn`), and the denominator does not vanish by
`wirtZ_extension_ne_zero` — which is where orientation is spent. -/
theorem continuousWithinAt_complexDilatation_extension {z : ℂ} (hz : ‖z‖ < 1)
    (S : Set C(Circle, Circle)) (hSb : ∀ ψ ∈ S, Function.Bijective (ψ : Circle → Circle))
    (φ : C(Circle, Circle)) (hφS : φ ∈ S) (hor : HasIncreasingLift (φ : Circle → Circle)) :
    ContinuousWithinAt (fun ψ : C(Circle, Circle) => complexDilatation (extension ψ) z) S φ := by
  have hsub : S ⊆ {ψ : C(Circle, Circle) | Function.Bijective (ψ : Circle → Circle)} :=
    fun ψ hψ => hSb ψ hψ
  have hd := (extension_derivative_continuousOn z hz).mono hsub φ hφS
  have hA : ContinuousWithinAt
      (fun ψ : C(Circle, Circle) => (fderiv ℝ (extension ψ) z : ℂ →L[ℝ] ℂ) 1) S φ := hd.fst
  have hB : ContinuousWithinAt
      (fun ψ : C(Circle, Circle) => (fderiv ℝ (extension ψ) z : ℂ →L[ℝ] ℂ) Complex.I) S φ := hd.snd
  have hZ : ContinuousWithinAt
      (fun ψ : C(Circle, Circle) => wirtZ (extension ψ) z) S φ := by
    simp only [wirtZ]
    exact (hA.sub (continuousWithinAt_const.mul hB)).div_const 2
  have hZb : ContinuousWithinAt
      (fun ψ : C(Circle, Circle) => wirtZbar (extension ψ) z) S φ := by
    simp only [wirtZbar]
    exact (hA.add (continuousWithinAt_const.mul hB)).div_const 2
  have hne : wirtZ (extension φ) z ≠ 0 :=
    wirtZ_extension_ne_zero _ (hSb φ hφS) φ.continuous hor z hz
  exact (hZb.div hZ hne).congr (fun ψ _ => rfl) rfl

/-- The two halves together: `φ ↦ μ(E(φ))` is continuous, as a map into
`ℂ → ℂ` with the topology of pointwise convergence, on any set of
homeomorphisms with increasing lifts. -/
theorem continuousOn_complexDilatation_extension
    (S : Set C(Circle, Circle)) (hSb : ∀ ψ ∈ S, Function.Bijective (ψ : Circle → Circle))
    (hSo : ∀ ψ ∈ S, HasIncreasingLift (ψ : Circle → Circle)) :
    ContinuousOn (fun ψ : C(Circle, Circle) => complexDilatation (extension ψ)) S := by
  rw [continuousOn_pi]
  intro z
  rcases lt_or_ge ‖z‖ 1 with hz | hz
  · exact fun φ hφ =>
      continuousWithinAt_complexDilatation_extension hz S hSb φ hφ (hSo φ hφ)
  · refine ContinuousOn.congr (continuousOn_const (c := (0:ℂ))) (fun ψ _ => ?_)
    exact complexDilatation_extension_of_one_le _ hz

/-- **`φ^μ` is onto**, and no plane topology is needed for it.

This was the invariance-of-domain gap, threaded as `hsurj` through most of
Sections 6 and 7.  It closes because the *interior* half of "`f^μ` is a
homeomorphism of `D̄`" is available analytically: `f^μ` is onto `D̄`
(`beltramiSolution_bijOn`) and maps `D` into `D`
(`beltramiSolution_mem_disk`), so a preimage of a boundary point cannot be
interior — it must already lie on `S¹`.

What genuinely needs plane topology is the statement for an *arbitrary*
quasiconformal homeomorphism of `D̄`, where nondegeneracy is unavailable; but
that is not what any of these theorems were asking for. -/
theorem beltramiBoundary_surjective (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    Function.Surjective (beltramiBoundary μ) := by
  intro η
  obtain ⟨w, hw, hfw⟩ := (beltramiSolution_bijOn μ hμ).surjOn
    (show ((η : Circle) : ℂ) ∈ Metric.closedBall (0:ℂ) 1 by simp)
  have hw1 : ‖w‖ ≤ 1 := by simpa using hw
  have hwsphere : ‖w‖ = 1 := by
    rcases lt_or_eq_of_le hw1 with hlt | heq
    · exfalso
      have hlt' := beltramiSolution_mem_disk μ hμ hlt
      rw [hfw, Circle.norm_coe] at hlt'
      exact lt_irrefl 1 hlt'
    · exact heq
  refine ⟨⟨w, mem_sphere_zero_iff_norm.2 hwsphere⟩, Subtype.ext ?_⟩
  exact (beltramiBoundary_coe μ hμ _).trans hfw

theorem beltramiBoundary_bijective (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) :
    Function.Bijective (beltramiBoundary μ) :=
  ⟨beltramiBoundary_injective μ hμ, beltramiBoundary_surjective μ hμ⟩

/-- The map `σ : M → M`, `σ(μ) = μ(E(φ^μ))`, of formula (6.1); well-defined
(i.e. valued in `M` again) by Theorem 2 applied to `φ^μ`. -/
def sigmaMap (μ : ℂ → ℂ) : ℂ → ℂ := complexDilatation (extension (beltramiBoundary μ))

/-- `f^μ` *is* a quasiconformal extension of `φ^μ`, with `K = (1+k)/(1-k)`.
Everything needed is already recorded: `f^μ` is a continuous bijection of `D̄`
whose dilatation is `μ` (`beltramiSolution_isKQuasiconformalOn`), and `φ^μ` is
by definition its boundary map. -/
theorem hasQCExtension_beltramiBoundary (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ)
    {k : ℝ} (hk : k < 1) (hkb : ∀ z : ℂ, ‖z‖ < 1 → ‖μ z‖ ≤ k) :
    HasQCExtension (beltramiBoundary μ) ((1 + k) / (1 - k)) :=
  ⟨beltramiSolution μ, beltramiSolution_continuousOn μ hμ, beltramiSolution_bijOn μ hμ,
    beltramiSolution_isKQuasiconformalOn μ hμ hk hkb,
    fun ζ => (beltramiBoundary_coe μ hμ ζ).symm⟩

/-- `σ` really does land in `M` again.

Measurability is free — `fderiv` is measurable, so
`measurable_complexDilatation` applies to any map whatsoever, `E(φ^μ)`
included.  The content is the bound `‖σ(μ)‖ < 1`, and by now that is one
application of `theorem2_quasiconformal` to `φ^μ`: `f^μ` is a quasiconformal
extension of `φ^μ` with `K = (1+k)/(1-k)` (`hasQCExtension_beltramiBoundary`),
so `E(φ^μ)` is `K'`-quasiconformal for some `K'`, and `(K'-1)/(K'+1) < 1` is
the bound.

`h51` is Douady–Earle's Section 5 estimate, stated for every `K` because the
`K` that arises here is manufactured from `μ`'s own bound.  It is now the only
input: surjectivity of `φ^μ` used to be assumed and is now
`beltramiBoundary_surjective`. -/
theorem sigmaMap_isBeltramiCoeff (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ)
    (h51 : ∀ K : ℝ, ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ ψ : Circle → Circle, Function.Bijective ψ → HasQCExtension ψ K →
        ∀ z : ℂ, ‖z‖ < 1 → a ≤ alphaFn ψ z ∧ alphaFn ψ z ≤ betaFn ψ z ∧ betaFn ψ z ≤ b) :
    IsBeltramiCoeff (sigmaMap μ) := by
  obtain ⟨k, hk, hkb⟩ := hμ.2
  have hbij : Function.Bijective (beltramiBoundary μ) := beltramiBoundary_bijective μ hμ
  have hqc : HasQCExtension (beltramiBoundary μ) ((1 + k) / (1 - k)) :=
    hasQCExtension_beltramiBoundary μ hμ hk hkb
  obtain ⟨K', hK'⟩ :=
    theorem2_quasiconformal (beltramiBoundary μ) hbij _ hqc (h51 ((1 + k) / (1 - k)))
  refine ⟨measurable_complexDilatation _, (K' - 1) / (K' + 1), ?_, fun z hz => ?_⟩
  · rw [div_lt_one (by linarith [hK'.1])]
    linarith
  · exact hK'.2 z (by simpa using hz)

/-- `E(φ^μ)` is itself a normalized solution of the Beltrami equation, for the
coefficient `σ(μ)`.

Four of the five conditions are proved here.  The Beltrami equation is the
interesting one, and it holds *by construction*: `σ(μ)` is defined to be
`Φ_z̄/Φ_z`, so `Φ_z̄ = σ(μ)·Φ_z` is just `div_mul_cancel₀`.  That cancellation
needs `Φ_z ≠ 0`, and the need is real rather than technical — where `Φ_z = 0`
Lean's `x/0 = 0` sets `σ(μ) = 0`, and the equation would then assert
`Φ_z̄ = 0`, which is false at such a point unless the whole differential
vanishes.  `wirtZ_extension_ne_zero` supplies the hypothesis, and `horient`
is its price: the nonvanishing of `Φ_z`, as opposed to the nonvanishing of the
Jacobian, is an orientation statement.  `φ^μ` is orientation preserving —
it is the boundary map of a quasiconformal homeomorphism of `D̄` — but that
implication is circle-lifting, which this development does not have, so the
lift is a hypothesis.

Continuity and bijectivity on `D̄` are Theorem 1 (`extension_isHomeomorphOn`);
the normalization at `1, i, -1` is inherited from `f^μ`. -/
theorem isBeltramiSolution_extension_beltramiBoundary (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ)
    (horient : HasIncreasingLift (beltramiBoundary μ)) :
    IsBeltramiSolution (sigmaMap μ) (extension (beltramiBoundary μ)) := by
  have hbij : Function.Bijective (beltramiBoundary μ) := beltramiBoundary_bijective μ hμ
  have hcont : Continuous (beltramiBoundary μ) := beltramiBoundary_continuous μ hμ
  obtain ⟨hBij, hCont, -⟩ := extension_isHomeomorphOn (beltramiBoundary μ) hbij hcont
  refine ⟨hCont, hBij, extension_beltramiBoundary_one μ hμ,
    extension_beltramiBoundary_I μ hμ, extension_beltramiBoundary_neg_one μ hμ, ?_,
    fun ζ => by rw [extension_eq_boundary]; exact Circle.norm_coe _⟩
  intro z hz
  rw [sigmaMap, complexDilatation]
  exact (div_mul_cancel₀ _ (wirtZ_extension_ne_zero _ hbij hcont horient z hz)).symm

/-- `E(φ^μ) = f^{σ(μ)}` (formula (6.2)).

Given the previous lemma this is exactly the uniqueness half of the measurable
Riemann mapping theorem: both sides are normalized solutions for `σ(μ)`, so
`beltramiSolution_eqOn` identifies them on `D̄`.

`h51` is needed only to know `σ(μ) ∈ M`, via `sigmaMap_isBeltramiCoeff`. -/
theorem extension_beltramiBoundary_eq (μ : ℂ → ℂ) (hμ : IsBeltramiCoeff μ)
    (horient : HasIncreasingLift (beltramiBoundary μ))
    (h51 : ∀ K : ℝ, ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ ψ : Circle → Circle, Function.Bijective ψ → HasQCExtension ψ K →
        ∀ z : ℂ, ‖z‖ < 1 → a ≤ alphaFn ψ z ∧ alphaFn ψ z ≤ betaFn ψ z ∧ betaFn ψ z ≤ b) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → extension (beltramiBoundary μ) z = beltramiSolution (sigmaMap μ) z := by
  intro z hz
  have hbij : Function.Bijective (beltramiBoundary μ) := beltramiBoundary_bijective μ hμ
  exact beltramiSolution_eqOn (sigmaMap μ) (sigmaMap_isBeltramiCoeff μ hμ h51)
    (extension (beltramiBoundary μ))
    (isBeltramiSolution_extension_beltramiBoundary μ hμ horient)
    (fun w hw => differentiableAt_of_wirtZ_ne_zero
      (wirtZ_extension_ne_zero _ hbij (beltramiBoundary_continuous μ hμ) horient w hw))
    (by simpa using hz)

/-- **Proposition 3**: `σ : M → M` is continuous; in fact uniformly
continuous on each `M_k = {μ ∈ M : ‖μ‖_∞ ≤ k}`, `k < 1`. -/
theorem sigmaMap_uniformlyContinuousOn (k : ℝ) (hk : k < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ μ ν : ℂ → ℂ, IsBeltramiCoeff μ → IsBeltramiCoeff ν →
        (∀ z, ‖z‖ < 1 → ‖μ z‖ ≤ k) → (∀ z, ‖z‖ < 1 → ‖ν z‖ ≤ k) →
        (∀ z, ‖z‖ < 1 → ‖μ z - ν z‖ < δ) →
        ∀ z, ‖z‖ < 1 → ‖sigmaMap μ z - sigmaMap ν z‖ < ε := by
  sorry

/-- The action of `G` on `M`, formula (6.5): `ν = g_*(μ)` iff `g : D_μ → D_ν`
is conformal, expressed via the chain-rule identity for `g ∈ G₊`. -/
def actsOn (g : ℂ → ℂ) (μ ν : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 → μ z = ν (g z) * (star (wirtZ g z) / wirtZ g z)

/-! ### Towards Lemma 4

The proof of Lemma 4 in the paper is: `ν = g_*(μ)` iff `g : D_μ → D_ν` is
conformal, and since `f^μ : D_μ → D_0` and `f^ν : D_ν → D_0` are conformal,
this holds iff `f^ν ∘ g ∘ (f^μ)⁻¹ : D_0 → D_0` is conformal.  In terms of
complex dilatations the substantive direction is the computation below: if
`f^ν ∘ g = h ∘ f^μ` near `z` with `g` and `h` conformal, then taking complex
dilatations of both sides and using `complexDilatation_comp_right` /
`complexDilatation_comp_left` gives exactly (6.5).

The pointwise regularity of `f^μ` — real differentiability with `f_z ≠ 0` at
every point — is not part of `beltramiSolution_existsUnique`, and cannot be:
it fails for some `μ`.  The direction `⇐` therefore takes it as an explicit
hypothesis below.  The direction `⇒` needs only quasiconformality, which the
statement does record. -/


/-- The analytic core of Lemma 4: a conjugacy `Fν ∘ g = h ∘ Fμ` by conformal
maps `g` and `h` forces the complex dilatations to transform by (6.5). -/
theorem dilatation_transform_of_conj (g h Fμ Fν : ℂ → ℂ) (z : ℂ)
    (hgz : DifferentiableAt ℂ g z) (hhz : DifferentiableAt ℂ h (Fμ z))
    (hFμ : DifferentiableAt ℝ Fμ z) (hFν : DifferentiableAt ℝ Fν (g z))
    (hh' : deriv h (Fμ z) ≠ 0) (heq : Fν ∘ g =ᶠ[nhds z] h ∘ Fμ) :
    complexDilatation Fμ z = complexDilatation Fν (g z) * (star (deriv g z) / deriv g z) := by
  have h1 : complexDilatation (Fν ∘ g) z = complexDilatation (h ∘ Fμ) z := by
    unfold complexDilatation wirtZ wirtZbar
    rw [heq.fderiv_eq]
  rw [complexDilatation_comp_right Fν g z hgz hFν,
    complexDilatation_comp_left h Fμ z hFμ hhz hh'] at h1
  exact h1.symm

/-- **Lemma 4, the direction `⇐`**, under the Ahlfors–Bers regularity of `f^μ`
and `f^ν` stated as hypotheses: a conjugacy `f^ν ∘ g = h ∘ f^μ` by elements of
`G₊` implies `ν = g_*(μ)`. -/
theorem actsOn_of_conj (g h μ ν : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) (hν : IsBeltramiCoeff ν)
    (hg : IsDiskAutPlus g)
    (hh : ∀ z : ℂ, ‖z‖ < 1 → DifferentiableAt ℂ h (beltramiSolution μ z))
    (hh' : ∀ z : ℂ, ‖z‖ < 1 → deriv h (beltramiSolution μ z) ≠ 0)
    (hFμ : ∀ z : ℂ, ‖z‖ < 1 → DifferentiableAt ℝ (beltramiSolution μ) z)
    (heqμ : ∀ z : ℂ, ‖z‖ < 1 →
      wirtZbar (beltramiSolution μ) z = μ z * wirtZ (beltramiSolution μ) z)
    (hFμ' : ∀ z : ℂ, ‖z‖ < 1 → wirtZ (beltramiSolution μ) z ≠ 0)
    (hFν : ∀ w : ℂ, ‖w‖ < 1 → DifferentiableAt ℝ (beltramiSolution ν) w)
    (heqν : ∀ w : ℂ, ‖w‖ < 1 →
      wirtZbar (beltramiSolution ν) w = ν w * wirtZ (beltramiSolution ν) w)
    (hFν' : ∀ w : ℂ, ‖w‖ < 1 → wirtZ (beltramiSolution ν) w ≠ 0)
    (hconj : ∀ z : ℂ, ‖z‖ ≤ 1 → beltramiSolution ν (g z) = h (beltramiSolution μ z)) :
    actsOn g μ ν := by
  intro z hz
  have hgd : DifferentiableAt ℂ g z := isDiskAutPlus_differentiableAt g hg z hz
  have hgz : ‖g z‖ < 1 := isDiskAutPlus_mapsTo_disk g hg z hz
  have heq : (beltramiSolution ν ∘ g) =ᶠ[nhds z] (h ∘ beltramiSolution μ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
    exact hconj w (le_of_lt (mem_ball_zero_iff.1 hw))
  have key := dilatation_transform_of_conj g h (beltramiSolution μ) (beltramiSolution ν) z
    hgd (hh z hz) (hFμ z hz) (hFν (g z) hgz) (hh' z hz) heq
  rw [complexDilatation_beltramiSolution μ z (heqμ z hz) (hFμ' z hz),
    complexDilatation_beltramiSolution ν (g z) (heqν (g z) hgz) (hFν' (g z) hgz)] at key
  rw [wirtZ_eq_deriv g z hgd]
  exact key

/-- Lemma 4 `⇐`, with the Ahlfors–Bers regularity carried as `BeltramiRegular`.

It used to be *derived*, from the everywhere nondegeneracy that
`beltramiSolution_existsUnique` then asserted.  That assertion was false
(`no_nondegenerate_solution_cubeMap`), so the regularity is a hypothesis again
— and it has to be: `actsOn` is a pointwise statement about `μ` and `ν`, while
what the corrected theorem supplies holds only a.e.  Nothing downstream uses
this direction of Lemma 4; only `⇒` is consumed, and that goes through
`exists_conj_of_actsOn`. -/
theorem actsOn_of_conj_plus (g h μ ν : ℂ → ℂ) (hμ : IsBeltramiCoeff μ) (hν : IsBeltramiCoeff ν)
    (hg : IsDiskAutPlus g) (hh : IsDiskAutPlus h)
    (hregμ : BeltramiRegular μ) (hregν : BeltramiRegular ν)
    (hconj : ∀ z : ℂ, ‖z‖ ≤ 1 → beltramiSolution ν (g z) = h (beltramiSolution μ z)) :
    actsOn g μ ν :=
  actsOn_of_conj g h μ ν hμ hν hg
    (fun _ hz => isDiskAutPlus_differentiableAt h hh _ (beltramiSolution_mem_disk μ hμ hz))
    (fun _ hz => deriv_isDiskAutPlus_ne_zero h hh (beltramiSolution_mem_disk μ hμ hz).le)
    (fun _ hz => differentiableAt_beltramiSolution hregμ hz)
    (fun z hz => (hregμ z hz).1)
    (fun z hz => (hregμ z hz).2)
    (fun _ hw => differentiableAt_beltramiSolution hregν hw)
    (fun w hw => (hregν w hw).1)
    (fun w hw => (hregν w hw).2)
    hconj

/-- The conjugating element of `G` in Lemma 4 is automatically orientation
preserving: `isDiskAutPlus_of_conj` at `f^μ`, `f^ν`, whose dilatations have
modulus `< 1` by hypothesis. -/
theorem isDiskAutPlus_of_conj_beltrami (g h μ ν : ℂ → ℂ)
    (hμ : IsBeltramiCoeff μ) (hν : IsBeltramiCoeff ν)
    (hg : IsDiskAutPlus g) (hh : IsDiskAut h)
    (hregμ : BeltramiRegular μ) (hregν : BeltramiRegular ν)
    (hconj : ∀ z : ℂ, ‖z‖ ≤ 1 → beltramiSolution ν (g z) = h (beltramiSolution μ z)) :
    IsDiskAutPlus h := by
  have hz0 : ‖(0:ℂ)‖ < 1 := by norm_num
  have hg0 : ‖g 0‖ < 1 := isDiskAutPlus_mapsTo_disk g hg 0 hz0
  exact isDiskAutPlus_of_conj g h (beltramiSolution μ) (beltramiSolution ν) hg hh
    (differentiableAt_beltramiSolution hregμ hz0)
    (differentiableAt_beltramiSolution hregν hg0)
    (beltramiSolution_mem_disk μ hμ hz0)
    (norm_wirtZbar_lt_norm_wirtZ_beltramiSolution hμ hregμ hz0)
    (norm_wirtZbar_lt_norm_wirtZ_beltramiSolution hν hregν hg0)
    hconj

section Lemma4Forward
open Metric Filter
open scoped ComplexConjugate

/-- `f^m(D) = D`, from the existing spec only. -/
theorem beltramiSolution_image_disc (m : ℂ → ℂ) (hm : IsBeltramiCoeff m) :
    beltramiSolution m '' LiZhongQC.unitDisc = LiZhongQC.unitDisc := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact mem_ball_zero_iff.2 (beltramiSolution_mem_disk m hm (mem_ball_zero_iff.1 hz))
  · intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    obtain ⟨z, hz, hzw⟩ :=
      (beltramiSolution_bijOn m hm).surjOn (mem_closedBall_zero_iff.2 hw1.le)
    refine ⟨z, ?_, hzw⟩
    rcases (mem_closedBall_zero_iff.1 hz).lt_or_eq with h | h
    · exact mem_ball_zero_iff.2 h
    · exfalso
      have h1 : ‖beltramiSolution m z‖ = 1 :=
        (beltramiSolution_spec m hm).2.2.2.2.2.2 ⟨z, mem_sphere_zero_iff_norm.2 h⟩
      rw [hzw] at h1
      linarith

/-- An element of `G₊` is a conformal automorphism of `D` in Li Zhong's sense. -/
theorem isDiskAutPlus_isConformalOnto (g : ℂ → ℂ) (hg : IsDiskAutPlus g) :
    LiZhongQC.IsConformalOnto g LiZhongQC.unitDisc LiZhongQC.unitDisc := by
  obtain ⟨lam, a, hlam, ha, hform⟩ := hg
  have hrot := AhlforsBers.isConformalOnto_rot (a := conj lam) (by rw [Complex.norm_conj, hlam])
  simp only [Complex.conj_conj] at hrot
  have hgfun : g = (fun w => lam * w) ∘ LiZhongQC.blaschke a := funext fun z => hform z
  rw [hgfun]
  exact hrot.comp (LiZhongQC.isConformalOnto_blaschke ha)

/-- **Lemma 4, the direction `⇒`**.  Given `ν = g_*(μ)`, the map
`h = f^ν ∘ g ∘ (f^μ)⁻¹` has vanishing dilatation, hence is conformal, hence
belongs to `G₊`.

The three inputs this used to lack — the inverse of `f^μ` with its regularity,
Weyl's lemma, and the classification of the conformal bijections of `D` — all
come from `lizhong_quasiconformal_teichmuller`.  `f^μ` and `f^ν ∘ g` are both
`L²` generalized homeomorphic solutions for `μ` (`beltramiSolution_isKQC` and
`thm10_2_genHomeoSolution_of_isKQC`, with the dilatation of `f^ν ∘ g` pulled back
through `g` by `t1_ae_transport`); by the similarity principle, which contains
Weyl's lemma, they differ by a conformal self-map of `D`
(`same_dilatation_conformal`); and that map is `c · diskAut a`
(`exists_rotation_blaschke_of_isConformalOnto_unitDisc`).  The identity on `D`
extends to `D̄` by continuity.

Stated with `IsDiskAutPlus h` rather than `IsDiskAut h`, which is what the
classification actually gives and what the users of Lemma 4 need. -/
theorem exists_conj_of_actsOn (g : ℂ → ℂ) (hg : IsDiskAutPlus g) (μ ν : ℂ → ℂ)
    (hμ : IsBeltramiCoeff μ) (hν : IsBeltramiCoeff ν) (hact : actsOn g μ ν) :
    ∃ h : ℂ → ℂ, IsDiskAutPlus h ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → beltramiSolution ν (g z) = h (beltramiSolution μ z) := by
  obtain ⟨Kμ, hKμ⟩ := beltramiSolution_isKQC μ hμ
  obtain ⟨Kν, hKν⟩ := beltramiSolution_isKQC ν hν
  have hD : IsOpen LiZhongQC.unitDisc := isOpen_ball
  have hDm : MeasurableSet LiZhongQC.unitDisc := measurableSet_ball
  obtain ⟨hμm, k, hk, hkb⟩ := id hμ
  have hμLZ : LiZhongQC.IsBeltramiCoeff μ LiZhongQC.unitDisc k := by
    refine ⟨hμm.aestronglyMeasurable, ?_⟩
    rw [ae_restrict_iff' hDm]
    exact Filter.Eventually.of_forall fun z hz => hkb z (mem_ball_zero_iff.1 hz)
  have hgconf := isDiskAutPlus_isConformalOnto g hg
  -- a.e. dilatation of `f^m`, from the existing spec
  have hdil : ∀ m : ℂ → ℂ, IsBeltramiCoeff m →
      ∀ᵐ w ∂(volume.restrict LiZhongQC.unitDisc),
        LiZhongQC.complexDilatation (beltramiSolution m) w = m w ∧
          DifferentiableAt ℝ (beltramiSolution m) w := by
    intro m hm
    rw [ae_restrict_iff' hDm]
    filter_upwards [beltramiSolution_beltramiEq_ae m hm, beltramiSolution_wirtZ_ne_zero_ae m hm]
      with w h1 h2 hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    exact ⟨complexDilatation_beltramiSolution m w (h1 hw1) (h2 hw1),
      differentiableAt_of_wirtZ_ne_zero (h2 hw1)⟩
  -- `f^ν ∘ g` is q.c. with dilatation `μ` a.e.
  have hFK : LiZhongQC.IsKQC (beltramiSolution ν ∘ g) LiZhongQC.unitDisc (1 * Kν) :=
    LiZhongQC.thm7_1_comp (LiZhongQC.isKQC_one_of_conformal hD hgconf) hKν hgconf.2.2.le
  have hpull := LiZhongQC.t1_ae_transport hD hD hgconf (hdil ν hν)
  have hFd : ∀ᵐ z ∂(volume.restrict LiZhongQC.unitDisc),
      LiZhongQC.complexDilatation (beltramiSolution ν ∘ g) z = μ z := by
    filter_upwards [hpull, ae_restrict_mem hDm] with z hz' hz
    obtain ⟨h1, h2⟩ := hz'
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    have hgd := isDiskAutPlus_differentiableAt g hg z hz1
    show complexDilatation (beltramiSolution ν ∘ g) z = μ z
    rw [complexDilatation_comp_right _ g z hgd h2, hact z hz1, wirtZ_eq_deriv g z hgd]
    exact congrArg (· * (star (deriv g z) / deriv g z)) h1
  have hFgen : LiZhongQC.IsGenHomeoSolution (beltramiSolution ν ∘ g) μ LiZhongQC.unitDisc 2 := by
    obtain ⟨-, hh, g', h', hp, heq⟩ := LiZhongQC.thm10_2_genHomeoSolution_of_isKQC hFK
    exact ⟨hh, g', h', hp, by
      filter_upwards [heq, hFd] with z ha hb
      rw [hb] at ha
      exact ha⟩
  have hfgen : LiZhongQC.IsGenHomeoSolution (beltramiSolution μ) μ LiZhongQC.unitDisc 2 := by
    obtain ⟨-, hh, g', h', hp, heq⟩ := LiZhongQC.thm10_2_genHomeoSolution_of_isKQC hKμ
    exact ⟨hh, g', h', hp, by
      filter_upwards [heq, hdil μ hμ] with z ha hb
      rw [hb.1] at ha
      exact ha⟩
  -- similarity principle + classification of Aut(D)
  obtain ⟨φ, hφ, hφeq⟩ := LiZhongQC.same_dilatation_conformal hD hk hμLZ hfgen hFgen
  rw [beltramiSolution_image_disc μ hμ, image_comp, hgconf.2.2, beltramiSolution_image_disc ν hν] at hφ
  obtain ⟨c, a', hc, ha', hφb⟩ := LiZhongQC.exists_rotation_blaschke_of_isConformalOnto_unitDisc hφ
  have hh : IsDiskAutPlus (fun z => c * diskAut a' z) := ⟨c, a', hc, ha', fun z => rfl⟩
  refine ⟨fun z => c * diskAut a' z, hh, ?_⟩
  -- equality on `D`
  have hDeq : EqOn (beltramiSolution ν ∘ g) ((fun z => c * diskAut a' z) ∘ beltramiSolution μ)
      (ball (0 : ℂ) 1) := fun z hz => by
    rw [hφeq z hz]
    have hmem : beltramiSolution μ z ∈ LiZhongQC.unitDisc := by
      rw [← beltramiSolution_image_disc μ hμ]; exact mem_image_of_mem _ hz
    exact hφb hmem
  -- extension to `D̄` by continuity
  have hgmaps : MapsTo g (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    obtain ⟨lam, a, hlam, ha, hform⟩ := hg
    intro z hz
    rw [mem_closedBall_zero_iff, hform z, norm_mul, hlam, one_mul]
    exact diskAut_norm_le_one a z ha (mem_closedBall_zero_iff.1 hz)
  have hgc : ContinuousOn g (closedBall (0 : ℂ) 1) := by
    have := (isDiskAutPlus_diffContOnCl g hg).continuousOn
    rwa [closure_ball (0 : ℂ) one_ne_zero] at this
  have hhc : ContinuousOn (fun z => c * diskAut a' z) (closedBall (0 : ℂ) 1) := by
    have := (isDiskAutPlus_diffContOnCl _ hh).continuousOn
    rwa [closure_ball (0 : ℂ) one_ne_zero] at this
  have hc1 : ContinuousOn (beltramiSolution ν ∘ g) (closedBall (0 : ℂ) 1) :=
    (beltramiSolution_continuousOn ν hν).comp hgc hgmaps
  have hc2 : ContinuousOn ((fun z => c * diskAut a' z) ∘ beltramiSolution μ)
      (closedBall (0 : ℂ) 1) :=
    hhc.comp (beltramiSolution_continuousOn μ hμ) (beltramiSolution_bijOn μ hμ).mapsTo
  have hall := hDeq.of_subset_closure hc1 hc2 ball_subset_closedBall
    (closure_ball (0 : ℂ) one_ne_zero).symm.subset
  intro z hz
  exact hall (mem_closedBall_zero_iff.2 hz)

end Lemma4Forward

/-- **Lemma 4**: `ν = g_*(μ)` iff `f^ν ∘ g ∘ (f^μ)⁻¹ ∈ G`.

Both of the inputs the previous statement of this theorem listed as missing are
now supplied.  The Ahlfors–Bers regularity is derived rather than assumed
(`actsOn_of_conj_plus`), and the orientation of `h` is *proved*
(`isDiskAutPlus_of_conj_beltrami`) from the mirror of
`complexDilatation_comp_left` that the old docstring asked for.  The direction
`⇒` is `exists_conj_of_actsOn`, proved.

The hypotheses `hregμ`, `hregν` are used only by `⇐`.  `BeltramiRegular` asks
for `f_z ≠ 0` at *every* point of `D`, which fails for some `μ`
(`no_nondegenerate_solution_cubeMap`), so the equivalence as a whole is
conditional on them; `⇒` alone is unconditional. -/
theorem lemma4_conj_iff (g : ℂ → ℂ) (hg : IsDiskAutPlus g) (μ ν : ℂ → ℂ)
    (hμ : IsBeltramiCoeff μ) (hν : IsBeltramiCoeff ν)
    (hregμ : BeltramiRegular μ) (hregν : BeltramiRegular ν) :
    actsOn g μ ν ↔
      ∃ h : ℂ → ℂ, IsDiskAut h ∧
        ∀ z : ℂ, ‖z‖ ≤ 1 → beltramiSolution ν (g z) = h (beltramiSolution μ z) := by
  constructor
  · intro hact
    obtain ⟨h, hh, hconj⟩ := exists_conj_of_actsOn g hg μ ν hμ hν hact
    exact ⟨h, Or.inl hh, hconj⟩
  · rintro ⟨h, hh, hconj⟩
    exact actsOn_of_conj_plus g h μ ν hμ hν hg
      (isDiskAutPlus_of_conj_beltrami g h μ ν hμ hν hg hh hregμ hregν hconj)
      hregμ hregν hconj

/-- **Corollary to Lemma 4**: `σ : M → M` is conformally natural.

The argument is the paper's, and the two halves it needs are both here.

*From `f` to `E`.*  Lemma 4 turns `ν = g_*(μ)` into a conjugacy
`f^ν ∘ g = h ∘ f^μ` on `D̄` (hypothesis `hconjf`).  Restricting to `S¹` gives
`φ^ν ∘ ψ_g = ψ_h ∘ φ^μ`, and conformal naturality of `E` promotes that back to
`E(φ^ν) ∘ g = h ∘ E(φ^μ)`.  The promotion needs `extension_naturality` only in
its two degenerate cases — once with the outer automorphism the identity, once
with the inner one — which is what avoids having to invert `g` inside the
extension.

*From `E` to `σ`.*  Taking complex dilatations of that conjugacy is
`dilatation_transform_of_conj`, and by definition `σ(μ) = μ(E(φ^μ))`, so the
result is exactly `actsOn g (σ μ) (σ ν)`.

The input `hconjf` with `IsDiskAutPlus h` is exactly what Lemma 4 `⇒`
(`exists_conj_of_actsOn`) supplies.  Two further inputs this theorem
used to carry are gone: surjectivity of `φ^μ` is `beltramiBoundary_surjective`,
and real differentiability of `Φ` is `differentiableAt_extension`. -/
theorem sigmaMap_naturality (g : ℂ → ℂ) (hg : IsDiskAutPlus g) (μ ν : ℂ → ℂ)
    (hμ : IsBeltramiCoeff μ) (hν : IsBeltramiCoeff ν)
    (h : ℂ → ℂ) (hh : IsDiskAutPlus h)
    (hconjf : ∀ z : ℂ, ‖z‖ ≤ 1 → beltramiSolution ν (g z) = h (beltramiSolution μ z)) :
    actsOn g (sigmaMap μ) (sigmaMap ν) := by
  set ψg := diskAutToCircle g (Or.inl hg) with hψg
  set ψh := diskAutToCircle h (Or.inl hh) with hψh
  have hbijμ : Function.Bijective (beltramiBoundary μ) := beltramiBoundary_bijective μ hμ
  have hbijν : Function.Bijective (beltramiBoundary ν) := beltramiBoundary_bijective ν hν
  have hcontμ : Continuous (beltramiBoundary μ) := beltramiBoundary_continuous μ hμ
  have hcontν : Continuous (beltramiBoundary ν) := beltramiBoundary_continuous ν hν
  have hbψg : Function.Bijective ψg := bijective_diskAutToCircle g hg _
  have hbψh : Function.Bijective ψh := bijective_diskAutToCircle h hh _
  have hcomp : (beltramiBoundary ν) ∘ ψg = ψh ∘ (beltramiBoundary μ) := by
    funext ζ
    refine Subtype.ext ?_
    show ((beltramiBoundary ν (ψg ζ) : Circle) : ℂ) = h ((beltramiBoundary μ ζ : Circle) : ℂ)
    rw [beltramiBoundary_coe ν hν, beltramiBoundary_coe μ hμ]
    exact hconjf (ζ : ℂ) (by simp)
  have hA : ∀ w : ℂ, ‖w‖ ≤ 1 →
      extension ((id : Circle → Circle) ∘ (beltramiBoundary ν) ∘ ψg) w
        = id (extension (beltramiBoundary ν) (g w)) :=
    fun w hw => extension_naturality (beltramiBoundary ν) id g id ψg
      (Or.inl isDiskAutPlus_id) (Or.inl hg) (fun _ => rfl) (fun _ => rfl)
      hbijν hcontν Function.bijective_id hbψg w hw
  have hB : ∀ w : ℂ, ‖w‖ ≤ 1 →
      extension (ψh ∘ (beltramiBoundary μ) ∘ (id : Circle → Circle)) w
        = h (extension (beltramiBoundary μ) (id w)) :=
    fun w hw => extension_naturality (beltramiBoundary μ) h id ψh id
      (Or.inl hh) (Or.inl isDiskAutPlus_id) (fun _ => rfl) (fun _ => rfl)
      hbijμ hcontμ hbψh Function.bijective_id w hw
  have hconjE : ∀ w : ℂ, ‖w‖ ≤ 1 →
      extension (beltramiBoundary ν) (g w) = h (extension (beltramiBoundary μ) w) := by
    intro w hw
    have h1 := hA w hw
    have h2 := hB w hw
    simp only [Function.id_comp, Function.comp_id, id_eq] at h1 h2
    rw [← h1, ← h2, hcomp]
  intro z hz
  have hgd : DifferentiableAt ℂ g z := isDiskAutPlus_differentiableAt g hg z hz
  have hgz : ‖g z‖ < 1 := isDiskAutPlus_mapsTo_disk g hg z hz
  have hΦμ : ‖extension (beltramiBoundary μ) z‖ < 1 :=
    extension_mem_disk _ hbijμ hcontμ z hz
  have heqf : (extension (beltramiBoundary ν)) ∘ g
      =ᶠ[nhds z] h ∘ (extension (beltramiBoundary μ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
    exact hconjE w (le_of_lt (mem_ball_zero_iff.1 hw))
  have key := dilatation_transform_of_conj g h (extension (beltramiBoundary μ))
      (extension (beltramiBoundary ν)) z hgd
      (isDiskAutPlus_differentiableAt h hh _ hΦμ)
      (differentiableAt_extension _ hbijμ hcontμ z hz)
      (differentiableAt_extension _ hbijν hcontν (g z) hgz)
      (deriv_isDiskAutPlus_ne_zero h hh hΦμ.le) heqf
  rw [wirtZ_eq_deriv g z hgd]
  exact key

end
