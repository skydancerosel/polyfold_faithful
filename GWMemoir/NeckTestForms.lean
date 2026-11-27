import GWMemoir.LinearCRNodesDense
import GWMemoir.LinearCRNodesEstimate

/-!
# The neck test forms, and `D` Fredholm and onto at a constant map from two spheres

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Proposition 4.23,
p. 118, level `0`, `a = 0`), at the constant map `u ≡ q` from two spheres joined at a node
(`twoSpheres`), with `0 < δ₀ < 2π`.

* `neckFormN J₀ φ c`: the form `y ↦ (v ↦ conj(dφ(y) v) · c(φ y))` on the source of a holomorphic
  chart `φ` (`·` the action of `ℂ` through `J₀`), `0` off it; it is anti-linear
  (`neckFormN_mem`), and in the polar coordinates of `φ` it reads
  `ξ(σ)(∂_s σ) = conj(-2π ζ) · c(ζ)`, `ζ = e^{-2π(s+it)}` (`formInPolar_neckFormN`).
* `neckCoef J₀ F ζ = conj((-2πζ)⁻¹) · F(log ζ)`, `F` periodic in `t`: smooth on `ℂ` when `F`
  is smooth and vanishes for large `s` (`contDiff_neckCoef`), and the polar value of the
  corresponding form is `F` (`cmulL_neckCoef`).
* `contDiff_testTermX`, `contDiff_neckTerm`: the disc test terms `ρ_i · testForm φ i` and the neck
  terms `χ_j · neckFormN`, read along any smooth map `τ : ℂ → S`, are smooth; with `mfderiv_sumInl`
  this gives the smoothness of the glued forms in both holomorphic charts of each sphere
  (`isSphereSmooth_two_of_along`).
* **`neckTestForms_of_glueCharts`**: `NeckTestForms J F` for every atlas of the constant map from
  `twoSpheres` with `GlueCharts A` and all gluing data `F`.
* **`linCRN_isFredholm_twoSpheres_of_glueCharts`**: on such an atlas with the standard neck charts,
  `D` is Fredholm and onto, of index `dim E`.
* **`linCRN_isFredholm_twoSpheres_uncond`**: for every `J`, `q` and `0 < δ₀ < 2π` there are an atlas
  and gluing data on which `D` is Fredholm and onto, of index `dim E`, with `ker D ≅ E`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The disc test terms along a smooth map, on any nodal surface -/

section Along

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {m : ℕ} {X : NodalSurface m} {q : Q} (A : SectionAtlas (E := E) X (fun _ => q))

/-- The derivative of a map `ℂ → S` read in the chart of `S` at `c`. -/
lemma tcc_mfderivX {τ : ℂ → X.S} (hτ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ τ) (c : X.S) {z : ℂ}
    (hz : τ z ∈ (chartAt E2 c).source) (w : ℂ) :
    tangentCoordChange 𝓘(ℝ, E2) (τ z) c (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z w) =
      fderiv ℝ (fun z => chartAt E2 c (τ z)) z w := by
  have hc : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) (chartAt E2 c) (τ z) :=
    mdifferentiableAt_atlas (ChartedSpace.chart_mem_atlas _) hz
  have h := mfderiv_comp z hc ((hτ z).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, mfderiv_chartAt_eq_tangentCoordChange hz] at h
  exact (congrArg (fun L => L w) h).symm

/-- The value of a test form on a tangent vector. -/
lemma testForm_applyX (φ : Ix A → ℝ × ℝ → ℝ) (j : Fin A.nd) (y : X.S) (v : E2) :
    testForm A φ j y v =
      (discCut (stripPt (A.center j) (A.ε j) y))⁻¹ •
        (Module.finBasis ℝ E).equivFun.symm fun k => ∑ d' : Fin 2,
          φ (j, d', k) (stripPt (A.center j) (A.ε j) y) *
            (tangentCoordChange 𝓘(ℝ, E2) y (A.center j) y v) d' := by
  simp only [testForm, ContinuousLinearMap.comp_apply, smul_apply,
    LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
  congr 2

/-- **One term of the test forms, read along a smooth map `τ : ℂ → S`, is smooth** (as
`contDiff_testTerm`, on any nodal surface). -/
theorem contDiff_testTermX {τ : ℂ → X.S} (hτ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ τ)
    (φ : Ix A → ℝ × ℝ → ℝ) (hφ : ∀ o, ContDiff ℝ ∞ (φ o)) (j : Fin A.nd)
    {ρ : X.S → ℝ} (hρs : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ) ∞ ρ)
    (hρ : tsupport ρ ⊆ discSet (A.center j) (A.ε j)) (w : ℂ) :
    ContDiff ℝ ∞ fun z => ρ (τ z) • testForm A φ j (τ z)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z w) := by
  let c : X.S := A.center j
  let ε := A.ε j
  let V : Set ℂ := τ ⁻¹' discSet (X := X) c ε
  have hVo : IsOpen V := (isOpen_discSet (X := X) c ε).preimage hτ.continuous
  have hVs : ∀ z ∈ V, τ z ∈ (chartAt E2 c).source := fun z hz => by
    have := hz.1; rwa [extChartAt_source] at this
  let ψ : ℂ → E2 := fun z => chartAt E2 c (τ z)
  have hψ : ContDiffOn ℝ ∞ ψ V := fun z hz => by
    have h1 := (contMDiffAt_extChartAt' (I := 𝓘(ℝ, E2)) (n := ∞) (M := X.S) (x := c)
      (hVs z hz)).comp z (hτ z)
    exact (contMDiffAt_iff_contDiffAt.1 h1).contDiffWithinAt
  have hψ' : ContDiffOn ℝ ∞ (fun z => fderiv ℝ ψ z w) V :=
    ((hψ.fderiv_of_isOpen hVo (by simp)).clm_apply contDiffOn_const)
  rw [contDiff_iff_contDiffAt]
  intro z₀
  by_cases h₀ : τ z₀ ∈ tsupport ρ
  swap
  · have hopen : IsOpen {z | τ z ∉ tsupport ρ} :=
      (isClosed_tsupport ρ).isOpen_compl.preimage hτ.continuous
    refine contDiffAt_const (c := (0 : E)).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds h₀] with z hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  have hz₀ : z₀ ∈ V := hρ h₀
  have hV : V ∈ 𝓝 z₀ := hVo.mem_nhds hz₀
  have hρc : ContDiff ℝ ∞ fun z => ρ (τ z) := contMDiff_iff_contDiff.1 (hρs.comp hτ)
  have hpl : ContDiffAt ℝ ∞ (fun z => placeInv (X := X) c ε (ψ z)) z₀ :=
    (contDiff_placeInv (X := X) c ε).contDiffAt.comp z₀ (hψ.contDiffAt hV)
  have hcut : discCut (placeInv (X := X) c ε (ψ z₀)) ≠ 0 := by
    have h : placeInv (X := X) c ε (ψ z₀) ∈ discD := hz₀.2
    exact (discCut_pos h).ne'
  have hsum : ContDiffAt ℝ ∞ (fun z => (Module.finBasis ℝ E).equivFun.symm fun k =>
      ∑ d' : Fin 2, φ (j, d', k) (placeInv (X := X) c ε (ψ z)) *
        (fderiv ℝ ψ z w) d') z₀ := by
    refine (LinearMap.toContinuousLinearMap
      (Module.finBasis ℝ E).equivFun.symm.toLinearMap).contDiff.contDiffAt.comp z₀ ?_
    refine contDiffAt_pi.2 fun k => ContDiffAt.sum fun d' _ => ?_
    exact ((hφ _).contDiffAt.comp z₀ hpl).mul
      ((EuclideanSpace.proj d' : E2 →L[ℝ] ℝ).contDiff.contDiffAt.comp z₀
        (hψ'.contDiffAt hV))
  have hmain : ContDiffAt ℝ ∞ (fun z => ρ (τ z) •
      ((discCut (placeInv (X := X) c ε (ψ z)))⁻¹ •
        (Module.finBasis ℝ E).equivFun.symm fun k =>
          ∑ d' : Fin 2, φ (j, d', k) (placeInv (X := X) c ε (ψ z)) *
            (fderiv ℝ ψ z w) d')) z₀ :=
    hρc.contDiffAt.smul (((contDiff_discCut.contDiffAt.comp z₀ hpl).inv hcut).smul hsum)
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [hV] with z hz
  refine congrArg (ρ (τ z) • ·) ((testForm_applyX A φ j (τ z) _).trans ?_)
  erw [tcc_mfderivX hτ (A.center j) (hVs z hz) w]
  rfl

end Along

/-! ## 2. The neck forms -/

section NeckForm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {m : ℕ} {X : NodalSurface m}

/-- The real-linear map `a ↦ ā · e`, `·` the action of `ℂ` through `J₀`. -/
def conjMulL (J₀ : E →L[ℝ] E) (e : E) : ℂ →L[ℝ] E :=
  ((cmulL J₀).flip e).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)

lemma conjMulL_apply (J₀ : E →L[ℝ] E) (e : E) (a : ℂ) :
    conjMulL J₀ e a = cmulL J₀ ((starRingEnd ℂ) a) e := rfl

open Classical in
/-- **The neck form of `c` in the chart `φ`**: `y ↦ (v ↦ conj(dφ(y) v) · c(φ y))` on the source
of `φ`, `0` off it. -/
def neckFormN (J₀ : E →L[ℝ] E) (φ : OpenPartialHomeomorph X.S ℂ) (c : ℂ → E) : Form E X :=
  fun y => if y ∈ φ.source then (conjMulL J₀ (c (φ y))).comp (dChart φ y) else 0

lemma neckFormN_apply_of_mem (J₀ : E →L[ℝ] E) {φ : OpenPartialHomeomorph X.S ℂ} (c : ℂ → E)
    {y : X.S} (hy : y ∈ φ.source) (v : E2) :
    neckFormN J₀ φ c y v = cmulL J₀ ((starRingEnd ℂ) (dChart φ y v)) (c (φ y)) := by
  simp only [neckFormN, hy, if_true]
  rfl

/-- **The neck forms are anti-linear**, for `J₀ = J(q)` and a holomorphic chart `φ`. -/
theorem neckFormN_mem (J : AlmostComplexStructure E Q) {q : Q} {φ : OpenPartialHomeomorph X.S ℂ}
    {x : X.S} (hφ : X.IsHolChart φ x) (c : ℂ → E) (y : X.S) :
    neckFormN (J.J q) φ c y ∈ X.antiLinearForms J q y := by
  refine (NodalSurface.mem_antiLinearForms J X).2 fun v => ?_
  by_cases hy : y ∈ φ.source
  · rw [neckFormN_apply_of_mem _ c hy, neckFormN_apply_of_mem _ c hy]
    have hj : dChart φ y (X.j.J y v) = Complex.I * dChart φ y v := (hφ.2.2 y hy).2 v
    have key : ∀ (b : ℂ) (e : E), J.J q (cmulL (J.J q) b e) = cmulL (J.J q) (Complex.I * b) e :=
      fun b e => by rw [cmulL_mul (acs_sq J q), cmulL_apply (J.J q) Complex.I]; simp
    have hc : (starRingEnd ℂ) (Complex.I * dChart φ y v) =
        -(Complex.I * (starRingEnd ℂ) (dChart φ y v)) := by
      rw [map_mul, Complex.conj_I]; ring
    rw [hj, hc, map_neg, neg_apply, neg_neg, key]
  · simp [neckFormN, hy]

/-- `∂_s e^{-2π(s+it)} = -2π e^{-2π(s+it)}`. -/
lemma fderiv_expPolar_one_zero (p : ℝ × ℝ) :
    fderiv ℝ expPolar p (1, 0) = -2 * Real.pi * expPolar p := by
  have hf : HasFDerivAt (fun p : ℝ × ℝ => (-2 * Real.pi : ℂ) *
      (Complex.ofRealCLM p.1 + Complex.ofRealCLM p.2 * Complex.I))
      ((-2 * Real.pi : ℂ) • ((Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
        Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)))) p :=
    (((Complex.ofRealCLM.hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ))).add
      ((Complex.ofRealCLM.hasFDerivAt.comp p (hasFDerivAt_snd (𝕜 := ℝ))).mul_const
        Complex.I)).const_mul (-2 * Real.pi : ℂ))
  have h := hf.cexp
  have e : (fun p : ℝ × ℝ => Complex.exp ((-2 * Real.pi : ℂ) *
      (Complex.ofRealCLM p.1 + Complex.ofRealCLM p.2 * Complex.I))) = expPolar := by
    funext p; simp [expPolar]
  rw [e] at h
  rw [h.fderiv]
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Complex.ofRealCLM_apply, smul_eq_mul]
  simp only [expPolar, Complex.ofReal_one, Complex.ofReal_zero]
  ring

variable {q : Q}

/-- **The neck form in the polar coordinates of its chart**:
`ξ(σ(p))(∂_s σ(p)) = conj(-2π ζ) · c(ζ)`, `ζ = e^{-2π(s+it)}`. -/
theorem formInPolar_neckFormN {φ : OpenPartialHomeomorph X.S ℂ} {x : X.S}
    (hφ : X.IsHolChart φ x) (ht : φ.target = univ)
    (hsm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ φ.symm) (J₀ : E →L[ℝ] E) (c : ℂ → E) (p : ℝ × ℝ) :
    X.formInPolar (fun _ => q) (neckFormN J₀ φ c) φ x p =
      cmulL J₀ ((starRingEnd ℂ) (-2 * Real.pi * expPolar p)) (c (expPolar p)) := by
  have hp : expPolar p ∈ φ.target := by rw [ht]; trivial
  have hy : X.polar φ p ∈ φ.source := X.polar_mem_source hp
  have hφp : φ (X.polar φ p) = expPolar p := by rw [NodalSurface.polar_eq]; exact φ.right_inv hp
  have hsmA : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) φ.symm (expPolar p) :=
    hsm.mdifferentiable (by simp) _
  have hpol := (polar_deriv hφ hp hsmA).1
  have hφd : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) φ (X.polar φ p) := (hφ.2.2 _ hy).1
  have hcomp : ((φ : X.S → ℂ) ∘ X.polar φ) = expPolar := by
    funext p'
    exact φ.right_inv (by rw [ht]; trivial)
  have hd : dChart φ (X.polar φ p) (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar φ) p (1, 0)) =
      -2 * Real.pi * expPolar p := by
    have h := mfderiv_comp p hφd hpol
    rw [hcomp, mfderiv_eq_fderiv] at h
    rw [← fderiv_expPolar_one_zero p]
    exact (congrArg (fun L => L (1, 0)) h).symm
  simp only [NodalSurface.formInPolar]
  rw [tcc_const]
  erw [neckFormN_apply_of_mem _ c hy]
  rw [hd, hφp]

/-- **The neck terms along a smooth map are smooth**: for `χ = g(|φ|²)` and `c` smooth on `ℂ`,
`z ↦ χ(τ z) · ξ(τ z)(dτ(z) w)` is smooth for every smooth `τ : ℂ → S`. -/
theorem contDiff_neckTerm {φ : OpenPartialHomeomorph X.S ℂ} (ht : φ.target = univ)
    (hsm : ∀ y ∈ φ.source, ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) ∞ φ y) (hsym : Continuous φ.symm)
    (s₀ : ℝ) (J₀ : E →L[ℝ] E) {c : ℂ → E} (hc : ContDiff ℝ ∞ c)
    {τ : ℂ → X.S} (hτ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ τ) (w : ℂ) :
    ContDiff ℝ ∞ fun z => chiSN φ s₀ (τ z) • neckFormN J₀ φ c (τ z)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z w) := by
  rw [contDiff_iff_contDiffAt]
  intro z₀
  by_cases h₀ : τ z₀ ∈ tsupport (chiSN φ s₀)
  swap
  · have hopen : IsOpen {z | τ z ∉ tsupport (chiSN φ s₀)} :=
      (isClosed_tsupport _).isOpen_compl.preimage hτ.continuous
    refine contDiffAt_const (c := (0 : E)).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds h₀] with z hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  have hz₀ : τ z₀ ∈ φ.source := zSet_sub ht (tsupport_chiSN_sub hsym h₀)
  let V : Set ℂ := τ ⁻¹' φ.source
  have hVo : IsOpen V := φ.open_source.preimage hτ.continuous
  let g : ℂ → ℂ := fun z => φ (τ z)
  have hg : ContDiffOn ℝ ∞ g V := fun z hz =>
    (contMDiffAt_iff_contDiffAt.1 ((hsm _ hz).comp z (hτ z))).contDiffWithinAt
  have hg' : ContDiffOn ℝ ∞ (fun z => fderiv ℝ g z w) V :=
    (hg.fderiv_of_isOpen hVo (by simp)).clm_apply contDiffOn_const
  have hV : V ∈ 𝓝 z₀ := hVo.mem_nhds hz₀
  have hχ : ContDiff ℝ ∞ fun z => chiSN φ s₀ (τ z) :=
    contMDiff_iff_contDiff.1 ((contMDiff_chiSN ht hsym hsm).comp hτ)
  have h1 : ContDiffAt ℝ ∞ (fun z => cmulL J₀ (Complex.conjCLE (fderiv ℝ g z w))) z₀ :=
    (cmulL J₀).contDiff.contDiffAt.comp z₀
      (Complex.conjCLE.contDiff.contDiffAt.comp z₀ (hg'.contDiffAt hV))
  have h2 : ContDiffAt ℝ ∞ (fun z => c (g z)) z₀ := hc.contDiffAt.comp z₀ (hg.contDiffAt hV)
  have hmain : ContDiffAt ℝ ∞ (fun z => chiSN φ s₀ (τ z) •
      cmulL J₀ (Complex.conjCLE (fderiv ℝ g z w)) (c (g z))) z₀ :=
    hχ.contDiffAt.smul (h1.clm_apply h2)
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [hV] with z hz
  have hd : dChart φ (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z w) = fderiv ℝ g z w := by
    have h := mfderiv_comp z ((hsm _ hz).mdifferentiableAt (by simp))
      ((hτ z).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at h
    exact (congrArg (fun L => L w) h).symm
  erw [neckFormN_apply_of_mem _ c hz]
  erw [hd]
  rfl

end NeckForm

/-! ## 3. The coefficient of the neck forms -/

section Coef

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A periodic function of `(s, t)` is invariant under integer shifts of `t`. -/
lemma periodic_intT {F : ℝ × ℝ → E} (hF : ∀ s t, F (s, t + 1) = F (s, t)) (s t : ℝ) (n : ℤ) :
    F (s, t + n) = F (s, t) := by
  have hp : Function.Periodic (fun t => F (s, t)) 1 := fun t => hF s t
  simpa using (hp.int_mul n) t

/-- A periodic function of `(s, t)` read through `log`: `F(log e^{-2π(s+it)}) = F(s, t)`. -/
lemma comp_logE_expPolar {F : ℝ × ℝ → E} (hF : ∀ s t, F (s, t + 1) = F (s, t)) (p : ℝ × ℝ) :
    F (logE (expPolar p)) = F p := by
  obtain ⟨h1, n, h2⟩ := expPolar_injOn (expPolar_logE (expPolar_ne_zero p))
  rw [show logE (expPolar p) = (p.1, p.2 + n) from Prod.ext h1 h2, periodic_intT hF]

/-- **A smooth periodic function read through `log` is smooth off `0`**: on the slit plane through
`log`; across the negative axis through `log(-ζ) + (0, ½)`. -/
lemma contDiffAt_comp_logE {F : ℝ × ℝ → E} (hFs : ContDiff ℝ ∞ F)
    (hF : ∀ s t, F (s, t + 1) = F (s, t)) {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ ∞ (fun w => F (logE w)) w := by
  by_cases hs : w ∈ Complex.slitPlane
  · exact hFs.contDiffAt.comp w (contDiffAt_logE hs)
  have hs' : -w ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff] at hs ⊢
    simp only [not_or, not_lt, ne_eq, not_not] at hs
    left
    have hre : w.re ≠ 0 := fun h => hw (Complex.ext h hs.2)
    simp only [Complex.neg_re]
    exact neg_pos.2 (lt_of_le_of_ne hs.1 hre)
  have e : ∀ w' : ℂ, w' ≠ 0 → F (logE (-w') + (0, 1 / 2)) = F (logE w') := by
    intro w' hw'
    have h : expPolar (logE (-w') + (0, 1 / 2)) = w' := by
      rw [show logE (-w') + ((0 : ℝ), (1 / 2 : ℝ)) = ((logE (-w')).1, (logE (-w')).2 + 1 / 2) by
        ext <;> simp, expPolar_add_half, expPolar_logE (neg_ne_zero.2 hw'), neg_neg]
    have := comp_logE_expPolar hF (logE (-w') + (0, 1 / 2))
    rw [h] at this
    exact this.symm
  refine ContDiffAt.congr_of_eventuallyEq (f := fun w => F (logE (-w) + (0, 1 / 2))) ?_ ?_
  · exact hFs.contDiffAt.comp w
      (((contDiffAt_logE hs').comp w contDiff_neg.contDiffAt).add contDiffAt_const)
  · filter_upwards [isOpen_ne.mem_nhds hw] with w' hw' using (e w' hw').symm

/-- **The coefficient of the neck form with polar value `F`**:
`c(ζ) = conj((-2πζ)⁻¹) · F(log ζ)` (`0` at `ζ = 0`). -/
def neckCoef (J₀ : E →L[ℝ] E) (F : ℝ × ℝ → E) (w : ℂ) : E :=
  cmulL J₀ ((starRingEnd ℂ) (-2 * Real.pi * w)⁻¹) (F (logE w))

lemma two_pi_mul_ne {w : ℂ} (hw : w ≠ 0) : (-2 * Real.pi * w : ℂ) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) hw

/-- **The polar value of the neck form of `neckCoef J₀ F` is `F`**. -/
theorem cmulL_neckCoef {J₀ : E →L[ℝ] E} (hJ : ∀ v, J₀ (J₀ v) = -v) {F : ℝ × ℝ → E}
    (hF : ∀ s t, F (s, t + 1) = F (s, t)) (p : ℝ × ℝ) :
    cmulL J₀ ((starRingEnd ℂ) (-2 * Real.pi * expPolar p)) (neckCoef J₀ F (expPolar p)) = F p := by
  rw [neckCoef, ← cmulL_mul hJ, ← map_mul, mul_inv_cancel₀ (two_pi_mul_ne (expPolar_ne_zero p)),
    map_one, cmulL_one, comp_logE_expPolar hF]

/-- **The coefficient is smooth on `ℂ`** when `F` is smooth, periodic and vanishes for large `s`:
off `0` by `contDiffAt_comp_logE`; near `0` it vanishes. -/
theorem contDiff_neckCoef (J₀ : E →L[ℝ] E) {F : ℝ × ℝ → E} (hFs : ContDiff ℝ ∞ F)
    (hF : ∀ s t, F (s, t + 1) = F (s, t)) (hR : ∃ R, ∀ p : ℝ × ℝ, R < p.1 → F p = 0) :
    ContDiff ℝ ∞ (neckCoef J₀ F) := by
  obtain ⟨R, hR⟩ := hR
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    refine contDiffAt_const (c := (0 : E)).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-2 * Real.pi * R))] with w' hw'
    rw [Metric.mem_ball, dist_zero_right] at hw'
    by_cases h0 : w' = 0
    · subst h0; simp [neckCoef]
    have hlog : Real.log ‖w'‖ < -2 * Real.pi * R := by
      rw [← Real.log_exp (-2 * Real.pi * R)]
      exact Real.log_lt_log (norm_pos_iff.2 h0) hw'
    have hs : R < (logE w').1 := by
      simp only [logE, Complex.log_re]
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    simp [neckCoef, hR _ hs]
  · have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => (-2 * Real.pi * w : ℂ)⁻¹) w :=
      (contDiffAt_inv ℝ (two_pi_mul_ne hw)).comp w (contDiff_const.mul contDiff_id).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun w : ℂ => cmulL J₀ (Complex.conjCLE (-2 * Real.pi * w : ℂ)⁻¹)) w :=
      (cmulL J₀).contDiff.contDiffAt.comp w (Complex.conjCLE.contDiff.contDiffAt.comp w h1)
    exact h2.clm_apply (contDiffAt_comp_logE hFs hF hw)

/-- The weight `ε(s)/β⁺(s - s₀)`, `ε(s) = β⁺(4(s - s₀) - 1)`: smooth, `0` for `s ≤ s₀ + ¼`,
`1/β⁺(s - s₀)` for `s ≥ s₀ + ½`. -/
def neckWt (s₀ s : ℝ) : ℝ :=
  Real.smoothTransition (4 * (s - s₀) - 1) / Real.smoothTransition (s - s₀)

lemma contDiff_neckWt (s₀ : ℝ) : ContDiff ℝ ∞ (neckWt s₀) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  rcases lt_or_ge s₀ s with h | h
  · have hpos : Real.smoothTransition (s - s₀) ≠ 0 :=
      (Real.smoothTransition.pos_of_pos (by linarith)).ne'
    exact (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (contDiff_id.sub contDiff_const)).sub contDiff_const)).contDiffAt.div
      (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt hpos
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (show s < s₀ + 1 / 4 by linarith)] with y hy
    simp only [neckWt]
    rw [Real.smoothTransition.zero_of_nonpos (by rw [mem_Iio] at hy; linarith), zero_div]

lemma smoothTransition_mul_neckWt {s₀ s : ℝ} (hs : s₀ + 1 / 2 ≤ s) :
    Real.smoothTransition (s - s₀) * neckWt s₀ s = 1 := by
  have hpos : 0 < Real.smoothTransition (s - s₀) := Real.smoothTransition.pos_of_pos (by linarith)
  rw [neckWt, Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 4 * (s - s₀) - 1 by linarith)]
  field_simp

variable (E) in
/-- **The polar values of the neck forms**: `F(p) = ∑_k (neckWt s₀ s) γ_k(p) e_k`. -/
def neckVal (s₀ : ℝ) (γ : Fin (Module.finrank ℝ E) → ℝ × ℝ → ℝ) (p : ℝ × ℝ) : E :=
  (Module.finBasis ℝ E).equivFun.symm fun k => neckWt s₀ p.1 * γ k p

lemma crd_neckVal (s₀ : ℝ) (γ : Fin (Module.finrank ℝ E) → ℝ × ℝ → ℝ) (k : Fin (Module.finrank ℝ E))
    (p : ℝ × ℝ) : crd k (neckVal E s₀ γ p) = neckWt s₀ p.1 * γ k p :=
  crd_symm k _

lemma contDiff_neckVal (s₀ : ℝ) {γ : Fin (Module.finrank ℝ E) → ℝ × ℝ → ℝ}
    (hγ : ∀ k, ContDiff ℝ ∞ (γ k)) : ContDiff ℝ ∞ (neckVal E s₀ γ) :=
  (LinearMap.toContinuousLinearMap
    (Module.finBasis ℝ E).equivFun.symm.toLinearMap).contDiff.comp
    (contDiff_pi.2 fun k => ((contDiff_neckWt s₀).comp contDiff_fst).mul (hγ k))

lemma neckVal_periodic (s₀ : ℝ) {γ : Fin (Module.finrank ℝ E) → ℝ × ℝ → ℝ}
    (hγ : ∀ k s t, γ k (s, t + 1) = γ k (s, t)) (s t : ℝ) :
    neckVal E s₀ γ (s, t + 1) = neckVal E s₀ γ (s, t) := by
  simp only [neckVal, hγ]

lemma neckVal_eventually_zero (s₀ : ℝ) {γ : Fin (Module.finrank ℝ E) → ℝ × ℝ → ℝ}
    (hγ : ∀ k, IsTest (γ k)) : ∃ R, ∀ p : ℝ × ℝ, R < p.1 → neckVal E s₀ γ p = 0 := by
  choose R hR using fun k => (hγ k).bddSupp
  refine ⟨∑ k, |R k|, fun p hp => ?_⟩
  have h : ∀ k, γ k p = 0 := fun k => by
    have h1 : R k ≤ ∑ k, |R k| :=
      (le_abs_self _).trans (Finset.single_le_sum (fun k _ => abs_nonneg (R k)) (Finset.mem_univ k))
    obtain ⟨s, t⟩ := p
    exact hR k s t (lt_of_lt_of_le (h1.trans_lt hp) (le_abs_self s))
  simp only [neckVal, h, mul_zero]
  exact map_zero _

end Coef

/-! ## 4. Smoothness on both spheres -/

section Two

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `d(inl ∘ σ_s⁻¹)(z) = Dσ_s⁻¹(z)`. -/
lemma mfderiv_inl_holChart_symm (s : ℝ) (hs : s ^ 2 = 1) (z : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) (fun z => (Sum.inl ((holChart s hs).symm z) : S22)) z =
      DtauS s hs z := by
  have hinl : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) (@Sum.inl S2 S2) ((holChart s hs).symm z) :=
    ((ContMDiff.inl (I := 𝓘(ℝ, E2)) (M := S2) (M' := S2) (n := ∞)).mdifferentiable
      (by simp) _)
  have h := mfderiv_comp z hinl (mdifferentiable_holChart_symm s hs z)
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) (Sum.inl ∘ (holChart s hs).symm) z = _
  rw [h, mfderiv_sumInl (p := Sum.inl ((holChart s hs).symm z))]
  rfl

/-- `d(inr ∘ σ_s⁻¹)(z) = Dσ_s⁻¹(z)`. -/
lemma mfderiv_inr_holChart_symm (s : ℝ) (hs : s ^ 2 = 1) (z : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) (fun z => (Sum.inr ((holChart s hs).symm z) : S22)) z =
      DtauS s hs z := by
  have hinr : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) (@Sum.inr S2 S2) ((holChart s hs).symm z) :=
    ((ContMDiff.inr (I := 𝓘(ℝ, E2)) (M := S2) (M' := S2) (n := ∞)).mdifferentiable
      (by simp) _)
  have h := mfderiv_comp z hinr (mdifferentiable_holChart_symm s hs z)
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) (Sum.inr ∘ (holChart s hs).symm) z = _
  rw [h, mfderiv_sumInr]
  rfl

/-- `projF J₀ G` along a holomorphic map, from the smoothness of `G` along it in all directions. -/
lemma contDiff_projF_along {m : ℕ} {X : NodalSurface m} (J₀ : E →L[ℝ] E) {G : Form E X}
    {τ : ℂ → X.S}
    (hhol : ∀ z, X.j.J (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z (1 : ℂ)) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z Complex.I)
    (h : ∀ w, ContDiff ℝ ∞ fun z => G (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z w)) :
    ContDiff ℝ ∞ fun z => projF J₀ G (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z (1 : ℂ)) := by
  have e : (fun z => projF J₀ G (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z (1 : ℂ))) = fun z =>
      (1 / 2 : ℝ) • (G (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z (1 : ℂ)) +
        J₀ (G (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z Complex.I))) := by
    funext z
    rw [projF_apply, ← hhol z]
    rfl
  rw [e]
  exact ((h 1).add (J₀.contDiff.comp (h Complex.I))).const_smul _

/-- **Smoothness on both spheres from smoothness along smooth maps**: if `G` read along every
smooth `τ : ℂ → S² ⊔ S²` is smooth in every direction, `projF J₀ G` has smooth coefficients in both
holomorphic charts of each sphere. -/
theorem isSphereSmooth_two_of_along (J₀ : E →L[ℝ] E) {G : Form E twoSpheres}
    (h : ∀ τ : ℂ → S22, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ τ → ∀ w,
      ContDiff ℝ ∞ fun z => G (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z w)) :
    IsSphereSmooth (fun z => projF J₀ G (Sum.inl z)) ∧
      IsSphereSmooth (fun z => projF J₀ G (Sum.inr z)) := by
  have hl : ∀ (s : ℝ) (hs : s ^ 2 = 1),
      ContDiff ℝ ∞ (chartCoef s hs fun z => projF J₀ G (Sum.inl z)) := by
    intro s hs
    let τ : ℂ → S22 := fun z => Sum.inl ((holChart s hs).symm z)
    have hτ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ τ :=
      (ContMDiff.inl (I := 𝓘(ℝ, E2)) (M := S2) (M' := S2)).comp (contMDiff_holChart_symm s hs)
    have hhol : ∀ z, twoSpheres.j.J (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z (1 : ℂ)) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z Complex.I := fun z => by
      rw [mfderiv_inl_holChart_symm, twoSpheres_j_inl]
      have h := (DtauS_I s hs z 1).symm
      rw [mul_one] at h
      exact h
    have e : chartCoef s hs (fun z => projF J₀ G (Sum.inl z)) =
        fun z => projF J₀ G (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z (1 : ℂ)) := by
      funext z
      rw [mfderiv_inl_holChart_symm]
      rfl
    rw [e]
    exact contDiff_projF_along J₀ hhol (h τ hτ)
  have hr : ∀ (s : ℝ) (hs : s ^ 2 = 1),
      ContDiff ℝ ∞ (chartCoef s hs fun z => projF J₀ G (Sum.inr z)) := by
    intro s hs
    let τ : ℂ → S22 := fun z => Sum.inr ((holChart s hs).symm z)
    have hτ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ τ :=
      (ContMDiff.inr (I := 𝓘(ℝ, E2)) (M := S2) (M' := S2)).comp (contMDiff_holChart_symm s hs)
    have hhol : ∀ z, twoSpheres.j.J (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z (1 : ℂ)) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z Complex.I := fun z => by
      rw [mfderiv_inr_holChart_symm, twoSpheres_j_inr]
      have h := (DtauS_I s hs z 1).symm
      rw [mul_one] at h
      exact h
    have e : chartCoef s hs (fun z => projF J₀ G (Sum.inr z)) =
        fun z => projF J₀ G (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z (1 : ℂ)) := by
      funext z
      rw [mfderiv_inr_holChart_symm]
      rfl
    rw [e]
    exact contDiff_projF_along J₀ hhol (h τ hτ)
  exact ⟨⟨hl 1 _, hl (-1) _⟩, ⟨hr 1 _, hr (-1) _⟩⟩

end Two

/-! ## 5. The neck test forms -/

section Main

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}

/-- The glued form `∑ ρ_i · testForm φ i + ∑ χ_j · neckFormN`, read along any smooth map, is
smooth in every direction. -/
theorem contDiff_glueForm_along (hG : GlueCharts A) (F : FormGlueN A) (J₀ : E →L[ℝ] E)
    (φ : Ix A → ℝ × ℝ → ℝ) (hφ : ∀ o, ContDiff ℝ ∞ (φ o)) (c : Fin A.nn → ℂ → E)
    (hc : ∀ j, ContDiff ℝ ∞ (c j)) {τ : ℂ → S22} (hτ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ τ) (w : ℂ) :
    ContDiff ℝ ∞ fun z => glueForm F (testForm A φ) (fun j => neckFormN J₀ (A.hol j) (c j))
      (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z w) := by
  have e : (fun z => glueForm F (testForm A φ) (fun j => neckFormN J₀ (A.hol j) (c j))
      (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z w)) = fun z =>
        (∑ i, F.ρ i (τ z) • testForm A φ i (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z w)) +
        ∑ j, chiSN (A.hol j) (A.s0 j) (τ z) •
          neckFormN J₀ (A.hol j) (c j) (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z w) := by
    have key : ∀ (y : S22) (v : E2), glueForm F (testForm A φ)
        (fun j => neckFormN J₀ (A.hol j) (c j)) y v =
          (∑ i, F.ρ i y • testForm A φ i y v) +
            ∑ j, chiSN (A.hol j) (A.s0 j) y • neckFormN J₀ (A.hol j) (c j) y v := by
      intro y v
      simp only [glueForm, add_apply, FunLike.coe_sum, Finset.sum_apply, smul_apply]
    funext z
    exact key _ _
  rw [e]
  refine (ContDiff.sum fun i _ => ?_).add (ContDiff.sum fun j _ => ?_)
  · exact contDiff_testTermX A hτ φ hφ i (F.ρ i).contMDiff (F.hρ i) w
  · exact contDiff_neckTerm (hG.target j) (hG.smooth j) (hG.smooth_symm j).continuous
      (A.s0 j) J₀ (hc j) hτ w

/-- **The neck test forms exist** on every atlas of the constant map from `twoSpheres` satisfying
`GlueCharts`, for all gluing data `F`: `ξN_j` is the neck form, in the chart `A.hol j`, of the
coefficient `conj((-2πζ)⁻¹) · ∑_k (ε/β⁺)(s) γ_{j,k}(log ζ) e_k`. -/
theorem neckTestForms_of_glueCharts (hG : GlueCharts A) (F : FormGlueN A) : NeckTestForms J F := by
  intro φ hφ γ hγ
  let Fj : Fin A.nn → ℝ × ℝ → E := fun j => neckVal E (A.s0 j) fun k => γ (j, k)
  have hFs : ∀ j, ContDiff ℝ ∞ (Fj j) := fun j => contDiff_neckVal _ fun k => (hγ (j, k)).smooth
  have hFp : ∀ j s t, Fj j (s, t + 1) = Fj j (s, t) := fun j =>
    neckVal_periodic _ fun k => (hγ (j, k)).periodic
  have hFR : ∀ j, ∃ R, ∀ p : ℝ × ℝ, R < p.1 → Fj j p = 0 := fun j =>
    neckVal_eventually_zero _ fun k => hγ (j, k)
  let c : Fin A.nn → ℂ → E := fun j => neckCoef (J.J q) (Fj j)
  have hc : ∀ j, ContDiff ℝ ∞ (c j) := fun j => contDiff_neckCoef _ (hFs j) (hFp j) (hFR j)
  have hsm := isSphereSmooth_two_of_along (J.J q)
    (G := glueForm F (testForm A φ) (fun j => neckFormN (J.J q) (A.hol j) (c j)))
    fun τ hτ w => contDiff_glueForm_along hG F (J.J q) φ (fun o => (hφ o).smooth) c hc hτ w
  refine ⟨fun j => neckFormN (J.J q) (A.hol j) (c j), fun j k x hx => ?_,
    fun j x _ => neckFormN_mem J (A.isHol j) _ _, hsm.1, hsm.2⟩
  symm
  simp only [formNeckRep]
  rw [formInPolar_neckFormN (A.isHol j) (hG.target j) (hG.smooth_symm j),
    cmulL_neckCoef (acs_sq J q) (hFp j) x]
  change Real.smoothTransition (x.1 - A.s0 j) * crd k (neckVal E (A.s0 j) (fun k => γ (j, k)) x) =
    γ (j, k) x
  rw [crd_neckVal, ← mul_assoc, smoothTransition_mul_neckWt hx, one_mul]

variable (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- **`D` is Fredholm and onto, of index `dim E`** (Memoir Prop 4.23, `a = 0`, two spheres joined
at a node, `0 < δ₀ < 2π`) on every atlas of the constant map with the standard neck charts and
`GlueCharts`, for all gluing data of the sections. -/
theorem linCRN_isFredholm_twoSpheres_of_glueCharts (hsm : NeckSmooth A) (G : GlueDataN A)
    (hA : IsStdNeck A) (hG : GlueCharts A) (hδ : 0 < δ 0) (hδ' : δ 0 < 2 * Real.pi) :
    ContinuousLinearMap.IsFredholm (linCRN2 J hsm G δ h0 hmono) ∧
      Surjective (linCRN2 J hsm G δ h0 hmono) ∧
      fredholmIndex (linCRN2 J hsm G δ h0 hmono) = Module.finrank ℝ E := by
  obtain ⟨F⟩ := nonempty_formGlueN hG twoSpheres_chartsOnto
  have hd : DenseRange (linCRN2 J hsm G δ h0 hmono) :=
    denseRange_linCRN_of_neckTestForms hsm G hA hδ' hG F (neckTestForms_of_glueCharts J hG F)
  obtain ⟨h1, h2⟩ := linCRN_isFredholm_twoSpheres J hsm G δ h0 hmono hδ hδ' hd
  exact ⟨h1, linCRN_surjective_of_denseRange J hsm G δ h0 hmono hδ hδ' hd, h2⟩

variable (q) in
/-- **`D` at a constant map from two spheres joined at a node** (Memoir Prop 4.23, p. 118, level
`0`, `a = 0`): for every `J`, `q` and `0 < δ₀ < 2π`, there are an atlas with the standard neck
charts and gluing data on which `D` is Fredholm and onto, of index `dim E`, and its kernel is a copy
of `E = T_qQ` (the constant sections). -/
theorem linCRN_isFredholm_twoSpheres_uncond (hδ : 0 < δ 0) (hδ' : δ 0 < 2 * Real.pi) :
    ∃ (A : SectionAtlas (E := E) twoSpheres (fun _ => q)) (hsm : NeckSmooth A)
      (G : GlueDataN A), IsStdNeck A ∧ GlueCharts A ∧
        ContinuousLinearMap.IsFredholm (linCRN2 J hsm G δ h0 hmono) ∧
        Surjective (linCRN2 J hsm G δ h0 hmono) ∧
        fredholmIndex (linCRN2 J hsm G δ h0 hmono) = Module.finrank ℝ E ∧
        Nonempty (E ≃ₗ[ℝ] (linCRN2 J hsm G δ h0 hmono).ker) := by
  obtain ⟨A, hA, hG, hsm, ⟨G⟩, -⟩ := exists_glueAtlas_twoSpheres (E := E) q
  obtain ⟨h1, h2, h3⟩ :=
    linCRN_isFredholm_twoSpheres_of_glueCharts J δ h0 hmono hsm G hA hG hδ hδ'
  exact ⟨A, hsm, G, hA, hG, h1, h2, h3, ⟨linCRN_ker_equiv J hsm G δ h0 hmono⟩⟩

end Main

end GWMemoir
