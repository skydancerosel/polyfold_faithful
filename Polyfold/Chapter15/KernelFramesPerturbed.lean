import Polyfold.Chapter15.KernelChartChange
import Polyfold.Chapter15.CanonicalLiftIndependence
import Polyfold.Chapter15.RelativeSeeds
import Polyfold.Chapter6.PerturbedOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702 (**Theorem 15.4.1**; 2017: Theorem 15.6), and Part I, §6.6, p. 275 (**Theorem
6.6.18**, last paragraph of the proof): the orientation `o_{i,y}` of `ker (f − sᵢ)'(y)` is the
tangent orientation of the solution set of a perturbed section.

# The frames `o_{i,y}` and Part I's tangent orientation of `f + (−ŝ)`

## The text, paraphrased

(pp. 701–702) Since `f` is oriented, every onto operator `(f − sᵢ)'(y)` inherits an orientation
`o_{i,y}` of its kernel `T_yMᵢ`.  (Theorem 6.6.18, proof) For an sc⁺-section `s`, the solution set
of `f + s` gets a natural orientation from `o_f`, since `det((f + s)'(x))` is oriented from
`DET(f, x)`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `exists_basis_ray_iff`, `mem_kerFrames_iff`: a frame is in `kerFrames` iff the wedge of its
  chart vectors spans the ray `orKer o` of `λ(ker)`; `kerFrames_eq_of_subOp_eq`,
  `kerSet_eq_of_subOp_eq` (the frames and the kernel depend on the operator only);
  `chartVec_image_eq_kerSet_transfer` (the description of a tangent set as a kernel holds in
  every chart point).
* `minusSection`, `isZeroAt_sectionAdd_minusSection_iff`, **`subOp_eq_linZero`**: for a global
  sc⁺-section `ŝ`, `(f − ŝ)'(y)` is Part I's linearization `linZero` of the section `f + (−ŝ)` at
  its zero `y`; `isLinSurjAt_sectionAdd_minusSection`; **`mem_kerFrames_iff_tangentOr`**,
  `kerFrames_iff_tangentOr_chart`: the positive frames of `ker (f − ŝ)'(y)` for `o_y` are the
  frames whose wedge spans Part I's tangent orientation `tangentOr` of `f + (−ŝ)` for the
  inherited orientation `orSectionAdd o_y`, read in any chart.
* `KernelBranching.subOp_eq_of_eqOn`, `KernelBranching.frames_eq_kerFrames_global`,
  **`KernelBranching.mem_frames_iff_tangentOr`**: for a local branching structure described by
  kernels and a global sc⁺-section `ŝ` equal to `sᵢ` on an open `N₁`, at `z ∈ Mᵢ ∩ N₁` and in
  every strong bundle chart `c` at `z`: `z` is a zero of `f + (−ŝ)` with onto linearization, the
  chart vectors of `T_zMᵢ` are `ker (f + (−ŝ))'(z)`, of dimension `dᵢ`, and the frames `o_{i,z}`
  are those whose wedge spans the tangent orientation of `f + (−ŝ)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

/-- **A ray of `λ(N)` through a basis and through a tuple**: a ray `r` of `λ(N)` is the ray of
`b₁ ∧ … ∧ bₙ` for a basis `b` of `N` with underlying vectors `w` iff the `wᵢ` lie in `N` and
`r` is the ray of `w₁ ∧ … ∧ wₙ`. -/
theorem exists_basis_ray_iff {E : Type*} [AddCommGroup E] [Module ℝ E] (N : Submodule ℝ E)
    [FiniteDimensional ℝ N] {n : ℕ} (hn : finrank ℝ N = n) (w : Fin n → E)
    (r : Module.Ray ℝ (maxPow N)) :
    (∃ b : Basis (Fin n) ℝ N, (∀ i, (b i : E) = w i) ∧
        r = rayOfNeZero ℝ _ (wedge_equiv_ne_zero hn (LinearEquiv.refl ℝ N) b)) ↔
      ∃ (hmem : ∀ i, w i ∈ N) (hne : wedge (fun i => (⟨w i, hmem i⟩ : N)) hn.symm ≠ 0),
        r = rayOfNeZero ℝ _ hne := by
  constructor
  · rintro ⟨b, hb, hr⟩
    have hmem : ∀ i, w i ∈ N := fun i => hb i ▸ (b i).2
    have e : (fun i => (LinearEquiv.refl ℝ N) (b i)) = fun i => (⟨w i, hmem i⟩ : N) :=
      funext fun i => Subtype.ext (hb i)
    have hw : wedge (fun i => (LinearEquiv.refl ℝ N) (b i))
        (hn.symm.trans (LinearEquiv.refl ℝ N).finrank_eq) =
        wedge (fun i => (⟨w i, hmem i⟩ : N)) hn.symm := by rw [e]
    have hne : wedge (fun i => (⟨w i, hmem i⟩ : N)) hn.symm ≠ 0 :=
      hw ▸ wedge_equiv_ne_zero hn (LinearEquiv.refl ℝ N) b
    exact ⟨hmem, hne, hr.trans (rayOfNeZero_congr hw _ _)⟩
  · rintro ⟨hmem, hne, hr⟩
    have hli : LinearIndependent ℝ fun i => (⟨w i, hmem i⟩ : N) := (wedge_ne_zero_iff _).1 hne
    set b := basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [Fintype.card_fin, hn])
    have hb : ∀ i, b i = ⟨w i, hmem i⟩ := fun i => by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank']
    refine ⟨b, fun i => congrArg Subtype.val (hb i), hr.trans (rayOfNeZero_congr ?_ _ _)⟩
    congr 1
    exact funext fun i => (hb i).symm

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}} {f s : A.Obj → A.W} {O : Set A.Obj} {y : A.Obj}

/-- **The positive frames of the kernel in terms of rays**: for an operator `L₀` equal to
`(f − s)'(y)` in the chart point `p` and a subspace `N` equal to the image of its kernel, a
frame `v` of `L` is positive iff the chart vectors of `v` lie in `N` and their wedge spans the
ray `orKer o` of `λ(N)`. -/
theorem mem_kerFrames_iff (hf : A.B.IsScFredholmSection f) (hO : IsOpen O)
    (hs : IsScPlusSectionOn A s O) (p : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O)
    (hfs : f y = s y) (hys : y ∈ A.X.PObj.smoothSet) (hsec : A.B.HasScPlusSectionsThrough)
    (hsurj : Surjective (subOp hf.isScSmooth hs p hsub hfs)) (o : p.Or f hf)
    (L : Set A.X.PObj.TangentSpace) {n : ℕ}
    (hn : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth hs p hsub hfs : ↥p.T →L[ℝ] ↥p.K) :
      ↥p.T →ₗ[ℝ] ↥p.K)).map (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)) = n)
    {L₀ : ↥p.T →L[ℝ] ↥p.K} (h₀ : subOp hf.isScSmooth hs p hsub hfs = L₀)
    (hL₀ : L₀ ∈ p.linSet f) (hs₀ : Surjective L₀) {N : Submodule ℝ (p.c.φ.model.E 0)}
    (hN : (LinearMap.ker (L₀ : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N) (hn' : finrank ℝ N = n)
    (v : Fin n → A.X.PObj.TangentSpace) :
    v ∈ kerFrames hf hO hs p hsub hfs hys hsec hsurj o L hn ↔
      (∀ i, v i ∈ L) ∧ ∃ (hmem : ∀ i, chartVec p.c.isChart (v i) ∈ N)
        (hne : wedge (fun i => (⟨chartVec p.c.isChart (v i), hmem i⟩ : N)) hn'.symm ≠ 0),
        p.orKer o hL₀ hs₀ hN = rayOfNeZero ℝ _ hne := by
  subst h₀
  subst hN
  have := p.finiteDimensional_of_mem_linSet hf hL₀ rfl
  rw [← exists_basis_ray_iff _ hn]
  unfold kerFrames chartFrames
  simp only [mem_ofPred_eq, p.orientation_eq_orKerOrientation_iff o hL₀ hsurj rfl hn]

/-! ### The kernel as the chart image of a tangent set, in two chart points -/

/-- **`chartVec '' L = ker (f − s)'(y)` does not depend on the chart point**: if the chart vectors
of a set `L ⊆ T_yX` in the chart point `p` are the kernel of `(f − s)'(y)`, the same holds in
every chart point `p'` with domain in `O` (the kernels correspond under the tangent map of the
transition, `subOp_conj`). -/
theorem chartVec_image_eq_kerSet_transfer (hf : A.B.IsScSmoothSection f)
    (hs : IsScPlusSectionOn A s O) (p p' : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O)
    (hsub' : p'.c.φ.source ⊆ O) (hfs : f y = s y) (hys : y ∈ A.X.PObj.smoothSet)
    {L : Set A.X.PObj.TangentSpace}
    (hL : ∀ α ∈ L, A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y)
    (hker : chartVec p.c.isChart '' L = kerSet p.c f s p.z) :
    chartVec p'.c.isChart '' L = kerSet p'.c f s p'.z := by
  set κ := conjKerEquivOfMap (p.transferT p') (p.transferK p')
    (subOp_conj hf hs p p' hsub hsub' hfs) p.T.subtypeL Subtype.val_injective
    rfl p'.T.subtypeL Subtype.val_injective rfl with hκdef
  have hκ : ∀ v, ((κ v : _) : p'.c.φ.model.E 0) = p.baseDeriv p' v := fun v => by
    obtain ⟨w, rfl⟩ := (kerEquivOfMap _ p.T.subtypeL Subtype.val_injective rfl).surjective v
    exact (coe_conjKerEquivOfMap _ _ (subOp_conj hf hs p p' hsub hsub' hfs) _ _ rfl
      _ _ rfl w).trans rfl
  have hzl : levelLift p.c.φ 1 y = p.z :=
    p.c.φ.model.E.toBase_injective 1 ((A.X.PObj.toBase_levelLift p.c.isChart p.mem_source
      (smoothSet_subset_levelSet 1 hys)).trans p.toBase_z.symm)
  have hcv : ∀ α ∈ L, chartVec p'.c.isChart α = p.baseDeriv p' (chartVec p.c.isChart α) :=
    fun α hα => by
      have h := chartVec_eq_scDeriv_transition p.c.isChart p'.c.isChart (p.baseRet_retract p')
        p.mem_source p'.mem_source (hL α hα)
      rwa [hzl] at h
  have hker' := hker.trans (kerSet_eq_coe_map_ker hf hs p hsub hfs)
  rw [kerSet_eq_coe_map_ker hf hs p' hsub' hfs]
  ext w
  constructor
  · rintro ⟨α, hα, rfl⟩
    have hm : chartVec p.c.isChart α ∈
        (LinearMap.ker ((subOp hf hs p hsub hfs : ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K)).map
          (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) := by
      rw [← SetLike.mem_coe, ← hker']
      exact mem_image_of_mem _ hα
    rw [hcv α hα]
    exact (hκ ⟨_, hm⟩) ▸ (κ ⟨_, hm⟩).2
  · intro hw
    have h1 : ((κ.symm ⟨w, hw⟩ : _) : p.c.φ.model.E 0) ∈ chartVec p.c.isChart '' L := by
      rw [hker']
      exact (κ.symm ⟨w, hw⟩).2
    obtain ⟨α, hα, hαe⟩ := h1
    refine ⟨α, hα, ?_⟩
    rw [hcv α hα, hαe, ← hκ, LinearEquiv.apply_symm_apply]

/-! ### The section `f − ŝ` for a global sc⁺-section `ŝ` -/

/-- **The sc⁺-section `−ŝ`.** -/
abbrev minusSection (ŝ : A.Obj → A.W) : A.Obj → A.W :=
  Polyfold.sectionSmul A.P (fun _ => (-1 : ℝ)) ŝ

theorem isScPlusSection_minusSection {ŝ : A.Obj → A.W} (hŝ : A.B.IsScPlusSection ŝ) :
    A.B.IsScPlusSection (minusSection ŝ) :=
  hŝ.smul_left (isScSmoothMap_real_const (-1))

/-- `f + (−ŝ)` vanishes exactly where `f = ŝ`. -/
theorem isZeroAt_sectionAdd_minusSection_iff (hf : IsSection A.P f) {ŝ : A.Obj → A.W}
    (hŝ : IsSection A.P ŝ) :
    IsZeroAt A.P (Polyfold.sectionAdd A.P f (minusSection ŝ)) y ↔ f y = ŝ y := by
  have e : extendZero univ ŝ = ŝ :=
    funext fun y => (extendZero_eqOn (fun y _ => hŝ y) (mem_univ y)).symm
  have h := isZeroAt_subSec_iff hf (O := univ) (s := ŝ) (fun y _ => hŝ y) (mem_univ y)
  unfold subSec at h
  rwa [e] at h

section Perturbed

variable (hf : A.B.IsScFredholmSection f) {ŝ : A.Obj → A.W} (hŝ : A.B.IsScPlusSection ŝ)

/-- **`(f − ŝ)'(y)` is the linearization of the section `f + (−ŝ)` at its zero `y`**: the operator
`subOp` of the pair `(f, ŝ)` in a chart point is Part I's `linZero` of `f + (−ŝ)`. -/
theorem subOp_eq_linZero (p : ChartPoint A.B y) (hfs : f y = ŝ y)
    (hx : IsZeroAt A.P (Polyfold.sectionAdd A.P f (minusSection ŝ)) y) :
    subOp hf.isScSmooth (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ) p
        (subset_univ _) hfs =
      p.linZero (theorem_3_1_18_preprint hf (isScPlusSection_minusSection hŝ)) hx := by
  refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
  rw [coe_subOp, ChartPoint.coe_linZero, linAt_apply]
  unfold subDeriv
  refine congrArg (fun M : p.c.φ.model.E 0 →L[ℝ] p.c.F 0 => M v) ?_
  refine scDeriv_eq_of_eqOn_relOpen p.c.relOpen
    (isSc1_sub_comp_r hf.isScSmooth (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ)
      p.isChart (subset_univ _))
    ((hf.isScSmooth.sectionAdd (isScPlusSection_minusSection hŝ)).isSc1_principal_comp_r p.isChart)
    subset_rfl subset_rfl (fun u hu => ?_) p.mem_U
  have hO := p.c.r_mem_O hu
  change p.c.principal f (r p.c.R u) - p.c.principal ŝ (r p.c.R u) =
    p.c.principal (Polyfold.sectionAdd A.P f (minusSection ŝ)) (r p.c.R u)
  rw [p.c.principal_sectionAdd hf.isScSmooth.1 hŝ.1.sectionSmul hO,
    principal_sectionSmul_const p.c hŝ.1 (-1) hO, neg_one_smul, sub_eq_add_neg]

/-- **`(f + (−ŝ))'(y)` is onto when `(f − ŝ)'(y)` is onto in a chart point.** -/
theorem isLinSurjAt_sectionAdd_minusSection (p : ChartPoint A.B y) (hfs : f y = ŝ y)
    (hsurj : Surjective (subOp hf.isScSmooth (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ)
      p (subset_univ _) hfs)) :
    A.B.IsLinSurjAt (Polyfold.sectionAdd A.P f (minusSection ŝ)) y := by
  have hx : IsZeroAt A.P (Polyfold.sectionAdd A.P f (minusSection ŝ)) y :=
    (isZeroAt_sectionAdd_minusSection_iff hf.isScSmooth.1 hŝ.1).2 hfs
  refine ⟨p.c, p.isChart, p.mem_source, p.z, p.toBase_z, fun k hk => ?_⟩
  have hkK : k ∈ p.K := by
    refine (mem_rangeS_ρCLM_iff p.c.isRetraction p.mem_O p.mem_U).2 ?_
    rwa [p.toBase_z]
  obtain ⟨v, hv⟩ := hsurj ⟨k, hkK⟩
  rw [subOp_eq_linZero hf hŝ p hfs hx] at hv
  exact ⟨v, congrArg Subtype.val hv⟩

/-- **The positive frames of `ker (f − ŝ)'(y)` in terms of Part I's tangent orientation of
`f + (−ŝ)`**: a frame `v` of `L` is positive for the orientation of the kernel induced by
`o ∈ Or_y^f` iff the chart vectors of `v` lie in `ker (f + (−ŝ))'(y)` and their wedge spans the
tangent orientation of the solution set of `f + (−ŝ)` for the inherited orientation
(`orSectionAdd`). -/
theorem mem_kerFrames_iff_tangentOr (p : ChartPoint A.B y) (hfs : f y = ŝ y)
    (hx : IsZeroAt A.P (Polyfold.sectionAdd A.P f (minusSection ŝ)) y)
    (hLg : A.B.IsLinSurjAt (Polyfold.sectionAdd A.P f (minusSection ŝ)) y)
    (hys : y ∈ A.X.PObj.smoothSet) (hsec : A.B.HasScPlusSectionsThrough)
    (hsurj : Surjective (subOp hf.isScSmooth (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ)
      p (subset_univ _) hfs)) (o : p.Or f hf) (L : Set A.X.PObj.TangentSpace) {n : ℕ}
    (hn : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth
        (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ) p (subset_univ _) hfs :
        ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)) = n)
    (hn' : finrank ℝ (p.c.linKer (Polyfold.sectionAdd A.P f (minusSection ŝ)) p.z) = n)
    (v : Fin n → A.X.PObj.TangentSpace) :
    v ∈ kerFrames hf isOpen_univ (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ) p
        (subset_univ _) hfs hys hsec hsurj o L hn ↔
      (∀ i, v i ∈ L) ∧ ∃ (hmem : ∀ i, chartVec p.c.isChart (v i) ∈
          p.c.linKer (Polyfold.sectionAdd A.P f (minusSection ŝ)) p.z)
        (hne : wedge (fun i => (⟨chartVec p.c.isChart (v i), hmem i⟩ :
          p.c.linKer (Polyfold.sectionAdd A.P f (minusSection ŝ)) p.z)) hn'.symm ≠ 0),
        p.tangentOr (theorem_3_1_18_preprint hf (isScPlusSection_minusSection hŝ)) hx hLg
            (p.orSectionAdd hf (isScPlusSection_minusSection hŝ) o) = rayOfNeZero ℝ _ hne := by
  rw [p.tangentOr_orSectionAdd hf (isScPlusSection_minusSection hŝ) hx hLg o]
  exact mem_kerFrames_iff hf isOpen_univ _ p (subset_univ _) hfs hys hsec hsurj o L hn
    (subOp_eq_linZero hf hŝ p hfs hx)
    (p.linZero_mem_linSet_of_sectionAdd hf (isScPlusSection_minusSection hŝ) hx)
    (p.linZero_surjective (theorem_3_1_18_preprint hf (isScPlusSection_minusSection hŝ)) hx hLg)
    (p.map_ker_linZero (theorem_3_1_18_preprint hf (isScPlusSection_minusSection hŝ)) hx) hn' v

/-- **The positive frames of `ker (f − ŝ)'(y)`, read in a chart `c'`, in terms of the tangent
orientation of `f + (−ŝ)` read in any other chart `c`**: `y` is a zero of `f + (−ŝ)` with onto
linearization, `ker (f + (−ŝ))'(y)` has the same dimension in `c`, and a frame `v` of `L` is
positive iff its chart vectors in `c` lie in that kernel and their wedge spans the tangent
orientation for the inherited orientation. -/
theorem kerFrames_iff_tangentOr_chart (hfs : f y = ŝ y) (hys : y ∈ A.X.PObj.smoothSet)
    (hsec : A.B.HasScPlusSectionsThrough) (o : Orx f hf y hys)
    {c c' : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hc' : A.B.IsChart c')
    (hyc : y ∈ c.φ.source) (hyc' : y ∈ c'.φ.source)
    (hsurj' : Surjective (subOp hf.isScSmooth
      (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ) (chartPtOf c' hc' hyc' hys)
      (subset_univ _) hfs))
    {L : Set A.X.PObj.TangentSpace}
    (hL : ∀ α ∈ L, A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y)
    (hker : chartVec c'.isChart '' L = kerSet c' f ŝ (chartPtOf c' hc' hyc' hys).z) {n : ℕ}
    (hn' : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth
        (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ) (chartPtOf c' hc' hyc' hys)
        (subset_univ _) hfs : ↥(chartPtOf c' hc' hyc' hys).T →L[ℝ]
          ↥(chartPtOf c' hc' hyc' hys).K) :
        ↥(chartPtOf c' hc' hyc' hys).T →ₗ[ℝ] ↥(chartPtOf c' hc' hyc' hys).K)).map
      ((chartPtOf c' hc' hyc' hys).T.subtypeL :
        ↥(chartPtOf c' hc' hyc' hys).T →ₗ[ℝ] (chartPtOf c' hc' hyc' hys).c.φ.model.E 0)) = n) :
    ∃ (hx : IsZeroAt A.P (Polyfold.sectionAdd A.P f (minusSection ŝ)) y)
      (hLg : A.B.IsLinSurjAt (Polyfold.sectionAdd A.P f (minusSection ŝ)) y)
      (hnk : finrank ℝ ((chartPtOf c hc hyc hys).c.linKer
        (Polyfold.sectionAdd A.P f (minusSection ŝ)) (chartPtOf c hc hyc hys).z) = n),
      chartVec (chartPtOf c hc hyc hys).c.isChart '' L =
          ((chartPtOf c hc hyc hys).c.linKer (Polyfold.sectionAdd A.P f (minusSection ŝ))
            (chartPtOf c hc hyc hys).z : Set ((chartPtOf c hc hyc hys).c.φ.model.E 0)) ∧
      ∀ v : Fin n → A.X.PObj.TangentSpace,
        v ∈ kerFrames hf isOpen_univ (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ)
            (chartPtOf c' hc' hyc' hys) (subset_univ _) hfs hys hsec hsurj'
            (toChartOr hf hys c' hc' hyc' o) L hn' ↔
          (∀ i, v i ∈ L) ∧ ∃ (hmem : ∀ i, chartVec (chartPtOf c hc hyc hys).c.isChart (v i) ∈
              (chartPtOf c hc hyc hys).c.linKer (Polyfold.sectionAdd A.P f (minusSection ŝ))
                (chartPtOf c hc hyc hys).z)
            (hne : wedge (fun i => (⟨chartVec (chartPtOf c hc hyc hys).c.isChart (v i), hmem i⟩ :
              (chartPtOf c hc hyc hys).c.linKer (Polyfold.sectionAdd A.P f (minusSection ŝ))
                (chartPtOf c hc hyc hys).z)) hnk.symm ≠ 0),
            (chartPtOf c hc hyc hys).tangentOr
                (theorem_3_1_18_preprint hf (isScPlusSection_minusSection hŝ)) hx hLg
                ((chartPtOf c hc hyc hys).orSectionAdd hf (isScPlusSection_minusSection hŝ)
                  (toChartOr hf hys c hc hyc o)) = rayOfNeZero ℝ _ hne := by
  have hx : IsZeroAt A.P (Polyfold.sectionAdd A.P f (minusSection ŝ)) y :=
    (isZeroAt_sectionAdd_minusSection_iff hf.isScSmooth.1 hŝ.1).2 hfs
  have hLg := isLinSurjAt_sectionAdd_minusSection hf hŝ (chartPtOf c' hc' hyc' hys) hfs hsurj'
  have hop := subOp_eq_linZero hf hŝ (chartPtOf c hc hyc hys) hfs hx
  have hsurj : Surjective (subOp hf.isScSmooth
      (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ) (chartPtOf c hc hyc hys)
      (subset_univ _) hfs) := by
    rw [hop]
    exact (chartPtOf c hc hyc hys).linZero_surjective _ hx hLg
  have hn := (conjKerEquivOfMap ((chartPtOf c' hc' hyc' hys).transferT (chartPtOf c hc hyc hys))
    ((chartPtOf c' hc' hyc' hys).transferK (chartPtOf c hc hyc hys))
    (subOp_conj hf.isScSmooth (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ)
      (chartPtOf c' hc' hyc' hys) (chartPtOf c hc hyc hys) (subset_univ _) (subset_univ _) hfs)
    (chartPtOf c' hc' hyc' hys).T.subtypeL Subtype.val_injective rfl
    (chartPtOf c hc hyc hys).T.subtypeL Subtype.val_injective rfl).finrank_eq.symm.trans hn'
  have hnk : finrank ℝ ((chartPtOf c hc hyc hys).c.linKer
      (Polyfold.sectionAdd A.P f (minusSection ŝ)) (chartPtOf c hc hyc hys).z) = n := by
    rw [← (chartPtOf c hc hyc hys).map_ker_linZero
      (theorem_3_1_18_preprint hf (isScPlusSection_minusSection hŝ)) hx, ← hop]
    exact hn
  refine ⟨hx, hLg, hnk, ?_, fun v => ?_⟩
  · refine (chartVec_image_eq_kerSet_transfer hf.isScSmooth
      (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ) (chartPtOf c' hc' hyc' hys)
      (chartPtOf c hc hyc hys) (subset_univ _) (subset_univ _) hfs hys hL hker).trans
      ((kerSet_eq_coe_map_ker hf.isScSmooth (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ)
        (chartPtOf c hc hyc hys) (subset_univ _) hfs).trans ?_)
    rw [hop, (chartPtOf c hc hyc hys).map_ker_linZero
      (theorem_3_1_18_preprint hf (isScPlusSection_minusSection hŝ)) hx]
  rw [← kerFrames_toChartOr hf isOpen_univ (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ)
    hfs hys hsec o hc' hc hyc' hyc (subset_univ _) (subset_univ _) hsurj' hsurj hL hker hn' hn]
  exact mem_kerFrames_iff_tangentOr hf hŝ (chartPtOf c hc hyc hys) hfs hx hLg hys hsec hsurj _ L
    hn hnk v

end Perturbed

/-! ### Two local sections with the same operator -/

/-- **The positive frames of the kernel depend on the operator only**: if `(f − s)'(y)` and
`(f − s')'(y)` are the same operator in the chart point `p`, the two sets of positive frames
agree. -/
theorem kerFrames_eq_of_subOp_eq {s' : A.Obj → A.W} {O' : Set A.Obj}
    (hf : A.B.IsScFredholmSection f) (hO : IsOpen O) (hs : IsScPlusSectionOn A s O)
    (hO' : IsOpen O') (hs' : IsScPlusSectionOn A s' O') (p : ChartPoint A.B y)
    (hsub : p.c.φ.source ⊆ O) (hsub' : p.c.φ.source ⊆ O') (hfs : f y = s y) (hfs' : f y = s' y)
    (hys : y ∈ A.X.PObj.smoothSet) (hsec : A.B.HasScPlusSectionsThrough)
    (hsurj : Surjective (subOp hf.isScSmooth hs p hsub hfs))
    (hsurj' : Surjective (subOp hf.isScSmooth hs' p hsub' hfs')) (o : p.Or f hf)
    (L : Set A.X.PObj.TangentSpace) {n : ℕ}
    (hn : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth hs p hsub hfs : ↥p.T →L[ℝ] ↥p.K) :
      ↥p.T →ₗ[ℝ] ↥p.K)).map (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)) = n)
    (hn' : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth hs' p hsub' hfs' :
      ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K)).map
        (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)) = n)
    (hop : subOp hf.isScSmooth hs p hsub hfs = subOp hf.isScSmooth hs' p hsub' hfs') :
    kerFrames hf hO hs p hsub hfs hys hsec hsurj o L hn =
      kerFrames hf hO' hs' p hsub' hfs' hys hsec hsurj' o L hn' := by
  ext v
  exact (mem_kerFrames_iff hf hO hs p hsub hfs hys hsec hsurj o L hn hop
    (subOp_mem_linSet hf hO' hs' p hsub' hfs' hys hsec) hsurj' rfl hn' v).trans
    (mem_kerFrames_iff hf hO' hs' p hsub' hfs' hys hsec hsurj' o L hn' rfl
      (subOp_mem_linSet hf hO' hs' p hsub' hfs' hys hsec) hsurj' rfl hn' v).symm

/-- The kernel sets of two local sections with the same operator agree. -/
theorem kerSet_eq_of_subOp_eq {s' : A.Obj → A.W} {O' : Set A.Obj}
    (hf : A.B.IsScSmoothSection f) (hs : IsScPlusSectionOn A s O)
    (hs' : IsScPlusSectionOn A s' O') (p : ChartPoint A.B y)
    (hsub : p.c.φ.source ⊆ O) (hsub' : p.c.φ.source ⊆ O') (hfs : f y = s y) (hfs' : f y = s' y)
    (hop : subOp hf hs p hsub hfs = subOp hf hs' p hsub' hfs') :
    kerSet p.c f s p.z = kerSet p.c f s' p.z := by
  rw [kerSet_eq_coe_map_ker hf hs p hsub hfs, kerSet_eq_coe_map_ker hf hs' p hsub' hfs', hop]

/-! ### The frames of a structure described by kernels and a global extension of `sᵢ` -/

namespace KernelBranching

variable {Λ : A.W → ℚ≥0} {x : A.Obj} (K : KernelBranching A f Λ x)
  (hf : A.B.IsScFredholmSection f) (hsec : A.B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy)
  {ŝ : A.Obj → A.W} (hŝ : A.B.IsScPlusSection ŝ) {N₁ : Set A.Obj} (hN₁O : N₁ ⊆ K.O)
  {i : K.ι} (heq : EqOn ŝ (K.s i) N₁)

include hN₁O heq in
/-- **`(f − sᵢ)'(z) = (f − ŝ)'(z)`** in a chart point with domain in the set where `ŝ = sᵢ`. -/
theorem subOp_eq_of_eqOn {z : A.Obj} (hz : z ∈ K.M i) (p : ChartPoint A.B z)
    (hsub : p.c.φ.source ⊆ N₁) (hfs : f z = ŝ z) :
    subOp hf.isScSmooth (K.isScPlus i) p (hsub.trans hN₁O) (K.eq_of_mem hz) =
      subOp hf.isScSmooth (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ) p
        (subset_univ _) hfs := by
  refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
  rw [coe_subOp, coe_subOp]
  unfold subDeriv
  refine congrArg (fun M : p.c.φ.model.E 0 →L[ℝ] p.c.F 0 => M v) ?_
  refine scDeriv_eq_of_eqOn_relOpen p.c.relOpen
    (isSc1_sub_comp_r hf.isScSmooth (K.isScPlus i) p.isChart (hsub.trans hN₁O))
    (isSc1_sub_comp_r hf.isScSmooth (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ)
      p.isChart (subset_univ _)) subset_rfl subset_rfl (fun u hu => ?_) p.mem_U
  have hO := p.c.r_mem_O hu
  have hp : p.c.principal ŝ (r p.c.R u) = p.c.principal (K.s i) (r p.c.R u) := by
    unfold StrongBundleChart.principal
    rw [heq (hsub (p.c.φ.symm_mapsTo hO))]
  change p.c.principal f (r p.c.R u) - p.c.principal (K.s i) (r p.c.R u) =
    p.c.principal f (r p.c.R u) - p.c.principal ŝ (r p.c.R u)
  rw [hp]

include hN₁O heq in
/-- **The frames `o_{i,z}` are the positive frames of `ker (f − ŝ)'(z)`**, read in a chart with
domain in the set where `ŝ = sᵢ`; the chart vectors of `T_zMᵢ` are the kernel of
`(f − ŝ)'(z)`. -/
theorem frames_eq_kerFrames_global {z : A.Obj} (hz : z ∈ K.M i)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hzc : z ∈ c.φ.source)
    (hsub : c.φ.source ⊆ N₁) (hfs : f z = ŝ z) :
    ∃ (hsurj : Surjective (subOp hf.isScSmooth
        (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ)
        (chartPtOf c hc hzc (K.smooth i z hz)) (subset_univ _) hfs))
      (hn : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth
          (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ)
          (chartPtOf c hc hzc (K.smooth i z hz)) (subset_univ _) hfs :
          ↥(chartPtOf c hc hzc (K.smooth i z hz)).T →L[ℝ]
            ↥(chartPtOf c hc hzc (K.smooth i z hz)).K) :
          ↥(chartPtOf c hc hzc (K.smooth i z hz)).T →ₗ[ℝ]
            ↥(chartPtOf c hc hzc (K.smooth i z hz)).K)).map
        ((chartPtOf c hc hzc (K.smooth i z hz)).T.subtypeL :
          ↥(chartPtOf c hc hzc (K.smooth i z hz)).T →ₗ[ℝ]
            (chartPtOf c hc hzc (K.smooth i z hz)).c.φ.model.E 0)) = K.dim i),
      chartVec c.isChart '' A.X.PObj.submanifoldTangent (K.M i) z =
          kerSet c f ŝ (chartPtOf c hc hzc (K.smooth i z hz)).z ∧
        K.frames hf hsec o i z =
          kerFrames hf isOpen_univ (IsScPlusSectionOn.of_isScPlusSection hŝ isOpen_univ)
            (chartPtOf c hc hzc (K.smooth i z hz)) (subset_univ _) hfs (K.smooth i z hz) hsec
            hsurj (toChartOr hf (K.smooth i z hz) c hc hzc (o z (K.smooth i z hz)))
            (A.X.PObj.submanifoldTangent (K.M i) z) hn := by
  have hop := K.subOp_eq_of_eqOn hf hŝ hN₁O heq hz (chartPtOf c hc hzc (K.smooth i z hz)) hsub
    hfs
  have hsurj₀ : Surjective (subOp hf.isScSmooth (K.isScPlus i)
      (chartPtOf c hc hzc (K.smooth i z hz)) (hsub.trans hN₁O) (K.eq_of_mem hz)) :=
    (surjective_subOp_iff hf.isScSmooth (K.isScPlus i) _ (hsub.trans hN₁O) (K.eq_of_mem hz)).2
      (K.onto i z hz c hc (hsub.trans hN₁O) hzc _
        (chartPtOf c hc hzc (K.smooth i z hz)).toBase_z)
  have hker₀ := K.tangent_eq i z hz c hc (hsub.trans hN₁O) hzc _
    (chartPtOf c hc hzc (K.smooth i z hz)).toBase_z
  have hn₀ : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth (K.isScPlus i)
      (chartPtOf c hc hzc (K.smooth i z hz)) (hsub.trans hN₁O) (K.eq_of_mem hz) :
        ↥(chartPtOf c hc hzc (K.smooth i z hz)).T →L[ℝ]
          ↥(chartPtOf c hc hzc (K.smooth i z hz)).K) :
        ↥(chartPtOf c hc hzc (K.smooth i z hz)).T →ₗ[ℝ]
          ↥(chartPtOf c hc hzc (K.smooth i z hz)).K)).map
      ((chartPtOf c hc hzc (K.smooth i z hz)).T.subtypeL :
        ↥(chartPtOf c hc hzc (K.smooth i z hz)).T →ₗ[ℝ]
          (chartPtOf c hc hzc (K.smooth i z hz)).c.φ.model.E 0)) = K.dim i := by
    obtain ⟨N', hN', -, hn⟩ := exists_submodule_chartVec_image c.isChart
      (K.isSubmanifoldOfDim i).1 ((K.isSubmanifoldOfDim i).2 z hz) hzc
    have h := (kerSet_eq_coe_map_ker hf.isScSmooth (K.isScPlus i)
      (chartPtOf c hc hzc (K.smooth i z hz)) (hsub.trans hN₁O)
      (K.eq_of_mem hz)).symm.trans (hker₀.symm.trans hN'.symm)
    rw [SetLike.coe_injective h]
    exact hn
  have hfr := K.frames_eq_chart hf hsec o hz hc hzc (hsub.trans hN₁O) hsurj₀ hn₀
  refine ⟨hop ▸ hsurj₀, hop ▸ hn₀, hker₀.trans ?_, hfr.trans ?_⟩
  · exact kerSet_eq_of_subOp_eq hf.isScSmooth (K.isScPlus i) _
      (chartPtOf c hc hzc (K.smooth i z hz)) (hsub.trans hN₁O) (subset_univ _) (K.eq_of_mem hz)
      hfs hop
  · exact kerFrames_eq_of_subOp_eq hf K.isOpen_O (K.isScPlus i) isOpen_univ _
      (chartPtOf c hc hzc (K.smooth i z hz)) (hsub.trans hN₁O) (subset_univ _) (K.eq_of_mem hz)
      hfs (K.smooth i z hz) hsec hsurj₀ (hop ▸ hsurj₀) _ _ hn₀ (hop ▸ hn₀) hop

include hN₁O heq in
/-- **The frames `o_{i,z}` in terms of Part I's tangent orientation of `f + (−ŝ)`**, for a
global sc⁺-section `ŝ` equal to `sᵢ` on the open set `N₁ ∋ z`, read in any strong bundle chart
`c` at `z ∈ Mᵢ`: `z` is a zero of `f + (−ŝ)` with onto linearization, the chart vectors of
`T_zMᵢ` are `ker (f + (−ŝ))'(z)`, of dimension `dᵢ`, and a frame `v` of `T_zMᵢ` is in `o_{i,z}`
iff the wedge of its chart vectors spans the tangent orientation of `f + (−ŝ)` at `z` for the
orientation inherited from `o_z`. -/
theorem mem_frames_iff_tangentOr (hN₁ : IsOpen N₁) {z : A.Obj} (hz : z ∈ K.M i)
    (hzN₁ : z ∈ N₁) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hzc : z ∈ c.φ.source) :
    ∃ (hx : IsZeroAt A.P (Polyfold.sectionAdd A.P f (minusSection ŝ)) z)
      (hLg : A.B.IsLinSurjAt (Polyfold.sectionAdd A.P f (minusSection ŝ)) z)
      (hnk : finrank ℝ ((chartPtOf c hc hzc (K.smooth i z hz)).c.linKer
        (Polyfold.sectionAdd A.P f (minusSection ŝ))
          (chartPtOf c hc hzc (K.smooth i z hz)).z) = K.dim i),
      chartVec (chartPtOf c hc hzc (K.smooth i z hz)).c.isChart ''
          A.X.PObj.submanifoldTangent (K.M i) z =
        ((chartPtOf c hc hzc (K.smooth i z hz)).c.linKer
          (Polyfold.sectionAdd A.P f (minusSection ŝ)) (chartPtOf c hc hzc (K.smooth i z hz)).z :
          Set ((chartPtOf c hc hzc (K.smooth i z hz)).c.φ.model.E 0)) ∧
      ∀ v : Fin (K.dim i) → A.X.PObj.TangentSpace,
        v ∈ K.frames hf hsec o i z ↔
          (∀ j, v j ∈ A.X.PObj.submanifoldTangent (K.M i) z) ∧
          ∃ (hmem : ∀ j, chartVec (chartPtOf c hc hzc (K.smooth i z hz)).c.isChart (v j) ∈
              (chartPtOf c hc hzc (K.smooth i z hz)).c.linKer
                (Polyfold.sectionAdd A.P f (minusSection ŝ))
                (chartPtOf c hc hzc (K.smooth i z hz)).z)
            (hne : wedge (fun j =>
              (⟨chartVec (chartPtOf c hc hzc (K.smooth i z hz)).c.isChart (v j), hmem j⟩ :
                (chartPtOf c hc hzc (K.smooth i z hz)).c.linKer
                  (Polyfold.sectionAdd A.P f (minusSection ŝ))
                  (chartPtOf c hc hzc (K.smooth i z hz)).z)) hnk.symm ≠ 0),
            (chartPtOf c hc hzc (K.smooth i z hz)).tangentOr
                (theorem_3_1_18_preprint hf (isScPlusSection_minusSection hŝ)) hx hLg
                ((chartPtOf c hc hzc (K.smooth i z hz)).orSectionAdd hf
                  (isScPlusSection_minusSection hŝ)
                  (toChartOr hf (K.smooth i z hz) c hc hzc (o z (K.smooth i z hz)))) =
              rayOfNeZero ℝ _ hne := by
  have hfs : f z = ŝ z := (K.eq_of_mem hz).trans (heq hzN₁).symm
  obtain ⟨hsurj, hn, hker, hfr⟩ := K.frames_eq_kerFrames_global hf hsec o hŝ hN₁O heq hz
    (StrongBundle.IsChart.restrictInter hN₁ hc)
    (StrongBundleChart.mem_restrictInter_source _ hN₁ hzc hzN₁)
    (StrongBundleChart.restrictInter_source_subset _ hN₁) hfs
  obtain ⟨hx, hLg, hnk, hA, hiff⟩ := kerFrames_iff_tangentOr_chart hf hŝ hfs (K.smooth i z hz)
    hsec (o z (K.smooth i z hz)) hc (StrongBundle.IsChart.restrictInter hN₁ hc) hzc
    (StrongBundleChart.mem_restrictInter_source _ hN₁ hzc hzN₁) hsurj (fun α hα => hα.1) hker hn
  exact ⟨hx, hLg, hnk, hA, fun v => (Set.ext_iff.1 hfr v).trans (hiff v)⟩

end KernelBranching

end SBLocalization

end Polyfold
