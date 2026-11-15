import Polyfold.Chapter15.CanonicalOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702 (**Theorem 15.4.1**, **Definition 15.4.2**; 2017: Theorem 15.6, Definition 15.7): the
orientation `o_{i,y}` of `ker (f − sᵢ)'(y)` induced by `o_y` does not depend on the chart.

# Chart independence of the kernel orientation

## The text, paraphrased

(pp. 701–702) Since `f` is oriented, every `(f − sᵢ)'(y)` inherits an orientation `o_{i,y}`; for
an onto operator it is an orientation of the kernel.  The text states this without reference to
a chart.

## What is formalized

* `ChartPoint.scDeriv_principal_baseDeriv_of_isSc1`: the linearizations at a zero, read in two
  chart points, are conjugate under the tangent map of the transition and the fibre transition,
  for a section whose principal parts are `sc¹` in the two charts (Part I's
  `scDeriv_principal_baseDeriv`, which asks for a globally sc-smooth section, with the same
  proof).
* `SBLocalization.subOp_conj`: `(f − s)'(y)` read in two chart points with domains in `O` is
  conjugate (`s` a local sc⁺-section on `O`).
* **`SBLocalization.orKer_orTransfer`**: the orientation of the kernel read in `p'` for the
  transferred orientation is the image, under the tangent map of the transition, of the one read
  in `p` (Part I's `orTransfer_surjRay`).
* **`SBLocalization.kerFrames_orTransfer`**, **`kerFrames_toChartOr`**: the positive frames of
  `T_yMᵢ` for `o_{i,y}` (`kerFrames`) are the same in every chart with domain in `O`.
* **`KernelBranching.frames_eq_chart`**: the frames `o_{i,y}` of a structure described by
  kernels, read in any strong bundle chart with domain in `O`.
-/

set_option maxSynthPendingDepth 3

open Module TensorProduct Bundle Topology Set

noncomputable section

namespace Polyfold

universe u v

open StrongRetr

namespace ChartPoint

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {x : X} (p p' : ChartPoint B x)

/-- **The linearizations of a section in two chart points are conjugate**, for a section `g` of
`P` whose principal parts are `sc¹` in the two charts: at a zero `x` of `g`,
`D(ĝ' ∘ r')(z') ∘ D(τ ∘ r)(z) = Γ ∘ D(ĝ ∘ r)(z)`.  (Part I's `scDeriv_principal_baseDeriv` for a
section that is sc-smooth only near `x`; the proof is the same.) -/
theorem scDeriv_principal_baseDeriv_of_isSc1 {g : X → Y} (hf : IsSection P g)
    (hfr : IsSc1 p.c.U (p.c.principal g ∘ r p.c.R))
    (hfr' : IsSc1 p'.c.U (p'.c.principal g ∘ r p'.c.R))
    (hx0 : IsZeroAt P g x) (v : p.c.φ.model.E 0) :
    scDeriv p'.c.U (p'.c.principal g ∘ r p'.c.R) p'.z (p.baseDeriv p' v) =
      p.fiberMap p' (scDeriv p.c.U (p.c.principal g ∘ r p.c.R) p.z v) := by
  have hz1 : p.z ∈ p.c.φ.model.E.lvlSet (p.baseRet p').U 1 := p.z_mem_baseRet p'
  have hRwU : (p.baseRet p').U ⊆ p.c.U := p.baseRet_U_subset p'
  have hr1 : IsSc1 p.c.U (r p.c.R) := (r_isScSmooth p.c.relOpen p.c.isRetraction).isSc1
  have hrRw : IsSc1 (p.baseRet p').U (r p.c.R) := hr1.of_subset hRwU
  have hfrRw : IsSc1 (p.baseRet p').U (p.c.principal g ∘ r p.c.R) := hfr.of_subset hRwU
  have hDfr : scDeriv (p.baseRet p').U (p.c.principal g ∘ r p.c.R) p.z =
      scDeriv p.c.U (p.c.principal g ∘ r p.c.R) p.z :=
    scDeriv_eq_of_eqOn_relOpen (p.baseRet p').relOpen hfrRw hfr subset_rfl hRwU
      (fun _ _ => rfl) hz1
  set RK := p.bundleRet p' with hRKdef
  set Φ : (p.c.φ.model.E.prod p.c.F) 0 → p'.c.F 0 :=
    fun q => ((p.c.transition p'.c ∘ RK) q).2 with hΦdef
  have hΦ : IsSc1 RK.U Φ := ((p.isScSmooth_bundleTransition p').snd RK.isScDomain).isSc1
  have hSD : ∀ u ∈ (p.baseRet p').U, ((u, 0) : (p.c.φ.model.E.prod p.c.F) 0) ∈ RK.U :=
    fun u hu => ⟨⟨hu.1, mem_univ _⟩, ⟨hu.2, mem_univ _⟩⟩
  have hzero : ∀ u ∈ (p.baseRet p').U, Φ (u, 0) = 0 := by
    intro u hu
    have hru : r p.c.R u ∈ p.c.φ.overlap p'.c.φ := by
      rw [← p.baseRet_retract p']; exact (p.baseRet p').apply_mem_retract hu
    have hR0 : p.c.R (u, 0) = (r p.c.R u, 0) := by
      rw [apply_eq p.c.isRetraction hu.1, (ρ_isLinear p.c.isRetraction hu.1).map_zero]
    have hK0 : (r p.c.R u, (0 : p.c.F 0)) ∈ p.c.K := by
      rw [← hR0]; exact ⟨(u, 0), ⟨hu.1, mem_univ _⟩, rfl⟩
    change (p.c.transition p'.c (p.c.R (u, 0))).2 = 0
    rw [hR0]
    exact p.c.transition_snd_zero p'.c hK0 (p.c.φ.symm_mem_of_mem_overlap p'.c.φ hru)
  set σ := scPair (r p.c.R) (p.c.principal g ∘ r p.c.R) with hσdef
  have hσmem : ∀ u ∈ (p.baseRet p').U, ∃ y₁, y₁ ∈ p.c.φ.source ∧ y₁ ∈ p'.c.φ.source ∧
      r p.c.R u = p.c.φ y₁ ∧ σ u = p.c (g y₁) ∧ σ u ∈ RK.retract := by
    intro u hu
    obtain ⟨y₁, hy₁, hy₁', hy₁u⟩ := p.exists_eq_of_mem_baseRet p' hu
    have hσu : σ u = p.c (g y₁) := by
      change (r p.c.R u, p.c.principal g (r p.c.R u)) = p.c (g y₁)
      rw [hy₁u, p.c.apply_section' hf hy₁]
    refine ⟨y₁, hy₁, hy₁', hy₁u, hσu, ?_⟩
    rw [hRKdef, p.bundleRet_retract p', hσu]
    exact ⟨g y₁, ⟨p.c.mem_source_of_proj (by rw [hf]; exact hy₁),
      p'.c.mem_source_of_proj (by rw [hf]; exact hy₁')⟩, rfl⟩
  have hmapsσ : MapsTo σ (p.baseRet p').U RK.U := fun u hu => by
    obtain ⟨-, -, -, -, -, h⟩ := hσmem u hu
    exact RK.retract_subset h
  have hσ1 : IsSc1 (p.baseRet p').U σ := hrRw.scPair' hfrRw
  have hEq : EqOn ((p'.c.principal g ∘ r p'.c.R) ∘ (p.c.φ.transition p'.c.φ ∘ p.baseRet p'))
      (Φ ∘ σ) (p.baseRet p').U := by
    intro u hu
    obtain ⟨y₁, hy₁, hy₁', hru, hσu, hσK⟩ := hσmem u hu
    have hτu : p.c.φ.transition p'.c.φ (r p.c.R u) = p'.c.φ y₁ := by
      rw [hru, p.c.φ.transition_apply p'.c.φ hy₁]
    have hr' : r p'.c.R (p'.c.φ y₁) = p'.c.φ y₁ :=
      r_eq_self p'.c.isRetraction (by rw [p'.c.r_image]; exact p'.c.φ.mapsTo_model y₁ hy₁')
    change p'.c.principal g (r p'.c.R (p.c.φ.transition p'.c.φ (r p.c.R u))) =
      (p.c.transition p'.c (RK (σ u))).2
    rw [RK.apply_eq_self_of_mem_retract hσK, hσu]
    change _ = (p'.c (p.c.toPartialEquiv.symm (p.c (g y₁)))).2
    rw [p.c.toPartialEquiv.left_inv (p.c.mem_source_of_proj (by rw [hf]; exact hy₁)),
      p'.c.apply_section' hf hy₁', hτu, hr']
  have hmapsτ : MapsTo (p.c.φ.transition p'.c.φ ∘ p.baseRet p') (p.baseRet p').U p'.c.U :=
    fun u hu => by
      obtain ⟨y₁, hy₁, hy₁', hru⟩ := p.exists_eq_of_mem_baseRet p' hu
      change p.c.φ.transition p'.c.φ (r p.c.R u) ∈ p'.c.U
      rw [hru, p.c.φ.transition_apply p'.c.φ hy₁]
      exact mem_U_of_mem_O p'.c.isRetraction
        (by rw [p'.c.r_image]; exact p'.c.φ.mapsTo_model y₁ hy₁')
  have hτ1 := p.isSc1_transition p'
  have hℓ : IsSc1 (p.baseRet p').U
      ((p'.c.principal g ∘ r p'.c.R) ∘ (p.c.φ.transition p'.c.φ ∘ p.baseRet p')) :=
    (theorem_1_3_1' (p.baseRet p').isScDomain p'.c.relOpen.isScDomain hτ1 hfr' hmapsτ).1
  have hΦσ : IsSc1 (p.baseRet p').U (Φ ∘ σ) :=
    (theorem_1_3_1' (p.baseRet p').isScDomain RK.isScDomain hσ1 hΦ hmapsσ).1
  have hDeq : scDeriv (p.baseRet p').U
      ((p'.c.principal g ∘ r p'.c.R) ∘ (p.c.φ.transition p'.c.φ ∘ p.baseRet p')) p.z =
        scDeriv (p.baseRet p').U (Φ ∘ σ) p.z :=
    scDeriv_eq_of_eqOn_relOpen (p.baseRet p').relOpen hℓ hΦσ subset_rfl subset_rfl hEq hz1
  have hfz : p.c.principal g (p.c.φ.model.E.toBase 1 p.z) = 0 := by
    rw [p.toBase_z]; exact (p.c.isZeroAt_iff hf p.mem_source).1 hx0
  have hlevσ : levelMap σ 1 p.z = ((p.z, 0) : (p.c.φ.model.E.prod p.c.F) 1) := by
    apply levelMap_eq_of_toBase_eq
    rw [ScBanach.prod_toBase, map_zero]
    change ((p.c.φ.model.E.toBase 1 p.z, (0 : p.c.F 0)) : (p.c.φ.model.E.prod p.c.F) 0) =
      (r p.c.R (p.c.φ.model.E.toBase 1 p.z),
        p.c.principal g (r p.c.R (p.c.φ.model.E.toBase 1 p.z)))
    rw [p.r_toBase_z, hfz]
  have hΓ : ∀ k, Φ (p.c.φ.model.E.toBase 1 p.z, k) = p.fiberMap p' k :=
    p.bundleTransition_apply p'
  have h1 := scDeriv_comp_apply' (p.baseRet p').relOpen p'.c.relOpen hτ1 hfr' hmapsτ hz1 v
  rw [p.levelMap_transition p'] at h1
  have h2 := scDeriv_comp_apply' (p.baseRet p').relOpen RK.relOpen hσ1 hΦ hmapsσ hz1 v
  rw [hlevσ, hσdef, scDeriv_scPair (p.baseRet p').relOpen hrRw hfrRw hz1,
    ContinuousLinearMap.prod_apply,
    scDeriv_fiber_of_vanishing (p.baseRet p').relOpen hΦ hz1 hSD (p.mem_bundleRet p') hzero
      (p.fiberMap p') hΓ] at h2
  change scDeriv p'.c.U _ p'.z
    (scDeriv (p.baseRet p').U (p.c.φ.transition p'.c.φ ∘ p.baseRet p') p.z v) = _
  rw [h1, hDeq, ← h2, hDfr]

end ChartPoint

/-! ### Orientations pulled back along the identity, and maps of bases -/

/-- **A basis `b` of `N` is positive for the ray `r` iff its image under `κ : N ≅ N'` is positive
for `λ(κ) r`** (orientations read by `pullOr` along the identity). -/
theorem orientation_map_pullOr_iff {N N' : Type*} [AddCommGroup N] [Module ℝ N]
    [FiniteDimensional ℝ N] [AddCommGroup N'] [Module ℝ N'] [FiniteDimensional ℝ N'] {k : ℕ}
    (hk : finrank ℝ N = k) (hk' : finrank ℝ N' = k) (κ : N ≃ₗ[ℝ] N')
    (r : Module.Ray ℝ (maxPow N)) (b : Basis (Fin k) ℝ N) :
    (b.map κ).orientation =
        pullOr hk' (LinearEquiv.refl ℝ N') (Module.Ray.map (maxPowEquiv κ) r) ↔
      b.orientation = pullOr hk (LinearEquiv.refl ℝ N) r := by
  have h1 : pullOr hk' (LinearEquiv.refl ℝ N') (Module.Ray.map (maxPowEquiv κ) r) =
      pullOr hk' κ.symm r := by
    rw [← pullOr_trans hk' κ.symm κ r]
    congr 1
    exact (LinearEquiv.symm_trans_self κ).symm
  rw [h1, orientation_eq_pullOr_iff, orientation_eq_pullOr_iff]
  have h2 : rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk' κ.symm (b.map κ)) =
      rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk (LinearEquiv.refl ℝ N) b) :=
    rayOfNeZero_congr (by
      congr 1
      funext i
      simp) _ _
  rw [h2]

namespace SBLocalization

open StrongBundle MPolyfold Linearization15 EpGroupoid Function

variable {A : SEP.{u}} {f s : A.Obj → A.W} {O : Set A.Obj} {y : A.Obj}

/-! ### `(f − s)'(y)` in two chart points -/

/-- The principal part of the section `f − s` (`subSec`), composed with `r`, is `sc¹` in a chart
with domain in `O`. -/
theorem isSc1_principal_subSec_comp_r (hf : A.B.IsScSmoothSection f)
    (hs : IsScPlusSectionOn A s O) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ O) : IsSc1 c.U (c.principal (subSec f s O) ∘ r c.R) := by
  have hgrep : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal (subSec f s O) z)) := by
    refine (isScSmoothRetractMap_sectionSubOn hf hs hc hsub).congr fun w hw => ?_
    change (w, c.principal (sectionSubOn f s O) w) = (w, c.principal (subSec f s O) w)
    rw [principal_sectionSubOn hf.1 hs.1 hsub hw, principal_subSec hf.1 hs.1 hsub hw]
  have := hgrep.comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen) c.base_retract
  exact ((this.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl).isSc1

/-- `D((f̂ − ŝ) ∘ r)(z)` is the chart operator of the section `f − s` (`subSec`). -/
theorem subDeriv_eq_scDeriv_subSec (hf : A.B.IsScSmoothSection f)
    (hs : IsScPlusSectionOn A s O) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ O) {z : c.φ.model.E 1} (hzU : c.φ.model.E.toBase 1 z ∈ c.U) :
    subDeriv c f s z = scDeriv c.U (c.principal (subSec f s O) ∘ r c.R) z := by
  refine scDeriv_eq_of_eqOn_relOpen c.relOpen (isSc1_sub_comp_r hf hs hc hsub)
    (isSc1_principal_subSec_comp_r hf hs hc hsub) subset_rfl subset_rfl (fun u hu => ?_) hzU
  change c.principal f (r c.R u) - c.principal s (r c.R u) =
    c.principal (subSec f s O) (r c.R u)
  rw [principal_subSec hf.1 hs.1 hsub (c.r_mem_O hu)]

/-- **`(f − s)'(y)` read in two chart points is conjugate**: for chart points `p`, `p'` at `y`
with domains in `O` and `f(y) = s(y)`, `(f − s)'(y)_{p'} ∘ A = Γ ∘ (f − s)'(y)_p` with
`A = D(τ ∘ r)(z)` (`transferT`) and the fibre transition `Γ` (`transferK`). -/
theorem subOp_conj (hf : A.B.IsScSmoothSection f) (hs : IsScPlusSectionOn A s O)
    (p p' : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O) (hsub' : p'.c.φ.source ⊆ O)
    (hfs : f y = s y) (v : ↥p.T) :
    subOp hf hs p' hsub' hfs (p.transferT p' v) = p.transferK p' (subOp hf hs p hsub hfs v) := by
  apply Subtype.ext
  rw [coe_subOp, ChartPoint.coe_transferK_apply, coe_subOp, ChartPoint.coe_transferT_apply,
    subDeriv_eq_scDeriv_subSec hf hs p'.isChart hsub' p'.mem_U,
    subDeriv_eq_scDeriv_subSec hf hs p.isChart hsub p.mem_U]
  exact p.scDeriv_principal_baseDeriv_of_isSc1 p' (isSection_subSec hf.1 s O)
    (isSc1_principal_subSec_comp_r hf hs p.isChart hsub)
    (isSc1_principal_subSec_comp_r hf hs p'.isChart hsub')
    ((isZeroAt_subSec_iff hf.1 hs.1 (hsub p.mem_source)).2 hfs) v

/-! ### The kernel orientation in two chart points -/

/-- **`o_{i,y}` does not depend on the chart point**: read in `p'`, the orientation of
`ker (f − s)'(y)` for the transferred orientation (`orTransfer`) is the image under the tangent
map `A = D(τ ∘ r)(z)` of the transition of the one read in `p` (Part I's `orTransfer_surjRay`). -/
theorem orKer_orTransfer (hf : A.B.IsScFredholmSection f) (hO : IsOpen O)
    (hs : IsScPlusSectionOn A s O) (p p' : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O)
    (hsub' : p'.c.φ.source ⊆ O) (hfs : f y = s y) (hys : y ∈ A.X.PObj.smoothSet)
    (hsec : A.B.HasScPlusSectionsThrough)
    (hsurj : Surjective (subOp hf.isScSmooth hs p hsub hfs))
    (hsurj' : Surjective (subOp hf.isScSmooth hs p' hsub' hfs)) (o : p.Or f hf) :
    p'.orKer (p.orTransfer p' hf hys o) (subOp_mem_linSet hf hO hs p' hsub' hfs hys hsec)
        hsurj' rfl =
      Module.Ray.map (maxPowEquiv (conjKerEquivOfMap (p.transferT p') (p.transferK p')
          (subOp_conj hf.isScSmooth hs p p' hsub hsub' hfs) p.T.subtypeL Subtype.val_injective
          rfl p'.T.subtypeL Subtype.val_injective rfl))
        (p.orKer o (subOp_mem_linSet hf hO hs p hsub hfs hys hsec) hsurj rfl) :=
  p.orTransfer_surjRay p' hf hys o (subOp_mem_linSet hf hO hs p hsub hfs hys hsec) hsurj
    (subOp_mem_linSet hf hO hs p' hsub' hfs hys hsec) hsurj'
    (subOp_conj hf.isScSmooth hs p p' hsub hsub' hfs) rfl rfl

/-- **The positive frames of the kernel do not depend on the chart point** (2021 pp. 701–702:
`o_{i,y}` is an orientation of `ker (f − sᵢ)'(y) = T_yMᵢ`): for chart points `p`, `p'` at `y`
with domains in `O` and a set `L ⊆ T_yX` whose chart vectors in `p` are the kernel,
the frames of `L` positive for `o` in `p` are those positive for the transferred orientation in
`p'`. -/
theorem kerFrames_orTransfer (hf : A.B.IsScFredholmSection f) (hO : IsOpen O)
    (hs : IsScPlusSectionOn A s O) (p p' : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O)
    (hsub' : p'.c.φ.source ⊆ O) (hfs : f y = s y) (hys : y ∈ A.X.PObj.smoothSet)
    (hsec : A.B.HasScPlusSectionsThrough)
    (hsurj : Surjective (subOp hf.isScSmooth hs p hsub hfs))
    (hsurj' : Surjective (subOp hf.isScSmooth hs p' hsub' hfs)) (o : p.Or f hf)
    {L : Set A.X.PObj.TangentSpace}
    (hL : ∀ α ∈ L, A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y)
    (hker : chartVec p.c.isChart '' L = kerSet p.c f s p.z) {n : ℕ}
    (hn : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth hs p hsub hfs : ↥p.T →L[ℝ] ↥p.K) :
      ↥p.T →ₗ[ℝ] ↥p.K)).map (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)) = n)
    (hn' : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth hs p' hsub' hfs :
      ↥p'.T →L[ℝ] ↥p'.K) : ↥p'.T →ₗ[ℝ] ↥p'.K)).map
        (p'.T.subtypeL : ↥p'.T →ₗ[ℝ] p'.c.φ.model.E 0)) = n) :
    kerFrames hf hO hs p' hsub' hfs hys hsec hsurj' (p.orTransfer p' hf hys o) L hn' =
      kerFrames hf hO hs p hsub hfs hys hsec hsurj o L hn := by
  have hfin := p.finiteDimensional_of_mem_linSet hf
    (subOp_mem_linSet hf hO hs p hsub hfs hys hsec) rfl
  have hfin' := p'.finiteDimensional_of_mem_linSet hf
    (subOp_mem_linSet hf hO hs p' hsub' hfs hys hsec) rfl
  set κ := conjKerEquivOfMap (p.transferT p') (p.transferK p')
    (subOp_conj hf.isScSmooth hs p p' hsub hsub' hfs) p.T.subtypeL Subtype.val_injective
    rfl p'.T.subtypeL Subtype.val_injective rfl with hκdef
  have hκ : ∀ v, ((κ v : _) : p'.c.φ.model.E 0) = p.baseDeriv p' v := fun v => by
    obtain ⟨w, rfl⟩ := (kerEquivOfMap _ p.T.subtypeL Subtype.val_injective rfl).surjective v
    exact (coe_conjKerEquivOfMap _ _ (subOp_conj hf.isScSmooth hs p p' hsub hsub' hfs) _ _ rfl
      _ _ rfl w).trans rfl
  have hzl : levelLift p.c.φ 1 y = p.z :=
    p.c.φ.model.E.toBase_injective 1 ((A.X.PObj.toBase_levelLift p.c.isChart p.mem_source
      (smoothSet_subset_levelSet 1 hys)).trans p.toBase_z.symm)
  have hcv : ∀ α ∈ L, chartVec p'.c.isChart α = p.baseDeriv p' (chartVec p.c.isChart α) :=
    fun α hα => by
      have h := chartVec_eq_scDeriv_transition p.c.isChart p'.c.isChart (p.baseRet_retract p')
        p.mem_source p'.mem_source (hL α hα)
      rwa [hzl] at h
  have hmemN : ∀ α ∈ L, chartVec p.c.isChart α ∈
      (LinearMap.ker ((subOp hf.isScSmooth hs p hsub hfs : ↥p.T →L[ℝ] ↥p.K) :
        ↥p.T →ₗ[ℝ] ↥p.K)).map (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) := fun α hα => by
    have h : chartVec p.c.isChart α ∈ kerSet p.c f s p.z := hker ▸ mem_image_of_mem _ hα
    rw [kerSet_eq_coe_map_ker hf.isScSmooth hs p hsub hfs] at h
    exact h
  have hray := orKer_orTransfer hf hO hs p p' hsub hsub' hfs hys hsec hsurj hsurj' o
  ext v
  change v ∈ chartFrames p'.c.isChart L _ (pullOr hn' (LinearEquiv.refl ℝ _)
      (p'.orKer (p.orTransfer p' hf hys o) (subOp_mem_linSet hf hO hs p' hsub' hfs hys hsec)
        hsurj' rfl)) ↔
    v ∈ chartFrames p.c.isChart L _ (pullOr hn (LinearEquiv.refl ℝ _)
      (p.orKer o (subOp_mem_linSet hf hO hs p hsub hfs hys hsec) hsurj rfl))
  rw [hray]
  constructor
  · rintro ⟨hv, b', hb', hbo'⟩
    have hbb : (b'.map κ.symm).map κ = b' := Basis.eq_of_apply_eq fun i => by
      rw [Basis.map_apply, Basis.map_apply, LinearEquiv.apply_symm_apply]
    refine ⟨hv, b'.map κ.symm, fun i => ?_, ?_⟩
    · have hw : κ ⟨chartVec p.c.isChart (v i), hmemN _ (hv i)⟩ = b' i :=
        Subtype.ext ((hκ _).trans ((hcv _ (hv i)).symm.trans (hb' i).symm))
      rw [Basis.map_apply, ← hw, LinearEquiv.symm_apply_apply]
    · rw [← hbb] at hbo'
      exact (orientation_map_pullOr_iff hn hn' κ _ _).1 hbo'
  · rintro ⟨hv, b, hb, hbo⟩
    refine ⟨hv, b.map κ, fun i => ?_, (orientation_map_pullOr_iff hn hn' κ _ _).2 hbo⟩
    rw [Basis.map_apply, hκ, hb i, hcv _ (hv i)]

/-- **The positive frames of the kernel for `o_y ∈ Or_y^f` do not depend on the chart**: the
frames read in two charts `c`, `c'` at `y` with domains in `O` (through `toChartOr`) agree. -/
theorem kerFrames_toChartOr (hf : A.B.IsScFredholmSection f) (hO : IsOpen O)
    (hs : IsScPlusSectionOn A s O) (hfs : f y = s y) (hys : y ∈ A.X.PObj.smoothSet)
    (hsec : A.B.HasScPlusSectionsThrough) (o : Orx f hf y hys)
    {c c' : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hc' : A.B.IsChart c')
    (hyc : y ∈ c.φ.source) (hyc' : y ∈ c'.φ.source) (hsub : c.φ.source ⊆ O)
    (hsub' : c'.φ.source ⊆ O)
    (hsurj : Surjective (subOp hf.isScSmooth hs (chartPtOf c hc hyc hys) hsub hfs))
    (hsurj' : Surjective (subOp hf.isScSmooth hs (chartPtOf c' hc' hyc' hys) hsub' hfs))
    {L : Set A.X.PObj.TangentSpace}
    (hL : ∀ α ∈ L, A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y)
    (hker : chartVec c.isChart '' L = kerSet c f s (chartPtOf c hc hyc hys).z) {n : ℕ}
    (hn : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth hs (chartPtOf c hc hyc hys) hsub hfs :
      ↥(chartPtOf c hc hyc hys).T →L[ℝ] ↥(chartPtOf c hc hyc hys).K) :
        ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ] ↥(chartPtOf c hc hyc hys).K)).map
      ((chartPtOf c hc hyc hys).T.subtypeL :
        ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ] (chartPtOf c hc hyc hys).c.φ.model.E 0)) = n)
    (hn' : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth hs (chartPtOf c' hc' hyc' hys)
      hsub' hfs : ↥(chartPtOf c' hc' hyc' hys).T →L[ℝ] ↥(chartPtOf c' hc' hyc' hys).K) :
        ↥(chartPtOf c' hc' hyc' hys).T →ₗ[ℝ] ↥(chartPtOf c' hc' hyc' hys).K)).map
      ((chartPtOf c' hc' hyc' hys).T.subtypeL :
        ↥(chartPtOf c' hc' hyc' hys).T →ₗ[ℝ] (chartPtOf c' hc' hyc' hys).c.φ.model.E 0)) = n) :
    kerFrames hf hO hs (chartPtOf c' hc' hyc' hys) hsub' hfs hys hsec hsurj'
        (toChartOr hf hys c' hc' hyc' o) L hn' =
      kerFrames hf hO hs (chartPtOf c hc hyc hys) hsub hfs hys hsec hsurj
        (toChartOr hf hys c hc hyc o) L hn := by
  rw [toChartOr_eq_orTransfer hf hys o hc hc' hyc hyc']
  exact kerFrames_orTransfer hf hO hs _ _ hsub hsub' hfs hys hsec hsurj hsurj' _ hL hker hn hn'

/-- **The frames `o_{i,y}` of a structure described by kernels, read in any chart**: for
`y ∈ Mᵢ` and a strong bundle chart `c` at `y` with domain in `O`, `K.frames` are the frames of
`T_yMᵢ` whose chart vectors in `c` are a basis of `ker (f − sᵢ)'(y)` positive for the orientation
induced by `o_y`. -/
theorem KernelBranching.frames_eq_chart {Λ : A.W → ℚ≥0} {x : A.Obj}
    (K : KernelBranching A f Λ x) (hf : A.B.IsScFredholmSection f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy) {i : K.ι} {y : A.Obj}
    (hy : y ∈ K.M i) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hyc : y ∈ c.φ.source) (hsub : c.φ.source ⊆ K.O)
    (hsurj : Surjective (subOp hf.isScSmooth (K.isScPlus i)
      (chartPtOf c hc hyc (K.smooth i y hy)) hsub (K.eq_of_mem hy)))
    (hn : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth (K.isScPlus i)
        (chartPtOf c hc hyc (K.smooth i y hy)) hsub (K.eq_of_mem hy) :
        ↥(chartPtOf c hc hyc (K.smooth i y hy)).T →L[ℝ]
          ↥(chartPtOf c hc hyc (K.smooth i y hy)).K) :
        ↥(chartPtOf c hc hyc (K.smooth i y hy)).T →ₗ[ℝ]
          ↥(chartPtOf c hc hyc (K.smooth i y hy)).K)).map
      ((chartPtOf c hc hyc (K.smooth i y hy)).T.subtypeL :
        ↥(chartPtOf c hc hyc (K.smooth i y hy)).T →ₗ[ℝ]
          (chartPtOf c hc hyc (K.smooth i y hy)).c.φ.model.E 0)) = K.dim i) :
    K.frames hf hsec o i y =
      kerFrames hf K.isOpen_O (K.isScPlus i) (chartPtOf c hc hyc (K.smooth i y hy)) hsub
        (K.eq_of_mem hy) (K.smooth i y hy) hsec hsurj
        (toChartOr hf (K.smooth i y hy) c hc hyc (o y (K.smooth i y hy)))
        (A.X.PObj.submanifoldTangent (K.M i) y) hn := by
  rw [K.frames_eq hf hsec o hy]
  exact kerFrames_toChartOr hf K.isOpen_O (K.isScPlus i) (K.eq_of_mem hy) (K.smooth i y hy) hsec
    (o y (K.smooth i y hy)) hc (K.isChart_chart y) hyc (K.mem_chart (K.mem_O hy)) hsub
    (K.chart_subset y) hsurj (K.surj hf hy) (fun α hα => hα.1)
    (K.tangent_eq i y hy c hc hsub hyc _ (chartPtOf c hc hyc (K.smooth i y hy)).toBase_z) hn
    (K.finrank_ker hf hy)

end SBLocalization

end Polyfold
