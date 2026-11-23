import Polyfold.Chapter15.RestrictedOrientation
import Polyfold.Chapter15.CanonicalOrientationPullback

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702, **Theorem 15.4.1** and **Definition 15.4.2**, on the restriction `W|V → X|V` of a
strong bundle over an ep-groupoid to a saturated open set `V` (Proposition 7.1.22, p. 250).

# The formula of Theorem 15.4.1 on a saturated open set

## The text, paraphrased

(p. 702) `T̂_((f, o), Λ)(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ · (ker (f − sᵢ)'(y), o_{i,y})` in a local
sc⁺-section structure `(sᵢ, σᵢ)` of `Λ`, with `o_{i,y}` induced by `o_y`.  The formula is local:
it only involves `f`, `Λ` and `o` near `y`.

## What is formalized (namespace `Polyfold.SBLocalization`)

For `V` open and saturated, `ι : X|V → X` the inclusion (`restrFun`, by definition
`A.baseEP.subFunctor hV`), `f|V`, `Λ|V` and `o|V` (`restrSec`, `restrMult`, `restrOr`):

* `chartVec_tangent_obj_restr`, `fibreInv_tangent_obj_chartVec_restr`,
  `exists_fibreInv_tangent_obj_eq_restr`: `Tι` is the identity of the chart vectors of a chart
  `c'` of `W` inside `V` and of the carried chart of `W|V`, and `(Tι)⁻¹` maps `T_{ι y}X` onto
  `T_y(X|V)`.
* `subOp_mpullPt_restr`, `mapDomain_linW_mpullPt_restr`: the operators `(f|V − sᵢ|V)'(y)` and
  the formal sum of their oriented kernels, read through the inclusion.
* **`KernelBranching.canonSum_restrOr`**: for local branching structures described by kernels
  `K` of `(f|V, Λ|V)` and `K'` of `(f, Λ)`, `T̂_K(y) = (Tι)⁻¹ T̂_{K'}(ι y)` at every common smooth
  point.
* **`IsCanonicalFor.eq_pullSection_restr`**: a canonical orientation of `Λ|V ∘ f|V` for
  `(f|V, o|V)` is the pull-back `ι^* T̂` (Chapter 11's `pullSection`) of a canonical orientation
  of `Λ ∘ f` for `(f, o)`, at every smooth point.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}} {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V)

/-- **The inclusion `ι : X|V → X`** as a functor from the base of `A.restr hV`; by definition
`A.baseEP.subFunctor hV`. -/
abbrev restrFun : EpFunctor (A.restr hV).X A.X := A.baseEP.subFunctor hV

theorem restrFun_obj (y : (A.restr hV).Obj) : (restrFun hV).obj y = restrBase hV y := rfl

variable (hVo : IsOpen V)

include hVo

/-- The inclusion is a local sc-diffeomorphism on objects. -/
theorem isLocalScDiffeo_restrFun :
    (A.restr hV).X.PObj.IsLocalScDiffeo A.X.PObj (restrFun hV).obj :=
  A.baseEP.isLocalScDiffeo_subFunctor_obj hV hVo

/-! ### `Tι` in a chart and the carried chart -/

/-- **`Tι` is the identity of the chart vectors** of a chart `c'` of `W` with domain in `V` and
of the carried chart of `W|V`. -/
theorem chartVec_tangent_obj_restr (y : (A.restr hV).Obj)
    {c' : StrongBundleChart A.X.PObj A.P} (hsub : c'.φ.source ⊆ V)
    {α : (A.restr hV).X.PObj.TangentSpace}
    (hα : restrBase hV ((A.restr hV).X.PObj.levelVal 1 ((A.restr hV).X.PObj.tangentProj α)) ∈
      c'.φ.source) :
    chartVec c'.isChart ((restrFun hV).tangent.obj α) =
      chartVec ((restrIso hV hVo y).transportChart c' hsub).isChart α := by
  have hαU : α ∈ (A.restr hV).X.PObj.tangentPreimage univ :=
    mem_univ ((A.restr hV).X.PObj.levelVal 1 ((A.restr hV).X.PObj.tangentProj α))
  rw [EpFunctor.tangent_obj_eq_tangentMapOn (F := restrFun hV) (restrIso hV hVo y).base hαU]
  exact chartVec_tangentMapOn_of_isScDiffeoOn (restrIso hV hVo y).base c'.isChart
    ⟨mem_univ _, hα⟩

/-- The inverse `(Tι)⁻¹` on `T_{ι y}X` lands in `T_y(X|V)` and is the identity of the chart
vectors of `c'` and the carried chart. -/
theorem fibreInv_tangent_obj_chartVec_restr (y : (A.restr hV).Obj)
    {c' : StrongBundleChart A.X.PObj A.P} (hsub : c'.φ.source ⊆ V)
    (hyc' : restrBase hV y ∈ c'.φ.source) {α' : A.X.PObj.TangentSpace}
    (hα' : A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α') = restrBase hV y) :
    (A.restr hV).X.PObj.levelVal 1 ((A.restr hV).X.PObj.tangentProj
        (fibreInv (restrFun hV).tangent.obj y α')) = y ∧
      chartVec ((restrIso hV hVo y).transportChart c' hsub).isChart
          (fibreInv (restrFun hV).tangent.obj y α') = chartVec c'.isChart α' := by
  obtain ⟨h1, h2⟩ := EpFunctor.fibreInv_spec_tangent (isLocalScDiffeo_restrFun hV hVo) hα'
  refine ⟨h1, ?_⟩
  rw [← chartVec_tangent_obj_restr hV hVo y hsub (by rw [h1]; exact hyc'), h2]

/-- `(Tι)⁻¹` maps `T_{ι y}X` onto `T_y(X|V)`. -/
theorem exists_fibreInv_tangent_obj_eq_restr (y : (A.restr hV).Obj)
    {α : (A.restr hV).X.PObj.TangentSpace}
    (hα : (A.restr hV).X.PObj.levelVal 1 ((A.restr hV).X.PObj.tangentProj α) = y) :
    ∃ α', A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α') = restrBase hV y ∧
      fibreInv (restrFun hV).tangent.obj y α' = α :=
  ⟨(restrFun hV).tangent.obj α, by
    rw [EpFunctor.levelVal_tangentProj_tangent_obj, hα]; rfl,
    fibreInv_apply (EpFunctor.injOn_tangent_obj (isLocalScDiffeo_restrFun hV hVo) y) hα⟩

variable {f : A.Obj → A.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hsec : A.B.HasScPlusSectionsThrough)

include hF

/-! ### The operators `(f|V − sᵢ|V)'` in the carried chart point -/

/-- **`(f|V − s'|V)'(y)` read in the carried chart point is `(f − s')'(ι y)`** read in the
original chart point. -/
theorem subOp_mpullPt_restr {y : (A.restr hV).Obj} {s' : A.Obj → A.W} {O' : Set A.Obj}
    (hO' : IsOpen O') (hO's : O' ⊆ V) (hs' : IsScPlusSectionOn A s' O')
    (p : ChartPoint A.B (restrBase hV y)) (hp : p.c.φ.source ⊆ V) (hsub' : p.c.φ.source ⊆ O')
    (hsub : ((restrIso hV hVo y).mpullPt p hp (mem_univ y) rfl).c.φ.source ⊆
      isoSet (restrIso hV hVo y) O')
    (hfs : restrSec hV f hF.1.1.1 y = isoSec (restrIso hV hVo y) s' y)
    (hfs' : f (restrBase hV y) = s' (restrBase hV y)) (v : ↥p.T) :
    ((subOp (isScFredholmSectionFunctor_restrSec hV hVo hF).2.isScSmooth
        (isScPlusSectionOn_isoSec (restrIso hV hVo y) hO' hO's hs')
        ((restrIso hV hVo y).mpullPt p hp (mem_univ y) rfl) hsub hfs v).1 : p.c.F 0) =
      (subOp hF.2.isScSmooth hs' p hsub' hfs' v).1 :=
  congrArg (fun M : p.c.φ.model.E 0 →L[ℝ] p.c.F 0 => M v.1)
    (subDeriv_transportChart (restrIso hV hVo y) (hsub := hp) hF.2.isScSmooth
      (eqOn_restrSec hV hVo hF.1.1.1 y) hs' p.isChart hsub' p.mem_U)

include hsec

open Classical in
/-- **The formal sum of oriented kernels is carried by `(Tι)⁻¹`**: for a local sc⁺-section
structure `(sᵢ, σᵢ)` of `Λ` on `O' ⊆ V` and the carried structure of `Λ|V`, the image of
`∑ σᵢ · (f|V − sᵢ|V)'(y)` under `L ↦ (ker L, o(L))` in the carried chart point, for the carried
orientation, is the image under `(Tι)⁻¹` of the sum at `ι(y)`. -/
theorem mapDomain_linW_mpullPt_restr {y : (A.restr hV).Obj} {Λ : A.W → ℚ≥0} {O' : Set A.Obj}
    (hO' : IsOpen O') (hO's : O' ⊆ V) {k : ℕ} {sb : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    (hrep' : IsLocalRepOn A Λ O' sb σ)
    (hrep : IsLocalRepOn (A.restr hV) (restrMult hV Λ) (isoSet (restrIso hV hVo y) O')
      (fun i => isoSec (restrIso hV hVo y) (sb i)) σ)
    (p : ChartPoint A.B (restrBase hV y)) (hp : p.c.φ.source ⊆ V) (hsub' : p.c.φ.source ⊆ O')
    (hsub : ((restrIso hV hVo y).mpullPt p hp (mem_univ y) rfl).c.φ.source ⊆
      isoSet (restrIso hV hVo y) O')
    (hys : y ∈ (A.restr hV).X.PObj.smoothSet) (hys' : restrBase hV y ∈ A.X.PObj.smoothSet)
    (hlin : ((restrIso hV hVo y).mpullPt p hp (mem_univ y) rfl).linSet
      (restrSec hV f hF.1.1.1) = p.linSet f)
    (o₀ : p.Or f hF.2) :
    (linW (isScFredholmSectionFunctor_restrSec hV hVo hF).2
        (isOpen_isoSet (restrIso hV hVo y) hO') hrep
        ((restrIso hV hVo y).mpullPt p hp (mem_univ y) rfl) hsub hys
        (hasScPlusSectionsThrough_restr hV hVo hsec)).mapDomain
        (linOrTangent (isScFredholmSectionFunctor_restrSec hV hVo hF).2
          ((restrIso hV hVo y).mpullPt p hp (mem_univ y) rfl)
          ((restrIso hV hVo y).morPull (isScFredholmSectionFunctor_restrSec hV hVo hF).2 hF.2 p
            hp (mem_univ y) rfl hlin o₀)) =
      (linW hF.2 hO' hrep' p hsub' hys' hsec).mapDomain
        (fun L => (linOrTangent hF.2 p o₀ L).map (fibreInv (restrFun hV).tangent.obj y)) := by
  have hF₁ := isScFredholmSectionFunctor_restrSec hV hVo hF
  set L := restrIso hV hVo y with hL
  have hfL : EqOn (restrSec hV f hF.1.1.1) (L.Ψ ∘ f ∘ L.ϕ) univ :=
    eqOn_restrSec hV hVo hF.1.1.1 y
  have hyU : y ∈ (univ : Set (A.restr hV).Obj) := mem_univ y
  have hxO : restrBase hV y ∈ O' := hsub' p.mem_source
  have hcond : ∀ i, isoSec L (sb i) y = restrSec hV f hF.1.1.1 y ↔
      sb i (restrBase hV y) = f (restrBase hV y) := fun i => by
    have e2 : restrSec hV f hF.1.1.1 y = L.Ψ (f (restrBase hV y)) := hfL hyU
    change L.Ψ (sb i (restrBase hV y)) = restrSec hV f hF.1.1.1 y ↔ _
    rw [e2]
    constructor
    · intro h0
      have h1 := congrArg L.Φ h0
      rwa [L.zero.right_inv _ (show A.P (sb i (restrBase hV y)) ∈ V by
          rw [(hrep'.2.1 i).1 _ hxO]; exact hO's hxO),
        L.zero.right_inv _ (show A.P (f (restrBase hV y)) ∈ V by
          rw [hF.1.1.1 (restrBase hV y)]; exact hO's hxO)] at h1
    · intro h0
      rw [h0]
  unfold linW
  rw [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : sb i (restrBase hV y) = f (restrBase hV y)
  · rw [dif_pos ((hcond i).2 hi), dif_pos hi, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    refine congrArg (fun g => Finsupp.single g (σ i)) ?_
    have hτ := fun (α' : A.X.PObj.TangentSpace)
        (hα' : A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α') = restrBase hV y) =>
      fibreInv_tangent_obj_chartVec_restr hV hVo y hp p.mem_source hα'
    exact linOrTangent_mconj hF.2 hF₁.2 p (L.mpullPt p hp hyU rfl)
      (fibreInv (restrFun hV).tangent.obj y)
      (L.mcastT p hp hyU rfl) (L.mcastK p hp hyU rfl)
      (ContinuousLinearEquiv.refl ℝ (p.c.φ.model.E 0)) (fun _ => rfl)
      (fun α' hα' => ⟨(hτ α' hα').1, (hτ α' hα').2⟩)
      (fun α hα => exists_fibreInv_tangent_obj_eq_restr hV hVo y hα)
      (StrongBundle.LocalIso.mcastT_mem hlin) o₀ _ _
      (fun v => Subtype.ext (subOp_mpullPt_restr hV hVo hF hO' hO's (hrep'.2.1 i) p hp hsub'
        hsub ((hcond i).2 hi).symm hi.symm v))
  · rw [dif_neg (mt (hcond i).1 hi), dif_neg hi, Finsupp.mapDomain_zero, Finsupp.mapDomain_zero]

omit hF hsec in
/-- The chart point of Part I in the carried chart is the carried chart point. -/
theorem chartPtOf_transportChart_eq_mpullPt_restr {y : (A.restr hV).Obj}
    {c' : StrongBundleChart A.X.PObj A.P} (hc' : A.B.IsChart c') (hsub : c'.φ.source ⊆ V)
    (hyc' : restrBase hV y ∈ c'.φ.source) (hys : y ∈ (A.restr hV).X.PObj.smoothSet)
    (hys' : restrBase hV y ∈ A.X.PObj.smoothSet)
    (hc : (A.restr hV).B.IsChart ((restrIso hV hVo y).transportChart c' hsub))
    (hyc : y ∈ ((restrIso hV hVo y).transportChart c' hsub).φ.source) :
    chartPtOf ((restrIso hV hVo y).transportChart c' hsub) hc hyc hys =
      (restrIso hV hVo y).mpullPt (chartPtOf c' hc' hyc' hys') hsub (mem_univ y) rfl := by
  have hz : (exists_lift_of_smooth ((restrIso hV hVo y).transportChart c' hsub) hyc hys).choose =
      (exists_lift_of_smooth c' hyc' hys').choose := by
    refine c'.φ.model.E.toBase_injective 1
      ((exists_lift_of_smooth ((restrIso hV hVo y).transportChart c' hsub) hyc
        hys).choose_spec.trans
          (Eq.trans ?_ (exists_lift_of_smooth c' hyc' hys').choose_spec.symm))
    rfl
  unfold StrongBundle.LocalIso.mpullPt chartPtOf chartPt
  congr 1

open Classical in
/-- The sum of oriented kernels at `y` for `o|V`, in a chart point equal to the carried chart
point, is the image under `(Tι)⁻¹` of the sum at `ι(y)`. -/
theorem mapDomain_linW_of_eq_mpullPt_restr {y : (A.restr hV).Obj} {Λ : A.W → ℚ≥0}
    (o : ∀ x (hs : x ∈ A.X.PObj.smoothSet), Orx f hF.2 x hs) {O' : Set A.Obj}
    (hO' : IsOpen O') (hO's : O' ⊆ V) {k : ℕ} {sb : Fin k → A.Obj → A.W}
    {σ : Fin k → ℚ≥0} (hrep' : IsLocalRepOn A Λ O' sb σ)
    (hrep : IsLocalRepOn (A.restr hV) (restrMult hV Λ) (isoSet (restrIso hV hVo y) O')
      (fun i => isoSec (restrIso hV hVo y) (sb i)) σ)
    (p : ChartPoint A.B (restrBase hV y)) (hp : p.c.φ.source ⊆ V)
    (hsub' : p.c.φ.source ⊆ O') (hys : y ∈ (A.restr hV).X.PObj.smoothSet)
    (hys' : restrBase hV y ∈ A.X.PObj.smoothSet) (q : ChartPoint (A.restr hV).B y)
    (hq : q = (restrIso hV hVo y).mpullPt p hp (mem_univ y) rfl)
    (hsubq : q.c.φ.source ⊆ isoSet (restrIso hV hVo y) O') :
    (linW (isScFredholmSectionFunctor_restrSec hV hVo hF).2
        (isOpen_isoSet (restrIso hV hVo y) hO') hrep q hsubq hys
        (hasScPlusSectionsThrough_restr hV hVo hsec)).mapDomain
        (linOrTangent (isScFredholmSectionFunctor_restrSec hV hVo hF).2 q
          ((orxPt (A.restr hV).B y hys).orTransfer q
            (isScFredholmSectionFunctor_restrSec hV hVo hF).2 hys
            (restrOr hV hVo hF hsec o y hys))) =
      (linW hF.2 hO' hrep' p hsub' hys' hsec).mapDomain
        (fun L => (linOrTangent hF.2 p ((orxPt A.B _ hys').orTransfer p hF.2 hys'
          (o _ hys')) L).map (fibreInv (restrFun hV).tangent.obj y)) := by
  subst hq
  have hF₁ := isScFredholmSectionFunctor_restrSec hV hVo hF
  have hsec₁ := hasScPlusSectionsThrough_restr hV hVo hsec
  have hlin : ((restrIso hV hVo y).mpullPt p hp (mem_univ y) rfl).linSet
      (restrSec hV f hF.1.1.1) = p.linSet f :=
    StrongBundle.LocalIso.linSet_mpullPt hF₁.2 hF.2 (eqOn_restrSec hV hVo hF.1.1.1 y) hsec₁
      hsec hys hys'
  have e := (restrIso hV hVo y).orTransfer_mpullPt_orxViaAt hF₁.2 hF.2
    (eqOn_restrSec hV hVo hF.1.1.1 y) hsec₁ hsec (mem_univ y) hys rfl p hp (o _ hys')
  have e' : (orxPt (A.restr hV).B y hys).orTransfer
      ((restrIso hV hVo y).mpullPt p hp (mem_univ y) rfl) hF₁.2 hys
        (restrOr hV hVo hF hsec o y hys) =
      (restrIso hV hVo y).morPull hF₁.2 hF.2 p hp (mem_univ y) rfl hlin
        ((orxPt A.B _ hys').orTransfer p hF.2 hys' (o _ hys')) := e
  rw [e']
  exact mapDomain_linW_mpullPt_restr hV hVo hF hsec hO' hO's hrep' hrep p hp hsub' hsubq hys
    hys' hlin _

/-! ### The formula of Theorem 15.4.1 through the inclusion -/

/-- **2021 Theorem 15.4.1 / Definition 15.4.2 on a saturated open set** (pp. 701–702): for
`f|V`, `Λ|V` and `o|V`, the formula `∑ σᵢ · (T_yMᵢ, o_{i,y})` of a local branching structure `K`
of `Λ|V ∘ f|V` described by kernels is, at every smooth `y ∈ U(K)` with `ι(y) ∈ U(K')`, the image
under `(Tι)⁻¹` of the formula of a structure `K'` of `Λ ∘ f`. -/
theorem KernelBranching.canonSum_restrOr {Λ : A.W → ℚ≥0}
    (o : ∀ x (hs : x ∈ A.X.PObj.smoothSet), Orx f hF.2 x hs) {x : (A.restr hV).Obj}
    {x' : A.Obj} (K : KernelBranching (A.restr hV) (restrSec hV f hF.1.1.1) (restrMult hV Λ) x)
    (K' : KernelBranching A f Λ x') {y : (A.restr hV).Obj} (hyU : y ∈ K.U)
    (hyU' : restrBase hV y ∈ K'.U) (hys : y ∈ (A.restr hV).X.PObj.smoothSet) :
    K.canonSum (isScFredholmSectionFunctor_restrSec hV hVo hF).2
        (hasScPlusSectionsThrough_restr hV hVo hsec) (restrOr hV hVo hF hsec o) y =
      (K'.canonSum hF.2 hsec o (restrBase hV y)).mapDomain
        (OrTangent.map (fibreInv (restrFun hV).tangent.obj y)) := by
  classical
  have hF₁ := isScFredholmSectionFunctor_restrSec hV hVo hF
  have hsec₁ := hasScPlusSectionsThrough_restr hV hVo hsec
  set L := restrIso hV hVo y with hLdef
  have hys' : restrBase hV y ∈ A.X.PObj.smoothSet := restrBase_mem_smoothSet hV hVo hys
  have hgy : L.g (restrBase hV y) = y := L.base.left_inv y (mem_univ y)
  have hG : IsOpen (V ∩ L.g ⁻¹' K.O) :=
    L.base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage L.isOpen_U' K.isOpen_O
  have hW : IsOpen (K'.O ∩ (V ∩ L.g ⁻¹' K.O)) := K'.isOpen_O.inter hG
  have hyW : restrBase hV y ∈ K'.O ∩ (V ∩ L.g ⁻¹' K.O) :=
    ⟨K'.U_subset hyU', restrBase_mem hV y, by rw [mem_preimage, hgy]; exact K.U_subset hyU⟩
  set c' := (orChart A.B (restrBase hV y)).restrictInter hW with hc'def
  have hc' : A.B.IsChart c' :=
    StrongBundle.IsChart.restrictInter hW (isChart_orChart (B := A.B) _)
  have hyc' : restrBase hV y ∈ c'.φ.source :=
    StrongBundleChart.mem_restrictInter_source _ hW (mem_orChart _) hyW
  have hcV : c'.φ.source ⊆ K'.O ∩ (V ∩ L.g ⁻¹' K.O) :=
    StrongBundleChart.restrictInter_source_subset (orChart A.B (restrBase hV y)) hW
  have hsubK' : c'.φ.source ⊆ K'.O := fun z hz => (hcV hz).1
  have hsubU' : c'.φ.source ⊆ V := fun z hz => (hcV hz).2.1
  have hO₁ : IsOpen (K'.O ∩ V) := K'.isOpen_O.inter hVo
  have hrep₁ : IsLocalRepOn A Λ (K'.O ∩ V) K'.sAll K'.σAll :=
    K'.isLocalRep.mono hO₁ inter_subset_left
  have hrepI := isLocalRepOn_isoSec L (Λ := restrMult hV Λ) (fun _ _ => rfl) hO₁
    inter_subset_right hrep₁
  have hsub₁ : c'.φ.source ⊆ K'.O ∩ V := fun z hz => ⟨hsubK' hz, hsubU' hz⟩
  have hc : (A.restr hV).B.IsChart (L.transportChart c' hsubU') :=
    L.isChart_transportChart c' hsubU' hc'
  have hyc : y ∈ (L.transportChart c' hsubU').φ.source := ⟨mem_univ y, hyc'⟩
  have hsubI : (L.transportChart c' hsubU').φ.source ⊆ isoSet L (K'.O ∩ V) :=
    fun z hz => ⟨hz.1, hsub₁ hz.2⟩
  have hsubK : (L.transportChart c' hsubU').φ.source ⊆ K.O := fun z hz => by
    have h1 : L.g (L.ϕ z) ∈ K.O := (hcV hz.2).2.2
    rwa [L.base.left_inv z hz.1] at h1
  have e1 : K'.canonSum hF.2 hsec o (restrBase hV y) =
      Finsupp.mapRange ((↑) : ℚ≥0 → ℚ) NNRat.cast_zero
        ((linW hF.2 hO₁ hrep₁ (chartPtOf c' hc' hyc' hys') hsub₁ hys' hsec).mapDomain
          (linOrTangent hF.2 (chartPtOf c' hc' hyc' hys')
            (toChartOr hF.2 hys' c' hc' hyc' (o _ hys')))) := Finsupp.ext fun g => by
    rw [Finsupp.mapRange_apply, K'.canonSum_apply_eq hF.2 hsec o hyU' hys' hc' hyc' hsubK' g,
      linW_chartPtOf_eq hF.2 K'.isOpen_O hO₁ K'.isLocalRep hrep₁ hys' hsec hc' hyc' hsubK'
        hsub₁]
  have e2 : K.canonSum hF₁.2 hsec₁ (restrOr hV hVo hF hsec o) y =
      Finsupp.mapRange ((↑) : ℚ≥0 → ℚ) NNRat.cast_zero
        ((linW hF₁.2 (isOpen_isoSet L hO₁) hrepI
            (chartPtOf (L.transportChart c' hsubU') hc hyc hys) hsubI hys hsec₁).mapDomain
          (linOrTangent hF₁.2 (chartPtOf (L.transportChart c' hsubU') hc hyc hys)
            (toChartOr hF₁.2 hys (L.transportChart c' hsubU') hc hyc
              (restrOr hV hVo hF hsec o y hys)))) :=
    Finsupp.ext fun g => by
      rw [Finsupp.mapRange_apply, K.canonSum_apply_eq hF₁.2 hsec₁ _ hyU hys hc hyc hsubK g,
        linW_chartPtOf_eq hF₁.2 K.isOpen_O (isOpen_isoSet L hO₁) K.isLocalRep hrepI hys hsec₁
          hc hyc hsubK hsubI]
  rw [e1, e2, Finsupp.mapDomain_mapRange _ _ _ _ (fun x y => NNRat.cast_add x y),
    ← Finsupp.mapDomain_comp]
  congr 1
  exact mapDomain_linW_of_eq_mpullPt_restr hV hVo hF hsec o hO₁ inter_subset_right hrep₁
    hrepI (chartPtOf c' hc' hyc' hys') hsubU' hsub₁ hys hys' _
    (chartPtOf_transportChart_eq_mpullPt_restr hV hVo hc' hsubU' hyc' hys hys' hc hyc) hsubI

/-- **The canonical orientation on a saturated open set is the pull-back of the canonical
orientation** (2021 Theorem 15.4.1, Definition 15.4.2, with Definition 11.3.6's pull-back): if
`T̂₁` is canonical for `Λ|V ∘ f|V` and `o|V`, and `T̂` is canonical for `Λ ∘ f` and `o`, then
`T̂₁ = ι^* T̂` (Chapter 11's `pullSection`) at every smooth point of `X|V`. -/
theorem IsCanonicalFor.eq_pullSection_restr {Λ : A.W → ℚ≥0}
    {o : ∀ x (hs : x ∈ A.X.PObj.smoothSet), Orx f hF.2 x hs} {n n' : ℕ}
    {T₁ : (A.restr hV).Obj → (A.restr hV).X.PObj.OrTangent →₀ ℚ}
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}
    (hT₁ : IsCanonicalFor (restrMult hV Λ) (isScFredholmSectionFunctor_restrSec hV hVo hF).2
      (hasScPlusSectionsThrough_restr hV hVo hsec) (restrOr hV hVo hF hsec o) n T₁)
    (hT : IsCanonicalFor Λ hF.2 hsec o n' T) {y : (A.restr hV).Obj}
    (hys : y ∈ (A.restr hV).X.PObj.smoothSet) : T₁ y = (restrFun hV).pullSection T y := by
  rw [EpFunctor.pullSection_of_mem hys]
  have hys' : restrBase hV y ∈ A.X.PObj.smoothSet := restrBase_mem_smoothSet hV hVo hys
  by_cases hy : y ∈ EpGroupoid.supp
      (fun z => ((restrMult hV Λ (restrSec hV f hF.1.1.1 z) : ℚ≥0) : ℚ))
  · have hy' : restrBase hV y ∈ EpGroupoid.supp (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) := hy
    obtain ⟨K, hc, hn, hR⟩ := hT₁.2 y hy
    obtain ⟨K', hc', hn', hR'⟩ := hT.2 _ hy'
    rw [hR y K.mem_U hys, K.orientedSum_toOrientedTame]
    refine (KernelBranching.canonSum_restrOr hV hVo hF hsec o K K' K.mem_U K'.mem_U hys).trans ?_
    rw [← K'.orientedSum_toOrientedTame hc' hn', ← hR' _ K'.mem_U hys']
    rfl
  · have hy' : restrBase hV y ∉ EpGroupoid.supp (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) := hy
    rw [hT₁.1.eq_zero_of_not_mem hys hy]
    refine Eq.symm ?_
    have h0 : T (restrBase hV y) = 0 := hT.1.eq_zero_of_not_mem hys' hy'
    change (T (restrBase hV y)).mapDomain _ = 0
    rw [h0, Finsupp.mapDomain_zero]

end SBLocalization

end Polyfold
