import Polyfold.Chapter15.RestrictedBundleGeneralPosition
import Polyfold.Chapter15.CanonicalLiftContinuityLocal
import Polyfold.Chapter12.LocalOrientationEquivalenceComparison
import Polyfold.Chapter12.LocalOrientationComparisonEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5
(Lemma 12.5.1, Definition 12.5.4, pp. 592–594) and Part I, Definition 6.2.1 (p. 239),
Definition 6.6.16 (p. 274), on the restriction `W|V → X|V` of a strong bundle over an ep-groupoid
to a saturated open set `V` (Proposition 7.1.22, p. 250).

# The orientation of `f` restricted to a saturated open set

## The text, paraphrased

An orientation of an sc-Fredholm section functor `f` is a continuous section `x ↦ o_x` of the
orientation bundle `O_f → X_∞` which is invariant under the morphisms (Definition 12.5.4).  The
sets `Or_x^f` are made with sc⁺-sections defined near `x`, the morphisms act through the local
strong bundle isomorphisms `Φ̂`, and continuity is tested along sc-smooth paths; all of this is
local and compatible with local strong bundle isomorphisms.

## What is formalized (namespace `Polyfold.SBLocalization`)

For `A : SEP`, `V` open and saturated, `f|V = restrSec hV f` on `A.restr hV`, and a family
`o_y ∈ Or_y^f`:

* `restrOr`: the family `o|V`, `y ↦ (orientation map of the inclusion W|V → W)(o_y)`;
  `restrOr_eq` (it may be computed with the inclusion read at any base point).
* `isIndexAt_restrSec`: the index of `(f|V, x)` is that of `(f, x)` (Definition 6.2.1).
* **`isSectionOrientationLoc_restrOr`**: if `o` is an orientation of `f` in the sense of
  Definition 6.6.16 made with local sc⁺-sections, so is `o|V` for `f|V`.
* `germAgree₄_restrIso_mor`: the local isomorphisms of a morphism of `X|V` and of its image in
  `X` correspond under the inclusion.
* **`isOrInvariant_restrOr`**: if `o` is invariant under the morphisms of `X`, then `o|V` is
  invariant under those of `X|V`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold SEP EpStrongBundle

variable {A : SEP.{u}} {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V) (hVo : IsOpen V)
  {f : A.Obj → A.W}

include hVo

/-- A smooth point of `X|V` is a smooth point of `X`. -/
theorem restrBase_mem_smoothSet {y : (A.restr hV).Obj}
    (hy : y ∈ (A.restr hV).X.PObj.smoothSet) : restrBase hV y ∈ A.X.PObj.smoothSet :=
  ((restrIso hV hVo y).mem_smoothSet_iff (mem_univ y)).1 hy

/-- `X|V` is tame if `X` is. -/
theorem isTame_restr_of_isTame (hX : A.X.PObj.IsTame) : (A.restr hV).X.PObj.IsTame :=
  (A.baseEP.isLocalScDiffeo_subFunctor_obj hV hVo).isTame hX

/-- The inclusions `W|V → W` read at two base points have the same germ everywhere. -/
theorem germEq_restrIso (a b y : (A.restr hV).Obj) :
    StrongBundle.LocalIso.GermEq (restrIso hV hVo a) (restrIso hV hVo b) y :=
  ⟨⟨univ, isOpen_univ, mem_univ y, subset_rfl, subset_rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩

variable (hF : A.E.IsScFredholmSectionFunctor f) (hsec : A.B.HasScPlusSectionsThrough)

include hF hsec

/-- **The restriction `o|V` of a family of orientations**: `o_y ∈ Or_y^f` for `y ∈ V` read as an
orientation of `DET(f|V, y)` through the orientation map of the inclusion `W|V → W`. -/
def restrOr (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy) :
    ∀ y (hy : y ∈ (A.restr hV).X.PObj.smoothSet),
      Orx (restrSec hV f hF.1.1.1) (isScFredholmSectionFunctor_restrSec hV hVo hF).2 y hy :=
  fun y hy => (restrIso hV hVo y).orxViaAt (isScFredholmSectionFunctor_restrSec hV hVo hF).2 hF.2
    (eqOn_restrSec hV hVo hF.1.1.1 y) (hasScPlusSectionsThrough_restr hV hVo hsec) hsec
    (mem_univ y) hy rfl (o (restrBase hV y) (restrBase_mem_smoothSet hV hVo hy))

/-- `o|V` at `y` computed with the inclusion read at any base point `a`. -/
theorem restrOr_eq (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (a y : (A.restr hV).Obj) (hy : y ∈ (A.restr hV).X.PObj.smoothSet) :
    restrOr hV hVo hF hsec o y hy =
      (restrIso hV hVo a).orxViaAt (isScFredholmSectionFunctor_restrSec hV hVo hF).2 hF.2
        (eqOn_restrSec hV hVo hF.1.1.1 a) (hasScPlusSectionsThrough_restr hV hVo hsec) hsec
        (mem_univ y) hy rfl (o (restrBase hV y) (restrBase_mem_smoothSet hV hVo hy)) :=
  DFunLike.congr_fun (StrongBundle.LocalIso.orxViaAt_germ
    (isScFredholmSectionFunctor_restrSec hV hVo hF).2 hF.2 (eqOn_restrSec hV hVo hF.1.1.1 y)
    (eqOn_restrSec hV hVo hF.1.1.1 a) (hasScPlusSectionsThrough_restr hV hVo hsec) hsec
    (mem_univ y) (mem_univ y) hy rfl rfl (germEq_restrIso hV hVo y a y)) _

/-! ### The index -/

/-- **The index of `(f|V, x)` is the index of `(f, x)`** (Definition 6.2.1, p. 239): the two sets
`Lin` coincide in a chart point of `W` inside `V` and the chart point of `W|V` carried by the
inclusion. -/
theorem isIndexAt_restrSec {x : (A.restr hV).Obj} {i : ℤ}
    (hi : A.B.IsIndexAt f (restrBase hV x) i) :
    (A.restr hV).B.IsIndexAt (restrSec hV f hF.1.1.1) x i := by
  have hF₁ := isScFredholmSectionFunctor_restrSec hV hVo hF
  have hsec₁ := hasScPlusSectionsThrough_restr hV hVo hsec
  obtain ⟨s, hs, hz, -⟩ := id hi
  have hxs' : restrBase hV x ∈ A.X.PObj.smoothSet :=
    (theorem_3_1_18_preprint hF.2 hs).mem_smoothSet_of_isZeroAt hz
  have hxs : x ∈ (A.restr hV).X.PObj.smoothSet :=
    ((restrIso hV hVo x).mem_smoothSet_iff (mem_univ x)).2 hxs'
  set p := restrPt A.B (restrBase hV x) hVo (restrBase_mem hV x) hxs' with hp
  have hpV : p.c.φ.source ⊆ V := restrPt_sub _ _ _ _
  set q := (restrIso hV hVo x).mpullPt p hpV (mem_univ x) rfl with hq
  have hlin : q.linSet (restrSec hV f hF.1.1.1) = p.linSet f :=
    StrongBundle.LocalIso.linSet_mpullPt hF₁.2 hF.2 (eqOn_restrSec hV hVo hF.1.1.1 x) hsec₁ hsec
      hxs hxs'
  obtain ⟨S, hS⟩ := q.linSet_nonempty hF₁.2 hxs hsec₁
  have h1 := (q.isFredholm_isIndexAt_of_mem_linSet hF₁.2 hS).2
  have h2 := (p.fredholmIndex_of_mem_linSet hF.2 hi (hlin ▸ hS)).2
  exact h2 ▸ h1

/-! ### The continuity (Definition 6.6.16) -/

/-- **`o|V` is an orientation of `f|V` in the sense of Definition 6.6.16 made with local
sc⁺-sections, if `o` is one of `f`** (p. 274): the inclusion `W|V → W` is a local strong bundle
isomorphism, and such maps carry continuous families of orientations to continuous families
(Theorem 12.5.3, last sentence, `LocalIso.isContOn_pullLoc`). -/
theorem isSectionOrientationLoc_restrOr (hX : A.X.PObj.IsTame)
    (hft : A.B.IsScFredholmSectionTame f)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hoL : IsSectionOrientationLoc hX hft fun y hy => orxLocEquiv hft hsec y hy (o y hy)) :
    IsSectionOrientationLoc (isTame_restr_of_isTame hV hVo hX)
      (isScFredholmSectionTame_restrSec hV hVo hF.1 hft)
      fun y hy => orxLocEquiv (isScFredholmSectionTame_restrSec hV hVo hF.1 hft)
        (hasScPlusSectionsThrough_restr hV hVo hsec) y hy (restrOr hV hVo hF hsec o y hy) := by
  have hX₁ := isTame_restr_of_isTame hV hVo hX
  have hft₁ := isScFredholmSectionTame_restrSec hV hVo hF.1 hft
  have hsec₁ := hasScPlusSectionsThrough_restr hV hVo hsec
  have hcont := (isSectionOrientationLoc_iff_isContOn_univ hX hft _).1 hoL
  intro x _
  set L := restrIso hV hVo x with hL
  have hfL := eqOn_restrSec hV hVo hF.1.1.1 x
  have hpull := L.isContOn_pullLoc hX₁ hX hft₁ hft hfL hcont
  refine ⟨univ ∩ L.ϕ ⁻¹' univ, ⟨mem_univ x, mem_univ _⟩, ?_⟩
  have heq : (fun y hy => orxLocEquiv hft₁ hsec₁ y hy (restrOr hV hVo hF hsec o y hy)) =
      L.pullLoc hft₁ hft hfL (fun y hy => orxLocEquiv hft hsec y hy (o y hy)) := by
    funext y hy
    have hy' : restrBase hV y ∈ A.X.PObj.smoothSet := restrBase_mem_smoothSet hV hVo hy
    rw [L.pullLoc_of_mem hft₁ hft hfL _ (mem_univ y) hy hy', restrOr_eq hV hVo hF hsec o x y hy]
    exact DFunLike.congr_fun (L.orxLocEquiv_orxViaAt hft₁ hft hfL hsec₁ hsec (mem_univ y) rfl hy
      hy') (o (restrBase hV y) hy')
  rw [heq]
  exact hpull

/-! ### The invariance under the morphisms (Definition 12.5.4) -/

omit hF hsec in
/-- **The local isomorphisms of a morphism of `X|V` and of its image in `X` correspond under
the inclusion**: the composites of the inclusion with `Φ̂_α` and of `Φ̂_{ι(α)}` with the inclusion
have the same germ at `t(α)`. -/
theorem germAgree₄_restrIso_mor (α : (A.restr hV).Mor) (a b : (A.restr hV).Obj) :
    StrongBundle.LocalIso.GermAgree₄ (restrIso hV hVo a) ((A.restr hV).E.morIso α)
      (A.E.morIso ((A.baseEP.subFunctor hV).mor α)) (restrIso hV hVo b)
      ((A.restr hV).X.tgt α) := by
  set ϕ : EpFunctor (A.restr hV).X A.X := A.baseEP.subFunctor hV with hϕ
  set S := (A.restr hV).X.sheetAt α with hS
  set S' := A.X.sheetAt (ϕ.mor α) with hS'
  have hτc : ContinuousOn S.tgtInv S.tgtSet := S.isScDiffeoOn_tgt.isScSmoothOn_inv.continuousOn
  have hϕc : Continuous ϕ.mor := continuousOn_univ.1 ϕ.isScSmoothMap_mor.continuousOn
  have hO₁ : IsOpen (S.tgtSet ∩ S.tgtInv ⁻¹' (ϕ.mor ⁻¹' S'.carrier)) :=
    hτc.isOpen_inter_preimage S.isScDiffeoOn_tgt.isOpen_target
      (S'.isScDiffeoOn_tgt.isOpen_source.preimage hϕc)
  set N := S.tgtSet ∩ S.tgtInv ⁻¹' (ϕ.mor ⁻¹' S'.carrier) with hN
  have key : ∀ y ∈ N, S'.tgtInv (ϕ.obj y) = ϕ.mor (S.tgtInv y) ∧ ϕ.obj y ∈ S'.tgtSet := by
    rintro y ⟨hyT, hyC⟩
    have hm' : ϕ.mor (S.tgtInv y) ∈ S'.carrier := hyC
    have ht : A.X.tgt (ϕ.mor (S.tgtInv y)) = ϕ.obj y :=
      (ϕ.tgt_mor _).trans (congrArg ϕ.obj (S.isScDiffeoOn_tgt.right_inv y hyT))
    refine ⟨?_, ht ▸ S'.isScDiffeoOn_tgt.mapsTo hm'⟩
    rw [← ht]; exact S'.isScDiffeoOn_tgt.left_inv _ hm'
  refine ⟨⟨N, hO₁, ?_, fun y hy => hy.1, fun y _ => mem_univ y, fun y hy => ?_,
    fun w hw => ?_⟩⟩
  · refine ⟨EpStrongBundle.mem_tgtSet rfl, ?_⟩
    change ϕ.mor (S.tgtInv ((A.restr hV).X.tgt α)) ∈ S'.carrier
    rw [EpStrongBundle.tgtInv_tgt]; exact A.X.mem_sheetAt _
  · obtain ⟨h1, -⟩ := key y hy
    change ϕ.obj ((A.restr hV).X.src (S.tgtInv y)) = A.X.src (S'.tgtInv (ϕ.obj y))
    rw [h1]; exact (ϕ.src_mor _).symm
  · obtain ⟨h1, h2⟩ := key ((A.restr hV).P w) hw
    have hw1 : (A.restr hV).P w =
        (A.restr hV).X.src (EpStrongBundle.morInvSec (A.restr hV).X α ((A.restr hV).P w)) :=
      (EpStrongBundle.src_morInvSec α hw.1).symm
    have hcov : A.P (restrFib hV w) = ϕ.obj ((A.restr hV).P w) := P_restrFib hV w
    have hw2 : A.P (restrFib hV w) =
        A.X.src (EpStrongBundle.morInvSec A.X (ϕ.mor α) (A.P (restrFib hV w))) :=
      (EpStrongBundle.src_morInvSec (ϕ.mor α) (hcov ▸ h2)).symm
    change restrFib hV ((A.restr hV).E.sectionAct (EpStrongBundle.morInvSec (A.restr hV).X α) w) =
      A.E.sectionAct (EpStrongBundle.morInvSec A.X (ϕ.mor α)) (restrFib hV w)
    rw [(A.restr hV).E.sectionAct_of_eq _ hw1, A.E.sectionAct_of_eq _ hw2]
    refine ((Hom.isStrongBundleFunctor (A.restrHom hV)).isMap.map_μ _ _ _).trans ?_
    refine A.E.μ_mk_congr ?_ rfl _ _
    change ϕ.mor ((A.restr hV).X.inv (S.tgtInv ((A.restr hV).P w))) =
      A.X.inv (S'.tgtInv (A.P (restrFib hV w)))
    rw [hcov, h1]
    exact ϕ.toGroupoidFunctor.mor_inv _

/-- **`o|V` is invariant under the morphisms of `X|V` if `o` is invariant under those of `X`**
(Definition 12.5.4, p. 594): `φ_*` is the orientation map of the local isomorphism of `φ`, and
the square of the inclusion and these isomorphisms commutes as germs. -/
theorem isOrInvariant_restrOr (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hinv : A.E.IsOrInvariant hF hsec o) :
    (A.restr hV).E.IsOrInvariant (isScFredholmSectionFunctor_restrSec hV hVo hF)
      (hasScPlusSectionsThrough_restr hV hVo hsec) (restrOr hV hVo hF hsec o) := by
  have hF₁ := isScFredholmSectionFunctor_restrSec hV hVo hF
  have hsec₁ := hasScPlusSectionsThrough_restr hV hVo hsec
  set ϕ : EpFunctor (A.restr hV).X A.X := A.baseEP.subFunctor hV with hϕ
  intro α y y' hy hy' hs hs'
  subst hy hy'
  have hbs : restrBase hV ((A.restr hV).X.src α) ∈ A.X.PObj.smoothSet :=
    restrBase_mem_smoothSet hV hVo hs
  have hbs' : restrBase hV ((A.restr hV).X.tgt α) ∈ A.X.PObj.smoothSet :=
    restrBase_mem_smoothSet hV hVo hs'
  have hsrc : A.X.src (ϕ.mor α) = restrBase hV ((A.restr hV).X.src α) := ϕ.src_mor α
  have htgt : A.X.tgt (ϕ.mor α) = restrBase hV ((A.restr hV).X.tgt α) := ϕ.tgt_mor α
  have hsq := StrongBundle.LocalIso.orxViaAt_square
    (L := restrIso hV hVo ((A.restr hV).X.src α)) (L₂ := (A.restr hV).E.morIso α)
    (M := A.E.morIso (ϕ.mor α)) (M₂ := restrIso hV hVo ((A.restr hV).X.tgt α))
    hF₁.2 hF₁.2 hF.2 hF.2 (eqOn_restrSec hV hVo hF.1.1.1 _)
    ((A.restr hV).E.eqOn_morIso_of_functor hF₁ α) (A.E.eqOn_morIso_of_functor hF (ϕ.mor α))
    (eqOn_restrSec hV hVo hF.1.1.1 _) hsec₁ hsec₁ hsec hsec
    (b := (A.restr hV).X.tgt α) (EpStrongBundle.mem_tgtSet rfl) (mem_univ _) hs'
    ((A.restr hV).E.morIso_ϕ_eq rfl rfl) rfl (mem_univ _) (EpStrongBundle.mem_tgtSet htgt) rfl
    (A.E.morIso_ϕ_eq hsrc htgt)
    (germAgree₄_restrIso_mor hV hVo α _ _)
  have h2 := hinv (ϕ.mor α) hsrc htgt hbs hbs'
  rw [A.E.orMor_eq_orxViaAt hF hsec (ϕ.mor α) hsrc htgt hbs hbs'] at h2
  have h1 := DFunLike.congr_fun hsq (o _ hbs)
  have h3 := congrArg ((restrIso hV hVo ((A.restr hV).X.tgt α)).orxViaAt hF₁.2 hF.2
      (eqOn_restrSec hV hVo hF.1.1.1 _) hsec₁ hsec (mem_univ _) hs' rfl) h2
  rw [(A.restr hV).E.orMor_eq_orxViaAt hF₁ hsec₁ α rfl rfl hs hs']
  exact h1.trans h3

end SBLocalization

end Polyfold
