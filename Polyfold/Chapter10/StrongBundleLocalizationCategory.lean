import Polyfold.Chapter10.StrongBundleWeakFibredProduct
import Polyfold.Chapter10.StrongBundleLocalizationExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.5 "Localization in the Strong Bundle Case" (pp. 504–508; 2017:
pp. 364–368): **Definition 10.5.1** (2021 p. 506; 2017: Definition 10.14, p. 366), the category
`SEP(F⁻¹)`, and **Remark 10.5.3** (2021 p. 506, new in the 2021 edition), the strong bundle
version of Theorem 10.3.10.  The text introduces refinements and their classes "following our
earlier construction" (p. 504) and calls the classes the morphisms of a category; the
composition, the transitivity of the equivalence and the category laws are not spelled out.  We
give them following §10.3 and Appendix 10.6.1, with the weak fibred product of strong bundles
of `StrongBundleWeakFibredProduct.lean`.

# The category of generalized strong bundle maps

## The construction

For `D : W ←Φ W'' →Ψ W'` and `E : W' ←Φ' V'' →Ψ' W'''`, the middle of the composite is
`W'' ×_{W'} V'' = πX*W''` over the weak fibred product `X'' ×_{X'} Y''` of `ψ` and `ϕ'`
(`SDiagram.compMid`), with `ΠW''` the projection of the pull-back (`compLeft`, a strong bundle
equivalence) and `ΠV''(p, w) = Φ'_{p.z}⁻¹(μ'(p.φ, Ψ(w)))` (`compRight`); the composite is
`D ∘ E = W ←(Φ∘ΠW'') W'' ×_{W'} V'' →(Ψ'∘ΠV'') W'''` (`SDiagram.comp`, representing
`[E] ∘ [D]`).

## What is formalized

* The strong bundle version of **Theorem 10.3.8** (2021 p. 488; 2017: Theorem 10.3, p. 352):
  `SDiagram.IsRefinement.comp`, `SDiagram.Equiv.comp` (the class of the composite depends only
  on the classes), `isRefinement_assoc`, `equiv_assoc` (associativity), `equiv_comp_id`,
  `equiv_id_comp` (units, from the sections `unitSection`, `unitSectionLeft` and
  `isRefinement_comp_of_section`, `isRefinement_comp_of_sectionLeft`), `equiv_ofHom_comp`,
  `equiv_comp_symm`, `equiv_symm_comp`.
* The strong bundle version of **Lemma 10.3.4** (2021 p. 485; 2017: Lemma 10.4, p. 349):
  `SDiagram.lemma_10_3_4`, `Equiv.trans`, `equivalence_equiv`, `cls_eq_cls_iff`.
* **Definition 10.5.1**: `GenSBMap.comp`, `GenSBMap.cls_comp_cls`; the `Category` instance
  `SEPLoc.category`; `SEPLoc.homMk`, `homMk_comp`, `id_eq`, `homMk_eq_homMk_iff`,
  `homMk_surjective`; the functor `SEPLoc.localizationFunctor : SEP ⥤ SEP(F⁻¹)`,
  `Ψ ↦ [W ←1 W →Ψ W']` (the analog of Theorem 10.3.14), `localizationFunctor_toPrefunctor`,
  `isInvertedBy_localizationFunctor`.
* **Remark 10.5.3** (Theorem 10.3.10 in the strong bundle case): `SEPLoc.theorem_10_3_10` (if `Ψ`
  is a strong bundle equivalence, `[D]` is an isomorphism and every inverse is
  `[W' ←Ψ W'' →Φ W]`), `isIso_of_isGeneralizedIso`, `inv_homMk`; towards the converse,
  `SEPLoc.baseFunctor : SEP(F⁻¹) ⥤ EP(E⁻¹)` and `isEquivalence_base_of_isIso` (if `[D]` is an
  isomorphism, the functor `ψ` covered by `Ψ` is an equivalence).
* Tools: `EpStrongBundle.act` (`γ · w`), `act_comp`, `act_unit`, `act_comp_inv_act`,
  `StrongBundleNatTrans.obj_eq_act`; `SEP.equivalences.of_comp_left` (two out of three);
  `SBLocalization.unitLift` (`c ↦ (f(c), 1, g(c))`).
* Satisfiability (`StrongBundleLocalizationCategoryExamples`): `isIso_homMk_negDiagram`,
  `homMk_foldDiagram_comp`, `nonempty_comp_foldDiagram`.

## Our reading

* The composite is built on the pull-back of `W''` along `πX`, so that `ΠW''` is a strong bundle
  equivalence by construction.  The squares in the proofs of Theorem 10.3.8 and of
  associativity then commute strictly, by the fibrewise injectivity of strong bundle
  equivalences (`IsStrongBundleEquivalence.eq_of_obj_eq`).
* Remark 10.5.3 says that the analog of Theorem 10.3.10 is built into Definition 10.5.2.  We
  prove that generalized strong bundle isomorphisms are isomorphisms of `SEP(F⁻¹)`.

## Not formalized

* The converse (an isomorphism of `SEP(F⁻¹)` is a generalized strong bundle isomorphism) beyond
  its base half `isEquivalence_base_of_isIso`: it would need strong bundle versions of the
  claims (C1), (C2) of Appendix 10.6.2 (pp. 515–519).
* The universal property of the localization, as in `LocalizationCategory.lean`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### The action `γ · w = μ(γ, w)` as a total function -/

section Act

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B)

namespace EpStrongBundle

open Classical in
/-- `γ · w = μ(γ, w)` if `P(w) = s(γ)`, and `w` otherwise. -/
def act (γ : Mor) (w : W) : W := if h : P w = X.src γ then E.μ ⟨(γ, w), h⟩ else w

variable {E}

theorem act_eq {γ : Mor} {w : W} (h : P w = X.src γ) : E.act γ w = E.μ ⟨(γ, w), h⟩ := by
  classical
  exact dif_pos h

theorem P_act {γ : Mor} {w : W} (h : P w = X.src γ) : P (E.act γ w) = X.tgt γ := by
  rw [act_eq h, E.P_μ]

/-- `(a ∘ b) · w = a · (b · w)` (Definition 8.3.1 (3)). -/
theorem act_comp {a b : Mor} {w : W} (hw : P w = X.src b) (hab : X.src a = X.tgt b) :
    E.act (X.comp a b) w = E.act a (E.act b w) := by
  rw [act_eq (hw.trans (X.src_comp a b hab).symm), act_eq hw,
    act_eq (show P (E.μ ⟨(b, w), hw⟩) = X.src a by rw [E.P_μ]; exact hab.symm)]
  exact E.μ_comp a b w hw hab

/-- `1 · w = w` (Definition 8.3.1 (2)). -/
theorem act_unit {x : Obj} {w : W} (h : P w = x) : E.act (X.unit x) w = w := by
  subst h
  rw [act_eq (X.src_unit (P w)).symm]
  exact E.μ_unit w

/-- `(g ∘ h⁻¹) · (h · v) = g · v`. -/
theorem act_comp_inv_act {g h : Mor} {v : W} (hv : P v = X.src h) (hg : X.src g = X.src h) :
    E.act (X.comp g (X.inv h)) (E.act h v) = E.act g v := by
  have h₁ : X.src g = X.tgt (X.inv h) := by rw [X.tgt_inv]; exact hg
  rw [← act_comp hv (by rw [X.src_comp _ _ h₁, X.src_inv]),
    X.comp_assoc _ _ _ h₁ (X.src_inv h), X.inv_comp, GroupoidStr.comp_unit_of_eq hg]

/-- A natural transformation of strong bundle functors in terms of the action: `Ψ(w) = τ(P w) ·
Φ(w)` ((10.23), Remark 10.4.9). -/
theorem StrongBundleNatTrans.obj_eq_act {Obj' Mor' : Type u} [TopologicalSpace Obj']
    [T2Space Obj'] [ParacompactSpace Obj'] [TopologicalSpace Mor'] [T2Space Mor']
    [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'} {W' : Type u} [TopologicalSpace W']
    [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'} [∀ x, AddCommGroup (P' ⁻¹' {x})]
    [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
    [ParacompactSpace (pullbackSpace P' X'.src)] {E' : EpStrongBundle X' B'}
    {ϕ ψ : EpFunctor X' X} {Φ Ψ : EpFunctor E'.toEpGroupoid E.toEpGroupoid}
    (θ : E'.StrongBundleNatTrans E ϕ ψ Φ Ψ) (w : W') :
    Ψ.obj w = E.act (θ.τ.app (P' w)) (Φ.obj w) :=
  (θ.obj_eq w).trans (act_eq _).symm

end EpStrongBundle

end Act

/-! ### `SEP`: two out of three -/

namespace SEP

variable {A A' A'' : SEP.{u}}

/-- Two out of three in `SEP` (`IsStrongBundleEquivalence.of_comp_left`). -/
theorem equivalences.of_comp_left {F : A ⟶ A'} {G : A' ⟶ A''} (hG : equivalences G)
    (hFG : equivalences (F ≫ G)) : equivalences F :=
  EpStrongBundle.IsStrongBundleEquivalence.of_comp_left hG (Hom.isStrongBundleFunctor F) hFG

end SEP

/-! ### The lift `C → A ×_Y B`, `c ↦ (f(c), 1, g(c))`, for `F ∘ f = G ∘ g` -/

namespace SBLocalization

open WeakFibredProduct EPLocalization

section UnitLift

variable {A B C Y : EP.{u}} {F : EpFunctor A.X Y.X} {G : EpFunctor B.X Y.X}
  (f : EpFunctor C.X A.X) (g : EpFunctor C.X B.X) (hfg : F.comp f = G.comp g)

include hfg in
theorem unitLift_obj_eq (c : C.Obj) : G.obj (g.obj c) = F.obj (f.obj c) :=
  (congrArg (fun K : EpFunctor C.X Y.X => K.obj c) hfg).symm

include hfg in
theorem unitLift_mor_eq (m : C.Mor) : G.mor (g.mor m) = F.mor (f.mor m) :=
  (congrArg (fun K : EpFunctor C.X Y.X => K.mor m) hfg).symm

/-- `c ↦ (f(c), 1_{F(f(c))}, g(c))`. -/
def unitLiftObj (c : C.Obj) : Obj F G :=
  Obj.mk F G (f.obj c) (Y.X.unit (F.obj (f.obj c))) (g.obj c) (Y.X.src_unit _)
    ((Y.X.tgt_unit _).trans (unitLift_obj_eq f g hfg c).symm)

/-- `m ↦ (f(m), 1_{F(f(s m))}, g(m))`. -/
def unitLiftMor (m : C.Mor) : Mor F G :=
  Mor.mk F G (f.mor m) (Y.X.unit (F.obj (f.obj (C.X.src m)))) (g.mor m)
    (by rw [Y.X.src_unit, f.src_mor])
    (by rw [Y.X.tgt_unit, g.src_mor, unitLift_obj_eq f g hfg])

/-- **The lift `C → A ×_Y B`** of `f : C → A`, `g : C → B` with `F ∘ f = G ∘ g`,
`c ↦ (f(c), 1, g(c))`; for `f = g = 1` it is the diagonal `diagFunctor`. -/
def unitLift (h : Admissible F G) : EpFunctor C.X (epGroupoid F G h) where
  obj := unitLiftObj f g hfg
  mor := unitLiftMor f g hfg
  src_mor m := Obj.ext (f.src_mor m) rfl (g.src_mor m)
  tgt_mor m := by
    refine Obj.ext (f.tgt_mor m) ?_ (g.tgt_mor m)
    change Y.X.comp (Y.X.comp (G.mor (g.mor m)) (Y.X.unit (F.obj (f.obj (C.X.src m)))))
        (Y.X.inv (F.mor (f.mor m))) = Y.X.unit (F.obj (f.obj (C.X.tgt m)))
    rw [unitLift_mor_eq f g hfg, GroupoidStr.comp_unit_of_eq (by rw [F.src_mor, f.src_mor]),
      Y.X.comp_inv, F.tgt_mor, f.tgt_mor]
  mor_comp m m' hc := by
    have hc' : src (unitLiftMor f g hfg m) = tgt (unitLiftMor f g hfg m') := by
      refine Obj.ext ((f.src_mor m).trans ((congrArg f.obj hc).trans (f.tgt_mor m').symm)) ?_
        ((g.src_mor m).trans ((congrArg g.obj hc).trans (g.tgt_mor m').symm))
      change Y.X.unit (F.obj (f.obj (C.X.src m))) =
        Y.X.comp (Y.X.comp (G.mor (g.mor m')) (Y.X.unit (F.obj (f.obj (C.X.src m')))))
          (Y.X.inv (F.mor (f.mor m')))
      rw [unitLift_mor_eq f g hfg, GroupoidStr.comp_unit_of_eq (by rw [F.src_mor, f.src_mor]),
        Y.X.comp_inv, F.tgt_mor, f.tgt_mor, hc]
    change unitLiftMor f g hfg (C.X.comp m m') =
      comp (unitLiftMor f g hfg m) (unitLiftMor f g hfg m')
    refine Mor.ext ((f.mor_comp m m' hc).trans (h_comp hc').symm) ?_
      ((g.mor_comp m m' hc).trans (k_comp hc').symm)
    rw [φ_comp hc']
    change Y.X.unit (F.obj (f.obj (C.X.src (C.X.comp m m')))) =
      Y.X.unit (F.obj (f.obj (C.X.src m')))
    rw [C.X.src_comp _ _ hc]
  mor_unit c := by
    refine Mor.ext (f.mor_unit c) ?_ (g.mor_unit c)
    change Y.X.unit (F.obj (f.obj (C.X.src (C.X.unit c)))) = Y.X.unit (F.obj (f.obj c))
    rw [C.X.src_unit]
  isScSmoothMap_obj := isScSmoothOn_obj_of h f.isScSmoothMap_obj
    (Y.X.isScSmoothMap_unit.comp (F.isScSmoothMap_obj.comp f.isScSmoothMap_obj))
    g.isScSmoothMap_obj
  isScSmoothMap_mor := isScSmoothOn_mor_of h f.isScSmoothMap_mor
    (Y.X.isScSmoothMap_unit.comp
      (F.isScSmoothMap_obj.comp (f.isScSmoothMap_obj.comp C.X.isScSmoothMap_src)))
    g.isScSmoothMap_mor

theorem projLeft_comp_unitLift (h : Admissible F G) :
    (projLeft F G h).comp (unitLift f g hfg h) = f := EpFunctor.ext rfl rfl

theorem projRight_comp_unitLift (h : Admissible F G) :
    (projRight F G h).comp (unitLift f g hfg h) = g := EpFunctor.ext rfl rfl

end UnitLift

/-! ### Composition of strong bundle diagrams -/

namespace SDiagram

open SEP EpStrongBundle

variable {A A' A'' A''' : SEP.{u}}

theorem admissible (D : SDiagram A A') (E : SDiagram A' A'') :
    Admissible (Hom.ϕ D.Ψ) (Hom.ϕ E.Φ) :=
  .of_isEquivalence_right E.hΦ.isEquivalence_base

/-- The weak fibred product `X'' ×_{X'} Y''` of the bases of `Ψ` and `Φ'`. -/
abbrev compBase (D : SDiagram A A') (E : SDiagram A' A'') : EP.{u} :=
  wfp (A := D.B.baseEP) (B := E.B.baseEP) (C := A'.baseEP) (Hom.ϕ D.Ψ) (Hom.ϕ E.Φ)
    (D.admissible E)

/-- **The middle of the composite**: the weak fibred product `W'' ×_{W'} V''` of the strong bundle
functor `Ψ : W'' → W'` and the strong bundle equivalence `Φ' : V'' → W'`, the pull-back of `W''`
along `πX : X'' ×_{X'} Y'' → X''` (`SBWeakFibredProduct`, with the roles of the factors
exchanged). -/
abbrev compMid (D : SDiagram A A') (E : SDiagram A' A'') : SEP.{u} :=
  D.B.pullbackAlong (compBase D E) (projLeft (Hom.ϕ D.Ψ) (Hom.ϕ E.Φ) (D.admissible E))

/-- The projection to `W''`, a strong bundle equivalence. -/
def compLeft (D : SDiagram A A') (E : SDiagram A' A'') : compMid D E ⟶ D.B :=
  D.B.pullbackHom (compBase D E) (projLeft (Hom.ϕ D.Ψ) (Hom.ϕ E.Φ) (D.admissible E))

theorem equivalences_compLeft (D : SDiagram A A') (E : SDiagram A' A'') :
    SEP.equivalences (compLeft D E) :=
  D.B.equivalences_pullbackHom _ (isEquivalence_projLeft E.hΦ.isEquivalence_base _)

/-- The projection to `V''`, `(p, w) ↦ Φ'_{p.z}⁻¹(μ'(p.φ, Ψ(w)))`. -/
def compRight (D : SDiagram A A') (E : SDiagram A' A'') : compMid D E ⟶ E.B :=
  coneHom E.hΦ D.Ψ (Y := compBase D E) (projLeft (Hom.ϕ D.Ψ) (Hom.ϕ E.Φ) (D.admissible E))
    (projRight (Hom.ϕ D.Ψ) (Hom.ϕ E.Φ) (D.admissible E))
    (natTrans (Hom.ϕ D.Ψ) (Hom.ϕ E.Φ) (D.admissible E))

/-- **The composite diagram** `W ←(Φ∘ΠW'') W'' ×_{W'} V'' →(Ψ'∘ΠV'') W''` of
`D : W ←Φ W'' →Ψ W'` and `E : W' ←Φ' V'' →Ψ' W''` (the strong bundle version of the composite of
Theorem 10.3.8, used in Definition 10.5.1). -/
abbrev comp (D : SDiagram A A') (E : SDiagram A' A'') : SDiagram A A'' :=
  ⟨compMid D E, compLeft D E ≫ D.Φ,
    SEP.equivalences.comp_mem _ _ (equivalences_compLeft D E) D.isEquivalence_Φ,
    compRight D E ≫ E.Ψ⟩

variable (D : SDiagram A A') (E : SDiagram A' A'')

/-- The point `p = (x'', φ, y'')` of `X'' ×_{X'} Y''` under `m`. -/
abbrev pt (m : (compMid D E).W) : Obj (Hom.ϕ D.Ψ) (Hom.ϕ E.Φ) := (compMid D E).P m

/-- The point of `W''` of `m`. -/
abbrev fib (m : (compMid D E).W) : D.B.W := (Hom.Φ (compLeft D E)).obj m

theorem P_fib (m : (compMid D E).W) : D.B.P (fib D E m) = (pt D E m).x :=
  (Hom.isStrongBundleFunctor (compLeft D E)).isStrongBundleMap_obj.covers m

theorem P_compRight (m : (compMid D E).W) :
    E.B.P ((Hom.Φ (compRight D E)).obj m) = (pt D E m).z :=
  P_coneHom E.hΦ D.Ψ _ _ _ m

theorem act_mem (m : (compMid D E).W) :
    A'.P ((Hom.Φ D.Ψ).obj (fib D E m)) = A'.X.src (pt D E m).φ := by
  rw [(pt D E m).src_φ, (Hom.isStrongBundleFunctor D.Ψ).isStrongBundleMap_obj.covers, P_fib]

/-- `Φ'(ΠV''(m)) = p.φ · Ψ(ΠW''(m))`. -/
theorem obj_compRight (m : (compMid D E).W) :
    (Hom.Φ E.Φ).obj ((Hom.Φ (compRight D E)).obj m) =
      A'.E.act (pt D E m).φ ((Hom.Φ D.Ψ).obj (fib D E m)) := by
  rw [act_eq (act_mem D E m)]
  exact obj_coneHom E.hΦ D.Ψ _ _ _ m

/-- `ΠV''(m)` is the unique `e` over `p.z` with `Φ'(e) = p.φ · Ψ(ΠW''(m))`. -/
theorem compRight_obj_eq {m : (compMid D E).W} {e : E.B.W} (hP : E.B.P e = (pt D E m).z)
    (h : (Hom.Φ E.Φ).obj e = A'.E.act (pt D E m).φ ((Hom.Φ D.Ψ).obj (fib D E m))) :
    (Hom.Φ (compRight D E)).obj m = e :=
  coneHom_obj_eq E.hΦ D.Ψ _ _ _ hP (h.trans (act_eq (act_mem D E m)))

variable {D E}

/-- **The main step of the strong bundle version of Theorem 10.3.8**: if `D'` refines `D` (by
`H`) and `E'` refines `E` (by `K`), then `D' ∘ E'` refines `D ∘ E`, by the lift of
`H ∘ ΠW` over the functor `L` of (10.28), (10.30) (`wfpMap`); its square with the projections
to the middles of `E` and `E'` commutes strictly, by the fibrewise injectivity of `Φ'`. -/
theorem IsRefinement.comp {D D' : SDiagram A A'} {E E' : SDiagram A' A''}
    (hd : D'.IsRefinement D) (he : E'.IsRefinement E) : (D'.comp E').IsRefinement (D.comp E) := by
  obtain ⟨H, hH, hHΦ, hHΨ⟩ := hd
  obtain ⟨K, hK, hKΦ, hKΨ⟩ := he
  obtain ⟨θτ⟩ := hHΨ.symm
  obtain ⟨θσ⟩ := hKΦ.symm
  let L := wfpMap (A := D.B.baseEP) (A' := D'.B.baseEP) (B := E.B.baseEP) (B' := E'.B.baseEP)
    (Y := A'.baseEP) θτ.τ θσ.τ (D.admissible E) (D'.admissible E')
  let Ht : compMid D' E' ⟶ compMid D E :=
    D.B.pullbackLiftHom (compBase D E) (projLeft (Hom.ϕ D.Ψ) (Hom.ϕ E.Φ) (D.admissible E)) L
      (compLeft D' E' ≫ H) rfl
  have e₁ : Ht ≫ compLeft D E = compLeft D' E' ≫ H := D.B.pullbackLiftHom_comp _ _ _ _ _
  have e₂ : Ht ≫ compRight D E = compRight D' E' ≫ K := by
    refine Hom.ext_obj rfl (funext fun m => ?_)
    change (Hom.Φ (compRight D E)).obj ((Hom.Φ Ht).obj m) =
      (Hom.Φ K).obj ((Hom.Φ (compRight D' E')).obj m)
    have hx := P_fib D' E' m
    have hz := P_compRight D' E' m
    refine compRight_obj_eq D E ?_ ?_
    · rw [(Hom.isStrongBundleFunctor K).isStrongBundleMap_obj.covers, hz]
      rfl
    · change (Hom.Φ (K ≫ E.Φ)).obj ((Hom.Φ (compRight D' E')).obj m) =
        A'.E.act (mapMid (A := D.B.baseEP) (A' := D'.B.baseEP) (B := E.B.baseEP)
            (B' := E'.B.baseEP) (Y := A'.baseEP) θτ.τ θσ.τ (pt D' E' m).x (pt D' E' m).φ
            (pt D' E' m).z)
          ((Hom.Φ (H ≫ D.Ψ)).obj (fib D' E' m))
      have h₁ : A'.P ((Hom.Φ D'.Ψ).obj (fib D' E' m)) = A'.X.src (pt D' E' m).φ :=
        act_mem D' E' m
      have h₂ : A'.X.src (θσ.τ.app (pt D' E' m).z) = A'.X.tgt (pt D' E' m).φ := by
        rw [θσ.τ.src_app, (pt D' E' m).tgt_φ]
      have h₃ : A'.P ((Hom.Φ D'.Ψ).obj (fib D' E' m)) = A'.X.src (θτ.τ.app (pt D' E' m).x) := by
        rw [θτ.τ.src_app, (Hom.isStrongBundleFunctor D'.Ψ).isStrongBundleMap_obj.covers, hx]
      have h₄ : A'.X.src (A'.X.comp (θσ.τ.app (pt D' E' m).z) (pt D' E' m).φ) =
          A'.X.src (θτ.τ.app (pt D' E' m).x) := by
        rw [A'.X.src_comp _ _ h₂, ← h₁, h₃]
      rw [θσ.obj_eq_act, hz, obj_compRight, ← act_comp h₁ h₂, θτ.obj_eq_act, hx, mapMid,
        act_comp_inv_act h₃ h₄]
  refine ⟨Ht, SEP.equivalences.of_comp_left (equivalences_compLeft D E) ?_, ?_, ?_⟩
  · exact (congrArg (fun F : compMid D' E' ⟶ D.B => SEP.equivalences F) e₁).mpr
      (SEP.equivalences.comp_mem _ _ (equivalences_compLeft D' E') hH)
  · change SEP.NatEquiv (Ht ≫ compLeft D E ≫ D.Φ) (compLeft D' E' ≫ D'.Φ)
    rw [← Category.assoc, e₁, Category.assoc]
    exact hHΦ.comp_left _
  · change SEP.NatEquiv (Ht ≫ compRight D E ≫ E.Ψ) (compRight D' E' ≫ E'.Ψ)
    rw [← Category.assoc, e₂, Category.assoc]
    exact hKΨ.comp_left _

/-- **The strong bundle version of Theorem 10.3.8, first claim**: the class of the composite
depends only on the classes. -/
theorem Equiv.comp {D₁ D₂ : SDiagram A A'} {E₁ E₂ : SDiagram A' A''} (hd : Equiv D₁ D₂)
    (he : Equiv E₁ E₂) : Equiv (D₁.comp E₁) (D₂.comp E₂) := by
  obtain ⟨D, hd₁, hd₂⟩ := hd
  obtain ⟨E, he₁, he₂⟩ := he
  exact ⟨D.comp E, hd₁.comp he₁, hd₂.comp he₂⟩

/-- **Associativity** (the strong bundle version of 2021 p. 514): `(D ∘ D') ∘ D''` refines
`D ∘ (D' ∘ D'')`, by the lift of `ΠW ∘ ΠW` over the reassociation `assocFunctor`; the square
with the projections to the middle of `D''` commutes strictly (fibrewise injectivity of the
equivalences of `D'` and `D''`). -/
theorem isRefinement_assoc (D : SDiagram A A') (D' : SDiagram A' A'') (D'' : SDiagram A'' A''') :
    ((D.comp D').comp D'').IsRefinement (D.comp (D'.comp D'')) := by
  let R := assocFunctor (A := D.B.baseEP) (B := D'.B.baseEP) (C := D''.B.baseEP)
    (Y := A'.baseEP) (Z := A''.baseEP) (Φ := Hom.ϕ D.Ψ) (G := Hom.ϕ D'.Φ) (Ψ := Hom.ϕ D'.Ψ)
    (H := Hom.ϕ D''.Φ) (h₁ := D.admissible D') (h₃ := D'.admissible D'')
    ((D.comp D').admissible D'') (D.admissible (D'.comp D''))
  let Rt : compMid (D.comp D') D'' ⟶ compMid D (D'.comp D'') :=
    D.B.pullbackLiftHom (compBase D (D'.comp D''))
      (projLeft (Hom.ϕ D.Ψ) (Hom.ϕ (D'.comp D'').Φ) (D.admissible (D'.comp D''))) R
      (compLeft (D.comp D') D'' ≫ compLeft D D') rfl
  have e₁ : Rt ≫ compLeft D (D'.comp D'') = compLeft (D.comp D') D'' ≫ compLeft D D' :=
    D.B.pullbackLiftHom_comp _ _ _ _ _
  have e₂ : (Rt ≫ compRight D (D'.comp D'')) ≫ compRight D' D'' =
      compRight (D.comp D') D'' := by
    refine Hom.ext_obj rfl (funext fun m => ?_)
    change (Hom.Φ (compRight D' D'')).obj ((Hom.Φ (compRight D (D'.comp D''))).obj
      ((Hom.Φ Rt).obj m)) = (Hom.Φ (compRight (D.comp D') D'')).obj m
    have hpt : pt D' D'' ((Hom.Φ (compRight D (D'.comp D''))).obj ((Hom.Φ Rt).obj m)) =
        (pt D (D'.comp D'') ((Hom.Φ Rt).obj m)).z :=
      P_compRight D (D'.comp D'') _
    have hfib : fib D' D'' ((Hom.Φ (compRight D (D'.comp D''))).obj ((Hom.Φ Rt).obj m)) =
        (Hom.Φ (compRight D D')).obj (fib (D.comp D') D'' m) := by
      refine D'.hΦ.eq_of_obj_eq ?_ ?_
      · refine (P_fib D' D'' _).trans (Eq.trans ?_ (P_compRight D D' _).symm)
        rw [hpt]
        exact (congrArg (fun p : Obj (Hom.ϕ D.Ψ) (Hom.ϕ D'.Φ) => p.z)
          (P_fib (D.comp D') D'' m)).symm
      · change (Hom.Φ (D'.comp D'').Φ).obj
            ((Hom.Φ (compRight D (D'.comp D''))).obj ((Hom.Φ Rt).obj m)) = _
        rw [obj_compRight D (D'.comp D''), obj_compRight D D']
        exact congrArg (fun p : Obj (Hom.ϕ D.Ψ) (Hom.ϕ D'.Φ) => A'.E.act p.φ
          ((Hom.Φ D.Ψ).obj (fib D D' (fib (D.comp D') D'' m)))) (P_fib (D.comp D') D'' m).symm
    refine (compRight_obj_eq (D.comp D') D'' ?_ ?_).symm
    · exact (P_compRight D' D'' _).trans
        (congrArg (fun p : Obj (Hom.ϕ D'.Ψ) (Hom.ϕ D''.Φ) => p.z) hpt)
    · rw [obj_compRight D' D'', hfib]
      exact congrArg (fun p : Obj (Hom.ϕ D'.Ψ) (Hom.ϕ D''.Φ) => A''.E.act p.φ
        ((Hom.Φ D'.Ψ).obj ((Hom.Φ (compRight D D')).obj (fib (D.comp D') D'' m)))) hpt
  refine ⟨Rt, SEP.equivalences.of_comp_left (equivalences_compLeft D (D'.comp D'')) ?_, ?_, ?_⟩
  · exact (congrArg (fun F : compMid (D.comp D') D'' ⟶ D.B => SEP.equivalences F) e₁).mpr
      (SEP.equivalences.comp_mem _ _ (equivalences_compLeft (D.comp D') D'')
        (equivalences_compLeft D D'))
  · change SEP.NatEquiv (Rt ≫ compLeft D (D'.comp D'') ≫ D.Φ)
      (compLeft (D.comp D') D'' ≫ compLeft D D' ≫ D.Φ)
    rw [← Category.assoc, e₁, Category.assoc]
    exact .refl _
  · change SEP.NatEquiv (Rt ≫ compRight D (D'.comp D'') ≫ compRight D' D'' ≫ D''.Ψ)
      (compRight (D.comp D') D'' ≫ D''.Ψ)
    rw [← e₂, Category.assoc, Category.assoc]
    exact .refl _

theorem equiv_assoc (D : SDiagram A A') (D' : SDiagram A' A'') (D'' : SDiagram A'' A''') :
    Equiv ((D.comp D').comp D'') (D.comp (D'.comp D'')) :=
  (isRefinement_assoc D D' D'').equiv

/-! ### Units -/

section Units

variable (D : SDiagram A A') (E : SDiagram A' A'')

/-- The unit section `w ↦ ((P(w), 1, P(S(w))), w)` of `ΠW'' : W'' ×_{W'} V'' → W''`, for a
strong bundle functor `S : W'' → V''` with `Φ' ∘ S = Ψ`. -/
def unitSection (S : D.B ⟶ E.B) (hS : S ≫ E.Φ = D.Ψ) : D.B ⟶ compMid D E :=
  D.B.pullbackLiftHom (compBase D E) (projLeft (Hom.ϕ D.Ψ) (Hom.ϕ E.Φ) (D.admissible E))
    (unitLift (A := D.B.baseEP) (B := E.B.baseEP) (C := D.B.baseEP) (Y := A'.baseEP)
      (EpFunctor.id _) (Hom.ϕ S)
      ((EpFunctor.ext rfl rfl : (Hom.ϕ D.Ψ).comp (EpFunctor.id _) = Hom.ϕ D.Ψ).trans
        (congrArg Hom.ϕ hS).symm) (D.admissible E))
    (𝟙 D.B) (EpFunctor.ext rfl rfl)

theorem unitSection_comp_compLeft (S : D.B ⟶ E.B) (hS : S ≫ E.Φ = D.Ψ) :
    unitSection D E S hS ≫ compLeft D E = 𝟙 D.B :=
  D.B.pullbackLiftHom_comp _ _ _ _ _

theorem equivalences_unitSection (S : D.B ⟶ E.B) (hS : S ≫ E.Φ = D.Ψ) :
    SEP.equivalences (unitSection D E S hS) :=
  SEP.equivalences.of_comp_left (equivalences_compLeft D E)
    ((congrArg (fun F : D.B ⟶ D.B => SEP.equivalences F)
      (unitSection_comp_compLeft D E S hS)).mpr (SEP.equivalences.id_mem _))

theorem unitSection_comp_compRight (S : D.B ⟶ E.B) (hS : S ≫ E.Φ = D.Ψ) :
    unitSection D E S hS ≫ compRight D E = S := by
  refine Hom.ext_obj rfl (funext fun w => ?_)
  change (Hom.Φ (compRight D E)).obj ((Hom.Φ (unitSection D E S hS)).obj w) = (Hom.Φ S).obj w
  have hw : A'.P ((Hom.Φ D.Ψ).obj w) = (Hom.ϕ D.Ψ).obj (D.B.P w) :=
    (Hom.isStrongBundleFunctor D.Ψ).isStrongBundleMap_obj.covers w
  refine compRight_obj_eq D E ((Hom.isStrongBundleFunctor S).isStrongBundleMap_obj.covers w) ?_
  exact (congrArg (fun F : D.B ⟶ A' => (Hom.Φ F).obj w) hS).trans (act_unit hw).symm

/-- **Units, right form**: if `S : W'' → V''` has `Φ' ∘ S = Ψ`, then `W ←Φ W'' →(Ψ'∘S) W''`
refines `D ∘ E` (by the unit section). -/
theorem isRefinement_comp_of_section (S : D.B ⟶ E.B) (hS : S ≫ E.Φ = D.Ψ) :
    (⟨D.B, D.Φ, D.isEquivalence_Φ, S ≫ E.Ψ⟩ : SDiagram A A'').IsRefinement (D.comp E) := by
  refine ⟨unitSection D E S hS, equivalences_unitSection D E S hS, ?_, ?_⟩
  · change SEP.NatEquiv (unitSection D E S hS ≫ compLeft D E ≫ D.Φ) D.Φ
    rw [← Category.assoc, unitSection_comp_compLeft, Category.id_comp]
    exact .refl _
  · change SEP.NatEquiv (unitSection D E S hS ≫ compRight D E ≫ E.Ψ) (S ≫ E.Ψ)
    rw [← Category.assoc, unitSection_comp_compRight]
    exact .refl _

/-- The section `v ↦ ((P(S v), 1, P(v)), S(v))` of `ΠV''`, for a strong bundle equivalence
`S : V'' → W''` with `Ψ ∘ S = Φ'`. -/
def unitSectionLeft (S : E.B ⟶ D.B) (hS : S ≫ D.Ψ = E.Φ) : E.B ⟶ compMid D E :=
  D.B.pullbackLiftHom (compBase D E) (projLeft (Hom.ϕ D.Ψ) (Hom.ϕ E.Φ) (D.admissible E))
    (unitLift (A := D.B.baseEP) (B := E.B.baseEP) (C := E.B.baseEP) (Y := A'.baseEP)
      (Hom.ϕ S) (EpFunctor.id _)
      ((congrArg Hom.ϕ hS).trans
        (EpFunctor.ext rfl rfl : Hom.ϕ E.Φ = (Hom.ϕ E.Φ).comp (EpFunctor.id _)))
      (D.admissible E))
    S (EpFunctor.ext rfl rfl)

theorem unitSectionLeft_comp_compLeft (S : E.B ⟶ D.B) (hS : S ≫ D.Ψ = E.Φ) :
    unitSectionLeft D E S hS ≫ compLeft D E = S :=
  D.B.pullbackLiftHom_comp _ _ _ _ _

theorem unitSectionLeft_comp_compRight (S : E.B ⟶ D.B) (hS : S ≫ D.Ψ = E.Φ) :
    unitSectionLeft D E S hS ≫ compRight D E = 𝟙 E.B := by
  refine Hom.ext_obj rfl (funext fun v => ?_)
  change (Hom.Φ (compRight D E)).obj ((Hom.Φ (unitSectionLeft D E S hS)).obj v) = v
  have hv : A'.P ((Hom.Φ D.Ψ).obj ((Hom.Φ S).obj v)) =
      (Hom.ϕ D.Ψ).obj ((Hom.ϕ S).obj (E.B.P v)) :=
    (Hom.isStrongBundleFunctor (S ≫ D.Ψ)).isStrongBundleMap_obj.covers v
  refine compRight_obj_eq D E rfl ?_
  exact (congrArg (fun F : E.B ⟶ A' => (Hom.Φ F).obj v) hS).symm.trans (act_unit hv).symm

/-- **Units, left form**: if `S : V'' → W''` is a strong bundle equivalence with `Ψ ∘ S = Φ'`,
then `W ←(Φ∘S) V'' →Ψ' W''` refines `D ∘ E`. -/
theorem isRefinement_comp_of_sectionLeft (S : E.B ⟶ D.B) (hS : S ≫ D.Ψ = E.Φ)
    (hS' : SEP.equivalences S) :
    (⟨E.B, S ≫ D.Φ, SEP.equivalences.comp_mem _ _ hS' D.isEquivalence_Φ, E.Ψ⟩ :
      SDiagram A A'').IsRefinement (D.comp E) := by
  refine ⟨unitSectionLeft D E S hS, SEP.equivalences.of_comp_left (equivalences_compLeft D E)
    ((congrArg (fun F : E.B ⟶ D.B => SEP.equivalences F)
      (unitSectionLeft_comp_compLeft D E S hS)).mpr hS'), ?_, ?_⟩
  · change SEP.NatEquiv (unitSectionLeft D E S hS ≫ compLeft D E ≫ D.Φ) (S ≫ D.Φ)
    rw [← Category.assoc, unitSectionLeft_comp_compLeft]
    exact .refl _
  · change SEP.NatEquiv (unitSectionLeft D E S hS ≫ compRight D E ≫ E.Ψ) E.Ψ
    rw [← Category.assoc, unitSectionLeft_comp_compRight, Category.id_comp]
    exact .refl _

end Units

/-- `D ∘ 1 ≈ D`. -/
theorem equiv_comp_id (D : SDiagram A A') : Equiv (D.comp (SDiagram.id A')) D :=
  ⟨_, isRefinement_comp_of_section D (SDiagram.id A') D.Ψ (Category.comp_id _),
    isRefinement_of_natEquiv D D.Φ D.isEquivalence_Φ _ (.refl _) (.of_eq (Category.comp_id _))⟩

/-- `1 ∘ E ≈ E`. -/
theorem equiv_id_comp (E : SDiagram A' A'') : Equiv ((SDiagram.id A').comp E) E :=
  ⟨_, isRefinement_comp_of_sectionLeft (SDiagram.id A') E E.Φ (Category.comp_id _)
      E.isEquivalence_Φ,
    isRefinement_of_natEquiv E _ _ E.Ψ (.of_eq (Category.comp_id _)) (.refl _)⟩

/-- `i(Ψ') ∘ i(Ψ) ≈ i(Ψ' ∘ Ψ)` (the functoriality of `Ψ ↦ [W ←1 W →Ψ W']`). -/
theorem equiv_ofHom_comp (F : A ⟶ A') (G : A' ⟶ A'') :
    Equiv ((ofHom F).comp (ofHom G)) (ofHom (F ≫ G)) :=
  (isRefinement_comp_of_section (ofHom F) (ofHom G) F (Category.comp_id _)).equiv.symm

/-- `D ∘ D⁻¹ ≈ 1` when `Ψ` is a strong bundle equivalence. -/
theorem equiv_comp_symm (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) :
    Equiv (D.comp (D.symm hΨ)) (SDiagram.id A) := by
  refine ⟨_, isRefinement_comp_of_section D (D.symm hΨ) (𝟙 D.B) (Category.id_comp _),
    D.Φ, D.isEquivalence_Φ, .of_eq (Category.comp_id _), ?_⟩
  change SEP.NatEquiv (D.Φ ≫ 𝟙 A) (𝟙 D.B ≫ D.Φ)
  rw [Category.comp_id, Category.id_comp]
  exact .refl _

/-- `D⁻¹ ∘ D ≈ 1` when `Ψ` is a strong bundle equivalence. -/
theorem equiv_symm_comp (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) :
    Equiv ((D.symm hΨ).comp D) (SDiagram.id A') := by
  refine ⟨_, isRefinement_comp_of_section (D.symm hΨ) D (𝟙 D.B) (Category.id_comp _),
    D.Ψ, hΨ, .of_eq (Category.comp_id _), ?_⟩
  change SEP.NatEquiv (D.Ψ ≫ 𝟙 A') (𝟙 D.B ≫ D.Ψ)
  rw [Category.comp_id, Category.id_comp]
  exact .refl _

/-- **The strong bundle version of 2021 Lemma 10.3.4, p. 485 (2017: Lemma 10.4, p. 349)**: the
equivalence of diagrams is transitive.  With `w` refining `D` (by `H`) and `D'` (by `H'`), and
`w'` refining `D'` (by `K`) and `D''` (by `K'`), the diagram on the weak fibred product
`w ×_{D'} w'` of the strong bundle equivalences `H'`, `K` (`SBWeakFibredProduct`) refines `D`
by `H ∘ ΠX` and `D''` by `K' ∘ ΠZ`. -/
theorem lemma_10_3_4 {D D' D'' : SDiagram A A'} (h : Equiv D D') (h' : Equiv D' D'') :
    Equiv D D'' := by
  obtain ⟨w, ⟨H, hH, hHΦ, hHΨ⟩, ⟨H', hH', hH'Φ, hH'Ψ⟩⟩ := h
  obtain ⟨w', ⟨K, hK, hKΦ, hKΨ⟩, ⟨K', hK', hK'Φ, hK'Ψ⟩⟩ := h'
  obtain ⟨hZ, hnat, -, -⟩ := SBWeakFibredProduct.theorem_10_2_2 hH' K
  have hX := SBWeakFibredProduct.theorem_10_2_2_right hH' K hK
  let pX := SBWeakFibredProduct.projX hH' K
  let pZ := SBWeakFibredProduct.projZ hH' K
  let e : SDiagram A A' := ⟨SBWeakFibredProduct.wfpSEP hH' K, pX ≫ w.Φ,
    SEP.equivalences.comp_mem _ _ hX w.isEquivalence_Φ, pZ ≫ w'.Ψ⟩
  refine ⟨e, ⟨pX ≫ H, SEP.equivalences.comp_mem _ _ hX hH, ?_, ?_⟩,
    ⟨pZ ≫ K', SEP.equivalences.comp_mem _ _ hZ hK', ?_, ?_⟩⟩
  · exact hHΦ.comp_left pX
  · exact (hHΨ.comp_left pX).trans ((hH'Ψ.symm.comp_left pX).trans
      ((hnat.comp_right D'.Ψ).trans (hKΨ.comp_left pZ)))
  · exact (hK'Φ.comp_left pZ).trans ((hKΦ.symm.comp_left pZ).trans
      ((hnat.symm.comp_right D'.Φ).trans (hH'Φ.comp_left pX)))
  · exact hK'Ψ.comp_left pZ

theorem Equiv.trans {D D' D'' : SDiagram A A'} (h : Equiv D D') (h' : Equiv D' D'') :
    Equiv D D'' :=
  lemma_10_3_4 h h'

theorem equivalence_equiv : _root_.Equivalence (Equiv (A := A) (A' := A')) :=
  ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- `[D] = [D']` iff `D` and `D'` have a common refinement. -/
theorem cls_eq_cls_iff {D D' : SDiagram A A'} : D.cls = D'.cls ↔ Equiv D D' :=
  ⟨fun h => equivalence_equiv.eqvGen_iff.1 (Quot.eqvGen_exact h), cls_eq_cls_of_equiv⟩

end SDiagram

/-! ### The category `SEP(F⁻¹)` -/

namespace GenSBMap

variable {A A' A'' : SEP.{u}}

/-- **The composition of generalized strong bundle maps** (2021 Definition 10.5.1, following
Theorem 10.3.8): `[E] ∘ [D] = [D ∘ E]`, well defined by `SDiagram.Equiv.comp`. -/
def comp (f : GenSBMap A A') (g : GenSBMap A' A'') : GenSBMap A A'' :=
  Quot.lift₂ (fun D E => (SDiagram.comp D E).cls)
    (fun D _ _ h => SDiagram.cls_eq_cls_of_equiv (SDiagram.Equiv.comp (.refl D) h))
    (fun _ _ E h => SDiagram.cls_eq_cls_of_equiv (SDiagram.Equiv.comp h (.refl E))) f g

theorem cls_comp_cls (D : SDiagram A A') (E : SDiagram A' A'') :
    comp D.cls E.cls = (D.comp E).cls := rfl

end GenSBMap

namespace SEPLoc

/-- **2021 Definition 10.5.1, p. 506 (2017: Definition 10.14, p. 366)**: `SEP(F⁻¹)` is a
category, with the composition `GenSBMap.comp` and the identities `[1_W]`
(the strong bundle version of Theorem 10.3.8). -/
instance category : Category.{u + 1} SEPLoc.{u} where
  toQuiver := inferInstance
  id := idHom
  comp := GenSBMap.comp
  id_comp f := by
    obtain ⟨D, rfl⟩ := SDiagram.cls_surjective f
    exact SDiagram.cls_eq_cls_of_equiv (SDiagram.equiv_id_comp D)
  comp_id f := by
    obtain ⟨D, rfl⟩ := SDiagram.cls_surjective f
    exact SDiagram.cls_eq_cls_of_equiv (SDiagram.equiv_comp_id D)
  assoc f g k := by
    obtain ⟨D, rfl⟩ := SDiagram.cls_surjective f
    obtain ⟨E, rfl⟩ := SDiagram.cls_surjective g
    obtain ⟨C, rfl⟩ := SDiagram.cls_surjective k
    exact SDiagram.cls_eq_cls_of_equiv (SDiagram.equiv_assoc D E C)

variable {A A' A'' : SEP.{u}}

/-- The generalized strong bundle map `[D] : W → W'` as a morphism of `SEP(F⁻¹)`. -/
def homMk (D : SDiagram A A') : of A ⟶ of A' := D.cls

theorem homMk_comp (D : SDiagram A A') (E : SDiagram A' A'') :
    homMk D ≫ homMk E = homMk (D.comp E) := rfl

theorem id_eq (A : SEP.{u}) : 𝟙 (of A) = homMk (SDiagram.id A) := rfl

theorem homMk_eq_homMk_iff {D D' : SDiagram A A'} : homMk D = homMk D' ↔ SDiagram.Equiv D D' :=
  SDiagram.cls_eq_cls_iff

theorem homMk_surjective {X Y : SEPLoc.{u}} (f : X ⟶ Y) :
    ∃ D : SDiagram X.toSEP Y.toSEP, homMk D = f :=
  SDiagram.cls_surjective f

/-- **The localization functor `i : SEP → SEP(F⁻¹)`**, `Ψ ↦ [W ←1 W →Ψ W']` (the strong bundle
version of Theorem 10.3.14). -/
def localizationFunctor : SEP.{u} ⥤ SEPLoc.{u} where
  obj A := of A
  map Ψ := homMk (SDiagram.ofHom Ψ)
  map_id _ := rfl
  map_comp F G := (homMk_eq_homMk_iff.2 (SDiagram.equiv_ofHom_comp F G)).symm

theorem localizationFunctor_toPrefunctor :
    localizationFunctor.toPrefunctor = localizationPrefunctor.{u} := rfl

/-- **The strong bundle version of 2021 Theorem 10.3.10, p. 489 (2017: Theorem 10.4, p. 353)**
(Remark 10.5.3), the direction proved here: if `Ψ` is a strong bundle equivalence, then
`[W ←Φ W'' →Ψ W']` is an isomorphism of `SEP(F⁻¹)`, and every inverse of it is
`[W' ←Ψ W'' →Φ W]`. -/
theorem theorem_10_3_10 (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) :
    IsIso (homMk D) ∧ ∀ g : of A' ⟶ of A, homMk D ≫ g = 𝟙 _ → g ≫ homMk D = 𝟙 _ →
      g = homMk (D.symm hΨ) := by
  have h₁ : homMk D ≫ homMk (D.symm hΨ) = 𝟙 _ :=
    homMk_eq_homMk_iff.2 (D.equiv_comp_symm hΨ)
  have h₂ : homMk (D.symm hΨ) ≫ homMk D = 𝟙 _ :=
    homMk_eq_homMk_iff.2 (D.equiv_symm_comp hΨ)
  refine ⟨⟨_, h₁, h₂⟩, fun g hg₁ hg₂ => ?_⟩
  calc g = g ≫ homMk D ≫ homMk (D.symm hΨ) := by rw [h₁, Category.comp_id]
    _ = homMk (D.symm hΨ) := by rw [← Category.assoc, hg₂, Category.id_comp]

/-- A generalized strong bundle isomorphism (Definition 10.5.2) is an isomorphism of
`SEP(F⁻¹)`. -/
theorem isIso_of_isGeneralizedIso {f : GenSBMap A A'} (hf : f.IsGeneralizedIso) :
    IsIso (show of A ⟶ of A' from f) := by
  obtain ⟨D, rfl, hΨ⟩ := hf
  exact (theorem_10_3_10 D hΨ).1

theorem inv_homMk (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) :
    have := (theorem_10_3_10 D hΨ).1
    CategoryTheory.inv (homMk D) = homMk (D.symm hΨ) := by
  have := (theorem_10_3_10 D hΨ).1
  exact IsIso.inv_eq_of_hom_inv_id (homMk_eq_homMk_iff.2 (D.equiv_comp_symm hΨ))

/-- The localization functor inverts the strong bundle equivalences. -/
theorem isInvertedBy_localizationFunctor :
    SEP.equivalences.IsInvertedBy localizationFunctor.{u} := fun _ _ _ hΨ =>
  (theorem_10_3_10 (SDiagram.ofHom _) hΨ).1

/-! ### The functor to `EP(E⁻¹)` and the base half of the converse of Theorem 10.3.10 -/

/-- **The functor `SEP(F⁻¹) → EP(E⁻¹)`**, `[D] ↦ [d]` (2021 p. 504: a generalized strong bundle
map covers a generalized map of the bases); on representatives the composite of the underlying
diagrams is the underlying diagram of the composite (`rfl`). -/
def baseFunctor : SEPLoc.{u} ⥤ EPLoc.{u} where
  obj X := EPLoc.of X.toSEP.baseEP
  map f := GenSBMap.base f
  map_id _ := rfl
  map_comp f g := by
    obtain ⟨D, rfl⟩ := SDiagram.cls_surjective f
    obtain ⟨E, rfl⟩ := SDiagram.cls_surjective g
    rfl

theorem baseFunctor_map_homMk (D : SDiagram A A') :
    baseFunctor.map (homMk D) = EPLoc.homMk D.base := rfl

/-- **The base half of the converse in the strong bundle version of Theorem 10.3.10**: if
`[W ←Φ W'' →Ψ W']` is an isomorphism of `SEP(F⁻¹)`, then the functor `ψ` of ep-groupoids
covered by `Ψ` is an equivalence (Theorem 10.3.10 for the underlying diagram). -/
theorem isEquivalence_base_of_isIso (D : SDiagram A A') (h : IsIso (homMk D)) :
    (SEP.Hom.ϕ D.Ψ).IsEquivalence := by
  have := Functor.map_isIso baseFunctor (homMk D)
  exact (EPLoc.isIso_homMk_iff D.base).1 this
end SEPLoc

end SBLocalization

/-! ### Satisfiability -/

namespace StrongBundleLocalizationCategoryExamples

open SBLocalization StrongBundleLocalizationExamples StrongBundleEquivalenceExamples

variable (n k : ℕ)

/-- **The strong bundle version of Theorem 10.3.10 for the example** `D = [(-id)*W' ←1 (-id)*W'
→P' W']` (`negDiagram`, `P'` a strong bundle equivalence): `[D]` is an isomorphism of
`SEP(F⁻¹)` with `[D⁻¹] ∘ [D] = 1`, `i(P')` is an isomorphism, and `P'` covers an equivalence. -/
theorem isIso_homMk_negDiagram :
    IsIso (SEPLoc.homMk (negDiagram n k)) ∧
      SEPLoc.homMk (negDiagram n k) ≫
        SEPLoc.homMk ((negDiagram n k).symm (negSEPHom_mem_equivalences n k)) = 𝟙 _ ∧
      IsIso (SEPLoc.localizationFunctor.map (negSEPHom n k)) ∧
      (SEP.Hom.ϕ (negSEPHom n k)).IsEquivalence := by
  have h := (SEPLoc.theorem_10_3_10 (negDiagram n k) (negSEPHom_mem_equivalences n k)).1
  exact ⟨h, SEPLoc.homMk_eq_homMk_iff.2 ((negDiagram n k).equiv_comp_symm _),
    SEPLoc.isInvertedBy_localizationFunctor _ (negSEPHom_mem_equivalences n k),
    SEPLoc.isEquivalence_base_of_isIso (negDiagram n k) h⟩

/-- **A non-trivial composite**: with `F = [W' ←P' (-id)*W' →P' W']` (`foldDiagram`), `F ∘ F = 1`
in `SEP(F⁻¹)`. -/
theorem homMk_foldDiagram_comp :
    SEPLoc.homMk (foldDiagram n k) ≫ SEPLoc.homMk (foldDiagram n k) = 𝟙 _ := by
  have h : SEPLoc.homMk (foldDiagram n k) = 𝟙 _ := cls_foldDiagram n k
  rw [h, Category.comp_id]

/-- The middle of the composite `F ∘ F` is a nonempty strong bundle (through the unit
section). -/
theorem nonempty_comp_foldDiagram :
    Nonempty ((foldDiagram n k).comp (foldDiagram n k)).B.W := by
  obtain ⟨w, -⟩ := (negSEP n k).B.surjective ((0 : Fin n → ℝ) : (negSEP n k).Obj)
  exact ⟨(SEP.Hom.Φ (SDiagram.unitSection (foldDiagram n k) (foldDiagram n k) (𝟙 _)
    (Category.id_comp _))).obj w⟩

end StrongBundleLocalizationCategoryExamples

end Polyfold
