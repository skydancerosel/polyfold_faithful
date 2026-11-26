import Polyfold.Chapter16.StrongPolyfoldBundle
import Polyfold.Chapter16.ZhouUniquenessCheck
import Polyfold.Chapter8.ZhouGroupoid
import Polyfold.Chapter10.EquivalenceReduced
import Polyfold.Chapter10.StrongBundleWeakFibredProduct
import Polyfold.Chapter10.StrongBundleEquivalenceExamples
import Polyfold.Chapter6.IntervalEndInclusion
import Polyfold.Chapter5.SmoothSetMaps

/-!
Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I: The Polyfolds of Gromov–Witten
Theory*, Memoirs AMS 248 (2017), §2.2 (pp. 33–38): **Definition 2.28** (ep-groupoids), the
equivalences of ep-groupoids and polyfold structures before **Definition 2.29**, **Definition
2.29** (polyfolds), the strong bundle `(E, μ)` over an ep-groupoid of **Definition 2.37**, and
**Definition 2.38** (strong polyfold bundle structures), compared with the book (*Polyfold and
Fredholm Theory*, Springer 2021): Definitions 7.1.3, 10.1.1, 8.3.1, 16.1.1, 16.1.2, 16.3.1.

# Polyfold and strong polyfold bundle structures in the memoir's form

## The memoir, paraphrased

(Definition 2.28) An ep-groupoid: M-polyfold structures on objects and morphisms, the structure
maps sc-smooth, `s, t` surjective local sc-diffeomorphisms, and every `x` has an open `V(x)` with
`t : s⁻¹(V(x)) → X` proper.  (p. 34) An equivalence `F : X → Y`: (1) a local sc-diffeomorphism
on objects and on morphisms, (2) `|F|` a homeomorphism, (3) `G(x) → G(F(x))` an isomorphism.  A
polyfold structure on a paracompact Hausdorff `Z` is `(X, β)` with `β : |X| → Z` a homeomorphism;
`(X, β) ∼ (X', β')` if a third structure `(X'', β'')` and equivalences `F : X'' → X`,
`F' : X'' → X'` have `β'' = β ∘ |F| = β' ∘ |F'|`.  (Definition 2.29) A polyfold is a paracompact
Hausdorff `Z` with an equivalence class of polyfold structures.  (pp. 37–38) `μ : X ₛ×_p E → E`
covers `t`, with (1) `μ` a local sc-diffeomorphism of `E(i)` onto `E(i)`, `i = 0, 1`, linear on
the fibres; (2) `μ(1_x, e) = e`; (3) `μ(h ∘ g, e) = μ(h, μ(g, e))` for `s(h) = t(g)` and
`s(t) = p(e)`; "(1) is a consequence of (2) and (3)".  (Definition 2.37) Such `(E, μ)` is a strong
bundle over the ep-groupoid.  (Definition 2.38) For a continuous surjection `p : W → Z` of
paracompact Hausdorff spaces, a strong polyfold bundle structure is `(P : E → X, Γ, γ)` with
homeomorphisms `Γ : |E| → W`, `γ : |X| → Z` and `p ∘ Γ = γ ∘ |P|`.

## What is formalized (namespace `GWMemoir`)

* `MemoirProper`, `exists_isProperMap_closure_of_memoirProper` (**Definition 2.28**: the memoir's
  properness gives the book's Definition 7.1.3 (3)), `epGroupoidOfMemoir`, the witness
  `memoirProper_action`; `memoir_definition_2_28_surjective` (the surjectivity of `s, t` follows
  from the units).
* `IsMemoirEquivalence`, **`isMemoirEquivalence_iff`**: the memoir's equivalences are the book's
  (Definition 10.1.1).
* `MemoirPolyfoldStructure`, `MemoirEquiv`, **`memoirEquiv_iff`** (the third-structure relation is
  the book's generalized-isomorphism relation of Definition 16.1.2), `MemoirPolyfoldClass`
  (**Definition 2.29**); `hasParacompactOrbitSpace` (**paracompactness of `|X|` follows**, from
  `Z`), `toPolyfoldStructure` (with (ZHOU) one has a book structure), `ofPolyfoldStructure`,
  **`ofPolyfoldStructure_equiv_iff`** (the two relations agree on book structures), and
  **`memoir_definition_2_29_not_isZhou`**: (ZHOU) does not follow (Appendix 7.6.3's groupoid).
* `memoir_definition_2_37_three_mem`, **`memoir_definition_2_37_iff`** (Definition 2.37 with (3)
  read as `s(g) = p(e)`, level `0` of (1): the book's Definition 8.3.1, surjectivity of `μ` from
  (2)).
* `MemoirStrongPolyfoldBundleStructure` (**Definition 2.38**), `hasParacompactOrbitSpace`,
  `toStrongPolyfoldBundleStructure` (with (ZHOU) and Definition 8.4.2), `ofStrongPolyfoldBundle
  Structure`, and **`memoir_definition_2_38_not_isZhou`**.

## Readings

* Definition 2.37 (3) prints `s(t) = p(e)`; `t` is the target map, not a morphism.  We read
  `s(g) = p(e)`: it is the condition `(g, e) ∈ X ₛ×_p E` under which `μ(g, e)` is defined, and
  then `p(μ(g, e)) = t(g) = s(h)` makes `μ(h, μ(g, e))` and `μ(h ∘ g, e)` defined
  (`memoir_definition_2_37_three_mem`).
* The level-`1` half of (1) and the claim that (1) follows from (2), (3) are not formalized: the
  missing lemma is that `e ↦ (τ⁻¹(p e), μ((τ⁻¹(p e))⁻¹, e))` is sc-smooth into the sub-M-polyfold
  `X ₛ×_p E` (and on `E(1)`).
* The memoir's Definition 2.38 does not ask for (ZHOU), a paracompact `|X|` (which follows) or the
  local regularity property (Definition 8.4.2).  Whether Definition 8.4.2 follows from the
  memoir's conditions with (ZHOU) is not settled here: an example needs a strong bundle
  isomorphism of the pull-back bundle over a groupoid without (LR) (`ZhouExample.not_isLR`).
* The memoir refers the equivalence of strong polyfold bundle structures to its reference [24];
  we use the book's Definition 16.3.3 for it.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory TopologicalSpace

noncomputable section

namespace GWMemoir

open Polyfold EPLocalization SBLocalization

universe u

/-! ### Definition 2.28: the properness condition -/

section Def228

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Memoir Definition 2.28 (proper), p. 33**: every object `x` has an open `V(x) ∋ x` with
`t : s⁻¹(V(x)) → X` proper (the book's Definition 7.1.3 (3) asks this on `s⁻¹(cl V(x))`). -/
def MemoirProper (G : GroupoidStr Obj Mor) : Prop :=
  ∀ x : Obj, ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧ IsProperMap ((G.src ⁻¹' V).domRestrict G.tgt)

omit [T2Space Mor] [ParacompactSpace Mor] in
/-- **The memoir's properness gives the book's** (Definition 7.1.3 (3), 2021 p. 226): shrink
`V(x)` to an open `V' ∋ x` with `cl V' ⊆ V(x)` (`X` is regular); `s⁻¹(cl V')` is closed in
`s⁻¹(V(x))`, and the restriction of a proper map to a closed subset is proper. -/
theorem exists_isProperMap_closure_of_memoirProper {G : GroupoidStr Obj Mor}
    (hs : Continuous G.src) (h : MemoirProper G) (x : Obj) :
    ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧ IsProperMap ((G.src ⁻¹' closure V).domRestrict G.tgt) := by
  obtain ⟨V, hV, hxV, hp⟩ := h x
  obtain ⟨t, ht, htc, htV⟩ := exists_mem_nhds_isClosed_subset (hV.mem_nhds hxV)
  have hsub : closure (interior t) ⊆ V :=
    (closure_minimal interior_subset htc).trans htV
  refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht, ?_⟩
  have hi : G.src ⁻¹' closure (interior t) ⊆ G.src ⁻¹' V := preimage_mono hsub
  have hemb : IsClosedEmbedding (Set.inclusion hi) := by
    refine ⟨IsEmbedding.inclusion hi, ?_⟩
    have : range (Set.inclusion hi) =
        (fun y : G.src ⁻¹' V => G.src y.1) ⁻¹' closure (interior t) := by
      ext y
      refine ⟨?_, fun hy => ⟨⟨y.1, hy⟩, rfl⟩⟩
      rintro ⟨z, rfl⟩
      exact z.2
    rw [this]
    exact isClosed_closure.preimage (hs.comp continuous_subtype_val)
  exact hp.comp hemb.isProperMap

/-- **Memoir Definition 2.28 as an ep-groupoid of the book**: the data of Definition 7.1.3 with
the memoir's properness condition. -/
def epGroupoidOfMemoir (G : GroupoidStr Obj Mor) (PObj : MPolyfold Obj) (PMor : MPolyfold Mor)
    (hs : PMor.IsLocalScDiffeo PObj G.src) (ht : PMor.IsLocalScDiffeo PObj G.tgt)
    (hu : PObj.IsScSmoothMap PMor G.unit) (hi : PMor.IsScSmoothMap PMor G.inv)
    (hp : MemoirProper G) (hm : IsScSmoothComp PObj PMor G.src G.tgt G.comp hs ht.isScSmoothMap) :
    EpGroupoid Obj Mor where
  toGroupoidStr := G
  PObj := PObj
  PMor := PMor
  isLocalScDiffeo_src := hs
  isLocalScDiffeo_tgt := ht
  isScSmoothMap_unit := hu
  isScSmoothMap_inv := hi
  exists_isProperMap := exists_isProperMap_closure_of_memoirProper hs.continuous hp
  isScSmoothComp := hm

/-- **Memoir Definition 2.28, "surjective"**: `s` and `t` of an ep-groupoid are surjective
(`s(1_x) = t(1_x) = x`); the book does not list it. -/
theorem memoir_definition_2_28_surjective (X : EpGroupoid Obj Mor) :
    Surjective X.src ∧ Surjective X.tgt :=
  ⟨fun x => ⟨X.unit x, X.src_unit x⟩, fun x => ⟨X.unit x, X.tgt_unit x⟩⟩

/-- **Witness for `MemoirProper`**: the translation groupoid `K ⋉ U` of a finite group, with
`V(x) = U`. -/
theorem memoirProper_action {K U : Type u} [Group K] [Finite K] [TopologicalSpace K]
    [DiscreteTopology K] [TopologicalSpace U] [T2Space U] [ParacompactSpace U] [MulAction K U]
    {P : MPolyfold U} (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y) :
    MemoirProper (EpGroupoid.Examples.actionEpGroupoid hP).toGroupoidStr := fun _ =>
  ⟨univ, isOpen_univ, mem_univ _,
    (EpGroupoid.Examples.action_isProperMap_tgt hP).restrict (isClosed_univ.preimage
      continuous_snd)⟩

end Def228

/-! ### The memoir's equivalences of ep-groupoids (p. 34) -/

section Equivalences

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- **The memoir's equivalence of ep-groupoids** (p. 34): an sc-smooth functor `F : X → Y` which
(1) is a local sc-diffeomorphism on objects and on morphisms, (2) induces a homeomorphism
`|F| : |X| → |Y|`, (3) induces isomorphisms `G(x) → G(F(x))`. -/
structure IsMemoirEquivalence (F : EpFunctor X Y) : Prop where
  isLocalScDiffeo_obj : X.PObj.IsLocalScDiffeo Y.PObj F.obj
  isLocalScDiffeo_mor : X.PMor.IsLocalScDiffeo Y.PMor F.mor
  isHomeomorph_orbitMap : IsHomeomorph F.orbitMap
  bijective_isotropyHom : ∀ x, Bijective (F.isotropyHom x)

/-- **The memoir's equivalences are the book's** (Definition 10.1.1, 2021 p. 461: full,
faithful, `|F|` a homeomorphism, a local sc-diffeomorphism on objects).  Full: for
`ψ : F(x) → F(x')`, injectivity of `|F|` gives `φ : x → x'`, and `F(φ)⁻¹ ∘ ψ = F(g)` for some
`g ∈ G(x)`, so `ψ = F(φ ∘ g)`.  Faithful: `F(φ'⁻¹ ∘ φ) = 1` forces `φ'⁻¹ ∘ φ = 1`. -/
theorem isMemoirEquivalence_iff (F : EpFunctor X Y) : IsMemoirEquivalence F ↔ F.IsEquivalence := by
  refine ⟨fun h => ?_, fun h => ⟨h.isLocalScDiffeo_obj, F.isLocalScDiffeo_mor h.isLocalScDiffeo_obj,
    h.isHomeomorph_orbitMap, h.bijective_isotropyHom⟩⟩
  refine ⟨(F.full_iff).2 fun x x' ψ hs ht => ?_, (F.faithful_iff).2 fun φ φ' hs ht he => ?_,
    h.isHomeomorph_orbitMap, h.isLocalScDiffeo_obj⟩
  · have hπ : X.π x = X.π x' := by
      apply h.isHomeomorph_orbitMap.injective
      rw [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π]
      exact (GroupoidStr.π_eq_π_iff _).2 ⟨ψ, hs, ht⟩
    obtain ⟨φ, hφs, hφt⟩ := (GroupoidStr.π_eq_π_iff _).1 hπ
    have h1 : Y.src (Y.inv (F.mor φ)) = Y.tgt ψ := by
      rw [Y.src_inv, F.tgt_mor, hφt, ht]
    let g : Y.Isotropy (F.obj x) :=
      ⟨Y.comp (Y.inv (F.mor φ)) ψ, by rw [Y.src_comp _ _ h1, hs],
        by rw [Y.tgt_comp _ _ h1, Y.tgt_inv, F.src_mor, hφs]⟩
    obtain ⟨a, ha⟩ := (h.bijective_isotropyHom x).2 g
    have ha' : F.mor a.val = Y.comp (Y.inv (F.mor φ)) ψ := congrArg GroupoidStr.Isotropy.val ha
    have h2 : X.src φ = X.tgt a.val := hφs.trans a.tgt_val.symm
    refine ⟨X.comp φ a.val, by rw [X.src_comp _ _ h2, a.src_val], by rw [X.tgt_comp _ _ h2, hφt],
      ?_⟩
    rw [F.mor_comp _ _ h2, ha', ← Y.comp_assoc _ _ _ (by rw [Y.tgt_inv]) h1, Y.comp_inv,
      F.tgt_mor, hφt, ← ht, Y.unit_comp]
  · have h1 : X.src (X.inv φ') = X.tgt φ := by rw [X.src_inv, ht]
    let a : X.Isotropy (X.src φ) :=
      ⟨X.comp (X.inv φ') φ, X.src_comp _ _ h1, by rw [X.tgt_comp _ _ h1, X.tgt_inv, hs]⟩
    have ha : F.isotropyHom (X.src φ) a = F.isotropyHom (X.src φ) 1 := by
      apply GroupoidStr.Isotropy.ext
      rw [EpFunctor.isotropyHom_val, EpFunctor.isotropyHom_val, F.mor_comp _ _ h1,
        F.mor_inv, he, Y.inv_comp, GroupoidStr.Isotropy.val_one, F.mor_unit, F.src_mor, hs]
    have ha1 : X.comp (X.inv φ') φ = X.unit (X.src φ) :=
      congrArg GroupoidStr.Isotropy.val ((h.bijective_isotropyHom _).1 ha)
    calc φ = X.comp φ' (X.comp (X.inv φ') φ) := by
            rw [← X.comp_assoc _ _ _ (by rw [X.tgt_inv]) h1, X.comp_inv, ← ht, X.unit_comp]
      _ = φ' := by rw [ha1, hs, X.comp_unit]

end Equivalences

/-! ### Polyfold structures and Definition 2.29 -/

/-- **A polyfold structure in the memoir's sense** (p. 34): on a paracompact Hausdorff space
`Z`, a pair `(X, β)` of an ep-groupoid `X` and a homeomorphism `β : |X| → Z`.  Unlike the book's
Definition 16.1.1 (`PolyfoldStructure`) it asks neither (ZHOU) nor a paracompact `|X|`. -/
structure MemoirPolyfoldStructure (Z : Type u) [TopologicalSpace Z] [ParacompactSpace Z]
    [T2Space Z] : Type (u + 1) where
  /-- The ep-groupoid. -/
  X : EP.{u}
  /-- The homeomorphism `β : |X| → Z`. -/
  β : X.X.OrbitSpace ≃ₜ Z

namespace MemoirPolyfoldStructure

variable {Z : Type u} [TopologicalSpace Z] [ParacompactSpace Z] [T2Space Z]

/-- The pair `(X, β)` of the book's Remark 10.3.18. -/
def toOrbitChart (p : MemoirPolyfoldStructure Z) : OrbitChart Z := ⟨p.X, p.β⟩

/-- **The paracompactness of `|X|` follows**: `|X|` is homeomorphic to the paracompact `Z`.
(The memoir's Remark 2.30 leaves the paracompactness of `|X|` open for a general ep-groupoid; for
a polyfold structure it is built in through `Z`.) -/
theorem hasParacompactOrbitSpace (p : MemoirPolyfoldStructure Z) :
    p.X.X.HasParacompactOrbitSpace :=
  p.β.paracompactSpace_iff.2 inferInstance

/-- **The memoir's equivalence of polyfold structures** (p. 34): a third structure `(X'', β'')`
and equivalences `F : X'' → X`, `F' : X'' → X'` (in the memoir's sense) with
`β'' = β ∘ |F| = β' ∘ |F'|`. -/
def MemoirEquiv (p q : MemoirPolyfoldStructure Z) : Prop :=
  ∃ (r : MemoirPolyfoldStructure Z) (F : EpFunctor r.X.X p.X.X) (F' : EpFunctor r.X.X q.X.X),
    IsMemoirEquivalence F ∧ IsMemoirEquivalence F' ∧
      ⇑r.β = ⇑p.β ∘ F.orbitMap ∧ ⇑r.β = ⇑q.β ∘ F'.orbitMap

/-- **The two notions of equivalence agree**: the memoir's relation (a third structure and two
equivalences) is the book's (a generalized isomorphism `f` with `β' ∘ |f| = β`, Definition
16.1.2 and Remark 10.3.18).  A generalized isomorphism is the class of a diagram
`X ← X'' → X'` of equivalences (Theorem 10.3.10), and `|[d]| = |F'| ∘ |F|⁻¹`. -/
theorem memoirEquiv_iff {p q : MemoirPolyfoldStructure Z} :
    MemoirEquiv p q ↔ OrbitChart.Rel p.toOrbitChart q.toOrbitChart := by
  constructor
  · rintro ⟨r, F, F', hF, hF', h1, h2⟩
    have hFe := (isMemoirEquivalence_iff F).1 hF
    let d : Diagram p.X q.X := ⟨r.X, F, hFe, F'⟩
    refine ⟨EPLoc.homMk d, (EPLoc.theorem_10_3_10 d).1.2 ((isMemoirEquivalence_iff F').1 hF'), ?_⟩
    funext z
    obtain ⟨w, rfl⟩ := hFe.isHomeomorph_orbitMap.surjective z
    change q.β (d.orbitMap (d.F.orbitMap w)) = p.β (F.orbitMap w)
    rw [Diagram.orbitMap_orbitMap_F]
    exact (congrFun h2 w).symm.trans (congrFun h1 w)
  · rintro ⟨f, hf, hβ⟩
    obtain ⟨d, rfl⟩ := EPLoc.homMk_surjective f
    have hΦ := (EPLoc.theorem_10_3_10 d).1.1 hf
    let r : MemoirPolyfoldStructure Z :=
      ⟨d.A, (IsHomeomorph.homeomorph _ d.isEquivalence_F.isHomeomorph_orbitMap).trans p.β⟩
    refine ⟨r, d.F, d.Φ, (isMemoirEquivalence_iff _).2 d.isEquivalence_F,
      (isMemoirEquivalence_iff _).2 hΦ, rfl, ?_⟩
    funext w
    change p.β (d.F.orbitMap w) = q.β (d.Φ.orbitMap w)
    rw [← Diagram.orbitMap_orbitMap_F]
    exact (congrFun hβ (d.F.orbitMap w)).symm

theorem MemoirEquiv.refl (p : MemoirPolyfoldStructure Z) : MemoirEquiv p p :=
  memoirEquiv_iff.2 (OrbitChart.Rel.refl _)

theorem MemoirEquiv.symm {p q : MemoirPolyfoldStructure Z} (h : MemoirEquiv p q) :
    MemoirEquiv q p :=
  memoirEquiv_iff.2 (memoirEquiv_iff.1 h).symm

theorem MemoirEquiv.trans {p q r : MemoirPolyfoldStructure Z} (h : MemoirEquiv p q)
    (h' : MemoirEquiv q r) : MemoirEquiv p r :=
  memoirEquiv_iff.2 ((memoirEquiv_iff.1 h).trans (memoirEquiv_iff.1 h'))

instance setoid (Z : Type u) [TopologicalSpace Z] [ParacompactSpace Z] [T2Space Z] :
    Setoid (MemoirPolyfoldStructure Z) where
  r := MemoirEquiv
  iseqv := ⟨MemoirEquiv.refl, MemoirEquiv.symm, MemoirEquiv.trans⟩

/-- A memoir polyfold structure with (ZHOU) is a polyfold structure of the book
(Definition 16.1.1): the paracompactness of `|X|` follows. -/
def toPolyfoldStructure (p : MemoirPolyfoldStructure Z) (hZ : p.X.X.IsZhou) :
    PolyfoldStructure Z :=
  ⟨p.X, p.hasParacompactOrbitSpace, hZ, p.β⟩

/-- The memoir polyfold structure underlying a book polyfold structure. -/
def ofPolyfoldStructure (q : PolyfoldStructure Z) : MemoirPolyfoldStructure Z := ⟨q.X, q.β⟩

/-- **On book polyfold structures the two equivalences agree** (Definition 16.1.2). -/
theorem ofPolyfoldStructure_equiv_iff {q q' : PolyfoldStructure Z} :
    MemoirEquiv (ofPolyfoldStructure q) (ofPolyfoldStructure q') ↔ q.Equiv q' :=
  memoirEquiv_iff.trans PolyfoldStructure.equiv_iff_rel.symm

end MemoirPolyfoldStructure

/-- **Memoir Definition 2.29, p. 34**: a polyfold is a paracompact Hausdorff space `Z` with an
equivalence class of (memoir) polyfold structures. -/
abbrev MemoirPolyfoldClass (Z : Type u) [TopologicalSpace Z] [ParacompactSpace Z] [T2Space Z] :
    Type (u + 1) :=
  Quotient (MemoirPolyfoldStructure.setoid Z)

/-- **A book polyfold structure makes `Z` paracompact and Hausdorff** (Theorem 7.3.1: `|X|` is
metrizable), so the memoir's standing assumption on `Z` holds for the book's polyfolds. -/
theorem PolyfoldStructure.paracompact_t2 {Z : Type u} [TopologicalSpace Z]
    (q : PolyfoldStructure Z) : ParacompactSpace Z ∧ T2Space Z := by
  have : ParacompactSpace q.X.X.OrbitSpace := q.paracompact
  have := q.X.X.theorem_7_3_1_metrizable q.paracompact
  exact ⟨q.β.symm.paracompactSpace_iff.2 inferInstance, q.β.symm.isEmbedding.t2Space⟩

/-- The book's polyfolds embed into the memoir's: `[q] ↦ [q]` (well defined and injective by
`ofPolyfoldStructure_equiv_iff`). -/
def PolyfoldClass.toMemoir {Z : Type u} [TopologicalSpace Z] [ParacompactSpace Z] [T2Space Z] :
    PolyfoldClass Z → MemoirPolyfoldClass Z :=
  Quotient.map MemoirPolyfoldStructure.ofPolyfoldStructure fun _ _ h =>
    MemoirPolyfoldStructure.ofPolyfoldStructure_equiv_iff.2 h

theorem PolyfoldClass.toMemoir_injective {Z : Type u} [TopologicalSpace Z] [ParacompactSpace Z]
    [T2Space Z] : Injective (PolyfoldClass.toMemoir (Z := Z)) := by
  intro c c' h
  induction c using Quotient.inductionOn
  induction c' using Quotient.inductionOn
  exact Quotient.sound (MemoirPolyfoldStructure.ofPolyfoldStructure_equiv_iff.1 (Quotient.exact h))

/-! ### (ZHOU) does not follow: Appendix 7.6.3's groupoid -/

namespace ZhouExample

open EpGroupoid.Examples.ZhouRetract MeasureTheory

instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

/-- The data `δ_m = m` and a normalized bump for Appendix 7.6.3. -/
abbrev D : Data := Data.std

/-- The object space `Y ⊆ ℝ ⊕ L²(ℝ)` is second countable (`L²(ℝ)` is separable). -/
instance : SecondCountableTopology (O D) := by
  have : SecondCountableTopology (Lp ℝ 2 (volume : Measure ℝ)) := Lp.SecondCountableTopology
  have hz : SecondCountableTopology (Z D 0) := by
    have h := (ZhouLine.level0_line (CylinderSobolev.nonneg_of_strictMono D.h0 D.hmono 0) D.h0).1
    exact h.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (E D 0) := by
    change SecondCountableTopology (ℝ × Z D 0)
    infer_instance
  infer_instance

/-- `ℤ/2 ⋉ Y` (Appendix 7.6.3) as an object of `EP`. -/
abbrev zhouEP : EP.{0} := ⟨O D, ℤˣ × O D, X D⟩

theorem hasParacompactOrbitSpace : zhouEP.X.HasParacompactOrbitSpace :=
  EpGroupoid.Examples.hasParacompactOrbitSpace_action (isScSmoothMap_smul D)

instance : ParacompactSpace zhouEP.X.OrbitSpace := hasParacompactOrbitSpace

instance : T2Space zhouEP.X.OrbitSpace :=
  have := zhouEP.X.theorem_7_3_1_metrizable hasParacompactOrbitSpace
  inferInstance

/-- `(ℤ/2 ⋉ Y, 1)`, a memoir polyfold structure on `|ℤ/2 ⋉ Y|`. -/
def memoirStructure : MemoirPolyfoldStructure zhouEP.X.OrbitSpace := ⟨zhouEP, Homeomorph.refl _⟩

end ZhouExample

/-- **(ZHOU) does not follow from the memoir's definition** (Definition 2.29 versus the book's
Definition 16.1.1): the ep-groupoid `ℤ/2 ⋉ Y` of the book's Appendix 7.6.3 gives a memoir
polyfold structure on the paracompact Hausdorff space `|ℤ/2 ⋉ Y|`, and it does not satisfy
(ZHOU) (`ZhouRetract.not_isZhou`). -/
theorem memoir_definition_2_29_not_isZhou :
    ∃ (Z : Type) (_ : TopologicalSpace Z) (_ : ParacompactSpace Z) (_ : T2Space Z)
      (p : MemoirPolyfoldStructure Z), ¬ p.X.X.IsZhou :=
  ⟨_, _, inferInstance, inferInstance, ZhouExample.memoirStructure,
    EpGroupoid.Examples.ZhouRetract.not_isZhou _⟩

/-! ### Definition 2.37: the strong bundle `(E, μ)` over an ep-groupoid -/

section Def237

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

/-- **The reading of Memoir Definition 2.37 (3), p. 37**: the printed side condition is
`s(t) = p(e)`; read as `s(g) = p(e)`, it says `(g, e) ∈ X ₛ×_p E`, and then, with `s(h) = t(g)`,
both sides of `μ(h ∘ g, e) = μ(h, μ(g, e))` are defined: `s(h ∘ g) = s(g) = p(e)` and
`p(μ(g, e)) = t(g) = s(h)`. -/
theorem memoir_definition_2_37_three_mem (E : EpStrongBundle X B) {g h : Mor} {e : W}
    (hge : P e = X.src g) (hhg : X.src h = X.tgt g) :
    P e = X.src (X.comp h g) ∧ P (E.μ ⟨(g, e), hge⟩) = X.src h :=
  ⟨hge.trans (X.src_comp h g hhg).symm, (E.P_μ _).trans hhg.symm⟩

/-- **Memoir Definition 2.37, p. 38, with (3) read as `s(g) = p(e)` and the level-`0` part of
(1)**: an sc-smooth strong bundle map `μ : X ₛ×_p E → E` covering `t`, a local
sc-diffeomorphism of `E(0)`, with (2) and (3), is a strong bundle over the ep-groupoid in the
sense of the book's Definition 8.3.1.  The surjectivity of `μ`, which the book lists in (1),
follows from (2): `μ(1_{p(e)}, e) = e`. -/
def epStrongBundleOfMemoir (μ : pullbackSpace P X.src → W)
    (hmap : haveI := B.paracompactSpace_pullback X.PMor X.src
      (B.pullback X.isScSmoothMap_src).IsStrongBundleMap B X.tgt μ)
    (hloc : haveI := B.paracompactSpace_pullback X.PMor X.src
      (B.pullback X.isScSmoothMap_src).toMPolyfold0.IsLocalScDiffeo B.toMPolyfold0 μ)
    (h2 : ∀ e, μ (X.unitPair e) = e)
    (h3 : ∀ (h g : Mor) (e : W) (hge : P e = X.src g) (hhg : X.src h = X.tgt g)
      (hμ : P (μ ⟨(g, e), hge⟩) = X.src h),
      μ ⟨(X.comp h g, e), hge.trans (X.src_comp h g hhg).symm⟩ = μ ⟨(h, μ ⟨(g, e), hge⟩), hμ⟩) :
    EpStrongBundle X B where
  μ := μ
  isStrongBundleMap := hmap
  surjective e := ⟨X.unitPair e, h2 e⟩
  isLocalScDiffeo := hloc
  μ_unit := h2
  μ_comp ψ γ w h₁ h₂ := h3 ψ γ w h₁ h₂ _

end Def237

/-! ### Definition 2.38: strong polyfold bundle structures -/

/-- **Memoir Definition 2.38, p. 38**: for `p : Y → Z` between paracompact Hausdorff spaces, a
strong polyfold bundle structure `(P : E → X, Γ, γ)`: a strong bundle over an ep-groupoid
(Definition 2.37) and homeomorphisms `Γ : |E| → Y`, `γ : |X| → Z` with `p ∘ Γ = γ ∘ |P|`.
Unlike the book's Definition 16.3.1 (`StrongPolyfoldBundleStructure`) it asks neither (ZHOU), a
paracompact `|X|`, nor the local regularity property (Definition 8.4.2). -/
structure MemoirStrongPolyfoldBundleStructure {Y Z : Type u} [TopologicalSpace Y]
    [ParacompactSpace Y] [T2Space Y] [TopologicalSpace Z] [ParacompactSpace Z] [T2Space Z]
    (p : Y → Z) : Type (u + 1) where
  /-- The strong bundle `P : E → X` over the ep-groupoid `X`. -/
  A : SEP.{u}
  /-- `Γ : |E| → Y`. -/
  Γ : A.E.toEpGroupoid.OrbitSpace ≃ₜ Y
  /-- `γ : |X| → Z`. -/
  γ : A.X.OrbitSpace ≃ₜ Z
  /-- `p ∘ Γ = γ ∘ |P|`. -/
  comm : p ∘ Γ = γ ∘ A.E.projFunctor.orbitMap

namespace MemoirStrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [ParacompactSpace Y] [T2Space Y]
  [TopologicalSpace Z] [ParacompactSpace Z] [T2Space Z] {p : Y → Z}

/-- **The paracompactness of `|X|` follows** (from `γ` and the paracompact `Z`). -/
theorem hasParacompactOrbitSpace (S : MemoirStrongPolyfoldBundleStructure p) :
    S.A.X.HasParacompactOrbitSpace :=
  S.γ.paracompactSpace_iff.2 inferInstance

/-- The underlying memoir polyfold structure `(X, γ)` on `Z`. -/
def toMemoirPolyfoldStructure (S : MemoirStrongPolyfoldBundleStructure p) :
    MemoirPolyfoldStructure Z :=
  ⟨S.A.baseEP, S.γ⟩

/-- With (ZHOU) and the local regularity property of Definition 8.4.2, a memoir structure is a
strong polyfold bundle structure of the book (Definition 16.3.1). -/
def toStrongPolyfoldBundleStructure (S : MemoirStrongPolyfoldBundleStructure p)
    (hZ : S.A.X.IsZhou) (hLR : S.A.E.IsLRLocal) : StrongPolyfoldBundleStructure p :=
  ⟨S.A, hZ, S.hasParacompactOrbitSpace, hLR, S.Γ, S.γ, S.comm⟩

/-- The memoir structure underlying a book structure. -/
def ofStrongPolyfoldBundleStructure (S : StrongPolyfoldBundleStructure p) :
    MemoirStrongPolyfoldBundleStructure p :=
  ⟨S.A, S.Γ, S.γ, S.comm⟩

theorem toStrongPolyfoldBundleStructure_of (S : StrongPolyfoldBundleStructure p) :
    (ofStrongPolyfoldBundleStructure S).toStrongPolyfoldBundleStructure S.isZhou S.isLRLocal = S :=
  rfl

end MemoirStrongPolyfoldBundleStructure

namespace ZhouExample

/-- The constant functor from `ℤ/2 ⋉ Y` to the point `ℝ⁰`. -/
def toPoint : EpFunctor zhouEP.X (EpGroupoid.trivial (rnPolyfold 0)) where
  obj _ := 0
  mor _ := 0
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := Subsingleton.elim _ _
  mor_unit _ := Subsingleton.elim _ _
  isScSmoothMap_obj :=
    MPolyfold.isScSmoothMap_const (mem_smoothSet_of_isScSmoothMap MPolyfold.isScSmoothMap_id 0)
  isScSmoothMap_mor :=
    MPolyfold.isScSmoothMap_const (mem_smoothSet_of_isScSmoothMap MPolyfold.isScSmoothMap_id 0)

/-- The strong bundle `Y × ℝ → Y` over `ℤ/2 ⋉ Y`: the pull-back of `ℝ⁰ × ℝ → ℝ⁰` along the
constant functor (`SEP.pullbackAlong`). -/
abbrev zhouSEP : SEP.{0} :=
  (StrongBundleEquivalenceExamples.epSEP 0 1).pullbackAlong zhouEP toPoint

instance : ParacompactSpace zhouSEP.X.OrbitSpace := hasParacompactOrbitSpace

instance : T2Space zhouSEP.X.OrbitSpace := inferInstanceAs (T2Space zhouEP.X.OrbitSpace)

instance : MetrizableSpace zhouSEP.E.toEpGroupoid.OrbitSpace :=
  zhouSEP.E.metrizableSpace_orbitSpace hasParacompactOrbitSpace

instance : ParacompactSpace zhouSEP.E.toEpGroupoid.OrbitSpace :=
  paracompactSpace_of_metrizableSpace _

/-- `|E|`. -/
abbrev zhouSEP_W : Type := zhouSEP.E.toEpGroupoid.OrbitSpace

/-- `|X|`. -/
abbrev zhouSEP_X : Type := zhouSEP.X.OrbitSpace

/-- `(Y × ℝ → Y, 1, 1)`, a memoir strong polyfold bundle structure for `|P| : |E| → |X|`. -/
def memoirBundleStructure :
    MemoirStrongPolyfoldBundleStructure zhouSEP.E.projFunctor.orbitMap :=
  ⟨zhouSEP, Homeomorph.refl _, Homeomorph.refl _, rfl⟩

end ZhouExample

/-- **(ZHOU) does not follow from the memoir's Definition 2.38** (versus the book's Definition
16.3.1): the pull-back of `ℝ⁰ × ℝ → ℝ⁰` to the ep-groupoid `ℤ/2 ⋉ Y` of Appendix 7.6.3 is a
memoir strong polyfold bundle structure for `|P| : |E| → |X|` (paracompact Hausdorff spaces), and
its base does not satisfy (ZHOU). -/
theorem memoir_definition_2_38_not_isZhou :
    ∃ (Y Z : Type) (_ : TopologicalSpace Y) (_ : ParacompactSpace Y) (_ : T2Space Y)
      (_ : TopologicalSpace Z) (_ : ParacompactSpace Z) (_ : T2Space Z) (p : Y → Z)
      (S : MemoirStrongPolyfoldBundleStructure p), ¬ S.A.X.IsZhou :=
  ⟨ZhouExample.zhouSEP_W, ZhouExample.zhouSEP_X, _, inferInstance, inferInstance, _, inferInstance,
    inferInstance, _,
    ZhouExample.memoirBundleStructure, EpGroupoid.Examples.ZhouRetract.not_isZhou _⟩

end GWMemoir
