import Polyfold.Chapter9.SupportManifold
import Polyfold.Chapter10.EquivalenceRefinement
import Polyfold.Chapter10.LocalizationCategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9,
§9.1, **Proposition 9.1.9** (p. 405; 2017: Proposition 9.1, p. 294), the text's construction in
the proof (pp. 406–407) and the independence of the choices.

# The text's groupoid `M` on `⊔ M_x`, and the naturality of the structures of Proposition 9.1.9

## The text, paraphrased

(Proof of Proposition 9.1.9 (2)) For `x ∈ supp(Θ)` choose `U(x)` with a local branching
structure; for `Θ` of orbifold-type its sheets coincide, `M_x`.  The disjoint union `M = ⊔ M_x`
is the object space of a category whose morphisms are the disjoint union of the sets
`M(x, x') = {φ | s(φ) ∈ M_x, t(φ) ∈ M_{x'}}`; it is an étale proper groupoid, the functor
`β : M → Z`, `y ↦ |y|` (`Z = |supp(Θ)|` with only identities), induces a homeomorphism
`|β| : |M| → Z`, and other choices give a groupoid `M'` defining an *equivalent* orbifold
structure (the text leaves the equivalence to the reader, pointing to Morita equivalence and to
Chapter 10).  (Proof of (1)) The manifold structure on `Z` "does not depend on the choices of the
specific `U(x)`" (left to the reader).

## What is formalized

* `EpGroupoid.SheetIndex Θ` (the points of `supp(Θ)`, discrete) and `EpGroupoid.SheetChoice X Θ`
  (a choice of a local branching structure at every `x ∈ supp(Θ)`, the text's choices), with
  `nonempty_sheetChoice`.
* `EpGroupoid.sheetCover hA c`: the open covering `(M_x)_{x ∈ supp(Θ)}` of `supp(Θ)`,
  `M_x = supp(Θ) ∩ U(x)`; `image_sheetCover_set`: `M_x` is a sheet of the chosen local branching
  structure (for `Θ` of orbifold-type every sheet is `M_x`).
* `EpGroupoid.textGroupoid hA c`: the text's groupoid `M`, the refinement of Proposition 10.1.3
  of the full ep-subgroupoid on `supp(Θ)` along `(M_x)`: objects `(x, y)` with `y ∈ M_x` (the
  disjoint union `⊔ M_x`), morphisms `((x, x'), φ)` with `s(φ) ∈ M_x`, `t(φ) ∈ M_{x'}` (the
  disjoint union of the `M(x, x')`); an ep-groupoid (étale, proper).
* `EpGroupoid.textOrbitHomeomorph`: `|β| : |M| ≃ₜ Z`, `|(x, y)| ↦ |y|`.
* **`EpGroupoid.proposition_9_1_9_two_text`** (Proposition 9.1.9 (2) as printed, with the text's
  groupoid): for every choice, `M` is an ep-groupoid whose objects are the disjoint union of the
  sheets `M_x`, `supp(Θ)` is a smooth finite-dimensional submanifold of `X`, `|β|` is a
  homeomorphism, and the functor `M → supp(Θ)` (to the full ep-subgroupoid of
  `proposition_9_1_9_two`) is an equivalence (Definition 10.1.1) over `Z`.
* The independence of the choices: `OpenCover.refineFunctor` (a refinement of coverings gives a
  functor of the refinements), `OpenCover.isEquivalence_refineFunctor` (it is an equivalence);
  **`EpGroupoid.proposition_9_1_9_two_independent`**: for two choices `c`, `c'` the diagram
  `M_c ← M_{c,c'} → M_{c'}` (the common refinement by the `M_x ∩ M'_{x'}`) consists of
  equivalences over `Z`, so `[M_c ← M_{c,c'} → M_{c'}]` is a generalized isomorphism in
  `EP(E⁻¹)` (Definition 10.3.9, Theorem 10.3.10) whose map of orbit spaces commutes with the
  homeomorphisms `|β|`, `|β'|` to `Z`: the orbifold structures are equivalent.
* **`EpGroupoid.proposition_9_1_9_one_unique`** (the manifold structure does not depend on the
  choices): any two M-polyfold structures on `Z` for which `p : supp(Θ) → Z`, `a ↦ |a|`, is a
  local sc-diffeomorphism are the same (the identity of `Z` is a local sc-diffeomorphism both
  ways); `proposition_9_1_9_one` constructs one of them from the charts `Ψ_x`.

## How it relates to the text

The text's `M` is built with a choice of `U(x)` for every `x ∈ supp(Θ)`; we take the choice of a
local branching structure (the data of Lemma 9.1.7's `U(x)` that the construction uses is its
open set).  "Equivalent orbifold structure" is read as a generalized isomorphism of Chapter 10
compatible with the maps to `Z` (the Morita equivalence of the text, through the common
refinement).  `M` needs `supp(Θ) ≠ ∅` (for `Θ = 0`, `Z = ∅` and there is nothing to construct;
the open-subset M-polyfold structure of the project is defined for nonempty subsets).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace CategoryTheory

noncomputable section

namespace Polyfold

universe u

attribute [local instance] paracompactSpace_discrete_prod

/-! ### Refinements of coverings give equivalences -/

namespace EpGroupoid

namespace OpenCover

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {ι κ : Type u} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace κ]
  [DiscreteTopology κ] [Nonempty Obj]
  (𝒰 : X.OpenCover ι) (𝒱 : X.OpenCover κ) (r : κ → ι) (hr : ∀ k, 𝒱.set k ⊆ 𝒰.set (r k))

/-- `(k, x) ↦ (r(k), x)` on objects, for a refinement `V_k ⊆ U_{r(k)}`. -/
def refineObj (p : 𝒱.objSet) : 𝒰.objSet := ⟨(r p.1.1, p.1.2), hr p.1.1 p.2⟩

/-- `((k, k'), φ) ↦ ((r(k), r(k')), φ)` on morphisms. -/
def refineMor (q : 𝒱.morSet) : 𝒰.morSet :=
  ⟨((r q.1.1.1, r q.1.1.2), q.1.2), hr _ q.2.1, hr _ q.2.2⟩

/-- **The functor `X_𝒱 → X_𝒰` of a refinement** `V_k ⊆ U_{r(k)}`. -/
def refineFunctor : EpFunctor 𝒱.epGroupoid 𝒰.epGroupoid where
  obj := refineObj 𝒰 𝒱 r hr
  mor := refineMor 𝒰 𝒱 r hr
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp q q' h := by
    have h' := (src_eq_tgt h).2
    have h'' : X.src (refineMor 𝒰 𝒱 r hr q).1.2 = X.tgt (refineMor 𝒰 𝒱 r hr q').1.2 := h'
    refine morSet_ext ?_ ?_ ?_
    · change r (𝒱.comp q q').1.1.1 = (𝒰.comp _ _).1.1.1
      rw [comp_val h', comp_val h'']; rfl
    · change r (𝒱.comp q q').1.1.2 = (𝒰.comp _ _).1.1.2
      rw [comp_val h', comp_val h'']; rfl
    · change (𝒱.comp q q').1.2 = (𝒰.comp _ _).1.2
      rw [comp_val h', comp_val h'']; rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := by
    have hamb : ((discretePolyfold κ).prod X.PObj).IsScSmoothMap ((discretePolyfold ι).prod X.PObj)
        (fun p : κ × Obj => (r p.1, p.2)) :=
      MPolyfold.IsScSmoothOn.prodMk
        (isScSmoothMap_discrete_of_continuous ((continuous_of_discreteTopology (f := r)).comp
          continuous_fst))
        (MPolyfold.isScSmoothMap_snd _ _)
    exact MPolyfold.isScSmoothMap_restrict 𝒱.isOpen_objSet 𝒰.isOpen_objSet hamb _
  isScSmoothMap_mor := by
    have hamb : ((discretePolyfold (κ × κ)).prod X.PMor).IsScSmoothMap
        ((discretePolyfold (ι × ι)).prod X.PMor)
        (fun q : (κ × κ) × Mor => ((r q.1.1, r q.1.2), q.2)) :=
      MPolyfold.IsScSmoothOn.prodMk
        (isScSmoothMap_discrete_of_continuous ((continuous_of_discreteTopology
          (f := fun kk : κ × κ => (r kk.1, r kk.2))).comp continuous_fst))
        (MPolyfold.isScSmoothMap_snd _ _)
    exact MPolyfold.isScSmoothMap_restrict 𝒱.isOpen_morSet 𝒰.isOpen_morSet hamb _

theorem functor_comp_refineFunctor :
    𝒰.functor.comp (refineFunctor 𝒰 𝒱 r hr) = 𝒱.functor :=
  EpFunctor.ext rfl rfl

/-- **A refinement of coverings gives an equivalence** `X_𝒱 → X_𝒰` (two out of three:
`F_𝒰 ∘ G = F_𝒱`, both equivalences by Proposition 10.1.3). -/
theorem isEquivalence_refineFunctor : (refineFunctor 𝒰 𝒱 r hr).IsEquivalence :=
  EpFunctor.IsEquivalence.of_comp_left 𝒰.proposition_10_1_3
    ((functor_comp_refineFunctor 𝒰 𝒱 r hr).symm ▸ 𝒱.proposition_10_1_3)

/-- The common refinement `(U_i ∩ U'_j)_{(i, j)}` of two coverings. -/
def inf (𝒰 : X.OpenCover ι) (𝒰' : X.OpenCover κ) : X.OpenCover (ι × κ) where
  set ij := 𝒰.set ij.1 ∩ 𝒰'.set ij.2
  isOpen ij := (𝒰.isOpen ij.1).inter (𝒰'.isOpen ij.2)
  exists_mem x := by
    obtain ⟨i, hi⟩ := 𝒰.exists_mem x
    obtain ⟨j, hj⟩ := 𝒰'.exists_mem x
    exact ⟨(i, j), hi, hj⟩

end OpenCover

/-! ### The text's choices and the covering `(M_x)` -/

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

variable (Θ) in
/-- The index set of the text's groupoid: the points `x ∈ supp(Θ)`, with the discrete topology
(a type synonym of `supp Θ`, which carries the subspace topology). -/
def SheetIndex : Type u := supp Θ

instance : TopologicalSpace (SheetIndex Θ) := ⊥

instance : DiscreteTopology (SheetIndex Θ) := ⟨rfl⟩

/-- The point `x ∈ supp(Θ)` of an index. -/
def SheetIndex.pt (x : SheetIndex Θ) : supp Θ := x

/-- The index of a point `x ∈ supp(Θ)`. -/
def SheetIndex.mk (x : supp Θ) : SheetIndex Θ := x

variable (X Θ) in
/-- **The text's choices**: a local branching structure (with its `U(x)`) at every
`x ∈ supp(Θ)`. -/
def SheetChoice : Type (u + 1) := ∀ x : SheetIndex Θ, X.LocalBranchingStructure Θ x.pt.1

/-- The text's choices exist (Definition 9.1.2 (2)–(4)). -/
theorem nonempty_sheetChoice (hΘ : X.IsBranchedEpSubgroupoid Θ) : Nonempty (X.SheetChoice Θ) :=
  ⟨fun x => (hΘ.localBranching x.pt.1 x.pt.2).some⟩

section Cover

variable (hA : X.IsEpSubgroupoid (supp Θ)) [ParacompactSpace (supp Θ)] (c : X.SheetChoice Θ)

/-- **The covering `(M_x)_{x ∈ supp(Θ)}`** of the object space `supp(Θ)` of the full
ep-subgroupoid, `M_x = supp(Θ) ∩ U(x)`. -/
def sheetCover : (subEpGroupoid hA).OpenCover (SheetIndex Θ) where
  set x := Subtype.val ⁻¹' (c x).U
  isOpen x := (c x).isOpen_U.preimage continuous_subtype_val
  exists_mem a := ⟨SheetIndex.mk a, (c (SheetIndex.mk a)).mem_U⟩

/-- **`M_x` is a sheet** of the chosen local branching structure at `x` (for `Θ` of
orbifold-type every sheet `M_i` is `supp(Θ) ∩ U(x)`, `supp_inter_eq_of_isOrbifoldType`). -/
theorem image_sheetCover_set (ho : IsOrbifoldType Θ) (x : SheetIndex Θ) (i : (c x).ι) :
    Subtype.val '' (sheetCover hA c).set x = (c x).M i := by
  rw [← supp_inter_eq_of_isOrbifoldType ho x.pt.2 (c x) i]
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨hy, hyU⟩
    exact ⟨⟨y, hy⟩, hyU, rfl⟩

variable [Nonempty (supp Θ)]

/-- **The text's groupoid `M`** (proof of Proposition 9.1.9 (2)): objects `(x, y)`, `y ∈ M_x`,
morphisms `((x, x'), φ)` with `s(φ) ∈ M_x`, `t(φ) ∈ M_{x'}`; an ep-groupoid (the refinement of
Proposition 10.1.3). -/
abbrev textGroupoid : EpGroupoid (sheetCover hA c).objSet (sheetCover hA c).morSet :=
  (sheetCover hA c).epGroupoid

/-- **`|β| : |M| ≃ₜ Z`**, `|(x, y)| ↦ |y|`: the homeomorphism `|F|` of Proposition 10.1.3 followed
by `|supp(Θ)|_{subEpGroupoid} ≃ₜ Z` (`orbitSuppHomeomorph`). -/
def textOrbitHomeomorph : (textGroupoid hA c).OrbitSpace ≃ₜ X.orbitSupp Θ :=
  (IsHomeomorph.homeomorph _ (sheetCover hA c).proposition_10_1_3.isHomeomorph_orbitMap).trans
    (orbitSuppHomeomorph hA)

theorem textOrbitHomeomorph_π (p : (sheetCover hA c).objSet) :
    (textOrbitHomeomorph hA c ((textGroupoid hA c).π p) : X.OrbitSpace) = X.π p.1.2.1 := rfl

theorem textOrbitHomeomorph_eq :
    ⇑(textOrbitHomeomorph hA c) = orbitSuppHomeomorph hA ∘ (sheetCover hA c).functor.orbitMap :=
  rfl

end Cover

/-! ### Proposition 9.1.9 (2) with the text's groupoid -/

/-- **2021 Proposition 9.1.9 (2)**, p. 405, with the text's construction (proof, pp. 406–407;
2017: Proposition 9.1 (2), p. 295): for `Θ` of orbifold-type and every choice of local branching
structures `c`, the text's groupoid `M = textGroupoid hA c` is an ep-groupoid (étale and proper)
whose object space is the disjoint union of the sheets `M_x` (each a sheet of `c x`), `supp(Θ)` is
a smooth finite-dimensional submanifold of `X` (the `M_x` are open in it), the functor `β` induces
a homeomorphism `|M| ≃ₜ Z = |supp(Θ)|`, `|(x, y)| ↦ |y|`, and the functor `M → supp(Θ)`,
`(x, y) ↦ y`, to the full ep-subgroupoid is an equivalence (Definition 10.1.1). -/
theorem proposition_9_1_9_two_text (hΘ : X.IsBranchedEpSubgroupoid Θ) (ho : IsOrbifoldType Θ)
    [Nonempty (supp Θ)] (c : X.SheetChoice Θ) :
    haveI := X.PObj.paracompactSpace_subtype (supp Θ)
    let hA := isEpSubgroupoid_supp_of_isOrbifoldType hΘ ho
    X.PObj.IsSmoothSubmanifold (supp Θ) ∧
      (∀ x i, Subtype.val '' (sheetCover hA c).set x = (c x).M i) ∧
      (sheetCover hA c).functor.IsEquivalence ∧
      ∃ e : (textGroupoid hA c).OrbitSpace ≃ₜ X.orbitSupp Θ,
        ∀ p, (e ((textGroupoid hA c).π p) : X.OrbitSpace) = X.π p.1.2.1 :=
  haveI := X.PObj.paracompactSpace_subtype (supp Θ)
  ⟨isSmoothSubmanifold_supp_of_isOrbifoldType hΘ ho, image_sheetCover_set _ c ho,
    (sheetCover _ c).proposition_10_1_3, textOrbitHomeomorph _ c, textOrbitHomeomorph_π _ c⟩

/-! ### Independence of the choices -/

section Independence

open EPLocalization

variable (hA : X.IsEpSubgroupoid (supp Θ)) [ParacompactSpace (supp Θ)] [Nonempty (supp Θ)]
  (c c' : X.SheetChoice Θ)

/-- The bundled text's groupoid, an object of `EP`. -/
abbrev textEP : EP.{u} := EP.mk _ _ (textGroupoid hA c)

/-- The common refinement of the coverings of two choices (pieces `M_x ∩ M'_{x'}`). -/
abbrev commonCover : (subEpGroupoid hA).OpenCover (SheetIndex Θ × SheetIndex Θ) :=
  (sheetCover hA c).inf (sheetCover hA c')

/-- The equivalence `M_{c,c'} → M_c`. -/
abbrev commonFst : EpFunctor (commonCover hA c c').epGroupoid (textGroupoid hA c) :=
  OpenCover.refineFunctor (sheetCover hA c) (commonCover hA c c') Prod.fst fun _ _ h => h.1

/-- The equivalence `M_{c,c'} → M_{c'}`. -/
abbrev commonSnd : EpFunctor (commonCover hA c c').epGroupoid (textGroupoid hA c') :=
  OpenCover.refineFunctor (sheetCover hA c') (commonCover hA c c') Prod.snd fun _ _ h => h.2

/-- The diagram `M_c ← M_{c,c'} → M_{c'}` (Chapter 10's generalized map). -/
def choiceDiagram : Diagram (textEP hA c) (textEP hA c') where
  A := EP.mk _ _ (commonCover hA c c').epGroupoid
  F := commonFst hA c c'
  isEquivalence_F := OpenCover.isEquivalence_refineFunctor _ _ _ _
  Φ := commonSnd hA c c'

theorem orbitMap_commonFst (q : (commonCover hA c c').epGroupoid.OrbitSpace) :
    textOrbitHomeomorph hA c ((commonFst hA c c').orbitMap q) =
      textOrbitHomeomorph hA c' ((commonSnd hA c c').orbitMap q) := by
  induction q using Quotient.inductionOn with | h p => rfl

/-- **The independence of the choices in Proposition 9.1.9 (2)** (the text: "different choices
… define an equivalent orbifold structure", left to the reader): for two choices `c`, `c'`, the
diagram `M_c ← M_{c,c'} → M_{c'}` consists of equivalences (Definition 10.1.1), so it is a
generalized isomorphism of `EP(E⁻¹)` (Theorem 10.3.10), and its map of orbit spaces
`|M_c| → |M_{c'}|` is a homeomorphism commuting with `|β|`, `|β'|` to `Z`. -/
theorem proposition_9_1_9_two_independent :
    (commonFst hA c c').IsEquivalence ∧ (commonSnd hA c c').IsEquivalence ∧
      EPLoc.IsGeneralizedIso (EPLoc.homMk (choiceDiagram hA c c')) ∧
      IsHomeomorph (choiceDiagram hA c c').orbitMap ∧
      ∀ z, textOrbitHomeomorph hA c' ((choiceDiagram hA c c').orbitMap z) =
        textOrbitHomeomorph hA c z := by
  have h₁ := OpenCover.isEquivalence_refineFunctor (sheetCover hA c) (commonCover hA c c')
    Prod.fst fun _ _ h => h.1
  have h₂ := OpenCover.isEquivalence_refineFunctor (sheetCover hA c') (commonCover hA c c')
    Prod.snd fun _ _ h => h.2
  set e₁ := IsHomeomorph.homeomorph _ h₁.isHomeomorph_orbitMap
  refine ⟨h₁, h₂, (EPLoc.theorem_10_3_10 _).1.2 h₂, ?_, fun z => ?_⟩
  · exact h₂.isHomeomorph_orbitMap.comp e₁.symm.isHomeomorph
  · change textOrbitHomeomorph hA c' ((commonSnd hA c c').orbitMap (e₁.symm z)) = _
    rw [← orbitMap_commonFst]
    exact congrArg _ (e₁.apply_symm_apply z)

end Independence

/-! ### Proposition 9.1.9 (1): the structure does not depend on the choices -/

/-- **The independence of the choices in Proposition 9.1.9 (1)** (the text: the smooth manifold
structure on `Z` "does not depend on the choices of the specific `U(x)`", left to the reader):
the M-polyfold structure on `Z = |supp(Θ)|` is determined by the requirement that
`p : supp(Θ) → Z`, `a ↦ |a|`, be a local sc-diffeomorphism, so whatever charts `Ψ_x` were used:
for two structures `PZ`, `PZ'` with this property, the identity of `Z` is a local
sc-diffeomorphism `PZ → PZ'` and `PZ' → PZ` (the two maximal atlases agree).  Near `|a|`,
`id = p ∘ (p|V)⁻¹`. -/
theorem proposition_9_1_9_one_unique (hA : X.IsEpSubgroupoid (supp Θ)) [ParacompactSpace (supp Θ)]
    [ParacompactSpace (X.orbitSupp Θ)] {PZ PZ' : MPolyfold (X.orbitSupp Θ)}
    (h : (subEpGroupoid hA).PObj.IsLocalScDiffeo PZ (X.orbitSuppProj Θ))
    (h' : (subEpGroupoid hA).PObj.IsLocalScDiffeo PZ' (X.orbitSuppProj Θ)) :
    PZ.IsLocalScDiffeo PZ' id ∧ PZ'.IsLocalScDiffeo PZ id := by
  have key : ∀ {Q Q' : MPolyfold (X.orbitSupp Θ)},
      (subEpGroupoid hA).PObj.IsLocalScDiffeo Q (X.orbitSuppProj Θ) →
      (subEpGroupoid hA).PObj.IsLocalScDiffeo Q' (X.orbitSuppProj Θ) → Q.IsLocalScDiffeo Q' id := by
    intro Q Q' hQ hQ' z
    obtain ⟨a, rfl⟩ : ∃ a, X.orbitSuppProj Θ a = z := by
      obtain ⟨_, a, ha, rfl⟩ := z
      exact ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨U, V, g, haU, hd⟩ := hQ a
    have hg : Q.IsLocalScDiffeoAt (subEpGroupoid hA).PObj g (X.orbitSuppProj Θ a) :=
      hd.symm.isLocalScDiffeoAt (hd.mapsTo haU)
    have hp : (subEpGroupoid hA).PObj.IsLocalScDiffeoAt Q' (X.orbitSuppProj Θ)
        (g (X.orbitSuppProj Θ a)) := hQ'.at _
    refine (hp.comp hg).congr ?_
    filter_upwards [hd.isOpen_target.mem_nhds (hd.mapsTo haU)] with w hw
    exact hd.right_inv w hw
  exact ⟨key h h', key h' h⟩

end EpGroupoid

end Polyfold
