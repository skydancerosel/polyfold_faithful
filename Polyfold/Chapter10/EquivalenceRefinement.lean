import Polyfold.Chapter10.Equivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.1 "Equivalences", pp. 462–463 (2017: p. 334): the refinement `X_𝒰`
and **Proposition 10.1.3** (2017: Proposition 10.1).  Numbers and pages are the 2021 text's, the
2017 ones in parentheses.

# The refinement of an ep-groupoid along an open covering

## The text, paraphrased

(p. 462) For an open covering `𝒰` of the object M-polyfold of `X`, the refinement `X_𝒰` has the
disjoint union `⊔_{U ∈ 𝒰} U` as objects, written `(x, U)` with `x ∈ U`, and as morphisms the
triples `(U, φ, V)` with `s(φ) ∈ U`, `t(φ) ∈ V`; the structure maps are the obvious ones and the
M-polyfold structures are induced from `X` and `𝐗`.  (Proposition 10.1.3, p. 462 (2017:
Proposition 10.1, p. 334)) `X_𝒰` is an ep-groupoid and `F : X_𝒰 → X`, `(x, U) ↦ x`,
`(U, φ, V) ↦ φ`, is an equivalence.  *Proof* (text, pp. 462–463): `s, t` are local
sc-diffeomorphisms; for properness at `(x, U)` take `V(x)` with `cl V(x) ⊆ U` and the properness
property of `X`, then a sequence argument; `F` is an equivalence of categories and a local
sc-diffeomorphism, so Lemma 10.1.2 applies.

## What is formalized

* `EpGroupoid.OpenCover X ι` (a covering `U_i`, `i ∈ ι`, by open sets), with the trivial
  covering `OpenCover.univ` as a witness.
* `OpenCover.objSet`, `morSet`, the structure maps `src`, `tgt`, `comp`, `unit`, `inv`,
  `groupoidStr`; the M-polyfolds `objPolyfold`, `morPolyfold`; `isLocalScDiffeo_src`,
  `isLocalScDiffeo_tgt`, `isScSmoothMap_unit`, `isScSmoothMap_inv`, `exists_isProperMap`,
  `isScSmoothCompSheet`; `OpenCover.epGroupoid` (**`X_𝒰` is an ep-groupoid**).
* `OpenCover.functor : X_𝒰 → X` and `OpenCover.proposition_10_1_3` (**Proposition 10.1.3**).
* Witness: `Examples.reflectionCover`, the covering `{x > -1}`, `{x < 1}` of `ℤ/2 ⋉ ℝ`, with
  `isEquivalence_reflectionCover` and `not_injective_reflectionCover_obj` (the equivalence
  `X_𝒰 → X` is not injective on objects, so not an isomorphism).
* Helpers: `paracompactSpace_discrete_prod`, `isOpen_of_discrete_left`,
  `MPolyfold.isScSmoothOn_restrictOpen_iff`, `isScSmoothMap_restrict`,
  `isLocalScDiffeoAt_restrict`, `isLocalScDiffeo_snd_discrete`, `isLocalScDiffeo_sheet`.

## What the text leaves implicit, and the choices made

* The covering is indexed by a type `ι` (the text's index set is `𝒰` itself) with the discrete
  topology; `X_𝒰` is the open subset `{(i, x) | x ∈ U_i}` of `ι × X`, an open subset of
  `discretePolyfold ι × X`, which is how "induced from `X`" is read.  A morphism is
  `((i, j), φ)`, the text's `(U_i, φ, U_j)` reordered.
* The open-subset M-polyfold structure (`restrictOpen`) needs a nonempty subset, so the
  M-polyfold structure, `epGroupoid` and Proposition 10.1.3 assume `[Nonempty Obj]` (for an empty
  `X` there is nothing to prove).
* The properness is proved with ultrafilters instead of sequences.  The text writes `(U, φ, v)`
  for `(U, φ, V)` in the formula for `F` (possible misprint).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v w

/-! ### Products with a discrete factor; open subsets -/

/-- `ι × Y` is paracompact for a discrete `ι` and a paracompact `Y` (it is `Σ (_ : ι), Y`). -/
theorem paracompactSpace_discrete_prod {ι Y : Type*} [TopologicalSpace ι] [DiscreteTopology ι]
    [TopologicalSpace Y] [ParacompactSpace Y] : ParacompactSpace (ι × Y) := by
  let e : (Σ _ : ι, Y) ≃ₜ ι × Y :=
    { Equiv.sigmaEquivProd ι Y with
      continuous_toFun := continuous_sigma fun _ => continuous_const.prodMk continuous_id
      continuous_invFun := continuous_prod_of_discrete_left.2 fun i =>
        show Continuous (Sigma.mk (β := fun _ : ι => Y) i) from continuous_sigmaMk }
  exact e.paracompactSpace_iff.1 inferInstance

attribute [local instance] paracompactSpace_discrete_prod

/-- A subset of `G × Y`, `G` discrete, is open if all its slices are. -/
theorem isOpen_of_discrete_left {G Y : Type*} [TopologicalSpace G] [DiscreteTopology G]
    [TopologicalSpace Y] {S : Set (G × Y)} (h : ∀ g, IsOpen {y | (g, y) ∈ S}) : IsOpen S := by
  have hS : S = ⋃ g, {g} ×ˢ {y | (g, y) ∈ S} := by
    ext ⟨g, y⟩
    simp only [mem_iUnion, mem_prod, mem_singleton_iff]
    exact ⟨fun h => ⟨g, rfl, h⟩, fun ⟨_, hg, h⟩ => hg ▸ h⟩
  rw [hS]
  exact isOpen_iUnion fun g => (isOpen_discrete _).prod (h g)

namespace MPolyfold

variable {A : Type u} [TopologicalSpace A] [T2Space A] [ParacompactSpace A] {P : MPolyfold A}
  {B : Type v} [TopologicalSpace B] [T2Space B] [ParacompactSpace B] {Q : MPolyfold B}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}
  {O : Set A} (hO : IsOpen O) [Nonempty O] [ParacompactSpace O]
  {O' : Set B} (hO' : IsOpen O') [Nonempty O'] [ParacompactSpace O']

include hO in
/-- **Sc-smoothness into an open subset** is sc-smoothness into the ambient M-polyfold. -/
theorem isScSmoothOn_restrictOpen_iff {g : Z → O} {W : Set Z} :
    S.IsScSmoothOn (P.restrictOpen hO) g W ↔ S.IsScSmoothOn P (Subtype.val ∘ g) W := by
  constructor
  · intro h
    exact IsScSmoothOn.comp (isScSmoothMap_subtypeVal hO) h (mapsTo_univ _ _)
  · intro h
    refine (IsScSmoothOn.comp (isScSmoothOn_openRetraction hO) h fun z _ => (g z).2).congr
      fun z _ => ?_
    simp only [Function.comp_apply, openRetraction_of_mem (g z).2]

include hO hO' in
/-- A map between open subsets induced by an sc-smooth map is sc-smooth. -/
theorem isScSmoothMap_restrict {F : A → B} (hF : P.IsScSmoothMap Q F)
    (hFO : ∀ p : O, F p.1 ∈ O') :
    (P.restrictOpen hO).IsScSmoothMap (Q.restrictOpen hO') fun p : O => (⟨F p.1, hFO p⟩ : O') :=
  IsScSmoothMap.codRestrict_restrictOpen hO' (hF.comp (isScSmoothMap_subtypeVal hO)) hFO

include hO hO' in
/-- A map between open subsets induced by a continuous map which is a local sc-diffeomorphism at
`p` is a local sc-diffeomorphism at `p`. -/
theorem isLocalScDiffeoAt_restrict {F : A → B} (hFc : Continuous F) (hFO : ∀ p : O, F p.1 ∈ O')
    {p : O} (hF : P.IsLocalScDiffeoAt Q F p.1) :
    (P.restrictOpen hO).IsLocalScDiffeoAt (Q.restrictOpen hO')
      (fun p : O => (⟨F p.1, hFO p⟩ : O')) p := by
  have h1 : (P.restrictOpen hO).IsLocalScDiffeoAt Q
      (Subtype.val ∘ fun p : O => (⟨F p.1, hFO p⟩ : O')) p :=
    hF.comp ((isLocalScDiffeo_subtypeVal hO).at p)
  exact IsLocalScDiffeoAt.of_comp_left ((isLocalScDiffeo_subtypeVal hO').at _)
    ((hFc.comp continuous_subtype_val).subtype_mk _) h1

end MPolyfold

/-- A map into a discrete M-polyfold, continuous on an open set, is sc-smooth there (a copy of a
private lemma of `Chapter7/NonVacuity.lean`). -/
theorem isScSmoothOn_discrete_of_continuousOn {G : Type*} [TopologicalSpace G]
    [DiscreteTopology G] {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {PY : MPolyfold Y} {f : Y → G} {W : Set Y} (hW : IsOpen W) (hf : ContinuousOn f W) :
    PY.IsScSmoothOn (discretePolyfold G) f W := by
  refine MPolyfold.IsScSmoothOn.of_locally hW fun y hy => ⟨W ∩ f ⁻¹' {f y},
    hf.isOpen_inter_preimage hW (isOpen_discrete _), ⟨hy, rfl⟩, inter_subset_left, ?_⟩
  exact ((isScSmoothMap_const_discrete (f y)).mono
    (hf.isOpen_inter_preimage hW (isOpen_discrete _)) (subset_univ _)).congr
    fun z hz => hz.2.symm

/-- `π₂ : G × Y → Y`, `G` discrete, is a local sc-diffeomorphism at every point. -/
theorem isLocalScDiffeo_snd_discrete {G : Type u} [TopologicalSpace G] [DiscreteTopology G]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {PY : MPolyfold Y}
    [ParacompactSpace (G × Y)] :
    ((discretePolyfold G).prod PY).IsLocalScDiffeo PY Prod.snd := fun p =>
  ⟨{p.1} ×ˢ univ, univ, fun y => (p.1, y), ⟨mem_singleton _, mem_univ _⟩,
    isScDiffeoOn_snd_sheet p.1⟩

/-- The sheet inclusion `y ↦ (g, y)` is a local sc-diffeomorphism at every point. -/
theorem isLocalScDiffeo_sheet {G : Type u} [TopologicalSpace G] [DiscreteTopology G]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {PY : MPolyfold Y}
    [ParacompactSpace (G × Y)] (g : G) :
    PY.IsLocalScDiffeo ((discretePolyfold G).prod PY) fun y => (g, y) := fun _ =>
  ⟨univ, {g} ×ˢ univ, Prod.snd, mem_univ _, (isScDiffeoOn_snd_sheet g).symm⟩

/-! ### The refinement `X_𝒰` -/

/-- **An open covering of the object M-polyfold** of `X`, indexed by `ι` (the text's `𝒰`, a set of
open sets, is the case `ι = 𝒰`). -/
structure EpGroupoid.OpenCover {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (ι : Type u) : Type u where
  /-- The open set `U_i`. -/
  set : ι → Set Obj
  isOpen : ∀ i, IsOpen (set i)
  exists_mem : ∀ x, ∃ i, x ∈ set i

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {ι : Type u}

/-- **The trivial covering** `{X}` (a witness for `OpenCover`). -/
def OpenCover.univ (X : EpGroupoid Obj Mor) : X.OpenCover PUnit where
  set _ := Set.univ
  isOpen _ := isOpen_univ
  exists_mem _ := ⟨PUnit.unit, mem_univ _⟩

namespace OpenCover

variable (𝒰 : X.OpenCover ι)

/-- The objects `(i, x)`, `x ∈ U_i`, of `X_𝒰`. -/
def objSet : Set (ι × Obj) := {p | p.2 ∈ 𝒰.set p.1}

/-- The morphisms `((i, j), φ)` with `s(φ) ∈ U_i`, `t(φ) ∈ U_j`, of `X_𝒰` (the text's triples
`(U_i, φ, U_j)`). -/
def morSet : Set ((ι × ι) × Mor) := {q | X.src q.2 ∈ 𝒰.set q.1.1 ∧ X.tgt q.2 ∈ 𝒰.set q.1.2}

section Topology

variable [TopologicalSpace ι] [DiscreteTopology ι]

theorem isOpen_objSet : IsOpen 𝒰.objSet :=
  isOpen_of_discrete_left fun i => 𝒰.isOpen i

theorem isOpen_morSet : IsOpen 𝒰.morSet :=
  isOpen_of_discrete_left fun ij =>
    ((𝒰.isOpen ij.1).preimage X.continuous_src).inter ((𝒰.isOpen ij.2).preimage X.continuous_tgt)

instance : ParacompactSpace 𝒰.objSet :=
  ((discretePolyfold ι).prod X.PObj).paracompactSpace_subtype _

instance : ParacompactSpace 𝒰.morSet :=
  ((discretePolyfold (ι × ι)).prod X.PMor).paracompactSpace_subtype _

instance [Nonempty Obj] : Nonempty 𝒰.objSet := by
  obtain ⟨x⟩ := ‹Nonempty Obj›
  obtain ⟨i, hi⟩ := 𝒰.exists_mem x
  exact ⟨⟨(i, x), hi⟩⟩

instance [Nonempty Obj] : Nonempty 𝒰.morSet := by
  obtain ⟨x⟩ := ‹Nonempty Obj›
  obtain ⟨i, hi⟩ := 𝒰.exists_mem x
  exact ⟨⟨((i, i), X.unit x), show X.src (X.unit x) ∈ 𝒰.set i ∧ X.tgt (X.unit x) ∈ 𝒰.set i from
    ⟨by rw [X.src_unit]; exact hi, by rw [X.tgt_unit]; exact hi⟩⟩⟩

end Topology

/-! #### The structure maps -/

/-- `s(i, φ, j) = (i, s φ)`. -/
def src (q : 𝒰.morSet) : 𝒰.objSet := ⟨(q.1.1.1, X.src q.1.2), q.2.1⟩

/-- `t(i, φ, j) = (j, t φ)`. -/
def tgt (q : 𝒰.morSet) : 𝒰.objSet := ⟨(q.1.1.2, X.tgt q.1.2), q.2.2⟩

theorem comp_mem {q q' : 𝒰.morSet} (h : X.src q.1.2 = X.tgt q'.1.2) :
    ((q'.1.1.1, q.1.1.2), X.comp q.1.2 q'.1.2) ∈ 𝒰.morSet :=
  ⟨by rw [X.src_comp _ _ h]; exact q'.2.1, by rw [X.tgt_comp _ _ h]; exact q.2.2⟩

open scoped Classical in
/-- `(j, ψ, k) ∘ (i, φ, j) = (i, ψ ∘ φ, k)` (the first argument for a non-composable pair). -/
def comp (q q' : 𝒰.morSet) : 𝒰.morSet :=
  if h : X.src q.1.2 = X.tgt q'.1.2 then ⟨_, 𝒰.comp_mem h⟩ else q

/-- `1_(i, x) = (i, 1_x, i)`. -/
def unit (p : 𝒰.objSet) : 𝒰.morSet :=
  ⟨((p.1.1, p.1.1), X.unit p.1.2), show X.src (X.unit p.1.2) ∈ 𝒰.set p.1.1 ∧
    X.tgt (X.unit p.1.2) ∈ 𝒰.set p.1.1 from
    ⟨by rw [X.src_unit]; exact p.2, by rw [X.tgt_unit]; exact p.2⟩⟩

/-- `(i, φ, j)⁻¹ = (j, φ⁻¹, i)`. -/
def inv (q : 𝒰.morSet) : 𝒰.morSet :=
  ⟨((q.1.1.2, q.1.1.1), X.inv q.1.2), show X.src (X.inv q.1.2) ∈ 𝒰.set q.1.1.2 ∧
    X.tgt (X.inv q.1.2) ∈ 𝒰.set q.1.1.1 from
    ⟨by rw [X.src_inv]; exact q.2.2, by rw [X.tgt_inv]; exact q.2.1⟩⟩

variable {𝒰}

theorem comp_val {q q' : 𝒰.morSet} (h : X.src q.1.2 = X.tgt q'.1.2) :
    (𝒰.comp q q').1 = ((q'.1.1.1, q.1.1.2), X.comp q.1.2 q'.1.2) := by
  rw [comp, dif_pos h]

theorem morSet_ext {q q' : 𝒰.morSet} (h₁ : q.1.1.1 = q'.1.1.1) (h₂ : q.1.1.2 = q'.1.1.2)
    (h₃ : q.1.2 = q'.1.2) : q = q' :=
  Subtype.ext (Prod.ext (Prod.ext h₁ h₂) h₃)

theorem objSet_ext {p p' : 𝒰.objSet} (h₁ : p.1.1 = p'.1.1) (h₂ : p.1.2 = p'.1.2) : p = p' :=
  Subtype.ext (Prod.ext h₁ h₂)

theorem src_eq_tgt {q q' : 𝒰.morSet} (h : 𝒰.src q = 𝒰.tgt q') :
    q.1.1.1 = q'.1.1.2 ∧ X.src q.1.2 = X.tgt q'.1.2 :=
  ⟨congrArg (fun p : 𝒰.objSet => p.1.1) h, congrArg (fun p : 𝒰.objSet => p.1.2) h⟩

variable (𝒰)

/-- **The groupoid `X_𝒰`** (2021 p. 462): objects `(i, x)`, morphisms `(i, φ, j)`. -/
def groupoidStr : GroupoidStr 𝒰.objSet 𝒰.morSet where
  src := 𝒰.src
  tgt := 𝒰.tgt
  comp := 𝒰.comp
  unit := 𝒰.unit
  inv := 𝒰.inv
  src_comp q q' h := by
    have h' := (src_eq_tgt h).2
    exact objSet_ext (show (𝒰.comp q q').1.1.1 = q'.1.1.1 by rw [comp_val h'])
      (show X.src (𝒰.comp q q').1.2 = X.src q'.1.2 by rw [comp_val h']; exact X.src_comp _ _ h')
  tgt_comp q q' h := by
    have h' := (src_eq_tgt h).2
    exact objSet_ext (show (𝒰.comp q q').1.1.2 = q.1.1.2 by rw [comp_val h'])
      (show X.tgt (𝒰.comp q q').1.2 = X.tgt q.1.2 by rw [comp_val h']; exact X.tgt_comp _ _ h')
  comp_assoc q q' q'' h₁ h₂ := by
    have h₁' := (src_eq_tgt h₁).2
    have h₂' := (src_eq_tgt h₂).2
    have h₃ : X.src (𝒰.comp q q').1.2 = X.tgt q''.1.2 := by
      rw [comp_val h₁', X.src_comp _ _ h₁', h₂']
    have h₄ : X.src q.1.2 = X.tgt (𝒰.comp q' q'').1.2 := by
      rw [comp_val h₂', X.tgt_comp _ _ h₂', h₁']
    refine morSet_ext ?_ ?_ ?_
    · rw [comp_val h₃, comp_val h₄, comp_val h₂']
    · rw [comp_val h₃, comp_val h₄, comp_val h₁']
    · rw [comp_val h₃, comp_val h₄, comp_val h₁', comp_val h₂']
      exact X.comp_assoc _ _ _ h₁' h₂'
  src_unit p := objSet_ext rfl (X.src_unit p.1.2)
  tgt_unit p := objSet_ext rfl (X.tgt_unit p.1.2)
  comp_unit q := by
    have h : X.src q.1.2 = X.tgt (𝒰.unit (𝒰.src q)).1.2 := (X.tgt_unit _).symm
    refine morSet_ext ?_ ?_ ?_
    · rw [comp_val h]; rfl
    · rw [comp_val h]
    · rw [comp_val h]; exact X.comp_unit _
  unit_comp q := by
    have h : X.src (𝒰.unit (𝒰.tgt q)).1.2 = X.tgt q.1.2 := X.src_unit _
    refine morSet_ext ?_ ?_ ?_
    · rw [comp_val h]
    · rw [comp_val h]; rfl
    · rw [comp_val h]; exact X.unit_comp _
  src_inv q := objSet_ext rfl (X.src_inv q.1.2)
  tgt_inv q := objSet_ext rfl (X.tgt_inv q.1.2)
  comp_inv q := by
    have h : X.src q.1.2 = X.tgt (𝒰.inv q).1.2 := (X.tgt_inv _).symm
    refine morSet_ext ?_ ?_ ?_
    · rw [comp_val h]; rfl
    · rw [comp_val h]; rfl
    · rw [comp_val h]; exact X.comp_inv _
  inv_comp q := by
    have h : X.src (𝒰.inv q).1.2 = X.tgt q.1.2 := X.src_inv _
    refine morSet_ext ?_ ?_ ?_
    · rw [comp_val h]; rfl
    · rw [comp_val h]; rfl
    · rw [comp_val h]; exact X.inv_comp _

/-! #### The M-polyfold structures -/

variable [TopologicalSpace ι] [DiscreteTopology ι] [Nonempty Obj]

/-- The object M-polyfold of `X_𝒰`: the open subset `⊔ U_i` of `ι × X` (`ι` discrete). -/
def objPolyfold : MPolyfold 𝒰.objSet :=
  ((discretePolyfold ι).prod X.PObj).restrictOpen 𝒰.isOpen_objSet

/-- The morphism M-polyfold of `X_𝒰`: an open subset of `(ι × ι) × 𝐗`. -/
def morPolyfold : MPolyfold 𝒰.morSet :=
  ((discretePolyfold (ι × ι)).prod X.PMor).restrictOpen 𝒰.isOpen_morSet

/-- The source map on the ambient spaces, `((i, j), φ) ↦ (i, s φ)`. -/
def srcAmb (q : (ι × ι) × Mor) : ι × Obj := (q.1.1, X.src q.2)

/-- The target map on the ambient spaces, `((i, j), φ) ↦ (j, t φ)`. -/
def tgtAmb (q : (ι × ι) × Mor) : ι × Obj := (q.1.2, X.tgt q.2)

omit [DiscreteTopology ι] [Nonempty Obj] in
theorem continuous_srcAmb : Continuous (srcAmb (X := X) (ι := ι)) :=
  (continuous_fst.comp continuous_fst).prodMk (X.continuous_src.comp continuous_snd)

omit [DiscreteTopology ι] [Nonempty Obj] in
theorem continuous_tgtAmb : Continuous (tgtAmb (X := X) (ι := ι)) :=
  (continuous_snd.comp continuous_fst).prodMk (X.continuous_tgt.comp continuous_snd)

omit [Nonempty Obj] in
theorem isLocalScDiffeoAt_srcAmb (q : (ι × ι) × Mor) :
    ((discretePolyfold (ι × ι)).prod X.PMor).IsLocalScDiffeoAt
      ((discretePolyfold ι).prod X.PObj) (srcAmb (X := X)) q := by
  have h := MPolyfold.IsLocalScDiffeoAt.comp ((isLocalScDiffeo_sheet (PY := X.PObj) q.1.1).at _)
    (MPolyfold.IsLocalScDiffeoAt.comp (X.isLocalScDiffeo_src.at q.2)
      ((isLocalScDiffeo_snd_discrete (PY := X.PMor)).at q))
  refine h.congr ?_
  filter_upwards [(isOpen_sheet (X := Mor) q.1).mem_nhds ⟨mem_singleton _, mem_univ _⟩]
    with q' hq'
  have hq'1 : q'.1 = q.1 := hq'.1
  simp only [Function.comp_apply, srcAmb, hq'1]

omit [Nonempty Obj] in
theorem isLocalScDiffeoAt_tgtAmb (q : (ι × ι) × Mor) :
    ((discretePolyfold (ι × ι)).prod X.PMor).IsLocalScDiffeoAt
      ((discretePolyfold ι).prod X.PObj) (tgtAmb (X := X)) q := by
  have h := MPolyfold.IsLocalScDiffeoAt.comp ((isLocalScDiffeo_sheet (PY := X.PObj) q.1.2).at _)
    (MPolyfold.IsLocalScDiffeoAt.comp (X.isLocalScDiffeo_tgt.at q.2)
      ((isLocalScDiffeo_snd_discrete (PY := X.PMor)).at q))
  refine h.congr ?_
  filter_upwards [(isOpen_sheet (X := Mor) q.1).mem_nhds ⟨mem_singleton _, mem_univ _⟩]
    with q' hq'
  have hq'1 : q'.1 = q.1 := hq'.1
  simp only [Function.comp_apply, tgtAmb, hq'1]

theorem isLocalScDiffeo_src : 𝒰.morPolyfold.IsLocalScDiffeo 𝒰.objPolyfold 𝒰.src := fun q =>
  MPolyfold.isLocalScDiffeoAt_restrict 𝒰.isOpen_morSet 𝒰.isOpen_objSet continuous_srcAmb
    (fun q => q.2.1) (isLocalScDiffeoAt_srcAmb q.1)

theorem isLocalScDiffeo_tgt : 𝒰.morPolyfold.IsLocalScDiffeo 𝒰.objPolyfold 𝒰.tgt := fun q =>
  MPolyfold.isLocalScDiffeoAt_restrict 𝒰.isOpen_morSet 𝒰.isOpen_objSet continuous_tgtAmb
    (fun q => q.2.2) (isLocalScDiffeoAt_tgtAmb q.1)

theorem isScSmoothMap_unit : 𝒰.objPolyfold.IsScSmoothMap 𝒰.morPolyfold 𝒰.unit := by
  have hF : ((discretePolyfold ι).prod X.PObj).IsScSmoothMap
      ((discretePolyfold (ι × ι)).prod X.PMor) fun p : ι × Obj => ((p.1, p.1), X.unit p.2) :=
    isScSmoothMap_prod_discrete_iff.2 fun i =>
      (isScSmoothMap_sheet (PX := X.PMor) (i, i)).comp X.isScSmoothMap_unit
  exact MPolyfold.isScSmoothMap_restrict 𝒰.isOpen_objSet 𝒰.isOpen_morSet hF
    fun p => (𝒰.unit p).2

theorem isScSmoothMap_inv : 𝒰.morPolyfold.IsScSmoothMap 𝒰.morPolyfold 𝒰.inv := by
  have hF : ((discretePolyfold (ι × ι)).prod X.PMor).IsScSmoothMap
      ((discretePolyfold (ι × ι)).prod X.PMor)
      fun q : (ι × ι) × Mor => ((q.1.2, q.1.1), X.inv q.2) :=
    isScSmoothMap_prod_discrete_iff.2 fun ij =>
      (isScSmoothMap_sheet (PX := X.PMor) (ij.2, ij.1)).comp X.isScSmoothMap_inv
  exact MPolyfold.isScSmoothMap_restrict 𝒰.isOpen_morSet 𝒰.isOpen_morSet hF
    fun q => (𝒰.inv q).2

omit [DiscreteTopology ι] [Nonempty Obj] in
theorem continuous_src : Continuous 𝒰.src :=
  (continuous_srcAmb.comp continuous_subtype_val).subtype_mk _

omit [DiscreteTopology ι] [Nonempty Obj] in
theorem continuous_tgt : Continuous 𝒰.tgt :=
  (continuous_tgtAmb.comp continuous_subtype_val).subtype_mk _

/-! #### Properness (the proof of Proposition 10.1.3) -/

omit [Nonempty Obj] in
/-- `X_𝒰` is proper: for `(i, x)` take `V(x)` with `cl V(x) ⊆ U_i` inside a neighbourhood with the
properness property of `X`, and `Vt = {i} × V(x)`. -/
theorem exists_isProperMap (p : 𝒰.objSet) : ∃ V : Set 𝒰.objSet, IsOpen V ∧ p ∈ V ∧
    IsProperMap ((𝒰.src ⁻¹' closure V).domRestrict 𝒰.tgt) := by
  obtain ⟨V₀, hV₀o, hpV₀, hprop⟩ := X.exists_isProperMap p.1.2
  have := X.PObj.metrizableSpace
  have hW : 𝒰.set p.1.1 ∩ V₀ ∈ 𝓝 p.1.2 := ((𝒰.isOpen _).inter hV₀o).mem_nhds ⟨p.2, hpV₀⟩
  obtain ⟨C, hC, hCc, hCsub⟩ := exists_mem_nhds_isClosed_subset hW
  have hclV : closure (interior C) ⊆ 𝒰.set p.1.1 ∩ V₀ :=
    (closure_minimal interior_subset hCc).trans hCsub
  set Vt : Set 𝒰.objSet := Subtype.val ⁻¹' ({p.1.1} ×ˢ interior C) with hVt
  refine ⟨Vt, ((isOpen_discrete _).prod isOpen_interior).preimage continuous_subtype_val,
    ⟨mem_singleton _, mem_interior_iff_mem_nhds.2 hC⟩, ?_⟩
  have hD : ∀ q : 𝒰.morSet, 𝒰.src q ∈ closure Vt →
      q.1.1.1 = p.1.1 ∧ X.src q.1.2 ∈ closure (interior C) := by
    intro q hq
    have h1 := continuous_subtype_val.closure_preimage_subset _ hq
    rw [closure_prod_eq, closure_singleton] at h1
    exact ⟨h1.1, h1.2⟩
  have hsub₀ : closure (interior C) ⊆ closure V₀ :=
    closure_mono (interior_subset.trans (hCsub.trans inter_subset_right))
  rw [isProperMap_iff_ultrafilter]
  refine ⟨𝒰.continuous_tgt.comp continuous_subtype_val, fun 𝒱 y hy => ?_⟩
  have hj : ∀ᶠ d in (𝒱 : Filter (𝒰.src ⁻¹' closure Vt)), d.1.1.1.2 = y.1.1 := by
    have h := ((continuous_fst.comp continuous_subtype_val).tendsto y).comp hy
    rwa [nhds_discrete, tendsto_pure] at h
  have hsrc : ∀ d : 𝒰.src ⁻¹' closure Vt, X.src d.1.1.2 ∈ closure V₀ := fun d =>
    hsub₀ (hD d.1 d.2).2
  let g : 𝒰.src ⁻¹' closure Vt → X.src ⁻¹' closure V₀ := fun d => ⟨d.1.1.2, hsrc d⟩
  have h2 : Tendsto ((X.src ⁻¹' closure V₀).domRestrict X.tgt) (Ultrafilter.map g 𝒱)
      (𝓝 y.1.2) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff]
    exact ((continuous_snd.comp continuous_subtype_val).tendsto y).comp hy
  obtain ⟨φ', hφ'y, hle⟩ := (isProperMap_iff_ultrafilter.1 hprop).2 h2
  have hg : Tendsto g 𝒱 (𝓝 φ') := by
    rw [Ultrafilter.coe_map] at hle
    exact hle
  have hφ : Tendsto (fun d : 𝒰.src ⁻¹' closure Vt => d.1.1.2) 𝒱 (𝓝 φ'.1) :=
    (continuous_subtype_val.tendsto φ').comp hg
  have hsφ : X.src φ'.1 ∈ closure (interior C) :=
    isClosed_closure.mem_of_tendsto ((X.continuous_src.tendsto _).comp hφ)
      (Eventually.of_forall fun d => (hD d.1 d.2).2)
  have htφ : X.tgt φ'.1 = y.1.2 := hφ'y
  let d₀ : 𝒰.morSet := ⟨((p.1.1, y.1.1), φ'.1), (hclV hsφ).1, by
    change X.tgt φ'.1 ∈ 𝒰.set y.1.1
    rw [htφ]
    exact y.2⟩
  have hd₀ : Tendsto (fun d : 𝒰.src ⁻¹' closure Vt => d.1) 𝒱 (𝓝 d₀) := by
    rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds ?_ hφ
    rw [nhds_discrete, tendsto_pure]
    filter_upwards [hj] with d hdj
    exact Prod.ext (hD d.1 d.2).1 hdj
  have hd₀D : 𝒰.src d₀ ∈ closure Vt :=
    isClosed_closure.mem_of_tendsto ((𝒰.continuous_src.tendsto _).comp hd₀)
      (Eventually.of_forall fun d => d.2)
  refine ⟨⟨d₀, hd₀D⟩, objSet_ext rfl htφ, ?_⟩
  have := (Topology.IsInducing.subtypeVal.tendsto_nhds_iff (f := id)
    (y := (⟨d₀, hd₀D⟩ : 𝒰.src ⁻¹' closure Vt))).2 hd₀
  exact tendsto_id'.1 this

/-! #### The composition -/

theorem isScSmoothCompSheet :
    IsScSmoothCompSheet 𝒰.objPolyfold 𝒰.morPolyfold 𝒰.src 𝒰.tgt 𝒰.comp := by
  intro σ W V hd
  have hΩ : IsOpen (𝒰.tgt ⁻¹' V) := hd.isScSmoothOn_inv.isOpen.preimage 𝒰.continuous_tgt
  have hσt : 𝒰.morPolyfold.IsScSmoothOn 𝒰.morPolyfold (σ ∘ 𝒰.tgt) (𝒰.tgt ⁻¹' V) :=
    MPolyfold.IsScSmoothOn.comp hd.isScSmoothOn_inv
      ((𝒰.isLocalScDiffeo_tgt.isScSmoothMap).mono hΩ (subset_univ _)) fun _ h => h
  -- `m(ψ) = σ(t ψ)` in the ambient space
  have hm : 𝒰.morPolyfold.IsScSmoothOn ((discretePolyfold (ι × ι)).prod X.PMor)
      (fun ψ => (σ (𝒰.tgt ψ)).1) (𝒰.tgt ⁻¹' V) :=
    MPolyfold.IsScSmoothOn.comp (MPolyfold.isScSmoothMap_subtypeVal 𝒰.isOpen_morSet) hσt
      (mapsTo_univ _ _)
  have hm₂ : 𝒰.morPolyfold.IsScSmoothOn X.PMor (fun ψ => (σ (𝒰.tgt ψ)).1.2) (𝒰.tgt ⁻¹' V) :=
    MPolyfold.IsScSmoothOn.comp (MPolyfold.isScSmoothMap_snd _ _) hm (mapsTo_univ _ _)
  have hkey : ∀ ψ ∈ 𝒰.tgt ⁻¹' V, X.src (σ (𝒰.tgt ψ)).1.2 = X.tgt ψ.1.2 := fun ψ hψ =>
    congrArg (fun p : 𝒰.objSet => p.1.2) (hd.right_inv _ hψ)
  have hψ2 : 𝒰.morPolyfold.IsScSmoothMap X.PMor fun ψ : 𝒰.morSet => ψ.1.2 :=
    (MPolyfold.isScSmoothMap_snd _ _).comp (MPolyfold.isScSmoothMap_subtypeVal 𝒰.isOpen_morSet)
  -- the composite in `𝐗`
  have hG₂ : 𝒰.morPolyfold.IsScSmoothOn X.PMor
      (fun ψ => X.comp (σ (𝒰.tgt ψ)).1.2 ψ.1.2) (𝒰.tgt ⁻¹' V) := by
    refine MPolyfold.IsScSmoothOn.of_locally hΩ fun ψ₀ hψ₀ => ?_
    obtain ⟨W₀, V₀, σ₀, hmem, hd₀⟩ := X.isLocalScDiffeo_src (σ (𝒰.tgt ψ₀)).1.2
    have hΩ₀ : IsOpen (𝒰.tgt ⁻¹' V ∩ (fun ψ => (σ (𝒰.tgt ψ)).1.2) ⁻¹' W₀) :=
      hm₂.continuousOn.isOpen_inter_preimage hΩ hd₀.isOpen_source
    refine ⟨_, hΩ₀, ⟨hψ₀, hmem⟩, inter_subset_left, ?_⟩
    have hX := X.isScSmoothCompSheet σ₀ W₀ V₀ hd₀
    refine (MPolyfold.IsScSmoothOn.comp hX (hψ2.mono hΩ₀ (subset_univ _)) fun ψ hψ => ?_).congr
      fun ψ hψ => ?_
    · change X.tgt ψ.1.2 ∈ V₀
      rw [← hkey ψ hψ.1]
      exact hd₀.mapsTo hψ.2
    · change X.comp (σ₀ (X.tgt ψ.1.2)) ψ.1.2 = X.comp (σ (𝒰.tgt ψ)).1.2 ψ.1.2
      rw [← hkey ψ hψ.1, hd₀.left_inv _ hψ.2]
  have hG₁ : 𝒰.morPolyfold.IsScSmoothOn (discretePolyfold (ι × ι))
      (fun ψ => (ψ.1.1.1, (σ (𝒰.tgt ψ)).1.1.2)) (𝒰.tgt ⁻¹' V) :=
    isScSmoothOn_discrete_of_continuousOn hΩ
      ((continuous_fst.comp (continuous_fst.comp continuous_subtype_val)).continuousOn.prodMk
        ((continuous_snd.comp continuous_fst).comp_continuousOn hm.continuousOn))
  refine (MPolyfold.isScSmoothOn_restrictOpen_iff 𝒰.isOpen_morSet).2
    ((MPolyfold.IsScSmoothOn.prodMk hG₁ hG₂).congr fun ψ hψ => ?_)
  change _ = (𝒰.comp (σ (𝒰.tgt ψ)) ψ).1
  rw [comp_val (hkey ψ hψ)]

/-- **2021 Proposition 10.1.3, p. 462 (2017: Proposition 10.1, p. 334), first part**: the
refinement `X_𝒰` of `X` associated with an open covering `𝒰` is an ep-groupoid. -/
def epGroupoid : EpGroupoid 𝒰.objSet 𝒰.morSet where
  toGroupoidStr := 𝒰.groupoidStr
  PObj := 𝒰.objPolyfold
  PMor := 𝒰.morPolyfold
  isLocalScDiffeo_src := 𝒰.isLocalScDiffeo_src
  isLocalScDiffeo_tgt := 𝒰.isLocalScDiffeo_tgt
  isScSmoothMap_unit := 𝒰.isScSmoothMap_unit
  isScSmoothMap_inv := 𝒰.isScSmoothMap_inv
  exists_isProperMap := 𝒰.exists_isProperMap
  isScSmoothComp := (isScSmoothComp_iff_sheet _ _).2 𝒰.isScSmoothCompSheet

/-- **The functor `F : X_𝒰 → X`**, `(i, x) ↦ x`, `(i, φ, j) ↦ φ` (Proposition 10.1.3). -/
def functor : EpFunctor 𝒰.epGroupoid X where
  obj p := p.1.2
  mor q := q.1.2
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ h := comp_val (src_eq_tgt h).2 ▸ rfl
  mor_unit _ := rfl
  isScSmoothMap_obj :=
    (MPolyfold.isScSmoothMap_snd _ _).comp (MPolyfold.isScSmoothMap_subtypeVal 𝒰.isOpen_objSet)
  isScSmoothMap_mor :=
    (MPolyfold.isScSmoothMap_snd _ _).comp (MPolyfold.isScSmoothMap_subtypeVal 𝒰.isOpen_morSet)

/-- **2021 Proposition 10.1.3, p. 462 (2017: Proposition 10.1, p. 334)**: `F : X_𝒰 → X` is an
equivalence of ep-groupoids. -/
theorem proposition_10_1_3 : 𝒰.functor.IsEquivalence :=
  𝒰.functor.lemma_10_1_2
    { faithful := (GroupoidFunctor.faithful_iff _).2 fun _ _ hs ht he =>
        morSet_ext (congrArg (fun p : 𝒰.objSet => p.1.1) hs)
          (congrArg (fun p : 𝒰.objSet => p.1.1) ht) he
      full := (GroupoidFunctor.full_iff _).2 fun p p' ψ hs ht =>
        ⟨⟨((p.1.1, p'.1.1), ψ), show X.src ψ ∈ 𝒰.set p.1.1 ∧ X.tgt ψ ∈ 𝒰.set p'.1.1 from
          ⟨hs ▸ p.2, ht ▸ p'.2⟩⟩, objSet_ext rfl hs, objSet_ext rfl ht, rfl⟩
      essSurj := (GroupoidFunctor.essSurj_iff _).2 fun y => by
        obtain ⟨i, hi⟩ := 𝒰.exists_mem y
        exact ⟨⟨(i, y), hi⟩, X.unit y, X.src_unit y, X.tgt_unit y⟩ }
    ((isLocalScDiffeo_snd_discrete (PY := X.PObj)).comp
      (MPolyfold.isLocalScDiffeo_subtypeVal 𝒰.isOpen_objSet))

end OpenCover

namespace Examples

/-- **A two-set covering** of `ℤ/2 ⋉ ℝ` (`reflectionEpGroupoid`): `U_true = {x > -1}`,
`U_false = {x < 1}`; they overlap on `(-1, 1)`. -/
def reflectionCover : reflectionEpGroupoid.OpenCover Bool where
  set b := match b with
    | true => {x | -1 < x 0}
    | false => {x | x 0 < 1}
  isOpen b := by
    cases b
    · exact isOpen_lt (continuous_apply 0) continuous_const
    · exact isOpen_lt continuous_const (continuous_apply 0)
  exists_mem x := by
    by_cases h : x 0 < 1
    · exact ⟨false, h⟩
    · exact ⟨true, show -1 < x 0 by linarith [not_lt.1 h]⟩

/-- **Proposition 10.1.3 for the two-set covering**: `X_𝒰 → ℤ/2 ⋉ ℝ` is an equivalence. -/
theorem isEquivalence_reflectionCover : reflectionCover.functor.IsEquivalence :=
  reflectionCover.proposition_10_1_3

/-- The equivalence `X_𝒰 → X` is not injective on objects: `(true, 0)` and `(false, 0)` both go to
`0`; so it is not an isomorphism. -/
theorem not_injective_reflectionCover_obj : ¬ Function.Injective reflectionCover.functor.obj := by
  intro h
  have h' := @h ⟨(true, 0), show (-1 : ℝ) < (0 : Fin 1 → ℝ) 0 by norm_num⟩
    ⟨(false, 0), show (0 : Fin 1 → ℝ) 0 < 1 by norm_num⟩ rfl
  exact absurd (congrArg (fun p : reflectionCover.objSet => p.1.1) h') (by decide)

end Examples

end EpGroupoid

end Polyfold
