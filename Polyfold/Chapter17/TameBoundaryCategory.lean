import Polyfold.Chapter17.TameBoundaryGerms
import Polyfold.Chapter17.LevelOneCategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.4 (pp. 787–792): the good open neighbourhoods recalled in **(17.53)–(17.55)**,
**Definition 17.4.1** (the faces `F_{U(ō)}`), the tuples and the relation **(17.56)–(17.58)**,
**Definition 17.4.2** (the objects of `bC`), **Definition 17.4.3** (the morphisms), the forgetful
map **(17.59)**, **Definition 17.4.4** (the morphism class and the forgetful functor
`B_C : bC → ∂C`, (17.63)).  Numbers and pages are the 2021
text's.

# The tame boundary category `bC`: objects and morphisms

## The text, paraphrased

(p. 787) For a tame ep-groupoid and `x ∈ ∂X`, a good open neighbourhood `U(x) = V(x) ∩ ∂X`
(Proposition 14.1.1, Definition 14.1.2): `V(x)` open with the natural `G_x`-action, `V(x)` and
`V(x) ∩ ∂X` connected, `t` proper on `s⁻¹(cl V(x))`, `d_X(x)` components `θᵢ°` of
`{d_X = 1}` whose closures `θᵢ` in `V(x)` contain `x`, with `d_X(y) = #{i | y ∈ θᵢ}`; hence
`U(x) = ⋃ θᵢ` (17.55).  The `θᵢ` are the faces of `U(x)`; they depend only on `U(x)`.
(p. 788) For a tame polyfold `C = (C, F, M)`, `∂C` is the full subcategory of the `α` with
`d_C(α) ≥ 1`.  (**Definition 17.4.1**) For `Ψ ∈ F(α)`, `Ψ(ō) = α`, and a good open
neighbourhood `U(ō) ⊆ ∂O`, `F_{U(ō)}` is the set of its faces.  (17.56)–(17.58) Tuples
`(α, Ψ, U(ō), θ)` with `θ ∈ F_{U(ō)}`; `(α, Ψ, U(ō), θ) ∼ (α', Ψ', U'(ō'), θ')` iff `α = α'` and
the local sc-diffeomorphism `f` of `h = (ō, 1_α, ō') ∈ M(Ψ, Ψ')` maps `θ` near `ō` onto `θ'` near
`ō'`.  (**Definition 17.4.2**) The objects of `bC` are the classes `[α, Ψ, U(ō), θ]`;
`[α, Ψ, U(ō), θ] ↦ α` (17.59).  (**Definition 17.4.3**) A morphism `Φ = (ᾱ, φ, ᾱ')` is a
morphism `φ : α → α'` of `C` whose `f` (of `h = (ō, φ, ō')`) maps `θ` near `ō` onto `θ'` near
`ō'`; `θ' = f_*θ` is determined by `θ`; given `ᾱ` and `φ` there is a unique `ᾱ'` and a unique
`Φ : ᾱ → ᾱ'` over `φ`.  (**Definition 17.4.4**) These `Φ` form the morphism class of `bC`, and
`ᾱ ↦ α`, `Φ ↦ φ` is the forgetful functor `B_C : bC → ∂C` (17.63).  (p. 791) Over an object `α`
of `∂C` lie finitely many `ᾱᵢ`.  (p. 792) The isotropy group `G` of `α` acts on `F_{U(ō)}` by
permutations.  (**Definition 17.4.5**) `G_θ` is the subgroup of `G` fixing `θ`.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `GoodNbhd Ψ o` (Definition 14.1.2 for the ep-groupoid `G ⋉ O` of `Ψ`), `GoodNbhd.faces`
  (`F_{U(ō)}`) and **`definition_17_4_1`**: every face contains `ō` and lies in `U(ō)`, the
  faces cover `U(ō)` (17.55), there are `d_O(ō)` of them, and they depend only on `U(ō)`
  (`faces_eq_of_bdry_eq`).
* `BdryTuple` (the tuples of (17.57)), `BdryTuple.Equiv` ((17.56), (17.58)), `bdryTupleSetoid`
  (an equivalence relation, `BdryTuple.equiv_refl/symm/trans`), **`BookObj`** (the classes of
  Definition 17.4.2) and the forgetful map `BookObj.base` (17.59).
* The model of the objects through a reference uniformizer `bdryRefUnif α ∈ F(α)`: `BObj` (an object
  `α` and a face germ at the point `refPt α` of `bdryRefUnif α`), `BdryTuple.toBObj`, and
  **`definition_17_4_2`** (`bookObjEquiv : BookObj ≃ BObj`).
* `BLift ᾱ φ ᾱ'` (Definition 17.4.3 (2), in the reference uniformizers), its independence of the
  representatives (`bLift_iff_tuple`), `existsUnique_bLift` (the unique `ᾱ'` and `Φ`, p. 790),
  `BMor` and **`definition_17_4_3`**, the groupoid `bC` (`bdryGroupoid`), the groupoidal category
  `bdryCategory` (finite hom-sets), and **`definition_17_4_4`**: the forgetful functor
  `bdryFunctor : bC → ∂C` (17.63), with `bdryFunctorC : bC → C`; over `α ∈ ∂C` lie exactly
  `d_C(α)` objects (`encard_obj_preimage`).
* Definition 17.4.5 (`G_θ`) and the action of `G` on `F_{U(ō)}` are in
  `TameBoundaryUniformizer.lean`.

## Readings

* "Good open neighbourhood `U(ō) ⊂ ∂O`" is Definition 14.1.2 for the translation ep-groupoid
  `G ⋉ O` of `Ψ` (the text: "we recall it here"): a natural neighbourhood `V` of `ō` with the
  properties (17.53); `U(ō) = V ∩ ∂O` is `NatNbhd.bdry`.  The faces of `U(ō)` are the faces of
  the open set `V` (2021 Definition 2.7.6), i.e. the `θᵢ` of (17.53) (4)
  (`HasBoundaryFaces.isFaceIn_iff`).
* (17.58) and Definition 17.4.3 (2), "`f(θ ∩ W(ō)) = θ' ∩ W'(ō')` for suitable small
  neighbourhoods" ("`θ` and `θ'` ... are identical up to `f` near `ō` and `ō'`"), are read on
  the level of face germs: `f` carries the class `[ō, V, θ]` of Part I's tame boundary `bO` to
  `[ō', V', θ']` (`GermLift`, `TameBoundaryGerms.lean`).
* The objects of `bC` are classes over the uniformizers `Ψ ∈ F(α)` and so live one universe up;
  the category `bC` is built on `BObj` (one reference uniformizer `bdryRefUnif α ∈ F(α)` per object,
  which needs `F(α) ≠ ∅`, `HasUniformizers`), and `bookObjEquiv` identifies `BObj` with the
  classes of Definition 17.4.2.  `BLift` is the condition of Definition 17.4.3 (2) in the
  reference uniformizers; `bLift_iff_tuple` shows that it is the condition for every choice of
  representatives.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

universe u

namespace Polyfold

open TameBoundary

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-! ### Definition 17.4.1: good open neighbourhoods and their faces -/

section Good

variable (S) in
/-- **A good open neighbourhood `U(ō) = V(ō) ∩ ∂O` of `ō`** (2021 (17.53), Definition 14.1.2 for
the translation ep-groupoid `G ⋉ O` of `Ψ`): a natural neighbourhood `V(ō)` with the properties
(17.53). -/
abbrev GoodNbhd (Ψ : S.Unif) (o : Ψ.1.O) : Type u :=
  {V : Ψ.1.ep.NatNbhd o // Ψ.1.ep.IsGoodBoundaryNbhd V}

namespace GoodNbhd

variable {Ψ : S.Unif} {o : Ψ.1.O} (V : S.GoodNbhd Ψ o)

/-- **The faces `F_{U(ō)}` of the good neighbourhood** (2021 Definition 17.4.1): the faces of the
open set `V(ō)` (2021 Definition 2.7.6), i.e. the `θᵢ` of (17.53) (4). -/
def faces : Set (Set Ψ.1.O) := {θ | IsFaceIn Ψ.1.P.degIndex V.1.U θ}

/-- `U(ō) = V(ō) ∩ ∂O`. -/
abbrev bdry : Set Ψ.1.O := V.1.bdry

theorem mem_faces_iff {θ : Set Ψ.1.O} : θ ∈ V.faces ↔ IsFaceIn Ψ.1.P.degIndex V.1.U θ := Iff.rfl

omit V in
theorem mem_boundary (V : S.GoodNbhd Ψ o) : o ∈ Ψ.1.P.boundary := V.2.mem_boundary

omit V in
theorem one_le_degIndex (V : S.GoodNbhd Ψ o) : 1 ≤ Ψ.1.P.degIndex o := V.mem_boundary

theorem isOpen : IsOpen V.1.U := V.1.isOpen_U

theorem mem : o ∈ V.1.U := V.1.mem_U

/-- `V(ō)` is a face-structured open set. -/
theorem isFaceStructuredOpen : IsFaceStructuredOpen Ψ.1.P.degIndex V.1.U := by
  obtain ⟨θ, hθ⟩ := V.2.hasFaces
  exact hθ.isFaceStructuredOpen V.1.isOpen_U

/-- Every face of `V(ō)` contains `ō` (17.53) (4): `V(ō)` is centred at `ō`. -/
theorem isCenteredAt : IsCenteredAt Ψ.1.P.degIndex o V.1.U := by
  intro γ hγ
  obtain ⟨θ, hθ⟩ := V.2.hasFaces
  obtain ⟨i, rfl⟩ := hθ.isFaceIn_iff.1 hγ
  exact (hθ.mem_closure i).2 |> fun h => ⟨V.1.mem_U, h⟩

/-- `d_O ≤ d_O(ō)` on `V(ō)` ((17.54)). -/
theorem degIndex_le {y : Ψ.1.O} (hy : y ∈ V.1.U) : Ψ.1.P.degIndex y ≤ Ψ.1.P.degIndex o := by
  obtain ⟨θ, hθ⟩ := V.2.hasFaces
  have h := hθ.deg_eq y hy
  have hle : {i | y ∈ V.1.U ∩ closure (θ i)}.encard ≤ (univ : Set (Fin _)).encard :=
    encard_le_encard (subset_univ _)
  rw [h, encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] at hle
  exact_mod_cast hle

/-- `V(ō) ∈ N_{O,ō}` (2021 Definition 2.7.6). -/
theorem mem_faceStructuredNbhdsAt : V.1.U ∈ faceStructuredNbhdsAt Ψ.1.P.degIndex o :=
  ⟨⟨V.isFaceStructuredOpen, ⟨o, V.mem⟩, ⟨Ψ.1.P.degIndex o, by
    rintro _ ⟨y, hy, rfl⟩; exact V.degIndex_le hy⟩⟩, V.mem, fun _ hy => V.degIndex_le hy⟩

theorem mem_of_mem_faces {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) : o ∈ θ := V.isCenteredAt θ hθ

theorem faces_eq_facesThrough : V.faces = facesThrough Ψ.1.P.degIndex V.1.U o := by
  ext θ
  exact ⟨fun h => ⟨h, V.mem_of_mem_faces h⟩, fun h => h.1⟩

/-- A face of `U(ō)` lies in `U(ō)`. -/
theorem subset_bdry {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) : θ ⊆ V.bdry := by
  obtain ⟨γ, hγ⟩ := V.2.hasFaces
  obtain ⟨i, rfl⟩ := hγ.isFaceIn_iff.1 hθ
  change _ ⊆ V.1.U ∩ Ψ.1.ep.PObj.boundary
  rw [hγ.inter_boundary_eq]
  exact subset_iUnion (fun j => V.1.U ∩ closure (γ j)) i

/-- **(17.55)**: `U(ō)` is the union of its faces. -/
theorem sUnion_faces : ⋃₀ V.faces = V.bdry := by
  refine Subset.antisymm (sUnion_subset fun θ hθ => V.subset_bdry hθ) ?_
  obtain ⟨γ, hγ⟩ := V.2.hasFaces
  change V.1.U ∩ Ψ.1.ep.PObj.boundary ⊆ _
  rw [hγ.inter_boundary_eq]
  exact iUnion_subset fun i => subset_sUnion_of_mem (hγ.isFaceIn i)

/-- **There are `d_O(ō)` faces** ((17.53) (4)). -/
theorem encard_faces : V.faces.encard = Ψ.1.P.degIndex o := by
  rw [V.faces_eq_facesThrough]
  exact V.isFaceStructuredOpen.2 o V.mem

theorem finite_faces : V.faces.Finite :=
  Set.finite_of_encard_eq_coe V.encard_faces

/-- **The faces depend only on `U(ō)`, not on `V(ō)`** (2021 p. 787). -/
theorem faces_eq_of_bdry_eq {V' : S.GoodNbhd Ψ o} (h : V.bdry = V'.bdry) :
    V.faces = V'.faces := by
  have key : ∀ (W : S.GoodNbhd Ψ o) (θ : Set Ψ.1.O), θ ∈ W.faces ↔
      ∃ p ∈ W.bdry, Ψ.1.P.degIndex p = 1 ∧ θ = W.bdry ∩
        closure (connectedComponentIn (W.bdry ∩ {y | Ψ.1.P.degIndex y = 1}) p) := by
    intro W θ
    have hB : W.1.U ∩ {y | Ψ.1.P.degIndex y = 1} = W.bdry ∩ {y | Ψ.1.P.degIndex y = 1} := by
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun ⟨hy, h1⟩ => ⟨⟨hy, show 1 ≤ _ from h1.ge⟩, h1⟩, fun ⟨hy, h1⟩ => ⟨hy.1, h1⟩⟩
    have hcl : ∀ p, W.1.U ∩ closure (connectedComponentIn
        (W.bdry ∩ {y | Ψ.1.P.degIndex y = 1}) p) = W.bdry ∩ closure (connectedComponentIn
        (W.bdry ∩ {y | Ψ.1.P.degIndex y = 1}) p) := by
      intro p
      refine Subset.antisymm (fun y ⟨hy, hyc⟩ => ⟨⟨hy, ?_⟩, hyc⟩) (inter_subset_inter_left _
        inter_subset_left)
      have hsub : connectedComponentIn (W.bdry ∩ {y | Ψ.1.P.degIndex y = 1}) p ⊆
          Ψ.1.P.boundary :=
        (connectedComponentIn_subset _ _).trans fun z hz => hz.1.2
      exact closure_minimal hsub Ψ.1.P.isClosed_boundary hyc
    constructor
    · rintro ⟨p, hp, hp1, rfl⟩
      refine ⟨p, ⟨hp, show 1 ≤ _ from hp1.ge⟩, hp1, ?_⟩
      rw [faceAt, hB, hcl]
    · rintro ⟨p, hp, hp1, rfl⟩
      refine ⟨p, hp.1, hp1, ?_⟩
      rw [faceAt, hB, hcl]
  ext θ
  rw [key V θ, key V' θ, h]

end GoodNbhd

/-- **2021 Definition 17.4.1, p. 788**, with the remarks of p. 787: for a good open neighbourhood
`U(ō)` of `ō` the faces `F_{U(ō)}` contain `ō` and lie in `U(ō)`, cover `U(ō)` (17.55), are
`d_O(ō)` in number, and depend only on `U(ō)`. -/
theorem definition_17_4_1 {Ψ : S.Unif} {o : Ψ.1.O} (V : S.GoodNbhd Ψ o) :
    (∀ θ ∈ V.faces, o ∈ θ ∧ θ ⊆ V.bdry) ∧ ⋃₀ V.faces = V.bdry ∧
      V.faces.encard = Ψ.1.P.degIndex o ∧
      ∀ V' : S.GoodNbhd Ψ o, V.bdry = V'.bdry → V.faces = V'.faces :=
  ⟨fun _ hθ => ⟨V.mem_of_mem_faces hθ, V.subset_bdry hθ⟩, V.sUnion_faces, V.encard_faces,
    fun _ h => V.faces_eq_of_bdry_eq h⟩

/-- Good open neighbourhoods exist at every boundary point of `O` for a tame `Ψ`, inside every
open set (Proposition 14.1.1). -/
theorem exists_goodNbhd {Ψ : S.Unif} (hΨ : Ψ.1.P.IsTame) {o : Ψ.1.O}
    (ho : o ∈ Ψ.1.P.boundary) {W : Set Ψ.1.O} (hW : IsOpen W) (hoW : o ∈ W) :
    ∃ V : S.GoodNbhd Ψ o, V.1.U ⊆ W := by
  obtain ⟨V, hVW, hV⟩ := Ψ.1.ep.exists_isGoodBoundaryNbhd hΨ ho hW hoW
  exact ⟨⟨V, hV⟩, hVW⟩

end Good

/-! ### Face germs of good neighbourhoods -/

section FaceGerm

variable (hT : S.IsTame) {Ψ : S.Unif} {o : Ψ.1.O}

/-- The admissible triple `(ō, V(ō), θ)` of Part I (2021 Definition 2.7.10) of a face `θ` of a
good neighbourhood. -/
def GoodNbhd.triple (V : S.GoodNbhd Ψ o) {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    BTriple (S.hdU hT Ψ) :=
  ⟨⟨o, V.1.U, V.mem_faceStructuredNbhdsAt, V.one_le_degIndex⟩, θ,
    ⟨hθ, V.mem_of_mem_faces hθ⟩⟩

/-- **The face germ `[ō, V(ō), θ]`** of a face of `U(ō)`. -/
def GoodNbhd.germ (V : S.GoodNbhd Ψ o) {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) : S.bO hT Ψ :=
  (V.triple hT hθ).cls

@[simp] theorem GoodNbhd.bMap_germ (V : S.GoodNbhd Ψ o) {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    bMap (S.hdU hT Ψ) (V.germ hT hθ) = o := rfl

/-- **Every face germ at `ō` is the germ of a face of `U(ō)`.** -/
theorem GoodNbhd.exists_germ_eq (V : S.GoodNbhd Ψ o) (p : S.bO hT Ψ)
    (hp : bMap (S.hdU hT Ψ) p = o) : ∃ (θ : Set Ψ.1.O) (hθ : θ ∈ V.faces), V.germ hT hθ = p := by
  obtain ⟨t₀, rfl⟩ := BSpace.exists_rep (S.hdU hT Ψ) p
  have hx : t₀.x = o := hp
  have hd := S.hdU hT Ψ
  have hV'' : t₀.V ∩ V.1.U ∈ faceStructuredNbhdsAt Ψ.1.P.degIndex t₀.x :=
    inter_mem_faceStructuredNbhdsAt hd t₀.mem (hx ▸ V.mem_faceStructuredNbhdsAt)
  obtain ⟨θ'', hθ'', he''⟩ := exists_face_restrict hd t₀.mem hV''.1.1.1 hV''.2.1
    inter_subset_left t₀.mem_faces
  have hmem := faceExt_mem_facesThrough hd V.isOpen (inter_subset_right (s := t₀.V)) hθ''
  rw [hx] at hmem
  refine ⟨faceExt Ψ.1.P.degIndex V.1.U θ'', hmem.1, ?_⟩
  let r : BTriple (S.hdU hT Ψ) := ⟨⟨t₀.x, t₀.V ∩ V.1.U, hV'', t₀.one_le⟩, θ'', hθ''⟩
  have h1 : r.cls = t₀.cls := (cls_eq_iff_faceExt (S.hdU hT Ψ) (a := r) (b := t₀) rfl
    inter_subset_left).2 he''
  have h2 : r.cls = (V.triple hT hmem.1).cls := (cls_eq_iff_faceExt (S.hdU hT Ψ) (a := r)
    (b := V.triple hT hmem.1) hx inter_subset_right).2 rfl
  exact h2.symm.trans h1

/-- Distinct faces of `U(ō)` have distinct germs. -/
theorem GoodNbhd.germ_injective (V : S.GoodNbhd Ψ o) {θ θ' : Set Ψ.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V.faces) (h : V.germ hT hθ = V.germ hT hθ') : θ = θ' := by
  have := (cls_eq_iff_faceExt (S.hdU hT Ψ) (a := V.triple hT hθ) (b := V.triple hT hθ') rfl
    subset_rfl).1 h
  change faceExt Ψ.1.P.degIndex V.1.U θ = θ' at this
  rwa [faceExt_self (S.hdU hT Ψ) V.isOpen hθ] at this

end FaceGerm

/-! ### (17.56)–(17.58) and Definition 17.4.2: the objects of `bC` -/

section Objects

variable (S) in
/-- **The tuples `(α, Ψ, U(ō), θ)` of 2021 (17.57)**: `Ψ ∈ F(α)`, `ō ∈ O` with `Ψ(ō) = α`, a good
open neighbourhood `U(ō)` and a face `θ ∈ F_{U(ō)}`. -/
structure BdryTuple where
  /-- The object `α`. -/
  α : C.Obj
  /-- The uniformizer `Ψ ∈ F(α)`. -/
  Ψ : C.LocalUniformizer
  mem : Ψ ∈ S.F α
  /-- The point `ō` mapped to `α`. -/
  o : Ψ.O
  obj_o : Ψ.obj o = α
  /-- The good open neighbourhood `U(ō)`. -/
  V : S.GoodNbhd ⟨Ψ, α, mem⟩ o
  /-- The face `θ ∈ F_{U(ō)}`. -/
  θ : Set Ψ.O
  face : θ ∈ V.faces

namespace BdryTuple

/-- `Ψ` as a uniformizer of `S`. -/
abbrev unif (t : S.BdryTuple) : S.Unif := ⟨t.Ψ, t.α, t.mem⟩

/-- The face germ `[ō, V(ō), θ]` of the tuple. -/
abbrev germ (t : S.BdryTuple) (hT : S.IsTame) : S.bO hT t.unif := t.V.germ hT t.face

/-- **`h = (ō, 1_α, ō') ∈ M(Ψ, Ψ')`** of (17.58). -/
def idTr (t t' : S.BdryTuple) (h : t.α = t'.α) : S.Tr t.unif t'.unif :=
  ⟨t.o, C.toGroupoidStr.unit t.α, t'.o, (C.toGroupoidStr.src_unit _).trans t.obj_o.symm,
    (C.toGroupoidStr.tgt_unit _).trans (h.trans t'.obj_o.symm)⟩

/-- **2021 (17.56), (17.58)**: `(α, Ψ, U(ō), θ) ∼ (α', Ψ', U'(ō'), θ')` iff `α = α'` and the local
sc-diffeomorphism `f` of `h = (ō, 1_α, ō')` carries `θ` near `ō` to `θ'` near `ō'`. -/
def Equiv (t : S.BdryTuple) (hT : S.IsTame) (t' : S.BdryTuple) : Prop :=
  ∃ h : t.α = t'.α, S.GermLift hT (t.idTr t' h) (t.germ hT) (t'.germ hT)

variable {t t' t'' : S.BdryTuple} {hT : S.IsTame}

theorem idTr_self : t.idTr t rfl = S.toTr (GroupoidStr.TransitionSet.unit t.o) := by
  refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
  change C.toGroupoidStr.unit t.α = C.toGroupoidStr.unit (t.Ψ.obj t.o)
  rw [t.obj_o]

theorem equiv_refl : t.Equiv hT t := ⟨rfl, by rw [idTr_self]; exact germLift_unit rfl⟩

theorem equiv_symm (h : t.Equiv hT t') : t'.Equiv hT t := by
  obtain ⟨hα, hl⟩ := h
  refine ⟨hα.symm, ?_⟩
  have he : (S.toTr (GroupoidStr.TransitionSet.inv (t.idTr t' hα)) : S.Tr t'.unif t.unif) =
      t'.idTr t hα.symm := by
    refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
    change C.toGroupoidStr.inv (C.toGroupoidStr.unit t.α) = C.toGroupoidStr.unit t'.α
    rw [GroupoidStr.inv_unit, hα]
  rw [← he]
  exact germLift_inv hl

theorem equiv_trans (h₁ : t.Equiv hT t') (h₂ : t'.Equiv hT t'') : t.Equiv hT t'' := by
  obtain ⟨hα, hl⟩ := h₁
  obtain ⟨hα', hl'⟩ := h₂
  have hab : C.toGroupoidStr.src (t'.idTr t'' hα').mor = C.toGroupoidStr.tgt (t.idTr t' hα).mor := by
    change C.toGroupoidStr.src (C.toGroupoidStr.unit t'.α) =
      C.toGroupoidStr.tgt (C.toGroupoidStr.unit t.α)
    rw [GroupoidStr.src_unit, GroupoidStr.tgt_unit, hα]
  refine ⟨hα.trans hα', ?_⟩
  have he : (S.toTr (GroupoidStr.TransitionSet.comp (t'.idTr t'' hα') (t.idTr t' hα) hab) :
      S.Tr t.unif t''.unif) = t.idTr t'' (hα.trans hα') := by
    refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
    change C.toGroupoidStr.comp (C.toGroupoidStr.unit t'.α) (C.toGroupoidStr.unit t.α) =
      C.toGroupoidStr.unit t.α
    exact GroupoidStr.unit_comp_of_eq ((C.toGroupoidStr.tgt_unit _).trans hα)
  rw [← he]
  exact germLift_comp hab rfl hl hl'

end BdryTuple

variable (S) in
/-- The equivalence relation (17.58) on the tuples (17.57). -/
def bdryTupleSetoid (hT : S.IsTame) : Setoid S.BdryTuple where
  r t t' := t.Equiv hT t'
  iseqv := ⟨fun _ => BdryTuple.equiv_refl, BdryTuple.equiv_symm, BdryTuple.equiv_trans⟩

variable (S) in
/-- **2021 Definition 17.4.2, p. 789**: the objects `[α, Ψ, U(ō), θ]` of `bC`, the classes of the
tuples (17.57) under (17.58). -/
def BookObj (hT : S.IsTame) : Type (u + 1) := Quotient (S.bdryTupleSetoid hT)

/-- **The forgetful map (17.59)** `[α, Ψ, U(ō), θ] ↦ α`. -/
def BookObj.base {hT : S.IsTame} : S.BookObj hT → C.Obj :=
  Quotient.lift (fun t : S.BdryTuple => t.α) fun _ _ h => h.1

/-! #### The reference uniformizers -/

variable (S) in
/-- A reference uniformizer `bdryRefUnif α ∈ F(α)` (needs `F(α) ≠ ∅`). -/
def bdryRefUnif (hS : S.HasUniformizers) (α : C.Obj) : S.Unif := ⟨Set.Nonempty.some (hS α), α, (Set.Nonempty.some_mem (hS α))⟩

theorem bdryRefUnif_mem (hS : S.HasUniformizers) (α : C.Obj) : (S.bdryRefUnif hS α).1 ∈ S.F α :=
  (Set.Nonempty.some_mem (hS α))

variable (S) in
/-- The point `ō ∈ O` of `bdryRefUnif α` mapped to `α`. -/
def refPt (hS : S.HasUniformizers) (α : C.Obj) : (S.bdryRefUnif hS α).1.O :=
  (S.isAt α _ (Set.Nonempty.some_mem (hS α))).choose

@[simp] theorem obj_refPt (hS : S.HasUniformizers) (α : C.Obj) :
    (S.bdryRefUnif hS α).1.obj (S.refPt hS α) = α :=
  (S.isAt α _ (Set.Nonempty.some_mem (hS α))).choose_spec

variable (S) in
/-- **The objects of `bC`** in the model through the reference uniformizers: an object `α` and a
face germ at `refPt α ∈ ∂O` (equivalent to Definition 17.4.2, `bookObjEquiv`). -/
@[ext] structure BObj (hT : S.IsTame) (hS : S.HasUniformizers) where
  /-- The underlying object `α`. -/
  α : C.Obj
  /-- The face germ at `ō = refPt α`. -/
  p : S.bO hT (S.bdryRefUnif hS α)
  bMap_p : bMap (S.hdU hT _) p = S.refPt hS α

variable {hT : S.IsTame} {hS : S.HasUniformizers}

variable (hS) in
/-- `(ō, 1_α, ō_ref) ∈ M(Ψ, bdryRefUnif α)` for a tuple. -/
def BdryTuple.toRefTr (t : S.BdryTuple) : S.Tr t.unif (S.bdryRefUnif hS t.α) :=
  ⟨t.o, C.toGroupoidStr.unit t.α, S.refPt hS t.α, (C.toGroupoidStr.src_unit _).trans t.obj_o.symm,
    (C.toGroupoidStr.tgt_unit _).trans (obj_refPt hS t.α).symm⟩

variable (hT hS) in
/-- **A tuple as an object of the model**: its face germ carried to `bdryRefUnif α` by
`(ō, 1_α, ō_ref)`. -/
def BdryTuple.toBObj (t : S.BdryTuple) : S.BObj hT hS :=
  ⟨t.α, germPush (t.toRefTr hS) (t.germ hT) rfl,
    (germLift_germPush (t.toRefTr hS) (t.germ hT) rfl).bMap_tgt⟩

theorem BdryTuple.germLift_toBObj (t : S.BdryTuple) :
    S.GermLift hT (t.toRefTr hS) (t.germ hT) (t.toBObj hT hS).p :=
  germLift_germPush _ _ rfl

/-- **The tuples equivalent under (17.58) are those with the same object of the model.** -/
theorem BdryTuple.toBObj_eq_iff {t t' : S.BdryTuple} :
    t.toBObj hT hS = t'.toBObj hT hS ↔ t.Equiv hT t' := by
  obtain ⟨α, Ψ, mem, o, obj_o, V, θ, face⟩ := t
  obtain ⟨α', Ψ', mem', o', obj_o', V', θ', face'⟩ := t'
  constructor
  · intro h
    have hα : α = α' := congrArg BObj.α h
    subst hα
    have hp := eq_of_heq (BObj.ext_iff.1 h).2
    refine ⟨rfl, ?_⟩
    set t : S.BdryTuple := ⟨α, Ψ, mem, o, obj_o, V, θ, face⟩
    set t' : S.BdryTuple := ⟨α, Ψ', mem', o', obj_o', V', θ', face'⟩
    have h1 := t.germLift_toBObj (hT := hT) (hS := hS)
    have h2 := germLift_inv (t'.germLift_toBObj (hT := hT) (hS := hS))
    change S.GermLift hT (t.toRefTr hS) (t.germ hT) (t.toBObj hT hS).p at h1
    rw [show (t.toBObj hT hS).p = (t'.toBObj hT hS).p from hp] at h1
    have hab : C.toGroupoidStr.src (S.toTr (GroupoidStr.TransitionSet.inv (t'.toRefTr hS)) :
        S.Tr (S.bdryRefUnif hS α) t'.unif).mor = C.toGroupoidStr.tgt (t.toRefTr hS).mor := by
      change C.toGroupoidStr.src (C.toGroupoidStr.inv (C.toGroupoidStr.unit α)) =
        C.toGroupoidStr.tgt (C.toGroupoidStr.unit α)
      simp
    have h3 := germLift_comp hab rfl h1 h2
    have he : (S.toTr (GroupoidStr.TransitionSet.comp
        (S.toTr (GroupoidStr.TransitionSet.inv (t'.toRefTr hS)) : S.Tr (S.bdryRefUnif hS α) t'.unif)
        (t.toRefTr hS) hab) : S.Tr t.unif t'.unif) = t.idTr t' rfl := by
      refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
      change C.toGroupoidStr.comp (C.toGroupoidStr.inv (C.toGroupoidStr.unit α))
        (C.toGroupoidStr.unit α) = C.toGroupoidStr.unit α
      rw [GroupoidStr.inv_unit]
      exact GroupoidStr.unit_comp_of_eq (C.toGroupoidStr.tgt_unit _)
    rw [he] at h3
    exact h3
  · rintro ⟨hα, hl⟩
    change α = α' at hα
    subst hα
    set t : S.BdryTuple := ⟨α, Ψ, mem, o, obj_o, V, θ, face⟩
    set t' : S.BdryTuple := ⟨α, Ψ', mem', o', obj_o', V', θ', face'⟩
    have hab : C.toGroupoidStr.src (t'.toRefTr hS).mor =
        C.toGroupoidStr.tgt (t.idTr t' rfl).mor := by
      change C.toGroupoidStr.src (C.toGroupoidStr.unit α) =
        C.toGroupoidStr.tgt (C.toGroupoidStr.unit α)
      simp
    have h3 := germLift_comp hab rfl hl (t'.germLift_toBObj (hT := hT) (hS := hS))
    have he : (S.toTr (GroupoidStr.TransitionSet.comp (t'.toRefTr hS) (t.idTr t' rfl) hab) :
        S.Tr t.unif (S.bdryRefUnif hS α)) = t.toRefTr hS := by
      refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
      change C.toGroupoidStr.comp (C.toGroupoidStr.unit α) (C.toGroupoidStr.unit α) =
        C.toGroupoidStr.unit α
      exact GroupoidStr.unit_comp_of_eq (C.toGroupoidStr.tgt_unit _)
    rw [he] at h3
    refine BObj.ext rfl (heq_of_eq ?_)
    exact germLift_unique (t.germLift_toBObj (hT := hT) (hS := hS)) h3

/-- **Every object of the model comes from a tuple** (good open neighbourhoods exist at the
reference point, Proposition 14.1.1). -/
theorem BdryTuple.toBObj_surjective : Surjective (BdryTuple.toBObj (S := S) hT hS) := by
  rintro ⟨α, p, hp⟩
  have hΨ := S.isTame_unif hT (S.bdryRefUnif hS α)
  have hb : S.refPt hS α ∈ (S.bdryRefUnif hS α).1.P.boundary := by
    obtain ⟨t₀, rfl⟩ := BSpace.exists_rep (S.hdU hT (S.bdryRefUnif hS α)) p
    have h1 := t₀.one_le
    have hx : t₀.x = S.refPt hS α := hp
    rw [hx] at h1
    exact h1
  obtain ⟨V, -⟩ := exists_goodNbhd hΨ hb isOpen_univ (mem_univ _)
  obtain ⟨θ, hθ, hgerm⟩ := V.exists_germ_eq hT p hp
  let t : S.BdryTuple := ⟨α, (S.bdryRefUnif hS α).1, bdryRefUnif_mem hS α, S.refPt hS α,
    obj_refPt hS α, V, θ, hθ⟩
  refine ⟨t, ?_⟩
  have he : t.toRefTr hS = S.toTr (GroupoidStr.TransitionSet.unit (S.refPt hS α)) := by
    refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
    change C.toGroupoidStr.unit α =
      C.toGroupoidStr.unit ((S.bdryRefUnif hS α).1.obj (S.refPt hS α))
    rw [obj_refPt]
  have h1 := t.germLift_toBObj (hT := hT) (hS := hS)
  rw [he] at h1
  have h2 := germLift_unique h1 (germLift_unit (hT := hT) (p := t.germ hT) rfl)
  refine BObj.ext rfl (heq_of_eq ?_)
  exact h2.trans hgerm

variable (hT hS) in
/-- **2021 Definition 17.4.2**: the classes `[α, Ψ, U(ō), θ]` are the objects of the model
`BObj` (through any choice of reference uniformizers). -/
def bookObjEquiv : S.BookObj hT ≃ S.BObj hT hS :=
  Equiv.ofBijective (Quotient.lift (BdryTuple.toBObj hT hS) fun _ _ h =>
      BdryTuple.toBObj_eq_iff.2 h)
    ⟨fun a b h => by
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      exact Quotient.sound (BdryTuple.toBObj_eq_iff.1 h),
     fun b => by
      obtain ⟨t, rfl⟩ := BdryTuple.toBObj_surjective (hT := hT) b
      exact ⟨Quotient.mk _ t, rfl⟩⟩

theorem bookObjEquiv_mk (t : S.BdryTuple) :
    S.bookObjEquiv hT hS (Quotient.mk _ t) = t.toBObj hT hS := rfl

/-- **2021 Definition 17.4.2**, with (17.59): the classes of the tuples form the type `BookObj`,
two tuples have the same class iff (17.58), the class map to the model is a bijection preserving
the forgetful map `[α, Ψ, U(ō), θ] ↦ α`. -/
theorem definition_17_4_2 :
    (∀ t t' : S.BdryTuple, (Quotient.mk (S.bdryTupleSetoid hT) t =
      Quotient.mk (S.bdryTupleSetoid hT) t') ↔ t.Equiv hT t') ∧
    Bijective (S.bookObjEquiv hT hS) ∧
    ∀ a : S.BookObj hT, (S.bookObjEquiv hT hS a).α = a.base := by
  refine ⟨fun t t' => Quotient.eq, (S.bookObjEquiv hT hS).bijective, fun a => ?_⟩
  induction a using Quotient.inductionOn
  rfl

end Objects

/-! ### Definitions 17.4.3, 17.4.4: the morphisms of `bC` and the forgetful functor -/

section Morphisms

variable {hT : S.IsTame} {hS : S.HasUniformizers}

variable (hS) in
/-- `h = (ō, φ, ō') ∈ M(bdryRefUnif α, bdryRefUnif α')` for `φ : α → α'` (Definition 17.4.3 (1)). -/
def bdryRefTr {α α' : C.Obj} (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') : S.Tr (S.bdryRefUnif hS α) (S.bdryRefUnif hS α') :=
  ⟨S.refPt hS α, φ, S.refPt hS α', hs.trans (obj_refPt hS α).symm,
    ht.trans (obj_refPt hS α').symm⟩

/-- **2021 Definition 17.4.3 (2)**, in the reference uniformizers: `φ : α → α'` and the local
sc-diffeomorphism `f` of `h = (ō, φ, ō')` carries the face germ of `ᾱ` to that of `ᾱ'`
(`θ' = f_*θ`). -/
def BLift (a : S.BObj hT hS) (φ : C.Mor) (b : S.BObj hT hS) : Prop :=
  ∃ (hs : C.toGroupoidStr.src φ = a.α) (ht : C.toGroupoidStr.tgt φ = b.α),
    S.GermLift hT (S.bdryRefTr hS φ hs ht) a.p b.p

namespace BLift

variable {a b c : S.BObj hT hS} {φ ψ : C.Mor}

theorem src_eq (h : S.BLift a φ b) : C.toGroupoidStr.src φ = a.α := h.1

theorem tgt_eq (h : S.BLift a φ b) : C.toGroupoidStr.tgt φ = b.α := h.2.1

/-- The identity of `α` lifts to `ᾱ → ᾱ`. -/
theorem unit (a : S.BObj hT hS) : S.BLift a (C.toGroupoidStr.unit a.α) a := by
  refine ⟨C.toGroupoidStr.src_unit _, C.toGroupoidStr.tgt_unit _, ?_⟩
  have he : S.bdryRefTr hS (C.toGroupoidStr.unit a.α) (C.toGroupoidStr.src_unit _)
      (C.toGroupoidStr.tgt_unit _) = S.toTr (GroupoidStr.TransitionSet.unit (S.refPt hS a.α)) := by
    refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
    change C.toGroupoidStr.unit a.α =
      C.toGroupoidStr.unit ((S.bdryRefUnif hS a.α).1.obj (S.refPt hS a.α))
    rw [obj_refPt]
  rw [he]
  exact germLift_unit a.bMap_p

theorem inv (h : S.BLift a φ b) : S.BLift b (C.toGroupoidStr.inv φ) a := by
  obtain ⟨hs, ht, hl⟩ := h
  refine ⟨(C.toGroupoidStr.src_inv φ).trans ht, (C.toGroupoidStr.tgt_inv φ).trans hs, ?_⟩
  have he : (S.toTr (GroupoidStr.TransitionSet.inv (S.bdryRefTr hS φ hs ht)) :
      S.Tr (S.bdryRefUnif hS b.α) (S.bdryRefUnif hS a.α)) =
      S.bdryRefTr hS (C.toGroupoidStr.inv φ) ((C.toGroupoidStr.src_inv φ).trans ht)
        ((C.toGroupoidStr.tgt_inv φ).trans hs) :=
    GroupoidStr.TransitionSet.ext rfl rfl rfl
  rw [← he]
  exact germLift_inv hl

theorem comp (hψ : S.BLift a ψ b) (hφ : S.BLift b φ c) :
    S.BLift a (C.toGroupoidStr.comp φ ψ) c := by
  obtain ⟨hs, ht, hl⟩ := hψ
  obtain ⟨hs', ht', hl'⟩ := hφ
  have hab : C.toGroupoidStr.src φ = C.toGroupoidStr.tgt ψ := hs'.trans ht.symm
  refine ⟨(C.toGroupoidStr.src_comp _ _ hab).trans hs, (C.toGroupoidStr.tgt_comp _ _ hab).trans ht',
    ?_⟩
  have he : (S.toTr (GroupoidStr.TransitionSet.comp (S.bdryRefTr hS φ hs' ht') (S.bdryRefTr hS ψ hs ht)
      hab) : S.Tr (S.bdryRefUnif hS a.α) (S.bdryRefUnif hS c.α)) =
      S.bdryRefTr hS (C.toGroupoidStr.comp φ ψ) ((C.toGroupoidStr.src_comp _ _ hab).trans hs)
        ((C.toGroupoidStr.tgt_comp _ _ hab).trans ht') :=
    GroupoidStr.TransitionSet.ext rfl rfl rfl
  rw [← he]
  exact germLift_comp hab rfl hl hl'

/-- **`ᾱ'` is determined by `ᾱ` and `φ`** (2021 p. 790). -/
theorem unique {b' : S.BObj hT hS} (h : S.BLift a φ b) (h' : S.BLift a φ b') : b = b' := by
  obtain ⟨β, p, hp⟩ := b
  obtain ⟨β', p', hp'⟩ := b'
  obtain ⟨hs, ht, hl⟩ := h
  obtain ⟨hs', ht', hl'⟩ := h'
  change C.toGroupoidStr.tgt φ = β at ht
  change C.toGroupoidStr.tgt φ = β' at ht'
  subst ht ht'
  exact BObj.ext rfl (heq_of_eq (germLift_unique hl hl'))

/-- **Existence of `φ_*ᾱ`** (2021 p. 790). -/
theorem exists_of_src_eq (a : S.BObj hT hS) (hs : C.toGroupoidStr.src φ = a.α) :
    ∃ b, S.BLift a φ b := by
  let h := S.bdryRefTr hS φ hs rfl
  exact ⟨⟨C.toGroupoidStr.tgt φ, germPush h a.p a.bMap_p,
    (germLift_germPush h a.p a.bMap_p).bMap_tgt⟩, hs, rfl, germLift_germPush h a.p a.bMap_p⟩

end BLift

/-- **2021 p. 790**: given `ᾱ` and `φ : α → α'` there is a unique `ᾱ' = φ_*ᾱ` over `α'` with a
morphism `Φ = (ᾱ, φ, ᾱ')`. -/
theorem existsUnique_bLift (a : S.BObj hT hS) {φ : C.Mor} (hs : C.toGroupoidStr.src φ = a.α) :
    ∃! b, S.BLift a φ b :=
  let ⟨b, hb⟩ := BLift.exists_of_src_eq a hs
  ⟨b, hb, fun _ h => h.unique hb⟩

/-- **Independence of the representatives** in Definition 17.4.3 (2): for tuples `t`, `t'`
representing `ᾱ`, `ᾱ'` and `φ : α → α'`, `φ` lifts to `ᾱ → ᾱ'` iff `h = (ō, φ, ō') ∈ M(Ψ, Ψ')`
carries the face germ of `t` to that of `t'`. -/
theorem bLift_iff_tuple (t t' : S.BdryTuple) {φ : C.Mor} (hs : C.toGroupoidStr.src φ = t.α)
    (ht : C.toGroupoidStr.tgt φ = t'.α) :
    S.BLift (t.toBObj hT hS) φ (t'.toBObj hT hS) ↔
      S.GermLift hT (⟨t.o, φ, t'.o, hs.trans t.obj_o.symm, ht.trans t'.obj_o.symm⟩ :
        S.Tr t.unif t'.unif) (t.germ hT) (t'.germ hT) := by
  set h : S.Tr t.unif t'.unif := ⟨t.o, φ, t'.o, hs.trans t.obj_o.symm, ht.trans t'.obj_o.symm⟩
  have h1 := t.germLift_toBObj (hT := hT) (hS := hS)
  have h2 := t'.germLift_toBObj (hT := hT) (hS := hS)
  constructor
  · rintro ⟨hs', ht', hl⟩
    -- `(t'.toRefTr)⁻¹ ∘ bdryRefTr φ ∘ t.toRefTr = h`
    have hab₁ : C.toGroupoidStr.src (S.bdryRefTr hS φ hs' ht').mor =
        C.toGroupoidStr.tgt (t.toRefTr hS).mor := by
      change C.toGroupoidStr.src φ = C.toGroupoidStr.tgt (C.toGroupoidStr.unit t.α)
      rw [GroupoidStr.tgt_unit]; exact hs
    have k₁ := germLift_comp hab₁ rfl h1 hl
    have hab₂ : C.toGroupoidStr.src (S.toTr (GroupoidStr.TransitionSet.inv (t'.toRefTr hS)) :
        S.Tr (S.bdryRefUnif hS t'.α) t'.unif).mor = C.toGroupoidStr.tgt (S.toTr
          (GroupoidStr.TransitionSet.comp (S.bdryRefTr hS φ hs' ht') (t.toRefTr hS) hab₁) :
            S.Tr t.unif (S.bdryRefUnif hS t'.α)).mor := by
      change C.toGroupoidStr.src (C.toGroupoidStr.inv (C.toGroupoidStr.unit t'.α)) =
        C.toGroupoidStr.tgt (C.toGroupoidStr.comp φ (C.toGroupoidStr.unit t.α))
      rw [GroupoidStr.src_inv, GroupoidStr.tgt_unit, C.toGroupoidStr.tgt_comp _ _ (by
        rw [GroupoidStr.tgt_unit]; exact hs), ht]
    have k₂ := germLift_comp hab₂ rfl k₁ (germLift_inv h2)
    have he : (S.toTr (GroupoidStr.TransitionSet.comp
        (S.toTr (GroupoidStr.TransitionSet.inv (t'.toRefTr hS)) :
          S.Tr (S.bdryRefUnif hS t'.α) t'.unif)
        (S.toTr (GroupoidStr.TransitionSet.comp (S.bdryRefTr hS φ hs' ht') (t.toRefTr hS) hab₁) :
          S.Tr t.unif (S.bdryRefUnif hS t'.α)) hab₂) : S.Tr t.unif t'.unif) = h := by
      refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
      change C.toGroupoidStr.comp (C.toGroupoidStr.inv (C.toGroupoidStr.unit t'.α))
        (C.toGroupoidStr.comp φ (C.toGroupoidStr.unit t.α)) = φ
      rw [GroupoidStr.inv_unit, GroupoidStr.comp_unit_of_eq hs,
        GroupoidStr.unit_comp_of_eq ht]
    rw [he] at k₂
    exact k₂
  · intro hl
    refine ⟨hs, ht, ?_⟩
    have hab₁ : C.toGroupoidStr.src h.mor = C.toGroupoidStr.tgt
        (S.toTr (GroupoidStr.TransitionSet.inv (t.toRefTr hS)) :
          S.Tr (S.bdryRefUnif hS t.α) t.unif).mor := by
      change C.toGroupoidStr.src φ = C.toGroupoidStr.tgt (C.toGroupoidStr.inv
        (C.toGroupoidStr.unit t.α))
      rw [GroupoidStr.tgt_inv, GroupoidStr.src_unit]; exact hs
    have k₁ := germLift_comp hab₁ rfl (germLift_inv h1) hl
    have hab₂ : C.toGroupoidStr.src (t'.toRefTr hS).mor = C.toGroupoidStr.tgt (S.toTr
        (GroupoidStr.TransitionSet.comp h (S.toTr (GroupoidStr.TransitionSet.inv
          (t.toRefTr hS)) : S.Tr (S.bdryRefUnif hS t.α) t.unif) hab₁) :
            S.Tr (S.bdryRefUnif hS t.α) t'.unif).mor := by
      change C.toGroupoidStr.src (C.toGroupoidStr.unit t'.α) = C.toGroupoidStr.tgt
        (C.toGroupoidStr.comp φ (C.toGroupoidStr.inv (C.toGroupoidStr.unit t.α)))
      rw [GroupoidStr.src_unit, C.toGroupoidStr.tgt_comp _ _ (by
        rw [GroupoidStr.tgt_inv, GroupoidStr.src_unit]; exact hs), ht]
    have k₂ := germLift_comp hab₂ rfl k₁ h2
    have he : (S.toTr (GroupoidStr.TransitionSet.comp (t'.toRefTr hS) (S.toTr
        (GroupoidStr.TransitionSet.comp h (S.toTr (GroupoidStr.TransitionSet.inv
          (t.toRefTr hS)) : S.Tr (S.bdryRefUnif hS t.α) t.unif) hab₁) :
            S.Tr (S.bdryRefUnif hS t.α) t'.unif) hab₂) :
              S.Tr (S.bdryRefUnif hS t.α) (S.bdryRefUnif hS t'.α)) = S.bdryRefTr hS φ hs ht := by
      refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
      change C.toGroupoidStr.comp (C.toGroupoidStr.unit t'.α)
        (C.toGroupoidStr.comp φ (C.toGroupoidStr.inv (C.toGroupoidStr.unit t.α))) = φ
      rw [GroupoidStr.inv_unit, GroupoidStr.comp_unit_of_eq hs,
        GroupoidStr.unit_comp_of_eq ht]
    rw [he] at k₂
    exact k₂

/-- **2021 Definition 17.4.3, p. 789**: for representatives `t`, `t'` of `ᾱ`, `ᾱ'` and
`φ : α → α'`, `(ᾱ, φ, ᾱ')` is a morphism of `bC` iff the local sc-diffeomorphism of
`h = (ō, φ, ō')` carries `θ` near `ō` to `θ'` near `ō'` (independently of the representatives), and
`ᾱ' = φ_*ᾱ` is the unique object with this property. -/
theorem definition_17_4_3 (t t' : S.BdryTuple) {φ : C.Mor} (hs : C.toGroupoidStr.src φ = t.α)
    (ht : C.toGroupoidStr.tgt φ = t'.α) :
    (S.BLift (t.toBObj hT hS) φ (t'.toBObj hT hS) ↔
      S.GermLift hT (⟨t.o, φ, t'.o, hs.trans t.obj_o.symm, ht.trans t'.obj_o.symm⟩ :
        S.Tr t.unif t'.unif) (t.germ hT) (t'.germ hT)) ∧
    ∃! b : S.BObj hT hS, S.BLift (t.toBObj hT hS) φ b :=
  ⟨bLift_iff_tuple t t' hs ht, existsUnique_bLift _ hs⟩

variable (S hT hS) in
/-- **2021 Definition 17.4.3, p. 789**: a morphism `Φ = (ᾱ, φ, ᾱ') : ᾱ → ᾱ'` of `bC`, a morphism
`φ : α → α'` of `C` carrying the face of `ᾱ` near `ō` to that of `ᾱ'` near `ō'`. -/
@[ext] structure BMor where
  /-- The source object `ᾱ`. -/
  src : S.BObj hT hS
  /-- The morphism `φ : α → α'` of `C`. -/
  mor : C.Mor
  /-- The target object `ᾱ'`. -/
  tgt : S.BObj hT hS
  lifts : S.BLift src mor tgt

namespace BMor

variable (Φ : S.BMor hT hS)

theorem src_mor : C.toGroupoidStr.src Φ.mor = Φ.src.α := Φ.lifts.src_eq

theorem tgt_mor : C.toGroupoidStr.tgt Φ.mor = Φ.tgt.α := Φ.lifts.tgt_eq

end BMor

/-- The composite `(ᾱ', φ', ᾱ'') ∘ (ᾱ, φ, ᾱ') = (ᾱ, φ' ∘ φ, ᾱ'')` of composable morphisms. -/
def BMor.compOf (Φ Ψ : S.BMor hT hS) (h : Φ.src = Ψ.tgt) : S.BMor hT hS :=
  ⟨Ψ.src, C.toGroupoidStr.comp Φ.mor Ψ.mor, Φ.tgt, BLift.comp (by rw [h]; exact Ψ.lifts)
    Φ.lifts⟩

open scoped Classical in
/-- The composition of `bC`, extended by `Φ` off the composable pairs. -/
def BMor.comp (Φ Ψ : S.BMor hT hS) : S.BMor hT hS :=
  if h : Φ.src = Ψ.tgt then Φ.compOf Ψ h else Φ

theorem BMor.comp_of_eq {Φ Ψ : S.BMor hT hS} (h : Φ.src = Ψ.tgt) :
    Φ.comp Ψ = Φ.compOf Ψ h := dif_pos h

variable (S hT hS) in
/-- **The tame boundary category `bC`** (2021 Definitions 17.4.2–17.4.4) as a groupoid: the
composition `(ᾱ', φ', ᾱ'') ∘ (ᾱ, φ, ᾱ') = (ᾱ, φ' ∘ φ, ᾱ'')` (Lemma: `BLift.comp`), units
`(ᾱ, 1_α, ᾱ)`, inverses `(ᾱ', φ⁻¹, ᾱ)`. -/
def bdryGroupoid : GroupoidStr (S.BObj hT hS) (S.BMor hT hS) where
  src := BMor.src
  tgt := BMor.tgt
  comp := BMor.comp
  unit a := ⟨a, C.toGroupoidStr.unit a.α, a, BLift.unit a⟩
  inv Φ := ⟨Φ.tgt, C.toGroupoidStr.inv Φ.mor, Φ.src, Φ.lifts.inv⟩
  src_comp Φ Ψ h := by rw [BMor.comp_of_eq h]; rfl
  tgt_comp Φ Ψ h := by rw [BMor.comp_of_eq h]; rfl
  comp_assoc Φ Ψ Χ h₁ h₂ := by
    rw [BMor.comp_of_eq h₁, BMor.comp_of_eq h₂, BMor.comp_of_eq (Φ := Φ.compOf Ψ h₁) (Ψ := Χ) h₂,
      BMor.comp_of_eq (Φ := Φ) (Ψ := Ψ.compOf Χ h₂) h₁]
    refine BMor.ext rfl ?_ rfl
    exact C.toGroupoidStr.comp_assoc _ _ _ (by rw [Φ.src_mor, Ψ.tgt_mor, h₁])
      (by rw [Ψ.src_mor, Χ.tgt_mor, h₂])
  src_unit _ := rfl
  tgt_unit _ := rfl
  comp_unit Φ := by
    rw [BMor.comp_of_eq rfl]
    exact BMor.ext rfl (GroupoidStr.comp_unit_of_eq Φ.src_mor) rfl
  unit_comp Φ := by
    rw [BMor.comp_of_eq rfl]
    exact BMor.ext rfl (GroupoidStr.unit_comp_of_eq Φ.tgt_mor) rfl
  src_inv _ := rfl
  tgt_inv _ := rfl
  comp_inv Φ := by
    rw [BMor.comp_of_eq rfl]
    refine BMor.ext rfl ?_ rfl
    change C.toGroupoidStr.comp Φ.mor (C.toGroupoidStr.inv Φ.mor) =
      C.toGroupoidStr.unit Φ.tgt.α
    rw [C.toGroupoidStr.comp_inv, Φ.tgt_mor]
  inv_comp Φ := by
    rw [BMor.comp_of_eq rfl]
    refine BMor.ext rfl ?_ rfl
    change C.toGroupoidStr.comp (C.toGroupoidStr.inv Φ.mor) Φ.mor =
      C.toGroupoidStr.unit Φ.src.α
    rw [C.toGroupoidStr.inv_comp, Φ.src_mor]

@[simp] theorem bdryGroupoid_src (Φ : S.BMor hT hS) : (S.bdryGroupoid hT hS).src Φ = Φ.src := rfl

@[simp] theorem bdryGroupoid_tgt (Φ : S.BMor hT hS) : (S.bdryGroupoid hT hS).tgt Φ = Φ.tgt := rfl

@[simp] theorem bdryGroupoid_unit (a : S.BObj hT hS) :
    ((S.bdryGroupoid hT hS).unit a).mor = C.toGroupoidStr.unit a.α := rfl

@[simp] theorem bdryGroupoid_inv (Φ : S.BMor hT hS) :
    ((S.bdryGroupoid hT hS).inv Φ).mor = C.toGroupoidStr.inv Φ.mor := rfl

theorem bdryGroupoid_comp_mor {Φ Ψ : S.BMor hT hS} (h : Φ.src = Ψ.tgt) :
    ((S.bdryGroupoid hT hS).comp Φ Ψ).mor = C.toGroupoidStr.comp Φ.mor Ψ.mor := by
  change (Φ.comp Ψ).mor = _
  rw [BMor.comp_of_eq h]; rfl

/-- A morphism is determined by its source and its morphism of `C`. -/
theorem BMor.ext_of_src {Φ Ψ : S.BMor hT hS} (hs : Φ.src = Ψ.src) (hm : Φ.mor = Ψ.mor) :
    Φ = Ψ := by
  refine BMor.ext hs hm ?_
  have h := Ψ.lifts
  rw [← hs, ← hm] at h
  exact Φ.lifts.unique h

variable (S hT hS) in
/-- **`bC` is a groupoidal category** (hom-sets inject into those of `C`). -/
def bdryCategory : GroupoidalCategory.{u} where
  Obj := S.BObj hT hS
  Mor := S.BMor hT hS
  toGroupoidStr := S.bdryGroupoid hT hS
  finite_mor a b := by
    refine Set.Finite.of_finite_image (f := BMor.mor) ?_ ?_
    · refine (C.finite_mor a.α b.α).subset ?_
      rintro _ ⟨Φ, ⟨hs, ht⟩, rfl⟩
      exact ⟨by rw [Φ.src_mor, ← hs]; rfl, by rw [Φ.tgt_mor, ← ht]; rfl⟩
    · rintro Φ ⟨hs, -⟩ Ψ ⟨hs', -⟩ hm
      exact BMor.ext_of_src (hs.trans hs'.symm) hm

/-- Objects of `bC` lie over `∂C`. -/
theorem BObj.mem_boundarySet (a : S.BObj hT hS) : a.α ∈ S.boundarySet := by
  change 1 ≤ S.degIndex a.α
  rw [definition_17_1_30 (bdryRefUnif_mem hS a.α) (obj_refPt hS a.α)]
  obtain ⟨t₀, ht₀⟩ := BSpace.exists_rep (S.hdU hT (S.bdryRefUnif hS a.α)) a.p
  have h1 := t₀.one_le
  have hx : t₀.x = S.refPt hS a.α := by rw [← a.bMap_p, ← ht₀]; rfl
  rw [hx] at h1
  exact h1

variable (S hT hS) in
/-- **The forgetful functor `B_C : bC → ∂C`** (2021 (17.63)): `ᾱ ↦ α`, `Φ ↦ φ`. -/
def bdryFunctor : GroupoidFunctor (S.bdryGroupoid hT hS) S.boundary where
  obj a := ⟨a.α, a.mem_boundarySet⟩
  mor Φ := ⟨Φ.mor, by rw [Φ.src_mor]; exact Φ.src.mem_boundarySet,
    by rw [Φ.tgt_mor]; exact Φ.tgt.mem_boundarySet⟩
  src_mor Φ := Subtype.ext Φ.src_mor
  tgt_mor Φ := Subtype.ext Φ.tgt_mor
  mor_comp Φ Ψ h := by
    have h' : C.toGroupoidStr.src Φ.mor = C.toGroupoidStr.tgt Ψ.mor := by
      rw [Φ.src_mor, Ψ.tgt_mor]; exact congrArg BObj.α h
    refine Subtype.ext ?_
    change ((S.bdryGroupoid hT hS).comp Φ Ψ).mor = _
    rw [bdryGroupoid_comp_mor h]
    simp only [GroupoidStr.fullSub, dif_pos h']
  mor_unit _ := rfl

variable (S hT hS) in
/-- The forgetful functor `B : bC → C` (2021 (17.81)), `B_C` followed by `∂C ⊆ C`. -/
def bdryFunctorC : GroupoidFunctor (S.bdryGroupoid hT hS) C.toGroupoidStr :=
  (GroupoidStr.fullSubInclusion C.toGroupoidStr S.boundarySet).comp (S.bdryFunctor hT hS)

@[simp] theorem bdryFunctorC_obj (a : S.BObj hT hS) : (S.bdryFunctorC hT hS).obj a = a.α := rfl

@[simp] theorem bdryFunctorC_mor (Φ : S.BMor hT hS) : (S.bdryFunctorC hT hS).mor Φ = Φ.mor :=
  rfl

/-- **Over `α ∈ ∂C` lie exactly `d_C(α)` objects of `bC`** (2021 p. 791, "a finite number of
`ᾱᵢ`"). -/
theorem encard_obj_preimage (α : C.Obj) :
    {a : S.BObj hT hS | a.α = α}.encard = S.degIndex α := by
  rw [definition_17_1_30 (bdryRefUnif_mem hS α) (obj_refPt hS α),
    ← encard_bMap_preimage (S.hdU hT (S.bdryRefUnif hS α)) (S.refPt hS α)]
  refine Set.encard_congr ?_
  exact {
    toFun := fun a => ⟨cast (by rw [a.2]) a.1.p, by
      obtain ⟨⟨β, p, hp⟩, hβ⟩ := a
      change β = α at hβ
      subst hβ
      exact hp⟩
    invFun := fun p => ⟨⟨α, p.1, p.2⟩, rfl⟩
    left_inv := fun a => by
      obtain ⟨⟨β, p, hp⟩, hβ⟩ := a
      change β = α at hβ
      subst hβ
      rfl
    right_inv := fun p => rfl }

/-- **2021 Definition 17.4.4, p. 791**: the morphisms `Φ` form the morphism class of the groupoid
`bC`, every hom-set is finite, `Φ ↦ φ` with `ᾱ ↦ α` is the forgetful functor `B_C : bC → ∂C`
(17.63), and `B_C` is faithful. -/
theorem definition_17_4_4 :
    (∀ a b : S.BObj hT hS, ((S.bdryGroupoid hT hS).mor a b).Finite) ∧
    (∀ Φ : S.BMor hT hS, ((S.bdryFunctor hT hS).mor Φ).1 = Φ.mor ∧
      ((S.bdryFunctor hT hS).obj Φ.src).1 = Φ.src.α) ∧
    ∀ Φ Ψ : S.BMor hT hS, Φ.src = Ψ.src → (S.bdryFunctor hT hS).mor Φ =
      (S.bdryFunctor hT hS).mor Ψ → Φ = Ψ :=
  ⟨(S.bdryCategory hT hS).finite_mor, fun _ => ⟨rfl, rfl⟩, fun _ _ hs hm =>
    BMor.ext_of_src hs (congrArg Subtype.val hm)⟩

end Morphisms

end GCT.PolyfoldConstruction

end Polyfold
