import Polyfold.Chapter19.BasicConstruction
import Polyfold.Chapter17.ProperCoveringModel

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19, §19.7
"Covering Constructions", pp. 905–910: **Definition 19.7.1** (finite-to-one covering functor),
**Remark 19.7.2**, **Definition 19.7.3** (proper covering uniformizer), **Definition 19.7.4**
(cartesian diagram (19.22)), **Lemma 19.7.5**, **Remark 19.7.6**, **Definition 19.7.7** (proper
covering uniformizer construction), **Remark 19.7.8**, the transition sets `M(Ψ̂, Ψ̂')` with the map
`p` of (19.23), **Lemma 19.7.9**, **Lemma 19.7.10**, the structural diagrams of p. 909–910 and
**Definition 19.7.11** (basic construction for `P`).  Numbers and pages are the 2021 text's.

# Covering constructions: the set-level part

## The text, paraphrased

(Definition 19.7.1) A finite-to-one covering functor `P : A → B` of groupoidal categories is
surjective on objects with finite preimages, and `φ̂ ↦ (P(φ̂), s(φ̂))` is a bijection
`𝐀 → 𝐁 ₛ×_P A`.  (Remark 19.7.2) There is no topology; compare Definition 17.8.1.
(Definition 19.7.3) A proper covering uniformizer for `P` at `β` with isotropy `G` is a pair of
functors `Ψ̂ : E → A`, `Ψ : G ⋉ O_β → B` with `τ̂ : E → G ⋉ O_β` a proper ep-groupoid covering
model (Definition 17.8.4) such that (1) the distinguished point `o_β` is mapped by `Ψ` to `β`;
(2) `Ψ`, `Ψ̂` are fully faithful, injective on objects and `P ∘ Ψ̂ = Ψ ∘ τ̂`; (3) the diagram
(19.22) is cartesian.  (Definition 19.7.4) Cartesian: on objects the image of `⟨τ̂, Ψ̂⟩` consists
exactly of the `(o, a)` with `P(a) = Ψ(o)`, each with a unique `e`; on morphisms every `φ̂` with
`P(φ̂) = Ψ(g, o)` is `Ψ̂(ĝ)` for some `ĝ` with `τ̂(ĝ) = (g, o)`.  (Lemma 19.7.5) `Ψ` is determined
by `Ψ̂`: `Ψ(o) = P ∘ Ψ̂ ∘ (τ̂|Ô_a)⁻¹(o)` and `Ψ(g, o) = P ∘ Ψ̂(ĝ)`.  (Definition 19.7.7) A proper
covering uniformizer construction `F̂` assigns to `β` a set `F̂(β)` of such uniformizers; it
induces `F` for `B` (19.24).  (19.23) `p(e, φ̂, e') = (τ̂(e), P(φ̂), τ̂'(e'))`.
(Lemma 19.7.9) `p` is surjective, and the preimages of `h = (o, φ, o')` correspond to the
`e ∈ E` with `τ̂(e) = o`; they are finite.  (Lemma 19.7.10) `(e, φ̂, e') ↦ (p(e, φ̂, e'), e)` is a
bijection `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`.  (pp. 909–910) `p` commutes with `s`, `t`, `ι`, `u`, `m`.
(Definition 19.7.11) A basic construction for `P` is a pair `(F̂, 𝓕)` with `𝓕` a transition
construction for the induced `F`, so that `(F, 𝓕)` is a basic construction for `B`.

## What is formalized

* **Definition 19.7.1**: `IsFiniteToOneCovering P`; the lift `IsFiniteToOneCovering.lift`
  (`P_lift`, `src_lift`, `eq_lift`), `existsUnique_lift`.  **Remark 19.7.2**:
  `remark_19_7_2` (the identity functor of any groupoidal category is one).
* **Definitions 19.7.3, 19.7.4**: `CoveringUniformizer P β` (the data `Ψ`, `E`, `τ̂` with a
  `ProperCoveringModel`, `Ψ̂`, and (1)–(3)), `definition_19_7_4` (the cartesian property as
  printed, with the uniqueness of `e`), `CoveringUniformizer.isCentredAt`.
* **Lemma 19.7.5**: `lemma_19_7_5` (two functors `Ψ₁`, `Ψ₂` with `P ∘ Ψ̂ = Ψᵢ ∘ τ̂` agree), and
  the printed formulas `CoveringUniformizer.obj_eq`, `CoveringUniformizer.mor_eq`.
  **Remark 19.7.6**: `CoveringUniformizer.remark_19_7_6`.
* **Definition 19.7.7**: `CoveringUniformizerConstruction P`, `.Unif`, the induced
  `toUniformizerConstruction` (19.24), `Unif.toUnif`.  **Remark 19.7.8**: `remark_19_7_8`.
* The transition sets `CoveringUniformizer.Trans` and `transMap` (`p`, (19.23)), with
  `transMap_unit`, `transMap_inv`, `transMap_comp` (the structural diagrams of pp. 909–910).
* **Lemma 19.7.9**: `lemma_19_7_9` (surjective; `x ↦ s(x)` is a bijection from `p⁻¹(h)` onto
  `τ̂⁻¹(s(h))`; finite), with `finite_fiber_τ`.
* **Lemma 19.7.10**: `FibTrans`, `fibredTransMap`, `lemma_19_7_10`, `transEquiv`.
* **Definition 19.7.11**: `CoveringBasicConstruction P` (`hatU`, `𝓕`), `toBasic`.

## Readings

* "Functors `Ψ̂ : E → A`": `E` is an ep-groupoid and `Ψ̂` a functor of the underlying groupoids, as
  for Chapter 17's `ProperCoveringUniformizer`; `Ψ` is a `Uniformizer` of `B` (its fields are the
  conditions of (2) for `Ψ`).  The distinguished point `o_β` of (1) is the point `ō` of the
  model (Definition 17.8.4), as in Corollary 19.7.20 ("distinguished element `ō ∈ O` satisfying
  `Ψ(ō) = β`"); "with isotropy `G`" is then a consequence (`isCentredAt`).
* Definition 19.7.4: the inclusion of the image of `⟨τ̂, Ψ̂⟩` in the pairs is `P ∘ Ψ̂ = Ψ ∘ τ̂`;
  the uniqueness of `e` follows from the injectivity of `Ψ̂` (`definition_19_7_4`).
* Definition 19.7.7: `F̂ : B → SET` is read on objects (as Definition 19.1.3); the induced `F` is
  `F(β) = {Ψ | (Ψ̂, Ψ) ∈ F̂(β)}`.  "Finite-to-one *proper* covering functor" (Proposition
  19.7.13), "finite-to-one *local* covering functor" (Proposition 19.7.14) are read as Definition
  19.7.1.
* The finiteness in Lemma 19.7.9 comes from Definition 19.7.1 (1) (`Ψ̂` is injective on objects
  and maps `τ̂⁻¹(o)` into `P⁻¹(Ψ(o))`); Definition 17.8.4 does not ask for finite fibres.
-/

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

variable {A B : GroupoidalCategory.{u}}

/-! ### Definition 19.7.1 -/

/-- **2021 Definition 19.7.1, p. 906 (finite-to-one covering functor)**: a functor `P : A → B` of
groupoidal categories which (1) is surjective on objects with finite preimages, and (2) for
which `φ̂ ↦ (P(φ̂), s(φ̂))` is a bijection `𝐀 → 𝐁 ₛ×_P A`. -/
structure IsFiniteToOneCovering (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr) : Prop where
  /-- (1) `P` is surjective on objects. -/
  surjective : Surjective P.obj
  /-- (1) The preimage of every object is finite. -/
  finite_fiber : ∀ β, (P.obj ⁻¹' {β}).Finite
  /-- (2) `𝐀 → 𝐁 ₛ×_P A`, `φ̂ ↦ (P(φ̂), s(φ̂))`, is a bijection. -/
  bijective : Bijective fun φ : A.Mor =>
    (⟨(P.mor φ, A.toGroupoidStr.src φ), P.src_mor φ⟩ :
      {p : B.Mor × A.Obj // B.toGroupoidStr.src p.1 = P.obj p.2})

namespace IsFiniteToOneCovering

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}

/-- **The lift** of `φ` with `s(φ) = P(a)`: the unique `φ̂` with `P(φ̂) = φ`, `s(φ̂) = a`. -/
def lift (hP : IsFiniteToOneCovering P) (φ : B.Mor) (a : A.Obj) (h : B.toGroupoidStr.src φ = P.obj
    a) : A.Mor :=
  (hP.bijective.2 ⟨(φ, a), h⟩).choose

theorem lift_spec (hP : IsFiniteToOneCovering P) (φ : B.Mor) (a : A.Obj) (h : B.toGroupoidStr.src
    φ = P.obj a) :
    P.mor (hP.lift φ a h) = φ ∧ A.toGroupoidStr.src (hP.lift φ a h) = a := by
  have h' := (hP.bijective.2 ⟨(φ, a), h⟩).choose_spec
  have h'' := congrArg Subtype.val h'
  exact ⟨congrArg Prod.fst h'', congrArg Prod.snd h''⟩

theorem P_lift (hP : IsFiniteToOneCovering P) (φ : B.Mor) (a : A.Obj) (h : B.toGroupoidStr.src φ =
    P.obj a) :
    P.mor (hP.lift φ a h) = φ := (hP.lift_spec φ a h).1

theorem src_lift (hP : IsFiniteToOneCovering P) (φ : B.Mor) (a : A.Obj) (h : B.toGroupoidStr.src φ
    = P.obj a) :
    A.toGroupoidStr.src (hP.lift φ a h) = a := (hP.lift_spec φ a h).2

/-- A morphism of `A` is determined by its image and its source. -/
theorem mor_ext (hP : IsFiniteToOneCovering P) {φ φ' : A.Mor} (hm : P.mor φ = P.mor φ')
    (hs : A.toGroupoidStr.src φ = A.toGroupoidStr.src φ') : φ = φ' :=
  hP.bijective.1 (Subtype.ext (Prod.ext hm hs))

theorem eq_lift (hP : IsFiniteToOneCovering P) {φ : B.Mor} {a : A.Obj} (h : B.toGroupoidStr.src φ
    = P.obj a) {φ' : A.Mor}
    (hm : P.mor φ' = φ) (hs : A.toGroupoidStr.src φ' = a) : φ' = hP.lift φ a h :=
  hP.mor_ext (hm.trans (hP.P_lift φ a h).symm) (hs.trans (hP.src_lift φ a h).symm)

/-- Definition 19.7.1 (2) in the form used in the proofs: every `φ` with `s(φ) = P(a)` has a
unique lift with source `a`. -/
theorem existsUnique_lift (hP : IsFiniteToOneCovering P) {φ : B.Mor} {a : A.Obj} (h :
    B.toGroupoidStr.src φ = P.obj a) :
    ∃! φ' : A.Mor, P.mor φ' = φ ∧ A.toGroupoidStr.src φ' = a :=
  ⟨hP.lift φ a h, hP.lift_spec φ a h, fun _ h' => hP.eq_lift h h'.1 h'.2⟩

end IsFiniteToOneCovering

/-- **2021 Remark 19.7.2, p. 906**: Definition 19.7.1 involves no topology; the identity functor
of any groupoidal category is a finite-to-one covering functor. -/
theorem remark_19_7_2 (C : GroupoidalCategory.{u}) :
    IsFiniteToOneCovering (GroupoidFunctor.id C.toGroupoidStr) where
  surjective := surjective_id
  finite_fiber β := by
    change ((id : C.Obj → C.Obj) ⁻¹' {β}).Finite
    exact finite_singleton β
  bijective := ⟨fun _ _ h => congrArg (fun p => p.1.1) h,
    fun p => ⟨p.1.1, Subtype.ext (Prod.ext rfl p.2)⟩⟩

/-! ### Definitions 19.7.3 and 19.7.4 -/

/-- **2021 Definition 19.7.3, p. 906 (proper covering uniformizer)**, with **Definition 19.7.4,
p. 907 (cartesian)**: at the object `β` of `B`, a uniformizer `Ψ : G ⋉ O_β → B` (fully faithful,
injective on objects), an ep-groupoid `E`, a proper ep-groupoid covering model
`τ̂ : E → G ⋉ O_β` (Definition 17.8.4, `model`) and a functor `Ψ̂ : E → A` (`hat`) with (1)
`Ψ(ō) = β`, (2) `Ψ̂` fully faithful and injective on objects and `P ∘ Ψ̂ = Ψ ∘ τ̂`, (3) the
diagram (19.22) cartesian (Definition 19.7.4: `cartesian_obj`, `cartesian_mor`). -/
structure CoveringUniformizer (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr) (β : B.Obj) :
    Type (u + 1) where
  /-- The uniformizer `Ψ : G ⋉ O_β → B`. -/
  Ψ : B.Uniformizer
  /-- The objects of `E`. -/
  ObjE : Type u
  /-- The morphisms of `E`. -/
  MorE : Type u
  [topObjE : TopologicalSpace ObjE]
  [t2ObjE : T2Space ObjE]
  [paraObjE : ParacompactSpace ObjE]
  [topMorE : TopologicalSpace MorE]
  [t2MorE : T2Space MorE]
  [paraMorE : ParacompactSpace MorE]
  /-- The ep-groupoid `E`. -/
  E : EpGroupoid ObjE MorE
  /-- The functor `τ̂ : E → G ⋉ O_β`. -/
  τ : EpFunctor E (actionEpGroupoid Ψ.smooth_smul)
  /-- `τ̂` is a proper ep-groupoid covering model (Definition 17.8.4); its point is `o_β`. -/
  model : ProperCoveringModel τ
  /-- The functor `Ψ̂ : E → A`. -/
  hat : GroupoidFunctor E.toGroupoidStr A.toGroupoidStr
  /-- (1) `Ψ(o_β) = β`. -/
  obj_pt : Ψ.obj model.pt = β
  /-- (2) `Ψ̂` is injective on objects. -/
  injective_hat : Injective hat.obj
  /-- (2) `Ψ̂` is full. -/
  full_hat : hat.toFunctor.Full
  /-- (2) `Ψ̂` is faithful. -/
  faithful_hat : hat.toFunctor.Faithful
  /-- (2) `P ∘ Ψ̂ = Ψ ∘ τ̂` on objects. -/
  obj_comm : ∀ e, P.obj (hat.obj e) = Ψ.obj (τ.obj e)
  /-- (2) `P ∘ Ψ̂ = Ψ ∘ τ̂` on morphisms. -/
  mor_comm : ∀ φ, P.mor (hat.mor φ) = Ψ.mor (τ.mor φ)
  /-- (3), Definition 19.7.4 on objects: every `(o, a)` with `P(a) = Ψ(o)` is `(τ̂(e), Ψ̂(e))`. -/
  cartesian_obj : ∀ (o : Ψ.O) (a : A.Obj), P.obj a = Ψ.obj o → ∃ e, τ.obj e = o ∧ hat.obj e = a
  /-- (3), Definition 19.7.4 on morphisms: every `φ̂` with `P(φ̂) = Ψ(g, o)` is `Ψ̂(ĝ)` with
  `τ̂(ĝ) = (g, o)`. -/
  cartesian_mor : ∀ (φ : A.Mor) (p : Ψ.G × Ψ.O), P.mor φ = Ψ.mor p →
    ∃ ψ, τ.mor ψ = p ∧ hat.mor ψ = φ

attribute [instance] CoveringUniformizer.topObjE CoveringUniformizer.t2ObjE
  CoveringUniformizer.paraObjE CoveringUniformizer.topMorE CoveringUniformizer.t2MorE
  CoveringUniformizer.paraMorE

namespace CoveringUniformizer

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} {β : B.Obj}
  (Ψh : CoveringUniformizer P β)

/-- **2021 Definition 19.7.4, p. 907, as printed**: on the object level the image of
`⟨τ̂, Ψ̂⟩ : E → O_β × A` is precisely the set of pairs `(o, a)` with `P(a) = Ψ(o)`, each with a
unique `e`; on morphisms every `φ̂` with `P(φ̂) = Ψ(g, o)` is `Ψ̂(ĝ)` with `τ̂(ĝ) = (g, o)`. -/
theorem definition_19_7_4 :
    range (fun e => (Ψh.τ.obj e, Ψh.hat.obj e)) = {p | P.obj p.2 = Ψh.Ψ.obj p.1} ∧
      (∀ (o : Ψh.Ψ.O) (a : A.Obj), P.obj a = Ψh.Ψ.obj o →
        ∃! e, Ψh.τ.obj e = o ∧ Ψh.hat.obj e = a) ∧
      ∀ (φ : A.Mor) (p : Ψh.Ψ.G × Ψh.Ψ.O), P.mor φ = Ψh.Ψ.mor p →
        ∃ ψ, Ψh.τ.mor ψ = p ∧ Ψh.hat.mor ψ = φ := by
  refine ⟨ext fun p => ⟨?_, fun hp => ?_⟩, fun o a h => ?_, Ψh.cartesian_mor⟩
  · rintro ⟨e, rfl⟩
    exact Ψh.obj_comm e
  · obtain ⟨e, he, he'⟩ := Ψh.cartesian_obj p.1 p.2 hp
    exact ⟨e, Prod.ext he he'⟩
  · obtain ⟨e, he, he'⟩ := Ψh.cartesian_obj o a h
    exact ⟨e, ⟨he, he'⟩, fun e' h' => Ψh.injective_hat (h'.2.trans he'.symm)⟩

/-- "With isotropy `G`" (Definition 19.7.3): `Ψ` is centred at `β`, `G` fixing `o_β`, so
`G ≅ Aut(β)` (`Uniformizer.isotropyEquiv`). -/
theorem isCentredAt : Ψh.Ψ.IsCentredAt β := ⟨Ψh.model.pt, Ψh.obj_pt, Ψh.model.smul_pt⟩

/-- **Lemma 19.7.5, the printed formula on objects**: `Ψ(o) = P ∘ Ψ̂ ∘ (τ̂|Ô_a)⁻¹(o)` for
`a ∈ τ̂⁻¹(o_β)`. -/
theorem obj_eq {a : Ψh.ObjE} (ha : a ∈ Ψh.model.fiber) (o : Ψh.Ψ.O) :
    Ψh.Ψ.obj o = P.obj (Ψh.hat.obj (Ψh.model.σ a o)) := by
  rw [Ψh.obj_comm, Ψh.model.obj_σ ha]

/-- **Lemma 19.7.5, the printed formula on morphisms**: `Ψ(g, o) = P ∘ Ψ̂(ĝ)` for the `ĝ` with
`τ̂(ĝ) = (g, o)` and `s(ĝ) = ô ∈ Ô_a` over `o`. -/
theorem mor_eq {a : Ψh.ObjE} (ha : a ∈ Ψh.model.fiber) (g : Ψh.Ψ.G) (o : Ψh.Ψ.O) :
    Ψh.Ψ.mor (g, o) = P.mor (Ψh.hat.mor (Ψh.model.liftMor g (Ψh.model.σ a o))) := by
  rw [Ψh.mor_comm, Ψh.model.mor_eq, Ψh.model.groupIndex_liftMor, Ψh.model.src_liftMor,
    Ψh.model.obj_σ ha]

end CoveringUniformizer

/-! ### Lemma 19.7.5 -/

section Lemma5

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {PO : MPolyfold O} {hPO : ∀ g : G, PO.IsScSmoothMap PO fun y => g • y}
  {ObjE MorE : Type u} [TopologicalSpace ObjE] [T2Space ObjE] [ParacompactSpace ObjE]
  [TopologicalSpace MorE] [T2Space MorE] [ParacompactSpace MorE] {E : EpGroupoid ObjE MorE}

/-- **2021 Lemma 19.7.5, p. 907**: for a proper ep-groupoid covering model `τ̂ : E → G ⋉ O`, a
functor `P : A → B` and a functor `Ψ̂ : E → A`, at most one functor `Ψ : G ⋉ O → B` satisfies
`P ∘ Ψ̂ = Ψ ∘ τ̂`: `Ψ(o) = P(Ψ̂(e))` for any `e` over `o`, and `Ψ(g, o) = P(Ψ̂(ĝ))` for the `ĝ` with
`τ̂(ĝ) = (g, o)`.  (Only the commutativity and Definition 17.8.4 are used.) -/
theorem lemma_19_7_5 (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr)
    {τ : EpFunctor E (actionEpGroupoid hPO)} (M : ProperCoveringModel τ)
    (hat : GroupoidFunctor E.toGroupoidStr A.toGroupoidStr)
    (Ψ₁ Ψ₂ : GroupoidFunctor (GroupoidStr.translation G O) B.toGroupoidStr)
    (h₁ : ∀ e, P.obj (hat.obj e) = Ψ₁.obj (τ.obj e)) (h₁' : ∀ φ, P.mor (hat.mor φ) = Ψ₁.mor (τ.mor
        φ))
    (h₂ : ∀ e, P.obj (hat.obj e) = Ψ₂.obj (τ.obj e)) (h₂' : ∀ φ, P.mor (hat.mor φ) = Ψ₂.mor (τ.mor
        φ)) :
    Ψ₁ = Ψ₂ := by
  refine GroupoidFunctor.ext (funext fun o => ?_) (funext fun p => ?_)
  · obtain ⟨e, rfl⟩ := M.surjective o
    rw [← h₁, h₂]
  · obtain ⟨e, he⟩ := M.surjective p.2
    have hm : τ.mor (M.liftMor p.1 e) = p := by
      rw [M.mor_eq, M.groupIndex_liftMor, M.src_liftMor, he]
    rw [← hm, ← h₁', h₂']

/-- **2021 Remark 19.7.6, p. 908**: two proper covering uniformizers with the same `E`, `τ̂`-data
and `Ψ̂` have the same `Ψ` on objects and morphisms (so one may speak of "the uniformizer `Ψ̂`"). -/
theorem CoveringUniformizer.remark_19_7_6 {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    {β : B.Obj} (Ψh : CoveringUniformizer P β)
    (Ψ' : GroupoidFunctor (GroupoidStr.translation Ψh.Ψ.G Ψh.Ψ.O) B.toGroupoidStr)
    (h : ∀ e, P.obj (Ψh.hat.obj e) = Ψ'.obj (Ψh.τ.obj e))
    (h' : ∀ φ, P.mor (Ψh.hat.mor φ) = Ψ'.mor (Ψh.τ.mor φ)) : Ψ' = Ψh.Ψ.functor :=
  lemma_19_7_5 P Ψh.model Ψh.hat Ψ' Ψh.Ψ.functor h h' Ψh.obj_comm Ψh.mor_comm

end Lemma5

/-! ### Definition 19.7.7 -/

/-- **2021 Definition 19.7.7, p. 908 (proper covering uniformizer construction)**: a set `F̂(β)`
of proper covering uniformizers for `P` at every object `β` of `B`. -/
structure CoveringUniformizerConstruction (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr) :
    Type (u + 1) where
  /-- The sets `F̂(β)`. -/
  F : ∀ β : B.Obj, Set (CoveringUniformizer P β)

namespace CoveringUniformizerConstruction

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
  (F : CoveringUniformizerConstruction P)

/-- **The induced uniformizer construction (19.24)** for `B`: `F(β) = {Ψ | (Ψ̂, Ψ) ∈ F̂(β)}`. -/
def toUniformizerConstruction : B.UniformizerConstruction where
  F β := (fun Ψh => Ψh.Ψ) '' F.F β
  isAt β Ψ hΨ := by
    obtain ⟨Ψh, -, rfl⟩ := hΨ
    exact ⟨Ψh.model.pt, Ψh.obj_pt⟩

/-- A uniformizer of the construction: `β` and `Ψ̂ ∈ F̂(β)`. -/
structure Unif where
  /-- The object `β`. -/
  β : B.Obj
  /-- The proper covering uniformizer `Ψ̂ ∈ F̂(β)`. -/
  Ψh : CoveringUniformizer P β
  mem : Ψh ∈ F.F β

variable {F}

/-- The underlying uniformizer `Ψ ∈ F(β)` of `Ψ̂ ∈ F̂(β)`. -/
def Unif.toUnif (x : F.Unif) : F.toUniformizerConstruction.Unif :=
  ⟨x.Ψh.Ψ, x.β, x.Ψh, x.mem, rfl⟩

@[simp] theorem Unif.toUnif_val (x : F.Unif) : x.toUnif.1 = x.Ψh.Ψ := rfl

/-- **2021 Remark 19.7.8, p. 908**: from `Ψ̂ ∈ F̂(β)` we construct the associated `Ψ ∈ F(β)`,
which is centred at `β`; every `Ψ ∈ F(β)` arises so. -/
theorem remark_19_7_8 (β : B.Obj) :
    (∀ Ψh ∈ F.F β, Ψh.Ψ ∈ F.toUniformizerConstruction.F β ∧ Ψh.Ψ.IsCentredAt β) ∧
      ∀ Ψ ∈ F.toUniformizerConstruction.F β, ∃ Ψh ∈ F.F β, Ψh.Ψ = Ψ :=
  ⟨fun Ψh h => ⟨⟨Ψh, h, rfl⟩, Ψh.isCentredAt⟩, fun _ h => h⟩

end CoveringUniformizerConstruction

/-! ### The transition sets `M(Ψ̂, Ψ̂')` and the map `p` (19.23) -/

namespace CoveringUniformizer

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} {β β' β'' : B.Obj}

/-- **The transition set `M(Ψ̂, Ψ̂')`** (p. 908): the triples `(e, φ̂, e')` with
`φ̂ : Ψ̂(e) → Ψ̂'(e')`. -/
abbrev Trans (Ψh : CoveringUniformizer P β) (Ψh' : CoveringUniformizer P β') : Type u :=
  A.toGroupoidStr.TransitionSet Ψh.hat.obj Ψh'.hat.obj

variable (Ψh : CoveringUniformizer P β) (Ψh' : CoveringUniformizer P β')
  (Ψh'' : CoveringUniformizer P β'')

/-- **The map `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` of (19.23)**: `p(e, φ̂, e') = (τ̂(e), P(φ̂), τ̂'(e'))`. -/
def transMap (x : Ψh.Trans Ψh') : Ψh.Ψ.Trans Ψh'.Ψ where
  src := Ψh.τ.obj x.src
  mor := P.mor x.mor
  tgt := Ψh'.τ.obj x.tgt
  src_mor := by rw [P.src_mor, x.src_mor, Ψh.obj_comm]
  tgt_mor := by rw [P.tgt_mor, x.tgt_mor, Ψh'.obj_comm]

@[simp] theorem transMap_src (x : Ψh.Trans Ψh') : (Ψh.transMap Ψh' x).src = Ψh.τ.obj x.src := rfl
@[simp] theorem transMap_mor (x : Ψh.Trans Ψh') : (Ψh.transMap Ψh' x).mor = P.mor x.mor := rfl
@[simp] theorem transMap_tgt (x : Ψh.Trans Ψh') : (Ψh.transMap Ψh' x).tgt = Ψh'.τ.obj x.tgt := rfl

/-- The unit diagram (19.31): `p ∘ û = u ∘ τ̂`. -/
theorem transMap_unit (e : Ψh.ObjE) :
    Ψh.transMap Ψh (TransitionSet.unit e) = TransitionSet.unit (Ψh.τ.obj e) :=
  TransitionSet.ext rfl ((P.mor_unit _).trans (by rw [Ψh.obj_comm]; rfl)) rfl

/-- The inversion diagram (19.31): `p ∘ ι̂ = ι ∘ p`. -/
theorem transMap_inv (x : Ψh.Trans Ψh') : Ψh'.transMap Ψh x.inv = (Ψh.transMap Ψh' x).inv :=
  TransitionSet.ext rfl (P.mor_inv _) rfl

/-- The multiplication diagram (19.32): `p ∘ m̂ = m ∘ (p ₛ×ₜ p)`. -/
theorem transMap_comp (x : Ψh'.Trans Ψh'') (y : Ψh.Trans Ψh')
    (h : A.toGroupoidStr.src x.mor = A.toGroupoidStr.tgt y.mor) :
    Ψh.transMap Ψh'' (TransitionSet.comp x y h) =
      TransitionSet.comp (Ψh'.transMap Ψh'' x) (Ψh.transMap Ψh' y)
        (by rw [transMap_mor, transMap_mor, P.src_mor, P.tgt_mor, h]) :=
  TransitionSet.ext rfl (P.mor_comp _ _ h) rfl

/-- The source and target diagram (19.30): `s ∘ p = τ̂ ∘ s` and `t ∘ p = τ̂' ∘ t`. -/
theorem transMap_src_tgt (x : Ψh.Trans Ψh') :
    (Ψh.transMap Ψh' x).src = Ψh.τ.obj x.src ∧ (Ψh.transMap Ψh' x).tgt = Ψh'.τ.obj x.tgt :=
  ⟨rfl, rfl⟩

/-- The fibre `τ̂⁻¹(o)` is finite (Definition 19.7.1 (1): `Ψ̂` embeds it in `P⁻¹(Ψ(o))`). -/
theorem finite_fiber_τ (hP : IsFiniteToOneCovering P) (o : Ψh.Ψ.O) :
    (Ψh.τ.obj ⁻¹' {o}).Finite := by
  refine Finite.of_finite_image ((hP.finite_fiber (Ψh.Ψ.obj o)).subset ?_)
    Ψh.injective_hat.injOn
  rintro _ ⟨e, he, rfl⟩
  change P.obj (Ψh.hat.obj e) = Ψh.Ψ.obj o
  rw [Ψh.obj_comm, show Ψh.τ.obj e = o from he]

variable {Ψh Ψh'}

/-- The element of `M(Ψ̂, Ψ̂')` over `h ∈ M(Ψ, Ψ')` with source `e`, `τ̂(e) = s(h)` (the
construction in the proof of Lemma 19.7.9). -/
def liftTrans (hP : IsFiniteToOneCovering P) (h : Ψh.Ψ.Trans Ψh'.Ψ) (e : Ψh.ObjE)
    (he : h.src = Ψh.τ.obj e) : Ψh.Trans Ψh' :=
  have hs : B.toGroupoidStr.src h.mor = P.obj (Ψh.hat.obj e) := by
    rw [h.src_mor, he, Ψh.obj_comm]
  have ht : P.obj (A.toGroupoidStr.tgt (hP.lift h.mor _ hs)) = Ψh'.Ψ.obj h.tgt := by
    rw [← P.tgt_mor, hP.P_lift, h.tgt_mor]
  { src := e
    mor := hP.lift h.mor _ hs
    tgt := (Ψh'.cartesian_obj h.tgt _ ht).choose
    src_mor := hP.src_lift _ _ hs
    tgt_mor := (Ψh'.cartesian_obj h.tgt _ ht).choose_spec.2.symm }

theorem liftTrans_src (hP : IsFiniteToOneCovering P) (h : Ψh.Ψ.Trans Ψh'.Ψ) (e : Ψh.ObjE)
    (he : h.src = Ψh.τ.obj e) : (liftTrans hP h e he).src = e := rfl

theorem transMap_liftTrans (hP : IsFiniteToOneCovering P) (h : Ψh.Ψ.Trans Ψh'.Ψ) (e : Ψh.ObjE)
    (he : h.src = Ψh.τ.obj e) : Ψh.transMap Ψh' (liftTrans hP h e he) = h := by
  have hs : B.toGroupoidStr.src h.mor = P.obj (Ψh.hat.obj e) := by
    rw [h.src_mor, he, Ψh.obj_comm]
  have ht : P.obj (A.toGroupoidStr.tgt (hP.lift h.mor _ hs)) = Ψh'.Ψ.obj h.tgt := by
    rw [← P.tgt_mor, hP.P_lift, h.tgt_mor]
  exact TransitionSet.ext he.symm (hP.P_lift _ _ hs) (Ψh'.cartesian_obj h.tgt _ ht).choose_spec.1

/-- An element of `M(Ψ̂, Ψ̂')` is determined by its image under `p` and its source. -/
theorem trans_ext (hP : IsFiniteToOneCovering P) {x y : Ψh.Trans Ψh'}
    (hp : Ψh.transMap Ψh' x = Ψh.transMap Ψh' y) (hs : x.src = y.src) : x = y := by
  have hm : x.mor = y.mor := hP.mor_ext (congrArg TransitionSet.mor hp) (by
    rw [x.src_mor, y.src_mor, hs])
  refine TransitionSet.ext hs hm (Ψh'.injective_hat ?_)
  rw [← x.tgt_mor, ← y.tgt_mor, hm]

theorem eq_liftTrans (hP : IsFiniteToOneCovering P) (x : Ψh.Trans Ψh') :
    x = liftTrans hP (Ψh.transMap Ψh' x) x.src rfl :=
  trans_ext hP (transMap_liftTrans hP _ _ _).symm rfl

variable (Ψh Ψh')

/-- **2021 Lemma 19.7.9, p. 908**: `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is surjective; for
`h = (o, φ, o')` the preimages `p⁻¹(h)` correspond bijectively, by `x ↦ s(x)`, to the
`e ∈ E` with `τ̂(e) = o`; and `p⁻¹(h)` is finite. -/
theorem lemma_19_7_9 (hP : IsFiniteToOneCovering P) :
    Surjective (Ψh.transMap Ψh') ∧
      ∀ h : Ψh.Ψ.Trans Ψh'.Ψ, BijOn (fun x : Ψh.Trans Ψh' => x.src) (Ψh.transMap Ψh' ⁻¹' {h})
          (Ψh.τ.obj ⁻¹' {h.src}) ∧ (Ψh.transMap Ψh' ⁻¹' {h}).Finite := by
  have hsurj : Surjective (Ψh.transMap Ψh') := fun h => by
    obtain ⟨e, he⟩ := Ψh.model.surjective h.src
    exact ⟨liftTrans hP h e he.symm, transMap_liftTrans hP h e he.symm⟩
  refine ⟨hsurj, fun h => ?_⟩
  have hbij : BijOn (fun x : Ψh.Trans Ψh' => x.src) (Ψh.transMap Ψh' ⁻¹' {h})
      (Ψh.τ.obj ⁻¹' {h.src}) := by
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => trans_ext hP (hx.trans hy.symm) hxy,
      fun e he => ⟨liftTrans hP h e (he : Ψh.τ.obj e = h.src).symm,
        transMap_liftTrans hP h e _, rfl⟩⟩
    have hx' : Ψh.transMap Ψh' x = h := hx
    change Ψh.τ.obj x.src = h.src
    rw [← hx']
    rfl
  exact ⟨hbij, Finite.of_finite_image ((Ψh.finite_fiber_τ hP h.src).subset hbij.mapsTo.image_subset)
    hbij.injOn⟩

/-- The fibred product `M(Ψ, Ψ') ₛ×_τ̂ E = {(h, e) | s(h) = τ̂(e)}` of Lemma 19.7.10. -/
abbrev FibTrans : Type u := {p : Ψh.Ψ.Trans Ψh'.Ψ × Ψh.ObjE // p.1.src = Ψh.τ.obj p.2}

/-- The map `(e, φ̂, e') ↦ (p(e, φ̂, e'), e)` of Lemma 19.7.10 and (19.26). -/
def fibredTransMap (x : Ψh.Trans Ψh') : Ψh.FibTrans Ψh' := ⟨(Ψh.transMap Ψh' x, x.src), rfl⟩

/-- **2021 Lemma 19.7.10, p. 909**: `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`,
`(e, φ̂, e') ↦ ((τ̂(e), P(φ̂), τ̂'(e')), e)`, is a bijection. -/
theorem lemma_19_7_10 (hP : IsFiniteToOneCovering P) : Bijective (Ψh.fibredTransMap Ψh') :=
  ⟨fun _ _ hxy => trans_ext hP (congrArg (fun q : Ψh.FibTrans Ψh' => q.1.1) hxy)
      (congrArg (fun q : Ψh.FibTrans Ψh' => q.1.2) hxy),
    fun q => ⟨liftTrans hP q.1.1 q.1.2 q.2, Subtype.ext (Prod.ext
      (transMap_liftTrans hP _ _ _) rfl)⟩⟩

/-- The bijection of Lemma 19.7.10 as an equivalence, with inverse `liftTrans`. -/
def transEquiv (hP : IsFiniteToOneCovering P) : Ψh.Trans Ψh' ≃ Ψh.FibTrans Ψh' where
  toFun := Ψh.fibredTransMap Ψh'
  invFun q := liftTrans hP q.1.1 q.1.2 q.2
  left_inv x := (eq_liftTrans hP x).symm
  right_inv _ := Subtype.ext (Prod.ext (transMap_liftTrans hP _ _ _) rfl)

@[simp] theorem transEquiv_apply (hP : IsFiniteToOneCovering P) (x : Ψh.Trans Ψh') :
    Ψh.transEquiv Ψh' hP x = Ψh.fibredTransMap Ψh' x := rfl

end CoveringUniformizer

/-! ### Definition 19.7.11 -/

/-- **2021 Definition 19.7.11, p. 910 (basic construction for `P`)**: a proper covering
uniformizer construction `F̂` (`hatU`) and a transition construction `𝓕` for the induced
uniformizer construction `F` of `B`, so that `(F, 𝓕)` is a basic construction for `B`. -/
structure CoveringBasicConstruction (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr) :
    Type (u + 1) where
  /-- The proper covering uniformizer construction `F̂`. -/
  hatU : CoveringUniformizerConstruction P
  /-- The transition construction `𝓕` for `F`. -/
  𝓕 : hatU.toUniformizerConstruction.TransitionConstruction

namespace CoveringBasicConstruction

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} (Bh : CoveringBasicConstruction P)

/-- **The underlying basic construction `(F, 𝓕)` for `B`** (Definition 19.7.11). -/
abbrev toBasic : B.BasicConstruction := ⟨Bh.hatU.toUniformizerConstruction, Bh.𝓕⟩

@[simp] theorem toBasic_U : Bh.toBasic.U = Bh.hatU.toUniformizerConstruction := rfl

/-- `F̂(β) ≠ ∅` on every isomorphism class (the standing assumption `F(α) ≠ ∅`, Theorem 19.2.2,
for `F̂`). -/
def HasClassUniformizers : Prop := ∀ z : B.OrbitSpace, ∃ β, B.π β = z ∧ (Bh.hatU.F β).Nonempty

theorem HasClassUniformizers.toBasic (h : Bh.HasClassUniformizers) :
    Bh.toBasic.U.HasClassUniformizers := fun z => by
  obtain ⟨β, hβ, Ψh, hΨh⟩ := h z
  exact ⟨β, hβ, Ψh.Ψ, Ψh, hΨh, rfl⟩

end CoveringBasicConstruction

end GroupoidalCategory

end Polyfold
