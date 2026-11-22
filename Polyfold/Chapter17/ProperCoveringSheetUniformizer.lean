import Polyfold.Chapter17.ProperCoveringUniformizer

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8:
**Remark 17.8.11**, second part (p. 835): the restrictions of `Ψ̂` to `G_α ⋉ O_α`,
`α ∈ P⁻¹(β)`, are uniformizers.  Numbers and pages are the 2021 text's.

# The sheets of a proper covering uniformizer are uniformizers

## The text, paraphrased

(Remark 17.8.11) `Ψ : G ⋉ O_β → B` is a uniformizer in the usual sense, but `Ψ̂` is not: it is
defined on a special ep-groupoid.  "Note, however that the restrictions of `Ψ̂` to `G_α ⋉ O_α`
for `α ∈ P⁻¹(β)` are uniformizers."

## What is formalized

For a proper covering model `τ̂ : E → G ⋉ O` (Definition 17.8.4) and `y ∈ τ̂⁻¹(ō)`:
* `ProperCoveringModel.sheetIsotropyHom`: `G_y → G`, `φ ↦ g_φ`, an injective homomorphism
  (`injective_sheetIsotropyHom`); `G_y` acts on `O` through it (`sheetAction`).
* `ProperCoveringModel.sheetIncl` (connected model): the functor `G_y ⋉ O → E`,
  `o ↦ σ_y(o) = (τ̂|U(y))⁻¹(o)`, `(h, o) ↦` the morphism of `E` with source `σ_y(o)` over `g_h`
  (Lemma 17.8.9 gives its target `σ_y(g_h ∗ o)`).  It is fully faithful
  (`sheetIncl_full`, `sheetIncl_faithful`), injective on objects, with image `U(y)`
  (`range_sheetIncl_obj`), and `|G_y ⋉ O| → |E|` is an open embedding
  (`isOpenEmbedding_orbitMap_sheetIncl`).
* **Remark 17.8.11, second part**: `ProperCoveringUniformizer.sheetUniformizerAt`
  (`Ψ̂ ∘ sheetIncl`, a uniformizer of `A` in the sense of Definition 17.1.3, at `α = Ψ̂(y)`,
  centred there, with isotropy `G_y ≅ G_α`), `remark_17_8_11_two`.
* Witness: `remark_17_8_11_two_reflection`: the two-sheet uniformizer of `ℤˣ ⋉ ℝ` at `0`; both
  sheet uniformizers have the group `ℤ/2` acting non-trivially.

## Readings

* `O_α` is the sheet `U(y)`, `y ∈ τ̂⁻¹(ō)` the distinguished point over `α = Ψ̂(y)` (the
  construction (17.93)–(17.98)); we parametrize it by the sc-diffeomorphism `σ_y : O → U(y)`, so
  the uniformizer has the M-polyfold `O`.  `G_α` is the isotropy group `G_y` of `y` in `E`,
  isomorphic to `G_α` of `A` (Ψ̂ is fully faithful); it acts on `U(y)` by `φ ∗` (p. 834), which
  is `g_φ ∗` in the chart `τ̂`.
* We take the model connected (`hO_conn : U.model.Connected`, Definition 17.8.4's "connected"),
  the tacit setting of the remark: its notation `O_α`, `G_α ⋉ O_α` and the action `φ ∗` are those
  of pp. 832–834, which begin "Suppose further that `O` is connected" and use it in Lemmas 17.8.8
  and 17.8.9; Proposition 17.8.6 shrinks any model to a connected one.  Without it, a morphism of
  `E` leaving `U(y)` may lie over an element of the image of `G_y` (Lemma 17.8.9 is about the
  component `𝐄^φ`), and the full subgroupoid on `U(y)` need not be a translation groupoid of
  `G_y` (`remark_17_8_11_two_disconnected`, `ProperCoveringSheetCounterexample.lean`).
* "Uniformizer" is Definition 17.1.3 (`GCT.LocalUniformizer`): the orbit map is an open embedding;
  this uses that `|P|` is continuous (Definition 17.8.1 (1)).
-/

open Set Function Topology

noncomputable section

namespace Polyfold

open EpGroupoid EpGroupoid.Examples

universe u

/-! ### The sheet functor `G_y ⋉ O → E` -/

section Model

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {P : MPolyfold O} {hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y}
  {ObjE MorE : Type u} [TopologicalSpace ObjE] [T2Space ObjE] [ParacompactSpace ObjE]
  [TopologicalSpace MorE] [T2Space MorE] [ParacompactSpace MorE] {E : EpGroupoid ObjE MorE}
  {τ : EpFunctor E (actionEpGroupoid hP)}

namespace ProperCoveringModel

variable (M : ProperCoveringModel τ) (y : ObjE)

/-- An element of `G_y` with `y ∈ τ̂⁻¹(ō)` is a morphism of `𝐀_ō`. -/
theorem isotropy_mem_morOn {y : ObjE} (hy : y ∈ M.fiber) (h : E.Isotropy y) :
    h.val ∈ E.morOn M.fiber :=
  ⟨by rw [h.src_val]; exact hy, by rw [h.tgt_val]; exact hy⟩

/-- `G_y → G`, `φ ↦ g_φ` (p. 832). -/
def sheetIsotropyHom : E.Isotropy y →* G where
  toFun h := M.groupIndex h.val
  map_one' := M.groupIndex_unit y
  map_mul' a b := M.groupIndex_comp (a.src_val.trans b.tgt_val.symm)

@[simp] theorem sheetIsotropyHom_apply (h : E.Isotropy y) :
    M.sheetIsotropyHom y h = M.groupIndex h.val := rfl

/-- `φ ↦ g_φ` is injective on `G_y`: a morphism is determined by `g_φ` and its source. -/
theorem injective_sheetIsotropyHom : Injective (M.sheetIsotropyHom y) := fun a b h =>
  GroupoidStr.Isotropy.ext (M.eq_of_groupIndex_eq h (a.src_val.trans b.src_val.symm))

/-- `G_y` acts on `O` through `φ ↦ g_φ`. -/
abbrev sheetAction : MulAction (E.Isotropy y) O := MulAction.compHom O (M.sheetIsotropyHom y)

/-- The translation groupoid `G_y ⋉ O`. -/
abbrev sheetGroupoid : GroupoidStr O (E.Isotropy y × O) :=
  @GroupoidStr.translation (E.Isotropy y) O _ (M.sheetAction y)

theorem sheetGroupoid_tgt (p : E.Isotropy y × O) :
    (M.sheetGroupoid y).tgt p = M.groupIndex p.1.val • p.2 := rfl

variable {y}

/-- **Lemma 17.8.9 on the sheet `U(y)`**: for a connected model, the morphism over `g_h`,
`h ∈ G_y`, with source `σ_y(o)` has target `σ_y(g_h ∗ o)`. -/
theorem tgt_liftMor_σ (hO : M.Connected) (hy : y ∈ M.fiber) (h : E.Isotropy y) (o : O) :
    E.tgt (M.liftMor (M.groupIndex h.val) (M.σ y o)) = M.σ y (M.groupIndex h.val • o) := by
  set ψ := M.liftMor (M.groupIndex h.val) (M.σ y o)
  have hb : M.baseMor ψ = h.val := by
    have h1 := M.liftMor_eq h.val
    rw [h.src_val] at h1
    rw [baseMor, M.groupIndex_liftMor, M.src_liftMor, M.sheetIndex_σ hy]
    exact h1
  have hmem := M.mem_connectedComponent_baseMor hO ψ
  rw [hb] at hmem
  rw [M.lemma_17_8_9 (M.isotropy_mem_morOn hy h) hmem, h.tgt_val, M.src_liftMor, M.obj_σ hy]

/-- **The sheet functor `G_y ⋉ O → E`** (connected model): `o ↦ σ_y(o)`,
`(h, o) ↦` the morphism over `g_h` with source `σ_y(o)`. -/
def sheetIncl (hO : M.Connected) (hy : y ∈ M.fiber) :
    GroupoidFunctor (M.sheetGroupoid y) E.toGroupoidStr where
  obj o := M.σ y o
  mor p := M.liftMor (M.groupIndex p.1.val) (M.σ y p.2)
  src_mor p := M.src_liftMor _ _
  tgt_mor p := M.tgt_liftMor_σ hO hy p.1 p.2
  mor_comp p q hpq := by
    refine M.eq_of_groupIndex_eq ?_ ?_
    · have hs : E.src (M.liftMor (M.groupIndex p.1.val) (M.σ y p.2)) =
          E.tgt (M.liftMor (M.groupIndex q.1.val) (M.σ y q.2)) := by
        rw [M.src_liftMor, M.tgt_liftMor_σ hO hy]
        exact congrArg (M.σ y) hpq
      change M.groupIndex (M.liftMor (M.groupIndex (E.comp p.1.val q.1.val)) (M.σ y q.2)) =
        M.groupIndex (E.comp _ _)
      rw [M.groupIndex_comp hs, M.groupIndex_liftMor, M.groupIndex_liftMor, M.groupIndex_liftMor,
        M.groupIndex_comp (p.1.src_val.trans q.1.tgt_val.symm)]
    · have hs : E.src (M.liftMor (M.groupIndex p.1.val) (M.σ y p.2)) =
          E.tgt (M.liftMor (M.groupIndex q.1.val) (M.σ y q.2)) := by
        rw [M.src_liftMor, M.tgt_liftMor_σ hO hy]
        exact congrArg (M.σ y) hpq
      change E.src (M.liftMor _ (M.σ y q.2)) = _
      rw [M.src_liftMor, E.src_comp _ _ hs, M.src_liftMor]
  mor_unit o := by
    refine M.eq_of_groupIndex_eq ?_ ?_
    · change M.groupIndex (M.liftMor (M.groupIndex (E.unit y)) (M.σ y o)) = _
      rw [M.groupIndex_liftMor, M.groupIndex_unit, M.groupIndex_unit]
    · change E.src (M.liftMor _ (M.σ y o)) = _
      rw [M.src_liftMor, E.src_unit]

variable (hO : M.Connected) (hy : y ∈ M.fiber)
include hO hy

@[simp] theorem sheetIncl_obj (o : O) : (M.sheetIncl hO hy).obj o = M.σ y o := rfl

theorem sheetIncl_mor (p : E.Isotropy y × O) :
    (M.sheetIncl hO hy).mor p = M.liftMor (M.groupIndex p.1.val) (M.σ y p.2) := rfl

/-- The objects of `G_y ⋉ O` go injectively onto the sheet `U(y)`. -/
theorem injective_sheetIncl_obj : Injective (M.sheetIncl hO hy).obj := fun o o' h => by
  rw [← M.obj_σ hy o, ← M.obj_σ hy o']
  exact congrArg τ.obj h

theorem range_sheetIncl_obj : range (M.sheetIncl hO hy).obj = M.U y := by
  ext e
  constructor
  · rintro ⟨o, rfl⟩
    exact M.σ_mem_U hy o
  · intro he
    exact ⟨τ.obj e, M.σ_obj hy he⟩

/-- A morphism of `E` between two points of `U(y)` lies over an element of `G_y`. -/
theorem exists_isotropy_of_mor (ψ : MorE) {o o' : O} (hs : E.src ψ = M.σ y o)
    (ht : E.tgt ψ = M.σ y o') :
    ∃ h : E.Isotropy y, M.groupIndex h.val = M.groupIndex ψ ∧ M.groupIndex h.val • o = o' := by
  have hb := M.mem_connectedComponent_baseMor hO ψ
  obtain ⟨-, ht', -⟩ := M.constant_on_component hb
  have hsb : E.src (M.baseMor ψ) = y := by
    rw [baseMor, M.src_liftMor, hs, M.sheetIndex_σ hy]
  have htb : E.tgt (M.baseMor ψ) = y := by
    rw [← M.sheetIndex_of_mem_fiber (M.baseMor_mem ψ).2, ← ht', ht, M.sheetIndex_σ hy]
  refine ⟨⟨M.baseMor ψ, hsb, htb⟩, M.groupIndex_liftMor _ _, ?_⟩
  change M.groupIndex (M.baseMor ψ) • o = o'
  rw [baseMor, M.groupIndex_liftMor, ← M.obj_σ hy o, ← hs, ← M.obj_tgt, ht, M.obj_σ hy]

/-- `G_y ⋉ O → E` is full. -/
theorem sheetIncl_full : (M.sheetIncl hO hy).toFunctor.Full := by
  refine (GroupoidFunctor.full_iff _).2 fun o o' ψ hs ht => ?_
  obtain ⟨h, hg, hh⟩ := M.exists_isotropy_of_mor hO hy ψ hs ht
  refine ⟨(h, o), rfl, hh, ?_⟩
  change M.liftMor (M.groupIndex h.val) (M.σ y o) = ψ
  rw [hg, show M.σ y o = E.src ψ from hs.symm]
  exact M.liftMor_eq ψ

/-- `G_y ⋉ O → E` is faithful. -/
theorem sheetIncl_faithful : (M.sheetIncl hO hy).toFunctor.Faithful := by
  refine (GroupoidFunctor.faithful_iff _).2 fun p p' hs _ he => ?_
  have hs' : p.2 = p'.2 := hs
  have hg := congrArg M.groupIndex he
  rw [sheetIncl_mor, sheetIncl_mor, M.groupIndex_liftMor, M.groupIndex_liftMor] at hg
  exact Prod.ext (M.injective_sheetIsotropyHom y hg) hs'

omit hO in
/-- `σ_y` maps open sets to open sets: `σ_y(W) = U(y) ∩ τ̂⁻¹(W)`. -/
theorem isOpenMap_σ : IsOpenMap (M.σ y) := by
  intro W hW
  have heq : M.σ y '' W = M.U y ∩ τ.obj ⁻¹' W := by
    ext e
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨M.σ_mem_U hy o, by rw [mem_preimage, M.obj_σ hy]; exact ho⟩
    · rintro ⟨he, hW'⟩
      exact ⟨τ.obj e, hW', M.σ_obj hy he⟩
  rw [heq]
  exact (M.isOpen_U hy).inter
    (hW.preimage (continuousOn_univ.1 τ.isScSmoothMap_obj.continuousOn))

/-- **`|G_y ⋉ O| → |E|` is an open embedding**: continuous, open (`σ_y` and `π_E` are open), and
injective (two points of `U(y)` in one orbit of `E` are in one orbit of `G_y`). -/
theorem isOpenEmbedding_orbitMap_sheetIncl :
    IsOpenEmbedding (M.sheetIncl hO hy).orbitMap := by
  have hc : ∀ h : E.Isotropy y, Continuous fun o : O => (M.sheetIsotropyHom y h) • o :=
    fun h => continuousOn_univ.1 (hP _).continuousOn
  have hπ : IsOpenMap (M.sheetGroupoid y).π := by
    let := M.sheetAction y
    exact GroupoidStr.isOpenMap_π_translation hc
  have hcomp : (M.sheetIncl hO hy).orbitMap ∘ (M.sheetGroupoid y).π = E.π ∘ M.σ y := rfl
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · refine continuous_quot_lift _ ?_
    exact E.continuous_π.comp (M.continuous_σ hy)
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h o =>
    induction b using Quotient.inductionOn with
    | h o' =>
    obtain ⟨ψ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hab
    obtain ⟨h, -, hh⟩ := M.exists_isotropy_of_mor hO hy ψ hs ht
    exact (GroupoidStr.π_eq_π_iff _).2 ⟨(h, o), rfl, hh⟩
  · intro W hW
    have hW' : IsOpen ((M.sheetGroupoid y).π ⁻¹' W) := hW
    have heq : (M.sheetIncl hO hy).orbitMap '' W =
        E.π '' (M.σ y '' ((M.sheetGroupoid y).π ⁻¹' W)) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        induction w using Quotient.inductionOn with
        | h o => exact ⟨M.σ y o, ⟨o, hw, rfl⟩, rfl⟩
      · rintro ⟨e, ⟨o, ho, rfl⟩, rfl⟩
        exact ⟨_, ho, rfl⟩
    rw [heq]
    exact E.proposition_7_1_8 _ (M.isOpenMap_σ hy _ hW')

end ProperCoveringModel

end Model

/-! ### Remark 17.8.11, second part -/

namespace ProperCoveringUniformizer

variable {A B : GCT.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} {β : B.Obj}
  (U : ProperCoveringUniformizer P β)

/-- **Remark 17.8.11, second part** (p. 835): for a connected model (`hO_conn`) and a
distinguished point `y ∈ τ̂⁻¹(o_β)` over `α = Ψ̂(y) ∈ P⁻¹(β)`, the restriction of `Ψ̂` to the
sheet, `Ψ̂ ∘ sheetIncl : G_y ⋉ O → A`, is a uniformizer (Definition 17.1.3, without the
topological condition). -/
def sheetUniformizerAt (hO_conn : U.model.Connected) {y : U.ObjE} (hy : y ∈ U.model.fiber) :
    A.toGroupoidalCategory.Uniformizer where
  O := U.Ψ.O
  P := U.Ψ.P
  G := U.E.Isotropy y
  fin := Finite.of_injective _ (U.model.injective_sheetIsotropyHom y)
  topG := ⊥
  discG := @DiscreteTopology.mk _ ⊥ rfl
  act := U.model.sheetAction y
  smooth_smul h := U.Ψ.smooth_smul (U.model.sheetIsotropyHom y h)
  functor := U.hat.comp (U.model.sheetIncl hO_conn hy)
  injective_obj := U.injective_hat.comp (U.model.injective_sheetIncl_obj hO_conn hy)
  full := by
    have h1 := (GroupoidFunctor.full_iff _).1 U.full_hat
    have h2 := (GroupoidFunctor.full_iff _).1 (U.model.sheetIncl_full hO_conn hy)
    refine (GroupoidFunctor.full_iff _).2 fun o o' ψ hs ht => ?_
    obtain ⟨φ, hφs, hφt, rfl⟩ := h1 _ _ ψ hs ht
    obtain ⟨p, hps, hpt, rfl⟩ := h2 o o' φ hφs hφt
    exact ⟨p, hps, hpt, rfl⟩
  faithful := by
    have h1 := (GroupoidFunctor.faithful_iff _).1 U.faithful_hat
    have h2 := (GroupoidFunctor.faithful_iff _).1 (U.model.sheetIncl_faithful hO_conn hy)
    refine (GroupoidFunctor.faithful_iff _).2 fun p p' hs ht he => h2 p p' hs ht (h1 _ _ ?_ ?_ he)
    · rw [(U.model.sheetIncl hO_conn hy).src_mor, (U.model.sheetIncl hO_conn hy).src_mor]
      exact congrArg _ hs
    · rw [(U.model.sheetIncl hO_conn hy).tgt_mor, (U.model.sheetIncl hO_conn hy).tgt_mor]
      exact congrArg _ ht

variable (hO_conn : U.model.Connected) {y : U.ObjE} (hy : y ∈ U.model.fiber)

theorem sheetUniformizerAt_obj (o : U.Ψ.O) :
    (U.sheetUniformizerAt hO_conn hy).functor.obj o = U.hat.obj (U.model.σ y o) := rfl

/-- The sheet uniformizer is centred at `α = Ψ̂(y)`: `o_β ↦ Ψ̂(y)`, and `o_β` is fixed by `G_y`. -/
theorem sheetUniformizerAt_isCentredAt :
    (U.sheetUniformizerAt hO_conn hy).IsCentredAt (U.hat.obj y) := by
  refine ⟨U.model.pt, ?_, fun h => ?_⟩
  · change U.hat.obj (U.model.σ y U.model.pt) = _
    rw [U.model.σ_pt hy]
  · change U.model.sheetIsotropyHom y h • U.model.pt = U.model.pt
    exact U.model.smul_pt _

/-- The image of the sheet uniformizer on objects is `Ψ̂(U(y))`. -/
theorem range_sheetUniformizerAt_obj :
    range (U.sheetUniformizerAt hO_conn hy).functor.obj = U.hat.obj '' U.model.U y := by
  rw [← U.model.range_sheetIncl_obj hO_conn hy, ← range_comp]
  rfl

/-- `|Ψ̂ ∘ ι| = |Ψ̂| ∘ |ι|` for the sheet functor `ι`. -/
theorem orbitMap_sheetUniformizerAt :
    (U.sheetUniformizerAt hO_conn hy).functor.orbitMap =
      U.hat.orbitMap ∘ (U.model.sheetIncl hO_conn hy).orbitMap := by
  funext q
  induction q using Quotient.inductionOn with
  | h o => rfl

/-- `|Ψ̂| : |E| → |A|` is an open embedding (Definition 17.8.10 (4), with `|P|` continuous). -/
theorem isOpenEmbedding_hat_orbitMap (hPc : P.IsProperCoveringGCT) :
    IsOpenEmbedding U.hat.orbitMap := by
  obtain ⟨V, hV, -, -, -, he, hr⟩ := U.orbit_homeomorph
  exact ⟨he, hr ▸ hV.preimage hPc.continuous_orbitMap⟩

/-- **Remark 17.8.11, second part, as uniformizers of the GCT `A`** (Definition 17.1.3): for a
proper covering functor `P` and a connected model, the restriction of `Ψ̂` to each sheet is a
local uniformizer of `A`: `|G_y ⋉ O| → |E| → |A|` is a composite of open embeddings. -/
def sheetLocalUniformizerAt (hPc : P.IsProperCoveringGCT) : A.LocalUniformizer :=
  { U.sheetUniformizerAt hO_conn hy with
    isOpenEmbedding_orbitMap := by
      rw [U.orbitMap_sheetUniformizerAt hO_conn hy]
      exact (U.isOpenEmbedding_hat_orbitMap hPc).comp
        (U.model.isOpenEmbedding_orbitMap_sheetIncl hO_conn hy) }

include hO_conn in
/-- **Remark 17.8.11, second part**: at every `α ∈ P⁻¹(β)` (i.e. `α = Ψ̂(y)` for a distinguished
point `y`, Definition 17.8.10 (1)) the restriction of `Ψ̂` to the sheet is a local uniformizer
of `A` centred at `α`, with image `Ψ̂(U(y))` on objects and group `G_y`. -/
theorem remark_17_8_11_two (hPc : P.IsProperCoveringGCT) {α : A.Obj} (hα : P.obj α = β) :
    ∃ y ∈ U.model.fiber, U.hat.obj y = α ∧
      ∃ Φ : A.LocalUniformizer, Φ.toUniformizer.IsCentredAt α ∧
        range Φ.functor.obj = U.hat.obj '' U.model.U y ∧ Φ.G = U.E.Isotropy y := by
  obtain ⟨y, hy, rfl⟩ := U.bijOn_fiber.surjOn hα
  exact ⟨y, hy, rfl, U.sheetLocalUniformizerAt hO_conn hy hPc,
    U.sheetUniformizerAt_isCentredAt hO_conn hy, U.range_sheetUniformizerAt_obj hO_conn hy, rfl⟩

end ProperCoveringUniformizer

/-! ### Witness -/

section Witness

attribute [local instance] instMulActionUnitsBool'

/-- **Witness for Remark 17.8.11, second part**: the two-sheet uniformizer of `ℤˣ ⋉ ℝ` at `0`
(over a proper covering functor of GCTs) has a connected model (`hO_conn`: `O = ℝ`), and at each of
the two distinguished points the sheet uniformizer has `G_y ≅ ℤ/2` acting non-trivially
(`-1` reflects `ℝ`). -/
theorem remark_17_8_11_two_reflection :
    ∃ (hPc : (sheetGCTFunctor isScSmoothMap_units_smul Bool).IsProperCoveringGCT)
      (hO_conn : reflectionSheetUniformizer.model.Connected),
      reflectionSheetUniformizer.model.fiber.ncard = 2 ∧
      ∀ (y) (hy : y ∈ reflectionSheetUniformizer.model.fiber),
        ∃ (h : (reflectionSheetUniformizer.sheetLocalUniformizerAt hO_conn hy hPc).G)
          (x : (reflectionSheetUniformizer.sheetLocalUniformizerAt hO_conn hy hPc).O),
          h • x ≠ x := by
  obtain ⟨hPc, h2, -⟩ := reflectionSheetUniformizer_nondegenerate
  have hO : reflectionSheetUniformizer.model.Connected := by
    change ConnectedSpace (Fin 1 → ℝ)
    infer_instance
  refine ⟨hPc, hO, h2, fun y hy => ?_⟩
  have hy0 : y.2 = 0 := hy
  have ht : reflectionSheetUniformizer.E.tgt ((-1 : ℤˣ), y) = y := by
    refine Prod.ext rfl ?_
    change (-1 : ℤˣ) • y.2 = y.2
    rw [hy0, units_smul_zero_rn]
  refine ⟨⟨((-1 : ℤˣ), y), rfl, ht⟩, (fun _ => 1 : Fin 1 → ℝ), fun h => ?_⟩
  have := congrFun h 0
  change ((-1 : ℤˣ) • (fun _ => 1 : Fin 1 → ℝ)) 0 = 1 at this
  norm_num [Units.smul_def] at this

end Witness

end Polyfold
