import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_37

/-! Round trip for V11_37 (2021 Definition 11.6.5, p. 554, and the diagram on p. 555; 2017:
Definition 11.7: natural transformations `(ζ, ξ) → (ζ', ξ')` of functors between proper
coverings, pairs `τ_Y`, `τ_X` with `τ_X ∘ F = F' ∘ τ_Y` (11.20)).

The item lists the definitions `ProperCoveringHom.NatTrans`, `NaturallyEquivalent`, `refl`,
`symm`, `trans`, `whiskerLeft`, `whiskerRight` (vocabulary) and five theorems; `A` is the
conjunction of their types, universes at `0`: `NatTrans.naturality_F` (the diagram on p. 555),
`naturallyEquivalent_equivalence`, `NaturallyEquivalent.comp_left`, `.comp_right`, and the
witness `naturallyEquivalent_pairToPointCovering` (no universes).

`B` says that `Γ.NatTrans Γ'` is exactly the set of pairs `(τ_Y, τ_X)` of `EpNatTrans` with
`τ_X(F(y)) = F'(τ_Y(y))`.

* The definitions agree: `B_holds` proves `B` outright from the structure `NatTrans` (its field
  `comm`, its constructor, and `cases`).  So `A_to_B` is `fun _ => B_holds` and does not use
  its hypothesis: none of `A`'s theorems is about the characterization.
* `B_to_A`: the witness from `B` (the pair `(1, 1)` satisfies (11.20) and so occurs).  The other
  four conjuncts are stated for arbitrary functors `F`, `F'` (not only proper coverings, which
  `B` assumes), so they are not consequences of `B`; they are general facts about the
  definitions and are re-proved outright (`naturality_F`: `F'` applied to the naturality square
  of `τ_Y`, with (11.20); the others from the vocabulary `refl`, `symm`, `trans`, `whiskerLeft`,
  `whiskerRight`). -/

namespace RoundTrip.V11_37
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.ProperCoveringHom.NatTrans.naturality_F.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.ProperCoveringHom.naturallyEquivalent_equivalence.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.ProperCoveringHom.NaturallyEquivalent.comp_left.{0, 0, 0, 0, 0, 0}) ∧
  (type_of% @Polyfold.ProperCoveringHom.NaturallyEquivalent.comp_right.{0, 0, 0, 0, 0, 0}) ∧
  (type_of% @Polyfold.CoveringEquivalence.Examples.naturallyEquivalent_pairToPointCovering)

theorem A_holds : A :=
  ⟨@Polyfold.ProperCoveringHom.NatTrans.naturality_F.{0, 0, 0, 0},
    @Polyfold.ProperCoveringHom.naturallyEquivalent_equivalence.{0, 0, 0, 0},
    @Polyfold.ProperCoveringHom.NaturallyEquivalent.comp_left.{0, 0, 0, 0, 0, 0},
    @Polyfold.ProperCoveringHom.NaturallyEquivalent.comp_right.{0, 0, 0, 0, 0, 0},
    @Polyfold.CoveringEquivalence.Examples.naturallyEquivalent_pairToPointCovering⟩

/-- `B` holds outright: the project's `NatTrans` is the text's notion by definition. -/
theorem B_holds : B := by
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjY' MorY' _ _ _ _ _ _
    ObjX' MorX' _ _ _ _ _ _ Y X Y' X' F F' _ _ Γ Γ'
  refine ⟨fun τ y => τ.comm y, fun τY τX h => ⟨⟨τY, τX, h⟩, rfl, rfl⟩, fun τ τ' h₁ h₂ => ?_⟩
  cases τ; cases τ'; cases h₁; cases h₂; rfl

/-- `A → B` (without its hypothesis: `B` is the definition). -/
theorem A_to_B : A → B := fun _ => B_holds

/-! ### Outright re-proofs of the general conjuncts (same binders as the project's) -/

section General

variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY' MorY' : Type} [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
  [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
  {ObjX' MorX' : Type} [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
  [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
  {ObjY'' MorY'' : Type} [TopologicalSpace ObjY''] [T2Space ObjY''] [ParacompactSpace ObjY'']
  [TopologicalSpace MorY''] [T2Space MorY''] [ParacompactSpace MorY'']
  {ObjX'' MorX'' : Type} [TopologicalSpace ObjX''] [T2Space ObjX''] [ParacompactSpace ObjX'']
  [TopologicalSpace MorX''] [T2Space MorX''] [ParacompactSpace MorX'']
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}
  {Y' : EpGroupoid ObjY' MorY'} {X' : EpGroupoid ObjX' MorX'}
  {Y'' : EpGroupoid ObjY'' MorY''} {X'' : EpGroupoid ObjX'' MorX''}
  {F : EpFunctor Y X} {F' : EpFunctor Y' X'} {F'' : EpFunctor Y'' X''}

/-- The diagram after Definition 11.6.5 (outright: `F'` applied to the naturality of `τ_Y`). -/
theorem naturality_F' {Γ Γ' : ProperCoveringHom F F'} (τ : Γ.NatTrans Γ') (ψ : MorY) :
    X'.comp (τ.τX.app (F.obj (Y.tgt ψ))) (Γ.Φ.mor (F.mor ψ)) =
      X'.comp (Γ'.Φ.mor (F.mor ψ)) (τ.τX.app (F.obj (Y.src ψ))) := by
  have h := congrArg F'.mor (τ.τY.naturality ψ)
  rw [F'.mor_comp _ _ (by rw [τ.τY.src_app, Γ.Ψ.tgt_mor]),
    F'.mor_comp _ _ (by rw [Γ'.Ψ.src_mor, τ.τY.tgt_app])] at h
  rw [τ.comm, τ.comm, Γ.comm_mor, Γ'.comm_mor]
  exact h

theorem naturallyEquivalent_equivalence' :
    Equivalence (ProperCoveringHom.NaturallyEquivalent (F := F) (F' := F')) :=
  ⟨fun Γ => ⟨ProperCoveringHom.NatTrans.refl Γ⟩, fun ⟨τ⟩ => ⟨τ.symm⟩,
    fun ⟨τ⟩ ⟨τ'⟩ => ⟨τ.trans τ'⟩⟩

theorem comp_left' {Γ Γ' : ProperCoveringHom F' F''} (h : Γ.NaturallyEquivalent Γ')
    (Λ : ProperCoveringHom F F') : (Γ.comp Λ).NaturallyEquivalent (Γ'.comp Λ) :=
  let ⟨τ⟩ := h
  ⟨τ.whiskerLeft Λ⟩

theorem comp_right' {Γ Γ' : ProperCoveringHom F F'} (h : Γ.NaturallyEquivalent Γ')
    (Λ : ProperCoveringHom F' F'') : (Λ.comp Γ).NaturallyEquivalent (Λ.comp Γ') :=
  let ⟨τ⟩ := h
  ⟨τ.whiskerRight Λ⟩

end General

open CoveringEquivalence.Examples EpGroupoid.Examples in
theorem B_to_A : B → A := by
  intro hB
  refine ⟨@naturality_F', @naturallyEquivalent_equivalence', @comp_left', @comp_right', ?_⟩
  -- the witness: `(1, 1)` satisfies (11.20), so by `B` it is a natural transformation
  obtain ⟨-, hex, -⟩ := hB _ _ _ _ _ _ _ _ pairEpGroupoid pairEpGroupoid pointEpGroupoid
    pointEpGroupoid (EpFunctor.id pairEpGroupoid) (EpFunctor.id pointEpGroupoid)
    EpFunctor.isProperCovering_id EpFunctor.isProperCovering_id
    pairToPointCovering pairToPointCovering
  obtain ⟨τ, -, -⟩ := hex (EpNatTrans.refl pairToPoint) (EpNatTrans.refl pairToPoint)
    (fun _ => rfl)
  exact ⟨τ⟩

#rt_check RoundTrip.V11_37.A_to_B [Polyfold.ProperCoveringHom.NatTrans.naturality_F,
  Polyfold.ProperCoveringHom.naturallyEquivalent_equivalence,
  Polyfold.ProperCoveringHom.NaturallyEquivalent.comp_left,
  Polyfold.ProperCoveringHom.NaturallyEquivalent.comp_right,
  Polyfold.CoveringEquivalence.Examples.naturallyEquivalent_pairToPointCovering]
#rt_check RoundTrip.V11_37.B_to_A [Polyfold.ProperCoveringHom.NatTrans.naturality_F,
  Polyfold.ProperCoveringHom.naturallyEquivalent_equivalence,
  Polyfold.ProperCoveringHom.NaturallyEquivalent.comp_left,
  Polyfold.ProperCoveringHom.NaturallyEquivalent.comp_right,
  Polyfold.CoveringEquivalence.Examples.naturallyEquivalent_pairToPointCovering]
#rt_overlap RoundTrip.V11_37.B_to_A [Polyfold.ProperCoveringHom.NatTrans.naturality_F,
  Polyfold.ProperCoveringHom.naturallyEquivalent_equivalence,
  Polyfold.ProperCoveringHom.NaturallyEquivalent.comp_left,
  Polyfold.ProperCoveringHom.NaturallyEquivalent.comp_right,
  Polyfold.CoveringEquivalence.Examples.naturallyEquivalent_pairToPointCovering]

end RoundTrip.V11_37
