import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_39

set_option maxSynthPendingDepth 3

/-!
Round trip for V11_39 (Theorem 11.6.6, all claims, with steps (D)–(F); 2021 p. 555, pp. 560–561).

The item lists the definitions `projLeftHom`, `projRightHom`, `natTransProj` (vocabulary) and five
theorems.  `A` is the conjunction of their types, universes at `0`: `theorem_11_6_6` (all claims
for `H = hFunctor`, `(π_Y, π_X) = projLeftHom`, `(π_{Y''}, π_{X''}) = projRightHom`), the witness
`theorem_11_6_6_pairToPoint`, the witness `nonempty_fiber_id`, Chapter 10's
`WeakFibredProduct.isEquivalence_projRight` (for an equivalence `F` and any `G` with an admissible
weak fibred product, `πZ : X ×_Y Z → Z` is an equivalence) and Chapter 7's
`MPolyfold.IsLocalScDiffeo.isTame` (tameness pulls back along local sc-diffeomorphisms).

`B`: for proper coverings `F, F', F''`, an equivalence `Γ : F → F'` and `Λ : F'' → F'`, there are
`H` of (11.18), (11.19), a proper covering, and `πR`, `πL` with the projection entries, with `πR`
an equivalence, `Γ ∘ πL ≃ Λ ∘ πR` (pairs of `EpNatTrans` with (11.20)), `Λ` equivalence ⇒ `πL`
equivalence; and `X''` tame ⇒ `P`, `Q` tame.

* `A ⇒ B` (`A_to_B`): `H := hFunctor`, `πR := projRightHom`, `πL := projLeftHom` (entries by
  `rfl`), the rest from `theorem_11_6_6` (the project's `NatTrans` is `B`'s pair with (11.20)).
* `B ⇒ A` (`B_to_A`): `theorem_11_6_6` from `B`, after identifying `B`'s `H`, `πR`, `πL` with
  `hFunctor`, `projRightHom`, `projLeftHom` (`EpFunctor.ext`, `ProperCoveringHom.ext`);
  `theorem_11_6_6_pairToPoint` from `B` applied to `pairToPointCovering` and the identity of the
  point (its `Nonempty` half is the explicit object `(0, (), ())`); `isEquivalence_projRight`
  from `B`'s (2) applied to identity coverings `1_X, 1_Y, 1_Z` and `Γ = (F, F)`, `Λ = (G, G)`;
  `nonempty_fiber_id` and `IsLocalScDiffeo.isTame` are not about Theorem 11.6.6 and are re-proved
  outright (one line each; the latter by copying the project's proof from non-item lemmas).
-/

namespace RoundTrip.V11_39
open Polyfold

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.ProperCoveringHom.theorem_11_6_6.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.CoveringEquivalence.Examples.theorem_11_6_6_pairToPoint ∧
  type_of% @Polyfold.CoveringEquivalence.Examples.nonempty_fiber_id ∧
  type_of% @Polyfold.WeakFibredProduct.isEquivalence_projRight.{0, 0, 0} ∧
  type_of% @Polyfold.MPolyfold.IsLocalScDiffeo.isTame.{0, 0}

theorem A_holds : A :=
  ⟨@ProperCoveringHom.theorem_11_6_6, CoveringEquivalence.Examples.theorem_11_6_6_pairToPoint,
    CoveringEquivalence.Examples.nonempty_fiber_id, @WeakFibredProduct.isEquivalence_projRight,
    @MPolyfold.IsLocalScDiffeo.isTame⟩

theorem A_to_B (hA : A) : B := by
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjY' MorY' _ _ _ _ _ _
    ObjX' MorX' _ _ _ _ _ _ ObjY'' MorY'' _ _ _ _ _ _ ObjX'' MorX'' _ _ _ _ _ _
    Y X Y' X' Y'' X'' F F' F'' hF hF' hF'' Γ hΓ Λ
  obtain ⟨hmain, -⟩ := hA
  obtain ⟨hH, hR, ⟨τ⟩, hT, hL⟩ := hmain Γ Λ hF hF' hF'' hΓ
  exact ⟨⟨_, ⟨fun o => ⟨rfl, rfl, rfl⟩, fun m => ⟨rfl, rfl, rfl⟩⟩, hH, _, _,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    hR, ⟨τ.τY, τ.τX, τ.comm⟩, hL⟩, hT⟩

section
variable {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY}

/-- `(f, f) : 1_X → 1_Y`, a functor between the identity coverings. -/
def idHom (f : EpFunctor X Y) : ProperCoveringHom (EpFunctor.id X) (EpFunctor.id Y) :=
  ⟨f, f, fun _ => rfl, fun _ => rfl⟩

end

theorem B_to_A (hB : B) : A := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Theorem 11.6.6
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjY' MorY' _ _ _ _ _ _
      ObjX' MorX' _ _ _ _ _ _ ObjY'' MorY'' _ _ _ _ _ _ ObjX'' MorX'' _ _ _ _ _ _
      Y X Y' X' Y'' X'' F F' F'' Γ Λ hF hF' hF'' hΓ
    obtain ⟨⟨H, ⟨hHo, hHm⟩, hHpc, πR, πL, h1, h2, h3, h4, h5, h6, h7, h8, hR, ⟨τY, τX, hτ⟩, hL⟩,
      hT⟩ := hB ObjY MorY ObjX MorX ObjY' MorY' ObjX' MorX' ObjY'' MorY'' ObjX'' MorX''
        Y X Y' X' Y'' X'' F F' F'' hF hF' hF'' Γ hΓ Λ
    have eH : H = ProperCoveringHom.hFunctor Γ Λ
        (.of_isEquivalence_left hΓ.isEquivalence_Ψ) (.of_isEquivalence_left hΓ.isEquivalence_Φ) :=
      EpFunctor.ext
        (funext fun o => WeakFibredProduct.Obj.ext (hHo o).1 (hHo o).2.1 (hHo o).2.2)
        (funext fun m => WeakFibredProduct.Mor.ext (hHm m).1 (hHm m).2.1 (hHm m).2.2)
    subst eH
    have eR : πR = ProperCoveringHom.projRightHom Γ Λ
        (.of_isEquivalence_left hΓ.isEquivalence_Ψ) (.of_isEquivalence_left hΓ.isEquivalence_Φ) :=
      ProperCoveringHom.ext (EpFunctor.ext (funext h1) (funext h2))
        (EpFunctor.ext (funext h3) (funext h4))
    have eL : πL = ProperCoveringHom.projLeftHom Γ Λ
        (.of_isEquivalence_left hΓ.isEquivalence_Ψ) (.of_isEquivalence_left hΓ.isEquivalence_Φ) :=
      ProperCoveringHom.ext (EpFunctor.ext (funext h5) (funext h6))
        (EpFunctor.ext (funext h7) (funext h8))
    subst eR eL
    exact ⟨hHpc, hR, ⟨⟨τY, τX, hτ⟩⟩, hT, hL⟩
  · -- the witness `theorem_11_6_6_pairToPoint`
    open EpGroupoid.Examples CoveringEquivalence.Examples in
    obtain ⟨⟨H, ⟨hHo, hHm⟩, hHpc, -⟩, -⟩ := hB ℤ (ℤ × ℤ) ℤ (ℤ × ℤ) Unit Unit Unit Unit Unit Unit
      Unit Unit pairEpGroupoid pairEpGroupoid pointEpGroupoid pointEpGroupoid pointEpGroupoid
      pointEpGroupoid (EpFunctor.id _) (EpFunctor.id _) (EpFunctor.id _)
      EpFunctor.isProperCovering_id EpFunctor.isProperCovering_id EpFunctor.isProperCovering_id
      pairToPointCovering isEquivalence_pairToPointCovering
      (ProperCoveringHom.id (EpFunctor.id pointEpGroupoid))
    refine ⟨⟨WeakFibredProduct.Obj.mk _ _ (0 : ℤ) () () rfl rfl⟩, ?_⟩
    have eH : H = ProperCoveringHom.hFunctor pairToPointCovering
        (ProperCoveringHom.id (EpFunctor.id pointEpGroupoid))
        (.of_isEquivalence_left isEquivalence_pairToPoint)
        (.of_isEquivalence_left isEquivalence_pairToPoint) :=
      EpFunctor.ext
        (funext fun o => WeakFibredProduct.Obj.ext (hHo o).1 (hHo o).2.1 (hHo o).2.2)
        (funext fun m => WeakFibredProduct.Mor.ext (hHm m).1 (hHm m).2.1 (hHm m).2.2)
    subst eH
    exact hHpc
  · -- the witness `nonempty_fiber_id` (not about Theorem 11.6.6; outright)
    exact fun x => ⟨EpFunctor.IsProperCovering.Fiber.mk x rfl⟩
  · -- `isEquivalence_projRight`, from `B` (2) for identity coverings
    intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G hF h
    have hΓ : (idHom (Y := Y) F).IsEquivalence :=
      (ProperCoveringHom.isEquivalence_iff EpFunctor.isProperCovering_id
        EpFunctor.isProperCovering_id _).2 ⟨hF, hF⟩
    obtain ⟨⟨_H, -, -, πR, _πL, h1, h2, -, -, -, -, -, -, hR, -⟩, -⟩ := hB ObjX MorX ObjX MorX
      ObjY MorY ObjY MorY ObjZ MorZ ObjZ MorZ X X Y Y Z Z (EpFunctor.id X) (EpFunctor.id Y)
      (EpFunctor.id Z) EpFunctor.isProperCovering_id EpFunctor.isProperCovering_id
      EpFunctor.isProperCovering_id (idHom F) hΓ (idHom G)
    have e : πR.Ψ = WeakFibredProduct.projRight F G h := EpFunctor.ext (funext h1) (funext h2)
    rw [← e]
    exact hR.isEquivalence_Ψ
  · -- `IsLocalScDiffeo.isTame` (Chapter 7; outright, the project's proof)
    intro M _ _ _ N _ _ _ P Q f hf hQ
    exact MPolyfold.isTame_of_forall_exists_chart _ fun x => by
      obtain ⟨U, V, g, hx, hd⟩ := hf x
      exact hd.exists_tame_chart hQ hx

#rt_check RoundTrip.V11_39.A_to_B [Polyfold.ProperCoveringHom.theorem_11_6_6,
  Polyfold.CoveringEquivalence.Examples.theorem_11_6_6_pairToPoint,
  Polyfold.CoveringEquivalence.Examples.nonempty_fiber_id,
  Polyfold.WeakFibredProduct.isEquivalence_projRight, Polyfold.MPolyfold.IsLocalScDiffeo.isTame]
#rt_check RoundTrip.V11_39.B_to_A [Polyfold.ProperCoveringHom.theorem_11_6_6,
  Polyfold.CoveringEquivalence.Examples.theorem_11_6_6_pairToPoint,
  Polyfold.CoveringEquivalence.Examples.nonempty_fiber_id,
  Polyfold.WeakFibredProduct.isEquivalence_projRight, Polyfold.MPolyfold.IsLocalScDiffeo.isTame]
#rt_overlap RoundTrip.V11_39.B_to_A [Polyfold.ProperCoveringHom.theorem_11_6_6,
  Polyfold.CoveringEquivalence.Examples.theorem_11_6_6_pairToPoint,
  Polyfold.CoveringEquivalence.Examples.nonempty_fiber_id,
  Polyfold.WeakFibredProduct.isEquivalence_projRight, Polyfold.MPolyfold.IsLocalScDiffeo.isTame]

end RoundTrip.V11_39
