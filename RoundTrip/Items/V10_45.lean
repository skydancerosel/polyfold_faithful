import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_45

/-! Round trip for V10_45 (2021 Theorem 10.3.14, p. 491; 2017: Theorem 10.5, p. 354): the
localization functor `i : EP → EP(E⁻¹)`.

The item lists three definitions (`Diagram.ofFunctor`, `EPLoc.localizationFunctor`,
`Examples.pairToPointEP`; vocabulary) and ten theorems; `A` is the conjunction of their types,
universes at `0` (`B` lives in `Type`; the `Examples` have no universe parameters):
`Diagram.isRefinement_ofFunctor_comp` (the composite of `d_Φ`, `d_Ψ` refines `d_{Ψ∘Φ}`),
`localizationFunctor_obj`, `localizationFunctor_map`, `theorem_10_3_14` (identity on objects,
`i(Φ) = [X ←1 X →Φ Y]`, `i(F)` a generalized isomorphism with inverse `[Y ←F X →1 X]` for an
equivalence `F`), `isInvertedBy_localizationFunctor` (Mathlib's `IsInvertedBy` for
`EP.equivalences`), `inv_localizationFunctor_map`, `homMk_eq` (`[X ←F A →Φ Y] = i(Φ) ∘ i(F)⁻¹`),
and the witnesses `not_isIso_pairToPointEP`, `isGeneralizedIso_pairToPoint`,
`inv_localizationFunctor_map_pairToPoint`.

`B` says: `Φ ↦ iB Φ = [X ←1 X →Φ Y]` (the project's `Diagram.ofFunctor`) preserves identities and
composition (stated elementarily), and `iB F` is an isomorphism of `EPLoc` for every
equivalence `F`.

* `A_to_B`: identities by `rfl`; composition from `isRefinement_ofFunctor_comp` (a refinement
  gives equal classes); invertibility from `isInvertedBy_localizationFunctor`.
* `B_to_A`: `isInvertedBy_localizationFunctor`, the `IsGeneralizedIso` part of
  `theorem_10_3_14` and of the witness come from `B`'s third part; `obj`/`map` are `rfl`.  The
  rest is not a consequence of `B` and is re-proved outright from non-item lemmas:
  `isRefinement_ofFunctor_comp` is a statement about representatives (`B` only speaks of
  classes); the inverse formula `i(F)⁻¹ = [Y ←F X →1 X]` (in `theorem_10_3_14`,
  `inv_localizationFunctor_map` and the witness) comes from `Diagram.equiv_comp_symm` /
  `theorem_10_3_10` (Theorem 10.3.10), not stated in `B` (the text's statement only says that
  `i(F)` is invertible); `homMk_eq` is the project's refinement by `πA`; and
  `not_isIso_pairToPointEP` is a fact about `EP`.

**The no-peeking check.**  The statements of `homMk_eq`, `inv_localizationFunctor_map` and the
last witness contain the banned `isInvertedBy_localizationFunctor` (as the `IsIso` instance of
`inv`), and every statement mentioning `localizationFunctor` reaches the banned
`isRefinement_ofFunctor_comp` through its field `map_comp`.  As in V8_4, both directions are
proved through `A'`, which is `A` with `localizationFunctor` replaced by `loc'` (same `obj` and
`map`, `map_comp` from the re-proved `isRefinement_ofFunctor_comp'`) and the `IsIso` instances
replaced by `isIso_loc'` (from `EPLoc.isIso_homMk`, Theorem 10.3.10); `A = A'` is `rfl` (structure
eta and proof irrelevance), and `A_to_B := A'_to_B`, `B_to_A := B_to_A'` are point-free.  Both
then pass the official `#rt_check`. -/

namespace RoundTrip.V10_45
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.Diagram.isRefinement_ofFunctor_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.localizationFunctor_obj.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.localizationFunctor_map.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.theorem_10_3_14.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isInvertedBy_localizationFunctor.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.inv_localizationFunctor_map.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.homMk_eq.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Examples.not_isIso_pairToPointEP) ∧
  (type_of% @Polyfold.EPLocalization.Examples.isGeneralizedIso_pairToPoint) ∧
  (type_of% @Polyfold.EPLocalization.Examples.inv_localizationFunctor_map_pairToPoint)

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.Diagram.isRefinement_ofFunctor_comp.{0},
    @Polyfold.EPLocalization.EPLoc.localizationFunctor_obj.{0},
    @Polyfold.EPLocalization.EPLoc.localizationFunctor_map.{0},
    @Polyfold.EPLocalization.EPLoc.theorem_10_3_14.{0},
    @Polyfold.EPLocalization.EPLoc.isInvertedBy_localizationFunctor.{0},
    @Polyfold.EPLocalization.EPLoc.inv_localizationFunctor_map.{0},
    @Polyfold.EPLocalization.EPLoc.homMk_eq.{0},
    @Polyfold.EPLocalization.Examples.not_isIso_pairToPointEP,
    @Polyfold.EPLocalization.Examples.isGeneralizedIso_pairToPoint,
    @Polyfold.EPLocalization.Examples.inv_localizationFunctor_map_pairToPoint⟩

/-! ### Glue: `localizationFunctor` and the `IsIso` instances, from non-item lemmas -/

/-- `isRefinement_ofFunctor_comp`, re-proved (the project's proof: the refinement `πX`, as
`Φ ∘ πX ≃ πY`). -/
theorem isRefinement_ofFunctor_comp' {X Y Z : EP.{0}} (Φ : X ⟶ Y) (Ψ : Y ⟶ Z) :
    ((Diagram.ofFunctor Φ).comp (Diagram.ofFunctor Ψ)).IsRefinement
      (Diagram.ofFunctor (Φ ≫ Ψ)) :=
  ⟨WeakFibredProduct.projLeft Φ (EpFunctor.id Y.X) _,
    WeakFibredProduct.isEquivalence_projLeft (EpFunctor.IsEquivalence.id _) _, .refl _,
    (WeakFibredProduct.naturallyEquivalent _).comp_right Ψ⟩

/-- `localizationFunctor`, with `map_comp` from `isRefinement_ofFunctor_comp'`; it is
`localizationFunctor` by `rfl` (`loc'_eq`). -/
noncomputable def loc' : EP.{0} ⥤ EPLoc.{0} where
  obj X := EPLoc.of X
  map Φ := EPLoc.homMk (Diagram.ofFunctor Φ)
  map_id _ := rfl
  map_comp Φ Ψ := EPLoc.homMk_eq_homMk_iff.2 (isRefinement_ofFunctor_comp' Φ Ψ).equiv.symm

/-- `i(F)` is an isomorphism for an equivalence `F` (Theorem 10.3.10, a non-item lemma); used
only as the `IsIso` instance inside `A'`. -/
theorem isIso_loc' {X Y : EP.{0}} (F : X ⟶ Y) (hF : EpFunctor.IsEquivalence F) :
    IsIso (loc'.map F) :=
  EPLoc.isIso_homMk (Diagram.ofFunctor F) hF

/-- `A` with `localizationFunctor` replaced by `loc'` and the `IsIso` instances by
`isIso_loc'`. -/
def A' : Prop :=
  (∀ {X Y Z : EP.{0}} (Φ : X ⟶ Y) (Ψ : Y ⟶ Z),
      ((Diagram.ofFunctor Φ).comp (Diagram.ofFunctor Ψ)).IsRefinement
        (Diagram.ofFunctor (Φ ≫ Ψ))) ∧
  (∀ X : EP.{0}, loc'.obj X = EPLoc.of X) ∧
  (∀ {X Y : EP.{0}} (Φ : X ⟶ Y), loc'.map Φ = EPLoc.homMk (Diagram.ofFunctor Φ)) ∧
  ((∀ X : EP.{0}, loc'.obj X = EPLoc.of X) ∧
    (∀ {X Y : EP.{0}} (Φ : X ⟶ Y), loc'.map Φ =
      EPLoc.homMk ⟨X, EpFunctor.id X.X, EpFunctor.IsEquivalence.id X.X, Φ⟩) ∧
    ∀ {X Y : EP.{0}} (F : X ⟶ Y) (hF : EpFunctor.IsEquivalence F),
      EPLoc.IsGeneralizedIso (loc'.map F) ∧
      ∀ g : EPLoc.of Y ⟶ EPLoc.of X, loc'.map F ≫ g = 𝟙 (loc'.obj X) →
        g ≫ loc'.map F = 𝟙 (EPLoc.of Y) →
        g = EPLoc.homMk ⟨X, F, hF, EpFunctor.id X.X⟩) ∧
  EP.equivalences.{0}.IsInvertedBy loc' ∧
  (∀ {X Y : EP.{0}} (F : X ⟶ Y) (hF : EpFunctor.IsEquivalence F),
      haveI := isIso_loc' F hF
      inv (loc'.map F) = EPLoc.homMk ⟨X, F, hF, EpFunctor.id X.X⟩) ∧
  (∀ {X Y : EP.{0}} (d : Diagram X Y),
      haveI := isIso_loc' d.F d.isEquivalence_F
      EPLoc.homMk d = inv (loc'.map d.F) ≫ loc'.map d.Φ) ∧
  (¬ IsIso Examples.pairToPointEP) ∧
  (EPLoc.IsGeneralizedIso (loc'.map Examples.pairToPointEP) ∧ ¬ IsIso Examples.pairToPointEP) ∧
  (haveI := isIso_loc' Examples.pairToPointEP Examples.isEquivalence_pairToPointEP;
    inv (loc'.map Examples.pairToPointEP) =
      EPLoc.homMk ⟨Examples.pairEP, EpGroupoid.Examples.pairToPoint,
        EpGroupoid.Examples.isEquivalence_pairToPoint, EpFunctor.id Examples.pairEP.X⟩)

/-- Sanity checks (not used below: they mention the banned declarations). -/
theorem loc'_eq : loc' = EPLoc.localizationFunctor.{0} := rfl

/-- `A` and `A'` are the same proposition. -/
theorem A_eq_A' : A = A' := rfl

/-! ### `A → B` -/

theorem A'_to_B (hA : A') : B.{0} := by
  obtain ⟨hcomp, -, -, -, hinv, -⟩ := hA
  refine ⟨fun X => rfl, fun X Y Z Φ Ψ => ?_, fun X Y F hF => hinv F hF⟩
  -- `[d_{Ψ∘Φ}] = [d_Φ.comp d_Ψ] = [d_Φ] ≫ [d_Ψ]`, from the refinement
  exact EPLoc.homMk_eq_homMk_iff.2 (hcomp Φ Ψ).equiv.symm

theorem A_to_B : A → B.{0} := A'_to_B

/-! ### `B → A` -/

theorem B_to_A' (hB : B.{0}) : A' := by
  obtain ⟨-, -, hiso⟩ := hB
  -- `i(F)` is a generalized isomorphism, from `B`
  have hgen : ∀ {X Y : EP.{0}} (F : X ⟶ Y), EpFunctor.IsEquivalence F →
      EPLoc.IsGeneralizedIso (loc'.map F) := fun F hF =>
    (EPLoc.isGeneralizedIso_iff_isIso _).2 (hiso _ _ F hF)
  -- the inverse formula (Theorem 10.3.10 (2)), outright
  have hinvf : ∀ {X Y : EP.{0}} (F : X ⟶ Y) (hF : EpFunctor.IsEquivalence F),
      haveI := isIso_loc' F hF
      inv (loc'.map F) = EPLoc.homMk ⟨X, F, hF, EpFunctor.id X.X⟩ := by
    intro X Y F hF
    have := isIso_loc' F hF
    exact IsIso.inv_eq_of_hom_inv_id
      (EPLoc.homMk_eq_homMk_iff.2 ((Diagram.ofFunctor F).equiv_comp_symm hF))
  -- `pairToPoint` is not an isomorphism of `EP`, outright (the project's proof)
  have hnot : ¬ IsIso Examples.pairToPointEP := fun h => by
    obtain ⟨G, hFG, -⟩ := h.out
    exact EpGroupoid.Examples.not_exists_leftInverse_pairToPoint
      ⟨G, fun x => congrArg (fun H : Examples.pairEP ⟶ Examples.pairEP => H.obj x) hFG⟩
  refine ⟨isRefinement_ofFunctor_comp', fun X => rfl, fun Φ => rfl,
    ⟨fun X => rfl, fun Φ => rfl, fun F hF => ⟨hgen F hF, fun g hg₁ hg₂ => ?_⟩⟩,
    fun X Y F hF => hiso X Y F hF, hinvf, fun d => ?_, hnot,
    ⟨hgen _ Examples.isEquivalence_pairToPointEP, hnot⟩,
    hinvf _ Examples.isEquivalence_pairToPointEP⟩
  · -- the inverse of `i(F)` is `[Y ←F X →1 X]`, outright (Theorem 10.3.10 (2))
    exact (EPLoc.theorem_10_3_10 (Diagram.ofFunctor F)).2 hF g hg₁ hg₂
  · -- `[X ←F A →Φ Y] = i(Φ) ∘ i(F)⁻¹`, outright (the project's refinement by `πA`)
    rw [hinvf _ d.isEquivalence_F]
    refine EPLoc.homMk_eq_homMk_iff.2 (Diagram.IsRefinement.equiv (d' := Diagram.comp
      ⟨d.A, d.F, d.isEquivalence_F, EpFunctor.id d.A.X⟩ (Diagram.ofFunctor d.Φ)) ?_).symm
    exact ⟨WeakFibredProduct.projLeft (EpFunctor.id d.A.X) (EpFunctor.id d.A.X) _,
      WeakFibredProduct.isEquivalence_projLeft (EpFunctor.IsEquivalence.id _) _, .refl _,
      (WeakFibredProduct.naturallyEquivalent _).comp_right d.Φ⟩

theorem B_to_A : B.{0} → A := B_to_A'

/-! ### The checks -/

/-- `A → A`: the official checks fail on it, because the value of `A` contains the banned
`isInvertedBy_localizationFunctor` (the `IsIso` instances in the statements) and reaches
`isRefinement_ofFunctor_comp` (through `localizationFunctor`'s `map_comp`); this is why the
directions are proved through `A'` and stated point-free. -/
theorem A_self : A → A := id

/--
error: rt_check FAIL: RoundTrip.V10_45.A_self uses [Polyfold.EPLocalization.Diagram.isRefinement_ofFunctor_comp, Polyfold.EPLocalization.EPLoc.isInvertedBy_localizationFunctor]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_45.A_self [Polyfold.EPLocalization.Diagram.isRefinement_ofFunctor_comp,
  Polyfold.EPLocalization.EPLoc.localizationFunctor_obj,
  Polyfold.EPLocalization.EPLoc.localizationFunctor_map,
  Polyfold.EPLocalization.EPLoc.theorem_10_3_14,
  Polyfold.EPLocalization.EPLoc.isInvertedBy_localizationFunctor,
  Polyfold.EPLocalization.EPLoc.inv_localizationFunctor_map,
  Polyfold.EPLocalization.EPLoc.homMk_eq,
  Polyfold.EPLocalization.Examples.not_isIso_pairToPointEP,
  Polyfold.EPLocalization.Examples.isGeneralizedIso_pairToPoint,
  Polyfold.EPLocalization.Examples.inv_localizationFunctor_map_pairToPoint]

#rt_check RoundTrip.V10_45.A_to_B [Polyfold.EPLocalization.Diagram.isRefinement_ofFunctor_comp,
  Polyfold.EPLocalization.EPLoc.localizationFunctor_obj,
  Polyfold.EPLocalization.EPLoc.localizationFunctor_map,
  Polyfold.EPLocalization.EPLoc.theorem_10_3_14,
  Polyfold.EPLocalization.EPLoc.isInvertedBy_localizationFunctor,
  Polyfold.EPLocalization.EPLoc.inv_localizationFunctor_map,
  Polyfold.EPLocalization.EPLoc.homMk_eq,
  Polyfold.EPLocalization.Examples.not_isIso_pairToPointEP,
  Polyfold.EPLocalization.Examples.isGeneralizedIso_pairToPoint,
  Polyfold.EPLocalization.Examples.inv_localizationFunctor_map_pairToPoint]
#rt_check RoundTrip.V10_45.B_to_A [Polyfold.EPLocalization.Diagram.isRefinement_ofFunctor_comp,
  Polyfold.EPLocalization.EPLoc.localizationFunctor_obj,
  Polyfold.EPLocalization.EPLoc.localizationFunctor_map,
  Polyfold.EPLocalization.EPLoc.theorem_10_3_14,
  Polyfold.EPLocalization.EPLoc.isInvertedBy_localizationFunctor,
  Polyfold.EPLocalization.EPLoc.inv_localizationFunctor_map,
  Polyfold.EPLocalization.EPLoc.homMk_eq,
  Polyfold.EPLocalization.Examples.not_isIso_pairToPointEP,
  Polyfold.EPLocalization.Examples.isGeneralizedIso_pairToPoint,
  Polyfold.EPLocalization.Examples.inv_localizationFunctor_map_pairToPoint]
#rt_overlap RoundTrip.V10_45.B_to_A [Polyfold.EPLocalization.Diagram.isRefinement_ofFunctor_comp,
  Polyfold.EPLocalization.EPLoc.localizationFunctor_obj,
  Polyfold.EPLocalization.EPLoc.localizationFunctor_map,
  Polyfold.EPLocalization.EPLoc.theorem_10_3_14,
  Polyfold.EPLocalization.EPLoc.isInvertedBy_localizationFunctor,
  Polyfold.EPLocalization.EPLoc.inv_localizationFunctor_map,
  Polyfold.EPLocalization.EPLoc.homMk_eq,
  Polyfold.EPLocalization.Examples.not_isIso_pairToPointEP,
  Polyfold.EPLocalization.Examples.isGeneralizedIso_pairToPoint,
  Polyfold.EPLocalization.Examples.inv_localizationFunctor_map_pairToPoint]

end RoundTrip.V10_45
