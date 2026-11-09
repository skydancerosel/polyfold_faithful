import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_70

/-! Round trip for V10_70 (the strong bundle version of 2021 Theorem 10.3.8, behind Definition
10.5.1: composition of generalized strong bundle maps, well defined, associative, unital).

The item lists the definitions `compMid`, `compLeft`, `compRight`, `SDiagram.comp`,
`GenSBMap.comp` (vocabulary) and ten theorems; `A` is the conjunction of their types, universes
at `0`:
`SDiagram.IsRefinement.comp` (refinements of the factors give a refinement of the composites),
`SDiagram.Equiv.comp`, `SDiagram.isRefinement_assoc` (`(D ∘ D') ∘ D''` REFINES
`D ∘ (D' ∘ D'')`), `SDiagram.equiv_assoc`, `SDiagram.equiv_comp_id`, `SDiagram.equiv_id_comp`,
`SDiagram.equiv_ofHom_comp` (`ofHom F ∘ ofHom G ≈ ofHom (F ≫ G)`), `GenSBMap.cls_comp_cls`
(`[D] ∘ [E] = [D ∘ E]`), and the examples `homMk_foldDiagram_comp`, `nonempty_comp_foldDiagram`.

`B`: (1) equal classes of the factors give equal classes of the composites; (2) associativity
and (3) both unit laws, up to equality of classes.

* `A_to_B`: (1) from `Equiv.comp` with the non-item `cls_eq_cls_iff` (V10_69) and
  `cls_eq_cls_of_equiv`; (2) `equiv_assoc`; (3) `equiv_id_comp`, `equiv_comp_id`.
* `B_to_A`: not proved.  `B` speaks of classes only.  `A` also has the refinement-level lemmas
  `IsRefinement.comp` and `isRefinement_assoc` (a one-sided refinement relation, strictly finer
  than equality of classes), the functoriality `equiv_ofHom_comp` of `ofHom`, and the non-emptiness
  example `nonempty_comp_foldDiagram`, none of which `B` addresses.  `B_to_A_core` proves from
  `B` the class-level conjuncts: `Equiv.comp`, `equiv_assoc`, `equiv_comp_id`, `equiv_id_comp`
  (with the non-item `cls_eq_cls_iff`), `cls_comp_cls` (`rfl`) and `homMk_foldDiagram_comp`
  (from the non-item `cls_foldDiagram`, `[F] = [1]`, and `B` (1), (3)). -/

namespace RoundTrip.V10_70
open Polyfold Polyfold.SBLocalization CategoryTheory
open Polyfold.StrongBundleLocalizationExamples Polyfold.StrongBundleEquivalenceExamples

/-! The project's statement (universes at `0`), one definition per theorem. -/
def A1 : Prop := type_of% @Polyfold.SBLocalization.SDiagram.IsRefinement.comp.{0}
def A2 : Prop := type_of% @Polyfold.SBLocalization.SDiagram.Equiv.comp.{0}
def A3 : Prop := type_of% @Polyfold.SBLocalization.SDiagram.isRefinement_assoc.{0}
def A4 : Prop := type_of% @Polyfold.SBLocalization.SDiagram.equiv_assoc.{0}
def A5 : Prop := type_of% @Polyfold.SBLocalization.SDiagram.equiv_comp_id.{0}
def A6 : Prop := type_of% @Polyfold.SBLocalization.SDiagram.equiv_id_comp.{0}
def A7 : Prop := type_of% @Polyfold.SBLocalization.SDiagram.equiv_ofHom_comp.{0}
def A8 : Prop := type_of% @Polyfold.SBLocalization.GenSBMap.cls_comp_cls.{0}
def A9 : Prop :=
  type_of% @Polyfold.StrongBundleLocalizationCategoryExamples.homMk_foldDiagram_comp
def A10 : Prop :=
  type_of% @Polyfold.StrongBundleLocalizationCategoryExamples.nonempty_comp_foldDiagram

/-- The project's statement. -/
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6 ∧ A7 ∧ A8 ∧ A9 ∧ A10

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.SDiagram.IsRefinement.comp.{0},
    @Polyfold.SBLocalization.SDiagram.Equiv.comp.{0},
    @Polyfold.SBLocalization.SDiagram.isRefinement_assoc.{0},
    @Polyfold.SBLocalization.SDiagram.equiv_assoc.{0},
    @Polyfold.SBLocalization.SDiagram.equiv_comp_id.{0},
    @Polyfold.SBLocalization.SDiagram.equiv_id_comp.{0},
    @Polyfold.SBLocalization.SDiagram.equiv_ofHom_comp.{0},
    @Polyfold.SBLocalization.GenSBMap.cls_comp_cls.{0},
    @Polyfold.StrongBundleLocalizationCategoryExamples.homMk_foldDiagram_comp,
    @Polyfold.StrongBundleLocalizationCategoryExamples.nonempty_comp_foldDiagram⟩

theorem A_to_B : A → B := by
  rintro ⟨-, hcomp, -, hassoc, hcid, hidc, -, -, -, -⟩
  refine ⟨?_, ?_, ?_⟩
  · intro A A' A'' D₁ D₂ E₁ E₂ hD hE
    exact SDiagram.cls_eq_cls_of_equiv
      (hcomp (SDiagram.cls_eq_cls_iff.1 hD) (SDiagram.cls_eq_cls_iff.1 hE))
  · intro A A' A'' A''' D E G
    exact SDiagram.cls_eq_cls_of_equiv (hassoc D E G)
  · intro A A' D
    exact ⟨SDiagram.cls_eq_cls_of_equiv (hidc D), SDiagram.cls_eq_cls_of_equiv (hcid D)⟩

/-- The class-level part of `A`. -/
def A_core : Prop := A2 ∧ A4 ∧ A5 ∧ A6 ∧ A8 ∧ A9

theorem B_to_A_core : B → A_core := by
  rintro ⟨hwd, hassoc, hunit⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A A' A'' D₁ D₂ E₁ E₂ hd he
    exact SDiagram.cls_eq_cls_iff.1
      (hwd A A' A'' D₁ D₂ E₁ E₂ (SDiagram.cls_eq_cls_of_equiv hd) (SDiagram.cls_eq_cls_of_equiv he))
  · intro A A' A'' A''' D D' D''
    exact SDiagram.cls_eq_cls_iff.1 (hassoc A A' A'' A''' D D' D'')
  · intro A A' D
    exact SDiagram.cls_eq_cls_iff.1 (hunit A A' D).2
  · intro A' A'' E
    exact SDiagram.cls_eq_cls_iff.1 (hunit A' A'' E).1
  · intro A A' A'' D E
    rfl
  · intro n k
    -- `[F ∘ F] = [1 ∘ 1] = [1]`, from `[F] = [1]` (`cls_foldDiagram`) and `B` (1), (3)
    show ((foldDiagram n k).comp (foldDiagram n k)).cls = (SDiagram.id (epSEP n k)).cls
    rw [hwd _ _ _ _ _ _ _ (cls_foldDiagram n k) (cls_foldDiagram n k)]
    exact (hunit _ _ (SDiagram.id (epSEP n k))).1

/-! ### Harness checks

`A`'s statement mentions `GenSBMap.comp` (in `cls_comp_cls`) and the category `SEPLoc` (in
`homMk_foldDiagram_comp`), whose proof fields (`Quot.lift₂`'s compatibility, `id_comp`,
`comp_id`, `assoc`) are proved with the banned `Equiv.comp`, `equiv_assoc`, `equiv_comp_id`,
`equiv_id_comp` (and through them `IsRefinement.comp`, `isRefinement_assoc`).  So plain
`#rt_check` fails on both proofs for those names only (recorded with `#guard_msgs`), and
`#rt_check_soft` passes, naming `SEPLoc.category` and `GenSBMap.comp`. -/

/--
error: rt_check FAIL: RoundTrip.V10_70.A_to_B uses [Polyfold.SBLocalization.SDiagram.IsRefinement.comp,
 Polyfold.SBLocalization.SDiagram.Equiv.comp,
 Polyfold.SBLocalization.SDiagram.isRefinement_assoc,
 Polyfold.SBLocalization.SDiagram.equiv_assoc,
 Polyfold.SBLocalization.SDiagram.equiv_comp_id,
 Polyfold.SBLocalization.SDiagram.equiv_id_comp]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_70.A_to_B [Polyfold.SBLocalization.SDiagram.IsRefinement.comp,
  Polyfold.SBLocalization.SDiagram.Equiv.comp,
  Polyfold.SBLocalization.SDiagram.isRefinement_assoc,
  Polyfold.SBLocalization.SDiagram.equiv_assoc,
  Polyfold.SBLocalization.SDiagram.equiv_comp_id,
  Polyfold.SBLocalization.SDiagram.equiv_id_comp,
  Polyfold.SBLocalization.SDiagram.equiv_ofHom_comp,
  Polyfold.SBLocalization.GenSBMap.cls_comp_cls,
  Polyfold.StrongBundleLocalizationCategoryExamples.homMk_foldDiagram_comp,
  Polyfold.StrongBundleLocalizationCategoryExamples.nonempty_comp_foldDiagram]
/--
error: rt_check FAIL: RoundTrip.V10_70.B_to_A_core uses [Polyfold.SBLocalization.SDiagram.IsRefinement.comp,
 Polyfold.SBLocalization.SDiagram.Equiv.comp,
 Polyfold.SBLocalization.SDiagram.isRefinement_assoc,
 Polyfold.SBLocalization.SDiagram.equiv_assoc,
 Polyfold.SBLocalization.SDiagram.equiv_comp_id,
 Polyfold.SBLocalization.SDiagram.equiv_id_comp]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_70.B_to_A_core [Polyfold.SBLocalization.SDiagram.IsRefinement.comp,
  Polyfold.SBLocalization.SDiagram.Equiv.comp,
  Polyfold.SBLocalization.SDiagram.isRefinement_assoc,
  Polyfold.SBLocalization.SDiagram.equiv_assoc,
  Polyfold.SBLocalization.SDiagram.equiv_comp_id,
  Polyfold.SBLocalization.SDiagram.equiv_id_comp,
  Polyfold.SBLocalization.SDiagram.equiv_ofHom_comp,
  Polyfold.SBLocalization.GenSBMap.cls_comp_cls,
  Polyfold.StrongBundleLocalizationCategoryExamples.homMk_foldDiagram_comp,
  Polyfold.StrongBundleLocalizationCategoryExamples.nonempty_comp_foldDiagram]
#rt_check_soft RoundTrip.V10_70.A_to_B [Polyfold.SBLocalization.SDiagram.IsRefinement.comp,
  Polyfold.SBLocalization.SDiagram.Equiv.comp,
  Polyfold.SBLocalization.SDiagram.isRefinement_assoc,
  Polyfold.SBLocalization.SDiagram.equiv_assoc,
  Polyfold.SBLocalization.SDiagram.equiv_comp_id,
  Polyfold.SBLocalization.SDiagram.equiv_id_comp,
  Polyfold.SBLocalization.SDiagram.equiv_ofHom_comp,
  Polyfold.SBLocalization.GenSBMap.cls_comp_cls,
  Polyfold.StrongBundleLocalizationCategoryExamples.homMk_foldDiagram_comp,
  Polyfold.StrongBundleLocalizationCategoryExamples.nonempty_comp_foldDiagram]
#rt_check_soft RoundTrip.V10_70.B_to_A_core [Polyfold.SBLocalization.SDiagram.IsRefinement.comp,
  Polyfold.SBLocalization.SDiagram.Equiv.comp,
  Polyfold.SBLocalization.SDiagram.isRefinement_assoc,
  Polyfold.SBLocalization.SDiagram.equiv_assoc,
  Polyfold.SBLocalization.SDiagram.equiv_comp_id,
  Polyfold.SBLocalization.SDiagram.equiv_id_comp,
  Polyfold.SBLocalization.SDiagram.equiv_ofHom_comp,
  Polyfold.SBLocalization.GenSBMap.cls_comp_cls,
  Polyfold.StrongBundleLocalizationCategoryExamples.homMk_foldDiagram_comp,
  Polyfold.StrongBundleLocalizationCategoryExamples.nonempty_comp_foldDiagram]

#rt_overlap RoundTrip.V10_70.B_to_A_core [Polyfold.SBLocalization.SDiagram.IsRefinement.comp,
  Polyfold.SBLocalization.SDiagram.Equiv.comp,
  Polyfold.SBLocalization.SDiagram.isRefinement_assoc,
  Polyfold.SBLocalization.SDiagram.equiv_assoc,
  Polyfold.SBLocalization.SDiagram.equiv_comp_id,
  Polyfold.SBLocalization.SDiagram.equiv_id_comp,
  Polyfold.SBLocalization.SDiagram.equiv_ofHom_comp,
  Polyfold.SBLocalization.GenSBMap.cls_comp_cls,
  Polyfold.StrongBundleLocalizationCategoryExamples.homMk_foldDiagram_comp,
  Polyfold.StrongBundleLocalizationCategoryExamples.nonempty_comp_foldDiagram]

end RoundTrip.V10_70
