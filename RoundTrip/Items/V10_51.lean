import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_51

/-! Round trip for V10_51 (2021 §10.5, p. 504: the diagrams of strong bundles, refinements,
equivalence, and the classes `[D]`).

The item lists the definitions `SDiagram`, `IsRefinement`, `precomp`, `IsCommonRefinement`,
`Equiv`, `SEP.NatEquiv`, `GenSBMap`, `cls`, `foldDiagram` (vocabulary) and twelve theorems; `A` is
the conjunction of their types, universes at `0`: the two examples of refinements
(`isRefinement_precomp`, `isRefinement_of_natEquiv`), `IsRefinement.refl`, `IsRefinement.trans`,
`Equiv.refl`, `Equiv.symm`, `IsRefinement.equiv`, `SEP.NatEquiv.comp_left`,
`cls_eq_cls_of_equiv`, `cls_eq_cls_iff` (`[D] = [D'] ↔ D, D'` have a common refinement: the
transitivity of `Equiv`, the strong bundle Lemma 10.3.4, proved in the project with the weak
fibred product of strong bundles), and the witnesses `isRefinement_foldDiagram`,
`cls_foldDiagram`.

* `A_to_B`: (a) is the fields of `SDiagram` (`isEquivalence_Φ` is by definition
  `IsStrongBundleEquivalence`; `SEP.Hom.isStrongBundleFunctor`), and every triple is the diagram
  `⟨C, Φ, h, Ψ⟩`; (b), (c) hold by `Iff.rfl` (the composite of morphisms of `SEP` is the pair of
  composites, definitionally); (d) is `cls_eq_cls_iff` and (c); (e) is `Quot.exists_rep`.
* `B_to_A`: `cls_eq_cls_iff` comes from `B` (d) and (c) — this is the only conjunct with
  mathematical content beyond the definitions.  The other eleven are elementary facts about the
  definitions, not consequences of `B` (which says nothing about `precomp`, `foldDiagram`, or
  composites of refinements); they are re-proved outright from non-item project lemmas
  (`SEP.NatEquiv.refl`, `symm`, `trans`, `StrongBundleNatTrans.whiskerLeft`,
  `SEP.equivalences.comp_mem`, `negSEPHom_mem_equivalences`), copying the project's short proofs,
  with `comp_left` re-proved locally (`comp_left'`) since it is banned. -/

namespace RoundTrip.V10_51
open Polyfold CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.SDiagram.isRefinement_precomp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.isRefinement_of_natEquiv.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.IsRefinement.refl.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.IsRefinement.trans.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.Equiv.refl.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.Equiv.symm.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.IsRefinement.equiv.{0}) ∧
  (type_of% @Polyfold.SEP.NatEquiv.comp_left.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.cls_eq_cls_of_equiv.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.cls_eq_cls_iff.{0}) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.isRefinement_foldDiagram) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.cls_foldDiagram)

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.SDiagram.isRefinement_precomp.{0},
    @Polyfold.SBLocalization.SDiagram.isRefinement_of_natEquiv.{0},
    @Polyfold.SBLocalization.SDiagram.IsRefinement.refl.{0},
    @Polyfold.SBLocalization.SDiagram.IsRefinement.trans.{0},
    @Polyfold.SBLocalization.SDiagram.Equiv.refl.{0},
    @Polyfold.SBLocalization.SDiagram.Equiv.symm.{0},
    @Polyfold.SBLocalization.SDiagram.IsRefinement.equiv.{0},
    @Polyfold.SEP.NatEquiv.comp_left.{0},
    @Polyfold.SBLocalization.SDiagram.cls_eq_cls_of_equiv.{0},
    @Polyfold.SBLocalization.SDiagram.cls_eq_cls_iff.{0},
    @Polyfold.StrongBundleLocalizationExamples.isRefinement_foldDiagram,
    @Polyfold.StrongBundleLocalizationExamples.cls_foldDiagram⟩

open SBLocalization in
/-- B's refinement is the project's (definitionally). -/
theorem isRefinement_iff_isRefB {A A' : SEP.{0}} (D D' : SDiagram A A') :
    D'.IsRefinement D ↔ IsRefB D' D := Iff.rfl

open SBLocalization in
/-- B's equivalence is the project's (definitionally). -/
theorem equiv_iff_equivB {A A' : SEP.{0}} (D D' : SDiagram A A') :
    D.Equiv D' ↔ EquivB D D' := Iff.rfl

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, -, -, -, -, -, -, hiff, -, -⟩
  intro A A'
  refine ⟨fun D => ⟨D.isEquivalence_Φ, SEP.Hom.isStrongBundleFunctor D.Ψ⟩,
    fun C Φ Ψ h => ⟨⟨C, Φ, h, Ψ⟩, rfl, HEq.rfl, HEq.rfl⟩, isRefinement_iff_isRefB,
    equiv_iff_equivB, fun D D' => hiff.trans (equiv_iff_equivB D D'), fun f => Quot.exists_rep f⟩

/-- `SEP.NatEquiv.comp_left`, re-proved (the project's proof). -/
theorem comp_left' {A A' A'' : SEP.{0}} {F G : A ⟶ A'} (h : SEP.NatEquiv F G) (K : A'' ⟶ A) :
    SEP.NatEquiv (K ≫ F) (K ≫ G) :=
  let ⟨θ⟩ := h
  ⟨θ.whiskerLeft (SEP.Hom.isStrongBundleFunctor F) (SEP.Hom.isStrongBundleFunctor K)⟩

open SBLocalization StrongBundleLocalizationExamples StrongBundleEquivalenceExamples in
theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun D C H hH => ⟨H, hH, .refl _, .refl _⟩,
    fun D Φ' hΦ' Ψ' h₁ h₂ => ⟨𝟙 _, SEP.equivalences.id_mem _, h₁.symm, h₂.symm⟩,
    fun D => ⟨𝟙 _, SEP.equivalences.id_mem _, .refl _, .refl _⟩, ?_,
    fun D => ⟨D, ⟨𝟙 _, SEP.equivalences.id_mem _, .refl _, .refl _⟩,
      ⟨𝟙 _, SEP.equivalences.id_mem _, .refl _, .refl _⟩⟩,
    fun h => let ⟨D'', h₁, h₂⟩ := h; ⟨D'', h₂, h₁⟩,
    fun {_ _ D' _} h => ⟨D', ⟨𝟙 _, SEP.equivalences.id_mem _, .refl _, .refl _⟩, h⟩,
    @comp_left', fun h => Quot.sound h,
    fun {A A' D D'} => ((hB A A').2.2.2.2.1 D D').trans (equiv_iff_equivB D D').symm,
    ?_, ?_⟩
  · intro A A' D D' D'' h'' h'
    obtain ⟨H, hH, hΦ, hΨ⟩ := h'
    obtain ⟨H', hH', hΦ', hΨ'⟩ := h''
    exact ⟨H' ≫ H, SEP.equivalences.comp_mem _ _ hH' hH, (comp_left' hΦ H').trans hΦ',
      (comp_left' hΨ H').trans hΨ'⟩
  · intro n k
    have h : SEP.NatEquiv (negSEPHom n k ≫ 𝟙 (epSEP n k)) (negSEPHom n k) := by
      rw [Category.comp_id]; exact .refl _
    exact ⟨negSEPHom n k, negSEPHom_mem_equivalences n k, h, h⟩
  · intro n k
    have h : SEP.NatEquiv (negSEPHom n k ≫ 𝟙 (epSEP n k)) (negSEPHom n k) := by
      rw [Category.comp_id]; exact .refl _
    exact Quot.sound ⟨foldDiagram n k, ⟨𝟙 _, SEP.equivalences.id_mem _, .refl _, .refl _⟩,
      ⟨negSEPHom n k, negSEPHom_mem_equivalences n k, h, h⟩⟩

#rt_check RoundTrip.V10_51.A_to_B [Polyfold.SBLocalization.SDiagram.isRefinement_precomp,
  Polyfold.SBLocalization.SDiagram.isRefinement_of_natEquiv,
  Polyfold.SBLocalization.SDiagram.IsRefinement.refl,
  Polyfold.SBLocalization.SDiagram.IsRefinement.trans,
  Polyfold.SBLocalization.SDiagram.Equiv.refl, Polyfold.SBLocalization.SDiagram.Equiv.symm,
  Polyfold.SBLocalization.SDiagram.IsRefinement.equiv, Polyfold.SEP.NatEquiv.comp_left,
  Polyfold.SBLocalization.SDiagram.cls_eq_cls_of_equiv,
  Polyfold.SBLocalization.SDiagram.cls_eq_cls_iff,
  Polyfold.StrongBundleLocalizationExamples.isRefinement_foldDiagram,
  Polyfold.StrongBundleLocalizationExamples.cls_foldDiagram]
#rt_check RoundTrip.V10_51.B_to_A [Polyfold.SBLocalization.SDiagram.isRefinement_precomp,
  Polyfold.SBLocalization.SDiagram.isRefinement_of_natEquiv,
  Polyfold.SBLocalization.SDiagram.IsRefinement.refl,
  Polyfold.SBLocalization.SDiagram.IsRefinement.trans,
  Polyfold.SBLocalization.SDiagram.Equiv.refl, Polyfold.SBLocalization.SDiagram.Equiv.symm,
  Polyfold.SBLocalization.SDiagram.IsRefinement.equiv, Polyfold.SEP.NatEquiv.comp_left,
  Polyfold.SBLocalization.SDiagram.cls_eq_cls_of_equiv,
  Polyfold.SBLocalization.SDiagram.cls_eq_cls_iff,
  Polyfold.StrongBundleLocalizationExamples.isRefinement_foldDiagram,
  Polyfold.StrongBundleLocalizationExamples.cls_foldDiagram]
#rt_overlap RoundTrip.V10_51.B_to_A [Polyfold.SBLocalization.SDiagram.isRefinement_precomp,
  Polyfold.SBLocalization.SDiagram.isRefinement_of_natEquiv,
  Polyfold.SBLocalization.SDiagram.IsRefinement.refl,
  Polyfold.SBLocalization.SDiagram.IsRefinement.trans,
  Polyfold.SBLocalization.SDiagram.Equiv.refl, Polyfold.SBLocalization.SDiagram.Equiv.symm,
  Polyfold.SBLocalization.SDiagram.IsRefinement.equiv, Polyfold.SEP.NatEquiv.comp_left,
  Polyfold.SBLocalization.SDiagram.cls_eq_cls_of_equiv,
  Polyfold.SBLocalization.SDiagram.cls_eq_cls_iff,
  Polyfold.StrongBundleLocalizationExamples.isRefinement_foldDiagram,
  Polyfold.StrongBundleLocalizationExamples.cls_foldDiagram]

end RoundTrip.V10_51
