import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_71

/-! Round trip for V10_71 (2021 Remark 10.5.3: the strong bundle case of Theorem 10.3.10, one
direction: a diagram whose two legs are strong bundle equivalences represents an isomorphism of
`SEP(F⁻¹)`).

The item lists the definitions `SEPLoc.baseFunctor` (vocabulary) and seven theorems; `A` is the
conjunction of their types, all universes at `0`:
`SEPLoc.theorem_10_3_10` (`[D]` is an isomorphism, and every two-sided inverse is
`[D.symm hΨ]`), `SEPLoc.isIso_of_isGeneralizedIso`, `SEPLoc.inv_homMk`
(`inv [D] = [D.symm hΨ]`), `SDiagram.equiv_comp_symm`, `SDiagram.equiv_symm_comp`
(`D ∘ D⁻¹ ≈ 1`, `D⁻¹ ∘ D ≈ 1`), `SEPLoc.isEquivalence_base_of_isIso` (the base half of the
converse: if `[D]` is an isomorphism, `ψ` is an equivalence of ep-groupoids) and the example
`isIso_homMk_negDiagram`.

`B`: for every diagram `D` with `Ψ` a strong bundle equivalence, `[D ∘ revB D] = [1_W]` and
`[revB D ∘ D] = [1_W']`, `revB D h = ⟨D.B, D.Ψ, h, D.Φ⟩` (the blind author's reversed diagram,
equal to the project's `D.symm h` by `rfl`).

* `A_to_B`: `equiv_comp_symm`, `equiv_symm_comp` and the non-item `cls_eq_cls_of_equiv`.
* `B_to_A`: `B`'s two equations are `homMk D ≫ homMk (D.symm hΨ) = 𝟙` and
  `homMk (D.symm hΨ) ≫ homMk D = 𝟙` (by `rfl`: `homMk_comp`, `id_eq`); from them the isomorphism,
  the uniqueness of the inverse, `isIso_of_isGeneralizedIso`, `inv_homMk` and (with the non-item
  `cls_eq_cls_iff`, V10_69) `equiv_comp_symm`, `equiv_symm_comp`; the example from these.
  `isEquivalence_base_of_isIso` is the base half of the CONVERSE of Theorem 10.3.10, about which
  `B` (one direction) says nothing: it is re-proved outright, as in the project, from the
  non-item `EPLoc.isIso_homMk_iff` (Theorem 10.3.10 for ep-groupoids) and the functor
  `baseFunctor` (two lines). -/

namespace RoundTrip.V10_71
open Polyfold Polyfold.SBLocalization CategoryTheory
open Polyfold.StrongBundleLocalizationExamples Polyfold.StrongBundleEquivalenceExamples

/-! The project's statement (universes at `0`), one definition per theorem: `A3` (the type of
`inv_homMk`) mentions the banned `theorem_10_3_10` itself, as the `IsIso` instance of `inv`. -/
def A1 : Prop := type_of% @Polyfold.SBLocalization.SEPLoc.theorem_10_3_10.{0}
def A2 : Prop := type_of% @Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso.{0}
def A3 : Prop := type_of% @Polyfold.SBLocalization.SEPLoc.inv_homMk.{0}
def A4 : Prop := type_of% @Polyfold.SBLocalization.SDiagram.equiv_comp_symm.{0}
def A5 : Prop := type_of% @Polyfold.SBLocalization.SDiagram.equiv_symm_comp.{0}
def A6 : Prop := type_of% @Polyfold.SBLocalization.SEPLoc.isEquivalence_base_of_isIso.{0}
def A7 : Prop :=
  type_of% @Polyfold.StrongBundleLocalizationCategoryExamples.isIso_homMk_negDiagram

/-- The project's statement. -/
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6 ∧ A7

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.SEPLoc.theorem_10_3_10.{0},
    @Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso.{0},
    @Polyfold.SBLocalization.SEPLoc.inv_homMk.{0},
    @Polyfold.SBLocalization.SDiagram.equiv_comp_symm.{0},
    @Polyfold.SBLocalization.SDiagram.equiv_symm_comp.{0},
    @Polyfold.SBLocalization.SEPLoc.isEquivalence_base_of_isIso.{0},
    @Polyfold.StrongBundleLocalizationCategoryExamples.isIso_homMk_negDiagram⟩

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, hcs, hsc, -, -⟩
  intro A A' D h
  exact ⟨SDiagram.cls_eq_cls_of_equiv (hcs D h), SDiagram.cls_eq_cls_of_equiv (hsc D h)⟩

/-- `revB` is the project's `symm`. -/
theorem revB_eq {A A' : SEP.{0}} (D : SDiagram A A') (h : SEP.equivalences D.Ψ) :
    revB D h = D.symm h := rfl

section FromB

variable (hB : B)
include hB

theorem hom_inv {A A' : SEP.{0}} (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) :
    SEPLoc.homMk D ≫ SEPLoc.homMk (D.symm hΨ) = 𝟙 _ :=
  (hB A A' D hΨ).1

theorem inv_hom {A A' : SEP.{0}} (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) :
    SEPLoc.homMk (D.symm hΨ) ≫ SEPLoc.homMk D = 𝟙 _ :=
  (hB A A' D hΨ).2

theorem a1 : A1 := by
  intro A A' D hΨ
  have h₁ := hom_inv hB D hΨ
  have h₂ := inv_hom hB D hΨ
  refine ⟨⟨_, h₁, h₂⟩, fun g hg₁ hg₂ => ?_⟩
  calc g = g ≫ SEPLoc.homMk D ≫ SEPLoc.homMk (D.symm hΨ) := by rw [h₁, Category.comp_id]
    _ = SEPLoc.homMk (D.symm hΨ) := by rw [← Category.assoc, hg₂, Category.id_comp]

theorem isIso' {A A' : SEP.{0}} (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) :
    IsIso (SEPLoc.homMk D) :=
  ⟨⟨_, hom_inv hB D hΨ, inv_hom hB D hΨ⟩⟩

end FromB

/-- The base half of the converse (not addressed by `B`), re-proved outright as in the project. -/
theorem a6 : A6 := by
  intro A A' D h
  have := Functor.map_isIso SEPLoc.baseFunctor (SEPLoc.homMk D)
  exact (EPLocalization.EPLoc.isIso_homMk_iff D.base).1 this

theorem a2 (hB : B) : A2 := by
  intro A A' f hf
  obtain ⟨D, rfl, hΨ⟩ := hf
  exact isIso' hB D hΨ

/-- (Term mode, so that the goal's `have this := (theorem_10_3_10 D hΨ).1` is never elaborated
into the proof: the instance of `inv` is our `isIso' hB D hΨ`, equal by proof irrelevance.) -/
theorem a3 (hB : B) : A3 := fun {_ _} D hΨ =>
  @IsIso.inv_eq_of_hom_inv_id _ _ _ _ _ (isIso' hB D hΨ) _ (hom_inv hB D hΨ)

theorem a4 (hB : B) : A4 := by
  intro A A' D hΨ
  exact SDiagram.cls_eq_cls_iff.1 (hB A A' D hΨ).1

theorem a5 (hB : B) : A5 := by
  intro A A' D hΨ
  exact SDiagram.cls_eq_cls_iff.1 (hB A A' D hΨ).2

theorem a7 (hB : B) : A7 := by
  intro n k
  have hI := isIso' hB (negDiagram n k) (negSEPHom_mem_equivalences n k)
  exact ⟨hI, hom_inv hB (negDiagram n k) (negSEPHom_mem_equivalences n k),
    isIso' hB (SDiagram.ofHom (negSEPHom n k)) (negSEPHom_mem_equivalences n k),
    a6 (negDiagram n k) hI⟩

theorem B_to_A : B → A := fun hB => ⟨a1 hB, a2 hB, a3 hB, a4 hB, a5 hB, a6, a7 hB⟩

/-! ### Harness checks

The statement of `inv_homMk` (our `A3`) contains the banned `SEPLoc.theorem_10_3_10` itself (the
`IsIso` instance of `inv`), so every term mentioning `A` reaches it and plain `#rt_check` fails on
both directions for that name only (recorded below with `#guard_msgs`).  `#rt_check_except_defs`
is the harness traversal `rtCollect` with the body of the statement definition `A3` not unfolded:
our proofs reach the banned theorems only through that statement (`A_to_B` never uses `A3`;
`B_to_A` proves `A3` with the instance `isIso' hB D hΨ` of our own, equal by proof
irrelevance). -/

open Lean Elab Command in
/-- `#rt_check_except_defs T [nᵢ]`: the proof of `T` reaches the banned `nᵢ` only through the
body of the statement definition `RoundTrip.V10_71.A3`. -/
elab "#rt_check_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let used := rtCollect env roots.toList (NameSet.empty.insert ``RoundTrip.V10_71.A3)
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do
    throwError "FAIL: {t.getId} uses {bad} outside the statement A3"
  logInfo m!"OK: {t.getId} reaches the banned theorems only through the statement A3"

/--
error: rt_check FAIL: RoundTrip.V10_71.A_to_B uses [Polyfold.SBLocalization.SEPLoc.theorem_10_3_10,
 Polyfold.SBLocalization.SDiagram.equiv_comp_symm,
 Polyfold.SBLocalization.SDiagram.equiv_symm_comp]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_71.A_to_B [Polyfold.SBLocalization.SEPLoc.theorem_10_3_10,
  Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso,
  Polyfold.SBLocalization.SEPLoc.inv_homMk,
  Polyfold.SBLocalization.SDiagram.equiv_comp_symm,
  Polyfold.SBLocalization.SDiagram.equiv_symm_comp,
  Polyfold.SBLocalization.SEPLoc.isEquivalence_base_of_isIso,
  Polyfold.StrongBundleLocalizationCategoryExamples.isIso_homMk_negDiagram]
/--
error: rt_check FAIL: RoundTrip.V10_71.B_to_A uses [Polyfold.SBLocalization.SEPLoc.theorem_10_3_10,
 Polyfold.SBLocalization.SDiagram.equiv_comp_symm,
 Polyfold.SBLocalization.SDiagram.equiv_symm_comp]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_71.B_to_A [Polyfold.SBLocalization.SEPLoc.theorem_10_3_10,
  Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso,
  Polyfold.SBLocalization.SEPLoc.inv_homMk,
  Polyfold.SBLocalization.SDiagram.equiv_comp_symm,
  Polyfold.SBLocalization.SDiagram.equiv_symm_comp,
  Polyfold.SBLocalization.SEPLoc.isEquivalence_base_of_isIso,
  Polyfold.StrongBundleLocalizationCategoryExamples.isIso_homMk_negDiagram]
#rt_check_except_defs RoundTrip.V10_71.A_to_B [Polyfold.SBLocalization.SEPLoc.theorem_10_3_10,
  Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso,
  Polyfold.SBLocalization.SEPLoc.inv_homMk,
  Polyfold.SBLocalization.SDiagram.equiv_comp_symm,
  Polyfold.SBLocalization.SDiagram.equiv_symm_comp,
  Polyfold.SBLocalization.SEPLoc.isEquivalence_base_of_isIso,
  Polyfold.StrongBundleLocalizationCategoryExamples.isIso_homMk_negDiagram]
#rt_check_except_defs RoundTrip.V10_71.B_to_A [Polyfold.SBLocalization.SEPLoc.theorem_10_3_10,
  Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso,
  Polyfold.SBLocalization.SEPLoc.inv_homMk,
  Polyfold.SBLocalization.SDiagram.equiv_comp_symm,
  Polyfold.SBLocalization.SDiagram.equiv_symm_comp,
  Polyfold.SBLocalization.SEPLoc.isEquivalence_base_of_isIso,
  Polyfold.StrongBundleLocalizationCategoryExamples.isIso_homMk_negDiagram]
#rt_overlap RoundTrip.V10_71.B_to_A [Polyfold.SBLocalization.SEPLoc.theorem_10_3_10,
  Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso,
  Polyfold.SBLocalization.SEPLoc.inv_homMk,
  Polyfold.SBLocalization.SDiagram.equiv_comp_symm,
  Polyfold.SBLocalization.SDiagram.equiv_symm_comp,
  Polyfold.SBLocalization.SEPLoc.isEquivalence_base_of_isIso,
  Polyfold.StrongBundleLocalizationCategoryExamples.isIso_homMk_negDiagram]

open Lean Elab Command in
/-- `#rt_overlap` with the body of the statement definition `A3` not unfolded on our side. -/
elab "#rt_overlap_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let used := rtCollect env (((rtValue? ci).map (·.getUsedConstants)).getD #[]).toList
    (NameSet.empty.insert ``RoundTrip.V10_71.A3)
  let mut roots : Array Name := #[]
  for b in bs.getElems do
    if let some c := env.find? b.getId then
      roots := roots ++ (((rtValue? c).map (·.getUsedConstants)).getD #[])
  let closure := rtCollect env roots.toList {}
  let shared := used.toList.filter fun n =>
    closure.contains n && (match env.find? n with | some (.thmInfo _) => true | _ => false) &&
      (`Polyfold).isPrefixOf n
  logInfo m!"rt_overlap (A3 not unfolded) {t.getId}: {shared.length} shared project theorems {shared}"

#rt_overlap_except_defs RoundTrip.V10_71.B_to_A [Polyfold.SBLocalization.SEPLoc.theorem_10_3_10,
  Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso,
  Polyfold.SBLocalization.SEPLoc.inv_homMk,
  Polyfold.SBLocalization.SDiagram.equiv_comp_symm,
  Polyfold.SBLocalization.SDiagram.equiv_symm_comp,
  Polyfold.SBLocalization.SEPLoc.isEquivalence_base_of_isIso,
  Polyfold.StrongBundleLocalizationCategoryExamples.isIso_homMk_negDiagram]

end RoundTrip.V10_71
