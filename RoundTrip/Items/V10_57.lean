import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_57

/-! Round trip for V10_57 (2021 Remark 10.5.3, p. 506, new in the 2021 edition: the comparison
with Theorem 10.3.10).

`A` is the conjunction of the types of the two listed theorems, universes at `0`:
`GenSBMap.remark_10_5_3` (a generalized strong bundle isomorphism covers a generalized isomorphism
of the bases, induces one of the total spaces, and `|[D]|` is a homeomorphism) and
`SEPLoc.isIso_of_isGeneralizedIso` (a generalized strong bundle isomorphism is an isomorphism of
`SEP(F⁻¹)`).

`B` = (1) Theorem 10.3.10 for ep-groupoids: `f` is an isomorphism of `EP(E⁻¹)` iff `f = [d]` with
both legs equivalences; and (2) its strong bundle analogue: a morphism of `SEP(F⁻¹)` is an
isomorphism iff it is `[D]` with both legs strong bundle equivalences.

* `A → B` is **not proved**: the `→` half of (2) (an isomorphism of `SEP(F⁻¹)` has a
  representative with `Ψ` a strong bundle equivalence) is not in `A`, and the project does not
  prove it (only its base half, `SEPLoc.isEquivalence_base_of_isIso`: the functor `ψ` covered by
  `Ψ` is an equivalence).  It would need strong bundle versions of the claims (C1), (C2) of
  Appendix 10.6.2.  Everything else of `B` follows: `A_to_BWeak` proves (1) (outright, from the
  non-item `EPLoc.homMk_surjective`, `EPLoc.isIso_homMk_iff`, `EPLoc.isIso_homMk`: it is not part
  of `A`) and the `←` half of (2) (from `A`'s `isIso_of_isGeneralizedIso`).  `B_iff` records that
  `B` is exactly `BWeak` plus the missing converse.
* `B_to_A`: `remark_10_5_3` from `B` (1) `←` applied to the base diagram `d` and to the
  total-space diagram of a representative (both have both legs equivalences), plus the non-item
  `Diagram.isHomeomorph_orbitMap` for `|[D]|`; `isIso_of_isGeneralizedIso` from `B` (2) `←`. -/

namespace RoundTrip.V10_57
open Polyfold CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.GenSBMap.remark_10_5_3.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.GenSBMap.remark_10_5_3.{0},
    @Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso.{0}⟩

/-- The missing half: an isomorphism of `SEP(F⁻¹)` is the class of a diagram with both legs
strong bundle equivalences (the `→` half of `B` (2)). -/
def Converse : Prop :=
  ∀ (A A' : SEP.{0})
      (f : (SBLocalization.SEPLoc.of A : SBLocalization.SEPLoc) ⟶ SBLocalization.SEPLoc.of A'),
    IsIso f →
      ∃ D : SBLocalization.SDiagram A A', SBLocalization.SEPLoc.homMk D = f ∧
        D.B.E.IsStrongBundleEquivalence A.E D.Φ.ϕ D.Φ.Φ ∧
        D.B.E.IsStrongBundleEquivalence A'.E D.Ψ.ϕ D.Ψ.Φ

/-- `B` without the missing half: (1) in full, and the `←` half of (2). -/
def BWeak : Prop :=
  (∀ (X Y : EP.{0})
      (f : (EPLocalization.EPLoc.of X : EPLocalization.EPLoc) ⟶ EPLocalization.EPLoc.of Y),
    IsIso f ↔
      ∃ d : EPLocalization.Diagram X Y, EPLocalization.EPLoc.homMk d = f ∧
        d.F.IsEquivalence ∧ d.Φ.IsEquivalence) ∧
  (∀ (A A' : SEP.{0})
      (f : (SBLocalization.SEPLoc.of A : SBLocalization.SEPLoc) ⟶ SBLocalization.SEPLoc.of A'),
    (∃ D : SBLocalization.SDiagram A A', SBLocalization.SEPLoc.homMk D = f ∧
        D.B.E.IsStrongBundleEquivalence A.E D.Φ.ϕ D.Φ.Φ ∧
        D.B.E.IsStrongBundleEquivalence A'.E D.Ψ.ϕ D.Ψ.Φ) → IsIso f)

/-- `B` is `BWeak` together with the missing converse. -/
theorem B_iff : B ↔ BWeak ∧ Converse :=
  ⟨fun h => ⟨⟨h.1, fun A A' f => (h.2 A A' f).2⟩, fun A A' f => (h.2 A A' f).1⟩,
    fun h => ⟨h.1.1, fun A A' f => ⟨h.2 A A' f, h.1.2 A A' f⟩⟩⟩

/-- Everything of `B` except the missing converse follows from `A` ((1) outright). -/
theorem A_to_BWeak : A → BWeak := by
  rintro ⟨-, hiso⟩
  refine ⟨fun X Y f => ⟨fun h => ?_, ?_⟩, fun A A' f => ?_⟩
  · obtain ⟨d, rfl⟩ := EPLocalization.EPLoc.homMk_surjective f
    exact ⟨d, rfl, d.isEquivalence_F, (EPLocalization.EPLoc.isIso_homMk_iff d).1 h⟩
  · rintro ⟨d, rfl, -, h⟩
    exact EPLocalization.EPLoc.isIso_homMk d h
  · rintro ⟨D, rfl, -, hΨ⟩
    exact hiso (f := D.cls) ⟨D, rfl, hΨ⟩

/-- Hence `A ∧ Converse → B`. -/
theorem A_and_Converse_to_B : A ∧ Converse → B := fun h => B_iff.2 ⟨A_to_BWeak h.1, h.2⟩

theorem B_to_A : B → A := by
  rintro ⟨h1, h2⟩
  refine ⟨fun {A A' f} hf => ?_, fun {A A' f} hf => ?_⟩
  · obtain ⟨D, rfl, hΨ⟩ := hf
    have hb : IsIso (EPLocalization.EPLoc.homMk D.base) :=
      (h1 _ _ _).2 ⟨D.base, rfl, D.hΦ.isEquivalence_base, hΨ.isEquivalence_base⟩
    have ht : IsIso (EPLocalization.EPLoc.homMk D.total) :=
      (h1 _ _ _).2 ⟨D.total, rfl, D.hΦ.isEquivalence, hΨ.isEquivalence⟩
    exact ⟨hb.out, ht.out, D.total.isHomeomorph_orbitMap hΨ.isEquivalence⟩
  · obtain ⟨D, rfl, hΨ⟩ := hf
    exact (h2 A A' (SBLocalization.SEPLoc.homMk D)).2 ⟨D, rfl, D.isEquivalence_Φ, hΨ⟩

#rt_check RoundTrip.V10_57.A_to_BWeak [Polyfold.SBLocalization.GenSBMap.remark_10_5_3,
  Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso]
#rt_check RoundTrip.V10_57.B_to_A [Polyfold.SBLocalization.GenSBMap.remark_10_5_3,
  Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso]
#rt_overlap RoundTrip.V10_57.B_to_A [Polyfold.SBLocalization.GenSBMap.remark_10_5_3,
  Polyfold.SBLocalization.SEPLoc.isIso_of_isGeneralizedIso]

end RoundTrip.V10_57
