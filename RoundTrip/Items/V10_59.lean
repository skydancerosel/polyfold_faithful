import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_59

/-! Round trip for V10_59 (2021 Theorem 10.5.4, pp. 507–508; 2017: Theorem 10.9, p. 367; without
the `Fred` part).

The item lists the definitions `GenSBMap.rep`, `GenSBMap.pushforward`, `GenSBMap.pullback`
(vocabulary) and eight theorems; `A` is the conjunction of their types, universes at `0`
(`bijOn_pushforward_negDiagram`, `pushforward_foldDiagram` have none, they live at `0`):
`GenSBMap.pushforward_eq`, `GenSBMap.pullback_eq`, `GenSBMap.theorem_10_5_4`,
`SDiagram.invOn_pullback_pushforward`, `SDiagram.bijOn_pushforward`,
`SDiagram.bijOn_pushforward_plus`, and the two examples.

`B` (a)–(f): `[D]_* = Ψ_* Φ*` for every representative with both legs equivalences; `[D]_*`, `[D]*`
map `Γ` to `Γ` and are mutually inverse there; `[D⁻¹]` is a generalized strong bundle isomorphism
with `[D⁻¹]_* = [D]*`; the same on `Γ⁺`; `|[D]| = |[D']|` gives `[D]_* = [D']_*`, `[D]* = [D']*`.

* `A_to_B`: all of `B` from `A`'s `theorem_10_5_4` (`Γ⁺ ⊆ Γ`, the non-item
  `plusSectionFunctors_subset`, for the inverse on `Γ⁺`).
* `B_to_A`: `pullback_eq` (not stated in `B`) follows from `B` (d) and (a) applied to the inverse
  diagram (`[D]* = [D⁻¹]_* = Ψ'_* Φ'* = Φ_* Ψ*`).  With it, `theorem_10_5_4` is `B` repackaged
  (`BijOn` from `MapsTo` and `InvOn`), the three `SDiagram` statements are `B` for the class
  `[D]` of the given diagram, and the examples are `B` for the example classes (with the non-item
  `cls_foldDiagram`, `SDiagram.pushforward_id`). -/

namespace RoundTrip.V10_59
open Polyfold CategoryTheory Set Function SBLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.GenSBMap.pushforward_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.GenSBMap.pullback_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.GenSBMap.theorem_10_5_4.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.invOn_pullback_pushforward.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.bijOn_pushforward.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.bijOn_pushforward_plus.{0}) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.bijOn_pushforward_negDiagram) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.pushforward_foldDiagram)

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.GenSBMap.pushforward_eq.{0},
    @Polyfold.SBLocalization.GenSBMap.pullback_eq.{0},
    @Polyfold.SBLocalization.GenSBMap.theorem_10_5_4.{0},
    @Polyfold.SBLocalization.SDiagram.invOn_pullback_pushforward.{0},
    @Polyfold.SBLocalization.SDiagram.bijOn_pushforward.{0},
    @Polyfold.SBLocalization.SDiagram.bijOn_pushforward_plus.{0},
    @Polyfold.StrongBundleLocalizationExamples.bijOn_pushforward_negDiagram,
    @Polyfold.StrongBundleLocalizationExamples.pushforward_foldDiagram⟩

theorem A_to_B : A → B := by
  rintro ⟨-, -, hT, -, -, -, -, -⟩
  intro A A' f hf
  obtain ⟨h1, ⟨hM, hM', hInv, -⟩, h3, ⟨hMp, hMp', -⟩, h5⟩ := hT hf
  refine ⟨fun D hΨ hD s hs => (h1 D hΨ hD).1 hs, fun s hs => hM hs, fun t ht => hM' ht,
    fun s hs => hInv.1 hs, fun t ht => hInv.2 ht,
    fun D hΨ hD => ⟨⟨D.symm hΨ, rfl, D.isEquivalence_Φ⟩, fun h t ht => h3 D hΨ hD ht⟩,
    fun s hs => hMp hs, fun t ht => hMp' ht,
    fun s hs => hInv.1 (A.E.plusSectionFunctors_subset hs),
    fun t ht => hInv.2 (A'.E.plusSectionFunctors_subset ht),
    fun f' hf' h => ⟨fun s hs => (h5 f' hf' h).1 hs, fun t ht => (h5 f' hf' h).2 ht⟩⟩

/-! ### `B → A` -/

section FromB

variable (hB : B)
include hB

theorem pushforward_eq' {A A' : SEP.{0}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso)
    {D : SDiagram A A'} (hD : D.cls = f) (hΨ : SEP.equivalences D.Ψ) :
    EqOn (GenSBMap.pushforward hf) (D.pushforward hΨ) A.E.sectionFunctors :=
  fun s hs => (hB A A' f hf).1 D hΨ hD s hs

/-- `[D]* = [D⁻¹]_* = Φ_* Ψ*`, from `B` (d) and (a) for the inverse diagram. -/
theorem pullback_eq' {A A' : SEP.{0}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso)
    {D : SDiagram A A'} (hD : D.cls = f) (hΨ : SEP.equivalences D.Ψ) :
    EqOn (GenSBMap.pullback hf) (D.pullback hΨ) A'.E.sectionFunctors := by
  intro t ht
  obtain ⟨hs, hEq⟩ := (hB A A' f hf).2.2.2.2.2.1 D hΨ hD
  exact (hEq hs t ht).symm.trans ((hB A' A _ hs).1 (invDiagB D hΨ) D.isEquivalence_Φ rfl t ht)

theorem mapsTo_pushforward' {A A' : SEP.{0}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso) :
    MapsTo (GenSBMap.pushforward hf) A.E.sectionFunctors A'.E.sectionFunctors :=
  fun s hs => (hB A A' f hf).2.1 s hs

theorem mapsTo_pullback' {A A' : SEP.{0}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso) :
    MapsTo (GenSBMap.pullback hf) A'.E.sectionFunctors A.E.sectionFunctors :=
  fun t ht => (hB A A' f hf).2.2.1 t ht

theorem invOn' {A A' : SEP.{0}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso) :
    InvOn (GenSBMap.pullback hf) (GenSBMap.pushforward hf) A.E.sectionFunctors
      A'.E.sectionFunctors :=
  ⟨fun s hs => (hB A A' f hf).2.2.2.1 s hs, fun t ht => (hB A A' f hf).2.2.2.2.1 t ht⟩

theorem bijOn' {A A' : SEP.{0}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso) :
    BijOn (GenSBMap.pushforward hf) A.E.sectionFunctors A'.E.sectionFunctors :=
  (invOn' hB hf).bijOn (mapsTo_pushforward' hB hf) (mapsTo_pullback' hB hf)

theorem invOn_plus' {A A' : SEP.{0}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso) :
    InvOn (GenSBMap.pullback hf) (GenSBMap.pushforward hf) A.E.plusSectionFunctors
      A'.E.plusSectionFunctors :=
  ⟨fun s hs => (hB A A' f hf).2.2.2.2.2.2.2.2.1 s hs,
    fun t ht => (hB A A' f hf).2.2.2.2.2.2.2.2.2.1 t ht⟩

theorem theorem_10_5_4' {A A' : SEP.{0}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso) :
    type_of% (@Polyfold.SBLocalization.GenSBMap.theorem_10_5_4.{0} A A' f hf) := by
  have hb := hB A A' f hf
  refine ⟨fun D hΨ hD => ⟨pushforward_eq' hB hf hD hΨ, pullback_eq' hB hf hD hΨ⟩,
    ⟨mapsTo_pushforward' hB hf, mapsTo_pullback' hB hf, invOn' hB hf, bijOn' hB hf⟩,
    fun D hΨ hD t ht => ?_, ⟨fun s hs => hb.2.2.2.2.2.2.1 s hs,
      fun t ht => hb.2.2.2.2.2.2.2.1 t ht,
      (invOn_plus' hB hf).bijOn (fun s hs => hb.2.2.2.2.2.2.1 s hs)
        (fun t ht => hb.2.2.2.2.2.2.2.1 t ht)⟩,
    fun f' hf' h => ⟨fun s hs => (hb.2.2.2.2.2.2.2.2.2.2 f' hf' h).1 s hs,
      fun t ht => (hb.2.2.2.2.2.2.2.2.2.2 f' hf' h).2 t ht⟩⟩
  obtain ⟨hs, hEq⟩ := hb.2.2.2.2.2.1 D hΨ hD
  exact hEq hs t ht

/-- The statements on a diagram `D` are `B` for its class `[D]`. -/
theorem invOn_pullback_pushforward' {A A' : SEP.{0}} (D : SDiagram A A')
    (hΨ : SEP.equivalences D.Ψ) :
    InvOn (D.pullback hΨ) (D.pushforward hΨ) A.E.sectionFunctors A'.E.sectionFunctors := by
  have hf : D.cls.IsGeneralizedIso := ⟨D, rfl, hΨ⟩
  refine ⟨fun s hs => ?_, fun t ht => ?_⟩
  · have e₁ := pushforward_eq' hB hf rfl hΨ hs
    have hm := mapsTo_pushforward' hB hf hs
    change D.pullback hΨ (D.pushforward hΨ s) = s
    rw [← e₁, ← pullback_eq' hB hf rfl hΨ hm]
    exact (invOn' hB hf).1 hs
  · have e₁ := pullback_eq' hB hf rfl hΨ ht
    have hm := mapsTo_pullback' hB hf ht
    change D.pushforward hΨ (D.pullback hΨ t) = t
    rw [← e₁, ← pushforward_eq' hB hf rfl hΨ hm]
    exact (invOn' hB hf).2 ht

theorem mapsTo_D_pushforward {A A' : SEP.{0}} (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) :
    MapsTo (D.pushforward hΨ) A.E.sectionFunctors A'.E.sectionFunctors := fun s hs => by
  have hf : D.cls.IsGeneralizedIso := ⟨D, rfl, hΨ⟩
  rw [← pushforward_eq' hB hf rfl hΨ hs]
  exact mapsTo_pushforward' hB hf hs

theorem mapsTo_D_pullback {A A' : SEP.{0}} (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) :
    MapsTo (D.pullback hΨ) A'.E.sectionFunctors A.E.sectionFunctors := fun t ht => by
  have hf : D.cls.IsGeneralizedIso := ⟨D, rfl, hΨ⟩
  rw [← pullback_eq' hB hf rfl hΨ ht]
  exact mapsTo_pullback' hB hf ht

theorem bijOn_pushforward_plus' {A A' : SEP.{0}} (D : SDiagram A A')
    (hΨ : SEP.equivalences D.Ψ) :
    BijOn (D.pushforward hΨ) A.E.plusSectionFunctors A'.E.plusSectionFunctors := by
  have hf : D.cls.IsGeneralizedIso := ⟨D, rfl, hΨ⟩
  refine ((invOn_pullback_pushforward' hB D hΨ).mono A.E.plusSectionFunctors_subset
    A'.E.plusSectionFunctors_subset).bijOn (fun s hs => ?_) (fun t ht => ?_)
  · rw [← pushforward_eq' hB hf rfl hΨ (A.E.plusSectionFunctors_subset hs)]
    exact (hB A A' _ hf).2.2.2.2.2.2.1 s hs
  · rw [← pullback_eq' hB hf rfl hΨ (A'.E.plusSectionFunctors_subset ht)]
    exact (hB A A' _ hf).2.2.2.2.2.2.2.1 t ht

end FromB

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {A A' f} hf {D} hD hΨ => pushforward_eq' hB hf hD hΨ,
    fun {A A' f} hf {D} hD hΨ => pullback_eq' hB hf hD hΨ,
    fun {A A' f} hf => theorem_10_5_4' hB hf,
    fun {A A'} D hΨ => invOn_pullback_pushforward' hB D hΨ,
    fun {A A'} D hΨ => (invOn_pullback_pushforward' hB D hΨ).bijOn
      (mapsTo_D_pushforward hB D hΨ) (mapsTo_D_pullback hB D hΨ),
    fun {A A'} D hΨ => bijOn_pushforward_plus' hB D hΨ,
    fun n k => bijOn' hB _, fun n k s hs => ?_⟩
  rw [pushforward_eq' hB _ (StrongBundleLocalizationExamples.cls_foldDiagram n k).symm
    (SEP.equivalences.id_mem _) hs]
  exact SDiagram.pushforward_id _ hs

#rt_check RoundTrip.V10_59.A_to_B [Polyfold.SBLocalization.GenSBMap.pushforward_eq,
  Polyfold.SBLocalization.GenSBMap.pullback_eq, Polyfold.SBLocalization.GenSBMap.theorem_10_5_4,
  Polyfold.SBLocalization.SDiagram.invOn_pullback_pushforward,
  Polyfold.SBLocalization.SDiagram.bijOn_pushforward,
  Polyfold.SBLocalization.SDiagram.bijOn_pushforward_plus,
  Polyfold.StrongBundleLocalizationExamples.bijOn_pushforward_negDiagram,
  Polyfold.StrongBundleLocalizationExamples.pushforward_foldDiagram]
#rt_check RoundTrip.V10_59.B_to_A [Polyfold.SBLocalization.GenSBMap.pushforward_eq,
  Polyfold.SBLocalization.GenSBMap.pullback_eq, Polyfold.SBLocalization.GenSBMap.theorem_10_5_4,
  Polyfold.SBLocalization.SDiagram.invOn_pullback_pushforward,
  Polyfold.SBLocalization.SDiagram.bijOn_pushforward,
  Polyfold.SBLocalization.SDiagram.bijOn_pushforward_plus,
  Polyfold.StrongBundleLocalizationExamples.bijOn_pushforward_negDiagram,
  Polyfold.StrongBundleLocalizationExamples.pushforward_foldDiagram]
#rt_overlap RoundTrip.V10_59.B_to_A [Polyfold.SBLocalization.GenSBMap.pushforward_eq,
  Polyfold.SBLocalization.GenSBMap.pullback_eq, Polyfold.SBLocalization.GenSBMap.theorem_10_5_4,
  Polyfold.SBLocalization.SDiagram.invOn_pullback_pushforward,
  Polyfold.SBLocalization.SDiagram.bijOn_pushforward,
  Polyfold.SBLocalization.SDiagram.bijOn_pushforward_plus,
  Polyfold.StrongBundleLocalizationExamples.bijOn_pushforward_negDiagram,
  Polyfold.StrongBundleLocalizationExamples.pushforward_foldDiagram]

end RoundTrip.V10_59
