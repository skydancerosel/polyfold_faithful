import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_12

/-! Round trip for V2_12 (Definition 2.13: M-polyfolds).

`A` is the conjunction of the types of `Polyfold.MPolyfold.IsChart.compatible`,
`Polyfold.MPolyfold.IsChart.restrict`, `Polyfold.MPolyfold.isChart_congr` and
`Polyfold.MPolyfold.exists_isChart_mem_source`, universe instantiated at `0` (B lives in `Type`).
`MPolyfold`, `MPolyfold.IsChart` and `LocalModel.toMPolyfold` are definitions (vocabulary).

`A → B`: (a) reflexivity and symmetry are `MAtlas.Equiv.refl/symm` (item V2_11), transitivity is
`MChart.compatible_of_locally` (item V2_10) with the middle atlas as the covering family (A's
`IsChart.compatible` cannot be used: B (a) is for every topological space, not only Hausdorff
paracompact ones).  (b) is definitional.  (c) `→`: `P.atlas ∪ {φ}` is an atlas equivalent to
`P.atlas`; `←`: A's `isChart_congr` with the M-polyfold `⟨A⟩`.

`B → A`: `IsChart.compatible`, `isChart_congr` and `exists_isChart_mem_source` follow from B (a)
and (c) (two charts of the class lie in equivalent atlases; equivalent atlases have the same
class).  `IsChart.restrict` (restriction of a chart of the maximal atlas, not in the text's
Definition 2.13 nor in B) is proved directly by `Compatible.restrict_left` (item V2_10). -/

namespace RoundTrip.V2_12
open Polyfold Set

/-- The project's statement, universe instantiated at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.IsChart.compatible.{0}) ∧
    (type_of% @Polyfold.MPolyfold.IsChart.restrict.{0}) ∧
    (type_of% @Polyfold.MPolyfold.isChart_congr.{0}) ∧
    (type_of% @Polyfold.MPolyfold.exists_isChart_mem_source.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.IsChart.compatible.{0}, @Polyfold.MPolyfold.IsChart.restrict.{0},
    @Polyfold.MPolyfold.isChart_congr.{0}, @Polyfold.MPolyfold.exists_isChart_mem_source.{0}⟩

/-- Atlas equivalence is transitive (locality of compatibility). -/
theorem equiv_trans {X : Type} [TopologicalSpace X] {A₁ A₂ A₃ : MAtlas X} (h₁ : A₁.Equiv A₂)
    (h₂ : A₂.Equiv A₃) : A₁.Equiv A₃ := by
  rw [MAtlas.equiv_iff] at h₁ h₂ ⊢
  intro φ hφ ψ hψ
  exact MChart.compatible_of_locally φ ψ A₂.charts (fun χ hχ => h₁ φ hφ χ hχ)
    (fun χ hχ => h₂ χ hχ ψ hψ) (fun x _ => A₂.cover x)

theorem A_to_B : A → B := by
  rintro ⟨-, -, hcongr, -⟩ X _
  refine ⟨⟨MAtlas.Equiv.refl, MAtlas.Equiv.symm, equiv_trans⟩, fun 𝒜 => ?_, ?_⟩
  · constructor
    · rintro ⟨h2, hp, A, rfl⟩
      exact ⟨h2, hp, ⟨A⟩, rfl⟩
    · rintro ⟨h2, hp, P, rfl⟩
      exact ⟨h2, hp, P.atlas, rfl⟩
  · intro _ _ P φ
    constructor
    · intro hφ
      let D : MAtlas X :=
        { charts := insert φ P.atlas.charts
          compatible := by
            rintro ψ (rfl | hψ) χ (rfl | hχ)
            · exact MChart.compatible_self _
            · exact hφ χ hχ
            · exact (hφ ψ hψ).symm
            · exact P.atlas.compatible ψ hψ χ hχ
          cover := fun x => by
            obtain ⟨ψ, hψ, hx⟩ := P.atlas.cover x
            exact ⟨ψ, mem_insert_of_mem _ hψ, hx⟩ }
      refine ⟨D, ⟨D, ?_⟩, mem_insert _ _⟩
      exact (union_eq_self_of_subset_left (subset_insert _ _)).symm
    · rintro ⟨A, hA, hφA⟩
      exact (hcongr (P := P) (Q := ⟨A⟩) hA φ).2 fun ψ hψ => A.compatible φ hφA ψ hψ

/-- Equivalent atlases have the same class (from B (a)). -/
theorem classB_eq (hB : B) {X : Type} [TopologicalSpace X] {A₁ A₂ : MAtlas X}
    (h : A₁.Equiv A₂) : classB A₁ = classB A₂ := by
  ext A'
  exact ⟨fun h' => (hB X).1.trans ((hB X).1.symm h) h', fun h' => (hB X).1.trans h h'⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {X} _ _ _ P φ ψ hφ hψ => ?_, fun {X} _ _ _ P φ hφ s hs hso => ?_,
    fun {X} _ _ _ P Q h φ => ?_, fun {X} _ _ _ P x => ?_⟩
  · obtain ⟨A₁, h₁, hφ₁⟩ := ((hB X).2.2 P φ).1 hφ
    obtain ⟨A₂, h₂, hψ₂⟩ := ((hB X).2.2 P ψ).1 hψ
    have h₁₂ : A₁.Equiv A₂ := (hB X).1.trans ((hB X).1.symm h₁) h₂
    exact (MAtlas.equiv_iff A₁ A₂).1 h₁₂ φ hφ₁ ψ hψ₂
  · exact fun ψ hψ => (hφ ψ hψ).restrict_left hs hso
  · rw [(hB X).2.2 P φ, (hB X).2.2 Q φ, classB_eq hB h]
  · obtain ⟨φ, hφ, hx⟩ := P.atlas.cover x
    exact ⟨φ, ((hB X).2.2 P φ).2 ⟨P.atlas, (hB X).1.refl _, hφ⟩, hx⟩

#rt_check RoundTrip.V2_12.A_to_B [Polyfold.MPolyfold.IsChart.compatible,
  Polyfold.MPolyfold.IsChart.restrict, Polyfold.MPolyfold.isChart_congr,
  Polyfold.MPolyfold.exists_isChart_mem_source]
#rt_check RoundTrip.V2_12.B_to_A [Polyfold.MPolyfold.IsChart.compatible,
  Polyfold.MPolyfold.IsChart.restrict, Polyfold.MPolyfold.isChart_congr,
  Polyfold.MPolyfold.exists_isChart_mem_source]
#rt_overlap RoundTrip.V2_12.B_to_A [Polyfold.MPolyfold.IsChart.compatible,
  Polyfold.MPolyfold.IsChart.restrict, Polyfold.MPolyfold.isChart_congr,
  Polyfold.MPolyfold.exists_isChart_mem_source]

end RoundTrip.V2_12
