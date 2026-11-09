import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_13

/-! Round trip for V7_13 (Proposition 7.3, pp. 229–230: the local closure relation).

`A` is the conjunction of the types of the two listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `EpGroupoid.proposition_7_1_10` (`∀ x, ∃ U, IsOpen U ∧ x ∈ U ∧ ∀ A ⊆ U,
π '' closure A = closure (π '' A)`) and `EpGroupoid.proposition_7_1_10_of_isProperMap` (for every
`U` with `t : s⁻¹(cl U) → X` proper, the relation holds for all `A ⊆ cl U`).  The project's
topology on `X.OrbitSpace` is Mathlib's quotient instance, definitionally `B`'s `orbitTop X`.

* `A → B`: `B` is `proposition_7_1_10`, with the redundant `z = π x` dropped.
* `B → A`: `proposition_7_1_10` is `B` at `z = π x`.  `proposition_7_1_10_of_isProperMap` is not a
  consequence of `B` (`B` gives *some* `U` per point; the conjunct is about every `U` with the
  properness property and every `A ⊆ cl U`); it is re-proved outright here, by the project's
  argument (the saturation `π⁻¹(π A) = t(s⁻¹ A)`, Proposition 7.1 — an item theorem of V7_11,
  not of this item — and closedness of `t(s⁻¹(cl A))` for proper `t`). -/

namespace RoundTrip.V7_13
open Polyfold Topology Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.proposition_7_1_10.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_7_1_10_of_isProperMap.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.proposition_7_1_10.{0}, @Polyfold.EpGroupoid.proposition_7_1_10_of_isProperMap.{0}⟩

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X z x _
  exact hA.1 X x

/-! ### `B → A` -/

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- The saturation `π⁻¹(π(A)) = t(s⁻¹(A))` (re-proved; the project's version is private). -/
theorem preimage_π_image_eq' (A : Set Obj) :
    X.π ⁻¹' (X.π '' A) = X.tgt '' (X.src ⁻¹' A) := by
  ext y
  constructor
  · rintro ⟨a, ha, hay⟩
    obtain ⟨φ, rfl, rfl⟩ := (X.π_eq_π_iff).1 hay
    exact ⟨φ, ha, rfl⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨X.src φ, hφ, X.π_src_eq_π_tgt φ⟩

/-- `proposition_7_1_10_of_isProperMap`, re-proved outright. -/
theorem proposition_7_3_of_isProperMap' {U A : Set Obj}
    (hU : IsProperMap ((X.src ⁻¹' closure U).domRestrict X.tgt)) (hA : A ⊆ closure U) :
    X.π '' closure A = closure (X.π '' A) := by
  refine (image_closure_subset_closure_image X.continuous_π).antisymm fun z hz => ?_
  obtain ⟨y, rfl⟩ := X.surjective_π z
  have hy : y ∈ closure (X.tgt '' (X.src ⁻¹' A)) := by
    rw [← preimage_π_image_eq',
      ← X.proposition_7_1_8.preimage_closure_eq_closure_preimage X.continuous_π]
    exact hz
  have hcl : IsClosed (X.tgt '' (X.src ⁻¹' closure A)) :=
    isClosed_image_preimage_of_isProperMap_domRestrict hU (closure_minimal hA isClosed_closure)
      (isClosed_closure.preimage X.continuous_src)
  obtain ⟨φ, hφ, rfl⟩ :=
    (hcl.closure_subset_iff.2 (image_mono (preimage_mono subset_closure))) hy
  exact ⟨X.src φ, hφ, X.π_src_eq_π_tgt φ⟩

end

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X x
    exact hB Obj Mor X (X.π x) x rfl
  · intro Obj Mor _ _ _ _ _ _ X U A hU hA
    exact proposition_7_3_of_isProperMap' X hU hA

#rt_check RoundTrip.V7_13.A_to_B [Polyfold.EpGroupoid.proposition_7_1_10,
  Polyfold.EpGroupoid.proposition_7_1_10_of_isProperMap]
#rt_check RoundTrip.V7_13.B_to_A [Polyfold.EpGroupoid.proposition_7_1_10,
  Polyfold.EpGroupoid.proposition_7_1_10_of_isProperMap]
#rt_overlap RoundTrip.V7_13.B_to_A [Polyfold.EpGroupoid.proposition_7_1_10,
  Polyfold.EpGroupoid.proposition_7_1_10_of_isProperMap]

end RoundTrip.V7_13
