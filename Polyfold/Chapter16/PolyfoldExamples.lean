import Polyfold.Chapter16.ZhouUniquenessCheck
import Polyfold.Chapter16.PolyfoldPartitions
import Polyfold.Chapter9.GeneralLevelZero

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.1: nonvacuity witnesses for **Definitions 16.1.3, 16.1.5, 16.1.14, 16.1.17, 16.1.20**.

# The polyfold `ℝ` with the structure `ℤ/3 × ℝ ⇉ ℝ`

`z3Polyfold` (the class of `z3PolyfoldStructure`, `ZhouUniquenessCheck.lean`) is tame
(`z3Polyfold_isTame`), admits sc-smooth bump functions (`z3Polyfold_admitsBumpFunctions`, the
Hilbert case of Theorem 5.5.7) and sc-smooth partitions of unity
(`z3Polyfold_admitsScPartitionsOfUnity`, Theorem 7.5.7), has degeneracy index `0`
(`z3Polyfold_degIndex`) and empty boundary (`z3Polyfold_boundary`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

namespace PolyfoldStructure

open EpGroupoid.Examples

/-- **Witness for Definition 16.1.20**: `z3Polyfold` is tame. -/
theorem z3Polyfold_isTame : z3Polyfold.IsTame :=
  ⟨z3PolyfoldStructure, rfl, rnPolyfold_isTame⟩

/-- **Witness for Definition 16.1.5 (1)**: `z3Polyfold` admits sc-smooth bump functions. -/
theorem z3Polyfold_admitsBumpFunctions : z3Polyfold.AdmitsBumpFunctions :=
  ⟨z3PolyfoldStructure, rfl, MPolyfold.admitsBumpFunctions_of_hilbert fun x => by
    obtain ⟨φ, h1, h2, h3, -⟩ := rnPolyfold_one_hilbert_hypothesis x
    exact ⟨φ, h1, h2, h3⟩⟩

/-- **Witness for Definition 16.1.5 (2)**: `z3Polyfold` admits sc-smooth partitions of unity. -/
theorem z3Polyfold_admitsScPartitionsOfUnity : z3Polyfold.AdmitsScPartitionsOfUnity :=
  ⟨z3PolyfoldStructure, rfl, trivialZ3EpGroupoid.theorem_7_5_7
    hasParacompactOrbitSpace_trivialZ3 (rnPolyfold_admitsScPartitionsOfUnity 1)⟩

/-- **Witness for Definition 16.1.14**: the degeneracy index of `z3Polyfold` vanishes. -/
theorem z3Polyfold_degIndex : z3Polyfold.degIndex = fun _ => 0 := by
  funext z
  obtain ⟨x, hx⟩ := trivialZ3EpGroupoid.surjective_π (z3PolyfoldStructure.β.symm z)
  have h : z3PolyfoldStructure.β (z3PolyfoldStructure.X.X.π x) = z := by
    change z3PolyfoldStructure.β (trivialZ3EpGroupoid.π x) = z
    rw [hx, Homeomorph.apply_symm_apply]
  exact (z3Polyfold.definition_16_1_14 z3PolyfoldStructure rfl h).trans
    (MPolyfold.degIndex_rn x)

/-- **Witness for Definition 16.1.17**: `∂ℝ = ∅` for `z3Polyfold`. -/
theorem z3Polyfold_boundary : z3Polyfold.boundary = ∅ := by
  ext z
  change 1 ≤ z3Polyfold.degIndex z ↔ False
  rw [z3Polyfold_degIndex]
  simp

end PolyfoldStructure

end Polyfold
