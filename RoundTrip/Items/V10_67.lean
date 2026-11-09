import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_67

/-! Round trip for V10_67 (2021 Theorem 10.5.7 = 2017 Theorem 10.10: between strong bundles with
the local regularity property, generalized strong bundle isomorphisms with the same orbit map
are equal; does not hold as we read it).

The item lists the definition `SBLocalization.Theorem_10_5_7` (the project's transcription, with
the project's `EpStrongBundle.IsLR`; vocabulary) and three theorems; `A` is the conjunction of
their types (none has universe parameters; `Theorem_10_5_7` is stated in universe `0`):
`LocalizationLRCounterexample.not_theorem_10_5_7` (`¬ Theorem_10_5_7`),
`LocalizationLRCounterexample.isLR_z3EpBundle` (the trivial bundle `ℝ × ℝᵏ → ℝ` over
`ℤ/3 × ℝ ⇉ ℝ`, trivial `μ`, has the project's (LR)) and
`StrongBundleLocalizationExamples.remark_10_5_5` (`[W ←1 W →Inv W]` and `[1_W]` are generalized
strong bundle isomorphisms with the same orbit map, and differ, already on the bases).

`B` is the text read literally, with the blind author's (LR) `IsLRB` (Definition 8.4.2 tested on
all strong bundle isomorphisms of `W|U(x)`, not only on global strong bundle maps as the
project's `IsLR` does).  As its author predicted, `B` does not hold as we read it.

* `not_B`: the bundle `z3SEP 0` has `IsLRB` (`isLRB_z3`: `μ` is the projection, so an
  `IsoW`-preserving `Φ` is the identity, which is the natural lift of `1`); `B` applied to
  `[W ←1 W →Inv W]` and `[1_W]` would identify them, but their base classes are separated by the
  isotropy relation at the generator of `ℤ/3` (the non-item `isotropyRel_id`,
  `not_isotropyRel_inv`, `Diagram.Equiv.isotropyRel_iff`).  This re-does the argument of
  `remark_10_5_5` from non-item lemmas.
* `not_A_to_B : ¬ (A → B)`; `B_to_A` only ex falso.
* `A_to_notB : A → ¬ B`: `A`'s own counterexample (`remark_10_5_5`) refutes `B` too, since it
  also satisfies `B`'s (LR). -/

namespace RoundTrip.V10_67
open Polyfold Polyfold.SBLocalization CategoryTheory
open Polyfold.StrongBundleLocalizationExamples Polyfold.EpGroupoid.Examples

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.LocalizationLRCounterexample.not_theorem_10_5_7) ∧
  (type_of% @Polyfold.LocalizationLRCounterexample.isLR_z3EpBundle) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.remark_10_5_5)

theorem A_holds : A :=
  ⟨@Polyfold.LocalizationLRCounterexample.not_theorem_10_5_7,
    @Polyfold.LocalizationLRCounterexample.isLR_z3EpBundle,
    @Polyfold.StrongBundleLocalizationExamples.remark_10_5_5⟩

/-- The bundle `ℝ × ℝ⁰ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` (trivial `μ`) has `B`'s local regularity
property: `μ(φ, w) = w`, so `IsoW E w (Φ w)` forces `Φ w = w = 1 ∗ w`. -/
theorem isLRB_z3 : IsLRB (z3SEP 0).E := by
  intro x O hO hxO
  obtain ⟨R, hRO⟩ := trivialZ3EpGroupoid.theorem_7_1 x hO hxO
  refine ⟨R, hRO, fun β Φ _ hiso => ⟨1, fun w hw => ?_⟩⟩
  obtain ⟨φ, h, hφ⟩ := hiso w hw
  exact hφ.symm

/-- `[W ←1 W →Inv W] ≠ [1_W]` (already on the bases), from non-item lemmas. -/
theorem cls_inv_ne_cls_id :
    (SDiagram.ofHom (z3InvHom 0)).cls ≠ (SDiagram.id (z3SEP 0)).cls := by
  intro h
  have he := EPLocalization.EPLoc.homMk_eq_homMk_iff.1 (congrArg GenSBMap.base h)
  exact not_isotropyRel_inv 0 ((he.isotropyRel_iff _ _).2 (isotropyRel_id 0))

theorem not_B : ¬ B := by
  intro hB
  exact cls_inv_ne_cls_id (hB (z3SEP 0) (z3SEP 0) isLRB_z3 isLRB_z3 _ _
    (GenSBMap.isGeneralizedIso_ofHom (z3InvHom_mem_equivalences 0))
    (GenSBMap.isGeneralizedIso_ofHom (SEP.equivalences.id_mem _)) (orbitMap_ofHom_z3InvHom 0))

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B → A` only ex falso. -/
theorem B_to_A : B → A := fun h => absurd h not_B

/-- `A`'s counterexample refutes `B` as well (it also has `B`'s (LR)). -/
theorem A_to_notB : A → ¬ B := by
  rintro ⟨-, -, hrem⟩ hB
  obtain ⟨hInv, hId, horb, -, hne⟩ := hrem 0
  exact hne (hB (z3SEP 0) (z3SEP 0) isLRB_z3 isLRB_z3 _ _ hInv hId horb)

#rt_check RoundTrip.V10_67.not_B [Polyfold.LocalizationLRCounterexample.not_theorem_10_5_7,
  Polyfold.LocalizationLRCounterexample.isLR_z3EpBundle,
  Polyfold.StrongBundleLocalizationExamples.remark_10_5_5]
#rt_check RoundTrip.V10_67.B_to_A [Polyfold.LocalizationLRCounterexample.not_theorem_10_5_7,
  Polyfold.LocalizationLRCounterexample.isLR_z3EpBundle,
  Polyfold.StrongBundleLocalizationExamples.remark_10_5_5]
#rt_check RoundTrip.V10_67.A_to_notB [Polyfold.LocalizationLRCounterexample.not_theorem_10_5_7,
  Polyfold.LocalizationLRCounterexample.isLR_z3EpBundle,
  Polyfold.StrongBundleLocalizationExamples.remark_10_5_5]
#rt_overlap RoundTrip.V10_67.B_to_A [Polyfold.LocalizationLRCounterexample.not_theorem_10_5_7,
  Polyfold.LocalizationLRCounterexample.isLR_z3EpBundle,
  Polyfold.StrongBundleLocalizationExamples.remark_10_5_5]

#print axioms RoundTrip.V10_67.not_B

end RoundTrip.V10_67
