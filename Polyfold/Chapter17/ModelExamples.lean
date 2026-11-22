import Polyfold.Chapter17.ModelComparison
import Polyfold.Chapter17.OverlappingUniformizers

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 752–761): non-degenerate witnesses for Theorem 17.1.14, Lemma 17.1.15,
Theorem 17.1.18 and Theorem 17.1.27.  Numbers and pages are the 2021 text's.

# Witnesses for the models `X_Ψ`

* **The reflection model** (on `ℤ/2 ⋉ ℝ`, `reflectionConstruction`): `reflectionPairFamily`, two
  copies of the tautological uniformizer `Ψ₀`, and `reflectionSingleFamily`, one copy.
  `reflectionPair_model`: `X_Ψ` is a tame ep-groupoid, it has a morphism between its two pieces
  and an object with a non-trivial automorphism, and `Γ_Ψ` is an equivalence with `|Γ_Ψ|` a
  homeomorphism (Theorem 17.1.14, Lemma 17.1.15).  `reflection_comparison`: Theorem 17.1.18 for
  the one-copy and the two-copy families, and an object `p` of the weak fibred product with
  `τ(p) = (−1, 0)`, a morphism `0 → 0` of `C` other than the unit (Theorem 17.1.27).
* **The model of two different overlapping uniformizers** (`overlapConstruction`,
  `overlapCoveringFamily` with `Ψ₀ : ℤ/2 ⋉ ℝ`, `Ψ₁ : ℤ/2 ⋉ (−2, 2)`, `Ψ₂ : {1} ⋉ (1, 3)`):
  `overlap_model`: `X_Ψ` is tame, has a morphism from the piece of `Ψ₁` to the piece of `Ψ₂`
  over `(−1, −3/2)`, and `Γ_Ψ` is an equivalence; `overlap_comparison`: Theorem 17.1.18 for
  `{Ψ₀}` and `{Ψ₀, Ψ₁, Ψ₂}`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

open EPLocalization EPLocalization.EPLoc

namespace GCT.PolyfoldConstruction

/-! ### The reflection model -/

section ReflectionModel

open EpGroupoid.Examples

/-- The footprint of `Ψ₀` is `|C|`. -/
theorem reflectionUnif_footprint : reflectionUnif.1.footprint = univ := by
  refine eq_univ_of_forall fun z => ?_
  induction z using Quotient.inductionOn with
  | h x => exact reflectionUnif.1.mem_footprint_iff.2 ⟨x, rfl⟩

/-- **Two copies of the reflection uniformizer**, a covering family indexed by `Bool`. -/
def reflectionPairFamily : reflectionConstruction.CoveringFamily where
  ι := Bool
  Ψ := fun _ => reflectionUnif
  cover := eq_univ_of_forall fun z =>
    mem_iUnion.2 ⟨true, by
      rw [reflectionUnif_footprint]
      exact mem_univ z⟩

/-- **One copy of the reflection uniformizer**, a covering family indexed by `Unit`. -/
def reflectionSingleFamily : reflectionConstruction.CoveringFamily where
  ι := Unit
  Ψ := fun _ => reflectionUnif
  cover := eq_univ_of_forall fun z =>
    mem_iUnion.2 ⟨(), by
      rw [reflectionUnif_footprint]
      exact mem_univ z⟩

/-- **The non-degenerate witness of Theorem 17.1.14 and Lemma 17.1.15**: for two copies of `Ψ₀`,
`X_Ψ` is a tame ep-groupoid; `(0, 1, 0)` is a morphism from the piece `false` to the piece
`true`; `(0, (−1, 0), 0)` is an automorphism of `0` in the piece `false` other than the unit;
`Γ_Ψ` is an equivalence and `|Γ_Ψ|` a homeomorphism. -/
theorem reflectionPair_model :
    (reflectionConstruction.modelEpGroupoid reflectionPairFamily.Ψ).IsTame ∧
      (∃ m : reflectionConstruction.ModelMor reflectionPairFamily.Ψ,
        ((reflectionConstruction.modelEP reflectionPairFamily.Ψ).X.src m).1 = false ∧
          ((reflectionConstruction.modelEP reflectionPairFamily.Ψ).X.tgt m).1 = true) ∧
      (∃ m : reflectionConstruction.ModelMor reflectionPairFamily.Ψ,
        (reflectionConstruction.modelEP reflectionPairFamily.Ψ).X.src m =
            (reflectionConstruction.modelEP reflectionPairFamily.Ψ).X.tgt m ∧
          m ≠ (reflectionConstruction.modelEP reflectionPairFamily.Ψ).X.unit
            ((reflectionConstruction.modelEP reflectionPairFamily.Ψ).X.src m)) ∧
      (reflectionConstruction.modelFunctor reflectionPairFamily.Ψ).toFunctor.IsEquivalence ∧
      IsHomeomorph (reflectionConstruction.modelFunctor reflectionPairFamily.Ψ).orbitMap := by
  refine ⟨reflectionConstruction.isTame_modelEpGroupoid _ reflectionConstruction_isTame,
    ⟨⟨(false, true), ⟨(0 : Fin 1 → ℝ), GCT.reflection.toGroupoidStr.unit 0, (0 : Fin 1 → ℝ),
      rfl, one_smul _ _⟩⟩, rfl, rfl⟩,
    ⟨⟨(false, false), ⟨(0 : Fin 1 → ℝ), ((-1 : ℤˣ), 0), (0 : Fin 1 → ℝ), rfl, smul_zero _⟩⟩,
      rfl, fun h => ?_⟩, reflectionConstruction.lemma_17_1_15 reflectionPairFamily⟩
  have h' := congrArg (fun m : reflectionConstruction.ModelMor reflectionPairFamily.Ψ =>
    (m.2.mor : ℤˣ × (Fin 1 → ℝ)).1) h
  exact absurd h' (by decide)

/-- **The non-degenerate witness of Theorems 17.1.18 and 17.1.27**: for one and two copies of
`Ψ₀`, `f = f_{Ψ,Ψ'}` is a generalized isomorphism with `|Γ_Ψ'| ∘ |f| = |Γ_Ψ|` and `|f|` a
homeomorphism, and the weak fibred product has an object `p` (`q = 0` in the one copy, `0` in
the copy `true`, joined by `(−1, 0)`) whose canonical morphism `τ(p) : 0 → 0` is not the
unit. -/
theorem reflection_comparison :
    IsGeneralizedIso (reflectionConstruction.comparison reflectionSingleFamily
        reflectionPairFamily) ∧
      (reflectionConstruction.modelFunctor reflectionPairFamily.Ψ).orbitMap ∘
          EPLoc.orbitMap (reflectionConstruction.comparison reflectionSingleFamily
            reflectionPairFamily) =
        (reflectionConstruction.modelFunctor reflectionSingleFamily.Ψ).orbitMap ∧
      IsHomeomorph (EPLoc.orbitMap (reflectionConstruction.comparison reflectionSingleFamily
        reflectionPairFamily)) ∧
      ∃ p : (reflectionConstruction.modelFibredProduct reflectionSingleFamily.Ψ
          reflectionPairFamily.Ψ reflectionPairFamily.cover).Obj,
        ((reflectionConstruction.canonicalNatTrans reflectionSingleFamily.Ψ
            reflectionPairFamily.Ψ reflectionPairFamily.cover).app p).1 = ((-1 : ℤˣ), 0) ∧
          ((reflectionConstruction.canonicalNatTrans reflectionSingleFamily.Ψ
            reflectionPairFamily.Ψ reflectionPairFamily.cover).app p).1 ≠
            GCT.reflection.toGroupoidStr.unit 0 := by
  obtain ⟨h₁, -, -, h₄, h₅⟩ := reflectionConstruction.theorem_17_1_18 reflectionSingleFamily
    reflectionPairFamily reflectionPairFamily
  refine ⟨h₁, h₄, h₅, (reflectionConstruction.fibredProductObjEquiv _ _ _).symm
    ⟨((), true), ⟨(0 : Fin 1 → ℝ), ((-1 : ℤˣ), 0), (0 : Fin 1 → ℝ), rfl, smul_zero _⟩⟩, rfl,
    fun h => absurd (congrArg Prod.fst h) (by decide)⟩

end ReflectionModel

/-! ### The model of two different overlapping uniformizers -/

section OverlapModel

open EpGroupoid.Examples

/-- The one-element family `{Ψ₀}` of `overlapConstruction`. -/
def overlapSingleFamily : overlapConstruction.CoveringFamily where
  ι := Unit
  Ψ := fun _ => overlapUnif₀
  cover := eq_univ_of_forall fun z =>
    mem_iUnion.2 ⟨(), by
      rw [overlapUnif₀_footprint]
      exact mem_univ z⟩

/-- **The model of a covering family with two different overlapping uniformizers**
(`Ψ₁ : ℤ/2 ⋉ (−2, 2)`, `Ψ₂ : {1} ⋉ (1, 3)`, both in `F(3/2)`): `X_Ψ` is tame, it has a
morphism from the piece of `Ψ₁` to the piece of `Ψ₂` over `(−1, −3/2)`, and `Γ_Ψ` is an
equivalence with `|Γ_Ψ|` a homeomorphism. -/
theorem overlap_model :
    (overlapConstruction.modelEpGroupoid overlapCoveringFamily.Ψ).IsTame ∧
      (∃ m : overlapConstruction.ModelMor overlapCoveringFamily.Ψ,
        @Eq (Fin 3) ((overlapConstruction.modelEP overlapCoveringFamily.Ψ).X.src m).1 1 ∧
          @Eq (Fin 3) ((overlapConstruction.modelEP overlapCoveringFamily.Ψ).X.tgt m).1 2 ∧
          (overlapConstruction.modelFunctor overlapCoveringFamily.Ψ).mor m =
            ((-1 : ℤˣ), fun _ => -(3 / 2 : ℝ))) ∧
      (overlapConstruction.modelFunctor overlapCoveringFamily.Ψ).toFunctor.IsEquivalence ∧
      IsHomeomorph (overlapConstruction.modelFunctor overlapCoveringFamily.Ψ).orbitMap := by
  obtain ⟨⟨a, ha, -⟩, -, -⟩ := overlap_transition_nonempty
  exact ⟨overlapConstruction.isTame_modelEpGroupoid _ overlapConstruction_isTame,
    ⟨⟨((1 : Fin 3), (2 : Fin 3)), a⟩, rfl, rfl, ha⟩,
    overlapConstruction.lemma_17_1_15 overlapCoveringFamily⟩

/-- **Theorem 17.1.18 for `{Ψ₀}` and `{Ψ₀, Ψ₁, Ψ₂}`**: `f` is a generalized isomorphism with
`|Γ_Ψ'| ∘ |f| = |Γ_Ψ|`, and `|f|` is a homeomorphism. -/
theorem overlap_comparison :
    IsGeneralizedIso (overlapConstruction.comparison overlapSingleFamily overlapCoveringFamily) ∧
      (overlapConstruction.modelFunctor overlapCoveringFamily.Ψ).orbitMap ∘
          EPLoc.orbitMap (overlapConstruction.comparison overlapSingleFamily
            overlapCoveringFamily) =
        (overlapConstruction.modelFunctor overlapSingleFamily.Ψ).orbitMap ∧
      IsHomeomorph (EPLoc.orbitMap (overlapConstruction.comparison overlapSingleFamily
        overlapCoveringFamily)) :=
  let h := overlapConstruction.theorem_17_1_18 overlapSingleFamily overlapCoveringFamily
    overlapCoveringFamily
  ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩

end OverlapModel

end GCT.PolyfoldConstruction

end Polyfold
