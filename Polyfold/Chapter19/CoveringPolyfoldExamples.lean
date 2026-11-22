import Polyfold.Chapter19.CoveringPolyfold
import Polyfold.Chapter19.CoveringLocalExamples

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19, §19.7
"Covering Constructions": the witness for **Proposition 19.7.26** (pp. 926–927), **Theorem
19.7.28** (pp. 928–929) and **Theorem 19.7.29** (pp. 929–930).  Numbers and pages are the 2021
text's.

# The absolute-value covering as a covering polyfold

The witness is the absolute-value example `absBasic` of `CoveringCounterexamples.lean`:
`P : ℤ/2 ⋉ (ℤˣ × ℝ) → ℤ/2 ⋉ ℝ`, with `F̂(β) = {absCU β}`, the global sheet model at `β = 0`.

* `absBasic_covering_polyfold_nondegenerate`: all hypotheses of the theorems of
  `CoveringPolyfold.lean` hold (finite-to-one covering, `IsCompatible`, `HasClassUniformizers`,
  `T_{|B|}` metrizable, tame domains), every `F̂(β)` is non-empty, the proper covering
  uniformizer at `0` has two sheets over `o_β = 0`, and its group `ℤ/2` acts non-trivially.
* `absBasic_proposition_19_7_26`, `absBasic_theorem_19_7_28_one`, `absBasic_theorem_19_7_29`:
  parts of the conclusions at `Ψ̂ = Ψ̂' = absCU 0`.
* `absPolyfoldCoveringFunctor`: the proper polyfold covering functor of Theorem 19.7.28 (3).
-/

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples GCT.PolyfoldConstruction
open Chapter19

/-- The metrizability of `T_{|B|}` for `absBasic` (the hypothesis of Theorem 19.7.25). -/
theorem absBasic_metrizableSpace :
    @MetrizableSpace _ (absBasic.toBasic.natTop absBasic_hasClassUniformizers.toBasic) :=
  not_theorem_19_7_25_four_b.1

/-- The domains of the uniformizers of `absBasic` are tame (the tame half of Proposition
19.7.26): each is an open subset of `ℝ`. -/
theorem absBasic_isTame (Ψ : absBasic.toBasic.U.Unif) : Ψ.1.P.IsTame := by
  obtain ⟨D, hD⟩ := absHatU_slice Ψ
  rw [hD]
  exact (MPolyfold.isLocalScDiffeo_subtypeVal D.isOpen).isTame rnPolyfold_isTame

/-- The member `Ψ̂ = absCU 0` of `F̂(0)` (the global sheet model at `0`). -/
def absUnifZero : absBasic.hatU.Unif := ⟨0, absCU 0, mem_singleton _⟩

/-- **Proposition 19.7.26 for `absBasic`** at `Ψ̂ = Ψ̂' = absCU 0`:
`p : M̂(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is a surjective local sc-diffeomorphism. -/
theorem absBasic_proposition_19_7_26 :
    haveI := absBasic.t2Space_MHat absCovP_isFiniteToOneCovering
    haveI := absBasic.paracompactSpace_MHat absCovP_isFiniteToOneCovering
    (absBasic.hatPolyfold absCovP_isFiniteToOneCovering absUnifZero absUnifZero).IsLocalScDiffeo
        (absBasic.basePolyfold absUnifZero absUnifZero) (absBasic.pB absUnifZero absUnifZero) ∧
      Surjective (absBasic.pB absUnifZero absUnifZero) :=
  (absBasic.proposition_19_7_26 absCovP_isFiniteToOneCovering absBasic_hasClassUniformizers
    absBasic_metrizableSpace absUnifZero absUnifZero).2.1

/-- **Theorem 19.7.28 (1) for `absBasic`** at `Ψ̂ = Ψ̂' = absCU 0`: `ŝ` and `t̂` are local
sc-diffeomorphisms. -/
theorem absBasic_theorem_19_7_28_one :
    haveI := absBasic.t2Space_MHat absCovP_isFiniteToOneCovering
    haveI := absBasic.paracompactSpace_MHat absCovP_isFiniteToOneCovering
    (absBasic.hatPolyfold absCovP_isFiniteToOneCovering absUnifZero absUnifZero).IsLocalScDiffeo
        absUnifZero.Ψh.E.PObj (absBasic.srcHat absUnifZero absUnifZero) ∧
      (absBasic.hatPolyfold absCovP_isFiniteToOneCovering absUnifZero absUnifZero).IsLocalScDiffeo
        absUnifZero.Ψh.E.PObj (absBasic.tgtHat absUnifZero absUnifZero) :=
  (absBasic.theorem_19_7_28_one_hyp absCovP_isFiniteToOneCovering absBasic_isCompatible
    absBasic_hasClassUniformizers absBasic_metrizableSpace absUnifZero absUnifZero
    absUnifZero).2.1.2.2

/-- **Theorem 19.7.29 for `absBasic`**: the polyfold construction of `B` has covering
uniformizers, and `Γ ₛ×_τ̂ Ψ̂` at `Ψ̂ = Ψ̂' = absCU 0` is injective. -/
theorem absBasic_theorem_19_7_29 :
    (absBasic.toBasic.toPolyfoldConstruction absBasic_metrizableSpace).HasCoveringUniformizers ∧
      Injective (absBasic.gammaFib absUnifZero absUnifZero) :=
  have h := absBasic.theorem_19_7_29_hyp absCovP_isFiniteToOneCovering absBasic_isCompatible
    absBasic_hasClassUniformizers absBasic_metrizableSpace absUnifZero absUnifZero
  ⟨h.1.1, h.2.2.2.2.1⟩

/-- **The proper polyfold covering functor of Theorem 19.7.28 (3) for `absBasic`**: two sheets of
`ℤ/2 ⋉ ℝ` over `ℤ/2 ⋉ ℝ` (`-1` acting by the reflection). -/
def absPolyfoldCoveringFunctor :=
  absBasic.toProperPolyfoldCoveringFunctor absCovP_isFiniteToOneCovering absBasic_isCompatible
    absBasic_hasClassUniformizers absBasic_metrizableSpace

/-- **The witness is non-degenerate**: the hypotheses of Theorems 19.7.28, 19.7.29 hold
(finite-to-one covering, `IsCompatible`, `F̂(β) ≠ ∅` on every class, `T_{|B|}` metrizable, tame
domains); the proper covering uniformizer at `0` has two sheets over `o_β = 0` and its group
`ℤ/2` acts non-trivially on `O = ℝ`. -/
theorem absBasic_covering_polyfold_nondegenerate :
    IsFiniteToOneCovering absCovP ∧ absBasic.IsCompatible ∧ absBasic.HasClassUniformizers ∧
      @MetrizableSpace _ (absBasic.toBasic.natTop absBasic_hasClassUniformizers.toBasic) ∧
      (∀ Ψ : absBasic.toBasic.U.Unif, Ψ.1.P.IsTame) ∧
      (∀ β, (absBasic.hatU.F β).Nonempty) ∧
      absUnifZero.Ψh.model.fiber.ncard = 2 ∧
      ∃ (g : absUnifZero.Ψh.Ψ.G) (o : absUnifZero.Ψh.Ψ.O), g • o ≠ o := by
  refine ⟨absCovP_isFiniteToOneCovering, absBasic_isCompatible, absBasic_hasClassUniformizers,
    absBasic_metrizableSpace, absBasic_isTame, fun β => ⟨absCU β, mem_singleton _⟩, ?_, ?_⟩
  · change (absCU 0).model.fiber.ncard = 2
    rw [absCU_zero]
    change (sheetModel (absSliceUnif overlapSlice₀).smooth_smul ℤˣ _ _).fiber.ncard = 2
    refine (congrArg Set.ncard (sheetModel_fiber _ _ _ _)).trans ?_
    rw [Set.ncard_prod, Set.ncard_univ]
    refine (congrArg (Nat.card ℤˣ * ·) (Set.ncard_singleton _)).trans ?_
    rw [mul_one, Nat.card_eq_fintype_card, Fintype.card_units_int]
  · change ∃ (g : (absCU 0).Ψ.G) (o : (absCU 0).Ψ.O), g • o ≠ o
    rw [absCU_zero]
    refine ⟨⟨-1, Subgroup.mem_top _⟩, ⟨fun _ => 1, mem_univ _⟩, fun h => ?_⟩
    have := congrFun (congrArg Subtype.val h) 0
    change ((-1 : ℤˣ) • (fun _ : Fin 1 => (1 : ℝ))) 0 = 1 at this
    rw [units_smul_rn_neg_one] at this
    norm_num at this

end GroupoidalCategory

end Polyfold
