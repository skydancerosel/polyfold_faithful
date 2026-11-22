import Polyfold.Chapter19.BasicRegularity
import Polyfold.Chapter19.MetrizabilityExamples
import Polyfold.Chapter17.Subpolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.5 "The polyfold structure for `(S, T)`" (pp. 886–890): witnesses for the hypotheses of
Theorems 19.5.1 and 19.5.3, Corollary 19.5.2 and Propositions 19.5.7 and 19.5.11.  Numbers and
pages are the 2021 text's.

# The polyfold structure for `(S, T)`: witnesses

## The constructions

* `reflectionBasic` (`ℤ/2 ⋉ ℝ`, reflection; `BasicConstructionExamples`): `T` is metrizable,
  the properness condition holds and the domain `ℝ` is tame; the isotropy group of `0` is
  `ℤ/2`, acting non-trivially near `0`, and (LUC) of Definition 19.5.8 holds.
* `z3Basic` (`ℤ/3 ⋉ ℝ`, trivial action): `T` is metrizable and (ZHOU) of Definition 19.5.6
  holds, with smooth classes (`z3Basic_isSmoothClass`) and isotropy `ℤ/3` everywhere.

## What is formalized

* `reflectionBasic_theorem_19_5_1`, `reflectionBasic_corollary_19_5_2`,
  `reflectionBasic_theorem_19_5_3_one`, `reflectionBasic_theorem_19_5_3_two_tame`,
  `reflectionBasic_isLUC`.
* `z3Basic_hB`, `z3Basic_metrizableSpace`, `z3Basic_isSmoothClass`, `z3Basic_isZhou`,
  `z3Basic_proposition_19_5_7`, `z3Basic_proposition_19_5_11`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace Filter

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

open EpGroupoid.Examples BasicConstruction

/-! ### `reflectionBasic` -/

section Reflection

/-- **Theorem 19.5.1 for `reflectionBasic`** (its hypotheses hold: `T` is metrizable). -/
theorem reflectionBasic_theorem_19_5_1 (Ψ Ψ' : reflectionBasic.U.Unif) :
    (reflectionBasic.transPolyfold Ψ Ψ').IsLocalScDiffeo Ψ.1.P
        (fun a : reflectionBasic.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) ∧
      (reflectionBasic.transPolyfold Ψ Ψ').IsLocalScDiffeo Ψ'.1.P
        (fun a : reflectionBasic.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).tgt) :=
  let h := reflectionBasic.theorem_19_5_1 reflectionBasic_hB reflectionBasic_metrizableSpace Ψ Ψ'
  ⟨h.1, h.2.1⟩

/-- **Corollary 19.5.2 for `reflectionBasic`**. -/
theorem reflectionBasic_corollary_19_5_2 (Ψ Ψ' : reflectionBasic.U.Unif) :
    Ψ.1.P.IsScSmoothMap (reflectionBasic.transPolyfold Ψ Ψ)
        (fun o => reflectionBasic.rep.toTr (GroupoidStr.TransitionSet.unit o : Ψ.1.Trans Ψ.1)) ∧
      (reflectionBasic.transPolyfold Ψ Ψ').IsScSmoothMap (reflectionBasic.transPolyfold Ψ' Ψ)
        (fun a : reflectionBasic.M Ψ Ψ' => reflectionBasic.rep.toTr (a : Ψ.1.Trans Ψ'.1).inv) :=
  let h := reflectionBasic.corollary_19_5_2 Ψ Ψ' Ψ'
  ⟨h.1, h.2.1⟩

/-- **Theorem 19.5.3 (1) for `reflectionBasic`**: properness holds and `T` is paracompact. -/
theorem reflectionBasic_theorem_19_5_3_one :
    @MetrizableSpace _ (reflectionBasic.natTop reflectionBasic_hB) :=
  reflectionBasic.theorem_19_5_3_one reflectionBasic_hB reflectionBasic_propernessV2
    (Or.inr (by
      let _ := reflectionBasic.natTop reflectionBasic_hB
      have := reflectionBasic_metrizableSpace
      exact paracompactSpace_of_metrizableSpace _))

/-- The domains of the uniformizers of `reflectionBasic` are tame (the hypothesis of the tame half
of Theorem 19.5.3 (2)). -/
theorem reflectionBasic_isTame (Ψ : reflectionBasic.U.Unif) : Ψ.1.P.IsTame := by
  rw [translationUnif_eq _ Ψ]
  exact rnPolyfold_isTame

/-- **Theorem 19.5.3 (2), tame half, for `reflectionBasic`**. -/
theorem reflectionBasic_theorem_19_5_3_two_tame :
    (toPolyfoldConstruction reflectionBasic_metrizableSpace).IsTame ∧
      (∀ Ψ Ψ' : (toPolyfoldConstruction reflectionBasic_metrizableSpace).Unif,
        ((toPolyfoldConstruction reflectionBasic_metrizableSpace).transPolyfold Ψ Ψ').IsTame) ∧
      ∀ c : (toPolyfoldConstruction reflectionBasic_metrizableSpace).CoveringFamily,
        ((toPolyfoldConstruction reflectionBasic_metrizableSpace).modelEP c.Ψ).X.IsTame :=
  (theorem_19_5_3_two reflectionBasic_metrizableSpace).2.2.2.2 reflectionBasic_isTame

/-- **(LUC) of Definition 19.5.8 for `reflectionBasic`** (at `0` the isotropy group is `ℤ/2`). -/
theorem reflectionBasic_isLUC : reflectionBasic.IsLUC := fun z => by
  obtain ⟨x, rfl⟩ :=
    (GroupoidalCategory.translation ℤˣ (Fin 1 → ℝ)).toGroupoidStr.surjective_π z
  exact ⟨x, tautUniformizer (rnPolyfold 1) isScSmoothMap_units_smul, rfl, x, rfl, rfl,
    (Uniformizer.isLUCAt_iff (tautUniformizer (rnPolyfold 1) isScSmoothMap_units_smul) x).2
      (isLUC_reflection x)⟩

end Reflection

/-! ### `z3Basic` -/

section Z3

theorem z3Basic_hB : z3Basic.U.HasClassUniformizers :=
  (translationBasic_hasUniformizers _).hasClassUniformizers

/-- The natural topology of `z3Basic` is metrizable (`|Ψ₀|` is onto). -/
theorem z3Basic_metrizableSpace : @MetrizableSpace _ (z3Basic.natTop z3Basic_hB) :=
  z3Basic.metrizableSpace_natTop_of_surjective z3Basic_hB (α := 0)
    (Ψ := tautUniformizer (rnPolyfold 1) isScSmoothMap_z3_smul) rfl fun z => by
      obtain ⟨x, rfl⟩ := (GroupoidalCategory.translation (Multiplicative (ZMod 3))
        (Fin 1 → ℝ)).toGroupoidStr.surjective_π z
      exact ⟨x, rfl⟩

/-- `z3Basic` has a smooth class (so (ZHOU) is not vacuous). -/
theorem z3Basic_isSmoothClass :
    z3Basic.IsSmoothClass
      ((GroupoidalCategory.translation (Multiplicative (ZMod 3)) (Fin 1 → ℝ)).π 0) :=
  ⟨⟨tautUniformizer (rnPolyfold 1) isScSmoothMap_z3_smul, 0, rfl⟩, 0,
    GCT.PolyfoldConstruction.rn_one_zero_mem_smoothSet,
    rfl⟩

/-- **(ZHOU) of Definition 19.5.6 for `z3Basic`**. -/
theorem z3Basic_isZhou : z3Basic.IsZhou := by
  rintro z ⟨⟨Ψ, α, hΨ⟩, q, hq, rfl⟩
  have hΨ' : Ψ = tautUniformizer (rnPolyfold 1) isScSmoothMap_z3_smul := hΨ
  subst hΨ'
  exact ⟨_, _, rfl, (rnPolyfold 1).smoothMk q hq, rfl, rfl,
    fun _ _ _ => Eventually.of_forall fun _ => rfl⟩

/-- **Proposition 19.5.7 for `z3Basic`**. -/
theorem z3Basic_proposition_19_5_7 : (toPolyfoldConstruction z3Basic_metrizableSpace).IsZhou :=
  proposition_19_5_7 z3Basic_metrizableSpace z3Basic_isZhou

/-- **Proposition 19.5.11 for `z3Basic`**. -/
theorem z3Basic_proposition_19_5_11 :
    z3Basic.IsSLUC ∧ z3Basic.IsSLR ∧ z3Basic.IsLUC ∧ z3Basic.IsLR :=
  proposition_19_5_11 z3Basic_metrizableSpace z3Basic_isZhou

end Z3

end GroupoidalCategory

end Polyfold
