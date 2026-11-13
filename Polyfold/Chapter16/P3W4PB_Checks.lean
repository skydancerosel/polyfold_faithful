import Polyfold.Chapter16.P3W4PB_Multisections
import Polyfold.Chapter16.P3W3V_UniquenessCheck

/-!
# Chapter 16, §16.5: the representative-independence checks on V's ℤ/3 example

Agent PB of Part III, wave 4.

Definition 16.5.1 (2021 p. 733; 2017: Definition 16.35) relates two representatives
`(Λ, W)`, `(Λ', W')` when `Λ = f̄*Λ'` for a generalized isomorphism `f̄` with `Γ' ∘ |f̄| = Γ`.
Such an `f̄` is not unique for non-effective targets (`uniqueness_16_3_3_counterexample`: on the
trivial-action ℤ/3 example both `[1_W]` and `[W ←1 W →Inv W]` qualify).  The relation does not
depend on that choice: `pullMult_eq_of_Γ` computes `f̄*Λ'` from `λ` and `Γ` alone.  Here the
check on the ℤ/3 example itself: the two pull-backs of every multisection functor agree.
-/

open Set Function

universe u

namespace Polyfold

open EPLocalization SBLocalization StrongPolyfoldBundleStructure
open EpGroupoid.Examples StrongBundleLocalizationExamples LocalizationLRCounterexample

namespace StrongPolyfoldBundle

variable (k : ℕ)

/-- **Definition 16.5.1 on the ℤ/3 example** (2021 p. 733): the two generalized isomorphisms of
`uniqueness_16_3_3_counterexample` pull every multisection functor `Λ` back to the same functor,
so the relation of Definition 16.5.1 does not depend on the choice of `f̄` there. -/
theorem pullMult_z3_independent (Λ : (z3SEP k).W → ℚ≥0) (hΛ : IsWFunctor (z3SEP k) Λ) :
    GenSBMap.pullMult (uniqueness_16_3_3_counterexample k).1 Λ =
      GenSBMap.pullMult (uniqueness_16_3_3_counterexample k).2.1 Λ := by
  have hcomm : ∀ w', Λ (((z3Structure k).Γ.symm
      ((z3Structure k).Γ ((z3Structure k).A.E.toEpGroupoid.π w'))).out) = Λ w' := by
    intro w'
    refine hΛ.eq_of_π_eq ?_
    rw [Homeomorph.symm_apply_apply]
    exact Quotient.out_eq _
  funext w
  exact (pullMult_eq_of_Γ (S := z3Structure k) (S' := z3Structure k)
    (uniqueness_16_3_3_counterexample k).1 (uniqueness_16_3_3_counterexample k).2.2.2.1 hΛ
    (lam := fun y => Λ ((z3Structure k).Γ.symm y).out) hcomm w).trans
    (pullMult_eq_of_Γ (S := z3Structure k) (S' := z3Structure k)
    (uniqueness_16_3_3_counterexample k).2.1 (uniqueness_16_3_3_counterexample k).2.2.2.2.2.1 hΛ
    (lam := fun y => Λ ((z3Structure k).Γ.symm y).out) hcomm w).symm

end StrongPolyfoldBundle

end Polyfold
