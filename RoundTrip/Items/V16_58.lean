import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_58

set_option maxSynthPendingDepth 3

/-! Round trip for V16_58 (2021 Theorem 16.3.17 (2), p. 728; 2017: Theorem 16.4 (2)).

`A` is the conjunction of the types of `StrongPolyfoldBundle.theorem_16_3_17_two` (main
conjunct), `theorem_16_3_17_two_hyp` (the same with the reflexive local step `hloc` as a hypothesis
in place of tameness), `theorem_16_3_17_two_hyp_witness` (the hypotheses of the `_hyp` form are
satisfiable) and `EpStrongBundle.hasReflexiveLocalExtensions_of_isTame` (the local step for tame
`X`), all at universe `0` (the ep-level lemma at the universe of the models of bundles over
`Type`, the one the project uses).

Main conjunct vs `B`.  `A`'s main conjunct assumes `c.IsTame`, `IsAuxNormBoundary n` and a
structure `S ∈ c̄` with `S.A.E.HasReflexiveFibers` in which `normOf n` is a reflexive auxiliary
norm over `∂X`.  `B` assumes `c.polyfold.IsTame` (`= c.IsTame` by definition),
`c.HasReflexiveFibers` (reflexive fibres in SOME structure) and `IsAuxNormBoundary n` with SOME
`S ∈ c̄` in which `normOf n` is reflexive over `∂X`.  The two differ only in whether the reflexive
fibres sit in the same structure as the reflexive norm; `HasReflexiveFibers.of_mem` (Definition
16.3.12, "and then all") closes the gap.  Equivalent.

The three side conjuncts do not follow from `B` (the `_hyp` form assumes no tameness; the witness
and the ep-level local step are not about the extension); they are re-proved outright from
non-item lemmas (the project's proofs: `EpStrongBundle.theorem_12_2_13_hyp`,
`StrongBundle.exists_reflexiveLocalExtension_of_isTame`, `theorem_12_2_11_exists`,
`hasReflexiveLocalExtensions_of_isReflexiveAuxNorm`, `descend` lemmas). -/

namespace RoundTrip.V16_58
open Polyfold StrongPolyfoldBundle StrongPolyfoldBundleStructure

def A : Prop :=
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp_witness.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame.{0})

theorem A_holds : A :=
  ⟨@Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp_witness.{0},
    @Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame.{0}⟩

theorem Amain_to_B : (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two.{0}) → B := by
  intro h Y Z _ _ p c hc hrf n ⟨hn, S, hS, hr⟩
  exact h hc hn hS (hrf.of_mem hS) hr

theorem B_to_Amain : B → (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two.{0}) := by
  intro hB Y Z _ _ p c hc n hn S hS hBf hr
  exact hB c hc ⟨S, hS, hBf⟩ n ⟨hn, S, hS, hr⟩

theorem A_to_B : A → B := fun h => Amain_to_B h.1

/-- The ep-level local step for tame `X`, re-proved (the project's proof). -/
theorem hasReflexiveLocalExtensions_of_isTame' :
    type_of% @Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame.{0} := by
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E hX hB N hN
  exact fun _ hx => StrongBundle.exists_reflexiveLocalExtension_of_isTame hX hB hN.continuousOn
    (fun y hy => (hN.fiber y hy).isFiberSeminorm) hN.tendsto_zeroOne hN.le_liminf hx

/-- `theorem_16_3_17_two_hyp`, re-proved (the project's proof). -/
theorem theorem_16_3_17_two_hyp' :
    type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp.{0} := by
  intro Y Z _ _ p c n hn S hS hB hr hloc
  obtain ⟨Ñ, hÑ, hÑn⟩ := EpStrongBundle.theorem_12_2_13_hyp S.paracompact hB hr hloc
  refine ⟨S.descend Ñ, ⟨isAuxNorm_descend hS hÑ.toIsAuxNorm, S, hS, ?_⟩, fun y hy hb => ?_⟩
  · rw [S.normOf_descend hÑ.toIsAuxNorm.isOneInvariant]; exact hÑ
  · rw [c.Y01_eq hS] at hy
    obtain ⟨e, rfl⟩ := hy
    rw [S.descend_oneToY hÑ.toIsAuxNorm.isOneInvariant]
    have hb' : S.A.P (S.A.B.oneVal e) ∈ S.A.X.PObj.boundary := by
      rw [← hS] at hb
      exact (PolyfoldClass.mem_boundary_iff _ S.toPolyfoldStructure rfl
        (S.p_Γ (S.A.E.toEpGroupoid.π (S.A.B.oneVal e))).symm).1 hb
    exact hÑn e hb'

/-- `theorem_16_3_17_two_hyp_witness`, re-proved (the project's proof). -/
theorem theorem_16_3_17_two_hyp_witness' :
    type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp_witness.{0} := by
  intro Y Z _ _ p c hc
  obtain ⟨S, hS, hB⟩ := hc
  obtain ⟨N, hN⟩ := S.A.E.theorem_12_2_11_exists S.paracompact hB
  have hn := isAuxNorm_descend hS hN.toIsAuxNorm
  have e : S.normOf (S.descend N) = N := S.normOf_descend hN.toIsAuxNorm.isOneInvariant
  refine ⟨S.descend N, S, fun S' hS' => (hn S' hS').isAuxNormOn _, hS, hB, ?_, ?_⟩
  · rw [e]; exact hN.isReflexiveAuxNormOn _
  · rw [e]; exact EpStrongBundle.hasReflexiveLocalExtensions_of_isReflexiveAuxNorm hN

theorem B_to_A : B → A := fun hB =>
  ⟨B_to_Amain hB, theorem_16_3_17_two_hyp', theorem_16_3_17_two_hyp_witness',
    hasReflexiveLocalExtensions_of_isTame'⟩

#rt_check RoundTrip.V16_58.A_to_B [Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp_witness,
  Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame]
#rt_check RoundTrip.V16_58.B_to_A [Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp_witness,
  Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame]
#rt_check RoundTrip.V16_58.Amain_to_B [Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp_witness,
  Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame]
#rt_check RoundTrip.V16_58.B_to_Amain [Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp_witness,
  Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame]
#rt_overlap RoundTrip.V16_58.B_to_A [Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_two_hyp_witness,
  Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame]

end RoundTrip.V16_58
