import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_28

set_option maxSynthPendingDepth 3

/-! Round trip for V16_28 (2021 Theorem 16.4.6, p. 732; 2017: Theorem 16.5: Stokes for
branched suborbifolds of a polyfold).

`A` is the conjunction of the types of the item's 25 theorems, at universe `0` (the three
witnesses have no universe parameter): the four identities on representatives with
`HasEpStokes` (`_of_epStokes`), with sc-smooth partitions of unity (`_hyp`, `_both_hyp`), and
unconditionally (`_all`, `_both_all`); the ep-groupoid level assertions
`EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity`, `EP.stokesWithoutPartitions_all`,
`EP.theorem_9_5_17_all`, `EP.theorem_9_5_18_all`, `EP.theorem_9_5_17_dim1_all`,
`EP.theorem_9_5_18_dim1_all` (Stokes for **every** ep-groupoid, no partitions of unity);
`hasEpStokes_all`, `hasEpStokes_of_admitsScPartitionsOfUnity`; and three witnesses.

* `A_to_B` (through `main_A_to_B`): the class integral is computed on every representative
  (`OrientedSuborbifold.integral_eq`, `integralEff_eq`), so `B`'s equations are the four `_all`
  identities; `B`'s existence clause is `θ.out` (`isCompactBranched_of_mk`,
  `isTameOriented_iff`).
* `main_B_to_A`: the four `_all` identities from `B` applied to `⟦a⟧`, whose hypotheses
  (compact, tame, `n`-dimensional, tame oriented) come from the representative (`hyps`).
* `B_to_A` is **not** proved: `A` contains Stokes' theorem on the ep-groupoid level for every
  ep-groupoid (`EP.stokesWithoutPartitions_all`, `EP.theorem_9_5_17_all`, ...), while `B` only
  speaks of polyfolds, whose ep-groupoids have a paracompact orbit space and satisfy (ZHOU).
  For an ep-groupoid without these there is no polyfold to apply `B` to; deriving those
  conjuncts would mean re-proving the Chapter 9 Stokes theorems. -/

namespace RoundTrip.V16_28
open Polyfold Polyfold.PolyfoldClass

/-- The project's statement (universe `0`; the three witnesses have no universe parameter). -/
def A : Prop :=
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_of_epStokes.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_of_epStokes.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_of_epStokes.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_of_epStokes.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.hasEpStokes_of_admitsScPartitionsOfUnity.{0}) ∧
  (type_of% @Polyfold.EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity.{0}) ∧
  (type_of% @Polyfold.EP.stokesWithoutPartitions_witness) ∧
  (type_of% @Polyfold.PolyfoldClass.hasEpStokes_witness) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_hyp.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_hyp.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_hyp.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_hyp.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_both_hyp.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_hyp_witness) ∧
  (type_of% @Polyfold.EP.stokesWithoutPartitions_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.hasEpStokes_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_both_all.{0}) ∧
  (type_of% @Polyfold.EP.theorem_9_5_17_all.{0}) ∧
  (type_of% @Polyfold.EP.theorem_9_5_18_all.{0}) ∧
  (type_of% @Polyfold.EP.theorem_9_5_17_dim1_all.{0}) ∧
  (type_of% @Polyfold.EP.theorem_9_5_18_dim1_all.{0})

theorem A_holds : A :=
  ⟨@Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_of_epStokes.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_of_epStokes.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_of_epStokes.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_of_epStokes.{0},
    @Polyfold.PolyfoldClass.hasEpStokes_of_admitsScPartitionsOfUnity.{0},
    @Polyfold.EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity.{0},
    @Polyfold.EP.stokesWithoutPartitions_witness,
    @Polyfold.PolyfoldClass.hasEpStokes_witness,
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_hyp.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_hyp.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_hyp.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_hyp.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_both_hyp.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_hyp_witness,
    @Polyfold.EP.stokesWithoutPartitions_all.{0},
    @Polyfold.PolyfoldClass.hasEpStokes_all.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_all.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_all.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_all.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_all.{0},
    @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_both_all.{0},
    @Polyfold.EP.theorem_9_5_17_all.{0},
    @Polyfold.EP.theorem_9_5_18_all.{0},
    @Polyfold.EP.theorem_9_5_17_dim1_all.{0},
    @Polyfold.EP.theorem_9_5_18_dim1_all.{0}⟩

/-- The text's claim as the project states it: the four identities of Theorem 16.4.6 on every
compact tame oriented representative, with no partitions of unity. -/
def Amain : Prop :=
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_all.{0})

theorem main_A_to_B : Amain → B := by
  rintro ⟨hall, heff, hd1, heffd1⟩
  refine ⟨?_, ?_⟩
  · intro Z _ c θ m hc _ _ ht
    refine ⟨⟨θ.out, Quotient.out_eq θ,
      OrientedSuborbifold.isCompactBranched_of_mk hc _ (Quotient.out_eq θ),
      (OrientedSuborbifold.isTameOriented_iff θ).1 ht _ (Quotient.out_eq θ)⟩, ?_⟩
    intro hm a ha hca hta τ
    rw [OrientedSuborbifold.integral_eq θ _ hc ht _ a ha,
      OrientedSuborbifold.integralEff_eq θ _ hc ht _ a ha]
    exact ⟨hall a hm _ _ τ, heff a hm _ _ τ⟩
  · intro Z _ c θ hc _ _ ht
    refine ⟨⟨θ.out, Quotient.out_eq θ,
      OrientedSuborbifold.isCompactBranched_of_mk hc _ (Quotient.out_eq θ),
      (OrientedSuborbifold.isTameOriented_iff θ).1 ht _ (Quotient.out_eq θ)⟩, ?_⟩
    intro a ha hca hta τ
    rw [OrientedSuborbifold.integral_eq θ _ hc ht _ a ha,
      OrientedSuborbifold.integralEff_eq θ _ hc ht _ a ha]
    exact ⟨hd1 a _ _ τ, heffd1 a _ _ τ⟩

/-- From `B`: the hypotheses of `B` hold for the class of a compact tame oriented
representative. -/
theorem hyps {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z} (a : OrientedRep c) {n : ℕ}
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented n) :
    BranchedSuborbifold.IsCompact (OrientedSuborbifold.toBranched (⟦a⟧ : OrientedSuborbifold c)) ∧
      BranchedSuborbifold.IsTame (OrientedSuborbifold.toBranched (⟦a⟧ : OrientedSuborbifold c)) ∧
      BranchedSuborbifold.IsNDimensional
        (OrientedSuborbifold.toBranched (⟦a⟧ : OrientedSuborbifold c)) n ∧
      OrientedSuborbifold.IsTameOriented (⟦a⟧ : OrientedSuborbifold c) n :=
  ⟨⟨a.toBranchedRep, rfl, hcpt⟩,
    ⟨a.toBranchedRep, rfl, fun x hx => (hloc x hx).elim fun C _ => ⟨C.toTameBranchingStructure⟩⟩,
    ⟨a.toBranchedRep, rfl, EpGroupoid.FormEval.isNDimensional_of_loc hloc⟩, ⟨a, rfl, hloc⟩⟩

theorem main_B_to_A : B → Amain := by
  rintro ⟨hgen, h1⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z _ c m a hm hcpt hloc τ
    obtain ⟨hc, htm, hnd, ht⟩ := hyps a hcpt hloc
    have := ((hgen Z c ⟦a⟧ m hc htm hnd ht).2 hm a rfl hcpt hloc τ).1
    rwa [OrientedSuborbifold.integral_eq _ _ hc ht _ a rfl] at this
  · intro Z _ c m a hm hcpt hloc τ
    obtain ⟨hc, htm, hnd, ht⟩ := hyps a hcpt hloc
    have := ((hgen Z c ⟦a⟧ m hc htm hnd ht).2 hm a rfl hcpt hloc τ).2
    rwa [OrientedSuborbifold.integralEff_eq _ _ hc ht _ a rfl] at this
  · intro Z _ c a hcpt hloc τ
    obtain ⟨hc, htm, hnd, ht⟩ := hyps a hcpt hloc
    have := ((h1 Z c ⟦a⟧ hc htm hnd ht).2 a rfl hcpt hloc τ).1
    rwa [OrientedSuborbifold.integral_eq _ _ hc ht _ a rfl] at this
  · intro Z _ c a hcpt hloc τ
    obtain ⟨hc, htm, hnd, ht⟩ := hyps a hcpt hloc
    have := ((h1 Z c ⟦a⟧ hc htm hnd ht).2 a rfl hcpt hloc τ).2
    rwa [OrientedSuborbifold.integralEff_eq _ _ hc ht _ a rfl] at this

theorem A_to_B : A → B := fun h =>
  main_A_to_B ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

#rt_check RoundTrip.V16_28.A_to_B [Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_of_epStokes, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_of_epStokes, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_of_epStokes, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_of_epStokes, Polyfold.PolyfoldClass.hasEpStokes_of_admitsScPartitionsOfUnity, Polyfold.EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity, Polyfold.EP.stokesWithoutPartitions_witness, Polyfold.PolyfoldClass.hasEpStokes_witness, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_both_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_hyp_witness, Polyfold.EP.stokesWithoutPartitions_all, Polyfold.PolyfoldClass.hasEpStokes_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_both_all, Polyfold.EP.theorem_9_5_17_all, Polyfold.EP.theorem_9_5_18_all, Polyfold.EP.theorem_9_5_17_dim1_all, Polyfold.EP.theorem_9_5_18_dim1_all]
#rt_check RoundTrip.V16_28.main_A_to_B [Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_of_epStokes, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_of_epStokes, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_of_epStokes, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_of_epStokes, Polyfold.PolyfoldClass.hasEpStokes_of_admitsScPartitionsOfUnity, Polyfold.EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity, Polyfold.EP.stokesWithoutPartitions_witness, Polyfold.PolyfoldClass.hasEpStokes_witness, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_both_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_hyp_witness, Polyfold.EP.stokesWithoutPartitions_all, Polyfold.PolyfoldClass.hasEpStokes_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_both_all, Polyfold.EP.theorem_9_5_17_all, Polyfold.EP.theorem_9_5_18_all, Polyfold.EP.theorem_9_5_17_dim1_all, Polyfold.EP.theorem_9_5_18_dim1_all]
#rt_check RoundTrip.V16_28.main_B_to_A [Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_of_epStokes, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_of_epStokes, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_of_epStokes, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_of_epStokes, Polyfold.PolyfoldClass.hasEpStokes_of_admitsScPartitionsOfUnity, Polyfold.EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity, Polyfold.EP.stokesWithoutPartitions_witness, Polyfold.PolyfoldClass.hasEpStokes_witness, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_both_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_hyp_witness, Polyfold.EP.stokesWithoutPartitions_all, Polyfold.PolyfoldClass.hasEpStokes_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_both_all, Polyfold.EP.theorem_9_5_17_all, Polyfold.EP.theorem_9_5_18_all, Polyfold.EP.theorem_9_5_17_dim1_all, Polyfold.EP.theorem_9_5_18_dim1_all]
#rt_overlap RoundTrip.V16_28.main_B_to_A [Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_of_epStokes, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_of_epStokes, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_of_epStokes, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_of_epStokes, Polyfold.PolyfoldClass.hasEpStokes_of_admitsScPartitionsOfUnity, Polyfold.EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity, Polyfold.EP.stokesWithoutPartitions_witness, Polyfold.PolyfoldClass.hasEpStokes_witness, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_both_hyp, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_hyp_witness, Polyfold.EP.stokesWithoutPartitions_all, Polyfold.PolyfoldClass.hasEpStokes_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_dim1_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_eff_dim1_all, Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_both_all, Polyfold.EP.theorem_9_5_17_all, Polyfold.EP.theorem_9_5_18_all, Polyfold.EP.theorem_9_5_17_dim1_all, Polyfold.EP.theorem_9_5_18_dim1_all]

end RoundTrip.V16_28
