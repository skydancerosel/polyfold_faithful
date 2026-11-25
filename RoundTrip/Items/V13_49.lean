import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V13_49

set_option maxSynthPendingDepth 3

/-! Round trip for V13_49 (2021 Theorem 13.5.6, p. 634; 2017: Theorem 13.9: atomic
sc⁺-multisections through a given vector or section).

`A` is the conjunction of the types of the six listed theorems at universe `0` (`B` is stated on
`SEP.{0}`): the helpers `normW_μ`, `AtomicData.pointwiseNorm_mult_le`,
`AtomicData.isLocalRepOn_mult`, and `theorem_13_5_6_1`, `theorem_13_5_6_2`, `theorem_13_5_6`.

* `B_to_A`: `A`'s bump hypothesis is `AdmitsBumpFunctionsPointwise` (`f(x) ≠ 0`), which gives
  `B`'s `AdmitsBumpFunctions` (`f ≢ 0`) by `AdmitsBumpFunctionsPointwise.weak`.  `A`'s
  `NaturalRep R` is `B`'s `NatNbhd.ofRep R`; `fibAct g w = μ(g, w)` by `fibAct_of`.  For (2), `B`
  gives atomic data `D` at `x` related to `Λ`, so `Λ = D.mult` (`IsRelated.eq_mult`), and the
  sections of `D` form a local representation of `Λ` on `U(x)` (the proof of
  `isLocalRepOn_mult`, copied); restricted to `U(x) ∩ O` the section `s_i = s` carries weight
  `|I|⁻¹ > 0`.  The three helper conjuncts are not consequences of `B`; they are re-proved
  outright by copying the project's proofs.
* `A_to_B` is not proved: `B` assumes only `AdmitsBumpFunctions` (Definition 12.3.1 as printed,
  "not identically zero") while `A` assumes the pointwise reading; the project records the
  implication weak ⇒ pointwise as open (`BumpEp.lean`).  Also for (2): `B` asks for atomic data
  `D` with `D.x = x` relating `Λ` whose section `s_i` equals `s` near `x`, while `A` gives atomic
  data at an unspecified point together with a local representation near `x` containing `s`. -/

open scoped Classical

namespace RoundTrip.V13_49
open Polyfold Polyfold.SBLocalization

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.normW_μ.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AtomicData.pointwiseNorm_mult_le.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AtomicData.isLocalRepOn_mult.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_5_6_1.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_5_6_2.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_5_6.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.normW_μ.{0},
    @Polyfold.SBLocalization.AtomicData.pointwiseNorm_mult_le.{0},
    @Polyfold.SBLocalization.AtomicData.isLocalRepOn_mult.{0},
    @Polyfold.SBLocalization.theorem_13_5_6_1.{0},
    @Polyfold.SBLocalization.theorem_13_5_6_2.{0},
    @Polyfold.SBLocalization.theorem_13_5_6.{0}⟩

/-! ### The helper conjuncts, re-proved outright (the project's proofs, copied) -/

section Copies

variable {A : SEP.{0}}

theorem normW_μ' {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N) {φ : A.Mor} {w : A.W}
    (h : A.P w = A.X.src φ) (hw : w ∈ A.B.oneSet) :
    normW N (A.E.μ ⟨(φ, w), h⟩) = normW N w := by
  obtain ⟨h1, he⟩ := A.E.exists_oneVal_eq_μ (A.B.oneMk w hw) φ (by rw [A.B.oneVal_oneMk]; exact h)
  have hμ : A.E.μ ⟨(φ, w), h⟩ = A.B.oneVal h1 :=
    (A.E.μ_congr (Prod.ext rfl (A.B.oneVal_oneMk w hw).symm)).trans he.symm
  have hm := mem_oneSet_μ h hw
  rw [normW_of_mem N hm, normW_of_mem N hw]
  have e : A.B.oneMk _ hm = h1 := A.B.oneVal_injective (by rw [A.B.oneVal_oneMk, hμ])
  rw [e]
  exact hN.map_μ h1 _ φ _ he

theorem pointwiseNorm_mult_le' (D : AtomicData A) [Nonempty D.I] {N : A.B.One → ℝ}
    (hN : A.E.IsAuxNorm N) {b : ℝ}
    (hb : 0 ≤ b) (hD : ∀ i, ∀ y ∈ D.R.U, normW N (D.s i y) ≤ b) (y : A.Obj) :
    pointwiseNorm N D.mult y ≤ b := by
  refine csSup_le ((D.isScPlusMultisection_mult.suppAt_nonempty y).image _) ?_
  rintro _ ⟨w, ⟨-, hpos⟩, rfl⟩
  by_cases hr : D.Reach (A.P w)
  · obtain ⟨φ, hs, ht⟩ := hr
    rw [D.mult_eq hs.symm ht, AtomicData.count] at hpos
    obtain ⟨i, hi⟩ : ∃ i, D.s i (A.P (A.E.μ ⟨(φ, w), hs.symm⟩)) = A.E.μ ⟨(φ, w), hs.symm⟩ := by
      by_contra hall
      rw [Finset.filter_false_of_mem fun i _ h => hall ⟨i, h⟩, Finset.card_empty, Nat.cast_zero,
        mul_zero] at hpos
      exact lt_irrefl _ hpos
    have hPm : A.P (A.E.μ ⟨(φ, w), hs.symm⟩) = A.X.tgt φ := A.E.P_μ _
    rw [hPm] at hi
    have hm1 : A.E.μ ⟨(φ, w), hs.symm⟩ ∈ A.B.oneSet := by
      rw [← hi]; exact (D.isScPlusSectionOn i).mem_oneSet ht
    rw [← normW_μ' hN hs.symm (mem_oneSet_of_μ hs.symm hm1), ← hi]
    exact hD i _ ht
  · rw [D.mult_of_not_reach hr, zeroMultisection] at hpos
    split_ifs at hpos with hw
    · rw [hw, normW_fiberZero hN.isAuxNorm]; exact hb
    · exact absurd hpos (lt_irrefl _)

theorem isLocalRepOn_mult' (D : AtomicData A) [Nonempty D.I] :
    IsLocalRepOn A D.mult D.R.U (fun n => D.s ((Fintype.equivFin D.I).symm n))
      (fun _ => (Fintype.card D.I : ℚ≥0)⁻¹) := by
  have hcard : (Fintype.card D.I : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine isLocalRepOn_of_fintype (K := D.I) D.s (fun _ => (Fintype.card D.I : ℚ≥0)⁻¹)
    (fun _ => inv_pos.2 (pos_iff_ne_zero.2 hcard)) D.isScPlusSectionOn ?_ fun w hw => ?_
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard]
  · rw [D.mult_of_mem hw, AtomicData.count, Finset.natCast_card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : D.s i (A.P w) = w
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

end Copies

/-! ### `B ⇒ A` -/

theorem B_to_A : B → A := by
  intro hB
  -- part (1) from `B`
  have h1 : type_of% @Polyfold.SBLocalization.theorem_13_5_6_1.{0} := by
    intro A hpara hbump N hN w hw hw0 x hwx R
    subst hwx
    obtain ⟨Λ, hat, hsupp, hpos⟩ :=
      (hB A hpara hbump.weak N hN).1 (A.P w) w rfl hw hw0 (EpGroupoid.NatNbhd.ofRep R)
    refine ⟨Λ, hat, hsupp, fun g => ?_⟩
    have := hpos g
    rwa [fibAct_of] at this
  -- part (2) from `B`
  have h2 : type_of% @Polyfold.SBLocalization.theorem_13_5_6_2.{0} := by
    intro A hpara hbump N hN x R s hs ε hε
    obtain ⟨Λ, hat, hsupp, hnorm, D, hDx, hrel, i, O, hO, hxO, hOs⟩ :=
      (hB A hpara hbump.weak N hN).2 x (EpGroupoid.NatNbhd.ofRep R) s hs ε hε
    subst hDx
    have : Nonempty D.I := ⟨i⟩
    have hΛ : Λ = D.mult := hrel.eq_mult
    subst hΛ
    refine ⟨D.mult, hat, hsupp, hnorm, D.R.U ∩ O, _, _, _, D.R.isOpen_U.inter hO,
      ⟨D.R.mem_U, hxO⟩, (isLocalRepOn_mult' D).mono (D.R.isOpen_U.inter hO) Set.inter_subset_left,
      Fintype.equivFin D.I i, inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos), fun y hy => ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact (hOs y hy.2).1
  refine ⟨@normW_μ', @pointwiseNorm_mult_le', @isLocalRepOn_mult', h1, h2, ?_⟩
  intro A hpara hbump N hN
  exact ⟨fun _ hw hw0 R => h1 hpara hbump hN hw hw0 rfl R,
    fun _ R _ hs _ hε => h2 hpara hbump hN R hs hε⟩

#rt_check RoundTrip.V13_49.B_to_A [Polyfold.SBLocalization.normW_μ,
  Polyfold.SBLocalization.AtomicData.pointwiseNorm_mult_le,
  Polyfold.SBLocalization.AtomicData.isLocalRepOn_mult,
  Polyfold.SBLocalization.theorem_13_5_6_1, Polyfold.SBLocalization.theorem_13_5_6_2,
  Polyfold.SBLocalization.theorem_13_5_6]
#rt_overlap RoundTrip.V13_49.B_to_A [Polyfold.SBLocalization.normW_μ,
  Polyfold.SBLocalization.AtomicData.pointwiseNorm_mult_le,
  Polyfold.SBLocalization.AtomicData.isLocalRepOn_mult,
  Polyfold.SBLocalization.theorem_13_5_6_1, Polyfold.SBLocalization.theorem_13_5_6_2,
  Polyfold.SBLocalization.theorem_13_5_6]

end RoundTrip.V13_49
