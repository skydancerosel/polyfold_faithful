import Polyfold.Chapter9.OrientationExample
import Polyfold.Chapter9.GeneralCorollaries

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.3, **Example 9.3.5**, p. 425 (2017: Example 9.1, p. 313): "In this case we have in fact four
different possibilities to orient."

# Example 9.3.5: the orientations given by sign choices on the two structures

The text orients the graphs `G⁺⁺, G⁻⁻` of the first structure and `G⁺⁻, G⁻⁺` of the second by
signs.  There are four sign choices for each structure.

## What is formalized

* `orientedLift1_const_eq_orientedLift2_const`: with all four graphs oriented by the same sign
  (all left to right, or all right to left) the two structures give the same orientation.
* `orientedLift1_eq_orientedLift2_iff`: these are the only coincidences: a sign choice `ε` on
  the first structure and `δ` on the second give the same orientation iff all signs are equal.
* `orientedLift2_injective`: the four sign choices of the second structure give four different
  orientations (for the first: `orientedLift1_injective`).
* `ncard_signOrientations`, `example_9_3_5_six`: the eight sign choices give exactly **six**
  orientations of `Θ` (four from each structure, two in common).  So "four different
  possibilities to orient" holds for each structure separately, and does not hold as we read it
  for `Θ`.

## Not formalized here

The classification of all orientations of `Θ` (Definition 9.3.2, with rational weights) is proved
in `GapP2_D2Example935Class.lean` (`example_9_3_5_classification`, 2026-11-12).  What this file
expected, and the classification confirms: on each of the four open arcs of `supp(Θ) ∖ {0}` an
orientation is `a [→] + (1 − a) [←]` with a rational `a ∈ [0, 1]` constant along the arc, and the structures at
the origin force `a(G⁺⁺, s > 0) + a(G⁻⁻, s > 0) = a(G⁺⁺, s < 0) + a(G⁻⁻, s < 0)`; the six
orientations here are the members of this family with all `a ∈ {0, 1}`.  The proof uses the
description of all one-dimensional submanifolds inside `supp(Θ)` through the origin and the
constancy of the coefficients along the arcs (`GapP2_D2Example935Sheets.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

open EpGroupoid

section Example935

/-- **All signs equal**: orienting all four graphs by the same sign `c`, the two structures give
the same orientation of `Θ`.  (For `s ≤ 0`, `G⁺⁻ = G⁺⁺` and `G⁻⁺ = G⁻⁻`; for `s > 0`,
`G⁺⁻ = G⁻⁻` and `G⁻⁺ = G⁺⁺`; the slopes agree at the common points.) -/
theorem orientedLift1_const_eq_orientedLift2_const (c : Bool) :
    orientedLift1 (fun _ => c) = orientedLift2 (fun _ => c) := by
  funext z
  rw [orientedLift1, orientedLift2, orientedSumRn_bool, orientedSumRn_bool]
  by_cases hs : z 0 ≤ 0
  · have h1 : z ∈ graph2 (beta2 true) ↔ z ∈ graph2 (beta1 true) := by
      change z 1 = betaPM (z 0) ↔ z 1 = betaPP (z 0)
      rw [betaPM_of_nonpos hs]
    have h2 : z ∈ graph2 (beta2 false) ↔ z ∈ graph2 (beta1 false) := by
      change z 1 = betaMP (z 0) ↔ z 1 = betaMM (z 0)
      rw [betaMP_of_nonpos hs]
    have d1 : deriv (beta1 true) (z 0) = deriv (beta2 true) (z 0) := by
      rcases hs.lt_or_eq with hlt | heq
      · exact deriv_eq_of_eqOn_Iio (fun t ht => (betaPM_of_nonpos ht.le).symm) hlt
      · rw [heq, deriv_beta1_zero, deriv_beta2_zero]
    have d2 : deriv (beta1 false) (z 0) = deriv (beta2 false) (z 0) := by
      rcases hs.lt_or_eq with hlt | heq
      · exact deriv_eq_of_eqOn_Iio (fun t ht => (betaMP_of_nonpos ht.le).symm) hlt
      · rw [heq, deriv_beta1_zero, deriv_beta2_zero]
    congr 1
    · by_cases ha : z ∈ graph2 (beta1 true)
      · rw [if_pos ha, if_pos (h1.2 ha)]
        exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) true))
          (graphOrientation_tangent_eq (contDiff_beta1 true) (contDiff_beta2 true)
            (boolSign_ne_zero _) ha (h1.2 ha) d1)
      · rw [if_neg ha, if_neg fun h => ha (h1.1 h)]
    · by_cases ha : z ∈ graph2 (beta1 false)
      · rw [if_pos ha, if_pos (h2.2 ha)]
        exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) false))
          (graphOrientation_tangent_eq (contDiff_beta1 false) (contDiff_beta2 false)
            (boolSign_ne_zero _) ha (h2.2 ha) d2)
      · rw [if_neg ha, if_neg fun h => ha (h2.1 h)]
  · have hs' : 0 < z 0 := lt_of_not_ge hs
    have h1 : z ∈ graph2 (beta2 true) ↔ z ∈ graph2 (beta1 false) := by
      change z 1 = betaPM (z 0) ↔ z 1 = betaMM (z 0)
      rw [betaPM_of_pos hs']
    have h2 : z ∈ graph2 (beta2 false) ↔ z ∈ graph2 (beta1 true) := by
      change z 1 = betaMP (z 0) ↔ z 1 = betaPP (z 0)
      rw [betaMP_of_pos hs']
    have d1 : deriv (beta1 false) (z 0) = deriv (beta2 true) (z 0) :=
      deriv_eq_of_eqOn_Ioi (fun t ht => (betaPM_of_pos ht).symm) hs'
    have d2 : deriv (beta1 true) (z 0) = deriv (beta2 false) (z 0) :=
      deriv_eq_of_eqOn_Ioi (fun t ht => (betaMP_of_pos ht).symm) hs'
    rw [add_comm]
    congr 1
    · by_cases ha : z ∈ graph2 (beta1 false)
      · rw [if_pos ha, if_pos (h1.2 ha)]
        exact congrArg (fun g => Finsupp.single g (1 : ℚ))
          (graphOrientation_tangent_eq (contDiff_beta1 false) (contDiff_beta2 true)
            (boolSign_ne_zero _) ha (h1.2 ha) d1)
      · rw [if_neg ha, if_neg fun h => ha (h1.1 h)]
    · by_cases ha : z ∈ graph2 (beta1 true)
      · rw [if_pos ha, if_pos (h2.2 ha)]
        exact congrArg (fun g => Finsupp.single g (1 : ℚ))
          (graphOrientation_tangent_eq (contDiff_beta1 true) (contDiff_beta2 false)
            (boolSign_ne_zero _) ha (h2.2 ha) d2)
      · rw [if_neg ha, if_neg fun h => ha (h2.1 h)]

/-- **The coincidences between the two structures**: the sign choice `ε` on `G⁺⁺, G⁻⁻` and the
sign choice `δ` on `G⁺⁻, G⁻⁺` give the same orientation of `Θ` iff all four signs are equal. -/
theorem orientedLift1_eq_orientedLift2_iff (ε δ : Bool → Bool) :
    orientedLift1 ε = orientedLift2 δ ↔ ∃ c, ε = (fun _ => c) ∧ δ = fun _ => c := by
  constructor
  · intro h
    have hp := congrFun h (ptPP 1)
    have hm := congrFun h (ptPP (-1))
    have hn := congrFun h (ptMM (-1))
    rw [orientedLift1_ptPP ε one_ne_zero, orientedLift2_ptPP_of_pos δ one_pos] at hp
    rw [orientedLift1_ptPP ε (by norm_num), orientedLift2_ptPP_of_neg δ (by norm_num)] at hm
    rw [orientedLift1_ptMM ε (by norm_num), orientedLift2_ptMM_of_neg δ (by norm_num)] at hn
    have hp' := (Finsupp.single_left_inj one_ne_zero).1 hp
    have hm' := (Finsupp.single_left_inj one_ne_zero).1 hm
    have hn' := (Finsupp.single_left_inj one_ne_zero).1 hn
    have e1 : ε true = δ false := by
      by_contra hne
      exact graphOrientation_tangent_ne' contDiff_betaPP hne (ptPP_mem 1) hp'
    have e2 : ε true = δ true := by
      by_contra hne
      exact graphOrientation_tangent_ne' contDiff_betaPP hne (ptPP_mem (-1)) hm'
    have e3 : ε false = δ false := by
      by_contra hne
      exact graphOrientation_tangent_ne' contDiff_betaMM hne (ptMM_mem (-1)) hn'
    refine ⟨ε true, funext fun b => ?_, funext fun b => ?_⟩
    · cases b
      · rw [e3, ← e1]
      · rfl
    · cases b
      · exact e1.symm
      · exact e2.symm
  · rintro ⟨c, rfl, rfl⟩
    exact orientedLift1_const_eq_orientedLift2_const c

/-- The sign choices of the second structure give four different orientations. -/
theorem orientedLift2_injective : Function.Injective orientedLift2 := by
  intro δ δ' h
  funext b
  by_contra hb
  cases b
  · have h1 := congrFun h (ptPP 1)
    rw [orientedLift2_ptPP_of_pos δ one_pos, orientedLift2_ptPP_of_pos δ' one_pos] at h1
    exact graphOrientation_tangent_ne' contDiff_betaPP hb (ptPP_mem 1)
      ((Finsupp.single_left_inj one_ne_zero).1 h1)
  · have h1 := congrFun h (ptPP (-1))
    rw [orientedLift2_ptPP_of_neg δ (by norm_num), orientedLift2_ptPP_of_neg δ' (by norm_num)]
      at h1
    exact graphOrientation_tangent_ne' contDiff_betaPP hb (ptPP_mem (-1))
      ((Finsupp.single_left_inj one_ne_zero).1 h1)

/-- **Example 9.3.5: the orientations by sign choices are six.**  The eight sign choices (four on
`G⁺⁺, G⁻⁻`, four on `G⁺⁻, G⁻⁺`) give exactly six orientations of `Θ`: four from each structure,
the two with all signs equal in common.  So "four different possibilities to orient" holds for
each structure, and does not hold as we read it for `Θ`. -/
theorem ncard_signOrientations :
    (range orientedLift1 ∪ range orientedLift2).ncard = 6 := by
  have hA : (range orientedLift1).ncard = 4 := by
    rw [← image_univ, ncard_image_of_injective _ orientedLift1_injective, ncard_univ]
    simp
  have hB : (range orientedLift2).ncard = 4 := by
    rw [← image_univ, ncard_image_of_injective _ orientedLift2_injective, ncard_univ]
    simp
  have hI : range orientedLift1 ∩ range orientedLift2 =
      {orientedLift1 fun _ => true, orientedLift1 fun _ => false} := by
    ext T
    constructor
    · rintro ⟨⟨ε, rfl⟩, ⟨δ, hδ⟩⟩
      obtain ⟨c, rfl, -⟩ := (orientedLift1_eq_orientedLift2_iff _ δ).1 hδ.symm
      cases c
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rintro (rfl | rfl)
      · exact ⟨⟨_, rfl⟩, ⟨_, (orientedLift1_const_eq_orientedLift2_const true).symm⟩⟩
      · exact ⟨⟨_, rfl⟩, ⟨_, (orientedLift1_const_eq_orientedLift2_const false).symm⟩⟩
  have hne : (orientedLift1 fun _ => true) ≠ orientedLift1 fun _ => false := fun h => by
    have := congrFun (orientedLift1_injective h) true
    exact Bool.noConfusion this
  have hIc : (range orientedLift1 ∩ range orientedLift2).ncard = 2 := by
    rw [hI, ncard_pair hne]
  have h := ncard_union_add_ncard_inter (range orientedLift1) (range orientedLift2)
    (finite_range _) (finite_range _)
  omega

/-- **Example 9.3.5, the count**: the sign choices on the two structures give six orientations
of `Θ` (Definition 9.3.2), no hypothesis (the independence of the tangent sums is a theorem). -/
theorem example_9_3_5_six :
    (∀ T ∈ range orientedLift1 ∪ range orientedLift2,
      (trivial (rnPolyfold 2)).IsOrientation example935Theta T) ∧
    (range orientedLift1 ∪ range orientedLift2).ncard = 6 := by
  refine ⟨?_, ncard_signOrientations⟩
  rintro T (⟨ε, rfl⟩ | ⟨δ, rfl⟩)
  · exact orientedLift1_isOrientation (hasIndependentTangentSums _) ε
  · exact orientedLift2_isOrientation (hasIndependentTangentSums _) δ

end Example935

end Polyfold
