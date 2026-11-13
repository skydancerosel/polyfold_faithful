import Polyfold.Chapter13.MultisectionAlgebra
import Polyfold.Chapter10.StrongBundleEquivalenceExamples
import Polyfold.Chapter5.AllowableSectionsMetric

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.2, p. 611, the sentence after **Definition 13.2.9** (2017: after Definition 13.11).

# No inverses for the sum of sc⁺-multisections

## The text, paraphrased

The sum `⊕` of sc⁺-multisections is associative and commutative; in general there are no inverses.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `multisectionAdd_zeroMultisection`: the multisection `Λ₀` of the zero section is a neutral
  element, `Λ ⊕ Λ₀ = Λ` for every sc⁺-multisection `Λ` (so "inverse" means `Λ ⊕ Λ' = Λ₀`).
* `remark_13_2_9_no_inverse`: on the trivial strong bundle `ℝⁿ × ℝᵏ → ℝⁿ` (`k ≥ 1`) over the
  trivial ep-groupoid, the two-valued sc⁺-multisection `twoValued` (weight `½` on the zero section
  and `½` on a constant section `c ≠ 0`) has no inverse: `Λ ⊕ Λ' ≠ Λ₀` for every
  sc⁺-multisection `Λ'`.  Over a point `x`, `(Λ ⊕ Λ')(0_x) = ½(Λ'(0) + Λ'(−c)) ≤ ½`, while
  `Λ₀(0_x) = 1`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle

/-! ### The neutral element -/

/-- The multisection of the zero section over a fibre: `Λ₀(u) = [u = 0]`. -/
theorem zeroMultisection_fib {A : SEP.{u}} {x : A.Obj} (u : A.P ⁻¹' {x}) :
    zeroMultisection A u = ∑ _k : Fin 1, if u = 0 then (1 : ℚ≥0) else 0 := by
  have hP : A.P (u : A.W) = x := u.2
  rw [Fin.sum_univ_one, zeroMultisection]
  refine if_congr ?_ rfl rfl
  rw [hP]
  exact ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩

/-- **The zero multisection is neutral for `⊕`**: `Λ ⊕ Λ₀ = Λ` for an sc⁺-multisection `Λ`. -/
theorem multisectionAdd_zeroMultisection {A : SEP.{u}} {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) : multisectionAdd Λ (zeroMultisection A) = Λ := by
  funext w
  obtain ⟨k, a, σ, r⟩ := hΛ.exists_fib_rep (A.P w)
  have h := multisectionAdd_fib_rep a σ (fun _ : Fin 1 => (0 : A.P ⁻¹' {A.P w}))
    (fun _ => 1) r zeroMultisection_fib ⟨w, rfl⟩
  refine h.trans ?_
  rw [r ⟨w, rfl⟩, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_one, add_zero, mul_one]

/-! ### The example -/

namespace NoInverse

open TrivialBundle StrongBundleEquivalenceExamples

variable (n k : ℕ)

/-- The trivial strong bundle `ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ`. -/
abbrev A : SEP.{0} := epSEP n k

variable {n k}

/-- The constant section `x ↦ (x, c)`. -/
def constSec (c : Fin k → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) × (Fin k → ℝ) :=
  graphSection fun _ => c

/-- The two local sections: the zero section and the constant section `c`. -/
def secs (c : Fin k → ℝ) : Fin 2 → (A n k).Obj → (A n k).W :=
  ![fiberZero (A n k).P, constSec c]

/-- **The two-valued sc⁺-multisection** `Λ(w) = ½[w = 0] + ½[w = c]`. -/
def twoValued (c : Fin k → ℝ) : (A n k).W → ℚ≥0 := fun w =>
  ∑ i : Fin 2, if w = secs c i ((A n k).P w) then (1 / 2 : ℚ≥0) else 0

theorem isLocalRepOn_twoValued (c : Fin k → ℝ) :
    IsLocalRepOn (A n k) (twoValued c) univ (secs c) fun _ => 1 / 2 := by
  refine ⟨fun _ => by norm_num, fun i => ?_, ?_, fun w _ => rfl⟩
  · fin_cases i
    · exact isScPlusSectionOn_fiberZero isOpen_univ
    · exact IsScPlusSectionOn.of_isScPlusSection (A := A n k)
        (isScPlusSection_graphSection contDiff_const) isOpen_univ
  · rw [Fin.sum_univ_two]; norm_num

/-- `twoValued c` is an sc⁺-multisection (Definition 13.2.1). -/
theorem isScPlusMultisection_twoValued (c : Fin k → ℝ) :
    IsScPlusMultisection (A n k) (twoValued c) :=
  ⟨fun _ => rfl, fun x => hasLocalSectionStructure_of_isLocalRepOn isOpen_univ (mem_univ x)
    (isLocalRepOn_twoValued c)⟩

/-- Two different points of a fibre have total weight at most `1`. -/
theorem add_le_one_of_ne {A : SEP.{u}} {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    {x : A.Obj} {u v : A.P ⁻¹' {x}} (huv : u ≠ v) : Λ u + Λ v ≤ 1 := by
  obtain ⟨O, m, s, σ, -, hx, h⟩ := hΛ.exists_isLocalRepOn x
  rw [h.apply_fib hx u, h.apply_fib hx v, ← Finset.sum_add_distrib]
  refine (Finset.sum_le_sum fun i _ => ?_).trans_eq h.2.2.1
  by_cases hu : u = ⟨s i x, (h.2.1 i).1 x hx⟩
  · have hv : ¬ v = ⟨s i x, (h.2.1 i).1 x hx⟩ := fun hv => huv (hu.trans hv.symm)
    rw [if_pos hu, if_neg hv, add_zero]
  · rw [if_neg hu, zero_add]
    split_ifs
    · exact le_rfl
    · exact zero_le

/-- **2021, p. 611, after Definition 13.2.9 ("in general, there are no inverses")**: for `c ≠ 0`
the two-valued sc⁺-multisection `twoValued c` of `ℝⁿ × ℝᵏ → ℝⁿ` has no inverse for `⊕`:
`twoValued c ⊕ Λ' ≠ Λ₀` for every sc⁺-multisection `Λ'`. -/
theorem remark_13_2_9_no_inverse {c : Fin k → ℝ} (hc : c ≠ 0) {Λ' : (A n k).W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A n k) Λ') :
    multisectionAdd (twoValued c) Λ' ≠ zeroMultisection (A n k) := by
  intro hsum
  set x : (A n k).Obj := (0 : Fin n → ℝ)
  have hrep := fun u => (isLocalRepOn_twoValued (n := n) c).apply_fib (mem_univ x) u
  obtain ⟨m, b, σ, hb⟩ := hΛ'.exists_fib_rep x
  have h0 := multisectionAdd_fib_rep _ (fun _ => 1 / 2) b σ hrep hb 0
  set a : Fin 2 → (A n k).P ⁻¹' {x} := fun i =>
    ⟨secs c i x, ((isLocalRepOn_twoValued c).2.1 i).1 x (mem_univ x)⟩ with ha_def
  rw [hsum, zeroMultisection_fib, Fin.sum_univ_one, if_pos rfl, Fintype.sum_prod_type,
    Fin.sum_univ_two] at h0
  -- `a 0 = 0` and `a 1 ≠ 0`
  have ha0 : a 0 = 0 := Subtype.ext rfl
  have ha1 : a 1 ≠ 0 := fun e => hc (by
    have h1 := congrArg (fun v : (A n k).P ⁻¹' {x} => ((v : (A n k).W)).2) e
    have h2 : (((0 : (A n k).P ⁻¹' {x}) : (A n k).W)).2 = 0 := snd_zero (n := n) (k := k) _
    exact h1.trans h2)
  -- the two sums are `½ Λ'(0)` and `½ Λ'(-a 1)`
  have e0 : (∑ j, if (0 : (A n k).P ⁻¹' {x}) = a 0 + b j then (1 / 2 : ℚ≥0) * σ j else 0) =
      1 / 2 * Λ' (0 : (A n k).P ⁻¹' {x}) := by
    rw [hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha0, zero_add]
    split_ifs <;> simp
  have e1 : (∑ j, if (0 : (A n k).P ⁻¹' {x}) = a 1 + b j then (1 / 2 : ℚ≥0) * σ j else 0) =
      1 / 2 * Λ' (-a 1 : (A n k).P ⁻¹' {x}) := by
    rw [hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ((0 : (A n k).P ⁻¹' {x}) = a 1 + b j) ↔ (-a 1 = b j) := by
      rw [eq_comm, add_comm, add_eq_zero_iff_eq_neg, eq_comm]
    by_cases h : -a 1 = b j
    · rw [if_pos (this.2 h), if_pos h]
    · rw [if_neg (fun e => h (this.1 e)), if_neg h, mul_zero]
  rw [e0, e1, ← mul_add] at h0
  have hle := add_le_one_of_ne hΛ' (u := 0) (v := -a 1) (fun e => ha1 (neg_eq_zero.1 e.symm))
  have : (1 : ℚ≥0) ≤ 1 / 2 := by
    calc (1 : ℚ≥0) = 1 / 2 * (Λ' (0 : (A n k).P ⁻¹' {x}) + Λ' (-a 1 : (A n k).P ⁻¹' {x})) := h0
      _ ≤ 1 / 2 * 1 := by gcongr
      _ = 1 / 2 := mul_one _
  exact absurd this (by norm_num)

/-- The hypothesis `c ≠ 0` is satisfiable for `k ≥ 1`, and `twoValued c` is an sc⁺-multisection:
the example is not vacuous. -/
theorem exists_no_inverse (hk : 0 < k) :
    ∃ Λ : (A n k).W → ℚ≥0, IsScPlusMultisection (A n k) Λ ∧
      ∀ Λ', IsScPlusMultisection (A n k) Λ' → multisectionAdd Λ Λ' ≠ zeroMultisection (A n k) := by
  refine ⟨twoValued (fun _ => 1), isScPlusMultisection_twoValued _, fun Λ' hΛ' =>
    remark_13_2_9_no_inverse ?_ hΛ'⟩
  intro h
  have := congrFun h ⟨0, hk⟩
  simp at this

end NoInverse

end SBLocalization

end Polyfold
