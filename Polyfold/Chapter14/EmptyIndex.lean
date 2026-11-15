import Polyfold.Chapter14.BoundaryStructured
import Polyfold.Chapter12.AuxNormEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
Definition 14.1.3 (p. 642) and Theorem 14.1.9 (p. 646): the index sets `I_x` of a symmetric
structure over `∂X` are non-empty (Definition 14.1.3 (3) divides by `|I_x|`), so a
multisection over `∂X` charges every boundary fibre, and this is what Theorem 14.1.9 needs.

# Non-empty index sets over `∂X`

## What is formalized

`BoundarySymmetricStructure` (Definition 14.1.3) carries `Nonempty I_x`, as the factor `|I_x|⁻¹`
of (3) presumes.  Consequences:

* `ChargesBoundary Λ`: every fibre over `∂X` carries a point with `Λ(w) ≠ 0`.  It holds for
  every sc⁺-multisection over `∂X` (`chargesBoundary_of_isBoundaryScPlusMultisection`), hence for
  every structurable `Λ` (`IsBoundaryStructurable.chargesBoundary`) and every tuple
  (`BoundaryStructuredTuple.chargesBoundary`).  For a tuple it is the same as all `I_x ≠ ∅`
  (`BoundarySymmetricStructure.nonempty_I_a6`, `chargesBoundary_of_nonempty_a6`).
* `chargesBoundary_of_structurable_eq_a6`: the condition is also necessary for the conclusion of
  Theorem 14.1.9 (a structurable `Λ'` on `X` charges every fibre).
* `not_isBoundaryScPlusMultisection_zeroFun`: when `∂X ≠ ∅`, `Λ ≡ 0` is not an sc⁺-multisection
  over `∂X` (without `I_x ≠ ∅` it would be one, with empty index sets, and Theorem 14.1.9 would
  fail for it).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-- **`Λ` charges every fibre over `∂X`**: for `x ∈ ∂X` some `w` over `x` has `Λ(w) ≠ 0`.  For
the text's multisections (`I_x ≠ ∅` in Definition 14.1.3 (3)) this holds automatically. -/
def ChargesBoundary (Λ : A.W → ℚ≥0) : Prop :=
  ∀ x ∈ A.X.PObj.boundary, ∃ w, A.P w = x ∧ Λ w ≠ 0

/-- A symmetric structure over `∂X` at a point that `Λ` charges has a non-empty index set. -/
theorem BoundarySymmetricStructure.nonempty_I_a6 {Λ : A.W → ℚ≥0} {x : A.Obj}
    {V : A.X.NatNbhd x} (S : BoundarySymmetricStructure A Λ V) {y : A.Obj} (hy : y ∈ V.bdry)
    (h : ∃ w, A.P w = y ∧ Λ w ≠ 0) : Nonempty S.I := by
  obtain ⟨w, hw, hne⟩ := h
  by_contra hI
  rw [not_nonempty_iff] at hI
  have := S.rep w (by rw [hw]; exact hy)
  rw [Fintype.card_eq_zero, Nat.cast_zero, inv_zero, zero_mul] at this
  exact hne this

/-- For a tuple over `∂X`, `ChargesBoundary` gives non-empty index sets. -/
theorem BoundaryStructuredTuple.nonempty_I_a6 (T : BoundaryStructuredTuple A)
    (h : ChargesBoundary T.Λ) (x : A.X.PObj.boundary) : Nonempty (T.dec.S x).I :=
  (T.dec.S x).nonempty_I_a6 ⟨(T.dec.𝒰.nbhd x).mem_U, x.2⟩ (h x x.2)

/-- Conversely, a tuple with non-empty index sets charges every fibre over `∂X`. -/
theorem chargesBoundary_of_nonempty_a6 (T : BoundaryStructuredTuple A)
    (h : ∀ x, Nonempty (T.dec.S x).I) : ChargesBoundary T.Λ := by
  classical
  intro x hx
  set y : A.X.PObj.boundary := ⟨x, hx⟩
  have hy : x ∈ (T.dec.𝒰.nbhd y).bdry := ⟨(T.dec.𝒰.nbhd y).mem_U, hx⟩
  obtain ⟨i⟩ := h y
  refine ⟨(T.dec.S y).s i x, (T.dec.S y).P_s i hy, ?_⟩
  have hP := (T.dec.S y).P_s i hy
  have hr := (T.dec.S y).rep ((T.dec.S y).s i x) (by rw [hP]; exact hy)
  rw [hr, hP]
  refine mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) ?_
  refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, ?_⟩)
  simp

/-- **Nonvacuity**: the zero multisection charges every fibre (`Λ(0_x) = 1`). -/
theorem chargesBoundary_zeroMultisection_a6 : ChargesBoundary (zeroMultisection A) := by
  classical
  intro x _
  have hP : A.P (fiberZero A.P x) = x := proj_fiberZero A.P x
  refine ⟨fiberZero A.P x, hP, ?_⟩
  rw [zeroMultisection, if_pos (by rw [hP])]
  exact one_ne_zero

/-- **`ChargesBoundary` is necessary for Theorem 14.1.9**: if a structurable `Λ'` on `X` agrees
with `Λ` over `∂X`, then `Λ` charges every fibre over `∂X` (the local weights of `Λ'` sum to
`1`, Definition 13.2.1). -/
theorem chargesBoundary_of_structurable_eq_a6 {Λ Λ' : A.W → ℚ≥0} (hΛ' : IsStructurable A Λ')
    (h : ∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w) : ChargesBoundary Λ := by
  classical
  intro x hx
  obtain ⟨R, k, s, σ, hpos, hsc, hsum, hrep⟩ := hΛ'.1.2 x
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hsum
    · exact hk
  set i : Fin k := ⟨0, hk⟩
  have hP : A.P (s i x) = x := (hsc i).1 x R.mem_U
  refine ⟨s i x, hP, ?_⟩
  rw [← h _ (by rw [hP]; exact hx), hrep _ (by rw [hP]; exact R.mem_U)]
  refine ne_of_gt (lt_of_lt_of_le (hpos i) ?_)
  have := Finset.single_le_sum (f := fun j => if s i x = s j (A.P (s i x)) then σ j else 0)
    (fun j _ => by positivity) (Finset.mem_univ i)
  simpa [hP] using this

/-- **Sc⁺-multisections over `∂X` charge every boundary fibre** (`I_x ≠ ∅` in Definition
14.1.3). -/
theorem chargesBoundary_of_isBoundaryScPlusMultisection {Λ : A.W → ℚ≥0}
    (hΛ : IsBoundaryScPlusMultisection A Λ) : ChargesBoundary Λ :=
  fun _ hx => hΛ.exists_ne_zero hx

/-- **Structurable `Λ` over `∂X` charge every boundary fibre.** -/
theorem IsBoundaryStructurable.chargesBoundary {Λ : A.W → ℚ≥0}
    (hΛ : IsBoundaryStructurable A Λ) : ChargesBoundary Λ :=
  chargesBoundary_of_isBoundaryScPlusMultisection hΛ.1

/-- **A tuple over `∂X` charges every boundary fibre.** -/
theorem BoundaryStructuredTuple.chargesBoundary (T : BoundaryStructuredTuple A) :
    ChargesBoundary T.Λ :=
  chargesBoundary_of_nonempty_a6 T fun x => (T.dec.S x).nonempty

/-! ### The function `Λ ≡ 0` over `∂X` -/

/-- **Two correspondences out of an empty index set are equal.** -/
theorem IndexCorr.eq_of_isEmpty_a6 {α β : Type u} (hα : IsEmpty α) (τ τ' : IndexCorr α β) :
    τ = τ' := by
  induction τ using IndexCorr.ind with
  | h d =>
    induction τ' using IndexCorr.ind with
    | h d' =>
      have : IsEmpty d.I := ⟨fun k => hα.false (d.a k)⟩
      have : IsEmpty d'.I := ⟨fun k => hα.false (d'.a k)⟩
      exact IndexCorr.mk_eq_mk.2 ⟨_root_.Equiv.equivOfIsEmpty _ _, fun k => isEmptyElim k⟩

theorem boundaryDomSupp_zeroFun_a6 : boundaryDomSupp (fun _ : A.W => (0 : ℚ≥0)) = ∅ := by
  rw [boundaryDomSupp, closure_empty_iff, eq_empty_iff_forall_notMem]
  rintro x ⟨-, w, -, -, hpos⟩
  exact lt_irrefl _ hpos

/-- **`Λ ≡ 0` is not an sc⁺-multisection over `∂X` when `∂X ≠ ∅`**: Definition 14.1.3 (3) with
`I_x ≠ ∅` gives every boundary fibre a point of positive weight. -/
theorem not_isBoundaryScPlusMultisection_zeroFun {x : A.Obj} (hx : x ∈ A.X.PObj.boundary) :
    ¬ IsBoundaryScPlusMultisection A (fun _ => 0) := fun h => by
  obtain ⟨w, -, hw⟩ := chargesBoundary_of_isBoundaryScPlusMultisection h x hx
  exact hw rfl

end SBLocalization

end Polyfold
