import Polyfold.Chapter14.P3W3B1_BoundaryStructured
import Polyfold.Chapter12.P3N_AuxNormEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
Definition 14.1.3 (p. 642) and Theorem 14.1.9 (p. 646): the index sets `I_x` of a symmetric
structure over `∂X` are non-empty in the text (Definition 14.1.3 (3) divides by `|I_x|`), and
this is what Theorem 14.1.9 needs.

# Empty index sets over `∂X`

## What is formalized

The project's `BoundarySymmetricStructure` (B1, Definition 14.1.3) allows `I_x = ∅` (then (3)
reads `Λ(w) = 0⁻¹·0 = 0` in `ℚ≥0`).  With such structures the function `Λ ≡ 0` is structurable
over `∂X`, and no structurable `Λ'` on `X` (whose local weights sum to `1`, Definition 13.2.1)
restricts to it over a boundary point.  So the formal statement `theorem_14_1_9_statement` (B1)
does not hold as we read it whenever `∂X ≠ ∅`; the text's `|I_x|⁻¹` presumes `I_x ≠ ∅`.

* `ChargesBoundary Λ`: every fibre over `∂X` carries a point with `Λ(w) ≠ 0` (for the text's
  multisections `∑_w Λ(w) = 1` on every fibre).  For a tuple this is the same as all `I_x ≠ ∅`
  (`BoundarySymmetricStructure.nonempty_I_a6`, `chargesBoundary_of_nonempty_a6`).
* `chargesBoundary_of_structurable_eq_a6`: the condition is necessary for the conclusion of
  Theorem 14.1.9 (a structurable `Λ'` on `X` charges every fibre).
* `isBoundaryStructurable_zeroFun_a6`: `Λ ≡ 0` is structurable over `∂X` with `I_x = ∅`.
* **`not_theorem_14_1_9_statement_a6`**: for tame `X` with paracompact `|X|`, sc-smooth
  partitions of unity and `∂X ≠ ∅`, `¬ theorem_14_1_9_statement A`.
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

/-! ### The function `Λ ≡ 0` with empty index sets -/

/-- Two correspondences out of an empty index set are equal. -/
theorem IndexCorr.eq_of_isEmpty_a6 {α β : Type u} (hα : IsEmpty α) (τ τ' : IndexCorr α β) :
    τ = τ' := by
  induction τ using IndexCorr.ind with
  | h d =>
    induction τ' using IndexCorr.ind with
    | h d' =>
      have : IsEmpty d.I := ⟨fun k => hα.false (d.a k)⟩
      have : IsEmpty d'.I := ⟨fun k => hα.false (d'.a k)⟩
      exact IndexCorr.mk_eq_mk.2 ⟨_root_.Equiv.equivOfIsEmpty _ _, fun k => isEmptyElim k⟩

/-- The trivial action on `PEmpty`. -/
@[reducible] def pemptyAction_a6 (G : Type*) [Monoid G] : MulAction G PEmpty.{u + 1} where
  smul _ e := e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The symmetric structure with `I_x = ∅` for `Λ ≡ 0` (Definition 14.1.3 as formalized). -/
def emptyBoundaryStructure_a6 {x : A.Obj} (V : A.X.NatNbhd x) :
    BoundarySymmetricStructure A (fun _ => 0) V where
  I := PEmpty.{u + 1}
  mulAction := pemptyAction_a6 _
  s e := e.elim
  isFaceScPlus e := e.elim
  equivariant _ e := e.elim
  rep _ _ := by simp

/-- Correspondences for the empty structures: the unique correspondence `∅ → ∅`. -/
def emptyTau_a6 (𝒰 : A.X.BoundaryGoodSystem) :
    (⟨𝒰, fun x => emptyBoundaryStructure_a6 (𝒰.nbhd x)⟩ :
      BoundaryDecoration A (fun _ => 0)).Tau where
  τ _ _ _ := IndexCorr.ofEquiv (_root_.Equiv.refl PEmpty.{u + 1})
  locallyConstant _ _ _ _ := Eventually.of_forall fun _ => rfl
  finite _ _ := (finite_singleton (IndexCorr.ofEquiv (_root_.Equiv.refl PEmpty.{u + 1}))).subset
    (by rintro _ ⟨_, _, rfl⟩; rfl)
  swap _ _ _ _ := IndexCorr.eq_of_isEmpty_a6 (inferInstanceAs (IsEmpty PEmpty.{u + 1})) _ _
  diag _ _ _ _ := IndexCorr.eq_of_isEmpty_a6 (inferInstanceAs (IsEmpty PEmpty.{u + 1})) _ _
  biact _ _ _ _ _ _ := IndexCorr.eq_of_isEmpty_a6 (inferInstanceAs (IsEmpty PEmpty.{u + 1})) _ _
  compat _ _ _ _ := IndexCorr.sat_of_forall (fun i _ => PEmpty.elim i) _

/-- **`Λ ≡ 0` is structurable over `∂X`** in the formal sense (with `I_x = ∅`), over a tame
ep-groupoid with paracompact orbit space. -/
theorem isBoundaryStructurable_zeroFun_a6 (hX : A.X.IsTame)
    (hpara : A.X.HasParacompactOrbitSpace) : IsBoundaryStructurable A (fun _ => 0) := by
  obtain ⟨𝒰, -⟩ := A.X.theorem_14_1_6_hyp hX hpara (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  refine ⟨⟨fun _ _ => rfl, fun x hx => ?_⟩, _, ⟨emptyTau_a6 𝒰⟩⟩
  obtain ⟨V, -, hV⟩ := A.X.exists_isGoodBoundaryNbhd hX hx isOpen_univ (mem_univ x)
  exact ⟨V, hV, ⟨emptyBoundaryStructure_a6 V⟩⟩

theorem boundaryDomSupp_zeroFun_a6 : boundaryDomSupp (fun _ : A.W => (0 : ℚ≥0)) = ∅ := by
  rw [boundaryDomSupp, closure_empty_iff, eq_empty_iff_forall_notMem]
  rintro x ⟨-, w, -, -, hpos⟩
  exact lt_irrefl _ hpos

/-- **The formal statement of Theorem 14.1.9 does not hold as we read it when `∂X ≠ ∅`**: with
the formal Definition 14.1.3 (empty `I_x` allowed), `Λ ≡ 0` is structurable over `∂X`
(`isBoundaryStructurable_zeroFun_a6`), `Ũ = ∅` and `f = 0` meet the hypotheses, and no
structurable `Λ'` vanishes over a boundary point (`chargesBoundary_of_structurable_eq_a6`).  The
text's `|I_x|⁻¹` presumes `I_x ≠ ∅`; `theorem_14_1_9_charged_a6` (file `P3W6A6_Theorem1419`) is
the theorem with that reading. -/
theorem not_theorem_14_1_9_statement_a6 (hX : A.X.IsTame) (hpara : A.X.HasParacompactOrbitSpace)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {x : A.Obj} (hx : x ∈ A.X.PObj.boundary) :
    ¬ theorem_14_1_9_statement A := by
  intro h
  obtain ⟨N, hN⟩ := A.theorem_12_2_2 hpara
  obtain ⟨Λ', hΛ', -, -, hres⟩ := h hX hpara hpu (fun _ => 0)
    (isBoundaryStructurable_zeroFun_a6 hX hpara) N hN ∅ isOpen_empty
    (A.X.isSaturated_iff.2 fun _ h => absurd h (notMem_empty _))
    (by rw [boundaryDomSupp_zeroFun_a6]) (0 : A.Obj → ℝ) continuous_const (fun _ => le_rfl)
    (fun _ => rfl) (by rw [tsupport_zero]) (fun y hy => by
      rw [boundaryDomSupp_zeroFun_a6] at hy; exact absurd hy (notMem_empty _))
  obtain ⟨w, -, hne⟩ := chargesBoundary_of_structurable_eq_a6 hΛ' hres x hx
  exact hne rfl

end SBLocalization

end Polyfold
