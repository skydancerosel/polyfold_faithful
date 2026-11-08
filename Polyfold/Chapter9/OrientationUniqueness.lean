import Polyfold.Chapter9.OrientationExample

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.3 "Orientations": **Lemma 9.3.4** (2021 pp. 423–424; 2017: Lemma 9.10).
Numbers and pages are the 2021 text's, the 2017 ones in parentheses.

# Orientations agreeing at good points

## The text, paraphrased

Two orientations `T̂¹_Θ`, `T̂²_Θ` of a branched ep⁺-subgroupoid `Θ` which agree at good points
are the same.  *Proof* (text): at a bad point `x`, group the `(Mᵢ, oᵢ)` of the first oriented
representation by `T_xMᵢ`; Proposition 9.2.8 gives, for each class, sequences of good points
`x_k^q → x` and a partition `I¹ ⊔ … ⊔ Iᵉ` of the class with `x_k^q ∈ Mᵢ` iff `i ∈ I^q`; split
`I^q = I^q_+ ⊔ I^q_-` by the orientation at `x`; at `x_k^q` the two orientations agree, and the
limit gives the part of `T̂¹(x)` over the class; the same for the second representation, and the
two parts are equal.

## What is formalized

* `MPolyfold.HasOrientedGoodPointsAt x n`: the good-point input, for every finite family of
  oriented `n`-dimensional submanifolds through `x` (blocks of the tangent classes with a good
  point `y_e` of the family on exactly the members of the block, at which relative orientations
  are those at `x`); satisfiable (`hasOrientedGoodPointsAt_rn_zero`).
* `EpGroupoid.IsOrientationOfDim Θ n T` (orientations with `n`-dimensional representations
  (9.9)), witnesses `isOrientationOfDim_sum_rn`, `orientedLift1/2_isOrientationOfDim`.
* **Lemma 9.3.4**: `lemma_9_3_4` (for `n`-dimensional orientations under the hypothesis above).
* `lemma_9_3_4_mixed_dim`: without equidimensionality the statement does not hold as we read it.

## What the text leaves implicit, and the choices made

* The proof uses the good points of the first structure only; to compare with the second
  structure the sequences must also lie on exactly a block of the `Nⱼ`, which needs an argument
  the text does not give.  We apply Proposition 9.2.8 to the union of both families, and take its
  oriented form (with the local constancy of relative orientations) as the hypothesis
  `HasOrientedGoodPointsAt`.
* Equidimensionality: for `Θ = 1_{ℝ × 0} + 1_{(0,0)}` in `ℝ²`, the orientations
  `(ℝ × 0, +) + ({0}, ±)` agree off the bad point `(0, 0)` and differ there.

## Not formalized, and why

* Proposition 9.2.8 for oriented families (the hypothesis above), and Theorem 9.2.1's
  independence for the witnesses (hypothesis `hind`).
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology CategoryTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

variable (P) in
/-- **The good-point input of the proof of Lemma 9.3.4**, as a hypothesis at `x`: for every finite
family of oriented `n`-dimensional submanifolds `(A_k, o_k)` through `x`, every `k₀` and every open
`W ∋ x`, the indices `k` with `T_x A_k = T_x A_{k₀}` split into blocks `e`, each with a point
`y_e ∈ W` lying exactly on the `A_k` of the block (Proposition 9.2.8, applied to the whole family),
near which these `A_k` coincide (a good point of the family), and at which two `o_k` agree iff
they agree at `x` (the relative orientations at `y_e` are those at `x`). -/
def HasOrientedGoodPointsAt (x : X) (n : ℕ) : Prop :=
  ∀ (κ : Type u) [Fintype κ] (A : κ → Set X) (d : κ → ℕ)
    (o : ∀ k, P.SubmanifoldOrientation (A k) (d k)),
    (∀ k, d k = n) → (∀ k, P.IsSubmanifoldOfDim (A k) (d k)) → (∀ k, x ∈ A k) →
    ∀ (k₀ : κ) (W : Set X), IsOpen W → x ∈ W →
      ∃ (p : ℕ) (blk : κ → Fin p) (y : Fin p → X), ∀ e, y e ∈ W ∧
        (∀ k, y e ∈ A k ↔
          P.submanifoldTangent (A k) x = P.submanifoldTangent (A k₀) x ∧ blk k = e) ∧
        (∃ V : Set X, IsOpen V ∧ y e ∈ V ∧
          ∀ k k', y e ∈ A k → y e ∈ A k' → V ∩ A k = V ∩ A k') ∧
        ∀ k k', y e ∈ A k → y e ∈ A k' →
          ((o k).tangent (y e) = (o k').tangent (y e) ↔ (o k).tangent x = (o k').tangent x)

end MPolyfold

/-- **Satisfiability of `HasOrientedGoodPointsAt`**: it holds at the point of `ℝ⁰` (one block,
`y = x`). -/
theorem hasOrientedGoodPointsAt_rn_zero (x : Fin 0 → ℝ) (n : ℕ) :
    (rnPolyfold 0).HasOrientedGoodPointsAt x n := by
  intro κ _ A d o _ _ hx k₀ W _ hxW
  have hA : ∀ k, A k = A k₀ := fun k => Set.ext fun z => by
    rw [Subsingleton.elim z x]; exact iff_of_true (hx k) (hx k₀)
  refine ⟨1, fun _ => 0, fun _ => x, fun e => ⟨hxW, fun k => ?_,
    ⟨univ, isOpen_univ, mem_univ _, fun k k' _ _ => by rw [hA k, hA k']⟩,
    fun k k' _ _ => Iff.rfl⟩⟩
  exact iff_of_true (hx k) ⟨by rw [hA k], Subsingleton.elim _ _⟩

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
variable {Θ : Obj → ℚ}

variable (X) in
/-- **An `n`-dimensional orientation**: an orientation whose local representations (9.9) can be
taken with `n`-dimensional `(Mᵢ, oᵢ)`. -/
def IsOrientationOfDim (Θ : Obj → ℚ) (n : ℕ) (T : Obj → X.PObj.OrTangent →₀ ℚ) : Prop :=
  X.IsOrientation Θ T ∧ ∀ x ∈ supp Θ, ∃ B : X.OrientedBranchingStructure Θ x,
    (∀ i, B.dim i = n) ∧ ∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = B.orientedSum y

/-- A point `y ∈ U(x) ∩ Mᵢ` near which all `Mⱼ ∋ y` coincide is a good point. -/
theorem mem_goodSet_of {x : Obj} (B : X.LocalBranchingStructure Θ x) {y : Obj} {i : B.ι}
    (hyU : y ∈ B.U) (hyi : y ∈ B.M i) {V : Set Obj} (hV : IsOpen V) (hyV : y ∈ V)
    (h : ∀ i j, y ∈ B.M i → y ∈ B.M j → V ∩ B.M i = V ∩ B.M j) : y ∈ X.goodSet Θ := by
  have hMU : y ∈ B.MU := mem_iUnion.2 ⟨i, hyi⟩
  refine ⟨(show y ∈ supp Θ ∩ B.U by rw [← B.MU_eq]; exact hMU).1, x, B, hyU, hMU, V ∩ B.U,
    hV.inter B.isOpen_U, ⟨hyV, hyU⟩, inter_subset_right, fun i j hi hj => ?_⟩
  rw [inter_right_comm, h i j hi hj, inter_right_comm]

/-- Splitting a sum along a map to `Fin p`. -/
theorem sum_ite_eq_sum_fiber {ι : Type*} [Fintype ι] {p : ℕ} (g : ι → Fin p) (Q : ι → Prop)
    [DecidablePred Q] (a : ι → ℚ) :
    (∑ i, if Q i then a i else 0) = ∑ e, ∑ i, if g i = e ∧ Q i then a i else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hQ : Q i <;> simp [hQ]

open scoped Classical in
/-- **Lemma 9.3.4, 2021 pp. 423–424 (2017: Lemma 9.10)**, for `n`-dimensional orientations: two
orientations `T̂¹`, `T̂²` of `Θ` which agree at the good points agree on `X_∞`.  The good-point
input of the text's proof (Proposition 9.2.8, here applied to the union of the two oriented
families, and the constancy of relative orientations) is the hypothesis
`HasOrientedGoodPointsAt`. -/
theorem lemma_9_3_4 (hΘ : X.IsBranchedEpSubgroupoid Θ) {n : ℕ}
    {T₁ T₂ : Obj → X.PObj.OrTangent →₀ ℚ} (h₁ : X.IsOrientationOfDim Θ n T₁)
    (h₂ : X.IsOrientationOfDim Θ n T₂)
    (hgood : ∀ x ∈ supp Θ, X.PObj.HasOrientedGoodPointsAt x n)
    (hagree : ∀ y ∈ X.goodSet Θ, T₁ y = T₂ y) :
    ∀ x ∈ X.PObj.smoothSet, T₁ x = T₂ x := by
  intro x hx
  by_cases hxs : x ∈ supp Θ
  swap
  · rw [h₁.1.eq_zero_of_not_mem hx hxs, h₂.1.eq_zero_of_not_mem hx hxs]
  obtain ⟨B₁, hd₁, hT₁⟩ := h₁.2 x hxs
  obtain ⟨B₂, hd₂, hT₂⟩ := h₂.2 x hxs
  rw [hT₁ x B₁.mem_U hx, hT₂ x B₂.mem_U hx]
  ext t
  rw [B₁.orientedSum_apply, B₂.orientedSum_apply,
    Finset.filter_true_of_mem (s := Finset.univ) (p := fun i => x ∈ B₁.M i)
      fun i _ => B₁.mem_M i,
    Finset.filter_true_of_mem (s := Finset.univ) (p := fun j => x ∈ B₂.M j)
      fun j _ => B₂.mem_M j]
  let A : B₁.ι ⊕ B₂.ι → Set Obj := Sum.elim B₁.M B₂.M
  let d : B₁.ι ⊕ B₂.ι → ℕ := Sum.elim B₁.dim B₂.dim
  let o : ∀ k, X.PObj.SubmanifoldOrientation (A k) (d k) := fun k =>
    match k with
    | .inl i => B₁.orient i
    | .inr j => B₂.orient j
  by_cases ht : ∃ k, (o k).tangent x = t
  swap
  · push Not at ht
    have e1 : (∑ i, if (B₁.orient i).tangent x = t then B₁.σ i else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => if_neg (ht (.inl i))
    have e2 : (∑ j, if (B₂.orient j).tangent x = t then B₂.σ j else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => if_neg (ht (.inr j))
    rw [e1, e2]
  obtain ⟨k₀, hk₀⟩ := ht
  obtain ⟨p, blk, y, hy⟩ := hgood x hxs (B₁.ι ⊕ B₂.ι) A d o
    (by rintro (i | j); exacts [hd₁ i, hd₂ j])
    (by rintro (i | j); exacts [B₁.isSubmanifoldOfDim i, B₂.isSubmanifoldOfDim j])
    (by rintro (i | j); exacts [B₁.mem_M i, B₂.mem_M j]) k₀ (B₁.U ∩ B₂.U)
    (B₁.isOpen_U.inter B₂.isOpen_U) ⟨B₁.mem_U, B₂.mem_U⟩
  have hcls : ∀ k, (o k).tangent x = t →
      X.PObj.submanifoldTangent (A k) x = X.PObj.submanifoldTangent (A k₀) x := fun k hk =>
    congrArg MPolyfold.OrTangent.carrier (hk.trans hk₀.symm)
  have hblock : ∀ e,
      (∑ i, if blk (.inl i) = e ∧ (B₁.orient i).tangent x = t then B₁.σ i else 0) =
        ∑ j, if blk (.inr j) = e ∧ (B₂.orient j).tangent x = t then B₂.σ j else 0 := by
    intro e
    obtain ⟨hyW, hmem, ⟨V, hV, hyV, hcoinc⟩, hrel⟩ := hy e
    by_cases hb : ∃ k, blk k = e ∧ (o k).tangent x = t
    swap
    · push Not at hb
      have h1 : ∀ i, blk (.inl i) = e → (B₁.orient i).tangent x ≠ t := fun i => hb (.inl i)
      have h2 : ∀ j, blk (.inr j) = e → (B₂.orient j).tangent x ≠ t := fun j => hb (.inr j)
      have e1 : (∑ i, if blk (.inl i) = e ∧ (B₁.orient i).tangent x = t then B₁.σ i else 0) =
          0 := Finset.sum_eq_zero fun i _ => if_neg fun h => h1 i h.1 h.2
      have e2 : (∑ j, if blk (.inr j) = e ∧ (B₂.orient j).tangent x = t then B₂.σ j else 0) =
          0 := Finset.sum_eq_zero fun j _ => if_neg fun h => h2 j h.1 h.2
      rw [e1, e2]
    obtain ⟨k₁, hk₁e, hk₁t⟩ := hb
    have hy₁ : y e ∈ A k₁ := (hmem k₁).2 ⟨hcls k₁ hk₁t, hk₁e⟩
    have hg : y e ∈ X.goodSet Θ := by
      rcases k₁ with i | j
      · exact mem_goodSet_of B₁.toLocalBranchingStructure hyW.1 (i := i) hy₁ hV hyV
          fun i j hi hj => hcoinc (.inl i) (.inl j) hi hj
      · exact mem_goodSet_of B₂.toLocalBranchingStructure hyW.2 (i := j) hy₁ hV hyV
          fun i j hi hj => hcoinc (.inr i) (.inr j) hi hj
    have hsm : y e ∈ X.PObj.smoothSet := hΘ.support_subset hg.1
    have heq : B₁.orientedSum (y e) = B₂.orientedSum (y e) := by
      rw [← hT₁ _ hyW.1 hsm, ← hT₂ _ hyW.2 hsm]; exact hagree _ hg
    have key : ∀ k, (y e ∈ A k ∧ (o k).tangent (y e) = (o k₁).tangent (y e)) ↔
        (blk k = e ∧ (o k).tangent x = t) := fun k => by
      constructor
      · rintro ⟨hyk, hk⟩
        exact ⟨((hmem k).1 hyk).2, ((hrel k k₁ hyk hy₁).1 hk).trans hk₁t⟩
      · rintro ⟨hke, hkt⟩
        have hyk : y e ∈ A k := (hmem k).2 ⟨hcls k hkt, hke⟩
        exact ⟨hyk, (hrel k k₁ hyk hy₁).2 (hkt.trans hk₁t.symm)⟩
    have h := DFunLike.congr_fun heq ((o k₁).tangent (y e))
    rw [B₁.orientedSum_apply, B₂.orientedSum_apply, Finset.sum_filter, Finset.sum_filter] at h
    calc (∑ i, if blk (.inl i) = e ∧ (B₁.orient i).tangent x = t then B₁.σ i else 0)
        = ∑ i, if y e ∈ B₁.M i then
            (if (B₁.orient i).tangent (y e) = (o k₁).tangent (y e) then B₁.σ i else 0) else 0 :=
          Finset.sum_congr rfl fun i _ => by
            rw [← ite_and]; exact if_congr (key (.inl i)).symm rfl rfl
      _ = ∑ j, if y e ∈ B₂.M j then
            (if (B₂.orient j).tangent (y e) = (o k₁).tangent (y e) then B₂.σ j else 0) else 0 := h
      _ = _ := Finset.sum_congr rfl fun j _ => by
            rw [← ite_and]; exact if_congr (key (.inr j)) rfl rfl
  calc (∑ i, if (B₁.orient i).tangent x = t then B₁.σ i else 0)
      = ∑ e, ∑ i, if blk (.inl i) = e ∧ (B₁.orient i).tangent x = t then B₁.σ i else 0 :=
        sum_ite_eq_sum_fiber (fun i => blk (.inl i)) _ _
    _ = ∑ e, ∑ j, if blk (.inr j) = e ∧ (B₂.orient j).tangent x = t then B₂.σ j else 0 :=
        Finset.sum_congr rfl fun e _ => hblock e
    _ = _ := (sum_ite_eq_sum_fiber (fun j => blk (.inr j)) _ _).symm

open scoped Classical in
/-- **Satisfiability of `IsOrientationOfDim`**: the oriented sums `∑ σᵢ T_y(Mᵢ, oᵢ)` of closed
oriented `m`-dimensional submanifolds of `ℝⁿ` are `m`-dimensional orientations (given Theorem
9.2.1's independence). -/
theorem isOrientationOfDim_sum_rn {n : ℕ} {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) {m : ℕ}
    (hM : ∀ i, (rnPolyfold n).IsSubmanifoldOfDim (M i) m) (hc : ∀ i, IsClosed (M i))
    (o : ∀ i, (rnPolyfold n).SubmanifoldOrientation (M i) m) {Θ : (Fin n → ℝ) → ℚ}
    (hΘ : Θ = fun y => ∑ i with y ∈ M i, σ i)
    (hind : (trivial (rnPolyfold n)).HasIndependentTangentSums Θ) :
    (trivial (rnPolyfold n)).IsOrientationOfDim Θ m (orientedSumRn M σ o) := by
  subst hΘ
  exact ⟨isOrientation_sum_rn M σ hσ hM hc o hind, fun x _ =>
    ⟨orientedBranchingStructure_sum_rn M σ hσ hM hc o x, fun _ => rfl,
      fun y hy _ => (orientedSum_sum_rn_eq M σ hσ hM hc o hy).symm⟩⟩

end EpGroupoid

open MPolyfold EpGroupoid

/-- The oriented lifts of Example 9.3.5 are `1`-dimensional orientations. -/
theorem orientedLift1_isOrientationOfDim
    (hind : (trivial (rnPolyfold 2)).HasIndependentTangentSums example935Theta)
    (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientationOfDim example935Theta 1 (orientedLift1 ε) :=
  isOrientationOfDim_sum_rn (fun b => graph2 (beta1 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b))
    (fun b => isClosed_graph2 (contDiff_beta1 b).continuous) (orient1 ε) rfl hind

theorem orientedLift2_isOrientationOfDim
    (hind : (trivial (rnPolyfold 2)).HasIndependentTangentSums example935Theta)
    (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientationOfDim example935Theta 1 (orientedLift2 ε) :=
  isOrientationOfDim_sum_rn (fun b => graph2 (beta2 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta2 b))
    (fun b => isClosed_graph2 (contDiff_beta2 b).continuous) (orient2 ε)
    example935Theta_eq_two hind

/-! ### Lemma 9.3.4 without equidimensionality -/

section MixedDim

/-- The line `ℝ × {0}` (`true`) and the point `{0}` (`false`) in `ℝ²`. -/
def mixedM (b : Bool) : Set (Fin 2 → ℝ) := cond b (graph2 fun _ => 0) {0}

/-- Their dimensions `1` and `0`. -/
def mixedDim (b : Bool) : ℕ := cond b 1 0

open scoped Classical in
/-- `Θ = 1_{ℝ × {0}} + 1_{(0, 0)}`. -/
def mixedTheta (y : Fin 2 → ℝ) : ℚ := ∑ b with y ∈ mixedM b, (1 : ℚ)

theorem mixedM_isSubmanifoldOfDim :
    ∀ b, (rnPolyfold 2).IsSubmanifoldOfDim (mixedM b) (mixedDim b)
  | true => rnPolyfold_isSubmanifoldOfDim_graph2 contDiff_const
  | false => rnPolyfold_isSubmanifoldOfDim_singleton 0

theorem isClosed_mixedM : ∀ b, IsClosed (mixedM b)
  | true => isClosed_graph2 continuous_const
  | false => isClosed_singleton

theorem zero_mem_mixedM : ∀ b, (0 : Fin 2 → ℝ) ∈ mixedM b
  | true => show (0 : Fin 2 → ℝ) 1 = (fun _ : ℝ => (0 : ℝ)) ((0 : Fin 2 → ℝ) 0) from rfl
  | false => mem_singleton _

/-- `Θ` is a branched ep⁺-subgroupoid (of mixed dimension). -/
theorem mixedTheta_isBranched : (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid mixedTheta :=
  isBranchedEpSubgroupoid_sum_rn mixedM (fun _ => 1) (fun _ => one_pos)
    (fun b => (mixedM_isSubmanifoldOfDim b).1) isClosed_mixedM

/-- The orientations of the line (by `(1, 0)`) and of the point (by `O`). -/
def mixedOrient (O : Set (Fin 0 → (rnPolyfold 2).TangentSpace))
    (hO : (rnPolyfold 2).IsOrientedAt 0 ⟨0, (rnPolyfold 2).submanifoldTangent {0} 0, O⟩) :
    ∀ b, (rnPolyfold 2).SubmanifoldOrientation (mixedM b) (mixedDim b)
  | true => graphOrientation contDiff_const 1 one_ne_zero
  | false => SubmanifoldOrientation.ofPoint O hO

/-- **`(0, 0)` is a bad point of `Θ`**: near `(0, 0)` the line and the point do not coincide. -/
theorem zero_not_mem_goodSet_mixed :
    (0 : Fin 2 → ℝ) ∉ (trivial (rnPolyfold 2)).goodSet mixedTheta := by
  rintro ⟨-, x', B', h0U', hg'⟩
  let B : (trivial (rnPolyfold 2)).LocalBranchingStructure mixedTheta 0 :=
    localBranchingStructure_sum_rn mixedM (fun _ => 1) (fun _ => one_pos)
      (fun b => (mixedM_isSubmanifoldOfDim b).1) isClosed_mixedM 0
  obtain ⟨-, V, hV, h0V, -, hcoinc⟩ := B'.lemma_9_2_3 B h0U' B.mem_U hg'
  have hf : Continuous fun s : ℝ => s • (![1, 0] : Fin 2 → ℝ) :=
    continuous_id.smul continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hV.preimage hf) 0
    (show (0 : ℝ) • (![1, 0] : Fin 2 → ℝ) ∈ V by rw [zero_smul]; exact h0V)
  have hzV : (ε / 2) • (![1, 0] : Fin 2 → ℝ) ∈ V := hball (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith)
  have hz : (ε / 2) • (![1, 0] : Fin 2 → ℝ) ∈ V ∩ B.M ⟨true, zero_mem_mixedM true⟩ :=
    ⟨hzV, show ((ε / 2) • (![1, 0] : Fin 2 → ℝ)) 1 =
      (fun _ : ℝ => (0 : ℝ)) (((ε / 2) • (![1, 0] : Fin 2 → ℝ)) 0) by simp,
      fun b _ => zero_mem_mixedM b⟩
  rw [hcoinc ⟨true, zero_mem_mixedM true⟩ ⟨false, zero_mem_mixedM false⟩ (B.mem_M _)
    (B.mem_M _)] at hz
  have h0 := congrFun (show (ε / 2) • (![1, 0] : Fin 2 → ℝ) = 0 from hz.2.1) 0
  simp at h0
  linarith

open scoped Classical in
/-- **Lemma 9.3.4 does not hold as we read it without equidimensionality**: for
`Θ = 1_{ℝ × {0}} + 1_{(0, 0)}` (a branched ep⁺-subgroupoid of `ℝ²`), the two orientations
`T_y(ℝ × {0}, +) + T_y({0}, ±)` agree at every good point but differ at the bad point `(0, 0)`
(given Theorem 9.2.1's independence for `Θ`). -/
theorem lemma_9_3_4_mixed_dim
    (hind : (trivial (rnPolyfold 2)).HasIndependentTangentSums mixedTheta) :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid mixedTheta ∧
    ∃ T₁ T₂ : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ,
      (trivial (rnPolyfold 2)).IsOrientation mixedTheta T₁ ∧
      (trivial (rnPolyfold 2)).IsOrientation mixedTheta T₂ ∧
      (∀ y ∈ (trivial (rnPolyfold 2)).goodSet mixedTheta, T₁ y = T₂ y) ∧ T₁ 0 ≠ T₂ 0 := by
  obtain ⟨O₁, O₂, hne, h₁, h₂⟩ := exists_two_orientations_point (n := 2) 0
  refine ⟨mixedTheta_isBranched, orientedSumRn mixedM (fun _ => 1) (mixedOrient O₁ h₁),
    orientedSumRn mixedM (fun _ => 1) (mixedOrient O₂ h₂),
    isOrientation_sum_rn' mixedM (fun _ => 1) (fun _ => one_pos) mixedM_isSubmanifoldOfDim
      isClosed_mixedM _ rfl hind,
    isOrientation_sum_rn' mixedM (fun _ => 1) (fun _ => one_pos) mixedM_isSubmanifoldOfDim
      isClosed_mixedM _ rfl hind, fun y hy => ?_, fun h => ?_⟩
  · have hy0 : y ∉ mixedM false := fun h => zero_not_mem_goodSet_mixed (h ▸ hy)
    rw [orientedSumRn_bool, orientedSumRn_bool, if_neg hy0, if_neg hy0]
    rfl
  · rw [orientedSumRn_bool, orientedSumRn_bool, if_pos (zero_mem_mixedM true),
      if_pos (zero_mem_mixedM true), if_pos (zero_mem_mixedM false),
      if_pos (zero_mem_mixedM false)] at h
    have h' := (Finsupp.single_left_inj one_ne_zero).1 (add_left_cancel h)
    apply hne
    change (⟨0, (rnPolyfold 2).submanifoldTangent {0} 0, O₁⟩ : (rnPolyfold 2).OrTangent) =
      ⟨0, (rnPolyfold 2).submanifoldTangent {0} 0, O₂⟩ at h'
    simpa using h'

end MixedDim

end Polyfold
