import Polyfold.Chapter5.PartitionsOfUnity

/-!
# Norm-one projections in WCG spaces (Amir–Lindenstrauss)

A tool for the non-separable case of 2021 Theorem 5.5.16, p. 235 (preprint 5.43).

Let `X` be a Banach space and `K ⊆ X` weakly compact with dense span. A pair `(A, D)` with
`A ⊆ X` and `D ⊆ X*` is a **Lindenstrauss pair for `K`** (`IsLPair K A D`) if:
* `A` is a `ℚ`-linear subspace;
* `D` norms `A`: every `a ∈ A` has some `f ∈ D` with `‖f‖ ≤ 1` and `f a = ‖a‖`;
* `A ∩ K` is dense in `K` for the topology of `D`: for every finite `u ⊆ D`, `x ∈ K` and `ε > 0`,
  some `a ∈ A ∩ K` has `|f a − f x| < ε` for all `f ∈ u`.

`IsLPair.exists_proj` then gives a projection `P` with these properties:
* `‖P‖ ≤ 1`;
* its range is the closure of `A`;
* `f ∘ P = f` for `f ∈ D`, i.e. `P` is the projection along `D_⊥`.

*Proof.*
1. Weak compactness (`IsCompact.inter_iInter_nonempty` in `WeakSpace ℝ X`) and Mazur's theorem
   (`Convex.toWeakSpace_closure`) put every `x ∈ K` in `cl A + D_⊥`.
2. Norming makes `cl A + D_⊥` closed, so it is all of `X`, and makes the decomposition unique
   with `‖P x‖ ≤ ‖x‖`.

Krein's theorem (convex hulls of weakly compact sets) is not needed. Only the density of `A ∩ K`
in `K` for the topology of `D` is used, not convexity of `K`.
-/

open Set Function Filter Topology Metric
open scoped Cardinal

noncomputable section

namespace Polyfold

universe u

section LPair

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A **Lindenstrauss pair** `(A, D)` for `K` (a tool for 2021 Theorem 5.5.16, p. 235). -/
structure IsLPair (K A : Set X) (D : Set (StrongDual ℝ X)) : Prop where
  zero_mem : (0 : X) ∈ A
  add_mem : ∀ a ∈ A, ∀ b ∈ A, a + b ∈ A
  qsmul_mem : ∀ q : ℚ, ∀ a ∈ A, (q : ℝ) • a ∈ A
  norming : ∀ a ∈ A, ∃ f ∈ D, ‖f‖ ≤ 1 ∧ f a = ‖a‖
  rich : ∀ u : Finset (StrongDual ℝ X), (↑u : Set (StrongDual ℝ X)) ⊆ D → ∀ x ∈ K, ∀ ε > 0,
    ∃ a ∈ A ∩ K, ∀ f ∈ u, |f a - f x| < ε

variable {K A : Set X} {D : Set (StrongDual ℝ X)}

namespace IsLPair

/-- The closure of `A` is a linear subspace. -/
def sub (hp : IsLPair K A D) : Submodule ℝ X where
  carrier := closure A
  add_mem' {a b} ha hb :=
    map_mem_closure₂ continuous_add ha hb fun a ha b hb => hp.add_mem a ha b hb
  zero_mem' := subset_closure hp.zero_mem
  smul_mem' c a ha := by
    have hq : ∀ q : ℚ, (q : ℝ) • a ∈ closure A := fun q =>
      map_mem_closure (continuous_const_smul (q : ℝ)) ha fun b hb => hp.qsmul_mem q b hb
    exact Rat.denseRange_cast.induction_on (p := fun r : ℝ => r • a ∈ closure A) c
      (isClosed_closure.preimage (continuous_id.smul continuous_const)) hq

lemma mem_sub (hp : IsLPair K A D) {x : X} : x ∈ hp.sub ↔ x ∈ closure A := Iff.rfl

/-- **Norming on the closure**: if `z ∈ cl A` and `f z = f w` for all `f ∈ D`, then
`‖z‖ ≤ ‖w‖`. -/
lemma norm_le (hp : IsLPair K A D) {z w : X} (hz : z ∈ closure A) (hzw : ∀ f ∈ D, f z = f w) :
    ‖z‖ ≤ ‖w‖ := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, ha, hza⟩ := Metric.mem_closure_iff.1 hz (ε / 2) (by positivity)
  obtain ⟨f, hfD, hf1, hfa⟩ := hp.norming a ha
  rw [dist_eq_norm] at hza
  have h1 : f a - f z ≤ ‖a - z‖ := by
    rw [← map_sub]
    exact (le_abs_self _).trans ((f.le_opNorm _).trans (by
      rw [← norm_neg (a - z), neg_sub]; nlinarith [norm_nonneg (z - a)]))
  have h2 : f w ≤ ‖w‖ :=
    (le_abs_self _).trans ((f.le_opNorm w).trans (by nlinarith [norm_nonneg w]))
  have h3 : ‖z‖ ≤ ‖a‖ + ‖z - a‖ := by
    have := norm_add_le a (z - a); rwa [add_sub_cancel] at this
  have h4 : ‖a - z‖ = ‖z - a‖ := norm_sub_rev a z
  rw [← hfa, ← hzw f hfD] at *
  linarith

/-- **Uniqueness**: a point of `cl A` is determined by the values of `D` on it. -/
lemma eq_of_forall (hp : IsLPair K A D) {m m' : X} (hm : m ∈ closure A) (hm' : m' ∈ closure A)
    (h : ∀ f ∈ D, f m = f m') : m = m' := by
  have hz : m - m' ∈ closure A := hp.sub.sub_mem hm hm'
  have := hp.norm_le (w := 0) hz fun f hf => by rw [map_sub, h f hf, sub_self, map_zero]
  rw [norm_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- **The weak compactness step**: every `x ∈ K` agrees on `D` with a point of `cl A`. -/
lemma exists_mem_closure (hp : IsLPair K A D) (hK : IsCompact (toWeakSpace ℝ X '' K)) {x : X}
    (hx : x ∈ K) : ∃ m ∈ closure A, ∀ f ∈ D, f m = f x := by
  classical
  set T := toWeakSpace ℝ X with hT
  have hev : ∀ f : StrongDual ℝ X, Continuous fun w : WeakSpace ℝ X => f (T.symm w) := fun f =>
    WeakBilin.eval_continuous (topDualPairing ℝ X).flip f
  set s : Set (WeakSpace ℝ X) := T '' K ∩ closure (T '' (A ∩ K)) with hs
  have hsc : IsCompact s := hK.inter_right isClosed_closure
  set t : D → Set (WeakSpace ℝ X) := fun f => {w | f.1 (T.symm w) = f.1 x} with ht
  have htc : ∀ f, IsClosed (t f) := fun f => isClosed_eq (hev f) continuous_const
  obtain ⟨w, ⟨⟨-, hwcl⟩, hwt⟩⟩ := hsc.inter_iInter_nonempty t htc fun u => by
    set Φ : WeakSpace ℝ X → (u → ℝ) := fun w i => (i : D).1 (T.symm w) with hΦ
    have hΦc : Continuous Φ := continuous_pi fun i => hev _
    have hcl : IsClosed (Φ '' s) := (hsc.image hΦc).isClosed
    have hsub : T '' (A ∩ K) ⊆ s := fun w hw =>
      ⟨image_mono inter_subset_right hw, subset_closure hw⟩
    have hmem : Φ (T x) ∈ closure (Φ '' (T '' (A ∩ K))) := by
      refine Metric.mem_closure_iff.2 fun ε hε => ?_
      obtain ⟨a, ha, haf⟩ := hp.rich (u.image fun i => (i : D).1)
        (by intro f hf; obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hf; exact i.2) x hx
        (ε / 2) (by positivity)
      refine ⟨Φ (T a), ⟨T a, ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
      refine (dist_pi_le_iff (by positivity)).2 (fun i => ?_) |>.trans_lt (half_lt_self hε)
      rw [Real.dist_eq, abs_sub_comm]
      exact (haf _ (Finset.mem_image_of_mem _ i.2)).le
    have hin : Φ (T x) ∈ Φ '' s :=
      closure_minimal (image_mono hsub) hcl hmem
    obtain ⟨w, hws, hwx⟩ := hin
    refine ⟨w, hws, mem_iInter₂.2 fun i hi => ?_⟩
    have := congrFun hwx ⟨i, hi⟩
    simp only [hΦ] at this
    simpa [ht, T] using this
  -- `w` lies in the weak closure of `cl A`, which is `T '' cl A` (Mazur)
  have hconv : Convex ℝ (closure A) := hp.sub.convex
  have hw : w ∈ T '' closure A := by
    rw [← closure_closure (s := A), hconv.toWeakSpace_closure ℝ]
    exact closure_mono (image_mono (inter_subset_left.trans subset_closure)) hwcl
  obtain ⟨m, hm, rfl⟩ := hw
  refine ⟨m, hm, fun f hf => ?_⟩
  have := mem_iInter.1 hwt ⟨f, hf⟩
  simpa [t] using this

/-- **The projection of a Lindenstrauss pair** (Amir–Lindenstrauss; a tool for 2021 Theorem
5.5.16, p. 235). In a Banach space with a weakly compact `K` of dense span, a Lindenstrauss pair
`(A, D)` for `K` gives a norm-one projection onto `cl A` along `D_⊥`. -/
theorem exists_proj [CompleteSpace X] (hp : IsLPair K A D)
    (hK : IsCompact (toWeakSpace ℝ X '' K))
    (hspan : closure (Submodule.span ℝ K : Set X) = univ) :
    ∃ P : X →L[ℝ] X, (∀ x, P x ∈ closure A) ∧ (∀ x, ∀ f ∈ D, f (P x) = f x) ∧ ‖P‖ ≤ 1 := by
  classical
  -- the subspace `cl A + D_⊥`
  let W : Submodule ℝ X :=
    { carrier := {x | ∃ m ∈ closure A, ∀ f ∈ D, f m = f x}
      add_mem' := by
        rintro x y ⟨m, hm, hmx⟩ ⟨m', hm', hmy⟩
        exact ⟨m + m', hp.sub.add_mem hm hm', fun f hf => by
          rw [map_add, map_add, hmx f hf, hmy f hf]⟩
      zero_mem' := ⟨0, hp.sub.zero_mem, fun f _ => rfl⟩
      smul_mem' := by
        rintro c x ⟨m, hm, hmx⟩
        exact ⟨c • m, hp.sub.smul_mem c hm, fun f hf => by
          rw [map_smul, map_smul, hmx f hf]⟩ }
  have hKW : K ⊆ W := fun x hx => hp.exists_mem_closure hK hx
  have hWcl : IsClosed (W : Set X) := by
    refine isClosed_of_closure_subset fun x hx => ?_
    obtain ⟨xs, hxs, hlim⟩ := mem_closure_iff_seq_limit.1 hx
    choose ms hms hmsx using hxs
    have hcauchy : CauchySeq ms := by
      refine Metric.cauchySeq_iff.2 fun ε hε => ?_
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq ε hε
      refine ⟨N, fun i hi j hj => ?_⟩
      rw [dist_eq_norm]
      refine lt_of_le_of_lt (hp.norm_le (hp.sub.sub_mem (hms i) (hms j)) fun f hf => ?_)
        (by rw [← dist_eq_norm]; exact hN i hi j hj)
      rw [map_sub, map_sub, hmsx i f hf, hmsx j f hf]
    obtain ⟨m, hm⟩ := cauchySeq_tendsto_of_complete hcauchy
    refine ⟨m, isClosed_closure.mem_of_tendsto hm (Eventually.of_forall hms), fun f hf => ?_⟩
    refine tendsto_nhds_unique ((f.continuous.tendsto m).comp hm) ?_
    have : (fun n => f (ms n)) = fun n => f (xs n) := funext fun n => hmsx n f hf
    rw [comp_def, this]
    exact (f.continuous.tendsto x).comp hlim
  have hWuniv : ∀ x, x ∈ W := by
    intro x
    have hspW : (Submodule.span ℝ K : Set X) ⊆ W := Submodule.span_le.2 hKW
    have : x ∈ closure (Submodule.span ℝ K : Set X) := by rw [hspan]; trivial
    exact closure_minimal hspW hWcl this
  choose P₀ hP₀A hP₀f using hWuniv
  have hadd : ∀ x y, P₀ (x + y) = P₀ x + P₀ y := fun x y =>
    hp.eq_of_forall (hP₀A _) (hp.sub.add_mem (hP₀A x) (hP₀A y)) fun f hf => by
      rw [hP₀f _ f hf, map_add, map_add, hP₀f x f hf, hP₀f y f hf]
  have hsmul : ∀ (c : ℝ) x, P₀ (c • x) = c • P₀ x := fun c x =>
    hp.eq_of_forall (hP₀A _) (hp.sub.smul_mem c (hP₀A x)) fun f hf => by
      rw [hP₀f _ f hf, map_smul, map_smul, hP₀f x f hf]
  have hbound : ∀ x, ‖P₀ x‖ ≤ 1 * ‖x‖ := fun x => by
    rw [one_mul]; exact hp.norm_le (hP₀A x) (hP₀f x)
  let L : X →ₗ[ℝ] X := ⟨⟨P₀, hadd⟩, hsmul⟩
  exact ⟨L.mkContinuous 1 hbound, hP₀A, hP₀f, LinearMap.mkContinuous_norm_le _ zero_le_one _⟩

end IsLPair

end LPair

/-! ### The Lindenstrauss closure of a set -/

section Closure

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A norming functional of `x` (Hahn–Banach). -/
def lclNrm (x : X) : StrongDual ℝ X := (exists_dual_vector'' ℝ x).choose

lemma lclNrm_spec (x : X) : ‖lclNrm x‖ ≤ 1 ∧ lclNrm x x = ‖x‖ :=
  (exists_dual_vector'' ℝ x).choose_spec

open Classical in
/-- A point of `K` in the box `|p.1 − p.2| < 1/(n+1)`, `p ∈ u`, if there is one. -/
def lclWit (K : Set X) (u : Finset (StrongDual ℝ X × ℚ)) (n : ℕ) : X :=
  if h : ∃ k ∈ K, ∀ p ∈ u, |p.1 k - p.2| < 1 / ((n : ℝ) + 1) then h.choose else 0

lemma lclWit_spec {K : Set X} {u : Finset (StrongDual ℝ X × ℚ)} {n : ℕ}
    (h : ∃ k ∈ K, ∀ p ∈ u, |p.1 k - p.2| < 1 / ((n : ℝ) + 1)) :
    lclWit K u n ∈ K ∧ ∀ p ∈ u, |p.1 (lclWit K u n) - p.2| < 1 / ((n : ℝ) + 1) := by
  classical
  rw [lclWit, dif_pos h]; exact h.choose_spec

/-- The witnesses for boxes built on functionals of `D`. -/
def lclWitSet (K : Set X) (D : Set (StrongDual ℝ X)) : Set X :=
  {x | ∃ (u : Finset (StrongDual ℝ X × ℚ)) (n : ℕ), (∀ p ∈ u, p.1 ∈ D) ∧ lclWit K u n = x}

/-- Sums of two elements of `A`. -/
def lclAddSet (A : Set X) : Set X := range fun p : A × A => (p.1 : X) + p.2

/-- Rational multiples of elements of `A`. -/
def lclQSet (A : Set X) : Set X := range fun p : ULift.{u} ℚ × A => ((p.1.down : ℚ) : ℝ) • (p.2 : X)

/-- One step of the closure, on the `X` side. -/
def lclStepA (K A : Set X) (D : Set (StrongDual ℝ X)) : Set X :=
  A ∪ lclAddSet A ∪ lclQSet A ∪ lclWitSet K D ∪ {0}

/-- One step of the closure, on the dual side. -/
def lclStepD (A : Set X) (D : Set (StrongDual ℝ X)) : Set (StrongDual ℝ X) := D ∪ lclNrm '' A

/-- The iterates of the closure step, from `(S, ∅)`. -/
def iterL (K S : Set X) : ℕ → Set X × Set (StrongDual ℝ X)
  | 0 => (S, ∅)
  | n + 1 => (lclStepA K (iterL K S n).1 (iterL K S n).2, lclStepD (iterL K S n).1 (iterL K S n).2)

/-- The **Lindenstrauss closure** of `S`, `X` side. -/
def lclA (K S : Set X) : Set X := ⋃ n, (iterL K S n).1

/-- The **Lindenstrauss closure** of `S`, dual side. -/
def lclD (K S : Set X) : Set (StrongDual ℝ X) := ⋃ n, (iterL K S n).2

variable {K : Set X}

lemma iterL_succ (S : Set X) (n : ℕ) : iterL K S (n + 1) =
    (lclStepA K (iterL K S n).1 (iterL K S n).2, lclStepD (iterL K S n).1 (iterL K S n).2) := rfl

lemma subset_lclStepA (A : Set X) (D : Set (StrongDual ℝ X)) : A ⊆ lclStepA K A D :=
  fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h)))

lemma iterL_mono_n (S : Set X) : Monotone fun n => (iterL K S n).1 :=
  monotone_nat_of_le_succ fun n => by
    simp only [iterL_succ]; exact subset_lclStepA _ _

lemma iterL_mono_n' (S : Set X) : Monotone fun n => (iterL K S n).2 :=
  monotone_nat_of_le_succ fun n => by
    simp only [iterL_succ]; exact subset_union_left

lemma lclStepA_mono {A A' : Set X} {D D' : Set (StrongDual ℝ X)} (hA : A ⊆ A') (hD : D ⊆ D') :
    lclStepA K A D ⊆ lclStepA K A' D' := by
  refine union_subset_union (union_subset_union (union_subset_union (union_subset_union hA ?_)
    ?_) ?_) le_rfl
  · rintro _ ⟨p, rfl⟩; exact ⟨(⟨p.1, hA p.1.2⟩, ⟨p.2, hA p.2.2⟩), rfl⟩
  · rintro _ ⟨p, rfl⟩; exact ⟨(p.1, ⟨p.2, hA p.2.2⟩), rfl⟩
  · rintro _ ⟨u, n, hu, rfl⟩; exact ⟨u, n, fun p hp => hD (hu p hp), rfl⟩

lemma lclStepD_mono {A A' : Set X} {D D' : Set (StrongDual ℝ X)} (hA : A ⊆ A') (hD : D ⊆ D') :
    lclStepD A D ⊆ lclStepD A' D' :=
  union_subset_union hD (image_mono hA)

lemma iterL_mono_S {S S' : Set X} (h : S ⊆ S') (n : ℕ) :
    (iterL K S n).1 ⊆ (iterL K S' n).1 ∧ (iterL K S n).2 ⊆ (iterL K S' n).2 := by
  induction n with
  | zero => exact ⟨h, le_rfl⟩
  | succ n ih =>
    simp only [iterL_succ]
    exact ⟨lclStepA_mono ih.1 ih.2, lclStepD_mono ih.1 ih.2⟩

lemma lclA_mono {S S' : Set X} (h : S ⊆ S') : lclA K S ⊆ lclA K S' :=
  iUnion_mono fun n => (iterL_mono_S h n).1

lemma lclD_mono {S S' : Set X} (h : S ⊆ S') : lclD K S ⊆ lclD K S' :=
  iUnion_mono fun n => (iterL_mono_S h n).2

lemma subset_lclA (S : Set X) : S ⊆ lclA K S := fun _ hx => mem_iUnion.2 ⟨0, hx⟩

/-- A finite subset of an increasing union lies in one member. -/
lemma lcl_finset_subset_of_monotone {α : Type*} {F : ℕ → Set α} (hF : Monotone F)
    (u : Finset α) (hu : (↑u : Set α) ⊆ ⋃ n, F n) : ∃ N, (↑u : Set α) ⊆ F N := by
  classical
  induction u using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s _ ih =>
    rw [Finset.coe_insert, insert_subset_iff] at hu
    obtain ⟨n, hn⟩ := mem_iUnion.1 hu.1
    obtain ⟨N, hN⟩ := ih hu.2
    refine ⟨max n N, ?_⟩
    rw [Finset.coe_insert, insert_subset_iff]
    exact ⟨hF (le_max_left n N) hn, hN.trans (hF (le_max_right n N))⟩

/-- **The Lindenstrauss closure is a Lindenstrauss pair.** -/
theorem isLPair_lcl (S : Set X) : IsLPair K (lclA K S) (lclD K S) := by
  classical
  have hA := iterL_mono_n (K := K) S
  have hD := iterL_mono_n' (K := K) S
  have hstep : ∀ n, lclStepA K (iterL K S n).1 (iterL K S n).2 ⊆ lclA K S := fun n _ hx =>
    mem_iUnion.2 ⟨n + 1, by rw [iterL_succ]; exact hx⟩
  refine ⟨hstep 0 (Or.inr rfl), fun a ha b hb => ?_, fun q a ha => ?_, fun a ha => ?_,
    fun u hu x hx ε hε => ?_⟩
  · obtain ⟨n, hn⟩ := mem_iUnion.1 ha
    obtain ⟨m, hm⟩ := mem_iUnion.1 hb
    exact hstep (max n m) (Or.inl (Or.inl (Or.inl (Or.inr
      ⟨(⟨a, hA (le_max_left n m) hn⟩, ⟨b, hA (le_max_right n m) hm⟩), rfl⟩))))
  · obtain ⟨n, hn⟩ := mem_iUnion.1 ha
    exact hstep n (Or.inl (Or.inl (Or.inr ⟨(ULift.up q, ⟨a, hn⟩), rfl⟩)))
  · obtain ⟨n, hn⟩ := mem_iUnion.1 ha
    refine ⟨lclNrm a, mem_iUnion.2 ⟨n + 1, ?_⟩, lclNrm_spec a⟩
    rw [iterL_succ]; exact Or.inr ⟨a, hn, rfl⟩
  · obtain ⟨N, hN⟩ := lcl_finset_subset_of_monotone hD u hu
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt (by positivity : 0 < ε / 2)
    have hq : ∀ f : StrongDual ℝ X, ∃ q : ℚ, |f x - q| < 1 / ((n₀ : ℝ) + 1) := fun f => by
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
        (by linarith [show (0 : ℝ) < 1 / ((n₀ : ℝ) + 1) by positivity] :
          f x - 1 / ((n₀ : ℝ) + 1) < f x + 1 / ((n₀ : ℝ) + 1))
      exact ⟨q, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩⟩
    choose q hq using hq
    set u' := u.image fun f => (f, q f) with hu'
    have hex : ∃ k ∈ K, ∀ p ∈ u', |p.1 k - p.2| < 1 / ((n₀ : ℝ) + 1) := ⟨x, hx, by
      intro p hp; obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hp; exact hq f⟩
    obtain ⟨hwK, hwbox⟩ := lclWit_spec hex
    refine ⟨lclWit K u' n₀, ⟨hstep N (Or.inl (Or.inr ⟨u', n₀, ?_, rfl⟩)), hwK⟩, fun f hf => ?_⟩
    · intro p hp; obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hp; exact hN hf
    · have h1 := hwbox (f, q f) (Finset.mem_image_of_mem _ hf)
      have h2 := hq f
      calc |f (lclWit K u' n₀) - f x| ≤ |f (lclWit K u' n₀) - q f| + |f x - q f| := by
            rw [abs_sub_comm (f x)]; exact abs_sub_le _ _ _
        _ < ε := by linarith

/-- **Finite character**: each point of the closure of `S` lies in the closure of a finite subset
of `S`. -/
theorem iterL_finite (S : Set X) (n : ℕ) :
    (∀ a ∈ (iterL K S n).1, ∃ F : Finset X, (↑F : Set X) ⊆ S ∧ a ∈ (iterL K ↑F n).1) ∧
      ∀ f ∈ (iterL K S n).2, ∃ F : Finset X, (↑F : Set X) ⊆ S ∧ f ∈ (iterL K ↑F n).2 := by
  classical
  induction n with
  | zero =>
    refine ⟨fun a ha => ⟨{a}, by simpa [iterL] using ha, by simp [iterL]⟩, fun f hf => ?_⟩
    simp [iterL] at hf
  | succ n ih =>
    obtain ⟨ihA, ihD⟩ := ih
    have monoA : ∀ {F F' : Finset X}, F ⊆ F' → (iterL K (↑F) n).1 ⊆ (iterL K (↑F') n).1 :=
      fun h => (iterL_mono_S (Finset.coe_subset.2 h) n).1
    have monoD : ∀ {F F' : Finset X}, F ⊆ F' → (iterL K (↑F) n).2 ⊆ (iterL K (↑F') n).2 :=
      fun h => (iterL_mono_S (Finset.coe_subset.2 h) n).2
    simp only [iterL_succ]
    refine ⟨fun a ha => ?_, fun f hf => ?_⟩
    · rcases ha with ((((ha | ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨u, m, hu, rfl⟩) | ha)
      · obtain ⟨F, hF, haF⟩ := ihA a ha
        exact ⟨F, hF, subset_lclStepA _ _ haF⟩
      · obtain ⟨F₁, hF₁, h₁⟩ := ihA _ p.1.2
        obtain ⟨F₂, hF₂, h₂⟩ := ihA _ p.2.2
        refine ⟨F₁ ∪ F₂, by rw [Finset.coe_union]; exact union_subset hF₁ hF₂,
          Or.inl (Or.inl (Or.inl (Or.inr ⟨(⟨p.1, monoA Finset.subset_union_left h₁⟩,
            ⟨p.2, monoA Finset.subset_union_right h₂⟩), rfl⟩)))⟩
      · obtain ⟨F, hF, h⟩ := ihA _ p.2.2
        exact ⟨F, hF, Or.inl (Or.inl (Or.inr ⟨(p.1, ⟨p.2, h⟩), rfl⟩))⟩
      · have hu' : ∀ p : u, ∃ F : Finset X, (↑F : Set X) ⊆ S ∧ p.1.1 ∈ (iterL K ↑F n).2 :=
          fun p => ihD _ (hu p.1 p.2)
        choose F hF hpF using hu'
        refine ⟨u.attach.biUnion F, ?_, Or.inl (Or.inr ⟨u, m, fun p hp => ?_, rfl⟩)⟩
        · intro x hx
          obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 hx
          exact hF p hp
        · exact monoD (Finset.subset_biUnion_of_mem F (Finset.mem_attach u ⟨p, hp⟩))
            (hpF ⟨p, hp⟩)
      · exact ⟨∅, by simp, Or.inr ha⟩
    · rcases hf with hf | ⟨a, ha, rfl⟩
      · obtain ⟨F, hF, h⟩ := ihD f hf
        exact ⟨F, hF, Or.inl h⟩
      · obtain ⟨F, hF, h⟩ := ihA a ha
        exact ⟨F, hF, Or.inr ⟨a, h, rfl⟩⟩

/-- **Finite character of the closure.** -/
theorem lclA_finite (S : Set X) {a : X} (ha : a ∈ lclA K S) :
    ∃ F : Finset X, (↑F : Set X) ⊆ S ∧ a ∈ lclA K ↑F := by
  obtain ⟨n, hn⟩ := mem_iUnion.1 ha
  obtain ⟨F, hF, h⟩ := (iterL_finite S n).1 a hn
  exact ⟨F, hF, mem_iUnion.2 ⟨n, h⟩⟩

/-! #### Cardinality -/

lemma lcl_mk_finset_le_max (α : Type u) : #(Finset α) ≤ max #α ℵ₀ := by
  rcases finite_or_infinite α with h | h
  · exact Cardinal.mk_le_aleph0.trans (le_max_right _ _)
  · rw [Cardinal.mk_finset_of_infinite]; exact le_max_left _ _

lemma lcl_card_mul_le {a b c : Cardinal} (hc : ℵ₀ ≤ c) (ha : a ≤ c) (hb : b ≤ c) : a * b ≤ c :=
  (Cardinal.mul_le_max a b).trans (max_le (max_le ha hb) hc)

lemma lcl_mk_iUnion_nat_le {α : Type u} (A : ℕ → Set α) {c : Cardinal.{u}} (hc : ℵ₀ ≤ c)
    (h : ∀ n, #(A n) ≤ c) : #(⋃ n, A n) ≤ c := by
  have : (⋃ n, A n) = ⋃ i : ULift.{u} ℕ, A i.down := by
    ext x; simp only [mem_iUnion]
    exact ⟨fun ⟨n, hn⟩ => ⟨ULift.up n, hn⟩, fun ⟨i, hi⟩ => ⟨i.down, hi⟩⟩
  rw [this]
  refine (Cardinal.mk_iUnion_le _).trans (lcl_card_mul_le hc (Cardinal.mk_le_aleph0.trans hc) ?_)
  exact ciSup_le' fun i => h i.down

lemma card_lclStepA {A : Set X} {D : Set (StrongDual ℝ X)} {c : Cardinal.{u}} (hc : ℵ₀ ≤ c)
    (hA : #A ≤ c) (hD : #D ≤ c) : #(lclStepA K A D) ≤ c := by
  classical
  have h1 : #(lclAddSet A) ≤ c := Cardinal.mk_range_le.trans (by
    simp only [Cardinal.mk_prod, Cardinal.lift_id]; exact lcl_card_mul_le hc hA hA)
  have h2 : #(lclQSet A) ≤ c := Cardinal.mk_range_le.trans (by
    simp only [Cardinal.mk_prod, Cardinal.lift_id]
    exact lcl_card_mul_le hc (Cardinal.mk_le_aleph0.trans hc) hA)
  have h3 : #(lclWitSet K D) ≤ c := by
    let g : Finset (D × ULift.{u} ℚ) × ULift.{u} ℕ → X := fun p =>
      lclWit K (p.1.image fun r => ((r.1 : StrongDual ℝ X), (r.2.down : ℚ))) p.2.down
    have hsub : lclWitSet K D ⊆ range g := by
      rintro _ ⟨u, n, hu, rfl⟩
      refine ⟨(u.attach.image fun p => (⟨p.1.1, hu p.1 p.2⟩, ULift.up p.1.2), ULift.up n), ?_⟩
      simp only [g, Finset.image_image]
      congr 1
      ext p
      simp
    refine (Cardinal.mk_le_mk_of_subset hsub).trans (Cardinal.mk_range_le.trans ?_)
    simp only [Cardinal.mk_prod, Cardinal.lift_id]
    refine lcl_card_mul_le hc ((lcl_mk_finset_le_max _).trans (max_le ?_ hc))
      (Cardinal.mk_le_aleph0.trans hc)
    simp only [Cardinal.mk_prod, Cardinal.lift_id]
    exact lcl_card_mul_le hc hD (Cardinal.mk_le_aleph0.trans hc)
  have h4 : #({0} : Set X) ≤ c := by
    rw [Cardinal.mk_singleton]; exact Cardinal.one_le_aleph0.trans hc
  refine (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hc ?_ h4)
  refine (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hc ?_ h3)
  refine (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hc ?_ h2)
  exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hc hA h1)

lemma card_lclStepD {A : Set X} {D : Set (StrongDual ℝ X)} {c : Cardinal.{u}} (hc : ℵ₀ ≤ c)
    (hA : #A ≤ c) (hD : #D ≤ c) : #(lclStepD A D) ≤ c :=
  (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hc hD (Cardinal.mk_image_le.trans hA))

/-- **Cardinality of the closure**: at most `max(#S, ℵ₀)`. -/
theorem card_lcl {S : Set X} {c : Cardinal.{u}} (hc : ℵ₀ ≤ c) (hS : #S ≤ c) :
    #(lclA K S) ≤ c ∧ #(lclD K S) ≤ c := by
  have h : ∀ n, #(iterL K S n).1 ≤ c ∧ #(iterL K S n).2 ≤ c := by
    intro n
    induction n with
    | zero => exact ⟨hS, by simp [iterL]⟩
    | succ n ih =>
      rw [iterL_succ]
      exact ⟨card_lclStepA hc ih.1 ih.2, card_lclStepD hc ih.1 ih.2⟩
  exact ⟨lcl_mk_iUnion_nat_le _ hc fun n => (h n).1, lcl_mk_iUnion_nat_le _ hc fun n => (h n).2⟩

end Closure

end Polyfold
