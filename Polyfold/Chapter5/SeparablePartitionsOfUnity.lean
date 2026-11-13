import Polyfold.Chapter5.PartitionsOfUnity

/-!
# Smooth partitions of unity on separable spaces, and Corollary 5.5.17 without hypothesis

2021 Theorem 5.5.16, p. 235 (2017: Theorem 5.14; preprint: Theorem 5.43), cited from
Godefroy–Troyanski–Whitfield–Zizler: a WCG Banach space with a `C^k`-bump function admits `C^k`
partitions of unity.  2021 Corollary 5.5.17, p. 235 (preprint 5.44) applies it to `E₀` a Hilbert
space.  The project states Corollary 5.5.17 with Theorem 5.5.16 as a hypothesis (row V5.63).

Two facts remove the hypothesis.

* **The `0`-level of an sc-Banach space is separable** (`ScBanach.separableSpace_zero`): the
  inclusion `E₁ → E₀` is a compact operator with dense range, and the range of a compact operator
  is separable.
* **A separable Banach space with a `C^k`-bump function admits `C^k` partitions of unity**
  (`admitsContDiffPartitionsOfUnity_of_separable`; Bonic–Frampton 1966, the separable case of
  Theorem 5.5.16, and separable spaces are WCG by Proposition 5.5.15 (2)).  The proof: a bump
  `ψ = 1` near `0` with bounded support (from the given bump and a bump of `ℝ`), a countable cover
  by balls `B(xₙ, rₙ)` with `ψₙ = ψ((· − xₙ)/rₙ)` supported in a member of the cover
  (Lindelöf), the locally finite family `fₙ = ψₙ ∏_{j<n}(1 − ψⱼ)` with `Σ fₙ = 1`, which gives
  `C^k` Urysohn functions, and then Mathlib's bump coverings
  (`BumpCovering.exists_isSubordinate_of_prop`, `BumpCovering.toPartitionOfUnity`), as in `admitsScPartitionsOfUnity_of_approx`.

## What is formalized

* `ScBanach.separableSpace_zero`, `IsCompactOperator.isSeparable_range`.
* `HasContDiffBump.exists_one_on_ball`: a `C^k` bump `ψ : V → [0, 1]` with `ψ = 1` on `B(0, 1)`
  and support in `B(0, R)`.
* `exists_contDiff_urysohn_of_separable`: `C^k` Urysohn functions on a separable space with a
  `C^k` bump.
* `admitsContDiffPartitionsOfUnity_of_separable`, and
  `godefroyTroyanskiWhitfieldZizlerStatement_of_separable` (Theorem 5.5.16 for separable spaces).
* `corollary_5_5_17_unconditional`: 2021 Corollary 5.5.17 as stated, with no hypothesis.
* `MPolyfold.admitsScPartitionsOfUnity_of_hilbert_unconditional`: an M-polyfold built on
  sc-Hilbert spaces admits sc-smooth partitions of unity.
-/

open Set Function Filter Topology Metric
open scoped Pointwise

noncomputable section

namespace Polyfold

universe u

/-! ### The `0`-level of an sc-Banach space is separable -/

section Separable

/-- **The range of a compact operator is separable**: it lies in `⋃ₙ n·K` for a compact `K`. -/
theorem IsCompactOperator.isSeparable_range {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] {T : V →L[ℝ] W}
    (hT : IsCompactOperator T) : TopologicalSpace.IsSeparable (range T) := by
  obtain ⟨K, hK, hKn⟩ := hT
  have hsep : TopologicalSpace.IsSeparable (⋃ n : ℕ, (n : ℝ) • K) :=
    TopologicalSpace.IsSeparable.iUnion fun n => (hK.smul (n : ℝ)).isSeparable
  refine hsep.mono ?_
  rintro _ ⟨x, rfl⟩
  have htend : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • x) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).smul_const x
    simpa using this
  obtain ⟨n, hn⟩ := ((htend.eventually hKn).and (eventually_ge_atTop 1)).exists
  refine mem_iUnion.2 ⟨n, (n : ℝ)⁻¹ • x |> T, hn.1, ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn.2)
  simp only [map_smul, smul_smul, mul_inv_cancel₀ hn0, one_smul]

/-- **The `0`-level `E₀` of an sc-Banach space is separable**: the inclusion `E₁ → E₀` is a
compact operator (sc-structure) with dense range (`E_∞` is dense). -/
theorem ScBanach.separableSpace_zero (E : ScBanach) : TopologicalSpace.SeparableSpace (E 0) := by
  have h1 := IsCompactOperator.isSeparable_range (E.incl_isCompactOperator 0)
  have h2 : closure (range (E.incl 0)) = univ := (E.denseRange_incl 0).closure_range
  rw [← TopologicalSpace.isSeparable_univ_iff, ← h2]
  exact h1.closure

end Separable

/-! ### Separable spaces with a `C^k` bump admit `C^k` partitions of unity -/

section SeparablePOU

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ∞}

/-- **A normalized bump**: from a `C^k`-bump function on `V`, a `C^k` function `ψ : V → [0, 1]`
with `ψ = 1` on the ball `B(0, 1)` and support in a ball `B(0, R)`. -/
theorem HasContDiffBump.exists_one_on_ball (hb : HasContDiffBump V k) :
    ∃ (ψ : V → ℝ) (R : ℝ), ContDiff ℝ k ψ ∧ (∀ x, ψ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ball (0 : V) 1, ψ x = 1) ∧ support ψ ⊆ ball (0 : V) R := by
  obtain ⟨b, hbc, hb0, hbb⟩ := hb
  obtain ⟨a, ha⟩ : ∃ a, b a ≠ 0 := by
    by_contra h
    exact hb0 (funext fun x => by_contra fun hx => h ⟨x, hx⟩)
  set c := b a with hcdef
  have hcpos : 0 < |c| := abs_pos.2 ha
  -- `h = 1` near `c`, `h = 0` off `B(c, |c|/2)`; `ψ₀ = h ∘ b`
  let hB : ContDiffBump c := ⟨|c| / 4, |c| / 2, by positivity, by linarith⟩
  set ψ₀ : V → ℝ := fun x => hB (b x) with hψ₀
  have hψ₀c : ContDiff ℝ k ψ₀ := hB.contDiff.comp hbc
  have hbcont : Continuous b := hbc.continuous
  -- `ψ₀ = 1` on a ball around `a`
  obtain ⟨ρ, hρ, hρball⟩ : ∃ ρ > 0, ball a ρ ⊆ {x | |b x - c| < |c| / 4} :=
    Metric.isOpen_iff.1 (isOpen_lt (continuous_abs.comp (hbcont.sub continuous_const))
      continuous_const) a (by simp [hcdef]; positivity)
  -- `supp ψ₀ ⊆ supp b ⊆ B(a, R)`
  obtain ⟨R, hR⟩ := (hbb.subset_ball a)
  have hψ₀supp : support ψ₀ ⊆ ball a R := by
    intro x hx
    by_contra hxR
    have hbx : b x = 0 := by
      by_contra hne; exact hxR (hR hne)
    refine hx ?_
    change hB (b x) = 0
    rw [hbx]
    refine image_eq_zero_of_notMem_tsupport ?_
    rw [hB.tsupport_eq, mem_closedBall, Real.dist_eq, zero_sub, abs_neg]
    change ¬ |c| ≤ |c| / 2
    linarith
  refine ⟨fun x => ψ₀ (a + ρ • x), R / ρ,
    hψ₀c.comp (contDiff_const.add (contDiff_const.smul contDiff_id)),
    fun x => ⟨hB.nonneg, hB.le_one⟩, fun x hx => ?_, fun x hx => ?_⟩
  · have hmem : a + ρ • x ∈ ball a ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hρ]
      have := mem_ball_zero_iff.1 hx
      nlinarith [norm_nonneg x]
    have h1 : |b (a + ρ • x) - c| < |c| / 4 := hρball hmem
    exact hB.one_of_mem_closedBall (by rw [mem_closedBall, Real.dist_eq]; exact h1.le)
  · have h1 := hψ₀supp hx
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hρ] at h1
    rw [mem_ball_zero_iff, lt_div_iff₀ hρ]
    linarith

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The telescoping identity `Σ_{n<N} ψₙ ∏_{j<n}(1 − ψⱼ) = 1 − ∏_{j<N}(1 − ψⱼ)`. -/
lemma sum_range_mul_prod_one_sub (ψ : ℕ → V → ℝ) (N : ℕ) (y : V) :
    ∑ n ∈ Finset.range N, ψ n y * ∏ j ∈ Finset.range n, (1 - ψ j y) =
      1 - ∏ j ∈ Finset.range N, (1 - ψ j y) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.prod_range_succ]
    ring

variable [TopologicalSpace.SeparableSpace V]

set_option maxHeartbeats 800000 in
-- one proof: the countable cover, the locally finite family and the Urysohn function
/-- **`C^k` Urysohn functions on a separable space with a `C^k`-bump function**: for disjoint
closed `s, t ⊆ V` there is a `C^k` function `F : V → [0, 1]` with `F = 0` on `s` and `F = 1` on
`t`. -/
theorem exists_contDiff_urysohn_of_separable (hb : HasContDiffBump V k) {s t : Set V}
    (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ F : V → ℝ, ContDiff ℝ k F ∧ EqOn F 0 s ∧ EqOn F 1 t ∧ ∀ x, F x ∈ Icc (0 : ℝ) 1 := by
  classical
  obtain ⟨ψ, R, hψc, hψ01, hψ1, hψsupp⟩ := hb.exists_one_on_ball
  have hR : 0 < R := by
    have h0 : ψ 0 = 1 := hψ1 0 (mem_ball_self one_pos)
    have h1 := hψsupp (show (0 : V) ∈ support ψ by rw [mem_support, h0]; exact one_ne_zero)
    rwa [mem_ball_zero_iff, norm_zero] at h1
  -- for each `x`, a side (`x ∉ s` or `x ∉ t`) and a radius `r_x` with `B(x, 2 R r_x)` on that side
  have hside : ∀ x : V, ∃ (side : Bool) (r : ℝ), 0 < r ∧
      ball x (2 * R * r) ⊆ (if side then sᶜ else tᶜ) := by
    intro x
    by_cases hx : x ∈ s
    · have hxt : x ∈ tᶜ := fun h' => Set.disjoint_left.1 hst hx h'
      obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.1 ht.isOpen_compl x hxt
      exact ⟨false, ε / (2 * R), by positivity, by
        simp only [Bool.false_eq_true, if_false]
        convert hεt using 2; field_simp⟩
    · obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 hs.isOpen_compl x hx
      exact ⟨true, ε / (2 * R), by positivity, by
        simp only [if_true]
        convert hεs using 2; field_simp⟩
  choose side r hr hrside using hside
  -- a countable subcover of `{B(x, r_x)}`, enumerated
  obtain ⟨T, hTc, hTcov⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x => ball x (r x))
    fun x => isOpen_ball
  have hTcov' : ⋃ x ∈ T, ball x (r x) = univ :=
    hTcov.trans (eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, mem_ball_self (hr x)⟩)
  have hTne : T.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := hTcov'.symm ▸ mem_univ (0 : V)
    simp [h] at this
  obtain ⟨xs, hxs⟩ := hTc.exists_eq_range hTne
  -- `ψₙ = ψ((· − xₙ)/rₙ)`
  set ψn : ℕ → V → ℝ := fun n y => ψ ((r (xs n))⁻¹ • (y - xs n)) with hψndef
  have hψnc : ∀ n, ContDiff ℝ k (ψn n) := fun n =>
    hψc.comp (contDiff_const.smul (contDiff_id.sub contDiff_const))
  have hψn01 : ∀ n y, ψn n y ∈ Icc (0 : ℝ) 1 := fun n y => hψ01 _
  have hψn1 : ∀ n, ∀ y ∈ ball (xs n) (r (xs n)), ψn n y = 1 := by
    intro n y hy
    refine hψ1 _ ?_
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hr _),
      inv_mul_lt_iff₀ (hr _), mul_one, ← dist_eq_norm]
    exact hy
  have hψnsupp : ∀ n y, ψn n y ≠ 0 →
      y ∈ (if side (xs n) then sᶜ else tᶜ) := by
    intro n y hy
    have h1 := hψsupp (mem_support.2 hy)
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hr _),
      inv_mul_lt_iff₀ (hr _), ← dist_eq_norm] at h1
    refine hrside _ (mem_ball.2 (lt_of_lt_of_le h1 ?_))
    have := hr (xs n)
    nlinarith [hR]
  -- every point lies in some `B(xₘ, rₘ)`
  have hcov : ∀ y : V, ∃ m, y ∈ ball (xs m) (r (xs m)) := by
    intro y
    have := hTcov'.symm ▸ mem_univ y
    obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 this
    rw [hxs] at hxT
    obtain ⟨m, rfl⟩ := hxT
    exact ⟨m, hyx⟩
  -- `fₙ = ψₙ ∏_{j<n}(1 − ψⱼ)` and `F = Σ_{side = true} fₙ`
  set fn : ℕ → V → ℝ := fun n y => ψn n y * ∏ j ∈ Finset.range n, (1 - ψn j y) with hfndef
  have hfnc : ∀ n, ContDiff ℝ k (fn n) := fun n =>
    (hψnc n).mul (contDiff_prod fun j _ => contDiff_const.sub (hψnc j))
  have hfn0 : ∀ n y, 0 ≤ fn n y := fun n y =>
    mul_nonneg (hψn01 n y).1 (Finset.prod_nonneg fun j _ => by linarith [(hψn01 j y).2])
  have hfn_zero : ∀ m, ∀ y ∈ ball (xs m) (r (xs m)), ∀ n, m < n → fn n y = 0 := by
    intro m y hy n hn
    simp only [hfndef]
    rw [Finset.prod_eq_zero (Finset.mem_range.2 hn) (by rw [hψn1 m y hy, sub_self]), mul_zero]
  have hfn_sum : ∀ m, ∀ y ∈ ball (xs m) (r (xs m)),
      ∑ n ∈ Finset.range (m + 1), fn n y = 1 := by
    intro m y hy
    rw [sum_range_mul_prod_one_sub,
      Finset.prod_eq_zero (Finset.mem_range.2 (Nat.lt_succ_self m))
        (by rw [hψn1 m y hy, sub_self]), sub_zero]
  set c : ℕ → ℝ := fun n => if side (xs n) then 1 else 0 with hcdef
  set F : V → ℝ := fun y => ∑ᶠ n, fn n y * c n with hFdef
  have hFloc : ∀ m, ∀ y ∈ ball (xs m) (r (xs m)),
      F y = ∑ n ∈ Finset.range (m + 1), fn n y * c n := by
    intro m y hy
    refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
    rw [Finset.coe_range, mem_Iio]
    by_contra hge
    exact hn (show fn n y * c n = 0 by rw [hfn_zero m y hy n (by omega), zero_mul])
  refine ⟨F, contDiff_iff_contDiffAt.2 fun y => ?_, fun y hy => ?_, fun y hy => ?_, fun y => ?_⟩
  · obtain ⟨m, hm⟩ := hcov y
    have hloc : ContDiffAt ℝ k (fun z => ∑ n ∈ Finset.range (m + 1), fn n z * c n) y :=
      (ContDiff.sum fun n _ => (hfnc n).mul contDiff_const).contDiffAt
    refine hloc.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hm] with z hz
    exact hFloc m z hz
  · -- on `s`, the terms with `side = true` vanish
    obtain ⟨m, hm⟩ := hcov y
    rw [hFloc m y hm, Pi.zero_apply]
    refine Finset.sum_eq_zero fun n _ => ?_
    by_cases hside : side (xs n)
    · have : fn n y = 0 := by
        by_contra hne
        have hψ : ψn n y ≠ 0 := fun h0 => hne (by simp only [hfndef, h0, zero_mul])
        have := hψnsupp n y hψ
        rw [if_pos hside] at this
        exact this hy
      rw [this, zero_mul]
    · simp [hcdef, hside]
  · -- on `t`, the terms with `side = false` vanish, and `Σ fₙ = 1`
    obtain ⟨m, hm⟩ := hcov y
    rw [hFloc m y hm, Pi.one_apply, ← hfn_sum m y hm]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hside : side (xs n)
    · simp [hcdef, hside]
    · have : fn n y = 0 := by
        by_contra hne
        have hψ : ψn n y ≠ 0 := fun h0 => hne (by simp only [hfndef, h0, zero_mul])
        have := hψnsupp n y hψ
        rw [if_neg hside] at this
        exact this hy
      rw [this, zero_mul]
  · obtain ⟨m, hm⟩ := hcov y
    rw [hFloc m y hm]
    refine ⟨Finset.sum_nonneg fun n _ => mul_nonneg (hfn0 n y) (by simp only [hcdef]; split_ifs
      <;> norm_num), ?_⟩
    calc ∑ n ∈ Finset.range (m + 1), fn n y * c n ≤ ∑ n ∈ Finset.range (m + 1), fn n y :=
          Finset.sum_le_sum fun n _ => mul_le_of_le_one_right (hfn0 n y)
            (by simp only [hcdef]; split_ifs <;> norm_num)
      _ = 1 := hfn_sum m y hm

/-- **Bonic–Frampton: a separable Banach space with a `C^k`-bump function admits `C^k` partitions
of unity** (the separable case of 2021 Theorem 5.5.16, p. 235).  From the `C^k` Urysohn functions
(`exists_contDiff_urysohn_of_separable`), Mathlib's bump coverings and
`ρᵢ = fᵢ ∏_{j < i}(1 − fⱼ)`. -/
theorem admitsContDiffPartitionsOfUnity_of_separable (hb : HasContDiffBump V k) :
    AdmitsContDiffPartitionsOfUnity V k := by
  classical
  intro ι U hUo hUcov
  obtain ⟨b, hbp, hbsub⟩ := BumpCovering.exists_isSubordinate_of_prop
    (fun g : V → ℝ => ContDiff ℝ k g) (fun s t hs ht hst => by
      obtain ⟨F, hF, hF0, hF1, hF01⟩ := exists_contDiff_urysohn_of_separable hb hs ht hst
      exact ⟨⟨F, hF.continuous⟩, hF, hF0, hF1, hF01⟩)
    isClosed_univ U hUo (by rw [hUcov])
  refine ⟨b.toPartitionOfUnity, hbsub.toPartitionOfUnity, fun i => ?_⟩
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  obtain ⟨T, hT⟩ := b.exists_finset_toPartitionOfUnity_eventuallyEq i x
  refine ContDiffAt.congr_of_eventuallyEq ?_ hT
  have h1 : (⇑(b i) * ⇑(∏ j ∈ T with WellOrderingRel j i, (1 - b j))) =
      fun y => b i y * ∏ j ∈ T with WellOrderingRel j i, (1 - b j y) := by
    funext y
    simp [ContinuousMap.coe_prod, Finset.prod_apply]
  rw [h1]
  exact ((hbp i).mul (contDiff_prod fun j _ => contDiff_const.sub (hbp j))).contDiffAt

/-- **2021 Theorem 5.5.16, p. 235 (preprint 5.43), for separable spaces**: the statement
`GodefroyTroyanskiWhitfieldZizlerStatement V k` holds for every separable `V` (WCG by Proposition
5.5.15 (2)).  The `0`-level of an sc-Banach space is separable (`ScBanach.separableSpace_zero`), so
this is the case the sc-calculus needs. -/
theorem godefroyTroyanskiWhitfieldZizlerStatement_of_separable :
    GodefroyTroyanskiWhitfieldZizlerStatement V k :=
  fun _ hb => admitsContDiffPartitionsOfUnity_of_separable hb

end SeparablePOU

/-! ### Corollary 5.5.17 without hypothesis -/

/-- **2021 Corollary 5.5.17, p. 235 (preprint 5.44)**: if `E₀` is a Hilbert space (`‖v‖² = b(v, v)`
for a continuous bilinear `b`), the local model `(O, C, E)` has the sc-smooth approximation
property.  No hypothesis is needed: `E₀` is separable (`ScBanach.separableSpace_zero`), has a
`C^∞` bump (`hasContDiffBump_of_hilbert`), hence `C^∞` partitions of unity (Theorem 5.5.16 for
separable spaces, `admitsContDiffPartitionsOfUnity_of_separable`), and Proposition 5.5.11
applies. -/
theorem corollary_5_5_17_unconditional (M : LocalModel)
    (hH : ∃ b : M.E 0 →L[ℝ] M.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v) : M.HasApproxProperty := by
  obtain ⟨b, hb⟩ := hH
  have := M.E.separableSpace_zero
  exact proposition_5_5_11 M
    (admitsContDiffPartitionsOfUnity_of_separable (hasContDiffBump_of_hilbert b hb))

section Consequences

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **An M-polyfold built on sc-Hilbert spaces admits sc-smooth partitions of unity** (Corollary
5.5.17 in the charts and Theorem 5.5.10), with no hypothesis on Theorem 5.5.16. -/
theorem MPolyfold.admitsScPartitionsOfUnity_of_hilbert_unconditional
    (h : ∀ x, ∃ φ : MChart X, PX.IsChart φ ∧ x ∈ φ.source ∧
      ∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v) :
    PX.AdmitsScPartitionsOfUnity := by
  refine theorem_5_5_10.2 ⟨{φ | PX.IsChart φ ∧
    ∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v}, fun φ hφ => hφ.1,
    fun x => ?_, fun φ hφ => corollary_5_5_17_unconditional _ hφ.2⟩
  obtain ⟨φ, hφ, hx, hb⟩ := h x
  exact ⟨φ, ⟨hφ, hb⟩, hx⟩

end Consequences

end Polyfold
