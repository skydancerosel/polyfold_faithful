import Polyfold.Chapter13.P3M_ScPlusSectionOn

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.2, **Definitions 13.2.2–13.2.4** (pp. 608–609; 2017: Definitions 13.2–13.4).

# Supports, pointwise norms and triviality of sc⁺-multisections

## The text, paraphrased

(Definition 13.2.2) For an sc⁺-multisection `Λ : W → ℚ⁺`, the domain support is the closure of
the set of `x` over which some `w ≠ 0` has `Λ(w) > 0`, and the support is `{w | Λ(w) > 0}`.  For
every `x` the set `supp(Λ)(x)` is finite, `∑_{w ∈ supp(Λ)(x)} Λ(w) = 1`, and for `x ∈ U(x₀)` with
a local section structure, `supp(Λ)(x) = {s₁(x), …, s_k(x)}`.
(Definition 13.2.3) For an auxiliary norm `N`, `N(Λ)(x) = max{N(w) | w ∈ supp(Λ)(x)}`; then
`dom-supp(Λ) = cl(P(supp(Λ) ∩ (W ∖ 0_W))) = cl({x | N(Λ)(x) > 0})`.
(Definition 13.2.4) `Λ` is trivial on `V` if `Λ(0_x) = 1` for `x ∈ V` (hence `Λ(w) = 0` for
`w ≠ 0_x`); the domain support is the smallest closed set outside of which `Λ` is trivial.

## What is formalized (namespace `Polyfold.SBLocalization`)

* Definition 13.2.2: `supp`, `suppAt`, `domSupp`; `IsLocalRepOn.suppAt_eq` (the support over
  `x ∈ U(x₀)` is `{sᵢ(x)}`), `IsScPlusMultisection.finite_suppAt`,
  `IsScPlusMultisection.sum_suppAt` / `finsum_suppAt` (the weights over a point sum to `1`),
  `domSupp_eq_closure_image` (the first relation after Definition 13.2.3).
* Definition 13.2.3: `normW` (the auxiliary norm read on `W`, `0` off `W_{0,1}`),
  `pointwiseNorm`; `IsScPlusMultisection.suppAt_subset_oneSet`,
  `IsScPlusMultisection.isGreatest_pointwiseNorm` (the maximum is attained),
  `domSupp_eq_closure_pointwiseNorm` (the second relation, for any auxiliary norm).
* Definition 13.2.4: `IsTrivialOn`; `IsScPlusMultisection.isTrivialOn_iff` (the text's "hence"),
  `IsScPlusMultisection.isLeast_domSupp` (the domain support is the least closed set outside of
  which `Λ` is trivial); witness `isTrivialOn_zeroMultisection`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle

variable {A : SEP.{u}}

/-! ### Local representations over a point -/

/-- A local representation on `O` read in the fibre over `x ∈ O`. -/
theorem IsLocalRepOn.apply_of_proj {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ) {x : A.Obj}
    (hx : x ∈ O) {w : A.W} (hw : A.P w = x) :
    Λ w = ∑ i, if w = s i x then σ i else 0 := by
  classical
  have := h.2.2.2 w (by rw [hw]; exact hx)
  rw [hw] at this
  convert this

/-- Every sc⁺-multisection has a local representation on an open neighbourhood of each point. -/
theorem IsScPlusMultisection.exists_isLocalRepOn {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (x : A.Obj) :
    ∃ (O : Set A.Obj) (k : ℕ) (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0),
      IsOpen O ∧ x ∈ O ∧ IsLocalRepOn A Λ O s σ := by
  obtain ⟨R, k, s, σ, h⟩ := hΛ.2 x
  exact ⟨R.U, k, s, σ, R.isOpen_U, R.mem_U, h⟩

/-! ### Definition 13.2.2 -/

/-- **2021 Definition 13.2.2 (2), p. 608 (2017: Definition 13.2)**: the support
`supp(Λ) = {w ∈ W | Λ(w) > 0}`. -/
def supp (Λ : A.W → ℚ≥0) : Set A.W := {w | 0 < Λ w}

/-- `supp(Λ)(x) = {w ∈ W | P(w) = x, Λ(w) > 0}` (p. 608). -/
def suppAt (Λ : A.W → ℚ≥0) (x : A.Obj) : Set A.W := {w | A.P w = x ∧ 0 < Λ w}

/-- **2021 Definition 13.2.2 (1), p. 608**: the domain support
`dom-supp(Λ) = cl_X({x ∈ X | ∃ w ∈ W_x ∖ {0}, Λ(w) > 0})`. -/
def domSupp (Λ : A.W → ℚ≥0) : Set A.Obj :=
  closure {x | ∃ w, A.P w = x ∧ w ≠ fiberZero A.P x ∧ 0 < Λ w}

/-- **p. 608**: over a point `x ∈ U(x₀)` of a local section structure,
`supp(Λ)(x) = {s₁(x), …, s_k(x)}`. -/
theorem IsLocalRepOn.suppAt_eq {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ) {x : A.Obj}
    (hx : x ∈ O) : suppAt Λ x = range fun i => s i x := by
  classical
  ext w
  constructor
  · rintro ⟨hw, hpos⟩
    rw [h.apply_of_proj hx hw] at hpos
    by_contra hne
    refine hpos.ne' (Finset.sum_eq_zero fun i _ => if_neg fun (e : w = s i x) => hne ⟨i, e.symm⟩)
  · rintro ⟨i, rfl⟩
    have hP : A.P (s i x) = x := (h.2.1 i).1 x hx
    refine ⟨hP, ?_⟩
    rw [h.apply_of_proj hx hP]
    refine lt_of_lt_of_le (h.1 i) ?_
    have := Finset.single_le_sum (f := fun j => if s i x = s j x then σ j else 0)
      (fun j _ => zero_le) (Finset.mem_univ i)
    simpa using this

/-- **p. 608**: `supp(Λ)(x)` is finite. -/
theorem IsScPlusMultisection.finite_suppAt {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (x : A.Obj) : (suppAt Λ x).Finite := by
  obtain ⟨O, k, s, σ, -, hx, h⟩ := hΛ.exists_isLocalRepOn x
  rw [h.suppAt_eq hx]; exact finite_range _

/-- The weights of a local representation over `x ∈ O` sum to `1` (a `Finset` form). -/
theorem IsLocalRepOn.sum_image_eq_one {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ) {x : A.Obj}
    (hx : x ∈ O) :
    ∑ w ∈ Finset.univ.image (fun i => s i x), Λ w = 1 := by
  classical
  have e1 : ∀ w ∈ Finset.univ.image (fun i => s i x),
      Λ w = ∑ i, if w = s i x then σ i else 0 := fun w hw => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
    exact h.apply_of_proj hx ((h.2.1 i).1 x hx)
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  have e2 : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      (∑ w ∈ Finset.univ.image (fun i => s i x), if w = s i x then σ i else 0) = σ i :=
    fun i _ => by
      rw [Finset.sum_ite_eq']
      exact if_pos (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  rw [Finset.sum_congr rfl e2]
  exact h.2.2.1

/-- **p. 608**: `∑_{w ∈ supp(Λ)(x)} Λ(w) = 1`. -/
theorem IsScPlusMultisection.sum_suppAt {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (x : A.Obj) : ∑ w ∈ (hΛ.finite_suppAt x).toFinset, Λ w = 1 := by
  classical
  obtain ⟨O, k, s, σ, -, hx, h⟩ := hΛ.exists_isLocalRepOn x
  have : (hΛ.finite_suppAt x).toFinset = Finset.univ.image (fun i => s i x) := by
    ext w
    rw [Finite.mem_toFinset, h.suppAt_eq hx, Finset.mem_image]
    simp
  rw [this]
  exact h.sum_image_eq_one hx

/-- **p. 608**, as a `finsum`: `∑_{w ∈ supp(Λ)(x)} Λ(w) = 1`. -/
theorem IsScPlusMultisection.finsum_suppAt {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (x : A.Obj) : ∑ᶠ w ∈ suppAt Λ x, Λ w = 1 := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (hΛ.finite_suppAt x)]
  exact hΛ.sum_suppAt x

theorem IsScPlusMultisection.suppAt_nonempty {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (x : A.Obj) : (suppAt Λ x).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have := hΛ.finsum_suppAt x
  rw [hne, finsum_mem_empty] at this
  exact zero_ne_one this

/-- **The first relation after Definition 13.2.3, p. 608**:
`dom-supp(Λ) = cl_X(P(supp(Λ) ∩ (W ∖ 0_W)))`. -/
theorem domSupp_eq_closure_image (Λ : A.W → ℚ≥0) :
    domSupp Λ = closure (A.P '' (supp Λ ∩ {w | w ≠ fiberZero A.P (A.P w)})) := by
  unfold domSupp
  congr 1
  ext x
  constructor
  · rintro ⟨w, rfl, hw0, hpos⟩
    exact ⟨w, ⟨hpos, hw0⟩, rfl⟩
  · rintro ⟨w, ⟨hpos, hw0⟩, rfl⟩
    exact ⟨w, rfl, hw0, hpos⟩

/-! ### Definition 13.2.3 -/

open scoped Classical in
/-- An auxiliary norm `N : W_{0,1} → ℝ` read on `W` (with the value `0` off `W_{0,1}`). -/
def normW (N : A.B.One → ℝ) (w : A.W) : ℝ :=
  if h : w ∈ A.B.oneSet then N (A.B.oneMk w h) else 0

theorem normW_of_mem (N : A.B.One → ℝ) {w : A.W} (h : w ∈ A.B.oneSet) :
    normW N w = N (A.B.oneMk w h) := by
  unfold normW; rw [dif_pos h]

/-- **2021 Definition 13.2.3, p. 608 (2017: Definition 13.3)**: the pointwise norm
`N(Λ)(x) = max{N(w) | w ∈ supp(Λ)(x)}` (as a supremum; it is attained,
`IsScPlusMultisection.isGreatest_pointwiseNorm`). -/
def pointwiseNorm (N : A.B.One → ℝ) (Λ : A.W → ℚ≥0) (x : A.Obj) : ℝ :=
  sSup (normW N '' suppAt Λ x)

/-- The points of `supp(Λ)(x)` lie in `W_{0,1}` (they are values of sc⁺-sections), so `N` is
defined on them. -/
theorem IsScPlusMultisection.suppAt_subset_oneSet {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (x : A.Obj) : suppAt Λ x ⊆ A.B.oneSet := by
  obtain ⟨O, k, s, σ, -, hx, h⟩ := hΛ.exists_isLocalRepOn x
  rw [h.suppAt_eq hx]
  rintro _ ⟨i, rfl⟩
  exact (h.2.1 i).mem_oneSet hx

/-- **Definition 13.2.3**: the maximum is attained (`supp(Λ)(x)` is finite and nonempty). -/
theorem IsScPlusMultisection.isGreatest_pointwiseNorm {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (N : A.B.One → ℝ) (x : A.Obj) :
    IsGreatest (normW N '' suppAt Λ x) (pointwiseNorm N Λ x) := by
  have hfin := (hΛ.finite_suppAt x).image (normW N)
  have hne := (hΛ.suppAt_nonempty x).image (normW N)
  exact ⟨hne.csSup_mem hfin, fun r hr => le_csSup hfin.bddAbove hr⟩

theorem normW_nonneg {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) (w : A.W) : 0 ≤ normW N w := by
  unfold normW
  split_ifs with h
  · exact hN.nonneg _
  · exact le_rfl

/-- For an auxiliary norm, `N(w) = 0` exactly at the zero of the fibre (on `W_{0,1}`). -/
theorem normW_eq_zero_iff {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) {w : A.W}
    (h : w ∈ A.B.oneSet) : normW N w = 0 ↔ w = fiberZero A.P (A.P w) := by
  rw [normW_of_mem N h]
  set v : A.B.oneFiber (A.P w) := ⟨⟨w, rfl⟩, h⟩ with hv
  have hvt : A.B.toOne v = A.B.oneMk w h := rfl
  constructor
  · intro h0
    have := (hN.fiber (A.P w)).eq_zero v (by rw [hvt]; exact h0)
    have e := congrArg (fun u : A.B.oneFiber (A.P w) => ((u : A.P ⁻¹' {A.P w}) : A.W)) this
    exact e
  · intro e
    have hz : A.B.oneMk w h = A.B.zeroOne (A.P w) := A.B.oneVal_injective e
    rw [hz]
    exact (hN.fiber (A.P w)).map_zero

/-- **The second relation after Definition 13.2.3, p. 608**:
`dom-supp(Λ) = cl_X({x ∈ X | N(Λ)(x) > 0})`, for every auxiliary norm `N`. -/
theorem IsScPlusMultisection.domSupp_eq_closure_pointwiseNorm {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) :
    domSupp Λ = closure {x | 0 < pointwiseNorm N Λ x} := by
  unfold domSupp
  congr 1
  ext x
  constructor
  · rintro ⟨w, hw, hw0, hpos⟩
    have hws : w ∈ suppAt Λ x := ⟨hw, hpos⟩
    have hw1 := hΛ.suppAt_subset_oneSet x hws
    have hN0 : normW N w ≠ 0 := fun e => hw0 (by
      have := (normW_eq_zero_iff hN hw1).1 e; rw [hw] at this; exact this)
    exact lt_of_lt_of_le (lt_of_le_of_ne (normW_nonneg hN w) (Ne.symm hN0))
      ((hΛ.isGreatest_pointwiseNorm N x).2 (mem_image_of_mem _ hws))
  · intro hpos
    obtain ⟨w, hws, hwN⟩ := (hΛ.isGreatest_pointwiseNorm N x).1
    refine ⟨w, hws.1, fun e => ?_, hws.2⟩
    have hw1 := hΛ.suppAt_subset_oneSet x hws
    have : normW N w = 0 := (normW_eq_zero_iff hN hw1).2 (by rw [hws.1]; exact e)
    rw [hwN] at this
    exact (lt_irrefl _ (this ▸ hpos : (0 : ℝ) < 0))

/-! ### Definition 13.2.4 -/

/-- **2021 Definition 13.2.4, p. 609 (2017: Definition 13.4)**: `Λ` is trivial on `V` if
`Λ(0_x) = 1` for all `x ∈ V`. -/
def IsTrivialOn (Λ : A.W → ℚ≥0) (V : Set A.Obj) : Prop :=
  ∀ x ∈ V, Λ (fiberZero A.P x) = 1

/-- Over one point: `Λ(0_x) = 1` if and only if `Λ` vanishes on `W_x ∖ {0_x}` (the weights over
`x` sum to `1`). -/
theorem IsScPlusMultisection.apply_fiberZero_eq_one_iff {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (x : A.Obj) :
    Λ (fiberZero A.P x) = 1 ↔ ∀ w, A.P w = x → w ≠ fiberZero A.P x → Λ w = 0 := by
  classical
  have hsum := hΛ.sum_suppAt x
  set T := (hΛ.finite_suppAt x).toFinset with hT
  constructor
  · intro h1 w hw hw0
    by_contra hne
    have hwT : w ∈ T := (Finite.mem_toFinset _).2 ⟨hw, pos_iff_ne_zero.2 hne⟩
    have h0T : fiberZero A.P x ∈ T :=
      (Finite.mem_toFinset _).2 ⟨proj_fiberZero A.P x, by rw [h1]; exact one_pos⟩
    have hsub : ({fiberZero A.P x, w} : Finset A.W) ⊆ T := by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact h0T
      · rw [Finset.mem_singleton.1 hu]; exact hwT
    have hle := Finset.sum_le_sum_of_subset (f := Λ) hsub
    rw [Finset.sum_pair (Ne.symm hw0), h1, hsum] at hle
    exact absurd hle (not_le.2 (lt_add_of_pos_right 1 (pos_iff_ne_zero.2 hne)))
  · intro h
    have hsubT : T ⊆ {fiberZero A.P x} := fun w hw => by
      rw [Finite.mem_toFinset] at hw
      by_contra hne
      exact (hw.2.ne' (h w hw.1 (by simpa using hne)))
    rcases Finset.subset_singleton_iff.1 hsubT with he | he
    · rw [he, Finset.sum_empty] at hsum; exact absurd hsum zero_ne_one
    · rw [he, Finset.sum_singleton] at hsum; exact hsum

/-- **Definition 13.2.4, "and hence"**: `Λ` is trivial on `V` if and only if `Λ(w) = 0` for all
`w ≠ 0` over `V`. -/
theorem IsScPlusMultisection.isTrivialOn_iff {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (V : Set A.Obj) :
    IsTrivialOn Λ V ↔ ∀ w, A.P w ∈ V → w ≠ fiberZero A.P (A.P w) → Λ w = 0 := by
  constructor
  · intro h w hw hw0
    exact (hΛ.apply_fiberZero_eq_one_iff _).1 (h _ hw) w rfl hw0
  · intro h x hx
    exact (hΛ.apply_fiberZero_eq_one_iff x).2 fun w hw hw0 => h w (hw ▸ hx) (hw ▸ hw0)

/-- **p. 609**: "the domain support of `Λ` is the smallest closed set in `X` outside of which `Λ`
is trivial". -/
theorem IsScPlusMultisection.isLeast_domSupp {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) :
    IsLeast {F : Set A.Obj | IsClosed F ∧ IsTrivialOn Λ Fᶜ} (domSupp Λ) := by
  refine ⟨⟨isClosed_closure, (hΛ.isTrivialOn_iff _).2 fun w hw hw0 => ?_⟩, ?_⟩
  · by_contra hne
    exact hw (subset_closure ⟨w, rfl, hw0, pos_iff_ne_zero.2 hne⟩)
  · rintro F ⟨hF, htriv⟩
    refine closure_minimal ?_ hF
    rintro x ⟨w, rfl, hw0, hpos⟩
    by_contra hx
    exact hpos.ne' ((hΛ.isTrivialOn_iff _).1 htriv w hx hw0)

/-- Definition 13.2.4 is satisfiable: the multisection of the zero section is trivial on `X`. -/
theorem isTrivialOn_zeroMultisection (A : SEP.{u}) : IsTrivialOn (zeroMultisection A) univ :=
  fun x _ => by simp [zeroMultisection, proj_fiberZero]

end SBLocalization

end Polyfold
