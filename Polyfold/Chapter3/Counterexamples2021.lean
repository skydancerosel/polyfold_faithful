import Polyfold.Chapter3.Book2021Items
import Polyfold.Chapter3.GoodPositionSc

/-!
# Corrections as machine-checked counterexamples: Lemma 3.8.6 (2), gap G.46, the set `Σ`

Three places where the project says that a statement of the 2021 text "does not hold as we read
it" had no direct Lean counterexample: Lemma 3.8.6 (2) at `N = 0` (row V3.120), the boundary step
of the proof of Theorem 5.3.12 (gap G.46) and the set `Σ` of the proof of Theorem 3.2.3 (row
V3.24).  This file supplies them.

## Lemma 3.8.6 (2) at `N = 0` (row V3.120)

2021 Lemma 3.8.6 (2), p. 148 (new in the 2021 edition): if `N` is in good position to
`C = [0, ∞)ⁿ ⊕ W`, `N ∩ C` is a closed convex cone and `N ⊆ ℝ^{Γᶜ} ⊕ W`, then
`(N, N ∩ C) ≅ (ℝ, ℝ₊)`.  The project proves it for `N ≠ 0` (`lemma_3_8_6_two_2021`), and
`lemma_3_8_5_not_literal_2021` lists the facts about `N = 0` that refute it.  Here the refutation
is stated directly: `not_lemma_3_8_6_two_2021` is the negation of Lemma 3.8.6 (2) as printed
(every `E`, every presentation, every `N`), witnessed by `N = 0` in `E = ℝ`, `C = [0, ∞)`.

## Good position is not stable under `ℝ × ·` (gap G.46)

The proof of 2021 Theorem 5.3.12, p. 222 (2017: Theorem 5.7; preprint: Theorem 5.19, p. 180),
applies "as before" the argument of Theorem 5.3.10 to the parametrized section
`F(λ, x) = f(x) + Σ λᵢ sᵢ(x)`.  At a zero `(0, x)` with `x ∈ ∂X` where all `sᵢ` vanish,
`ker F'(0, x) = ℝᵐ × ker f'(x)`, and good position of `ker f'(x)` to `C_x` does not give good
position of `ℝᵐ × ker f'(x)` to `ℝᵐ × C_x` (Findings, Chapter 5, item 88).  The smallest
instance, machine-checked here:

* `isInGoodPosition_diag_2021`: the line `ℝ(1, 1)` is in good position to the corner `[0, ∞)²`
  (2021 Definition 3.1.24, p. 102; preprint Definition 3.21), with good complement `ℝ(1, −1)`
  (also with the sc-complement of the definition as written: `isInGoodPositionSc_diag_2021`);
* `not_isInGoodPosition_prod_diag_2021`: `ℝ × ℝ(1, 1)` is **not** in good position to
  `ℝ × [0, ∞)²` in `ℝ × ℝ²`, not even with an algebraic complement.  A good complement `Y` would
  have, for `(a, 0)` with `|a|` large and `y ∈ Y`, `(a, 0) + y ∈ ℝ × [0, ∞)²`; so the second
  components of `Y` lie in `[0, ∞)² ∩ −[0, ∞)² = 0`, `Y ⊆ ℝ × 0 ⊆ ℝ × ℝ(1, 1)`, and
  `(0, (1, 0))` is not in `ℝ × ℝ(1, 1) + Y`.
* `theorem_5_3_12_goodPosition_not_stable_2021` packages both.

So "as before" cannot apply the implicit function theorem for sections in good position (2021
Theorem 3.6.8; preprint 3.54) to `F` at these zeros, and the project's proof of Theorem 5.3.12
(`theorem_5_19`) avoids them (row V5.40).  This certifies gap **G.46**.

## The set `Σ` of the proof of Theorem 3.2.3 (row V3.24)

The proof of 2021 Theorem 3.2.3, p. 107 (2017: Theorem 3.6; preprint: Theorem 3.27, p. 84),
says that for data `(φ, N, Y, V, δ)` of Definition 3.2.1 the set `Σ = {v + y ∈ C | v ∈ V, y ∈ Y}`
is relatively open in `C` and contains `0`.  As we read it, this does not hold (Findings, Chapter
3, item 83): in `ℝ³` with `C = [0, ∞)³`, `N = ℝ(1, 1, 1)` is in good position with the good
sc-complement `Y = {x + y − z = 0}` (`isScGoodComplement_cube_2021`), and for every `V ⊆ N ∩ C`
the points `(a, 0, a + a²) ∈ C`, `a > 0`, are not in `Σ` (on `Σ`, `x + y − z ≥ 0`) and tend to `0`
(`theorem_3_2_3_sigma_not_relOpen_2021`).  The project's Theorem 3.2.3 assumes `π(O) ⊆ C`
(condition (b) of `TangentGermChart.IsRegular`), under which `Σ ∩ O` is relatively open in `O`.

## Helpers

`isCompl_span_pair`, `levelSub_const`, `le_smooth_const`, `isScSplitting_const`: linear algebra in
`ℝ²` and sc-splittings of constant sc-structures (from the round-trip file
`RoundTrip/Items/V3_73.lean`, reused by `Chapter3/RecentreCounterexample2021.lean`).
-/

open Set Function Module

noncomputable section

namespace Polyfold

namespace Counterexamples2021

/-! ### Helpers -/

/-- Two lines `ℝu`, `ℝe` of `ℝ²` with `det(u, e) ≠ 0` are complementary. -/
lemma isCompl_span_pair (u e : Fin 2 → ℝ) (hdet : u 0 * e 1 - u 1 * e 0 ≠ 0) :
    IsCompl (ℝ ∙ u) (ℝ ∙ e) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx'
    have h0 := congrFun hb 0
    have h1 := congrFun hb 1
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
    have : a * (u 0 * e 1 - u 1 * e 0) = 0 := by linear_combination (-e 1) * h0 + e 0 * h1
    rcases mul_eq_zero.1 this with ha | ha
    · rw [ha, zero_smul]
    · exact absurd ha hdet
  · rw [codisjoint_iff, eq_top_iff]
    intro p _
    rw [Submodule.mem_sup]
    refine ⟨((p 0 * e 1 - p 1 * e 0) / (u 0 * e 1 - u 1 * e 0)) • u,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u),
      ((u 0 * p 1 - u 1 * p 0) / (u 0 * e 1 - u 1 * e 0)) • e,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e), ?_⟩
    funext i
    fin_cases i <;>
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdet]
      ring

lemma levelSub_const (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : Submodule ℝ V) (m : ℕ) : (ScBanach.const V).levelSub A m = A := by
  ext x; rw [ScBanach.mem_levelSub, ScBanach.const_toBase]

lemma le_smooth_const (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : Submodule ℝ V) : A ≤ (ScBanach.const V).smooth := by
  intro x _
  exact (ScScale.mem_smooth_iff _).2 fun m => ⟨x, ScBanach.const_toBase V m x⟩

/-- For a constant sc-structure every algebraic splitting is an sc-splitting. -/
lemma isScSplitting_const (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A B : Submodule ℝ V) (h : IsCompl A B) :
    (ScBanach.const V).IsScSplitting A B := by
  refine ⟨(ScBanach.proposition_1_6_iff (ScBanach.const V) A).2 (le_smooth_const V A),
    (ScBanach.proposition_1_6_iff (ScBanach.const V) B).2 (le_smooth_const V B), fun m => ?_⟩
  rw [levelSub_const, levelSub_const]; exact h

/-! ### Lemma 3.8.6 (2) at `N = 0` (row V3.120) -/

/-- **2021 Lemma 3.8.6 (2), p. 148, as printed, does not hold as we read it** (row V3.120): it
fails for `N = 0` in `E = ℝ ⊕ ℝ⁰`, `C = [0, ∞) ⊕ ℝ⁰`, where `N` is in good position, `N ∩ C = 0`
is a closed convex cone and `N ⊆ ℝ^{Γᶜ} ⊕ W` (the kernel of `P : N → ℝ^Γ` is `N`), but `N ≇ ℝ`.
The statement with `N ≠ 0` is `lemma_3_8_6_two_2021`. -/
theorem not_lemma_3_8_6_two_2021 :
    ¬ ∀ (E : ScBanach) (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
      (N : Submodule ℝ (E 0)) [FiniteDimensional ℝ N],
      IsInGoodPosition E (T 0 ⁻¹' quadrant n W 0) N →
      IsClosedConvexCone (quadCone (coordFun (T 0)) N) →
      LinearMap.ker (sigmaCoord (coordFun (T 0)) N) = ⊤ →
      ∃ e : N ≃ₗ[ℝ] ℝ, ∀ x : N, x ∈ quadCone (coordFun (T 0)) N ↔ 0 ≤ e x := by
  intro h
  obtain ⟨h1, h2, h3, -, h5⟩ := lemma_3_8_5_not_literal_2021
  obtain ⟨e, -⟩ := h E₁ 1 (rnSc 0) (ScIso.refl E₁) ⊥ h1 h2 h3
  exact h5.false e

/-! ### Good position is not stable under `ℝ × ·` (gap G.46) -/

/-- `ℝ²` with the constant sc-structure. -/
abbrev E2 : ScBanach := ScBanach.const (Fin 2 → ℝ)

/-- `ℝ × ℝ²` with the constant sc-structure. -/
abbrev E3 : ScBanach := ScBanach.const (ℝ × (Fin 2 → ℝ))

/-- The corner `[0, ∞)² ⊆ ℝ²`. -/
def corner : Set (E2 0) := {x | ∀ i, 0 ≤ x i}

/-- The partial quadrant `ℝ × [0, ∞)² ⊆ ℝ × ℝ²`. -/
def cornerProd : Set (E3 0) := {p | ∀ i, 0 ≤ p.2 i}

/-- The diagonal `ℝ(1, 1) ⊆ ℝ²`. -/
def diag : Submodule ℝ (E2 0) := ℝ ∙ ![1, 1]

/-- The antidiagonal `ℝ(1, −1) ⊆ ℝ²`, the good complement of `ℝ(1, 1)`. -/
def antidiag : Submodule ℝ (E2 0) := ℝ ∙ ![1, -1]

/-- `ℝ × ℝ(1, 1) ⊆ ℝ × ℝ²`. -/
def diagProd : Submodule ℝ (E3 0) := (⊤ : Submodule ℝ ℝ).prod diag

theorem cornerProd_eq : cornerProd = (univ : Set ℝ) ×ˢ corner := by
  ext p; simp [cornerProd, corner]

theorem isCompl_diag_antidiag : IsCompl diag antidiag :=
  isCompl_span_pair _ _ (by norm_num)

/-- `ℝ(1, −1)` is a good complement of `ℝ(1, 1)` for `[0, ∞)²`, with `ε = 1/2`: for `n = t(1, 1)`
and `p = s(1, −1)` with `|s| ≤ |t|/2`, `n + p = (t + s, t − s)` lies in the corner iff `t ≥ 0`. -/
theorem isGoodComplement_diag_antidiag : IsGoodComplement E2 corner diag antidiag := by
  refine ⟨isCompl_diag_antidiag, 1 / 2, by norm_num, fun x hx p hp hle => ?_⟩
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hp
  -- `|s| ≤ ‖p‖ ≤ ‖n‖ / 2 ≤ |t| / 2`
  have hs : |s| ≤ ‖s • (![1, -1] : Fin 2 → ℝ)‖ := by
    have := norm_le_pi_norm (s • (![1, -1] : Fin 2 → ℝ)) 0
    simpa using this
  have ht : ‖t • (![1, 1] : Fin 2 → ℝ)‖ ≤ |t| := by
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg t)).2 fun i => ?_
    fin_cases i <;> simp
  have hst : |s| ≤ |t| / 2 := by
    have := hs.trans (hle.trans (mul_le_mul_of_nonneg_left ht (by norm_num)))
    linarith
  have hs1 := neg_abs_le s
  have hs2 := le_abs_self s
  simp only [corner, mem_ofPred_eq, Fin.forall_fin_two, Pi.add_apply, Pi.smul_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, mul_one, mul_neg]
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at hst
    constructor
    · intro _; constructor <;> linarith
    · intro _; exact ⟨h0, h0⟩
  · rw [abs_of_neg h0] at hst
    constructor
    · intro h; linarith [h.1]
    · intro h; linarith [h.1, h.2]

/-- **`ℝ(1, 1)` is in good position to `[0, ∞)²`** (2021 Definition 3.1.24, p. 102; preprint
Definition 3.21), with good complement `ℝ(1, −1)`. -/
theorem isInGoodPosition_diag_2021 : IsInGoodPosition E2 corner diag := by
  refine ⟨⟨⟨![1, 1], Submodule.mem_span_singleton_self _⟩, ?_⟩,
    antidiag, isGoodComplement_diag_antidiag⟩
  rw [mem_interior]
  refine ⟨{v : diag | ∀ i, 0 < (v : Fin 2 → ℝ) i}, fun v hv i => (hv i).le, ?_, ?_⟩
  · simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)
  · intro i; fin_cases i <;> simp

/-- `ℝ(1, 1)` is in good position to `[0, ∞)²` also with the sc-complement of Definition 3.1.24 as
written (`IsInGoodPositionSc`). -/
theorem isInGoodPositionSc_diag_2021 : IsInGoodPositionSc E2 corner diag :=
  ⟨isInGoodPosition_diag_2021.interior_nonempty, antidiag,
    isScSplitting_const _ _ _ isCompl_diag_antidiag, isGoodComplement_diag_antidiag.exists_eps⟩

/-- **`ℝ × ℝ(1, 1)` is not in good position to `ℝ × [0, ∞)²`** (gap G.46), not even with an
algebraic good complement: the second components of a good complement would lie in
`[0, ∞)² ∩ −[0, ∞)² = 0`. -/
theorem not_isInGoodPosition_prod_diag_2021 : ¬ IsInGoodPosition E3 cornerProd diagProd := by
  rintro ⟨-, Y, hY⟩
  obtain ⟨ε, hε, hgood⟩ := hY.exists_eps
  -- every `y ∈ Y` has nonnegative second components
  have hnn : ∀ y ∈ Y, ∀ i, 0 ≤ (y : E3 0).2 i := by
    intro y hy i
    set a : ℝ := ‖y‖ / ε + 1 with ha
    have ha0 : 0 < a := by positivity
    have hn : ((a, 0) : E3 0) ∈ diagProd := ⟨Submodule.mem_top, Submodule.zero_mem _⟩
    have hnorm : ‖y‖ ≤ ε * ‖((a, 0) : E3 0)‖ := by
      have h1 : ‖((a, 0) : E3 0)‖ = a := by
        rw [Prod.norm_def, norm_zero, Real.norm_of_nonneg ha0.le, max_eq_left ha0.le]
      rw [h1, ha, mul_add, mul_div_cancel₀ _ hε.ne', mul_one]
      linarith
    have hin : ((a, 0) : E3 0) ∈ cornerProd := fun _ => le_rfl
    have := ((hgood _ hn y hy hnorm).1 hin) i
    simpa using this
  -- so the second components vanish
  have hzero : ∀ y ∈ Y, (y : E3 0).2 = 0 := by
    intro y hy
    funext i
    have h1 := hnn y hy i
    have h2 := hnn (-y) (Y.neg_mem hy) i
    simp only [Prod.snd_neg, Pi.neg_apply] at h2
    simp only [Pi.zero_apply]
    linarith
  -- `(0, (1, 0)) = n + y` with `n ∈ ℝ × ℝ(1, 1)`, `y ∈ Y`
  have htop : ((0, ![1, 0]) : E3 0) ∈ diagProd ⊔ Y := by
    rw [hY.isCompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨n, hn, y, hy, hny⟩ := Submodule.mem_sup.1 htop
  have h2 : n.2 = ![1, 0] := by
    have := congrArg Prod.snd hny
    rw [Prod.snd_add, hzero y hy, add_zero] at this
    exact this
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hn.2
  have h0 := congrFun ht 0
  have h1 := congrFun ht 1
  rw [h2] at h0 h1
  have e0 : t = 1 := by simpa using h0
  have e1 : t = 0 := by simpa using h1
  exact one_ne_zero (e0.symm.trans e1)

/-- **Gap G.46, the boundary step of the proof of 2021 Theorem 5.3.12, p. 222 (2017: Theorem 5.7;
preprint: Theorem 5.19)**: good position is not stable under products with `ℝ` (Findings, Chapter
5, item 88).  `ℝ(1, 1)` is in good position to `[0, ∞)²` (with an sc-complement), but
`ℝ × ℝ(1, 1)` is not in good position to `ℝ × [0, ∞)²`, neither with an
sc-complement (Definition 3.1.24 as written) nor with an algebraic one. -/
theorem theorem_5_3_12_goodPosition_not_stable_2021 :
    IsInGoodPositionSc E2 corner diag ∧
      cornerProd = (univ : Set ℝ) ×ˢ corner ∧
      diagProd = (⊤ : Submodule ℝ ℝ).prod diag ∧
      ¬ IsInGoodPosition E3 cornerProd diagProd ∧
      ¬ IsInGoodPositionSc E3 cornerProd diagProd :=
  ⟨isInGoodPositionSc_diag_2021, cornerProd_eq, rfl, not_isInGoodPosition_prod_diag_2021,
    fun h => not_isInGoodPosition_prod_diag_2021 h.toIsInGoodPosition⟩

/-! ### The set `Σ` of the proof of Theorem 3.2.3 (row V3.24) -/

/-- `ℝ³` with the constant sc-structure. -/
abbrev Ecube : ScBanach := ScBanach.const (Fin 3 → ℝ)

/-- The corner `[0, ∞)³ ⊆ ℝ³`. -/
def cube : Set (Ecube 0) := {x | ∀ i, 0 ≤ x i}

/-- The line `N = ℝ(1, 1, 1)`. -/
def diagCube : Submodule ℝ (Ecube 0) := ℝ ∙ ![1, 1, 1]

/-- The functional `ℓ(x, y, z) = x + y − z`. -/
def ellCube : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0 +
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1 -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2

theorem ellCube_apply (x : Fin 3 → ℝ) : ellCube x = x 0 + x 1 - x 2 := rfl

/-- The plane `Y = {x + y − z = 0}`. -/
def planeCube : Submodule ℝ (Ecube 0) := LinearMap.ker ellCube

/-- The set `Σ = {v + y ∈ C | v ∈ V, y ∈ Y}` of the proof of Theorem 3.2.3. -/
def sigmaCube (V : Set (Ecube 0)) : Set (Ecube 0) :=
  {z | z ∈ cube ∧ ∃ v ∈ V, ∃ y ∈ planeCube, z = v + y}

theorem isCompl_diagCube_planeCube : IsCompl diagCube planeCube := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have h := LinearMap.mem_ker.1 hy
    rw [ellCube_apply] at h
    have h' : t * 1 + t * 1 - t * 1 = 0 := h
    have ht : t = 0 := by linarith
    rw [ht, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro z _
    rw [Submodule.mem_sup]
    refine ⟨ellCube z • ![1, 1, 1], Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
      z - ellCube z • ![1, 1, 1], ?_, by abel⟩
    rw [planeCube, LinearMap.mem_ker, map_sub, map_smul, ellCube_apply ![1, 1, 1]]
    simp

/-- **`Y = {x + y − z = 0}` is a good sc-complement of `N = ℝ(1, 1, 1)` for `[0, ∞)³`**
(Definition 3.1.24 as written, `ε = 1/2`), and `N ∩ C` has interior in `N`. -/
theorem isScGoodComplement_cube_2021 :
    IsScGoodComplement Ecube cube diagCube planeCube ∧
      (interior (Subtype.val ⁻¹' cube : Set diagCube)).Nonempty := by
  refine ⟨⟨isScSplitting_const _ _ _ isCompl_diagCube_planeCube, 1 / 2, by norm_num,
    fun x hx p _ hle => ?_⟩, ⟨⟨![1, 1, 1], Submodule.mem_span_singleton_self _⟩, ?_⟩⟩
  · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have ht : ‖t • (![1, 1, 1] : Fin 3 → ℝ)‖ ≤ |t| := by
      refine (pi_norm_le_iff_of_nonneg (abs_nonneg t)).2 fun i => ?_
      fin_cases i <;> simp
    have hp : ∀ i, |p i| ≤ |t| / 2 := fun i => by
      have h1 := norm_le_pi_norm p i
      rw [Real.norm_eq_abs] at h1
      have := h1.trans (hle.trans (mul_le_mul_of_nonneg_left ht (by norm_num)))
      linarith
    have hval : ∀ i, (t • (![1, 1, 1] : Fin 3 → ℝ)) i = t := fun i => by
      fin_cases i <;> simp
    simp only [cube, mem_ofPred_eq, Pi.add_apply, hval]
    rcases le_or_gt 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at hp
      refine ⟨fun _ i => ?_, fun _ _ => h0⟩
      have := neg_abs_le (p i)
      linarith [hp i]
    · rw [abs_of_neg h0] at hp
      refine ⟨fun h => absurd (h 0) (not_le.2 h0), fun h => ?_⟩
      have := le_abs_self (p 0)
      linarith [hp 0, h 0]
  · rw [mem_interior]
    refine ⟨{v : diagCube | ∀ i, 0 < (v : Fin 3 → ℝ) i}, fun v hv i => (hv i).le, ?_, ?_⟩
    · simp only [ofPred_forall]
      exact isOpen_iInter_of_finite fun i =>
        isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)
    · intro i; fin_cases i <;> simp

/-- **The set `Σ` of the proof of 2021 Theorem 3.2.3, p. 107 (preprint Theorem 3.27, p. 84), is in
general not relatively open in `C`, as we read it** (row V3.24; Findings, Chapter 3, item 83): in
`ℝ³` with `C = [0, ∞)³`, `N = ℝ(1, 1, 1)` and its good complement `Y = {x + y − z = 0}`, for no
`V ⊆ N ∩ C` is `Σ = {v + y ∈ C | v ∈ V, y ∈ Y}` relatively open in `C` with `0 ∈ Σ`. -/
theorem theorem_3_2_3_sigma_not_relOpen_2021 (V : Set (Ecube 0))
    (hV : V ⊆ (diagCube : Set (Ecube 0)) ∩ cube) :
    ¬ ((∃ O : Set (Ecube 0), IsOpen O ∧ sigmaCube V = O ∩ cube) ∧ (0 : Ecube 0) ∈ sigmaCube V) := by
  rintro ⟨⟨O, hO, hSig⟩, h0⟩
  have h0O : (0 : Ecube 0) ∈ O := by rw [hSig] at h0; exact h0.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO 0 h0O
  -- the point `z = (a, 0, a + a²)` with `a = min (r/4) (1/2)`
  set a : ℝ := min (r / 4) (1 / 2) with ha
  have ha0 : 0 < a := lt_min (by positivity) (by norm_num)
  have ha1 : a ≤ 1 / 2 := min_le_right _ _
  have har : a ≤ r / 4 := min_le_left _ _
  set z : Ecube 0 := ![a, 0, a + a ^ 2] with hz
  have hzC : z ∈ cube := by
    intro i
    fin_cases i
    · change 0 ≤ a; exact ha0.le
    · change (0 : ℝ) ≤ 0; exact le_rfl
    · change 0 ≤ a + a ^ 2; positivity
  have hzO : z ∈ O := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    have hle : ‖z‖ ≤ a + a ^ 2 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      have h2 : 0 < a + a ^ 2 := by positivity
      fin_cases i <;> simp [hz, abs_of_pos ha0, abs_of_pos h2] <;> nlinarith
    nlinarith
  have hzSig : z ∈ sigmaCube V := by rw [hSig]; exact ⟨hzO, hzC⟩
  obtain ⟨-, v, hv, y, hy, hzvy⟩ := hzSig
  obtain ⟨hvN, hvC⟩ := hV hv
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hvN
  have ht : 0 ≤ t := by simpa using hvC 0
  have hyl : ellCube y = 0 := LinearMap.mem_ker.1 hy
  have hl := congrArg ellCube hzvy
  rw [map_add, hyl, add_zero, map_smul, ellCube_apply, ellCube_apply] at hl
  simp [hz] at hl
  nlinarith

end Counterexamples2021

end Polyfold
