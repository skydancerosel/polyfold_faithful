import Polyfold.Chapter3.ExtremeRays
import Polyfold.Chapter3.GoodPositionSc

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.8.1.4:
**Lemmas 3.8.9–3.8.11** (preprint 3.66–3.68), pp. 150–152: the complement `Ñ` of `N ∩ W` in `N`.

# The complement `Ñ` of `N ∩ W`

## The text, paraphrased

`E = ℝⁿ ⊕ W`, `C = [0, ∞)ⁿ ⊕ W`, `N ⊆ E` finite-dimensional in good position to `C` with
sc-complement `N^⊥` and constant `c`; `W` is identified with `{0} ⊕ W`, and `Ñ` is an algebraic
complement of `N ∩ W` in `N`.  `Σ` is the union of the `σ_a = {i | a_i = 0}` over the nonzero
`a ∈ C ∩ N`, and `ℝ^{Σᶜ} ⊕ W` the subspace where the coordinates in `Σ` vanish.
(Lemma 3.8.9) `Ñ` is in good position to `C`, with good complement `(N ∩ W) ⊕ N^⊥`.
(Lemma 3.8.10) `C ∩ Ñ` is a closed convex cone in `Ñ`, and a generator `a` of an extreme ray has
`dim Ñ − 1 = #σ_a = d_C(a)`.
(Lemma 3.8.11) Either `Ñ ∩ (ℝ^{Σᶜ} ⊕ W) = {0}`, or `Ñ ⊆ ℝ^{Σᶜ} ⊕ W`, `dim Ñ = 1` and `Σ = ∅`.

## What is formalized

* `Polyfold.wPart` (`{0} ⊕ W`), `Polyfold.bigSigma` (`Σ`, (3.36)), `Polyfold.sigmaCompl`
  (`ℝ^{Σᶜ} ⊕ W`).
* `Polyfold.lemma_3_8_9`: **Lemma 3.8.9** for a good sc-complement `N^⊥`
  (`IsScGoodComplement`, the text's definition); the proof uses only that `N^⊥` is closed
  (`Polyfold.lemma_3_8_9_of_isClosed`), through the continuous projection onto `N` along `N^⊥`
  (the text's constant `c₁`).  The conclusion is the project's `IsGoodComplement` (algebraic
  splitting) and `IsInGoodPosition`; that `(N ∩ W) ⊕ N^⊥` is again an sc-subspace, and Lemma 3.8.9
  with the text's notions on both sides, is `lemma_3_8_9_sc` (`GoodComplementIntersectionSc.lean`).
* `Polyfold.lemma_3_8_10`: **Lemma 3.8.10**; the cone property does not need good position
  (`Polyfold.isClosedConvexCone_of_disjoint`), the dimension formula is Lemma 3.8.3 for `Ñ`.
* `Polyfold.lemma_3_8_11`: **Lemma 3.8.11**, by the text's argument: every generator of an extreme
  ray of `C ∩ Ñ` spans the line of a nonzero `x ∈ Ñ ∩ (ℝ^{Σᶜ} ⊕ W)`, so by Lemma 3.8.1
  (`lemma_3_8_1_zero_union`) `C ∩ Ñ ⊆ ℝx`, and the interior gives `Ñ = ℝx`.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

variable {n : ℕ} {W : ScBanach}

/-- `{0} ⊕ W` inside `ℝⁿ ⊕ W`. -/
def wPart (n : ℕ) (W : ScBanach) : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0) :=
  LinearMap.ker (LinearMap.fst ℝ (Fin n → ℝ) (W 0))

lemma mem_wPart {x : ((ScBanach.const (Fin n → ℝ)).prod W) 0} : x ∈ wPart n W ↔ x.1 = 0 :=
  Iff.rfl

lemma add_mem_quadrant_iff_of_mem_wPart {x w : ((ScBanach.const (Fin n → ℝ)).prod W) 0}
    (hw : w ∈ wPart n W) : x + w ∈ quadrant n W 0 ↔ x ∈ quadrant n W 0 := by
  have h : (x + w).1 = x.1 := by rw [Prod.fst_add, mem_wPart.1 hw, add_zero]
  change (∀ i, 0 ≤ (x + w).1 i) ↔ ∀ i, 0 ≤ x.1 i
  rw [h]

/-- The index set `Σ` of (3.36): the `i` with `a_i = 0` for some nonzero `a ∈ C ∩ N`. -/
def bigSigma (N : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)) : Set (Fin n) :=
  {i | ∃ a ∈ N, a ∈ quadrant n W 0 ∧ a ≠ 0 ∧ a.1 i = 0}

/-- The subspace `ℝ^{Σᶜ} ⊕ W` of `ℝⁿ ⊕ W`: the coordinates in `Σ` vanish. -/
def sigmaCompl (N : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)) :
    Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0) where
  carrier := {x | ∀ i ∈ bigSigma N, x.1 i = 0}
  add_mem' hx hy i hi := by simp [hx i hi, hy i hi]
  zero_mem' _ _ := rfl
  smul_mem' c x hx i hi := by simp [hx i hi]

/-! ### Lemma 3.8.9 -/

/-- **Lemma 3.8.9 (preprint 3.66)**, 2021 p. 150, for a closed good complement: if `N` is in good
position with closed good complement `N^⊥` and `Ñ` is an algebraic complement of `N ∩ W` in `N`,
then `(N ∩ W) ⊕ N^⊥` is a good complement of `Ñ` and `Ñ` is in good position. -/
theorem lemma_3_8_9_of_isClosed {N P Ñ : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)}
    [FiniteDimensional ℝ N]
    (hint : (interior (Subtype.val ⁻¹' quadrant n W 0 : Set N)).Nonempty)
    (hP : IsGoodComplement _ (quadrant n W 0) N P)
    (hPc : IsClosed (P : Set (((ScBanach.const (Fin n → ℝ)).prod W) 0)))
    (hÑ : Ñ ≤ N) (hdisj : Disjoint Ñ (N ⊓ wPart n W)) (hsup : Ñ ⊔ (N ⊓ wPart n W) = N) :
    IsGoodComplement _ (quadrant n W 0) Ñ ((N ⊓ wPart n W) ⊔ P) ∧
      IsInGoodPosition _ (quadrant n W 0) Ñ := by
  have hgc : IsGoodComplement _ (quadrant n W 0) Ñ ((N ⊓ wPart n W) ⊔ P) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx'
      have hbN : b ∈ N := by
        have := N.sub_mem (hÑ hx) (Submodule.mem_inf.1 ha).1
        rwa [add_sub_cancel_left] at this
      have hb0 : b = 0 := (Submodule.disjoint_def.1 hP.isCompl.disjoint) b hbN hb
      subst hb0
      rw [add_zero] at hx ⊢
      exact (Submodule.disjoint_def.1 hdisj) a hx ha
    · rw [codisjoint_iff, ← sup_assoc, hsup, hP.isCompl.sup_eq_top]
    · obtain ⟨ε, hε, hgood⟩ := hP.exists_eps
      have hNc : IsClosed (N : Set (((ScBanach.const (Fin n → ℝ)).prod W) 0)) :=
        Submodule.closed_of_finiteDimensional N
      obtain ⟨pr, hpr⟩ : ∃ pr : _ →L[ℝ] N, ∀ y, pr y = N.projectionOnto P hP.isCompl y :=
        ⟨N.projectionOntoL P (Submodule.IsCompl.isTopCompl_of_isClosed hP.isCompl hNc hPc), fun y =>
          congrFun (Submodule.coe_projectionOntoL _) y⟩
      refine ⟨ε / (1 + ‖pr‖), by positivity, fun x hx p hp hle => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hp
      have haN := (Submodule.mem_inf.1 ha).1
      have h1 : pr a = ⟨a, haN⟩ := by
        rw [hpr]; exact Submodule.projectionOnto_apply_of_mem_left _ haN
      have h2 : pr b = 0 := by
        rw [hpr]; exact Submodule.projectionOnto_apply_right hP.isCompl ⟨b, hb⟩
      have hna : ‖a‖ ≤ ‖pr‖ * ‖a + b‖ := by
        have : pr (a + b) = ⟨a, haN⟩ := by rw [map_add, h1, h2, add_zero]
        calc ‖a‖ = ‖pr (a + b)‖ := by rw [this]; rfl
          _ ≤ ‖pr‖ * ‖a + b‖ := pr.le_opNorm _
      have e1 : ‖b‖ ≤ ‖a + b‖ + ‖a‖ := by
        calc ‖b‖ = ‖(a + b) - a‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖a + b‖ + ‖a‖ := norm_sub_le _ _
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_add, mul_one] at hle
      have hnb : ‖b‖ ≤ ε * ‖x‖ := by nlinarith [mul_comm ‖pr‖ ‖a + b‖]
      rw [show x + (a + b) = (x + b) + a by abel,
        add_mem_quadrant_iff_of_mem_wPart (Submodule.mem_inf.1 ha).2]
      exact hgood x (hÑ hx) b hb hnb
  refine ⟨hgc, ⟨?_, ⟨_, hgc⟩⟩⟩
  obtain ⟨x₀, hx₀⟩ := hint
  have hx₀N : (x₀ : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈ Ñ ⊔ (N ⊓ wPart n W) := by
    rw [hsup]; exact x₀.2
  obtain ⟨y₀, hy₀, w, hw, hyw⟩ := Submodule.mem_sup.1 hx₀N
  let f : Ñ → N := fun y => ⟨y + w, N.add_mem (hÑ y.2) (Submodule.mem_inf.1 hw).1⟩
  have hf : Continuous f := (continuous_subtype_val.add continuous_const).subtype_mk _
  have hfy : f ⟨y₀, hy₀⟩ = x₀ := Subtype.ext hyw
  refine ⟨⟨y₀, hy₀⟩, interior_maximal ?_
    ((isOpen_interior (s := (Subtype.val ⁻¹' quadrant n W 0 : Set N))).preimage hf) ?_⟩
  · intro y hy
    have h1 : f y ∈ (Subtype.val ⁻¹' quadrant n W 0 : Set N) := interior_subset hy
    exact (add_mem_quadrant_iff_of_mem_wPart (Submodule.mem_inf.1 hw).2).1 h1
  · rw [mem_preimage, hfy]; exact hx₀

/-- **Lemma 3.8.9 (preprint 3.66)**, 2021 p. 150: if `N` is in good position to
`C = [0, ∞)ⁿ ⊕ W` with good sc-complement `N^⊥` and `Ñ` is an algebraic complement of `N ∩ W` in
`N`, then `Ñ` is in good position to `C` with good complement `(N ∩ W) ⊕ N^⊥`. -/
theorem lemma_3_8_9 {N P Ñ : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)}
    [FiniteDimensional ℝ N] (hN : IsInGoodPositionSc _ (quadrant n W 0) N)
    (hP : IsScGoodComplement _ (quadrant n W 0) N P)
    (hÑ : Ñ ≤ N) (hdisj : Disjoint Ñ (N ⊓ wPart n W)) (hsup : Ñ ⊔ (N ⊓ wPart n W) = N) :
    IsInGoodPosition _ (quadrant n W 0) Ñ ∧
      IsGoodComplement _ (quadrant n W 0) Ñ ((N ⊓ wPart n W) ⊔ P) :=
  (lemma_3_8_9_of_isClosed hN.interior_nonempty hP.toIsGoodComplement hP.isClosed hÑ hdisj
    hsup).symm

/-! ### Lemma 3.8.10 -/

/-- `C ∩ Ñ` is a closed convex cone in `Ñ` whenever `Ñ ⊆ N` meets `N ∩ W` only in `0`. -/
theorem isClosedConvexCone_of_disjoint
    {N Ñ : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)} (hÑ : Ñ ≤ N)
    (hdisj : Disjoint Ñ (N ⊓ wPart n W)) :
    IsClosedConvexCone (Subtype.val ⁻¹' quadrant n W 0 : Set Ñ) where
  isClosed := (quadrant_isClosed n W 0).preimage continuous_subtype_val
  convex := by
    have := (quadrant_convex n W 0).linear_preimage Ñ.subtype
    exact this
  inter_neg := by
    ext x
    simp only [mem_inter_iff, Set.mem_neg, mem_singleton_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      have h0 : ∀ i, (x : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i = 0 :=
        fun i => le_antisymm (by simpa using h2 i) (h1 i)
      exact Subtype.ext ((Submodule.disjoint_def.1 hdisj) _ x.2
        (Submodule.mem_inf.2 ⟨hÑ x.2, mem_wPart.2 (by exact funext h0)⟩))
    · rintro rfl
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> simp
  smul_mem t ht x hx := fun i => mul_nonneg ht (hx i)

/-- **Lemma 3.8.10 (preprint 3.67)**, 2021 p. 151: under the hypotheses of Lemma 3.8.9, `C ∩ Ñ`
is a closed convex cone in `Ñ`, and a generator `a` of an extreme ray of `C ∩ Ñ` has
`dim Ñ − 1 = #σ_a = d_C(a)`. -/
theorem lemma_3_8_10 {N P Ñ : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)}
    [FiniteDimensional ℝ N] (hN : IsInGoodPositionSc _ (quadrant n W 0) N)
    (hP : IsScGoodComplement _ (quadrant n W 0) N P)
    (hÑ : Ñ ≤ N) (hdisj : Disjoint Ñ (N ⊓ wPart n W)) (hsup : Ñ ⊔ (N ⊓ wPart n W) = N) :
    IsClosedConvexCone (Subtype.val ⁻¹' quadrant n W 0 : Set Ñ) ∧
      ∀ a : Ñ, IsExtremeRayGen (Subtype.val ⁻¹' quadrant n W 0 : Set Ñ) a →
        finrank ℝ Ñ - 1 = quadrantDeg (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∧
          quadrantDeg (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) =
            degIndex _ (quadrant n W 0) (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) := by
  have : FiniteDimensional ℝ Ñ := Submodule.finiteDimensional_of_le hÑ
  have hK := isClosedConvexCone_of_disjoint hÑ hdisj
  exact ⟨hK, fun a ha => ⟨lemma_3_8_3_goodPosition hK ha
    (lemma_3_8_9 hN hP hÑ hdisj hsup).1, (degIndex_quadrant ha.1).symm⟩⟩

/-! ### Lemma 3.8.11 -/

/-- For `a ∈ C ∩ N ∖ {0}` and `x ∈ ℝ^{Σᶜ} ⊕ W`, `λ a + x ∈ C` for `λ = Σ |x_i| / a_i + 1`. -/
lemma large_smul_add_mem {N : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)}
    {a x : ((ScBanach.const (Fin n → ℝ)).prod W) 0} (haN : a ∈ N) (haC : a ∈ quadrant n W 0)
    (ha0 : a ≠ 0) (hx : x ∈ sigmaCompl N) :
    (∑ i, |x.1 i| / a.1 i + 1) • a + x ∈ quadrant n W 0 := by
  refine fun i => ?_
  have hsum : 0 ≤ ∑ j, |x.1 j| / a.1 j :=
    Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (haC j)
  simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i ∈ bigSigma N
  · rw [hx i hi, add_zero]; exact mul_nonneg (by linarith) (haC i)
  · have hai : a.1 i ≠ 0 := fun h => hi ⟨a, haN, haC, ha0, h⟩
    have hapos := lt_of_le_of_ne (haC i) (Ne.symm hai)
    have h1 := Finset.single_le_sum (f := fun j => |x.1 j| / a.1 j)
      (fun j _ => div_nonneg (abs_nonneg _) (haC j)) (Finset.mem_univ i)
    have h2 : |x.1 i| / a.1 i ≤ ∑ j, |x.1 j| / a.1 j + 1 := by simp only at h1; linarith
    rw [div_le_iff₀ hapos] at h2
    have := neg_abs_le (x.1 i)
    linarith

/-- Step of the proof of Lemma 3.8.11: a generator `b` of an extreme ray of `C ∩ Ñ` spans every
`x ∈ Ñ ∩ (ℝ^{Σᶜ} ⊕ W)`. -/
lemma exists_eq_smul_of_isExtremeRayGen
    {N Ñ : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)} (hÑ : Ñ ≤ N)
    (hK : IsClosedConvexCone (Subtype.val ⁻¹' quadrant n W 0 : Set Ñ)) {b : Ñ}
    (hb : IsExtremeRayGen (Subtype.val ⁻¹' quadrant n W 0 : Set Ñ) b) {x : Ñ}
    (hx : (x : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈ sigmaCompl N) :
    ∃ r : ℝ, x = r • b := by
  obtain ⟨hbK, hb0, hext⟩ := hb
  have hb0' : (b : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ≠ 0 := fun h => hb0 (Subtype.ext h)
  set l := ∑ i, |(x : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i| /
    (b : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i + 1 with hl
  have hlpos : 0 < l := by
    have : 0 ≤ ∑ i, |(x : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i| /
        (b : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i :=
      Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (hbK j)
    linarith
  have hy : l • b + x ∈ (Subtype.val ⁻¹' quadrant n W 0 : Set Ñ) :=
    large_smul_add_mem (hÑ b.2) hbK hb0' hx
  have hy' : (2 * l) • b - (l • b + x) ∈ (Subtype.val ⁻¹' quadrant n W 0 : Set Ñ) := by
    have he : (2 * l) • b - (l • b + x) = l • b + -x := by rw [two_mul, add_smul]; abel
    rw [he]
    have h := large_smul_add_mem (hÑ b.2) hbK hb0' (neg_mem hx)
    simp only [Prod.fst_neg, Pi.neg_apply, abs_neg] at h
    exact h
  obtain ⟨t, -, ht⟩ := hK.mem_rayOf_of_smul_sub_mem hext (by positivity) hy hy'
  exact ⟨t - l, by rw [show (t - l) • b = t • b - l • b from sub_smul t l b, ← ht]; abel⟩

/-- **Lemma 3.8.11 (preprint 3.68)**, 2021 p. 151: under the hypotheses of Lemma 3.8.9, either
`Ñ ∩ (ℝ^{Σᶜ} ⊕ W) = {0}`, or `Ñ ⊆ ℝ^{Σᶜ} ⊕ W`, `dim Ñ = 1` and `Σ = ∅`. -/
theorem lemma_3_8_11 {N P Ñ : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)}
    [FiniteDimensional ℝ N] (hN : IsInGoodPositionSc _ (quadrant n W 0) N)
    (hP : IsScGoodComplement _ (quadrant n W 0) N P)
    (hÑ : Ñ ≤ N) (hdisj : Disjoint Ñ (N ⊓ wPart n W)) (hsup : Ñ ⊔ (N ⊓ wPart n W) = N) :
    Ñ ⊓ sigmaCompl N = ⊥ ∨ (Ñ ≤ sigmaCompl N ∧ finrank ℝ Ñ = 1 ∧ bigSigma N = ∅) := by
  have : FiniteDimensional ℝ Ñ := Submodule.finiteDimensional_of_le hÑ
  by_cases h : Ñ ⊓ sigmaCompl N = ⊥
  · exact Or.inl h
  right
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨hxÑ, hxS⟩ := Submodule.mem_inf.1 hx
  set x' : Ñ := ⟨x, hxÑ⟩
  have hx'0 : x' ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hK := isClosedConvexCone_of_disjoint hÑ hdisj
  have hgp := (lemma_3_8_9 hN hP hÑ hdisj hsup).1
  -- every generator of an extreme ray lies on the line `ℝ x`
  have hgen : ∀ b : Ñ, IsExtremeRayGen (Subtype.val ⁻¹' quadrant n W 0 : Set Ñ) b →
      b ∈ Submodule.span ℝ {x'} := by
    intro b hb
    obtain ⟨r, hr⟩ := exists_eq_smul_of_isExtremeRayGen hÑ hK hb (x := x') hxS
    have hr0 : r ≠ 0 := by rintro rfl; exact hx'0 (by simpa using hr)
    rw [Submodule.mem_span_singleton]
    exact ⟨r⁻¹, by rw [hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]⟩
  -- hence `C ∩ Ñ ⊆ ℝ x` (Lemma 3.8.1)
  have hKspan : (Subtype.val ⁻¹' quadrant n W 0 : Set Ñ) ⊆ Submodule.span ℝ {x'} := by
    rw [lemma_3_8_1_zero_union hK]
    refine closure_minimal (convexHull_min (union_subset ?_ ?_) (Submodule.convex _))
      (Submodule.closed_of_finiteDimensional _)
    · rw [singleton_subset_iff]; exact Submodule.zero_mem _
    · rintro y ⟨R, ⟨b, hbK, hb0, rfl, hext⟩, hy⟩
      obtain ⟨t, -, rfl⟩ := hy
      exact Submodule.smul_mem _ t (hgen b ⟨hbK, hb0, hext⟩)
  have htop : Submodule.span ℝ {x'} = ⊤ := Submodule.eq_top_of_nonempty_interior' _
    (hgp.interior_nonempty.mono (interior_mono hKspan))
  have hdim : finrank ℝ Ñ = 1 := by
    have := finrank_span_singleton (K := ℝ) hx'0
    rwa [htop, finrank_top] at this
  have hle : Ñ ≤ sigmaCompl N := by
    intro y hy
    have hmem : (⟨y, hy⟩ : Ñ) ∈ Submodule.span ℝ {x'} := htop ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
    have hyr : y = r • x := (congrArg Subtype.val hr).symm
    rw [hyr]; exact Submodule.smul_mem _ r hxS
  refine ⟨hle, hdim, ?_⟩
  -- an extreme ray exists, since `C ∩ Ñ` has interior in `Ñ ≠ 0`
  obtain ⟨R, hR⟩ : (extremeRays (Subtype.val ⁻¹' quadrant n W 0 : Set Ñ)).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hempty
    have hK0 : (Subtype.val ⁻¹' quadrant n W 0 : Set Ñ) ⊆ {0} := by
      rw [lemma_3_8_1_zero_union hK, hempty, sUnion_empty, union_empty, convexHull_singleton,
        closure_singleton]
    have : Nontrivial Ñ := ⟨⟨x', 0, hx'0⟩⟩
    have := hgp.interior_nonempty.mono (interior_mono hK0)
    rw [interior_singleton] at this
    exact not_nonempty_empty this
  obtain ⟨b, hbK, hb0, rfl, hext⟩ := hR
  have hdeg := ((lemma_3_8_10 hN hP hÑ hdisj hsup).2 b ⟨hbK, hb0, hext⟩).1
  rw [hdim] at hdeg
  ext i
  simp only [mem_empty_iff_false, iff_false]
  intro hi
  have hbi : (b : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i = 0 := hle b.2 i hi
  have hcard : Fintype.card {j // (b : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 j = 0} = 0 := by
    rw [card_zeroIdx]; omega
  exact (Fintype.card_eq_zero_iff.1 hcard).false ⟨i, hbi⟩

end Polyfold
