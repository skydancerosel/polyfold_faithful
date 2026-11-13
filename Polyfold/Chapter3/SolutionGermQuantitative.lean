import Polyfold.Chapter3.GermIFT

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.3: **Remark 3.3.8**
(preprint 3.36), p. 113: Corollary 3.3.7 in quantitative form.

# The quantitative solution germ

## The text, paraphrased

For an sc⁰-contraction germ `f(a, w) = w − B(a, w)` which is an sc-smooth germ with `f(0) = 0`
there are decreasing sequences `(ε_i)`, `(τ_i)` such that (1) `δ` is a continuous solution of
`f(a, δ(a)) = 0` on `{a ∈ C̃ | |a|₀ ≤ ε₀}` with values in `{|w|₀ ≤ τ₀}`, `δ(0) = 0`; (2) a solution
`f(a, w) = 0` with `|a|₀ ≤ ε₀`, `|w|₀ ≤ τ₀` has `w = δ(a)`; (3) `|a|₀ ≤ ε_i` implies `δ(a) ∈ W_i`
and `|δ(a)|_i ≤ τ_i`; (4) `δ : {|a|₀ ≤ ε_i} → W_i` is of class `C^i`.

## What is formalized

`Polyfold.remark_3_3_8`: the four statements, for the text's sc⁰-contraction germ
(`IsSc0ContractionGerm`, Definition 3.3.1) which is an sc-smooth germ (`IsScSmoothGerm`), on any
quadrant-like `C̃` of a finite-dimensional `P` (the text: `[0, ∞)ᵏ ⊕ ℝⁿ⁻ᵏ`), with `ε_i, τ_i > 0`
antitone and `δ` the solution germ of Theorem 3.3.2 (`ContractionGerm.sol`).  The sets are the
closed balls `{a ∈ C̃ | ‖a‖ ≤ ε_i}`; "`δ(a) ∈ W_i`" is `δ(a) ∈ range (W_i → W₀)`, and the level-`i`
map is `levelMap δ i`.  Proof: Theorem 3.3.2 (existence, uniqueness in the contraction region,
continuity of the level-`i` fixed points), Corollary 3.3.7 with `m = k = i`, and a choice of radii
made monotone by taking running minima.
-/

open Set Filter Topology Function Metric

noncomputable section

namespace Polyfold

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {Ct : Set P} {W : ScBanach}

namespace ContractionGerm

variable (𝒞 : ContractionGerm P Ct W)

lemma fixLvl_zero_eq (hC : IsQuadrantLike (ScBanach.const P) Ct) (i : ℕ) :
    𝒞.fixLvl i 0 = 0 := by
  have h0 : (0 : P) ∈ 𝒞.N i ∩ Ct := ⟨𝒞.N_zero i, hC.zero_mem⟩
  apply W.toBase_injective i
  rw [𝒞.toBase_fixLvl i h0, map_zero, 𝒞.sol_zero]

/-- The radius at level `i`: for `a ∈ C̃` with `‖a‖ ≤ e`, `a` lies in `N i` and in a given
relatively open neighbourhood `V` of `0`, and `|δ_i(a)|_i ≤ τ`. -/
lemma exists_radius (hC : IsQuadrantLike (ScBanach.const P) Ct) (i : ℕ) {V : Set P}
    (hV : ∃ O : Set P, IsOpen O ∧ V = O ∩ Ct) (h0V : (0 : P) ∈ V) {τ : ℝ} (hτ : 0 < τ) :
    ∃ e > 0, ∀ a ∈ Ct, ‖a‖ ≤ e → a ∈ 𝒞.N i ∧ a ∈ V ∧ ‖𝒞.fixLvl i a‖ ≤ τ := by
  obtain ⟨O, hO, rfl⟩ := hV
  have hc := 𝒞.continuousOn_fixLvl i 0 ⟨𝒞.N_zero i, hC.zero_mem⟩
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨d₁, hd₁, hd₁'⟩ := hc τ hτ
  obtain ⟨d₂, hd₂, hd₂'⟩ := Metric.isOpen_iff.1 (𝒞.N_open i) 0 (𝒞.N_zero i)
  obtain ⟨d₃, hd₃, hd₃'⟩ := Metric.isOpen_iff.1 hO 0 h0V.1
  set e := min d₁ (min d₂ d₃) / 2 with he
  have hepos : 0 < e := by positivity
  have hlt : ∀ a : P, ‖a‖ ≤ e → ‖a‖ < min d₁ (min d₂ d₃) := fun a ha =>
    ha.trans_lt (by rw [he]; linarith [lt_min hd₁ (lt_min hd₂ hd₃)])
  refine ⟨e, hepos, fun a ha hae => ?_⟩
  have hb := hlt a hae
  have hN : a ∈ 𝒞.N i := hd₂' (mem_ball_zero_iff.2 (hb.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))))
  refine ⟨hN, ⟨hd₃' (mem_ball_zero_iff.2 (hb.trans_le
    ((min_le_right _ _).trans (min_le_right _ _)))), ha⟩, ?_⟩
  have := hd₁' ⟨hN, ha⟩ (by rw [dist_zero_right]; exact hb.trans_le (min_le_left _ _))
  rw [dist_eq_norm, 𝒞.fixLvl_zero_eq hC, sub_zero] at this
  exact this.le

end ContractionGerm

/-- Running minima of a positive sequence: positive, antitone, and below the sequence. -/
lemma exists_antitone_le {e : ℕ → ℝ} (he : ∀ i, 0 < e i) :
    ∃ ε : ℕ → ℝ, Antitone ε ∧ (∀ i, 0 < ε i) ∧ ∀ i, ε i ≤ e i := by
  let ε : ℕ → ℝ := fun i => Nat.rec (e 0) (fun j r => min r (e (j + 1))) i
  have hs : ∀ j, ε (j + 1) = min (ε j) (e (j + 1)) := fun j => rfl
  refine ⟨ε, antitone_nat_of_succ_le fun j => by rw [hs]; exact min_le_left _ _, fun i => ?_,
    fun i => ?_⟩
  · induction i with
    | zero => exact he 0
    | succ j ih => rw [hs]; exact lt_min ih (he _)
  · cases i with
    | zero => exact le_rfl
    | succ j => rw [hs]; exact min_le_right _ _

/-- **Remark 3.3.8 (preprint 3.36)**, 2021 p. 113, Corollary 3.3.7 in quantitative terms: let
`f(a, w) = w − B(a, w)` be an sc⁰-contraction germ (Definition 3.3.1) on the quadrant-like
`C̃ ⊆ P` which is an sc-smooth germ (`f(0) = 0` is part of the definition).  Then there are a
map `δ` and antitone positive sequences `(ε_i)`, `(τ_i)` with
1. `δ(0) = 0`, and on `{a ∈ C̃ | ‖a‖ ≤ ε₀}` `δ` is continuous, `|δ(a)|₀ ≤ τ₀` and `f(a, δ(a)) = 0`;
2. if `a ∈ C̃`, `‖a‖ ≤ ε₀`, `|w|₀ ≤ τ₀` and `f(a, w) = 0`, then `w = δ(a)`;
3. if `a ∈ C̃`, `‖a‖ ≤ ε_i`, then `δ(a) ∈ W_i` and `|δ(a)|_i ≤ τ_i`;
4. `δ : {a ∈ C̃ | ‖a‖ ≤ ε_i} → W_i` is of class `C^i`. -/
theorem remark_3_3_8 (hC : IsQuadrantLike (ScBanach.const P) Ct)
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
    (h : IsSc0ContractionGerm Ct G B) (hB : IsScSmoothGerm G B) :
    ∃ (δ : P → W 0) (ε τ : ℕ → ℝ), Antitone ε ∧ Antitone τ ∧ (∀ i, 0 < ε i) ∧ (∀ i, 0 < τ i) ∧
      (δ 0 = 0 ∧ ContinuousOn δ {a ∈ Ct | ‖a‖ ≤ ε 0} ∧
        ∀ a ∈ Ct, ‖a‖ ≤ ε 0 → ‖δ a‖ ≤ τ 0 ∧ contractionMap B (a, δ a) = 0) ∧
      (∀ a ∈ Ct, ‖a‖ ≤ ε 0 → ∀ w : W 0, ‖w‖ ≤ τ 0 → contractionMap B (a, w) = 0 → w = δ a) ∧
      (∀ i, ∀ a ∈ Ct, ‖a‖ ≤ ε i →
        δ a ∈ range (W.toBase i) ∧ ‖levelMap (E := ScBanach.const P) (F := W) δ i a‖ ≤ τ i) ∧
      (∀ i : ℕ, ContDiffOn ℝ i (levelMap (E := ScBanach.const P) (F := W) δ i)
        {a ∈ Ct | ‖a‖ ≤ ε i}) := by
  set 𝒞 := h.toContractionGerm
  -- `τ_i = τ₀ / 2^i` with the closed `τ₀`-ball inside the contraction region `O 0`
  obtain ⟨τ₀', hτ₀', hτ₀O⟩ := Metric.isOpen_iff.1 (𝒞.O_open 0) 0 (𝒞.zero_mem_O 0)
  set τ : ℕ → ℝ := fun i => τ₀' / 2 / 2 ^ i with hτdef
  have hτpos : ∀ i, 0 < τ i := fun i => by positivity
  have hτanti : Antitone τ := fun i j hij => by
    simp only [hτdef]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ (by norm_num) hij)
  -- Corollary 3.3.7 with `m = k = i`, and the radii
  have hcor := fun i : ℕ => corollary_3_3_7 𝒞 hC hB i i
  choose V hVrel h0V hVrange hVcd using hcor
  have hrad := fun i : ℕ => 𝒞.exists_radius hC i (hVrel i) (h0V i) (hτpos i)
  choose e he hspec using hrad
  obtain ⟨ε, hεanti, hεpos, hεle⟩ := exists_antitone_le he
  have hmem : ∀ i, ∀ a ∈ Ct, ‖a‖ ≤ ε i → a ∈ 𝒞.N i ∧ a ∈ V i ∧ ‖𝒞.fixLvl i a‖ ≤ τ i :=
    fun i a ha hae => hspec i a ha (hae.trans (hεle i))
  have hO : ∀ w : W 0, ‖w‖ ≤ τ 0 → w ∈ 𝒞.O 0 := fun w hw => hτ₀O (mem_ball_zero_iff.2
    (hw.trans_lt (by simp only [hτdef, pow_zero, div_one]; linarith)))
  have hsolfix : ∀ a ∈ Ct, ‖a‖ ≤ ε 0 → contractionMap B (a, 𝒞.sol a) = 0 := fun a ha hae => by
    change 𝒞.sol a - B (a, 𝒞.sol a) = 0
    rw [sub_eq_zero]; exact (𝒞.sol_fixed ⟨(hmem 0 a ha hae).1, ha⟩).symm
  refine ⟨𝒞.sol, ε, τ, hεanti, hτanti, hεpos, hτpos, ⟨𝒞.sol_zero, ?_, fun a ha hae =>
    ⟨(hmem 0 a ha hae).2.2, hsolfix a ha hae⟩⟩, ?_, ?_, ?_⟩
  · exact (𝒞.continuousOn_fixLvl 0).mono fun a ha => ⟨(hmem 0 a ha.1 ha.2).1, ha.1⟩
  · intro a ha hae w hw hf
    have hf' : w - B (a, w) = 0 := hf
    exact 𝒞.eq_sol ⟨(hmem 0 a ha hae).1, ha⟩ (hO w hw) (sub_eq_zero.1 hf').symm
  · intro i a ha hae
    obtain ⟨hN, hV, hb⟩ := hmem i a ha hae
    refine ⟨hVrange i a hV, ?_⟩
    rw [𝒞.levelMap_sol i ⟨hN, ha⟩]; exact hb
  · intro i
    exact (hVcd i).mono fun a ha => (hmem i a ha.1 ha.2).2.1

end Polyfold
