import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_58

/-! Round trip for V4_58 (Theorem 3.78 in the `C^∞` form used in §4.3).

`A` is the conjunction of the types of `Polyfold.ContractionData.exists_solution_smooth`,
`Polyfold.theorem_3_8_22_smooth`, `Polyfold.ContractionData.exists_radii`,
`Polyfold.Radii.contDiffOn_τ` and `Polyfold.theorem_3_8_22` (none has universe parameters: all
spaces live in `Type`).

`A → B`: B states Theorem 3.78 for every smoothness class `j ∈ ℕ ∪ {∞}`, `j ≥ 1`, in the blind
coordinates (`ℝⁿ = Fin n → ℝ`, `C = quadC n k`, `f` into `Fin N → ℝ`).  For `j = ∞` this is an
instance of `theorem_3_8_22_smooth`, for finite `j` of `theorem_3_8_22` (the glue of V3_63:
`quadC n k` is a partial quadrant via `ℝⁿ ≅ ℝᵏ × ℝⁿ⁻ᵏ`, `fderivWithin f U 0 = L` by unique
differentiability of `U`, B's good complement is the project's, `τ` is composed with `Y ↪ ℝⁿ`).
The clause `f (k + τ k) = 0` of `A` is dropped.

`B → A` is not proved: as in V3_63, B (following the literal text) never asserts that the graph of
`τ` consists of zeros of `f`, so A's existence clause (`f (k + τ k) = 0`, resp.
`B (k, τ k) = τ k`) would have to be re-proved by the contraction argument; moreover
`exists_radii` and `Radii.contDiffOn_τ` are lemmas of the proof (the radii of Lemmas 3.79–3.80, the
regularity of the fixed point map `S.τ` of a given `Radii` structure) that B does not mention. -/

open Set

noncomputable section

namespace RoundTrip.V4_58
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ContractionData.exists_solution_smooth) ∧
  (type_of% @Polyfold.theorem_3_8_22_smooth) ∧
  (type_of% @Polyfold.ContractionData.exists_radii) ∧
  (type_of% @Polyfold.Radii.contDiffOn_τ) ∧
  (type_of% @Polyfold.theorem_3_8_22)

theorem A_holds : A :=
  ⟨@Polyfold.ContractionData.exists_solution_smooth, @Polyfold.theorem_3_8_22_smooth,
    @Polyfold.ContractionData.exists_radii, @Polyfold.Radii.contDiffOn_τ, @Polyfold.theorem_3_8_22⟩

/-! ### Glue (from V3_63): `quadC n k` is a partial quadrant -/

/-- The index equivalence `Fin k ⊕ Fin (n − k) ≃ Fin n`. -/
def splitIdx (n k : ℕ) (hk : k ≤ n) : Fin k ⊕ Fin (n - k) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hk))

lemma splitIdx_inl_val (n k : ℕ) (hk : k ≤ n) (i : Fin k) :
    ((splitIdx n k hk (Sum.inl i) : Fin n) : ℕ) = i := by
  simp [splitIdx]

/-- The linear equivalence `ℝⁿ ≅ ℝᵏ × ℝⁿ⁻ᵏ` (the first `k` coordinates, the rest). -/
def splitEquiv (n k : ℕ) (hk : k ≤ n) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin k → ℝ) × (Fin (n - k) → ℝ) :=
  (LinearEquiv.funCongrLeft ℝ ℝ (splitIdx n k hk)).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin (n - k)) ℝ ℝ)

lemma splitEquiv_fst (n k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin k) :
    (splitEquiv n k hk x).1 i = x (splitIdx n k hk (Sum.inl i)) := rfl

lemma mem_quadC_iff (n k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) :
    x ∈ quadC n k ↔ ∀ i : Fin k, 0 ≤ (splitEquiv n k hk x).1 i := by
  constructor
  · intro hx i
    rw [splitEquiv_fst]
    apply hx
    rw [splitIdx_inl_val]
    exact i.2
  · intro hx i hi
    have := hx ⟨i, hi⟩
    rw [splitEquiv_fst] at this
    have heq : splitIdx n k hk (Sum.inl ⟨i, hi⟩) = i := Fin.ext (splitIdx_inl_val n k hk _)
    rwa [heq] at this

theorem isPartialQuadrant_quadC (n k : ℕ) (hk : k ≤ n) :
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) (quadC n k) := by
  refine ⟨k, ScBanach.const (Fin (n - k) → ℝ), scIsoOfLinearEquiv (splitEquiv n k hk), ?_⟩
  ext x
  rw [mem_quadC_iff n k hk]
  change _ ↔ ∀ i, 0 ≤ ((scIsoOfLinearEquiv (splitEquiv n k hk)).lvl 0 x).1 i
  rw [scIsoOfLinearEquiv_apply]

/-! ### `A → B` -/

/-- The common glue: from the conclusion of `theorem_3_8_22` (or `theorem_3_8_22_smooth`) at the
smoothness exponent `J`, the conclusion of B. -/
theorem conclusion_of {n k N : ℕ} {J : WithTop ℕ∞} {U : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → (Fin N → ℝ)} {L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)}
    {Y : Submodule ℝ (Fin n → ℝ)} (hJ : J ≠ 0)
    (h : ∃ (V' : Set (kerCLM L)) (τ : kerCLM L → Y) (ε σ : ℝ),
      (∃ O : Set (kerCLM L), IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' quadC n k) ∧
      (0 : kerCLM L) ∈ V' ∧
      ContDiffOn ℝ J τ V' ∧ τ 0 = 0 ∧ fderivWithin ℝ τ V' 0 = 0 ∧
      (∀ v ∈ V', (v : Fin n → ℝ) + τ v ∈ U ∧ f ((v : Fin n → ℝ) + τ v) = 0) ∧
      0 < ε ∧ 0 < σ ∧ (∀ v ∈ V', ‖v‖ ≤ ε → ‖τ v‖ ≤ σ) ∧
      (∀ v ∈ V', ‖v‖ ≤ ε → ∀ y ∈ Y, ‖y‖ ≤ σ → (v : Fin n → ℝ) + y ∈ U →
        f ((v : Fin n → ℝ) + y) = 0 → y = τ v)) :
    ∃ (V : Set (kerCLM L)) (τ : kerCLM L → (Fin n → ℝ)) (ε σ : ℝ),
      (∃ O : Set (kerCLM L), IsOpen O ∧ V = O ∩ (Subtype.val ⁻¹' quadC n k)) ∧ 0 ∈ V ∧
      (∀ v ∈ V, τ v ∈ Y) ∧ ContDiffOn ℝ J τ V ∧ 0 < ε ∧ 0 < σ ∧
      (τ 0 = 0 ∧ HasFDerivWithinAt τ (0 : kerCLM L →L[ℝ] (Fin n → ℝ)) V 0 ∧
        ∀ v ∈ V, (v : Fin n → ℝ) + τ v ∈ U) ∧
      (∀ v ∈ V, ‖v‖ ≤ ε → ‖τ v‖ ≤ σ) ∧
      (∀ v ∈ V, ∀ y ∈ Y, ‖v‖ ≤ ε → ‖y‖ ≤ σ → (v : Fin n → ℝ) + y ∈ U →
        f ((v : Fin n → ℝ) + y) = 0 → y = τ v) := by
  obtain ⟨V', τ, ε, σ, hV'rel, h0V', hτcd, hτ0, hDτ0, hsol, hε, hσ, hbound, huniq⟩ := h
  refine ⟨V', fun v => (τ v : Fin n → ℝ), ε, σ, hV'rel, h0V', fun v _ => (τ v).2, ?_, hε, hσ,
    ⟨?_, ?_, fun v hv => (hsol v hv).1⟩, ?_, ?_⟩
  · exact Y.subtypeL.contDiff.comp_contDiffOn hτcd
  · simp [hτ0]
  · have hd : DifferentiableWithinAt ℝ τ V' 0 := hτcd.differentiableOn hJ 0 h0V'
    have h1 := hd.hasFDerivWithinAt
    rw [hDτ0] at h1
    have h2 := Y.subtypeL.hasFDerivAt.comp_hasFDerivWithinAt (0 : kerCLM L) h1
    simpa using h2
  · intro v hv hvε
    exact hbound v hv hvε
  · intro v hv y hy hvε hyσ hyU hfy
    exact huniq v hv hvε y hy hyσ hyU hfy

theorem A_to_B : A → B := by
  rintro ⟨-, h378s, -, -, h378⟩ n k N j U f L Y hkn hj hUrel h0 hf hf0 hL hsurj hint hgood
  have hC : IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) (quadC n k) :=
    isPartialQuadrant_quadC n k hkn
  have hU : IsRelOpenInQuadrant (ScBanach.const (Fin n → ℝ)) (quadC n k) U := ⟨hC, hUrel⟩
  have hUD : UniqueDiffWithinAt ℝ U 0 := hU.isScDomain.uniqueDiffWithinAt 0 0 h0
  have hLeq : fderivWithin ℝ f U 0 = L := hL.fderivWithin hUD
  obtain ⟨hKY, ε₀, hε₀, hgood'⟩ := hgood
  have hY : IsGoodComplement (ScBanach.const (Fin n → ℝ)) (quadC n k) (kerCLM L) Y :=
    ⟨hKY, ε₀, hε₀, hgood'⟩
  have hKC : IsInGoodPosition (ScBanach.const (Fin n → ℝ)) (quadC n k) (kerCLM L) :=
    ⟨hint, Y, hY⟩
  have hsurj' : Function.Surjective (fderivWithin ℝ f U 0) := by rw [hLeq]; exact hsurj
  have hK : kerCLM L = LinearMap.ker (fderivWithin ℝ f U 0 : (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ)) := by
    rw [hLeq]; rfl
  have hj0 : ((j : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    intro h0'
    have : (j : ℕ∞) = 0 := by exact_mod_cast h0'
    rw [this] at hj
    exact absurd hj (by norm_num)
  refine conclusion_of hj0 ?_
  induction j using ENat.recTopCoe with
  | top => exact h378s hU h0 hf hf0 hsurj' hK hKC hY
  | coe i =>
    have hi : 1 ≤ i := by exact_mod_cast hj
    have hf' : ContDiffOn ℝ (i : WithTop ℕ∞) f U := by exact_mod_cast hf
    have := h378 hU h0 hi hf' hf0 hsurj' hK hKC hY
    exact_mod_cast this

#rt_check RoundTrip.V4_58.A_to_B [Polyfold.ContractionData.exists_solution_smooth,
  Polyfold.theorem_3_8_22_smooth, Polyfold.ContractionData.exists_radii,
  Polyfold.Radii.contDiffOn_τ, Polyfold.theorem_3_8_22]
#rt_overlap RoundTrip.V4_58.A_to_B [Polyfold.ContractionData.exists_solution_smooth,
  Polyfold.theorem_3_8_22_smooth, Polyfold.ContractionData.exists_radii,
  Polyfold.Radii.contDiffOn_τ, Polyfold.theorem_3_8_22]

end RoundTrip.V4_58

end
