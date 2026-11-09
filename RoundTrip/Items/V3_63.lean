import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_63

/-! Round trip for V3_63 (Theorem 3.78, the implicit function theorem in partial quadrants).

`A` is the conjunction of the types of `Polyfold.theorem_3_8_22` and
`Polyfold.ContractionData.exists_solution` (neither has universe parameters: all spaces live in
`Type`).

`A → B`: the blind setting (`ℝⁿ = Fin n → ℝ`, `C = quadC n k`, `f` into `Fin N → ℝ`) is an instance
of `theorem_3_8_22`: `quadC n k` is a partial quadrant (`isPartialQuadrant_quadC`, via the linear
equivalence `ℝⁿ ≅ ℝᵏ × ℝⁿ⁻ᵏ`), `fderivWithin f U 0 = L` by unique differentiability of `U`, the
blind good position/complement data are the project's `IsInGoodPosition`/`IsGoodComplement`, and
`τ : K → Y` is composed with `Y ↪ ℝⁿ`.  The clause `f(k + τ k) = 0` of `A` is dropped.

`B → A` is not proved: `B` (following the literal text) never asserts that the graph of `τ`
consists of zeros of `f` (`A`'s `f (k + τ k) = 0`); its conclusions about `f` are only the
uniqueness clause (3), whose hypothesis is a zero of `f`.  No instance of `B` yields a zero of any
map, so `A`'s existence clause would have to be re-proved (the contraction argument of Lemmas
3.79–3.82).  `B_to_A378_without_existence` checks that in the blind coordinates `B` yields every
other clause of `theorem_3_8_22`.  The remaining differences (an arbitrary finite-dimensional `V`
with any norm, an arbitrary normed target `F`, an abstract partial quadrant
`C = T⁻¹([0,∞)ⁿ ⊕ W)`, and the normalized conjunct `ContractionData.exists_solution`) are
transport glue only. -/

open Set

noncomputable section

namespace RoundTrip.V3_63
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.theorem_3_8_22) ∧ (type_of% @Polyfold.ContractionData.exists_solution)

theorem A_holds : A := ⟨@Polyfold.theorem_3_8_22, @Polyfold.ContractionData.exists_solution⟩

/-! ### Glue: `quadC n k` is a partial quadrant -/

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

theorem A_to_B : A → B := by
  intro hA n k N j U f L Y hkn hj hUrel h0 hf hf0 hL hsurj hint hgood
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
  obtain ⟨V', τ, ε, σ, hV'rel, h0V', hτcd, hτ0, hDτ0, hsol, hε, hσ, hbound, huniq⟩ :=
    hA.1 hU h0 hj hf hf0 hsurj' hK hKC hY
  refine ⟨V', fun v => (τ v : Fin n → ℝ), ε, σ, hV'rel, h0V', fun v _ => (τ v).2, ?_, hε, hσ,
    ⟨?_, ?_, fun v hv => (hsol v hv).1⟩, ?_, ?_⟩
  · exact Y.subtypeL.contDiff.comp_contDiffOn hτcd
  · simp [hτ0]
  · have hj' : (j : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    have hd : DifferentiableWithinAt ℝ τ V' 0 := hτcd.differentiableOn hj' 0 h0V'
    have h1 := hd.hasFDerivWithinAt
    rw [hDτ0] at h1
    have h2 := Y.subtypeL.hasFDerivAt.comp_hasFDerivWithinAt (0 : kerCLM L) h1
    simpa using h2
  · intro v hv hvε
    exact hbound v hv hvε
  · intro v hv y hy hvε hyσ hyU hfy
    exact huniq v hv hvε y hy hyσ hyU hfy

#rt_check RoundTrip.V3_63.A_to_B [Polyfold.theorem_3_8_22, Polyfold.ContractionData.exists_solution]

/-! ### `B → A` without the existence clause (diagnostic)

`B → A` is not proved.  To locate the gap: `B` gives `theorem_3_8_22`, restricted to the blind
coordinates (`V = Fin n → ℝ`, `F = Fin N → ℝ`, `C = quadC n q`), with every clause except
`f (k + τ k) = 0` (`B_to_A378_without_existence`). -/

/-- `theorem_3_8_22` in the blind coordinates, without the clause `f (k + τ k) = 0`. -/
def A378NoExistence : Prop :=
  ∀ (n q N j : ℕ) (U : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin N → ℝ))
    (K Y : Submodule ℝ (Fin n → ℝ)),
    q ≤ n → IsRelOpenInQuadrant (ScBanach.const (Fin n → ℝ)) (quadC n q) U →
    (0 : Fin n → ℝ) ∈ U → 1 ≤ j → ContDiffOn ℝ j f U → f 0 = 0 →
    Function.Surjective (fderivWithin ℝ f U 0) →
    K = LinearMap.ker (fderivWithin ℝ f U 0 : (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ)) →
    IsInGoodPosition (ScBanach.const (Fin n → ℝ)) (quadC n q) K →
    IsGoodComplement (ScBanach.const (Fin n → ℝ)) (quadC n q) K Y →
    ∃ (V' : Set K) (τ : K → Y) (ε σ : ℝ),
      (∃ O : Set K, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' (quadC n q)) ∧ (0 : K) ∈ V' ∧
      ContDiffOn ℝ j τ V' ∧ τ 0 = 0 ∧ fderivWithin ℝ τ V' 0 = 0 ∧
      (∀ k ∈ V', (k : Fin n → ℝ) + τ k ∈ U) ∧
      0 < ε ∧ 0 < σ ∧ (∀ k ∈ V', ‖k‖ ≤ ε → ‖τ k‖ ≤ σ) ∧
      (∀ k ∈ V', ‖k‖ ≤ ε → ∀ y ∈ Y, ‖y‖ ≤ σ → (k : Fin n → ℝ) + y ∈ U →
        f ((k : Fin n → ℝ) + y) = 0 → y = τ k)

theorem B_to_A378_without_existence : B → A378NoExistence := by
  intro hB n q N j U f K Y hqn hU h0 hj hf hf0 hsurj hK hKC hY
  subst hK
  set L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ) := fderivWithin ℝ f U 0 with hLdef
  have hj' : (j : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hL : HasFDerivWithinAt f L U 0 := ((hf.differentiableOn hj') 0 h0).hasFDerivWithinAt
  obtain ⟨V, τb, ε, σ, ⟨O, hO, hV⟩, h0V, hτY, hτcd, hε, hσ, ⟨hτ0, hDτ, hτU⟩, hbound, huniq⟩ :=
    hB n q N j U f L Y hqn hj hU.relOpen h0 hf hf0 hL hsurj hKC.interior_nonempty
      ⟨hY.isCompl, hY.exists_eps⟩
  -- the projection onto `Y` along `K`
  set pY : (Fin n → ℝ) →L[ℝ] Y :=
    LinearMap.toContinuousLinearMap (Submodule.projectionOnto Y (kerCLM L) hY.isCompl.symm)
    with hpY
  have hpY_mem : ∀ x ∈ Y, ((pY x : Y) : Fin n → ℝ) = x := fun x hx => by
    have := Submodule.projectionOnto_apply_left hY.isCompl.symm ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hτeq : ∀ k ∈ V, ((pY (τb k) : Y) : Fin n → ℝ) = τb k := fun k hk => hpY_mem _ (hτY k hk)
  -- unique differentiability of `V` at `0`
  have hconv : Convex ℝ (Subtype.val ⁻¹' quadC n q : Set (kerCLM L)) :=
    fun x hx y hy a b ha hb hab => (isPartialQuadrant_quadC n q hqn).convex hx hy ha hb hab
  have hint : (interior (Subtype.val ⁻¹' quadC n q : Set (kerCLM L))).Nonempty :=
    hKC.interior_nonempty
  have h0C : (0 : kerCLM L) ∈ (Subtype.val ⁻¹' quadC n q : Set (kerCLM L)) := by
    rw [hV] at h0V; exact h0V.2
  have hVUD : UniqueDiffWithinAt ℝ V 0 := by
    rw [hV, inter_comm]
    exact (uniqueDiffWithinAt_convex (E := kerCLM L) hconv hint (subset_closure h0C)).inter
      (hO.mem_nhds (by rw [hV] at h0V; exact h0V.1))
  refine ⟨V, fun k => pY (τb k), ε, σ, ⟨O, hO, hV⟩, h0V, pY.contDiff.comp_contDiffOn hτcd, ?_, ?_,
    fun k hk => by rw [hτeq k hk]; exact hτU k hk, hε, hσ, fun k hk hkε => ?_,
    fun k hk hkε y hy hyσ hyU hfy => ?_⟩
  · exact (congrArg pY hτ0).trans (map_zero pY)
  · have h1 := pY.hasFDerivAt.comp_hasFDerivWithinAt (0 : kerCLM L) hDτ
    rw [ContinuousLinearMap.comp_zero] at h1
    exact h1.fderivWithin hVUD
  · have := hbound k hk hkε
    rw [← hτeq k hk] at this
    exact this
  · rw [hτeq k hk]
    exact huniq k hk y hy hkε hyσ hyU hfy

#rt_check RoundTrip.V3_63.B_to_A378_without_existence
  [Polyfold.theorem_3_8_22, Polyfold.ContractionData.exists_solution]
#rt_overlap RoundTrip.V3_63.B_to_A378_without_existence
  [Polyfold.theorem_3_8_22, Polyfold.ContractionData.exists_solution]
#rt_overlap RoundTrip.V3_63.A_to_B [Polyfold.theorem_3_8_22, Polyfold.ContractionData.exists_solution]

end RoundTrip.V3_63

end
