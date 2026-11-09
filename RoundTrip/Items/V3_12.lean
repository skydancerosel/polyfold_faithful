import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_12

/-! Round trip for V3_12 (Proposition 3.10: the linearization of a basic germ plus an sc⁺-germ).
Refreshed 2026-11-02 against HEAD (new conjuncts: Proposition 3.10 on every level).

`A` is the conjunction of the types of the listed theorems `proposition_3_1_10`,
`proposition_3_1_10_scPlus`, `IsSc1GermWith.isScOperator_deriv_zero`, `ScBanach.scIndex_projWOp`,
`proposition_3_1_10_basic`, `StabilityData.exists_isFredholm_Dfs'`, and (new) `proposition_3_1_10_level`,
`proposition_3_1_10_full`, `IsBasicGerm.levelDeriv_add_eq`, `IsBasicGerm.snd_levelDeriv_add` (no
universe parameters; all spaces in `Type`).  `ScBanach.projWOp` is a definition (vocabulary).

B has two clauses: (i) `Df(0)` is sc-Fredholm of index `n − N`; (ii) for every `m`, the
level-`m` operator of `Df(x)` is Fredholm of index `n − N` for `x ∈ U_{m+1}` small on level `m`.

* `A → B` is now PROVED (`A_to_B`, through A's `proposition_3_1_10_full`).  Glue as before:
  `CtB n k` is a partial quadrant (the linear equivalence `ℝⁿ ≅ ℝᵏ × ℝⁿ⁻ᵏ`, as in V3_63), B's
  basic germ is the project's with `B := w − P_W h` (V3_10 glue), `s` sc-smooth into `F¹` is sc¹
  into `F¹`; for (i) `scIndex` is B's `indexB` of the base map definitionally; for (ii) B's
  operator `L` is `levelDeriv Df m x` (its defining identity is A's, with `x₁ = ι x`), B's
  `IsFredholmB`/`indexB` are Mathlib's `IsFredholm`/`fredholmIndex`, `dim ℝⁿ = n`.  The audit's
  partial result `A_to_B1` (clause (i) only) is kept.
* `B → A` is not proved: genuine difference of scope (A: any finite-dimensional `P`, `Q`, any
  partial (or quadrant-like) `C̃`, `s` only sc¹ into `F¹`, plus auxiliary statements (the sc⁺
  decomposition of `Df(0)`, the index of `(a, w) ↦ (0, w)`, `Df(0)` of any sc¹-germ is an
  sc-operator, the `StabilityData` level-`0` Fredholm statement, the level-`m` decomposition
  `Df(x)_m = T₀ + S(x) + K(x)` and its `W`-component), none of which B speaks about).
-/

namespace RoundTrip.V3_12
open Polyfold Set

/-- The project's statement (no universe parameters). -/
def A : Prop :=
  (type_of% @Polyfold.proposition_3_1_10) ∧
  (type_of% @Polyfold.proposition_3_1_10_scPlus) ∧
  (type_of% @Polyfold.IsSc1GermWith.isScOperator_deriv_zero) ∧
  (type_of% @Polyfold.ScBanach.scIndex_projWOp) ∧
  (type_of% @Polyfold.proposition_3_1_10_basic) ∧
  (type_of% @Polyfold.StabilityData.exists_isFredholm_Dfs') ∧
  (type_of% @Polyfold.proposition_3_1_10_level) ∧
  (type_of% @Polyfold.proposition_3_1_10_full) ∧
  (type_of% @Polyfold.IsBasicGerm.levelDeriv_add_eq) ∧
  (type_of% @Polyfold.IsBasicGerm.snd_levelDeriv_add)

theorem A_holds : A :=
  ⟨@Polyfold.proposition_3_1_10, @Polyfold.proposition_3_1_10_scPlus,
    @Polyfold.IsSc1GermWith.isScOperator_deriv_zero, @Polyfold.ScBanach.scIndex_projWOp,
    @Polyfold.proposition_3_1_10_basic, @Polyfold.StabilityData.exists_isFredholm_Dfs',
    @Polyfold.proposition_3_1_10_level, @Polyfold.proposition_3_1_10_full,
    @Polyfold.IsBasicGerm.levelDeriv_add_eq, @Polyfold.IsBasicGerm.snd_levelDeriv_add⟩

/-! ### Glue: `CtB n k` is a partial quadrant (as in V3_63) -/

/-- The index equivalence `Fin k ⊕ Fin (n − k) ≃ Fin n`. -/
def splitIdx (n k : ℕ) (hk : k ≤ n) : Fin k ⊕ Fin (n - k) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hk))

lemma splitIdx_inl_val (n k : ℕ) (hk : k ≤ n) (i : Fin k) :
    ((splitIdx n k hk (Sum.inl i) : Fin n) : ℕ) = i := by
  simp [splitIdx]

/-- The linear equivalence `ℝⁿ ≅ ℝᵏ × ℝⁿ⁻ᵏ`. -/
noncomputable def splitEquiv (n k : ℕ) (hk : k ≤ n) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin k → ℝ) × (Fin (n - k) → ℝ) :=
  (LinearEquiv.funCongrLeft ℝ ℝ (splitIdx n k hk)).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin (n - k)) ℝ ℝ)

lemma splitEquiv_fst (n k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin k) :
    (splitEquiv n k hk x).1 i = x (splitIdx n k hk (Sum.inl i)) := rfl

lemma mem_CtB_iff (n k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) :
    x ∈ CtB n k ↔ ∀ i : Fin k, 0 ≤ (splitEquiv n k hk x).1 i := by
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

theorem isPartialQuadrant_CtB (n k : ℕ) (hk : k ≤ n) :
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) (CtB n k) := by
  refine ⟨k, ScBanach.const (Fin (n - k) → ℝ), scIsoOfLinearEquiv (splitEquiv n k hk), ?_⟩
  ext x
  rw [mem_CtB_iff n k hk]
  change _ ↔ ∀ i, 0 ≤ ((scIsoOfLinearEquiv (splitEquiv n k hk)).lvl 0 x).1 i
  rw [scIsoOfLinearEquiv_apply]

/-! ### Glue: B's basic germs are the project's (V3_10) -/

section Glue
variable {n k N : ℕ} {W : ScBanach} {G : ScNbhdGerm (EB n W) (CtB n k ×ˢ Set.univ)}
  {f : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0}

lemma toBase_BB (hf : IsSc0Germ (F := EB N W) G f) {m : ℕ} {x : (EB n W).lvl m}
    (hx : x ∈ G.U m) :
    W.toBase m (x.2 - (levelMap (E := EB n W) (F := EB N W) f m x).2) =
      BB f ((EB n W).toBase m x) := by
  have h1 := hf.toBase_levelMap hx
  rw [ScBanach.paramProd_toBase, ScBanach.paramProd_toBase] at h1
  rw [ScBanach.paramProd_toBase, BB, map_sub, ← h1]

theorem B_to_proj (h : IsBasicGermB n k N W G f) : IsBasicGerm (CtB n k) G f (BB f) := by
  obtain ⟨hs, hf0, hB0, hc⟩ := h
  have hf : IsSc0Germ (F := EB N W) G f := (hs 0)
  refine ⟨hs, hf0, fun x _ => by simp [BB], ⟨⟨fun m x hx => ⟨_, toBase_BB hf hx⟩, fun m => ?_⟩,
    hB0, ?_⟩⟩
  · have hcont := hf.continuousOn m
    refine (continuous_snd.continuousOn.sub (continuous_snd.comp_continuousOn hcont)).congr ?_
    intro x hx
    exact levelMap_eq_of_toBase_eq (toBase_BB hf hx)
  · intro ε hε m
    obtain ⟨O, hO, hUO⟩ := G.relOpen m
    have h0O : (0 : (EB n W).lvl m) ∈ O := by
      have := G.zero_mem m; rw [hUO] at this; exact this.1
    obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO 0 h0O
    obtain ⟨δ, hδ, hcδ⟩ := hc ε hε m
    refine ⟨min ρ δ, lt_min hρ hδ, fun a ha har w w' hwr hw'r => ?_⟩
    have hmem : ∀ v : W.lvl m, ‖v‖ < min ρ δ → ((a, v) : (EB n W).lvl m) ∈ G.U m := by
      intro v hv
      rw [hUO]
      refine ⟨hρO ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk]
        exact max_lt (har.trans_le (min_le_left _ _)) (hv.trans_le (min_le_left _ _))
      · rw [ScBanach.paramProd_lvlSet]; exact ⟨ha, mem_univ _⟩
    refine ⟨hmem w hwr, ?_⟩
    obtain ⟨b, b', hb, hb', hest⟩ := hcδ a w w' (hmem w hwr) (hmem w' hw'r)
      (har.trans_le (min_le_right _ _)) (hwr.trans_le (min_le_right _ _))
      (hw'r.trans_le (min_le_right _ _))
    have e1 : levelB (BB f) m (a, w) = b :=
      levelMap_eq_of_toBase_eq (by rw [hb, ScBanach.paramProd_toBase])
    have e2 : levelB (BB f) m (a, w') = b' :=
      levelMap_eq_of_toBase_eq (by rw [hb', ScBanach.paramProd_toBase])
    rw [e1, e2]; exact hest

end Glue

/-- B's first clause: `Df(0)` is sc-Fredholm of index `n − N`. -/
def B1 : Prop :=
  ∀ (n k N : ℕ) (W : ScBanach), k ≤ n →
    ∀ (G : ScNbhdGerm (EB n W) (CtB n k ×ˢ Set.univ))
      (h : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0)
      (s : (EB n W).lvl 0 → (EB N W).shift.lvl 0),
      IsBasicGermB n k N W G h → IsScSmoothGerm (F := (EB N W).shift) G s →
      sumB h s 0 = 0 →
      ∀ D : (EB n W).lvl 1 → (EB n W).lvl 0 →L[ℝ] (EB N W).lvl 0,
        IsSc1GermWith (F := EB N W) G (sumB h s) D →
        ∃ T : ScOperator (EB n W) (EB N W),
          T.lvl 0 = D 0 ∧ IsScFredholm T ∧ indexB (T.lvl 0) = (n : ℤ) - N

/-- **`A → B (i)`**, through A's `proposition_3_1_10`. -/
theorem A_to_B1 : A → B1 := by
  rintro ⟨hA, -⟩ n k N W hk G h s hh hs _ D hD
  obtain ⟨Ds, hDs⟩ := (hs 1).1
  obtain ⟨hop, hF, hI⟩ := hA (isPartialQuadrant_CtB n k hk) (B_to_proj hh) hDs hD
  refine ⟨hop.toScOperator, hop.toScOperator_zero, hF, ?_⟩
  have e : indexB (hop.toScOperator.lvl 0) = scIndex hop.toScOperator := rfl
  rw [e, hI, Module.finrank_fin_fun, Module.finrank_fin_fun]

/-- B's Fredholm notion is Mathlib's (one direction suffices). -/
theorem fredB_of_isFredholm {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] {T : V →L[ℝ] V'} (h : T.IsFredholm) :
    IsFredholmB T :=
  ⟨h.finite_ker, h.isClosed_range, h.finite_coker⟩

/-- **`A → B`**, through A's `proposition_3_1_10_full` (both statements of Proposition 3.10). -/
theorem A_to_B : A → B := by
  rintro ⟨-, -, -, -, -, -, -, hfull, -⟩ n k N W hk G h s hh hs _ D hD
  obtain ⟨Ds, hDs⟩ := (hs 1).1
  obtain ⟨⟨hop, hF, hI⟩, hlev⟩ :=
    hfull (isPartialQuadrant_CtB n k hk) (B_to_proj hh) hDs hD
  refine ⟨⟨hop.toScOperator, hop.toScOperator_zero, hF, ?_⟩, fun m => ?_⟩
  · have e : indexB (hop.toScOperator.lvl 0) = scIndex hop.toScOperator := rfl
    rw [e, hI, Module.finrank_fin_fun, Module.finrank_fin_fun]
  · obtain ⟨δ, hδ, hL⟩ := hlev m
    refine ⟨δ, hδ, fun x x₁ hxx₁ hx hxδ => ?_⟩
    obtain ⟨hid, hFr, hind⟩ := hL x hx hxδ
    have hx₁ : (EB n W).shift.toBase m x = x₁ :=
      (EB n W).toBase_injective 1 (by rw [← ScBanach.shift_toBase]; exact hxx₁)
    refine ⟨levelDeriv D m x, fun v => ?_, fredB_of_isFredholm hFr, ?_⟩
    · rw [hid v, hx₁]
    · have e : indexB (levelDeriv D m x) = fredholmIndex (levelDeriv D m x) := rfl
      rw [e, hind, Module.finrank_fin_fun, Module.finrank_fin_fun]

#rt_check RoundTrip.V3_12.A_to_B1 [Polyfold.proposition_3_1_10, Polyfold.proposition_3_1_10_scPlus,
  Polyfold.IsSc1GermWith.isScOperator_deriv_zero, Polyfold.ScBanach.scIndex_projWOp,
  Polyfold.proposition_3_1_10_basic, Polyfold.StabilityData.exists_isFredholm_Dfs',
  Polyfold.proposition_3_1_10_level, Polyfold.proposition_3_1_10_full,
  Polyfold.IsBasicGerm.levelDeriv_add_eq, Polyfold.IsBasicGerm.snd_levelDeriv_add]
#rt_check RoundTrip.V3_12.A_to_B [Polyfold.proposition_3_1_10, Polyfold.proposition_3_1_10_scPlus,
  Polyfold.IsSc1GermWith.isScOperator_deriv_zero, Polyfold.ScBanach.scIndex_projWOp,
  Polyfold.proposition_3_1_10_basic, Polyfold.StabilityData.exists_isFredholm_Dfs',
  Polyfold.proposition_3_1_10_level, Polyfold.proposition_3_1_10_full,
  Polyfold.IsBasicGerm.levelDeriv_add_eq, Polyfold.IsBasicGerm.snd_levelDeriv_add]

end RoundTrip.V3_12
