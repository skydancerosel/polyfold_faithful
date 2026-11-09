import Polyfold.Chapter3.ContractionGerm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.3,
Lemmas 3.3.4 and 3.3.5 (preprint 3.31 and 3.32), Theorem 3.3.6 (preprint 3.33) (the germ implicit function theorem), Corollary 3.3.7 (preprint 3.34),
Theorem 3.35.

# The germ implicit function theorem

## The text, paraphrased

(Lemma 3.3.4 (preprint 3.31)) Let `f(a, w) = w − B(a, w)` be an sc⁰-contraction germ of class sc^k, `k ≥ 1`, with
solution germ `δ` of class sc^j.  Then
`f⁽¹⁾(v, b, u, w) = (u − B(v, u), w − DB(v, δ(v))(b, w)) = (u, w) − B⁽¹⁾(v, b, u, w)` is an
sc⁰-contraction germ `O(TC̃ ⊕ TW, 0) → TW` of class `sc^{min(k−1, j)}`, and its solution germ is
`Tδ`.  (Lemma 3.3.5 (preprint 3.32)) Iterating, for `j ≤ k` there is a contraction germ `f⁽ʲ⁾` of class
`sc^{min(k−j, 1)}` with solution germ `T^jδ`.  (Theorem 3.3.6 (preprint 3.33)) If `f` is sc^k, then `δ` is sc^k:
otherwise `δ` is sc^j but not sc^{j+1} for some `j < k`; `f⁽ʲ⁾` is sc¹, so by Theorem 3.3.3 (preprint 3.30) its
solution germ `T^jδ` is sc¹, so `δ` is sc^{j+1}.  (Corollary 3.3.7 (preprint 3.34)) If `f` is sc-smooth then for
all `m, k` there is a relatively open `V_{m,k} ∋ 0` with `δ(V_{m,k}) ⊆ W_m` and
`δ : V_{m,k} → W_m` of class `C^k`.  (Theorem 3.35) The same for any finite-dimensional partial
quadrant `C̃ ⊆ ℝⁿ`.

## What is formalized

* `ContractionGerm.next 𝒞 hC hB s` (**the germ `f⁽¹⁾` of Lemma 3.3.4 (preprint 3.31)**, formula (38)), a
  `ContractionGerm (P × P) (C̃ × P) (TW)` with explicit regions `N(m+2+s) × P`, `O(m+1) × W_m`,
  `K(m+1) × W_m`; its map `nextB` is `(pr₁ ∘ TB ∘ σ, pr₂ ∘ TB ∘ Γ)` with the reshuffle
  `σ(v, b, u, w) = ((v, u), (b, w))` and `Γ(v, b, u, w) = ((v, δ(v)), (b, w))`.
  `ContractionGerm.lemma_3_3_4`: it is of class `sc^{min(k−1, j)}` (`nextB_isSckGerm`) and its
  solution germ is `Tδ = (δ(v), Dδ(v)b)` on `N(2+s) ∩ C̃ × P` (`next_sol`,
  `next_sol_eq_tangentMapWith`).
* `ContractionGerm.sol_isSckGerm` (**Lemma 3.3.5 (preprint 3.32) and the proof of Theorem 3.3.6 (preprint 3.33)**, as one induction
  on `j` over all contraction germs: if `f` is sc^k and `j ≤ k`, then `δ` is an sc^j-germ on some
  `germ s`), **Theorem 3.3.6 (preprint 3.33)** (`theorem_3_3_6`), **Corollary 3.3.7 (preprint 3.34)** (`corollary_3_3_7`), **Theorem
  3.35** (`theorem_3_35_preprint`, for `C̃` a partial quadrant in `P`), and the versions from Definition
  3.28's balls (`theorem_3_3_2_of_isSc0ContractionGerm`, `theorem_3_3_6_of_isSc0ContractionGerm`)
  through the working form `IsSc0ContractionGerm.toContractionGerm` (the construction in the
  proof of Theorem 3.3.2 (preprint 3.29), at the end of this file).

## What the text leaves implicit, and the choices made (the findings)

* **The germ shrinks with `k`.**  Theorem 3.3.3 (preprint 3.30) gives sc¹ on the re-indexed germ `germ 1`
  (see `ContractionGerm.lean`), and each induction step of Theorem 3.3.6 (preprint 3.33) shifts again: `δ` is
  sc^k on `germ (s k)` with `s k` growing with `k`.  The proof gives the explicit shift
  `s_k = 2^k − 1`: the step `j → j + 1` (`isSckGerm_succ_of_next`) combines the shift `s` of `δ`
  and the shift `s'` of `Tδ` (the solution germ of `f⁽¹⁾`, again shifted by `s_j`) into
  `s + s' + 1`, so `s_0 = 0`, `s_{j+1} = 2s_j + 1`.  So `theorem_3_3_6_smooth`, `corollary_3_3_7`
  and `theorem_3_35_smooth_preprint` below state "δ is sc-smooth" as "for every `k`, sc^k on `germ s_k`"
  (`V_{m,k}` depending on `k`, as in Corollary 3.3.7 (preprint 3.34)'s first clause); no single `germ s` is
  certified for all `k`.  The text's reading — one germ on which `δ` is sc^k for every `k`
  (`IsScSmoothGerm`) — nevertheless holds, on the diagonal germ `V_m = N(m + Σ_{j ≤ m} s_j) ∩ C̃`,
  since sc^j only involves the levels `≥ j` (`corollary_3_3_7_isScSmoothGerm`,
  `theorem_3_35_isScSmoothGerm_preprint`, `theorem_3_35_of_isSc0ContractionGerm_preprint` in `GermIFTSmooth.lean`;
  round-trip items V3.31, V3.32).
* **Lemma 3.3.5 (preprint 3.32) is reorganised.**  The text proves Theorem 3.3.6 (preprint 3.33) by contradiction from Lemma 3.3.5 (preprint 3.32)
  (an `f⁽ʲ⁾` with solution `T^jδ`).  Here the induction is on `j` with the statement quantified
  over all contraction germs (the parameter space of `f⁽¹⁾` is `P × P`, its fibre `TW`): if `δ`
  is sc^j then `f⁽¹⁾` is sc^j (Lemma 3.3.4 (preprint 3.31), `k − 1 ≥ j`), so its solution `Tδ` is sc^j by the
  induction hypothesis, and `δ` is sc¹ by Theorem 3.3.3 (preprint 3.30), hence sc^{j+1}.  This is the content of
  Lemma 3.3.5 (preprint 3.32) without the iterated germs `f⁽ʲ⁾`.
* **The solution germ of `f⁽¹⁾` is `Tδ`**: the text says "from the uniqueness".  Uniqueness holds
  in `O⁽¹⁾₀ = O₁ × W₀`, and `Tδ(v, b) = (δ(v), Dδ(v)b)` lies there because `δ(v) ∈ O₁` for
  `v ∈ N 1` (the fibre of the tangent germ is unbounded, which is why the regions are kept
  explicit); and `Dδ(v) = (1 − D₂B)⁻¹D₁B` needs `v ∈ N 2` (the level-`1` operators), hence the
  region `N(2+s) × P` of `f⁽¹⁾`.
* **"As one verifies by comparing `Tf` with `f⁽¹⁾`"** (Lemma 3.3.4 (preprint 3.31)) is the chain rule for germs
  (`IsSckGerm.comp`, `IsSckGerm.pair`) with the sc-operators `σ`, the projections, and the
  shifted solution germ `v ↦ δ(v) ∈ W₁` (Proposition 1.2.2 (preprint 1.17) for germs, `IsSckGerm.shift`).
* **Corollary 3.3.7 (preprint 3.34) (2)** uses Proposition 1.2.3 (preprint 1.18) for germs (`IsSckGerm.contDiffOn_levels`, proved
  in `GermLevels.lean`; the text cites the version for relatively open sets).
* The identifications `TC̃ = C̃ × P` (for finite-dimensional `P`, `(const P).tangent` and
  `const (P × P)` have the same levels) are sc-isomorphisms applied through the chain rule,
  `constTangentOp`; the text identifies silently.
-/

open Set Filter Topology Function Asymptotics Metric

noncomputable section

namespace Polyfold

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

/-! ### The reshuffling sc-operators -/

section Operators

variable (P W)

/-- `σ : (P ⊕ P) ⊕ TW → T(P ⊕ W)`, `((v, b), (u, w)) ↦ ((v, u), (b, w))`. -/
def tangentShuffle :
    ScOperator (ScBanach.paramProd (P × P) W.tangent) (ScBanach.paramProd P W).tangent where
  lvl m :=
    (((ContinuousLinearMap.fst ℝ P P).comp
        (ContinuousLinearMap.fst ℝ (P × P) (W (m + 1) × W m))).prod
      ((ContinuousLinearMap.fst ℝ (W (m + 1)) (W m)).comp
        (ContinuousLinearMap.snd ℝ (P × P) (W (m + 1) × W m)))).prod
    (((ContinuousLinearMap.snd ℝ P P).comp
        (ContinuousLinearMap.fst ℝ (P × P) (W (m + 1) × W m))).prod
      ((ContinuousLinearMap.snd ℝ (W (m + 1)) (W m)).comp
        (ContinuousLinearMap.snd ℝ (P × P) (W (m + 1) × W m))))
  incl_comm _ _ := rfl

@[simp] lemma tangentShuffle_apply (m : ℕ) (q : (ScBanach.paramProd (P × P) W.tangent) m) :
    tangentShuffle P W m q = (((q.1.1, q.2.1), (q.1.2, q.2.2)) : (ScBanach.paramProd P W).tangent m) :=
  rfl

/-- The projection `(P ⊕ P) ⊕ TW → P¹`, `((v, b), (u, w)) ↦ v` (into the shifted constant
structure, the source of the shifted solution germ). -/
def projV : ScOperator (ScBanach.paramProd (P × P) W.tangent) (ScBanach.const P).shift where
  lvl m := (ContinuousLinearMap.fst ℝ P P).comp
    (ContinuousLinearMap.fst ℝ (P × P) (W (m + 1) × W m))
  incl_comm _ _ := rfl

@[simp] lemma projV_apply (m : ℕ) (q : (ScBanach.paramProd (P × P) W.tangent) m) :
    projV P W m q = q.1.1 := rfl

/-- The projection `(P ⊕ P) ⊕ TW → P ⊕ W`, `((v, b), (u, w)) ↦ (b, w)`. -/
def projBW : ScOperator (ScBanach.paramProd (P × P) W.tangent) (ScBanach.paramProd P W) where
  lvl m := ((ContinuousLinearMap.snd ℝ P P).comp
      (ContinuousLinearMap.fst ℝ (P × P) (W (m + 1) × W m))).prod
    ((ContinuousLinearMap.snd ℝ (W (m + 1)) (W m)).comp
      (ContinuousLinearMap.snd ℝ (P × P) (W (m + 1) × W m)))
  incl_comm _ _ := rfl

@[simp] lemma projBW_apply (m : ℕ) (q : (ScBanach.paramProd (P × P) W.tangent) m) :
    projBW P W m q = ((q.1.2, q.2.2) : (ScBanach.paramProd P W) m) := rfl

/-- The identification `P¹ ⊕ W¹ = (P ⊕ W)¹` (identity on every level). -/
def shiftParamOp : ScOperator ((ScBanach.const P).shift.prod W.shift) (ScBanach.paramProd P W).shift where
  lvl m := ContinuousLinearMap.id ℝ (P × W (m + 1))
  incl_comm _ _ := rfl

@[simp] lemma shiftParamOp_apply (m : ℕ) (q : ((ScBanach.const P).shift.prod W.shift) m) :
    shiftParamOp P W m q = q := rfl

/-- The identification `P ⊕ P = T P` of the constant structures (identity on every level). -/
def constTangentOp : ScOperator (ScBanach.const (P × P)) (ScBanach.const P).tangent where
  lvl _ := ContinuousLinearMap.id ℝ (P × P)
  incl_comm _ _ := rfl

@[simp] lemma constTangentOp_apply (m : ℕ) (q : P × P) : constTangentOp P m q = q := rfl

/-- The identification `T P = P ⊕ P` of the constant structures (identity on every level). -/
def constTangentOp' : ScOperator (ScBanach.const P).tangent (ScBanach.const (P × P)) where
  lvl _ := ContinuousLinearMap.id ℝ (P × P)
  incl_comm _ _ := rfl

@[simp] lemma constTangentOp'_apply (m : ℕ) (q : P × P) : constTangentOp' P m q = q := rfl

end Operators

namespace ContractionGerm

variable (𝒞 : ContractionGerm P Ct W)
  {D : (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] W 0}

/-! ### Lemma 3.3.4 (preprint 3.31): the contraction germ `f⁽¹⁾` -/

/-- The germ of neighbourhoods of `f⁽¹⁾`: `U⁽¹⁾_m = {((v, b), (u, w)) | (v, u) ∈ U_{m+1},
v ∈ N(m+1+s)}` in `(P ⊕ P) ⊕ TW`. -/
def nextG (s : ℕ) :
    ScNbhdGerm (ScBanach.paramProd (P × P) W.tangent) ((Ct ×ˢ univ) ×ˢ univ) where
  U m := {q | (tangentShuffle P W m q).1 ∈ 𝒞.G.U (m + 1) ∧ projV P W m q ∈ 𝒞.N (m + 1 + s)}
  nested m q hq := ⟨𝒞.G.nested (m + 1) _ hq.1, 𝒞.N_anti_le (by omega) hq.2⟩
  zero_mem m := ⟨𝒞.G.zero_mem (m + 1), 𝒞.N_zero _⟩
  relOpen m := by
    obtain ⟨O, hO, hU⟩ := 𝒞.G.relOpen (m + 1)
    refine ⟨{q | (tangentShuffle P W m q).1 ∈ O} ∩ {q | projV P W m q ∈ 𝒞.N (m + 1 + s)}, ?_, ?_⟩
    · exact (hO.preimage (continuous_fst.comp (tangentShuffle P W m).continuous)).inter
        ((𝒞.N_open _).preimage (projV P W m).continuous)
    · ext q
      rw [ScBanach.paramProd_lvlSet]
      change (tangentShuffle P W m q).1 ∈ 𝒞.G.U (m + 1) ∧ projV P W m q ∈ 𝒞.N (m + 1 + s) ↔
        ((tangentShuffle P W m q).1 ∈ O ∧ projV P W m q ∈ 𝒞.N (m + 1 + s)) ∧
          q ∈ (Ct ×ˢ univ) ×ˢ univ
      rw [hU, ScBanach.paramProd_lvlSet]
      have : (tangentShuffle P W m q).1 ∈ Ct ×ˢ univ ↔ q ∈ (Ct ×ˢ univ) ×ˢ univ := by
        simp only [mem_prod, mem_univ, and_true]
        exact Iff.rfl
      rw [mem_inter_iff, this]
      tauto

lemma nextG_U (s m : ℕ) (q : (ScBanach.paramProd (P × P) W.tangent) m) :
    q ∈ (𝒞.nextG s).U m ↔
      (((q.1 : P × P).1, (q.2 : W (m + 1) × W m).1) : (ScBanach.paramProd P W) (m + 1)) ∈
        𝒞.G.U (m + 1) ∧ (q.1 : P × P).1 ∈ 𝒞.N (m + 1 + s) := Iff.rfl

lemma mem_Ct_of_mem_nextG {s m : ℕ} {q : (ScBanach.paramProd (P × P) W.tangent) m}
    (hq : q ∈ (𝒞.nextG s).U m) : (q.1 : P × P).1 ∈ Ct := by
  have := 𝒞.G.U_subset (m + 1) hq.1
  rw [ScBanach.paramProd_lvlSet] at this
  exact this.1

/-- `Γ((v, b), (u, w)) = ((v, δ(v)), (b, w))` (with `δ(v) ∈ W₁`, the shifted solution germ). -/
def nextΓ : (ScBanach.paramProd (P × P) W.tangent) 0 → (ScBanach.paramProd P W).tangent 0 :=
  pairMap (shiftParamOp P W 0 ∘ pairMap (projV P W 0)
      (levelMap (E := ScBanach.const P) (F := W) 𝒞.sol 1 ∘ projV P W 0))
    (projBW P W 0)

lemma nextΓ_apply (q : (ScBanach.paramProd (P × P) W.tangent) 0) :
    𝒞.nextΓ q = ((((q.1 : P × P).1, levelMap (E := ScBanach.const P) (F := W) 𝒞.sol 1 (q.1 : P × P).1),
      ((q.1 : P × P).2, (q.2 : W 1 × W 0).2)) : (ScBanach.paramProd P W).tangent 0) := rfl

/-- **The map `B⁽¹⁾` of Lemma 3.3.4 (preprint 3.31)**, formula (38):
`B⁽¹⁾((v, b), (u, w)) = (B(v, u), DB(v, δ(v))(b, w))`, written as `(pr₁ ∘ TB ∘ σ, pr₂ ∘ TB ∘ Γ)`. -/
def nextB (D : (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] W 0) :
    (ScBanach.paramProd (P × P) W.tangent) 0 → W.tangent 0 :=
  pairMap (ScBanach.fstOp W.shift W 0 ∘ tangentMapWith 𝒞.B D ∘ tangentShuffle P W 0)
    (ScBanach.sndOp W.shift W 0 ∘ tangentMapWith 𝒞.B D ∘ 𝒞.nextΓ)

lemma nextB_apply (q : (ScBanach.paramProd (P × P) W.tangent) 0) :
    𝒞.nextB D q = ((levelB 𝒞.B 1 ((q.1 : P × P).1, (q.2 : W 1 × W 0).1),
      D (((q.1 : P × P).1, levelMap (E := ScBanach.const P) (F := W) 𝒞.sol 1 (q.1 : P × P).1) :
        (ScBanach.paramProd P W) 1) (((q.1 : P × P).2, (q.2 : W 1 × W 0).2) :
          (ScBanach.paramProd P W) 0)) : W.tangent 0) :=
  rfl

omit 𝒞 in
lemma isQuadrantLike_next (hC : IsQuadrantLike (ScBanach.const P) Ct) (W : ScBanach) :
    IsQuadrantLike (ScBanach.paramProd (P × P) W.tangent) ((Ct ×ˢ univ) ×ˢ univ) :=
  (hC.prod_univ_const (Q := P)).paramProd W.tangent

variable (hC : IsQuadrantLike (ScBanach.const P) Ct)
include hC

omit hC in
/-- `Γ` maps `U⁽¹⁾_m` into `(TU)_m = U_{m+1} × E_m`, with level maps
`((v, b), (u, w)) ↦ ((v, δ_{m+1}(v)), (b, w))`. -/
lemma levelMap_nextΓ {s m : ℕ} {q : (ScBanach.paramProd (P × P) W.tangent) m}
    (hq : q ∈ (𝒞.nextG s).U m) :
    levelMap 𝒞.nextΓ m q = ((((q.1 : P × P).1, 𝒞.fixLvl (m + 1) (q.1 : P × P).1),
      ((q.1 : P × P).2, (q.2 : W (m + 1) × W m).2)) : (ScBanach.paramProd P W).tangent m) := by
  have hv : (q.1 : P × P).1 ∈ 𝒞.N (m + 1) ∩ Ct :=
    ⟨𝒞.N_anti_le (by omega) hq.2, 𝒞.mem_Ct_of_mem_nextG hq⟩
  have hv1 : (q.1 : P × P).1 ∈ 𝒞.N 1 ∩ Ct :=
    ⟨𝒞.N_anti_le (by omega) hq.2, 𝒞.mem_Ct_of_mem_nextG hq⟩
  apply levelMap_eq_of_toBase_eq
  rw [ScBanach.tangent_toBase, ScBanach.paramProd_shift_toBase, ScBanach.paramProd_toBase,
    𝒞.shift_toBase_fixLvl m hv, ScBanach.paramProd_toBase, ScBanach.tangent_toBase, nextΓ_apply]
  simp only
  rw [𝒞.levelMap_sol 1 hv1]

omit hC in
lemma nextΓ_mapsToGerm (s : ℕ) : (𝒞.nextG s).MapsToGerm 𝒞.G.tangent 𝒞.nextΓ := by
  intro m q hq
  rw [𝒞.levelMap_nextΓ hq]
  refine ⟨?_, mem_univ _⟩
  exact 𝒞.mem_G_fixLvl (m + 1) ⟨𝒞.N_anti_le (by omega) hq.2, 𝒞.mem_Ct_of_mem_nextG hq⟩

omit hC in
lemma tangentShuffle_mapsToGerm (s : ℕ) :
    (𝒞.nextG s).MapsToGerm 𝒞.G.tangent (tangentShuffle P W 0) := by
  intro m q hq
  rw [ScOperator.levelMap_eq, tangentShuffle_apply]
  exact ⟨hq.1, mem_univ _⟩

lemma projV_mapsToGerm (s : ℕ) : (𝒞.nextG s).MapsToGerm (𝒞.germ hC s).shift (projV P W 0) := by
  intro m q hq
  rw [ScOperator.levelMap_eq, projV_apply]
  exact ⟨hq.2, 𝒞.mem_Ct_of_mem_nextG hq⟩

/-- `Γ` is an sc^j-germ when `δ` is. -/
lemma nextΓ_isSckGerm {j s : ℕ} (hs : IsSckGerm j (𝒞.germ hC s) 𝒞.sol) :
    IsSckGerm j (𝒞.nextG s) 𝒞.nextΓ := by
  have hC' := isQuadrantLike_next hC W
  refine IsSckGerm.pair hC' ?_ ((projBW P W).isSckGerm j _ hC')
  refine IsSckGerm.operator_comp hC' _ (IsSckGerm.pair hC' ((projV P W).isSckGerm j _ hC') ?_)
  exact IsSckGerm.comp hC' hC.shift (hs.shift hC) ((projV P W).isSckGerm j _ hC')
    (𝒞.projV_mapsToGerm hC s)

/-- **Lemma 3.3.4 (preprint 3.31), the regularity**: if `TB` is an sc^j-germ on `TU` and `δ` an sc^j-germ on
`germ s`, then `B⁽¹⁾` is an sc^j-germ on `U⁽¹⁾`. -/
theorem nextB_isSckGerm {j s : ℕ} (hTB : IsSckGerm j 𝒞.G.tangent (tangentMapWith 𝒞.B D))
    (hs : IsSckGerm j (𝒞.germ hC s) 𝒞.sol) : IsSckGerm j (𝒞.nextG s) (𝒞.nextB D) := by
  have hC' := isQuadrantLike_next hC W
  have hCT : IsQuadrantLike (ScBanach.paramProd P W).tangent
      ((ScBanach.paramProd P W).tangentSet (Ct ×ˢ univ)) := (hC.paramProd W).tangentSet
  refine IsSckGerm.pair hC' (IsSckGerm.operator_comp hC' _ ?_) (IsSckGerm.operator_comp hC' _ ?_)
  · exact IsSckGerm.comp hC' hCT hTB ((tangentShuffle P W).isSckGerm j _ hC')
      (𝒞.tangentShuffle_mapsToGerm s)
  · exact IsSckGerm.comp hC' hCT hTB (𝒞.nextΓ_isSckGerm hC hs) (𝒞.nextΓ_mapsToGerm s)

variable (hB : IsSc1GermWith 𝒞.G 𝒞.B D)
include hB

omit hC in
/-- The level-`m` map of `B⁽¹⁾` at a point of `N(m+1) ∩ C̃`:
`B⁽¹⁾_m((v, b), (u, w)) = (B_{m+1}(v, u), Df(v, δ_{m+1}(v))(b, w))`. -/
lemma levelB_next {m : ℕ} {v b : P} (hv : v ∈ 𝒞.N (m + 1) ∩ Ct) {u : W (m + 1)}
    (hu : u ∈ 𝒞.O (m + 1)) (w : W m) :
    levelB (𝒞.nextB D) m (((v, b), (u, w)) : (ScBanach.paramProd (P × P) W.tangent) m) =
      ((levelB 𝒞.B (m + 1) (v, u), 𝒞.Lop (D := D) m v (b, w)) : W.tangent m) := by
  have hv1 : v ∈ 𝒞.N 1 ∩ Ct := ⟨𝒞.N_anti_le (by omega) hv.1, hv.2⟩
  have hvu : ((v, u) : (ScBanach.paramProd P W) (m + 1)) ∈ 𝒞.G.U (m + 1) := 𝒞.mem_G (m + 1) v hv u hu
  apply levelMap_eq_of_toBase_eq
  rw [ScBanach.tangent_toBase, ScBanach.paramProd_toBase, ScBanach.tangent_toBase, nextB_apply]
  simp only
  rw [𝒞.levelMap_sol 1 hv1]
  refine Prod.ext ?_ ?_
  · show W.shift.toBase m (levelB 𝒞.B (m + 1) (v, u)) = levelB 𝒞.B 1 (v, W.shift.toBase m u)
    rw [← IsSc1GermWith.levelMap_shift_toBase hB.isSc0 hvu, ScBanach.paramProd_shift_toBase]
  · show W.toBase m (𝒞.Lop (D := D) m v (b, w)) = D (v, 𝒞.fixLvl 1 v) (b, W.toBase m w)
    rw [Lop, hB.toBase_levelDeriv (𝒞.mem_G_fixLvl (m + 1) hv), ScBanach.paramProd_shift_toBase,
      ScBanach.paramProd_toBase, 𝒞.shift_toBase_fixLvl m hv]

omit hC hB in
lemma nextB_zero : 𝒞.nextB D ((0 : P × P), (0 : W.tangent 0)) = 0 := by
  rw [nextB_apply]
  refine Prod.ext ?_ ?_
  · show levelB 𝒞.B 1 ((0 : P), (0 : W 1)) = 0
    apply levelMap_eq_of_toBase_eq
    rw [map_zero, ScBanach.paramProd_toBase, map_zero]
    exact 𝒞.B_zero.symm
  · show D _ (((0 : P), (0 : W 0)) : (ScBanach.paramProd P W) 0) = 0
    exact map_zero _

/-- **The contraction germ `f⁽¹⁾` of Lemma 3.3.4 (preprint 3.31)** (formula (38)), in the working form: parameter
space `P × P ⊇ C̃ × P`, fibre `TW`, map `B⁽¹⁾`, regions `N(m+2+s) × P`, `O(m+1) × W_m`,
`K(m+1) × W_m`. -/
def next (s : ℕ) : ContractionGerm (P × P) (Ct ×ˢ univ) W.tangent where
  B := 𝒞.nextB D
  G := 𝒞.nextG s
  B_zero := 𝒞.nextB_zero (D := D)
  isSc0 := 𝒞.nextB_isSckGerm hC (j := 0) hB.tangent_isSc0 (𝒞.isSolutionGerm_germ hC s).isSc0
  N m := 𝒞.N (m + 2 + s) ×ˢ univ
  N_open m := (𝒞.N_open _).prod isOpen_univ
  N_zero m := ⟨𝒞.N_zero _, mem_univ _⟩
  N_anti m := prod_mono (𝒞.N_anti_le (by omega)) subset_rfl
  O m := 𝒞.O (m + 1) ×ˢ univ
  K m := 𝒞.K (m + 1) ×ˢ univ
  O_open m := (𝒞.O_open _).prod isOpen_univ
  K_closed m := (𝒞.K_closed _).prod isClosed_univ
  K_zero m := ⟨𝒞.K_zero _, mem_univ _⟩
  K_sub m := prod_mono (𝒞.K_sub _) subset_rfl
  K_incl m w hw := ⟨𝒞.K_incl (m + 1) w.1 hw.1, mem_univ _⟩
  mem_G m a ha w hw := by
    refine ⟨?_, 𝒞.N_anti_le (by omega) ha.1.1⟩
    exact 𝒞.mem_G (m + 1) a.1 ⟨𝒞.N_anti_le (by omega) ha.1.1, ha.2.1⟩ w.1 hw.1
  mapsTo m a ha w hw := by
    obtain ⟨v, b⟩ := a
    obtain ⟨u, w⟩ := w
    have hv : v ∈ 𝒞.N (m + 1) ∩ Ct := ⟨𝒞.N_anti_le (by omega) ha.1.1, ha.2.1⟩
    show levelB (𝒞.nextB D) m ((v, b), (u, w)) ∈ 𝒞.K (m + 1) ×ˢ univ
    rw [𝒞.levelB_next hB hv (𝒞.K_sub _ hw.1)]
    exact ⟨𝒞.mapsTo (m + 1) v hv hw.1, mem_univ _⟩
  contr m a ha w hw w' hw' := by
    obtain ⟨v, b⟩ := a
    obtain ⟨u, w⟩ := w
    obtain ⟨u', w'⟩ := w'
    have hv : v ∈ 𝒞.N (m + 1) ∩ Ct := ⟨𝒞.N_anti_le (by omega) ha.1.1, ha.2.1⟩
    rw [𝒞.levelB_next hB hv hw.1, 𝒞.levelB_next hB hv hw'.1]
    have h1 := 𝒞.contr (m + 1) v hv u hw.1 u' hw'.1
    have h2 : ‖𝒞.Lop (D := D) m v (b, w) - 𝒞.Lop (D := D) m v (b, w')‖ ≤ 1 / 2 * ‖w - w'‖ := by
      rw [𝒞.Lop_apply m v b w, 𝒞.Lop_apply m v b w', add_sub_add_left_eq_sub, ← map_sub]
      calc ‖𝒞.Top (D := D) m v (w - w')‖ ≤ ‖𝒞.Top (D := D) m v‖ * ‖w - w'‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 / 2 * ‖w - w'‖ := by gcongr; exact 𝒞.norm_Top_le hC hB hv
    show max ‖levelB 𝒞.B (m + 1) (v, u) - levelB 𝒞.B (m + 1) (v, u')‖
        ‖𝒞.Lop (D := D) m v (b, w) - 𝒞.Lop (D := D) m v (b, w')‖ ≤ 1 / 2 * max ‖u - u'‖ ‖w - w'‖
    refine max_le (h1.trans ?_) (h2.trans ?_) <;> gcongr
    · exact le_max_left _ _
    · exact le_max_right _ _

@[simp] lemma next_B (s : ℕ) : (𝒞.next hC hB s).B = 𝒞.nextB D := rfl
@[simp] lemma next_G (s : ℕ) : (𝒞.next hC hB s).G = 𝒞.nextG s := rfl
@[simp] lemma next_N (s m : ℕ) : (𝒞.next hC hB s).N m = 𝒞.N (m + 2 + s) ×ˢ univ := rfl
@[simp] lemma next_O (s m : ℕ) : (𝒞.next hC hB s).O m = 𝒞.O (m + 1) ×ˢ univ := rfl

/-- **Lemma 3.3.4 (preprint 3.31), the solution germ**: the solution germ of `f⁽¹⁾` is
`Tδ(v, b) = (δ(v), Dδ(v)b)` (by the uniqueness of Theorem 3.3.2 (preprint 3.29) in `O₁ × W₀`). -/
theorem next_sol {s : ℕ} {v b : P} (hv : v ∈ 𝒞.N (2 + s) ∩ Ct) :
    (𝒞.next hC hB s).sol (v, b) = ((𝒞.fixLvl 1 v, 𝒞.Aop (D := D) 0 v b) : W.tangent 0) := by
  have hv1 : v ∈ 𝒞.N 1 ∩ Ct := ⟨𝒞.N_anti_le (by omega) hv.1, hv.2⟩
  have ha : ((v, b) : P × P) ∈ (𝒞.next hC hB s).N 0 ∩ (Ct ×ˢ univ) :=
    ⟨⟨hv.1, mem_univ _⟩, hv.2, mem_univ _⟩
  refine ((𝒞.next hC hB s).eq_sol ha ⟨𝒞.fixLvl_mem_O 1 hv1, mem_univ _⟩ ?_).symm
  rw [next_B, nextB_apply]
  simp only
  rw [𝒞.levelMap_sol 1 hv1]
  refine Prod.ext (𝒞.fixLvl_fixed 1 hv1) ?_
  show D (v, 𝒞.fixLvl 1 v) (b, 𝒞.Aop (D := D) 0 v b) = 𝒞.Aop (D := D) 0 v b
  have := 𝒞.Lop_Aop hC hB hv1 b
  rwa [Lop, levelDeriv_zero] at this

theorem next_sol_eq_tangentMapWith {s : ℕ} {q : P × P} (hq : q.1 ∈ 𝒞.N (2 + s) ∩ Ct) :
    (𝒞.next hC hB s).sol q = tangentMapWith 𝒞.sol (𝒞.solDeriv (D := D)) q := by
  obtain ⟨v, b⟩ := q
  rw [𝒞.next_sol hC hB hq]
  have hv1 : v ∈ 𝒞.N 1 ∩ Ct := ⟨𝒞.N_anti_le (by omega) hq.1, hq.2⟩
  have hv2 : v ∈ 𝒞.N 2 ∩ Ct := ⟨𝒞.N_anti_le (by omega) hq.1, hq.2⟩
  change _ = ((levelMap (E := ScBanach.const P) 𝒞.sol 1 v, 𝒞.solDeriv (D := D) v b) : W.tangent 0)
  rw [𝒞.levelMap_sol 1 hv1, 𝒞.solDeriv_of_mem hv2]

/-- **Lemma 3.3.4 (preprint 3.31)**, assembled: if `f` is sc^{k+1} with derivative family `D` and `δ` is sc^j on
`germ s`, then `f⁽¹⁾ = next s` is a contraction germ of class `sc^{min(k, j)}` whose solution germ
is `Tδ` on `(N(2+s) ∩ C̃) × P`. -/
theorem lemma_3_3_4 {k j s : ℕ} (hk : IsSckGerm (k + 1) 𝒞.G 𝒞.B)
    (hs : IsSckGerm j (𝒞.germ hC s) 𝒞.sol) :
    IsSckGerm (min k j) (𝒞.next hC hB s).G (𝒞.next hC hB s).B ∧
      ∀ q : P × P, q.1 ∈ 𝒞.N (2 + s) ∩ Ct →
        (𝒞.next hC hB s).sol q = tangentMapWith 𝒞.sol (𝒞.solDeriv (D := D)) q := by
  refine ⟨?_, fun q hq => 𝒞.next_sol_eq_tangentMapWith hC hB hq⟩
  have hTB : IsSckGerm (min k j) 𝒞.G.tangent (tangentMapWith 𝒞.B D) := by
    have h1 : IsSckGerm k 𝒞.G.tangent (tangentMapGerm 𝒞.G 𝒞.B) := hk.2
    have h2 := IsSckGerm.congr (hC.paramProd W).tangentSet
      (IsSc1Germ.tangentMapGerm_eqOn (hC.paramProd W) hB) h1
    exact h2.of_le (min_le_left _ _)
  exact 𝒞.nextB_isSckGerm hC hTB (hs.of_le (min_le_right _ _))

/-! ### Theorem 3.3.6 (preprint 3.33): the induction -/

/-- **The induction step of Theorem 3.3.6 (preprint 3.33)**: `δ` is sc¹ on `germ 1` (Theorem 3.3.3 (preprint 3.30)); if the solution
germ `Tδ` of `f⁽¹⁾ = next s` is sc^j on `(next s).germ s'`, then `δ` is sc^{j+1} on
`germ (s + s' + 1)`.  The germ of `Tδ` is transported from `P × P` to `T P` along the
sc-isomorphism `constTangentOp`. -/
theorem isSckGerm_succ_of_next {j s s' : ℕ}
    (hs' : IsSckGerm j ((𝒞.next hC hB s).germ hC.prod_univ_const s') (𝒞.next hC hB s).sol) :
    IsSckGerm (j + 1) (𝒞.germ hC (s + s' + 1)) 𝒞.sol := by
  have hCt : IsQuadrantLike (ScBanach.const P).tangent ((ScBanach.const P).tangentSet Ct) :=
    hC.tangentSet
  have hC' : IsQuadrantLike (ScBanach.const (P × P)) (Ct ×ˢ univ) := hC.prod_univ_const
  have h1 : IsSc1GermWith (𝒞.germ hC 1) 𝒞.sol (𝒞.solDeriv (D := D)) := 𝒞.isSc1GermWith_sol hC hB
  have hsub : ∀ m, (𝒞.germ hC (s + s' + 1)).U m ⊆ (𝒞.germ hC 1).U m :=
    𝒞.germ_U_subset hC (by omega)
  refine ⟨h1.isSc1Germ.mono hsub, ?_⟩
  have hmaps : (𝒞.germ hC (s + s' + 1)).tangent.MapsToGerm ((𝒞.next hC hB s).germ hC' s')
      (constTangentOp' P 0) := by
    intro m q hq
    rw [ScOperator.levelMap_eq, constTangentOp'_apply]
    have hq1 : q.1 ∈ 𝒞.N (m + 1 + (s + s' + 1)) ∩ Ct := hq.1
    exact ⟨⟨𝒞.N_anti_le (by omega) hq1.1, mem_univ _⟩, hq1.2, mem_univ _⟩
  have h2 : IsSckGerm j (𝒞.germ hC (s + s' + 1)).tangent
      ((𝒞.next hC hB s).sol ∘ constTangentOp' P 0) :=
    IsSckGerm.comp hCt hC' hs' ((constTangentOp' P).isSckGerm j _ hCt) hmaps
  have h3 : IsSckGerm j (𝒞.germ hC (s + s' + 1)).tangent (𝒞.next hC hB s).sol :=
    IsSckGerm.congr hCt (fun _ _ => rfl) h2
  refine IsSckGerm.congr hCt (fun q hq => ?_) h3
  have hq1 : q.1 ∈ 𝒞.N (1 + (s + s' + 1)) ∩ Ct := hq.1
  rw [𝒞.next_sol_eq_tangentMapWith hC hB (q := q) ⟨𝒞.N_anti_le (by omega) hq1.1, hq1.2⟩,
    ← IsSc1Germ.tangentMapGerm_eqOn hC h1
      (show q ∈ (𝒞.germ hC 1).tangent.U 0 from ⟨⟨𝒞.N_anti_le (by omega) hq1.1, hq1.2⟩, mem_univ _⟩)]
  exact (IsSc1Germ.tangentMapGerm_mono hC h1.isSc1Germ hsub hq).symm

end ContractionGerm

/-- **Lemma 3.3.5 (preprint 3.32) and the proof of Theorem 3.3.6 (preprint 3.33)**, as one induction on `j` over all contraction
germs: if the sc⁰-contraction germ `f = w − B(a, w)` is of class sc^k and `j ≤ k`, then its
solution germ `δ` is an sc^j-germ on `germ s` for some `s`.  Step `j → j + 1`: by the induction
hypothesis `δ` is sc^j on some `germ s`; `f⁽¹⁾ = next s` is a contraction germ of class sc^j
(Lemma 3.3.4 (preprint 3.31), `k − 1 ≥ j`) with solution germ `Tδ`, which is sc^j by the induction hypothesis
applied to `f⁽¹⁾` (a contraction germ on `(P × P) ⊕ TW`); `δ` is sc¹ by Theorem 3.3.3 (preprint 3.30); so `δ` is
sc^{j+1}. -/
theorem ContractionGerm.sol_isSckGerm : ∀ (j : ℕ) {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {W : ScBanach} {Ct : Set P} (𝒞 : ContractionGerm P Ct W)
    (hC : IsQuadrantLike (ScBanach.const P) Ct) {k : ℕ}, j ≤ k → IsSckGerm k 𝒞.G 𝒞.B →
    ∃ s, IsSckGerm j (𝒞.germ hC s) 𝒞.sol
  | 0, P, _, _, _, W, Ct, 𝒞, hC, _, _, _ => ⟨0, (theorem_3_3_2 𝒞 hC).1.isSc0⟩
  | j + 1, P, _, _, _, W, Ct, 𝒞, hC, k, hjk, hB => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hD : IsSc1GermWith 𝒞.G 𝒞.B (scDerivGerm 𝒞.G 𝒞.B) := hB.1.isSc1GermWith_scDerivGerm
    have hTB : IsSckGerm j 𝒞.G.tangent (tangentMapWith 𝒞.B (scDerivGerm 𝒞.G 𝒞.B)) :=
      (hB.2 : IsSckGerm k' 𝒞.G.tangent (tangentMapGerm 𝒞.G 𝒞.B)).of_le (by omega)
    obtain ⟨s, hs⟩ := ContractionGerm.sol_isSckGerm j 𝒞 hC (k := k' + 1) (by omega) hB
    have hB' : IsSckGerm j (𝒞.next hC hD s).G (𝒞.next hC hD s).B := 𝒞.nextB_isSckGerm hC hTB hs
    obtain ⟨s', hs'⟩ := ContractionGerm.sol_isSckGerm j (𝒞.next hC hD s) hC.prod_univ_const
      (k := j) le_rfl hB'
    exact ⟨s + s' + 1, 𝒞.isSckGerm_succ_of_next hC hD hs'⟩

namespace ContractionGerm

variable (𝒞 : ContractionGerm P Ct W) (hC : IsQuadrantLike (ScBanach.const P) Ct)

/-- **Theorem 3.3.6 (preprint 3.33) (Germ implicit function theorem)**: if the sc⁰-contraction germ
`f(a, w) = w − B(a, w)` is of class sc^k, its solution germ `δ` (Theorem 3.3.2 (preprint 3.29)) is of class sc^k
**on the shrunken germ `germ s = (N(m+s) ∩ C̃)_m` for some `s`** (see the module docstring: the
text's germs are up to shrinking).  The proof gives `s = 2^k − 1`: `sol_isSckGerm` returns `0` for
`j = 0` and `s + s' + 1` for `j + 1` (`isSckGerm_succ_of_next`), with `s` and `s'` both the shifts
of level `j`, so `s_{j+1} = 2s_j + 1`; the statement keeps the existential. -/
theorem _root_.Polyfold.theorem_3_3_6 {k : ℕ} (hB : IsSckGerm k 𝒞.G 𝒞.B) :
    ∃ s, 𝒞.IsSolutionGerm (𝒞.germ hC s) 𝒞.sol ∧ IsSckGerm k (𝒞.germ hC s) 𝒞.sol := by
  obtain ⟨s, hs⟩ := 𝒞.sol_isSckGerm k hC le_rfl hB
  exact ⟨s, 𝒞.isSolutionGerm_germ hC s, hs⟩

/-- The sc-smooth case of Theorem 3.3.6 (preprint 3.33) ("the solution germ is sc-smooth at the smooth point `0`",
Corollary 3.34): for every `k`, `δ` is sc^k on some `germ s` (depending on `k`).  For one germ on
which `δ` is sc^k for every `k`, see `corollary_3_3_7_isScSmoothGerm` (`GermIFTSmooth.lean`). -/
theorem _root_.Polyfold.theorem_3_3_6_smooth (hB : IsScSmoothGerm 𝒞.G 𝒞.B) (k : ℕ) :
    ∃ s, 𝒞.IsSolutionGerm (𝒞.germ hC s) 𝒞.sol ∧ IsSckGerm k (𝒞.germ hC s) 𝒞.sol :=
  theorem_3_3_6 𝒞 hC (hB k)

/-- The inclusions of the constant structure are the identity. -/
lemma _root_.Polyfold.ScBanach.const_inclK (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (m : ℕ) : ∀ (k : ℕ) (x : V), (ScBanach.const V).inclK m k x = x
  | 0, _ => rfl
  | k + 1, x => ScBanach.const_inclK V m k x

include hC in
/-- **Corollary 3.3.7 (preprint 3.34)**: if the sc⁰-contraction germ is sc-smooth, then for every `m` and `k` there
is a relatively open neighbourhood `V_{m,k}` of `0` in `C̃` with (1) `δ(V_{m,k}) ⊆ W_m` and (2)
`δ : V_{m,k} → W_m` of class `C^k` (Proposition 1.2.3 (preprint 1.18) for germs).  Here `V_{m,k} = N(m+k+s) ∩ C̃`
with `s` from Theorem 3.3.6 (preprint 3.33) for this `k`. -/
theorem _root_.Polyfold.corollary_3_3_7 (hB : IsScSmoothGerm 𝒞.G 𝒞.B) (m k : ℕ) :
    ∃ V : Set P, (∃ O : Set P, IsOpen O ∧ V = O ∩ Ct) ∧ (0 : P) ∈ V ∧
      (∀ a ∈ V, 𝒞.sol a ∈ range (W.toBase m)) ∧
      ContDiffOn ℝ k (levelMap (E := ScBanach.const P) (F := W) 𝒞.sol m) V := by
  obtain ⟨s, hsol, hs⟩ := theorem_3_3_6_smooth 𝒞 hC hB k
  refine ⟨(𝒞.germ hC s).U (m + k), ⟨𝒞.N (m + k + s), 𝒞.N_open _, rfl⟩, (𝒞.germ hC s).zero_mem _,
    fun a ha => ?_, ?_⟩
  · have := hsol.isSc0.mem_range m a ⟨𝒞.N_anti_le (by omega) ha.1, ha.2⟩
    rwa [ScBanach.const_toBase] at this
  · refine (hs.contDiffOn_levels hC m).congr fun a _ => ?_
    rw [Function.comp_apply, ScBanach.const_inclK]

/-- **Theorem 3.35**: for `C̃` a finite-dimensional partial quadrant in `P` (the text: in `ℝⁿ`), an
sc⁰-contraction germ of class sc^k has a solution germ of class sc^k (on some `germ s`). -/
theorem _root_.Polyfold.theorem_3_35_preprint (hC : IsPartialQuadrant (ScBanach.const P) Ct) {k : ℕ}
    (hB : IsSckGerm k 𝒞.G 𝒞.B) :
    ∃ s, 𝒞.IsSolutionGerm (𝒞.germ hC.isQuadrantLike s) 𝒞.sol ∧
      IsSckGerm k (𝒞.germ hC.isQuadrantLike s) 𝒞.sol :=
  theorem_3_3_6 𝒞 hC.isQuadrantLike hB

/-- **Theorem 3.35**, second sentence: if `f` is sc-smooth, so is `δ` (for every `k`, sc^k on
some `germ s` depending on `k`; see the module docstring).  On one germ for all `k`:
`theorem_3_35_isScSmoothGerm_preprint` (`GermIFTSmooth.lean`). -/
theorem _root_.Polyfold.theorem_3_35_smooth_preprint (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (hB : IsScSmoothGerm 𝒞.G 𝒞.B) (k : ℕ) :
    ∃ s, 𝒞.IsSolutionGerm (𝒞.germ hC.isQuadrantLike s) 𝒞.sol ∧
      IsSckGerm k (𝒞.germ hC.isQuadrantLike s) 𝒞.sol :=
  theorem_3_3_6 𝒞 hC.isQuadrantLike (hB k)

end ContractionGerm

/-! ### From Definition 3.3.1 (preprint 3.28) (balls) to the working form -/

namespace IsSc0ContractionGerm

variable {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
  (h : IsSc0ContractionGerm Ct G B)

/-- A radius `r m > 0` with the `1/2`-contraction on `{‖a‖ < r m} × {‖w‖ < r m}` on level `m`. -/
def rad (m : ℕ) : ℝ := (h.contraction (1 / 2) (by norm_num) m).choose

lemma rad_pos (m : ℕ) : 0 < h.rad m := (h.contraction (1 / 2) (by norm_num) m).choose_spec.1

lemma rad_spec (m : ℕ) : ∀ a ∈ Ct, ‖a‖ < h.rad m → ∀ w w' : W m, ‖w‖ < h.rad m → ‖w'‖ < h.rad m →
    ((a, w) : P × W m) ∈ G.U m ∧ ‖levelB B m (a, w) - levelB B m (a, w')‖ ≤ 1 / 2 * ‖w - w'‖ :=
  (h.contraction (1 / 2) (by norm_num) m).choose_spec.2

include h in
/-- Radii `r' m ≤ r m`, decreasing fast enough for `K_{m+1} → K_m`. -/
def rad' : ℕ → ℝ
  | 0 => h.rad 0
  | m + 1 => min (h.rad (m + 1)) (rad' m / (‖W.incl m‖ + 1))

lemma rad'_pos : ∀ m, 0 < h.rad' m
  | 0 => h.rad_pos 0
  | m + 1 => lt_min (h.rad_pos _) (div_pos (rad'_pos m) (by positivity))

lemma rad'_le : ∀ m, h.rad' m ≤ h.rad m
  | 0 => le_rfl
  | _ + 1 => min_le_left _ _

lemma norm_incl_le_of_le {m : ℕ} {w : W (m + 1)} (hw : ‖w‖ ≤ h.rad' (m + 1) / 2) :
    ‖W.incl m w‖ ≤ h.rad' m / 2 := by
  have h1 : h.rad' (m + 1) ≤ h.rad' m / (‖W.incl m‖ + 1) := min_le_right _ _
  calc ‖W.incl m w‖ ≤ ‖W.incl m‖ * ‖w‖ := (W.incl m).le_opNorm w
    _ ≤ (‖W.incl m‖ + 1) * (h.rad' m / (‖W.incl m‖ + 1) / 2) := by
        gcongr
        · linarith [norm_nonneg (W.incl m)]
        · exact hw.trans (by gcongr)
    _ = h.rad' m / 2 := by field_simp

include h in
/-- `B_m(0) = 0`. -/
lemma levelB_zero_eq (m : ℕ) :
    levelMap (E := ScBanach.paramProd P W) (F := W) B m (0 : (ScBanach.paramProd P W) m) = 0 := by
  apply levelMap_eq_of_toBase_eq
  rw [map_zero, map_zero]
  exact h.B_zero.symm

/-- The radius of continuity of `B_m` at `0`: `‖B_m(a, w)‖ < r' m / 4` on `G.U m ∩ ball 0 (ρ₀ m)`. -/
lemma exists_cont_rad (m : ℕ) : ∃ ρ > 0, ∀ x ∈ G.U m, ‖x‖ < ρ → ‖levelB B m x‖ < h.rad' m / 4 := by
  have hc := h.isSc0.continuousOn m 0 (G.zero_mem m)
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨ρ, hρ, hρ'⟩ := hc (h.rad' m / 4) (by have := h.rad'_pos m; positivity)
  refine ⟨ρ, hρ, fun x hx hxρ => ?_⟩
  have := hρ' hx (by rwa [dist_zero_right])
  rwa [dist_eq_norm, h.levelB_zero_eq, sub_zero] at this

include h in
def contRad (m : ℕ) : ℝ := (h.exists_cont_rad m).choose

lemma contRad_pos (m : ℕ) : 0 < h.contRad m := (h.exists_cont_rad m).choose_spec.1

lemma contRad_spec (m : ℕ) : ∀ x ∈ G.U m, ‖x‖ < h.contRad m → ‖levelB B m x‖ < h.rad' m / 4 :=
  (h.exists_cont_rad m).choose_spec.2

include h in
/-- The decreasing parameter radii `ρ m ≤ min (ρ₀ m) (r' m)`. -/
def prad : ℕ → ℝ
  | 0 => min (h.contRad 0) (h.rad' 0)
  | m + 1 => min (prad m) (min (h.contRad (m + 1)) (h.rad' (m + 1)))

lemma prad_pos : ∀ m, 0 < h.prad m
  | 0 => lt_min (h.contRad_pos 0) (h.rad'_pos 0)
  | m + 1 => lt_min (prad_pos m) (lt_min (h.contRad_pos _) (h.rad'_pos _))

lemma prad_le_contRad : ∀ m, h.prad m ≤ h.contRad m
  | 0 => min_le_left _ _
  | _ + 1 => (min_le_right _ _).trans (min_le_left _ _)

lemma prad_le_rad' : ∀ m, h.prad m ≤ h.rad' m
  | 0 => min_le_right _ _
  | _ + 1 => (min_le_right _ _).trans (min_le_right _ _)

lemma prad_anti (m : ℕ) : h.prad (m + 1) ≤ h.prad m := min_le_left _ _

/-- **The working form of Definition 3.3.1 (preprint 3.28)** (the construction in the proof of Theorem 3.29): the
regions `N m = ball 0 (ρ m)`, `O m = ball 0 (r' m)`, `K m = closedBall 0 (r' m / 2)`. -/
def toContractionGerm : ContractionGerm P Ct W where
  B := B
  G := G
  B_zero := h.B_zero
  isSc0 := h.isSc0
  N m := Metric.ball 0 (h.prad m)
  N_open _ := Metric.isOpen_ball
  N_zero m := Metric.mem_ball_self (h.prad_pos m)
  N_anti m := Metric.ball_subset_ball (h.prad_anti m)
  O m := Metric.ball 0 (h.rad' m)
  K m := Metric.closedBall 0 (h.rad' m / 2)
  O_open _ := Metric.isOpen_ball
  K_closed _ := Metric.isClosed_closedBall
  K_zero m := Metric.mem_closedBall_self (by have := h.rad'_pos m; positivity)
  K_sub m := Metric.closedBall_subset_ball (by have := h.rad'_pos m; linarith)
  K_incl m w hw := by
    rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
    exact h.norm_incl_le_of_le hw
  mem_G m a ha w hw := by
    rw [Metric.mem_ball, dist_zero_right] at hw
    have ha' : ‖a‖ < h.rad m := by
      have := ha.1; rw [Metric.mem_ball, dist_zero_right] at this
      exact this.trans_le ((h.prad_le_rad' m).trans (h.rad'_le m))
    exact (h.rad_spec m a ha.2 ha' w w (hw.trans_le (h.rad'_le m)) (hw.trans_le (h.rad'_le m))).1
  mapsTo m a ha w hw := by
    rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
    have haρ : ‖a‖ < h.prad m := by have := ha.1; rwa [Metric.mem_ball, dist_zero_right] at this
    have ha' : ‖a‖ < h.rad m := haρ.trans_le ((h.prad_le_rad' m).trans (h.rad'_le m))
    have hw' : ‖w‖ < h.rad m := by
      have := h.rad'_pos m
      exact (hw.trans_lt (by linarith)).trans_le (h.rad'_le m)
    have h0 : ‖(0 : W m)‖ < h.rad m := by rw [norm_zero]; exact h.rad_pos m
    obtain ⟨hmem, hcontr⟩ := h.rad_spec m a ha.2 ha' w 0 hw' h0
    have hB0 : ‖levelB B m (a, 0)‖ < h.rad' m / 4 := by
      refine h.contRad_spec m _ (h.rad_spec m a ha.2 ha' 0 0 h0 h0).1 ?_
      rw [Prod.norm_def, norm_zero]
      exact (max_eq_left (norm_nonneg a)).le.trans_lt (haρ.trans_le (h.prad_le_contRad m))
    rw [sub_zero] at hcontr
    calc ‖levelB B m (a, w)‖ ≤ ‖levelB B m (a, w) - levelB B m (a, 0)‖ + ‖levelB B m (a, 0)‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ 1 / 2 * ‖w‖ + h.rad' m / 4 := by linarith
      _ ≤ h.rad' m / 2 := by linarith
  contr m a ha w hw w' hw' := by
    rw [Metric.mem_ball, dist_zero_right] at hw hw'
    have ha' : ‖a‖ < h.rad m := by
      have := ha.1; rw [Metric.mem_ball, dist_zero_right] at this
      exact this.trans_le ((h.prad_le_rad' m).trans (h.rad'_le m))
    exact (h.rad_spec m a ha.2 ha' w w' (hw.trans_le (h.rad'_le m)) (hw'.trans_le (h.rad'_le m))).2

@[simp] lemma toContractionGerm_B : h.toContractionGerm.B = B := rfl
@[simp] lemma toContractionGerm_G : h.toContractionGerm.G = G := rfl

end IsSc0ContractionGerm

/-- **Theorem 3.3.2 (preprint 3.29) in the text's form** (from Definition 3.3.1 (preprint 3.28) with balls): an sc⁰-contraction
germ admits an sc⁰-solution germ `δ : O(C̃, 0) → (W, 0)`, `δ(0) = 0`, `(a, δ(a)) ∈ U_m` for
`a ∈ V_m`, `f(a, δ(a)) = 0` on `V₀`, uniquely determined among the solutions `w` with `‖w‖ < r`
for `a ∈ V₀`. -/
theorem theorem_3_3_2_of_isSc0ContractionGerm (hC : IsQuadrantLike (ScBanach.const P) Ct)
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
    (h : IsSc0ContractionGerm Ct G B) :
    ∃ (V : ScNbhdGerm (ScBanach.const P) Ct) (δ : P → W 0), IsSc0Germ V δ ∧ δ 0 = 0 ∧
      (∀ m, ∀ a ∈ V.U m, ((a, levelMap (E := ScBanach.const P) δ m a) : P × W m) ∈ G.U m) ∧
      (∀ a ∈ V.U 0, contractionMap B (a, δ a) = 0) ∧
      ∃ r > 0, ∀ a ∈ V.U 0, ∀ w : W 0, ‖w‖ < r → contractionMap B (a, w) = 0 → w = δ a := by
  set 𝒞 := h.toContractionGerm
  obtain ⟨hsol, huniq⟩ := theorem_3_3_2 𝒞 hC
  refine ⟨𝒞.germ hC 0, 𝒞.sol, hsol.isSc0, hsol.zero, hsol.mem_G, fun a ha => ?_,
    h.rad' 0, h.rad'_pos 0, fun a ha w hw hfix => ?_⟩
  · show 𝒞.sol a - B (a, 𝒞.sol a) = 0
    exact sub_eq_zero.2 (hsol.fixed a ha).symm
  · refine huniq a ha w ?_ ?_
    · rw [ContractionGerm.germ_U] at ha
      show w ∈ Metric.ball (0 : W 0) (h.rad' 0)
      rwa [Metric.mem_ball, dist_zero_right]
    · have : w - B (a, w) = 0 := hfix
      exact (sub_eq_zero.1 this).symm

/-- **Theorem 3.3.6 (preprint 3.33) in the text's form** (from Definition 3.3.1 (preprint 3.28) with balls): if the sc⁰-contraction
germ is of class sc^k, there is a solution germ `δ : O(C̃, 0) → (W, 0)` of class sc^k. -/
theorem theorem_3_3_6_of_isSc0ContractionGerm (hC : IsQuadrantLike (ScBanach.const P) Ct)
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
    (h : IsSc0ContractionGerm Ct G B) {k : ℕ} (hB : IsSckGerm k G B) :
    ∃ (V : ScNbhdGerm (ScBanach.const P) Ct) (δ : P → W 0), IsSckGerm k V δ ∧ δ 0 = 0 ∧
      (∀ m, ∀ a ∈ V.U m, ((a, levelMap (E := ScBanach.const P) δ m a) : P × W m) ∈ G.U m) ∧
      ∀ a ∈ V.U 0, contractionMap B (a, δ a) = 0 := by
  obtain ⟨s, hsol, hs⟩ := theorem_3_3_6 h.toContractionGerm hC hB
  refine ⟨_, _, hs, hsol.zero, hsol.mem_G, fun a ha => ?_⟩
  show h.toContractionGerm.sol a - B (a, h.toContractionGerm.sol a) = 0
  rw [sub_eq_zero]
  exact (hsol.fixed a ha).symm

end Polyfold
