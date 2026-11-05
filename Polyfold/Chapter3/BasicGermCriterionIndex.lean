import Polyfold.Chapter3.BasicGermCriterionProof

/-!
# The basic germ criterion (Theorem 3.58): the family `L(b)` from conditions (1) and (2)

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I*, §3.7, **Theorem 3.58** (basic germ
criterion), first half of the proof: from the sc-Fredholm property (1) of the linearizations
`Df(b, 0)` with constant index and the compactness property (2), the operators
`L(b) = P ∘ Df(b, 0)|X : X → Y` are sc-isomorphisms for `b` near `0` with uniform lower bounds
`|L(b)h|_m ≥ c_m|h|_m` (Lemmas 3.59, 3.60 and the index argument "`P ∘ Df(b)|X` is an injective
sc-Fredholm operator of index `0`, hence an sc-isomorphism").  Together with
`theorem_3_58_of_family` (`BasicGermCriterionProof.lean`) this gives **`Polyfold.theorem_3_58`**.

## Main results

* `Polyfold.exists_bound_of_continuousOn_clm`: a jointly continuous family of operators is
  uniformly bounded near a parameter.
* `Polyfold.fredholmIndex_block`, `Polyfold.surjective_of_fredholmIndex_block`: for a Fredholm
  operator `T : P ⊕ X → Q ⊕ Y` with `P`, `Q` finite-dimensional, `ind T = dim P + ind L − dim Q`
  for the block `L = pr_Y ∘ T ∘ inr_X`, and an injective `L` is surjective when
  `ind T = dim P − dim Q`.
* `Polyfold.derivParamOp` (`Df(b, 0)` as an sc-operator), `Polyfold.derivFamOp` (the family
  `L(b)`), `Polyfold.CompactnessCondition` (condition (2)),
  `Polyfold.familyCompactness_derivFamOp` (the compactness property `FamilyCompactness` of the
  family from (2), Finding 73).
* `Polyfold.theorem_3_58`: **Theorem 3.58** in the coordinates `E = ℝⁿ ⊕ X`, `F = ℝᴺ ⊕ Y`.

## Remarks on the text

* Condition (1) is used only at the points `(b, 0)`, `b ∈ C̃`, and only through the index on the
  levels (`IsScFredholm.fredholmIndex_lvl`); it is stated for these points.
* The text's "`P ∘ Df(b)|X` is an injective sc-Fredholm operator of index `0`" is here the block
  computation `ind Df(b, 0) = dim ℝⁿ + ind L(b) − dim ℝᴺ` on every level
  (`fredholmIndex_block`): `Df(b, 0)` differs from `inr ∘ L(b) ∘ pr_X` by a finite-rank operator,
  and `ind Df(0) = dim ℝⁿ − dim ℝᴺ` because `L(0)` is bijective (condition (2), `B ⊇ ker Df(0)`
  and `Y = Df(0)X`).  The sc-Fredholm property of `P` and the composition rule for sc-Fredholm
  operators are not needed.
* In Lemma 3.59 the text takes `z_j = Df(b_j)h_j ∈ A` "bounded on every level since `A` is a smooth
  subspace"; the boundedness of the `A`-component uses a uniform bound on `Df(b_j, 0)(0, ·)` for `j`
  large, from the joint continuity of `(b, h) ↦ Df(b, 0)(0, h)` (`exists_bound_of_continuousOn_clm`),
  and condition (2) is applied to the tail of the sequences.  In Lemma 3.60 the text writes
  `Df(b_j)h_j = P ∘ Df(b_j)h_j`, omitting the bounded `A`-component.
* The smallness of `b` in condition (2) is read as uniform in the level `m` (`∃ r > 0, ∀ m, …`), as
  the order of the quantifiers in the text suggests; Lemma 3.60 needs the compactness property on
  every level on one fixed neighbourhood.
-/

open Set Filter Topology Function Metric Module

noncomputable section

namespace Polyfold

/-! ### A uniform operator bound from joint continuity -/

/-- **A uniform bound from joint continuity**: if `(b, v) ↦ Φ(b)v` is continuous on `s × V` for a
family of continuous linear maps `Φ(b)`, then `‖Φ(b)v‖ ≤ M‖v‖` with a single `M` for all `b ∈ s`
near `b₀`.  (Continuity at `(b₀, 0)` with `ε = 1` on the ball of radius `δ/2`, then scaling.) -/
theorem exists_bound_of_continuousOn_clm {B V W : Type*} [PseudoMetricSpace B]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : B → V →L[ℝ] W} {s : Set B} (hΦ : ContinuousOn (fun p : B × V => Φ p.1 p.2) (s ×ˢ univ))
    {b₀ : B} (hb₀ : b₀ ∈ s) : ∃ M : ℝ, ∀ᶠ b in 𝓝[s] b₀, ∀ v, ‖Φ b v‖ ≤ M * ‖v‖ := by
  have hc := hΦ (b₀, 0) ⟨hb₀, mem_univ _⟩
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc 1 one_pos
  refine ⟨2 / δ, ?_⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun b hbd hbs v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set v' : V := (δ / (2 * ‖v‖)) • v with hv'
  have hv'n : ‖v'‖ = δ / 2 := by
    rw [hv', norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hdist : dist ((b, v') : B × V) (b₀, 0) < δ := by
    rw [Prod.dist_eq, dist_zero_right, hv'n]
    exact max_lt hbd (by linarith)
  have h1 := hδ' ⟨hbs, mem_univ _⟩ hdist
  simp only [map_zero, dist_zero_right] at h1
  have h2 : Φ b v' = (δ / (2 * ‖v‖)) • Φ b v := by rw [hv', map_smul]
  rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
  have h3 : δ / (2 * ‖v‖) * ‖Φ b v‖ ≤ 1 := h1.le
  calc ‖Φ b v‖ = (2 * ‖v‖ / δ) * (δ / (2 * ‖v‖) * ‖Φ b v‖) := by field_simp
    _ ≤ (2 * ‖v‖ / δ) * 1 := by gcongr
    _ = 2 / δ * ‖v‖ := by ring

/-! ### The index of the block operators -/

section BlockIndex

variable {P Q V W : Type*} [AddCommGroup P] [Module ℝ P] [FiniteDimensional ℝ P]
  [AddCommGroup Q] [Module ℝ Q] [FiniteDimensional ℝ Q] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- `pr₂ : P ⊕ V → V` has finite index `dim P`. -/
theorem hasFiniteIndex_snd_and_linIndex :
    HasFiniteIndex (LinearMap.snd ℝ P V) ∧ linIndex (LinearMap.snd ℝ P V) = finrank ℝ P := by
  have hker : finrank ℝ (LinearMap.ker (LinearMap.snd ℝ P V)) = finrank ℝ P := by
    rw [LinearMap.ker_snd, LinearMap.finrank_range_of_inj LinearMap.inl_injective]
  have hrange : LinearMap.range (LinearMap.snd ℝ P V) = ⊤ :=
    LinearMap.range_eq_top.2 Prod.snd_surjective
  have hsub : Subsingleton (V ⧸ LinearMap.range (LinearMap.snd ℝ P V)) := by
    rw [hrange]; exact Submodule.Quotient.subsingleton_iff.2 rfl
  have hkerfin : FiniteDimensional ℝ (LinearMap.ker (LinearMap.snd ℝ P V)) := by
    rw [LinearMap.ker_snd]; infer_instance
  have : Finite (V ⧸ LinearMap.range (LinearMap.snd ℝ P V)) := Finite.of_subsingleton
  have h2 : finrank ℝ (V ⧸ LinearMap.range (LinearMap.snd ℝ P V)) = 0 :=
    finrank_zero_of_subsingleton
  refine ⟨⟨hkerfin, Module.Finite.of_finite⟩, ?_⟩
  unfold linIndex
  rw [hker, h2, Nat.cast_zero, sub_zero]

/-- `inr : W → Q ⊕ W` has finite index `−dim Q`. -/
theorem hasFiniteIndex_inr_and_linIndex :
    HasFiniteIndex (LinearMap.inr ℝ Q W) ∧ linIndex (LinearMap.inr ℝ Q W) = -finrank ℝ Q := by
  have hker : LinearMap.ker (LinearMap.inr ℝ Q W) = ⊥ := LinearMap.ker_eq_bot.2 LinearMap.inr_injective
  have e : ((Q × W) ⧸ LinearMap.range (LinearMap.inr ℝ Q W)) ≃ₗ[ℝ] Q :=
    (Submodule.quotEquivOfEq _ _ (LinearMap.range_inr ℝ Q W)).trans
      (LinearMap.quotKerEquivOfSurjective (LinearMap.fst ℝ Q W) Prod.fst_surjective)
  have hcoker : FiniteDimensional ℝ ((Q × W) ⧸ LinearMap.range (LinearMap.inr ℝ Q W)) :=
    e.symm.finiteDimensional
  refine ⟨⟨by rw [hker]; infer_instance, hcoker⟩, ?_⟩
  unfold linIndex
  rw [hker, finrank_bot, e.finrank_eq, Nat.cast_zero, zero_sub]

end BlockIndex

section BlockBanach

variable {P Q X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- **The index of a block operator**: let `T : P ⊕ X → Q ⊕ Y` be Fredholm with `P`, `Q`
finite-dimensional, and `L : X → Y` the block `pr_Y ∘ T ∘ inr_X`, assumed of finite index.  Then
`ind T = dim P + ind L − dim Q`: `T` differs from `inr_Y ∘ L ∘ pr_X` by the finite-rank operator
`(p, x) ↦ T(p, 0) + (pr_Q T(0, x), 0)`, which does not change the index (Kato IV.5.26). -/
theorem fredholmIndex_block (T : P × X →L[ℝ] Q × Y) (hT : T.IsFredholm) (L : X →L[ℝ] Y)
    (hL : ∀ x, (T (0, x)).2 = L x) (hLfin : HasFiniteIndex (L : X →ₗ[ℝ] Y)) :
    fredholmIndex T = finrank ℝ P + linIndex (L : X →ₗ[ℝ] Y) - finrank ℝ Q := by
  set Td : P × X →L[ℝ] Q × Y :=
    (ContinuousLinearMap.inr ℝ Q Y).comp (L.comp (ContinuousLinearMap.snd ℝ P X)) with hTd
  set Kb : P × X →L[ℝ] Q × Y := T - Td with hKb
  -- `Kb` has finite-dimensional range
  have hKbrange : LinearMap.range (Kb : P × X →ₗ[ℝ] Q × Y) ≤
      LinearMap.range ((T : P × X →ₗ[ℝ] Q × Y).comp (LinearMap.inl ℝ P X)) ⊔
        LinearMap.range (LinearMap.inl ℝ Q Y) := by
    rintro _ ⟨⟨p, x⟩, rfl⟩
    refine Submodule.mem_sup.2 ⟨T (p, 0), ⟨p, rfl⟩, ((T (0, x)).1, 0), ⟨(T (0, x)).1, rfl⟩, ?_⟩
    have e1 : ((p, x) : P × X) = (p, 0) + (0, x) := by simp
    change T (p, 0) + ((T (0, x)).1, (0 : Y)) = T (p, x) - ((0 : Q), L x)
    rw [← hL x, e1, map_add]
    ext <;> simp
  have : FiniteDimensional ℝ (LinearMap.range (Kb : P × X →ₗ[ℝ] Q × Y)) :=
    Submodule.finiteDimensional_of_le hKbrange
  have hKbc : IsCompactOperator Kb := isCompactOperator_of_finiteDimensional_range Kb
  have hTdeq : Td = T + (-Kb) := by rw [hKb]; abel
  have hTdF : Td.IsFredholm := by rw [hTdeq]; exact isFredholm_add_isCompactOperator hT hKbc.neg
  have hind : fredholmIndex Td = fredholmIndex T := by
    rw [hTdeq]; exact fredholmIndex_add_isCompactOperator hT hKbc.neg
  -- the index of `Td = inr ∘ L ∘ snd`
  have hTdlin : (Td : P × X →ₗ[ℝ] Q × Y) =
      (LinearMap.inr ℝ Q Y).comp ((L : X →ₗ[ℝ] Y).comp (LinearMap.snd ℝ P X)) := rfl
  obtain ⟨hsndF, hsndI⟩ := hasFiniteIndex_snd_and_linIndex (P := P) (V := X)
  obtain ⟨hinrF, hinrI⟩ := hasFiniteIndex_inr_and_linIndex (Q := Q) (W := Y)
  have h1 := linIndex_comp hsndF hLfin
  have h2 := linIndex_comp (hsndF.comp hLfin) hinrF
  rw [← hind]
  unfold fredholmIndex
  rw [hTdlin, h2, h1, hsndI, hinrI]
  ring

/-- **Surjectivity from the index**: if `T : P ⊕ X → Q ⊕ Y` is Fredholm of index `dim P − dim Q`
and the block `L = pr_Y ∘ T ∘ inr_X : X → Y` is injective, then `L` is surjective (it has index
`0`).  The finite index of `L` comes from that of `inr_Y ∘ L ∘ pr_X`, a compact perturbation of
`T`. -/
theorem surjective_of_fredholmIndex_block (T : P × X →L[ℝ] Q × Y) (hT : T.IsFredholm)
    (hind : fredholmIndex T = finrank ℝ P - finrank ℝ Q) (L : X →L[ℝ] Y)
    (hL : ∀ x, (T (0, x)).2 = L x) (hLinj : Injective L) : Surjective L := by
  set Td : P × X →L[ℝ] Q × Y :=
    (ContinuousLinearMap.inr ℝ Q Y).comp (L.comp (ContinuousLinearMap.snd ℝ P X)) with hTd
  set Kb : P × X →L[ℝ] Q × Y := T - Td with hKb
  have hKbrange : LinearMap.range (Kb : P × X →ₗ[ℝ] Q × Y) ≤
      LinearMap.range ((T : P × X →ₗ[ℝ] Q × Y).comp (LinearMap.inl ℝ P X)) ⊔
        LinearMap.range (LinearMap.inl ℝ Q Y) := by
    rintro _ ⟨⟨p, x⟩, rfl⟩
    refine Submodule.mem_sup.2 ⟨T (p, 0), ⟨p, rfl⟩, ((T (0, x)).1, 0), ⟨(T (0, x)).1, rfl⟩, ?_⟩
    have e1 : ((p, x) : P × X) = (p, 0) + (0, x) := by simp
    change T (p, 0) + ((T (0, x)).1, (0 : Y)) = T (p, x) - ((0 : Q), L x)
    rw [← hL x, e1, map_add]
    ext <;> simp
  have : FiniteDimensional ℝ (LinearMap.range (Kb : P × X →ₗ[ℝ] Q × Y)) :=
    Submodule.finiteDimensional_of_le hKbrange
  have hKbc : IsCompactOperator Kb := isCompactOperator_of_finiteDimensional_range Kb
  have hTdeq : Td = T + (-Kb) := by rw [hKb]; abel
  have hTdF : Td.IsFredholm := by rw [hTdeq]; exact isFredholm_add_isCompactOperator hT hKbc.neg
  -- `L` has finite index: trivial kernel, and `Y / range L` is a quotient of `(Q ⊕ Y) / range Td`
  have hLker : LinearMap.ker (L : X →ₗ[ℝ] Y) = ⊥ := LinearMap.ker_eq_bot.2 hLinj
  have hle : LinearMap.range (Td : P × X →ₗ[ℝ] Q × Y) ≤
      Submodule.comap (LinearMap.snd ℝ Q Y) (LinearMap.range (L : X →ₗ[ℝ] Y)) := by
    rintro _ ⟨⟨p, x⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hsurj : Surjective (Submodule.mapQ _ _ (LinearMap.snd ℝ Q Y) hle) := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
    exact ⟨Submodule.Quotient.mk ((0 : Q), y), by rw [Submodule.mapQ_apply]; rfl⟩
  have := hTdF.finite_coker
  have hLcoker : FiniteDimensional ℝ (Y ⧸ LinearMap.range (L : X →ₗ[ℝ] Y)) :=
    Module.Finite.of_surjective _ hsurj
  have hLfin : HasFiniteIndex (L : X →ₗ[ℝ] Y) := ⟨by rw [hLker]; infer_instance, hLcoker⟩
  have hblock := fredholmIndex_block T hT L hL hLfin
  have hLind : linIndex (L : X →ₗ[ℝ] Y) = 0 := by rw [hblock] at hind; omega
  unfold linIndex at hLind
  rw [hLker, finrank_bot, Nat.cast_zero, zero_sub, neg_eq_zero, Nat.cast_eq_zero,
    Module.finrank_zero_iff, Submodule.Quotient.subsingleton_iff] at hLind
  exact LinearMap.range_eq_top.1 hLind

end BlockBanach

/-! ### The family `L(b) = P ∘ Df(b, 0)|X` as sc-operators -/

section Family

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] {X Y : ScBanach} {Ct : Set P}

local notation "𝔼" => ScBanach.paramProd P X
local notation "𝔽" => ScBanach.paramProd Q Y

variable {U : Set ((ScBanach.paramProd P X) 0)}
  {f : (ScBanach.paramProd P X) 0 → (ScBanach.paramProd Q Y) 0}

/-- `(b, 0) ∈ U_m` for every level `m` when `(b, 0) ∈ U`. -/
lemma mem_lvlSet_param {b : P} (hb : ((b, 0) : 𝔼 0) ∈ U) (m : ℕ) :
    ((b, 0) : P × X m) ∈ (𝔼).lvlSet U m := by
  rw [ScBanach.mem_lvlSet, ScBanach.paramProd_toBase, map_zero]; exact hb

/-- `(b, 0)` is a smooth point. -/
lemma param_mem_smoothLvl (b : P) : ((b, 0) : P × X 1) ∈ (𝔼).smoothLvl 1 := by
  rw [ScScale.mem_smoothLvl_iff]
  intro j
  exact ⟨((b, 0) : P × X j), by rw [ScBanach.paramProd_toBase, ScBanach.paramProd_toBase, map_zero,
    map_zero]⟩

/-- **The linearization `Df(b, 0) : E → F` at the smooth point `(b, 0)` as an sc-operator** (the
remark after Proposition 1.16, `IsSc1With.scOperator_deriv`). -/
def derivParamOp (hf : IsScSmooth U f) (b : P) (hb : ((b, 0) : 𝔼 0) ∈ U) : ScOperator 𝔼 𝔽 :=
  (hf.isSc1.isSc1With_scDeriv.scOperator_deriv (mem_lvlSet_param hb 1) (param_mem_smoothLvl b)).toScOperator

lemma derivParamOp_zero (hf : IsScSmooth U f) (b : P) (hb : ((b, 0) : 𝔼 0) ∈ U) :
    derivParamOp hf b hb 0 = scDeriv (E := 𝔼) (F := 𝔽) U f ((b, 0) : P × X 1) :=
  IsScOperator.toScOperator_zero _

/-- The level maps of `Df(b, 0)` are the level operators `Df(b, 0) : E_m → F_m`. -/
lemma derivParamOp_lvl (hf : IsScSmooth U f) (b : P) (hb : ((b, 0) : 𝔼 0) ∈ U) (m : ℕ) :
    derivParamOp hf b hb m = levelDeriv (scDeriv (E := 𝔼) (F := 𝔽) U f) m ((b, 0) : P × X (m + 1)) := by
  refine ContinuousLinearMap.ext fun v => (𝔽).toBase_injective m ?_
  rw [(derivParamOp hf b hb).toBase_comm, derivParamOp_zero,
    hf.isSc1.isSc1With_scDeriv.toBase_levelDeriv (mem_lvlSet_param hb (m + 1)),
    ScBanach.paramProd_shift_toBase, map_zero]

open scoped Classical in
/-- **The family `L(b) = P ∘ Df(b, 0)|X : X → Y`** of the proof of Theorem 3.58, as sc-operators
(the zero operator where `(b, 0) ∉ U`). -/
def derivFamOp (hf : IsScSmooth U f) (b : P) : ScOperator X Y :=
  if hb : ((b, 0) : 𝔼 0) ∈ U then
    (ScBanach.sndOp (ScBanach.const Q) Y).comp ((derivParamOp hf b hb).comp (ScBanach.inrOp P X))
  else ScOperator.zero X Y

lemma derivFamOp_apply (hf : IsScSmooth U f) {b : P} (hb : ((b, 0) : 𝔼 0) ∈ U) (m : ℕ) (h : X m) :
    derivFamOp hf b m h =
      (levelDeriv (scDeriv (E := 𝔼) (F := 𝔽) U f) m ((b, 0) : P × X (m + 1)) ((0 : P), h)).2 := by
  rw [derivFamOp, dif_pos hb]
  show (derivParamOp hf b hb m ((0 : P), h)).2 = _
  rw [derivParamOp_lvl]

/-- The level-`m` operators `Df(b, 0)(0, ·) : X_m → F_m` depend jointly continuously on `(b, h)`
(Proposition 1.16 (2)). -/
lemma continuousOn_levelDeriv_param (hf : IsScSmooth U f) {O : Set P}
    (hOU : ∀ b ∈ O, ((b, 0) : 𝔼 0) ∈ U) (m : ℕ) :
    ContinuousOn (fun p : P × X m =>
      levelDeriv (scDeriv (E := 𝔼) (F := 𝔽) U f) m ((p.1, 0) : P × X (m + 1)) ((0 : P), p.2))
      (O ×ˢ univ) := by
  have h1 := hf.isSc1.isSc1With_scDeriv.continuousOn_levelDeriv m
  set J : P × X m → (𝔼) (m + 1) × (𝔼) m :=
    fun p => ((((p.1, 0) : P × X (m + 1)), ((0 : P), p.2)) : (𝔼) (m + 1) × (𝔼) m) with hJ
  have hj : Continuous J :=
    (continuous_fst.prodMk continuous_const).prodMk (continuous_const.prodMk continuous_snd)
  have hmaps : MapsTo J (O ×ˢ univ) ((𝔼).lvlSet U (m + 1) ×ˢ univ) :=
    fun p hp => ⟨mem_lvlSet_param (hOU p.1 hp.1) (m + 1), mem_univ _⟩
  have h2 := h1.comp hj.continuousOn hmaps
  exact h2

/-- `(b, h) ↦ L(b)h` is jointly continuous on `O × X_m`. -/
lemma continuousOn_derivFamOp (hf : IsScSmooth U f) {O : Set P}
    (hOU : ∀ b ∈ O, ((b, 0) : 𝔼 0) ∈ U) (m : ℕ) :
    ContinuousOn (fun p : P × X m => derivFamOp hf p.1 m p.2) (O ×ˢ univ) := by
  have := continuous_snd.comp_continuousOn (continuousOn_levelDeriv_param hf hOU m)
  exact this.congr fun p hp => by
    rw [Function.comp_apply, derivFamOp_apply hf (hOU p.1 hp.1)]

variable (Ct) in
/-- **Condition (2) of Theorem 3.58, the compactness property**, in coordinates: there is `r > 0`
such that for every level `m`, if `b_j → b` in `C̃ ∩ {(b, 0) ∈ U}` with `|b| < r`, `(η_j) ⊆ X_m` is
bounded and `Df(b_j, 0)(0, η_j) = y_j + z_j` with `y_j → 0` in `F_m` and `(z_j)` bounded in
`F_{m+1}`, then `(η_j)` has a convergent subsequence in `X_m`.  (The text: "for `b ∈ B ∩ U`
small enough. If `(b_j) ⊂ B ∩ U` is a sequence converging to `b` and `(η_j) ⊂ X` is bounded on
level `m` ..."; the smallness of `b` is read as uniform in `m`.) -/
def CompactnessCondition (U : Set (𝔼 0)) (f : 𝔼 0 → 𝔽 0) : Prop :=
  ∃ r > 0, ∀ m : ℕ, ∀ (b : ℕ → P) (b₀ : P) (η : ℕ → X m) (y : ℕ → 𝔽 m) (z : ℕ → 𝔽 (m + 1)),
    (∀ j, b j ∈ Ct ∧ ((b j, 0) : 𝔼 0) ∈ U) → b₀ ∈ Ct → ‖b₀‖ < r → Tendsto b atTop (𝓝 b₀) →
    (∃ M : ℝ, ∀ j, ‖η j‖ ≤ M) →
    (∀ j, levelDeriv (scDeriv (E := 𝔼) (F := 𝔽) U f) m ((b j, 0) : P × X (m + 1)) ((0 : P), η j) =
      y j + (𝔽).incl m (z j)) →
    Tendsto y atTop (𝓝 0) → (∃ M : ℝ, ∀ j, ‖z j‖ ≤ M) →
    ∃ (η₀ : X m) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (η ∘ φ) atTop (𝓝 η₀)

/-- **The compactness property of the family `L(b)` (Finding 73) from condition (2)**: if
`b_j → b₀` in `O`, `(h_j)` is bounded in `X_m` and `L(b_j)h_j → 0`, then `Df(b_j, 0)(0, h_j) =
(0, L(b_j)h_j) + ((Df(b_j, 0)(0, h_j))_Q, 0)` with the `Q`-component bounded (the joint continuity
gives a uniform operator bound near `b₀`, `exists_bound_of_continuousOn_clm`, for `j` large), so
(2) applies to the tail of the sequences. -/
theorem familyCompactness_derivFamOp (hf : IsScSmooth U f) {r : ℝ} {O : Set P}
    (hOU : ∀ b ∈ O, b ∈ Ct ∧ ((b, 0) : 𝔼 0) ∈ U) (hOr : ∀ b ∈ O, ‖b‖ < r) (m : ℕ)
    (h2 : ∀ (b : ℕ → P) (b₀ : P) (η : ℕ → X m) (y : ℕ → 𝔽 m) (z : ℕ → 𝔽 (m + 1)),
      (∀ j, b j ∈ Ct ∧ ((b j, 0) : 𝔼 0) ∈ U) → b₀ ∈ Ct → ‖b₀‖ < r → Tendsto b atTop (𝓝 b₀) →
      (∃ M : ℝ, ∀ j, ‖η j‖ ≤ M) →
      (∀ j, levelDeriv (scDeriv (E := 𝔼) (F := 𝔽) U f) m ((b j, 0) : P × X (m + 1)) ((0 : P), η j) =
        y j + (𝔽).incl m (z j)) →
      Tendsto y atTop (𝓝 0) → (∃ M : ℝ, ∀ j, ‖z j‖ ≤ M) →
      ∃ (η₀ : X m) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (η ∘ φ) atTop (𝓝 η₀)) :
    FamilyCompactness O (derivFamOp hf) m := by
  intro b b₀ η hbO hb₀O hb hη hL0
  -- a uniform bound on `Df(b_j, 0)(0, ·)` for `j` large
  set Φ : P → X m →L[ℝ] 𝔽 m := fun b =>
    (levelDeriv (scDeriv (E := 𝔼) (F := 𝔽) U f) m ((b, 0) : P × X (m + 1))).comp
      (ContinuousLinearMap.inr ℝ P (X m)) with hΦ
  have hΦc : ContinuousOn (fun p : P × X m => Φ p.1 p.2) (O ×ˢ univ) :=
    continuousOn_levelDeriv_param hf (fun b hb => (hOU b hb).2) m
  obtain ⟨M₁, hM₁⟩ := exists_bound_of_continuousOn_clm hΦc hb₀O
  have hbO' : Tendsto b atTop (𝓝[O] b₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hb, Eventually.of_forall hbO⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hbO'.eventually hM₁)
  obtain ⟨M, hM⟩ := hη
  -- the tails
  set b' : ℕ → P := fun j => b (j + N) with hb'
  set η' : ℕ → X m := fun j => η (j + N) with hη'
  set y' : ℕ → 𝔽 m := fun j => ((0 : Q), derivFamOp hf (b' j) m (η' j)) with hy'
  set z' : ℕ → 𝔽 (m + 1) := fun j =>
    ((levelDeriv (scDeriv (E := 𝔼) (F := 𝔽) U f) m ((b' j, 0) : P × X (m + 1)) ((0 : P), η' j)).1,
      (0 : Y (m + 1))) with hz'
  have hb'O : ∀ j, b' j ∈ O := fun j => hbO _
  obtain ⟨η₀, φ, hφ, hlim⟩ := h2 b' b₀ η' y' z' (fun j => hOU _ (hb'O j)) (hOU b₀ hb₀O).1
    (hOr b₀ hb₀O) (hb.comp (tendsto_add_atTop_nat N)) ⟨M, fun j => hM _⟩
    (fun j => by
      refine Prod.ext ?_ ?_
      · show _ = 0 + ((𝔽).incl m (z' j)).1
        rw [ScBanach.paramProd_incl, zero_add]
      · show _ = derivFamOp hf (b' j) m (η' j) + ((𝔽).incl m (z' j)).2
        rw [ScBanach.paramProd_incl, derivFamOp_apply hf (hOU _ (hb'O j)).2]
        simp only [hz', map_zero, add_zero])
    (by
      have : Tendsto (fun j => derivFamOp hf (b' j) m (η' j)) atTop (𝓝 0) :=
        hL0.comp (tendsto_add_atTop_nat N)
      show Tendsto (fun j => (((0 : Q), derivFamOp hf (b' j) m (η' j)) : 𝔽 m)) atTop
        (𝓝 ((0 : Q), (0 : Y m)))
      exact tendsto_const_nhds.prodMk_nhds this)
    ⟨|M₁| * M, fun j => by
      have h1 : ∀ v, ‖Φ (b' j) v‖ ≤ M₁ * ‖v‖ := hN (j + N) (by omega)
      have h2 : ‖z' j‖ ≤ ‖Φ (b' j) (η' j)‖ := by
        rw [hz', Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
        exact norm_fst_le (Φ (b' j) (η' j))
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
      calc ‖z' j‖ ≤ M₁ * ‖η' j‖ := h2.trans (h1 _)
        _ ≤ |M₁| * ‖η' j‖ := mul_le_mul_of_nonneg_right (le_abs_self M₁) (norm_nonneg _)
        _ ≤ |M₁| * M := mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)⟩
  exact ⟨η₀, fun j => φ j + N, fun i j hij => by simp only; have := hφ hij; omega, hlim⟩


/-- Injectivity of an sc-operator on level `0` gives injectivity on every level. -/
lemma ScOperator.injective_lvl {E F : ScBanach} (T : ScOperator E F) (h : Injective (T 0)) (m : ℕ) :
    Injective (T m) := fun x y hxy => by
  apply E.toBase_injective m
  apply h
  rw [← T.toBase_comm, ← T.toBase_comm, hxy]

/-- The compactness property of a family passes to subsets of parameters. -/
lemma FamilyCompactness.mono {Bf : Type} [NormedAddCommGroup Bf] [NormedSpace ℝ Bf]
    [FiniteDimensional ℝ Bf] {O K : Set Bf} {L : Bf → ScOperator X Y} {m : ℕ}
    (h : FamilyCompactness O L m) (hKO : K ⊆ O) : FamilyCompactness K L m :=
  fun b b₀ η hb hb₀ => h b b₀ η (fun j => hKO (hb j)) (hKO hb₀)

/-- **Theorem 3.58 (Basic Germ Criterion)**, in the coordinates of the text's proof
(`E = ℝⁿ ⊕ X`, `C = C̃ ⊕ X`, `F = ℝᴺ ⊕ Y`): let `U` be a relatively open neighbourhood of `0` in the
partial quadrant `C̃ ⊕ X` and `f : U → ℝᴺ ⊕ Y` sc-smooth such that

1. at the smooth points `(b, 0) ∈ U`, `b ∈ C̃`, the linearization `Df(b, 0) : E → F` is sc-Fredholm
   with index independent of `b` (`h1`; the text asks this at all smooth points of `U`);
2. `P ∘ Df(0)|X : X → Y` is bijective (`h2bij`; the text: `B ⊇ ker Df(0)` and `Y = Df(0)X`) and the
   compactness property holds (`h2cpt`, `CompactnessCondition`);
3. the estimate `|[D₂f(b, 0) − D₂f(b, x)]h|_m ≤ ε|h|_m` holds for `b` small and `x ∈ X_{m+1}`
   small on level `m` (`h3`, `DerivCondition`).

Then there are an open neighbourhood `Vo` of `0` in `ℝⁿ` and a family `b ↦ L(b)` of
sc-isomorphisms `X → Y` with `L(b) = P ∘ D₂f(b, 0)|X` for `b ∈ Vo ∩ C̃`, such that the
push-forward `k = Φ_*(f − f(0))`, `k(b, x) = ((1 − P)h(b, x), L(b)⁻¹P h(b, x))`, is a basic germ
on `O(U ∩ (Vo ⊕ X), 0)` with contraction map `H(b, x) = x − L(b)⁻¹P h(b, x)`, the fibre map
`Φ((b, x), (c, y)) = ((b, x), (c, L(b)⁻¹y))` is a strong bundle isomorphism covering the identity,
and `f − s`, `s = f(0)` the constant sc⁺-section, is conjugated near `0` to a basic germ.

Proof: Lemma 3.59 (`lemma_3_59`) gives the injectivity of `L(b)` near `0`, Lemma 3.60
(`lemma_3_60`) the uniform lower bounds on a compact neighbourhood `K`, the index argument
(`surjective_of_fredholmIndex_block`: `ind Df(b, 0) = ind Df(0) = n − N` on every level, so
`ind L(b) = 0` and the injective `L(b)` is surjective) the sc-isomorphisms, and
`theorem_3_58_of_family` concludes with condition (3). -/
theorem theorem_3_58 (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (hU : IsRelOpenInQuadrant 𝔼 (Ct ×ˢ univ) U) (h0 : (0 : 𝔼 0) ∈ U) (hf : IsScSmooth U f)
    (h1 : ∀ b ∈ Ct, ∀ hb : ((b, 0) : 𝔼 0) ∈ U,
      IsScFredholm (derivParamOp hf b hb) ∧ scIndex (derivParamOp hf b hb) = scIndex (derivParamOp hf 0 h0))
    (h2bij : Bijective fun h : X 0 => (scDeriv (E := 𝔼) (F := 𝔽) U f 0 ((0 : P), h)).2)
    (h2cpt : CompactnessCondition Ct U f) (h3 : DerivCondition Ct U f) :
    ∃ (Vo : Set P) (hVo : IsOpen Vo) (hVo0 : (0 : P) ∈ Vo) (L : P → ScIso X Y),
      (∀ b ∈ Vo ∩ Ct, ∀ h : X 0,
        L b 0 h = (scDeriv (E := 𝔼) (F := 𝔽) U f ((b, 0) : P × X 1) ((0 : P), h)).2) ∧
      IsBasicGerm Ct (ScNbhdGerm.ofSet (hU.inter_isOpen (hVo.prod isOpen_univ)).relOpen
        ⟨h0, hVo0, mem_univ _⟩) (pushGerm358 L f) (contrMap358 L f) ∧
      IsStrongBundleIso (U ∩ Vo ×ˢ univ) (U ∩ Vo ×ˢ univ)
        (fiberIsoMap (Q := Q) X fun b => (L b).symm) (fiberIsoMap X L) ∧
      IsConjugateToBasicGerm (U ∩ Vo ×ˢ univ) (shiftedGerm f) := by
  obtain ⟨r₂, hr₂, h2⟩ := h2cpt
  obtain ⟨Vopen, hVopen, hUeq⟩ := hU.relOpen
  have hCt0 : (0 : P) ∈ Ct := hC.isQuadrantLike.zero_mem
  have hCtcl : IsClosed Ct := by
    have := hC.isClosed_lvlSet 0
    rwa [ScBanach.lvlSet_zero] at this
  -- `Vopen' = {b | (b, 0) ∈ V}`
  set Vopen' : Set P := {b | ((b, 0) : 𝔼 0) ∈ Vopen} with hVopen'
  have hVopen'o : IsOpen Vopen' :=
    hVopen.preimage (continuous_id.prodMk continuous_const : Continuous fun b : P => ((b, 0) : 𝔼 0))
  have hV0' : (0 : P) ∈ Vopen' := by
    show ((0, 0) : 𝔼 0) ∈ Vopen
    have : (0 : 𝔼 0) ∈ Vopen := (hUeq ▸ h0).1
    exact this
  have hbU : ∀ b ∈ Vopen' ∩ Ct, ((b, 0) : 𝔼 0) ∈ U := fun b hb => by
    rw [hUeq]; exact ⟨hb.1, hb.2, mem_univ _⟩
  -- the neighbourhood `O` of Lemma 3.59
  set O : Set P := (Vopen' ∩ ball 0 r₂) ∩ Ct with hO
  have hOU : ∀ b ∈ O, b ∈ Ct ∧ ((b, 0) : 𝔼 0) ∈ U := fun b hb => ⟨hb.2, hbU b ⟨hb.1.1, hb.2⟩⟩
  have hOr : ∀ b ∈ O, ‖b‖ < r₂ := fun b hb => mem_ball_zero_iff.1 hb.1.2
  have h0O : (0 : P) ∈ O := ⟨⟨hV0', mem_ball_self hr₂⟩, hCt0⟩
  have hcpt : ∀ m, FamilyCompactness O (derivFamOp hf) m := fun m =>
    familyCompactness_derivFamOp hf hOU hOr m (h2 m)
  have hcont : ∀ m, ContinuousOn (fun p : P × X m => derivFamOp hf p.1 m p.2) (O ×ˢ univ) :=
    fun m => continuousOn_derivFamOp hf (fun b hb => (hOU b hb).2) m
  -- Lemma 3.59
  have hinj0 : Injective (derivFamOp hf 0 0) := by
    have e : ∀ h : X 0, derivFamOp hf 0 0 h = (scDeriv (E := 𝔼) (F := 𝔽) U f 0 ((0 : P), h)).2 :=
      fun h => by rw [derivFamOp_apply hf h0 0 h, levelDeriv_zero]; rfl
    intro x y hxy
    apply h2bij.1
    simp only
    rw [← e, ← e, hxy]
  obtain ⟨r₁, hr₁, hinj⟩ := lemma_3_59 h0O (derivFamOp hf) (hcont 0) hinj0 (hcpt 0)
  -- the compact neighbourhood `K` of Lemma 3.60
  have hnhds : Vopen' ∩ ball 0 r₂ ∩ ball 0 r₁ ∈ 𝓝 (0 : P) :=
    ((hVopen'o.inter isOpen_ball).inter isOpen_ball).mem_nhds
      ⟨⟨hV0', mem_ball_self hr₂⟩, mem_ball_self hr₁⟩
  obtain ⟨r₁', hr₁', hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hnhds
  set K : Set P := closedBall 0 r₁' ∩ Ct with hK
  have hKO : K ⊆ O := fun b hb => ⟨(hball hb.1).1, hb.2⟩
  have hKr₁ : ∀ b ∈ K, ‖b‖ < r₁ := fun b hb => mem_ball_zero_iff.1 (hball hb.1).2
  have hKc : IsCompact K := (isCompact_closedBall (0 : P) r₁').inter_right hCtcl
  have h0K : (0 : P) ∈ K := ⟨mem_closedBall_self hr₁'.le, hCt0⟩
  have hinjK : ∀ b ∈ K, ∀ m, Injective (derivFamOp hf b m) := fun b hb m =>
    (derivFamOp hf b).injective_lvl (hinj b (hKO hb) (hKr₁ b hb)) m
  -- Lemma 3.60
  have hc : ∀ m, ∃ c > 0, ∀ b ∈ K, ∀ h : X m, c * ‖h‖ ≤ ‖derivFamOp hf b m h‖ := fun m =>
    lemma_3_60 hKc (derivFamOp hf) m ((hcont m).mono (prod_mono hKO subset_rfl))
      (fun b hb => hinjK b hb m) ((hcpt m).mono hKO)
  -- the index: `ind Df(0) = n − N` from the bijectivity of `L(0)` on level `0`
  have hLblock : ∀ b (hb : ((b, 0) : 𝔼 0) ∈ U) m (x : X m),
      (derivParamOp hf b hb m ((0 : P), x)).2 = derivFamOp hf b m x := fun b hb m x => by
    rw [derivParamOp_lvl, derivFamOp_apply hf hb]
  have hind0 : scIndex (derivParamOp hf 0 h0) = finrank ℝ P - finrank ℝ Q := by
    obtain ⟨hF, -⟩ := h1 0 hCt0 h0
    have hF0 := hF.fredholmIndex_lvl 0
    rw [scIndex_eq_fredholmIndex]
    have hbij : Bijective (derivFamOp hf 0 0) := by
      have e : (derivFamOp hf 0 0 : X 0 → Y 0) =
          fun h => (scDeriv (E := 𝔼) (F := 𝔽) U f 0 ((0 : P), h)).2 := by
        funext h; rw [derivFamOp_apply hf h0 0 h, levelDeriv_zero]; rfl
      rw [e]; exact h2bij
    have hLfin : HasFiniteIndex (derivFamOp hf 0 0 : X 0 →ₗ[ℝ] Y 0) :=
      HasFiniteIndex.equiv (LinearEquiv.ofBijective _ hbij)
    have := fredholmIndex_block (derivParamOp hf 0 h0 0) hF0.1 (derivFamOp hf 0 0)
      (hLblock 0 h0 0) hLfin
    have hl0 : linIndex (derivFamOp hf 0 0 : X 0 →ₗ[ℝ] Y 0) = 0 :=
      linIndex_equiv (LinearEquiv.ofBijective _ hbij)
    rw [this, hl0]
    ring
  -- surjectivity of `L(b)` on every level for `b ∈ K`
  have hsurj : ∀ b ∈ K, ∀ m, Surjective (derivFamOp hf b m) := fun b hb m => by
    obtain ⟨hF, hind⟩ := h1 b hb.2 (hOU b (hKO hb)).2
    have hFm := hF.fredholmIndex_lvl m
    exact surjective_of_fredholmIndex_block (derivParamOp hf b (hOU b (hKO hb)).2 m) hFm.1
      (by rw [hFm.2, hind, hind0]) (derivFamOp hf b m) (hLblock b _ m) (hinjK b hb m)
  -- the family of sc-isomorphisms
  let mkIso : ∀ b ∈ K, ScIso X Y := fun b hb =>
    { lvl := fun m => ContinuousLinearEquiv.ofBijective (derivFamOp hf b m)
        (LinearMap.ker_eq_bot.2 (hinjK b hb m)) (LinearMap.range_eq_top.2 (hsurj b hb m))
      incl_comm := fun m x => (derivFamOp hf b).incl_comm m x }
  classical
  let L : P → ScIso X Y := fun b => if hb : b ∈ K then mkIso b hb else mkIso 0 h0K
  have hLapply : ∀ b ∈ K, ∀ m (x : X m), L b m x = derivFamOp hf b m x := fun b hb m x => by
    simp only [L, dif_pos hb]; rfl
  -- the neighbourhood `Vo` and the conclusion
  have hVoK : ∀ b ∈ ball (0 : P) r₁' ∩ Ct, b ∈ K := fun b hb => ⟨ball_subset_closedBall hb.1, hb.2⟩
  have hL' : ∀ b ∈ ball (0 : P) r₁' ∩ Ct, ∀ h : X 0,
      L b 0 h = (scDeriv (E := 𝔼) (F := 𝔽) U f ((b, 0) : P × X 1) ((0 : P), h)).2 := fun b hb h => by
    rw [hLapply b (hVoK b hb), derivFamOp_apply hf (hOU b (hKO (hVoK b hb))).2, levelDeriv_zero]
  refine ⟨ball 0 r₁', isOpen_ball, mem_ball_self hr₁', L, hL', ?_⟩
  exact theorem_3_58_of_family hC hU h0 hf isOpen_ball (mem_ball_self hr₁')
    (fun b hb => (hOU b (hKO (hVoK b hb))).2) hL'
    (fun m => by
      obtain ⟨c, hc0, hcm⟩ := hc m
      exact ⟨c, hc0, fun b hb h => by rw [hLapply b (hVoK b hb)]; exact hcm b (hVoK b hb) h⟩) h3


end Family

end Polyfold
