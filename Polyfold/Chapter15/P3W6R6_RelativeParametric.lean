import Polyfold.Chapter15.P3W6R6_RelativeBranch
import Polyfold.Chapter15.P3W6R6_RelativeReduction

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (2017: Theorem 15.5), steps (c)–(d), pp. 698–699: "Achieving global
transversality" relative to `Λ₀`, i.e. R6's `HasParametricGeneralPositionRel`, proved under the
hypotheses of the theorem (GB's `hasParametricGeneralPosition` with `Λ₀` for the trivial
multisection).

# Relative parametrized general position

## The text, paraphrased

For `Λ̃_t = Λ₀ ⊕ Λ_t` with (15.1) relative to `Λ₀` at the points of `supp(Λ₀ ∘ f)`, the
parametrized problem near every `(0, x)` is in general position; for small `t` only points near
`supp(Λ₀ ∘ f)` matter; the implicit function theorem and Sard's theorem give a null set of
parameters off which `(f, Λ̃_t)` is in general position.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `sectionAdd_paramSec_zero`, `subSec_eq_of_add`, `exists_of_multisectionAdd_pos_at`: small
  identities in the fibres.
* **`exists_local_paramGP_rel`**: the local step at a point `x₀` with (15.1) relative to `Λ₀`:
  an open `V ∋ x₀`, `δ > 0` and a null set `CV` with `(f, Λ₀ ⊕ Λ_t)` in general position at every
  point of `V ∩ supp((Λ₀ ⊕ Λ_t) ∘ f)` for `‖t‖ < δ`, `t ∉ CV`.  For every pair of branches
  `(s⁰_a, Σ_j t_j s_{ij})`: if `s⁰_a(x₀) = f(x₀)`, Part I's local Sard step
  (`exists_null_isGeneralPositionGerm_paramSlice_near`) on `ℝ^ℓ × O` with
  `isGeneralPositionGerm_branchParam_rel`; otherwise the closed zero set of the parametrized branch
  (`isClosed_solutionSet`) misses a neighbourhood of `(0, x₀)`.
* **`exists_pos_supp_rel_subset`**: the compactness (15.2) relative to `Λ₀`: every saturated open
  `V ⊇ supp(Λ₀ ∘ f)` contains `supp((Λ₀ ⊕ Λ_t) ∘ f)` for small `|t|₁` (a cluster point `z` of a
  sequence outside `V`, a branch `s⁰_a` of `Λ₀` near `z` met infinitely often, and the
  continuity of `f − s⁰_a` give `f(z) = s⁰_a(z)`).
* **`hasParametricGeneralPositionRel`**: `HasParametricGeneralPositionRel A f Λ₀ N U` for tame `X`,
  an sc-Fredholm section functor `f` with tame germ data, `(N, U)` controlling compactness, and an
  sc⁺-multisection `Λ₀` with `N(Λ₀) ≤ 1`, `dom-supp(Λ₀) ⊆ U` (compactness of `|S_f|` is not used).
* **`theorem_15_3_7_relative_of_local`**: TX's relative statement from `HasLocalGPFamiliesRel`
  alone; **`theorem_15_3_9_of_local_rel`**: Theorem 15.3.9 from `hB`, the extension statement of
  Theorem 14.1.9, and `HasLocalGPFamiliesRel`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### Fibre identities -/

/-- At `t = 0` the branch `s⁰ + Σ_j t_j s_j` is `s⁰`. -/
theorem sectionAdd_paramSec_zero {s₀ : A.Obj → A.W} (hs₀ : IsSection A.P s₀) {ℓ : ℕ}
    {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsSection A.P (s j)) (y : A.Obj) :
    Polyfold.sectionAdd A.P s₀ (paramSec s 0) y = s₀ y := by
  rw [sectionAdd_apply hs₀ (isSection_paramSec s 0)]
  have h : (⟨paramSec s 0 y, isSection_paramSec s 0 y⟩ : A.P ⁻¹' {y}) = 0 := by
    rw [paramFib hs 0 y]
    simp
  rw [h, add_zero]

/-- If `f(y) = a + b` with `a = s(y)` in `W_y`, then `(f − s)(y) = b`. -/
theorem subSec_eq_of_add {f s : A.Obj → A.W} (hf : IsSection A.P f) {O : Set A.Obj}
    (hsec : ∀ y ∈ O, A.P (s y) = y) {y : A.Obj} (hy : y ∈ O) (a b : A.P ⁻¹' {y})
    (ha : (a : A.W) = s y) (hab : ((a + b : A.P ⁻¹' {y}) : A.W) = f y) :
    subSec f s O y = b := by
  have hs' : A.P (extendZero O s y) = y := isSection_extendZero O s y
  have hval : subSec f s O y = (((⟨f y, hf y⟩ : A.P ⁻¹' {y}) +
      ((-1 : ℝ) • (⟨extendZero O s y, hs'⟩ : A.P ⁻¹' {y})) : A.P ⁻¹' {y}) : A.W) := by
    unfold subSec
    rw [sectionAdd_apply hf (isSection_extendZero O s).sectionSmul]
    congr 2
    exact Subtype.ext (sectionSmul_apply (f := fun _ => (-1 : ℝ)) (isSection_extendZero O s) y)
  have h1 : (⟨f y, hf y⟩ : A.P ⁻¹' {y}) = a + b := Subtype.ext hab.symm
  have h2 : (⟨extendZero O s y, hs'⟩ : A.P ⁻¹' {y}) = a :=
    Subtype.ext ((extendZero_eqOn hsec hy).symm.trans ha.symm)
  rw [hval, h1, h2, neg_one_smul]
  congr 1
  abel

/-- `exists_of_multisectionAdd_pos` in the fibre over a given point. -/
theorem exists_of_multisectionAdd_pos_at {Λ Λ' : A.W → ℚ≥0} {x : A.Obj} {w : A.W}
    (hw : A.P w = x) (h : 0 < multisectionAdd Λ Λ' w) :
    ∃ a b : A.P ⁻¹' {x}, 0 < Λ a ∧ 0 < Λ' b ∧ ((a + b : A.P ⁻¹' {x}) : A.W) = w := by
  subst hw
  exact exists_of_multisectionAdd_pos h

/-! ### The local step -/

set_option maxHeartbeats 1600000 in
-- Part I's local step for each pair of branches, assembled over the branches
/-- **The local step of "Achieving global transversality" relative to `Λ₀`** (proof of Theorem
15.3.9, steps (c)–(d), with p. 697): let `X` be tame, `f` an sc-Fredholm section functor with tame
germ data, `Λ₀` an sc⁺-multisection, `t ↦ Λ_t` a family of sc⁺-multisections with (15.1) relative
to `Λ₀` at `x₀`.  There are an open `V ∋ x₀`, `δ > 0` and a Lebesgue null set `CV ⊆ ℝ^ℓ` such that
`(f, Λ₀ ⊕ Λ_t)` is in general position at every point of `V ∩ supp((Λ₀ ⊕ Λ_t) ∘ f)` for
`‖t‖ < δ`, `t ∉ CV`. -/
theorem exists_local_paramGP_rel (hX : A.X.IsTame) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ₀ : A.W → ℚ≥0} (hΛ₀ : IsScPlusMultisection A Λ₀) {ℓ : ℕ}
    {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0} (hΛ : ∀ t, IsScPlusMultisection A (Λ t))
    {x₀ : A.X.PObj.Level 1} (hon : IsParamOntoAtRel f Λ₀ Λ x₀) :
    ∃ V : Set A.Obj, IsOpen V ∧ A.X.PObj.levelVal 1 x₀ ∈ V ∧ ∃ δ > (0 : ℝ),
      ∃ CV : Set (Fin ℓ → ℝ), volume CV = 0 ∧ ∀ t : Fin ℓ → ℝ, ‖t‖ < δ → t ∉ CV →
        ∀ y ∈ V, 0 < multisectionAdd Λ₀ (Λ t) (f y) →
          IsInGeneralPositionAt f (multisectionAdd Λ₀ (Λ t)) y := by
  classical
  obtain ⟨O₁, k, s, σ, hs, hO₁, hx₀O₁, hrep₁, hon⟩ := hon
  set y₀ := A.X.PObj.levelVal 1 x₀ with hy₀
  obtain ⟨O₂, k₀, s₀', σ₀, hO₂, hx₀O₂, hrep₀'⟩ := hΛ₀.exists_isLocalRepOn y₀
  set O := O₁ ∩ O₂ with hOdef
  have hO : IsOpen O := hO₁.inter hO₂
  have hx₀O : y₀ ∈ O := ⟨hx₀O₁, hx₀O₂⟩
  set s₀ : Fin k₀ → A.Obj → A.W := fun a => extendZero O₂ (s₀' a) with hs₀def
  have hs₀ : ∀ a, IsSection A.P (s₀ a) := fun a => isSection_extendZero O₂ _
  have hrep₀ : IsLocalRepOn A Λ₀ O s₀ σ₀ := hrep₀'.extendZero.mono hO inter_subset_right
  have hrep : ∀ t, IsLocalRepOn A (Λ t) O (fun i => paramSec (s i) t) σ :=
    fun t => (hrep₁ t).mono hO inter_subset_left
  have : Nonempty O := ⟨⟨y₀, hx₀O⟩⟩
  have := A.X.PObj.paracompactSpace_subtype O
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
    (A.X.PObj.restrictOpen hO) A.B
  have := MPolyfold.paracompactSpace_prod (rnPolyfold ℓ) (A.X.PObj.restrictOpen hO)
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin ℓ → ℝ) × O → O))
    ((rnPolyfold ℓ).prod (A.X.PObj.restrictOpen hO)) (A.B.restrictOpen hO)
  have hXO : (A.X.PObj.restrictOpen hO).IsTame := MPolyfold.isTame_restrictOpen _ hO hX
  have hs' : ∀ i j, IsScPlusSectionOn A (s i j) O := fun i j =>
    (isScPlusSectionOn_of_paramSec hs hrep₁ i j).mono hO inter_subset_left
  set p₀ : O := ⟨y₀, hx₀O⟩
  -- Part I's local step, or a neighbourhood free of zeros, for every pair of branches
  have hbr : ∀ (a : Fin k₀) (i : Fin k), ∃ W : Set ((Fin ℓ → ℝ) × O), IsOpen W ∧
      ((0 : Fin ℓ → ℝ), p₀) ∈ W ∧ ∃ CV : Set (Fin ℓ → ℝ), volume CV = 0 ∧
        ∀ t (p : O), (t, p) ∈ W →
          f p = Polyfold.sectionAdd A.P (s₀ a) (paramSec (s i) t) p → t ∉ CV →
          (A.B.restrictOpen hO).IsGeneralPositionGerm
            (subRestrict (O := O) f (Polyfold.sectionAdd A.P (s₀ a) (paramSec (s i) t))
              hft.isScSmooth.1) p := by
    intro a i
    have hsa : IsScPlusSectionOn A (s₀ a) O := hrep₀.2.1 a
    have hgO := isScFredholmSectionTame_subRestrict hO hft hsa
    have htp : ∀ j, (A.B.restrictOpen hO).IsScPlusSection (negRestrict (O := O) (s i j)) :=
      fun j => isScPlusSection_negRestrict hO (hs' i j)
    have hsl := fun t => paramSlice_branch_eq_rel (O := O) hft.isScSmooth.1 (hs₀ a) (hs i) t
    have hzero : ∀ t (p : O), IsZeroAt (pullbackProj (pullbackProj A.P (Subtype.val : O → A.Obj))
        Prod.snd) (paramSection (subRestrict (O := O) f (s₀ a) hft.isScSmooth.1)
          hgO.isScSmooth.1 (fun j => negRestrict (O := O) (s i j)) fun j => (htp j).1) (t, p) ↔
        f p = Polyfold.sectionAdd A.P (s₀ a) (paramSec (s i) t) p := by
      intro t p
      rw [isZeroAt_paramSection_iff]
      change IsZeroAt _ (paramSlice _ _ _ _ t) p ↔ _
      rw [hsl t]
      unfold subRestrict
      rw [isZeroAt_restrictSection_iff]
      exact isZeroAt_subSec_iff hft.isScSmooth.1
        (fun y _ => (hs₀ a).sectionAdd (isSection_paramSec _ t) y) p.2
    by_cases hx0 : f y₀ = s₀ a y₀
    · have hz₀ := (hzero 0 p₀).2 (by
        change f y₀ = Polyfold.sectionAdd A.P (s₀ a) (paramSec (s i) 0) y₀
        rw [sectionAdd_paramSec_zero (hs₀ a) (hs i)]
        exact hx0)
      have hgp := isGeneralPositionGerm_branchParam_rel hO hf hft hrep₀ a (hs' i) (hs i) hx₀O hx0
        fun L hL φ hφ hx m V T hT w => hon L hL φ hφ hx m V T hT i w
      obtain ⟨W, hWo, hW0, CV, hCV, hW⟩ :=
        StrongBundle.exists_null_isGeneralPositionGerm_paramSlice_near hXO hgO htp hz₀ hgp
      refine ⟨W, hWo, hW0, CV, hCV, fun t p htp' hfp htCV => ?_⟩
      have h := hW (t, p) htp' ((hzero t p).2 hfp) htCV
      change (A.B.restrictOpen hO).IsGeneralPositionGerm (paramSlice _ _ _ _ t) p at h
      rwa [hsl t] at h
    · have hcl := isClosed_solutionSet (theorem_3_1_21_tame hgO htp).isScSmooth
      refine ⟨_, hcl.isOpen_compl, fun h0 => hx0 ?_, ∅, measure_empty,
        fun t p htp' hfp _ => absurd ((hzero t p).2 hfp) htp'⟩
      have h1 := (hzero 0 p₀).1 h0
      change f y₀ = Polyfold.sectionAdd A.P (s₀ a) (paramSec (s i) 0) y₀ at h1
      rwa [sectionAdd_paramSec_zero (hs₀ a) (hs i)] at h1
  choose W hWo hW0 CV hCV hW using hbr
  have hnhds : ∀ a i, W a i ∈ 𝓝 ((0 : Fin ℓ → ℝ), p₀) := fun a i =>
    (hWo a i).mem_nhds (hW0 a i)
  have hprod : ∀ a i, ∃ u ∈ 𝓝 (0 : Fin ℓ → ℝ), ∃ v ∈ 𝓝 p₀, u ×ˢ v ⊆ W a i :=
    fun a i => mem_nhds_prod_iff.1 (hnhds a i)
  choose u hu v hv huv using hprod
  have hu' : (⋂ a, ⋂ i, u a i) ∈ 𝓝 (0 : Fin ℓ → ℝ) := iInter_mem.2 fun a => iInter_mem.2 (hu a)
  have hv' : (⋂ a, ⋂ i, v a i) ∈ 𝓝 p₀ := iInter_mem.2 fun a => iInter_mem.2 (hv a)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hu'
  obtain ⟨v', hv'sub, hv'o, hp₀v'⟩ := mem_nhds_iff.1 hv'
  refine ⟨Subtype.val '' v', hO.isOpenMap_subtype_val v' hv'o, ⟨p₀, hp₀v', rfl⟩, δ, hδ,
    ⋃ a, ⋃ i, CV a i, measure_iUnion_null fun a => measure_iUnion_null (hCV a),
    fun t ht htCV => ?_⟩
  rintro _ ⟨p, hpv', rfl⟩ hpos
  have htu : ∀ a i, t ∈ u a i := fun a i =>
    mem_iInter.1 (mem_iInter.1 (hball (mem_ball_zero_iff.2 ht)) a) i
  have hpv : ∀ a i, p ∈ v a i := fun a i => mem_iInter.1 (mem_iInter.1 (hv'sub hpv') a) i
  have hΛ' := definition_13_2_9 hΛ₀ (hΛ t)
  have hy1 := mem_levelSet_one_of_pos hf hΛ' hpos
  set yl := A.X.PObj.levelMk 1 (p : A.Obj) hy1
  have hyl : A.X.PObj.levelVal 1 yl = p := A.X.PObj.levelVal_levelMk 1 _ hy1
  refine ⟨hy1, ?_⟩
  obtain ⟨c₀, hc₀, hpc₀⟩ := StrongBundle.exists_chart_mem A.B (A.X.PObj.levelVal 1 yl)
  have hso : IsOpen (c₀.φ.source ∩ O) := c₀.φ.isOpen_source.inter hO
  set c := c₀.restrict inter_subset_left hso
  have hc : A.B.IsChart c :=
    (StrongBundle.isChart_of_mem A.B hc₀).restrict inter_subset_left hso
  have hsub : c.φ.source ⊆ O := inter_subset_right
  have hyc : A.X.PObj.levelVal 1 yl ∈ c.φ.source := ⟨hpc₀, by rw [hyl]; exact p.2⟩
  have hrepS := isLocalRepOn_multisectionAdd hO hs₀ (fun i => isSection_paramSec (s i) t)
    hrep₀ (hrep t)
  refine isReducedOntoAtLevel_of_isGeneralPositionGerm hf hft hO hrepS hc hsub hyc
    fun n hn => ?_
  have e : (⟨A.X.PObj.levelVal 1 yl, hsub hyc⟩ : O) = p := Subtype.ext hyl
  rw [e]
  refine hW ((Fintype.equivFin (Fin k₀ × Fin k)).symm n).1
    ((Fintype.equivFin (Fin k₀ × Fin k)).symm n).2 t p
    (huv _ _ ⟨htu _ _, hpv _ _⟩) ?_ fun h' => htCV (mem_iUnion.2 ⟨_, mem_iUnion.2 ⟨_, h'⟩⟩)
  rw [← hyl]
  exact hn.symm

/-! ### The compactness (15.2) relative to `Λ₀` -/

variable {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {N : A.B.One → ℝ} {U : Set A.Obj}

set_option maxHeartbeats 800000 in
-- the cluster-point argument with a branch of `Λ₀` met infinitely often
/-- **The compactness (15.2) relative to `Λ₀`** (proof of Theorem 15.3.9 with p. 696): if `(N, U)`
controls the compactness of `f`, `N(Λ₀) ≤ 1`, `dom-supp(Λ₀) ⊆ U`, and the family has
`N(Λ_t) ≤ |t|₁ (1 − N(Λ₀))` and `dom-supp(Λ_t) ⊆ U`, then every saturated open
`V ⊇ supp(Λ₀ ∘ f)` contains `supp((Λ₀ ⊕ Λ_t) ∘ f)` for small `|t|₁`.  *Proof*: points
`x_n ∉ V` of the supports with `|t_n|₁ → 0` have orbits in the compact
`cl|{x ∈ U | N(f(x)) ≤ 1}|`; at a cluster point `z`, `f(y_k) = a_k + b_k` with `a_k` on a branch
`s⁰_a` of `Λ₀` (one branch is met infinitely often) and `N(b_k) → 0`; then
`(f − s⁰_a)(y_k) = b_k → 0_z`, so `f(z) = s⁰_a(z)`, `z ∈ supp(Λ₀ ∘ f) ⊆ V`: absurd. -/
theorem exists_pos_supp_rel_subset (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hcc : ControlsCompactness A f N U)
    (hΛ₀ : IsScPlusMultisection A Λ₀) (hN₀ : ∀ x, pointwiseNorm N Λ₀ x ≤ 1)
    (hdom₀ : domSupp Λ₀ ⊆ U) {ℓ : ℕ} {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0}
    (hΛ : ∀ t, IsScPlusMultisection A (Λ t))
    (hNorm : ∀ t x, pointwiseNorm N (Λ t) x ≤ (∑ j, |t j|) * (1 - pointwiseNorm N Λ₀ x))
    (hdom : ∀ t, domSupp (Λ t) ⊆ U) {V : Set A.Obj} (hVo : IsOpen V) (hVs : A.X.IsSaturated V)
    (hSV : ∀ x, 0 < Λ₀ (f x) → x ∈ V) :
    ∃ ε > (0 : ℝ), ∀ t : Fin ℓ → ℝ, ∑ j, |t j| < ε →
      ∀ x, 0 < multisectionAdd Λ₀ (Λ t) (f x) → x ∈ V := by
  classical
  have hN : A.E.IsAuxNorm N := hcc.1
  have hNB : A.B.IsAuxNorm N := hN.isAuxNorm
  have hsec : IsSection A.P f := hft.isScSmooth.1
  obtain ⟨_hfs, hfun⟩ := hf.1
  have hsum1 : ∀ t : Fin ℓ → ℝ, ∑ j, |t j| ≤ 1 →
      ∀ x, pointwiseNorm N (multisectionAdd Λ₀ (Λ t)) x ≤ 1 := by
    intro t ht x
    refine (pointwiseNorm_multisectionAdd_le hNB hΛ₀ (hΛ t) x).trans ?_
    have h1 : (∑ j, |t j|) * (1 - pointwiseNorm N Λ₀ x) ≤ 1 - pointwiseNorm N Λ₀ x :=
      mul_le_of_le_one_left (by linarith [hN₀ x]) ht
    linarith [hNorm t x]
  by_contra hne
  push Not at hne
  have hx : ∀ n : ℕ, ∃ t : Fin ℓ → ℝ, ∑ j, |t j| < 1 / ((n : ℝ) + 1) ∧
      ∃ x, 0 < multisectionAdd Λ₀ (Λ t) (f x) ∧ x ∉ V := fun n => hne _ (by positivity)
  choose t ht x hxpos hxV using hx
  have ht1 : ∀ n, ∑ j, |t n j| ≤ 1 := fun n => (ht n).le.trans (by
    rw [div_le_one (by positivity)]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hxUN : ∀ n, x n ∈ U ∧ A.B.AuxLe N (f (x n)) 1 := fun n =>
    auxLe_of_pos hsec (definition_13_2_9 hΛ₀ (hΛ (t n))) hcc.2.2.2.1 (hsum1 _ (ht1 n))
      ((domSupp_multisectionAdd_subset _ _).trans (union_subset hdom₀ (hdom _))) (hxpos n)
  -- a cluster point of the orbits
  set K := closure (A.X.π '' {x ∈ U | A.B.AuxLe N (f x) 1})
  have hK : IsCompact K := hcc.2.2.2.2
  have hxK : ∀ n, A.X.π (x n) ∈ K := fun n => subset_closure ⟨x n, hxUN n, rfl⟩
  obtain ⟨q, -, hq⟩ := hK (f := map (fun n => A.X.π (x n)) atTop)
    (le_principal_iff.2 (mem_map.2 (Eventually.of_forall hxK)))
  obtain ⟨z, rfl⟩ := A.X.surjective_π q
  have := A.X.PObj.metrizableSpace
  obtain ⟨Bz, hBz⟩ := (𝓝 z).exists_antitone_basis
  have hy : ∀ k : ℕ, ∃ n ≥ k, ∃ y ∈ interior (Bz k), A.X.π y = A.X.π (x n) := by
    intro k
    have hO : A.X.π '' interior (Bz k) ∈ 𝓝 (A.X.π z) :=
      (A.X.proposition_7_1_8 _ isOpen_interior).mem_nhds
        ⟨z, mem_interior_iff_mem_nhds.2 (hBz.mem k), rfl⟩
    have h2 : ∃ᶠ n in atTop, A.X.π (x n) ∈ A.X.π '' interior (Bz k) :=
      Filter.frequently_map.1 (hq.frequently (Filter.eventually_of_mem hO fun _ h => h))
    obtain ⟨n, hnk, ⟨y, hyB, hyx⟩⟩ := Filter.frequently_atTop.1 h2 k
    exact ⟨n, hnk, y, hyB, hyx⟩
  choose n hnk y hyB hyx using hy
  have hyz : Tendsto y atTop (𝓝 z) :=
    hBz.tendsto fun k => interior_subset (hyB k)
  have hyV : ∀ k, y k ∉ V := by
    intro k hk
    apply hxV (n k)
    rw [← hVs]
    exact ⟨y k, hk, hyx k⟩
  have hypos : ∀ k, 0 < multisectionAdd Λ₀ (Λ (t (n k))) (f (y k)) := by
    intro k
    obtain ⟨φ, hφs, hφt⟩ := A.X.π_eq_π_iff.1 (hyx k)
    have hΛφ : multisectionAdd Λ₀ (Λ (t (n k))) (f (A.X.tgt φ)) =
        multisectionAdd Λ₀ (Λ (t (n k))) (f (A.X.src φ)) := by
      rw [hfun φ]
      exact (definition_13_2_9 hΛ₀ (hΛ _)).1 _
    rw [← hφs, ← hΛφ, hφt]
    exact hxpos (n k)
  -- the decomposition `f(y_k) = a_k + b_k`
  have hdec : ∀ k, ∃ a b : A.P ⁻¹' {y k}, 0 < Λ₀ a ∧ 0 < Λ (t (n k)) b ∧
      ((a + b : A.P ⁻¹' {y k}) : A.W) = f (y k) ∧
      normW N (b : A.W) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨a, b, ha, hb, hab⟩ := exists_of_multisectionAdd_pos_at (hsec (y k)) (hypos k)
    refine ⟨a, b, ha, hb, hab, ?_⟩
    have hbs : (b : A.W) ∈ suppAt (Λ (t (n k))) (y k) := ⟨b.2, hb⟩
    have h1 := ((hΛ (t (n k))).isGreatest_pointwiseNorm N (y k)).2 ⟨_, hbs, rfl⟩
    have h0 := pointwiseNorm_nonneg hNB Λ₀ (y k)
    have hs0 : 0 ≤ ∑ j, |t (n k) j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    refine h1.trans ((hNorm _ _).trans ?_)
    calc (∑ j, |t (n k) j|) * (1 - pointwiseNorm N Λ₀ (y k)) ≤ ∑ j, |t (n k) j| :=
          mul_le_of_le_one_right hs0 (by linarith)
      _ ≤ 1 / ((n k : ℝ) + 1) := (ht (n k)).le
      _ ≤ 1 / ((k : ℝ) + 1) := by
          gcongr
          exact_mod_cast hnk k
  choose a b ha hb hab hbN using hdec
  -- a local representation of `Λ₀` at `z`, and a branch met infinitely often
  obtain ⟨O₂, k₀, s₀', σ₀, hO₂, hzO₂, hrep₀'⟩ := hΛ₀.exists_isLocalRepOn z
  set s₀ : Fin k₀ → A.Obj → A.W := fun i => extendZero O₂ (s₀' i) with hs₀def
  have hrep₀ : IsLocalRepOn A Λ₀ O₂ s₀ σ₀ := hrep₀'.extendZero
  have hev : ∀ᶠ k in atTop, y k ∈ O₂ := hyz.eventually (hO₂.mem_nhds hzO₂)
  have hbr : ∀ k, y k ∈ O₂ → ∃ i, (a k : A.W) = s₀ i (y k) := by
    intro k hk
    have hmem : (a k : A.W) ∈ suppAt Λ₀ (y k) := ⟨(a k).2, ha k⟩
    rw [hrep₀.suppAt_eq hk] at hmem
    obtain ⟨i, hi⟩ := hmem
    exact ⟨i, hi.symm⟩
  have hfreq : ∃ i, ∃ᶠ k in atTop, y k ∈ O₂ ∧ (a k : A.W) = s₀ i (y k) := by
    by_contra H
    simp only [not_exists, Filter.not_frequently] at H
    obtain ⟨k, hk1, hk2⟩ := ((eventually_all.2 H).and hev).exists
    obtain ⟨i, hi⟩ := hbr k hk2
    exact hk1 i ⟨hk2, hi⟩
  obtain ⟨i, hi⟩ := hfreq
  obtain ⟨ψ, hψ, hψi⟩ := Filter.extraction_of_frequently_atTop hi
  -- the section `f − s⁰_i` on `O₂` is continuous
  have : Nonempty O₂ := ⟨⟨z, hzO₂⟩⟩
  have := A.X.PObj.paracompactSpace_subtype O₂
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : O₂ → A.Obj))
    (A.X.PObj.restrictOpen hO₂) A.B
  have hsi : IsScPlusSectionOn A (s₀ i) O₂ := hrep₀.2.1 i
  have hgO := isScFredholmSectionTame_subRestrict hO₂ hft hsi
  have hgc : Continuous (subRestrict (O := O₂) f (s₀ i) hft.isScSmooth.1) :=
    continuousOn_univ.1 hgO.isScSmooth.2.continuousOn
  have hgc' : ContinuousOn (subSec f (s₀ i) O₂) O₂ := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_snd.comp continuous_subtype_val).comp hgc
  have hyψ : Tendsto (fun m => y (ψ m)) atTop (𝓝 z) := hyz.comp hψ.tendsto_atTop
  have hgz : Tendsto (fun m => subSec f (s₀ i) O₂ (y (ψ m))) atTop
      (𝓝 (subSec f (s₀ i) O₂ z)) :=
    (hgc'.continuousAt (hO₂.mem_nhds hzO₂)).tendsto.comp hyψ
  have hgb : ∀ m, subSec f (s₀ i) O₂ (y (ψ m)) = (b (ψ m) : A.W) := fun m =>
    subSec_eq_of_add hsec hsi.1 (hψi m).1 (a (ψ m)) (b (ψ m)) (hψi m).2 (hab (ψ m))
  -- `b_k → 0_z`
  have hb0 : Tendsto (fun m => (b (ψ m) : A.W)) atTop (𝓝 (fiberZero A.P z)) := by
    have h1 : ∀ m, (b (ψ m) : A.W) ∈ A.B.oneSet := fun m =>
      (hΛ _).suppAt_subset_oneSet _ ⟨(b (ψ m)).2, hb (ψ m)⟩
    set w : ℕ → A.B.One := fun m => A.B.oneMk (b (ψ m)) (h1 m)
    have hwP : Tendsto (fun m => A.P (A.B.oneVal (w m))) atTop (𝓝 z) := by
      refine hyψ.congr fun m => ?_
      change y (ψ m) = A.P (A.B.oneVal (A.B.oneMk _ (h1 m)))
      rw [A.B.oneVal_oneMk]
      exact (show A.P (b (ψ m) : A.W) = y (ψ m) from (b (ψ m)).2).symm
    have hwN : Tendsto (fun m => N (w m)) atTop (𝓝 0) := by
      refine squeeze_zero (fun m => hNB.nonneg _) (fun m => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop)
      have h2 := hbN (ψ m)
      rw [normW_of_mem N (h1 m)] at h2
      exact h2
    have hw0 := hNB.tendsto_zeroOne w z hwP hwN
    have h3 := (A.B.continuous_oneVal.tendsto _).comp hw0
    rw [A.B.oneVal_zeroOne] at h3
    exact h3.congr fun m => A.B.oneVal_oneMk _ _
  have hgz0 : subSec f (s₀ i) O₂ z = fiberZero A.P z :=
    tendsto_nhds_unique hgz (hb0.congr fun m => (hgb m).symm)
  have hfz : f z = s₀ i z := (isZeroAt_subSec_iff hsec hsi.1 hzO₂).1 hgz0
  have hz0 : 0 < Λ₀ (f z) := by
    have hmem : s₀ i z ∈ suppAt Λ₀ z := by rw [hrep₀.suppAt_eq hzO₂]; exact ⟨i, rfl⟩
    rw [hfz]
    exact hmem.2
  exact hyV _ ((hyz.eventually (hVo.mem_nhds (hSV z hz0))).exists.choose_spec)

/-! ### Achieving global transversality relative to `Λ₀` -/

set_option maxHeartbeats 1600000 in
-- the assembly over a finite cover of `|supp(Λ₀ ∘ f)|`
/-- **"Achieving global transversality" relative to `Λ₀`** (proof of Theorem 15.3.9, steps
(c)–(d), "argue as in Theorem 15.3.7"): R6's `HasParametricGeneralPositionRel A f Λ₀ N U` holds
for tame `X`, an sc-Fredholm section functor `f` with tame germ data, `(N, U)` controlling
compactness and an sc⁺-multisection `Λ₀` with `N(Λ₀) ≤ 1` and `dom-supp(Λ₀) ⊆ U`.  *Proof*: the
local step (`exists_local_paramGP_rel`) at every point of `supp(Λ₀ ∘ f)`; finitely many cover the
compact `|supp(Λ₀ ∘ f)|`; by the relative (15.2) (`exists_pos_supp_rel_subset`) the support of
`(Λ₀ ⊕ Λ_t) ∘ f` lies in the saturation of their union for small `t`; general position at a point
is carried along morphisms (`isInGeneralPositionAt_of_mor`). -/
theorem hasParametricGeneralPositionRel (hX : A.X.IsTame)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hcc : ControlsCompactness A f N U) (hΛ₀ : IsScPlusMultisection A Λ₀)
    (hN₀ : ∀ x, pointwiseNorm N Λ₀ x ≤ 1) (hdom₀ : domSupp Λ₀ ⊆ U) :
    HasParametricGeneralPositionRel A f Λ₀ N U := by
  classical
  intro ℓ Λ hΛ _ hNorm hdom hon
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  obtain ⟨_hfs, hfun⟩ := hf.1
  set S := {x | 0 < Λ₀ (f x)} with hSdef
  have hloc : ∀ z : S, ∃ V : Set A.Obj, IsOpen V ∧ (z : A.Obj) ∈ V ∧
      ∃ δ > (0 : ℝ), ∃ CV : Set (Fin ℓ → ℝ), volume CV = 0 ∧ ∀ t : Fin ℓ → ℝ, ‖t‖ < δ →
        t ∉ CV → ∀ y ∈ V, 0 < multisectionAdd Λ₀ (Λ t) (f y) →
          IsInGeneralPositionAt f (multisectionAdd Λ₀ (Λ t)) y := by
    rintro ⟨z, hz⟩
    have hz1 := mem_levelSet_one_of_pos hf hΛ₀ hz
    have e := A.X.PObj.levelVal_levelMk 1 z hz1
    have h := exists_local_paramGP_rel hX hf hft hΛ₀ hΛ (x₀ := A.X.PObj.levelMk 1 z hz1)
      (hon _ (by rw [e]; exact hz))
    rw [e] at h
    exact h
  choose V hVo hzV δ hδ CV hCV hgp using hloc
  have hK := isCompact_image_supp_comp hf hfc hΛ₀ hcc hN₀ hdom₀
  have hcov : A.X.π '' S ⊆ ⋃ z : S, A.X.π '' V z := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_iUnion.2 ⟨⟨z, hz⟩, z, hzV _, rfl⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun z => A.X.π '' V z)
    (fun z => A.X.proposition_7_1_8 _ (hVo z)) hcov
  set Vs := A.X.saturation (⋃ z ∈ T, V z) with hVs
  have hVso : IsOpen Vs :=
    (A.X.proposition_7_1_8 _ (isOpen_biUnion fun z _ => hVo z)).preimage A.X.continuous_π
  have hVss : A.X.IsSaturated Vs := by
    change A.X.π ⁻¹' (A.X.π '' (A.X.π ⁻¹' (A.X.π '' _))) = A.X.π ⁻¹' (A.X.π '' _)
    rw [image_preimage_eq _ A.X.surjective_π]
  have hSV : ∀ z, 0 < Λ₀ (f z) → z ∈ Vs := by
    intro z hz
    obtain ⟨i, hiT, y, hy, hyz⟩ := mem_iUnion₂.1 (hT ⟨z, hz, rfl⟩)
    exact ⟨y, mem_iUnion₂.2 ⟨i, hiT, hy⟩, hyz⟩
  obtain ⟨ε₀, hε₀, hε₀V⟩ :=
    exists_pos_supp_rel_subset hf hft hcc hΛ₀ hN₀ hdom₀ hΛ hNorm hdom hVso hVss hSV
  have hsum : Tendsto (fun t : Fin ℓ → ℝ => ∑ j, |t j|) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : Fin ℓ → ℝ => ∑ j, |t j|) :=
      continuous_finsetSum _ fun j _ => (continuous_apply j).abs
    simpa using hc.tendsto 0
  have hnorm : Tendsto (fun t : Fin ℓ → ℝ => ‖t‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_norm (E := Fin ℓ → ℝ)).tendsto 0
  have hev : ∀ᶠ t in 𝓝 (0 : Fin ℓ → ℝ), (∀ i ∈ T, ‖t‖ < δ i) ∧ ∑ j, |t j| < ε₀ :=
    ((eventually_all_finset T).2 fun i _ => hnorm.eventually (gt_mem_nhds (hδ i))).and
      (hsum.eventually (gt_mem_nhds hε₀))
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, ?_⟩
  have hCVT : volume (⋃ i ∈ T, CV i) = 0 :=
    (measure_biUnion_null_iff T.countable_toSet).2 fun i _ => hCV i
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hCVT] with t htCV htε
  obtain ⟨htδ, htsum⟩ := hεP (by rwa [dist_zero_right])
  have hΛ' := definition_13_2_9 hΛ₀ (hΛ t)
  rw [isInGeneralPosition_iff_forall_at hf hΛ']
  intro x hpos
  obtain ⟨y, hy, hyx⟩ := hε₀V t htsum x hpos
  obtain ⟨i, hiT, hyi⟩ := mem_iUnion₂.1 hy
  obtain ⟨φ, hφs, hφt⟩ := A.X.π_eq_π_iff.1 hyx
  have hΛφ : multisectionAdd Λ₀ (Λ t) (f (A.X.tgt φ)) =
      multisectionAdd Λ₀ (Λ t) (f (A.X.src φ)) := by
    rw [hfun φ]
    exact hΛ'.1 _
  have hposy : 0 < multisectionAdd Λ₀ (Λ t) (f y) := by
    rw [← hφs, ← hΛφ, hφt]; exact hpos
  have hgy := hgp i t (htδ i hiT) (fun h => htCV (mem_iUnion₂.2 ⟨i, hiT, h⟩)) y hyi hposy
  have h := isInGeneralPositionAt_of_mor hf hΛ' φ (by rw [hφs]; exact hgy)
  rwa [hφt] at h

/-! ### The relative statement and Theorem 15.3.9 with one step left -/

/-- **TX's relative statement (steps (c)–(d) of the proof of Theorem 15.3.9)** from the relative
local families alone (`HasLocalGPFamiliesRel` with domain support in `U ∖ ∂X`, assumed under the
statement's hypotheses); the relative parametric step is `hasParametricGeneralPositionRel`. -/
theorem theorem_15_3_7_relative_of_local
    (H : A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
      ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
        A.E.HasCompactSolutionSetEp f →
      ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
      ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) →
        (∀ x, 0 < h x ∧ h x ≤ 1) →
      ∀ Λ₀ : A.W → ℚ≥0, IsStructurable A Λ₀ → domSupp Λ₀ ⊆ U →
        (∀ x, pointwiseNorm N Λ₀ x < h x) →
        (∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
          0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x) →
        HasLocalGPFamiliesRel A f Λ₀ N (U ∩ A.X.PObj.boundaryᶜ)
          (fun x => h x - pointwiseNorm N Λ₀ x)) :
    theorem_15_3_7_relative_statement A :=
  theorem_15_3_7_relative_of_hyp fun hX hpara hPU f hf hft hS N U hcc h hc hfun hh Λ₀ hΛ₀ hdom
      hN hbd =>
    ⟨H hX hpara hPU f hf hft hS N U hcc h hc hfun hh Λ₀ hΛ₀ hdom hN hbd,
      hasParametricGeneralPositionRel hX hf hft hcc hΛ₀.1
        (fun x => (hN x).le.trans (hh x).2) hdom⟩

/-- **Theorem 15.3.9 (Transversal Extension Theorem), p. 694**, from TY's tame bundle charts
`hB`, the extension statement of Theorem 14.1.9 and the relative local families
(`HasLocalGPFamiliesRel`, assumed under the hypotheses of TX's relative statement).  GL's
extension statement does not hold when `∂X ≠ ∅` (A6), so use `theorem_15_3_9_charged_of_local_rel`
(file `P3W6R6_ChargedExtension`) there. -/
theorem theorem_15_3_9_of_local_rel
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hext : theorem_14_1_9_extension_statement A)
    (H : A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
      ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
        A.E.HasCompactSolutionSetEp f →
      ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
      ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) →
        (∀ x, 0 < h x ∧ h x ≤ 1) →
      ∀ Λ₀ : A.W → ℚ≥0, IsStructurable A Λ₀ → domSupp Λ₀ ⊆ U →
        (∀ x, pointwiseNorm N Λ₀ x < h x) →
        (∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
          0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x) →
        HasLocalGPFamiliesRel A f Λ₀ N (U ∩ A.X.PObj.boundaryᶜ)
          (fun x => h x - pointwiseNorm N Λ₀ x)) :
    theorem_15_3_9_statement A :=
  theorem_15_3_9_of_extension_ty hB hext (theorem_15_3_7_relative_of_local H)

/-- **The remaining hypothesis of `theorem_15_3_7_relative_of_local` is satisfiable** on
`ℝⁿ × ℝ⁰ → ℝⁿ`. -/
theorem theorem_15_3_7_relative_statement_epSEP_zero_of_local (n : ℕ) :
    theorem_15_3_7_relative_statement (StrongBundleEquivalenceExamples.epSEP n 0) :=
  theorem_15_3_7_relative_of_local fun _ _ _ f _ _ _ _ _ hcc _ _ _ _ Λ₀ _ _ _ _ =>
    hasLocalGPFamiliesRel_epSEP_zero n f Λ₀ hcc.1.isAuxNorm _ _

end SBLocalization

end Polyfold
