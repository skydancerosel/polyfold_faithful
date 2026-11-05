import Polyfold.Chapter3.BasicGermLinearization
import Polyfold.Chapter3.SolutionLinearization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
**Proposition 3.10, second statement** (p. 68): the linearization of a basic germ plus an
sc⁺-germ is Fredholm of index `n − N` on every level `m`, at points `(a, w) ∈ E_{m+1}` small in
`E_m`.  Round-trip item V3.12.

# The linearization of a basic germ on level `m`

## The text, paraphrased

Let `f = h + s : O([0,∞)^k ⊕ ℝ^{n−k} ⊕ W, 0) → ℝᴺ ⊕ W` with `h` a basic germ (Definition 3.7,
`h(a, w) = (·, w − B(a, w))`) and `s` an sc⁺-germ.  "Moreover `Df(a, w) : ℝⁿ ⊕ W_m → ℝᴺ ⊕ W_m` is
Fredholm of index `n − N` for `(a, w) ∈ E_{m+1}` small in `E_m`."  Proof (the text's, for the
first statement, applied on level `m`): `Df(a, w)(δa, δw) = (pr_{ℝᴺ}Df(a, w)(δa, δw),
δw − D₂B(a, w)δw − D₁B(a, w)δa + pr_W Ds(a, w)(δa, δw))`; the `ℝᴺ`-component and `D₁B(a, w)δa`
have finite rank, `Ds(a, w)` maps `E_m` to `F_{m+1}` so `ι Ds(a, w)` is compact on level `m`, and
`‖D₂B(a, w)‖_m ≤ ε` by Lemma 3.9 on level `m`.

## What is formalized

* `Polyfold.IsBasicGerm.snd_deriv_add`: on level `0`, at `x ∈ U₁`, the `W`-component of
  `D(h + ι s)(x)` is `δw − DB(x)(δa, δw) + pr_W ι Ds(x)(δa, δw)` (uniqueness of derivatives within
  `U₁`, density of `E₁` in `E₀`).
* `Polyfold.IsBasicGerm.snd_levelDeriv_add`: the same identity for the level-`m` operators
  (`levelDeriv`, Proposition 1.16) at `x ∈ U_{m+1}`, with `pr_W ι Ds(x)` replaced by
  `ι_m ∘ pr_W ∘ Ds(x)_m`, `Ds(x)_m : E_m → F_{m+1}`.
* `Polyfold.IsBasicGerm.levelDeriv_add_eq`: the decomposition `Df(x)_m = T₀ + S(x) + K(x)` on
  level `m`, `T₀(δa, δw) = (0, δw)` (the operator (32), `ScBanach.projWOp`),
  `S(x)(δa, δw) = (0, −D₂B(x)_m δw)`, `K(x)` the rest; `K(x)` is compact
  (`IsBasicGerm.isCompactOperator_levelK`).
* `Polyfold.proposition_3_10_level` (**Proposition 3.10, second statement**, on every level): for
  every `m` there is `δ > 0` such that for every `x ∈ U_{m+1}` with `|ιx|_m < δ` the level-`m`
  operator `Df(x)_m : ℝⁿ ⊕ W_m → ℝᴺ ⊕ W_m` (the bounded operator with `ι_m Df(x)_m v =
  Df(x₁) ι_m v`, `x₁ ∈ U₁` the image of `x`) is Fredholm of index `dim ℝⁿ − dim ℝᴺ`.
* `Polyfold.proposition_3_10_full`: both statements of Proposition 3.10 together.

## What the text leaves implicit, and the choices made (the findings)

* **The text's proof goes through on level `m` as written.**  The only input beyond the level-`0`
  argument is Lemma 3.9 on level `m` (`IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le`,
  smallness of `x` on level `m` only), and the compactness of `F_{m+1} → F_m`.  The small part
  `S(x)` is handled by the stability of the index under small perturbations
  (`isFredholm_fredholmIndex_add_of_norm_lt`, with `ε` chosen against a quasi-inverse of
  `T₀ : E_m → F_m`), a Neumann series argument (equivalently, `1 − D₂B(x)_m` is invertible on
  `W_m` once `‖D₂B(x)_m‖ < 1`).
* The radius `δ` depends on `m` (it is the radius of Lemma 3.9 on level `m` for an `ε` depending on
  a quasi-inverse of `(32)` on level `m`); the text's "small in `E_m`" says the same.
* `x` is a point of `U_{m+1}` (so that `Df(x)` has a level-`m` operator, Proposition 1.16); its
  size on level `m + 1` is not restricted.
* `f(0) = 0` is not used (it is a property of `f`, not of `Df`).  The quadrant hypothesis is the
  one of Lemma 3.9 on level `m` (`IsQuadrantLike` for `C̃`; partial quadrants have it,
  `IsPartialQuadrant.isQuadrantLike`).
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

/-- A continuous linear map with finite-dimensional domain is compact. -/
theorem isCompactOperator_of_finiteDimensional_domain {V Y : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : V →L[ℝ] Y) : IsCompactOperator g := by
  have : FiniteDimensional ℝ (LinearMap.range (g : V →ₗ[ℝ] Y)) :=
    LinearMap.finiteDimensional_range _
  exact isCompactOperator_of_finiteDimensional_range g

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {W : ScBanach}
  {Ct : Set P} {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)}
  {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

local notation "E'" => ScBanach.paramProd P W
local notation "F'" => ScBanach.paramProd Q W

namespace IsBasicGerm

variable (hC : IsQuadrantLike (ScBanach.const P) Ct) {h : P × W 0 → Q × W 0}
  {Bc : P × W 0 → W 0} (hh : IsBasicGerm Ct G h Bc)
  {DB : (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] W 0}
  (hB : IsSc1GermWith (F := W) G Bc DB) {s : P × W 0 → Q × W 1}
  {Ds : (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ]
    (ScBanach.paramProd Q W).shift 0}
  (hs : IsSc1GermWith (F := (ScBanach.paramProd Q W).shift) G s Ds)
  {DF : (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] (ScBanach.paramProd Q W) 0}
  (hF : IsSc1GermWith G (fun x => h x + (ScBanach.paramProd Q W).toBase 1 (s x)) DF)
include hC hh hB hs hF

/-- The `W`-component of `Df(x)`, `f = h + ι s`, at `x ∈ U₁` (proof of Proposition 3.10):
`pr_W Df(x)(δa, δw) = δw − DB(x)(δa, δw) + pr_W ι Ds(x)(δa, δw)`.  Both sides are derivatives
of `pr_W ∘ f = pr_W − B + pr_W ι s` (Definition 3.7, on `U₀`) within `U₁` at `x`; uniqueness
within `U₁` and density of `E₁` in `E₀`. -/
theorem snd_deriv_add {x : (E') 1} (hx : x ∈ G.U 1) (v : (E') 0) :
    (DF x v).2 = v.2 - DB x v + ((F').toBase 1 (Ds x v)).2 := by
  have hCq : IsQuadrantLike (E') (Ct ×ˢ univ) := hC.paramProd W
  set ι₀ : (E') 1 →L[ℝ] (E') 0 := (E').toBase 1 with hι₀
  set A : (E') 0 →L[ℝ] W 0 := (ContinuousLinearMap.snd ℝ Q (W 0)).comp (DF x) with hA
  set A' : (E') 0 →L[ℝ] W 0 := ContinuousLinearMap.snd ℝ P (W 0) - DB x +
    ((ContinuousLinearMap.snd ℝ Q (W 0)).comp ((F').toBase 1)).comp (Ds x) with hA'
  have h1 : HasFDerivWithinAt
      (fun y : (E') 1 => (h (ι₀ y) + (F').toBase 1 (s (ι₀ y))).2) (A.comp ι₀) (G.U 1) x :=
    (hF.hasFDerivWithinAt x hx).snd
  have h2 : HasFDerivWithinAt
      (fun y : (E') 1 => (h (ι₀ y) + (F').toBase 1 (s (ι₀ y))).2) (A'.comp ι₀) (G.U 1) x := by
    have ha : HasFDerivWithinAt (fun y : (E') 1 => (ι₀ y).2)
        ((ContinuousLinearMap.snd ℝ P (W 0)).comp ι₀) (G.U 1) x :=
      ((ContinuousLinearMap.snd ℝ P (W 0)).comp ι₀).hasFDerivAt.hasFDerivWithinAt
    have hb := hB.hasFDerivWithinAt x hx
    have hc := ((ContinuousLinearMap.snd ℝ Q (W 0)).comp
      ((F').toBase 1)).hasFDerivAt.comp_hasFDerivWithinAt x (hs.hasFDerivWithinAt x hx)
    have hsum := (ha.sub hb).add hc
    have heq : A'.comp ι₀ = (ContinuousLinearMap.snd ℝ P (W 0)).comp ι₀ - (DB x).comp ι₀ +
        ((ContinuousLinearMap.snd ℝ Q (W 0)).comp ((F').toBase 1)).comp ((Ds x).comp ι₀) := by
      ext y <;> rfl
    rw [heq]
    refine hsum.congr (fun y hy => ?_) ?_
    · change (h (ι₀ y)).2 + ((F').toBase 1 (s (ι₀ y))).2 =
        (ι₀ y).2 - Bc (ι₀ y) + ((F').toBase 1 (s (ι₀ y))).2
      rw [hh.snd_eq _ (G.toBase_mem hy)]
    · change (h (ι₀ x)).2 + ((F').toBase 1 (s (ι₀ x))).2 =
        (ι₀ x).2 - Bc (ι₀ x) + ((F').toBase 1 (s (ι₀ x))).2
      rw [hh.snd_eq _ (G.toBase_mem hx)]
  have heq := (G.uniqueDiffWithinAt hCq 1 hx).eq h1 h2
  have hAA' : A = A' := ContinuousLinearMap.ext_of_comp_toBase_one heq
  have := DFunLike.congr_fun hAA' v
  simpa [hA, hA'] using this

/-- **The `W`-component of `Df(x)` on level `m`**: for `x ∈ U_{m+1}` and `v ∈ E_m`,
`pr_W Df(x)_m v = pr_W v − DB(x)_m v + ι_m pr_W Ds(x)_m v`, where `Df(x)_m`, `DB(x)_m` and
`Ds(x)_m : E_m → F_{m+1}` are the level-`m` operators (`levelDeriv`, Proposition 1.16).  From
`snd_deriv_add` at the level-`1` image of `x`, through the injectivity of `ι_m : W_m → W₀`. -/
theorem snd_levelDeriv_add {m : ℕ} {x : (E') (m + 1)} (hx : x ∈ G.U (m + 1)) (v : (E') m) :
    (levelDeriv DF m x v).2 =
      v.2 - levelDeriv DB m x v + W.incl m (levelDeriv Ds m x v).2 := by
  have hx₁ : (E').shift.toBase m x ∈ G.U 1 := G.shift_toBase_mem hx
  apply W.toBase_injective m
  have hL : W.toBase m (levelDeriv DF m x v).2 =
      (DF ((E').shift.toBase m x) ((E').toBase m v)).2 := by
    have := congrArg Prod.snd (hF.toBase_levelDeriv hx v)
    rwa [ScBanach.paramProd_toBase] at this
  have hLB := hB.toBase_levelDeriv hx v
  have hLs := hs.toBase_levelDeriv hx v
  have h0 := hh.snd_deriv_add hC hB hs hF hx₁ ((E').toBase m v)
  have hι : ∀ y : (F').shift m,
      ((F').toBase 1 ((F').shift.toBase m y)).2 = W.toBase m (W.incl m y.2) := fun y => by
    rw [← ScBanach.shift_toBase, ScBanach.paramProd_toBase]
    rfl
  have hv : ((E').toBase m v).2 = W.toBase m v.2 := by rw [ScBanach.paramProd_toBase]
  rw [hL, h0, map_add, map_sub, hLB, ← hLs, hι, hv]

/-- The finite-rank and compact part `K(x)` of the level-`m` operator `Df(x)_m` (proof of
Proposition 3.10): `K(x)(δa, δw) = (pr_{ℝᴺ} Df(x)_m(δa, δw), −DB(x)_m(δa, 0) +
ι_m pr_W Ds(x)_m(δa, δw))`. -/
def levelK (DF : (E') 1 → (E') 0 →L[ℝ] (F') 0) (DB : (E') 1 → (E') 0 →L[ℝ] W 0)
    (Ds : (E') 1 → (E') 0 →L[ℝ] (F').shift 0) (m : ℕ) (x : (E') (m + 1)) :
    (E') m →L[ℝ] (F') m :=
  (ContinuousLinearMap.inl ℝ Q (W m)).comp
      ((ContinuousLinearMap.fst ℝ Q (W m)).comp (levelDeriv DF m x)) -
    ((ContinuousLinearMap.inr ℝ Q (W m)).comp
      ((levelDeriv DB m x).comp (ContinuousLinearMap.inl ℝ P (W m)))).comp
      (ContinuousLinearMap.fst ℝ P (W m)) +
    ((ContinuousLinearMap.inr ℝ Q (W m)).comp (W.incl m)).comp
      ((ContinuousLinearMap.snd ℝ Q (W (m + 1))).comp (levelDeriv Ds m x))

/-- The small part `S(x)(δa, δw) = (0, −D₂B(x)_m δw)` of the level-`m` operator `Df(x)_m`. -/
def levelS (DB : (E') 1 → (E') 0 →L[ℝ] W 0) (m : ℕ) (x : (E') (m + 1)) :
    (E') m →L[ℝ] (F') m :=
  -((ContinuousLinearMap.inr ℝ Q (W m)).comp
    (((levelDeriv DB m x).comp (ContinuousLinearMap.inr ℝ P (W m))).comp
      (ContinuousLinearMap.snd ℝ P (W m))))

omit hC hh hB hs hF in
lemma levelS_apply (DB : (E') 1 → (E') 0 →L[ℝ] W 0) (m : ℕ) (x : (E') (m + 1)) (v : (E') m) :
    levelS (Q := Q) DB m x v = ((0 : Q), -(levelDeriv DB m x ((0 : P), v.2))) := by
  simp only [levelS, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_snd', Prod.neg_mk, neg_zero]

/-- **The decomposition of `Df(x)_m`** (proof of Proposition 3.10, on level `m`):
`Df(x)_m = T₀ + S(x) + K(x)` with `T₀(δa, δw) = (0, δw)` (the operator (32) on level `m`),
`S(x)(δa, δw) = (0, −D₂B(x)_m δw)` and `K(x)` of finite rank plus compact. -/
theorem levelDeriv_add_eq {m : ℕ} {x : (E') (m + 1)} (hx : x ∈ G.U (m + 1)) :
    levelDeriv DF m x =
      ScBanach.projWOp P W Q m + levelS (Q := Q) DB m x + levelK DF DB Ds m x := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h2 := hh.snd_levelDeriv_add hC hB hs hF hx v
  have hlin : levelDeriv DB m x v =
      levelDeriv DB m x (v.1, (0 : W m)) + levelDeriv DB m x ((0 : P), v.2) := by
    rw [← map_add]; simp
  rw [add_apply, add_apply, levelS_apply, ScBanach.projWOp_apply]
  refine Prod.ext ?_ ?_
  · simp [levelK]
  · simp only [levelK, add_apply, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.snd_add, Prod.snd_sub]
    rw [h2, hlin]
    abel

omit hC hh hB hs hF in
/-- `K(x)` is compact: the `ℝᴺ`-component and `(δa, δw) ↦ (0, DB(x)_m(δa, 0))` have finite rank
(through `ℝᴺ` and `ℝⁿ`), and `ι_m ∘ pr_W ∘ Ds(x)_m` factors through the compact inclusion
`W_{m+1} → W_m`. -/
theorem isCompactOperator_levelK (DF : (E') 1 → (E') 0 →L[ℝ] (F') 0)
    (DB : (E') 1 → (E') 0 →L[ℝ] W 0) (Ds : (E') 1 → (E') 0 →L[ℝ] (F').shift 0) (m : ℕ)
    (x : (E') (m + 1)) : IsCompactOperator (levelK DF DB Ds m x) := by
  have h1 : IsCompactOperator ((ContinuousLinearMap.inl ℝ Q (W m)).comp
      ((ContinuousLinearMap.fst ℝ Q (W m)).comp (levelDeriv DF m x))) :=
    (isCompactOperator_of_finiteDimensional_domain (ContinuousLinearMap.inl ℝ Q (W m))).comp_clm _
  have h2 : IsCompactOperator (((ContinuousLinearMap.inr ℝ Q (W m)).comp
      ((levelDeriv DB m x).comp (ContinuousLinearMap.inl ℝ P (W m)))).comp
      (ContinuousLinearMap.fst ℝ P (W m))) :=
    (isCompactOperator_of_finiteDimensional_domain ((ContinuousLinearMap.inr ℝ Q (W m)).comp
      ((levelDeriv DB m x).comp (ContinuousLinearMap.inl ℝ P (W m))))).comp_clm
      (ContinuousLinearMap.fst ℝ P (W m))
  have h3 : IsCompactOperator (((ContinuousLinearMap.inr ℝ Q (W m)).comp (W.incl m)).comp
      ((ContinuousLinearMap.snd ℝ Q (W (m + 1))).comp (levelDeriv Ds m x))) :=
    ((W.incl_isCompactOperator m).clm_comp (ContinuousLinearMap.inr ℝ Q (W m))).comp_clm _
  exact (h1.sub h2).add h3

end IsBasicGerm

/-! ### Proposition 3.10, second statement -/

/-- **Proposition 3.10, second statement** (round-trip item V3.12): let `h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`
be a basic germ (Definition 3.7, `h = (·, w − B(a, w))` on `U₀`), `s` an sc⁺-germ (sc¹ into
`(ℝᴺ ⊕ W)¹`, derivative `Ds`) and `f = h + s` sc¹ with derivative `Df`.  Then for every level `m`
there is `δ > 0` such that for every `x ∈ U_{m+1}` with `|ιx|_m < δ` the level-`m` operator
`Df(x)_m : ℝⁿ ⊕ W_m → ℝᴺ ⊕ W_m` — the bounded operator `levelDeriv Df m x` with
`ι_m Df(x)_m v = Df(x₁) ι_m v`, `x₁ ∈ U₁` the level-`1` point with the image of `x` — is Fredholm
of index `dim ℝⁿ − dim ℝᴺ`.  Proof (the text's): `Df(x)_m = T₀ + S(x) + K(x)`
(`IsBasicGerm.levelDeriv_add_eq`), `T₀ = (32)` is Fredholm of index `n − N` on level `m`,
`‖S(x)‖ ≤ ε` by Lemma 3.9 on level `m` (so `T₀ + S(x)` is Fredholm of the same index), and `K(x)`
is compact. -/
theorem proposition_3_10_level (hC : IsQuadrantLike (ScBanach.const P) Ct)
    {h : P × W 0 → Q × W 0} {Bc : P × W 0 → W 0} (hh : IsBasicGerm Ct G h Bc)
    {s : P × W 0 → Q × W 1} {Ds : (E') 1 → (E') 0 →L[ℝ] (F').shift 0}
    (hs : IsSc1GermWith (F := (F').shift) G s Ds) {DF : (E') 1 → (E') 0 →L[ℝ] (F') 0}
    (hF : IsSc1GermWith G (fun x => h x + (F').toBase 1 (s x)) DF) (m : ℕ) :
    ∃ δ > 0, ∀ x ∈ G.U (m + 1), ‖(E').incl m x‖ < δ →
      (∀ v : (E') m, (F').toBase m (levelDeriv DF m x v) =
        DF ((E').shift.toBase m x) ((E').toBase m v)) ∧
      (levelDeriv DF m x).IsFredholm ∧
      fredholmIndex (levelDeriv DF m x) = finrank ℝ P - finrank ℝ Q := by
  set DB := scDerivGerm (F := W) G Bc with hDB
  have hB : IsSc1GermWith (F := W) G Bc DB :=
    ((hh.B_isScSmoothGerm hC) 1).1.isSc1GermWith_scDerivGerm
  -- the operator (32) on level `m`: Fredholm of index `n − N`, with a quasi-inverse `q`
  obtain ⟨hT₀F, hT₀I⟩ := (ScBanach.isScFredholm_projWOp P W Q).fredholmIndex_lvl m
  rw [ScBanach.scIndex_projWOp] at hT₀I
  obtain ⟨q, hq⟩ := hT₀F.exists_isQuasiInverse
  -- Lemma 3.9 on level `m` with `ε = 1/(‖q‖ + 1)`
  obtain ⟨r, hr, h39⟩ := hh.contraction.exists_norm_levelDeriv_snd_le hC hB
    (ε := 1 / (‖q‖ + 1)) (by positivity) m
  refine ⟨r, hr, fun x hx hxr => ⟨fun v => hF.toBase_levelDeriv hx v, ?_⟩⟩
  have hS : ‖IsBasicGerm.levelS (Q := Q) DB m x‖ ≤ 1 / (‖q‖ + 1) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [IsBasicGerm.levelS_apply, Prod.norm_mk, norm_zero, norm_neg]
    exact max_le (by positivity)
      ((h39 x hx hxr v.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le v) (by positivity)))
  have hsmall : ‖q‖ * ‖IsBasicGerm.levelS (Q := Q) DB m x‖ < 1 := by
    calc ‖q‖ * ‖IsBasicGerm.levelS (Q := Q) DB m x‖ ≤ ‖q‖ * (1 / (‖q‖ + 1)) :=
          mul_le_mul_of_nonneg_left hS (norm_nonneg _)
      _ < 1 := by rw [mul_one_div, div_lt_one (by positivity)]; linarith
  obtain ⟨hF1, hI1⟩ := isFredholm_fredholmIndex_add_of_norm_lt hq hsmall
  have hK := IsBasicGerm.isCompactOperator_levelK DF DB Ds m x
  rw [hh.levelDeriv_add_eq hC hB hs hF hx]
  exact ⟨isFredholm_add_isCompactOperator hF1 hK,
    by rw [fredholmIndex_add_isCompactOperator hF1 hK, hI1, hT₀I]⟩

/-- **Proposition 3.10** (both statements; round-trip item V3.12): for a basic germ `h`, an
sc⁺-germ `s` and `f = h + s` sc¹ with derivative `Df`, (1) `Df(0)` is an sc-operator which is
sc-Fredholm of index `n − N` (`proposition_3_10`), and (2) on every level `m`, `Df(x)_m` is
Fredholm of index `n − N` for `x ∈ U_{m+1}` small on level `m` (`proposition_3_10_level`). -/
theorem proposition_3_10_full (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    {h : P × W 0 → Q × W 0} {Bc : P × W 0 → W 0} (hh : IsBasicGerm Ct G h Bc)
    {s : P × W 0 → Q × W 1} {Ds : (E') 1 → (E') 0 →L[ℝ] (F').shift 0}
    (hs : IsSc1GermWith (F := (F').shift) G s Ds) {DF : (E') 1 → (E') 0 →L[ℝ] (F') 0}
    (hF : IsSc1GermWith G (fun x => h x + (F').toBase 1 (s x)) DF) :
    (∃ hop : IsScOperator (DF 0), IsScFredholm hop.toScOperator ∧
      scIndex hop.toScOperator = finrank ℝ P - finrank ℝ Q) ∧
    ∀ m : ℕ, ∃ δ > 0, ∀ x ∈ G.U (m + 1), ‖(E').incl m x‖ < δ →
      (∀ v : (E') m, (F').toBase m (levelDeriv DF m x v) =
        DF ((E').shift.toBase m x) ((E').toBase m v)) ∧
      (levelDeriv DF m x).IsFredholm ∧
      fredholmIndex (levelDeriv DF m x) = finrank ℝ P - finrank ℝ Q :=
  ⟨proposition_3_10 hC hh hs hF, proposition_3_10_level hC.isQuadrantLike hh hs hF⟩

end Polyfold
