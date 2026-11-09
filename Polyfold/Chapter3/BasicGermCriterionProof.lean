import Polyfold.Chapter3.BasicGermCriterion
import Polyfold.Chapter3.FredholmGermLinearization

/-!
# The basic germ criterion (Theorem 3.7.1 (preprint 3.58)), given the family of sc-isomorphisms

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I*, §3.7, **Theorem 3.7.1 (preprint 3.58)** (basic germ
criterion): let `U` be a relatively open neighbourhood of `0` in the partial quadrant `C` of the
sc-Banach space `E` and `f : U → F` sc-smooth with (1) `Df(x)` sc-Fredholm of constant index at
smooth points, (2) an sc-splitting `E = B ⊕ X`, `B` finite-dimensional containing `ker Df(0)`,
`X ⊆ C`, with the compactness property, and (3) the estimate
`|[D₂f(b, 0) − D₂f(b, x)]h|_m ≤ ε|h|_m` for `b` small and `x ∈ X_{m+1}` small on level `m`.  Then
`f − f(0)` is conjugated near `0` to a basic germ.

The text's proof first produces, from (1) and (2) (Lemmas 3.7.2, 3.7.3 (preprint 3.59, 3.60) and the index argument), the
family `b ↦ L(b) = P ∘ Df(b)|X : X → Y` of sc-isomorphisms with uniform lower bounds
`|L(b)h|_m ≥ c_m|h|_m` on a neighbourhood of `0`, and then proves the theorem from this family
and (3).  This file formalizes the second half, **in the coordinates of the text's proof**
(`B = ℝⁿ`, `E = ℝⁿ ⊕ X`, `C = C̃ ⊕ X`, `A = ℝᴺ`, `F = ℝᴺ ⊕ Y` with `Y = Df(0)X`):
`Polyfold.theorem_3_7_1_of_family`.  The first half (the family from (1), (2)) is in
`BasicGermCriterionIndex.lean`.

## Main results

* `Polyfold.norm_sub_sub_le_of_hasFDerivWithinAt_segment`: the mean value inequality along a segment
  with the derivative bound in a weaker norm (the text's integral
  `∫₀¹ D₂f(b, tx + (1 − t)x')(x − x') dt` in `F_m`).
* `Polyfold.DerivCondition`: condition (3) of Theorem 3.7.1 (preprint 3.58) in coordinates.
* `Polyfold.contrMap358_contraction`: the contraction estimate
  `|H(b, x) − H(b, x')|_m ≤ ε|x − x'|_m` for `H(b, x) = x − L(b)⁻¹P h(b, x)`, first for
  `x, x' ∈ X_{m+1}` and then by density for `x, x' ∈ X_m`.
* `Polyfold.IsSckGerm.isSck_ofSet`, `Polyfold.IsScSmoothGerm.isScSmooth_ofSet`: a germ on the
  special germ `ofSet U` is an sc^k (sc-smooth) map on `U` (the converse of `IsSck.isSckGerm`).
* `Polyfold.fiberIsoMap_isStrongBundleIso`: the fibre map
  `Φ((b, x), (c, y)) = ((b, x), (c, L(b)⁻¹y))` is a strong bundle isomorphism
  `U' ◁ (ℝᴺ ⊕ Y) → U' ◁ (ℝᴺ ⊕ X)` covering the identity (sc-smoothness from Lemma 3.7.4 (preprint 3.61),
  `famInv_isScSmooth_of`; the shifted structure through the shifted family `shiftFam`).
* `Polyfold.theorem_3_7_1_of_family`: the push-forward `k = Φ_*(f − f(0))` is a basic germ with
  contraction map `H`, and `f − f(0)` is conjugated near `0` to a basic germ
  (`IsConjugateToBasicGerm`).

## Remarks on the text

* Condition (3) is stated with `x ∈ X_{m+1}` but the smallness `|x|_m < r` and the estimate in the
  level-`m` norm of `h`; the mean value inequality for `h(b, ·) : X_{m+1} → F_m` (Proposition 1.2.1 (preprint 1.16))
  therefore has to be taken along the segment with the derivative bound in the norm of
  `X_m`, not of `X_{m+1}` (Finding 73); here the one-dimensional mean value inequality for
  `t ↦ h(b, x' + t(x − x')) − L(b)(x' + t(x − x'))` on `[0, 1]`.
* The text's "the map `(b, x) ↦ H(b, x)` is sc-smooth, therefore by the density of `X_{m+1}` in
  `X_m`" is the continuity of `H_m` on `U'_m` (`IsSc0`) and a sequence argument.
* The strong bundle map `Φ` is sc-smooth on `U' ◁ (ℝᴺ ⊕ Y)` and on `(U' ◁ (ℝᴺ ⊕ Y))[1]` (Definition
  2.47); the second is Lemma 3.7.4 (preprint 3.61) for the shifted family `L(b) : X¹ → Y¹` ("if we raise the index
  by one, then the map ... is also sc-smooth by Proposition 1.17").
* `U` is replaced by `U' = U ∩ (Vo ⊕ X)` so that `(b, x) ∈ U'` implies `b ∈ O = Vo ∩ C̃`
  ("replacing, if necessary, the relatively open neighbourhood `U ⊂ C` of `0` by a smaller one").
-/

open Set Filter Topology Function Metric

noncomputable section

namespace Polyfold

/-! ### A mean value inequality along a segment, with the derivative bound in a weaker norm -/

/-- **The mean value inequality of the proof of Theorem 3.7.1 (preprint 3.58)** (the text's
`h(b, x) − h(b, x') = ∫₀¹ D₂f(b, tx + (1 − t)x')(x − x') dt`): let `g : E₁ → F` be differentiable
on the convex set `S` with derivative `D(z) ∘ ι`, where `ι : E₁ → E₀` is continuous linear (the
inclusion `E_{m+1} → E_m`) and `D(z) : E₀ → F`, and suppose `‖(D(z) − T)v‖ ≤ ε‖v‖` for `z ∈ S` and
`v ∈ E₀`.  Then `‖g(x) − g(x') − T(ι(x − x'))‖ ≤ ε‖ι(x − x')‖` for `x, x' ∈ S`: the increment is
measured in the norm of `E₀`, not of `E₁`.  Proof: the one-dimensional mean value inequality for
`t ↦ g(x' + t(x − x')) − T(ι(x' + t(x − x')))` on `[0, 1]`. -/
theorem norm_sub_sub_le_of_hasFDerivWithinAt_segment {E₁ E₀ F : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : E₁ → F} {S : Set E₁} (hS : Convex ℝ S) {ι : E₁ →L[ℝ] E₀}
    {D : E₁ → E₀ →L[ℝ] F} {T : E₀ →L[ℝ] F} (hg : ∀ z ∈ S, HasFDerivWithinAt g ((D z).comp ι) S z)
    {ε : ℝ} (hD : ∀ z ∈ S, ∀ v, ‖D z v - T v‖ ≤ ε * ‖v‖) {x x' : E₁} (hx : x ∈ S) (hx' : x' ∈ S) :
    ‖g x - g x' - T (ι (x - x'))‖ ≤ ε * ‖ι (x - x')‖ := by
  set c : ℝ → E₁ := fun t => x' + t • (x - x') with hc
  have hcS : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ S := fun t ht => by
    have := hS.add_smul_sub_mem hx' hx ht
    simpa [hc] using this
  have hcd : ∀ t, HasDerivAt c (x - x') t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => t • (x - x')) ((1 : ℝ) • (x - x')) t :=
      (hasDerivAt_id' t).smul_const (x - x')
    rw [one_smul] at h1
    exact h1.const_add x'
  set γ : ℝ → F := fun t => g (c t) - T (ι (c t)) with hγ
  have hγd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt γ (D (c t) (ι (x - x')) - T (ι (x - x'))) (Icc 0 1) t := by
    intro t ht
    have h1 : HasDerivWithinAt (g ∘ c) ((D (c t)).comp ι (x - x')) (Icc 0 1) t :=
      (hg (c t) (hcS t ht)).comp_hasDerivWithinAt t (hcd t).hasDerivWithinAt hcS
    have h2 : HasDerivWithinAt (fun t => T (ι (c t))) (T (ι (x - x'))) (Icc 0 1) t :=
      ((T.comp ι).hasFDerivAt.comp_hasDerivWithinAt t (hcd t).hasDerivWithinAt)
    exact h1.sub h2
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖D (c t) (ι (x - x')) - T (ι (x - x'))‖ ≤ ε * ‖ι (x - x')‖ :=
    fun t ht => hD (c t) (hcS t (Ico_subset_Icc_self ht)) _
  have := norm_image_sub_le_of_norm_deriv_le_segment' hγd hbound 1 ⟨zero_le_one, le_rfl⟩
  rw [sub_zero, mul_one] at this
  have e1 : γ 1 = g x - T (ι x) := by simp [hγ, hc]
  have e0 : γ 0 = g x' - T (ι x') := by simp [hγ, hc]
  rw [e1, e0] at this
  convert this using 2
  rw [map_sub, map_sub]
  abel

/-! ### The setting of Theorem 3.7.1 (preprint 3.58) in coordinates -/

section Setting

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] {X Y : ScBanach} {Ct : Set P}

local notation "𝔼" => ScBanach.paramProd P X
local notation "𝔽" => ScBanach.paramProd Q Y

variable (Ct) in
/-- **Condition (3) of Theorem 3.7.1 (preprint 3.58)**, in the coordinates `E = ℝⁿ ⊕ X`: for every level `m` and
`ε > 0` there is `r > 0` such that `|[D₂f(b, 0) − D₂f(b, x)]h|_m ≤ ε|h|_m` for all `h ∈ X_m`, all
`b ∈ C̃` with `|b| < r` and all `x ∈ X_{m+1}` with `|x|_m < r` (both `(b, 0)` and `(b, x)` in `U`).
Here `D₂f(b, x)h = Df(b, x)(0, h)` on level `m` is the level operator `levelDeriv`. -/
def DerivCondition (U : Set (𝔼 0)) (f : 𝔼 0 → 𝔽 0) : Prop :=
  ∀ m : ℕ, ∀ ε > 0, ∃ r > 0, ∀ b ∈ Ct, ‖b‖ < r →
    ∀ x : X (m + 1), ((b, 0) : P × X (m + 1)) ∈ (𝔼).lvlSet U (m + 1) →
      ((b, x) : P × X (m + 1)) ∈ (𝔼).lvlSet U (m + 1) → ‖X.incl m x‖ < r → ∀ h : X m,
      ‖levelDeriv (scDeriv (E := 𝔼) (F := 𝔽) U f) m ((b, 0) : P × X (m + 1)) ((0 : P), h) -
        levelDeriv (scDeriv (E := 𝔼) (F := 𝔽) U f) m ((b, x) : P × X (m + 1)) ((0 : P), h)‖ ≤ ε * ‖h‖

-- (section variables must not be declared through the local notation: Lean then silently drops
-- every declaration using them)
variable {U : Set ((ScBanach.paramProd P X) 0)}
  {f : (ScBanach.paramProd P X) 0 → (ScBanach.paramProd Q Y) 0} {L : P → ScIso X Y} {O : Set P}

/-- The germ `h = f − f(0)` of the proof of Theorem 3.7.1 (preprint 3.58). -/
def shiftedGerm (f : 𝔼 0 → 𝔽 0) : 𝔼 0 → 𝔽 0 := fun x => f x - f 0

/-- The push-forward germ `k = Φ_*(h)`, `k(b, x) = ((1 − P)h(b, x), L(b)⁻¹ P h(b, x))`. -/
def pushGerm358 (L : P → ScIso X Y) (f : 𝔼 0 → 𝔽 0) : 𝔼 0 → (ScBanach.paramProd Q X) 0 :=
  fun x => ((f x - f 0).1, (L x.1 0).symm (f x - f 0).2)

/-- The contraction map `H(b, x) = x − L(b)⁻¹ P h(b, x)` of the proof of Theorem 3.7.1 (preprint 3.58). -/
def contrMap358 (L : P → ScIso X Y) (f : 𝔼 0 → 𝔽 0) : 𝔼 0 → X 0 :=
  fun x => x.2 - (L x.1 0).symm (f x - f 0).2

lemma pushGerm358_snd (x : 𝔼 0) : (pushGerm358 L f x).2 = x.2 - contrMap358 L f x := by
  show _ = x.2 - (x.2 - _)
  rw [sub_sub_cancel]
  rfl

/-- The level-`m` operator `Df(b, 0)(0, ·)` has `Y`-component `L(b)_m` when `L(b) = P ∘ D₂f(b, 0)|X`
on level `0`. -/
lemma snd_levelDeriv_eq_L (hf : IsScSmooth U f)
    (hL : ∀ b ∈ O, ∀ h : X 0, L b 0 h = (scDeriv (E := 𝔼) (F := 𝔽) U f ((b, 0) : P × X 1) ((0 : P), h)).2)
    {m : ℕ} {b : P} (hb : b ∈ O) (hbU : ((b, 0) : P × X (m + 1)) ∈ (𝔼).lvlSet U (m + 1))
    (v : X m) : (levelDeriv (scDeriv (E := 𝔼) (F := 𝔽) U f) m ((b, 0) : P × X (m + 1)) ((0 : P), v)).2 = L b m v := by
  apply Y.toBase_injective m
  have h1 := hf.isSc1.isSc1With_scDeriv.toBase_levelDeriv hbU ((0 : P), v)
  have h2 := congrArg Prod.snd h1
  rw [ScBanach.paramProd_toBase] at h2
  simp only at h2
  rw [h2, ScBanach.paramProd_shift_toBase, ScBanach.paramProd_toBase, map_zero,
    (L b).toBase_comm, hL b hb]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- `L(b)⁻¹` on level `m` is bounded by `c_m⁻¹`. -/
lemma norm_symm_le {m : ℕ} {c : ℝ} (hc0 : 0 < c) {b : P} (hcm : ∀ h : X m, c * ‖h‖ ≤ ‖L b m h‖)
    (u : Y m) : ‖(L b m).symm u‖ ≤ c⁻¹ * ‖u‖ := by
  rw [le_inv_mul_iff₀ hc0]
  have := hcm ((L b m).symm u)
  rwa [ContinuousLinearEquiv.apply_symm_apply] at this

/-- The level-`m` map of the contraction map `H`: `H_m(b, w) = w − L(b)_m⁻¹((f_m(b, w))₂ − c_m)`,
`c_m` the level-`m` lift of `(f(0))₂`. -/
lemma levelMap_contrMap358 (hf : IsScSmooth U f) (h0 : (0 : 𝔼 0) ∈ U) {m : ℕ} {b : P} {w : X m}
    (hbw : ((b, w) : P × X m) ∈ (𝔼).lvlSet U m) :
    levelMap (E := 𝔼) (F := X) (contrMap358 L f) m (b, w) =
      w - (L b m).symm ((levelMap (E := 𝔼) (F := 𝔽) f m (b, w)).2 - (levelMap (E := 𝔼) (F := 𝔽) f m 0).2) := by
  have h0m : (0 : 𝔼 m) ∈ (𝔼).lvlSet U m := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  apply levelMap_eq_of_toBase_eq
  rw [map_sub, (L b).symm_toBase_comm, map_sub]
  have e1 := congrArg Prod.snd (hf.isSc1.isSc0.toBase_levelMap hbw)
  have e2 := congrArg Prod.snd (hf.isSc1.isSc0.toBase_levelMap h0m)
  rw [ScBanach.paramProd_toBase] at e1 e2
  simp only at e1 e2
  rw [e1, e2, map_zero, ScBanach.paramProd_toBase]
  simp only [contrMap358, Prod.snd_sub]


/-- The level-`m` germ of neighbourhoods of the proof: `(a, z) ∈ U_m` for `a ∈ C̃` and `z ∈ X_m`
small, with `U = V ∩ (C̃ ⊕ X)` and the ball `B(0, ρ) ⊆ V`. -/
lemma mem_lvlSet_of_small {V : Set (𝔼 0)} (hUV : U = V ∩ (Ct ×ˢ univ)) {ρ : ℝ}
    (hρV : ball (0 : 𝔼 0) ρ ⊆ V) {m : ℕ} {a : P} (ha : a ∈ Ct) (har : ‖a‖ < ρ) {z : X m}
    (hz : ‖X.toBase m z‖ < ρ) : ((a, z) : P × X m) ∈ (𝔼).lvlSet U m := by
  rw [ScBanach.mem_lvlSet, ScBanach.paramProd_toBase, hUV]
  refine ⟨hρV ?_, ha, mem_univ _⟩
  rw [mem_ball_zero_iff, Prod.norm_def]
  exact max_lt har hz

/-- **The contraction estimate of the proof of Theorem 3.7.1 (preprint 3.58)**: for every level `m` and `ε > 0`,
`|H(b, x) − H(b, x')|_m ≤ ε|x − x'|_m` for `b ∈ C̃` small and `x, x' ∈ X_m` small, where
`H(b, x) = x − L(b)⁻¹P h(b, x)`.  Proof: for `x, x' ∈ X_{m+1}`,
`H(b, x) − H(b, x') = L(b)⁻¹[L(b)(x − x') − P(h(b, x) − h(b, x'))]` and the bracket is bounded by
`ε c_m|x − x'|_m` through the mean value inequality along the segment (condition (3) bounds the
derivative in the level-`m` norm, `norm_sub_sub_le_of_hasFDerivWithinAt_segment`); the estimate
extends to `x, x' ∈ X_m` by the density of `X_{m+1}` in `X_m` and the continuity of `H_m`. -/
theorem contrMap358_contraction (hU : IsRelOpenInQuadrant 𝔼 (Ct ×ˢ univ) U) (h0 : (0 : 𝔼 0) ∈ U)
    (hf : IsScSmooth U f) {Vo : Set P} (hVo : IsOpen Vo) (hVo0 : (0 : P) ∈ Vo)
    (hL : ∀ b ∈ Vo ∩ Ct, ∀ h : X 0,
      L b 0 h = (scDeriv (E := 𝔼) (F := 𝔽) U f ((b, 0) : P × X 1) ((0 : P), h)).2)
    (hc : ∀ m, ∃ c > 0, ∀ b ∈ Vo ∩ Ct, ∀ h : X m, c * ‖h‖ ≤ ‖L b m h‖)
    (h3 : DerivCondition Ct U f)
    (hBcont : ∀ m, ContinuousOn (levelMap (E := 𝔼) (F := X) (contrMap358 L f) m)
      ((𝔼).lvlSet (U ∩ Vo ×ˢ univ) m))
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ r > 0, ∀ a ∈ Ct, ‖a‖ < r → ∀ w w' : X m, ‖w‖ < r → ‖w'‖ < r →
      ((a, w) : P × X m) ∈ (𝔼).lvlSet (U ∩ Vo ×ˢ univ) m ∧
      ‖levelB (contrMap358 L f) m (a, w) - levelB (contrMap358 L f) m (a, w')‖ ≤ ε * ‖w - w'‖ := by
  obtain ⟨c, hc0, hcm⟩ := hc m
  obtain ⟨r₃, hr₃, h3'⟩ := h3 m (ε * c) (by positivity)
  obtain ⟨V, hVopen, hUV⟩ := hU.relOpen
  have h0V : (0 : 𝔼 0) ∈ V := (hUV ▸ h0).1
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hVopen 0 h0V
  obtain ⟨ρ', hρ', hρ'Vo⟩ := Metric.isOpen_iff.1 hVo 0 hVo0
  set K : ℝ := ‖X.toBase m‖ + 1 with hK
  have hKpos : 0 < K := by positivity
  set r : ℝ := min (min r₃ ρ') (min ρ (ρ / K)) with hr
  have hrpos : 0 < r := by positivity
  have hrr₃ : r ≤ r₃ := (min_le_left _ _).trans (min_le_left _ _)
  have hrρ' : r ≤ ρ' := (min_le_left _ _).trans (min_le_right _ _)
  have hrρ : r ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hrρK : r ≤ ρ / K := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, hrpos, ?_⟩
  intro a ha har w w' hw hw'
  have haVo : a ∈ Vo := hρ'Vo (by rw [mem_ball_zero_iff]; exact har.trans_le hrρ')
  have haO : a ∈ Vo ∩ Ct := ⟨haVo, ha⟩
  -- the level-`m` norm of `toBase z` is small when `z` is
  have htb : ∀ z : X m, ‖z‖ < r → ‖X.toBase m z‖ < ρ := fun z hz =>
    calc ‖X.toBase m z‖ ≤ ‖X.toBase m‖ * ‖z‖ := (X.toBase m).le_opNorm z
      _ ≤ K * ‖z‖ := by gcongr; rw [hK]; linarith
      _ < K * (ρ / K) := by gcongr; exact hz.trans_le hrρK
      _ = ρ := by field_simp
  have hmemU : ∀ z : X m, ‖z‖ < r → ((a, z) : P × X m) ∈ (𝔼).lvlSet U m := fun z hz =>
    mem_lvlSet_of_small hUV hρV ha (har.trans_le hrρ) (htb z hz)
  have hmem : ∀ z : X m, ‖z‖ < r → ((a, z) : P × X m) ∈ (𝔼).lvlSet (U ∩ Vo ×ˢ univ) m :=
    fun z hz => by
      rw [ScBanach.lvlSet_inter]
      exact ⟨hmemU z hz, by rw [ScBanach.mem_lvlSet, ScBanach.paramProd_toBase]; exact ⟨haVo, mem_univ _⟩⟩
  have hmem1 : ∀ z : X (m + 1), ‖X.incl m z‖ < r →
      ((a, z) : P × X (m + 1)) ∈ (𝔼).lvlSet U (m + 1) := fun z hz => hmemU (X.incl m z) hz
  have hmem10 : ((a, 0) : P × X (m + 1)) ∈ (𝔼).lvlSet U (m + 1) :=
    hmem1 0 (by rw [map_zero, norm_zero]; exact hrpos)
  refine ⟨hmem w hw, ?_⟩
  set B := contrMap358 L f with hB
  -- Step 1: the estimate for `x, x' ∈ X_{m+1}` with `|x|_m, |x'|_m < r`
  have hstep : ∀ w₁ w₁' : X (m + 1), ‖X.incl m w₁‖ < r → ‖X.incl m w₁'‖ < r →
      ‖levelB B m (a, X.incl m w₁) - levelB B m (a, X.incl m w₁')‖ ≤
        ε * ‖X.incl m w₁ - X.incl m w₁'‖ := by
    intro w₁ w₁' hw₁ hw₁'
    set S : Set (X (m + 1)) := X.incl m ⁻¹' ball 0 r with hS
    have hSc : Convex ℝ S := by
      have := (convex_ball (0 : X m) r).linear_preimage (X.incl m : X (m + 1) →ₗ[ℝ] X m)
      simpa [hS] using this
    have hw₁S : w₁ ∈ S := by rw [hS, mem_preimage, mem_ball_zero_iff]; exact hw₁
    have hw₁'S : w₁' ∈ S := by rw [hS, mem_preimage, mem_ball_zero_iff]; exact hw₁'
    set D := scDeriv (E := 𝔼) (F := 𝔽) U f with hD
    set g : X (m + 1) → 𝔽 m := fun z => levelMap (E := 𝔼) (F := 𝔽) f m ((𝔼).incl m (a, z)) with hg
    set Dz : X (m + 1) → X m →L[ℝ] 𝔽 m := fun z =>
      (levelDeriv D m ((a, z) : P × X (m + 1))).comp (ContinuousLinearMap.inr ℝ P (X m)) with hDz
    set T : X m →L[ℝ] 𝔽 m :=
      (levelDeriv D m ((a, 0) : P × X (m + 1))).comp (ContinuousLinearMap.inr ℝ P (X m)) with hT
    have hgd : ∀ z ∈ S, HasFDerivWithinAt g ((Dz z).comp (X.incl m)) S z := by
      intro z hz
      have hzS : ‖X.incl m z‖ < r := by rwa [hS, mem_preimage, mem_ball_zero_iff] at hz
      have h1 := hf.isSc1.isSc1With_scDeriv.hasFDerivWithinAt_level hU.isScDomain (hmem1 z hzS)
      have hj : HasFDerivWithinAt (fun z : X (m + 1) => ((a, z) : 𝔼 (m + 1)))
          (ContinuousLinearMap.inr ℝ P (X (m + 1))) S z :=
        ((hasFDerivAt_const a z).prodMk (hasFDerivAt_id z)).hasFDerivWithinAt
      have hmaps : MapsTo (fun z : X (m + 1) => ((a, z) : 𝔼 (m + 1))) S ((𝔼).lvlSet U (m + 1)) :=
        fun z hz => hmem1 z (by rwa [hS, mem_preimage, mem_ball_zero_iff] at hz)
      have h2 := h1.comp z hj hmaps
      refine h2.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
      change levelDeriv D m ((a, z) : P × X (m + 1)) ((𝔼).incl m ((0 : P), v)) =
        levelDeriv D m ((a, z) : P × X (m + 1)) ((0 : P), X.incl m v)
      rw [ScBanach.paramProd_incl]
    have hbound : ∀ z ∈ S, ∀ v : X m, ‖Dz z v - T v‖ ≤ ε * c * ‖v‖ := by
      intro z hz v
      have hzS : ‖X.incl m z‖ < r := by rwa [hS, mem_preimage, mem_ball_zero_iff] at hz
      have := h3' a ha (har.trans_le hrr₃) z hmem10 (hmem1 z hzS) (hzS.trans_le hrr₃) v
      rw [norm_sub_rev] at this
      exact this
    have hmvt := norm_sub_sub_le_of_hasFDerivWithinAt_segment hSc hgd hbound hw₁S hw₁'S
    -- the `Y`-component
    have hTv : ∀ v : X m, (T v).2 = L a m v := fun v =>
      snd_levelDeriv_eq_L hf hL haO hmem10 v
    have hsnd : ‖(levelMap (E := 𝔼) (F := 𝔽) f m (a, X.incl m w₁)).2 -
        (levelMap (E := 𝔼) (F := 𝔽) f m (a, X.incl m w₁')).2 - L a m (X.incl m (w₁ - w₁'))‖ ≤
        ε * c * ‖X.incl m (w₁ - w₁')‖ := by
      have := (norm_snd_le (g w₁ - g w₁' - T (X.incl m (w₁ - w₁')))).trans hmvt
      rw [Prod.snd_sub, Prod.snd_sub, hTv] at this
      exact this
    -- Step 3: `H_m(a, x) − H_m(a, x') = L(a)⁻¹[L(a)(x − x') − (f_m(a, x) − f_m(a, x'))₂]`
    have hwm : ((a, X.incl m w₁) : P × X m) ∈ (𝔼).lvlSet U m := hmemU _ hw₁
    have hwm' : ((a, X.incl m w₁') : P × X m) ∈ (𝔼).lvlSet U m := hmemU _ hw₁'
    rw [levelB, levelB, levelMap_contrMap358 hf h0 hwm, levelMap_contrMap358 hf h0 hwm']
    have e : ∀ (u u' : X m) (A A' C : Y m),
        u - (L a m).symm (A - C) - (u' - (L a m).symm (A' - C)) =
          (L a m).symm (L a m (u - u') - (A - A')) := by
      intro u u' A A' C
      simp only [map_sub, ContinuousLinearEquiv.symm_apply_apply]
      abel
    rw [e, ← map_sub]
    calc ‖(L a m).symm (L a m (X.incl m (w₁ - w₁')) -
          ((levelMap (E := 𝔼) (F := 𝔽) f m (a, X.incl m w₁)).2 -
            (levelMap (E := 𝔼) (F := 𝔽) f m (a, X.incl m w₁')).2))‖
        ≤ c⁻¹ * ‖L a m (X.incl m (w₁ - w₁')) -
          ((levelMap (E := 𝔼) (F := 𝔽) f m (a, X.incl m w₁)).2 -
            (levelMap (E := 𝔼) (F := 𝔽) f m (a, X.incl m w₁')).2)‖ :=
          norm_symm_le hc0 (hcm a haO) _
      _ ≤ c⁻¹ * (ε * c * ‖X.incl m (w₁ - w₁')‖) := by
          gcongr
          rw [norm_sub_rev]; exact hsnd
      _ = ε * ‖X.incl m (w₁ - w₁')‖ := by field_simp
  -- Step 4: density of `X_{m+1}` in `X_m`
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (X.denseRange_incl m w)
  obtain ⟨u', hu', hlim'⟩ := mem_closure_iff_seq_limit.1 (X.denseRange_incl m w')
  choose w₁ hw₁ using hu
  choose w₁' hw₁' using hu'
  have hev : ∀ᶠ n in atTop, ‖u n‖ < r := hlim.norm.eventually_lt_const hw
  have hev' : ∀ᶠ n in atTop, ‖u' n‖ < r := hlim'.norm.eventually_lt_const hw'
  have hBw : Tendsto (fun n => levelB B m (a, u n)) atTop (𝓝 (levelB B m (a, w))) :=
    ((hBcont m (a, w) (hmem w hw)).tendsto).comp (tendsto_nhdsWithin_iff.2
      ⟨tendsto_const_nhds.prodMk_nhds hlim, hev.mono fun n hn => hmem (u n) hn⟩)
  have hBw' : Tendsto (fun n => levelB B m (a, u' n)) atTop (𝓝 (levelB B m (a, w'))) :=
    ((hBcont m (a, w') (hmem w' hw')).tendsto).comp (tendsto_nhdsWithin_iff.2
      ⟨tendsto_const_nhds.prodMk_nhds hlim', hev'.mono fun n hn => hmem (u' n) hn⟩)
  refine le_of_tendsto_of_tendsto (hBw.sub hBw').norm ((hlim.sub hlim').norm.const_mul ε) ?_
  filter_upwards [hev, hev'] with n hn hn'
  have := hstep (w₁ n) (w₁' n) (by rw [hw₁]; exact hn) (by rw [hw₁']; exact hn')
  rw [hw₁, hw₁'] at this
  exact this


end Setting

/-! ### From germs on `ofSet U` back to maps on `U` -/

section Bridge

variable {E F : ScBanach} {C U : Set (E 0)}

/-- An sc⁰-germ on the special germ `ofSet U` is an sc⁰ map on `U`. -/
lemma IsSc0Germ.isSc0_ofSet (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C) (h0 : (0 : E 0) ∈ U)
    {f : E 0 → F 0} (hf : IsSc0Germ (ScNbhdGerm.ofSet hU h0) f) : IsSc0 E F U f :=
  ⟨hf.mem_range, hf.continuousOn⟩

/-- An sc^k-germ on the special germ `ofSet U` is an sc^k map on `U` (the converse of
`IsSck.isSckGerm`). -/
theorem IsSckGerm.isSck_ofSet : ∀ {k : ℕ} {E F : ScBanach} {C U : Set (E 0)}, IsQuadrantLike E C →
    ∀ (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C) (h0 : (0 : E 0) ∈ U) {f : E 0 → F 0},
    IsSckGerm k (ScNbhdGerm.ofSet hU h0) f → IsSck k E F U f
  | 0, _, _, _, _, _, hU, h0, _, h => IsSc0Germ.isSc0_ofSet hU h0 h
  | k + 1, E, F, C, U, hC, hU, h0, f, h => by
    obtain ⟨D, hD⟩ := h.1
    have h1 : IsSc1With U f D :=
      ⟨hD.isSc0.isSc0_ofSet hU h0, hD.hasFDerivWithinAt, by
        have := hD.tangent_isSc0
        rw [ScNbhdGerm.ofSet_tangent] at this
        exact this.isSc0_ofSet _ _⟩
    have hUd : IsScDomain E U :=
      ⟨fun m => by
        obtain ⟨O, hO, rfl⟩ := hU
        exact ⟨E.lvlSet O m, E.lvlSet C m, E.isOpen_lvlSet hO m, hC.convex m, rfl⟩,
       fun m x hx => (ScNbhdGerm.ofSet hU h0).uniqueDiffWithinAt hC m hx⟩
    refine ⟨h1.isSc1, ?_⟩
    have h2 := h.2
    rw [ScNbhdGerm.ofSet_tangent] at h2
    have h3 := IsSckGerm.isSck_ofSet (k := k) hC.tangentSet _ _ h2
    refine IsSck.congr hUd.tangentSet ?_ h3
    have := IsSc1.scDerivGerm_ofSet_eqOn hC hU h0 h1.isSc1
    rw [ScNbhdGerm.ofSet_tangent] at this
    exact this

theorem IsScSmoothGerm.isScSmooth_ofSet (hC : IsQuadrantLike E C)
    (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C) (h0 : (0 : E 0) ∈ U) {f : E 0 → F 0}
    (hf : IsScSmoothGerm (ScNbhdGerm.ofSet hU h0) f) : IsScSmooth U f :=
  fun k => (hf k).isSck_ofSet hC hU h0

end Bridge

/-! ### The fibre isomorphism `Φ((b, x), (c, y)) = ((b, x), (c, M(b)y))` as a strong bundle map -/

section FiberIso

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] {X Y : ScBanach} {Ct : Set P}

/-- The shifted family `M¹(b) = M(b) : X¹ → Y¹` of a family of sc-isomorphisms. -/
def shiftFam (M : P → ScIso X Y) : P → ScIso X.shift Y.shift := fun b =>
  { lvl := fun m => M b (m + 1)
    incl_comm := fun m x => (M b).incl_comm (m + 1) x }

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
@[simp] lemma shiftFam_apply (M : P → ScIso X Y) (b : P) (m : ℕ) (x : X (m + 1)) :
    shiftFam M b m x = M b (m + 1) x := rfl

variable (Z : ScBanach)

/-- The strong bundle map `Φ((b, z), (c, y)) = ((b, z), (c, M(b)y))` of `U ◁ (Q ⊕ Y) → U ◁ (Q ⊕ X)`,
`U ⊆ P ⊕ Z`, covering the identity, for a family `b ↦ M(b)` of sc-isomorphisms `Y → X`. -/
def fiberIsoMap (M : P → ScIso Y X) :
    (ScBanach.paramProd P Z) 0 × (ScBanach.paramProd Q Y) 0 →
      (ScBanach.paramProd P Z) 0 × (ScBanach.paramProd Q X) 0 :=
  fun p => (p.1, (p.2.1, M p.1.1 0 p.2.2))

/-- The sc-operator `((b, z), (c, y)) ↦ (b, y)`. -/
def paramFiberOp (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] (Z Y : ScBanach) :
    ScOperator ((ScBanach.paramProd P Z).prod (ScBanach.paramProd Q Y)) (ScBanach.paramProd P Y) where
  lvl m := ((ContinuousLinearMap.fst ℝ P (Z m)).comp (ContinuousLinearMap.fst ℝ (P × Z m) (Q × Y m))).prod
    ((ContinuousLinearMap.snd ℝ Q (Y m)).comp (ContinuousLinearMap.snd ℝ (P × Z m) (Q × Y m)))
  incl_comm _ _ := rfl

variable {Z}

lemma famMap_shiftFam (M : P → ScIso Y X) (p : (ScBanach.paramProd P Y.shift) 0) :
    famMap (shiftFam M) p = levelMap (E := ScBanach.paramProd P Y) (F := X) (famMap M) 1 p := by
  rw [levelMap_famMap]; rfl

variable {O : Set P}

/-- `(O ⊕ Y)¹ = O ⊕ Y¹` is an sc-domain when `O ⊕ Y` is. -/
lemma IsScDomain.paramProd_shift (hO : IsScDomain (ScBanach.paramProd P Y) (O ×ˢ univ)) :
    IsScDomain (ScBanach.paramProd P Y.shift) (O ×ˢ univ) :=
  ⟨fun m => by have := hO.relOpenConvex (m + 1); rwa [ScBanach.paramProd_lvlSet] at this ⊢,
   fun m x hx => by
    have := hO.uniqueDiffWithinAt (m + 1) x (by rwa [ScBanach.paramProd_lvlSet] at hx ⊢)
    rwa [ScBanach.paramProd_lvlSet] at this ⊢⟩

/-- The level shift of the sc-smoothness of `(b, y) ↦ M(b)y` (Proposition 1.2.2 (preprint 1.17)). -/
lemma famMap_shiftFam_isScSmooth (hO : IsScDomain (ScBanach.paramProd P Y) (O ×ˢ univ))
    {M : P → ScIso Y X}
    (hM : IsScSmooth (E := ScBanach.paramProd P Y) (F := X) (O ×ˢ univ) (famMap M)) :
    IsScSmooth (E := ScBanach.paramProd P Y.shift) (F := X.shift) (O ×ˢ univ) (famMap (shiftFam M)) := by
  have h1 := hM.shift hO
  rw [ScBanach.paramProd_lvlSet] at h1
  exact h1.congr hO.paramProd_shift fun p _ => (famMap_shiftFam M p).symm

variable {U' : Set ((ScBanach.paramProd P Z) 0)}

/-- `Φ = fiberIsoMap M` is sc-smooth on `U' ◁ (Q ⊕ Y)` when `(b, y) ↦ M(b)y` is sc-smooth on
`O ⊕ Y` and `U' ⊆ O ⊕ Z`. -/
lemma fiberIsoMap_isScSmooth (hU' : IsRelOpenInQuadrant (ScBanach.paramProd P Z) (Ct ×ˢ univ) U')
    (hU'O : ∀ u ∈ U', u.1 ∈ O) (hO : IsScDomain (ScBanach.paramProd P Y) (O ×ˢ univ))
    {M : P → ScIso Y X}
    (hM : IsScSmooth (E := ScBanach.paramProd P Y) (F := X) (O ×ˢ univ) (famMap M)) :
    IsScSmooth (E := (ScBanach.paramProd P Z).prod (ScBanach.paramProd Q Y))
      (F := (ScBanach.paramProd P Z).prod (ScBanach.paramProd Q X)) (U' ×ˢ univ) (fiberIsoMap Z M) := by
  have hUF : IsScDomain ((ScBanach.paramProd P Z).prod (ScBanach.paramProd Q Y)) (U' ×ˢ univ) :=
    (hU'.prod_univ _).isScDomain
  have h1 : IsScSmooth (E := (ScBanach.paramProd P Z).prod (ScBanach.paramProd Q Y)) (F := X)
      (U' ×ˢ univ) (famMap M ∘ (paramFiberOp P Q Z Y) 0) :=
    IsScSmooth.comp hUF hO hM ((paramFiberOp P Q Z Y).isScSmooth hUF)
      fun p hp => ⟨hU'O p.1 hp.1, mem_univ _⟩
  have h2 : IsScSmooth (E := (ScBanach.paramProd P Z).prod (ScBanach.paramProd Q Y))
      (F := ScBanach.paramProd Q X) (U' ×ˢ univ)
      (scPair (((ScBanach.fstOp (ScBanach.const Q) Y).comp
        (ScBanach.sndOp (ScBanach.paramProd P Z) (ScBanach.paramProd Q Y))) 0)
        (famMap M ∘ (paramFiberOp P Q Z Y) 0)) :=
    ((_ : ScOperator _ _).isScSmooth hUF).scPair hUF h1
  have h3 := (((ScBanach.fstOp (ScBanach.paramProd P Z) (ScBanach.paramProd Q Y)).isScSmooth hUF).scPair
    hUF h2)
  exact h3.congr hUF fun p _ => rfl

/-- `(Vo ∩ C̃) ⊕ X` is relatively open in the partial quadrant `C̃ ⊕ X` for an open `Vo ⊆ P`. -/
lemma isRelOpenInQuadrant_param (hC : IsPartialQuadrant (ScBanach.const P) Ct) {Vo : Set P}
    (hVo : IsOpen Vo) (X : ScBanach) :
    IsRelOpenInQuadrant (ScBanach.paramProd P X) (Ct ×ˢ univ) ((Vo ∩ Ct) ×ˢ univ) :=
  ⟨hC.prod_univ X, Vo ×ˢ univ, hVo.prod isOpen_univ, by rw [prod_inter_prod, univ_inter]⟩

/-- `shiftFiber Φ = Φ¹` for the fibre isomorphism: the lift to `F'₁` of `(c, M(b)ιy₁)` is
`(c, M(b)y₁)`. -/
lemma shiftFiber_fiberIsoMap (M : P → ScIso Y X)
    (p : ((ScBanach.paramProd P Z).prod (ScBanach.paramProd Q Y).shift) 0) :
    shiftFiber (E := ScBanach.paramProd P Z) (F := ScBanach.paramProd Q Y)
      (E' := ScBanach.paramProd P Z) (F' := ScBanach.paramProd Q X) (fiberIsoMap Z M) p =
      fiberIsoMap (Q := Q) Z (shiftFam M)
        (p : (ScBanach.paramProd P Z) 0 × (ScBanach.paramProd Q Y.shift) 0) := by
  unfold shiftFiber
  refine Prod.ext rfl ?_
  have e : (fiberIsoMap (Q := Q) Z M (p.1, (ScBanach.paramProd Q Y).toBase 1 p.2)).2 =
      (ScBanach.paramProd Q X).toBase 1 ((p.2.1, M p.1.1 1 p.2.2) : Q × X 1) := by
    rw [ScBanach.paramProd_toBase, ScBanach.paramProd_toBase, (M p.1.1).toBase_comm]
    rfl
  rw [e, Function.leftInverse_invFun ((ScBanach.paramProd Q X).toBase_injective 1)]
  rfl

/-- The strong bundle map `Φ((b, x), (c, y)) = ((b, x), (c, M(b)y))` on `U' ◁ (Q ⊕ Y)`, covering
the identity of `U'`, for a family of sc-isomorphisms `M(b) : Y → X` with `(b, y) ↦ M(b)y`
sc-smooth on `O ⊕ Y`, `U' ⊆ O ⊕ X`. -/
theorem fiberIsoMap_isStrongBundleMap (hC : IsPartialQuadrant (ScBanach.const P) Ct) {Vo : Set P}
    (hVo : IsOpen Vo) (hU' : IsRelOpenInQuadrant (ScBanach.paramProd P Z) (Ct ×ˢ univ) U')
    (hU'O : ∀ u ∈ U', u.1 ∈ Vo ∩ Ct) {M : P → ScIso Y X}
    (hM : IsScSmooth (E := ScBanach.paramProd P Y) (F := X) ((Vo ∩ Ct) ×ˢ univ) (famMap M)) :
    IsStrongBundleMap (E := ScBanach.paramProd P Z) (F := ScBanach.paramProd Q Y)
      (E' := ScBanach.paramProd P Z) (F' := ScBanach.paramProd Q X) U' U' (fiberIsoMap Z M) where
  mapsTo p hp := ⟨hp.1, mem_univ _⟩
  fst_independent _ _ _ _ := rfl
  fiber_linear u _ :=
    ⟨fun a b => Prod.ext rfl (map_add (M u.1 0) a.2 b.2), fun c a => Prod.ext rfl (map_smul (M u.1 0) c a.2)⟩
  preserves_filtration m k _ u _ hum h hh := by
    refine ⟨hum, ?_⟩
    obtain ⟨hk, rfl⟩ := hh
    refine ⟨(hk.1, M u.1 k hk.2), ?_⟩
    rw [ScBanach.paramProd_toBase, ScBanach.paramProd_toBase, (M u.1).toBase_comm]
    rfl
  isScSmooth_zero := fiberIsoMap_isScSmooth hU' hU'O (isRelOpenInQuadrant_param hC hVo Y).isScDomain hM
  isScSmooth_one := by
    have h1 : IsScSmooth (E := (ScBanach.paramProd P Z).prod (ScBanach.paramProd Q Y).shift)
        (F := (ScBanach.paramProd P Z).prod (ScBanach.paramProd Q X).shift) (U' ×ˢ univ)
        (fun p => fiberIsoMap (Q := Q) Z (shiftFam M)
          (p : (ScBanach.paramProd P Z) 0 × (ScBanach.paramProd Q Y.shift) 0)) :=
      fiberIsoMap_isScSmooth (Q := Q) (Y := Y.shift) (X := X.shift) hU' hU'O
        (isRelOpenInQuadrant_param hC hVo Y.shift).isScDomain
        (famMap_shiftFam_isScSmooth (isRelOpenInQuadrant_param hC hVo Y).isScDomain hM)
    exact h1.congr (hU'.prod_univ (ScBanach.paramProd Q Y).shift).isScDomain
      fun p _ => (shiftFiber_fiberIsoMap M p).symm

/-- **The strong bundle isomorphism `Φ` of the proof of Theorem 3.7.1 (preprint 3.58)**:
`Φ((b, x), (c, y)) = ((b, x), (c, L(b)⁻¹y))` with inverse `((b, x), (c, x')) ↦ ((b, x), (c, L(b)x'))`,
on `U' ◁ (Q ⊕ Y) → U' ◁ (Q ⊕ X)`, for a family of sc-isomorphisms `L(b) : X → Y` such that
`(b, h) ↦ L(b)h` and `(b, y) ↦ L(b)⁻¹y` are sc-smooth on `O ⊕ X`, `O ⊕ Y` (Lemma 3.7.4 (preprint 3.61)). -/
theorem fiberIsoMap_isStrongBundleIso (hC : IsPartialQuadrant (ScBanach.const P) Ct) {Vo : Set P}
    (hVo : IsOpen Vo) (hU' : IsRelOpenInQuadrant (ScBanach.paramProd P Z) (Ct ×ˢ univ) U')
    (hU'O : ∀ u ∈ U', u.1 ∈ Vo ∩ Ct) {L : P → ScIso X Y}
    (hL : IsScSmooth (E := ScBanach.paramProd P X) (F := Y) ((Vo ∩ Ct) ×ˢ univ) (famMap L))
    (hLinv : IsScSmooth (E := ScBanach.paramProd P Y) (F := X) ((Vo ∩ Ct) ×ˢ univ) (famInv L)) :
    IsStrongBundleIso (E := ScBanach.paramProd P Z) (F := ScBanach.paramProd Q Y)
      (E' := ScBanach.paramProd P Z) (F' := ScBanach.paramProd Q X) U' U'
      (fiberIsoMap Z fun b => (L b).symm) (fiberIsoMap Z L) where
  toFun := fiberIsoMap_isStrongBundleMap hC hVo hU' hU'O (M := fun b => (L b).symm) hLinv
  invFun := fiberIsoMap_isStrongBundleMap hC hVo hU' hU'O hL
  left_inv p _ := by
    refine Prod.ext rfl (Prod.ext rfl ?_)
    show L p.1.1 0 ((L p.1.1 0).symm p.2.2) = p.2.2
    exact (L p.1.1 0).apply_symm_apply p.2.2
  right_inv p _ := by
    refine Prod.ext rfl (Prod.ext rfl ?_)
    show (L p.1.1 0).symm (L p.1.1 0 p.2.2) = p.2.2
    exact (L p.1.1 0).symm_apply_apply p.2.2

/-- The sc-operator `J(b, h) = ((b, 0), (0, h)) : P ⊕ X → T(P ⊕ X)`. -/
def tangentInjOp (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (X : ScBanach) : ScOperator (ScBanach.paramProd P X) (ScBanach.paramProd P X).tangent where
  lvl m := ((ContinuousLinearMap.inl ℝ P (X (m + 1))).comp (ContinuousLinearMap.fst ℝ P (X m))).prod
    ((ContinuousLinearMap.inr ℝ P (X m)).comp (ContinuousLinearMap.snd ℝ P (X m)))
  incl_comm m x := by
    refine Prod.ext (Prod.ext rfl ?_) rfl
    show X.incl (m + 1) (0 : X (m + 2)) = 0
    exact map_zero _

/-- The sc-smoothness of `(b, h) ↦ L(b)h = P ∘ D₂f(b, 0)h` on `(Vo ∩ C̃) ⊕ X` from the
sc-smoothness of `f` (the text: "since `B` is a finite-dimensional sc-smooth space, the map
`(B ∩ U) ⊕ X → Y : (b, x) ↦ P ∘ Df(b)x` is sc-smooth"): it is `pr_Y ∘ Tf ∘ J`,
`J(b, h) = ((b, 0), (0, h))`. -/
theorem famMap_isScSmooth_of_deriv (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    {U : Set ((ScBanach.paramProd P X) 0)} (hU : IsRelOpenInQuadrant (ScBanach.paramProd P X) (Ct ×ˢ univ) U)
    {f : (ScBanach.paramProd P X) 0 → (ScBanach.paramProd Q Y) 0} (hf : IsScSmooth U f)
    {Vo : Set P} (hVo : IsOpen Vo) (hOU : ∀ b ∈ Vo ∩ Ct, ((b, 0) : (ScBanach.paramProd P X) 0) ∈ U)
    {L : P → ScIso X Y} (hL : ∀ b ∈ Vo ∩ Ct, ∀ h : X 0,
      L b 0 h = (scDeriv (E := ScBanach.paramProd P X) (F := ScBanach.paramProd Q Y) U f
        ((b, 0) : P × X 1) ((0 : P), h)).2) :
    IsScSmooth (E := ScBanach.paramProd P X) (F := Y) ((Vo ∩ Ct) ×ˢ univ) (famMap L) := by
  have hOd := (isRelOpenInQuadrant_param hC hVo X).isScDomain
  have hT : IsScSmooth ((ScBanach.paramProd P X).tangentSet U) (tangentMap U f) :=
    (isScSmooth_iff.1 hf).2
  have hJ := (tangentInjOp P X).isScSmooth hOd
  have hmaps : MapsTo ((tangentInjOp P X) 0) ((Vo ∩ Ct) ×ˢ univ)
      ((ScBanach.paramProd P X).tangentSet U) := fun p hp => by
    show (((p.1, 0), (0, p.2)) : (ScBanach.paramProd P X).tangent 0).1 ∈
      (ScBanach.paramProd P X).lvlSet U 1
    rw [ScBanach.mem_lvlSet, ScBanach.paramProd_toBase, map_zero]
    exact hOU p.1 hp.1
  have h1 := IsScSmooth.comp hOd hU.isScDomain.tangentSet hT hJ hmaps
  have h2 := (h1.snd hOd).snd hOd
  refine h2.congr hOd fun p hp => ?_
  show (scDeriv (E := ScBanach.paramProd P X) (F := ScBanach.paramProd Q Y) U f
    ((p.1, 0) : P × X 1) ((0 : P), p.2)).2 = L p.1 0 p.2
  exact (hL p.1 hp.1 p.2).symm

/-- **Lemma 3.7.4 (preprint 3.61) in set form**: `(b, y) ↦ L(b)⁻¹y` is sc-smooth on `(Vo ∩ C̃) ⊕ Y` when
`(b, h) ↦ L(b)h` is sc-smooth on `(Vo ∩ C̃) ⊕ X` and the `L(b)` satisfy the uniform lower bounds
(iii) there. -/
theorem famInv_isScSmooth_of (hC : IsPartialQuadrant (ScBanach.const P) Ct) {Vo : Set P}
    (hVo : IsOpen Vo) (hVo0 : (0 : P) ∈ Vo) {L : P → ScIso X Y}
    (hL : IsScSmooth (E := ScBanach.paramProd P X) (F := Y) ((Vo ∩ Ct) ×ˢ univ) (famMap L))
    (hc : ∀ m, ∃ c > 0, ∀ b ∈ Vo ∩ Ct, ∀ h : X m, c * ‖h‖ ≤ ‖L b m h‖) :
    IsScSmooth (E := ScBanach.paramProd P Y) (F := X) ((Vo ∩ Ct) ×ˢ univ) (famInv L) := by
  have hCq : IsQuadrantLike (ScBanach.const P) Ct := hC.isQuadrantLike
  have hOrel : ∃ O' : Set ((ScBanach.const P) 0), IsOpen O' ∧ Vo ∩ Ct = O' ∩ Ct := ⟨Vo, hVo, rfl⟩
  have h0O : (0 : (ScBanach.const P) 0) ∈ Vo ∩ Ct := ⟨hVo0, hCq.zero_mem⟩
  set Gv : ScNbhdGerm (ScBanach.const P) Ct := ScNbhdGerm.ofSet hOrel h0O with hGv
  have hUX := isRelOpenInQuadrant_param hC hVo X
  have hUY := isRelOpenInQuadrant_param hC hVo Y
  have hCX : IsQuadrantLike (ScBanach.paramProd P X) (Ct ×ˢ univ) := (hC.prod_univ X).isQuadrantLike
  have hCY : IsQuadrantLike (ScBanach.paramProd P Y) (Ct ×ˢ univ) := (hC.prod_univ Y).isQuadrantLike
  have h0X : (0 : (ScBanach.paramProd P X) 0) ∈ (Vo ∩ Ct) ×ˢ univ := ⟨h0O, mem_univ _⟩
  have h0Y : (0 : (ScBanach.paramProd P Y) 0) ∈ (Vo ∩ Ct) ×ˢ univ := ⟨h0O, mem_univ _⟩
  have hGvU : ∀ m, Gv.U m = Vo ∩ Ct := fun m => by
    rw [hGv, ScNbhdGerm.ofSet_U, ScBanach.const_lvlSet]
  have hG : IsScSmoothGerm (Gv.prodFull X) (famMap L) := fun k =>
    IsSckGerm.of_U_eq hCX (fun m => by rw [ScNbhdGerm.ofSet_U, ScBanach.paramProd_lvlSet,
      ScNbhdGerm.prodFull_U, hGvU]) ((hL.isScSmoothGerm hCX hUX.relOpen h0X) k)
  have hc' : ∀ m, ∃ c > 0, ∀ v ∈ Gv.U 0, ∀ h : X m, c * ‖h‖ ≤ ‖L v m h‖ := by
    rw [hGvU]; exact hc
  have h1 := lemma_3_7_4 hC hG hc'
  have h2 : IsScSmoothGerm (ScNbhdGerm.ofSet hUY.relOpen h0Y) (famInv L) := fun k =>
    IsSckGerm.of_U_eq hCY (fun m => by rw [ScNbhdGerm.ofSet_U, ScBanach.paramProd_lvlSet,
      ScNbhdGerm.prodFull_U, hGvU]) (h1 k)
  exact h2.isScSmooth_ofSet hCY hUY.relOpen h0Y

end FiberIso

/-! ### Theorem 3.7.1 (preprint 3.58) from the family of sc-isomorphisms -/

section Main

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] {X Y : ScBanach} {Ct : Set P}

local notation "𝔼" => ScBanach.paramProd P X
local notation "𝔽" => ScBanach.paramProd Q Y

variable {U : Set ((ScBanach.paramProd P X) 0)}
  {f : (ScBanach.paramProd P X) 0 → (ScBanach.paramProd Q Y) 0} {L : P → ScIso X Y}

/-- **Theorem 3.7.1 (preprint 3.58) (basic germ criterion), given the family of sc-isomorphisms**: let `U` be a
relatively open neighbourhood of `0` in the partial quadrant `C̃ ⊕ X` of `E = ℝⁿ ⊕ X` and
`f : U → F = ℝᴺ ⊕ Y` sc-smooth (the coordinates of the text's proof, `B = ℝⁿ`, `A = ℝᴺ`).  Suppose
that for `b` in a relatively open neighbourhood `O = Vo ∩ C̃` of `0` in `C̃` the operators
`L(b) = P ∘ D₂f(b, 0)|X : X → Y` are sc-isomorphisms with the uniform lower bounds
`|L(b)h|_m ≥ c_m|h|_m` (the conclusions of Lemmas 3.7.2, 3.7.3 (preprint 3.59, 3.60) and of the index argument of the
text), and that condition (3) of Theorem 3.7.1 (preprint 3.58) holds.  Then, with `U' = U ∩ (Vo ⊕ X)`:
the push-forward `k = Φ_*(f − f(0))`, `k(b, x) = ((1 − P)h(b, x), L(b)⁻¹P h(b, x))`, is a basic
germ on `O(U', 0)` with contraction map `H(b, x) = x − L(b)⁻¹P h(b, x)`; the fibre map
`Φ((b, x), (c, y)) = ((b, x), (c, L(b)⁻¹y))` is a strong bundle isomorphism
`U' ◁ (ℝᴺ ⊕ Y) → U' ◁ (ℝᴺ ⊕ X)` covering the identity; hence `f − s`, `s = f(0)` the constant
sc⁺-section, is conjugated near `0` to a basic germ. -/
theorem theorem_3_7_1_of_family (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (hU : IsRelOpenInQuadrant 𝔼 (Ct ×ˢ univ) U) (h0 : (0 : 𝔼 0) ∈ U) (hf : IsScSmooth U f)
    {Vo : Set P} (hVo : IsOpen Vo) (hVo0 : (0 : P) ∈ Vo)
    (hOU : ∀ b ∈ Vo ∩ Ct, ((b, 0) : 𝔼 0) ∈ U)
    (hL : ∀ b ∈ Vo ∩ Ct, ∀ h : X 0,
      L b 0 h = (scDeriv (E := 𝔼) (F := 𝔽) U f ((b, 0) : P × X 1) ((0 : P), h)).2)
    (hc : ∀ m, ∃ c > 0, ∀ b ∈ Vo ∩ Ct, ∀ h : X m, c * ‖h‖ ≤ ‖L b m h‖)
    (h3 : DerivCondition Ct U f) :
    IsBasicGerm Ct (ScNbhdGerm.ofSet (hU.inter_isOpen (hVo.prod isOpen_univ)).relOpen
        ⟨h0, hVo0, mem_univ _⟩) (pushGerm358 L f) (contrMap358 L f) ∧
    IsStrongBundleIso (U ∩ Vo ×ˢ univ) (U ∩ Vo ×ˢ univ)
      (fiberIsoMap (Q := Q) X fun b => (L b).symm) (fiberIsoMap X L) ∧
    IsConjugateToBasicGerm (U ∩ Vo ×ˢ univ) (shiftedGerm f) := by
  have hU' : IsRelOpenInQuadrant 𝔼 (Ct ×ˢ univ) (U ∩ Vo ×ˢ univ) :=
    hU.inter_isOpen (hVo.prod isOpen_univ)
  have h0' : (0 : 𝔼 0) ∈ U ∩ Vo ×ˢ univ := ⟨h0, hVo0, mem_univ _⟩
  have hUC : U ⊆ Ct ×ˢ univ := by obtain ⟨O, -, rfl⟩ := hU.relOpen; exact inter_subset_right
  have hU'O : ∀ u ∈ U ∩ Vo ×ˢ univ, u.1 ∈ Vo ∩ Ct := fun u hu => ⟨hu.2.1, (hUC hu.1).1⟩
  have hCq : IsQuadrantLike 𝔼 (Ct ×ˢ univ) := (hC.prod_univ X).isQuadrantLike
  have hU'd := hU'.isScDomain
  -- the family and its inverse are sc-smooth (Lemma 3.7.4 (preprint 3.61))
  have hLsm := famMap_isScSmooth_of_deriv hC hU hf hVo hOU hL
  have hLinv := famInv_isScSmooth_of hC hVo hVo0 hLsm hc
  have hΦ := fiberIsoMap_isStrongBundleIso (Q := Q) (Z := X) hC hVo hU' hU'O hLsm hLinv
  -- the push-forward germ and the contraction map are sc-smooth on `U'`
  have hfU' : IsScSmooth (U ∩ Vo ×ˢ univ) f := hf.of_subset hU'd inter_subset_left
  have hconst : IsScSmooth (U ∩ Vo ×ˢ univ) fun _ : 𝔼 0 => f 0 := by
    have := IsScSmooth.comp hU'd hU.isScDomain hf ((ScOperator.zero 𝔼 𝔼).isScSmooth hU'd)
      (fun x _ => show (ScOperator.zero 𝔼 𝔼) 0 x ∈ U from h0)
    exact this.congr hU'd fun _ _ => rfl
  have hh : IsScSmooth (U ∩ Vo ×ˢ univ) fun x => f x - f 0 := hfU'.sub hU'd hconst
  have hh2 : IsScSmooth (F := Y) (U ∩ Vo ×ˢ univ) fun x => (f x - f 0).2 := hh.snd hU'd
  have hpair : IsScSmooth (F := ScBanach.paramProd P Y) (U ∩ Vo ×ˢ univ)
      (scPair ((ScBanach.fstOp (ScBanach.const P) X) 0) fun x => (f x - f 0).2) :=
    ((ScBanach.fstOp (ScBanach.const P) X).isScSmooth hU'd).scPair hU'd hh2
  have hinv : IsScSmooth (F := X) (U ∩ Vo ×ˢ univ)
      (famInv L ∘ scPair ((ScBanach.fstOp (ScBanach.const P) X) 0) fun x => (f x - f 0).2) :=
    IsScSmooth.comp hU'd (isRelOpenInQuadrant_param hC hVo Y).isScDomain hLinv hpair
      fun x hx => ⟨hU'O x hx, mem_univ _⟩
  have hk : IsScSmooth (U ∩ Vo ×ˢ univ) (pushGerm358 L f) :=
    ((hh.fst hU'd).scPair hU'd hinv).congr hU'd fun _ _ => rfl
  have hB : IsScSmooth (U ∩ Vo ×ˢ univ) (contrMap358 L f) :=
    (((ScBanach.sndOp (ScBanach.const P) X).isScSmooth hU'd).sub hU'd hinv).congr hU'd
      fun _ _ => rfl
  -- the basic germ
  have hbasic : IsBasicGerm Ct (ScNbhdGerm.ofSet hU'.relOpen h0') (pushGerm358 L f)
      (contrMap358 L f) :=
    { isScSmooth := hk.isScSmoothGerm hCq hU'.relOpen h0'
      f_zero := by simp [pushGerm358]
      snd_eq := fun x _ => pushGerm358_snd x
      contraction :=
        { isSc0 := (hB.isScSmoothGerm hCq hU'.relOpen h0') 0
          B_zero := by
            show (0 : X 0) - (L 0 0).symm (f ((0, 0) : 𝔼 0) - f 0).2 = 0
            have e : ((0, 0) : 𝔼 0) = 0 := rfl
            rw [e, sub_self, Prod.snd_zero, map_zero, sub_zero]
          contraction := fun ε hε m =>
            contrMap358_contraction hU h0 hf hVo hVo0 hL hc h3 (fun m => (hB 0).continuousOn m) hε m } }
  refine ⟨hbasic, hΦ, ?_⟩
  refine ⟨P, Q, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, X, Ct, U ∩ Vo ×ˢ univ, fiberIsoMap (Q := Q) X fun b => (L b).symm,
    fiberIsoMap X L, ScNbhdGerm.ofSet hU'.relOpen h0', pushGerm358 L f, contrMap358 L f, hC, hU',
    hΦ, ?_, ?_, hbasic, ?_⟩
  · show ((fiberIsoMap (Q := Q) X fun b => (L b).symm) (0, 0)).1 = 0
    rfl
  · intro u hu
    exact hu
  · exact Eventually.of_forall fun u _ => rfl


end Main

end Polyfold
