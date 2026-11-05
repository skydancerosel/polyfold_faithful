import Polyfold.Chapter1.Properties

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.2,
Propositions 1.16–1.19 and Corollary 1.20 on all levels (the proofs are those of [25] = arXiv
1002.3381, §2.1, Propositions 2.1–2.4 and Corollary 2.5, as written out in `Exposition/Chapter1.md`
§3.4).

# Sc-differentiability and classical differentiability on the levels

## The text, paraphrased

(Proposition 1.16) An sc⁰ map `f : U → F` on a relatively open subset `U` of a partial quadrant is
sc¹ iff (1) for every `m ≥ 1` the induced map `f : U_m → F_{m−1}` is `C¹`, so that
`df : U_m → L(E_m, F_{m−1})` is continuous, and (2) for every `m ≥ 1` and `x ∈ U_m` the operator
`df(x) : E_m → F_{m−1}` extends to a bounded `Df(x) : E_{m−1} → F_{m−1}` such that
`U_m ⊕ E_{m−1} → F_{m−1}`, `(x, h) ↦ Df(x)h`, is continuous.  (Proposition 1.17) If `f : U → V` is
sc^k then `f : U¹ → V¹` is sc^k.  (Proposition 1.18) If `f : U → V` is sc^k then `f : U_{m+k} → V_m`
is `C^k` for every `m`, and `f : U_{m+l} → V_m` is `C^l` for `0 ≤ l ≤ k`.  (Proposition 1.19) If
`f : U_{m+l} → F_m` is `C^{l+1}` for all `m ≥ 0` and `0 ≤ l ≤ k`, then `f` is sc^{k+1}.
(Corollary 1.20) If `f : U → ℝᴺ` has `f : U_l → ℝᴺ` of class `C^{l+1}` for `0 ≤ l ≤ k`, then `f` is
sc^{k+1}.

## What is formalized

* `Polyfold.contDiffOn_clm_comp_of_isCompactOperator` (the **compact-open lemma**): if
  `(x, y) ↦ A(x)y` is `C^k` on `s × Y` with `A(x) ∈ L(Y, Z)`, and `ι : Y' → Y` is a compact
  operator, then `x ↦ A(x) ∘ ι` is `C^k` as a map `s → L(Y', Z)`.  For `k = 0` this is the
  compactness argument of [25, Proposition 2.1] (the subsequence `h_n → h` in `E_{m}` for unit
  vectors `h_n ∈ E_{m+1}`); for `k ≥ 1` it is proved by induction with the mean value inequality,
  and it replaces the multilinear maps `Γ(x)(h₁, …, h_k, h)` and the differentiation under the
  integral sign of [25, Proposition 2.3].
* `Polyfold.levelDeriv D m x : E_m → F_m` (`x ∈ E_{m+1}`): the level-`m` operator of `Df(x)`,
  i.e. the unique bounded `T` with `ι_m ∘ T = Df(x) ∘ ι_m`; for an sc¹ map it exists for
  `x ∈ U_{m+1}` (`IsSc1With.toBase_levelDeriv`), and `(x, h) ↦ Df(x)h` is continuous on
  `U_{m+1} × E_m` (`IsSc1With.continuousOn_levelDeriv`): this is condition (3) of Definition 1.14
  on level `m`, and condition (2) of Proposition 1.16.
* **Proposition 1.16** (`Polyfold.proposition_1_16`): for an sc⁰ map `f` on an sc-domain `U`,
  `f` is sc¹ iff there is a family `Dl m x ∈ L(E_m, F_m)` (`x ∈ U_{m+1}`) with
  `Polyfold.IsSc1Levels U f Dl`: `f : U_{m+1} → F_m` is differentiable at every point of
  `U_{m+1}` with derivative `Dl m x|_{E_{m+1}}`, and `(x, h) ↦ Dl m x h` is continuous on
  `U_{m+1} × E_m`.  The continuity of `x ↦ df(x) ∈ L(E_{m+1}, F_m)` and the `C¹` statement are
  `IsSc1Levels.continuousOn_clm`, `IsSc1Levels.contDiffOn`; for an sc¹ map directly:
  `IsSc1With.hasFDerivWithinAt_level`, `IsSc1With.continuousOn_levelDeriv_clm`,
  `IsSc1With.contDiffOn_level` (the direction (⇒), [25, Proposition 2.1], level-raising by the
  integral `f(x+h) − f(x) = ∫₀¹ Df(x+τh)h dτ` in `F_m`).  The direction (⇐) uses that the
  extensions `Dl m x` are the restrictions of `Dl 0 (x)` (`IsSc1Levels.toBase_apply`, Lemma 3.H
  of the exposition), which the text does not state.
* **Proposition 1.17** (`Polyfold.IsSck.shift`, `Polyfold.IsScSmooth.shift`): if `f` is sc^k on
  `U` then `f : U¹ → F¹` (the level-`1` map `levelMap f 1` between the shifted spaces) is sc^k on
  `U¹ = U_1`; for sc¹ with the level operators `levelDeriv D 1` (`IsSc1With.shift`).
* **Proposition 1.18** (`Polyfold.IsSck.contDiffOn_levels`, `IsSck.contDiffOn_levels_of_le`,
  `IsSck.contDiffOn_base`): if `f` is sc^k then `f : U_{m+k} → F_m` is `C^k` for every `m`,
  `f : U_{m+l} → F_m` is `C^l` for `l ≤ k`, and in particular `f : U_k → F_0` is `C^k`.  The proof
  is an induction on `k` over all sc-domains: the derivative of `f : U_{m+k+1} → F_m` is
  `x ↦ Df(x)|_{E_{m+k+1}}`, which is `C^k` into `L(E_{m+k+1}, F_m)` by the compact-open lemma
  applied to the second component `(x, h) ↦ Df(x)h` of the level-`(m+k)` tangent map (which is
  `C^k` by the induction hypothesis for `Tf`).
* **Proposition 1.19** (`Polyfold.proposition_1_19`) and **Corollary 1.20**
  (`Polyfold.corollary_1_20`, `Polyfold.corollary_1_20_base`) for all `k`, under the **stronger**
  hypothesis that `f : U_m → F_m` is `C^{k+1}` for every `m`; `Polyfold.IsScSmooth.of_contDiffOn_levels`:
  a map that is `C^∞` on every level is sc-smooth, and
  `Polyfold.IsScSmooth.of_contDiffOn_finiteDimensional`: a `C^∞` map into a finite-dimensional
  space is sc-smooth.  **Under the text's hypothesis** (`f : U_{m+l} → F_m` of class `C^{l+1}` for
  all `m` and `l ≤ k`) both are proved in `Polyfold/Chapter1/LevelsWeak.lean`
  (`Polyfold.proposition_1_19_text`, `Polyfold.corollary_1_20_text`, and the sc-smooth versions
  `IsScSmooth.of_contDiffOn_levels_text`, `IsScSmooth.of_contDiffOn_levels_finiteDimensional_text`),
  by the induction `(S_k)` of [25, Proposition 2.4] on the elementary maps
  `(x, h₁, …, h_j) ↦ d^j f(x)(h₁, …, h_j)`.

## The two hypotheses of Proposition 1.19

* With the stronger hypothesis the induction of this file is immediate: the level maps of `Tf`
  are `(x, h) ↦ (f(x), d(f_m)(x)h)`, which are `C^k` when the `f_m` are `C^{k+1}` (for `k = 0`
  the two hypotheses agree, `proposition_1_19_zero`).  With the text's hypothesis `Tf` does not
  satisfy the hypothesis with `k − 1` in general (its second component is only `C^l` on
  `U_{m+l+1} × E_{m+l} → F_m`), and the induction has to carry the description `(S_k)` of the
  components of `T^{k+1}f`; this is done in `LevelsWeak.lean`.

## What the text leaves implicit, and the choices made

* Proposition 1.16 (2) writes one operator `Df(x)` for all `m`; here `Dl m x` is a family, and the
  compatibility `ι_m ∘ Dl m x = Dl 0 (x) ∘ ι_m` is proved (`IsSc1Levels.toBase_apply`) from the
  uniqueness of derivatives on `U_{m+1}` and the density of `E_{m+1}` in `E_m`; it is what makes
  the direction (⇐), called "clear" in [25], work.
* The hypotheses "`U` relatively open in a partial quadrant" of the text enter only through
  `IsScDomain E U` (open-in-convex levels with unique differentiability), as in the chain rule;
  it is needed for the segments `x + τh ⊆ U_{m+1}` of the integral representation and for the
  uniqueness of derivatives.  Proposition 1.17 for sc⁰ needs no hypothesis on `U`.
* In [25, Proposition 2.1] the integral `∫₀¹ Df(x+τh)h dτ` is first formed in `F_0` and then
  "the integrand is continuous into `F_m`"; here the Bochner integral is formed in `F_m` directly,
  and its image under `ι_m : F_m → F_0` is identified with `f(x+h) − f(x)` by the fundamental
  theorem of calculus for the `C¹` map `f : U_1 → F_0`.
* [25, Proposition 2.3] proves `f : U_k → F_0` is `C^k` and then invokes Proposition 2.2 for the
  general level; here the general level is proved directly, with a compatible level-lowering
  operator `ρ : E_n → E_m` (`n = m + k`) as a parameter (`IsSck.contDiffOn_levels'`), which avoids
  identifying `(E^m)_k` with `E_{m+k}`.
-/

open Set Filter Topology Function Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### The compact-open lemma -/

section CompactOpen

variable {X Y Y' : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Y'] [NormedSpace ℝ Y']

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
/-- Uniform continuity on compact sets: if `(x, w) ↦ B x w` is continuous on `s × Y`, `x ∈ s` and
`K ⊆ Y` is compact, then for `x' ∈ s` near `x`, `‖B x' w − B x w‖ ≤ c` for all `w ∈ K`. -/
theorem exists_delta_of_continuousOn {W : Type} [NormedAddCommGroup W] {s : Set X} {B : X → Y → W}
    (hB : ContinuousOn (fun p : X × Y => B p.1 p.2) (s ×ˢ univ)) {x : X} (hx : x ∈ s) {K : Set Y}
    (hK : IsCompact K) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ x' ∈ s, ‖x' - x‖ < δ → ∀ w ∈ K, ‖B x' w - B x w‖ ≤ c := by
  let Θ : s × Y → W := fun q => B q.1.1 q.2 - B x q.2
  have hΘ : Continuous Θ := by
    have h1 : Continuous fun q : s × Y => B q.1.1 q.2 :=
      hB.comp_continuous (f := fun q : s × Y => ((q.1.1 : X), q.2)) (by fun_prop)
        fun q => ⟨q.1.2, mem_univ _⟩
    have h2 : Continuous fun q : s × Y => B x q.2 :=
      hB.comp_continuous (f := fun q : s × Y => (x, q.2)) (by fun_prop) fun _ => ⟨hx, mem_univ _⟩
    exact h1.sub h2
  have key : ∀ᶠ y in 𝓝 (⟨x, hx⟩ : s), ∀ w ∈ K, ‖Θ (y, w)‖ ≤ c := by
    refine hK.eventually_forall_of_forall_eventually (P := fun y w => ‖Θ (y, w)‖ ≤ c) fun w _ => ?_
    have h0 : Θ (⟨x, hx⟩, w) = 0 := by simp [Θ]
    have := hΘ.continuousAt.eventually_mem (x := (⟨x, hx⟩, w))
      (s := Metric.closedBall 0 c) (by rw [h0]; exact Metric.closedBall_mem_nhds 0 hc)
    exact this.mono fun q hq => by simpa using hq
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 key
  refine ⟨δ, hδ, fun x' hx' hxδ w hw => ?_⟩
  have := hδ' (y := ⟨x', hx'⟩) (by rw [Subtype.dist_eq, dist_eq_norm]; exact hxδ) w hw
  simpa [Θ] using this

omit [NormedSpace ℝ X] in
/-- **The compact-open lemma, `k = 0`**: if `(x, y) ↦ A(x)y` is continuous on `s × Y` and
`ι : Y' → Y` is a compact operator, then `x ↦ A(x) ∘ ι` is continuous on `s` in the operator norm
of `L(Y', Z)` (the compactness argument of [25, Proposition 2.1]). -/
theorem continuousOn_clm_comp_of_isCompactOperator {Z : Type} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {s : Set X} {A : X → Y →L[ℝ] Z}
    (hA : ContinuousOn (fun p : X × Y => A p.1 p.2) (s ×ˢ univ)) {ι : Y' →L[ℝ] Y}
    (hι : IsCompactOperator ι) : ContinuousOn (fun x => (A x).comp ι) s := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨K, hK, hKsub⟩ := hι.image_closedBall_subset_compact (f := (ι : Y' →ₗ[ℝ] Y)) 1
  obtain ⟨δ, hδ, hδ'⟩ := exists_delta_of_continuousOn (B := fun x y => A x y) hA hx hK (half_pos hε)
  refine ⟨δ, hδ, fun x' hx' hxx' => ?_⟩
  rw [dist_eq_norm] at hxx' ⊢
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  rw [← ContinuousLinearMap.sub_comp]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos hε).le fun v hv => ?_
  have hunit : ι v ∈ K := hKsub ⟨v, by rw [mem_closedBall, dist_zero_right, hv], rfl⟩
  simpa using hδ' x' hx' hxx' _ hunit

/-- **The compact-open lemma**: let `s ⊆ X` be open-in-convex with unique differentiability,
`ι : Y' → Y` a compact operator and `A : X → L(Y, Z)` such that `(x, y) ↦ A(x)y` is `C^k` on
`s × Y`.  Then `x ↦ A(x) ∘ ι` is `C^k` on `s` as a map into `L(Y', Z)`.

For `k = 0` this is `continuousOn_clm_comp_of_isCompactOperator`; the induction step shows that
`x ↦ A(x) ∘ ι` is differentiable with derivative `δx ↦ (y' ↦ D_x(A(x)(ιy'))δx)` by the mean value
inequality along segments in `s` (uniformly in `y'` of norm `≤ 1`, by the uniform continuity of the
partial derivative on `{x} × ι(B̄₁)`), and applies the induction hypothesis to the partial
derivative `(x, y) ↦ D_x(A(x)y) ∈ L(X, Z)`, which is `C^{k−1}` and linear in `y`. -/
theorem contDiffOn_clm_comp_of_isCompactOperator {s : Set X}
    (hs : ∃ O C : Set X, IsOpen O ∧ Convex ℝ C ∧ s = O ∩ C) (hsu : UniqueDiffOn ℝ s)
    {ι : Y' →L[ℝ] Y} (hι : IsCompactOperator ι) :
    ∀ {k : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {A : X → Y →L[ℝ] Z},
      ContDiffOn ℝ k (fun p : X × Y => A p.1 p.2) (s ×ˢ univ) →
        ContDiffOn ℝ k (fun x => (A x).comp ι) s
  | 0, Z, _, _, A, hA => by
    rw [Nat.cast_zero, contDiffOn_zero] at hA ⊢
    exact continuousOn_clm_comp_of_isCompactOperator hA hι
  | k + 1, Z, _, _, A, hA => by
    classical
    set Φ : X × Y → Z := fun p => A p.1 p.2 with hΦdef
    set t : Set (X × Y) := s ×ˢ univ with htdef
    have htu : UniqueDiffOn ℝ t := hsu.prod uniqueDiffOn_univ
    have hk1 : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hk1] at hA ⊢
    -- the partial derivative in `x`
    set Bf : X → Y → X →L[ℝ] Z :=
      fun x y => (fderivWithin ℝ Φ t (x, y)).comp (ContinuousLinearMap.inl ℝ X Y) with hBf
    have hΦ' : ContDiffOn ℝ k (fderivWithin ℝ Φ t) t := hA.fderivWithin htu le_rfl
    have hBk : ContDiffOn ℝ k (fun p : X × Y => Bf p.1 p.2) t := hΦ'.clm_comp contDiffOn_const
    have hBcont : ContinuousOn (fun p : X × Y => Bf p.1 p.2) t := hBk.continuousOn
    have hderiv : ∀ x ∈ s, ∀ y, HasFDerivWithinAt (fun x => A x y) (Bf x y) s x := by
      intro x hx y
      have hxy : (x, y) ∈ t := mk_mem_prod hx (mem_univ y)
      have h1 : HasFDerivWithinAt Φ (fderivWithin ℝ Φ t (x, y)) t (x, y) :=
        (hA.differentiableOn (by simp) (x, y) hxy).hasFDerivWithinAt
      have h2 : HasFDerivWithinAt (fun x : X => (x, y)) (ContinuousLinearMap.inl ℝ X Y) s x :=
        (hasFDerivWithinAt_id x s).prodMk (hasFDerivWithinAt_const y x s)
      exact h1.comp x h2 fun x hx => mk_mem_prod hx (mem_univ _)
    -- `Bf x` is linear and continuous in `y` for `x ∈ s`
    have hadd : ∀ x ∈ s, ∀ y₁ y₂, Bf x (y₁ + y₂) = Bf x y₁ + Bf x y₂ := by
      intro x hx y₁ y₂
      have h := (hderiv x hx y₁).add (hderiv x hx y₂)
      exact (hsu x hx).eq (hderiv x hx _) (h.congr' (fun z _ => by simp) hx)
    have hsmul : ∀ x ∈ s, ∀ (a : ℝ) (y : Y), Bf x (a • y) = a • Bf x y := by
      intro x hx a y
      have h := (hderiv x hx y).const_smul a
      exact (hsu x hx).eq (hderiv x hx _) (h.congr' (fun z _ => by simp) hx)
    let B : X → Y →L[ℝ] (X →L[ℝ] Z) := fun x =>
      if hx : x ∈ s then
        { toFun := Bf x
          map_add' := hadd x hx
          map_smul' := hsmul x hx
          cont := hBcont.comp_continuous (f := fun y => (x, y)) (by fun_prop)
            fun y => ⟨hx, mem_univ _⟩ }
      else 0
    have hB : ∀ x ∈ s, ∀ y, B x y = Bf x y := fun x hx y => by
      simp only [B, dif_pos hx]; rfl
    -- the induction hypothesis for `B`
    have hBk' : ContDiffOn ℝ k (fun p : X × Y => B p.1 p.2) t :=
      hBk.congr fun p hp => hB p.1 hp.1 p.2
    have hIH : ContDiffOn ℝ k (fun x => (B x).comp ι) s :=
      contDiffOn_clm_comp_of_isCompactOperator hs hsu hι hBk'
    -- the candidate derivative
    set G' : X → X →L[ℝ] (Y' →L[ℝ] Z) := fun x => ((B x).comp ι).flip with hG'
    have hG'k : ContDiffOn ℝ k G' s :=
      (ContinuousLinearMap.flipₗᵢ ℝ Y' X Z).toContinuousLinearEquiv.contDiff.comp_contDiffOn hIH
    -- differentiability of `x ↦ A(x) ∘ ι` with derivative `G'`
    have hGd : ∀ x ∈ s, HasFDerivWithinAt (fun x => (A x).comp ι) (G' x) s x := by
      intro x hx
      obtain ⟨O, C, hO, hC, hsOC⟩ := hs
      obtain ⟨K, hK, hKsub⟩ := hι.image_closedBall_subset_compact (f := (ι : Y' →ₗ[ℝ] Y)) 1
      have hxO : x ∈ O := (hsOC ▸ hx).1
      obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO x hxO
      rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
      intro c hc
      obtain ⟨δ, hδ, hδ'⟩ := exists_delta_of_continuousOn hBcont hx hK hc
      have ev1 : ∀ᶠ z in 𝓝[s] x, z ∈ s := self_mem_nhdsWithin
      have ev2 : ∀ᶠ z in 𝓝[s] x, dist z x < min ρ δ :=
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (lt_min hρ hδ))
      filter_upwards [ev1, ev2] with z hz hzd
      have hzρ : ‖z - x‖ < ρ := by
        rw [← dist_eq_norm]; exact lt_of_lt_of_le hzd (min_le_left _ _)
      have hzδ : ‖z - x‖ < δ := by
        rw [← dist_eq_norm]; exact lt_of_lt_of_le hzd (min_le_right _ _)
      -- the segment from `x` to `z` lies in `s`
      have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • (z - x) ∈ s := by
        intro τ hτ
        rw [hsOC]
        refine ⟨hρO ?_, hC.add_smul_sub_mem (hsOC ▸ hx).2 (hsOC ▸ hz).2 hτ⟩
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hτ.1]
        calc τ * ‖z - x‖ ≤ 1 * ‖z - x‖ := mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg _)
          _ < ρ := by rw [one_mul]; exact hzρ
      have hsegδ : ∀ τ ∈ Icc (0 : ℝ) 1, ‖x + τ • (z - x) - x‖ < δ := by
        intro τ hτ
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
        calc τ * ‖z - x‖ ≤ 1 * ‖z - x‖ := mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg _)
          _ < δ := by rw [one_mul]; exact hzδ
      -- the operator norm bound, on unit vectors
      refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun v hv => ?_
      have hwK : ι v ∈ K := hKsub ⟨v, by rw [mem_closedBall, dist_zero_right, hv], rfl⟩
      have hval : ((A z).comp ι - (A x).comp ι - G' x (z - x)) v =
          A z (ι v) - A x (ι v) - Bf x (ι v) (z - x) := by
        simp only [sub_apply, ContinuousLinearMap.comp_apply, hG',
          ContinuousLinearMap.flip_apply, hB x hx]
      rw [hval]
      -- the mean value inequality along the segment
      set φ : ℝ → Z := fun τ => A (x + τ • (z - x)) (ι v) - τ • Bf x (ι v) (z - x) with hφ
      have hγ : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => x + τ • (z - x)) (z - x) τ := fun τ => by
        simpa using ((hasDerivAt_id τ).smul_const (z - x)).const_add x
      have hder : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ
          (Bf (x + τ • (z - x)) (ι v) (z - x) - Bf x (ι v) (z - x)) (Icc 0 1) τ := by
        intro τ hτ
        have h1 : HasDerivWithinAt (fun τ : ℝ => A (x + τ • (z - x)) (ι v))
            (Bf (x + τ • (z - x)) (ι v) (z - x)) (Icc 0 1) τ :=
          HasFDerivWithinAt.comp_hasDerivWithinAt (l := fun x => A x (ι v))
            (f := fun τ : ℝ => x + τ • (z - x)) τ (hderiv _ (hseg τ hτ) (ι v))
            (hγ τ).hasDerivWithinAt hseg
        have h2 : HasDerivWithinAt (fun τ : ℝ => τ • Bf x (ι v) (z - x)) (Bf x (ι v) (z - x))
            (Icc 0 1) τ := by
          simpa using ((hasDerivAt_id τ).smul_const (Bf x (ι v) (z - x))).hasDerivWithinAt
        exact h1.sub h2
      have hbound : ∀ τ ∈ Icc (0 : ℝ) 1,
          ‖Bf (x + τ • (z - x)) (ι v) (z - x) - Bf x (ι v) (z - x)‖ ≤ c * ‖z - x‖ := by
        intro τ hτ
        have := hδ' _ (hseg τ hτ) (hsegδ τ hτ) (ι v) hwK
        calc ‖Bf (x + τ • (z - x)) (ι v) (z - x) - Bf x (ι v) (z - x)‖
            = ‖(Bf (x + τ • (z - x)) (ι v) - Bf x (ι v)) (z - x)‖ := by
              rw [sub_apply]
          _ ≤ ‖Bf (x + τ • (z - x)) (ι v) - Bf x (ι v)‖ * ‖z - x‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ c * ‖z - x‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc 0 1)
        (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
      have h01 : φ 1 - φ 0 = A z (ι v) - A x (ι v) - Bf x (ι v) (z - x) := by
        simp only [hφ, one_smul, zero_smul, add_zero, sub_zero, add_sub_cancel]; abel
      rwa [h01, sub_zero, norm_one, mul_one] at this
    exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hsu).2
      ⟨fun h0 => absurd h0 (by simp), G', hG'k, hGd⟩

end CompactOpen

/-! ### Levels of the shifted space `E¹` and of the tangent `TE` -/

namespace ScBanach

variable (E : ScBanach)

/-- The level sets of `U¹ = U_1 ⊆ (E¹)₀` are those of `U`, shifted by one. -/
lemma shift_lvlSet (U : Set (E 0)) (m : ℕ) :
    E.shift.lvlSet (E.lvlSet U 1) m = E.lvlSet U (m + 1) := by
  ext x
  rw [mem_lvlSet, mem_lvlSet, mem_lvlSet, ← E.shift_toBase]

lemma mem_lvlSet_shift_toBase {U : Set (E 0)} {m : ℕ} {x : E (m + 1)} :
    E.shift.toBase m x ∈ E.lvlSet U 1 ↔ x ∈ E.lvlSet U (m + 1) := by
  rw [mem_lvlSet, mem_lvlSet, ← E.shift_toBase]

/-- `T(U¹) = (TU)¹`: the level-`1` part of `TU ⊆ TE` is `T(U_1) ⊆ T(E¹) = (TE)¹`. -/
lemma shift_tangentSet (U : Set (E 0)) :
    E.tangent.lvlSet (E.tangentSet U) 1 = E.shift.tangentSet (E.lvlSet U 1) := by
  ext p
  rw [mem_lvlSet_tangentSet]
  exact Iff.rfl

lemma inclK_mem_lvlSet {U : Set (E 0)} {m k : ℕ} {x : E (m + k)} (hx : x ∈ E.lvlSet U (m + k)) :
    E.inclK m k x ∈ E.lvlSet U m := by
  rw [mem_lvlSet, E.toBase_inclK]; exact hx

/-- The inclusion `E_{m+k+1} → E_{m+1}` (the `inclK` of `E¹`) maps `U_{m+k+1}` into `U_{m+1}`. -/
lemma shift_inclK_mem_lvlSet {U : Set (E 0)} {m k : ℕ} {x : E (m + k + 1)}
    (hx : x ∈ E.lvlSet U (m + k + 1)) : E.shift.inclK m k x ∈ E.lvlSet U (m + 1) := by
  rw [← E.shift_lvlSet] at hx ⊢
  exact E.shift.inclK_mem_lvlSet hx

/-- `E_{m+k+1} → E_{m+1} → E_m` is `E_{m+(k+1)} → E_m`. -/
lemma incl_shift_inclK (m : ℕ) : ∀ (k : ℕ) (x : E (m + k + 1)),
    E.incl m (E.shift.inclK m k x) = E.inclK m (k + 1) x
  | 0, _ => rfl
  | k + 1, x => incl_shift_inclK m k (E.incl (m + k + 1) x)

/-- The inclusions of `TE` are those of `E¹` and `E`. -/
lemma tangent_inclK (m : ℕ) : ∀ (k : ℕ) (p : E.tangent (m + k)),
    E.tangent.inclK m k p = ((E.shift.inclK m k p.1, E.inclK m k p.2) : E.tangent m)
  | 0, _ => rfl
  | k + 1, p => tangent_inclK m k (E.tangent.incl (m + k) p)

end ScBanach

variable {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0} {D : E 1 → E 0 →L[ℝ] F 0}

/-- The level maps of `f : U¹ → F¹` (the map `levelMap f 1 : U_1 → F_1` between the shifted
spaces) are the level maps of `f`, shifted by one. -/
lemma IsSc0.levelMap_shift (hf : IsSc0 E F U f) {m : ℕ} {x : E (m + 1)}
    (hx : x ∈ E.lvlSet U (m + 1)) :
    levelMap (E := E.shift) (F := F.shift) (levelMap f 1) m x = levelMap f (m + 1) x := by
  apply levelMap_eq_of_toBase_eq
  apply F.toBase_injective 1
  rw [← F.shift_toBase, hf.toBase_levelMap hx,
    hf.toBase_levelMap (E.mem_lvlSet_shift_toBase.2 hx), E.shift_toBase]

/-- **Proposition 1.17 for sc⁰**: if `f : U → F` is sc⁰ then `f : U¹ → F¹` is sc⁰ (no hypothesis
on `U`). -/
theorem IsSc0.shift (hf : IsSc0 E F U f) :
    IsSc0 E.shift F.shift (E.lvlSet U 1) (levelMap f 1) where
  mem_range m x hx := by
    rw [E.shift_lvlSet] at hx
    refine ⟨levelMap f (m + 1) x, ?_⟩
    apply F.toBase_injective 1
    rw [← F.shift_toBase, hf.toBase_levelMap hx,
      hf.toBase_levelMap (E.mem_lvlSet_shift_toBase.2 hx), E.shift_toBase]
  continuousOn m := by
    rw [E.shift_lvlSet]
    exact (hf.continuousOn (m + 1)).congr fun x hx => hf.levelMap_shift hx

/-- `U¹ = U_1` is an sc-domain in `E¹` when `U` is one in `E`. -/
lemma IsScDomain.shift (hU : IsScDomain E U) : IsScDomain E.shift (E.lvlSet U 1) where
  relOpenConvex m := by rw [E.shift_lvlSet]; exact hU.relOpenConvex (m + 1)
  uniqueDiffWithinAt m x hx := by
    rw [E.shift_lvlSet] at hx ⊢; exact hU.uniqueDiffWithinAt (m + 1) x hx

/-! ### The level operators `Df(x) : E_m → F_m` -/

open scoped Classical in
/-- The **level-`m` operator** of a derivative family `D` (`D x = Df(x) : E₀ → F₀` for `x ∈ E₁`) at
`x ∈ E_{m+1}`: the continuous linear `T : E_m → F_m` with `ι_m ∘ T = Df(x) ∘ ι_m`, i.e. the operator
`Df(x) : E_m → F_m` of Proposition 1.16 (2), when it exists (a junk value otherwise; it is unique
by the injectivity of `ι_m`). -/
def levelDeriv (D : E 1 → E 0 →L[ℝ] F 0) (m : ℕ) (x : E (m + 1)) : E m →L[ℝ] F m :=
  if h : ∃ T : E m →L[ℝ] F m, ∀ v, F.toBase m (T v) = D (E.shift.toBase m x) (E.toBase m v) then
    h.choose
  else 0

lemma toBase_levelDeriv {m : ℕ} {x : E (m + 1)}
    (h : ∃ T : E m →L[ℝ] F m, ∀ v, F.toBase m (T v) = D (E.shift.toBase m x) (E.toBase m v))
    (v : E m) : F.toBase m (levelDeriv D m x v) = D (E.shift.toBase m x) (E.toBase m v) := by
  rw [levelDeriv, dif_pos h]; exact h.choose_spec v

/-- On level `0` the level operator is `Df(x)` itself. -/
@[simp] lemma levelDeriv_zero (D : E 1 → E 0 →L[ℝ] F 0) (x : E 1) : levelDeriv D 0 x = D x := by
  ext v
  exact toBase_levelDeriv (D := D) (m := 0) ⟨D x, fun _ => rfl⟩ v

namespace IsSc1With

/-- For an sc¹ map and `x ∈ U_{m+1}`, the level-`m` operator `Df(x) : E_m → F_m` exists: it is the
second component of the level-`m` tangent map `(x, h) ↦ (f(x), Df(x)h)`, which is linear and
continuous in `h` (condition (3) of Definition 1.14). -/
theorem exists_levelDeriv (h : IsSc1With U f D) {m : ℕ} {x : E (m + 1)}
    (hx : x ∈ E.lvlSet U (m + 1)) :
    ∃ T : E m →L[ℝ] F m, ∀ v, F.toBase m (T v) = D (E.shift.toBase m x) (E.toBase m v) := by
  have hmem : ∀ v : E m, ((x, v) : E.tangent m) ∈ E.tangent.lvlSet (E.tangentSet U) m :=
    fun v => by rw [ScBanach.mem_lvlSet_tangentSet]; exact hx
  set Tm : E m → F m := fun v => (levelMap (tangentMapWith f D) m ((x, v) : E.tangent m)).2 with hTm
  have hTm' : ∀ v, F.toBase m (Tm v) = D (E.shift.toBase m x) (E.toBase m v) := by
    intro v
    have := congrArg Prod.snd (h.tangent_isSc0.toBase_levelMap (hmem v))
    rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase] at this
    exact this
  have hcont : Continuous Tm := by
    have := (h.tangent_isSc0.continuousOn m).comp_continuous
      (f := fun v : E m => ((x, v) : E.tangent m)) (by fun_prop) hmem
    exact continuous_snd.comp this
  exact ⟨{ toFun := Tm
           map_add' := fun v w => F.toBase_injective m (by
             rw [map_add, hTm', hTm', hTm', map_add, map_add])
           map_smul' := fun a v => F.toBase_injective m (by
             rw [map_smul, hTm', hTm', map_smul, map_smul]; rfl)
           cont := hcont }, hTm'⟩

/-- `ι_m ∘ Df(x)|_{E_m} = Df(x) ∘ ι_m` for `x ∈ U_{m+1}`. -/
theorem toBase_levelDeriv (h : IsSc1With U f D) {m : ℕ} {x : E (m + 1)}
    (hx : x ∈ E.lvlSet U (m + 1)) (v : E m) :
    F.toBase m (levelDeriv D m x v) = D (E.shift.toBase m x) (E.toBase m v) :=
  Polyfold.toBase_levelDeriv (h.exists_levelDeriv hx) v

/-- The level-`m` tangent map is `(x, h) ↦ (f(x), Df(x)h)` on `(TU)_m = U_{m+1} × E_m`, with the
level operators. -/
theorem levelMap_tangentMapWith (h : IsSc1With U f D) {m : ℕ} {p : E.tangent m}
    (hp : p ∈ E.tangent.lvlSet (E.tangentSet U) m) :
    levelMap (tangentMapWith f D) m p =
      ((levelMap f (m + 1) p.1, levelDeriv D m p.1 p.2) : F.tangent m) := by
  rw [ScBanach.mem_lvlSet_tangentSet] at hp
  apply levelMap_eq_of_toBase_eq
  rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase]
  change ((F.shift.toBase m (levelMap f (m + 1) p.1), F.toBase m (levelDeriv D m p.1 p.2)) :
    F.tangent 0) = (levelMap f 1 (E.shift.toBase m p.1), D (E.shift.toBase m p.1) (E.toBase m p.2))
  refine Prod.ext ?_ (h.toBase_levelDeriv hp p.2)
  apply F.toBase_injective 1
  rw [← F.shift_toBase, h.isSc0.toBase_levelMap hp,
    h.isSc0.toBase_levelMap (E.mem_lvlSet_shift_toBase.2 hp), E.shift_toBase]

/-- **Proposition 1.16 (2)** (condition (3) of Definition 1.14 on level `m`): `(x, h) ↦ Df(x)h` is
continuous `U_{m+1} × E_m → F_m`. -/
theorem continuousOn_levelDeriv (h : IsSc1With U f D) (m : ℕ) :
    ContinuousOn (fun p : E (m + 1) × E m => levelDeriv D m p.1 p.2)
      (E.lvlSet U (m + 1) ×ˢ univ) := by
  have := h.tangent_isSc0.continuousOn m
  rw [ScBanach.lvlSet_tangentSet] at this
  refine (continuous_snd.comp_continuousOn this).congr fun p hp => ?_
  have hp' : p ∈ E.tangent.lvlSet (E.tangentSet U) m := by
    rw [ScBanach.lvlSet_tangentSet]; exact hp
  rw [Function.comp_apply, h.levelMap_tangentMapWith hp']

/-- **Proposition 1.16 (1), continuity of `df`**: `x ↦ Df(x)|_{E_{m+1}}` is continuous
`U_{m+1} → L(E_{m+1}, F_m)` in the operator norm (the compactness argument of
[25, Proposition 2.1], here the compact-open lemma for `k = 0`). -/
theorem continuousOn_levelDeriv_clm (h : IsSc1With U f D) (m : ℕ) :
    ContinuousOn (fun x => (levelDeriv D m x).comp (E.incl m)) (E.lvlSet U (m + 1)) :=
  continuousOn_clm_comp_of_isCompactOperator (A := levelDeriv D m) (h.continuousOn_levelDeriv m)
    (E.incl_isCompactOperator m)

/-- **Proposition 1.16 (1), differentiability** (the level-raising step of [25, Proposition 2.1]):
for an sc¹ map on an sc-domain, `f : U_{m+1} → F_m` is differentiable at every `x ∈ U_{m+1}`
within `U_{m+1}`, with derivative `Df(x)|_{E_{m+1}}`.

The proof is the integral representation `f(x+k) − f(x) = ∫₀¹ Df(x+τk)k dτ`: the integrand is
continuous into `F_m` (condition (3) on level `m`), so the Bochner integral exists in `F_m`; its
image under `ι_m` is `∫₀¹ Df(x+τk)k dτ` in `F_0`, which is `f(x+k) − f(x)` by the fundamental
theorem of calculus for the `C¹` map `f : U_1 → F_0`.  Then
`‖f(x+k) − f(x) − Df(x)k‖_m ≤ sup_τ ‖(Df(x+τk) − Df(x))|_{E_{m+1}}‖ ‖k‖_{m+1}`, and the operator
norm tends to `0` by `continuousOn_levelDeriv_clm`. -/
theorem hasFDerivWithinAt_level (hU : IsScDomain E U) (h : IsSc1With U f D) {m : ℕ}
    {x : E (m + 1)} (hx : x ∈ E.lvlSet U (m + 1)) :
    HasFDerivWithinAt (levelMap f m ∘ E.incl m) ((levelDeriv D m x).comp (E.incl m))
      (E.lvlSet U (m + 1)) x := by
  obtain ⟨O, C, hO, hC, hUOC⟩ := hU.relOpenConvex (m + 1)
  have hxO : x ∈ O := (hUOC ▸ hx).1
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO x hxO
  have hcont := h.continuousOn_levelDeriv_clm m x hx
  rw [Metric.continuousWithinAt_iff] at hcont
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδ'⟩ := hcont c hc
  have ev1 : ∀ᶠ z in 𝓝[E.lvlSet U (m + 1)] x, z ∈ E.lvlSet U (m + 1) := self_mem_nhdsWithin
  have ev2 : ∀ᶠ z in 𝓝[E.lvlSet U (m + 1)] x, dist z x < min ρ δ :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (lt_min hρ hδ))
  filter_upwards [ev1, ev2] with z hz hzd
  set k := z - x with hk
  have hkρ : ‖k‖ < ρ := by rw [hk, ← dist_eq_norm]; exact lt_of_lt_of_le hzd (min_le_left _ _)
  have hkδ : ‖k‖ < δ := by rw [hk, ← dist_eq_norm]; exact lt_of_lt_of_le hzd (min_le_right _ _)
  -- the segment from `x` to `z` lies in `U_{m+1}`
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • k ∈ E.lvlSet U (m + 1) := by
    intro τ hτ
    rw [hUOC]
    refine ⟨hρO ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hτ.1]
      calc τ * ‖k‖ ≤ 1 * ‖k‖ := mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg _)
        _ < ρ := by rw [one_mul]; exact hkρ
    · have := hC.add_smul_sub_mem (hUOC ▸ hx).2 (hUOC ▸ hz).2 hτ
      rwa [hk]
  have hsegδ : ∀ τ ∈ Icc (0 : ℝ) 1, dist (x + τ • k) x < δ := by
    intro τ hτ
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    calc τ * ‖k‖ ≤ 1 * ‖k‖ := mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg _)
      _ < δ := by rw [one_mul]; exact hkδ
  have hseg₁ : ∀ τ ∈ Icc (0 : ℝ) 1,
      E.shift.toBase m x + τ • E.shift.toBase m k ∈ E.lvlSet U 1 := fun τ hτ => by
    rw [← map_smul, ← map_add]; exact E.mem_lvlSet_shift_toBase.2 (hseg τ hτ)
  -- the integrand `τ ↦ Df(x + τk)k` in `F_m`
  set g : ℝ → F m := fun τ => levelDeriv D m (x + τ • k) (E.incl m k) with hg
  have hgc : ContinuousOn g (Icc 0 1) :=
    (h.continuousOn_levelDeriv m).comp (f := fun τ : ℝ => (x + τ • k, E.incl m k))
      (Continuous.continuousOn (by fun_prop)) fun τ hτ => mk_mem_prod (hseg τ hτ) (mem_univ _)
  have hgi : IntervalIntegrable g volume 0 1 := hgc.intervalIntegrable_of_Icc zero_le_one
  -- the fundamental theorem of calculus for `f : U_1 → F_0` along the segment
  set φ : ℝ → F 0 := fun τ => f (E.toBase 1 (E.shift.toBase m x + τ • E.shift.toBase m k)) with hφ
  have hγ : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => E.shift.toBase m x + τ • E.shift.toBase m k)
      (E.shift.toBase m k) τ := fun τ => by
    simpa using ((hasDerivAt_id τ).smul_const (E.shift.toBase m k)).const_add (E.shift.toBase m x)
  have hφd : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ
      (D (E.shift.toBase m x + τ • E.shift.toBase m k) (E.toBase 1 (E.shift.toBase m k)))
      (Icc 0 1) τ := fun τ hτ =>
    HasFDerivWithinAt.comp_hasDerivWithinAt (l := f ∘ E.toBase 1)
      (f := fun τ : ℝ => E.shift.toBase m x + τ • E.shift.toBase m k) τ
      (h.hasFDerivWithinAt _ (hseg₁ τ hτ)) (hγ τ).hasDerivWithinAt hseg₁
  have hφ'i : IntervalIntegrable
      (fun τ => D (E.shift.toBase m x + τ • E.shift.toBase m k) (E.toBase 1 (E.shift.toBase m k)))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
    exact h.continuousOn_deriv.comp
      (f := fun τ : ℝ => (E.shift.toBase m x + τ • E.shift.toBase m k, E.toBase 1 (E.shift.toBase m k)))
      (Continuous.continuousOn (by fun_prop)) fun τ hτ => hseg₁ τ hτ
  have hFTC : ∫ τ in (0 : ℝ)..1,
      D (E.shift.toBase m x + τ • E.shift.toBase m k) (E.toBase 1 (E.shift.toBase m k)) =
        φ 1 - φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (fun τ hτ => (hφd τ hτ).continuousWithinAt)
      (fun τ hτ => (hφd τ (Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)) hφ'i
  have e1 : φ 1 = f (E.toBase m (E.incl m z)) := by
    simp only [hφ, one_smul, ← map_add, hk, add_sub_cancel, ← E.shift_toBase]; rfl
  have e0 : φ 0 = f (E.toBase m (E.incl m x)) := by
    simp only [hφ, zero_smul, add_zero, ← E.shift_toBase]; rfl
  -- the integral representation in `F_m`
  have hint : levelMap f m (E.incl m z) - levelMap f m (E.incl m x) = ∫ τ in (0 : ℝ)..1, g τ := by
    apply F.toBase_injective m
    rw [map_sub, h.isSc0.toBase_levelMap (m := m) (x := E.incl m z) hz,
      h.isSc0.toBase_levelMap (m := m) (x := E.incl m x) hx,
      ← (F.toBase m).intervalIntegral_comp_comm hgi,
      intervalIntegral.integral_congr (g := fun τ =>
        D (E.shift.toBase m x + τ • E.shift.toBase m k) (E.toBase 1 (E.shift.toBase m k))) ?_,
      hFTC, e1, e0]
    intro τ hτ
    rw [uIcc_of_le zero_le_one] at hτ
    simp only [hg]
    rw [h.toBase_levelDeriv (hseg τ hτ), map_add, map_smul, ← E.shift_toBase]
    rfl
  -- the estimate
  have hconst : ((levelDeriv D m x).comp (E.incl m)) k =
      ∫ τ in (0 : ℝ)..1, levelDeriv D m x (E.incl m k) := by
    rw [intervalIntegral.integral_const, sub_zero, one_smul]; rfl
  change ‖levelMap f m (E.incl m z) - levelMap f m (E.incl m x) - _‖ ≤ _
  rw [hint, hconst, ← intervalIntegral.integral_sub hgi intervalIntegrable_const]
  have hbd : ∀ τ ∈ Set.uIoc (0 : ℝ) 1, ‖g τ - levelDeriv D m x (E.incl m k)‖ ≤ c * ‖k‖ := by
    intro τ hτ
    rw [uIoc_of_le zero_le_one] at hτ
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1.le, hτ.2⟩
    have h1 := hδ' (hseg τ hτ') (hsegδ τ hτ')
    rw [dist_eq_norm] at h1
    calc ‖g τ - levelDeriv D m x (E.incl m k)‖
        = ‖((levelDeriv D m (x + τ • k)).comp (E.incl m) -
            (levelDeriv D m x).comp (E.incl m)) k‖ := rfl
      _ ≤ ‖(levelDeriv D m (x + τ • k)).comp (E.incl m) -
            (levelDeriv D m x).comp (E.incl m)‖ * ‖k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖k‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  simpa using this

/-- **Proposition 1.16 (1)** for an sc¹ map: `f : U_{m+1} → F_m` is `C¹` on `U_{m+1}` for every `m`
(Proposition 1.18 for `k = 1`). -/
theorem contDiffOn_level (hU : IsScDomain E U) (h : IsSc1With U f D) (m : ℕ) :
    ContDiffOn ℝ 1 (levelMap f m ∘ E.incl m) (E.lvlSet U (m + 1)) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (hU.uniqueDiffWithinAt (m + 1))]
  refine ⟨fun h0 => absurd h0 (by simp), fun x => (levelDeriv D m x).comp (E.incl m), ?_,
    fun x hx => h.hasFDerivWithinAt_level hU hx⟩
  rw [contDiffOn_zero]; exact h.continuousOn_levelDeriv_clm m

/-- The level operator is the derivative of `f : U_m → F_m` when the latter exists: if
`f_m : U_m → F_m` is differentiable at `x ∈ U_{m+1} ⊆ U_m` within `U_m` with derivative `L`, then
`L = Df(x)|_{E_m}` (uniqueness of derivatives on `U_{m+1}` and density of `E_{m+1}` in `E_m`;
Lemma 3.H of the exposition). -/
theorem levelDeriv_eq (hU : IsScDomain E U) (h : IsSc1With U f D) {m : ℕ} {x : E (m + 1)}
    (hx : x ∈ E.lvlSet U (m + 1)) {L : E m →L[ℝ] F m}
    (hL : HasFDerivWithinAt (levelMap f m) L (E.lvlSet U m) (E.incl m x)) :
    levelDeriv D m x = L := by
  have h1 : HasFDerivWithinAt (f ∘ E.toBase (m + 1)) (((F.toBase m).comp L).comp (E.incl m))
      (E.lvlSet U (m + 1)) x := by
    have := ((F.toBase m).hasFDerivAt.comp_hasFDerivWithinAt _ hL).comp x
      (E.incl m).hasFDerivWithinAt fun y hy => hy
    exact this.congr (fun y hy => (h.isSc0.toBase_levelMap (m := m) (x := E.incl m y) hy).symm)
      (h.isSc0.toBase_levelMap (m := m) (x := E.incl m x) hx).symm
  have h2 : HasFDerivWithinAt (f ∘ E.toBase (m + 1))
      ((D (E.shift.toBase m x)).comp (E.toBase (m + 1))) (E.lvlSet U (m + 1)) x := by
    have := (h.hasFDerivWithinAt _ (E.mem_lvlSet_shift_toBase.2 hx)).comp x
      (E.shift.toBase m).hasFDerivWithinAt fun y hy => E.mem_lvlSet_shift_toBase.2 hy
    refine (this.congr (fun y _ => congrArg f (E.shift_toBase m y))
      (congrArg f (E.shift_toBase m x))).congr_fderiv ?_
    ext y
    exact congrArg (D (E.shift.toBase m x)) (E.shift_toBase m y).symm
  have heq := (hU.uniqueDiffWithinAt (m + 1) x hx).eq h1 h2
  have hd : Dense (Submodule.span ℝ (range (E.incl m)) : Set (E m)) :=
    Dense.mono Submodule.subset_span (E.denseRange_incl m)
  have h3 : (F.toBase m).comp L = (D (E.shift.toBase m x)).comp (E.toBase m) := by
    refine ContinuousLinearMap.ext_on hd ?_
    rintro _ ⟨w, rfl⟩
    exact congrArg (fun T : E (m + 1) →L[ℝ] F 0 => T w) heq
  ext v
  apply F.toBase_injective m
  rw [h.toBase_levelDeriv hx]
  exact (congrArg (fun T : E m →L[ℝ] F 0 => T v) h3).symm

end IsSc1With

/-! ### Proposition 1.16 -/

/-- **The level conditions of Proposition 1.16** for a family of operators `Dl m x ∈ L(E_m, F_m)`,
`x ∈ E_{m+1}` (the text's `Df(x) : E_{m−1} → F_{m−1}`, `x ∈ U_m`, with `m − 1` written `m`):
(1) `f : U_{m+1} → F_m` is differentiable at every `x ∈ U_{m+1}` with derivative `Dl m x|_{E_{m+1}}`
(so `Dl m x` is the extension of `df(x)` of condition (2)), and (2) `(x, h) ↦ Dl m x h` is
continuous on `U_{m+1} × E_m`.  The continuity of `df : U_{m+1} → L(E_{m+1}, F_m)` and the `C¹`
statement of (1) follow (`IsSc1Levels.continuousOn_clm`, `IsSc1Levels.contDiffOn`). -/
structure IsSc1Levels (U : Set (E 0)) (f : E 0 → F 0) (Dl : ∀ m, E (m + 1) → E m →L[ℝ] F m) :
    Prop where
  hasFDerivWithinAt : ∀ m, ∀ x ∈ E.lvlSet U (m + 1),
    HasFDerivWithinAt (levelMap f m ∘ E.incl m) ((Dl m x).comp (E.incl m)) (E.lvlSet U (m + 1)) x
  continuousOn : ∀ m,
    ContinuousOn (fun p : E (m + 1) × E m => Dl m p.1 p.2) (E.lvlSet U (m + 1) ×ˢ univ)

namespace IsSc1Levels

variable {Dl : ∀ m, E (m + 1) → E m →L[ℝ] F m}

/-- Proposition 1.16 (1): `df : U_{m+1} → L(E_{m+1}, F_m)` is continuous. -/
theorem continuousOn_clm (h : IsSc1Levels U f Dl) (m : ℕ) :
    ContinuousOn (fun x => (Dl m x).comp (E.incl m)) (E.lvlSet U (m + 1)) :=
  continuousOn_clm_comp_of_isCompactOperator (A := Dl m) (h.continuousOn m)
    (E.incl_isCompactOperator m)

/-- Proposition 1.16 (1): `f : U_{m+1} → F_m` is `C¹`. -/
theorem contDiffOn (hU : IsScDomain E U) (h : IsSc1Levels U f Dl) (m : ℕ) :
    ContDiffOn ℝ 1 (levelMap f m ∘ E.incl m) (E.lvlSet U (m + 1)) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (hU.uniqueDiffWithinAt (m + 1))]
  refine ⟨fun h0 => absurd h0 (by simp), fun x => (Dl m x).comp (E.incl m), ?_,
    h.hasFDerivWithinAt m⟩
  rw [contDiffOn_zero]; exact h.continuousOn_clm m

/-- The level operators are the restrictions of the level-`0` operator: `ι_m ∘ Dl m x = Dl 0 x ∘ ι_m`
for `x ∈ U_{m+1}` (Lemma 3.H of the exposition: by the uniqueness of the derivative of
`f : U_{m+1} → F_0` at `x` and the density of `E_{m+1}` in `E_m`).  The text writes `Df(x)` for
all these operators without comment. -/
theorem toBase_apply (hU : IsScDomain E U) (hf : IsSc0 E F U f) (h : IsSc1Levels U f Dl) {m : ℕ}
    {x : E (m + 1)} (hx : x ∈ E.lvlSet U (m + 1)) (v : E m) :
    F.toBase m (Dl m x v) = Dl 0 (E.shift.toBase m x) (E.toBase m v) := by
  have h1 : HasFDerivWithinAt (f ∘ E.toBase (m + 1)) ((F.toBase m).comp ((Dl m x).comp (E.incl m)))
      (E.lvlSet U (m + 1)) x := by
    have := (F.toBase m).hasFDerivAt.comp_hasFDerivWithinAt x (h.hasFDerivWithinAt m x hx)
    exact this.congr (fun y hy => (hf.toBase_levelMap (m := m) (x := E.incl m y) hy).symm)
      (hf.toBase_levelMap (m := m) (x := E.incl m x) hx).symm
  have h2 : HasFDerivWithinAt (f ∘ E.toBase (m + 1))
      (((Dl 0 (E.shift.toBase m x)).comp (E.incl 0)).comp (E.shift.toBase m))
      (E.lvlSet U (m + 1)) x := by
    have h0 := h.hasFDerivWithinAt 0 _ (E.mem_lvlSet_shift_toBase.2 hx)
    rw [funext (levelMap_zero f)] at h0
    have := h0.comp x (E.shift.toBase m).hasFDerivWithinAt
      fun y hy => E.mem_lvlSet_shift_toBase.2 hy
    exact this.congr (fun y _ => congrArg f (E.shift_toBase m y)) (congrArg f (E.shift_toBase m x))
  have heq := (hU.uniqueDiffWithinAt (m + 1) x hx).eq h1 h2
  have hd : Dense (Submodule.span ℝ (range (E.incl m)) : Set (E m)) :=
    Dense.mono Submodule.subset_span (E.denseRange_incl m)
  have h3 : (F.toBase m).comp (Dl m x) = (Dl 0 (E.shift.toBase m x)).comp (E.toBase m) := by
    refine ContinuousLinearMap.ext_on hd ?_
    rintro _ ⟨w, rfl⟩
    have := congrArg (fun T : E (m + 1) →L[ℝ] F 0 => T w) heq
    simp only [ContinuousLinearMap.comp_apply] at this ⊢
    rw [this]
    exact congrArg (Dl 0 (E.shift.toBase m x)) (E.shift_toBase m w).symm
  exact congrArg (fun T : E m →L[ℝ] F 0 => T v) h3

/-- **Proposition 1.16 (⇐)**: an sc⁰ map on an sc-domain satisfying the level conditions is sc¹,
with `Df(x) = Dl 0 x`. -/
theorem isSc1With (hU : IsScDomain E U) (hf : IsSc0 E F U f) (h : IsSc1Levels U f Dl) :
    IsSc1With U f (Dl 0) where
  isSc0 := hf
  hasFDerivWithinAt x hx := by
    have := h.hasFDerivWithinAt 0 x hx
    rwa [funext (levelMap_zero f)] at this
  tangent_isSc0 := by
    have hTf' : ∀ m, ∀ p ∈ E.tangent.lvlSet (E.tangentSet U) m,
        F.tangent.toBase m ((levelMap f (m + 1) p.1, Dl m p.1 p.2) : F.tangent m) =
          tangentMapWith f (Dl 0) (E.tangent.toBase m p) := by
      intro m p hp
      rw [ScBanach.mem_lvlSet_tangentSet] at hp
      rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase]
      change ((F.shift.toBase m (levelMap f (m + 1) p.1), F.toBase m (Dl m p.1 p.2)) :
        F.tangent 0) = (levelMap f 1 (E.shift.toBase m p.1), Dl 0 (E.shift.toBase m p.1) (E.toBase m p.2))
      refine Prod.ext ?_ (h.toBase_apply hU hf hp p.2)
      apply F.toBase_injective 1
      rw [← F.shift_toBase, hf.toBase_levelMap hp,
        hf.toBase_levelMap (E.mem_lvlSet_shift_toBase.2 hp), E.shift_toBase]
    refine ⟨fun m p hp => ⟨_, hTf' m p hp⟩, fun m => ?_⟩
    refine ContinuousOn.congr ?_ fun p hp => levelMap_eq_of_toBase_eq (hTf' m p hp)
    rw [ScBanach.lvlSet_tangentSet]
    refine ContinuousOn.prodMk ?_ ?_
    · exact (hf.continuousOn (m + 1)).comp continuousOn_fst fun p hp => hp.1
    · exact h.continuousOn m

end IsSc1Levels

/-- **Proposition 1.16 (⇒)**: the level operators of an sc¹ map on an sc-domain satisfy the level
conditions. -/
theorem IsSc1With.isSc1Levels (hU : IsScDomain E U) (h : IsSc1With U f D) :
    IsSc1Levels U f fun m => levelDeriv D m where
  hasFDerivWithinAt _ _ hx := h.hasFDerivWithinAt_level hU hx
  continuousOn m := h.continuousOn_levelDeriv m

/-- **Proposition 1.16**: an sc⁰ map `f : U → F` on an sc-domain `U` is sc¹ iff there are operators
`Dl m x ∈ L(E_m, F_m)` (`x ∈ U_{m+1}`) such that, for every `m`, `f : U_{m+1} → F_m` is
differentiable with derivative `Dl m x|_{E_{m+1}}` (hence `C¹`, with `df` continuous into
`L(E_{m+1}, F_m)`: `IsSc1Levels.contDiffOn`, `IsSc1Levels.continuousOn_clm`) and
`(x, h) ↦ Dl m x h` is continuous on `U_{m+1} × E_m`. -/
theorem proposition_1_16 (hU : IsScDomain E U) (hf : IsSc0 E F U f) :
    IsSc1 U f ↔ ∃ Dl : ∀ m, E (m + 1) → E m →L[ℝ] F m, IsSc1Levels U f Dl :=
  ⟨fun ⟨_, h⟩ => ⟨_, h.isSc1Levels hU⟩, fun ⟨_, h⟩ => ⟨_, h.isSc1With hU hf⟩⟩

/-! ### Proposition 1.17: lifting the index -/

/-- **Proposition 1.17 for sc¹**: if `f : U → F` is sc¹ with derivatives `Df` then `f : U¹ → F¹` is
sc¹ on `U¹ = U_1`, with derivatives the level-`1` operators `Df(x) : E_1 → F_1`, `x ∈ U_2`. -/
theorem IsSc1With.shift (hU : IsScDomain E U) (h : IsSc1With U f D) :
    IsSc1With (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) (levelDeriv D 1) where
  isSc0 := h.isSc0.shift
  hasFDerivWithinAt x hx := h.hasFDerivWithinAt_level hU (m := 1) hx
  tangent_isSc0 := by
    have := h.tangent_isSc0.shift
    rw [E.shift_tangentSet] at this
    refine this.congr fun p hp => ?_
    have hp' : p ∈ E.tangent.lvlSet (E.tangentSet U) 1 := by rw [E.shift_tangentSet]; exact hp
    rw [h.levelMap_tangentMapWith hp']
    change ((levelMap f 2 p.1, levelDeriv D 1 p.1 p.2) : F.tangent 1) =
      (levelMap (levelMap f 1) 1 p.1, levelDeriv D 1 p.1 p.2)
    rw [h.isSc0.levelMap_shift (E.mem_lvlSet_tangentSet.1 hp')]

/-- **Proposition 1.17**: if `f : U → F` is sc^k on an sc-domain `U` then `f : U¹ → F¹` is sc^k.
Induction on `k`: the tangent map of `f : U¹ → F¹` is the level-`1` map of `Tf`, on
`T(U¹) = (TU)¹`. -/
theorem IsSck.shift : ∀ {k : ℕ} {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0},
    IsScDomain E U → IsSck k E F U f → IsSck k E.shift F.shift (E.lvlSet U 1) (levelMap f 1)
  | 0, _, _, _, _, _, hf => IsSc0.shift hf
  | k + 1, E, F, U, f, hU, hf => by
    have h1 : IsSc1With (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1)
        (levelDeriv (scDeriv U f) 1) := hf.1.isSc1With_scDeriv.shift hU
    refine ⟨h1.isSc1, ?_⟩
    have := IsSck.shift (k := k) hU.tangentSet hf.2
    rw [E.shift_tangentSet] at this
    refine IsSck.congr hU.shift.tangentSet (fun p hp => ?_) this
    have hp' : p ∈ E.tangent.lvlSet (E.tangentSet U) 1 := by rw [E.shift_tangentSet]; exact hp
    simp only [tangentMap]
    rw [hf.1.isSc1With_scDeriv.levelMap_tangentMapWith hp']
    change ((levelMap f 2 p.1, levelDeriv (scDeriv U f) 1 p.1 p.2) : F.tangent 1) =
      ((levelMap (E := E.shift) (F := F.shift) (levelMap f 1) 1 p.1,
        scDeriv (E.lvlSet U 1) (levelMap f 1) p.1 p.2) : F.shift.tangent 0)
    rw [hf.1.isSc0.levelMap_shift (E.mem_lvlSet_tangentSet.1 hp'),
      IsSc1.scDeriv_eqOn h1 (hU.shift.uniqueDiffWithinAt 1) hp]

/-- **Proposition 1.17 for sc-smooth maps**: `f : U → F` sc-smooth ⇒ `f : U¹ → F¹` sc-smooth. -/
theorem IsScSmooth.shift (hU : IsScDomain E U) (hf : IsScSmooth U f) :
    IsScSmooth (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) :=
  fun k => (hf k).shift hU

/-! ### Proposition 1.18: sc^k maps are `C^k` from `U_{m+k}` to `F_m` -/

/-- **Proposition 1.18**, with a compatible level-lowering operator `ρ : E_n → E_m`, `n = m + k`, as
a parameter: if `f` is sc^k on an sc-domain `U` then `f_m ∘ ρ : U_n → F_m` is `C^k`.

Induction on `k` over all sc-domains.  For `k + 1`: `f : U_{m+k+1} → F_m` is differentiable with
derivative `x ↦ Df(x)|_{E_{m+k+1}}` (Proposition 1.16 on level `m`, restricted); by the induction
hypothesis for `Tf` the map `(x, h) ↦ Df(x)h` is `C^k` on `U_{m+k+1} × E_{m+k}`, so by the
compact-open lemma `x ↦ Df(x)|_{E_{m+k+1}}` is `C^k` into `L(E_{m+k+1}, F_m)`. -/
theorem IsSck.contDiffOn_levels' : ∀ {k : ℕ} {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0},
    IsScDomain E U → IsSck k E F U f → ∀ {m n : ℕ}, n = m + k → ∀ (ρ : E n →L[ℝ] E m),
      (∀ x, E.toBase m (ρ x) = E.toBase n x) → ContDiffOn ℝ k (levelMap f m ∘ ρ) (E.lvlSet U n)
  | 0, E, F, U, f, _, hf, m, n, hn, ρ, hρ => by
    subst n
    rw [Nat.cast_zero, contDiffOn_zero]
    have hρ' : ∀ x, ρ x = x := fun x => E.toBase_injective m (hρ x)
    exact (hf.continuousOn m).congr fun x _ => by rw [Function.comp_apply, hρ']
  | k + 1, E, F, U, f, hU, hf, m, n, hn, ρ, hρ => by
    subst hn
    have hD := hf.1.isSc1With_scDeriv
    -- `ρ = ι_m ∘ ρ'` with `ρ' : E_{m+k+1} → E_{m+1}`
    have hρ' : ∀ x, E.incl m (E.shift.inclK m k x) = ρ x := fun x =>
      E.toBase_injective m (by rw [E.incl_shift_inclK, E.toBase_inclK, hρ])
    -- the derivative of `f : U_{m+k+1} → F_m`
    have hder : ∀ x ∈ E.lvlSet U (m + (k + 1)), HasFDerivWithinAt (levelMap f m ∘ ρ)
        ((levelDeriv (scDeriv U f) m (E.shift.inclK m k x)).comp ρ) (E.lvlSet U (m + (k + 1))) x := by
      intro x hx
      have h1 := hD.hasFDerivWithinAt_level hU (E.shift_inclK_mem_lvlSet hx)
      have h2 := h1.comp x (E.shift.inclK m k).hasFDerivWithinAt
        fun y hy => E.shift_inclK_mem_lvlSet hy
      have e1 : (levelMap f m ∘ E.incl m) ∘ E.shift.inclK m k = levelMap f m ∘ ρ :=
        funext fun y => congrArg (levelMap f m) (hρ' y)
      have e2 : ((levelDeriv (scDeriv U f) m (E.shift.inclK m k x)).comp (E.incl m)).comp
          (E.shift.inclK m k) = (levelDeriv (scDeriv U f) m (E.shift.inclK m k x)).comp ρ :=
        ContinuousLinearMap.ext fun y => congrArg _ (hρ' y)
      rwa [e1, e2] at h2
    -- the derivative is `C^k`: induction hypothesis for `Tf` and the compact-open lemma
    have hT := IsSck.contDiffOn_levels' (k := k) hU.tangentSet hf.2 rfl (E.tangent.inclK m k)
      (E.tangent.toBase_inclK m k)
    rw [ScBanach.lvlSet_tangentSet] at hT
    unfold tangentMap at hT
    have hΦ : ContDiffOn ℝ k (fun p : E (m + k + 1) × E (m + k) =>
        levelDeriv (scDeriv U f) m (E.shift.inclK m k p.1) (E.inclK m k p.2))
        (E.lvlSet U (m + k + 1) ×ˢ univ) := by
      refine (contDiff_snd.comp_contDiffOn hT).congr fun p hp => ?_
      have hmem : ((E.shift.inclK m k p.1, E.inclK m k p.2) : E.tangent m) ∈
          E.tangent.lvlSet (E.tangentSet U) m := by
        rw [ScBanach.mem_lvlSet_tangentSet]; exact E.shift_inclK_mem_lvlSet hp.1
      rw [Function.comp_apply, Function.comp_apply, E.tangent_inclK,
        hD.levelMap_tangentMapWith hmem]
    have hA := contDiffOn_clm_comp_of_isCompactOperator (hU.relOpenConvex (m + k + 1))
      (hU.uniqueDiffWithinAt (m + k + 1)) (E.incl_isCompactOperator (m + k))
      (A := fun x => (levelDeriv (scDeriv U f) m (E.shift.inclK m k x)).comp (E.inclK m k)) hΦ
    rw [Nat.cast_succ,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (hU.uniqueDiffWithinAt (m + (k + 1)))]
    refine ⟨fun h0 => absurd h0 (by simp), _, ?_, hder⟩
    refine hA.congr fun x _ => ?_
    ext y
    exact congrArg (levelDeriv (scDeriv U f) m (E.shift.inclK m k x))
      ((hρ' y).symm.trans (E.incl_shift_inclK m k y))

/-- **Proposition 1.18**: if `f` is sc^k on an sc-domain `U` then `f : U_{m+k} → F_m` is `C^k` for
every `m`. -/
theorem IsSck.contDiffOn_levels {k : ℕ} (hU : IsScDomain E U) (hf : IsSck k E F U f) (m : ℕ) :
    ContDiffOn ℝ k (levelMap f m ∘ E.inclK m k) (E.lvlSet U (m + k)) :=
  hf.contDiffOn_levels' hU rfl (E.inclK m k) (E.toBase_inclK m k)

/-- **Proposition 1.18**, second part: if `f` is sc^k then `f : U_{m+l} → F_m` is `C^l` for
`0 ≤ l ≤ k`. -/
theorem IsSck.contDiffOn_levels_of_le {k l : ℕ} (hl : l ≤ k) (hU : IsScDomain E U)
    (hf : IsSck k E F U f) (m : ℕ) :
    ContDiffOn ℝ l (levelMap f m ∘ E.inclK m l) (E.lvlSet U (m + l)) :=
  (hf.of_le hl).contDiffOn_levels hU m

/-- **Proposition 1.18** on the base level: if `f` is sc^k then `f : U_k → F_0` is `C^k`. -/
theorem IsSck.contDiffOn_base {k : ℕ} (hU : IsScDomain E U) (hf : IsSck k E F U f) :
    ContDiffOn ℝ k (f ∘ E.toBase k) (E.lvlSet U k) := by
  have := hf.contDiffOn_levels' hU (Nat.zero_add k).symm (E.toBase k) fun _ => rfl
  rwa [funext (levelMap_zero f)] at this

/-- An sc-smooth map is `C^k` from `U_{m+k}` to `F_m` for all `m`, `k`. -/
theorem IsScSmooth.contDiffOn_levels (hU : IsScDomain E U) (hf : IsScSmooth U f) (m k : ℕ) :
    ContDiffOn ℝ k (levelMap f m ∘ E.inclK m k) (E.lvlSet U (m + k)) :=
  (hf k).contDiffOn_levels hU m

/-! ### Proposition 1.19 and Corollary 1.20 for all `k` -/

/-- **Proposition 1.19** (with the hypothesis "`f : U_m → F_m` is `C^{k+1}` for every `m`", see the
module docstring): an sc⁰ map on an sc-domain whose level maps are `C^{k+1}` is sc^{k+1}.
Induction on `k`: the level-`m` tangent map is `(x, h) ↦ (f(x), d f_m(x) h)` on `U_{m+1} × E_m`,
which is `C^k` when the `f_m` are `C^{k+1}`. -/
theorem proposition_1_19 : ∀ {k : ℕ} {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0},
    IsScDomain E U → IsSc0 E F U f → (∀ m, ContDiffOn ℝ (k + 1) (levelMap f m) (E.lvlSet U m)) →
      IsSck (k + 1) E F U f
  | 0, E, F, U, f, hU, hf, h => by
    have hD := proposition_1_19_zero hU hf fun m => by simpa using h m
    exact ⟨hD.isSc1, hD.isSc1.tangentMap_isSc0⟩
  | k + 1, E, F, U, f, hU, hf, h => by
    have h1 : ∀ m, ContDiffOn ℝ 1 (levelMap f m) (E.lvlSet U m) := fun m =>
      (h m).of_le (by norm_cast; omega)
    have hD := proposition_1_19_zero hU hf h1
    have hD' := hD.isSc1.isSc1With_scDeriv
    refine ⟨hD.isSc1, proposition_1_19 (k := k) hU.tangentSet hD.isSc1.tangentMap_isSc0 fun m => ?_⟩
    -- the level-`m` tangent map is `(x, h) ↦ (f(x), d f_m(x) h)`
    have hTf : ∀ p ∈ E.tangent.lvlSet (E.tangentSet U) m, levelMap (tangentMap U f) m p =
        ((levelMap f (m + 1) p.1, fderivWithin ℝ (levelMap f m) (E.lvlSet U m) (E.incl m p.1) p.2) :
          F.tangent m) := by
      intro p hp
      have hp1 : p.1 ∈ E.lvlSet U (m + 1) := E.mem_lvlSet_tangentSet.1 hp
      unfold tangentMap
      rw [hD'.levelMap_tangentMapWith hp, hD'.levelDeriv_eq hU hp1
        ((h1 m).differentiableOn one_ne_zero (E.incl m p.1) hp1).hasFDerivWithinAt]
    refine ContDiffOn.congr ?_ hTf
    rw [ScBanach.lvlSet_tangentSet]
    refine ContDiffOn.prodMk ?_ ?_
    · exact ((h (m + 1)).of_le (by norm_cast; omega)).comp
        (contDiffOn_fst (s := E.lvlSet U (m + 1) ×ˢ (univ : Set (E m)))) fun p hp => hp.1
    · have hd : ContDiffOn ℝ (k + 1) (fderivWithin ℝ (levelMap f m) (E.lvlSet U m))
          (E.lvlSet U m) := (h m).fderivWithin (hU.uniqueDiffWithinAt m) (by norm_cast)
      have hg : ContDiffOn ℝ (k + 1) (fun p : E (m + 1) × E m => E.incl m p.1)
          (E.lvlSet U (m + 1) ×ˢ univ) := ((E.incl m).contDiff.comp contDiff_fst).contDiffOn
      exact (hd.comp hg fun p hp => hp.1).clm_apply contDiffOn_snd

/-- **Corollary 1.20** (with the hypothesis "`f : U_m → ℝᴺ` is `C^{k+1}` for every `m`"): a map into
a finite-dimensional space (constant sc-structure) that is `C^{k+1}` on every level `U_m` is
sc^{k+1}. -/
theorem corollary_1_20 {k : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (hU : IsScDomain E U) {f : E 0 → (ScBanach.const V) 0}
    (h : ∀ m, ContDiffOn ℝ (k + 1) (f ∘ E.toBase m) (E.lvlSet U m)) :
    IsSck (k + 1) E (ScBanach.const V) U f := by
  have hlvl : ∀ m, levelMap f m = f ∘ E.toBase m := fun m => funext fun x =>
    levelMap_eq_of_toBase_eq (ScBanach.const_toBase V m _)
  have hf : IsSc0 E (ScBanach.const V) U f :=
    ⟨fun m x _ => ⟨f (E.toBase m x), ScBanach.const_toBase V m _⟩,
      fun m => by rw [hlvl]; exact (h m).continuousOn⟩
  exact proposition_1_19 hU hf fun m => by rw [hlvl]; exact h m

/-- **Corollary 1.20** from the base level: a map `f : U → ℝᴺ` of class `C^{k+1}` on `U = U_0` is
sc^{k+1} (its restrictions to the levels `U_m` are `C^{k+1}`). -/
theorem corollary_1_20_base {k : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (hU : IsScDomain E U) {f : E 0 → (ScBanach.const V) 0}
    (h : ContDiffOn ℝ (k + 1) f U) : IsSck (k + 1) E (ScBanach.const V) U f :=
  corollary_1_20 hU fun m => h.comp (E.toBase m).contDiff.contDiffOn (E.mapsTo_toBase_lvlSet U m)

lemma natCast_add_one_le_infty (k : ℕ) : ((k : WithTop ℕ∞) + 1) ≤ ∞ := by
  exact_mod_cast le_top

/-- **Sc-smoothness from classical smoothness on the levels** (Proposition 1.19 for all `k`): if
`f : U → F` maps every `U_m` into `F_m` and the induced maps `f : U_m → F_m` are `C^∞`, then `f` is
sc-smooth. -/
theorem IsScSmooth.of_contDiffOn_levels (hU : IsScDomain E U)
    (hmem : ∀ m, ∀ x ∈ E.lvlSet U m, f (E.toBase m x) ∈ range (F.toBase m))
    (h : ∀ m, ContDiffOn ℝ ∞ (levelMap f m) (E.lvlSet U m)) : IsScSmooth U f := by
  have hf : IsSc0 E F U f := ⟨hmem, fun m => (h m).continuousOn⟩
  intro k
  cases k with
  | zero => exact hf
  | succ k => exact proposition_1_19 hU hf fun m => (h m).of_le (natCast_add_one_le_infty k)

/-- **Corollary 1.20 for sc-smoothness**: a `C^∞` map `f : U → ℝᴺ` on an sc-domain `U` (into a
finite-dimensional space with its constant sc-structure) is sc-smooth. -/
theorem IsScSmooth.of_contDiffOn_finiteDimensional {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hU : IsScDomain E U)
    {f : E 0 → (ScBanach.const V) 0} (h : ContDiffOn ℝ ∞ f U) : IsScSmooth U f := by
  intro k
  cases k with
  | zero => exact (corollary_1_20_base (k := 0) hU (h.of_le (natCast_add_one_le_infty 0))).isSc0
  | succ k => exact corollary_1_20_base hU (h.of_le (natCast_add_one_le_infty k))

end Polyfold
