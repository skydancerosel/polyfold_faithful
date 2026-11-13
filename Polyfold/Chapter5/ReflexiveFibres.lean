import Polyfold.Chapter5.AuxNorm
import Polyfold.Chapter5.WeakSequentialCompactness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.1, pp. 207–208:
**Definition 5.1.4, Lemma 5.1.5, Definition 5.1.6, Definition 5.1.7, Proposition 5.1.8**
(2017: Definition 5.2, Lemma 5.2, Definition 5.3, Definition 5.4, Proposition 5.2).

# Reflexive `(0, 1)`-fibres, mixed convergence, reflexive auxiliary norms

## The text, paraphrased

(Definition 5.1.4) `P : Y → X` has reflexive `(0, 1)`-fibres if there is a strong bundle atlas whose
local models `K ⊆ C ◁ F` all have `F₁` reflexive.  (Lemma 5.1.5) For `y_k ∈ Y_{0,1}` with
`P(y_k) → x` on level 0 and two strong bundle charts `Ψ`, `Ψ'` around `x` with reflexive `F₁`,
`F'₁`, the fibre parts `h_k`, `h'_k` of `Ψ(y_k)`, `Ψ'(y_k)` converge weakly together.  Proof: the
transition is `(a, h) ↦ (φ(a), A(a, h))`; `h_k ⇀ h` in `F₁` gives `h_k → h` in `F₀`; the operators
`A(a_k, ·) : F₁ → F'₁` are uniformly bounded, so `(h'_k)` is bounded in `F'₁`, and it converges on
level 0; bounded plus level-0 convergence gives `h'_k ⇀ h'` in `F'₁`.  (Definition 5.1.6)
`y_k` is mixed convergent to `y ∈ Y_{0,1}` if `P(y_k) → P(y)` in `X₀` and, in some strong bundle
chart around `P(y)` with reflexive `F₁`, the fibre parts converge weakly in `F₁`.  (Definition
5.1.7) A reflexive auxiliary norm is a continuous `N : Y_{0,1} → [0, ∞)` which is a complete norm on
every fibre, satisfies condition (2) of Definition 5.1.1, and is lower semicontinuous along mixed
convergent sequences, `N(y) ≤ liminf N(y_k)`.  (Proposition 5.1.8, proof "left to the reader")
With reflexive `(0, 1)`-fibres a reflexive auxiliary norm exists, and for an auxiliary norm `N₀`
and a reflexive auxiliary norm `N₁` there is a continuous `f : X → (0, ∞)` with
`f(x)·N₀ ≤ N₁ ≤ (1/f(x))·N₀` on the fibre over `x`.

## What is formalized

* `StrongBundleChart.liftOneSnd` (the fibre part `h ∈ F₁` of `Φ[1](y)`),
  `StrongBundleChart.mem_K_of_tendsto` (`K` is closed along sequences whose base limit lies in `O`).
* `StrongBundle.HasReflexiveFibers` (**Definition 5.1.4**), `hasReflexiveFibers_of_atlas`.
* `StrongBundle.exists_limit_of_weakTendsto` (a weak limit of fibre parts in one chart is the
  fibre part of a point `y ∈ Y_{0,1}` over the limit, and `y_k → y` in `Y`),
  `StrongBundle.weakTendsto_transfer` (the transfer to a second chart), **`Polyfold.lemma_5_1_5`**
  and its strong form `Polyfold.lemma_5_1_5_limit` (the two weak limits are the parts of one point).
* `StrongBundle.MixedTendsto` (**Definition 5.1.6**), `MixedTendsto.weakTendsto_of_isChart`
  (**chart independence**: the weak convergence holds in every chart around `P(y)` with reflexive
  `F₁`), `MixedTendsto.tendsto_oneVal` (mixed convergence implies convergence in `Y`),
  `StrongBundle.exists_mixedTendsto_subseq` (a sequence with `P(y_k) → x` and `N(y_k)` bounded for
  an auxiliary norm has a mixed convergent subsequence; this is the step of Proposition 5.2.7).
* `StrongBundle.IsReflexiveAuxNorm` (**Definition 5.1.7**; `liminf` in `EReal`),
  `IsReflexiveAuxNorm.le_of_frequently_le`, `le_liminf_coe_of_eventually`.
* **Proposition 5.1.8**: `Polyfold.proposition_5_1_8_exists` (the glued norm
  `Σᵢ ρᵢ(P(w))·|Φᵢ[1](w)|₁` over the reflexive charts is a reflexive auxiliary norm:
  `isReflexiveAuxNorm_gluedNorm`), `Polyfold.proposition_5_1_8_compare`,
  `Polyfold.proposition_5_1_8`.
* For Part III (the M-polyfold forms of Remark 12.2.12 (1) and of the last clause of Theorem
  12.2.11): `IsAuxNorm.comp_mul`, `IsReflexiveAuxNorm.comp_mul` (`(g ∘ P)·N` for continuous
  `g > 0`), `IsReflexiveAuxNorm.eventually_sub_lt`, `exists_reflexiveAuxNorm_sandwich`
  (`N₁ ≤ N' ≤ N₂` with `N₁`, `N₂` reflexive).
* Satisfiability (in `ReflexiveCompactness.lean`): `TrivialBundle.hasReflexiveFibers_bundle`
  (`ℝⁿ × ℝᵏ → ℝⁿ`) and `TrivialBundle.exists_isReflexiveAuxNorm_bundle`.

## What the text leaves implicit, and the choices made

* **Definition 5.1.4** is read as: every point of `X` lies in the domain of a strong bundle chart
  compatible with the atlas (`B.IsChart`) whose `F₁` is reflexive.  These charts cover `Y`; the
  text's "there exists a strong bundle atlas" asks for such a cover by charts of an equivalent
  atlas.
  `hasReflexiveFibers_of_atlas`: it holds when every chart of the given atlas has reflexive `F₁`.
* `IsReflexive F` is the surjectivity of the canonical map into the bidual (`WeakSequentialCompactness`).
* **Lemma 5.1.5** holds in the stronger form `lemma_5_1_5_limit`: for every pair of compatible
  charts around `x` with reflexive `F₁`, `F'₁` and every weak limit `h` in the first, there is one
  `y ∈ Y_{0,1}` over `x` with fibre parts `h` and `h'`, and `h'_k ⇀ h'`.  Only `F'₁` reflexive is
  used for the direction `Ψ ⇒ Ψ'`.  The text's step "`(a, h)` lies in `K`" (needed to form
  `Φ(a, h)`) is `mem_K_of_tendsto` (the retraction `R` is continuous on `U ◁ F` and fixes `K`); the
  uniform bound of `A(a_k, ·)` is the local comparison of the norms `|·|₁` of two charts
  (`exists_norm_liftOne_le_mul`, from Lemma 5.1.2's argument).
* **Definition 5.1.6** asks for one chart; `MixedTendsto.weakTendsto_of_isChart` gives all charts
  (the text's "in view of this lemma we can define").  The convergence `P(y_k) → P(y)` is in `X`
  (level 0).  The fibre parts of `y_k` are read in the chart only for large `k` (where `P(y_k)` lies
  in its domain); weak convergence only depends on the tail.
* **Definition 5.1.7 (3)** is printed with `liminf_{k → 0}`; we read `k → ∞`.  The `liminf` is
  taken in `EReal` (so that an unbounded sequence has `liminf = ∞`); equivalently
  (`IsReflexiveAuxNorm.le_of_frequently_le`, `le_liminf_coe_of_eventually`): `N(y) ≤ r` whenever
  `N(y_k) ≤ r` for infinitely many `k`.
* **Proposition 5.1.8** (no proof in the text).  Existence: a partition of unity on the paracompact
  `X` subordinate to the domains of the reflexive charts, and the glued norm of the proof of
  Proposition 5.1.3 over these charts.  It is an auxiliary norm by Lemma 5.1.2 as in Proposition
  5.1.3; lower semicontinuity along mixed convergent sequences holds because near `P(y)` only
  finitely many terms are nonzero, `ρᵢ(P(y_k)) → ρᵢ(P(y))`, and in each chart the fibre parts
  converge weakly (chart independence), so `‖hᵢ‖ ≤ liminf ‖hᵢ(k)‖` (weak lower semicontinuity of
  the norm, `WeakTendsto.eventually_norm_gt`).  Comparison: a reflexive auxiliary norm is an
  auxiliary norm, and Proposition 5.1.3 applies.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundleChart

variable (c : StrongBundleChart PX P)

/-- The fibre part `h ∈ F₁` of `Φ[1](y) = (a, h)` (meaningful for `y ∈ Y_{0,1}` in the domain). -/
def liftOneSnd (y : Y) : c.F 1 := (c.liftOne y).2

omit [T2Space Y] [ParacompactSpace Y] in
lemma liftOneSnd_def (y : Y) : c.liftOneSnd y = (c.liftOne y).2 := rfl

omit [T2Space Y] [ParacompactSpace Y] in
/-- **`K` is closed along sequences with base limit in `O`**: if `p_k ∈ K` eventually and
`p_k → q` with `q.1 ∈ O`, then `q ∈ K` (the retraction `R` is continuous on `U ◁ F` and fixes `K`).
This is the step "`Φ(a, h)` is defined" of the proof of Lemma 5.1.5. -/
lemma mem_K_of_tendsto {p : ℕ → c.φ.model.E 0 × c.F 0} {q : c.φ.model.E 0 × c.F 0}
    (hp : ∀ᶠ k in atTop, p k ∈ c.K) (hq : Tendsto p atTop (𝓝 q)) (hq1 : q.1 ∈ c.φ.model.O) :
    q ∈ c.K := by
  set R := c.isRetraction.toScRetraction c.relOpen with hRdef
  have hret : R.retract = c.K := rfl
  have hqU : q ∈ R.U := by
    refine ⟨(c.isRetraction.baseRetraction c.relOpen).retract_subset ?_, mem_univ _⟩
    rw [c.base_retract]; exact hq1
  have hcont : ContinuousWithinAt R R.U q := R.isSc1.isSc0.continuousOn_base q hqU
  have hmemU : ∀ᶠ k in atTop, p k ∈ R.U :=
    hp.mono fun k hk => R.retract_subset (by rw [hret]; exact hk)
  have h1 : Tendsto (fun k => R (p k)) atTop (𝓝 (R q)) :=
    hcont.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hq, hmemU⟩)
  have h2 : Tendsto (fun k => R (p k)) atTop (𝓝 q) :=
    hq.congr' (hp.mono fun k hk =>
      (R.apply_eq_self_of_mem_retract (by rw [hret]; exact hk)).symm)
  have hfix : R q = q := tendsto_nhds_unique h1 h2
  rw [← hret]
  exact R.mem_retract_iff.2 ⟨hqU, hfix⟩

end StrongBundleChart

namespace StrongBundle

variable {B : StrongBundle PX P}

/-! ### Definition 5.1.4 -/

variable (B) in
/-- **2021 Definition 5.1.4, p. 207** (2017: Definition 5.2): `P : Y → X` has **reflexive
`(0, 1)`-fibres**: every point of `X` lies in the domain of a strong bundle chart (compatible with
the atlas) whose local model `K ⊆ C ◁ F` has `F₁` reflexive. -/
def HasReflexiveFibers : Prop :=
  ∀ x : X, ∃ c : StrongBundleChart PX P, B.IsChart c ∧ x ∈ c.φ.source ∧ IsReflexive (c.F 1)

/-- If every chart of the atlas has reflexive `F₁`, the bundle has reflexive `(0, 1)`-fibres. -/
theorem hasReflexiveFibers_of_atlas (h : ∀ c ∈ B.atlas.charts, IsReflexive (c.F 1)) :
    B.HasReflexiveFibers := fun x => by
  obtain ⟨c, hc, hx⟩ := exists_chart_mem B x
  exact ⟨c, B.isChart_of_mem hc, hx, h c hc⟩

/-! ### Lemma 5.1.5 -/

section Lemma515

variable {c c' : StrongBundleChart PX P}

lemma apply_eq_liftOneSnd (hc : B.IsChart c) {y : Y} (hy : P y ∈ c.φ.source)
    (h1 : y ∈ B.oneSet) : c y = (c.φ (P y), c.F.toBase 1 (c.liftOneSnd y)) := by
  have hs := c.mem_source_of_proj hy
  rw [← c.toBase_liftOne ((mem_oneSet_iff_of_isChart hc hs).1 h1)]
  exact Prod.ext (fst_liftOne hy) rfl

/-- Two points of `Y_{0,1}` in one fibre with the same fibre part in a chart are equal. -/
lemma eq_of_liftOneSnd_eq (hc : B.IsChart c) {y y' : B.One}
    (hP : P (B.oneVal y) = P (B.oneVal y')) (hx : P (B.oneVal y) ∈ c.φ.source)
    (hh : c.liftOneSnd (B.oneVal y) = c.liftOneSnd (B.oneVal y')) : y = y' := by
  apply B.oneVal_injective
  have hx' : P (B.oneVal y') ∈ c.φ.source := hP ▸ hx
  refine c.toPartialEquiv.injOn (c.mem_source_of_proj hx) (c.mem_source_of_proj hx') ?_
  rw [apply_eq_liftOneSnd hc hx (B.oneVal_mem y), apply_eq_liftOneSnd hc hx' (B.oneVal_mem y'),
    hP, hh]

lemma isCompactOperator_toBase_one (F : ScBanach) : IsCompactOperator (F.toBase 1) :=
  (F.incl_isCompactOperator 0).clm_comp (F.toBase 0)

/-- **A weak limit of the fibre parts in one chart is the fibre part of a point of `Y_{0,1}`**:
if `P(y_k) → x` and `h_k ⇀ h` in `F₁` (`h_k` the fibre part of `Φ[1](y_k)`), then there is
`y ∈ Y_{0,1}` over `x` with fibre part `h`, and `y_k → y` in `Y` (on level 0).  The text: "`h_k ⇀ h`
in `F₁` implies `h_k → h` in `F₀`", with `(a, h) ∈ K`. -/
theorem exists_limit_of_weakTendsto (hc : B.IsChart c) {w : ℕ → B.One} {x : X}
    (hx : x ∈ c.φ.source) (hP : Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 x)) {h : c.F 1}
    (hh : WeakTendsto (fun k => c.liftOneSnd (B.oneVal (w k))) h) :
    ∃ y : B.One, P (B.oneVal y) = x ∧ c.liftOneSnd (B.oneVal y) = h ∧
      Tendsto (fun k => B.oneVal (w k)) atTop (𝓝 (B.oneVal y)) := by
  have hev : ∀ᶠ k in atTop, P (B.oneVal (w k)) ∈ c.φ.source :=
    hP.eventually (c.φ.isOpen_source.mem_nhds hx)
  have hsrc : ∀ᶠ k in atTop, B.oneVal (w k) ∈ c.toPartialEquiv.source :=
    hev.mono fun k hk => c.mem_source_of_proj hk
  have hcw : ∀ᶠ k in atTop, c (B.oneVal (w k)) =
      (c.φ (P (B.oneVal (w k))), c.F.toBase 1 (c.liftOneSnd (B.oneVal (w k)))) :=
    hev.mono fun k hk => apply_eq_liftOneSnd hc hk (B.oneVal_mem _)
  have hφ : Tendsto (fun k => c.φ (P (B.oneVal (w k)))) atTop (𝓝 (c.φ x)) :=
    (c.φ.continuousOn_toFun.continuousAt (c.φ.isOpen_source.mem_nhds hx)).tendsto.comp hP
  have hb : Tendsto (fun k => c.F.toBase 1 (c.liftOneSnd (B.oneVal (w k)))) atTop
      (𝓝 (c.F.toBase 1 h)) := hh.tendsto_of_isCompactOperator (isCompactOperator_toBase_one c.F)
  set q : c.φ.model.E 0 × c.F 0 := (c.φ x, c.F.toBase 1 h) with hqdef
  have hcq : Tendsto (fun k => c (B.oneVal (w k))) atTop (𝓝 q) :=
    (hφ.prodMk_nhds hb).congr' (hcw.mono fun k hk => hk.symm)
  have hK : ∀ᶠ k in atTop, c (B.oneVal (w k)) ∈ c.K :=
    hsrc.mono fun k hk => by rw [← c.image_source]; exact ⟨_, hk, rfl⟩
  have hqK : q ∈ c.K := c.mem_K_of_tendsto hK hcq (c.φ.mapsTo_model x hx)
  have hqt : q ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hqK
  set y₀ := c.toPartialEquiv.symm q with hy₀
  have hy₀s : y₀ ∈ c.toPartialEquiv.source := c.toPartialEquiv.map_target hqt
  have hcy₀ : c y₀ = q := c.toPartialEquiv.right_inv hqt
  have hPy₀ : P y₀ = x := by
    have hPys : P y₀ ∈ c.φ.source := by rw [c.source_eq] at hy₀s; exact hy₀s
    have h1 := c.covers y₀ hy₀s
    change (c y₀).1 = c.φ (P y₀) at h1
    rw [hcy₀] at h1
    exact c.φ.toPartialEquiv.injOn hPys hx h1.symm
  have hy₀1 : y₀ ∈ B.oneSet :=
    (mem_oneSet_iff_of_isChart hc hy₀s).2 (by rw [hcy₀]; exact ⟨h, rfl⟩)
  refine ⟨B.oneMk y₀ hy₀1, hPy₀, ?_, ?_⟩
  · change Function.invFun (c.F.toBase 1) (c y₀).2 = h
    rw [hcy₀]
    exact Function.leftInverse_invFun (c.F.toBase_injective 1) h
  · have hKt : ∀ᶠ k in atTop, c (B.oneVal (w k)) ∈ c.toPartialEquiv.target :=
      hK.mono fun k hk => by rw [c.target_eq]; exact hk
    have h4 := (c.continuousOn_invFun q hqt).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hcq, hKt⟩)
    exact h4.congr' (hsrc.mono fun k hk => c.toPartialEquiv.left_inv hk)

/-- **Weak convergence in a second chart** (the second half of the proof of Lemma 5.1.5): if
`y_k → y` in `Y`, `P(y)` lies in the domain of `Ψ'` with `F'₁` reflexive, and the fibre parts
`h'_k` are eventually bounded in `F'₁`, then `h'_k ⇀ h'(y)` in `F'₁`. -/
theorem weakTendsto_liftOneSnd_of_tendsto (hc' : B.IsChart c') (hF' : IsReflexive (c'.F 1))
    {w : ℕ → B.One} {y : B.One} (hx' : P (B.oneVal y) ∈ c'.φ.source)
    (hY : Tendsto (fun k => B.oneVal (w k)) atTop (𝓝 (B.oneVal y))) {C : ℝ}
    (hbd : ∀ᶠ k in atTop, ‖c'.liftOneSnd (B.oneVal (w k))‖ ≤ C) :
    WeakTendsto (fun k => c'.liftOneSnd (B.oneVal (w k))) (c'.liftOneSnd (B.oneVal y)) := by
  have hys : B.oneVal y ∈ c'.toPartialEquiv.source := c'.mem_source_of_proj hx'
  have hso : IsOpen c'.toPartialEquiv.source := c'.isOpen_source B.continuous
  have hsrc : ∀ᶠ k in atTop, B.oneVal (w k) ∈ c'.toPartialEquiv.source :=
    hY.eventually (hso.mem_nhds hys)
  have h1 : Tendsto (fun k => c' (B.oneVal (w k))) atTop (𝓝 (c' (B.oneVal y))) :=
    (c'.continuousOn_toFun.continuousAt (hso.mem_nhds hys)).tendsto.comp hY
  have h2 : Tendsto (fun k => c'.F.toBase 1 (c'.liftOneSnd (B.oneVal (w k)))) atTop
      (𝓝 (c'.F.toBase 1 (c'.liftOneSnd (B.oneVal y)))) := by
    have e : c'.F.toBase 1 (c'.liftOneSnd (B.oneVal y)) = (c' (B.oneVal y)).2 :=
      toBase_liftOne_snd hc' hys (B.oneVal_mem y)
    rw [e]
    exact (continuous_snd.tendsto _ |>.comp h1).congr' (hsrc.mono fun k hk =>
      (toBase_liftOne_snd hc' hk (B.oneVal_mem _)).symm)
  exact weakTendsto_of_bounded_of_tendsto hF' (c'.F.toBase_injective 1) hbd h2

/-- **The transfer of weak convergence from one chart to another** (Lemma 5.1.5, direction
`Ψ ⇒ Ψ'`, with the identification of the limits). -/
theorem weakTendsto_transfer (hc : B.IsChart c) (hc' : B.IsChart c') (hF' : IsReflexive (c'.F 1))
    {w : ℕ → B.One} {x : X} (hx : x ∈ c.φ.source) (hx' : x ∈ c'.φ.source)
    (hP : Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 x)) {h : c.F 1}
    (hh : WeakTendsto (fun k => c.liftOneSnd (B.oneVal (w k))) h) :
    ∃ y : B.One, P (B.oneVal y) = x ∧ c.liftOneSnd (B.oneVal y) = h ∧
      Tendsto (fun k => B.oneVal (w k)) atTop (𝓝 (B.oneVal y)) ∧
      WeakTendsto (fun k => c'.liftOneSnd (B.oneVal (w k))) (c'.liftOneSnd (B.oneVal y)) := by
  obtain ⟨y, hPy, hhy, hY⟩ := exists_limit_of_weakTendsto hc hx hP hh
  refine ⟨y, hPy, hhy, hY, ?_⟩
  obtain ⟨C, -, hC⟩ := hh.exists_bound
  obtain ⟨V, hVo, hxV, -, D, hD, hV⟩ := exists_norm_liftOne_le_mul hc' hc hx' hx
  have hev : ∀ᶠ k in atTop, P (B.oneVal (w k)) ∈ V := hP.eventually (hVo.mem_nhds hxV)
  refine weakTendsto_liftOneSnd_of_tendsto hc' hF' (hPy ▸ hx') hY (C := D * C)
    (hev.mono fun k hk => ?_)
  exact (hV (w k) hk).trans (mul_le_mul_of_nonneg_left (hC k) hD.le)

end Lemma515

end StrongBundle

open StrongBundle in
/-- **2021 Lemma 5.1.5, p. 207** (2017: Lemma 5.2): for `y_k ∈ Y_{0,1}` with `P(y_k) → x` and two
strong bundle charts `Ψ`, `Ψ'` around `x` with `F₁`, `F'₁` reflexive, the fibre parts `h_k` of
`Ψ[1](y_k)` converge weakly in `F₁` if and only if the fibre parts `h'_k` of `Ψ'[1](y_k)` converge
weakly in `F'₁`. -/
theorem lemma_5_1_5 {B : StrongBundle PX P} {c c' : StrongBundleChart PX P} (hc : B.IsChart c)
    (hc' : B.IsChart c') (hF : IsReflexive (c.F 1)) (hF' : IsReflexive (c'.F 1)) {w : ℕ → B.One}
    {x : X} (hx : x ∈ c.φ.source) (hx' : x ∈ c'.φ.source)
    (hP : Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 x)) :
    (∃ h, WeakTendsto (fun k => c.liftOneSnd (B.oneVal (w k))) h) ↔
      ∃ h', WeakTendsto (fun k => c'.liftOneSnd (B.oneVal (w k))) h' := by
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨y, -, -, -, hy⟩ := weakTendsto_transfer hc hc' hF' hx hx' hP hh
    exact ⟨_, hy⟩
  · rintro ⟨h', hh'⟩
    obtain ⟨y, -, -, -, hy⟩ := weakTendsto_transfer hc' hc hF hx' hx hP hh'
    exact ⟨_, hy⟩

open StrongBundle in
/-- **Lemma 5.1.5, strong form**: the weak limits in the two charts are the fibre parts of one point
`y ∈ Y_{0,1}` over `x`, and `y_k → y` in `Y`.  Only `F'₁` needs to be reflexive. -/
theorem lemma_5_1_5_limit {B : StrongBundle PX P} {c c' : StrongBundleChart PX P}
    (hc : B.IsChart c) (hc' : B.IsChart c') (hF' : IsReflexive (c'.F 1)) {w : ℕ → B.One} {x : X}
    (hx : x ∈ c.φ.source) (hx' : x ∈ c'.φ.source)
    (hP : Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 x)) {h : c.F 1}
    (hh : WeakTendsto (fun k => c.liftOneSnd (B.oneVal (w k))) h) :
    ∃ y : B.One, P (B.oneVal y) = x ∧ c.liftOneSnd (B.oneVal y) = h ∧
      Tendsto (fun k => B.oneVal (w k)) atTop (𝓝 (B.oneVal y)) ∧
      WeakTendsto (fun k => c'.liftOneSnd (B.oneVal (w k))) (c'.liftOneSnd (B.oneVal y)) :=
  weakTendsto_transfer hc hc' hF' hx hx' hP hh

namespace StrongBundle

variable {B : StrongBundle PX P}

/-! ### Definition 5.1.6 -/

variable (B) in
/-- **2021 Definition 5.1.6, p. 207** (2017: Definition 5.3; mixed convergence): `y_k ∈ Y_{0,1}`
is **mixed convergent** to `y ∈ Y_{0,1}` (`y_k →ᵐ y`) if `P(y_k) → P(y)` in `X` (level 0) and in
some strong bundle chart `Ψ` around `P(y)` with `F₁` reflexive the fibre parts converge weakly,
`h_k ⇀ h` in `F₁`, where `Ψ[1](y_k) = (a_k, h_k)` and `Ψ[1](y) = (a, h)`. -/
def MixedTendsto (w : ℕ → B.One) (y : B.One) : Prop :=
  Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 (P (B.oneVal y))) ∧
    ∃ c : StrongBundleChart PX P, B.IsChart c ∧ P (B.oneVal y) ∈ c.φ.source ∧
      IsReflexive (c.F 1) ∧
      WeakTendsto (fun k => c.liftOneSnd (B.oneVal (w k))) (c.liftOneSnd (B.oneVal y))

/-- **Chart independence of mixed convergence** (after Lemma 5.1.5): the weak convergence holds in
every strong bundle chart around `P(y)` with reflexive `F₁`. -/
theorem MixedTendsto.weakTendsto_of_isChart {w : ℕ → B.One} {y : B.One} (hm : B.MixedTendsto w y)
    {c' : StrongBundleChart PX P} (hc' : B.IsChart c') (hx' : P (B.oneVal y) ∈ c'.φ.source)
    (hF' : IsReflexive (c'.F 1)) :
    WeakTendsto (fun k => c'.liftOneSnd (B.oneVal (w k))) (c'.liftOneSnd (B.oneVal y)) := by
  obtain ⟨hP, c, hc, hx, -, hh⟩ := hm
  obtain ⟨y', hPy', hhy', -, hy'⟩ := weakTendsto_transfer hc hc' hF' hx hx' hP hh
  have hyy : y' = y := eq_of_liftOneSnd_eq hc hPy' (hPy' ▸ hx) hhy'
  rwa [hyy] at hy'

/-- **Mixed convergence implies convergence in `Y`** (on level 0; the text: "moreover `h_k → h` in
`Y_{0,0}`", proof of Proposition 5.2.7). -/
theorem MixedTendsto.tendsto_oneVal {w : ℕ → B.One} {y : B.One} (hm : B.MixedTendsto w y) :
    Tendsto (fun k => B.oneVal (w k)) atTop (𝓝 (B.oneVal y)) := by
  obtain ⟨hP, c, hc, hx, -, hh⟩ := hm
  obtain ⟨y', hPy', hhy', hY⟩ := exists_limit_of_weakTendsto hc hx hP hh
  have hyy : y' = y := eq_of_liftOneSnd_eq hc hPy' (hPy' ▸ hx) hhy'
  rwa [hyy] at hY

/-- Mixed convergence passes to subsequences. -/
theorem MixedTendsto.comp_strictMono {w : ℕ → B.One} {y : B.One} (hm : B.MixedTendsto w y)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : B.MixedTendsto (w ∘ φ) y := by
  obtain ⟨hP, c, hc, hx, hF, hh⟩ := hm
  exact ⟨hP.comp hφ.tendsto_atTop, c, hc, hx, hF, hh.comp_strictMono hφ⟩

/-- **Mixed convergent subsequences** (the step "we may assume after perhaps taking a subsequence
that `h_k →ᵐ h`" of the proof of Proposition 5.2.7): with reflexive `(0, 1)`-fibres, a sequence
`y_k ∈ Y_{0,1}` with `P(y_k) → x` and `N(y_k) ≤ r` eventually, for an auxiliary norm `N`, has a
subsequence mixed convergent to some `y ∈ Y_{0,1}` over `x`. -/
theorem exists_mixedTendsto_subseq (hB : B.HasReflexiveFibers) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) {w : ℕ → B.One} {x : X}
    (hP : Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 x)) {r : ℝ}
    (hr : ∀ᶠ k in atTop, N (w k) ≤ r) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : B.One, P (B.oneVal y) = x ∧ B.MixedTendsto (w ∘ φ) y := by
  obtain ⟨c, hc, hx, hF⟩ := hB x
  obtain ⟨V, hVo, hxV, -, a, A, ha, haA, hV⟩ := hN.exists_bounds hc hx
  have hev : ∀ᶠ k in atTop, P (B.oneVal (w k)) ∈ V := hP.eventually (hVo.mem_nhds hxV)
  have hbd : ∀ᶠ k in atTop, ‖c.liftOneSnd (B.oneVal (w k))‖ ≤ A * r :=
    (hev.and hr).mono fun k hk =>
      (hV (w k) hk.1).2.trans (mul_le_mul_of_nonneg_left hk.2 (ha.trans haA).le)
  obtain ⟨h, φ, hφ, hh⟩ := exists_subseq_weakTendsto_of_eventually hF hbd
  have hPφ := hP.comp hφ.tendsto_atTop
  obtain ⟨y, hPy, hhy, -⟩ := exists_limit_of_weakTendsto hc hx hPφ hh
  refine ⟨φ, hφ, y, hPy, ?_, c, hc, hPy ▸ hx, hF, ?_⟩
  · rw [hPy]; exact hPφ
  · rw [hhy]; exact hh

/-! ### Definition 5.1.7 -/

variable (B) in
/-- **2021 Definition 5.1.7, p. 208** (2017: Definition 5.4): a **reflexive auxiliary norm** for a
strong bundle with reflexive `(0, 1)`-fibres is an auxiliary norm `N : Y_{0,1} → ℝ` (continuous, a
complete norm on every fibre, condition (2) of Definition 5.1.1) which is lower semicontinuous along
mixed convergent sequences: `y_k →ᵐ y` implies `N(y) ≤ liminf N(y_k)` (printed `k → 0`; the
`liminf` taken in `EReal`). -/
structure IsReflexiveAuxNorm (N : B.One → ℝ) : Prop extends B.IsAuxNorm N where
  le_liminf : ∀ (w : ℕ → B.One) (y : B.One), B.MixedTendsto w y →
    (N y : EReal) ≤ liminf (fun k => (N (w k) : EReal)) atTop

/-- The `liminf` clause in the form used in the proofs: if `N(y_k) ≤ r` for infinitely many `k`
and `y_k →ᵐ y`, then `N(y) ≤ r`. -/
theorem IsReflexiveAuxNorm.le_of_frequently_le {N : B.One → ℝ} (hN : B.IsReflexiveAuxNorm N)
    {w : ℕ → B.One} {y : B.One} (hm : B.MixedTendsto w y) {r : ℝ}
    (hr : ∃ᶠ k in atTop, N (w k) ≤ r) : N y ≤ r := by
  have h1 := hN.le_liminf w y hm
  have h2 : liminf (fun k => (N (w k) : EReal)) atTop ≤ (r : EReal) :=
    liminf_le_of_frequently_le' (hr.mono fun k hk => EReal.coe_le_coe_iff.2 hk)
  exact EReal.coe_le_coe_iff.1 (h1.trans h2)

/-- A criterion for the `liminf` clause: `a - ε < u_k` eventually, for every `ε > 0`. -/
theorem le_liminf_coe_of_eventually {u : ℕ → ℝ} {a : ℝ}
    (h : ∀ ε > 0, ∀ᶠ k in atTop, a - ε < u k) :
    (a : EReal) ≤ liminf (fun k => (u k : EReal)) atTop := by
  refine le_of_forall_lt fun b hb => ?_
  induction b using EReal.rec with
  | bot => exact lt_of_lt_of_le (EReal.bot_lt_coe (a - 1)) (le_liminf_of_le (by isBoundedDefault)
      ((h 1 one_pos).mono fun k hk => EReal.coe_le_coe_iff.2 hk.le))
  | top => exact absurd hb (not_lt.2 le_top)
  | coe b =>
    have hb' : b < a := EReal.coe_lt_coe_iff.1 hb
    obtain ⟨m, hbm, hma⟩ := exists_between hb'
    refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hbm) (le_liminf_of_le (by isBoundedDefault) ?_)
    filter_upwards [h (a - m) (sub_pos.2 hma)] with k hk
    exact EReal.coe_le_coe_iff.2 (by linarith)

/-! ### Proposition 5.1.8 -/

section Prop518

variable {ι : Type*} {c : ι → StrongBundleChart PX P} {ρ : PartitionOfUnity ι X univ}

lemma mul_sub_le_of_sub_lt {a b a' b' δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a')
    (hb' : 0 ≤ b') (hδ : 0 < δ) (h1 : a - δ < a') (h2 : b - δ < b') :
    a * b - δ * (a + b) ≤ a' * b' := by
  rcases le_or_gt a δ with had | had <;> rcases le_or_gt b δ with hbd | hbd
  · nlinarith [mul_nonneg ha' hb']
  · nlinarith [mul_nonneg ha' hb']
  · nlinarith [mul_nonneg ha' hb']
  · have e1 : 0 < a - δ := by linarith
    have e2 : 0 < b - δ := by linarith
    nlinarith [mul_le_mul h1.le h2.le e2.le ha']

/-- **The glued norm over charts with reflexive `F₁` is lower semicontinuous along mixed convergent
sequences** (the clause (3) of Definition 5.1.7 in Proposition 5.1.8). -/
theorem le_liminf_gluedNorm (hc : ∀ i, B.IsChart (c i)) (hF : ∀ i, IsReflexive ((c i).F 1))
    (hρ : ρ.IsSubordinate fun i => (c i).φ.source) {w : ℕ → B.One} {y : B.One}
    (hm : B.MixedTendsto w y) :
    (gluedNorm B c ρ y : EReal) ≤ liminf (fun k => (gluedNorm B c ρ (w k) : EReal)) atTop := by
  classical
  set x := P (B.oneVal y) with hxdef
  obtain ⟨is, n, hn, hnsub, hsupp⟩ :=
    ρ.locallyFinite.exists_finset_nhds_support_subset hρ (fun i => (c i).φ.isOpen_source) x
  have hxis : ∀ i ∈ is, x ∈ (c i).φ.source := fun i hi =>
    mem_iInter₂.1 (hnsub (mem_of_mem_nhds hn)) i hi
  have hxn : x ∈ n := mem_of_mem_nhds hn
  have hNy : gluedNorm B c ρ y =
      ∑ i ∈ is, ρ i x * ‖(c i).liftOneSnd (B.oneVal y)‖ := gluedNorm_eq_sum (hsupp x hxn)
  have hev : ∀ᶠ k in atTop, P (B.oneVal (w k)) ∈ n := hm.1.eventually hn
  have hNw : ∀ᶠ k in atTop, gluedNorm B c ρ (w k) =
      ∑ i ∈ is, ρ i (P (B.oneVal (w k))) * ‖(c i).liftOneSnd (B.oneVal (w k))‖ :=
    hev.mono fun k hk => gluedNorm_eq_sum (hsupp _ hk)
  have hweak : ∀ i ∈ is, WeakTendsto (fun k => (c i).liftOneSnd (B.oneVal (w k)))
      ((c i).liftOneSnd (B.oneVal y)) := fun i hi =>
    hm.weakTendsto_of_isChart (hc i) (hxis i hi) (hF i)
  have hρc : ∀ i, Tendsto (fun k => ρ i (P (B.oneVal (w k)))) atTop (𝓝 (ρ i x)) := fun i =>
    ((ρ i).continuous.tendsto x).comp hm.1
  refine le_liminf_coe_of_eventually fun ε hε => ?_
  set M : ℝ := ∑ i ∈ is, (ρ i x + ‖(c i).liftOneSnd (B.oneVal y)‖) + 1 with hM
  have hM0 : 0 < M := by
    have : 0 ≤ ∑ i ∈ is, (ρ i x + ‖(c i).liftOneSnd (B.oneVal y)‖) :=
      Finset.sum_nonneg fun i _ => add_nonneg (ρ.nonneg i x) (norm_nonneg _)
    linarith
  set δ := ε / M with hδ
  have hδ0 : 0 < δ := div_pos hε hM0
  have hall : ∀ᶠ k in atTop, ∀ i ∈ is, ρ i x - δ < ρ i (P (B.oneVal (w k))) ∧
      ‖(c i).liftOneSnd (B.oneVal y)‖ - δ < ‖(c i).liftOneSnd (B.oneVal (w k))‖ := by
    refine (Filter.eventually_all_finset is).2 fun i hi => ?_
    exact ((tendsto_order.1 (hρc i)).1 _ (sub_lt_self _ hδ0)).and
      ((hweak i hi).eventually_norm_gt hδ0)
  filter_upwards [hall, hNw] with k hk hNk
  rw [hNy, hNk]
  have hterm : ∀ i ∈ is, ρ i x * ‖(c i).liftOneSnd (B.oneVal y)‖ -
      δ * (ρ i x + ‖(c i).liftOneSnd (B.oneVal y)‖) ≤
      ρ i (P (B.oneVal (w k))) * ‖(c i).liftOneSnd (B.oneVal (w k))‖ := fun i hi =>
    mul_sub_le_of_sub_lt (ρ.nonneg i x) (norm_nonneg _) (ρ.nonneg i _) (norm_nonneg _) hδ0
      (hk i hi).1 (hk i hi).2
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hlt : δ * ∑ i ∈ is, (ρ i x + ‖(c i).liftOneSnd (B.oneVal y)‖) < ε := by
    have h1 : δ * ∑ i ∈ is, (ρ i x + ‖(c i).liftOneSnd (B.oneVal y)‖) < δ * M :=
      mul_lt_mul_of_pos_left (by linarith) hδ0
    have h2 : δ * M = ε := by rw [hδ]; field_simp
    linarith
  linarith

/-- **The glued norm over charts with reflexive `F₁` is a reflexive auxiliary norm.** -/
theorem isReflexiveAuxNorm_gluedNorm (hc : ∀ i, B.IsChart (c i))
    (hF : ∀ i, IsReflexive ((c i).F 1)) (hρ : ρ.IsSubordinate fun i => (c i).φ.source) :
    B.IsReflexiveAuxNorm (gluedNorm B c ρ) := by
  have hN : B.IsAuxNorm (gluedNorm B c ρ) := by
    refine (lemma_5_1_2 (continuous_gluedNorm hc hρ) (isCompleteFiberNorm_gluedNorm hc hρ)).2
      fun x => ?_
    obtain ⟨c', hc'm, hx'⟩ := exists_chart_mem B x
    have hc' := B.isChart_of_mem hc'm
    obtain ⟨V, hVo, hxV, hVc, C, hC, hV⟩ := gluedNorm_bounds hc hρ hc' hx'
    refine ⟨c', hc', V, hVo, hxV, hVc, 1 / C, C + 1 / C, by positivity,
      by linarith [one_div_pos.2 hC], fun w hw => ⟨?_, ?_⟩⟩
    · rw [one_div_mul_eq_div, div_le_iff₀ hC, mul_comm]; exact (hV w hw).1
    · exact (hV w hw).2.trans (mul_le_mul_of_nonneg_right (by linarith [one_div_pos.2 hC])
        (gluedNorm_nonneg w))
  exact ⟨hN, fun w y hm => le_liminf_gluedNorm hc hF hρ hm⟩

end Prop518

end StrongBundle

open StrongBundle in
/-- **2021 Proposition 5.1.8, p. 208, existence** (2017: Proposition 5.2; proof left to the reader
in the text): a strong bundle with reflexive `(0, 1)`-fibres admits a reflexive auxiliary norm (the
glued norm `Σᵢ ρᵢ(P(w))·|Φᵢ[1](w)|₁` over the strong bundle charts with reflexive `F₁`, for a
partition of unity of the paracompact `X` subordinate to their domains). -/
theorem proposition_5_1_8_exists {B : StrongBundle PX P} (hB : B.HasReflexiveFibers) :
    ∃ N : B.One → ℝ, B.IsReflexiveAuxNorm N := by
  set ι := {c : StrongBundleChart PX P // B.IsChart c ∧ IsReflexive (c.F 1)}
  set c : ι → StrongBundleChart PX P := fun i => i.1 with hcdef
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i => (c i).φ.source) (fun i => (c i).φ.isOpen_source) fun x _ => by
      obtain ⟨c₀, hc₀, hx, hF⟩ := hB x
      exact mem_iUnion.2 ⟨⟨c₀, hc₀, hF⟩, hx⟩
  exact ⟨gluedNorm B c ρ, isReflexiveAuxNorm_gluedNorm (fun i => i.2.1) (fun i => i.2.2) hρ⟩

open StrongBundle in
/-- **2021 Proposition 5.1.8, p. 208, comparison** (2017: Proposition 5.2): for an auxiliary norm
`N₀` and a reflexive auxiliary norm `N₁` there is a continuous `f : X → (0, ∞)` with
`f(x)·N₀(y) ≤ N₁(y) ≤ (1/f(x))·N₀(y)` for `y ∈ Y_{0,1}`, `x = P(y)`. -/
theorem proposition_5_1_8_compare {B : StrongBundle PX P} {N₀ N₁ : B.One → ℝ}
    (h₀ : B.IsAuxNorm N₀) (h₁ : B.IsReflexiveAuxNorm N₁) :
    ∃ f : X → ℝ, Continuous f ∧ (∀ x, 0 < f x) ∧ ∀ w : B.One,
      f (P (B.oneVal w)) * N₀ w ≤ N₁ w ∧ N₁ w ≤ (f (P (B.oneVal w)))⁻¹ * N₀ w :=
  proposition_5_1_3_compare h₀ h₁.toIsAuxNorm

open StrongBundle in
/-- **2021 Proposition 5.1.8, p. 208** (2017: Proposition 5.2), both parts. -/
theorem proposition_5_1_8 {B : StrongBundle PX P} (hB : B.HasReflexiveFibers) :
    (∃ N : B.One → ℝ, B.IsReflexiveAuxNorm N) ∧
      ∀ N₀ N₁ : B.One → ℝ, B.IsAuxNorm N₀ → B.IsReflexiveAuxNorm N₁ →
        ∃ f : X → ℝ, Continuous f ∧ (∀ x, 0 < f x) ∧ ∀ w : B.One,
          f (P (B.oneVal w)) * N₀ w ≤ N₁ w ∧ N₁ w ≤ (f (P (B.oneVal w)))⁻¹ * N₀ w :=
  ⟨proposition_5_1_8_exists hB, fun _ _ h₀ h₁ => proposition_5_1_8_compare h₀ h₁⟩

/-! ### Positive multiples and the sandwich

The M-polyfold form of Theorem 12.2.11 and Remark 12.2.12. -/

namespace StrongBundle

variable {B : StrongBundle PX P}

/-- The `liminf` clause in the form "`N(y) - ε < N(y_k)` eventually". -/
theorem IsReflexiveAuxNorm.eventually_sub_lt {N : B.One → ℝ} (hN : B.IsReflexiveAuxNorm N)
    {w : ℕ → B.One} {y : B.One} (hm : B.MixedTendsto w y) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, N y - ε < N (w k) := by
  have h1 : ((N y - ε : ℝ) : EReal) < liminf (fun k => (N (w k) : EReal)) atTop :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (sub_lt_self _ hε)) (hN.le_liminf w y hm)
  exact (eventually_lt_of_lt_liminf h1).mono fun k hk => EReal.coe_lt_coe_iff.1 hk

/-- **`(g ∘ P)·N` is an auxiliary norm** for an auxiliary norm `N` and a continuous
`g : X → (0, ∞)`. -/
theorem IsAuxNorm.comp_mul {N : B.One → ℝ} (hN : B.IsAuxNorm N) {g : X → ℝ} (hg : Continuous g)
    (hg0 : ∀ x, 0 < g x) : B.IsAuxNorm fun w => g (P (B.oneVal w)) * N w where
  continuous := (hg.comp (B.continuous.comp B.continuous_oneVal)).mul hN.continuous
  fiber x := by
    have e : ∀ v : B.oneFiber x, g (P (B.oneVal (B.toOne v))) = g x := fun v =>
      congrArg g (proj_oneVal_toOne B v)
    have ha := hg0 x
    exact
      { eq_zero := fun v hv => (hN.fiber x).eq_zero v
          ((mul_eq_zero.1 (by rw [e v] at hv; exact hv)).resolve_left ha.ne')
        smul := fun t v => by rw [e, e, (hN.fiber x).smul]; ring
        add_le := fun v w => by
          rw [e, e, e, ← mul_add]
          exact mul_le_mul_of_nonneg_left ((hN.fiber x).add_le v w) ha.le
        complete := fun u hu => by
          obtain ⟨v, hv⟩ := (hN.fiber x).complete u fun ε hε => by
            obtain ⟨n, hn⟩ := hu (g x * ε) (mul_pos ha hε)
            refine ⟨n, fun m hm k hk => (mul_lt_mul_iff_of_pos_left ha).1 ?_⟩
            have := hn m hm k hk
            rwa [e] at this
          refine ⟨v, ?_⟩
          have h1 := hv.const_mul (g x)
          rw [mul_zero] at h1
          exact h1.congr fun k => by rw [e] }
  tendsto_zeroOne w x hw hNw := by
    refine hN.tendsto_zeroOne w x hw ?_
    have hgx : Tendsto (fun k => g (P (B.oneVal (w k)))) atTop (𝓝 (g x)) :=
      (hg.tendsto x).comp hw
    have h1 := hNw.div hgx (hg0 x).ne'
    rw [zero_div] at h1
    exact h1.congr fun k => mul_div_cancel_left₀ _ (hg0 (P (B.oneVal (w k)))).ne'

/-- **Remark 12.2.12 (1), M-polyfold form** (stated in the 2021 text for ep-groupoids, p. 577):
`(g ∘ P)·N` is a reflexive auxiliary norm for a reflexive auxiliary norm `N` and a continuous
`g : X → (0, ∞)`. -/
theorem IsReflexiveAuxNorm.comp_mul {N : B.One → ℝ} (hN : B.IsReflexiveAuxNorm N) {g : X → ℝ}
    (hg : Continuous g) (hg0 : ∀ x, 0 < g x) :
    B.IsReflexiveAuxNorm fun w => g (P (B.oneVal w)) * N w := by
  refine ⟨hN.toIsAuxNorm.comp_mul hg hg0, fun w y hm => le_liminf_coe_of_eventually ?_⟩
  intro ε hε
  set a := g (P (B.oneVal y))
  set b := N y
  have ha := hg0 (P (B.oneVal y))
  have hb := hN.nonneg y
  set δ := ε / (a + b + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  have hgk : ∀ᶠ k in atTop, a - δ < g (P (B.oneVal (w k))) :=
    (tendsto_order.1 ((hg.tendsto _).comp hm.1)).1 _ (sub_lt_self _ hδ0)
  filter_upwards [hgk, hN.eventually_sub_lt hm hδ0] with k hk1 hk2
  have h := mul_sub_le_of_sub_lt ha.le hb (hg0 _).le (hN.nonneg (w k)) hδ0 hk1 hk2
  have h2 : δ * (a + b) < ε := by
    have : δ * (a + b + 1) = ε := by rw [hδ]; exact div_mul_cancel₀ ε (by positivity)
    nlinarith
  linarith

/-- **The sandwich, M-polyfold form of the last clause of Theorem 12.2.11** (p. 577): with
reflexive `(0, 1)`-fibres, every auxiliary norm `N'` lies between two reflexive auxiliary norms,
`N₁ ≤ N' ≤ N₂`. -/
theorem exists_reflexiveAuxNorm_sandwich (hB : B.HasReflexiveFibers) {N' : B.One → ℝ}
    (hN' : B.IsAuxNorm N') :
    ∃ N₁ N₂ : B.One → ℝ, B.IsReflexiveAuxNorm N₁ ∧ B.IsReflexiveAuxNorm N₂ ∧
      ∀ w, N₁ w ≤ N' w ∧ N' w ≤ N₂ w := by
  obtain ⟨N, hN⟩ := proposition_5_1_8_exists hB
  obtain ⟨f, hf, hf0, hfN⟩ := proposition_5_1_8_compare hN' hN
  refine ⟨fun w => f (P (B.oneVal w)) * N w, fun w => (f (P (B.oneVal w)))⁻¹ * N w,
    hN.comp_mul hf hf0, hN.comp_mul (hf.inv₀ fun x => (hf0 x).ne') fun x => inv_pos.2 (hf0 x),
    fun w => ⟨?_, ?_⟩⟩
  · change f (P (B.oneVal w)) * N w ≤ N' w
    have h := (hfN w).2
    have hp := hf0 (P (B.oneVal w))
    calc f (P (B.oneVal w)) * N w ≤ f (P (B.oneVal w)) * ((f (P (B.oneVal w)))⁻¹ * N' w) :=
          mul_le_mul_of_nonneg_left h hp.le
      _ = N' w := by rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
  · change N' w ≤ (f (P (B.oneVal w)))⁻¹ * N w
    have h := (hfN w).1
    have hp := hf0 (P (B.oneVal w))
    rw [inv_mul_eq_div, le_div_iff₀ hp]
    linarith [mul_comm (f (P (B.oneVal w))) (N' w)]

end StrongBundle

end Polyfold
