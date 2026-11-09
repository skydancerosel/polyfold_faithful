import Polyfold.Chapter5.Compactness
import Polyfold.Chapter5.BumpFunctions

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §5.3,
**Remark 5.3.4 (preprint 5.12)** (the completion of the allowable sc⁺-sections) *(book 2017: Remark 5.3; see
`BookConcordance.md`)*.

# The solution set of `f + s` for `s` in the completion of `Γ^{+,1}_U(P)` is compact

## The text, paraphrased

(Remark 5.3.4 (preprint 5.12)) Let `f` be an sc-Fredholm section with compact solution set, `N` an auxiliary norm
and `U` an open neighbourhood of `f⁻¹(0)` adapted to `N` as in the properness result (Theorem 5.2.2 (preprint 5.5)).
On `Γ^{+,1}_U(P)` (the sc⁺-sections with support in `U` and `N(s) ≤ 1`) take the distance
`ρ(s, s') = sup_x N(s(x) − s'(x))`.  Then for every `s` in the completion of `Γ^{+,1}_U(P)` the
solution set of `f + s = 0` is still compact.

## What is formalized

* `Polyfold.StrongBundle.IsInAllowableCompletion` (**the completion of `(Γ^{+,1}_U(P), ρ)`, as
  sections**): a section `s` with values in `Y_{0,1}` such that for every `ε > 0` some
  `s' ∈ Γ^{+,1}_U(P)` (`StrongBundle.allowableSections`) has `N(s(x) − s'(x)) ≤ ε` for all `x`
  (the difference taken in the fibre `(Y_{0,1})_x`, `StrongBundle.sectionOneVec`);
  `StrongBundle.isInAllowableCompletion_of_mem` (the allowable sections themselves).
* `StrongBundle.IsInAllowableCompletion.isZeroAt_of_not_mem` and `.auxLe_one`: a point of the
  completion vanishes off `U` and has `N(s(x)) ≤ 1` everywhere (the hypotheses of the project's
  `Polyfold.remark_5_3_4`).
* `StrongBundle.IsInAllowableCompletion.isClosed_solutionSet_sectionAdd` (**the solution set of
  `f + s` is closed**, the step the text does not discuss): for a continuous section `f` and `s` in
  the completion, `{x | f(x) + s(x) = 0}` is closed in `X`.
* `Polyfold.remark_5_3_4_completion` (**Remark 5.3.4 (preprint 5.12) as stated**, for `U` with
  `cl{x ∈ U | N(f(x)) ≤ 1}` compact) and `Polyfold.remark_5_3_4_of_isScFredholmSection` (for an
  sc-Fredholm section with compact solution set, with the neighbourhood `U` of Theorem 5.2.2 (preprint 5.5)).

## What the text leaves implicit, and the choices made (the findings)

* **The completion is represented by sections.**  The fibres `(Y_{0,1})_x` are complete for `N`
  (Definition 5.1.1 (preprint 5.1) (1)), so a `ρ`-Cauchy sequence in `Γ^{+,1}_U(P)` converges uniformly (in `N`)
  to a section with values in `Y_{0,1}`; the remark speaks of `f + s` for `s` in the completion,
  which presupposes this identification.  `IsInAllowableCompletion` is the property "uniform
  `N`-limit of allowable sections"; the metric space `(Γ^{+,1}_U(P), ρ)` and its completion are
  not constructed (Chapter 5 item 89).
* **Closedness is the missing step.**  `Polyfold.remark_5_3_4` (in `Compactness.lean`) gives
  `S_{f+s} ⊆ {x ∈ U | N(f(x)) ≤ 1}` and the compactness of the closure.  The continuity of a
  limit `s` is not part of the data (`ρ` is a uniform distance in `N`, not in the topology of `Y`),
  so the closedness of `S_{f+s}` has to be proved.  It is proved by a
  chart argument: near a limit point `x` of `S_{f+s}`, in a strong bundle chart `Φ` of the atlas,
  Lemma 5.1.2 (preprint 5.2)'s bound `|Φ[1](w)₂|₁ ≤ A·N(w)` (`StrongBundle.IsAuxNorm.exists_norm_liftOne_le`)
  turns `N(s − s') ≤ ε` into `|Φ(s(y))₂ − Φ(s'(y))₂|₀ ≤ ‖ι‖·A·ε` near `x` for an allowable `s'`;
  `y ↦ Φ(f(y))₂ + Φ(s'(y))₂` is continuous at `x` (`s'` is sc⁺, so continuous) and is small at the
  zeros of `f + s`, so `|Φ(f(x))₂ + Φ(s(x))₂|₀ ≤ 2‖ι‖Aε` for every `ε`, i.e. `f(x) + s(x) = 0`.
  Only the continuity of `f` is used (no sc-Fredholm property, no compactness).
* This file moves the round-trip auditor's proof (round-trip item V5.22,
  `RoundTrip/Items/V5_22.lean`, `isClosed_solSet`) into the project.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace StrongBundle

variable (B) in
/-- The value `s(x)` of a section `s` with values in `Y_{0,1}`, as a vector of the fibre
`(Y_{0,1})_x` (`StrongBundle.oneFiber`). -/
def sectionOneVec {s : X → Y} (hs : IsSection P s) (hs1 : ∀ x, s x ∈ B.oneSet) (x : X) :
    B.oneFiber x :=
  ⟨⟨s x, hs x⟩, hs1 x⟩

variable (B) in
/-- **The completion of `(Γ^{+,1}_U(P), ρ)`, as sections** (Remark 5.3.4 (preprint 5.12)): `s` is a section of `P`
with values in `Y_{0,1}` which is a uniform `N`-limit of allowable sections, i.e. for every
`ε > 0` some `s' ∈ Γ^{+,1}_U(P)` has `ρ(s, s') = sup_x N(s(x) − s'(x)) ≤ ε` (the difference
taken in the fibre `(Y_{0,1})_x`).  Since the fibres are complete for `N`, these are the limits
of the `ρ`-Cauchy sequences of allowable sections. -/
structure IsInAllowableCompletion (N : B.One → ℝ) (U : Set X) (s : X → Y) : Prop where
  isSection : IsSection P s
  mem_oneSet : ∀ x, s x ∈ B.oneSet
  approx : ∀ ε > 0, ∃ s', ∃ hs' : s' ∈ B.allowableSections N U, ∀ x,
    N (B.toOne (B.sectionOneVec isSection mem_oneSet x -
      B.sectionOneVec hs'.1.1 hs'.1.mem_oneSet x)) ≤ ε

/-- Remark 5.3.4 (preprint 5.12): the allowable sections lie in the completion (the constant sequence; round-trip
item V5.22). -/
theorem isInAllowableCompletion_of_mem {N : B.One → ℝ} (hN : B.IsAuxNorm N) {U : Set X}
    {s : X → Y} (hs : s ∈ B.allowableSections N U) : B.IsInAllowableCompletion N U s := by
  refine ⟨hs.1.1, hs.1.mem_oneSet, fun ε hε => ⟨s, hs, fun x => ?_⟩⟩
  rw [sub_self]
  change N (B.zeroOne x) ≤ ε
  rw [(hN.fiber x).map_zero]
  exact hε.le

/-- An allowable section vanishes off `U` (its support lies in `U`; used for Remark 5.3.4 (preprint 5.12),
round-trip item V5.22). -/
lemma sectionOneVec_eq_zero_of_mem_allowableSections {N : B.One → ℝ} {U : Set X} {s : X → Y}
    (hs : s ∈ B.allowableSections N U) {x : X} (hx : x ∉ U) :
    B.sectionOneVec hs.1.1 hs.1.mem_oneSet x = 0 := by
  have h0 : s x = fiberZero P x := by
    by_contra h
    exact hx (hs.2.1 (subset_closure h))
  exact Subtype.ext (Subtype.ext h0)

namespace IsInAllowableCompletion

variable {N : B.One → ℝ} {U : Set X} {s : X → Y}

/-- **A point of the completion vanishes off `U`** (Remark 5.3.4 (preprint 5.12), "both survive uniform limits";
round-trip item V5.22): `N(s(x)) ≤ ε` for every `ε` at `x ∉ U`. -/
theorem isZeroAt_of_not_mem (hN : B.IsAuxNorm N) (hs : B.IsInAllowableCompletion N U s) {x : X}
    (hx : x ∉ U) : IsZeroAt P s x := by
  have hle : ∀ ε > 0, N (B.toOne (B.sectionOneVec hs.isSection hs.mem_oneSet x)) ≤ ε := by
    intro ε hε
    obtain ⟨s', hs', hd⟩ := hs.approx ε hε
    have := hd x
    rwa [sectionOneVec_eq_zero_of_mem_allowableSections hs' hx, sub_zero] at this
  have h0 : N (B.toOne (B.sectionOneVec hs.isSection hs.mem_oneSet x)) = 0 :=
    le_antisymm (le_of_forall_pos_le_add fun ε hε => by simpa using hle ε hε)
      ((hN.fiber x).nonneg _)
  have h1 := (hN.fiber x).eq_zero _ h0
  exact congrArg (fun v : B.oneFiber x => ((v : P ⁻¹' {x}) : Y)) h1

/-- **A point of the completion has `N(s(x)) ≤ 1` everywhere** (Remark 5.3.4 (preprint 5.12); round-trip item
V5.22): the triangle inequality in the fibre and `N(s'(x)) ≤ 1` for the allowable `s'`. -/
theorem auxLe_one (hN : B.IsAuxNorm N) (hs : B.IsInAllowableCompletion N U s) (x : X) :
    B.AuxLe N (s x) 1 := by
  refine ⟨hs.mem_oneSet x, ?_⟩
  change N (B.toOne (B.sectionOneVec hs.isSection hs.mem_oneSet x)) ≤ 1
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨s', hs', hd⟩ := hs.approx ε hε
  have h1 := hd x
  have h2 : N (B.toOne (B.sectionOneVec hs'.1.1 hs'.1.mem_oneSet x)) ≤ 1 :=
    hs'.2.2 x (hs'.1.mem_oneSet x)
  have h3 := (hN.fiber x).add_le
    (B.sectionOneVec hs.isSection hs.mem_oneSet x - B.sectionOneVec hs'.1.1 hs'.1.mem_oneSet x)
    (B.sectionOneVec hs'.1.1 hs'.1.mem_oneSet x)
  rw [sub_add_cancel] at h3
  linarith

/-- **The solution set of `f + s` is closed** for a continuous section `f` and a point `s` of the
completion of `Γ^{+,1}_U(P)` (Remark 5.3.4 (preprint 5.12); the step the text does not discuss).  *Proof*: let `x`
be a limit point of `S_{f+s}`, and `Φ` a strong bundle chart of the atlas at `x`.  Lemma 5.1.2 (preprint 5.2)
(`IsAuxNorm.exists_norm_liftOne_le`) gives `|Φ(w)₂|₀ ≤ κ·A·N(w)` for `w ∈ Y_{0,1}` over a
neighbourhood `V` of `x` (`κ = ‖ι : F₁ → F₀‖`).  For an allowable `s'` with `ρ(s, s') ≤ ε` the
principal parts satisfy `|Φ(s(y))₂ − Φ(s'(y))₂|₀ ≤ κAε` on `V`; `y ↦ |Φ(f(y))₂ + Φ(s'(y))₂|₀` is
continuous at `x` and `≤ κAε` at the zeros of `f + s` in `V`, hence at `x`, so
`|Φ(f(x))₂ + Φ(s(x))₂|₀ ≤ 2κAε` for every `ε > 0`.  Thus `Φ(f(x) + s(x)) = Φ(0_x)`.  Round-trip
item V5.22. -/
theorem isClosed_solutionSet_sectionAdd (hN : B.IsAuxNorm N) {f : X → Y} (hfc : Continuous f)
    (hf : IsSection P f) (hs : B.IsInAllowableCompletion N U s) :
    IsClosed (solutionSet P (sectionAdd P f s)) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B x
  have hcB := B.isChart_of_mem hc
  obtain ⟨V, hVo, hxV, hVc, A, hA, hbd⟩ := hN.exists_norm_liftOne_le hcB hxc
  set κ := ‖c.F.toBase 1‖ with hκ
  have hκ0 : 0 ≤ κ := norm_nonneg _
  have hsrc : ∀ {y : X} (v : P ⁻¹' {y}), y ∈ c.φ.source → (v : Y) ∈ c.toPartialEquiv.source :=
    fun {y} v hy => c.mem_source_of_proj (by rw [v.2]; exact hy)
  -- the chart estimate (Lemma 5.1.2 (preprint 5.2))
  have key : ∀ y ∈ V, ∀ v : B.oneFiber y,
      ‖(c ((v : P ⁻¹' {y}) : Y)).2‖ ≤ κ * (A * N (B.toOne v)) := by
    intro y hy v
    have hPy : P (B.oneVal (B.toOne v)) ∈ V := by
      have e : P (B.oneVal (B.toOne v)) = y := (v : P ⁻¹' {y}).2
      rw [e]; exact hy
    have hb := hbd (B.toOne v) hPy
    have hmem : (c ((v : P ⁻¹' {y}) : Y)).2 ∈ Set.range (c.F.toBase 1) :=
      v.2 c hc (hsrc (v : P ⁻¹' {y}) (hVc hy))
    have he : c.F.toBase 1 (c.liftOne ((v : P ⁻¹' {y}) : Y)).2 = (c ((v : P ⁻¹' {y}) : Y)).2 :=
      congrArg Prod.snd (c.toBase_liftOne hmem)
    rw [← he]
    exact ((c.F.toBase 1).le_opNorm _).trans (mul_le_mul_of_nonneg_left hb hκ0)
  -- the principal parts
  have hsecs := hs.isSection
  have hfx : ∀ y ∈ c.φ.source, (c (sectionAdd P f s y)).2 = (c (f y)).2 + (c (s y)).2 :=
    fun y hy => by rw [sectionAdd_apply hf hsecs]; exact c.snd_add hy _ _
  have hfreq : ∃ᶠ y in 𝓝 x, y ∈ solutionSet P (sectionAdd P f s) :=
    mem_closure_iff_frequently.1 hx
  have hVev : ∀ᶠ y in 𝓝 x, y ∈ V := hVo.mem_nhds hxV
  have hcf : ContinuousAt (fun y => (c (f y)).2) x := by
    have h1 : ContinuousAt c (f x) := c.continuousOn_toFun.continuousAt
      ((c.isOpen_source B.continuous).mem_nhds (c.mem_source_of_proj (by rw [hf x]; exact hxc)))
    exact continuous_snd.continuousAt.comp (h1.comp hfc.continuousAt)
  -- the estimate at `x`
  have hest : ∀ ε > 0, ‖(c (f x)).2 + (c (s x)).2‖ ≤ 2 * (κ * (A * ε)) := by
    intro ε hε
    obtain ⟨s', hs', hd⟩ := hs.approx ε hε
    have hs'sec := hs'.1.1
    have hdiff : ∀ y ∈ V, ‖(c (s y)).2 - (c (s' y)).2‖ ≤ κ * (A * ε) := by
      intro y hy
      have h1 := key y hy (B.sectionOneVec hsecs hs.mem_oneSet y -
        B.sectionOneVec hs'sec hs'.1.mem_oneSet y)
      have h3 : (c (((B.sectionOneVec hsecs hs.mem_oneSet y -
          B.sectionOneVec hs'sec hs'.1.mem_oneSet y : B.oneFiber y) : P ⁻¹' {y}) : Y)).2 =
          (c (s y)).2 - (c (s' y)).2 :=
        c.snd_sub (hVc hy) _ _
      rw [h3] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hd y) hA.le) hκ0)
    have hcs' : ContinuousAt (fun y => (c (s' y)).2) x := by
      have h0 := (hs'.1.continuousOn_source hcB).continuousAt (c.φ.isOpen_source.mem_nhds hxc)
      have h1 : ContinuousAt c (s' x) := c.continuousOn_toFun.continuousAt
        ((c.isOpen_source B.continuous).mem_nhds
          (c.mem_source_of_proj (by rw [hs'sec x]; exact hxc)))
      exact continuous_snd.continuousAt.comp (h1.comp h0)
    have hg : ContinuousAt (fun y => ‖(c (f y)).2 + (c (s' y)).2‖) x := (hcf.add hcs').norm
    have hgx : ‖(c (f x)).2 + (c (s' x)).2‖ ≤ κ * (A * ε) := by
      by_contra hlt
      push Not at hlt
      have hev := hg.eventually (lt_mem_nhds hlt)
      obtain ⟨y, hyS, hyV, hy⟩ := (hfreq.and_eventually (hVev.and hev)).exists
      have hz : (c (f y)).2 + (c (s y)).2 = 0 := by
        rw [← hfx y (hVc hyV)]
        have : sectionAdd P f s y = fiberZero P y := hyS
        rw [this]; exact c.snd_fiberZero (hVc hyV)
      have : (c (f y)).2 + (c (s' y)).2 = -((c (s y)).2 - (c (s' y)).2) := by
        rw [eq_neg_of_add_eq_zero_left hz]; abel
      rw [this, norm_neg] at hy
      exact absurd (hdiff y hyV) (not_le.2 hy)
    have : (c (f x)).2 + (c (s x)).2 =
        ((c (f x)).2 + (c (s' x)).2) + ((c (s x)).2 - (c (s' x)).2) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    linarith [hdiff x hxV]
  have hzero : (c (f x)).2 + (c (s x)).2 = 0 := by
    by_contra hne
    have hpos : 0 < ‖(c (f x)).2 + (c (s x)).2‖ := norm_pos_iff.2 hne
    set δ := ‖(c (f x)).2 + (c (s x)).2‖
    have h := hest (δ / (4 * (κ * A) + 1)) (by positivity)
    have hκA : 0 ≤ κ * A := mul_nonneg hκ0 hA.le
    have : 2 * (κ * (A * (δ / (4 * (κ * A) + 1)))) ≤ δ / 2 := by
      rw [← mul_assoc, ← mul_assoc, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    linarith
  -- conclude: `Φ(f(x) + s(x)) = Φ(0_x)`
  have hsrc1 : sectionAdd P f s x ∈ c.toPartialEquiv.source :=
    c.mem_source_of_proj (by rw [hf.sectionAdd hsecs x]; exact hxc)
  have hsrc0 : fiberZero P x ∈ c.toPartialEquiv.source :=
    c.mem_source_of_proj (by rw [proj_fiberZero P]; exact hxc)
  change sectionAdd P f s x = fiberZero P x
  refine c.toPartialEquiv.injOn hsrc1 hsrc0 (Prod.ext ?_ ?_)
  · rw [c.fst_apply (by rw [hf.sectionAdd hsecs x]; exact hxc),
      c.fst_apply (by rw [proj_fiberZero P]; exact hxc), hf.sectionAdd hsecs x,
      proj_fiberZero P]
  · rw [hfx x hxc, hzero, c.snd_fiberZero hxc]

end IsInAllowableCompletion

end StrongBundle

open StrongBundle

/-- **Remark 5.3.4 (preprint 5.12)** (as stated): let `f` be a continuous section, `N` an auxiliary norm and `U` an
open neighbourhood of `f⁻¹(0)` adapted to `N` (`cl{x ∈ U | N(f(x)) ≤ 1}` compact, as in Theorem
5.5).  For every `s` in the completion of `(Γ^{+,1}_U(P), ρ)` the solution set of `f + s = 0` is
compact (and lies in `{x ∈ U | N(f(x)) ≤ 1}`).  *Proof*: `s` vanishes off `U` and has
`N(s) ≤ 1` (`IsInAllowableCompletion.isZeroAt_of_not_mem`, `.auxLe_one`), so `remark_5_3_4` gives
the inclusion and the compactness of the closure; the solution set is closed
(`IsInAllowableCompletion.isClosed_solutionSet_sectionAdd`).  Round-trip item V5.22. -/
theorem remark_5_3_4_completion {N : B.One → ℝ} (hN : B.IsAuxNorm N) {f : X → Y}
    (hfc : Continuous f) (hf : IsSection P f) {U : Set X} (hSU : solutionSet P f ⊆ U)
    (hU : IsCompact (closure {x ∈ U | B.AuxLe N (f x) 1})) {s : X → Y}
    (hs : B.IsInAllowableCompletion N U s) :
    solutionSet P (sectionAdd P f s) ⊆ {x ∈ U | B.AuxLe N (f x) 1} ∧
      IsCompact (solutionSet P (sectionAdd P f s)) := by
  obtain ⟨hsub, hcl⟩ := remark_5_3_4 hN hf hSU hU hs.isSection
    (fun x hx => hs.isZeroAt_of_not_mem hN hx) (fun x => hs.auxLe_one hN x)
  have hclosed := hs.isClosed_solutionSet_sectionAdd hN hfc hf
  rw [hclosed.closure_eq] at hcl
  exact ⟨hsub, hcl⟩

/-- **Remark 5.3.4 (preprint 5.12) for an sc-Fredholm section** (the text's setting): if `f` is sc-Fredholm with
compact solution set and `N` is an auxiliary norm, there is an open neighbourhood `U` of `f⁻¹(0)`
(the one of Theorem 5.2.2 (preprint 5.5), `cl{x ∈ U | N(f(x)) ≤ 1}` compact) such that for every `s` in the
completion of `(Γ^{+,1}_U(P), ρ)` the solution set of `f + s = 0` is compact.  Round-trip item
V5.22. -/
theorem remark_5_3_4_of_isScFredholmSection {f : X → Y} (hf : B.IsScFredholmSection f)
    (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ} (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      IsCompact (closure {x ∈ U | B.AuxLe N (f x) 1}) ∧
      ∀ s : X → Y, B.IsInAllowableCompletion N U s →
        IsCompact (solutionSet P (sectionAdd P f s)) := by
  obtain ⟨U, hUo, hSU, hK⟩ := (theorem_5_2_2_preprint hf hS).2 N hN
  have hfc : Continuous f := continuousOn_univ.1 hf.isScSmooth.2.continuousOn
  exact ⟨U, hUo, hSU, hK, fun s hs =>
    (remark_5_3_4_completion hN hfc hf.isScSmooth.1 hSU hK hs).2⟩

end Polyfold
