import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_22

/-!
Round trip for V5_22 (Remark 5.12).  Refreshed 2026-11-02: the comparison row now cites the
completion form (`StrongBundle.IsInAllowableCompletion`, the closedness of `S_{f+s}`,
`remark_5_12_completion`, `remark_5_12_of_isScFredholmSection`; the closedness argument is the one
this item's first audit supplied, moved into the project).

A = `remark_5_12` ∧ `IsAuxNorm.auxLe_of_sectionAdd` ∧
`IsInAllowableCompletion.isClosed_solutionSet_sectionAdd` ∧ `remark_5_12_completion` ∧
`remark_5_12_of_isScFredholmSection` (universes `0`; `IsInAllowableCompletion` is vocabulary, and is
B's `InCompletion`: `inCompletion_of`).

B: for an sc-Fredholm `f` (germ reading, as in A) with compact `S_f`, `U` adapted, and `s` in the
`ρ`-completion of `Γ^{+,1}_U(P)` (a uniform `N`-limit of allowable sections), the solution set is
COMPACT.

`A ⇒ B` is proved (as in the first audit, from A's first conjunct): the completion gives `s = 0`
off `U` and `N(s) ≤ 1` (`vanish_off`, `auxLe_one`), `remark_5_12` gives compact closure, and the
closedness of `S_{f+s}` is proved here (`isClosed_solSet`) by a chart argument: near a limit point
`x`, in a strong bundle chart of the atlas, Lemma 5.2's bound `|Φ[1](w)₂|₁ ≤ A·N(w)`
(`IsAuxNorm.exists_norm_liftOne_le`) turns the uniform `N`-approximation of `s` by sc⁺-sections
`s'` into an `F₀`-approximation of the principal parts, and `f̂ + ŝ'` is continuous at `x`.

`B ⇒ A` is not proved: A's first four conjuncts are about ARBITRARY (continuous) sections `f`,
`s`, without the sc-Fredholm property or compactness of `S_f`.  B gives the fifth conjunct
`remark_5_12_of_isScFredholmSection` together with Theorem 5.5 (which supplies an adapted `U`):
`B_gives_of_isScFredholmSection`.
-/

namespace RoundTrip.V5_22
open Polyfold Filter Topology

/-- The project's statement (Remark 5.12, its fibre lemma, and the completion form), universes
instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.remark_5_12.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.IsAuxNorm.auxLe_of_sectionAdd.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.IsInAllowableCompletion.isClosed_solutionSet_sectionAdd.{0, 0} ∧
  type_of% @Polyfold.remark_5_12_completion.{0, 0} ∧
  type_of% @Polyfold.remark_5_12_of_isScFredholmSection.{0, 0}

theorem A_holds : A := ⟨@Polyfold.remark_5_12.{0, 0},
  @Polyfold.StrongBundle.IsAuxNorm.auxLe_of_sectionAdd.{0, 0},
  @Polyfold.StrongBundle.IsInAllowableCompletion.isClosed_solutionSet_sectionAdd.{0, 0},
  @Polyfold.remark_5_12_completion.{0, 0}, @Polyfold.remark_5_12_of_isScFredholmSection.{0, 0}⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The value of a section with values in `Y_{0,1}` as a vector of `(Y_{0,1})_x`. -/
def vecOf (Bd : StrongBundle PX P) {s : X → Y} (hsec : IsSection P s)
    (h1 : ∀ x, s x ∈ Bd.oneSet) (x : X) : Bd.oneFiber x :=
  ⟨⟨s x, hsec x⟩, h1 x⟩

lemma fibDist_eq' {Bd : StrongBundle PX P} (N : Bd.One → ℝ) {s s' : X → Y}
    (hsec : IsSection P s) (h1 : ∀ x, s x ∈ Bd.oneSet)
    (hsec' : IsSection P s') (h1' : ∀ x, s' x ∈ Bd.oneSet) (x : X) :
    fibDist Bd N s s' x = N (Bd.toOne (vecOf Bd hsec h1 x - vecOf Bd hsec' h1' x)) := by
  unfold fibDist
  rw [dif_pos ⟨⟨hsec x, hsec' x⟩, ⟨h1 x, h1' x⟩⟩]
  rfl

/-- An allowable section vanishes off `U`. -/
lemma vecOf_eq_zero {Bd : StrongBundle PX P} {N : Bd.One → ℝ} {U : Set X} {s' : X → Y}
    (hs' : s' ∈ Gamma1 Bd N U) {x : X} (hx : x ∉ U) :
    vecOf Bd hs'.1.1 hs'.1.mem_oneSet x = 0 := by
  have h0 : s' x = ((0 : P ⁻¹' {x}) : Y) := by
    by_contra h
    exact hx (hs'.2.1 (subset_closure h))
  exact Subtype.ext (Subtype.ext h0)

/-- A point of the completion vanishes off `U`. -/
theorem vanish_off {Bd : StrongBundle PX P} {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N) {U : Set X}
    {s : X → Y} (hs : InCompletion Bd N U s) {x : X} (hx : x ∉ U) : IsZeroAt P s x := by
  have hle : ∀ ε > 0, N (Bd.toOne (vecOf Bd hs.1 hs.2.1 x)) ≤ ε := by
    intro ε hε
    obtain ⟨s', hs', hd⟩ := hs.2.2 ε hε
    have := hd x
    rw [fibDist_eq' N hs.1 hs.2.1 hs'.1.1 hs'.1.mem_oneSet, vecOf_eq_zero hs' hx,
      sub_zero] at this
    exact this
  have h0 : N (Bd.toOne (vecOf Bd hs.1 hs.2.1 x)) = 0 :=
    le_antisymm (le_of_forall_pos_le_add fun ε hε => by simpa using hle ε hε)
      ((hN.fiber x).nonneg _)
  have h1 := (hN.fiber x).eq_zero _ h0
  exact congrArg (fun v : Bd.oneFiber x => ((v : P ⁻¹' {x}) : Y)) h1

/-- A point of the completion has `N(s(x)) ≤ 1` everywhere. -/
theorem auxLe_one {Bd : StrongBundle PX P} {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N) {U : Set X}
    {s : X → Y} (hs : InCompletion Bd N U s) (x : X) : Bd.AuxLe N (s x) 1 := by
  refine ⟨hs.2.1 x, ?_⟩
  change N (Bd.toOne (vecOf Bd hs.1 hs.2.1 x)) ≤ 1
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨s', hs', hd⟩ := hs.2.2 ε hε
  have h1 := hd x
  rw [fibDist_eq' N hs.1 hs.2.1 hs'.1.1 hs'.1.mem_oneSet] at h1
  obtain ⟨_, h2⟩ := hs'.2.2 x
  have h2' : N (Bd.toOne (vecOf Bd hs'.1.1 hs'.1.mem_oneSet x)) ≤ 1 := h2
  have h3 := (hN.fiber x).add_le (vecOf Bd hs.1 hs.2.1 x - vecOf Bd hs'.1.1 hs'.1.mem_oneSet x)
    (vecOf Bd hs'.1.1 hs'.1.mem_oneSet x)
  rw [sub_add_cancel] at h3
  linarith

/-- **The solution set of `f + s = 0` is closed** for a continuous section `f` and a point `s`
of the completion of `Γ^{+,1}_U(P)`. -/
theorem isClosed_solSet {Bd : StrongBundle PX P} {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N)
    {U : Set X} {f s : X → Y} (hfc : Continuous f) (hf : IsSection P f)
    (hs : InCompletion Bd N U s) : IsClosed (solSet P (sectionAdd P f s)) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem Bd x
  have hcB := Bd.isChart_of_mem hc
  obtain ⟨V, hVo, hxV, hVc, A, hA, hbd⟩ := hN.exists_norm_liftOne_le hcB hxc
  set κ := ‖c.F.toBase 1‖ with hκ
  have hκ0 : 0 ≤ κ := norm_nonneg _
  have hsrc : ∀ {y : X} (v : P ⁻¹' {y}), y ∈ c.φ.source → (v : Y) ∈ c.toPartialEquiv.source :=
    fun {y} v hy => c.mem_source_of_proj (by rw [v.2]; exact hy)
  -- the chart estimate (Lemma 5.2)
  have key : ∀ y ∈ V, ∀ v : Bd.oneFiber y,
      ‖(c ((v : P ⁻¹' {y}) : Y)).2‖ ≤ κ * (A * N (Bd.toOne v)) := by
    intro y hy v
    have hPy : P (Bd.oneVal (Bd.toOne v)) ∈ V := by
      have e : P (Bd.oneVal (Bd.toOne v)) = y := (v : P ⁻¹' {y}).2
      rw [e]; exact hy
    have hb := hbd (Bd.toOne v) hPy
    have hmem : (c ((v : P ⁻¹' {y}) : Y)).2 ∈ Set.range (c.F.toBase 1) :=
      v.2 c hc (hsrc (v : P ⁻¹' {y}) (hVc hy))
    have he : c.F.toBase 1 (c.liftOne ((v : P ⁻¹' {y}) : Y)).2 = (c ((v : P ⁻¹' {y}) : Y)).2 :=
      congrArg Prod.snd (c.toBase_liftOne hmem)
    rw [← he]
    exact ((c.F.toBase 1).le_opNorm _).trans (mul_le_mul_of_nonneg_left hb hκ0)
  -- the principal parts
  have hsecs := hs.1
  have hfx : ∀ y ∈ c.φ.source, (c (sectionAdd P f s y)).2 = (c (f y)).2 + (c (s y)).2 :=
    fun y hy => by rw [sectionAdd_apply hf hsecs]; exact c.snd_add hy _ _
  have hfreq : ∃ᶠ y in 𝓝 x, y ∈ solSet P (sectionAdd P f s) := mem_closure_iff_frequently.1 hx
  have hVev : ∀ᶠ y in 𝓝 x, y ∈ V := hVo.mem_nhds hxV
  have hcf : ContinuousAt (fun y => (c (f y)).2) x := by
    have h1 : ContinuousAt c (f x) := c.continuousOn_toFun.continuousAt
      ((c.isOpen_source Bd.continuous).mem_nhds (c.mem_source_of_proj (by rw [hf x]; exact hxc)))
    exact continuous_snd.continuousAt.comp (h1.comp hfc.continuousAt)
  -- the estimate at `x`
  have hest : ∀ ε > 0, ‖(c (f x)).2 + (c (s x)).2‖ ≤ 2 * (κ * (A * ε)) := by
    intro ε hε
    obtain ⟨s', hs', hd⟩ := hs.2.2 ε hε
    have hs'sec := hs'.1.1
    have hdiff : ∀ y ∈ V, ‖(c (s y)).2 - (c (s' y)).2‖ ≤ κ * (A * ε) := by
      intro y hy
      have h1 := key y hy (vecOf Bd hsecs hs.2.1 y - vecOf Bd hs'sec hs'.1.mem_oneSet y)
      have h2 := hd y
      rw [fibDist_eq' N hsecs hs.2.1 hs'sec hs'.1.mem_oneSet] at h2
      have h3 : (c (((vecOf Bd hsecs hs.2.1 y - vecOf Bd hs'sec hs'.1.mem_oneSet y :
          Bd.oneFiber y) : P ⁻¹' {y}) : Y)).2 = (c (s y)).2 - (c (s' y)).2 :=
        c.snd_sub (hVc hy) _ _
      rw [h3] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hA.le) hκ0)
    have hcs' : ContinuousAt (fun y => (c (s' y)).2) x := by
      have h0 := (hs'.1.continuousOn_source hcB).continuousAt (c.φ.isOpen_source.mem_nhds hxc)
      have h1 : ContinuousAt c (s' x) := c.continuousOn_toFun.continuousAt
        ((c.isOpen_source Bd.continuous).mem_nhds
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

/-- The project's completion is B's. -/
theorem inCompletion_of {Bd : StrongBundle PX P} {N : Bd.One → ℝ} {U : Set X} {s : X → Y}
    (hs : Bd.IsInAllowableCompletion N U s) : InCompletion Bd N U s := by
  refine ⟨hs.isSection, hs.mem_oneSet, fun ε hε => ?_⟩
  obtain ⟨s', hs', hd⟩ := hs.approx ε hε
  refine ⟨s', ⟨hs'.1, hs'.2.1, fun x => ⟨hs'.1.mem_oneSet x, hs'.2.2 x _⟩⟩, fun x => ?_⟩
  rw [fibDist_eq' N hs.isSection hs.mem_oneSet hs'.1.1 hs'.1.mem_oneSet]
  exact hd x

end Glue

/-- `A ⇒ B`: A's first conjunct (Remark 5.12) gives the inclusion into
`{x ∈ U | N(f(x)) ≤ 1}` and the compactness of the closure; the completion supplies A's
hypotheses on `s` (`vanish_off`, `auxLe_one`), and `isClosed_solSet` the closedness. -/
theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f N U hf _hS hN hU s hs
  obtain ⟨_hUo, hSU, hK⟩ := hU
  have hfsec : IsSection P f := hf.isScSmooth.1
  have hfc : Continuous f := continuousOn_univ.1 hf.isScSmooth.2.continuousOn
  obtain ⟨-, hcl⟩ := hA.1 hN hfsec hSU hK hs.1 (fun x hx => vanish_off hN hs hx)
    (fun x => auxLe_one hN hs x)
  have hclosed := isClosed_solSet hN hfc hfsec hs
  have : closure (solutionSet P (sectionAdd P f s)) = solSet P (sectionAdd P f s) :=
    hclosed.closure_eq
  rw [this] at hcl
  exact hcl

/-- B gives A's last conjunct, with Theorem 5.5 (`theorem_5_5`, another item's theorem) for the
existence of an adapted `U`. -/
theorem B_gives_of_isScFredholmSection (hB : B) :
    type_of% @Polyfold.remark_5_12_of_isScFredholmSection.{0, 0} := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f hf hS N hN
  obtain ⟨U, hUo, hSU, hK⟩ := (theorem_5_5 hf hS).2 N hN
  exact ⟨U, hUo, hSU, hK, fun s hs =>
    hB PX P Bd f N U hf hS hN ⟨hUo, hSU, hK⟩ s (inCompletion_of hs)⟩

/-! `B ⇒ A` is not proved: `remark_5_12`, `auxLe_of_sectionAdd`, `isClosed_solutionSet_sectionAdd`
and `remark_5_12_completion` are statements about ARBITRARY sections `f`, `s` (`f` only a
continuous section, no sc-Fredholm property, no compactness of `S_f`; in `remark_5_12` `s` any
section vanishing off `U` with `N(s) ≤ 1`), and `auxLe_of_sectionAdd` is a pointwise fibre lemma;
B only speaks of sc-Fredholm `f` with compact `S_f`.  Their content is elementary or the chart
argument above, but it does not follow from B. -/

#rt_check RoundTrip.V5_22.A_to_B [Polyfold.remark_5_12,
  Polyfold.StrongBundle.IsAuxNorm.auxLe_of_sectionAdd,
  Polyfold.StrongBundle.IsInAllowableCompletion.isClosed_solutionSet_sectionAdd,
  Polyfold.remark_5_12_completion, Polyfold.remark_5_12_of_isScFredholmSection]
#rt_check RoundTrip.V5_22.B_gives_of_isScFredholmSection [Polyfold.remark_5_12,
  Polyfold.StrongBundle.IsAuxNorm.auxLe_of_sectionAdd,
  Polyfold.StrongBundle.IsInAllowableCompletion.isClosed_solutionSet_sectionAdd,
  Polyfold.remark_5_12_completion, Polyfold.remark_5_12_of_isScFredholmSection]
#rt_overlap RoundTrip.V5_22.B_gives_of_isScFredholmSection [Polyfold.remark_5_12,
  Polyfold.StrongBundle.IsAuxNorm.auxLe_of_sectionAdd,
  Polyfold.StrongBundle.IsInAllowableCompletion.isClosed_solutionSet_sectionAdd,
  Polyfold.remark_5_12_completion, Polyfold.remark_5_12_of_isScFredholmSection]

end RoundTrip.V5_22
