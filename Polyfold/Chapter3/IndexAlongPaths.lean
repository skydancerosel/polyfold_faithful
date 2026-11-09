import Polyfold.Chapter3.IndexLocallyConstantG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.1,
**Definition 6.2.1 (preprint 6.1)** (the index of an sc-Fredholm germ `(f, x)` at a smooth point which need not be
a zero) and **Proposition 6.2.2 (preprint 6.2)** (stability of `ind(f, x)` along sc-smooth paths, p. 201–203),
in the text's germ reading of Definition 3.1.11 (preprint 3.11) (round-trip item V3.98 (a); Findings, Chapter 3,
items 340–349).

# The index at non-zeros and along paths

## The text, paraphrased

(§6.1) At a smooth point `x` with `f(x) ≠ 0` there is no intrinsic linearization, but in a strong
bundle `P : Y → X` one takes a local sc⁺-section `s` with `s(x) = f(x)` (in a chart,
`s(y) = R(y, f(x))`) and linearizes `f − s` at its zero `x`.  Two such `s, t` give
`(f − s)'(x) = (f − t)'(x) + (t − s)'(x)` with `(t − s)'(x)` an sc⁺-operator, so the Fredholm
property and the index do not depend on `s` (Proposition 1.1.11 (preprint 1.10)).  (Definition 6.2.1 (preprint 6.1)) `Lin(f, x)` is
the set of all `(f − s)'(x) + a`, `a` an sc⁺-operator, and `ind(f, x) := ind (f − s)'(x)`.
(Proposition 6.2.2 (preprint 6.2)) For a tame M-polyfold `X`, an sc-Fredholm section `f` and smooth points
`x₀, x₁` joined by an sc-smooth path `φ : [0, 1] → X`, `ind(f, x₀) = ind(f, x₁)`.  *Proof.* Fix
`t₀`; choose a locally defined sc⁺-section `s(t, x)` of the pull-back to `[0, 1] × X` with
`s(t, φ(t)) = f(φ(t))` near `t₀` ("we do not need a sc-smooth partition of unity"); add finitely
many sc⁺-sections `sᵢ(t, x)` with parameters `λ` so that `F(λ, t, x) = f(x) − s(t, x) + Σ λᵢ sᵢ`
has a surjective linearization in good position at `(0, t₀, φ(t₀))`; the implicit function theorem
gives a solution manifold `S ∋ (0, t, φ(t))`, `t` near `t₀`, with `ker F' = TS` and `F'` onto along
it, so `t ↦ dim T_{(0,t,φ(t))}S = ind(F, (0, t, φ(t))) = ind(f, φ(t)) + m + p` is locally
constant.

## What is formalized

* `Polyfold.StrongBundle.IsIndexAt B f x i` (**Definition 6.2.1 (preprint 6.1)**): there is an sc⁺-section `s`
  with `f + s` vanishing at `x` and `(f + s)'(x)` Fredholm of index `i` in every chart
  (`IsLinOfIndex`; the text's `f − s` with `s(x) = f(x)` is `f + (−s)`).
* `Polyfold.StrongBundle.IsLinOfIndex.unique`: at a zero of an sc-Fredholm section the index of
  `IsLinOfIndex` is unique (the linearization is Fredholm, so the definition is not vacuous).
* `Polyfold.StrongBundle.isLinOfIndex_sectionAdd_of_isZeroAt` (**the "same index" of Definition
  6.1**): at a zero `x` of the sc-Fredholm section `f`, adding an sc⁺-section vanishing at `x`
  does not change the index — not through the compactness of `(t − s)'(x)` as in the text, but
  through Theorem 3.1.18 (preprint 3.15): `f + s` has germ data in the same chart with the same conjugation to a
  basic germ (`sectionAdd_chartData_germ`), so both indices are `dim Pn − dim Q`
  (`ConjugationData.congr` of `BasicGermShrink.lean`).
* `Polyfold.StrongBundle.IsIndexAt.unique` (**Definition 6.2.1 (preprint 6.1) is well defined**),
  `isIndexAt_of_isZeroAt`, `IsIndexAt.isLinOfIndex_of_isZeroAt` (at a zero, `ind(f, x)` is the
  index of `f'(x)`), `StrongBundle.exists_isIndexAt` (**with bump functions, `ind(f, x)` exists
  at every smooth point**: Lemma 5.3.3 (preprint 5.11) through `f(x)` and Theorem 3.1.18 (preprint 3.15)).
* `Polyfold.isIndexAt_locally_constant_of_isZeroAt_sectionAdd`: **`ind(f, y)` is constant along
  the zero set of `f + s` near a zero**, for `f` with tame germ data on an M-polyfold admitting
  bump functions and any sc⁺-section `s` (Theorem 3.1.18 (preprint 3.15) and the local constancy along the zero
  set, `index_locally_constant_of_admitsBumpFunctions`).
* `Polyfold.isIndexAt_eventually_const_of_path`: **the local form of Proposition 6.2.2 (preprint 6.2) along a
  continuous path**: if an sc⁺-section `s` makes `f + s` vanish along `φ` near `t₀`, then
  `t ↦ ind(f, φ(t))` is constant near `t₀`; `Polyfold.isIndexAt_const_of_forall_eventually` and
  `Polyfold.isIndexAt_const_of_path`: on a preconnected parameter space a locally constant index
  is constant, so if every `t` has such an `s`, then `ind(f, φ(t))` is constant.
* `Polyfold.MPolyfold.admitsBumpFunctions_prod_rn`: **`ℝⁿ × X` admits sc-smooth bump functions
  when `X` does** (products `β₁(r) β₂(x)` of a `C^∞` bump and a bump of `X`).
* `Polyfold.isLinOfIndex_paramLift_sectionAdd_eventually_const`: **the text's device on
  `ℝ × X`**: for an sc⁺-section `s̃` of the pull-back `π*P` with `f̃ + s̃` vanishing along the
  graph `t ↦ (t, φ(t))` near `t₀` (`f̃ = f ∘ π`, Theorem 3.1.21 (preprint 3.18)), the index of `(f̃ + s̃)'(t, φ(t))`
  is constant near `t₀`; `Polyfold.proposition_6_2_2_of_sections_of_slice`: **Proposition 6.2.2 (preprint 6.2)
  follows from the two steps (E), (S) below**, stated as hypotheses.

## What the text leaves implicit, and the choices made

* **Definition 6.2.1 (preprint 6.1) with global sc⁺-sections.**  The text's `s` is defined near `x`; here `s` is an
  sc⁺-section of `P` on all of `X` (`IsScPlusSection`).  With bump functions the two readings
  agree (Lemma 5.3.3 (preprint 5.11) cuts a local section off); without them the formal definition is a priori
  stronger.  `IsIndexAt` is stated existentially; `IsIndexAt.unique` makes it a function of `(f, x)`
  on the smooth points where some `s` exists.
* **"Same index" without compact operators.**  The text invokes Proposition 1.1.11 (preprint 1.10) (sc⁺-operators
  are level-wise compact) for the independence of `s`.  The project has no "`Lin(z)` of an
  sc⁺-section is compact" lemma; the independence is proved from the germ data instead (Theorem
  3.15 keeps the chart and the basic germ), which is the same fact one level down.
* **Proposition 6.2.2 (preprint 6.2) along paths: the reduction.**  Of the text's proof, the stabilization by
  finitely many sections, the implicit function theorem and the index count are the local
  constancy along the zero set (`index_locally_constant_of_admitsBumpFunctions`, applied here on
  `ℝ × X` with bump functions from `admitsBumpFunctions_prod_rn`).  Two steps are stated as
  hypotheses of `proposition_6_2_2_of_sections_of_slice`: (E) the sc⁺-section
  `s̃(t, x) = −R(x, f(φ(t)))` of `π*P` with `f̃ + s̃ = 0` along the graph of the path (its
  sc⁺-smoothness needs that `t ↦ Φ(f(φ(t)))₂` is sc-smooth into `F¹`, a curve of smooth points
  from the constant sc-structure of `ℝ`, and the `[1]`-sc-smoothness of the bundle retraction;
  the cut-off is `isScPlusSection_cutoffSection` in the product chart); (S) the slice relation
  `ind (f̃ + s̃)'(t, φ(t)) = ind (f + s̃(t, ·))'(φ(t)) + 1`, the analogue of
  `isLinOfIndex_of_paramSection_isLinOfIndex` for a `t`-dependent section
  (`fredholmIndex_eq_of_param` with `k = 1`).  Given (E) and (S),
  `isLinOfIndex_paramLift_sectionAdd_eventually_const` and `isIndexAt_const_of_path` give
  Proposition 6.2.2 (preprint 6.2) for every sc-smooth path on a preconnected parameter set.  **Both steps are
  proved in `IndexAlongPathsDevice.lean`** (`exists_isScPlusSection_pullback_of_path`,
  `StrongBundle.isIndexAt_of_pullback_isLinOfIndex`), which states `proposition_6_2_2`.  The
  tameness of `X` enters through the tame germ data (Definition 3.6.4 (preprint 3.51)), the bump functions through
  Lemma 5.3.3 (preprint 5.11) for the stabilizing sections and the cut-off of the section along the path (the text
  uses locally defined sections and no bump functions).
-/

open Set Filter Topology Function Module ContinuousLinearMap
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### Fibrewise algebra of sections -/

section SectionAlgebra

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {f s : X → Y} {x : X}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- A zero of `f` is the zero of the fibre. -/
lemma IsZeroAt.mk_eq_zero (hf : IsSection P f) (hx : IsZeroAt P f x) :
    (⟨f x, hf x⟩ : P ⁻¹' {x}) = 0 := Subtype.ext hx

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `f + s` vanishes at `x` if `f` and `s` do. -/
lemma IsZeroAt.sectionAdd (hf : IsSection P f) (hs : IsSection P s) (hx : IsZeroAt P f x)
    (hsx : IsZeroAt P s x) : IsZeroAt P (sectionAdd P f s) x := by
  unfold IsZeroAt
  rw [sectionAdd_apply hf hs, hx.mk_eq_zero hf, hsx.mk_eq_zero hs, add_zero]
  rfl

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `0 + s = s`. -/
lemma fiberZero_sectionAdd (hs : IsSection P s) : sectionAdd P (fiberZero P) s = s := by
  funext x
  rw [sectionAdd_apply isSection_fiberZero hs]
  have : (⟨fiberZero P x, isSection_fiberZero x⟩ : P ⁻¹' {x}) = 0 := rfl
  rw [this, zero_add]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- If `f` and `f + s` vanish at `x`, so does `s`. -/
lemma isZeroAt_of_isZeroAt_sectionAdd (hf : IsSection P f) (hs : IsSection P s)
    (hx : IsZeroAt P f x) (h : IsZeroAt P (sectionAdd P f s) x) : IsZeroAt P s x := by
  have e := h.mk_eq_zero (hf.sectionAdd hs)
  have hA : (⟨sectionAdd P f s x, (hf.sectionAdd hs) x⟩ : P ⁻¹' {x}) =
      ⟨f x, hf x⟩ + ⟨s x, hs x⟩ := Subtype.ext (sectionAdd_apply hf hs x)
  rw [hA, hx.mk_eq_zero hf, zero_add] at e
  exact congrArg Subtype.val e

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `a·s` vanishes where `s` does. -/
lemma IsZeroAt.sectionSmul (hs : IsSection P s) (hsx : IsZeroAt P s x) (a : X → ℝ) :
    IsZeroAt P (sectionSmul P a s) x := by
  unfold IsZeroAt
  rw [sectionSmul_apply hs, hsx.mk_eq_zero hs, smul_zero]
  rfl

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- The difference `s' − s` of two sections, as `s' + (−1)·s`. -/
def sectionDiff (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (s' s : X → Y) : X → Y :=
  sectionAdd P s' (sectionSmul P (fun _ => (-1 : ℝ)) s)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
lemma IsSection.sectionDiff {s' : X → Y} (hs' : IsSection P s') (hs : IsSection P s) :
    IsSection P (sectionDiff P s' s) :=
  hs'.sectionAdd hs.sectionSmul

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
lemma sectionDiff_mk {s' : X → Y} (hs' : IsSection P s') (hs : IsSection P s) (x : X) :
    (⟨sectionDiff P s' s x, (hs'.sectionDiff hs) x⟩ : P ⁻¹' {x}) =
      ⟨s' x, hs' x⟩ - ⟨s x, hs x⟩ := by
  refine Subtype.ext ?_
  change sectionDiff P s' s x = _
  unfold sectionDiff
  rw [sectionAdd_apply hs' hs.sectionSmul]
  have h1 : (⟨sectionSmul P (fun _ => (-1 : ℝ)) s x, hs.sectionSmul x⟩ : P ⁻¹' {x}) =
      (-1 : ℝ) • ⟨s x, hs x⟩ := Subtype.ext (sectionSmul_apply (f := fun _ => (-1 : ℝ)) hs x)
  rw [h1, neg_one_smul, sub_eq_add_neg]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `(f + s) + (s' − s) = f + s'`. -/
lemma sectionAdd_sectionAdd_sectionDiff {s' : X → Y} (hf : IsSection P f) (hs : IsSection P s)
    (hs' : IsSection P s') :
    sectionAdd P (sectionAdd P f s) (sectionDiff P s' s) = sectionAdd P f s' := by
  funext x
  rw [sectionAdd_apply (hf.sectionAdd hs) (hs'.sectionDiff hs), sectionAdd_apply hf hs']
  congr 1
  have hA : (⟨sectionAdd P f s x, (hf.sectionAdd hs) x⟩ : P ⁻¹' {x}) =
      ⟨f x, hf x⟩ + ⟨s x, hs x⟩ := Subtype.ext (sectionAdd_apply hf hs x)
  rw [hA, sectionDiff_mk hs' hs]
  abel

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- If `f + s` and `f + s'` vanish at `x`, then `s' − s` vanishes at `x`. -/
lemma isZeroAt_sectionDiff_of_isZeroAt_sectionAdd {s' : X → Y} (hf : IsSection P f)
    (hs : IsSection P s) (hs' : IsSection P s') (h : IsZeroAt P (sectionAdd P f s) x)
    (h' : IsZeroAt P (sectionAdd P f s') x) : IsZeroAt P (sectionDiff P s' s) x := by
  have e : (⟨sectionAdd P f s x, (hf.sectionAdd hs) x⟩ : P ⁻¹' {x}) =
      ⟨f x, hf x⟩ + ⟨s x, hs x⟩ := Subtype.ext (sectionAdd_apply hf hs x)
  have e' : (⟨sectionAdd P f s' x, (hf.sectionAdd hs') x⟩ : P ⁻¹' {x}) =
      ⟨f x, hf x⟩ + ⟨s' x, hs' x⟩ := Subtype.ext (sectionAdd_apply hf hs' x)
  have h0 := h.mk_eq_zero (hf.sectionAdd hs)
  have h0' := h'.mk_eq_zero (hf.sectionAdd hs')
  rw [e] at h0
  rw [e'] at h0'
  have : (⟨sectionDiff P s' s x, (hs'.sectionDiff hs) x⟩ : P ⁻¹' {x}) = 0 := by
    rw [sectionDiff_mk hs' hs]
    calc (⟨s' x, hs' x⟩ : P ⁻¹' {x}) - ⟨s x, hs x⟩ =
        (⟨f x, hf x⟩ + ⟨s' x, hs' x⟩) - (⟨f x, hf x⟩ + ⟨s x, hs x⟩) := by abel
      _ = 0 := by rw [h0, h0', sub_zero]
  exact congrArg Subtype.val this

end SectionAlgebra

/-! ### Definition 6.2.1 (preprint 6.1): the index of `(f, x)` at a smooth point -/

section IndexAt

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f s : X → Y}

open StrongRetr

variable (B) in
/-- **Definition 6.2.1 (preprint 6.1)**: the sc-Fredholm germ `(f, x)` has **index `i`** if there is an sc⁺-section
`s` of `P` with `f + s` vanishing at `x` (the text's `f − s` with `s(x) = f(x)`) such that
`(f + s)'(x)` is Fredholm of index `i` in every strong bundle chart (`IsLinOfIndex`).  By
`IsIndexAt.unique` the index does not depend on `s`. -/
def StrongBundle.IsIndexAt (f : X → Y) (x : X) (i : ℤ) : Prop :=
  ∃ s : X → Y, B.IsScPlusSection s ∧ IsZeroAt P (sectionAdd P f s) x ∧
    B.IsLinOfIndex (sectionAdd P f s) x i

/-- **The index of `IsLinOfIndex` is unique at a zero of an sc-Fredholm section**: in any chart
around the zero, `Lin(z) : T_zO → K_z` is a bounded operator (`linAt_isScFredholm`), so the two
quantifications of `IsLinOfIndex` are not vacuous and the indices agree. -/
theorem StrongBundle.IsLinOfIndex.unique (hf : B.IsScFredholmSection f) {x : X}
    (hx : IsZeroAt P f x) {i j : ℤ} (hi : B.IsLinOfIndex f x i) (hj : B.IsLinOfIndex f x j) :
    i = j := by
  obtain ⟨c, hc, hxV⟩ := exists_chart_mem B x
  have hc' := B.isChart_of_mem hc
  have hxs : x ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx
  obtain ⟨z, hz⟩ := (PX.mem_levelSet_iff c.isChart hxV).1 (mem_iInter.1 hxs 1)
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := by
    rw [hz]
    exact StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ c.φ.mapsTo_model x hxV)
  obtain ⟨hD, hT, hK, hTK, -, -, -⟩ := StrongBundle.linAt_isScFredholm hf hx hc' hxV hz hzU
  have hmem : ∀ v : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z v ∈ rangeS (ρCLM c.isRetraction hzU) := fun v => by
    have := hTK v v.2
    rwa [hD.toScOperator_zero] at this
  have h1 := hi c hc' hxV z hz hzU ((linAt c.U c.R (c.principal f) z).codRestrict _ hmem)
    fun _ => rfl
  have h2 := hj c hc' hxV z hz hzU ((linAt c.U c.R (c.principal f) z).codRestrict _ hmem)
    fun _ => rfl
  exact h1.2.symm.trans h2.2

/-- **Adding an sc⁺-section vanishing at a zero does not change the index** (the "same Fredholm
index" of Definition 6.2.1 (preprint 6.1) and of the paragraph before it, at a zero): for an sc-Fredholm section `f`
with `f(x) = 0` and an sc⁺-section `s` with `s(x) = 0`, `IsLinOfIndex f x i` gives
`IsLinOfIndex (f + s) x i`.  Proof: the germ datum of `f` at `x` (chart `c`, filling germ `g`,
sc⁺-germ `t₀`, conjugation data `dc`) gives the index `dim Pn − dim Q` of `f'(x)`
(`isLinOfIndex_of_conjugationData`), so `i = dim Pn − dim Q` (`IsLinOfIndex.unique`); Theorem
3.15 gives germ data of `f + s` in the same chart with `(g + ŝ ∘ r) − (ŝ₁ ∘ r + t₀) = g − t₀`
(`sectionAdd_chartData_germ`), whose conjugation data are `dc` up to the values on `U`
(`ConjugationData.congr`), so `(f + s)'(x)` has the same index.  The text argues with the
compactness of `(t − s)'(x)`; the germ data give it without compact operators. -/
theorem StrongBundle.isLinOfIndex_sectionAdd_of_isZeroAt (hf : B.IsScFredholmSection f)
    (hs : B.IsScPlusSection s) {x : X} (hx : IsZeroAt P f x) (hsx : IsZeroAt P s x) {i : ℤ}
    (hi : B.IsLinOfIndex f x i) : B.IsLinOfIndex (sectionAdd P f s) x i := by
  have hfs : IsSection P f := hf.isScSmooth.1
  have hxs : x ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj⟩ := hf.germ x hxs
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  have hidx := StrongBundle.isLinOfIndex_of_conjugationData hf.isScSmooth hx hc hxV hφ0 h0U
    hfill ht₀ ht₀0 dc
  have hi' : i = finrank ℝ dc.Pn - finrank ℝ dc.Q := hi.unique hf hx hidx
  obtain ⟨h1, h2, h3, -⟩ :=
    StrongBundle.sectionAdd_chartData_germ hfs hs hc h0U hfill ht₀ ht₀0 hconj
  have hx' : IsZeroAt P (sectionAdd P f s) x := hx.sectionAdd hfs hs.1 hsx
  have hfs' := theorem_3_1_18_preprint hf hs
  -- the same conjugation data, for the new filling and sc⁺-germ
  set dc' := dc.congr (k' := fun u => (g u + c.principal s (StrongRetr.r c.R u)) -
      c.F.toBase 1 (c.principalLift s (StrongRetr.r c.R u) + t₀ u))
    (Eventually.of_forall fun u hu => by
      simp only [map_add]
      rw [hs.toBase_principalLift hc (c.r_mem_O hu)]
      abel)
  have hidx' := StrongBundle.isLinOfIndex_of_conjugationData hfs'.isScSmooth hx' hc hxV hφ0 h0U
    h1 h2 h3 dc'
  rw [hi']
  exact hidx'

/-- **Definition 6.2.1 (preprint 6.1) is well defined**: at a smooth point `x` of an sc-Fredholm section `f`, two
sc⁺-sections `s, s'` with `f + s`, `f + s'` vanishing at `x` give the same index: `s' − s` is an
sc⁺-section vanishing at `x` (`IsScPlusSection.add`, `IsScPlusSection.smul_left`),
`(f + s) + (s' − s) = f + s'`, and `isLinOfIndex_sectionAdd_of_isZeroAt` at the zero `x` of the
sc-Fredholm section `f + s` (Theorem 3.1.18 (preprint 3.15)). -/
theorem StrongBundle.IsIndexAt.unique (hf : B.IsScFredholmSection f) {x : X} {i j : ℤ}
    (hi : B.IsIndexAt f x i) (hj : B.IsIndexAt f x j) : i = j := by
  obtain ⟨s, hs, hsx, hLi⟩ := hi
  obtain ⟨s', hs', hs'x, hLj⟩ := hj
  have hfs : IsSection P f := hf.isScSmooth.1
  have hd : B.IsScPlusSection (sectionDiff P s' s) :=
    hs'.add (hs.smul_left (isScSmoothMap_real_const (-1)))
  have hdx : IsZeroAt P (sectionDiff P s' s) x :=
    isZeroAt_sectionDiff_of_isZeroAt_sectionAdd hfs hs.1 hs'.1 hsx hs'x
  have h := StrongBundle.isLinOfIndex_sectionAdd_of_isZeroAt (theorem_3_1_18_preprint hf hs) hd hsx hdx hLi
  rw [sectionAdd_sectionAdd_sectionDiff hfs hs.1 hs'.1] at h
  exact h.unique (theorem_3_1_18_preprint hf hs') hs'x hLj

/-- At a zero, the index of `f'(x)` is the index of the germ (`s = 0`). -/
theorem StrongBundle.isIndexAt_of_isZeroAt (hf : IsSection P f) {x : X} (hx : IsZeroAt P f x)
    {i : ℤ} (hi : B.IsLinOfIndex f x i) : B.IsIndexAt f x i :=
  ⟨fiberZero P, StrongBundle.isScPlusSection_fiberZero, by rwa [sectionAdd_fiberZero hf],
    by rwa [sectionAdd_fiberZero hf]⟩

/-- At a zero of an sc-Fredholm section, the index of the germ is the index of `f'(x)`. -/
theorem StrongBundle.IsIndexAt.isLinOfIndex_of_isZeroAt (hf : B.IsScFredholmSection f) {x : X}
    (hx : IsZeroAt P f x) {i : ℤ} (hi : B.IsIndexAt f x i) : B.IsLinOfIndex f x i := by
  obtain ⟨s, hs, hsx, hL⟩ := hi
  have hfs : IsSection P f := hf.isScSmooth.1
  have hs0 : IsZeroAt P s x := isZeroAt_of_isZeroAt_sectionAdd hfs hs.1 hx hsx
  have h := StrongBundle.isLinOfIndex_sectionAdd_of_isZeroAt (theorem_3_1_18_preprint hf hs)
    (hs.smul_left (isScSmoothMap_real_const (-1))) hsx (hs0.sectionSmul hs.1 _) hL
  have e : sectionAdd P (sectionAdd P f s) (sectionSmul P (fun _ => (-1 : ℝ)) s) = f := by
    have := sectionAdd_sectionAdd_sectionDiff hfs hs.1 isSection_fiberZero
    unfold sectionDiff at this
    rwa [fiberZero_sectionAdd hs.1.sectionSmul, sectionAdd_fiberZero hfs] at this
  rwa [e] at h

/-- **Definition 6.2.1 (preprint 6.1) is total on smooth points when `X` admits bump functions**: for an
sc-Fredholm section `f` and a smooth point `x`, there is an sc⁺-section `s` with
`(f + s)(x) = 0` (Lemma 5.3.3 (preprint 5.11) through the smooth point `f(x)`, negated), and `(f + s)'(x)` is
Fredholm (Theorem 3.1.18 (preprint 3.15) and Proposition 3.6.5 (preprint 3.52) for the germ data of `f + s` at `x`), so `ind(f, x)`
exists. -/
theorem StrongBundle.exists_isIndexAt (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSection f) {x : X} (hx : x ∈ PX.smoothSet) :
    ∃ i : ℤ, B.IsIndexAt f x i := by
  obtain ⟨N, hN⟩ := proposition_5_1_3_exists (B := B)
  have hfs : IsSection P f := hf.isScSmooth.1
  have he : f x ∈ B.toMPolyfold0.smoothSet :=
    mem_iInter.2 fun m => hf.isScSmooth.2.mapsTo_levelSet m (mem_iInter.1 hx m)
  obtain ⟨-, s₀, hs₀, hs₀x, -, -⟩ :=
    lemma_5_3_3 hbump hN hx he (hfs x) one_pos isOpen_univ (mem_univ x)
  set s := sectionSmul P (fun _ => (-1 : ℝ)) s₀ with hsdef
  have hs : B.IsScPlusSection s := hs₀.smul_left (isScSmoothMap_real_const (-1))
  have hzero : IsZeroAt P (sectionAdd P f s) x := by
    unfold IsZeroAt
    rw [sectionAdd_apply hfs hs.1]
    have h1 : (⟨s x, hs.1 x⟩ : P ⁻¹' {x}) = (-1 : ℝ) • ⟨s₀ x, hs₀.1 x⟩ :=
      Subtype.ext (sectionSmul_apply (f := fun _ => (-1 : ℝ)) hs₀.1 x)
    have h2 : (⟨s₀ x, hs₀.1 x⟩ : P ⁻¹' {x}) = ⟨f x, hfs x⟩ := Subtype.ext hs₀x
    rw [h1, h2, neg_one_smul, add_neg_cancel]
    rfl
  have hF := theorem_3_1_18_preprint hf hs
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj⟩ := hF.germ x hx
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  exact ⟨_, s, hs, hzero, StrongBundle.isLinOfIndex_of_conjugationData hF.isScSmooth hzero hc
    hxV hφ0 h0U hfill ht₀ ht₀0 dc⟩

/-! ### The index along the zero set of `f + s`, and along paths -/

/-- **The index of the germ is locally constant along the zero set of `f + s`**: let `X` admit
sc-smooth bump functions, `f` be an sc-Fredholm section with tame germ data and `s` an
sc⁺-section with `(f + s)(x₀) = 0`.  Then there are an open `V ∋ x₀` and `i ∈ ℤ` with
`ind(f, y) = i` (Definition 6.2.1 (preprint 6.1)) at every zero `y ∈ V` of `f + s`.  (`theorem_3_1_18_tame` and
`index_locally_constant_of_admitsBumpFunctions` for `f + s`.) -/
theorem isIndexAt_locally_constant_of_isZeroAt_sectionAdd (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (hs : B.IsScPlusSection s) {x₀ : X}
    (hx₀ : IsZeroAt P (sectionAdd P f s) x₀) :
    ∃ (V : Set X) (i : ℤ), IsOpen V ∧ x₀ ∈ V ∧
      ∀ y ∈ V, IsZeroAt P (sectionAdd P f s) y → B.IsIndexAt f y i := by
  obtain ⟨V, i, hVo, hxV, hall⟩ :=
    index_locally_constant_of_admitsBumpFunctions hbump (theorem_3_1_18_tame hf hs) hx₀
  exact ⟨V, i, hVo, hxV, fun y hy hy0 => ⟨s, hs, hy0, hall y hy hy0⟩⟩

/-- **The local form of Proposition 6.2.2 (preprint 6.2) along a continuous path**: if an sc⁺-section `s` makes
`f + s` vanish along `φ` near `t₀`, then `t ↦ ind(f, φ(t))` is constant near `t₀`.  (The text
obtains such an `s`, depending on `t`, on `[0, 1] × X`; see the module docstring.) -/
theorem isIndexAt_eventually_const_of_path (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (hs : B.IsScPlusSection s) {T : Type*}
    [TopologicalSpace T] {φ : T → X} {t₀ : T} (hφ : ContinuousAt φ t₀)
    (hz : ∀ᶠ t in 𝓝 t₀, IsZeroAt P (sectionAdd P f s) (φ t)) :
    ∃ i : ℤ, ∀ᶠ t in 𝓝 t₀, B.IsIndexAt f (φ t) i := by
  obtain ⟨V, i, hVo, hxV, hall⟩ :=
    isIndexAt_locally_constant_of_isZeroAt_sectionAdd hbump hf hs hz.self_of_nhds
  refine ⟨i, ?_⟩
  filter_upwards [hz, hφ.preimage_mem_nhds (hVo.mem_nhds hxV)] with t ht htV
  exact hall _ htV ht

/-- **A locally constant index along a map from a preconnected space is constant**: if every
`t` has a neighbourhood on which `ind(f, φ(t'))` is one integer, then one integer serves for all
`t` (`IsIndexAt.unique` makes the index a locally constant function;
`IsLocallyConstant.apply_eq_of_isPreconnected`). -/
theorem isIndexAt_const_of_forall_eventually (hf : B.IsScFredholmSection f) {T : Type*}
    [TopologicalSpace T] [PreconnectedSpace T] {φ : T → X}
    (h : ∀ t, ∃ i : ℤ, ∀ᶠ t' in 𝓝 t, B.IsIndexAt f (φ t') i) :
    ∃ i : ℤ, ∀ t, B.IsIndexAt f (φ t) i := by
  classical
  choose ind hind using h
  have hlc : IsLocallyConstant ind := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    filter_upwards [hind t] with t' ht'
    exact ((hind t').self_of_nhds).unique hf ht'
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact ⟨0, fun t => (IsEmpty.false t).elim⟩
  refine ⟨ind t₀, fun t => ?_⟩
  rw [← hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ t) (mem_univ t₀)]
  exact (hind t).self_of_nhds

/-- **Proposition 6.2.2 (preprint 6.2) along a path, given the sections**: let `T` be a preconnected space and
`φ : T → X` continuous, and suppose that for every `t` there is an sc⁺-section `s_t` with
`f + s_t` vanishing along `φ` near `t`.  Then `ind(f, φ(t))` (Definition 6.2.1 (preprint 6.1)) is the same for all
`t` (`isIndexAt_eventually_const_of_path`, `isIndexAt_const_of_forall_eventually`). -/
theorem isIndexAt_const_of_path (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    {φ : T → X} (hφ : Continuous φ)
    (hs : ∀ t, ∃ s : X → Y, B.IsScPlusSection s ∧
      ∀ᶠ t' in 𝓝 t, IsZeroAt P (sectionAdd P f s) (φ t')) :
    ∃ i : ℤ, ∀ t, B.IsIndexAt f (φ t) i :=
  isIndexAt_const_of_forall_eventually hf.toIsScFredholmSection fun t => by
    obtain ⟨s, hs, hz⟩ := hs t
    exact isIndexAt_eventually_const_of_path hbump hf hs hφ.continuousAt hz

end IndexAt

/-! ### Bump functions on `ℝⁿ × X` -/

section ProdBump

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- A `C^∞` function `g : ℝⁿ → ℝ` is an sc-smooth function on the M-polyfold `ℝⁿ`
(`isScSmoothMap_real_of_contDiff` for the source `rnPolyfold n`). -/
theorem isScSmoothMap_rn_real_of_contDiff {n : ℕ} {g : (Fin n → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) :
    (rnPolyfold n).IsScSmoothMap realPolyfold g := by
  refine MPolyfold.isScSmoothMap_of_local fun x => ⟨rnChart n 0, realChart, univ,
    isChart_rnChart 0, isChart_realChart, isOpen_univ, mem_univ x, subset_univ _,
    mapsTo_univ _ _, ?_⟩
  rw [← rnChart_source 0, (rnChart n 0).image_source, rnChart_model_O]
  change IsScSmoothRetractMap (rnSc n) univ univ realSc univ univ (fun r => g (r + 0))
  exact isScSmoothRetractMap_const_of_contDiff (V := Fin n → ℝ) (V' := ℝ)
    (hg.comp (contDiff_id.add contDiff_const))

/-- **The product of two sc-smooth functions is sc-smooth** (the product rule `IsScSmooth.smul` in
every chart). -/
theorem MPolyfold.IsScSmoothMap.mul {a b : X → ℝ} (ha : PX.IsScSmoothMap realPolyfold a)
    (hb : PX.IsScSmoothMap realPolyfold b) : PX.IsScSmoothMap realPolyfold fun x => a x * b x := by
  refine isScSmoothMap_real_of_local fun x => ?_
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source x
  refine ⟨φ, φ.source, hφ, φ.isOpen_source, hx, subset_rfl, ?_⟩
  rw [φ.image_source]
  have h1 := ha.real_chart hφ
  have h2 := hb.real_chart hφ
  refine ⟨mapsTo_univ _ _, fun R hR => ?_⟩
  exact ((h1.comp_isScSmooth R hR).smul R.isScDomain (h2.comp_isScSmooth R hR)).congr
    R.isScDomain fun _ _ => rfl

/-- The support of `(r, x) ↦ β₁(r) β₂(x)` lies in `supp β₁ × supp β₂`. -/
lemma tsupport_prod_mul_subset {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W]
    (β₁ : Z → ℝ) (β₂ : W → ℝ) :
    tsupport (fun p : Z × W => β₁ p.1 * β₂ p.2) ⊆ tsupport β₁ ×ˢ tsupport β₂ := by
  rw [tsupport, tsupport, tsupport, ← closure_prod_eq]
  refine closure_mono fun p hp => ?_
  rw [mem_support] at hp
  exact ⟨left_ne_zero_of_mul hp, right_ne_zero_of_mul hp⟩

/-- **`ℝⁿ × X` admits sc-smooth bump functions when `X` does** (Definition 5.3.1 (preprint 5.9) for the product
M-polyfold of Theorem 3.1.21 (preprint 3.18)): around `(r, x)` in an open `U ⊇ U₁ × U₂`, the product `β₁(r') β₂(x')`
of a `C^∞` bump `β₁` on `ℝⁿ` supported in `U₁` and a bump `β₂` of `X` supported in `U₂`. -/
theorem MPolyfold.admitsBumpFunctions_prod_rn {n : ℕ} [ParacompactSpace ((Fin n → ℝ) × X)]
    (hbump : PX.AdmitsBumpFunctions) : ((rnPolyfold n).prod PX).AdmitsBumpFunctions := by
  rintro ⟨r, x⟩ U hU hxU
  obtain ⟨U₁, U₂, hU₁, hU₂, hr, hx, hsub⟩ := isOpen_prod_iff.1 hU r x hxU
  obtain ⟨β₂, hβ₂, hβ₂x, hβ₂s⟩ := hbump x U₂ hU₂ hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU₁ r hr
  let b : ContDiffBump r := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨fun p => b p.1 * β₂ p.2, ?_, ?_, ?_⟩
  · exact ((isScSmoothMap_rn_real_of_contDiff b.contDiff).comp
      (MPolyfold.isScSmoothMap_fst (rnPolyfold n) PX)).mul
      (hβ₂.comp (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX))
  · show b r * β₂ x ≠ 0
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)), one_mul]
    exact hβ₂x
  · refine (tsupport_prod_mul_subset _ _).trans ((prod_mono ?_ hβ₂s).trans hsub)
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by change ε / 2 < ε; linarith)).trans hball

end ProdBump

/-! ### The text's device on `ℝ × X` -/

section Device

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The text's device for Proposition 6.2.2 (preprint 6.2), on `ℝ × X`**: let `X` admit sc-smooth bump functions
and `f` be an sc-Fredholm section with tame germ data; let `f̃ = f ∘ π` be its pull-back to
`ℝ × X` (Theorem 3.1.21 (preprint 3.18), `paramLift`), `φ : ℝ → X` continuous at `t₀`, and `s̃` an sc⁺-section of
`π*P` with `f̃ + s̃` vanishing along the graph `t ↦ (t, φ(t))` near `t₀` (the text's
`s(t, x)` with `s(t, φ(t)) = f(φ(t))`).  Then the index of `(f̃ + s̃)'(t, φ(t))` is the same for
all `t` near `t₀`: `f̃ + s̃` is an sc-Fredholm section of `π*P` with tame germ data
(`IsScFredholmSectionTame.param`, `theorem_3_1_18_tame`), `ℝ × X` admits bump functions
(`admitsBumpFunctions_prod_rn`), and the index is locally constant along its zero set
(`index_locally_constant_of_admitsBumpFunctions`), which contains the graph near `t₀`.  What is
not formalized (module docstring): the construction of `s̃` and the slice relation
`ind (f̃ + s̃)'(t, φ(t)) = ind (f + s̃(t, ·))'(φ(t)) + 1`. -/
theorem isLinOfIndex_paramLift_sectionAdd_eventually_const
    [ParacompactSpace ((Fin 1 → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
    (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    {φ : (Fin 1 → ℝ) → X} {t₀ : Fin 1 → ℝ} (hφ : ContinuousAt φ t₀)
    (hz : ∀ᶠ t in 𝓝 t₀, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (t, φ t)) :
    ∃ i : ℤ, ∀ᶠ t in 𝓝 t₀, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (t, φ t) i := by
  obtain ⟨V, i, hVo, hxV, hall⟩ := index_locally_constant_of_admitsBumpFunctions
    (MPolyfold.admitsBumpFunctions_prod_rn hbump) (theorem_3_1_18_tame hf.param hS) hz.self_of_nhds
  refine ⟨i, ?_⟩
  filter_upwards [hz, (continuousAt_id.prodMk hφ).preimage_mem_nhds (hVo.mem_nhds hxV)]
    with t ht htV
  exact hall _ htV ht

/-- **Proposition 6.2.2 (preprint 6.2) from the two open steps (E) and (S)** (the precise reduction; module
docstring): let `X` admit bump functions, `f` have tame germ data, `φ : ℝ → X` be continuous, and
suppose (E) every `t₀` has an sc⁺-section `S` of `π*P` with `f̃ + S` vanishing along the graph of
`φ` near `t₀`, and (S) at a zero `(t, φ(t))` of `f̃ + S` the index `i` of `(f̃ + S)'(t, φ(t))` gives
`ind(f, φ(t)) = i − 1`.  Then `ind(f, φ(t))` is one integer for all `t`
(`isLinOfIndex_paramLift_sectionAdd_eventually_const`, `isIndexAt_const_of_forall_eventually`;
`ℝ` is preconnected).  For the text's sc-smooth path `φ : [0, 1] → X`, (E) is the text's
construction of `s(t, x)` and (S) its index count `ind(F, (0, t, φ(t))) = ind(f, φ(t)) + m + p`. -/
theorem proposition_6_2_2_of_sections_of_slice
    [ParacompactSpace ((Fin 1 → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
    (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
    {φ : (Fin 1 → ℝ) → X} (hφ : Continuous φ)
    (hE : ∀ t₀, ∃ S : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd,
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S ∧
      ∀ᶠ t in 𝓝 t₀, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (t, φ t))
    (hS : ∀ S : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd,
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S →
      ∀ (t : Fin 1 → ℝ) (i : ℤ),
        IsZeroAt (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (t, φ t) →
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
          (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (t, φ t) i →
        B.IsIndexAt f (φ t) (i - 1)) :
    ∃ i : ℤ, ∀ t, B.IsIndexAt f (φ t) i := by
  refine isIndexAt_const_of_forall_eventually hf.toIsScFredholmSection fun t₀ => ?_
  obtain ⟨S, hSp, hz⟩ := hE t₀
  obtain ⟨i, hi⟩ :=
    isLinOfIndex_paramLift_sectionAdd_eventually_const hbump hf hSp hφ.continuousAt hz
  refine ⟨i - 1, ?_⟩
  filter_upwards [hz, hi] with t ht hti
  exact hS S hSp t i ht hti

end Device

end Polyfold
