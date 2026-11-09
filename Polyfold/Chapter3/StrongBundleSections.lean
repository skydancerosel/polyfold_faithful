import Polyfold.Chapter2.StrongBundlePullback
import Polyfold.Chapter3.Filler
import Polyfold.Chapter3.LocalCompactness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
Definitions 3.1.3 (preprint 3.3) (sc-smooth section germs), 3.6 (filled versions), 3.11 (sc-Fredholm germs) and
3.14 (sc-Fredholm sections), with the section algebra of a strong bundle over an M-polyfold they
presuppose (the fibrewise sum of sections, principal parts in a strong bundle chart, the local
representatives of sc-smooth and sc⁺-sections in *any* compatible chart), and
**Theorem 3.1.18 (preprint 3.15)** (stability of sc-Fredholm sections under sc⁺-perturbations).

Since the switch of Definition 3.1.11 (preprint 3.11) to the text's germ reading (phase 2, 2026-11-01; Findings,
Chapter 3, items 330–339) the notions and the theorem of this file carry the suffix `WholeChart` /
`_wholeChart`: they are the project's original whole-chart reading, stricter than the text
(Findings, Chapter 3, items 220–221, 260–266); the text's germ reading is `IsScFredholmGerm`
(`GermFillingChart.lean`), `IsScFredholmSection` (`TameGermsG.lean`) and `theorem_3_1_18_preprint`
(`FredholmSectionsG.lean`) (phase 2, items 270–330).

# Sc-Fredholm sections of strong bundles

## The text, paraphrased

(Definition 3.1.3 (preprint 3.3)) An sc-smooth section germ `(f, x₀)` of `P : Y → X` is a continuous section
`f : V → P⁻¹(V)` near the smooth point `x₀` such that in a strong bundle chart
`(Φ, P⁻¹(V), K, U ◁ F)` with `φ(x₀) = 0` the principal part `f̂` of `Φ ∘ f ∘ φ⁻¹ : O → K` has
`f̂ ∘ r : O(C, 0) → F` sc-smooth (Definition 3.1.2 (preprint 3.2)).  (Definition 3.1.6 (preprint 3.6)) `(f, x₀)` has a filling if in
such a chart the section germ `Φ ∘ f ∘ φ⁻¹` has a filling `g : U → U ◁ F` (Definition 3.1.4 (preprint 3.4)) near
`0`; `(g, 0)` is a filled version.  (Definition 3.1.11 (preprint 3.11)) `(f, x₀)` is an sc-Fredholm germ if it has a
filled version `(g, 0)` and a local sc⁺-section `s : U → U ◁ F` with `s(0) = g(0)` such that
`g − s` is conjugated to a basic germ: a strong bundle isomorphism `Ψ : U ◁ F → U' ◁ F'` covering
an sc-diffeomorphism `ψ : U → U'` with `Ψ ∘ (g − s) ∘ ψ⁻¹` a basic germ (Definition 3.1.7 (preprint 3.7)).
(Definition 3.1.16 (preprint 3.14)) A section `f` of the tame strong bundle `P : Y → X` is sc-Fredholm if (1) it is
sc-smooth, (2) regularizing (`x ∈ X_m`, `f(x) ∈ Y_{m,m+1}` imply `x ∈ X_{m+1}`), (3) `(f, x)` is
an sc-Fredholm germ at every smooth point.  (Theorem 3.1.18 (preprint 3.15)) `f ∈ Fred(P)`, `s ∈ Γ⁺(P)` imply
`f + s ∈ Fred(P)`.

## What is formalized

* The sum rule of the sc-calculus on sets (`Polyfold.IsScSmooth.add`, `sub`, `neg`,
  `IsScSmooth.toBase_shift`), which the text uses silently ("`f + s` is an sc-smooth section").
* The section algebra: `Polyfold.fiberZero`, `Polyfold.IsZeroAt` (`f(x) = 0`),
  `Polyfold.sectionAdd` (`f + s`, fibrewise); the principal part
  `Polyfold.StrongBundleChart.principal` of a section in a chart, `principalLift` (its lift to
  `F₁`), and the identities `apply_section` (`Φ ∘ f ∘ φ⁻¹(z) = (z, f̂(z))`), `principal_sectionAdd`,
  `isZeroAt_iff` (`f(x) = 0 ⟺ f̂(φ(x)) = 0`).
* `Polyfold.StrongBundle.IsChart` (a strong bundle chart compatible with the atlas: the text's
  "strong bundle chart of `P`"), and the local representatives
  `StrongBundle.IsScSmoothSection.isScSmoothRetractMap` (`z ↦ (z, f̂(z))` is sc-smooth `O → K`)
  and `StrongBundle.IsScPlusSection.isScSmoothRetractMap_one` (`z ↦ (z, ŝ₁(z))` is sc-smooth
  `O → K[1]`) **in every compatible chart**, not only in the charts of the atlas (the change of
  chart on `[1]` is the compatibility of Definition 2.6.4 (preprint 2.50)).
* `Polyfold.StrongBundle.IsScSmoothSectionGerm` (**Definition 3.1.3 (preprint 3.3)**),
  `Polyfold.IsFilledVersion` (**Definition 3.1.6 (preprint 3.6)**, the local data), `Polyfold.IsStrongBundleIso`
  (the strong bundle isomorphisms of Definition 3.1.11 (preprint 3.11)), `Polyfold.IsConjugateToBasicGerm`,
  `Polyfold.StrongBundle.IsScFredholmGermWholeChart` (**Definition 3.1.11 (preprint 3.11)**),
  `Polyfold.StrongBundle.IsScFredholmSectionWholeChart` (**Definition 3.1.16 (preprint 3.14)**).
* `Polyfold.theorem_3_1_18_wholeChart` (**Theorem 3.1.18 (preprint 3.15)**): `sectionAdd f s` is an sc-Fredholm section when `f`
  is one and `s` is an sc⁺-section, with the three auxiliary statements
  `StrongBundle.IsScSmoothSection.sectionAdd` (`f + s` is sc-smooth),
  `StrongBundle.regularizing_sectionAdd_wholeChart` (`f + s` is regularizing) and
  `StrongBundle.IsScFredholmGermWholeChart.sectionAdd` (the germ property, from Lemma 3.1.20 (preprint 3.17) and
  `(g + t̃) − (t̃ + t₀) = g − t₀`).

## What the text leaves implicit, and the choices made (the findings)

* **Tameness is not used.**  Definition 3.1.16 (preprint 3.14) and Theorem 3.1.18 (preprint 3.15) are stated for a tame strong bundle
  (a strong bundle over a tame M-polyfold); nothing in Definitions 3.3–3.14 or in the proof of
  Theorem 3.1.18 (preprint 3.15) uses the tameness, so `IsScFredholmSectionWholeChart` and `theorem_3_1_18_wholeChart` do not assume it
  (they apply to tame bundles in particular).
* **"Strong bundle chart"** in Definitions 3.1.3, 3.1.6, 3.1.11 (preprint 3.3, 3.6, 3.11) is read as a chart compatible with the
  atlas of `P` (`StrongBundle.IsChart`), not necessarily a member of the atlas: a chart of the
  atlas need not be centred (`φ(x₀) = 0`), and the notion must not depend on the chosen atlas in
  its equivalence class.  This is why the local representatives of sc-smooth and sc⁺-sections
  are proved sc-smooth in every compatible chart.
* **The filled version is defined on all of `U`.**  The text's `g : U → U ◁ F` is a "section germ"
  (defined near `0`); here `g` is sc-smooth on the whole `U` of the chart (`IsFilledVersion`),
  which is no restriction for germs on ordinary neighbourhoods (germ data restrict to a smaller
  relatively open `U₀ ⊆ U`: `ConjugationData.ofSubset`, `IsFillingGerm.of_subset` in
  `Chapter3/RestrictOpenGerms.lean`; `StrongBundleChart.restrict` restricts the base of a chart to
  an open set of `X`, which does not by itself put the model domain inside `U₀`), but it is one for
  germs whose level sets shrink with the level (a
  map `C^k` on `(−1/k, 1/k)` for every `k` is an sc-smooth germ smooth on no neighbourhood,
  machine-checked in `Chapter3/GermVsChart.lean`, `exists_isScSmoothGerm_not_isScSmooth`): the
  notions here are the project's original whole-chart reading, stricter than the text's
  (Findings, Chapter 3 items 220–221 and 260–266; round-trip items V3.9, V3.43).  The text's germ
  reading is `StrongBundle.IsScFredholmGerm` (`GermFillingChart.lean`; phase 2, items 270–330),
  the canonical name since the switch, and `isScFredholmGerm_iff_germG_wholeChart` says that
  `IsScFredholmGermWholeChart` is exactly the germ reading with `g` and `s` sc-smooth on the whole
  `U`; whether the two agree for sections sc-smooth on `X` is open (item 264).  Conditions (1)–(3) of Definition 3.1.4 (preprint 3.4)
  keep their "near `0`" form (`IsFillerOf`).
* **Local sc⁺-sections** `s : U → U ◁ F` are maps `s : E₀ → F₁` sc-smooth into `F¹` on `U`
  (the principal part, as in `Polyfold.IsScPlusSection` of Definition 2.6.3 (preprint 2.49)); `g − s` is
  `u ↦ g(u) − ι(s(u))` with the inclusion `ι : F₁ → F₀`.
* **Conjugation to a basic germ.**  "`Ψ ∘ (g − s) ∘ ψ⁻¹ : U' → U' ◁ F'` is a basic germ" is read as:
  `Ψ` is a strong bundle isomorphism `U ◁ F → U' ◁ F'` (`IsStrongBundleIso`: strong bundle maps
  in both directions, inverse to each other), `ψ(0) = 0`, `U' ⊆ C' = C̃ ⊕ W` relatively open with
  `C̃` a partial quadrant of a finite-dimensional space, `h : O(C', 0) → ℝᴺ ⊕ W` a basic germ on a
  germ of neighbourhoods `G` with `G₀ ⊆ U'`, and `(Ψ(u, (g − s)(u)))₂ = h(ψ(u))` for `u ∈ U` near
  `0`.  The text's `C' = Tψ(0)C` (proof of Theorem 3.6.8 (preprint 3.54)) is not imposed.
* **`f + s`** needs the fibrewise vector space structure, given on `P⁻¹(x)`; `sectionAdd` is the
  sum in the fibre (with a junk value where `f` or `s` is not a section).  In a chart,
  `(f + s)^ = f̂ + ŝ` because `Φ` is linear on the fibres.
* **Theorem 3.1.18 (preprint 3.15), "`f + s` is an sc-smooth section which is also regularizing".**  Sc-smoothness
  of `f + s` is the sum rule in the charts (the local representative of `s` lies in `K[1] ⊆ K`,
  and `K` has linear fibres); regularizing: `s(x) ∈ Y_{m,m+1}` for `x ∈ X_m` (an sc⁺-section is
  sc-smooth into `Y[1]`), and `Y_{m,m+1}` is closed under fibrewise subtraction, so
  `(f + s)(x) ∈ Y_{m,m+1}` gives `f(x) ∈ Y_{m,m+1}`.  Both are a paragraph here and a clause in
  the text.
* An sc⁺-section is required to be continuous on `X` only through its charts; its continuity on
  each chart domain is `IsScPlusSection.continuousOn_source`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### The sum rule of the sc-calculus on sets -/

/-- The addition `F ⊕ F → F` as an sc-operator. -/
def ScBanach.addOp (F : ScBanach) : ScOperator (F.prod F) F where
  lvl m := ContinuousLinearMap.fst ℝ (F m) (F m) + ContinuousLinearMap.snd ℝ (F m) (F m)
  incl_comm m x := by
    change F.incl m (x.1 + x.2) = F.incl m x.1 + F.incl m x.2
    exact map_add _ _ _

@[simp] lemma ScBanach.addOp_apply (F : ScBanach) (p : (F.prod F) 0) :
    F.addOp 0 p = p.1 + p.2 := rfl

/-- The negation `F → F` as an sc-operator. -/
def ScBanach.negOp (F : ScBanach) : ScOperator F F where
  lvl m := -ContinuousLinearMap.id ℝ (F m)
  incl_comm m x := by
    change F.incl m (-x) = -(F.incl m x)
    exact map_neg _ _

@[simp] lemma ScBanach.negOp_apply (F : ScBanach) (x : F 0) : F.negOp 0 x = -x := rfl

section SumRule

variable {U : Set (E 0)} {f g : E 0 → F 0}

/-- **The sum rule**: the sum of sc-smooth maps is sc-smooth (pairing followed by the
sc-operator `F ⊕ F → F`). -/
theorem IsScSmooth.add (hU : IsScDomain E U) (hf : IsScSmooth U f) (hg : IsScSmooth U g) :
    IsScSmooth U fun x => f x + g x := by
  have := IsScSmooth.comp hU (isScDomain_univ _) (F.addOp.isScSmooth (isScDomain_univ _))
    (hf.scPair hU hg) (mapsTo_univ _ _)
  exact this.congr hU fun x _ => rfl

theorem IsScSmooth.neg (hU : IsScDomain E U) (hf : IsScSmooth U f) :
    IsScSmooth U fun x => -f x := by
  have := IsScSmooth.comp hU (isScDomain_univ _) (F.negOp.isScSmooth (isScDomain_univ _)) hf
    (mapsTo_univ _ _)
  exact this.congr hU fun x _ => rfl

theorem IsScSmooth.sub (hU : IsScDomain E U) (hf : IsScSmooth U f) (hg : IsScSmooth U g) :
    IsScSmooth U fun x => f x - g x :=
  (hf.add hU (hg.neg hU)).congr hU fun _ _ => (sub_eq_add_neg _ _).symm

/-- A map sc-smooth into `F¹` is sc-smooth into `F` (composition with the inclusion `F¹ → F`). -/
theorem IsScSmooth.toBase_shift {s : E 0 → F 1} (hU : IsScDomain E U)
    (hs : IsScSmooth (F := F.shift) U s) : IsScSmooth U fun x => F.toBase 1 (s x) := by
  have := IsScSmooth.comp hU (isScDomain_univ _) (F.shiftIncl.isScSmooth (isScDomain_univ _)) hs
    (mapsTo_univ _ _)
  exact this.congr hU fun x _ => rfl

/-- The second component of a map sc-smooth into `E' ⊕ F'`. -/
theorem IsScSmooth.snd {E' F' : ScBanach} {h : E 0 → (E'.prod F') 0} (hU : IsScDomain E U)
    (hh : IsScSmooth U h) : IsScSmooth (F := F') U fun x => (h x).2 := by
  have := IsScSmooth.comp hU (isScDomain_univ _) ((E'.prodSndOp F').isScSmooth (isScDomain_univ _))
    hh (mapsTo_univ _ _)
  exact this.congr hU fun x _ => rfl

/-- The first component of a map sc-smooth into `E' ⊕ F'`. -/
theorem IsScSmooth.fst {E' F' : ScBanach} {h : E 0 → (E'.prod F') 0} (hU : IsScDomain E U)
    (hh : IsScSmooth U h) : IsScSmooth (F := E') U fun x => (h x).1 := by
  have := IsScSmooth.comp hU (isScDomain_univ _) ((E'.prodFstOp F').isScSmooth (isScDomain_univ _))
    hh (mapsTo_univ _ _)
  exact this.congr hU fun x _ => rfl

end SumRule

/-! ### The section algebra of a bundle with linear fibres -/

universe u v

section Sections

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The zero of the fibre `P⁻¹(x)`, as a point of `Y`. -/
def fiberZero (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (x : X) : Y := ((0 : P ⁻¹' {x}) : Y)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
variable (P) in
lemma proj_fiberZero (x : X) : P (fiberZero P x) = x := (0 : P ⁻¹' {x}).2

/-- `f(x) = 0`: the section `f` vanishes at `x` (its value is the zero of the fibre). -/
def IsZeroAt (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (f : X → Y) (x : X) : Prop :=
  f x = fiberZero P x

open scoped Classical in
/-- The fibrewise sum `f + s` of two sections `f, s : X → Y` (with the junk value `f(x)` at a point
where one of them is not a section). -/
def sectionAdd (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (f s : X → Y) (x : X) : Y :=
  if h : P (f x) = x ∧ P (s x) = x then
    (((⟨f x, h.1⟩ : P ⁻¹' {x}) + ⟨s x, h.2⟩ : P ⁻¹' {x}) : Y)
  else f x

variable {f s : X → Y}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
lemma sectionAdd_apply (hf : IsSection P f) (hs : IsSection P s) (x : X) :
    sectionAdd P f s x = (((⟨f x, hf x⟩ : P ⁻¹' {x}) + ⟨s x, hs x⟩ : P ⁻¹' {x}) : Y) := by
  rw [sectionAdd, dif_pos ⟨hf x, hs x⟩]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `f + s` is a section. -/
lemma IsSection.sectionAdd (hf : IsSection P f) (hs : IsSection P s) :
    IsSection P (sectionAdd P f s) := fun x => by
  rw [sectionAdd_apply hf hs]
  exact ((⟨f x, hf x⟩ : P ⁻¹' {x}) + ⟨s x, hs x⟩ : P ⁻¹' {x}).2

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `fiberZero` is a section. -/
lemma isSection_fiberZero : IsSection P (fiberZero P) := proj_fiberZero P

namespace StrongBundleChart

variable (c : StrongBundleChart PX P)

/-- The **principal part** `f̂ : O → F` of a section `f` in the strong bundle chart `c`:
`Φ ∘ f ∘ φ⁻¹(z) = (z, f̂(z))` (Definition 3.1.3 (preprint 3.3), "the section `f̂ : O → K ⊂ U ◁ F` is of the form
`f̂(p) = (p, f̂(p))`"). -/
def principal (f : X → Y) : c.φ.model.E 0 → c.F 0 := fun z => (c (f (c.φ.symm z))).2

/-- The lift of the principal part to `F₁` (meaningful for sc⁺-sections). -/
def principalLift (f : X → Y) : c.φ.model.E 0 → c.F 1 :=
  fun z => Function.invFun (c.F.toBase 1) (c.principal f z)

lemma localRepOne_eq (f : X → Y) (z : c.φ.model.E 0) :
    StrongBundle.localRepOne c f z = ((c (f (c.φ.symm z))).1, c.principalLift f z) := rfl

lemma mem_source_of_proj {y : Y} (hy : P y ∈ c.φ.source) : y ∈ c.toPartialEquiv.source := by
  rw [c.source_eq]; exact hy

lemma fst_apply {y : Y} (hy : P y ∈ c.φ.source) : (c y).1 = c.φ (P y) :=
  c.covers y (c.mem_source_of_proj hy)

/-- The local representative of a section: `Φ(f(φ⁻¹(z))) = (z, f̂(z))` for `z ∈ O`. -/
lemma apply_section (hf : IsSection P f) {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) :
    c (f (c.φ.symm z)) = (z, c.principal f z) := by
  refine Prod.ext ?_ rfl
  rw [c.fst_apply (by rw [hf]; exact c.φ.symm_mapsTo hz), hf, c.φ.apply_symm_apply hz]

/-- `Φ(f(x)) = (φ(x), f̂(φ(x)))` for `x ∈ V`. -/
lemma apply_section' (hf : IsSection P f) {x : X} (hx : x ∈ c.φ.source) :
    c (f x) = (c.φ x, c.principal f (c.φ x)) := by
  have := c.apply_section hf (c.φ.mapsTo_model x hx)
  rwa [c.φ.symm_apply_apply hx] at this

/-- `Φ` is additive on the fibres. -/
lemma snd_add {x : X} (hx : x ∈ c.φ.source) (v w : P ⁻¹' {x}) :
    (c ((v + w : P ⁻¹' {x}) : Y)).2 = (c (v : Y)).2 + (c (w : Y)).2 :=
  (c.fiber_linear x hx).map_add v w

/-- `Φ` maps the zero of the fibre to `(φ(x), 0)`. -/
lemma snd_fiberZero {x : X} (hx : x ∈ c.φ.source) : (c (fiberZero P x)).2 = 0 :=
  (c.fiber_linear x hx).map_zero

lemma snd_sub {x : X} (hx : x ∈ c.φ.source) (v w : P ⁻¹' {x}) :
    (c ((v - w : P ⁻¹' {x}) : Y)).2 = (c (v : Y)).2 - (c (w : Y)).2 :=
  (c.fiber_linear x hx).map_sub v w

/-- The principal part of `f + s` is `f̂ + ŝ`. -/
lemma principal_sectionAdd (hf : IsSection P f) (hs : IsSection P s) {z : c.φ.model.E 0}
    (hz : z ∈ c.φ.model.O) :
    c.principal (sectionAdd P f s) z = c.principal f z + c.principal s z := by
  unfold principal
  rw [sectionAdd_apply hf hs]
  exact c.snd_add (c.φ.symm_mapsTo hz) _ _

/-- `f(x) = 0` if and only if the principal part vanishes at `φ(x)`. -/
lemma isZeroAt_iff (hf : IsSection P f) {x : X} (hx : x ∈ c.φ.source) :
    IsZeroAt P f x ↔ c.principal f (c.φ x) = 0 := by
  have h1 : c.principal f (c.φ x) = (c (f x)).2 := (congrArg Prod.snd (c.apply_section' hf hx)).symm
  constructor
  · intro h
    rw [h1, h, c.snd_fiberZero hx]
  · intro h
    have h2 : c (f x) = c (fiberZero P x) := by
      rw [c.apply_section' hf hx, h]
      refine Prod.ext ?_ (c.snd_fiberZero hx).symm
      change c.φ x = (c (fiberZero P x)).1
      rw [c.fst_apply (by rw [proj_fiberZero P]; exact hx), proj_fiberZero P]
    exact c.toPartialEquiv.injOn (c.mem_source_of_proj (by rw [hf]; exact hx))
      (c.mem_source_of_proj (by rw [proj_fiberZero P]; exact hx)) h2

/-- The principal part of `f` on `O` is `0` at the zeros. -/
lemma principal_eq_zero_of_isZeroAt (hf : IsSection P f) {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O)
    (h : IsZeroAt P f (c.φ.symm z)) : c.principal f z = 0 := by
  have := (c.isZeroAt_iff hf (c.φ.symm_mapsTo hz)).1 h
  rwa [c.φ.apply_symm_apply hz] at this

/-- The fibre of `K` over `u ∈ O` is a linear subspace: `(u, a), (u, b) ∈ K` give
`(u, a + b) ∈ K`. -/
lemma add_mem_K {u : c.φ.model.E 0} {a b : c.F 0} (ha : (u, a) ∈ c.K) (hb : (u, b) ∈ c.K) :
    (u, a + b) ∈ c.K := by
  have hR := c.isRetraction
  rw [StrongBundleChart.K, hR.mem_image_iff c.relOpen] at ha hb ⊢
  refine ⟨ha.1, ?_⟩
  have huU : u ∈ c.U := (hR.baseRetraction c.relOpen).retract_subset ha.1
  change (c.R (u, a + b)).2 = a + b
  rw [(hR.fiber_linear u huU).map_add]
  exact congrArg₂ (· + ·) ha.2 hb.2

end StrongBundleChart

end Sections

/-! ### Strong bundle charts of a strong bundle; local representatives -/

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
  {f s : X → Y}

namespace StrongBundle

/-- A **strong bundle chart of `P`**: a strong bundle chart compatible with the atlas of `B`
(Definition 2.6.4 (preprint 2.50); the charts the text uses in Definitions 3.1.3, 3.1.6, 3.1.11 (preprint 3.3, 3.6, 3.11)). -/
def IsChart (c : StrongBundleChart PX P) : Prop := ∀ c' ∈ B.atlas.charts, c.Compatible c'

lemma isChart_of_mem {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts) : B.IsChart c :=
  fun c' hc' => B.atlas.compatible c hc c' hc'

/-- A strong bundle chart of `P` is a chart of the M-polyfold `Y[0]`. -/
lemma IsChart.toMChart {c : StrongBundleChart PX P} (hc : B.IsChart c) :
    B.toMPolyfold0.IsChart (c.toMChart B.continuous) := by
  rintro _ ⟨c', hc', rfl⟩
  exact (hc c' hc').toMChart B.continuous

variable {B}

/-- **The local representative of an sc-smooth section** in a strong bundle chart of `P`:
`z ↦ (z, f̂(z))` is sc-smooth `O → K` (Definition 2.6.6 (preprint 2.52) read in the chart). -/
theorem IsScSmoothSection.isScSmoothRetractMap (hf : B.IsScSmoothSection f)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) :
    IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal f z)) := by
  have h := hf.2.smooth c.φ (c.toMChart B.continuous) c.isChart hc.toMChart c.φ.source
    c.φ.isOpen_source (fun x hx => ⟨mem_univ _, hx⟩)
    (fun x hx => c.mem_source_of_proj (by rw [hf.1 x]; exact hx))
  rw [c.φ.image_source] at h
  exact h.congr fun z hz => c.apply_section hf.1 hz

/-- The principal part of an sc-smooth section is continuous on `O`. -/
theorem IsScSmoothSection.continuousOn_principal (hf : B.IsScSmoothSection f)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) :
    ContinuousOn (c.principal f) c.φ.model.O :=
  (continuous_snd.comp_continuousOn
    ((hf.isScSmoothRetractMap hc).continuousOn c.φ.model.isScRetract)).congr fun _ _ => rfl

/-- The principal part of an sc⁺-section takes values in `F₁`, in every strong bundle chart of
`P` (the compatibility of Definition 2.6.4 (preprint 2.50) on `[1]`). -/
theorem IsScPlusSection.principal_mem_range (hs : B.IsScPlusSection s) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) :
    c.principal s z ∈ range (c.F.toBase 1) := by
  set x := c.φ.symm z with hx
  have hxV : x ∈ c.φ.source := c.φ.symm_mapsTo hz
  obtain ⟨c', hc', hsx⟩ := B.atlas.cover (s x)
  have hxV' : x ∈ c'.φ.source := by rw [c'.source_eq, mem_preimage, hs.1 x] at hsx; exact hsx
  have h1 : (c' (s x)).2 ∈ range (c'.F.toBase 1) := (hs.2 c' hc').1 x hxV'
  have h2 := (hc c' hc').2.2.2.2.2 (c' (s x))
    ⟨s x, ⟨hsx, c.mem_source_of_proj (by rw [hs.1 x]; exact hxV)⟩, rfl⟩ h1
  rw [c'.transition_apply c hsx] at h2
  exact h2

/-- **The local representative of an sc⁺-section** in a strong bundle chart of `P`:
`z ↦ (z, ŝ₁(z))` is sc-smooth `O → K[1]` (Definition 2.6.6 (preprint 2.52) read in the chart; for a chart not in
the atlas this is the change of chart `(Φ ∘ Φ'⁻¹)[1]` of Definition 2.6.4 (preprint 2.50)). -/
theorem IsScPlusSection.isScSmoothRetractMap_one (hs : B.IsScPlusSection s)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) :
    IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F.shift)
      (c.φ.model.C ×ˢ univ) (strongShiftOne c.K) (fun z => (z, c.principalLift s z)) := by
  have hP := B.continuous
  -- the map lands in `K[1]`
  have hmaps : MapsTo (fun z => (z, c.principalLift s z)) c.φ.model.O (strongShiftOne c.K) := by
    intro z hz
    change (z, c.F.toBase 1 (c.principalLift s z)) ∈ c.K
    rw [StrongBundleChart.principalLift, Function.invFun_eq (hs.principal_mem_range hc hz)]
    rw [← c.apply_section hs.1 hz, ← c.image_source]
    exact ⟨_, c.mem_source_of_proj (by rw [hs.1]; exact c.φ.symm_mapsTo hz), rfl⟩
  refine IsScSmoothRetractMap.of_locally hmaps fun z hz => ?_
  set x := c.φ.symm z with hx
  have hxV : x ∈ c.φ.source := c.φ.symm_mapsTo hz
  obtain ⟨c', hc', hsx⟩ := B.atlas.cover (s x)
  have hxV' : x ∈ c'.φ.source := by rw [c'.source_eq, mem_preimage, hs.1 x] at hsx; exact hsx
  -- the open set `W` with `O ∩ W = φ(V ∩ V')`
  obtain ⟨W, hW, hWeq⟩ := c.φ.exists_isOpen_image_eq (s := c.φ.source ∩ c'.φ.source)
    inter_subset_left (c.φ.isOpen_source.inter c'.φ.isOpen_source)
  refine ⟨W, hW, ?_, ?_⟩
  · have : z ∈ c.φ '' (c.φ.source ∩ c'.φ.source) := ⟨x, ⟨hxV, hxV'⟩, c.φ.apply_symm_apply hz⟩
    rw [hWeq] at this; exact this.2
  rw [← hWeq]
  -- the three factors
  have hcomp : c.φ.Compatible c'.φ := c.isChart.compatible c'.isChart (P := PX)
  have h1 : IsScSmoothRetractMap c.φ.model.E c.φ.model.C (c.φ.overlap c'.φ) c'.φ.model.E
      c'.φ.model.C (c'.φ.overlap c.φ) (c.φ.transition c'.φ) :=
    hcomp.1.mono_target (c.φ.transition_mapsTo c'.φ)
  have h2 : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C (c'.φ.overlap c.φ)
      (c'.φ.model.E.prod c'.F.shift) (c'.φ.model.C ×ˢ univ) (strongShiftOne (c'.overlap c))
      (StrongBundle.localRepOne c' s) := by
    obtain ⟨W', hW', hW'eq⟩ := c'.φ.exists_isOpen_image_eq (s := c'.φ.source ∩ c.φ.source)
      inter_subset_left (c'.φ.isOpen_source.inter c.φ.isOpen_source)
    have hov : c'.φ.overlap c.φ = c'.φ.model.O ∩ W' := hW'eq
    rw [hov]
    refine (IsScSmoothRetractMap.restrict (hs.2 c' hc').2 c'.φ.model.isScRetract
      (W := W')).mono_target ?_
    · intro z hz
      rw [← hov] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      have hy1 : (c' (s y)).2 ∈ range (c'.F.toBase 1) := (hs.2 c' hc').1 y hy.1
      have hrep : StrongBundle.localRepOne c' s (c'.φ y) =
          ((c' (s y)).1, Function.invFun (c'.F.toBase 1) (c' (s y)).2) := by
        rw [StrongBundle.localRepOne, c'.φ.symm_apply_apply hy.1]
      change ((StrongBundle.localRepOne c' s (c'.φ y)).1,
        c'.F.toBase 1 (StrongBundle.localRepOne c' s (c'.φ y)).2) ∈ c'.overlap c
      rw [hrep]
      simp only [Function.invFun_eq hy1, Prod.mk.eta]
      exact ⟨s y, ⟨c'.mem_source_of_proj (by rw [hs.1]; exact hy.1),
        c.mem_source_of_proj (by rw [hs.1]; exact hy.2)⟩, rfl⟩
  have h3 : IsScSmoothRetractMap (c'.φ.model.E.prod c'.F.shift) (c'.φ.model.C ×ˢ univ)
      (strongShiftOne (c'.overlap c)) (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
      (strongShiftOne c.K) (shiftFiber (c'.transition c)) := by
    refine (hc c' hc').2.2.2.1.mono_target ?_
    intro p hp
    have := (hc c' hc').2.2.2.1.mapsTo hp
    change (_, _) ∈ c.overlap c' at this
    change (_, _) ∈ c.K
    rw [← c.image_source]
    exact image_mono inter_subset_left this
  have hret : IsScRetract (c'.φ.model.E.prod c'.F.shift) (c'.φ.model.C ×ˢ univ)
      (strongShiftOne (c'.overlap c)) := c'.isScRetract_overlap_one c hP
  refine ((h3.comp h2 hret).comp h1 (c'.φ.isScRetract_overlap c.φ)).congr ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [Function.comp_apply]
  rw [c.φ.transition_apply c'.φ hy.1]
  have hsy : s y ∈ c'.toPartialEquiv.source := c'.mem_source_of_proj (by rw [hs.1]; exact hy.2)
  have hy1 : (c' (s y)).2 ∈ range (c'.F.toBase 1) := (hs.2 c' hc').1 y hy.2
  have hrep : StrongBundle.localRepOne c' s (c'.φ y) =
      ((c' (s y)).1, Function.invFun (c'.F.toBase 1) (c' (s y)).2) := by
    rw [StrongBundle.localRepOne, c'.φ.symm_apply_apply hy.2]
  rw [hrep]
  unfold shiftFiber
  simp only [Function.invFun_eq hy1, Prod.mk.eta]
  rw [c'.transition_apply c hsy, c.apply_section' hs.1 hy.1]
  rfl

/-- An sc⁺-section is continuous on the domain of every chart of the atlas (through the chart
`Φ[1]`); the text's "sc⁺-sections are sc-smooth sections, hence continuous". -/
theorem IsScPlusSection.continuousOn_source (hs : B.IsScPlusSection s) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) : ContinuousOn s c.φ.source := by
  have h1 : ContinuousOn (fun z => (z, c.F.toBase 1 (c.principalLift s z))) c.φ.model.O := by
    have := (hs.isScSmoothRetractMap_one hc).continuousOn c.φ.model.isScRetract
    exact continuous_id.continuousOn.prodMk ((c.F.toBase 1).continuous.comp_continuousOn
      (continuous_snd.comp_continuousOn this))
  have h2 : ∀ z ∈ c.φ.model.O,
      (z, c.F.toBase 1 (c.principalLift s z)) ∈ c.toPartialEquiv.target := by
    intro z hz
    rw [c.target_eq]
    exact (hs.isScSmoothRetractMap_one hc).mapsTo hz
  have h3 : ContinuousOn (fun z => c.toPartialEquiv.symm (z, c.F.toBase 1 (c.principalLift s z)))
      c.φ.model.O := c.continuousOn_invFun.comp h1 h2
  have h4 := h3.comp c.φ.continuousOn_toFun (c.φ.mapsTo_model)
  refine h4.congr fun x hx => ?_
  simp only [Function.comp_apply]
  rw [StrongBundleChart.principalLift, Function.invFun_eq (hs.principal_mem_range hc
    (c.φ.mapsTo_model x hx)), ← c.apply_section' hs.1 hx]
  exact (c.toPartialEquiv.left_inv (c.mem_source_of_proj (by rw [hs.1]; exact hx))).symm

end StrongBundle

end Bundle


/-! ### Definition 3.1.6 (preprint 3.6) (filled versions), strong bundle isomorphisms, conjugation to a basic germ -/

section LocalData

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **Definition 3.1.6 (preprint 3.6), the local data**: `g : U → F` is a **filled version** of the principal part
`f̂ : O → F` of a section of the tame strong local bundle `K = R(U ◁ F) → O`: `g` is sc-smooth on
`U` (the principal part of an sc-smooth section `u ↦ (u, g(u))` of `U ◁ F → U`) and fills `f̂` in
the sense of Definition 3.1.4 (preprint 3.4) (`IsFillerOf`: conditions (1)–(3) near `0`).  The text's germ
`(g, 0)` is defined near `0` only; here on the whole `U` of the chart — stricter than the text for
germs whose level sets shrink with the level (Findings, Chapter 3 items 220–221 and 260–263; the
text's germ reading is `IsFillingGerm` in `Chapter3/GermVsChart.lean`, and
`IsFillingGerm.isFilledVersion` recovers this notion from it when `g` is sc-smooth on `U`). -/
structure IsFilledVersion (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) (fb g : E 0 → F 0) : Prop where
  isScSmooth : IsScSmooth U g
  filler : IsFillerOf hU hR h0 fb g

/-- A **strong bundle isomorphism** `Ψ : U ◁ F → U' ◁ F'` (Definition 3.1.11 (preprint 3.11): "a strong bundle
isomorphism `Ψ : U ◁ F → U' ◁ F'` covering the sc-diffeomorphism `ψ : U → U'`"): strong bundle maps
(Definition 2.6.1 (preprint 2.47)) in both directions, inverse to each other on `U ⊕ F` and `U' ⊕ F'`.  The base
maps `ψ = base Ψ`, `ψ' = base Ψ'` are then inverse sc-diffeomorphisms `U ≅ U'`. -/
structure IsStrongBundleIso {E' F' : ScBanach} (U : Set (E 0)) (U' : Set (E' 0))
    (Ψ : E 0 × F 0 → E' 0 × F' 0) (Ψ' : E' 0 × F' 0 → E 0 × F 0) : Prop where
  toFun : IsStrongBundleMap U U' Ψ
  invFun : IsStrongBundleMap U' U Ψ'
  left_inv : ∀ p ∈ U ×ˢ (univ : Set (F 0)), Ψ' (Ψ p) = p
  right_inv : ∀ p ∈ U' ×ˢ (univ : Set (F' 0)), Ψ (Ψ' p) = p

/-- **Definition 3.1.11 (preprint 3.11), second paragraph**: the principal part `k : U → F` of a section of
`U ◁ F → U` is **conjugated to a basic germ**: there are a strong bundle isomorphism
`Ψ : U ◁ F → U' ◁ F'` with `ψ(0) = 0`, where `U'` is relatively open in the partial quadrant
`C' = C̃ ⊕ W` of `E' = ℝⁿ ⊕ W` (`C̃` a partial quadrant in the finite-dimensional `ℝⁿ`) and
`F' = ℝᴺ ⊕ W`, and a basic germ `h : O(C', 0) → ℝᴺ ⊕ W` (Definition 3.1.7 (preprint 3.7), on a germ of
neighbourhoods `G` with `G₀ ⊆ U'`) such that the push-forward section `Ψ ∘ (u, k(u)) ∘ ψ⁻¹` is
`h` near `0`: `(Ψ(u, k(u)))₂ = h(ψ(u))` for `u ∈ U` near `0`. -/
def IsConjugateToBasicGerm (U : Set (E 0)) (k : E 0 → F 0) : Prop :=
  ∃ (Pn Q : Type) (_ : NormedAddCommGroup Pn) (_ : NormedSpace ℝ Pn) (_ : FiniteDimensional ℝ Pn)
    (_ : NormedAddCommGroup Q) (_ : NormedSpace ℝ Q) (_ : FiniteDimensional ℝ Q)
    (W : ScBanach) (Ct : Set Pn) (U' : Set ((ScBanach.paramProd Pn W) 0))
    (Ψ : E 0 × F 0 → (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0)
    (Ψ' : (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0 → E 0 × F 0)
    (G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ)) (h : Pn × W 0 → Q × W 0)
    (Bc : Pn × W 0 → W 0),
    IsPartialQuadrant (ScBanach.const Pn) Ct ∧
    IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U' ∧
    IsStrongBundleIso U U' Ψ Ψ' ∧ IsStrongBundleMap.base Ψ 0 = 0 ∧ G.U 0 ⊆ U' ∧
    IsBasicGerm Ct G h Bc ∧
    ∀ᶠ u in 𝓝 (0 : E 0), u ∈ U → (Ψ (u, k u)).2 = h (IsStrongBundleMap.base Ψ u)

/-- Conjugation to a basic germ depends only on the values of `k` on `U`. -/
theorem IsConjugateToBasicGerm.congr {k k' : E 0 → F 0} (h : IsConjugateToBasicGerm U k)
    (hkk' : ∀ u ∈ U, k u = k' u) : IsConjugateToBasicGerm U k' := by
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, hb, Bc, hCt, hU', hΨ, h0, hG, hh,
    hev⟩ := h
  refine ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, hb, Bc, hCt, hU', hΨ, h0, hG, hh, ?_⟩
  filter_upwards [hev] with u hu huU
  rw [← hkk' u huU]; exact hu huU

/-- The condition (1) of a filler only involves the values of `f̂` on `O`. -/
theorem IsFillerOf.congr_left (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) {fb fb' g : E 0 → F 0} (h : IsFillerOf hU hR h0 fb g)
    (hff' : ∀ x ∈ StrongRetr.r R '' U, fb x = fb' x) : IsFillerOf hU hR h0 fb' g :=
  ⟨h.eq_on.mono fun x hx hxO => (hff' x hxO) ▸ hx hxO, h.mem_of_fixed, h.isSc1, h.linearization⟩

end LocalData

/-! ### Definitions 3.1.3, 3.1.11, 3.1.16 (preprint 3.3, 3.11, 3.14) for sections of a strong bundle -/

section FredholmSections

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
  {f s : X → Y}

namespace StrongBundleChart

variable (c : StrongBundleChart PX P)

omit [T2Space Y] [ParacompactSpace Y] in
/-- The base retraction `r : U → U` of the chart, `r(U) = O`. -/
lemma r_image : StrongRetr.r c.R '' c.U = c.φ.model.O := c.base_retract

omit [T2Space Y] [ParacompactSpace Y] in
lemma r_mem_O {u : c.φ.model.E 0} (hu : u ∈ c.U) : StrongRetr.r c.R u ∈ c.φ.model.O :=
  c.r_image ▸ ⟨u, hu, rfl⟩

omit [T2Space Y] [ParacompactSpace Y] in
/-- `0 ∈ U` for a chart centred at `x₀` (`φ(x₀) = 0 ∈ O ⊆ U`). -/
lemma zero_mem_U {x₀ : X} (hx : x₀ ∈ c.φ.source) (h0 : c.φ x₀ = 0) : (0 : c.φ.model.E 0) ∈ c.U := by
  have := c.φ.mapsTo_model x₀ hx
  rw [h0, ← c.r_image] at this
  obtain ⟨u, hu, hueq⟩ := this
  rw [← hueq]; exact StrongRetr.r_mem c.isRetraction hu

omit [T2Space Y] [ParacompactSpace Y] in
lemma isQuadrantLike : IsQuadrantLike c.φ.model.E c.φ.model.C :=
  c.relOpen.isPartialQuadrant.isQuadrantLike

end StrongBundleChart

namespace StrongBundle

variable {B}

/-- There is a chart of the atlas around every point of `X` (`P` is surjective). -/
lemma exists_chart_mem (B : StrongBundle PX P) (x : X) : ∃ c ∈ B.atlas.charts, x ∈ c.φ.source := by
  obtain ⟨y, rfl⟩ := B.surjective x
  obtain ⟨c, hc, hy⟩ := B.atlas.cover y
  rw [c.source_eq] at hy
  exact ⟨c, hc, hy⟩

/-- `ι(ŝ₁(z)) = ŝ(z)` on `O` for an sc⁺-section. -/
lemma IsScPlusSection.toBase_principalLift (hs : B.IsScPlusSection s) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) :
    c.F.toBase 1 (c.principalLift s z) = c.principal s z :=
  Function.invFun_eq (hs.principal_mem_range hc hz)

/-- `(z, ŝ(z)) ∈ K` for `z ∈ O` (an sc⁺-section is a section of `K → O`). -/
lemma IsScPlusSection.mem_K (hs : B.IsScPlusSection s) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) : (z, c.principal s z) ∈ c.K := by
  have := (hs.isScSmoothRetractMap_one hc).mapsTo hz
  change (z, c.F.toBase 1 (c.principalLift s z)) ∈ c.K at this
  rwa [hs.toBase_principalLift hc hz] at this

/-- `ŝ(φ(x)) ∈ F_{m+1}` for `x ∈ X_m`: an sc⁺-section takes values in `Y_{m,m+1}` on `X_m`. -/
lemma IsScPlusSection.snd_mem_range (hs : B.IsScPlusSection s) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {m : ℕ} {x : X} (hxV : x ∈ c.φ.source) (hx : x ∈ PX.levelSet m) :
    (c (s x)).2 ∈ range (c.F.toBase (m + 1)) := by
  have hz : c.φ x ∈ c.φ.model.O := c.φ.mapsTo_model x hxV
  have hm : c.φ x ∈ range (c.φ.model.E.toBase m) := (PX.mem_levelSet_iff c.isChart hxV).1 hx
  obtain ⟨q, hq⟩ := (hs.isScSmoothRetractMap_one hc).mem_range_toBase c.φ.model.isScRetract hz hm
  rw [ScBanach.prod_toBase] at hq
  have h2 : c.F.shift.toBase m q.2 = c.principalLift s (c.φ x) := congrArg Prod.snd hq
  refine ⟨q.2, ?_⟩
  rw [c.F.shift_toBase, h2, hs.toBase_principalLift hc hz]
  exact (congrArg Prod.snd (c.apply_section' hs.1 hxV)).symm

/-- **The sum rule in a chart**: `z ↦ (z, f̂(z) + ŝ(z))` is sc-smooth `O → K` for an sc-smooth
section `f` and an sc⁺-section `s`. -/
theorem IsScSmoothSection.add_isScSmoothRetractMap (hf : B.IsScSmoothSection f)
    (hs : B.IsScPlusSection s) {c : StrongBundleChart PX P} (hc : B.IsChart c) :
    IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal f z + c.principal s z)) where
  mapsTo z hz := c.add_mem_K ((hf.isScSmoothRetractMap hc).mapsTo hz) (hs.mem_K hc hz)
  comp_isScSmooth R hR := by
    have hU := R.isScDomain
    have h1 : IsScSmooth R.U fun u => c.principal f (R u) :=
      (((hf.isScSmoothRetractMap hc).comp_isScSmooth R hR).snd hU).congr hU fun _ _ => rfl
    have h2 : IsScSmooth (F := c.F.shift) R.U fun u => c.principalLift s (R u) :=
      (((hs.isScSmoothRetractMap_one hc).comp_isScSmooth R hR).snd hU).congr hU fun _ _ => rfl
    have h3 : IsScSmooth R.U fun u => c.principal s (R u) :=
      (h2.toBase_shift hU).congr hU fun u hu =>
        hs.toBase_principalLift hc (hR ▸ R.apply_mem_retract hu)
    exact (R.isScSmooth.scPair hU (h1.add hU h3)).congr hU fun _ _ => rfl

/-- `f + s` is continuous on the domain of every strong bundle chart of `P`. -/
theorem continuousOn_sectionAdd (hf : B.IsScSmoothSection f) (hs : B.IsScPlusSection s)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) :
    ContinuousOn (sectionAdd P f s) c.φ.source := by
  have hsec := hf.1.sectionAdd hs.1
  have h1 : ContinuousOn (fun z => (z, c.principal f z + c.principal s z)) c.φ.model.O :=
    (hf.add_isScSmoothRetractMap hs hc).continuousOn c.φ.model.isScRetract
  have h2 : ∀ z ∈ c.φ.model.O,
      (z, c.principal f z + c.principal s z) ∈ c.toPartialEquiv.target := by
    intro z hz
    rw [c.target_eq]
    exact (hf.add_isScSmoothRetractMap hs hc).mapsTo hz
  have h3 := c.continuousOn_invFun.comp h1 h2
  refine (h3.comp c.φ.continuousOn_toFun c.φ.mapsTo_model).congr fun x hx => ?_
  simp only [Function.comp_apply]
  rw [← c.principal_sectionAdd hf.1 hs.1 (c.φ.mapsTo_model x hx), ← c.apply_section' hsec hx]
  exact (c.toPartialEquiv.left_inv (c.mem_source_of_proj (by rw [hsec]; exact hx))).symm

/-- **Theorem 3.1.18 (preprint 3.15), first clause**: the sum of an sc-smooth section and an sc⁺-section is an
sc-smooth section (the sum rule in the charts). -/
theorem IsScSmoothSection.sectionAdd (hf : B.IsScSmoothSection f) (hs : B.IsScPlusSection s) :
    B.IsScSmoothSection (Polyfold.sectionAdd P f s) := by
  have hsec := hf.1.sectionAdd hs.1
  refine ⟨hsec, MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ ?_ fun x _ => ?_⟩
  · refine continuousOn_univ.2 (continuous_iff_continuousAt.2 fun x => ?_)
    obtain ⟨c, hc, hx⟩ := B.exists_chart_mem x
    exact (continuousOn_sectionAdd hf hs (B.isChart_of_mem hc)).continuousAt
      (c.φ.isOpen_source.mem_nhds hx)
  · obtain ⟨c, hc, hx⟩ := B.exists_chart_mem x
    refine ⟨c.φ, c.toMChart B.continuous, c.φ.source, c.isChart, (B.isChart_of_mem hc).toMChart,
      c.φ.isOpen_source, hx, fun y hy => ⟨mem_univ _, hy⟩,
      fun y hy => c.mem_source_of_proj (by rw [hsec y]; exact hy), ?_⟩
    rw [c.φ.image_source]
    refine (hf.add_isScSmoothRetractMap hs (B.isChart_of_mem hc)).congr fun z hz => ?_
    change (z, c.principal f z + c.principal s z) = c (Polyfold.sectionAdd P f s (c.φ.symm z))
    rw [c.apply_section hsec hz, c.principal_sectionAdd hf.1 hs.1 hz]

/-- **Definition 3.1.3 (preprint 3.3)**: an **sc-smooth section germ** `(f, x₀)` of `P : Y → X`: a section `f`
and a smooth point `x₀` such that in some strong bundle chart of `P` with `φ(x₀) = 0 ∈ O` the
principal part `f̂` of `Φ ∘ f ∘ φ⁻¹ : O → K` has `f̂ ∘ r : O(C, 0) → F` sc-smooth in the sense of
Definition 3.1.2 (preprint 3.2), on some sc-germ of neighbourhoods `G` of `0` with `G₀ ⊆ U` (the text's germ
reading: the levels `G_m` may shrink with `m`, Definition 3.1.1 (preprint 3.1); Findings, Chapter 3, items 221 and
260; until 2026-11-02 the germ was the chart's `U ∩ E_m`).  The text's "continuous section on an
open neighbourhood `V` of `x₀`" is the section on `V = dom φ`. -/
structure IsScSmoothSectionGerm (f : X → Y) (x₀ : X) : Prop where
  isSection : IsSection P f
  smooth_pt : x₀ ∈ PX.smoothSet
  exists_chart : ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source)
    (_ : c.φ x₀ = 0) (_ : (0 : c.φ.model.E 0) ∈ c.U),
    ∃ G : ScNbhdGerm c.φ.model.E c.φ.model.C, G.U 0 ⊆ c.U ∧
      IsScSmoothGerm G (c.principal f ∘ StrongRetr.r c.R)

/-- An sc-smooth section (Definition 2.6.6 (preprint 2.52)) is an sc-smooth section germ (Definition 3.1.3 (preprint 3.3)) at every
smooth point around which there is a centred strong bundle chart. -/
theorem IsScSmoothSection.isScSmoothSectionGerm (hf : B.IsScSmoothSection f) {x₀ : X}
    (hx₀ : x₀ ∈ PX.smoothSet) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hx : x₀ ∈ c.φ.source) (h0 : c.φ x₀ = 0) : B.IsScSmoothSectionGerm f x₀ := by
  refine ⟨hf.1, hx₀, c, hc, hx, h0, c.zero_mem_U hx h0, ?_⟩
  have h1 := (hf.isScSmoothRetractMap hc).comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen)
    c.base_retract
  have h2 : IsScSmooth c.U (c.principal f ∘ StrongRetr.r c.R) :=
    (h1.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl
  exact ⟨ScNbhdGerm.ofSet c.relOpen.relOpen (c.zero_mem_U hx h0), fun _ hu => hu,
    h2.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen _⟩

variable (B) in
/-- **Definition 3.1.11 (preprint 3.11)**: `(f, x₀)` is an **sc-Fredholm germ** of the section `f` at the smooth point
`x₀`: in some strong bundle chart of `P` centred at `x₀`, the principal part `f̂` has a filled
version `g : U → F` (Definition 3.1.6 (preprint 3.6)), and there is a local sc⁺-section `s : U → F¹` with
`s(0) = g(0)` such that `g − s` is conjugated to a basic germ (Definition 3.1.7 (preprint 3.7)). This is the
project's original whole-chart reading, stricter than the text (Findings, Chapter 3, items 220–221,
260–266); the text's germ reading is `IsScFredholmGerm` (`GermFillingChart.lean`, phase 2, items
270–330). -/
def IsScFredholmGermWholeChart (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScSmooth (F := c.F.shift) c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u))

variable (B) in
/-- **Definition 3.1.16 (preprint 3.14)**: an **sc-Fredholm section** of the strong bundle `P : Y → X`: (1) `f` is
sc-smooth; (2) `f` is regularizing: `x ∈ X_m` and `f(x) ∈ Y_{m,m+1}` imply `x ∈ X_{m+1}`; (3)
`(f, x)` is an sc-Fredholm germ at every smooth point `x`. (The text states the definition for a
tame strong bundle; tameness plays no role in it, nor in Theorem 3.1.18 (preprint 3.15).) This is the project's
original whole-chart reading, stricter than the text (Findings, Chapter 3, items 220–221, 260–266);
the text's germ reading is `IsScFredholmSection` (`TameGermsG.lean`, phase 2, items 270–330). -/
structure IsScFredholmSectionWholeChart (f : X → Y) : Prop where
  isScSmooth : B.IsScSmoothSection f
  regularizing : ∀ m, ∀ x ∈ PX.levelSet m, f x ∈ B.doubleLevel m (m + 1) → x ∈ PX.levelSet (m + 1)
  germ : ∀ x ∈ PX.smoothSet, B.IsScFredholmGermWholeChart f x

/-- **Theorem 3.1.18 (preprint 3.15), second clause**: `f + s` is regularizing when `f` is: `s(x) ∈ Y_{m,m+1}` for
`x ∈ X_m`, and `Y_{m,m+1}` is closed under fibrewise subtraction, so `(f + s)(x) ∈ Y_{m,m+1}` gives
`f(x) ∈ Y_{m,m+1}`. -/
theorem regularizing_sectionAdd_wholeChart (hf : B.IsScFredholmSectionWholeChart f) (hs : B.IsScPlusSection s) :
    ∀ m, ∀ x ∈ PX.levelSet m, sectionAdd P f s x ∈ B.doubleLevel m (m + 1) →
      x ∈ PX.levelSet (m + 1) := by
  intro m x hx hfs
  have hfsec := hf.isScSmooth.1
  refine hf.regularizing m x hx fun c hc hmem => ?_
  have hxV : x ∈ c.φ.source := by rw [c.source_eq, mem_preimage, hfsec x] at hmem; exact hmem
  have h1 := hfs c hc (c.mem_source_of_proj (by rw [(hfsec.sectionAdd hs.1) x]; exact hxV))
  refine ⟨?_, ?_⟩
  · rw [c.fst_apply (by rw [hfsec]; exact hxV), hfsec]
    exact (PX.mem_levelSet_iff c.isChart hxV).1 hx
  · have hsx := hs.snd_mem_range (B.isChart_of_mem hc) hxV hx
    have heq : (c (f x)).2 = (c (sectionAdd P f s x)).2 - (c (s x)).2 := by
      rw [sectionAdd_apply hfsec hs.1, c.snd_add hxV]
      change (c (f x)).2 = (c (f x)).2 + (c (s x)).2 - (c (s x)).2
      abel
    obtain ⟨a, ha⟩ := h1.2
    obtain ⟨b, hb⟩ := hsx
    exact ⟨a - b, by rw [map_sub, ha, hb, heq]⟩

/-- **Theorem 3.1.18 (preprint 3.15), the germ property**: if `(f, x)` is an sc-Fredholm germ and `s` is an
sc⁺-section, then `(f + s, x)` is an sc-Fredholm germ, in the same chart: the filled version
`g + t̃` with `t̃ = ŝ ∘ r` (Lemma 3.1.20 (preprint 3.17)), the sc⁺-section `t̃ + t₀`, and
`(g + t̃) − (t̃ + t₀) = g − t₀`, which is conjugated to the same basic germ. -/
theorem IsScFredholmGermWholeChart.sectionAdd {x : X} (hfs : IsSection P f) (hg : B.IsScFredholmGermWholeChart f x)
    (hs : B.IsScPlusSection s) : B.IsScFredholmGermWholeChart (Polyfold.sectionAdd P f s) x := by
  obtain ⟨hxs, c, hc, hxV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj⟩ := hg
  have hU := c.relOpen.isScDomain
  -- `ŝ₁ ∘ r` is sc-smooth into `F¹` on `U`, and `ŝ ∘ r = ι ∘ ŝ₁ ∘ r`
  have hlift : IsScSmooth (F := c.F.shift) c.U fun u => c.principalLift s (StrongRetr.r c.R u) :=
    (((hs.isScSmoothRetractMap_one hc).comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen)
      c.base_retract).snd hU).congr hU
      fun _ _ => rfl
  have hsr : IsScSmooth c.U fun u => c.principal s (StrongRetr.r c.R u) :=
    (hlift.toBase_shift hU).congr hU fun u hu => hs.toBase_principalLift hc (c.r_mem_O hu)
  refine ⟨hxs, c, hc, hxV, h0, h0U, fun u => g u + c.principal s (StrongRetr.r c.R u),
    fun u => c.principalLift s (StrongRetr.r c.R u) + t₀ u, ⟨hfill.isScSmooth.add hU hsr, ?_⟩,
    hlift.add hU ht₀, ?_, ?_⟩
  · -- Lemma 3.1.20 (preprint 3.17)
    have h17 := lemma_3_1_20 c.relOpen c.isRetraction h0U hfill.filler
      (s := c.principal s) fun z hz => hs.mem_K hc (c.r_image ▸ hz)
    refine h17.congr_left c.relOpen c.isRetraction h0U fun z hz => ?_
    exact (c.principal_sectionAdd hfs hs.1 (c.r_image ▸ hz)).symm
  · -- the value at `0`
    simp only [map_add, ht₀0]
    rw [hs.toBase_principalLift hc (c.r_mem_O h0U), add_comm]
  · -- `(g + t̃) − (t̃ + t₀) = g − t₀` on `U`
    refine hconj.congr fun u hu => ?_
    simp only [map_add]
    rw [hs.toBase_principalLift hc (c.r_mem_O hu)]
    abel

/-- **Theorem 3.1.18 (preprint 3.15) (stability under sc⁺-perturbations)**: if `f` is an sc-Fredholm section of the
strong bundle `P : Y → X` and `s` is an sc⁺-section, then `f + s` is an sc-Fredholm section.
(The text assumes the bundle tame; tameness is not used.) -/
theorem _root_.Polyfold.theorem_3_1_18_wholeChart (hf : B.IsScFredholmSectionWholeChart f) (hs : B.IsScPlusSection s) :
    B.IsScFredholmSectionWholeChart (sectionAdd P f s) where
  isScSmooth := hf.isScSmooth.sectionAdd hs
  regularizing := regularizing_sectionAdd_wholeChart hf hs
  germ x hx := (hf.germ x hx).sectionAdd hf.isScSmooth.1 hs

end StrongBundle

end FredholmSections

end Polyfold
