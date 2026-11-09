import Polyfold.Chapter5.AuxNorm
import Polyfold.Chapter3.ParamPerturbation
import Polyfold.Chapter3.ParamPerturbationG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §5.3 (the start:
`Γ⁺(P)`, Definition 5.3.1 (preprint 5.9), Proposition 5.3.2 (preprint 5.10), **Lemma 5.3.3 (preprint 5.11)**, `Γ^{+,1}_U(P)`) and Appendix 5.4.2
(**Definitions 5.5.2, 5.5.6 (preprint 5.29, 5.33), Proposition 5.5.3 (preprint 5.30), Theorem 5.5.7 (preprint 5.34), Proposition 5.5.8 (preprint 5.35)**)
*(book 2017: Definition 5.7, Proposition 5.4, Lemma 5.3; Definitions 5.13, 5.15, Proposition 5.5,
Theorem 5.11, Proposition 5.6; see `BookConcordance.md`)*.

# Sc-smooth bump functions and the existence of sc⁺-sections

## The text, paraphrased

(§5.3) For an sc-Fredholm section `f` one studies `f + s`, `s ∈ Γ⁺(P)`; the supply of
sc⁺-sections comes from sc-smooth bump functions.  (Definition 5.3.1 (preprint 5.9)) `X` admits sc-smooth bump
functions if for every `x` and open `U(x)` there is an sc-smooth `f : X → ℝ` with `f ≠ 0` and
`supp(f) ⊆ U(x)`.  (Proposition 5.3.2 (preprint 5.10) = 5.30) Then there is an sc-smooth `f : X → [0, 1]` with
`f(x) = 1`, `supp(f) ⊆ U(x)`, and `f ≡ 1` near `x`; proof: `f = σ ∘ g` for a bump `g` with
`g(x) = 1` (sic) and `σ` "`0` for `s ≤ 1` and `1` for `s ≥ 1`", `f = σ(δ·g)`, `δ > 1`, for the
second claim.  (Lemma 5.3.3 (preprint 5.11)) For a tame strong bundle over a tame `X` admitting sc-smooth bump
functions, an auxiliary norm `N`, a smooth `x`, a smooth `e ∈ P⁻¹(x)`, `ε > 0` and an open `U ∋ x`,
there is `s ∈ Γ⁺(P)` with `s(x) = e`, `supp(s) ⊆ U` and `N(s(x)) < N(e) + ε`; proof: in a strong
bundle chart centred at `x`, `t(y) = R(y, ê)`, `N(t(y)) < N(e) + ε` for `|y|₀ < δ`, and
`s = β·t` for a bump `β` with `β(0) = 1` supported in `O' ∩ {|y|₀ < ε}`.  (After Lemma 5.3.3 (preprint 5.11))
`Γ^{+,1}_U(P)` is the set of `s ∈ Γ⁺(P)` with `supp(s) ⊆ U` and `N(s(x)) ≤ 1` for all `x`.
(Definition 5.5.2 (preprint 5.29)) "admits sc-smooth bump functions": `f` **not identically zero** with support in
`U(x)`.  For a Hilbert space `E`, `f(x) = β(‖x‖²)` is smooth, hence sc-smooth by Corollary 1.2.5 (preprint 1.20).
(Definition 5.5.6 (preprint 5.33)) A local model `(O, C, E)` has the sc-smooth bump function property if for every
`x ∈ O` and open `U(x) ⊆ O` with `cl_E(U(x)) ⊆ O` there is an sc-smooth `f : O → ℝ` with `f ≠ 0`
and `supp(f) ⊆ U(x)`.  (Theorem 5.5.7 (preprint 5.34), "clearly") `X` admits sc-smooth bump functions iff it has
an atlas whose local models have the bump property.  (Proposition 5.5.8 (preprint 5.35)) If `E₀` is a Hilbert space,
`(O, C, E)` has the bump property: `β(‖x‖²)`, scaled, translated, composed with the retraction.

## What is formalized

* **`ℝ` as an M-polyfold** (`Polyfold.realPolyfold`, the chart `realChart`); an sc-smooth function
  is `PX.IsScSmoothMap realPolyfold f`.  `MPolyfold.isScSmoothMap_of_local` (sc-smoothness of a
  map between M-polyfolds is checked in one pair of charts around each point, continuity
  included), `MPolyfold.IsScSmoothMap.real_chart`, `isScSmoothMap_real_of_local`,
  `isScSmoothMap_real_const`, `MPolyfold.IsScSmoothMap.comp_contDiff` (`σ ∘ f` for `C^∞` `σ`).
* `MPolyfold.AdmitsBumpFunctions` (**Definition 5.3.1 (preprint 5.9)**, read with `f(x) ≠ 0`),
  `MPolyfold.AdmitsBumpFunctionsWeak` (**Definition 5.5.2 (preprint 5.29)** as written) and
  `AdmitsBumpFunctions.weak`; `Polyfold.proposition_5_5_3` and `Polyfold.proposition_5_3_2`
  (**Propositions 5.5.3 and 5.3.2 (preprint 5.30 and 5.10)**: `f : X → [0, 1]`, `f(x) = 1`, `supp(f) ⊆ U`, `f ≡ 1` near `x`).
* `LocalModel.HasBumpProperty` (**Definition 5.5.6 (preprint 5.33)**), `Polyfold.theorem_5_5_7` (**Theorem 5.5.7 (preprint 5.34)**),
  `closure_inter_ball_subset` (a retract is closed near each of its points),
  `LocalModel.hasBumpProperty_of_quadratic` (the bump property when `κ‖v‖² ≤ b(v, v)` for a
  continuous bilinear `b`) and `Polyfold.proposition_5_5_8` (**Proposition 5.5.8 (preprint 5.35)**, `‖v‖² = b(v, v)`);
  `MPolyfold.admitsBumpFunctions_of_hilbert` (an M-polyfold built on sc-Hilbert spaces admits
  sc-smooth bump functions, the remark before Definition 5.3.1 (preprint 5.9)).
* **Sections**: `Polyfold.sectionSupport` (`supp(s)`), `StrongBundle.scPlusSections` (**`Γ⁺(P)`**),
  `StrongBundle.allowableSections` (**`Γ^{+,1}_U(P)`**), `IsScPlusSection.mem_oneSet`;
  `sectionSmul`, `sectionSum`; `StrongBundle.isScPlusSection_fiberZero` (the zero section),
  `StrongBundle.IsScPlusSection.smul_left` (**`f·s ∈ Γ⁺(P)` for sc-smooth `f` and `s ∈ Γ⁺(P)`**),
  `StrongBundle.IsScPlusSection.add` and `StrongBundle.isScPlusSection_sectionSum` (finite sums);
  `isScSmooth_const_of_mem_smooth`.
* `StrongBundle.cutoffSection` with `StrongBundle.isScPlusSection_cutoffSection` (**a local
  sc⁺-section `z ↦ (z, τ(z))` of `K[1] → O` cut off by a bump function supported in the chart
  domain and extended by `0` is an sc⁺-section**), and `Polyfold.lemma_5_3_3`
  (**Lemma 5.3.3 (preprint 5.11)**, with the bound at every point).

## What the text leaves implicit, and the choices made

* **Definition 5.3.1 (preprint 5.9) "`f ≠ 0`" against Definition 5.5.2 (preprint 5.29) "not identically zero".**  Proposition 5.5.3 (preprint 5.30)'s
  proof starts from "a bump function `g` with `g(0) = 1`" (meaning `g(x) = 1`), which needs
  `g(x) ≠ 0` at the given point; on an M-polyfold there are no translations to move a bump that is
  merely not identically zero to `x`.  `AdmitsBumpFunctions` is therefore Definition 5.3.1 (preprint 5.9) read as
  `f(x) ≠ 0`; it implies the reading of Definition 5.5.2 (preprint 5.29) (`AdmitsBumpFunctions.weak`), and it is the
  hypothesis of Proposition 5.5.3 (preprint 5.30), Theorem 5.5.7 (preprint 5.34) and Lemma 5.3.3 (preprint 5.11).  Definition 5.5.6 (preprint 5.33)'s "`f ≠ 0`" is read
  the same way, so that Theorem 5.5.7 (preprint 5.34) is an equivalence between the same notions.
* **Proposition 5.5.3 (preprint 5.30).**  The text's `σ` ("`0` for `s ≤ 1` and `1` for `s ≥ 1`") is misprinted, and
  `f = σ ∘ g` needs `g(x) = 1`, not given.  Here `f = τ(3g/g(x) − 1)`, `τ` Mathlib's
  `Real.smoothTransition` (`0` on `(−∞, 0]`, `1` on `[1, ∞)`): `f(x) = τ(2) = 1`, `f ≡ 1` where
  `g/g(x) > 2/3`, and `f ≠ 0` only where `g/g(x) > 1/3`, so `supp(f) ⊆ supp(g)`.
* **Theorem 5.5.7 (preprint 5.34), "⇐".**  "Clearly" hides the support condition: a bump `f₀` of the chart `φ`
  with `supp_O(f₀) ⊆ U(x)` and `cl_E(U(x)) ⊆ O` gives `f = f₀ ∘ φ` on `V`, but `cl_X(supp f)` may
  leave `V` (for example `X = E` a Hilbert space, `V` its open unit ball, `φ(u) = u/(1 − |u|²)`
  onto `O = E`, `U(x) = O` and `f₀ ≡ 1`: then `f` is `1` on `V` and `0` outside).  The proof
  here chooses `U₁ ∋ x` with `cl_X(U₁) ⊆ U ∩ V` (`X` is regular) and a ball `B(φ(x), r/2)` with
  `B(φ(x), r) ∩ O ⊆ φ(U₁)`; then `supp(f) ⊆ cl_X(U₁)`, and `f` extended by `0` is sc-smooth.
  The condition `cl_E(U(x)) ⊆ O` for the small ball holds because a retract is closed near its
  points (`closure_inter_ball_subset`: the retraction is continuous on its domain
  `C ∩ W'`, `C` is closed).  "⇒" uses every chart of `X`.
* **Proposition 5.5.8 (preprint 5.35).**  "`E₀` is a Hilbert space" is stated as: the norm of `E₀` comes from a
  continuous bilinear form, `‖v‖² = b(v, v)`; an `InnerProductSpace` instance on `E₀` would create a
  second, non-defeq `NormedSpace` structure next to the one of the sc-scale.  The proof uses only
  that `v ↦ b(v − x, v − x)` is `C^∞` and dominates `κ‖v − x‖²`
  (`LocalModel.hasBumpProperty_of_quadratic`, which also covers spaces isomorphic to a Hilbert
  space); `f(v) = τ(1 − b(v − x, v − x)/ρ)` is `C^∞` on `E₀`, hence sc-smooth on `E` (Corollary
  1.20 from the base level, `IsScSmooth.of_contDiffOn_finiteDimensional`), and `f ∘ r` for every
  retraction `r` onto `O`.
* **The product rule.**  "`β·t` is an sc⁺-section" needs the product of an sc-smooth function and
  an sc⁺-section, which the text does not state; in a chart of the atlas it is the product rule of
  the sc-calculus (`IsScSmooth.smul`) for `(f ∘ φ⁻¹)·ŝ`.  Lemma 5.3.3 (preprint 5.11) needs a local version: `t` is
  defined only on the chart domain, so the section is the cut-off `cutoffSection` (sc⁺ on the chart
  domain through `Φ[1]`, the zero section off `supp(β)`, and these two open sets cover `X`).
* **Lemma 5.3.3 (preprint 5.11).**  (a) The bound `N(s(x)) < N(e) + ε` "at `x`" is trivial (`s(x) = e`); the bound
  proved, and needed for `Γ^{+,1}_U` in §5.3, is `N(s(y)) < N(e) + ε` for **all** `y`, and the
  text's proof gives it, with `ε` reused for the radius `δ`.  (b) **Tameness, the normality of
  `X` and a chart centred at `x` are not needed**: any strong bundle chart of the atlas around
  `x` works, with `t(y) = Φ⁻¹(R(φ(y), ê))`, `ê = Φ(e)₂ ∈ F_∞` (smoothness of `e` gives a constant
  `ê₁ ∈ (F¹)_∞`, so `z ↦ R[1](z, ê₁)` is sc-smooth into `K[1]`); `β` is a bump with `β(x) = 1`
  supported in `U` and in the open set where `N(t(y)) < N(e) + ε` (continuity of `N` on `Y[1]`
  and of `t` into `Y[1]`).  `N(s(y)) = β(y)·N(t(y)) ≤ N(t(y))` because `β ∈ [0, 1]` and `N` is a
  norm on the fibres.
  (c) The hypothesis that `x` is smooth is kept (the text's), but it follows from `e` smooth.
* `Γ^{+,1}_U(P)` is stated with `N(s(x)) ≤ 1` at every `x`, which is meaningful because sc⁺-sections
  take values in `Y_{0,1}` (`IsScPlusSection.mem_oneSet`).  The text's metric
  `ρ(s, s') = sup N(s(x) − s'(x))` on it is not formalized.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v w

/-! ### The real line as an M-polyfold; sc-smooth functions -/

section RealLine

/-- `ℝ` with the constant sc-structure. -/
abbrev realSc : ScBanach := ScBanach.const ℝ

lemma real_relOpen_univ : IsRelOpenInQuadrant realSc univ univ :=
  ⟨isPartialQuadrant_univ _, univ, isOpen_univ, (inter_univ _).symm⟩

/-- The identity chart of `ℝ`, modelled on `(ℝ, ℝ, ℝ)`. -/
def realChart : MChart ℝ where
  model := LocalModel.ofRelOpen real_relOpen_univ
  toPartialEquiv := (Equiv.refl ℝ).toPartialEquiv
  isOpen_source := isOpen_univ
  target_eq := rfl
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn

@[simp] lemma realChart_apply (r : ℝ) : realChart r = r := rfl

@[simp] lemma realChart_symm_apply (r : ℝ) : realChart.symm r = r := rfl

lemma realChart_compatible : realChart.Compatible realChart := MChart.compatible_self _

/-- **`ℝ` as an M-polyfold**, with the single chart `id`; an **sc-smooth function** on an
M-polyfold `X` is an sc-smooth map `X → ℝ` (Definition 2.3.8 (preprint 2.14)). -/
def realPolyfold : MPolyfold ℝ where
  atlas :=
    { charts := {realChart}
      compatible := fun φ hφ ψ hψ => by
        rw [mem_singleton_iff.1 hφ, mem_singleton_iff.1 hψ]
        exact realChart_compatible
      cover := fun r => ⟨realChart, mem_singleton _, mem_univ r⟩ }

lemma isChart_realChart : realPolyfold.IsChart realChart := by
  intro ψ hψ
  rw [mem_singleton_iff.1 hψ]
  exact realChart_compatible

end RealLine

section Locality

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}

/-- **Sc-smoothness of a map between M-polyfolds is local and may be checked in one pair of charts
around each point** (Definition 2.3.8 (preprint 2.14); continuity follows from the local representatives). -/
theorem MPolyfold.isScSmoothMap_of_local {f : X → Z}
    (h : ∀ x, ∃ (φ : MChart X) (ψ : MChart Z) (V : Set X), PX.IsChart φ ∧ PZ.IsChart ψ ∧
      IsOpen V ∧ x ∈ V ∧ V ⊆ φ.source ∧ MapsTo f V ψ.source ∧
      IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V) ψ.model.E ψ.model.C ψ.model.O
        (ψ ∘ f ∘ φ.symm)) :
    PX.IsScSmoothMap PZ f := by
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun x => by
    obtain ⟨φ, ψ, V, -, -, hVo, hxV, hVφ, hfV, hrep⟩ := h x
    have h1 := hrep.continuousOn (φ.isScRetract_image hVφ hVo)
    have h2 : ContinuousOn (ψ.symm ∘ (ψ ∘ f ∘ φ.symm) ∘ φ) V :=
      ψ.continuousOn_invFun.comp (h1.comp (φ.continuousOn_toFun.mono hVφ)
        fun y hy => mem_image_of_mem _ hy) fun y hy => by
          simp only [Function.comp_apply, φ.symm_apply_apply (hVφ hy)]
          exact ψ.mapsTo_model _ (hfV hy)
    have h3 : ContinuousOn f V := h2.congr fun y hy => by
      simp only [Function.comp_apply, φ.symm_apply_apply (hVφ hy), ψ.symm_apply_apply (hfV hy)]
    exact h3.continuousAt (hVo.mem_nhds hxV)
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ hcont.continuousOn fun x _ => ?_
  obtain ⟨φ, ψ, V, hφ, hψ, hVo, hxV, hVφ, hfV, hrep⟩ := h x
  exact ⟨φ, ψ, V, hφ, hψ, hVo, hxV, fun y hy => ⟨mem_univ _, hVφ hy⟩, hfV, hrep⟩

/-- An sc-smooth function `f : X → ℝ` read in a chart `φ` of `X`: `f ∘ φ⁻¹` is sc-smooth on the
retract `O` of the chart. -/
theorem MPolyfold.IsScSmoothMap.real_chart {f : X → ℝ} (hf : PX.IsScSmoothMap realPolyfold f)
    {φ : MChart X} (hφ : PX.IsChart φ) :
    IsScSmoothRetractMap φ.model.E φ.model.C φ.model.O realSc univ univ (f ∘ φ.symm) := by
  have h := hf.smooth φ realChart hφ isChart_realChart φ.source φ.isOpen_source
    (fun x hx => ⟨mem_univ _, hx⟩) (mapsTo_univ _ _)
  rw [φ.image_source] at h
  exact h

/-- A function which near every point is, in some chart, sc-smooth on the retract is an
sc-smooth function. -/
theorem isScSmoothMap_real_of_local {f : X → ℝ}
    (h : ∀ x, ∃ (φ : MChart X) (V : Set X), PX.IsChart φ ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ φ.source ∧
      IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V) realSc univ univ (f ∘ φ.symm)) :
    PX.IsScSmoothMap realPolyfold f := by
  refine MPolyfold.isScSmoothMap_of_local fun x => ?_
  obtain ⟨φ, V, hφ, hVo, hxV, hVφ, hrep⟩ := h x
  exact ⟨φ, realChart, V, hφ, isChart_realChart, hVo, hxV, hVφ, mapsTo_univ _ _, hrep⟩

/-- A constant function is sc-smooth. -/
theorem isScSmoothMap_real_const (a : ℝ) : PX.IsScSmoothMap realPolyfold fun _ => a := by
  refine isScSmoothMap_real_of_local fun x => ?_
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source x
  refine ⟨φ, φ.source, hφ, φ.isOpen_source, hx, subset_rfl, ?_⟩
  rw [φ.image_source]
  refine ⟨mapsTo_univ _ _, fun R _ => ?_⟩
  exact IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) R.isScDomain contDiffOn_const

/-- A `C^∞` function `σ : ℝ → ℝ` is an sc-smooth self-map of the M-polyfold `ℝ`. -/
theorem isScSmoothMap_real_of_contDiff {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) :
    realPolyfold.IsScSmoothMap realPolyfold σ := by
  refine MPolyfold.isScSmoothMap_of_local fun x => ⟨realChart, realChart, univ, isChart_realChart,
    isChart_realChart, isOpen_univ, mem_univ x, subset_univ _, mapsTo_univ _ _, ?_⟩
  change IsScSmoothRetractMap realSc univ (id '' univ) realSc univ univ σ
  rw [image_id]
  exact isScSmoothRetractMap_const_of_contDiff (V := ℝ) (V' := ℝ) hσ

/-- **`σ ∘ f` is sc-smooth** for an sc-smooth function `f` and a `C^∞` function `σ : ℝ → ℝ`. -/
theorem MPolyfold.IsScSmoothMap.comp_contDiff {f : X → ℝ} (hf : PX.IsScSmoothMap realPolyfold f)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) : PX.IsScSmoothMap realPolyfold (σ ∘ f) :=
  MPolyfold.IsScSmoothMap.comp (isScSmoothMap_real_of_contDiff hσ) hf

end Locality

/-! ### Definitions 5.3.1 and 5.5.2 (preprint 5.9 and 5.29) and Propositions 5.3.2 and 5.5.3 (preprint 5.10 and 5.30): sc-smooth bump functions -/

section Bump

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)

/-- **Definition 5.3.1 (preprint 5.9)**: the M-polyfold `X` **admits sc-smooth bump functions** if for every
`x ∈ X` and every open neighbourhood `U` of `x` there is an sc-smooth `f : X → ℝ` with
`supp(f) ⊆ U` and `f ≠ 0`, the latter read as **`f(x) ≠ 0`** (the reading Proposition 5.5.3 (preprint 5.30)'s proof
uses; Definition 5.5.2 (preprint 5.29) reads "not identically zero", `AdmitsBumpFunctionsWeak`). -/
def MPolyfold.AdmitsBumpFunctions : Prop :=
  ∀ x (U : Set X), IsOpen U → x ∈ U →
    ∃ f : X → ℝ, PX.IsScSmoothMap realPolyfold f ∧ f x ≠ 0 ∧ tsupport f ⊆ U

/-- **Definition 5.5.2 (preprint 5.29)** as written: for every `x` and every open neighbourhood `U` of `x` there is
an sc-smooth `f : X → ℝ` **not identically zero** with `supp(f) ⊆ U`. -/
def MPolyfold.AdmitsBumpFunctionsWeak : Prop :=
  ∀ x (U : Set X), IsOpen U → x ∈ U →
    ∃ f : X → ℝ, PX.IsScSmoothMap realPolyfold f ∧ f ≠ 0 ∧ tsupport f ⊆ U

variable {PX}

/-- The reading of Definition 5.3.1 (preprint 5.9) implies that of Definition 5.5.2 (preprint 5.29). -/
theorem MPolyfold.AdmitsBumpFunctions.weak (h : PX.AdmitsBumpFunctions) :
    PX.AdmitsBumpFunctionsWeak := fun x U hU hx => by
  obtain ⟨f, hf, hfx, hsupp⟩ := h x U hU hx
  exact ⟨f, hf, fun h0 => hfx (congrFun h0 x), hsupp⟩

/-- **Proposition 5.5.3 (preprint 5.30)** (= Proposition 5.10): if `X` admits sc-smooth bump functions, then for
every `x` and every open neighbourhood `U` of `x` there is an sc-smooth `f : X → [0, 1]` with
`f(x) = 1` and `supp(f) ⊆ U`, and `f ≡ 1` near `x`.  (The text's `σ`, "`0` for `s ≤ 1` and `1`
for `s ≥ 1`", is misprinted; here `f = σ ∘ g` with `σ(s) = τ(3s/g(x) − 1)`, `τ` the smooth
transition from `0` on `(−∞, 0]` to `1` on `[1, ∞)`.) -/
theorem proposition_5_5_3 (h : PX.AdmitsBumpFunctions) {x : X} {U : Set X} (hU : IsOpen U)
    (hx : x ∈ U) :
    ∃ f : X → ℝ, PX.IsScSmoothMap realPolyfold f ∧ (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧ f x = 1 ∧
      tsupport f ⊆ U ∧ ∀ᶠ y in 𝓝 x, f y = 1 := by
  obtain ⟨g, hg, hgx, hsupp⟩ := h x U hU hx
  set σ : ℝ → ℝ := fun s => Real.smoothTransition (3 * s / g x - 1) with hσ
  have hσc : ContDiff ℝ ∞ σ :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp
      (((contDiff_const.mul contDiff_id).div_const _).sub contDiff_const)
  have hσ0 : σ 0 = 0 := by
    simp only [hσ, mul_zero, zero_div, zero_sub]
    exact Real.smoothTransition.zero_of_nonpos (by norm_num)
  refine ⟨σ ∘ g, hg.comp_contDiff hσc, fun y => ⟨Real.smoothTransition.nonneg _,
    Real.smoothTransition.le_one _⟩, ?_, (tsupport_comp_subset hσ0 g).trans hsupp, ?_⟩
  · simp only [Function.comp_apply, hσ]
    rw [mul_div_assoc, div_self hgx]
    exact Real.smoothTransition.one_of_one_le (by norm_num)
  · have hcont : ContinuousAt (fun y => g y / g x) x :=
      (hg.continuousOn.continuousAt (isOpen_univ.mem_nhds (mem_univ x))).div_const _
    have h1 : g x / g x = 1 := div_self hgx
    have hev : ∀ᶠ y in 𝓝 x, (2 : ℝ) / 3 < g y / g x :=
      hcont.eventually (lt_mem_nhds (by change (2 : ℝ) / 3 < g x / g x; rw [h1]; norm_num))
    filter_upwards [hev] with y hy
    simp only [Function.comp_apply, hσ]
    refine Real.smoothTransition.one_of_one_le ?_
    rw [mul_div_assoc]
    linarith

/-- **Proposition 5.3.2 (preprint 5.10)**: the statement of Proposition 5.5.3 (preprint 5.30). -/
theorem proposition_5_3_2 (h : PX.AdmitsBumpFunctions) {x : X} {U : Set X} (hU : IsOpen U)
    (hx : x ∈ U) :
    ∃ f : X → ℝ, PX.IsScSmoothMap realPolyfold f ∧ (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧ f x = 1 ∧
      tsupport f ⊆ U ∧ ∀ᶠ y in 𝓝 x, f y = 1 :=
  proposition_5_5_3 h hU hx

end Bump

/-! ### Definition 5.5.6 (preprint 5.33), Theorem 5.5.7 (preprint 5.34), Proposition 5.5.8 (preprint 5.35): the bump property of local models -/

section LocalBump

/-- **Definition 5.5.6 (preprint 5.33)**: the local model `(O, C, E)` has the **sc-smooth bump function property**
if for every `x ∈ O` and every open neighbourhood `U(x) = O ∩ W` of `x` in `O` with
`cl_E(U(x)) ⊆ O` there is an sc-smooth `f : O → ℝ` with `f ≠ 0`, read as `f(x) ≠ 0` (as in
Definition 5.3.1 (preprint 5.9)), and `supp(f) ⊆ U(x)`, the support taken in `O`. -/
def LocalModel.HasBumpProperty (M : LocalModel) : Prop :=
  ∀ x ∈ M.O, ∀ W : Set (M.E 0), IsOpen W → x ∈ W → closure (M.O ∩ W) ⊆ M.O →
    ∃ f : M.E 0 → ℝ, IsScSmoothRetractMap M.E M.C M.O realSc univ univ f ∧ f x ≠ 0 ∧
      closure (M.O ∩ support f) ∩ M.O ⊆ W

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- A retract is closed near each of its points: `O ∩ cl(B(z, r/2)) ⊆ O` when `B(z, r)` lies in
the open set `W'` with `U = C ∩ W'` the domain of a retraction onto `O`. -/
lemma closure_inter_ball_subset {M : LocalModel} {z : M.E 0} {r : ℝ} (R : ScRetraction M.E M.C)
    (hR : R.retract = M.O) {W' : Set (M.E 0)} (hW' : R.U = W' ∩ M.C)
    (hball : Metric.ball z r ⊆ W') : closure (M.O ∩ Metric.ball z (r / 2)) ⊆ M.O := by
  intro p hp
  have hOC : M.O ⊆ M.C := fun y hy => by
    rw [← hR] at hy
    have := R.retract_subset hy
    rw [hW'] at this; exact this.2
  have hpC : p ∈ M.C :=
    R.relOpen.isPartialQuadrant.isClosed.closure_subset_iff.2 (inter_subset_left.trans hOC)
      hp
  have hpb : p ∈ Metric.closedBall z (r / 2) :=
    (closure_mono inter_subset_right).trans Metric.closure_ball_subset_closedBall hp
  have hr : 0 ≤ r := by
    have := Metric.mem_closedBall.1 hpb
    linarith [dist_nonneg (x := p) (y := z)]
  have hpW' : p ∈ W' := by
    refine hball (Metric.mem_ball.2 ?_)
    have := Metric.mem_closedBall.1 hpb
    rcases hr.lt_or_eq with hr' | hr'
    · linarith
    · subst hr'
      have hO : M.O ∩ Metric.ball z (0 / 2) = ∅ := by
        rw [zero_div, Metric.ball_zero, inter_empty]
      rw [hO, closure_empty] at hp
      exact absurd hp (notMem_empty p)
  have hpU : p ∈ R.U := by rw [hW']; exact ⟨hpW', hpC⟩
  have hsub : M.O ∩ Metric.ball z (r / 2) ⊆ R.U := fun y hy => R.retract_subset (hR ▸ hy.1)
  have hfix : EqOn R id (insert p (M.O ∩ Metric.ball z (r / 2))) := by
    refine EqOn.of_subset_closure (s := M.O ∩ Metric.ball z (r / 2))
      (fun y hy => R.apply_eq_self_of_mem_retract (hR ▸ hy.1))
      (R.isSc1.isSc0.continuousOn_base.mono (insert_subset hpU hsub)) continuousOn_id
      (subset_insert _ _) (insert_subset hp subset_closure)
  rw [← hR]
  exact R.mem_retract_iff.2 ⟨hpU, hfix (mem_insert p _)⟩

/-- **Theorem 5.5.7 (preprint 5.34)**: `X` admits sc-smooth bump functions if and only if it admits an sc-smooth
atlas (a family of charts of `X` covering `X`) whose local models have the sc-smooth bump function
property.  ("Clearly"; for "⇐" the bump `f₀` of a chart is supported in a small ball
`B(φ(x), r/2)` with `φ⁻¹(B(φ(x), r) ∩ O)` inside a neighbourhood `U₁` of `x` with
`cl_X(U₁) ⊆ U ∩ V`, so that `cl_X(supp f) ⊆ U` and the extension by `0` is sc-smooth; the text's
`cl_C(V) ⊆ O` alone gives neither.) -/
theorem theorem_5_5_7 :
    PX.AdmitsBumpFunctions ↔ ∃ S : Set (MChart X), (∀ φ ∈ S, PX.IsChart φ) ∧
      (∀ x, ∃ φ ∈ S, x ∈ φ.source) ∧ ∀ φ ∈ S, φ.model.HasBumpProperty := by
  constructor
  · -- every chart of `X` has the bump property
    intro h
    refine ⟨{φ | PX.IsChart φ}, fun φ hφ => hφ, fun x => PX.exists_isChart_mem_source x,
      fun φ hφ => ?_⟩
    intro z hz W hW hzW _
    set U := φ.source ∩ φ ⁻¹' W with hUdef
    have hUo : IsOpen U := φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source hW
    have hxU : φ.symm z ∈ U := ⟨φ.symm_mapsTo hz, by
      rw [mem_preimage, φ.apply_symm_apply hz]; exact hzW⟩
    obtain ⟨f, hf, hfx, hsupp⟩ := h (φ.symm z) U hUo hxU
    refine ⟨f ∘ φ.symm, hf.real_chart hφ, hfx, fun p hp => ?_⟩
    have hcw : ContinuousWithinAt φ.symm (φ.model.O ∩ support (f ∘ φ.symm)) p :=
      (φ.continuousOn_invFun p hp.2).mono inter_subset_left
    have h1 := hcw.mem_closure_image hp.1
    have h2 : φ.symm '' (φ.model.O ∩ support (f ∘ φ.symm)) ⊆ support f := by
      rintro _ ⟨z', hz', rfl⟩; exact hz'.2
    have h3 : φ.symm p ∈ U := hsupp (closure_mono h2 h1)
    have := h3.2
    rwa [mem_preimage, φ.apply_symm_apply hp.2] at this
  · rintro ⟨S, hS, hcov, hbump⟩ x U hU hx
    obtain ⟨φ, hφS, hxφ⟩ := hcov x
    have hφ := hS φ hφS
    -- a neighbourhood `U₁` of `x` with `cl_X(U₁) ⊆ U ∩ V`
    obtain ⟨t, ht, htc, htsub⟩ :=
      exists_mem_nhds_isClosed_subset ((hU.inter φ.isOpen_source).mem_nhds ⟨hx, hxφ⟩)
    set U₁ := interior t with hU₁
    have hxU₁ : x ∈ U₁ := mem_interior_iff_mem_nhds.2 ht
    have hU₁cl : closure U₁ ⊆ U ∩ φ.source :=
      (closure_minimal interior_subset htc).trans htsub
    have hU₁V : U₁ ⊆ φ.source := subset_closure.trans (hU₁cl.trans inter_subset_right)
    obtain ⟨W₁, hW₁o, hW₁⟩ := φ.exists_isOpen_image_eq hU₁V isOpen_interior
    set z := φ x with hz
    have hzW₁ : z ∈ W₁ := by
      have : z ∈ φ '' U₁ := ⟨x, hxU₁, rfl⟩
      rw [hW₁] at this; exact this.2
    have hzO : z ∈ φ.model.O := φ.mapsTo_model x hxφ
    -- a small ball around `z`
    obtain ⟨R₀, hR₀⟩ := φ.model.isScRetract
    obtain ⟨W', hW'o, hW'eq⟩ := R₀.relOpen.relOpen
    have hzW' : z ∈ W' := by
      have : z ∈ R₀.U := R₀.retract_subset (hR₀ ▸ hzO)
      rw [hW'eq] at this; exact this.1
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hW₁o.inter hW'o) z ⟨hzW₁, hzW'⟩
    have hclos := closure_inter_ball_subset R₀ hR₀ hW'eq (hball.trans inter_subset_right)
    obtain ⟨f₀, hf₀, hf₀z, hf₀supp⟩ := hbump φ hφS z hzO (Metric.ball z (r / 2))
      Metric.isOpen_ball (Metric.mem_ball_self (by positivity)) hclos
    -- the extension by zero
    set f : X → ℝ := φ.source.indicator (f₀ ∘ φ) with hfdef
    have hsuppf : support f ⊆ U₁ := by
      intro y hy
      have hyV : y ∈ φ.source := by
        by_contra hyV; exact hy (indicator_of_notMem hyV _)
      have hfy : f₀ (φ y) ≠ 0 := by
        have := mem_support.1 hy; rwa [hfdef, indicator_of_mem hyV] at this
      have h1 : φ y ∈ Metric.ball z (r / 2) :=
        hf₀supp ⟨subset_closure ⟨φ.mapsTo_model y hyV, hfy⟩, φ.mapsTo_model y hyV⟩
      have h2 : φ y ∈ W₁ :=
        (hball (Metric.ball_subset_ball (by linarith) h1)).1
      have h3 : φ y ∈ φ '' U₁ := by rw [hW₁]; exact ⟨φ.mapsTo_model y hyV, h2⟩
      obtain ⟨y', hy', hyy'⟩ := h3
      rwa [φ.toPartialEquiv.injOn (hU₁V hy') hyV hyy'] at hy'
    have htsupp : tsupport f ⊆ U ∩ φ.source := (closure_mono hsuppf).trans hU₁cl
    refine ⟨f, ?_, ?_, htsupp.trans inter_subset_left⟩
    · refine isScSmoothMap_real_of_local fun y => ?_
      by_cases hy : y ∈ φ.source
      · refine ⟨φ, φ.source, hφ, φ.isOpen_source, hy, subset_rfl, ?_⟩
        rw [φ.image_source]
        refine hf₀.congr fun z' hz' => ?_
        simp only [Function.comp_apply, hfdef, indicator_of_mem (φ.symm_mapsTo hz'),
          φ.apply_symm_apply hz']
      · obtain ⟨ψ, hψ, hyψ⟩ := PX.exists_isChart_mem_source y
        have hyt : y ∉ tsupport f := fun h => hy (htsupp h).2
        refine ⟨ψ, ψ.source ∩ (tsupport f)ᶜ, hψ,
          ψ.isOpen_source.inter (isClosed_tsupport f).isOpen_compl, ⟨hyψ, hyt⟩,
          inter_subset_left, ⟨mapsTo_univ _ _, fun R hR => ?_⟩⟩
        refine IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) R.isScDomain
          (contDiffOn_const (c := (0 : ℝ)).congr fun u hu => ?_)
        obtain ⟨y', hy', hy'eq⟩ : R u ∈ ψ '' (ψ.source ∩ (tsupport f)ᶜ) :=
          hR ▸ R.apply_mem_retract hu
        simp only [Function.comp_apply, ← hy'eq, ψ.symm_apply_apply hy'.1]
        exact image_eq_zero_of_notMem_tsupport hy'.2
    · simp only [hfdef, indicator_of_mem hxφ, Function.comp_apply]
      exact hf₀z

/-- **Proposition 5.5.8 (preprint 5.35)** in the form the proof uses: if the norm of `E₀` is dominated by a
continuous quadratic form, `κ‖v‖² ≤ b(v, v)` (`E₀` is Hilbertable), then `(O, C, E)` has the
sc-smooth bump function property: `f(v) = τ(1 − b(v − x, v − x)/ρ)` (`τ` the smooth transition)
is `C^∞` on `E₀`, hence sc-smooth (Corollary 1.2.5 (preprint 1.20)), with `f(x) = 1` and support in a small ball;
"using scaling, translating, and composition with the sc-smooth retraction onto `O`". -/
theorem LocalModel.hasBumpProperty_of_quadratic (M : LocalModel)
    (b : M.E 0 →L[ℝ] M.E 0 →L[ℝ] ℝ) {κ : ℝ} (hκ : 0 < κ) (hb : ∀ v, κ * ‖v‖ ^ 2 ≤ b v v) :
    M.HasBumpProperty := by
  intro x _ W hW hxW _
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW x hxW
  set ρ := κ * (r / 2) ^ 2 with hρ
  have hρpos : 0 < ρ := by positivity
  set q : M.E 0 → ℝ := fun v => b (v - x) (v - x) with hq
  set f : M.E 0 → ℝ := fun v => Real.smoothTransition (1 - q v / ρ) with hf
  have hqc : ContDiff ℝ ∞ q :=
    b.isBoundedBilinearMap.contDiff.comp
      ((contDiff_id.sub contDiff_const).prodMk (contDiff_id.sub contDiff_const))
  have hfc : ContDiff ℝ ∞ f :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub (hqc.div_const _))
  have hfsc : IsScSmooth (E := M.E) (F := realSc) univ f :=
    IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) (isScDomain_univ _) hfc.contDiffOn
  refine ⟨f, ⟨mapsTo_univ _ _, fun R _ => IsScSmooth.comp R.isScDomain (isScDomain_univ _) hfsc
    R.isScSmooth (mapsTo_univ _ _)⟩, ?_, ?_⟩
  · have : f x = 1 := by
      simp only [hf, hq, sub_self, map_zero, zero_div, sub_zero]
      exact Real.smoothTransition.one_of_one_le le_rfl
    rw [this]; exact one_ne_zero
  · have hsupp : support f ⊆ Metric.ball x (r / 2) := by
      intro v hv
      have h1 : 0 < 1 - q v / ρ := by
        by_contra h
        exact hv (Real.smoothTransition.zero_of_nonpos (not_lt.1 h))
      have h2 : q v < ρ := (div_lt_one hρpos).1 (sub_pos.1 h1)
      have h3 : κ * ‖v - x‖ ^ 2 < κ * (r / 2) ^ 2 := (hb (v - x)).trans_lt h2
      have h4 : ‖v - x‖ ^ 2 < (r / 2) ^ 2 := lt_of_mul_lt_mul_left h3 hκ.le
      have h5 : ‖v - x‖ < r / 2 :=
        lt_of_pow_lt_pow_left₀ 2 (by positivity) h4
      rw [Metric.mem_ball, dist_eq_norm]; exact h5
    intro p hp
    have h1 : p ∈ Metric.closedBall x (r / 2) :=
      ((closure_mono (inter_subset_right.trans hsupp)).trans
        Metric.closure_ball_subset_closedBall) hp.1
    exact hball (Metric.closedBall_subset_ball (by linarith) h1)

/-- **Proposition 5.5.8 (preprint 5.35)**: if the `0`-level `E₀` of the sc-Banach space `E` is a Hilbert space
(its norm comes from a continuous symmetric bilinear form `b`, `‖v‖² = b(v, v)`), the local model
`(O, C, E)` has the sc-smooth bump function property. -/
theorem proposition_5_5_8 (M : LocalModel)
    (hH : ∃ b : M.E 0 →L[ℝ] M.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v) : M.HasBumpProperty := by
  obtain ⟨b, hb⟩ := hH
  exact M.hasBumpProperty_of_quadratic b one_pos fun v => by rw [one_mul, hb]

/-- **An M-polyfold built on sc-Hilbert spaces admits sc-smooth bump functions** (§5.3, before
Definition 5.3.1 (preprint 5.9): "This is, for example, the case if `X` is built on sc-Hilbert spaces"):
Proposition 5.5.8 (preprint 5.35) in the charts and Theorem 5.5.7 (preprint 5.34). -/
theorem MPolyfold.admitsBumpFunctions_of_hilbert
    (h : ∀ x, ∃ φ : MChart X, PX.IsChart φ ∧ x ∈ φ.source ∧
      ∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v) :
    PX.AdmitsBumpFunctions := by
  refine theorem_5_5_7.2 ⟨{φ | PX.IsChart φ ∧ ∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ,
    ∀ v, ‖v‖ ^ 2 = b v v}, fun φ hφ => hφ.1, fun x => ?_, fun φ hφ => proposition_5_5_8 _ hφ.2⟩
  obtain ⟨φ, hφ, hx, hb⟩ := h x
  exact ⟨φ, ⟨hφ, hb⟩, hx⟩

end LocalBump

/-! ### Sections: supports, `Γ⁺(P)`, `Γ^{+,1}_U(P)`, products and sums -/

section Sections

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A constant map with a smooth value is sc-smooth. -/
theorem isScSmooth_const_of_mem_smooth {G F : ScBanach} {V : Set (G 0)} (hV : IsScDomain G V)
    {k : F 0} (hk : k ∈ F.smooth) : IsScSmooth (E := G) (F := F) V fun _ => k := by
  refine IsScSmooth.of_contDiffOn_levels hV (fun m _ _ => F.mem_smooth_iff.1 hk m) fun m => ?_
  obtain ⟨y, hy⟩ := F.mem_smooth_iff.1 hk m
  have : ∀ z ∈ G.lvlSet V m, levelMap (E := G) (F := F) (fun _ => k) m z = y :=
    fun z _ => levelMap_eq_of_toBase_eq hy
  exact contDiffOn_const.congr this

variable (P) in
/-- The **support** `supp(s) = cl{x ∈ X | s(x) ≠ 0_x}` of a section `s` (§5.3). -/
def sectionSupport (s : X → Y) : Set X := closure {x | s x ≠ fiberZero P x}

open scoped Classical in
variable (P) in
/-- The product `f·s` of a function `f : X → ℝ` and a section `s`, in the fibres (junk where `s`
is not a section). -/
def sectionSmul (f : X → ℝ) (s : X → Y) (x : X) : Y :=
  if h : P (s x) = x then ((f x • (⟨s x, h⟩ : P ⁻¹' {x}) : P ⁻¹' {x}) : Y) else s x

open scoped Classical in
variable (P) in
/-- The finite sum `Σ_{i ∈ I} sᵢ` of sections, in the fibres. -/
def sectionSum {ι : Type*} (I : Finset ι) (s : ι → X → Y) (x : X) : Y :=
  if h : ∀ i, P (s i x) = x then ((∑ i ∈ I, (⟨s i x, h i⟩ : P ⁻¹' {x}) : P ⁻¹' {x}) : Y)
  else fiberZero P x

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
lemma sectionSmul_apply {f : X → ℝ} {s : X → Y} (hs : IsSection P s) (x : X) :
    sectionSmul P f s x = ((f x • (⟨s x, hs x⟩ : P ⁻¹' {x}) : P ⁻¹' {x}) : Y) := by
  rw [sectionSmul, dif_pos (hs x)]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
lemma IsSection.sectionSmul {f : X → ℝ} {s : X → Y} (hs : IsSection P s) :
    IsSection P (sectionSmul P f s) := fun x => by
  rw [sectionSmul_apply hs]; exact (f x • (⟨s x, hs x⟩ : P ⁻¹' {x}) : P ⁻¹' {x}).2

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
lemma sectionSum_apply {ι : Type*} {I : Finset ι} {s : ι → X → Y} (hs : ∀ i, IsSection P (s i))
    (x : X) :
    sectionSum P I s x = ((∑ i ∈ I, (⟨s i x, hs i x⟩ : P ⁻¹' {x}) : P ⁻¹' {x}) : Y) := by
  rw [sectionSum, dif_pos fun i => hs i x]

namespace StrongBundleChart

variable (c : StrongBundleChart PX P)

omit [T2Space Y] [ParacompactSpace Y] in
/-- `(u, 0) ∈ K` for `u ∈ O`. -/
lemma zero_mem_K {u : c.φ.model.E 0} (hu : u ∈ c.φ.model.O) : (u, 0) ∈ c.K := by
  rw [← c.image_source]
  have hy : P (fiberZero P (c.φ.symm u)) ∈ c.φ.source := by
    rw [proj_fiberZero P]; exact c.φ.symm_mapsTo hu
  refine ⟨fiberZero P (c.φ.symm u), c.mem_source_of_proj hy, Prod.ext ?_ ?_⟩
  · rw [c.fst_apply hy, proj_fiberZero P, c.φ.apply_symm_apply hu]
  · exact c.snd_fiberZero (c.φ.symm_mapsTo hu)

omit [T2Space Y] [ParacompactSpace Y] in
/-- `K[1]` has linear fibres. -/
lemma smul_mem_strongShiftOne {p : (c.φ.model.E.prod c.F.shift) 0} (hp : p ∈ strongShiftOne c.K)
    (t : ℝ) : (p.1, t • p.2) ∈ strongShiftOne c.K := by
  change (p.1, c.F.toBase 1 (t • p.2)) ∈ c.K
  rw [map_smul]; exact c.smul_mem_K hp t

omit [T2Space Y] [ParacompactSpace Y] in
lemma add_mem_strongShiftOne {u : c.φ.model.E 0} {a b : c.F 1}
    (ha : ((u, a) : (c.φ.model.E.prod c.F.shift) 0) ∈ strongShiftOne c.K)
    (hb : ((u, b) : (c.φ.model.E.prod c.F.shift) 0) ∈ strongShiftOne c.K) :
    ((u, a + b) : (c.φ.model.E.prod c.F.shift) 0) ∈ strongShiftOne c.K := by
  change (u, c.F.toBase 1 (a + b)) ∈ c.K
  rw [map_add]; exact c.add_mem_K ha hb

end StrongBundleChart

namespace StrongBundle

variable (B : StrongBundle PX P)

/-- **`Γ⁺(P)`**: the space of sc⁺-sections of `P` (Definition 2.6.6 (preprint 2.52)). -/
def scPlusSections : Set (X → Y) := {s | B.IsScPlusSection s}

/-- **`Γ^{+,1}_U(P)`** (§5.3, after Lemma 5.3.3 (preprint 5.11)): the sc⁺-sections `s` with `supp(s) ⊆ U` and
`N(s(x)) ≤ 1` for all `x`, for an auxiliary norm `N` and an open `U ⊆ X` (the "allowable
sc⁺-sections"). -/
def allowableSections (N : B.One → ℝ) (U : Set X) : Set (X → Y) :=
  {s | B.IsScPlusSection s ∧ sectionSupport P s ⊆ U ∧
    ∀ x (hx : s x ∈ B.oneSet), N (B.oneMk (s x) hx) ≤ 1}

variable {B}

/-- The values of an sc⁺-section lie in `Y_{0,1}` (so the condition `N(s(x)) ≤ 1` of
`Γ^{+,1}_U(P)` is a condition at every point). -/
lemma IsScPlusSection.mem_oneSet {s : X → Y} (hs : B.IsScPlusSection s) (x : X) :
    s x ∈ B.oneSet := by
  obtain ⟨-, g, hg, -⟩ := (B.isScPlusSection_iff s).1 hs
  rw [← hg]; exact B.oneVal_mem (g x)

omit [T2Space Y] [ParacompactSpace Y] in
/-- The local representative of an sc⁺-section in a chart of the atlas, on `O`. -/
lemma localRepOne_fst {s : X → Y} (hs : IsSection P s) {c : StrongBundleChart PX P}
    {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) : (localRepOne c s z).1 = z :=
  congrArg Prod.fst (c.apply_section hs hz)

lemma toBase_localRepOne_snd {s : X → Y} (hs : B.IsScPlusSection s) {c : StrongBundleChart PX P}
    (hc : c ∈ B.atlas.charts) {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) :
    c.F.toBase 1 (localRepOne c s z).2 = (c (s (c.φ.symm z))).2 :=
  Function.invFun_eq ((hs.2 c hc).1 _ (c.φ.symm_mapsTo hz))

/-- **The zero section is an sc⁺-section.** -/
theorem isScPlusSection_fiberZero : B.IsScPlusSection (fiberZero P) := by
  refine ⟨isSection_fiberZero, fun c hc => ⟨fun x hx => ?_, ?_⟩⟩
  · rw [c.snd_fiberZero hx]; exact ⟨0, map_zero _⟩
  · have hrep : EqOn (c.φ.model.E.prodInlOp c.F.shift 0) (localRepOne c (fiberZero P))
        c.φ.model.O := fun z hz => by
      change ((z, 0) : (c.φ.model.E.prod c.F.shift) 0) = c.liftOne (fiberZero P (c.φ.symm z))
      rw [liftOne_fiberZero (c.φ.symm_mapsTo hz), c.φ.apply_symm_apply hz]
    refine ((c.φ.model.E.prodInlOp c.F.shift).isScSmoothRetractMap c.φ.model.isScRetract
      fun z hz => ?_).congr hrep
    change (z, c.F.toBase 1 0) ∈ c.K
    rw [map_zero]; exact c.zero_mem_K hz

/-- **The product rule for sections**: `f·s` is an sc⁺-section for an sc-smooth function
`f : X → ℝ` and an sc⁺-section `s` (in a chart, `(f·s)^ = (f ∘ φ⁻¹)·ŝ`, and the product rule of
the sc-calculus, `IsScSmooth.smul`). -/
theorem IsScPlusSection.smul_left {f : X → ℝ} (hf : PX.IsScSmoothMap realPolyfold f)
    {s : X → Y} (hs : B.IsScPlusSection s) : B.IsScPlusSection (sectionSmul P f s) := by
  have hsec := hs.1
  have hval : ∀ (c : StrongBundleChart PX P) {x : X}, x ∈ c.φ.source →
      (c (sectionSmul P f s x)).2 = f x • (c (s x)).2 := fun c x hx => by
    rw [sectionSmul_apply hsec]
    exact (c.fiber_linear x hx).map_smul (f x) ⟨s x, hsec x⟩
  refine ⟨hsec.sectionSmul, fun c hc => ⟨fun x hx => ?_, ?_⟩⟩
  · rw [hval c hx]
    obtain ⟨a, ha⟩ := (hs.2 c hc).1 x hx
    exact ⟨f x • a, by rw [map_smul, ha]⟩
  · set L := localRepOne c s with hL
    set G : c.φ.model.E 0 → (c.φ.model.E.prod c.F.shift) 0 :=
      fun z => ((L z).1, f (c.φ.symm z) • (L z).2) with hG
    have hrep : EqOn G (localRepOne c (sectionSmul P f s)) c.φ.model.O := fun z hz => by
      have hzs := c.φ.symm_mapsTo hz
      refine Prod.ext ?_ (c.F.toBase_injective 1 ?_)
      · change (L z).1 = (c (sectionSmul P f s (c.φ.symm z))).1
        rw [localRepOne_fst hsec hz, c.fst_apply (by rw [hsec.sectionSmul]; exact hzs),
          hsec.sectionSmul, c.φ.apply_symm_apply hz]
      · change c.F.toBase 1 (f (c.φ.symm z) • (L z).2) =
          c.F.toBase 1 (Function.invFun (c.F.toBase 1) (c (sectionSmul P f s (c.φ.symm z))).2)
        rw [map_smul, toBase_localRepOne_snd hs hc hz, hval c hzs]
        obtain ⟨a, ha⟩ := (hs.2 c hc).1 _ hzs
        exact (Function.invFun_eq ⟨f (c.φ.symm z) • a, by rw [map_smul, ha]⟩).symm
    have hL1 := (hs.2 c hc).2
    have hf1 := hf.real_chart c.isChart
    refine IsScSmoothRetractMap.congr ⟨fun z hz => ?_, fun R hR => ?_⟩ hrep
    · exact c.smul_mem_strongShiftOne (hL1.mapsTo hz) _
    · have hU := R.isScDomain
      have h1 := hL1.comp_isScSmooth R hR
      have h2 := (hf1.comp_isScSmooth R hR).smul hU (h1.snd hU)
      exact ((h1.fst hU).scPair hU h2).congr hU fun _ _ => rfl

/-- **The sum of two sc⁺-sections is an sc⁺-section.** -/
theorem IsScPlusSection.add {s₁ s₂ : X → Y} (hs₁ : B.IsScPlusSection s₁)
    (hs₂ : B.IsScPlusSection s₂) : B.IsScPlusSection (sectionAdd P s₁ s₂) := by
  have h₁ := hs₁.1
  have h₂ := hs₂.1
  have hval : ∀ (c : StrongBundleChart PX P) {x : X}, x ∈ c.φ.source →
      (c (sectionAdd P s₁ s₂ x)).2 = (c (s₁ x)).2 + (c (s₂ x)).2 := fun c x hx => by
    rw [sectionAdd_apply h₁ h₂]; exact c.snd_add hx _ _
  refine ⟨h₁.sectionAdd h₂, fun c hc => ⟨fun x hx => ?_, ?_⟩⟩
  · rw [hval c hx]
    obtain ⟨a, ha⟩ := (hs₁.2 c hc).1 x hx
    obtain ⟨b, hb⟩ := (hs₂.2 c hc).1 x hx
    exact ⟨a + b, by rw [map_add, ha, hb]⟩
  · set L₁ := localRepOne c s₁
    set L₂ := localRepOne c s₂
    set G : c.φ.model.E 0 → (c.φ.model.E.prod c.F.shift) 0 :=
      fun z => ((L₁ z).1, (L₁ z).2 + (L₂ z).2) with hG
    have hrep : EqOn G (localRepOne c (sectionAdd P s₁ s₂)) c.φ.model.O := fun z hz => by
      have hzs := c.φ.symm_mapsTo hz
      refine Prod.ext ?_ (c.F.toBase_injective 1 ?_)
      · change (L₁ z).1 = (c (sectionAdd P s₁ s₂ (c.φ.symm z))).1
        rw [localRepOne_fst h₁ hz, c.fst_apply (by rw [h₁.sectionAdd h₂]; exact hzs),
          h₁.sectionAdd h₂, c.φ.apply_symm_apply hz]
      · change c.F.toBase 1 ((L₁ z).2 + (L₂ z).2) =
          c.F.toBase 1 (Function.invFun (c.F.toBase 1) (c (sectionAdd P s₁ s₂ (c.φ.symm z))).2)
        rw [map_add, toBase_localRepOne_snd hs₁ hc hz, toBase_localRepOne_snd hs₂ hc hz,
          hval c hzs]
        obtain ⟨a, ha⟩ := (hs₁.2 c hc).1 _ hzs
        obtain ⟨b, hb⟩ := (hs₂.2 c hc).1 _ hzs
        exact (Function.invFun_eq ⟨a + b, by rw [map_add, ha, hb]⟩).symm
    have hL₁ := (hs₁.2 c hc).2
    have hL₂ := (hs₂.2 c hc).2
    refine IsScSmoothRetractMap.congr ⟨fun z hz => ?_, fun R hR => ?_⟩ hrep
    · have ha := hL₁.mapsTo hz
      have hb := hL₂.mapsTo hz
      have e1 : localRepOne c s₁ z = (z, (localRepOne c s₁ z).2) :=
        Prod.ext (localRepOne_fst h₁ hz) rfl
      have e2 : localRepOne c s₂ z = (z, (localRepOne c s₂ z).2) :=
        Prod.ext (localRepOne_fst h₂ hz) rfl
      rw [e1] at ha; rw [e2] at hb
      change ((localRepOne c s₁ z).1, (localRepOne c s₁ z).2 + (localRepOne c s₂ z).2) ∈
        strongShiftOne c.K
      rw [localRepOne_fst h₁ hz]
      exact c.add_mem_strongShiftOne ha hb
    · have hU := R.isScDomain
      have g₁ := hL₁.comp_isScSmooth R hR
      have g₂ := hL₂.comp_isScSmooth R hR
      exact ((g₁.fst hU).scPair hU ((g₁.snd hU).add hU (g₂.snd hU))).congr hU fun _ _ => rfl

/-- **Finite sums of sc⁺-sections are sc⁺-sections.** -/
theorem isScPlusSection_sectionSum {ι : Type*} (I : Finset ι) {s : ι → X → Y}
    (hs : ∀ i, B.IsScPlusSection (s i)) : B.IsScPlusSection (sectionSum P I s) := by
  classical
  have hsec : ∀ i, IsSection P (s i) := fun i => (hs i).1
  induction I using Finset.induction_on with
  | empty =>
    have : sectionSum P (∅ : Finset ι) s = fiberZero P := funext fun x => by
      rw [sectionSum_apply hsec, Finset.sum_empty]; rfl
    rw [this]; exact isScPlusSection_fiberZero
  | insert a I ha ih =>
    have hI : IsSection P (sectionSum P I s) := fun x => by
      rw [sectionSum_apply hsec]
      exact ((∑ i ∈ I, (⟨s i x, hsec i x⟩ : P ⁻¹' {x})) : P ⁻¹' {x}).2
    have hfib : ∀ x, (⟨sectionSum P I s x, hI x⟩ : P ⁻¹' {x}) =
        ∑ i ∈ I, (⟨s i x, hsec i x⟩ : P ⁻¹' {x}) :=
      fun x => Subtype.ext (sectionSum_apply (I := I) hsec x)
    have : sectionSum P (insert a I) s = sectionAdd P (s a) (sectionSum P I s) := funext fun x => by
      rw [sectionAdd_apply (hsec a) hI, sectionSum_apply (I := insert a I) hsec,
        Finset.sum_insert ha, hfib]
    rw [this]; exact (hs a).add ih

end StrongBundle

end Sections

/-! ### Lemma 5.3.3 (preprint 5.11): existence of sc⁺-sections -/

section Existence

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace StrongBundle

open scoped Classical in
/-- **A local sc⁺-section cut off by a bump function and extended by `0`**: for a strong bundle
chart `Φ` and a map `τ : O → F₁` (the principal part of a section `z ↦ (z, τ(z))` of
`K[1] → O`), the section `y ↦ Φ⁻¹(φ(y), β(y)·τ(φ(y)))` on `dom φ`, `0_y` outside. -/
def cutoffSection (c : StrongBundleChart PX P) (β : X → ℝ) (τ : c.φ.model.E 0 → c.F 1) (y : X) :
    Y :=
  if y ∈ c.φ.source then c.toPartialEquiv.symm (c.φ y, c.F.toBase 1 (β y • τ (c.φ y)))
  else fiberZero P y

variable {c : StrongBundleChart PX P} {β : X → ℝ} {τ : c.φ.model.E 0 → c.F 1}

omit [T2Space Y] [ParacompactSpace Y] in
lemma cutoff_mem_K (hτ : MapsTo (fun z => (z, τ z)) c.φ.model.O (strongShiftOne c.K)) {y : X}
    (hy : y ∈ c.φ.source) : (c.φ y, c.F.toBase 1 (β y • τ (c.φ y))) ∈ c.K := by
  rw [map_smul]
  exact c.smul_mem_K (hτ (c.φ.mapsTo_model y hy)) _

omit [T2Space Y] [ParacompactSpace Y] in
lemma apply_cutoffSection (hτ : MapsTo (fun z => (z, τ z)) c.φ.model.O (strongShiftOne c.K))
    {y : X} (hy : y ∈ c.φ.source) :
    c (cutoffSection c β τ y) = (c.φ y, c.F.toBase 1 (β y • τ (c.φ y))) := by
  rw [cutoffSection, if_pos hy]
  exact c.toPartialEquiv.right_inv (by rw [c.target_eq]; exact cutoff_mem_K hτ hy)

omit [T2Space Y] [ParacompactSpace Y] in
lemma cutoffSection_mem_source (hτ : MapsTo (fun z => (z, τ z)) c.φ.model.O (strongShiftOne c.K))
    {y : X} (hy : y ∈ c.φ.source) : cutoffSection c β τ y ∈ c.toPartialEquiv.source := by
  rw [cutoffSection, if_pos hy]
  exact c.toPartialEquiv.map_target (by rw [c.target_eq]; exact cutoff_mem_K hτ hy)

omit [T2Space Y] [ParacompactSpace Y] in
lemma isSection_cutoffSection
    (hτ : MapsTo (fun z => (z, τ z)) c.φ.model.O (strongShiftOne c.K)) :
    IsSection P (cutoffSection c β τ) := by
  intro y
  by_cases hy : y ∈ c.φ.source
  · have hs := cutoffSection_mem_source (β := β) hτ hy
    have hPs : P (cutoffSection c β τ y) ∈ c.φ.source := by rw [c.source_eq] at hs; exact hs
    have h1 := c.covers _ hs
    rw [apply_cutoffSection hτ hy] at h1
    exact c.φ.toPartialEquiv.injOn hPs hy h1.symm
  · rw [cutoffSection, if_neg hy]; exact proj_fiberZero P y

omit [T2Space Y] [ParacompactSpace Y] in
lemma cutoffSection_eq_zero (hτ : MapsTo (fun z => (z, τ z)) c.φ.model.O (strongShiftOne c.K))
    {y : X} (hβ : β y = 0) : cutoffSection c β τ y = fiberZero P y := by
  by_cases hy : y ∈ c.φ.source
  · have hP0 : P (fiberZero P y) ∈ c.φ.source := by rw [proj_fiberZero P]; exact hy
    refine c.toPartialEquiv.injOn (cutoffSection_mem_source hτ hy) (c.mem_source_of_proj hP0) ?_
    rw [apply_cutoffSection hτ hy, hβ, zero_smul, map_zero]
    refine (Prod.ext ?_ (c.snd_fiberZero hy)).symm
    rw [c.fst_apply hP0, proj_fiberZero P]
  · rw [cutoffSection, if_neg hy]

lemma cutoffSection_mem_oneSet (hc : c ∈ B.atlas.charts)
    (hτ : MapsTo (fun z => (z, τ z)) c.φ.model.O (strongShiftOne c.K)) (y : X) :
    cutoffSection c β τ y ∈ B.oneSet := by
  by_cases hy : y ∈ c.φ.source
  · rw [B.mem_oneSet_iff hc (cutoffSection_mem_source hτ hy), apply_cutoffSection hτ hy]
    exact ⟨_, rfl⟩
  · rw [cutoffSection, if_neg hy]; exact B.fiberZero_mem_oneSet y

omit [T2Space Y] [ParacompactSpace Y] in
lemma liftOne_cutoffSection (hτ : MapsTo (fun z => (z, τ z)) c.φ.model.O (strongShiftOne c.K))
    {y : X} (hy : y ∈ c.φ.source) :
    c.liftOne (cutoffSection c β τ y) = (c.φ y, β y • τ (c.φ y)) := by
  unfold StrongBundleChart.liftOne
  rw [apply_cutoffSection hτ hy]
  exact Prod.ext rfl (Function.leftInverse_invFun (c.F.toBase_injective 1) _)

/-- **The cut-off of a local sc⁺-section is an sc⁺-section**: if `z ↦ (z, τ(z))` is sc-smooth
`O → K[1]` in a strong bundle chart `Φ` of the atlas and `β : X → ℝ` is sc-smooth with
`supp(β) ⊆ dom φ`, then `y ↦ Φ⁻¹(φ(y), β(y)·τ(φ(y)))`, extended by `0`, is an sc⁺-section
(in `Φ[1]` its representative is `z ↦ (z, β(φ⁻¹(z))·τ(z))`, by the product rule; off `supp(β)` it
is the zero section). -/
theorem isScPlusSection_cutoffSection (hc : c ∈ B.atlas.charts)
    (hβ : PX.IsScSmoothMap realPolyfold β) (hβs : tsupport β ⊆ c.φ.source)
    (hτ : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F.shift)
      (c.φ.model.C ×ˢ univ) (strongShiftOne c.K) (fun z => (z, τ z))) :
    B.IsScPlusSection (cutoffSection c β τ) := by
  have hτm := hτ.mapsTo
  have hsec := isSection_cutoffSection (β := β) hτm
  set g : X → B.One := fun y => B.oneMk (cutoffSection c β τ y) (cutoffSection_mem_oneSet hc hτm y)
    with hg
  refine (B.isScPlusSection_iff _).2 ⟨hsec, g, rfl, ?_⟩
  refine MPolyfold.isScSmoothMap_of_local fun y => ?_
  by_cases hy : y ∈ c.φ.source
  · refine ⟨c.φ, oneChart hc (g y), c.φ.source, c.isChart, B.isChart_oneChart hc (g y),
      c.φ.isOpen_source, hy, subset_rfl, fun y' hy' => cutoffSection_mem_source hτm hy', ?_⟩
    rw [c.φ.image_source]
    have hβ1 := hβ.real_chart c.isChart
    have hmain : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O
        (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c.K)
        (fun z => (z, β (c.φ.symm z) • τ z)) := by
      refine ⟨fun z hz => c.smul_mem_strongShiftOne (hτm hz) _, fun R hR => ?_⟩
      have hU := R.isScDomain
      have h1 := hτ.comp_isScSmooth R hR
      have h2 := (hβ1.comp_isScSmooth R hR).smul hU (h1.snd hU)
      exact (R.isScSmooth.scPair hU h2).congr hU fun _ _ => rfl
    refine hmain.congr fun z hz => ?_
    have hzs := c.φ.symm_mapsTo hz
    change (z, β (c.φ.symm z) • τ z) = c.liftOne (cutoffSection c β τ (c.φ.symm z))
    rw [liftOne_cutoffSection hτm hzs, c.φ.apply_symm_apply hz]
  · have hyt : y ∉ tsupport β := fun h => hy (hβs h)
    obtain ⟨c', hc', hyc'⟩ := exists_chart_mem B y
    set V := c'.φ.source ∩ (tsupport β)ᶜ with hV
    have hVo : IsOpen V := c'.φ.isOpen_source.inter (isClosed_tsupport β).isOpen_compl
    have hzero : ∀ y' ∈ V, cutoffSection c β τ y' = fiberZero P y' := fun y' hy' =>
      cutoffSection_eq_zero hτm (image_eq_zero_of_notMem_tsupport hy'.2)
    refine ⟨c'.φ, oneChart hc' (g y), V, c'.isChart, B.isChart_oneChart hc' (g y), hVo,
      ⟨hyc', hyt⟩, inter_subset_left, fun y' hy' => ?_, ?_⟩
    · change cutoffSection c β τ y' ∈ c'.toPartialEquiv.source
      exact c'.mem_source_of_proj (by rw [hsec y']; exact hy'.1)
    · have hret : IsScRetract c'.φ.model.E c'.φ.model.C (c'.φ '' V) :=
        c'.φ.isScRetract_image inter_subset_left hVo
      refine ((c'.φ.model.E.prodInlOp c'.F.shift).isScSmoothRetractMap hret
        fun z hz => ?_).congr ?_
      · change (z, c'.F.toBase 1 0) ∈ c'.K
        rw [map_zero]; exact c'.zero_mem_K (c'.φ.image_subset_model inter_subset_left hz)
      · rintro _ ⟨y', hy', rfl⟩
        change ((c'.φ y', 0) : (c'.φ.model.E.prod c'.F.shift) 0) =
          c'.liftOne (cutoffSection c β τ (c'.φ.symm (c'.φ y')))
        rw [c'.φ.symm_apply_apply hy'.1, hzero y' hy', liftOne_fiberZero hy'.1]

/-- **Lemma 5.3.3 (preprint 5.11) (existence of sc⁺-sections)**: let `P : Y → X` be a strong bundle over an
M-polyfold which admits sc-smooth bump functions (Definition 5.3.1 (preprint 5.9), read as `f(x) ≠ 0`), and `N` an
auxiliary norm.  For a smooth point `x ∈ X`, a smooth point `e` of the fibre `P⁻¹(x)`, an open
neighbourhood `U` of `x` and `ε > 0`, there is an sc⁺-section `s` with `s(x) = e`,
`supp(s) ⊆ U` and **`N(s(y)) < N(e) + ε` for all `y`** (the text writes the bound at `x` only,
where it is trivial).  The proof is the text's: in a strong bundle chart around `x`, `t(y) =
R(φ(y), ê)` with `ê = Φ(e)₂ ∈ F_∞` constant, cut off by a bump `β` with `β(x) = 1` supported where
`N(t(y)) < N(e) + ε`.  Neither tameness nor a chart centred at `x` is needed. -/
theorem _root_.Polyfold.lemma_5_3_3 (hbump : PX.AdmitsBumpFunctions) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N)
    {x : X} (_hx : x ∈ PX.smoothSet) {e : Y} (he : e ∈ B.toMPolyfold0.smoothSet) (hex : P e = x)
    {ε : ℝ} (hε : 0 < ε) {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ he1 : e ∈ B.oneSet, ∃ s : X → Y, B.IsScPlusSection s ∧ s x = e ∧
      sectionSupport P s ⊆ U ∧
        ∀ y (hy : s y ∈ B.oneSet), N (B.oneMk (s y) hy) < N (B.oneMk e he1) + ε := by
  obtain ⟨c, hc, hxc⟩ := exists_chart_mem B x
  have hR := c.isRetraction
  have hPex : P e ∈ c.φ.source := by rw [hex]; exact hxc
  have hes : e ∈ c.toPartialEquiv.source := c.mem_source_of_proj hPex
  have hce : c e = (c.φ x, (c e).2) := Prod.ext (by rw [c.fst_apply hPex, hex]) rfl
  -- `ê = Φ(e)₂` is a smooth point of `F`
  have hsm : (c e).2 ∈ c.F.smooth := by
    refine c.F.mem_smooth_iff.2 fun m => ?_
    have hm : e ∈ B.toMPolyfold0.levelSet m := mem_iInter.1 he m
    rw [B.toMPolyfold0.mem_levelSet_iff (B.isChart_toMChart hc) hes] at hm
    obtain ⟨w, hw⟩ := hm
    have h2 := ScBanach.prod_toBase c.φ.model.E c.F m w
    have h3 : c e = _ := hw.symm.trans h2
    exact ⟨w.2, (congrArg Prod.snd h3).symm⟩
  have he1 : e ∈ B.oneSet := by
    rw [B.mem_oneSet_iff hc hes]; exact c.F.mem_smooth_iff.1 hsm 1
  set ê₁ : c.F 1 := Function.invFun (c.F.toBase 1) (c e).2 with hê₁def
  have hê₁ : c.F.toBase 1 ê₁ = (c e).2 := Function.invFun_eq (c.F.mem_smooth_iff.1 hsm 1)
  have hê₁s : ê₁ ∈ c.F.shift.smooth := by
    have h1 : ê₁ ∈ c.F.smoothLvl 1 := by
      change c.F.toBase 1 ê₁ ∈ c.F.smooth; rw [hê₁]; exact hsm
    rw [← c.F.shift_smoothLvl 0] at h1
    exact h1
  -- the local section `t(y) = R(φ(y), ê)`, principal part `τ`
  set τ : c.φ.model.E 0 → c.F 1 := fun z => (shiftFiber c.R (z, ê₁)).2 with hτdef
  have hOU : ∀ z ∈ c.φ.model.O, z ∈ c.U := fun z hz =>
    (hR.baseRetraction c.relOpen).retract_subset (by rw [c.base_retract]; exact hz)
  have hshift : ∀ z ∈ c.φ.model.O, shiftFiber c.R (z, ê₁) = (z, τ z) := fun z hz => by
    refine Prod.ext ?_ rfl
    change (c.R (z, c.F.toBase 1 ê₁)).1 = z
    rw [hR.apply_fst (hOU z hz)]
    exact (hR.baseRetraction c.relOpen).apply_eq_self_of_mem_retract
      (by rw [c.base_retract]; exact hz)
  have hτι : ∀ z ∈ c.φ.model.O, c.F.toBase 1 (τ z) = (c.R (z, (c e).2)).2 := fun z hz => by
    rw [← hê₁]; exact hR.toBase_shiftFiber_snd (p := (z, ê₁)) (hOU z hz)
  have hτ : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O
      (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c.K)
      (fun z => (z, τ z)) := by
    refine ⟨fun z hz => ?_, fun R' hR' => ?_⟩
    · change (z, τ z) ∈ strongShiftOne c.K
      rw [← hshift z hz]
      have := (hR.toScRetractionOne c.relOpen).apply_mem_retract
        (show ((z, ê₁) : (c.φ.model.E.prod c.F.shift) 0) ∈ c.U ×ˢ univ from ⟨hOU z hz, mem_univ _⟩)
      rw [hR.toScRetractionOne_retract c.relOpen] at this
      exact this
    · have hU' := R'.isScDomain
      have hRO : ∀ u ∈ R'.U, R' u ∈ c.φ.model.O := fun u hu => hR' ▸ R'.apply_mem_retract hu
      have hpair := R'.isScSmooth.scPair hU' (isScSmooth_const_of_mem_smooth hU' hê₁s)
      have hcomp := IsScSmooth.comp hU' (c.relOpen.prod_univ c.F.shift).isScDomain
        hR.isScSmooth_one hpair fun u hu => ⟨hOU _ (hRO u hu), mem_univ _⟩
      exact hcomp.congr hU' fun u hu => hshift _ (hRO u hu)
  have hτm := hτ.mapsTo
  -- `t` as a map into `Y[1]` on `dom φ`, and the open set where `N(t(y)) < N(e) + ε`
  set y₀ := B.oneMk e he1 with hy₀
  set χ := oneChart hc y₀ with hχ
  set tt : X → B.One := fun y => χ.symm (c.φ y, τ (c.φ y)) with htt
  have hcont : ContinuousOn (fun y => N (tt y)) c.φ.source :=
    hN.continuous.comp_continuousOn (χ.continuousOn_invFun.comp
      ((hτ.continuousOn c.φ.model.isScRetract).comp c.φ.continuousOn_toFun
        fun y hy => c.φ.mapsTo_model y hy) fun y hy => hτm (c.φ.mapsTo_model y hy))
  set G := c.φ.source ∩ (fun y => N (tt y)) ⁻¹' Iio (N y₀ + ε) with hG
  have hGo : IsOpen G := hcont.isOpen_inter_preimage c.φ.isOpen_source isOpen_Iio
  have hRce : c.R (c e) = c e := by
    obtain ⟨q, hq, hqe⟩ : c e ∈ c.K := by rw [← c.image_source]; exact ⟨e, hes, rfl⟩
    rw [← hqe, hR.idem q hq]
  have hτx : c.F.toBase 1 (τ (c.φ x)) = (c e).2 := by
    rw [hτι _ (c.φ.mapsTo_model x hxc)]
    conv_rhs => rw [← hRce]
    rw [← hce]
  have htt_val : ∀ y ∈ c.φ.source,
      B.oneVal (tt y) = c.toPartialEquiv.symm (c.φ y, c.F.toBase 1 (τ (c.φ y))) := fun y hy =>
    oneChart_symm_apply hc y₀ (hτm (c.φ.mapsTo_model y hy))
  have httx : tt x = y₀ := by
    apply B.oneVal_injective
    rw [htt_val x hxc, hτx, ← hce]
    exact c.toPartialEquiv.left_inv hes
  have hxG : x ∈ G := ⟨hxc, by
    change N (tt x) < N y₀ + ε
    rw [httx]; linarith⟩
  -- the bump function
  obtain ⟨β, hβ, hβ01, hβx, hβs, -⟩ := proposition_5_5_3 hbump (hU.inter hGo) ⟨hxU, hxG⟩
  have hβsrc : tsupport β ⊆ c.φ.source := fun y hy => (hβs hy).2.1
  refine ⟨he1, cutoffSection c β τ, isScPlusSection_cutoffSection hc hβ hβsrc hτ, ?_, ?_, ?_⟩
  · -- `s(x) = e`
    refine c.toPartialEquiv.injOn (cutoffSection_mem_source hτm hxc) hes ?_
    rw [apply_cutoffSection hτm hxc, hβx, one_smul, hτx, ← hce]
  · -- `supp(s) ⊆ U`
    refine (closure_minimal (fun y hy => subset_tsupport _ ?_) (isClosed_tsupport β)).trans
      (hβs.trans inter_subset_left)
    exact mem_support.2 fun h0 => hy (cutoffSection_eq_zero hτm h0)
  · -- the bound
    intro y hy
    by_cases hβy : β y = 0
    · have h0 : B.oneMk (cutoffSection c β τ y) hy = B.zeroOne y :=
        B.oneVal_injective (cutoffSection_eq_zero hτm hβy)
      rw [h0, (hN.fiber y).map_zero]
      linarith [hN.nonneg y₀]
    · have hyG : y ∈ G := (hβs (subset_tsupport _ hβy)).2
      have hyc : y ∈ c.φ.source := hyG.1
      have hNt : N (tt y) < N y₀ + ε := hyG.2
      have hKy : (c.φ y, c.F.toBase 1 (τ (c.φ y))) ∈ c.K := hτm (c.φ.mapsTo_model y hyc)
      have hPt : P (B.oneVal (tt y)) = y := by
        rw [htt_val y hyc, c.proj_symm hKy, c.φ.symm_apply_apply hyc]
      have hsrc_t : P (B.oneVal (tt y)) ∈ c.φ.source := by rw [hPt]; exact hyc
      have heq : B.oneMk (cutoffSection c β τ y) hy = B.toOne (β y • B.ofOne (tt y)) := by
        apply B.oneVal_injective
        change cutoffSection c β τ y =
          ((β y • (⟨B.oneVal (tt y), rfl⟩ : P ⁻¹' {P (B.oneVal (tt y))}) :
            P ⁻¹' {P (B.oneVal (tt y))}) : Y)
        refine c.toPartialEquiv.injOn (cutoffSection_mem_source hτm hyc)
          (c.mem_source_of_proj ?_) ?_
        · rw [show P ((β y • (⟨B.oneVal (tt y), rfl⟩ : P ⁻¹' {P (B.oneVal (tt y))}) :
            P ⁻¹' {P (B.oneVal (tt y))}) : Y) = P (B.oneVal (tt y)) from
              (β y • (⟨B.oneVal (tt y), rfl⟩ : P ⁻¹' {P (B.oneVal (tt y))})).2]
          exact hsrc_t
        · have h2 := (c.fiber_linear _ hsrc_t).map_smul (β y)
            (⟨B.oneVal (tt y), rfl⟩ : P ⁻¹' {P (B.oneVal (tt y))})
          refine Prod.ext ?_ ?_
          · rw [apply_cutoffSection hτm hyc]
            change c.φ y = (c ((β y • (⟨B.oneVal (tt y), rfl⟩ : P ⁻¹' {P (B.oneVal (tt y))}) :
              P ⁻¹' {P (B.oneVal (tt y))}) : Y)).1
            rw [c.fst_apply (by
              rw [show P ((β y • (⟨B.oneVal (tt y), rfl⟩ : P ⁻¹' {P (B.oneVal (tt y))}) :
                P ⁻¹' {P (B.oneVal (tt y))}) : Y) = P (B.oneVal (tt y)) from
                  (β y • (⟨B.oneVal (tt y), rfl⟩ : P ⁻¹' {P (B.oneVal (tt y))})).2]
              exact hsrc_t)]
            rw [show P ((β y • (⟨B.oneVal (tt y), rfl⟩ : P ⁻¹' {P (B.oneVal (tt y))}) :
              P ⁻¹' {P (B.oneVal (tt y))}) : Y) = P (B.oneVal (tt y)) from
                (β y • (⟨B.oneVal (tt y), rfl⟩ : P ⁻¹' {P (B.oneVal (tt y))})).2, hPt]
          · rw [apply_cutoffSection hτm hyc, h2, map_smul]
            change β y • c.F.toBase 1 (τ (c.φ y)) = β y • (c (B.oneVal (tt y))).2
            rw [htt_val y hyc, c.apply_symm hKy]
      rw [heq, hN.smul, abs_of_nonneg (hβ01 y).1, toOne_ofOne]
      calc β y * N (tt y) ≤ N (tt y) := mul_le_of_le_one_left (hN.nonneg _) (hβ01 y).2
        _ < N y₀ + ε := hNt

end StrongBundle

end Existence

end Polyfold
