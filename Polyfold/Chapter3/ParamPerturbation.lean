import Polyfold.Chapter2.FibredProduct
import Polyfold.Chapter3.StrongBundleSections
import Polyfold.Chapter3.BasicClassComposition
import Polyfold.Chapter3.LinearizationCharts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
**Theorem 3.18** (parametrized perturbations; book 2017: Theorem 3.3), with the verification the
text calls "readily verified" and the linearization of the parametrized section used after
Theorem 3.19 (and for transversality in Chapter 5).

# Parametrized perturbations

## The text, paraphrased

(Before Theorem 3.18) For a strong bundle `P : Y → X` and an sc-Fredholm section `f`, the
projection `π : ℝⁿ × X → X` pulls `P` back to the strong bundle `π*(P) : π*Y → ℝⁿ × X`; the
section `f̃(r, x) = ((r, x), f(x))` of `π*(P)` "is a sc-Fredholm section as is readily
verified".  For sc⁺-sections `s₁, …, sₙ` of `P`, `s̃(r, x) = ((r, x), Σ rᵢ sᵢ(x))` is an
sc⁺-section of `π*(P)`, and by Theorem 3.15 `f̃ + s̃` is sc-Fredholm.  (Theorem 3.18) Let
`P : Y → X` be a tame strong bundle, `f` an sc-Fredholm section and `s₁, …, sₙ ∈ Γ⁺(P)`.  Then
`ℝⁿ × X → Y, (r, x) ↦ f(x) + Σ rᵢ sᵢ(x)` defines an sc-Fredholm section of `π*(P)`.  (After
Theorem 3.19) The linearization of `f̃(r, x) = f(x) + Σ rᵢ sᵢ(x)` at `(0, x₀)` is
`(h, u) ↦ f'(x₀)u + Σ hᵢ eᵢ`, `eᵢ = sᵢ(x₀)`.

## What is formalized

* **`ℝⁿ` and `ℝⁿ × X`.**  `Polyfold.rnPolyfold n` (`ℝⁿ` with its constant sc-structure and the
  chart `id`), the translation charts `rnChart n a : r ↦ r − a` (`isChart_rnChart`; needed for
  charts of `ℝⁿ × X` centred at `(r₀, x)`), `rnPolyfold_isTame`; for the product
  `(rnPolyfold n).prod PX`: `prod_rn_mem_levelSet_iff`, `prod_rn_mem_smoothSet_iff` (the levels
  and smooth points of `(r, x)` are those of `x`) and `prod_rn_isTame` (`ℝⁿ × X` is tame when
  `X` is, so `π*P` is a tame strong bundle when `P` is).
* **The pull-back bundle.**  `Polyfold.StrongBundle.pullback B hπ`: Proposition 2.54 as a
  structure (the atlas `pullbackAtlas` of all pulled-back charts; `proposition_2_54` states its
  existence); `exists_pullbackChartData`, `PullbackChartData.isChart_toChart` (a chart pulled
  back from a strong bundle chart *compatible with* the atlas of `P` is a chart of `π*P`);
  `pullbackLift` (the section `z ↦ (z, τ(z))` of a map `τ` over `π`) and
  `StrongBundle.IsScSmoothSection.pullback` (the pull-back of an sc-smooth section along an
  sc-smooth map is sc-smooth).
* **Two rules of the sc-calculus**: `IsScSmooth.smul` (a scalar factor: `x ↦ a(x) v(x)`, from
  `isScSmooth_smul`, scalar multiplication `ℝ ⊕ F → F` is sc-smooth, Proposition 1.19) and
  `IsScSmooth.finsetSum`.
* **The sections.**  `paramSection f hf s hs` is the text's `F(r, x) = f(x) + Σ rᵢ sᵢ(x)`
  (computed in `P⁻¹(x)` and regarded in the fibre of `π*Y` over `(r, x)`), `paramLift` is
  `f̃(r, x) = ((r, x), f(x))`, `paramComb` is `s̃(r, x) = ((r, x), Σ rᵢ sᵢ(x))`, and
  `paramSection_eq_sectionAdd`: `F = f̃ + s̃` in the fibres of `π*Y`.
  `StrongBundle.isScPlusSection_paramComb`: **`s̃` is an sc⁺-section of `π*P`**.
* **The `Λ`-extension** (any finite-dimensional `Λ`, used with `Λ = ℝⁿ`):
  `IsStrongBundleMap.paramMap`, `IsStrongBundleIso.paramMap` (**the product `1_Λ × Φ` with the
  identity of `Λ` is a strong bundle map / isomorphism**), `ScNbhdGerm.paramExtend`
  (`U''_m = {((a, λ), w) | (a, w) ∈ U_m}`), `IsBasicGerm.paramExtend` (**the `Λ`-extension
  `h'((a, λ), w) = h(a, w)` of a basic germ is a basic germ** on the parameter quadrant
  `(C̃ × Λ) ⊕ W`), and `IsConjugateToBasicGerm.paramExtend` (if `k` is conjugated to a basic
  germ by `Ψ`, then `(λ, u) ↦ k(u)` is conjugated to its `Λ`-extension by the reassociation of
  the factors composed with `1_Λ × Ψ`).
* **The product chart.**  `PullbackChartData.ofProd c r₀`: the chart `ψ = (r ↦ r − r₀) × φ` of
  `ℝⁿ × X` with the retraction `1 × r` of `ℝⁿ × U` onto `ℝⁿ × O`, through the strong bundle
  chart `c` of `P`; `ofProd_isFillerOf` (**filler conditions (1)–(3) for `(a, u) ↦ g(u)` from
  those of `g`**: `ker D(1 × r)(0) = 0 × ker Dr(0)`, `ρ'(0) = ρ(0)`);
  `ofProd_principal_paramSection` (**the principal part of `F` in the product chart is
  `(a, u) ↦ f̂(u) + Σ (a + r₀)ᵢ ŝᵢ(u)`**, the text's `(r, u) ↦ f̂(u) + Σ rᵢ ŝᵢ(u)` with
  `r = a + r₀`) and `ofProd_principal_paramComb`.
* **The theorem.**  `StrongBundle.IsScFredholmGermWholeChart.param` (**`(f̃, (r₀, x))` is an sc-Fredholm
  germ**: filled version `(a, u) ↦ g(u)`, sc⁺-section `(a, u) ↦ t₀(u)`, conjugation to the
  `ℝⁿ`-extension of the basic germ of `g − t₀`), `StrongBundle.regularizing_paramLift_wholeChart`,
  `StrongBundle.IsScFredholmSectionWholeChart.param` (**`f̃` is an sc-Fredholm section of `π*P`**), and
  **`Polyfold.theorem_3_18_wholeChart`**: `F` is an sc-Fredholm section of `π*P`, by Theorem 3.15 as in
  the text; `theorem_3_18'_wholeChart` is the same with the paracompactness supplied by Theorem 2.16.
* **Tame germ data** (Definition 3.51, `TameGerms.lean`): `PullbackChartData.ofProd_isTame` (**the
  product chart of a tame chart is tame**: the base retraction `1 × r` on `ℝⁿ × U`, with the
  identity of `ℝⁿ` tame and `ScRetraction.IsTameWith.prod`), `StrongBundle.IsScFredholmGermTameWholeChart.param`,
  `StrongBundle.IsScFredholmSectionTameWholeChart.param` and `Polyfold.theorem_3_18_tame_wholeChart`: **`F` has tame
  germ data when `f` has** (Findings, Chapter 3 item 195).
* **The linearization.**  `scDeriv_paramSection_wholeChart`: in the product chart at `(r₀, x)`,
  `D(F̂ ∘ (1 × r))(0)(δa, δu) = D(Ĝ ∘ r)(0) δu + Σ δaᵢ ŝᵢ(0)` with `Ĝ = f̂ + Σ r₀ᵢ ŝᵢ`;
  `linAt_paramSection_wholeChart` (the same in the chart form `linAt` of `LinearizationCharts.lean`, on
  `T₀(ℝⁿ × O) ⊆ ℝⁿ × T₀O`, `ofProd_mem_tangent`, `ofProd_scDeriv_r`) and
  `linAt_paramSection_zero_wholeChart` (at `r₀ = 0`: **`(δr, ξ) ↦ f'(x)ξ + Σ δrᵢ sᵢ(x)`**, the text's
  formula after Theorem 3.19).

## What the text leaves implicit, and the choices made (the findings)

* **Tameness is not used** (as in Theorem 3.15; the book drops "tame" in Theorem 3.18):
  `theorem_3_18_wholeChart` has no tameness hypothesis.  Since Definition 3.14 is stated for tame strong
  bundles, the text needs `π*P` tame when `P` is; for the base that is `prod_rn_isTame`, for the
  charts of the germ data (Definition 3.51, what the implicit function theorems of §3.6 use for
  `F` in Chapter 5) it is `theorem_3_18_tame_wholeChart`.
* **`ℝⁿ × X` and `π*(P)` are used without being constructed.**  `ℝⁿ` is the M-polyfold with the
  identity chart; its charts include the translations, which the germ property at `(r₀, x)`
  needs (Definition 3.11 asks for a chart centred at `(r₀, x)`; the product `id × φ` is centred
  only at `r₀ = 0`).  `π*(P)` carries the "natural structure" of Proposition 2.54 (all
  pulled-back charts, through every chart of `ℝⁿ × X`, not only product charts).  Its
  paracompactness and that of `ℝⁿ × X` (Definitions 2.13, 2.51) are instance arguments, proved
  by `MPolyfold.paracompactSpace_prod` and `paracompactSpace_pullbackSpace` (Theorem 2.16): not
  added hypotheses.
* **"`f̃` is a sc-Fredholm section as is readily verified".**  The verification is the
  `ℝⁿ`-extension: in the product chart the filled version, the sc⁺-part and the conjugation are
  those of `f` composed with `(a, u) ↦ u`, and the basic germ is extended to the parameter
  space `C̃ × ℝⁿ` (the new germ of neighbourhoods is unbounded in the `ℝⁿ`-direction, which
  Definition 3.1 allows; the contraction estimate of Definition 3.28 is uniform in `λ` because
  `B'` does not depend on it).  The parameter factor is put second (`Pn × ℝⁿ`) to reuse
  `IsPartialQuadrant.const_prod_univ`; the order is immaterial.
* **"`s̃` is a sc⁺-section of the pull back bundle"** needs the product rule for a scalar factor
  in the sc-calculus (not stated in Chapter 1) and the sc-smoothness of the coordinate
  `(r, x) ↦ r` read in an *arbitrary* chart of `ℝⁿ × X` (the atlas of `π*P` contains charts
  pulled back through all charts of `ℝⁿ × X`).
* **The text's sketch of the germ of `F`** (filled version `(r, u) ↦ g(u) + Σ rᵢ s̃ᵢ(u)`,
  `s̃ᵢ = ŝᵢ ∘ r`; sc⁺-part `t₀(u) + Σ rᵢ s̃ᵢ(u)`; conjugation `Ψ'(r, u, k) = (r − r₀, Ψ(u, k))`)
  is what the proof produces: the germ data of `f̃` in the product chart composed, by Theorem
  3.15 (`StrongBundle.IsScFredholmGermWholeChart.sectionAdd`), with `s̃`, whose principal part is
  `(a, u) ↦ Σ (a + r₀)ᵢ ŝᵢ(u)`.  The translation `r − r₀` sits in the chart, so the
  conjugation itself has no translation.
* **The linearization after Theorem 3.19** is stated at `(0, x₀)` with `f(x₀) = 0`.  At a
  general `(r₀, x)` the first term is the linearization of `f + Σ r₀ᵢ sᵢ`, not `f'(x)`
  (`linAt_paramSection_wholeChart`).  The formula is stated in the chart form `linAt` (Definition 3.53
  works in charts, gap G.13); it is the derivative at the centre of the chart and does not need
  `F(r₀, x) = 0`.
* Typos in the passage: "a parametrized version of Proposition 3.15" (Theorem 3.15); after
  Theorem 3.19, "the sc¹-sections `sᵢ`" (they must be sc⁺, as Theorem 3.18 requires and the
  preceding paragraph provides) and `ℝᵏ ⊕ X` for `ℝᵏ × X`; the symbol `f̃` denotes both
  `((r, x), f(x))` and `f(x) + Σ rᵢ sᵢ(x)`.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### `ℝⁿ` as a tame M-polyfold -/

section Rn

variable (n : ℕ)

/-- `ℝⁿ` with its constant sc-structure. -/
abbrev rnSc : ScBanach := ScBanach.const (Fin n → ℝ)

lemma rn_relOpen_univ : IsRelOpenInQuadrant (rnSc n) univ univ :=
  ⟨isPartialQuadrant_univ _, univ, isOpen_univ, (inter_univ _).symm⟩

/-- The local model `(ℝⁿ, ℝⁿ, ℝⁿ)`. -/
def rnModel : LocalModel := LocalModel.ofRelOpen (rn_relOpen_univ n)

/-- The translation chart `r ↦ r − a` of `ℝⁿ`, modelled on `(ℝⁿ, ℝⁿ, ℝⁿ)`. -/
def rnChart (a : Fin n → ℝ) : MChart (Fin n → ℝ) where
  model := rnModel n
  toPartialEquiv := (Equiv.subRight a).toPartialEquiv
  isOpen_source := isOpen_univ
  target_eq := rfl
  continuousOn_toFun := (continuous_sub_right a).continuousOn
  continuousOn_invFun := (continuous_add_const a).continuousOn

variable {n}

@[simp] lemma rnChart_apply (a r : Fin n → ℝ) : rnChart n a r = r - a := rfl

@[simp] lemma rnChart_symm_apply (a r : Fin n → ℝ) : (rnChart n a).symm r = r + a := rfl

lemma rnChart_source (a : Fin n → ℝ) : (rnChart n a).source = univ := rfl

lemma rnChart_model_O (a : Fin n → ℝ) : (rnChart n a).model.O = univ := rfl

/-- A `C^∞` map between finite-dimensional spaces is sc-smooth on `univ` for the constant
structures, as a map between the retracts `univ`. -/
theorem isScSmoothRetractMap_const_of_contDiff {V V' : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [FiniteDimensional ℝ V'] {g : V → V'} (hg : ContDiff ℝ ∞ g) :
    IsScSmoothRetractMap (ScBanach.const V) univ univ (ScBanach.const V') univ univ g := by
  have hU : IsRelOpenInQuadrant (ScBanach.const V) univ univ :=
    ⟨isPartialQuadrant_univ _, univ, isOpen_univ, (inter_univ _).symm⟩
  refine (isScSmoothRetractMap_iff_exists hU.isScRetract).2
    ⟨mapsTo_univ _ _, ScRetraction.id hU, image_id _, ?_⟩
  exact IsScSmooth.of_contDiffOn_finiteDimensional (V := V') hU.isScDomain
    (f := g ∘ ScRetraction.id hU) hg.contDiffOn

lemma rnChart_overlap (a b : Fin n → ℝ) : (rnChart n a).overlap (rnChart n b) = univ := by
  refine eq_univ_of_forall fun (r : Fin n → ℝ) => ⟨r + a, ⟨mem_univ _, mem_univ _⟩, ?_⟩
  change r + a - a = r
  abel

/-- Two translation charts of `ℝⁿ` are compatible (the transition maps are translations). -/
theorem rnChart_compatible (a b : Fin n → ℝ) : (rnChart n a).Compatible (rnChart n b) := by
  have key : ∀ a b : Fin n → ℝ, IsScSmoothRetractMap (rnSc n) univ
      ((rnChart n a).overlap (rnChart n b)) (rnSc n) univ ((rnChart n b).overlap (rnChart n a))
      ((rnChart n a).transition (rnChart n b)) := by
    intro a b
    rw [rnChart_overlap, rnChart_overlap]
    have : (rnChart n a).transition (rnChart n b) = fun r => r + a - b := rfl
    rw [this]
    exact isScSmoothRetractMap_const_of_contDiff
      ((contDiff_id.add contDiff_const).sub contDiff_const)
  exact ⟨key a b, key b a⟩

variable (n)

/-- **`ℝⁿ` as an M-polyfold**, with the single chart `id = rnChart n 0`; every translation chart
is a chart of it (`isChart_rnChart`). -/
def rnPolyfold : MPolyfold (Fin n → ℝ) where
  atlas :=
    { charts := {rnChart n 0}
      compatible := fun φ hφ ψ hψ => by
        rw [mem_singleton_iff.1 hφ, mem_singleton_iff.1 hψ]
        exact rnChart_compatible 0 0
      cover := fun r => ⟨rnChart n 0, mem_singleton _, mem_univ r⟩ }

variable {n}

lemma isChart_rnChart (a : Fin n → ℝ) : (rnPolyfold n).IsChart (rnChart n a) := by
  intro ψ hψ
  rw [mem_singleton_iff.1 hψ]
  exact rnChart_compatible a 0

/-- `ℝⁿ` is a **tame** M-polyfold (its only chart is modelled on the tame retract `ℝⁿ`). -/
theorem rnPolyfold_isTame : (rnPolyfold n).IsTame := by
  refine ⟨(rnPolyfold n).atlas, MAtlas.Equiv.refl _, fun φ hφ => ?_⟩
  rw [mem_singleton_iff.1 hφ]
  exact ⟨ScRetraction.id (rn_relOpen_univ n), image_id _, ScRetraction.id_isTame _⟩

/-- Every point of `ℝⁿ` is on every level. -/
lemma rnPolyfold_levelSet (m : ℕ) : (rnPolyfold n).levelSet m = univ := by
  refine eq_univ_of_forall fun r => ?_
  rw [(rnPolyfold n).mem_levelSet_iff (isChart_rnChart 0) (mem_univ r)]
  exact ⟨rnChart n 0 r, ScBanach.const_toBase _ m _⟩

end Rn

/-! ### The product `ℝⁿ × X` -/

section Product

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} [ParacompactSpace ((Fin n → ℝ) × X)]

/-- A point `(r, x)` of `ℝⁿ × X` is on level `m` if and only if `x` is (`ℝⁿ` is on every
level). -/
lemma prod_rn_mem_levelSet_iff {m : ℕ} {z : (Fin n → ℝ) × X} :
    z ∈ ((rnPolyfold n).prod PX).levelSet m ↔ z.2 ∈ PX.levelSet m := by
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source z.2
  have hχ : ((rnPolyfold n).prod PX).IsChart ((rnChart n 0).prod φ) :=
    MPolyfold.IsChart.prod (isChart_rnChart 0) hφ
  rw [((rnPolyfold n).prod PX).mem_levelSet_iff hχ
    (show z ∈ ((rnChart n 0).prod φ).source from ⟨mem_univ _, hx⟩), PX.mem_levelSet_iff hφ hx]
  have hb : ∀ y : ((rnChart n 0).prod φ).model.E m,
      ((rnChart n 0).prod φ).model.E.toBase m y =
        ((ScBanach.const (Fin n → ℝ)).toBase m y.1, φ.model.E.toBase m y.2) := fun y =>
    ScBanach.prod_toBase (ScBanach.const (Fin n → ℝ)) φ.model.E m y
  constructor
  · rintro ⟨y, hy⟩
    rw [hb] at hy
    exact ⟨y.2, congrArg Prod.snd hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨((z.1 - 0 : Fin n → ℝ), y), ?_⟩
    exact (hb _).trans (Prod.ext (ScBanach.const_toBase _ m _) hy)

/-- The smooth points of `ℝⁿ × X` are the `(r, x)` with `x` smooth. -/
lemma prod_rn_mem_smoothSet_iff {z : (Fin n → ℝ) × X} :
    z ∈ ((rnPolyfold n).prod PX).smoothSet ↔ z.2 ∈ PX.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter, prod_rn_mem_levelSet_iff]

/-- **The text's tameness**: `ℝⁿ × X` is tame when `X` is (so `π*P` is a tame strong bundle when
`P` is, as Definition 3.14 requires). -/
theorem prod_rn_isTame (hX : PX.IsTame) : ((rnPolyfold n).prod PX).IsTame :=
  (MPolyfold.isTame_prod (rnPolyfold n) PX rnPolyfold_isTame hX).1

end Product

/-! ### Two rules of the sc-calculus: scalar multiplication and finite sums -/

section Calculus

variable {E F : ScBanach}

/-- Scalar multiplication `ℝ ⊕ F → F`, `(t, h) ↦ t h`, is sc-smooth (it is continuous bilinear
on every level). -/
theorem isScSmooth_smul (F : ScBanach) :
    IsScSmooth (E := (ScBanach.const ℝ).prod F) (F := F) univ fun p => p.1 • p.2 := by
  have hb : ∀ m (p : ((ScBanach.const ℝ).prod F) m), F.toBase m (p.1 • p.2) =
      (((ScBanach.const ℝ).prod F).toBase m p).1 • (((ScBanach.const ℝ).prod F).toBase m p).2 := by
    intro m p
    rw [ScBanach.prod_toBase, ScBanach.const_toBase, map_smul]
  refine IsScSmooth.of_contDiffOn_levels (isScDomain_univ _)
    (fun m p _ => ⟨p.1 • p.2, hb m p⟩) fun m => ?_
  have : levelMap (E := (ScBanach.const ℝ).prod F) (F := F) (fun p => p.1 • p.2) m =
      fun p => p.1 • p.2 := funext fun p => levelMap_eq_of_toBase_eq (hb m p)
  rw [this]
  exact (contDiff_fst.smul contDiff_snd).contDiffOn

/-- **The product rule for a scalar factor**: `x ↦ a(x) v(x)` is sc-smooth for sc-smooth
`a : U → ℝ` and `v : U → F`. -/
theorem IsScSmooth.smul {U : Set (E 0)} (hU : IsScDomain E U) {a : E 0 → ℝ} {v : E 0 → F 0}
    (ha : IsScSmooth (F := ScBanach.const ℝ) U a) (hv : IsScSmooth U v) :
    IsScSmooth U fun x => a x • v x := by
  have := IsScSmooth.comp hU (isScDomain_univ _) (isScSmooth_smul F)
    (IsScSmooth.scPair (G := F) hU ha hv) (mapsTo_univ _ _)
  exact this.congr hU fun x _ => rfl

/-- Finite sums of sc-smooth maps are sc-smooth. -/
theorem IsScSmooth.finsetSum {U : Set (E 0)} (hU : IsScDomain E U) {ι : Type} (s : Finset ι)
    {g : ι → E 0 → F 0} (hg : ∀ i ∈ s, IsScSmooth U (g i)) :
    IsScSmooth U fun x => ∑ i ∈ s, g i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    let T : ScOperator E F := { lvl := fun _ => 0, incl_comm := fun _ _ => by simp }
    exact (T.isScSmooth hU).congr hU fun _ _ => rfl
  | insert a s has ih =>
    simp only [Finset.sum_insert has]
    exact IsScSmooth.add hU (hg a (Finset.mem_insert_self a s))
      (ih fun b hb => hg b (Finset.mem_insert_of_mem hb))

/-- The coordinate `r ↦ rᵢ` of `ℝⁿ` as an sc-operator `ℝⁿ → ℝ`. -/
def rnCoordOp {n : ℕ} (i : Fin n) : ScOperator (rnSc n) (ScBanach.const ℝ) where
  lvl _ := ContinuousLinearMap.proj i
  incl_comm _ _ := rfl

end Calculus

/-! ### The `Λ`-extension: products with the identity of a finite-dimensional space -/

section ParamExtension

variable {E F E' F' : ScBanach} (Λ : Type) [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
  [FiniteDimensional ℝ Λ]

/-- The reassociation `((a, u), k) ↦ (a, (u, k))` as an sc-operator. -/
def ScBanach.assocOp (E F G : ScBanach) : ScOperator ((E.prod F).prod G) (E.prod (F.prod G)) where
  lvl m := (ContinuousLinearEquiv.prodAssoc ℝ (E m) (F m) (G m)).toContinuousLinearMap
  incl_comm _ _ := rfl

/-- The reassociation `(a, (u, k)) ↦ ((a, u), k)` as an sc-operator. -/
def ScBanach.assocInvOp (E F G : ScBanach) :
    ScOperator (E.prod (F.prod G)) ((E.prod F).prod G) where
  lvl m := (ContinuousLinearEquiv.prodAssoc ℝ (E m) (F m) (G m)).symm.toContinuousLinearMap
  incl_comm _ _ := rfl

lemma relOpen_univ_const (Λ : Type) [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
    [FiniteDimensional ℝ Λ] :
    IsRelOpenInQuadrant (ScBanach.const Λ) univ univ :=
  ⟨isPartialQuadrant_univ _, univ, isOpen_univ, (inter_univ _).symm⟩

/-- `Λ × U` is relatively open in `Λ × C`. -/
lemma IsRelOpenInQuadrant.univ_prod {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) :
    IsRelOpenInQuadrant ((ScBanach.const Λ).prod E) (univ ×ˢ C) (univ ×ˢ U) :=
  (relOpen_univ_const Λ).prod hU

/-- The product `1_Λ × Φ : (Λ × U) ◁ F → (Λ × U') ◁ F'` of the identity of `Λ` with a map
`Φ : U ◁ F → U' ◁ F'`: `((a, u), k) ↦ ((a, φ(u)), Γ(u, k))`. -/
def paramMap (Φ : E 0 × F 0 → E' 0 × F' 0) :
    ((ScBanach.const Λ).prod E) 0 × F 0 → ((ScBanach.const Λ).prod E') 0 × F' 0 :=
  fun p => ((p.1.1, (Φ (p.1.2, p.2)).1), (Φ (p.1.2, p.2)).2)

variable {Λ}

lemma paramMap_shiftFiber (Φ : E 0 × F 0 → E' 0 × F' 0)
    (p : ((ScBanach.const Λ).prod E).prod F.shift 0) :
    shiftFiber (paramMap Λ Φ) p =
      ((p.1.1, (shiftFiber Φ (p.1.2, p.2)).1), (shiftFiber Φ (p.1.2, p.2)).2) := rfl

/-- **The product with the identity of `Λ` is a strong bundle map** (Definition 2.47): on `[0]`
and `[1]` it is `1 × Φ` up to the reassociations of the factors. -/
theorem IsStrongBundleMap.paramMap {C : Set (E 0)} {U : Set (E 0)} {U' : Set (E' 0)}
    (hU : IsRelOpenInQuadrant E C U) {Φ : E 0 × F 0 → E' 0 × F' 0}
    (hΦ : IsStrongBundleMap U U' Φ) :
    IsStrongBundleMap (univ ×ˢ U) (univ ×ˢ U') (paramMap Λ Φ) where
  mapsTo p hp := ⟨⟨mem_univ _, (hΦ.mapsTo ⟨hp.1.2, mem_univ _⟩).1⟩, mem_univ _⟩
  fst_independent u hu h h' := by
    change ((u.1, (Φ (u.2, h)).1) : Λ × E' 0) = (u.1, (Φ (u.2, h')).1)
    rw [hΦ.fst_independent u.2 hu.2 h h']
  fiber_linear u hu := hΦ.fiber_linear u.2 hu.2
  preserves_filtration m k hk u hu hum h hh := by
    obtain ⟨y, hy⟩ := hum
    rw [ScBanach.prod_toBase] at hy
    have hu2 : u.2 ∈ range (E.toBase m) := ⟨y.2, congrArg Prod.snd hy⟩
    obtain ⟨⟨y', hy'⟩, h2⟩ := hΦ.preserves_filtration m k hk u.2 hu.2 hu2 h hh
    refine ⟨⟨((u.1 : Λ), y'), ?_⟩, h2⟩
    rw [ScBanach.prod_toBase, ScBanach.const_toBase, hy']
    rfl
  isScSmooth_zero := by
    have hD₁ := ((hU.univ_prod Λ).prod_univ F).isScDomain
    have hD₂ := ((relOpen_univ_const Λ).prod (hU.prod_univ F)).isScDomain
    have h1 := (ScBanach.assocOp (ScBanach.const Λ) E F).isScSmooth hD₁
    have h2 := IsScSmooth.prodMap (F := ScBanach.const Λ) (F' := E'.prod F')
      (isScDomain_univ (ScBanach.const Λ)) (hU.prod_univ F).isScDomain hD₂
      (isScSmooth_id (isScDomain_univ (ScBanach.const Λ))) hΦ.isScSmooth_zero
    have h3 := (ScBanach.assocInvOp (ScBanach.const Λ) E' F').isScSmooth
      (isScDomain_univ ((ScBanach.const Λ).prod (E'.prod F')))
    have h12 := IsScSmooth.comp hD₁ hD₂ h2 h1 fun p hp => ⟨mem_univ _, hp.1.2, mem_univ _⟩
    exact (IsScSmooth.comp hD₁ (isScDomain_univ _) h3 h12 (mapsTo_univ _ _)).congr hD₁
      fun _ _ => rfl
  isScSmooth_one := by
    have hD₁ := ((hU.univ_prod Λ).prod_univ F.shift).isScDomain
    have hD₂ := ((relOpen_univ_const Λ).prod (hU.prod_univ F.shift)).isScDomain
    have h1 := (ScBanach.assocOp (ScBanach.const Λ) E F.shift).isScSmooth hD₁
    have h2 := IsScSmooth.prodMap (F := ScBanach.const Λ) (F' := E'.prod F'.shift)
      (isScDomain_univ (ScBanach.const Λ)) (hU.prod_univ F.shift).isScDomain hD₂
      (isScSmooth_id (isScDomain_univ (ScBanach.const Λ))) hΦ.isScSmooth_one
    have h3 := (ScBanach.assocInvOp (ScBanach.const Λ) E' F'.shift).isScSmooth
      (isScDomain_univ ((ScBanach.const Λ).prod (E'.prod F'.shift)))
    have h12 := IsScSmooth.comp hD₁ hD₂ h2 h1 fun p hp => ⟨mem_univ _, hp.1.2, mem_univ _⟩
    exact (IsScSmooth.comp hD₁ (isScDomain_univ _) h3 h12 (mapsTo_univ _ _)).congr hD₁
      fun _ _ => rfl

/-- **The product with the identity of `Λ` is a strong bundle isomorphism**, with inverse
`1_Λ × Φ'`. -/
theorem IsStrongBundleIso.paramMap {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)}
    {U' : Set (E' 0)} (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    {Φ : E 0 × F 0 → E' 0 × F' 0} {Φ' : E' 0 × F' 0 → E 0 × F 0}
    (hΦ : IsStrongBundleIso U U' Φ Φ') :
    IsStrongBundleIso (univ ×ˢ U) (univ ×ˢ U') (paramMap Λ Φ) (paramMap Λ Φ') where
  toFun := hΦ.toFun.paramMap hU
  invFun := hΦ.invFun.paramMap hU'
  left_inv p hp := by
    have h := hΦ.left_inv (p.1.2, p.2) ⟨hp.1.2, mem_univ _⟩
    change ((p.1.1, (Φ' ((Φ (p.1.2, p.2)).1, (Φ (p.1.2, p.2)).2)).1),
      (Φ' ((Φ (p.1.2, p.2)).1, (Φ (p.1.2, p.2)).2)).2) = p
    rw [Prod.mk.eta, h]
  right_inv p hp := by
    have h := hΦ.right_inv (p.1.2, p.2) ⟨hp.1.2, mem_univ _⟩
    change ((p.1.1, (Φ ((Φ' (p.1.2, p.2)).1, (Φ' (p.1.2, p.2)).2)).1),
      (Φ ((Φ' (p.1.2, p.2)).1, (Φ' (p.1.2, p.2)).2)).2) = p
    rw [Prod.mk.eta, h]

end ParamExtension

/-! #### Basic germs on the parameter quadrant `(C̃ × Λ) ⊕ W` -/

section BasicExtension

variable {Pn Q : Type} [NormedAddCommGroup Pn] [NormedSpace ℝ Pn] [FiniteDimensional ℝ Pn]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  (Λ : Type) [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  {W : ScBanach} {Ct : Set Pn}

/-- The level maps of `g ∘ T` for an sc-operator `T`. -/
lemma levelMap_comp_scOperator {E F G : ScBanach} (g : F 0 → G 0) (T : ScOperator E F) (m : ℕ)
    (x : E m) : levelMap (g ∘ T 0) m x = levelMap g m (T m x) := by
  unfold levelMap
  rw [Function.comp_apply, ← T.toBase_comm]

variable (Pn W) in
/-- The projection `((a, λ), w) ↦ (a, w)`, an sc-operator `(P × Λ) ⊕ W → P ⊕ W`. -/
def paramForgetOp : ScOperator (ScBanach.paramProd (Pn × Λ) W) (ScBanach.paramProd Pn W) where
  lvl m := ((ContinuousLinearMap.fst ℝ Pn Λ).comp (ContinuousLinearMap.fst ℝ (Pn × Λ) (W m))).prod
    (ContinuousLinearMap.snd ℝ (Pn × Λ) (W m))
  incl_comm _ _ := rfl

@[simp] lemma paramForgetOp_apply (m : ℕ) (p : (ScBanach.paramProd (Pn × Λ) W) m) :
    paramForgetOp Pn Λ W m p = (p.1.1, p.2) := rfl

variable (Pn W) in
/-- The reassociation `(λ, (a, w)) ↦ ((a, λ), w)`, an sc-operator `Λ ⊕ (P ⊕ W) → (P × Λ) ⊕ W`. -/
def paramSwapOp :
    ScOperator ((ScBanach.const Λ).prod (ScBanach.paramProd Pn W)) (ScBanach.paramProd (Pn × Λ) W)
    where
  lvl m := (((ContinuousLinearMap.fst ℝ Pn (W m)).comp
      (ContinuousLinearMap.snd ℝ Λ (Pn × W m))).prod
      (ContinuousLinearMap.fst ℝ Λ (Pn × W m))).prod
    ((ContinuousLinearMap.snd ℝ Pn (W m)).comp (ContinuousLinearMap.snd ℝ Λ (Pn × W m)))
  incl_comm _ _ := rfl

variable (Pn W) in
/-- The inverse reassociation `((a, λ), w) ↦ (λ, (a, w))`. -/
def paramSwapInvOp :
    ScOperator (ScBanach.paramProd (Pn × Λ) W) ((ScBanach.const Λ).prod (ScBanach.paramProd Pn W))
    where
  lvl m := ((ContinuousLinearMap.snd ℝ Pn Λ).comp (ContinuousLinearMap.fst ℝ (Pn × Λ) (W m))).prod
    (((ContinuousLinearMap.fst ℝ Pn Λ).comp (ContinuousLinearMap.fst ℝ (Pn × Λ) (W m))).prod
      (ContinuousLinearMap.snd ℝ (Pn × Λ) (W m)))
  incl_comm _ _ := rfl

@[simp] lemma paramSwapOp_apply (m : ℕ)
    (p : ((ScBanach.const Λ).prod (ScBanach.paramProd Pn W)) m) :
    paramSwapOp Pn Λ W m p = ((p.2.1, p.1), p.2.2) := rfl

@[simp] lemma paramSwapInvOp_apply (m : ℕ) (p : (ScBanach.paramProd (Pn × Λ) W) m) :
    paramSwapInvOp Pn Λ W m p = (p.1.2, (p.1.1, p.2)) := rfl

/-- **The `Λ`-extension of a germ of neighbourhoods**: `U''_m = {((a, λ), w) | (a, w) ∈ U_m}`, a
germ of neighbourhoods of `0` in the partial quadrant `(C̃ × Λ) ⊕ W`. -/
def ScNbhdGerm.paramExtend (G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ)) :
    ScNbhdGerm (ScBanach.paramProd (Pn × Λ) W) ((Ct ×ˢ (univ : Set Λ)) ×ˢ univ) where
  U m := {p | ((p.1.1, p.2) : Pn × W m) ∈ G.U m}
  nested m p hp := G.nested m (p.1.1, p.2) hp
  zero_mem m := G.zero_mem m
  relOpen m := by
    obtain ⟨O, hO, hGO⟩ := G.relOpen m
    refine ⟨(paramForgetOp Pn Λ W m) ⁻¹' O, hO.preimage (paramForgetOp Pn Λ W m).continuous, ?_⟩
    ext p
    have h1 := ScBanach.paramProd_lvlSet (P := Pn) W Ct m
    have h2 := ScBanach.paramProd_lvlSet (P := Pn × Λ) W (Ct ×ˢ univ) m
    rw [h1] at hGO
    rw [h2, Set.mem_ofPred_eq, hGO]
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
    exact Iff.rfl

/-- **The `Λ`-extension of a basic germ is a basic germ**: if `h(a, w) = (h₁(a, w), w − B(a, w))`
is basic on `C̃ ⊕ W`, then `h'((a, λ), w) = h(a, w)` is basic on `(C̃ × Λ) ⊕ W`, with
`B'((a, λ), w) = B(a, w)` (the contraction estimate does not involve `λ`). -/
theorem IsBasicGerm.paramExtend (hCt : IsQuadrantLike (ScBanach.const Pn) Ct)
    {G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ)} {h : Pn × W 0 → Q × W 0}
    {Bc : Pn × W 0 → W 0} (hh : IsBasicGerm Ct G h Bc) :
    IsBasicGerm (Ct ×ˢ (univ : Set Λ)) (G.paramExtend Λ) (fun p => h (p.1.1, p.2))
      (fun p => Bc (p.1.1, p.2)) where
  isScSmooth := by
    have hC := hCt.paramProd W
    have hC' := (hCt.prod_univ_const (Q := Λ)).paramProd W
    exact IsScSmoothGerm.comp hC' hC hh.isScSmooth
      ((paramForgetOp Pn Λ W).isScSmoothGerm (G.paramExtend Λ) hC') fun m p hp => by
        change levelMap (⇑(paramForgetOp Pn Λ W 0)) m p ∈ G.U m
        rw [ScOperator.levelMap_eq]; exact hp
  f_zero := hh.f_zero
  snd_eq x hx := hh.snd_eq _ hx
  contraction :=
    { isSc0 := IsSc0Germ.comp hh.contraction.isSc0 ((paramForgetOp Pn Λ W).isSc0Germ _)
        fun m p hp => by
          change levelMap (⇑(paramForgetOp Pn Λ W 0)) m p ∈ G.U m
          rw [ScOperator.levelMap_eq]; exact hp
      B_zero := hh.contraction.B_zero
      contraction := fun ε hε m => by
        obtain ⟨r, hr, H⟩ := hh.contraction.contraction ε hε m
        refine ⟨r, hr, fun a ha har w w' hw hw' => ?_⟩
        have ha1 : ‖a.1‖ < r := lt_of_le_of_lt (norm_fst_le a) har
        obtain ⟨hmem, hest⟩ := H a.1 ha.1 ha1 w w' hw hw'
        refine ⟨hmem, ?_⟩
        have e1 := levelMap_comp_scOperator Bc (paramForgetOp Pn Λ W) m (a, w)
        have e2 := levelMap_comp_scOperator Bc (paramForgetOp Pn Λ W) m (a, w')
        change ‖levelMap (Bc ∘ paramForgetOp Pn Λ W 0) m (a, w) -
          levelMap (Bc ∘ paramForgetOp Pn Λ W 0) m (a, w')‖ ≤ ε * ‖w - w'‖
        rw [e1, e2]
        exact hest }

/-- **The `Λ`-extension of a conjugation to a basic germ**: if `k : U → F` is conjugated to a
basic germ `h` by `Ψ : U ◁ F → U' ◁ (ℝᴺ ⊕ W)`, then `(λ, u) ↦ k(u)` on `Λ × U` is conjugated to
the basic germ `h'((a, λ), w) = h(a, w)` on `(C̃ × Λ) ⊕ W` by
`Ψ''((λ, u), k) = ((ψ(u)₁, λ), ψ(u)₂), Γ(u, k))`, the product `1_Λ × Ψ` (a strong bundle
isomorphism, `IsStrongBundleIso.paramMap`) followed by the linear reassociation of the factors. -/
theorem IsConjugateToBasicGerm.paramExtend {E F : ScBanach} {C U : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U) {k : E 0 → F 0} (hk : IsConjugateToBasicGerm U k) :
    IsConjugateToBasicGerm (E := (ScBanach.const Λ).prod E) (F := F) (univ ×ˢ U)
      fun v => k v.2 := by
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, h0, hG, hh,
    hev⟩ := hk
  -- the domain `U'' = {((a, λ), w) | (a, w) ∈ U'}`
  set U'' : Set ((ScBanach.paramProd (Pn × Λ) W) 0) := (paramForgetOp Pn Λ W 0) ⁻¹' U' with hU''
  have hrel'' : IsRelOpenInQuadrant (ScBanach.paramProd (Pn × Λ) W) ((Ct ×ˢ univ) ×ˢ univ) U'' := by
    refine ⟨(hCt.const_prod_univ Λ).prod_univ W, ?_⟩
    obtain ⟨O, hO, hUO⟩ := hU'.relOpen
    refine ⟨(paramForgetOp Pn Λ W 0) ⁻¹' O, hO.preimage (paramForgetOp Pn Λ W 0).continuous, ?_⟩
    ext p
    rw [hU'', mem_preimage, hUO]
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
    exact Iff.rfl
  have hrel₁ := hU'.univ_prod Λ
  -- the linear reassociation as a strong bundle isomorphism
  have hswap := ScOperator.isStrongBundleIso_prodMap hrel₁ hrel'' (paramSwapOp Pn Λ W)
    (paramSwapInvOp Pn Λ W) (ScOperator.id (ScBanach.paramProd Q W))
    (ScOperator.id (ScBanach.paramProd Q W)) (fun p hp => hp.2) (fun p hp => ⟨mem_univ _, hp⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hiso := (hΨ.paramMap (Λ := Λ) hU hU').comp (hU.univ_prod Λ) hrel₁ hrel'' hswap
  refine ⟨Pn × Λ, Q, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, W, Ct ×ˢ univ, U'', _, _, G.paramExtend Λ, fun p => h (p.1.1, p.2),
    fun p => Bc (p.1.1, p.2), hCt.const_prod_univ Λ, hrel'', hiso, ?_, ?_,
    hh.paramExtend Λ hCt.isQuadrantLike, ?_⟩
  · change paramSwapOp Pn Λ W 0 ((0 : Λ), IsStrongBundleMap.base Ψ 0) = 0
    rw [h0]
    exact map_zero _
  · intro p hp
    exact hG hp
  · have ht : Tendsto (fun v : ((ScBanach.const Λ).prod E) 0 => v.2) (𝓝 0) (𝓝 0) :=
      continuous_snd.tendsto' _ _ rfl
    filter_upwards [ht.eventually hev] with v hv hvU
    exact hv hvU.2

end BasicExtension


/-! ### The pull-back bundle as a strong bundle; pulled-back charts and sections -/

section Pullback

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {π : Z → X}

/-- **Proposition 2.54** as a structure: the pull-back strong bundle `π*P : π*Y → Z` of the strong
bundle `P : Y → X` along the sc-smooth `π : Z → X`, with the atlas of all pulled-back charts
(`pullbackAtlas`; `proposition_2_54` states its existence).  The paracompactness of `π*Y` is an
instance argument; it holds by `paracompactSpace_pullbackSpace`. -/
def StrongBundle.pullback (B : StrongBundle PX P) (hπ : PZ.IsScSmoothMap PX π)
    [ParacompactSpace (pullbackSpace P π)] : StrongBundle PZ (pullbackProj P π) where
  continuous := continuous_pullbackProj P π
  surjective z := by
    obtain ⟨y, hy⟩ := B.surjective (π z)
    exact ⟨⟨(z, y), hy⟩, rfl⟩
  banachable z := by
    obtain ⟨Bsp, h1, h2, h3, ⟨e⟩⟩ := B.banachable (π z)
    exact ⟨Bsp, h1, h2, h3, ⟨(pullbackFiberCLE z).trans e⟩⟩
  atlas := pullbackAtlas B hπ

omit [T2Space Y] [ParacompactSpace Y] in
/-- Pulled-back chart data through a given strong bundle chart `c` around `π(z)` (the
construction in `pullbackAtlas`): a chart of `Z` around `z` with `π(dom ψ) ⊆ dom φ`. -/
theorem exists_pullbackChartData (hπ : PZ.IsScSmoothMap PX π) (c : StrongBundleChart PX P)
    {z : Z} (hz : π z ∈ c.φ.source) :
    ∃ d : PullbackChartData PX P PZ π, d.c = c ∧ z ∈ d.ψ.source := by
  obtain ⟨ψ₀, hψ₀, hz₀⟩ := PZ.exists_isChart_mem_source z
  have hπc : Continuous π := continuousOn_univ.1 hπ.continuousOn
  have hV : IsOpen (ψ₀.source ∩ π ⁻¹' c.φ.source) :=
    ψ₀.isOpen_source.inter (c.φ.isOpen_source.preimage hπc)
  set ψ := ψ₀.restrict inter_subset_left hV
  have hψ : PZ.IsChart ψ := MPolyfold.IsChart.restrict PZ hψ₀ inter_subset_left hV
  have hψf : MapsTo π ψ.source c.φ.source := fun z hz => hz.2
  obtain ⟨RZ, hRZ⟩ := ψ.model.isScRetract
  have hsm := hπ.smooth ψ c.φ hψ c.isChart ψ.source ψ.isOpen_source
    (fun z hz => ⟨mem_univ _, hz⟩) hψf
  rw [ψ.image_source] at hsm
  exact ⟨⟨c, ψ, hψ, hψf, RZ, hRZ, hsm⟩, rfl, show z ∈ ψ.source from ⟨hz₀, hz⟩⟩

variable [ParacompactSpace (pullbackSpace P π)]

/-- A chart pulled back from a strong bundle chart of `P` (compatible with the atlas, not
necessarily in it) is a strong bundle chart of `π*P`. -/
theorem PullbackChartData.isChart_toChart (B : StrongBundle PX P) (hπ : PZ.IsScSmoothMap PX π)
    (d : PullbackChartData PX P PZ π) (hc : B.IsChart d.c) (q₀ : pullbackSpace P π) :
    (B.pullback hπ).IsChart (d.toChart q₀) := by
  rintro _ ⟨d₂, q₂, hd₂, rfl⟩
  exact PullbackChartData.compatible_toChart d d₂ q₀ q₂ B.continuous (hc d₂.c hd₂)
    (d.isChart.compatible d₂.isChart (P := PZ))

variable (π) in
/-- The section `z ↦ (z, τ(z))` of `π*Y` defined by a map `τ : Z → Y` over `π`
(`P(τ(z)) = π(z)`). -/
def pullbackLift (τ : Z → Y) (hτ : ∀ z, P (τ z) = π z) : Z → pullbackSpace P π :=
  fun z => ⟨(z, τ z), hτ z⟩

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] [ParacompactSpace (pullbackSpace P π)] in
lemma isSection_pullbackLift {τ : Z → Y} (hτ : ∀ z, P (τ z) = π z) :
    IsSection (pullbackProj P π) (pullbackLift π τ hτ) := fun _ => rfl

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [T2Space Y] [ParacompactSpace Y]
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] [T2Space Z] [ParacompactSpace Z]
  [ParacompactSpace (pullbackSpace P π)] in
lemma continuous_pullbackLift {τ : Z → Y} (hτ : ∀ z, P (τ z) = π z) (hc : Continuous τ) :
    Continuous (pullbackLift π τ hτ) :=
  (continuous_id.prodMk hc).subtype_mk _

namespace PullbackChartData

variable (d : PullbackChartData PX P PZ π) (q₀ : pullbackSpace P π)

omit [T2Space Y] [ParacompactSpace Y] [ParacompactSpace (pullbackSpace P π)] in
/-- The pulled-back chart at a lifted section: `Φ_π(z, τ(z)) = (ψ(z), pr_F Φ(τ(z)))`. -/
lemma toChart_pullbackLift {τ : Z → Y} (hτ : ∀ z, P (τ z) = π z) (z : Z) :
    d.toChart q₀ (pullbackLift π τ hτ z) = (d.ψ z, (d.c (τ z)).2) := rfl

omit [T2Space Y] [ParacompactSpace Y] [ParacompactSpace (pullbackSpace P π)] in
lemma g_mem_O {w : d.ψ.model.E 0} (hw : w ∈ d.ψ.model.O) : d.g w ∈ d.c.φ.model.O :=
  d.smooth.mapsTo hw

omit [T2Space Y] [ParacompactSpace Y] [ParacompactSpace (pullbackSpace P π)] in
/-- The local representative of a pulled-back section `σ ∘ π`: `w ↦ (w, σ̂(g(w)))` on `O_Z`. -/
lemma toChart_pullbackLift_comp {σ : X → Y} (hσ : IsSection P σ) {w : d.ψ.model.E 0}
    (hw : w ∈ d.ψ.model.O) :
    d.toChart q₀ (pullbackLift π (σ ∘ π) (fun z => hσ (π z)) (d.ψ.symm w)) =
      (w, d.c.principal σ (d.g w)) := by
  have hz : π (d.ψ.symm w) ∈ d.c.φ.source := d.mapsTo (d.ψ.symm_mapsTo hw)
  rw [toChart_pullbackLift, d.ψ.apply_symm_apply hw]
  change (w, (d.c (σ (π (d.ψ.symm w)))).2) = _
  rw [d.c.apply_section' hσ hz]
  rfl

end PullbackChartData

namespace StrongBundle

variable {B : StrongBundle PX P}

/-- **The pull-back of an sc-smooth section** `σ` of `P` along the sc-smooth `π` is an sc-smooth
section `z ↦ (z, σ(π(z)))` of `π*P` (in the pulled-back charts its representative is
`w ↦ (w, σ̂(g(w)))`, `g = φ ∘ π ∘ ψ⁻¹`). -/
theorem IsScSmoothSection.pullback {σ : X → Y} (hσ : B.IsScSmoothSection σ)
    (hπ : PZ.IsScSmoothMap PX π) :
    (B.pullback hπ).IsScSmoothSection (pullbackLift π (σ ∘ π) fun z => hσ.1 (π z)) := by
  have hσc : Continuous σ := continuousOn_univ.1 hσ.2.continuousOn
  have hπc : Continuous π := continuousOn_univ.1 hπ.continuousOn
  refine ⟨isSection_pullbackLift _, MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ
    (continuous_pullbackLift _ (hσc.comp hπc)).continuousOn fun z _ => ?_⟩
  obtain ⟨c, hc, hzc⟩ := B.exists_chart_mem (π z)
  obtain ⟨d, rfl, hzd⟩ := exists_pullbackChartData hπ c hzc
  set q₀ := pullbackLift π (σ ∘ π) (fun z => hσ.1 (π z)) z
  have hmem : d.toChart q₀ ∈ (B.pullback hπ).atlas.charts := ⟨d, q₀, hc, rfl⟩
  refine ⟨d.ψ, (d.toChart q₀).toMChart (B.pullback hπ).continuous, d.ψ.source, d.isChart,
    (B.pullback hπ).isChart_toMChart hmem, d.ψ.isOpen_source, hzd,
    fun y hy => ⟨mem_univ _, hy⟩, fun y hy => hy, ?_⟩
  rw [d.ψ.image_source]
  -- the representative `w ↦ (w, σ̂(g(w)))`
  have hcB : B.IsChart d.c := B.isChart_of_mem hc
  have h1 := (hσ.isScSmoothRetractMap hcB).comp d.smooth d.c.φ.model.isScRetract
  have h2 := ((d.c.φ.model.E.prodSndOp d.c.F).isScSmoothRetractMap d.c.isScRetract
    (C₁ := univ) (O₁ := (univ : Set (d.c.F 0))) (mapsTo_univ _ _)).comp h1 d.c.isScRetract
  have h3 := IsScSmoothRetractMap.scPair (isScSmoothRetractMap_id (C := d.ψ.model.C)
    d.ψ.model.O) h2 (O' := (d.toChart q₀).K) (C' := d.ψ.model.C ×ˢ univ) fun w hw => by
      change (w, d.c.principal σ (d.g w)) ∈ _
      rw [← d.toChart_pullbackLift_comp q₀ hσ.1 hw]
      exact (d.toChart q₀).image_source ▸
        ⟨_, show _ ∈ (d.toChart q₀).toPartialEquiv.source from d.ψ.symm_mapsTo hw, rfl⟩
  refine h3.congr fun w hw => ?_
  exact (d.toChart_pullbackLift_comp q₀ hσ.1 hw).symm

end StrongBundle

end Pullback

/-! ### The sections `f̃`, `s̃` and `F = f̃ + s̃` of `π*P → ℝⁿ × X` -/

section Param

universe u v

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- The fibre combination `Σ rᵢ sᵢ(x) ∈ P⁻¹(x)` at `z = (r, x)`. -/
def fiberComb (s : Fin n → X → Y) (hs : ∀ i, IsSection P (s i)) (z : (Fin n → ℝ) × X) :
    P ⁻¹' {z.2} :=
  ∑ i, z.1 i • (⟨s i z.2, hs i z.2⟩ : P ⁻¹' {z.2})

/-- **The section of Theorem 3.18**: `F(r, x) = f(x) + Σ rᵢ sᵢ(x)`, computed in the fibre
`P⁻¹(x)` and regarded as a point of the fibre of `π*Y` over `(r, x)`. -/
def paramSection (f : X → Y) (hf : IsSection P f) (s : Fin n → X → Y)
    (hs : ∀ i, IsSection P (s i)) :
    (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X) :=
  fun z => ⟨(z, (((⟨f z.2, hf z.2⟩ : P ⁻¹' {z.2}) + fiberComb s hs z : P ⁻¹' {z.2}) : Y)),
    (((⟨f z.2, hf z.2⟩ : P ⁻¹' {z.2}) + fiberComb s hs z : P ⁻¹' {z.2})).2⟩

/-- The pulled-back section `f̃(r, x) = ((r, x), f(x))` of the text. -/
abbrev paramLift (f : X → Y) (hf : IsSection P f) :
    (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X) :=
  pullbackLift Prod.snd (f ∘ Prod.snd) fun z => hf z.2

/-- The text's `s̃(r, x) = ((r, x), Σ rᵢ sᵢ(x))`. -/
abbrev paramComb (s : Fin n → X → Y) (hs : ∀ i, IsSection P (s i)) :
    (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X) :=
  pullbackLift Prod.snd (fun z => (fiberComb s hs z : Y)) fun z => (fiberComb s hs z).2

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- `F = f̃ + s̃`, the sum taken in the fibres of `π*Y` (the text's proof of Theorem 3.18). -/
theorem paramSection_eq_sectionAdd (f : X → Y) (hf : IsSection P f) (s : Fin n → X → Y)
    (hs : ∀ i, IsSection P (s i)) :
    paramSection f hf s hs = sectionAdd (pullbackProj P Prod.snd) (paramLift (n := n) f hf)
      (paramComb s hs) := by
  funext z
  rw [sectionAdd_apply (f := paramLift (n := n) f hf) (s := paramComb s hs)
    (isSection_pullbackLift _) (isSection_pullbackLift _)]
  set e := pullbackFiberEquiv P (Prod.snd : (Fin n → ℝ) × X → X) z
  have h1 : e ⟨paramLift (n := n) f hf z, rfl⟩ = ⟨f z.2, hf z.2⟩ := Subtype.ext rfl
  have h2 : e ⟨paramComb s hs z, rfl⟩ = fiberComb s hs z := Subtype.ext rfl
  have h3 : e ⟨paramSection f hf s hs z, rfl⟩ = ⟨f z.2, hf z.2⟩ + fiberComb s hs z :=
    Subtype.ext rfl
  have h4 := pullbackFiberEquiv_add P (Prod.snd : (Fin n → ℝ) × X → X) z
    ⟨paramLift (n := n) f hf z, rfl⟩ ⟨paramComb s hs z, rfl⟩
  rw [h1, h2, ← h3] at h4
  exact congrArg Subtype.val (e.injective h4).symm

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- The value of a pulled-back chart at `s̃`: `Φ_π(s̃(z)) = (ψ(z), Σ rᵢ ŝᵢ(x))`, by the linearity
of `Φ` on the fibre over `x = π(z)`. -/
lemma PullbackChartData.toChart_paramComb
    (d : PullbackChartData PX P ((rnPolyfold n).prod PX) Prod.snd)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) {s : Fin n → X → Y}
    (hs : ∀ i, IsSection P (s i)) {z : (Fin n → ℝ) × X} (hz : z ∈ d.ψ.source) :
    (d.toChart q₀ (paramComb s hs z)).2 = ∑ i, z.1 i • (d.c (s i z.2)).2 := by
  have hzc : z.2 ∈ d.c.φ.source := d.mapsTo hz
  let L : P ⁻¹' {z.2} →ₗ[ℝ] d.c.F 0 := IsLinearMap.mk' _ (d.c.fiber_linear z.2 hzc)
  have h := map_sum L (fun i => z.1 i • (⟨s i z.2, hs i z.2⟩ : P ⁻¹' {z.2})) Finset.univ
  simp only [map_smul] at h
  exact h

/-- The coordinates `w ↦ (ψ⁻¹(w))₁ ∈ ℝⁿ` of a chart `ψ` of `ℝⁿ × X` are sc-smooth on its retract
(the projection `ℝⁿ × X → ℝⁿ` read in `ψ` and the identity chart of `ℝⁿ`). -/
lemma isScSmooth_chart_coord {ψ : MChart ((Fin n → ℝ) × X)}
    (hψ : ((rnPolyfold n).prod PX).IsChart ψ) (i : Fin n) (R : ScRetraction ψ.model.E ψ.model.C)
    (hR : R.retract = ψ.model.O) :
    IsScSmooth (F := ScBanach.const ℝ) R.U fun u => (ψ.symm (R u)).1 i := by
  have h1 := (MPolyfold.isScSmoothMap_fst (rnPolyfold n) PX).smooth ψ (rnChart n 0) hψ
    (isChart_rnChart 0) ψ.source ψ.isOpen_source (fun z hz => ⟨mem_univ _, hz⟩)
    (fun _ _ => mem_univ _)
  rw [ψ.image_source] at h1
  have h2 := ((rnCoordOp (n := n) i).isScSmoothRetractMap (isScRetract_univ (rnSc n))
    (O₁ := univ) (C₁ := univ) (mapsTo_univ _ _)).comp h1 (isScRetract_univ (rnSc n))
  refine (h2.comp_isScSmooth R hR).congr R.isScDomain fun u _ => ?_
  change ((ψ.symm (R u)).1 - 0) i = (ψ.symm (R u)).1 i
  rw [sub_zero]

namespace StrongBundle

variable {B : StrongBundle PX P}

/-- **`s̃(r, x) = Σ rᵢ sᵢ(x)` is an sc⁺-section of `π*P`** (the text: "`s̃(r, x) := ((r, x),
Σ rᵢ sᵢ(x))` is a sc⁺-section of the pull back bundle"): in a pulled-back chart its principal
part is `w ↦ Σ λᵢ(w) ŝᵢ(g(w))`, with `λ(w) = (ψ⁻¹(w))₁` sc-smooth and `ŝᵢ ∘ g` sc-smooth into
`F¹`; the product and sum rules of the sc-calculus conclude. -/
theorem isScPlusSection_paramComb {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i)) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection
      (paramComb s fun i => (hs i).1) := by
  refine ⟨isSection_pullbackLift _, ?_⟩
  rintro _ ⟨d, q₀, hc, rfl⟩
  have hcB : B.IsChart d.c := B.isChart_of_mem hc
  set c' := d.toChart q₀ with hc'
  set S := paramComb s fun i => (hs i).1 with hS
  have hval := fun {z} (hz : z ∈ d.ψ.source) =>
    d.toChart_paramComb q₀ (fun i => (hs i).1) hz
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [hval hz]
    have hmem : ∀ i, (d.c (s i z.2)).2 ∈
        (LinearMap.range ((d.c.F.toBase 1 : d.c.F 1 →L[ℝ] d.c.F 0) : d.c.F 1 →ₗ[ℝ] d.c.F 0)) :=
      fun i => ((hs i).2 d.c hc).1 z.2 (d.mapsTo hz)
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)
  -- the representative `G(w) = (w, Σ λᵢ(w) ŝᵢ₁(g(w)))`
  set G : d.ψ.model.E 0 → (d.ψ.model.E.prod d.c.F.shift) 0 := fun w =>
    (w, ∑ i, (d.ψ.symm w).1 i • d.c.principalLift (s i) (d.g w)) with hG
  have hsum : ∀ w ∈ d.ψ.model.O, d.c.F.toBase 1 (G w).2 =
      ∑ i, (d.ψ.symm w).1 i • d.c.principal (s i) (d.g w) := by
    intro w hw
    simp only [hG, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hs i).toBase_principalLift hcB (d.g_mem_O hw)]
  have hc'val : ∀ w ∈ d.ψ.model.O, c' (S (d.ψ.symm w)) = (w, d.c.F.toBase 1 (G w).2) := by
    intro w hw
    refine Prod.ext (d.ψ.apply_symm_apply hw) ?_
    rw [hval (d.ψ.symm_mapsTo hw), hsum w hw]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hz : (d.ψ.symm w).2 ∈ d.c.φ.source := d.mapsTo (d.ψ.symm_mapsTo hw)
    rw [d.c.apply_section' (hs i).1 hz]
    rfl
  have hrep : EqOn G (localRepOne c' S) d.ψ.model.O := by
    intro w hw
    change G w = ((c' (S (d.ψ.symm w))).1, Function.invFun (d.c.F.toBase 1) (c' (S (d.ψ.symm w))).2)
    rw [hc'val w hw]
    exact Prod.ext rfl (Function.leftInverse_invFun (d.c.F.toBase_injective 1) _).symm
  refine IsScSmoothRetractMap.congr ?_ hrep
  refine ⟨fun w hw => ?_, fun R hR => ?_⟩
  · have hmem : c' (S (d.ψ.symm w)) ∈ c'.K := by
      rw [← c'.image_source]
      exact ⟨_, show _ ∈ c'.toPartialEquiv.source from d.ψ.symm_mapsTo hw, rfl⟩
    rw [hc'val w hw] at hmem
    exact hmem
  · have hU := R.isScDomain
    have hlam : ∀ i, IsScSmooth (F := ScBanach.const ℝ) R.U fun u => (d.ψ.symm (R u)).1 i :=
      fun i => isScSmooth_chart_coord d.isChart i R hR
    have hŝ : ∀ i, IsScSmooth (F := d.c.F.shift) R.U
        fun u => d.c.principalLift (s i) (d.g (R u)) := by
      intro i
      have h1 := ((hs i).isScSmoothRetractMap_one hcB).comp d.smooth d.c.φ.model.isScRetract
      exact ((h1.comp_isScSmooth R hR).snd hU).congr hU fun _ _ => rfl
    have h2 : IsScSmooth (F := d.c.F.shift) R.U
        fun u => ∑ i, (d.ψ.symm (R u)).1 i • d.c.principalLift (s i) (d.g (R u)) :=
      IsScSmooth.finsetSum hU _ fun i _ => (hlam i).smul hU (hŝ i)
    exact (R.isScSmooth.scPair hU h2).congr hU fun _ _ => rfl

end StrongBundle

/-! ### The product chart `(r ↦ r − r₀) × φ` and the germ property of `f̃` -/

/-- **The product chart at `(r₀, x)`** pulled back from a strong bundle chart `c` of `P`: the
chart `ψ = (r ↦ r − r₀) × φ` of `ℝⁿ × X` on `ℝⁿ × V`, with the retraction `1 × r` of `ℝⁿ × U`
onto `ℝⁿ × O`; here `g = φ ∘ π ∘ ψ⁻¹` is the projection `(a, u) ↦ u` on `ℝⁿ × O`. -/
def PullbackChartData.ofProd (c : StrongBundleChart PX P) (r₀ : Fin n → ℝ) :
    PullbackChartData PX P ((rnPolyfold n).prod PX) Prod.snd where
  c := c
  ψ := (rnChart n r₀).prod c.φ
  isChart := MPolyfold.IsChart.prod (isChart_rnChart r₀) c.isChart
  mapsTo := fun _ hz => hz.2
  RZ := (ScRetraction.id (rn_relOpen_univ n)).prod (c.isRetraction.baseRetraction c.relOpen)
  RZ_retract := by
    have h := ScRetraction.prod_retract (ScRetraction.id (rn_relOpen_univ n))
      (c.isRetraction.baseRetraction c.relOpen)
    rw [c.base_retract] at h
    refine h.trans ?_
    change (id '' univ) ×ˢ c.φ.model.O = univ ×ˢ c.φ.model.O
    rw [image_id]
  smooth := by
    refine ((ScBanach.prodSndOp (rnSc n) c.φ.model.E).isScSmoothRetractMap
      ((rnChart n r₀).prod c.φ).model.isScRetract (fun w hw => hw.2)).congr fun w hw => ?_
    change w.2 = c.φ (c.φ.symm w.2)
    rw [c.φ.apply_symm_apply hw.2]

namespace PullbackChartData

variable (c : StrongBundleChart PX P) (r₀ : Fin n → ℝ)

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- **Filler conditions (1)–(3) in the product chart**: if `g` fills `f̂` in the chart `c`, then
`(a, u) ↦ g(u)` fills `(a, u) ↦ f̂(u)` in the product chart (`ker D(1 × r)(0) = 0 × ker Dr(0)`,
and `[1 − ρ(r(a, u))]g(u) = [1 − ρ(r(u))]g(u)` does not depend on `a`). -/
theorem ofProd_isFillerOf (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (h0U : (0 : c.φ.model.E 0) ∈ c.U) (h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O)
    {fb g : c.φ.model.E 0 → c.F 0} (hfill : IsFillerOf c.relOpen c.isRetraction h0U fb g) :
    IsFillerOf ((ofProd c r₀).toChart q₀).relOpen ((ofProd c r₀).toChart q₀).isRetraction
      (show (0 : (ofProd c r₀).ψ.model.E 0) ∈ ((ofProd c r₀).toChart q₀).U from ⟨mem_univ _, h0U⟩)
      (fun w => fb w.2) (fun w => g w.2) := by
  have h0U' : (0 : ((ofProd c r₀).toChart q₀).φ.model.E 0) ∈ ((ofProd c r₀).toChart q₀).U :=
    ⟨mem_univ _, h0U⟩
  set c' := (ofProd c r₀).toChart q₀ with hc'
  have hU := c.relOpen.isScDomain
  have hU' : IsRelOpenInQuadrant (rnSc n |>.prod c.φ.model.E) (univ ×ˢ c.φ.model.C)
      (univ ×ˢ c.U) := c.relOpen.univ_prod (Fin n → ℝ)
  have ht : Tendsto (fun w : (rnSc n |>.prod c.φ.model.E) 0 => w.2) (𝓝 0) (𝓝 0) :=
    continuous_snd.tendsto' _ _ rfl
  have hrr : ∀ u ∈ c.U, StrongRetr.r c.R (StrongRetr.r c.R u) = StrongRetr.r c.R u :=
    fun u hu => StrongRetr.r_r c.isRetraction hu
  -- `k(u) = [1 − ρ(r(u))]g(u)` and its pull-back along `(a, u) ↦ u`
  set k : c.φ.model.E 0 → c.F 0 := fun y => g y - StrongRetr.ρ c.R (StrongRetr.r c.R y) (g y)
    with hk
  have hsnd := (ScBanach.prodSndOp (rnSc n) c.φ.model.E).isScSmooth hU'.isScDomain
  have hk1 : IsSck 1 _ _ c.U k := ⟨hfill.isSc1, hfill.isSc1.tangentMap_isSc0⟩
  have hcomp := IsSck.comp hU'.isScDomain hU hk1 (hsnd 1) fun w hw => hw.2
  let g' : c'.φ.model.E 0 → c'.F 0 := fun w => g w.2
  have heq : EqOn (k ∘ (ScBanach.prodSndOp (rnSc n) c.φ.model.E 0))
      (fun y => g' y - StrongRetr.ρ c'.R (StrongRetr.r c'.R y) (g' y)) (univ ×ˢ c.U) := by
    intro y hy
    change g y.2 - (c.R (StrongRetr.r c.R y.2, g y.2)).2 =
      g y.2 - (c.R (c.φ (c.φ.symm (StrongRetr.r c.R (StrongRetr.r c.R y.2))), g y.2)).2
    rw [hrr y.2 hy.2, c.φ.apply_symm_apply (c.r_mem_O hy.2)]
  have h0' : (0 : (rnSc n |>.prod c.φ.model.E) 1) ∈
      (rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1 := by
    change (rnSc n |>.prod c.φ.model.E).toBase 1 0 ∈ univ ×ˢ c.U
    rw [map_zero]
    exact ⟨mem_univ _, h0U⟩
  refine ⟨?_, ?_, hcomp.1.congr heq, ?_⟩
  · filter_upwards [ht.eventually hfill.eq_on] with w hw hwO
    obtain ⟨v, hv, rfl⟩ := hwO
    exact hw ⟨v.2, hv.2, rfl⟩
  · filter_upwards [ht.eventually hfill.mem_of_fixed] with y hy hyU hfix
    change g y.2 = (c.R (c.φ (c.φ.symm (StrongRetr.r c.R (StrongRetr.r c.R y.2))), g y.2)).2
      at hfix
    rw [hrr y.2 hyU.2, c.φ.apply_symm_apply (c.r_mem_O hyU.2)] at hfix
    obtain ⟨u, hu, hru⟩ := hy hyU.2 hfix
    exact ⟨(y.1, u), ⟨mem_univ _, hu⟩, Prod.ext rfl hru⟩
  · set D := scDeriv c.U (StrongRetr.r c.R) (0 : c.φ.model.E 1) with hDdef
    -- `D(1 × r)(0) = 1 × Dr(0)`
    let D' : (Fin n → ℝ) × c.φ.model.E 0 →L[ℝ] (Fin n → ℝ) × c.φ.model.E 0 :=
      scDeriv c'.U (StrongRetr.r c'.R) (0 : c'.φ.model.E 1)
    have hDv : ∀ v : (Fin n → ℝ) × c.φ.model.E 0, D' v = (v.1, D v.2) := by
      intro v
      have h1 := scDeriv_prodMap (F := rnSc n) (F' := c.φ.model.E) (rn_relOpen_univ n) c.relOpen
        (isScSmooth_id (isScDomain_univ (rnSc n)))
        (c.isRetraction.baseRetraction c.relOpen).isScSmooth h0'
      have e := congrArg (fun L : (rnSc n |>.prod c.φ.model.E) 0 →L[ℝ]
        (rnSc n |>.prod c.φ.model.E) 0 => L v) h1
      have h2 : scDeriv (E := rnSc n) (F := rnSc n) univ id (0 : (rnSc n) 1) =
          ContinuousLinearMap.id ℝ (Fin n → ℝ) :=
        IsSc1.scDeriv_eqOn (isSc1With_id univ) ((rn_relOpen_univ n).isScDomain.uniqueDiffWithinAt 1)
          (by rw [ScBanach.mem_lvlSet]; exact mem_univ _)
      refine e.trans (Prod.ext ?_ rfl)
      exact congrArg (fun L : (rnSc n) 0 →L[ℝ] (rnSc n) 0 => L v.1) h2
    -- `ρ'(0) = ρ(0)`
    have hr0 : StrongRetr.r c.R 0 = 0 := StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ h0O)
    let ρ' : c.F 0 →L[ℝ] c.F 0 := StrongRetr.ρCLM c'.isRetraction h0U'
    have hρ0 : ∀ h : c.F 0, ρ' h = StrongRetr.ρCLM c.isRetraction h0U h := by
      intro h
      change (c.R (c.φ (c.φ.symm (StrongRetr.r c.R 0)), h)).2 = (c.R (0, h)).2
      rw [hr0, c.φ.apply_symm_apply h0O]
    -- the kernel `ker (1 × Dr(0)) = 0 × ker Dr(0)`, and `ker ρ'(0) = ker ρ(0)`
    let e₁ : LinearMap.ker (D' : (Fin n → ℝ) × c.φ.model.E 0 →ₗ[ℝ] (Fin n → ℝ) × c.φ.model.E 0)
        ≃L[ℝ] LinearMap.ker (D : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) :=
      { toFun := fun v => ⟨(v : (Fin n → ℝ) × c.φ.model.E 0).2, by
          have h : D' (v : (Fin n → ℝ) × c.φ.model.E 0) = 0 := LinearMap.mem_ker.1 v.2
          rw [hDv] at h
          exact LinearMap.mem_ker.2 (congrArg Prod.snd h)⟩
        invFun := fun u => ⟨((0 : Fin n → ℝ), (u : c.φ.model.E 0)), by
          refine LinearMap.mem_ker.2 ?_
          change D' ((0 : Fin n → ℝ), (u : c.φ.model.E 0)) = 0
          rw [hDv]
          exact Prod.ext rfl (LinearMap.mem_ker.1 u.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun v => by
          have h : D' (v : (Fin n → ℝ) × c.φ.model.E 0) = 0 := LinearMap.mem_ker.1 v.2
          rw [hDv] at h
          exact Subtype.ext (Prod.ext (congrArg Prod.fst h).symm rfl)
        right_inv := fun _ => rfl
        continuous_toFun := continuous_induced_rng.2 (continuous_snd.comp continuous_subtype_val)
        continuous_invFun :=
          continuous_induced_rng.2 (continuous_const.prodMk continuous_subtype_val) }
    let e₂ : LinearMap.ker ((StrongRetr.ρCLM c.isRetraction h0U : c.F 0 →L[ℝ] c.F 0) :
          c.F 0 →ₗ[ℝ] c.F 0) ≃L[ℝ] LinearMap.ker (ρ' : c.F 0 →ₗ[ℝ] c.F 0) :=
      { toFun := fun u => ⟨(u : c.F 0), by
          refine LinearMap.mem_ker.2 ?_
          exact (hρ0 u).trans (LinearMap.mem_ker.1 u.2)⟩
        invFun := fun u => ⟨(u : c.F 0), by
          refine LinearMap.mem_ker.2 ?_
          exact (hρ0 u).symm.trans (LinearMap.mem_ker.1 u.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := continuous_induced_rng.2 continuous_subtype_val
        continuous_invFun := continuous_induced_rng.2 continuous_subtype_val }
    obtain ⟨Φ, hΦ⟩ := hfill.linearization
    refine ⟨e₁.trans (Φ.trans e₂), fun v => ?_⟩
    refine (hΦ (e₁ v)).trans ?_
    -- the derivative of `k ∘ pr₂` at `0`
    have hD1 : IsSc1With (univ ×ˢ c.U)
        (fun y => g' y - StrongRetr.ρ c'.R (StrongRetr.r c'.R y) (g' y))
        (scDeriv (univ ×ˢ c.U) (k ∘ (ScBanach.prodSndOp (rnSc n) c.φ.model.E 0))) :=
      hcomp.1.isSc1With_scDeriv.congr heq
    have hder := IsSc1.scDeriv_eqOn hD1 (hU'.isScDomain.uniqueDiffWithinAt 1) h0'
    have hchain := scDeriv_comp_apply_of_isScDomain hU'.isScDomain hU (hsnd 1).isSc1 hfill.isSc1
      (fun w hw => hw.2) h0' v.1
    rw [ScOperator.scDeriv_eq _ hU'.isScDomain h0', ScOperator.levelMap_eq, map_zero] at hchain
    exact hchain.trans (congrArg (fun L : (rnSc n |>.prod c.φ.model.E) 0 →L[ℝ] c.F 0 =>
      L v.1) hder).symm

end PullbackChartData

namespace PullbackChartData

variable (c : StrongBundleChart PX P) (r₀ : Fin n → ℝ)
  (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- The principal part of `s̃` in the product chart: `(a, u) ↦ Σ (a + r₀)ᵢ ŝᵢ(u)` on `ℝⁿ × O`
(`a = r − r₀` is the chart coordinate of `r`).  At `r(a, u) = (a, r(u))` it is
`Σ (a + r₀)ᵢ s̃ᵢ(u)` with `s̃ᵢ = ŝᵢ ∘ r`, the extension of Lemma 3.16 used by Theorem 3.15. -/
theorem ofProd_principal_paramComb {s : Fin n → X → Y} (hs : ∀ i, IsSection P (s i))
    {w : (Fin n → ℝ) × c.φ.model.E 0} (hw : w.2 ∈ c.φ.model.O) :
    ((ofProd c r₀).toChart q₀).principal (paramComb s hs) w =
      ∑ i, (w.1 + r₀) i • c.principal (s i) w.2 :=
  (ofProd c r₀).toChart_paramComb q₀ hs
    ((ofProd c r₀).ψ.symm_mapsTo (show w ∈ (ofProd c r₀).ψ.model.O from ⟨mem_univ _, hw⟩))

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- **The principal part of `F` in the product chart** (Theorem 3.18, the text's
`F(r, x) = f(x) + Σ rᵢ sᵢ(x)` read in the chart `(r ↦ r − r₀) × Φ`):
`(a, u) ↦ f̂(u) + Σ (a + r₀)ᵢ ŝᵢ(u)` on `ℝⁿ × O`; for `r₀ = 0` it is the text's
`(r, u) ↦ f̂(u) + Σ rᵢ ŝᵢ(u)`. -/
theorem ofProd_principal_paramSection {f : X → Y} (hf : IsSection P f) {s : Fin n → X → Y}
    (hs : ∀ i, IsSection P (s i)) {w : (Fin n → ℝ) × c.φ.model.E 0} (hw : w.2 ∈ c.φ.model.O) :
    ((ofProd c r₀).toChart q₀).principal (paramSection f hf s hs) w =
      c.principal f w.2 + ∑ i, (w.1 + r₀) i • c.principal (s i) w.2 := by
  have hw' : w ∈ ((ofProd c r₀).toChart q₀).φ.model.O := ⟨mem_univ _, hw⟩
  rw [paramSection_eq_sectionAdd]
  exact (((ofProd c r₀).toChart q₀).principal_sectionAdd (f := paramLift f hf)
    (s := paramComb s hs) (isSection_pullbackLift _) (isSection_pullbackLift _) hw').trans
    (congrArg (c.principal f w.2 + ·) (ofProd_principal_paramComb c r₀ q₀ hs hw))

end PullbackChartData

namespace StrongBundle

variable {B : StrongBundle PX P} {f : X → Y}

/-- **The germ property of `f̃ = f ∘ π` at `(r₀, x)`** (the text's "readily verified"): in the
product chart `(r ↦ r − r₀) × φ` pulled back from a centred chart of `f` at `x`, the principal
part of `f̃` is `(a, u) ↦ f̂(u)`; its filled version is `(a, u) ↦ g(u)` (filler conditions from
those of `g`, `ofProd_isFillerOf`), the sc⁺-section to subtract is `(a, u) ↦ t₀(u)`, and
`(a, u) ↦ (g − t₀)(u)` is conjugated to the `ℝⁿ`-extension `h'((b, a), w) = h(b, w)` of the basic
germ of `g − t₀` (`IsConjugateToBasicGerm.paramExtend`). -/
theorem IsScFredholmGermWholeChart.param (hfs : IsSection P f) {x : X} (hg : B.IsScFredholmGermWholeChart f x)
    (r₀ : Fin n → ℝ) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmGermWholeChart
      (paramLift (n := n) f hfs) (r₀, x) := by
  obtain ⟨hxs, c, hc, hxV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj⟩ := hg
  set d := PullbackChartData.ofProd (n := n) c r₀ with hd
  set q₀ := paramLift (n := n) f hfs (r₀, x) with hq₀
  have hU := c.relOpen.isScDomain
  have hU' : IsRelOpenInQuadrant (rnSc n |>.prod c.φ.model.E) (univ ×ˢ c.φ.model.C)
      (univ ×ˢ c.U) := c.relOpen.univ_prod (Fin n → ℝ)
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := h0 ▸ c.φ.mapsTo_model x hxV
  have hsnd := (ScBanach.prodSndOp (rnSc n) c.φ.model.E).isScSmooth hU'.isScDomain
  refine ⟨prod_rn_mem_smoothSet_iff.2 hxs, d.toChart q₀, d.isChart_toChart B _ hc q₀,
    show (r₀, x) ∈ d.ψ.source from ⟨mem_univ _, hxV⟩, ?_, ⟨mem_univ _, h0U⟩,
    fun w => g w.2, fun w => t₀ w.2, ⟨?_, ?_⟩, ?_, ht₀0, ?_⟩
  · change ((r₀ - r₀, c.φ x) : (Fin n → ℝ) × c.φ.model.E 0) = 0
    rw [sub_self, h0]
    rfl
  · exact IsScSmooth.comp hU'.isScDomain hU hfill.isScSmooth hsnd fun w hw => hw.2
  · exact PullbackChartData.ofProd_isFillerOf c r₀ q₀ h0U h0O hfill.filler
  · exact IsScSmooth.comp hU'.isScDomain hU ht₀ hsnd fun w hw => hw.2
  · exact IsConjugateToBasicGerm.paramExtend (Fin n → ℝ) c.relOpen hconj

/-- `f̃` is regularizing when `f` is: `(r, x) ∈ (ℝⁿ × X)_m` and `f̃(r, x) ∈ (π*Y)_{m,m+1}` give
`x ∈ X_m`, `f(x) ∈ Y_{m,m+1}` (test in the pulled-back charts), hence `x ∈ X_{m+1}`. -/
theorem regularizing_paramLift_wholeChart (hf : B.IsScFredholmSectionWholeChart f) :
    ∀ m, ∀ z ∈ ((rnPolyfold n).prod PX).levelSet m,
      paramLift (n := n) f hf.isScSmooth.1 z ∈
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).doubleLevel m (m + 1) →
      z ∈ ((rnPolyfold n).prod PX).levelSet (m + 1) := by
  intro m z hz hdl
  rw [prod_rn_mem_levelSet_iff] at hz ⊢
  have hfsec := hf.isScSmooth.1
  refine hf.regularizing m z.2 hz fun c hc hmem => ?_
  have hxV : z.2 ∈ c.φ.source := by
    rw [c.source_eq, mem_preimage, hfsec z.2] at hmem; exact hmem
  obtain ⟨d, rfl, hzd⟩ := exists_pullbackChartData (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)
    c (z := z) hxV
  have h1 := hdl (d.toChart (paramLift (n := n) f hfsec z)) ⟨d, _, hc, rfl⟩
    (show z ∈ d.ψ.source from hzd)
  refine ⟨?_, h1.2⟩
  rw [d.c.fst_apply (by rw [hfsec]; exact hxV), hfsec]
  exact (PX.mem_levelSet_iff d.c.isChart hxV).1 hz

/-- **`f̃(r, x) = ((r, x), f(x))` is an sc-Fredholm section of `π*P`** (the text: "the section
`f̃` of `π*(P)` ... is a sc-Fredholm section as is readily verified"). -/
theorem IsScFredholmSectionWholeChart.param (hf : B.IsScFredholmSectionWholeChart f) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSectionWholeChart
      (paramLift (n := n) f hf.isScSmooth.1) where
  isScSmooth := hf.isScSmooth.pullback _
  regularizing := regularizing_paramLift_wholeChart hf
  germ z hz :=
    (hf.germ z.2 (prod_rn_mem_smoothSet_iff.1 hz)).param hf.isScSmooth.1 z.1

end StrongBundle

/-- **Theorem 3.18 (parametrized perturbations).**  Let `P : Y → X` be a strong bundle, `f` an
sc-Fredholm section and `s₁, …, sₙ` sc⁺-sections of `P`.  Then
`F(r, x) = f(x) + Σ rᵢ sᵢ(x)` is an sc-Fredholm section of the pull-back bundle
`π*P : π*Y → ℝⁿ × X`, `π(r, x) = x` (Proposition 2.54, `StrongBundle.pullback`).

The proof is the text's: `F = f̃ + s̃` fibrewise (`paramSection_eq_sectionAdd`), `f̃` is
sc-Fredholm (`IsScFredholmSectionWholeChart.param`), `s̃` is sc⁺ (`isScPlusSection_paramComb`), and
Theorem 3.15 applies.  The text assumes `P` tame; tameness is not used (as for Theorem 3.15), and
`π*P` is tame when `P` is (`prod_rn_isTame`).  The paracompactness of `ℝⁿ × X` and of `π*Y` are
instance arguments; they hold by `MPolyfold.paracompactSpace_prod` and
`paracompactSpace_pullbackSpace`. -/
theorem theorem_3_18_wholeChart {B : StrongBundle PX P} {f : X → Y} (hf : B.IsScFredholmSectionWholeChart f)
    {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i)) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSectionWholeChart
      (paramSection f hf.isScSmooth.1 s fun i => (hs i).1) := by
  rw [paramSection_eq_sectionAdd]
  exact theorem_3_15_wholeChart hf.param (StrongBundle.isScPlusSection_paramComb hs)

omit [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- **Theorem 3.18 with no instance argument**: the paracompactness of `ℝⁿ × X` and of `π*Y`
(Definitions 2.13 and 2.51) is supplied by Theorem 2.16 (`MPolyfold.paracompactSpace_prod`,
`paracompactSpace_pullbackSpace`), in the form of `proposition_2_54`. -/
theorem theorem_3_18'_wholeChart {B : StrongBundle PX P} {f : X → Y} (hf : B.IsScFredholmSectionWholeChart f)
    {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i)) :
    haveI := MPolyfold.paracompactSpace_prod (rnPolyfold n) PX
    haveI := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin n → ℝ) × X → X))
      ((rnPolyfold n).prod PX) B
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSectionWholeChart
      (paramSection f hf.isScSmooth.1 s fun i => (hs i).1) := by
  have := MPolyfold.paracompactSpace_prod (rnPolyfold n) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin n → ℝ) × X → X))
    ((rnPolyfold n).prod PX) B
  exact theorem_3_18_wholeChart hf hs

/-! ### Theorem 3.18 for tame germ data -/

namespace PullbackChartData

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- **The product chart of a tame chart is tame**: the base retraction of the product chart
`(r ↦ r − r₀) × φ` is `1 × r` on `ℝⁿ × U`; the factor `ℝⁿ` is free (the identity retraction of
the whole space, `ScRetraction.id_isTame`), so `d(a, u) = d_C(u)`, and the minimal subspaces and
the tangent spaces are products (exposition Lemma 4.D, `ScRetraction.IsTameWith.prod`). -/
theorem ofProd_isTame (c : StrongBundleChart PX P) (r₀ : Fin n → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (hc : (c.isRetraction.baseRetraction c.relOpen).IsTame) :
    (((ofProd c r₀).toChart q₀).isRetraction.baseRetraction
      ((ofProd c r₀).toChart q₀).relOpen).IsTame := by
  obtain ⟨n₁, W₁, T₁, hT₁⟩ := (rn_relOpen_univ n).isPartialQuadrant
  obtain ⟨n₂, W₂, T₂, hT₂⟩ := c.relOpen.isPartialQuadrant
  have h := ScRetraction.IsTameWith.prod hT₁ hT₂
    (ScRetraction.id_isTame (rn_relOpen_univ n) n₁ W₁ T₁ hT₁) (hc n₂ W₂ T₂ hT₂)
  exact h.isTame (prod_eq_prodPresentation T₁ T₂ hT₁ hT₂)

end PullbackChartData

namespace StrongBundle

variable {B : StrongBundle PX P} {f : X → Y}

/-- **The germ property of `f̃ = f ∘ π` at `(r₀, x)` in a tame chart**: if `(f, x)` has germ data in
a tame chart `c` (Definition 3.50), then `(f̃, (r₀, x))` has germ data in the product chart
`(r ↦ r − r₀) × φ` (`IsScFredholmGermWholeChart.param`), which is tame (`ofProd_isTame`). -/
theorem IsScFredholmGermTameWholeChart.param (hfs : IsSection P f) {x : X}
    (hg : B.IsScFredholmGermTameWholeChart f x) (r₀ : Fin n → ℝ) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmGermTameWholeChart
      (paramLift (n := n) f hfs) (r₀, x) := by
  obtain ⟨hxs, c, hct, hxV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj⟩ := hg
  set d := PullbackChartData.ofProd (n := n) c r₀ with hd
  set q₀ := paramLift (n := n) f hfs (r₀, x) with hq₀
  have hU := c.relOpen.isScDomain
  have hU' : IsRelOpenInQuadrant (rnSc n |>.prod c.φ.model.E) (univ ×ˢ c.φ.model.C)
      (univ ×ˢ c.U) := c.relOpen.univ_prod (Fin n → ℝ)
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := h0 ▸ c.φ.mapsTo_model x hxV
  have hsnd := (ScBanach.prodSndOp (rnSc n) c.φ.model.E).isScSmooth hU'.isScDomain
  refine ⟨prod_rn_mem_smoothSet_iff.2 hxs, d.toChart q₀,
    ⟨d.isChart_toChart B _ hct.1 q₀, PullbackChartData.ofProd_isTame c r₀ q₀ hct.2⟩,
    show (r₀, x) ∈ d.ψ.source from ⟨mem_univ _, hxV⟩, ?_, ⟨mem_univ _, h0U⟩,
    fun w => g w.2, fun w => t₀ w.2, ⟨?_, ?_⟩, ?_, ht₀0, ?_⟩
  · change ((r₀ - r₀, c.φ x) : (Fin n → ℝ) × c.φ.model.E 0) = 0
    rw [sub_self, h0]
    rfl
  · exact IsScSmooth.comp hU'.isScDomain hU hfill.isScSmooth hsnd fun w hw => hw.2
  · exact PullbackChartData.ofProd_isFillerOf c r₀ q₀ h0U h0O hfill.filler
  · exact IsScSmooth.comp hU'.isScDomain hU ht₀ hsnd fun w hw => hw.2
  · exact IsConjugateToBasicGerm.paramExtend (Fin n → ℝ) c.relOpen hconj

/-- **`f̃(r, x) = ((r, x), f(x))` is an sc-Fredholm section of `π*P` with tame germ data** when
`f` has tame germ data (Definition 3.51): `IsScFredholmSectionWholeChart.param` and the tame product charts
of `IsScFredholmGermTameWholeChart.param`. -/
theorem IsScFredholmSectionTameWholeChart.param (hf : B.IsScFredholmSectionTameWholeChart f) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSectionTameWholeChart
      (paramLift (n := n) f hf.isScSmooth.1) where
  toIsScFredholmSectionWholeChart := hf.toIsScFredholmSectionWholeChart.param
  germTame z hz :=
    (hf.germTame z.2 (prod_rn_mem_smoothSet_iff.1 hz)).param hf.isScSmooth.1 z.1

end StrongBundle

/-- **Theorem 3.18 for a tame strong bundle** (parametrized perturbations, Definition 3.51):
if `f` is an sc-Fredholm section with tame germ data and `s₁, …, sₙ` are sc⁺-sections, then
`F(r, x) = f(x) + Σ rᵢ sᵢ(x)` is an sc-Fredholm section of `π*P` with tame germ data: `F = f̃ + s̃`,
`f̃` has tame germ data in the product charts (`IsScFredholmSectionTameWholeChart.param`), and Theorem 3.15
keeps the chart (`theorem_3_15_tame_wholeChart`).  This is what the implicit function theorems of §3.6 need
for `F` (Chapter 5, Theorem 5.13). -/
theorem theorem_3_18_tame_wholeChart {B : StrongBundle PX P} {f : X → Y} (hf : B.IsScFredholmSectionTameWholeChart f)
    {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i)) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSectionTameWholeChart
      (paramSection f hf.isScSmooth.1 s fun i => (hs i).1) := by
  rw [paramSection_eq_sectionAdd]
  exact theorem_3_15_tame_wholeChart hf.param (StrongBundle.isScPlusSection_paramComb hs)

/-! ### The linearization of `F` in the product chart -/

/-- **The linearization of `F` at the centre of the product chart** (used for transversality, as
in the text after Theorem 3.19): in the product chart `(r ↦ r − r₀) × Φ` pulled back from a strong
bundle chart `c` with `0 ∈ O`, the derivative of `F̂ ∘ (1 × r)` at `0` is
`(δa, δu) ↦ D(Ĝ ∘ r)(0) δu + Σ δaᵢ ŝᵢ(0)`, `Ĝ = f̂ + Σ r₀ᵢ ŝᵢ` the principal part of
`f + Σ r₀ᵢ sᵢ` (the product rule at `a = 0`: the term `Σ aᵢ D(ŝᵢ ∘ r)` vanishes there). -/
theorem scDeriv_paramSection_wholeChart {B : StrongBundle PX P} {f : X → Y} (hf : B.IsScFredholmSectionWholeChart f)
    {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i)) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O) (r₀ : Fin n → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) (v : (Fin n → ℝ) × c.φ.model.E 0) :
    scDeriv (univ ×ˢ c.U) (((PullbackChartData.ofProd c r₀).toChart q₀).principal
        (paramSection f hf.isScSmooth.1 s fun i => (hs i).1) ∘
          StrongRetr.r ((PullbackChartData.ofProd c r₀).toChart q₀).R)
        (0 : (rnSc n |>.prod c.φ.model.E) 1) v =
      scDeriv c.U ((fun u => c.principal f u + ∑ i, r₀ i • c.principal (s i) u) ∘
        StrongRetr.r c.R) (0 : c.φ.model.E 1) v.2 + ∑ i, v.1 i • c.principal (s i) 0 := by
  set d := PullbackChartData.ofProd (n := n) c r₀ with hd
  set c' := d.toChart q₀ with hc'
  set Fs := paramSection f hf.isScSmooth.1 s fun i => (hs i).1 with hFs
  have hU := c.relOpen.isScDomain
  have hU' : IsRelOpenInQuadrant (rnSc n |>.prod c.φ.model.E) (univ ×ˢ c.φ.model.C)
      (univ ×ˢ c.U) := c.relOpen.univ_prod (Fin n → ℝ)
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hr0 : StrongRetr.r c.R 0 = 0 := StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ h0O)
  -- the pieces on `U`
  have hfr : IsScSmooth c.U (c.principal f ∘ StrongRetr.r c.R) :=
    (((hf.isScSmooth.isScSmoothRetractMap hc).comp_isScSmooth
      (c.isRetraction.baseRetraction c.relOpen) c.base_retract).snd hU).congr hU fun _ _ => rfl
  have hsr : ∀ i, IsScSmooth c.U (c.principal (s i) ∘ StrongRetr.r c.R) := fun i => by
    have hlift : IsScSmooth (F := c.F.shift) c.U
        fun u => c.principalLift (s i) (StrongRetr.r c.R u) :=
      (((hs i).isScSmoothRetractMap_one hc).comp_isScSmooth
        (c.isRetraction.baseRetraction c.relOpen) c.base_retract).snd hU |>.congr hU
        fun _ _ => rfl
    exact (hlift.toBase_shift hU).congr hU fun u hu => (hs i).toBase_principalLift hc (c.r_mem_O hu)
  have hGr : IsScSmooth c.U ((fun u => c.principal f u + ∑ i, r₀ i • c.principal (s i) u) ∘
      StrongRetr.r c.R) := by
    have hconst : ∀ i, IsScSmooth (F := ScBanach.const ℝ) c.U fun _ => r₀ i := fun i =>
      IsScSmooth.of_contDiffOn_finiteDimensional hU contDiffOn_const
    exact (hfr.add hU (IsScSmooth.finsetSum hU _ fun i _ => (hconst i).smul hU (hsr i))).congr hU
      fun _ _ => rfl
  -- the map `Φ = F̂ ∘ (1 × r)` is sc¹ on `ℝⁿ × U`, and equal there to
  -- `Ψ(a, u) = Ĝ(r(u)) + Σ aᵢ ŝᵢ(r(u))`
  have hc'B : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsChart c' :=
    d.isChart_toChart B _ hc q₀
  have hΦ : IsScSmooth (univ ×ˢ c.U) (c'.principal Fs ∘ StrongRetr.r c'.R) :=
    ((((theorem_3_18_wholeChart hf hs).isScSmooth.isScSmoothRetractMap hc'B).comp_isScSmooth
      (c'.isRetraction.baseRetraction c'.relOpen) c'.base_retract).snd hU'.isScDomain).congr
      hU'.isScDomain fun _ _ => rfl
  have hΦΨ : ∀ w ∈ (univ ×ˢ c.U : Set ((Fin n → ℝ) × c.φ.model.E 0)),
      (c'.principal Fs ∘ StrongRetr.r c'.R) w =
        ((fun u => c.principal f u + ∑ i, r₀ i • c.principal (s i) u) ∘ StrongRetr.r c.R) w.2 +
          ∑ i, w.1 i • (c.principal (s i) ∘ StrongRetr.r c.R) w.2 := by
    intro w hw
    have hrw : StrongRetr.r c.R w.2 ∈ c.φ.model.O := c.r_mem_O hw.2
    have := PullbackChartData.ofProd_principal_paramSection c r₀ q₀ hf.isScSmooth.1
      (fun i => (hs i).1) (w := (w.1, StrongRetr.r c.R w.2)) hrw
    refine this.trans ?_
    simp only [Function.comp_apply, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  -- the derivative on level `1`
  have h01 : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  have h0' : (0 : (rnSc n |>.prod c.φ.model.E) 1) ∈
      (rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1 := by
    change (rnSc n |>.prod c.φ.model.E).toBase 1 0 ∈ univ ×ˢ c.U
    rw [map_zero]
    exact ⟨mem_univ _, h0U⟩
  set D := scDeriv c.U ((fun u => c.principal f u + ∑ i, r₀ i • c.principal (s i) u) ∘
    StrongRetr.r c.R) (0 : c.φ.model.E 1) with hD
  set L : (Fin n → ℝ) × c.φ.model.E 0 →L[ℝ] c.F 0 :=
    D.comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (c.φ.model.E 0)) +
      ∑ i, ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (c.φ.model.E 0))).smulRight
          (c.principal (s i) 0) with hL
  have hmaps : MapsTo (Prod.snd : (Fin n → ℝ) × c.φ.model.E 1 → c.φ.model.E 1)
      ((rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1) (c.φ.model.E.lvlSet c.U 1) := by
    intro w hw
    have := hw
    rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase] at this
    exact this.2
  have hb : ∀ w : (rnSc n |>.prod c.φ.model.E) 1,
      (rnSc n |>.prod c.φ.model.E).toBase 1 w = (w.1, c.φ.model.E.toBase 1 w.2) := fun w => by
    rw [ScBanach.prod_toBase, ScBanach.const_toBase]
  have hderG := (hGr.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01).comp
    (0 : (rnSc n |>.prod c.φ.model.E) 1) hasFDerivWithinAt_snd hmaps
  have hderS : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasFDerivWithinAt
      (fun w : (rnSc n |>.prod c.φ.model.E) 1 =>
        w.1 i • ((c.principal (s i) ∘ StrongRetr.r c.R) ∘ c.φ.model.E.toBase 1) w.2)
      ((0 : (rnSc n |>.prod c.φ.model.E) 1).1 i •
          ((scDeriv c.U (c.principal (s i) ∘ StrongRetr.r c.R) 0).comp (c.φ.model.E.toBase 1)).comp
            (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (c.φ.model.E 1)) +
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ)
          (c.φ.model.E 1))).smulRight
          (((c.principal (s i) ∘ StrongRetr.r c.R) ∘ c.φ.model.E.toBase 1)
            (0 : (rnSc n |>.prod c.φ.model.E) 1).2))
      ((rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1) 0 := by
    intro i _
    have h1 : HasFDerivWithinAt (fun w : (rnSc n |>.prod c.φ.model.E) 1 => w.1 i)
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ)
          (c.φ.model.E 1))) ((rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1) 0 :=
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ)
        (c.φ.model.E 1))).hasFDerivWithinAt
    have h2 := ((hsr i).isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01).comp
      (0 : (rnSc n |>.prod c.φ.model.E) 1) hasFDerivWithinAt_snd hmaps
    exact h1.fun_smul h2
  have hderΨ := hderG.add (HasFDerivWithinAt.fun_sum hderS)
  have hderΦ : HasFDerivWithinAt ((c'.principal Fs ∘ StrongRetr.r c'.R) ∘
      (rnSc n |>.prod c.φ.model.E).toBase 1) (L.comp ((rnSc n |>.prod c.φ.model.E).toBase 1))
      ((rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1) 0 := by
    refine (hderΨ.congr (fun w hw => ?_) ?_).congr_fderiv ?_
    · have := hΦΨ _ hw
      rw [hb] at this
      exact this
    · have := hΦΨ _ h0'
      rw [hb] at this
      exact this
    · refine ContinuousLinearMap.ext fun w => ?_
      simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
        FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply,
        Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_smul, zero_add, map_zero, hr0, hL, hb]
      rfl
  have hderΦ' := hΦ.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h0'
  have heq := ContinuousLinearMap.ext_of_comp_toBase_one (E := rnSc n |>.prod c.φ.model.E)
    ((hU'.isScDomain.uniqueDiffWithinAt 1 0 h0').eq hderΦ' hderΦ)
  have hv := congrArg (fun T : (rnSc n |>.prod c.φ.model.E) 0 →L[ℝ] c.F 0 => T v) heq
  refine hv.trans ?_
  simp only [hL, add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply]

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- `D(1 × r)(0) = 1 × Dr(0)` in the product chart. -/
lemma PullbackChartData.ofProd_scDeriv_r (c : StrongBundleChart PX P) (r₀ : Fin n → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) (h0U : (0 : c.φ.model.E 0) ∈ c.U)
    (v : (Fin n → ℝ) × c.φ.model.E 0) :
    scDeriv (univ ×ˢ c.U) (StrongRetr.r ((ofProd c r₀).toChart q₀).R)
      (0 : (rnSc n |>.prod c.φ.model.E) 1) v = (v.1, scDeriv c.U (StrongRetr.r c.R) 0 v.2) := by
  have h0' : (0 : (rnSc n |>.prod c.φ.model.E) 1) ∈
      (rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1 := by
    change (rnSc n |>.prod c.φ.model.E).toBase 1 0 ∈ univ ×ˢ c.U
    rw [map_zero]
    exact ⟨mem_univ _, h0U⟩
  have h1 := scDeriv_prodMap (F := rnSc n) (F' := c.φ.model.E) (rn_relOpen_univ n) c.relOpen
    (isScSmooth_id (isScDomain_univ (rnSc n)))
    (c.isRetraction.baseRetraction c.relOpen).isScSmooth h0'
  have e := congrArg (fun L : (rnSc n |>.prod c.φ.model.E) 0 →L[ℝ]
    (rnSc n |>.prod c.φ.model.E) 0 => L v) h1
  have h2 : scDeriv (E := rnSc n) (F := rnSc n) univ id (0 : (rnSc n) 1) =
      ContinuousLinearMap.id ℝ (Fin n → ℝ) :=
    IsSc1.scDeriv_eqOn (isSc1With_id univ) ((rn_relOpen_univ n).isScDomain.uniqueDiffWithinAt 1)
      (by rw [ScBanach.mem_lvlSet]; exact mem_univ _)
  refine e.trans (Prod.ext ?_ rfl)
  exact congrArg (fun L : (rnSc n) 0 →L[ℝ] (rnSc n) 0 => L v.1) h2

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- The tangent space of the product chart at `0`: `T₀(ℝⁿ × O) ⊆ ℝⁿ × T₀O`. -/
lemma PullbackChartData.ofProd_mem_tangent (c : StrongBundleChart PX P) (r₀ : Fin n → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) (h0U : (0 : c.φ.model.E 0) ∈ c.U)
    {w : (Fin n → ℝ) × c.φ.model.E 0}
    (hw : w ∈ rangeS (scDeriv ((ofProd c r₀).toChart q₀).U
      (StrongRetr.r ((ofProd c r₀).toChart q₀).R) (0 : ((ofProd c r₀).toChart q₀).φ.model.E 1))) :
    w.2 ∈ rangeS (scDeriv c.U (StrongRetr.r c.R) (0 : c.φ.model.E 1)) := by
  obtain ⟨y, hy⟩ := hw
  refine ⟨y.2, ?_⟩
  have := (ofProd_scDeriv_r c r₀ q₀ h0U y).symm.trans hy
  exact congrArg Prod.snd this

/-- **The linearization of `F` at the centre `(r₀, x)` of the product chart, in the chart form
`linAt` of `LinearizationCharts.lean`**: on `T₀(ℝⁿ × O) = ℝⁿ × T₀O`,
`Lin_F(0)(δa, δu) = Lin_G(0) δu + Σ δaᵢ ŝᵢ(0)` with `G = f + Σ r₀ᵢ sᵢ`. -/
theorem linAt_paramSection_wholeChart {B : StrongBundle PX P} {f : X → Y} (hf : B.IsScFredholmSectionWholeChart f)
    {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i)) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O) (r₀ : Fin n → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) {w : (Fin n → ℝ) × c.φ.model.E 0}
    (hw : w ∈ rangeS (scDeriv ((PullbackChartData.ofProd c r₀).toChart q₀).U
      (StrongRetr.r ((PullbackChartData.ofProd c r₀).toChart q₀).R)
      (0 : ((PullbackChartData.ofProd c r₀).toChart q₀).φ.model.E 1))) :
    linAt ((PullbackChartData.ofProd c r₀).toChart q₀).U
        ((PullbackChartData.ofProd c r₀).toChart q₀).R
        (((PullbackChartData.ofProd c r₀).toChart q₀).principal
          (paramSection f hf.isScSmooth.1 s fun i => (hs i).1)) 0 ⟨w, hw⟩ =
      linAt c.U c.R (fun u => c.principal f u + ∑ i, r₀ i • c.principal (s i) u) 0
          ⟨w.2, PullbackChartData.ofProd_mem_tangent c r₀ q₀
            (StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)) hw⟩ +
        ∑ i, w.1 i • c.principal (s i) 0 :=
  scDeriv_paramSection_wholeChart hf hs hc h0O r₀ q₀ w

/-- **The text's form** (after Theorem 3.19): at `r₀ = 0` the linearization of `F` at `(0, x)` is
`(δr, ξ) ↦ f'(x)ξ + Σ δrᵢ sᵢ(x)`, in the chart form `Lin_F(0)(δa, δu) = Lin_f(0) δu +
Σ δaᵢ ŝᵢ(0)`. -/
theorem linAt_paramSection_zero_wholeChart {B : StrongBundle PX P} {f : X → Y}
    (hf : B.IsScFredholmSectionWholeChart f) {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i))
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) {w : (Fin n → ℝ) × c.φ.model.E 0}
    (hw : w ∈ rangeS (scDeriv ((PullbackChartData.ofProd c 0).toChart q₀).U
      (StrongRetr.r ((PullbackChartData.ofProd c 0).toChart q₀).R)
      (0 : ((PullbackChartData.ofProd c 0).toChart q₀).φ.model.E 1))) :
    linAt ((PullbackChartData.ofProd c 0).toChart q₀).U
        ((PullbackChartData.ofProd c 0).toChart q₀).R
        (((PullbackChartData.ofProd c 0).toChart q₀).principal
          (paramSection f hf.isScSmooth.1 s fun i => (hs i).1)) 0 ⟨w, hw⟩ =
      linAt c.U c.R (c.principal f) 0
          ⟨w.2, PullbackChartData.ofProd_mem_tangent c 0 q₀
            (StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)) hw⟩ +
        ∑ i, w.1 i • c.principal (s i) 0 := by
  rw [linAt_paramSection_wholeChart hf hs hc h0O 0 q₀ hw]
  have : (fun u => c.principal f u + ∑ i, (0 : Fin n → ℝ) i • c.principal (s i) u) =
      c.principal f := funext fun u => by simp
  simp only [this]
  rfl

end Param

end Polyfold
