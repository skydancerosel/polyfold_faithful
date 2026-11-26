import Polyfold.Chapter6.OrientationMainClean
import Polyfold.Chapter6.CubePropertyP
import Polyfold.Chapter6.UnitIntervalSections
import Polyfold.Chapter6.ParamKernel
import Polyfold.Chapter6.LinOrientation
import Polyfold.Chapter7.DegeneracyZeroTame

/-!
Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I: The Polyfolds of Gromov–Witten Theory*
(Memoirs AMS 248, 2017), Appendix 5.10.3–5.10.4, pp. 181–187: **Definitions 5.17, 5.19, 5.25**,
**Propositions 5.18, 5.26**, **Lemmas 5.20–5.24**, and the polyfold case 5.27–5.32, in the
memoir's form (an M-polyfold `X` without boundary, `∂X = ∅`, with sc-smooth partitions of unity),
proved from the book's §6.6 (2021, pp. 261–276).

# Orientations of sc-Fredholm sections over `X` without boundary

## What is formalized

* `memoirLin`, `memoirDET`, `memoirOr` (**Definitions 5.17, 5.19**): the book's `Lin(f, x)`,
  `DET(f, x)` and `Or_x^f` (Definitions 6.2.1, 6.6.2); `memoir_proposition_5_18` (**Proposition
  5.18**): `DET(f, x)` is a topological line bundle with exactly two orientations
  (Proposition 6.6.1).
* `memoir_lemma_5_20` (**Lemma 5.20**): Proposition 6.6.3 (3) on `[0, 1]`, for a path in the
  domain of one strong bundle chart.
* `memoir_lemma_5_21` (**Lemma 5.21**): for `X` without boundary (`d_X ≡ 0`) the memoir's
  property (∗), surjectivity of the linearization of `F_t` at `(0, φ(t))` for every `t ∈ [0, 1]`,
  from the book's property (P) of Lemma 6.6.4 (general position, which contains the surjectivity);
  the tameness of `X` asked by the book holds since `d_X ≡ 0`
  (`MPolyfold.isTame_of_degIndex_eq_zero`).
* `memoir_lemma_5_22` (**Lemma 5.22**): the book's Lemma 6.6.6.
* `memoir_lemma_5_24` (**Lemmas 5.23–5.24**): for `X` without boundary, the propagation of
  orientations is independent of the choices and invariant under sc-smooth homotopy with fixed
  end points: the unique functor `Γ_f` on the category `PX` of homotopy classes of sc-smooth
  paths with property (∗) (Theorem 6.6.13), tameness of `X` again from `d_X ≡ 0`.
* `memoirSectionOrientation` (**Definition 5.25**) and `memoir_proposition_5_26`
  (**Proposition 5.26**): Definition 6.6.16 and Theorem 6.6.18 for `X` without boundary.

## Readings and differences

* The memoir works with sc-Hilbert models; the book's statements hold for sc-Banach models, and
  the Hilbert case is a special case.  "X has no boundary" is `∀ x, PX.degIndex x = 0`; "sc-smooth
  partitions of unity" is read as the book's `PX.AdmitsBumpFunctions`.
* The book asks the germs of `f` to be tame (`IsScFredholmSectionTame`, Definition 3.6.4); the
  memoir does not mention this.  For `d_X ≡ 0` it is expected to follow from the sc-Fredholm
  property by restricting strong bundle charts (the bundle analogue of
  `MPolyfold.isTame_of_degIndex_eq_zero`); this lemma is not in the project, and the hypothesis
  is kept.
* Lemma 5.20 asks a section `s` over `[0, 1] × X` for any sc-smooth path; the book's Proposition
  6.6.3 (3) is proved for a path in the domain of one chart (the book propagates locally and
  composes), which is the form proved here.
* Lemma 5.22 is the book's Lemma 6.6.6, whose surjectivity hypothesis is that of the full section
  `F` at `(0, (t, φ(t)))`; the memoir's (∗) is the surjectivity of the slice `F_t`, which gives
  it.
* Proposition 5.26 asks `f'(x)` onto at the zeros; the book's Theorem 6.6.18 asks general position
  at the zeros, which contains the surjectivity; that the two agree for `d_X ≡ 0` is not proved
  here, and general position is kept.
* Definition 5.25 asks the orientations to propagate along every sc-smooth path; the book's
  Definition 6.6.16 asks continuity over orientable neighbourhoods, related to propagation by
  Theorems 6.6.13 and 6.6.17.  The memoir's definition is read as the book's.
* The polyfold case (5.27–5.32) is the book's Chapter 12 and Chapter 18: Definition 5.27 and
  Lemma 5.28 are Definition 12.5.2 and Theorem 12.5.3 (`Polyfold.orMor`, `Polyfold.pushOr`,
  `Polyfold.pullOr`); Remark 5.29 is the action of automorphisms on `DET(F, x)` in
  `Chapter12/OrientationBundleEp.lean`; Lemma 5.30 is Theorem 12.5.7; Definition 5.31 is
  Definition 12.5.4 (`Polyfold.definition_12_5_4`); Definition 5.32 is Definition 18.5.4
  (`IsOrientable` in `Chapter18/Orientations.lean`), read through the reference model of
  Chapter 18.  These are recorded as readings; no separate statements are made here.
-/

open Set Filter Topology Function Bundle CategoryTheory
open Polyfold Polyfold.StrongRetr Polyfold.StrongBundle Polyfold.UnitCube

noncomputable section

namespace GWMemoir

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### Definitions 5.17, 5.19 and Proposition 5.18 -/

section Lin

variable {x : X} (p : ChartPoint B x)

variable (f) in
/-- **Memoir Definition 5.17, p. 181**: `Lin(f, x₀) = {(f − s)'(x₀) + a | a an sc⁺-operator}`, the
book's Definition 6.2.1 (2021, p. 261), read in a chart point (`ChartPoint.linSet`). -/
abbrev memoirLin : Set (↥p.T →L[ℝ] ↥p.K) := p.linSet f

variable (f) in
/-- **Memoir Proposition 5.18, p. 182, the bundle**: `DET(f, x₀) = ⋃_{A ∈ Lin(f, x₀)} {A} × det(A)`,
the restriction of `DET(T_{x₀}X, E_{x₀})` to `Lin(f, x₀)`. -/
abbrev memoirDET (hf : B.IsScFredholmSection f) : p.linSet f → Type _ := p.detLin f hf

variable (f) in
/-- **Memoir Definition 5.19, p. 182**: an orientation of `f` at the smooth point `x₀` is one of
the two orientations of `DET(f, x₀)` (the book's Definition 6.6.2, `Or_x^f`). -/
abbrev memoirOr (hf : B.IsScFredholmSection f) : Type _ := p.Or f hf

/-- **Memoir Proposition 5.18, p. 182**: `DET(f, x₀)` is in a natural way a topological line bundle
over the convex set `Lin(f, x₀)`, and it has exactly two orientations (the book's Proposition
6.6.1, 2021 p. 262).  `hsec` (an sc⁺-section through `−f(x₀)`, which makes `Lin(f, x₀)` nonempty)
holds with sc-smooth bump functions (`MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough`). -/
theorem memoir_proposition_5_18 (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (hsec : B.HasScPlusSectionsThrough) :
    VectorBundle ℝ ℝ (memoirDET f p hf) ∧
      ∃ o₁ o₂ : memoirOr f p hf, o₁ ≠ o₂ ∧ ∀ o, o = o₁ ∨ o = o₂ :=
  proposition_6_6_1 (p.convex_linSet hf) (p.linSet_nonempty hf hx hsec)
    (p.isFredholm_of_mem_linSet hf)

end Lin

/-! ### Lemmas 5.20–5.22 -/

/-- **Memoir Lemma 5.20, p. 182**: an sc⁺-section `s` of the pull-back of `E` to `[0, 1] × X` with
`s(t, φ(t)) = f(φ(t))` (with the sign convention of `sectionAdd`: `(f + S)(t, φ(t)) = 0`); the
book's Proposition 6.6.3 (3) on `[0, 1]` (2021, p. 263), for a path in the domain of one chart. -/
theorem memoir_lemma_5_20 [ParacompactSpace (unitInterval × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : unitInterval × X → X))]
    (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScSmoothSection f)
    {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts)
    {φ : unitInterval → X} (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ)
    (hφc : ∀ t, φ t ∈ c.φ.source) :
    ∃ S : unitInterval × X → pullbackSpace P (Prod.snd : unitInterval × X → X),
      (B.pullback (MPolyfold.isScSmoothMap_snd unitIntervalPolyfold PX)).IsScPlusSection S ∧
      ∀ t, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd)
          (pullbackLift Prod.snd (f ∘ Prod.snd) fun z => hf.1 z.2) S) (t, φ t) := by
  obtain ⟨-, S, -, -, -, hS, -, hz⟩ := proposition_6_6_3_three_interval hbump hf hc hφ hφc
  exact ⟨S, hS, hz⟩

/-- **Memoir Lemma 5.21, p. 182**, for `X` without boundary: given the section `S` of Lemma 5.20
along an sc-smooth path `φ : [0, 1] → X` (here `[0, 1]¹`), there are finitely many sc⁺-sections
`s₁, …, s_k` of the pull-back bundle over `[0, 1] × X` such that (∗) for every `t ∈ [0, 1]` the
linearization of `F_t(λ, y) = f(y) + S(t, y) + Σ λᵢ sᵢ(t, y)` at `(0, φ(t))` is surjective.
From the book's Lemma 6.6.4 (property (P), 2021 p. 264), whose general position contains the
surjectivity; `X` is tame since `d_X ≡ 0`. -/
theorem memoir_lemma_5_21
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]
    (hbd : ∀ x, PX.degIndex x = 0) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {φ : (Fin 1 → unitInterval) → X}
    (hφ : (cubePolyfold 1).IsScSmoothMap PX φ)
    {S : (Fin 1 → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX)).IsScPlusSection S)
    (hz : ∀ t, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (t, φ t)) :
    ∃ (k : ℕ) (s : Fin k → (Fin 1 → unitInterval) × X →
        pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
      (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX)).IsScPlusSection
        (s i)),
      ∀ [ParacompactSpace ((Fin k → ℝ) × X)]
        [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
        [ParacompactSpace ((Fin k → ℝ) × ((Fin 1 → unitInterval) × X))]
        [ParacompactSpace (pullbackSpace (pullbackProj P
          (Prod.snd : (Fin 1 → unitInterval) × X → X))
          (Prod.snd : (Fin k → ℝ) × ((Fin 1 → unitInterval) × X) → (Fin 1 → unitInterval) × X))],
        ∀ t : Fin 1 → unitInterval,
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsLinSurjAt
            (paramSection
              (prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) t)
              (((isSection_pullbackLift _).sectionAdd hS.1).prodSlice t)
              (fun i => prodSlice (s i) t) fun i => (hs i).1.prodSlice t) (0, φ t) := by
  obtain ⟨k, s, hs, hP⟩ :=
    lemma_6_6_4_propertyP_cube (PX.isTame_of_degIndex_eq_zero hbd) hbump hf hφ hS hz
  exact ⟨k, s, hs, fun {_ _ _ _} t => (hP t).1.isLinSurjAt⟩

/-- **Memoir Lemma 5.22, p. 183**: the sequence (5.75)
`0 → ker((f − s(t, ·))'(φ(t))) →j ker(F_t'(0, φ(t))) →p ℝᵏ →c E_{φ(t)}/R((f − s(t, ·))'(φ(t))) → 0`
is exact: the book's Lemma 6.6.6 (2021, p. 266). -/
alias memoir_lemma_5_22 := lemma_6_6_6

/-! ### Lemmas 5.23–5.24 and Definition 5.25 -/

/-- **Memoir Lemmas 5.23 and 5.24, p. 184**, for `X` without boundary: the propagation of an
orientation along sc-smooth paths does not depend on the choices of `s`, `sᵢ`, and two paths with
the same end points which are sc-smoothly homotopic (end points fixed) propagate an orientation to
the same orientation: there is a unique functor `Γ_f` on the category `PX` of homotopy classes of
sc-smooth paths with property (∗) of the book's Theorem 6.6.13 (2021, p. 273).  The tameness of
`X` asked there holds since `d_X ≡ 0`. -/
theorem memoir_lemma_5_24 (hbd : ∀ x, PX.degIndex x = 0) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) :
    haveI := paracompactSpace_rn_prod PX
    haveI := paracompactSpace_rn_pullback B
    ∃! G : ∀ x y : PathCat PX, (x ⟶ y) →
        (Orx f hf.toIsScFredholmSection x.pt x.smooth ≃
          Orx f hf.toIsScFredholmSection y.pt y.smooth),
      (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
      (∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
        G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
      IsStarProperty f hf.toIsScFredholmSection G :=
  theorem_6_6_13 (PX.isTame_of_degIndex_eq_zero hbd) hbump hf

variable (f) in
/-- **Memoir Definition 5.25, p. 184**: an orientation of `f` (over `X` without boundary) is a
choice of an orientation `o_x` of `DET(f, x)` at every smooth point which propagates along
sc-smooth paths; read as the book's Definition 6.6.16 (2021, p. 274). -/
abbrev memoirSectionOrientation (hf : B.IsScFredholmSection f) : Type _ :=
  SectionOrientation f hf

/-- **Memoir Proposition 5.26, p. 184**, for `X` without boundary: for a proper oriented
sc-Fredholm section `f`, in general position at its zeros, `M = f⁻¹(0)` is a smooth compact
manifold with the natural orientation given by `o` (the book's Theorem 6.6.18, 2021 p. 275; the
tameness of `X` holds since `d_X ≡ 0`). -/
theorem memoir_proposition_5_26 (hbd : ∀ x, PX.degIndex x = 0)
    (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x)
    (o : memoirSectionOrientation f hf.toIsScFredholmSection) :
    B.SolutionSetInGeneralPosition f ∧ IsNaturalSolutionOrientation f hf hgp o :=
  theorem_6_6_18 (PX.isTame_of_degIndex_eq_zero hbd) hf hP hgp o

end GWMemoir
