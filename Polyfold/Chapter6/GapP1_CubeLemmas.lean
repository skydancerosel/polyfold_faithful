import Polyfold.Chapter6.GapP1_CubeFredholm
import Polyfold.Chapter6.SolutionManifoldFamily2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **Lemma 6.6.4**
(general position of `F` along the family) and **Lemma 6.6.5** (the solution set is a manifold
with boundary and corners), pp. 264–265 (preprint Lemmas 6.29–6.30), **for families on the
M-polyfold `[0, 1]ⁿ` itself** (gap G.65 (a), step 5; rows V6.33, V6.34).

# Lemmas 6.6.4–6.6.5 on `[0, 1]ⁿ × X`

## The text, paraphrased

For an sc-smooth path `φ : [0, 1] → X` and an sc⁺-section `s` of the pull-back of `Y → X` to
`X × [0, 1]` with `s(φ(t), t) = f(φ(t))`, the section `F(t, y, λ) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)`
over `[0, 1] × X × ℝᵏ` vanishes at `(t, φ(t), 0)`.  (Lemma 6.6.4) There are `s₁, …, s_k` with
property (P), which implies that `F` is in general position to the boundary of
`[0, 1] × X × ℝᵏ` at all points `(t, φ(t), 0)`.  (Lemma 6.6.5) The solution set `S` near these
points is a smooth manifold with boundary with corners.

## What is formalized

The project's forms (`lemma_6_6_4`, `lemma_6_6_5_isManifold`, `lemma_6_6_5_isSubmanifoldOfDim`)
read the families on `ℝⁿ` (decision D2).  Here the parameter space is `[0, 1]ⁿ`
(`cubePolyfold n`, with its corners), every `q ∈ [0, 1]ⁿ` counts, and `t ∈ [0, 1]` is `n = 1`:

* `theorem_3_1_21_tame_cube`: `F(λ, (q, y)) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)` is an sc-Fredholm
  section with tame germ data of the pull-back bundle over `ℝᵏ × ([0, 1]ⁿ × X)` (through
  `IsScFredholmSectionTame.paramCube`), and `isZeroAt_stab_cube`: `(0, (q, Φ(q)))` is a zero of
  `F` when `(f̃ + S)(q, Φ(q)) = 0`.
* **`lemma_6_6_4_cube`**: for an sc-smooth family `Φ : [0, 1]ⁿ → X` and an sc⁺-section `S` over
  `[0, 1]ⁿ × X` with `(f̃ + S)(q, Φ(q)) = 0` for all `q`, there are finitely many sc⁺-sections
  `s₁, …, s_k` over `[0, 1]ⁿ × X` such that `F` is in general position (Definition 5.3.9) at
  `(0, (q, Φ(q)))` for **every** `q ∈ [0, 1]ⁿ`, including the boundary and corners of
  `[0, 1]ⁿ`.  `lemma_6_6_4_cube_family`: the same with `S` supplied by Proposition 6.6.3 (3) on
  `[0, 1]ⁿ` (`proposition_6_6_3_three_cube`), for `Φ` in the domain of one strong bundle chart.
* **`lemma_6_6_5_isManifold_cube`**, `lemma_6_6_5_isSubmanifoldOfDim_cube`: for such `sᵢ`, near
  every `(0, (q, Φ(q)))` the solution set `S = F⁻¹(0)` is a smooth manifold with boundary and
  corners (Mathlib's `IsManifold (modelWithCornersEuclideanQuadrant d) ∞`), resp. a
  `d`-dimensional submanifold of `ℝᵏ × ([0, 1]ⁿ × X)`; its corners now include those coming
  from `[0, 1]ⁿ`, as in the text.

## Continued in later files

* Property (P) for the slices `F_q` at every `q ∈ [0, 1]ⁿ`, boundary points included, and its
  equivalence with the general position of `F`: `lemma_6_6_4_propertyP_cube`,
  `isGeneralPositionGerm_cubeSlice_iff` (`GapP1_CubeBoundaryP`). The `ℝⁿ` argument
  (`lemma_6_6_4_propertyP`, `ℝⁿ` has no boundary) is replaced at the boundary by a one-sided
  minimum along reduced directions (`mem_minimalSubspaceWith_of_hasFDerivWithinAt`,
  `GapP1_CubeBoundarySlice`). (The example `X = [0, ∞)²`, `f(y) = y₁ + y₂`, `s(y, t) = 2t`,
  `φ(t) = (t, t)`, `k = 0` once noted here does not separate the two: there the reduced tangent
  space of `[0, 1] × X` at `(0, (0, 0))` is `0`, so `F` is not in general position.)
* The submersion `π : S → [0, 1]ⁿ` in the corner sense at boundary points, at the chart level:
  `lemma_6_6_5_submersion_cube` (`GapP1_CubeBoundarySubmersion`); the fibres:
  `lemma_6_6_5_fibre_isManifold_cube`.
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube

section CubeLemmas

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {n : ℕ}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]

/-- **Theorem 3.1.21 over `[0, 1]ⁿ × X`, tame form** (with Theorem 3.1.18): for an sc-Fredholm
section `f` with tame germ data and sc⁺-sections `S`, `s₁, …, s_k` of `pr₂*P` over
`[0, 1]ⁿ × X`, `F(λ, (q, y)) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)` is an sc-Fredholm section with
tame germ data of the pull-back bundle over `ℝᵏ × ([0, 1]ⁿ × X)`. -/
theorem theorem_3_1_21_tame_cube {k : ℕ}
    [ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X))]
    [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))]
    (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    {s : Fin k → (Fin n → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection
      (s i)) :
    ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
        ((cubePolyfold n).prod PX))).IsScFredholmSectionTame
      (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
        ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) :=
  theorem_3_1_21_tame (theorem_3_1_18_tame hf.paramCube hS) hs

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))] in
/-- The points `(0, (q, Φ(q)))` are zeros of `F` when `(f̃ + S)(q, Φ(q)) = 0` (the text's
`F(t, φ(t), 0) = 0`). -/
theorem isZeroAt_stab_cube {k : ℕ} {G : (Fin n → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hG : IsSection (pullbackProj P Prod.snd) G)
    {s : Fin k → (Fin n → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hs : ∀ i, IsSection (pullbackProj P Prod.snd) (s i)) {z : (Fin n → unitInterval) × X}
    (hz : IsZeroAt (pullbackProj P Prod.snd) G z) :
    IsZeroAt (pullbackProj (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd)
      (paramSection G hG s hs) ((0 : Fin k → ℝ), z) := by
  rw [isZeroAt_paramSection_iff]
  change IsZeroAt _ (paramSlice _ _ s hs 0) z
  rw [paramSlice_zero]
  exact hz

/-- **2021 Lemma 6.6.4, p. 264, for families on `[0, 1]ⁿ`** (preprint Lemma 6.29), in the form
the text derives from property (P) ("`F` is in general position to the boundary of
`[0, 1] × X × ℝᵏ` at all points `(t, φ(t), 0)`"): let `X` be tame with sc-smooth bump functions,
`f` an sc-Fredholm section with tame germ data, `Φ : [0, 1]ⁿ → X` sc-smooth and `S` an
sc⁺-section of `pr₂*P` over `[0, 1]ⁿ × X` with `(f̃ + S)(q, Φ(q)) = 0` for all `q`.  Then there
are finitely many sc⁺-sections `s₁, …, s_k` over `[0, 1]ⁿ × X` such that
`F(λ, (q, y)) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)` is in general position at `(0, (q, Φ(q)))` for
**every** `q ∈ [0, 1]ⁿ`.  *Proof*: `f̃ + S` is tame sc-Fredholm over the tame `[0, 1]ⁿ × X`
(`IsScFredholmSectionTame.paramCube`, `prod_cube_isTame`), which admits bump functions
(`admitsBumpFunctions_prod_cube`); `exists_sections_isGeneralPositionGerm_of_isCompact` applies
to the compact set `{(q, Φ(q))}`. -/
theorem lemma_6_6_4_cube (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {Φ : (Fin n → unitInterval) → X}
    (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    (hz : ∀ q, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, Φ q)) :
    ∃ (k : ℕ) (s : Fin k → (Fin n → unitInterval) × X →
        pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
      (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection
        (s i)),
      ∀ [ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X))]
        [ParacompactSpace (pullbackSpace (pullbackProj P
          (Prod.snd : (Fin n → unitInterval) × X → X))
          (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))],
        ∀ q, ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
            (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
              ((cubePolyfold n).prod PX))).IsGeneralPositionGerm
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1)
            (0, (q, Φ q)) := by
  have hΦc : Continuous Φ := continuousOn_univ.1 hΦ.continuousOn
  have hγ : Continuous fun q : Fin n → unitInterval => (q, Φ q) := continuous_id.prodMk hΦc
  have hg := theorem_3_1_18_tame hf.paramCube hS
  have hK : IsCompact (range fun q : Fin n → unitInterval => (q, Φ q)) := isCompact_range hγ
  have hK0 : ∀ x ∈ range fun q : Fin n → unitInterval => (q, Φ q),
      IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) x := by
    rintro _ ⟨q, rfl⟩
    exact hz q
  obtain ⟨k, s, hs, W, -, hKW, hW⟩ := exists_sections_isGeneralPositionGerm_of_isCompact
    (prod_cube_isTame hX) (admitsBumpFunctions_prod_cube hbump) hg hK hK0
  refine ⟨k, s, hs, ?_⟩
  intro _ _ q
  exact hW _ (hKW ⟨q, rfl⟩) (hz q)

/-- **2021 Lemma 6.6.4 on `[0, 1]ⁿ` with the section of Proposition 6.6.3 (3)**: for a family
`Φ : [0, 1]ⁿ → dom φ_c` in the domain of one strong bundle chart of the atlas, there are an
sc⁺-section `S` over `[0, 1]ⁿ × X` with `(f̃ + S)(q, Φ(q)) = 0` for all `q`
(`proposition_6_6_3_three_cube`) and `s₁, …, s_k` putting `F` in general position at every
`(0, (q, Φ(q)))` (`lemma_6_6_4_cube`): the hypothesis on `S` of `lemma_6_6_4_cube` is
satisfiable. -/
theorem lemma_6_6_4_cube_family (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts)
    {Φ : (Fin n → unitInterval) → X} (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ)
    (hΦc : ∀ q, Φ q ∈ c.φ.source) :
    ∃ (S : (Fin n → unitInterval) × X →
        pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
      (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S),
      (∀ q, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, Φ q)) ∧
      ∃ (k : ℕ) (s : Fin k → (Fin n → unitInterval) × X →
          pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
        (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection
          (s i)),
        ∀ [ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X))]
          [ParacompactSpace (pullbackSpace (pullbackProj P
            (Prod.snd : (Fin n → unitInterval) × X → X))
            (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))],
          ∀ q, ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
              (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
                ((cubePolyfold n).prod PX))).IsGeneralPositionGerm
              (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
                ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1)
              (0, (q, Φ q)) := by
  obtain ⟨-, S, -, -, -, hS, -, hz⟩ :=
    proposition_6_6_3_three_cube hbump hf.isScSmooth hc hΦ hΦc
  exact ⟨S, hS, hz, lemma_6_6_4_cube hX hbump hf hΦ hS hz⟩

variable {k : ℕ} [ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))]
  (hf : B.IsScFredholmSectionTame f) {Φ : (Fin n → unitInterval) → X}
  {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
  (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
  {s : Fin k → (Fin n → unitInterval) × X →
    pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
  (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection (s i))

include hS hs in
/-- **2021 Lemma 6.6.5, p. 265, the first sentence, on `[0, 1]ⁿ`, in Mathlib's language**
(preprint Lemma 6.30): in the setting of `lemma_6_6_4_cube` (`F` in general position at the
points `(0, (q, Φ(q)))`), for every `q ∈ [0, 1]ⁿ` the point `(0, (q, Φ(q)))` lies in
`S = F⁻¹(0)`, and near it `S` is a smooth manifold with boundary and corners
(`theorem_3_1_26_isManifold` applied to `F` over `ℝᵏ × ([0, 1]ⁿ × X)`). -/
theorem lemma_6_6_5_isManifold_cube
    (hz : ∀ q, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, Φ q))
    (hP : ∀ q, ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((cubePolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q)))
    (q : Fin n → unitInterval) :
    IsZeroAt (pullbackProj (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
        Prod.snd)
      (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
        ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1)
      ((0 : Fin k → ℝ), (q, Φ q)) ∧
    ∃ U : Set ((Fin k → ℝ) × ((Fin n → unitInterval) × X)), IsOpen U ∧
      ((0 : Fin k → ℝ), (q, Φ q)) ∈ U ∧
      ∃ (d : ℕ) (hsub : ((rnPolyfold k).prod ((cubePolyfold n).prod PX)).IsSubMPolyfold
          {y ∈ U | IsZeroAt (pullbackProj (pullbackProj P
            (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd)
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) y}),
        letI := ((rnPolyfold k).prod ((cubePolyfold n).prod PX)).paracompactSpace_subtype
          {y ∈ U | IsZeroAt (pullbackProj (pullbackProj P
            (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd)
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) y}
        ∃ h : (MPolyfold.subPolyfold hsub).HasCornerStructureOfDim d,
          letI := (MPolyfold.subPolyfold hsub).cornerChartedSpace h
          IsManifold (modelWithCornersEuclideanQuadrant d) ∞
            {y ∈ U | IsZeroAt (pullbackProj (pullbackProj P
              (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd)
              (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
                ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) y} := by
  have hFt := theorem_3_1_21_tame_cube hf hS hs
  have h0 := isZeroAt_stab_cube ((isSection_pullbackLift _).sectionAdd hS.1)
    (fun i => (hs i).1) (k := k) (hz q)
  exact ⟨h0, theorem_3_1_26_isManifold (isScFredholmSectionTame2021_iff.2 hFt) h0
    (isGoodPositionGermTame2021_iff.2 ((hP q).isGoodPositionGermTame hFt h0))⟩

include hS hs in
/-- **2021 Lemma 6.6.5 on `[0, 1]ⁿ`, as a submanifold of dimension the index**: for every
`q ∈ [0, 1]ⁿ` there are an open `V ∋ (0, (q, Φ(q)))` and `d` such that every zero of `F` in `V`
is in good position with `F'` onto of index `d`, and `S ∩ V` is a `d`-dimensional smooth
submanifold of `ℝᵏ × ([0, 1]ⁿ × X)` (`theorem_3_6_8_isSubmanifoldOfDim`). -/
theorem lemma_6_6_5_isSubmanifoldOfDim_cube
    (hz : ∀ q, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, Φ q))
    (hP : ∀ q, ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((cubePolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q)))
    (q : Fin n → unitInterval) :
    ∃ (V : Set ((Fin k → ℝ) × ((Fin n → unitInterval) × X))) (d : ℕ), IsOpen V ∧
      ((0 : Fin k → ℝ), (q, Φ q)) ∈ solutionSet
        (pullbackProj (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd)
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) ∩ V ∧
      (∀ y ∈ V, IsZeroAt (pullbackProj (pullbackProj P
          (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd)
          (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
            ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) y →
        ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
          (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
            ((cubePolyfold n).prod PX))).IsGoodPositionGermTame
          (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
            ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) y ∧
        ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
          (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
            ((cubePolyfold n).prod PX))).IsSurjLinOfIndex
          (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
            ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) y d) ∧
      ((rnPolyfold k).prod ((cubePolyfold n).prod PX)).IsSubmanifoldOfDim
        (solutionSet (pullbackProj (pullbackProj P
          (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd)
          (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
            ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) ∩ V) d := by
  have hFt := theorem_3_1_21_tame_cube hf hS hs
  have h0 := isZeroAt_stab_cube ((isSection_pullbackLift _).sectionAdd hS.1)
    (fun i => (hs i).1) (k := k) (hz q)
  obtain ⟨V, d, hVo, hqV, hall, hsub⟩ :=
    theorem_3_6_8_isSubmanifoldOfDim hFt ((hP q).isGoodPositionGermTame hFt h0) h0
  exact ⟨V, d, hVo, ⟨h0, hqV⟩, hall, hsub⟩

end CubeLemmas

end Polyfold
