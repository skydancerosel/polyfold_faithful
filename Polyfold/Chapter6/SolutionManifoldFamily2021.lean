import Polyfold.Chapter6.Lemma629
import Polyfold.Chapter6.ParamKernel
import Polyfold.Chapter9.MathlibSolutionSets

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **Lemma 6.6.5**
(p. 265; preprint Lemma 6.30, p. 222) as a statement about manifolds.  Gap G.62, rows V6.34,
V6.42.

# The solution set of the stabilized section near the family of zeros

## The text, paraphrased

(Lemma 6.6.5) The solution set `S` of `F(t, y, λ) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)` near
`(t, φ(t), 0)` is a smooth manifold with boundary with corners containing `{(t, φ(t), 0)}`; by (P)
the projection `π : S → [0, 1]` is a submersion; its fibres `S_t` are manifolds with boundary with
corners, `T_{(φ(t), 0)} S_t = ker F_t'(φ(t), 0) = L_t`, and `L` is a smooth vector bundle.

## What is formalized

The setting is that of `lemma_6_6_4` and `exists_isStabKernels`: `t ∈ [0, 1]` is `q ∈ ℝⁿ`
(decision D2), `F(λ, (q, y)) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)` is a section of the pull-back
bundle over `ℝᵏ × (ℝⁿ × X)` (`paramSection`), and `F` is in general position at the points
`(0, (q, Φ(q)))`, `q` near `[0, 1]ⁿ` (the conclusion of `lemma_6_6_4`).

* `lemma_6_6_5_isManifold` (**the first sentence, in Mathlib's language**): for `q` near
  `[0, 1]ⁿ`, `(0, (q, Φ(q)))` is a zero of `F` and has an open neighbourhood `U` such that
  `S(F, U)` is a smooth manifold with boundary and corners
  (`IsManifold (modelWithCornersEuclideanQuadrant d) ∞`) for the charted space of its induced
  corner structure (`theorem_3_1_26_isManifold` applied to `F`).
* `lemma_6_6_5_isSubmanifoldOfDim`: the same as a `d`-dimensional smooth submanifold of
  `ℝᵏ × (ℝⁿ × X)` (`IsSubmanifoldOfDim`, `theorem_3_6_8_isSubmanifoldOfDim`), every zero nearby
  being in good position with `F'` onto of index `d`.
* `exists_mem_linKer_sliceProj_eq` and **`lemma_6_6_5_submersion`** (**`π` is a submersion at the
  points of the family**): in the product chart `χ = (λ ↦ λ) × ((q ↦ q) × φ)` at
  `(0, (q, z))`, `z` over `φ(Φ(q))`, the tangent space of `S` is `ker F'` (Theorem 3.6.8,
  `exists_tangentSpace_eq_linKer`) and `dπ = sliceProj : (λ, (σ, v)) ↦ σ` maps it onto `ℝⁿ`: the
  derivative of the curve of zeros `q' ↦ (0, (q', Φ(q')))` lies in `ker F'`
  (`fderiv_mem_linKer`) and has `ℝⁿ`-component the identity.

## What is not formalized

* That `π` is a submersion at the points of `S` off the family, the fibres `S_t` as manifolds
  with boundary with corners (they need property (P) for the slices `F_t`, gap G.63), and the
  smooth structure of `L`.  `L_t = ker F'(0, (q, Φ(q))) ∩ {σ = 0}`
  (`linKer_inf_ker_sliceProj_eq_map`) is a continuous family of subspaces (`exists_isStabKernels`),
  which is what the continuation of orientations uses.
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle

section Stab

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {n k : ℕ}
  [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

/-- **`dπ` maps `ker F'` onto `ℝⁿ` at the points of a family of zeros** (the submersion of Lemma
6.6.5 at `(t, φ(t), 0)`): for `F(λ, (q', y)) = G(q', y) + Σ λᵢ sᵢ(q', y)` and an sc-smooth
`Φ : ℝⁿ → X` with `G(q', Φ(q')) = 0` near `q`, in the product chart `χ` at `(0, (q, z))` every
`σ ∈ ℝⁿ` is the `ℝⁿ`-component of a vector of `ker Lin_F`: the derivative of the curve
`q' ↦ (0, (q', Φ(q')))` in the direction `σ` (`fderiv_mem_linKer`). -/
theorem exists_mem_linKer_sliceProj_eq
    {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection G)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    {x : X} (p : ChartPoint B x) (q : Fin n → ℝ) {Φ : (Fin n → ℝ) → X}
    (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ) (hΦq : Φ q = x)
    (hΦ0 : ∀ᶠ q' in 𝓝 q, IsZeroAt (pullbackProj P Prod.snd) G (q', Φ q'))
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X)) (σ : Fin n → ℝ) :
    ∃ w ∈ ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).toChart
        q₁).linKer (paramSection G hG.1 s fun i => (hs i).1)
        ((0, (q, p.z)) : ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
          0).toChart q₁).φ.model.E 1),
      sliceProj k n (p.c.φ.model.E 0) w = σ := by
  subst hΦq
  set cZ := (PullbackChartData.ofProd p.c 0).toChart q₀ with hcZ
  set χ := (PullbackChartData.ofProd cZ 0).toChart q₁ with hχ
  have hcZc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsChart cZ :=
    (PullbackChartData.ofProd p.c 0).isChart_toChart B _ p.isChart q₀
  have hχc : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((rnPolyfold n).prod PX))).IsChart χ :=
    (PullbackChartData.ofProd cZ 0).isChart_toChart _ _ hcZc q₁
  have hsrc : ((0 : Fin k → ℝ), (q, Φ q)) ∈ χ.φ.source := ⟨mem_univ _, mem_univ _, p.mem_source⟩
  have hz' : χ.φ.model.E.toBase 1 ((0, (q, p.z)) : χ.φ.model.E 1) =
      χ.φ ((0 : Fin k → ℝ), (q, Φ q)) := by
    change ((rnSc k).prod ((rnSc n).prod p.c.φ.model.E)).toBase 1 (0, (q, p.z)) =
      ((0 : Fin k → ℝ) - 0, ((q : Fin n → ℝ) - 0, p.c.φ (Φ q)))
    rw [ScBanach.prod_toBase, ScBanach.prod_toBase, ScBanach.const_toBase, ScBanach.const_toBase,
      p.toBase_z, sub_zero, sub_zero]
  have hF0 : ∀ᶠ q' in 𝓝 q, IsZeroAt
      (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
      (paramSection G hG.1 s fun i => (hs i).1) ((0 : Fin k → ℝ), (q', Φ q')) :=
    hΦ0.mono fun q' h => by
      rw [isZeroAt_paramSection_iff]
      change IsZeroAt _ (paramSlice G hG.1 s (fun i => (hs i).1) 0) (q', Φ q')
      rw [paramSlice_zero]
      exact h
  have hFsm : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((rnPolyfold n).prod PX))).IsScSmoothSection
        (paramSection G hG.1 s fun i => (hs i).1) := by
    rw [paramSection_eq_sectionAdd]
    exact (hG.pullback _).sectionAdd (StrongBundle.isScPlusSection_paramComb hs)
  have hΓ : (rnPolyfold n).IsScSmoothMap ((rnPolyfold k).prod ((rnPolyfold n).prod PX))
      (fun q' => ((0 : Fin k → ℝ), (q', Φ q'))) :=
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_rn_rn_of_contDiff contDiff_const)
      (MPolyfold.IsScSmoothOn.prodMk MPolyfold.isScSmoothMap_id hΦ)
  obtain ⟨hd, hmem⟩ := fderiv_mem_linKer hFsm hχc hΓ hsrc hF0 _ hz' σ
  refine ⟨_, hmem, ?_⟩
  have hd' : HasFDerivAt (fun q' : Fin n → ℝ => (((0 : Fin k → ℝ) - 0, (q' - 0, p.c.φ (Φ q'))) :
      (Fin k → ℝ) × ((Fin n → ℝ) × p.c.φ.model.E 0)))
      (fderiv ℝ (fun q' => χ.φ ((0 : Fin k → ℝ), (q', Φ q'))) q :
        (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) × ((Fin n → ℝ) × p.c.φ.model.E 0)) q :=
    hd.hasFDerivAt
  have := hd'.snd.fst.unique ((hasFDerivAt_id q).sub_const 0)
  exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L σ) this

variable (hf : B.IsScFredholmSectionTame f) {Φ : (Fin n → ℝ) → X}
  {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
  (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
  {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
  (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))

include hf hS hs in
/-- The stabilized section `F` is sc-Fredholm with tame germ data (Theorems 3.1.18 and 3.1.21),
and `(0, (q, Φ(q)))` is a zero of `F` when `(f̃ + S)(q, Φ(q)) = 0`. -/
theorem isScFredholmSectionTame_stab :
    ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((rnPolyfold n).prod PX))).IsScFredholmSectionTame
      (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
        ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) ∧
    ∀ q : Fin n → ℝ, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q) →
      IsZeroAt (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1)
        ((0 : Fin k → ℝ), (q, Φ q)) := by
  refine ⟨theorem_3_1_21_tame (theorem_3_1_18_tame hf.param hS) hs, fun q h => ?_⟩
  rw [isZeroAt_paramSection_iff]
  change IsZeroAt _ (paramSlice _ _ s (fun i => (hs i).1) 0) (q, Φ q)
  rw [paramSlice_zero]
  exact h

/-- **2021 Lemma 6.6.5, p. 265, the first sentence, in Mathlib's language** (preprint Lemma 6.30):
in the setting of `lemma_6_6_4` (`F` in general position at the points `(0, (q, Φ(q)))`), for
every `q` near `[0, 1]ⁿ` the point `(0, (q, Φ(q)))` lies in `S = F⁻¹(0)`, and near it `S` is a
smooth manifold with boundary and corners (`theorem_3_1_26_isManifold` applied to `F`). -/
theorem lemma_6_6_5_isManifold
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q))
    (hP : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q))) :
    ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      IsZeroAt (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1)
        ((0 : Fin k → ℝ), (q, Φ q)) ∧
      ∃ U : Set ((Fin k → ℝ) × ((Fin n → ℝ) × X)), IsOpen U ∧ ((0 : Fin k → ℝ), (q, Φ q)) ∈ U ∧
        ∃ (d : ℕ) (hsub : ((rnPolyfold k).prod ((rnPolyfold n).prod PX)).IsSubMPolyfold
            {y ∈ U | IsZeroAt (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
              Prod.snd) (paramSection (sectionAdd (pullbackProj P Prod.snd)
                (paramLift f hf.isScSmooth.1) S) ((isSection_pullbackLift _).sectionAdd hS.1) s
                  fun i => (hs i).1) y}),
          letI := ((rnPolyfold k).prod ((rnPolyfold n).prod PX)).paracompactSpace_subtype
            {y ∈ U | IsZeroAt (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
              Prod.snd) (paramSection (sectionAdd (pullbackProj P Prod.snd)
                (paramLift f hf.isScSmooth.1) S) ((isSection_pullbackLift _).sectionAdd hS.1) s
                  fun i => (hs i).1) y}
          ∃ h : (MPolyfold.subPolyfold hsub).HasCornerStructureOfDim d,
            letI := (MPolyfold.subPolyfold hsub).cornerChartedSpace h
            IsManifold (modelWithCornersEuclideanQuadrant d) ∞
              {y ∈ U | IsZeroAt (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
                Prod.snd) (paramSection (sectionAdd (pullbackProj P Prod.snd)
                  (paramLift f hf.isScSmooth.1) S) ((isSection_pullbackLift _).sectionAdd hS.1) s
                    fun i => (hs i).1) y} := by
  obtain ⟨hFt, hzero⟩ := isScFredholmSectionTame_stab (Φ := Φ) hf hS hs
  filter_upwards [hz, hP] with q hq hgp
  have h0 := hzero q hq
  exact ⟨h0, theorem_3_1_26_isManifold (isScFredholmSectionTame2021_iff.2 hFt) h0
    (isGoodPositionGermTame2021_iff.2 (hgp.isGoodPositionGermTame hFt h0))⟩

/-- **2021 Lemma 6.6.5, the first sentence, as a submanifold of dimension the index**: for `q`
near `[0, 1]ⁿ` there are an open `V ∋ (0, (q, Φ(q)))` and `d` such that every zero of `F` in `V`
is in good position with `F'` onto of index `d`, and `S ∩ V` is a `d`-dimensional smooth
submanifold of `ℝᵏ × (ℝⁿ × X)` (`theorem_3_6_8_isSubmanifoldOfDim`). -/
theorem lemma_6_6_5_isSubmanifoldOfDim
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q))
    (hP : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q))) :
    ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      ∃ (V : Set ((Fin k → ℝ) × ((Fin n → ℝ) × X))) (d : ℕ), IsOpen V ∧
        ((0 : Fin k → ℝ), (q, Φ q)) ∈ solutionSet
          (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
          (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
            ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) ∩ V ∧
        (∀ y ∈ V, IsZeroAt (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
            Prod.snd) (paramSection (sectionAdd (pullbackProj P Prod.snd)
              (paramLift f hf.isScSmooth.1) S) ((isSection_pullbackLift _).sectionAdd hS.1) s
                fun i => (hs i).1) y →
          ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
            (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
              ((rnPolyfold n).prod PX))).IsGoodPositionGermTame
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) y ∧
          ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
            (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
              ((rnPolyfold n).prod PX))).IsSurjLinOfIndex
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) y d) ∧
        ((rnPolyfold k).prod ((rnPolyfold n).prod PX)).IsSubmanifoldOfDim
          (solutionSet (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) ∩ V) d := by
  obtain ⟨hFt, hzero⟩ := isScFredholmSectionTame_stab (Φ := Φ) hf hS hs
  filter_upwards [hz, hP] with q hq hgp
  have h0 := hzero q hq
  obtain ⟨V, d, hVo, hqV, hall, hsub⟩ :=
    theorem_3_6_8_isSubmanifoldOfDim hFt (hgp.isGoodPositionGermTame hFt h0) h0
  exact ⟨V, d, hVo, ⟨h0, hqV⟩, hall, hsub⟩

/-- **2021 Lemma 6.6.5, p. 265: `π : S → [0, 1]` is a submersion at the points of the family**
(preprint Lemma 6.30): for `q` near `[0, 1]ⁿ` there is an open `V ∋ (0, (q, Φ(q)))` such that in
the product chart `χ` over any chart point `(c, z)` of `Φ(q)`, the tangent space at `(0, (q, z))`
of the solution set `S ∩ V` (read in `χ` through any open `G` on which it is a retract) is
`ker F'(0, (q, z))`, and `dπ : (λ, (σ, v)) ↦ σ` maps it onto `ℝⁿ`. -/
theorem lemma_6_6_5_submersion (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q))
    (hP : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q))) :
    ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      ∃ V : Set ((Fin k → ℝ) × ((Fin n → ℝ) × X)), IsOpen V ∧ ((0 : Fin k → ℝ), (q, Φ q)) ∈ V ∧
        ∀ (p : ChartPoint B (Φ q)) (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
          (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
            (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))
          (G : Set ((Fin k → ℝ) × ((Fin n → ℝ) × X))), IsOpen G →
          G ⊆ ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
            0).toChart q₁).φ.source → ((0 : Fin k → ℝ), (q, Φ q)) ∈ G →
          IsScRetract ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
              0).toChart q₁).φ.model.E
            ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
              0).toChart q₁).φ.model.C
            (((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
              0).toChart q₁).φ '' (G ∩ (solutionSet
                (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
                (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
                  ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) ∩ V))) →
          tangentSpace ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
              0).toChart q₁).φ.model.E
            ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
              0).toChart q₁).φ.model.C
            (((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
              0).toChart q₁).φ '' (G ∩ (solutionSet
                (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
                (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
                  ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) ∩ V)))
            ((0, (q, p.z)) : ((PullbackChartData.ofProd
              ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).toChart q₁).φ.model.E 1) =
            ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
              0).toChart q₁).linKer
              (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
                ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1)
              ((0, (q, p.z)) : ((PullbackChartData.ofProd
                ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).toChart q₁).φ.model.E 1) ∧
          ∀ σ : Fin n → ℝ, ∃ w ∈ ((PullbackChartData.ofProd
              ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).toChart q₁).linKer
              (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
                ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1)
              ((0, (q, p.z)) : ((PullbackChartData.ofProd
                ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).toChart q₁).φ.model.E 1),
            sliceProj k n (p.c.φ.model.E 0) w = σ := by
  obtain ⟨hFt, hzero⟩ := isScFredholmSectionTame_stab (Φ := Φ) hf hS hs
  have hzq : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), ∀ᶠ q' in 𝓝 q,
      IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q', Φ q') :=
    hz.eventually_nhdsSet
  filter_upwards [hz, hP, hzq] with q hq hgp hq'
  have h0 := hzero q hq
  obtain ⟨V, hVo, hqV, -, hT⟩ := exists_tangentSpace_eq_linKer hFt
    (hgp.isGoodPositionGermTame hFt h0) h0
  refine ⟨V, hVo, hqV, fun p q₀ q₁ G hGo hGc hqG hR => ⟨?_, fun σ => ?_⟩⟩
  · have hχc : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((rnPolyfold n).prod PX))).IsChart
        ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).toChart q₁) :=
      (PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).isChart_toChart
        _ _ ((PullbackChartData.ofProd p.c 0).isChart_toChart B _ p.isChart q₀) q₁
    refine hT _ hqV h0 _ hχc ⟨mem_univ _, mem_univ _, p.mem_source⟩ G hGo hGc hqG hR _ ?_
    change ((rnSc k).prod ((rnSc n).prod p.c.φ.model.E)).toBase 1 (0, (q, p.z)) =
      ((0 : Fin k → ℝ) - 0, ((q : Fin n → ℝ) - 0, p.c.φ (Φ q)))
    rw [ScBanach.prod_toBase, ScBanach.prod_toBase, ScBanach.const_toBase, ScBanach.const_toBase,
      p.toBase_z, sub_zero, sub_zero]
  · exact exists_mem_linKer_sliceProj_eq (theorem_3_1_18_tame hf.param hS).isScSmooth hs p q hΦ
      rfl hq' q₀ q₁ σ

end Stab

end Polyfold
