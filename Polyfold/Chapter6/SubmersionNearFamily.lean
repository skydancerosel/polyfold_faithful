import Polyfold.Chapter6.SlicePropertyP
import Polyfold.Chapter6.KernelFamily

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **Lemma 6.6.5**
(p. 265; preprint Lemma 6.30): **`π : S → [0, 1]` is a submersion**, off the family as well.
Gap G.62, rows V6.34, V6.42.

# The projection of the solution set is a submersion near the family

## The text, paraphrased

The solution set `S` of `F = 0` near the points `(t, φ(t), 0)` is a manifold, and by (P) the
projection `π : S → [0, 1]` is a submersion.

## What is formalized

`lemma_6_6_5_submersion` (`SolutionManifoldFamily2021.lean`) proves that `dπ` maps the tangent
space `ker F'` onto `ℝⁿ` at the points `(0, (q, Φ(q)))` of the family.  Here:

* `eventually_surjective_of_frame` (linear algebra): for a continuous frame `e_i(q)` and a
  continuous linear `π : E → ℝᵐ`, if `π(span e(q₀)) = ℝᵐ` then `π(span e(q)) = ℝᵐ` for `q` near
  `q₀` (a determinant that is `1` at `q₀`).
* `exists_nhds_surjective_linKer` (**surjectivity of `π` on the kernels is open along the
  zeros**): for a tame sc-Fredholm section `g`, a zero `x₀` in good position and a chart `c` at
  `x₀`, if a continuous linear `π` maps `ker Lin_g(z₀)` onto `ℝᵐ`, then it maps `ker Lin_g(z)`
  onto `ℝᵐ` at all zeros near `x₀`.  The zeros near `x₀` form a smooth submanifold, the image of
  an sc⁺-retraction `s` (`isSmoothSubmanifold_solutionSet_inter`), so `y ↦ (φ(y) on level 1)` is
  continuous on them (`s` is continuous into `X¹`); the kernels then have a continuous frame
  (`exists_local_frame_linKer`).
* **`lemma_6_6_5_submersion_nhds`**: in the setting of Lemma 6.6.4, for `q` near `[0, 1]ⁿ` and
  every product chart `χ` at `(0, (q, Φ(q)))`, there is a neighbourhood `W` of `(0, (q, Φ(q)))`
  such that at **every** zero `y ∈ W` of `F` the tangent space of `S` is `ker F'(y)`
  (`exists_tangentSpace_eq_linKer`) and `dπ = sliceProj` maps it onto `ℝⁿ`: `π` is a submersion
  on `S ∩ W`.
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle MPolyfold

/-! ### Linear algebra: surjectivity onto `ℝᵐ` is open along a continuous frame -/

/-- **Surjectivity along a continuous frame is open**: if `π` maps the span of `e(q₀)` onto `ℝᵐ`,
it maps the span of `e(q)` onto `ℝᵐ` for `q` near `q₀`.  *Proof*: preimages `a_j` of the standard
basis at `q₀` give a matrix `M(q)` with columns `π(Σᵢ a_j i eᵢ(q))`, continuous at `q₀` with
`M(q₀) = 1`, so `det M(q) ≠ 0` near `q₀`. -/
theorem eventually_surjective_of_frame {Q : Type*} [TopologicalSpace Q] {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] {m d : ℕ} (π : E →L[ℝ] (Fin m → ℝ)) (e : Fin d → Q → E) {q₀ : Q}
    (hec : ∀ i, ContinuousAt (e i) q₀)
    (h0 : ∀ σ, ∃ a : Fin d → ℝ, π (∑ i, a i • e i q₀) = σ) :
    ∀ᶠ q in 𝓝 q₀, ∀ σ, ∃ a : Fin d → ℝ, π (∑ i, a i • e i q) = σ := by
  classical
  choose a ha using fun j : Fin m => h0 (Pi.single j 1)
  set v : Fin m → Q → Fin m → ℝ := fun j q => π (∑ i, a j i • e i q) with hv
  have hvc : ∀ j, ContinuousAt (v j) q₀ := fun j =>
    π.continuous.continuousAt.comp
      (tendsto_finsetSum _ fun i _ => continuousAt_const.smul (hec i))
  set M : Q → Matrix (Fin m) (Fin m) ℝ := fun q => Matrix.of fun r j => v j q r with hM
  have hMc : ContinuousAt (fun q => (M q).det) q₀ := by
    have hM' : ContinuousAt M q₀ := continuousAt_pi.2 fun r => continuousAt_pi.2 fun j =>
      (continuous_apply r).continuousAt.comp (hvc j)
    exact (continuous_id.matrix_det).continuousAt.comp hM'
  have hM0 : M q₀ = 1 := by
    ext r j
    simp only [hM, hv, Matrix.of_apply, ha j, Matrix.one_apply, Pi.single_apply]
  have hdet : ∀ᶠ q in 𝓝 q₀, (M q).det ≠ 0 := by
    have : (M q₀).det ≠ 0 := by rw [hM0, Matrix.det_one]; exact one_ne_zero
    exact hMc.eventually (isOpen_ne.mem_nhds this)
  filter_upwards [hdet] with q hq σ
  set x := Matrix.mulVec (M q)⁻¹ σ with hx
  refine ⟨fun i => ∑ j, x j * a j i, ?_⟩
  have hMx : Matrix.mulVec (M q) x = σ := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hq),
      Matrix.one_mulVec]
  rw [← hMx]
  have : (∑ i, (∑ j, x j * a j i) • e i q) = ∑ j, x j • ∑ i, a j i • e i q := by
    simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  rw [this, map_sum]
  ext r
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    hM, Matrix.of_apply, hv]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-! ### Surjectivity onto `ℝᵐ` on the kernels is open along the zeros -/

section Core

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y}

/-- **A continuous level-`1` lift of the zeros near a zero in good position**: near `x₀`, the
zeros of `g` in the domain of a chart `φ` lift continuously to level `1` (the solution set is the
image of an sc⁺-retraction `s`, continuous into `X¹`, and `φ` is continuous on level `1`). -/
theorem exists_continuousOn_levelLift_solutionSet (hg : B.IsScFredholmSectionTame g) {x₀ : X}
    (hgp : B.IsGoodPositionGermTame g x₀) (hx₀ : IsZeroAt P g x₀) {φ : MChart X}
    (hφ : PX.IsChart φ) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ (∀ y ∈ V, IsZeroAt P g y → B.IsGoodPositionGermTame g y) ∧
      (∀ y ∈ V, IsZeroAt P g y → y ∈ PX.levelSet 1) ∧
      ContinuousOn (levelLift φ 1) (solutionSet P g ∩ V ∩ φ.source) := by
  obtain ⟨V₀, hV₀o, hx₀V₀, hall, -⟩ := exists_tangentSpace_eq_linKer hg hgp hx₀
  have hA := StrongBundle.isSmoothSubmanifold_solutionSet_inter hg.isScSmooth.1 hV₀o hall
  have hx₀A : x₀ ∈ solutionSet P g ∩ V₀ := ⟨hx₀, hx₀V₀⟩
  set D := hA.data hx₀A with hD
  have hs := D.isScPlusRetractionOn
  have hfix : ∀ y ∈ solutionSet P g ∩ V₀ ∩ D.V, D.s y = y := by
    intro y hy
    have : y ∈ D.s '' D.V := by rw [D.image]; exact hy
    obtain ⟨v, hv, rfl⟩ := this
    exact hs.idem v hv
  refine ⟨V₀ ∩ D.V, hV₀o.inter D.isOpen, ⟨hx₀V₀, hA.mem_data_V hx₀A⟩,
    fun y hy hy0 => hall y hy.1 hy0, fun y hy hy0 => ?_, ?_⟩
  · rw [← hfix y ⟨⟨hy0, hy.1⟩, hy.2⟩]; exact hs.mem_levelSet y hy.2
  · have hx₀1 : x₀ ∈ PX.levelSet 1 := by
      rw [← hfix x₀ ⟨hx₀A, hA.mem_data_V hx₀A⟩]
      exact hs.mem_levelSet x₀ (hA.mem_data_V hx₀A)
    set x₁ : PX.Level 1 := ⟨x₀, hx₀1⟩
    have h1 : ContinuousOn (PX.toLevelOne x₁ ∘ D.s) D.V := (hs.isScSmoothOn_one x₁).continuousOn
    have h2 : ContinuousOn (levelChart hφ x₁) (levelChart hφ x₁).source :=
      (levelChart hφ x₁).continuousOn_toFun
    have hmaps : MapsTo (PX.toLevelOne x₁ ∘ D.s) (solutionSet P g ∩ (V₀ ∩ D.V) ∩ φ.source)
        (levelChart hφ x₁).source := by
      intro y hy
      change PX.levelVal 1 (PX.toLevelOne x₁ (D.s y)) ∈ φ.source
      rw [levelVal_toLevelOne x₁ (hs.mem_levelSet y hy.1.2.2),
        hfix y ⟨⟨hy.1.1, hy.1.2.1⟩, hy.1.2.2⟩]
      exact hy.2
    refine ((h2.comp (h1.mono fun y hy => hy.1.2.2) hmaps)).congr fun y hy => ?_
    change levelLift φ 1 y = levelChart hφ x₁ (PX.toLevelOne x₁ (D.s y))
    rw [levelChart_apply, levelVal_toLevelOne x₁ (hs.mem_levelSet y hy.1.2.2),
      hfix y ⟨⟨hy.1.1, hy.1.2.1⟩, hy.1.2.2⟩]

/-- **Surjectivity onto `ℝᵐ` on the kernels of the linearizations is open along the zeros**:
for a tame sc-Fredholm section `g`, a zero `x₀` in good position, a chart `c` at `x₀` and a
continuous linear `π : E₀ → ℝᵐ` mapping `ker Lin_g(z₀)` onto `ℝᵐ`, there is a neighbourhood `W`
of `x₀` such that `π` maps `ker Lin_g(z)` onto `ℝᵐ` at every zero `y ∈ W` (`z` over `φ(y)`).
*Proof*: a continuous level-`1` lift of the zeros (`exists_continuousOn_levelLift_solutionSet`),
a continuous frame of the kernels (`exists_local_frame_linKer`), and
`eventually_surjective_of_frame`. -/
theorem exists_nhds_surjective_linKer (hg : B.IsScFredholmSectionTame g)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {x₀ : X} (hx₀c : x₀ ∈ c.φ.source)
    (hx₀ : IsZeroAt P g x₀) (hgp : B.IsGoodPositionGermTame g x₀) {m : ℕ}
    (π : c.φ.model.E 0 →L[ℝ] (Fin m → ℝ)) {z₀ : c.φ.model.E 1}
    (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀) (hsurj : ∀ σ, ∃ w ∈ c.linKer g z₀, π w = σ) :
    ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ W ⊆ c.φ.source ∧ ∀ y ∈ W, IsZeroAt P g y →
      ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y → ∀ σ, ∃ w ∈ c.linKer g z, π w = σ := by
  classical
  obtain ⟨V, hVo, hx₀V, hall, hlev, hcont⟩ :=
    exists_continuousOn_levelLift_solutionSet hg hgp hx₀ c.isChart
  set T := solutionSet P g ∩ V ∩ c.φ.source with hT
  have hx₀T : x₀ ∈ T := ⟨⟨hx₀, hx₀V⟩, hx₀c⟩
  set z : T → c.φ.model.E 1 := fun y => levelLift c.φ 1 y with hzdef
  have hz : Continuous z := hcont.domRestrict
  have hzy : ∀ y : T, c.φ.model.E.toBase 1 (z y) = c.φ y := fun y =>
    PX.toBase_levelLift c.isChart y.2.2 (hlev y y.2.1.2 y.2.1.1)
  obtain ⟨U, hUo, hx₀U, d, hd, e, hec, he⟩ := exists_local_frame_linKer hg hc
    (Subtype.val : T → X) continuous_subtype_val (fun y => y.2.2) (fun y => y.2.1.1)
    (fun y => hall y y.2.1.2 y.2.1.1) z hz hzy ⟨x₀, hx₀T⟩
  -- at `x₀`: the frame spans the kernel
  have hzx₀ : z ⟨x₀, hx₀T⟩ = z₀ := (c.φ.model.E.toBase_injective 1) ((hzy _).trans hz₀.symm)
  have hspan : Submodule.span ℝ (range fun i => e i ⟨x₀, hx₀T⟩) = c.linKer g z₀ := by
    rw [← hzx₀]
    obtain ⟨hfd, hdim⟩ := hd _ hx₀U
    obtain ⟨hmem, hind⟩ := he _ hx₀U
    refine Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.2 (range_subset_iff.2 hmem)) ?_
    rw [finrank_span_eq_card hind, Fintype.card_fin, hdim]
  have h0 : ∀ σ, ∃ a : Fin d → ℝ, π (∑ i, a i • e i ⟨x₀, hx₀T⟩) = σ := by
    intro σ
    obtain ⟨w, hw, hπw⟩ := hsurj σ
    rw [← hspan] at hw
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
    exact ⟨a, hπw⟩
  have hev := eventually_surjective_of_frame π e
    (fun i => (hec i).continuousAt (hUo.mem_nhds hx₀U)) h0
  obtain ⟨U', hU', hU'o, hx₀U'⟩ := eventually_nhds_iff.1 (hev.and (hUo.mem_nhds hx₀U))
  obtain ⟨O, hOo, hOU'⟩ := isOpen_induced_iff.1 hU'o
  refine ⟨O ∩ V ∩ c.φ.source, (hOo.inter hVo).inter c.φ.isOpen_source,
    ⟨⟨show (⟨x₀, hx₀T⟩ : T) ∈ Subtype.val ⁻¹' O by rw [hOU']; exact hx₀U', hx₀V⟩, hx₀c⟩,
    fun y hy => hy.2,
    fun y hy hy0 z' hz' σ => ?_⟩
  have hyT : y ∈ T := ⟨⟨hy0, hy.1.2⟩, hy.2⟩
  have hyU' : (⟨y, hyT⟩ : T) ∈ U' := by
    rw [← hOU']; exact hy.1.1
  obtain ⟨hsurj', hyU⟩ := hU' _ hyU'
  have hzz : z' = z ⟨y, hyT⟩ :=
    (c.φ.model.E.toBase_injective 1) (hz'.trans (hzy ⟨y, hyT⟩).symm)
  obtain ⟨a, ha⟩ := hsurj' σ
  refine ⟨∑ i, a i • e i ⟨y, hyT⟩, ?_, ha⟩
  rw [hzz]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((he _ hyU).1 i)

end Core

/-! ### `π` is a submersion near the family -/

section Family

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {n k : ℕ}
  [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

/-- **2021 Lemma 6.6.5, p. 265: `π : S → [0, 1]` is a submersion near the family** (preprint
Lemma 6.30).  In the setting of `lemma_6_6_4` (`F = f + S + Σ λᵢ sᵢ` in general position at the
points `(0, (q, Φ(q)))`), for every `q` near `[0, 1]ⁿ` and every product chart
`χ = (λ ↦ λ) × ((q' ↦ q') × φ)` over a chart point of `Φ(q)` there are open sets `V`, `W`
containing `(0, (q, Φ(q)))`, `W` in the domain of `χ`, such that at **every** zero `y` of `F` in
`V ∩ W`, for `z` over `χ(y)`:
* the tangent space at `z` of the solution set `S ∩ V`, read in `χ` through any open `G` on which
  it is a retract, is `ker F'(z)` (`exists_tangentSpace_eq_linKer`), and
* `dπ = sliceProj : (λ, (σ, v)) ↦ σ` maps `ker F'(z)` onto `ℝⁿ`.
So `π` is a submersion on `S ∩ V ∩ W`, a neighbourhood of the family in `S`
(`exists_nhds_surjective_linKer`, from `lemma_6_6_5_submersion`'s computation at the family). -/
theorem lemma_6_6_5_submersion_nhds (hf : B.IsScFredholmSectionTame f) {Φ : (Fin n → ℝ) → X}
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q))
    (hP : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q))) :
    ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      ∀ (p : ChartPoint B (Φ q)) (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
        (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
          (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X)),
      ∃ V W : Set ((Fin k → ℝ) × ((Fin n → ℝ) × X)), IsOpen V ∧ IsOpen W ∧
        ((0 : Fin k → ℝ), (q, Φ q)) ∈ V ∩ W ∧
        W ⊆ ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
            0).toChart q₁).φ.source ∧
        ∀ y ∈ V ∩ W, IsZeroAt (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
            Prod.snd) (paramSection (sectionAdd (pullbackProj P Prod.snd)
              (paramLift f hf.isScSmooth.1) S) ((isSection_pullbackLift _).sectionAdd hS.1) s
                fun i => (hs i).1) y →
          ∀ z : ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
              0).toChart q₁).φ.model.E 1,
            ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
              0).toChart q₁).φ.model.E.toBase 1 z =
              ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
                0).toChart q₁).φ y →
          (∀ G : Set ((Fin k → ℝ) × ((Fin n → ℝ) × X)), IsOpen G →
            G ⊆ ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
              0).toChart q₁).φ.source → y ∈ G →
            IsScRetract ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
                0).toChart q₁).φ.model.E
              ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
                0).toChart q₁).φ.model.C
              (((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
                0).toChart q₁).φ '' (G ∩ (solutionSet
                  (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
                  (paramSection (sectionAdd (pullbackProj P Prod.snd)
                    (paramLift f hf.isScSmooth.1) S)
                    ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) ∩ V))) →
            tangentSpace ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
                0).toChart q₁).φ.model.E
              ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
                0).toChart q₁).φ.model.C
              (((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
                0).toChart q₁).φ '' (G ∩ (solutionSet
                  (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
                  (paramSection (sectionAdd (pullbackProj P Prod.snd)
                    (paramLift f hf.isScSmooth.1) S)
                    ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) ∩ V))) z =
              ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
                0).toChart q₁).linKer
                (paramSection (sectionAdd (pullbackProj P Prod.snd)
                  (paramLift f hf.isScSmooth.1) S)
                  ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) z) ∧
          ∀ σ : Fin n → ℝ, ∃ w ∈ ((PullbackChartData.ofProd
              ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).toChart q₁).linKer
              (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
                ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) z,
            sliceProj k n (p.c.φ.model.E 0) w = σ := by
  obtain ⟨hFt, hzero⟩ := isScFredholmSectionTame_stab (Φ := Φ) hf hS hs
  have hzq : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), ∀ᶠ q' in 𝓝 q,
      IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q', Φ q') :=
    hz.eventually_nhdsSet
  filter_upwards [hz, hP, hzq] with q hq hgp hq'
  intro p q₀ q₁
  have h0 := hzero q hq
  have hgpt := hgp.isGoodPositionGermTame hFt h0
  have hχc : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((rnPolyfold n).prod PX))).IsChart
      ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).toChart q₁) :=
    (PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).isChart_toChart
      _ _ ((PullbackChartData.ofProd p.c 0).isChart_toChart B _ p.isChart q₀) q₁
  have hsrc : ((0 : Fin k → ℝ), (q, Φ q)) ∈
      ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
        0).toChart q₁).φ.source := ⟨mem_univ _, mem_univ _, p.mem_source⟩
  have hz' : ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
        0).toChart q₁).φ.model.E.toBase 1 ((0, (q, p.z)) : ((PullbackChartData.ofProd
          ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).toChart q₁).φ.model.E 1) =
      ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
        0).toChart q₁).φ ((0 : Fin k → ℝ), (q, Φ q)) := by
    change ((rnSc k).prod ((rnSc n).prod p.c.φ.model.E)).toBase 1 (0, (q, p.z)) =
      ((0 : Fin k → ℝ) - 0, ((q : Fin n → ℝ) - 0, p.c.φ (Φ q)))
    rw [ScBanach.prod_toBase, ScBanach.prod_toBase, ScBanach.const_toBase, ScBanach.const_toBase,
      p.toBase_z, sub_zero, sub_zero]
  obtain ⟨W, hWo, hx₀W, hWs, hW⟩ := exists_nhds_surjective_linKer hFt hχc hsrc h0 hgpt
    (sliceProj k n (p.c.φ.model.E 0)) hz' fun σ =>
      exists_mem_linKer_sliceProj_eq (theorem_3_1_18_tame hf.param hS).isScSmooth hs p q hΦ rfl
        hq' q₀ q₁ σ
  obtain ⟨V, hVo, hx₀V, -, hT⟩ := exists_tangentSpace_eq_linKer hFt hgpt h0
  exact ⟨V, W, hVo, hWo, ⟨hx₀V, hx₀W⟩, hWs, fun y hy hy0 z hzy =>
    ⟨fun G hGo hGc hyG hR => hT y hy.1 hy0 _ hχc (hWs hy.2) G hGo hGc hyG hR z hzy,
      hW y hy.2 hy0 z hzy⟩⟩

end Family

end Polyfold
