import Polyfold.Chapter15.P3W4GP_GeneralPosition
import Polyfold.Chapter15.P3W4SM_GeneralPositionLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.7** (General Position; 2017: Theorem 15.4), pp. 696–698, "Achieving global
transversality": the local step, one branch at a time, on an M-polyfold.

# The parametrized problem near a zero, on an M-polyfold

## The text, paraphrased

Near `(0, x)`, `x ∈ S_f`, the parametrized problem `f(y) = Σ_j t_j s_{ij}(y)` has, by (15.1) and
the implicit function theorem, a smooth finite-dimensional solution set; Sard's theorem for its
projection to `ℝ^ℓ` (on the intersections of faces) gives a null set of parameters off which the
slices are in general position.

## What is formalized

* `StrongBundle.exists_null_isGeneralPositionGerm_paramSlice_near` (Part I, local form): for a
  parametrized section `F(λ, y) = g(y) + Σ λᵢ tᵢ(y)` over a tame M-polyfold, in general position
  (Definition 5.3.9) at a zero `z₀`, there are an open `W ∋ z₀` and a Lebesgue null set `CV`
  such that the slice `g + Σ λᵢ tᵢ` is in general position at `y` for every zero `(λ, y) ∈ W`
  with `λ ∉ CV`.  It is the local core of Part I's `theorem_5_3_10_of_family` (Theorem 4.3.1 in
  the form `exists_local_family`, the Sard step `exists_null_isLinSurjAt_paramSlice_near`, Lemma
  5.26 and the chart independence of Definition 5.3.9), with no compactness assumption.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter MeasureTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### Part I: the local parametrized general position step -/

section PartILocal

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin m → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
  {B : StrongBundle PX P} {g : X → Y}

open StrongRetr MPolyfold

/-- **General position at `a` passes to the piece `A ∩ V` of the data**: the data of Definition
4.2.1 carried by `IsGeneralPositionAt A a` (Definition 4.2.10) make `A ∩ V` a smooth submanifold
(Definition 4.2.1) in general position at `a`, without asking `A` itself to be one. -/
theorem MPolyfold.IsGeneralPositionAt.exists_inter {A : Set X} {a : X}
    (h : PX.IsGeneralPositionAt A a) :
    ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ PX.IsSmoothSubmanifold (A ∩ V) ∧
      PX.IsGeneralPositionAt (A ∩ V) a := by
  obtain ⟨haA, d, φ, n, Wq, T, z, ha, hφ, haφ, hT, hz, hgp⟩ := h
  have himg : d.s '' d.V = (A ∩ d.V) ∩ d.V := by rw [d.image, inter_assoc, inter_self]
  let d' : PX.SubmanifoldData (A ∩ d.V) :=
    ⟨d.V, d.s, d.isOpen, d.isScPlusRetractionOn, himg⟩
  refine ⟨d.V, d.isOpen, ha, fun b hb => ⟨d.V, d.isOpen, hb.2, d.s, d.isScPlusRetractionOn,
    himg⟩, ⟨haA, ha⟩, d', φ, n, Wq, T, z, ha, hφ, haφ, hT, hz, ?_⟩
  have e : d'.toSubData.shrink φ ∩ (A ∩ d.V) = d.toSubData.shrink φ ∩ A := by
    ext b
    constructor
    · rintro ⟨hb, hbA, -⟩
      exact ⟨hb, hbA⟩
    · rintro ⟨hb, hbA⟩
      exact ⟨hb, hbA, d.toSubData.shrink_subset_V φ hb⟩
  unfold SubmanifoldData.IsGeneralPositionChart
  rw [e]
  exact hgp

set_option maxHeartbeats 1600000 in
-- the local assembly of Part I's Theorem 5.3.10 machinery
/-- **The local step of Part I's Theorem 5.3.10, without compactness**: let `X` be tame, `g` an
sc-Fredholm section with tame germ data, `tᵢ` sc⁺-sections, and `z₀` a zero of the parametrized
section `F(λ, y) = g(y) + Σ λᵢ tᵢ(y)` at which `F` is in general position (Definition 5.3.9).
There are an open `W ∋ z₀` and a Lebesgue null set `CV ⊆ ℝᵐ` such that at every zero
`(λ, y) ∈ W` of `F` with `λ ∉ CV` the slice `g + Σ λᵢ tᵢ` is in general position at `y`.
*Proof*: general position is open along `S̃ = F⁻¹(0)` (`exists_isOpen_isGeneralPositionGerm`),
so `A = S̃ ∩ W₀` is a smooth submanifold in general position; Theorem 4.3.1 in its local form
(`exists_local_family`) and the Sard step (`exists_null_isLinSurjAt_paramSlice_near`) give null
sets off which the fibres of `A` are submanifolds in general position and the slices are
transversal; Lemma 5.26 (`isGoodPositionGermTame_of_isGeneralPositionAt`) and the chart
independence of Definition 5.3.9 (`exists_isGeneralPositionGerm_iff`) conclude. -/
theorem StrongBundle.exists_null_isGeneralPositionGerm_paramSlice_near (hX : PX.IsTame)
    (hgF : B.IsScFredholmSectionTame g) {t : Fin m → X → Y} (htp : ∀ i, B.IsScPlusSection (t i))
    {z₀ : (Fin m → ℝ) × X}
    (hz₀ : IsZeroAt (pullbackProj P Prod.snd)
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) z₀)
    (hgp : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGeneralPositionGerm
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) z₀) :
    ∃ W : Set ((Fin m → ℝ) × X), IsOpen W ∧ z₀ ∈ W ∧ ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
      ∀ z ∈ W, IsZeroAt (pullbackProj P Prod.snd)
        (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) z → z.1 ∉ CV →
        B.IsGeneralPositionGerm (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) z.1)
          z.2 := by
  classical
  have hgs : IsSection P g := hgF.isScSmooth.1
  set F := paramSection g hgs t fun i => (htp i).1 with hF
  have hFt := theorem_3_1_21_tame hgF htp
  have hXm : ((rnPolyfold m).prod PX).IsTame := prod_rn_isTame hX
  -- general position along `S̃` near `z₀`
  obtain ⟨W₀, hW₀o, hz₀W₀, hA, hW₀⟩ := exists_isOpen_isGeneralPositionGerm hXm hFt hz₀ hgp
  set A := solutionSet (pullbackProj P Prod.snd) F ∩ W₀ with hAdef
  have hgpA : ∀ z ∈ A, ((rnPolyfold m).prod PX).IsGeneralPositionAt A z :=
    fun z hz => (hW₀ z hz.2 hz.1).2.2
  -- Theorem 4.3.1, local form
  obtain ⟨U₁, hU₁o, hz₀U₁, CV₁, hCV₁, hfib⟩ := exists_local_family hX hA hgpA ⟨hz₀, hz₀W₀⟩
  -- the Sard step: transversality of the slices
  obtain ⟨W₂, hW₂o, hz₀W₂, CV₂, hCV₂, htr⟩ :=
    exists_null_isLinSurjAt_paramSlice_near hgF htp hz₀ (hW₀ z₀ hz₀W₀ hz₀).1
  refine ⟨W₀ ∩ U₁ ∩ W₂, (hW₀o.inter hU₁o).inter hW₂o, ⟨⟨hz₀W₀, hz₀U₁⟩, hz₀W₂⟩, CV₁ ∪ CV₂,
    measure_union_null hCV₁ hCV₂, fun z hz hz0 hzCV => ?_⟩
  obtain ⟨⟨hzW₀, hzU₁⟩, hzW₂⟩ := hz
  set lam := z.1 with hlam
  set h := paramSlice g hgs t (fun i => (htp i).1) lam with hh
  have hzA : z ∈ A := ⟨hz0, hzW₀⟩
  have hy0 : IsZeroAt P h z.2 := (isZeroAt_paramSection_iff z).1 hz0
  -- the slice is tame Fredholm
  have hhF : B.IsScFredholmSectionTame h := by
    have h1 := theorem_3_1_18_tame hgF (isScPlusSection_paramSlice
      StrongBundle.isScPlusSection_fiberZero htp lam)
    rw [sectionAdd_paramSlice_fiberZero hgs (fun i => (htp i).1) lam] at h1
    exact h1
  -- transversality
  have htrans : B.IsLinSurjAt h z.2 :=
    htr z hzW₂ hz0 fun h' => hzCV (Or.inr h')
  -- the fibre of `A` through `z`: a submanifold piece `M` in general position at `z.2`
  obtain ⟨-, -, hgpF, -⟩ := hfib z ⟨hzA, hzU₁⟩ fun h' => hzCV (Or.inl h')
  obtain ⟨V, hVo, hyV, hMs, hgpM⟩ := hgpF.exists_inter
  have hMS : fibreSet A lam ∩ V ⊆ solutionSet P h := by
    rintro y ⟨hyA, -⟩
    exact (isZeroAt_paramSection_iff (lam, y)).1 hyA.1
  -- Lemma 5.26: good position of the slice at `z.2`
  have hgood := isGoodPositionGermTame_of_isGeneralPositionAt hhF hy0 htrans hMs hMS hgpM
  obtain ⟨V', hV'o, hyV', -, hA', hiff', -⟩ := exists_isGeneralPositionGerm_iff hhF hgood hy0
  refine (hiff' z.2 hyV' hy0).2 ?_
  -- `M` and `S_h ∩ V'` agree near `z.2`
  set G := V ∩ V' ∩ (fun x => (lam, x)) ⁻¹' W₀ with hG
  have hGo : IsOpen G := (hVo.inter hV'o).inter
    (hW₀o.preimage (continuous_const.prodMk continuous_id))
  have hyG : z.2 ∈ G := ⟨⟨hyV, hyV'⟩, hzW₀⟩
  refine IsGeneralPositionAt.congr_nhds hMs hA' hGo hyG ?_ hgpM
  ext x
  constructor
  · rintro ⟨⟨hxA, -⟩, hxG⟩
    exact ⟨⟨(isZeroAt_paramSection_iff (lam, x)).1 hxA.1, hxG.1.2⟩, hxG⟩
  · rintro ⟨⟨hx0, -⟩, hxG⟩
    exact ⟨⟨⟨(isZeroAt_paramSection_iff (lam, x)).2 hx0, hxG.2⟩, hxG.1.1⟩, hxG⟩

end PartILocal

end Polyfold
