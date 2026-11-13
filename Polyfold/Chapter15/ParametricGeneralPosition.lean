import Polyfold.Chapter15.BranchChart
import Polyfold.Chapter15.LinearizationFunctor

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.7** (General Position; 2017: Theorem 15.4), pp. 696–698, "Achieving global
transversality".

# Parametrized general position (GP's `HasParametricGeneralPosition`)

## The text, paraphrased

For the family `Λ_t = ⊕_i Λ^{x_i}_{t_i}` the parametrized problem near every `(0, x)`, `x ∈ S_f`,
is in general position by (15.1); by the compactness (15.2) only `x` near `S_f` matter for small
`t`; the implicit function theorem and Sard's theorem (on the intersections of faces) give a
null set of parameters off which `(f, Λ_t)` is in general position.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `isScPlusSectionOn_of_paramSec`: the branches `s_{ij}` of a linear family are sc⁺ on `O`.
* `isGeneralPositionGerm_branchParam`: (15.1) for one branch at `x ∈ S_f` makes the parametrized
  branch `(t, y) ↦ (f − Σ_j t_j s_j)|O` in general position at `(0, x)` in Part I's sense
  (Definition 5.3.9 on `ℝ^ℓ × O`).
* `isReducedOntoAtLevel_of_mor`, `isInGeneralPositionAt_of_mor`: general position at one point
  (Definition 15.3.5) is carried along morphisms (Theorem 15.1.1 (functoriality) and the
  transported chart).
* `exists_local_paramGP`: the local step: near a zero `x₀` of `f` with (15.1), there are an open
  `V ∋ x₀`, `δ > 0` and a null set `CV` with `(f, Λ_t)` in general position at every point of
  `V ∩ supp(Λ_t ∘ f)` for `‖t‖ < δ`, `t ∉ CV`.
* `exists_pos_auxLe_subset`: the compactness (15.2): every saturated open `V ⊇ S_f` contains
  `{x ∈ U | N(f(x)) ≤ ε}` for some `ε > 0`.
* **`hasParametricGeneralPosition`**: GP's `HasParametricGeneralPosition A f N U` under the
  hypotheses of Theorem 15.3.7 (tame `X`, `f` an sc-Fredholm section functor with tame germ data,
  `|S_f|` compact, `(N, U)` controlling compactness).
* `theorem_15_3_7_hyp_local`, `theorem_15_3_7_of_local`: Theorem 15.3.7 from a good system and
  `HasLocalGPFamilies` only; `theorem_15_3_7_statement_epSEP_zero_of_local`: the remaining
  hypothesis is satisfiable.

## Reading

* Sard's theorem "on the intersections of faces" is Part I's Theorem 4.3.1 in local form with the
  Sard step of Part I's proof of Theorem 5.3.10
  (`exists_null_isGeneralPositionGerm_paramSlice_near`), applied on `ℝ^ℓ × O` for every branch;
  `X` tame is the hypothesis of the theorem.
* The parametrized branch is read as `(f − 0)|O + Σ_j t_j (−s_{ij})|O`, Part I's `paramSection`
  for the sc-Fredholm section `(f − 0)|O` and the sc⁺-sections `(−s_{ij})|O`; its slice at `t` is
  the branch `(f − Σ_j t_j s_{ij})|O` of `Λ_t`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### The branches of a linear family -/

/-- **The branches `s_{ij}` of a linear family are sc⁺ on `O`**: `s_{ij} = Σ_k δ_{jk} s_{ik}` is
the branch of `Λ_{e_j}`. -/
theorem isScPlusSectionOn_of_paramSec {ℓ k : ℕ} {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0} {O : Set A.Obj}
    {s : Fin k → Fin ℓ → A.Obj → A.W} {σ : Fin k → ℚ≥0} (hs : ∀ i j, IsSection A.P (s i j))
    (hrep : ∀ t, IsLocalRepOn A (Λ t) O (fun i => paramSec (s i) t) σ) (i : Fin k)
    (j : Fin ℓ) : IsScPlusSectionOn A (s i j) O := by
  classical
  refine ((hrep (Pi.single j 1)).2.1 i).congr fun y _ => ?_
  change paramSec (s i) (Pi.single j 1) y = s i j y
  rw [paramSec_apply (hs i), Finset.sum_eq_single j
    (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp), Pi.single_eq_same,
    one_smul]

/-! ### (15.1) gives Part I's general position of the parametrized branch -/

section Branch

variable {O : Set A.Obj} (hO : IsOpen O) [Nonempty O] [ParacompactSpace O]
  [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))] {ℓ : ℕ}
  [ParacompactSpace ((Fin ℓ → ℝ) × O)]
  [ParacompactSpace (pullbackSpace (pullbackProj A.P (Subtype.val : O → A.Obj))
    (Prod.snd : (Fin ℓ → ℝ) × O → O))]

set_option maxHeartbeats 1600000 in
-- the chart reading of (15.1) and Part I's Theorem 5.3.10 step (i)–(ii)
include hO in
/-- **(15.1) for one branch makes the parametrized branch in general position at `(0, x)`**
(proof of Theorem 15.3.7, p. 696, read with Part I's proof of Theorem 5.3.10): at a zero `x` of
`f` in `O`, if `(v, τ) ↦ L v + Σ_j τ_j s_j(x)` maps `T^R_xX × ℝ^ℓ` onto `W_x` for every
operator `L` of `T(f, Λ₀)(x)` and every chart presentation, then
`F(t, y) = (f − 0)|O + Σ_j t_j (−s_j)|O` on `ℝ^ℓ × O` is in general position at `(0, x)`
(Definition 5.3.9). -/
theorem isGeneralPositionGerm_branchParam {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsScPlusSectionOn A (s j) O)
    (hsec : ∀ j, IsSection A.P (s j)) {x : A.X.PObj.Level 1}
    (hxO : A.X.PObj.levelVal 1 x ∈ O)
    (hx0 : f (A.X.PObj.levelVal 1 x) = fiberZero A.P (A.X.PObj.levelVal 1 x))
    (hon : ∀ L ∈ (linearization f (zeroMultisection A) x).support, ∀ (φ : MChart A.Obj)
      (hφ : A.X.PObj.IsChart φ) (hx : A.X.PObj.levelVal 1 x ∈ φ.source) (m : ℕ)
      (V : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin m → ℝ)).prod V)),
      φ.model.C = T 0 ⁻¹' quadrant m V 0 →
        ∀ w : A.P ⁻¹' {A.X.PObj.levelVal 1 x}, ∃ v ∈ reducedTangentFiber hφ hx T,
          ∃ τ : Fin ℓ → ℝ, L v + ∑ j, τ j •
            (⟨s j (A.X.PObj.levelVal 1 x), hsec j _⟩ : A.P ⁻¹' {A.X.PObj.levelVal 1 x}) = w) :
    ((A.B.restrictOpen hO).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold ℓ) (A.X.PObj.restrictOpen hO))).IsGeneralPositionGerm
      (paramSection (subRestrict (O := O) f (fiberZero A.P) hft.isScSmooth.1)
        (isScFredholmSectionTame_subRestrict hO hft
          (isScPlusSectionOn_fiberZero hO)).isScSmooth.1
        (fun j => negRestrict (O := O) (s j))
        fun j => (isScPlusSection_negRestrict hO (hs j)).1)
      (0, ⟨A.X.PObj.levelVal 1 x, hxO⟩) := by
  classical
  set y := A.X.PObj.levelVal 1 x with hy
  have hs0 : IsScPlusSectionOn A (fiberZero A.P) O := isScPlusSectionOn_fiberZero hO
  have hys : y ∈ A.X.PObj.smoothSet := mem_smoothSet_of_eq hft hO hs0 hxO hx0
  obtain ⟨-, c₀, hc₀, hxc₀, hφ0, -⟩ := hft.germTame y hys
  set c := c₀.restrictInter hO with hcdef
  have hc : A.B.IsTameChart c := hc₀.restrictInter hO
  have hsub : c.φ.source ⊆ O := c₀.restrictInter_source_subset hO
  have hxc : y ∈ c.φ.source := ⟨hxc₀, hxO⟩
  have hφ0c : c.φ y = 0 := hφ0
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  let d : LocalLinData A (zeroMultisection A) x :=
    ⟨O, hO, 1, fun _ => fiberZero A.P, fun _ => 1, isLocalRepOn_zeroMultisection hO, c, hc.1,
      hsub, hxc⟩
  have hL : toIntr c hxc (subDeriv c f (fiberZero A.P) (levelLift c.φ 1 y)) ∈
      (linearization f (zeroMultisection A) x).support := by
    rw [linearization_eq hf d]
    exact (mem_support_linSumIntr_iff hf.1.1.1 (fun _ => one_pos)
      (fun _ z _ => isSection_fiberZero (P := A.P) z) hsub hxc _).2 ⟨0, hx0.symm, rfl⟩
  have hon' := hon _ hL c.φ c.isChart hxc n Wq T hT
  set q₀ := subRestrict (O := O) f (fiberZero A.P) hft.isScSmooth.1 ⟨y, hxO⟩
  have hGP := isParamGP_restrictTo_of_onto hO hft hs hsec hc.1 hsub hxc hφ0c hx0 T hon' q₀
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs0
  have hy0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f (fiberZero A.P) hft.isScSmooth.1) ⟨y, hxO⟩ := by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hft.isScSmooth.1 hs0.1 hxO).2 hx0
  have hc'T : (A.B.restrictOpen hO).IsTameChart (c.restrictTo A.B.continuous hO hsub q₀) :=
    ⟨restrictOpen_isChart_restrictTo hO hc.1 hsub q₀, hc.2⟩
  exact isGeneralPositionGerm_paramSection_of_isParamGP hgO
    (fun j => isScPlusSection_negRestrict hO (hs j)) hy0 hc'T hxc hφ0c T hT hGP

end Branch

/-! ### General position at a point is carried along morphisms -/

/-- `μ(φ, ·) : W_x → W_y` is onto (inverse `μ(φ⁻¹, ·)`). -/
private theorem muLin_surjective_GB (φ : A.Mor) {x y : A.Obj} (hx : A.X.src φ = x)
    (hy : A.X.tgt φ = y) : Surjective (muLin φ hx hy) := by
  intro w
  have hw : A.P w = y := w.2
  have h1 : A.P (w : A.W) = A.X.src (A.X.inv φ) := by rw [hw, A.X.src_inv, hy]
  have h2 : A.P (A.E.μ ⟨(A.X.inv φ, (w : A.W)), h1⟩) = x := by
    rw [A.E.P_μ, A.X.tgt_inv, hx]
  refine ⟨⟨A.E.μ ⟨(A.X.inv φ, (w : A.W)), h1⟩, h2⟩, Subtype.ext ?_⟩
  rw [muLin_apply]
  exact A.E.μ_μ_inv φ w h1 _

/-- `Tφ(T^R_xX) ⊆ T^R_yX`, read in a chart `c` at `x` and its transport along `φ` at `y`. -/
private theorem tangentMorCLE_mem_reduced_GB {φ : A.Mor}
    (hφ : φ ∈ A.X.PMor.levelSet 1) {x y : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    {c : StrongBundleChart A.X.PObj A.P} (hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet)
    (hx' : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hy' : A.X.PObj.levelVal 1 y ∈ ((A.E.morIso φ).transportChart c hsub).φ.source)
    {m : ℕ} {V : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod V))
    {u : A.X.PObj.tangentFiber x} (hu : u ∈ reducedTangentFiber c.isChart hx' T) :
    A.X.tangentMorCLE hφ hx hy u ∈
      reducedTangentFiber ((A.E.morIso φ).transportChart c hsub).isChart hy' T := by
  simp only [reducedTangentFiber, Submodule.mem_comap] at hu ⊢
  rw [fiberCoord_eq_coe] at hu ⊢
  rw [chartVec_transport hφ hx hy hsub hx' hy' u]
  have e : ((A.E.morIso φ).transportChart c hsub).φ (A.X.PObj.levelVal 1 y) =
      c.φ (A.X.PObj.levelVal 1 x) := by
    rw [LocalIso.transportChart_φ_apply, hy, EpStrongBundle.morIso_ϕ_tgt, hx]
  rw [e]
  exact hu

/-- **General position at a point (Definition 15.3.5) is carried along morphisms**: for an
sc-Fredholm section functor `f`, an sc⁺-multisection `Λ` and a morphism `φ : x → y` of
level-`1` points, the reduced linearizations at `y` are onto if those at `x` are (Theorem 15.1.1:
`T(f,Λ)(y) = μ(φ, ·) ∘ T(f,Λ)(x) ∘ (Tφ)⁻¹`, and `Tφ(T^R_xX) = T^R_yX`). -/
theorem isReducedOntoAtLevel_of_mor {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (φ : A.Mor) {x y : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    (H : IsReducedOntoAtLevel f Λ x) : IsReducedOntoAtLevel f Λ y := by
  classical
  intro L' hL' ψ hψ hyψ m' V' T' hT'
  set hφ := mem_levelSet_one_of_src hx
  rw [theorem_15_1_1_functor hf hΛ φ hx hy, grfPush] at hL'
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hL')
  obtain ⟨d⟩ := nonempty_localLinData hΛ x
  set Lφ := A.E.morIso φ
  have hso : IsOpen (d.c.φ.source ∩ (A.X.sheetAt φ).srcSet) :=
    d.c.φ.isOpen_source.inter Lφ.isOpen_U'
  set c := d.c.restrict inter_subset_left hso
  have hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet := fun z hz => hz.2
  have hx' : A.X.PObj.levelVal 1 x ∈ c.φ.source :=
    ⟨d.mem, by rw [hx]; exact A.X.src_mem_sheetAt φ⟩
  have hy' : A.X.PObj.levelVal 1 y ∈ (Lφ.transportChart c hsub).φ.source := by
    refine ⟨by rw [hy]; exact A.X.tgt_mem_sheetAt φ, ?_⟩
    change Lφ.ϕ (A.X.PObj.levelVal 1 y) ∈ c.φ.source
    rw [hy, EpStrongBundle.morIso_ϕ_tgt, ← hx]; exact hx'
  obtain ⟨R₀, -⟩ := c.φ.model.isScRetract
  obtain ⟨m₀, V₀, T₀, hT₀⟩ := R₀.relOpen.isPartialQuadrant
  have hsurj := H L hL c.φ c.isChart hx' m₀ V₀ T₀ hT₀
  intro w
  obtain ⟨w₀, rfl⟩ := muLin_surjective_GB φ hx.symm hy.symm w
  obtain ⟨⟨u, hu⟩, hτ⟩ := hsurj w₀
  have e := reducedTangentFiber_eq hψ hyψ T' (Lφ.transportChart c hsub).isChart hy' T₀ hT' hT₀
  refine ⟨⟨A.X.tangentMorCLE hφ hx hy u, ?_⟩, ?_⟩
  · rw [e]
    exact tangentMorCLE_mem_reduced_GB hφ hx hy hsub hx' hy' T₀ hu
  · rw [LinearMap.domRestrict_apply, conjOp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [← hτ]
    rfl

/-- **General position at a point is invariant under morphisms** (Definition 15.3.5 at one
point, for the source and target of a morphism). -/
theorem isInGeneralPositionAt_of_mor {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (φ : A.Mor)
    (H : IsInGeneralPositionAt f Λ (A.X.src φ)) : IsInGeneralPositionAt f Λ (A.X.tgt φ) := by
  obtain ⟨hx1, hred⟩ := H
  set x := A.X.PObj.levelMk 1 (A.X.src φ) hx1
  have hx : A.X.PObj.levelVal 1 x = A.X.src φ := A.X.PObj.levelVal_levelMk 1 _ hx1
  have hy1 : A.X.tgt φ ∈ A.X.PObj.levelSet 1 :=
    (A.X.mem_levelSet_tgt_iff φ 1).2 ((A.X.mem_levelSet_src_iff φ 1).1 hx1)
  refine ⟨hy1, isReducedOntoAtLevel_of_mor hf hΛ φ hx
    (A.X.PObj.levelVal_levelMk 1 _ hy1) hred⟩

/-! ### The local step near a zero -/

set_option maxHeartbeats 1600000 in
-- Part I's local step for each branch, assembled over the branches
/-- **The local step of "Achieving global transversality"** (proof of Theorem 15.3.7, p. 697):
let `X` be tame, `f` an sc-Fredholm section functor with tame germ data, `t ↦ Λ_t` a family of
sc⁺-multisections with (15.1) at the zero `x₀` of `f`.  There are an open `V ∋ x₀`, `δ > 0` and
a Lebesgue null set `CV ⊆ ℝ^ℓ` such that `(f, Λ_t)` is in general position at every point of
`V ∩ supp(Λ_t ∘ f)` (Definition 15.3.5) for `‖t‖ < δ`, `t ∉ CV`.  *Proof*: for every branch,
`isGeneralPositionGerm_branchParam` and Part I's local step
(`exists_null_isGeneralPositionGerm_paramSlice_near`) on `ℝ^ℓ × O`; the slices are the branches
`(f − Σ_j t_j s_{ij})|O` of `Λ_t` (`paramSlice_branch_eq`), and general position of the branches
through `f(y)` is general position of `(f, Λ_t)` at `y`
(`isReducedOntoAtLevel_of_isGeneralPositionGerm`). -/
theorem exists_local_paramGP (hX : A.X.IsTame) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f) {ℓ : ℕ}
    {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0} (hΛ : ∀ t, IsScPlusMultisection A (Λ t))
    {x₀ : A.X.PObj.Level 1} (hx₀ : A.X.PObj.levelVal 1 x₀ ∈ solutionSet A.P f)
    (hon : IsParamOntoAt f Λ x₀) :
    ∃ V : Set A.Obj, IsOpen V ∧ A.X.PObj.levelVal 1 x₀ ∈ V ∧ ∃ δ > (0 : ℝ),
      ∃ CV : Set (Fin ℓ → ℝ), volume CV = 0 ∧ ∀ t : Fin ℓ → ℝ, ‖t‖ < δ → t ∉ CV →
        ∀ y ∈ V, 0 < Λ t (f y) → IsInGeneralPositionAt f (Λ t) y := by
  classical
  obtain ⟨O, k, s, σ, hs, hO, hx₀O, hrep, hon⟩ := hon
  set y₀ := A.X.PObj.levelVal 1 x₀ with hy₀
  have : Nonempty O := ⟨⟨y₀, hx₀O⟩⟩
  have := A.X.PObj.paracompactSpace_subtype O
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
    (A.X.PObj.restrictOpen hO) A.B
  have := MPolyfold.paracompactSpace_prod (rnPolyfold ℓ) (A.X.PObj.restrictOpen hO)
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin ℓ → ℝ) × O → O))
    ((rnPolyfold ℓ).prod (A.X.PObj.restrictOpen hO)) (A.B.restrictOpen hO)
  have hXO : (A.X.PObj.restrictOpen hO).IsTame := MPolyfold.isTame_restrictOpen _ hO hX
  have hs' : ∀ i j, IsScPlusSectionOn A (s i j) O := isScPlusSectionOn_of_paramSec hs hrep
  have hs0 : IsScPlusSectionOn A (fiberZero A.P) O := isScPlusSectionOn_fiberZero hO
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs0
  set p₀ : O := ⟨y₀, hx₀O⟩
  have hy0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f (fiberZero A.P) hft.isScSmooth.1) p₀ := by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hft.isScSmooth.1 hs0.1 hx₀O).2 hx₀
  -- Part I's local step for every branch
  have hbr : ∀ i, ∃ W : Set ((Fin ℓ → ℝ) × O), IsOpen W ∧ ((0 : Fin ℓ → ℝ), p₀) ∈ W ∧
      ∃ CV : Set (Fin ℓ → ℝ), volume CV = 0 ∧ ∀ t (p : O), (t, p) ∈ W →
        f p = paramSec (s i) t p → t ∉ CV →
        (A.B.restrictOpen hO).IsGeneralPositionGerm
          (subRestrict (O := O) f (paramSec (s i) t) hft.isScSmooth.1) p := by
    intro i
    have htp : ∀ j, (A.B.restrictOpen hO).IsScPlusSection (negRestrict (O := O) (s i j)) :=
      fun j => isScPlusSection_negRestrict hO (hs' i j)
    have hz₀ : IsZeroAt (pullbackProj (pullbackProj A.P (Subtype.val : O → A.Obj)) Prod.snd)
        (paramSection (subRestrict (O := O) f (fiberZero A.P) hft.isScSmooth.1)
          hgO.isScSmooth.1 (fun j => negRestrict (O := O) (s i j)) fun j => (htp j).1)
        ((0 : Fin ℓ → ℝ), p₀) := by
      rw [isZeroAt_paramSection_iff]
      change IsZeroAt _ (paramSlice _ _ _ _ 0) p₀
      rw [paramSlice_zero]
      exact hy0
    have hgp := isGeneralPositionGerm_branchParam hO hf hft (hs' i) (hs i) hx₀O hx₀
      fun L hL φ hφ hx m V T hT w => hon L hL φ hφ hx m V T hT i w
    obtain ⟨W, hWo, hW0, CV, hCV, hW⟩ :=
      StrongBundle.exists_null_isGeneralPositionGerm_paramSlice_near hXO hgO htp hz₀ hgp
    refine ⟨W, hWo, hW0, CV, hCV, fun t p htp' hfp htCV => ?_⟩
    have hsl := paramSlice_branch_eq (O := O) hft.isScSmooth.1 (hs i) t
    have hz : IsZeroAt (pullbackProj (pullbackProj A.P (Subtype.val : O → A.Obj)) Prod.snd)
        (paramSection (subRestrict (O := O) f (fiberZero A.P) hft.isScSmooth.1)
          hgO.isScSmooth.1 (fun j => negRestrict (O := O) (s i j)) fun j => (htp j).1)
        (t, p) := by
      rw [isZeroAt_paramSection_iff]
      change IsZeroAt _ (paramSlice _ _ _ _ t) p
      rw [hsl]
      unfold subRestrict
      rw [isZeroAt_restrictSection_iff]
      exact (isZeroAt_subSec_iff hft.isScSmooth.1 ((hrep t).2.1 i).1 p.2).2 hfp
    have h := hW (t, p) htp' hz htCV
    change (A.B.restrictOpen hO).IsGeneralPositionGerm (paramSlice _ _ _ _ t) p at h
    rwa [hsl] at h
  choose W hWo hW0 CV hCV hW using hbr
  -- a product neighbourhood inside every `W i`
  have hnhds : ∀ i, W i ∈ 𝓝 ((0 : Fin ℓ → ℝ), p₀) := fun i => (hWo i).mem_nhds (hW0 i)
  have hprod : ∀ i, ∃ u ∈ 𝓝 (0 : Fin ℓ → ℝ), ∃ v ∈ 𝓝 p₀, u ×ˢ v ⊆ W i :=
    fun i => mem_nhds_prod_iff.1 (hnhds i)
  choose u hu v hv huv using hprod
  have hu' : (⋂ i, u i) ∈ 𝓝 (0 : Fin ℓ → ℝ) := iInter_mem.2 hu
  have hv' : (⋂ i, v i) ∈ 𝓝 p₀ := iInter_mem.2 hv
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hu'
  obtain ⟨v', hv'sub, hv'o, hp₀v'⟩ := mem_nhds_iff.1 hv'
  refine ⟨Subtype.val '' v', hO.isOpenMap_subtype_val v' hv'o, ⟨p₀, hp₀v', rfl⟩, δ, hδ,
    ⋃ i, CV i, measure_iUnion_null hCV, fun t ht htCV => ?_⟩
  rintro _ ⟨p, hpv', rfl⟩ hpos
  have htu : ∀ i, t ∈ u i := fun i => mem_iInter.1 (hball (mem_ball_zero_iff.2 ht)) i
  have hpv : ∀ i, p ∈ v i := fun i => mem_iInter.1 (hv'sub hpv') i
  have hy1 := mem_levelSet_one_of_pos hf (hΛ t) hpos
  set yl := A.X.PObj.levelMk 1 (p : A.Obj) hy1
  have hyl : A.X.PObj.levelVal 1 yl = p := A.X.PObj.levelVal_levelMk 1 _ hy1
  refine ⟨hy1, ?_⟩
  -- a chart at `p` with domain in `O`
  obtain ⟨c₀, hc₀, hpc₀⟩ := StrongBundle.exists_chart_mem A.B (A.X.PObj.levelVal 1 yl)
  have hso : IsOpen (c₀.φ.source ∩ O) := c₀.φ.isOpen_source.inter hO
  set c := c₀.restrict inter_subset_left hso
  have hc : A.B.IsChart c :=
    (StrongBundle.isChart_of_mem A.B hc₀).restrict inter_subset_left hso
  have hsub : c.φ.source ⊆ O := inter_subset_right
  have hyc : A.X.PObj.levelVal 1 yl ∈ c.φ.source := ⟨hpc₀, by rw [hyl]; exact p.2⟩
  refine isReducedOntoAtLevel_of_isGeneralPositionGerm hf hft hO (hrep t) hc hsub hyc
    fun i hi => ?_
  have e : (⟨A.X.PObj.levelVal 1 yl, hsub hyc⟩ : O) = p := Subtype.ext hyl
  rw [e]
  refine hW i t p (huv i ⟨htu i, hpv i⟩) ?_ fun h' => htCV (mem_iUnion.2 ⟨i, h'⟩)
  rw [← hyl]
  exact hi.symm

/-! ### The compactness (15.2): small `N(f)` forces nearness to `S_f` -/

/-- On the support of `Λ ∘ f`, `N(f(x)) ≤ N(Λ)(x)`, and `x ∈ U` once `S_f ⊆ U` and
`dom-supp(Λ) ⊆ U` (as in `supp_comp_subset_controlled`, for any bound `r`). -/
theorem auxLe_of_pos {f : A.Obj → A.W} (hf : IsSection A.P f) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hSU : solutionSet A.P f ⊆ U) {r : ℝ} (hN : ∀ x, pointwiseNorm N Λ x ≤ r)
    (hdom : domSupp Λ ⊆ U) {x : A.Obj} (hx : 0 < Λ (f x)) :
    x ∈ U ∧ A.B.AuxLe N (f x) r := by
  have hmem : f x ∈ suppAt Λ x := ⟨hf x, hx⟩
  refine ⟨?_, hΛ.suppAt_subset_oneSet x hmem, ?_⟩
  · by_cases h0 : f x = fiberZero A.P x
    · exact hSU h0
    · exact hdom (subset_closure ⟨f x, hf x, h0, hx⟩)
  · have hle := (hΛ.isGreatest_pointwiseNorm N x).2 ⟨f x, hmem, rfl⟩
    rw [normW_of_mem N (hΛ.suppAt_subset_oneSet x hmem)] at hle
    exact hle.trans (hN x)

/-- **The compactness (15.2) in the proof of Theorem 15.3.7** (p. 696): if `(N, U)` controls the
compactness of `f` (Definition 15.3.1), every saturated open `V ⊇ S_f` contains
`{x ∈ U | N(f(x)) ≤ ε}` for some `ε > 0`.  *Proof*: otherwise points `x_n ∈ U ∖ V` with
`N(f(x_n)) ≤ 1/(n+1)` have orbits in the compact `cl|{x ∈ U | N(f(x)) ≤ 1}|`; at a cluster
point `|z|` the openness of `π` (Proposition 7.1.8), the saturation of `V` and the invariance of
`N ∘ f` give `y_k → z` outside `V` with `N(f(y_k)) → 0`, so `f(z) = 0` (Definition 5.1.1 (3) of
the auxiliary norm), `z ∈ S_f ⊆ V`, which is absurd. -/
theorem exists_pos_auxLe_subset {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hfc : Continuous f) {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U)
    {V : Set A.Obj} (hVo : IsOpen V) (hVs : A.X.IsSaturated V)
    (hSV : solutionSet A.P f ⊆ V) :
    ∃ ε > (0 : ℝ), ∀ x ∈ U, A.B.AuxLe N (f x) ε → x ∈ V := by
  classical
  have hN : A.E.IsAuxNorm N := hcc.1
  obtain ⟨⟨hfs, hfun⟩, -⟩ := hf
  have hsec : IsSection A.P f := hfs.1
  by_contra hne
  push Not at hne
  have hx : ∀ n : ℕ, ∃ x ∈ U, A.B.AuxLe N (f x) (1 / ((n : ℝ) + 1)) ∧ x ∉ V :=
    fun n => hne _ (by positivity)
  choose x hxU hxN hxV using hx
  -- a cluster point of the orbits
  set K := closure (A.X.π '' {x ∈ U | A.B.AuxLe N (f x) 1})
  have hK : IsCompact K := hcc.2.2.2.2
  have hxK : ∀ n, A.X.π (x n) ∈ K := fun n => subset_closure ⟨x n, ⟨hxU n, by
    obtain ⟨h1, hle⟩ := hxN n
    exact ⟨h1, hle.trans (by
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_left (Nat.cast_nonneg n))⟩⟩, rfl⟩
  obtain ⟨q, -, hq⟩ := hK (f := map (fun n => A.X.π (x n)) atTop)
    (le_principal_iff.2 (mem_map.2 (Eventually.of_forall hxK)))
  obtain ⟨z, rfl⟩ := A.X.surjective_π q
  have := A.X.PObj.metrizableSpace
  obtain ⟨Bz, hBz⟩ := (𝓝 z).exists_antitone_basis
  -- points `y_k ∈ int Bz k` in the orbit of some `x n`, `n ≥ k`
  have hy : ∀ k : ℕ, ∃ n ≥ k, ∃ y ∈ interior (Bz k), A.X.π y = A.X.π (x n) := by
    intro k
    have hO : A.X.π '' interior (Bz k) ∈ 𝓝 (A.X.π z) :=
      (A.X.proposition_7_1_8 _ isOpen_interior).mem_nhds
        ⟨z, mem_interior_iff_mem_nhds.2 (hBz.mem k), rfl⟩
    have h2 : ∃ᶠ n in atTop, A.X.π (x n) ∈ A.X.π '' interior (Bz k) :=
      Filter.frequently_map.1 (hq.frequently (Filter.eventually_of_mem hO fun _ h => h))
    obtain ⟨n, hnk, ⟨y, hyB, hyx⟩⟩ := Filter.frequently_atTop.1 h2 k
    exact ⟨n, hnk, y, hyB, hyx⟩
  choose n hnk y hyB hyx using hy
  have hyz : Tendsto y atTop (𝓝 z) :=
    hBz.tendsto fun k => interior_subset (hyB k)
  have hyV : ∀ k, y k ∉ V := by
    intro k hk
    apply hxV (n k)
    rw [← hVs]
    exact ⟨y k, hk, hyx k⟩
  -- `N(f(y_k)) ≤ 1/(k+1)`
  have hyN : ∀ k, A.B.AuxLe N (f (y k)) (1 / ((k : ℝ) + 1)) := by
    intro k
    obtain ⟨φ, hφs, hφt⟩ := A.X.π_eq_π_iff.1 (hyx k).symm
    have h := EpStrongBundle.auxLe_tgt_of_auxLe_src (E := A.E) hsec hfun hN φ
      (by rw [hφs]; exact hxN (n k))
    rw [hφt] at h
    obtain ⟨h1, hle⟩ := h
    refine ⟨h1, hle.trans ?_⟩
    gcongr
    exact_mod_cast hnk k
  choose h1 hle using hyN
  set w : ℕ → A.B.One := fun k => A.B.oneMk (f (y k)) (h1 k)
  have hwP : Tendsto (fun k => A.P (A.B.oneVal (w k))) atTop (𝓝 z) := by
    refine hyz.congr fun k => ?_
    change y k = A.P (A.B.oneVal (A.B.oneMk (f (y k)) (h1 k)))
    rw [A.B.oneVal_oneMk, hsec]
  have hwN : Tendsto (fun k => N (w k)) atTop (𝓝 0) :=
    squeeze_zero (fun k => hN.isAuxNorm.nonneg _) (fun k => hle k)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hw0 := hN.isAuxNorm.tendsto_zeroOne w z hwP hwN
  have hf0 : Tendsto (fun k => f (y k)) atTop (𝓝 (fiberZero A.P z)) := by
    have := (A.B.continuous_oneVal.tendsto _).comp hw0
    rw [A.B.oneVal_zeroOne] at this
    exact this.congr fun k => A.B.oneVal_oneMk _ _
  have hfz : f z = fiberZero A.P z :=
    tendsto_nhds_unique ((hfc.tendsto z).comp hyz) hf0
  exact hyV _ ((hyz.eventually (hVo.mem_nhds (hSV hfz))).exists.choose_spec)

/-! ### Achieving global transversality -/

variable {f : A.Obj → A.W} {N : A.B.One → ℝ} {U : Set A.Obj}

set_option maxHeartbeats 1600000 in
-- the assembly over a finite cover of `|S_f|`
/-- **"Achieving global transversality" in the proof of Theorem 15.3.7** (pp. 696–698): GP's
`HasParametricGeneralPosition` holds under the hypotheses of the theorem (tame `X`, an
sc-Fredholm section functor `f` with tame germ data, compact `|S_f|`, `(N, U)` controlling
compactness).  *Proof*: the local step (`exists_local_paramGP`) at every `z ∈ S_f`; finitely many
of the open sets `|V_z|` cover the compact `|S_f|`; by (15.2) (`exists_pos_auxLe_subset`) and
`N(Λ_t) ≤ |t|₁` the support of `Λ_t ∘ f` lies in the saturation of `⋃ V_z` for small `t`; general
position at a point is carried along morphisms (`isInGeneralPositionAt_of_mor`). -/
theorem hasParametricGeneralPosition (hX : A.X.IsTame) (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f)
    (hcc : ControlsCompactness A f N U) : HasParametricGeneralPosition A f N U := by
  classical
  intro ℓ Λ hΛ _ hNorm hdom hon
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  have hsec : IsSection A.P f := hft.isScSmooth.1
  obtain ⟨hfs, hfun⟩ := hf.1
  -- the local step at every zero
  have hloc : ∀ z : solutionSet A.P f, ∃ V : Set A.Obj, IsOpen V ∧ (z : A.Obj) ∈ V ∧
      ∃ δ > (0 : ℝ), ∃ CV : Set (Fin ℓ → ℝ), volume CV = 0 ∧ ∀ t : Fin ℓ → ℝ, ‖t‖ < δ →
        t ∉ CV → ∀ y ∈ V, 0 < Λ t (f y) → IsInGeneralPositionAt f (Λ t) y := by
    rintro ⟨z, hz⟩
    have hzs : z ∈ A.X.PObj.smoothSet := mem_smoothSet_of_eq hft isOpen_univ
      (isScPlusSectionOn_fiberZero isOpen_univ) (mem_univ z) hz
    have hz1 := smoothSet_subset_levelSet 1 hzs
    have e := A.X.PObj.levelVal_levelMk 1 z hz1
    have h := exists_local_paramGP hX hf hft hΛ (x₀ := A.X.PObj.levelMk 1 z hz1)
      (by rw [e]; exact hz) (hon _ (by rw [e]; exact hz))
    rw [e] at h
    exact h
  choose V hVo hzV δ hδ CV hCV hgp using hloc
  -- a finite cover of `|S_f|`
  have hcov : A.X.π '' solutionSet A.P f ⊆ ⋃ z : solutionSet A.P f, A.X.π '' V z := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_iUnion.2 ⟨⟨z, hz⟩, z, hzV _, rfl⟩
  obtain ⟨T, hT⟩ := hS.elim_finite_subcover (fun z => A.X.π '' V z)
    (fun z => A.X.proposition_7_1_8 _ (hVo z)) hcov
  set Vs := A.X.saturation (⋃ z ∈ T, V z) with hVs
  have hVso : IsOpen Vs :=
    (A.X.proposition_7_1_8 _ (isOpen_biUnion fun z _ => hVo z)).preimage A.X.continuous_π
  have hVss : A.X.IsSaturated Vs := by
    change A.X.π ⁻¹' (A.X.π '' (A.X.π ⁻¹' (A.X.π '' _))) = A.X.π ⁻¹' (A.X.π '' _)
    rw [image_preimage_eq _ A.X.surjective_π]
  have hSV : solutionSet A.P f ⊆ Vs := by
    intro z hz
    obtain ⟨i, hiT, y, hy, hyz⟩ := mem_iUnion₂.1 (hT ⟨z, hz, rfl⟩)
    exact ⟨y, mem_iUnion₂.2 ⟨i, hiT, hy⟩, hyz⟩
  obtain ⟨ε₀, hε₀, hε₀V⟩ := exists_pos_auxLe_subset hf hfc hcc hVso hVss hSV
  -- small parameters
  have hsum : Tendsto (fun t : Fin ℓ → ℝ => ∑ j, |t j|) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : Fin ℓ → ℝ => ∑ j, |t j|) :=
      continuous_finsetSum _ fun j _ => (continuous_apply j).abs
    simpa using hc.tendsto 0
  have hnorm : Tendsto (fun t : Fin ℓ → ℝ => ‖t‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_norm (E := Fin ℓ → ℝ)).tendsto 0
  have hev : ∀ᶠ t in 𝓝 (0 : Fin ℓ → ℝ), (∀ i ∈ T, ‖t‖ < δ i) ∧ ∑ j, |t j| < ε₀ :=
    ((eventually_all_finset T).2 fun i _ => hnorm.eventually (gt_mem_nhds (hδ i))).and
      (hsum.eventually (gt_mem_nhds hε₀))
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, ?_⟩
  have hCVT : volume (⋃ i ∈ T, CV i) = 0 :=
    (measure_biUnion_null_iff T.countable_toSet).2 fun i _ => hCV i
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hCVT] with t htCV htε
  obtain ⟨htδ, htsum⟩ := hεP (by rwa [dist_zero_right])
  rw [isInGeneralPosition_iff_forall_at hf (hΛ t)]
  intro x hpos
  obtain ⟨hxU, h1, hle⟩ := auxLe_of_pos hsec (hΛ t) hcc.2.2.2.1 (hNorm t) (hdom t) hpos
  obtain ⟨y, hy, hyx⟩ := hε₀V x hxU ⟨h1, hle.trans htsum.le⟩
  obtain ⟨i, hiT, hyi⟩ := mem_iUnion₂.1 hy
  obtain ⟨φ, hφs, hφt⟩ := A.X.π_eq_π_iff.1 hyx
  have hΛφ : Λ t (f (A.X.tgt φ)) = Λ t (f (A.X.src φ)) := by
    rw [hfun φ]
    exact (hΛ t).1 _
  have hposy : 0 < Λ t (f y) := by rw [← hφs, ← hΛφ, hφt]; exact hpos
  have hgy := hgp i t (htδ i hiT) (fun h => htCV (mem_iUnion₂.2 ⟨i, hiT, h⟩)) y hyi hposy
  have h := isInGeneralPositionAt_of_mor hf (hΛ t) φ (by rw [hφs]; exact hgy)
  rwa [hφt] at h

/-! ### Theorem 15.3.7 with one analytic step left -/

/-- **Theorem 15.3.7 (2017: Theorem 15.4), pp. 693–698, with `HasParametricGeneralPosition`
proved**: from a good system, the hypotheses of the theorem and GP's first analytic step
(`HasLocalGPFamilies`, the local constructions) there is a structurable `Λ` with the conclusions
(1)–(4). -/
theorem theorem_15_3_7_hyp_local (h𝒰 : Nonempty A.X.GoodSystem) (hX : A.X.IsTame)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) (hcc : ControlsCompactness A f N U) {h : A.Obj → ℝ}
    (hh : ∀ x, 0 < h x ∧ h x ≤ 1) (hloc : HasLocalGPFamilies A f N U h) :
    ∃ Λ : A.W → ℚ≥0, IsStructurable A Λ ∧ (∀ x, pointwiseNorm N Λ x < h x) ∧
      domSupp Λ ⊆ U ∧ IsTransversal f Λ ∧ IsInGeneralPosition A f Λ :=
  theorem_15_3_7_hyp h𝒰 hf hS hcc hh hloc (hasParametricGeneralPosition hX hf hft hS hcc)

/-- **Theorem 15.3.7 as stated (`theorem_15_3_7_statement`)** from a good system and GP's first
analytic step `HasLocalGPFamilies` alone (the second, `HasParametricGeneralPosition`, is
`hasParametricGeneralPosition`). -/
theorem theorem_15_3_7_of_local (h𝒰 : Nonempty A.X.GoodSystem)
    (H : A.X.IsTame → A.X.AdmitsBumpFunctionsPointwise →
      ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
        A.E.HasCompactSolutionSetEp f →
        ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
        ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) →
          (∀ x, 0 < h x ∧ h x ≤ 1) → HasLocalGPFamilies A f N U h) :
    theorem_15_3_7_statement A :=
  theorem_15_3_7_of_hyp h𝒰 fun htame hbump f hf hft hS N U hcc h hhc hhφ hh =>
    ⟨H htame hbump f hf hft hS N U hcc h hhc hhφ hh,
      hasParametricGeneralPosition htame hf hft hS hcc⟩

/-- **The remaining hypothesis of `theorem_15_3_7_of_local` is satisfiable**: on `ℝⁿ × ℝ⁰ → ℝⁿ`
it holds (GP's `hasLocalGPFamilies_epSEP_zero`), which gives the statement there through the
reduction. -/
theorem theorem_15_3_7_statement_epSEP_zero_of_local (n : ℕ) :
    theorem_15_3_7_statement (StrongBundleEquivalenceExamples.epSEP n 0) :=
  theorem_15_3_7_of_local (nonempty_goodSystem_epSEP_zero n)
    fun _ _ f _ _ _ _ U hcc h _ _ _ => hasLocalGPFamilies_epSEP_zero n f hcc.1.isAuxNorm U h

end SBLocalization

end Polyfold
