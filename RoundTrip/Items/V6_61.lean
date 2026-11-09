import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_61

/-! Round trip for V6_61 (Theorem 6.41, its proof, and the paragraph after it; §6.5, pp. 229–230).

A is the conjunction of the 16 theorems among the item's 22 declarations (universes at `0`):
`theorem_6_6_18_hyp`, `theorem_6_6_18_solutionSet` and the lemmas of its proof (good position, `T_yS =
ker f'(y)`, `f'(y) ∈ Lin`, the stabilization by `ℝ⁰`, tangent families, `cont_tangentOr`,
`isLineOrientation_tangentOr*`).

Neither direction is proved.  The glue that does go through is proved below.

* Hypotheses.  From A's hypotheses one gets B's: `IsSectionOrientation → D640` holds
  (`D640_of_isSectionOrientation`, through `exists_path_of_contractible`).  From B's hypotheses
  one does NOT get A's.  (i) `D640 → IsSectionOrientation` needs a basis of sc-smoothly
  contractible neighbourhoods at smooth points (see V6_60), i.e. mathematics.  (ii) B's `f` is
  only `IsScFredholmSection`, while A uses tame germ data at every smooth point
  (`IsScFredholmSectionTame`), the standing hypothesis of Chapter 5.
* Conclusion "compact manifold with boundary with corners": glue.  A's
  `SolutionSetInGeneralPosition` gives B's `IsCompactCornerManifold`
  (`isCompactCornerManifold_of_solutionSetInGeneralPosition`).  So under tame germ data A gives
  this part of B's (1) (`corner_of_A`).
* Conclusion "natural orientation".  A gives path-wise continuity: along every sc-smooth path of
  zeros inside the `V` of an orientable neighbourhood, in its chart, the tangent orientations
  `tangentOrAt (o_y)` form an orientation of the line bundle of the tangent family.  B asks for
  continuous local frames `v₁, …, vₙ` of `ker f'(y)` on `W ∩ S` (some chart, some open `W`) whose
  wedge lies in the ray `tangentOrAt (o_y)`.  Neither gives the other by glue.  In one direction
  one needs: the kernels as a continuous family over the manifold `S` (Lemma 6.30 is along
  paths), local frames, and the zeros near `x₀` joined by sc-smooth paths of zeros in `V`.  In the
  other direction one needs the agreement of the tangent orientations read in two charts, which the
  project does not formalize (`SolutionOrientation.lean`, "Reading").
* B's (2), the non-generic case, is absent from A.  For an sc⁺-perturbation `s` with `f + s`
  proper and generic, `S_{f+s}` is a compact manifold with corners oriented by an orientation `o'`
  of `f + s` induced by `o`.  The project states that this paragraph is not formalized.  It is a
  genuine gap: an orientation of `f + s` must be built from `o`.
* `B ⇒ A` also fails.  B gives none of the auxiliary lemmas, nor the extra conclusions of
  `SolutionSetInGeneralPosition` (transversality, general position of `S`, tameness of `S`,
  `d_S = d_X`).
-/

namespace RoundTrip.V6_61
open Polyfold Set
open scoped ContDiff

/-- The project's statement (the theorems among the item's declarations), universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_6_6_18_solutionSet.{0, 0} ∧
  type_of% @Polyfold.MPolyfold.IsGeneralPositionAt.isGoodPositionAt.{0} ∧
  type_of% @Polyfold.tangentSpace_solutionSet_eq_linKer.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.linZero_mem_linSet.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.linZero_surjective.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.map_ker_linZero.{0, 0} ∧
  type_of% @Polyfold.stabSign_of_surjective.{0, 0} ∧
  type_of% @Polyfold.stabRayEquiv_zero.{0, 0, 0} ∧
  type_of% @Polyfold.ChartPoint.stabRayEquiv_eq_tangentOr.{0, 0} ∧
  type_of% @Polyfold.IsStabKernels.orRay_eq_tangentOr.{0, 0, 0} ∧
  type_of% @Polyfold.isStabKernels_zero.{0, 0} ∧
  type_of% @Polyfold.exists_tangentFamily.{0, 0} ∧
  type_of% @Polyfold.tangentFamily_L.{0, 0} ∧
  type_of% @Polyfold.cont_tangentOr.{0, 0} ∧
  type_of% @Polyfold.isLineOrientation_tangentOr.{0, 0} ∧
  type_of% @Polyfold.isLineOrientation_tangentOr_of_isSectionOrientation.{0, 0} ∧
  type_of% @Polyfold.theorem_6_6_18_hyp.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_6_6_18_solutionSet.{0, 0},
    @Polyfold.MPolyfold.IsGeneralPositionAt.isGoodPositionAt.{0},
    @Polyfold.tangentSpace_solutionSet_eq_linKer.{0, 0},
    @Polyfold.ChartPoint.linZero_mem_linSet.{0, 0},
    @Polyfold.ChartPoint.linZero_surjective.{0, 0},
    @Polyfold.ChartPoint.map_ker_linZero.{0, 0},
    @Polyfold.stabSign_of_surjective.{0, 0},
    @Polyfold.stabRayEquiv_zero.{0, 0, 0},
    @Polyfold.ChartPoint.stabRayEquiv_eq_tangentOr.{0, 0},
    @Polyfold.IsStabKernels.orRay_eq_tangentOr.{0, 0, 0},
    @Polyfold.isStabKernels_zero.{0, 0},
    @Polyfold.exists_tangentFamily.{0, 0},
    @Polyfold.tangentFamily_L.{0, 0},
    @Polyfold.cont_tangentOr.{0, 0},
    @Polyfold.isLineOrientation_tangentOr.{0, 0},
    @Polyfold.isLineOrientation_tangentOr_of_isSectionOrientation.{0, 0},
    @Polyfold.theorem_6_6_18_hyp.{0, 0}⟩

section Paths

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]

/-- A reparametrized contraction line `s ↦ H(κ(s), y)` is an sc-smooth path in `U`. -/
theorem contraction_path {U : Set X} {H : (Fin 1 → ℝ) × X → X} {W : Set ((Fin 1 → ℝ) × X)}
    (hWU : Icc (0 : Fin 1 → ℝ) 1 ×ˢ U ⊆ W) (hH : ((rnPolyfold 1).prod PX).IsScSmoothOn PX H W)
    (hHU : ∀ t ∈ Icc (0 : Fin 1 → ℝ) 1, ∀ y ∈ U, H (t, y) ∈ U) {κ : ℝ → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hκI : ∀ s, κ s ∈ Icc (0 : ℝ) 1) {y : X} (hy : y ∈ U)
    (hys : y ∈ PX.smoothSet) :
    (rnPolyfold 1).IsScSmoothMap PX (fun s : Fin 1 → ℝ => H (pt1 (κ (s 0)), y)) ∧
      ∀ s : Fin 1 → ℝ, H (pt1 (κ (s 0)), y) ∈ U := by
  refine ⟨?_, fun s => hHU _ (pt1_mem_Icc (hκI _)) y hy⟩
  have hin : (rnPolyfold 1).IsScSmoothMap ((rnPolyfold 1).prod PX)
      (fun s : Fin 1 → ℝ => (pt1 (κ (s 0)), y)) :=
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_rn_rn_of_contDiff (contDiff_pt1_comp hκ))
      (isScSmoothMap_const_of_mem_smoothSet hys)
  exact MPolyfold.IsScSmoothOn.comp hH hin (fun s _ => hWU ⟨pt1_mem_Icc (hκI _), hy⟩)

/-- **An sc-smoothly contractible set joins its smooth points by sc-smooth paths in it.** -/
theorem exists_path_of_contractible {U : Set X} (hU : IsScContractibleB PX U) {y₁ y₂ : X}
    (h₁ : y₁ ∈ U) (h₂ : y₂ ∈ U) (hs₁ : y₁ ∈ PX.smoothSet) (hs₂ : y₂ ∈ PX.smoothSet) :
    ∃ γ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ ∧ γ (pt1 0) = y₁ ∧
      γ (pt1 1) = y₂ ∧ ∀ t, γ t ∈ U := by
  obtain ⟨H, y₀, W, -, hWU, hH, hHU, hH1, hH0⟩ := hU
  have hκI : ∀ s, Real.smoothTransition s ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨Real.smoothTransition.nonneg s, Real.smoothTransition.le_one s⟩
  have hκ' : ContDiff ℝ ∞ fun s : ℝ => Real.smoothTransition (1 - s) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
  obtain ⟨hρs, hρU⟩ := contraction_path hWU hH hHU hκ' (fun s => hκI _) h₁ hs₁
  obtain ⟨hσs, hσU⟩ := contraction_path hWU hH hHU Real.smoothTransition.contDiff hκI h₂ hs₂
  refine ⟨concatPath (fun s : Fin 1 → ℝ => H (pt1 (Real.smoothTransition (1 - s 0)), y₁))
    (fun s : Fin 1 → ℝ => H (pt1 (Real.smoothTransition (s 0)), y₂)),
    isScSmoothMap_concatPath hρs hσs ?_, ?_, ?_, ?_⟩
  · simp only [pt1_apply, sub_self, Real.smoothTransition.zero]
    rw [hH0 y₁ h₁, hH0 y₂ h₂]
  · rw [concatPath_zero]
    simp only [pt1_apply, sub_zero, Real.smoothTransition.one]
    exact hH1 y₁ h₁
  · rw [concatPath_one]
    simp only [pt1_apply, Real.smoothTransition.one]
    exact hH1 y₂ h₂
  · intro t
    unfold concatPath
    split_ifs
    · exact hρU _
    · exact hσU _

end Paths

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **A's hypothesis gives B's**: a project orientation of `f` (Definition 6.40, pairs `V ⊆ U`)
satisfies B's `D640` (sc-smoothly contractible `U`), with the pair `(U, U)`. -/
theorem D640_of_isSectionOrientation {Bd : StrongBundle PX P} {f : X → Y}
    {hf : Bd.IsScFredholmSection f} {o : (y : X) → (hy : y ∈ PX.smoothSet) → Orx f hf y hy}
    (ho : IsSectionOrientation f hf o) : D640 f hf o := by
  intro x hx U c hc _hUc hUo hxU hUcon hLP
  exact ho x hx c hc U U ⟨hLP, hUo, hUo, le_refl U, hxU,
    fun y₁ h₁ y₂ h₂ hs₁ hs₂ => exists_path_of_contractible hUcon h₁ h₂ hs₁ hs₂⟩

omit [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- **The conclusions of Theorem 5.18 give B's "compact manifold with boundary with corners".** -/
theorem isCompactCornerManifold_of_solutionSetInGeneralPosition {Bd : StrongBundle PX P}
    {g : X → Y} (h : Bd.SolutionSetInGeneralPosition g) :
    IsCompactCornerManifold PX (solSet P g) := by
  obtain ⟨-, -, hcpt, hS, -, hcs, -, -⟩ := h
  exact ⟨hcpt, hS.isSubMPolyfold, PX.paracompactSpace_subtype (solutionSet P g), hcs⟩

omit [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- **Partial `A ⇒ B` (1)**: with tame germ data (which B does not assume), A (its first conjunct,
`theorem_6_6_18_solutionSet`) gives B's first conclusion. -/
theorem corner_of_A (hA : type_of% @Polyfold.theorem_6_6_18_solutionSet.{0, 0})
    {Bd : StrongBundle PX P} {f : X → Y} (hX : PX.IsTame)
    (hft : Bd.IsScFredholmSectionTame f) (hP : Bd.IsProper f)
    (hgp : ∀ x, IsZeroAt P f x → Bd.IsGeneralPositionGerm f x) :
    IsCompactCornerManifold PX (solSet P f) :=
  isCompactCornerManifold_of_solutionSetInGeneralPosition (hA hX hft hP hgp)

end Glue

#rt_check RoundTrip.V6_61.D640_of_isSectionOrientation [Polyfold.theorem_6_6_18_solutionSet,
  Polyfold.MPolyfold.IsGeneralPositionAt.isGoodPositionAt,
  Polyfold.tangentSpace_solutionSet_eq_linKer, Polyfold.ChartPoint.linZero_mem_linSet,
  Polyfold.ChartPoint.linZero_surjective, Polyfold.ChartPoint.map_ker_linZero,
  Polyfold.stabSign_of_surjective, Polyfold.stabRayEquiv_zero,
  Polyfold.ChartPoint.stabRayEquiv_eq_tangentOr, Polyfold.IsStabKernels.orRay_eq_tangentOr,
  Polyfold.isStabKernels_zero, Polyfold.exists_tangentFamily, Polyfold.tangentFamily_L,
  Polyfold.cont_tangentOr, Polyfold.isLineOrientation_tangentOr,
  Polyfold.isLineOrientation_tangentOr_of_isSectionOrientation, Polyfold.theorem_6_6_18_hyp]
#rt_check RoundTrip.V6_61.corner_of_A [Polyfold.theorem_6_6_18_solutionSet,
  Polyfold.MPolyfold.IsGeneralPositionAt.isGoodPositionAt,
  Polyfold.tangentSpace_solutionSet_eq_linKer, Polyfold.ChartPoint.linZero_mem_linSet,
  Polyfold.ChartPoint.linZero_surjective, Polyfold.ChartPoint.map_ker_linZero,
  Polyfold.stabSign_of_surjective, Polyfold.stabRayEquiv_zero,
  Polyfold.ChartPoint.stabRayEquiv_eq_tangentOr, Polyfold.IsStabKernels.orRay_eq_tangentOr,
  Polyfold.isStabKernels_zero, Polyfold.exists_tangentFamily, Polyfold.tangentFamily_L,
  Polyfold.cont_tangentOr, Polyfold.isLineOrientation_tangentOr,
  Polyfold.isLineOrientation_tangentOr_of_isSectionOrientation, Polyfold.theorem_6_6_18_hyp]

end RoundTrip.V6_61
