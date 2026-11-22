import Polyfold.Chapter18.MultisectionConstructions
import Polyfold.Chapter18.CompactnessExamples
import Polyfold.Chapter8.Book
import Polyfold.Chapter5.SeparablePartitionsOfUnity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§§18.3–18.4, pp. 851–855: **non-degenerate witnesses for Theorem 18.3.5, Theorem 18.3.6,
Definition 18.4.1, Proposition 18.4.3 and Theorem 18.4.4** on the reflection bundle of the
diagonal section `reflDiag` (`FredholmSectionFunctorsExamples.lean`).

# sc⁺-multisection functors on the reflection bundle

`C = ℤ/2 ⋉ ℝ`, `μ(x) = ℝ`, the generator `−1` acting by `x ↦ −x` and `v ↦ −v`; the model with two
copies of `Ψ̄` (`reflPair`) is `ℝ ⊔ ℝ` with the trivial bundle `ℝ × ℝ` on each copy.

* `reflModel_admitsScPartitionsOfUnity`, `reflection_admitsModelPartitionsOfUnity`,
  `reflection_admitsModelBumpFunctions`: the model is built on `ℝ¹` (a Hilbert space), so it
  admits sc-smooth partitions of unity and bump functions (Definition 18.4.1).
* `reflModel_mem_smoothSet`, `reflModelW_mem_smoothSet`: every point of the model is smooth.
* `proposition_18_4_3_witness`: Proposition 18.4.3 at the object `0` (isotropy `ℤ/2`, acting by
  `v ↦ −v` on the fibre) and the vector `e = 1 ≠ 0`: an atomic, structurable sc⁺-multisection
  functor `Λ` with `Λ(0, 1) > 0`, on the bundle of the sc-Fredholm section functor `reflDiag`.
* `theorem_18_3_5_witness`: `Λ ⊕ Λ` and `2 ⊙ Λ` are structurable (Theorem 18.3.5).
* `reflIdCovering`, `theorem_18_3_6_witness`: the identity strong bundle proper covering and
  Theorem 18.3.6 for it.
* `isBoundaryStructurable_of_boundary_eq_empty`, `reflModel_boundary`, `theorem_18_4_4_witness`:
  all hypotheses of Theorem 18.4.4 with the non-trivial `Λ` above, an auxiliary norm, `V = |C|`
  and `β = 1`, and its conclusion.  Here `∂C = ∅` (`reflection_boundarySet`), so the extension
  condition (3) is empty; the norm bound (1) is not.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped ENNReal

noncomputable section

namespace Polyfold

namespace SBLocalization

variable {A : SEP.{u}}

/-- **Over an ep-groupoid without boundary every `Λ` is structurable over `∂X`**
(Definition 14.1.7 with `∂X = ∅`; a good system for `∂X` exists by `theorem_14_1_6_hyp`). -/
theorem isBoundaryStructurable_of_boundary_eq_empty (hX : A.X.IsTame)
    (hpara : A.X.HasParacompactOrbitSpace) (hb : A.X.PObj.boundary = ∅) (Λ : A.W → ℚ≥0) :
    IsBoundaryStructurable A Λ := by
  obtain ⟨𝒰, -⟩ := A.X.theorem_14_1_6_hyp hX hpara (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  have he : IsEmpty A.X.PObj.boundary := isEmpty_coe_sort.2 hb
  have hnb : ∀ x, x ∉ A.X.PObj.boundary := fun x hx => he.false ⟨x, hx⟩
  refine ⟨⟨fun q hq => (hnb _ hq).elim, fun x hx => (hnb x hx).elim⟩,
    ⟨𝒰, fun x => (he.false x).elim⟩, ⟨?_⟩⟩
  exact
    { τ := fun x => (he.false x).elim
      locallyConstant := fun x => (he.false x).elim
      finite := fun x => (he.false x).elim
      swap := fun x => (he.false x).elim
      diag := fun x => (he.false x).elim
      biact := fun x => (he.false x).elim
      compat := fun x => (he.false x).elim }

end SBLocalization

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor TrivialBundle
  StrongBundleUniformizerConstruction StrongBundleUniformizerData StrongPolyfoldBundleConstruction
  PolyfoldConstruction SBLocalization

/-! ### Smooth points, partitions of unity and bump functions of the model -/

/-- Every point of the trivial bundle `ℝ × ℝ → ℝ` is a smooth point of `W[0]`. -/
theorem reflK_mem_smoothSet (y : (Fin 1 → ℝ) × (Fin 1 → ℝ)) :
    y ∈ (TrivialBundle.bundle 1 1).toMPolyfold0.smoothSet := by
  have h := mem_smoothSet_toMPolyfold0_of_chart (B := TrivialBundle.bundle 1 1)
    (TrivialBundle.isChart_chart (k := 1) 0)
    (z := (show (TrivialBundle.chart (n := 1) (k := 1) 0).φ.model.E 0 from y.1)) (k := y.2)
    ⟨y, ⟨mem_univ _, mem_univ _⟩, rfl⟩
    ((TrivialBundle.chart (n := 1) (k := 1) 0).φ.model.E.mem_smooth_iff.2 fun m =>
      (bijective_toBase_const _ m).2 _)
    ((TrivialBundle.chart (n := 1) (k := 1) 0).F.mem_smooth_iff.2 fun m =>
      (bijective_toBase_const _ m).2 _)
  convert h using 1
  change y = ((Equiv.subRight (0 : Fin 1 → ℝ)).prodCongr (Equiv.refl (Fin 1 → ℝ))).symm (y.1, y.2)
  rcases y with ⟨a, b⟩
  simp [Prod.map]

/-- Every point of the model `ℝ ⊔ ℝ` is smooth. -/
theorem reflModel_mem_smoothSet (x : (reflQ.modelSEP reflPair.Ψ).Obj) :
    x ∈ (reflQ.modelSEP reflPair.Ψ).X.PObj.smoothSet := by
  obtain ⟨i, q⟩ := x
  exact ((MPolyfold.isLocalScDiffeo_sigmaMk (fun _ : Bool => rnPolyfold 1) i).mem_smoothSet_iff
    q).2 (by rw [rnPolyfold_smoothSet]; exact mem_univ q)

/-- Every point of the model bundle `(ℝ × ℝ) ⊔ (ℝ × ℝ)` is a smooth point of `W[0]`. -/
theorem reflModelW_mem_smoothSet (w : (reflQ.modelSEP reflPair.Ψ).W) :
    w ∈ (reflQ.modelSEP reflPair.Ψ).B.toMPolyfold0.smoothSet := by
  have e : (reflQ.modelSEP reflPair.Ψ).B.toMPolyfold0 =
      MPolyfold.sigma (fun _ : Bool => (TrivialBundle.bundle 1 1).toMPolyfold0) :=
    StrongBundle.sigma_toMPolyfold0 _
  rw [e]
  obtain ⟨i, k⟩ := w
  exact ((MPolyfold.isLocalScDiffeo_sigmaMk
    (fun _ : Bool => (TrivialBundle.bundle 1 1).toMPolyfold0) i).mem_smoothSet_iff k).2
    (reflK_mem_smoothSet k)

/-- **The model `ℝ ⊔ ℝ` admits sc-smooth partitions of unity** as an M-polyfold: its charts are
those of `ℝ¹`, a Hilbert space (Corollary 5.5.17 and Theorem 5.5.10). -/
theorem reflModel_admitsScPartitionsOfUnity :
    (reflQ.modelSEP reflPair.Ψ).X.PObj.AdmitsScPartitionsOfUnity := by
  refine MPolyfold.admitsScPartitionsOfUnity_of_hilbert_unconditional fun x => ?_
  obtain ⟨i, q⟩ := x
  obtain ⟨φ, hφ, hq, hb, -⟩ := rnPolyfold_one_hilbert_hypothesis q
  exact ⟨MPolyfold.sigmaChart i φ,
    (MPolyfold.isChart_sigmaChart_iff (P := fun _ : Bool => rnPolyfold 1)).2 hφ, ⟨q, hq, rfl⟩, hb⟩

/-- **Definition 18.4.1 holds for the reflection polyfold (partitions of unity)**. -/
theorem reflection_admitsModelPartitionsOfUnity :
    reflectionConstruction.AdmitsModelPartitionsOfUnity :=
  ⟨reflQ.baseCoveringFamily reflPair,
    (reflectionConstruction.remark_18_4_2 _).2.2 reflModel_admitsScPartitionsOfUnity⟩

/-- **Definition 18.4.1 holds for the reflection polyfold (bump functions)**. -/
theorem reflection_admitsModelBumpFunctions : reflectionConstruction.AdmitsModelBumpFunctions :=
  ⟨reflQ.baseCoveringFamily reflPair,
    EpGroupoid.theorem_12_3_2_1.2 reflModel_admitsScPartitionsOfUnity.admitsBumpFunctions⟩

/-! ### Proposition 18.4.3 -/

/-- The vector `1` over the point `0` of the copy `true`. -/
abbrev reflVec : reflQ.ModelW reflPair.Ψ := ⟨true, ((0 : Fin 1 → ℝ), fun _ => (1 : ℝ))⟩

/-- `Γ̄(reflVec) = (0, 1)`. -/
theorem bundleModelObj_reflVec :
    reflQ.bundleModelObj reflPair.Ψ reflVec = reflV.objMk (0 : Fin 1 → ℝ) (fun _ => (1 : ℝ)) :=
  rfl

/-- **Proposition 18.4.3 on the reflection bundle**: at the object `0`, whose isotropy `ℤ/2`
acts by `v ↦ −v` on the fibre, and the vector `e = 1 ≠ 0`, there is an atomic, structurable
sc⁺-multisection functor `Λ` with `Λ(0, 1) > 0`; the bundle carries the sc-Fredholm section
functor `reflDiag`. -/
theorem proposition_18_4_3_witness :
    reflQ.IsScFredholmSectionFunctor reflDiag ∧
      (∀ v : Fin 1 → ℝ, v ≠ 0 → reflV.map ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) v ≠ v) ∧
      ∃ Λ : reflV.EObj → ℚ≥0, reflQ.IsScPlusMultisectionFunctor Λ ∧
        reflQ.IsStructurableFunctor Λ ∧
        IsAtomic (reflQ.modelSEP reflPair.Ψ) (reflQ.bundlePull reflPair.Ψ Λ) ∧
        (fun _ => (1 : ℝ)) ≠ (0 : Fin 1 → ℝ) ∧
        0 < Λ (reflV.objMk (0 : Fin 1 → ℝ) (fun _ => (1 : ℝ))) := by
  obtain ⟨Λ, hΛ, hpos, hat, hst⟩ := reflQ.proposition_18_4_3 reflPair
    reflection_admitsModelBumpFunctions (w := reflVec) (reflModel_mem_smoothSet _)
    (reflModelW_mem_smoothSet _) (e := reflQ.bundleModelObj reflPair.Ψ reflVec)
    (reflV.groupoid.π_eq_π_iff.1 rfl)
  refine ⟨isScFredholmSectionFunctor_reflDiag, reflDiag_nondegenerate.2.1, Λ, hΛ, hst, hat,
    fun h => one_ne_zero (congrFun h 0), hpos⟩

/-! ### Theorems 18.3.5 and 18.3.6 -/

/-- **Theorem 18.3.5 on the reflection bundle**: for the non-trivial structurable `Λ` of
`proposition_18_4_3_witness`, `Λ ⊕ Λ` and `2 ⊙ Λ` are structurable sc⁺-multisection functors
(`β = 2` is an sc-smooth functor). -/
theorem theorem_18_3_5_witness :
    ∃ Λ : reflV.EObj → ℚ≥0, reflQ.IsStructurableFunctor Λ ∧
      0 < Λ (reflV.objMk (0 : Fin 1 → ℝ) (fun _ => (1 : ℝ))) ∧
      reflectionConstruction.IsScSmoothFunctionFunctor (fun _ => (2 : ℝ)) ∧
      reflQ.IsStructurableFunctor (multisectionFunctorAdd Λ Λ) ∧
      reflQ.IsStructurableFunctor (multisectionFunctorSmul (fun _ => (2 : ℝ)) Λ) := by
  obtain ⟨-, -, Λ, -, hst, -, -, hpos⟩ := proposition_18_4_3_witness
  have hβ : reflectionConstruction.IsScSmoothFunctionFunctor (fun _ => (2 : ℝ)) :=
    ⟨fun _ => rfl, fun _ => isScSmoothMap_real_const 2⟩
  obtain ⟨h1, h2⟩ := reflQ.theorem_18_3_5 hst hst hβ
  exact ⟨Λ, hst, hpos, hβ, h1, h2⟩

/-- **The identity strong bundle proper covering functor** of the reflection bundle, through
the model with two copies of `Ψ̄` (Definition 8.5.9 for the identity). -/
def reflIdCovering : StrongBundleProperCovering reflQ reflQ where
  functor := GroupoidFunctor.id reflV.groupoid
  base := GroupoidFunctor.id GCT.reflection.toGroupoidStr
  proj_functor _ := rfl
  c' := reflPair
  c := reflPair
  F := EpFunctor.id _
  A := id
  isProper := EpStrongBundle.isProperStrongBundleCovering2021_id _
  comm _ := reflV.groupoid.π_eq_π_iff.1 rfl

/-- **Theorem 18.3.6 on the reflection bundle**: the pull-back of the non-trivial structurable
`Λ` of `proposition_18_4_3_witness` along `reflIdCovering` is structurable. -/
theorem theorem_18_3_6_witness :
    ∃ Λ : reflV.EObj → ℚ≥0, reflQ.IsStructurableFunctor Λ ∧
      0 < Λ (reflV.objMk (0 : Fin 1 → ℝ) (fun _ => (1 : ℝ))) ∧
      reflQ.IsStructurableFunctor (Λ ∘ reflIdCovering.functor.obj) := by
  obtain ⟨-, -, Λ, -, hst, -, -, hpos⟩ := proposition_18_4_3_witness
  exact ⟨Λ, hst, hpos, theorem_18_3_6 reflIdCovering hst⟩

/-! ### Theorem 18.4.4 -/

/-- The model `ℝ ⊔ ℝ` has no boundary (`∂C = ∅`, `reflection_boundarySet`). -/
theorem reflModel_boundary : (reflQ.modelSEP reflPair.Ψ).X.PObj.boundary = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨α, hα, -⟩ := (reflQ.mem_boundary_model_iff reflPair x).1 hx
  rw [reflection_boundarySet] at hα
  exact hα

/-- **Theorem 18.4.4 on the reflection bundle**: all hypotheses hold for an auxiliary norm `N`,
the non-trivial structurable `Λ` of `proposition_18_4_3_witness`, `V = |C|` and `β = 1`, and the
theorem gives a structurable `Λ'` with `N(Λ') ≤ 1` and `|dom-supp(Λ')| ⊂ V`. -/
theorem theorem_18_4_4_witness :
    ∃ N : reflV.EObj → ℝ≥0∞, reflQ.IsAuxNormFunctor N ∧
      ∃ Λ : reflV.EObj → ℚ≥0, IsMorInvariant Λ ∧
        0 < Λ (reflV.objMk (0 : Fin 1 → ℝ) (fun _ => (1 : ℝ))) ∧
        IsBoundaryStructurable (reflQ.modelSEP reflPair.Ψ) (reflQ.bundlePull reflPair.Ψ Λ) ∧
        orbitBoundaryDomSupp reflectionConstruction Λ ⊆ univ ∧
        ∃ Λ' : reflV.EObj → ℚ≥0, reflQ.IsStructurableFunctor Λ' ∧
          (∀ α, pointwiseNormFunctor N Λ' α ≤ ENNReal.ofReal 1) ∧ orbitDomSupp Λ' ⊆ univ ∧
          ∀ e : reflV.EObj, reflV.base e ∈ reflectionConstruction.boundarySet → Λ' e = Λ e := by
  obtain ⟨N, hN⟩ := reflQ_exists_isAuxNormFunctor
  obtain ⟨-, -, Λ, hΛ, -, -, -, hpos⟩ := proposition_18_4_3_witness
  have hbs := isBoundaryStructurable_of_boundary_eq_empty
    (reflectionConstruction.isTame_modelEpGroupoid (Ψ := reflQ.modelBase reflPair.Ψ)
      reflectionConstruction_isTame)
    (reflQ.hasParacompactOrbitSpace_model reflPair) reflModel_boundary
    (reflQ.bundlePull reflPair.Ψ Λ)
  refine ⟨N, hN, Λ, hΛ.1, hpos, hbs, subset_univ _, ?_⟩
  refine reflQ.theorem_18_4_4 reflPair reflectionConstruction_isTame
    reflModel_admitsScPartitionsOfUnity (hN reflPair) hΛ.1 hbs isOpen_univ (subset_univ _)
    (fun _ => rfl) (fun _ => zero_le_one) continuous_const (subset_univ _) ?_
  intro α hα
  unfold orbitBoundaryDomSupp at hα
  rw [reflection_boundarySet] at hα
  simp at hα

end GCT.VectorBundle.ReflectionBundle

end Polyfold
