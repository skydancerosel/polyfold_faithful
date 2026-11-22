import Polyfold.Chapter18.Compactness
import Polyfold.Chapter18.FredholmSectionFunctorsExamples
import Polyfold.Chapter17.PolyfoldConstructionExamples
import Polyfold.Chapter5.Transversality

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.2, pp. 849–851: **witnesses for the compactness notions** (Definitions 18.2.1, 18.2.3, 18.2.4,
Theorems 18.2.2, 18.2.6) and for the auxiliary norms of `AuxiliaryNorms.lean`, on the reflection
bundle `P : E → ℤ/2 ⋉ ℝ` with the diagonal section `f(x) = (x, x)` (`reflDiag`).  Numbers and pages
are the 2021 text's.

* `reflQ_exists_isAuxNormFunctor`, `reflQ_hasReflexiveFibers`,
  `reflQ_exists_isReflexiveAuxNormFunctor`: auxiliary norms and reflexive auxiliary norms
  `N : E → [0, ∞]` exist (so the quantifiers over `N` in Definitions 18.2.1 (2), (3) and 18.2.4
  are not empty); in the model with two copies of `Ψ̄` (non-trivial isotropy `−1` at `0`),
  `N ∘ Γ̄` is finite on `W_{0,1}` (`reflQ_auxNorm_finite`).
* `reflDiag_hasCompactModuliSpace`, `reflDiag_isProper`, `reflDiag_isProperLtInfty`
  (Theorem 18.2.2 applied), `reflDiag_stronglyControlsCompactness` (Definition 18.2.3 for every
  auxiliary norm).
* `hasReflexiveLocalCompactness_of_locallyCompact` (a locally compact model object space gives
  Definition 18.2.4) and `reflDiag_hasReflexiveLocalCompactness`.
* `reflection_boundarySet` (`∂C = ∅` for `ℤ/2 ⋉ ℝ`), `theorem_18_2_6_witness`: all hypotheses of
  Theorem 18.2.6 hold for `reflDiag` (with `U_∂ = ∅`) and its conclusion.  The boundary is empty
  here; a witness with `∂C ≠ ∅` is not built.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped ENNReal

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor

namespace StrongPolyfoldBundleConstruction

open PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  {Q : V.StrongPolyfoldBundleConstruction S}

/-- **Locally compact uniformizer domains give the reflexive local compactness property**
(Definition 18.2.4): `U(z) = |Γ|(|int K|)` for a compact neighbourhood `K` of a representative,
whatever `N` is. -/
theorem hasReflexiveLocalCompactness_of_locallyCompact (c : Q.BundleCoveringFamily)
    [∀ i, WeaklyLocallyCompactSpace (Q.modelBase c.Ψ i).1.O] (f : V.SectionFunctor) :
    Q.HasReflexiveLocalCompactness f := by
  intro N _ z
  obtain ⟨q, rfl⟩ := (isHomeomorph_modelOrbitMap c.cover).surjective z
  obtain ⟨x, rfl⟩ := (Q.modelSEP c.Ψ).X.surjective_π q
  obtain ⟨i, y⟩ := x
  obtain ⟨K₀, hK₀, hK₀n⟩ := exists_compact_mem_nhds y
  set K : Set (S.ModelObj (Q.modelBase c.Ψ)) := Sigma.mk i '' K₀
  have hK : IsCompact K := hK₀.image continuous_sigmaMk
  have hKn : K ∈ 𝓝 (⟨i, y⟩ : S.ModelObj (Q.modelBase c.Ψ)) :=
    isOpenMap_sigmaMk.image_mem_nhds hK₀n
  have hKc : IsCompact ((S.modelFunctor (Q.modelBase c.Ψ)).orbitMap ''
      ((Q.modelSEP c.Ψ).X.π '' K)) :=
    (hK.image (Q.modelSEP c.Ψ).X.continuous_π).image
      (isHomeomorph_modelOrbitMap c.cover).continuous
  refine ⟨_, isOpen_modelImage c isOpen_interior,
    ⟨_, ⟨⟨i, y⟩, mem_interior_iff_mem_nhds.2 hKn, rfl⟩, rfl⟩, ?_⟩
  refine hKc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hKc.isClosed)
  exact inter_subset_left.trans (image_mono (image_mono interior_subset))

end StrongPolyfoldBundleConstruction

namespace ReflectionBundle

open StrongPolyfoldBundleConstruction PolyfoldConstruction

/-- **An auxiliary norm `N : E → [0, ∞]` exists** on the reflection bundle. -/
theorem reflQ_exists_isAuxNormFunctor : ∃ N : reflV.EObj → ℝ≥0∞, reflQ.IsAuxNormFunctor N :=
  reflQ.exists_isAuxNormFunctor reflQ_hasStrongBundleUniformizers

/-- For every auxiliary norm `N`, in the model with two copies of `Ψ̄` the value `N ∘ Γ̄` is
finite on `W_{0,1}`. -/
theorem reflQ_auxNorm_finite {N : reflV.EObj → ℝ≥0∞} (hN : reflQ.IsAuxNormFunctor N)
    (w : reflQ.ModelW reflPair.Ψ) (hw : w ∈ (reflQ.modelSEP reflPair.Ψ).B.oneSet) :
    reflQ.bundlePull reflPair.Ψ N w ≠ ⊤ :=
  (hN reflPair).ne_top w hw

/-- The model with two copies of `Ψ̄` has reflexive `(0, 1)`-fibres (finite-dimensional fibre
model `ℝ`). -/
theorem reflPair_hasReflexiveFibersIn : reflQ.HasReflexiveFibersIn reflPair.Ψ :=
  StrongBundle.hasReflexiveFibers_of_atlas fun c ⟨_, c', hc', hcc⟩ => by
    subst hcc
    obtain ⟨a, rfl⟩ := hc'
    exact isReflexive_of_finiteDimensional (F := Fin 1 → ℝ)

/-- **The reflection bundle has reflexive `(0, 1)`-fibres** (Definition 18.1.9, in every
model). -/
theorem reflQ_hasReflexiveFibers : reflQ.HasReflexiveFibers :=
  (reflQ.hasReflexiveFibers_iff_model reflPair).2 reflPair_hasReflexiveFibersIn

/-- **A reflexive auxiliary norm exists** on the reflection bundle. -/
theorem reflQ_exists_isReflexiveAuxNormFunctor :
    ∃ N : reflV.EObj → ℝ≥0∞, reflQ.IsReflexiveAuxNormFunctor N :=
  reflQ.exists_isReflexiveAuxNormFunctor reflQ_hasStrongBundleUniformizers
    reflQ_hasReflexiveFibers

/-- **Definition 18.2.1 (1) for `f(x) = (x, x)`**: `|S_f| = {|0|}` is compact. -/
theorem reflDiag_hasCompactModuliSpace : reflDiag.HasCompactModuliSpace := by
  unfold SectionFunctor.HasCompactModuliSpace
  rw [reflDiag_zeroSet, image_singleton]
  exact isCompact_singleton

/-- **Definition 18.2.1 (2) for `f`**: `f` is proper (Theorem 18.2.2). -/
theorem reflDiag_isProper : reflQ.IsProper reflDiag :=
  ((reflQ.theorem_18_2_2 reflDiag reflQ_hasStrongBundleUniformizers
    isScFredholmSectionFunctor_reflDiag).out 0 1).1 reflDiag_hasCompactModuliSpace

/-- **Definition 18.2.1 (3) for `f`**: `f` is proper`<∞` (Theorem 18.2.2). -/
theorem reflDiag_isProperLtInfty : reflQ.IsProperLtInfty reflDiag :=
  ((reflQ.theorem_18_2_2 reflDiag reflQ_hasStrongBundleUniformizers
    isScFredholmSectionFunctor_reflDiag).out 0 2).1 reflDiag_hasCompactModuliSpace

/-- **Definition 18.2.3 for `f`**: for every auxiliary norm `N` there is an open neighbourhood
`U` of `|S_f|` such that `(N, U)` strongly controls compactness, and an auxiliary norm exists. -/
theorem reflDiag_stronglyControlsCompactness :
    (∃ N : reflV.EObj → ℝ≥0∞, reflQ.IsAuxNormFunctor N) ∧
      ∀ N : reflV.EObj → ℝ≥0∞, reflQ.IsAuxNormFunctor N →
        ∃ U, reflDiag.StronglyControlsCompactness N U := by
  refine ⟨reflQ_exists_isAuxNormFunctor, fun N hN => ?_⟩
  obtain ⟨U, hUo, hSU, hC⟩ := reflDiag_isProperLtInfty.2 N hN
  exact ⟨U, hUo, hSU, hC⟩

/-- **Definition 18.2.4 for `f`**: `f` has the reflexive local compactness property (the model
object space `ℝ ⊔ ℝ` is locally compact). -/
theorem reflDiag_hasReflexiveLocalCompactness : reflQ.HasReflexiveLocalCompactness reflDiag :=
  have : ∀ i, WeaklyLocallyCompactSpace (reflQ.modelBase reflPair.Ψ i).1.O := fun _ =>
    inferInstanceAs (WeaklyLocallyCompactSpace (Fin 1 → ℝ))
  hasReflexiveLocalCompactness_of_locallyCompact reflPair reflDiag

/-- **`∂C = ∅`** for `C = ℤ/2 ⋉ ℝ` (`ℝ` has no boundary). -/
theorem reflection_boundarySet : reflectionConstruction.boundarySet = ∅ := by
  refine eq_empty_of_forall_notMem fun α (hα : 1 ≤ reflectionConstruction.degIndex α) => ?_
  rw [reflectionConstruction.definition_17_1_30 (α := α) (Ψ := LocalUniformizer.reflection) rfl
    (q := α) rfl] at hα
  have := rnPolyfold_degIndex 1 α
  change 1 ≤ (rnPolyfold 1).degIndex α at hα
  omega

/-- **The hypotheses of Theorem 18.2.6 hold for `f`** (with `U_∂ = ∅`, `C` tame, reflexive
fibres, a reflexive auxiliary norm, compact moduli space, reflexive local compactness), and its
conclusion: an open `U ⊇ |S_f|` with `U ∩ |∂C| = ∅` such that `(N, U)` controls compactness. -/
theorem theorem_18_2_6_witness :
    ∃ N : reflV.EObj → ℝ≥0∞, reflQ.IsReflexiveAuxNormFunctor N ∧
      reflectionConstruction.IsTame ∧ reflQ.HasReflexiveFibers ∧
      reflQ.IsScFredholmSectionFunctor reflDiag ∧ reflDiag.HasCompactModuliSpace ∧
      reflQ.HasReflexiveLocalCompactness reflDiag ∧
      ∃ U, U ∩ GCT.reflection.toGroupoidStr.π '' reflectionConstruction.boundarySet = ∅ ∧
        reflDiag.ControlsCompactness N U := by
  obtain ⟨N, hN⟩ := reflQ_exists_isReflexiveAuxNormFunctor
  refine ⟨N, hN, reflectionConstruction_isTame, reflQ_hasReflexiveFibers,
    isScFredholmSectionFunctor_reflDiag, reflDiag_hasCompactModuliSpace,
    reflDiag_hasReflexiveLocalCompactness, ?_⟩
  refine reflQ.theorem_18_2_6 reflDiag reflQ_hasStrongBundleUniformizers
    reflectionConstruction_isTame reflQ_hasReflexiveFibers hN isScFredholmSectionFunctor_reflDiag
    reflDiag_hasCompactModuliSpace reflDiag_hasReflexiveLocalCompactness
    ⟨∅, isOpen_empty, (empty_inter _).symm⟩ ?_ ?_
  · rw [reflection_boundarySet, inter_empty, image_empty]
  · rw [empty_inter, closure_empty]
    exact isCompact_empty

end ReflectionBundle

end GCT.VectorBundle

end Polyfold
