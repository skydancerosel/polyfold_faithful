import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, pp. 263–276
(preprint §6.5): families on the cube `[0, 1]ⁿ`.

# The cube `[0, 1]ⁿ` as a smooth manifold with corners

Mathlib has the model with corners `ModelWithCorners.pi I` of a finite family of models and the
charted space of a finite product (`piChartedSpace`), but not the smooth structure of the
product.  Here:

* **`isManifold_modelPi`**: a finite product of `Cᵐ` manifolds (with corners) is a `Cᵐ` manifold
  with corners for the model `ModelWithCorners.pi I`: the coordinate changes of the product
  charts are the products of the coordinate changes of the factors.
* **`contMDiff_eval_modelPi`**: the projection `x ↦ x i` is `Cᵐ`.
* The cube: `Fin n → [0, 1]` with the model `𝓡∂ⁿ := ModelWithCorners.pi fun _ => 𝓡∂ 1`
  (`cubeModel`), a smooth manifold with corners (`instIsManifoldCube`), and the inclusion
  `[0, 1]ⁿ → V` into an open `V ⊇ [0, 1]ⁿ` of `ℝⁿ` is `C^∞` (`contMDiff_cubeToOpens`).
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

section PiManifold

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] {H : ι → Type*} [∀ i, TopologicalSpace (H i)]
  (I : ∀ i, ModelWithCorners ℝ (E i) (H i))
  {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]

/-- The product of maps that are `Cᵐ` in the model coordinates is `Cᵐ` in the coordinates of
`ModelWithCorners.pi I`. -/
theorem contDiffOn_modelPi_conj {m : WithTop ℕ∞} (g : ∀ i, OpenPartialHomeomorph (H i) (H i))
    (hg : ∀ i, ContDiffOn ℝ m ((I i) ∘ g i ∘ (I i).symm)
      ((I i).symm ⁻¹' (g i).source ∩ range (I i))) :
    ContDiffOn ℝ m
      (ModelWithCorners.pi I ∘ OpenPartialHomeomorph.pi g ∘ (ModelWithCorners.pi I).symm)
      ((ModelWithCorners.pi I).symm ⁻¹' (OpenPartialHomeomorph.pi g).source ∩
        range (ModelWithCorners.pi I)) := by
  refine contDiffOn_pi.2 fun i => ?_
  have h : (fun x => (ModelWithCorners.pi I ∘ OpenPartialHomeomorph.pi g ∘
      (ModelWithCorners.pi I).symm) x i) =
      ((I i) ∘ g i ∘ (I i).symm) ∘ fun x : (∀ j, E j) => x i := rfl
  rw [h]
  refine (hg i).comp (ContinuousLinearMap.proj (R := ℝ) (φ := E) i).contDiff.contDiffOn ?_
  rintro x ⟨hx1, y, rfl⟩
  exact ⟨hx1 i trivial, y i, rfl⟩

/-- **A finite product of `Cᵐ` manifolds with corners is a `Cᵐ` manifold with corners** for the
model `ModelWithCorners.pi I`. -/
instance isManifold_modelPi {m : WithTop ℕ∞} [∀ i, IsManifold (I i) m (M i)] :
    IsManifold (ModelWithCorners.pi I) m (∀ i, M i) := by
  have : HasGroupoid (∀ i, M i) (contDiffGroupoid m (ModelWithCorners.pi I)) := by
    refine ⟨fun {e e'} he he' => ?_⟩
    obtain ⟨es, hes, rfl⟩ := he
    obtain ⟨es', hes', rfl⟩ := he'
    have hc : ∀ i, (es i).symm ≫ₕ es' i ∈ contDiffGroupoid m (I i) := fun i =>
      HasGroupoid.compatible (hes i trivial) (hes' i trivial)
    have heq : (OpenPartialHomeomorph.pi es).symm ≫ₕ OpenPartialHomeomorph.pi es' =
        OpenPartialHomeomorph.pi fun i => (es i).symm ≫ₕ es' i :=
      OpenPartialHomeomorph.toPartialEquiv_injective
        (PartialEquiv.pi_trans (fun i => (es i).toPartialEquiv.symm)
          fun i => (es' i).toPartialEquiv)
    have heqs : (OpenPartialHomeomorph.pi fun i => (es i).symm ≫ₕ es' i).symm =
        OpenPartialHomeomorph.pi fun i => ((es i).symm ≫ₕ es' i).symm :=
      OpenPartialHomeomorph.toPartialEquiv_injective (PartialEquiv.pi_symm _)
    rw [heq]
    refine ⟨contDiffOn_modelPi_conj I _ fun i => (hc i).1, ?_⟩
    change ContDiffOn ℝ m (_ ∘ _ ∘ _) (_ ∩ _)
    rw [heqs]
    exact contDiffOn_modelPi_conj I _ fun i => (hc i).2
  exact IsManifold.mk' _ _ _

/-- **The projection `x ↦ x i` of a finite product is `Cᵐ`.** -/
theorem contMDiff_eval_modelPi {m : WithTop ℕ∞} (i : ι) :
    ContMDiff (ModelWithCorners.pi I) (I i) m fun x : (∀ j, M j) => x i := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨(continuous_apply i).continuousAt, ?_⟩
  set p := extChartAt (ModelWithCorners.pi I) x x
  have hp : p i = extChartAt (I i) (x i) (x i) := rfl
  have hT : Tendsto (fun z : (∀ j, E j) => z i) (𝓝[range (ModelWithCorners.pi I)] p)
      (𝓝[range (I i)] (extChartAt (I i) (x i) (x i))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [← hp]
      exact ((continuous_apply i).tendsto p).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      obtain ⟨y, rfl⟩ := hz
      exact ⟨y i, rfl⟩
  have hmem : ∀ᶠ z in 𝓝[range (ModelWithCorners.pi I)] p,
      z i ∈ (extChartAt (I i) (x i)).target :=
    hT (extChartAt_target_mem_nhdsWithin (x i))
  refine ((ContinuousLinearMap.proj (R := ℝ) (φ := E) i).contDiff.contDiffWithinAt
    ).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hmem] with z hz
    exact (extChartAt (I i) (x i)).right_inv hz
  · exact (extChartAt (I i) (x i)).right_inv (mem_extChartAt_target (x i))

end PiManifold

section Cube

/-- **The model with corners of the cube `[0, 1]ⁿ`**: the product of `n` copies of `𝓡∂ 1`. -/
abbrev cubeModel (n : ℕ) :
    ModelWithCorners ℝ (Fin n → EuclideanSpace ℝ (Fin 1)) (ModelPi fun _ : Fin n =>
      EuclideanHalfSpace 1) :=
  ModelWithCorners.pi fun _ : Fin n => 𝓡∂ 1

/-- **The cube `[0, 1]ⁿ` is a smooth manifold with corners** (model `cubeModel n`). -/
instance instIsManifoldCube (n : ℕ) : IsManifold (cubeModel n) ∞ (Fin n → unitInterval) :=
  isManifold_modelPi _

/-- The inclusion `[0, 1]ⁿ → V` into an open `V ⊇ [0, 1]ⁿ` of `ℝⁿ`. -/
def cubeToOpens {n : ℕ} (V : TopologicalSpace.Opens (Fin n → ℝ))
    (hV : Icc (0 : Fin n → ℝ) 1 ⊆ V) (t : Fin n → unitInterval) : V :=
  ⟨fun i => (t i : ℝ), hV ⟨fun i => (t i).2.1, fun i => (t i).2.2⟩⟩

/-- **The inclusion `[0, 1]ⁿ → V` is `C^∞`** from the manifold with corners `[0, 1]ⁿ` to the
open subset `V` of `ℝⁿ`. -/
theorem contMDiff_cubeToOpens {n : ℕ} (V : TopologicalSpace.Opens (Fin n → ℝ))
    (hV : Icc (0 : Fin n → ℝ) 1 ⊆ V) :
    ContMDiff (cubeModel n) 𝓘(ℝ, Fin n → ℝ) ∞ (cubeToOpens V hV) := by
  refine (ContMDiff.subtypeVal_comp_iff V _).1 ?_
  refine contMDiff_pi_space.2 fun i => ?_
  have h1 : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ fun z : Icc (0 : ℝ) 1 => (z : ℝ) := contMDiff_subtypeVal_Icc
  exact h1.comp (contMDiff_eval_modelPi (fun _ : Fin n => 𝓡∂ 1) (M := fun _ => unitInterval) i)

end Cube

end Polyfold
