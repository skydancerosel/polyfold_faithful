import Polyfold.Chapter2.SubMPolyfoldTangent
import Polyfold.Chapter2.ReducedTangentIntrinsic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.3, Proposition 2.3.19
(3), p. 42 (preprint: Proposition 2.21 (3), p. 30): at a smooth `a ∈ A`, `T_aA` has an
**sc**-complement in `T_aX`.

# The sc-complement of `T_aA` in `T_aX`

## The text, paraphrased

(2021 Proposition 2.3.19 (3), p. 42) The tangent space `T_aA` of a sub-M-polyfold `A ⊆ X` at a
smooth point `a ∈ A` has an sc-complement in `T_aX`.  (Proof, p. 43) In a chart, with `ρ = φ∘r∘φ⁻¹`
and `t = ρ ∘ r`, `T_aA = Dt(a)E` and `T_aO = Dr(a)E = Dt(a)E ⊕ (Dr(a) − Dt(a))E`, both summands
being images of sc-projections, hence sc-subspaces.

## What is formalized (rows V2.25 and V7.30; completes `SubMPolyfoldTangent.lean`)

`SubMPolyfoldTangent.lean` gives the topological direct sum `T_aX = Ti(T_aA) ⊕ ker T(i⁻¹ ∘ r)`
(`proposition_2_3_19_3_linear_2021`).  Added here, for a smooth `a` and a chart `φ` around `a`:

* **`MPolyfold.proposition_2_3_19_3_sc_2021`**: the images `K`, `N ⊆ E` of `Ti(T_aA)` and of
  `ker T(i⁻¹ ∘ r)` under `Tφ(a) : T_aX → T_{φ(a)}O ⊆ E` are **sc-subspaces of `E`**, and on every
  level `m` they are complementary in `T_{φ(a)}O ∩ E_m`: `K_m ⊓ N_m = 0` and
  `K_m ⊔ N_m = (T_{φ(a)}O)_m`.  In the sc-Banach structure of `T_aX` (the sc-subspace
  `T_{φ(a)}O ⊆ E`, `isScSubspace_tangentFiberModel`), this is the sc-splitting
  `T_aX = T_aA ⊕ N`: `T_aA` has the sc-complement `ker T(i⁻¹ ∘ r)`.

## What the text leaves implicit, and the choices made

* The text's `Dt(a)` is the chart representative of the projection `Ti ∘ T(i⁻¹ ∘ r) = Tr(a)` of
  `T_aX` (an sc-operator at the smooth point `a`, `exists_clm_tangentMapOnFiber`).  Its
  idempotent extension to all of `E` is `L ∘ Dr(a)` (the text's `Dt(a) = D(ρ ∘ r)(a)`), and the
  complement is the range of the idempotent sc-operator `Dr(a) − L ∘ Dr(a)`; both ranges are
  sc-subspaces by `ScBanach.isScSplitting_of_idem` (Lemma 2.B (ii) of Chapter 1's exposition).
* The sc-complement is described in the chart, since the sc-structure of `T_aX` is carried by the
  chart model (`TangentSpaceLinear.lean`); the sets themselves (`Ti(T_aA)`, `ker T(i⁻¹ ∘ r)`) are
  intrinsic.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {A : Set X} (hA : P.IsSubMPolyfold A) [ParacompactSpace A]
variable {a : (subPolyfold hA).Level 1} {x : P.Level 1}
  (hax : ((subPolyfold hA).levelVal 1 a : A).1 = P.levelVal 1 x)
variable (d : P.SubData A) (a₀ : A) (hxV : P.levelVal 1 x ∈ d.V)
variable {φ : MChart X} (hφ : P.IsChart φ) (hxφ : P.levelVal 1 x ∈ φ.source)

include hax hxV in
lemma SubData.r_levelVal_eq : d.r (P.levelVal 1 x) = P.levelVal 1 x :=
  d.apply_eq_self ⟨levelVal_mem_of_sub hA hax, hxV⟩

/-- `Ti ∘ T(i⁻¹ ∘ r) = Tr(a)` as continuous linear maps `T_aX → T_aX`. -/
theorem subInclusionCLM_comp_subRetractionCLM_eq :
    (subInclusionCLM hA hax).comp (subRetractionCLM hA hax d a₀ hxV) =
      tangentMapOnCLM d.isScSmoothOn hxV (SubData.r_levelVal_eq hA hax d hxV) := by
  ext α
  rw [ContinuousLinearMap.comp_apply, subInclusionCLM_subRetractionCLM_apply, tangentMapOnCLM_apply]

/-- **Proposition 2.3.19 (3) (2021 p. 42; preprint 2.21 (3)), the sc-complement**: at a smooth
`a ∈ A`, in a chart `φ` around `a`, the images under `Tφ(a)` of `Ti(T_aA)` and of
`ker T(i⁻¹ ∘ r)` are sc-subspaces `K`, `N` of `E`, complementary on every level inside
`T_{φ(a)}O`: `T_aA` has the sc-complement `ker T(i⁻¹ ∘ r)` in `T_aX`. -/
theorem proposition_2_3_19_3_sc_2021 (hs : P.levelVal 1 x ∈ P.smoothSet) :
    ∃ K N : Submodule ℝ (φ.model.E 0),
      K = (LinearMap.range (subInclusionCLM hA hax :
          (subPolyfold hA).tangentFiber a →ₗ[ℝ] P.tangentFiber x)).map (fiberCoord hφ hxφ) ∧
      N = (LinearMap.ker (subRetractionCLM hA hax d a₀ hxV :
          P.tangentFiber x →ₗ[ℝ] (subPolyfold hA).tangentFiber a)).map (fiberCoord hφ hxφ) ∧
      φ.model.E.IsScSubspace K ∧ φ.model.E.IsScSubspace N ∧
      (∀ m, Disjoint (φ.model.E.levelSub K m) (φ.model.E.levelSub N m)) ∧
      (∀ m, φ.model.E.levelSub K m ⊔ φ.model.E.levelSub N m =
        φ.model.E.levelSub (tangentFiberModel hφ hxφ) m) := by
  set E := φ.model.E
  set Ti := subInclusionCLM hA hax
  set Tr := subRetractionCLM hA hax d a₀ hxV
  set M := tangentFiberModel hφ hxφ with hMdef
  -- the projection `Tr(a) = Ti ∘ T(i⁻¹ ∘ r)` and its chart representative `L`
  set Pr := tangentMapOnCLM d.isScSmoothOn hxV (SubData.r_levelVal_eq hA hax d hxV)
  have hPr : ∀ α, Ti (Tr α) = Pr α := fun α => by
    rw [← ContinuousLinearMap.comp_apply, subInclusionCLM_comp_subRetractionCLM_eq]
  obtain ⟨L, hL, hLs⟩ := exists_clm_tangentMapOnFiber d.isScSmoothOn hxV
    (SubData.r_levelVal_eq hA hax d hxV) hφ hφ hxφ hxφ
  have hL' : ∀ α : P.tangentFiber x, fiberCoord hφ hxφ (Pr α) = L (fiberCoord hφ hxφ α) := by
    intro α
    rw [fiberCoord_eq_coe, fiberCoord_eq_coe, ← hL, tangentMapOnCLM_eq]
  have hLop : IsScOperator L := hLs hs
  -- the retraction and `Dr(a)`
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  set av := levelLift φ 1 (P.levelVal 1 x)
  have haR : av ∈ E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR]; exact levelLift_mem_lvlSet_one hφ hxφ
  have haU : av ∈ E.lvlSet R.U 1 := R.lvlSet_retract_subset 1 haR
  have has : av ∈ E.smoothLvl 1 := (mem_smoothSet_iff_levelLift_mem_smoothLvl hφ hxφ).1 hs
  set D := scDeriv R.U R av
  have hDop : IsScOperator D := R.isSc1.isSc1With_scDeriv.scOperator_deriv haU has
  have hMiff : ∀ w, w ∈ M ↔ w ∈ range D := fun w => by
    rw [hMdef, mem_tangentFiberModel, ← hR, retractTangent_eq, R.mem_tangent_iff_mem_range haR]
  have hDM : ∀ w, D w ∈ M := fun w => (hMiff _).2 ⟨w, rfl⟩
  have hMD : ∀ w ∈ M, D w = w := fun w hw =>
    R.scDeriv_apply_eq_self_of_mem_range haR ((hMiff w).1 hw)
  have hcoordM : ∀ α, fiberCoord hφ hxφ α ∈ M := fun α => by
    rw [fiberCoord_eq_coe]; exact (tangentFiberEquiv hφ hxφ α).2
  -- `L` preserves `M` and is idempotent on `M`
  have hcoord_symm : ∀ (w : E 0) (hw : w ∈ M),
      fiberCoord hφ hxφ ((tangentFiberEquiv hφ hxφ).symm ⟨w, hw⟩) = w := fun w hw => by
    rw [fiberCoord_eq_coe, Equiv.apply_symm_apply]
  have hLM : ∀ w ∈ M, L w ∈ M := fun w hw => by
    have := hL' ((tangentFiberEquiv hφ hxφ).symm ⟨w, hw⟩)
    rw [hcoord_symm] at this
    rw [← this]; exact hcoordM _
  have hPrPr : ∀ α, Pr (Pr α) = Pr α := fun α => by
    rw [← hPr, ← hPr, subRetractionCLM_subInclusionCLM]
  have hLL : ∀ w ∈ M, L (L w) = L w := fun w hw => by
    have h1 := hL' ((tangentFiberEquiv hφ hxφ).symm ⟨w, hw⟩)
    rw [hcoord_symm] at h1
    have h2 := hL' (Pr ((tangentFiberEquiv hφ hxφ).symm ⟨w, hw⟩))
    rw [hPrPr, h1] at h2
    exact h2.symm
  -- the idempotent sc-operators `A' = L ∘ D` and `B' = D − L ∘ D`
  set A' := L.comp D
  set B' := D - A'
  have hA'apply : ∀ v, A' v = L (D v) := fun _ => rfl
  have hB'apply : ∀ v, B' v = D v - L (D v) := fun _ => rfl
  have hA'M : ∀ v, A' v ∈ M := fun v => hLM _ (hDM v)
  have hDD : ∀ v, D (D v) = D v := fun v => hMD _ (hDM v)
  have hDLD : ∀ v, D (L (D v)) = L (D v) := fun v => hMD _ (hA'M v)
  have hLLD : ∀ v, L (L (D v)) = L (D v) := fun v => hLL _ (hDM v)
  have hA'A' : ∀ v, A' (A' v) = A' v := fun v => by
    change L (D (L (D v))) = L (D v)
    rw [hDLD, hLLD]
  have hB'B' : ∀ v, B' (B' v) = B' v := fun v => by
    change D (D v - L (D v)) - L (D (D v - L (D v))) = D v - L (D v)
    rw [map_sub D, hDD, hDLD, map_sub L, hLLD, sub_self, sub_zero]
  have hA'op : IsScOperator A' := fun m => by
    obtain ⟨Lm, hLm⟩ := hLop m
    obtain ⟨Dm, hDm⟩ := hDop m
    exact ⟨Lm.comp Dm, fun z => by rw [ContinuousLinearMap.comp_apply, hLm, hDm]; rfl⟩
  have hB'op : IsScOperator B' := fun m => by
    obtain ⟨Dm, hDm⟩ := hDop m
    obtain ⟨Am, hAm⟩ := hA'op m
    exact ⟨Dm - Am, fun z => by
      rw [show (Dm - Am) z = Dm z - Am z from rfl, map_sub, hDm, hAm]; rfl⟩
  have hKsc : E.IsScSubspace (LinearMap.range (A' : E 0 →ₗ[ℝ] E 0)) := by
    have h := ScBanach.isScSplitting_of_idem hA'op.toScOperator (by
      rw [hA'op.toScOperator_zero]; exact hA'A')
    rw [hA'op.toScOperator_zero] at h
    exact h.1
  have hNsc : E.IsScSubspace (LinearMap.range (B' : E 0 →ₗ[ℝ] E 0)) := by
    have h := ScBanach.isScSplitting_of_idem hB'op.toScOperator (by
      rw [hB'op.toScOperator_zero]; exact hB'B')
    rw [hB'op.toScOperator_zero] at h
    exact h.1
  -- `L A' = A'`, `L B' = 0`
  have hLA' : ∀ v, L (A' v) = A' v := fun v => by
    change L (L (D v)) = L (D v); exact hLLD v
  have hLB' : ∀ v, L (B' v) = 0 := fun v => by
    change L (D v - L (D v)) = 0
    rw [map_sub, hLLD, sub_self]
  refine ⟨LinearMap.range (A' : E 0 →ₗ[ℝ] E 0), LinearMap.range (B' : E 0 →ₗ[ℝ] E 0),
    ?_, ?_, hKsc, hNsc, fun m => ?_, fun m => ?_⟩
  · -- `K = Tφ(a)(Ti(T_aA))`
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      refine ⟨Pr ((tangentFiberEquiv hφ hxφ).symm ⟨D u, hDM u⟩),
        ⟨Tr ((tangentFiberEquiv hφ hxφ).symm ⟨D u, hDM u⟩), hPr _⟩, ?_⟩
      rw [hL', hcoord_symm]; rfl
    · rintro _ ⟨_, ⟨β, rfl⟩, rfl⟩
      refine ⟨fiberCoord hφ hxφ (Ti β), ?_⟩
      change A' (fiberCoord hφ hxφ (Ti β)) = fiberCoord hφ hxφ (Ti β)
      rw [hA'apply, hMD _ (hcoordM _), ← hL', ← hPr, subRetractionCLM_subInclusionCLM]
  · -- `N = Tφ(a)(ker T(i⁻¹ ∘ r))`
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      set α := (tangentFiberEquiv hφ hxφ).symm ⟨D u, hDM u⟩ with hα
      have hcα : fiberCoord hφ hxφ α = D u := hcoord_symm _ _
      refine ⟨α - Pr α, ?_, ?_⟩
      · change Tr (α - Pr α) = 0
        rw [map_sub, ← hPr, subRetractionCLM_subInclusionCLM, sub_self]
      · rw [map_sub, hL', hcα]; rfl
    · rintro _ ⟨α, hα, rfl⟩
      have hPrα : Pr α = 0 := by
        rw [← hPr, show Tr α = 0 from hα, map_zero]
      refine ⟨fiberCoord hφ hxφ α, ?_⟩
      change B' (fiberCoord hφ hxφ α) = fiberCoord hφ hxφ α
      rw [hB'apply, hMD _ (hcoordM α), ← hL', hPrα, map_zero, sub_zero]
  · -- disjoint on level `m`
    rw [Submodule.disjoint_def]
    intro z hzK hzN
    obtain ⟨u, hu⟩ := hzK
    obtain ⟨v, hv⟩ := hzN
    apply E.toBase_injective m
    rw [map_zero]
    have h1 : A' u = E.toBase m z := hu
    have h2 : B' v = E.toBase m z := hv
    rw [← h1, ← hLA' u, h1, ← h2, hLB']
  · -- sum on level `m`
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro z ⟨u, hu⟩
        change E.toBase m z ∈ M
        rw [← show A' u = E.toBase m z from hu]; exact hA'M u
      · rintro z ⟨v, hv⟩
        change E.toBase m z ∈ M
        rw [← show B' v = E.toBase m z from hv, hB'apply]
        exact M.sub_mem (hDM v) (hA'M v)
    · intro z hz
      change E.toBase m z ∈ M at hz
      obtain ⟨Am, hAm⟩ := hA'op m
      obtain ⟨Bm, hBm⟩ := hB'op m
      refine Submodule.mem_sup.2 ⟨Am z, ⟨E.toBase m z, (hAm z).symm⟩, Bm z,
        ⟨E.toBase m z, (hBm z).symm⟩, ?_⟩
      apply E.toBase_injective m
      rw [map_add, hAm, hBm, hB'apply, hA'apply, add_sub_cancel, hMD _ hz]

end MPolyfold

end Polyfold
