import Polyfold.Chapter5.PartitionsOfUnity
import Polyfold.Chapter6.CubeSections
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): Definition 5.5.1 for the
product `[0, 1]ⁿ × X`.  Used in the proof of Corollary 15.3.10 (3) (p. 699), which applies
Theorem 15.3.9 on `[0, 1] × X` (gap TY-3).

# Sc-smooth partitions of unity on `[0, 1]ⁿ × X`

## The text, paraphrased

The proof of Corollary 15.3.10 (3) applies Theorem 15.3.9 to `[0, 1] × X`; that theorem asks for
sc-smooth partitions of unity on the M-polyfold of objects.  The text does not say why
`[0, 1] × X` has them.

## What is formalized (namespace `Polyfold`)

* `admitsScPartitionsOfUnity_of_urysohn`: an M-polyfold in which any two disjoint closed sets are
  separated by an sc-smooth function with values in `[0, 1]` admits sc-smooth partitions of unity
  (the second half of the proof of Theorem 5.5.10, Mathlib's
  `BumpCovering.exists_isSubordinate_of_prop`).
* `exists_cubeProd_urysohn_w5`: if `X` admits sc-smooth partitions of unity, two disjoint closed
  sets of `[0, 1]ⁿ × X` are separated by an sc-smooth function.  The construction: for each
  `x ∈ X` a smooth `gₓ : ℝⁿ → [0, 1]` that is `0` near the compact slice of `s` over `x` and `1`
  near that of `t`; by the tube lemma it separates `s` and `t` over an open `Vₓ ∋ x`; with an
  sc-smooth partition of unity `(ρₓ)` of `X` subordinate to `(Vₓ)`,
  `F(q, y) = Σₓ ρₓ(y) gₓ(q)`.
* **`admitsScPartitionsOfUnity_cubeProd`**: `[0, 1]ⁿ × X` admits sc-smooth partitions of unity if
  `X` does.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

universe u

section Urysohn

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **Partitions of unity from sc-smooth Urysohn functions** (the second half of the proof of
Theorem 5.5.10, p. 159 (preprint Theorem 5.37)): if any two disjoint closed subsets of `X` are
separated by an sc-smooth function with values in `[0, 1]`, then `X` admits sc-smooth partitions
of unity (`ρᵢ = fᵢ ∏_{j < i} (1 − f_j)` for a subordinate bump covering by sc-smooth `fᵢ`). -/
theorem admitsScPartitionsOfUnity_of_urysohn
    (h : ∀ s t : Set X, IsClosed s → IsClosed t → Disjoint s t → ∃ F : X → ℝ,
      PX.IsScSmoothMap realPolyfold F ∧ EqOn F 0 s ∧ EqOn F 1 t ∧ ∀ x, F x ∈ Icc (0 : ℝ) 1) :
    PX.AdmitsScPartitionsOfUnity := by
  classical
  intro ι V hVo hVcov
  obtain ⟨b, hbp, hb⟩ := BumpCovering.exists_isSubordinate_of_prop
    (fun g : X → ℝ => PX.IsScSmoothMap realPolyfold g) (fun s t hs ht hst => by
      obtain ⟨F, hF, hF0, hF1, hF01⟩ := h s t hs ht hst
      exact ⟨⟨F, continuousOn_univ.1 hF.continuousOn⟩, hF, hF0, hF1, hF01⟩)
    isClosed_univ V hVo (by rw [hVcov])
  refine ⟨b.toPartitionOfUnity, hb.toPartitionOfUnity, fun i => ?_⟩
  refine isScSmoothMap_real_of_eventuallyEq fun x => ?_
  obtain ⟨T, hT⟩ := b.exists_finset_toPartitionOfUnity_eventuallyEq i x
  refine ⟨_, ?_, hT⟩
  have h1 : (⇑(b i) * ⇑(∏ j ∈ T with WellOrderingRel j i, (1 - b j))) =
      fun y => b i y * ∏ j ∈ T with WellOrderingRel j i, (1 - b j y) := by
    funext y
    simp [ContinuousMap.coe_prod, Finset.prod_apply]
  rw [h1]
  exact (hbp i).real_mul (isScSmoothMap_real_finsetProd _ fun j _ =>
    (isScSmoothMap_real_const 1).real_sub (hbp j))

end Urysohn

section Cube

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {n : ℕ}

/-- The coordinates `[0, 1]ⁿ → ℝⁿ`. -/
private def cubeCoord (q : Fin n → unitInterval) : Fin n → ℝ := fun i => (q i : ℝ)

private theorem continuous_cubeCoord : Continuous (cubeCoord (n := n)) :=
  continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)

private theorem injective_cubeCoord : Injective (cubeCoord (n := n)) := fun _ _ h =>
  funext fun i => Subtype.ext (congrFun h i)

/-- **The local step**: over a neighbourhood `V` of `x` a single smooth function of the cube
coordinates separates `s` and `t` (the smooth Urysohn lemma on `ℝⁿ` for the compact slices over
`x`, and the tube lemma). -/
private theorem exists_local_separation {s t : Set ((Fin n → unitInterval) × X)}
    (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) (x : X) :
    ∃ (g : (Fin n → ℝ) → ℝ) (V : Set X), ContDiff ℝ ∞ g ∧ (∀ v, g v ∈ Icc (0 : ℝ) 1) ∧
      IsOpen V ∧ x ∈ V ∧ (∀ q y, y ∈ V → (q, y) ∈ s → g (cubeCoord q) = 0) ∧
      (∀ q y, y ∈ V → (q, y) ∈ t → g (cubeCoord q) = 1) := by
  set S : Set (Fin n → unitInterval) := {q | (q, x) ∈ s}
  set T : Set (Fin n → unitInterval) := {q | (q, x) ∈ t}
  have hcx : Continuous fun q : Fin n → unitInterval => (q, x) :=
    continuous_id.prodMk continuous_const
  have hS : IsClosed S := hs.preimage hcx
  have hT : IsClosed T := ht.preimage hcx
  have hSc : IsCompact (cubeCoord '' S) := hS.isCompact.image continuous_cubeCoord
  have hTc : IsCompact (cubeCoord '' T) := hT.isCompact.image continuous_cubeCoord
  have hST : Disjoint (cubeCoord '' S) (cubeCoord '' T) := by
    rw [disjoint_image_iff injective_cubeCoord]
    exact Set.disjoint_left.2 fun q hq hq' => Set.disjoint_left.1 hst hq hq'
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, Fin n → ℝ) (n := (⊤ : ℕ∞)) hSc.isClosed hTc.isClosed hST
  obtain ⟨OS, hOSo, hSOS, hOS0⟩ := mem_nhdsSet_iff_exists.1 hf0
  obtain ⟨OT, hOTo, hTOT, hOT1⟩ := mem_nhdsSet_iff_exists.1 hf1
  -- the tube lemma for the compact sets of cube points not mapped into `OS`, `OT`
  have hKS : IsCompact (cubeCoord ⁻¹' OS)ᶜ :=
    ((hOSo.preimage continuous_cubeCoord).isClosed_compl).isCompact
  have hKT : IsCompact (cubeCoord ⁻¹' OT)ᶜ :=
    ((hOTo.preimage continuous_cubeCoord).isClosed_compl).isCompact
  obtain ⟨uS, VS, -, hVSo, hKSu, hxVS, hVS⟩ := generalized_tube_lemma hKS isCompact_singleton
    hs.isOpen_compl (by
      rintro ⟨q, y⟩ ⟨hq, rfl⟩ hqs
      exact hq (hSOS (mem_image_of_mem _ hqs)))
  obtain ⟨uT, VT, -, hVTo, hKTu, hxVT, hVT⟩ := generalized_tube_lemma hKT isCompact_singleton
    ht.isOpen_compl (by
      rintro ⟨q, y⟩ ⟨hq, rfl⟩ hqt
      exact hq (hTOT (mem_image_of_mem _ hqt)))
  refine ⟨f, VS ∩ VT, contMDiff_iff_contDiff.1 f.contMDiff, hf01, hVSo.inter hVTo,
    ⟨hxVS rfl, hxVT rfl⟩, fun q y hy hqy => ?_, fun q y hy hqy => ?_⟩
  · by_contra hne
    have hq : q ∈ (cubeCoord ⁻¹' OS)ᶜ := fun h => hne (hOS0 h)
    exact hVS ⟨hKSu hq, hy.1⟩ hqy
  · by_contra hne
    have hq : q ∈ (cubeCoord ⁻¹' OT)ᶜ := fun h => hne (hOT1 h)
    exact hVT ⟨hKTu hq, hy.2⟩ hqy

variable [ParacompactSpace ((Fin n → unitInterval) × X)]

/-- **Sc-smooth Urysohn functions on `[0, 1]ⁿ × X`**: if `X` admits sc-smooth partitions of
unity, any two disjoint closed subsets of `[0, 1]ⁿ × X` are separated by an sc-smooth function
with values in `[0, 1]`, namely `F(q, y) = Σₓ ρₓ(y) gₓ(q)`. -/
theorem exists_cubeProd_urysohn_w5 (hPU : PX.AdmitsScPartitionsOfUnity)
    {s t : Set ((Fin n → unitInterval) × X)} (hs : IsClosed s) (ht : IsClosed t)
    (hst : Disjoint s t) :
    ∃ F : (Fin n → unitInterval) × X → ℝ,
      ((cubePolyfold n).prod PX).IsScSmoothMap realPolyfold F ∧ EqOn F 0 s ∧ EqOn F 1 t ∧
        ∀ p, F p ∈ Icc (0 : ℝ) 1 := by
  choose g V hg hg01 hVo hxV hgs hgt using exists_local_separation hs ht hst
  obtain ⟨ρ, hρsub, hρsc⟩ := hPU X V hVo (iUnion_eq_univ_iff.2 fun x => ⟨x, hxV x⟩)
  refine ⟨fun p => ∑ᶠ x, ρ x p.2 * g x (cubeCoord p.1), ?_, fun p hp => ?_, fun p hp => ?_,
    fun p => Polyfold.PartitionOfUnity.finsum_mul_mem_Icc ρ _ (fun x => hg01 x _) p.2⟩
  · refine isScSmoothMap_real_finsum (fun x => ?_) ?_
    · exact ((hρsc x).comp (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).real_mul
        ((UnitCube.isScSmoothMap_cube_real_of_contDiff (hg x)).comp
          (MPolyfold.isScSmoothMap_fst (cubePolyfold n) PX))
    · exact (ρ.locallyFinite.preimage_continuous continuous_snd).subset fun x p hp =>
        support_mul_subset_left _ _ hp
  · refine finsum_eq_zero_of_forall_eq_zero fun x => ?_
    by_cases h : ρ x p.2 = 0
    · rw [h, zero_mul]
    · rw [hgs x p.1 p.2 (hρsub x (subset_tsupport _ h)) hp, mul_zero]
  · have e : ∀ x, ρ x p.2 * g x (cubeCoord p.1) = ρ x p.2 := fun x => by
      by_cases h : ρ x p.2 = 0
      · rw [h, zero_mul]
      · rw [hgt x p.1 p.2 (hρsub x (subset_tsupport _ h)) hp, mul_one]
    change ∑ᶠ x, ρ x p.2 * g x (cubeCoord p.1) = 1
    simp only [e]
    exact ρ.sum_eq_one (mem_univ _)

/-- **`[0, 1]ⁿ × X` admits sc-smooth partitions of unity if `X` does** (Definition 5.5.1, for
the product M-polyfold of Part I's cube `[0, 1]ⁿ` with `X`). -/
theorem admitsScPartitionsOfUnity_cubeProd (hPU : PX.AdmitsScPartitionsOfUnity) :
    ((cubePolyfold n).prod PX).AdmitsScPartitionsOfUnity :=
  admitsScPartitionsOfUnity_of_urysohn fun _ _ hs ht hst =>
    exists_cubeProd_urysohn_w5 hPU hs ht hst

end Cube

end Polyfold
