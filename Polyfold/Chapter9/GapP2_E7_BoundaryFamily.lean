import Polyfold.Chapter9.GapP2_E7_FamilyMeasure
import Polyfold.Chapter9.GapP2_E6_BoundarySheets
import Polyfold.Chapter11.BoundaryOrientationEquiv

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.3, Definition 9.3.10 (p. 427) and §9.5, **Theorems 9.5.15, 9.5.16**
(p. 449; 2017: Theorems 9.4, 9.5).  Numbers and pages are the 2021 text's.

# The boundary sheets of an oriented tame structure as an oriented sheet family

The local expression of Theorem 9.5.15 integrates over the boundary sheets
`∂₁Mᵢ = {d_{Mᵢ} = 1}` with the orientations `o_{∂Mᵢ}` (E6, `GapP2_E6_BoundarySheets.lean`).  To
apply the machinery of `GapP2_E7_SheetFamily.lean` they must form an `OrientedSheetFamily`, i.e.
their union must be `D ∩ U(x)` for one saturated set `D` that does not depend on the structure,
and `T̂_{∂Θ}` must be natural.

* `reducedCodimPart_natural`: the reduced-codimension-one part of `T̂Θ` is carried along by the
  sc-diffeomorphisms whose tangent maps are those of morphisms (`Tf` preserves the reduced
  codimension, Chapter 11's `hasReducedCodim_map_tangentMapOn_iff`).
* **`isNaturalOn_boundaryOrientation`**: `T̂_{∂Θ} = boundaryOrientation T̂Θ` is natural
  (`Tf` moves the boundary operation, `boundaryOp_map_tangentMapOn`).
* `boundaryStratumSet Θ T = {y ∈ supp Θ | T̂Θ(y) has a term of reduced codimension 1}` and
  **`isMorSaturated_boundaryStratumSet`**.
* `OrientedTameStructure.mem_boundaryStratumSet_iff`: for a structure describing `T̂Θ`, a point
  of `U(x)` lies in `boundaryStratumSet` iff it lies on some `∂₁Mᵢ` (the weights are positive, so
  the terms of `∑ σᵢ T_y(Mᵢ, oᵢ)` do not cancel).
* **`OrientedTameStructure.boundaryFamily`**: the family `(∂₁Mᵢ, o_{∂Mᵢ})`, `(σᵢ)` on `U(x)`, and
  `represents_boundaryFamily`: it describes `T̂_{∂Θ}` ((9.12)).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

open scoped Classical in
theorem finsupp_filter_mapDomain_of_iff {α β : Type*} {p : α → β} {P : β → Prop}
    {Q : α → Prop} (w : α →₀ ℚ) (h : ∀ g ∈ w.support, P (p g) ↔ Q g) :
    (w.mapDomain p).filter P = (w.filter Q).mapDomain p := by
  classical
  have e1 : w.mapDomain p = ∑ g ∈ w.support, Finsupp.single (p g) (w g) := rfl
  have e2 : w.filter Q = ∑ g ∈ w.support, (Finsupp.single g (w g)).filter Q := by
    conv_lhs => rw [← Finsupp.sum_single w]
    rw [Finsupp.sum, Finsupp.filter_sum]
  rw [e1, e2, Finsupp.filter_sum, Finsupp.mapDomain_finsetSum]
  refine Finset.sum_congr rfl fun g hg => ?_
  by_cases hq : Q g
  · rw [Finsupp.filter_single_of_pos _ ((h g hg).2 hq), Finsupp.filter_single_of_pos _ hq,
      Finsupp.mapDomain_single]
  · rw [Finsupp.filter_single_of_neg _ (fun hp => hq ((h g hg).1 hp)),
      Finsupp.filter_single_of_neg _ hq, Finsupp.mapDomain_zero]

theorem finsupp_sum_single_ne_zero {ι β : Type*} [DecidableEq β] {s : Finset ι} (hs : s.Nonempty)
    (g : ι → β) {σ : ι → ℚ} (hσ : ∀ i, 0 < σ i) :
    ∑ i ∈ s, Finsupp.single (g i) (σ i) ≠ 0 := by
  obtain ⟨i₀, hi₀⟩ := hs
  intro h0
  have h1 := congrArg (fun w : β →₀ ℚ => w (g i₀)) h0
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finsupp.coe_zero,
    Pi.zero_apply] at h1
  have h2 : σ i₀ ≤ ∑ i ∈ s, (if g i = g i₀ then σ i else 0) := by
    have := Finset.single_le_sum (f := fun i => if g i = g i₀ then σ i else 0)
      (fun i _ => by split_ifs; exacts [(hσ i).le, le_rfl]) hi₀
    simpa using this
  linarith [hσ i₀]

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}

/-! ### Naturality of the boundary part -/

open scoped Classical in
/-- **The reduced-codimension-one part of `T̂Θ` is natural**: for an sc-diffeomorphism `f`
given by morphisms and `a ∈ supp Θ`, the part of `T̂Θ(f a)` of reduced codimension `ℓ` is the
image under `Tf` of that of `T̂Θ(a)`. -/
theorem reducedCodimPart_natural (hΘ : X.IsBranchedEpSubgroupoid Θ) (hT : X.IsOrientation Θ T)
    {f f' : Obj → Obj} {U U' : Set Obj} (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U')
    (hmor : X.IsMorTangentOn hf U) {a : Obj} (ha : a ∈ supp Θ) (haU : a ∈ U) (ℓ : ℕ) :
    X.reducedCodimPart (f a) ℓ (T (f a)) =
      (X.reducedCodimPart a ℓ (T a)).mapDomain
        (OrTangent.map (tangentMapOn hf.isScSmoothOn)) := by
  have hsm : a ∈ X.PObj.smoothSet := hΘ.support_subset ha
  rw [reducedCodimPart, reducedCodimPart, isNaturalOn_of_isOrientation hΘ hT hf hmor a ha haU]
  exact finsupp_filter_mapDomain_of_iff _ fun g hg =>
    hasReducedCodim_map_tangentMapOn_iff hf haU ((hT.mem a hsm).2 g hg).1

/-- **`T̂_{∂Θ}` is natural** on every `D ⊆ supp Θ`: `T̂_{∂Θ}(f a) = Tf_* T̂_{∂Θ}(a)`. -/
theorem isNaturalOn_boundaryOrientation (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hT : X.IsOrientation Θ T) {D : Set Obj} (hD : D ⊆ supp Θ) :
    X.IsNaturalOn (X.boundaryOrientation T) D := by
  classical
  intro f f' U U' hf hmor a ha haU
  have hsm : a ∈ X.PObj.smoothSet := hΘ.support_subset (hD ha)
  rw [boundaryOrientation, boundaryOrientation, reducedCodimPart_natural hΘ hT hf hmor (hD ha) haU,
    ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr fun g hg => ?_
  have hg' : g ∈ (T a).support := by
    rw [reducedCodimPart, Finsupp.support_filter] at hg
    exact (Finset.mem_filter.1 hg).1
  exact boundaryOp_map_tangentMapOn hf haU ((hT.mem a hsm).2 g hg')

/-! ### The intrinsic stratum set -/

variable (X) in
/-- **The points of `supp Θ` where `T̂Θ` has a term of reduced codimension `1`**: for every
oriented tame structure describing `T̂Θ`, the union of the boundary sheets `∂₁Mᵢ` in `U(x)`
(`OrientedTameStructure.mem_boundaryStratumSet_iff`). -/
def boundaryStratumSet (Θ : Obj → ℚ) (T : Obj → X.PObj.OrTangent →₀ ℚ) : Set Obj :=
  {y | y ∈ supp Θ ∧ X.reducedCodimPart y 1 (T y) ≠ 0}

theorem boundaryStratumSet_subset_supp : X.boundaryStratumSet Θ T ⊆ supp Θ := fun _ h => h.1

theorem mem_boundaryStratumSet_tgt (hΘ : X.IsBranchedEpSubgroupoid Θ) (hT : X.IsOrientation Θ T)
    (φ : Mor) (h : X.src φ ∈ X.boundaryStratumSet Θ T) :
    X.tgt φ ∈ X.boundaryStratumSet Θ T := by
  have hsupp := isMorSaturated_supp hΘ.isFunctorial
  refine ⟨(hsupp φ).1 h.1, fun h0 => h.2 ?_⟩
  -- the inverse morphism carries the part at `t(φ)` to the part at `s(φ)`
  set ψ := X.inv φ
  have hψs : X.src ψ = X.tgt φ := X.src_inv φ
  have hψt : X.tgt ψ = X.src φ := X.tgt_inv φ
  have hs : X.src ψ ∈ supp Θ := hψs ▸ (hsupp φ).1 h.1
  have e := reducedCodimPart_natural hΘ hT (X.isScDiffeoOn_hat ψ) (X.isMorTangentOn_hat ψ) hs
    (X.src_mem_sheetAt ψ) 1
  rw [X.hat_src, hψt, hψs, h0, Finsupp.mapDomain_zero] at e
  exact e

/-- **The stratum set is saturated.** -/
theorem isMorSaturated_boundaryStratumSet (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hT : X.IsOrientation Θ T) : X.IsMorSaturated (X.boundaryStratumSet Θ T) := fun φ =>
  ⟨mem_boundaryStratumSet_tgt hΘ hT φ, fun h => by
    have := mem_boundaryStratumSet_tgt hΘ hT (X.inv φ) (by rw [X.src_inv]; exact h)
    rwa [X.tgt_inv] at this⟩

theorem isNaturalOn_boundaryStratumSet (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hT : X.IsOrientation Θ T) :
    X.IsNaturalOn (X.boundaryOrientation T) (X.boundaryStratumSet Θ T) :=
  isNaturalOn_boundaryOrientation hΘ hT boundaryStratumSet_subset_supp

/-! ### The boundary family of an oriented tame structure -/

namespace OrientedTameStructure

variable {m : ℕ} {x : Obj} (C : X.OrientedTameStructure (m + 1) Θ x)

open scoped Classical in
theorem reducedCodimPart_eq_sum (hCT : C.Represents T)
    {y : Obj} (hyU : y ∈ C.U) (hys : y ∈ X.PObj.smoothSet) :
    X.reducedCodimPart y 1 (T y) = ∑ i with y ∈ C.boundarySheet i,
      Finsupp.single ((C.orient i).tangent y) (C.σ i) := by
  rw [hCT y hyU hys, reducedCodimPart_orientedSum]
  refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
  constructor
  · rintro ⟨hy, h⟩
    exact ((C.orient i).hasReducedCodim_iff_mem_boundaryStratum hy).1 h
  · intro h
    exact ⟨h.1, ((C.orient i).hasReducedCodim_iff_mem_boundaryStratum h.1).2 h⟩

/-- **The stratum set in `U(x)` is the union of the boundary sheets** of every oriented tame
structure describing `T̂Θ`. -/
theorem mem_boundaryStratumSet_iff (hΘ : X.IsBranchedEpSubgroupoid Θ) (hCT : C.Represents T)
    {y : Obj} (hyU : y ∈ C.U) :
    y ∈ X.boundaryStratumSet Θ T ↔ ∃ i, y ∈ C.boundarySheet i := by
  classical
  constructor
  · rintro ⟨hys, hne⟩
    rw [C.reducedCodimPart_eq_sum hCT hyU (hΘ.support_subset hys)] at hne
    by_contra hno
    push Not at hno
    exact hne (Finset.sum_eq_zero fun i hi => absurd (Finset.mem_filter.1 hi).2 (hno i))
  · rintro ⟨i, hi⟩
    have hys : y ∈ supp Θ := (C.toLocalBranchingStructure.mem_supp_iff hyU).2 ⟨i, hi.1⟩
    refine ⟨hys, ?_⟩
    rw [C.reducedCodimPart_eq_sum hCT hyU (hΘ.support_subset hys)]
    exact finsupp_sum_single_ne_zero ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩ _
      C.σ_pos

theorem iUnion_boundarySheet (hΘ : X.IsBranchedEpSubgroupoid Θ) (hCT : C.Represents T) :
    ⋃ i, C.boundarySheet i = X.boundaryStratumSet Θ T ∩ C.rep.U := by
  ext y
  rw [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    have hyU : y ∈ C.U := C.subset_U i hi.1
    exact ⟨(C.mem_boundaryStratumSet_iff hΘ hCT hyU).2 ⟨i, hi⟩, C.U_eq ▸ hyU⟩
  · rintro ⟨h, hyU⟩
    exact (C.mem_boundaryStratumSet_iff hΘ hCT (C.U_eq ▸ hyU)).1 h

/-- **The boundary family** `(∂₁Mᵢ, o_{∂Mᵢ})`, `(σᵢ)` of an oriented tame structure of dimension
`m + 1` describing `T̂Θ`: an oriented sheet family of dimension `m` for the stratum set. -/
def boundaryFamily (hΘ : X.IsBranchedEpSubgroupoid Θ) (hCT : C.Represents T) :
    X.OrientedSheetFamily (X.boundaryStratumSet Θ T) m x where
  rep := C.rep
  ι := C.ι
  N := C.boundarySheet
  σ := C.σ
  orient := C.boundaryOrient
  isSmoothSubmanifold := fun i => (C.isSubmanifoldOfDim_boundarySheet i).1
  iUnion_eq := C.iUnion_boundarySheet hΘ hCT

theorem boundaryFamily_N (hΘ : X.IsBranchedEpSubgroupoid Θ) (hCT : C.Represents T) (i : C.ι) :
    (C.boundaryFamily hΘ hCT).N i = C.boundarySheet i := rfl

/-- **The boundary family describes `T̂_{∂Θ}`** ((9.12), `boundaryOrientation_eq_sum`). -/
theorem represents_boundaryFamily (hΘ : X.IsBranchedEpSubgroupoid Θ) (hCT : C.Represents T) :
    (C.boundaryFamily hΘ hCT).Represents (X.boundaryOrientation T) := by
  classical
  intro y hy
  have hyU : y ∈ C.U := C.U_eq ▸ hy.2
  rw [C.boundaryOrientation_eq_sum hCT hyU (hΘ.support_subset hy.1.1),
    OrientedSheetFamily.orientedSum, Finset.sum_filter]
  rfl

end OrientedTameStructure

end EpGroupoid

end Polyfold
