import Polyfold.Chapter17.SubpolyfoldStructure
import Polyfold.Chapter17.PolyfoldFaces
import Polyfold.Chapter17.ProperCoveringModelRestrict
import Polyfold.Chapter17.TameBoundaryTame
import Polyfold.Chapter17.BranchedSubcategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, p. 845: the full subcategory **`C_U`** associated to an open subset `U` of `|C|`, used in
Theorem 18.1.5, as a polyfold in its own right.  Numbers and pages are the 2021 text's.

# The polyfold `C_U` for an open `U ⊆ |C|`

## The text, paraphrased

(p. 845) "We denote, for a polyfold `C` and an open subset `U` of `|C|`, by `C_U` the full
subcategory associated to objects with `|α| ∈ U`."  Theorem 18.1.5 then speaks of a tame
orbifold-type ep⁺-subcategory `Θ : C_U → {0, 1}`, so `C_U` carries the polyfold structure
inherited from `C`.

## What is formalized

* `GCT.objOver C U = π⁻¹(U)` (the objects of `C_U`) and **`GCT.openSub C U`** (`C_U`, the full
  subcategory as a GCT, `GCT.sub`); `GCT.range_subOrbitMap_objOver` (`|C_U| → |C|` has image
  `U`), `GCT.isOpenEmbedding_subOrbitMap_objOver`, `GCT.openSubHomeomorph : |C_U| ≃ₜ U`.
* `LocalUniformizer.isOpen_preimage_objOver`: `Ψ⁻¹(π⁻¹ U)` is open in `O`.
* `PolyfoldConstruction.isSubpolyfold_objOver`: `π⁻¹(U)` is a subpolyfold (Definition 17.3.1).
* **`PolyfoldConstruction.openSubConstruction S hU : (C.openSub U).PolyfoldConstruction`**, the
  polyfold structure `(F_U, M)` of `C_U` (Proposition 17.3.6 for the subpolyfold `π⁻¹(U)`):
  `F_U(α) = {Ψ_U | Ψ ∈ F(α)}` with `Ψ_U : G ⋉ Ψ⁻¹(π⁻¹ U) → C_U` (`mem_openSubConstruction_F_iff`);
  `hasUniformizers_openSubConstruction`, **`isTame_openSubConstruction`** (`C_U` is tame when
  `C` is).
* `GCT.restrictTheta Θ` (`Θ|C_U`), `isFunctorial_restrictTheta`,
  `isOrbifoldTypeBranched_restrictTheta`.
* The transfer of local branching structures to a restricted uniformizer:
  `localBranching_restrict` (an open restriction of the object space keeps local branching
  structures and their tame sheets), and **`isBranchedEpSubgroupoid_restrict`**,
  **`isTameBranched_restrict`**: if `Θ ∘ Ψ` has, at every point of `Ψ⁻¹(π⁻¹ U)` in its support,
  a local branching structure with tame sheets, then `Θ|C_U ∘ Ψ_U` is a tame branched
  ep⁺-subgroupoid of `G ⋉ Ψ⁻¹(π⁻¹ U)`.
* **`openSub_isBranchedSubcategory`**: the criterion for `Θ|C_U` to be a tame branched
  ep⁺-subcategory of `C_U` (Definitions 17.5.1, 17.5.4 (3)), in terms of local branching
  structures of `Θ ∘ Ψ` at the points of the uniformizers of `C` lying over `U`.

## Readings

* `C_U` is `C.sub (π⁻¹ U)` (`SubpolyfoldStructure.lean`), `|C_U|` with the topology of `|C|`;
  for open `U` it is homeomorphic to `U` (`openSubHomeomorph`).
* The polyfold structure of `C_U` is the one of Proposition 17.3.6 for the subpolyfold `π⁻¹(U)`:
  the uniformizers are the restrictions `Ψ_U` of the `Ψ ∈ F(α)`, `α ∈ C_U`, to the open
  `G`-invariant subset `Ψ⁻¹(π⁻¹ U)` of `O` (with its sub-M-polyfold structure, the open-subset
  structure), and `M(Ψ_U, Ψ'_U)` is the open subset `s⁻¹(Ψ⁻¹(π⁻¹ U))` of `M(Ψ, Ψ')`.
* A functor `Θ : C → ℚ` restricts to `Θ|C_U = Θ ∘ (C_U → C)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

/-! ### The full subcategory `C_U` -/

namespace GCT

variable (C : GCT.{u})

/-- **The objects of `C_U`**: the `α` with `|α| ∈ U` (2021 p. 845). -/
abbrev objOver (U : Set C.toGroupoidStr.OrbitSpace) : Set C.Obj := C.toGroupoidStr.π ⁻¹' U

/-- **`C_U`**, the full subcategory associated to the objects with `|α| ∈ U` (2021 p. 845), as a
GCT (`|C_U|` with the topology of `|C|`). -/
abbrev openSub (U : Set C.toGroupoidStr.OrbitSpace) : GCT.{u} := C.sub (C.objOver U)

variable {C}

/-- `π⁻¹(U)` is saturated. -/
theorem isSaturated_objOver (U : Set C.toGroupoidStr.OrbitSpace) :
    C.toGroupoidStr.IsSaturated (C.objOver U) :=
  C.toGroupoidStr.isSaturated_iff.2 fun φ hφ => by
    change C.toGroupoidStr.π (C.toGroupoidStr.tgt φ) ∈ U
    rw [← C.toGroupoidStr.π_src_eq_π_tgt φ]
    exact hφ

/-- `|C_U| → |C|` sends `|α|` to `|α|`. -/
theorem subOrbitMap_π (U : Set C.toGroupoidStr.OrbitSpace) (α : C.objOver U) :
    C.subOrbitMap (C.objOver U) ((C.toGroupoidStr.fullSub (C.objOver U)).π α) =
      C.toGroupoidStr.π α.1 := rfl

/-- **The image of `|C_U| → |C|` is `U`.** -/
theorem range_subOrbitMap_objOver (U : Set C.toGroupoidStr.OrbitSpace) :
    range (C.subOrbitMap (C.objOver U)) = U := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    induction w using Quotient.inductionOn with
    | h α => exact α.2
  · intro hz
    induction z using Quotient.inductionOn with
    | h α => exact ⟨(C.toGroupoidStr.fullSub (C.objOver U)).π ⟨α, hz⟩, rfl⟩

/-- **`|C_U| → |C|` is an open embedding** for open `U`. -/
theorem isOpenEmbedding_subOrbitMap_objOver {U : Set C.toGroupoidStr.OrbitSpace}
    (hU : IsOpen U) :
    @IsOpenEmbedding _ _ (C.openSub U).top _ (C.subOrbitMap (C.objOver U)) :=
  @IsOpenEmbedding.mk _ _ (C.openSub U).top _ _ (C.isEmbedding_subOrbitMap _)
    ((range_subOrbitMap_objOver U).symm ▸ hU)

/-- **`|C_U| ≅ U`** for open `U`. -/
def openSubHomeomorph {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U) :
    @Homeomorph (C.openSub U).toGroupoidStr.OrbitSpace U (C.openSub U).top _ :=
  letI := (C.openSub U).top
  ((isOpenEmbedding_subOrbitMap_objOver hU).isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr (range_subOrbitMap_objOver U))

@[simp] theorem openSubHomeomorph_apply {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U)
    (z : (C.openSub U).toGroupoidStr.OrbitSpace) :
    ((openSubHomeomorph hU z : U) : C.toGroupoidStr.OrbitSpace) = C.subOrbitMap (C.objOver U) z :=
  rfl

/-- **`Θ|C_U`**, the restriction of a functor `Θ : C → ℚ` to `C_U`. -/
abbrev restrictTheta (U : Set C.toGroupoidStr.OrbitSpace) (Θ : C.Obj → ℚ) :
    (C.openSub U).Obj → ℚ :=
  fun α => Θ (show C.objOver U from α).1

theorem isFunctorial_restrictTheta (U : Set C.toGroupoidStr.OrbitSpace) {Θ : C.Obj → ℚ}
    (hΘ : C.toGroupoidStr.IsFunctorial Θ) :
    (C.openSub U).toGroupoidStr.IsFunctorial (restrictTheta U Θ) :=
  fun φ => hΘ (show C.toGroupoidStr.morOn (C.objOver U) from φ).1

theorem isOrbifoldTypeBranched_restrictTheta (U : Set C.toGroupoidStr.OrbitSpace)
    {Θ : C.Obj → ℚ} (h : C.IsOrbifoldTypeBranched Θ) :
    (C.openSub U).IsOrbifoldTypeBranched (restrictTheta U Θ) :=
  fun _ => h _

/-! ### Restricted uniformizers -/

namespace LocalUniformizer

variable (Ψ : C.LocalUniformizer)

/-- `Ψ⁻¹(π⁻¹ U)` is open in `O` for open `U`. -/
theorem isOpen_preimage_objOver {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U) :
    IsOpen (Ψ.obj ⁻¹' C.objOver U) :=
  hU.preimage Ψ.continuous_π_obj

/-- `Ψ⁻¹(π⁻¹ U)` is a sub-M-polyfold of `O` (an open subset). -/
theorem isSubMPolyfold_preimage_objOver {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U) :
    Ψ.P.IsSubMPolyfold (Ψ.obj ⁻¹' C.objOver U) :=
  MPolyfold.isSubMPolyfold_of_isOpen' (Ψ.isOpen_preimage_objOver hU)

/-- **`Ψ_U : G ⋉ Ψ⁻¹(π⁻¹ U) → C_U`**, the restriction of `Ψ` (p. 785 for the subpolyfold
`π⁻¹ U`). -/
abbrev restrictOver {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U) :
    (C.openSub U).LocalUniformizer :=
  Ψ.restrict (isSaturated_objOver U) (Ψ.isSubMPolyfold_preimage_objOver hU)

/-- **`Ψ_U` is tame when `Ψ` is**: an open subset of a tame M-polyfold, with the sub-M-polyfold
structure, is tame. -/
theorem isTame_restrictOver {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U)
    (h : Ψ.IsTame) : (Ψ.restrictOver hU).IsTame := by
  have ht := MPolyfold.HasTameInducedStructure.inter_isOpen_of_isSubMPolyfold
    (Ψ.P.hasTameInducedStructure_univ h) (Ψ.isOpen_preimage_objOver hU)
  rw [univ_inter] at ht
  obtain ⟨_, ht⟩ := ht
  exact ht

end LocalUniformizer

/-! ### Local branching structures on a restricted uniformizer -/

namespace LocalUniformizer

variable {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U) (Ψ : C.LocalUniformizer)

open scoped Classical in
/-- The map `O → Ψ⁻¹(π⁻¹ U)`, the identity on `Ψ⁻¹(π⁻¹ U)` (and the constant `q` elsewhere). -/
def restrictOverRetract (q : Ψ.obj ⁻¹' C.objOver U) (y : Ψ.O) : Ψ.obj ⁻¹' C.objOver U :=
  if h : y ∈ Ψ.obj ⁻¹' C.objOver U then ⟨y, h⟩ else q

theorem restrictOverRetract_of_mem (q : Ψ.obj ⁻¹' C.objOver U) {y : Ψ.O}
    (hy : y ∈ Ψ.obj ⁻¹' C.objOver U) : Ψ.restrictOverRetract q y = ⟨y, hy⟩ := by
  unfold restrictOverRetract
  rw [dif_pos hy]

/-- **The open set `Ψ⁻¹(π⁻¹ U)` of `O` and the M-polyfold `Ψ⁻¹(π⁻¹ U)` of `Ψ_U` are
sc-diffeomorphic** by the identity (`restrictOverRetract` and the inclusion). -/
theorem isScDiffeoOn_restrictOverRetract (q : Ψ.obj ⁻¹' C.objOver U) :
    Ψ.P.IsScDiffeoOn (Ψ.restrictOver hU).P (Ψ.restrictOverRetract q) Subtype.val
      (Ψ.obj ⁻¹' C.objOver U) univ := by
  have hW := Ψ.isOpen_preimage_objOver hU
  have p := Ψ.isSubMPolyfold_preimage_objOver hU
  have hr : ∀ y ∈ Ψ.obj ⁻¹' C.objOver U, ((Ψ.restrictOverRetract q y : Ψ.obj ⁻¹' C.objOver U) :
      Ψ.O) = y := fun y hy => by rw [Ψ.restrictOverRetract_of_mem q hy]
  exact
    { isScSmoothOn := MPolyfold.isScSmoothOn_subPolyfold_of_val p
        ((MPolyfold.isScSmoothMap_id.mono hW (subset_univ _)).congr fun y hy => (hr y hy).symm)
      isScSmoothOn_inv := MPolyfold.subPolyfold_inclusion_isScSmooth p
      mapsTo := fun _ _ => mem_univ _
      mapsTo_inv := fun y _ => y.2
      left_inv := fun y hy => hr y hy
      right_inv := fun y _ => Ψ.restrictOverRetract_of_mem q y.2 }

/-- **Restricting a local branching structure to `Ψ_U`**: a local branching structure of
`Θ ∘ Ψ` at a point `q` of `Ψ⁻¹(π⁻¹ U)` gives one of `Θ|C_U ∘ Ψ_U` at `q` (the sheets
`Mᵢ ∩ Ψ⁻¹(π⁻¹ U)`, the same weights); tame sheets stay tame. -/
theorem localBranching_restrict {Θ : C.Obj → ℚ} (q : Ψ.obj ⁻¹' C.objOver U)
    (B : Ψ.ep.LocalBranchingStructure (Θ ∘ Ψ.obj) q.1) :
    ∃ B' : (Ψ.restrictOver hU).ep.LocalBranchingStructure
        (restrictTheta U Θ ∘ (Ψ.restrictOver hU).obj) q,
      (∀ i, Ψ.P.HasTameInducedStructure (B.M i)) →
        ∀ i, (Ψ.restrictOver hU).P.HasTameInducedStructure (B'.M i) := by
  have hf := Ψ.isScDiffeoOn_restrictOverRetract hU q
  have hΘ : ∀ u ∈ Ψ.obj ⁻¹' C.objOver U,
      (restrictTheta U Θ ∘ (Ψ.restrictOver hU).obj) (Ψ.restrictOverRetract q u) =
        (Θ ∘ Ψ.obj) u := fun u hu => by
    rw [Ψ.restrictOverRetract_of_mem q hu]
    rfl
  refine ⟨B.mapDiffeo (X := Ψ.ep) (Y := (Ψ.restrictOver hU).ep) hf q.2
    (Ψ.restrictOverRetract_of_mem q q.2) hΘ, fun ht i => ?_⟩
  exact MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn
    ((B.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen)
    (MPolyfold.HasTameInducedStructure.inter_isOpen (B.isSmoothSubmanifold i) (ht i)
      hf.isScSmoothOn.isOpen) hf inter_subset_right

/-- **`Θ|C_U ∘ Ψ_U` is a tame branched ep⁺-subgroupoid** of `G ⋉ Ψ⁻¹(π⁻¹ U)` as soon as `Θ` is a
functor `C → ℚ⁺` and `Θ ∘ Ψ` has, at every point of `Ψ⁻¹(π⁻¹ U)` in its support, a local
branching structure with tame sheets (Definitions 9.1.2 and 9.3.12 for `Ψ_U`). -/
theorem isBranchedEpSubgroupoid_restrict {Θ : C.Obj → ℚ} (h0 : ∀ α, 0 ≤ Θ α)
    (hΘ : C.toGroupoidStr.IsFunctorial Θ)
    (h : ∀ q ∈ Ψ.obj ⁻¹' C.objOver U, 0 < Θ (Ψ.obj q) →
      ∃ B : Ψ.ep.LocalBranchingStructure (Θ ∘ Ψ.obj) q,
        ∀ i, Ψ.P.HasTameInducedStructure (B.M i)) :
    (Ψ.restrictOver hU).ep.IsBranchedEpSubgroupoid
        (restrictTheta U Θ ∘ (Ψ.restrictOver hU).obj) ∧
      (Ψ.restrictOver hU).ep.IsTameBranched (restrictTheta U Θ ∘ (Ψ.restrictOver hU).obj) := by
  have key : ∀ q ∈ EpGroupoid.supp (restrictTheta U Θ ∘ (Ψ.restrictOver hU).obj),
      ∃ B' : (Ψ.restrictOver hU).ep.LocalBranchingStructure
        (restrictTheta U Θ ∘ (Ψ.restrictOver hU).obj) q,
        ∀ i, (Ψ.restrictOver hU).P.HasTameInducedStructure (B'.M i) := by
    intro q hq
    obtain ⟨B, hB⟩ := h q.1 q.2 hq
    obtain ⟨B', hB'⟩ := Ψ.localBranching_restrict hU q B
    exact ⟨B', hB' hB⟩
  refine ⟨{ nonneg := fun _ => h0 _
            isFunctorial := (Ψ.restrictOver hU).isFunctorial_comp
              (isFunctorial_restrictTheta U hΘ)
            support_subset := fun q hq => ?_
            paracompactSpace_orbitSupp := (Ψ.restrictOver hU).paracompactSpace_subset _
            localBranching := fun q hq => ⟨(key q hq).choose⟩ },
    (EpGroupoid.isTameBranched_iff_exists _ _).2 key⟩
  obtain ⟨B', -⟩ := key q hq
  obtain ⟨i⟩ := B'.nonempty_ι_of_mem_supp hq
  exact (B'.isSmoothSubmanifold i).subset_smoothSet (B'.mem_M i)

end LocalUniformizer

/-! ### The polyfold structure of `C_U` -/

namespace PolyfoldConstruction

variable (S : C.PolyfoldConstruction)

/-- **`π⁻¹(U)` is a subpolyfold** (Definition 17.3.1) for open `U ⊆ |C|`: it is saturated and
its preimage under every uniformizer is open. -/
theorem isSubpolyfold_objOver {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U) :
    S.IsSubpolyfold (C.objOver U) :=
  ⟨isSaturated_objOver U, fun _ _ Ψ _ => Ψ.isSubMPolyfold_preimage_objOver hU⟩

/-- **The polyfold structure `(F_U, M)` of `C_U`** (2021 p. 845, with Proposition 17.3.6 for the
subpolyfold `π⁻¹(U)`). -/
abbrev openSubConstruction {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U) :
    (C.openSub U).PolyfoldConstruction :=
  subConstruction (S.isSubpolyfold_objOver hU)

variable {S}

/-- **`F_U(α) = {Ψ_U | Ψ ∈ F(α)}`.** -/
theorem mem_openSubConstruction_F_iff {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U)
    (α : (C.openSub U).Obj) (L : (C.openSub U).LocalUniformizer) :
    L ∈ (S.openSubConstruction hU).F α ↔
      ∃ Ψ ∈ S.F (show C.objOver U from α).1, L = Ψ.restrictOver hU := by
  rw [mem_subF_iff]
  exact ⟨fun ⟨Ψ, hΨ, h⟩ => ⟨Ψ, hΨ, h⟩, fun ⟨Ψ, hΨ, h⟩ => ⟨Ψ, hΨ, h⟩⟩

/-- `C_U` has uniformizers at every object when `C` does. -/
theorem hasUniformizers_openSubConstruction {U : Set C.toGroupoidStr.OrbitSpace}
    (hU : IsOpen U) (h : S.HasUniformizers) :
    (S.openSubConstruction hU).HasUniformizers := fun α => by
  obtain ⟨Ψ, hΨ⟩ := h (show C.objOver U from α).1
  exact ⟨Ψ.restrictOver hU, (mem_openSubConstruction_F_iff hU α _).2 ⟨Ψ, hΨ, rfl⟩⟩

/-- **`C_U` is tame when `C` is** (Definition 17.2.13 for `(F_U, M)`). -/
theorem isTame_openSubConstruction {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U)
    (h : S.IsTame) : (S.openSubConstruction hU).IsTame := fun α L hL => by
  obtain ⟨Ψ, hΨ, rfl⟩ := (mem_openSubConstruction_F_iff hU α L).1 hL
  exact Ψ.isTame_restrictOver hU (h _ Ψ hΨ)

/-- **A criterion for `Θ|C_U` to be a tame branched ep⁺-subcategory of `C_U`** (Definitions
17.5.1 and 17.5.4 (3) for `(F_U, M)`): `Θ` is a functor `C → ℚ⁺` and, for every uniformizer
`Ψ ∈ F(α)` of `C` at an object over `U`, `Θ ∘ Ψ` has at every point of `Ψ⁻¹(π⁻¹ U)` in its
support a local branching structure with tame sheets. -/
theorem openSub_isBranchedSubcategory {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U)
    {Θ : C.Obj → ℚ} (h0 : ∀ α, 0 ≤ Θ α) (hΘ : C.toGroupoidStr.IsFunctorial Θ)
    (h : ∀ α ∈ C.objOver U, ∀ Ψ ∈ S.F α, ∀ q ∈ Ψ.obj ⁻¹' C.objOver U, 0 < Θ (Ψ.obj q) →
      ∃ B : Ψ.ep.LocalBranchingStructure (Θ ∘ Ψ.obj) q,
        ∀ i, Ψ.P.HasTameInducedStructure (B.M i)) :
    (S.openSubConstruction hU).IsBranchedSubcategory (restrictTheta U Θ) ∧
      (S.openSubConstruction hU).IsTameSubcategory (restrictTheta U Θ) := by
  have key : ∀ α (L : (C.openSub U).LocalUniformizer), L ∈ (S.openSubConstruction hU).F α →
      L.ep.IsBranchedEpSubgroupoid (restrictTheta U Θ ∘ L.obj) ∧
        L.ep.IsTameBranched (restrictTheta U Θ ∘ L.obj) := by
    intro α L hL
    obtain ⟨Ψ, hΨ, rfl⟩ := (mem_openSubConstruction_F_iff hU α L).1 hL
    exact Ψ.isBranchedEpSubgroupoid_restrict hU h0 hΘ
      (h _ (show C.objOver U from α).2 Ψ hΨ)
  exact ⟨⟨fun _ => h0 _, isFunctorial_restrictTheta U hΘ, fun α L hL => (key α L hL).1⟩,
    fun α _ L hL => (key α L hL).2⟩

end PolyfoldConstruction

end GCT

end Polyfold
