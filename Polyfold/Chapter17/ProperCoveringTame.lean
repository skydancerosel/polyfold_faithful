import Polyfold.Chapter17.ProperCoveringBranched
import Polyfold.Chapter17.BranchedSubcategory

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8:
**Proposition 17.8.16 (3)** (p. 839, tameness is preserved by the pull-back along a proper
polyfold covering functor).  Numbers and pages are the 2021 text's.

# Tameness and proper coverings

## The text, paraphrased

(Proposition 17.8.16 (3)) If `Θ : B → ℚ⁺` is tame, then `P^*Θ = Θ ∘ P` is tame.  *Proof*: "all the
procedures in the proof of the previous result preserve the tameness property": `Θ` is moved to
`Γ^*Θ`, then to `τ̂^*(Γ^*Θ)` and to `Γ̂^*(τ̂^*(Γ^*Θ)) = P^*Θ`.

## What is formalized

* The ep-level step (the "easy exercise" of p. 839 with tameness): for a proper covering functor
  `τ : E → X` of ep-groupoids (Definition 8.5.1), `τ^*Θ'` is tame (Definition 9.3.6) when `Θ'` is
  (`EpFunctor.IsProperCovering.isTameBranched_pullbackTheta`).  A tame local branching structure
  of `Θ'` at `τ(e)` is moved by the local inverse of `τ` near `e`; its sheets keep a tame induced
  structure (`HasTameInducedStructure.image_of_isScDiffeoOn`), and the restriction to a natural
  representation is Chapter 17's `isTameBranched_iff_exists`.
* Tameness (Definition 17.5.4 (3)) for the induced structures: `IsTameBase` on `B` (through the
  uniformizers `Ψ` at the points of `supp(Θ)`) and `IsTameHat` on `A` (through the `Ψ̂`).
* **Proposition 17.8.16 (3)**: `proposition_17_8_16_three`, and the combined form
  `proposition_17_8_16_branched_tame`.
* Witness: `proposition_17_8_16_three_reflection` for `Θ₀ = 1_{0}` on `ℤˣ ⋉ ℝ` and the two-sheet
  construction (`isTameBranched_reflectionTheta`: `Θ₀` is tame; its support `{0}` has isotropy
  `ℤ/2`).

## Readings

* Definition 17.5.4 (3) for `A` with the uniformizers `Ψ̂ ∈ F(β)`: we read "`α ∈ supp(Θ')` and
  `Ψ̂ ∈ F(α)`" as `Ψ̂ ∈ F(β)` for some `α ∈ P⁻¹(β)` with `Θ'(α) > 0` (the distinguished points of
  `Ψ̂` are mapped onto `P⁻¹(β)`, Definition 17.8.10 (1)).  As in `ProperCoveringBranched`, this
  is the local form of the text's proof through each `Ψ̂`; the global model (17.104) is not needed.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

open EpGroupoid EpGroupoid.Examples

universe u

/-! ### The ep-level step -/

section EpLevel

variable {ObjE MorE ObjX MorX : Type u} [TopologicalSpace ObjE] [T2Space ObjE]
  [ParacompactSpace ObjE] [TopologicalSpace MorE] [T2Space MorE] [ParacompactSpace MorE]
  [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {E : EpGroupoid ObjE MorE} {X : EpGroupoid ObjX MorX} {τ : EpFunctor E X}

namespace EpFunctor.IsProperCovering

/-- **The easy exercise of p. 839 with tameness** (Proposition 17.8.16 (3), ep-level): the
pull-back `τ^*Θ'` of a tame `Θ'` (Definition 9.3.6) along a proper covering functor of
ep-groupoids (Definition 8.5.1) is tame.  A tame local branching structure at `τ(e)` is moved by
the local inverse of `τ` near `e`; tame sheets stay tame. -/
theorem isTameBranched_pullbackTheta (hτ : τ.IsProperCovering) {Θ' : ObjX → ℚ}
    (hΘ' : X.IsTameBranched Θ') : E.IsTameBranched (τ.pullbackTheta Θ') := by
  rw [E.isTameBranched_iff_exists]
  intro x hx
  obtain ⟨T⟩ := hΘ' _ hx
  obtain ⟨U, V, g, hxU, hd⟩ := hτ.isLocalScDiffeo x
  refine ⟨T.toLocalBranchingStructure.mapDiffeo hd.symm (hd.mapsTo hxU) (hd.left_inv x hxU)
    fun z hz => by simp only [EpFunctor.pullbackTheta_apply, hd.right_inv z hz], fun i => ?_⟩
  exact MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn
    ((T.isSmoothSubmanifold i).inter_isOpen hd.symm.isScSmoothOn.isOpen)
    (MPolyfold.HasTameInducedStructure.inter_isOpen (T.isSmoothSubmanifold i)
      (T.hasTameInducedStructure i) hd.symm.isScSmoothOn.isOpen) hd.symm inter_subset_right

end EpFunctor.IsProperCovering

end EpLevel

/-! ### Proposition 17.8.16 (3) -/

namespace ProperCoveringUniformizerConstruction

variable {A B : GCT.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
  (F : ProperCoveringUniformizerConstruction P)

/-- **Definition 17.5.4 (3) for the induced structure of `B`**: for `β ∈ supp(Θ)` and
`(Ψ̂, Ψ) ∈ F(β)`, `Θ ∘ Ψ` is a tame branched ep⁺-subgroupoid of `G ⋉ O_β`. -/
def IsTameBase (Θ : B.Obj → ℚ) : Prop :=
  ∀ β, 0 < Θ β → ∀ U ∈ F.F β, U.Ψ.ep.IsTameBranched (Θ ∘ U.Ψ.obj)

/-- **Definition 17.5.4 (3) for the induced structure of `A`** (the uniformizers `Ψ̂ : E → A`):
for `(Ψ̂, Ψ) ∈ F(β)` such that some `α ∈ P⁻¹(β)` lies in `supp(Θ')`, `Θ' ∘ Ψ̂` is tame on `E`. -/
def IsTameHat (Θ' : A.Obj → ℚ) : Prop :=
  ∀ β, (∃ α, P.obj α = β ∧ 0 < Θ' α) → ∀ U ∈ F.F β, U.E.IsTameBranched (Θ' ∘ U.hat.obj)

variable {F}

/-- **Proposition 17.8.16 (3)**, p. 839: if `Θ` is tame, so is `P^*Θ = Θ ∘ P`.  *Proof*:
`Θ ∘ P ∘ Ψ̂ = τ̂^*(Θ ∘ Ψ)` and `τ̂` is a proper covering functor of ep-groupoids, along which
tameness pulls back. -/
theorem proposition_17_8_16_three (hPc : P.IsProperCoveringGCT) {Θ : B.Obj → ℚ}
    (hΘ : F.IsTameBase Θ) : F.IsTameHat (Θ ∘ P.obj) := by
  rintro β ⟨α, rfl, hα⟩ U hU
  rw [U.comp_hat_eq_pullbackTheta]
  exact (U.isProperCovering_τ hPc).isTameBranched_pullbackTheta (hΘ _ hα U hU)

/-- **Proposition 17.8.16 with (3)**: a tame branched ep⁺-subcategory pulls back to a tame branched
ep⁺-subcategory. -/
theorem proposition_17_8_16_branched_tame (hPc : P.IsProperCoveringGCT) {Θ : B.Obj → ℚ}
    (hΘ : F.IsBranchedBase Θ) (ht : F.IsTameBase Θ) :
    F.IsBranchedHat (Θ ∘ P.obj) ∧ F.IsTameHat (Θ ∘ P.obj) :=
  ⟨proposition_17_8_16 hPc hΘ, proposition_17_8_16_three hPc ht⟩

end ProperCoveringUniformizerConstruction

/-! ### Witness -/

section Witness

attribute [local instance] instMulActionUnitsBool'

open ProperCoveringUniformizerConstruction

/-- `Θ₀ = 1_{0}` is a tame branched ep⁺-subgroupoid of `ℤˣ ⋉ ℝ`: the sheet `{0}` avoids the
boundary (`ℝ` has none), so it has a tame induced structure. -/
theorem isTameBranched_reflectionTheta : reflectionEpGroupoid.IsTameBranched reflectionTheta := by
  rw [reflectionEpGroupoid.isTameBranched_iff_exists]
  intro x hx
  have hx0 : x = 0 := by
    by_contra h
    simp [supp, reflectionTheta_apply, h] at hx
  subst hx0
  exact ⟨localBranchingStructure_reflectionTheta, fun i =>
    MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero
      (localBranchingStructure_reflectionTheta.isSmoothSubmanifold i)
      fun a _ => rnPolyfold_degIndex 1 a⟩

/-- **Witness for Proposition 17.8.16 (3)**: for the two-sheet covering
`ℤˣ ⋉ (Bool × ℝ) → ℤˣ ⋉ ℝ` and `Θ₀ = 1_{0}` (tame, support `{0}` with isotropy `ℤ/2`), the
hypothesis holds and `Θ₀ ∘ P` is tame and branched, equal to `1` at `(true, 0)` and `(false, 0)`;
the hypothesis of `IsTameHat` is met at `β = 0`. -/
theorem proposition_17_8_16_three_reflection :
    (sheetConstruction isScSmoothMap_units_smul Bool).IsTameBase reflectionTheta ∧
      (sheetConstruction isScSmoothMap_units_smul Bool).IsTameHat
        (reflectionTheta ∘ (sheetGCTFunctor isScSmoothMap_units_smul Bool).obj) ∧
      (∃ α, (sheetGCTFunctor isScSmoothMap_units_smul Bool).obj α = 0 ∧
        0 < (reflectionTheta ∘ (sheetGCTFunctor isScSmoothMap_units_smul Bool).obj) α) ∧
      ((sheetConstruction isScSmoothMap_units_smul Bool).F 0).Nonempty := by
  have hPc := isProperCoveringGCT_sheet isScSmoothMap_units_smul
    (fun (_ : ℤˣ) (_ : Bool) => rfl)
  have hT : (sheetConstruction isScSmoothMap_units_smul Bool).IsTameBase reflectionTheta := by
    rintro β - _ ⟨h, rfl⟩
    exact isTameBranched_reflectionTheta
  obtain ⟨-, -, -, -, h1, -⟩ := proposition_17_8_16_reflection
  refine ⟨hT, proposition_17_8_16_three hPc hT, ⟨(true, 0), rfl, by rw [h1]; exact one_pos⟩,
    ⟨_, sheetUniformizer_mem isScSmoothMap_units_smul Bool 0 units_smul_zero_rn⟩⟩

end Witness

end Polyfold
