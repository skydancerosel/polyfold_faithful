import Polyfold.Chapter15.CylinderEndLocalization
import Polyfold.Chapter9.GeneralCorollaries

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Corollary 15.3.10 (3)** (p. 700; 2017: Corollary 15.1): "`Θ̃` restricts to `{i} × X = X` as
`Θᵢ`" on the level of the boundary `∂Θ̃` (Definition 9.2.16), and Remark 9.2.14.

# The weights of `∂Θ̃` on the ends of the cylinder

## The text, paraphrased

`∂Θ(y) = ∑_{i : y ∈ ∂Mᵢ} σᵢ` for `y ∈ ∂X` (Definition 9.2.16, Proposition 9.2.15), and a point
`y ∈ Mᵢ ∩ ∂X` lies in `∂Mᵢ` iff `T_yMᵢ ⊄ T_y^R X` (Remark 9.2.14).  For the cobordism `Θ̃` over
`[0, 1] × X` the sheets `M̃ⱼ = {f̃ = s̃ⱼ}` through `(i, x)` have `T M̃ⱼ = ker (f̃ − s̃ⱼ)'`, which is
not contained in `T^R = {0} × T_xX`, since `(f̃ − s̃ⱼ)'` is onto on `T^R`; so `∂Θ̃(i, x) = Θ̃(i, x)
= Θᵢ(x)`.

## What is formalized

Namespace `Polyfold.EpGroupoid`:
* **`boundaryTheta_eq_self_iff`**: for a local branching structure and `y ∈ U(x) ∩ ∂X`,
  `∂Θ(y) = Θ(y)` iff every sheet through `y` has `y` in its boundary.
* `boundaryTheta_eq_self_iff_not_isTangentReducedAt`: the same with `T_yMᵢ ⊄ T_y^R X`
  (Remark 9.2.14).
* `HasFullBoundaryWeight Θ`: `∂Θ = Θ` on `∂X ∩ supp Θ`; then `supp ∂Θ = ∂X ∩ supp Θ`
  (`supp_boundaryTheta_eq`).
* `exists_mem_ker_notMem_of_surjective_domRestrict`: the linear algebra of the text's argument:
  an operator that is onto on a proper subspace `R` has a kernel vector outside `R`.

Namespace `Polyfold.SBLocalization`, for `Θ̃ = Λ̃ ∘ f̃` with `Λ̃ = Λⁱ` over `t = i`, `d_X ≡ 0`,
and `∂Θ̃ = Θ̃` on `∂([0, 1] × X) ∩ supp Θ̃`:
* **`boundaryTheta_cyl_eq`**: `∂Θ̃(i, x) = Θᵢ(x)` (the weights on the ends).
* **`surjective_cylEndProj`**, `bijective_cylEndProj`: the end `i` of `|supp ∂Θ̃|` maps onto
  `|supp Θᵢ|`, bijectively.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

/-- **An operator that is onto on a proper subspace has a kernel vector outside it** (the
argument for `T M̃ ⊄ T^R` in the proof of Corollary 15.3.10 (3)): if `L|R` is onto and `R ≠ T`,
then `ker L ⊄ R`. -/
theorem exists_mem_ker_notMem_of_surjective_domRestrict {𝕜 T W : Type*} [Field 𝕜]
    [AddCommGroup T] [Module 𝕜 T] [AddCommGroup W] [Module 𝕜 W] (L : T →ₗ[𝕜] W)
    {R : Submodule 𝕜 T} (hR : R ≠ ⊤) (hL : Surjective (L.domRestrict R)) :
    ∃ v ∈ LinearMap.ker L, v ∉ R := by
  obtain ⟨v, hv⟩ : ∃ v : T, v ∉ R := by
    by_contra h
    push Not at h
    exact hR (eq_top_iff.2 fun v _ => h v)
  obtain ⟨u, hu⟩ := hL (L v)
  refine ⟨v - u, ?_, fun h => hv ?_⟩
  · rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact hu.symm
  · have := R.add_mem h u.2
    rwa [sub_add_cancel] at this

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

open scoped Classical in
/-- **`∂Θ(y) = Θ(y)` iff every sheet through `y` has `y` in its boundary** (Definition 9.2.16,
Proposition 9.2.15): for a local branching structure `(Mᵢ)`, `(σᵢ)` on `U(x)` and `y ∈ U(x)`. -/
theorem boundaryTheta_eq_self_iff {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x)
    {y : Obj} (hy : y ∈ B.U) :
    X.boundaryTheta Θ y = Θ y ↔
      ∀ i, y ∈ B.M i → y ∈ X.PObj.submanifoldBoundary (B.M i) := by
  rw [boundaryTheta_eq (hasIndependentTangentSums Θ) B hy, B.eq_sum y hy]
  have hsub : (Finset.univ.filter fun i => y ∈ X.PObj.submanifoldBoundary (B.M i)) ⊆
      Finset.univ.filter fun i => y ∈ B.M i := fun i hi =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _,
      MPolyfold.submanifoldBoundary_subset _ (Finset.mem_filter.1 hi).2⟩
  constructor
  · intro h i hi
    by_contra hni
    have hlt := Finset.sum_lt_sum_of_subset (f := B.σ) hsub
      (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
      (fun h' => hni (Finset.mem_filter.1 h').2) (B.σ_pos i) (fun j _ _ => (B.σ_pos j).le)
    exact absurd h hlt.ne
  · intro h
    refine Finset.sum_congr (Finset.Subset.antisymm hsub fun i hi => ?_) fun _ _ => rfl
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h i (Finset.mem_filter.1 hi).2⟩

/-- **`∂Θ(y) = Θ(y)` iff `T_yMᵢ ⊄ T_y^R X` for every sheet through `y`** (Remark 9.2.14), for
`y ∈ U(x) ∩ ∂X`. -/
theorem boundaryTheta_eq_self_iff_not_isTangentReducedAt {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) {y : Obj} (hy : y ∈ B.U) (hb : y ∈ X.PObj.boundary) :
    X.boundaryTheta Θ y = Θ y ↔
      ∀ i, y ∈ B.M i → ¬ X.PObj.IsTangentReducedAt (B.M i) y := by
  rw [boundaryTheta_eq_self_iff B hy]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [MPolyfold.mem_submanifoldBoundary_iff (B.isSmoothSubmanifold i)]
  exact ⟨fun h => h.2.2, fun h => ⟨hi, hb, h⟩⟩

variable (X) in
/-- **`∂Θ = Θ` on `∂X ∩ supp Θ`**: every sheet of `Θ` through a boundary point has that point
in its boundary (`boundaryTheta_eq_self_iff`). -/
def HasFullBoundaryWeight (Θ : Obj → ℚ) : Prop :=
  ∀ y ∈ X.PObj.boundary ∩ supp Θ, X.boundaryTheta Θ y = Θ y

/-- The criterion in terms of sheets: every point of `∂X ∩ supp Θ` has a local branching
structure all of whose sheets have the point in their boundary. -/
theorem hasFullBoundaryWeight_of_sheets {Θ : Obj → ℚ}
    (h : ∀ y ∈ X.PObj.boundary ∩ supp Θ, ∃ B : X.LocalBranchingStructure Θ y,
      ∀ i, y ∈ X.PObj.submanifoldBoundary (B.M i)) : X.HasFullBoundaryWeight Θ := fun y hy => by
  obtain ⟨B, hB⟩ := h y hy
  exact (boundaryTheta_eq_self_iff B B.mem_U).2 fun i _ => hB i

/-- If `∂Θ = Θ` on `∂X ∩ supp Θ`, then `supp ∂Θ = ∂X ∩ supp Θ`. -/
theorem supp_boundaryTheta_eq {Θ : Obj → ℚ} (h : X.HasFullBoundaryWeight Θ) :
    supp (X.boundaryTheta Θ) = X.PObj.boundary ∩ supp Θ :=
  Subset.antisymm (X.supp_boundaryTheta_subset Θ) fun y hy => by
    change 0 < X.boundaryTheta Θ y
    rw [h y hy]
    exact hy.2

end EpGroupoid

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-- **`∂Θ̃(i, x) = Θᵢ(x)`** (proof of Corollary 15.3.10 (3), p. 700): for `Λ̃ = Λⁱ` over `t = i`,
the slice `t = i` in `∂([0, 1] × X)`, and `∂Θ̃ = Θ̃` on `∂([0, 1] × X) ∩ supp Θ̃`. -/
theorem boundaryTheta_cyl_eq {f : A.Obj → A.W} (hf : IsSection A.P f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λᵢ : A.W → ℚ≥0} {i : ℝ}
    (hi : ∀ w, ((cubeVal w).1.1 0 : ℝ) = i → Λ' w = Λᵢ (cubeVal w).2)
    (hfull : (A.cubeSEP 1).X.HasFullBoundaryWeight
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)))
    {z : (A.cubeSEP 1).Obj} (hz : (z.1 0 : ℝ) = i)
    (hzb : z ∈ (A.cubeSEP 1).X.PObj.boundary) :
    (A.cubeSEP 1).X.boundaryTheta (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) z =
      (Λᵢ (f z.2) : ℚ) := by
  have e : Λ' (cubeLiftEp (n := 1) f hf z) = Λᵢ (f z.2) := hi _ hz
  by_cases hs : z ∈ EpGroupoid.supp (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ))
  · exact (hfull z ⟨hzb, hs⟩).trans (congrArg (fun q : ℚ≥0 => (q : ℚ)) e)
  · rw [EpGroupoid.boundaryTheta_eq_zero_of_not_mem_supp hs]
    have h0 : ¬ (0 : ℚ) < (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ) := hs
    have h1 : ¬ (0 : ℚ) < (Λᵢ (f z.2) : ℚ) := fun h => h0 (lt_of_lt_of_eq h
      (congrArg (fun q : ℚ≥0 => (q : ℚ)) e).symm)
    exact le_antisymm (NNRat.coe_nonneg _) (not_lt.1 h1)

/-- **The end `i` of `|supp ∂Θ̃|` maps onto `|supp Θᵢ|`** (`∂Θ̃ = Θᵢ` on the end `i`), under the
hypotheses of `boundaryTheta_cyl_eq`, the slice `t = i` lying in `∂([0, 1] × X)`. -/
theorem surjective_cylEndProj {f : A.Obj → A.W} (hf : IsSection A.P f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λᵢ : A.W → ℚ≥0} {i : unitInterval}
    (hi : ∀ w, ((cubeVal w).1.1 0 : ℝ) = i → Λ' w = Λᵢ (cubeVal w).2)
    (hfull : (A.cubeSEP 1).X.HasFullBoundaryWeight
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)))
    (hbd : ∀ z : (A.cubeSEP 1).Obj, (z.1 0 : ℝ) = i → z ∈ (A.cubeSEP 1).X.PObj.boundary)
    (hover : ∀ p : cylEnd (X := A.X) (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) i,
      cylEndMap p ∈ A.X.orbitSupp (fun x => (Λᵢ (f x) : ℚ))) :
    Surjective (cylEndProj hover) := by
  rintro ⟨_, x, hx, rfl⟩
  set z : (A.cubeSEP 1).Obj := ((fun _ => i), x) with hzdef
  have hzt : (z.1 0 : ℝ) = i := rfl
  have hzs : z ∈ EpGroupoid.supp ((A.cubeSEP 1).X.boundaryTheta
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ))) := by
    change (0 : ℚ) < _
    rw [boundaryTheta_cyl_eq hf hi hfull hzt (hbd z hzt)]
    exact hx
  let p : cylEnd (X := A.X) (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) i :=
    ⟨⟨(A.X.cubeProd 1).π z, z, hzs, rfl⟩, by
      change A.X.cylOrbitTime ((A.X.cubeProd 1).π z) = i
      rw [cylOrbitTime_π]⟩
  refine ⟨p, Subtype.ext ?_⟩
  exact A.X.cylEndMap_π p z rfl

/-- **The end `i` of `|supp ∂Θ̃|` is `|supp Θᵢ|`**: `|(i, x)| ↦ |x|` is a continuous bijection
from the end onto `|supp Θᵢ|`. -/
theorem bijective_cylEndProj {f : A.Obj → A.W} (hf : IsSection A.P f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λᵢ : A.W → ℚ≥0} {i : unitInterval}
    (hi : ∀ w, ((cubeVal w).1.1 0 : ℝ) = i → Λ' w = Λᵢ (cubeVal w).2)
    (hfull : (A.cubeSEP 1).X.HasFullBoundaryWeight
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)))
    (hbd : ∀ z : (A.cubeSEP 1).Obj, (z.1 0 : ℝ) = i → z ∈ (A.cubeSEP 1).X.PObj.boundary)
    (hover : ∀ p : cylEnd (X := A.X) (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) i,
      cylEndMap p ∈ A.X.orbitSupp (fun x => (Λᵢ (f x) : ℚ))) :
    Bijective (cylEndProj hover) :=
  ⟨fun _ _ h => A.X.injective_cylEndMap _ _ (congrArg Subtype.val h),
    surjective_cylEndProj hf hi hfull hbd hover⟩

end SBLocalization

end Polyfold
