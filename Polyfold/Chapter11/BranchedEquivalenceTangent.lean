import Polyfold.Chapter11.BranchedEquivalence
import Polyfold.Chapter9.OrientationBasic
import Polyfold.Chapter11.BranchedEquivalenceLocalization
import Polyfold.Chapter11.EpEquivalenceGeometry
import Polyfold.Chapter9.SubmanifoldTangentImage

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.3 "Branched Ep⁺-Subgroupoids and Equivalences" (pp. 538–542; 2017:
pp. 391–396): **Theorem 11.3.7** (tangent) and **Theorem 11.3.8** (boundary) (2017: Theorems 11.5,
11.6), together with the invariance of Chapter 9's tangent, orientation and boundary notions under
sc-diffeomorphisms between *different* M-polyfolds used by them and by Theorem 11.3.5.  Numbers and
pages are the 2021 text's, the 2017 ones in parentheses.  Lemma 11.3.4 is in
`BranchedEquivalenceTangentSection.lean`, Theorem 11.3.5, Definition 11.3.6 and Theorem 11.3.9 in
`BranchedEquivalenceTangentOrientation.lean`.

# Tangents and boundaries of branched ep⁺-subgroupoids along equivalences

## The text, paraphrased

(Theorem 11.3.7, p. 541) For a generalized isomorphism `f : X → Y` and branched
ep⁺-subgroupoids `Θ` on `X`, `Θ'` on `Y`: `(Tf)_* TΘ = T(f_*Θ)` and `(Tf)^* TΘ' = T(f^*Θ')`,
where `Tf = [TX ←TF TA →TG TY]` for `f = [X ←F A →G Y]`.  *Proof* (text): `TΘ` is locally given
by the tangents of the `Mᵢ` of a local branching structure; "the result is easily established",
details left to the reader.

(Theorem 11.3.8, pp. 541–542) `f_*(∂Θ) = ∂(f_*Θ)` and `f^*(∂Θ') = ∂(f^*Θ')` (11.11).  *Proof*
(text): local branching structures and the local sc-diffeomorphisms `ψ̂` of morphisms are moved by
equivalences, and for a submanifold `M ∋ x` the degeneracy index `d_M(x)` is preserved; left to
the reader.

## What is formalized

* Chapter 9 across M-polyfolds, for an sc-diffeomorphism `f : U → U'`, `U ⊆ X`, `U' ⊆ Y`
  (Chapter 9 has the versions for `X = Y`): `MPolyfold.submanifoldTangent_image_of_isScDiffeoOn`
  (`T_{f(a)} f(A) = Tf(T_aA)`), `chartVec_tangentMapOn_of_isScDiffeoOn`, `OrTangent.map`,
  `IsOrientedAt.map_tangentMapOn`, `SubmanifoldOrientation.mapDiffeo` (`f_*o`, continuity read in
  the chart `φ ∘ f⁻¹`), `mapDiffeo_tangent`, `IsTangentReducedAt.image_of_isScDiffeoOn`,
  `isTangentReducedAt_image_iff_of_isScDiffeoOn`,
  `mem_submanifoldBoundary_image_iff_of_isScDiffeoOn` (`d_M` preserved).
* Moved local branching structures (`LocalBranchingStructure.mapDiffeo` of
  `BranchedEquivalence.lean`): `tangentSum_mapDiffeo`, `tangentSum_eq_of_isScDiffeoOn` (Theorem
  9.2.1's independence is local and transported), `EpGroupoid.tangentTheta_tangentMapOn`,
  `EpGroupoid.boundaryTheta_apply_of_isScDiffeoOn`; oriented structures
  `OrientedBranchingStructure.mapDiffeo`, `orientedSum_mapDiffeo`.
* Equivalences `F`: `hasIndependentTangentSums_pushforwardTheta`,
  `hasIndependentTangentSums_pullbackTheta`, `tangentValue_pushforwardTheta_obj`,
  `tangentValue_pushforwardTheta` (`T(F_*Θ)(y) = Tψ ∘ TF(TΘ(x))`), `tangentValue_pullbackTheta`;
  **Theorem 11.3.7 for equivalences** `tangentTheta_pushforwardTheta`, `tangentTheta_pullbackTheta`;
  **Theorem 11.3.8 for equivalences** `boundaryTheta_pushforwardTheta`,
  `boundaryTheta_pullbackTheta`.
* Generalized isomorphisms (`EPLocalization.EPLoc`): **Theorem 11.3.7** `theorem_11_3_7_push`,
  `theorem_11_3_7_pull` (with `Tf = EPLoc.tangentFunctor.map f` of Theorem 11.1.1,
  `EpEquivalenceGeometry.lean`); **Theorem 11.3.8** `theorem_11_3_8_push`, `theorem_11_3_8_pull`;
  `hasIndependentTangentSums_pushTheta`, `hasIndependentTangentSums_pullTheta`.

## What the text leaves implicit, and the choices made

* `TΘ` and `∂Θ` (Theorem 9.2.1, Definitions 9.2.12, 9.2.16) are well defined in Chapter 9 under
  `HasIndependentTangentSums` (Theorem 9.2.1's independence; on `ℝᵐ` it always holds,
  `hasIndependentTangentSums_rn`).  The theorems assume it for `Θ` only: it is *transported* to
  `f_*Θ` and `f^*Θ'` (a structure at `y` moved back by the chart `Q = ψ̂ ∘ F` gives one at `x`).
* The tangent `(Tf)_*` acts on `TΘ : TX → ℚ⁺` as the push-forward of Definition 11.3.1 along the
  tangent generalized isomorphism; `TF` is an equivalence by Theorem 10.1.7.  The tangent sets are
  Part I's tangent bundles (no linear structure, point G.7).
* "`d_M(x)` is preserved" is read as: `x ∈ ∂M` iff `f(x) ∈ ∂f(M)` (`∂M` of Definition 9.2.16 via
  Remark 9.2.14); Theorem 10.3.19 is not used.

Images of submanifolds under sc-diffeomorphisms (`MPolyfold.OrTangent.map`,
`MPolyfold.OrTangent.map_carrier`, `MPolyfold.OrTangent.map_eq_push`,
`MPolyfold.IsOrientedAt.map_tangentMapOn`, …): `Chapter9/SubmanifoldTangentImage.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function Module Submodule

noncomputable section

namespace Polyfold

universe u v w

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-! ### Tangent sets of submanifolds under sc-diffeomorphisms `X ⊇ U → U' ⊆ Y` -/

/-! ### Chart vectors and oriented tangent sets -/

@[simp] theorem OrTangent.map_dim (f : P.TangentSpace → Q.TangentSpace) (g : OrTangent P) :
    (g.map f).dim = g.dim := rfl

theorem OrTangent.map_map (f : P.TangentSpace → Q.TangentSpace)
    (f' : Q.TangentSpace → S.TangentSpace) (g : OrTangent P) :
    (g.map f).map f' = g.map (f' ∘ f) := by
  simp only [OrTangent.map, image_image]
  rfl

theorem OrTangent.map_id (g : OrTangent P) : g.map id = g := OrTangent.push_id g

theorem OrTangent.map_congr {f f' : P.TangentSpace → Q.TangentSpace} {g : OrTangent P}
    (h : ∀ α ∈ g.carrier, f α = f' α) (hfr : ∀ v ∈ g.frames, ∀ i, v i ∈ g.carrier) :
    g.map f = g.map f' := by
  simp only [OrTangent.map]
  congr 1
  · exact image_congr h
  · exact image_congr fun v hv => funext fun i => h _ (hfr v hv i)

/-! ### `T_yM ⊆ T^R_yX` and `∂M` under sc-diffeomorphisms between different M-polyfolds -/

/-- `IsTangentReducedAt.image` for an sc-diffeomorphism between open subsets of two
M-polyfolds. -/
theorem IsTangentReducedAt.image_of_isScDiffeoOn {f : X → Y} {g : Y → X} {U : Set X}
    {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') {A : Set X}
    (hfA : Q.IsSmoothSubmanifold (f '' A)) (hAU : A ⊆ U) {a : X}
    (h : P.IsTangentReducedAt A a) : Q.IsTangentReducedAt (f '' A) (f a) := by
  obtain ⟨haA, d, -, -, -, -, -, haV, -⟩ := id h
  have hfaA : f a ∈ f '' A := ⟨a, haA, rfl⟩
  obtain ⟨ψ, hψ, hfaψ⟩ := Q.exists_isChart_mem_source (f a)
  obtain ⟨n, W, T, hT⟩ := ψ.model.isPartialQuadrant
  set χ := transportChart hf ψ with hχdef
  have hχ : P.IsChart χ := transportChart_isChart hf hψ
  have haχ : a ∈ χ.source := ⟨hAU haA, hfaψ⟩
  have hfa1 : f a ∈ Q.levelSet 1 := hfA.mem_levelSet_one hfaA
  have hz : ψ.model.E.toBase 1 (levelLift ψ 1 (f a)) = ψ (f a) :=
    Q.toBase_levelLift hψ hfaψ hfa1
  have hred := h.isReducedChart d hχ T hT haV haχ hz
  set G := f '' d.toSubData.shrink χ with hGdef
  have hWU : d.toSubData.shrink χ ⊆ U := fun x hx => (d.toSubData.shrink_subset_source χ hx).1
  have hinj : InjOn f U := fun x hx x' hx' hxx' => by
    rw [← hf.left_inv x hx, ← hf.left_inv x' hx', hxx']
  have himg : χ '' (d.toSubData.shrink χ ∩ A) = ψ '' (G ∩ f '' A) := by
    change (ψ ∘ f) '' _ = _
    rw [image_comp, hinj.image_inter hWU hAU]
  have hred' : IsReducedTangentAt ψ.model.E ψ.model.C (ψ '' (G ∩ f '' A)) T
      (levelLift ψ 1 (f a)) := by
    rw [← himg]; exact hred
  set d' := hfA.data hfaA
  have hfaV' : f a ∈ d'.V := hfA.mem_data_V hfaA
  have hG : IsOpen G := hf.isOpen_image_of_subset (d.toSubData.isOpen_shrink χ) hWU
  have hGψ : G ⊆ ψ.source := by
    rintro _ ⟨x, hx, rfl⟩; exact (d.toSubData.shrink_subset_source χ hx).2
  have hQ : IsScRetract ψ.model.E ψ.model.C (ψ '' (G ∩ f '' A)) := by
    rw [← himg]; exact d.toSubData.isScRetract_image χ hχ
  have hzs : levelLift ψ 1 (f a) ∈ ψ.model.E.smoothLvl 1 := by
    change ψ.model.E.toBase 1 _ ∈ (ψ.model.E.smooth : Set (ψ.model.E 0))
    rw [hz]; exact d'.apply_mem_smooth hψ hfaA hfaV' hfaψ
  have hres := isReducedTangentAt_chart_change hψ hψ hG (d'.toSubData.isOpen_shrink ψ) hGψ
    (d'.toSubData.shrink_subset_source ψ) hQ (d'.toSubData.isScRetract_image ψ hψ) hfaA
    ⟨a, d.toSubData.mem_shrink χ haA haV haχ, rfl⟩ (d'.toSubData.mem_shrink ψ hfaA hfaV' hfaψ)
    hz hz hzs T hT T hT hred'
  exact ⟨hfaA, d', ψ, n, W, T, _, hfaV', hψ, hfaψ, hT, hz, hres⟩

theorem isTangentReducedAt_image_iff_of_isScDiffeoOn {f : X → Y} {g : Y → X} {U : Set X}
    {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (hAU : A ⊆ U) {a : X} (ha : a ∈ A) :
    Q.IsTangentReducedAt (f '' A) (f a) ↔ P.IsTangentReducedAt A a := by
  have hfA := hA.image_of_isScDiffeoOn hf hAU
  refine ⟨fun h => ?_, fun h => h.image_of_isScDiffeoOn hf hfA hAU⟩
  have hgf : g '' (f '' A) = A := by
    rw [image_image]
    exact (image_congr fun y hy => hf.left_inv y (hAU hy)).trans (image_id' A)
  have hfAU' : f '' A ⊆ U' := image_subset_iff.2 fun y hy => hf.mapsTo (hAU hy)
  have := h.image_of_isScDiffeoOn hf.symm (hgf.symm ▸ hA) hfAU'
  rwa [hgf, hf.left_inv a (hAU ha)] at this

/-- **`∂M` is carried by sc-diffeomorphisms between different M-polyfolds**: `f(a) ∈ ∂(f(A))` iff
`a ∈ ∂A` (the step "`d_M(x)` is being preserved" of the proof of Theorem 11.3.8). -/
theorem mem_submanifoldBoundary_image_iff_of_isScDiffeoOn {f : X → Y} {g : Y → X} {U : Set X}
    {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (hAU : A ⊆ U) {a : X} (haU : a ∈ U) :
    f a ∈ Q.submanifoldBoundary (f '' A) ↔ a ∈ P.submanifoldBoundary A := by
  have hfA := hA.image_of_isScDiffeoOn hf hAU
  have hinj : InjOn f U := fun x hx x' hx' hxx' => by
    rw [← hf.left_inv x hx, ← hf.left_inv x' hx', hxx']
  have hmem : f a ∈ f '' A ↔ a ∈ A := hinj.mem_image_iff hAU haU
  rw [mem_submanifoldBoundary_iff hA, mem_submanifoldBoundary_iff hfA, hmem,
    ← hf.mem_boundary_iff haU]
  constructor
  · rintro ⟨ha, hb, hT⟩
    exact ⟨ha, hb, fun h => hT ((isTangentReducedAt_image_iff_of_isScDiffeoOn hf hA hAU ha).2 h)⟩
  · rintro ⟨ha, hb, hT⟩
    exact ⟨ha, hb, fun h => hT ((isTangentReducedAt_image_iff_of_isScDiffeoOn hf hA hAU ha).1 h)⟩

end MPolyfold

/-! ### Local branching structures moved by sc-diffeomorphisms: tangents, boundaries -/

section Branched

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

namespace EpGroupoid.LocalBranchingStructure

open MPolyfold

variable {Θ : Obj → ℚ} {Θ' : Obj' → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x)
  {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}

/-- `T_{f(x)} f(Mᵢ ∩ W) = Tf(T_xMᵢ)`. -/
theorem submanifoldTangent_image_inter (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hxW : x ∈ W)
    (i : B.ι) :
    Y.PObj.submanifoldTangent (f '' (B.M i ∩ W)) (f x) =
      tangentMapOn hf.isScSmoothOn '' X.PObj.submanifoldTangent (B.M i) x := by
  rw [submanifoldTangent_image_of_isScDiffeoOn hf
    ((B.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen) inter_subset_right
    ⟨B.mem_M i, hxW⟩, submanifoldTangent_inter_isOpen hf.isScSmoothOn.isOpen hxW]

/-- **The tangent sum of a moved structure**: `∑ σᵢ T_{f(x)} f(Mᵢ ∩ W) = Tf(∑ σᵢ T_xMᵢ)`. -/
theorem tangentSum_mapDiffeo (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hxW : x ∈ W) {y : Obj'}
    (hxy : f x = y) (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u) :
    (B.mapDiffeo hf hxW hxy hΘ).tangentSum =
      B.tangentSum.mapDomain (image (tangentMapOn hf.isScSmoothOn)) := by
  subst hxy
  rw [tangentSum, tangentSum, Finsupp.mapDomain_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.mapDomain_single]
  exact congrArg (Finsupp.single · _) (B.submanifoldTangent_image_inter hf hxW i)

/-- **Independence of the tangent sums is local and carried by sc-diffeomorphisms**: if all local
branching structures of `Θ` at `x` have the same `∑ σᵢ T_xMᵢ` and `Θ' ∘ f = Θ` on `W`, all of
`Θ'` at `f(x)` have the same sum (move them back by `f⁻¹`, compare, move forward). -/
theorem tangentSum_eq_of_isScDiffeoOn (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hxW : x ∈ W)
    (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u)
    (hind : ∀ B B' : X.LocalBranchingStructure Θ x, B.tangentSum = B'.tangentSum) {y : Obj'}
    (hxy : f x = y) (B₁ B₂ : Y.LocalBranchingStructure Θ' y) : B₁.tangentSum = B₂.tangentSum := by
  subst hxy
  have hΘ' : ∀ v ∈ W', Θ (g v) = Θ' v := fun v hv => by
    rw [← hΘ _ (hf.mapsTo_inv hv), hf.right_inv v hv]
  have key : ∀ B : Y.LocalBranchingStructure Θ' (f x), B.tangentSum =
      (B.mapDiffeo hf.symm (hf.mapsTo hxW) (hf.left_inv x hxW) hΘ').tangentSum.mapDomain
        (image (tangentMapOn hf.isScSmoothOn)) := by
    intro B
    rw [tangentSum_mapDiffeo, ← Finsupp.mapDomain_comp]
    conv_lhs => rw [← Finsupp.mapDomain_id (v := B.tangentSum)]
    refine Finsupp.mapDomain_congr fun L hL => ?_
    rw [Function.comp_apply, image_image, id]
    refine ((image_congr fun β hβ => ?_).trans (image_id' L)).symm
    exact hf.tangent.right_inv β (show _ ∈ W' from by
      rw [B.tangentSum_mem.2 L hL β hβ]; exact hf.mapsTo hxW)
  rw [key B₁, key B₂, hind]

/-- The value `TΘ'(Tf α) = TΘ(α)` of Definition 9.2.12 under an sc-diffeomorphism with
`Θ' ∘ f = Θ` (the local step of Theorem 11.3.7). -/
theorem _root_.Polyfold.EpGroupoid.tangentTheta_tangentMapOn
    (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u)
    (hΘb : X.IsBranchedEpSubgroupoid Θ) (hind : X.HasIndependentTangentSums Θ)
    (hind' : Y.HasIndependentTangentSums Θ') {α : X.PObj.TangentSpace}
    (hα : α ∈ X.PObj.tangentPreimage W) :
    Y.tangentTheta Θ' (tangentMapOn hf.isScSmoothOn α) = X.tangentTheta Θ α := by
  classical
  have hαW : X.PObj.levelVal 1 (X.PObj.tangentProj α) ∈ W := hα
  have hfx : Y.PObj.levelVal 1 (Y.PObj.tangentProj (tangentMapOn hf.isScSmoothOn α)) =
      f (X.PObj.levelVal 1 (X.PObj.tangentProj α)) :=
    levelVal_tangentProj_tangentMapOn hf.isScSmoothOn hα
  by_cases hx : X.PObj.levelVal 1 (X.PObj.tangentProj α) ∈ supp Θ
  · obtain ⟨B⟩ := hΘb.localBranching _ hx
    set B' := B.mapDiffeo hf hαW rfl hΘ
    have hU : Y.PObj.levelVal 1 (Y.PObj.tangentProj (tangentMapOn hf.isScSmoothOn α)) ∈ B'.U := by
      rw [hfx]; exact B'.mem_U
    rw [Y.tangentTheta_eq hind' B' hU, X.tangentTheta_eq hind B B.mem_U, Finset.sum_filter,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hiff : tangentMapOn hf.isScSmoothOn α ∈ Y.PObj.submanifoldTangent (B'.M i)
        (Y.PObj.levelVal 1 (Y.PObj.tangentProj (tangentMapOn hf.isScSmoothOn α))) ↔
        α ∈ X.PObj.submanifoldTangent (B.M i) (X.PObj.levelVal 1 (X.PObj.tangentProj α)) := by
      rw [hfx]
      change _ ∈ Y.PObj.submanifoldTangent (f '' (B.M i ∩ W)) _ ↔ _
      rw [B.submanifoldTangent_image_inter hf hαW i]
      exact hf.injOn_tangent.mem_image_iff (fun β hβ => show _ ∈ W from by
        rw [levelVal_tangentProj_of_mem hβ]; exact hαW) hα
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  · have hy : f (X.PObj.levelVal 1 (X.PObj.tangentProj α)) ∉ supp Θ' := by
      change ¬ 0 < Θ' _; rw [hΘ _ hαW]; exact hx
    rw [EpGroupoid.tangentTheta, EpGroupoid.tangentTheta, hfx, Y.tangentValue_eq_zero hy,
      X.tangentValue_eq_zero hx, EpGroupoid.grEval_zero, EpGroupoid.grEval_zero]

/-- `∂Θ'(f(x)) = ∂Θ(x)` (Definition 9.2.16) under an sc-diffeomorphism with `Θ' ∘ f = Θ` (the
local step of Theorem 11.3.8: the `d_{Mᵢ}(x)` are preserved). -/
theorem _root_.Polyfold.EpGroupoid.boundaryTheta_apply_of_isScDiffeoOn
    (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u)
    (hΘb : X.IsBranchedEpSubgroupoid Θ) (hind : X.HasIndependentTangentSums Θ)
    (hind' : Y.HasIndependentTangentSums Θ') {x : Obj} (hxW : x ∈ W) :
    Y.boundaryTheta Θ' (f x) = X.boundaryTheta Θ x := by
  classical
  by_cases hx : x ∈ supp Θ
  · obtain ⟨B⟩ := hΘb.localBranching _ hx
    set B' := B.mapDiffeo hf hxW rfl hΘ
    rw [Y.boundaryTheta_eq hind' B' B'.mem_U, X.boundaryTheta_eq hind B B.mem_U, Finset.sum_filter,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hA := (B.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen
    have hiff : f x ∈ Y.PObj.submanifoldBoundary (B'.M i) ↔
        x ∈ X.PObj.submanifoldBoundary (B.M i) :=
      (mem_submanifoldBoundary_image_iff_of_isScDiffeoOn hf hA inter_subset_right hxW).trans
        (mem_submanifoldBoundary_inter_isOpen_iff (B.isSmoothSubmanifold i)
          hf.isScSmoothOn.isOpen hxW)
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  · have hy : f x ∉ supp Θ' := by change ¬ 0 < Θ' _; rw [hΘ _ hxW]; exact hx
    rw [EpGroupoid.boundaryTheta_eq_zero_of_not_mem_supp hy,
      EpGroupoid.boundaryTheta_eq_zero_of_not_mem_supp hx]

end EpGroupoid.LocalBranchingStructure

namespace EpGroupoid.OrientedBranchingStructure

open MPolyfold

variable {Θ : Obj → ℚ} {Θ' : Obj' → ℚ} {x : Obj} (B : X.OrientedBranchingStructure Θ x)
  {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}

/-- **An oriented local branching structure moved by an sc-diffeomorphism** (the step of the
proof of Theorem 11.3.5, p. 540): `(f(Mᵢ ∩ W), f_* oᵢ)` with the same weights. -/
def mapDiffeo (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hxW : x ∈ W) {y : Obj'}
    (hxy : f x = y) (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u) : Y.OrientedBranchingStructure Θ' y where
  toLocalBranchingStructure := B.toLocalBranchingStructure.mapDiffeo hf hxW hxy hΘ
  dim := B.dim
  isSubmanifoldOfDim i := ((B.isSubmanifoldOfDim i).inter_isOpen
    hf.isScSmoothOn.isOpen).image_isScDiffeoOn hf inter_subset_right
  orient i := ((B.orient i).restrict hf.isScSmoothOn.isOpen).mapDiffeo
    ((B.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen) hf inter_subset_right

/-- `∑_{z ∈ f(Mᵢ)} σᵢ T_z(f(Mᵢ), f_*oᵢ) = Tf(∑_{f⁻¹z ∈ Mᵢ} σᵢ T_{f⁻¹z}(Mᵢ, oᵢ))` on the domain
of the moved structure. -/
theorem orientedSum_mapDiffeo (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hxW : x ∈ W)
    {y : Obj'} (hxy : f x = y) (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u) {z : Obj'}
    (hz : z ∈ (B.mapDiffeo hf hxW hxy hΘ).U) :
    (B.mapDiffeo hf hxW hxy hΘ).orientedSum z =
      (B.orientedSum (g z)).mapDomain (OrTangent.map (tangentMapOn hf.isScSmoothOn)) := by
  classical
  rw [orientedSum, orientedSum, Finsupp.mapDomain_finsetSum, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hiff := B.toLocalBranchingStructure.mem_image_iff_of_mem_mapU hf (i := i) hz
  split_ifs with h1 h2 h2
  · rw [Finsupp.mapDomain_single]
    have hgz : g z ∈ B.M i ∩ W := ⟨h2, hz.2.2⟩
    congr 1
    have h := SubmanifoldOrientation.mapDiffeo_tangent ((B.orient i).restrict
      hf.isScSmoothOn.isOpen) ((B.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen) hf
      inter_subset_right hgz
    rw [hf.right_inv z hz.1, SubmanifoldOrientation.restrict_tangent _ _ hgz.2] at h
    exact h
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · simp

end EpGroupoid.OrientedBranchingStructure

end Branched

/-! ### Equivalences: independence, `TΘ`, `∂Θ` (Theorems 11.3.7 and 11.3.8 for equivalences) -/

section Equivalence

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

namespace EpFunctor

open MPolyfold EpGroupoid

variable {F : EpFunctor X Y}

theorem pushforwardTheta_Q (hF : F.IsEquivalence) {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ)
    {x : Obj} {y : Obj'} (T : F.TransportChart x y) :
    ∀ u ∈ T.W, F.pushforwardTheta Θ (T.Q u) = Θ u := fun u hu =>
  pushforwardTheta_eq hF.full hΘ ⟨T.ψ u, T.src_ψ u hu, T.tgt_ψ u hu⟩

/-- **Theorem 9.2.1's independence is carried by `F_*`**: if the sums `∑ σᵢ T_xMᵢ` of `Θ` do not
depend on the local branching structure, neither do those of `F_*Θ` (structures at `y` are moved
to `x` by the chart `Q = ψ̂ ∘ F`). -/
theorem hasIndependentTangentSums_pushforwardTheta (hF : F.IsEquivalence) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) (hind : X.HasIndependentTangentSums Θ) :
    Y.HasIndependentTangentSums (F.pushforwardTheta Θ) := by
  intro y B₁ B₂
  obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso y
  obtain ⟨T, -⟩ := exists_transportChart hF.isLocalScDiffeo_obj hs ht
  exact LocalBranchingStructure.tangentSum_eq_of_isScDiffeoOn T.isScDiffeoOn_Q T.mem_W
    (pushforwardTheta_Q hF hΘ T) (hind x) T.Q_self B₁ B₂

/-- **Theorem 9.2.1's independence is carried by `F^*`** (structures are moved by a local inverse
of `F`). -/
theorem hasIndependentTangentSums_pullbackTheta (hF : F.IsEquivalence) {Θ' : Obj' → ℚ}
    (hind : Y.HasIndependentTangentSums Θ') :
    X.HasIndependentTangentSums (F.pullbackTheta Θ') := by
  intro x B₁ B₂
  obtain ⟨U, V, g, hxU, hd⟩ := hF.isLocalScDiffeo_obj x
  have hΘ : ∀ v ∈ V, F.pullbackTheta Θ' (g v) = Θ' v := fun v hv => by
    simp only [pullbackTheta_apply, hd.right_inv v hv]
  exact LocalBranchingStructure.tangentSum_eq_of_isScDiffeoOn hd.symm (hd.mapsTo hxU) hΘ
    (hind _) (hd.left_inv x hxU) B₁ B₂

/-- `F_*Θ(F(u)) = Θ(u)`. -/
theorem pushforwardTheta_obj_eqOn (hF : F.IsEquivalence) {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ)
    (U : Set Obj) : ∀ u ∈ U, F.pushforwardTheta Θ (F.obj u) = Θ u := fun u _ =>
  pushforwardTheta_obj hF.full hΘ u

/-- `TF = Tf` on `T_xX` for a local sc-diffeomorphism `f = F|U` around `x`. -/
theorem tangent_obj_eq_tangentMapOn {U : Set Obj} {V : Set Obj'} {g : Obj' → Obj}
    (hd : X.PObj.IsScDiffeoOn Y.PObj F.obj g U V) {α : X.PObj.TangentSpace}
    (hα : α ∈ X.PObj.tangentPreimage U) : F.tangent.obj α = tangentMapOn hd.isScSmoothOn α :=
  (tangentMapOn_eq_tangentMap F.isScSmoothMap_obj hd.isScSmoothOn hα).symm

/-- **`T(F_*Θ)(F(x)) = TF(TΘ(x))`** (Theorem 9.2.1's section functor along `F`, at `F(x)`). -/
theorem tangentValue_pushforwardTheta_obj (hF : F.IsEquivalence) {Θ : Obj → ℚ}
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hind : X.HasIndependentTangentSums Θ) (x : Obj) :
    Y.tangentValue (F.pushforwardTheta Θ) (F.obj x) =
      (X.tangentValue Θ x).mapDomain (image F.tangent.obj) := by
  by_cases hx : x ∈ supp Θ
  · obtain ⟨B⟩ := hΘ.localBranching x hx
    obtain ⟨U, V, g, hxU, hd⟩ := hF.isLocalScDiffeo_obj x
    have hΘU := pushforwardTheta_obj_eqOn hF hΘ.isFunctorial U
    rw [Y.tangentValue_eq (hasIndependentTangentSums_pushforwardTheta hF hΘ.isFunctorial hind)
      (B.mapDiffeo hd hxU rfl hΘU), B.tangentSum_mapDiffeo hd hxU rfl hΘU,
      X.tangentValue_eq hind B]
    refine Finsupp.mapDomain_congr fun L hL => image_congr fun α hα => ?_
    refine (tangent_obj_eq_tangentMapOn hd ?_).symm
    change _ ∈ U
    rw [B.tangentSum_mem.2 L hL α hα]
    exact hxU
  · have hy : F.obj x ∉ supp (F.pushforwardTheta Θ) := by
      change ¬ 0 < F.pushforwardTheta Θ (F.obj x)
      rw [pushforwardTheta_obj hF.full hΘ.isFunctorial]
      exact hx
    rw [Y.tangentValue_eq_zero hy, X.tangentValue_eq_zero hx, Finsupp.mapDomain_zero]

/-- **`T(F_*Θ)(y) = Tψ ∘ TF(TΘ(x))`** for `ψ : F(x) → y` (the formal sums are moved by the linear
sc-isomorphism `Tψ ∘ TF(x) : T_xX → T_yY` of (11.8)). -/
theorem tangentValue_pushforwardTheta (hF : F.IsEquivalence) {Θ : Obj → ℚ}
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hind : X.HasIndependentTangentSums Θ) {x : Obj}
    {ψ : Mor'} (hs : Y.src ψ = F.obj x) :
    Y.tangentValue (F.pushforwardTheta Θ) (Y.tgt ψ) =
      (X.tangentValue Θ x).mapDomain (image (Y.tangentMor ψ ∘ F.tangent.obj)) := by
  rw [← Y.grPush_tangentValue (isBranchedEpSubgroupoid_pushforwardTheta hF hΘ)
    (hasIndependentTangentSums_pushforwardTheta hF hΘ.isFunctorial hind) ψ, hs,
    tangentValue_pushforwardTheta_obj hF hΘ hind, grPush, ← Finsupp.mapDomain_comp,
    Set.image_comp_eq]

/-- **`T(F^*Θ')(x) = TF(x)⁻¹(TΘ'(F(x)))`**, read with a local inverse `g` of `F`:
`T(F^*Θ')(x) = Tg(TΘ'(F(x)))`. -/
theorem tangentValue_pullbackTheta (hF : F.IsEquivalence) {Θ' : Obj' → ℚ}
    (hΘ' : Y.IsBranchedEpSubgroupoid Θ') (hind' : Y.HasIndependentTangentSums Θ') {x : Obj}
    {U : Set Obj} {V : Set Obj'} {g : Obj' → Obj} (hd : X.PObj.IsScDiffeoOn Y.PObj F.obj g U V)
    (hxU : x ∈ U) :
    X.tangentValue (F.pullbackTheta Θ') x =
      (Y.tangentValue Θ' (F.obj x)).mapDomain (image (tangentMapOn hd.isScSmoothOn_inv)) := by
  have hΘ : ∀ v ∈ V, F.pullbackTheta Θ' (g v) = Θ' v := fun v hv => by
    simp only [pullbackTheta_apply, hd.right_inv v hv]
  have hgx : g (F.obj x) = x := hd.left_inv x hxU
  by_cases hx : F.obj x ∈ supp Θ'
  · obtain ⟨B⟩ := hΘ'.localBranching _ hx
    rw [X.tangentValue_eq (hasIndependentTangentSums_pullbackTheta hF hind')
      (B.mapDiffeo hd.symm (hd.mapsTo hxU) hgx hΘ), B.tangentSum_mapDiffeo hd.symm _ hgx hΘ,
      Y.tangentValue_eq hind' B]
  · have hy : x ∉ supp (F.pullbackTheta Θ') := hx
    rw [X.tangentValue_eq_zero hy, Y.tangentValue_eq_zero hx, Finsupp.mapDomain_zero]

/-- **2021 Theorem 11.3.7 for an equivalence, push-forward** (p. 541 (2017: Theorem 11.5)):
`(TF)_* TΘ = T(F_*Θ)` for the tangent `TF : TX → TY` (an equivalence, Theorem 10.1.7), `TΘ` of
Definition 9.2.12. -/
theorem tangentTheta_pushforwardTheta (hF : F.IsEquivalence) {Θ : Obj → ℚ}
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hind : X.HasIndependentTangentSums Θ) :
    F.tangent.pushforwardTheta (X.tangentTheta Θ) = Y.tangentTheta (F.pushforwardTheta Θ) := by
  have hTF := theorem_10_1_7 hF
  have hb := isBranchedEpSubgroupoid_pushforwardTheta hF hΘ
  have hind' := hasIndependentTangentSums_pushforwardTheta hF hΘ.isFunctorial hind
  funext v
  obtain ⟨a, k, hs, ht⟩ := hTF.exists_iso v
  rw [pushforwardTheta_eq hTF.full (X.isFunctorial_tangentTheta hΘ hind) ⟨k, hs, ht⟩,
    ← (Y.isFunctorial_tangentTheta hb hind').eq_of_isomorphic ⟨k, hs, ht⟩]
  obtain ⟨U, V, g, hxU, hd⟩ := hF.isLocalScDiffeo_obj (X.PObj.levelVal 1 (X.PObj.tangentProj a))
  rw [tangent_obj_eq_tangentMapOn hd hxU]
  exact (tangentTheta_tangentMapOn hd (pushforwardTheta_obj_eqOn hF hΘ.isFunctorial U) hΘ hind
    hind' hxU).symm

/-- **2021 Theorem 11.3.7 for an equivalence, pull-back**: `(TF)^* TΘ' = T(F^*Θ')`. -/
theorem tangentTheta_pullbackTheta (hF : F.IsEquivalence) {Θ' : Obj' → ℚ}
    (hΘ' : Y.IsBranchedEpSubgroupoid Θ') (hind' : Y.HasIndependentTangentSums Θ') :
    F.tangent.pullbackTheta (Y.tangentTheta Θ') = X.tangentTheta (F.pullbackTheta Θ') := by
  funext a
  obtain ⟨U, V, g, hxU, hd⟩ := hF.isLocalScDiffeo_obj (X.PObj.levelVal 1 (X.PObj.tangentProj a))
  have hΘ : ∀ v ∈ V, F.pullbackTheta Θ' (g v) = Θ' v := fun v hv => by
    simp only [pullbackTheta_apply, hd.right_inv v hv]
  have hβ : F.tangent.obj a ∈ Y.PObj.tangentPreimage V := by
    rw [tangent_obj_eq_tangentMapOn hd hxU]
    exact tangentMapOn_mapsTo hd.isScSmoothOn hd.mapsTo hxU
  have h1 := tangentTheta_tangentMapOn hd.symm hΘ hΘ' hind'
    (hasIndependentTangentSums_pullbackTheta hF hind') hβ
  rw [pullbackTheta_apply, ← h1, tangent_obj_eq_tangentMapOn hd hxU]
  exact congrArg _ (hd.tangent.left_inv a hxU)

/-- **2021 Theorem 11.3.8 for an equivalence, (11.11) push-forward** (p. 541 (2017: Theorem
11.6)): `F_*(∂Θ) = ∂(F_*Θ)` for the boundary `∂Θ` of Definition 9.2.16. -/
theorem boundaryTheta_pushforwardTheta (hF : F.IsEquivalence) {Θ : Obj → ℚ}
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hind : X.HasIndependentTangentSums Θ) :
    F.pushforwardTheta (X.boundaryTheta Θ) = Y.boundaryTheta (F.pushforwardTheta Θ) := by
  have hind' := hasIndependentTangentSums_pushforwardTheta hF hΘ.isFunctorial hind
  funext y
  obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso y
  obtain ⟨T, -⟩ := exists_transportChart hF.isLocalScDiffeo_obj hs ht
  rw [pushforwardTheta_eq hF.full (X.isFunctorial_boundaryTheta hΘ hind) ⟨ψ, hs, ht⟩, ← T.Q_self,
    boundaryTheta_apply_of_isScDiffeoOn T.isScDiffeoOn_Q (pushforwardTheta_Q hF hΘ.isFunctorial T)
      hΘ hind hind' T.mem_W]

/-- **2021 Theorem 11.3.8 for an equivalence, (11.11) pull-back**: `F^*(∂Θ') = ∂(F^*Θ')`. -/
theorem boundaryTheta_pullbackTheta (hF : F.IsEquivalence) {Θ' : Obj' → ℚ}
    (hΘ' : Y.IsBranchedEpSubgroupoid Θ') (hind' : Y.HasIndependentTangentSums Θ') :
    F.pullbackTheta (Y.boundaryTheta Θ') = X.boundaryTheta (F.pullbackTheta Θ') := by
  funext x
  obtain ⟨U, V, g, hxU, hd⟩ := hF.isLocalScDiffeo_obj x
  have hΘ : ∀ v ∈ V, F.pullbackTheta Θ' (g v) = Θ' v := fun v hv => by
    simp only [pullbackTheta_apply, hd.right_inv v hv]
  have h := boundaryTheta_apply_of_isScDiffeoOn hd.symm hΘ hΘ' hind'
    (hasIndependentTangentSums_pullbackTheta hF hind') (hd.mapsTo hxU)
  rw [hd.left_inv x hxU] at h
  exact h.symm

end EpFunctor

end Equivalence

/-! ### Generalized isomorphisms: Theorems 11.3.7 and 11.3.8 -/

namespace EPLocalization

open EpFunctor EpGroupoid CategoryTheory

namespace EPLoc

variable {X Y : EP.{u}}

/-- Theorem 9.2.1's independence is carried by `f_* = Φ_* F^*`. -/
theorem hasIndependentTangentSums_pushTheta {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ : X.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) (hind : X.X.HasIndependentTangentSums Θ) :
    Y.X.HasIndependentTangentSums (pushTheta f Θ) :=
  hasIndependentTangentSums_pushforwardTheta (isEquivalence_rep_Φ hf)
    ((rep f).F.isFunctorial_pullbackTheta hΘ)
    (hasIndependentTangentSums_pullbackTheta (rep f).isEquivalence_F hind)

/-- Theorem 9.2.1's independence is carried by `f^* = F_* Φ^*`. -/
theorem hasIndependentTangentSums_pullTheta {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsFunctorial Θ') (hind' : Y.X.HasIndependentTangentSums Θ') :
    X.X.HasIndependentTangentSums (pullTheta f Θ') :=
  hasIndependentTangentSums_pushforwardTheta (rep f).isEquivalence_F
    ((rep f).Φ.isFunctorial_pullbackTheta hΘ')
    (hasIndependentTangentSums_pullbackTheta (isEquivalence_rep_Φ hf) hind')

/-- **2021 Theorem 11.3.8, (11.11) first line** (p. 541 (2017: Theorem 11.6)): for a generalized
isomorphism `f : X → Y` and a branched ep⁺-subgroupoid `Θ` (with Theorem 9.2.1's independence),
`f_*(∂Θ) = ∂(f_*Θ)`. -/
theorem theorem_11_3_8_push {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ : X.Obj → ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hind : X.X.HasIndependentTangentSums Θ) :
    pushTheta f (X.X.boundaryTheta Θ) = Y.X.boundaryTheta (pushTheta f Θ) := by
  have hF := (rep f).isEquivalence_F
  unfold pushTheta Diagram.pushTheta
  rw [boundaryTheta_pullbackTheta hF hΘ hind,
    boundaryTheta_pushforwardTheta (isEquivalence_rep_Φ hf)
    (isBranchedEpSubgroupoid_pullbackTheta hF hΘ) (hasIndependentTangentSums_pullbackTheta hF hind)]

/-- **2021 Theorem 11.3.8, (11.11) second line**: `f^*(∂Θ') = ∂(f^*Θ')`. -/
theorem theorem_11_3_8_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hind' : Y.X.HasIndependentTangentSums Θ') :
    pullTheta f (Y.X.boundaryTheta Θ') = X.X.boundaryTheta (pullTheta f Θ') := by
  have hd := isEquivalence_rep_Φ hf
  unfold pullTheta Diagram.pullTheta
  rw [boundaryTheta_pullbackTheta hd hΘ' hind', boundaryTheta_pushforwardTheta
    (rep f).isEquivalence_F (isBranchedEpSubgroupoid_pullbackTheta hd hΘ')
    (hasIndependentTangentSums_pullbackTheta hd hind')]

end EPLoc

namespace EPLoc

variable {X Y : EP.{max u 1}}

/-- `T[d] = [Td]` on the chosen representative. -/
theorem tangentFunctor_map_eq (f : of X ⟶ of Y) :
    tangentFunctor.map f = homMk (rep f).tangent := by
  conv_lhs => rw [← homMk_rep f]
  rfl

/-- **2021 Theorem 11.3.7, first identity** (p. 541 (2017: Theorem 11.5)): for a generalized
isomorphism `f : X → Y` with tangent `Tf = [TX ←TF TA →TΦ TY]` (Theorem 11.1.1,
`EPLoc.tangentFunctor`) and a branched ep⁺-subgroupoid `Θ` (with Theorem 9.2.1's independence),
`(Tf)_* TΘ = T(f_*Θ)`. -/
theorem theorem_11_3_7_push {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ : X.Obj → ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hind : X.X.HasIndependentTangentSums Θ) :
    pushTheta (X := X.tangent) (Y := Y.tangent) (tangentFunctor.map f) (X.X.tangentTheta Θ) =
      Y.X.tangentTheta (pushTheta f Θ) := by
  have hd := isEquivalence_rep_Φ hf
  have hF := (rep f).isEquivalence_F
  rw [tangentFunctor_map_eq]
  refine (pushTheta_homMk (X := X.tangent) (Y := Y.tangent) (rep f).tangent (theorem_10_1_7 hd)
    (Θ := X.X.tangentTheta Θ) (X.X.isFunctorial_tangentTheta hΘ hind)).trans ?_
  change (rep f).Φ.tangent.pushforwardTheta ((rep f).F.tangent.pullbackTheta
    (X.X.tangentTheta Θ)) = _
  rw [tangentTheta_pullbackTheta hF hΘ hind, tangentTheta_pushforwardTheta hd
    (isBranchedEpSubgroupoid_pullbackTheta hF hΘ) (hasIndependentTangentSums_pullbackTheta hF hind)]
  rfl

/-- **2021 Theorem 11.3.7, second identity**: `(Tf)^* TΘ' = T(f^*Θ')`. -/
theorem theorem_11_3_7_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hind' : Y.X.HasIndependentTangentSums Θ') :
    pullTheta (X := X.tangent) (Y := Y.tangent) (tangentFunctor.map f) (Y.X.tangentTheta Θ') =
      X.X.tangentTheta (pullTheta f Θ') := by
  have hd := isEquivalence_rep_Φ hf
  have hF := (rep f).isEquivalence_F
  rw [tangentFunctor_map_eq]
  refine (pullTheta_homMk (X := X.tangent) (Y := Y.tangent) (rep f).tangent
    (Θ' := Y.X.tangentTheta Θ') (Y.X.isFunctorial_tangentTheta hΘ' hind')).trans ?_
  change (rep f).F.tangent.pushforwardTheta ((rep f).Φ.tangent.pullbackTheta
    (Y.X.tangentTheta Θ')) = _
  rw [tangentTheta_pullbackTheta hd hΘ' hind', tangentTheta_pushforwardTheta hF
    (isBranchedEpSubgroupoid_pullbackTheta hd hΘ')
    (hasIndependentTangentSums_pullbackTheta hd hind')]
  rfl

end EPLoc

end EPLocalization

end Polyfold
