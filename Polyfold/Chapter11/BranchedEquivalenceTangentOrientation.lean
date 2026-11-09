import Polyfold.Chapter11.BranchedEquivalenceTangentSection
import Polyfold.Chapter9.OrientationBoundary

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.3 "Branched Ep⁺-Subgroupoids and Equivalences" (pp. 539–542; 2017:
pp. 393–396): **Theorem 11.3.5**, **Definition 11.3.6**, (11.10) and **Theorem 11.3.9** (2017:
Theorem 11.5, Definition 11.6, (11.10), Theorem 11.8).  Numbers and pages are the 2021 text's.

# Orientations along generalized isomorphisms

## The text, paraphrased

(Theorem 11.3.5, p. 539) For a generalized isomorphism `f : X → Y` and oriented branched
ep⁺-subgroupoids `(Θ, T̂_Θ)` on `X`, `(Θ', T̂_Θ')` on `Y`, `f_* T̂_Θ` orients `f_*Θ` and `f^* T̂_Θ'`
orients `f^*Θ'`.  *Proof* (text): for an equivalence `F`, `y ∈ Y_∞`, `ψ : F(x) → y`, an oriented
local branching structure `(Mᵢ, oᵢ), (σᵢ)` at `x` is mapped by `ψ̂ ∘ F` with the same weights, and
`F_* T̂_Θ` is the resulting oriented sum near `y`; for `F^*` one takes preimages under a local
sc-diffeomorphism `F : U(x) → V(F(x))`.  (Definition 11.3.6, p. 541) `f_*Θ̂ = (f_*Θ, f_* T̂_Θ)`,
`f^*Θ̂' = (f^*Θ', f^* T̂_Θ')`, and (11.10) `(g ∘ f)_* = g_* ∘ f_*`, `(g ∘ f)^* = f^* ∘ g^*`.
(Theorem 11.3.9, p. 542) For oriented tame `Θ̂`, `Θ̂'`: `∂(f_*Θ̂) = f_*(∂Θ̂)` and
`∂(f^*Θ̂') = f^*(∂Θ̂')`; proof left to the reader.

## What is formalized

* `EpFunctor.TransportChart.tangentMor_ψ_tangent_obj`: `Tψ_u ∘ TF = T(ψ̂ ∘ F)` on `T_uX`.
* Theorem 11.3.5 for equivalences (`isOrientation_pushSection`, `isOrientation_pullSection`) and
  for generalized isomorphisms (`theorem_11_3_5_push`, `theorem_11_3_5_pull`).
* Definition 11.3.6: `EPLocalization.OrientedBranched` and its `push`, `pull`; (11.10):
  `OrientedBranched.push_comp`, `pull_comp`; also `pull_push`.
* Theorem 11.3.9 under a boundary-transfer hypothesis (`MPolyfold.IsBoundaryTransfer`):
  `EpFunctor.pushSection_boundaryLift`, `pullSection_boundaryLift`, and for a representative
  diagram `EPLoc.theorem_11_3_9_push`, `theorem_11_3_9_pull` (with Theorem 11.3.8 for `∂Θ`).
* Witnesses: `(Θ, T̂¹)` of Example 9.3.5 as an `OrientedBranched`, its push-forward along the
  identity generalized isomorphism, and the boundary-transfer hypothesis along the identity.

## Choices

* As in Chapter 9, Theorem 9.2.1's independence of the tangent sums is a hypothesis on `Θ` (part
  of `OrientedBranched`); it is carried by `f_*` and `f^*` (`BranchedEquivalenceTangent.lean`).
* `T̂_{∂Θ}` is Chapter 9's `boundaryLift bd T̂_Θ` with the boundary operation `bd` as data, so
  Theorem 11.3.9 is stated for a representative `X ←F A →Φ Y` and boundary operations on `X`, `A`,
  `Y` that the transfer maps `Tψ ∘ TF(a)` and `TF(a)⁻¹` carry into each other, preserving the
  degree `d_M = 1` (`IsBoundaryTransfer`, the text's "`d_M(x)` is being preserved").

## Not formalized, and why

* That the boundary operations of Definition 9.3.8 satisfy `IsBoundaryTransfer` along
  equivalences, i.e. that sc-diffeomorphisms between different M-polyfolds preserve tame induced
  structures, `d_M` and outward vectors: `bd` itself is data in Chapter 9 (the partial cones of
  submanifolds are not formalized).  Hence also no version of Theorem 11.3.9 independent of the
  representative.
-/

set_option maxSynthPendingDepth 3

open Set Function Module Submodule

noncomputable section

namespace Polyfold

universe u v

/-! ### Boundary operations moved by fibre maps -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

variable (P Q) in
/-- **The boundary operations `bd` at `x` and `bd'` at `y` correspond under `f : T_xX → T_yY`**
(the content of "`d_M(x)` is being preserved", 2021 p. 541, for the boundary operations of
Definition 9.3.10): `f` preserves the degree `1` of oriented tangent spaces and
`bd'(f_* L) = f_*(bd L)` in degree `1`. -/
def IsBoundaryTransfer (x : X) (y : Y) (f : P.TangentSpace → Q.TangentSpace)
    (bd : OrTangent P → OrTangent P) (bd' : OrTangent Q → OrTangent Q) : Prop :=
  ∀ g : OrTangent P, P.IsOrientedAt x g →
    (Q.HasSubDegree y 1 (g.map f) ↔ P.HasSubDegree x 1 g) ∧
      (P.HasSubDegree x 1 g → bd' (g.map f) = (bd g).map f)

/-- The identity transfers every boundary operation to itself (satisfiability). -/
theorem isBoundaryTransfer_id (x : X) (bd : OrTangent P → OrTangent P) :
    P.IsBoundaryTransfer P x x id bd bd := fun g _ =>
  ⟨by simp only [OrTangent.map_id], fun _ => by simp only [OrTangent.map_id]⟩

end MPolyfold

section Equivalence

variable {Obj Mor Obj' Mor' : Type u}
  [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

open MPolyfold

namespace EpGroupoid

open scoped Classical in
/-- The degree-`1` part and the boundary operation commute with a fibre map that transfers them. -/
theorem mapDomain_boundary_mapDomain_map {x : Obj} {y : Obj'} {w : X.PObj.OrTangent →₀ ℚ}
    (hw : w ∈ X.GrHat x) {f : X.PObj.TangentSpace → Y.PObj.TangentSpace}
    {bd : X.PObj.OrTangent → X.PObj.OrTangent} {bd' : Y.PObj.OrTangent → Y.PObj.OrTangent}
    (hbd : X.PObj.IsBoundaryTransfer Y.PObj x y f bd bd') :
    ((X.degreePart x 1 w).mapDomain bd).mapDomain (OrTangent.map f) =
      (Y.degreePart y 1 (w.mapDomain (OrTangent.map f))).mapDomain bd' := by
  conv_lhs => rw [← Finsupp.sum_single w]
  conv_rhs => rw [← Finsupp.sum_single w]
  simp only [Finsupp.sum, degreePart, Finsupp.mapDomain_finsetSum, Finsupp.filter_sum,
    Finsupp.mapDomain_single]
  refine Finset.sum_congr rfl fun g hg => ?_
  obtain ⟨hdeg, hb⟩ := hbd g (hw.2 g hg)
  by_cases h1 : X.PObj.HasSubDegree x 1 g
  · rw [Finsupp.filter_single_of_pos _ h1, Finsupp.filter_single_of_pos _ (hdeg.2 h1),
      Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hb h1]
  · rw [Finsupp.filter_single_of_neg _ h1,
      Finsupp.filter_single_of_neg _ fun h => h1 (hdeg.1 h), Finsupp.mapDomain_zero,
      Finsupp.mapDomain_zero, Finsupp.mapDomain_zero]

theorem boundaryLift_of_eq_zero {bd : X.PObj.OrTangent → X.PObj.OrTangent}
    {T : Obj → X.PObj.OrTangent →₀ ℚ} {y : Obj} (h : T y = 0) : X.boundaryLift bd T y = 0 := by
  rw [boundaryLift, h, degreePart, Finsupp.filter_zero, Finsupp.mapDomain_zero]

end EpGroupoid

namespace EpFunctor

open EpGroupoid

variable {F : EpFunctor X Y}

/-! ### The transport chart moves tangent vectors by `Tψ ∘ TF` -/

/-- **`Tψ_u ∘ TF = TQ` on `T_uX`, `u ∈ W`**, for the chart `Q = ψ̂ ∘ F` of a transport chart
(the morphisms `ψ_u : F(u) → Q(u)` depend sc-smoothly on `u`). -/
theorem TransportChart.tangentMor_ψ_tangent_obj {x : Obj} {y : Obj'} (T : F.TransportChart x y)
    {α : X.PObj.TangentSpace} (hα : α ∈ X.PObj.tangentPreimage T.W) :
    Y.tangentMor (T.ψ (X.PObj.levelVal 1 (X.PObj.tangentProj α))) (F.tangent.obj α) =
      tangentMapOn T.isScDiffeoOn_Q.isScSmoothOn α := by
  have hb : Y.tBase (tangentMapOn T.isScSmoothOn_ψ α) =
      T.ψ (X.PObj.levelVal 1 (X.PObj.tangentProj α)) :=
    levelVal_tangentProj_tangentMapOn T.isScSmoothOn_ψ hα
  have hs : Y.tSrc (tangentMapOn T.isScSmoothOn_ψ α) = F.tangent.obj α :=
    tangentMap_tangentMapOn_of_eqOn T.isScSmoothOn_ψ Y.isScSmoothMap_src F.isScSmoothMap_obj
      (fun u hu => T.src_ψ u hu) hα
  have ht : Y.tTgt (tangentMapOn T.isScSmoothOn_ψ α) =
      tangentMapOn T.isScDiffeoOn_Q.isScSmoothOn α := by
    change MPolyfold.tangentMap Y.isScSmoothMap_tgt (tangentMapOn T.isScSmoothOn_ψ α) = _
    rw [tangentMap_tangentMapOn Y.isScSmoothMap_tgt T.isScSmoothOn_ψ hα]
    exact tangentMapOn_congr _ _ T.isScSmoothOn_ψ.isOpen subset_rfl subset_rfl
      (fun u hu => T.tgt_ψ u hu) hα
  rw [← hb, ← hs, Y.tangentMor_tSrc, ht]

/-! ### Theorem 11.3.5 for equivalences -/

/-- **Theorem 11.3.5 for an equivalence, push-forward** (2021 pp. 539–540): `F_* T̂_Θ` is an
orientation of `F_*Θ`.  An oriented branching structure at `x` representing `T̂_Θ` is moved by
`ψ̂ ∘ F` (`OrientedBranchingStructure.mapDiffeo` along a transport chart). -/
theorem isOrientation_pushSection (hF : F.IsEquivalence) {Θ : Obj → ℚ}
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) (hT : X.IsOrientation Θ T) :
    Y.IsOrientation (F.pushforwardTheta Θ) (F.pushSection T) := by
  have hd := hF.isLocalScDiffeo_obj
  have hfun := hΘ.isFunctorial
  have hS := isGrHatSection_pushSection hF hT.isGrHatSection
  refine IsOrientation.mk' (hasIndependentTangentSums_pushforwardTheta hF hfun hind) hS.mem
    hS.natural (fun y hy hys => ?_) fun y hy => ?_
  · obtain ⟨x, ψ, hs, rfl⟩ := hF.exists_iso y
    have hxs : x ∈ X.PObj.smoothSet :=
      (hd.mem_smoothSet_iff x).1 (hs ▸ Y.src_mem_smoothSet_of_tgt hy)
    have hΘx : F.pushforwardTheta Θ (Y.tgt ψ) = Θ x := pushforwardTheta_eq hF.full hfun ⟨ψ, hs, rfl⟩
    rw [pushSection_eq hF hT.isGrHatSection hs hy,
      hT.eq_zero_of_not_mem hxs fun h =>
        hys (show 0 < F.pushforwardTheta Θ (Y.tgt ψ) by rw [hΘx]; exact h),
      Finsupp.mapDomain_zero]
  · obtain ⟨x, ψ, hs, rfl⟩ := hF.exists_iso y
    have hΘx : F.pushforwardTheta Θ (Y.tgt ψ) = Θ x := pushforwardTheta_eq hF.full hfun ⟨ψ, hs, rfl⟩
    have hx : x ∈ supp Θ := show 0 < Θ x by rw [← hΘx]; exact hy
    obtain ⟨B, hB⟩ := hT.locallyOriented x hx
    obtain ⟨C, -⟩ := exists_transportChart hd hs rfl
    refine ⟨B.mapDiffeo C.isScDiffeoOn_Q C.mem_W C.Q_self (pushforwardTheta_Q hF hfun C),
      fun z hz hzs => ?_⟩
    rw [B.orientedSum_mapDiffeo C.isScDiffeoOn_Q C.mem_W C.Q_self (pushforwardTheta_Q hF hfun C)
      hz]
    obtain ⟨hzW', hzU, hzW⟩ := hz
    have htu : Y.tgt (C.ψ (C.Qinv z)) = z :=
      (C.tgt_ψ _ hzW).trans (C.isScDiffeoOn_Q.right_inv z hzW')
    have hsu := C.src_ψ _ hzW
    have hzs' : Y.tgt (C.ψ (C.Qinv z)) ∈ Y.PObj.smoothSet := by rw [htu]; exact hzs
    have hus : C.Qinv z ∈ X.PObj.smoothSet :=
      (hd.mem_smoothSet_iff _).1 (hsu ▸ Y.src_mem_smoothSet_of_tgt hzs')
    calc F.pushSection T z = F.pushSection T (Y.tgt (C.ψ (C.Qinv z))) := by rw [htu]
      _ = (T (C.Qinv z)).mapDomain
          (OrTangent.map (Y.tangentMor (C.ψ (C.Qinv z)) ∘ F.tangent.obj)) :=
        pushSection_eq hF hT.isGrHatSection hsu hzs'
      _ = (B.orientedSum (C.Qinv z)).mapDomain
          (OrTangent.map (Y.tangentMor (C.ψ (C.Qinv z)) ∘ F.tangent.obj)) := by
        rw [hB _ hzU hus]
      _ = _ := mapDomain_map_congr (B.orientedSum_mem _) fun α hα => by
        have h := C.tangentMor_ψ_tangent_obj (α := α)
          (show _ ∈ C.W by rw [hα]; exact hzW)
        rw [hα] at h
        exact h

/-- **Theorem 11.3.5 for an equivalence, pull-back** (2021 p. 540): `F^* T̂_Θ'` is an orientation
of `F^*Θ'`; an oriented branching structure at `F(x)` is moved back by a local inverse of `F`. -/
theorem isOrientation_pullSection (hF : F.IsEquivalence) {Θ' : Obj' → ℚ}
    {T' : Obj' → Y.PObj.OrTangent →₀ ℚ} (hind' : Y.HasIndependentTangentSums Θ')
    (hT' : Y.IsOrientation Θ' T') :
    X.IsOrientation (F.pullbackTheta Θ') (F.pullSection T') := by
  have hd := hF.isLocalScDiffeo_obj
  have hS := isGrHatSection_pullSection hd hT'.isGrHatSection
  refine IsOrientation.mk' (hasIndependentTangentSums_pullbackTheta hF hind') hS.mem hS.natural
    (fun x hx hxs => ?_) fun x hx => ?_
  · rw [pullSection_of_mem hx, hT'.eq_zero_of_not_mem ((hd.mem_smoothSet_iff x).2 hx)
      fun h => hxs (show 0 < F.pullbackTheta Θ' x by rw [pullbackTheta_apply]; exact h),
      Finsupp.mapDomain_zero]
  · have hFx : F.obj x ∈ supp Θ' := by
      have h : 0 < F.pullbackTheta Θ' x := hx
      rwa [pullbackTheta_apply] at h
    obtain ⟨B', hB'⟩ := hT'.locallyOriented _ hFx
    obtain ⟨U, V, g, hxU, hdF⟩ := hd x
    have hΘ : ∀ v ∈ V, F.pullbackTheta Θ' (g v) = Θ' v := fun v hv => by
      simp only [pullbackTheta_apply, hdF.right_inv v hv]
    refine ⟨B'.mapDiffeo hdF.symm (hdF.mapsTo hxU) (hdF.left_inv x hxU) hΘ, fun z hz hzs => ?_⟩
    rw [B'.orientedSum_mapDiffeo hdF.symm (hdF.mapsTo hxU) (hdF.left_inv x hxU) hΘ hz]
    obtain ⟨hzU, hFzU', -⟩ := hz
    have hFzs : F.obj z ∈ Y.PObj.smoothSet := (hd.mem_smoothSet_iff z).2 hzs
    rw [pullSection_of_mem hzs, hB' (F.obj z) hFzU' hFzs]
    exact mapDomain_map_congr (B'.orientedSum_mem _) fun β hβ =>
      fibreInv_eq_tangentMapOn hd hdF hzU hβ

/-! ### Theorem 11.3.9 for equivalences, under the boundary-transfer hypothesis -/

/-- **Theorem 11.3.9 for an equivalence, push-forward, orientation part**: if the transfer maps
`Tψ ∘ TF(x)` carry `bd` to `bd'`, then `F_* T̂_{∂Θ} = T̂_{∂(F_*Θ)}`. -/
theorem pushSection_boundaryLift {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsGrHatSection T)
    {bd : X.PObj.OrTangent → X.PObj.OrTangent} {bd' : Y.PObj.OrTangent → Y.PObj.OrTangent}
    (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj)
    (hbd : ∀ x ∈ X.PObj.smoothSet, ∀ ψ : Mor', Y.src ψ = F.obj x →
      X.PObj.IsBoundaryTransfer Y.PObj x (Y.tgt ψ) (Y.tangentMor ψ ∘ F.tangent.obj) bd bd') :
    F.pushSection (X.boundaryLift bd T) = Y.boundaryLift bd' (F.pushSection T) := by
  classical
  funext y
  rw [boundaryLift]
  unfold pushSection
  split_ifs with h
  · obtain ⟨hs, ht⟩ := h.2.choose_spec
    have hy' : Y.tgt h.2.choose.2 ∈ Y.PObj.smoothSet := by rw [ht]; exact h.1
    have hxs : h.2.choose.1 ∈ X.PObj.smoothSet :=
      (hF.mem_smoothSet_iff _).1 (hs ▸ Y.src_mem_smoothSet_of_tgt hy')
    have := mapDomain_boundary_mapDomain_map (hT.mem _ hxs) (ht ▸ hbd _ hxs _ hs)
    rw [boundaryLift]
    convert this using 3
  · rw [degreePart, Finsupp.filter_zero, Finsupp.mapDomain_zero]

/-- **Theorem 11.3.9 for an equivalence, pull-back, orientation part**: if the fibre inverses
`TF(x)⁻¹` carry `bd'` to `bd`, then `F^* T̂_{∂Θ'} = T̂_{∂(F^*Θ')}`. -/
theorem pullSection_boundaryLift {T' : Obj' → Y.PObj.OrTangent →₀ ℚ}
    (hT' : Y.IsGrHatSection T') (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj)
    {bd : X.PObj.OrTangent → X.PObj.OrTangent} {bd' : Y.PObj.OrTangent → Y.PObj.OrTangent}
    (hbd : ∀ x ∈ X.PObj.smoothSet,
      Y.PObj.IsBoundaryTransfer X.PObj (F.obj x) x (fibreInv F.tangent.obj x) bd' bd) :
    F.pullSection (Y.boundaryLift bd' T') = X.boundaryLift bd (F.pullSection T') := by
  funext x
  by_cases hx : x ∈ X.PObj.smoothSet
  · rw [pullSection_of_mem hx, boundaryLift, boundaryLift, pullSection_of_mem hx]
    exact mapDomain_boundary_mapDomain_map (hT'.mem _ ((hF.mem_smoothSet_iff x).2 hx))
      (hbd x hx)
  · rw [pullSection_of_not_mem hx, boundaryLift_of_eq_zero (pullSection_of_not_mem hx)]

end EpFunctor

end Equivalence

/-! ### Theorem 11.3.5, Definition 11.3.6, (11.10), Theorem 11.3.9 -/

namespace EPLocalization

open EpFunctor EpGroupoid MPolyfold CategoryTheory

namespace EPLoc

variable {X Y Z : EP.{u}}

/-- **Theorem 11.3.5, push-forward** (2021 p. 539): for a generalized isomorphism `f` and an
oriented branched ep⁺-subgroupoid `(Θ, T̂_Θ)` on `X`, `f_* T̂_Θ` is an orientation of `f_*Θ`
(Theorem 9.2.1's independence of the tangent sums of `Θ` is assumed, as in Chapter 9). -/
theorem theorem_11_3_5_push {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ : X.Obj → ℚ}
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ)
    (hind : X.X.HasIndependentTangentSums Θ) (hT : X.X.IsOrientation Θ T) :
    Y.X.IsOrientation (pushTheta f Θ) (pushSection f T) :=
  isOrientation_pushSection (isEquivalence_rep_Φ hf)
    (isBranchedEpSubgroupoid_pullbackTheta (rep f).isEquivalence_F hΘ)
    (hasIndependentTangentSums_pullbackTheta (rep f).isEquivalence_F hind)
    (isOrientation_pullSection (rep f).isEquivalence_F hind hT)

/-- **Theorem 11.3.5, pull-back** (2021 p. 539): `f^* T̂_Θ'` is an orientation of `f^*Θ'`. -/
theorem theorem_11_3_5_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ')
    (hind' : Y.X.HasIndependentTangentSums Θ') (hT' : Y.X.IsOrientation Θ' T') :
    X.X.IsOrientation (pullTheta f Θ') (pullSection f T') :=
  isOrientation_pushSection (rep f).isEquivalence_F
    (isBranchedEpSubgroupoid_pullbackTheta (isEquivalence_rep_Φ hf) hΘ')
    (hasIndependentTangentSums_pullbackTheta (isEquivalence_rep_Φ hf) hind')
    (isOrientation_pullSection (isEquivalence_rep_Φ hf) hind' hT')

end EPLoc

/-- **An oriented branched ep⁺-subgroupoid `Θ̂ = (Θ, T̂_Θ)`** (Definitions 9.3.2, 11.3.6) on an
ep-groupoid in `EP`, with Theorem 9.2.1's independence of its tangent sums (a hypothesis in
Chapter 9; `hasIndependentTangentSums_rn` discharges it on `ℝⁿ`). -/
structure OrientedBranched (X : EP.{u}) where
  /-- The branched ep⁺-subgroupoid `Θ`. -/
  Θ : X.Obj → ℚ
  /-- The orientation `T̂_Θ`. -/
  T : X.Obj → X.X.PObj.OrTangent →₀ ℚ
  isBranchedEpSubgroupoid : X.X.IsBranchedEpSubgroupoid Θ
  hasIndependentTangentSums : X.X.HasIndependentTangentSums Θ
  isOrientation : X.X.IsOrientation Θ T

namespace OrientedBranched

variable {X Y Z : EP.{u}}

theorem ext' {A B : OrientedBranched X} (hΘ : A.Θ = B.Θ) (hT : A.T = B.T) : A = B := by
  cases A; cases B; cases hΘ; cases hT; rfl

/-- **Definition 11.3.6, push-forward** (2021 p. 541): `f_*Θ̂ = (f_*Θ, f_* T̂_Θ)` for a
generalized isomorphism `f` (an oriented branched ep⁺-subgroupoid by Theorems 11.3.3, 11.3.5). -/
def push {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f) (A : OrientedBranched X) :
    OrientedBranched Y where
  Θ := EPLoc.pushTheta f A.Θ
  T := EPLoc.pushSection f A.T
  isBranchedEpSubgroupoid := isBranchedEpSubgroupoid_pushforwardTheta (EPLoc.isEquivalence_rep_Φ hf)
    (isBranchedEpSubgroupoid_pullbackTheta (EPLoc.rep f).isEquivalence_F A.isBranchedEpSubgroupoid)
  hasIndependentTangentSums := EPLoc.hasIndependentTangentSums_pushTheta hf
    A.isBranchedEpSubgroupoid.isFunctorial A.hasIndependentTangentSums
  isOrientation := EPLoc.theorem_11_3_5_push hf A.isBranchedEpSubgroupoid
    A.hasIndependentTangentSums A.isOrientation

/-- **Definition 11.3.6, pull-back** (2021 p. 541): `f^*Θ̂' = (f^*Θ', f^* T̂_Θ')`. -/
def pull {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f) (A : OrientedBranched Y) :
    OrientedBranched X where
  Θ := EPLoc.pullTheta f A.Θ
  T := EPLoc.pullSection f A.T
  isBranchedEpSubgroupoid := isBranchedEpSubgroupoid_pushforwardTheta (EPLoc.rep f).isEquivalence_F
    (isBranchedEpSubgroupoid_pullbackTheta (EPLoc.isEquivalence_rep_Φ hf)
      A.isBranchedEpSubgroupoid)
  hasIndependentTangentSums := EPLoc.hasIndependentTangentSums_pullTheta hf
    A.isBranchedEpSubgroupoid.isFunctorial A.hasIndependentTangentSums
  isOrientation := EPLoc.theorem_11_3_5_pull hf A.isBranchedEpSubgroupoid
    A.hasIndependentTangentSums A.isOrientation

/-- **(11.10), push-forward** (2021 p. 541): `(g ∘ f)_* Θ̂ = g_* f_* Θ̂`. -/
theorem push_comp {f : EPLoc.of X ⟶ EPLoc.of Y} {g : EPLoc.of Y ⟶ EPLoc.of Z}
    (hf : EPLoc.IsGeneralizedIso f) (hg : EPLoc.IsGeneralizedIso g)
    (hfg : EPLoc.IsGeneralizedIso (f ≫ g)) (A : OrientedBranched X) :
    push hfg A = push hg (push hf A) :=
  ext' (EPLoc.pushTheta_comp hf hg A.isBranchedEpSubgroupoid.isFunctorial)
    (EPLoc.pushSection_comp hf hg A.isOrientation.isGrHatSection)

/-- **(11.10), pull-back** (2021 p. 541): `(g ∘ f)^* Θ̂ = f^* g^* Θ̂`. -/
theorem pull_comp {f : EPLoc.of X ⟶ EPLoc.of Y} {g : EPLoc.of Y ⟶ EPLoc.of Z}
    (hf : EPLoc.IsGeneralizedIso f) (hg : EPLoc.IsGeneralizedIso g)
    (hfg : EPLoc.IsGeneralizedIso (f ≫ g)) (A : OrientedBranched Z) :
    pull hfg A = pull hf (pull hg A) :=
  ext' (EPLoc.pullTheta_comp f g A.isBranchedEpSubgroupoid.isFunctorial)
    (EPLoc.pullSection_comp hf hg A.isOrientation.isGrHatSection)

/-- `f^* f_* Θ̂ = Θ̂` for a generalized isomorphism. -/
theorem pull_push {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f)
    (A : OrientedBranched X) (hA : ∀ x, x ∉ X.X.PObj.smoothSet → A.T x = 0) :
    pull hf (push hf A) = A :=
  ext' (EPLoc.pullTheta_pushTheta hf A.isBranchedEpSubgroupoid.isFunctorial)
    (EPLoc.pullSection_pushSection hf ⟨A.isOrientation.isGrHatSection, hA⟩)

end OrientedBranched

namespace EPLoc

variable {X Y : EP.{u}}

/-- **Theorem 11.3.9, push-forward, for a representative** (2021 p. 541), under the
boundary-transfer hypotheses: for `d : X ←F A →Φ Y` with `Φ` an equivalence and a boundary
operation `bdA` on `A` such that `TF(a)⁻¹` carries `bd` to `bdA` and `Tψ ∘ TΦ(a)` carries `bdA`
to `bd'`, `d_*(∂Θ) = ∂(d_*Θ)` and `d_* T̂_{∂Θ} = T̂_{∂(d_*Θ)}`. -/
theorem theorem_11_3_9_push (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {Θ : X.Obj → ℚ}
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ)
    (hind : X.X.HasIndependentTangentSums Θ) (hT : X.X.IsOrientation Θ T)
    {bd : X.X.PObj.OrTangent → X.X.PObj.OrTangent} {bd' : Y.X.PObj.OrTangent → Y.X.PObj.OrTangent}
    {bdA : d.A.X.PObj.OrTangent → d.A.X.PObj.OrTangent}
    (hbdF : ∀ a ∈ d.A.X.PObj.smoothSet,
      X.X.PObj.IsBoundaryTransfer d.A.X.PObj (d.F.obj a) a (fibreInv d.F.tangent.obj a) bd bdA)
    (hbdΦ : ∀ a ∈ d.A.X.PObj.smoothSet, ∀ ψ : Y.Mor, Y.X.src ψ = d.Φ.obj a →
      d.A.X.PObj.IsBoundaryTransfer Y.X.PObj a (Y.X.tgt ψ) (Y.X.tangentMor ψ ∘ d.Φ.tangent.obj)
        bdA bd') :
    d.pushTheta (X.X.boundaryTheta Θ) = Y.X.boundaryTheta (d.pushTheta Θ) ∧
      d.pushSection (X.X.boundaryLift bd T) = Y.X.boundaryLift bd' (d.pushSection T) := by
  have hF := d.isEquivalence_F
  refine ⟨?_, ?_⟩
  · unfold Diagram.pushTheta
    rw [boundaryTheta_pullbackTheta hF hΘ hind,
      boundaryTheta_pushforwardTheta hΦ (isBranchedEpSubgroupoid_pullbackTheta hF hΘ)
        (hasIndependentTangentSums_pullbackTheta hF hind)]
  · unfold Diagram.pushSection
    rw [pullSection_boundaryLift hT.isGrHatSection hF.isLocalScDiffeo_obj hbdF,
      pushSection_boundaryLift (isGrHatSection_pullSection hF.isLocalScDiffeo_obj
        hT.isGrHatSection) hΦ.isLocalScDiffeo_obj hbdΦ]

/-- **Theorem 11.3.9, pull-back, for a representative** (2021 p. 541), under the
boundary-transfer hypotheses: `d^*(∂Θ') = ∂(d^*Θ')` and `d^* T̂_{∂Θ'} = T̂_{∂(d^*Θ')}`. -/
theorem theorem_11_3_9_pull (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ')
    (hind' : Y.X.HasIndependentTangentSums Θ') (hT' : Y.X.IsOrientation Θ' T')
    {bd : X.X.PObj.OrTangent → X.X.PObj.OrTangent} {bd' : Y.X.PObj.OrTangent → Y.X.PObj.OrTangent}
    {bdA : d.A.X.PObj.OrTangent → d.A.X.PObj.OrTangent}
    (hbdΦ : ∀ a ∈ d.A.X.PObj.smoothSet,
      Y.X.PObj.IsBoundaryTransfer d.A.X.PObj (d.Φ.obj a) a (fibreInv d.Φ.tangent.obj a) bd' bdA)
    (hbdF : ∀ a ∈ d.A.X.PObj.smoothSet, ∀ ψ : X.Mor, X.X.src ψ = d.F.obj a →
      d.A.X.PObj.IsBoundaryTransfer X.X.PObj a (X.X.tgt ψ) (X.X.tangentMor ψ ∘ d.F.tangent.obj)
        bdA bd) :
    d.pullTheta (Y.X.boundaryTheta Θ') = X.X.boundaryTheta (d.pullTheta Θ') ∧
      d.pullSection (Y.X.boundaryLift bd' T') = X.X.boundaryLift bd (d.pullSection T') := by
  have hF := d.isEquivalence_F
  refine ⟨?_, ?_⟩
  · unfold Diagram.pullTheta
    rw [boundaryTheta_pullbackTheta hΦ hΘ' hind',
      boundaryTheta_pushforwardTheta hF (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
        (hasIndependentTangentSums_pullbackTheta hΦ hind')]
  · unfold Diagram.pullSection
    rw [pullSection_boundaryLift hT'.isGrHatSection hΦ.isLocalScDiffeo_obj hbdΦ,
      pushSection_boundaryLift (isGrHatSection_pullSection hΦ.isLocalScDiffeo_obj
        hT'.isGrHatSection) hF.isLocalScDiffeo_obj hbdF]

end EPLoc

end EPLocalization

/-! ### Witnesses -/

namespace EpGroupoid.Examples

open MPolyfold EpFunctor EPLocalization CategoryTheory

/-- The trivial ep-groupoid on `ℝ²` as an object of `EP`. -/
abbrev rn2EP : EP.{0} := ⟨_, _, trivial (rnPolyfold 2)⟩

/-- **An oriented branched ep⁺-subgroupoid in the sense of Definition 11.3.6**: `(Θ, T̂¹)` of
Example 9.3.5 on `ℝ²`. -/
def example935Oriented : OrientedBranched rn2EP :=
  ⟨example935Theta, exampleT1, example_9_3_5_rn.1, hasIndependentTangentSums_rn rfl _,
    example_9_3_5_rn.2.1⟩

theorem isGeneralizedIso_id_rn2EP : EPLoc.IsGeneralizedIso (𝟙 (EPLoc.of rn2EP)) :=
  ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩

/-- `Θ̂` of Example 9.3.5 pushed forward along the identity generalized isomorphism (the
hypotheses of Definition 11.3.6 are satisfiable). -/
def example935Oriented_push : OrientedBranched rn2EP :=
  example935Oriented.push isGeneralizedIso_id_rn2EP

/-- The boundary-transfer hypothesis of Theorem 11.3.9 holds along the identity equivalence of
the trivial ep-groupoid on `ℝ²` for the identity boundary operation (satisfiability). -/
theorem isBoundaryTransfer_id_rn2 (x : Fin 2 → ℝ) (ψ : Fin 2 → ℝ)
    (hs : (trivial (rnPolyfold 2)).src ψ = x) :
    (trivial (rnPolyfold 2)).PObj.IsBoundaryTransfer (trivial (rnPolyfold 2)).PObj x
      ((trivial (rnPolyfold 2)).tgt ψ)
      ((trivial (rnPolyfold 2)).tangentMor ψ ∘
        (EpFunctor.id (trivial (rnPolyfold 2))).tangent.obj) id id := fun g hg => by
  have hψ : (trivial (rnPolyfold 2)).tgt ψ = x := hs
  have hfix : ∀ α ∈ g.carrier, ((trivial (rnPolyfold 2)).tangentMor ψ ∘
      (EpFunctor.id (trivial (rnPolyfold 2))).tangent.obj) α = id α := fun α hα => by
    rw [Function.comp_apply, tangent_id]
    exact (trivial (rnPolyfold 2)).tangentMor_unit_of_eq ((hg.1 α hα).trans hs.symm)
  have hmap : g.map ((trivial (rnPolyfold 2)).tangentMor ψ ∘
      (EpFunctor.id (trivial (rnPolyfold 2))).tangent.obj) = g := by
    rw [OrTangent.map_congr hfix fun v hv i => hg.mem_carrier hv i, OrTangent.map_id]
  exact ⟨by rw [hψ, hmap], fun _ => rfl⟩

end EpGroupoid.Examples

end Polyfold
