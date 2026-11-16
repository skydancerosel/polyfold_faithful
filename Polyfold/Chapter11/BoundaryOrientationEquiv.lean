import Polyfold.Chapter11.BranchedEquivalenceTangentOrientation
import Polyfold.Chapter9.BoundaryOperation
import Polyfold.Chapter9.TangentMapBoundaryOps
import Polyfold.Chapter9.GeneralCorollaries

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.3: **Theorem 11.3.9** (2021 p. 542; 2017: Theorem 11.7, p. 395), for
the boundary operation of Definition 9.3.8 (2021 p. 427; 2017: Definition 9.9) built in
`Chapter9/BoundaryOperation.lean`.  Numbers and pages are the 2021 text's.

# Boundary orientations along generalized isomorphisms

## The text, paraphrased

(Proof of Theorem 11.3.8, p. 542) Local branching structures and submanifolds `M ∋ x` are moved by
equivalences and by the local sc-diffeomorphisms `ψ̂` of morphisms, and `d_M(x)` is preserved.
(Theorem 11.3.9, p. 542) For a generalized isomorphism `f : X → Y` and oriented tame branched
ep⁺-subgroupoids `Θ̂`, `Θ̂'`: `∂(f_*Θ̂) = f_*(∂Θ̂)` and `∂(f^*Θ̂') = f^*(∂Θ̂')`; the proof is left
to the reader.

## What is formalized

* **sc-diffeomorphisms move the boundary operation.**  A presented chart `ψ` at `f(x)` gives the
  presented chart `ψ ∘ f` at `x` with the same model and presentation
  (`PresentedChart.transport`), so `Tf` preserves `T^R_xX` and `C_xX`
  (`isReducedVec_tangentMapOn_iff`, `isInwardVec_tangentMapOn_iff`), the reduced codimension
  (`hasReducedCodim_map_tangentMapOn_iff`) and the boundary operation
  (`boundaryOp_map_tangentMapOn`: `∂(Tf_*(L, o)) = Tf_*(∂(L, o))`).  Together:
  `isReducedBoundaryTransfer_of_eqOn` for every fibre map agreeing with `Tf` on `T_xX`.
* **Equivalences move it**: along `Tψ ∘ TF(x)` for every `ψ : F(x) → y`
  (`EpFunctor.isReducedBoundaryTransfer_tangentMor`, through the transport chart `ψ̂ ∘ F` of
  Chapter 10) and along the fibre inverses `TF(x)⁻¹` (`isReducedBoundaryTransfer_fibreInv`).
* **The boundary-transfer hypothesis of `BranchedEquivalenceTangentOrientation.lean`** for the
  boundary operation of Definition 9.3.8: `IsReducedBoundaryTransfer.isBoundaryTransfer` turns the
  above into `IsBoundaryTransfer … boundaryOp boundaryOp`, given that `f` carries tangent sets of
  tame submanifolds to tangent sets of tame submanifolds and back (`CarriesTameTangents`).
* **Theorem 11.3.9 for the generalized isomorphism itself, without transfer hypotheses**, for
  the intrinsic `T̂_{∂Θ} = boundaryOrientation T̂_Θ` of Definition 9.3.10:
  `EPLoc.theorem_11_3_9_push_boundaryOrientation`, `EPLoc.theorem_11_3_9_pull_boundaryOrientation`
  (`f_*(∂Θ) = ∂(f_*Θ)` and `f_* T̂_{∂Θ} = T̂_{∂(f_*Θ)}`, and the same for `f^*`; the
  independence of the tangent sums is Theorem 9.2.1 (1), `EpGroupoid.hasIndependentTangentSums`),
  also for a
  representative diagram (`Diagram.pushSection_boundaryOrientation`,
  `Diagram.pullSection_boundaryOrientation`).
* **The same for Chapter 9's `boundaryLift boundaryOp`** on oriented tame `Θ̂` whose transform is
  tame (`EPLoc.theorem_11_3_9_push_boundaryOp`, `EPLoc.theorem_11_3_9_pull_boundaryOp`).
* Witnesses: the tame-tangent condition along the identity (`carriesTameTangents_id`); the
  tameness hypotheses for Example 9.3.5 on `ℝ²` and its push-forward along the identity
  (`isTameOrientation_example935`, `isTameOrientation_example935_push`), used together in
  `theorem_11_3_9_push_boundaryOp_example935`.

## What the text leaves implicit, and the choices made

* "`d_M(x)` is being preserved" is read for the intrinsic degree of `T_xM`, its reduced
  codimension `dim(T_xM / T_xM ∩ T^R_xX)` (`HasReducedCodim`), which for tame `M` is `d_M(x)`
  (`hasSubDegree_iff`).  It is preserved by every sc-diffeomorphism, without tameness.
* `boundaryOrientation` is a function of `T̂_Θ`, so Theorem 11.3.9 holds for every section of
  `Gr̂`, oriented or not; `f_*(∂Θ) = ∂(f_*Θ)` is Theorem 11.3.8.

## Not formalized, and why

* That sc-diffeomorphisms carry submanifolds with tame induced structure to such submanifolds
  (`CarriesTameTangents`, and the tameness of `f_*Θ̂` in the `boundaryLift` version): it needs
  the restriction of sc-diffeomorphisms to sub-M-polyfolds and the tameness of open parts of
  tame sub-M-polyfolds, neither of which is formalized.  For the intrinsic `boundaryOrientation`
  it is not needed.
* `∂Θ̂ = (∂Θ, T̂_{∂Θ})` as an oriented branched ep⁺-subgroupoid (Definition 9.3.10's claim that
  `T̂_{∂Θ}` orients `∂Θ`) is not formalized, so Theorem 11.3.9 is stated componentwise.

Boundary operators under tangent maps (`MPolyfold.boundaryOp_map`, `MPolyfold.boundaryOp_succ`,
`MPolyfold.boundaryOp_zero`, `MPolyfold.OrTangent.map_mk`, …):
`Chapter9/TangentMapBoundaryOps.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function Module Submodule

noncomputable section

namespace Polyfold

universe u v

/-! ### Fibre maps moving the boundary operation -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- The frames of `boundaryOp g` lie in its carrier. -/
theorem boundaryOp_frames_mem (g : OrTangent P) {v : Fin (P.boundaryOp g).dim → P.TangentSpace}
    (hv : v ∈ (P.boundaryOp g).frames) (i : Fin (P.boundaryOp g).dim) :
    v i ∈ (P.boundaryOp g).carrier := by
  obtain ⟨_ | m, L, O⟩ := g
  · exact False.elim hv
  · exact hv.1 i

theorem boundaryOp_carrier_subset (g : OrTangent P) : (P.boundaryOp g).carrier ⊆ g.carrier := by
  rw [boundaryOp_carrier]
  exact fun α hα => hα.1

/-! ### Presented charts through sc-diffeomorphisms -/

variable (P Q) in
/-- **`f : T_xX → T_yY` moves the reduced codimension `1` and the boundary operation of
Definition 9.3.8** on oriented tangent sets over `x` (the intrinsic counterpart of
`IsBoundaryTransfer`, with `d_M = 1` read as reduced codimension `1`). -/
def IsReducedBoundaryTransfer (x : X) (y : Y) (f : P.TangentSpace → Q.TangentSpace) : Prop :=
  ∀ o : OrTangent P, P.IsOrientedAt x o →
    (Q.HasReducedCodim y 1 (o.map f) ↔ P.HasReducedCodim x 1 o) ∧
      Q.boundaryOp (o.map f) = (P.boundaryOp o).map f

/-- **sc-diffeomorphisms move the boundary operation**: every fibre map agreeing with `Tf` on
`T_xX`, `x ∈ U`, satisfies `IsReducedBoundaryTransfer`. -/
theorem isReducedBoundaryTransfer_of_eqOn {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y}
    (hf : P.IsScDiffeoOn Q f g U U') {x : X} (hx : x ∈ U) {f' : P.TangentSpace → Q.TangentSpace}
    (hf' : ∀ α, P.levelVal 1 (P.tangentProj α) = x → f' α = tangentMapOn hf.isScSmoothOn α) :
    P.IsReducedBoundaryTransfer Q x (f x) f' := fun o hO => by
  have hmap : o.map f' = o.map (tangentMapOn hf.isScSmoothOn) :=
    OrTangent.map_congr (fun α hα => hf' α (hO.1 α hα)) fun v hv i => hO.mem_carrier hv i
  have hmap' : (P.boundaryOp o).map f' = (P.boundaryOp o).map (tangentMapOn hf.isScSmoothOn) :=
    OrTangent.map_congr (fun α hα => hf' α (hO.1 α (boundaryOp_carrier_subset o hα)))
      fun v hv i => boundaryOp_frames_mem o hv i
  rw [hmap, hmap']
  exact ⟨hasReducedCodim_map_tangentMapOn_iff hf hx hO.1, boundaryOp_map_tangentMapOn hf hx hO⟩

theorem isReducedBoundaryTransfer_id (x : X) : P.IsReducedBoundaryTransfer P x x id :=
  fun o _ => ⟨by rw [OrTangent.map_id], by rw [OrTangent.map_id, OrTangent.map_id]⟩

variable (P) in
/-- `L` is the tangent set `T_xA` of a smooth submanifold `A ∋ x` with tame induced structure. -/
def IsTameTangentSet (x : X) (L : Set P.TangentSpace) : Prop :=
  ∃ (A : Set X) (_ : P.IsSmoothSubmanifold A), x ∈ A ∧ P.HasTameInducedStructure A ∧
    P.submanifoldTangent A x = L

variable (P Q) in
/-- **`f` carries tangent sets of tame submanifolds through `x` to those through `y`, and
back**, on oriented tangent sets over `x` (the tameness part of "`d_M(x)` is being
preserved"; witness: `carriesTameTangents_id`). -/
def CarriesTameTangents (x : X) (y : Y) (f : P.TangentSpace → Q.TangentSpace) : Prop :=
  ∀ o : OrTangent P, P.IsOrientedAt x o →
    (Q.IsTameTangentSet y (f '' o.carrier) ↔ P.IsTameTangentSet x o.carrier)

theorem carriesTameTangents_id (x : X) : P.CarriesTameTangents P x x id :=
  fun o _ => by rw [image_id]

/-- **The boundary-transfer hypothesis for the boundary operation of Definition 9.3.8**: a
fibre map moving the reduced codimension and the boundary operation, and carrying tangent sets
of tame submanifolds, satisfies `IsBoundaryTransfer … boundaryOp boundaryOp`. -/
theorem IsReducedBoundaryTransfer.isBoundaryTransfer {x : X} {y : Y}
    {f : P.TangentSpace → Q.TangentSpace} (h : P.IsReducedBoundaryTransfer Q x y f)
    (htame : P.CarriesTameTangents Q x y f) :
    P.IsBoundaryTransfer Q x y f P.boundaryOp Q.boundaryOp := fun o hO => by
  obtain ⟨hcod, hbd⟩ := h o hO
  refine ⟨?_, fun _ => hbd⟩
  rw [hasSubDegree_iff, hasSubDegree_iff]
  exact and_congr (htame o hO) hcod

/-- Along an sc-diffeomorphism carrying tame tangent sets, the boundary operation of
Definition 9.3.8 satisfies the boundary-transfer hypothesis. -/
theorem isBoundaryTransfer_boundaryOp_of_isScDiffeoOn {f : X → Y} {g : Y → X} {U : Set X}
    {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') {x : X} (hx : x ∈ U)
    (htame : P.CarriesTameTangents Q x (f x) (tangentMapOn hf.isScSmoothOn)) :
    P.IsBoundaryTransfer Q x (f x) (tangentMapOn hf.isScSmoothOn) P.boundaryOp Q.boundaryOp :=
  (isReducedBoundaryTransfer_of_eqOn hf hx fun _ _ => rfl).isBoundaryTransfer htame

end MPolyfold

/-! ### Equivalences -/

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
/-- The reduced-codimension-`1` part and the boundary operation commute with a fibre map that
moves them. -/
theorem mapDomain_boundaryOp_reducedCodimPart {x : Obj} {y : Obj'} {w : X.PObj.OrTangent →₀ ℚ}
    (hw : w ∈ X.GrHat x) {f : X.PObj.TangentSpace → Y.PObj.TangentSpace}
    (hbd : X.PObj.IsReducedBoundaryTransfer Y.PObj x y f) :
    ((X.reducedCodimPart x 1 w).mapDomain X.PObj.boundaryOp).mapDomain (OrTangent.map f) =
      (Y.reducedCodimPart y 1 (w.mapDomain (OrTangent.map f))).mapDomain Y.PObj.boundaryOp := by
  conv_lhs => rw [← Finsupp.sum_single w]
  conv_rhs => rw [← Finsupp.sum_single w]
  simp only [Finsupp.sum, reducedCodimPart, Finsupp.mapDomain_finsetSum, Finsupp.filter_sum,
    Finsupp.mapDomain_single]
  refine Finset.sum_congr rfl fun g hg => ?_
  obtain ⟨hdeg, hb⟩ := hbd g (hw.2 g hg)
  by_cases h1 : X.PObj.HasReducedCodim x 1 g
  · rw [Finsupp.filter_single_of_pos _ h1, Finsupp.filter_single_of_pos _ (hdeg.2 h1),
      Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hb]
  · rw [Finsupp.filter_single_of_neg _ h1,
      Finsupp.filter_single_of_neg _ fun h => h1 (hdeg.1 h), Finsupp.mapDomain_zero,
      Finsupp.mapDomain_zero, Finsupp.mapDomain_zero]

theorem boundaryOrientation_of_eq_zero {T : Obj → X.PObj.OrTangent →₀ ℚ} {y : Obj}
    (h : T y = 0) : X.boundaryOrientation T y = 0 := by
  rw [boundaryOrientation, h, reducedCodimPart, Finsupp.filter_zero, Finsupp.mapDomain_zero]

end EpGroupoid

namespace EpFunctor

open EpGroupoid

variable {F : EpFunctor X Y}

/-- **Equivalences move the boundary operation, push-forward**: `Tψ ∘ TF(x)` satisfies
`IsReducedBoundaryTransfer` for every `ψ : F(x) → y` (it is `TQ` for the transport chart
`Q = ψ̂ ∘ F` on `T_xX`). -/
theorem isReducedBoundaryTransfer_tangentMor (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) (x : Obj)
    {ψ : Mor'} (hs : Y.src ψ = F.obj x) :
    X.PObj.IsReducedBoundaryTransfer Y.PObj x (Y.tgt ψ) (Y.tangentMor ψ ∘ F.tangent.obj) := by
  obtain ⟨T, hT⟩ := exists_transportChart hF hs rfl
  have h := isReducedBoundaryTransfer_of_eqOn T.isScDiffeoOn_Q T.mem_W
    (f' := Y.tangentMor ψ ∘ F.tangent.obj) fun α hα => by
      have hαW : α ∈ X.PObj.tangentPreimage T.W := by change _ ∈ T.W; rw [hα]; exact T.mem_W
      rw [Function.comp_apply, ← T.tangentMor_ψ_tangent_obj hαW, hα, T.ψ_self, hT]
  rwa [T.Q_self] at h

/-- **Equivalences move the boundary operation, pull-back**: the fibre inverse `TF(x)⁻¹`
satisfies `IsReducedBoundaryTransfer` (it is `T(F|U)⁻¹` on `T_{F(x)}Y`). -/
theorem isReducedBoundaryTransfer_fibreInv (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) (x : Obj) :
    Y.PObj.IsReducedBoundaryTransfer X.PObj (F.obj x) x (fibreInv F.tangent.obj x) := by
  obtain ⟨U, V, g, hxU, hd⟩ := hF x
  have h := isReducedBoundaryTransfer_of_eqOn hd.symm (hd.mapsTo hxU)
    (f' := fibreInv F.tangent.obj x) fun β hβ => fibreInv_eq_tangentMapOn hF hd hxU hβ
  rwa [hd.left_inv x hxU] at h

/-- **Theorem 11.3.9 for an equivalence, push-forward, orientation part, with the boundary
operation of Definition 9.3.8**: `F_* T̂_{∂Θ} = T̂_{∂(F_*Θ)}`, no transfer hypothesis. -/
theorem pushSection_boundaryOrientation {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsGrHatSection T) (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) :
    F.pushSection (X.boundaryOrientation T) = Y.boundaryOrientation (F.pushSection T) := by
  classical
  funext y
  rw [boundaryOrientation]
  unfold pushSection
  split_ifs with h
  · obtain ⟨hs, ht⟩ := h.2.choose_spec
    have hy' : Y.tgt h.2.choose.2 ∈ Y.PObj.smoothSet := by rw [ht]; exact h.1
    have hxs : h.2.choose.1 ∈ X.PObj.smoothSet :=
      (hF.mem_smoothSet_iff _).1 (hs ▸ Y.src_mem_smoothSet_of_tgt hy')
    have := mapDomain_boundaryOp_reducedCodimPart (hT.mem _ hxs)
      (ht ▸ isReducedBoundaryTransfer_tangentMor hF _ hs)
    rw [boundaryOrientation]
    convert this using 3
  · rw [reducedCodimPart, Finsupp.filter_zero, Finsupp.mapDomain_zero]

/-- **Theorem 11.3.9 for an equivalence, pull-back, orientation part, with the boundary
operation of Definition 9.3.8**: `F^* T̂_{∂Θ'} = T̂_{∂(F^*Θ')}`, no transfer hypothesis. -/
theorem pullSection_boundaryOrientation {T' : Obj' → Y.PObj.OrTangent →₀ ℚ}
    (hT' : Y.IsGrHatSection T') (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) :
    F.pullSection (Y.boundaryOrientation T') = X.boundaryOrientation (F.pullSection T') := by
  funext x
  by_cases hx : x ∈ X.PObj.smoothSet
  · rw [pullSection_of_mem hx, boundaryOrientation, boundaryOrientation, pullSection_of_mem hx]
    exact mapDomain_boundaryOp_reducedCodimPart (hT'.mem _ ((hF.mem_smoothSet_iff x).2 hx))
      (isReducedBoundaryTransfer_fibreInv hF x)
  · rw [pullSection_of_not_mem hx, boundaryOrientation_of_eq_zero (pullSection_of_not_mem hx)]

/-- `F^*` only sees `Y_∞`. -/
theorem pullSection_congr (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj)
    {T₁ T₂ : Obj' → Y.PObj.OrTangent →₀ ℚ} (h : ∀ y ∈ Y.PObj.smoothSet, T₁ y = T₂ y) :
    F.pullSection T₁ = F.pullSection T₂ := by
  funext x
  by_cases hx : x ∈ X.PObj.smoothSet
  · rw [pullSection_of_mem hx, pullSection_of_mem hx, h _ ((hF.mem_smoothSet_iff x).2 hx)]
  · rw [pullSection_of_not_mem hx, pullSection_of_not_mem hx]

/-- Along an equivalence carrying tame tangent sets, the boundary operation of Definition 9.3.8
satisfies the boundary-transfer hypothesis of `pushSection_boundaryLift`. -/
theorem isBoundaryTransfer_tangentMor (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) (x : Obj)
    {ψ : Mor'} (hs : Y.src ψ = F.obj x)
    (htame : X.PObj.CarriesTameTangents Y.PObj x (Y.tgt ψ) (Y.tangentMor ψ ∘ F.tangent.obj)) :
    X.PObj.IsBoundaryTransfer Y.PObj x (Y.tgt ψ) (Y.tangentMor ψ ∘ F.tangent.obj)
      X.PObj.boundaryOp Y.PObj.boundaryOp :=
  (isReducedBoundaryTransfer_tangentMor hF x hs).isBoundaryTransfer htame

/-- The same for the fibre inverses of `pullSection_boundaryLift`. -/
theorem isBoundaryTransfer_fibreInv (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) (x : Obj)
    (htame : Y.PObj.CarriesTameTangents X.PObj (F.obj x) x (fibreInv F.tangent.obj x)) :
    Y.PObj.IsBoundaryTransfer X.PObj (F.obj x) x (fibreInv F.tangent.obj x)
      Y.PObj.boundaryOp X.PObj.boundaryOp :=
  (isReducedBoundaryTransfer_fibreInv hF x).isBoundaryTransfer htame

end EpFunctor

end Equivalence

/-! ### Theorem 11.3.9 -/

namespace EPLocalization

open EpFunctor EpGroupoid MPolyfold CategoryTheory

namespace Diagram

variable {X Y : EP.{u}}

/-- **Theorem 11.3.9 for a representative, push-forward, orientation part**: for
`d : X ←F A →Φ Y` with `Φ` an equivalence, `d_* T̂_{∂Θ} = T̂_{∂(d_*Θ)}`, no transfer
hypothesis. -/
theorem pushSection_boundaryOrientation (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hT : X.X.IsGrHatSection T) :
    d.pushSection (X.X.boundaryOrientation T) = Y.X.boundaryOrientation (d.pushSection T) := by
  have hF := d.isEquivalence_F
  unfold pushSection
  rw [EpFunctor.pullSection_boundaryOrientation hT hF.isLocalScDiffeo_obj,
    EpFunctor.pushSection_boundaryOrientation
      (isGrHatSection_pullSection hF.isLocalScDiffeo_obj hT) hΦ.isLocalScDiffeo_obj]

/-- **Theorem 11.3.9 for a representative, pull-back, orientation part**:
`d^* T̂_{∂Θ'} = T̂_{∂(d^*Θ')}`, no transfer hypothesis. -/
theorem pullSection_boundaryOrientation (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hT' : Y.X.IsGrHatSection T') :
    d.pullSection (Y.X.boundaryOrientation T') = X.X.boundaryOrientation (d.pullSection T') := by
  have hF := d.isEquivalence_F
  unfold pullSection
  rw [EpFunctor.pullSection_boundaryOrientation hT' hΦ.isLocalScDiffeo_obj,
    EpFunctor.pushSection_boundaryOrientation
      (isGrHatSection_pullSection hΦ.isLocalScDiffeo_obj hT') hF.isLocalScDiffeo_obj]

end Diagram

namespace EPLoc

variable {X Y : EP.{u}}

/-- **Theorem 11.3.9, push-forward** (2021 p. 542; 2017: Theorem 11.7), for the generalized
isomorphism itself and the boundary operation of Definition 9.3.8: `f_*(∂Θ) = ∂(f_*Θ)` and
`f_* T̂_{∂Θ} = T̂_{∂(f_*Θ)}`, with `T̂_{∂Θ} = boundaryOrientation T̂_Θ` (Definition 9.3.10).  No
boundary-transfer hypothesis; `T̂_Θ` need only be a section of `Gr̂`.  The independence of the
tangent sums used by Theorem 11.3.8 is Theorem 9.2.1 (1) (`EpGroupoid.hasIndependentTangentSums`).
-/
theorem theorem_11_3_9_push_boundaryOrientation {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ : X.Obj → ℚ}
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ)
    (hT : X.X.IsGrHatSection T) :
    pushTheta f (X.X.boundaryTheta Θ) = Y.X.boundaryTheta (pushTheta f Θ) ∧
      pushSection f (X.X.boundaryOrientation T) = Y.X.boundaryOrientation (pushSection f T) :=
  ⟨theorem_11_3_8_push hf hΘ (X.X.hasIndependentTangentSums Θ),
    (rep f).pushSection_boundaryOrientation (isEquivalence_rep_Φ hf) hT⟩

/-- **Theorem 11.3.9, pull-back** (2021 p. 542), for the generalized isomorphism itself:
`f^*(∂Θ') = ∂(f^*Θ')` and `f^* T̂_{∂Θ'} = T̂_{∂(f^*Θ')}`.  No boundary-transfer hypothesis; the
independence of the tangent sums is Theorem 9.2.1 (1). -/
theorem theorem_11_3_9_pull_boundaryOrientation {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ')
    (hT' : Y.X.IsGrHatSection T') :
    pullTheta f (Y.X.boundaryTheta Θ') = X.X.boundaryTheta (pullTheta f Θ') ∧
      pullSection f (Y.X.boundaryOrientation T') = X.X.boundaryOrientation (pullSection f T') :=
  ⟨theorem_11_3_8_pull hf hΘ' (Y.X.hasIndependentTangentSums Θ'),
    (rep f).pullSection_boundaryOrientation (isEquivalence_rep_Φ hf) hT'⟩

/-- `f_*` only sees `X_∞`. -/
theorem pushSection_congr {f : of X ⟶ of Y} {T₁ T₂ : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (h : ∀ x ∈ X.X.PObj.smoothSet, T₁ x = T₂ x) : pushSection f T₁ = pushSection f T₂ := by
  unfold pushSection Diagram.pushSection
  rw [pullSection_congr (rep f).isEquivalence_F.isLocalScDiffeo_obj h]

/-- `f^*` only sees `Y_∞`. -/
theorem pullSection_congr {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {T₁ T₂ : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (h : ∀ y ∈ Y.X.PObj.smoothSet, T₁ y = T₂ y) :
    pullSection f T₁ = pullSection f T₂ := by
  unfold pullSection Diagram.pullSection
  rw [EpFunctor.pullSection_congr (isEquivalence_rep_Φ hf).isLocalScDiffeo_obj h]

/-- `boundaryLift boundaryOp` of an oriented tame `Θ̂` is `boundaryOrientation` (also off
`X_∞`, where both vanish when `T̂_Θ` does). -/
theorem boundaryLift_boundaryOp_eq {Z : EP.{u}} {Θ : Z.Obj → ℚ}
    {T : Z.Obj → Z.X.PObj.OrTangent →₀ ℚ} (hT : Z.X.IsOrientation Θ T)
    (htame : Z.X.IsTameOrientation Θ T) (h0 : ∀ z ∉ Z.X.PObj.smoothSet, T z = 0) :
    Z.X.boundaryLift Z.X.PObj.boundaryOp T = Z.X.boundaryOrientation T := by
  funext z
  by_cases hz : z ∈ Z.X.PObj.smoothSet
  · exact boundaryLift_boundaryOp_eq_boundaryOrientation hT htame hz
  · rw [boundaryLift_of_eq_zero (h0 z hz), boundaryOrientation_of_eq_zero (h0 z hz)]

/-- **Theorem 11.3.9, push-forward, with Chapter 9's `T̂_{∂Θ} = boundaryLift boundaryOp T̂_Θ`**
(2021 p. 542): for oriented tame `Θ̂` with `f_*Θ̂` tame, `f_* T̂_{∂Θ} = T̂_{∂(f_*Θ)}`, no
boundary-transfer hypothesis. -/
theorem theorem_11_3_9_push_boundaryOp {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ)
    (hind : X.X.HasIndependentTangentSums Θ) (hT : X.X.IsOrientation Θ T)
    (htame : X.X.IsTameOrientation Θ T)
    (htame' : Y.X.IsTameOrientation (pushTheta f Θ) (pushSection f T)) :
    pushSection f (X.X.boundaryLift X.X.PObj.boundaryOp T) =
      Y.X.boundaryLift Y.X.PObj.boundaryOp (pushSection f T) := by
  rw [pushSection_congr fun x hx => boundaryLift_boundaryOp_eq_boundaryOrientation hT htame hx,
    (theorem_11_3_9_push_boundaryOrientation hf hΘ hT.isGrHatSection).2,
    boundaryLift_boundaryOp_eq (theorem_11_3_5_push hf hΘ hind hT) htame'
      fun y hy => EpFunctor.pushSection_of_not_mem hy]

/-- **Theorem 11.3.9, pull-back, with Chapter 9's `T̂_{∂Θ'} = boundaryLift boundaryOp T̂_Θ'`**:
for oriented tame `Θ̂'` with `f^*Θ̂'` tame, `f^* T̂_{∂Θ'} = T̂_{∂(f^*Θ')}`. -/
theorem theorem_11_3_9_pull_boundaryOp {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hind' : Y.X.HasIndependentTangentSums Θ')
    (hT' : Y.X.IsOrientation Θ' T') (htame' : Y.X.IsTameOrientation Θ' T')
    (htame : X.X.IsTameOrientation (pullTheta f Θ') (pullSection f T')) :
    pullSection f (Y.X.boundaryLift Y.X.PObj.boundaryOp T') =
      X.X.boundaryLift X.X.PObj.boundaryOp (pullSection f T') := by
  rw [pullSection_congr hf fun y hy => boundaryLift_boundaryOp_eq_boundaryOrientation hT' htame' hy,
    (theorem_11_3_9_pull_boundaryOrientation hf hΘ' hT'.isGrHatSection).2,
    boundaryLift_boundaryOp_eq (theorem_11_3_5_pull hf hΘ' hind' hT') htame
      fun x hx => EpFunctor.pushSection_of_not_mem hx]

end EPLoc

end EPLocalization

/-! ### Witnesses -/

namespace EpGroupoid.Examples

open MPolyfold EPLocalization CategoryTheory

/-- Example 9.3.5's `(Θ, T̂¹)` on `ℝ²` is tame (`ℝ²` has no boundary). -/
theorem isTameOrientation_example935 :
    (trivial (rnPolyfold 2)).IsTameOrientation example935Theta exampleT1 :=
  isTameOrientation_of_degIndex_eq_zero (fun a => rnPolyfold_degIndex 2 a) example_9_3_5_rn.2.1

/-- Its push-forward along the identity generalized isomorphism is tame. -/
theorem isTameOrientation_example935_push :
    rn2EP.X.IsTameOrientation example935Oriented_push.Θ example935Oriented_push.T :=
  isTameOrientation_of_degIndex_eq_zero (fun a => rnPolyfold_degIndex 2 a)
    example935Oriented_push.isOrientation

/-- The hypotheses of `theorem_11_3_9_push_boundaryOp` hold together: Example 9.3.5 along the
identity generalized isomorphism of `ℝ²`. -/
theorem theorem_11_3_9_push_boundaryOp_example935 :
    EPLoc.pushSection (𝟙 (EPLoc.of rn2EP))
        (rn2EP.X.boundaryLift rn2EP.X.PObj.boundaryOp exampleT1) =
      rn2EP.X.boundaryLift rn2EP.X.PObj.boundaryOp
        (EPLoc.pushSection (𝟙 (EPLoc.of rn2EP)) exampleT1) :=
  EPLoc.theorem_11_3_9_push_boundaryOp isGeneralizedIso_id_rn2EP example_9_3_5_rn.1
    (hasIndependentTangentSums_rn rfl _) example_9_3_5_rn.2.1 isTameOrientation_example935
    isTameOrientation_example935_push

end EpGroupoid.Examples

end Polyfold
