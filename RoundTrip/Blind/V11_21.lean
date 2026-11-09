import Polyfold
/-! Blind formalization of V11_21 (the Springer 2021 book, Part II, §11.3, Theorem 11.3.5,
p. 539, with the proof's step, pp. 539–540).

Text: for a generalized isomorphism `f`, `f_*T̂_Θ` orients `f_*Θ` and `f^*T̂_{Θ'}` orients
`f^*Θ'`; the proof moves an oriented local branching structure by `ψ̂ ∘ F` with the same
weights.

Choices:
- Setting: objects `X Y : EP.{0}` (all spaces in `Type`), `f` a morphism of the project's
  `EP(E⁻¹)`, "generalized isomorphism" the project's `EPLoc.IsGeneralizedIso` (`#print`ed),
  representatives the project's `Diagram` with `EPLoc.homMk d = f`, as in my `V11_18.lean`,
  `V11_20.lean`.  B asserts the claim for every representative (the text computes `f_*`, `f^*`
  on a representative).
- `Θ`, `Θ'`: branched ep⁺-subgroupoids (the project's `IsBranchedEpSubgroupoid`), the setting of
  §11.3.  `f_*Θ`, `f^*Θ'`: `Diagram.pushTheta`, `Diagram.pullTheta`; `f_*T̂`, `f^*T̂'`:
  `Diagram.pushSection`, `Diagram.pullSection` (Lemma 11.3.4; all `#print`ed, see `V11_18.lean`,
  `V11_20.lean`).
- "`T̂` orients `Θ`" (Definition 9.3.2): the project's `IsOrientation` (`#print`ed: `T̂(x) ∈
  Gr̂(x)` and natural on `X_∞`, lifting `T_Θ` = the project's `tangentValue`, locally of the form
  `∑_{y ∈ Mᵢ} σᵢ T_y(Mᵢ, oᵢ)` for an oriented local branching structure; compared with the text in
  `V9_30.lean`).  `T_Θ` is computed by `tangentValue` on a chosen local branching structure; the
  text's `T_Θ` is well defined by Theorem 9.2.1, and I add no hypothesis such as the project's
  `HasIndependentTangentSums` (the text has none).
- The proof's step (`MoveB`), for an equivalence `F : X → Y` (`EpFunctor.IsEquivalence`) on
  ep-groupoids in `Type`: an oriented local branching structure (project's
  `OrientedBranchingStructure`, `#print`ed) of a branched `Θ` at `x` and `ψ : F(x) → y` give an
  open `W ∋ x` in `U(x)` on which `g = ψ̂ ∘ F` (`EpGroupoid.hat`, Definition 7.1.4) is an
  sc-diffeomorphism onto an open `W'`, and an oriented local branching structure of `F_*Θ`
  (`pushforwardTheta`) at `y` with domain `g(W)`, sheets `g(Mᵢ ∩ W)`, the same weights, and
  orientations `Tg_*(oᵢ)`: `T_{g z}(g(Mᵢ ∩ W), oᵢ') = Tg (T_z(Mᵢ, oᵢ))` for `z ∈ Mᵢ ∩ W`, with
  `Tg` Part I's `tangentMapOn` and `OrTangent.map` (image of the subspace and of the frames).
  This conjunct is my reading of a proof remark; drop it if only the theorem is wanted.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_21
open Polyfold Polyfold.EPLocalization

/-- The proof's step: oriented local branching structures are moved by `g = ψ̂ ∘ F`, with the
same weights and the pushed-forward orientations. -/
def MoveB : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
    F.IsEquivalence →
    ∀ Θ : Obj → ℚ, X.IsBranchedEpSubgroupoid Θ →
    ∀ (x : Obj) (B : X.OrientedBranchingStructure Θ x) (ψ : Mor') (y : Obj'),
      Y.src ψ = F.obj x → Y.tgt ψ = y →
      ∃ W : Set Obj, IsOpen W ∧ x ∈ W ∧ W ⊆ B.U ∧
        ∃ (g' : Obj' → Obj) (W' : Set Obj')
          (hg : X.PObj.IsScDiffeoOn Y.PObj (Y.hat ψ ∘ F.obj) g' W W'), IsOpen W' ∧
          ∃ B' : Y.OrientedBranchingStructure (F.pushforwardTheta Θ) y,
            B'.U = (Y.hat ψ ∘ F.obj) '' W ∧
            ∃ e : B.ι ≃ B'.ι, ∀ i,
              B'.M (e i) = (Y.hat ψ ∘ F.obj) '' (B.M i ∩ W) ∧ B'.σ (e i) = B.σ i ∧
              ∀ z ∈ B.M i ∩ W,
                (B'.orient (e i)).tangent ((Y.hat ψ ∘ F.obj) z) =
                  MPolyfold.OrTangent.map (MPolyfold.tangentMapOn hg.isScSmoothOn)
                    ((B.orient i).tangent z)

/-- Theorem 11.3.5: push-forwards and pull-backs of orientations along a generalized
isomorphism are orientations. -/
def TheoremB : Prop :=
  ∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d : Diagram X Y, EPLoc.homMk d = f →
      (∀ (Θ : X.Obj → ℚ) (T : X.Obj → X.X.PObj.OrTangent →₀ ℚ),
        X.X.IsBranchedEpSubgroupoid Θ → X.X.IsOrientation Θ T →
          Y.X.IsOrientation (d.pushTheta Θ) (d.pushSection T)) ∧
      (∀ (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ),
        Y.X.IsBranchedEpSubgroupoid Θ' → Y.X.IsOrientation Θ' T' →
          X.X.IsOrientation (d.pullTheta Θ') (d.pullSection T'))

/-- Theorem 11.3.5 and the step of its proof. -/
def B : Prop := TheoremB ∧ MoveB

end RoundTrip.V11_21
