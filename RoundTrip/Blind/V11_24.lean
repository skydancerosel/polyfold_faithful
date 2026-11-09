import Polyfold
/-! Blind formalization of V11_24 (the Springer 2021 book, Part II, §11.3, Theorem 11.3.8 and
(11.11), pp. 541–542).

Text: `f_*(∂Θ) = ∂(f_*Θ)` and `f^*(∂Θ') = ∂(f^*Θ')` (11.11); in the sketch of the proof
`d_M(x)` "is being preserved".

Choices:
- Setting: objects `X Y : EP.{0}` (all spaces in `Type`), `f` a generalized isomorphism of the
  project's `EP(E⁻¹)` (`EPLoc.IsGeneralizedIso`, `#print`ed, the setting of §11.3),
  representatives `d` with `EPLoc.homMk d = f`; `f_*`, `f^*` the project's `Diagram.pushTheta`,
  `Diagram.pullTheta` on every representative (`#print`ed), as in my `V11_18.lean`.
- `Θ`, `Θ'`: branched ep⁺-subgroupoids (`IsBranchedEpSubgroupoid`).  `∂Θ` (Definition 9.2.16,
  `∂Θ(y) = ∑_{y ∈ ∂Mᵢ} σᵢ` with `∂Mᵢ = {d_{Mᵢ} ≥ 1}`): the project's `boundaryTheta`
  (`#print`ed: on `∂X` the part of the tangent sum `T_Θ(y) = ∑ σ_L L` with `L` not in the reduced
  tangent space, `0` off `∂X`; the project states it agrees locally with `∑_{y ∈ Mᵢ, d_{Mᵢ}(y) ≥ 1}
  σᵢ`).  I use it because Definition 9.2.16 as printed characterizes `∂Θ` only on `supp(∂Θ)` (my
  `V9_27.lean`).  (11.11) is an equality of functions on all objects.
- "`d_M(x)` is being preserved" (`DegPreservedB`): in the proof the sheets `M` of a local
  branching structure are moved by `g = ψ̂ ∘ F` (`F` an equivalence, `ψ : F(x) → y`,
  `EpGroupoid.hat`, as in my `V11_17.lean`); I read the remark as: whenever `g` is an
  sc-diffeomorphism `W → W'` between open sets, every sub-M-polyfold `M ⊆ W` with sub-M-polyfold
  image `g(M)` has `d_{g(M)}(g(z)) = d_M(z)` for `z ∈ M`.  `d_M`: the project's `subDegIndex`
  (`#print`ed: the degeneracy index, Definition 2.22, of `M` with its induced structure).  The
  hypotheses "`M`, `g(M)` are sub-M-polyfolds" are needed to state `d_M`; the remark itself is a
  proof remark, drop this conjunct if only (11.11) is wanted.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_24
open Polyfold Polyfold.EPLocalization

/-- (11.11): `f_*(∂Θ) = ∂(f_*Θ)` and `f^*(∂Θ') = ∂(f^*Θ')`. -/
def BoundaryB : Prop :=
  ∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d : Diagram X Y, EPLoc.homMk d = f →
      (∀ Θ : X.Obj → ℚ, X.X.IsBranchedEpSubgroupoid Θ →
        d.pushTheta (X.X.boundaryTheta Θ) = Y.X.boundaryTheta (d.pushTheta Θ)) ∧
      (∀ Θ' : Y.Obj → ℚ, Y.X.IsBranchedEpSubgroupoid Θ' →
        d.pullTheta (Y.X.boundaryTheta Θ') = X.X.boundaryTheta (d.pullTheta Θ'))

/-- The proof's remark: the local sc-diffeomorphisms `ψ̂ ∘ F` preserve the degeneracy index of
sub-M-polyfolds. -/
def DegPreservedB : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
    F.IsEquivalence →
    ∀ (ψ : Mor') (W : Set Obj) (W' : Set Obj') (g' : Obj' → Obj),
      IsOpen W → IsOpen W' → X.PObj.IsScDiffeoOn Y.PObj (Y.hat ψ ∘ F.obj) g' W W' →
      ∀ (M : Set Obj) (hM : X.PObj.IsSubMPolyfold M)
        (hM' : Y.PObj.IsSubMPolyfold ((Y.hat ψ ∘ F.obj) '' M)), M ⊆ W →
        ∀ (z : Obj) (hz : z ∈ M),
          Y.PObj.subDegIndex hM' ⟨(Y.hat ψ ∘ F.obj) z, Set.mem_image_of_mem _ hz⟩ =
            X.PObj.subDegIndex hM ⟨z, hz⟩

/-- Theorem 11.3.8: (11.11), and the preservation of `d_M` used in its proof. -/
def B : Prop := BoundaryB ∧ DegPreservedB

end RoundTrip.V11_24
