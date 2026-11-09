import Polyfold
/-! Blind formalization of V11_22 (the Springer 2021 book, Part II, §11.3, Definition 11.3.6 and
(11.10), p. 541).

Text: `f_*Θ̂ = (f_*Θ, f_*T̂_Θ)` and `f^*Θ̂' = (f^*Θ', f^*T̂_{Θ'})`; `(g ∘ f)_* = g_* ∘ f_*`,
`(g ∘ f)^* = f^* ∘ g^*`, `f^*f_*Θ̂ = Θ̂` and `f_*f^*Θ̂' = Θ̂'` (11.10).

Choices:
- Setting: objects `X Y Z : EP.{0}` (all spaces in `Type`), generalized isomorphisms
  `f : X → Y`, `g : Y → Z` of the project's `EP(E⁻¹)` (`EPLoc.IsGeneralizedIso`, `#print`ed),
  `g ∘ f` is Mathlib's `f ≫ g`; representatives the project's `Diagram` with `EPLoc.homMk d = f`,
  as in my `V11_18.lean`, `V11_20.lean`, `V11_21.lean`.  Every identity is asserted for every
  choice of representatives.
- An oriented branched ep⁺-subgroupoid `Θ̂ = (Θ, T̂_Θ)` (Definition 9.3.2): a pair with `Θ` a
  branched ep⁺-subgroupoid (`IsBranchedEpSubgroupoid`) and `T̂_Θ` an orientation of it (the
  project's `IsOrientation`, `#print`ed, compared with the text in `V9_30.lean`), my
  `IsOrientedPairB`.  I do not use the project's bundled `OrientedBranched`, which also carries a
  field `HasIndependentTangentSums` that the text's definition does not list.
- `f_*Θ`, `f^*Θ'`: `Diagram.pushTheta`, `Diagram.pullTheta`; `f_*T̂`, `f^*T̂'`:
  `Diagram.pushSection`, `Diagram.pullSection` (all `#print`ed; `f_* = G_*F^*`, `f^* = F_*G^*` on
  a representative `X ←F A →G Y`).
- Definition 11.3.6 presupposes (Theorems 11.3.3, 11.3.5) that the pairs `f_*Θ̂`, `f^*Θ̂'` are
  oriented branched ep⁺-subgroupoids; B includes this (conjunct `PairsB`).
- (11.10): pairs are compared componentwise; the functors `Θ` on all objects; the orientations,
  which the text defines on `X_∞` only, at the smooth objects (the push-forward/pull-back of
  sections is `0` elsewhere by construction, while an orientation in the project's sense is
  unconstrained there, so the identities `f^*f_*T̂ = T̂`, `f_*f^*T̂' = T̂'` are asserted on `X_∞`,
  `Y_∞`; the composition laws hold as equalities of functions).
- Nothing looks false to me.
-/
namespace RoundTrip.V11_22
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- `(Θ, T)` is an oriented branched ep⁺-subgroupoid of `X`. -/
def IsOrientedPairB (X : EP.{0}) (Θ : X.Obj → ℚ) (T : X.Obj → X.X.PObj.OrTangent →₀ ℚ) :
    Prop :=
  X.X.IsBranchedEpSubgroupoid Θ ∧ X.X.IsOrientation Θ T

/-- Definition 11.3.6: `f_*Θ̂ = (f_*Θ, f_*T̂_Θ)` and `f^*Θ̂' = (f^*Θ', f^*T̂_{Θ'})` are oriented
branched ep⁺-subgroupoids. -/
def PairsB : Prop :=
  ∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d : Diagram X Y, EPLoc.homMk d = f →
      (∀ Θ T, IsOrientedPairB X Θ T → IsOrientedPairB Y (d.pushTheta Θ) (d.pushSection T)) ∧
      (∀ Θ' T', IsOrientedPairB Y Θ' T' → IsOrientedPairB X (d.pullTheta Θ') (d.pullSection T'))

/-- (11.10), first half: `(g ∘ f)_* = g_* ∘ f_*` and `(g ∘ f)^* = f^* ∘ g^*` on oriented branched
ep⁺-subgroupoids. -/
def CompB : Prop :=
  ∀ (X Y Z : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y) (g : EPLoc.of Y ⟶ EPLoc.of Z),
    EPLoc.IsGeneralizedIso f → EPLoc.IsGeneralizedIso g →
    ∀ (d : Diagram X Y) (e : Diagram Y Z) (c : Diagram X Z),
      EPLoc.homMk d = f → EPLoc.homMk e = g → EPLoc.homMk c = f ≫ g →
      (∀ Θ T, IsOrientedPairB X Θ T →
        c.pushTheta Θ = e.pushTheta (d.pushTheta Θ) ∧
        c.pushSection T = e.pushSection (d.pushSection T)) ∧
      (∀ Θ'' T'', IsOrientedPairB Z Θ'' T'' →
        c.pullTheta Θ'' = d.pullTheta (e.pullTheta Θ'') ∧
        c.pullSection T'' = d.pullSection (e.pullSection T''))

/-- (11.10), second half: `f^*f_*Θ̂ = Θ̂` and `f_*f^*Θ̂' = Θ̂'`. -/
def InvB : Prop :=
  ∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d d' : Diagram X Y, EPLoc.homMk d = f → EPLoc.homMk d' = f →
      (∀ Θ T, IsOrientedPairB X Θ T →
        d'.pullTheta (d.pushTheta Θ) = Θ ∧
        ∀ x ∈ X.X.PObj.smoothSet, d'.pullSection (d.pushSection T) x = T x) ∧
      (∀ Θ' T', IsOrientedPairB Y Θ' T' →
        d'.pushTheta (d.pullTheta Θ') = Θ' ∧
        ∀ y ∈ Y.X.PObj.smoothSet, d'.pushSection (d.pullSection T') y = T' y)

/-- Definition 11.3.6 and (11.10). -/
def B : Prop := PairsB ∧ CompB ∧ InvB

end RoundTrip.V11_22
