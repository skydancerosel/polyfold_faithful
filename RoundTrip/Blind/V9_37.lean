import Polyfold
/-! Blind formalization of V9_37 (the text's Part II, §9.3, (9.11), p. 427, and Proposition 9.3.9,
p. 428 of the Springer 2021 book; new in the 2021 edition): the boundary orientation does not
depend on the structure.

Text: for two oriented local branching structures the parts of `T̂_Θ(y)` of each degree
`ℓ = d_{Mᵢ}(y)` agree (9.11), since tangent spaces of different degree never coincide
(Lemma 9.3.7); the definition of `T̂_{∂Θ}` does not depend on the structure.

Choices:
- Setting: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor`, a branched
  ep⁺-subgroupoid `Θ` (project's `IsBranchedEpSubgroupoid`, V9_1) with an orientation `T` (my
  `IsOrientationB`, Definition 9.3.2, copied from `RoundTrip/Blind/V9_30.lean`).
- The argument cites Lemma 9.3.7, which needs a tame ambient M-polyfold and sheets with tame
  induced structures; I add these presupposed hypotheses: the object M-polyfold `X.PObj` is tame
  (`MPolyfold.IsTame`), and every sheet of the two structures has a tame induced structure
  (`HasTameInducedStructure`), as for the tame structures of Definition 9.3.6.  I do NOT require
  `Θ` tame nor the natural action / properness property of Definition 9.3.6 (not used).
- "two oriented local branching structures": two local branching structures `B`, `B'` at the same
  `x ∈ supp Θ` (possibly different `U`, `U'`), with dimensions `nᵢ` and orientations `oᵢ` of the
  sheets (project's `SubmanifoldOrientation`), both representing `T` by (9.9) at the smooth points
  of their neighbourhoods.  Claims at every `y ∈ U ∩ U'`.
- (9.11): for every `ℓ`, `∑_{i : y ∈ Mᵢ, d_{Mᵢ}(y) = ℓ} σᵢ T_y(Mᵢ, oᵢ)` is the same for `B` and
  `B'` (`degSumB`; `d_{Mᵢ}` my `dMB` of `RoundTrip/Blind/V9_35.lean`).
- Proposition 9.3.9: `T̂_{∂Θ}(y)` by (9.12) (V9_38) is `∑_{i : y ∈ ∂Mᵢ, d_{Mᵢ}(y) = 1}
  σᵢ T_y(∂Mᵢ, o_{∂Mᵢ})` (`bdSumB`), the same for `B` and `B'`.  `T_y(∂Mᵢ, o_{∂Mᵢ})` is the oriented
  tangent set `(T_y∂Mᵢ, frames a with (e, a) positive for oᵢ)` of Definition 9.3.8 (`bdOrB`),
  with "outward `e`" as in my `RoundTrip/Blind/V9_36.lean` (`IsOutwardB`), and the frames taken
  for SOME outward `e` (by Definition 9.3.8 they do not depend on `e`); junk for `nᵢ = 0`, where
  no point has `d_{Mᵢ}(y) = 1`.  Off `supp Θ` both sums are `0` (no sheet through `y`).
- The "since …" clause is the reason (Lemma 9.3.7 = V9_35), not formalized again.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_37
open Polyfold

section
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]

open Classical in
/-- `d_M(y)`: the degeneracy index of `y` for the structure induced on the sub-M-polyfold `M`
(`0` if `M` is not a sub-M-polyfold or `y ∉ M`). -/
noncomputable def dMB (P : MPolyfold Z) (M : Set Z) (y : Z) : ℕ :=
  if h : P.IsSubMPolyfold M ∧ y ∈ M then P.subDegIndex h.1 ⟨y, h.2⟩ else 0

/-- `e` is an outward pointing vector of `M` at `y` (as in `RoundTrip/Blind/V9_36.lean`). -/
def IsOutwardB (P : MPolyfold Z) (M : Set Z) (y : Z) (e : P.TangentSpace) : Prop :=
  e ∈ P.submanifoldTangent M y ∧
  ∀ (φ : MChart Z) (hφ : P.IsChart φ), y ∈ φ.source →
    MPolyfold.chartVec hφ e ∉
      posTangentConeAt (φ.toPartialEquiv '' (M ∩ φ.source)) (φ.toPartialEquiv y)

/-- `T_y(∂M, o_{∂M})` (Definition 9.3.8): `T_y∂M` with the frames `a` such that `(e, a)` is
positive for `o_y`, `e` outward; a junk value for `n = 0`. -/
def bdOrB {P : MPolyfold Z} {M : Set Z} : {n : ℕ} → P.SubmanifoldOrientation M n → Z →
    P.OrTangent
  | 0, _, _ => ⟨0, ∅, ∅⟩
  | m + 1, o, y =>
    ⟨m, P.submanifoldTangent (P.submanifoldBoundary M) y,
      {a | (∀ i, a i ∈ P.submanifoldTangent (P.submanifoldBoundary M) y) ∧
        ∃ e, IsOutwardB P M y e ∧ (Fin.cons e a : Fin (m + 1) → P.TangentSpace) ∈ o.frames y}⟩

end

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

open Classical in
/-- `∑_{i : y ∈ Mᵢ} σᵢ T_y(Mᵢ, oᵢ)` (as in `RoundTrip/Blind/V9_30.lean`). -/
noncomputable def orSumB {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)) (y : Obj) :
    X.PObj.OrTangent →₀ ℚ :=
  ∑ i with y ∈ B.M i, Finsupp.single ((o i).tangent y) (B.σ i)

/-- **Definition 9.3.2** (as in `RoundTrip/Blind/V9_30.lean`): `T` is an orientation of `Θ`. -/
structure IsOrientationB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ)
    (T : Obj → X.PObj.OrTangent →₀ ℚ) : Prop where
  mem : ∀ x ∈ X.PObj.smoothSet,
    (∀ g, 0 ≤ T x g) ∧ ∀ g ∈ (T x).support, X.PObj.IsOrientedAt x g
  functor : ∀ φ : Mor, X.src φ ∈ X.PObj.smoothSet →
    Finsupp.mapDomain (MPolyfold.OrTangent.push (X.tangentMor φ)) (T (X.src φ)) = T (X.tgt φ)
  lifts : ∀ x ∈ X.PObj.smoothSet,
    Finsupp.mapDomain MPolyfold.OrTangent.carrier (T x) = X.tangentValue Θ x
  locRep : ∀ x ∈ EpGroupoid.supp Θ, ∃ (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)),
    ∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = orSumB B n o y

open Classical in
/-- The degree-`ℓ` part `∑_{i : y ∈ Mᵢ, d_{Mᵢ}(y) = ℓ} σᵢ T_y(Mᵢ, oᵢ)` of (9.11). -/
noncomputable def degSumB {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)) (y : Obj) (ℓ : ℕ) :
    X.PObj.OrTangent →₀ ℚ :=
  ∑ i with y ∈ B.M i ∧ dMB X.PObj (B.M i) y = ℓ, Finsupp.single ((o i).tangent y) (B.σ i)

open Classical in
/-- (9.12): `∑_{i : y ∈ ∂Mᵢ, d_{Mᵢ}(y) = 1} σᵢ T_y(∂Mᵢ, o_{∂Mᵢ})`. -/
noncomputable def bdSumB {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)) (y : Obj) :
    X.PObj.OrTangent →₀ ℚ :=
  ∑ i with y ∈ X.PObj.submanifoldBoundary (B.M i) ∧ dMB X.PObj (B.M i) y = 1,
    Finsupp.single (bdOrB (o i) y) (B.σ i)

end

/-- **(9.11) and Proposition 9.3.9**: for two oriented local branching structures with tame
sheets representing the orientation `T̂_Θ` (tame object M-polyfold), the degree-`ℓ` parts of
`T̂_Θ(y)` agree for every `ℓ`, and so do the sums (9.12) defining `T̂_{∂Θ}(y)`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor), X.PObj.IsTame →
    ∀ (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    ∀ T : Obj → X.PObj.OrTangent →₀ ℚ, IsOrientationB X Θ T →
    ∀ x ∈ EpGroupoid.supp Θ,
    ∀ (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
      (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i))
      (B' : X.LocalBranchingStructure Θ x) (n' : B'.ι → ℕ)
      (o' : ∀ i, X.PObj.SubmanifoldOrientation (B'.M i) (n' i)),
      (∀ i, X.PObj.HasTameInducedStructure (B.M i)) →
      (∀ i, X.PObj.HasTameInducedStructure (B'.M i)) →
      (∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = orSumB B n o y) →
      (∀ y ∈ B'.U, y ∈ X.PObj.smoothSet → T y = orSumB B' n' o' y) →
      ∀ y ∈ B.U ∩ B'.U,
        -- (9.11)
        (∀ ℓ : ℕ, degSumB B n o y ℓ = degSumB B' n' o' y ℓ) ∧
        -- Proposition 9.3.9
        bdSumB B n o y = bdSumB B' n' o' y

end RoundTrip.V9_37
