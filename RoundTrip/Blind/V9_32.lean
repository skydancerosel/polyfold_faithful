import Polyfold
/-! Blind formalization of V9_32 (the text's Part II, §9.3, Lemma 9.3.4, p. 423 of the Springer
2021 book; 2017: Lemma 9.10, p. 311): orientations are determined by good points.

Text: two orientations `T̂¹_Θ`, `T̂²_Θ` of a branched ep⁺-subgroupoid `Θ` which agree at good
points are the same.

Choices:
- Setting: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor` and
  `X.IsBranchedEpSubgroupoid Θ` (V9_1).  Orientations: my `IsOrientationB` (Definition 9.3.2,
  copied from `RoundTrip/Blind/V9_30.lean`).
- Good points: Definition 9.2.2 (V9_15) defines them only for an EQUIDIMENSIONAL `Θ`, relative to a
  local branching structure: `y ∈ ⋃ᵢ Mᵢ` with an open `V ∋ y`, `V ⊆ U(x)`, and
  `Mᵢ ∩ V = Mⱼ ∩ V` whenever `y ∈ Mᵢ ∩ Mⱼ` (my `IsGoodAt`, as in `RoundTrip/Blind/V9_15.lean`).
  "Good points" of `Θ` (the set `S^g_Θ` of V9_19; being good is intrinsic by V9_16, V9_17): the
  `y ∈ supp Θ` that are good for some local branching structure at some `x` with `y ∈ U(x)`
  (`goodSetB`).
- Since good points presuppose equidimensionality, I add the hypothesis "`Θ` is `n`-dimensional
  for some `n`" (the project's `X.IsNDimensional Θ n`, checked against the text in V9_2; the same
  reading as `RoundTrip/Blind/V9_15.lean`).  Without it, with good points defined by the same
  formula, the lemma fails: `Θ = 1_{ℝ × {0}} + 1_{(0,0)}` on `ℝ²` (identity morphisms only) has the
  bad point `0` only, and the orientations `(line, +) + (point, ±)` agree at all good points but
  differ at `0`.
- "agree at good points": `T̂¹(y) = T̂²(y)` for every good `y`; "are the same": equal at every
  smooth object (the domain `X^∞` of the section functors; values elsewhere are junk).
- With the added hypothesis nothing looks false to me.
-/
namespace RoundTrip.V9_32
open Polyfold

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

/-- Definition 9.2.2 (as in `RoundTrip/Blind/V9_15.lean`): `y` is a good point of the local
branching structure `B` on `U(x)`. -/
def IsGoodAt {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (y : Obj) : Prop :=
  y ∈ ⋃ i, B.M i ∧
    ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ V ⊆ B.U ∧
      ∀ i j : B.ι, y ∈ B.M i ∩ B.M j → B.M i ∩ V = B.M j ∩ V

/-- The good points `S^g_Θ` of `supp Θ`. -/
def goodSetB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) : Set Obj :=
  {y | y ∈ EpGroupoid.supp Θ ∧
    ∃ (x : Obj) (B : X.LocalBranchingStructure Θ x), y ∈ B.U ∧ IsGoodAt B y}

end

/-- **Lemma 9.3.4**: two orientations of an (equidimensional) branched ep⁺-subgroupoid which
agree at the good points agree everywhere on `X^∞`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    (∃ n : ℕ, X.IsNDimensional Θ n) →
    ∀ T₁ T₂ : Obj → X.PObj.OrTangent →₀ ℚ, IsOrientationB X Θ T₁ → IsOrientationB X Θ T₂ →
      (∀ y ∈ goodSetB X Θ, T₁ y = T₂ y) → ∀ y ∈ X.PObj.smoothSet, T₁ y = T₂ y

end RoundTrip.V9_32
