import Polyfold.Chapter11.BoundaryOrientationEquiv

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 11,
§11.3: **Theorem 11.3.9** (2021 p. 542; 2017: Theorem 11.7) as an equality of oriented pairs,
`∂(f_*Θ̂) = f_*(∂Θ̂)` and `∂(f^*Θ̂') = f^*(∂Θ̂')`, with `∂Θ̂ := (∂Θ, T̂_∂Θ)` the abbreviation
after Definition 9.3.10 (2021 p. 428).  Numbers and pages are the 2021 text's.

## The text, paraphrased

(p. 428, after Definition 9.3.10) For an oriented, tame, branched ep⁺-subgroupoid one abbreviates
`Θ̂ := (Θ, T̂_Θ)` and `∂Θ̂ := (∂Θ, T̂_∂Θ)`.  (p. 542, Theorem 11.3.9) For a generalized
isomorphism `f`, `∂(f_*Θ̂) = f_*(∂Θ̂)` and `∂(f^*Θ̂') = f^*(∂Θ̂')`; the proof is left to the reader.

## What is formalized (namespace `Polyfold.EPLocalization`)

* `OrientedPair X`: pairs `(Θ, T̂)` of a function `X → ℚ` and a section of `Ĝr(X)`, with the
  push-forward and pull-back `OrientedPair.push f`, `OrientedPair.pull f` (componentwise, as in
  Definition 11.3.6).
* `OrientedBranched.toPair` (`Θ̂ = (Θ, T̂_Θ)`) and **`OrientedBranched.boundary`**
  (`∂Θ̂ = (∂Θ, T̂_∂Θ)`, with the intrinsic boundary orientation of Definition 9.3.10, V9.38);
  `toPair_push`, `toPair_pull`: `f_*Θ̂` of Definition 11.3.6 is the pushed pair.
* `OrientedTameBranched X`: an oriented branched ep⁺-subgroupoid with a tame orientation
  (Definition 9.3.6), the hypothesis of Definition 9.3.10 and of Theorem 11.3.9.
* **`theorem_11_3_9_push_pair`**: `(f_*Θ̂).boundary = f_*(∂Θ̂)`; **`theorem_11_3_9_pull_pair`**:
  `(f^*Θ̂').boundary = f^*(∂Θ̂')`, corollaries of the componentwise
  `EPLoc.theorem_11_3_9_push_boundaryOrientation`, `EPLoc.theorem_11_3_9_pull_boundaryOrientation`.
  They hold for every oriented branched ep⁺-subgroupoid; tameness is not used.  The tame forms are
  `OrientedTameBranched.theorem_11_3_9_push`, `OrientedTameBranched.theorem_11_3_9_pull`.
* Witnesses: `example935OrientedTame` (Example 9.3.5 on `ℝ²` is oriented and tame) and
  `theorem_11_3_9_push_pair_example935` (the corollary along the identity generalized isomorphism).

## Reading

The text writes `∂Θ̂` only as the pair `(∂Θ, T̂_∂Θ)`; it does not state that `∂Θ` is itself a
branched ep⁺-subgroupoid with orientation `T̂_∂Θ`, and that is not formalized here, so `∂Θ̂` is
an `OrientedPair`, not an `OrientedBranched`.  The tameness of `f_*Θ̂` is not needed for the
equalities.
-/

set_option maxSynthPendingDepth 3

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace EPLocalization

open EpGroupoid MPolyfold

variable {X Y : EP.{u}}

/-- **A pair `(Θ, T̂)`** (2021 p. 428): a function `X → ℚ` and a section of `Ĝr(X)`, the shape of
`Θ̂ = (Θ, T̂_Θ)` and `∂Θ̂ = (∂Θ, T̂_∂Θ)`. -/
abbrev OrientedPair (X : EP.{u}) : Type (max u 1) :=
  (X.Obj → ℚ) × (X.Obj → X.X.PObj.OrTangent →₀ ℚ)

namespace OrientedPair

/-- `f_*(Θ, T̂) = (f_*Θ, f_*T̂)` (Definition 11.3.6, componentwise). -/
def push (f : EPLoc.of X ⟶ EPLoc.of Y) (p : OrientedPair X) : OrientedPair Y :=
  (EPLoc.pushTheta f p.1, EPLoc.pushSection f p.2)

/-- `f^*(Θ', T̂') = (f^*Θ', f^*T̂')` (Definition 11.3.6, componentwise). -/
def pull (f : EPLoc.of X ⟶ EPLoc.of Y) (p : OrientedPair Y) : OrientedPair X :=
  (EPLoc.pullTheta f p.1, EPLoc.pullSection f p.2)

end OrientedPair

namespace OrientedBranched

/-- `Θ̂ = (Θ, T̂_Θ)` as a pair. -/
def toPair (A : OrientedBranched X) : OrientedPair X := (A.Θ, A.T)

/-- **`∂Θ̂ = (∂Θ, T̂_∂Θ)`** (2021 p. 428, after Definition 9.3.10): the boundary `∂Θ` of
Definition 9.2.16 with the induced orientation `T̂_∂Θ` of Definition 9.3.10 (the intrinsic
`boundaryOrientation`, built from the boundary operation of Definition 9.3.8). -/
def boundary (A : OrientedBranched X) : OrientedPair X :=
  (X.X.boundaryTheta A.Θ, X.X.boundaryOrientation A.T)

theorem toPair_push {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f)
    (A : OrientedBranched X) : (A.push hf).toPair = A.toPair.push f := rfl

theorem toPair_pull {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f)
    (A : OrientedBranched Y) : (A.pull hf).toPair = A.toPair.pull f := rfl

/-- **Theorem 11.3.9, push-forward, for pairs** (2021 p. 542): `∂(f_*Θ̂) = f_*(∂Θ̂)` for a
generalized isomorphism `f` and every oriented branched ep⁺-subgroupoid `Θ̂`. -/
theorem theorem_11_3_9_push_pair {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f)
    (A : OrientedBranched X) : (A.push hf).boundary = A.boundary.push f := by
  obtain ⟨h1, h2⟩ := EPLoc.theorem_11_3_9_push_boundaryOrientation hf A.isBranchedEpSubgroupoid
    A.isOrientation.isGrHatSection
  exact Prod.ext h1.symm h2.symm

/-- **Theorem 11.3.9, pull-back, for pairs** (2021 p. 542): `∂(f^*Θ̂') = f^*(∂Θ̂')`. -/
theorem theorem_11_3_9_pull_pair {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f)
    (A : OrientedBranched Y) : (A.pull hf).boundary = A.boundary.pull f := by
  obtain ⟨h1, h2⟩ := EPLoc.theorem_11_3_9_pull_boundaryOrientation hf A.isBranchedEpSubgroupoid
    A.isOrientation.isGrHatSection
  exact Prod.ext h1.symm h2.symm

end OrientedBranched

/-- **An oriented, tame, branched ep⁺-subgroupoid `Θ̂`** (the hypothesis of Definition 9.3.10,
2021 p. 427, and of Theorem 11.3.9): an oriented branched ep⁺-subgroupoid whose orientation is
represented near every point of `supp(Θ)` by oriented branching structures with tame `Mᵢ`. -/
structure OrientedTameBranched (X : EP.{u}) extends OrientedBranched X where
  isTame : X.X.IsTameOrientation Θ T

namespace OrientedTameBranched

/-- `∂Θ̂ = (∂Θ, T̂_∂Θ)` (Definition 9.3.10 and the abbreviation after it). -/
def boundary (A : OrientedTameBranched X) : OrientedPair X := A.toOrientedBranched.boundary

/-- For oriented tame `Θ̂`, the intrinsic `T̂_∂Θ` is Chapter 9's `boundaryLift boundaryOp` on
`X_∞` (`boundaryLift_boundaryOp_eq_boundaryOrientation`). -/
theorem boundary_snd_eq_boundaryLift (A : OrientedTameBranched X) {y : X.Obj}
    (hy : y ∈ X.X.PObj.smoothSet) :
    A.boundary.2 y = X.X.boundaryLift X.X.PObj.boundaryOp A.T y :=
  (X.X.boundaryLift_boundaryOp_eq_boundaryOrientation A.isOrientation A.isTame hy).symm

/-- **Theorem 11.3.9, push-forward** (2021 p. 542), for oriented tame `Θ̂`:
`∂(f_*Θ̂) = f_*(∂Θ̂)`. -/
theorem theorem_11_3_9_push {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f)
    (A : OrientedTameBranched X) :
    (A.toOrientedBranched.push hf).boundary = A.boundary.push f :=
  A.toOrientedBranched.theorem_11_3_9_push_pair hf

/-- **Theorem 11.3.9, pull-back** (2021 p. 542), for oriented tame `Θ̂'`:
`∂(f^*Θ̂') = f^*(∂Θ̂')`. -/
theorem theorem_11_3_9_pull {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f)
    (A : OrientedTameBranched Y) :
    (A.toOrientedBranched.pull hf).boundary = A.boundary.pull f :=
  A.toOrientedBranched.theorem_11_3_9_pull_pair hf

end OrientedTameBranched

end EPLocalization

/-! ### Witnesses -/

namespace EpGroupoid.Examples

open EPLocalization CategoryTheory

/-- **Witness**: Example 9.3.5's `(Θ, T̂¹)` on `ℝ²` is an oriented, tame, branched
ep⁺-subgroupoid. -/
def example935OrientedTame : OrientedTameBranched rn2EP :=
  ⟨example935Oriented, isTameOrientation_example935⟩

/-- **Witness**: Theorem 11.3.9 for pairs along the identity generalized isomorphism of `ℝ²`. -/
theorem theorem_11_3_9_push_pair_example935 :
    (example935OrientedTame.toOrientedBranched.push isGeneralizedIso_id_rn2EP).boundary =
      example935OrientedTame.boundary.push (𝟙 (EPLoc.of rn2EP)) :=
  example935OrientedTame.theorem_11_3_9_push isGeneralizedIso_id_rn2EP

end EpGroupoid.Examples

end Polyfold
