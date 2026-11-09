import Polyfold
/-! Blind formalization of V9_34 (the text's Part II, §9.3, Definition 9.3.6, p. 425 of the
Springer 2021 book; 2017: Definition 9.10, p. 314): tame `Θ`.

Text: `Θ` is tame if every `x ∈ supp(Θ)` has an open `U(x)` with the natural `G_x`-action and the
properness property and a local branching structure on it whose `Mᵢ` have equivalent tame
structures; in particular every `Mᵢ` is then a manifold with boundary with corners.

Choices:
- This item is a definition.  B (a) says the project's `X.IsTameBranched Θ` is my `IsTameB X Θ`,
  for every branched ep⁺-subgroupoid `Θ` (the definition is made for those; project's
  `IsBranchedEpSubgroupoid`, V9_1).  B (b) is the "in particular".
- Setting: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor`.
- "`U(x)` with the natural `G_x`-action": my `IsNatAction X x U Φ Γ`, copied from
  `RoundTrip/Blind/V7_21.lean` (the data of Theorem 7.1: `U` open, `x ∈ U`, `Φ : G_x → Diff_sc(U)`
  a homomorphism, `Γ : G_x × U → 𝐗` sc-smooth with `Γ(g, x) = g`, `s Γ(g, y) = y`,
  `t Γ(g, y) = Φ(g)(y)`, every morphism between points of `U` is `Γ(g, s h)` for a unique `g`).
  I did NOT use the project's `NaturalRep`, which also demands `U` connected (see V7_21); the two
  readings should give the same tame `Θ` (pass to the component of `x`, which is `G_x`-invariant),
  but B (a) needs that argument.
- "the properness property": the project's `X.HasPropernessProperty U` (Definition 7.17,
  `#print`ed: `U` open and `cl_X(U)` proper; compared with the text in
  `RoundTrip/Blind/V7_59.lean`).
- "a local branching structure on it": a project `LocalBranchingStructure Θ x` with `U(x)` as its
  neighbourhood.  "whose `Mᵢ` have equivalent tame structures": the M-polyfold structure that `Mᵢ`
  inherits as a sub-M-polyfold is equivalent to a tame one, the project's
  `HasTameInducedStructure` (`#print`ed: `Mᵢ` is a sub-M-polyfold and its induced structure is
  tame, `MPolyfold.IsTame` = an equivalent atlas of tame retracts, Definition 2.37).
- (b) "every `Mᵢ` is then a manifold with boundary with corners": for every such data at every
  `x ∈ supp Θ`, the induced structure on every `Mᵢ` (with some paracompactness, which the induced
  structure needs) is a manifold with boundary with corners: the project's
  `MPolyfold.IsManifoldWithCornersLoc` (`#print`ed: an equivalent atlas of charts on relatively
  open subsets of partial quadrants in finite-dimensional spaces).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_34
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The natural `G_x`-action on the open neighbourhood `U` of `x` (the data `Φ`, `Γ` of
Theorem 7.1), as in `RoundTrip/Blind/V7_21.lean`. -/
structure IsNatAction (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor) : Prop where
  isOpen : IsOpen U
  mem : x ∈ U
  diffeo : ∀ g, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U
  hom : ∀ g h, ∀ y ∈ U, Φ (g * h) y = Φ g (Φ h y)
  smooth : ∀ g, X.PObj.IsScSmoothOn X.PMor (Γ g) U
  Γ_x : ∀ g, Γ g x = g.val
  src_tgt : ∀ g, ∀ y ∈ U, X.src (Γ g y) = y ∧ X.tgt (Γ g y) = Φ g y
  unique : ∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g, Γ g (X.src h) = h

/-- The data of Definition 9.3.6 at `x`: `U(x)` with the natural `G_x`-action and the properness
property, and a local branching structure on `U(x)` whose `Mᵢ` have tame induced structures. -/
def IsTameDataB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (x : Obj) (U : Set Obj)
    (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor)
    (B : X.LocalBranchingStructure Θ x) : Prop :=
  IsNatAction X x U Φ Γ ∧ X.HasPropernessProperty U ∧ B.U = U ∧
    ∀ i, X.PObj.HasTameInducedStructure (B.M i)

/-- **Definition 9.3.6**: `Θ` is tame. -/
def IsTameB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) : Prop :=
  ∀ x ∈ EpGroupoid.supp Θ, ∃ (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj)
    (Γ : X.Isotropy x → Obj → Mor) (B : X.LocalBranchingStructure Θ x),
    IsTameDataB X Θ x U Φ Γ B

end

/-- **Definition 9.3.6**: (a) the project's tame branched ep⁺-subgroupoids are the text's;
(b) the sheets of the local branching structures in the definition are manifolds with boundary
with corners. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    -- (a)
    (X.IsTameBranched Θ ↔ IsTameB X Θ) ∧
    -- (b)
    (∀ x ∈ EpGroupoid.supp Θ, ∀ (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj)
      (Γ : X.Isotropy x → Obj → Mor) (B : X.LocalBranchingStructure Θ x),
      IsTameDataB X Θ x U Φ Γ B → ∀ i,
        ∃ (hM : X.PObj.IsSubMPolyfold (B.M i)) (_ : ParacompactSpace (B.M i)),
          (MPolyfold.subPolyfold hM).IsManifoldWithCornersLoc)

end RoundTrip.V9_34
