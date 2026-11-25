import Polyfold
/-! Blind formalization of V17_130 (the text's Part II, §17.8, Proposition 17.8.6 and (17.99),
pp. 831–832 of the Springer 2021 book; new in the 2021 edition).

Text: a proper covering model can be restricted to a connected one on a `G`-invariant
neighbourhood of `ō`; the component `C` of `ō` is `G`-invariant (17.99).

Choices:
- Setting: universe `0` for both universe levels of the project's `ProperCoveringModel`: a finite
  discrete group `G` acting on a Hausdorff paracompact `O` with an M-polyfold structure `P` by
  sc-smooth maps (`hP`), an ep-groupoid `E` on `ObjE`, `MorE`, an ep-functor
  `τ̂ : E → G ⋉ O` (the project's `EpGroupoid.Examples.actionEpGroupoid hP`), and a proper
  covering model `M : ProperCoveringModel τ̂` (Definition 17.8.4, the project's structure; its
  docstring matches (1)–(3) of the definition).  `ō = M.pt`.
- "restricted to ... on a `G`-invariant neighbourhood `O'` of `ō`": an open `G`-invariant
  `O' ∋ ō` (`SubMulAction G O`, open); the restriction is `τ̂' : τ̂⁻¹(O') → G ⋉ O'` with the
  sets `U(y) ∩ τ̂⁻¹(O')`.
  "connected" (Definition 17.8.4, the project's `ProperCoveringModel.Connected`, `#print`ed:
  `ConnectedSpace` of the base) for the restriction over `O'` means `O'` connected; I write
  `IsConnected (O' : Set O)` directly, because the project's `restrictModel` needs paracompactness
  instances on `↥O'`, `τ̂⁻¹(O')`, ... that I did not want to quantify.  So B does not mention the
  restricted model itself; that the restriction to an open `G`-invariant `O' ∋ ō` is a proper
  covering model is the project's construction `restrictModel` (taken as given).
- The neighbourhood: the proof works inside `O* = ⋂_g g⁻¹ U` for an open neighbourhood `U` of `ō`
  and takes the component `C` of `ō` in `O*` (17.99).  I read the proposition as: for every open
  `U ∋ ō` there is such an `O' ⊆ U` (if the text only claims existence, this is stronger; it is
  what the construction gives).
- (17.99): for an open `U ∋ ō`, the connected component `C` of `ō` in `⋂_g g⁻¹ U` (Mathlib's
  `connectedComponentIn`) satisfies `g ∗ C ⊆ C` for all `g` (hence `g ∗ C = C`).  Written out
  with Mathlib, not with the project's `invariantComponent`.
- B is the conjunction.  Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_130
open Polyfold

/-- Proposition 17.8.6 and (17.99): a proper covering model restricts to a connected one over an
open `G`-invariant neighbourhood `O'` of `ō` inside any given open `U ∋ ō`; the component of `ō`
in `⋂_g g⁻¹U` is `G`-invariant. -/
def B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    (O : Type) [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
    (P : MPolyfold O) (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y)
    (ObjE MorE : Type) [TopologicalSpace ObjE] [T2Space ObjE] [ParacompactSpace ObjE]
    [TopologicalSpace MorE] [T2Space MorE] [ParacompactSpace MorE]
    (E : EpGroupoid ObjE MorE) (τ : EpFunctor E (EpGroupoid.Examples.actionEpGroupoid hP))
    (M : ProperCoveringModel τ),
    (∀ U : Set O, IsOpen U → M.pt ∈ U →
      ∃ O' : SubMulAction G O, IsOpen (O' : Set O) ∧ M.pt ∈ O' ∧
        (O' : Set O) ⊆ U ∧ IsConnected (O' : Set O)) ∧
    (∀ U : Set O, IsOpen U → M.pt ∈ U → ∀ (g : G),
      ∀ x ∈ connectedComponentIn (⋂ h : G, (fun y => h • y) ⁻¹' U) M.pt,
        g • x ∈ connectedComponentIn (⋂ h : G, (fun y => h • y) ⁻¹' U) M.pt)

end RoundTrip.V17_130
