import Polyfold
/-! Blind formalization of V7_19 (the 2017 book, Part II, §7.1, p. 231, after Theorem 7.1: the
splitting `𝐔(x) = ⨆_{g ∈ G_x} 𝐔(g)`). Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files) with their topologies
  (`T2`, paracompact) as instances and `X : EpGroupoid Obj Mor` (the project's Definition 7.3,
  fields read with `#print`); `PObj`, `PMor` are the M-polyfold structures of `X` and `𝐗`.
- `G_x` is my type `Gx X x = {g : Mor // s g = x ∧ t g = x}`; "the finite group `G_x ⊂ 𝐗`" is
  the set `{g | s g = x ∧ t g = x}` of morphisms.
- "`U(x) = U` the open neighbourhood guaranteed by Theorem 7.1": `U` carries data `Φ`, `Γ`
  satisfying the conclusions of Theorem 7.1; `IsNatRepData` is copied verbatim from my `V7_17`
  (`Φ(g)` sc-diffeomorphisms of `U`, `Φ` multiplicative, `Γ(g, ·)` sc-smooth on `U`, (1)–(3)).
- `𝐔(x) = {φ | s φ ∈ U ∧ t φ ∈ U}` (`morU`); the sentence on the full subcategory
  `(U(x), 𝐔(x))` is a definition.
- "One can choose `U(x)` so small that …": the text shrinks the same `U(x)` twice (first so that
  `𝐔(x)` lies in a given small neighbourhood of `G_x`, then, connected, so that it splits); I
  read the outcome as one existence statement: for every open neighbourhood `V` of `x` and
  every open `W ⊆ 𝐗` containing `G_x` there is a connected open `U` with `x ∈ U ⊆ V`, carrying
  Theorem 7.1 data, with `𝐔(x) ⊆ W` and the splitting. (The quantifier over `V` expresses "so
  small"; it is not in the text explicitly for the second step.)
- The splitting: `UU : Gx X x → Set Mor` (the text's `𝐔(g)`) with `𝐔(g)` the connected
  component of `𝐔(x)` containing `g` (`connectedComponentIn morU g`; "enumerated by `g`" read
  as `g ∈ 𝐔(g)`), the `𝐔(g)` pairwise disjoint (so there are `#G_x` of them) and covering
  `𝐔(x)`; and
  `s, t : 𝐔(g) → U(x)` sc-diffeomorphisms (`MPolyfold.IsScDiffeoOn PMor PObj s σ (UU g) U` for
  some inverse `σ`, which includes that `𝐔(g)` is open in `𝐗`).
- "By the properness property", "using that `s` is a local sc-diffeomorphism" name the method,
  not hypotheses.
-/
namespace RoundTrip.V7_19
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The isotropy group `G_x`: the morphisms `x → x`. -/
def Gx (X : EpGroupoid Obj Mor) (x : Obj) : Type := {g : Mor // X.src g = x ∧ X.tgt g = x}

/-- The conclusions of Theorem 7.1 for the neighbourhood `U` and the data `Φ`, `Γ` (as in
`V7_17`). -/
def IsNatRepData (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : Gx X x → Obj → Obj) (Γ : Gx X x → Obj → Mor) : Prop :=
  (∀ g : Gx X x, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U) ∧
  (∀ g h k : Gx X x, k.1 = X.comp g.1 h.1 → ∀ y ∈ U, Φ k y = Φ g (Φ h y)) ∧
  (∀ g : Gx X x, X.PObj.IsScSmoothOn X.PMor (Γ g) U) ∧
  (∀ g : Gx X x, Γ g x = g.1) ∧
  (∀ g : Gx X x, ∀ y ∈ U, X.src (Γ g y) = y ∧ X.tgt (Γ g y) = Φ g y) ∧
  (∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g : Gx X x, Γ g (X.src h) = h) ∧
  Set.BijOn (fun p : Gx X x × Obj => Γ p.1 p.2) (Set.univ ×ˢ U)
    {φ : Mor | X.src φ ∈ U ∧ X.tgt φ ∈ U}

/-- `𝐔(x)`: the morphisms between points of `U`. -/
def morU (X : EpGroupoid Obj Mor) (U : Set Obj) : Set Mor := {φ | X.src φ ∈ U ∧ X.tgt φ ∈ U}

end

/-- Shrinking the Theorem 7.1 neighbourhood: `U(x)` can be chosen connected, inside any given
`V`, with `𝐔(x)` inside any given open neighbourhood `W` of `G_x`, and with `𝐔(x)` the disjoint
union of its connected components `𝐔(g) ∋ g`, `g ∈ G_x`, on which `s` and `t` are
sc-diffeomorphisms onto `U(x)`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (x : Obj) (V : Set Obj) (W : Set Mor), IsOpen V → x ∈ V → IsOpen W →
    {g : Mor | X.src g = x ∧ X.tgt g = x} ⊆ W →
    ∃ (U : Set Obj) (Φ : Gx X x → Obj → Obj) (Γ : Gx X x → Obj → Mor),
      IsOpen U ∧ IsConnected U ∧ x ∈ U ∧ U ⊆ V ∧ IsNatRepData X x U Φ Γ ∧
      morU X U ⊆ W ∧
      ∃ UU : Gx X x → Set Mor,
        (∀ g : Gx X x, UU g = connectedComponentIn (morU X U) g.1) ∧
        Pairwise (fun g h : Gx X x => Disjoint (UU g) (UU h)) ∧
        (⋃ g : Gx X x, UU g) = morU X U ∧
        ∀ g : Gx X x,
          (∃ σ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.src σ (UU g) U) ∧
          (∃ τ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.tgt τ (UU g) U)

end RoundTrip.V7_19
