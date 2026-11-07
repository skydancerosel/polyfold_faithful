import Polyfold
/-! Blind formalization of V7_17 (the 2017 book, Part II, §7.1, Theorem 7.1, p. 231: the natural
representation of `G_x`). Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files) with their topologies
  (`T2`, paracompact) as instances and `X : EpGroupoid Obj Mor` (the project's Definition 7.3,
  fields read with `#print`); `PObj`, `PMor` are the M-polyfold structures of `X` and `𝐗`.
- `G = G_x` is my type `Gx X x = {g : Mor // s g = x ∧ t g = x}` (Definition 7.2), with product
  `g · h = g ∘ h = X.comp g h`; I do not use the project's `Isotropy` group instance (its
  definition is not in the vocabulary).
- `Φ : G → Diff_sc(U)` is a function `Φ : Gx X x → Obj → Obj` (values off `U` are junk and never
  used): every `Φ g` is an sc-diffeomorphism of the open set `U` onto itself (project's
  `MPolyfold.IsScDiffeoOn` with some inverse, read with `#print`: sc-smooth both ways, maps `U`
  to `U`, mutually inverse on `U`), and "group homomorphism" is `Φ(g ∘ h) = Φ(g) ∘ Φ(h)` on `U`
  (the product of `Diff_sc(U)` is composition; `Φ(1) = id` and `Φ(g⁻¹) = Φ(g)⁻¹` follow). The
  product `g ∘ h` is passed as any `k` with `k.1 = X.comp g.1 h.1`, to avoid proof terms.
- `Γ : G × U → 𝐗` is curried, `Γ : Gx X x → Obj → Mor` (junk off `U`). "sc-smooth on `G × U`":
  `G × U` carries the M-polyfold structure of the disjoint union of the copies `{g} × U` of `U`
  (stated on p. 232, item V7_20), so sc-smoothness means: each `Γ g` is sc-smooth on the open set
  `U ⊆ X` (`MPolyfold.IsScSmoothOn PObj PMor (Γ g) U`).
- (1) `Γ(g, x) = g`; (2) `s Γ(g, y) = y`, `t Γ(g, y) = Φ(g)(y)` for `y ∈ U`; (3) every
  morphism `h` with `s h, t h ∈ U` is `Γ(g, s h)` for a unique `g`, and (the "i.e.") `Γ` is a
  bijection from `G × U` onto `𝐔 = {φ | s φ ∈ U ∧ t φ ∈ U}` (`Set.BijOn` of the uncurried `Γ`
  from `univ ×ˢ U`). Both forms of (3) are included; given (2) they are equivalent.
- `U`: an open set with `x ∈ U ⊆ V`, for every open neighbourhood `V` of `x`. The theorem does not
  ask `U` to be connected, so I do not.
- The sentence after the theorem (the name "natural representation", `g ∗ y = Φ(g)(y)`) is
  terminology, not a claim.
-/
namespace RoundTrip.V7_17
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The isotropy group `G_x`: the morphisms `x → x`. -/
def Gx (X : EpGroupoid Obj Mor) (x : Obj) : Type := {g : Mor // X.src g = x ∧ X.tgt g = x}

/-- The conclusions of Theorem 7.1 for the neighbourhood `U` and the data `Φ`, `Γ`. -/
def IsNatRepData (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : Gx X x → Obj → Obj) (Γ : Gx X x → Obj → Mor) : Prop :=
  -- `Φ(g) ∈ Diff_sc(U)`
  (∀ g : Gx X x, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U) ∧
  -- `Φ` is a group homomorphism: `Φ(g ∘ h) = Φ(g) ∘ Φ(h)` on `U`
  (∀ g h k : Gx X x, k.1 = X.comp g.1 h.1 → ∀ y ∈ U, Φ k y = Φ g (Φ h y)) ∧
  -- `Γ : G × U → 𝐗` is sc-smooth (on each copy `{g} × U`)
  (∀ g : Gx X x, X.PObj.IsScSmoothOn X.PMor (Γ g) U) ∧
  -- (1)
  (∀ g : Gx X x, Γ g x = g.1) ∧
  -- (2)
  (∀ g : Gx X x, ∀ y ∈ U, X.src (Γ g y) = y ∧ X.tgt (Γ g y) = Φ g y) ∧
  -- (3)
  (∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g : Gx X x, Γ g (X.src h) = h) ∧
  -- (3), "i.e.": `Γ : G × U → {φ | s φ, t φ ∈ U}` is a bijection
  Set.BijOn (fun p : Gx X x × Obj => Γ p.1 p.2) (Set.univ ×ˢ U)
    {φ : Mor | X.src φ ∈ U ∧ X.tgt φ ∈ U}

end

/-- Theorem 7.1: every open neighbourhood `V` of `x` contains an open neighbourhood `U` of `x`
carrying a homomorphism `Φ : G_x → Diff_sc(U)` and an sc-smooth `Γ : G_x × U → 𝐗` with
(1) `Γ(g, x) = g`, (2) `s Γ(g, y) = y`, `t Γ(g, y) = Φ(g)(y)`, (3) `Γ` bijective onto the
morphisms between points of `U`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (x : Obj) (V : Set Obj), IsOpen V → x ∈ V →
    ∃ (U : Set Obj) (Φ : Gx X x → Obj → Obj) (Γ : Gx X x → Obj → Mor),
      IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ IsNatRepData X x U Φ Γ

end RoundTrip.V7_17
