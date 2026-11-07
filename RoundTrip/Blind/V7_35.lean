import Polyfold
/-! Blind formalization of V7_35 (the 2017 book's Part II, §7.2, Lemma 7.3, pp. 239–240).

Text: for an ep-groupoid `X` the following are equivalent. (1) `X` is effective. (2) For every
object `x` and every open neighbourhood `V(x)` there is an open neighbourhood `U(x) ⊆ V(x)`
equipped with the natural `G_x`-action such that `Φ : G_x → Diff_sc(U(x))` is injective.

Choices:
- Setting: `Obj Mor : Type` (spaces in `Type`; the project's `EpGroupoid` is universe-polymorphic,
  this is `u = 0`), with their topologies, Hausdorff and paracompact, `X : EpGroupoid Obj Mor`
  (the project's Definition 7.3, checked with `#print`; see `RoundTrip/Blind/V7_33.lean`).
- "effective" is my `IsEffectiveB` (Definition 7.11, as in `RoundTrip/Blind/V7_33.lean`).
- `G_x` is the project's `X.Isotropy x` with its group structure; I checked by `rfl` that
  `(g * h).val = g ∘ h`, `1.val = 1_x`, `g⁻¹.val = ι(g)`.
- "`U(x)` equipped with the natural `G_x`-action": the data `(Φ, Γ)` of Theorem 7.1 (statement
  of item V7_17) on `U = U(x)`, my structure `NatRepB X x`: `U` open, connected, `x ∈ U`; `Φ(g)`
  an sc-diffeomorphism of `U` onto `U` (the project's `IsScDiffeoOn`, checked with `#print`: both
  maps sc-smooth on the open sets, `MapsTo` both ways, mutually inverse there) for every `g`;
  `Φ(gh) = Φ(g) ∘ Φ(h)` on `U` (a homomorphism into `Diff_sc(U)`); `Γ : G_x × U → 𝐗` sc-smooth,
  read as `Γ(g, ·)` sc-smooth on `U` for every `g` (`G_x` is finite and discrete); (1)
  `Γ(g, x) = g`; (2) `s Γ(g, y) = y`, `t Γ(g, y) = Φ(g)(y)` on `U`; (3) every morphism `h` between
  points of `U` is `Γ(g, s h)` for a unique `g`.  Total functions `Obj → Obj`, `Obj → Mor`; only
  their values on `U` matter.  I wrote my own structure rather than use the project's
  `NaturalRep` (its fields, seen with `#print`, turn out to be the same list).
- Connectedness of `U` is an added hypothesis: Theorem 7.1 as quoted does not ask it, but the
  text presupposes it (p. 231, item V7_19: "one chooses the connected open neighborhood `U(x)`";
  Proposition 7.5 also has connected `U(y)`), and without it (2) ⇒ (1) is FALSE: for
  `G = {1, a, b, ab} ≅ (ℤ/2)²` acting on `ℝ` by `a = id`, `b = −id` (translation groupoid,
  `x = 0`, not effective), take `U = (−ε, ε) ∪ ±(c − ε, c + ε)` and on the two outer intervals
  twist the action by the automorphism `θ : a ↔ b` (`Γ(g, y) = (θ g, y)`); all of Theorem 7.1
  holds, `Φ` is injective, and `U` is as small as one likes.
- "`Φ` injective": `Φ(g) = Φ(h)` as maps of `U` implies `g = h`.
- "open neighbourhood `V(x)`": every open `V ⊆ Obj` with `x ∈ V`.
- With connected `U`, nothing looks false to me.
-/
namespace RoundTrip.V7_35
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Definition 7.11**: `X` is effective: for every `x`, every `g ∈ G_x ∖ {1_x}` and every open
neighbourhood `W` of `g` in `𝐗` there is `ψ ∈ W` with `s ψ ≠ t ψ`. -/
def IsEffectiveB (X : EpGroupoid Obj Mor) : Prop :=
  ∀ (x : Obj) (g : X.Isotropy x), g.val ≠ X.unit x →
    ∀ W : Set Mor, IsOpen W → g.val ∈ W → ∃ ψ ∈ W, X.src ψ ≠ X.tgt ψ

/-- **The natural `G_x`-action on `U`** (the data of Theorem 7.1): a connected open `U ∋ x`, a
homomorphism `Φ : G_x → Diff_sc(U)` and an sc-smooth `Γ : G_x × U → 𝐗` with (1) `Γ(g, x) = g`,
(2) `s Γ(g, y) = y`, `t Γ(g, y) = Φ(g)(y)`, (3) `Γ(·, y)` is a bijection onto the morphisms from
`y` to points of `U`. -/
structure NatRepB (X : EpGroupoid Obj Mor) (x : Obj) where
  /-- The neighbourhood `U = U(x)`. -/
  U : Set Obj
  isOpen_U : IsOpen U
  isConnected_U : IsConnected U
  mem_U : x ∈ U
  /-- The action `Φ : G_x → Diff_sc(U)`. -/
  Φ : X.Isotropy x → Obj → Obj
  /-- The map `Γ : G_x × U → 𝐗`. -/
  Γ : X.Isotropy x → Obj → Mor
  diffeo : ∀ g, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U
  hom : ∀ g h, ∀ y ∈ U, Φ (g * h) y = Φ g (Φ h y)
  smooth : ∀ g, X.PObj.IsScSmoothOn X.PMor (Γ g) U
  Γ_x : ∀ g, Γ g x = g.val
  src_Γ : ∀ g, ∀ y ∈ U, X.src (Γ g y) = y
  tgt_Γ : ∀ g, ∀ y ∈ U, X.tgt (Γ g y) = Φ g y
  unique : ∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g, Γ g (X.src h) = h

end

/-- Lemma 7.3: `X` is effective iff every object has arbitrarily small neighbourhoods with the
natural action on which `Φ` is injective. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    IsEffectiveB X ↔
      ∀ (x : Obj) (V : Set Obj), IsOpen V → x ∈ V →
        ∃ R : NatRepB X x, R.U ⊆ V ∧
          ∀ g h : X.Isotropy x, (∀ y ∈ R.U, R.Φ g y = R.Φ h y) → g = h

end RoundTrip.V7_35
