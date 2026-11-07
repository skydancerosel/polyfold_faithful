import Polyfold
/-! Blind formalization of V7_37 (the 2017 book's Part II, §7.2, before Definition 7.12, p. 241).

Text: every object `x` has a suitable open neighbourhood `U(x)`, which can be chosen arbitrarily
small, on which `G_x` acts by `Φ : G_x → Diff_sc(U(x))`.  `g ∈ G_x` acts trivially if `Φ(g) = 1`
for some open `U(x)` with the `G_x`-action.  `1_x` acts trivially.  Since `G_x` is finite, `U(x)`
can be chosen so small that `ker Φ` is the subgroup of the elements acting trivially; this
subgroup `T_x` is, as a kernel, a normal subgroup of `G_x`.

Choices:
- Setting: `Obj Mor : Type` (spaces in `Type`; the project's `EpGroupoid` is universe-polymorphic,
  this is `u = 0`), with their topologies, Hausdorff and paracompact, `X : EpGroupoid Obj Mor`
  (the project's Definition 7.3, checked with `#print`; see `RoundTrip/Blind/V7_33.lean`).
- `G_x` is the project's `X.Isotropy x` with its group structure; checked by `rfl`:
  `(g * h).val = g ∘ h`, `1.val = 1_x`, `g⁻¹.val = ι(g)`.
- "`U(x)` on which `G_x` acts by `Φ`" / "equipped with the `G_x`-action": the data of
  Theorem 7.1 (item V7_17), my structure `NatRepB X x` (as in `RoundTrip/Blind/V7_35.lean`: `U`
  open and connected, `x ∈ U`, `Φ(g) ∈ Diff_sc(U)`, `Φ` multiplicative on `U`, `Γ(g, ·)`
  sc-smooth on `U`, `Γ(g, x) = g`, `s Γ(g, y) = y`, `t Γ(g, y) = Φ(g)(y)`, unique `g` with
  `Γ(g, s h) = h`).  Connectedness is not in Theorem 7.1 as quoted; I add it as the text's
  presupposition (p. 231: "the connected open neighborhood `U(x)`"), as in V7_35, where it is
  needed.  Here it changes nothing: the component of `x` in a `G_x`-invariant `U` is again
  `G_x`-invariant and open (M-polyfolds are locally connected).
- "acts trivially" (`ActsTriviallyB`): there is such data `R` with `Φ(g) = id` on `R.U`.
  `T_x = {g | g acts trivially}` (`TxB`).  "`ker Φ`" for data `R`: `{g | Φ(g) = id on R.U}`.
- B is the conjunction of: (a) the reminder: every `x` has, inside every open `V ∋ x`, data `R`
  with `R.U ⊆ V`; (b) the definitional part: the project's `ActsTrivially` and `trivialSubgroup`
  (`#print` shows `ActsTrivially g = ∃ R : NaturalRep x, Φ g = id on R.U`) are my
  `ActsTriviallyB` and `TxB`; (c) `1_x` acts trivially; (d) "so small": inside every open
  `V ∋ x` there is data `R` with `R.U ⊆ V` and `ker Φ = T_x` (I read "can be chosen so small" as:
  arbitrarily small such `U(x)` exist); (e) `T_x` is (the carrier of) a normal subgroup of `G_x`.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_37
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

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

/-- `g ∈ G_x` **acts trivially**: `Φ(g) = 1` on `U(x)` for some `U(x)` with the natural action. -/
def ActsTriviallyB (X : EpGroupoid Obj Mor) {x : Obj} (g : X.Isotropy x) : Prop :=
  ∃ R : NatRepB X x, ∀ y ∈ R.U, R.Φ g y = y

/-- `T_x ⊆ G_x`: the elements acting trivially. -/
def TxB (X : EpGroupoid Obj Mor) (x : Obj) : Set (X.Isotropy x) :=
  {g | ActsTriviallyB X g}

end

/-- The elements of `G_x` acting trivially: arbitrarily small natural actions exist, `1_x` acts
trivially, for small `U(x)` the kernel of `Φ` is `T_x`, and `T_x` is a normal subgroup. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    -- (a) arbitrarily small neighbourhoods with the natural action
    (∀ (x : Obj) (V : Set Obj), IsOpen V → x ∈ V → ∃ R : NatRepB X x, R.U ⊆ V) ∧
    -- (b) the project's notions are the text's
    (∀ (x : Obj) (g : X.Isotropy x), X.ActsTrivially g ↔ ActsTriviallyB X g) ∧
    (∀ x : Obj, (X.trivialSubgroup x : Set (X.Isotropy x)) = TxB X x) ∧
    -- (c) `1_x` acts trivially
    (∀ x : Obj, ActsTriviallyB X (1 : X.Isotropy x)) ∧
    -- (d) on small `U(x)`, `ker Φ = T_x`
    (∀ (x : Obj) (V : Set Obj), IsOpen V → x ∈ V →
      ∃ R : NatRepB X x, R.U ⊆ V ∧
        ∀ g : X.Isotropy x, (∀ y ∈ R.U, R.Φ g y = y) ↔ g ∈ TxB X x) ∧
    -- (e) `T_x` is a normal subgroup of `G_x`
    (∀ x : Obj, ∃ N : Subgroup (X.Isotropy x), N.Normal ∧ (N : Set (X.Isotropy x)) = TxB X x)

end RoundTrip.V7_37
