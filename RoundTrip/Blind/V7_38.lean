import Polyfold
/-! Blind formalization of V7_38 (the 2017 book's Part II, §7.2, Definition 7.12, p. 241).

Text: the non-effective part is `𝐗^T = {φ ∈ T_x ⊆ G_x | x ∈ X} ⊆ 𝐗`.  Morphisms `φ, φ'` are
equivalent, `φ ∼ φ'`, if (1) `s(φ) = s(φ') = x` and (2) `φ = φ' ∘ g` for some `g ∈ T_x`.  The set
`𝐗^R` of reduced morphisms is the collection of all equivalence classes `[φ]`.

Choices:
- Setting: `Obj Mor : Type` (spaces in `Type`; the project's `EpGroupoid` is universe-polymorphic,
  this is `u = 0`), with their topologies, Hausdorff and paracompact, `X : EpGroupoid Obj Mor`
  (the project's Definition 7.3, checked with `#print`; see `RoundTrip/Blind/V7_33.lean`).
- `G_x` is the project's `X.Isotropy x` (morphisms `g` with `s g = t g = x`); `φ' ∘ g` is the
  project's `X.comp φ' g` (`comp φ ψ = φ ∘ ψ`, first `ψ`; `φ'` and `g` are composable since
  `t g = x = s φ'`).
- `T_x` (p. 241, item V7_37) is my `TxB` as in `RoundTrip/Blind/V7_37.lean`: the `g ∈ G_x` with
  `Φ(g) = id` on `U` for some data `(U, Φ, Γ)` of Theorem 7.1 (`NatRepB`, `U` open and connected;
  connectedness is the text's presupposition, see `RoundTrip/Blind/V7_35.lean`; it does not change
  `T_x`, the component of `x` in `U` being again invariant and open).  I do not use the project's
  `trivialSet` in my definitions.
- `𝐗^T` (`XTB`): the morphisms `φ` equal to some `g ∈ T_x`, `x ∈ X`.
- `∼` (`RelB`): `s φ = s φ'` and `φ = φ' ∘ g` for some `g ∈ T_{s φ}`.
- "equivalent", "equivalence classes": the text presupposes that `∼` is an equivalence relation;
  B states it (`Equivalence (RelB X)`).
- This item is a definition.  B says: the project's `nonEffectivePart` is `XTB`; its
  `ReducedRel` is `RelB`; `RelB` is an equivalence relation; the project's `ReducedMor` with its
  projection `reducedπ` (only types and docstrings read before writing mine; `#print` shows a
  `Quot` of `ReducedRel`) is the set of `∼`-classes: `reducedπ` is onto and identifies exactly the
  equivalent morphisms.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_38
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

/-- **Definition 7.12**: the non-effective part `𝐗^T = {φ ∈ T_x | x ∈ X}`. -/
def XTB (X : EpGroupoid Obj Mor) : Set Mor :=
  {φ | ∃ (x : Obj) (g : X.Isotropy x), g ∈ TxB X x ∧ φ = g.val}

/-- **Definition 7.12**: `φ ∼ φ'`: `s φ = s φ' = x` and `φ = φ' ∘ g` for some `g ∈ T_x`. -/
def RelB (X : EpGroupoid Obj Mor) (φ φ' : Mor) : Prop :=
  X.src φ = X.src φ' ∧ ∃ g : X.Isotropy (X.src φ), g ∈ TxB X (X.src φ) ∧ φ = X.comp φ' g.val

end

/-- Definition 7.12: the project's `𝐗^T`, `∼` and `𝐗^R` are the text's, and `∼` is an
equivalence relation. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    X.nonEffectivePart = XTB X ∧
    (∀ φ φ' : Mor, X.ReducedRel φ φ' ↔ RelB X φ φ') ∧
    Equivalence (RelB X) ∧
    Function.Surjective X.reducedπ ∧
    (∀ φ φ' : Mor, X.reducedπ φ = X.reducedπ φ' ↔ RelB X φ φ')

end RoundTrip.V7_38
