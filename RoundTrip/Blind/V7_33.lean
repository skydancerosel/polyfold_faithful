import Polyfold
/-! Blind formalization of V7_33 (the 2017 book's Part II, §7.2, Definition 7.11 and the
sentences after it, p. 239).

Text: `X` is effective if for every `x`, every `g ∈ G_x ∖ {1_x}` and every open neighbourhood
`𝐔(g) ⊆ 𝐗` there is `ψ ∈ 𝐔(g)` with `s(ψ) ≠ t(ψ)`; `x` is regular if `G_x = {1_x}`; if `s(φ)`
is regular then so is `t(φ)`; `X_reg = {x | G_x = {1_x}}`.

Choices:
- Setting: `Obj Mor : Type` (spaces in `Type`; the project's `EpGroupoid` is universe-polymorphic,
  this is `u = 0`) with their topologies, Hausdorff and paracompact, and `X : EpGroupoid Obj Mor`.
  The project's `EpGroupoid` (Definition 7.3, checked with `#print`: groupoid laws on composable
  pairs, M-polyfold structures `PObj`, `PMor`, `s`, `t` local sc-diffeomorphisms, `u`, `ι`
  sc-smooth, the properness condition, `m` sc-smooth on `𝐗 ₛ×ₜ 𝐗`) is my notion of ep-groupoid;
  it is not part of this item.
- `G_x` is the project's `X.Isotropy x` (checked: morphisms `g` with `s g = t g = x`).  I check
  by `rfl` that its group law is `(g * h).val = g ∘ h`, `1.val = 1_x = u(x)`, `g⁻¹.val = ι(g)`;
  but I state `g ≠ 1_x` and `G_x = {1_x}` on the underlying morphisms (`g.val ≠ X.unit x`, all
  `g.val = X.unit x`), so no group structure is used here.
- "open neighbourhood `𝐔(g)`": every open `W ⊆ Mor` with `g ∈ W`.
- This item is mostly a definition.  B says: the project's `IsEffective`, `IsRegular`,
  `regularSet` are my `IsEffectiveB`, `IsRegularB`, `XregB` (only their types and docstrings were
  read before writing mine), and the one claim of the text: `s(φ)` regular implies `t(φ)` regular,
  for every morphism `φ`.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_33
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Definition 7.11**: `X` is effective: for every `x`, every `g ∈ G_x ∖ {1_x}` and every open
neighbourhood `W` of `g` in `𝐗` there is `ψ ∈ W` with `s ψ ≠ t ψ`. -/
def IsEffectiveB (X : EpGroupoid Obj Mor) : Prop :=
  ∀ (x : Obj) (g : X.Isotropy x), g.val ≠ X.unit x →
    ∀ W : Set Mor, IsOpen W → g.val ∈ W → ∃ ψ ∈ W, X.src ψ ≠ X.tgt ψ

/-- **Definition 7.11**: `x` is regular: `G_x = {1_x}`. -/
def IsRegularB (X : EpGroupoid Obj Mor) (x : Obj) : Prop :=
  ∀ g : X.Isotropy x, g.val = X.unit x

/-- The regular part `X_reg = {x ∈ X | G_x = {1_x}}`. -/
def XregB (X : EpGroupoid Obj Mor) : Set Obj :=
  {x | IsRegularB X x}

end

/-- Definition 7.11: the project's effectiveness, regularity and regular part are the text's;
and the target of a morphism with regular source is regular. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    (X.IsEffective ↔ IsEffectiveB X) ∧
    (∀ x : Obj, X.IsRegular x ↔ IsRegularB X x) ∧
    X.regularSet = XregB X ∧
    (∀ φ : Mor, IsRegularB X (X.src φ) → IsRegularB X (X.tgt φ))

end RoundTrip.V7_33
