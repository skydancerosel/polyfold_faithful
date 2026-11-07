import Polyfold
/-! Blind formalization of V7_36 (the 2017 book's Part II, §7.2, Proposition 7.8, p. 240).

Text: if `X` is an effective ep-groupoid, then `X_reg = {x ∈ X | G_x = {1_x}}` is open and dense
in `X`.

Choices:
- Setting: `Obj Mor : Type` (spaces in `Type`; the project's `EpGroupoid` is universe-polymorphic,
  this is `u = 0`), with their topologies, Hausdorff and paracompact, `X : EpGroupoid Obj Mor`
  (the project's Definition 7.3, checked with `#print`; see `RoundTrip/Blind/V7_33.lean`).
- "effective" (Definition 7.11) is my `IsEffectiveB` and `X_reg` my `XregB`, both as in
  `RoundTrip/Blind/V7_33.lean` (which asserts that they agree with the project's `IsEffective`
  and `regularSet`): for every `x`, every `g ∈ G_x` with `g ≠ 1_x` (on the underlying morphisms)
  and every open `W ∋ g` of `𝐗` there is `ψ ∈ W` with `s ψ ≠ t ψ`.
- "open and dense in `X`": `IsOpen` and `Dense` in the object space `Obj`.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_36
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

/-- Proposition 7.8: the regular part of an effective ep-groupoid is open and dense. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    IsEffectiveB X → IsOpen (XregB X) ∧ Dense (XregB X)

end RoundTrip.V7_36
