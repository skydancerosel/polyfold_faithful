import Polyfold
/-! Blind formalization of V13_8 (the Springer 2021 book, Part II, §13.1, Theorem 13.1.8,
p. 604; 2017: Theorem 13.2).

Text: if `X` has paracompact orbit space and `W(x) ∋ x` are open, there is a good system with
`U(x) ⊂ W(x)` for all `x`.

Choices:
- Setting: an arbitrary ep-groupoid `X : EpGroupoid Obj Mor` with `Obj Mor : Type` (universe 0,
  as in the other blind files; the topological instances are those the project's `EpGroupoid`
  requires).
- "paracompact orbit space": the project's `EpGroupoid.HasParacompactOrbitSpace` (`#print`ed:
  `ParacompactSpace X.OrbitSpace`, Definition 7.5.1).
- "`W(x) ∋ x` open": a family `W : Obj → Set Obj` with `W x` open and `x ∈ W x` for every
  object `x` (no invariance asked; the text asks none).
- "good system": the project's `EpGroupoid.GoodSystem` (`#print`ed: for every `x` an open
  `U(x) ∋ x` with the natural `G_x`-action (`NatNbhd`), `cl U(x)` proper, and the components of
  `𝒰(x, x')` sc-diffeomorphic under `s`, `t` onto open sets: Definition 13.1.2 (1)–(3));
  `U(x)` is `GoodSystem.U`.  `U(x) ⊂ W(x)` read as `⊆`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V13_8
open Polyfold

/-- Theorem 13.1.8: a good system inside any given family of open neighbourhoods. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    X.HasParacompactOrbitSpace →
    ∀ W : Obj → Set Obj, (∀ x, IsOpen (W x)) → (∀ x, x ∈ W x) →
      ∃ 𝒰 : X.GoodSystem, ∀ x, 𝒰.U x ⊆ W x

end RoundTrip.V13_8
