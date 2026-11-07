import Polyfold
/-! Blind formalization of V7_43 (the text's §7.3, Lemma 7.4, pp. 244–245; the 2017 book,
arXiv 1707.08941, Part II).

Text: every point `z ∈ |X|` has an open neighbourhood `V(z)` on which the topology is
metrizable, i.e. `|X|` is locally metrizable; in fact one can take `|U(x)|`, where `U(x)` is an
open neighbourhood equipped with the natural `G_x`-action.

Choices:
- Setting: an arbitrary ep-groupoid `X : EpGroupoid Obj Mor` (vocabulary, Definition 7.3),
  `Obj Mor : Type` (universe 0).  `|X|`: `X.OrbitSpace` with the quotient topology (the instance
  found, checked by `rfl` to be `coinduced X.π`); `π : X → |X|` is `X.π`.
- "the topology on `V` is metrizable": the subspace topology on `↥V` is Mathlib's
  `MetrizableSpace`.
- "an open neighbourhood `U(x)` equipped with the natural `G_x`-action": the open set `R.U` of a
  natural representation `R : X.NaturalRep x` (the vocabulary's data of Theorem 7.1: open
  connected `U ∋ x`, `Φ : G_x → Diff_sc(U)`, `Γ`, properties (1)–(3)), for `x` with `|x| = z`;
  `|U(x)| = π(U(x))`.
- "one can take `|U(x)|`": read as: for every such `U(x)` (every natural representation at any
  `x` over `z`), `|U(x)|` is an open neighbourhood of `z = |x|` with metrizable topology.  (The
  weaker reading "for some `U(x)`" would follow from Theorem 7.1's existence; I take the
  universal one as the text's "where `U(x)` is an open neighbourhood ...".)  Since the second
  conjunct alone would be vacuous at points without natural representations, B keeps the first
  claim (local metrizability) as its own conjunct.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_43
open Polyfold

/-- Lemma 7.4: every point of `|X|` has an open neighbourhood with metrizable subspace topology;
in fact `|U(x)| = π(U(x))` is one, for every natural representation `U(x)` of `G_x`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    (∀ z : X.OrbitSpace, ∃ V : Set X.OrbitSpace,
      IsOpen V ∧ z ∈ V ∧ TopologicalSpace.MetrizableSpace V) ∧
    (∀ (x : Obj) (R : X.NaturalRep x),
      IsOpen (X.π '' R.U) ∧ X.π x ∈ X.π '' R.U ∧
        TopologicalSpace.MetrizableSpace (X.π '' R.U))

end RoundTrip.V7_43
