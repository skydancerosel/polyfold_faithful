import Polyfold
/-! Blind formalization of V7_42 (the text's §7.3, Theorem 7.2, p. 244; the 2017 book,
arXiv 1707.08941, Part II).

Text: for an ep-groupoid `(X, 𝐗)` the orbit space `|X|` is a locally metrizable, regular,
Hausdorff topological space; if in addition `|X|` is paracompact, it is metrizable (by the
Nagata/Smirnov metrization theorem).

Choices:
- Setting: an arbitrary ep-groupoid `X : EpGroupoid Obj Mor` (vocabulary, Definition 7.3),
  `Obj Mor : Type` (universe 0).
- `|X|`: `X.OrbitSpace` (`Quotient` of `Obj` by `x ∼ y` iff there is a morphism `x → y`) with the
  instance Lean finds, which I checked by `rfl` (not kept here) to be the quotient topology
  `coinduced X.π`.
- "locally metrizable" (as in Lemma 7.4): every point has an open neighbourhood `V` whose
  subspace topology is metrizable (`LocallyMetrizable`, Mathlib's `MetrizableSpace` on `↥V`).
- "regular": the text's definition (paragraph before Lemma 7.7): for every nonempty closed `A`
  and `z ∉ A` there are open `U ∋ z`, `V ⊇ A` with `U ∩ V = ∅` (`IsRegularText`, defined
  literally; it is Mathlib's `RegularSpace`, without any T₁ condition).
- "Hausdorff": Mathlib's `T2Space`.  "paracompact": Mathlib's `ParacompactSpace` (every open cover
  has a locally finite open refinement); any Hausdorff requirement in the text's notion of
  paracompactness is already part of the conclusion.  "metrizable": Mathlib's `MetrizableSpace`.
- The reference to Nagata/Smirnov is the reason, not part of the claim.  B is the conjunction of
  the four claims.  Nothing looks false to me.
-/
namespace RoundTrip.V7_42
open Polyfold

/-- Locally metrizable: every point has an open neighbourhood whose subspace topology is
metrizable. -/
def LocallyMetrizable (Y : Type) [TopologicalSpace Y] : Prop :=
  ∀ y : Y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ TopologicalSpace.MetrizableSpace V

/-- The text's regularity (p. 246): a nonempty closed set and a point outside it have disjoint
open neighbourhoods. -/
def IsRegularText (Y : Type) [TopologicalSpace Y] : Prop :=
  ∀ A : Set Y, A.Nonempty → IsClosed A → ∀ z : Y, z ∉ A →
    ∃ U V : Set Y, IsOpen U ∧ IsOpen V ∧ z ∈ U ∧ A ⊆ V ∧ U ∩ V = ∅

/-- Theorem 7.2: `|X|` is locally metrizable, regular and Hausdorff, and metrizable when it is
paracompact. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    LocallyMetrizable X.OrbitSpace ∧ IsRegularText X.OrbitSpace ∧ T2Space X.OrbitSpace ∧
      (ParacompactSpace X.OrbitSpace → TopologicalSpace.MetrizableSpace X.OrbitSpace)

end RoundTrip.V7_42
