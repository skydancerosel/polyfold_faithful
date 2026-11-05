import Polyfold
/-! Blind formalization of V2_12 (the text's §2.2, Definition 2.13, p. 24).

Text: an M-polyfold is a Hausdorff paracompact topological space with an equivalence class of
sc-smooth atlases.

Choices:
- This item is a definition.  Setting: a topological space `X : Type` (spaces put in `Type`; the
  project's `MPolyfold` is universe-polymorphic, this is the instance `u = 0`).  "Hausdorff" is
  `T2Space X`, "paracompact" is Mathlib's `ParacompactSpace X`.
- Atlases and their equivalence (Definition 2.12) are the project's `MAtlas X` and `MAtlas.Equiv`
  (checked with `#print`: pairwise compatible `MChart`s covering `X`; `A ~ A'` iff some atlas has
  chart set `A.charts ∪ A'.charts`), characterized as the text's notions in my
  `RoundTrip/Blind/V2_11.lean` (charts in `RoundTrip/Blind/V2_10.lean`).
- "Equivalence class" presupposes that atlas equivalence is an equivalence relation; B asserts
  this as its first conjunct (a), for every topological space.  This is a presupposition of the
  definition, not a sentence of the text; reflexivity and symmetry are immediate, transitivity
  uses locality of sc-smoothness and the chain rule.  `classB A = {A' | A ~ A'}` is the class of
  `A`.  An M-polyfold structure on `X` (`IsMPolyfoldStructureB X 𝒜`): `X` is Hausdorff and
  paracompact and `𝒜` is the class of some atlas.
- B (b): the project's `MPolyfold X` (checked with `#print`: requires `[T2Space X]`
  `[ParacompactSpace X]`, and has a single field `atlas : MAtlas X`, representing its class) gives
  exactly these structures: `𝒜` is an M-polyfold structure iff `X` is Hausdorff, paracompact and
  `𝒜` is the class of `P.atlas` for some `P : MPolyfold X`.
- B (c), my reading of how the class enters: the charts of the M-polyfold are the charts of the
  atlases in its class (the maximal atlas), and the project's `P.IsChart` (checked: compatible with
  every chart of `P.atlas`) is exactly this.  Hence everything the project defines through
  `IsChart` depends only on the class.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_12
open Polyfold

/-- The equivalence class `{A' | A ~ A'}` of the atlas `A` (Definition 2.12). -/
def classB {X : Type} [TopologicalSpace X] (A : MAtlas X) : Set (MAtlas X) :=
  {A' | A.Equiv A'}

/-- **Definition 2.13**: an M-polyfold structure on `X`: `X` is Hausdorff and paracompact and
`𝒜` is an equivalence class of sc-smooth atlases. -/
def IsMPolyfoldStructureB (X : Type) [TopologicalSpace X] (𝒜 : Set (MAtlas X)) : Prop :=
  T2Space X ∧ ParacompactSpace X ∧ ∃ A : MAtlas X, 𝒜 = classB A

/-- Definition 2.13: atlas equivalence is an equivalence relation; the project's M-polyfolds,
up to the class of their atlas, are the text's; and their charts are those of the class. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X],
    -- (a) presupposed by "equivalence class"
    Equivalence (@MAtlas.Equiv X _) ∧
    -- (b) M-polyfold structures = classes of the atlases of project M-polyfolds
    (∀ 𝒜 : Set (MAtlas X), IsMPolyfoldStructureB X 𝒜 ↔
      ∃ (_ : T2Space X) (_ : ParacompactSpace X) (P : MPolyfold X), 𝒜 = classB P.atlas) ∧
    -- (c) the charts of the M-polyfold are the charts of the atlases in its class
    (∀ [T2Space X] [ParacompactSpace X] (P : MPolyfold X) (φ : MChart X),
      P.IsChart φ ↔ ∃ A ∈ classB P.atlas, φ ∈ A.charts)

end RoundTrip.V2_12
