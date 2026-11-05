import Polyfold
/-! Blind formalization of V3_24 (the text's §3.2, Theorem 3.27, p. 81). Choices:
- Setting: `X : Type` (universe 0, as asked) with an M-polyfold structure `PX`, `M : Set X`,
  `n : ℕ`.  Hypotheses as quoted: `X` tame (`MPolyfold.IsTame`, Definition 2.37) and `M` has the
  `n`-dimensional tangent germ property.
- "tangent germ property" (Definition 3.25): I used the project's `HasTangentGermProperty` and its
  data `TangentGermChart M x n` (I have no other source for Definition 3.25).  Two features of that
  reading, recorded as the project documents them: the good complement `Y` is required closed
  (the text's sc-complement is closed, so this is no extra hypothesis), and "`δ` an sc^∞-germ" is
  read with neighbourhoods depending on the level and on `k` (`IsScInftyGermAt`); `N ∩ C`'s good
  position uses `IsInGoodPosition` (an algebraic good complement).  These choices make the data of
  Definition 3.25 more plentiful, hence claim (2) below (for *all* data) stronger.
- (1) "a sub-M-polyfold whose induced structure is tame and sc-smoothly equivalent to a smooth
  manifold with boundary with corners": `PX.IsSubMPolyfold M` (Definition 2.20), the induced
  structure `subPolyfold` (Proposition 2.21; it needs `ParacompactSpace M`, which is asserted
  existentially as part of the claim), `MPolyfold.IsTame` of it, and `MPolyfold.HasCornerStructure`
  of it (Definition 4.1: an equivalent atlas of corner charts on relatively open subsets of partial
  quadrants of finite-dimensional spaces with the constant sc-structure).
- (2) "with the data of Definition 3.25, `y ↦ π ∘ φ(y)` is a smooth chart of `M` around `x`": for
  every `x ∈ M` and *every* data `d` at `x`, with `π = d.π : E → N` the projection along `Y`, there is
  a chart of the induced M-polyfold structure of `M` (`IsChart`, i.e. compatible with its atlas)
  whose domain contains `x`, whose map is `y ↦ π(φ(y))` on its domain, and whose local model is a
  relatively open subset `V'` of the partial quadrant `N ∩ C` of `N` with the constant sc-structure
  (`LocalModel.ofRelOpen`), i.e. a corner chart; `IsSmoothChartAt` is defined here.  The chart is
  only required on some open neighbourhood of `x` in `M` ("around `x`").
- Doubt: Definition 3.25 (as read above) gives `δ` smooth only in a germ sense with `k`-dependent
  neighbourhoods, which may be too weak for the chart in (2) to be smooth on a neighbourhood; I
  formalize the claim literally anyway.
-/
namespace RoundTrip.V3_24
open Polyfold

/-- `κ : Z → V` is, on some open neighbourhood of `z`, a chart of the M-polyfold `QZ` modelled on a
relatively open subset of the partial quadrant `Cv` of the finite-dimensional space `V` (constant
sc-structure, identity retraction): a smooth corner chart of `Z` around `z` with map `κ`. -/
def IsSmoothChartAt {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (QZ : MPolyfold Z) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Cv : Set V) (z : Z) (κ : Z → V) : Prop :=
  ∃ (Vn : Set V) (hV : IsRelOpenInQuadrant (ScBanach.const V) Cv Vn) (e : PartialEquiv Z V)
    (h1 : IsOpen e.source) (h2 : e.target = Vn) (h3 : ContinuousOn e e.source)
    (h4 : ContinuousOn e.symm Vn),
    z ∈ e.source ∧ (∀ y ∈ e.source, e y = κ y) ∧
      QZ.IsChart ⟨LocalModel.ofRelOpen hV, e, h1, h2, h3, h4⟩

/-- Theorem 3.27: a subset with the `n`-dimensional tangent germ property of a tame M-polyfold is a
sub-M-polyfold, tame and with a compatible manifold-with-corners structure, and `π ∘ φ` (from any
data of Definition 3.25) is a smooth chart of it. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (M : Set X) (n : ℕ),
    PX.IsTame → PX.HasTangentGermProperty M n →
    ∃ (hM : PX.IsSubMPolyfold M) (_ : ParacompactSpace M),
      (PX.subPolyfold hM).IsTame ∧ (PX.subPolyfold hM).HasCornerStructure ∧
      ∀ (x : X) (hx : x ∈ M) (d : PX.TangentGermChart M x n),
        letI := d.finiteDimensional
        IsSmoothChartAt (PX.subPolyfold hM) (Subtype.val ⁻¹' d.φ.model.C : Set d.N) ⟨x, hx⟩
          (fun y : M => d.π (d.φ.toPartialEquiv y))

end RoundTrip.V3_24
