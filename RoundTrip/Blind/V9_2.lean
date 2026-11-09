import Polyfold
/-! Blind formalization of V9_2 (the Springer 2021 book, Part II, §9.1, Remark 9.1.1, p. 402
[2017: Remark 9.1, p. 291] and the last paragraph of Definition 9.1.2, p. 402): the dimension of a
submanifold, `n`-dimensional `Θ`.

Text: the dimension of `T_mM` is locally constant in `m ∈ M`, the local dimension of `M`.  `Θ` is
`n`-dimensional if at every point of its support the manifolds of a local branching structure can
be taken `n`-dimensional (2017: are `n`-dimensional); by a footnote (new in 2021) an
`n`-dimensional `Θ` is not `m`-dimensional for `m ≠ n`; `Θ` is locally equidimensional if small
structures have sheets of one dimension.

Choices:
- Setting: `Obj Mor : Type` (universe 0) and the project's `X : EpGroupoid Obj Mor`; for the
  remark, any M-polyfold `P : MPolyfold Z`, `Z : Type`.  Submanifolds: the project's
  `IsSmoothSubmanifold` (Part I, Definition 4.13: locally the image of an sc⁺-retraction) and its
  data `SubmanifoldData` (`#print`ed: open `V`, sc⁺-retraction `s` on `V`, `s(V) = M ∩ V`).
- `T_mM = Tr(m)(T_mX)` (2021 p. 409, Part I Remark 4.2.2): my `TyMB`, the images under the
  project's tangent map `d.tmap = Ts` of the sc⁺-retraction of some data `d` at `m` of the vectors
  over `m` (union over the data; by Part I the choice does not matter).  The project's `T_mX` has
  no linear structure, so "the dimension of `T_mM`" is read in a chart (my `HasDimB`): for a chart
  `φ` of the structure around `m`, the second components `h` of `Tφ(α) = (φ(m), h)`, `α ∈ T_mM`
  (the project's `tangentChartMap`, compared with the text's `Tφ` in
  `RoundTrip/Blind/V2_19.lean`), form an `n`-dimensional linear subspace of `E₀`.  (Some chart;
  the linear structure of `T_mX` does not depend on the chart.)
- (a) "locally constant in `m ∈ M`": every `m ∈ M` has an open `W ∋ m` and an `n` with
  `dim T_{m'}M = n` for all `m' ∈ M ∩ W` (this includes that every `T_mM` has a dimension).
- (b) "`n`-dimensional" (2021 reading, "can be taken"): every `x ∈ supp Θ` has SOME local
  branching structure (my `IsLBSB`, copied from `RoundTrip/Blind/V9_1.lean`) all of whose `Mᵢ`
  are `n`-dimensional (`dim T_mMᵢ = n` for all `m ∈ Mᵢ`).  This is a definition: B says the
  project's `X.IsNDimensional Θ n` is it (for every `Θ : Obj → ℚ`; both sides make sense for any
  function).
- (c) the footnote: for a branched ep⁺-subgroupoid (my `IsBranchedB` of V9_1) that is `n`- and
  `m`-dimensional, `m = n`.  Literally this fails for `Θ = 0` (empty support: `Θ` is then
  `n`-dimensional for every `n`), so I add the hypothesis `supp Θ ≠ ∅`, which the footnote clearly
  presupposes.
- (d) "locally equidimensional" is a pure definition with no project counterpart in the
  vocabulary; I record my reading as `IsLocallyEquidimB` (every point of the support has a local
  branching structure whose sheets all have one dimension `n`, `n` depending on the point; "small
  structures" read as "some structure on a small `U(x)`") but B makes no claim about it.
- Nothing else looks false to me.
-/
namespace RoundTrip.V9_2
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `supp(Θ) = {x | Θ(x) > 0}`. -/
def suppB (Θ : Obj → ℚ) : Set Obj := {x | 0 < Θ x}

/-- The inclusion `A → U` is proper: preimages of compact subsets of `U` are compact. -/
def IsProperInclB (A U : Set Obj) : Prop :=
  ∀ K : Set Obj, K ⊆ U → IsCompact K → IsCompact (K ∩ A)

open Classical in
/-- **Definition 9.1.2 (2)–(4)**: `(U, (Mᵢ)_{i ∈ ι}, (σᵢ)_{i ∈ ι})` is a local branching structure
of `Θ` at `x`. -/
def IsLBSB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (x : Obj) {ι : Type} [Fintype ι]
    (U : Set Obj) (M : ι → Set Obj) (σ : ι → ℚ) : Prop :=
  IsOpen U ∧ x ∈ U ∧
  (∀ i, M i ⊆ U ∧ X.PObj.IsSmoothSubmanifold (M i) ∧ x ∈ M i ∧ IsProperInclB (M i) U) ∧
  (∀ i, 0 < σ i) ∧
  ∀ y ∈ U, Θ y = ∑ i with y ∈ M i, σ i

/-- **Definition 9.1.2**: `Θ` is a branched ep⁺-subgroupoid of `X`. -/
def IsBranchedB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) : Prop :=
  -- `Θ : X → ℚ⁺` is a functor
  (∀ x, 0 ≤ Θ x) ∧ (∀ φ : Mor, Θ (X.src φ) = Θ (X.tgt φ)) ∧
  -- (1)
  suppB Θ ⊆ X.PObj.smoothSet ∧ ParacompactSpace ↥(X.π '' suppB Θ) ∧
  -- (2)–(4) at every point of the support
  ∀ x ∈ suppB Θ, ∃ (ι : Type) (_ : Fintype ι) (U : Set Obj) (M : ι → Set Obj) (σ : ι → ℚ),
    IsLBSB X Θ x U M σ

end

section
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]

/-- `T_yX`: the tangent vectors over `y` (the fibre of `p : TX → X¹` over `y ∈ X₁`). -/
def TxXB (P : MPolyfold Z) (y : Z) : Set P.TangentSpace :=
  {α | P.levelVal 1 (P.tangentProj α) = y}

/-- `T_yM = Tr(y)(T_yX)` for the sc⁺-retractions `r` of the data of Definition 4.13 of `M` at
`y` (the union over all such data; by Part I it does not depend on the data). -/
def TyMB (P : MPolyfold Z) (M : Set Z) (y : Z) : Set P.TangentSpace :=
  {α | ∃ d : P.SubmanifoldData M, y ∈ d.V ∧ ∃ β ∈ TxXB P y, d.tmap β = α}

/-- The chart image `{h | (φ(y), h) = Tφ(α), α ∈ S}` of a set `S` of tangent vectors. -/
def chartImgB {P : MPolyfold Z} {φ : MChart Z} (hφ : P.IsChart φ) (S : Set P.TangentSpace) :
    Set (φ.model.E.lvl 0) :=
  (fun α => (MPolyfold.tangentChartMap hφ α).2) '' S

/-- Remark 9.1.1: `M` has (local) dimension `n` at `y`: in a chart `φ` around `y`, `T_yM` is an
`n`-dimensional linear subspace of `E`. -/
def HasDimB (P : MPolyfold Z) (M : Set Z) (y : Z) (n : ℕ) : Prop :=
  ∃ (φ : MChart Z) (hφ : P.IsChart φ), y ∈ φ.source ∧
    ∃ S : Submodule ℝ (φ.model.E.lvl 0), FiniteDimensional ℝ S ∧
      chartImgB hφ (TyMB P M y) = (S : Set (φ.model.E.lvl 0)) ∧ Module.finrank ℝ S = n

end

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `Θ` is `n`-dimensional: at every point of the support there is a local branching structure
whose submanifolds are all `n`-dimensional. -/
def IsNDimB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (n : ℕ) : Prop :=
  ∀ x ∈ suppB Θ, ∃ (ι : Type) (_ : Fintype ι) (U : Set Obj) (M : ι → Set Obj) (σ : ι → ℚ),
    IsLBSB X Θ x U M σ ∧ ∀ i, ∀ m ∈ M i, HasDimB X.PObj (M i) m n

/-- (Recorded reading, not used in `B`.)  `Θ` is locally equidimensional: every point of the
support has a local branching structure whose submanifolds all have the same dimension. -/
def IsLocallyEquidimB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) : Prop :=
  ∀ x ∈ suppB Θ, ∃ (n : ℕ) (ι : Type) (_ : Fintype ι) (U : Set Obj) (M : ι → Set Obj)
    (σ : ι → ℚ), IsLBSB X Θ x U M σ ∧ ∀ i, ∀ m ∈ M i, HasDimB X.PObj (M i) m n

end

/-- Remark 9.1.1 and the end of Definition 9.1.2: (a) the dimension of `T_mM` is locally
constant on a submanifold `M`; (b) the project's `n`-dimensional `Θ` is the text's; (c) a
nonzero `n`-dimensional `Θ` is not `m`-dimensional for `m ≠ n`. -/
def B : Prop :=
  -- (a)
  (∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (M : Set Z), P.IsSmoothSubmanifold M → ∀ m ∈ M,
      ∃ (n : ℕ) (W : Set Z), IsOpen W ∧ m ∈ W ∧ ∀ m' ∈ M ∩ W, HasDimB P M m' n) ∧
  -- (b)
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (n : ℕ),
      X.IsNDimensional Θ n ↔ IsNDimB X Θ n) ∧
  -- (c)
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (n m : ℕ),
      IsBranchedB X Θ → (suppB Θ).Nonempty → IsNDimB X Θ n → IsNDimB X Θ m → m = n)

end RoundTrip.V9_2
