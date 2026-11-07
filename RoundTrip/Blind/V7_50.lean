import Polyfold
/-! Blind formalization of V7_50 (the 2017 book's Part I, Lemma 2.7 (Michael, [55] Lemma 1) and
Proposition 2.17, p. 51; used for Corollary 7.2, p. 247, and recalled on p. 249).

Text: (Lemma 2.7) a regular Hausdorff space `X` is paracompact iff every open cover of `X` has a
locally finite refinement consisting of closed sets.  (Proposition 2.17) if `Y` is regular
Hausdorff and `(Y_i)_{i ∈ I}` is a locally finite family of closed subspaces with
`Y = ⋃ Y_i`, every `Y_i` paracompact, then `Y` is paracompact.

Choices:
- Pure point-set topology; no project definition is used.  Setting: `T : Type` (universe 0, as in
  the other blind files) with a topology; "regular Hausdorff": Mathlib's `[T2Space T]
  [RegularSpace T]`.
- "paracompact": Mathlib's `ParacompactSpace` — every open cover (indexed by a type in the same
  universe) has a locally finite open refinement covering the space; no Hausdorff condition, as
  the book's definition (p. 249: "a paracompact space is not required to be Hausdorff").  For a
  subspace `Y_i` it is `ParacompactSpace ↥(Y i)` with the subspace topology.
- Covers are indexed families `U : ι → Set T` (`ι : Type`), open and with union `univ`.
  "A locally finite refinement consisting of closed sets": a family `F : κ → Set T` (`κ : Type`)
  of closed sets, covering `T`, locally finite (Mathlib's `LocallyFinite`: every point has a
  neighbourhood meeting `F k` for only finitely many `k`), with every `F k` contained in some
  `U i`.
- Proposition 2.17: the family is indexed by `ι : Type`, closed, locally finite, with union
  `univ`.
- Not included as a separate conjunct: the use in the proof of Corollary 7.2 ("a finite union of
  closed paracompact sets is paracompact"); it is the case of a finite family of Proposition 2.17
  applied inside the (regular Hausdorff) subspace that is the union.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_50

/-- Every open cover of `T` has a locally finite refinement by closed sets covering `T`. -/
def HasLocFinClosedRefinements (T : Type) [TopologicalSpace T] : Prop :=
  ∀ (ι : Type) (U : ι → Set T), (∀ i, IsOpen (U i)) → ⋃ i, U i = Set.univ →
    ∃ (κ : Type) (F : κ → Set T), (∀ k, IsClosed (F k)) ∧ ⋃ k, F k = Set.univ ∧
      LocallyFinite F ∧ ∀ k, ∃ i, F k ⊆ U i

/-- Lemma 2.7 (Michael) and Proposition 2.17 (locally finite unions of closed paracompact
subspaces of a regular Hausdorff space are paracompact). -/
def B : Prop :=
  (∀ (T : Type) [TopologicalSpace T] [T2Space T] [RegularSpace T],
    ParacompactSpace T ↔ HasLocFinClosedRefinements T) ∧
  (∀ (T : Type) [TopologicalSpace T] [T2Space T] [RegularSpace T] (ι : Type) (Y : ι → Set T),
    (∀ i, IsClosed (Y i)) → LocallyFinite Y → ⋃ i, Y i = Set.univ →
    (∀ i, ParacompactSpace ↥(Y i)) → ParacompactSpace T)

end RoundTrip.V7_50
