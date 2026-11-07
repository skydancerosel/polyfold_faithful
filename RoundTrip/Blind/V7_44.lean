import Polyfold
/-! Blind formalization of V7_44 (the text's §7.3, Lemma 7.5, p. 245; the 2017 book,
arXiv 1707.08941, Part II).

Text: for the quotient topology on `|X|`, every point `z ∈ |X|` has a countable neighbourhood
basis of open sets `𝒱_z = {V_k(z) | k = 1, 2, 3, …}` with `z ∈ V_{k+1}(z) ⊂ V_k(z)`.

Choices:
- Setting: an arbitrary ep-groupoid `X : EpGroupoid Obj Mor` (vocabulary, Definition 7.3),
  `Obj Mor : Type` (universe 0).  `|X|`: `X.OrbitSpace` with the instance found, checked by `rfl`
  to be the quotient topology `coinduced X.π`.
- The sequence is indexed by `k : ℕ` starting at `0` instead of `1` (a shift of index).
- "neighbourhood basis consisting of open sets": every `V_k` is open and contains `z`, and every
  neighbourhood of `z` contains some `V_k` — Mathlib's `(𝓝 z).HasBasis (fun _ ↦ True) V`, plus
  `IsOpen (V k)`.
- `⊂` read as `⊆` (the text's inclusion sign); a strict inclusion would be impossible at isolated
  points of `|X|` (e.g. for a discrete object space), where the basis must reach `{z}`.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_44
open Polyfold

/-- Lemma 7.5: every point of `|X|` has a decreasing countable neighbourhood basis of open
sets. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (z : X.OrbitSpace),
    ∃ V : ℕ → Set X.OrbitSpace,
      (∀ k, IsOpen (V k)) ∧ (∀ k, z ∈ V (k + 1) ∧ V (k + 1) ⊆ V k) ∧
        (nhds z).HasBasis (fun _ ↦ True) V

end RoundTrip.V7_44
