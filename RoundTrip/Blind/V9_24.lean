import Polyfold
/-! Blind formalization of V9_24 (the text's Part II, §9.2, Lemma 9.2.13, p. 419 of the Springer
2021 book; 2017: Lemma 9.9, p. 307): for a submanifold `M` of `X` and `x ∈ M` the following are
equivalent: (1) `x ∈ ∂X` and `d_M(x) = 0`; (2) `T_xM ⊆ T^R_xX`.

Choices:
- Setting: an M-polyfold `P : MPolyfold Z` on `Z : Type` (universe 0), Hausdorff and
  paracompact.  In §9.2 `X` is the object M-polyfold of an ep-groupoid; the lemma only involves
  that M-polyfold, and every M-polyfold is the object space of an ep-groupoid (the project's
  `EpGroupoid.trivial`), so this is the text's generality.  No tameness hypothesis (none is
  stated).
- "submanifold": a smooth finite-dimensional submanifold (Definition 4.13 [2017: 4.4]), the
  project's `MPolyfold.IsSmoothSubmanifold`; `x ∈ M`.
- `∂X`: the project's `MPolyfold.boundary` (`d_X(x) ≥ 1`, Definition 2.25).
- `d_M(x) = 0`: the degeneracy index of `M` with its induced M-polyfold structure is `0` at `x`;
  written as `x ∉ ∂M`, with the project's `MPolyfold.submanifoldBoundary P M`
  (`= {y ∈ M | d_M(y) ≥ 1}` for a smooth submanifold `M`, via `subDegIndex`, `#print`ed), which
  for `x ∈ M` is exactly `¬ (d_M(x) ≥ 1)`.
- `T_xM ⊆ T^R_xX`: the project's `MPolyfold.IsTangentReducedAt P M x` (`#print`ed): for some
  data of Definition 4.13 at `x`, some chart `φ` at `x`, some presentation `T` of its partial
  quadrant and the level-1 lift `z` of `φ(x)`, the chart tangent space `T_z(φ(W ∩ M))` lies in the
  minimal subspace `E_z` (so in `T^R_zO = T_zO ∩ E_z`).  I did not define `T^R_xX` myself: Part I's
  `T_xX` has no linear structure in the project; I take this chart form as the text's notion
  (the project's docstring says it then holds in all such charts; not checked).
- DOES NOT HOLD AS I READ IT (formalized literally): (2) ⇒ (1) fails at interior points.  If
  `d_X(x) = 0` (e.g. `Z = ℝ`, `M = {0}`, `x = 0`), a chart with `φ(x)` in the interior of its
  quadrant has `E_z = E`, so (2) holds, while (1) fails since `x ∉ ∂X`.  Presumably the text has
  `x ∈ ∂X` as a standing hypothesis (then (1) is just `d_M(x) = 0`); with that hypothesis the
  equivalence is what I would expect to hold.
-/
namespace RoundTrip.V9_24
open Polyfold

/-- **Lemma 9.2.13** (literal): for a smooth finite-dimensional submanifold `M` and `x ∈ M`,
`x ∈ ∂X ∧ d_M(x) = 0` iff `T_xM ⊆ T^R_xX`. -/
def B : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (M : Set Z) (x : Z), P.IsSmoothSubmanifold M → x ∈ M →
      ((x ∈ P.boundary ∧ x ∉ P.submanifoldBoundary M) ↔ P.IsTangentReducedAt M x)

end RoundTrip.V9_24
