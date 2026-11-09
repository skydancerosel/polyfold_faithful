import Polyfold
/-! Blind formalization of V9_25 (the text's Part II, §9.2, Remark 9.2.14, p. 419 of the Springer
2021 book; 2017: Remark 9.5, p. 307): for a submanifold `M` of `X`, `x ∈ ∂M` iff `x ∈ ∂X` and
`T_xM` is not contained in `T^R_xX`.

Choices:
- Setting: as in `RoundTrip/Blind/V9_24.lean`: an M-polyfold `P : MPolyfold Z`, `Z : Type`
  (universe 0), Hausdorff and paracompact (the object M-polyfold of the ep-groupoid of §9.2;
  every M-polyfold is one, via the project's `EpGroupoid.trivial`); no tameness hypothesis.
- "submanifold": a smooth finite-dimensional submanifold (project's `IsSmoothSubmanifold`).
  The point `x` ranges over `M` (the text's `T_xM` presupposes `x ∈ M`; I add `x ∈ M` as a
  hypothesis).  The 2017 wording ("the reduced part of `C_xX`") is not used; this is the 2021
  statement.
- `∂M`: the project's `MPolyfold.submanifoldBoundary P M`, the points `y ∈ M` with `d_M(y) ≥ 1`
  for the induced structure (`#print`ed: via `subDegIndex`).  `∂X`: `MPolyfold.boundary`.
- `T_xM ⊆ T^R_xX`: the project's `MPolyfold.IsTangentReducedAt P M x` (chart form; see the header
  of `RoundTrip/Blind/V9_24.lean`).
- Nothing looks false to me (unlike the literal Lemma 9.2.13, the conjunct `x ∈ ∂X` is on the
  right side here).
-/
namespace RoundTrip.V9_25
open Polyfold

/-- **Remark 9.2.14**: for `x ∈ M`, `x ∈ ∂M` iff `x ∈ ∂X` and `T_xM ⊄ T^R_xX`. -/
def B : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (M : Set Z) (x : Z), P.IsSmoothSubmanifold M → x ∈ M →
      (x ∈ P.submanifoldBoundary M ↔ (x ∈ P.boundary ∧ ¬ P.IsTangentReducedAt M x))

end RoundTrip.V9_25
