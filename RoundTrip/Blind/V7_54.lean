import Polyfold
/-! Blind formalization of V7_54 (the 2017 book's Part II, §7.4, Proposition 7.12, p. 249, proof
pp. 249–250).

Text: if `(X, 𝐗)` is an ep-groupoid with paracompact orbit space, then so is `(X¹, 𝐗¹)`.

Choices:
- Setting as in `RoundTrip/Blind/V7_49.lean`: `Obj Mor : Type` (universe 0) with the instances
  of the project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's ep-groupoid,
  Definition 7.3, fields read with `#print`).
- "with paracompact orbit space" (Definition 7.15): the project's `HasParacompactOrbitSpace`
  (checked with `#print`: `ParacompactSpace X.OrbitSpace`, Mathlib's paracompactness of the
  quotient `|X|`, no Hausdorff condition; see `RoundTrip/Blind/V7_53.lean`).
- `(X¹, 𝐗¹)`: my `IsLiftB`, copied from `RoundTrip/Blind/V7_52.lean` — an ep-groupoid on the
  levels `X_1`, `𝐗_1` (the project's `Level 1` types with the level topologies), with the
  M-polyfold structures `X¹`, `𝐗¹` (atlases equivalent to the project's `shift`) and the
  structure maps of `X` restricted to level 1 (`m` on composable pairs).
- B: there is such an ep-groupoid `Y` and its orbit space `|X¹|` is paracompact.  The orbit space
  of any `Y` with `IsLiftB X Y` is the same (its relation "isomorphic" only involves `s, t`, which
  are fixed by `IsLiftB`, and the topology of `X_1`), so the existential loses nothing.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_54
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `Y` is the ep-groupoid `X¹ = (X¹, 𝐗¹)`: the M-polyfolds `X¹`, `𝐗¹` (up to equivalence of
atlases) and the structure maps of `X` restricted to level `1` (as in V7_52). -/
def IsLiftB (X : EpGroupoid Obj Mor) (Y : EpGroupoid (X.PObj.Level 1) (X.PMor.Level 1)) :
    Prop :=
  Y.PObj.atlas.Equiv X.PObj.shift.atlas ∧
  Y.PMor.atlas.Equiv X.PMor.shift.atlas ∧
  (∀ φ : X.PMor.Level 1, X.PObj.levelVal 1 (Y.src φ) = X.src (X.PMor.levelVal 1 φ)) ∧
  (∀ φ : X.PMor.Level 1, X.PObj.levelVal 1 (Y.tgt φ) = X.tgt (X.PMor.levelVal 1 φ)) ∧
  (∀ x : X.PObj.Level 1, X.PMor.levelVal 1 (Y.unit x) = X.unit (X.PObj.levelVal 1 x)) ∧
  (∀ φ : X.PMor.Level 1, X.PMor.levelVal 1 (Y.inv φ) = X.inv (X.PMor.levelVal 1 φ)) ∧
  (∀ φ ψ : X.PMor.Level 1, Y.src φ = Y.tgt ψ →
    X.PMor.levelVal 1 (Y.comp φ ψ) = X.comp (X.PMor.levelVal 1 φ) (X.PMor.levelVal 1 ψ))

end

/-- Proposition 7.12: `X¹` is an ep-groupoid with paracompact orbit space if `X` is. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor), X.HasParacompactOrbitSpace →
    ∃ Y : EpGroupoid (X.PObj.Level 1) (X.PMor.Level 1),
      IsLiftB X Y ∧ Y.HasParacompactOrbitSpace

end RoundTrip.V7_54
