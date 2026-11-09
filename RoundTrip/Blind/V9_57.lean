import Polyfold
/-! Blind formalization of V9_57 (the Springer 2021 book, Part II, §9.5, Proposition 9.5.13,
p. 446; new in the 2021 edition): the normalizing factors.

Text: (1) for effective `X` the branched integral and the effective branched integral agree;
(2) under (LUC) the effective branched integral on `X` is the branched integral on the reduced
ep-groupoid `X_R`.  Proof: `T_x = {1}`, so the normalizing factors agree.

Choices:
- The item is "the normalizing factors": the vocabulary has no sc-differential forms and no
  branched integrals, so the integrals themselves are not formalized.  The two integrals are
  built from the same local sums `∑ᵢ σᵢ ∫_{Kᵢ} ω` and differ only by their normalizing factors
  `1/♯G_x` (branched integral on `X`), `1/♯G^eff_x` (effective branched integral on `X`) and
  `1/♯G^R_x` (branched integral on `X_R`, `G^R_x` the isotropy group of `x` in `X_R`); the local
  branching structures and the forms on `X` and on `X_R` are the same objects (same object
  M-polyfold).  B states the equalities of these factors (as equalities of the orders, all of
  them positive, `1 ∈ G_x`), together with the proof's `T_x = {1}` in (1).
- Setting: `Obj Mor : Type` (universe 0), the project's ep-groupoid `X : EpGroupoid Obj Mor`.
  `G_x`: `X.Isotropy x`.  `T_x`: the project's `X.trivialSubgroup x` (elements acting trivially,
  compared in `RoundTrip/Blind/V7_37.lean`); `G^eff_x`: the project's `X.EffIsotropy x`
  (`G_x ⧸ normalClosure(T_x)`, compared with `G_x/T_x` in `RoundTrip/Blind/V7_41.lean`).
  "Effective": the project's `IsEffective` (Definition 7.11, `#print`ed: every `g ≠ 1_x` has
  morphisms `ψ` with `s ψ ≠ t ψ` in every neighbourhood).  (LUC): the project's `IsLUC`
  (2021 Definition 7.2.18, compared in `RoundTrip/Blind/V8_45.lean`).
- `X_R`: the project's `X.reducedEpGroupoid`, which needs `T2Space` and `ParacompactSpace`
  instances on `𝐗^R`; under (LUC) the text uses that `X_R` is an ep-groupoid, so these
  instances are taken as hypotheses (the presupposition "`X_R` is an ep-groupoid").
  `G^R_x`: `X.reducedEpGroupoid.Isotropy x`.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_57
open Polyfold

/-- **Proposition 9.5.13 (the normalizing factors)**: (1) for effective `X`, `T_x = {1}` and
`♯G^eff_x = ♯G_x`; (2) under (LUC), `♯G^R_x = ♯G^eff_x` for the isotropy group `G^R_x` of `x`
in `X_R`. -/
def B : Prop :=
  -- (1)
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor), X.IsEffective → ∀ x : Obj,
      X.trivialSubgroup x = ⊥ ∧ Nat.card (X.EffIsotropy x) = Nat.card (X.Isotropy x)) ∧
  -- (2)
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor), X.IsLUC →
    ∀ [T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor] (x : Obj),
      Nat.card (X.reducedEpGroupoid.Isotropy x) = Nat.card (X.EffIsotropy x))

end RoundTrip.V9_57
