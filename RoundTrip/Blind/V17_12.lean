import Polyfold
/-! Blind formalization of V17_12 (the text's Part II, §17.1, Proposition 17.1.11, p. 750 of the
Springer 2021 book; new in 2021).

Text: every `q ∈ O` has an open neighbourhood `U(q)` such that `t : s⁻¹(cl U(q)) → O'` is proper
for every `Ψ'`.

Choices:
- Setting: a GCT `C : GCT` (Definition 17.1.1; universe `0`) with a polyfold structure
  `S = (F, M) : C.PolyfoldConstruction` (Definition 17.1.8), a uniformizer `Ψ : G ⋉ O → C` of `F`
  (`S.Unif`: a local uniformizer lying in some `F(α)`), `q ∈ O`.
- `Ψ'` ranges over all uniformizers of `F` (`S.Unif`), with `O'` its M-polyfold.
- `M(Ψ, Ψ')` with its topology from `(F, M)`: the project's transition M-polyfold `S.Tr Ψ Ψ'`
  (`#print`ed: a synonym of the transition set `(↑Ψ).Trans ↑Ψ'` of tuples `(q, φ, q')`, carrying
  the topology `topM` of the structure); `s(q, φ, q') = q`, `t(q, φ, q') = q'` are
  `GroupoidStr.TransitionSet.src/tgt`.
- `cl U(q)` is the closure in `O`.  "proper": Mathlib's `IsProperMap` of the restriction
  `t : s⁻¹(cl U(q)) → O'` (continuous and universally closed; for the metrizable `O'` this is the
  same as continuous with compact preimages of compact sets).  This is also the form the project
  uses in the ep-groupoid axiom.
- I do not use the project's `HasPropernessProperty` (Definition 17.1.12), which by its docstring
  says the same thing.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_12
open Polyfold

/-- The source map `s : M(Ψ, Ψ') → O`. -/
def srcT {C : GCT} (S : C.PolyfoldConstruction) (Ψ Ψ' : S.Unif) : S.Tr Ψ Ψ' → Ψ.1.O :=
  fun a => GroupoidStr.TransitionSet.src (a : Ψ.1.Trans Ψ'.1)

/-- The target map `t : M(Ψ, Ψ') → O'`. -/
def tgtT {C : GCT} (S : C.PolyfoldConstruction) (Ψ Ψ' : S.Unif) : S.Tr Ψ Ψ' → Ψ'.1.O :=
  fun a => GroupoidStr.TransitionSet.tgt (a : Ψ.1.Trans Ψ'.1)

/-- Proposition 17.1.11: the properness property of the transition M-polyfolds. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (Ψ : S.Unif) (q : Ψ.1.O),
    ∃ U : Set Ψ.1.O, IsOpen U ∧ q ∈ U ∧
      ∀ Ψ' : S.Unif,
        IsProperMap ((srcT S Ψ Ψ' ⁻¹' closure U).domRestrict (tgtT S Ψ Ψ'))

end RoundTrip.V17_12
