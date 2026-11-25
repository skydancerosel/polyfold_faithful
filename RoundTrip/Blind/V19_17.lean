import Polyfold
/-! Blind formalization of V19_17 (the text's §19.3, Theorem 19.3.3, p. 873 of the Springer 2021
book; 2017: Theorem 19.2).

Text: `T_{Ψ,Ψ'}` is regular, Hausdorff and locally metrizable; `s`, `t` are local
homeomorphisms, `u`, `m` continuous, `ι` a homeomorphism, and `Ψ̄ : G × O → M(Ψ, Ψ)` a
homeomorphism.

Choices:
- Setting: universe `0`: a groupoidal category `C` with a basic construction `B = (F, 𝓕)`
  (`C.BasicConstruction`, Definition 19.1.7).  `T_{Ψ,Ψ'}` is, by Definition 19.3.2, the topology
  `T^F_{Ψ,Ψ'}` of any representative `F` of `𝓕`; I state the theorem for EVERY representative
  `F` (`⟦F⟧ = 𝓕`), with `M(Ψ, Ψ')` topologized as the vocabulary's `F.Tr Ψ Ψ'` (open sets
  `IsOpenTr`, the collection of Lemma 19.3.1).  I did not use the project's `B.M`, `B.rep`,
  `natTop`, `hatHomeomorph`, `invHomeomorph` or `sheet`.
- `Ψ, Ψ', Ψ''` range over the uniformizers occurring in `F` (`B.U.Unif`).
- "regular" = `RegularSpace`, "Hausdorff" = `T2Space`, "locally metrizable" = every point has an
  open neighbourhood which is metrizable in the subspace topology.
- Structure maps as in Proposition 19.3.5 (p. 746): `s`, `t`, `u`, `ι` = the vocabulary's
  `TransitionSet.src`, `tgt`, `unit`, `inv`; `m` = `F.mulMap` on `F.FibProd` (the fibred product
  `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` with the subspace topology of the product).  "local homeomorphism" =
  `IsLocalHomeomorph`; "homeomorphism" = a `≃ₜ` whose underlying map is the given map.
- `Ψ̄ : G × O → M(Ψ, Ψ)`, `(g, o) ↦ (o, Ψ(g, o), g ∗ o)` = the vocabulary's `Ψ.hat`
  (Lemma 17.1.9); `G` discrete (part of the uniformizer), `G × O` with the product topology.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_17
open Polyfold

/-- Theorem 19.3.3: the transition sets `M(Ψ, Ψ')` with `T_{Ψ,Ψ'}`. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (F : B.U.TransitionData),
    Quotient.mk (GroupoidalCategory.UniformizerConstruction.TransitionData.setoid B.U) F = B.𝓕 →
    -- regular, Hausdorff, locally metrizable
    (∀ Ψ Ψ' : B.U.Unif,
      RegularSpace (F.Tr Ψ Ψ') ∧ T2Space (F.Tr Ψ Ψ') ∧
      ∀ h : F.Tr Ψ Ψ', ∃ W : Set (F.Tr Ψ Ψ'), IsOpen W ∧ h ∈ W ∧
        TopologicalSpace.MetrizableSpace W) ∧
    -- `s` and `t` are local homeomorphisms
    (∀ Ψ Ψ' : B.U.Unif,
      IsLocalHomeomorph (fun h : F.Tr Ψ Ψ' =>
        (GroupoidStr.TransitionSet.src (h : (Ψ : C.Uniformizer).Trans Ψ') :
          (Ψ : C.Uniformizer).O)) ∧
      IsLocalHomeomorph (fun h : F.Tr Ψ Ψ' =>
        (GroupoidStr.TransitionSet.tgt (h : (Ψ : C.Uniformizer).Trans Ψ') :
          (Ψ' : C.Uniformizer).O))) ∧
    -- `u` is continuous
    (∀ Ψ : B.U.Unif,
      Continuous (fun o : (Ψ : C.Uniformizer).O =>
        F.toTr (GroupoidStr.TransitionSet.unit o : (Ψ : C.Uniformizer).Trans Ψ))) ∧
    -- `m` is continuous
    (∀ Ψ Ψ' Ψ'' : B.U.Unif, Continuous (F.mulMap Ψ Ψ' Ψ'')) ∧
    -- `ι` is a homeomorphism
    (∀ Ψ Ψ' : B.U.Unif, ∃ e : F.Tr Ψ Ψ' ≃ₜ F.Tr Ψ' Ψ,
      ∀ h : (Ψ : C.Uniformizer).Trans Ψ',
        e (F.toTr h) = F.toTr (GroupoidStr.TransitionSet.inv h)) ∧
    -- `Ψ̄ : G × O → M(Ψ, Ψ)` is a homeomorphism
    (∀ Ψ : B.U.Unif, ∃ e : (Ψ : C.Uniformizer).G × (Ψ : C.Uniformizer).O ≃ₜ F.Tr Ψ Ψ,
      ∀ p, e p = F.toTr ((Ψ : C.Uniformizer).hat p))

end RoundTrip.V19_17
