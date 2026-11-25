import Polyfold
/-! Blind formalization of V19_19 (the text's §19.3, Proposition 19.3.5, p. 875 of the Springer
2021 book; 2017: Proposition 19.2).

Text: `s` and `t` are local homeomorphisms, `u` and `m` are continuous and `ι` is a
homeomorphism.

Choices:
- Setting: universe `0`: a groupoidal category `C`, a uniformizer construction `F` and arbitrary
  transition data `F` for it (vocabulary: `C.UniformizerConstruction`, `U.TransitionData`); the
  transition sets `M(Ψ, Ψ')` carry the topology `T^F_{Ψ,Ψ'}` of Lemma 19.3.1 (the vocabulary's
  `F.Tr Ψ Ψ'`, open sets `IsOpenTr`).  Stating it for all transition data covers `T_{Ψ,Ψ'}` of
  every transition construction (Definition 19.3.2).  `Ψ, Ψ', Ψ''` range over the uniformizers
  occurring in `F` (`U.Unif`); `O`, `O'` carry the topologies of their M-polyfold structures.
- The structure maps (Definition 17.1.5 / p. 746): `s(o, φ, o') = o : M(Ψ, Ψ') → O`,
  `t(o, φ, o') = o' : M(Ψ, Ψ') → O'`, `u(o) = (o, 1, o) : O → M(Ψ, Ψ)`,
  `ι(o, φ, o') = (o', φ⁻¹, o) : M(Ψ, Ψ') → M(Ψ', Ψ)` (the vocabulary's `TransitionSet.src`,
  `tgt`, `unit`, `inv`), and `m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')`,
  `m((o', φ', o''), (o, φ, o')) = (o, φ' ∘ φ, o'')` on the fibred product with the subspace
  topology of the product (the vocabulary's `F.FibProd` and `F.mulMap`).
- "local homeomorphism" = Mathlib's `IsLocalHomeomorph`; "`ι` is a homeomorphism" = there is a
  homeomorphism `M(Ψ, Ψ') ≃ₜ M(Ψ', Ψ)` whose underlying map is `ι`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_19
open Polyfold

/-- Proposition 19.3.5: the structure maps of the transition sets. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (U : C.UniformizerConstruction) (F : U.TransitionData),
    -- `s` and `t` are local homeomorphisms
    (∀ Ψ Ψ' : U.Unif,
      IsLocalHomeomorph (fun h : F.Tr Ψ Ψ' =>
        (GroupoidStr.TransitionSet.src (h : (Ψ : C.Uniformizer).Trans Ψ') :
          (Ψ : C.Uniformizer).O)) ∧
      IsLocalHomeomorph (fun h : F.Tr Ψ Ψ' =>
        (GroupoidStr.TransitionSet.tgt (h : (Ψ : C.Uniformizer).Trans Ψ') :
          (Ψ' : C.Uniformizer).O))) ∧
    -- `u` is continuous
    (∀ Ψ : U.Unif,
      Continuous (fun o : (Ψ : C.Uniformizer).O =>
        F.toTr (GroupoidStr.TransitionSet.unit o : (Ψ : C.Uniformizer).Trans Ψ))) ∧
    -- `m` is continuous
    (∀ Ψ Ψ' Ψ'' : U.Unif, Continuous (F.mulMap Ψ Ψ' Ψ'')) ∧
    -- `ι` is a homeomorphism
    (∀ Ψ Ψ' : U.Unif, ∃ e : F.Tr Ψ Ψ' ≃ₜ F.Tr Ψ' Ψ,
      ∀ h : (Ψ : C.Uniformizer).Trans Ψ',
        e (F.toTr h) = F.toTr (GroupoidStr.TransitionSet.inv h))

end RoundTrip.V19_19
