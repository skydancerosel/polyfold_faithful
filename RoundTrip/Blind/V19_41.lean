import Polyfold
/-! Blind formalization of V19_41 (the text's §19.5, Proposition 19.5.11, p. 890 of the Springer
2021 book; new in the 2021 edition).

Text: (ZHOU) of the basic construction implies (SLUC) and (SLR).

Choices:
- Setting: universe `0`: a groupoidal category `C : GroupoidalCategory.{0}` with a basic
  construction `B = (F, 𝓕)` (`C.BasicConstruction`, Definition 19.1.7).
- Hypothesis added: `B.U.HasClassUniformizers` (every class of `|S|` contains an object `α` with
  `F(α) ≠ ∅`).  The definitions of (LUC)/(LR) for a basic construction (Definitions 19.5.8,
  19.5.10) ask, for each class `z`, for an object `α_z ∈ z` with a uniformizer `Ψ ∈ F(α_z)` at
  `α_z`; I read the section as presupposing such objects exist (the setting of §19.2 onwards).
  No metrizability of `T` is assumed (the quoted statement has none).
- (ZHOU): the vocabulary's `B.IsZhou` (Definition 19.5.6, checked by `#print`); (SLUC): `B.IsSLUC`
  ((LUC) of every level `(Fⁱ, 𝓕ⁱ)`, `IsLUCLevel i`, Definition 19.5.8); (SLR): `B.IsSLR` ((LR) of
  every level, `IsLRLevel i`: Chapter 7's (LR) of `(G ⋉ O)ⁱ` at the point over `ō`, Definition
  19.5.10).  All three are properties of the basic construction, as the text says.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_41
open Polyfold

/-- Proposition 19.5.11: (ZHOU) of a basic construction implies (SLUC) and (SLR). -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction),
    B.U.HasClassUniformizers → B.IsZhou → B.IsSLUC ∧ B.IsSLR

end RoundTrip.V19_41
