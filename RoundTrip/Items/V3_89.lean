import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_89

/-! Round trip for V3_89 (Theorem 3.58, the basic germ criterion).

`A` is the conjunction of the types of `Polyfold.theorem_3_7_1`,
`Polyfold.familyCompactness_derivFamOp`, `Polyfold.fredholmIndex_block`,
`Polyfold.surjective_of_fredholmIndex_block`, `Polyfold.lemma_3_7_2` and `Polyfold.lemma_3_7_3`.
`fredholmIndex_block` and `surjective_of_fredholmIndex_block` have four universe parameters
(`P Q X Y : Type*`), instantiated at `0`; the others live in `Type`.

Neither direction is proved.

`A → B` (not proved, believed to be glue plus standard sc-Fredholm facts): `theorem_3_7_1` is
stated in coordinates `E = P ⊕ X`, `C = C̃ ⊕ X`, `F = Q ⊕ Y` (`ScBanach.paramProd`), whereas `B`
has arbitrary sc-Banach spaces `E`, `F`, an sc-splitting `E = B ⊕ X` with `B ⊇ ker Df(0)`, and no
splitting of `F`.  To instantiate `A` one needs (a) an sc-isomorphism `E ≅ B ⊕ X` onto a
`paramProd` (with `X` given its induced sc-structure), (b) `C ∩ B` a partial quadrant of `B` (true:
the defining functionals of `C` vanish on `X` because `b + x ∈ C ↔ b ∈ C`), (c) an sc-splitting
`F = Q ⊕ Y` with `Y = Df(0)X` — this uses the sc-Fredholm property of `Df(0)` (regularity and
closed finite-codimensional range on every level), which `B` gives only through
`ConstIndexFredholm` — and (d) transport of `IsScSmooth`, `scDeriv`, the compactness and `D₂f`
conditions and `IsConjugateToBasicGerm` along these sc-isomorphisms.  `A`'s hypotheses are then
implied by `B`'s: (1) only at the points `(b, 0)` (smooth points), (2) the bijectivity of
`P ∘ Df(0)|X` (from `ker Df(0) ⊆ B`, `Y = Df(0)X`), and `A`'s `CompactnessCondition` after
shrinking `r` so that `|b₀| < r`, `b₀ ∈ C̃` force `(b₀, 0) ∈ U`.

`B → A` fails for genuine reasons: `A`'s condition (1) is required only at the points `(b, 0)` and
`A`'s condition (2) is only the bijectivity of `P ∘ Df(0)|X` (it does not give `ker Df(0) ⊆ ℝⁿ ⊕ 0`),
so `B`'s hypotheses (Fredholm of constant index at *all* smooth points of `U`, `B ⊇ ker Df(0)`)
are not available; `A`'s conclusion is more specific (the family `L(b) = P ∘ D₂f(b, 0)|X` of
sc-isomorphisms, the explicit push-forward `pushGerm358` and the fibre isomorphism `fiberIsoMap`);
and the conjuncts `lemma_3_7_2`, `lemma_3_7_3`, `fredholmIndex_block`,
`surjective_of_fredholmIndex_block`, `familyCompactness_derivFamOp` are general lemmas with no
counterpart in `B`. -/

open Set

noncomputable section

namespace RoundTrip.V3_89
open Polyfold

/-- The project's statement (universes of the two block-index lemmas at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.theorem_3_7_1) ∧ (type_of% @Polyfold.familyCompactness_derivFamOp) ∧
    (type_of% @Polyfold.fredholmIndex_block.{0, 0, 0, 0}) ∧
    (type_of% @Polyfold.surjective_of_fredholmIndex_block.{0, 0, 0, 0}) ∧
    (type_of% @Polyfold.lemma_3_7_2) ∧ (type_of% @Polyfold.lemma_3_7_3)

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_7_1, @Polyfold.familyCompactness_derivFamOp,
    @Polyfold.fredholmIndex_block.{0, 0, 0, 0}, @Polyfold.surjective_of_fredholmIndex_block.{0, 0, 0, 0},
    @Polyfold.lemma_3_7_2, @Polyfold.lemma_3_7_3⟩

end RoundTrip.V3_89

end
