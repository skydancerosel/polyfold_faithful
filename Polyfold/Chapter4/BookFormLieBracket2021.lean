import Polyfold.Chapter4.VectorFieldsGlobal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4:
**Proposition 4.4.5** (p. 196; proof in §§4.5.1–4.5.2, pp. 200–202), in one statement (2017:
Proposition 4.5; preprint: Proposition 4.26).

# Proposition 4.4.5 in book form

## The text, paraphrased

(Proposition 4.4.5) For sc-smooth vector fields `A`, `B` on the M-polyfold `X`, the usual formula
in local coordinates defines the Lie bracket `[A, B]`, an sc-smooth section of `TX|X² → X²`, the
pull-back of `TX → X¹` by the inclusion `X² → X¹`.

## What is formalized

* `MPolyfold.proposition_4_4_5_book`: there is a map `L : X² → TX` which in **every** chart `ψ`
  around `x` is given by the usual formula, `Tψ(L(x)) = (ψ(x), [A_ψ, B_ψ](ψ(x)))` with
  `[A_ψ, B_ψ](z) = DÃ_ψ(z)B_ψ(z) − DB̃_ψ(z)A_ψ(z)` (`chartLieBracket`, `retractLieBracket`;
  Lemma 4.5.1: the formula does not depend on the chart), and `L` is sc-smooth `X² → TX` with
  `p(L(x)) = x`.  `L` is `lieBracket`; assembled from `tangentChartMap_lieBracket` and
  `proposition_4_4_5`, the local computation being `proposition_4_4_5_local`.

## The reading

* "An sc-smooth section of `TX|X² → X²`" is read as an sc-smooth map `X² → TX` covering the
  inclusion `X² → X¹`.  The pull-back bundle itself, as a sub-M-polyfold of `X² × TX`, with
  `[A, B]` an sc-smooth section of it, is `proposition_4_4_5_section` (`GapP1_Lemma451Bundle.lean`,
  gap G.92).
-/

open Set Function

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {A B : P.Level 1 → P.TangentSpace}

/-- **2021 Proposition 4.4.5, p. 196** (2017: Proposition 4.5; preprint: Proposition 4.26), in book
form: for sc-smooth vector fields `A`, `B` on `X`, the usual formula in local coordinates defines a
map `[A, B] : X² → TX` — in every chart `ψ` around `x ∈ X²`,
`Tψ([A, B](x)) = (ψ(x), [A_ψ, B_ψ](ψ(x)))` — which is sc-smooth and covers the inclusion
`X² → X¹` (`p([A, B](x)) = x`), i.e. an sc-smooth section of `TX|X² → X²` read as a map.
The map is `lieBracket hA hB`. -/
theorem proposition_4_4_5_book (hA : P.IsScVectorField A) (hB : P.IsScVectorField B) :
    ∃ L : P.shift.Level 1 → P.TangentSpace,
      (∀ (x : P.shift.Level 1) {ψ : MChart X} (hψ : P.IsChart ψ)
        (_ : P.levelVal 1 (P.shift.levelVal 1 x) ∈ ψ.source) (y₀ : P.Level 1),
        tangentChartMap hψ (L x) =
          ((levelLift ψ 1 (P.levelVal 1 (P.shift.levelVal 1 x)), chartLieBracket hψ y₀ A B
            (levelLift (levelChart hψ y₀) 1 (P.shift.levelVal 1 x))) : ψ.model.E.tangent 0)) ∧
      P.shift.shift.IsScSmoothMap P.tangentPolyfold L ∧
      ∀ x, P.tangentProj (L x) = P.shift.levelVal 1 x :=
  ⟨lieBracket hA hB, fun x _ hψ hx y₀ => tangentChartMap_lieBracket hA hB x hψ hx y₀,
    (proposition_4_4_5 hA hB).1, (proposition_4_4_5 hA hB).2⟩

end MPolyfold

end Polyfold
