import Polyfold.Chapter4.VectorFieldsGlobal
import Polyfold.Chapter8.TangentLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Appendix 4.5,
**Lemma 4.5.1** (p. 201, new in the 2021 edition; the proof is left to the reader), for a local
sc-diffeomorphism between **open subsets** of an M-polyfold (gap G.92, first half).

# Lemma 4.5.1 between open subsets

## The text, paraphrased

(Lemma 4.5.1) A local sc-diffeomorphism `φ` of `X` that relates the sc-smooth vector fields `A`
and `B` to themselves (`Tφ(A(x)) = A(φ(x))`, `Tφ(B(x)) = B(φ(x))`) relates `[A, B]` to itself.
A local sc-diffeomorphism is defined on an open subset `U ⊆ X` with values in an open `U' ⊆ X`.

## What is formalized

* `restrictVectorField hU A`: the restriction `A|U` of a vector field to the open sub-M-polyfold
  `U` (`MPolyfold.restrictOpen`, Part I), `(Tι)⁻¹ ∘ A ∘ ι₁` with `ι : U → X` the inclusion;
  `IsScVectorField.restrictOpen`: it is an sc-smooth vector field of `U`;
  `tangentMap_restrictVectorField`: `Tι (A|U(x)) = A(x)`.
* `tangentMap_lieBracket_restrictOpen`: `Tι [A|U, B|U](x) = [A, B](x)` for `x ∈ U²`, and
  `lieBracket_restrictOpen`: `[A|U, B|U] = [A, B]|U` (the bracket is local).
* `lemma_4_5_1_open` (**Lemma 4.5.1** for maps between open subsets): for open `U, U' ⊆ X`, an
  sc-smooth `φ : U → U'` (in particular a local sc-diffeomorphism of `X` from `U` onto `U'`) with
  `Tφ ∘ A|U = A|U' ∘ φ₁` and `Tφ ∘ B|U = B|U' ∘ φ₁` on `U¹`, `Tφ ∘ [A|U, B|U] = [A|U', B|U'] ∘ φ₂`
  on `U²`; and `lemma_4_5_1_open_ambient`, the same read in `TX`:
  `T(ι' ∘ φ)((Tι)⁻¹[A, B](x)) = [A, B](φ(x))`.

## The reading

* `U`, `U'` carry Part I's structure `restrictOpen` (charts of `X` inside `U`), which needs a junk
  point (`[Nonempty U]`) and `[ParacompactSpace U]` (supplied by `MPolyfold.paracompactSpace_subtype`).
* As in `lemma_4_5_1` (V4.77), the relations are assumed on `U¹`, since the computation of §4.5.2
  differentiates them; the map `φ` need only be sc-smooth.
-/

open Set Function

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

section Restrict

variable {U : Set X} (hU : IsOpen U) [Nonempty U] [ParacompactSpace U]

/-- The restriction `A|U = (Tι)⁻¹ ∘ A ∘ ι₁ : U¹ → TU` of a vector field to an open subset `U`,
with `(Tι)⁻¹` the tangent map of `x ↦ x`, `X ⊇ U → U`. -/
def restrictVectorField (A : P.Level 1 → P.TangentSpace) (x : (P.restrictOpen hU).Level 1) :
    (P.restrictOpen hU).TangentSpace :=
  tangentMapOn (isScSmoothOn_openRetraction hU)
    (A (liftLevelOneMap (isScSmoothMap_subtypeVal hU) x))

variable {hU} {A B : P.Level 1 → P.TangentSpace}

@[simp] lemma levelVal_liftLevelOneMap_subtypeVal
    (x : (P.restrictOpen hU).Level 1) :
    P.levelVal 1 (liftLevelOneMap (isScSmoothMap_subtypeVal hU) x) =
      ((P.restrictOpen hU).levelVal 1 x : X) := rfl

/-- `A(ι₁ x)` lies over `U`. -/
lemma mem_tangentPreimage_restrict (hA : P.IsScVectorField A) (x : (P.restrictOpen hU).Level 1) :
    A (liftLevelOneMap (isScSmoothMap_subtypeVal hU) x) ∈ P.tangentPreimage U := by
  change P.levelVal 1 (P.tangentProj (A _)) ∈ U
  rw [hA.2]
  exact ((P.restrictOpen hU).levelVal 1 x).2

/-- `Tι (A|U(x)) = A(x)`. -/
theorem tangentMap_restrictVectorField (hA : P.IsScVectorField A)
    (x : (P.restrictOpen hU).Level 1) :
    tangentMap (isScSmoothMap_subtypeVal hU) (restrictVectorField hU A x) =
      A (liftLevelOneMap (isScSmoothMap_subtypeVal hU) x) :=
  (isScDiffeoOn_tangentMap_subtypeVal hU).right_inv _ (mem_tangentPreimage_restrict hA x)

/-- **The restriction of an sc-smooth vector field to an open subset is an sc-smooth vector
field.** -/
theorem IsScVectorField.restrictOpen (hA : P.IsScVectorField A) :
    (P.restrictOpen hU).IsScVectorField (restrictVectorField hU A) := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 : (P.restrictOpen hU).shift.IsScSmoothMap P.tangentPolyfold
        (A ∘ liftLevelOneMap (isScSmoothMap_subtypeVal hU)) :=
      hA.1.comp (IsScSmoothMap.levelOne (isScSmoothMap_subtypeVal hU) fun _ => rfl)
    exact IsScSmoothOn.comp (tangentMapOn_isScSmoothOn (isScSmoothOn_openRetraction hU)) h1
      fun x _ => mem_tangentPreimage_restrict hA x
  · apply level_ext
    rw [restrictVectorField, levelVal_tangentProj_tangentMapOn _
      (mem_tangentPreimage_restrict hA x), hA.2, levelVal_liftLevelOneMap_subtypeVal,
      openRetraction_of_mem ((P.restrictOpen hU).levelVal 1 x).2]

/-- **`Tι [A|U, B|U](x) = [A, B](x)`** for `x ∈ U²` (Lemma 4.5.1 for the inclusion `ι`). -/
theorem tangentMap_lieBracket_restrictOpen (hA : P.IsScVectorField A) (hB : P.IsScVectorField B)
    (x : (P.restrictOpen hU).shift.Level 1) :
    tangentMap (isScSmoothMap_subtypeVal hU) (lieBracket hA.restrictOpen hB.restrictOpen x) =
      lieBracket hA hB (levelTwoMap (isScSmoothMap_subtypeVal hU) x) :=
  lemma_4_5_1 _ hA.restrictOpen hB.restrictOpen hA hB (tangentMap_restrictVectorField hA)
    (tangentMap_restrictVectorField hB) x

/-- `[A, B](x)` lies over `U` for `x ∈ U²`. -/
lemma lieBracket_mem_tangentPreimage (hA : P.IsScVectorField A) (hB : P.IsScVectorField B)
    (x : (P.restrictOpen hU).shift.Level 1) :
    lieBracket hA hB (levelTwoMap (isScSmoothMap_subtypeVal hU) x) ∈ P.tangentPreimage U := by
  rw [← tangentMap_lieBracket_restrictOpen hA hB x]
  rw [← range_tangentMap_subtypeVal hU]
  exact mem_range_self _

/-- **The bracket is local**: `[A|U, B|U] = [A, B]|U = (Tι)⁻¹ ∘ [A, B] ∘ ι₂`. -/
theorem lieBracket_restrictOpen (hA : P.IsScVectorField A) (hB : P.IsScVectorField B)
    (x : (P.restrictOpen hU).shift.Level 1) :
    lieBracket hA.restrictOpen hB.restrictOpen x =
      tangentMapOn (isScSmoothOn_openRetraction hU)
        (lieBracket hA hB (levelTwoMap (isScSmoothMap_subtypeVal hU) x)) := by
  rw [← tangentMap_lieBracket_restrictOpen hA hB x]
  exact ((isScDiffeoOn_tangentMap_subtypeVal hU).left_inv _ (mem_univ _)).symm

end Restrict

section Open

variable {U U' : Set X} {hU : IsOpen U} {hU' : IsOpen U'} [Nonempty U] [ParacompactSpace U]
  [Nonempty U'] [ParacompactSpace U'] {A B : P.Level 1 → P.TangentSpace}

/-- **2021 Lemma 4.5.1, p. 201** (new in the 2021 edition), for a map `φ : U → U'` between open
subsets of `X` (the text: a local sc-diffeomorphism of `X`): if `φ` is sc-smooth and
`Tφ ∘ A|U = A|U' ∘ φ₁`, `Tφ ∘ B|U = B|U' ∘ φ₁` on `U¹`, then `Tφ ∘ [A|U, B|U] = [A|U', B|U'] ∘ φ₂`
on `U²`; by `lieBracket_restrictOpen` the brackets of the restrictions are the restrictions of
`[A, B]`.  Every local sc-diffeomorphism between open subsets is such a `φ`. -/
theorem _root_.Polyfold.lemma_4_5_1_open {φ : U → U'}
    (hφ : (P.restrictOpen hU).IsScSmoothMap (P.restrictOpen hU') φ)
    (hA : P.IsScVectorField A) (hB : P.IsScVectorField B)
    (hAφ : ∀ x, tangentMap hφ (restrictVectorField hU A x) =
      restrictVectorField hU' A (liftLevelOneMap hφ x))
    (hBφ : ∀ x, tangentMap hφ (restrictVectorField hU B x) =
      restrictVectorField hU' B (liftLevelOneMap hφ x))
    (x : (P.restrictOpen hU).shift.Level 1) :
    tangentMap hφ (lieBracket hA.restrictOpen hB.restrictOpen x) =
      lieBracket hA.restrictOpen hB.restrictOpen (levelTwoMap hφ x) :=
  lemma_4_5_1 hφ hA.restrictOpen hB.restrictOpen hA.restrictOpen hB.restrictOpen hAφ hBφ x

/-- **Lemma 4.5.1 between open subsets, read in `TX`**: for `g = ι' ∘ φ : U → X` sc-smooth with
`Tg(A|U(x)) = A(g(x))` and `Tg(B|U(x)) = B(g(x))` on `U¹`,
`Tg((Tι)⁻¹[A, B](x)) = [A, B](g(x))` for `x ∈ U²` (the text's `Tφ([A, B](x)) = [A, B](φ(x))`). -/
theorem _root_.Polyfold.lemma_4_5_1_open_ambient {g : U → X}
    (hg : (P.restrictOpen hU).IsScSmoothMap P g)
    (hA : P.IsScVectorField A) (hB : P.IsScVectorField B)
    (hAg : ∀ x, tangentMap hg (restrictVectorField hU A x) = A (liftLevelOneMap hg x))
    (hBg : ∀ x, tangentMap hg (restrictVectorField hU B x) = B (liftLevelOneMap hg x))
    (x : (P.restrictOpen hU).shift.Level 1) :
    tangentMap hg (tangentMapOn (isScSmoothOn_openRetraction hU)
        (lieBracket hA hB (levelTwoMap (isScSmoothMap_subtypeVal hU) x))) =
      lieBracket hA hB (levelTwoMap hg x) := by
  rw [← lieBracket_restrictOpen hA hB x]
  exact lemma_4_5_1 hg hA.restrictOpen hB.restrictOpen hA hB hAg hBg x

end Open

end MPolyfold

end Polyfold
