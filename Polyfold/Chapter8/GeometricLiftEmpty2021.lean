import Polyfold.Chapter8.NonVacuity
import Mathlib.CategoryTheory.Groupoid.Discrete

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 8,
§8.5, **Proposition 8.5.7** (p. 390; 2017: Proposition 8.3) for `D = ∅`.

# Proposition 8.5.7 needs `D` nonempty

## The text, paraphrased

(Definition 8.5.5) A covering functor `f : D → C` of finite groupoids, `C` with one object `x`,
is a functor with `ψ ↦ (f(ψ), s(ψ))` a bijection onto `C ₛ×_f D`; a geometric lift is a natural
transformation `τ : L_D → L_C ∘ f`.  (Proposition 8.5.7) A geometric lift gives a proper
covering functor `F : Y → G_x ⋉ U(x)`, `Y = ⊔_{y ∈ D} U(y)`.

## What is formalized

* `CoveringExamples.EmptyD`: the empty groupoid; `emptyCover : ∅ → SingleObj ℤˣ` is a covering
  functor (`isCoveringFunctor_of_isEmpty`: both sides of the bijection are empty).
* `CoveringExamples.emptyLift`: a geometric lift of it, `L_C(⋆) = ℝ` with `ℤ/2` acting by
  reflection (`reflectionHom`).
* **`CoveringExamples.not_proposition_8_5_7_empty`**: `F` is not a proper covering functor, since
  `Y = ∅` while `U(x) = ℝ`, so `F` is not surjective on objects (Definition 8.5.1 (1);
  `geometricLiftFunctor_surjective_iff`).  As we read Definition 8.5.5, which does not exclude
  `D = ∅`, Proposition 8.5.7 does not hold for this covering functor; `proposition_8_5_7`
  assumes `[Nonempty D]`, which holds where the proposition is used (Theorem 8.5.8,
  `D = F⁻¹(x)`).
-/

open CategoryTheory Set Function

namespace Polyfold.CoveringExamples

/-- **The empty groupoid** `D = ∅` (the discrete groupoid on `PEmpty`). -/
abbrev EmptyD : Type := Discrete PEmpty.{1}

instance : IsEmpty EmptyD := ⟨fun a => a.as.elim⟩

instance : Fintype EmptyD := Fintype.ofIsEmpty

instance (a b : EmptyD) : Fintype (a ⟶ b) := isEmptyElim a

/-- The functor `∅ → SingleObj ℤˣ`, a covering functor (Definition 8.5.5 allows `D = ∅`). -/
def emptyCover : EmptyD ⥤ SingleObj ℤˣ := Discrete.functor fun a => a.elim

theorem isCoveringFunctor_emptyCover : IsCoveringFunctor emptyCover :=
  isCoveringFunctor_of_isEmpty _

/-- **A geometric lift of `emptyCover`** (Definition 8.5.5): `L_C(⋆) = ℝ` with `ℤ/2` acting by
reflection, `L_D` and `τ` empty. -/
def emptyLift : GeometricLift.{0} emptyCover where
  LC := SingleObj.functor reflectionHom
  LD := Discrete.functor fun a => a.elim
  τ := Discrete.natTrans fun a => a.as.elim

/-- **2021 Proposition 8.5.7 (p. 390) for `D = ∅`**: for the covering functor `∅ → SingleObj ℤˣ`
and its geometric lift with `U(x) = ℝ`, the functor `F : ∅ → ℤ/2 ⋉ ℝ` is not a proper covering
functor, as it is not surjective on objects.  The hypothesis `[Nonempty D]` of
`proposition_8_5_7` cannot be dropped. -/
theorem not_proposition_8_5_7_empty :
    IsCoveringFunctor emptyCover ∧ ¬ (geometricLiftFunctor emptyLift).IsProperCovering := by
  refine ⟨isCoveringFunctor_emptyCover, fun h => ?_⟩
  rcases (geometricLiftFunctor_surjective_iff emptyLift).1 h.surjective with hD | hU
  · exact hD.elim isEmptyElim
  · exact hU.false (0 : Fin 1 → ℝ)

end Polyfold.CoveringExamples
