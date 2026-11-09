import Polyfold
/-! Blind formalization of V11_16 (the text's Part II, §11.3, pp. 536–537 of the Springer 2021
book, after Lemma 11.3.2; 2017: pp. 389–390).

Text: for a generalized isomorphism `f = [X ←F A →Φ Y]`, `f_*Θ = Φ_*F^*Θ` and
`f^*Θ' = F_*Φ^*Θ'`, independent of the representative; `(g ∘ f)_* = g_* ∘ f_*` and the like are
"easily verified".

Choices:
- Setting: `X`, `Y`, `Z` objects of the project's bundled `EP.{0}` (all spaces in `Type`); `f`,
  `g` morphisms of the project's `EP(E⁻¹)`, diagrams the project's `Diagram` (`d.F` the
  equivalence `F`, `d.Φ` the functor `Φ`), `[d]` is `EPLoc.homMk d`; "generalized
  isomorphism": Mathlib's `IsIso` (Definition 10.3.9).
- `F^*`, `F_*`, `Φ^*`, `Φ_*`: the project's `pullbackTheta`, `pushforwardTheta` (Definition
  11.3.1, compared with the text in my `RoundTrip/Blind/V11_14.lean`).  `f_*Θ`, `f^*Θ'` are
  computed on a representative (`pushRepB`, `pullRepB`); the project's `EPLoc.pushTheta`,
  `pullTheta` are not used.
- `Θ`, `Θ'`: functors to `ℚ⁺` (`IsQFunctorB`: `0 ≤ Θ`, constant along morphisms), the domain of
  Definition 11.3.1; the equalities are asserted only for them.
- "independent of the representative": any two representatives give the same `f_*Θ`, `f^*Θ'`.
- "`(g ∘ f)_* = g_* ∘ f_*` and the like": I formalize `(g ∘ f)_* = g_* ∘ f_*` and its pull-back
  analogue `(g ∘ f)^* = f^* ∘ g^*`, for generalized isomorphisms `f : X → Y`, `g : Y → Z` and any
  representatives of `f`, `g`, `g ∘ f` (Mathlib's `f ≫ g`).  Other identities that "the like"
  might cover (`1_* = id`, `f^*f_* = id`, ...) are not included.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_16
open Polyfold CategoryTheory
open Polyfold.EPLocalization

/-- `Θ : X → ℚ⁺` is a functor: nonnegative and constant along morphisms. -/
def IsQFunctorB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) : Prop :=
  (∀ x, 0 ≤ Θ x) ∧ ∀ φ : Mor, Θ (X.src φ) = Θ (X.tgt φ)

/-- `Φ_*F^*Θ` for the representative `d = X ←F A →Φ Y`. -/
noncomputable def pushRepB {X Y : EP.{0}} (d : Diagram X Y) (Θ : X.Obj → ℚ) : Y.Obj → ℚ :=
  d.Φ.pushforwardTheta (d.F.pullbackTheta Θ)

/-- `F_*Φ^*Θ'` for the representative `d = X ←F A →Φ Y`. -/
noncomputable def pullRepB {X Y : EP.{0}} (d : Diagram X Y) (Θ' : Y.Obj → ℚ) : X.Obj → ℚ :=
  d.F.pushforwardTheta (d.Φ.pullbackTheta Θ')

/-- Pp. 536–537: `f_* = Φ_*F^*` and `f^* = F_*Φ^*` do not depend on the representative, and
`(g ∘ f)_* = g_* ∘ f_*`, `(g ∘ f)^* = f^* ∘ g^*`. -/
def B : Prop :=
  (∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), IsIso f →
    ∀ d d' : Diagram X Y, EPLoc.homMk d = f → EPLoc.homMk d' = f →
      (∀ Θ : X.Obj → ℚ, IsQFunctorB X.X Θ → pushRepB d Θ = pushRepB d' Θ) ∧
      (∀ Θ' : Y.Obj → ℚ, IsQFunctorB Y.X Θ' → pullRepB d Θ' = pullRepB d' Θ')) ∧
  (∀ (X Y Z : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y) (g : EPLoc.of Y ⟶ EPLoc.of Z),
    IsIso f → IsIso g →
    ∀ (d : Diagram X Y) (e : Diagram Y Z) (c : Diagram X Z),
      EPLoc.homMk d = f → EPLoc.homMk e = g → EPLoc.homMk c = f ≫ g →
      (∀ Θ : X.Obj → ℚ, IsQFunctorB X.X Θ → pushRepB c Θ = pushRepB e (pushRepB d Θ)) ∧
      (∀ Θ'' : Z.Obj → ℚ, IsQFunctorB Z.X Θ'' →
        pullRepB c Θ'' = pullRepB d (pullRepB e Θ'')))

end RoundTrip.V11_16
