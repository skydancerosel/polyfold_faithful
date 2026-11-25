import Polyfold
/-! Blind formalization of V15_29 (the Springer 2021 book, Part II, §15.3, Theorem 15.3.7,
pp. 693–698; 2017: Theorem 15.4): general position, existence of the perturbation.

Text: `X` tame with sc-smooth bump functions, `f` sc-Fredholm with `|S_f|` compact, `(N, U)`
controlling compactness, `h : X → (0, 1]` a continuous functor.  There is an sc⁺-multisection
functor `Λ` with (1) `N(Λ) < h`, (2) `dom-supp Λ ⊆ U`, (3) `T(f,Λ)` onto on `supp(Λ ∘ f)`,
(4) kernels in general position to `∂X`; `Λ` can be taken structurable.

Choices:
- Setting: universe 0, a strong bundle over an ep-groupoid `A : SEP.{0}` (as in my earlier
  `V15_*.lean`).  "`X` tame": `A.X.IsTame` (Definition 7.1.6); "with sc-smooth bump functions":
  `A.X.AdmitsBumpFunctions` (the ep-groupoid notion, Definition 12.3.1, `#print`ed: for every
  object `x` and saturated open `U ∋ x` an sc-smooth, not identically zero, morphism-invariant
  `f : X → ℝ` with support in `U`).
- `f` sc-Fredholm: `A.E.IsScFredholmSectionFunctor f` (`#print`ed: sc-smooth section functor and
  sc-Fredholm section).  `|S_f|` compact: `A.E.HasCompactSolutionSetEp f` (`#print`ed:
  `π(S_f)` compact in `|X|`).
- `(N, U)` controlling compactness: the project's `ControlsCompactness` (Definition 15.3.1,
  `#print`ed: `N` an auxiliary norm, `U` open and saturated, `S_f ⊆ U`, and the closure of
  `π{x ∈ U | N(f(x)) ≤ 1}` compact).
- `h : X → (0, 1]` a continuous functor: my `IsUnitFunctor`: `h : Obj → ℝ` continuous with
  `0 < h ≤ 1` and `h(s φ) = h(t φ)` for every morphism.
- (1) `N(Λ) < h`: pointwise at every object, `N(Λ)(x) < h(x)` with the project's
  `pointwiseNorm` (Definition 13.2.3, `#print`ed: the sup of `N` over `supp Λ ∩ W_x`).
  (2) the project's `domSupp` (Definition 13.2.2 (1), closure of the points carrying a nonzero
  `w` with `Λ(w) > 0`).  (3) "`T(f,Λ)` onto on `supp(Λ ∘ f)`": the project's `IsTransversal`
  (Definition 15.2.1, `#print`ed: at every `x` with `Λ(f(x)) > 0`, `x ∈ X₁` and every operator of
  `T(f,Λ)(x)` with positive weight onto).  (4) "kernels in general position to `∂X`":
  `(f, Λ)` in general position, the project's `IsInGeneralPosition` (Definition 15.3.5,
  `#print`ed: at every `x ∈ X₁` with `Λ(f(x)) > 0` every operator of `T(f,Λ)(x)` is onto on the
  reduced tangent space `T^R_xX`, in every chart and presentation).
- "`Λ` can be taken structurable": B asserts the existence of a structurable `Λ`
  (`IsStructurable`, Definition 13.3.6) with (1)–(4); this implies the version without
  structurability.  I add no hypothesis for the structurable version (none is quoted).
- The "in particular" sentence of the theorem is the separate item V15_30.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V15_29
open Polyfold Polyfold.SBLocalization

/-- `h : X → (0, 1]` is a continuous functor. -/
def IsUnitFunctor (A : SEP.{0}) (h : A.Obj → ℝ) : Prop :=
  Continuous h ∧ (∀ x, 0 < h x ∧ h x ≤ 1) ∧ ∀ φ : A.Mor, h (A.X.src φ) = h (A.X.tgt φ)

/-- Theorem 15.3.7: a structurable sc⁺-multisection functor with (1)–(4) exists. -/
def B : Prop :=
  ∀ (A : SEP.{0}), A.X.IsTame → A.X.AdmitsBumpFunctions →
    ∀ (f : A.Obj → A.W), A.E.IsScFredholmSectionFunctor f → A.E.HasCompactSolutionSetEp f →
    ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
    ∀ (h : A.Obj → ℝ), IsUnitFunctor A h →
      ∃ Λ : A.W → ℚ≥0, IsScPlusMultisection A Λ ∧ IsStructurable A Λ ∧
        -- (1) `N(Λ) < h`
        (∀ x, pointwiseNorm N Λ x < h x) ∧
        -- (2) `dom-supp Λ ⊆ U`
        domSupp Λ ⊆ U ∧
        -- (3) `T(f,Λ)` onto on `supp(Λ ∘ f)`
        IsTransversal f Λ ∧
        -- (4) general position to `∂X`
        IsInGeneralPosition A f Λ

end RoundTrip.V15_29
