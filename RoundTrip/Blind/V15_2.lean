import Polyfold
/-! Blind formalization of V15_2 (the Springer 2021 book, Part II, §15.1, Theorem 15.1.1,
pp. 684–687; 2017: Theorem 15.1).

Text: for an sc-Fredholm section `f` and an sc⁺-multisection `Λ` there is a unique section functor
`T(f,Λ)` of `GrF(X) → X_∞` with (1) `T(f,Λ)(x) = 0` off `supp(Λ ∘ f)` and
(2) `T(f,Λ)(y) = ∑_{f(y) = sᵢ(y)} σᵢ (f − sᵢ)'(y)` for any local sc⁺-section structure.

Choices:
- Setting: universe 0; a strong bundle `P : W → X` over an ep-groupoid is the project's `SEP.{0}`.
  `f` is an sc-Fredholm section functor (`EpStrongBundle.IsScFredholmSectionFunctor`: an sc-smooth
  section functor which is sc-Fredholm); `Λ : W → ℚ⁺` an sc⁺-multisection functor
  (`IsScPlusMultisection`, Definition 13.2.1).  No other hypothesis.
- `GrF(x)` is the project's `GrF x` (2021 p. 683: finite formal sums with coefficients in `ℚ⁺` of
  linear operators `T_xX → W_x`, defined at `x ∈ X₁`).  A section of `GrF(X) → X_∞` is a choice
  `T(x) ∈ GrF(x)`; I represent it by a function on the level-`1` points and, following my
  statement file literally (`X_∞`), impose (1), (2), the functor property and uniqueness only at
  the smooth points `x ∈ X_∞` (`smoothSet`).  If the text means `X₁` this is weaker.
- "functor": for every morphism `φ : x → y` (`φ ∈ 𝐗₁` so that `Tφ` exists) between smooth points,
  `T(y) = φ_* T(x)`, with the project's `grfPush` (`∑ σ_L·L ↦ ∑ σ_L·μ(φ,·) ∘ L ∘ (Tφ)⁻¹`, p. 683).
- `supp(Λ ∘ f) = {x | Λ(f(x)) > 0}`; "`0`" is the empty formal sum.
- (2): a local sc⁺-section structure is an open `O` with sc⁺-sections `s₁, …, s_k` on `O` and
  weights `σᵢ > 0`, `∑ σᵢ = 1`, `Λ(w) = ∑_{i : w = sᵢ(P w)} σᵢ` over `O` (the project's
  `IsLocalRepOn`, `#print`ed).  `∑_{f(y) = sᵢ(y)} σᵢ (f − sᵢ)'(y)` is the project's `linSumIntr c`
  (`#print`ed: the sum over `i` with `f̂(y) = ŝᵢ(y)` of `σᵢ·Φ_y⁻¹ ∘ D((f̂ − ŝᵢ) ∘ r)(φ(y)) ∘ Tφ`
  read in a strong bundle chart `c`); I require it for EVERY chart `c` of the bundle atlas
  (`StrongBundle.IsChart`) with domain in `O` around `y` (the text's `(f − sᵢ)'(y)` is intrinsic).
- Nothing looks doubtful to me (apart from the `X_∞` / `X₁` question above).
-/
namespace RoundTrip.V15_2
open Polyfold Polyfold.SBLocalization

/-- The properties of Theorem 15.1.1 for a choice `T(x) ∈ GrF(x)`, at the smooth points. -/
def IsLinearizationB {A : SEP.{0}} (f : A.Obj → A.W) (Λ : A.W → ℚ≥0)
    (T : (x : A.X.PObj.Level 1) → GrF x) : Prop :=
  -- functor `X_∞ → GrF(X)` over the identity
  (∀ (φ : A.Mor) (hφ : φ ∈ A.X.PMor.levelSet 1) (x y : A.X.PObj.Level 1)
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ),
    A.X.PObj.levelVal 1 x ∈ A.X.PObj.smoothSet →
      T y = grfPush φ hφ hx hy (T x)) ∧
  -- (1) `T(f,Λ)(x) = 0` off `supp(Λ ∘ f)`
  (∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.smoothSet →
    Λ (f (A.X.PObj.levelVal 1 x)) = 0 → T x = 0) ∧
  -- (2) the formula for any local sc⁺-section structure, in any chart
  (∀ (O : Set A.Obj), IsOpen O → ∀ (k : ℕ) (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0),
    IsLocalRepOn A Λ O s σ →
    ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c → c.φ.source ⊆ O →
    ∀ (y : A.X.PObj.Level 1) (hy : A.X.PObj.levelVal 1 y ∈ c.φ.source),
      A.X.PObj.levelVal 1 y ∈ A.X.PObj.smoothSet →
        T y = linSumIntr c hy f s σ)

/-- Theorem 15.1.1: `T(f,Λ)` exists and is unique (on `X_∞`). -/
def B : Prop :=
  ∀ (A : SEP.{0}) (f : A.Obj → A.W) (Λ : A.W → ℚ≥0),
    A.E.IsScFredholmSectionFunctor f → IsScPlusMultisection A Λ →
      ∃ T : (x : A.X.PObj.Level 1) → GrF x, IsLinearizationB f Λ T ∧
        ∀ T' : (x : A.X.PObj.Level 1) → GrF x, IsLinearizationB f Λ T' →
          ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.smoothSet → T' x = T x

end RoundTrip.V15_2
