import Polyfold
/-! Blind formalization of V15_12 (the Springer 2021 book, Part II, §15.2, Theorem 15.2.2,
pp. 688–689; 2017: Theorem 15.2).

Text: let `x ∈ supp(Λ ∘ f)` with `d_X(x) = 0` and `(f, Λ)` transversal at `x`.  There is `U(x)` with
the natural `G_x`-action such that (1) `d_X ≡ 0` on `U(x)`; (2) `T(f,Λ)` is onto on `M_{U(x)}`;
(3) there are submanifolds `Mᵢ` and weights `σᵢ > 0` with (a) `Mᵢ` smooth with `d ≡ 0`; (b) properly
embedded; (c) `M_{U(x)} = ⋃ Mᵢ`; (d) `Λ(f(y)) = ∑_{y ∈ Mᵢ} σᵢ`; (e) `T(f,Λ)(y) =
∑_{f(y) = sᵢ(y)} σᵢ (f − sᵢ)'(y)`.

Choices:
- Setting: universe 0, `SEP.{0}` (a strong bundle over an ep-groupoid; no tameness needed in the
  interior), `f` an sc-Fredholm section functor (`EpStrongBundle.IsScFredholmSectionFunctor`),
  `Λ` an sc⁺-multisection functor (`IsScPlusMultisection`).
- `supp(Λ ∘ f) = {x | Λ(f(x)) > 0}`; `M_{U(x)} = {y ∈ U(x) | Λ(f(y)) > 0}`.  `d_X` is the degeneracy
  index of the object M-polyfold (`MPolyfold.degIndex`).  "transversal at `x`": the project's
  `IsTransversalAt` (Definition 15.2.1 (2), `#print`ed: `Λ(f(x)) > 0` and every operator of
  `T(f,Λ)(x)` with positive weight is onto, `x ∈ X₁`); "`T(f,Λ)` onto at `y`": `IsOntoAt`.
  `T(f,Λ)(y)` is the project's `linearization f Λ y` (Definition 15.1.7: the formal sum of
  Theorem 15.1.1 (2) for some local structure and chart, `#print`ed).
- "`U(x)` with the natural `G_x`-action": the domain `R.U` of a natural representation
  `R : NaturalRep x` (`#print`ed: connected open `U ∋ x` with the action `Φ`, `Γ`).
- Reading of (3): the `sᵢ`, `σᵢ` in (e) are a local sc⁺-section structure of `Λ` (`IsLocalRepOn`)
  on an open `O ⊇ U(x)`, and the submanifolds are its solution sets
  `Mᵢ = {y ∈ U(x) | f(y) = sᵢ(y)}` with the same weights `σᵢ > 0`.  (a): `Mᵢ ⊆ X_∞`, `Mᵢ` a smooth
  submanifold (the project's `MPolyfold.IsSmoothSubmanifold`), `d ≡ 0` on `Mᵢ`; (b): the inclusion
  `Mᵢ → U(x)` is a proper map; (c), (d) as written; (e): for every level-`1` point `y ∈ U(x)` and
  every bundle chart `c` with domain in `O` around `y`, `T(f,Λ)(y)` is the formal sum
  `linSumIntr c` (`∑_{i : f(y) = sᵢ(y)} σᵢ (f − sᵢ)'(y)` read in `c`, as in my `V15_2.lean`).
  Linking the `Mᵢ` to the `sᵢ` is my reading of how (e) enters; with it (c), (d) are automatic.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V15_12
open Polyfold Polyfold.SBLocalization

/-- The sheet `Mᵢ = {y ∈ U | f(y) = sᵢ(y)}`. -/
def sheet {A : SEP.{0}} (U : Set A.Obj) (f s : A.Obj → A.W) : Set A.Obj :=
  {y | y ∈ U ∧ f y = s y}

open Classical in
/-- Theorem 15.2.2. -/
def B : Prop :=
  ∀ (A : SEP.{0}) (f : A.Obj → A.W) (Λ : A.W → ℚ≥0),
    A.E.IsScFredholmSectionFunctor f → IsScPlusMultisection A Λ →
    ∀ x : A.Obj, 0 < Λ (f x) → A.X.PObj.degIndex x = 0 → IsTransversalAt f Λ x →
    ∃ R : A.X.NaturalRep x,
      -- (1) `d_X ≡ 0` on `U(x)`
      (∀ y ∈ R.U, A.X.PObj.degIndex y = 0) ∧
      -- (2) `T(f,Λ)` onto on `M_{U(x)}`
      (∀ y ∈ R.U, 0 < Λ (f y) → IsOntoAt f Λ y) ∧
      -- (3)
      ∃ (O : Set A.Obj), IsOpen O ∧ R.U ⊆ O ∧
      ∃ (k : ℕ) (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0), IsLocalRepOn A Λ O s σ ∧
        -- (a) smooth submanifolds with `d ≡ 0`
        (∀ i, sheet R.U f (s i) ⊆ A.X.PObj.smoothSet ∧
          A.X.PObj.IsSmoothSubmanifold (sheet R.U f (s i)) ∧
          ∀ y ∈ sheet R.U f (s i), A.X.PObj.degIndex y = 0) ∧
        -- (b) properly embedded
        (∀ i, ∃ h : sheet R.U f (s i) ⊆ R.U, IsProperMap (Set.inclusion h)) ∧
        -- (c) `M_{U(x)} = ⋃ Mᵢ`
        ({y | y ∈ R.U ∧ 0 < Λ (f y)} = ⋃ i, sheet R.U f (s i)) ∧
        -- (d) `Λ(f(y)) = ∑_{y ∈ Mᵢ} σᵢ` (weights `σᵢ > 0` by `IsLocalRepOn`)
        (∀ y ∈ R.U, Λ (f y) = ∑ i with y ∈ sheet R.U f (s i), σ i) ∧
        -- (e) the linearization is the formal sum over the branches
        (∀ (y : A.X.PObj.Level 1), A.X.PObj.levelVal 1 y ∈ R.U →
          ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c → c.φ.source ⊆ O →
          ∀ hy : A.X.PObj.levelVal 1 y ∈ c.φ.source,
            linearization f Λ y = linSumIntr c hy f s σ)

end RoundTrip.V15_12
