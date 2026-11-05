import Polyfold
/-! Blind formalization of V3_89 (the text's §3.7, Theorem 3.58, p. 116). Choices:
- Setting: arbitrary sc-Banach spaces `E`, `F`; `C ⊆ E₀` a partial quadrant and `U` a relatively
  open neighbourhood of `0` in `C` (`IsRelOpenInQuadrant`, `0 ∈ U`); `f : U → F` sc-smooth
  (`IsScSmooth U f`, Definition 1.15).  `f(0)` need not vanish.  No universe choices arise.
- `Df(x)` for `x ∈ U₁` is the derivative family `scDeriv U f` (a genuine derivative family since
  `f` is sc¹, and unique); on level `m` at a point of level `m + 1` it is `levelDeriv`.
- (1) "`Df(x)` sc-Fredholm of constant index at smooth points" (`ConstIndexFredholm`, defined
  here): there is `i : ℤ` such that for every smooth point `x ∈ U ∩ E_∞` (lifted to `x₁ ∈ E₁`) the
  operator `Df(x)` is an sc-operator `E → F` (some `T : ScOperator E F` with `T₀ = Df(x)`), which
  is sc-Fredholm (`IsScFredholm`, Definition 1.8) of index `scIndex T = i`.  "Constant" is read
  as one index for all smooth points of `U`.
- (2) "a splitting `E = B ⊕ X` with `B ⊇ ker Df(0)`": an sc-splitting (`E.IsScSplitting B X`) with
  `B` finite-dimensional (presupposed: the conclusion's basic germ has finite-dimensional
  parameters and the compactness condition takes limits `b_j → b` in `B`), and
  `ker Df(0) ⊆ B`.  I also add the compatibility `C = (B ∩ C) ⊕ X`
  (`b + x ∈ C ⟺ b ∈ C` for `b ∈ B`, `x ∈ X`), which the text presupposes when it writes points of
  `U` as `(b, x)`, `b ∈ B ∩ C`, `x ∈ X` small, in (3).
  "`Y = Df(0)X`" only names the image; it enters none of the quoted conditions, so it does not
  appear in `B`.
- "a compactness condition" (`CompactnessProp`, defined here; the quote does not spell it out, I
  follow the reading recorded in the docstring of the project's `CompactnessCondition`, but in the
  intrinsic setting `E = B ⊕ X`): there is `r > 0` such that for every level `m`: if
  `b_j → b` with `b_j, b ∈ B ∩ U`, `|b| < r`, `(η_j) ⊆ X_m` is bounded and
  `Df(b_j)η_j = y_j + z_j` on level `m` with `y_j → 0` in `F_m` and `(z_j)` bounded in `F_{m+1}`,
  then `(η_j)` has a convergent subsequence in `E_m`.  (Doubt: the text may say "`(y_j)` converges"
  instead of "`y_j → 0`".)
- (3) "a uniform estimate on `D₂f`" (`UniformD2Estimate`, defined here, after the project's
  `DerivCondition` docstring): for every `m` and `ε > 0` there is `r > 0` with
  `|[Df(b) − Df(b + x)]h|_m ≤ ε|h|_m` for all `b ∈ B ∩ U` with `|b| < r`, `x ∈ X_{m+1}` with
  `|x|_m < r` and `b + x ∈ U`, and `h ∈ X_m` (`D₂f(b, x)h = Df(b + x)h` for `h ∈ X`).
- Conclusion "`f − f(0)` is conjugated near `0` to a basic germ": there is a relatively open
  neighbourhood `U₀ ⊆ U` of `0` in `C` with `IsConjugateToBasicGerm U₀ (f − f(0))` (Definition 3.11,
  second paragraph: a strong bundle isomorphism `U₀ ◁ F → U' ◁ (ℝᴺ ⊕ W)` covering an
  sc-diffeomorphism fixing `0`, `U'` relatively open in `C̃ ⊕ W`, `C̃ ⊆ ℝⁿ` a partial quadrant,
  pushing `f − f(0)` forward to a basic germ near `0`).  I used the project's definition.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_89
open Polyfold Filter

/-- The kernel `ker L ⊆ E₀` of a bounded operator `L : E₀ → F₀`. -/
def kerOf {E F : ScBanach} (L : E.lvl 0 →L[ℝ] F.lvl 0) : Submodule ℝ (E.lvl 0) :=
  LinearMap.ker (L : E.lvl 0 →ₗ[ℝ] F.lvl 0)

/-- Condition (1): at every smooth point `x ∈ U` the linearization `Df(x)` is an sc-Fredholm
operator `E → F`, of one and the same index `i`. -/
def ConstIndexFredholm (E F : ScBanach) (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0) : Prop :=
  ∃ i : ℤ, ∀ x₁ : E.lvl 1, E.toBase 1 x₁ ∈ U → E.toBase 1 x₁ ∈ E.smooth →
    ∃ T : ScOperator E F, T.lvl 0 = scDeriv U f x₁ ∧ IsScFredholm T ∧ scIndex T = i

/-- Condition (2), the compactness property, for the splitting `E = B ⊕ X`. -/
def CompactnessProp (E F : ScBanach) (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (Bs X : Submodule ℝ (E.lvl 0)) : Prop :=
  ∃ r > 0, ∀ (m : ℕ) (b : ℕ → E.lvl (m + 1)) (b₀ : E.lvl (m + 1)) (η : ℕ → E.lvl m)
      (y : ℕ → F.lvl m) (z : ℕ → F.lvl (m + 1)),
    (∀ j, E.toBase (m + 1) (b j) ∈ Bs ∧ E.toBase (m + 1) (b j) ∈ U) →
    E.toBase (m + 1) b₀ ∈ Bs → E.toBase (m + 1) b₀ ∈ U → ‖E.toBase (m + 1) b₀‖ < r →
    Tendsto (fun j => E.toBase (m + 1) (b j)) atTop (nhds (E.toBase (m + 1) b₀)) →
    (∀ j, E.toBase m (η j) ∈ X) → (∃ M : ℝ, ∀ j, ‖η j‖ ≤ M) →
    (∀ j, levelDeriv (scDeriv U f) m (b j) (η j) = y j + F.incl m (z j)) →
    Tendsto y atTop (nhds 0) → (∃ M : ℝ, ∀ j, ‖z j‖ ≤ M) →
    ∃ (η₀ : E.lvl m) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (η ∘ φ) atTop (nhds η₀)

/-- Condition (3): `|[D₂f(b, 0) − D₂f(b, x)]h|_m ≤ ε|h|_m` uniformly for `b ∈ B ∩ U` small, `x ∈ X`
small on level `m + 1` (measured on level `m`), `h ∈ X_m`. -/
def UniformD2Estimate (E F : ScBanach) (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (Bs X : Submodule ℝ (E.lvl 0)) : Prop :=
  ∀ (m : ℕ), ∀ ε > 0, ∃ r > 0, ∀ (b x : E.lvl (m + 1)),
    E.toBase (m + 1) b ∈ Bs → E.toBase (m + 1) b ∈ U → ‖E.toBase (m + 1) b‖ < r →
    E.toBase (m + 1) x ∈ X → ‖E.incl m x‖ < r → E.toBase (m + 1) (b + x) ∈ U →
    ∀ h : E.lvl m, E.toBase m h ∈ X →
      ‖levelDeriv (scDeriv U f) m b h - levelDeriv (scDeriv U f) m (b + x) h‖ ≤ ε * ‖h‖

/-- Theorem 3.58 (basic germ criterion): under (1) constant-index sc-Fredholm linearizations at
smooth points, (2) a splitting `E = B ⊕ X` with `B ⊇ ker Df(0)` and the compactness property, and
(3) the uniform estimate on `D₂f`, the germ `f − f(0)` is conjugated near `0` to a basic germ. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (Bs X : Submodule ℝ (E.lvl 0)),
    IsRelOpenInQuadrant E C U → 0 ∈ U → IsScSmooth U f →
    ConstIndexFredholm E F U f →
    E.IsScSplitting Bs X → FiniteDimensional ℝ Bs →
    (∀ b ∈ Bs, ∀ x ∈ X, (b + x ∈ C ↔ b ∈ C)) →
    kerOf (scDeriv U f 0) ≤ Bs →
    CompactnessProp E F U f Bs X →
    UniformD2Estimate E F U f Bs X →
    ∃ U₀ : Set (E.lvl 0), IsRelOpenInQuadrant E C U₀ ∧ 0 ∈ U₀ ∧ U₀ ⊆ U ∧
      IsConjugateToBasicGerm U₀ (fun u => f u - f 0)

end RoundTrip.V3_89
