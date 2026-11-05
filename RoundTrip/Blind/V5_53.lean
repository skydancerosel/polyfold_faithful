import Polyfold
/-! Blind formalization of V5_53 (the text's §5.4.2, Proposition 5.35, p. 194, and §5.3, p. 173).

Text: if `E₀` is a Hilbert space, `(O, C, E)` has the sc-bump function property (proof:
`β(‖x‖²)`, scaling, translating, composing with the retraction).  §5.3: "This [`X` admits
sc-smooth bump functions] is, for example, the case if `X` is built on sc-Hilbert spaces."

Choices:
- B is the conjunction of Proposition 5.35 and the §5.3 sentence.
- (Prop. 5.35) for every local model `M = (O, C, E)` (the project's `LocalModel`; levels of `E` in
  `Type`).  "`E₀` is a Hilbert space": `E₀` is complete (built into `ScBanach`) and its GIVEN norm
  comes from an inner product: `IsHilbertNormB`, a symmetric continuous bilinear form `b` with
  `b(x, x) = ‖x‖²` (equivalently, a Mathlib `InnerProductSpace` structure inducing the norm).  I
  did NOT read it as "`E₀` admits an equivalent Hilbert norm" (a weaker hypothesis, giving a
  stronger claim; the proof works the same way with that norm).
- "the sc-bump function property": Definition 5.33 read LITERALLY, `HasBumpPropertyB` (the same
  definition as in `RoundTrip/Blind/V5_51.lean`: for every `x ∈ O` and open `U = O ∩ W ∋ x` with
  `cl_E(U) ⊆ O`, an sc-smooth `f : O → ℝ` — the project's `IsScSmoothRetractMap … realSc univ univ`,
  checked — not identically zero on `O`, with `cl_O{f ≠ 0} ⊆ U`).  The proof's `β(‖·‖²)` gives
  `f(x) ≠ 0`, which is more; the text's claim is the property.  I did not use the project's
  `HasBumpProperty` (`f(x) ≠ 0`).
- (§5.3) "`X` is built on sc-Hilbert spaces": `X : Type` (universe 0, as asked), Hausdorff
  paracompact, with `PX : MPolyfold X`, has an atlas (one equivalent to `PX.atlas`, `MAtlas.Equiv`)
  every chart of which has a local model `(O, C, E)` with `E` an sc-Hilbert space: EVERY level
  `E_m` with a Hilbert norm (`IsScHilbertB`).  "admits sc-smooth bump functions": Definition 5.9
  read literally ("`f ≠ 0`" = not identically zero), the project's `PX.AdmitsBumpFunctionsWeak`
  (checked with `#print`: for every `x` and open `U ∋ x` an sc-smooth `f : X → ℝ`, `f ≠ 0`,
  `tsupport f ⊆ U`), as in `RoundTrip/Blind/V5_16.lean` / `V5_45.lean`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_53
open Polyfold

/-- The norm of `V` comes from an inner product: `‖x‖² = b(x, x)` for a symmetric continuous
bilinear form `b`. -/
def IsHilbertNormB (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop :=
  ∃ b : V →L[ℝ] V →L[ℝ] ℝ, (∀ x y, b x y = b y x) ∧ ∀ x, b x x = ‖x‖ ^ 2

/-- An sc-Hilbert space: every level `E_m` is a Hilbert space. -/
def IsScHilbertB (E : ScBanach) : Prop :=
  ∀ m, IsHilbertNormB (E.lvl m)

/-- **Definition 5.33** (literal): the sc-smooth bump function property of `(O, C, E)`. -/
def HasBumpPropertyB (M : LocalModel) : Prop :=
  ∀ x ∈ M.O, ∀ U : Set (M.E.lvl 0), U ⊆ M.O → x ∈ U → (∃ W, IsOpen W ∧ U = M.O ∩ W) →
    closure U ⊆ M.O →
      ∃ f : M.E.lvl 0 → ℝ,
        IsScSmoothRetractMap M.E M.C M.O realSc Set.univ Set.univ f ∧
        (∃ y ∈ M.O, f y ≠ 0) ∧ closure (M.O ∩ Function.support f) ∩ M.O ⊆ U

/-- Proposition 5.35: a local model on an sc-Banach space with Hilbert `E₀` has the sc-smooth bump
function property; and an M-polyfold built on sc-Hilbert spaces admits sc-smooth bump
functions. -/
def B : Prop :=
  (∀ M : LocalModel, IsHilbertNormB (M.E.lvl 0) → HasBumpPropertyB M) ∧
  (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    (∃ A : MAtlas X, A.Equiv PX.atlas ∧ ∀ φ ∈ A.charts, IsScHilbertB φ.model.E) →
      PX.AdmitsBumpFunctionsWeak)

end RoundTrip.V5_53
