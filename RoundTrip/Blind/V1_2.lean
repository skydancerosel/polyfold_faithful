import Polyfold
/-! Blind formalization of V1_2 (the text's §1.1, Definition 1.3, p. 7). Choices:
- This item is a definition.  Setting: sc-Banach spaces `E F : ScBanach` (the project's
  sc-Banach spaces, levels in `Type`; that `ScBanach` is the text's notion is item V1_1).  Only its
  bare structure is used: the levels `E.lvl m` and the composite inclusions `E.toBase m : E_m → E₀`
  (checked with `#print`/`rfl`: `toBase (m+1) = toBase m ∘ incl m`), which present `E_m ⊆ E₀`.
- The text's notions, defined here from that structure:
  * `IsScOperatorText T` for a linear map `T : E₀ → F₀` (not assumed continuous): for every `m`
    there is a continuous `T_m : E_m → F_m` with `ι_m ∘ T_m = T ∘ ι_m`.  This says
    `T(E_m) ⊆ F_m`, and `T_m` is then the induced map (unique, the inclusions being injective),
    required continuous.
  * `IsScIsoText T`: a bijective sc-operator whose inverse (a linear map `S` with `S ∘ T = id`,
    `T ∘ S = id`) is an sc-operator.
- B states the definition as a characterization of the project's notions: the predicate
  `IsScOperator` (on continuous base maps), the structure `ScOperator` (an sc-operator is the
  level-0 map of an `ScOperator`) and the structure `ScIso` (a linear sc-isomorphism is the
  level-0 map of an `ScIso`).  The definition asserts no further property.
-/
namespace RoundTrip.V1_2
open Polyfold

/-- **Definition 1.3**: `T : E → F` is an sc-operator: `T(E_m) ⊆ F_m` and the induced map
`E_m → F_m` is continuous, for every `m`. -/
def IsScOperatorText {E F : ScBanach} (T : E.lvl 0 →ₗ[ℝ] F.lvl 0) : Prop :=
  ∀ m : ℕ, ∃ Tm : E.lvl m → F.lvl m,
    (∀ x, F.toBase m (Tm x) = T (E.toBase m x)) ∧ Continuous Tm

/-- **Definition 1.3**: a linear sc-isomorphism is a bijective sc-operator whose inverse is an
sc-operator. -/
def IsScIsoText {E F : ScBanach} (T : E.lvl 0 →ₗ[ℝ] F.lvl 0) : Prop :=
  IsScOperatorText T ∧ Function.Bijective T ∧
    ∃ S : F.lvl 0 →ₗ[ℝ] E.lvl 0,
      Function.LeftInverse S T ∧ Function.RightInverse S T ∧ IsScOperatorText S

/-- Definition 1.3: the project's sc-operators and sc-isomorphisms are the text's. -/
def B : Prop :=
  (∀ (E F : ScBanach) (T₀ : E.lvl 0 →L[ℝ] F.lvl 0),
    IsScOperator T₀ ↔ IsScOperatorText (T₀ : E.lvl 0 →ₗ[ℝ] F.lvl 0)) ∧
  (∀ (E F : ScBanach) (T : E.lvl 0 →ₗ[ℝ] F.lvl 0),
    (∃ T' : ScOperator E F, ∀ x, T'.lvl 0 x = T x) ↔ IsScOperatorText T) ∧
  (∀ (E F : ScBanach) (T : E.lvl 0 →ₗ[ℝ] F.lvl 0),
    (∃ T' : ScIso E F, ∀ x, T'.lvl 0 x = T x) ↔ IsScIsoText T)

end RoundTrip.V1_2
