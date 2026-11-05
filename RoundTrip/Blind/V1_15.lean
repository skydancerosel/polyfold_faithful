import Polyfold
/-! Blind formalization of V1_15 (the text's §1.2, Proposition 1.16, p. 12).

Text: let `U` be relatively open in a partial quadrant of `E` and `F` an sc-Banach space.  An
`sc⁰` map `f : U → F` is `sc¹` iff (1) for every `m ≥ 1`, `f : U_m → F_{m−1}` is `C¹`, so that
`df : U_m → L(E_m, F_{m−1})` is continuous; and (2) for every `m ≥ 1` and `x ∈ U_m`, `df(x)`
extends to a bounded `Df(x) : E_{m−1} → F_{m−1}` with `(x, h) ↦ Df(x)h` continuous on
`U_m ⊕ E_{m−1}`.  In particular, at a smooth point `x ∈ U_∞` of an `sc¹` map, `Df(x) : E → F` is an
sc-operator.

Choices:
- Setting: `E F : ScBanach` (levels in `Type`, forced by the project's `ScBanach`); `C, U ⊆ E₀`
  with `IsRelOpenInQuadrant E C U` (checked with `#print`: `C` a partial quadrant, `U = O ∩ C`,
  `O` open).  `f : E₀ → F₀` is a total function; only its values on `U` matter.
- `sc⁰` is the project's `IsSc0` (checked: `f(U_m) ⊆ F_m` and `U_m → F_m` continuous for all `m`);
  `sc¹` is the project's `IsSc1` / `IsSc1With U f D` (checked with `#print`: `IsSc0`; for `x ∈ U₁`,
  `f ∘ ι₁ : E₁ → F₀` has derivative `D x ∘ ι₁` within `U₁`, `D x : E₀ →L F₀`; and the tangent map
  `(x, h) ↦ (f(x), D x h)` is `sc⁰` on `TU = U₁ × E₀ ⊆ E₁ × E₀`).  This is Definition 1.14.
- Indexing: the text's `m ≥ 1` is written `m + 1` with `m : ℕ`, so `U_m → F_{m−1}` becomes
  `U_{m+1} → F_m`.  "`f : U_{m+1} → F_m`" is `levelTo f (m+1) m : E_{m+1} → F_m`
  (`x ↦` the point of `F_m` over `f(x)`, via `Function.invFun`; it exists on `U_{m+1}` since `f` is
  `sc⁰`).  `U_{m+1}` is `E.lvlSet U (m+1) = ι⁻¹(U) ⊆ E_{m+1}`.
- (1) "`C¹`" is `ContDiffOn ℝ 1` on `U_{m+1}` (derivatives within `U_{m+1}`, which is locally a
  convex set with nonempty interior); "`df`" is `fderivWithin` on `U_{m+1}`, and its continuity
  (the "so that" clause) is stated as an extra conjunct.
- (2) is: there is a family `Dl m x : E_m →L F_m` (`x ∈ E_{m+1}`) with `Dl m x ∘ ι = df(x)` for
  `x ∈ U_{m+1}` (the extension; `ι : E_{m+1} → E_m`) and `(x, h) ↦ Dl m x h` continuous on
  `U_{m+1} × E_m`.  A family is the same as one extension per `x` (choice).
- B is the conjunction of the equivalence and the "in particular": for every derivative family
  `D` of the `sc¹` map `f` (`IsSc1With`) and every `x ∈ U ∩ E_∞` (given by its lift `x₁ ∈ E₁`),
  `D x₁ : E₀ → F₀` is an sc-operator (the project's `IsScOperator`, checked with `#print`: for
  every `m` there is `T_m : E_m →L F_m` with `ι_m ∘ T_m = D x₁ ∘ ι_m`).  `E_∞` is
  `E.smooth = ⋂ₘ ι_m(E_m)` (checked).
- Nothing looks false to me.
-/
namespace RoundTrip.V1_15
open Polyfold

/-- The map `E_a → F_b` induced by `f : E₀ → F₀`: the point of `F_b` over `f(x)` (junk if none). -/
noncomputable def levelTo {E F : ScBanach} (f : E.lvl 0 → F.lvl 0) (a b : ℕ) :
    E.lvl a → F.lvl b :=
  fun x => Function.invFun (F.toBase b) (f (E.toBase a x))

/-- Proposition 1.16: `sc¹` in terms of the levels, and `Df(x)` is an sc-operator at smooth
points. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0),
    IsRelOpenInQuadrant E C U → IsSc0 E F U f →
      (IsSc1 U f ↔
        -- (1) `f : U_{m+1} → F_m` is `C¹`, so `df : U_{m+1} → L(E_{m+1}, F_m)` is continuous
        (∀ m : ℕ,
          ContDiffOn ℝ 1 (levelTo f (m + 1) m) (E.lvlSet U (m + 1)) ∧
          ContinuousOn (fderivWithin ℝ (levelTo f (m + 1) m) (E.lvlSet U (m + 1)))
            (E.lvlSet U (m + 1))) ∧
        -- (2) `df(x)` extends to `Df(x) : E_m → F_m`, jointly continuous on `U_{m+1} × E_m`
        (∃ Dl : (m : ℕ) → E.lvl (m + 1) → E.lvl m →L[ℝ] F.lvl m,
          ∀ m : ℕ,
            (∀ x ∈ E.lvlSet U (m + 1),
              (Dl m x).comp (E.incl m) =
                fderivWithin ℝ (levelTo f (m + 1) m) (E.lvlSet U (m + 1)) x) ∧
            ContinuousOn (fun p : E.lvl (m + 1) × E.lvl m => Dl m p.1 p.2)
              (E.lvlSet U (m + 1) ×ˢ Set.univ))) ∧
      -- at a smooth point `x ∈ U_∞` of an `sc¹` map, `Df(x) : E → F` is an sc-operator
      (∀ D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0, IsSc1With U f D →
        ∀ x₁ : E.lvl 1, E.toBase 1 x₁ ∈ U → E.toBase 1 x₁ ∈ E.smooth →
          IsScOperator (D x₁))

end RoundTrip.V1_15
