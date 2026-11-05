import Polyfold
/-! Blind formalization of V1_13 (the text's §1.1, Definition 1.14, pp. 10–11).

Text: `f : U → U'` is `sc¹` if (1) `f` is `sc⁰`; (2) for every `x ∈ U₁` there is a bounded linear
`Df(x) : E₀ → F₀` with `|f(x+h) − f(x) − Df(x)h|₀ / |h|₁ → 0` as `|h|₁ → 0`, `h ∈ E₁`,
`x + h ∈ U₁`; (3) the tangent map `Tf : TU → TU'`, `Tf(x, h) = (f(x), Df(x)h)`, is `sc⁰`.
"In general `x ↦ Df(x)` is not continuous into `L(E₀, F₀)` with the operator norm, but it is with
the compact-open topology; the `sc¹` maps between finite-dimensional spaces are the `C¹` maps."

Choices:
- Setting: `E F : ScBanach` (levels in `Type`, forced by the project's `ScBanach`).  The domain
  is a tuple `(U, C, E)`: `IsRelOpenInQuadrant E C U` (checked with `#print`: `C` the preimage of
  `[0,∞)ⁿ ⊕ W` under an sc-isomorphism `E ≅ ℝⁿ ⊕ W`, `U = O ∩ C` with `O` open).  `f : E₀ → F₀` is
  a total function; only its values on `U` matter.  The target tuple `(U', C', F)` plays no role in
  the definition beyond `f(U) ⊆ U'` (then `Tf(TU) ⊆ TU'` automatically, and continuity into `TU'`
  is continuity into `TF`), so the definition is stated for maps `U → F`.
- `sc⁰` (Definition 1.12) is the project's `IsSc0 E F U f` (checked with `#print`: for every `m`,
  `f(U_m) ⊆ F_m` and the induced map `U_m → F_m` is continuous).
- The definition (written out by me): `Sc1With U f D` for a family `D x = Df(x) : E₀ →L F₀`
  indexed by `x ∈ E₁` (values off `U₁` are irrelevant): (1) `IsSc0`; (2) at every `x ∈ U₁`,
  `f ∘ ι₁ : E₁ → F₀` has derivative `Df(x) ∘ ι₁` within `U₁` (Mathlib's `HasFDerivWithinAt`, which
  is exactly the quotient condition with `|h|₁` in the denominator, `x + h ∈ U₁`); (3) the tangent
  map `tanMap f D (x, h) = (f(x), Df(x)h)` on `(TE)₀ = E₁ × E₀` is `sc⁰` from
  `TU = {(x, h) | x ∈ U₁}` (`TE = E¹ ⊕ E`, `TF = F¹ ⊕ F`, Definition 1.13; `f(x) ∈ F₁` is lifted
  to `F₁` by `Function.invFun`).  `Sc1 U f := ∃ D, Sc1With U f D` (choosing one `Df(x)` for each
  `x` is the same as choosing a family).
- The three remarks are B (conjunction):
  (a) "in general not continuous for the operator norm": there EXIST a tuple `(U, C, E)`, `F` and
      an `sc¹` map `f` such that for EVERY derivative family `D` of `f` the map
      `x ↦ Df(x) : U₁ → L(E₀, F₀)` (`U₁` with the `E₁`-topology; Mathlib's topology on `→L` is the
      operator-norm topology) is not continuous.  (`D` is in fact unique on `U₁`, but quantifying
      over all `D` makes the statement independent of that.)
  (b) "but it is with the compact-open topology": for every `sc¹` `f` and every derivative family
      `D`, `x ↦ Df(x)`, viewed in `C(E₀, F₀)` with Mathlib's (compact-open) topology, is
      continuous on `U₁` (`E₁`-topology).
  (c) "the `sc¹` maps between finite-dimensional spaces are the `C¹` maps": for sc-Banach spaces
      `E`, `F` with `E₀`, `F₀` finite-dimensional (such spaces carry only the constant
      sc-structure up to isomorphism, so I do not require `E = ScBanach.const _`) and a tuple
      `(U, C, E)`, `f` is `sc¹` on `U` iff `ContDiffOn ℝ 1 f U` (`C¹` on the relatively open subset
      `U` of a quadrant, with derivatives within `U`).
- Nothing looks false to me.
-/
namespace RoundTrip.V1_13
open Polyfold

/-- The map `E_a → F_b` induced by `f : E₀ → F₀`: the point of `F_b` over `f(x)` (junk if none). -/
noncomputable def levelTo {E F : ScBanach} (f : E.lvl 0 → F.lvl 0) (a b : ℕ) :
    E.lvl a → F.lvl b :=
  fun x => Function.invFun (F.toBase b) (f (E.toBase a x))

/-- `TU = U¹ ⊕ E ⊆ (TE)₀ = E₁ × E₀`: the pairs `(x, h)` with `x ∈ U ∩ E₁`. -/
def tanSet (E : ScBanach) (U : Set (E.lvl 0)) : Set ((E.shift.prod E).lvl 0) :=
  {p | E.toBase 1 p.1 ∈ U}

/-- The tangent map `Tf(x, h) = (f(x), Df(x)h) : (TE)₀ → (TF)₀` for a derivative family `D`. -/
noncomputable def tanMap {E F : ScBanach} (f : E.lvl 0 → F.lvl 0)
    (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0) : (E.shift.prod E).lvl 0 → (F.shift.prod F).lvl 0 :=
  fun p => (levelTo f 1 1 p.1, D p.1 p.2)

/-- Definition 1.14: `f` is `sc¹` on `U` with derivative family `D` (`D x = Df(x)`, `x ∈ U₁`). -/
def Sc1With {E F : ScBanach} (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0) : Prop :=
  -- (1) `f` is `sc⁰`
  IsSc0 E F U f ∧
  -- (2) `|f(x+h) − f(x) − Df(x)h|₀ / |h|₁ → 0` for `h ∈ E₁`, `x + h ∈ U₁`
  (∀ x ∈ E.lvlSet U 1,
    HasFDerivWithinAt (f ∘ E.toBase 1) ((D x).comp (E.toBase 1)) (E.lvlSet U 1) x) ∧
  -- (3) `Tf : TU → TF` is `sc⁰`
  IsSc0 (E.shift.prod E) (F.shift.prod F) (tanSet E U) (tanMap f D)

/-- Definition 1.14: `f : U → F` is `sc¹`. -/
def Sc1 {E F : ScBanach} (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0) : Prop :=
  ∃ D, Sc1With U f D

/-- The remarks after Definition 1.14: `x ↦ Df(x)` need not be norm-continuous, is continuous for
the compact-open topology, and in finite dimensions `sc¹ = C¹`. -/
def B : Prop :=
  -- (a) in general not continuous into `L(E₀, F₀)` with the operator norm
  (∃ (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0),
    IsRelOpenInQuadrant E C U ∧ Sc1 U f ∧
      ∀ D, Sc1With U f D → ¬ ContinuousOn D (E.lvlSet U 1)) ∧
  -- (b) continuous with the compact-open topology
  (∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0),
    IsRelOpenInQuadrant E C U → Sc1With U f D →
      ContinuousOn (fun x => ((D x : E.lvl 0 →L[ℝ] F.lvl 0) : C(E.lvl 0, F.lvl 0)))
        (E.lvlSet U 1)) ∧
  -- (c) between finite-dimensional spaces, `sc¹` = `C¹`
  (∀ (E F : ScBanach), FiniteDimensional ℝ (E.lvl 0) → FiniteDimensional ℝ (F.lvl 0) →
    ∀ (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0), IsRelOpenInQuadrant E C U →
      (Sc1 U f ↔ ContDiffOn ℝ 1 f U))

end RoundTrip.V1_13
