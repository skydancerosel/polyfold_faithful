import Polyfold
/-! Blind formalization of V1_14 (the text's §1.1, Definition 1.15, p. 11).

Text: "Inductively, an `sc⁰` map `f` is `sc²` if it is `sc¹` and `Tf : TU → TV` is `sc¹`; then
`T²f = T(Tf)` is `sc⁰`, and `f` is `sc³` if `T²f` is `sc¹`, and so on.  `f` is `sc^∞`, or
sc-smooth, if it is `sc^k` for all `k ≥ 0`."

Choices:
- Setting: `E F : ScBanach` (levels in `Type`, forced by the project's `ScBanach`); tuples
  `(U, C, E)`, `(V, C', F)` (`IsRelOpenInQuadrant`, checked with `#print`) and a total map
  `f : E₀ → F₀` with `f(U) ⊆ V`.
- Prelude (same as my `RoundTrip/Blind/V1_13.lean`, Definition 1.14 written out): `tanSet`
  (`TU = U¹ ⊕ E`), `tanMap f D` (`Tf(x, h) = (f(x), Df(x)h)`), `Sc1With U f D` (`sc⁰` = the
  project's `IsSc0`, checked; differentiability of `f ∘ ι₁` within `U₁` with derivative
  `Df(x) ∘ ι₁`; `Tf` `sc⁰` on `TU`).  `TE = E¹ ⊕ E` is `E.shift.prod E`.
- The definition (written out by me): `SckB 0 = sc⁰`; `SckB (k+1) f` iff `f` is `sc¹` with some
  derivative family `D` and `Tf = tanMap f D` is `SckB k` on `TU` (into `TF`).  Unwinding, `sc²` =
  `sc¹` and `Tf` `sc¹`; `sc³` = additionally `T²f` `sc¹`, as in the text.  The text's recursion
  ("`f` is `sc^{k+1}` if it is `sc^k` and `T^k f` is `sc¹`") and mine agree because `Df(x)` is
  unique for `x ∈ U₁` (`U₁` is relatively open in a partial quadrant of `E₁`, and `E₁` is dense in
  `E₀`), and `TU` is again a tuple (Definition 1.13).  `ScSmoothB` = `SckB k` for all `k`.
- The one property asserted in the text, "then `T²f = T(Tf)` is `sc⁰`", is B: if `f` is `sc²`, then
  for ANY derivative families `D` of `f` and `D'` of `Tf = tanMap f D` (on `TU`), the second
  tangent map `tanMap (tanMap f D) D'` is `sc⁰` on `T(TU)` (into `T(TF)`).  Quantifying over all
  derivative families renders the definite article in "`T²f`"; with an existential it would be
  part of the definition.  "And so on" is read as continuing the definition, which `SckB` does
  for every `k`.
- Nothing looks false to me.
-/
namespace RoundTrip.V1_14
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
  IsSc0 E F U f ∧
  (∀ x ∈ E.lvlSet U 1,
    HasFDerivWithinAt (f ∘ E.toBase 1) ((D x).comp (E.toBase 1)) (E.lvlSet U 1) x) ∧
  IsSc0 (E.shift.prod E) (F.shift.prod F) (tanSet E U) (tanMap f D)

/-- Definition 1.15: `f : U → F` is `sc^k` (`sc⁰`; `sc^{k+1}`: `sc¹` with `Tf : TU → TF`
`sc^k`). -/
def SckB : ℕ → (E F : ScBanach) → Set (E.lvl 0) → (E.lvl 0 → F.lvl 0) → Prop
  | 0, E, F, U, f => IsSc0 E F U f
  | k + 1, E, F, U, f => ∃ D, Sc1With U f D ∧
      SckB k (E.shift.prod E) (F.shift.prod F) (tanSet E U) (tanMap f D)

/-- Definition 1.15: `f` is `sc^∞` (sc-smooth) if it is `sc^k` for every `k`. -/
def ScSmoothB {E F : ScBanach} (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0) : Prop :=
  ∀ k : ℕ, SckB k E F U f

/-- If `f` is `sc²`, then `T²f = T(Tf)` is `sc⁰` (for any choice of the derivatives). -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (C' V : Set (F.lvl 0)) (f : E.lvl 0 → F.lvl 0),
    IsRelOpenInQuadrant E C U → IsRelOpenInQuadrant F C' V → Set.MapsTo f U V →
    SckB 2 E F U f →
      ∀ (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0)
        (D' : (E.shift.prod E).lvl 1 → (E.shift.prod E).lvl 0 →L[ℝ] (F.shift.prod F).lvl 0),
        Sc1With U f D → Sc1With (tanSet E U) (tanMap f D) D' →
          IsSc0 ((E.shift.prod E).shift.prod (E.shift.prod E))
            ((F.shift.prod F).shift.prod (F.shift.prod F))
            (tanSet (E.shift.prod E) (tanSet E U)) (tanMap (tanMap f D) D')

end RoundTrip.V1_14
