import Polyfold
/-! Blind formalization of V13_49 (the Springer 2021 book, Part II, §13.5, Theorem 13.5.6,
p. 634; 2017: Theorem 13.9).

Text: `|X|` paracompact, bump functions, an auxiliary norm `N`.  (1) For smooth `w ≠ 0` over
`x` and `U(x)` with the natural action there is an atomic `Λ` with
`dom-supp Λ ⊆ π⁻¹(U(x))` and `Λ(g ∗ w) > 0` for all `g`.  (2) For an sc⁺-section `s` on `U(x)`
and `ε > 0` there is an atomic `Λ` supported in `π⁻¹(U(x))` with `N(Λ)(y) ≤ N(s(x)) + ε`,
whose local structure near `x` contains `s` with positive weight.

Choices:
- Setting: universe 0; the strong bundle `P : W → X` over the ep-groupoid `X` is the project's
  `SEP.{0}` (`A.W`, `A.Obj`, `A.P`, `A.X`, the strong bundle `A.B`, the bundle over the
  ep-groupoid `A.E`), as in the other blind files on strong bundles over ep-groupoids.
- Hypotheses: `A.X.HasParacompactOrbitSpace` (`#print`ed: `|X|` paracompact);
  "bump functions": `A.X.AdmitsBumpFunctions` (Definition 12.3.1, `#print`ed: for every `x`
  and saturated open `U ∋ x` an sc-smooth invariant `f ≢ 0` with `supp f ⊆ U`);
  "an auxiliary norm `N`": `N : W_{0,1} → ℝ` (`A.B.One → ℝ`) with `A.E.IsAuxNorm N`
  (Definition 8.3.5).  `N` is quantified universally; it enters only (2).
- `π⁻¹(U(x))`: `π : X → |X|` the orbit map, so `π⁻¹(U(x))` is read as `π⁻¹(π(U(x)))`, the
  saturation of `U(x)` (`GroupoidStr.saturation`, `#print`ed `π⁻¹(π(A))`).  "Supported in" in
  (2) is read as `dom-supp Λ ⊆ π⁻¹(π(U(x)))`.
- "atomic": the project's `SBLocalization.IsAtomic` (`#print`ed: `IsScPlusMultisection A Λ ∧
  ∃ D : AtomicData A, D.IsRelated Λ`, Definition 13.5.1 with `U(x)` the domain of a natural
  representation); `dom-supp`: `domSupp` (`#print`ed: closure of the `x` over which `Λ` charges
  a nonzero point, Definition 13.2.2); `N(Λ)(y)`: `pointwiseNorm N Λ y` (Definition 13.2.3, a
  supremum); `N(s(x))`: `normW N (s x)` (`N` read on `W`, `0` off `W_{0,1}`).
- (1): `w` "smooth": `w ∈ W_∞`, the smooth points of the M-polyfold `W` (`A.B.toMPolyfold0`,
  `smoothSet`); `w ≠ 0`: `w` is not the zero `0_x` of its fibre `W_x` (`fiberZero`);
  "`U(x)` with the natural action": any `U : A.X.NatNbhd x` (open `U(x) ∋ x` inside the domain of
  a natural representation, invariant under it).  `g ∗ w = μ(g, w)` for `g ∈ G_x` a morphism
  `x → x` (`fibAct g.val w`); "for all `g`": all `g ∈ G_x`.
- (2): "an sc⁺-section `s` on `U(x)`": `s : X → W` with `IsScPlusSectionOn A s U.U` for a
  `U : NatNbhd x` as in (1) (values off `U(x)` irrelevant).  `N(Λ)(y) ≤ N(s(x)) + ε` for all
  objects `y`.  "whose local structure near `x` contains `s` with positive weight": `Λ` is related
  to atomic data `D` at the point `D.x = x` (the data of Definition 13.5.1) one of whose sections
  `s_i` agrees with `s` on an open neighbourhood `O` of `x`, and `Λ(s(y)) > 0` for `y ∈ O`.  This
  is my reading of the summary's phrase; the atomic `Λ` of (2) is asked to be atomic at `x`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V13_49
open Polyfold Polyfold.SBLocalization

/-- Theorem 13.5.6: atomic sc⁺-multisections through a given smooth vector, and through a given
local sc⁺-section with norm control. -/
def B : Prop :=
  ∀ A : SEP.{0}, A.X.HasParacompactOrbitSpace → A.X.AdmitsBumpFunctions →
  ∀ N : A.B.One → ℝ, A.E.IsAuxNorm N →
    -- (1)
    (∀ (x : A.Obj) (w : A.W), A.P w = x → w ∈ A.B.toMPolyfold0.smoothSet →
      w ≠ fiberZero A.P x → ∀ U : A.X.NatNbhd x,
        ∃ Λ : A.W → ℚ≥0, SBLocalization.IsAtomic A Λ ∧
          domSupp Λ ⊆ A.X.saturation U.U ∧
          ∀ g : A.X.Isotropy x, 0 < Λ (fibAct g.val w)) ∧
    -- (2)
    (∀ (x : A.Obj) (U : A.X.NatNbhd x) (s : A.Obj → A.W), IsScPlusSectionOn A s U.U →
      ∀ ε : ℝ, 0 < ε →
        ∃ Λ : A.W → ℚ≥0, SBLocalization.IsAtomic A Λ ∧
          domSupp Λ ⊆ A.X.saturation U.U ∧
          (∀ y : A.Obj, pointwiseNorm N Λ y ≤ normW N (s x) + ε) ∧
          ∃ D : AtomicData A, D.x = x ∧ D.IsRelated Λ ∧
            ∃ (i : D.I) (O : Set A.Obj), IsOpen O ∧ x ∈ O ∧
              ∀ y ∈ O, D.s i y = s y ∧ 0 < Λ (s y))

end RoundTrip.V13_49
