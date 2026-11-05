import Polyfold
/-! Blind formalization of V2_5 (the text's §2.1, Proposition 2.6, p. 20).

Text: let `f : O → O'` (a map between sc-smooth retracts `(O, C, E)` and `(O', C', E')`) and
`r : U → U`, `s : V → V` two retractions onto `O`.  (1) `f ∘ r` is sc-smooth iff `f ∘ s` is.
(2) If so, `T(f ∘ r) = T(f ∘ s)` on `TO`.  (3) `T(f ∘ r)` maps `TO` into `TO'`.

Choices:
- Setting: `E E' : ScBanach` (levels in `Type`, forced by `ScBanach`), `C, O ⊆ E₀`,
  `C', O' ⊆ E'₀`.  `(O', C', E')` is an sc-smooth retract (`IsScRetract`, checked with `#print`:
  `O' = r'(U')` for some `ScRetraction E' C'`); this is presupposed by "`f : O → O'`" and by `TO'`.
  `(O, C, E)` is a retract because `r` exists.
- "retractions onto `O`": `r s : ScRetraction E C` (checked: `U` relatively open in the partial
  quadrant `C`, `r` sc-smooth on `U`, `r ∘ r = r` on `U`) with `r(U) = s(V) = O` (`.retract`,
  checked: the image of the domain).  Both live on the same `C`, the partial quadrant of the
  retract `(O, C, E)`.
- `f : O → O'` is a total map `E₀ → E'₀` with `f(O) ⊆ O'` (only its values on `O` matter).
  "`f ∘ r` is sc-smooth": `IsScSmooth r.U (f ∘ r)` (Definition 1.15, as a map `U → E'`).
- `T(·)`: the project's `Polyfold.tangentMap` (Definition 1.14 (3): `Tg(x, h) = (g(x), Dg(x)h)`
  with the derivative family chosen from the definition of sc¹; unique at the points of `U₁`).
- `TO = Tr(TU)` (Definition 2.5): for a retraction `ρ` onto `O`, the image of `TU` under `Tρ`
  (the project's `ScRetraction.tangent`, checked with `#print`).  The text's `TO` does not depend
  on `ρ` (Proposition 2.4); to avoid relying on that, (2) and (3) are asserted on `Tρ(TU_ρ)` for
  EVERY retraction `ρ` onto `O`, and in (3) into `Tρ'(TU_ρ')` for EVERY retraction `ρ'` onto `O'`.
- (2) and (3) are asserted under the hypothesis of (2), "if so" (`f ∘ r` sc-smooth); without it
  `T(f ∘ r)` is not defined in the text.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_5
open Polyfold

/-- Proposition 2.6: sc-smoothness of `f ∘ r` and the tangent map `T(f ∘ r)` on `TO` do not depend
on the retraction `r` onto `O`, and `T(f ∘ r)` maps `TO` into `TO'`. -/
def B : Prop :=
  ∀ (E E' : ScBanach) (C O : Set (E.lvl 0)) (C' O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0),
    IsScRetract E' C' O' → Set.MapsTo f O O' →
    ∀ (r s : ScRetraction E C), r.retract = O → s.retract = O →
      -- (1)
      (IsScSmooth r.U (f ∘ r.toFun) ↔ IsScSmooth s.U (f ∘ s.toFun)) ∧
      (IsScSmooth r.U (f ∘ r.toFun) →
        -- (2) `T(f ∘ r) = T(f ∘ s)` on `TO`
        (∀ ρ : ScRetraction E C, ρ.retract = O →
          ∀ p ∈ Polyfold.tangentMap ρ.U ρ.toFun '' E.tangentSet ρ.U,
            Polyfold.tangentMap r.U (f ∘ r.toFun) p = Polyfold.tangentMap s.U (f ∘ s.toFun) p) ∧
        -- (3) `T(f ∘ r)` maps `TO` into `TO'`
        (∀ ρ : ScRetraction E C, ρ.retract = O → ∀ ρ' : ScRetraction E' C', ρ'.retract = O' →
          Set.MapsTo (Polyfold.tangentMap r.U (f ∘ r.toFun))
            (Polyfold.tangentMap ρ.U ρ.toFun '' E.tangentSet ρ.U)
            (Polyfold.tangentMap ρ'.U ρ'.toFun '' E'.tangentSet ρ'.U)))

end RoundTrip.V2_5
