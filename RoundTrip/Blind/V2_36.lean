import Polyfold
/-! Blind formalization of V2_36 (the text's §2.3, before Theorem 2.31, p. 35).

Text: a retract `(O, C, E)` is an M-polyfold, and `d_O(x) = min d_{C'}(φ(x))` over germs of
sc-diffeomorphisms `φ : (O, x) → (O', φ(x))` into retracts.

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `(O, C, E)` an sc-smooth
  retract (`IsScRetract`, checked with `#print`).  `O` is the subtype `↥O` of `E₀` with the
  subspace topology (Hausdorff and paracompact instances are found automatically: it is a metric
  space).
- "`O` is an M-polyfold": there is an M-polyfold structure `P : MPolyfold ↥O` (Definition 2.13)
  of which the identity chart `id : O → O` with model `(O, C, E)` is a chart (`P.IsChart`, i.e.
  compatible with `P`'s atlas, checked with `#print`).  The identity chart is the project's
  `LocalModel.selfChart` (checked with `#print`: `Subtype.val`, source `univ`, target `O`, model
  `(O, C, E)`); it needs `O ≠ ∅`, so the condition is "for every proof of nonemptiness" (for
  `O = ∅` the claim is just the existence of some structure).
- `d_O`: the degeneracy index (Definition 2.22) of THAT M-polyfold, the project's
  `MPolyfold.degIndex` (checked: the `sInf` of `d_{C'}(ψ(x))` over the charts `ψ` compatible with
  the atlas, around `x`) of `LocalModel.toMPolyfold` (checked with `#print`: the structure on
  `↥O` whose atlas is the single identity chart), as in `RoundTrip/Blind/V2_37.lean`.
- Germs (my `IsGermDiffeoB`, as in `RoundTrip/Blind/V2_35.lean`): open `V ∋ x` in `E₀`,
  `V' ∋ φ(x)` in `E'₀`, `φ` sc-smooth between the retracts `(O ∩ V, C, E)`, `(O' ∩ V', C', E')`
  (the project's `IsScSmoothRetractMap`, Definition 2.7, checked) with sc-smooth inverse `ψ`.
  The target retracts `(O', C', E')` range over all sc-smooth retracts, `E' : ScBanach`.
- `d_{C'}` is the project's `degIndex E' C'` (Definition 1.23, checked: the number of vanishing
  half-line coordinates for a chosen presentation of the partial quadrant `C'`).
- "`d_O(x) = min …`": `d_O(x)` is the least element (`IsLeast`) of the set of the values
  `d_{C'}(φ(x))`, so that the minimum is attained (no `sInf` junk).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_36
open Polyfold

/-- A germ of sc-diffeomorphisms `f : (O, x) → (O', f(x))` between the retracts `(O, C, E)` and
`(O', C', E')`, represented on the open neighbourhoods `O ∩ V` of `x` and `O' ∩ V'` of `f(x)`,
with sc-smooth inverse `g`. -/
def IsGermDiffeoB {E E' : ScBanach} (C O : Set (E.lvl 0)) (C' O' : Set (E'.lvl 0))
    (x : E.lvl 0) (f : E.lvl 0 → E'.lvl 0) (g : E'.lvl 0 → E.lvl 0)
    (V : Set (E.lvl 0)) (V' : Set (E'.lvl 0)) : Prop :=
  IsOpen V ∧ IsOpen V' ∧ x ∈ V ∧ f x ∈ V' ∧
    IsScSmoothRetractMap E C (O ∩ V) E' C' (O' ∩ V') f ∧
    IsScSmoothRetractMap E' C' (O' ∩ V') E C (O ∩ V) g ∧
    (∀ z ∈ O ∩ V, g (f z) = z) ∧ (∀ z ∈ O' ∩ V', f (g z) = z)

/-- The values `d_{C'}(φ(x))` over all germs of sc-diffeomorphisms `φ : (O, x) → (O', φ(x))`
into sc-smooth retracts `(O', C', E')`. -/
def germDegValues {E : ScBanach} (C O : Set (E.lvl 0)) (x : E.lvl 0) : Set ℕ :=
  {d | ∃ (E' : ScBanach) (C' O' : Set (E'.lvl 0)), IsScRetract E' C' O' ∧
    ∃ (f : E.lvl 0 → E'.lvl 0) (g : E'.lvl 0 → E.lvl 0) (V : Set (E.lvl 0))
      (V' : Set (E'.lvl 0)), IsGermDiffeoB C O C' O' x f g V V' ∧ d = degIndex E' C' (f x)}

/-- A retract is an M-polyfold (with the identity chart), and its degeneracy index at `x` is the
minimum of `d_{C'}(φ(x))` over germs of sc-diffeomorphisms `φ` from `(O, x)` into retracts. -/
def B : Prop :=
  ∀ (E : ScBanach) (C O : Set (E.lvl 0)) (hO : IsScRetract E C O),
    -- `O` is an M-polyfold, with the identity chart
    (∃ P : MPolyfold ↥O,
      ∀ hne : O.Nonempty, P.IsChart ((LocalModel.mk E C O hO).selfChart hne)) ∧
    -- `d_O(x) = min d_{C'}(φ(x))` over germs `φ : (O, x) → (O', φ(x))`
    (∀ (hne : O.Nonempty) (x : ↥O),
      IsLeast (germDegValues C O (x : E.lvl 0))
        (((LocalModel.mk E C O hO).toMPolyfold hne).degIndex x))

end RoundTrip.V2_36
