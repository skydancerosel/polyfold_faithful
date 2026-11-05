import Polyfold
/-! Blind formalization of V1_17 (the text's §1.2, Proposition 1.18, p. 13).

Text: let `U` and `V` be relatively open subsets of partial quadrants in sc-Banach spaces.  If
`f : U → V` is `sc^k`, then for every `m ≥ 0` the map `f : U_{m+k} → V_m` is of class `C^k`;
moreover `f : U_{m+l} → V_m` is `C^l` for every `0 ≤ l ≤ k`.

Choices:
- Setting: `E F : ScBanach` (levels in `Type`, forced by `ScBanach`); `U ⊆ C ⊆ E₀` and
  `V ⊆ C' ⊆ F₀` with `C`, `C'` partial quadrants and `U`, `V` relatively open in them
  (`IsRelOpenInQuadrant`, checked with `#print`: `C = T⁻¹([0,∞)ⁿ ⊕ W)` for an sc-isomorphism `T`,
  and `U = O ∩ C` with `O` open).  `f : E₀ → F₀` is a total function with `f(U) ⊆ V`; only its
  values on `U` matter.  `k : ℕ` (finite `k`, as the text's `sc^k`).
- `sc^k` is the project's `IsSck k E F U f` (checked with `#print`/`rfl`: `sc⁰` for `k = 0`, and
  `sc^{k+1}` = `sc¹` with `Tf : TU → TF` `sc^k`; `sc¹` = `IsSc1With` for some derivative family:
  `sc⁰`, the level-1 differentiability condition with a bounded `Df(x) : E₀ → F₀`, and `Tf` `sc⁰`).
- "`f : U_{a} → V_m`" (`a = m + l ≥ m`) is the map `levelTo f a m : E_a → F_m`,
  `x ↦ the point of F_m lying over f(x)` (via `Function.invFun` of the injective inclusion
  `F_m → F₀`; a junk value where no such point exists, which does not happen on `U_a`).
  `U_a` is `E.lvlSet U a = U ∩ E_a ⊆ E_a`, `V_m` is `F.lvlSet V m`.
- "of class `C^l`" on the relatively open subset `U_{m+l}` of a partial quadrant of `E_{m+l}` is
  Mathlib's `ContDiffOn ℝ l` on `U_{m+l}` (derivatives within the set; this set is locally convex
  with nonempty interior, so this is the usual notion with one-sided derivatives at the boundary).
- B is the conjunction of the two sentences: (i) for every `m`, `f` maps `U_{m+k}` into `V_m`
  (the text's `f : U_{m+k} → V_m`) and is `C^k` there; (ii) for every `m` and `l ≤ k`, it is `C^l`
  from `U_{m+l}` to `F_m`.
-/
namespace RoundTrip.V1_17
open Polyfold

/-- The map `E_a → F_b` induced by `f : E₀ → F₀`: the point of `F_b` over `f(x)` (junk if none). -/
noncomputable def levelTo {E F : ScBanach} (f : E.lvl 0 → F.lvl 0) (a b : ℕ) :
    E.lvl a → F.lvl b :=
  fun x => Function.invFun (F.toBase b) (f (E.toBase a x))

/-- `sc^k` maps between relatively open subsets of partial quadrants are `C^l` from `U_{m+l}` to
`V_m` for `l ≤ k`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (C' V : Set (F.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (k : ℕ),
    IsRelOpenInQuadrant E C U → IsRelOpenInQuadrant F C' V → Set.MapsTo f U V →
    IsSck k E F U f →
      (∀ m : ℕ,
        Set.MapsTo (levelTo f (m + k) m) (E.lvlSet U (m + k)) (F.lvlSet V m) ∧
        ContDiffOn ℝ k (levelTo f (m + k) m) (E.lvlSet U (m + k))) ∧
      (∀ m l : ℕ, l ≤ k →
        ContDiffOn ℝ l (levelTo f (m + l) m) (E.lvlSet U (m + l)))

end RoundTrip.V1_17
