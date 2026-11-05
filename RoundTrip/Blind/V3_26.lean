import Polyfold
/-! Blind formalization of V3_26 (the text's §3.3, Theorem 3.29, p. 86). Choices:
- Setting (as in the blind V3_30): the parameter space is literally `ℝⁿ = Fin n → ℝ` with the
  constant sc-structure (`ScBanach.const`), `C̃ ⊆ ℝⁿ` a partial quadrant (`IsPartialQuadrant`,
  Definition 1.11; the text's Definition 3.28 places `C̃` in a finite-dimensional `ℝⁿ`), `W` an
  arbitrary sc-Banach space, and `C̃ ⊕ W` is `ScBanach.paramProd (Fin n → ℝ) W` with the set
  `C̃ × W`.  No universe choices arise (sc-Banach spaces live in `Type 1`, levels in `Type`).
- "`f : O(C̃ ⊕ W, 0) → (W, 0)` an sc⁰-contraction germ": a germ of neighbourhoods
  `G : ScNbhdGerm (ℝⁿ ⊕ W) (C̃ × W)` (Definition 3.1) and `f = contractionMap B`, i.e.
  `f(a, w) = w − B(a, w)`, with `IsSc0ContractionGerm C̃ G B` (Definition 3.28: `B` an sc⁰-germ,
  `B(0, 0) = 0`, and on every level `m` a Lipschitz constant `ε` of `B(a, ·)` near `(0, 0)`).
- "an sc⁰-solution germ `δ : O(C̃, 0) → (W, 0)` with `f(a, δ(a)) = 0`" (`IsSolGerm`, the same
  definition as in V3_30): a germ of neighbourhoods `V : ScNbhdGerm ℝⁿ C̃` and a map `δ` which is
  an sc⁰-germ on `V` (Definition 3.2), `δ(0) = 0`, with `(a, δ(a))` in the domain `G₀` of `f` and
  `f(a, δ(a)) = 0` for `a ∈ V₀`.  (Asking `(a, δ(a)) ∈ G_m` for `a ∈ V_m` on every level would be
  equivalent after shrinking `V`, by continuity of `δ` on every level.)
- "admits a uniquely determined" solution germ: existence of such `(V, δ)`, and uniqueness *as a
  germ*: any two solution germs `(V, δ)`, `(V', δ')` agree on a common smaller germ of
  neighbourhoods `V'' ⊆ V ∩ V'` (level by level), i.e. `δ = δ'` on `V''₀` (agreement on level `0`
  gives agreement on all levels, since `V''_m` maps into `V''₀`).
- The proof method ("parametrized Banach fixed point theorem") is not part of the claim.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_26
open Polyfold

/-- `δ` is a solution germ of `f = w − B(a, w)` on the germ of neighbourhoods `V`: an sc⁰-germ with
`δ(0) = 0`, `(v, δ v)` in the domain of `f` and `f(v, δ v) = 0` for `v ∈ V₀`. -/
def IsSolGerm {n : ℕ} {W : ScBanach} {Ct : Set (Fin n → ℝ)}
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0)
    (V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) (δ : (Fin n → ℝ) → W.lvl 0) : Prop :=
  IsSc0Germ V δ ∧ δ 0 = 0 ∧
    ∀ a ∈ V.U 0, ((a, δ a) : (Fin n → ℝ) × W.lvl 0) ∈ G.U 0 ∧ contractionMap Bm (a, δ a) = 0

/-- Theorem 3.29: an sc⁰-contraction germ has an sc⁰-solution germ `δ` with `f(a, δ(a)) = 0`, and
any two solution germs coincide near `0` (on a common smaller germ of neighbourhoods). -/
def B : Prop :=
  ∀ (n : ℕ) (W : ScBanach) (Ct : Set (Fin n → ℝ))
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0),
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) Ct →
    IsSc0ContractionGerm Ct G Bm →
      (∃ (V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) (δ : (Fin n → ℝ) → W.lvl 0),
          IsSolGerm G Bm V δ) ∧
      ∀ (V V' : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) (δ δ' : (Fin n → ℝ) → W.lvl 0),
        IsSolGerm G Bm V δ → IsSolGerm G Bm V' δ' →
        ∃ V'' : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct,
          (∀ m, V''.U m ⊆ V.U m ∩ V'.U m) ∧ ∀ a ∈ V''.U 0, δ a = δ' a

end RoundTrip.V3_26
