import Polyfold
/-! Blind formalization of V3_30 (the text's §3.3, Theorem 3.33, p. 88). Choices:
- Setting: the parameter space is literally `ℝⁿ = Fin n → ℝ` with the constant sc-structure
  (`ScBanach.const`), `C̃ ⊆ ℝⁿ` a partial quadrant (`IsPartialQuadrant`, Definition 1.11), `W` an
  arbitrary sc-Banach space, and `C̃ ⊕ W` is `ScBanach.paramProd (Fin n → ℝ) W` with the set
  `C̃ × W`.  No universe choices arise (sc-Banach spaces live in `Type 1` with levels in `Type`).
- "`f : O(C̃ ⊕ W, 0) → (W, 0)` an sc⁰-contraction germ": a germ of neighbourhoods
  `G : ScNbhdGerm (ℝⁿ ⊕ W) (C̃ × W)` (Definition 3.1) and `f = contractionMap B`, i.e.
  `f(a, w) = w − B(a, w)`, with `IsSc0ContractionGerm C̃ G B` (Definition 3.28).
- "of class sc^k": `IsSckGerm k G f` (Definition 3.2) for the germ `f` itself (equivalently for
  `B`, since `f = w − B`); `k` arbitrary.
- "its solution germ `δ`, `f(v, δ(v)) = 0`": the solution germ of Theorem 3.29 is only determined
  as a germ, so I quantify over *every* representative: any germ of neighbourhoods
  `V : ScNbhdGerm ℝⁿ C̃` and map `δ` which is an sc⁰-germ on `V` (Definition 3.2) with `δ(0) = 0`,
  `(v, δ(v))` in the domain `G₀` of `f` and `f(v, δ(v)) = 0` for `v ∈ V₀` (`IsSolGerm`, defined
  here).  "is of class sc^k" is read as: `δ` is an sc^k-germ on some smaller germ of
  neighbourhoods `V' ⊆ V` (level by level), as germs are equal once restricted.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_30
open Polyfold

/-- `δ` is a solution germ of `f = w − B(a, w)` on the germ of neighbourhoods `V`: an sc⁰-germ with
`δ(0) = 0`, `(v, δ v)` in the domain of `f` and `f(v, δ v) = 0` for `v ∈ V₀`. -/
def IsSolGerm {n : ℕ} {W : ScBanach} {Ct : Set (Fin n → ℝ)}
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0)
    (V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) (δ : (Fin n → ℝ) → W.lvl 0) : Prop :=
  IsSc0Germ V δ ∧ δ 0 = 0 ∧
    ∀ a ∈ V.U 0, ((a, δ a) : (Fin n → ℝ) × W.lvl 0) ∈ G.U 0 ∧ contractionMap Bm (a, δ a) = 0

/-- Theorem 3.33: the solution germ of an sc⁰-contraction germ of class sc^k is of class sc^k. -/
def B : Prop :=
  ∀ (n : ℕ) (W : ScBanach) (Ct : Set (Fin n → ℝ))
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0) (k : ℕ),
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) Ct →
    IsSc0ContractionGerm Ct G Bm →
    IsSckGerm k G (contractionMap Bm) →
    ∀ (V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) (δ : (Fin n → ℝ) → W.lvl 0),
      IsSolGerm G Bm V δ →
      ∃ V' : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct,
        (∀ m, V'.U m ⊆ V.U m) ∧ IsSckGerm k V' δ

end RoundTrip.V3_30
