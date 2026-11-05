import Polyfold
/-! Blind formalization of V3_27 (the text's §3.3, Theorem 3.30, p. 86; cited from [21]). Choices:
- Setting (as in the blind V3_26/V3_30): the parameter space is literally `ℝⁿ = Fin n → ℝ` with
  the constant sc-structure, `C̃ ⊆ ℝⁿ` a partial quadrant (`IsPartialQuadrant`), `W` an arbitrary
  sc-Banach space, `C̃ ⊕ W` is `ScBanach.paramProd (Fin n → ℝ) W` with the set `C̃ × W`.  No
  universe choices arise.
- "`f` an sc⁰-contraction germ": a germ of neighbourhoods `G` (Definition 3.1) and
  `f = contractionMap B` (`f(a, w) = w − B(a, w)`) with `IsSc0ContractionGerm C̃ G B`
  (Definition 3.28).
- "`f` of class sc¹": `IsSc1Germ G f` (Definition 3.2, for the germ `f` itself on `G`).
- "its solution germ `δ`": the solution germ of Theorem 3.29 is determined only as a germ, so the
  claim is made for *every* representative: any germ of neighbourhoods `V` of `0` in `C̃` and map
  `δ` that is an sc⁰-germ on `V` with `δ(0) = 0`, `(a, δ(a)) ∈ G₀` and `f(a, δ(a)) = 0` on `V₀`
  (`IsSolGerm`, as in V3_26/V3_30).  "`δ` is of class sc¹" (as a germ): `δ` is an sc¹-germ
  (`IsSc1Germ`) on some smaller germ of neighbourhoods `V' ⊆ V` (level by level).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_27
open Polyfold

/-- `δ` is a solution germ of `f = w − B(a, w)` on the germ of neighbourhoods `V`: an sc⁰-germ with
`δ(0) = 0`, `(v, δ v)` in the domain of `f` and `f(v, δ v) = 0` for `v ∈ V₀`. -/
def IsSolGerm {n : ℕ} {W : ScBanach} {Ct : Set (Fin n → ℝ)}
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0)
    (V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) (δ : (Fin n → ℝ) → W.lvl 0) : Prop :=
  IsSc0Germ V δ ∧ δ 0 = 0 ∧
    ∀ a ∈ V.U 0, ((a, δ a) : (Fin n → ℝ) × W.lvl 0) ∈ G.U 0 ∧ contractionMap Bm (a, δ a) = 0

/-- Theorem 3.30: the solution germ of an sc⁰-contraction germ of class sc¹ is of class sc¹. -/
def B : Prop :=
  ∀ (n : ℕ) (W : ScBanach) (Ct : Set (Fin n → ℝ))
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0),
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) Ct →
    IsSc0ContractionGerm Ct G Bm →
    IsSc1Germ G (contractionMap Bm) →
    ∀ (V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) (δ : (Fin n → ℝ) → W.lvl 0),
      IsSolGerm G Bm V δ →
      ∃ V' : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct,
        (∀ m, V'.U m ⊆ V.U m) ∧ IsSc1Germ V' δ

end RoundTrip.V3_27
