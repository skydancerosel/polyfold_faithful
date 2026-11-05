import Polyfold
/-! Blind formalization of V3_32 (the text's §3.3, Theorem 3.35, p. 89). `B` is the conjunction of
the two claims (sc^k for every `k`, and sc-smooth).  Choices:
- Setting (as in the blind V3_26/V3_30): the parameter space is literally `ℝⁿ = Fin n → ℝ` with
  the constant sc-structure, `C̃ ⊆ ℝⁿ` a partial quadrant (`IsPartialQuadrant`, Definition 1.11:
  "a finite-dimensional partial quadrant in `ℝⁿ`"), `W` an arbitrary sc-Banach space, `C̃ ⊕ W` is
  `ScBanach.paramProd (Fin n → ℝ) W` with the set `C̃ × W`.  No universe choices arise.
- "sc⁰-contraction germ `f`": a germ of neighbourhoods `G` (Definition 3.1) and
  `f = contractionMap B` (`f(a, w) = w − B(a, w)`) with `IsSc0ContractionGerm C̃ G B`
  (Definition 3.28).
- "of class sc^k": `IsSckGerm k G f` (Definition 3.2), `k` arbitrary.  "sc-smooth":
  `IsScSmoothGerm G f` (sc^k for every `k` on the same germ of neighbourhoods).
- "its solution germ": every representative `(V, δ)` of the solution germ of Theorem 3.29
  (`IsSolGerm`, as in V3_26/V3_30: an sc⁰-germ on `V` with `δ(0) = 0`, `(a, δ a) ∈ G₀`,
  `f(a, δ a) = 0` on `V₀`).  "is of class sc^k" (resp. "is sc-smooth"): `δ` is an sc^k-germ (resp.
  an sc-smooth germ, `IsScSmoothGerm`) on some smaller germ of neighbourhoods `V' ⊆ V`.
- For the sc-smooth conclusion I read "sc-smooth germ" as in Definition 3.2: one germ of
  neighbourhoods `V'` on which `δ` is sc^k for all `k` (not a `k`-dependent `V'`; the weaker
  reading would be `∀ k, ∃ V'`).  A diagonal choice `V'_m = ⋂_{j ≤ m} V^{(j)}_m` shows the two
  readings agree, so this is not a strengthening in substance.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_32
open Polyfold

/-- `δ` is a solution germ of `f = w − B(a, w)` on the germ of neighbourhoods `V`: an sc⁰-germ with
`δ(0) = 0`, `(v, δ v)` in the domain of `f` and `f(v, δ v) = 0` for `v ∈ V₀`. -/
def IsSolGerm {n : ℕ} {W : ScBanach} {Ct : Set (Fin n → ℝ)}
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0)
    (V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) (δ : (Fin n → ℝ) → W.lvl 0) : Prop :=
  IsSc0Germ V δ ∧ δ 0 = 0 ∧
    ∀ a ∈ V.U 0, ((a, δ a) : (Fin n → ℝ) × W.lvl 0) ∈ G.U 0 ∧ contractionMap Bm (a, δ a) = 0

/-- Theorem 3.35: on a finite-dimensional partial quadrant `C̃ ⊆ ℝⁿ`, the solution germ of an
sc⁰-contraction germ of class sc^k is of class sc^k, and it is sc-smooth if the germ is. -/
def B : Prop :=
  ∀ (n : ℕ) (W : ScBanach) (Ct : Set (Fin n → ℝ))
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0),
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) Ct →
    IsSc0ContractionGerm Ct G Bm →
      (∀ k : ℕ, IsSckGerm k G (contractionMap Bm) →
        ∀ (V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) (δ : (Fin n → ℝ) → W.lvl 0),
          IsSolGerm G Bm V δ →
          ∃ V' : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct,
            (∀ m, V'.U m ⊆ V.U m) ∧ IsSckGerm k V' δ) ∧
      (IsScSmoothGerm G (contractionMap Bm) →
        ∀ (V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) (δ : (Fin n → ℝ) → W.lvl 0),
          IsSolGerm G Bm V δ →
          ∃ V' : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct,
            (∀ m, V'.U m ⊆ V.U m) ∧ IsScSmoothGerm V' δ)

end RoundTrip.V3_32
