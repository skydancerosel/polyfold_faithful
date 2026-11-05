import Polyfold
/-! Blind formalization of V3_37 (the text's §3.5, Lemma 3.42, p. 101). `B` is the conjunction of
the two claims (for one pair `ε'₀, τ'₀`).  Choices:
- Setting ("the setting after Theorem 3.38", as in the blind V3_34/V3_38): `ℝⁿ = Fin n → ℝ`,
  `ℝᴺ = Fin N → ℝ` (constant sc-structures), `C̃ ⊆ ℝⁿ` a partial quadrant, `W` an arbitrary
  sc-Banach space; `E = ℝⁿ ⊕ W` (`ScBanach.paramProd (Fin n → ℝ) W`) with `C = C̃ × W`,
  `F = ℝᴺ ⊕ W`; primed data `n', N', C̃' ⊆ ℝ^{n'}, W'`, `E' = ℝ^{n'} ⊕ W'`, `C' = C̃' × W'`,
  `F' = ℝ^{N'} ⊕ W'` likewise.  No universe choices arise.
- `f = h + s`: `h` a basic germ (`IsBasicGerm C̃ G h B`, Definition 3.7) on a germ of
  neighbourhoods `G`, `s` an sc⁺-germ (sc-smooth germ into `F¹`) with `s(0) = 0` on the same `G`.
  The hypotheses of Theorem 3.43 (`Df(0)` onto, `ker Df(0)` in good position) are *not* assumed:
  the lemma precedes Theorem 3.43 and is stated in the setting after Theorem 3.38.
- `g = Φ_*(f)`: as in V3_38, for *every* strong bundle isomorphism `Φ` as produced by
  Theorem 3.38: `IsStrongBundleIso U U' Φ Φ'`, `U` a relatively open neighbourhood of `0` in `C`
  inside `G₀`, `U'` relatively open in `C'`, `φ = base Φ` with `φ(0) = 0`,
  `g = pushforward Φ Φ' f` on `U'`.
- "`g¹` basic" and "`δ` the solution germ of `P' ∘ g¹`": the data of the basic germ `g¹` are made
  explicit (V3_38's `IsRaisedBasic` with its witnesses universally quantified): any germ of
  neighbourhoods `G₁` of `0` in `C̃' ⊕ W'¹`, basic germ `g₁` with contraction map `B₁`
  (`IsBasicGerm C̃' G₁ g₁ B₁`) agreeing with `g` on level 1 inside `U'`; then `P' ∘ g¹ = w − B₁`,
  and `δ` is any representative `(V_δ, δ)` of its solution germ (`IsSolGerm`, as in V3_26/V3_30,
  with fibre `W'¹`, so `δ(a) ∈ W'₁`).
- "There are `ε'₀, τ'₀`": positive reals (presupposed).  "a solution `(a', w')` of `g = 0` with
  `|a'|₀ ≤ ε'₀`, `|w'|₀ ≤ τ'₀`": a point of the domain `U'` of `g` with `g(a', w') = 0` and these
  bounds; "has `w' = δ(a')`": `a'` lies in the domain `V_δ₀` of `δ` and `w' = ι δ(a')`
  (`ι : W'₁ → W'₀`).  "`|δ(a')|₀ ≤ τ'₀` if `|a'|₀ ≤ ε'₀`": for `a' ∈ C̃'` (the domain of the germ
  `δ`) with `|a'| ≤ ε'₀`, `a' ∈ V_δ₀` and `|ι δ(a')|₀ ≤ τ'₀`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_37
open Polyfold

/-- `δ` is a solution germ of `f = w − B(a, w)` on the germ of neighbourhoods `V`: an sc⁰-germ with
`δ(0) = 0`, `(v, δ v)` in the domain of `f` and `f(v, δ v) = 0` for `v ∈ V₀`. -/
def IsSolGerm {n : ℕ} {W : ScBanach} {Ct : Set (Fin n → ℝ)}
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0)
    (V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) (δ : (Fin n → ℝ) → W.lvl 0) : Prop :=
  IsSc0Germ V δ ∧ δ 0 = 0 ∧
    ∀ a ∈ V.U 0, ((a, δ a) : (Fin n → ℝ) × W.lvl 0) ∈ G.U 0 ∧ contractionMap Bm (a, δ a) = 0

/-- Lemma 3.42: in the setting after Theorem 3.38 (`g = Φ_*(h + s)`, `g¹` basic, `δ` the solution
germ of `P' ∘ g¹`) there are `ε'₀, τ'₀ > 0` such that every zero `(a', w')` of `g` with
`|a'|₀ ≤ ε'₀`, `|w'|₀ ≤ τ'₀` has `w' = δ(a')`, and `|δ(a')|₀ ≤ τ'₀` whenever `|a'|₀ ≤ ε'₀`. -/
def B : Prop :=
  ∀ (n N : ℕ) (W : ScBanach) (Ct : Set (Fin n → ℝ))
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (h : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 → (ScBanach.paramProd (Fin N → ℝ) W).lvl 0)
    (Bh : (Fin n → ℝ) × W.lvl 0 → W.lvl 0)
    (s : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 →
      (ScBanach.paramProd (Fin N → ℝ) W).shift.lvl 0),
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) Ct →
    IsBasicGerm Ct G h Bh →
    IsScSmoothGerm (F := (ScBanach.paramProd (Fin N → ℝ) W).shift) G s → s 0 = 0 →
    let f : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 → (ScBanach.paramProd (Fin N → ℝ) W).lvl 0 :=
      fun x => h x + (ScBanach.paramProd (Fin N → ℝ) W).toBase 1 (s x)
    ∀ (n' N' : ℕ) (W' : ScBanach) (Ct' : Set (Fin n' → ℝ))
      (U : Set ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0))
      (U' : Set ((ScBanach.paramProd (Fin n' → ℝ) W').lvl 0))
      (Φ : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0 →
        (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0 × (ScBanach.paramProd (Fin N' → ℝ) W').lvl 0)
      (Φ' : (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0 ×
          (ScBanach.paramProd (Fin N' → ℝ) W').lvl 0 →
        (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0),
      IsPartialQuadrant (ScBanach.const (Fin n' → ℝ)) Ct' →
      IsRelOpenInQuadrant (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) U → 0 ∈ U →
      U ⊆ G.U 0 →
      IsRelOpenInQuadrant (ScBanach.paramProd (Fin n' → ℝ) W') (Ct' ×ˢ Set.univ) U' →
      IsStrongBundleIso U U' Φ Φ' → IsStrongBundleMap.base Φ 0 = 0 →
      let g := pushforward Φ Φ' f
      ∀ (G₁ : ScNbhdGerm (ScBanach.paramProd (Fin n' → ℝ) W'.shift) (Ct' ×ˢ Set.univ))
        (g₁ : (Fin n' → ℝ) × W'.lvl 1 → (Fin N' → ℝ) × W'.lvl 1)
        (B₁ : (Fin n' → ℝ) × W'.lvl 1 → W'.lvl 1),
        IsBasicGerm Ct' G₁ g₁ B₁ →
        (∀ x ∈ G₁.U 0,
          (((x.1, W'.incl 0 x.2) : (Fin n' → ℝ) × W'.lvl 0) ∈ U') ∧
            g (x.1, W'.incl 0 x.2) = ((g₁ x).1, W'.incl 0 (g₁ x).2)) →
        ∀ (Vδ : ScNbhdGerm (ScBanach.const (Fin n' → ℝ)) Ct') (δ : (Fin n' → ℝ) → W'.lvl 1),
          IsSolGerm (W := W'.shift) G₁ B₁ Vδ δ →
          ∃ ε τ : ℝ, 0 < ε ∧ 0 < τ ∧
            (∀ (a : Fin n' → ℝ) (w : W'.lvl 0),
              ((a, w) : (Fin n' → ℝ) × W'.lvl 0) ∈ U' → g (a, w) = 0 → ‖a‖ ≤ ε → ‖w‖ ≤ τ →
                a ∈ Vδ.U 0 ∧ w = W'.incl 0 (δ a)) ∧
            (∀ a ∈ Ct', ‖a‖ ≤ ε → a ∈ Vδ.U 0 ∧ ‖W'.incl 0 (δ a)‖ ≤ τ)

end RoundTrip.V3_37
