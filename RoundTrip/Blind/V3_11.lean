import Polyfold
/-! Blind formalization of V3_11 (the text's §3.1, Lemma 3.9, p. 67). Choices:
- Setting and "`B` as in Definition 3.7" exactly as in my `RoundTrip/Blind/V3_10.lean` (copied
  here): `E = ℝⁿ ⊕ W`, `F = ℝᴺ ⊕ W` (`ScBanach.paramProd`), `C̃ = [0, ∞)ᵏ ⊕ ℝ^{n−k}` (`CtB n k`,
  `k ≤ n`), a basic germ `f` on the germ of neighbourhoods `G = O(C̃ ⊕ W, 0)` (`IsBasicGermB`), and
  `B(a, w) = w − P_W f(a, w)` (`BB f`).
- `D₂B`: `f` is sc-smooth, so it is sc¹ with a derivative family `D x = Df(x) : E₀ → F₀`, `x ∈ U₁`
  (the project's `IsSc1GermWith G f D`, Definition 3.2, audited in V3_2).  Then
  `D₂B(a, w)ζ = ζ − P_W Df(a, w)(0, ζ)` (`D2B D x ζ`).  B quantifies over all such `D` (unique on
  `U₁`, `U₁` being relatively open in a partial quadrant).
- "for `(a, w) ∈ E_{m+1}` close enough to `(0, 0)` in `E_m`": there is `δ > 0` such that for every
  point `x` of the level-`m+1` domain `G_{m+1}` (so `Df(x)` acts on level `m`) with
  `|ι x|_m < δ` (`ι = E.incl m : E_{m+1} → E_m`); `x` enters `D` as the level-1 point `x₁` with the
  same image in `E₀`.  "`|D₂B(a, w)ζ|_m ≤ ε|ζ|_m` for `ζ ∈ W_m`": `D₂B(a, w)ζ` lies in `W_m`
  (a lift `η`) and `|η|_m ≤ ε|ζ|_m`.
- "in particular `D₂B(0, 0) = 0`": `D₂B(0, 0)ζ = 0` for all `ζ ∈ W₀` (B states it).
- Nothing looks false to me.
-/
namespace RoundTrip.V3_11
open Polyfold

/-- `C̃ = [0, ∞)ᵏ ⊕ ℝ^{n−k} ⊆ ℝⁿ`: the first `k` coordinates are nonnegative. -/
def CtB (n k : ℕ) : Set (Fin n → ℝ) :=
  {a | ∀ i : Fin n, (i : ℕ) < k → 0 ≤ a i}

/-- `ℝⁿ ⊕ W`. -/
noncomputable abbrev EB (n : ℕ) (W : ScBanach) : ScBanach :=
  ScBanach.paramProd (Fin n → ℝ) W

/-- `B(a, w) = w − P_W f(a, w)`. -/
def BB {n N : ℕ} {W : ScBanach} (f : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0)
    (x : (Fin n → ℝ) × W.lvl 0) : W.lvl 0 :=
  x.2 - (f x).2

/-- **Definition 3.7** (copied from V3_10): `f` is a basic germ on `G`. -/
def IsBasicGermB (n k N : ℕ) (W : ScBanach) (G : ScNbhdGerm (EB n W) (CtB n k ×ˢ Set.univ))
    (f : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0) : Prop :=
  IsScSmoothGerm (F := EB N W) G f ∧ f 0 = 0 ∧ BB f (0, 0) = 0 ∧
  ∀ ε > (0 : ℝ), ∀ m : ℕ, ∃ δ > (0 : ℝ), ∀ (a : Fin n → ℝ) (w w' : W.lvl m),
    ((a, w) : (EB n W).lvl m) ∈ G.U m → ((a, w') : (EB n W).lvl m) ∈ G.U m →
    ‖a‖ < δ → ‖w‖ < δ → ‖w'‖ < δ →
    ∃ b b' : W.lvl m, W.toBase m b = BB f (a, W.toBase m w) ∧
      W.toBase m b' = BB f (a, W.toBase m w') ∧ ‖b - b'‖ ≤ ε * ‖w - w'‖

/-- `D₂B(x)ζ = ζ − P_W Df(x)(0, ζ)`, the fibre derivative of `B = w − P_W f` at `x ∈ E₁`. -/
def D2B {n N : ℕ} {W : ScBanach}
    (D : (EB n W).lvl 1 → (EB n W).lvl 0 →L[ℝ] (EB N W).lvl 0) (x : (EB n W).lvl 1)
    (ζ : W.lvl 0) : W.lvl 0 :=
  ζ - (D x ((0 : Fin n → ℝ), ζ)).2

/-- Lemma 3.9: for every `ε > 0` and `m`, `|D₂B(a, w)ζ|_m ≤ ε|ζ|_m` (`ζ ∈ W_m`) for `(a, w)` on
level `m + 1` close enough to `(0, 0)` in `E_m`; in particular `D₂B(0, 0) = 0`. -/
def B : Prop :=
  ∀ (n k N : ℕ) (W : ScBanach), k ≤ n →
    ∀ (G : ScNbhdGerm (EB n W) (CtB n k ×ˢ Set.univ))
      (f : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0),
      IsBasicGermB n k N W G f →
      ∀ D : (EB n W).lvl 1 → (EB n W).lvl 0 →L[ℝ] (EB N W).lvl 0,
        IsSc1GermWith (F := EB N W) G f D →
        (∀ ε > (0 : ℝ), ∀ m : ℕ, ∃ δ > (0 : ℝ),
          ∀ (x : (EB n W).lvl (m + 1)) (x₁ : (EB n W).lvl 1),
            (EB n W).toBase (m + 1) x = (EB n W).toBase 1 x₁ → x ∈ G.U (m + 1) →
            ‖(EB n W).incl m x‖ < δ →
            ∀ ζ : W.lvl m, ∃ η : W.lvl m,
              W.toBase m η = D2B D x₁ (W.toBase m ζ) ∧ ‖η‖ ≤ ε * ‖ζ‖) ∧
        (∀ ζ : W.lvl 0, D2B D 0 ζ = 0)

end RoundTrip.V3_11
