import Polyfold
/-! Blind formalization of V3_10 (the text's §3.1, Definition 3.7, p. 66). Choices:
- This item is a definition; the text asserts no further property.  Setting: `ℝⁿ = Fin n → ℝ`
  and `ℝᴺ = Fin N → ℝ` with the constant sc-structures, `W` an sc-Banach space,
  `E = ℝⁿ ⊕ W` and `F = ℝᴺ ⊕ W` (the project's `ScBanach.paramProd`, i.e. `(const ℝⁿ).prod W`:
  levels `ℝⁿ × W_m`, norm the max of the two norms).  The partial quadrant is the text's
  `[0, ∞)ᵏ ⊕ ℝ^{n−k} ⊕ W`: `C̃ = CtB n k` (the first `k` coordinates nonnegative, `k ≤ n`) and
  `C = C̃ × W`.  No universe choices arise.
- "an sc-smooth germ `f : O(C, 0) → ℝᴺ ⊕ W`": a germ of neighbourhoods `G` around `0` in `C`
  (the project's `ScNbhdGerm`, Definition 3.1, audited in V3_1) and `IsScSmoothGerm G f`
  (Definition 3.2, audited in V3_2); `f` is a total map `ℝⁿ × W₀ → ℝᴺ × W₀`.
- "`P_W ∘ f(a, w) = w − B(a, w)`" *defines* `B(a, w) = w − P_W f(a, w)` (`BB f`); `B(0, 0) = 0`
  is then automatic from `f(0) = 0` (kept, as the text states it).
- "`|B(a, w) − B(a, w')|_m ≤ ε|w − w'|_m` for `(a, w), (a, w')` close enough to `(0, 0)` on level
  `m`, for every `ε > 0`, `m ≥ 0`": for every `ε > 0` and `m` there is `δ > 0` such that for
  `(a, w), (a, w')` in the level-`m` domain `G_m` (`w, w' ∈ W_m`) with `|a|, |w|_m, |w'|_m < δ`,
  the values `B(a, w), B(a, w')` lie in `W_m` (lifts `b, b'`) and `|b − b'|_m ≤ ε|w − w'|_m`.
- B: the project's `IsBasicGerm C̃ G f B` (for some `B`), with `P = ℝⁿ`, `Q = ℝᴺ`, `Ct = C̃`, is
  equivalent to my `IsBasicGermB`.  (The project allows a general `Ct`; I compare on the text's.)
- Nothing looks false to me.
-/
namespace RoundTrip.V3_10
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

/-- **Definition 3.7**: `f : O([0, ∞)ᵏ ⊕ ℝ^{n−k} ⊕ W, 0) → ℝᴺ ⊕ W` (on the germ `G`) is a basic
germ. -/
def IsBasicGermB (n k N : ℕ) (W : ScBanach) (G : ScNbhdGerm (EB n W) (CtB n k ×ˢ Set.univ))
    (f : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0) : Prop :=
  IsScSmoothGerm (F := EB N W) G f ∧ f 0 = 0 ∧ BB f (0, 0) = 0 ∧
  ∀ ε > (0 : ℝ), ∀ m : ℕ, ∃ δ > (0 : ℝ), ∀ (a : Fin n → ℝ) (w w' : W.lvl m),
    ((a, w) : (EB n W).lvl m) ∈ G.U m → ((a, w') : (EB n W).lvl m) ∈ G.U m →
    ‖a‖ < δ → ‖w‖ < δ → ‖w'‖ < δ →
    ∃ b b' : W.lvl m, W.toBase m b = BB f (a, W.toBase m w) ∧
      W.toBase m b' = BB f (a, W.toBase m w') ∧ ‖b - b'‖ ≤ ε * ‖w - w'‖

/-- Definition 3.7: on `O([0, ∞)ᵏ ⊕ ℝ^{n−k} ⊕ W, 0)`, the project's basic germs are the text's. -/
def B : Prop :=
  ∀ (n k N : ℕ) (W : ScBanach), k ≤ n →
    ∀ (G : ScNbhdGerm (EB n W) (CtB n k ×ˢ Set.univ))
      (f : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0),
      (∃ Bf : (Fin n → ℝ) × W.lvl 0 → W.lvl 0, IsBasicGerm (CtB n k) G f Bf) ↔
        IsBasicGermB n k N W G f

end RoundTrip.V3_10
