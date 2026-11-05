import Polyfold
/-! Blind formalization of V3_12 (the text's §3.1, Proposition 3.10, p. 68). Choices:
- Setting as in my `RoundTrip/Blind/V3_10.lean` (definitions copied): `E = ℝⁿ ⊕ W`,
  `F = ℝᴺ ⊕ W` (`ScBanach.paramProd`), `C̃ = [0, ∞)ᵏ ⊕ ℝ^{n−k}` (`CtB n k`, `k ≤ n`), the germ of
  neighbourhoods `G = O(C̃ ⊕ W, 0)`, and "`h` a basic germ" is my `IsBasicGermB` (Definition 3.7).
- "`s` an sc⁺-germ": an sc-smooth germ `s : O(C, 0) → F¹` into the shifted space (`IsScSmoothGerm`
  with target `F.shift`, Definition 3.2, audited in V3_2).  I take `s` on the same germ of
  neighbourhoods `G` as `h` (two germs can be restricted to a common smaller one).
  `f = h + s` is `h + ι ∘ s` (`ι = F.toBase 1 : F₁ → F₀`; `sumB`).  "`f(0) = 0`": `f 0 = 0`.
- `Df`: the derivative family of the sc¹-germ `f` (the project's `IsSc1GermWith G f D`,
  Definition 3.2); B quantifies over all such `D` (unique on `U₁`).  `Df(0) = D 0`.
- "`Df(0) : ℝⁿ ⊕ W → ℝᴺ ⊕ W` is sc-Fredholm of index `n − N`": some sc-operator `T : E → F`
  (the project's `ScOperator`, Definition 1.3) has base map `D 0` and is sc-Fredholm (the project's
  `IsScFredholm`, Definition 1.8), and the index of its base map `T₀ = Df(0) : E₀ → F₀`
  (`indexB`, `dim ker − dim coker`) is `n − N`.
- "for every `m`, `Df(a, w)` on level `m` is Fredholm of index `n − N` for `(a, w) ∈ E_{m+1}` small
  in `E_m`": for every `m` there is `δ > 0` such that for every point `x` of the level-`m+1`
  domain `G_{m+1}` with `|ι x|_m < δ` (`ι = E.incl m`; `x` enters `D` as the level-1 point `x₁`
  with the same image in `E₀`), the level-`m` operator of `Df(x)` exists (a bounded
  `L : E_m → F_m` with `ι L v = Df(x) ι v`) and is Fredholm (classical: `IsFredholmB`, finite
  dimensional kernel, closed range, finite dimensional cokernel) of index `n − N`.
- Nothing looks false to me.
-/
namespace RoundTrip.V3_12
open Polyfold

section Fredholm
variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V']
  [NormedSpace ℝ V']

/-- The kernel of a bounded operator. -/
def kerB (A : V →L[ℝ] V') : Submodule ℝ V := LinearMap.ker (A : V →ₗ[ℝ] V')

/-- The range of a bounded operator. -/
def rangeB (A : V →L[ℝ] V') : Submodule ℝ V' := LinearMap.range (A : V →ₗ[ℝ] V')

/-- A bounded operator is **Fredholm**: finite dimensional kernel, closed range of finite
codimension. -/
def IsFredholmB (A : V →L[ℝ] V') : Prop :=
  FiniteDimensional ℝ (kerB A) ∧ IsClosed (rangeB A : Set V') ∧
    FiniteDimensional ℝ (V' ⧸ rangeB A)

/-- The index `dim ker A − dim coker A`. -/
noncomputable def indexB (A : V →L[ℝ] V') : ℤ :=
  (Module.finrank ℝ (kerB A) : ℤ) - (Module.finrank ℝ (V' ⧸ rangeB A) : ℤ)

end Fredholm

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

/-- `f = h + s`, the sc⁺-germ `s : E₀ → F₁` included into `F₀`. -/
noncomputable def sumB {n N : ℕ} {W : ScBanach} (h : (EB n W).lvl 0 → (EB N W).lvl 0)
    (s : (EB n W).lvl 0 → (EB N W).shift.lvl 0) (x : (EB n W).lvl 0) : (EB N W).lvl 0 :=
  h x + (EB N W).toBase 1 (s x)

/-- Proposition 3.10: for `f = h + s` (`h` basic, `s` sc⁺, `f(0) = 0`), `Df(0)` is sc-Fredholm of
index `n − N`, and on every level `m`, `Df(a, w)` is Fredholm of index `n − N` for `(a, w)` on
level `m + 1` small in `E_m`. -/
def B : Prop :=
  ∀ (n k N : ℕ) (W : ScBanach), k ≤ n →
    ∀ (G : ScNbhdGerm (EB n W) (CtB n k ×ˢ Set.univ))
      (h : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0)
      (s : (EB n W).lvl 0 → (EB N W).shift.lvl 0),
      IsBasicGermB n k N W G h → IsScSmoothGerm (F := (EB N W).shift) G s →
      sumB h s 0 = 0 →
      ∀ D : (EB n W).lvl 1 → (EB n W).lvl 0 →L[ℝ] (EB N W).lvl 0,
        IsSc1GermWith (F := EB N W) G (sumB h s) D →
        -- `Df(0)` is sc-Fredholm of index `n − N`
        (∃ T : ScOperator (EB n W) (EB N W),
          T.lvl 0 = D 0 ∧ IsScFredholm T ∧ indexB (T.lvl 0) = (n : ℤ) - N) ∧
        -- on level `m`, `Df(a, w)` is Fredholm of index `n − N` near `0`
        (∀ m : ℕ, ∃ δ > (0 : ℝ),
          ∀ (x : (EB n W).lvl (m + 1)) (x₁ : (EB n W).lvl 1),
            (EB n W).toBase (m + 1) x = (EB n W).toBase 1 x₁ → x ∈ G.U (m + 1) →
            ‖(EB n W).incl m x‖ < δ →
            ∃ L : (EB n W).lvl m →L[ℝ] (EB N W).lvl m,
              (∀ v : (EB n W).lvl m,
                (EB N W).toBase m (L v) = D x₁ ((EB n W).toBase m v)) ∧
              IsFredholmB L ∧ indexB L = (n : ℤ) - N)

end RoundTrip.V3_12
