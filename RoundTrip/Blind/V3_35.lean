import Polyfold
/-! Blind formalization of V3_35 (the text's §3.5, Theorem 3.40, p. 94). Choices:
- Setting: `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (constant sc-structures), `C̃ ⊆ ℝⁿ` a partial
  quadrant (`IsPartialQuadrant`), `W` an arbitrary sc-Banach space; `E = ℝⁿ ⊕ W` is
  `ScBanach.paramProd (Fin n → ℝ) W`, the partial quadrant `C = C̃ ⊕ W` is the set `C̃ × W`, and
  the target `F = ℝᴺ ⊕ W` is `ScBanach.paramProd (Fin N → ℝ) W`.  No universe choices arise.
- "`h` a basic germ" (Definition 3.7): a germ of neighbourhoods `G = O(C̃ ⊕ W, 0)` with
  `IsBasicGerm C̃ G h B` for some contraction map `B` (sc-smooth germ, `h(0) = 0`,
  `P ∘ h(a, w) = w − B(a, w)` with `B` an sc⁰-contraction germ, Definition 3.28).
- "`s` an sc⁺-germ with `s(0) = 0`": an sc-smooth germ `s : O(C̃ ⊕ W, 0) → F¹` into the shifted
  space `F¹ = (ℝᴺ ⊕ W)¹` (`IsScSmoothGerm` with target `F.shift`), `s(0) = 0`.  I take `s` on the
  same germ of neighbourhoods `G` as `h` (germs can be restricted to a common `G`).
- `f = h + s`, with `s` included into `F` by `F₁ → F₀`; the domain `U` of `f` is `G₀ = G.U 0`
  (a relatively open neighbourhood of `0` in `C`), and `S = {x ∈ U | f(x) = 0}`.
- "relatively open neighbourhoods `U ⊃ O(0) ⊃ O(1) ⊃ ⋯` of `0` on level `0`": sets `O(m)` of the
  form `O' ∩ C` with `O'` open in `E₀`, containing `0`, with `O(0) ⊆ U` and `O(m+1) ⊆ O(m)`.
- "`cl_{C₀}(S ∩ O(m)) ⊆ C_m`": the closure of `S ∩ O(m)` in `C₀` (= closure in `E₀`
  intersected with `C`) consists of points of `C` lying on level `m` (in the range of
  `E_m → E₀`).
- Doubt: the title says "local regularity and compactness", but the quoted statement only claims
  the inclusion `cl_{C₀}(S ∩ O(m)) ⊆ C_m`, not that this closure is compact in `C_m`.  I formalize
  only what is quoted (no compactness claim).
-/
namespace RoundTrip.V3_35
open Polyfold

/-- Theorem 3.40: for `f = h + s` (basic germ plus sc⁺-germ vanishing at `0`) there are nested
relatively open neighbourhoods `O(m)` of `0` in `C` inside `U` such that the closure in `C₀` of
the zeros of `f` in `O(m)` lies on level `m`. -/
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
    let S : Set ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0) := {x | x ∈ G.U 0 ∧ f x = 0}
    ∃ O : ℕ → Set ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0),
      (∀ m, (∃ O' : Set ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0),
          IsOpen O' ∧ O m = O' ∩ (Ct ×ˢ Set.univ)) ∧ 0 ∈ O m ∧ O (m + 1) ⊆ O m) ∧
      O 0 ⊆ G.U 0 ∧
      ∀ m, closure (S ∩ O m) ∩ (Ct ×ˢ Set.univ) ⊆
        (Ct ×ˢ Set.univ) ∩ Set.range ((ScBanach.paramProd (Fin n → ℝ) W).toBase m)

end RoundTrip.V3_35
