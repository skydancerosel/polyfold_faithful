import Polyfold
/-! Blind formalization of V3_34 (the text's §3.4, Theorem 3.38, p. 90). Choices:
- Setting: `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (constant sc-structures), `C̃ ⊆ ℝⁿ` a partial
  quadrant (`IsPartialQuadrant`), `W` an arbitrary sc-Banach space; `E = ℝⁿ ⊕ W` is
  `ScBanach.paramProd (Fin n → ℝ) W` with the partial quadrant `C = C̃ × W`, the fibre
  `F = ℝᴺ ⊕ W` is `ScBanach.paramProd (Fin N → ℝ) W`.  Likewise for the primed data
  (`n', N', C̃' ⊆ ℝ^{n'}, W'`), which are existentially quantified.  No universe choices arise.
- "`f` a basic germ" (Definition 3.7): `IsBasicGerm C̃ G f B` on a germ of neighbourhoods
  `G = O(C̃ ⊕ W, 0)` for some contraction map `B`.
- "`s` the principal part of an sc⁺-section with `s(0) = 0`": an sc-smooth germ
  `s : O(C̃ ⊕ W, 0) → F¹` (target the shifted space `F.shift`, `IsScSmoothGerm`), `s(0) = 0`; I take
  it on the same germ of neighbourhoods `G` as `f`.  `f + s` adds `s` included by `F₁ → F₀`.
- "strong bundle isomorphism `Φ : U ◁ (ℝᴺ ⊕ W) → U' ◁ (ℝ^{N'} ⊕ W')` covering the
  sc-diffeomorphism `φ`": `IsStrongBundleIso U U' Φ Φ'` (`Φ'` its inverse), with `U` a relatively
  open neighbourhood of `0` in `C` inside the domain `G₀` of `f + s`, `U'` relatively open in
  `C' = C̃' × W'` (`IsRelOpenInQuadrant`), and `φ = base Φ` with `φ(0) = 0` (needed for a germ
  statement at `0`).
- "`(Φ_*(f + s))¹` (levels raised by one) is a basic germ": with `g = Φ_*(f + s)` the
  push-forward (`pushforward Φ Φ'`, `g(u') = (Φ(φ⁻¹u', (f + s)(φ⁻¹u')))₂`), there are a germ of
  neighbourhoods `G₁` of `0` in `C̃' ⊕ W'¹` (`paramProd (ℝ^{n'}) W'.shift`), a map
  `g₁ : ℝ^{n'} ⊕ W'₁ → ℝ^{N'} ⊕ W'₁` and a contraction map `B₁` with
  `IsBasicGerm C̃' G₁ g₁ B₁`, such that `g₁` is `g` read on level `1`: for `x ∈ G₁₀` its
  level-`0` image lies in `U'` and `g(x) = g₁(x)` under the inclusions `W'₁ → W'₀`
  (`IsRaisedBasic`, defined here).
- "`n − N = n' − N'`": equality of integers.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_34
open Polyfold

/-- The level-raised germ `g¹` of `g : U' → ℝ^{N'} ⊕ W'` is a basic germ: some basic germ `g₁` on a
germ of neighbourhoods `G₁` of `0` in `C̃' ⊕ W'¹` agrees with `g` on level `1` inside `U'`. -/
def IsRaisedBasic {n' N' : ℕ} {W' : ScBanach} (Ct' : Set (Fin n' → ℝ))
    (U' : Set ((ScBanach.paramProd (Fin n' → ℝ) W').lvl 0))
    (g : (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0 →
      (ScBanach.paramProd (Fin N' → ℝ) W').lvl 0) : Prop :=
  ∃ (G₁ : ScNbhdGerm (ScBanach.paramProd (Fin n' → ℝ) W'.shift) (Ct' ×ˢ Set.univ))
    (g₁ : (Fin n' → ℝ) × W'.lvl 1 → (Fin N' → ℝ) × W'.lvl 1)
    (B₁ : (Fin n' → ℝ) × W'.lvl 1 → W'.lvl 1),
    IsBasicGerm Ct' G₁ g₁ B₁ ∧
      ∀ x ∈ G₁.U 0,
        (((x.1, W'.incl 0 x.2) : (Fin n' → ℝ) × W'.lvl 0) ∈ U') ∧
          g (x.1, W'.incl 0 x.2) = ((g₁ x).1, W'.incl 0 (g₁ x).2)

/-- Theorem 3.38: for a basic germ `f` and an sc⁺-germ `s` with `s(0) = 0` there is a strong bundle
isomorphism `Φ` (covering an sc-diffeomorphism fixing `0`) such that `Φ_*(f + s)`, levels raised by
one, is a basic germ; the index `n − N` is preserved. -/
def B : Prop :=
  ∀ (n N : ℕ) (W : ScBanach) (Ct : Set (Fin n → ℝ))
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (f : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 → (ScBanach.paramProd (Fin N → ℝ) W).lvl 0)
    (Bf : (Fin n → ℝ) × W.lvl 0 → W.lvl 0)
    (s : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 →
      (ScBanach.paramProd (Fin N → ℝ) W).shift.lvl 0),
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) Ct →
    IsBasicGerm Ct G f Bf →
    IsScSmoothGerm (F := (ScBanach.paramProd (Fin N → ℝ) W).shift) G s → s 0 = 0 →
    ∃ (n' N' : ℕ) (W' : ScBanach) (Ct' : Set (Fin n' → ℝ))
      (U : Set ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0))
      (U' : Set ((ScBanach.paramProd (Fin n' → ℝ) W').lvl 0))
      (Φ : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0 →
        (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0 × (ScBanach.paramProd (Fin N' → ℝ) W').lvl 0)
      (Φ' : (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0 ×
          (ScBanach.paramProd (Fin N' → ℝ) W').lvl 0 →
        (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0),
      IsPartialQuadrant (ScBanach.const (Fin n' → ℝ)) Ct' ∧
      IsRelOpenInQuadrant (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) U ∧ 0 ∈ U ∧
      U ⊆ G.U 0 ∧
      IsRelOpenInQuadrant (ScBanach.paramProd (Fin n' → ℝ) W') (Ct' ×ˢ Set.univ) U' ∧
      IsStrongBundleIso U U' Φ Φ' ∧ IsStrongBundleMap.base Φ 0 = 0 ∧
      IsRaisedBasic Ct' U'
        (pushforward Φ Φ' (fun x => f x + (ScBanach.paramProd (Fin N → ℝ) W).toBase 1 (s x))) ∧
      (n : ℤ) - N = (n' : ℤ) - N'

end RoundTrip.V3_34
