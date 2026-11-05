import Polyfold
/-! Blind formalization of V3_76 (the text's §3.4, Corollary 3.39, p. 93). Choices:
- Setting: `E, F` arbitrary sc-Banach spaces (`ScBanach`, levels in `Type`), `C ⊆ E₀` a partial
  quadrant (`IsPartialQuadrant`), a germ of neighbourhoods `G = O(C, 0)` (`ScNbhdGerm`,
  Definition 3.1), the sc-germ `g : O(C, 0) → F` (a total map `E₀ → F₀`, only its values near `0`
  matter).  The basic-germ side as in the earlier blind file V3_34 (Theorem 3.38):
  `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (constant structures), `C̃ ⊆ ℝⁿ` a partial quadrant, `W` an
  sc-Banach space, `E' = ℝⁿ ⊕ W` (`ScBanach.paramProd`) with `C' = C̃ × W`, `F' = ℝᴺ ⊕ W`.  No
  universe choices arise.
- "`g` equivalent by a strong bundle isomorphism `Φ` to a basic germ": `Φ : U ◁ F → U' ◁ (ℝᴺ ⊕ W)`
  with inverse `Φ'` (`IsStrongBundleIso U U' Φ Φ'`), `U` a relatively open neighbourhood of `0` in
  `C` inside `G₀`, `U'` relatively open in `C'`, covering `φ = base Φ` with `φ(0) = 0`, and the
  push-forward `Φ_*(g)` (`pushforward Φ Φ' g`) is a basic germ (`IsBasicGerm`, Definition 3.7) on
  some germ of neighbourhoods `G'` of `0` in `C'` with `G'₀ ⊆ U'`.  sc-smoothness of `g` itself is
  not assumed (it follows near `0`).
- "`s` an sc⁺-germ": an sc-smooth germ `s : O(C, 0) → F¹` on `G` (`IsScSmoothGerm` with target
  `F.shift`).  Added hypothesis `s(0) = 0`: it is presupposed (the text's germs are
  `O(C, 0) → (F, 0)`; without it `(g + s)(0) = s(0) ≠ 0` while basic germs vanish at `0` and strong
  bundle isomorphisms are fibrewise linear, so the claim would fail).
- "there is a strong bundle map `Ψ`": read as a strong bundle *isomorphism* (needed for the
  push-forward `(Ψ ∘ Φ)_*` to make sense; Theorem 3.38 produces one):
  `Ψ : U₁ ◁ (ℝᴺ ⊕ W) → U'' ◁ (ℝ^{N'} ⊕ W')` with inverse `Ψ'`, `U₁ ⊆ U'` a relatively open
  neighbourhood of `0` in `C'`, `U''` relatively open in `C̃' × W'` (`C̃' ⊆ ℝ^{n'}` a partial
  quadrant), `ψ(0) = 0`.  `(Ψ ∘ Φ)_*(g + s)` is `pushforward (Ψ ∘ Φ) (Φ' ∘ Ψ') (g + s)` (with
  `F₁ → F₀` for `s`).
- "`(…)¹` is a basic germ": the level-raised germ is a basic germ (`IsRaisedBasic`, as in V3_34:
  some basic germ on a germ of neighbourhoods of `0` in `C̃' ⊕ W'¹` agrees with the push-forward on
  level `1` inside `U''`).
- Nothing else in the statement looks false to me.
-/
namespace RoundTrip.V3_76
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

/-- Corollary 3.39: if `Φ_*(g)` is a basic germ for a strong bundle isomorphism `Φ` and `s` is an
sc⁺-germ (with `s(0) = 0`), then there is a strong bundle isomorphism `Ψ` such that
`((Ψ ∘ Φ)_*(g + s))¹` is a basic germ. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C : Set (E.lvl 0)) (G : ScNbhdGerm E C)
    (g : E.lvl 0 → F.lvl 0) (s : E.lvl 0 → F.shift.lvl 0)
    (n N : ℕ) (W : ScBanach) (Ct : Set (Fin n → ℝ))
    (U : Set (E.lvl 0)) (U' : Set ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0))
    (Φ : E.lvl 0 × F.lvl 0 →
      (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0)
    (Φ' : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0 →
      E.lvl 0 × F.lvl 0),
    IsPartialQuadrant E C →
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) Ct →
    IsRelOpenInQuadrant E C U → 0 ∈ U → U ⊆ G.U 0 →
    IsRelOpenInQuadrant (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) U' →
    IsStrongBundleIso U U' Φ Φ' → IsStrongBundleMap.base Φ 0 = 0 →
    (∃ (G' : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
        (Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0),
        G'.U 0 ⊆ U' ∧ IsBasicGerm Ct G' (pushforward Φ Φ' g) Bm) →
    IsScSmoothGerm (F := F.shift) G s → s 0 = 0 →
    ∃ (n' N' : ℕ) (W' : ScBanach) (Ct' : Set (Fin n' → ℝ))
      (U₁ : Set ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0))
      (U'' : Set ((ScBanach.paramProd (Fin n' → ℝ) W').lvl 0))
      (Ψ : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0 →
        (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0 × (ScBanach.paramProd (Fin N' → ℝ) W').lvl 0)
      (Ψ' : (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0 ×
          (ScBanach.paramProd (Fin N' → ℝ) W').lvl 0 →
        (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0),
      IsPartialQuadrant (ScBanach.const (Fin n' → ℝ)) Ct' ∧
      IsRelOpenInQuadrant (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) U₁ ∧
      0 ∈ U₁ ∧ U₁ ⊆ U' ∧
      IsRelOpenInQuadrant (ScBanach.paramProd (Fin n' → ℝ) W') (Ct' ×ˢ Set.univ) U'' ∧
      IsStrongBundleIso U₁ U'' Ψ Ψ' ∧ IsStrongBundleMap.base Ψ 0 = 0 ∧
      IsRaisedBasic Ct' U''
        (pushforward (Ψ ∘ Φ) (Φ' ∘ Ψ') (fun x => g x + F.toBase 1 (s x)))

end RoundTrip.V3_76
