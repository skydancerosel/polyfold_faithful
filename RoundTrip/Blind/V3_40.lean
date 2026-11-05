import Polyfold
/-! Blind formalization of V3_40 (the text's §3.5, Lemma 3.45, p. 104). Choices:
- Setting: the lemma sits in the proof of Theorem 3.43, so I take the hypotheses of Theorem 3.43
  exactly as in the blind V3_38: `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ`, `C̃ ⊆ ℝⁿ` a partial quadrant,
  `W` an sc-Banach space, `E = ℝⁿ ⊕ W` with `C = C̃ × W`, `F = ℝᴺ ⊕ W`, primed data likewise
  (`E' = ℝ^{n'} ⊕ W'`, `C' = C̃' × W'`); `f = h + s` (`h` basic, `IsBasicGerm`; `s` an sc⁺-germ,
  sc-smooth into `F¹`, `s(0) = 0`); `Df(0) = D 0` onto for a derivative family `D` of `f`
  (`IsSc1GermWith`); `K = ker Df(0)` finite-dimensional and in good position to `C`
  (`IsInGoodPositionSc`, Definition 3.21 with an *sc-complement*, as in V3_38; the project's
  `IsGoodComplement` was not used); every strong bundle isomorphism `Φ` as in Theorem 3.38
  (`IsStrongBundleIso U U' Φ Φ'`, `0 ∈ U ⊆ G₀` relatively open in `C`, `U'` relatively open in
  `C'`, `φ = base Φ` with `φ(0) = 0`, `g = Φ_*(f)` with `g¹` basic: `IsRaisedBasic` as in V3_34).
- "`K^⊥`": any good complement of `K` with respect to `C` (`IsGoodComplementSc E C K K^⊥`; the
  good position of `K` provides one).
- "`Tφ(0)`": `Dφ(0) = Dφ 0 : E₀ → E'₀` for any derivative family `Dφ` of the sc¹ map
  `φ : U → E'` (`IsSc1With U φ Dφ`, Definition 1.14; `φ` is an sc-diffeomorphism, and the
  derivative at the smooth point `0 ∈ U` is unique).
- "`K' = Tφ(0)K`" and "`(K')^⊥ = Tφ(0)(K^⊥)`" are read as the definitions of the two subspaces
  (images `Submodule.map`); the identity `K' = ker Dg(0)` of the surrounding proof is not part of
  the claim.
- "is a good complement of `K'` in `E'`": `IsGoodComplementSc E' C' (Tφ(0)K) (Tφ(0)K^⊥)` (an
  sc-complement with the `ε`-condition for `C'`).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_40
open Polyfold

/-- Definition 3.21 (complement): `Y` is a good complement of `N` with respect to `C`: an
sc-complement (`E_m = N_m ⊕ Y_m` on every level) with `n ∈ C ⟺ n + y ∈ C` for `|y|₀ ≤ ε|n|₀`. -/
def IsGoodComplementSc (E : ScBanach) (C : Set (E.lvl 0)) (N Y : Submodule ℝ (E.lvl 0)) :
    Prop :=
  E.IsScSplitting N Y ∧ ∃ ε > 0, ∀ x ∈ N, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + y ∈ C)

/-- Definition 3.21: the (finite-dimensional) subspace `N` is in good position to `C`: `N ∩ C` has
nonempty interior in `N` and `N` has a good complement. -/
def IsInGoodPositionSc (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0)) : Prop :=
  (interior (Subtype.val ⁻¹' C : Set N)).Nonempty ∧ ∃ Y, IsGoodComplementSc E C N Y

/-- The kernel `ker L ⊆ E₀` of a bounded operator `L : E₀ → F₀`. -/
def kerOf {E F : ScBanach} (L : E.lvl 0 →L[ℝ] F.lvl 0) : Submodule ℝ (E.lvl 0) :=
  LinearMap.ker (L : E.lvl 0 →ₗ[ℝ] F.lvl 0)

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

/-- Lemma 3.45: in the setting of Theorem 3.43, for a good complement `K^⊥` of `K = ker Df(0)`,
`Tφ(0)(K^⊥)` is a good complement of `K' = Tφ(0)K` in `E'` (with respect to `C'`). -/
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
    ∀ D : (ScBanach.paramProd (Fin n → ℝ) W).lvl 1 →
        (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 →L[ℝ] (ScBanach.paramProd (Fin N → ℝ) W).lvl 0,
      IsSc1GermWith G f D → Function.Surjective (D 0) →
      ∀ [FiniteDimensional ℝ (kerOf (D 0))],
      IsInGoodPositionSc (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) (kerOf (D 0)) →
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
      IsRaisedBasic Ct' U' (pushforward Φ Φ' f) →
    ∀ Kperp : Submodule ℝ ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0),
      IsGoodComplementSc (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) (kerOf (D 0)) Kperp →
    ∀ Dφ : (ScBanach.paramProd (Fin n → ℝ) W).lvl 1 →
        (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 →L[ℝ] (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0,
      IsSc1With U (IsStrongBundleMap.base Φ) Dφ →
      IsGoodComplementSc (ScBanach.paramProd (Fin n' → ℝ) W') (Ct' ×ˢ Set.univ)
        ((kerOf (D 0)).map (Dφ 0 : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 →ₗ[ℝ]
          (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0))
        (Kperp.map (Dφ 0 : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 →ₗ[ℝ]
          (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0))

end RoundTrip.V3_40
