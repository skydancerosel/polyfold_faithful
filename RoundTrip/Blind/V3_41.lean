import Polyfold
/-! Blind formalization of V3_41 (the text's §3.5, Lemma 3.46, p. 104; proof §3.8.2). Choices:
- Setting: the proof of Theorem 3.43, with the hypotheses of Theorem 3.43 taken over from my
  blind file V3_38.  `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (constant sc-structures), `C̃ ⊆ ℝⁿ` a
  partial quadrant, `W` an arbitrary sc-Banach space, `E = ℝⁿ ⊕ W`
  (`ScBanach.paramProd (Fin n → ℝ) W`) with `C = C̃ × W`, `F = ℝᴺ ⊕ W`; `f = h + s` with `h` a
  basic germ (`IsBasicGerm`) on a germ of neighbourhoods `G` and `s` an sc⁺-germ (sc-smooth germ
  into `F¹`) with `s(0) = 0`; `Df(0)` (for any derivative family `D` of the sc¹-germ `f`)
  surjective; `K = ker Df(0)` finite-dimensional and in good position to `C`
  (`IsInGoodPositionSc`, Definition 3.21 with the text's *sc-complement*, `IsGoodComplementSc`).
  The primed data: `ℝ^{n'}`, `ℝ^{N'}`, `C̃' ⊆ ℝ^{n'}` a partial quadrant, `W'`,
  `E' = ℝ^{n'} ⊕ W'`, `C' = C̃' × W'`, `F' = ℝ^{N'} ⊕ W'`; `Φ : U ◁ F → U' ◁ F'` a strong bundle
  isomorphism (`IsStrongBundleIso`) with `φ(0) = 0`, `U ⊆ G₀` and `U'` relatively open, and
  `g = Φ_*(f)` (`pushforward Φ Φ' f`).  No universe choices arise.
- "`g¹` basic" (Theorem 3.38): the data are named, since `δ` is built from them: a basic germ
  `g₁` on a germ of neighbourhoods `G₁` of `0` in `C̃' ⊕ W'¹`, with contraction map `B₁`, which
  agrees with `g` on level `1` inside `U'` (as `IsRaisedBasic` in V3_38).  `P'` is the projection
  `ℝ^{N'} ⊕ W' → W'`; `P' ∘ g¹ = w − B₁(a, w)` is the contraction germ.
- "`δ` the solution germ of `P' ∘ g¹`" (Theorem 3.29): any `δ : C̃' → W'₁` that is continuous into
  `W'₁` on a relatively open neighbourhood `V_δ` of `0` in `C̃'`, with `δ(0) = 0`, `(a, δ(a)) ∈ G₁₀`
  and `P'g¹(a, δ(a)) = 0` for `a ∈ V_δ`.  Near `0` such a `δ` is unique (the contraction property on
  level `0` of `W'¹`), so this is the solution germ on level `0`, all that `H` and `DH(0)` see.
- "`H(a) = (1 − P') ∘ g(a, δ(a))`" (from Lemma 3.44's statement): the `ℝ^{N'}`-component of
  `g(a, ι δ(a))`, `ι : W'₁ → W'₀`.  "`DH(0)`": any `L : ℝ^{n'} → ℝ^{N'}` with
  `HasFDerivWithinAt H L C̃' 0` (unique, `C̃'` being a partial quadrant).  The existence of `DH(0)`
  is presupposed by the statement and taken as a hypothesis (the text establishes it earlier).
  `K̃ = ker L`.
- "`K' = ker Dg(0)`": for any derivative family `D'` of `g` as an sc¹-germ on a germ of
  neighbourhoods `G'` of `0` in `C'` inside `U'` (the derivative at the smooth point `0` is
  unique), `K' = ker D'(0)` (`kerOf`).
- Claim: (a) `K̃` is in good position to `C̃'` in `ℝ^{n'}` (`IsInGoodPositionSc` for the constant
  sc-structure, where an sc-complement is an algebraic complement); (b) there is a good complement
  `Z` of `K̃` in `ℝ^{n'}` such that `Z ⊕ W'` (`Z.prod ⊤ ⊆ ℝ^{n'} × W'₀`) is a good complement of
  `K'` in `E'` with respect to `C'` (sc-complement with the `ε` property, `IsGoodComplementSc`).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_41
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

/-- Lemma 3.46: in the proof of Theorem 3.43 (`f = h + s`, `Df(0)` onto, `ker Df(0)` in good
position, `g = Φ_*(f)` with `g¹` basic, `δ` the solution germ of `P' ∘ g¹`,
`H(a) = (1 − P')g(a, δ(a))`), `K̃ = ker DH(0)` is in good position to `C̃'` and has a good
complement `Z` in `ℝ^{n'}` such that `Z ⊕ W'` is a good complement of `K' = ker Dg(0)`. -/
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
        -- `g¹` is the basic germ `g₁` (contraction map `B₁`)
        ∀ (G₁ : ScNbhdGerm (ScBanach.paramProd (Fin n' → ℝ) W'.shift) (Ct' ×ˢ Set.univ))
          (g₁ : (Fin n' → ℝ) × W'.lvl 1 → (Fin N' → ℝ) × W'.lvl 1)
          (B₁ : (Fin n' → ℝ) × W'.lvl 1 → W'.lvl 1),
          IsBasicGerm Ct' G₁ g₁ B₁ →
          (∀ x ∈ G₁.U 0,
            (((x.1, W'.incl 0 x.2) : (Fin n' → ℝ) × W'.lvl 0) ∈ U') ∧
              pushforward Φ Φ' f (x.1, W'.incl 0 x.2) = ((g₁ x).1, W'.incl 0 (g₁ x).2)) →
        -- `δ` the solution germ of `P' ∘ g¹`
        ∀ (Vδ : Set (Fin n' → ℝ)) (δ : (Fin n' → ℝ) → W'.lvl 1),
          (∃ O : Set (Fin n' → ℝ), IsOpen O ∧ Vδ = O ∩ Ct') → 0 ∈ Vδ →
          ContinuousOn δ Vδ → δ 0 = 0 →
          (∀ a ∈ Vδ, ((a, δ a) : (Fin n' → ℝ) × W'.lvl 1) ∈ G₁.U 0 ∧ (g₁ (a, δ a)).2 = 0) →
        -- `L = DH(0)`, `H(a) = (1 − P') g(a, δ(a))`
        ∀ L : (Fin n' → ℝ) →L[ℝ] (Fin N' → ℝ),
          HasFDerivWithinAt (fun a => (pushforward Φ Φ' f (a, W'.incl 0 (δ a))).1) L Ct' 0 →
        -- `D'(0) = Dg(0)`
        ∀ (G' : ScNbhdGerm (ScBanach.paramProd (Fin n' → ℝ) W') (Ct' ×ˢ Set.univ))
          (D' : (ScBanach.paramProd (Fin n' → ℝ) W').lvl 1 →
            (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0 →L[ℝ]
              (ScBanach.paramProd (Fin N' → ℝ) W').lvl 0),
          G'.U 0 ⊆ U' → IsSc1GermWith G' (pushforward Φ Φ' f) D' →
        -- the claim
        IsInGoodPositionSc (ScBanach.const (Fin n' → ℝ)) Ct'
            (LinearMap.ker (L : (Fin n' → ℝ) →ₗ[ℝ] (Fin N' → ℝ))) ∧
          ∃ Z : Submodule ℝ (Fin n' → ℝ),
            IsGoodComplementSc (ScBanach.const (Fin n' → ℝ)) Ct'
              (LinearMap.ker (L : (Fin n' → ℝ) →ₗ[ℝ] (Fin N' → ℝ))) Z ∧
            IsGoodComplementSc (ScBanach.paramProd (Fin n' → ℝ) W') (Ct' ×ˢ Set.univ)
              (kerOf (D' 0)) (Z.prod (⊤ : Submodule ℝ (W'.lvl 0)))

end RoundTrip.V3_41
