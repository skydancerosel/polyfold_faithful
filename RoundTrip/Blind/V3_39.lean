import Polyfold
/-! Blind formalization of V3_39 (the text's §3.5, Lemma 3.44, p. 103). Choices:
- Setting: the lemma sits in the proof of Theorem 3.43, so I take the hypotheses of Theorem 3.43
  exactly as in the blind V3_38: `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ`, `C̃ ⊆ ℝⁿ` a partial quadrant,
  `W` an sc-Banach space, `E = ℝⁿ ⊕ W` with `C = C̃ × W`, `F = ℝᴺ ⊕ W`, and primed data likewise;
  `f = h + s` (`h` basic, `IsBasicGerm`; `s` an sc⁺-germ, sc-smooth into `F¹`, `s(0) = 0`);
  `Df(0) = D 0` onto for a derivative family `D` of `f` (`IsSc1GermWith`), `K = ker Df(0)`
  finite-dimensional and in good position to `C` (`IsInGoodPositionSc`: Definition 3.21 with an
  *sc-complement*, defined here as in V3_38; the project's `IsGoodComplement` was not used); every
  strong bundle isomorphism `Φ` as in Theorem 3.38 (`IsStrongBundleIso U U' Φ Φ'`, `0 ∈ U ⊆ G₀`
  relatively open in `C`, `U'` relatively open in `C'`, `φ(0) = 0`), `g = Φ_*(f)`
  (`pushforward`).  (The lemma's proof needs neither the surjectivity nor the good position; they
  are kept as the ambient hypotheses.)
- "`g¹` basic" / "`δ`": as in my blind V3_37, any basic germ `g₁` (on `G₁`, contraction map `B₁`)
  agreeing with `g` on level 1 inside `U'`, and any representative `(V_δ, δ)` of the solution germ
  of `P' ∘ g¹ = w − B₁(a, w)` (`IsSolGerm`, fibre `W'¹`, so `δ : C̃' → W'₁`).
- "`Dg(0)`": `D' 0` for any derivative family `D'` of the sc¹-germ `g` on a germ of
  neighbourhoods `G'` of `0` in `C'` inside `U'` (`IsSc1GermWith`); `K' = ker Dg(0)` (`kerOf`).
- "`H(a) = (1 − P') ∘ g(a, δ(a))`": the `ℝ^{N'}`-component of `g(a, ι δ(a))` (`ι : W'₁ → W'₀`);
  `(1 − P')` as a map to `ℝ^{N'}` (same kernel as into `F'`).
- "`Dδ(0)`", "`DH(0)`": any `L, M` with `δ : ℝⁿ' → W'₁` and `H` having derivatives `L`, `M` at `0`
  within `C̃'` (`HasFDerivWithinAt`; unique since `C̃'` is convex with nonempty interior).
  `K̃ = ker DH(0) ⊆ ℝ^{n'}`.
- "`α ↦ (α, Dδ(0)α)` induces a linear isomorphism `K̃ → K'`": there is a linear equivalence
  `e : K̃ ≃ K'` with `e(α) = (α, ι Dδ(0) α)` in `E'₀` (this includes that the map lands in `K'`).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_39
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

/-- `δ` is a solution germ of `f = w − B(a, w)` on the germ of neighbourhoods `V`: an sc⁰-germ with
`δ(0) = 0`, `(v, δ v)` in the domain of `f` and `f(v, δ v) = 0` for `v ∈ V₀`. -/
def IsSolGerm {n : ℕ} {W : ScBanach} {Ct : Set (Fin n → ℝ)}
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0)
    (V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) (δ : (Fin n → ℝ) → W.lvl 0) : Prop :=
  IsSc0Germ V δ ∧ δ 0 = 0 ∧
    ∀ a ∈ V.U 0, ((a, δ a) : (Fin n → ℝ) × W.lvl 0) ∈ G.U 0 ∧ contractionMap Bm (a, δ a) = 0

/-- Lemma 3.44: with `H(a) = (1 − P') g(a, δ(a))`, the map `α ↦ (α, Dδ(0)α)` induces a linear
isomorphism `K̃ = ker DH(0) → ker Dg(0) = K'`. -/
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
      ∀ (G' : ScNbhdGerm (ScBanach.paramProd (Fin n' → ℝ) W') (Ct' ×ˢ Set.univ))
        (D' : (ScBanach.paramProd (Fin n' → ℝ) W').lvl 1 →
          (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0 →L[ℝ]
            (ScBanach.paramProd (Fin N' → ℝ) W').lvl 0),
        G'.U 0 ⊆ U' → IsSc1GermWith G' g D' →
      let H : (Fin n' → ℝ) → (Fin N' → ℝ) := fun a => (g (a, W'.incl 0 (δ a))).1
      ∀ (L : (Fin n' → ℝ) →L[ℝ] W'.lvl 1) (M : (Fin n' → ℝ) →L[ℝ] (Fin N' → ℝ)),
        HasFDerivWithinAt δ L Ct' 0 → HasFDerivWithinAt H M Ct' 0 →
        ∃ e : LinearMap.ker (M : (Fin n' → ℝ) →ₗ[ℝ] (Fin N' → ℝ)) ≃ₗ[ℝ] kerOf (D' 0),
          ∀ α : LinearMap.ker (M : (Fin n' → ℝ) →ₗ[ℝ] (Fin N' → ℝ)),
            ((e α : (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0) : (Fin n' → ℝ) × W'.lvl 0) =
              ((α : Fin n' → ℝ), W'.incl 0 (L α))

end RoundTrip.V3_39
