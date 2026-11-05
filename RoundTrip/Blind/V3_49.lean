import Polyfold
/-! Blind formalization of V3_49 (the text's §3.6, Lemma 3.55, p. 114; proof §3.8.3). Choices:
- Setting: `E` an arbitrary sc-Banach space and `C ⊆ E₀` a partial quadrant, given with a
  presentation `T : E ≅ ℝⁿ ⊕ W` (an sc-isomorphism, the project's `ScIso`), `C = T⁻¹([0,∞)ⁿ ⊕ W)`
  (`quadOf T`; every partial quadrant is of this form, Definition 1.11).  The presentation is
  needed to name `C_x` (below); the claim is made for every presentation.  No universe choices.
- `C_x` (Definition 2.33, the partial quadrant at `x`): `C_x = ⋂_{i ∈ I(x)} H_i`, `I(x)` the
  indices of the half-line coordinates vanishing at `x`, `H_i = {h | (Th)_i ≥ 0}` (`quadAt T x`,
  defined here).  `C_x` does not depend on the presentation; the claim is stated with the
  presentation of `C` that is quantified.
- "`N` a finite-dimensional smooth subspace in good position with good complement `Y`"
  (Definition 3.21): `N` finite-dimensional (instance), `N ⊆ E_∞` (`N ≤ E.smooth`), `N ∩ C` has
  nonempty interior in `N`, and `Y` is a good complement: an *sc-complement* of `N`
  (`E.IsScSplitting N Y`) with `ε > 0` such that `n ∈ C ⟺ n + y ∈ C` whenever `n ∈ N`, `y ∈ Y`,
  `|y|₀ ≤ ε|n|₀` (`IsGoodComplementSc`, as in my earlier blind files V3_38/V3_42).
- "`V ⊆ N ∩ C` relatively open": `V = O ∩ (N ∩ C)` with `O` open in `N` (seen in the type `N`),
  and `0 ∈ V` (presupposed by `τ(0) = 0`).
- "`τ : V → Y₁` of class `C¹` with `τ(0) = 0`, `Dτ(0) = 0`": `τ : N → E₁` with values in `Y` (under
  `ι₁ : E₁ → E₀`) on `V`, `ContDiffOn ℝ 1 τ V` into `E₁`, `τ(0) = 0`, and derivative `0` at `0`
  within `V` (into `E₁`).  `Dτ(v)` below is `fderivWithin ℝ τ V v : N → E₁` (`V` is a relatively
  open piece of the convex set `N ∩ C` with nonempty interior, so this derivative is unique).
- Conclusion: there is `V'` relatively open in `N ∩ C` with `0 ∈ V'` and `V' ⊆ V` (presupposed:
  `τ(v)` must be defined), such that for every `v ∈ V'`, with `x = v + τ(v)`:
  (1) "`v + τ(v) ∈ C₁`": `x ∈ C` and `x` lies on level `1` (it is `ι₁` of a point of `E₁`);
  (2) "`Y` is a topological complement of `N_v = {n + Dτ(v)n}`" (`Nv`, defined here, a subspace of
  `E₀`, `Dτ(v)n` seen in `E₀`): `IsCompl N_v Y`.  `N_v` is finite-dimensional and `Y` is closed
  (an sc-complement), so the algebraic complement is automatically topological;
  (3) there is `γ_v > 0` with `n ∈ C_x ⟺ n + y ∈ C_x` for `n ∈ N_v`, `y ∈ Y`, `|y|₀ ≤ γ_v|n|₀`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_49
open Polyfold

/-- The partial quadrant `C = T⁻¹([0,∞)ⁿ ⊕ W)` of a presentation `T : E ≅ ℝⁿ ⊕ W`. -/
def quadOf {E W : ScBanach} {n : ℕ} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    Set (E.lvl 0) :=
  {x | ∀ i, 0 ≤ ((T.lvl 0) x).1 i}

/-- Definition 2.33: the partial quadrant `C_x = ⋂_{i ∈ I(x)} H_i` at `x`, where `I(x)` is the set
of indices `i` with `(Tx)_i = 0` and `H_i = {h | (Th)_i ≥ 0}`. -/
def quadAt {E W : ScBanach} {n : ℕ} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (x : E.lvl 0) : Set (E.lvl 0) :=
  {h | ∀ i, ((T.lvl 0) x).1 i = 0 → 0 ≤ ((T.lvl 0) h).1 i}

/-- Definition 3.21 (complement): `Y` is a good complement of `N` with respect to `C`: an
sc-complement (`E_m = N_m ⊕ Y_m` on every level) with `n ∈ C ⟺ n + y ∈ C` for `|y|₀ ≤ ε|n|₀`. -/
def IsGoodComplementSc (E : ScBanach) (C : Set (E.lvl 0)) (N Y : Submodule ℝ (E.lvl 0)) :
    Prop :=
  E.IsScSplitting N Y ∧ ∃ ε > 0, ∀ x ∈ N, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + y ∈ C)

/-- `N_v = {n + Dτ(v)n | n ∈ N} ⊆ E₀` for `L = Dτ(v) : N → E₁`. -/
def Nv {E : ScBanach} (N : Submodule ℝ (E.lvl 0)) (L : N →L[ℝ] E.lvl 1) :
    Submodule ℝ (E.lvl 0) :=
  LinearMap.range ((N.subtypeL + (E.toBase 1).comp L : N →L[ℝ] E.lvl 0) : N →ₗ[ℝ] E.lvl 0)

/-- Lemma 3.55: for `N` in good position to `C` with good complement `Y` and a `C¹` map
`τ : V → Y₁` with `τ(0) = 0`, `Dτ(0) = 0`, near `0` in `N ∩ C`: (1) `v + τ(v) ∈ C₁`; (2) `Y` is a
topological complement of `N_v = {n + Dτ(v)n}`; (3) `N_v` and `Y` satisfy the good-position
estimate with respect to `C_x`, `x = v + τ(v)`, with a constant `γ_v > 0`. -/
def B : Prop :=
  ∀ (E W : ScBanach) (n : ℕ) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (N Y : Submodule ℝ (E.lvl 0)) [FiniteDimensional ℝ N] (V : Set N) (τ : N → E.lvl 1),
    N ≤ E.smooth →
    (interior (Subtype.val ⁻¹' quadOf T : Set N)).Nonempty →
    IsGoodComplementSc E (quadOf T) N Y →
    (∃ O : Set N, IsOpen O ∧ V = O ∩ (Subtype.val ⁻¹' quadOf T)) → (0 : N) ∈ V →
    (∀ v ∈ V, E.toBase 1 (τ v) ∈ Y) →
    ContDiffOn ℝ 1 τ V → τ 0 = 0 → HasFDerivWithinAt τ (0 : N →L[ℝ] E.lvl 1) V 0 →
    ∃ V' : Set N, (∃ O' : Set N, IsOpen O' ∧ V' = O' ∩ (Subtype.val ⁻¹' quadOf T)) ∧
      (0 : N) ∈ V' ∧ V' ⊆ V ∧
      ∀ v ∈ V',
        -- (1) `x = v + τ(v) ∈ C₁`
        ((v : E.lvl 0) + E.toBase 1 (τ v) ∈ quadOf T ∧
          ∃ x₁ : E.lvl 1, E.toBase 1 x₁ = (v : E.lvl 0) + E.toBase 1 (τ v)) ∧
        -- (2) `E₀ = N_v ⊕ Y`
        IsCompl (Nv N (fderivWithin ℝ τ V v)) Y ∧
        -- (3) the good-position estimate for `N_v`, `Y` and `C_x`
        ∃ γ > 0, ∀ m ∈ Nv N (fderivWithin ℝ τ V v), ∀ y ∈ Y, ‖y‖ ≤ γ * ‖m‖ →
          (m ∈ quadAt T ((v : E.lvl 0) + E.toBase 1 (τ v)) ↔
            m + y ∈ quadAt T ((v : E.lvl 0) + E.toBase 1 (τ v)))

end RoundTrip.V3_49
