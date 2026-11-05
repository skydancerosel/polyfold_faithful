import Polyfold
/-! Blind formalization of V3_38 (the text's §3.5, Theorem 3.43, p. 102). Choices:
- Setting: `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (constant sc-structures), `C̃ ⊆ ℝⁿ` a partial
  quadrant, `W` an arbitrary sc-Banach space; `E = ℝⁿ ⊕ W` (`ScBanach.paramProd (Fin n → ℝ) W`)
  with the partial quadrant `C = C̃ × W`, target `F = ℝᴺ ⊕ W`; primed data `n', N', C̃' ⊆ ℝ^{n'}`,
  `W'`, `E' = ℝ^{n'} ⊕ W'`, `C' = C̃' × W'`, `F' = ℝ^{N'} ⊕ W'` likewise.  No universe choices.
- "`f = h + s`" (the setting of §3.5, Theorems 3.38/3.40): `h` a basic germ (`IsBasicGerm C̃ G h B`,
  Definition 3.7) on a germ of neighbourhoods `G`, `s` an sc⁺-germ (sc-smooth germ into `F¹`,
  `IsScSmoothGerm` with target `F.shift`) with `s(0) = 0`, on the same `G`; `f = h + s` (with
  `F₁ → F₀`); `U ⊆ G₀` below is the domain.
- "`Df(0)` surjective": `Df(0) = D 0` for *any* derivative family `D` of the sc¹-germ `f`
  (`IsSc1GermWith G f D`; the derivative at the smooth point `0` is unique), onto `F₀`.
- "`K = ker Df(0)` in good position to `C`" (Definition 3.21): `K` finite-dimensional (an
  instance hypothesis), `K ∩ C` with nonempty interior in `K`, and a good complement
  (`IsInGoodPositionSc`).  Good complement (`IsGoodComplementSc`, defined here): an
  *sc-complement* `Y` (`E.IsScSplitting K Y`) with `ε > 0` such that `k ∈ C ⟺ k + y ∈ C` for
  `|y|₀ ≤ ε|k|₀`.  (The project's `IsGoodComplement`, an algebraic complement, was not used.)
- "`g = Φ_*(f)`": `Φ` is a strong bundle isomorphism as produced by Theorem 3.38 (V3_34), and the
  claim is made for *every* such `Φ`: `IsStrongBundleIso U U' Φ Φ'` with `U` a relatively open
  neighbourhood of `0` in `C` inside `G₀`, `U'` relatively open in `C'`, `φ = base Φ` with
  `φ(0) = 0`, and `g = pushforward Φ Φ' f` whose level-raised germ `g¹` is a basic germ
  (`IsRaisedBasic`, as in V3_34).  (Theorem 3.38 also gives `n − N = n' − N'`; not needed here.)
- "`K' = ker Dg(0)`": `g` is an sc¹-germ on some germ of neighbourhoods `G'` of `0` in `C'` inside
  `U'` with derivative family `D'` (asserted, since `Dg(0)` must exist), and `K' = ker D'(0)`;
  `K'` is finite-dimensional and in good position to `C'` (`IsInGoodPositionSc`).
- "a good complement `Y'` and a `C¹` map `τ : V → Y'₁`, `V` relatively open in `K' ∩ C'`, with (1)
  `τ` an sc-smooth germ; (2) `τ(0) = 0`, `Dτ(0) = 0`" (`IsGraphSolution`, defined here): `Y'` a
  good complement of `K'`, `V ⊆ K'` relatively open in `K' ∩ C'` with `0 ∈ V`, `τ : K' → E'₁` with
  values in `Y'` (under `E'₁ → E'₀`), `C¹` on `V` into `E'₁` (`ContDiffOn ℝ 1`), an sc-smooth germ
  (`IsScSmoothGerm`) from `O(K' ∩ C', 0)` (`K'` with the constant sc-structure) into `E'¹` on some
  germ of neighbourhoods inside `V` (the declared codomain `Y'₁` is level `0` of `Y'¹ ⊆ E'¹`),
  `τ(0) = 0`, and `Dτ(0) = 0` (derivative within `V`, into `E'₁`).
- "(3) after shrinking `U`, `φ({f = 0}) = {g = 0} = {y + τ(y) | y ∈ V}`": there is a relatively
  open neighbourhood `U₀ ⊆ U` of `0` in `C` with `φ({x ∈ U₀ | f(x) = 0}) = {x' ∈ φ(U₀) | g(x') = 0}`
  and the latter equal to `{y + τ(y) | y ∈ V}` (`τ(y)` included into `E'₀`).
- Doubt: reading (1) with codomain `E'¹` (rather than `E'`) is the stronger of the two readings;
  I chose it because the statement declares `τ : V → Y'₁`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_38
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

/-- The local solution data: `Y` a good complement of `N`, `V` a relatively open neighbourhood of
`0` in `N ∩ C`, `τ : V → Y₁` of class `C¹`, an sc-smooth germ into `E¹`, `τ(0) = 0`, `Dτ(0) = 0`. -/
def IsGraphSolution (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0))
    [FiniteDimensional ℝ N] (Y : Submodule ℝ (E.lvl 0)) (V : Set N) (τ : N → E.lvl 1) : Prop :=
  IsGoodComplementSc E C N Y ∧
  (∃ O : Set N, IsOpen O ∧ V = O ∩ (Subtype.val ⁻¹' C)) ∧ (0 : N) ∈ V ∧
  (∀ v ∈ V, E.toBase 1 (τ v) ∈ Y) ∧
  ContDiffOn ℝ 1 τ V ∧
  (∃ Vg : ScNbhdGerm (ScBanach.const N) (Subtype.val ⁻¹' C : Set N),
      Vg.U 0 ⊆ V ∧ IsScSmoothGerm (F := E.shift) Vg τ) ∧
  τ 0 = 0 ∧ HasFDerivWithinAt τ (0 : N →L[ℝ] E.lvl 1) V 0

/-- The graph `{v + τ(v) | v ∈ V} ⊆ E₀` of `τ : V → E₁` over `V ⊆ N`. -/
def graphSet (E : ScBanach) {N : Submodule ℝ (E.lvl 0)} (V : Set N) (τ : N → E.lvl 1) :
    Set (E.lvl 0) :=
  {x | ∃ v ∈ V, x = (v : E.lvl 0) + E.toBase 1 (τ v)}

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

/-- The conclusion of Theorem 3.43 for `f : U → F`, the base map `φ : U → U'` and `g = Φ_*(f)`:
`K' = ker Dg(0)` is in good position to `C'`, there are `Y'`, `V`, `τ` as in `IsGraphSolution`, and
after shrinking `U` to `U₀`: `φ({f = 0}) = {g = 0} = {y + τ(y) | y ∈ V}`. -/
def Concl (E F E' F' : ScBanach) (C U : Set (E.lvl 0)) (C' U' : Set (E'.lvl 0))
    (f : E.lvl 0 → F.lvl 0) (φ : E.lvl 0 → E'.lvl 0) (g : E'.lvl 0 → F'.lvl 0) : Prop :=
  ∃ (G' : ScNbhdGerm E' C') (D' : E'.lvl 1 → E'.lvl 0 →L[ℝ] F'.lvl 0),
    G'.U 0 ⊆ U' ∧ IsSc1GermWith G' g D' ∧
    ∃ (_ : FiniteDimensional ℝ (kerOf (D' 0))),
      IsInGoodPositionSc E' C' (kerOf (D' 0)) ∧
      ∃ (Y' : Submodule ℝ (E'.lvl 0)) (V : Set (kerOf (D' 0))) (τ : kerOf (D' 0) → E'.lvl 1),
        IsGraphSolution E' C' (kerOf (D' 0)) Y' V τ ∧
        ∃ U₀ : Set (E.lvl 0), IsRelOpenInQuadrant E C U₀ ∧ 0 ∈ U₀ ∧ U₀ ⊆ U ∧
          φ '' {x | x ∈ U₀ ∧ f x = 0} = {x' | x' ∈ φ '' U₀ ∧ g x' = 0} ∧
          {x' | x' ∈ φ '' U₀ ∧ g x' = 0} = graphSet E' V τ

/-- Theorem 3.43: for `f = h + s` with `Df(0)` onto and `ker Df(0)` in good position, and
`g = Φ_*(f)` with `g¹` basic (Theorem 3.38), `ker Dg(0)` is in good position, and near `0` the
zero sets `φ({f = 0}) = {g = 0}` are the graph of a `C¹`, sc-smooth germ `τ : V → Y'₁` with
`τ(0) = 0`, `Dτ(0) = 0`. -/
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
        Concl (ScBanach.paramProd (Fin n → ℝ) W) (ScBanach.paramProd (Fin N → ℝ) W)
          (ScBanach.paramProd (Fin n' → ℝ) W') (ScBanach.paramProd (Fin N' → ℝ) W')
          (Ct ×ˢ Set.univ) U (Ct' ×ˢ Set.univ) U' f (IsStrongBundleMap.base Φ)
          (pushforward Φ Φ' f)

end RoundTrip.V3_38
