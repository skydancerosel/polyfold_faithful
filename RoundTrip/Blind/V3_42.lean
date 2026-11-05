import Polyfold
/-! Blind formalization of V3_42 (the text's §3.5, Corollary 3.47, p. 106). Choices:
- Setting ("the hypotheses of Theorem 3.43", as I read them from V3_38's statement):
  `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (constant sc-structures), `C̃ ⊆ ℝⁿ` a partial quadrant,
  `W` an arbitrary sc-Banach space; `E = ℝⁿ ⊕ W` (`ScBanach.paramProd (Fin n → ℝ) W`) with the
  partial quadrant `C = C̃ × W`, target `F = ℝᴺ ⊕ W`.  `h` a basic germ (`IsBasicGerm C̃ G h B`,
  Definition 3.7) on a germ of neighbourhoods `G`, `s` an sc⁺-germ (sc-smooth germ into `F¹`,
  `IsScSmoothGerm` with target `F.shift`) with `s(0) = 0`, on the same `G`; `f = h + s` (with
  `F₁ → F₀`); `U = G₀` its domain.  The strong bundle isomorphism `Φ` / `g = Φ_*(f)` of
  Theorem 3.43 plays no role in the corollary's claim and is not assumed.
- "`Df(0)` surjective": `Df(0) = D 0` for *any* derivative family `D` of the sc¹-germ `f`
  (`IsSc1GermWith G f D`; the derivative at the smooth point `0` is unique), `D 0 : E₀ → F₀` onto.
- "`K = ker Df(0)` in good position to `C`" (Definition 3.21): `K` is finite-dimensional (an
  instance hypothesis), `K ∩ C` has nonempty interior in `K`, and `K` has a good complement
  (`IsInGoodPositionSc`).  Good complement (`IsGoodComplementSc`, defined here): an
  *sc-complement* `Y` (`E.IsScSplitting K Y`: both sc-subspaces, `E_m = K_m ⊕ Y_m` on every
  level) with `ε > 0` such that `k ∈ C ⟺ k + y ∈ C` whenever `|y|₀ ≤ ε|k|₀`.  (The project's
  `IsGoodComplement` only asks for an algebraic complement; I did not use it.)
- Conclusion (`IsGraphSolution`, defined here): a good complement `Y` of `K`, `V ⊆ K` relatively
  open in `K ∩ C` with `0 ∈ V`, and `σ : V → Y₁` (a map `K → E₁` with values in `Y` under
  `E₁ → E₀`) that is `C¹` on `V` into `E₁` (`ContDiffOn ℝ 1`); (1) "`σ` an sc-smooth germ": an
  sc-smooth germ (`IsScSmoothGerm`) from `O(K ∩ C, 0)` (`K` with the constant sc-structure) into
  `E¹` (the declared codomain `Y₁` is level `0` of `Y¹ ⊆ E¹`) on some germ of neighbourhoods
  inside `V`; (2) `σ(0) = 0` and `Dσ(0) = 0` (derivative within `V`, into `E₁`); (3) "after
  shrinking `U`": there is a relatively open neighbourhood `U₀ ⊆ U` of `0` in `C` with
  `{x ∈ U₀ | f(x) = 0} = {v + σ(v) | v ∈ V}` (`LocalGraphRep`, `graphSet`; `kerOf L` is
  `ker L` of a bounded operator, a helper defined here).
- Doubt: reading (1) with codomain `E¹` (rather than `E`) is the stronger of the two readings;
  I chose it because the statement declares `σ : V → Y₁`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_42
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
`0` in `N ∩ C`, `σ : V → Y₁` of class `C¹`, an sc-smooth germ into `E¹`, `σ(0) = 0`, `Dσ(0) = 0`. -/
def IsGraphSolution (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0))
    [FiniteDimensional ℝ N] (Y : Submodule ℝ (E.lvl 0)) (V : Set N) (σ : N → E.lvl 1) : Prop :=
  IsGoodComplementSc E C N Y ∧
  (∃ O : Set N, IsOpen O ∧ V = O ∩ (Subtype.val ⁻¹' C)) ∧ (0 : N) ∈ V ∧
  (∀ v ∈ V, E.toBase 1 (σ v) ∈ Y) ∧
  ContDiffOn ℝ 1 σ V ∧
  (∃ Vg : ScNbhdGerm (ScBanach.const N) (Subtype.val ⁻¹' C : Set N),
      Vg.U 0 ⊆ V ∧ IsScSmoothGerm (F := E.shift) Vg σ) ∧
  σ 0 = 0 ∧ HasFDerivWithinAt σ (0 : N →L[ℝ] E.lvl 1) V 0

/-- The graph `{v + σ(v) | v ∈ V} ⊆ E₀` of `σ : V → E₁` over `V ⊆ N`. -/
def graphSet (E : ScBanach) {N : Submodule ℝ (E.lvl 0)} (V : Set N) (σ : N → E.lvl 1) :
    Set (E.lvl 0) :=
  {x | ∃ v ∈ V, x = (v : E.lvl 0) + E.toBase 1 (σ v)}

/-- The kernel `ker L ⊆ E₀` of a bounded operator `L : E₀ → F₀`. -/
def kerOf {E F : ScBanach} (L : E.lvl 0 →L[ℝ] F.lvl 0) : Submodule ℝ (E.lvl 0) :=
  LinearMap.ker (L : E.lvl 0 →ₗ[ℝ] F.lvl 0)

/-- The conclusion of Corollary 3.47 for `f` with domain `U ⊆ C` and `K`: a good complement `Y` and
`σ : V → Y₁` as in `IsGraphSolution`, and after shrinking `U` to a relatively open neighbourhood
`U₀` of `0` in `C`, `{x ∈ U₀ | f(x) = 0} = {v + σ(v) | v ∈ V}`. -/
def LocalGraphRep (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (K : Submodule ℝ (E.lvl 0)) [FiniteDimensional ℝ K] : Prop :=
  ∃ (Y : Submodule ℝ (E.lvl 0)) (V : Set K) (σ : K → E.lvl 1),
    IsGraphSolution E C K Y V σ ∧
    ∃ U₀ : Set (E.lvl 0), IsRelOpenInQuadrant E C U₀ ∧ 0 ∈ U₀ ∧ U₀ ⊆ U ∧
      {x | x ∈ U₀ ∧ f x = 0} = graphSet E V σ

/-- Corollary 3.47: for `f = h + s` with `Df(0)` onto and `K = ker Df(0)` in good position to `C`,
near `0` the zero set of `f` is the graph `{v + σ(v) | v ∈ V}` of a `C¹`, sc-smooth germ
`σ : V → Y₁` over a relatively open `V ⊆ K ∩ C`, `Y` a good complement of `K`. -/
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
      LocalGraphRep (ScBanach.paramProd (Fin n → ℝ) W) (ScBanach.paramProd (Fin N → ℝ) W)
        (Ct ×ˢ Set.univ) (G.U 0) f (kerOf (D 0))

end RoundTrip.V3_42
