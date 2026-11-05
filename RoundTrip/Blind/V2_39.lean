import Polyfold
/-! Blind formalization of V2_39 (the text's §2.4, Definition 2.33, p. 39).

Text: `C_e := ⋂_{f ∈ F(e)} H_f` and `E_e := ⋂_{f ∈ F(e)} f`; `E_e ⊂ C_e ⊂ E`, `E_e` has
codimension `d_C(e)`.

Choices:
- This item is a definition plus properties.  Setting: `E : ScBanach` (levels in `Type`, forced
  by `ScBanach`), `C ⊆ E₀` a partial quadrant given with a presentation
  `T : E ≅ ℝⁿ ⊕ W` (`C = T⁻¹([0,∞)ⁿ ⊕ W)`), `e ∈ C`.
- Extended faces: with the coordinate functionals `λ_i(v) = (Tv)_i` (`lamB`, continuous linear),
  the extended faces of `C` are the closed hyperplanes `f_i = {λ_i = 0}` (`extFaceB`), and `H_{f_i}`
  is the closed half-space `{λ_i ≥ 0}` bounded by `f_i` and containing `C` (`halfB`).  `F(e)`, the
  extended faces containing `e`, is indexed by `I(e) = {i | λ_i(e) = 0}` (`i ↦ f_i` is injective,
  the `λ_i` being linearly independent).  So `C_e = ⋂_{i ∈ I(e)} H_i` (`CeB`, a set) and
  `E_e = ⋂_{i ∈ I(e)} f_i` (`EeB`, a linear subspace, as an infimum of kernels).  These are
  presentation-independent in the text; B asserts the claims for EVERY presentation `T`.
- "`E_e ⊂ C_e ⊂ E`": `E_e ⊆ C_e` (the inclusion `C_e ⊆ E` is the type: both are subsets of
  `E₀`).  "Codimension `d_C(e)`": `rank(E₀ / E_e) = d_C(e)` as cardinals (so an infinite
  codimension is not confused with `0`), `d_C` the project's `degIndex E C` (Definition 1.23,
  checked with `#print`: the number of vanishing half-line coordinates for a chosen
  presentation).
- B also asserts that the project's `partialQuadrantAtWith T e` and `minimalSubspaceWith T e`
  (whose docstrings name them `C_e` of Definition 2.33 and `E_x`) are `CeB T e` and `EeB T e`.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_39
open Polyfold

section
variable {E : ScBanach} {n : ℕ} {W : ScBanach}

/-- The coordinate functional `λ_i(v) = (Tv)_i`. -/
noncomputable def lamB (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (i : Fin n) :
    E.lvl 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i ∘L ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W.lvl 0)) ∘L
    (T.lvl 0 : E.lvl 0 →L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W).lvl 0)

/-- The extended face `f_i = {λ_i = 0}`. -/
noncomputable def extFaceB (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (i : Fin n) :
    Submodule ℝ (E.lvl 0) :=
  LinearMap.ker (lamB T i : E.lvl 0 →ₗ[ℝ] ℝ)

/-- The half-space `H_{f_i} = {λ_i ≥ 0}` bounded by `f_i` and containing `C`. -/
def halfB (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (i : Fin n) : Set (E.lvl 0) :=
  {v | 0 ≤ lamB T i v}

/-- `F(e)`: (the indices of) the extended faces containing `e`. -/
def FeB (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e : E.lvl 0) : Set (Fin n) :=
  {i | e ∈ extFaceB T i}

/-- `C_e = ⋂_{f ∈ F(e)} H_f`. -/
def CeB (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e : E.lvl 0) : Set (E.lvl 0) :=
  ⋂ i ∈ FeB T e, halfB T i

/-- `E_e = ⋂_{f ∈ F(e)} f`. -/
noncomputable def EeB (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e : E.lvl 0) :
    Submodule ℝ (E.lvl 0) :=
  ⨅ i ∈ FeB T e, extFaceB T i

end

/-- Definition 2.33: `E_e ⊆ C_e`, and `E_e` has codimension `d_C(e)`; the project's `C_e`, `E_e`
are these. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (n : ℕ) (W : ScBanach)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)), C = T.lvl 0 ⁻¹' quadrant n W 0 →
    ∀ e ∈ C,
      -- `E_e ⊂ C_e`
      (↑(EeB T e) : Set (E.lvl 0)) ⊆ CeB T e ∧
      -- `codim E_e = d_C(e)`
      Module.rank ℝ (E.lvl 0 ⧸ EeB T e) = (degIndex E C e : Cardinal) ∧
      -- the project's objects
      partialQuadrantAtWith T e = CeB T e ∧ minimalSubspaceWith T e = EeB T e

end RoundTrip.V2_39
