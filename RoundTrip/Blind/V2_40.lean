import Polyfold
/-! Blind formalization of V2_40 (the text's §2.4, Definition 2.34, pp. 39–40).

Text: an sc-smooth retraction `r : U → U` is tame if (1) `d_C(r(x)) = d_C(x)` on `U` and (2) at
every smooth `x ∈ O` there is an sc-subspace `A ⊂ E_x` with `E = T_xO ⊕ A`.  A tame retract is
the image of a tame retraction.

Choices:
- This item is a definition (no further property asserted), so B says the project's notions
  `ScRetraction.IsTame` and `IsTameRetract` are equivalent to my renderings `IsTameB`,
  `IsTameRetractB` of the text's definitions.
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C ⊆ E₀`.  "sc-smooth
  retraction `r : U → U`" is the project's `ScRetraction E C` (checked with `#print`: `U`
  relatively open in the partial quadrant `C`, `r` sc-smooth on `U`, `r(U) ⊆ U`, `r ∘ r = r` on
  `U`), `O = r(U)` its `retract` (checked: `toFun '' U`).
- `d_C` and `E_x` are defined from a presentation `T : E ≅ ℝⁿ ⊕ W` of `C`
  (`C = T⁻¹([0,∞)ⁿ ⊕ W)`), with `λ_i(v) = (Tv)_i`: `d_C(x) = #{i | λ_i(x) = 0}` (`dCB`; a finite
  set, so `ncard` has no junk) and `E_x = E_e` of Definition 2.33 `= ⋂_{i : λ_i(x) = 0} ker λ_i`
  (`ExB`).  Both are presentation-independent in the text; `IsTameB` requires the conditions for
  EVERY presentation (equivalent to "for one" given that independence).
- (2): "smooth `x ∈ O`" is `x ∈ O ∩ E_∞`; `T_xO = Dr(x)E` is the range of
  `scDeriv R.U R.toFun x₁`, `x₁` the lift of `x` to `E₁` (as in `RoundTrip/Blind/V2_37.lean`).
  "`E = T_xO ⊕ A`" between sc-subspaces is read as an sc-splitting (Definition 1.5, the project's
  `IsScSplitting`, checked with `#print`: both sc-subspaces and `E_m = (T_xO)_m ⊕ A_m` on every
  level); I read "sc-complement" (a level-0 algebraic complement only would be weaker).
  "`A` an sc-subspace" (`IsScSubspace`, checked) and `A ⊆ E_x` are stated explicitly.
- "A tame retract is the image of a tame retraction": `(O, C, E)` is a tame retract iff
  `O = r(U)` for a tame `r : U → U` on `C`.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_40
open Polyfold

section
variable {E : ScBanach} {n : ℕ} {W : ScBanach}

/-- The coordinate functional `λ_i(v) = (Tv)_i`. -/
noncomputable def lamB (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (i : Fin n) :
    E.lvl 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i ∘L ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W.lvl 0)) ∘L
    (T.lvl 0 : E.lvl 0 →L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W).lvl 0)

/-- `d_C(x)`: the number of vanishing half-line coordinates of `x`. -/
noncomputable def dCB (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E.lvl 0) : ℕ :=
  {i : Fin n | lamB T i x = 0}.ncard

/-- `E_x = ⋂_{i : λ_i(x) = 0} {λ_i = 0}`. -/
noncomputable def ExB (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E.lvl 0) :
    Submodule ℝ (E.lvl 0) :=
  ⨅ i ∈ {i : Fin n | lamB T i x = 0}, LinearMap.ker (lamB T i : E.lvl 0 →ₗ[ℝ] ℝ)

end

/-- The tangent space `T_xO = Dr(x)E` computed with the retraction `R`, at the level-1 point
`x₁`. -/
noncomputable def tangentAt {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C)
    (x₁ : E.lvl 1) : Submodule ℝ (E.lvl 0) :=
  LinearMap.range (scDeriv R.U R.toFun x₁ : E.lvl 0 →ₗ[ℝ] E.lvl 0)

/-- Conditions (1) and (2) of Definition 2.34, with `d_C` and `E_x` computed from the
presentation `T`. -/
def IsTameWithB {E : ScBanach} {C : Set (E.lvl 0)} {n : ℕ} {W : ScBanach}
    (R : ScRetraction E C) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) : Prop :=
  -- (1) `d_C(r(x)) = d_C(x)` on `U`
  (∀ x ∈ R.U, dCB T (R.toFun x) = dCB T x) ∧
  -- (2) at smooth `x ∈ O`, an sc-subspace `A ⊆ E_x` with `E = T_xO ⊕ A`
  (∀ x ∈ R.retract, x ∈ E.smooth → ∀ x₁ : E.lvl 1, E.toBase 1 x₁ = x →
    ∃ A : Submodule ℝ (E.lvl 0),
      E.IsScSubspace A ∧ A ≤ ExB T x ∧ E.IsScSplitting (tangentAt R x₁) A)

/-- Definition 2.34: a tame sc-smooth retraction (conditions for every presentation of `C`). -/
def IsTameB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) : Prop :=
  ∀ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
    C = T.lvl 0 ⁻¹' quadrant n W 0 → IsTameWithB R T

/-- Definition 2.34: `(O, C, E)` is a tame retract if `O` is the image of a tame retraction. -/
def IsTameRetractB (E : ScBanach) (C O : Set (E.lvl 0)) : Prop :=
  ∃ R : ScRetraction E C, R.retract = O ∧ IsTameB R

/-- Definition 2.34: the project's tame retractions and tame retracts are the text's. -/
def B : Prop :=
  (∀ (E : ScBanach) (C : Set (E.lvl 0)) (R : ScRetraction E C), R.IsTame ↔ IsTameB R) ∧
  (∀ (E : ScBanach) (C O : Set (E.lvl 0)), IsTameRetract E C O ↔ IsTameRetractB E C O)

end RoundTrip.V2_40
