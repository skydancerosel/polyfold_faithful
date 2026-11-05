import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_41

/-! Round trip for V2_41 (Proposition 2.35: `(1 − Dr(x))E ⊆ E_x`, and `A = (1 − Dr(x))E` works in
condition (2) of Definition 2.34).

`A` is the conjunction of the types of `Polyfold.proposition_2_35`,
`ScRetraction.scDeriv_mapsTo_minimalSubspace`, `ScRetraction.isScOperator_scDeriv`,
`ScRetraction.isScSplitting_range_scDeriv` and `coord_scDeriv_eq` (no universe parameters).

Same notions on both sides: B's `complB R x₁` is the project's `range (id − Dr(x))` (`complB_eq`),
B's `tangentAt R x₁` is `range Dr(x)`, and "smooth `x ∈ O` with lift `x₁`" is the project's
`x₁ ∈ O₁ ∩ (E₁)_∞`.

`A → B`: B assumes `R.IsTame` (every presentation) and fixes a presentation `T`; A's
`proposition_2_35` needs only `R.IsTameWith T`.  The sc-subspace clause of B is part of the
project's `IsScSplitting`.

`B → A`: `proposition_2_35` (stated for `R.IsTameWith T`, one presentation) is B after
`IsTameWith.isTame` (a non-item project lemma: tameness for one presentation gives it for all).
`coord_scDeriv_eq` (`λ_j ∘ Dr(x) = λ_j` for `j ∈ I(x)`) is B's inclusion read in coordinates.  The
other three conjuncts are facts about an ARBITRARY sc-smooth retraction (no tameness): `Dr(x)` maps
`E_x` to itself at `x ∈ O₁` (the sign argument), `Dr(x)` is an sc-operator at smooth points, and
`E = Dr(x)E ⊕ (1 − Dr(x))E` is an sc-splitting at smooth `x ∈ O`.  B, which assumes tameness,
cannot supply them; they are re-proved outright from non-item project lemmas
(`IsSc1With.mapsTo_minimalSubspace`, `IsSc1With.scOperator_deriv`, `scDeriv_comp_self`,
`ScBanach.isScSplitting_of_idem`). -/

namespace RoundTrip.V2_41
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.proposition_2_35) ∧
    (type_of% @Polyfold.ScRetraction.scDeriv_mapsTo_minimalSubspace) ∧
    (type_of% @Polyfold.ScRetraction.isScOperator_scDeriv) ∧
    (type_of% @Polyfold.ScRetraction.isScSplitting_range_scDeriv) ∧
    (type_of% @Polyfold.coord_scDeriv_eq)

theorem A_holds : A :=
  ⟨@Polyfold.proposition_2_35, @Polyfold.ScRetraction.scDeriv_mapsTo_minimalSubspace,
    @Polyfold.ScRetraction.isScOperator_scDeriv, @Polyfold.ScRetraction.isScSplitting_range_scDeriv,
    @Polyfold.coord_scDeriv_eq⟩

/-! ### Glue -/

section Glue

variable {E : ScBanach} {C : Set (E 0)}

/-- `(1 − Dr(x))E` of B is the project's `range (id − Dr(x))`. -/
lemma complB_eq (R : ScRetraction E C) (x₁ : E 1) :
    complB R x₁ = LinearMap.range ((ContinuousLinearMap.id ℝ (E 0) : E 0 →ₗ[ℝ] E 0) -
      (scDeriv R.U R x₁ : E 0 →ₗ[ℝ] E 0)) := rfl

lemma tangentAt_eq (R : ScRetraction E C) (x₁ : E 1) :
    tangentAt R x₁ = LinearMap.range (scDeriv R.U R x₁ : E 0 →ₗ[ℝ] E 0) := rfl

end Glue

theorem A_to_B : A → B := by
  intro hA E C R hR x hx hxs x₁ hx₁ n W T hT
  have h1 : x₁ ∈ E.lvlSet R.retract 1 := by rw [ScBanach.mem_lvlSet, hx₁]; exact hx
  have h2 : x₁ ∈ E.smoothLvl 1 := by
    change E.toBase 1 x₁ ∈ (E.smooth : Set (E 0)); rw [hx₁]; exact hxs
  obtain ⟨hle, hsplit⟩ := hA.1 hT (hR n W T hT) h1 h2
  rw [hx₁] at hle
  rw [complB_eq, tangentAt_eq]
  exact ⟨hle, hsplit.2.1, hle, hsplit⟩

/-! ### `B → A` -/

section Outright

variable {E : ScBanach} {n : ℕ} {W : ScBanach} {C : Set (E 0)}

/-- `Dr(x)E_x ⊆ E_x` for any retraction (outright). -/
theorem mapsTo_outright (R : ScRetraction E C)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) :
    MapsTo (scDeriv R.U R x) (minimalSubspaceWith T (E.toBase 1 x))
      (minimalSubspaceWith T (E.toBase 1 x)) := by
  have h := IsSc1With.mapsTo_minimalSubspace T hT T hT R.relOpen R.isSc1.isSc1With_scDeriv
    (fun _ hz => R.U_subset_C (R.mapsTo hz)) (R.lvlSet_retract_subset 1 hx)
  rwa [R.apply_eq_self_of_mem_retract hx] at h

/-- `Dr(x)` is an sc-operator at smooth points (outright). -/
theorem isScOperator_outright (R : ScRetraction E C) {x : E 1}
    (hx : x ∈ E.lvlSet R.U 1) (hs : x ∈ E.smoothLvl 1) : IsScOperator (scDeriv R.U R x) :=
  R.isSc1.isSc1With_scDeriv.scOperator_deriv hx hs

/-- `E = Dr(x)E ⊕ (1 − Dr(x))E` for any retraction at smooth `x ∈ O` (outright). -/
theorem isScSplitting_outright (R : ScRetraction E C) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) :
    E.IsScSplitting (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0))
      (LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) := by
  set D := scDeriv R.U R x with hD
  have hop := isScOperator_outright R (R.lvlSet_retract_subset 1 hx) hs
  set P := hop.toScOperator with hP
  have hP0 : P 0 = D := hop.toScOperator_zero
  have hDD : ∀ v, D (D v) = D v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hx)
  have hidem : ∀ v, P 0 (P 0 v) = P 0 v := by rw [hP0]; exact hDD
  have h := ScBanach.isScSplitting_of_idem P hidem
  rw [hP0] at h
  have hker : LinearMap.ker (D : E 0 →ₗ[ℝ] E 0) =
      LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - D : E 0 →ₗ[ℝ] E 0) := by
    ext v
    constructor
    · intro hv
      refine ⟨v, ?_⟩
      have : D v = 0 := hv
      simp [this]
    · rintro ⟨u, rfl⟩
      change D (u - D u) = 0
      rw [map_sub, hDD, sub_self]
  rwa [hker] at h

end Outright

theorem B_to_A : B → A := by
  intro hB
  -- Proposition 2.35 for one presentation, from B
  have hprop : type_of% @Polyfold.proposition_2_35 := by
    intro E n W C R T hT hRT x hx hs
    have h := hB E C R (ScRetraction.IsTameWith.isTame hT hRT) (E.toBase 1 x) hx hs x rfl n W T hT
    rw [complB_eq, tangentAt_eq] at h
    exact ⟨h.1, h.2.2.2⟩
  refine ⟨hprop, @mapsTo_outright, @isScOperator_outright, @isScSplitting_outright, ?_⟩
  -- `coord_scDeriv_eq`: B's inclusion in coordinates
  intro E n W C R T hT hRT x hx hs j hj v
  have h := (hprop hT hRT hx hs).1 ⟨v, rfl⟩
  rw [mem_minimalSubspaceWith] at h
  have := h j hj
  change (T 0 (v - scDeriv R.U R x v)).1 j = 0 at this
  rw [map_sub, Prod.fst_sub, Pi.sub_apply, sub_eq_zero] at this
  exact this.symm

#rt_check RoundTrip.V2_41.A_to_B [Polyfold.proposition_2_35,
  Polyfold.ScRetraction.scDeriv_mapsTo_minimalSubspace, Polyfold.ScRetraction.isScOperator_scDeriv,
  Polyfold.ScRetraction.isScSplitting_range_scDeriv, Polyfold.coord_scDeriv_eq]
#rt_check RoundTrip.V2_41.B_to_A [Polyfold.proposition_2_35,
  Polyfold.ScRetraction.scDeriv_mapsTo_minimalSubspace, Polyfold.ScRetraction.isScOperator_scDeriv,
  Polyfold.ScRetraction.isScSplitting_range_scDeriv, Polyfold.coord_scDeriv_eq]
#rt_overlap RoundTrip.V2_41.B_to_A [Polyfold.proposition_2_35,
  Polyfold.ScRetraction.scDeriv_mapsTo_minimalSubspace, Polyfold.ScRetraction.isScOperator_scDeriv,
  Polyfold.ScRetraction.isScSplitting_range_scDeriv, Polyfold.coord_scDeriv_eq]

end RoundTrip.V2_41
