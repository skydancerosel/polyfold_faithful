import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_12

/-! Round trip for V1_12 (Definition 1.13: the tangent `(TU, TC, TE)` of a tuple `(U, C, E)`).

`A` is the conjunction of the types of the theorems in the item's declaration list:
`ScBanach.lvlSet_tangentSet`, `IsScDomain.tangentSet`, `ScBanach.shift_tangentSet` (the
definitions `ScBanach.tangent`, `ScBanach.tangentSet` are vocabulary).  None has universe
parameters (`ScBanach` lives in `Type`).

The blind notions are the project's: `tanSpace E` is `E.tangent` (both `E.shift.prod E`) and
`tanSet E A` is `E.tangentSet A` (`tanSet_eq`, by `rfl`).

`B` (the text's "it is again a tuple") is TRUE, proved here outright (`B_holds`): for
`C = T₀⁻¹([0,∞)ⁿ ⊕ W₀)` with `T : E ≅ ℝⁿ ⊕ W`, the map
`S_m : E_{m+1} × E_m → ℝⁿ × (W_{m+1} × E_m)`, `(x, h) ↦ ((T_{m+1} x).1, ((T_{m+1} x).2, h))` is an
sc-isomorphism `TE ≅ ℝⁿ ⊕ (W¹ ⊕ E)` with `TC = S₀⁻¹([0,∞)ⁿ ⊕ (W¹ ⊕ E)₀)`, and
`TU = {(x, h) | ι₁x ∈ O} ∩ TC`.  The project does not contain this: its docstring says that `TC`
is a partial quadrant in `TE` "is not proved"; `A` only carries the consequence
`IsScDomain.tangentSet` (stability of the level-wise open-∩-convex / unique-differentiability
property under `T`) and two level-set identities.  So `A_to_B` is proved without using `A`, and
`B_to_A` likewise (each conjunct of `A` holds for arbitrary `U` / arbitrary `IsScDomain`s, a
wider class than the tuples `B` speaks about). -/

namespace RoundTrip.V1_12
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScBanach.lvlSet_tangentSet) ∧ (type_of% @Polyfold.IsScDomain.tangentSet) ∧
    (type_of% @Polyfold.ScBanach.shift_tangentSet)

theorem A_holds : A :=
  ⟨@Polyfold.ScBanach.lvlSet_tangentSet, @Polyfold.IsScDomain.tangentSet,
    @Polyfold.ScBanach.shift_tangentSet⟩

/-- The blind tangent space and tangent sets are the project's. -/
theorem tanSpace_eq (E : ScBanach) : tanSpace E = E.tangent := rfl

theorem tanSet_eq (E : ScBanach) (A : Set (E.lvl 0)) : tanSet E A = E.tangentSet A := rfl

/-- The sc-isomorphism `TE = E¹ ⊕ E ≅ ℝⁿ ⊕ (W¹ ⊕ E)` induced by `T : E ≅ ℝⁿ ⊕ W`. -/
noncomputable def tanIso {E : ScBanach} {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    ScIso (tanSpace E) ((ScBanach.const (Fin n → ℝ)).prod (W.shift.prod E)) where
  lvl m := ((T (m + 1)).prodCongr (ContinuousLinearEquiv.refl ℝ (E m))).trans
    (ContinuousLinearEquiv.prodAssoc ℝ (Fin n → ℝ) (W (m + 1)) (E m))
  incl_comm m x := by
    have h := T.incl_comm (m + 1) x.1
    change (((T (m + 1 + 1) x.1).1, (W.incl (m + 1) (T (m + 1 + 1) x.1).2, E.incl m x.2)) :
        (Fin n → ℝ) × (W (m + 1) × E m)) =
      ((T (m + 1) (E.incl (m + 1) x.1)).1, ((T (m + 1) (E.incl (m + 1) x.1)).2, E.incl m x.2))
    rw [← h]
    rfl

theorem tanIso_apply_fst {E : ScBanach} {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (p : (tanSpace E).lvl 0) :
    ((tanIso T) 0 p).1 = (T 1 p.1).1 := rfl

/-- `TC = S₀⁻¹([0,∞)ⁿ ⊕ (W¹ ⊕ E)₀)`. -/
theorem tanSet_quadrant {E : ScBanach} {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    tanSet E (T 0 ⁻¹' quadrant n W 0) = (tanIso T) 0 ⁻¹' quadrant n (W.shift.prod E) 0 := by
  ext p
  change (∀ i, 0 ≤ (T 0 (E.toBase 1 p.1)).1 i) ↔ ∀ i, 0 ≤ ((tanIso T) 0 p).1 i
  rw [tanIso_apply_fst, ← T.toBase_comm, ScBanach.prod_toBase, ScBanach.const_toBase]

/-- `B` holds (outright, without `A`). -/
theorem B_holds : B := by
  intro E C U ⟨⟨n, W, T, hC⟩, O, hO, hU⟩
  subst hC hU
  refine ⟨⟨n, W.shift.prod E, tanIso T, tanSet_quadrant T⟩,
    {p : (tanSpace E).lvl 0 | E.toBase 1 p.1 ∈ O}, ?_, rfl⟩
  exact hO.preimage ((E.toBase 1).continuous.comp continuous_fst)

/-- `A → B`: vacuous (`B` is proved outright; `A` does not contain it). -/
theorem A_to_B : A → B := fun _ => B_holds

/-- `B → A`: vacuous; the conjuncts of `A` are re-proved outright (they concern arbitrary `U` and
arbitrary `IsScDomain`s, not only tuples). -/
theorem B_to_A : B → A := by
  intro _
  have hmem : ∀ (E : ScBanach) (U : Set (E.lvl 0)) (m : ℕ) (p : E.tangent.lvl m),
      p ∈ E.tangent.lvlSet (E.tangentSet U) m ↔ p.1 ∈ E.lvlSet U (m + 1) := by
    intro E U m p
    rw [ScBanach.mem_lvlSet, ScBanach.mem_tangentSet, ScBanach.tangent_toBase]
    change E.toBase 1 (E.shift.toBase m p.1) ∈ U ↔ E.toBase (m + 1) p.1 ∈ U
    rw [← E.shift_toBase m p.1]
  have hlvl : ∀ (E : ScBanach) (U : Set (E.lvl 0)) (m : ℕ),
      E.tangent.lvlSet (E.tangentSet U) m = E.lvlSet U (m + 1) ×ˢ univ := by
    intro E U m
    ext q
    rw [hmem]
    change _ ↔ q.1 ∈ E.lvlSet U (m + 1) ∧ q.2 ∈ univ
    simp
  refine ⟨hlvl, ?_, ?_⟩
  · intro E U h
    refine ⟨fun m => ?_, fun m p hp => ?_⟩
    · obtain ⟨O, C, hO, hC, hU⟩ := h.relOpenConvex (m + 1)
      refine ⟨O ×ˢ univ, C ×ˢ univ, hO.prod isOpen_univ, hC.prod convex_univ, ?_⟩
      ext p
      rw [hmem, hU]
      change p.1 ∈ O ∩ C ↔ (p.1 ∈ O ∧ p.2 ∈ univ) ∧ (p.1 ∈ C ∧ p.2 ∈ univ)
      simp
    · have h1 := (h.uniqueDiffWithinAt (m + 1) p.1 ((hmem E U m p).1 hp)).prod
        (uniqueDiffWithinAt_univ (x := p.2))
      rw [hlvl]
      exact h1
  · intro E U
    ext p
    rw [hmem]
    exact Iff.rfl

#rt_check RoundTrip.V1_12.A_to_B [Polyfold.ScBanach.lvlSet_tangentSet,
  Polyfold.IsScDomain.tangentSet, Polyfold.ScBanach.shift_tangentSet]
#rt_check RoundTrip.V1_12.B_to_A [Polyfold.ScBanach.lvlSet_tangentSet,
  Polyfold.IsScDomain.tangentSet, Polyfold.ScBanach.shift_tangentSet]
#rt_overlap RoundTrip.V1_12.B_to_A [Polyfold.ScBanach.lvlSet_tangentSet,
  Polyfold.IsScDomain.tangentSet, Polyfold.ScBanach.shift_tangentSet]
#rt_overlap RoundTrip.V1_12.A_to_B [Polyfold.ScBanach.lvlSet_tangentSet,
  Polyfold.IsScDomain.tangentSet, Polyfold.ScBanach.shift_tangentSet]

end RoundTrip.V1_12
