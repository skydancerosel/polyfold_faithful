import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_6

/-! Round trip for V1_6 (Proposition 1.7: quotients `E/A` with levels `E_m/A_m`).

`A` is the type of `ScBanach.proposition_1_1_8` (no universe parameters): for a *closed* subspace `A`
there is an sc-Banach space `Q` and a level-wise surjective sc-operator `q : E → Q` with
`ker q_m = A_m`.  `B` asks, for an *sc-subspace* `A`, for an sc-Banach space `Q` with level-wise
continuous linear equivalences `Q_m ≃ E_m/A_m` carrying the inclusions to the induced maps.

* `A → B` (proved): from `q` the induced maps `E_m/A_m → Q_m` are continuous bijections between
  Banach spaces (`A_m` is closed), hence isomorphisms (open mapping theorem); they intertwine the
  inclusions because `q` does.
* `B → A` restricted to sc-subspaces (`B_to_A_scSubspace`, proved): `q_m := φ_m⁻¹ ∘ mk`.
* `B → A` itself is not derivable from `B`: `A` covers every closed subspace, `B` only
  sc-subspaces. -/

namespace RoundTrip.V1_6
open Polyfold

/-- The project's statement. -/
def A : Prop := type_of% @Polyfold.ScBanach.proposition_1_1_8

theorem A_holds : A := @Polyfold.ScBanach.proposition_1_1_8

section Glue

variable (E : ScBanach) {A' : Submodule ℝ (E.lvl 0)}

/-- The level-`m` isomorphism `E_m/A_m ≃ Q_m` induced by a level-wise surjective `q` with kernel
`A_m`. -/
noncomputable def indEquiv (hA : IsClosed (A' : Set (E.lvl 0))) {Q : ScBanach} (q : ScOperator E Q)
    (hs : ∀ m, Function.Surjective (q m))
    (hk : ∀ m, LinearMap.ker (q m : E m →ₗ[ℝ] Q m) = E.levelSub A' m) (m : ℕ) :
    (E.lvl m ⧸ E.levelSub A' m) ≃L[ℝ] Q.lvl m :=
  haveI : IsClosed (E.levelSub A' m : Set (E.lvl m)) := hA.preimage (E.toBase m).continuous
  ContinuousLinearEquiv.ofBijective
    ((E.levelSub A' m).liftQL (q m) (hk m).ge)
    (Submodule.ker_liftQ_eq_bot' _ _ (hk m).symm)
    (by
      refine LinearMap.range_eq_top.2 fun y => ?_
      obtain ⟨x, rfl⟩ := hs m y
      exact ⟨Submodule.Quotient.mk x, rfl⟩)

theorem indEquiv_mk (hA : IsClosed (A' : Set (E.lvl 0))) {Q : ScBanach} (q : ScOperator E Q)
    (hs : ∀ m, Function.Surjective (q m))
    (hk : ∀ m, LinearMap.ker (q m : E m →ₗ[ℝ] Q m) = E.levelSub A' m) (m : ℕ) (x : E.lvl m) :
    indEquiv E hA q hs hk m (Submodule.Quotient.mk x) = q m x := rfl

end Glue

theorem A_to_B : A → B := by
  intro hA E A' hsc
  obtain ⟨Q, q, hs, hk⟩ := hA E hsc.1
  refine ⟨Q, fun m => (indEquiv E hsc.1 q hs hk m).symm, fun m x => ?_⟩
  rw [ContinuousLinearEquiv.symm_symm, indEquiv_mk, q.incl_comm, ← indEquiv_mk E hsc.1 q hs hk,
    ContinuousLinearEquiv.symm_apply_apply]

/-- `B → A` for sc-subspaces (the scope of `B`). -/
theorem B_to_A_scSubspace (hB : B) (E : ScBanach) {A' : Submodule ℝ (E.lvl 0)}
    (hA : E.IsScSubspace A') : ∃ (Q : ScBanach) (q : ScOperator E Q),
      (∀ m, Function.Surjective (q m)) ∧
        ∀ m, LinearMap.ker (q m : E m →ₗ[ℝ] Q m) = E.levelSub A' m := by
  obtain ⟨Q, φ, hφ⟩ := hB E A' hA
  let q : ScOperator E Q :=
    { lvl := fun m => ((φ m).symm : _ →L[ℝ] Q.lvl m).comp (E.levelSub A' m).mkQL
      incl_comm := fun m x => by
        apply (φ m).injective
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply, Submodule.mkQL_apply, Submodule.mkQ_apply]
        exact hφ m x }
  refine ⟨Q, q, fun m y => ?_, fun m => ?_⟩
  · obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (φ m y)
    exact ⟨x, by
      change (φ m).symm (Submodule.Quotient.mk x) = y
      rw [hx, ContinuousLinearEquiv.symm_apply_apply]⟩
  · ext x
    change (φ m).symm (Submodule.Quotient.mk x) = 0 ↔ _
    rw [map_eq_zero_iff _ (φ m).symm.injective, Submodule.Quotient.mk_eq_zero]

#rt_check RoundTrip.V1_6.A_to_B [Polyfold.ScBanach.proposition_1_1_8]
#rt_check RoundTrip.V1_6.B_to_A_scSubspace [Polyfold.ScBanach.proposition_1_1_8]
#rt_overlap RoundTrip.V1_6.B_to_A_scSubspace [Polyfold.ScBanach.proposition_1_1_8]

end RoundTrip.V1_6
