import Polyfold.Chapter2.Retracts

/-!
# Tangent spaces of a point

A map constant on a set has zero sc-derivative there, and the tangent space of a singleton is zero.
The boundary results are in `Chapter9/Boundary.lean`.
-/

set_option maxSynthPendingDepth 3
open Set Filter Topology
noncomputable section
namespace Polyfold
universe u

/-- A map constant on an sc-domain has vanishing sc-derivative on `U₁` (uniqueness of the
derivative on `U₁`, `IsScDomain.uniqueDiffWithinAt_one`, and density of `E₁` in `E₀`). -/
theorem scDeriv_eq_zero_of_eqOn_const {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0}
    (hf : IsSc1 U f) (hU : IsScDomain E U) {q : F 0} (hc : ∀ x ∈ U, f x = q) {x : E 1}
    (hx : x ∈ E.lvlSet U 1) : scDeriv U f x = 0 := by
  have h1 := hf.isSc1With_scDeriv.hasFDerivWithinAt x hx
  have h2 : HasFDerivWithinAt (f ∘ E.toBase 1) (0 : E 1 →L[ℝ] F 0) (E.lvlSet U 1) x :=
    (hasFDerivWithinAt_const q x _).congr (fun y hy => hc _ hy) (hc _ hx)
  have h3 := (hU.uniqueDiffWithinAt_one x hx).eq h1 h2
  have hd : Dense (Submodule.span ℝ (range (E.toBase 1)) : Set (E 0)) :=
    Dense.mono Submodule.subset_span (E.denseRange_inclK 0 1)
  refine ContinuousLinearMap.ext_on hd ?_
  rintro _ ⟨y, rfl⟩
  have := congrArg (fun L : E 1 →L[ℝ] F 0 => L y) h3
  simpa using this

/-- The tangent space of a one-point retract `{q}` is `{0}`. -/
theorem tangentSpace_singleton_subset {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C)
    {q : E 0} (hR : R.retract = {q}) {z : E 1} (hz : E.toBase 1 z = q) :
    tangentSpace E C {q} z ⊆ {0} := by
  have hzR : z ∈ E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR, hz]; rfl
  rw [← hR, tangentSpace_eq_range R hzR]
  rintro _ ⟨v, rfl⟩
  have hc : ∀ u ∈ R.U, R u = q := fun u hu => by
    have := R.apply_mem_retract hu
    rw [hR] at this
    exact this
  rw [scDeriv_eq_zero_of_eqOn_const R.isSc1 R.isScDomain hc (R.lvlSet_retract_subset 1 hzR)]
  rfl

end Polyfold
end
