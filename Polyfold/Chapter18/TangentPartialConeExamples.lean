import Polyfold.Chapter18.TangentPartialCone
import Polyfold.Chapter18.HalfSpaceBundleConstruction

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
Remark 17.2.18, p. 784: **a non-degenerate witness for the partial cone `C_αC`**, at a boundary
object with non-trivial isotropy.

# The partial cone at the corner of `ℤ/2 ⋉ [0, ∞) × ℝ`

On the polyfold `C = ℤ/2 ⋉ H`, `H = [0, ∞) × ℝ`, `−1` acting by `(a, y) ↦ (a, −y)`
(`HalfSpaceBundleConstruction.lean`), the corner `α = (0, 0)` lies in `∂C` and has the
automorphism `(−1, (0, 0)) ≠ 1`.  `partialCone_corner`: `T_αC` is defined, `C_αC` contains `0` and
`T^R_αC`, is not all of `T_αC`, and `dim(T_αC / T^R_αC) = d_C(α) ≥ 1`; and `C_αC = S_Ψ⁻¹(C_qO)`
for the uniformizer and every chart and presentation (`partialCone_eq`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

namespace GCT.VectorBundle.HalfSpaceReflection

open PolyfoldConstruction HalfSpaceBundle

/-- The corner `(0, 0)` is a smooth object. -/
theorem isSmoothObj_corner : halfS.IsSmoothObj corner :=
  (isSmoothObj_obj_iff (tautUnif _ _ corner) corner).2
    (smoothSet_eq_univ (m := 1) ▸ mem_univ corner)

/-- `T_αC` is defined at the corner. -/
theorem tangentObj_corner : halfS.TangentObj corner :=
  tangentObj_of_isSmoothObj halfS_hasUniformizers isSmoothObj_corner

/-- `T_αC` at the corner, as an instance. -/
instance fact_tangentObj_corner : Fact (halfS.TangentObj corner) := ⟨tangentObj_corner⟩

/-- **The partial cone at the corner** (Remark 17.2.18): at the boundary object `α = (0, 0)` with
the non-trivial automorphism `(−1, (0, 0))`, `C_αC` contains `T^R_αC` (so `0`), is a proper subset
of `T_αC`, and `dim(T_αC / T^R_αC) = d_C(α) ≥ 1`. -/
theorem partialCone_corner :
    corner ∈ halfS.boundarySet ∧
      (∃ φ ∈ halfC.toGroupoidStr.mor corner corner, φ ≠ halfC.toGroupoidStr.unit corner) ∧
      (halfS.reducedTangent corner : Set (halfS.TangentSpaceAt corner)) ⊆
        halfS.partialCone corner ∧
      (0 : halfS.TangentSpaceAt corner) ∈ halfS.partialCone corner ∧
      halfS.partialCone corner ≠ univ ∧
      1 ≤ Module.finrank ℝ (halfS.TangentSpaceAt corner ⧸ halfS.reducedTangent corner) := by
  have hb : 1 ≤ halfS.degIndex corner := corner_mem_boundarySet
  have h0 : (0 : halfS.TangentSpaceAt corner) ∈ halfS.partialCone corner :=
    ((mem_reducedTangent_iff_lineality (S := halfS) corner 0).1
      (halfS.reducedTangent corner).zero_mem).1
  refine ⟨corner_mem_boundarySet, exists_ne_unit_corner,
    reducedTangent_subset_partialCone (S := halfS) corner, h0,
    partialCone_ne_univ (S := halfS) corner halfS_isTame isSmoothObj_corner hb, ?_⟩
  rw [finrank_quotient_reducedTangent_eq_degIndex (S := halfS) corner halfS_isTame
    isSmoothObj_corner]
  exact hb

end GCT.VectorBundle.HalfSpaceReflection

end Polyfold
