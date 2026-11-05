import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_39

/-! Round trip for V2_39 (Definition 2.33: `C_e`, `E_e`; `E_e ⊆ C_e`, `codim E_e = d_C(e)`).

`A` is the conjunction of the types of `Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith`,
`convex_partialQuadrantAtWith`, `finrank_quotient_minimalSubspaceWith`, `minimalSubspaceWith_le`
and `minimalSubspaceWith_eq` (no universe parameters).  `partialQuadrantAtWith` and
`minimalSubspaceWith` are definitions (vocabulary).

The definitions agree with B's: `partialQuadrantAtWith T e = CeB T e` and
`minimalSubspaceWith T e = EeB T e` for every sc-isomorphism `T : E ≅ ℝⁿ ⊕ W` and every `e`
(`pq_eq`, `ms_eq`, by unfolding; no presentation hypothesis is needed).

`A → B`: the inclusion `E_e ⊆ C_e` is A's first conjunct, and B's cardinal codimension is A's
`finrank_quotient_minimalSubspaceWith` (the quotient is finite-dimensional) together with
`degIndex_eq` (`d_C = degIndexWith T` on `C` for a presentation `T`).

`B → A` is proved only outright (B unused): every conjunct of A is stated for an ARBITRARY
sc-isomorphism `T` and point `e` (not a presentation of a `C ∋ e`), so B, which speaks only of
presentations of `C` and points of `C`, cannot supply them; convexity of `C_e` is not in B; and
`minimalSubspaceWith_le/_eq` (the minimal subspace does not depend on the presentation, the sign
argument of Lemma 1.24) is not stated in B at all — B asserts its claims for every presentation but
never that the `E_e` of two presentations agree.  The text defines `E_e`, `C_e` intrinsically
through the extended faces, so presentation independence is implicit in the text. -/

namespace RoundTrip.V2_39
open Polyfold Set Module Filter Topology

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith) ∧
    (type_of% @Polyfold.convex_partialQuadrantAtWith) ∧
    (type_of% @Polyfold.finrank_quotient_minimalSubspaceWith) ∧
    (type_of% @Polyfold.minimalSubspaceWith_le) ∧ (type_of% @Polyfold.minimalSubspaceWith_eq)

theorem A_holds : A :=
  ⟨@Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith,
    @Polyfold.convex_partialQuadrantAtWith, @Polyfold.finrank_quotient_minimalSubspaceWith,
    @Polyfold.minimalSubspaceWith_le, @Polyfold.minimalSubspaceWith_eq⟩

/-! ### Glue: the project's `C_e`, `E_e` are B's -/

section Glue

variable {E : ScBanach} {n : ℕ} {W : ScBanach}

lemma lamB_apply (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (i : Fin n) (v : E 0) :
    lamB T i v = (T 0 v).1 i := rfl

lemma mem_FeB (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e : E 0) (i : Fin n) :
    i ∈ FeB T e ↔ (T 0 e).1 i = 0 := Iff.rfl

/-- `C_e` (project) `= C_e` (B), for every `T` and `e`. -/
theorem pq_eq (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e : E 0) :
    partialQuadrantAtWith T e = CeB T e := by
  ext v
  simp only [CeB, halfB, mem_iInter, mem_FeB, lamB_apply]
  rfl

/-- `E_e` (project) `= E_e` (B), for every `T` and `e`. -/
theorem ms_eq (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e : E 0) :
    minimalSubspaceWith T e = EeB T e := by
  ext v
  rw [mem_minimalSubspaceWith, EeB]
  simp only [Submodule.mem_iInf, extFaceB, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    mem_FeB, lamB_apply]

end Glue

theorem A_to_B : A → B := by
  intro hA E C n W T hT e he
  have hsub := hA.1 T e
  have hfin := hA.2.2.1 T e
  rw [ms_eq] at hsub hfin
  rw [pq_eq] at hsub
  refine ⟨hsub, ?_, pq_eq T e, ms_eq T e⟩
  have : FiniteDimensional ℝ (E 0 ⧸ EeB T e) := by
    rw [← ms_eq]; infer_instance
  rw [← Module.finrank_eq_rank, hfin, degIndex_eq T hT he]

/-! ### `B → A`, outright (B is not used) -/

section Outright

variable {E : ScBanach} {C : Set (E 0)} {n n' : ℕ} {W W' : ScBanach}

theorem subset_outright (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e : E 0) :
    (minimalSubspaceWith T e : Set (E 0)) ⊆ partialQuadrantAtWith T e := fun v hv i hi => by
  rw [(mem_minimalSubspaceWith T).1 hv i hi]

theorem convex_outright (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e : E 0) :
    Convex ℝ (partialQuadrantAtWith T e) := by
  intro v hv w hw a b ha hb _ i hi
  have h1 := hv i hi
  have h2 := hw i hi
  simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  exact add_nonneg (mul_nonneg ha h1) (mul_nonneg hb h2)

theorem finrank_outright (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) :
    finrank ℝ (E 0 ⧸ minimalSubspaceWith T x) = degIndexWith T x := by
  classical
  have e : (E 0 ⧸ minimalSubspaceWith T x) ≃ₗ[ℝ] ({i : Fin n // (T 0 x).1 i = 0} → ℝ) :=
    LinearMap.quotKerEquivOfSurjective (coordMapL T x).toLinearMap (coordMapL_surjective T x)
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]
  rfl

theorem le_outright (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) (T' : ScIso E ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : C = T' 0 ⁻¹' quadrant n' W' 0) {x : E 0} (hx : x ∈ C) :
    minimalSubspaceWith T x ≤ minimalSubspaceWith T' x := by
  intro v hv
  rw [mem_minimalSubspaceWith]
  intro j hj
  have hev := eventually_add_smul_mem_of_minimalSubspace T hT hx hv
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hlin : ∀ t : ℝ, (T' 0 (x + t • v)).1 j = t * (T' 0 v).1 j := fun t => by
    simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hj, zero_add]
  have h1 := coord_nonneg hT' (hball (show dist (δ / 2) 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; exact half_lt_self hδ)) j
  have h2 := coord_nonneg hT' (hball (show dist (-(δ / 2)) 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hδ)]; exact half_lt_self hδ)) j
  rw [hlin] at h1 h2
  have hδ2 : 0 < δ / 2 := half_pos hδ
  nlinarith

end Outright

theorem B_to_A : B → A := by
  intro _
  exact ⟨@subset_outright, @convex_outright, @finrank_outright, @le_outright,
    fun T hT T' hT' _ hx => le_antisymm (le_outright T hT T' hT' hx) (le_outright T' hT' T hT hx)⟩

#rt_check RoundTrip.V2_39.A_to_B [Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith,
  Polyfold.convex_partialQuadrantAtWith, Polyfold.finrank_quotient_minimalSubspaceWith,
  Polyfold.minimalSubspaceWith_le, Polyfold.minimalSubspaceWith_eq]
#rt_check RoundTrip.V2_39.B_to_A [Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith,
  Polyfold.convex_partialQuadrantAtWith, Polyfold.finrank_quotient_minimalSubspaceWith,
  Polyfold.minimalSubspaceWith_le, Polyfold.minimalSubspaceWith_eq]
#rt_overlap RoundTrip.V2_39.B_to_A [Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith,
  Polyfold.convex_partialQuadrantAtWith, Polyfold.finrank_quotient_minimalSubspaceWith,
  Polyfold.minimalSubspaceWith_le, Polyfold.minimalSubspaceWith_eq]

end RoundTrip.V2_39
