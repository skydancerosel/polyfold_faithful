import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_61

/-!
Round trip for V5_61 (Proposition 5.42).  `A` is the conjunction of the types of
`Polyfold.proposition_5_5_15_reflexive`, `Polyfold.proposition_5_5_15_separable` and
`Polyfold.span_closedBall_eq_top`, universes instantiated at `0`.

Both sides use the project's `IsReflexive` and `IsWCG` (B checked them with `#print`).  The
difference is the setting:

* A is stated for every real **normed** space `V` (no `CompleteSpace`);
* B (following the text, "`E` a Banach space") only for complete `V`.

`A → B`: specialize.  `B → A`:
* (i) a reflexive normed space is automatically complete (`V ≅ V''` isometrically, and `V''` is
  complete), so B applies;
* (ii) for a separable normed space that is *not* complete B says nothing, so this conjunct is
  re-proved directly (the project's short argument: a null sequence built from a dense sequence,
  with its limit `0`, is norm compact, hence weakly compact, and spans a dense subspace) — the
  extra generality of A is genuine but harmless;
* `span_closedBall_eq_top` is a helper lemma (the closed unit ball spans `V`), not in B; it is
  re-proved directly (rescaling).
-/

namespace RoundTrip.V5_61
open Polyfold Set Filter Topology

/-- The project's statement, universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.proposition_5_5_15_reflexive.{0}) ∧
  (type_of% @Polyfold.proposition_5_5_15_separable.{0}) ∧
  (type_of% @Polyfold.span_closedBall_eq_top.{0})

theorem A_holds : A :=
  ⟨@Polyfold.proposition_5_5_15_reflexive.{0}, @Polyfold.proposition_5_5_15_separable.{0},
    @Polyfold.span_closedBall_eq_top.{0}⟩

theorem A_to_B : A → B := by
  intro hA V _ _ _
  exact ⟨fun h => hA.1 h, fun _ => hA.2.1⟩

section Glue

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A reflexive normed space is complete: it is isometric to its bidual. -/
theorem completeSpace_of_isReflexive (h : IsReflexive V) : CompleteSpace V :=
  (LinearIsometryEquiv.ofSurjective (NormedSpace.inclusionInDoubleDualLi (E := V) ℝ)
    h).toIsometryEquiv.completeSpace

/-- The closed unit ball spans `V` (re-proved; not in B). -/
theorem span_closedBall_eq_top' : Submodule.span ℝ (Metric.closedBall (0 : V) 1) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · exact zero_mem _
  have h1 : ‖v‖⁻¹ • v ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  have h2 := Submodule.smul_mem _ ‖v‖ (Submodule.subset_span h1)
  rwa [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv), one_smul] at h2

/-- A separable normed space (complete or not) is WCG (re-proved: B covers only Banach
spaces). -/
theorem isWCG_of_separable [TopologicalSpace.SeparableSpace V] : IsWCG V := by
  obtain ⟨y, hy⟩ := TopologicalSpace.exists_dense_seq V
  set a : ℕ → ℝ := fun n => ((n + 1 : ℝ) * (‖y n‖ + 1))⁻¹ with ha
  have hapos : ∀ n, 0 < a n := fun n => inv_pos.2 (by positivity)
  set z : ℕ → V := fun n => a n • y n with hz
  have hzlim : Tendsto z atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : 0 < (n + 1 : ℝ) := by positivity
    have h2 : 0 < ‖y n‖ + 1 := by positivity
    have h3 : ‖z n‖ = (‖y n‖ / (‖y n‖ + 1)) * (1 / (n + 1)) := by
      rw [hz, norm_smul, Real.norm_eq_abs, abs_of_pos (hapos n), ha]
      field_simp
    rw [h3]
    exact mul_le_of_le_one_left (by positivity) ((div_le_one h2).2 (by linarith))
  set K : Set V := insert 0 (range z)
  have hKc : IsCompact K := hzlim.isCompact_insert_range
  refine ⟨K, hKc.image (toWeakSpaceCLM ℝ V).continuous, ?_⟩
  have hsub : range y ⊆ Submodule.span ℝ K := by
    rintro _ ⟨n, rfl⟩
    have : y n = (a n)⁻¹ • z n := by
      rw [hz, smul_smul, inv_mul_cancel₀ (hapos n).ne', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_insert_of_mem _ ⟨n, rfl⟩))
  exact eq_univ_of_forall fun v => closure_mono hsub (hy.closure_eq ▸ mem_univ v)

end Glue

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {V} _ _ h => ?_, fun {V} _ _ _ => isWCG_of_separable,
    fun {V} _ _ => span_closedBall_eq_top'⟩
  have := completeSpace_of_isReflexive h
  exact (hB V).1 h

#rt_check RoundTrip.V5_61.A_to_B [Polyfold.proposition_5_5_15_reflexive,
  Polyfold.proposition_5_5_15_separable, Polyfold.span_closedBall_eq_top]
#rt_check RoundTrip.V5_61.B_to_A [Polyfold.proposition_5_5_15_reflexive,
  Polyfold.proposition_5_5_15_separable, Polyfold.span_closedBall_eq_top]
#rt_overlap RoundTrip.V5_61.B_to_A [Polyfold.proposition_5_5_15_reflexive,
  Polyfold.proposition_5_5_15_separable, Polyfold.span_closedBall_eq_top]

end RoundTrip.V5_61
