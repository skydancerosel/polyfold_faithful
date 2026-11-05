import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_59

/-!
Round trip for V5_59 (Definition 5.39; Theorem 5.40 as a statement).  The theorems listed are
`Polyfold.mem_cZero_iff` and `Polyfold.norm_cZero`, so `A` is the conjunction of their types,
universes instantiated at `0`; `cZero`, `IsCoordinatewiseContDiffEmbedding` and
`TorunczykStatement` are vocabulary, compared with B's notions below.

* (1) elements of `c₀(Γ)`: `mem_cZero_iff` is literally B's `c0SetB` condition; the second half
  (every function with that condition is bounded, hence in `ℓ^∞`) is proved directly.
* (2) the norm: A gives `‖f‖ = sup_γ |f(γ)|`; B says `|f(γ)| ≤ ‖f‖` with equality at some `γ`
  (or `Γ = ∅`).  A ⇒ B: the supremum is attained, because `{γ | ‖f‖/2 < |f(γ)|}` is finite and
  non-empty when `‖f‖ > 0`.  B ⇒ A: a bound attained at a point is the supremum.
* (3) `Topology.IsEmbedding h` is B's metric "injective, continuous, inverse continuous on the
  image" (`isEmbedding_iff_metric`); the coordinate conditions are identical.
* (4) the project's `AdmitsContDiffPartitionsOfUnity` (Mathlib `PartitionOfUnity`, subordinate,
  `C^k`) is B's `AdmitsCkPOUB` (locally finite closed supports vs. supports: `ρ.locallyFinite_tsupport`
  and `LocallyFinite.subset`); hence `TorunczykStatement V k ↔ TorunczykB V k`.
(3) and (4) are about the vocabulary only and are proved without `A`.
-/

namespace RoundTrip.V5_59
open Polyfold Set Filter Topology
open scoped ENNReal

/-- The project's statement, universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.mem_cZero_iff.{0}) ∧ (type_of% @Polyfold.norm_cZero.{0})

theorem A_holds : A := ⟨@Polyfold.mem_cZero_iff.{0}, @Polyfold.norm_cZero.{0}⟩

section Glue

/-- A homeomorphic embedding of metric spaces, written metrically. -/
theorem isEmbedding_iff_metric {α β : Type*} [MetricSpace α] [MetricSpace β] (f : α → β) :
    IsEmbedding f ↔ Function.Injective f ∧ Continuous f ∧
      ∀ a : α, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a' : α, dist (f a') (f a) < δ → dist a' a < ε := by
  constructor
  · intro he
    refine ⟨he.injective, he.continuous, fun a ε hε => ?_⟩
    have h1 : Metric.ball a ε ∈ comap f (𝓝 (f a)) := by
      rw [← he.isInducing.nhds_eq_comap a]; exact Metric.ball_mem_nhds a hε
    obtain ⟨δ, hδ, hsub⟩ := (Metric.nhds_basis_ball.comap f).mem_iff.1 h1
    exact ⟨δ, hδ, fun a' ha' => hsub ha'⟩
  · rintro ⟨hinj, hcont, hm⟩
    refine ⟨isInducing_iff_nhds.2 fun a => le_antisymm (hcont.tendsto a).le_comap ?_, hinj⟩
    refine Metric.nhds_basis_ball.ge_iff.2 fun ε hε => ?_
    obtain ⟨δ, hδ, h⟩ := hm a ε hε
    exact ⟨Metric.ball (f a) δ, Metric.ball_mem_nhds _ hδ, fun a' ha' => h a' ha'⟩

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coordEmb_iff {Γ : Type} (k : ℕ∞) (h : V → cZero Γ) :
    IsCoordinatewiseContDiffEmbedding k h ↔ IsCoordEmbB k h := by
  unfold IsCoordinatewiseContDiffEmbedding IsCoordEmbB
  rw [isEmbedding_iff_metric]
  tauto

theorem pou_iff (k : ℕ∞) : AdmitsContDiffPartitionsOfUnity V k ↔ AdmitsCkPOUB V k := by
  constructor
  · intro h ι U hU hcov
    obtain ⟨ρ, hsub, hρ⟩ := h ι U hU hcov
    exact ⟨fun i => ρ i, hρ, fun i x => ρ.nonneg i x, ρ.locallyFinite_tsupport,
      fun x => ρ.sum_eq_one (mem_univ x), hsub⟩
  · intro h ι U hU hcov
    obtain ⟨ρ, hρc, hnn, hlf, hsum, hsub⟩ := h ι U hU hcov
    refine ⟨{ toFun := fun i => ⟨ρ i, (hρc i).continuous⟩
              locallyFinite' := hlf.subset fun i => subset_tsupport _
              nonneg' := fun i x => hnn i x
              sum_eq_one' := fun x _ => hsum x
              sum_le_one' := fun x => (hsum x).le }, hsub, hρc⟩

theorem torunczyk_iff (k : ℕ∞) : TorunczykStatement V k ↔ TorunczykB V k :=
  iff_congr (pou_iff k) (exists_congr fun _ => exists_congr fun h => coordEmb_iff k h)

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hmem, hnorm⟩
  refine ⟨fun Γ F => hmem, fun Γ f hf => ?_, fun Γ F => ?_,
    fun V _ _ _ Γ k h => coordEmb_iff k h, fun V _ _ _ k => ⟨pou_iff k, torunczyk_iff k⟩⟩
  · -- every `c₀` function is bounded
    have hS : {γ | (1 : ℝ) < |f γ|}.Finite := hf 1 one_pos
    obtain ⟨b, hb⟩ := (hS.image fun γ => ‖f γ‖).bddAbove
    have hmemp : Memℓp f ∞ := by
      refine memℓp_infty_iff.2 ⟨max b 1, ?_⟩
      rintro _ ⟨γ, rfl⟩
      by_cases hγ : (1 : ℝ) < |f γ|
      · exact (hb ⟨γ, hγ, rfl⟩).trans (le_max_left _ _)
      · exact (le_of_not_gt hγ).trans (le_max_right _ _)
    refine ⟨⟨f, hmemp⟩, hmem.2 fun ε hε => hf ε hε, fun γ => rfl⟩
  · -- the norm is a maximum
    have hbdd : BddAbove (range fun γ => ‖(F : lp (fun _ : Γ => ℝ) ∞) γ‖) :=
      memℓp_infty_iff.1 (lp.memℓp (F : lp (fun _ : Γ => ℝ) ∞))
    have hle : ∀ γ, |(F : lp (fun _ : Γ => ℝ) ⊤) γ| ≤ ‖F‖ := fun γ => by
      rw [hnorm F, ← Real.norm_eq_abs]; exact le_ciSup hbdd γ
    refine ⟨hle, ?_⟩
    rcases isEmpty_or_nonempty Γ with hΓ | hΓ
    · exact Or.inr ⟨hΓ, by rw [hnorm F]; exact Real.iSup_of_isEmpty _⟩
    left
    rcases (norm_nonneg F).eq_or_lt with h0 | hpos
    · obtain ⟨γ⟩ := hΓ
      refine ⟨γ, le_antisymm (hle γ) ?_⟩
      rw [← h0]; exact abs_nonneg _
    set S := {γ | ‖F‖ / 2 < |(F : lp (fun _ : Γ => ℝ) ⊤) γ|} with hSdef
    have hSf : S.Finite := hmem.1 F.2 (‖F‖ / 2) (half_pos hpos)
    have hSne : hSf.toFinset.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty, Finite.toFinset_eq_empty] at hne
      have h1 : ‖F‖ ≤ ‖F‖ / 2 := by
        rw [hnorm F]
        refine ciSup_le fun γ => ?_
        rw [Real.norm_eq_abs]
        by_contra h
        have : γ ∈ S := lt_of_not_ge h
        rw [hne] at this; exact this
      linarith
    obtain ⟨γ₀, hγ₀, hmax⟩ := hSf.toFinset.exists_max_image
      (fun γ => |(F : lp (fun _ : Γ => ℝ) ⊤) γ|) hSne
    rw [Finite.mem_toFinset] at hγ₀
    refine ⟨γ₀, le_antisymm (hle γ₀) ?_⟩
    rw [hnorm F]
    refine ciSup_le fun γ => ?_
    rw [Real.norm_eq_abs]
    by_cases hγ : γ ∈ S
    · exact hmax γ (hSf.mem_toFinset.2 hγ)
    · exact (le_of_not_gt hγ).trans hγ₀.le

theorem B_to_A : B → A := by
  rintro ⟨hmem, -, hnorm, -, -⟩
  refine ⟨fun {Γ f} => hmem Γ f, fun {Γ} F => ?_⟩
  obtain ⟨hle, hmax⟩ := hnorm Γ F
  rcases hmax with ⟨γ₀, hγ₀⟩ | ⟨hΓ, h0⟩
  · have hbdd : BddAbove (range fun γ => ‖(F : lp (fun _ : Γ => ℝ) ∞) γ‖) :=
      ⟨‖F‖, by rintro _ ⟨γ, rfl⟩; exact (Real.norm_eq_abs _).trans_le (hle γ)⟩
    have : Nonempty Γ := ⟨γ₀⟩
    refine le_antisymm ?_ (ciSup_le fun γ => (Real.norm_eq_abs _).trans_le (hle γ))
    rw [← hγ₀, ← Real.norm_eq_abs]
    exact le_ciSup hbdd γ₀
  · rw [h0, Real.iSup_of_isEmpty]

#rt_check RoundTrip.V5_59.A_to_B [Polyfold.mem_cZero_iff, Polyfold.norm_cZero]
#rt_check RoundTrip.V5_59.B_to_A [Polyfold.mem_cZero_iff, Polyfold.norm_cZero]
#rt_overlap RoundTrip.V5_59.B_to_A [Polyfold.mem_cZero_iff, Polyfold.norm_cZero]

end RoundTrip.V5_59
