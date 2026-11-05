import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_55

/-!
Round trip for V5_55 (Theorem 5.37, "(i) ⇒ (ii)", the step "the sc-smooth function `f ∘ φ`
extended by `0` is supported in `W = φ⁻¹(V)` satisfying `cl_X(W) ⊆ U`, approximated by
`Σ β_x g(x)`").

`A` is the conjunction of the types of the two listed theorems `Polyfold.hasApproxProperty_restrict`
and `Polyfold.MChart.isClosed_inter_preimage`, universes instantiated at `0`.

* **B is false** (`not_B`), as its author predicted: B claims, literally, that `f ∘ φ` is
  sc-smooth on `dom φ` for every continuous `f : O → [0, 1]` with the support condition.  On the
  one-chart M-polyfold `ℝ` (`realPolyfold`, chart `realChart = id`, local model `(ℝ, ℝ, ℝ)`), which
  admits sc-smooth partitions of unity (`realPolyfold_admitsScPartitionsOfUnity`, from Mathlib's
  smooth partitions of unity on `ℝ` and `C^∞ ⇒ sc-smooth`), take `V = O = ℝ` and
  `f(x) = min(|x|, 1)`: sc-smoothness on the constant scale `ℝ` is `C^∞`
  (`isScSmooth_iff_contDiffOn_const`), and `f` is not differentiable at `0`.
  Hence `A → B` is false (`not_A_to_B`, A being true) and `B → A` holds ex falso.
* **The repaired reading** `BRepaired` ("sc-smooth" read as "continuous", `cl_X(φ⁻¹(V)) ⊆ U` as a
  hypothesis): `BRepaired → A` is proved (`BRepaired_to_A`).  Its last conjunct says that EVERY
  chart `φ` of an atlas equivalent to the structure has a local model with the sc-smooth
  approximation property; applied to the atlas of all charts of the structure and to the chart
  `φ.restrict s` (a chart of the structure) it gives `hasApproxProperty_restrict` (even without
  `cl_X(s) ⊆ dom φ`).  The second conjunct of A, `MChart.isClosed_inter_preimage`, is a point-set
  lemma unrelated to B; it is re-proved outright (`isClosed_inter_preimage_outright`).
  `A → BRepaired` is not proved: A gives the approximation property only for charts restricted to
  `s` with `cl_X(s) ⊆ dom φ`, not for every chart (the project leaves "every chart" open), and A
  does not provide the specific approximant `Σ_{x ∈ X} β_x ĝ(x)` of BRepaired's first conjunct.
-/

namespace RoundTrip.V5_55
open Polyfold Set Function Filter Topology

/-- The project's statement, universes `0`. -/
def A : Prop :=
  (type_of% @Polyfold.hasApproxProperty_restrict.{0}) ∧
  (type_of% @Polyfold.MChart.isClosed_inter_preimage.{0})

theorem A_holds : A :=
  ⟨@Polyfold.hasApproxProperty_restrict.{0}, @Polyfold.MChart.isClosed_inter_preimage.{0}⟩

/-! ### B is false -/

/-- The M-polyfold `ℝ` admits sc-smooth partitions of unity (Mathlib's smooth partitions of unity
on `ℝ`; `C^∞` functions are sc-smooth). -/
theorem realPolyfold_admitsScPartitionsOfUnity : realPolyfold.AdmitsScPartitionsOfUnity := by
  intro ι U hUo hUcov
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ ℝ) isClosed_univ U hUo
    (by rw [hUcov])
  exact ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity, fun i =>
    isScSmoothMap_real_of_contDiff (contMDiff_iff_contDiff.1 (f i).contMDiff)⟩

/-- `x ↦ min(|x|, 1)` is not differentiable at `0`. -/
lemma not_differentiableAt_minAbs : ¬ DifferentiableAt ℝ (fun x : ℝ => min |x| 1) 0 := by
  intro h
  refine not_differentiableAt_abs_zero (h.congr_of_eventuallyEq ?_)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  exact (min_eq_left hx.le).symm

/-- **B is false**: on `ℝ` with the chart `id`, `V = O = ℝ` and `f = min(|·|, 1)`, B claims that
`f ∘ id` is sc-smooth, i.e. `C^∞`. -/
theorem not_B : ¬ B := by
  intro hB
  have h := (hB ℝ realPolyfold realPolyfold_admitsScPartitionsOfUnity realPolyfold.atlas
    (MAtlas.Equiv.refl _) realChart (mem_singleton _)).1
  have hO : realChart.model.O = univ := rfl
  have hfc : ContinuousOn (fun x : ℝ => min |x| 1) univ :=
    (continuous_abs.min continuous_const).continuousOn
  have hf01 : ∀ x ∈ (univ : Set ℝ), (fun x : ℝ => min |x| 1) x ∈ Icc (0 : ℝ) 1 :=
    fun x _ => ⟨le_min (abs_nonneg x) zero_le_one, min_le_right _ _⟩
  obtain ⟨-, hsc, -, -⟩ := h univ (fun _ _ => mem_univ _) ⟨univ, isOpen_univ, by rw [hO, inter_univ]⟩
    (fun _ _ => mem_univ _) (fun x : ℝ => min |x| 1) hfc hf01 (fun _ _ => mem_univ _)
  have h1 := hsc.smooth realChart realChart isChart_realChart isChart_realChart univ isOpen_univ
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩) (fun _ _ => mem_univ _)
  have h2 := h1.comp_isScSmooth (ScRetraction.id real_relOpen_univ)
    (by change id '' univ = (fun x : ℝ => x) '' univ; rfl)
  have h3 : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => min |x| 1) univ :=
    (isScSmooth_iff_contDiffOn_const (V := ℝ) (W := ℝ) (isScDomain_univ _) _).1 h2
  exact not_differentiableAt_minAbs
    ((contDiffOn_univ.1 h3).differentiable (by simp) 0)

/-- A true statement does not imply B. -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- Ex falso. -/
theorem B_to_A : B → A := fun h => absurd h not_B

/-! ### The repaired reading -/

/-- The second conjunct of `A`, a point-set lemma, re-proved (it is unrelated to B). -/
theorem isClosed_inter_preimage_outright : type_of% @Polyfold.MChart.isClosed_inter_preimage.{0} := by
  intro X _ φ s hcl A hA hAs
  have hsub : φ.source ∩ φ ⁻¹' A ⊆ s := by
    rintro y ⟨hy, hyA⟩
    obtain ⟨y', hy', hyy'⟩ := hAs hyA
    have := φ.toPartialEquiv.injOn (hcl (subset_closure hy')) hy hyy'
    rwa [this] at hy'
  refine ⟨isClosed_of_closure_subset fun y hy => ?_, hsub⟩
  have hyφ : y ∈ φ.source := hcl (closure_mono hsub hy)
  have hcont : ContinuousAt φ y :=
    φ.continuousOn_toFun.continuousAt (φ.isOpen_source.mem_nhds hyφ)
  refine ⟨hyφ, ?_⟩
  have h1 := mem_closure_image hcont hy
  exact hA.closure_subset_iff.2 (image_subset_iff.2 fun z hz => hz.2) h1

/-- `BRepaired` implies `A`: its claim that every chart of an equivalent atlas has the
approximation property gives `hasApproxProperty_restrict` (for the atlas of all charts of the
structure); the point-set lemma is re-proved. -/
theorem BRepaired_to_A : BRepaired → A := by
  intro hB
  refine ⟨?_, isClosed_inter_preimage_outright⟩
  intro X _ _ _ PX h φ hφ s hs hso _
  let At : MAtlas X :=
    ⟨{ψ | PX.IsChart ψ}, fun ψ hψ χ hχ => MPolyfold.IsChart.compatible PX hψ hχ,
      fun x => PX.exists_isChart_mem_source x⟩
  have hAt : At.Equiv PX.atlas := (MAtlas.equiv_iff _ _).2 fun ψ hψ χ hχ => hψ χ hχ
  exact (hB X PX h At hAt (φ.restrict hs hso) (MPolyfold.IsChart.restrict PX hφ hs hso)).2

#rt_check RoundTrip.V5_55.B_to_A [Polyfold.hasApproxProperty_restrict,
  Polyfold.MChart.isClosed_inter_preimage]
#rt_check RoundTrip.V5_55.not_B [Polyfold.hasApproxProperty_restrict,
  Polyfold.MChart.isClosed_inter_preimage]
#rt_check RoundTrip.V5_55.BRepaired_to_A [Polyfold.hasApproxProperty_restrict,
  Polyfold.MChart.isClosed_inter_preimage]
#rt_overlap RoundTrip.V5_55.B_to_A [Polyfold.hasApproxProperty_restrict,
  Polyfold.MChart.isClosed_inter_preimage]
#rt_overlap RoundTrip.V5_55.BRepaired_to_A [Polyfold.hasApproxProperty_restrict,
  Polyfold.MChart.isClosed_inter_preimage]

end RoundTrip.V5_55
