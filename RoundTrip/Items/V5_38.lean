import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_38

/-!
Round trip for V5_38 (Theorem 5.18).  `A` is the type of `Polyfold.theorem_5_18`, universes
instantiated at `0`.

Neither `A → B` nor `B → A` is proved.

* `A → B` fails at one hypothesis only: B reads "bump functions" (Definition 5.9, "`f ≠ 0`") as
  "not identically zero" (`AdmitsBumpFunctionsWeak`), A as "`f(x) ≠ 0`" (`AdmitsBumpFunctions`).
  With the strong reading, `A → Bstrong` is proved below (`A_to_Bstrong`): the dense set `O` is
  `{s allowable | f + s satisfies SolutionSetInGeneralPosition}`, its `ρ`-density is derived from
  A's generic (family) form by the argument the project uses for `theorem_5_18_dense`, re-done here
  (`dense_of_generic`, not using any banned declaration); B's tameness of the bundle is not needed.
  `Bstrong` is B with `AdmitsBumpFunctions` in place of `AdmitsBumpFunctionsWeak` (B ⇒ Bstrong
  trivially, `B_to_Bstrong`).
* `B → A` fails: B assumes a tame strong bundle (an equivalent atlas of tame strong bundle charts),
  A only `PX.IsTame`; and B's conclusion is the dense-set form, while A's is the generic form (for
  every `s₀` with `N(s₀) ≤ 1 − ε` a finite family `s₀ + Σ λᵢ tᵢ` good for almost every small `λ`),
  plus A's `SolutionSetInGeneralPosition` gives more (transversality, `S` a smooth submanifold in
  general position, tame).
-/

/-! **Refresh 2026-11-02** (HEAD after the germ reading of Definition 3.11 and the notions built
on it).
theorem_5_18 and B now both use the germ-reading IsScFredholmSectionTame. The obstacles (weak vs
pointwise bump functions for A ⇒ B; B's tame strong bundle atlas and dense-set form for B ⇒ A) are
untouched by the germ switch; A ⇒ Bstrong still checks. Result unchanged.
-/

namespace RoundTrip.V5_38
open Polyfold MeasureTheory

/-- The project's statement, universes `0`. -/
def A : Prop := type_of% @Polyfold.theorem_5_18.{0, 0}

theorem A_holds : A := @Polyfold.theorem_5_18.{0, 0}

/-- B with the strong reading of "bump functions" (`f(x) ≠ 0`). -/
def Bstrong : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (N : Bd.One → ℝ),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctions →
    Bd.IsScFredholmSectionTame f → IsCompact (solSet P f) → Bd.IsAuxNorm N →
      ∃ U : Set X, IsOpen U ∧ solSet P f ⊆ U ∧
        (∀ s ∈ Bd.allowableSections N U, IsCompact (solSet P (sectionAdd P f s))) ∧
        ∃ O : Set (X → Y), IsRhoDense Bd N (Bd.allowableSections N U) O ∧
          ∀ s ∈ O,
            (∀ x ∈ solSet P (sectionAdd P f s), Bd.IsGeneralPositionGerm (sectionAdd P f s) x) ∧
            IsCompact (solSet P (sectionAdd P f s)) ∧
            ∃ (hS : PX.IsSubMPolyfold (solSet P (sectionAdd P f s)))
              (_ : ParacompactSpace (solSet P (sectionAdd P f s))),
              (PX.subPolyfold hS).HasCornerStructure ∧
              ∀ x : solSet P (sectionAdd P f s), (PX.subPolyfold hS).degIndex x = PX.degIndex x

theorem B_to_Bstrong : B → Bstrong := fun hB _X _ _ _ PX _Y _ _ _ P _ _ Bd f N hT hbump =>
  hB PX P Bd f N hT hbump.weak

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {Bd : StrongBundle PX P}

theorem sectionDistAt_comm {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N) {s s' : X → Y}
    (hs : Bd.IsScPlusSection s) (hs' : Bd.IsScPlusSection s') (x : X) :
    Bd.sectionDistAt N hs hs' x = Bd.sectionDistAt N hs' hs x := by
  unfold StrongBundle.sectionDistAt
  have h := (hN.fiber x).smul (-1)
    ((⟨⟨s x, hs.1 x⟩, hs.mem_oneSet x⟩ : Bd.oneFiber x) - ⟨⟨s' x, hs'.1 x⟩, hs'.mem_oneSet x⟩)
  rw [neg_one_smul, neg_sub, abs_neg, abs_one, one_mul] at h
  exact h.symm

set_option maxHeartbeats 1600000 in
/-- The dense-set form from the generic (family) form, for any property `Q` of the perturbation
(the argument of the project's `theorem_5_13` / `theorem_5_18_dense`: `s₀ = (1 − ε'/2)s'` and a
parameter `λ` outside the null set in a small ball). -/
theorem dense_of_generic {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N) {U : Set X}
    (Q : (X → Y) → Prop)
    (hgen : ∀ (s₀ : X → Y) (hs₀ : Bd.IsScPlusSection s₀), sectionSupport P s₀ ⊆ U → ∀ ε > 0,
      (∀ x (hx : s₀ x ∈ Bd.oneSet), N (Bd.oneMk (s₀ x) hx) ≤ 1 - ε) →
      ∃ (m : ℕ) (t : Fin m → X → Y) (ht : ∀ i, Bd.IsScPlusSection (t i)),
        (∀ i, sectionSupport P (t i) ⊆ U) ∧
        (∀ i x (hx : t i x ∈ Bd.oneSet), N (Bd.oneMk (t i x) hx) ≤ 1) ∧
        ∃ δ > 0, ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
          ∀ lam : Fin m → ℝ, ‖lam‖ < δ → lam ∉ CV →
            paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam ∈ Bd.allowableSections N U ∧
            Q (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam))
    (s' : X → Y) (hs' : Bd.IsScPlusSection s') (hs'alw : s' ∈ Bd.allowableSections N U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : X → Y) (hs : Bd.IsScPlusSection s), s ∈ Bd.allowableSections N U ∧
      (∀ x, Bd.sectionDistAt N hs hs' x ≤ ε) ∧ Q s := by
  classical
  obtain ⟨-, hs'supp, hs'N⟩ := hs'alw
  set ε' : ℝ := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'le1 : ε' ≤ 1 := min_le_right _ _
  set θ : ℝ := 1 - ε' / 2 with hθ
  have hθpos : 0 < θ := by rw [hθ]; linarith
  set s₀ : X → Y := sectionSmul P (fun _ => θ) s' with hs₀def
  have hs₀ : Bd.IsScPlusSection s₀ := hs'.smul_left (isScSmoothMap_real_const _)
  have hs₀supp : sectionSupport P s₀ ⊆ U :=
    (sectionSupport_sectionSmul_const_subset hs'.1 θ).trans hs'supp
  have hs₀N : ∀ x (hx : s₀ x ∈ Bd.oneSet), N (Bd.oneMk (s₀ x) hx) ≤ 1 - ε' / 2 := fun x hx => by
    rw [hN.oneMk_sectionSmul_const hs' θ x hx, abs_of_pos hθpos]
    calc θ * N (Bd.oneMk (s' x) (hs'.mem_oneSet x)) ≤ θ * 1 :=
          mul_le_mul_of_nonneg_left (hs'N x _) hθpos.le
      _ = 1 - ε' / 2 := by rw [mul_one]
  obtain ⟨m, t, ht, htsupp, htN, δ, hδ, CV, hCV, hlam⟩ :=
    hgen s₀ hs₀ hs₀supp (ε' / 2) (by positivity) hs₀N
  set r : ℝ := min δ (ε' / (2 * (m + 1))) with hr
  have hrpos : 0 < r := lt_min hδ (by positivity)
  obtain ⟨lam, hlamr, hlamCV⟩ : ∃ lam ∈ Metric.ball (0 : Fin m → ℝ) r, lam ∉ CV := by
    by_contra h
    have h1 : Metric.ball (0 : Fin m → ℝ) r ⊆ CV := fun lam hl => by
      by_contra hc
      exact h ⟨lam, hl, hc⟩
    have h2 := measure_mono_null h1 hCV
    exact (Metric.measure_ball_pos volume (0 : Fin m → ℝ) hrpos).ne' h2
  have hlamδ : ‖lam‖ < δ := lt_of_lt_of_le (mem_ball_zero_iff.1 hlamr) (min_le_left _ _)
  have hlamε : (m : ℝ) * ‖lam‖ ≤ ε' / 2 := by
    have h1 : ‖lam‖ ≤ ε' / (2 * (m + 1)) :=
      (mem_ball_zero_iff.1 hlamr).le.trans (min_le_right _ _)
    calc (m : ℝ) * ‖lam‖ ≤ m * (ε' / (2 * (m + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (ε' / 2) * (m / (m + 1)) := by field_simp
      _ ≤ (ε' / 2) * 1 := mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity)).2 (by linarith)) (by positivity)
      _ = ε' / 2 := mul_one _
  obtain ⟨halw, hQ⟩ := hlam lam hlamδ hlamCV
  have hsl : Bd.IsScPlusSection (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) :=
    isScPlusSection_paramSlice hs₀ ht lam
  refine ⟨_, hsl, halw, fun x => ?_, hQ⟩
  set u' : Bd.oneFiber x := ⟨⟨s' x, hs'.1 x⟩, hs'.mem_oneSet x⟩ with hu'
  set w : Fin m → Bd.oneFiber x := fun i => ⟨⟨t i x, (ht i).1 x⟩, (ht i).mem_oneSet x⟩ with hw
  have hu : (⟨⟨paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x, hsl.1 x⟩, hsl.mem_oneSet x⟩ :
      Bd.oneFiber x) = θ • u' + ∑ i, lam i • w i := by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    apply Subtype.ext
    change paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x = _
    unfold paramSlice
    have h1 : (⟨s₀ x, hs₀.1 x⟩ : P ⁻¹' {x}) = θ • ⟨s' x, hs'.1 x⟩ :=
      Subtype.ext (sectionSmul_apply (f := fun _ => θ) hs'.1 x)
    rw [h1]
    rfl
  have hdiff : (⟨⟨paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x, hsl.1 x⟩, hsl.mem_oneSet x⟩ :
      Bd.oneFiber x) - u' = (θ - 1) • u' + ∑ i, lam i • w i := by
    rw [hu, add_sub_right_comm, hθ]
    simp only [sub_smul, one_smul]
  have hli : ∀ i, |lam i| ≤ ‖lam‖ := fun i => by
    have := norm_le_pi_norm lam i
    rwa [Real.norm_eq_abs] at this
  have hwN : ∀ i, N (Bd.toOne (w i)) ≤ 1 := fun i => htN i x ((ht i).mem_oneSet x)
  have hu'N : N (Bd.toOne u') ≤ 1 := hs'N x _
  change N (Bd.toOne (_ - u')) ≤ ε
  rw [hdiff]
  calc N (Bd.toOne ((θ - 1) • u' + ∑ i, lam i • w i))
      ≤ N (Bd.toOne ((θ - 1) • u')) + N (Bd.toOne (∑ i, lam i • w i)) :=
        (hN.fiber x).add_le _ _
    _ = |θ - 1| * N (Bd.toOne u') + N (Bd.toOne (∑ i, lam i • w i)) := by rw [hN.smul]
    _ ≤ (ε' / 2) * 1 + ∑ i, N (Bd.toOne (lam i • w i)) := by
        refine add_le_add ?_ (hN.toOne_sum_le _ _)
        have hθ1 : |θ - 1| = ε' / 2 := by
          rw [hθ, show (1 - ε' / 2 - 1 : ℝ) = -(ε' / 2) by ring, abs_neg,
            abs_of_pos (by positivity)]
        rw [hθ1]
        exact mul_le_mul_of_nonneg_left hu'N (by positivity)
    _ = ε' / 2 + ∑ i, |lam i| * N (Bd.toOne (w i)) := by
        rw [mul_one]
        congr 1
        exact Finset.sum_congr rfl fun i _ => hN.smul (w i) (lam i)
    _ ≤ ε' / 2 + ∑ _i : Fin m, ‖lam‖ * 1 :=
        add_le_add le_rfl (Finset.sum_le_sum fun i _ =>
          mul_le_mul (hli i) (hwN i) (hN.nonneg _) (norm_nonneg _))
    _ = ε' / 2 + (m : ℝ) * ‖lam‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    _ ≤ ε := by linarith

end Glue

/-- A gives B with the strong reading of bump functions. -/
theorem A_to_Bstrong : A → Bstrong := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f N hT hbump hf hS hN
  obtain ⟨U, hUo, hSU, hcpt, hgen⟩ := hA hT.1 hbump hf hS hN
  refine ⟨U, hUo, hSU, hcpt,
    {s | s ∈ Bd.allowableSections N U ∧ Bd.SolutionSetInGeneralPosition (sectionAdd P f s)},
    ⟨fun s hs => hs.1, fun s hs δ hδ => ?_⟩, fun s hs => ?_⟩
  · obtain ⟨s', hs', halw, hdist, hQ⟩ := dense_of_generic hN
      (fun s => Bd.SolutionSetInGeneralPosition (sectionAdd P f s)) hgen s hs.1 hs (δ / 2)
      (by positivity)
    refine ⟨s', ⟨halw, hQ⟩, hs.1, hs', δ / 2, by linarith, fun x => ?_⟩
    rw [sectionDistAt_comm hN]
    exact hdist x
  · obtain ⟨-, hgp, hcomp, hS', -, hcs, -, hdeg⟩ := hs.2
    exact ⟨fun x hx => hgp x hx, hcomp, hS'.isSubMPolyfold, PX.paracompactSpace_subtype _, hcs,
      hdeg⟩

#rt_check RoundTrip.V5_38.A_to_Bstrong [Polyfold.theorem_5_18]

end RoundTrip.V5_38
