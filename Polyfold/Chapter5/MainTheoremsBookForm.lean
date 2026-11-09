import Polyfold.Chapter5.GeneralPosition

/-!
# Theorems 5.3.10 and 5.3.12 stated as the book states them

2021 Theorem 5.3.10, p. 220 (2017: Theorem 5.6; preprint: Theorem 5.18, p. 177) and 2021 Theorem
5.3.12, p. 222 (2017: Theorem 5.7; preprint: Theorem 5.19, p. 180).  The project's `theorem_5_3_10_param`
and `theorem_5_3_12_param` (`Chapter5/GeneralPosition.lean`) state these theorems in the form their proofs
produce: a finite family `t₁, …, t_m` of sc⁺-sections, the perturbation `paramSlice s₀ … t λ`, a
`δ > 0` and a null set of parameters, with an auxiliary norm bound on every `tᵢ`.  These objects
come from the proofs; the book's statements do not mention them.  This file states the two
theorems with the book's quantifiers only, as corollaries of the project's theorems.

## The text, paraphrased

(Theorem 5.3.10) Let `P : Y → X` be a strong bundle over a tame M-polyfold admitting sc-smooth
bump functions, `f` an sc-Fredholm section with compact solution set and `N` an auxiliary norm.
Then there is an open `U ⊇ S_f` such that `S_{f+s}` is compact for every `s ∈ Γ^{+,1}_U(P)`
(sc⁺-sections with support in `U` and `N(s(x)) ≤ 1`), and a dense subset `O` of the metric space
`(Γ^{+,1}_U(P), ρ)` such that for every `s ∈ O` and `x ∈ S_{f+s}` the pair `(f + s, x)` is in
general position (Definition 5.3.9); in particular `S_{f+s}` is a sub-M-polyfold whose induced
structure is that of a compact manifold with boundary with corners, with `d_{S_{f+s}} = d_X`.

(Theorem 5.3.12) Same bundle and section (no tameness of `X` is asked), and `(f, x)` in good
position at every zero `x ∈ ∂X`.  Then there is an open `U ⊇ S_f` such that `S_{f+s}` is compact
for every `s ∈ Γ^{+,1}_U(P)`, and an arbitrarily small `s ∈ Γ^{+,1}_U(P)` vanishing near `∂X`
such that `f + s` is transversal to the zero section and is in good position at every point of
`S_{f+s}`; in particular `S_{f+s}` is a sub-M-polyfold whose induced structure is that of a compact
manifold with boundary with corners.

## What is formalized

* `theorem_5_3_10`: Theorem 5.3.10 with the book's quantifiers (from `theorem_5_3_10_dense`).
* `theorem_5_3_12`: Theorem 5.3.12 with the book's quantifiers (from `theorem_5_3_12_param`).

## Readings

The notions are the project's, as in `theorem_5_3_10_param` and `theorem_5_3_12_param`:

* "sc-Fredholm section" is `IsScFredholmSectionTame` (germ data in a tame chart, row V3.103);
  "in general position" (Definition 5.3.9) is `IsGeneralPositionGerm`; "in good position" is
  `IsGoodPositionGermTame`; "transversal to the zero section" (Definition 5.3.7) is
  `IsTransversal`; `Γ^{+,1}_U(P)` is `allowableSections N U`.
* **Density** in `(Γ^{+,1}_U(P), ρ)`, `ρ(s, s') = sup_x N(s(x) − s'(x))`, is read pointwise: for
  every `s'` in `Γ^{+,1}_U(P)` and `ε > 0` there is `s ∈ O` with `N(s(x) − s'(x)) ≤ ε` for all `x`
  (`sectionDistAt`), which is `ρ(s, s') ≤ ε`.  The metric space itself is not built (Findings,
  Chapter 5, item 89).
* **"Arbitrarily small"** in Theorem 5.3.12 is read in the same distance: for every `ε > 0`,
  `N(s(x)) ≤ ε` for all `x`.  "`s(x) = 0` near `∂X`" is `∀ᶠ x in 𝓝ˢ ∂X, s(x) = 0`.
* "Manifold with boundary with corners" is `HasCornerStructure` in Theorem 5.3.10 and
  `IsManifoldWithCornersLoc` in Theorem 5.3.12, the forms the two project theorems prove; in
  Theorem 5.3.12 the sub-M-polyfold clause is stated for non-empty `S_{f+s}`, as in
  `theorem_5_3_12_param`.
* In Theorem 5.3.12 the text writes "the pair `(f, x)` is in good position" for `x ∈ S_{f+s}`;
  as we read it, the pair meant is `(f + s, x)` (good position is defined at zeros of the
  section), which is what is stated.
-/

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u v

section BookForm

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **2021 Theorem 5.3.10, p. 220 (perturbation: general position)** (2017: Theorem 5.6;
preprint: Theorem 5.18), with the book's quantifiers.  Let `P : Y → X` be a strong bundle over a
tame M-polyfold admitting sc-smooth bump functions, `f` an sc-Fredholm section with compact
solution set and `N` an auxiliary norm.  There is an open `U ⊇ S_f` such that `S_{f+s}` is
compact for every `s ∈ Γ^{+,1}_U(P)`, and a subset `O ⊆ Γ^{+,1}_U(P)`, dense for
`ρ(s, s') = sup_x N(s(x) − s'(x))`, such that for every `s ∈ O`, `(f + s, x)` is in general
position at every `x ∈ S_{f+s}`; in particular `S_{f+s}` is a compact sub-M-polyfold whose induced
structure is that of a manifold with boundary with corners, with `d_{S_{f+s}} = d_X`. -/
theorem theorem_5_3_10 (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∃ O ⊆ B.allowableSections N U,
        (∀ (s' : X → Y) (hs' : B.IsScPlusSection s'), s' ∈ B.allowableSections N U → ∀ ε > 0,
          ∃ (s : X → Y) (hs : B.IsScPlusSection s), s ∈ O ∧ ∀ x, B.sectionDistAt N hs hs' x ≤ ε) ∧
        ∀ s ∈ O,
          (∀ x ∈ solutionSet P (sectionAdd P f s), B.IsGeneralPositionGerm (sectionAdd P f s) x) ∧
          IsCompact (solutionSet P (sectionAdd P f s)) ∧
          ∃ hsub : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f s)),
            haveI := PX.paracompactSpace_subtype (solutionSet P (sectionAdd P f s))
            (MPolyfold.subPolyfold hsub).HasCornerStructure ∧
              ∀ a : solutionSet P (sectionAdd P f s),
                (MPolyfold.subPolyfold hsub).degIndex a = PX.degIndex a := by
  obtain ⟨U, hUo, hSU, hcpt, hdense⟩ := theorem_5_3_10_dense hX hbump hf hS hN
  refine ⟨U, hUo, hSU, hcpt,
    {s | s ∈ B.allowableSections N U ∧ B.SolutionSetInGeneralPosition (sectionAdd P f s)},
    fun s hs => hs.1, fun s' hs' hs'alw ε hε => ?_, fun s hs => ?_⟩
  · obtain ⟨s, hs, halw, hd, hgp⟩ := hdense s' hs' hs'alw ε hε
    exact ⟨s, hs, ⟨halw, hgp⟩, hd⟩
  · obtain ⟨-, hgen, hcomp, hsm, -, hcorner, -, hdeg⟩ := hs.2
    exact ⟨fun x hx => hgen x hx, hcomp, hsm.isSubMPolyfold, hcorner, hdeg⟩

/-- **2021 Theorem 5.3.12, p. 222 (perturbation and transversality: good position)** (2017:
Theorem 5.7; preprint: Theorem 5.19), with the book's quantifiers.  Let `P : Y → X` be a strong
bundle over an M-polyfold admitting sc-smooth bump functions, `f` an sc-Fredholm section with
compact solution set, `N` an auxiliary norm, and `(f, x)` in good position at every zero
`x ∈ ∂X`.  There is an open `U ⊇ S_f` such that `S_{f+s}` is compact for every
`s ∈ Γ^{+,1}_U(P)`, and for every `ε > 0` a section `s ∈ Γ^{+,1}_U(P)` with `N(s(x)) ≤ ε`,
vanishing near `∂X`, such that `f + s` is transversal to the zero section and in good position at
every point of `S_{f+s}`; in particular, if non-empty, `S_{f+s}` is a sub-M-polyfold whose induced
structure is that of a manifold with boundary with corners (compact by the first clause). -/
theorem theorem_5_3_12 (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N)
    (hbd : ∀ x ∈ PX.boundary, IsZeroAt P f x → B.IsGoodPositionGermTame f x) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ ε > 0, ∃ s ∈ B.allowableSections N U,
        (∀ x (hx : s x ∈ B.oneSet), N (B.oneMk (s x) hx) ≤ ε) ∧
        (∀ᶠ x in 𝓝ˢ PX.boundary, IsZeroAt P s x) ∧
        B.IsTransversal (sectionAdd P f s) ∧
        (∀ x ∈ solutionSet P (sectionAdd P f s), B.IsGoodPositionGermTame (sectionAdd P f s) x) ∧
        ((solutionSet P (sectionAdd P f s)).Nonempty →
          ∃ hsub : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f s)),
            haveI := PX.paracompactSpace_subtype (solutionSet P (sectionAdd P f s))
            (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc) := by
  classical
  obtain ⟨U, hUo, hSU, hcpt, m, t, ht, -, -, htN, δ, hδ, CV, hCV, hlam⟩ :=
    theorem_5_3_12_param hbump hf hS hN hbd
  refine ⟨U, hUo, hSU, hcpt, fun ε hε => ?_⟩
  -- a parameter `λ ∉ CV` with `|λ| < δ` and `m|λ| ≤ ε`
  set r : ℝ := min δ (ε / (m + 1)) with hr
  have hrpos : 0 < r := lt_min hδ (by positivity)
  obtain ⟨lam, hlamr, hlamCV⟩ : ∃ lam ∈ Metric.ball (0 : Fin m → ℝ) r, lam ∉ CV := by
    by_contra h
    have h1 : Metric.ball (0 : Fin m → ℝ) r ⊆ CV := fun lam hl => by
      by_contra hc
      exact h ⟨lam, hl, hc⟩
    exact (Metric.measure_ball_pos volume (0 : Fin m → ℝ) hrpos).ne' (measure_mono_null h1 hCV)
  have hlamδ : ‖lam‖ < δ := lt_of_lt_of_le (mem_ball_zero_iff.1 hlamr) (min_le_left _ _)
  have hlamε : (m : ℝ) * ‖lam‖ ≤ ε := by
    have h1 : ‖lam‖ ≤ ε / (m + 1) :=
      (mem_ball_zero_iff.1 hlamr).le.trans (min_le_right _ _)
    calc (m : ℝ) * ‖lam‖ ≤ m * (ε / (m + 1)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ε * (m / (m + 1)) := by field_simp
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).2 (by linarith))
          hε.le
      _ = ε := mul_one _
  obtain ⟨halw, hdisj, htr, hgood, -, hsub⟩ := hlam lam hlamδ hlamCV
  set s := paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam with hsdef
  have hsl : B.IsScPlusSection s :=
    isScPlusSection_paramSlice StrongBundle.isScPlusSection_fiberZero ht lam
  refine ⟨s, halw, fun x hx => ?_, ?_, htr, fun x hx => hgood x hx, fun hne => ?_⟩
  · -- `s(x) = Σ λᵢ tᵢ(x)` in the fibre, so `N(s(x)) ≤ Σ |λᵢ| N(tᵢ(x)) ≤ m|λ|`
    set w : Fin m → B.oneFiber x := fun i => ⟨⟨t i x, (ht i).1 x⟩, (ht i).mem_oneSet x⟩ with hw
    have hu : (⟨⟨s x, hsl.1 x⟩, hx⟩ : B.oneFiber x) = ∑ i, lam i • w i := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      apply Subtype.ext
      change paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam x = _
      unfold paramSlice
      have h0 : (⟨fiberZero P x, isSection_fiberZero x⟩ : P ⁻¹' {x}) = 0 := rfl
      rw [h0, zero_add]
      rfl
    have hli : ∀ i, |lam i| ≤ ‖lam‖ := fun i => by
      have := norm_le_pi_norm lam i
      rwa [Real.norm_eq_abs] at this
    have hwN : ∀ i, N (B.toOne (w i)) ≤ 1 := fun i => htN i x ((ht i).mem_oneSet x)
    change N (B.toOne (⟨⟨s x, hsl.1 x⟩, hx⟩ : B.oneFiber x)) ≤ ε
    rw [hu]
    calc N (B.toOne (∑ i, lam i • w i)) ≤ ∑ i, N (B.toOne (lam i • w i)) := hN.toOne_sum_le _ _
      _ = ∑ i, |lam i| * N (B.toOne (w i)) :=
          Finset.sum_congr rfl fun i _ => hN.smul (w i) (lam i)
      _ ≤ ∑ _i : Fin m, ‖lam‖ * 1 :=
          Finset.sum_le_sum fun i _ => mul_le_mul (hli i) (hwN i) (hN.nonneg _) (norm_nonneg _)
      _ = (m : ℝ) * ‖lam‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      _ ≤ ε := hlamε
  · -- `s = 0` off its support, an open set containing `∂X`
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhdsSet.2 hdisj.subset_compl_left]
      with y hy
    by_contra hne
    exact hy (subset_closure hne)
  · obtain ⟨hsub', -, hmc⟩ := hsub hne
    exact ⟨hsub', hmc⟩

end BookForm

end Polyfold
