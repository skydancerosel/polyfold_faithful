import Polyfold.Chapter6.UntamedIndexJump

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6:
**Theorem 6.6.17** (p. 275) and the orientation space `O_f` (pp. 274–275), read with the 2021
sc-Fredholm notion of **Definitions 3.1.16 = 3.6.4** (pp. 96, 135), whose germ data need not sit in
a tame chart.

# Theorem 6.6.17 with the 2021 (untamed) sc-Fredholm notion: the statement

## The text, paraphrased

(Theorem 6.6.17) For an sc-Fredholm section `f` of a strong bundle over a tame M-polyfold, the set
`O_f` of the pairs `(x, o)`, `x ∈ X_∞` and `o` an orientation of `DET(f, x)`, has exactly one
Hausdorff topology such that (1) `π_f : O_f → X_∞` is a local homeomorphism, (2) every smooth
point has a neighbourhood with precisely two continuous sections, (3) along an sc-smooth path a
continuous section of the pull-back of `O_f` is, near every parameter, given by the local
propagation of Theorem 6.6.11.

## What is formalized

* `exists_isPropagationNbhd_of_isPropagationContinuous`: in general, if a topology on `O_f` has
  property (3) (`IsPropagationContinuous`) and `Or_x^f` is not empty, then `x` lies in a
  propagation neighbourhood (`IsPropagationNbhd`): take the constant path at `x` and a constant
  section of the pull-back.
* For the untamed example `(bundle, sec)` of `Chapter3/UntamedBundle.lean`, where no open set
  containing `x₀` is a propagation neighbourhood (`not_isPropagationNbhd_sec`):
  `not_isPropagationContinuous_sec` (**no topology on `O_sec` has property (3)**),
  `not_isOrientationTopology_sec` (no topology on `O_sec` has the properties of Theorem 6.6.17),
  `not_theorem_6_6_17_conclusion`.
* `theorem_6_6_17_untamed_not`: **the statement of `theorem_6_6_17` with `IsScFredholmSection2021`
  (2021 Definitions 3.1.16 = 3.6.4) in place of `IsScFredholmSectionTame` does not hold as we read
  it**; `theorem_6_6_17_untamed_not_exists`: already the existence of a topology with (3).

## What this says about the text

The example meets the printed hypotheses (`untamed_example_hypotheses`): a tame strong bundle over
a tame M-polyfold without boundary with sc-smooth bump functions, and an sc-Fredholm section in
the sense of 2021 Definitions 3.1.16 = 3.6.4.  Property (3) refers to the propagation of Theorem
6.6.11, which needs a vector bundle of stabilized kernels along a path; through `x₀` its rank
would be `ind(sec, ·) + k`, and the index is `1` for `t ≤ 0` and `0` for `t > 0`
(`isIndexAt_sec_iff`).  With germ data in tame charts the statement is `theorem_6_6_17`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

section General

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **Property (3) of Theorem 6.6.17 gives a propagation neighbourhood of every smooth point with
an orientation**: for the constant path at `x` and the constant section `t ↦ (t, (x, o))` of the
pull-back of `O_f`, property (3) at `t₀ = 0` asks for a propagation neighbourhood containing the
path. -/
theorem exists_isPropagationNbhd_of_isPropagationContinuous {hf : B.IsScFredholmSection f}
    {t : TopologicalSpace (OrSpace f hf)} (ht : IsPropagationContinuous f hf t) {x : X}
    (hs : x ∈ PX.smoothSet) (o : Orx f hf x hs) :
    ∃ U : Set X, IsPropagationNbhd f hf U ∧ x ∈ U := by
  let _ : TopologicalSpace (OrSpace f hf) := t
  let p : OrSpace f hf := ⟨PX.smoothMk x hs, o⟩
  let α : unitInterval → OrPullback f hf (fun _ => x) := fun s => ⟨(s, p), rfl⟩
  have hα : Continuous α := (continuous_id.prodMk continuous_const).subtype_mk _
  obtain ⟨U, hU, hseg, -⟩ := (ht (fun _ => x) (isScSmoothMap_const_of_mem_smoothSet hs) α hα
    (fun _ => rfl) 0).self_of_nhds
  exact ⟨U, hU, hseg 0 ⟨le_rfl, zero_le_one⟩⟩

end General

namespace UntamedCorner

/-- **No topology on `O_sec` has property (3) of Theorem 6.6.17**: property (3) at the constant
path at `x₀` asks for a propagation neighbourhood of `x₀`. -/
theorem not_isPropagationContinuous_sec :
    haveI := paracompactSpace_rn_prod polyO
    haveI := paracompactSpace_rn_pullback bundle
    ¬ ∃ t : TopologicalSpace (OrSpace sec isScFredholmSection_sec),
      IsPropagationContinuous sec isScFredholmSection_sec t := by
  have := paracompactSpace_rn_prod polyO
  have := paracompactSpace_rn_pullback bundle
  rintro ⟨t, ht⟩
  obtain ⟨o, -⟩ := exists_two_orx isScFredholmSection_sec (mem_smoothSet_polyO x0)
    hasScPlusSectionsThrough_bundle
  exact not_isPropagationNbhd_sec
    (exists_isPropagationNbhd_of_isPropagationContinuous ht (mem_smoothSet_polyO x0) o)

/-- **No topology on `O_sec` has the properties of Theorem 6.6.17.** -/
theorem not_isOrientationTopology_sec :
    haveI := paracompactSpace_rn_prod polyO
    haveI := paracompactSpace_rn_pullback bundle
    ¬ ∃ t : TopologicalSpace (OrSpace sec isScFredholmSection_sec),
      IsOrientationTopology sec isScFredholmSection_sec t := fun ⟨t, ht⟩ =>
  not_isPropagationContinuous_sec ⟨t, ht.propagation⟩

/-- **The conclusion of `theorem_6_6_17` (2021 Theorem 6.6.17) does not hold for
`(bundle, sec)`.** -/
theorem not_theorem_6_6_17_conclusion :
    haveI := paracompactSpace_rn_prod polyO
    haveI := paracompactSpace_rn_pullback bundle
    ¬ ∃! t : TopologicalSpace (OrSpace sec isScFredholmSection_sec),
      IsOrientationTopology sec isScFredholmSection_sec t := fun h =>
  not_isOrientationTopology_sec h.exists

/-- **The existence part of 2021 Theorem 6.6.17, read with the 2021 sc-Fredholm notion, does not
hold as we read it**: for a tame strong bundle over an M-polyfold with bump functions and an
sc-Fredholm section in the sense of 2021 Definitions 3.1.16 = 3.6.4, `O_f` need not carry a
topology with property (3).  The counterexample is `(bundle, sec)`. -/
theorem theorem_6_6_17_untamed_not_exists :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      (Y : Type) [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
      (f : X → Y), B.IsTameBundle → PX.AdmitsBumpFunctions →
      ∀ hf : B.IsScFredholmSection2021 f,
      haveI := paracompactSpace_rn_prod PX
      haveI := paracompactSpace_rn_pullback B
      ∃ t : TopologicalSpace (OrSpace f (StrongBundle.isScFredholmSection2021_iff.1 hf)),
        IsPropagationContinuous f (StrongBundle.isScFredholmSection2021_iff.1 hf) t := fun h =>
  not_isPropagationContinuous_sec (h Ob polyO Kt kproj bundle sec isTameBundle_bundle
    admitsBumpFunctions_polyO isScFredholmSection2021_sec)

/-- **2021 Theorem 6.6.17, p. 275, read with the 2021 sc-Fredholm notion, does not hold as we read
it**: the statement of `theorem_6_6_17` with `IsScFredholmSection2021` (Definitions
3.1.16 = 3.6.4, no tameness of the chart of the germ data) in place of `IsScFredholmSectionTame`,
for a tame strong bundle (`IsTameBundle`) over an M-polyfold with bump functions.  The
counterexample is `(bundle, sec)`: no topology on `O_sec` has property (3).  With germ data in
tame charts the statement is `theorem_6_6_17`. -/
theorem theorem_6_6_17_untamed_not :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      (Y : Type) [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
      (f : X → Y), B.IsTameBundle → PX.AdmitsBumpFunctions →
      ∀ hf : B.IsScFredholmSection2021 f,
      haveI := paracompactSpace_rn_prod PX
      haveI := paracompactSpace_rn_pullback B
      ∃! t : TopologicalSpace (OrSpace f (StrongBundle.isScFredholmSection2021_iff.1 hf)),
        IsOrientationTopology f (StrongBundle.isScFredholmSection2021_iff.1 hf) t := fun h =>
  not_theorem_6_6_17_conclusion (h Ob polyO Kt kproj bundle sec isTameBundle_bundle
    admitsBumpFunctions_polyO isScFredholmSection2021_sec)

end UntamedCorner

end Polyfold
