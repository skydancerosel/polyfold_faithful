import Polyfold.Chapter3.UntamedBundleFrame
import Polyfold.Chapter3.UntamedBundleTame
import Polyfold.Chapter3.GlobalIFTNearbyOntoG
import Polyfold.Chapter3.TameGermsAddG
import Polyfold.Chapter3.MainTheorems2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §3.6:
**Theorem 3.6.8** (p. 136; 2017: Theorem 3.13; preprint: Theorem 3.54), **Theorem 3.1.22** (p. 100)
and **Definitions 3.6.3, 3.6.4, 3.6.6** (pp. 135–136), read with the 2021 filling of
**Definitions 3.1.4/3.6.1** (pp. 91, 134), which asks only for an sc-smooth retraction.  Gap G.79.

# Theorem 3.6.8 with the 2021 (untamed) sc-Fredholm notion: the statement

## The text, paraphrased

(Theorem 3.6.8, p. 136) Let `f` be an sc-Fredholm section of a tame strong bundle `Y → X`.  If
`f(x) = 0` and the sc-Fredholm germ `(f, x)` is in good position, then `x` has an open
neighbourhood `V` such that (1) at every zero in `V` the germ is in good position, (2) the solution
set in `V` is a sub-M-polyfold whose induced structure is that of a manifold with boundary with
corners.  The proof (p. 137) takes the strong bundle chart of the germ data to cover a tame
retraction; Definition 3.6.3 with Definitions 3.1.4/3.6.1 does not ask for it (the 2017 text and
the preprint do).

## What is formalized

For the strong bundle `bundle : K → O` over the tame M-polyfold without boundary `O ≅ ℝ` and its
section `sec` (`UntamedBundle.lean`, `UntamedBundleFrame.lean`):

* `theorem_3_6_8_untamed_example`: `O` is tame and has `d_X ≡ 0`, and `K → O` has a tame strong
  bundle chart around every point; `sec` is an sc-Fredholm section
  in the sense of 2021 Definitions 3.1.16 = 3.6.4 (`IsScFredholmSection2021`); `sec(x₀) = 0`; the
  germ `(sec, x₀)` is in good position (Definition 3.6.6; the fibre over `x₀` is `0`); and the
  solution set has no tangent germ data at `x₀` and is not a sub-M-polyfold in any neighbourhood of
  `x₀`.
* `not_theorem_3_6_8_conclusion`: the conclusion of `theorem_3_6_8'` does not hold for
  `(bundle, sec, x₀)`.
* `theorem_3_6_8_untamed_not`: **the statement of `theorem_3_6_8'` with `IsScFredholmSection2021`
  and `IsGoodPositionGerm` (germ data in any compatible chart) in place of the tame hypotheses
  does not hold** — Theorem 3.6.8 read with the 2021 notion does not hold as we read it;
  `theorem_3_1_22_untamed_not`: the same for the conclusion "the solution set near `x₀` is a
  sub-M-polyfold" over an M-polyfold without boundary (Theorems 3.1.22, 3.1.26).  In both, "tame
  strong bundle" is the hypothesis `IsTameBundle`: `X` is tame and every point lies in a strong
  bundle chart of the structure with a tame base retraction.
* `not_isScFredholmGermTame_sec_zero`: **the 2021 sc-Fredholm germ `(sec, x₀)` has no tame germ
  data**; `isScFredholmGerm2021_not_tame`, `isScFredholmGerm2021_not_2017`: "every 2021
  sc-Fredholm germ has tame germ data (is a 2017 sc-Fredholm germ)" does not hold.

## What this says about the text

* The example meets the printed hypotheses of the 2021 notion: a strong bundle over a tame
  M-polyfold, with an atlas of tame strong bundle charts (`exists_isTameChart`); the chart of the
  germ data at `x₀` is a strong bundle chart of the structure in the sense of Definition 2.6.4
  (compatible with the tame charts), with a retraction which is not tame; an sc-smooth
  regularizing section with germ data
  (Definition 3.6.3) at every smooth point, a zero `x₀` with `d_X(x₀) = 0` at which `f'(x₀)` is
  onto (the fibre is `0`).  The conclusion (2) does not hold.  With germ data in a tame chart — the
  2017 and preprint wording, and the chart taken in the proof on p. 137 — the theorem is
  `theorem_3_6_8'`; so "tame" in the proof is a hypothesis on the germ data, not a consequence of
  the tameness of `X`.
* Good position is used in the form `StrongBundle.IsGoodPositionGerm` (in the chart of the germ
  data).  Any other reading of Definition 3.6.6 at `x₀` holds as well: `d_X(x₀) = 0` and the fibre
  `Y_{x₀}` is `0` (`subsingleton_fiber_zero`).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace UntamedCorner

open ScOneExample Jump StrongRetr

/-- `O` has no boundary. -/
theorem isWithoutBoundary_polyO : polyO.IsWithoutBoundary := degIndex_polyO

end UntamedCorner

/-- **A tame strong bundle** (the phrase of 2021 Definition 3.6.6 and Theorem 3.6.8, p. 136, read
with p. 66 and p. 136): the base `X` is a tame M-polyfold and every point of `X` lies in a strong
bundle chart of the structure whose base retraction is tame. -/
def StrongBundle.IsTameBundle {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (B : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∀ x : X, ∃ c : StrongBundleChart PX P, B.IsTameChart c ∧ x ∈ c.φ.source

namespace UntamedCorner

/-- **`K → O` is a tame strong bundle.** -/
theorem isTameBundle_bundle : bundle.IsTameBundle := ⟨isTame_polyO, exists_isTameChart⟩

/-- **The untamed example** (2021 Theorem 3.6.8, p. 136, with the 2021 definitions as printed).
For the strong bundle `K → O` over `O ≅ ℝ` and the section `sec`:

* `O` is a tame M-polyfold without boundary and `K → O` is a tame strong bundle (a tame strong
  bundle chart around every point);
* `sec` is an sc-Fredholm section in the sense of 2021 Definitions 3.1.16 = 3.6.4, with germ data
  in tame charts at every point other than `x₀`;
* `sec(x₀) = 0`, the germ `(sec, x₀)` is in good position, and the fibre over `x₀` is `0`;
* the solution set has no tangent germ data (Definition 3.2.1 (2)) at `x₀`, and for no open
  `W ∋ x₀` is `{y ∈ W | sec(y) = 0}` a sub-M-polyfold of `O`.

So conclusion (2) of Theorem 3.6.8 does not hold here. -/
theorem theorem_3_6_8_untamed_example :
    polyO.IsTame ∧ polyO.IsWithoutBoundary ∧ bundle.IsTameBundle ∧
    bundle.IsScFredholmSection2021 sec ∧
    (∀ x, x ≠ x0 → bundle.IsScFredholmGermTame sec x) ∧
    IsZeroAt kproj sec x0 ∧ bundle.IsGoodPositionGerm sec x0 ∧ Subsingleton (kproj ⁻¹' {x0}) ∧
    (∀ d, IsEmpty (polyO.TangentGermChart (solutionSet kproj sec) x0 d)) ∧
    ∀ W : Set Ob, IsOpen W → x0 ∈ W → ¬ polyO.IsSubMPolyfold {y ∈ W | IsZeroAt kproj sec y} :=
  ⟨isTame_polyO, isWithoutBoundary_polyO, isTameBundle_bundle, isScFredholmSection2021_sec,
    fun _ hx => isScFredholmGermTame_sec_of_ne hx, isZeroAt_sec_x0, isGoodPositionGerm_sec_zero,
    subsingleton_fiber_zero, isEmpty_tangentGermChart,
    fun _ hW h0 => not_isSubMPolyfold_zeroSet hW h0⟩

/-- **The conclusion of `theorem_3_6_8'` (2021 Theorem 3.6.8 (1), (2)) does not hold for
`(bundle, sec, x₀)`**, also with good position in any compatible chart in (1). -/
theorem not_theorem_3_6_8_conclusion :
    ¬ ∃ Vx : Set Ob, IsOpen Vx ∧ x0 ∈ Vx ∧
      (∀ y ∈ Vx, IsZeroAt kproj sec y → bundle.IsGoodPositionGerm sec y) ∧
      ∃ d : ℕ, ∃ D : polyO.TangentGermChart (solutionSet kproj sec) x0 d,
        D.IsRegular ∧ D.φ.source ⊆ Vx ∧
        ∀ y ∈ solutionSet kproj sec ∩ D.φ.source,
          ∀ (n' : ℕ) (_ : polyO.TangentGermChart (solutionSet kproj sec) y n'), n' = d := by
  rintro ⟨-, -, -, -, d, D, -⟩
  exact (isEmpty_tangentGermChart d).false D

/-- **2021 Theorem 3.6.8, p. 136, read with the 2021 sc-Fredholm notion, does not hold as we read
it**: the statement of `theorem_3_6_8'` with `IsScFredholmSection2021` (Definitions 3.1.16 = 3.6.4
with the filling of Definitions 3.1.4/3.6.1, no tameness of the chart of the germ data) in place of
`IsScFredholmSectionTame`, and good position in the chart of the germ data
(`IsGoodPositionGerm`) in place of `IsGoodPositionGermTame`, for a tame strong bundle
(`IsTameBundle`).  The counterexample is `(bundle, sec, x₀)`.  With germ data in tame charts the
statement is `theorem_3_6_8'`. -/
theorem theorem_3_6_8_untamed_not :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      (Y : Type) [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
      (f : X → Y) (x₀ : X), B.IsTameBundle → B.IsScFredholmSection2021 f →
      B.IsGoodPositionGerm f x₀ → IsZeroAt P f x₀ →
      ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧
        (∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGerm f y) ∧
        ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source ⊆ Vx ∧
          ∀ y ∈ solutionSet P f ∩ D.φ.source,
            ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := fun h =>
  not_theorem_3_6_8_conclusion (h Ob polyO Kt kproj bundle sec x0 isTameBundle_bundle
    isScFredholmSection2021_sec isGoodPositionGerm_sec_zero isZeroAt_sec_x0)

/-- **2021 Theorems 3.1.22 and 3.1.26 (pp. 100, 103), read with the 2021 sc-Fredholm notion, do
not hold as we read them**: for a tame strong bundle over an M-polyfold without boundary, an
sc-Fredholm section in the sense of 2021 Definitions 3.1.16 = 3.6.4 and a zero `x₀` in good
position (in the chart of the germ data), the solution set need not be a sub-M-polyfold in any
neighbourhood of `x₀`.  The
counterexample is `(bundle, sec, x₀)`.  With germ data in tame charts the statements are
`theorem_3_1_22'` and `theorem_3_1_26'`. -/
theorem theorem_3_1_22_untamed_not :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      (Y : Type) [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
      (f : X → Y) (x₀ : X), B.IsTameBundle → PX.IsWithoutBoundary → B.IsScFredholmSection2021 f →
      IsZeroAt P f x₀ → B.IsGoodPositionGerm f x₀ →
      ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y} := fun h => by
  obtain ⟨W, hW, h0, hsub⟩ := h Ob polyO Kt kproj bundle sec x0 isTameBundle_bundle
    isWithoutBoundary_polyO isScFredholmSection2021_sec isZeroAt_sec_x0 isGoodPositionGerm_sec_zero
  exact not_isSubMPolyfold_zeroSet hW h0 hsub

/-- **The 2021 sc-Fredholm germ `(sec, x₀)` has no tame germ data**: no strong bundle chart of
`bundle` with a tame base retraction carries germ data of `sec` at `x₀`.  (Otherwise `sec` would be
an sc-Fredholm section with tame germ data, in good position in a tame chart at `x₀`
(`IsGoodPositionGerm.toTame`), and `theorem_3_6_8'` would give tangent germ data of the solution
set at `x₀`.) -/
theorem not_isScFredholmGermTame_sec_zero : ¬ bundle.IsScFredholmGermTame sec x0 := fun htame => by
  have hf : bundle.IsScFredholmSectionTame sec :=
    { StrongBundle.isScFredholmSection2021_iff.1 isScFredholmSection2021_sec with
      germTame := fun x _ => by
        by_cases hx : x = x0
        · rw [hx]; exact htame
        · exact isScFredholmGermTame_sec_of_ne hx }
  have hg : bundle.IsGoodPositionGermTame sec x0 :=
    isGoodPositionGerm_sec_zero.toTame isScSmoothSection_sec htame isZeroAt_sec_x0
  obtain ⟨-, -, -, -, d, D, -⟩ := theorem_3_6_8' hf hg isZeroAt_sec_x0
  exact (isEmpty_tangentGermChart d).false D

/-- **"A 2021 sc-Fredholm germ has tame germ data" does not hold**: there are a tame strong
bundle, a section which is sc-Fredholm in the sense of 2021 Definitions 3.1.16 = 3.6.4,
and a point at which the germ (2021 Definition 3.6.3) has no germ data in a tame chart. -/
theorem isScFredholmGerm2021_not_tame :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      (Y : Type) [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
      (f : X → Y) (x₀ : X), B.IsTameBundle → B.IsScFredholmSection2021 f →
      B.IsScFredholmGerm2021 f x₀ → B.IsScFredholmGermTame f x₀ := fun h =>
  not_isScFredholmGermTame_sec_zero (h Ob polyO Kt kproj bundle sec x0 isTameBundle_bundle
    isScFredholmSection2021_sec isScFredholmGerm2021_sec_zero)

/-- **2021 ⟹ 2017 does not hold for sc-Fredholm germs** (2021 Definition 3.6.3 versus 2017
Definitions 3.7/3.14 with the tame filling): the germ `(sec, x₀)` is a 2021 sc-Fredholm germ and
not a 2017 one.  (The converse is `IsScFredholmGerm2017.isScFredholmGerm2021`.) -/
theorem isScFredholmGerm2021_not_2017 :
    bundle.IsScFredholmGerm2021 sec x0 ∧ ¬ bundle.IsScFredholmGerm2017 sec x0 :=
  ⟨isScFredholmGerm2021_sec_zero, fun h =>
    not_isScFredholmGermTame_sec_zero (StrongBundle.isScFredholmGerm2017_iff.1 h)⟩

end UntamedCorner

end Polyfold
