import Polyfold.Chapter3.SectionCompactnessG
import Polyfold.Chapter3.TameGermsG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and §3.6:
**the Chapter 3 interface used by Chapter 5, in the text's germ reading of Definition 3.11**
(phase 2).  Corollary 3.13 for sc-Fredholm sections, and the germ invariance of Definition 3.53 in
a tame chart, for the germ notions (`IsScFredholmSection`, `IsGoodPositionGermTame`).

# The Chapter 5 interface, germ reading

## The text, paraphrased

(Corollary 3.13) If `f(x_k) = 0` and `x_k → x` in `X`, then `x_k → x` in every level `X_m`.
(Definition 3.53) Good position is a property of the germ `(f, x)`.  Chapter 5 uses both (Theorem
5.7: the solution set is compact on every level; Theorem 5.19: good position of a section that
agrees with `f` near `x`).

## What is formalized

* `Polyfold.corollary_3_13_section`: the germ form of `corollary_3_13_section_wholeChart`
  (`SectionCompactness.lean`), with the hypothesis `IsScFredholmSection` and the same
  conclusion; it uses Corollary 3.13 at the base point in the germ reading (`corollary_3_13`).
* `Polyfold.StrongBundle.IsGoodPositionGermTame.congr_nhds`: the germ form of the Chapter 5
  lemma `StrongBundle.IsGoodPositionGermTameWholeChart.congr_nhds` (`Chapter5/GeneralPosition.lean`): if
  `f = f'` near `x₀`, good position of `(f, x₀)` in a tame chart (germ reading) gives that of
  `(f', x₀)`, with the same chart, filling germ, sc⁺-germ and derivative family.

## What the text leaves implicit, and the choices made

* These are the two places where the Chapter 5 interface needs a germ statement that is not yet
  in the Chapter 3 germ files (Findings, Chapter 3, items 320–329; the coverage table of the
  phase 2 notes).  The second one is a Chapter 5 lemma: in the switch of Definition 3.11 to the
  germ reading (stage 2) the Chapter 5 copy is replaced by this one, whose proof only touches
  the condition "the filling agrees with the principal part near `0`" (`IsFillingGerm.eq_on`).
* A zero of a regularizing section is a smooth point; the germ form of that lemma
  (`IsScFredholmSection.mem_smoothSet_of_isZeroAt`) lives in `TameGermsG.lean` (moved there at
  the switch of Definition 3.11 to the germ reading, so that Chapter 5 reaches it).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **Corollary 3.13 for sc-Fredholm sections, germ reading** (phase 2; the germ form of
`corollary_3_13_section_wholeChart`, Definition 3.14 with the germ reading `IsScFredholmSection` of
Definition 3.11): if `f(x_k) = 0` and `x_k → x₀` in `X`, then `x₀` is a zero of `f`, a smooth
point, and for every `m` there are lifts `y_k ∈ X_m` of the `x_k` (for `k` large) converging in
`X_m` to the lift of `x₀`. -/
theorem corollary_3_13_section (hf : B.IsScFredholmSection f) {x : ℕ → X}
    (hx : ∀ n, IsZeroAt P f (x n)) {x₀ : X} (hlim : Tendsto x atTop (𝓝 x₀)) (m : ℕ) :
    IsZeroAt P f x₀ ∧ x₀ ∈ PX.smoothSet ∧
      ∃ y₀ : PX.Level m, PX.levelVal m y₀ = x₀ ∧ ∃ y : ℕ → PX.Level m,
        (∀ᶠ n in atTop, PX.levelVal m (y n) = x n) ∧ Tendsto y atTop (𝓝 y₀) := by
  have hx₀ : IsZeroAt P f x₀ := hf.isScSmooth.isZeroAt_of_tendsto hx hlim
  -- a zero of a regularizing section is a smooth point
  have hxs : x₀ ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx₀
  exact ⟨hx₀, hxs, corollary_3_13 hf.isScSmooth.1 (hf.germ x₀ hxs) hx₀ hx hlim m⟩

/-- **Good position is a property of the germ, germ reading** (Definition 3.53 in a tame chart;
phase 2, the germ form of the Chapter 5 lemma `StrongBundle.IsGoodPositionGermTameWholeChart.congr_nhds`):
if `f = f'` on an open `W ∋ x₀`, good position of `(f, x₀)` in a tame chart in the germ reading
(`IsGoodPositionGermTame`) gives that of `(f', x₀)`, in the same chart with the same filling germ,
sc⁺-germ and derivative family; only the condition "the filling agrees with the principal part on
`O` near `0`" involves the section. -/
theorem StrongBundle.IsGoodPositionGermTame.congr_nhds {f f' : X → Y} {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) {W : Set X} (hW : IsOpen W) (hx₀W : x₀ ∈ W)
    (hff' : ∀ y ∈ W, f y = f' y) : B.IsGoodPositionGermTame f' x₀ := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩ := hg
  obtain ⟨G, hGo, hG⟩ := c.φ.exists_isOpen_image_eq (s := W ∩ c.φ.source) inter_subset_right
    (hW.inter c.φ.isOpen_source)
  have h0G : (0 : c.φ.model.E 0) ∈ G := by
    have : c.φ x₀ ∈ c.φ '' (W ∩ c.φ.source) := ⟨x₀, ⟨hx₀W, hxV⟩, rfl⟩
    rw [hG, hφ0] at this; exact this.2
  refine ⟨hs, c, hc, hxV, hφ0, h0, g, s, ⟨?_, hfill.mem_of_fixed, hfill.germ⟩, hsm, hs0, hconj,
    hgp⟩
  filter_upwards [hfill.eq_on, hGo.mem_nhds h0G] with u hu huG huO
  rw [← hu huO]
  have huO' : u ∈ c.φ.model.O := c.r_image ▸ huO
  obtain ⟨y, hy, rfl⟩ : u ∈ c.φ '' (W ∩ c.φ.source) := by rw [hG]; exact ⟨huO', huG⟩
  unfold StrongBundleChart.principal
  rw [c.φ.symm_apply_apply hy.2, hff' y hy.1]

end Bundle

end Polyfold
