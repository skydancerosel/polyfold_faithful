import GWMemoir.FilledSection
import Polyfold.Chapter3.TameGermTransfer
import Polyfold.Chapter3.UntamedBundle
import Polyfold.Chapter5.BumpFunctions

/-!
# Proposition 4.8 gives the sc-Fredholm germ (Definition 3.1.11)

HWZ, *Applications of Polyfold Theory I* (Memoirs AMS 248, no. 1179), §4.2, p. 104: Propositions
4.7 and 4.8 give the Fredholm property of the Cauchy–Riemann section (Theorem 1.11).  Read in a
strong bundle chart: the filled map `f` of the chart, the constant sc⁺-section `s = f(0)`, and the
conjugation of `f − s` near `0` to a basic germ are the data of the book's Definition 3.1.11
(2021 p. 96, `StrongBundle.IsScFredholmGerm2021`, with the 2021 filling of Definition 3.1.4).

* `isScFredholmGerm2021_of_prop_4_8`: in a strong bundle chart `c` centred at a smooth point
  `x₀`, a filling `g` of the principal part satisfying `Prop_4_8 c.U g` gives an sc-Fredholm germ
  at `x₀`.  `Prop_4_8` conjugates `g − g(0)` on `U ∩ V` only, for some open `V ∋ 0`, while
  Definition 3.1.11 asks for a conjugation on the `U` of the chart; the proof passes to the chart
  shrunk to `W = V ∩ O'` (`StrongBundleChart.shrink`), where `O'` is open with
  `U ∩ r⁻¹(V) = U ∩ O'`, so that `r(U ∩ W) ⊆ W`.  The constant `s = g(0)` is an sc⁺-section since
  `g(0)` is a smooth point (`g` is sc-smooth and `0` is smooth).
* `isScFredholmSection2021_of_prop_4_8`: sc-smooth, regularizing, and such chart data at every
  smooth point give an sc-Fredholm section (Definition 3.1.16 = 3.6.4).
* `prop_4_8_untamed`, `isScFredholmGerm2021_untamed_of_prop_4_8`: the hypotheses hold in the
  book's untamed corner example (`Polyfold.UntamedCorner`): there the chart, filling and
  `Prop_4_8` are all present, and the theorem applies.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace GWMemoir

open Polyfold Polyfold.StrongRetr Polyfold.StrongBundle

universe u v

variable {E F : ScBanach}

/-- An sc-smooth map sends the smooth point `0 ∈ U` to a smooth point. -/
theorem mem_smooth_of_isScSmooth {U : Set (E 0)} {g : E 0 → F 0} (hg : IsScSmooth U g)
    (h0 : (0 : E 0) ∈ U) : g 0 ∈ F.smooth := by
  refine F.mem_smooth_iff.2 fun m => ?_
  have h0m : (0 : E m) ∈ E.lvlSet U m := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have := (hg 0).mem_range m 0 h0m
  rw [map_zero] at this
  obtain ⟨y, hy⟩ := this
  exact ⟨y, hy⟩

/-- A point of `F₁` over a smooth point of `F₀` is a smooth point of the shift `F¹`. -/
theorem mem_shift_smooth {y : F 1} (hy : F.toBase 1 y ∈ F.smooth) : y ∈ F.shift.smooth := by
  refine (F.shift).mem_smooth_iff.2 fun m => ?_
  obtain ⟨z, hz⟩ := F.mem_smooth_iff.1 hy (m + 1)
  refine ⟨z, F.toBase_injective 1 ?_⟩
  rw [← ScBanach.shiftScale_toBase, hz]

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **Memoir Proposition 4.8 gives an sc-Fredholm germ** (memoir §4.2, p. 104, the Fredholm
property of Theorem 1.11; book Definition 3.1.11 = 3.6.3, 2021 pp. 96, 135, with the 2021
filling; the memoir's Definition 2.44, p. 42, in the book's order):
in a strong bundle chart `c` centred at a smooth point `x₀`, a filling `g` of the principal part
of `f` for which `Prop_4_8 c.U g` holds (sc-smooth, and `g − g(0)` conjugated near `0` to a basic
germ) gives `IsScFredholmGerm2021 f x₀`, in the chart shrunk to a neighbourhood of `0` on which
the conjugation is defined, with the constant sc⁺-section `s = g(0)`. -/
theorem isScFredholmGerm2021_of_prop_4_8 {c : StrongBundleChart PX P} (hc : B.IsChart c)
    {x₀ : X} (hxs : x₀ ∈ PX.smoothSet) (hxV : x₀ ∈ c.φ.source) (hφ0 : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) {g : c.φ.model.E 0 → c.F 0}
    (hfill : IsFilling2021 c.relOpen c.isRetraction h0 (c.principal f) g)
    (h48 : Prop_4_8 c.U g) : B.IsScFredholmGerm2021 f x₀ := by
  obtain ⟨hgs, V, hVo, h0V, hconj⟩ := h48
  -- the open set `W = V ∩ O'` with `U ∩ r⁻¹(V) = U ∩ O'`
  have hrcont : ContinuousOn (r c.R) c.U :=
    (c.isRetraction.baseRetraction c.relOpen).isSc1.isSc0.continuousOn_base
  obtain ⟨O', hO'o, hO'⟩ := (continuousOn_iff'.1 hrcont) V hVo
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := zero_mem_O_of_chart hxV hφ0
  have hr0 : r c.R 0 = 0 := r_eq_self c.isRetraction h0O
  set W : Set (c.φ.model.E 0) := V ∩ O' with hWdef
  have hW : IsOpen W := hVo.inter hO'o
  have hmaps : MapsTo (r c.R) (c.U ∩ W) W := by
    rintro y ⟨hyU, hyV, hyO'⟩
    have hry : r c.R y ∈ V := by
      have : y ∈ r c.R ⁻¹' V ∩ c.U := by rw [hO']; exact ⟨hyO', hyU⟩
      exact this.1
    have hrU : r c.R y ∈ c.U := r_mem c.isRetraction hyU
    refine ⟨hry, ?_⟩
    have : r c.R y ∈ r c.R ⁻¹' V ∩ c.U := ⟨by
      change r c.R (r c.R y) ∈ V
      rw [r_r c.isRetraction hyU]; exact hry, hrU⟩
    rw [hO'] at this
    exact this.1
  have h0W : (0 : c.φ.model.E 0) ∈ W := by
    refine ⟨h0V, ?_⟩
    have : (0 : c.φ.model.E 0) ∈ r c.R ⁻¹' V ∩ c.U := ⟨by
      change r c.R 0 ∈ V
      rw [hr0]; exact h0V, h0⟩
    rw [hO'] at this
    exact this.1
  -- the shrunk chart
  set c' := c.shrink hW hmaps
  have h0' : (0 : c'.φ.model.E 0) ∈ c'.U := ⟨h0, h0W⟩
  have hsub : c'.U ⊆ c.U := inter_subset_left
  have hxV' : x₀ ∈ c'.φ.source := ⟨hxV, by
    change c.φ x₀ ∈ W
    rw [hφ0]; exact h0W⟩
  -- the constant sc⁺-section `s = g(0)`
  obtain ⟨y, hy⟩ := c.F.mem_smooth_iff.1 (mem_smooth_of_isScSmooth hgs h0) 1
  have hys : y ∈ c.F.shift.smooth := mem_shift_smooth (hy ▸ mem_smooth_of_isScSmooth hgs h0)
  have hsm1 : IsScSmooth (E := c'.φ.model.E) (F := c.F.shift) c'.U (fun _ => y) :=
    isScSmooth_const_of_mem_smooth c'.relOpen.isScDomain hys
  have hplus : IsScPlusGerm (F := c.F) c'.φ.model.C c'.U (fun _ => y) :=
    ⟨ScNbhdGerm.ofSet c'.relOpen.relOpen h0', fun _ hu => hu,
      hsm1.isScSmoothGerm c'.isQuadrantLike c'.relOpen.relOpen h0'⟩
  -- the conjugation on `U ∩ W ⊆ U ∩ V`
  have hUV : IsRelOpenInQuadrant c.φ.model.E c.φ.model.C (c.U ∩ V) := c.relOpen.inter_isOpen hVo
  have hconj' : IsConjugateToBasicGerm c'.U (fun u => g u - c.F.toBase 1 y) :=
    (hconj.of_subset hUV ⟨h0, h0V⟩ c'.relOpen
      (fun _ hu => ⟨hu.1, hu.2.1⟩) h0').congr fun u _ => by rw [hy]
  refine ⟨hxs, c', hc.shrink hW hmaps, hxV', hφ0, h0', g, fun _ => y, ?_, hplus, hy, hconj'⟩
  exact (hfill.isFillingGerm.of_subset c.relOpen c.isRetraction c'.relOpen c'.isRetraction hsub
    h0 h0').isFilling2021 (zero_mem_O_of_chart hxV' hφ0)

/-- **The Fredholm property of Memoir Theorem 1.11 from Proposition 4.8, chart by chart**
(memoir Definition 2.45, p. 42; book Definition 3.1.16 = 3.6.4, 2021 pp. 97, 135): an sc-smooth,
regularizing section with, at every smooth point, a centred strong bundle chart and a filling
satisfying Proposition 4.8, is an sc-Fredholm section. -/
theorem isScFredholmSection2021_of_prop_4_8 (hsm : B.IsScSmoothSection f)
    (hreg : ∀ m, ∀ x ∈ PX.levelSet m, f x ∈ B.doubleLevel m (m + 1) → x ∈ PX.levelSet (m + 1))
    (h : ∀ x₀ ∈ PX.smoothSet, ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c)
      (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0) (h0 : (0 : c.φ.model.E 0) ∈ c.U)
      (g : c.φ.model.E 0 → c.F 0),
      IsFilling2021 c.relOpen c.isRetraction h0 (c.principal f) g ∧ Prop_4_8 c.U g) :
    B.IsScFredholmSection2021 f where
  isScSmooth := hsm
  regularizing := hreg
  germ x hx := by
    obtain ⟨c, hc, hxV, hφ0, h0, g, hfill, h48⟩ := h x hx
    exact isScFredholmGerm2021_of_prop_4_8 hc hx hxV hφ0 h0 hfill h48

/-- **Propositions 4.7, 4.23 and 4.25 in a chart give the sc-Fredholm germ**: the composite of
`memoir_proposition_4_8_of_4_23` (through Proposition 4.26 = Theorem 3.7.1, for an open `U`, as
in the Gromov–Witten charts) and `isScFredholmGerm2021_of_prop_4_8`. -/
theorem isScFredholmGerm2021_of_prop_4_23 {c : StrongBundleChart PX P} (hc : B.IsChart c)
    {x₀ : X} (hxs : x₀ ∈ PX.smoothSet) (hxV : x₀ ∈ c.φ.source) (hφ0 : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (hUo : IsOpen c.U) {g : c.φ.model.E 0 → c.F 0}
    (hfill : IsFilling2021 c.relOpen c.isRetraction h0 (c.principal f) g)
    {A H : Submodule ℝ (c.φ.model.E 0)} (h47 : Prop_4_7 c.U g)
    (h423 : Prop_4_23 c.U g A H h47.1) (h425 : Prop_4_25 c.U g A H)
    (hAH : c.φ.model.E.IsScSplitting A H) [FiniteDimensional ℝ A]
    {B' X' : Submodule ℝ (c.φ.model.E 0)} (hBX : c.φ.model.E.IsScSplitting B' X')
    [FiniteDimensional ℝ B'] (hAB : A ≤ B') (hXH : X' ≤ H)
    (hker : LinearMap.ker (scDeriv c.U g 0 : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ≤ B') :
    B.IsScFredholmGerm2021 f x₀ :=
  isScFredholmGerm2021_of_prop_4_8 hc hxs hxV hφ0 h0 hfill
    (memoir_proposition_4_8_of_4_23 hUo h0 h47 h423 h425 hAH hBX hAB hXH hker)

end Bundle

/-! ### Witness: the untamed corner example of the book -/

section Witness

open Polyfold.UntamedCorner

/-- `Prop_4_8` holds for the filling `g` of the untamed corner example (`g` is a basic germ and
`g(0) = 0`; `V = E`). -/
theorem prop_4_8_untamed : Prop_4_8 chart0.U g :=
  ⟨isScSmooth_g, univ, isOpen_univ, mem_univ _, by
    rw [inter_univ]
    exact isConjugateToBasicGerm_g.congr fun u _ => by
      change g u = g u - g 0
      rw [g_zero, sub_zero]⟩

/-- **The hypotheses of `isScFredholmGerm2021_of_prop_4_8` hold together** in the untamed corner
example (chart `chart0`, smooth point `x0`, filling `g`). -/
theorem isScFredholmGerm2021_untamed_of_prop_4_8 : bundle.IsScFredholmGerm2021 sec x0 :=
  isScFredholmGerm2021_of_prop_4_8 isChart_chart0 (by rw [smoothSet_polyO]; exact mem_univ _)
    (mem_univ _) rfl zero_mem_U isFilling2021_sec_zero prop_4_8_untamed

end Witness

end GWMemoir
