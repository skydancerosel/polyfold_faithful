import Polyfold.Chapter5.Corollary58

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Corollary 5.2.5**
(p. 213) with **Definition 2.5.2** (tame sc-retractions, p. 53), **Definition 2.5.7** (tame
M-polyfolds, p. 57) and **Definition 3.6.4** (sc-Fredholm sections, p. 135; the 2021 text drops
"tame" from the definition, and the project's tame germ data `IsScFredholmSectionTame` are the
preprint's Definition 3.51) *(2017: Corollary 5.1, Definitions 2.17, 2.19, 3.15; preprint 2014:
Corollary 5.8, Definitions 2.34, 2.37, 3.51)*: **the index raise
of a tame chart is tame, and Corollary 5.2.5 holds with tame germ data** (research file; settles
Findings, Chapter 5, item 145, whose chart half Chapter 7 had settled for M-polyfold tameness
only).

# Tameness under the index raise, and Corollary 5.2.5 with tame germ data

## The question (Findings, Chapter 5, item 145)

Corollary 5.2.5 (`corollary_5_8`, `Corollary58.lean`) is formalized without tameness: for an
sc-Fredholm section `f` of `P : Y → X`, `f¹` is an sc-Fredholm section of `P¹ : Y¹ → X¹`.  The
text's standing hypothesis is a tame `X`, and the sections of Chapter 6 carry tame germ data
(`IsScFredholmSectionTame`, preprint Definition 3.51; 2021 Definition 3.6.4 without "tame").
Item 145 recorded the obstruction to shifting tameness: `ScRetraction.IsTame` quantifies over
*all* presentations `T¹ : E¹ ≅ ℝⁿ ⊕ W'` of the partial quadrant `C¹ ⊆ E¹`, and these are not all
index raises of presentations of `C`.

## The answer: yes, with Part I's own tools

The obstruction dissolves through **presentation independence** (Definition 2.5.2 does not depend
on the presentation, `ScRetraction.IsTameWith.isTame`, `TameFaces.lean`): it suffices to verify
tameness of `r¹` for the *one* presentation `T¹ = T.shiftPres` (the sc-isomorphism `T.shift`) of
`C¹`, which has the same `ℝⁿ`-coordinates as `T`.  Then

1. `d_{C¹}(y) = d_C(y)` for `y ∈ C¹` (`degIndex_shift`), so condition (1), `d(r¹ y) = d(y)`, is
   condition (1) for `r`;
2. the minimal subspace `E_y` of `T¹` is `E_y ∩ E₁` (`mem_minimalSubspaceWith_shift`);
3. `Dr¹(y) = Dr(y)|_{E₁}` (Proposition 1.2.2, `IsSc1With.shift`), whose range is `T_yO ∩ E₁`
   because `Dr(y)` is a projection (`scDeriv_comp_self`); and an sc-complement `A ⊆ E_y` of
   `T_yO` gives the sc-complement `A ∩ E₁ ⊆ E_y ∩ E₁` of `T_yO¹` (the sc-splitting shifts,
   `isScSplitting_levelSub_one`).

This is the argument of Chapter 7 (`Polyfold/Chapter7/Lift.lean`, private lemmas for
`MPolyfold.IsTame.levelOne`), repeated here in Part I with public names, so that it can be applied
to the base retraction of a strong bundle chart:

* `ScRetraction.IsTameWith.shift`, **`ScRetraction.IsTame.shift`** (the index raise of a tame
  sc-smooth retraction is tame), `IsTameRetract.shift` (`(O¹, C¹, E¹)` is a tame retract when
  `(O, C, E)` is), `MPolyfold.IsTame.shift` (a tame M-polyfold has tame `X¹`; Chapter 7's
  `MPolyfold.IsTame.levelOne`, reproved from the public lemmas);
* `IsStrongBundleRetraction.baseRetraction_shift_eqOn`, **`baseRetraction_shift_isTame`**: the
  base retraction of the index raise `R¹ = strongShift R` of a strong bundle retraction agrees on
  `U¹` with the index raise `r¹` of its base retraction `r` (`ι ∘ base R¹ = r ∘ ι`), so it is tame
  when `r` is (tameness depends only on the values on `U`, `ScRetraction.IsTame.congr`);
* **`StrongBundle.IsTameChart.shift`**: **the index raise `Φ¹` of a tame strong bundle chart is a
  tame strong bundle chart of `P¹`**;
* **`isScFredholmGermTame_sectionShift`**: tame germ data `(Φ, g, s)` of `f` at a smooth point
  give tame germ data `(Φ¹, g¹, s¹)` of `f¹` (the datum of `isScFredholmGerm_sectionShift`,
  `Corollary58.lean`, in the chart `Φ¹`, now known to be tame);
* **`corollary_5_2_5_tame`**: **Corollary 5.2.5 with tame germ data**: if `f` is an sc-Fredholm
  section of `P` with tame germ data (preprint Definition 3.51) and compact solution set, then
  `f¹` is an sc-Fredholm section of `P¹` with tame germ data and compact solution set;
  `corollary_5_2_5_tame_two` iterates to `f²`.

## What the text leaves implicit, and the choices made

* The text's "`f^i` is an sc-Fredholm section of `P^i`" is "a priori clear"; the tame version is
  not stated separately (the 2021 Definition 3.6.4 no longer carries "tame", which the text has
  as the standing hypothesis on `X`).  Here the tame chart of the germ datum is shifted
  explicitly.
* Nothing in `Corollary58.lean` or `StrongBundleShift.lean` is changed; the private Chapter 7
  lemmas are repeated (not imported: Chapter 7 is Part II, and `Lift.lean` would import the
  ep-groupoid theory into Chapter 5).

## What is left

Nothing of item 145: the chart half and the section half are both proved.  The remark of
`StrongBundleShift.lean` ("Tameness is not shifted … Not done") is superseded by this file.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

/-! ### The index raise of a tame sc-smooth retraction is tame (Definition 2.5.2) -/

section TameShift

variable {E : ScBanach}

/-- `(A ∩ E₁)_m = A ∩ E_{m+1}`: the filtration of `A ∩ E₁` in `E¹`. -/
theorem ScBanach.levelSub_shift_levelSub (A : Submodule ℝ (E 0)) (m : ℕ) :
    E.shift.levelSub (E.levelSub A 1) m = E.levelSub A (m + 1) := by
  ext v
  change E.toBase 1 (E.shift.toBase m v) ∈ A ↔ E.toBase (m + 1) v ∈ A
  rw [E.shift_toBase m v]

/-- An sc-subspace `A ⊆ E` gives the sc-subspace `A ∩ E₁ ⊆ E¹`. -/
theorem ScBanach.IsScSubspace.levelSub_one {A : Submodule ℝ (E 0)} (h : E.IsScSubspace A) :
    E.shift.IsScSubspace (E.levelSub A 1) := by
  refine ⟨E.isClosed_levelSub h.1 1, fun m => ?_⟩
  rw [ScBanach.levelSub_shift_levelSub, E.shift_smoothLvl]
  exact h.2 (m + 1)

/-- **The sc-splitting shifts**: `E = F ⊕ G` gives `E¹ = F¹ ⊕ G¹`. -/
theorem ScBanach.IsScSplitting.levelSub_one {F G : Submodule ℝ (E 0)}
    (h : E.IsScSplitting F G) :
    E.shift.IsScSplitting (E.levelSub F 1) (E.levelSub G 1) :=
  ⟨h.1.levelSub_one, h.2.1.levelSub_one, fun m => by
    rw [ScBanach.levelSub_shift_levelSub, ScBanach.levelSub_shift_levelSub]
    exact h.2.2 (m + 1)⟩

variable {n : ℕ} {W : ScBanach}

/-- **The shifted presentation** `T¹ : E¹ ≅ ℝⁿ ⊕ W¹` of `C¹` (the sc-isomorphism `T.shift`, whose
target `(ℝⁿ ⊕ W)¹` is `ℝⁿ ⊕ W¹` by definition of the shifted structures). -/
def ScIso.shiftPres (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    ScIso E.shift ((ScBanach.const (Fin n → ℝ)).prod W.shift) :=
  T.shift

/-- The `ℝⁿ`-coordinates of the shifted presentation `T¹ = T.shiftPres` are those of `T`. -/
theorem ScIso.shiftPres_apply_fst (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (w : E 1) :
    (T.shiftPres 0 w).1 = (T 0 (E.toBase 1 w)).1 := by
  rw [← T.toBase_comm, ScBanach.prod_toBase, ScBanach.const_toBase]
  rfl

/-- `T¹` presents `C¹`: `C¹ = (T¹)⁻¹([0, ∞)ⁿ ⊕ W¹)`. -/
theorem ScIso.shiftPres_presentation {C : Set (E 0)}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0) :
    E.lvlSet C 1 = T.shiftPres 0 ⁻¹' quadrant n W.shift 0 := by
  rw [hT, IsPartialQuadrant.lvlSet_eq T 1]
  rfl

/-- `d_{C¹}(y) = d_C(y)` for `y ∈ C¹`. -/
theorem degIndex_shift {C : Set (E 0)}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    {y : E 1} (hy : y ∈ E.lvlSet C 1) :
    degIndex E.shift (E.lvlSet C 1) y = degIndex E C (E.toBase 1 y) := by
  rw [degIndex_eq T.shiftPres (ScIso.shiftPres_presentation hT) hy,
    degIndex_eq T hT (x := E.toBase 1 y) hy, degIndexWith,
    degIndexWith, quadrantDeg, quadrantDeg, ScIso.shiftPres_apply_fst]

/-- `E_y` for `T¹` at `y ∈ E₁` is `E_y ∩ E₁` for `T`. -/
theorem mem_minimalSubspaceWith_shift
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {y v : E 1} :
    v ∈ minimalSubspaceWith T.shiftPres y ↔
      E.toBase 1 v ∈ minimalSubspaceWith T (E.toBase 1 y) := by
  rw [mem_minimalSubspaceWith, mem_minimalSubspaceWith, ScIso.shiftPres_apply_fst,
    ScIso.shiftPres_apply_fst]

/-- **The index raise of a tame retraction is tame with respect to `T¹`**: (1) `d_{C¹} = d_C` on
`C¹`; (2) `A ∩ E₁` is an sc-complement of `T_yO¹ = T_yO ∩ E₁` inside `E_y ∩ E₁`
(`Dr¹(y) = Dr(y)|_{E₁}`, Proposition 1.2.2). -/
theorem ScRetraction.IsTameWith.shift {C : Set (E 0)} {R : ScRetraction E C}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    (h : R.IsTameWith T) : R.shift.IsTameWith T.shiftPres := by
  refine ⟨fun x hx => ?_, fun x hx hs => ?_⟩
  · have hxC : x ∈ E.lvlSet C 1 := R.shift.U_subset_C hx
    have hrxC : R.shift x ∈ E.lvlSet C 1 := R.shift.U_subset_C (R.shift.mapsTo hx)
    rw [degIndex_shift hT hxC, degIndex_shift hT hrxC, ScRetraction.shift_apply,
      R.isSc1.isSc0.toBase_levelMap hx]
    exact h.degIndex_apply _ hx
  · have hy2 : E.toBase 1 (E.shift.toBase 1 x) = E.toBase 2 x := (E.shift_toBase 1 x).symm
    have hyO : E.shift.toBase 1 x ∈ E.lvlSet R.retract 1 := by
      have : E.shift.toBase 1 x ∈ R.shift.retract := hx
      rwa [R.shift_retract] at this
    have hys : E.shift.toBase 1 x ∈ E.smoothLvl 1 := by
      have : x ∈ E.smoothLvl 2 := by
        rw [← E.shift_smoothLvl 1]
        exact hs
      change E.toBase 1 (E.shift.toBase 1 x) ∈ E.smooth
      rw [hy2]
      exact this
    obtain ⟨A, hA, hAE⟩ := h.exists_complement _ hyO hys
    -- `Dr¹(x) = Dr(x)|E₁` (Proposition 1.2.2)
    have hD := R.isSc1.isSc1With_scDeriv
    have hxU : x ∈ E.shift.lvlSet R.shift.U 1 := R.shift.lvlSet_retract_subset 1 hx
    have heq : scDeriv R.shift.U R.shift x = levelDeriv (scDeriv R.U R) 1 x :=
      IsSc1.scDeriv_eqOn (hD.shift R.isScDomain) (R.isScDomain.shift.uniqueDiffWithinAt 1) hxU
    have hxU2 : x ∈ E.lvlSet R.U 2 := by
      change E.toBase 2 x ∈ R.U
      rw [← hy2]
      exact hxU
    have hbase : ∀ v : E 1, E.toBase 1 (scDeriv R.shift.U R.shift x v) =
        scDeriv R.U R (E.shift.toBase 1 x) (E.toBase 1 v) := fun v => by
      rw [heq]
      exact hD.toBase_levelDeriv hxU2 v
    -- `T_xO¹ = T_xO ∩ E₁`, since `Dr(x)` is a projection
    have hrange : LinearMap.range (scDeriv R.shift.U R.shift x : E 1 →ₗ[ℝ] E 1) =
        E.levelSub (LinearMap.range (scDeriv R.U R (E.shift.toBase 1 x) : E 0 →ₗ[ℝ] E 0))
          1 := by
      ext v
      rw [ScBanach.mem_levelSub, LinearMap.mem_range, LinearMap.mem_range]
      simp only [ContinuousLinearMap.coe_coe]
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨E.toBase 1 w, (hbase w).symm⟩
      · rintro ⟨w, hw⟩
        refine ⟨v, E.toBase_injective 1 ?_⟩
        rw [hbase, ← hw]
        exact congrArg (fun L : E 0 →L[ℝ] E 0 => L w) (R.scDeriv_comp_self hyO)
    refine ⟨E.levelSub A 1, ?_, fun v hv => (mem_minimalSubspaceWith_shift T).2 (hAE hv)⟩
    rw [hrange]
    exact hA.levelSub_one

/-- **The index raise of a tame sc-smooth retraction is tame** (Definition 2.5.2 for `r¹`, with
respect to every presentation of `C¹`): tameness for the one presentation `T¹` suffices
(`ScRetraction.IsTameWith.isTame`).  This is the step Findings, Chapter 5, item 145 left open. -/
theorem ScRetraction.IsTame.shift {C : Set (E 0)} {R : ScRetraction E C} (h : R.IsTame) :
    R.shift.IsTame := by
  obtain ⟨n, W, T, hT⟩ := R.relOpen.isPartialQuadrant
  exact ((h n W T hT).shift hT).isTame (ScIso.shiftPres_presentation hT)

/-- **The index raise of a tame retract is tame**: `(O¹, C¹, E¹)` is a tame retract if
`(O, C, E)` is. -/
theorem IsTameRetract.shift {C O : Set (E 0)} (h : IsTameRetract E C O) :
    IsTameRetract E.shift (E.lvlSet C 1) (E.lvlSet O 1) := by
  obtain ⟨R, rfl, hR⟩ := h
  exact ⟨R.shift, R.shift_retract, hR.shift⟩

/-- **The index raise of a tame M-polyfold is tame** (Definition 2.5.7 for `X¹`): the level charts
of tame charts are tame.  (Chapter 7's `MPolyfold.IsTame.levelOne`, reproved from the public
lemmas of this file.) -/
theorem MPolyfold.IsTame.shift {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] {P : MPolyfold Z} (hP : P.IsTame) : P.shift.IsTame :=
  MPolyfold.isTame_of_forall_exists_chart P.shift fun x => by
    obtain ⟨φ, hφ, hx, ht⟩ := MPolyfold.IsTame.exists_chart P hP (P.levelVal 1 x)
    exact ⟨MPolyfold.levelChart hφ x, P.shift_isChart hφ x, hx, ht.shift⟩

end TameShift

/-! ### The base retraction of `R¹` is the index raise of the base retraction of `R` -/

section StrongBundleRetraction

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}
  (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
include hU hR

/-- **`base(R¹) = r¹` on `U¹`**: the base retraction of the index raise `R¹ = strongShift R` of a
strong bundle retraction agrees on `U¹ = U ∩ E₁` with the index raise of the base retraction `r`
of `R` (both lift `r`: `ι ∘ base R¹ = r ∘ ι = ι ∘ r¹`). -/
theorem IsStrongBundleRetraction.baseRetraction_shift_eqOn :
    EqOn (hR.baseRetraction hU).shift ((hR.shift hU).baseRetraction hU.shift)
      (hR.baseRetraction hU).shift.U := by
  intro u hu
  apply E.toBase_injective 1
  rw [ScRetraction.shift_apply, (hR.baseRetraction hU).isSc1.isSc0.toBase_levelMap hu]
  exact (hR.toIsStrongBundleMap.toBase_base_strongShift hu).symm

/-- **The base retraction of the index raise of a tame strong bundle retraction is tame**: it
agrees on `U¹` with the index raise `r¹` of the tame base retraction `r`
(`baseRetraction_shift_eqOn`), which is tame (`ScRetraction.IsTame.shift`), and tameness depends
only on the values on the domain (`ScRetraction.IsTame.congr`). -/
theorem IsStrongBundleRetraction.baseRetraction_shift_isTame
    (h : (hR.baseRetraction hU).IsTame) : ((hR.shift hU).baseRetraction hU.shift).IsTame :=
  h.shift.congr rfl (hR.baseRetraction_shift_eqOn hU)

end StrongBundleRetraction

/-! ### Tame strong bundle charts and tame germ data under the index raise -/

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The index raise of a tame strong bundle chart is a tame strong bundle chart of `P¹`**: `Φ¹`
is a chart of `P¹` (`StrongBundle.isChart_shift`), and its base retraction, the base retraction of
`R¹`, is tame (`IsStrongBundleRetraction.baseRetraction_shift_isTame`). -/
theorem StrongBundle.IsTameChart.shift {c : StrongBundleChart PX P} (hc : B.IsTameChart c)
    (y₀ : B.ShiftSpace) : B.shift.IsTameChart (c.shift hc.1 y₀) :=
  ⟨B.isChart_shift hc.1 y₀,
    IsStrongBundleRetraction.baseRetraction_shift_isTame c.relOpen c.isRetraction hc.2⟩

open StrongBundle StrongBundleChart in
/-- **`f¹` has tame germ data at every smooth point of `X¹`** (preprint Definition 3.51 for `f¹`
on `P¹`):
from tame germ data `(Φ, g, s)` of `f` at the point, the data `(Φ¹, g¹, s¹)` of
`isScFredholmGerm_sectionShift` (`Corollary58.lean`), in the index raise `Φ¹` of the tame chart
`Φ`, which is tame (`StrongBundle.IsTameChart.shift`). -/
theorem isScFredholmGermTame_sectionShift (hf : B.IsScSmoothSection f) {x : PX.Level 1}
    (hx : x ∈ PX.shift.smoothSet) (hg : B.IsScFredholmGermTame f (PX.levelVal 1 x)) :
    B.shift.IsScFredholmGermTame (B.sectionShift f) x := by
  obtain ⟨-, c, hct, hxV, h0, h0U, g, s, hfill, hsP, hs0, hconj⟩ := hg
  have hc : B.IsChart c := hct.1
  have h0O : (0 : c.φ.model.E 0) ∈ StrongRetr.r c.R '' c.U := by
    rw [c.r_image, ← h0]; exact c.φ.mapsTo_model _ hxV
  obtain ⟨Gs, hGsU, hs⟩ := id hsP
  obtain ⟨Gg, -, hgG, -⟩ := hfill.germ
  have hQ := c.isQuadrantLike
  have hg0 : IsSc0Germ Gg g := hgG 0
  have hs0' : IsSc0Germ (F := c.F.shift) Gs s := hs 0
  have hk : IsSc0Germ (Gg.inter Gs) (fun u => g u - c.F.toBase 1 (s u)) :=
    (hgG.sub_inter hQ (hs.operator_comp hQ c.F.shiftIncl)) 0
  set y₀ := B.shiftZero x
  have h01 : (0 : c.φ.model.E 1) ∈ (c.shift hc y₀).U := by
    change c.φ.model.E.toBase 1 0 ∈ c.U
    rw [map_zero]; exact h0U
  refine ⟨hx, c.shift hc y₀, hct.shift y₀, hxV, shift_φ_eq_zero hc y₀ hxV h0, h01,
    levelMap (E := c.φ.model.E) (F := c.F) g 1, levelMap (E := c.φ.model.E) (F := c.F.shift) s 1,
    shift_isFillingGerm (hc := hc) (y₀ := y₀) hf h0U h0O hfill hsP hs0 hconj h01,
    ⟨Gs.shift, fun u hu => hGsU (Gs.toBase_mem hu), fun k => (hs k).shift hQ⟩, ?_, ?_⟩
  · -- `s¹(0) = g¹(0)`
    apply c.F.toBase_injective 1
    change c.F.toBase 1 (c.F.shift.toBase 1 (levelMap (E := c.φ.model.E) (F := c.F.shift) s 1 0)) =
      c.F.toBase 1 (levelMap (E := c.φ.model.E) (F := c.F) g 1 0)
    rw [hs0'.toBase_levelMap (Gs.zero_mem 1), hg0.toBase_levelMap (Gg.zero_mem 1), map_zero, hs0]
  · -- `g¹ − s¹ = (g − s)¹` near `0`
    refine (hconj.shift_germ c.relOpen h0U hk).congr_nhds ?_
    filter_upwards [Gg.eventually_mem_one c.U_subset_C, Gs.eventually_mem_one c.U_subset_C]
      with u hug hus huU
    apply levelMap_eq_of_toBase_eq
    change c.F.toBase 1 (levelMap (E := c.φ.model.E) (F := c.F) g 1 u -
      c.F.shift.toBase 1 (levelMap (E := c.φ.model.E) (F := c.F.shift) s 1 u)) = _
    rw [map_sub, hg0.toBase_levelMap (hug huU), hs0'.toBase_levelMap (hus huU)]

open StrongBundle in
/-- **Corollary 5.2.5 for `i = 1` with tame germ data, the section part**: if `f` is an
sc-Fredholm section of `P : Y → X` with tame germ data (preprint Definition 3.51), then `f¹` is an
sc-Fredholm section of `P¹ : Y¹ → X¹` with tame germ data (`corollary_5_8_isScFredholmSection`
and `isScFredholmGermTame_sectionShift`). -/
theorem corollary_5_2_5_isScFredholmSectionTame (hf : B.IsScFredholmSectionTame f) :
    B.shift.IsScFredholmSectionTame (B.sectionShift f) :=
  { corollary_5_8_isScFredholmSection hf.toIsScFredholmSection with
    germTame := fun x hx => isScFredholmGermTame_sectionShift hf.isScSmooth hx
      (hf.germTame _ ((MPolyfold.mem_shift_smoothSet_iff x).1 hx)) }

open StrongBundle in
/-- **Corollary 5.2.5 for `i = 1` with tame germ data**: if `f` is an sc-Fredholm section of
`P : Y → X` with tame germ data and compact solution set, then `f¹` is an sc-Fredholm section of
`P¹ : Y¹ → X¹` with tame germ data and compact solution set.  (The form of Corollary 5.2.5 that
the tame theory of Chapter 6 can consume; Findings, Chapter 5, item 145.) -/
theorem corollary_5_2_5_tame (hf : B.IsScFredholmSectionTame f)
    (hS : IsCompact (solutionSet P f)) :
    B.shift.IsScFredholmSectionTame (B.sectionShift f) ∧
      IsCompact (solutionSet B.shiftProj (B.sectionShift f)) :=
  ⟨corollary_5_2_5_isScFredholmSectionTame hf,
    (corollary_5_8 hf.toIsScFredholmSection hS).2⟩

open StrongBundle in
/-- **Corollary 5.2.5 for `i = 2` with tame germ data, by iteration.** -/
theorem corollary_5_2_5_tame_two (hf : B.IsScFredholmSectionTame f)
    (hS : IsCompact (solutionSet P f)) :
    B.shift.shift.IsScFredholmSectionTame (B.shift.sectionShift (B.sectionShift f)) ∧
      IsCompact (solutionSet B.shift.shiftProj (B.shift.sectionShift (B.sectionShift f))) :=
  corollary_5_2_5_tame (corollary_5_2_5_tame hf hS).1 (corollary_5_2_5_tame hf hS).2

end Polyfold
