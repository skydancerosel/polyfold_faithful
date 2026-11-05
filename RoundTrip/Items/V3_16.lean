import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_16

/-! Round trip for V3_16 (Definition 3.14: sc-Fredholm sections).  Refreshed 2026-11-02 (HEAD,
germ reading).

Listed: the definitions `StrongBundle.IsScFredholmSection` (now the germ reading: the germ
condition is `IsScFredholmGerm` with `IsFillingGerm`, `IsScPlusGerm`) and
`StrongBundle.IsScFredholmSectionWholeChart` (the audit's whole-chart notion), and the theorems
`StrongBundle.IsScFredholmSection.mem_smoothSet_of_isZeroAt` ("a zero of a regularizing section is
a smooth point", now stated for the germ-reading notion) and
`StrongBundle.IsScFredholmSectionWholeChart.isScFredholmSection` (whole-chart ⇒ germ reading);
`A` is the conjunction of their types, universes instantiated at `0`.

B: for sections of a tame strong bundle, the project's `IsScFredholmSection` is the text's
`IsScFredholmSectionB`.  Clause by clause:
* (1) sc-smoothness: the same `StrongBundle.IsScSmoothSection`.
* (2) regularizing: the project's `Y_{m,m+1}` is `doubleLevel` ("in **every** chart of the atlas
  around `y`"), B's is `YlevelB` ("in **some** compatible chart").  They are equal
  (`doubleLevel_eq_YlevelB`, for `k ≤ m + 1`): one inclusion takes an atlas chart around `y`, the
  other is the chart independence of the double filtration, re-proved here for compatible
  (not only atlas) charts by the project's argument for `mem_doubleLevel_iff`.  So (2) agrees.
* (3) the germ condition at every smooth point: the project's `IsScFredholmGerm` vs the text's
  `IsScFredholmGermB`, i.e. exactly V3_13.  At HEAD (V3_13 refreshed) the filling and the
  sc⁺-section agree (germ reading on both sides); what remains is that the project admits any
  compatible chart where B asks a tame one (genuine; moving germ data to a tame chart is open), the
  `ℝⁿ`/`Pn` transport of the conjugation and B's `Ψ` on `U₀ ⊆ U` (glue).
`section_iff_of_germ_iff` proves B's equivalence for every section at which the two germ notions
agree at all smooth points, so the whole difference is V3_13's.

* `A → B`: not proved (the germ notions differ at the chart's tameness; `A` is unrelated to the
  definitional comparison).
* `B → A`: proved outright (the hypothesis is not used, and could not be: `A` is for arbitrary,
  possibly non-tame, bundles): a zero `f(x) = 0_x` lies in `Y_{m,m+1}` over `X_m`
  (`fiberZero_mem_doubleLevel`), so by regularizing and induction `x ∈ X_m` for all `m`; and the
  whole-chart germ data are germ data (`IsScFredholmGermWholeChart.isScFredholmGerm`).
-/

namespace RoundTrip.V3_16
open Polyfold Set Filter Topology Function

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.StrongBundle.IsScFredholmSection.mem_smoothSet_of_isZeroAt.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.IsScFredholmSectionWholeChart.isScFredholmSection.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundle.IsScFredholmSection.mem_smoothSet_of_isZeroAt.{0, 0},
    @Polyfold.StrongBundle.IsScFredholmSectionWholeChart.isScFredholmSection.{0, 0}⟩

section Bundle
set_option linter.unusedSectionVars false
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The double filtration is chart independent also for compatible charts (the project's proof of
`mem_doubleLevel_iff`, with the compatibility of `c` given by `IsChart`). -/
theorem mem_doubleLevel_of_isChart (Bd : StrongBundle PX P) {c : StrongBundleChart PX P}
    (hc : Bd.IsChart c) {y : Y} (hy : y ∈ c.toPartialEquiv.source) {m k : ℕ} (hk : k ≤ m + 1)
    (h1 : (c y).1 ∈ range (c.φ.model.E.toBase m)) (h2 : (c y).2 ∈ range (c.F.toBase k)) :
    y ∈ Bd.doubleLevel m k := by
  intro c' hc' hy'
  have hcomp := hc c' hc'
  have hov : c y ∈ c.overlap c' := ⟨y, ⟨hy, hy'⟩, rfl⟩
  have htr : c.transition c' (c y) = c' y := c.transition_apply c' hy
  have hPy : P y ∈ c.φ.source := by rw [c.source_eq] at hy; exact hy
  have hPy' : P y ∈ c'.φ.source := by rw [c'.source_eq] at hy'; exact hy'
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := h1
    have hbase := (c.isChart.compatible c'.isChart (P := PX)).1
    have hwov : w ∈ c.φ.model.E.lvlSet (c.φ.overlap c'.φ) m := by
      rw [ScBanach.mem_lvlSet, hw, c.covers y hy]; exact ⟨P y, ⟨hPy, hPy'⟩, rfl⟩
    have := (hbase.isSc0 (c.φ.isScRetract_overlap c'.φ)).mem_range m w hwov
    rwa [hw, c.covers y hy, c.φ.transition_apply c'.φ hPy, ← c'.covers y hy'] at this
  · rcases Nat.lt_or_ge k (m + 1) with hkm | hkm
    · have hkm' : k ≤ m := Nat.lt_succ_iff.1 hkm
      obtain ⟨w₁, hw₁⟩ := StrongBundle.range_toBase_mono c.φ.model.E hkm' h1
      obtain ⟨w₂, hw₂⟩ := h2
      have hw : (c.φ.model.E.prod c.F).toBase k (w₁, w₂) = c y := by
        rw [ScBanach.prod_toBase]; exact Prod.ext hw₁ hw₂
      have hwov : ((w₁, w₂) : (c.φ.model.E.prod c.F) k) ∈
          (c.φ.model.E.prod c.F).lvlSet (c.overlap c') k := by
        rw [ScBanach.mem_lvlSet, hw]; exact hov
      obtain ⟨v, hv⟩ := (hcomp.1.isSc0 (c.isScRetract_overlap c' Bd.continuous)).mem_range k _ hwov
      rw [hw, htr, ScBanach.prod_toBase] at hv
      exact ⟨v.2, congrArg Prod.snd hv⟩
    · have hk' : k = m + 1 := le_antisymm hk hkm
      subst hk'
      obtain ⟨w₁, hw₁⟩ := h1
      obtain ⟨w₂, hw₂⟩ := h2
      have h2' : (c y).2 ∈ range (c.F.toBase 1) :=
        StrongBundle.range_toBase_mono c.F (Nat.le_add_left 1 m) ⟨w₂, hw₂⟩
      have hlift : c.liftOne y = (c.φ.model.E.prod c.F.shift).toBase m (w₁, w₂) := by
        rw [ScBanach.prod_toBase]
        refine Prod.ext hw₁.symm (c.F.toBase_injective 1 ?_)
        change c.F.toBase 1 (Function.invFun (c.F.toBase 1) (c y).2) =
          c.F.toBase 1 (c.F.shift.toBase m w₂)
        rw [Function.invFun_eq h2', ← hw₂]
        exact ScBanach.shiftScale_toBase c.F.toScScale m w₂
      have hliftov : c.liftOne y ∈ strongShiftOne (c.overlap c') := by
        change ((c.liftOne y).1, c.F.toBase 1 (c.liftOne y).2) ∈ c.overlap c'
        rw [c.toBase_liftOne h2']; exact hov
      have hwov : ((w₁, w₂) : (c.φ.model.E.prod c.F.shift) m) ∈
          (c.φ.model.E.prod c.F.shift).lvlSet (strongShiftOne (c.overlap c')) m := by
        rw [ScBanach.mem_lvlSet, ← hlift]; exact hliftov
      obtain ⟨v, hv⟩ := (hcomp.2.2.1.isSc0 (c.isScRetract_overlap_one c' Bd.continuous)).mem_range
        m _ hwov
      rw [← hlift] at hv
      have hsf : shiftFiber (c.transition c') (c.liftOne y) = c'.liftOne y := by
        unfold shiftFiber
        rw [c.toBase_liftOne h2', htr]; rfl
      rw [hsf, ScBanach.prod_toBase] at hv
      have h2'' : (c' y).2 ∈ range (c'.F.toBase 1) := by
        have := hcomp.2.2.2.2.1 (c y) hov h2'
        rwa [htr] at this
      refine ⟨v.2, ?_⟩
      rw [ScBanach.shiftScale_toBase c'.F.toScScale m v.2]
      change c'.F.toBase 1 (c'.F.shift.toBase m v.2) = (c' y).2
      rw [show c'.F.shift.toBase m v.2 = (c'.liftOne y).2 from congrArg Prod.snd hv]
      exact Function.invFun_eq h2''

/-- The project's `Y_{m,k}` (every atlas chart) is B's `Y_{m,k}` (some compatible chart). -/
theorem doubleLevel_eq_YlevelB (Bd : StrongBundle PX P) {m k : ℕ} (hk : k ≤ m + 1) :
    Bd.doubleLevel m k = YlevelB Bd m k := by
  ext y
  constructor
  · intro h
    obtain ⟨c, hc, hy⟩ := Bd.atlas.cover y
    exact ⟨c, Bd.isChart_of_mem hc, hy, h c hc hy⟩
  · rintro ⟨c, hc, hy, h1, h2⟩
    exact mem_doubleLevel_of_isChart Bd hc hy hk h1 h2

/-- **B reduced to V3_13**: at every section whose germs agree in the two senses at all smooth
points, the project's sc-Fredholm sections are the text's. -/
theorem section_iff_of_germ_iff (Bd : StrongBundle PX P) (f : X → Y)
    (hgerm : ∀ x ∈ PX.smoothSet, (Bd.IsScFredholmGerm f x ↔ IsScFredholmGermB Bd f x)) :
    Bd.IsScFredholmSection f ↔ IsScFredholmSectionB Bd f := by
  have hreg : ∀ m, Bd.doubleLevel m (m + 1) = YlevelB Bd m (m + 1) :=
    fun m => doubleLevel_eq_YlevelB Bd le_rfl
  constructor
  · intro h
    refine ⟨h.isScSmooth, fun m x hx hfx => h.regularizing m x hx (by rw [hreg]; exact hfx),
      fun x hx => (hgerm x hx).1 (h.germ x hx)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun m x hx hfx => h2 m x hx (by rw [← hreg]; exact hfx),
      fun x hx => (hgerm x hx).2 (h3 x hx)⟩

end Bundle

/-- `A`, re-proved outright (B is not used). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_⟩
  swap
  · intro X _ _ _ PX Y _ _ _ P _ _ Bd f h
    exact ⟨h.isScSmooth, h.regularizing, fun x hx => (h.germ x hx).isScFredholmGerm⟩
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f hf x hx
  refine mem_iInter.2 fun m => ?_
  induction m with
  | zero => rw [PX.levelSet_zero]; exact mem_univ _
  | succ m ih =>
    refine hf.regularizing m x ih ?_
    rw [hx]; exact Bd.fiberZero_mem_doubleLevel ih

#rt_check RoundTrip.V3_16.B_to_A [Polyfold.StrongBundle.IsScFredholmSection.mem_smoothSet_of_isZeroAt, Polyfold.StrongBundle.IsScFredholmSectionWholeChart.isScFredholmSection]
#rt_overlap RoundTrip.V3_16.B_to_A [Polyfold.StrongBundle.IsScFredholmSection.mem_smoothSet_of_isZeroAt, Polyfold.StrongBundle.IsScFredholmSectionWholeChart.isScFredholmSection]
#rt_check RoundTrip.V3_16.section_iff_of_germ_iff [Polyfold.StrongBundle.IsScFredholmSection.mem_smoothSet_of_isZeroAt, Polyfold.StrongBundle.IsScFredholmSectionWholeChart.isScFredholmSection]

end RoundTrip.V3_16
