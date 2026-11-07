import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_1

/-! Round trip for V6_1 (Definition 6.1, `Lin(f, x)`, with the facts stated with it and the
convexity of p. 219).  A is the conjunction of the nine theorems of the comparison row, universes
at `0`.

* `B_to_A` is proved.  Every conjunct of A about `linSet` follows from B's clause (1)
  (`linSet = LinB` at a smooth point) together with B's (2)–(6) for `LinB`; the smoothness of `x`
  that B presupposes comes from a zero of `f + s` (Theorem 3.15 and
  `IsScFredholmSection.mem_smoothSet_of_isZeroAt`, non-item lemmas).  Glue: B's `IsScPlusOpB` is
  the project's `IsScPlusOp` (`isScPlusOp_of_B`); B's sc-Fredholm `IsScFredholmOfIndex` gives the
  level-`0` Fredholm property and index (`isFredholm_of_B`).  The last conjunct,
  `AdmitsBumpFunctions.hasScPlusSectionsThrough` (Lemma 5.11 with bump functions), is not
  addressed by B and is re-proved outright from `lemma_5_11`.
* `A_to_B` is not proved; see the JSON.  `B_gives_sections` records why: B's (1) and (2) together
  say that for every sc-Fredholm section `f`, smooth point `x` and chart point there is a GLOBAL
  sc⁺-section `s` with `(f + s)(x) = 0`, which A only gets from `HasScPlusSectionsThrough`
  (bump functions), and which the text's local reading of Definition 6.1 does not presuppose. -/

namespace RoundTrip.V6_1
open Polyfold

/-- The project's statement (the nine theorems of the row), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.ChartPoint.mem_linSet_iff.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.exists_isScPlusOp_linAt_eq.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.linSet_nonempty.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.isScPlusOp_sub_of_mem_linSet.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.isFredholm_isIndexAt_of_mem_linSet.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.exists_index_linSet.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.fredholmIndex_of_mem_linSet.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.convex_linSet.{0, 0} ∧
  type_of% @Polyfold.MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.ChartPoint.mem_linSet_iff.{0, 0},
    @Polyfold.ChartPoint.exists_isScPlusOp_linAt_eq.{0, 0},
    @Polyfold.ChartPoint.linSet_nonempty.{0, 0},
    @Polyfold.ChartPoint.isScPlusOp_sub_of_mem_linSet.{0, 0},
    @Polyfold.ChartPoint.isFredholm_isIndexAt_of_mem_linSet.{0, 0},
    @Polyfold.ChartPoint.exists_index_linSet.{0, 0},
    @Polyfold.ChartPoint.fredholmIndex_of_mem_linSet.{0, 0},
    @Polyfold.ChartPoint.convex_linSet.{0, 0},
    @Polyfold.MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough.{0, 0}⟩

noncomputable section

section Glue
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {Bd : StrongBundle PX P} {x : X}
  {f : X → Y}

/-- B's sc⁺-operators `T_zO → K_z` are the project's. -/
theorem isScPlusOp_of_B {p : ChartPoint Bd x} {a : ↥p.T →L[ℝ] ↥p.K} (h : IsScPlusOpB p a) :
    p.IsScPlusOp a := by
  obtain ⟨hT, hK, S, hS⟩ := h
  exact ⟨hT, hK, S, fun v => hS ⟨v.1, v.2⟩ v rfl⟩

/-- B's "level `0` of an sc-Fredholm sc-operator of index `i`" gives the project's level-`0`
Fredholm property with index `i`. -/
theorem isFredholm_of_B {p : ChartPoint Bd x} {L : ↥p.T →L[ℝ] ↥p.K} {i : ℤ}
    (h : IsScFredholmOfIndex p L i) : L.IsFredholm ∧ fredholmIndex L = i := by
  obtain ⟨hT, hK, L₀, hL₀, hL, ⟨sp⟩, hi⟩ := h
  have hF0 := sp.isFredholm 0
  rw [hL.toScOperator_zero] at hF0
  let e₁ : ↥p.T ≃L[ℝ] ↥(p.c.φ.model.E.levelSub p.T 0) :=
    (p.c.φ.model.E.levelSubZeroEquiv p.T).symm
  let e₂ : ↥(p.c.F.levelSub p.K 0) ≃L[ℝ] ↥p.K := p.c.F.levelSubZeroEquiv p.K
  have heq : L = (e₂ : ↥(p.c.F.levelSub p.K 0) →L[ℝ] ↥p.K).comp
      (L₀.comp (e₁ : ↥p.T →L[ℝ] ↥(p.c.φ.model.E.levelSub p.T 0))) := by
    refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
    exact (hL₀ v (e₁ v) rfl).symm
  have hc := isFredholm_equiv_comp_equiv hF0 e₁ e₂
  rw [heq]
  refine ⟨hc.1, hc.2.trans ?_⟩
  rw [← hi, scIndex_eq_fredholmIndex, hL.toScOperator_zero]

theorem isSmoothPt_of (hx : x ∈ PX.smoothSet) : IsSmoothPt PX x := fun m => Set.mem_iInter.1 hx m

/-- A member of `linSet` comes from a zero of `f + s`, so `x` is smooth. -/
theorem smooth_of_mem (hf : Bd.IsScFredholmSection f) {p : ChartPoint Bd x}
    {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) : x ∈ PX.smoothSet := by
  obtain ⟨s, hs, hx, -⟩ := hL
  exact (theorem_3_15 hf hs).mem_smoothSet_of_isZeroAt hx

theorem linSet_eq (hB : B) (hf : Bd.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (p : ChartPoint Bd x) : p.linSet f = LinB p f :=
  ((hB PX P Bd f x hf (isSmoothPt_of hx)).1 p).1

theorem sub_of_B (hB : B) (hf : Bd.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (p : ChartPoint Bd x) {L L' : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f)
    (hL' : L' ∈ p.linSet f) : p.IsScPlusOp (L - L') := by
  rw [linSet_eq hB hf hx p] at hL hL'
  exact isScPlusOp_of_B (((hB PX P Bd f x hf (isSmoothPt_of hx)).1 p).2.2.2.2.1 L hL L' hL')

theorem index_of_B (hB : B) (hf : Bd.IsScFredholmSection f) (hx : x ∈ PX.smoothSet) :
    ∃ i : ℤ, ∀ p : ChartPoint Bd x, ∀ L ∈ p.linSet f, L.IsFredholm ∧ fredholmIndex L = i := by
  obtain ⟨i, hi⟩ := (hB PX P Bd f x hf (isSmoothPt_of hx)).2
  exact ⟨i, fun p L hL => isFredholm_of_B (hi p L (linSet_eq hB hf hx p ▸ hL))⟩

/-- `(f + s)'(x)` for a global sc⁺-section `s` with `(f + s)(x) = 0`. -/
def lin₁ (p : ChartPoint Bd x) (hf : Bd.IsScFredholmSection f) {s : X → Y}
    (hs : Bd.IsScPlusSection s) (hx : IsZeroAt P (sectionAdd P f s) x) : ↥p.T →L[ℝ] ↥p.K :=
  (linAt p.c.U p.c.R (p.c.principal (sectionAdd P f s)) p.z).codRestrict p.K
    fun v => p.scDeriv_mem_K (hf.isScSmooth.sectionAdd hs) hx v

theorem lin₁_apply (p : ChartPoint Bd x) (hf : Bd.IsScFredholmSection f) {s : X → Y}
    (hs : Bd.IsScPlusSection s) (hx : IsZeroAt P (sectionAdd P f s) x) (v : ↥p.T) :
    ((lin₁ p hf hs hx v : ↥p.K) : p.c.F 0) =
      linAt p.c.U p.c.R (p.c.principal (sectionAdd P f s)) p.z v := rfl

theorem lin₁_mem (p : ChartPoint Bd x) (hf : Bd.IsScFredholmSection f) {s : X → Y}
    (hs : Bd.IsScPlusSection s) (hx : IsZeroAt P (sectionAdd P f s) x) :
    lin₁ p hf hs hx ∈ p.linSet f :=
  ⟨s, hs, hx, 0, p.isScPlusOp_zero ((theorem_3_15 hf hs).mem_smoothSet_of_isZeroAt hx),
    fun v => by rw [zero_apply, Submodule.coe_zero, add_zero, lin₁_apply]⟩

end Glue

/-- **What B says beyond A**: B's (1) (`linSet = LinB`) and (2) (`LinB` is nonempty) give a
global sc⁺-section `s` with `(f + s)(x) = 0` for every sc-Fredholm `f`, smooth `x` and chart
point, with no bump functions.  A has such sections only under `HasScPlusSectionsThrough`. -/
theorem B_gives_sections (hB : B) {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (PX : MPolyfold X) {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})]
    [∀ x, Module ℝ (P ⁻¹' {x})] (Bd : StrongBundle PX P) (f : X → Y) (x : X)
    (hf : Bd.IsScFredholmSection f) (hx : IsSmoothPt PX x) (p : ChartPoint Bd x) :
    ∃ s : X → Y, Bd.IsScPlusSection s ∧ IsZeroAt P (sectionAdd P f s) x := by
  have h := (hB PX P Bd f x hf hx).1 p
  obtain ⟨L, hL⟩ := h.2.2.1
  rw [← h.1] at hL
  obtain ⟨s, hs, hx0, -⟩ := hL
  exact ⟨s, hs, hx0⟩

/-- A's last conjunct (Lemma 5.11 with bump functions), which B does not address: re-proved
outright from the non-item lemmas `proposition_5_3_exists` and `lemma_5_11`. -/
theorem hasScPlusSectionsThrough_outright :
    type_of% @Polyfold.MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough.{0, 0} := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd hbump x hx e he hex
  obtain ⟨N, hN⟩ := proposition_5_3_exists (B := Bd)
  obtain ⟨-, s, hs, hsx, -, -⟩ :=
    lemma_5_11 hbump hN hx he hex one_pos isOpen_univ (Set.mem_univ x)
  exact ⟨s, hs, hsx⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `mem_linSet_iff`
    intro X _ _ _ PX Y _ _ _ P _ _ Bd f s x p hf hs hx L
    constructor
    · intro hL
      have hxs := (theorem_3_15 hf hs).mem_smoothSet_of_isZeroAt hx
      refine ⟨L - lin₁ p hf hs hx, sub_of_B hB hf hxs p hL (lin₁_mem p hf hs hx), fun v => ?_⟩
      rw [sub_apply, Submodule.coe_sub, lin₁_apply]
      abel
    · rintro ⟨a, ha, hLv⟩
      exact ⟨s, hs, hx, a, ha, hLv⟩
  · -- `exists_isScPlusOp_linAt_eq`
    intro X _ _ _ PX Y _ _ _ P _ _ Bd f x p hf s s' hs hs' hx hx'
    have hxs := (theorem_3_15 hf hs).mem_smoothSet_of_isZeroAt hx
    refine ⟨lin₁ p hf hs' hx' - lin₁ p hf hs hx,
      sub_of_B hB hf hxs p (lin₁_mem p hf hs' hx') (lin₁_mem p hf hs hx), fun v => ?_⟩
    rw [sub_apply, Submodule.coe_sub, lin₁_apply, lin₁_apply]
    abel
  · -- `linSet_nonempty` (B needs no sections through `−f(x)` here)
    intro X _ _ _ PX Y _ _ _ P _ _ Bd f x p hf hx _
    rw [linSet_eq hB hf hx p]
    exact ((hB PX P Bd f x hf (isSmoothPt_of hx)).1 p).2.2.1
  · -- `isScPlusOp_sub_of_mem_linSet`
    intro X _ _ _ PX Y _ _ _ P _ _ Bd f x p hf L L' hL hL'
    exact sub_of_B hB hf (smooth_of_mem hf hL) p hL hL'
  · -- `isFredholm_isIndexAt_of_mem_linSet`
    intro X _ _ _ PX Y _ _ _ P _ _ Bd f x p hf L hL
    have hxs := smooth_of_mem hf hL
    obtain ⟨s, hs, hx0, -⟩ := id hL
    obtain ⟨i, hi⟩ := index_of_B hB hf hxs
    obtain ⟨hF, hLi⟩ := hi p L hL
    refine ⟨hF, ?_⟩
    rw [hLi]
    refine ⟨s, hs, hx0, fun c hc hxc z hz hzU L' hL' => ?_⟩
    let p' : ChartPoint Bd x := ⟨c, hc, hxc, z, hz⟩
    have hmem : (L' : ↥p'.T →L[ℝ] ↥p'.K) ∈ p'.linSet f :=
      ⟨s, hs, hx0, 0, p'.isScPlusOp_zero hxs, fun v => by
        rw [zero_apply, Submodule.coe_zero, add_zero]
        exact hL' v⟩
    exact hi p' L' hmem
  · -- `exists_index_linSet`
    intro X _ _ _ PX Y _ _ _ P _ _ Bd f x p hf
    rcases (p.linSet f).eq_empty_or_nonempty with h | ⟨L₀, hL₀⟩
    · exact ⟨0, fun L hL => absurd (h ▸ hL) (Set.notMem_empty L)⟩
    · obtain ⟨i, hi⟩ := index_of_B hB hf (smooth_of_mem hf hL₀)
      exact ⟨i, hi p⟩
  · -- `fredholmIndex_of_mem_linSet`
    intro X _ _ _ PX Y _ _ _ P _ _ Bd f x p hf i hiA L hL
    obtain ⟨i', hi'⟩ := index_of_B hB hf (smooth_of_mem hf hL)
    obtain ⟨s₀, hs₀, hz₀, hlin⟩ := hiA
    have h1 := hlin p.c p.isChart p.mem_source p.z p.toBase_z p.mem_U (lin₁ p hf hs₀ hz₀)
      (fun _ => rfl)
    have h2 := hi' p _ (lin₁_mem p hf hs₀ hz₀)
    obtain ⟨hF, hLi⟩ := hi' p L hL
    exact ⟨hF, hLi.trans (h2.2.symm.trans h1.2)⟩
  · -- `convex_linSet`
    intro X _ _ _ PX Y _ _ _ P _ _ Bd f x p hf
    rcases (p.linSet f).eq_empty_or_nonempty with h | ⟨L₀, hL₀⟩
    · rw [h]; exact convex_empty
    · have hxs := smooth_of_mem hf hL₀
      rw [linSet_eq hB hf hxs p]
      exact ((hB PX P Bd f x hf (isSmoothPt_of hxs)).1 p).2.2.2.2.2
  · -- `AdmitsBumpFunctions.hasScPlusSectionsThrough`: not in B (outright, Lemma 5.11)
    exact hasScPlusSectionsThrough_outright

end

/-! `#rt_overlap` of the outright conjunct alone, to separate it from the part of `B_to_A` that
uses B (the large overlap of `B_to_A` is mostly Lemma 5.11 and Theorem 3.15). -/
#rt_overlap RoundTrip.V6_1.hasScPlusSectionsThrough_outright [Polyfold.ChartPoint.mem_linSet_iff,
  Polyfold.ChartPoint.exists_isScPlusOp_linAt_eq, Polyfold.ChartPoint.linSet_nonempty,
  Polyfold.ChartPoint.isScPlusOp_sub_of_mem_linSet,
  Polyfold.ChartPoint.isFredholm_isIndexAt_of_mem_linSet, Polyfold.ChartPoint.exists_index_linSet,
  Polyfold.ChartPoint.fredholmIndex_of_mem_linSet, Polyfold.ChartPoint.convex_linSet,
  Polyfold.MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough]

#rt_check RoundTrip.V6_1.B_to_A [Polyfold.ChartPoint.mem_linSet_iff,
  Polyfold.ChartPoint.exists_isScPlusOp_linAt_eq, Polyfold.ChartPoint.linSet_nonempty,
  Polyfold.ChartPoint.isScPlusOp_sub_of_mem_linSet,
  Polyfold.ChartPoint.isFredholm_isIndexAt_of_mem_linSet, Polyfold.ChartPoint.exists_index_linSet,
  Polyfold.ChartPoint.fredholmIndex_of_mem_linSet, Polyfold.ChartPoint.convex_linSet,
  Polyfold.MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough]
#rt_overlap RoundTrip.V6_1.B_to_A [Polyfold.ChartPoint.mem_linSet_iff,
  Polyfold.ChartPoint.exists_isScPlusOp_linAt_eq, Polyfold.ChartPoint.linSet_nonempty,
  Polyfold.ChartPoint.isScPlusOp_sub_of_mem_linSet,
  Polyfold.ChartPoint.isFredholm_isIndexAt_of_mem_linSet, Polyfold.ChartPoint.exists_index_linSet,
  Polyfold.ChartPoint.fredholmIndex_of_mem_linSet, Polyfold.ChartPoint.convex_linSet,
  Polyfold.MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough]

end RoundTrip.V6_1
