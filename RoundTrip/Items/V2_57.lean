import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_57

/-! Round trip for V2_57 (Definition 2.50: strong bundle charts, their compatibility, strong bundle
atlases and their equivalence).

`A` is the conjunction of the types of the theorems `StrongBundleChart.continuous_fiber`,
`StrongBundleChart.Compatible.symm` and (refresh 2026-11-02, added to the row)
`StrongBundleChart.compatible_of_locally` (compatibility is local), `StrongBundleAtlas.equiv_iff`,
`StrongBundleAtlas.Equiv.trans`, `StrongBundleAtlas.equivalence` (atlas equivalence is an
equivalence relation), `IsStrongBundleRetraction.restrict`, `StrongBundleChart.Compatible.restrict`
(restriction of charts), at universes `0, 0` (`IsStrongBundleRetraction.restrict` has none).
`IsBanachable`, `StrongBundleChart`, `StrongBundleChart.K`, `StrongBundleChart.Compatible`,
`StrongBundleAtlas`, `StrongBundleAtlas.Equiv`, `StrongBundleChart.restrict` are definitions
(vocabulary; B compares the first ones with its own notions).

`A → B` (proved):
* charts: every field of a project chart is a clause of B's `IsStrongBundleChartB` (the strong
  bundle retraction is converted by `retr_to_B`; `r(U) = O` is `base_retract` definitionally);
  the continuity of the fibre maps is `continuous_fiber` (the hypothesis).  Conversely a B-chart
  whose base chart is a chart of `PX` is a project chart (`B_to_retr`); B itself restricts this
  clause to `PX.IsChart d.φ`, the project's extra field `isChart`.
* compatibility: the project's `Compatible` (four `IsScSmoothRetractMap`s in the "every
  retraction" form plus the `F₁`-preservation of both transitions) is B's `CompatibleB`
  (sc-diffeomorphisms between the retracts in the "one retraction" form, with explicit lifts
  `g₁`, `g₁'` on `[1]`): `→` needs the overlaps `Φ(P⁻¹(V ∩ V'))` and their `[1]`-parts to be
  retracts (`StrongBundleChart.isScRetract_overlap(_one)`, using `Continuous P` from B), the
  mutual inverse property is `transition_apply`, the lifts are `shiftFiber`; `←` reads the
  `F₁`-preservation off the lifts and transfers sc-smoothness by `IsScSmoothRetractMap.congr`.
* atlases and their equivalence: images under `toDataB`, using the two points above.

`A → B` uses only the conjunct `continuous_fiber`; the added conjuncts are not needed.

`B → A` fails by scope: `continuous_fiber`, `Compatible.symm` and the added chart/atlas lemmas hold
for any `P : Y → X` (no continuity, no Hausdorff/paracompact `Y`, no Banachable fibres), while B
only speaks about charts of a `P` satisfying all of these.  Moreover the added conjuncts are not
part of Definition 2.50 as B states it (B deliberately leaves out that atlas equivalence is an
equivalence relation): the locality of compatibility (Theorem 2.8 on `[0]` and `[1]`, the
`F₁`-condition through a middle chart), the restriction of strong bundle retractions and charts,
and transitivity would have to be proved anew, i.e. the project's arguments. -/

namespace RoundTrip.V2_57
open Polyfold Set

/-- The project's statement (universes `0`). -/
def A : Prop :=
  (type_of% @Polyfold.StrongBundleChart.continuous_fiber.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundleChart.Compatible.symm.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundleChart.compatible_of_locally.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundleAtlas.equiv_iff.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundleAtlas.Equiv.trans.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundleAtlas.equivalence.{0, 0}) ∧
    (type_of% @Polyfold.IsStrongBundleRetraction.restrict) ∧
    (type_of% @Polyfold.StrongBundleChart.Compatible.restrict.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundleChart.continuous_fiber.{0, 0},
    @Polyfold.StrongBundleChart.Compatible.symm.{0, 0},
    @Polyfold.StrongBundleChart.compatible_of_locally.{0, 0},
    @Polyfold.StrongBundleAtlas.equiv_iff.{0, 0}, @Polyfold.StrongBundleAtlas.Equiv.trans.{0, 0},
    @Polyfold.StrongBundleAtlas.equivalence.{0, 0}, @Polyfold.IsStrongBundleRetraction.restrict,
    @Polyfold.StrongBundleChart.Compatible.restrict.{0, 0}⟩

section Retraction

variable {E F : ScBanach} {C U : Set (E.lvl 0)} {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0}

/-- The project's strong bundle retractions are B's. -/
theorem retr_to_B (hR : IsStrongBundleRetraction U R) : IsStrongBundleRetractionB U R := by
  refine ⟨⟨⟨IsStrongBundleMap.base R, fun u hu => ⟨(hR.mapsTo ⟨hu, mem_univ _⟩).1,
    fun h => hR.fst_independent u hu h 0⟩⟩, hR.fiber_linear, ?_, hR.isScSmooth_zero,
    ⟨shiftFiber R, fun u hu h => ⟨rfl, ?_⟩, hR.isScSmooth_one⟩⟩,
    fun u hu h => hR.idem (u, h) ⟨hu, mem_univ _⟩⟩
  · intro m k hk q hq
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
      hR.preserves_filtration m k hk _ hq ⟨q.1, rfl⟩ _ ⟨q.2, rfl⟩
    exact ⟨(a, b), Prod.ext ha.symm hb.symm⟩
  · exact hR.toBase_shiftFiber_snd (p := (u, h)) hu

/-- B's strong bundle retractions (on a relatively open `U`) are the project's. -/
theorem B_to_retr (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetractionB U R) :
    IsStrongBundleRetraction U R := by
  obtain ⟨⟨⟨φ, hφ⟩, hlin, hfilt, h0, ⟨Φ₁, hΦ₁, h1⟩⟩, hidem⟩ := hR
  refine ⟨⟨?_, ?_, hlin, ?_, h0, ?_⟩, ?_⟩
  · rintro ⟨u, h⟩ ⟨hu, -⟩
    refine ⟨?_, mem_univ _⟩
    rw [(hφ u hu).2 h]; exact (hφ u hu).1
  · intro u hu h h'
    rw [(hφ u hu).2 h, (hφ u hu).2 h']
  · rintro m k hk u hu ⟨a, rfl⟩ h ⟨b, rfl⟩
    obtain ⟨q', hq'⟩ := hfilt m k hk (a, b) hu
    exact ⟨⟨q'.1, by rw [hq']⟩, ⟨q'.2, by rw [hq']⟩⟩
  · refine IsScSmooth.congr (hU.prod_univ F.shift).isScDomain ?_ h1
    rintro ⟨u, h⟩ ⟨hu, -⟩
    obtain ⟨e1, e2⟩ := hΦ₁ u hu h
    have hr : (R (u, F.toBase 1 h)).2 ∈ range (F.toBase 1) := ⟨_, e2⟩
    refine Prod.ext e1 ?_
    change (Φ₁ (u, h)).2 = Function.invFun (F.toBase 1) (R (u, F.toBase 1 h)).2
    apply F.toBase_injective 1
    rw [Function.invFun_eq hr, e2]
  · rintro ⟨u, h⟩ ⟨hu, -⟩
    exact hidem u hu h

end Retraction

section Shift

variable {E F E' F' : ScBanach} {A : Set (E.lvl 0 × F.lvl 0)}
  {g : E.lvl 0 × F.lvl 0 → E'.lvl 0 × F'.lvl 0} {g' : E'.lvl 0 × F'.lvl 0 → E.lvl 0 × F.lvl 0}

/-- A lift `g₁` of `g` on `A[1]` is `shiftFiber g` there. -/
theorem lift_eqOn {g₁ : (E.prod F.shift).lvl 0 → (E'.prod F'.shift).lvl 0}
    (hl : IsLiftOnB A g g₁) : EqOn g₁ (shiftFiber g) (oneB A) := by
  intro q hq
  refine Prod.ext (hl q hq).1 ?_
  change (g₁ q).2 = Function.invFun (F'.toBase 1) (g (q.1, F.toBase 1 q.2)).2
  rw [← (hl q hq).2]
  exact (Function.leftInverse_invFun (F'.toBase_injective 1) _).symm

/-- `shiftFiber g` is a lift of `g` on `A[1]` when `g` preserves fibre components in `F₁`. -/
theorem shiftFiber_lift
    (h5 : ∀ x ∈ A, x.2 ∈ range (F.toBase 1) → (g x).2 ∈ range (F'.toBase 1)) :
    IsLiftOnB A g (shiftFiber g) := fun q hq =>
  ⟨rfl, Function.invFun_eq (h5 _ hq ⟨q.2, rfl⟩)⟩

/-- `(g' ∘ g)[1] = id` on `A[1]` when `g' ∘ g = id` on `A`. -/
theorem shiftFiber_inv (hinv : ∀ a ∈ A, g' (g a) = a)
    (h5 : ∀ x ∈ A, x.2 ∈ range (F.toBase 1) → (g x).2 ∈ range (F'.toBase 1))
    {q : (E.prod F.shift).lvl 0} (hq : q ∈ oneB A) : shiftFiber g' (shiftFiber g q) = q := by
  have e : ((shiftFiber g q).1, F'.toBase 1 (shiftFiber g q).2) = g (q.1, F.toBase 1 q.2) :=
    Prod.ext rfl (Function.invFun_eq (h5 _ hq ⟨q.2, rfl⟩))
  change ((g' ((shiftFiber g q).1, F'.toBase 1 (shiftFiber g q).2)).1,
    Function.invFun (F.toBase 1) (g' ((shiftFiber g q).1, F'.toBase 1 (shiftFiber g q).2)).2) = q
  rw [e, hinv _ hq]
  exact Prod.ext rfl (Function.leftInverse_invFun (F.toBase_injective 1) q.2)

/-- The `F₁`-preservation of `g`, read off a lift. -/
theorem range_of_lift {g₁ : (E.prod F.shift).lvl 0 → (E'.prod F'.shift).lvl 0}
    (hl : IsLiftOnB A g g₁) : ∀ x ∈ A, x.2 ∈ range (F.toBase 1) →
      (g x).2 ∈ range (F'.toBase 1) := by
  rintro ⟨a, b⟩ hx ⟨w, rfl⟩
  exact ⟨_, (hl (a, w) hx).2⟩

end Shift

section Charts

variable {X Y : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [TopologicalSpace Y] {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- Project charts are B's charts (the fibre continuity from `continuous_fiber`). -/
theorem chart_to_B (hcf : type_of% @Polyfold.StrongBundleChart.continuous_fiber.{0, 0})
    (c : StrongBundleChart PX P) : IsStrongBundleChartB P (toDataB c) :=
  ⟨c.relOpen, retr_to_B c.isRetraction, c.base_retract, c.source_eq, c.target_eq,
    c.continuousOn_toFun, c.continuousOn_invFun, c.covers,
    fun x hx => ⟨c.fiber_linear x hx, hcf c x hx⟩⟩

/-- B's charts whose base chart is a chart of `PX` are project charts. -/
theorem chart_of_B (d : ChartDataB X Y) (hd : PX.IsChart d.φ) (h : IsStrongBundleChartB P d) :
    ∃ c : StrongBundleChart PX P, toDataB c = d := by
  obtain ⟨φ, F, U, R, Φ⟩ := d
  obtain ⟨hU, hRB, hbase, hsrc, htgt, hc1, hc2, hcov, hfib⟩ := h
  exact ⟨⟨φ, hd, F, U, R, hU, B_to_retr hU hRB, hbase, Φ, hsrc, htgt, hc1, hc2, hcov,
    fun x hx => (hfib x hx).1⟩, rfl⟩

/-- The project's compatibility is B's (for continuous `P`). -/
theorem compatible_iff (hP : Continuous P) (c c' : StrongBundleChart PX P) :
    c.Compatible c' ↔ CompatibleB (toDataB c) (toDataB c') := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    obtain ⟨ρ, hρ⟩ := c.isScRetract_overlap c' hP
    obtain ⟨ρ', hρ'⟩ := c'.isScRetract_overlap c hP
    obtain ⟨ρ₁, hρ₁⟩ := c.isScRetract_overlap_one c' hP
    obtain ⟨ρ₁', hρ₁'⟩ := c'.isScRetract_overlap_one c hP
    have hinv : ∀ a ∈ c.overlap c', c'.transition c (c.transition c' a) = a := by
      rintro _ ⟨y, ⟨hy, hy'⟩, rfl⟩
      rw [c.transition_apply c' hy, c'.transition_apply c hy']
    have hinv' : ∀ a ∈ c'.overlap c, c.transition c' (c'.transition c a) = a := by
      rintro _ ⟨y, ⟨hy', hy⟩, rfl⟩
      rw [c'.transition_apply c hy', c.transition_apply c' hy]
    refine ⟨⟨⟨h1.mapsTo, ρ, hρ, h1.comp_isScSmooth ρ hρ⟩, ⟨h2.mapsTo, ρ', hρ', h2.comp_isScSmooth ρ' hρ'⟩,
      hinv, hinv'⟩, shiftFiber (c.transition c'), shiftFiber (c'.transition c),
      shiftFiber_lift h5, shiftFiber_lift h6, ⟨h3.mapsTo, ρ₁, hρ₁, h3.comp_isScSmooth ρ₁ hρ₁⟩,
      ⟨h4.mapsTo, ρ₁', hρ₁', h4.comp_isScSmooth ρ₁' hρ₁'⟩, fun q hq => shiftFiber_inv hinv h5 hq,
      fun q hq => shiftFiber_inv hinv' h6 hq⟩
  · rintro ⟨⟨⟨m1, ρ, hρ, s1⟩, ⟨m2, ρ', hρ', s2⟩, -, -⟩, g₁, g₁', hl, hl',
      ⟨⟨m3, ρ₁, hρ₁, s3⟩, ⟨m4, ρ₁', hρ₁', s4⟩, -, -⟩⟩
    exact ⟨(isScSmoothRetractMap_iff_exists ⟨ρ, hρ⟩).2 ⟨m1, ρ, hρ, s1⟩,
      (isScSmoothRetractMap_iff_exists ⟨ρ', hρ'⟩).2 ⟨m2, ρ', hρ', s2⟩,
      ((isScSmoothRetractMap_iff_exists ⟨ρ₁, hρ₁⟩).2 ⟨m3, ρ₁, hρ₁, s3⟩).congr (lift_eqOn hl),
      ((isScSmoothRetractMap_iff_exists ⟨ρ₁', hρ₁'⟩).2 ⟨m4, ρ₁', hρ₁', s4⟩).congr (lift_eqOn hl'),
      range_of_lift hl, range_of_lift hl'⟩

/-- Project atlases are B's atlases. -/
theorem atlas_to_B (hcf : type_of% @Polyfold.StrongBundleChart.continuous_fiber.{0, 0})
    (hP : Continuous P) (A : StrongBundleAtlas PX P) : IsAtlasB P (toDataB '' A.charts) := by
  refine ⟨?_, ?_, fun y => ?_⟩
  · rintro _ ⟨c, -, rfl⟩; exact chart_to_B hcf c
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    exact (compatible_iff hP c c').1 (A.compatible c hc c' hc')
  · obtain ⟨c, hc, hy⟩ := A.cover y
    exact ⟨toDataB c, ⟨c, hc, rfl⟩, hy⟩

end Charts

theorem A_to_B : A → B := by
  rintro ⟨hcf, -⟩ X Y _ _ _ PX _ _ _ P _ _ hP _
  refine ⟨chart_to_B hcf, fun d hd h => chart_of_B d hd h, compatible_iff hP,
    atlas_to_B hcf hP, fun 𝒜 hch h𝒜 => ?_, fun A A' => ⟨?_, ?_⟩⟩
  · obtain ⟨hcharts, hcomp, hcover⟩ := h𝒜
    refine ⟨⟨{c | toDataB c ∈ 𝒜}, fun c hc c' hc' => (compatible_iff hP c c').2 (hcomp _ hc _ hc'),
      fun y => ?_⟩, ?_⟩
    · obtain ⟨d, hd, hy⟩ := hcover y
      obtain ⟨c, rfl⟩ := chart_of_B d (hch d hd) (hcharts d hd)
      exact ⟨c, hd, hy⟩
    · ext d
      refine ⟨fun ⟨c, hc, hcd⟩ => hcd ▸ hc, fun hd => ?_⟩
      obtain ⟨c, rfl⟩ := chart_of_B d (hch d hd) (hcharts d hd)
      exact ⟨c, hd, rfl⟩
  · rintro ⟨D, hD⟩
    change IsAtlasB P (toDataB '' A.charts ∪ toDataB '' A'.charts)
    rw [← image_union, ← hD]
    exact atlas_to_B hcf hP D
  · rintro ⟨-, hcomp, -⟩
    refine ⟨⟨A.charts ∪ A'.charts, fun c hc c' hc' => (compatible_iff hP c c').2
      (hcomp _ (hc.elim (fun h => Or.inl ⟨c, h, rfl⟩) fun h => Or.inr ⟨c, h, rfl⟩) _
        (hc'.elim (fun h => Or.inl ⟨c', h, rfl⟩) fun h => Or.inr ⟨c', h, rfl⟩)),
      fun y => ?_⟩, rfl⟩
    obtain ⟨c, hc, hy⟩ := A.cover y
    exact ⟨c, Or.inl hc, hy⟩

/- `#rt_check_soft`: the statement `A` mentions the definition `StrongBundleChart.restrict` (in the
type of `Compatible.restrict`), whose proof field `restrict._proof_3` is the banned
`IsStrongBundleRetraction.restrict`; the proof of `A_to_B` reaches it only that way (through the
binder type `A`), not as a lemma. -/
#rt_check_soft RoundTrip.V2_57.A_to_B [Polyfold.StrongBundleChart.continuous_fiber,
  Polyfold.StrongBundleChart.Compatible.symm, Polyfold.StrongBundleChart.compatible_of_locally,
  Polyfold.StrongBundleAtlas.equiv_iff, Polyfold.StrongBundleAtlas.Equiv.trans,
  Polyfold.StrongBundleAtlas.equivalence, Polyfold.IsStrongBundleRetraction.restrict,
  Polyfold.StrongBundleChart.Compatible.restrict]

end RoundTrip.V2_57
