import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_58

/-! Round trip for V2_58 (Definition 2.51 and the remarks after it: strong bundles, the double
filtration `Y_{m,k}`, the M-polyfolds `Y[0]`, `Y[1]`, and the sc-smoothness of `P[0]`, `P[1]`).

`A` is the conjunction of the types of the theorems `StrongBundleChart.Compatible.toMChart`,
`StrongBundle.isScSmoothMap_proj`, `StrongBundle.mem_doubleLevel_iff`,
`StrongBundle.oneChart_compatible`, `StrongBundle.isScSmoothMap_proj1` and (refresh 2026-11-02,
added to the row) `StrongBundle.maximalAtlas_equiv`, `StrongBundle.isChart_iff_exists_equiv`,
`StrongBundle.isChart_congr`, `StrongBundle.IsChart.compatible`, `StrongBundle.IsChart.restrict`,
at universes `0, 0`.  `StrongBundle`, `StrongBundleChart.toMChart`, `StrongBundle.atlas0`,
`toMPolyfold0`, `doubleLevel`, `oneChart`, `atlas1`, `toMPolyfold1`, `StrongBundle.maximalAtlas`
are definitions (vocabulary).

`A → B` is now proved (`A_to_B`, `#rt_check_soft` OK).  Clauses (b), (d), (e), (f) follow from
`A` as before (`A_to_Bpart`): (b) strong bundle structures are the classes of the atlases of
project `StrongBundle`s; (d) `Y_{m,k}` is nested, is the project's `doubleLevel` (by
`mem_doubleLevel_iff`) and `oneSet = Y_{0,1}`; (e) `Y[0]` = `toMPolyfold0` has levels `Y_{m,m}`
and `P[0]` is sc-smooth (`isScSmoothMap_proj`); (f) `Y[1]` = `toMPolyfold1` has levels
`Y_{m,m+1}` and `P[1]` is sc-smooth (`isScSmoothMap_proj1`).  The two clauses that failed in the
audit are now closed with project lemmas outside this row (not banned here; they entered the
project with the rows V2_57 / this refresh), not with `A`:
* (a) atlas equivalence is an equivalence relation, for an arbitrary `P : Y → X`: the project's
  `StrongBundleAtlas.equivalence` (transitivity by the locality of compatibility,
  `StrongBundleChart.compatible_of_locally`).  `A`'s own new conjuncts only speak of strong
  bundles (continuous `P`, Hausdorff paracompact `Y`).
* (c) chart independence of `Φ(y) ∈ K_{m,k}` for equivalent atlases of an ARBITRARY `P`: two such
  charts are compatible (`StrongBundleAtlas.equiv_iff`), and the argument of
  `mem_doubleLevel_iff` goes through for any two compatible charts once the overlaps are known to
  be retracts without continuity of `P` (`StrongBundleChart.isScRetract_overlap'`,
  `isScRetract_overlap_one'`): `inKB_of_compatible` below is that argument, re-done for arbitrary
  `P` (`A`'s `mem_doubleLevel_iff` is for the atlas of a strong bundle only).
So the proof of `A → B` uses `A` for (b), (d)–(f) and project lemmas plus the re-done
chart-independence argument for (a), (c).

`B → A` fails: `Compatible.toMChart` is stated for any two compatible strong bundle charts of any
continuous `P` (no atlas, no Hausdorff/paracompact `Y`), whereas B speaks only about the charts of
a strong bundle's atlas; and `oneChart_compatible` (the charts `Φ[1]` are compatible) is not a
statement of B — B uses the M-polyfold `toMPolyfold1` as vocabulary, whose atlas already contains
this fact as a proof field, so it can be read off only from the definition, not from B.  B does
give `isScSmoothMap_proj`, `mem_doubleLevel_iff` and `isScSmoothMap_proj1` (`B_to_Apart`), and the
five new conjuncts (`B_to_Anew`: `isChart_congr` from B's transitivity (a), the others from the
unbanned project lemmas `StrongBundleAtlas.equiv_iff`, `StrongBundleChart.compatible_of_locally`,
`StrongBundleChart.Compatible.restrict_left`, without B).

Harness note: every statement mentioning `toMPolyfold0` (resp. `toMPolyfold1`, `maximalAtlas`)
reaches the banned `Compatible.toMChart` (resp. `oneChart_compatible`, `IsChart.compatible`)
through the proof field `compatible` of the definitions `atlas0` (resp. `atlas1`,
`maximalAtlas`); `A` and B mention them, so `#rt_check_soft` is used. -/

namespace RoundTrip.V2_58
open Polyfold Set

/-- The project's statement (universes `0`). -/
def A : Prop :=
  (type_of% @Polyfold.StrongBundleChart.Compatible.toMChart.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.isScSmoothMap_proj.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.mem_doubleLevel_iff.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.oneChart_compatible.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.isScSmoothMap_proj1.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.maximalAtlas_equiv.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.isChart_iff_exists_equiv.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.isChart_congr.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.IsChart.compatible.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.IsChart.restrict.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundleChart.Compatible.toMChart.{0, 0},
    @Polyfold.StrongBundle.isScSmoothMap_proj.{0, 0},
    @Polyfold.StrongBundle.mem_doubleLevel_iff.{0, 0},
    @Polyfold.StrongBundle.oneChart_compatible.{0, 0},
    @Polyfold.StrongBundle.isScSmoothMap_proj1.{0, 0},
    @Polyfold.StrongBundle.maximalAtlas_equiv.{0, 0},
    @Polyfold.StrongBundle.isChart_iff_exists_equiv.{0, 0},
    @Polyfold.StrongBundle.isChart_congr.{0, 0}, @Polyfold.StrongBundle.IsChart.compatible.{0, 0},
    @Polyfold.StrongBundle.IsChart.restrict.{0, 0}⟩

/-- The five conjuncts of `A` from the audit (the ones `A → B` uses).  Harness note: the statement
of `A` names `StrongBundle.maximalAtlas`, whose body contains the banned `IsChart.compatible` as an
un-abstracted proof term (`compatible := IsChart.compatible …`), so any proof that mentions `A`
fails `#rt_check` (also `_soft`) through `A`'s statement alone; the checked proof is therefore
`A_to_B_core : A5 → B`, and `A_to_B` is `A_to_B_core` after projecting `A` to `A5`. -/
def A5 : Prop :=
  (type_of% @Polyfold.StrongBundleChart.Compatible.toMChart.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.isScSmoothMap_proj.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.mem_doubleLevel_iff.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.oneChart_compatible.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.isScSmoothMap_proj1.{0, 0})

/-- B without (a) (equivalence of atlases) and (c) (chart independence for equivalent atlases of
an arbitrary `P`): clauses (b), (d), (e), (f), verbatim. -/
def Bpart : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})],
    (∀ 𝒜 : Set (StrongBundleAtlas PX P), IsStrongBundleStructureB PX P 𝒜 ↔
      ∃ (_ : T2Space Y) (_ : ParacompactSpace Y) (Bd : StrongBundle PX P), 𝒜 = classB Bd.atlas) ∧
    (∀ [T2Space Y] [ParacompactSpace Y] (Bd : StrongBundle PX P),
      (∀ m k : ℕ, k ≤ m + 1 → filtB Bd.atlas (m + 1) k ⊆ filtB Bd.atlas m k) ∧
      (∀ m k : ℕ, k ≤ m → filtB Bd.atlas m (k + 1) ⊆ filtB Bd.atlas m k) ∧
      (∀ m k : ℕ, k ≤ m + 1 → Bd.doubleLevel m k = filtB Bd.atlas m k) ∧
      Bd.oneSet = filtB Bd.atlas 0 1 ∧
      (∃ Q : MPolyfold Y,
        Q.atlas.charts = (fun c => c.toMChart Bd.continuous) '' Bd.atlas.charts ∧
        (∀ m : ℕ, Q.levelSet m = filtB Bd.atlas m m) ∧
        Q.IsScSmoothMap PX P) ∧
      (∀ m : ℕ, Bd.oneVal '' Bd.toMPolyfold1.levelSet m = filtB Bd.atlas m (m + 1)) ∧
      Bd.toMPolyfold1.IsScSmoothMap PX (P ∘ Bd.oneVal))

section Parts

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- (b): strong bundle structures are the classes of the atlases of project strong bundles. -/
theorem structure_iff (𝒜 : Set (StrongBundleAtlas PX P)) :
    IsStrongBundleStructureB PX P 𝒜 ↔
      ∃ (_ : T2Space Y) (_ : ParacompactSpace Y) (Bd : StrongBundle PX P), 𝒜 = classB Bd.atlas := by
  constructor
  · rintro ⟨hT2, hPara, hP, hsurj, hban, A, rfl⟩
    exact ⟨hT2, hPara, ⟨hP, hsurj, hban, A⟩, rfl⟩
  · rintro ⟨hT2, hPara, Bd, rfl⟩
    exact ⟨hT2, hPara, Bd.continuous, Bd.surjective, Bd.banachable, Bd.atlas, rfl⟩

variable [T2Space Y] [ParacompactSpace Y] (Bd : StrongBundle PX P)

theorem filt_succ_left (m k : ℕ) : filtB Bd.atlas (m + 1) k ⊆ filtB Bd.atlas m k := by
  rintro y ⟨c, hc, hy, h1, h2⟩
  exact ⟨c, hc, hy, StrongBundle.range_toBase_mono _ (Nat.le_succ m) h1, h2⟩

theorem filt_succ_right (m k : ℕ) : filtB Bd.atlas m (k + 1) ⊆ filtB Bd.atlas m k := by
  rintro y ⟨c, hc, hy, h1, h2⟩
  exact ⟨c, hc, hy, h1, StrongBundle.range_toBase_mono _ (Nat.le_succ k) h2⟩

theorem oneSet_eq : Bd.oneSet = filtB Bd.atlas 0 1 := by
  ext y
  constructor
  · intro hy
    obtain ⟨c, hc, hyc⟩ := Bd.atlas.cover y
    exact ⟨c, hc, hyc, ⟨_, rfl⟩, hy c hc hyc⟩
  · rintro ⟨c, hc, hyc, -, h2⟩
    exact (Bd.mem_oneSet_iff hc hyc).2 h2

/-- `Y[0]_m = Y_{m,m}`. -/
theorem levelSet0_eq (m : ℕ) : Bd.toMPolyfold0.levelSet m = filtB Bd.atlas m m := by
  ext y
  constructor
  · intro hy
    obtain ⟨c, hc, hyc⟩ := Bd.atlas.cover y
    have h := (Bd.toMPolyfold0.mem_levelSet_iff (Bd.isChart_toMChart hc) hyc).1 hy
    obtain ⟨w, hw⟩ : ∃ w : (c.φ.model.E.prod c.F).lvl m,
        (c.φ.model.E.prod c.F).toBase m w = c y := h
    rw [ScBanach.prod_toBase] at hw
    exact ⟨c, hc, hyc, ⟨w.1, congrArg Prod.fst hw⟩, ⟨w.2, congrArg Prod.snd hw⟩⟩
  · rintro ⟨c, hc, hyc, ⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨c.toMChart Bd.continuous, Bd.isChart_toMChart hc, hyc, ⟨((a, b) :
      (c.φ.model.E.prod c.F).lvl m), ?_⟩⟩
    change (c.φ.model.E.prod c.F).toBase m (a, b) = c y
    rw [ScBanach.prod_toBase]
    exact Prod.ext ha hb

/-- `Y[1]_m = Y_{m,m+1}`, seen in `Y`. -/
theorem levelSet1_eq (m : ℕ) :
    Bd.oneVal '' Bd.toMPolyfold1.levelSet m = filtB Bd.atlas m (m + 1) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨c, hc, hyc⟩ := Bd.atlas.cover (Bd.oneVal z)
    have hzc : z ∈ (StrongBundle.oneChart hc z).source := hyc
    have h := (Bd.toMPolyfold1.mem_levelSet_iff (Bd.isChart_oneChart hc z) hzc).1 hz
    obtain ⟨w, hw⟩ : ∃ w : (c.φ.model.E.prod c.F.shift).lvl m,
        (c.φ.model.E.prod c.F.shift).toBase m w = c.liftOne (Bd.oneVal z) := h
    rw [ScBanach.prod_toBase] at hw
    have h1 : (c (Bd.oneVal z)).2 ∈ range (c.F.toBase 1) :=
      (Bd.mem_oneSet_iff hc hyc).1 (Bd.oneVal_mem z)
    have e := c.toBase_liftOne h1
    refine ⟨c, hc, hyc, ⟨w.1, ?_⟩, ⟨w.2, ?_⟩⟩
    · rw [← e, ← hw]
    · rw [← e, ← hw, ScBanach.shiftScale_toBase c.F.toScScale m w.2]
  · rintro ⟨c, hc, hyc, ⟨a, ha⟩, ⟨b, hb⟩⟩
    have h1 : (c y).2 ∈ range (c.F.toBase 1) :=
      StrongBundle.range_toBase_mono c.F (Nat.le_add_left 1 m) ⟨b, hb⟩
    have hy1 : y ∈ Bd.oneSet := (Bd.mem_oneSet_iff hc hyc).2 h1
    refine ⟨Bd.oneMk y hy1, ⟨StrongBundle.oneChart hc (Bd.oneMk y hy1),
      Bd.isChart_oneChart hc _, hyc, ⟨((a, b) : (c.φ.model.E.prod c.F.shift).lvl m), ?_⟩⟩, rfl⟩
    change (c.φ.model.E.prod c.F.shift).toBase m (a, b) = c.liftOne y
    rw [ScBanach.prod_toBase]
    refine Prod.ext ha ?_
    change c.F.shift.toBase m b = Function.invFun (c.F.toBase 1) (c y).2
    apply c.F.toBase_injective 1
    rw [Function.invFun_eq h1, ← hb, ScBanach.shiftScale_toBase c.F.toScScale m b]

end Parts

theorem A_to_Bpart : A5 → Bpart := by
  rintro ⟨-, hproj, hmem, -, hproj1⟩ X _ _ _ PX Y _ P _ _
  refine ⟨structure_iff, fun Bd => ⟨fun m k _ => filt_succ_left Bd m k,
    fun m k _ => filt_succ_right Bd m k, fun m k hk => ?_, oneSet_eq Bd,
    ⟨Bd.toMPolyfold0, rfl, levelSet0_eq Bd, hproj Bd⟩, levelSet1_eq Bd, hproj1 Bd⟩⟩
  ext y
  constructor
  · intro hy
    obtain ⟨c, hc, hyc⟩ := Bd.atlas.cover y
    exact ⟨c, hc, hyc, hy c hc hyc⟩
  · rintro ⟨c, hc, hyc, h⟩
    exact (hmem Bd hc hyc hk).2 h

section General

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The argument of `mem_doubleLevel_iff`, for two compatible strong bundle charts of an ARBITRARY
`P` (no continuity: the overlaps are retracts by `isScRetract_overlap'`, `isScRetract_overlap_one'`):
`Φ(y) ∈ K_{m,k}` implies `Φ'(y) ∈ K'_{m,k}`, `k ≤ m + 1`. -/
theorem inKB_of_compatible {c c' : StrongBundleChart PX P} (hcomp : c.Compatible c') {y : Y}
    (hy : y ∈ c.toPartialEquiv.source) (hy' : y ∈ c'.toPartialEquiv.source) {m k : ℕ}
    (hk : k ≤ m + 1) (h : InKB c m k y) : InKB c' m k y := by
  obtain ⟨h1, h2⟩ : (c y).1 ∈ range (c.φ.model.E.toBase m) ∧ (c y).2 ∈ range (c.F.toBase k) := h
  show (c' y).1 ∈ range (c'.φ.model.E.toBase m) ∧ (c' y).2 ∈ range (c'.F.toBase k)
  have hov : c y ∈ c.overlap c' := ⟨y, ⟨hy, hy'⟩, rfl⟩
  have htr : c.transition c' (c y) = c' y := c.transition_apply c' hy
  have hPy : P y ∈ c.φ.source := by rw [c.source_eq] at hy; exact hy
  have hPy' : P y ∈ c'.φ.source := by rw [c'.source_eq] at hy'; exact hy'
  refine ⟨?_, ?_⟩
  · -- the base component
    obtain ⟨w, hw⟩ := h1
    have hbase := (c.isChart.compatible c'.isChart (P := PX)).1
    have hwov : w ∈ c.φ.model.E.lvlSet (c.φ.overlap c'.φ) m := by
      rw [ScBanach.mem_lvlSet, hw, c.covers y hy]; exact ⟨P y, ⟨hPy, hPy'⟩, rfl⟩
    have := (hbase.isSc0 (c.φ.isScRetract_overlap c'.φ)).mem_range m w hwov
    rwa [hw, c.covers y hy, c.φ.transition_apply c'.φ hPy, ← c'.covers y hy'] at this
  · rcases Nat.lt_or_ge k (m + 1) with hkm | hkm
    · -- `k ≤ m`: the `[0]`-transition on level `k`
      have hkm' : k ≤ m := Nat.lt_succ_iff.1 hkm
      obtain ⟨w₁, hw₁⟩ := StrongBundle.range_toBase_mono c.φ.model.E hkm' h1
      obtain ⟨w₂, hw₂⟩ := h2
      have hw : (c.φ.model.E.prod c.F).toBase k (w₁, w₂) = c y := by
        rw [ScBanach.prod_toBase]; exact Prod.ext hw₁ hw₂
      have hwov : ((w₁, w₂) : (c.φ.model.E.prod c.F) k) ∈
          (c.φ.model.E.prod c.F).lvlSet (c.overlap c') k := by
        rw [ScBanach.mem_lvlSet, hw]; exact hov
      obtain ⟨v, hv⟩ := (hcomp.1.isSc0 (c.isScRetract_overlap' c')).mem_range k _ hwov
      rw [hw, htr, ScBanach.prod_toBase] at hv
      exact ⟨v.2, congrArg Prod.snd hv⟩
    · -- `k = m + 1`: the `[1]`-transition on level `m`
      have hk' : k = m + 1 := le_antisymm hk hkm
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
      obtain ⟨v, hv⟩ := (hcomp.2.2.1.isSc0 (c.isScRetract_overlap_one' c')).mem_range m _ hwov
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

/-- (c) for an arbitrary `P`: charts of equivalent atlases are compatible
(`StrongBundleAtlas.equiv_iff`), then `inKB_of_compatible` both ways. -/
theorem Bc_general : ∀ A A' : StrongBundleAtlas PX P, A.Equiv A' →
    ∀ c ∈ A.charts, ∀ c' ∈ A'.charts, ∀ y : Y,
      y ∈ c.toPartialEquiv.source → y ∈ c'.toPartialEquiv.source →
      ∀ m k : ℕ, k ≤ m + 1 → (InKB c m k y ↔ InKB c' m k y) := by
  intro A A' h c hc c' hc' y hy hy' m k hk
  have hcomp := (StrongBundleAtlas.equiv_iff A A').1 h c hc c' hc'
  exact ⟨inKB_of_compatible hcomp hy hy' hk, inKB_of_compatible hcomp.symm hy' hy hk⟩

end General

/-- `A → B` (core): (b), (d)–(f) from `A` (`A_to_Bpart`); (a) from the project's
`StrongBundleAtlas.equivalence`; (c) from `Bc_general`. -/
theorem A_to_B_core : A5 → B := by
  intro hA X _ _ _ PX Y _ P _ _
  obtain ⟨hb, hrest⟩ := A_to_Bpart hA PX P
  exact ⟨StrongBundleAtlas.equivalence, hb, Bc_general, hrest⟩

theorem A_to_B : A → B := fun hA =>
  A_to_B_core ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1⟩

/-- The part of `A` that B gives. -/
def Apart : Prop :=
  (type_of% @Polyfold.StrongBundle.isScSmoothMap_proj.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.mem_doubleLevel_iff.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.isScSmoothMap_proj1.{0, 0})

theorem B_to_Apart : B → Apart := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro X _ _ _ PX Y _ P _ _ _ _ Bd
    obtain ⟨-, -, -, hd⟩ := hB PX P
    obtain ⟨-, -, -, -, ⟨Q, hQ, -, hs⟩, -⟩ := hd Bd
    obtain ⟨⟨ch, hcomp, hcov⟩⟩ := Q
    change ch = Bd.atlas0.charts at hQ
    subst hQ
    exact hs
  · intro X _ _ _ PX Y _ P _ _ _ _ Bd c hc y hy m k hk
    obtain ⟨hequiv, -, hind, hd⟩ := hB PX P
    obtain ⟨-, -, hdl, -⟩ := hd Bd
    rw [hdl m k hk]
    constructor
    · rintro ⟨c', hc', hyc', h⟩
      exact (hind Bd.atlas Bd.atlas (hequiv.refl _) c hc c' hc' y hy hyc' m k hk).2 h
    · intro h
      exact ⟨c, hc, hy, h⟩
  · intro X _ _ _ PX Y _ P _ _ _ _ Bd
    obtain ⟨-, -, -, hd⟩ := hB PX P
    exact (hd Bd).2.2.2.2.2.2

/-- Four of the five added conjuncts of `A`: `isChart_congr` from B's (a) (transitivity), the
others from the unbanned project lemmas `StrongBundleAtlas.equiv_iff`,
`StrongBundleChart.compatible_of_locally`, `StrongBundleChart.Compatible.restrict_left` (not from
B).  The fifth, `maximalAtlas_equiv`, follows from `equiv_iff` by definition, but its statement names
`maximalAtlas`, whose body contains the banned `IsChart.compatible`, so no proof of it can pass
`#rt_check`; it is left out. -/
def Anew4 : Prop :=
  (type_of% @Polyfold.StrongBundle.isChart_iff_exists_equiv.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.isChart_congr.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.IsChart.compatible.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.IsChart.restrict.{0, 0})

section MaxAtlas

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The charts of `Bd` form an atlas (locality of compatibility); a copy of `maximalAtlas` built
from `StrongBundleChart.compatible_of_locally`. -/
noncomputable def maxAtlas' (Bd : StrongBundle PX P) : StrongBundleAtlas PX P where
  charts := {c | Bd.IsChart c}
  compatible c hc c' hc' := StrongBundleChart.compatible_of_locally c c' Bd.atlas.charts hc
    (fun χ hχ => (hc' χ hχ).symm) fun y _ => Bd.atlas.cover y
  cover y := by
    obtain ⟨c, hc, hy⟩ := Bd.atlas.cover y
    exact ⟨c, Bd.isChart_of_mem hc, hy⟩

end MaxAtlas

theorem B_to_Anew4 : B → Anew4 := by
  intro hB
  have hiff : type_of% @Polyfold.StrongBundle.isChart_iff_exists_equiv.{0, 0} := by
    intro X _ _ _ PX Y _ _ _ P _ _ Bd c
    constructor
    · intro hc
      exact ⟨maxAtlas' Bd, (StrongBundleAtlas.equiv_iff _ _).2 fun _ hc c' hc' => hc c' hc', hc⟩
    · rintro ⟨A, hA, hcA⟩ c' hc'
      exact (StrongBundleAtlas.equiv_iff A Bd.atlas).1 hA c hcA c' hc'
  refine ⟨hiff, ?_, ?_, ?_⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ Bd Bd' h c
    have hE := (hB PX P).1
    constructor
    · intro hc
      obtain ⟨A, hA, hcA⟩ := (hiff c).1 hc
      exact (hiff c).2 ⟨A, hE.trans hA h, hcA⟩
    · intro hc
      obtain ⟨A, hA, hcA⟩ := (hiff c).1 hc
      exact (hiff c).2 ⟨A, hE.trans hA (hE.symm h), hcA⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ Bd c c' hc hc'
    exact StrongBundleChart.compatible_of_locally c c' Bd.atlas.charts hc
      (fun χ hχ => (hc' χ hχ).symm) fun y _ => Bd.atlas.cover y
  · intro X _ _ _ PX Y _ _ _ P _ _ Bd c hc s hs hso c' hc'
    exact (hc c' hc').restrict_left hs hso

#rt_check_soft RoundTrip.V2_58.A_to_B_core [Polyfold.StrongBundleChart.Compatible.toMChart,
  Polyfold.StrongBundle.isScSmoothMap_proj, Polyfold.StrongBundle.mem_doubleLevel_iff,
  Polyfold.StrongBundle.oneChart_compatible, Polyfold.StrongBundle.isScSmoothMap_proj1,
  Polyfold.StrongBundle.maximalAtlas_equiv, Polyfold.StrongBundle.isChart_iff_exists_equiv,
  Polyfold.StrongBundle.isChart_congr, Polyfold.StrongBundle.IsChart.compatible,
  Polyfold.StrongBundle.IsChart.restrict]
#rt_check_soft RoundTrip.V2_58.B_to_Apart [Polyfold.StrongBundleChart.Compatible.toMChart,
  Polyfold.StrongBundle.isScSmoothMap_proj, Polyfold.StrongBundle.mem_doubleLevel_iff,
  Polyfold.StrongBundle.oneChart_compatible, Polyfold.StrongBundle.isScSmoothMap_proj1,
  Polyfold.StrongBundle.maximalAtlas_equiv, Polyfold.StrongBundle.isChart_iff_exists_equiv,
  Polyfold.StrongBundle.isChart_congr, Polyfold.StrongBundle.IsChart.compatible,
  Polyfold.StrongBundle.IsChart.restrict]
#rt_check_soft RoundTrip.V2_58.B_to_Anew4 [Polyfold.StrongBundleChart.Compatible.toMChart,
  Polyfold.StrongBundle.isScSmoothMap_proj, Polyfold.StrongBundle.mem_doubleLevel_iff,
  Polyfold.StrongBundle.oneChart_compatible, Polyfold.StrongBundle.isScSmoothMap_proj1,
  Polyfold.StrongBundle.maximalAtlas_equiv, Polyfold.StrongBundle.isChart_iff_exists_equiv,
  Polyfold.StrongBundle.isChart_congr, Polyfold.StrongBundle.IsChart.compatible,
  Polyfold.StrongBundle.IsChart.restrict]

end RoundTrip.V2_58
