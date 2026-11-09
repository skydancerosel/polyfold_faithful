import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_4

/-! Round trip for V5_4 (Lemma 5.2: local comparison of an auxiliary norm with `|·|₁`).

A = `lemma_5_1_2` ∧ `exists_le_mul_norm_liftOne` ∧ `IsAuxNorm.exists_norm_liftOne_le` ∧
`IsAuxNorm.exists_bounds` ∧ `lemma_5_1_2_literal` (universes at `0`; refreshed 2026-11-02:
`lemma_5_1_2_literal` is new in the comparison row).

`lemma_5_1_2_literal` is B itself (B's `fiberNormOne c y` is `‖(c.liftOne y).2‖` by definition;
`B_gives_lemma_5_2_literal`).  The only difference between `lemma_5_1_2` and B: in condition (ii),
A asks for the bounds on a neighbourhood `V ⊆ dom φ` of `x`, B on the whole domain `V = dom φ` of
the chart.  Passing from that form to B's needs a strong bundle chart with a smaller domain; when
this item was first audited the project had no restriction of strong bundle charts, so one is built
here (`StrongBundleChart'.restr`, restriction of the base chart to `dom φ ∩ φ⁻¹(G)`, `G` open, with
the strong bundle retraction restricted to `(U ∩ r⁻¹(G) ∩ G) ◁ F`), with `Compatible.restr` — pure
glue.  (The project now has `StrongBundleChart.restrict`, used by `lemma_5_1_2_literal`.)  `A_to_B`
still goes through `lemma_5_1_2` and this glue. -/

namespace RoundTrip.V5_4
open Polyfold Set Function Filter Topology

/-- The project's statement, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.lemma_5_1_2.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.exists_le_mul_norm_liftOne.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.IsAuxNorm.exists_norm_liftOne_le.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.IsAuxNorm.exists_bounds.{0, 0} ∧
  type_of% @Polyfold.lemma_5_1_2_literal.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.lemma_5_1_2.{0, 0}, @Polyfold.StrongBundle.exists_le_mul_norm_liftOne.{0, 0},
    @Polyfold.StrongBundle.IsAuxNorm.exists_norm_liftOne_le.{0, 0},
    @Polyfold.StrongBundle.IsAuxNorm.exists_bounds.{0, 0}, @Polyfold.lemma_5_1_2_literal.{0, 0}⟩

/-! ### Glue: restricting a strong bundle chart to `dom φ ∩ φ⁻¹(G)` -/

section Restr

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundleChart'

variable (c : StrongBundleChart PX P) {G : Set (c.φ.model.E 0)} (hG : IsOpen G)

/-- The new base domain `V ∩ φ⁻¹(G)`. -/
def rSource (G : Set (c.φ.model.E 0)) : Set X := c.φ.source ∩ c.φ ⁻¹' G

lemma rSource_subset : rSource c G ⊆ c.φ.source := inter_subset_left

include hG in
lemma isOpen_rSource : IsOpen (rSource c G) :=
  c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source hG

lemma image_rSource : c.φ '' rSource c G = c.φ.model.O ∩ G := by
  rw [rSource, image_inter_preimage, c.φ.image_source]

/-- The base retraction restricted to `U ∩ r⁻¹(G) ∩ G`. -/
abbrev rBaseR : ScRetraction c.φ.model.E c.φ.model.C :=
  (c.isRetraction.baseRetraction c.relOpen).restrictIn hG

lemma rBaseR_retract : (rBaseR c hG).retract = c.φ.model.O ∩ G := by
  rw [ScRetraction.restrictIn_retract, c.base_retract]

lemma r_mem_target {y : Y} (hy : P y ∈ rSource c G) :
    c y ∈ c.R '' ((rBaseR c hG).U ×ˢ univ) := by
  have hys : y ∈ c.toPartialEquiv.source := (c.mem_source_iff').2 hy.1
  have hK := c.apply_mem_K' hys
  have h1 : (c y).1 ∈ (rBaseR c hG).retract := by
    rw [rBaseR_retract, c.covers y hys]
    exact ⟨c.φ.mapsTo_model _ hy.1, hy.2⟩
  exact ⟨c y, ⟨(rBaseR c hG).retract_subset h1, mem_univ _⟩, c.R_apply_of_mem_K hK⟩

lemma r_mem_K {p : c.φ.model.E 0 × c.F 0} (hp : p ∈ c.R '' ((rBaseR c hG).U ×ˢ univ)) :
    p ∈ c.K ∧ p.1 ∈ G := by
  obtain ⟨q, hq, rfl⟩ := hp
  have hqU : q ∈ (rBaseR c hG).U ×ˢ (univ : Set (c.F 0)) := hq
  refine ⟨⟨q, ⟨hqU.1.1.1, mem_univ _⟩, rfl⟩, ?_⟩
  have := ((c.isRetraction.restrictIn c.relOpen hG).mapsTo hqU).1
  exact (c.isRetraction.baseRetraction c.relOpen).restrictIn_U_subset hG this

/-- The restricted bundle chart `Φ|P⁻¹(V ∩ φ⁻¹(G))`. -/
def rPE : PartialEquiv Y (c.φ.model.E 0 × c.F 0) where
  toFun y := c y
  invFun p := c.toPartialEquiv.symm p
  source := P ⁻¹' rSource c G
  target := c.R '' ((rBaseR c hG).U ×ˢ univ)
  map_source' y hy := r_mem_target c hG hy
  map_target' p hp := by
    obtain ⟨hK, hGp⟩ := r_mem_K c hG hp
    have hK' : p ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hK
    have hs := c.toPartialEquiv.map_target hK'
    refine ⟨(c.mem_source_iff').1 hs, ?_⟩
    change c.φ (P (c.toPartialEquiv.symm p)) ∈ G
    rw [← c.covers _ hs, c.toPartialEquiv.right_inv hK']
    exact hGp
  left_inv' y hy := c.toPartialEquiv.left_inv ((c.mem_source_iff').2 hy.1)
  right_inv' p hp := by
    obtain ⟨hK, -⟩ := r_mem_K c hG hp
    have hK' : p ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hK
    exact c.toPartialEquiv.right_inv hK'

/-- **The restriction of a strong bundle chart** to `P⁻¹(V ∩ φ⁻¹(G))`, `G` open. -/
def restr : StrongBundleChart PX P where
  φ := c.φ.restrict (rSource_subset c) (isOpen_rSource c hG)
  isChart := MPolyfold.IsChart.restrict PX c.isChart (rSource_subset c) (isOpen_rSource c hG)
  F := c.F
  U := (rBaseR c hG).U
  R := c.R
  relOpen := (rBaseR c hG).relOpen
  isRetraction := c.isRetraction.restrictIn c.relOpen hG
  base_retract :=
    (IsStrongBundleRetraction.restrictIn_base_retract c.relOpen c.isRetraction hG).trans (by
      rw [c.base_retract]; exact (image_rSource c).symm)
  toPartialEquiv := rPE c hG
  source_eq := rfl
  target_eq := rfl
  continuousOn_toFun := c.continuousOn_toFun.mono fun y hy => (c.mem_source_iff').2 hy.1
  continuousOn_invFun := c.continuousOn_invFun.mono fun p hp => by
    rw [c.target_eq]; exact (r_mem_K c hG hp).1
  covers y hy := c.covers y ((c.mem_source_iff').2 hy.1)
  fiber_linear x hx := c.fiber_linear x hx.1

lemma restr_φ_source : (restr c hG).φ.source = rSource c G := rfl

lemma mem_restr_source_iff {y : Y} :
    y ∈ (restr c hG).toPartialEquiv.source ↔
      y ∈ c.toPartialEquiv.source ∧ (c y).1 ∈ G := by
  constructor
  · intro hy
    have hys := (c.mem_source_iff').2 hy.1
    exact ⟨hys, by rw [c.covers y hys]; exact hy.2⟩
  · rintro ⟨hys, hGy⟩
    refine ⟨(c.mem_source_iff').1 hys, ?_⟩
    change c.φ (P y) ∈ G
    rw [← c.covers y hys]; exact hGy

variable (c'' : StrongBundleChart PX P)

lemma restr_overlap : (restr c hG).overlap c'' = c.overlap c'' ∩ (G ×ˢ univ) := by
  ext k
  constructor
  · rintro ⟨y, ⟨hy', hy''⟩, rfl⟩
    have := (mem_restr_source_iff c hG).1 hy'
    exact ⟨⟨y, ⟨this.1, hy''⟩, rfl⟩, this.2, mem_univ _⟩
  · rintro ⟨⟨y, ⟨hy, hy''⟩, rfl⟩, hGk, -⟩
    exact ⟨y, ⟨(mem_restr_source_iff c hG).2 ⟨hy, hGk⟩, hy''⟩, rfl⟩

lemma mem_overlap_restr_iff {k : c''.φ.model.E 0 × c''.F 0} :
    k ∈ c''.overlap (restr c hG) ↔ k ∈ c''.overlap c ∧ (c''.transition c k).1 ∈ G := by
  constructor
  · rintro ⟨y, ⟨hy'', hy'⟩, rfl⟩
    have := (mem_restr_source_iff c hG).1 hy'
    refine ⟨⟨y, ⟨hy'', this.1⟩, rfl⟩, ?_⟩
    rw [c''.transition_apply c hy'']; exact this.2
  · rintro ⟨⟨y, ⟨hy'', hy⟩, rfl⟩, hGk⟩
    rw [c''.transition_apply c hy''] at hGk
    exact ⟨y, ⟨hy'', (mem_restr_source_iff c hG).2 ⟨hy, hGk⟩⟩, rfl⟩

lemma overlap_restr_eq (hP : Continuous P) :
    ∃ Wo, IsOpen Wo ∧ c''.overlap (restr c hG) = c''.overlap c ∩ Wo := by
  obtain ⟨Wo, hWo, hWoeq⟩ := (c''.toMChart hP).exists_isOpen_image_eq
    (s := c''.toPartialEquiv.source ∩ (restr c hG).toPartialEquiv.source)
    inter_subset_left ((c''.isOpen_source hP).inter ((restr c hG).isOpen_source hP))
  refine ⟨Wo, hWo, ?_⟩
  ext k
  constructor
  · intro hk
    refine ⟨((mem_overlap_restr_iff c hG c'').1 hk).1, ?_⟩
    have : k ∈ (c''.toMChart hP) '' (c''.toPartialEquiv.source ∩
        (restr c hG).toPartialEquiv.source) := hk
    rw [hWoeq] at this; exact this.2
  · rintro ⟨hk, hkW⟩
    have : k ∈ (c''.toMChart hP).model.O ∩ Wo := ⟨c''.overlap_subset_K c hk, hkW⟩
    rw [← hWoeq] at this; exact this

variable {c c''} in
/-- **Compatibility passes to the restricted chart.** -/
theorem compatible_restr (hP : Continuous P) (hcc : c.Compatible c'') :
    (restr c hG).Compatible c'' := by
  have hO := c.isScRetract_overlap c'' hP
  have hO1 := c.isScRetract_overlap_one c'' hP
  have hO'' := c''.isScRetract_overlap c hP
  have hO''1 := c''.isScRetract_overlap_one c hP
  obtain ⟨Wo, hWo, hWoeq⟩ := overlap_restr_eq c hG c'' hP
  have hov := restr_overlap c hG c''
  have hmapT : ∀ k ∈ c.overlap c'' ∩ (G ×ˢ univ),
      c.transition c'' k ∈ c''.overlap (restr c hG) := by
    rintro _ ⟨⟨y, ⟨hy, hy''⟩, rfl⟩, hG', -⟩
    rw [c.transition_apply c'' hy]
    exact ⟨y, ⟨hy'', (mem_restr_source_iff c hG).2 ⟨hy, hG'⟩⟩, rfl⟩
  have hmapT' : ∀ k ∈ c''.overlap (restr c hG),
      c''.transition c k ∈ c.overlap c'' ∩ (G ×ˢ univ) := by
    intro k hk
    obtain ⟨hk1, hkG⟩ := (mem_overlap_restr_iff c hG c'').1 hk
    obtain ⟨y, ⟨hy'', hy⟩, rfl⟩ := hk1
    rw [c''.transition_apply c hy''] at hkG ⊢
    exact ⟨⟨y, ⟨hy, hy''⟩, rfl⟩, hkG, mem_univ _⟩
  have hss1 : strongShiftOne (E := c.φ.model.E) (F := c.F) ((restr c hG).overlap c'') =
      strongShiftOne (c.overlap c'') ∩ (G ×ˢ univ) := by
    rw [hov]; ext p; exact ⟨fun h => ⟨h.1, h.2.1, mem_univ _⟩, fun h => ⟨h.1, h.2.1, mem_univ _⟩⟩
  have hss : strongShiftOne (c''.overlap (restr c hG)) =
      strongShiftOne (c''.overlap c) ∩ (c''.φ.model.E.prodShiftInclOp c''.F 0) ⁻¹' Wo := by
    rw [hWoeq]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show IsScSmoothRetractMap (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ)
      ((restr c hG).overlap c'') (c''.φ.model.E.prod c''.F) (c''.φ.model.C ×ˢ univ)
      (c''.overlap (restr c hG)) (c.transition c'')
    rw [hov]
    exact (hcc.1.restrict hO).mono_target hmapT
  · show IsScSmoothRetractMap (c''.φ.model.E.prod c''.F) (c''.φ.model.C ×ˢ univ)
      (c''.overlap (restr c hG)) (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ)
      ((restr c hG).overlap c'') (c''.transition c)
    rw [hov, hWoeq]
    exact (hcc.2.1.restrict hO'').mono_target (by rw [← hWoeq]; exact hmapT')
  · show IsScSmoothRetractMap (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
      (strongShiftOne (E := c.φ.model.E) (F := c.F) ((restr c hG).overlap c''))
      (c''.φ.model.E.prod c''.F.shift)
      (c''.φ.model.C ×ˢ univ) (strongShiftOne (c''.overlap (restr c hG)))
      (shiftFiber (c.transition c''))
    rw [hss1]
    refine (hcc.2.2.1.restrict hO1).mono_target fun p hp => ?_
    have hr := hcc.2.2.2.2.1 _ hp.1 ⟨p.2, rfl⟩
    change ((c.transition c'' (p.1, c.F.toBase 1 p.2)).1,
      c''.F.toBase 1 (Function.invFun (c''.F.toBase 1)
        (c.transition c'' (p.1, c.F.toBase 1 p.2)).2)) ∈ c''.overlap (restr c hG)
    rw [Function.invFun_eq hr]
    exact hmapT _ ⟨hp.1, hp.2.1, mem_univ _⟩
  · show IsScSmoothRetractMap (c''.φ.model.E.prod c''.F.shift) (c''.φ.model.C ×ˢ univ)
      (strongShiftOne (c''.overlap (restr c hG))) (c.φ.model.E.prod c.F.shift)
      (c.φ.model.C ×ˢ univ)
      (strongShiftOne (E := c.φ.model.E) (F := c.F) ((restr c hG).overlap c''))
      (shiftFiber (c''.transition c))
    rw [hss, hss1]
    refine (hcc.2.2.2.1.restrict hO''1).mono_target ?_
    rintro p ⟨hp, hpW⟩
    have hk : (p.1, c''.F.toBase 1 p.2) ∈ c''.overlap (restr c hG) := by
      rw [hWoeq]; exact ⟨hp, hpW⟩
    have hr := hcc.2.2.2.2.2 _ hp ⟨p.2, rfl⟩
    have hm := hmapT' _ hk
    refine ⟨?_, hm.2.1, mem_univ _⟩
    change ((c''.transition c (p.1, c''.F.toBase 1 p.2)).1,
      c.F.toBase 1 (Function.invFun (c.F.toBase 1)
        (c''.transition c (p.1, c''.F.toBase 1 p.2)).2)) ∈ c.overlap c''
    rw [Function.invFun_eq hr]
    exact hm.1
  · intro x hx hx2
    rw [hov] at hx
    exact hcc.2.2.2.2.1 x hx.1 hx2
  · intro x hx hx2
    exact hcc.2.2.2.2.2 x ((mem_overlap_restr_iff c hG c'').1 hx).1 hx2

end StrongBundleChart'

variable [T2Space Y] [ParacompactSpace Y]

open StrongBundleChart' in
/-- A chart of `P` restricted to `dom φ ∩ φ⁻¹(G)` is again a chart of `P`. -/
theorem isChart_restr {Bd : StrongBundle PX P} {c : StrongBundleChart PX P} (hc : Bd.IsChart c)
    {G : Set (c.φ.model.E 0)} (hG : IsOpen G) : Bd.IsChart (restr c hG) :=
  fun c'' hc'' => compatible_restr hG Bd.continuous (hc c'' hc'')

open StrongBundleChart' in
/-- **The shrinking step**: given a chart `c` of `P` and an open `V ∋ x` inside its base domain,
some chart `c'` of `P` around `x` has its base domain inside `V` and the same `|·|₁` as `c`. -/
theorem exists_restr {Bd : StrongBundle PX P} {c : StrongBundleChart PX P} (hc : Bd.IsChart c)
    {V : Set X} (hVo : IsOpen V) (hVc : V ⊆ c.φ.source) {x : X} (hxV : x ∈ V) :
    ∃ c' : StrongBundleChart PX P, Bd.IsChart c' ∧ x ∈ c'.φ.source ∧ c'.φ.source ⊆ V ∧
      ∀ y, fiberNormOne c' y = ‖(c.liftOne y).2‖ := by
  obtain ⟨W, hW, hWeq⟩ := c.φ.exists_isOpen_image_eq hVc hVo
  refine ⟨restr c hW, isChart_restr hc hW, ⟨hVc hxV, ?_⟩, ?_, fun y => rfl⟩
  · have : c.φ x ∈ c.φ '' V := ⟨x, hxV, rfl⟩
    rw [hWeq] at this; exact this.2
  · rintro z ⟨hz, hzW⟩
    have : c.φ z ∈ c.φ '' V := by rw [hWeq]; exact ⟨c.φ.mapsTo_model z hz, hzW⟩
    obtain ⟨v, hv, hveq⟩ := this
    rw [← c.φ.toPartialEquiv.injOn (hVc hv) hz hveq]; exact hv

end Restr

/-- `A ⇒ B`: `lemma_5_1_2` with its neighbourhood `V` shrunk to a chart domain (`exists_restr`) for
"⇒", and `V := dom φ` for "⇐". -/
theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd N hcont hfib
  have L := hA.1 (B := Bd) hcont hfib
  constructor
  · intro hN x
    obtain ⟨c, hc, V, hVo, hxV, hVc, a, A', ha, haA, hb⟩ := L.1 hN x
    obtain ⟨c', hc', hx', hsub, hnorm⟩ := exists_restr hc hVo hVc hxV
    exact ⟨c', hc', hx', a, A', ha, haA, fun w hw => by rw [hnorm]; exact hb w (hsub hw)⟩
  · intro H
    refine L.2 fun x => ?_
    obtain ⟨c, hc, hx, a, A', ha, haA, hb⟩ := H x
    exact ⟨c, hc, c.φ.source, c.φ.isOpen_source, hx, subset_rfl, a, A', ha, haA, hb⟩

/-! `B ⇒ A` is not proved.  B gives A's main conjunct `lemma_5_1_2` (`B_gives_lemma_5_2`, the same
glue backwards) and `lemma_5_1_2_literal` (`B_gives_lemma_5_2_literal`, B itself), but not the other
three: `exists_le_mul_norm_liftOne` is a statement about an
arbitrary `g : Y_{0,1} → ℝ` continuous at `0_x` and homogeneous on the fibres (not about auxiliary
norms), and `IsAuxNorm.exists_norm_liftOne_le`/`exists_bounds` give the bounds in EVERY strong
bundle chart around `x`, while B gives them in SOME chart; transferring them to another chart
needs the local comparison of the `|·|₁` of two charts, which is exactly the upper-bound argument
of `exists_le_mul_norm_liftOne` (continuity of `Φ'[1] ∘ Φ[1]⁻¹` at the zero section plus
homogeneity), i.e. re-proving the item's own lemma. -/

/-- B gives A's main conjunct, Lemma 5.2 itself. -/
theorem B_gives_lemma_5_2 (hB : B) : type_of% @Polyfold.lemma_5_1_2.{0, 0} := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd N hcont hfib
  have L := hB PX P Bd N hcont hfib
  constructor
  · intro hN x
    obtain ⟨c, hc, hx, a, A', ha, haA, hb⟩ := L.1 hN x
    exact ⟨c, hc, c.φ.source, c.φ.isOpen_source, hx, subset_rfl, a, A', ha, haA, hb⟩
  · intro H
    refine L.2 fun x => ?_
    obtain ⟨c, hc, V, hVo, hxV, hVc, a, A', ha, haA, hb⟩ := H x
    obtain ⟨c', hc', hx', hsub, hnorm⟩ := exists_restr hc hVo hVc hxV
    exact ⟨c', hc', hx', a, A', ha, haA, fun w hw => by rw [hnorm]; exact hb w (hsub hw)⟩

/-- B gives `lemma_5_1_2_literal`: it is B, up to unfolding `fiberNormOne`. -/
theorem B_gives_lemma_5_2_literal (hB : B) : type_of% @Polyfold.lemma_5_1_2_literal.{0, 0} := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd N hcont hfib
  exact hB PX P Bd N hcont hfib

#rt_check RoundTrip.V5_4.A_to_B [Polyfold.lemma_5_1_2,
  Polyfold.StrongBundle.exists_le_mul_norm_liftOne,
  Polyfold.StrongBundle.IsAuxNorm.exists_norm_liftOne_le, Polyfold.StrongBundle.IsAuxNorm.exists_bounds,
  Polyfold.lemma_5_1_2_literal]
#rt_check RoundTrip.V5_4.B_gives_lemma_5_2 [Polyfold.lemma_5_1_2,
  Polyfold.StrongBundle.exists_le_mul_norm_liftOne,
  Polyfold.StrongBundle.IsAuxNorm.exists_norm_liftOne_le, Polyfold.StrongBundle.IsAuxNorm.exists_bounds,
  Polyfold.lemma_5_1_2_literal]
#rt_check RoundTrip.V5_4.B_gives_lemma_5_2_literal [Polyfold.lemma_5_1_2,
  Polyfold.StrongBundle.exists_le_mul_norm_liftOne,
  Polyfold.StrongBundle.IsAuxNorm.exists_norm_liftOne_le, Polyfold.StrongBundle.IsAuxNorm.exists_bounds,
  Polyfold.lemma_5_1_2_literal]
#rt_overlap RoundTrip.V5_4.B_gives_lemma_5_2 [Polyfold.lemma_5_1_2,
  Polyfold.StrongBundle.exists_le_mul_norm_liftOne,
  Polyfold.StrongBundle.IsAuxNorm.exists_norm_liftOne_le, Polyfold.StrongBundle.IsAuxNorm.exists_bounds,
  Polyfold.lemma_5_1_2_literal]

end RoundTrip.V5_4
