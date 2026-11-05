import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_98_r2
import RoundTrip.Blind.V3_98

/-!
Round trip for V3_98 (Definition 6.1, Proposition 6.2; the index along the solution set and along
paths), against the second blind statement `RoundTrip.V3_98_r2.B` (2026-11-02).  `A` is the
conjunction of the types of the theorems among the current decls, universes at `0`:
`theorem_3_54_index_locally_constant`, `theorem_3_54_index`, `isSurjLinOfIndex_of_forall_dim`,
`theorem_3_54_index_locally_constant_sc`, `StrongBundle.linAt_isScFredholm`,
`index_locally_constant_of_admitsBumpFunctions`, `theorem_3_54_index_locally_constant_general`,
`index_locally_constant_tame`, `theorem_3_54_index_locally_constant_general_tame`,
`StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex`, `StrongBundle.IsIndexAt.unique`,
`StrongBundle.exists_isIndexAt`, `exists_isScPlusSection_pullback_of_path`,
`StrongBundle.isIndexAt_of_pullback_isLinOfIndex`, `proposition_6_2`,
`StrongBundle.IsIndexAtLocal.unique`, `StrongBundle.exists_isIndexAtLocal`,
`StrongBundle.isIndexAtLocal_iff_isIndexAt`, `proposition_6_2_local`, `proposition_6_2_local'`
(`StrongBundle.IsLinOfIndex`, `StrongBundle.IsIndexAt`, `StrongBundle.restrictOpen`,
`StrongBundle.IsIndexAtLocal` are vocabulary).

Neither direction is proved.

* `A → B`.  B's clauses (0) and (a) follow from `A` (`B0_of_A`, `Ba_of_A`, proved from the
  hypothesis `A`).  The glue: B's index `HasIndex` (every strong bundle chart `c` at `x`, every
  chart-level sc⁺-section `ŝ` with `ŝ(φx) = f̂(φx)`, the level-`0` algebraic index of
  `D((f̂ − ŝ) ∘ r)(z)|_{T_zO} : T_zO → K_z`) is obtained from the project's `IsIndexAtLocal`
  (`hasIndex_of_isIndexAtLocal`): `ŝ` is made an sc⁺-section of `P|dom φ` (`cutoffSection` with
  `β = 1` in the transported chart), `f|dom φ − s` is sc-Fredholm with a zero at `x`, its index in
  every chart is that of a germ datum (from `A`'s `linAt_isScFredholm`), so it is a local
  Definition 6.1 index, equal to the given one by `A`'s `IsIndexAtLocal.unique`.  `B`'s index is
  unique at smooth points (`hasIndex_unique`: `ŝ(z) = R(z, f̂(φx))₂` is a witness).
  B's clause (b) is not derived: B assumes only `IsScFredholmSection` (germ data in some chart)
  over a tame M-polyfold (`PX.IsTame`), while `proposition_6_2_local` needs tame germ data
  (`IsScFredholmSectionTame`), and the project has no lemma producing tame germ data from a tame
  base; and B's path `γ` is sc-smooth only near `[0, 1]` in B's sense (`C^∞` into every level in
  every chart), while `proposition_6_2_local` needs `(rnPolyfold 1).IsScSmoothMap PX φ` on all
  of `ℝ` (no project lemma turns level-wise `C^∞` into sc-smoothness, nor extends a path from
  `[0, 1]`).  Under those two added hypotheses `A` gives (b): `Bb_of_tame_global`.
* `B → A`.  `B` speaks only of the level-`0` index and its constancy; `A` also contains the
  sc-Fredholm property on every level (`linAt_isScFredholm`, `…_sc`, `…_general(_tame)`),
  surjectivity and `dim ker = d` under good position (`theorem_3_54_index`,
  `isSurjLinOfIndex_of_forall_dim`), the index of the parametrized section, the path device,
  the bump-function versions and the agreement of global and local Definition 6.1
  (`isIndexAtLocal_iff_isIndexAt`) — none of which `B` gives.

The results against the first blind statement (`RoundTrip/Blind/V3_98.lean`) are kept at the end
under names ending in `_r1`.
-/

namespace RoundTrip.V3_98
open Polyfold StrongRetr Set Module

/-- The project's statement, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_54_index_locally_constant.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_index.{0, 0} ∧
    type_of% @Polyfold.isSurjLinOfIndex_of_forall_dim.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_index_locally_constant_sc.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.linAt_isScFredholm.{0, 0} ∧
    type_of% @Polyfold.index_locally_constant_of_admitsBumpFunctions.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_index_locally_constant_general.{0, 0} ∧
    type_of% @Polyfold.index_locally_constant_tame.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_index_locally_constant_general_tame.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsIndexAt.unique.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.exists_isIndexAt.{0, 0} ∧
    type_of% @Polyfold.exists_isScPlusSection_pullback_of_path.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.isIndexAt_of_pullback_isLinOfIndex.{0, 0} ∧
    type_of% @Polyfold.proposition_6_2.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsIndexAtLocal.unique.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.exists_isIndexAtLocal.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.isIndexAtLocal_iff_isIndexAt.{0, 0} ∧
    type_of% @Polyfold.proposition_6_2_local.{0, 0} ∧
    type_of% @Polyfold.proposition_6_2_local'.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_54_index_locally_constant.{0, 0}, @Polyfold.theorem_3_54_index.{0, 0},
    @Polyfold.isSurjLinOfIndex_of_forall_dim.{0, 0},
    @Polyfold.theorem_3_54_index_locally_constant_sc.{0, 0},
    @Polyfold.StrongBundle.linAt_isScFredholm.{0, 0},
    @Polyfold.index_locally_constant_of_admitsBumpFunctions.{0, 0},
    @Polyfold.theorem_3_54_index_locally_constant_general.{0, 0},
    @Polyfold.index_locally_constant_tame.{0, 0},
    @Polyfold.theorem_3_54_index_locally_constant_general_tame.{0, 0},
    @Polyfold.StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex.{0, 0},
    @Polyfold.StrongBundle.IsIndexAt.unique.{0, 0}, @Polyfold.StrongBundle.exists_isIndexAt.{0, 0},
    @Polyfold.exists_isScPlusSection_pullback_of_path.{0, 0},
    @Polyfold.StrongBundle.isIndexAt_of_pullback_isLinOfIndex.{0, 0},
    @Polyfold.proposition_6_2.{0, 0}, @Polyfold.StrongBundle.IsIndexAtLocal.unique.{0, 0},
    @Polyfold.StrongBundle.exists_isIndexAtLocal.{0, 0},
    @Polyfold.StrongBundle.isIndexAtLocal_iff_isIndexAt.{0, 0},
    @Polyfold.proposition_6_2_local.{0, 0}, @Polyfold.proposition_6_2_local'.{0, 0}⟩

/-- The conjunct `StrongBundle.linAt_isScFredholm` of `A`. -/
abbrev LinFred : Prop := type_of% @Polyfold.StrongBundle.linAt_isScFredholm.{0, 0}

/-- The conjunct `StrongBundle.IsIndexAtLocal.unique` of `A`. -/
abbrev LocUniq : Prop := type_of% @Polyfold.StrongBundle.IsIndexAtLocal.unique.{0, 0}

section Glue
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

omit [T2Space Y] [ParacompactSpace Y] in
/-- B's chart index is unique. -/
lemma chartLinIndex_unique {c : StrongBundleChart PX P} {f : X → Y}
    {ŝ : c.φ.model.E 0 → c.F 0} {x : X} {i j : ℤ}
    (hi : V3_98_r2.ChartLinIndex c f ŝ x i) (hj : V3_98_r2.ChartLinIndex c f ŝ x j) : i = j := by
  obtain ⟨z, hz, K, hK, L, hL, hF⟩ := hi
  obtain ⟨z', hz', K', hK', L', hL', hF'⟩ := hj
  obtain rfl : z = z' := c.φ.model.E.toBase_injective 1 (hz.trans hz'.symm)
  obtain rfl : K = K' := SetLike.coe_injective (hK.trans hK'.symm)
  obtain rfl : L = L' := LinearMap.ext fun v => Subtype.ext ((hL v).trans (hL' v).symm)
  exact hF.2.2.symm.trans hF'.2.2

/-- **A witness for B's index**: at a smooth point `x`, in a chart `c` of the atlas, the chart-level
sc⁺-section `ŝ(z) = R(z, f̂(φx))₂` passes through `f̂(φx)`. -/
lemma exists_chartScPlus {Bd : StrongBundle PX P} {f : X → Y} (hf : Bd.IsScSmoothSection f)
    {x : X} (hx : x ∈ PX.smoothSet) {c : StrongBundleChart PX P} (hc : c ∈ Bd.atlas.charts)
    (hxc : x ∈ c.φ.source) :
    ∃ ŝ : c.φ.model.E 0 → c.F 0, V3_98_r2.IsChartScPlusSection c ŝ ∧
      ŝ (c.φ x) = c.principal f (c.φ x) := by
  have hR := c.isRetraction
  have hfs := hf.1
  have hPe : P (f x) ∈ c.φ.source := by rw [hfs x]; exact hxc
  have hes : f x ∈ c.toPartialEquiv.source := c.mem_source_of_proj hPe
  have he : f x ∈ Bd.toMPolyfold0.smoothSet :=
    mem_iInter.2 fun m => hf.2.mapsTo_levelSet m (mem_iInter.1 hx m)
  have hsm : (c (f x)).2 ∈ c.F.smooth := by
    refine c.F.mem_smooth_iff.2 fun m => ?_
    have hm : f x ∈ Bd.toMPolyfold0.levelSet m := mem_iInter.1 he m
    rw [Bd.toMPolyfold0.mem_levelSet_iff (Bd.isChart_toMChart hc) hes] at hm
    obtain ⟨w, hw⟩ := hm
    have h2 := ScBanach.prod_toBase c.φ.model.E c.F m w
    have h3 : c (f x) = _ := hw.symm.trans h2
    exact ⟨w.2, (congrArg Prod.snd h3).symm⟩
  set ê₁ : c.F 1 := Function.invFun (c.F.toBase 1) (c (f x)).2 with hê₁def
  have hê₁ : c.F.toBase 1 ê₁ = (c (f x)).2 := Function.invFun_eq (c.F.mem_smooth_iff.1 hsm 1)
  have hê₁s : ê₁ ∈ c.F.shift.smooth := by
    have h1 : ê₁ ∈ c.F.smoothLvl 1 := by
      change c.F.toBase 1 ê₁ ∈ c.F.smooth; rw [hê₁]; exact hsm
    rw [← c.F.shift_smoothLvl 0] at h1
    exact h1
  have hOU : ∀ z ∈ c.φ.model.O, z ∈ c.U := fun z hz =>
    (hR.baseRetraction c.relOpen).retract_subset (by rw [c.base_retract]; exact hz)
  have hU := c.relOpen.isScDomain
  refine ⟨fun z => (c.R (z, (c (f x)).2)).2, ⟨fun y hy => ?_, ?_⟩, ?_⟩
  · have hRy : c.R (y, (c (f x)).2) = (y, (c.R (y, (c (f x)).2)).2) := by
      refine Prod.ext ?_ rfl
      change (c.R (y, (c (f x)).2)).1 = y
      rw [hR.apply_fst (hOU y hy)]
      exact (hR.baseRetraction c.relOpen).apply_eq_self_of_mem_retract
        (by rw [c.base_retract]; exact hy)
    rw [← hRy]
    exact ⟨_, ⟨hOU y hy, mem_univ _⟩, rfl⟩
  · refine ⟨fun u => (shiftFiber c.R (StrongRetr.r c.R u, ê₁)).2, ?_, fun u hu => ?_⟩
    · have hr : IsScSmooth c.U (StrongRetr.r c.R) := r_isScSmooth c.relOpen hR
      have hpair := hr.scPair hU (isScSmooth_const_of_mem_smooth hU hê₁s)
      have hcomp := IsScSmooth.comp hU (c.relOpen.prod_univ c.F.shift).isScDomain
        hR.isScSmooth_one hpair fun u hu => ⟨hOU _ (c.r_mem_O hu), mem_univ _⟩
      exact hcomp.snd hU
    · change c.F.toBase 1 (shiftFiber c.R (StrongRetr.r c.R u, ê₁)).2 =
        (c.R (StrongRetr.r c.R u, (c (f x)).2)).2
      rw [hR.toBase_shiftFiber_snd (p := (StrongRetr.r c.R u, ê₁)) (hOU _ (c.r_mem_O hu)), hê₁]
  · have hRce : c.R (c (f x)) = c (f x) := by
      obtain ⟨q, hq, hqe⟩ : c (f x) ∈ c.K := by rw [← c.image_source]; exact ⟨f x, hes, rfl⟩
      rw [← hqe, hR.idem q hq]
    have hce : c (f x) = (c.φ x, (c (f x)).2) := Prod.ext (by rw [c.fst_apply hPe, hfs x]) rfl
    change (c.R (c.φ x, (c (f x)).2)).2 = (c (f (c.φ.symm (c.φ x)))).2
    rw [c.φ.symm_apply_apply hxc, ← hce, hRce]

/-- **B's index is unique at smooth points.** -/
lemma hasIndex_unique {Bd : StrongBundle PX P} {f : X → Y} (hf : Bd.IsScSmoothSection f)
    {x : X} (hx : x ∈ PX.smoothSet) {i j : ℤ} (hi : V3_98_r2.HasIndex Bd f x i)
    (hj : V3_98_r2.HasIndex Bd f x j) : i = j := by
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem Bd x
  obtain ⟨ŝ, hŝ, hŝx⟩ := exists_chartScPlus hf hx hc hxc
  exact chartLinIndex_unique (hi c (Bd.isChart_of_mem hc) hxc ŝ hŝ hŝx)
    (hj c (Bd.isChart_of_mem hc) hxc ŝ hŝ hŝx)

/-- **At a zero of an sc-Fredholm section the index exists** (from `A`'s `linAt_isScFredholm`):
it is `dim Pn − dim Q` of a germ datum, in every chart. -/
lemma exists_isLinOfIndex (hLin : LinFred) {Bd : StrongBundle PX P} {g : X → Y}
    (hg : Bd.IsScFredholmSection g) {y : X} (hy0 : IsZeroAt P g y) :
    ∃ j : ℤ, Bd.IsLinOfIndex g y j := by
  have hys : y ∈ PX.smoothSet := hg.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨-, c₁, hc₁, hyV₁, hφ₁, h0₁, g₁, s₁, hfill₁, hs₁, hs0₁, hconj₁⟩ := hg.germ y hys
  obtain ⟨d₁⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj₁
  refine ⟨finrank ℝ d₁.Pn - finrank ℝ d₁.Q, fun c' hc' hyc' z hz hzU L hL => ?_⟩
  obtain ⟨hD, hT, hK, hTK, -, -, hlvl⟩ := hLin hg hy0 hc' hyc' hz hzU
  obtain ⟨hF0, -, hdat⟩ := hlvl 0
  have hd := hdat c₁ hc₁ hyV₁ hφ₁ h0₁ g₁ s₁ hfill₁ hs₁ hs0₁ d₁
  obtain ⟨hiff, hidx⟩ := hD.toScOperator.isFredholm_restrict_zero_iff hT hK hTK (L := L)
    (fun v => by rw [hL, hD.toScOperator_zero]; rfl)
  exact ⟨hiff.1 hF0, (hidx hF0).trans hd⟩

/-- `IsLinOfIndex` is unique at a zero (from `A`'s `linAt_isScFredholm`). -/
lemma isLinOfIndex_unique (hLin : LinFred) {Bd : StrongBundle PX P} {g : X → Y}
    (hg : Bd.IsScFredholmSection g) {y : X} (hy0 : IsZeroAt P g y) {i j : ℤ}
    (hi : Bd.IsLinOfIndex g y i) (hj : Bd.IsLinOfIndex g y j) : i = j := by
  obtain ⟨c, hc, hyc⟩ := StrongBundle.exists_chart_mem Bd y
  have hc' := Bd.isChart_of_mem hc
  have hys : y ∈ PX.smoothSet := hg.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨z, hz⟩ := (PX.mem_levelSet_iff c.isChart hyc).1 (mem_iInter.1 hys 1)
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := by
    rw [hz]
    exact StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ c.φ.mapsTo_model y hyc)
  obtain ⟨hD, hT, hK, hTK, -, -, -⟩ := hLin hg hy0 hc' hyc hz hzU
  have hmem : ∀ v : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal g) z v ∈ rangeS (ρCLM c.isRetraction hzU) := fun v => by
    have := hTK v v.2
    rwa [hD.toScOperator_zero] at this
  have h1 := hi c hc' hyc z hz hzU ((linAt c.U c.R (c.principal g) z).codRestrict _ hmem)
    fun _ => rfl
  have h2 := hj c hc' hyc z hz hzU ((linAt c.U c.R (c.principal g) z).codRestrict _ hmem)
    fun _ => rfl
  exact h1.2.symm.trans h2.2

set_option maxHeartbeats 1000000 in
/-- **From the project's local Definition 6.1 to B's index** (from `A`'s `linAt_isScFredholm`
and `IsIndexAtLocal.unique`). -/
theorem hasIndex_of_isIndexAtLocal (hLin : LinFred) (hUniq : LocUniq) {Bd : StrongBundle PX P}
    {f : X → Y} (hf : Bd.IsScFredholmSection f) {x : X} {i : ℤ}
    (hi : Bd.IsIndexAtLocal f x i) : V3_98_r2.HasIndex Bd f x i := by
  intro c hc hxc ŝ hŝ hŝx
  obtain ⟨hŝK, σ, hσ, hσŝ⟩ := hŝ
  have hV : IsOpen c.φ.source := c.φ.isOpen_source
  haveI : Nonempty c.φ.source := ⟨⟨x, hxc⟩⟩
  haveI := PX.paracompactSpace_subtype c.φ.source
  haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : c.φ.source → X))
    (PX.restrictOpen hV) Bd
  have hfs : IsSection P f := hf.isScSmooth.1
  set fV := restrictSection P c.φ.source f hfs with hfVdef
  have hfV : (Bd.restrictOpen hV).IsScFredholmSection fV := hf.restrictOpen hV
  set x' : c.φ.source := ⟨x, hxc⟩ with hx'def
  set cV := c.restrictTo Bd.continuous hV subset_rfl (fV x') with hcVdef
  have hcV : (Bd.restrictOpen hV).IsChart cV :=
    StrongBundle.restrictOpen_isChart_restrictTo hV hc subset_rfl _
  have hR := c.isRetraction
  have hOU : ∀ z ∈ c.φ.model.O, z ∈ c.U := fun z hz =>
    (hR.baseRetraction c.relOpen).retract_subset (by rw [c.base_retract]; exact hz)
  have hσO : ∀ z ∈ c.φ.model.O, c.F.toBase 1 (σ z) = ŝ z := fun z hz => by
    have h := hσŝ z (hOU z hz)
    rw [StrongRetr.r_eq_self hR (by rw [c.r_image]; exact hz)] at h
    exact h
  -- `ŝ` as an sc⁺-section of `P|dom φ`
  have hτ : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O
      (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c.K)
      (fun z => (z, σ z)) := by
    refine ⟨fun z hz => ?_, fun R' hR' => ?_⟩
    · change (z, c.F.toBase 1 (σ z)) ∈ c.K
      rw [hσO z hz]; exact hŝK z hz
    · have hU' := R'.isScDomain
      have hRO : ∀ u ∈ R'.U, R' u ∈ c.φ.model.O := fun u hu => hR' ▸ R'.apply_mem_retract hu
      have h1 := IsScSmooth.comp hU' c.relOpen.isScDomain hσ R'.isScSmooth
        fun u hu => hOU _ (hRO u hu)
      exact R'.isScSmooth.scPair hU' h1
  set s₀ := StrongBundle.cutoffSection cV (fun _ => (1 : ℝ)) σ with hs₀def
  have hs₀ : (Bd.restrictOpen hV).IsScPlusSection s₀ :=
    StrongBundle.isScPlusSection_cutoffSection_of_isChart hcV (isScSmoothMap_real_const 1)
      (fun v _ => v.2) hτ
  set s := sectionSmul (pullbackProj P (Subtype.val : c.φ.source → X)) (fun _ => (-1 : ℝ)) s₀
    with hsdef
  have hs : (Bd.restrictOpen hV).IsScPlusSection s :=
    hs₀.smul_left (isScSmoothMap_real_const (-1))
  set g := sectionAdd (pullbackProj P (Subtype.val : c.φ.source → X)) fV s with hgdef
  have hg : (Bd.restrictOpen hV).IsScFredholmSection g := theorem_3_15 hfV hs
  have hprin : ∀ z ∈ c.φ.model.O, cV.principal g z = c.principal f z - ŝ z := fun z hz => by
    have h0 : cV.principal s₀ z = ŝ z := by
      unfold StrongBundleChart.principal
      rw [StrongBundle.apply_cutoffSection (c := cV) (β := fun _ => (1 : ℝ)) hτ.mapsTo
        (cV.φ.symm_mapsTo hz)]
      change c.F.toBase 1 ((1 : ℝ) • σ (cV.φ (cV.φ.symm z))) = ŝ z
      rw [cV.φ.apply_symm_apply hz, one_smul, hσO z hz]
    rw [cV.principal_sectionAdd hfV.isScSmooth.1 hs.1 hz, principal_sectionSmul cV hs₀.1 _ hz,
      StrongBundleChart.principal_restrictTo hV Bd.continuous subset_rfl _ hfs hz, h0]
    change c.principal f z + (-1 : ℝ) • ŝ z = c.principal f z - ŝ z
    rw [neg_one_smul, ← sub_eq_add_neg]
  have hzero : IsZeroAt (pullbackProj P (Subtype.val : c.φ.source → X)) g x' := by
    rw [cV.isZeroAt_iff hg.isScSmooth.1 (show x' ∈ cV.φ.source from hxc)]
    change cV.principal g (c.φ x) = 0
    rw [hprin _ (c.φ.mapsTo_model x hxc)]
    exact sub_eq_zero.2 hŝx.symm
  -- its index is a local Definition 6.1 index, hence `i`
  obtain ⟨j, hj⟩ := exists_isLinOfIndex hLin hg hzero
  have hjloc : Bd.IsIndexAtLocal f x j := ⟨hfs, c.φ.source, hV, hxc, s, hs, hzero, hj⟩
  obtain rfl : j = i := hUniq hf hjloc hi
  -- read it in the chart `c`
  have hxs' : x' ∈ (PX.restrictOpen hV).smoothSet := hg.mem_smoothSet_of_isZeroAt hzero
  set z : c.φ.model.E 1 := MPolyfold.levelLift cV.φ 1 x' with hzdef
  have hz : c.φ.model.E.toBase 1 z = c.φ x :=
    (PX.restrictOpen hV).toBase_levelLift (MPolyfold.isChart_restrictTo hV c.isChart subset_rfl)
      hxc (mem_iInter.1 hxs' 1)
  have hzO : c.φ.model.E.toBase 1 z ∈ StrongRetr.r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model x hxc
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := StrongRetr.mem_U_of_mem_O hR hzO
  obtain ⟨hD, -, -, hTK, -, -, -⟩ := hLin hg hzero hcV hxc hz hzU
  have hmem : ∀ v : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (cV.principal g) z v ∈ rangeS (ρCLM c.isRetraction hzU) := fun v => by
    have := hTK v.1 v.2
    rwa [hD.toScOperator_zero] at this
  set L := (linAt c.U c.R (cV.principal g) z).codRestrict _ hmem with hLdef
  obtain ⟨hLF, hLi⟩ := hj cV hcV hxc z hz hzU L fun _ => rfl
  have hgr : IsScSmooth c.U (cV.principal g ∘ StrongRetr.r c.R) := by
    have h1 := (hg.isScSmooth.isScSmoothRetractMap hcV).comp_isScSmooth
      (c.isRetraction.baseRetraction c.relOpen) c.base_retract
    exact (h1.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl
  have hgr' : IsScSmooth c.U ((fun y => c.principal f y - ŝ y) ∘ StrongRetr.r c.R) :=
    hgr.congr c.relOpen.isScDomain fun u hu => hprin _ (c.r_mem_O hu)
  have hFin := Polyfold.IsFredholm.hasFiniteIndex hLF
  refine ⟨z, hz, rangeS (ρCLM c.isRetraction hzU), ?_, L.toLinearMap, fun v => ?_, ?_⟩
  · ext h
    rw [SetLike.mem_coe, mem_rangeS_ρCLM_iff c.isRetraction hzO hzU, hz]
    rfl
  · change linAt c.U c.R (cV.principal g) z v =
      scDeriv c.U ((fun y => c.principal f y - ŝ y) ∘ StrongRetr.r c.R) z v
    exact linAt_congr c.relOpen hgr.isSc1 hgr'.isSc1 (fun u hu => hprin u (c.r_image ▸ hu))
      (show c.φ.model.E.toBase 1 z ∈ c.U from hzU) v
  · exact ⟨hFin.finite_ker, hFin.finite_coker, hLi⟩

/-- **At a zero, the project's `IsLinOfIndex` gives the local Definition 6.1 index** (from `A`'s
`linAt_isScFredholm`; the zero section on `P|dom φ`). -/
theorem isIndexAtLocal_of_isLinOfIndex (hLin : LinFred) {Bd : StrongBundle PX P} {f : X → Y}
    (hf : Bd.IsScFredholmSection f) {y : X} (hy0 : IsZeroAt P f y) {i : ℤ}
    (hi : Bd.IsLinOfIndex f y i) : Bd.IsIndexAtLocal f y i := by
  obtain ⟨c, hcm, hyc⟩ := StrongBundle.exists_chart_mem Bd y
  have hc := Bd.isChart_of_mem hcm
  have hV : IsOpen c.φ.source := c.φ.isOpen_source
  haveI : Nonempty c.φ.source := ⟨⟨y, hyc⟩⟩
  haveI := PX.paracompactSpace_subtype c.φ.source
  haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : c.φ.source → X))
    (PX.restrictOpen hV) Bd
  have hfs : IsSection P f := hf.isScSmooth.1
  set fV := restrictSection P c.φ.source f hfs with hfVdef
  have hfV : (Bd.restrictOpen hV).IsScFredholmSection fV := hf.restrictOpen hV
  set y' : c.φ.source := ⟨y, hyc⟩ with hy'def
  have hy0' : IsZeroAt (pullbackProj P (Subtype.val : c.φ.source → X)) fV y' :=
    (isZeroAt_restrictSection_iff' hfs y').2 hy0
  obtain ⟨j, hj⟩ := exists_isLinOfIndex hLin hfV hy0'
  suffices hij : i = j by
    subst hij
    refine ⟨hfs, c.φ.source, hV, hyc, fiberZero _, StrongBundle.isScPlusSection_fiberZero, ?_, ?_⟩
    · rw [sectionAdd_fiberZero (isSection_restrictSection hfs)]; exact hy0'
    · rw [sectionAdd_fiberZero (isSection_restrictSection hfs)]; exact hj
  -- compare in `c` and its transport `cV`
  set cV := c.restrictTo Bd.continuous hV subset_rfl (fV y') with hcVdef
  have hcV : (Bd.restrictOpen hV).IsChart cV :=
    StrongBundle.restrictOpen_isChart_restrictTo hV hc subset_rfl _
  have hR := c.isRetraction
  have hys : y ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨z, hz⟩ := (PX.mem_levelSet_iff c.isChart hyc).1 (mem_iInter.1 hys 1)
  have hzO : c.φ.model.E.toBase 1 z ∈ StrongRetr.r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model y hyc
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := StrongRetr.mem_U_of_mem_O hR hzO
  obtain ⟨hD, -, -, hTK, -, -, -⟩ := hLin hf hy0 hc hyc hz hzU
  have hmem : ∀ v : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z v ∈ rangeS (ρCLM c.isRetraction hzU) := fun v => by
    have := hTK v v.2
    rwa [hD.toScOperator_zero] at this
  set L := (linAt c.U c.R (c.principal f) z).codRestrict _ hmem with hLdef
  have h1 := hi c hc hyc z hz hzU L fun _ => rfl
  have hfr : IsScSmooth c.U (c.principal f ∘ StrongRetr.r c.R) := by
    have h := (hf.isScSmooth.isScSmoothRetractMap hc).comp_isScSmooth
      (c.isRetraction.baseRetraction c.relOpen) c.base_retract
    exact (h.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl
  have hfVr : IsScSmooth c.U (cV.principal fV ∘ StrongRetr.r c.R) :=
    hfr.congr c.relOpen.isScDomain fun u hu =>
      (StrongBundleChart.principal_restrictTo hV Bd.continuous subset_rfl _ hfs
        (c.r_mem_O hu)).symm
  have h2 := hj cV hcV hyc z hz hzU L fun v => by
    change linAt c.U c.R (c.principal f) z v = linAt c.U c.R (cV.principal fV) z v
    exact linAt_congr c.relOpen hfr.isSc1 hfVr.isSc1 (fun u hu =>
      (StrongBundleChart.principal_restrictTo hV Bd.continuous subset_rfl _ hfs
        (c.r_image ▸ hu)).symm) (show c.φ.model.E.toBase 1 z ∈ c.U from hzU) v
  exact h1.2.symm.trans h2.2

end Glue

/-- **B (0) from `A`**: at every smooth point of an sc-Fredholm section, B's index exists
(`exists_isIndexAtLocal`, then `hasIndex_of_isIndexAtLocal`). -/
theorem B0_of_A (hA : A) : ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    Bd.IsScFredholmSection f →
      ∀ x : X, V3_98_r2.IsSmoothPt PX x → ∃ i : ℤ, V3_98_r2.HasIndex Bd f x i := by
  obtain ⟨-, -, -, -, hLin, -, -, -, -, -, -, -, -, -, -, hUniq, hEx, -, -, -⟩ := hA
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f hf x hx
  obtain ⟨i, hi⟩ := hEx hf (mem_iInter.2 hx)
  exact ⟨i, hasIndex_of_isIndexAtLocal hLin hUniq hf hi⟩

/-- **B (a) from `A`**: along the solution set near a zero the index is constant
(`index_locally_constant_tame`; B's tame bundle and good position hypotheses are not needed). -/
theorem Ba_of_A (hA : A) : ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    V3_98_r2.IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → x ∈ solutionSet P f →
    Bd.IsGoodPositionGermSc f x →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V, y ∈ solutionSet P f →
          ∀ i : ℤ, V3_98_r2.HasIndex Bd f y i ↔ V3_98_r2.HasIndex Bd f x i := by
  obtain ⟨-, -, -, -, hLin, -, -, hLoc, -, -, -, -, -, -, -, hUniq, -, -, -, -⟩ := hA
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _ hf hx0 _
  have hF := hf.toIsScFredholmSection
  obtain ⟨V, i, hVo, hxV, hall⟩ := hLoc hf hx0
  have key : ∀ y ∈ V, IsZeroAt P f y → ∀ k : ℤ, V3_98_r2.HasIndex Bd f y k ↔ k = i := by
    intro y hy hy0 k
    have hyi : V3_98_r2.HasIndex Bd f y i := hasIndex_of_isIndexAtLocal hLin hUniq hF
      (isIndexAtLocal_of_isLinOfIndex hLin hF hy0 (hall y hy hy0))
    exact ⟨fun hk => hasIndex_unique hF.isScSmooth (hF.mem_smoothSet_of_isZeroAt hy0) hk hyi,
      fun hk => hk ▸ hyi⟩
  refine ⟨V, hVo, hxV, fun y hy hy0 k => ?_⟩
  rw [key y hy hy0 k, key x hxV hx0 k]

/-- **B (b) under two added hypotheses**, from `A` (`proposition_6_2_local`): with tame germ data
(`IsScFredholmSectionTame`; B assumes only `IsScFredholmSection` and `PX.IsTame`) and a path
`φ : ℝ → X` sc-smooth in the project's sense on all of `ℝ` (B's path is level-wise `C^∞` near
`[0, 1]` only), B's indices at the smooth ends agree. -/
theorem Bb_of_tame_global (hA : A) {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (PX : MPolyfold X) {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSectionTame f)
    (φ : (Fin 1 → ℝ) → X) (hφ : (rnPolyfold 1).IsScSmoothMap PX φ)
    (h0 : V3_98_r2.IsSmoothPt PX (φ 0)) (h1 : V3_98_r2.IsSmoothPt PX (φ 1)) :
    ∀ i : ℤ, V3_98_r2.HasIndex Bd f (φ 0) i ↔ V3_98_r2.HasIndex Bd f (φ 1) i := by
  obtain ⟨-, -, -, -, hLin, -, -, -, -, -, -, -, -, -, -, hUniq, -, -, h62, -⟩ := hA
  have hF := hf.toIsScFredholmSection
  obtain ⟨k, hk⟩ := h62 hf hφ
  have e0 := hasIndex_of_isIndexAtLocal hLin hUniq hF (hk 0)
  have e1 := hasIndex_of_isIndexAtLocal hLin hUniq hF (hk 1)
  intro i
  constructor
  · intro hi
    rwa [hasIndex_unique hF.isScSmooth (mem_iInter.2 h0) hi e0]
  · intro hi
    rwa [hasIndex_unique hF.isScSmooth (mem_iInter.2 h1) hi e1]


/-! ### Results against the first blind statement (`RoundTrip.V3_98.B`, `RoundTrip/Blind/V3_98.lean`)

Unchanged from the first refresh except that `linAt_isScFredholm` (now in the decls) is taken from
the hypothesis `A`. -/

section GlueR1
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

omit [T2Space Y] [ParacompactSpace Y] in
/-- The conclusion of `linAt_isScFredholm` in a chart gives the first blind file's
`ChartLinScFredholm` there. -/
lemma chartLin_of_r1 (f : X → Y) (x : X) (c : StrongBundleChart PX P) (hxV : x ∈ c.φ.source)
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U)
    (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
    (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
    (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
    (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
      hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU))
    (hsc : IsScFredholm (hD.toScOperator.restrict hT hK hTK)) :
    ChartLinScFredholm c f x (fredholmIndex (hD.toScOperator.restrict hT hK hTK 0)) := by
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model x hxV
  set T := hD.toScOperator.restrict hT hK hTK with hTdef
  have hL : IsScOperator (T 0) := T.isScOperator
  have hLT : hL.toScOperator = T := ScOperator.ext_base (by rw [hL.toScOperator_zero])
  refine ⟨z, hz, rangeS (ρCLM c.isRetraction hzU), ?_, hT, hK, T 0, ?_, hL, ?_, ?_⟩
  · ext h
    rw [SetLike.mem_coe, mem_rangeS_ρCLM_iff c.isRetraction hzO hzU, hz]
    rfl
  · intro v
    change hD.toScOperator 0 v.1 = _
    rw [hD.toScOperator_zero]
  · rw [hLT]; exact hsc
  · rw [hLT, scIndex_eq_fredholmIndex]

/-- At a zero of an sc-Fredholm section, `IsLinOfIndex f x i` gives the first blind file's
`IndexAt Bd f x i` (with `linAt_isScFredholm` from `A`). -/
theorem indexAt_of_isLinOfIndex_r1 (hLin : LinFred) {Bd : StrongBundle PX P} {f : X → Y}
    (hF : Bd.IsScFredholmSection f) {x : X} (hx0 : IsZeroAt P f x) {i : ℤ}
    (hI : Bd.IsLinOfIndex f x i) : IndexAt Bd f x i := by
  intro c hc hxV
  have hxs : x ∈ PX.smoothSet := hF.mem_smoothSet_of_isZeroAt hx0
  have hz : c.φ.model.E.toBase 1 (MPolyfold.levelLift c.φ 1 x) = c.φ x :=
    PX.toBase_levelLift c.isChart hxV (Set.mem_iInter.1 hxs 1)
  have hzU : c.φ.model.E.toBase 1 (MPolyfold.levelLift c.φ 1 x) ∈ c.U := by
    rw [hz]
    exact StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ c.φ.mapsTo_model x hxV)
  obtain ⟨hD, hT, hK, hTK, -, hsc, -⟩ := hLin hF hx0 hc hxV hz hzU
  have hmem : ∀ v : ↥(rangeS (scDeriv c.U (r c.R) (MPolyfold.levelLift c.φ 1 x))),
      linAt c.U c.R (c.principal f) (MPolyfold.levelLift c.φ 1 x) v ∈
        rangeS (ρCLM c.isRetraction hzU) := fun v => by
    have := hTK v v.2
    rwa [hD.toScOperator_zero] at this
  obtain ⟨hLF, hLind⟩ := hI c hc hxV _ hz hzU
    ((linAt c.U c.R (c.principal f) (MPolyfold.levelLift c.φ 1 x)).codRestrict _ hmem)
    fun _ => rfl
  obtain ⟨-, hind0⟩ := hD.toScOperator.isFredholm_restrict_zero hT hK hTK
    (L := (linAt c.U c.R (c.principal f) (MPolyfold.levelLift c.φ 1 x)).codRestrict _ hmem)
    (fun x => by rw [hD.toScOperator_zero]; rfl) hLF
  have := chartLin_of_r1 f x c hxV _ hz hzU hD hT hK hTK hsc
  rwa [hind0, hLind] at this

end GlueR1

/-- **First blind statement, its (b), under the project's hypotheses** (bump functions, tame germ
data), from `A` (`index_locally_constant_of_admitsBumpFunctions`). -/
theorem B_b_of_tame_bump_r1 (hA : A) {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (PX : MPolyfold X) {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X) (hbump : PX.AdmitsBumpFunctions)
    (hf : Bd.IsScFredholmSectionTame f) (hx0 : IsZeroAt P f x₀) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧
      ∀ y ∈ V, IsZeroAt P f y → ∃ i : ℤ, IndexAt Bd f x₀ i ∧ IndexAt Bd f y i := by
  obtain ⟨-, -, -, -, hLin, hBump, -⟩ := hA
  obtain ⟨V, i, hVo, hxV, hall⟩ := hBump hbump hf hx0
  exact ⟨V, hVo, hxV, fun y hy hy0 => ⟨i,
    indexAt_of_isLinOfIndex_r1 hLin hf.toIsScFredholmSection hx0 (hall x₀ hxV hx0),
    indexAt_of_isLinOfIndex_r1 hLin hf.toIsScFredholmSection hy0 (hall y hy hy0)⟩⟩

/-- **First blind statement, its (a), under the project's hypotheses** (bump functions, tame germ
data, a path sc-smooth on all of `ℝ`), from `A` (`proposition_6_2`). -/
theorem B_a_of_tame_bump_r1 (hA : A) {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (PX : MPolyfold X) {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (hbump : PX.AdmitsBumpFunctions)
    (hf : Bd.IsScFredholmSectionTame f) (γ : (Fin 1 → ℝ) → X)
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hx0 : IsZeroAt P f (γ fun _ => 0))
    (hx1 : IsZeroAt P f (γ fun _ => 1)) :
    ∃ i : ℤ, IndexAt Bd f (γ fun _ => 0) i ∧ IndexAt Bd f (γ fun _ => 1) i := by
  obtain ⟨-, -, -, -, hLin, -, -, -, -, -, hUn, -, -, -, h62, -⟩ := hA
  have := MPolyfold.paracompactSpace_prod (rnPolyfold 1) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin 1 → ℝ) × X → X))
    ((rnPolyfold 1).prod PX) Bd
  obtain ⟨i, hi⟩ := h62 hbump hf hγ
  have hF := hf.toIsScFredholmSection
  -- at a zero, the global Definition 6.1 index is the index of `f'(x)` (`IsIndexAt.unique`)
  have hlin : ∀ t, IsZeroAt P f (γ t) → Bd.IsLinOfIndex f (γ t) i := fun t ht => by
    obtain ⟨j, hj⟩ := exists_isLinOfIndex hLin hF ht
    obtain rfl : j = i := hUn hF (StrongBundle.isIndexAt_of_isZeroAt hF.isScSmooth.1 ht hj) (hi t)
    exact hj
  exact ⟨i, indexAt_of_isLinOfIndex_r1 hLin hF hx0 (hlin _ hx0),
    indexAt_of_isLinOfIndex_r1 hLin hF hx1 (hlin _ hx1)⟩

#rt_check RoundTrip.V3_98.B0_of_A [Polyfold.theorem_3_54_index_locally_constant,
  Polyfold.theorem_3_54_index, Polyfold.isSurjLinOfIndex_of_forall_dim,
  Polyfold.theorem_3_54_index_locally_constant_sc, Polyfold.StrongBundle.linAt_isScFredholm,
  Polyfold.index_locally_constant_of_admitsBumpFunctions,
  Polyfold.theorem_3_54_index_locally_constant_general, Polyfold.index_locally_constant_tame,
  Polyfold.theorem_3_54_index_locally_constant_general_tame,
  Polyfold.StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex,
  Polyfold.StrongBundle.IsIndexAt.unique, Polyfold.StrongBundle.exists_isIndexAt,
  Polyfold.exists_isScPlusSection_pullback_of_path,
  Polyfold.StrongBundle.isIndexAt_of_pullback_isLinOfIndex, Polyfold.proposition_6_2,
  Polyfold.StrongBundle.IsIndexAtLocal.unique, Polyfold.StrongBundle.exists_isIndexAtLocal,
  Polyfold.StrongBundle.isIndexAtLocal_iff_isIndexAt, Polyfold.proposition_6_2_local,
  Polyfold.proposition_6_2_local']
#rt_check RoundTrip.V3_98.Ba_of_A [Polyfold.theorem_3_54_index_locally_constant,
  Polyfold.theorem_3_54_index, Polyfold.isSurjLinOfIndex_of_forall_dim,
  Polyfold.theorem_3_54_index_locally_constant_sc, Polyfold.StrongBundle.linAt_isScFredholm,
  Polyfold.index_locally_constant_of_admitsBumpFunctions,
  Polyfold.theorem_3_54_index_locally_constant_general, Polyfold.index_locally_constant_tame,
  Polyfold.theorem_3_54_index_locally_constant_general_tame,
  Polyfold.StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex,
  Polyfold.StrongBundle.IsIndexAt.unique, Polyfold.StrongBundle.exists_isIndexAt,
  Polyfold.exists_isScPlusSection_pullback_of_path,
  Polyfold.StrongBundle.isIndexAt_of_pullback_isLinOfIndex, Polyfold.proposition_6_2,
  Polyfold.StrongBundle.IsIndexAtLocal.unique, Polyfold.StrongBundle.exists_isIndexAtLocal,
  Polyfold.StrongBundle.isIndexAtLocal_iff_isIndexAt, Polyfold.proposition_6_2_local,
  Polyfold.proposition_6_2_local']
#rt_check RoundTrip.V3_98.Bb_of_tame_global [Polyfold.theorem_3_54_index_locally_constant,
  Polyfold.theorem_3_54_index, Polyfold.isSurjLinOfIndex_of_forall_dim,
  Polyfold.theorem_3_54_index_locally_constant_sc, Polyfold.StrongBundle.linAt_isScFredholm,
  Polyfold.index_locally_constant_of_admitsBumpFunctions,
  Polyfold.theorem_3_54_index_locally_constant_general, Polyfold.index_locally_constant_tame,
  Polyfold.theorem_3_54_index_locally_constant_general_tame,
  Polyfold.StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex,
  Polyfold.StrongBundle.IsIndexAt.unique, Polyfold.StrongBundle.exists_isIndexAt,
  Polyfold.exists_isScPlusSection_pullback_of_path,
  Polyfold.StrongBundle.isIndexAt_of_pullback_isLinOfIndex, Polyfold.proposition_6_2,
  Polyfold.StrongBundle.IsIndexAtLocal.unique, Polyfold.StrongBundle.exists_isIndexAtLocal,
  Polyfold.StrongBundle.isIndexAtLocal_iff_isIndexAt, Polyfold.proposition_6_2_local,
  Polyfold.proposition_6_2_local']
#rt_check RoundTrip.V3_98.B_b_of_tame_bump_r1 [Polyfold.theorem_3_54_index_locally_constant,
  Polyfold.theorem_3_54_index, Polyfold.isSurjLinOfIndex_of_forall_dim,
  Polyfold.theorem_3_54_index_locally_constant_sc, Polyfold.StrongBundle.linAt_isScFredholm,
  Polyfold.index_locally_constant_of_admitsBumpFunctions,
  Polyfold.theorem_3_54_index_locally_constant_general, Polyfold.index_locally_constant_tame,
  Polyfold.theorem_3_54_index_locally_constant_general_tame,
  Polyfold.StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex,
  Polyfold.StrongBundle.IsIndexAt.unique, Polyfold.StrongBundle.exists_isIndexAt,
  Polyfold.exists_isScPlusSection_pullback_of_path,
  Polyfold.StrongBundle.isIndexAt_of_pullback_isLinOfIndex, Polyfold.proposition_6_2,
  Polyfold.StrongBundle.IsIndexAtLocal.unique, Polyfold.StrongBundle.exists_isIndexAtLocal,
  Polyfold.StrongBundle.isIndexAtLocal_iff_isIndexAt, Polyfold.proposition_6_2_local,
  Polyfold.proposition_6_2_local']
#rt_check RoundTrip.V3_98.B_a_of_tame_bump_r1 [Polyfold.theorem_3_54_index_locally_constant,
  Polyfold.theorem_3_54_index, Polyfold.isSurjLinOfIndex_of_forall_dim,
  Polyfold.theorem_3_54_index_locally_constant_sc, Polyfold.StrongBundle.linAt_isScFredholm,
  Polyfold.index_locally_constant_of_admitsBumpFunctions,
  Polyfold.theorem_3_54_index_locally_constant_general, Polyfold.index_locally_constant_tame,
  Polyfold.theorem_3_54_index_locally_constant_general_tame,
  Polyfold.StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex,
  Polyfold.StrongBundle.IsIndexAt.unique, Polyfold.StrongBundle.exists_isIndexAt,
  Polyfold.exists_isScPlusSection_pullback_of_path,
  Polyfold.StrongBundle.isIndexAt_of_pullback_isLinOfIndex, Polyfold.proposition_6_2,
  Polyfold.StrongBundle.IsIndexAtLocal.unique, Polyfold.StrongBundle.exists_isIndexAtLocal,
  Polyfold.StrongBundle.isIndexAtLocal_iff_isIndexAt, Polyfold.proposition_6_2_local,
  Polyfold.proposition_6_2_local']

end RoundTrip.V3_98
