import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_3

set_option maxSynthPendingDepth 3

/-!
Round trip for V10_3 (2021 Proposition 10.1.3, p. 462 (2017: Proposition 10.1, p. 334): the
refinement `X_𝒰` and the equivalence `X_𝒰 → X`).

The item lists the definitions `OpenCover`, `OpenCover.univ`, `objSet`, `morSet`, `groupoidStr`,
`objPolyfold`, `morPolyfold`, `epGroupoid`, `functor`, `Examples.reflectionCover` (vocabulary)
and seven theorems.  `A` is the conjunction of the types of the theorems, universe at `0`
(`Obj Mor ι : Type`): the four ep-groupoid conditions of `X_𝒰` that the item lists
(`isLocalScDiffeo_src`, `isLocalScDiffeo_tgt`, `exists_isProperMap`, `isScSmoothCompSheet`),
`proposition_10_1_3` (the functor is an equivalence), and the witness
`isEquivalence_reflectionCover`, `not_injective_reflectionCover_obj`.

`B` pins down the project's `X_𝒰 = 𝒰.epGroupoid` and `𝒰.functor` by their data (objects,
morphisms, structure maps, M-polyfold structures `objPolyfold`, `morPolyfold`, the functor's
formulas) and says that the functor is an equivalence in the blind author's sense `IsEquivB`.

* `A ⇒ B`: the data equations are definitional (`Iff.rfl`, `rfl`), except composition
  (`OpenCover.comp_val`); `IsEquivB 𝒰.functor` is `A`'s `proposition_10_1_3` through the glue
  `isEquivB_of_isEquivalence` (the project's orbit space with the quotient topology is
  definitionally the blind `Quot`).
* `B ⇒ A`: `proposition_10_1_3` and `isEquivalence_reflectionCover` (B applied to the two-set
  covering of `ℤ/2 ⋉ ℝ`, `ι = Bool`) come from `B`'s `IsEquivB`, `not_injective_reflectionCover_obj`
  from `B`'s formula for the functor on objects.  The four ep-groupoid conditions of `X_𝒰` are
  in `B` only inside the definition `𝒰.epGroupoid` (the blind author: "is an ep-groupoid is the
  existence of `𝒰.epGroupoid`, not restated"), whose fields *are* these theorems; reading them off
  those fields would be circular, so they are re-proved outright (`isLocalScDiffeo_src'` etc.,
  copies of the project's proofs from non-item lemmas: `isLocalScDiffeoAt_srcAmb`,
  `isLocalScDiffeoAt_restrict`, `X.exists_isProperMap`, `X.isScSmoothCompSheet`, ...).

**Harness note.**  `B` and `A` (through `proposition_10_1_3`'s statement, `𝒰.functor :
EpFunctor 𝒰.epGroupoid X`) mention `OpenCover.epGroupoid`, whose fields are four of the banned
theorems passed as plain applications.  So every term mentioning `A` or `B` reaches them, and
`#rt_check` fails on both directions (recorded with `#guard_msgs`).  As in V7_40 we run
`#rt_check_except_defs`, the harness traversal `rtCollect` with the body of `epGroupoid` not
unfolded: both directions pass, so the proofs never use `epGroupoid`'s fields.
-/

namespace RoundTrip.V10_3
open Polyfold Set Function Topology Filter CategoryTheory

attribute [local instance] paracompactSpace_discrete_prod

open Lean Elab Command in
/-- `#rt_check_except_defs T [nᵢ]`: the proof of `T` reaches the banned `nᵢ` only through the body
of the definition `EpGroupoid.OpenCover.epGroupoid`. -/
elab "#rt_check_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let used := rtCollect env roots.toList
    (NameSet.empty.insert ``Polyfold.EpGroupoid.OpenCover.epGroupoid)
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do
    throwError "FAIL: {t.getId} uses {bad} outside the body of OpenCover.epGroupoid"
  logInfo m!"OK: {t.getId} reaches the banned theorems only through the body of OpenCover.epGroupoid"

open Lean Elab Command in
/-- `#rt_overlap_except_defs T [nᵢ]`: as `#rt_overlap`, with the body of `epGroupoid` not
unfolded on the side of `T`. -/
elab "#rt_overlap_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let used := rtCollect env (((rtValue? ci).map (·.getUsedConstants)).getD #[]).toList
    (NameSet.empty.insert ``Polyfold.EpGroupoid.OpenCover.epGroupoid)
  let mut roots : Array Name := #[]
  for b in bs.getElems do
    if let some c := env.find? b.getId then
      roots := roots ++ (((rtValue? c).map (·.getUsedConstants)).getD #[])
  let closure := rtCollect env roots.toList {}
  let shared := used.toList.filter fun n =>
    closure.contains n && (match env.find? n with | some (.thmInfo _) => true | _ => false) &&
      (`Polyfold).isPrefixOf n && !n.isInternal
  logInfo m!"rt_overlap_except_defs {t.getId}: {shared.length} shared non-internal project theorems {shared}"

/-- The project's statement (universe at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_src.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_tgt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.OpenCover.exists_isProperMap.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.OpenCover.isScSmoothCompSheet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.OpenCover.proposition_10_1_3.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.isEquivalence_reflectionCover) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.not_injective_reflectionCover_obj)

theorem A_holds : A :=
  ⟨@EpGroupoid.OpenCover.isLocalScDiffeo_src.{0}, @EpGroupoid.OpenCover.isLocalScDiffeo_tgt.{0},
    @EpGroupoid.OpenCover.exists_isProperMap.{0}, @EpGroupoid.OpenCover.isScSmoothCompSheet.{0},
    @EpGroupoid.OpenCover.proposition_10_1_3.{0},
    @EpGroupoid.Examples.isEquivalence_reflectionCover,
    @EpGroupoid.Examples.not_injective_reflectionCover_obj⟩

/-! ### Glue for Definition 10.1.1 -/

section Glue

variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

theorem orbitHomeoB_iff (F : EpFunctor X Y) : OrbitHomeoB F ↔ IsHomeomorph F.orbitMap := by
  constructor
  · rintro ⟨e, he⟩
    have : (F.orbitMap : X.OrbitSpace → Y.OrbitSpace) = e := by
      funext a
      induction a using Quotient.inductionOn with | h x => exact (he x).symm
    rw [this]
    exact e.isHomeomorph
  · intro h
    exact ⟨h.homeomorph, fun _ => rfl⟩

theorem isEquivB_of_isEquivalence {F : EpFunctor X Y} (h : F.IsEquivalence) : IsEquivB F :=
  ⟨⟨(GroupoidFunctor.faithful_iff _).1 h.faithful, (GroupoidFunctor.full_iff _).1 h.full⟩,
    (orbitHomeoB_iff F).2 h.isHomeomorph_orbitMap, h.isLocalScDiffeo_obj⟩

theorem isEquivalence_of_isEquivB {F : EpFunctor X Y} (h : IsEquivB F) : F.IsEquivalence :=
  ⟨(GroupoidFunctor.full_iff _).2 h.1.2, (GroupoidFunctor.faithful_iff _).2 h.1.1,
    (orbitHomeoB_iff F).1 h.2.1, h.2.2⟩

end Glue

/-! ### Re-proofs of the ep-groupoid conditions of `X_𝒰` (copies of the project's proofs) -/

section Reproof

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {ι : Type} (𝒰 : X.OpenCover ι) [TopologicalSpace ι] [DiscreteTopology ι]

theorem isLocalScDiffeo_src' [Nonempty Obj] :
    𝒰.morPolyfold.IsLocalScDiffeo 𝒰.objPolyfold 𝒰.src := fun q =>
  MPolyfold.isLocalScDiffeoAt_restrict 𝒰.isOpen_morSet 𝒰.isOpen_objSet
    EpGroupoid.OpenCover.continuous_srcAmb (fun q => q.2.1)
    (EpGroupoid.OpenCover.isLocalScDiffeoAt_srcAmb q.1)

theorem isLocalScDiffeo_tgt' [Nonempty Obj] :
    𝒰.morPolyfold.IsLocalScDiffeo 𝒰.objPolyfold 𝒰.tgt := fun q =>
  MPolyfold.isLocalScDiffeoAt_restrict 𝒰.isOpen_morSet 𝒰.isOpen_objSet
    EpGroupoid.OpenCover.continuous_tgtAmb (fun q => q.2.2)
    (EpGroupoid.OpenCover.isLocalScDiffeoAt_tgtAmb q.1)

theorem exists_isProperMap' (p : 𝒰.objSet) : ∃ V : Set 𝒰.objSet, IsOpen V ∧ p ∈ V ∧
    IsProperMap ((𝒰.src ⁻¹' closure V).domRestrict 𝒰.tgt) := by
  obtain ⟨V₀, hV₀o, hpV₀, hprop⟩ := X.exists_isProperMap p.1.2
  have := X.PObj.metrizableSpace
  have hW : 𝒰.set p.1.1 ∩ V₀ ∈ 𝓝 p.1.2 := ((𝒰.isOpen _).inter hV₀o).mem_nhds ⟨p.2, hpV₀⟩
  obtain ⟨C, hC, hCc, hCsub⟩ := exists_mem_nhds_isClosed_subset hW
  have hclV : closure (interior C) ⊆ 𝒰.set p.1.1 ∩ V₀ :=
    (closure_minimal interior_subset hCc).trans hCsub
  set Vt : Set 𝒰.objSet := Subtype.val ⁻¹' ({p.1.1} ×ˢ interior C) with hVt
  refine ⟨Vt, ((isOpen_discrete _).prod isOpen_interior).preimage continuous_subtype_val,
    ⟨mem_singleton _, mem_interior_iff_mem_nhds.2 hC⟩, ?_⟩
  have hD : ∀ q : 𝒰.morSet, 𝒰.src q ∈ closure Vt →
      q.1.1.1 = p.1.1 ∧ X.src q.1.2 ∈ closure (interior C) := by
    intro q hq
    have h1 := continuous_subtype_val.closure_preimage_subset _ hq
    rw [closure_prod_eq, closure_singleton] at h1
    exact ⟨h1.1, h1.2⟩
  have hsub₀ : closure (interior C) ⊆ closure V₀ :=
    closure_mono (interior_subset.trans (hCsub.trans inter_subset_right))
  rw [isProperMap_iff_ultrafilter]
  refine ⟨𝒰.continuous_tgt.comp continuous_subtype_val, fun 𝒱 y hy => ?_⟩
  have hj : ∀ᶠ d in (𝒱 : Filter (𝒰.src ⁻¹' closure Vt)), d.1.1.1.2 = y.1.1 := by
    have h := ((continuous_fst.comp continuous_subtype_val).tendsto y).comp hy
    rwa [nhds_discrete, tendsto_pure] at h
  have hsrc : ∀ d : 𝒰.src ⁻¹' closure Vt, X.src d.1.1.2 ∈ closure V₀ := fun d =>
    hsub₀ (hD d.1 d.2).2
  let g : 𝒰.src ⁻¹' closure Vt → X.src ⁻¹' closure V₀ := fun d => ⟨d.1.1.2, hsrc d⟩
  have h2 : Tendsto ((X.src ⁻¹' closure V₀).domRestrict X.tgt) (Ultrafilter.map g 𝒱)
      (𝓝 y.1.2) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff]
    exact ((continuous_snd.comp continuous_subtype_val).tendsto y).comp hy
  obtain ⟨φ', hφ'y, hle⟩ := (isProperMap_iff_ultrafilter.1 hprop).2 h2
  have hg : Tendsto g 𝒱 (𝓝 φ') := by
    rw [Ultrafilter.coe_map] at hle
    exact hle
  have hφ : Tendsto (fun d : 𝒰.src ⁻¹' closure Vt => d.1.1.2) 𝒱 (𝓝 φ'.1) :=
    (continuous_subtype_val.tendsto φ').comp hg
  have hsφ : X.src φ'.1 ∈ closure (interior C) :=
    isClosed_closure.mem_of_tendsto ((X.continuous_src.tendsto _).comp hφ)
      (Eventually.of_forall fun d => (hD d.1 d.2).2)
  have htφ : X.tgt φ'.1 = y.1.2 := hφ'y
  let d₀ : 𝒰.morSet := ⟨((p.1.1, y.1.1), φ'.1), (hclV hsφ).1, by
    change X.tgt φ'.1 ∈ 𝒰.set y.1.1
    rw [htφ]
    exact y.2⟩
  have hd₀ : Tendsto (fun d : 𝒰.src ⁻¹' closure Vt => d.1) 𝒱 (𝓝 d₀) := by
    rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds ?_ hφ
    rw [nhds_discrete, tendsto_pure]
    filter_upwards [hj] with d hdj
    exact Prod.ext (hD d.1 d.2).1 hdj
  have hd₀D : 𝒰.src d₀ ∈ closure Vt :=
    isClosed_closure.mem_of_tendsto ((𝒰.continuous_src.tendsto _).comp hd₀)
      (Eventually.of_forall fun d => d.2)
  refine ⟨⟨d₀, hd₀D⟩, EpGroupoid.OpenCover.objSet_ext rfl htφ, ?_⟩
  have := (Topology.IsInducing.subtypeVal.tendsto_nhds_iff (f := id)
    (y := (⟨d₀, hd₀D⟩ : 𝒰.src ⁻¹' closure Vt))).2 hd₀
  exact tendsto_id'.1 this

theorem isScSmoothCompSheet' [Nonempty Obj] :
    IsScSmoothCompSheet 𝒰.objPolyfold 𝒰.morPolyfold 𝒰.src 𝒰.tgt 𝒰.comp := by
  intro σ W V hd
  have hΩ : IsOpen (𝒰.tgt ⁻¹' V) := hd.isScSmoothOn_inv.isOpen.preimage 𝒰.continuous_tgt
  have hσt : 𝒰.morPolyfold.IsScSmoothOn 𝒰.morPolyfold (σ ∘ 𝒰.tgt) (𝒰.tgt ⁻¹' V) :=
    MPolyfold.IsScSmoothOn.comp hd.isScSmoothOn_inv
      (((isLocalScDiffeo_tgt' 𝒰).isScSmoothMap).mono hΩ (subset_univ _)) fun _ h => h
  have hm : 𝒰.morPolyfold.IsScSmoothOn ((discretePolyfold (ι × ι)).prod X.PMor)
      (fun ψ => (σ (𝒰.tgt ψ)).1) (𝒰.tgt ⁻¹' V) :=
    MPolyfold.IsScSmoothOn.comp (MPolyfold.isScSmoothMap_subtypeVal 𝒰.isOpen_morSet) hσt
      (mapsTo_univ _ _)
  have hm₂ : 𝒰.morPolyfold.IsScSmoothOn X.PMor (fun ψ => (σ (𝒰.tgt ψ)).1.2) (𝒰.tgt ⁻¹' V) :=
    MPolyfold.IsScSmoothOn.comp (MPolyfold.isScSmoothMap_snd _ _) hm (mapsTo_univ _ _)
  have hkey : ∀ ψ ∈ 𝒰.tgt ⁻¹' V, X.src (σ (𝒰.tgt ψ)).1.2 = X.tgt ψ.1.2 := fun ψ hψ =>
    congrArg (fun p : 𝒰.objSet => p.1.2) (hd.right_inv _ hψ)
  have hψ2 : 𝒰.morPolyfold.IsScSmoothMap X.PMor fun ψ : 𝒰.morSet => ψ.1.2 :=
    (MPolyfold.isScSmoothMap_snd _ _).comp (MPolyfold.isScSmoothMap_subtypeVal 𝒰.isOpen_morSet)
  have hG₂ : 𝒰.morPolyfold.IsScSmoothOn X.PMor
      (fun ψ => X.comp (σ (𝒰.tgt ψ)).1.2 ψ.1.2) (𝒰.tgt ⁻¹' V) := by
    refine MPolyfold.IsScSmoothOn.of_locally hΩ fun ψ₀ hψ₀ => ?_
    obtain ⟨W₀, V₀, σ₀, hmem, hd₀⟩ := X.isLocalScDiffeo_src (σ (𝒰.tgt ψ₀)).1.2
    have hΩ₀ : IsOpen (𝒰.tgt ⁻¹' V ∩ (fun ψ => (σ (𝒰.tgt ψ)).1.2) ⁻¹' W₀) :=
      hm₂.continuousOn.isOpen_inter_preimage hΩ hd₀.isOpen_source
    refine ⟨_, hΩ₀, ⟨hψ₀, hmem⟩, inter_subset_left, ?_⟩
    have hX := X.isScSmoothCompSheet σ₀ W₀ V₀ hd₀
    refine (MPolyfold.IsScSmoothOn.comp hX (hψ2.mono hΩ₀ (subset_univ _)) fun ψ hψ => ?_).congr
      fun ψ hψ => ?_
    · change X.tgt ψ.1.2 ∈ V₀
      rw [← hkey ψ hψ.1]
      exact hd₀.mapsTo hψ.2
    · change X.comp (σ₀ (X.tgt ψ.1.2)) ψ.1.2 = X.comp (σ (𝒰.tgt ψ)).1.2 ψ.1.2
      rw [← hkey ψ hψ.1, hd₀.left_inv _ hψ.2]
  have hG₁ : 𝒰.morPolyfold.IsScSmoothOn (discretePolyfold (ι × ι))
      (fun ψ => (ψ.1.1.1, (σ (𝒰.tgt ψ)).1.1.2)) (𝒰.tgt ⁻¹' V) :=
    isScSmoothOn_discrete_of_continuousOn hΩ
      ((continuous_fst.comp (continuous_fst.comp continuous_subtype_val)).continuousOn.prodMk
        ((continuous_snd.comp continuous_fst).comp_continuousOn hm.continuousOn))
  refine (MPolyfold.isScSmoothOn_restrictOpen_iff 𝒰.isOpen_morSet).2
    ((MPolyfold.IsScSmoothOn.prodMk hG₁ hG₂).congr fun ψ hψ => ?_)
  change _ = (𝒰.comp (σ (𝒰.tgt ψ)) ψ).1
  rw [EpGroupoid.OpenCover.comp_val (hkey ψ hψ)]

end Reproof

/-! ### `A ⇒ B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ _ X ι _ _ 𝒰
  refine ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => rfl, fun _ => rfl, fun q q' h => ?_,
    fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl,
    isEquivB_of_isEquivalence (hA.2.2.2.2.1 𝒰)⟩
  exact EpGroupoid.OpenCover.comp_val (EpGroupoid.OpenCover.src_eq_tgt h).2

/-! ### `B ⇒ A` -/

open EpGroupoid.Examples in
theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun 𝒰 _ _ _ => isLocalScDiffeo_src' 𝒰, fun 𝒰 _ _ _ => isLocalScDiffeo_tgt' 𝒰,
    fun 𝒰 _ _ p => exists_isProperMap' 𝒰 p, fun 𝒰 _ _ _ => isScSmoothCompSheet' 𝒰, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X ι 𝒰 _ _ _
    exact isEquivalence_of_isEquivB (hB Obj Mor X ι 𝒰).2.2.2.2.2.2.2.2.2.2.2
  · exact isEquivalence_of_isEquivB (hB _ _ _ _ reflectionCover).2.2.2.2.2.2.2.2.2.2.2
  · intro h
    have hobj := (hB _ _ _ _ reflectionCover).2.2.2.2.2.2.2.2.2.1
    have h' := @h ⟨(true, 0), show (-1 : ℝ) < (0 : Fin 1 → ℝ) 0 by norm_num⟩
      ⟨(false, 0), show (0 : Fin 1 → ℝ) 0 < 1 by norm_num⟩ (by rw [hobj, hobj])
    exact absurd (congrArg (fun p : reflectionCover.objSet => p.1.1) h') (by decide)

/-! ### Checks -/

/--
error: rt_check FAIL: RoundTrip.V10_3.A_to_B uses [Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_src,
 Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_tgt,
 Polyfold.EpGroupoid.OpenCover.exists_isProperMap,
 Polyfold.EpGroupoid.OpenCover.isScSmoothCompSheet]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_3.A_to_B [Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_src,
  Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_tgt,
  Polyfold.EpGroupoid.OpenCover.exists_isProperMap,
  Polyfold.EpGroupoid.OpenCover.isScSmoothCompSheet,
  Polyfold.EpGroupoid.OpenCover.proposition_10_1_3,
  Polyfold.EpGroupoid.Examples.isEquivalence_reflectionCover,
  Polyfold.EpGroupoid.Examples.not_injective_reflectionCover_obj]

/--
error: rt_check FAIL: RoundTrip.V10_3.B_to_A uses [Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_src,
 Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_tgt,
 Polyfold.EpGroupoid.OpenCover.exists_isProperMap,
 Polyfold.EpGroupoid.OpenCover.isScSmoothCompSheet]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_3.B_to_A [Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_src,
  Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_tgt,
  Polyfold.EpGroupoid.OpenCover.exists_isProperMap,
  Polyfold.EpGroupoid.OpenCover.isScSmoothCompSheet,
  Polyfold.EpGroupoid.OpenCover.proposition_10_1_3,
  Polyfold.EpGroupoid.Examples.isEquivalence_reflectionCover,
  Polyfold.EpGroupoid.Examples.not_injective_reflectionCover_obj]

#rt_check_except_defs RoundTrip.V10_3.A_to_B [Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_src,
  Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_tgt,
  Polyfold.EpGroupoid.OpenCover.exists_isProperMap,
  Polyfold.EpGroupoid.OpenCover.isScSmoothCompSheet,
  Polyfold.EpGroupoid.OpenCover.proposition_10_1_3,
  Polyfold.EpGroupoid.Examples.isEquivalence_reflectionCover,
  Polyfold.EpGroupoid.Examples.not_injective_reflectionCover_obj]
#rt_check_except_defs RoundTrip.V10_3.B_to_A [Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_src,
  Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_tgt,
  Polyfold.EpGroupoid.OpenCover.exists_isProperMap,
  Polyfold.EpGroupoid.OpenCover.isScSmoothCompSheet,
  Polyfold.EpGroupoid.OpenCover.proposition_10_1_3,
  Polyfold.EpGroupoid.Examples.isEquivalence_reflectionCover,
  Polyfold.EpGroupoid.Examples.not_injective_reflectionCover_obj]
#rt_overlap RoundTrip.V10_3.B_to_A [Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_src,
  Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_tgt,
  Polyfold.EpGroupoid.OpenCover.exists_isProperMap,
  Polyfold.EpGroupoid.OpenCover.isScSmoothCompSheet,
  Polyfold.EpGroupoid.OpenCover.proposition_10_1_3,
  Polyfold.EpGroupoid.Examples.isEquivalence_reflectionCover,
  Polyfold.EpGroupoid.Examples.not_injective_reflectionCover_obj]
#rt_overlap_except_defs RoundTrip.V10_3.B_to_A [Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_src,
  Polyfold.EpGroupoid.OpenCover.isLocalScDiffeo_tgt,
  Polyfold.EpGroupoid.OpenCover.exists_isProperMap,
  Polyfold.EpGroupoid.OpenCover.isScSmoothCompSheet,
  Polyfold.EpGroupoid.OpenCover.proposition_10_1_3,
  Polyfold.EpGroupoid.Examples.isEquivalence_reflectionCover,
  Polyfold.EpGroupoid.Examples.not_injective_reflectionCover_obj]

end RoundTrip.V10_3
