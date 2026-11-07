import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_21

/-! Round trip for V7_21 (pp. 231–232: the translation groupoid `G_x ⋉ U(x)` is an ep-groupoid).

`A` is the conjunction of the types of the four listed theorems, universes at `0`:
`NaturalRep.translation_isLocalScDiffeo_src`, `translation_isLocalScDiffeo_tgt`,
`translation_isScSmoothCompSheet`, `translation_isProperMap` (for every `V ⊆ U`).  The others
(`GroupoidStr.translation`, `translationGroupoid`, `shearHomeomorph`, `translationEpGroupoid`)
are definitions.  `A` is stated for `R : X.NaturalRep x`, whose `U` is **connected**; `B` is for
every natural action `IsNatAction` (`U` open, not necessarily connected).

* `A → B`: `A` cannot be applied when `U` is disconnected (no `NaturalRep` with that `U`
  exists).  But `B` holds outright (`B_holds`): the ep-groupoid structure of `G ⋉ U` uses only
  the action `Φ` (a group action by sc-diffeomorphisms, `Φ(1) = id` following from injectivity),
  never `Γ` or connectedness, and the project's generic `Examples.actionEpGroupoid` (the
  translation groupoid of a finite discrete group acting by sc-smooth maps, `NonVacuity.lean`,
  proved independently of the four theorems) gives it with the text's `s`, `t`, `∘` and exactly
  `B`'s M-polyfold structures.  So `A_to_B` does not use `A` (flagged in the JSON).
* `B → A`: `B` applied to the natural action underlying `R` gives an ep-groupoid `E` with
  `E.src = s`, `E.tgt = t`, `E.comp = ∘` on composable pairs and the same charts as
  `R.objPolyfold`, `R.morPolyfold`; sc-smoothness, sc-diffeomorphisms and the sheet form of
  condition (4) depend only on the charts (`smoothOn_transfer` …), which gives the first three
  conjuncts.  `translation_isProperMap` (for **every** `V`) is not a consequence of
  "ep-groupoid" (Definition 7.3 (3) gives one `V(x)` per point); it is re-proved outright
  (`t = π₂ ∘ shear` with `G_x` finite). -/

set_option linter.style.haveILetI false

namespace RoundTrip.V7_21
open Polyfold Set
open scoped Polyfold.EpGroupoid.NaturalRep

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.NaturalRep.translation_isLocalScDiffeo_src.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.translation_isLocalScDiffeo_tgt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.translation_isScSmoothCompSheet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.translation_isProperMap.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.NaturalRep.translation_isLocalScDiffeo_src.{0},
    @Polyfold.EpGroupoid.NaturalRep.translation_isLocalScDiffeo_tgt.{0},
    @Polyfold.EpGroupoid.NaturalRep.translation_isScSmoothCompSheet.{0},
    @Polyfold.EpGroupoid.NaturalRep.translation_isProperMap.{0}⟩

/-! ### Glue -/

section Glue

/-- The inclusion of an open subset is sc-smooth (as the private lemma of `NaturalAction.lean`). -/
theorem isScSmoothMap_restrictOpen_val' {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] (PY : MPolyfold Y) {V : Set Y} [Nonempty V] [ParacompactSpace V]
    (hV : IsOpen V) : (PY.restrictOpen hV).IsScSmoothMap PY (Subtype.val : V → Y) := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ continuous_subtype_val.continuousOn
    fun v _ => ?_
  obtain ⟨φ, hφ, hv⟩ := PY.exists_isChart_mem_source v.1
  set φ' := φ.restrict (s := φ.source ∩ V) inter_subset_left (φ.isOpen_source.inter hV)
  have hφ'c : PY.IsChart φ' := MPolyfold.IsChart.restrict PY hφ _ _
  have hsub : φ'.source ⊆ V := inter_subset_right
  refine ⟨φ'.restrictTo hsub, φ', Subtype.val ⁻¹' φ'.source,
    MPolyfold.isChart_restrictTo hV hφ'c hsub, hφ'c,
    φ'.isOpen_source.preimage continuous_subtype_val, ⟨hv, v.2⟩, fun w hw => ⟨mem_univ _, hw⟩,
    fun w hw => hw, ?_⟩
  rw [show Subtype.val ⁻¹' φ'.source = (φ'.restrictTo hsub).source from rfl,
    (φ'.restrictTo hsub).image_source]
  refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
  change z = φ' ((φ'.restrictTo hsub).symm z).1
  rw [MChart.restrictTo_symm_val hsub hz, φ'.apply_symm_apply hz]

variable {A' B' : Type} [TopologicalSpace A'] [T2Space A'] [ParacompactSpace A']
  [TopologicalSpace B'] [T2Space B'] [ParacompactSpace B']
  {P P' : MPolyfold A'} {Q Q' : MPolyfold B'}

/-- Sc-smoothness only depends on the charts. -/
theorem smoothOn_transfer (hP : ∀ φ, P.IsChart φ ↔ P'.IsChart φ)
    (hQ : ∀ ψ, Q.IsChart ψ ↔ Q'.IsChart ψ) {f : A' → B'} {U : Set A'}
    (h : P.IsScSmoothOn Q f U) : P'.IsScSmoothOn Q' f U :=
  ⟨h.isOpen, h.continuousOn, fun φ ψ hφ hψ => h.smooth φ ψ ((hP φ).2 hφ) ((hQ ψ).2 hψ)⟩

theorem diffeo_transfer (hP : ∀ φ, P.IsChart φ ↔ P'.IsChart φ)
    (hQ : ∀ ψ, Q.IsChart ψ ↔ Q'.IsChart ψ) {f : A' → B'} {g : B' → A'} {U : Set A'}
    {V : Set B'} (h : P.IsScDiffeoOn Q f g U V) : P'.IsScDiffeoOn Q' f g U V :=
  ⟨smoothOn_transfer hP hQ h.isScSmoothOn, smoothOn_transfer hQ hP h.isScSmoothOn_inv,
    h.mapsTo, h.mapsTo_inv, h.left_inv, h.right_inv⟩

theorem localDiffeo_transfer (hP : ∀ φ, P.IsChart φ ↔ P'.IsChart φ)
    (hQ : ∀ ψ, Q.IsChart ψ ↔ Q'.IsChart ψ) {f : A' → B'} (h : P.IsLocalScDiffeo Q f) :
    P'.IsLocalScDiffeo Q' f := fun a => by
  obtain ⟨U, V, g, ha, hd⟩ := h a
  exact ⟨U, V, g, ha, diffeo_transfer hP hQ hd⟩

end Glue

/-! ### `A → B`: `B` holds outright -/

theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X x U Φ Γ h
  letI : TopologicalSpace (X.Isotropy x) := ⊥
  haveI : DiscreteTopology (X.Isotropy x) := ⟨rfl⟩
  haveI : Nonempty U := ⟨⟨x, h.mem⟩⟩
  have hmaps : ∀ g, MapsTo (Φ g) U U := fun g => (h.diffeo g).choose_spec.mapsTo
  have hΦ1 : ∀ y ∈ U, Φ 1 y = y := fun y hy => by
    obtain ⟨ψ, hψ⟩ := h.diffeo 1
    have h1 : Φ 1 y = Φ 1 (Φ 1 y) := by rw [← h.hom 1 1 y hy, mul_one]
    calc Φ 1 y = ψ (Φ 1 (Φ 1 y)) := (hψ.left_inv _ (hmaps 1 hy)).symm
      _ = ψ (Φ 1 y) := by rw [← h1]
      _ = y := hψ.left_inv y hy
  letI : MulAction (X.Isotropy x) U :=
    { smul := fun g y => ⟨Φ g y, hmaps g y.2⟩
      one_smul := fun y => Subtype.ext (hΦ1 y y.2)
      mul_smul := fun g g' y => Subtype.ext (h.hom g g' y y.2) }
  haveI : ParacompactSpace U := X.PObj.paracompactSpace_subtype U
  haveI : Finite (X.Isotropy x) := by
    have hfin := MPolyfold.finite_isotropy_of_isLocalScDiffeo X.isLocalScDiffeo_tgt
      (X.exists_isProperMap x)
    have := hfin.to_subtype
    exact Finite.of_injective (fun g : X.Isotropy x =>
      (⟨g.val, g.src_val, g.tgt_val⟩ : {φ | X.src φ = x ∧ X.tgt φ = x}))
      fun g g' hgg => GroupoidStr.Isotropy.ext (congrArg Subtype.val hgg)
  haveI : ParacompactSpace (X.Isotropy x × U) :=
    MPolyfold.paracompactSpace_prod (discretePolyfold (X.Isotropy x))
      (X.PObj.restrictOpen h.isOpen)
  have hP : ∀ k : X.Isotropy x, (X.PObj.restrictOpen h.isOpen).IsScSmoothMap
      (X.PObj.restrictOpen h.isOpen) fun y : U => k • y := fun k =>
    MPolyfold.IsScSmoothMap.codRestrict_restrictOpen h.isOpen
      (MPolyfold.IsScSmoothOn.comp (h.diffeo k).choose_spec.isScSmoothOn
        (isScSmoothMap_restrictOpen_val' X.PObj h.isOpen) fun y _ => y.2) _
  exact ⟨inferInstance, inferInstance, EpGroupoid.Examples.actionEpGroupoid hP, fun _ => rfl,
    fun _ => rfl, fun _ _ _ => rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem A_to_B : A → B := fun _ => B_holds

/-! ### `B → A` -/

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}

/-- The natural action underlying a natural representation. -/
theorem isNatAction_of_rep (R : X.NaturalRep x) : IsNatAction X x R.U R.Φ R.Γ where
  isOpen := R.isOpen_U
  mem := R.mem_U
  diffeo g := ⟨_, R.isScDiffeoOn_Φ g⟩
  hom := R.Φ_mul
  smooth := R.isScSmoothOn_Γ
  Γ_x := R.Γ_self
  src_tgt g y hy := ⟨R.src_Γ g y hy, R.tgt_Γ g y hy⟩
  unique := R.existsUnique_Γ

end

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X x R
    obtain ⟨_, _, E, hs, -, -, hPO, hPM⟩ := hB Obj Mor X x R.U R.Φ R.Γ (isNatAction_of_rep R)
    have hsrc : E.src = R.translationGroupoid.src := funext hs
    have := localDiffeo_transfer hPM hPO E.isLocalScDiffeo_src
    rw [hsrc] at this
    exact this
  · intro Obj Mor _ _ _ _ _ _ X x R
    obtain ⟨_, _, E, -, ht, -, hPO, hPM⟩ := hB Obj Mor X x R.U R.Φ R.Γ (isNatAction_of_rep R)
    have htgt : E.tgt = R.translationGroupoid.tgt := funext fun p => Subtype.ext (ht p)
    have := localDiffeo_transfer hPM hPO E.isLocalScDiffeo_tgt
    rw [htgt] at this
    exact this
  · intro Obj Mor _ _ _ _ _ _ X x R
    obtain ⟨_, _, E, hs, ht, hc, hPO, hPM⟩ := hB Obj Mor X x R.U R.Φ R.Γ (isNatAction_of_rep R)
    have hsrc : E.src = R.translationGroupoid.src := funext hs
    have htgt : E.tgt = R.translationGroupoid.tgt := funext fun p => Subtype.ext (ht p)
    intro σ W V hd
    have hd' := diffeo_transfer (fun φ => (hPM φ).symm) (fun φ => (hPO φ).symm) hd
    rw [← hsrc] at hd'
    have h1 := E.isScSmoothCompSheet σ W V hd'
    rw [htgt] at h1
    refine (smoothOn_transfer hPM hPM h1).congr fun ψ hψ => ?_
    have hcomp : E.src (σ (R.translationGroupoid.tgt ψ)) = E.tgt ψ := by
      rw [htgt]; exact hd'.right_inv _ hψ
    exact hc _ _ hcomp
  · intro Obj Mor _ _ _ _ _ _ X x R V
    have : Finite (X.Isotropy x) := by
      have hfin := MPolyfold.finite_isotropy_of_isLocalScDiffeo X.isLocalScDiffeo_tgt
        (X.exists_isProperMap x)
      have := hfin.to_subtype
      exact Finite.of_injective (fun g : X.Isotropy x =>
        (⟨g.val, g.src_val, g.tgt_val⟩ : {φ | X.src φ = x ∧ X.tgt φ = x}))
        fun g g' hgg => GroupoidStr.Isotropy.ext (congrArg Subtype.val hgg)
    have h : IsProperMap fun p : X.Isotropy x × R.U => p.1 • p.2 :=
      isProperMap_snd_of_compactSpace.comp R.shearHomeomorph.isProperMap
    exact h.restrict (isClosed_closure.preimage continuous_snd)

#rt_check RoundTrip.V7_21.A_to_B [Polyfold.EpGroupoid.NaturalRep.translation_isLocalScDiffeo_src,
  Polyfold.EpGroupoid.NaturalRep.translation_isLocalScDiffeo_tgt,
  Polyfold.EpGroupoid.NaturalRep.translation_isScSmoothCompSheet,
  Polyfold.EpGroupoid.NaturalRep.translation_isProperMap]
#rt_check RoundTrip.V7_21.B_to_A [Polyfold.EpGroupoid.NaturalRep.translation_isLocalScDiffeo_src,
  Polyfold.EpGroupoid.NaturalRep.translation_isLocalScDiffeo_tgt,
  Polyfold.EpGroupoid.NaturalRep.translation_isScSmoothCompSheet,
  Polyfold.EpGroupoid.NaturalRep.translation_isProperMap]
#rt_overlap RoundTrip.V7_21.B_to_A [Polyfold.EpGroupoid.NaturalRep.translation_isLocalScDiffeo_src,
  Polyfold.EpGroupoid.NaturalRep.translation_isLocalScDiffeo_tgt,
  Polyfold.EpGroupoid.NaturalRep.translation_isScSmoothCompSheet,
  Polyfold.EpGroupoid.NaturalRep.translation_isProperMap]

end RoundTrip.V7_21
