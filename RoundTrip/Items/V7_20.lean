import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_20

/-! Round trip for V7_20 (p. 232: the M-polyfold `G × U`, "the finite disjoint union of copies of
the M-polyfold `U`").

`A` is the conjunction of the types of the listed theorems, universes at `0`:
`discreteChart_compatible`, `isScSmoothMap_discrete_iff`, `isScSmoothOn_univ_prod_discrete_iff`,
`isScSmoothMap_prod_discrete_iff`, `NaturalRep.isScSmoothMap_smul`; the definitions
`discretePolyfold`, `discreteChart`, `NaturalRep.objPolyfold`, `NaturalRep.morPolyfold` are
vocabulary.  The project's `G × U` (for a natural representation `R`) is
`morPolyfold = (discretePolyfold G_x).prod (X.PObj.restrictOpen R.isOpen_U)`.

* `A → B`: `B` asks for SOME M-polyfold structure on `Gx × U` (any open `U ∋ x`) whose sheets
  `{g} × U` are sc-diffeomorphic to `U ⊆ X` by the projection.  The project's construction
  `(discretePolyfold Gx).prod (X.PObj.restrictOpen hU)` is taken (the same as `morPolyfold`, but
  for an arbitrary open `U` rather than `R.U`, and with `B`'s subtype `Gx` for `G_x`).  `A`'s
  `isScSmoothMap_prod_discrete_iff` gives the sc-smoothness of `(g, y) ↦ y` from that of the
  inclusion `U → X`, and `A`'s `isScSmoothMap_discrete_iff` that of the constant `y ↦ g`; the
  inclusion `U → X` and its inverse `y ↦ ⟨y, _⟩` on `U` are sc-smooth by chart arguments proved
  here (the project's lemma for the inclusion is private).
* `B → A`: vacuous.  `A`'s conjuncts are facts about the project's definitions
  (`discreteChart`, `discretePolyfold`, `MPolyfold.prod`, `objPolyfold`), which `B`, an existence
  statement about some structure on `Gx × U`, does not mention; they are re-proved outright.
* Both checks are `#rt_check_soft`: every use of `discretePolyfold` reaches the banned
  `discreteChart_compatible` through the proof field `compatible` of the definition
  `discretePolyfold` (its statement already mentions `discretePolyfold`). -/

namespace RoundTrip.V7_20
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.discreteChart_compatible.{0}) ∧
  (type_of% @Polyfold.isScSmoothMap_discrete_iff.{0, 0}) ∧
  (type_of% @Polyfold.isScSmoothOn_univ_prod_discrete_iff.{0, 0, 0}) ∧
  (type_of% @Polyfold.isScSmoothMap_prod_discrete_iff.{0, 0, 0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.isScSmoothMap_smul.{0})

theorem A_holds : A :=
  ⟨@Polyfold.discreteChart_compatible.{0}, @Polyfold.isScSmoothMap_discrete_iff.{0, 0},
    @Polyfold.isScSmoothOn_univ_prod_discrete_iff.{0, 0, 0},
    @Polyfold.isScSmoothMap_prod_discrete_iff.{0, 0, 0},
    @Polyfold.EpGroupoid.NaturalRep.isScSmoothMap_smul.{0}⟩

/-! ### Open subsets: the inclusion and its inverse are sc-smooth -/

section RestrictOpen
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]

/-- The inclusion of an open subset is sc-smooth (as in the project, where it is private). -/
theorem isScSmoothMap_val' (PY : MPolyfold Y) {V : Set Y} [Nonempty V] [ParacompactSpace V]
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

open scoped Classical in
/-- `y ↦ ⟨y, _⟩` is sc-smooth on the open `V`, into the M-polyfold `V`. -/
theorem isScSmoothOn_mk' (PY : MPolyfold Y) {V : Set Y} [Nonempty V] [ParacompactSpace V]
    (hV : IsOpen V) (v₀ : V) :
    PY.IsScSmoothOn (PY.restrictOpen hV)
      (fun y => if h : y ∈ V then (⟨y, h⟩ : V) else v₀) V := by
  set f : Y → V := fun y => if h : y ∈ V then (⟨y, h⟩ : V) else v₀ with hf
  have hfc : ContinuousOn f V := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine continuous_id.congr fun v => ?_
    change v = f v.1
    simp only [f, dif_pos v.2]
  refine MPolyfold.IsScSmoothOn.of_exists_charts hV hfc fun y hy => ?_
  obtain ⟨φ, hφ, hyφ⟩ := PY.exists_isChart_mem_source y
  set φ' := φ.restrict (s := φ.source ∩ V) inter_subset_left (φ.isOpen_source.inter hV)
  have hφ'c : PY.IsChart φ' := MPolyfold.IsChart.restrict PY hφ _ _
  have hsub : φ'.source ⊆ V := inter_subset_right
  refine ⟨φ', φ'.restrictTo hsub, φ'.source, hφ'c, MPolyfold.isChart_restrictTo hV hφ'c hsub,
    φ'.isOpen_source, ⟨hyφ, hy⟩, fun w hw => ⟨hsub hw, hw⟩, fun w hw => ?_, ?_⟩
  · change (f w).1 ∈ φ'.source
    simp only [f, dif_pos (hsub hw)]
    exact hw
  · rw [φ'.image_source]
    refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
    have hzV : φ'.symm z ∈ V := hsub (φ'.symm_mapsTo hz)
    change z = φ' (f (φ'.symm z)).1
    simp only [f, dif_pos hzV]
    rw [φ'.apply_symm_apply hz]

end RestrictOpen

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  classical
  intro hA Obj Mor _ _ _ _ _ _ X x U hU hxU
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : ParacompactSpace U := X.PObj.paracompactSpace_subtype U
  have := MPolyfold.paracompactSpace_prod (discretePolyfold (Gx X x)) (X.PObj.restrictOpen hU)
  refine ⟨this, (discretePolyfold (Gx X x)).prod (X.PObj.restrictOpen hU), fun g => ?_⟩
  set v₀ : U := ⟨x, hxU⟩
  set f : Obj → U := fun y => if h : y ∈ U then (⟨y, h⟩ : U) else v₀ with hf
  -- `(g, y) ↦ y` is sc-smooth (`A`: sheetwise, the inclusion `U → X`)
  have hsnd : ((discretePolyfold (Gx X x)).prod (X.PObj.restrictOpen hU)).IsScSmoothMap X.PObj
      (fun p : Gx X x × U => (p.2 : Obj)) :=
    (hA.2.2.2.1 (G := Gx X x) (PX := X.PObj.restrictOpen hU) (PY := X.PObj)).2 fun _ =>
      isScSmoothMap_val' X.PObj hU
  -- `y ↦ g` is sc-smooth (`A`: continuous into a discrete M-polyfold)
  have hconst : X.PObj.IsScSmoothMap (discretePolyfold (Gx X x)) fun _ => g :=
    (hA.2.1 (G := Gx X x) (PX := X.PObj)).2 continuous_const
  exact ⟨fun y => (g, f y),
    { isScSmoothOn := hsnd.mono ((isOpen_discrete _).prod isOpen_univ) (subset_univ _)
      isScSmoothOn_inv := MPolyfold.IsScSmoothOn.prodMk (hconst.mono hU (subset_univ _))
        (isScSmoothOn_mk' X.PObj hU v₀)
      mapsTo := fun p _ => p.2.2
      mapsTo_inv := fun y _ => ⟨rfl, mem_univ _⟩
      left_inv := fun p hp => by
        have hp1 : p.1 = g := hp.1
        simp only [f, dif_pos p.2.2]
        exact Prod.ext hp1.symm rfl
      right_inv := fun y hy => by
        change (f y).1 = y
        simp only [f, dif_pos hy] }⟩

/-! ### `B → A` (vacuous): the conjuncts of `A`, re-proved outright -/

theorem discreteChart_compatible' {G : Type} [TopologicalSpace G] [DiscreteTopology G]
    (g g' : G) : (discreteChart g).Compatible (discreteChart g') := by
  have hO : (discreteChart g).overlap (discreteChart g') =
      (discreteChart g').overlap (discreteChart g) := by
    change (fun _ => (0 : (rnModel 0).E 0)) '' ({g} ∩ {g'}) =
      (fun _ => (0 : (rnModel 0).E 0)) '' ({g'} ∩ {g})
    rw [inter_comm]
  have htr : ∀ a b : G, (discreteChart a).transition (discreteChart b) = id := fun _ _ =>
    funext fun _ => rnModel_zero_eq _ _
  refine ⟨?_, ?_⟩
  · rw [htr, ← hO]
    exact isScSmoothRetractMap_id _
  · rw [htr, hO]
    exact isScSmoothRetractMap_id _

open scoped Polyfold.EpGroupoid.NaturalRep in
theorem isScSmoothMap_smul' : type_of% @Polyfold.EpGroupoid.NaturalRep.isScSmoothMap_smul.{0} := by
  intro Obj Mor _ _ _ _ _ _ X x R g
  exact MPolyfold.IsScSmoothMap.codRestrict_restrictOpen R.isOpen_U
    (MPolyfold.IsScSmoothOn.comp (R.isScDiffeoOn_Φ g).isScSmoothOn
      (isScSmoothMap_val' X.PObj R.isOpen_U) fun y _ => y.2) _

theorem B_to_A : B → A := by
  intro _
  refine ⟨@discreteChart_compatible', fun {G} _ _ {X} _ _ _ {PX} {f} =>
    ⟨fun h => continuousOn_univ.1 h.continuousOn, isScSmoothMap_discrete_of_continuous⟩,
    ?_, ?_, isScSmoothMap_smul'⟩
  · intro G _ _ X _ _ _ PX Y _ _ _ PY _ f U hU
    rw [isScSmoothOn_prod_discrete_iff (isOpen_univ.prod hU)]
    have : ∀ g : G, {x | (g, x) ∈ (univ ×ˢ U : Set (G × X))} = U := fun g => by
      ext x
      simp
    simp only [this]
  · intro G _ _ X _ _ _ PX Y _ _ _ PY _ f
    exact isScSmoothOn_prod_discrete_iff isOpen_univ

#rt_check_soft RoundTrip.V7_20.A_to_B [Polyfold.discreteChart_compatible,
  Polyfold.isScSmoothMap_discrete_iff, Polyfold.isScSmoothOn_univ_prod_discrete_iff,
  Polyfold.isScSmoothMap_prod_discrete_iff, Polyfold.EpGroupoid.NaturalRep.isScSmoothMap_smul]
#rt_check_soft RoundTrip.V7_20.B_to_A [Polyfold.discreteChart_compatible,
  Polyfold.isScSmoothMap_discrete_iff, Polyfold.isScSmoothOn_univ_prod_discrete_iff,
  Polyfold.isScSmoothMap_prod_discrete_iff, Polyfold.EpGroupoid.NaturalRep.isScSmoothMap_smul]
#rt_overlap RoundTrip.V7_20.B_to_A [Polyfold.discreteChart_compatible,
  Polyfold.isScSmoothMap_discrete_iff, Polyfold.isScSmoothOn_univ_prod_discrete_iff,
  Polyfold.isScSmoothMap_prod_discrete_iff, Polyfold.EpGroupoid.NaturalRep.isScSmoothMap_smul]

end RoundTrip.V7_20
