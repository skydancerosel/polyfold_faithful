import Polyfold.Chapter11.GapP2_H4Compat
import Polyfold.Chapter11.GapP2_H4CrossChart

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4 "Equivalences and Integration", proof of Theorem 11.4.1 (pp. 543–544;
2017: Theorem 11.8, p. 396), gap G.131.  Numbers and pages are the 2021 text's.

# Oriented tame structures and sheet integrals moved by an sc-diffeomorphism

The proof of Theorem 11.4.1 equips `U(F(x))` with "the branching structure obtained via
`F|U(x)`" and compares the integrals (11.12), (11.13).  This file does this for an
sc-diffeomorphism `f : W → W'` between open subsets of the object spaces of two ep-groupoids:

* `OrientedTameStructure.restrictRep`: an oriented tame structure restricted to a natural
  representation on a smaller neighbourhood;
* `OrientedTameStructure.move`: the structure `(f(Mᵢ ∩ W), f_* oᵢ)`, `(σᵢ)` with a given natural
  representation on `f(U(x))` (Chapter 11's `LocalBranchingStructure.mapDiffeo` with tame sheets
  and orientations), `represents_move`;
* `FormEval.EvCompatOn`: `ω_T(Tf ∘ β) = ω_S(β)` on the frames of the sheet; under it the sheets of
  the class `F.sheets` are carried to sheets of the class (`image_mem_sheets_cross`) and
  `∫_{f(A)} ω_T|(f(N), f_* o) = ∫_A ω_S|(N, o)` (`integ_image_cross`, the step (11.12) → (11.13));
* `sheetSum_move`: the sums `∑ σᵢ ∫_{Aᵢ} ω|(Mᵢ, oᵢ)` of a structure and of its moved structure.
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {n : ℕ}

namespace OrientedTameStructure

variable {Θ : Obj → ℚ} {x : Obj}

/-! ### Restriction to a smaller natural representation -/

/-- **An oriented tame structure restricted to a natural representation `R` on a smaller
neighbourhood** `R.U ⊆ U(x)`: the sheets `Mᵢ ∩ R.U` with the same weights and the restricted
orientations. -/
def restrictRep (C : X.OrientedTameStructure n Θ x) (R : X.NaturalRep x) (hR : R.U ⊆ C.U) :
    X.OrientedTameStructure n Θ x where
  toLocalBranchingStructure := C.toLocalBranchingStructure.restrict R.isOpen_U R.mem_U hR
  rep := R
  U_eq := rfl
  hasPropernessProperty := C.hasPropernessProperty.mono R.isOpen_U hR
  hasTameInducedStructure i := MPolyfold.HasTameInducedStructure.inter_isOpen
    (C.isSmoothSubmanifold i) (C.hasTameInducedStructure i) R.isOpen_U
  isSubmanifoldOfDim i := (C.isSubmanifoldOfDim i).inter_isOpen R.isOpen_U
  orient i := (C.orient i).restrict R.isOpen_U

variable (C : X.OrientedTameStructure n Θ x) (R : X.NaturalRep x) (hR : R.U ⊆ C.U)

@[simp] theorem restrictRep_U : (C.restrictRep R hR).U = R.U := rfl

@[simp] theorem restrictRep_M (i : C.ι) : (C.restrictRep R hR).M i = C.M i ∩ R.U := rfl

theorem represents_restrictRep {T : Obj → X.PObj.OrTangent →₀ ℚ} (hC : C.Represents T) :
    (C.restrictRep R hR).Represents T := by
  classical
  intro y hy hys
  rw [hC y (hR hy) hys, C.orientedSum_eq_sum_ite, (C.restrictRep R hR).orientedSum_eq_sum_ite]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hiff : y ∈ (C.restrictRep R hR).M i ↔ y ∈ C.M i := ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩
  have ht : ((C.restrictRep R hR).orient i).tangent y = (C.orient i).tangent y :=
    (C.orient i).restrict_tangent R.isOpen_U hy
  by_cases h : y ∈ C.M i
  · rw [if_pos h, if_pos (hiff.2 h), ht]
    rfl
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

theorem restrictRep_mem_sheets {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {F : X.FormEval n Ω}
    (hC : ∀ i, C.M i ∈ F.sheets) (i : C.ι) : (C.restrictRep R hR).M i ∈ F.sheets :=
  FormEval.inter_mem_sheets (hC i) R.isOpen_U

/-! ### Moving a structure by an sc-diffeomorphism -/

variable {Θ' : Obj' → ℚ} {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}

theorem mapU_eq (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hUW : C.U ⊆ W) :
    C.toLocalBranchingStructure.mapU g W W' = f '' C.U := by
  ext z
  constructor
  · rintro ⟨hzW', hzU, -⟩
    exact ⟨g z, hzU, hf.right_inv z hzW'⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hf.mapsTo (hUW hu), by rw [mem_preimage, hf.left_inv u (hUW hu)]; exact ⟨hu, hUW hu⟩⟩

/-- **The oriented tame structure moved by an sc-diffeomorphism** `f : W → W'`, `U(x) ⊆ W`
(the structure "obtained via `F|U(x)`" of the proof of Theorem 11.4.1): the sheets
`f(Mᵢ ∩ W)` with the weights `σᵢ` and the orientations `f_* oᵢ`, on `f(U(x))` with a given
natural representation `R'` of `G_{f(x)}` having the properness property. -/
def move (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hUW : C.U ⊆ W) {y : Obj'} (hxy : f x = y)
    (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u) (R' : Y.NaturalRep y) (hR' : R'.U = f '' C.U)
    (hP : Y.HasPropernessProperty (f '' C.U)) : Y.OrientedTameStructure n Θ' y where
  toLocalBranchingStructure := C.toLocalBranchingStructure.mapDiffeo hf (hUW C.mem_U) hxy hΘ
  rep := R'
  U_eq := (C.mapU_eq hf hUW).trans hR'.symm
  hasPropernessProperty := by
    change Y.HasPropernessProperty (C.toLocalBranchingStructure.mapU g W W')
    rw [C.mapU_eq hf hUW]; exact hP
  hasTameInducedStructure i := MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn
    ((C.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen)
    (MPolyfold.HasTameInducedStructure.inter_isOpen (C.isSmoothSubmanifold i)
      (C.hasTameInducedStructure i) hf.isScSmoothOn.isOpen) hf inter_subset_right
  isSubmanifoldOfDim i := ((C.isSubmanifoldOfDim i).inter_isOpen
    hf.isScSmoothOn.isOpen).image_isScDiffeoOn hf inter_subset_right
  orient i := ((C.orient i).restrict hf.isScSmoothOn.isOpen).mapDiffeo
    ((C.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen) hf inter_subset_right

variable (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hUW : C.U ⊆ W) {y : Obj'} (hxy : f x = y)
  (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u) (R' : Y.NaturalRep y) (hR' : R'.U = f '' C.U)
  (hP : Y.HasPropernessProperty (f '' C.U))

theorem move_U : (C.move hf hUW hxy hΘ R' hR' hP).U = f '' C.U := C.mapU_eq hf hUW

@[simp] theorem move_M (i : C.ι) : (C.move hf hUW hxy hΘ R' hR' hP).M i = f '' (C.M i ∩ W) :=
  rfl

theorem move_M_eq (i : C.ι) : (C.move hf hUW hxy hΘ R' hR' hP).M i = f '' C.M i := by
  rw [move_M, inter_eq_left.2 ((C.subset_U i).trans hUW)]

@[simp] theorem move_σ : (C.move hf hUW hxy hΘ R' hR' hP).σ = C.σ := rfl

theorem toOriented_move : (C.move hf hUW hxy hΘ R' hR' hP).toOriented =
    C.toOriented.mapDiffeo hf (hUW C.mem_U) hxy hΘ := rfl

/-- **The moved structure describes the moved orientation**: if `T'(z) = Tf_*(T(f⁻¹ z))` on
`f(U(x))` (at the points of `Y_∞`, whose preimages lie in `X_∞`), the moved structure describes
`T'`. -/
theorem represents_move {T : Obj → X.PObj.OrTangent →₀ ℚ} {T' : Obj' → Y.PObj.OrTangent →₀ ℚ}
    (hC : C.Represents T)
    (hT : ∀ z ∈ f '' C.U, z ∈ Y.PObj.smoothSet → g z ∈ X.PObj.smoothSet ∧
      T' z = (T (g z)).mapDomain (MPolyfold.OrTangent.map (MPolyfold.tangentMapOn
        hf.isScSmoothOn))) :
    (C.move hf hUW hxy hΘ R' hR' hP).Represents T' := by
  intro z hz hzs
  have hz' : z ∈ (C.toOriented.mapDiffeo hf (hUW C.mem_U) hxy hΘ).U := hz
  have hzU : z ∈ f '' C.U := (C.move_U hf hUW hxy hΘ R' hR' hP) ▸ hz
  obtain ⟨hgs, hT'⟩ := hT z hzU hzs
  rw [toOriented_move, OrientedBranchingStructure.orientedSum_mapDiffeo _ hf (hUW C.mem_U) hxy hΘ
    hz', hT', hC (g z) hz'.2.1 hgs]

end OrientedTameStructure

/-! ### Integrals over moved sheets -/

namespace FormEval

variable {ΩS ΩT : Type*} [AddCommGroup ΩS] [Module ℝ ΩS] [AddCommGroup ΩT] [Module ℝ ΩT]
  {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}

/-- **`ω_T(Tf β₁, …, Tf βₙ) = ω_S(β₁, …, βₙ)` on the tangent spaces of `N`**: the form `ω_T` on
`Y` is moved to `ω_S` on `X` by the sc-diffeomorphism `f`. -/
def EvCompatOn (FS : X.FormEval n ΩS) (FT : Y.FormEval n ΩT)
    (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (N : Set Obj) (ωS : ΩS) (ωT : ΩT) : Prop :=
  ∀ y ∈ N, ∀ β : Fin n → X.PObj.TangentSpace, (∀ i, β i ∈ X.PObj.submanifoldTangent N y) →
    FT.ev ωT (fun i => MPolyfold.tangentMapOn hf.isScSmoothOn (β i)) = FS.ev ωS β

variable {FS : X.FormEval n ΩS} {FT : Y.FormEval n ΩT}
  (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') {N : Set Obj}

/-- **The image of a sheet of the class is a sheet of the class**, if every form of `ΩT` is moved
to a form of `ΩS` on the sheet. -/
theorem image_mem_sheets_cross (hN : N ∈ FS.sheets) (hNW : N ⊆ W)
    (hcomp : ∀ ωT : ΩT, ∃ ωS : ΩS, EvCompatOn FS FT hf N ωS ωT) : f '' N ∈ FT.sheets := by
  refine ⟨hN.1.image_isScDiffeoOn hf hNW, (chart hN).mapDiffeoCross hN.1.1 hf hNW,
    fun ωT => ?_⟩
  obtain ⟨ωS, hω⟩ := hcomp ωT
  rw [(chart hN).mapDiffeoCross_dom hN.1.1 hf hNW]
  refine (integrableOn_chart hN ωS).congr_fun (fun u hu => ?_) (chart hN).measurableSet_dom'
  have hq := (chart hN).q_mem hu
  change _ = FT.ev ωT (((chart hN).mapDiffeoCross hN.1.1 hf hNW).tvec (f ((chart hN).q u)))
  have htv : ((chart hN).mapDiffeoCross hN.1.1 hf hNW).tvec (f ((chart hN).q u)) =
      fun i => MPolyfold.tangentMapOn hf.isScSmoothOn ((chart hN).tvec ((chart hN).q u) i) :=
    funext fun i => (chart hN).mapDiffeoCross_tvec hN.1.1 hf hNW hq i
  rw [htv, hω _ hq _ ((chart hN).tvec_mem hq)]

/-- The chart integral in the moved graph chart, for the moved orientation, over `f(A)`. -/
theorem chartInteg_mapDiffeoCross (hN : X.PObj.IsSmoothSubmanifold N)
    (c : X.PObj.GraphChart n N) (o : X.PObj.SubmanifoldOrientation N n) (hNW : N ⊆ W)
    {ωS : ΩS} {ωT : ΩT} (hω : EvCompatOn FS FT hf N ωS ωT) {A : Set Obj} (hA : A ⊆ N)
    (hAm : NullMeasurableSet (c.coord '' A) volume) :
    FT.chartInteg (c.mapDiffeoCross hN hf hNW) ωT (o.mapDiffeo hN hf hNW).tangent (f '' A) =
      FS.chartInteg c ωS o.tangent A := by
  have hAN : A ∩ N = A := inter_eq_left.2 hA
  have hAN' : f '' A ∩ f '' N = f '' A := inter_eq_left.2 (image_mono hA)
  have himg : (c.mapDiffeoCross hN hf hNW).coord '' (f '' A) = c.coord '' A := by
    rw [image_image]
    exact image_congr fun y hy => c.mapDiffeoCross_coord hN hf hNW (hA hy)
  unfold chartInteg
  rw [hAN, hAN', himg]
  refine setIntegral_congr_ae₀ hAm (Filter.Eventually.of_forall ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hyN := hA hy
  change FT.density _ ωT _ (f (c.q (c.coord y))) = FS.density c ωS o.tangent (c.q (c.coord y))
  rw [c.q_coord' hyN]
  have htv : (c.mapDiffeoCross hN hf hNW).tvec (f y) =
      fun i => MPolyfold.tangentMapOn hf.isScSmoothOn (c.tvec y i) :=
    funext fun i => c.mapDiffeoCross_tvec hN hf hNW hyN i
  simp only [density, MPolyfold.GraphChart.frameSgn_tangent, htv]
  rw [hω y hyN (c.tvec y) (c.tvec_mem hyN)]
  have hiff := o.mapDiffeo_frames_iff_cross hN hf hNW hyN (c.tvec y)
    (fun i => MPolyfold.levelVal_tangentProj_of_mem (c.tvec_mem hyN i))
  rw [← htv] at hiff
  by_cases h : c.tvec y ∈ o.frames y
  · rw [if_pos h, if_pos (hiff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

/-- **(11.12) = (11.13) for one sheet**: `∫_{f(A)} ω_T|(f(N), f_* o) = ∫_A ω_S|(N, o)` for a
sheet `N` of the class, `f(N)` of the class, and `A` measurable in `N`. -/
theorem integ_image_cross (hN : N ∈ FS.sheets) (hfN : f '' N ∈ FT.sheets) (hNW : N ⊆ W)
    (o : X.PObj.SubmanifoldOrientation N n) {ωS : ΩS} {ωT : ΩT}
    (hω : EvCompatOn FS FT hf N ωS ωT) {A : Set Obj} (hA : FS.sheetNull.IsMeasIn N A)
    {B : Set Obj'} (hB : B ∩ f '' N = f '' (A ∩ N)) :
    FT.integ ωT (f '' N) (o.mapDiffeo hN.1.1 hf hNW).tangent B = FS.integ ωS N o.tangent A := by
  rw [integ_eq hfN, integ_eq hN]
  have hAm : NullMeasurableSet ((chart hN).coord '' (A ∩ N)) volume :=
    nullMeasurableSet_coord_image (chart hN) hA
  have h1 : FT.chartInteg (chart hfN) ωT (o.mapDiffeo hN.1.1 hf hNW).tangent B =
      FT.chartInteg (chart hfN) ωT (o.mapDiffeo hN.1.1 hf hNW).tangent (f '' (A ∩ N)) := by
    unfold chartInteg; rw [hB, inter_eq_left.2 (image_mono inter_subset_right)]
  have h2 : FS.chartInteg (chart hN) ωS o.tangent A =
      FS.chartInteg (chart hN) ωS o.tangent (A ∩ N) := by
    unfold chartInteg; rw [inter_assoc, inter_self]
  rw [h1, h2]
  have hsub : f '' (A ∩ N) ⊆ f '' N ∩ f '' N := fun z hz =>
    ⟨image_mono inter_subset_right hz, image_mono inter_subset_right hz⟩
  have hAm' : NullMeasurableSet (((chart hN).mapDiffeoCross hN.1.1 hf hNW).coord ''
      (f '' (A ∩ N))) volume := by
    rw [image_image]
    refine (image_congr fun y hy => ?_).symm ▸ hAm
    exact ((chart hN).mapDiffeoCross_coord hN.1.1 hf hNW hy.2)
  rw [← FT.chartInteg_congr (hN.1.image_isScDiffeoOn hf hNW) hfN.1
    ((chart hN).mapDiffeoCross hN.1.1 hf hNW) (chart hfN) (o.mapDiffeo hN.1.1 hf hNW)
    (o.mapDiffeo hN.1.1 hf hNW) ωT hsub hAm' fun _ _ => rfl]
  exact chartInteg_mapDiffeoCross hf hN.1.1 (chart hN) o hNW hω inter_subset_right hAm

end FormEval

/-! ### The sums of (9.20) for a moved structure -/

namespace OrientedTameStructure

variable {Θ : Obj → ℚ} {Θ' : Obj' → ℚ} {x : Obj} (C : X.OrientedTameStructure n Θ x)
  {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}
  {ΩS ΩT : Type*} [AddCommGroup ΩS] [Module ℝ ΩS] [AddCommGroup ΩT] [Module ℝ ΩT]
  {FS : X.FormEval n ΩS} {FT : Y.FormEval n ΩT}

/-- **(11.12) = (11.13)**: for a structure `C` with sheets in the class and its moved structure,
`∑ σᵢ ∫_{B ∩ f(Mᵢ)} ω_T|(f(Mᵢ), f_* oᵢ) = ∑ σᵢ ∫_{A ∩ Mᵢ} ω_S|(Mᵢ, oᵢ)` whenever `B` meets
`f(Mᵢ)` in `f(A ∩ Mᵢ)`, `A` is measurable, and `ω_T` is moved to `ω_S` on the sheets. -/
theorem sheetSum_move (hn : 0 < n) (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hUW : C.U ⊆ W)
    {y : Obj'} (hxy : f x = y) (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u) (R' : Y.NaturalRep y)
    (hR' : R'.U = f '' C.U) (hP : Y.HasPropernessProperty (f '' C.U))
    (hS : ∀ i, C.M i ∈ FS.sheets) (hS' : ∀ i, (C.move hf hUW hxy hΘ R' hR' hP).M i ∈ FT.sheets)
    {ωS : ΩS} {ωT : ΩT} (hω : ∀ i, FormEval.EvCompatOn FS FT hf (C.M i ∩ W) ωS ωT)
    {A : Set Obj} (hA : C.IsMeas FS.sheetNull A) {B : Set Obj'}
    (hB : ∀ i, B ∩ f '' C.M i = f '' (A ∩ C.M i)) :
    (C.move hf hUW hxy hΘ R' hR' hP).sheetSum (FT.sheetIntegration hn) ωT B =
      C.sheetSum (FS.sheetIntegration hn) ωS A := by
  unfold sheetSum
  refine Finset.sum_congr rfl fun i _ => ?_
  have hMW : C.M i ∩ W = C.M i := inter_eq_left.2 ((C.subset_U i).trans hUW)
  have hNi : C.M i ∩ W ∈ FS.sheets := by rw [hMW]; exact hS i
  have hAi : FS.sheetNull.IsMeasIn (C.M i ∩ W) (A ∩ C.M i) := by
    rw [hMW]; exact (hA i).congr_inter (by rw [inter_assoc, inter_self])
  congr 1
  simp only [FormEval.sheetIntegration_integ]
  have hB' : (B ∩ f '' (C.M i ∩ W)) ∩ f '' (C.M i ∩ W) = f '' ((A ∩ C.M i) ∩ (C.M i ∩ W)) := by
    rw [hMW, inter_assoc, inter_self, hB i, inter_assoc, inter_self]
  have key := FormEval.integ_image_cross hf hNi (hS' i) inter_subset_right
    ((C.orient i).restrict hf.isScSmoothOn.isOpen) (hω i) hAi hB'
  refine key.trans ?_
  have hMU : C.M i ⊆ W := (C.subset_U i).trans hUW
  exact (FS.sheetIntegration hn).integ_congr ωS _ hNi _ (hS i) _ _ _
    (fun z hz => ⟨⟨hz.2, hMU hz.2⟩, hz.2⟩) hAi
    (fun z hz => (C.orient i).restrict_tangent _ (hMU hz.2))

end OrientedTameStructure

end EpGroupoid

end Polyfold
