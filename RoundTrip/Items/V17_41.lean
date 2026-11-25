import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_41

set_option maxSynthPendingDepth 3

/-! Round trip for V17_41 (2021 Proposition 17.2.4, p. 769: `T_αC` is Banachable, the charts
`S_Ψ` are topological linear isomorphisms with `S_{Ψ'} ∘ S_Ψ⁻¹ = Tσ(q)`, and `T_αC` is
sc-Banachable for smooth `α`).

`A` is the conjunction of the types of `proposition_17_2_4`, `proposition_17_2_4_banachable` and
`proposition_17_2_4_sc` (the definitions `tangentChartCLE`, `tangentNormedAddCommGroup` are
vocabulary), with `u := 0`.

* `A_to_B`: the structure on `T_αC` is the project's (through the reference chart; `Fact` from
  `B`'s hypotheses).  Banachable: `S_{Ψ_α}` (from `proposition_17_2_4`) followed by the chart
  isomorphism `T_qO ≃L T_{φ(q)}O ⊆ E₀`, a closed subspace of a Banach space.  The charts and the
  transition formula: `proposition_17_2_4` (`transTangent` and `transTangentCLM` have the same
  underlying map).  sc-Banachable: `E := (T_{φ₀(q₀)}O, induced filtration)` for a reference
  `(Ψ₀, q₀, φ₀)`, an sc-Banach space since it is an sc-subspace (`proposition_17_2_4_sc`); for any
  other `(Ψ, q, φ)` the sc-operators `L : E⁰ → F⁰`, `L' : F⁰ → E⁰` of `proposition_17_2_4_sc` (both
  directions) restrict on every level `m` to mutually inverse continuous linear maps between
  `E_m` and `T_{φ(q)}O ∩ F_m`.
* `B_to_A`: `A`'s three statements concern the project's own structure on `T_αC` (instances
  through the reference chart), which `B` does not mention (it asserts that *some* structure
  exists); they are proved outright from non-item lemmas (`coe_tangentChartCLE`,
  `tangentChart_symm_trans`, and copies of the project's proofs of the Banach and sc parts).  The
  direction is therefore proved without using `B`.
-/

namespace RoundTrip.V17_41
open Polyfold Polyfold.GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4_banachable.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4_sc.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4.{0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4_banachable.{0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4_sc.{0}⟩

/-! ### `A ⇒ B` -/

/-- `A` (`F₀ ⊇ A`) as a subtype equals its level-`0` part `levelSub A 0`. -/
def levelZeroEquiv (F : ScBanach) (A : Submodule ℝ (F.lvl 0)) :
    ↥A ≃L[ℝ] ↥(F.levelSub A 0) :=
  ContinuousLinearEquiv.ofEq _ _ (F.levelSub_zero A).symm

section Sc

variable {C : GCT.{0}} {S : C.PolyfoldConstruction} {α : C.Obj}

/-- The sc part of `A ⇒ B`. -/
theorem sc_of_A (hsc : type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4_sc.{0})
    [Fact (S.TangentObj α)] (hs : S.IsSmoothObj α) (Ψ₀ : S.Unif) (hΨ₀ : Ψ₀.1 ∈ S.F α)
    (x₀ : Ψ₀.1.P.Level 1) (hx₀ : Ψ₀.1.obj (Ψ₀.1.P.levelVal 1 x₀) = α)
    (E₀ : S.TangentSpaceAt α ≃L[ℝ] ↑(Ψ₀.1.P.tangentFiber x₀))
    (hE₀ : ⇑E₀ = ⇑(S.tangentChart Ψ₀ hΨ₀ x₀ hx₀)) :
    ∃ (E : ScBanach) (e : S.TangentSpaceAt α ≃L[ℝ] E.lvl 0),
      ∀ (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
        (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) (φ : MChart Ψ.1.O) (hφ : Ψ.1.P.IsChart φ)
        (hq : Ψ.1.P.levelVal 1 x ∈ φ.source),
        IsScIsoOnto E φ.model.E (MPolyfold.tangentFiberModel hφ hq)
          (fun y => ((Ψ.1.P.tangentFiberContinuousLinearEquiv hφ hq
            (S.tangentChart Ψ hΨ x hx (e.symm y)) : _) : φ.model.E.lvl 0)) := by
  have hφ₀ := Ψ₀.1.P.isChart_fiberChart x₀
  have hq₀ := Ψ₀.1.P.mem_fiberChart_source x₀
  set φ₀ := Ψ₀.1.P.fiberChart x₀
  obtain ⟨hA₀, -⟩ := hsc α hs Ψ₀ hΨ₀ x₀ hx₀ hφ₀ hq₀
  set A₀ := MPolyfold.tangentFiberModel hφ₀ hq₀
  let E := φ₀.model.E.ofSubspace hA₀
  let e : S.TangentSpaceAt α ≃L[ℝ] E.lvl 0 :=
    (E₀.trans (Ψ₀.1.P.tangentFiberContinuousLinearEquiv hφ₀ hq₀)).trans
      (levelZeroEquiv φ₀.model.E A₀)
  -- the reference chart in the model: `Tφ₀ ∘ S_{Ψ₀}`
  let T₀ : S.TangentSpaceAt α → φ₀.model.E.lvl 0 := fun t =>
    ((MPolyfold.tangentFiberEquiv hφ₀ hq₀ (S.tangentChart Ψ₀ hΨ₀ x₀ hx₀ t) : A₀) : _)
  let val : E.lvl 0 → φ₀.model.E.lvl 0 := fun y => (y : φ₀.model.E.levelSub A₀ 0).1
  have he : ∀ t, val (e t) = T₀ t := by
    intro t
    have h := congrFun hE₀ t
    rw [show T₀ t = ((MPolyfold.tangentFiberEquiv hφ₀ hq₀ (E₀ t) : A₀) : _) by rw [h]]
    rfl
  have hsurj₀ : ∀ (v : φ₀.model.E.lvl 0) (hv : v ∈ A₀),
      T₀ (e.symm (show φ₀.model.E.levelSub A₀ 0 from ⟨v, hv⟩)) = v := by
    intro v hv
    exact (he _).symm.trans (congrArg val (e.apply_symm_apply _))
  refine ⟨E, e, fun Ψ hΨ x hx φ hφ hq => ?_⟩
  set Aφ := MPolyfold.tangentFiberModel hφ hq
  let T : S.TangentSpaceAt α → φ.model.E.lvl 0 := fun t =>
    ((MPolyfold.tangentFiberEquiv hφ hq (S.tangentChart Ψ hΨ x hx t) : Aφ) : _)
  have hTmem : ∀ t, T t ∈ Aφ := fun t => (MPolyfold.tangentFiberEquiv hφ hq _).2
  have hT₀mem : ∀ t, T₀ t ∈ A₀ := fun t => (MPolyfold.tangentFiberEquiv hφ₀ hq₀ _).2
  have hsurj : ∀ (w : φ.model.E.lvl 0) (hw : w ∈ Aφ), T ((S.tangentChart Ψ hΨ x hx).symm
      ((MPolyfold.tangentFiberEquiv hφ hq).symm ⟨w, hw⟩)) = w := by
    intro w hw
    change ((MPolyfold.tangentFiberEquiv hφ hq (S.tangentChart Ψ hΨ x hx
      ((S.tangentChart Ψ hΨ x hx).symm _)) : Aφ) : _) = w
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  obtain ⟨L, hL, hLc⟩ := (hsc α hs Ψ₀ hΨ₀ x₀ hx₀ hφ₀ hq₀).2 Ψ hΨ x hx hφ hq
  obtain ⟨L', hL', hLc'⟩ := (hsc α hs Ψ hΨ x hx hφ hq).2 Ψ₀ hΨ₀ x₀ hx₀ hφ₀ hq₀
  -- `L` maps `A₀` onto `Aφ` with inverse `L'`
  have hLA : ∀ v ∈ A₀, L v ∈ Aφ ∧ L' (L v) = v := by
    intro v hv
    obtain ⟨t, rfl⟩ : ∃ t, T₀ t = v := ⟨_, hsurj₀ v hv⟩
    have h1 : L (T₀ t) = T t := (hLc t).symm
    refine ⟨h1 ▸ hTmem t, ?_⟩
    rw [h1]
    exact (hLc' t).symm
  have hLA' : ∀ w ∈ Aφ, L' w ∈ A₀ ∧ L (L' w) = w := by
    intro w hw
    obtain ⟨t, rfl⟩ : ∃ t, T t = w := ⟨_, hsurj w hw⟩
    have h1 : L' (T t) = T₀ t := (hLc' t).symm
    refine ⟨h1 ▸ hT₀mem t, ?_⟩
    rw [h1]
    exact (hLc t).symm
  have key : ∀ y : E.lvl 0, (fun y => ((Ψ.1.P.tangentFiberContinuousLinearEquiv hφ hq
      (S.tangentChart Ψ hΨ x hx (e.symm y)) : _) : φ.model.E.lvl 0)) y = L (val y) := by
    intro y
    have h2 : T₀ (e.symm y) = val y :=
      (he (e.symm y)).symm.trans (congrArg val (e.apply_symm_apply y))
    exact (hLc _).trans (congrArg L h2)
  refine ⟨fun m => ?_, ?_⟩
  · let Lm := (hL m).choose
    have hLm := (hL m).choose_spec
    let L'm := (hL' m).choose
    have hL'm := (hL' m).choose_spec
    have hf : ∀ y : φ₀.model.E.levelSub A₀ m, Lm y.1 ∈ φ.model.E.levelSub Aφ m := by
      intro y
      rw [ScBanach.mem_levelSub, hLm]
      exact (hLA _ y.2).1
    have hg : ∀ y : φ.model.E.levelSub Aφ m, L'm y.1 ∈ φ₀.model.E.levelSub A₀ m := by
      intro y
      rw [ScBanach.mem_levelSub, hL'm]
      exact (hLA' _ y.2).1
    exact ContinuousLinearEquiv.equivOfInverse
      ((Lm.comp (φ₀.model.E.levelSub A₀ m).subtypeL).codRestrict _ hf)
      ((L'm.comp (φ.model.E.levelSub Aφ m).subtypeL).codRestrict _ hg)
      (fun y => Subtype.ext (φ₀.model.E.toBase_injective m (by
        change φ₀.model.E.toBase m (L'm (Lm y.1)) = _
        rw [hL'm, hLm]
        exact (hLA _ y.2).2)))
      (fun y => Subtype.ext (φ.model.E.toBase_injective m (by
        change φ.model.E.toBase m (Lm (L'm y.1)) = _
        rw [hLm, hL'm]
        exact (hLA' _ y.2).2)))
  · intro m y
    rw [key]
    change φ.model.E.toBase m (Classical.choose (hL m) y.1) = _
    rw [Classical.choose_spec (hL m)]
    exact congrArg L (ScBanach.ofSubspace_toBase_coe hA₀ m y).symm

end Sc

theorem A_to_B : A → B := by
  rintro ⟨h4, -, hsc⟩
  intro C S α hreg hne
  haveI hF : Fact (S.TangentObj α) := ⟨⟨hreg, hne⟩⟩
  have hΨ₀ := refUnif_mem hF.out
  have hx₀ := obj_refPoint hF.out
  obtain ⟨E₀, hE₀⟩ := (h4 α _ hΨ₀ _ hx₀).1
  have hφ₀ := (S.refUnif hF.out).1.P.isChart_fiberChart (S.refPoint hF.out)
  have hq₀ := (S.refUnif hF.out).1.P.mem_fiberChart_source (S.refPoint hF.out)
  refine ⟨(inferInstance : AddCommGroup (S.TangentSpaceAt α)),
    (inferInstance : Module ℝ (S.TangentSpaceAt α)),
    (inferInstance : TopologicalSpace (S.TangentSpaceAt α)), ?_, ?_, ?_, ?_⟩
  · exact ⟨_, inferInstance, inferInstance, inferInstance,
      ⟨E₀.trans ((S.refUnif hF.out).1.P.tangentFiberContinuousLinearEquiv hφ₀ hq₀)⟩⟩
  · exact fun Ψ hΨ x hx => (h4 α Ψ hΨ x hx).1
  · intro Ψ hΨ x hx Ψ' hΨ' x' hx' v
    exact (h4 α Ψ hΨ x hx).2 Ψ' hΨ' x' hx' v
  · intro hs
    exact sc_of_A hsc hs _ hΨ₀ _ hx₀ E₀ hE₀

/-! ### `B ⇒ A` (outright: `A` is about the project's own structure on `T_αC`) -/

section Copies

variable {C : GCT.{0}} {S : C.PolyfoldConstruction} (α : C.Obj)

theorem p4' [hα : Fact (S.TangentObj α)] (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α)
    (x : Ψ.1.P.Level 1) (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) :
    (∃ E : S.TangentSpaceAt α ≃L[ℝ] Ψ.1.P.tangentFiber x, ⇑E = S.tangentChart Ψ hΨ x hx) ∧
      ∀ (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α) (x' : Ψ'.1.P.Level 1)
        (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α) (v : Ψ.1.P.tangentFiber x),
        S.tangentChart Ψ' hΨ' x' hx' ((S.tangentChart Ψ hΨ x hx).symm v) =
          S.transTangent (S.unitTr _ _ hx hx') rfl rfl v :=
  ⟨⟨S.tangentChartCLE α Ψ x hx, coe_tangentChartCLE α Ψ hΨ x hx⟩,
    fun Ψ' hΨ' x' hx' v => tangentChart_symm_trans Ψ hΨ x hx Ψ' hΨ' x' hx' v⟩

theorem banachable' [hα : Fact (S.TangentObj α)] (Ψ : S.Unif) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) {φ : MChart Ψ.1.O} (hφ : Ψ.1.P.IsChart φ)
    (hxφ : Ψ.1.P.levelVal 1 x ∈ φ.source) :
    @UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
        (S.tangentNormedAddCommGroup α Ψ x hx hφ hxφ).toPseudoMetricSpace) =
      (inferInstance : TopologicalSpace (S.TangentSpaceAt α)) ∧
    @CompleteSpace (S.TangentSpaceAt α) (@PseudoMetricSpace.toUniformSpace _
        (S.tangentNormedAddCommGroup α Ψ x hx hφ hxφ).toPseudoMetricSpace) := by
  set L := (S.tangentChartCLE α Ψ x hx).trans (MPolyfold.tangentFiberContinuousLinearEquiv hφ hxφ)
  refine ⟨(UniformSpace.toTopologicalSpace_comap).trans L.toHomeomorph.isInducing.eq_induced.symm,
    ?_⟩
  let _ := S.tangentNormedAddCommGroup α Ψ x hx hφ hxφ
  exact (IsometryEquiv.completeSpace_iff
    ⟨L.toLinearEquiv.toEquiv, Isometry.of_dist_eq fun _ _ => rfl⟩).2 inferInstance

theorem sc' (hs : S.IsSmoothObj α) (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α)
    (x : Ψ.1.P.Level 1) (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) {φ : MChart Ψ.1.O}
    (hφ : Ψ.1.P.IsChart φ) (hxφ : Ψ.1.P.levelVal 1 x ∈ φ.source) :
    φ.model.E.IsScSubspace (MPolyfold.tangentFiberModel hφ hxφ) ∧
      ∀ (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α) (x' : Ψ'.1.P.Level 1)
        (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α) {φ' : MChart Ψ'.1.O}
        (hφ' : Ψ'.1.P.IsChart φ') (hxφ' : Ψ'.1.P.levelVal 1 x' ∈ φ'.source),
        ∃ L : φ.model.E 0 →L[ℝ] φ'.model.E 0, IsScOperator L ∧
          ∀ e : S.TangentSpaceAt α,
            (MPolyfold.tangentFiberEquiv hφ' hxφ' (S.tangentChart Ψ' hΨ' x' hx' e) :
              φ'.model.E 0) =
              L (MPolyfold.tangentFiberEquiv hφ hxφ (S.tangentChart Ψ hΨ x hx e)) := by
  have hsm : ∀ (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
      (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α), Ψ.1.P.levelVal 1 x ∈ Ψ.1.P.smoothSet :=
    fun Ψ hΨ x hx => Set.mem_iInter.2 fun m => (regularity_eq_of_mem hΨ hx m).1 (hs m)
  refine ⟨MPolyfold.isScSubspace_tangentFiberModel hφ hxφ (hsm Ψ hΨ x hx),
    fun Ψ' hΨ' x' hx' φ' hφ' hxφ' => ?_⟩
  set a := S.unitTr (Ψ.1.P.levelVal 1 x) (Ψ'.1.P.levelVal 1 x') hx hx'
  have hxU : Ψ.1.P.levelVal 1 x ∈ (S.triple a).srcSet := (S.triple a).src_mem
  have hxy : (S.triple a).sigma (Ψ.1.P.levelVal 1 x) = Ψ'.1.P.levelVal 1 x' :=
    (S.triple a).sigma_src
  obtain ⟨L, hL, hLs⟩ := MPolyfold.exists_clm_tangentMapOnFiber (S.triple a).isScSmoothOn_sigma
    hxU hxy hφ hφ' hxφ hxφ'
  refine ⟨L, hLs (hsm Ψ hΨ x hx), fun e => ?_⟩
  have h := tangentChart_symm_trans Ψ hΨ x hx Ψ' hΨ' x' hx' (S.tangentChart Ψ hΨ x hx e)
  rw [Equiv.symm_apply_apply] at h
  rw [h, ← hL]
  exact congrArg (fun w => (MPolyfold.tangentFiberEquiv hφ' hxφ' w : φ'.model.E 0))
    (MPolyfold.tangentMapOnCLM_eq _ _ _ _)

end Copies

theorem B_to_A : B → A := fun _ =>
  ⟨fun α _ => p4' α, fun α _ => banachable' α, fun α hs => sc' α hs⟩

#rt_check RoundTrip.V17_41.A_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4_banachable,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4_sc]
#rt_check RoundTrip.V17_41.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4_banachable,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4_sc]
#rt_overlap RoundTrip.V17_41.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4_banachable,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_4_sc]

end RoundTrip.V17_41
