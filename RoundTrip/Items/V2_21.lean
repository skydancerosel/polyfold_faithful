import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_21

/-! Round trip for V2_21 (`TX` is an M-polyfold, `p : TX → X¹` sc-smooth).

`A` is the conjunction of the types of the listed theorems
`Polyfold.MPolyfold.tangentChart_overlap`, `.tangentChart_transition`, `.tangentChart_compatible`,
`.tangentProj_isScSmooth` (at universe `0`; B lives in `Type`) and
`.isScSmoothRetractMap_tangent_fst` (no universe parameter).  `tangentChart`, `tangentAtlas`,
`tangentPolyfold` are definitions (vocabulary).

Glue:
* B's topology `τB P` is the project's instance (`τB_eq`), B's `Tφ` (`TφB`) is the project's
  `tangentChartMap` on `TV`, B's `TO`/`TC` are `retractTangent`/`tangentSet`, B's chart
  `(TV, Tφ, (TO, TC, TE))` is `tangentChart hφ α₀` (any junk value `α₀`; when `TX` is empty, `TV`
  and `TO` are empty).
* B's (f) states `pr₁ : TO → O₁` sc-smooth into `E^1 = E.shiftAdd 1` (levels `E_{1+m}`), the project
  into `E¹ = E.shift` (levels `E_{m+1}`); they are sc-isomorphic with the identity on level `0`
  (`shiftIso`), so the two statements are equivalent (`fst_iff`).
* `B → A` for `isScSmoothRetractMap_tangent_fst` (any retract, no M-polyfold) uses B for the
  M-polyfold `O` with the single chart `id` (`LocalModel.toMPolyfold`); `O = ∅` is trivial. -/

namespace RoundTrip.V2_21
open Polyfold Set MPolyfold TopologicalSpace

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.tangentChart_overlap.{0}) ∧
    (type_of% @Polyfold.MPolyfold.tangentChart_transition.{0}) ∧
    (type_of% @Polyfold.MPolyfold.tangentChart_compatible.{0}) ∧
    (type_of% @Polyfold.MPolyfold.isScSmoothRetractMap_tangent_fst) ∧
    (type_of% @Polyfold.MPolyfold.tangentProj_isScSmooth.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.tangentChart_overlap.{0}, @Polyfold.MPolyfold.tangentChart_transition.{0},
    @Polyfold.MPolyfold.tangentChart_compatible.{0},
    @Polyfold.MPolyfold.isScSmoothRetractMap_tangent_fst,
    @Polyfold.MPolyfold.tangentProj_isScSmooth.{0}⟩

section Glue

/-! #### Retract-level glue -/

/-- `E¹ ≅ E^1`, the identity on level `0`. -/
noncomputable def shiftIso (E : ScBanach) : ScIso E.shift (E.shiftAdd 1) :=
  (E.shiftAddZeroIso.shift).trans (E.shiftAddShiftIso 0)

theorem shiftIso_zero (E : ScBanach) (x : E.shift 0) : (shiftIso E 0 x : E 1) = x := rfl

theorem shiftIso_symm_zero (E : ScBanach) (y : (E.shiftAdd 1) 0) :
    ((shiftIso E).symm 0 y : E 1) = y :=
  (shiftIso_zero E _).symm.trans ((shiftIso E 0).apply_symm_apply y)

/-- B's `TO = {(r(x), Dr(x)h)}` is the project's `Tr(TU)`. -/
theorem TOB_eq {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C) : TOB R = R.tangent := by
  ext p
  rw [R.mem_tangent_iff_exists]
  constructor
  · rintro ⟨x₁, hx₁, h, h1, h2⟩
    refine ⟨x₁, hx₁, h, Prod.ext ?_ h2⟩
    apply E.toBase_injective 1
    change E.toBase 1 p.1 = E.toBase 1 (levelMap R.toFun 1 x₁)
    rw [R.isSc1.isSc0.toBase_levelMap (m := 1) (x := x₁) hx₁]; exact h1
  · rintro ⟨x, hx, h, rfl⟩
    exact ⟨x, hx, h, R.isSc1.isSc0.toBase_levelMap hx, rfl⟩

theorem TOB_eq' {E : ScBanach} {C O : Set (E 0)} (R : ScRetraction E C) (hR : R.retract = O) :
    TOB R = retractTangent E C O := by
  rw [TOB_eq, ← hR, retractTangent_eq]

/-- Definition 2.7 in B's (existential) form is the project's, for an actual retract. -/
theorem retractMapB_iff {E E' : ScBanach} {C O : Set (E 0)} {C' O' : Set (E' 0)}
    {f : E 0 → E' 0} (hO : IsScRetract E C O) :
    IsScSmoothRetractMapB E C O E' O' f ↔ IsScSmoothRetractMap E C O E' C' O' f :=
  (isScSmoothRetractMap_iff_exists hO).symm

theorem retractMapB_congr {E E' : ScBanach} {C O : Set (E 0)} {O' : Set (E' 0)}
    {f f' : E 0 → E' 0} (hO : IsScRetract E C O) (h : IsScSmoothRetractMapB E C O E' O' f)
    (hff' : EqOn f f' O) : IsScSmoothRetractMapB E C O E' O' f' :=
  (retractMapB_iff (C' := univ) hO).2 (((retractMapB_iff (C' := univ) hO).1 h).congr hff')

/-- B's (f), `pr₁ : TO → O₁` into `E^1`, is the project's statement into `E¹`. -/
theorem fst_iff {E : ScBanach} {C O : Set (E 0)} (hO : IsScRetract E C O)
    (R : ScRetraction E C) (hR : R.retract = O) :
    IsScSmoothRetractMapB (TEB E) (TCB E C) (TOB R) (E.shiftAdd 1) (E.lvlSet O 1)
        (fun a : (TEB E).lvl 0 => (a.1 : (E.shiftAdd 1).lvl 0)) ↔
      IsScSmoothRetractMap E.tangent (E.tangentSet C) (retractTangent E C O) E.shift
        (E.lvlSet C 1) (E.lvlSet O 1) Prod.fst := by
  rw [isScSmoothRetractMap_iff_exists hO.tangentSet]
  unfold IsScSmoothRetractMapB
  rw [TOB_eq' R hR]
  constructor
  · rintro ⟨hmaps, S, hS, hsm⟩
    refine ⟨hmaps, S, hS, ?_⟩
    have h := IsScSmooth.comp S.isScDomain (isScDomain_univ _)
      ((shiftIso E).symm.toScOperator.isScSmooth (isScDomain_univ _)) hsm (mapsTo_univ _ _)
    exact h.congr S.isScDomain fun y _ => shiftIso_symm_zero E _
  · rintro ⟨hmaps, S, hS, hsm⟩
    refine ⟨hmaps, S, hS, ?_⟩
    have h := IsScSmooth.comp S.isScDomain (isScDomain_univ _)
      ((shiftIso E).toScOperator.isScSmooth (isScDomain_univ _)) hsm (mapsTo_univ _ _)
    exact h.congr S.isScDomain fun y _ => shiftIso_zero E _

/-! #### M-polyfold glue -/

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

theorem cast_vecB {p q : P.TangentPre} (e : p.φ = q.φ)
    (hpq : TangentSpace.mk p = TangentSpace.mk q) :
    cast (congrArg (fun c : MChart X => (TEB c.model.E).lvl 0) e) (vecB p) = vecB q := by
  obtain ⟨x, φ, h, hφ, hx, hl, ht⟩ := p
  obtain ⟨x', φ', h', hφ', hx', hl', ht'⟩ := q
  simp only at e
  subst e
  have hr := (TangentSpace.mk_eq_mk.1 hpq).2
  rw [TangentPre.transport_self] at hr
  rw [cast_eq]
  exact hr

theorem TφB_eq (p : P.TangentPre) : TφB P p.φ (TangentSpace.mk p) = vecB p := by
  unfold TφB
  rw [dif_pos ⟨p, rfl, rfl⟩]
  generalize_proofs h
  exact cast_vecB h.choose_spec.1 h.choose_spec.2

theorem tangentChartSet_eq (φ : MChart X) : tangentChartSet (P := P) φ = TVB P φ := by
  ext α
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  constructor
  · intro h; exact ⟨p, rfl, h⟩
  · rintro ⟨q, hq, hqx⟩
    rw [← hq]; exact hqx

theorem tangentChartMap_eq_TφB {φ : MChart X} (hφ : P.IsChart φ) {α : P.TangentSpace}
    (hα : α ∈ TVB P φ) : tangentChartMap hφ α = TφB P φ α := by
  rw [← tangentChartSet_eq] at hα
  obtain ⟨p, hpφ, rfl⟩ : ∃ p : P.TangentPre, p.φ = φ ∧ TangentSpace.mk p = α :=
    ⟨TangentPre.ofVec hφ (tangentChartMap_mem hφ hα), rfl, mk_ofVec_tangentChartMap hφ hα⟩
  subst hpφ
  rw [TφB_eq]
  exact tangentChartMap_mk_self p

theorem basicSet_eq {φ : MChart X} (hφ : P.IsChart φ) (W : Set ((TEB φ.model.E).lvl 0)) :
    {α | α ∈ TVB P φ ∧ TφB P φ α ∈ W} =
      {α | α ∈ tangentChartSet φ ∧ tangentChartMap hφ α ∈ W} := by
  ext α
  simp only [mem_ofPred_eq, tangentChartSet_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [tangentChartMap_eq_TφB hφ h1]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [← tangentChartMap_eq_TφB hφ h1]⟩

theorem τB_eq : τB P = (inferInstance : TopologicalSpace P.TangentSpace) := by
  unfold τB
  change _ = TopologicalSpace.generateFrom P.tangentBasis
  congr 1
  ext s
  constructor
  · rintro ⟨φ, hφ, W, hW, rfl⟩
    exact ⟨φ, hφ, W, hW, basicSet_eq hφ W⟩
  · rintro ⟨φ, hφ, W, hW, rfl⟩
    exact ⟨φ, hφ, W, hW, (basicSet_eq hφ W).symm⟩

theorem image_TφB {φ ψ : MChart X} (hφ : P.IsChart φ) :
    TφB P φ '' (TVB P φ ∩ TVB P ψ) =
      tangentChartMap hφ '' (tangentChartSet φ ∩ tangentChartSet ψ) := by
  rw [tangentChartSet_eq, tangentChartSet_eq]
  exact Set.image_congr fun α hα => (tangentChartMap_eq_TφB hφ hα.1).symm

theorem transition_eq {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ)
    (α₀ β₀ : P.TangentSpace) {α : P.TangentSpace} (hα : α ∈ tangentChartSet φ) :
    (tangentChart hφ α₀).transition (tangentChart hψ β₀) (tangentChartMap hφ α) =
      tangentChartMap hψ α := by
  change tangentChartMap hψ ((tangentChart hφ α₀).symm (tangentChart hφ α₀ α)) = _
  rw [(tangentChart hφ α₀).symm_apply_apply hα]

theorem transB_eq {φ ψ : MChart X} (hφ : P.IsChart φ) {α : P.TangentSpace}
    (hα : α ∈ TVB P φ) : transB (TVB P φ) (TφB P φ) (TφB P ψ) (TφB P φ α) = TφB P ψ α := by
  unfold transB
  rw [dif_pos ⟨α, hα, rfl⟩]
  generalize_proofs h
  obtain ⟨hy, hyeq⟩ := h.choose_spec
  have hy' : h.choose ∈ tangentChartSet φ := by rw [tangentChartSet_eq]; exact hy
  have hα' : α ∈ tangentChartSet φ := by rw [tangentChartSet_eq]; exact hα
  have : h.choose = α := tangentChartMap_injOn hφ hy' hα' (by
    rw [tangentChartMap_eq_TφB hφ hy, tangentChartMap_eq_TφB hφ hα, hyeq])
  rw [this]

omit [T2Space X] [ParacompactSpace X] in
theorem tangent_overlap_subset (φ ψ : MChart X) {a : φ.model.E.tangent 0}
    (ha : a ∈ retractTangent φ.model.E φ.model.C (φ.overlap ψ)) :
    a ∈ retractTangent φ.model.E φ.model.C φ.model.O :=
  (TangentPre.mem_retractTangent_image_iff inter_subset_left
    (φ.isOpen_source.inter ψ.isOpen_source)
    (retractTangent_fst_mem (φ.isScRetract_overlap ψ) ha)).1 ha

/-- B's chart `(TV, Tφ, (TO, TC, TE))` is a chart on `(TX, τB)`. -/
theorem isChartB_of {φ : MChart X} (hφ : P.IsChart φ) (R : ScRetraction φ.model.E φ.model.C)
    (hR : R.retract = φ.model.O) :
    @IsChartB _ (τB P) (TVB P φ) (TEB φ.model.E) (TCB φ.model.E φ.model.C) (TOB R) (TφB P φ) := by
  rw [τB_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [← tangentChartSet_eq]; exact isOpen_tangentChartSet hφ
  · rw [TOB_eq' R hR]; exact φ.model.isScRetract.tangentSet
  · rcases isEmpty_or_nonempty P.TangentSpace with hE | ⟨⟨α₀⟩⟩
    · have h1 : IsEmpty (TVB P φ) := ⟨fun a => hE.false a.1⟩
      have h2 : IsEmpty (TOB R) := ⟨fun a => by
        have ha : (a : (TEB φ.model.E).lvl 0) ∈ retractTangent φ.model.E φ.model.C φ.model.O := by
          rw [← TOB_eq' R hR]; exact a.2
        exact hE.false (TangentSpace.mk (TangentPre.ofVec hφ ha))⟩
      exact ⟨Homeomorph.empty, fun y => (h1.false y).elim⟩
    · have hs : (tangentChart hφ α₀).source = TVB P φ := tangentChartSet_eq φ
      have ht : (tangentChart hφ α₀).model.O = TOB R := (TOB_eq' R hR).symm
      refine ⟨(Homeomorph.setCongr hs.symm).trans
        ((tangentChart hφ α₀).sourceHomeomorph.trans (Homeomorph.setCongr ht)), fun y => ?_⟩
      change tangentChartMap hφ y.1 = TφB P φ y.1
      exact tangentChartMap_eq_TφB hφ y.2

/-- Formula (5), first part, from the project's `tangentChart_overlap`. -/
theorem image_eq_of
    (hov : ∀ {φ ψ : MChart X} (hφ : P.IsChart φ) (α₀ : P.TangentSpace) (hψ : P.IsChart ψ)
      (β₀ : P.TangentSpace), (tangentChart hφ α₀).overlap (tangentChart hψ β₀) =
        retractTangent φ.model.E φ.model.C (φ.overlap ψ))
    {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ) (R : ScRetraction φ.model.E φ.model.C)
    (hR : R.retract = φ.toPartialEquiv '' (φ.source ∩ ψ.source)) :
    TφB P φ '' (TVB P φ ∩ TVB P ψ) = TOB R := by
  rw [image_TφB hφ, TOB_eq' R hR]
  change _ = retractTangent φ.model.E φ.model.C (φ.overlap ψ)
  ext a
  constructor
  · rintro ⟨α, hα, rfl⟩
    rw [← hov hφ α hψ α]
    exact ⟨α, hα, rfl⟩
  · intro ha
    have hO := tangent_overlap_subset φ ψ ha
    rw [← hov hφ (TangentSpace.mk (TangentPre.ofVec hφ hO)) hψ
      (TangentSpace.mk (TangentPre.ofVec hφ hO))] at ha
    exact ha

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hov, htr, -, hfst, -⟩
  intro X _ _ _ P
  -- formula (5)
  have h5 : ∀ φ φ' : MChart X, P.IsChart φ → P.IsChart φ' →
      ∀ R : ScRetraction φ.model.E φ.model.C,
        R.retract = φ.toPartialEquiv '' (φ.source ∩ φ'.source) →
      ∀ R' : ScRetraction φ'.model.E φ'.model.C,
        R'.retract = φ'.toPartialEquiv '' (φ.source ∩ φ'.source) →
        TφB P φ '' (TVB P φ ∩ TVB P φ') = TOB R ∧
        (∀ α ∈ TVB P φ ∩ TVB P φ',
          TφB P φ' α = tangentMap R.U (chartTransB φ φ' ∘ R.toFun) (TφB P φ α)) ∧
        IsScSmoothRetractMapB (TEB φ.model.E) (TCB φ.model.E φ.model.C) (TOB R)
          (TEB φ'.model.E) (TOB R') (tangentMap R.U (chartTransB φ φ' ∘ R.toFun)) := by
    intro φ φ' hφ hφ' R hR R' hR'
    have hcomp := (hφ.compatible hφ' (P := P)).1
    have hR1 : R.retract = φ.overlap φ' := hR
    refine ⟨image_eq_of hov hφ hφ' R hR, ?_, ?_⟩
    · intro α hα
      have hα1 : α ∈ tangentChartSet φ := by rw [tangentChartSet_eq]; exact hα.1
      have hα2 : α ∈ tangentChartSet φ' := by rw [tangentChartSet_eq]; exact hα.2
      rw [← tangentChartMap_eq_TφB hφ' hα.2, ← tangentChartMap_eq_TφB hφ hα.1,
        ← transition_eq hφ hφ' α α hα1]
      have hmem : tangentChartMap hφ α ∈ retractTangent φ.model.E φ.model.C (φ.overlap φ') := by
        rw [← hov hφ α hφ' α]; exact ⟨α, ⟨hα1, hα2⟩, rfl⟩
      rw [htr hφ α hφ' α hmem]
      exact retractTangentMap_eqOn hcomp R hR1 hmem
    · have hT := (hcomp.tangent (φ.isScRetract_overlap φ') (φ'.isScRetract_overlap φ)).congr
        (retractTangentMap_eqOn hcomp R hR1)
      have hR2 : R'.retract = φ'.overlap φ := by
        rw [hR', MChart.overlap, inter_comm]
      rw [TOB_eq' R hR1, TOB_eq' R' hR2]
      exact (retractMapB_iff (φ.isScRetract_overlap φ').tangentSet).2 hT
  -- one half of the compatibility of the tangent charts
  have hhalf : ∀ φ φ' : MChart X, P.IsChart φ → P.IsChart φ' →
      IsScSmoothRetractMapB (TEB φ.model.E) (TCB φ.model.E φ.model.C)
        (TφB P φ '' (TVB P φ ∩ TVB P φ')) (TEB φ'.model.E) (TφB P φ' '' (TVB P φ ∩ TVB P φ'))
        (transB (TVB P φ) (TφB P φ) (TφB P φ')) := by
    intro φ φ' hφ hφ'
    obtain ⟨R, hR⟩ := φ.isScRetract_overlap φ'
    obtain ⟨R', hR'⟩ := φ'.isScRetract_image (s := φ.source ∩ φ'.source) inter_subset_right
      (φ.isOpen_source.inter φ'.isOpen_source)
    obtain ⟨himg, heq, hsm⟩ := h5 φ φ' hφ hφ' R hR R' hR'
    have himg' : TφB P φ' '' (TVB P φ ∩ TVB P φ') = TOB R' := by
      rw [inter_comm]
      exact image_eq_of hov hφ' hφ R' (by rw [hR', inter_comm])
    rw [himg, himg']
    refine retractMapB_congr (by rw [TOB_eq' R hR]; exact (φ.isScRetract_overlap φ').tangentSet)
      hsm ?_
    rw [← himg]
    rintro _ ⟨α, hα, rfl⟩
    rw [transB_eq hφ hα.1, heq α hα]
  refine ⟨fun φ hφ R hR => isChartB_of hφ R hR, h5, ?_, ?_, ?_, ?_⟩
  · -- the tangent charts are compatible
    intro φ φ' hφ hφ'
    refine ⟨hhalf φ φ' hφ hφ', ?_⟩
    have := hhalf φ' φ hφ' hφ
    rw [inter_comm] at this
    exact this
  · -- they cover `TX`
    intro α
    obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
    exact ⟨p.φ, p.isChart, p, rfl, p.mem_source⟩
  · -- Hausdorff and paracompact
    rw [τB_eq]
    exact ⟨inferInstance, inferInstance⟩
  · -- `p` in the charts
    intro φ hφ R hR
    refine ⟨fun α hα => ?_, (fst_iff φ.model.isScRetract R hR).2 (hfst φ.model.isScRetract)⟩
    have hα' : α ∈ tangentChartSet φ := by rw [tangentChartSet_eq]; exact hα
    rw [← tangentChartMap_eq_TφB hφ hα, tangentChartMap_fst hφ hα',
      P.toBase_levelLift hφ hα' (levelVal_mem _)]

section GlueB

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- One half of the compatibility of two tangent charts, from B's `CompatibleB`. -/
theorem compat_half {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ)
    (α₀ β₀ : P.TangentSpace)
    (h : IsScSmoothRetractMapB (TEB φ.model.E) (TCB φ.model.E φ.model.C)
      (TφB P φ '' (TVB P φ ∩ TVB P ψ)) (TEB ψ.model.E) (TφB P ψ '' (TVB P φ ∩ TVB P ψ))
      (transB (TVB P φ) (TφB P φ) (TφB P ψ))) :
    IsScSmoothRetractMap (tangentChart hφ α₀).model.E (tangentChart hφ α₀).model.C
      ((tangentChart hφ α₀).overlap (tangentChart hψ β₀)) (tangentChart hψ β₀).model.E
      (tangentChart hψ β₀).model.C ((tangentChart hψ β₀).overlap (tangentChart hφ α₀))
      ((tangentChart hφ α₀).transition (tangentChart hψ β₀)) := by
  have h1 : (tangentChart hφ α₀).overlap (tangentChart hψ β₀) = TφB P φ '' (TVB P φ ∩ TVB P ψ) :=
    (image_TφB hφ).symm
  have h2 : (tangentChart hψ β₀).overlap (tangentChart hφ α₀) = TφB P ψ '' (TVB P φ ∩ TVB P ψ) := by
    rw [inter_comm]; exact (image_TφB hψ).symm
  have hret := (tangentChart hφ α₀).isScRetract_overlap (tangentChart hψ β₀)
  rw [h1, h2]
  rw [h1] at hret
  refine (retractMapB_iff hret).1 (retractMapB_congr hret h ?_)
  rintro _ ⟨α, hα, rfl⟩
  have hα1 : α ∈ tangentChartSet φ := by rw [tangentChartSet_eq]; exact hα.1
  rw [transB_eq hφ hα.1, ← tangentChartMap_eq_TφB hφ hα.1, transition_eq hφ hψ α₀ β₀ hα1,
    tangentChartMap_eq_TφB hψ hα.2]

end GlueB

theorem B_to_A : B → A := by
  intro hB
  -- `pr₁ : TO → O₁` is sc-smooth, for the model of a chart, from B's (f)
  have hfstB : ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
      (P : MPolyfold X) {φ : MChart X}, P.IsChart φ →
      IsScSmoothRetractMap φ.model.E.tangent (φ.model.E.tangentSet φ.model.C)
        (retractTangent φ.model.E φ.model.C φ.model.O) φ.model.E.shift
        (φ.model.E.lvlSet φ.model.C 1) (φ.model.E.lvlSet φ.model.O 1) Prod.fst := by
    intro X _ _ _ P φ hφ
    obtain ⟨R, hR⟩ := φ.model.isScRetract
    exact (fst_iff φ.model.isScRetract R hR).1 ((hB X P).2.2.2.2.2 φ hφ R hR).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `tangentChart_overlap`
    intro X _ _ _ P φ ψ hφ α₀ hψ β₀
    obtain ⟨R, hR⟩ := φ.isScRetract_overlap ψ
    obtain ⟨R', hR'⟩ := ψ.isScRetract_image (s := φ.source ∩ ψ.source) inter_subset_right
      (φ.isOpen_source.inter ψ.isOpen_source)
    have h := ((hB X P).2.1 φ ψ hφ hψ R hR R' hR').1
    change tangentChartMap hφ '' (tangentChartSet φ ∩ tangentChartSet ψ) = _
    rw [← image_TφB hφ, h, TOB_eq' R hR]
  · -- `tangentChart_transition`
    intro X _ _ _ P φ ψ hφ α₀ hψ β₀ a ha
    obtain ⟨R, hR⟩ := φ.isScRetract_overlap ψ
    obtain ⟨R', hR'⟩ := ψ.isScRetract_image (s := φ.source ∩ ψ.source) inter_subset_right
      (φ.isOpen_source.inter ψ.isOpen_source)
    obtain ⟨himg, heq, -⟩ := (hB X P).2.1 φ ψ hφ hψ R hR R' hR'
    have ha' := ha
    rw [← TOB_eq' R hR, ← himg] at ha'
    obtain ⟨α, hα, rfl⟩ := ha'
    have hα1 : α ∈ tangentChartSet φ := by rw [tangentChartSet_eq]; exact hα.1
    have hcomp := (hφ.compatible hψ (P := P)).1
    rw [← tangentChartMap_eq_TφB hφ hα.1, transition_eq hφ hψ α₀ β₀ hα1,
      tangentChartMap_eq_TφB hψ hα.2, heq α hα]
    rw [← tangentChartMap_eq_TφB hφ hα.1] at ha ⊢
    exact (retractTangentMap_eqOn hcomp R hR ha).symm
  · -- `tangentChart_compatible`
    intro X _ _ _ P φ ψ hφ α₀ hψ β₀
    obtain ⟨-, -, hc, -⟩ := hB X P
    refine ⟨compat_half hφ hψ α₀ β₀ (hc φ ψ hφ hψ).1, compat_half hψ hφ β₀ α₀ ?_⟩
    have := (hc φ ψ hφ hψ).2
    rw [inter_comm] at this
    exact this
  · -- `isScSmoothRetractMap_tangent_fst`, through the M-polyfold `O`
    intro E C O hO
    rcases O.eq_empty_or_nonempty with hempty | hne
    · subst hempty
      obtain ⟨R, hR⟩ := hO
      have hU : R.U = ∅ := Set.image_eq_empty.1 hR
      have hT : retractTangent E C ∅ = ∅ := by
        rw [← hR, retractTangent_eq]
        apply Set.image_eq_empty.2
        ext p
        simp only [mem_empty_iff_false, iff_false]
        intro hp
        have : E.toBase 1 p.1 ∈ R.U := hp
        rw [hU] at this
        exact Set.notMem_empty _ this
      rw [hT]
      refine ⟨fun a ha => absurd ha (Set.notMem_empty a), fun S hS => ?_⟩
      have hSU : S.U = ∅ := Set.image_eq_empty.1 hS
      exact IsScSmooth.of_locally S.isScDomain fun y hy => by
        rw [hSU] at hy; exact absurd hy (Set.notMem_empty y)
    · let M : LocalModel := ⟨E, C, O, hO⟩
      exact hfstB (M.toMPolyfold hne) (φ := M.selfChart hne)
        ((M.toMPolyfold hne).isChart_of_mem (mem_singleton _))
  · -- `tangentProj_isScSmooth`
    intro X _ _ _ P _ _
    refine IsScSmoothOn.of_exists_charts isOpen_univ continuous_tangentProj.continuousOn
      fun α _ => ?_
    obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
    set φ := p.φ with hφdef
    have hφ : P.IsChart φ := p.isChart
    refine ⟨tangentChart hφ (TangentSpace.mk p), levelChart hφ (P.tangentProj (TangentSpace.mk p)),
      tangentChartSet φ, P.tangentPolyfold_isChart hφ _, P.shift_isChart hφ _,
      isOpen_tangentChartSet hφ, p.mem_source, fun β hβ => ⟨mem_univ _, hβ⟩, fun β hβ => hβ, ?_⟩
    have himg : tangentChart hφ (TangentSpace.mk p) '' tangentChartSet φ =
        retractTangent φ.model.E φ.model.C φ.model.O := (tangentChart hφ _).image_source
    rw [himg]
    refine (hfstB P hφ).congr fun a ha => ?_
    change a.1 = levelLift φ 1 (P.levelVal 1 (P.tangentProj (tangentChartInv hφ _ a)))
    rw [tangentChartInv_of_mem hφ _ ha, tangentProj_mk]
    exact (congrArg Prod.fst (TangentPre.ofVec_vec hφ ha)).symm

#rt_check_soft RoundTrip.V2_21.A_to_B [Polyfold.MPolyfold.tangentChart_overlap,
  Polyfold.MPolyfold.tangentChart_transition, Polyfold.MPolyfold.tangentChart_compatible,
  Polyfold.MPolyfold.isScSmoothRetractMap_tangent_fst, Polyfold.MPolyfold.tangentProj_isScSmooth]
#rt_check_soft RoundTrip.V2_21.B_to_A [Polyfold.MPolyfold.tangentChart_overlap,
  Polyfold.MPolyfold.tangentChart_transition, Polyfold.MPolyfold.tangentChart_compatible,
  Polyfold.MPolyfold.isScSmoothRetractMap_tangent_fst, Polyfold.MPolyfold.tangentProj_isScSmooth]
#rt_overlap RoundTrip.V2_21.B_to_A [Polyfold.MPolyfold.tangentChart_overlap,
  Polyfold.MPolyfold.tangentChart_transition, Polyfold.MPolyfold.tangentChart_compatible,
  Polyfold.MPolyfold.isScSmoothRetractMap_tangent_fst, Polyfold.MPolyfold.tangentProj_isScSmooth]

end RoundTrip.V2_21
