import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_19

/-! Round trip for V2_19 (Definition 2.18: the tangent space `TX`).

`A` is the conjunction of the types of the listed theorems
`Polyfold.MPolyfold.tangentChartMap_mk_self`, `.tangentChartMap_injOn`,
`.tangentChartMap_mk_ofVec`, `.tangentChartMap_mk_ofVec_of_mem`, all at universe `0` (B lives in
`Type`).  `TangentSpace`, `tangentProj`, `tangentFiber`, `tangentChartSet`, `tangentChartMap`,
`tangentBasis` are definitions (vocabulary), compared with B's notions below.

* `TX`, `p`, `T_xX`, `TV`: the project's objects are B's (`Quotient.exists_rep`, `mk_eq_mk`
  with `RelB p q ↔ Rel q p`, `tangentProj_mk`, `tangentFiber_eq`, `tangentChartSet_eq`).
* `Tφ`: the project's `tangentChartMap hφ` (`[(x, ψ, h)] ↦ T(φ ∘ ψ⁻¹)(ψ(x), h)`) agrees on `TV`
  with B's `TφB` (computed with a representative in the chart `φ`), by `tangentChartMap_mk_self`.
* The topology: `tangentBasis = TfamB`, so the instance is `generateFrom TfamB`.
* "`T_xX` is a vector space and `Tφ` is linear on it" is NOT in the project (its docstring: the
  linear structure of `T_xX` is not formalized, gap G.7).  It is proved here: `T_xX` is put in
  bijection (`fibreEquiv`) with the subspace `T_{φ₀(x)}O = range Dr(φ₀(x))` through one chart
  `φ₀` (bijectivity: `mk_ofVec_tangentChartMap` and A's `tangentChartMap_mk_ofVec`), the vector
  space structure is transported, and for every chart `φ` around `x`, `α ↦ (Tφ α).2` is
  `D(φ ∘ φ₀⁻¹ ∘ r)(φ₀(x)) ∘ fibreEquiv`, linear (A's `tangentChartMap_mk_ofVec_of_mem`). -/

namespace RoundTrip.V2_19
open Polyfold Set MPolyfold

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.tangentChartMap_mk_self.{0}) ∧
    (type_of% @Polyfold.MPolyfold.tangentChartMap_injOn.{0}) ∧
    (type_of% @Polyfold.MPolyfold.tangentChartMap_mk_ofVec.{0}) ∧
    (type_of% @Polyfold.MPolyfold.tangentChartMap_mk_ofVec_of_mem.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.tangentChartMap_mk_self.{0}, @Polyfold.MPolyfold.tangentChartMap_injOn.{0},
    @Polyfold.MPolyfold.tangentChartMap_mk_ofVec.{0},
    @Polyfold.MPolyfold.tangentChartMap_mk_ofVec_of_mem.{0}⟩

section Glue

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

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

theorem vecB_eq (p : P.TangentPre) : vecB p = p.vec := rfl

/-- B's relation `RelB p q` is the project's `Rel q p`. -/
theorem relB_iff (p q : P.TangentPre) : RelB p q ↔ q.Rel p := by
  have hcomp (_ : p.x = q.x) := (q.isChart.compatible p.isChart (P := P)).1
  have hmem (hx : p.x = q.x) : q.vec ∈
      retractTangent q.φ.model.E q.φ.model.C (q.φ.overlap p.φ) :=
    q.vec_mem_image inter_subset_left (q.φ.isOpen_source.inter p.φ.isOpen_source)
      ⟨q.mem_source, hx ▸ p.mem_source⟩
  constructor
  · rintro ⟨hx, R, hR, y₁, hy₁, hD⟩
    refine ⟨hx.symm, ?_⟩
    have hy : q.vec.1 = y₁ := by
      apply q.φ.model.E.toBase_injective 1
      rw [q.toBase_vec_fst, hy₁]
    refine Prod.ext ?_ ?_
    · rw [q.transport_fst p.isChart (hx ▸ p.mem_source), ← hx]; rfl
    · change (retractTangentMap _ _ (q.φ.overlap p.φ) (q.φ.transition p.φ) q.vec).2 = p.h
      rw [retractTangentMap_apply (hcomp hx) R hR (hmem hx)]
      change scDeriv R.U (q.φ.transition p.φ ∘ R) q.vec.1 q.h = p.h
      rw [hy]; exact hD
  · rintro ⟨hx, hT⟩
    obtain ⟨R, hR⟩ := q.φ.isScRetract_overlap p.φ
    refine ⟨hx.symm, R, hR, levelLift q.φ 1 q.x, q.toBase_vec_fst, ?_⟩
    have := congrArg Prod.snd hT
    change (retractTangentMap _ _ (q.φ.overlap p.φ) (q.φ.transition p.φ) q.vec).2 = p.h at this
    rw [retractTangentMap_apply (hcomp hx.symm) R hR (hmem hx.symm)] at this
    exact this

theorem mk_eq_iff (p q : P.TangentPre) : TangentSpace.mk p = TangentSpace.mk q ↔ RelB p q := by
  rw [relB_iff, eq_comm]; exact TangentSpace.mk_eq_mk

/-- Two equivalent tuples in the same chart have the same vector. -/
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

/-- `Tφ α` computed with any representative in the chart `φ`. -/
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

theorem tangentFiber_eq (x : P.Level 1) : P.tangentFiber x = TxXB P (P.levelVal 1 x) := by
  ext α
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  constructor
  · intro h
    refine ⟨p, rfl, ?_⟩
    change P.tangentProj (TangentSpace.mk p) = x at h
    rw [← h]; rfl
  · rintro ⟨q, hq, hqx⟩
    apply level_ext
    rw [← hq, tangentProj_mk]; exact hqx

/-- Every class over `V` has a representative in the chart `φ`. -/
theorem exists_rep_chart {φ : MChart X} (hφ : P.IsChart φ) {α : P.TangentSpace}
    (hα : α ∈ TVB P φ) : ∃ p : P.TangentPre, p.φ = φ ∧ TangentSpace.mk p = α := by
  rw [← tangentChartSet_eq] at hα
  exact ⟨TangentPre.ofVec hφ (tangentChartMap_mem hφ hα), rfl, mk_ofVec_tangentChartMap hφ hα⟩

/-- `Tφ` (project) and `TφB` agree on `TV`, given `Tφ[(x, φ, h)] = (φ(x), h)`. -/
theorem tangentChartMap_eq_TφB
    (hself : ∀ p : P.TangentPre, tangentChartMap p.isChart (TangentSpace.mk p) = p.vec)
    {φ : MChart X} (hφ : P.IsChart φ) {α : P.TangentSpace} (hα : α ∈ TVB P φ) :
    tangentChartMap hφ α = TφB P φ α := by
  obtain ⟨p, hpφ, rfl⟩ := exists_rep_chart hφ hα
  subst hpφ
  rw [TφB_eq]
  exact hself p

theorem tangentBasis_eq
    (hself : ∀ p : P.TangentPre, tangentChartMap p.isChart (TangentSpace.mk p) = p.vec) :
    P.tangentBasis = TfamB P := by
  ext s
  constructor
  · rintro ⟨φ, hφ, W, hW, rfl⟩
    refine ⟨φ, hφ, W, hW, ?_⟩
    ext α
    rw [mem_ofPred_eq, mem_ofPred_eq, tangentChartSet_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [← tangentChartMap_eq_TφB hself hφ h1]⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [tangentChartMap_eq_TφB hself hφ h1]⟩
  · rintro ⟨φ, hφ, W, hW, rfl⟩
    refine ⟨φ, hφ, W, hW, ?_⟩
    ext α
    rw [mem_ofPred_eq, mem_ofPred_eq, tangentChartSet_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [tangentChartMap_eq_TφB hself hφ h1]⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [← tangentChartMap_eq_TφB hself hφ h1]⟩

/-! #### The vector space `T_xX` -/

/-- The subspace `T_yO = range Dr(y)` of `E₀`. -/
noncomputable def Sf {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C) (y : E 1) :
    Submodule ℝ (E 0) :=
  LinearMap.range (scDeriv R.U R.toFun y : E 0 →ₗ[ℝ] E 0)

theorem mem_Sf {E : ScBanach} {C O : Set (E 0)} (R : ScRetraction E C) (hR : R.retract = O)
    {y : E 1} (hy : E.toBase 1 y ∈ O) (v : E 0) :
    v ∈ Sf R y ↔ ((y, v) : E.tangent 0) ∈ retractTangent E C O := by
  have := tangentSpace_eq_coe_submodule R (x := y) (by rw [ScBanach.mem_lvlSet, hR]; exact hy)
  rw [hR] at this
  change v ∈ (Sf R y : Set (E 0)) ↔ v ∈ tangentSpace E C O y
  rw [this]; rfl

variable (x : P.Level 1) {φ₀ : MChart X} (hφ₀ : P.IsChart φ₀)
  (hx : P.levelVal 1 x ∈ φ₀.source) (R : ScRetraction φ₀.model.E φ₀.model.C)
  (hR : R.retract = φ₀.model.O)

include hx in
theorem mem_fibre_chartSet {α : P.TangentSpace} (hα : α ∈ TxXB P (P.levelVal 1 x)) :
    α ∈ tangentChartSet φ₀ ∧ P.levelVal 1 (P.tangentProj α) = P.levelVal 1 x := by
  obtain ⟨p, rfl, hpx⟩ := hα
  exact ⟨by change p.x ∈ φ₀.source; rw [hpx]; exact hx, hpx⟩

include hφ₀ hx in
theorem toBase_lift : φ₀.model.E.toBase 1 (levelLift φ₀ 1 (P.levelVal 1 x)) ∈ φ₀.model.O := by
  rw [P.toBase_levelLift hφ₀ hx (levelVal_mem x)]; exact φ₀.mapsTo_model _ hx

include hx in
theorem fibre_fst {α : P.TangentSpace} (hα : α ∈ TxXB P (P.levelVal 1 x)) :
    (tangentChartMap hφ₀ α).1 = levelLift φ₀ 1 (P.levelVal 1 x) := by
  have h := mem_fibre_chartSet x hx hα
  rw [tangentChartMap_fst hφ₀ h.1, h.2]

include hx in
theorem fibre_mem {α : P.TangentSpace} (hα : α ∈ TxXB P (P.levelVal 1 x)) :
    ((levelLift φ₀ 1 (P.levelVal 1 x), (tangentChartMap hφ₀ α).2) : φ₀.model.E.tangent 0) ∈
      retractTangent φ₀.model.E φ₀.model.C φ₀.model.O := by
  rw [← fibre_fst x hφ₀ hx hα]
  exact tangentChartMap_mem hφ₀ (mem_fibre_chartSet x hx hα).1

theorem mk_ofVec_congr {a b : φ₀.model.E.tangent 0} (hab : a = b)
    (ha : a ∈ retractTangent φ₀.model.E φ₀.model.C φ₀.model.O)
    (hb : b ∈ retractTangent φ₀.model.E φ₀.model.C φ₀.model.O) :
    TangentSpace.mk (TangentPre.ofVec (P := P) hφ₀ ha) = TangentSpace.mk (TangentPre.ofVec hφ₀ hb) := by
  subst hab; rfl

include hx hR in
/-- `T_xX ≅ T_{φ₀(x)}O` through the chart `φ₀`. -/
noncomputable def fibreEquiv
    (hmk : ∀ {a : φ₀.model.E.tangent 0} (ha : a ∈ retractTangent φ₀.model.E φ₀.model.C φ₀.model.O),
      tangentChartMap hφ₀ (TangentSpace.mk (TangentPre.ofVec hφ₀ ha)) = a) :
    TxXB P (P.levelVal 1 x) ≃ Sf R (levelLift φ₀ 1 (P.levelVal 1 x)) where
  toFun α := ⟨(tangentChartMap hφ₀ α.1).2,
    (mem_Sf R hR (toBase_lift x hφ₀ hx) _).2 (fibre_mem x hφ₀ hx α.2)⟩
  invFun v := ⟨TangentSpace.mk (TangentPre.ofVec hφ₀
      ((mem_Sf R hR (toBase_lift x hφ₀ hx) v.1).1 v.2)),
    ⟨_, rfl, by
      rw [TangentPre.ofVec_x]
      change φ₀.symm (φ₀.model.E.toBase 1 (levelLift φ₀ 1 (P.levelVal 1 x))) = _
      rw [P.toBase_levelLift hφ₀ hx (levelVal_mem x), φ₀.symm_apply_apply hx]⟩⟩
  left_inv α := by
    apply Subtype.ext
    have hα := mem_fibre_chartSet x hx α.2
    exact (mk_ofVec_congr hφ₀
      (a := (levelLift φ₀ 1 (P.levelVal 1 x), (tangentChartMap hφ₀ α.1).2))
      (b := tangentChartMap hφ₀ α.1) (Prod.ext (fibre_fst x hφ₀ hx α.2).symm rfl)
      (fibre_mem x hφ₀ hx α.2) (tangentChartMap_mem hφ₀ hα.1)).trans
      (mk_ofVec_tangentChartMap hφ₀ hα.1)
  right_inv v := by
    apply Subtype.ext
    change (tangentChartMap hφ₀ (TangentSpace.mk (TangentPre.ofVec hφ₀ _))).2 = v.1
    rw [hmk]

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hself, -, hmk, hmk2⟩
  intro X _ _ _ P
  have hself' : ∀ p : P.TangentPre, tangentChartMap p.isChart (TangentSpace.mk p) = p.vec :=
    fun p => hself p
  refine ⟨TangentSpace.exists_rep, mk_eq_iff, fun p => rfl, tangentFiber_eq, ?_,
    fun φ _ => tangentChartSet_eq φ, fun φ hφ α hα => exists_rep_chart hφ hα, TφB_eq, ?_,
    fun φ hφ α hα => tangentChartMap_eq_TφB hself' hφ hα, ?_⟩
  · -- the vector space `T_xX`
    intro x
    obtain ⟨φ₀, hφ₀, hx⟩ := P.exists_isChart_mem_source (P.levelVal 1 x)
    obtain ⟨R, hR⟩ := φ₀.model.isScRetract
    let e := fibreEquiv x hφ₀ hx R hR (fun ha => hmk hφ₀ ha)
    letI : AddCommGroup (TxXB P (P.levelVal 1 x)) := e.addCommGroup
    letI : Module ℝ (TxXB P (P.levelVal 1 x)) := e.module ℝ
    refine ⟨inferInstance, inferInstance, fun φ hφ hxφ => ?_⟩
    -- `α ↦ (Tφ α).2` is `D(φ ∘ φ₀⁻¹ ∘ r')(φ₀(x)) ∘ e`
    have hcomp := (hφ₀.compatible hφ (P := P)).1
    obtain ⟨R', hR'⟩ := φ₀.isScRetract_overlap φ
    set L := scDeriv R'.U (φ₀.transition φ ∘ R'.toFun) (levelLift φ₀ 1 (P.levelVal 1 x))
      with hL
    have hf : ∀ α : TxXB P (P.levelVal 1 x), (TφB P φ α.1).2 = L (e α).1 := by
      intro α
      have hα := mem_fibre_chartSet x hx α.2
      have hαφ : α.1 ∈ TVB P φ := by
        rw [← tangentChartSet_eq]; change _ ∈ φ.source; rw [hα.2]; exact hxφ
      rw [← tangentChartMap_eq_TφB hself' hφ hαφ]
      have hrep : α.1 = TangentSpace.mk (TangentPre.ofVec hφ₀ (fibre_mem x hφ₀ hx α.2)) := by
        exact ((mk_ofVec_congr hφ₀
          (a := (levelLift φ₀ 1 (P.levelVal 1 x), (tangentChartMap hφ₀ α.1).2))
          (b := tangentChartMap hφ₀ α.1) (Prod.ext (fibre_fst x hφ₀ hx α.2).symm rfl)
          (fibre_mem x hφ₀ hx α.2) (tangentChartMap_mem hφ₀ hα.1)).trans
          (mk_ofVec_tangentChartMap hφ₀ hα.1)).symm
      have hov : ((levelLift φ₀ 1 (P.levelVal 1 x), (tangentChartMap hφ₀ α.1).2) :
          φ₀.model.E.tangent 0) ∈ retractTangent φ₀.model.E φ₀.model.C (φ₀.overlap φ) := by
        refine (TangentPre.mem_retractTangent_image_iff inter_subset_left
          (φ₀.isOpen_source.inter φ.isOpen_source) ?_).2 (fibre_mem x hφ₀ hx α.2)
        change φ₀.model.E.toBase 1 (levelLift φ₀ 1 (P.levelVal 1 x)) ∈ _
        rw [P.toBase_levelLift hφ₀ hx (levelVal_mem x)]
        exact ⟨_, ⟨hx, hxφ⟩, rfl⟩
      rw [hrep, hmk2 hφ₀ hφ _ hov, retractTangentMap_apply hcomp R' hR' hov]
      rfl
    have he_add : ∀ a b : TxXB P (P.levelVal 1 x), e (a + b) = e a + e b := by
      intro a b
      rw [Equiv.add_def, Equiv.apply_symm_apply]
    have he_smul : ∀ (c : ℝ) (a : TxXB P (P.levelVal 1 x)), e (c • a) = c • e a := by
      intro c a
      rw [Equiv.smul_def, Equiv.apply_symm_apply]
    constructor
    · intro a b
      change (TφB P φ (a + b).1).2 = (TφB P φ a.1).2 + (TφB P φ b.1).2
      rw [hf, hf, hf, he_add, Submodule.coe_add, map_add]
    · intro c a
      change (TφB P φ (c • a).1).2 = c • (TφB P φ a.1).2
      rw [hf, hf, he_smul, Submodule.coe_smul, map_smul]
  · -- `Tφ(TV) ⊆ TO`
    intro φ hφ R hR α hα
    rw [← tangentChartMap_eq_TφB hself' hφ hα, TOB_eq, ← retractTangent_eq, hR]
    rw [← tangentChartSet_eq] at hα
    exact tangentChartMap_mem hφ hα
  · -- the topology
    change TopologicalSpace.generateFrom P.tangentBasis = _
    rw [tangentBasis_eq hself']

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `Tφ[(x, φ, h)] = (φ(x), h)`
    intro X _ _ _ P p
    obtain ⟨-, -, -, -, -, -, -, h8, -, h10, -⟩ := hB X P
    rw [h10 p.φ p.isChart _ ⟨p, rfl, p.mem_source⟩, h8 p]
    rfl
  · -- `Tφ` is injective on `TV`
    intro X _ _ _ P φ hφ α hα β hβ heq
    obtain ⟨-, -, -, -, -, h6, h7, h8, -, h10, -⟩ := hB X P
    rw [h6 φ hφ] at hα hβ
    rw [h10 φ hφ α hα, h10 φ hφ β hβ] at heq
    obtain ⟨p, hpφ, rfl⟩ := h7 φ hφ α hα
    obtain ⟨q, hqφ, rfl⟩ := h7 φ hφ β hβ
    have hp8 := h8 p
    have hq8 := h8 q
    obtain ⟨x, φp, h, hφp, hxs, hl, ht⟩ := p
    obtain ⟨x', φq, h', hφq, hxs', hl', ht'⟩ := q
    simp only at hpφ hqφ
    subst φp
    subst φq
    dsimp only at hp8 hq8
    rw [hp8, hq8] at heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    change levelLift φ 1 x = levelLift φ 1 x' at h1
    change h = h' at h2
    have hxx : x = x' := by
      have := congrArg (φ.model.E.toBase 1) h1
      rw [P.toBase_levelLift hφ hxs hl, P.toBase_levelLift hφ hxs' hl'] at this
      exact φ.toPartialEquiv.injOn hxs hxs' this
    subst hxx h2
    rfl
  · -- `Tφ ∘ (Tφ)⁻¹ = id` on `TO`
    intro X _ _ _ P φ hφ a ha
    obtain ⟨-, -, -, -, -, -, -, h8, -, h10, -⟩ := hB X P
    rw [h10 φ hφ _ ⟨_, rfl, (TangentPre.ofVec hφ ha).mem_source⟩]
    have h8' := h8 (TangentPre.ofVec hφ ha)
    change TφB P φ _ = vecB (TangentPre.ofVec hφ ha) at h8'
    rw [h8']
    exact TangentPre.ofVec_vec hφ ha
  · -- formula (5)
    intro X _ _ _ P φ ψ hφ hψ a ha' ha
    obtain ⟨-, h2, -, -, -, -, h7, h8, -, h10, -⟩ := hB X P
    set q := TangentPre.ofVec hφ ha' with hqdef
    have hov : φ.model.E.toBase 1 a.1 ∈ φ.overlap ψ :=
      retractTangent_fst_mem (φ.isScRetract_overlap ψ) ha
    have hO : φ.model.E.toBase 1 a.1 ∈ φ.model.O := φ.overlap_subset ψ hov
    have hqx : q.x ∈ ψ.source := by
      rw [hqdef, TangentPre.ofVec_x]
      obtain ⟨y, hy, hyeq⟩ := hov
      rw [← hyeq, φ.symm_apply_apply hy.1]; exact hy.2
    have hαψ : TangentSpace.mk q ∈ TVB P ψ := ⟨q, rfl, hqx⟩
    rw [h10 ψ hψ _ hαψ]
    obtain ⟨p', hp'ψ, hp'q⟩ := h7 ψ hψ _ hαψ
    obtain ⟨hxpq, R, hR, y₁, hy₁, hD⟩ := (h2 p' q).1 hp'q
    have hp8 := h8 p'
    rw [hp'q] at hp8
    have hvec : q.vec = a := TangentPre.ofVec_vec hφ ha'
    -- the base point, through the transport of `q`
    have hfst : (retractTangentMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ) a).1 =
        levelLift ψ 1 p'.x := by
      have := q.transport_fst hψ hqx
      change (retractTangentMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ) q.vec).1 =
        levelLift ψ 1 q.x at this
      rw [hvec] at this
      rw [this, hxpq]
    -- the derivative, from `RelB`
    have hcomp := (hφ.compatible hψ (P := P)).1
    have hR' : R.retract = φ.overlap ψ := by
      rw [hR, hp'ψ]; rfl
    have hy : a.1 = y₁ := by
      apply φ.model.E.toBase_injective 1
      have hy₁' : φ.model.E.toBase 1 y₁ = φ q.x := hy₁
      rw [hy₁']
      change _ = φ (φ.symm (φ.model.E.toBase 1 a.1))
      rw [φ.apply_symm_apply hO]
    obtain ⟨x', φ', h', hφ', hxs', hl', ht'⟩ := p'
    simp only at hp'ψ
    subst φ'
    dsimp only at hp8
    rw [hp8]
    refine Prod.ext ?_ ?_
    · rw [hfst]; rfl
    · rw [retractTangentMap_apply hcomp R hR' ha]
      change h' = scDeriv R.U (φ.transition ψ ∘ R.toFun) a.1 a.2
      rw [hy]
      exact hD.symm

#rt_check RoundTrip.V2_19.A_to_B [Polyfold.MPolyfold.tangentChartMap_mk_self,
  Polyfold.MPolyfold.tangentChartMap_injOn, Polyfold.MPolyfold.tangentChartMap_mk_ofVec,
  Polyfold.MPolyfold.tangentChartMap_mk_ofVec_of_mem]
#rt_check RoundTrip.V2_19.B_to_A [Polyfold.MPolyfold.tangentChartMap_mk_self,
  Polyfold.MPolyfold.tangentChartMap_injOn, Polyfold.MPolyfold.tangentChartMap_mk_ofVec,
  Polyfold.MPolyfold.tangentChartMap_mk_ofVec_of_mem]
#rt_overlap RoundTrip.V2_19.B_to_A [Polyfold.MPolyfold.tangentChartMap_mk_self,
  Polyfold.MPolyfold.tangentChartMap_injOn, Polyfold.MPolyfold.tangentChartMap_mk_ofVec,
  Polyfold.MPolyfold.tangentChartMap_mk_ofVec_of_mem]

end RoundTrip.V2_19
