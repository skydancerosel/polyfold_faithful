import Polyfold.Chapter4.Poincare448Shift
import Polyfold.Chapter4.GapP1_OpenForms

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.4, **Lemma 4.4.8**
(Poincaré Lemma, p. 199; proof in §4.5.3, pp. 203–204): the reduction to Lemma 4.5.2 (part of
gap G.80).

# The Poincaré Lemma 4.4.8 from its local form 4.5.2

## The text, paraphrased

(Lemma 4.4.8) Every `x ∈ X` has open neighbourhoods `V(x) ⊆ U(x)` such that every closed
`[ω] ∈ Ωᵏ_∞(U(x))`, `k ≥ 1`, has `[τ] ∈ Ωᵏ⁻¹_∞(V(x))` with `d[τ] = [ω]` on `V(x)`.
(Proof) In a chart `(O, C, E)` around `x` with a retraction `r : W → W`, `r(W) = O`, take
`B_ε(x) ∩ C ⊆ W`, `U(x) = B_ε(x) ∩ O`, `δ` with `r(B_δ(x) ∩ C) ⊆ U(x)` and
`V(x) = r(B_δ(x) ∩ r⁻¹(B_δ(x)))`.  Pull a representative `ω ∈ Ωᵏ(U^i)` back by
`r : B_δ(x) ∩ C → U(x)`, apply Lemma 4.5.2 on the convex set `(B_δ(x) ∩ C)^i`, and pull the
primitive back by the inclusion `j : V(x) → B_δ(x) ∩ C`: `d(j^*τ) = j^*r^*ω = ω` on `V(x)^{i+1}`.

## What is formalized

* `IsConvexPiece M`: the retract `O` of a local model is relatively open in `C`, convex, and
  contains a smooth point; `IsConvexPiece.shiftIter` (it passes to every level `Oᵐ ⊆ Eᵐ`).
* `LocalPoincare`: **the statement of Lemma 4.5.2** in the form the proof of Lemma 4.4.8 uses —
  for every convex relatively open `D` of a partial quadrant containing a smooth point `c`
  (the centre of the homotopy `c + t(y − c)`; `c = 0` in the text), every closed sc-form of
  positive degree on `D` has a primitive (`MPolyfold.HasPoincare`).
* `hasPoincare_lift`: then the same holds on every level `D^m` (`LocalModel.liftEquiv`).
* The geometry of the proof: `exists_poincareChart` (the chart, the retraction, `ε`, `δ`),
  `isScSmoothMap_retractChart` (`φ⁻¹ ∘ r : B_δ(x) ∩ C → X` is sc-smooth) and
  `isScSmoothMap_chartInto` (`φ : V(x) → B_δ(x) ∩ C` is sc-smooth), with `V(x) = φ⁻¹(B_δ(φ(x)))`
  (this is the text's `r(B_δ(x) ∩ r⁻¹(B_δ(x)))`, since `r = id` on `O`).
* `exists_primitive_of_factor`: the computation `d(j^*τ) = j^*r^*ω = ω` on the direct limits.
* `lemma_4_4_8_of_local` (**Lemma 4.4.8**, given `LocalPoincare`): with `U(x)`, `V(x)` open
  (Part I's open sub-M-polyfolds, `BundledMPolyfold.openSub`), every closed
  `a ∈ Ω^{k+1}_∞(U(x))` has `b ∈ Ωᵏ_∞(V(x))` with `db = a|V(x)`.

## The reading

* `x ↦ φ(x)` is in general only a point of level `0`, so `B_δ(φ(x)) ∩ C` does not contain `0`
  and the centre of the homotopy of Lemma 4.5.2 must be another point; it must be smooth for the
  homotopy to be sc-smooth on every level.  `B_δ(φ(x)) ∩ C` contains smooth points
  (`exists_smooth_mem_relOpen`).  This is the form `LocalPoincare` asks for.
-/

open Set Function Metric

noncomputable section

namespace Polyfold

universe u v w

open MPolyfold BundledMPolyfold

/-! ### Convex pieces -/

/-- The retract `O` of the local model `M` is a **convex piece**: relatively open in the partial
quadrant `C`, convex, with a smooth point. -/
def IsConvexPiece (M : LocalModel) : Prop :=
  IsRelOpenInQuadrant M.E M.C M.O ∧ Convex ℝ M.O ∧ ∃ c ∈ M.O, c ∈ M.E.smooth

namespace IsConvexPiece

variable {M : LocalModel}

lemma nonempty (h : IsConvexPiece M) : M.O.Nonempty :=
  let ⟨_, _, c, hc, _⟩ := h
  ⟨c, hc⟩

theorem shift (h : IsConvexPiece M) : IsConvexPiece M.shift := by
  obtain ⟨hD, hcv, c, hcD, hc⟩ := h
  obtain ⟨c₁, hc₁⟩ := M.E.mem_smooth_iff.1 hc 1
  refine ⟨hD.shift, hcv.linear_preimage (M.E.toBase 1).toLinearMap, c₁, ?_, ?_⟩
  · change M.E.toBase 1 c₁ ∈ M.O
    rw [hc₁]
    exact hcD
  · change c₁ ∈ M.E.shift.smoothLvl 0
    rw [ScBanach.shift_smoothLvl]
    change M.E.toBase 1 c₁ ∈ M.E.smooth
    rw [hc₁]
    exact hc

theorem shiftIter (h : IsConvexPiece M) : ∀ m, IsConvexPiece (M.shiftIter m)
  | 0 => h
  | m + 1 => (shiftIter h m).shift

end IsConvexPiece

/-- **Lemma 4.5.2 (2021 p. 202), in the form used by the proof of Lemma 4.4.8**: for every convex
relatively open subset `D` of a partial quadrant `C ⊆ E` containing a smooth point, every closed
sc-differential `(k+1)`-form on `D` has a primitive. -/
def LocalPoincare : Prop :=
  ∀ (E : ScBanach) (C D : Set (E 0)) (hD : IsRelOpenInQuadrant E C D) (hne : D.Nonempty),
    Convex ℝ D → (∃ c ∈ D, c ∈ E.smooth) → ∀ k, (hD.toMPolyfold hne).HasPoincare k

/-- Under `LocalPoincare`, the Poincaré property holds on every level `D^m` of a convex piece. -/
theorem hasPoincare_lift (h452 : LocalPoincare) {M : LocalModel} (h : IsConvexPiece M)
    (m k : ℕ) : ((BundledMPolyfold.of (M.toMPolyfold h.nonempty)).lift m).P.HasPoincare k :=
  HasPoincare.of_scEquiv (LocalModel.liftEquiv (fun m => (h.shiftIter m).nonempty) m)
    (h452 _ _ _ (h.shiftIter m).1 _ (h.shiftIter m).2.1 (h.shiftIter m).2.2 k)

/-! ### Smooth points of relatively open subsets of partial quadrants -/

/-- A nonempty relatively open subset of a partial quadrant contains a smooth point (the smooth
points are dense, and a partial quadrant is convex with nonempty interior). -/
theorem exists_smooth_mem_relOpen {E : ScBanach} {C D : Set (E 0)} (hD : IsRelOpenInQuadrant E C D)
    (hne : D.Nonempty) : ∃ c ∈ D, c ∈ E.smooth := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨W, hW, rfl⟩ := hD.relOpen
  have hC := hD.isPartialQuadrant
  have hint : (interior C).Nonempty := hC.interior_lvlSet_nonempty 0
  have hcl : y ∈ closure (interior C) := by
    rw [hC.convex.closure_interior_eq_closure_of_nonempty_interior hint]
    exact subset_closure hy.2
  obtain ⟨z, hzW, hzC⟩ := mem_closure_iff.1 hcl W hW hy.1
  obtain ⟨c, hcs, hc⟩ := (E.dense_smooth 0).exists_mem_open (hW.inter _root_.isOpen_interior)
    ⟨z, hzW, hzC⟩
  exact ⟨c, ⟨hc.1, interior_subset hc.2⟩, hcs⟩

/-! ### The geometry of the proof -/

section Geometry

variable {A : BundledMPolyfold.{u}} {φ : MChart A.carrier} (hφ : A.P.IsChart φ)
  (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ.model.O) {p : φ.model.E 0}
  {ε δ : ℝ} (hball : ball p ε ∩ φ.model.C ⊆ R.U) (hδε : δ ≤ ε)
  (hRδ : ∀ z ∈ ball p δ ∩ φ.model.C, R z ∈ ball p ε)

lemma relOpenInQuadrant_subset_poincare {E : ScBanach} {C U : Set (E 0)}
    (h : IsRelOpenInQuadrant E C U) : U ⊆ C := by
  obtain ⟨W, -, rfl⟩ := h.relOpen
  exact inter_subset_right

include R in
/-- `B_δ(p) ∩ C` is relatively open in `C`. -/
lemma isRelOpen_ballInter : IsRelOpenInQuadrant φ.model.E φ.model.C (ball p δ ∩ φ.model.C) :=
  ⟨R.relOpen.isPartialQuadrant, ball p δ, isOpen_ball, rfl⟩

include hball hδε in
lemma ballInter_subset : ball p δ ∩ φ.model.C ⊆ R.U :=
  fun _ hz => hball ⟨ball_subset_ball hδε hz.1, hz.2⟩

include hR hball hδε in
lemma retract_mem_model (z : ↥(ball p δ ∩ φ.model.C)) : R z ∈ φ.model.O :=
  hR ▸ R.apply_mem_retract (ballInter_subset R hball hδε z.2)

include hφ hR hball hδε in
/-- **`φ⁻¹ ∘ r : B_δ(x) ∩ C → X` is sc-smooth** (in the chart `id` of `B_δ(x) ∩ C` and `φ` it
is `r`). -/
theorem isScSmoothMap_retractChart (hne : (ball p δ ∩ φ.model.C).Nonempty) :
    ((isRelOpen_ballInter (δ := δ) R).toMPolyfold hne).IsScSmoothMap A.P
      fun z => φ.symm (R z) := by
  have hDU := ballInter_subset R hball hδε
  have hRO := retract_mem_model R hR hball hδε
  have hcont : Continuous fun z : ↥(ball p δ ∩ φ.model.C) => φ.symm (R z) := by
    have h1 : ContinuousOn R (ball p δ ∩ φ.model.C) :=
      R.isSc1.isSc0.continuousOn_base.mono hDU
    have h2 : Continuous fun z : ↥(ball p δ ∩ φ.model.C) => R z :=
      h1.comp_continuous continuous_subtype_val fun z => z.2
    exact φ.continuousOn_invFun.comp_continuous h2 hRO
  set σ := (LocalModel.ofRelOpen (isRelOpen_ballInter (δ := δ) R)).selfChart hne
  refine IsScSmoothOn.of_exists_charts isOpen_univ hcont.continuousOn fun z _ =>
    ⟨σ, φ, univ, (isRelOpen_ballInter R).selfChart_isChart hne, hφ, isOpen_univ, mem_univ z,
      fun y _ => ⟨mem_univ y, mem_univ y⟩, fun y _ => φ.symm_mapsTo (hRO y), ?_⟩
  have hmap : IsScSmoothRetractMap φ.model.E φ.model.C (ball p δ ∩ φ.model.C) φ.model.E
      φ.model.C φ.model.O R :=
    (R.isScSmoothRetractMap.mono_source R.relOpen.isScRetract hDU).mono_target
      fun z hz => hR ▸ R.apply_mem_retract (hDU hz)
  refine (hmap.mono_source (isRelOpen_ballInter R).isScRetract
    (σ.image_subset_model fun y _ => mem_univ y)).congr ?_
  rintro _ ⟨y, -, rfl⟩
  have hy : σ.symm (σ y) = y := σ.symm_apply_apply (mem_univ y)
  exact (φ.apply_symm_apply (hRO y)).symm.trans
    (congrArg (fun w : ↥(ball p δ ∩ φ.model.C) => φ (φ.symm (R w.1))) hy.symm)

include hR in
/-- The points of `V = φ⁻¹(B_δ(p))` are mapped by `φ` into `B_δ(p) ∩ C`. -/
lemma chart_mem_ballInter {v : A.carrier} (hv : v ∈ φ.source ∩ φ ⁻¹' ball p δ) :
    φ v ∈ ball p δ ∩ φ.model.C :=
  ⟨hv.2, relOpenInQuadrant_subset_poincare R.relOpen
    (R.retract_subset (hR ▸ φ.mapsTo_model v hv.1))⟩

lemma isOpen_chartBall (δ : ℝ) : IsOpen (φ.source ∩ φ ⁻¹' ball p δ) :=
  φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source isOpen_ball

include hφ hR in
/-- **The chart `φ : V(x) → B_δ(x) ∩ C` is sc-smooth** on the open sub-M-polyfold `V(x)` (in the
charts `φ|V` and `id` it is the identity). -/
theorem isScSmoothMap_chartInto (hne : (ball p δ ∩ φ.model.C).Nonempty)
    [Nonempty ↥(φ.source ∩ φ ⁻¹' ball p δ)] [ParacompactSpace ↥(φ.source ∩ φ ⁻¹' ball p δ)] :
    (A.P.restrictOpen (isOpen_chartBall (p := p) δ)).IsScSmoothMap
      ((isRelOpen_ballInter (δ := δ) R).toMPolyfold hne)
      fun v => (⟨φ v.1, chart_mem_ballInter R hR v.2⟩ : ↥(ball p δ ∩ φ.model.C)) := by
  set Vs := φ.source ∩ φ ⁻¹' ball p δ
  have hVo : IsOpen Vs := isOpen_chartBall δ
  have hcont : Continuous fun v : ↥Vs =>
      (⟨φ v.1, chart_mem_ballInter R hR v.2⟩ : ↥(ball p δ ∩ φ.model.C)) :=
    (φ.continuousOn_toFun.comp_continuous continuous_subtype_val fun v => v.2.1).subtype_mk _
  set φ' := φ.restrict (s := Vs) inter_subset_left hVo
  have hφ'c : A.P.IsChart φ' := MPolyfold.IsChart.restrict A.P hφ _ _
  set φ'' := φ'.restrictTo (V := Vs) subset_rfl
  have hφ'' : (A.P.restrictOpen hVo).IsChart φ'' := isChart_restrictTo hVo hφ'c subset_rfl
  set σ := (LocalModel.ofRelOpen (isRelOpen_ballInter (δ := δ) R)).selfChart hne
  refine IsScSmoothOn.of_exists_charts isOpen_univ hcont.continuousOn fun v _ =>
    ⟨φ'', σ, univ, hφ'', (isRelOpen_ballInter R).selfChart_isChart hne, isOpen_univ, mem_univ v,
      fun w _ => ⟨mem_univ w, w.2⟩, fun w _ => mem_univ _, ?_⟩
  refine ((isScSmoothRetractMap_id (φ'' '' univ)).mono_target ?_).congr ?_
  · rintro _ ⟨w, -, rfl⟩
    exact chart_mem_ballInter R hR w.2
  · rintro _ ⟨w, -, rfl⟩
    simp only [Function.comp_apply, id, φ''.symm_apply_apply (show w ∈ φ''.source from w.2)]
    rfl

include hR in
/-- `φ⁻¹(r(φ(v))) = v` on `V`: `r = id` on `O`. -/
lemma retractChart_chartInto {v : A.carrier} (hv : v ∈ φ.source) :
    φ.symm (R (φ v)) = v := by
  have hO : φ v ∈ R.retract := hR ▸ φ.mapsTo_model v hv
  rw [R.apply_eq_self_of_mem_retract hO, φ.symm_apply_apply hv]

end Geometry

/-! ### The computation on the direct limits -/

section Assembly

variable {B : BundledMPolyfold.{u}} {Vb : BundledMPolyfold.{v}} {DB : BundledMPolyfold.{w}}

lemma formsInftyOf_formsStep_eq' (A : BundledMPolyfold.{u}) (k i : ℕ) (ω : A.forms k i) :
    A.formsInftyOf k (i + 1) (A.formsStep k i ω) = A.formsInftyOf k i ω := by
  have h := A.formsInftyOf_formsMap k (Nat.le_succ i) ω
  rw [formsMap_succ A k le_rfl, formsMap_self] at h
  exact h

/-- **The proof of Lemma 4.4.8 on the direct limits**: if `f = ρ ∘ j` and every level of `D`
has the Poincaré property in degree `k + 1`, every closed `a ∈ Ω^{k+1}_∞(U)` has
`b ∈ Ωᵏ_∞(V)` with `db = f^*a` (the text's `d(j^*τ) = j^*r^*ω = (r ∘ j)^*ω`). -/
theorem exists_primitive_of_factor (ρ : ScMap DB.P B.P) (j : ScMap Vb.P DB.P)
    (f : ScMap Vb.P B.P) (hf : ρ.comp j = f) (k : ℕ)
    (hP : ∀ m, (DB.lift m).P.HasPoincare k) (a : B.formsInfty (k + 1))
    (ha : B.formsInftyD (k + 1) a = 0) :
    ∃ b : Vb.formsInfty k, Vb.formsInftyD k b = formsInftyPullback f (k + 1) a := by
  subst hf
  obtain ⟨i, ω, rfl⟩ := Module.DirectLimit.exists_of a
  have ha' : B.formsInftyOf (k + 1 + 1) (i + 1) (B.formsD (k + 1) i ω) = 0 :=
    (formsInftyD_of B (k + 1) i ω).symm.trans ha
  obtain ⟨j', hj', hzero⟩ := Module.DirectLimit.of.zero_exact ha'
  obtain ⟨m, rfl⟩ : ∃ m, j' = m + 1 := ⟨j' - 1, by omega⟩
  have him : i ≤ m := by omega
  set ωm := B.formsMap (k + 1) i m him ω with hωm
  have hdωm : B.formsD (k + 1) m ωm = 0 :=
    (formsD_formsMap B (k + 1) him ω).trans hzero
  set σ := formsPullback ρ (k + 1) m ωm with hσ
  have hdσ : DB.formsD (k + 1) m σ = 0 :=
    (formsD_formsPullback ρ (k + 1) m ωm).trans
      ((congrArg (formsPullback ρ (k + 1 + 1) (m + 1)) hdωm).trans (map_zero _))
  obtain ⟨τ₀, hτ₀, hdτ₀⟩ := hP m σ.1 σ.2 (congrArg Subtype.val hdσ)
  set τ : DB.forms k m := ⟨τ₀, hτ₀⟩
  have hdτ : DB.formsD k m τ = DB.formsStep (k + 1) m σ := Subtype.ext hdτ₀
  refine ⟨Vb.formsInftyOf k m (formsPullback j k m τ), ?_⟩
  have e1 := formsInftyD_of Vb k m (formsPullback j k m τ)
  have e2 := formsD_formsPullback j k m τ
  have e3 := formsPullback_formsStep j (k + 1) m σ
  have e4 := formsInftyOf_formsStep_eq' Vb (k + 1) m (formsPullback j (k + 1) m σ)
  have e5 := formsPullback_comp j (k + 1) ρ m ωm
  have e6 := formsPullback_formsMap (ρ.comp j) (k + 1) him ω
  have e7 := Vb.formsInftyOf_formsMap (k + 1) him (formsPullback (ρ.comp j) (k + 1) i ω)
  have e8 := formsInftyPullback_of (ρ.comp j) (k + 1) i ω
  refine e1.trans ?_
  refine (congrArg (Vb.formsInftyOf (k + 1) (m + 1)) (e2.trans
    (congrArg (formsPullback j (k + 1) (m + 1)) hdτ))).trans ?_
  refine (congrArg (Vb.formsInftyOf (k + 1) (m + 1)) e3).trans ?_
  refine e4.trans ?_
  refine (congrArg (Vb.formsInftyOf (k + 1) m) (e5.symm.trans e6)).trans ?_
  exact e7.trans e8.symm

end Assembly

/-! ### Lemma 4.4.8 -/

/-- The chart, the retraction, `ε` and `δ` of the proof of Lemma 4.4.8 around `x`. -/
theorem exists_poincareChart (A : BundledMPolyfold.{u}) (x : A.carrier) :
    ∃ (φ : MChart A.carrier) (_ : A.P.IsChart φ) (_ : x ∈ φ.source)
      (R : ScRetraction φ.model.E φ.model.C) (_ : R.retract = φ.model.O) (ε δ : ℝ),
      0 < δ ∧ δ ≤ ε ∧ ball (φ x) ε ∩ φ.model.C ⊆ R.U ∧
        ∀ z ∈ ball (φ x) δ ∩ φ.model.C, R z ∈ ball (φ x) ε := by
  obtain ⟨φ, hφ, hx⟩ := A.P.exists_isChart_mem_source x
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  set p := φ x
  have hpO : p ∈ φ.model.O := φ.mapsTo_model x hx
  have hpU : p ∈ R.U := R.retract_subset (hR ▸ hpO)
  obtain ⟨W, hW, hWU⟩ := R.relOpen.relOpen
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW p (hWU ▸ hpU).1
  have hball : ball p ε ∩ φ.model.C ⊆ R.U := fun z hz => hWU ▸ ⟨hεW hz.1, hz.2⟩
  have hRp : R p = p := R.apply_eq_self_of_mem_retract (hR ▸ hpO)
  have hcont : ContinuousWithinAt R R.U p := R.isSc1.isSc0.continuousOn_base p hpU
  obtain ⟨δ₀, hδ₀, hδ₀R⟩ := Metric.continuousWithinAt_iff.1 hcont ε hε
  refine ⟨φ, hφ, hx, R, hR, ε, min δ₀ ε, lt_min hδ₀ hε, min_le_right _ _, hball, ?_⟩
  intro z hz
  have hzU : z ∈ R.U := hball ⟨ball_subset_ball (min_le_right _ _) hz.1, hz.2⟩
  have := hδ₀R hzU (lt_of_lt_of_le hz.1 (min_le_left _ _))
  rw [hRp] at this
  exact this

/-- **2021 Lemma 4.4.8 (Poincaré Lemma), p. 199, from Lemma 4.5.2** (`LocalPoincare`; the
proof of §4.5.3, pp. 203–204): every `x ∈ X` has open neighbourhoods `V(x) ⊆ U(x)` such that
for every `k`, every closed `[ω] ∈ Ω^{k+1}_∞(U(x))` has `[τ] ∈ Ωᵏ_∞(V(x))` with
`d[τ] = [ω]` on `V(x)` (degrees shifted by one: the text's `k ≥ 1` is `k + 1`). -/
theorem lemma_4_4_8_of_local (h452 : LocalPoincare) (A : BundledMPolyfold.{u}) (x : A.carrier) :
    ∃ (U V : Set A.carrier) (hU : IsOpen U) (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ U),
      ∀ (k : ℕ) (a : (A.openSub hU ⟨x, hVU hxV⟩).formsInfty (k + 1)),
        (A.openSub hU ⟨x, hVU hxV⟩).formsInftyD (k + 1) a = 0 →
        ∃ b : (A.openSub hV ⟨x, hxV⟩).formsInfty k,
          (A.openSub hV ⟨x, hxV⟩).formsInftyD k b =
            A.formsInftyResOpenOpen (k + 1) hU ⟨x, hVU hxV⟩ hV ⟨x, hxV⟩ hVU a := by
  obtain ⟨φ, hφ, hx, R, hR, ε, δ, hδ, hδε, hball, hRδ⟩ := exists_poincareChart A x
  set p := φ x
  set U := φ.source ∩ φ ⁻¹' ball p ε
  set V := φ.source ∩ φ ⁻¹' ball p δ
  have hUo : IsOpen U := isOpen_chartBall ε
  have hVo : IsOpen V := isOpen_chartBall δ
  have hxV : x ∈ V := ⟨hx, mem_ball_self hδ⟩
  have hVU : V ⊆ U := fun v hv => ⟨hv.1, ball_subset_ball hδε hv.2⟩
  refine ⟨U, V, hUo, hVo, hxV, hVU, fun k a ha => ?_⟩
  -- the convex piece `D = B_δ(p) ∩ C`
  have hDrel := isRelOpen_ballInter (δ := δ) (p := p) R
  have hneD : (ball p δ ∩ φ.model.C).Nonempty := ⟨p, chart_mem_ballInter R hR hxV⟩
  have hpiece : IsConvexPiece (LocalModel.ofRelOpen hDrel) :=
    ⟨hDrel, (convex_ball p δ).inter hDrel.isPartialQuadrant.convex,
      exists_smooth_mem_relOpen hDrel hneD⟩
  set DB := BundledMPolyfold.of (hDrel.toMPolyfold hneD)
  have : Nonempty U := ⟨⟨x, hVU hxV⟩⟩
  have : ParacompactSpace U := A.P.paracompactSpace_subtype U
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : ParacompactSpace V := A.P.paracompactSpace_subtype V
  -- `ρ = φ⁻¹ ∘ r : D → U` and `j = φ : V → D`
  have hρU : ∀ z : ↥(ball p δ ∩ φ.model.C), φ.symm (R z) ∈ U := fun z =>
    ⟨φ.symm_mapsTo (retract_mem_model R hR hball hδε z), by
      change φ (φ.symm (R z)) ∈ ball p ε
      rw [φ.apply_symm_apply (retract_mem_model R hR hball hδε z)]
      exact hRδ z z.2⟩
  let ρ : ScMap DB.P (A.openSub hUo ⟨x, hVU hxV⟩).P :=
    ⟨fun z : ↥(ball p δ ∩ φ.model.C) => ⟨φ.symm (R z), hρU z⟩,
      IsScSmoothMap.codRestrict_restrictOpen hUo
      (isScSmoothMap_retractChart hφ R hR hball hδε hneD) hρU⟩
  let j : ScMap (A.openSub hVo ⟨x, hxV⟩).P DB.P :=
    ⟨fun v : ↥V => ⟨φ v.1, chart_mem_ballInter R hR v.2⟩, isScSmoothMap_chartInto hφ R hR hneD⟩
  have hρj : ρ.comp j = A.inclOpenOpen hUo ⟨x, hVU hxV⟩ hVo ⟨x, hxV⟩ hVU := by
    have h : (ρ.comp j).toFun = (A.inclOpenOpen hUo ⟨x, hVU hxV⟩ hVo ⟨x, hxV⟩ hVU).toFun := by
      funext v
      exact Subtype.ext (retractChart_chartInto R hR (v : V).2.1)
    cases hc : ρ.comp j
    cases hi : A.inclOpenOpen hUo ⟨x, hVU hxV⟩ hVo ⟨x, hxV⟩ hVU
    rw [hc, hi] at h
    simp only at h
    subst h
    rfl
  exact exists_primitive_of_factor ρ j _ hρj k (hasPoincare_lift h452 hpiece · k) a ha

end Polyfold
