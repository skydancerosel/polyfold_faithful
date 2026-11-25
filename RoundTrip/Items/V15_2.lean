import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_2

set_option maxSynthPendingDepth 3

/-! Round trip for V15_2 (2021 Theorem 15.1.1, pp. 684–687; 2017: Theorem 15.1: the linearization
`T(f,Λ)` is well defined).

`A` is the conjunction of the types of the thirty theorems of the item (definitions are
vocabulary), all at universe `0` (`wsum_pair_eq_of_isLocal` has six universe parameters, all set
to `0`; the `Linearization15` model lemmas have none).

* `A_to_B`: `T := linearization f Λ`.  Functor property: `theorem_15_1_1_functor`; (2):
  `linearization_eq` with the data `(O, s, σ, c)`; (1): through the data of
  `nonempty_localLinData`, `linearization_eq` and the weighted count `IsLocalRepOn.count_eq` (no
  branch passes through `f(x)` when `Λ(f(x)) = 0`); uniqueness: a `T'` with (2) equals the formal
  sum of the data of `nonempty_localLinData` at every smooth point, i.e. `linearization f Λ`.
* `B_to_A`: not proved.  `B` speaks only about smooth points (`X_∞`) and sc⁺-multisections `Λ`;
  `A`'s `theorem_15_1_1_intrinsic`, `theorem_15_1_1` and `theorem_15_1_1_functor` hold at every
  level-`1` point, the first two for any `Λ` with the two local structures; and `A` contains
  proof-step lemmas (transport of sections along morphisms, the sc-Fredholm property of the
  summands, the separation lemma `wsum_pair_eq_of_isLocal`, …) that `B` does not mention.
  `main_B_to_A_smooth`: from `B`, the main conjunct `theorem_15_1_1_intrinsic` at smooth points for
  sc⁺-multisections.
-/

namespace RoundTrip.V15_2
open Polyfold Polyfold.SBLocalization Polyfold.Linearization15 Polyfold.StrongRetr
  Polyfold.MPolyfold

def A : Prop :=
  (type_of% @Polyfold.SBLocalization.theorem_15_1_1_intrinsic.{0}) ∧
  (type_of% @Polyfold.SBLocalization.linSumIntr_chart_independent.{0}) ∧
  (type_of% @Polyfold.SBLocalization.toIntr_chart_independent.{0}) ∧
  (type_of% @Polyfold.SBLocalization.linearization_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.nonempty_localLinData.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_1_1.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsLocalRepOn.count_eq.{0}) ∧
  (type_of% @Polyfold.Linearization15.theorem_15_1_1_model) ∧
  (type_of% @Polyfold.Linearization15.wsum_model_eq) ∧
  (type_of% @Polyfold.Linearization15.continuousOn_scDeriv_coe) ∧
  (type_of% @Polyfold.Linearization15.wsum_pair_eq_of_isLocal.{0, 0, 0, 0, 0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.subDeriv_isScFredholm.{0}) ∧
  (type_of% @Polyfold.SBLocalization.linearization_summand_isScFredholm.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_1_1_functor.{0}) ∧
  (type_of% @Polyfold.SBLocalization.conjOp_apply.{0}) ∧
  (type_of% @Polyfold.SBLocalization.muLin_apply.{0}) ∧
  (type_of% @Polyfold.SBLocalization.mem_levelSet_one_of_src.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isOpen_transSet.{0}) ∧
  (type_of% @Polyfold.SBLocalization.P_transSec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isScPlusSectionOn_transSec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isWFunctor_morIso_Φ.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isLocalRepOn_transSec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.principal_transportChart_transSec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.chartVec_transport.{0}) ∧
  (type_of% @Polyfold.SBLocalization.fiberLin_transport_muLin.{0}) ∧
  (type_of% @Polyfold.SBLocalization.fiberLin_transport_mem_range.{0}) ∧
  (type_of% @Polyfold.SBLocalization.toIntr_transportChart.{0}) ∧
  (type_of% @Polyfold.SBLocalization.linSumIntr_transportChart.{0}) ∧
  (type_of% @Polyfold.SBLocalization.linearizationFunctor_comp_grfProj_obj.{0}) ∧
  (type_of% @Polyfold.SBLocalization.linearizationFunctor_obj.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.theorem_15_1_1_intrinsic.{0},
    @Polyfold.SBLocalization.linSumIntr_chart_independent.{0},
    @Polyfold.SBLocalization.toIntr_chart_independent.{0},
    @Polyfold.SBLocalization.linearization_eq.{0},
    @Polyfold.SBLocalization.nonempty_localLinData.{0},
    @Polyfold.SBLocalization.theorem_15_1_1.{0},
    @Polyfold.SBLocalization.IsLocalRepOn.count_eq.{0},
    @Polyfold.Linearization15.theorem_15_1_1_model,
    @Polyfold.Linearization15.wsum_model_eq,
    @Polyfold.Linearization15.continuousOn_scDeriv_coe,
    @Polyfold.Linearization15.wsum_pair_eq_of_isLocal.{0, 0, 0, 0, 0, 0},
    @Polyfold.SBLocalization.subDeriv_isScFredholm.{0},
    @Polyfold.SBLocalization.linearization_summand_isScFredholm.{0},
    @Polyfold.SBLocalization.theorem_15_1_1_functor.{0},
    @Polyfold.SBLocalization.conjOp_apply.{0},
    @Polyfold.SBLocalization.muLin_apply.{0},
    @Polyfold.SBLocalization.mem_levelSet_one_of_src.{0},
    @Polyfold.SBLocalization.isOpen_transSet.{0},
    @Polyfold.SBLocalization.P_transSec.{0},
    @Polyfold.SBLocalization.isScPlusSectionOn_transSec.{0},
    @Polyfold.SBLocalization.isWFunctor_morIso_Φ.{0},
    @Polyfold.SBLocalization.isLocalRepOn_transSec.{0},
    @Polyfold.SBLocalization.principal_transportChart_transSec.{0},
    @Polyfold.SBLocalization.chartVec_transport.{0},
    @Polyfold.SBLocalization.fiberLin_transport_muLin.{0},
    @Polyfold.SBLocalization.fiberLin_transport_mem_range.{0},
    @Polyfold.SBLocalization.toIntr_transportChart.{0},
    @Polyfold.SBLocalization.linSumIntr_transportChart.{0},
    @Polyfold.SBLocalization.linearizationFunctor_comp_grfProj_obj.{0},
    @Polyfold.SBLocalization.linearizationFunctor_obj.{0}⟩

/-- The pieces of `A` that `A_to_B` uses: `linearization_eq`, `nonempty_localLinData`,
`IsLocalRepOn.count_eq`, `theorem_15_1_1_functor`. -/
def Aused : Prop :=
  (type_of% @Polyfold.SBLocalization.linearization_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.nonempty_localLinData.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsLocalRepOn.count_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_1_1_functor.{0})

theorem Aused_to_B : Aused → B := by
  rintro ⟨hlin, hne, hcount, hfun⟩ Asep f Λ hf hΛ
  -- (1) for `linearization`, from the weighted count
  have h1 : ∀ x : Asep.X.PObj.Level 1, Λ (f (Asep.X.PObj.levelVal 1 x)) = 0 →
      linearization f Λ x = 0 := by
    intro x h0
    obtain ⟨d⟩ := hne hΛ x
    rw [hlin hf d]
    classical
    set y := Asep.X.PObj.levelVal 1 x
    have hsec : IsSection Asep.P f := hf.1.1.1
    have hyO : d.c.φ y ∈ d.c.φ.model.O := d.c.φ.mapsTo_model _ d.mem
    have ha : d.c.φ.model.E.toBase 1 (levelLift d.c.φ 1 y) = d.c.φ y :=
      Asep.X.PObj.toBase_levelLift d.c.isChart d.mem (levelVal_mem x)
    have hK : (d.c.φ y, d.c.principal f (d.c.φ y)) ∈ d.c.K := d.c.principal_mem_K hsec hyO
    have hw : d.c.toPartialEquiv.symm (d.c.φ y, d.c.principal f (d.c.φ y)) = f y := by
      rw [← d.c.apply_section' hsec d.mem]
      exact d.c.toPartialEquiv.left_inv (d.c.mem_source_of_proj (by rw [hsec]; exact d.mem))
    have hc := hcount d.rep d.sub hyO (d.c.principal f (d.c.φ y))
    rw [if_pos hK, hw, h0] at hc
    have hnone : ∀ i, d.c.principal (d.s i) (d.c.φ y) ≠ d.c.principal f (d.c.φ y) :=
      fun i hi => by
        have := (Finset.sum_eq_zero_iff.1 hc) i (Finset.mem_univ i)
        rw [if_pos hi] at this
        exact (d.rep.1 i).ne' this
    change linSumModelMap _ _ _ _ _ _ _ = 0
    unfold linSumModelMap
    refine Finset.sum_eq_zero fun i _ => if_neg ?_
    rw [ha]; exact hnone i
  refine ⟨linearization f Λ, ⟨?_, fun x _ h0 => h1 x h0, ?_⟩, ?_⟩
  · intro φ hφ x y hx hy _
    exact hfun hf hΛ φ hx hy
  · intro O hO k s σ hrep c hc hsub y hy _
    exact hlin hf ⟨O, hO, k, s, σ, hrep, c, hc, hsub, hy⟩
  · intro T' hT' x hx
    obtain ⟨d⟩ := hne hΛ x
    rw [hT'.2.2 d.O d.isOpen d.k d.s d.σ d.rep d.c d.isChart d.sub x d.mem hx, hlin hf d]
    rfl

theorem A_to_B : A → B := fun h =>
  Aused_to_B ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The main conjunct `theorem_15_1_1_intrinsic`. -/
def Amain : Prop := type_of% @Polyfold.SBLocalization.theorem_15_1_1_intrinsic.{0}

/-- `B ⇒ theorem_15_1_1_intrinsic` at smooth points, for sc⁺-multisections `Λ` (the setting of
`B`). -/
theorem main_B_to_A_smooth : B → ∀ (Asep : SEP.{0}) {f : Asep.Obj → Asep.W}
    (_hf : Asep.E.IsScFredholmSectionFunctor f) {Λ : Asep.W → ℚ≥0}
    (_hΛ : IsScPlusMultisection Asep Λ) {O O' : Set Asep.Obj} {k l : ℕ}
    {s : Fin k → Asep.Obj → Asep.W} {σ : Fin k → ℚ≥0} {t : Fin l → Asep.Obj → Asep.W}
    {τ : Fin l → ℚ≥0} (_hs : IsLocalRepOn Asep Λ O s σ) (_ht : IsLocalRepOn Asep Λ O' t τ)
    (_hO : IsOpen O) (_hO' : IsOpen O') {c c' : StrongBundleChart Asep.X.PObj Asep.P}
    (_hc : Asep.B.IsChart c) (_hc' : Asep.B.IsChart c') (_hsub : c.φ.source ⊆ O)
    (_hsub' : c'.φ.source ⊆ O') {x : Asep.X.PObj.Level 1}
    (hx : Asep.X.PObj.levelVal 1 x ∈ c.φ.source) (hx' : Asep.X.PObj.levelVal 1 x ∈ c'.φ.source),
    Asep.X.PObj.levelVal 1 x ∈ Asep.X.PObj.smoothSet →
      linSumIntr c hx f s σ = linSumIntr c' hx' f t τ := by
  intro hB Asep f hf Λ hΛ O O' k l s σ t τ hs ht hO hO' c c' hc hc' hsub hsub' x hx hx' hsm
  obtain ⟨T, ⟨-, -, h2⟩, -⟩ := hB Asep f Λ hf hΛ
  rw [← h2 O hO k s σ hs c hc hsub x hx hsm, ← h2 O' hO' l t τ ht c' hc' hsub' x hx' hsm]


/--
error: rt_check FAIL: RoundTrip.V15_2.Aused_to_B uses [Polyfold.SBLocalization.mem_levelSet_one_of_src]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V15_2.Aused_to_B [Polyfold.SBLocalization.theorem_15_1_1_intrinsic,
  Polyfold.SBLocalization.linSumIntr_chart_independent,
  Polyfold.SBLocalization.toIntr_chart_independent, Polyfold.SBLocalization.linearization_eq,
  Polyfold.SBLocalization.nonempty_localLinData, Polyfold.SBLocalization.theorem_15_1_1,
  Polyfold.SBLocalization.IsLocalRepOn.count_eq, Polyfold.Linearization15.theorem_15_1_1_model,
  Polyfold.Linearization15.wsum_model_eq, Polyfold.Linearization15.continuousOn_scDeriv_coe,
  Polyfold.Linearization15.wsum_pair_eq_of_isLocal, Polyfold.SBLocalization.subDeriv_isScFredholm,
  Polyfold.SBLocalization.linearization_summand_isScFredholm,
  Polyfold.SBLocalization.theorem_15_1_1_functor, Polyfold.SBLocalization.conjOp_apply,
  Polyfold.SBLocalization.muLin_apply, Polyfold.SBLocalization.mem_levelSet_one_of_src,
  Polyfold.SBLocalization.isOpen_transSet, Polyfold.SBLocalization.P_transSec,
  Polyfold.SBLocalization.isScPlusSectionOn_transSec, Polyfold.SBLocalization.isWFunctor_morIso_Φ,
  Polyfold.SBLocalization.isLocalRepOn_transSec,
  Polyfold.SBLocalization.principal_transportChart_transSec,
  Polyfold.SBLocalization.chartVec_transport, Polyfold.SBLocalization.fiberLin_transport_muLin,
  Polyfold.SBLocalization.fiberLin_transport_mem_range,
  Polyfold.SBLocalization.toIntr_transportChart, Polyfold.SBLocalization.linSumIntr_transportChart,
  Polyfold.SBLocalization.linearizationFunctor_comp_grfProj_obj,
  Polyfold.SBLocalization.linearizationFunctor_obj]
/--
error: rt_check_soft FAIL: RoundTrip.V15_2.A_to_B uses [Polyfold.SBLocalization.mem_levelSet_one_of_src]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V15_2.A_to_B [Polyfold.SBLocalization.theorem_15_1_1_intrinsic,
  Polyfold.SBLocalization.linSumIntr_chart_independent,
  Polyfold.SBLocalization.toIntr_chart_independent, Polyfold.SBLocalization.linearization_eq,
  Polyfold.SBLocalization.nonempty_localLinData, Polyfold.SBLocalization.theorem_15_1_1,
  Polyfold.SBLocalization.IsLocalRepOn.count_eq, Polyfold.Linearization15.theorem_15_1_1_model,
  Polyfold.Linearization15.wsum_model_eq, Polyfold.Linearization15.continuousOn_scDeriv_coe,
  Polyfold.Linearization15.wsum_pair_eq_of_isLocal, Polyfold.SBLocalization.subDeriv_isScFredholm,
  Polyfold.SBLocalization.linearization_summand_isScFredholm,
  Polyfold.SBLocalization.theorem_15_1_1_functor, Polyfold.SBLocalization.conjOp_apply,
  Polyfold.SBLocalization.muLin_apply, Polyfold.SBLocalization.mem_levelSet_one_of_src,
  Polyfold.SBLocalization.isOpen_transSet, Polyfold.SBLocalization.P_transSec,
  Polyfold.SBLocalization.isScPlusSectionOn_transSec, Polyfold.SBLocalization.isWFunctor_morIso_Φ,
  Polyfold.SBLocalization.isLocalRepOn_transSec,
  Polyfold.SBLocalization.principal_transportChart_transSec,
  Polyfold.SBLocalization.chartVec_transport, Polyfold.SBLocalization.fiberLin_transport_muLin,
  Polyfold.SBLocalization.fiberLin_transport_mem_range,
  Polyfold.SBLocalization.toIntr_transportChart, Polyfold.SBLocalization.linSumIntr_transportChart,
  Polyfold.SBLocalization.linearizationFunctor_comp_grfProj_obj,
  Polyfold.SBLocalization.linearizationFunctor_obj]
/- `mem_levelSet_one_of_src` is reached only through the statement of `theorem_15_1_1_functor`
(the proof term `mem_levelSet_one_of_src hx` occurs in its type, hence in `A`); with it removed
from the list both directions pass. -/
#rt_check RoundTrip.V15_2.Aused_to_B [Polyfold.SBLocalization.theorem_15_1_1_intrinsic,
  Polyfold.SBLocalization.linSumIntr_chart_independent,
  Polyfold.SBLocalization.toIntr_chart_independent, Polyfold.SBLocalization.linearization_eq,
  Polyfold.SBLocalization.nonempty_localLinData, Polyfold.SBLocalization.theorem_15_1_1,
  Polyfold.SBLocalization.IsLocalRepOn.count_eq, Polyfold.Linearization15.theorem_15_1_1_model,
  Polyfold.Linearization15.wsum_model_eq, Polyfold.Linearization15.continuousOn_scDeriv_coe,
  Polyfold.Linearization15.wsum_pair_eq_of_isLocal, Polyfold.SBLocalization.subDeriv_isScFredholm,
  Polyfold.SBLocalization.linearization_summand_isScFredholm,
  Polyfold.SBLocalization.theorem_15_1_1_functor, Polyfold.SBLocalization.conjOp_apply,
  Polyfold.SBLocalization.muLin_apply,
  Polyfold.SBLocalization.isOpen_transSet, Polyfold.SBLocalization.P_transSec,
  Polyfold.SBLocalization.isScPlusSectionOn_transSec, Polyfold.SBLocalization.isWFunctor_morIso_Φ,
  Polyfold.SBLocalization.isLocalRepOn_transSec,
  Polyfold.SBLocalization.principal_transportChart_transSec,
  Polyfold.SBLocalization.chartVec_transport, Polyfold.SBLocalization.fiberLin_transport_muLin,
  Polyfold.SBLocalization.fiberLin_transport_mem_range,
  Polyfold.SBLocalization.toIntr_transportChart, Polyfold.SBLocalization.linSumIntr_transportChart,
  Polyfold.SBLocalization.linearizationFunctor_comp_grfProj_obj,
  Polyfold.SBLocalization.linearizationFunctor_obj]
#rt_check_soft RoundTrip.V15_2.A_to_B [Polyfold.SBLocalization.theorem_15_1_1_intrinsic,
  Polyfold.SBLocalization.linSumIntr_chart_independent,
  Polyfold.SBLocalization.toIntr_chart_independent, Polyfold.SBLocalization.linearization_eq,
  Polyfold.SBLocalization.nonempty_localLinData, Polyfold.SBLocalization.theorem_15_1_1,
  Polyfold.SBLocalization.IsLocalRepOn.count_eq, Polyfold.Linearization15.theorem_15_1_1_model,
  Polyfold.Linearization15.wsum_model_eq, Polyfold.Linearization15.continuousOn_scDeriv_coe,
  Polyfold.Linearization15.wsum_pair_eq_of_isLocal, Polyfold.SBLocalization.subDeriv_isScFredholm,
  Polyfold.SBLocalization.linearization_summand_isScFredholm,
  Polyfold.SBLocalization.theorem_15_1_1_functor, Polyfold.SBLocalization.conjOp_apply,
  Polyfold.SBLocalization.muLin_apply,
  Polyfold.SBLocalization.isOpen_transSet, Polyfold.SBLocalization.P_transSec,
  Polyfold.SBLocalization.isScPlusSectionOn_transSec, Polyfold.SBLocalization.isWFunctor_morIso_Φ,
  Polyfold.SBLocalization.isLocalRepOn_transSec,
  Polyfold.SBLocalization.principal_transportChart_transSec,
  Polyfold.SBLocalization.chartVec_transport, Polyfold.SBLocalization.fiberLin_transport_muLin,
  Polyfold.SBLocalization.fiberLin_transport_mem_range,
  Polyfold.SBLocalization.toIntr_transportChart, Polyfold.SBLocalization.linSumIntr_transportChart,
  Polyfold.SBLocalization.linearizationFunctor_comp_grfProj_obj,
  Polyfold.SBLocalization.linearizationFunctor_obj]
#rt_check RoundTrip.V15_2.main_B_to_A_smooth [Polyfold.SBLocalization.theorem_15_1_1_intrinsic,
  Polyfold.SBLocalization.linSumIntr_chart_independent,
  Polyfold.SBLocalization.toIntr_chart_independent, Polyfold.SBLocalization.linearization_eq,
  Polyfold.SBLocalization.nonempty_localLinData, Polyfold.SBLocalization.theorem_15_1_1,
  Polyfold.SBLocalization.IsLocalRepOn.count_eq, Polyfold.Linearization15.theorem_15_1_1_model,
  Polyfold.Linearization15.wsum_model_eq, Polyfold.Linearization15.continuousOn_scDeriv_coe,
  Polyfold.Linearization15.wsum_pair_eq_of_isLocal, Polyfold.SBLocalization.subDeriv_isScFredholm,
  Polyfold.SBLocalization.linearization_summand_isScFredholm,
  Polyfold.SBLocalization.theorem_15_1_1_functor, Polyfold.SBLocalization.conjOp_apply,
  Polyfold.SBLocalization.muLin_apply, Polyfold.SBLocalization.mem_levelSet_one_of_src,
  Polyfold.SBLocalization.isOpen_transSet, Polyfold.SBLocalization.P_transSec,
  Polyfold.SBLocalization.isScPlusSectionOn_transSec, Polyfold.SBLocalization.isWFunctor_morIso_Φ,
  Polyfold.SBLocalization.isLocalRepOn_transSec,
  Polyfold.SBLocalization.principal_transportChart_transSec,
  Polyfold.SBLocalization.chartVec_transport, Polyfold.SBLocalization.fiberLin_transport_muLin,
  Polyfold.SBLocalization.fiberLin_transport_mem_range,
  Polyfold.SBLocalization.toIntr_transportChart, Polyfold.SBLocalization.linSumIntr_transportChart,
  Polyfold.SBLocalization.linearizationFunctor_comp_grfProj_obj,
  Polyfold.SBLocalization.linearizationFunctor_obj]

end RoundTrip.V15_2
