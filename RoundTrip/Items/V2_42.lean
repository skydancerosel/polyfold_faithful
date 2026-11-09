import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_42

/-! Round trip for V2_42 (Proposition 2.36: `d_O = d_C`, `T^R_xO` an sc-subspace of codimension
`d_O(x)`, `C_xO` a partial quadrant).

`A` is the conjunction of the types of `Polyfold.proposition_2_5_6`, `proposition_2_5_6_degIndex`,
`quotDim_reducedTangentSpaceWith_eq`, `MPolyfold.degIndex_eq_chartDegIndex_of_isTameWith`
(universe `0`), `MPolyfold.degIndex_eq_chartDegIndex_of_isTameRetract` (universe `0`),
`LocalModel.degIndex_toMPolyfold_of_isTameWith`, `quotDim_eq_finrank_quotient_of_isCompl`
(universe `0`), `proposition_2_5_6_partialCone` and `isPartialQuadrant_ofSubspace`.  `splitIso` is a
definition (vocabulary).

`A → B`: B quantifies over every retraction `R` onto `O` (tame or not) and every presentation `T`;
`A` is stated for a retraction `R₀` that is tame with respect to `T`.  The glue: `T_xO = range Dr(x)`
does not depend on the retraction (`range_eq`, from `tangentSpace_eq_range`, i.e. Proposition 2.4),
so `T^R_xO` and `C_xO` computed with `R` and with the tame `R₀` agree; the codimension, stated in B
as a cardinal `Module.rank`, equals the natural number `quotDim` because the quotient embeds in the
finite-dimensional `E/E_x` (`rank_quot_eq`).

`B → A`: the retract statements follow from `B` applied to the tame retract `r(U)`
(`IsTameWith.isTame`: tameness for one presentation gives tameness for all).  The M-polyfold
statements (`degIndex_eq_chartDegIndex_of_isTameWith/_of_isTameRetract`: a chart `φ` on a tame
retract realizes `d_X`) follow from (14) of `B` for the local model of `φ` and Proposition 2.24
(`proposition_2_4_4`) along the sc-diffeomorphism `φ : V → O` (`chart_isScDiffeoOn`, new glue).
Three conjuncts are elementary linear algebra and are proved directly, without `B`:
`quotDim_eq_finrank_quotient_of_isCompl`, `isPartialQuadrant_ofSubspace` (the definition
`splitIso`), and `quotDim_reducedTangentSpaceWith_eq`, whose `T` is an arbitrary sc-isomorphism
`E ≅ ℝⁿ ⊕ W` (not assumed to present `C`), so it is more general than anything `B` says; its proof
is the project's two-line argument from `finrank_quotient_minimalSubspaceWith`. -/

namespace RoundTrip.V2_42
open Polyfold Set Module

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.proposition_2_5_6) ∧ (type_of% @Polyfold.proposition_2_5_6_degIndex) ∧
    (type_of% @Polyfold.quotDim_reducedTangentSpaceWith_eq) ∧
    (type_of% @Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameWith.{0}) ∧
    (type_of% @Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameRetract.{0}) ∧
    (type_of% @Polyfold.LocalModel.degIndex_toMPolyfold_of_isTameWith) ∧
    (type_of% @Polyfold.quotDim_eq_finrank_quotient_of_isCompl.{0}) ∧
    (type_of% @Polyfold.proposition_2_5_6_partialCone) ∧
    (type_of% @Polyfold.isPartialQuadrant_ofSubspace)

theorem A_holds : A :=
  ⟨@Polyfold.proposition_2_5_6, @Polyfold.proposition_2_5_6_degIndex,
    @Polyfold.quotDim_reducedTangentSpaceWith_eq,
    @Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameWith.{0},
    @Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameRetract.{0},
    @Polyfold.LocalModel.degIndex_toMPolyfold_of_isTameWith,
    @Polyfold.quotDim_eq_finrank_quotient_of_isCompl.{0}, @Polyfold.proposition_2_5_6_partialCone,
    @Polyfold.isPartialQuadrant_ofSubspace⟩

/-! ### Glue -/

/-- `T_xO = Dr(x)E` does not depend on the retraction onto `O` (Proposition 2.4). -/
theorem range_eq {E : ScBanach} {C : Set (E 0)} (R R' : ScRetraction E C)
    (h : R.retract = R'.retract) {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) :
    LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0) =
      LinearMap.range (scDeriv R'.U R' x : E 0 →ₗ[ℝ] E 0) := by
  have h1 := tangentSpace_eq_range R hx
  have h2 := tangentSpace_eq_range R' (h ▸ hx)
  rw [h] at h1
  ext v
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  change v ∈ Set.range (scDeriv R.U R x) ↔ v ∈ Set.range (scDeriv R'.U R' x)
  rw [← h1, ← h2]

/-- The cardinal codimension of `A ∩ K` in `A` is the natural number `quotDim A (A ∩ K)` when
`V/K` is finite-dimensional. -/
theorem rank_quot_eq {V : Type} [AddCommGroup V] [Module ℝ V] (A K : Submodule ℝ V)
    [FiniteDimensional ℝ (V ⧸ K)] :
    Module.rank ℝ (A ⧸ (A ⊓ K).comap A.subtype) = (quotDim A (A ⊓ K) : Cardinal) := by
  have hle : (A ⊓ K).comap A.subtype ≤ LinearMap.ker (K.mkQ.comp A.subtype) := by
    intro v hv
    simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.subtype_apply] at hv
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hv.2
  have hinj : Function.Injective (((A ⊓ K).comap A.subtype).liftQ (K.mkQ.comp A.subtype) hle) := by
    rw [← LinearMap.ker_eq_bot]
    apply Submodule.ker_liftQ_eq_bot
    intro v hv
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hv
    simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.subtype_apply]
    exact ⟨v.2, hv⟩
  have hlt : Module.rank ℝ (A ⧸ (A ⊓ K).comap A.subtype) < Cardinal.aleph0 :=
    (LinearMap.rank_le_of_injective _ hinj).trans_lt (Module.rank_lt_aleph0 ℝ (V ⧸ K))
  exact (Cardinal.cast_toNat_of_lt_aleph0 hlt).symm

/-- The partial cone does not depend on the retraction onto `O`. -/
theorem partialCone_eq {E : ScBanach} {C : Set (E 0)} {n : ℕ} {W : ScBanach} (R R' : ScRetraction E C)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (h : R.retract = R'.retract) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) : partialConeWith R T x = partialConeWith R' T x := by
  have h1 := tangentSpace_eq_range R hx
  have h2 := tangentSpace_eq_range R' (h ▸ hx)
  rw [h] at h1
  unfold partialConeWith
  rw [← h1, ← h2]

theorem A_to_B : A → B := by
  intro hA E C O hO hTame
  obtain ⟨h236, h236d, -, -, -, -, -, hcone, -⟩ := hA
  obtain ⟨R₀, hR₀, hR₀t⟩ := hTame
  subst hR₀
  refine ⟨fun x hx hsm x₁ hx₁ R hR n W T hT => ?_, fun x hx => ?_⟩
  · subst hx₁
    have htw : R₀.IsTameWith T := hR₀t n W T hT
    have hx₁O : x₁ ∈ E.lvlSet R₀.retract 1 := hx
    have hs : x₁ ∈ E.smoothLvl 1 := hsm
    have hxR : x₁ ∈ E.lvlSet R.retract 1 := by rw [hR]; exact hx₁O
    have hrange : tangentAt R x₁ = LinearMap.range (scDeriv R₀.U R₀ x₁ : E 0 →ₗ[ℝ] E 0) :=
      range_eq R R₀ hR hxR
    have hred : reducedTangentSpaceWith R T x₁ = reducedTangentSpaceWith R₀ T x₁ := by
      unfold reducedTangentSpaceWith
      rw [← hrange]
      rfl
    obtain ⟨hAsc, hredsc, hpq⟩ := hcone hT htw hx₁O hs
    obtain ⟨h13, -⟩ := h236 hT htw hx₁O hs
    refine ⟨hred ▸ hredsc, ?_, ?_⟩
    · rw [hrange, hred]
      unfold reducedTangentSpaceWith
      rw [rank_quot_eq]
      unfold reducedTangentSpaceWith at h13
      rw [h13]
      rfl
    · rw [hrange, partialCone_eq R R₀ T hR hxR]
      refine ⟨hAsc, ?_⟩
      convert hpq using 2
      ext v
      constructor
      · intro hv; exact hv.2
      · intro hv
        obtain ⟨u, hu⟩ := v.2
        exact ⟨⟨u, hu⟩, hv⟩
  · obtain ⟨n, W, T, hT⟩ := R₀.relOpen.isPartialQuadrant
    exact h236d hT (hR₀t n W T hT) ⟨x, hx⟩ ⟨x, hx⟩

/-! ### `B → A` -/

section ChartDiffeo

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

open scoped Classical in
/-- A chart `φ : V → O`, as a map into the M-polyfold `O`. -/
noncomputable def chartToModel (φ : MChart X) (hne : φ.model.O.Nonempty) : X → φ.model.O :=
  fun x => if h : φ x ∈ φ.model.O then ⟨φ x, h⟩ else ⟨hne.some, hne.some_mem⟩

omit [T2Space X] [ParacompactSpace X] in
lemma chartToModel_val {φ : MChart X} (hne : φ.model.O.Nonempty) {x : X} (hx : x ∈ φ.source) :
    (chartToModel φ hne x : φ.model.E 0) = φ x := by
  simp only [chartToModel, dif_pos (φ.mapsTo_model x hx)]

/-- A chart `φ : V → O` of an M-polyfold is an sc-diffeomorphism onto the M-polyfold `O`. -/
theorem chart_isScDiffeoOn (P : MPolyfold X) {φ : MChart X} (hφ : P.IsChart φ)
    (hne : φ.model.O.Nonempty) :
    P.IsScDiffeoOn (φ.model.toMPolyfold hne) (chartToModel φ hne)
      (fun z => φ.symm (z : φ.model.E 0)) φ.source univ := by
  have hQ : (φ.model.toMPolyfold hne).IsChart (φ.model.selfChart hne) :=
    (φ.model.toMPolyfold hne).isChart_of_mem (mem_singleton _)
  refine ⟨?_, ?_, fun _ _ => mem_univ _, fun z _ => φ.symm_mapsTo z.2, fun x hx => ?_,
    fun z _ => ?_⟩
  · have hcont : ContinuousOn (chartToModel φ hne) φ.source := by
      rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
      exact φ.continuousOn_toFun.congr fun x hx => chartToModel_val hne hx
    refine MPolyfold.IsScSmoothOn.of_exists_charts φ.isOpen_source hcont fun x hx => ?_
    refine ⟨φ, φ.model.selfChart hne, φ.source, hφ, hQ, φ.isOpen_source, hx,
      fun y hy => ⟨hy, hy⟩, fun _ _ => mem_univ _, ?_⟩
    rw [φ.image_source]
    refine (isScSmoothRetractMap_id φ.model.O).congr fun z hz => ?_
    change z = ((chartToModel φ hne (φ.symm z) : φ.model.O) : φ.model.E 0)
    rw [chartToModel_val hne (φ.symm_mapsTo hz), φ.apply_symm_apply hz]
  · have hcont : ContinuousOn (fun z : φ.model.O => φ.symm (z : φ.model.E 0)) univ :=
      continuousOn_univ.2
        (φ.continuousOn_invFun.comp_continuous continuous_subtype_val fun z => z.2)
    refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ hcont fun z _ => ?_
    refine ⟨φ.model.selfChart hne, φ, univ, hQ, hφ, isOpen_univ, mem_univ _,
      fun y _ => ⟨mem_univ _, mem_univ _⟩, fun y _ => φ.symm_mapsTo y.2, ?_⟩
    have himg : (φ.model.selfChart hne) '' univ = φ.model.O :=
      (φ.model.selfChart hne).image_source
    rw [himg]
    refine (isScSmoothRetractMap_id φ.model.O).congr fun z hz => ?_
    change z = φ (φ.symm (((φ.model.selfChart hne).symm z : φ.model.O) : φ.model.E 0))
    rw [LocalModel.selfChart_symm_apply φ.model hne hz, φ.apply_symm_apply hz]
  · rw [chartToModel_val hne hx, φ.symm_apply_apply hx]
  · apply Subtype.ext
    rw [chartToModel_val hne (φ.symm_mapsTo z.2), φ.apply_symm_apply z.2]

/-- From `B`: a chart on a tame retract realizes `d_X` (via (14) for the local model and
Proposition 2.24 along the chart). -/
theorem chart_degIndex_of_B (hB : B) (P : MPolyfold X) {φ : MChart X} (hφ : P.IsChart φ)
    (htame : IsTameRetract φ.model.E φ.model.C φ.model.O) {x : X} (hx : x ∈ φ.source) :
    P.degIndex x = MPolyfold.chartDegIndex φ x := by
  have hne : φ.model.O.Nonempty := ⟨φ x, φ.mapsTo_model x hx⟩
  rw [proposition_2_4_4 (chart_isScDiffeoOn P hφ hne) hx]
  have hF : chartToModel φ hne x = ⟨φ x, φ.mapsTo_model x hx⟩ :=
    Subtype.ext (chartToModel_val hne hx)
  rw [hF]
  exact (hB φ.model.E φ.model.C φ.model.O φ.model.isScRetract htame).2 (φ x)
    (φ.mapsTo_model x hx)

end ChartDiffeo

/-- `quotDim_eq_finrank_quotient_of_isCompl`, proved directly (linear algebra, no `B`). -/
theorem quotDim_isCompl' : type_of% @Polyfold.quotDim_eq_finrank_quotient_of_isCompl.{0} := by
  intro V _ _ A B K hAB hBK
  let Ψ : A →ₗ[ℝ] V ⧸ K := K.mkQ.comp A.subtype
  have hΨker : LinearMap.ker Ψ = (A ⊓ K).comap A.subtype := by
    ext ⟨w, hw⟩
    simp only [Ψ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf]
    exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩
  have hΨsurj : Function.Surjective Ψ := by
    intro q
    obtain ⟨v, rfl⟩ := K.mkQ_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Submodule.mem_sup.1 (hAB.sup_eq_top ▸ Submodule.mem_top (x := v))
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [Ψ, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    simpa using K.neg_mem (hBK hb)
  have hiso : (A ⧸ (A ⊓ K).comap A.subtype) ≃ₗ[ℝ] V ⧸ K :=
    hΨker ▸ Ψ.quotKerEquivOfSurjective hΨsurj
  exact hiso.finrank_eq

/-- `quotDim_reducedTangentSpaceWith_eq` (for an arbitrary sc-isomorphism `T`, not necessarily a
presentation of `C`), proved directly as in the project (no `B`). -/
theorem quotDim_red' : type_of% @Polyfold.quotDim_reducedTangentSpaceWith_eq := by
  intro E C n W R T hR x hx hs
  obtain ⟨A, hA, hAE⟩ := hR.exists_complement x hx hs
  have hcompl : IsCompl (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) A := by
    have := hA.2.2 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  rw [← finrank_quotient_minimalSubspaceWith T]
  exact quotDim_isCompl' hcompl hAE

/-- `isPartialQuadrant_ofSubspace`, directly from the definition `splitIso` (no `B`). -/
theorem isPartialQuadrant_ofSubspace' : type_of% @Polyfold.isPartialQuadrant_ofSubspace := by
  intro E A B hA hB d ℓ e hes he hℓe hBiff
  exact ⟨d, E.ofSubspace hB, splitIso hA hB ℓ e hes he hℓe hBiff, by ext v; rfl⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, quotDim_red', ?_, ?_, ?_, quotDim_isCompl', ?_, isPartialQuadrant_ofSubspace'⟩
  · -- `proposition_2_5_6`
    intro E n W C R T hT hR x hx hs
    have hBx := hB E C R.retract R.isScRetract ⟨R, rfl, hR.isTame hT⟩
    obtain ⟨-, hrk, -⟩ := hBx.1 (E.toBase 1 x) hx hs x rfl R rfl n W T hT
    refine ⟨?_, hBx.2 (E.toBase 1 x) hx⟩
    have := congrArg Cardinal.toNat hrk
    rw [Cardinal.toNat_natCast] at this
    exact this
  · -- `proposition_2_5_6_degIndex`
    intro E n W C R T hT hR hne x
    exact (hB E C R.retract R.isScRetract ⟨R, rfl, hR.isTame hT⟩).2 x x.2
  · -- `degIndex_eq_chartDegIndex_of_isTameWith`
    intro X _ _ _ P n W φ hφ R hR T hT htame x hx
    exact chart_degIndex_of_B hB P hφ ⟨R, hR, htame.isTame hT⟩ hx
  · -- `degIndex_eq_chartDegIndex_of_isTameRetract`
    intro X _ _ _ P φ hφ htame x hx
    exact chart_degIndex_of_B hB P hφ htame hx
  · -- `LocalModel.degIndex_toMPolyfold_of_isTameWith`
    intro n W M hne R hRM T hT hR x
    cases M with
    | mk E C O hO => exact (hB E C O hO ⟨R, hRM, hR.isTame hT⟩).2 x x.2
  · -- `proposition_2_5_6_partialCone`
    intro E n W C R T hT hR x hx hs
    have hBx := hB E C R.retract R.isScRetract ⟨R, rfl, hR.isTame hT⟩
    obtain ⟨hsc, -, h, hpq⟩ := hBx.1 (E.toBase 1 x) hx hs x rfl R rfl n W T hT
    refine ⟨h, hsc, ?_⟩
    have key : {v : E.levelSub (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) 0 |
        (v : E 0) ∈ partialQuadrantAtWith T (E.toBase 1 x)} =
        {v : E.levelSub (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) 0 |
          (v : E 0) ∈ partialConeWith R T x} := by
      ext v
      constructor
      · intro hv
        obtain ⟨u, hu⟩ := v.2
        exact ⟨⟨u, hu⟩, hv⟩
      · intro hv; exact hv.2
    exact (congrArg (IsPartialQuadrant (E.ofSubspace h)) key).mpr hpq

#rt_check RoundTrip.V2_42.A_to_B [Polyfold.proposition_2_5_6, Polyfold.proposition_2_5_6_degIndex,
  Polyfold.quotDim_reducedTangentSpaceWith_eq,
  Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameWith,
  Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameRetract,
  Polyfold.LocalModel.degIndex_toMPolyfold_of_isTameWith,
  Polyfold.quotDim_eq_finrank_quotient_of_isCompl, Polyfold.proposition_2_5_6_partialCone,
  Polyfold.isPartialQuadrant_ofSubspace]
#rt_check RoundTrip.V2_42.B_to_A [Polyfold.proposition_2_5_6, Polyfold.proposition_2_5_6_degIndex,
  Polyfold.quotDim_reducedTangentSpaceWith_eq,
  Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameWith,
  Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameRetract,
  Polyfold.LocalModel.degIndex_toMPolyfold_of_isTameWith,
  Polyfold.quotDim_eq_finrank_quotient_of_isCompl, Polyfold.proposition_2_5_6_partialCone,
  Polyfold.isPartialQuadrant_ofSubspace]
#rt_overlap RoundTrip.V2_42.B_to_A [Polyfold.proposition_2_5_6, Polyfold.proposition_2_5_6_degIndex,
  Polyfold.quotDim_reducedTangentSpaceWith_eq,
  Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameWith,
  Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameRetract,
  Polyfold.LocalModel.degIndex_toMPolyfold_of_isTameWith,
  Polyfold.quotDim_eq_finrank_quotient_of_isCompl, Polyfold.proposition_2_5_6_partialCone,
  Polyfold.isPartialQuadrant_ofSubspace]

end RoundTrip.V2_42
