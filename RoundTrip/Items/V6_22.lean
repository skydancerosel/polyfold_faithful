import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_22

/-! Round trip for V6_22 (Lemma 6.19 in the case used and Proposition 6.20: `DET(T, P, ε)`).

`A` is the conjunction of the types of `LocalDetChart.frame_ne_zero` and `proposition_6_5_4`
(universes at `0`); `LocalDetChart.kerFrame` and `LocalDetChart.frame` (`ω(S) = (k₁(S) ∧ … ∧ kₙ(S))
⊗ (e₁ ∧ … ∧ e_l)*`) are definitions (vocabulary).  A says: the chart frame never vanishes, and the
frames of two charts with the same `P` (any centres and radii) differ on the common ball by a
continuous nowhere-zero factor.  B says: with the natural (final) topologies of all continuous
local frames, `λ(ker PS)`, `λ*(coker PS)` and `DET(T, P, ε)` are topological line bundles over the
ball (local linear trivializations with fibre `ℝ`).

`B → A` (proved).  `frame_ne_zero` is not in B (B's line bundle structure says nothing about one
particular vector); it is proved directly (`frame_ne_zero'`, linear algebra on the project's
definition).  `proposition_6_5_4` comes from B's third conjunct: with `P = c.P` the chart frames of
`c` and `c'` over the common ball `W` are frame pairs in B's sense (`chartKerFrame`,
`chartCokFrame`: kernel frame `kᵢ + y(kᵢ, S)`, constant lifts of the basis of `F / R(P)`), so their
frame maps are continuous for B's topology (`continuous_frameMap`); `g = dualVec(ω_c)(ω_{c'})`, and
near each `S₀` B's linear trivialization `e` gives `g = e(ω_{c'})₂ / e(ω_c)₂`, a quotient of
continuous functions with nonvanishing denominator.

`A → B` (not proved; believed true, effort).  B's content is Lemma 6.19 for the (trivial) kernel
and cokernel bundles, which the project does not formalize.  To build B's trivializations from A
one needs (i) for EVERY continuous local frame `σ` of `ker(PS)` and `f` of `coker(PS)` (B's final
topology runs over all of them, not only chart frames), the continuity of their coefficients
relative to the chart frame (`det(kerProj ∘ σ)`, `det([f])⁻¹` in `F/R(P)`, and their product), and
(ii) the construction of an `OpenPartialHomeomorph`/`Trivialization` for the final topologies of
`λ`, `λ*` and `det` (continuity of the coordinate map out of a `⨆ coinduced` topology, the inverse
being a chart frame map).  A supplies only `frame_ne_zero` for this; `proposition_6_5_4` (two charts
with the same `P`) is not even needed on a single ball.  Re-proving (i)–(ii) is the substance of
Lemma 6.19, not glue.
-/

namespace RoundTrip.V6_22
open Polyfold Bundle Module TensorProduct

/-- The project's statement (`frame_ne_zero` and Proposition 6.20), universes instantiated at
`0`. -/
def A : Prop :=
  type_of% @Polyfold.LocalDetChart.frame_ne_zero.{0, 0} ∧
  type_of% @Polyfold.proposition_6_5_4.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.LocalDetChart.frame_ne_zero.{0, 0}, @Polyfold.proposition_6_5_4.{0, 0}⟩

section BtoA

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- `ω(S) ≠ 0`, proved directly (linear algebra on the project's definition; not in B). -/
theorem frame_ne_zero' (c : LocalDetChart E F) (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    c.frame S hS ≠ 0 := by
  have := c.finiteDimensional_coker S hS
  exact tmul_ne_zero_of_ne_zero (c.wedge_kerFrame_ne_zero S hS)
    (dualVec_ne_zero finrank_maxPow (c.wedge_cokerFrame_ne_zero S hS))

omit [CompleteSpace E] [CompleteSpace F] in
/-- A chart is admissible in B's sense. -/
theorem isDetChart (c : LocalDetChart E F) : IsDetChart c.T c.P c.ε :=
  ⟨c.isFredholm, c.isGoodLeftProj, c.ε_pos, c.isGoodLeftProj_of_lt, c.Y, c.isTopCompl,
    fun S hS => by
      obtain ⟨e, he⟩ := c.exists_equiv_of_lt S hS
      exact ⟨e, fun y => by rw [← coe_projRestrict_apply, ← he]; rfl⟩⟩

/-- The kernel frame `kᵢ(S) = kᵢ + y(kᵢ, S)` of a chart, as a continuous local frame in B's sense
over `U` (inside the chart's ball). -/
noncomputable def chartKerFrame (d : LocalDetChart E F) (U : Set (E →L[ℝ] F))
    (hU : ∀ S ∈ U, ‖S - d.T‖ < d.ε) : KerFrame d.P U where
  n := finrank ℝ d.K
  σ S i := d.kerMap S (Module.finBasis ℝ d.K i)
  cont := by
    refine continuous_pi fun i => ?_
    have h := (d.continuousOn_kerMap_apply (Module.finBasis ℝ d.K i : E)).comp_continuous
      (continuous_subtype_val (p := fun S => S ∈ U)) fun S => hU S S.2
    exact h
  mem S i := (d.lemma_6_5_2).2.1 S (hU S S.2) _ (Module.finBasis ℝ d.K i).2
  li S := by
    have h := (d.kerFrame_linearIndependent S (hU S S.2)).map' _ (Submodule.ker_subtype _)
    have heq : ⇑(LinearMap.ker ((d.P ∘L (S : E →L[ℝ] F) : E →L[ℝ] F) : E →ₗ[ℝ] F)).subtype ∘
        d.kerFrame S (hU S S.2) = fun i => d.kerMap S (Module.finBasis ℝ d.K i) := by
      funext i
      simp only [Function.comp_apply, Submodule.coe_subtype, LocalDetChart.kerFrame,
        LocalDetChart.coe_kerEquiv_apply]
    rw [heq] at h
    exact h
  card S := (d.kerEquiv S (hU S S.2)).finrank_eq

/-- A lift to `F` of the standard basis of `F / R(P)`. -/
noncomputable def cokLift (P : F →L[ℝ] F) [FiniteDimensional ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F))]
    (j : Fin (finrank ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)))) : F :=
  (Submodule.Quotient.mk_surjective _ (Module.finBasis ℝ _ j)).choose

omit [CompleteSpace F] in
theorem cokLift_spec (P : F →L[ℝ] F) [FiniteDimensional ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F))]
    (j : Fin (finrank ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)))) :
    (Submodule.Quotient.mk (cokLift P j) : F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) =
      Module.finBasis ℝ _ j :=
  (Submodule.Quotient.mk_surjective _ (Module.finBasis ℝ _ j)).choose_spec

omit [CompleteSpace E] [CompleteSpace F] in
/-- The classes of the lifts are the chart's cokernel frame. -/
theorem mk_cokLift (d : LocalDetChart E F) (S : E →L[ℝ] F) (hS : ‖S - d.T‖ < d.ε) :
    (fun j => (Submodule.Quotient.mk (cokLift d.P j) :
      F ⧸ LinearMap.range ((d.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F))) = d.cokerFrame S hS := by
  funext j
  simp only [LocalDetChart.cokerFrame, Function.comp_apply, ← cokLift_spec d.P j, cokerCompEquiv]
  rfl

/-- The constant cokernel frame of a chart (the lifts of the standard basis of `F / R(P)`). -/
noncomputable def chartCokFrame (d : LocalDetChart E F) (U : Set (E →L[ℝ] F))
    (hU : ∀ S ∈ U, ‖S - d.T‖ < d.ε) : CokFrame d.P U where
  l := finrank ℝ (F ⧸ LinearMap.range (d.P : F →ₗ[ℝ] F))
  f _ j := cokLift d.P j
  cont := continuous_const
  li S := by
    rw [mk_cokLift d S (hU S S.2)]
    exact d.cokerFrame_linearIndependent S (hU S S.2)
  card S := (cokerCompEquiv (d.isGoodLeftProj_of_lt S (hU S S.2))).symm.finrank_eq

/-- The frame of B's frame pair is the chart's frame `ω(S)`. -/
theorem wedgeAt_tmul_dualAt (d : LocalDetChart E F) (U : Set (E →L[ℝ] F))
    (hU : ∀ S ∈ U, ‖S - d.T‖ < d.ε) (S : U) :
    (chartKerFrame d U hU).wedgeAt S ⊗ₜ[ℝ] (chartCokFrame d U hU).dualAt S =
      d.frame S (hU S S.2) := by
  simp only [CokFrame.dualAt, LocalDetChart.frame]
  congr 2
  exact congrArg (fun v => wedge v _) (mk_cokLift d S (hU S S.2))

omit [CompleteSpace E] [CompleteSpace F] in
/-- A frame map of a frame pair is continuous for the natural topology (final topology). -/
theorem continuous_frameMap (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ) (U : OpenSub T ε)
    (k : KerFrame P U.1) (f : CokFrame P U.1) :
    @Continuous _ _ _ (natTopD T P ε)
      (frameMap (Fib := LD T P ε) U (fun S => k.wedgeAt S ⊗ₜ[ℝ] f.dualAt S)) :=
  continuous_iff_coinduced_le.2 (le_iSup (fun i : (Σ U : OpenSub T ε,
      KerFrame P U.1 × CokFrame P U.1) =>
    TopologicalSpace.coinduced (frameMap (Fib := LD T P ε) i.1
      (fun S => i.2.1.wedgeAt S ⊗ₜ[ℝ] i.2.2.dualAt S)) inferInstance) ⟨U, (k, f)⟩)

/-- `det(P S)` is a line on the ball of a chart. -/
theorem finrank_det (c : LocalDetChart E F) (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    finrank ℝ (fredholmDet (c.P ∘L S)) = 1 := by
  have := c.finiteDimensional_ker S hS
  have := c.finiteDimensional_coker S hS
  exact finrank_linDet _

set_option maxHeartbeats 1000000 in
/-- Proposition 6.20 from B (see the module docstring). -/
theorem prop620 (hB : B) (c c' : LocalDetChart E F) (hP : c'.P = c.P) :
    ∃ g : (E →L[ℝ] F) → ℝ, ContinuousOn g {S | ‖S - c.T‖ < c.ε ∧ ‖S - c'.T‖ < c'.ε} ∧
      ∀ (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) (hS' : ‖S - c'.T‖ < c'.ε), g S ≠ 0 ∧
        linDetEquivOfEq (congrArg (fun A : F →L[ℝ] F => ((A ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) hP)
          (c'.frame S hS') = g S • c.frame S hS := by
  rcases c' with ⟨T', hT', P', hP', Y', hY', ε', hε', h1', h2'⟩
  change P' = c.P at hP
  subst hP
  set c' : LocalDetChart E F := ⟨T', hT', c.P, hP', Y', hY', ε', hε', h1', h2'⟩ with hc'
  set W : Set (E →L[ℝ] F) := {S | ‖S - c.T‖ < c.ε ∧ ‖S - c'.T‖ < c'.ε} with hWdef
  have hW : IsOpen W :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
  classical
  let g : (E →L[ℝ] F) → ℝ := fun S =>
    if h : S ∈ W then dualVec (c.frame S h.1) (c'.frame S h.2) else 0
  have hgS : ∀ (S : E →L[ℝ] F) (h : S ∈ W), c'.frame S h.2 = g S • c.frame S h.1 := by
    intro S h
    simp only [g, dif_pos h]
    exact (dualVec_apply_smul (finrank_det c S h.1) (frame_ne_zero' c S h.1) _).symm
  refine ⟨g, ?_, fun S hS hS' => ⟨fun h0 => ?_, ?_⟩⟩
  rotate_left
  · have := hgS S ⟨hS, hS'⟩
    rw [h0, zero_smul] at this
    exact frame_ne_zero' c' S hS' this
  · rw [linDetEquivOfEq_self, LinearEquiv.refl_apply]
    exact hgS S ⟨hS, hS'⟩
  -- continuity, from B's trivializations
  intro S₀ hS₀
  let _ := natTopD c.T c.P c.ε
  obtain ⟨e, he0, hlin⟩ := (hB c.T c.P c.ε (isDetChart c)).2.2
    ⟨S₀, mem_ball_iff_norm.2 hS₀.1⟩
  let U : OpenSub c.T c.ε := ⟨W, hW, fun S hS => mem_ball_iff_norm.2 hS.1⟩
  let kf := chartKerFrame c W fun S h => h.1
  let cf := chartCokFrame c W fun S h => h.1
  let kf' : KerFrame c.P W := chartKerFrame c' W fun S h => h.2
  let cf' : CokFrame c.P W := chartCokFrame c' W fun S h => h.2
  have hfm := continuous_frameMap c.T c.P c.ε U kf cf
  have hfm' := continuous_frameMap c.T c.P c.ε U kf' cf'
  set V : Set (E →L[ℝ] F) := W ∩ Subtype.val '' e.baseSet with hVdef
  have hVo : IsOpen V := hW.inter (Metric.isOpen_ball.isOpenMap_subtype_val _ e.open_baseSet)
  have hS₀V : S₀ ∈ V := ⟨hS₀, _, he0, rfl⟩
  suffices hV : ContinuousOn g V from
    (hV.continuousAt (hVo.mem_nhds hS₀V)).continuousWithinAt
  have hxb : ∀ x : V, (⟨x.1, mem_ball_iff_norm.2 x.2.1.1⟩ : Metric.ball c.T c.ε) ∈ e.baseSet := by
    intro x
    obtain ⟨y, hy, hyx⟩ := x.2.2
    have : y = ⟨x.1, mem_ball_iff_norm.2 x.2.1.1⟩ := Subtype.ext hyx
    rwa [← this]
  have hin : Continuous fun x : V => ((⟨x.1, x.2.1⟩ : W), (1 : ℝ)) :=
    (Continuous.subtype_mk continuous_subtype_val _).prodMk continuous_const
  have hsrc : ∀ x : V, frameMap (Fib := LD c.T c.P c.ε) U
      (fun S => kf.wedgeAt S ⊗ₜ[ℝ] cf.dualAt S) (⟨x.1, x.2.1⟩, 1) ∈ e.source :=
    fun x => e.mem_source.2 (hxb x)
  have hsrc' : ∀ x : V, frameMap (Fib := LD c.T c.P c.ε) U
      (fun S => kf'.wedgeAt S ⊗ₜ[ℝ] cf'.dualAt S) (⟨x.1, x.2.1⟩, 1) ∈ e.source :=
    fun x => e.mem_source.2 (hxb x)
  have hφ := e.continuousOn.comp_continuous (hfm.comp hin) hsrc
  have hφ' := e.continuousOn.comp_continuous (hfm'.comp hin) hsrc'
  -- the values of the frame maps
  have hv : ∀ x : V, frameMap (Fib := LD c.T c.P c.ε) U
      (fun S => kf.wedgeAt S ⊗ₜ[ℝ] cf.dualAt S) (⟨x.1, x.2.1⟩, 1) =
      ⟨⟨x.1, mem_ball_iff_norm.2 x.2.1.1⟩, c.frame x.1 x.2.1.1⟩ := by
    intro x
    simp only [frameMap, one_smul]
    rw [wedgeAt_tmul_dualAt c W (fun S h => h.1) ⟨x.1, x.2.1⟩]
  have hv' : ∀ x : V, frameMap (Fib := LD c.T c.P c.ε) U
      (fun S => kf'.wedgeAt S ⊗ₜ[ℝ] cf'.dualAt S) (⟨x.1, x.2.1⟩, 1) =
      ⟨⟨x.1, mem_ball_iff_norm.2 x.2.1.1⟩, c'.frame x.1 x.2.1.2⟩ := by
    intro x
    simp only [frameMap, one_smul]
    exact congrArg _ (wedgeAt_tmul_dualAt c' W (fun S h => h.2) ⟨x.1, x.2.1⟩)
  have hφne : ∀ x : V, (e ⟨⟨x.1, mem_ball_iff_norm.2 x.2.1.1⟩, c.frame x.1 x.2.1.1⟩).2 ≠ 0 := by
    intro x h0
    have := (e.linearEquivAt ℝ _ (hxb x)).map_eq_zero_iff.1 h0
    exact frame_ne_zero' c x.1 x.2.1.1 this
  have heq : V.domRestrict g = fun x : V =>
      (e ⟨⟨x.1, mem_ball_iff_norm.2 x.2.1.1⟩, c'.frame x.1 x.2.1.2⟩).2 /
        (e ⟨⟨x.1, mem_ball_iff_norm.2 x.2.1.1⟩, c.frame x.1 x.2.1.1⟩).2 := by
    funext x
    rw [Set.domRestrict_apply, eq_div_iff (hφne x)]
    have h1 := hgS x.1 x.2.1
    have h2 : (e ⟨⟨x.1, mem_ball_iff_norm.2 x.2.1.1⟩, c'.frame x.1 x.2.1.2⟩).2 =
        e.linearEquivAt ℝ _ (hxb x) (c'.frame x.1 x.2.1.2) := rfl
    rw [h2, h1, LinearEquiv.map_smul, smul_eq_mul]
    rfl
  rw [continuousOn_iff_continuous_domRestrict, heq]
  refine Continuous.div ?_ ?_ hφne
  · have := continuous_snd.comp hφ'
    refine this.congr fun x => ?_
    simp only [Function.comp_apply]
    rw [hv' x]
  · have := continuous_snd.comp hφ
    refine this.congr fun x => ?_
    simp only [Function.comp_apply]
    rw [hv x]

end BtoA

/-- `B ⇒ A`: `frame_ne_zero` directly (not in B), Proposition 6.20 from B's trivializations. -/
theorem B_to_A : B → A :=
  fun hB => ⟨fun c S hS => frame_ne_zero' c S hS, fun c c' hP => prop620 hB c c' hP⟩

#rt_check RoundTrip.V6_22.B_to_A [Polyfold.LocalDetChart.frame_ne_zero, Polyfold.proposition_6_5_4]
#rt_overlap RoundTrip.V6_22.B_to_A [Polyfold.LocalDetChart.frame_ne_zero,
  Polyfold.proposition_6_5_4]

/-! `A_to_B` is not proved: see the module docstring (Lemma 6.19 for the final topologies is not
in A and not formalized in the project). -/

end RoundTrip.V6_22
