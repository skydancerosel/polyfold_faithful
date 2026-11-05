import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_31

/-! Round trip for V2_31 (§2.3, p. 32: the subspaces `E_x`, the cones `C_x`, `dim(E/E_x) = d_C(x)`).

`A` is the conjunction of the types of the theorems listed for the item (no universe parameters
except `ScBanach.subset_closure_ker_inter_range_toBase`, instantiated at `0`):
`mem_minimalSubspaceWith`, `isClosed_minimalSubspaceWith`, `finrank_quotient_minimalSubspaceWith`,
`minimalSubspaceWith_subset_partialQuadrantAtWith`, `isClosed_partialQuadrantAtWith`,
`exists_tendsto_lvl1_degIndexWith`, `exists_tendsto_smooth_degIndexWith`,
`ScBanach.subset_closure_ker_inter_range_toBase`, `partialQuadrantAtWith_subset_closure`.
`minimalSubspaceWith` and `partialQuadrantAtWith` are the vocabulary.

* `A → B`: B (1) (`rank(E/E_x) = d_C(x)` on the standard quadrant) from A's
  `finrank_quotient_minimalSubspaceWith` with `T = id` and `mem_minimalSubspaceWith`; B (2) (the
  project's `E_x`, `C_x` are the transports of the text's) from `mem_minimalSubspaceWith`, and by
  unfolding for `C_x`.
* `B → A`: the five conjuncts about `E_x`, `C_x` are derived from B (the description of `E_x`,
  `C_x` by B (2); the codimension formula from B (1) at the point `(|a|, w)` of the quadrant,
  transported by `T`).  The four density statements (`exists_tendsto_*`,
  `subset_closure_*`) are not part of the text's definitions nor of B; they are proved here
  directly (the project's own short arguments, re-proved verbatim below), without B.
-/

namespace RoundTrip.V2_31
open Polyfold Set Filter Topology Function Module

section Density
/-! Re-proofs of the four density statements (copies of the project's proofs; not from B). -/
variable {E : ScBanach} {n : ℕ} {W : ScBanach}

theorem lvl1_approx (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (x : E 0) : ∃ (ι : Type) (l : Filter ι) (σ : ι → E 0), l.NeBot ∧ Tendsto σ l (𝓝 x) ∧
      (∀ᶠ i in l, σ i ∈ range (E.toBase 1)) ∧ (∀ i, degIndexWith T (σ i) = degIndexWith T x) ∧
      (∀ i, T 0 (σ i) ∈ quadrant n W 0 ↔ T 0 x ∈ quadrant n W 0) := by
  set a := (T 0 x).1 with ha
  set w := (T 0 x).2 with hw
  let W₁ : Set (W 0) := range (W.toBase 1)
  have hdense : Dense W₁ := by
    have := W.denseRange_incl 0
    exact this
  let σ : W 0 → E 0 := fun w' => (T 0).symm (a, w')
  refine ⟨W 0, 𝓝[W₁] w, σ, mem_closure_iff_nhdsWithin_neBot.1 (hdense w), ?_, ?_, ?_, ?_⟩
  · have hσ : Continuous σ := (T 0).symm.continuous.comp (continuous_const.prodMk continuous_id)
    have : σ w = x := by
      simp only [σ, ha, hw, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
    rw [← this]
    exact (hσ.tendsto w).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w' hw'
    obtain ⟨w₁, rfl⟩ := hw'
    refine ⟨(T 1).symm ((a, w₁) : ((ScBanach.const (Fin n → ℝ)).prod W) 1), ?_⟩
    rw [T.symm_toBase_comm, ScBanach.prod_toBase]
    simp only [σ]
    congr 2
  · intro w'
    show quadrantDeg (T 0 ((T 0).symm (a, w'))) = quadrantDeg (T 0 x)
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · intro w'
    show T 0 ((T 0).symm (a, w')) ∈ quadrant n W 0 ↔ _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact Iff.rfl

theorem smooth_approx (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (x : E 0) : ∃ (ι : Type) (l : Filter ι) (σ : ι → E 0), l.NeBot ∧ Tendsto σ l (𝓝 x) ∧
      (∀ᶠ i in l, σ i ∈ E.smooth) ∧ (∀ i, degIndexWith T (σ i) = degIndexWith T x) ∧
      (∀ i, T 0 (σ i) ∈ quadrant n W 0 ↔ T 0 x ∈ quadrant n W 0) := by
  set a := (T 0 x).1 with ha
  set w := (T 0 x).2 with hw
  let Ws : Set (W 0) := (W.smooth : Set (W 0))
  have hdense : Dense Ws := W.dense_smooth 0
  let σ : W 0 → E 0 := fun w' => (T 0).symm (a, w')
  have hcont : Continuous σ := (T 0).symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hx : σ w = x := by
    simp only [σ, ha, hw, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨W 0, 𝓝[Ws] w, σ, mem_closure_iff_nhdsWithin_neBot.1 (hdense w), ?_, ?_, ?_, ?_⟩
  · rw [← hx]
    exact (hcont.tendsto w).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w' hw'
    have hp : ((a, w') : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈
        (((ScBanach.const (Fin n → ℝ)).prod W).smoothLvl 0) := by
      rw [ScBanach.prod_smoothLvl]
      refine ⟨?_, hw'⟩
      rw [ScBanach.constScale_smoothLvl]; exact mem_univ _
    exact T.symm.toScOperator.mapsTo_smoothLvl 0 hp
  · intro w'
    change quadrantDeg (T 0 ((T 0).symm (a, w'))) = quadrantDeg (T 0 x)
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · intro w'
    change T 0 ((T 0).symm (a, w')) ∈ quadrant n W 0 ↔ _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact Iff.rfl

theorem ker_density (E : ScBanach) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : E 0 →L[ℝ] V) :
    (LinearMap.ker (L : E 0 →ₗ[ℝ] V) : Set (E 0)) ⊆
      closure ((LinearMap.ker (L : E 0 →ₗ[ℝ] V) : Set (E 0)) ∩ range (E.toBase 1)) := by
  intro v hv
  set S : Submodule ℝ (E 0) := LinearMap.range (E.toBase 1 : E 1 →ₗ[ℝ] E 0) with hS
  have hSdense : Dense (S : Set (E 0)) := by
    have : (S : Set (E 0)) = range (E.incl 0) := by
      ext z; simp [hS, LinearMap.mem_range]; rfl
    rw [this]; exact E.denseRange_incl 0
  -- a right inverse of `L|S : S → L(S)` with values in `S`
  set L₁ : S →ₗ[ℝ] V := (L : E 0 →ₗ[ℝ] V).domRestrict S with hL₁
  obtain ⟨g, hg⟩ := L₁.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 L₁.surjective_rangeRestrict)
  have hgcont : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have hLg : ∀ a : LinearMap.range L₁, L (g a : E 0) = a := fun a => by
    have := LinearMap.congr_fun hg a
    exact congrArg Subtype.val this
  -- approximate `v` by `v_k ∈ S`
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (hSdense v)
  have hLu : ∀ k, L (u k) ∈ LinearMap.range L₁ := fun k => ⟨⟨u k, hu k⟩, rfl⟩
  set a : ℕ → LinearMap.range L₁ := fun k => ⟨L (u k), hLu k⟩ with ha
  have hLv : L v = 0 := LinearMap.mem_ker.1 hv
  have ha0 : Tendsto a atTop (𝓝 ⟨0, zero_mem _⟩) := by
    rw [tendsto_subtype_rng]
    change Tendsto (fun k => L (u k)) atTop (𝓝 (0 : V))
    rw [← hLv]
    exact (L.continuous.tendsto v).comp hlim
  have hga : Tendsto (fun k => (g (a k) : E 0)) atTop (𝓝 0) := by
    have := (continuous_subtype_val.comp hgcont).tendsto (⟨0, zero_mem _⟩ : LinearMap.range L₁)
    have h0 : ((g ⟨0, zero_mem _⟩ : S) : E 0) = 0 := by
      have : (⟨0, zero_mem _⟩ : LinearMap.range L₁) = 0 := rfl
      rw [this, map_zero]; rfl
    rw [Function.comp_apply, h0] at this
    exact this.comp ha0
  refine mem_closure_of_tendsto (b := atTop) (f := fun k => u k - (g (a k) : E 0)) ?_ ?_
  · simpa using hlim.sub hga
  · refine Eventually.of_forall fun k => ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
      change L (u k) - L (g (a k) : E 0) = 0
      rw [hLg]
      simp [ha]
    · exact S.sub_mem (hu k) (g (a k)).2

theorem pq_density (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (e : E 0) :
    partialQuadrantAtWith T e ⊆ closure (partialQuadrantAtWith T e ∩ range (E.toBase 1)) := by
  intro v hv
  set a := (T 0 v).1 with ha
  set w := (T 0 v).2 with hw
  let W₁ : Set (W 0) := range (W.toBase 1)
  have hdense : Dense W₁ := W.denseRange_incl 0
  have : (𝓝[W₁] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hdense w)
  let σ : W 0 → E 0 := fun w' => (T 0).symm (a, w')
  have hσ : Continuous σ := (T 0).symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hσw : σ w = v := by
    simp only [σ, ha, hw, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  refine mem_closure_of_tendsto (b := 𝓝[W₁] w) (f := σ) ?_ ?_
  · rw [← hσw]
    exact (hσ.tendsto w).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w' hw'
    refine ⟨fun i hi => ?_, ?_⟩
    · have : (T 0 (σ w')).1 i = a i := by
        simp only [σ, ContinuousLinearEquiv.apply_symm_apply]
      rw [this]
      exact hv i hi
    · obtain ⟨w₁, rfl⟩ := hw'
      refine ⟨(T 1).symm ((a, w₁) : ((ScBanach.const (Fin n → ℝ)).prod W) 1), ?_⟩
      rw [T.symm_toBase_comm, ScBanach.prod_toBase]
      simp only [σ]
      congr 2

end Density

section Glue
variable {k : ℕ} {W : ScBanach}

lemma coordB_apply (i : Fin k) (a : (EB k W).lvl 0) : coordB (W := W) i a = a.1 i := rfl

lemma mem_EiB_iff (i : Fin k) (a : (EB k W).lvl 0) : a ∈ EiB (W := W) i ↔ a.1 i = 0 := by
  rw [EiB, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, coordB_apply]

lemma mem_ExB_iff (x v : (EB k W).lvl 0) : v ∈ ExB x ↔ ∀ i, x.1 i = 0 → v.1 i = 0 := by
  simp only [ExB, EIB, IxB, Submodule.mem_iInf, mem_ofPred_eq]
  exact forall_congr' fun i => by rw [mem_EiB_iff, mem_EiB_iff]

lemma mem_CxB_iff (x v : (EB k W).lvl 0) : v ∈ CxB x ↔ ∀ i, x.1 i = 0 → 0 ≤ v.1 i := by
  simp only [CxB, HiB, IxB, mem_iInter, mem_ofPred_eq]
  exact forall_congr' fun i => by rw [mem_EiB_iff, coordB_apply]

end Glue

/-- The project's statement (the listed theorems; universe `0` where there is one). -/
def A : Prop :=
  (type_of% @Polyfold.mem_minimalSubspaceWith) ∧
  (type_of% @Polyfold.isClosed_minimalSubspaceWith) ∧
  (type_of% @Polyfold.finrank_quotient_minimalSubspaceWith) ∧
  (type_of% @Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith) ∧
  (type_of% @Polyfold.isClosed_partialQuadrantAtWith) ∧
  (type_of% @Polyfold.exists_tendsto_lvl1_degIndexWith) ∧
  (type_of% @Polyfold.exists_tendsto_smooth_degIndexWith) ∧
  (type_of% @Polyfold.ScBanach.subset_closure_ker_inter_range_toBase.{0}) ∧
  (type_of% @Polyfold.partialQuadrantAtWith_subset_closure)

theorem A_holds : A :=
  ⟨@Polyfold.mem_minimalSubspaceWith, @Polyfold.isClosed_minimalSubspaceWith,
    @Polyfold.finrank_quotient_minimalSubspaceWith,
    @Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith,
    @Polyfold.isClosed_partialQuadrantAtWith, @Polyfold.exists_tendsto_lvl1_degIndexWith,
    @Polyfold.exists_tendsto_smooth_degIndexWith,
    @Polyfold.ScBanach.subset_closure_ker_inter_range_toBase.{0},
    @Polyfold.partialQuadrantAtWith_subset_closure⟩

/-- `A → B`. -/
theorem A_to_B : A → B := by
  rintro ⟨hmem, -, hfin, -⟩
  refine ⟨?_, ?_⟩
  · intro k W x hx
    have hE : ExB x = minimalSubspaceWith (ScIso.refl (EB k W)) x := by
      ext v
      rw [mem_ExB_iff, hmem]
      rfl
    have := finiteDimensional_quotient_minimalSubspaceWith (ScIso.refl (EB k W)) x
    rw [hE, ← Module.finrank_eq_rank, hfin, degIndex_quadrant hx]
    rfl
  · intro E n W T x
    refine ⟨?_, ?_⟩
    · ext v
      rw [SetLike.mem_coe, hmem, mem_preimage, SetLike.mem_coe, mem_ExB_iff]
    · ext v
      rw [mem_preimage, mem_CxB_iff]
      rfl

/-- `B → A`. -/
theorem B_to_A : B → A := by
  rintro ⟨hB1, hB2⟩
  have hmem : ∀ {E : ScBanach} {n : ℕ} {W : ScBanach}
      (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {x v : E.lvl 0},
      v ∈ minimalSubspaceWith T x ↔ ∀ i, (T.lvl 0 x).1 i = 0 → (T.lvl 0 v).1 i = 0 := by
    intro E n W T x v
    rw [← SetLike.mem_coe, (hB2 E n W T x).1, mem_preimage, SetLike.mem_coe, mem_ExB_iff]
  have hcone : ∀ {E : ScBanach} {n : ℕ} {W : ScBanach}
      (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {x v : E.lvl 0},
      v ∈ partialQuadrantAtWith T x ↔ ∀ i, (T.lvl 0 x).1 i = 0 → 0 ≤ (T.lvl 0 v).1 i := by
    intro E n W T x v
    rw [(hB2 E n W T x).2, mem_preimage, mem_CxB_iff]
  refine ⟨@hmem, ?_, ?_, ?_, ?_, @lvl1_approx, @smooth_approx, @ker_density, @pq_density⟩
  · -- `E_x` is closed
    intro E n W T x
    have : (minimalSubspaceWith T x : Set (E.lvl 0)) =
        ⋂ i : {i : Fin n // (T.lvl 0 x).1 i = 0}, {v : E.lvl 0 | (T.lvl 0 v).1 i.1 = 0} := by
      ext v
      simp only [SetLike.mem_coe, hmem, mem_iInter, mem_ofPred_eq, Subtype.forall]
    rw [this]
    exact isClosed_iInter fun i => isClosed_eq
      ((continuous_apply i.1).comp (continuous_fst.comp (T.lvl 0).continuous)) continuous_const
  · -- `dim(E/E_x) = d_C(x)`
    intro E n W T x
    set p := T.lvl 0 x with hp
    let p' : (EB n W).lvl 0 := (fun i => |p.1 i|, p.2)
    have hp' : p' ∈ quadrant n W 0 := fun i => abs_nonneg _
    have hEx : ExB p' = ExB p := by
      ext v
      rw [mem_ExB_iff, mem_ExB_iff]
      dsimp only [p']
      simp only [abs_eq_zero]
    have hmap : (minimalSubspaceWith T x).map ((T.lvl 0).toLinearEquiv : E.lvl 0 →ₗ[ℝ] _) =
        ExB p := by
      ext w
      simp only [Submodule.mem_map, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
      constructor
      · rintro ⟨v, hv, rfl⟩
        rw [mem_ExB_iff]
        exact (hmem T).1 hv
      · intro hw
        refine ⟨(T.lvl 0).symm w, (hmem T).2 fun i hi => ?_, by simp⟩
        rw [ContinuousLinearEquiv.apply_symm_apply]
        exact (mem_ExB_iff p w).1 hw i hi
    have e := Submodule.Quotient.equiv _ _ (T.lvl 0).toLinearEquiv hmap
    rw [e.finrank_eq, ← hEx]
    unfold Module.finrank
    rw [hB1 n W p' hp', Cardinal.toNat_natCast, degIndex_quadrant hp']
    change (Finset.univ.filter fun i => |p.1 i| = 0).card =
      (Finset.univ.filter fun i => p.1 i = 0).card
    simp only [abs_eq_zero]
  · -- `E_x ⊆ C_x`
    intro E n W T e v hv
    rw [hcone]
    intro i hi
    rw [(hmem T).1 hv i hi]
  · -- `C_x` is closed
    intro E n W T e
    have : partialQuadrantAtWith T e =
        ⋂ i : {i : Fin n // (T.lvl 0 e).1 i = 0}, {v : E.lvl 0 | 0 ≤ (T.lvl 0 v).1 i.1} := by
      ext v
      simp only [hcone, mem_iInter, mem_ofPred_eq, Subtype.forall]
    rw [this]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((continuous_apply i.1).comp (continuous_fst.comp (T.lvl 0).continuous))

#rt_check RoundTrip.V2_31.A_to_B [Polyfold.mem_minimalSubspaceWith, Polyfold.isClosed_minimalSubspaceWith, Polyfold.finrank_quotient_minimalSubspaceWith, Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith, Polyfold.isClosed_partialQuadrantAtWith, Polyfold.exists_tendsto_lvl1_degIndexWith, Polyfold.exists_tendsto_smooth_degIndexWith, Polyfold.ScBanach.subset_closure_ker_inter_range_toBase, Polyfold.partialQuadrantAtWith_subset_closure]
#rt_check RoundTrip.V2_31.B_to_A [Polyfold.mem_minimalSubspaceWith, Polyfold.isClosed_minimalSubspaceWith, Polyfold.finrank_quotient_minimalSubspaceWith, Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith, Polyfold.isClosed_partialQuadrantAtWith, Polyfold.exists_tendsto_lvl1_degIndexWith, Polyfold.exists_tendsto_smooth_degIndexWith, Polyfold.ScBanach.subset_closure_ker_inter_range_toBase, Polyfold.partialQuadrantAtWith_subset_closure]
#rt_overlap RoundTrip.V2_31.B_to_A [Polyfold.mem_minimalSubspaceWith, Polyfold.isClosed_minimalSubspaceWith, Polyfold.finrank_quotient_minimalSubspaceWith, Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith, Polyfold.isClosed_partialQuadrantAtWith, Polyfold.exists_tendsto_lvl1_degIndexWith, Polyfold.exists_tendsto_smooth_degIndexWith, Polyfold.ScBanach.subset_closure_ker_inter_range_toBase, Polyfold.partialQuadrantAtWith_subset_closure]

end RoundTrip.V2_31
