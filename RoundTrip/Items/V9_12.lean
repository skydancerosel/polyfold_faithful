import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_12

/-! Round trip for V9_12 (§9.2, p. 409, with Part I Remark 4.2.2: the tangent space `T_yM` of a
submanifold, set form and chart form).

`A` is the conjunction of the types of the ten listed theorems, universes at `0`:
`mem_submanifoldTangent_iff`, `submanifoldTangent_subset_tangentFiber`,
`submanifoldTangent_inter_isOpen`, `submanifoldTangent_image`, `chartTangent_eq`,
`exists_submodule_chartTangent`, `finrank_chartTangent`, `chartTangent_chart_change`,
`exists_linearEquiv_chartTangent`, `LocalBranchingStructure.exists_submodule_of_mem_support`
(`submanifoldTangent`, `chartTangent` are vocabulary).

The project's `T_yM` is the set of vectors over `y` **fixed** by `Tr` (`r` the sc⁺-retraction of
some data at `y`); `B`'s is the **image** `Tr(T_yX)`.

* `A → B`: the image of the idempotent `Tr` on `T_yX` is its fixed set (`tmap_tmap`, and `Tr`
  maps `T_yX` to `T_{r(y)}X = T_yX`), so with `mem_submanifoldTangent_iff` (any data computes
  the fixed set) `B (c)` holds, `(a)` follows, and `(b)` is `exists_submodule_chartTangent` (the
  chart image of `T_yM` is a finite-dimensional subspace in every chart).
* `B → A`: `exists_submodule_chartTangent` and `exists_submodule_of_mem_support` follow from
  `B (b), (c)`.  The other eight conjuncts are calculus facts about the project's `T_yM` and its
  chart images (data independence for an arbitrary single data, germs, images under
  sc-diffeomorphisms, the chart model `T_z(φ(W ∩ A))`, the rank, chart changes) that `B` does
  not state; they are re-proved outright from non-item project lemmas (the proofs follow the
  project's). -/

namespace RoundTrip.V9_12
open Polyfold Polyfold.MPolyfold Set Module

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.mem_submanifoldTangent_iff.{0}) ∧
  (type_of% @Polyfold.MPolyfold.submanifoldTangent_subset_tangentFiber.{0}) ∧
  (type_of% @Polyfold.MPolyfold.submanifoldTangent_inter_isOpen.{0}) ∧
  (type_of% @Polyfold.MPolyfold.submanifoldTangent_image.{0}) ∧
  (type_of% @Polyfold.MPolyfold.chartTangent_eq.{0}) ∧
  (type_of% @Polyfold.MPolyfold.exists_submodule_chartTangent.{0}) ∧
  (type_of% @Polyfold.MPolyfold.finrank_chartTangent.{0}) ∧
  (type_of% @Polyfold.MPolyfold.chartTangent_chart_change.{0}) ∧
  (type_of% @Polyfold.MPolyfold.exists_linearEquiv_chartTangent.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.exists_submodule_of_mem_support.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.mem_submanifoldTangent_iff.{0},
    @Polyfold.MPolyfold.submanifoldTangent_subset_tangentFiber.{0},
    @Polyfold.MPolyfold.submanifoldTangent_inter_isOpen.{0},
    @Polyfold.MPolyfold.submanifoldTangent_image.{0},
    @Polyfold.MPolyfold.chartTangent_eq.{0},
    @Polyfold.MPolyfold.exists_submodule_chartTangent.{0},
    @Polyfold.MPolyfold.finrank_chartTangent.{0},
    @Polyfold.MPolyfold.chartTangent_chart_change.{0},
    @Polyfold.MPolyfold.exists_linearEquiv_chartTangent.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.exists_submodule_of_mem_support.{0}⟩

section
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

/-- The image of `Tr` on `T_yX` is the fixed set of `Tr` over `y` (for `y ∈ M ∩ V`), given that
any data computes the fixed set (`hiff`, the content of `mem_submanifoldTangent_iff`). -/
theorem image_eq_of_iff {M : Set Z} (d : P.SubmanifoldData M) {y : Z} (hyM : y ∈ M)
    (hyV : y ∈ d.V)
    (hiff : ∀ {α : P.TangentSpace}, α ∈ P.submanifoldTangent M y ↔
      P.levelVal 1 (P.tangentProj α) = y ∧ d.tmap α = α) :
    P.submanifoldTangent M y = d.tmap '' TxXB P y := by
  ext α
  constructor
  · intro hα
    obtain ⟨h1, h2⟩ := hiff.1 hα
    exact ⟨α, h1, h2⟩
  · rintro ⟨β, hβ, rfl⟩
    have hβV : β ∈ P.tangentPreimage d.V := by
      change P.levelVal 1 (P.tangentProj β) ∈ d.V
      rw [show P.levelVal 1 (P.tangentProj β) = y from hβ]; exact hyV
    refine hiff.2 ⟨?_, d.tmap_tmap hβV⟩
    rw [d.levelVal_tangentProj_tmap hβV, show P.levelVal 1 (P.tangentProj β) = y from hβ,
      d.apply_eq_self ⟨hyM, hyV⟩]

end

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA Z _ _ _ P M hM y hyM
  have hc : ∀ d : P.SubmanifoldData M, y ∈ d.V →
      P.submanifoldTangent M y = d.tmap '' TxXB P y := fun d hyV =>
    image_eq_of_iff d hyM hyV (hA.1 d hyV)
  refine ⟨fun d d' hd hd' => (hc d hd).symm.trans (hc d' hd'), fun d hd => ⟨?_, ?_⟩, hc⟩
  · rw [← hc d hd]; exact fun α hα => hα.1
  · intro φ hφ hyφ
    obtain ⟨N, hN, hfin⟩ := hA.2.2.2.2.2.1 hφ hM hyM hyφ
    refine ⟨N, hfin, ?_⟩
    rw [← hc d hd]
    exact hN.symm

/-! ### `B → A`: the outright re-proofs -/

section Reproofs
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

theorem mem_iff' {A : Set X} (d : P.SubmanifoldData A) {y : X} (hy : y ∈ d.V)
    {α : P.TangentSpace} :
    α ∈ P.submanifoldTangent A y ↔ P.levelVal 1 (P.tangentProj α) = y ∧ d.tmap α = α := by
  constructor
  · rintro ⟨hα, d', hy', hfix⟩
    have hαd : α ∈ P.tangentPreimage d.V := by change _ ∈ d.V; rw [hα]; exact hy
    have hαd' : α ∈ P.tangentPreimage d'.V := by change _ ∈ d'.V; rw [hα]; exact hy'
    exact ⟨hα, d'.tmap_eq_of_tmap_eq d hαd' hαd hfix⟩
  · rintro ⟨hα, hfix⟩
    exact ⟨hα, d, hy, hfix⟩

theorem subset_tangentFiber' {A : Set X} {y : X} (hy : y ∈ P.levelSet 1) :
    P.submanifoldTangent A y ⊆ P.tangentFiber (P.levelMk 1 y hy) := fun _ hα =>
  level_ext (by rw [hα.1, levelVal_levelMk])

theorem inter_isOpen' {A V : Set X} (hV : IsOpen V) {y : X} (hyV : y ∈ V) :
    P.submanifoldTangent (A ∩ V) y = P.submanifoldTangent A y :=
  submanifoldTangent_congr hV hyV (by rw [inter_assoc, inter_self])

theorem image' {f g : X → X} {U U' : Set X} (hf : P.IsScDiffeoOn P f g U U')
    {A : Set X} (hA : P.IsSmoothSubmanifold A) (hAU : A ⊆ U) {a : X} (ha : a ∈ A) :
    P.submanifoldTangent (f '' A) (f a) =
      tangentMapOn hf.isScSmoothOn '' P.submanifoldTangent A a := by
  have hfA := hA.image_of_isScDiffeoOn hf hAU
  refine Subset.antisymm (fun β hβ => ?_) (image_submanifoldTangent_subset hf hfA hAU ha)
  have hfAU' : f '' A ⊆ U' := image_subset_iff.2 fun y hy => hf.mapsTo (hAU hy)
  have hgf : g '' (f '' A) = A := by
    rw [image_image]
    exact (image_congr fun y hy => hf.left_inv y (hAU hy)).trans (image_id' A)
  have hga : g (f a) = a := hf.left_inv a (hAU ha)
  have h := image_submanifoldTangent_subset hf.symm (hgf.symm ▸ hA) hfAU' ⟨a, ha, rfl⟩
  rw [hgf, hga] at h
  have hβU' : β ∈ P.tangentPreimage U' := by
    change _ ∈ U'; rw [hβ.1]; exact hf.mapsTo (hAU ha)
  exact ⟨_, h ⟨β, hβ, rfl⟩, hf.tangentMapOn_tangentMapOn_inv hβU'⟩

variable {φ : MChart X} (hφ : P.IsChart φ)

theorem chartTangent_eq' {A : Set X} (d : P.SubmanifoldData A) {y : X} (hyA : y ∈ A)
    (hyV : y ∈ d.V) (hyφ : y ∈ φ.source) :
    P.chartTangent hφ A y =
      tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) (levelLift φ 1 y) := by
  have hy1 : y ∈ P.levelSet 1 := d.mem_levelSet_one hyA hyV
  have hz : φ.model.E.toBase 1 (levelLift φ 1 y) = φ y := P.toBase_levelLift hφ hyφ hy1
  obtain ⟨-, h2, -, -⟩ := d.remark_4_14 hφ hyA hyV hyφ hz
  have hyW : y ∈ d.toSubData.shrink φ := d.toSubData.mem_shrink φ hyA hyV hyφ
  rw [← h2]
  ext h
  constructor
  · rintro ⟨α, hα, rfl⟩
    have hαy : P.levelVal 1 (P.tangentProj α) = y := hα.1
    have hfix : d.tmap α = α := ((mem_iff' d hyV).1 hα).2
    have hαW : α ∈ P.tangentPreimage (d.toSubData.shrink φ) :=
      mem_tangentPreimage.2 (hαy ▸ hyW)
    have hαφ : α ∈ tangentChartSet φ := d.toSubData.shrink_subset_source φ hαW
    have hfst : (tangentChartMap hφ α).1 = levelLift φ 1 y := by
      rw [tangentChartMap_fst hφ hαφ, hαy]
    have hpair : ((levelLift φ 1 y, (tangentChartMap hφ α).2) : φ.model.E.tangent 0) =
        tangentChartMap hφ α := Prod.ext hfst.symm rfl
    refine ⟨(tangentChartMap hφ α).2, ?_, ?_⟩
    · simp only [tangentSpace, mem_ofPred_eq]
      rw [hpair]
      exact tangentChartMap_mem hφ hαφ
    · have := d.tangentChartMap_tmap hφ hαW
      rw [hfix] at this
      dsimp only
      rw [hpair, ← this]
  · rintro ⟨h', hh', rfl⟩
    have hmem : ((levelLift φ 1 y, h') : φ.model.E.tangent 0) ∈
        retractTangent φ.model.E φ.model.C φ.model.O := hh'
    set β := TangentSpace.mk (TangentPre.ofVec hφ hmem) with hβdef
    have hβ : tangentChartMap hφ β = (levelLift φ 1 y, h') := tangentChartMap_mk_ofVec hφ hmem
    have hβy : P.levelVal 1 (P.tangentProj β) = y := by
      rw [hβdef, tangentProj_mk, TangentPre.ofVec_x]
      change φ.symm (φ.model.E.toBase 1 (levelLift φ 1 y)) = y
      rw [hz, φ.symm_apply_apply hyφ]
    have hβW : β ∈ P.tangentPreimage (d.toSubData.shrink φ) :=
      mem_tangentPreimage.2 (hβy ▸ hyW)
    have hβV : β ∈ P.tangentPreimage d.V := d.toSubData.shrink_subset_V φ hβW
    refine ⟨d.tmap β, ?_, ?_⟩
    · have := d.tmap_mem_submanifoldTangent hβV
      rwa [hβy, d.apply_eq_self ⟨hyA, hyV⟩] at this
    · dsimp only
      rw [d.tangentChartMap_tmap hφ hβW, hβ]

theorem finrank_chartTangent' {A : Set X} {y : X} {n : ℕ} (h : P.HasDimAt A y n)
    (hA : P.IsSmoothSubmanifold A) (hyφ : y ∈ φ.source) {N : Submodule ℝ (φ.model.E 0)}
    (hN : (N : Set (φ.model.E 0)) = P.chartTangent hφ A y) : finrank ℝ N = n := by
  have hyA : y ∈ A := h.1
  set d := hA.data hyA
  have hyV := hA.mem_data_V hyA
  have hy1 : y ∈ P.levelSet 1 := d.mem_levelSet_one hyA hyV
  have hz : φ.model.E.toBase 1 (levelLift φ 1 y) = φ y := P.toBase_levelLift hφ hyφ hy1
  have h1 := h.finrank_eq d hφ hyV hyφ hz
  rw [← chartTangent_eq' hφ d hyA hyV hyφ, ← hN, Submodule.span_eq] at h1
  exact h1

theorem chart_change' {ψ : MChart X} (hψ : P.IsChart ψ) (A : Set X) {y : X}
    (hyφ : y ∈ φ.source) (hyψ : y ∈ ψ.source) :
    ∃ L : φ.model.E 0 →L[ℝ] ψ.model.E 0,
      P.chartTangent hψ A y = L '' P.chartTangent hφ A y ∧ InjOn L (P.chartTangent hφ A y) := by
  obtain ⟨L, hL⟩ := exists_clm_tangentChartMap_snd hφ hψ hyφ hyψ
  refine ⟨L, ?_, ?_⟩
  · rw [chartTangent, chartTangent, image_image]
    exact image_congr fun α hα => hL α hα.1
  · rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ h
    have h' : (tangentChartMap hψ α).2 = (tangentChartMap hψ β).2 := by
      rw [hL α hα.1, hL β hβ.1]; exact h
    rw [injOn_tangentChartMap_snd hψ hyψ (submanifoldTangent_subset_fiber A y hα)
      (submanifoldTangent_subset_fiber A y hβ) h']

theorem linearEquiv' {ψ : MChart X} (hψ : P.IsChart ψ) (A : Set X) {y : X}
    (hyφ : y ∈ φ.source) (hyψ : y ∈ ψ.source) {N : Submodule ℝ (φ.model.E 0)}
    {N' : Submodule ℝ (ψ.model.E 0)} (hN : (N : Set (φ.model.E 0)) = P.chartTangent hφ A y)
    (hN' : (N' : Set (ψ.model.E 0)) = P.chartTangent hψ A y) :
    ∃ (L : φ.model.E 0 →L[ℝ] ψ.model.E 0) (e : N ≃ₗ[ℝ] N'), ∀ v : N, (e v : ψ.model.E 0) = L v := by
  obtain ⟨L, himg, hinj⟩ := chart_change' hφ hψ A hyφ hyψ
  have hmaps : ∀ v ∈ N, (L : φ.model.E 0 →ₗ[ℝ] ψ.model.E 0) v ∈ N' := fun v hv => by
    rw [← SetLike.mem_coe, hN', himg]
    exact mem_image_of_mem L (by rw [← hN]; exact hv)
  let f : N →ₗ[ℝ] N' := (L : φ.model.E 0 →ₗ[ℝ] ψ.model.E 0).restrict hmaps
  have hbij : Function.Bijective f := by
    refine ⟨fun v w hvw => ?_, fun w => ?_⟩
    · have h1 : L v = L w := congrArg Subtype.val hvw
      have hv : (v : φ.model.E 0) ∈ P.chartTangent hφ A y := by rw [← hN]; exact v.2
      have hw : (w : φ.model.E 0) ∈ P.chartTangent hφ A y := by rw [← hN]; exact w.2
      exact Subtype.ext (hinj hv hw h1)
    · have hw : (w : ψ.model.E 0) ∈ L '' P.chartTangent hφ A y := by rw [← himg, ← hN']; exact w.2
      obtain ⟨v, hv, hvw⟩ := hw
      rw [← hN] at hv
      exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  exact ⟨L, LinearEquiv.ofBijective f hbij, fun v => rfl⟩

end Reproofs

/-- `exists_submodule_chartTangent` from `B (b), (c)`. -/
theorem exists_submodule_of_B (hB : B) {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {P : MPolyfold X} {φ : MChart X} (hφ : P.IsChart φ) {A : Set X}
    (hA : P.IsSmoothSubmanifold A) {y : X} (hyA : y ∈ A) (hyφ : y ∈ φ.source) :
    ∃ N : Submodule ℝ (φ.model.E 0), (N : Set (φ.model.E 0)) = P.chartTangent hφ A y ∧
      FiniteDimensional ℝ N := by
  obtain ⟨-, hb, hc⟩ := hB X P A hA y hyA
  have hyV := hA.mem_data_V hyA
  obtain ⟨S, hfin, hS⟩ := (hb _ hyV).2 φ hφ hyφ
  refine ⟨S, ?_, hfin⟩
  rw [← hS, chartImgB, ← hc _ hyV]
  rfl

theorem B_to_A : B → A := by
  intro hB
  refine ⟨@mem_iff', @subset_tangentFiber', @inter_isOpen', @image', @chartTangent_eq',
    fun hφ _ hA _ hyA hyφ => exists_submodule_of_B hB hφ hA hyA hyφ,
    @finrank_chartTangent', @chart_change', @linearEquiv', ?_⟩
  -- `exists_submodule_of_mem_support`
  intro Obj Mor _ _ _ _ _ _ X Θ x Bs L hL φ hφ hxφ
  classical
  have : ∃ i, X.PObj.submanifoldTangent (Bs.M i) x = L := by
    by_contra h
    push Not at h
    exact (Finsupp.mem_support_iff.1 hL)
      (by rw [Bs.tangentSum_apply]; exact Finset.sum_eq_zero fun i _ => if_neg (h i))
  obtain ⟨i, rfl⟩ := this
  obtain ⟨N, hN, hfin⟩ :=
    exists_submodule_of_B hB hφ (Bs.isSmoothSubmanifold i) (Bs.mem_M i) hxφ
  exact ⟨N, hfin, hN, (injOn_tangentChartMap_snd hφ hxφ).mono
    (submanifoldTangent_subset_fiber _ _)⟩

#rt_check RoundTrip.V9_12.A_to_B [Polyfold.MPolyfold.mem_submanifoldTangent_iff,
  Polyfold.MPolyfold.submanifoldTangent_subset_tangentFiber,
  Polyfold.MPolyfold.submanifoldTangent_inter_isOpen, Polyfold.MPolyfold.submanifoldTangent_image,
  Polyfold.MPolyfold.chartTangent_eq, Polyfold.MPolyfold.exists_submodule_chartTangent,
  Polyfold.MPolyfold.finrank_chartTangent, Polyfold.MPolyfold.chartTangent_chart_change,
  Polyfold.MPolyfold.exists_linearEquiv_chartTangent,
  Polyfold.EpGroupoid.LocalBranchingStructure.exists_submodule_of_mem_support]
#rt_check RoundTrip.V9_12.B_to_A [Polyfold.MPolyfold.mem_submanifoldTangent_iff,
  Polyfold.MPolyfold.submanifoldTangent_subset_tangentFiber,
  Polyfold.MPolyfold.submanifoldTangent_inter_isOpen, Polyfold.MPolyfold.submanifoldTangent_image,
  Polyfold.MPolyfold.chartTangent_eq, Polyfold.MPolyfold.exists_submodule_chartTangent,
  Polyfold.MPolyfold.finrank_chartTangent, Polyfold.MPolyfold.chartTangent_chart_change,
  Polyfold.MPolyfold.exists_linearEquiv_chartTangent,
  Polyfold.EpGroupoid.LocalBranchingStructure.exists_submodule_of_mem_support]
#rt_overlap RoundTrip.V9_12.B_to_A [Polyfold.MPolyfold.mem_submanifoldTangent_iff,
  Polyfold.MPolyfold.submanifoldTangent_subset_tangentFiber,
  Polyfold.MPolyfold.submanifoldTangent_inter_isOpen, Polyfold.MPolyfold.submanifoldTangent_image,
  Polyfold.MPolyfold.chartTangent_eq, Polyfold.MPolyfold.exists_submodule_chartTangent,
  Polyfold.MPolyfold.finrank_chartTangent, Polyfold.MPolyfold.chartTangent_chart_change,
  Polyfold.MPolyfold.exists_linearEquiv_chartTangent,
  Polyfold.EpGroupoid.LocalBranchingStructure.exists_submodule_of_mem_support]

end RoundTrip.V9_12
