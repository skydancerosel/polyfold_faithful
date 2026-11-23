import Polyfold.Chapter11.EffectiveMeasureEquivalence
import Polyfold.Chapter9.StokesLocalFormsCompare
import Polyfold.Chapter9.TameOpen

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4 "Equivalences and Integration", **Theorems 11.4.1, 11.4.2**
(pp. 543–544), in the form used in Part III, §15.4 and Chapter 16 for the restriction of an
ep-groupoid to a saturated open set.  Numbers and pages are the 2021 text's.

# The branched integrals along a full and faithful local sc-diffeomorphism

The proof of Theorem 11.4.1 is local on the support: it moves an oriented tame branching
structure by the sc-diffeomorphism `Q = ψ̂ ∘ Φ` of a chart and compares (11.12) with (11.13).
Here the functor `Φ : X → Y` is a local sc-diffeomorphism on objects, full, and bijective on the
isotropy groups; it need not be essentially surjective.  What is asked instead is that the
orbit set `|supp Θ'|` of the branched ep⁺-subgroupoid of `Y` lies in the image of `|Φ|`.

* `TransportChart.bijective_conj_of`, `exists_naturalRep_push_of`, `exists_rep_push_of`,
  `card_effIsotropy_eq_of`, `evCompatOn_Q_of`: the statements of Chapters 10 and 11 along a
  transport chart, for such a functor.
* `isLUC_of_isLocalScDiffeo`: the local unique continuation property (Definition 7.2.18) of `Y`
  passes to `X`.
* `isCompactBranched_pullbackTheta_of`, `isBranchedEpSubgroupoid_pullbackTheta_of`,
  `isOrientation_pullSection_of`, `hloc_pullSection_of`: `Φ^*Θ̂' = (Φ^*Θ', Φ^*T̂')` is a compact
  oriented branched ep⁺-subgroupoid described by oriented tame structures.
* **`integral_pull_of`**, **`integralEff_pull_of`**: `∫_{Φ^*Θ̂'} Φ^*ω' = ∫_{Θ̂'} ω'` and the
  same for the effective integrals.
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace EpFunctor

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Φ : EpFunctor X Y} {n : ℕ}
  {Ω Ω' : Type*} [AddCommGroup Ω] [Module ℝ Ω] [AddCommGroup Ω'] [Module ℝ Ω']
  {FX : X.FormEval n Ω} {FY : Y.FormEval n Ω'} {P : Ω' →ₗ[ℝ] Ω}
  {Θ' : Obj' → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ} {T' : Obj' → Y.PObj.OrTangent →₀ ℚ}

open OrientedTameStructure

/-! ### Transport charts -/

namespace TransportChart

variable {x : Obj} {y : Obj'} (Tc : Φ.TransportChart x y)

/-- `g ↦ ψ ∘ Φ(g) ∘ ψ⁻¹` is a bijection `G_x → G_y` if `Φ` is bijective on the isotropy
groups. -/
theorem bijective_conj_of (hiso : ∀ x, Bijective (Φ.isotropyHom x)) : Bijective Tc.conj :=
  (Y.isotropyConj Tc.ψ₀ Tc.src_ψ₀ Tc.tgt_ψ₀).bijective.comp (hiso x)

/-- **The push-forward of a natural representation** (2021 p. 467), as
`TransportChart.exists_naturalRep_push`. -/
theorem exists_naturalRep_push_of (hiso : ∀ x, Bijective (Φ.isotropyHom x))
    (R : X.NaturalRep x) (R'₀ : Y.NaturalRep y) (hR : R.U ⊆ Tc.W ∩ Tc.Q ⁻¹' R'₀.U) :
    ∃ R' : Y.NaturalRep y, R'.U = Tc.Q '' R.U ∧ R'.Φ = R'₀.Φ ∧ R'.Γ = R'₀.Γ ∧
      ∀ g, ∀ u ∈ R.U, Tc.Q (R.Φ g u) = R'.Φ (Tc.conj g) (Tc.Q u) := by
  have hRW : R.U ⊆ Tc.W := fun u hu => (hR hu).1
  have hd := Tc.isScDiffeoOn_image R.isOpen_U hRW
  have heq := Tc.Q_Φ_of_subset R R'₀ hR
  obtain ⟨R', h1, h2, h3⟩ := Y.exists_naturalRep_restrict R'₀ hd.isOpen_target
    (R.isConnected_U.image _ (Tc.continuousOn_Q.mono hRW)) ⟨x, R.mem_U, Tc.Q_self⟩
    (image_subset_iff.2 fun u hu => (hR hu).2) fun k => by
      obtain ⟨g, rfl⟩ := (Tc.bijective_conj_of hiso).2 k
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨R.Φ g u, R.mapsTo_Φ g hu, heq g u hu⟩
  exact ⟨R', h1, h2, h3, fun g u hu => by rw [h2]; exact heq g u hu⟩

/-- Natural representations on `U(x) ⊆ U₀(x) ∩ W ∩ Q⁻¹(V')` and on `Q(U(x))`, as
`TransportChart.exists_rep_push`. -/
theorem exists_rep_push_of (hiso : ∀ x, Bijective (Φ.isotropyHom x)) (R₀ : X.NaturalRep x)
    {V' : Set Obj'} (hV' : IsOpen V') (hyV' : y ∈ V') :
    ∃ (R : X.NaturalRep x) (R' : Y.NaturalRep y), R.U ⊆ R₀.U ∧ R.U ⊆ Tc.W ∧
      Tc.Q '' R.U ⊆ V' ∧ R'.U = Tc.Q '' R.U := by
  obtain ⟨R'₀, -⟩ := Y.theorem_7_1_13 y isOpen_univ (mem_univ y)
  have hO : IsOpen (Tc.W ∩ Tc.Q ⁻¹' (R'₀.U ∩ V')) :=
    Tc.continuousOn_Q.isOpen_inter_preimage Tc.isOpen_W (R'₀.isOpen_U.inter hV')
  have hxO : x ∈ Tc.W ∩ Tc.Q ⁻¹' (R'₀.U ∩ V') :=
    ⟨Tc.mem_W, by rw [mem_preimage, Tc.Q_self]; exact ⟨R'₀.mem_U, hyV'⟩⟩
  obtain ⟨R, hRsub, -, -⟩ := exists_naturalRep_shrink X R₀ hO hxO
  have hR : R.U ⊆ Tc.W ∩ Tc.Q ⁻¹' R'₀.U := fun u hu => ⟨(hRsub hu).1.1, (hRsub hu).1.2.1⟩
  obtain ⟨R', hR'U, -⟩ := Tc.exists_naturalRep_push_of hiso R R'₀ hR
  exact ⟨R, R', fun u hu => (hRsub hu).2, fun u hu => (hRsub hu).1.1,
    image_subset_iff.2 fun u hu => (hRsub hu).1.2.2, hR'U⟩

/-- `♯G_x^eff = ♯G_y^eff` along a transport chart, as `TransportChart.card_effIsotropy_eq`. -/
theorem card_effIsotropy_eq_of (hiso : ∀ x, Bijective (Φ.isotropyHom x)) (R : X.NaturalRep x)
    (R' : Y.NaturalRep y) (hRW : R.U ⊆ Tc.W) (hR' : R'.U = Tc.Q '' R.U) (hL : R.HasLUC)
    (hL' : R'.HasLUC) : Nat.card (X.EffIsotropy x) = Nat.card (Y.EffIsotropy y) := by
  have hR : R.U ⊆ Tc.W ∩ Tc.Q ⁻¹' R'.U := fun u hu =>
    ⟨hRW hu, by rw [mem_preimage, hR']; exact mem_image_of_mem _ hu⟩
  set e := MulEquiv.ofBijective Tc.conj (Tc.bijective_conj_of hiso)
  have hmap : (X.trivialSubgroup x).map e.toMonoidHom = Y.trivialSubgroup y := by
    rw [← R.kerΦ_eq_trivialSubgroup hL, ← R'.kerΦ_eq_trivialSubgroup hL']
    ext k
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine R'.mem_kerΦ.2 fun z hz => ?_
      rw [hR'] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      change R'.Φ (Tc.conj g) (Tc.Q u) = Tc.Q u
      rw [← Tc.Q_Φ_of_subset R R' hR g u hu, R.mem_kerΦ.1 hg u hu]
    · intro hk
      obtain ⟨g, rfl⟩ := (Tc.bijective_conj_of hiso).2 k
      refine ⟨g, R.mem_kerΦ.2 fun u hu => ?_, rfl⟩
      have h1 := Tc.Q_Φ_of_subset R R' hR g u hu
      rw [R'.mem_kerΦ.1 hk _ (by rw [hR']; exact mem_image_of_mem _ hu)] at h1
      have h2 := congrArg Tc.Qinv h1
      rwa [Tc.isScDiffeoOn_Q.left_inv _ (hRW (R.mapsTo_Φ g hu)),
        Tc.isScDiffeoOn_Q.left_inv _ (hRW hu)] at h2
  rw [Nat.card_congr (X.effIsotropyEquiv x).toEquiv, Nat.card_congr (Y.effIsotropyEquiv y).toEquiv]
  exact Nat.card_congr (QuotientGroup.congr _ _ e hmap).toEquiv

/-- **`ω'(TQ β) = (Φ^*ω')(β)`** on the tangent spaces of a submanifold `N ⊆ W`, as
`TransportChart.evCompatOn_Q`, for a map `P` of the forms with `(Pω')(α) = ω'(TΦ ∘ α)`. -/
theorem evCompatOn_Q_of
    (hev : ∀ (ω' : Ω') {N : Set Obj}, X.PObj.IsSmoothSubmanifold N → ∀ {y : Obj}, y ∈ N →
      ∀ α : Fin n → X.PObj.TangentSpace, (∀ i, α i ∈ X.PObj.submanifoldTangent N y) →
      FX.ev (P ω') α = FY.ev ω' (fun i => Φ.tangent.obj (α i)))
    (ω' : Ω') {N : Set Obj} (hN : X.PObj.IsSmoothSubmanifold N) (hNW : N ⊆ Tc.W) :
    FormEval.EvCompatOn FX FY Tc.isScDiffeoOn_Q N (P ω') ω' := by
  intro z hz β hβ
  have hb : ∀ i, X.PObj.levelVal 1 (X.PObj.tangentProj (β i)) = z := fun i => (hβ i).1
  have hQN : Y.PObj.IsSmoothSubmanifold (Tc.Q '' N) :=
    hN.image_of_isScDiffeoOn Tc.isScDiffeoOn_Q hNW
  have hmem : ∀ i, tangentMapOn Tc.isScDiffeoOn_Q.isScSmoothOn (β i) ∈
      Y.PObj.submanifoldTangent (Tc.Q '' N) (Tc.Q z) := fun i => by
    rw [submanifoldTangent_image_of_isScDiffeoOn Tc.isScDiffeoOn_Q hN hNW hz]
    exact mem_image_of_mem _ (hβ i)
  have hψ1 : Tc.ψ z ∈ Y.PMor.levelSet 1 := Y.mem_levelSet_one_of_tgt_mem_smoothSet (by
    rw [Tc.tgt_ψ z (hNW hz)]; exact (hQN.subset_smoothSet) (mem_image_of_mem _ hz))
  have hsrc : Y.src (Y.inv (Tc.ψ z)) = Tc.Q z := by rw [Y.src_inv, Tc.tgt_ψ z (hNW hz)]
  rw [← FY.ev_mor ω' hQN (mem_image_of_mem _ hz) (Y.inv (Tc.ψ z)) hsrc _ hmem,
    hev ω' hN hz β hβ]
  congr 1
  funext i
  have h := Tc.tangentMor_ψ_tangent_obj (α := β i) (show _ ∈ Tc.W by rw [hb i]; exact hNW hz)
  rw [hb i] at h
  rw [← h]
  exact Y.tangentMor_inv_tangentMor hψ1 (by rw [levelVal_tangentProj_tangent_obj, hb i,
    Tc.src_ψ z (hNW hz)])

end TransportChart

/-- The chart `Q` along the unit `1_{Φ(x)}`. -/
theorem nonempty_transportChart_unit (hd : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj) (x : Obj) :
    Nonempty (Φ.TransportChart x (Φ.obj x)) := by
  obtain ⟨Tc, -⟩ := exists_transportChart hd (Y.src_unit (Φ.obj x)) (Y.tgt_unit (Φ.obj x))
  exact ⟨Tc⟩

/-! ### The local unique continuation property -/

/-- **The local unique continuation property (2021 Definition 7.2.18) passes from `Y` to `X`**
along a functor which is a local sc-diffeomorphism on objects: `𝐗^T` is the part of
`Φ⁻¹(𝐘^T)` over the diagonal (Proposition 7.2.21). -/
theorem isLUC_of_isLocalScDiffeo (hd : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj) (hY : Y.IsLUC) :
    X.IsLUC := by
  rw [X.proposition_7_2_21, Φ.nonEffectivePart_eq hd]
  exact ((Y.proposition_7_2_21.1 hY).preimage Φ.continuous_mor).inter
    (isClosed_eq X.continuous_src X.continuous_tgt)

/-! ### `Φ^*Θ̂'` -/

/-- `|Φ|` is an open embedding for a full functor which is a local sc-diffeomorphism on
objects. -/
theorem isOpenEmbedding_orbitMap_of (hd : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj)
    (hfull : Φ.toFunctor.Full) : Topology.IsOpenEmbedding Φ.orbitMap :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap Φ.continuous_orbitMap
    (Φ.injective_orbitMap_of_full hfull) (Φ.isOpenMap_orbitMap hd.isOpenMap)

/-- **`Φ^*Θ'` is compact** if `Θ'` is and `|supp Θ'|` lies in the image of `|Φ|`. -/
theorem isCompactBranched_pullbackTheta_of (hd : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj)
    (hfull : Φ.toFunctor.Full) (hΘ' : Y.IsFunctorial Θ') (hc : Y.IsCompactBranched Θ')
    (hrange : Y.orbitSupp Θ' ⊆ range Φ.orbitMap) :
    X.IsCompactBranched (Φ.pullbackTheta Θ') := by
  unfold EpGroupoid.IsCompactBranched
  rw [Φ.orbitSupp_pullbackTheta hΘ']
  refine (isOpenEmbedding_orbitMap_of hd hfull).isEmbedding.isCompact_iff.2 ?_
  rw [image_preimage_eq_of_subset hrange]
  exact hc

/-- **`Φ^*Θ'` is a branched ep⁺-subgroupoid** (Theorem 11.3.3 (2)), for a compact `Θ'` with
`|supp Θ'|` in the image of `|Φ|`. -/
theorem isBranchedEpSubgroupoid_pullbackTheta_of (hd : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj)
    (hfull : Φ.toFunctor.Full) (hΘ' : Y.IsBranchedEpSubgroupoid Θ')
    (hc : Y.IsCompactBranched Θ') (hrange : Y.orbitSupp Θ' ⊆ range Φ.orbitMap) :
    X.IsBranchedEpSubgroupoid (Φ.pullbackTheta Θ') where
  nonneg _ := hΘ'.nonneg _
  isFunctorial := Φ.isFunctorial_pullbackTheta hΘ'.isFunctorial
  support_subset x hx := (hd.mem_smoothSet_iff x).1 (hΘ'.support_subset hx)
  paracompactSpace_orbitSupp := by
    have : CompactSpace (X.orbitSupp (Φ.pullbackTheta Θ')) := isCompact_iff_compactSpace.1
      (isCompactBranched_pullbackTheta_of hd hfull hΘ'.isFunctorial hc hrange)
    infer_instance
  localBranching x hx := by
    obtain ⟨B'⟩ := hΘ'.localBranching _ hx
    obtain ⟨U, V, g, hxU, hdF⟩ := hd x
    exact ⟨B'.mapDiffeo hdF.symm (hdF.mapsTo hxU) (hdF.left_inv x hxU) fun z hz => by
      simp only [pullbackTheta_apply, hdF.right_inv z hz]⟩

/-- **`Φ^*T̂'` is an orientation of `Φ^*Θ'`** (Theorem 11.3.5, 2021 p. 540), as
`isOrientation_pullSection`. -/
theorem isOrientation_pullSection_of (hd : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj)
    (hT' : Y.IsOrientation Θ' T') :
    X.IsOrientation (Φ.pullbackTheta Θ') (Φ.pullSection T') := by
  have hS := isGrHatSection_pullSection hd hT'.isGrHatSection
  refine IsOrientation.mk' (X.hasIndependentTangentSums _) hS.mem hS.natural
    (fun x hx hxs => ?_) fun x hx => ?_
  · rw [pullSection_of_mem hx, hT'.eq_zero_of_not_mem ((hd.mem_smoothSet_iff x).2 hx)
      fun h => hxs (show 0 < Φ.pullbackTheta Θ' x by rw [pullbackTheta_apply]; exact h),
      Finsupp.mapDomain_zero]
  · have hFx : Φ.obj x ∈ supp Θ' := by
      have h : 0 < Φ.pullbackTheta Θ' x := hx
      rwa [pullbackTheta_apply] at h
    obtain ⟨B', hB'⟩ := hT'.locallyOriented _ hFx
    obtain ⟨U, V, g, hxU, hdF⟩ := hd x
    have hΘ : ∀ v ∈ V, Φ.pullbackTheta Θ' (g v) = Θ' v := fun v hv => by
      simp only [pullbackTheta_apply, hdF.right_inv v hv]
    refine ⟨B'.mapDiffeo hdF.symm (hdF.mapsTo hxU) (hdF.left_inv x hxU) hΘ, fun z hz hzs => ?_⟩
    rw [B'.orientedSum_mapDiffeo hdF.symm (hdF.mapsTo hxU) (hdF.left_inv x hxU) hΘ hz]
    obtain ⟨hzU, hFzU', -⟩ := hz
    have hFzs : Φ.obj z ∈ Y.PObj.smoothSet := (hd.mem_smoothSet_iff z).2 hzs
    rw [pullSection_of_mem hzs, hB' (Φ.obj z) hFzU' hFzs]
    exact mapDomain_map_congr (B'.orientedSum_mem _) fun β hβ =>
      fibreInv_eq_tangentMapOn hd hdF hzU hβ

/-- **`Φ^*Θ̂'` is described by oriented tame structures**: a structure of `Θ̂'` at `Φ(x)`,
restricted and moved back by the chart `Q`, describes `Φ^*T̂'` at `x`. -/
theorem hloc_pullSection_of (hd : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj)
    (hiso : ∀ x, Bijective (Φ.isotropyHom x)) (hΘ' : Y.IsFunctorial Θ')
    (hT' : Y.IsGrHatSection T')
    (hloc' : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y, D.Represents T') :
    ∀ x ∈ supp (Φ.pullbackTheta Θ'), ∃ C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x,
      C.Represents (Φ.pullSection T') := fun x hx => by
  obtain ⟨Tc⟩ := nonempty_transportChart_unit hd x
  obtain ⟨D, hDT⟩ := hloc' (Φ.obj x) hx
  obtain ⟨V, hxV, hVP⟩ := X.exists_hasPropernessProperty x
  obtain ⟨R₀, hR₀⟩ := X.theorem_7_1_13 x hVP.1 hxV
  obtain ⟨R, R', hRR₀, hRW, hRD, hR'⟩ := Tc.exists_rep_push_of hiso R₀ D.isOpen_U D.mem_U
  have h1 : R'.U ⊆ D.U := hR' ▸ hRD
  have h4 : X.HasPropernessProperty R.U := hVP.mono R.isOpen_U (hRR₀.trans hR₀)
  have hS := isGrHatSection_pullSection hd hT'
  refine ⟨pullStructure Tc (Tc.pullbackTheta_Q hΘ') D R R' h1 hRW hR' h4, ?_⟩
  refine (D.restrictRep R' h1).represents_move _ _ _ _ _ _ _
    (D.represents_restrictRep R' h1 hDT) ?_
  rintro _ ⟨z, hz, rfl⟩ hus
  have hzW' := restrictRep_U_subset_W' Tc D R R' h1 hRW hR' hz
  have hgz := Tc.isScDiffeoOn_Q.mapsTo_inv hzW'
  have hzs : z ∈ Y.PObj.smoothSet := by
    have h := (Tc.mem_smoothSet_iff hd hgz).2 hus
    rwa [Tc.isScDiffeoOn_Q.right_inv z hzW'] at h
  refine ⟨?_, ?_⟩
  · rw [Tc.isScDiffeoOn_Q.right_inv z hzW']; exact hzs
  · rw [Tc.isScDiffeoOn_Q.right_inv z hzW']
    exact rel_symm Tc.isScDiffeoOn_Q hS (Tc.pullSection_Q hd hT') hzW' hus

/-! ### The local comparison -/

section Local

variable (hd : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj) (hfull : Φ.toFunctor.Full)
  (hiso : ∀ x, Bijective (Φ.isotropyHom x))
  (hev : ∀ (ω' : Ω') {N : Set Obj}, X.PObj.IsSmoothSubmanifold N → ∀ {y : Obj}, y ∈ N →
    ∀ α : Fin n → X.PObj.TangentSpace, (∀ i, α i ∈ X.PObj.submanifoldTangent N y) →
    FX.ev (P ω') α = FY.ev ω' (fun i => Φ.tangent.obj (α i)))

include hd hfull hiso hev in
/-- **The local data of the comparison (11.12) = (11.13)** at a point `x` of `supp Φ^*Θ'`: a
structure `C` of `Φ^*Θ̂'` at `x` with sheets in the class, restricted to `C₁` and moved by the
chart `Q` to a structure `D` of `Θ̂'` at `Φ(x)` with sheets in the class, such that for every
Borel set `K ⊆ |D.U|` of `|supp Θ'|` the sums of (9.20) of `Pω'` over `C₁` and of `ω'` over `D`
agree, with the same orders of the (effective) isotropy groups. -/
theorem exists_local_comparison (hn : 0 < n) (hΘ' : Y.IsFunctorial Θ')
    (hT' : Y.IsGrHatSection T') (hTX : X.IsGrHatSection T)
    (hTT : Φ.IsTransported T T')
    (hTSX : X.HasTameSheetsIn FX.sheets (Φ.pullbackTheta Θ'))
    {x : Obj} (C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x)
    (hCS : ∀ i, C.M i ∈ FX.sheets) (hCT : C.Represents T) :
    ∃ (C₁ : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x)
      (D : Y.OrientedTameStructure n Θ' (Φ.obj x)),
      (∀ i, C₁.M i ∈ FX.sheets) ∧ C₁.Represents T ∧ (∀ i, D.M i ∈ FY.sheets) ∧
      D.Represents T' ∧
      Nat.card (Y.Isotropy (Φ.obj x)) = Nat.card (X.Isotropy x) ∧
      (C₁.rep.HasLUC → D.rep.HasLUC →
        Nat.card (Y.EffIsotropy (Φ.obj x)) = Nat.card (X.EffIsotropy x)) ∧
      ∀ (ω' : Ω') (K : Set (Y.orbitSupp Θ')), MeasurableSet[borel (Y.orbitSupp Θ')] K →
        Subtype.val '' K ⊆ Y.π '' D.U →
        MeasurableSet[X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ')]
            (suppMap (Φ := Φ) hΘ' ⁻¹' K) ∧
          Subtype.val '' (suppMap (Φ := Φ) hΘ' ⁻¹' K) ⊆ X.π '' C₁.U ∧
          D.sheetSum (FY.sheetIntegration hn) ω' (Y.π ⁻¹' (Subtype.val '' K)) =
            C₁.sheetSum (FX.sheetIntegration hn) (P ω')
              (X.π ⁻¹' (Subtype.val '' (suppMap (Φ := Φ) hΘ' ⁻¹' K))) := by
  have _hT' := hT'
  have _hTX := hTX
  obtain ⟨Tc⟩ := nonempty_transportChart_unit hd x
  obtain ⟨V', hyV', hV'P⟩ := Y.exists_hasPropernessProperty (Φ.obj x)
  obtain ⟨R, R', hRC, hRW, hRV', hR'⟩ := Tc.exists_rep_push_of hiso C.rep hV'P.1 hyV'
  have hRU : R.U ⊆ C.U := C.U_eq ▸ hRC
  set C₁ := C.restrictRep R hRU with hC₁
  have hP' : Y.HasPropernessProperty (Tc.Q '' C₁.U) := hV'P.mono (hR' ▸ R'.isOpen_U) hRV'
  have hΘQ := Tc.pullbackTheta_Q hΘ'
  have hC₁S : ∀ i, C₁.M i ∈ FX.sheets := C.restrictRep_mem_sheets R hRU hCS
  have hC₁T : C₁.Represents T := C.represents_restrictRep R hRU hCT
  set D := C₁.move Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP' with hD
  have hDU : D.U = Tc.Q '' R.U := C₁.move_U Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP'
  have hcomp : ∀ (ω' : Ω') (i : C₁.ι),
      FormEval.EvCompatOn FX FY Tc.isScDiffeoOn_Q (C₁.M i ∩ Tc.W) (P ω') ω' := fun ω' i =>
    Tc.evCompatOn_Q_of hev ω' ((C₁.isSmoothSubmanifold i).inter_isOpen Tc.isOpen_W)
      inter_subset_right
  have hDS : ∀ i, D.M i ∈ FY.sheets := fun i =>
    FormEval.image_mem_sheets_cross Tc.isScDiffeoOn_Q
      (FormEval.inter_mem_sheets (hC₁S i) Tc.isOpen_W) inter_subset_right
      fun ω' => ⟨P ω', hcomp ω' i⟩
  have hDT : D.Represents T' := by
    refine C₁.represents_move _ _ _ _ _ _ _ hC₁T ?_
    rintro _ ⟨u, hu, rfl⟩ hzs
    have huW := hRW hu
    have hus := (Tc.mem_smoothSet_iff hd huW).1 hzs
    rw [Tc.isScDiffeoOn_Q.left_inv u huW]
    exact ⟨hus, hTT Tc u huW hus⟩
  refine ⟨C₁, D, hC₁S, hC₁T, hDS, hDT,
    (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj_of hiso))).symm,
    fun hL hL' => (Tc.card_effIsotropy_eq_of hiso R R' hRW hR' hL hL').symm, ?_⟩
  intro ω' K hK hKU
  have hmc : @Measurable _ _ (X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ'))
      (borel (Y.orbitSupp Θ')) (suppMap (Φ := Φ) hΘ') := fun s hs =>
    borel_le_borelNullSigma _ _ ((continuous_suppMap (Φ := Φ) hΘ').borel_measurable hs)
  have hK₁ : MeasurableSet[X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ')]
      (suppMap (Φ := Φ) hΘ' ⁻¹' K) := hmc hK
  have hKU₁ : Subtype.val '' (suppMap (Φ := Φ) hΘ' ⁻¹' K) ⊆ X.π '' C₁.U := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨z, hz, hzp⟩ := hKU (mem_image_of_mem _ hp)
    rw [hDU] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    refine ⟨u, hu, ?_⟩
    apply Φ.injective_orbitMap_of_full hfull
    rw [Φ.orbitMap_π, ← Tc.π_Q (hRW hu), hzp]
    rfl
  refine ⟨hK₁, hKU₁, ?_⟩
  have hA := C₁.isMeas_preimage hTSX hC₁S hK₁
  refine C₁.sheetSum_move hn Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP' hC₁S hDS
    (hcomp ω') hA fun i => ?_
  ext z
  constructor
  · rintro ⟨hzK, u, hu, rfl⟩
    refine ⟨u, ⟨?_, hu⟩, rfl⟩
    obtain ⟨k, hk, hkz⟩ := hzK
    have huW : u ∈ Tc.W := hRW (C₁.subset_U i hu)
    have hus : X.π u ∈ X.orbitSupp (Φ.pullbackTheta Θ') :=
      ⟨u, C₁.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i hu, rfl⟩
    refine ⟨⟨X.π u, hus⟩, ?_, rfl⟩
    have he : suppMap (Φ := Φ) hΘ' ⟨X.π u, hus⟩ = k := by
      apply Subtype.ext
      change Φ.orbitMap (X.π u) = k.1
      rw [Φ.orbitMap_π, ← Tc.π_Q huW, hkz]
    rw [mem_preimage, he]
    exact hk
  · rintro ⟨u, ⟨⟨p, hp, hpu⟩, hu⟩, rfl⟩
    have huW : u ∈ Tc.W := hRW (C₁.subset_U i hu)
    refine ⟨⟨_, hp, ?_⟩, u, hu, rfl⟩
    change Φ.orbitMap p.1 = Y.π (Tc.Q u)
    rw [hpu, Φ.orbitMap_π, Tc.π_Q huW]

end Local

/-! ### The integrals -/

section Integrals

variable (hd : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj) (hfull : Φ.toFunctor.Full)
  (hiso : ∀ x, Bijective (Φ.isotropyHom x))
  (hev : ∀ (ω' : Ω') {N : Set Obj}, X.PObj.IsSmoothSubmanifold N → ∀ {y : Obj}, y ∈ N →
    ∀ α : Fin n → X.PObj.TangentSpace, (∀ i, α i ∈ X.PObj.submanifoldTangent N y) →
    FX.ev (P ω') α = FY.ev ω' (fun i => Φ.tangent.obj (α i)))

include hd hfull hiso hev in
/-- **Theorem 11.4.1, 2021 p. 543, for the integrals, along a full and faithful local
sc-diffeomorphism** `Φ : X → Y` whose image contains the support: for `Θ̂'` on `Y` oriented, tame
(with sheets in the class), compact, of dimension `n`, with `|supp Θ'| ⊆ |Φ|(|X|)`,
`∫_{Φ^*Θ̂'} Φ^*ω' = ∫_{Θ̂'} ω'`. -/
theorem integral_pull_of (hn : 0 < n)
    (hΘ' : Y.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.IsCompactBranched Θ')
    (hT' : Y.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T')
    (hrange : Y.orbitSupp Θ' ⊆ range Φ.orbitMap)
    (hΘ : X.IsBranchedEpSubgroupoid (Φ.pullbackTheta Θ'))
    (hcpt : X.IsCompactBranched (Φ.pullbackTheta Θ'))
    (hT : X.IsOrientation (Φ.pullbackTheta Θ') T) (hTT : Φ.IsTransported T T')
    (hcov : ∀ x ∈ supp (Φ.pullbackTheta Θ'),
      ∃ C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x,
        (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T)
    (ω' : Ω') :
    branchedIntegral (FX.sheetIntegration hn) hΘ hcpt hT hcov (P ω') =
      branchedIntegral (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω' := by
  have hΘf := hΘ'.isFunctorial
  have hTSX : X.HasTameSheetsIn FX.sheets (Φ.pullbackTheta Θ') := hasTameSheetsIn_of_hcov hcov
  have : CompactSpace (Y.orbitSupp Θ') := isCompact_iff_compactSpace.1 hcpt'
  have hmc : @Measurable _ _ (X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ'))
      (borel (Y.orbitSupp Θ')) (suppMap (Φ := Φ) hΘf) := fun s hs =>
    borel_le_borelNullSigma _ _ ((continuous_suppMap (Φ := Φ) hΘf).borel_measurable hs)
  set μ₁ := branchedMeasure (FX.sheetIntegration hn) hΘ hcpt hT hcov (P ω') with hμ₁
  set μY := branchedMeasure (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω' with hμY
  set ν : @SignedMeasure (Y.orbitSupp Θ') (borel _) :=
    @VectorMeasure.map _ _ (X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ'))
      (borel (Y.orbitSupp Θ')) ℝ _ _ μ₁ (suppMap (Φ := Φ) hΘf) with hν
  have hνK : ∀ K : Set (Y.orbitSupp Θ'), MeasurableSet[borel (Y.orbitSupp Θ')] K →
      ν K = μ₁ (suppMap (Φ := Φ) hΘf ⁻¹' K) := fun K hK =>
    @VectorMeasure.map_apply _ _ (X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ'))
      (borel (Y.orbitSupp Θ')) ℝ _ _ μ₁ _ hmc K hK
  have key := signedMeasure_univ_eq_of_local (borel_le_borelNullSigma _) le_rfl μY ν fun q => by
    obtain ⟨p, hp⟩ := hrange q.2
    have hps : p ∈ X.orbitSupp (Φ.pullbackTheta Θ') := by
      rw [Φ.orbitSupp_pullbackTheta hΘf, mem_preimage, hp]; exact q.2
    obtain ⟨x, hx, rfl⟩ := hps
    obtain ⟨C, hCS, hCT⟩ := hcov x hx
    obtain ⟨C₁, D, hC₁S, hC₁T, hDS, hDT, hcard, -, hsum⟩ :=
      exists_local_comparison hd hfull hiso hev hn hΘf hT'.isGrHatSection hT.isGrHatSection hTT
        hTSX C hCS hCT
    refine ⟨Subtype.val ⁻¹' (Y.π '' D.U),
      (Y.proposition_7_1_8 _ D.isOpen_U).preimage continuous_subtype_val,
      ⟨Φ.obj x, D.mem_U, by rw [← hp, Φ.orbitMap_π]⟩, fun K hK hKN => ?_⟩
    have hKU : Subtype.val '' K ⊆ Y.π '' D.U := by
      rintro _ ⟨k, hk, rfl⟩
      exact hKN hk
    obtain ⟨hK₁, hKU₁, e⟩ := hsum ω' K hK hKU
    rw [hνK K hK, hμ₁, hμY,
      branchedMeasure_apply _ hΘ hcpt hT hcov (P ω') C₁ hC₁S hC₁T hK₁ hKU₁,
      branchedMeasure_apply _ hΘ' hcpt' hT' hcov' ω' D hDS hDT
        (borel_le_borelNullSigma _ _ hK) hKU, localMeasure, localMeasure, hcard, e]
  have hu := hνK univ (@MeasurableSet.univ _ (borel _))
  rw [preimage_univ] at hu
  unfold branchedIntegral
  rw [← hμ₁, ← hμY, ← hu, key]

include hd hfull hiso hev in
/-- **Theorem 11.4.2, 2021 p. 544, for the integrals, along a full and faithful local
sc-diffeomorphism** `Φ : X → Y` whose image contains the support:
`∮_{Φ^*Θ̂'} Φ^*ω' = ∮_{Θ̂'} ω'`. -/
theorem integralEff_pull_of (hn : 0 < n)
    (hΘ' : Y.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.IsCompactBranched Θ')
    (hT' : Y.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T' ∧ D.rep.HasLUC)
    (hLY : Y.IsLUC)
    (hrange : Y.orbitSupp Θ' ⊆ range Φ.orbitMap)
    (hΘ : X.IsBranchedEpSubgroupoid (Φ.pullbackTheta Θ'))
    (hcpt : X.IsCompactBranched (Φ.pullbackTheta Θ'))
    (hT : X.IsOrientation (Φ.pullbackTheta Θ') T) (hTT : Φ.IsTransported T T')
    (hcov : ∀ x ∈ supp (Φ.pullbackTheta Θ'),
      ∃ C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x,
        (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T ∧ C.rep.HasLUC)
    (ω' : Ω') :
    branchedIntegralEff (FX.sheetIntegration hn) hΘ hcpt hT hcov (P ω') =
      branchedIntegralEff (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω' := by
  have hΘf := hΘ'.isFunctorial
  have hLX : X.IsLUC := isLUC_of_isLocalScDiffeo hd hLY
  have hTSX : X.HasTameSheetsIn FX.sheets (Φ.pullbackTheta Θ') :=
    hasTameSheetsIn_of_hcov (plainCov hcov)
  have : CompactSpace (Y.orbitSupp Θ') := isCompact_iff_compactSpace.1 hcpt'
  have hmc : @Measurable _ _ (X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ'))
      (borel (Y.orbitSupp Θ')) (suppMap (Φ := Φ) hΘf) := fun s hs =>
    borel_le_borelNullSigma _ _ ((continuous_suppMap (Φ := Φ) hΘf).borel_measurable hs)
  set μ₁ := branchedMeasureEff (FX.sheetIntegration hn) hΘ hcpt hT hcov (P ω') with hμ₁
  set μY := branchedMeasureEff (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω' with hμY
  set ν : @SignedMeasure (Y.orbitSupp Θ') (borel _) :=
    @VectorMeasure.map _ _ (X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ'))
      (borel (Y.orbitSupp Θ')) ℝ _ _ μ₁ (suppMap (Φ := Φ) hΘf) with hν
  have hνK : ∀ K : Set (Y.orbitSupp Θ'), MeasurableSet[borel (Y.orbitSupp Θ')] K →
      ν K = μ₁ (suppMap (Φ := Φ) hΘf ⁻¹' K) := fun K hK =>
    @VectorMeasure.map_apply _ _ (X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ'))
      (borel (Y.orbitSupp Θ')) ℝ _ _ μ₁ _ hmc K hK
  have key := signedMeasure_univ_eq_of_local (borel_le_borelNullSigma _) le_rfl μY ν fun q => by
    obtain ⟨p, hp⟩ := hrange q.2
    have hps : p ∈ X.orbitSupp (Φ.pullbackTheta Θ') := by
      rw [Φ.orbitSupp_pullbackTheta hΘf, mem_preimage, hp]; exact q.2
    obtain ⟨x, hx, rfl⟩ := hps
    obtain ⟨C, hCS, hCT, -⟩ := hcov x hx
    obtain ⟨C₁, D, hC₁S, hC₁T, hDS, hDT, -, hcard, hsum⟩ :=
      exists_local_comparison hd hfull hiso hev hn hΘf hT'.isGrHatSection hT.isGrHatSection hTT
        hTSX C hCS hCT
    have hL₁ : C₁.rep.HasLUC := X.isLUC_iff_forall_naturalRep.1 hLX _ _
    have hLD : D.rep.HasLUC := Y.isLUC_iff_forall_naturalRep.1 hLY _ _
    refine ⟨Subtype.val ⁻¹' (Y.π '' D.U),
      (Y.proposition_7_1_8 _ D.isOpen_U).preimage continuous_subtype_val,
      ⟨Φ.obj x, D.mem_U, by rw [← hp, Φ.orbitMap_π]⟩, fun K hK hKN => ?_⟩
    have hKU : Subtype.val '' K ⊆ Y.π '' D.U := by
      rintro _ ⟨k, hk, rfl⟩
      exact hKN hk
    obtain ⟨hK₁, hKU₁, e⟩ := hsum ω' K hK hKU
    rw [hνK K hK, hμ₁, hμY,
      branchedMeasureEff_apply _ hΘ hcpt hT hcov (P ω') C₁ hC₁S hC₁T hL₁ hK₁ hKU₁,
      branchedMeasureEff_apply _ hΘ' hcpt' hT' hcov' ω' D hDS hDT hLD
        (borel_le_borelNullSigma _ _ hK) hKU, localMeasureEff, localMeasureEff,
      hcard hL₁ hLD, e]
  have hu := hνK univ (@MeasurableSet.univ _ (borel _))
  rw [preimage_univ] at hu
  unfold branchedIntegralEff
  rw [← hμ₁, ← hμY, ← hu, key]

end Integrals

end EpFunctor

end Polyfold
