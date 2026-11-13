import Polyfold.Chapter11.GapP2_H4Move

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4, proof of Theorem 11.4.1 (pp. 543–544; 2017: Theorem 11.8, p. 396),
gap G.131.  Numbers and pages are the 2021 text's.

# Matching oriented tame structures along an equivalence

For an equivalence `Φ : X → Y` and a transport chart `Q = ψ̂ ∘ Φ : W → W'` at `x ↦ y`
(`EpFunctor.TransportChart`, Chapter 10), the text "considers open neighborhoods `U(x)` and
`U(F(x))` such that `F : U(x) → U(F(x))` is an sc-diffeomorphism, and both neighborhoods have the
properness property and allow the natural actions", and moves a branching structure by `F|U(x)`.

* `TransportChart.mem_smoothSet_iff`, `pullbackTheta_Q`: `Q` preserves `X_∞` and `Φ^*Θ'`;
  `pullSection_Q`, `pushSection_Q`: the orientations `Φ^* T̂'`, `Φ_* T̂` are moved by `TQ`;
  `rel_symm`: the same relation read along `Q⁻¹`.
* `evCompatOn_Q`, `evCompatOn_Qinv`: for an evaluation compatible with the pull-back
  (`FormEval.IsPullback`), `ω'` is moved to `Φ^*ω'` by `Q` and `Φ^*ω'` to `ω'` by `Q⁻¹`.
* `exists_rep_push`: natural representations on `U(x)` and on `Q(U(x))` for small `U(x)`.
* `exists_push_structure`: a structure at `y` with sheets in the class describing `T̂'` from one at
  `x` (used for `Φ_*Θ̂`); `pullData`, `pullStructure`: a structure at `y` restricted to
  `Q(U(x))` and its move to `x` by `Q⁻¹` (used for `Φ^*Θ̂'`), with sheets in the class and
  describing the pulled-back orientation.
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

/-! ### A relation of oriented sections read backwards -/

namespace EpGroupoid

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- **`T'(f u) = Tf_* T(u)` on `W` gives `T(g z) = Tg_* T'(z)` on `W'`.** -/
theorem rel_symm {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}
    (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') {T : Obj → X.PObj.OrTangent →₀ ℚ}
    {T' : Obj' → Y.PObj.OrTangent →₀ ℚ} (hT : X.IsGrHatSection T)
    (h : ∀ u ∈ W, u ∈ X.PObj.smoothSet →
      T' (f u) = (T u).mapDomain (OrTangent.map (tangentMapOn hf.isScSmoothOn)))
    {z : Obj'} (hz : z ∈ W') (hgz : g z ∈ X.PObj.smoothSet) :
    T (g z) = (T' z).mapDomain (OrTangent.map (tangentMapOn hf.symm.isScSmoothOn)) := by
  have hgW : g z ∈ W := hf.mapsTo_inv hz
  have e : T' z = T' (f (g z)) := by rw [hf.right_inv z hz]
  rw [e, h (g z) hgW hgz, mapDomain_map_map]
  refine (mapDomain_map_id (hT.mem _ hgz) fun α hα => ?_).symm
  have hαU : α ∈ X.PObj.tangentPreimage W := by change _ ∈ W; rw [hα]; exact hgW
  exact hf.tangent.left_inv α hαU

end EpGroupoid

namespace EpFunctor

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Φ : EpFunctor X Y}

namespace TransportChart

variable {x : Obj} {y : Obj'} (T : Φ.TransportChart x y)

/-- `Q` preserves `X_∞` (through `ψ_u : Φ(u) → Q(u)`). -/
theorem mem_smoothSet_iff (hd : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj) {u : Obj} (hu : u ∈ T.W) :
    T.Q u ∈ Y.PObj.smoothSet ↔ u ∈ X.PObj.smoothSet := by
  rw [← hd.mem_smoothSet_iff u, ← T.src_ψ u hu, ← T.tgt_ψ u hu]
  exact ⟨fun h => Y.src_mem_smoothSet_of_tgt h, fun h => Y.tgt_mem_smoothSet_of_src h⟩

/-- `Φ^*Θ'(u) = Θ'(Q u)` on `W`. -/
theorem pullbackTheta_Q {Θ' : Obj' → ℚ} (hΘ' : Y.IsFunctorial Θ') :
    ∀ u ∈ T.W, Θ' (T.Q u) = Φ.pullbackTheta Θ' u := fun u hu => by
  rw [pullbackTheta_apply, ← T.tgt_ψ u hu, ← hΘ' (T.ψ u), T.src_ψ u hu]

/-- **`T'(Q u) = TQ_*(Φ^*T')(u)`** on `W ∩ X_∞`. -/
theorem pullSection_Q (hd : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj)
    {T' : Obj' → Y.PObj.OrTangent →₀ ℚ} (hT' : Y.IsGrHatSection T') :
    ∀ u ∈ T.W, u ∈ X.PObj.smoothSet →
      T' (T.Q u) = (Φ.pullSection T' u).mapDomain
        (OrTangent.map (tangentMapOn T.isScDiffeoOn_Q.isScSmoothOn)) := fun u hu hus => by
  have hΦs : Φ.obj u ∈ Y.PObj.smoothSet := (hd.mem_smoothSet_iff u).2 hus
  rw [pullSection_of_mem hus, mapDomain_map_map, ← T.tgt_ψ u hu,
    ← hT'.natural (T.ψ u) (by rw [T.src_ψ u hu]; exact hΦs), T.src_ψ u hu, grHatPush]
  refine mapDomain_map_congr (hT'.mem _ hΦs) fun β hβ => ?_
  obtain ⟨h1, h2⟩ := fibreInv_spec_tangent hd hβ
  have h := T.tangentMor_ψ_tangent_obj (α := fibreInv Φ.tangent.obj u β)
    (show _ ∈ T.W by rw [h1]; exact hu)
  rw [h1, h2] at h
  exact h

/-- **`(Φ_*T)(Q u) = TQ_* T(u)`** on `W ∩ X_∞`. -/
theorem pushSection_Q (hΦ : Φ.IsEquivalence) {Tx : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsGrHatSection Tx) :
    ∀ u ∈ T.W, u ∈ X.PObj.smoothSet →
      Φ.pushSection Tx (T.Q u) = (Tx u).mapDomain
        (OrTangent.map (tangentMapOn T.isScDiffeoOn_Q.isScSmoothOn)) := fun u hu hus => by
  have hQs : T.Q u ∈ Y.PObj.smoothSet := (T.mem_smoothSet_iff hΦ.isLocalScDiffeo_obj hu).2 hus
  have hts : Y.tgt (T.ψ u) ∈ Y.PObj.smoothSet := by rw [T.tgt_ψ u hu]; exact hQs
  have e := pushSection_eq hΦ hT (T.src_ψ u hu) hts
  rw [T.tgt_ψ u hu] at e
  rw [e]
  refine mapDomain_map_congr (hT.mem u hus) fun α hα => ?_
  have h := T.tangentMor_ψ_tangent_obj (α := α) (show _ ∈ T.W by rw [hα]; exact hu)
  rw [hα] at h
  exact h

/-! ### Forms moved by `Q` and `Q⁻¹` -/

variable {n : ℕ} {Ω Ω' : Type*} [AddCommGroup Ω] [Module ℝ Ω] [AddCommGroup Ω'] [Module ℝ Ω']
  {FX : X.FormEval n Ω} {FY : Y.FormEval n Ω'} {P : Ω' →ₗ[ℝ] Ω}

/-- **`ω'(TQ β) = (Φ^*ω')(β)`** on the tangent spaces of a submanifold `N ⊆ W`. -/
theorem evCompatOn_Q (hP : FX.IsPullback FY Φ P) (ω' : Ω') {N : Set Obj}
    (hN : X.PObj.IsSmoothSubmanifold N) (hNW : N ⊆ T.W) :
    FormEval.EvCompatOn FX FY T.isScDiffeoOn_Q N (P ω') ω' := by
  intro z hz β hβ
  have hb : ∀ i, X.PObj.levelVal 1 (X.PObj.tangentProj (β i)) = z := fun i => (hβ i).1
  have hQN : Y.PObj.IsSmoothSubmanifold (T.Q '' N) := hN.image_of_isScDiffeoOn T.isScDiffeoOn_Q hNW
  have hmem : ∀ i, tangentMapOn T.isScDiffeoOn_Q.isScSmoothOn (β i) ∈
      Y.PObj.submanifoldTangent (T.Q '' N) (T.Q z) := fun i => by
    rw [submanifoldTangent_image_of_isScDiffeoOn T.isScDiffeoOn_Q hN hNW hz]
    exact mem_image_of_mem _ (hβ i)
  have hψ1 : T.ψ z ∈ Y.PMor.levelSet 1 := Y.mem_levelSet_one_of_tgt_mem_smoothSet (by
    rw [T.tgt_ψ z (hNW hz)]; exact (hQN.subset_smoothSet) (mem_image_of_mem _ hz))
  have hsrc : Y.src (Y.inv (T.ψ z)) = T.Q z := by rw [Y.src_inv, T.tgt_ψ z (hNW hz)]
  rw [← FY.ev_mor ω' hQN (mem_image_of_mem _ hz) (Y.inv (T.ψ z)) hsrc _ hmem,
    hP.ev_pull ω' hN hz β hβ]
  congr 1
  funext i
  have h := T.tangentMor_ψ_tangent_obj (α := β i) (show _ ∈ T.W by rw [hb i]; exact hNW hz)
  rw [hb i] at h
  rw [← h]
  exact Y.tangentMor_inv_tangentMor hψ1 (by rw [levelVal_tangentProj_tangent_obj, hb i,
    T.src_ψ z (hNW hz)])

/-- **`(Φ^*ω')(TQ⁻¹ β) = ω'(β)`** on the tangent spaces of a submanifold `N' ⊆ W'`. -/
theorem evCompatOn_Qinv (hP : FX.IsPullback FY Φ P) (ω' : Ω') {N' : Set Obj'}
    (hN' : Y.PObj.IsSmoothSubmanifold N') (hNW : N' ⊆ T.W') :
    FormEval.EvCompatOn FY FX T.isScDiffeoOn_Q.symm N' ω' (P ω') := by
  intro z hz β hβ
  have hgN : X.PObj.IsSmoothSubmanifold (T.Qinv '' N') :=
    hN'.image_of_isScDiffeoOn T.isScDiffeoOn_Q.symm hNW
  have hgW : T.Qinv '' N' ⊆ T.W :=
    image_subset_iff.2 fun w hw => T.isScDiffeoOn_Q.mapsTo_inv (hNW hw)
  have hmem : ∀ i, tangentMapOn T.isScDiffeoOn_Q.symm.isScSmoothOn (β i) ∈
      X.PObj.submanifoldTangent (T.Qinv '' N') (T.Qinv z) := fun i => by
    rw [submanifoldTangent_image_of_isScDiffeoOn T.isScDiffeoOn_Q.symm hN' hNW hz]
    exact mem_image_of_mem _ (hβ i)
  have h := T.evCompatOn_Q hP ω' hgN hgW (T.Qinv z) (mem_image_of_mem _ hz) _ hmem
  rw [← h]
  congr 1
  funext i
  have hβU : β i ∈ Y.PObj.tangentPreimage T.W' := by
    change _ ∈ T.W'; rw [(hβ i).1]; exact hNW hz
  exact T.isScDiffeoOn_Q.tangent.right_inv (β i) hβU

/-! ### Natural representations on `U(x)` and `Q(U(x))` -/

/-- **Natural representations on `U(x) ⊆ U₀(x) ∩ W ∩ Q⁻¹(V')` and on `Q(U(x))`** (2021 p. 467,
"if `U(x)` is small enough the natural action on `U(y)` is defined"). -/
theorem exists_rep_push (hΦ : Φ.IsEquivalence) (R₀ : X.NaturalRep x) {V' : Set Obj'}
    (hV' : IsOpen V') (hyV' : y ∈ V') :
    ∃ (R : X.NaturalRep x) (R' : Y.NaturalRep y), R.U ⊆ R₀.U ∧ R.U ⊆ T.W ∧
      T.Q '' R.U ⊆ V' ∧ R'.U = T.Q '' R.U := by
  obtain ⟨R'₀, -⟩ := Y.theorem_7_1_13 y isOpen_univ (mem_univ y)
  have hO : IsOpen (T.W ∩ T.Q ⁻¹' (R'₀.U ∩ V')) :=
    T.continuousOn_Q.isOpen_inter_preimage T.isOpen_W (R'₀.isOpen_U.inter hV')
  have hxO : x ∈ T.W ∩ T.Q ⁻¹' (R'₀.U ∩ V') :=
    ⟨T.mem_W, by rw [mem_preimage, T.Q_self]; exact ⟨R'₀.mem_U, hyV'⟩⟩
  obtain ⟨R, hRsub, -, -⟩ := exists_naturalRep_shrink X R₀ hO hxO
  have hR : R.U ⊆ T.W ∩ T.Q ⁻¹' R'₀.U := fun u hu => ⟨(hRsub hu).1.1, (hRsub hu).1.2.1⟩
  obtain ⟨R', hR'U, -⟩ := T.exists_naturalRep_push hΦ R R'₀ hR
  exact ⟨R, R', fun u hu => (hRsub hu).2, fun u hu => (hRsub hu).1.1,
    image_subset_iff.2 fun u hu => (hRsub hu).1.2.2, hR'U⟩

end TransportChart

end EpFunctor

/-! ### Structures along a transport chart -/

namespace EpGroupoid.OrientedTameStructure

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Φ : EpFunctor X Y} {n : ℕ}
  {Ω Ω' : Type*} [AddCommGroup Ω] [Module ℝ Ω] [AddCommGroup Ω'] [Module ℝ Ω']
  {FX : X.FormEval n Ω} {FY : Y.FormEval n Ω'} {P : Ω' →ₗ[ℝ] Ω}
  {Θ : Obj → ℚ} {Θ' : Obj' → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}
  {T' : Obj' → Y.PObj.OrTangent →₀ ℚ} {x : Obj} {y : Obj'}

/-- **A structure at `y` from one at `x`** (the push-forward direction): if `C` at `x` has sheets
in the class and describes `T̂`, and `Θ'(Q u) = Θ(u)`, `T̂'(Q u) = TQ_* T̂(u)` on `W`, there is a
structure at `y` with sheets in the class describing `T̂'`. -/
theorem exists_push_structure (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (Tc : Φ.TransportChart x y) (hΘ : ∀ u ∈ Tc.W, Θ' (Tc.Q u) = Θ u)
    (hTT : ∀ u ∈ Tc.W, u ∈ X.PObj.smoothSet →
      T' (Tc.Q u) = (T u).mapDomain (OrTangent.map (tangentMapOn Tc.isScDiffeoOn_Q.isScSmoothOn)))
    (C : X.OrientedTameStructure n Θ x) (hCS : ∀ i, C.M i ∈ FX.sheets) (hCT : C.Represents T) :
    ∃ D : Y.OrientedTameStructure n Θ' y, (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T' := by
  obtain ⟨V', hyV', hV'P⟩ := Y.exists_hasPropernessProperty y
  obtain ⟨R, R', hRC, hRW, hRV', hR'⟩ := Tc.exists_rep_push hΦ C.rep hV'P.1 hyV'
  have hRU : R.U ⊆ C.U := C.U_eq ▸ hRC
  set C₁ := C.restrictRep R hRU
  have hP' : Y.HasPropernessProperty (Tc.Q '' C₁.U) :=
    hV'P.mono (hR' ▸ R'.isOpen_U) hRV'
  refine ⟨C₁.move Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘ R' hR' hP', fun i => ?_, ?_⟩
  · have hMW : C₁.M i ∩ Tc.W ⊆ Tc.W := inter_subset_right
    exact FormEval.image_mem_sheets_cross Tc.isScDiffeoOn_Q
      (FormEval.inter_mem_sheets (C.restrictRep_mem_sheets R hRU hCS i) Tc.isOpen_W) hMW
      fun ω' => ⟨P ω', Tc.evCompatOn_Q hP ω' ((C₁.isSmoothSubmanifold i).inter_isOpen
        Tc.isOpen_W) hMW⟩
  · refine C₁.represents_move _ _ _ _ _ _ _ (C.represents_restrictRep R hRU hCT) ?_
    rintro _ ⟨u, hu, rfl⟩ hzs
    have huW := hRW hu
    have hus := (Tc.mem_smoothSet_iff hΦ.isLocalScDiffeo_obj huW).1 hzs
    rw [Tc.isScDiffeoOn_Q.left_inv u huW]
    exact ⟨hus, hTT u huW hus⟩

/-- **The data for a structure at `x` from one at `y`** (the pull-back direction): natural
representations `R` at `x`, `R'` at `y` with `R'.U = Q(R.U) ⊆ U(y)`, `R.U ⊆ W`, and `R.U` with the
properness property. -/
theorem exists_pullData (hΦ : Φ.IsEquivalence) (Tc : Φ.TransportChart x y)
    (D : Y.OrientedTameStructure n Θ' y) :
    ∃ (R : X.NaturalRep x) (R' : Y.NaturalRep y), R'.U ⊆ D.U ∧ R.U ⊆ Tc.W ∧
      R'.U = Tc.Q '' R.U ∧ X.HasPropernessProperty R.U := by
  obtain ⟨V, hxV, hVP⟩ := X.exists_hasPropernessProperty x
  obtain ⟨R₀, hR₀⟩ := X.theorem_7_1_13 x hVP.1 hxV
  obtain ⟨R, R', hRR₀, hRW, hRD, hR'⟩ := Tc.exists_rep_push hΦ R₀ D.isOpen_U D.mem_U
  exact ⟨R, R', hR' ▸ hRD, hRW, hR', hVP.mono R.isOpen_U (hRR₀.trans hR₀)⟩

variable (Tc : Φ.TransportChart x y)

theorem Qinv_image_Q_image {A : Set Obj} (hA : A ⊆ Tc.W) : Tc.Qinv '' (Tc.Q '' A) = A := by
  rw [image_image]
  conv_rhs => rw [← image_id A]
  exact image_congr fun u hu => Tc.isScDiffeoOn_Q.left_inv u (hA hu)

theorem Qinv_y : Tc.Qinv y = x := by
  have h := Tc.isScDiffeoOn_Q.left_inv x Tc.mem_W
  rwa [Tc.Q_self] at h

/-- **The structure at `x` moved back from a structure `D` at `y` restricted to `Q(R.U)`.** -/
def pullStructure (hΘ : ∀ u ∈ Tc.W, Θ' (Tc.Q u) = Θ u) (D : Y.OrientedTameStructure n Θ' y)
    (R : X.NaturalRep x) (R' : Y.NaturalRep y) (hR'D : R'.U ⊆ D.U) (hRW : R.U ⊆ Tc.W)
    (hR' : R'.U = Tc.Q '' R.U) (hRP : X.HasPropernessProperty R.U) :
    X.OrientedTameStructure n Θ x :=
  (D.restrictRep R' hR'D).move Tc.isScDiffeoOn_Q.symm
    (by rw [restrictRep_U, hR']; exact image_subset_iff.2 fun u hu =>
      Tc.isScDiffeoOn_Q.mapsTo (hRW hu))
    (Qinv_y Tc)
    (fun z hz => by
      rw [← hΘ _ (Tc.isScDiffeoOn_Q.mapsTo_inv hz), Tc.isScDiffeoOn_Q.right_inv z hz])
    R (by rw [restrictRep_U, hR', Qinv_image_Q_image Tc hRW])
    (by rw [restrictRep_U, hR', Qinv_image_Q_image Tc hRW]; exact hRP)

variable (hΘ : ∀ u ∈ Tc.W, Θ' (Tc.Q u) = Θ u) (D : Y.OrientedTameStructure n Θ' y)
  (R : X.NaturalRep x) (R' : Y.NaturalRep y) (hR'D : R'.U ⊆ D.U) (hRW : R.U ⊆ Tc.W)
  (hR' : R'.U = Tc.Q '' R.U) (hRP : X.HasPropernessProperty R.U)

theorem pullStructure_U : (pullStructure Tc hΘ D R R' hR'D hRW hR' hRP).U = R.U := by
  exact (pullStructure Tc hΘ D R R' hR'D hRW hR' hRP).U_eq

include hRW hR' in
theorem restrictRep_U_subset_W' : (D.restrictRep R' hR'D).U ⊆ Tc.W' := by
  rw [restrictRep_U, hR']
  exact image_subset_iff.2 fun u hu => Tc.isScDiffeoOn_Q.mapsTo (hRW hu)

/-- The moved-back structure has its sheets in the class. -/
theorem pullStructure_mem_sheets (hP : FX.IsPullback FY Φ P) (hDS : ∀ i, D.M i ∈ FY.sheets)
    (i : D.ι) : (pullStructure Tc hΘ D R R' hR'D hRW hR' hRP).M i ∈ FX.sheets := by
  have hMW : (D.restrictRep R' hR'D).M i ∩ Tc.W' ⊆ Tc.W' := inter_subset_right
  refine FormEval.image_mem_sheets_cross Tc.isScDiffeoOn_Q.symm
    (FormEval.inter_mem_sheets (D.restrictRep_mem_sheets R' hR'D hDS i) Tc.isOpen_W') hMW
    fun ω => ?_
  obtain ⟨ω', rfl⟩ := hP.surjective ω
  exact ⟨ω', Tc.evCompatOn_Qinv hP ω' (((D.restrictRep R' hR'D).isSmoothSubmanifold i).inter_isOpen
    Tc.isOpen_W') hMW⟩

/-- The moved-back structure describes `T̂` if `T̂'(Q u) = TQ_* T̂(u)` on `W`. -/
theorem represents_pullStructure (hΦ : Φ.IsEquivalence) (hT : X.IsGrHatSection T)
    (hTT : ∀ u ∈ Tc.W, u ∈ X.PObj.smoothSet →
      T' (Tc.Q u) = (T u).mapDomain (OrTangent.map (tangentMapOn Tc.isScDiffeoOn_Q.isScSmoothOn)))
    (hDT : D.Represents T') : (pullStructure Tc hΘ D R R' hR'D hRW hR' hRP).Represents T := by
  refine (D.restrictRep R' hR'D).represents_move _ _ _ _ _ _ _
    (D.represents_restrictRep R' hR'D hDT) ?_
  rintro _ ⟨z, hz, rfl⟩ hus
  have hzW' := restrictRep_U_subset_W' Tc D R R' hR'D hRW hR' hz
  have hgz := Tc.isScDiffeoOn_Q.mapsTo_inv hzW'
  have hzs : z ∈ Y.PObj.smoothSet := by
    have h := (Tc.mem_smoothSet_iff hΦ.isLocalScDiffeo_obj hgz).2 hus
    rwa [Tc.isScDiffeoOn_Q.right_inv z hzW'] at h
  refine ⟨?_, ?_⟩
  · rw [Tc.isScDiffeoOn_Q.right_inv z hzW']; exact hzs
  · rw [Tc.isScDiffeoOn_Q.right_inv z hzW']
    exact rel_symm Tc.isScDiffeoOn_Q hT hTT hzW' hus

end EpGroupoid.OrientedTameStructure

end Polyfold
