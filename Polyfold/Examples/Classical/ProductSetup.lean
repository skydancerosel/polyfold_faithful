import Polyfold.Examples.Classical.Main
import Polyfold.Examples.OrbifoldSquareInf

/-!
# The classical reduction crossed with the weighted `ℓ²` factor: the strong polyfold bundle

For Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Theorem 16.6.6,
2021 p. 739.  The finite-dimensional setting of `Setup.lean` (a finite group `G` acting linearly
and faithfully on `ℝⁿ`, a fibre action `σ`) is crossed with the sc-Hilbert space `H` of
`WeightedEllTwo.lean` (strictly nested levels), on which `G` acts trivially, as in
`OrbifoldSquareInf*.lean`.

## What is formalized (namespace `Polyfold.Examples.Classical.Product`)

* `XP G n = (G ⋉ ℝⁿ) × H`, `AP σ = AG σ × AH`: the strong bundle `(ℝⁿ × ℝⁿ) × (H ◁ H)` over
  `(G ⋉ ℝⁿ) × H`, with `μ` given by `σ` on the fibre `ℝⁿ` and trivial on `H`.
* `π_eq_π_iff`, `card_isotropy`: orbits and isotropy (`♯G_{(x, e)} = ♯Stab_G(x)`).
* `isEffective_XP` (Definition 7.2.1), `isZhou_XP` (Definition 7.4.5),
  `hasParacompactOrbitSpace_XP`, `isLRLocal_EP` (Definition 8.4.2).
* `prStructure σ`, `prBundle σ` (Definitions 16.3.1, 16.3.4); `isTame_AP`,
  `prBundle_boundary_eq_empty`, `admitsBumpFunctions_AP`, `hasScPlusSectionsThrough_AP`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.Product

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure WeightedEllTwo SBLocalization
  Polyfold.Examples.OrbifoldSquareInf Polyfold.Examples.Classical

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]

instance instParaObjP₁ : ParacompactSpace ((Fin n → ℝ) × HObj) :=
  MPolyfold.paracompactSpace_prod (rnPolyfold n) PH

instance instParaObjP₂ : ParacompactSpace ((Fin n → ℝ) × AH.Obj) :=
  MPolyfold.paracompactSpace_prod (rnPolyfold n) PH

instance instParaWP₁ : ParacompactSpace (((Fin n → ℝ) × (Fin n → ℝ)) × (HObj × H 0)) :=
  inferInstance

instance instParaWP₂ : ParacompactSpace (((Fin n → ℝ) × (Fin n → ℝ)) × AH.W) :=
  inferInstanceAs (ParacompactSpace (((Fin n → ℝ) × (Fin n → ℝ)) × (HObj × H 0)))

omit [Fintype G] in
instance instParacompactMorP : ParacompactSpace ((G × (Fin n → ℝ)) × HObj) :=
  MPolyfold.paracompactSpace_prod (XG G n).PMor (EpGroupoid.trivial PH).PMor

variable (G n) in
/-- **The ep-groupoid `(G ⋉ ℝⁿ) × H`**, `G` acting trivially on `H`. -/
abbrev XP : EpGroupoid ((Fin n → ℝ) × HObj) ((G × (Fin n → ℝ)) × HObj) :=
  (XG G n).prod (EpGroupoid.trivial PH)

variable (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))

/-- **`(ℝⁿ × ℝⁿ) × (H ◁ H) → ℝⁿ × H` over `(G ⋉ ℝⁿ) × H`.** -/
abbrev AP : SEP.{0} := (AG σ).prod AH

theorem AP_X : (AP σ).X = XP G n := rfl

/-! ### Orbits and isotropy -/

/-- Two points of `ℝⁿ × H` are in one orbit iff their `H`-components agree and the
`ℝⁿ`-components lie in one `G`-orbit. -/
theorem π_eq_π_iff {x y : (Fin n → ℝ) × HObj} :
    (XP G n).π x = (XP G n).π y ↔ ∃ g : G, g • x.1 = y.1 ∧ x.2 = y.2 := by
  rw [EpGroupoid.prod_π_eq_π_iff]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨g, hg⟩ := (action_π_eq_π_iff isScSmoothMap_smul).1 h1
    exact ⟨g, hg, trivial_π_eq_π_iff.1 h2⟩
  · rintro ⟨g, hg, h2⟩
    exact ⟨(action_π_eq_π_iff isScSmoothMap_smul).2 ⟨g, hg⟩, trivial_π_eq_π_iff.2 h2⟩

/-- The components of an isotropy element of `(x, e)`: it is `((g, x), e)` with `g • x = x`. -/
theorem isotropy_val {x : (Fin n → ℝ) × HObj} (g : (XP G n).Isotropy x) :
    g.val.1.2 = x.1 ∧ g.val.2 = x.2 ∧ g.val.1.1 • x.1 = x.1 := by
  have hs : (g.val.1.2, g.val.2) = x := g.src_val
  have ht : (g.val.1.1 • g.val.1.2, g.val.2) = x := g.tgt_val
  have h1 : g.val.1.2 = x.1 := congrArg Prod.fst hs
  refine ⟨h1, congrArg Prod.snd hs, ?_⟩
  rw [← h1]
  exact (congrArg Prod.fst ht).trans h1.symm

/-- The isotropy group of `(x, e)` in `(G ⋉ ℝⁿ) × H` is the stabilizer of `x`. -/
def isotropyEquiv (x : (Fin n → ℝ) × HObj) :
    (XP G n).Isotropy x ≃ MulAction.stabilizer G x.1 where
  toFun g := ⟨g.val.1.1, (isotropy_val g).2.2⟩
  invFun h := ⟨((h.1, x.1), x.2), rfl, by
    change ((h.1 : G) • x.1, x.2) = x
    rw [h.2]⟩
  left_inv := fun (g : (XP G n).Isotropy x) => by
    obtain ⟨h1, h2, -⟩ := isotropy_val g
    refine GroupoidStr.Isotropy.ext ?_
    change ((g.val.1.1, x.1), x.2) = g.val
    exact Prod.ext (Prod.ext rfl h1.symm) h2.symm
  right_inv h := rfl

variable (G) in
/-- **`♯G_{(x, e)} = ♯Stab_G(x)`.** -/
theorem card_isotropy (x : (Fin n → ℝ) × HObj) :
    Nat.card ((XP G n).Isotropy x) = Nat.card (MulAction.stabilizer G x.1) :=
  Nat.card_congr (isotropyEquiv x)

/-! ### Effectiveness, (ZHOU), paracompactness -/

variable [FaithfulSMul G (Fin n → ℝ)]

/-- **`(G ⋉ ℝⁿ) × H` is effective** (Definition 7.2.1): near `((g, x), e)`, `g ≠ 1`, there are
`((g, x + t w), e)`, `t ≠ 0`, with `g • w ≠ w`, and these move their source. -/
theorem isEffective_XP : (XP G n).IsEffective := by
  intro x g hg W hW hgW
  obtain ⟨h2, he, ht⟩ := isotropy_val g
  have h1 : g.val.1.1 ≠ 1 := fun h => hg (GroupoidStr.Isotropy.ext
    (show g.val = ((1, x.1), x.2) from Prod.ext (Prod.ext h h2) he))
  obtain ⟨w, hw⟩ := exists_smul_ne (n := n) h1
  have hc : Continuous fun t : ℝ => ((g.val.1.1, x.1 + t • w), x.2) :=
    (continuous_const.prodMk (continuous_const.add (continuous_id.smul continuous_const))).prodMk
      continuous_const
  have hS : IsOpen ((fun t : ℝ => ((g.val.1.1, x.1 + t • w), x.2)) ⁻¹' W) := hW.preimage hc
  have h0S : (0 : ℝ) ∈ (fun t : ℝ => ((g.val.1.1, x.1 + t • w), x.2)) ⁻¹' W := by
    change ((g.val.1.1, x.1 + (0 : ℝ) • w), x.2) ∈ W
    rw [zero_smul, add_zero]
    have hg0 : g.val = ((g.val.1.1, x.1), x.2) := Prod.ext (Prod.ext rfl h2) he
    rw [← hg0]
    exact hgW
  have hN : (fun t : ℝ => ((g.val.1.1, x.1 + t • w), x.2)) ⁻¹' W ∈ 𝓝[≠] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (hS.mem_nhds h0S)
  obtain ⟨t, htW, ht0⟩ := Filter.nonempty_of_mem (inter_mem hN self_mem_nhdsWithin)
  refine ⟨((g.val.1.1, x.1 + t • w), x.2), htW, ?_⟩
  intro h
  have h' : x.1 + t • w = g.val.1.1 • (x.1 + t • w) := congrArg Prod.fst h
  rw [smul_add, ht, smul_comm] at h'
  exact hw (smul_right_injective _ (ht0 : t ≠ 0) (add_left_cancel h').symm)

/-- The inclusion `ℝⁿ → ℝⁿ × H`, `x ↦ (x, e)`, at a smooth point `e`, as an sc-smooth functor
`G ⋉ ℝⁿ → (G ⋉ ℝⁿ) × H`. -/
def inclFunctorP {e : HObj} (he : e ∈ PH.smoothSet) : EpFunctor (XG G n) (XP G n) where
  obj z := (z, e)
  mor φ := (φ, e)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj :=
    IsScSmoothOn.prodMk (isScSmoothMap_id (P := (XG G n).PObj)) (MPolyfold.isScSmoothMap_const he)
  isScSmoothMap_mor :=
    IsScSmoothOn.prodMk (isScSmoothMap_id (P := (XG G n).PMor)) (MPolyfold.isScSmoothMap_const he)

theorem isotropy_eq_one {x : (Fin n → ℝ) × HObj} (g : (XP G n).Isotropy x) (h : g.val.1.1 = 1) :
    g = 1 := by
  obtain ⟨h1, h2, -⟩ := isotropy_val g
  refine GroupoidStr.Isotropy.ext ?_
  change g.val = ((1, x.1), x.2)
  exact Prod.ext (Prod.ext h h1) h2

/-- **(ZHOU) for `(G ⋉ ℝⁿ) × H`** (2021 Definition 7.4.5, p. 331): an isotropy element acting as
the identity on `T_{(x, e)}(ℝⁿ × H)` acts as the identity on `T_xℝⁿ` (naturality of the tangent
of a morphism under `x ↦ (x, e)` and `(x, e) ↦ x`), hence is the unit by (ZHOU) for `G ⋉ ℝⁿ`. -/
theorem isZhou_XP : (XP G n).IsZhou := by
  intro y g hg
  have hxs0 : (XP G n).PObj.smoothVal y ∈ (XP G n).PObj.smoothSet :=
    (XP G n).PObj.smoothVal_mem y
  generalize hx : (XP G n).PObj.smoothVal y = x at g hxs0
  have hxs : x ∈ (XP G n).PObj.smoothSet := hxs0
  have hes : x.2 ∈ PH.smoothSet := (MPolyfold.mem_smoothSet_prod.1 hxs).2
  obtain ⟨h1, h2, h3⟩ := isotropy_val g
  have hzs : x.1 ∈ (rnPolyfold n).smoothSet := by
    rw [rnPolyfold_smoothSet]; exact mem_univ _
  let y5 : (rnPolyfold n).SmoothLevel := (rnPolyfold n).smoothMk x.1 hzs
  have hy5 : (rnPolyfold n).smoothVal y5 = x.1 := (rnPolyfold n).smoothVal_smoothMk x.1 hzs
  let g5 : (XG G n).Isotropy ((rnPolyfold n).smoothVal y5) :=
    ⟨g.val.1, h1.trans hy5.symm, by
      change g.val.1.1 • g.val.1.2 = _
      rw [h1, h3, hy5]⟩
  have h5 := isZhou_XG (G := G) (n := n) y5 g5 fun v hv => by
    let F := inclFunctorP (G := G) (n := n) hes
    have hv' : (rnPolyfold n).tangentProj v = (rnPolyfold n).smoothIncl y5 1 := hv
    have hvz : (rnPolyfold n).levelVal 1 ((rnPolyfold n).tangentProj v) = x.1 := by
      rw [hv']; exact hy5
    have hφ1 : g.val.1 ∈ (XG G n).PMor.levelSet 1 :=
      ((XG G n).mem_levelSet_src_iff _ 1).1 (mem_iInter.1 (by
        rw [rnPolyfold_smoothSet]; exact mem_univ _ :
          (XG G n).src g.val.1 ∈ (rnPolyfold n).smoothSet) 1)
    have ha : (XG G n).PObj.levelVal 1 ((XG G n).PObj.tangentProj v) = (XG G n).src g.val.1 :=
      hvz.trans h1.symm
    have nat := F.tangentMor_mor hφ1 ha
    have hmor : F.mor g.val.1 = g.val := Prod.ext rfl h2.symm
    rw [hmor] at nat
    have hfib : F.tangent.obj v ∈
        (XP G n).PObj.tangentFiber ((XP G n).PObj.smoothIncl y 1) := by
      change (XP G n).PObj.tangentProj (MPolyfold.tangentMap F.isScSmoothMap_obj v) = _
      refine level_ext ?_
      rw [levelVal_tangentProj_tangentMap]
      exact (Prod.ext hvz rfl : (_, x.2) = x).trans hx.symm
    have e1 : MPolyfold.tangentMap F.isScSmoothMap_obj v =
        MPolyfold.tangentMap F.isScSmoothMap_obj ((XG G n).tangentMor g.val.1 v) :=
      (hg _ hfib).symm.trans nat
    have hfst := MPolyfold.isScSmoothMap_fst (XG G n).PObj (EpGroupoid.trivial PH).PObj
    have hc := MPolyfold.tangentMap_comp hfst F.isScSmoothMap_obj
    have hid : MPolyfold.tangentMap (hfst.comp F.isScSmoothMap_obj) = id :=
      MPolyfold.tangentMap_id (P := (XG G n).PObj)
    have e2 := congrArg (MPolyfold.tangentMap hfst) e1
    have k1 := congrFun hc v
    have k2 := congrFun hc ((XG G n).tangentMor g.val.1 v)
    rw [hid] at k1 k2
    change (XG G n).tangentMor g.val.1 v = v
    exact k2.trans (e2.symm.trans k1.symm)
  rw [trivialSubgroup_XG] at h5
  have h5' : g5 = 1 := Subgroup.mem_bot.1 h5
  have h6 : g.val.1.1 = 1 := congrArg (fun a : (XG G n).Isotropy _ => a.val.1) h5'
  rw [isotropy_eq_one g h6]
  exact Subgroup.one_mem _

omit [FaithfulSMul G (Fin n → ℝ)] in
/-- `|(G ⋉ ℝⁿ) × H|` is paracompact. -/
theorem hasParacompactOrbitSpace_XP : (XP G n).HasParacompactOrbitSpace := by
  have : SecondCountableTopology (H 0) := secondCountableTopology_level_zero
  exact (XP G n).remark_7_5_2

instance instParacompactPullbackP :
    ParacompactSpace (pullbackSpace (AP σ).P (AP σ).X.src) :=
  (AP σ).B.paracompactSpace_pullback (AP σ).X.PMor _

/-- The bundle has the local regularity property (Propositions 7.4.22 and 8.4.3). -/
theorem isLRLocal_EP : (AP σ).E.IsLRLocal :=
  EpStrongBundle.proposition_8_4_3_isLRLocal (AP σ).E isEffective_XP
    ((XP G n).proposition_7_4_22_of_isZhou isZhou_XP)

/-! ### The structure -/

/-- **The strong polyfold bundle structure** over `(G ⋉ ℝⁿ) × H` (Definition 16.3.1). -/
def prStructure : StrongPolyfoldBundleStructure (AP σ).E.projFunctor.orbitMap where
  A := AP σ
  isZhou := isZhou_XP
  paracompact := hasParacompactOrbitSpace_XP
  isLRLocal := isLRLocal_EP σ
  Γ := Homeomorph.refl _
  γ := Homeomorph.refl _
  comm := rfl

/-- **The strong polyfold bundle over `(ℝⁿ × H)/G`** (Definition 16.3.4). -/
def prBundle : StrongPolyfoldBundle (AP σ).E.projFunctor.orbitMap := ⟦prStructure σ⟧

/-! ### Tameness, the boundary, bump functions -/

omit [FaithfulSMul G (Fin n → ℝ)] in
/-- **`ℝⁿ × H` is tame.** -/
theorem isTame_AP : (AP σ).X.PObj.IsTame :=
  EpGroupoid.isTame_prod (XG G n) (EpGroupoid.trivial PH) rnPolyfold_isTame isTame_PH

omit [FaithfulSMul G (Fin n → ℝ)] in
/-- **`ℝⁿ × H` has no boundary**: the degeneracy index vanishes. -/
theorem degIndex_AP (x : (Fin n → ℝ) × HObj) : (AP σ).X.PObj.degIndex x = 0 := by
  have h := EpGroupoid.degIndex_prod (XG G n) (EpGroupoid.trivial PH) rnPolyfold_isTame
    isTame_PH x.1 x.2
  have h1 : (rnPolyfold n).degIndex x.1 = 0 := MPolyfold.degIndex_rn x.1
  have h2 : PH.degIndex x.2 = 0 := degIndex_PH x.2
  have h3 : (XG G n).PObj.degIndex x.1 + (EpGroupoid.trivial PH).PObj.degIndex x.2 = 0 := by
    rw [show (XG G n).PObj.degIndex x.1 = 0 from h1,
      show (EpGroupoid.trivial PH).PObj.degIndex x.2 = 0 from h2]
  exact h.trans h3

/-- **`(ℝⁿ × H)/G` has no boundary.** -/
theorem prBundle_boundary_eq_empty : (prBundle σ).polyfold.boundary = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨x, rfl⟩ := (prStructure σ).surjective_γπ z
  have hx := (mem_boundary_iff_obj (c := prBundle σ) rfl x).1 hz
  have h : (0 : ℕ) < (AP σ).X.PObj.degIndex x := hx
  have h0' : (AP σ).X.PObj.degIndex x = 0 := degIndex_AP σ x
  omega

/-- `ℝⁿ × ℓ²` (with the maximum norm) has a `C^∞` bump function:
`(a, x) ↦ τ(1 − |a|² − |x|²)`. -/
theorem hasContDiffBump_prodP : HasContDiffBump ((Fin n → ℝ) × L2) ⊤ := by
  refine ⟨fun p => Real.smoothTransition (1 - ∑ i, p.1 i ^ 2 - inner ℝ p.2 p.2), ?_,
    fun h => ?_, ?_⟩
  · refine (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const.sub ?_).sub ?_)
    · exact ContDiff.sum fun i _ => ((contDiff_apply ℝ ℝ i).comp contDiff_fst).pow 2
    · exact contDiff_snd.inner ℝ contDiff_snd
  · have h1 := congrFun h (0 : (Fin n → ℝ) × L2)
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, inner_zero_left] at h1
    norm_num at h1
  · refine (Metric.isBounded_closedBall (x := (0 : (Fin n → ℝ) × L2)) (r := 1)).subset
      fun p hp => ?_
    have hpos : 0 < 1 - ∑ i, p.1 i ^ 2 - inner ℝ p.2 p.2 := by
      by_contra hle
      exact hp (Real.smoothTransition.zero_of_nonpos (not_lt.1 hle))
    rw [real_inner_self_eq_norm_sq] at hpos
    have hs : ∀ i, p.1 i ^ 2 ≤ ∑ j, p.1 j ^ 2 := fun i =>
      Finset.single_le_sum (f := fun j => p.1 j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    have hsum : 0 ≤ ∑ j, p.1 j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
    refine ⟨?_, ?_⟩
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      refine abs_le_one_iff_mul_self_le_one.2 ?_
      nlinarith [hs i, sq_nonneg ‖p.2‖]
    · have : ‖p.2‖ ^ 2 ≤ 1 := by nlinarith
      nlinarith [norm_nonneg p.2]

omit [FaithfulSMul G (Fin n → ℝ)] in
/-- **`ℝⁿ × H` admits sc-smooth bump functions** (Definition 5.5.2). -/
theorem admitsBumpFunctions_AP : (AP σ).X.PObj.AdmitsBumpFunctions := by
  have hP : (AP σ).X.PObj = (rnPolyfold n).prod PH := rfl
  rw [hP]
  refine MPolyfold.admitsBumpFunctions_of_hasContDiffBump fun x => ?_
  exact ⟨(rnChart n 0).prod (retractChart relOpen_H.isScRetract h0),
    MPolyfold.IsChart.prod (isChart_rnChart 0) (isChart_retractChart relOpen_H.isScRetract h0),
    ⟨mem_univ _, mem_univ _⟩, hasContDiffBump_prodP⟩

omit [FaithfulSMul G (Fin n → ℝ)] in
/-- `AP σ` has sc⁺-sections through every smooth fibre point (Lemma 5.3.3). -/
theorem hasScPlusSectionsThrough_AP : (AP σ).B.HasScPlusSectionsThrough :=
  MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough (admitsBumpFunctions_AP σ)

end Polyfold.Examples.Classical.Product
