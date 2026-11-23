import Polyfold.Examples.OrbifoldSquareInfBundle
import Polyfold.Examples.OrbifoldSquareStructure
import Polyfold.Chapter10.EquivalenceZhou
import Polyfold.Chapter6.IntervalEndInclusion
import Polyfold.Chapter6.DegIndexLevelZero
import Polyfold.Chapter5.SobolevRemarkAbstract
import Polyfold.Chapter5.IndexLocallyConstantLocal

/-!
# The orbifold `(ℂ × H)/ℤ₅`: the polyfold and the strong polyfold bundle

The infinite-dimensional version of the worked example `ℂ/ℤ₅`, `z ↦ z²`, for Hofer–Wysocki–Zehnder,
*Polyfold and Fredholm Theory* (Springer 2021), Theorem 16.6.6, 2021 p. 739.

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquareInf`)

* `π_eq_π_iff`, `isRegular_Xinf_iff`, `card_isotropy_of_ne_zero`: orbits and isotropy of
  `(ℤ/5 ⋉ ℂ) × H`.
* `isEffective_Xinf` (Definition 7.2.1), `isZhou_Xinf` (Definition 7.4.5),
  `hasParacompactOrbitSpace_Xinf`, `isLRLocal_Einf` (Definition 8.4.2).
* `infStructure`, `infBundle`: the strong polyfold bundle structure and the strong polyfold bundle
  over `(ℂ × H)/ℤ₅` (Definitions 16.3.1, 16.3.4).
* `isTame_Ainf`, `degIndex_Ainf`, `infBundle_boundary_eq_empty`: `ℂ × H` is tame without
  boundary, `∂Z = ∅`.
* `admitsBumpFunctions_Ainf` (Definition 5.5.2), `hasScPlusSectionsThrough_Ainf`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold.Examples.OrbifoldSquareInf

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure WeightedEllTwo OrbifoldSquare SBLocalization

instance instParacompactMorInf : ParacompactSpace ((G5 × (Fin 2 → ℝ)) × HObj) :=
  inferInstanceAs (ParacompactSpace (A5.Mor × AH.Mor))

/-- **The ep-groupoid `(ℤ/5 ⋉ ℂ) × H`** (the base of `Ainf`, with its object and morphism
types spelled out). -/
abbrev Xinf : EpGroupoid ((Fin 2 → ℝ) × HObj) ((G5 × (Fin 2 → ℝ)) × HObj) :=
  X5.prod (EpGroupoid.trivial PH)

theorem Ainf_X : Ainf.X = Xinf := rfl

/-! ### Orbits and isotropy -/

theorem trivial_π_eq_π_iff {a b : HObj} :
    (EpGroupoid.trivial PH).π a = (EpGroupoid.trivial PH).π b ↔ a = b := by
  rw [GroupoidStr.π_eq_π_iff]
  constructor
  · rintro ⟨φ, hs, ht⟩
    exact hs.symm.trans ht
  · rintro rfl
    exact ⟨a, rfl, rfl⟩

/-- Two points of `ℂ × H` are in one orbit iff their `H`-components agree and the
`ℂ`-components differ by a fifth root of unity. -/
theorem π_eq_π_iff {x y : (Fin 2 → ℝ) × HObj} :
    Xinf.π x = Xinf.π y ↔ ∃ g : G5, g • x.1 = y.1 ∧ x.2 = y.2 := by
  rw [EpGroupoid.prod_π_eq_π_iff]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨g, hg⟩ := (action_π_eq_π_iff isScSmoothMap_smul).1 h1
    exact ⟨g, hg, trivial_π_eq_π_iff.1 h2⟩
  · rintro ⟨g, hg, h2⟩
    exact ⟨(action_π_eq_π_iff isScSmoothMap_smul).2 ⟨g, hg⟩, trivial_π_eq_π_iff.2 h2⟩

/-- The components of an isotropy element of `(z, e)`: it is `((k, z), e)` with `k · z = z`. -/
theorem isotropy_val {x : (Fin 2 → ℝ) × HObj} (g : Xinf.Isotropy x) :
    g.val.1.2 = x.1 ∧ g.val.2 = x.2 ∧ g.val.1.1 • x.1 = x.1 := by
  have hs : (g.val.1.2, g.val.2) = x := g.src_val
  have ht : (g.val.1.1 • g.val.1.2, g.val.2) = x := g.tgt_val
  have h1 : g.val.1.2 = x.1 := congrArg Prod.fst hs
  refine ⟨h1, congrArg Prod.snd hs, ?_⟩
  rw [← h1]
  exact (congrArg Prod.fst ht).trans h1.symm

theorem isotropy_eq_one {x : (Fin 2 → ℝ) × HObj} (g : Xinf.Isotropy x) (h : g.val.1.1 = 1) : g = 1 := by
  obtain ⟨h1, h2, -⟩ := isotropy_val g
  refine GroupoidStr.Isotropy.ext ?_
  change g.val = ((1, x.1), x.2)
  exact Prod.ext (Prod.ext h h1) h2

/-- An object `(z, e)` has trivial isotropy iff `z ≠ 0`. -/
theorem isRegular_Xinf_iff {x : (Fin 2 → ℝ) × HObj} : Xinf.IsRegular x ↔ x.1 ≠ 0 := by
  constructor
  · intro h h0
    let g : Xinf.Isotropy x :=
      ⟨((Multiplicative.ofAdd 1, x.1), x.2), rfl, by
        change ((Multiplicative.ofAdd (1 : ZMod 5) : G5) • x.1, x.2) = x
        rw [h0, smul_zero5, ← h0]⟩
    have h1 : g.val.1.1 = (1 : Xinf.Isotropy x).val.1.1 := by rw [h g]
    have h2 : (Multiplicative.ofAdd (1 : ZMod 5) : G5) = 1 := h1
    exact absurd h2 (by decide)
  · intro hx g
    refine isotropy_eq_one g ?_
    by_contra hk
    exact hx ((smul_eq_self_iff hk x.1).1 (isotropy_val g).2.2)

theorem card_isotropy_of_ne_zero {x : (Fin 2 → ℝ) × HObj} (hx : x.1 ≠ 0) :
    Nat.card (Xinf.Isotropy x) = 1 := by
  have h := isRegular_Xinf_iff.2 hx
  exact Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩

/-! ### Effectiveness, (ZHOU), paracompactness -/

/-- **`(ℤ/5 ⋉ ℂ) × H` is effective** (Definition 7.2.1): the points with trivial isotropy,
`z ≠ 0`, are dense. -/
theorem isEffective_Xinf : Xinf.IsEffective := by
  refine Xinf.isEffective_of_dense_regularSet ?_
  have hd : Dense (({0}ᶜ : Set (Fin 2 → ℝ)) ×ˢ (univ : Set HObj)) :=
    (dense_compl_singleton (0 : Fin 2 → ℝ)).prod dense_univ
  refine hd.mono ?_
  rintro x ⟨hx, -⟩
  exact isRegular_Xinf_iff.2 hx

/-- The inclusion `ℂ → ℂ × H`, `z ↦ (z, e)`, at a smooth point `e`, as an sc-smooth functor
`ℤ/5 ⋉ ℂ → (ℤ/5 ⋉ ℂ) × H`. -/
def inclFunctor {e : HObj} (he : e ∈ PH.smoothSet) : EpFunctor X5 Xinf where
  obj z := (z, e)
  mor φ := (φ, e)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj :=
    IsScSmoothOn.prodMk (isScSmoothMap_id (P := X5.PObj)) (MPolyfold.isScSmoothMap_const he)
  isScSmoothMap_mor :=
    IsScSmoothOn.prodMk (isScSmoothMap_id (P := X5.PMor)) (MPolyfold.isScSmoothMap_const he)

/-- **(ZHOU) for `(ℤ/5 ⋉ ℂ) × H`** (2021 Definition 7.4.5, p. 331): an isotropy element acting as
the identity on `T_{(z, e)}(ℂ × H)` acts as the identity on `T_z ℂ` (naturality of the tangent
of a morphism under `z ↦ (z, e)` and `(z, e) ↦ z`), hence is the unit by (ZHOU) for `ℤ/5 ⋉ ℂ`. -/
theorem isZhou_Xinf : Xinf.IsZhou := by
  intro y g hg
  have hxs0 : Xinf.PObj.smoothVal y ∈ Xinf.PObj.smoothSet := Xinf.PObj.smoothVal_mem y
  generalize hx : Xinf.PObj.smoothVal y = x at g hxs0
  have hxs : x ∈ Xinf.PObj.smoothSet := hxs0
  have hes : x.2 ∈ PH.smoothSet := (MPolyfold.mem_smoothSet_prod.1 hxs).2
  obtain ⟨h1, h2, h3⟩ := isotropy_val g
  have hzs : x.1 ∈ (rnPolyfold 2).smoothSet := by
    rw [rnPolyfold_smoothSet]; exact mem_univ _
  let y5 : (rnPolyfold 2).SmoothLevel := (rnPolyfold 2).smoothMk x.1 hzs
  have hy5 : (rnPolyfold 2).smoothVal y5 = x.1 := (rnPolyfold 2).smoothVal_smoothMk x.1 hzs
  let g5 : X5.Isotropy ((rnPolyfold 2).smoothVal y5) :=
    ⟨g.val.1, h1.trans hy5.symm, by
      change g.val.1.1 • g.val.1.2 = _
      rw [h1, h3, hy5]⟩
  have h5 := isZhou_X5 y5 g5 fun v hv => by
    let F := inclFunctor hes
    have hv' : (rnPolyfold 2).tangentProj v = (rnPolyfold 2).smoothIncl y5 1 := hv
    have hvz : (rnPolyfold 2).levelVal 1 ((rnPolyfold 2).tangentProj v) = x.1 := by
      rw [hv']; exact hy5
    have hφ1 : g.val.1 ∈ X5.PMor.levelSet 1 :=
      (X5.mem_levelSet_src_iff _ 1).1 (mem_iInter.1 (by
        rw [rnPolyfold_smoothSet]; exact mem_univ _ : X5.src g.val.1 ∈ (rnPolyfold 2).smoothSet) 1)
    have ha : X5.PObj.levelVal 1 (X5.PObj.tangentProj v) = X5.src g.val.1 := hvz.trans h1.symm
    have nat := F.tangentMor_mor hφ1 ha
    have hmor : F.mor g.val.1 = g.val := Prod.ext rfl h2.symm
    rw [hmor] at nat
    have hfib : F.tangent.obj v ∈
        Xinf.PObj.tangentFiber (Xinf.PObj.smoothIncl y 1) := by
      change Xinf.PObj.tangentProj (MPolyfold.tangentMap F.isScSmoothMap_obj v) = _
      refine level_ext ?_
      rw [levelVal_tangentProj_tangentMap]
      exact (Prod.ext hvz rfl : (_, x.2) = x).trans hx.symm
    have e1 : MPolyfold.tangentMap F.isScSmoothMap_obj v =
        MPolyfold.tangentMap F.isScSmoothMap_obj (X5.tangentMor g.val.1 v) :=
      (hg _ hfib).symm.trans nat
    have hfst := MPolyfold.isScSmoothMap_fst X5.PObj (EpGroupoid.trivial PH).PObj
    have hc := MPolyfold.tangentMap_comp hfst F.isScSmoothMap_obj
    have hid : MPolyfold.tangentMap (hfst.comp F.isScSmoothMap_obj) = id :=
      MPolyfold.tangentMap_id (P := X5.PObj)
    have e2 := congrArg (MPolyfold.tangentMap hfst) e1
    have k1 := congrFun hc v
    have k2 := congrFun hc (X5.tangentMor g.val.1 v)
    rw [hid] at k1 k2
    change X5.tangentMor g.val.1 v = v
    exact k2.trans (e2.symm.trans k1.symm)
  rw [trivialSubgroup_X5] at h5
  have h5' : g5 = 1 := Subgroup.mem_bot.1 h5
  have h6 : g.val.1.1 = 1 := congrArg (fun a : X5.Isotropy _ => a.val.1) h5'
  rw [isotropy_eq_one g h6]
  exact Subgroup.one_mem _

/-- `|(ℤ/5 ⋉ ℂ) × H|` is paracompact. -/
theorem hasParacompactOrbitSpace_Xinf : Xinf.HasParacompactOrbitSpace := by
  have : SecondCountableTopology (H 0) := secondCountableTopology_level_zero
  exact Xinf.remark_7_5_2

instance instParacompactPullbackInf : ParacompactSpace (pullbackSpace Ainf.P Ainf.X.src) :=
  Ainf.B.paracompactSpace_pullback Ainf.X.PMor _

/-- The bundle has the local regularity property (Propositions 7.4.22 and 8.4.3). -/
theorem isLRLocal_Einf : Ainf.E.IsLRLocal :=
  EpStrongBundle.proposition_8_4_3_isLRLocal Ainf.E isEffective_Xinf
    (Xinf.proposition_7_4_22_of_isZhou isZhou_Xinf)

/-! ### The structure -/

/-- **The strong polyfold bundle structure** over `(ℤ/5 ⋉ ℂ) × H` (Definition 16.3.1). -/
def infStructure : StrongPolyfoldBundleStructure Ainf.E.projFunctor.orbitMap where
  A := Ainf
  isZhou := isZhou_Xinf
  paracompact := hasParacompactOrbitSpace_Xinf
  isLRLocal := isLRLocal_Einf
  Γ := Homeomorph.refl _
  γ := Homeomorph.refl _
  comm := rfl

/-- **The strong polyfold bundle over `(ℂ × H)/ℤ₅`** (Definition 16.3.4). -/
def infBundle : StrongPolyfoldBundle Ainf.E.projFunctor.orbitMap := ⟦infStructure⟧

/-- `(ℤ/5 ⋉ ℂ) × H` is effective (the statement for the base of `Ainf`). -/
theorem isEffective_Ainf : Ainf.X.IsEffective := isEffective_Xinf

/-- (ZHOU) for the base of `Ainf`. -/
theorem isZhou_Ainf : Ainf.X.IsZhou := isZhou_Xinf

/-! ### Tameness and the boundary -/

/-- The chart of `H` is modelled on a tame retract. -/
theorem isTameRetract_H : IsTameRetract H (univ : Set (H 0)) univ :=
  ⟨ScRetraction.id relOpen_H, image_id _, ScRetraction.id_isTame relOpen_H⟩

/-- **`H` is tame.** -/
theorem isTame_PH : PH.IsTame :=
  PH.isTame_of_forall_exists_chart fun x =>
    ⟨retractChart relOpen_H.isScRetract h0, isChart_retractChart relOpen_H.isScRetract h0,
      mem_univ x, isTameRetract_H⟩

/-- `H` has no boundary: `d_H = 0`. -/
theorem degIndex_PH (x : HObj) : PH.degIndex x = 0 :=
  Nat.le_zero.1 ((PH.degIndex_le (isChart_retractChart relOpen_H.isScRetract h0)
    (mem_univ x)).trans (le_of_eq (Polyfold.degIndex_univ H _)))

/-- **`ℂ × H` is tame.** -/
theorem isTame_Ainf : Ainf.X.PObj.IsTame :=
  EpGroupoid.isTame_prod X5 (EpGroupoid.trivial PH) rnPolyfold_isTame isTame_PH

/-- **`ℂ × H` has no boundary**: the degeneracy index vanishes. -/
theorem degIndex_Ainf (x : (Fin 2 → ℝ) × HObj) : Ainf.X.PObj.degIndex x = 0 := by
  have h := EpGroupoid.degIndex_prod X5 (EpGroupoid.trivial PH) rnPolyfold_isTame isTame_PH
    x.1 x.2
  have h1 : (rnPolyfold 2).degIndex x.1 = 0 := MPolyfold.degIndex_rn x.1
  have h2 : PH.degIndex x.2 = 0 := degIndex_PH x.2
  have h3 : X5.PObj.degIndex x.1 + (EpGroupoid.trivial PH).PObj.degIndex x.2 = 0 := by
    rw [show X5.PObj.degIndex x.1 = 0 from h1,
      show (EpGroupoid.trivial PH).PObj.degIndex x.2 = 0 from h2]
  exact h.trans h3

/-- **`(ℂ × H)/ℤ₅` has no boundary.** -/
theorem infBundle_boundary_eq_empty : infBundle.polyfold.boundary = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨x, rfl⟩ := infStructure.surjective_γπ z
  have hx := (mem_boundary_iff_obj (c := infBundle) rfl x).1 hz
  have h : (0 : ℕ) < Ainf.X.PObj.degIndex x := hx
  have h0' : Ainf.X.PObj.degIndex x = 0 := degIndex_Ainf x
  omega

/-! ### Bump functions -/

/-- `ℂ × ℓ²` (with the maximum norm) has a `C^∞` bump function:
`(a, x) ↦ τ(1 − |a|² − |x|²)`. -/
theorem hasContDiffBump_prod : HasContDiffBump ((Fin 2 → ℝ) × L2) ⊤ := by
  refine ⟨fun p => Real.smoothTransition (1 - (p.1 0 ^ 2 + p.1 1 ^ 2) - inner ℝ p.2 p.2),
    ?_, fun h => ?_, ?_⟩
  · refine (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const.sub ?_).sub ?_)
    · exact (((contDiff_apply ℝ ℝ (0 : Fin 2)).comp contDiff_fst).pow 2).add
        (((contDiff_apply ℝ ℝ (1 : Fin 2)).comp contDiff_fst).pow 2)
    · exact contDiff_snd.inner ℝ contDiff_snd
  · have h1 := congrFun h (0 : (Fin 2 → ℝ) × L2)
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, inner_zero_left] at h1
    norm_num at h1
  · refine (Metric.isBounded_closedBall (x := (0 : (Fin 2 → ℝ) × L2)) (r := 1)).subset
      fun p hp => ?_
    have hpos : 0 < 1 - (p.1 0 ^ 2 + p.1 1 ^ 2) - inner ℝ p.2 p.2 := by
      by_contra hle
      exact hp (Real.smoothTransition.zero_of_nonpos (not_lt.1 hle))
    rw [real_inner_self_eq_norm_sq] at hpos
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
    refine ⟨?_, ?_⟩
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      refine abs_le_one_iff_mul_self_le_one.2 ?_
      fin_cases i
      · change p.1 0 * p.1 0 ≤ 1
        nlinarith [sq_nonneg (p.1 1), sq_nonneg ‖p.2‖]
      · change p.1 1 * p.1 1 ≤ 1
        nlinarith [sq_nonneg (p.1 0), sq_nonneg ‖p.2‖]
    · have : ‖p.2‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (p.1 0), sq_nonneg (p.1 1)]
      nlinarith [norm_nonneg p.2]

/-- **`ℂ × H` admits sc-smooth bump functions** (Definition 5.5.2; level `0` of the model of a
product chart is `ℂ × ℓ²`). -/
theorem admitsBumpFunctions_Ainf : Ainf.X.PObj.AdmitsBumpFunctions := by
  have hP : Ainf.X.PObj = (rnPolyfold 2).prod PH := rfl
  rw [hP]
  refine MPolyfold.admitsBumpFunctions_of_hasContDiffBump fun x => ?_
  exact ⟨(rnChart 2 0).prod (retractChart relOpen_H.isScRetract h0),
    MPolyfold.IsChart.prod (isChart_rnChart 0) (isChart_retractChart relOpen_H.isScRetract h0),
    ⟨mem_univ _, mem_univ _⟩, hasContDiffBump_prod⟩

/-- `Ainf` has sc⁺-sections through every smooth fibre point (Lemma 5.3.3). -/
theorem hasScPlusSectionsThrough_Ainf : Ainf.B.HasScPlusSectionsThrough :=
  MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough admitsBumpFunctions_Ainf

end Polyfold.Examples.OrbifoldSquareInf
