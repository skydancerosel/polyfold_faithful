import Polyfold.Examples.Classical.Setup
import Polyfold.Chapter16.CircleSectionPolyfold
import Polyfold.Chapter17.BundleModelStructure
import Polyfold.Chapter18.OrientationWitness
import Polyfold.Chapter16.OrientationNonEffectiveWitness
import Polyfold.Chapter16.CircleSectionCobordism
import Polyfold.Chapter16.IndexZeroNoBumpsUnconditional

/-!
# The classical reduction: the polyfold `ℝⁿ/G` and the strong polyfold bundle

Setting for the comparison of Theorem 16.6.6, 2021 p. 739 (index `0`) with the classical count
of a proper equivariant map in finite dimensions.  The group `G` acts effectively:
`[FaithfulSMul G (Fin n → ℝ)]`.  Effectiveness (Definition 7.2.1) and (ZHOU) (Definition 7.4.5)
are what `EpStrongBundle.proposition_8_4_3_isLRLocal` uses for the local regularity of the
bundle (Definition 8.4.2).

## What is formalized (namespace `Polyfold.Examples.Classical`)

* `isEffective_XG` (Definition 7.2.1): near an isotropy morphism `(g, x)`, `g ≠ 1`, there are
  `(g, x + t w)` with `g • (x + t w) ≠ x + t w`.
* `card_isotropy`: `#G_x = #Stab_G(x)`; `trivialSubgroup_XG`: every `T_x` is trivial.
* `isZhou_XG` (Definition 7.4.5): the tangent map of `g •` at `x` is `x ↦ g • x` itself, which
  moves a vector for `g ≠ 1`.
* `isLRLocal_EG` (Definition 8.4.2), `hasParacompactOrbitSpace_XG`.
* `clStructure σ`, `clBundle σ`: the strong polyfold bundle structure and the strong polyfold
  bundle `|ℝⁿ × ℝⁿ| → ℝⁿ/G` (Definitions 16.3.1, 16.3.4).
* `clRep σ hφ heq`, `clFredholmSection σ hφ heq`: the sc-Fredholm section `|x| ↦ |(x, φ x)|`
  of an equivariant `C^∞` map (Definitions 16.3.18, 16.6.1).
* `clBundle_boundary_eq_empty`: `∂Z = ∅`.
* The standing data of Theorem 16.6.6: `mem_smoothSet_AG`, `isTame_AG`,
  `admitsBumpFunctions_AG`, `hasScPlusSectionsThrough_AG`, `isScFredholmSectionTame_fSec`,
  `isIndexAt_fSec` (Fredholm index `0`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  [FaithfulSMul G (Fin n → ℝ)]

/-! ### Isotropy -/

/-- For `g ≠ 1` some vector is moved by `g`. -/
theorem exists_smul_ne {g : G} (hg : g ≠ 1) : ∃ w : Fin n → ℝ, g • w ≠ w := by
  by_contra h
  push Not at h
  exact hg (eq_of_smul_eq_smul fun w => by rw [h w, one_smul])

/-- The group element of an isotropy morphism `≠ 1` is `≠ 1`. -/
theorem fst_ne_one_of_isotropy {x : Fin n → ℝ} (g : (XG G n).Isotropy x) (hg : g ≠ 1) :
    g.val.1 ≠ 1 := fun h =>
  hg (GroupoidStr.Isotropy.ext (Prod.ext h (g.src_val : g.val.2 = x)))

/-- **`G ⋉ ℝⁿ` is effective** (Definition 7.2.1): near `(g, x)`, `g ≠ 1`, there are
`(g, x + t w)`, `t ≠ 0`, with `g • w ≠ w`, and these move their source. -/
theorem isEffective_XG : (XG G n).IsEffective := by
  intro x g hg W hW hgW
  have h2 : g.val.2 = x := g.src_val
  have ht : g.val.1 • g.val.2 = x := g.tgt_val
  rw [h2] at ht
  have h1 := fst_ne_one_of_isotropy g hg
  obtain ⟨w, hw⟩ := exists_smul_ne (n := n) h1
  have hc : Continuous fun t : ℝ => (g.val.1, x + t • w) :=
    continuous_const.prodMk (continuous_const.add (continuous_id.smul continuous_const))
  have hS : IsOpen ((fun t : ℝ => (g.val.1, x + t • w)) ⁻¹' W) := hW.preimage hc
  have h0S : (0 : ℝ) ∈ (fun t : ℝ => (g.val.1, x + t • w)) ⁻¹' W := by
    change (g.val.1, x + (0 : ℝ) • w) ∈ W
    rw [zero_smul, add_zero]
    have hg0 : g.val = (g.val.1, x) := Prod.ext rfl h2
    rw [← hg0]
    exact hgW
  have hN : (fun t : ℝ => (g.val.1, x + t • w)) ⁻¹' W ∈ 𝓝[≠] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (hS.mem_nhds h0S)
  obtain ⟨t, htW, ht0⟩ := Filter.nonempty_of_mem (inter_mem hN self_mem_nhdsWithin)
  refine ⟨(g.val.1, x + t • w), htW, ?_⟩
  change x + t • w ≠ g.val.1 • (x + t • w)
  intro h
  rw [smul_add, ht, smul_comm] at h
  exact hw (smul_right_injective _ (ht0 : t ≠ 0) (add_left_cancel h).symm)

variable (G) in
/-- **`#G_x = #Stab_G(x)`**: the isotropy group of `x` in `G ⋉ ℝⁿ` is the stabilizer. -/
theorem card_isotropy (x : Fin n → ℝ) :
    Nat.card ((XG G n).Isotropy x) = Nat.card (MulAction.stabilizer G x) :=
  Nat.card_congr (isotropyEquivStabilizer (isScSmoothMap_smul (G := G)) x).toEquiv

/-- Every `T_x` is trivial. -/
theorem trivialSubgroup_XG (x : Fin n → ℝ) : (XG G n).trivialSubgroup x = ⊥ :=
  (XG G n).isEffective_iff_trivialSubgroup_eq_bot.1 (isEffective_XG (G := G) (n := n)) x

/-! ### (ZHOU) -/

/-- The vector `(0, w)` of `T_xℝⁿ` in the chart `y ↦ y − x`. -/
def baseVec (x w : Fin n → ℝ) : (rnChart n x).model.E.tangent 0 := ((0 : Fin n → ℝ), w)

theorem baseVec_mem (x w : Fin n → ℝ) :
    baseVec x w ∈ retractTangent (rnChart n x).model.E (rnChart n x).model.C
      (rnChart n x).model.O := by
  change baseVec x w ∈ retractTangent (rnSc n) univ univ
  rw [retractTangent_univ]
  exact mem_univ _

/-- `[x, y ↦ y − x, w] ∈ T_xℝⁿ`. -/
def baseTangent (x w : Fin n → ℝ) : (rnPolyfold n).TangentSpace :=
  TangentSpace.mk (TangentPre.ofVec (isChart_rnChart x) (baseVec_mem x w))

theorem levelVal_tangentProj_baseTangent (x w : Fin n → ℝ) :
    (rnPolyfold n).levelVal 1 ((rnPolyfold n).tangentProj (baseTangent x w)) = x := by
  change (rnChart n x).symm ((rnChart n x).model.E.toBase 1 0) = x
  rw [map_zero]
  exact zero_add x

theorem tangentChartMap_baseTangent (x w : Fin n → ℝ) :
    tangentChartMap (isChart_rnChart x) (baseTangent x w) = baseVec x w :=
  tangentChartMap_mk_ofVec _ (baseVec_mem x w)

/-- For `g • x = x`, `T(g •)` sends `(0, w)` to `(0, g • w)` in the chart `y ↦ y − x`. -/
theorem tangentChartMap_tangentMap_smul {g : G} {x : Fin n → ℝ} (hgx : g • x = x)
    (w : Fin n → ℝ) :
    tangentChartMap (isChart_rnChart x)
        (MPolyfold.tangentMap (isScSmoothMap_smul g) (baseTangent x w)) =
      ((0 : Fin n → ℝ), g • w) := by
  rw [tangentChartMap_tangentMap_of_linear (isScSmoothMap_smul g) (isChart_rnChart x)
    (isChart_rnChart x) (ScOperator.ofConst (rhoL g))
    (fun _ _ => mem_univ _) (fun y _ => ?_) (mem_univ _), tangentChartMap_baseTangent]
  · refine Prod.ext ?_ rfl
    change rhoL g (0 : Fin n → ℝ) = 0
    exact map_zero _
  · change g • y - x = rhoL g (y - x)
    rw [rhoL_apply, smul_sub, hgx]

/-- **(ZHOU) for `G ⋉ ℝⁿ`** (2021 Definition 7.4.5, p. 331): an isotropy `g ≠ 1` of `x`
moves a tangent vector of `T_xℝⁿ` (its tangent map is the linear map `g •`). -/
theorem isZhou_XG : (XG G n).IsZhou := by
  intro y g hg
  rw [trivialSubgroup_XG (G := G) (n := n), Subgroup.mem_bot]
  by_contra hne
  set x := (rnPolyfold n).smoothVal y with hxdef
  have h2 : g.val.2 = x := g.src_val
  have ht : g.val.1 • g.val.2 = x := g.tgt_val
  rw [h2] at ht
  have h1 := fst_ne_one_of_isotropy g hne
  obtain ⟨w, hw⟩ := exists_smul_ne (n := n) h1
  have hv : baseTangent x w ∈
      (rnPolyfold n).tangentFiber ((rnPolyfold n).smoothIncl y 1) := by
    change (rnPolyfold n).tangentProj (baseTangent x w) = _
    refine level_ext ?_
    exact levelVal_tangentProj_baseTangent x w
  have e1 := hg (baseTangent x w) hv
  have hval : g.val = (g.val.1, (rnPolyfold n).levelVal 1
      ((rnPolyfold n).tangentProj (baseTangent x w))) :=
    Prod.ext rfl (h2.trans (levelVal_tangentProj_baseTangent x w).symm)
  rw [hval] at e1
  replace e1 : MPolyfold.tangentMap (isScSmoothMap_smul g.val.1) (baseTangent x w) =
      baseTangent x w :=
    (tangentMor_actionEpGroupoid isScSmoothMap_smul
      (φ := (g.val.1, (rnPolyfold n).levelVal 1 ((rnPolyfold n).tangentProj (baseTangent x w))))
      (((XG G n).mem_levelSet_src_iff _ 1).1 (MPolyfold.levelVal_mem _))
      (α := baseTangent x w) rfl).symm.trans e1
  have h4 := congrArg (tangentChartMap (isChart_rnChart x)) e1
  rw [tangentChartMap_tangentMap_smul ht, tangentChartMap_baseTangent] at h4
  exact hw (congrArg Prod.snd h4)

/-! ### The structure -/

/-- `|G ⋉ ℝⁿ| = ℝⁿ/G` is paracompact. -/
theorem hasParacompactOrbitSpace_XG : (XG G n).HasParacompactOrbitSpace :=
  hasParacompactOrbitSpace_action isScSmoothMap_smul

variable (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))

/-- The bundle has the local regularity property (Propositions 7.4.22 and 8.4.3); this uses
effectiveness and (ZHOU), hence `[FaithfulSMul G (Fin n → ℝ)]`. -/
theorem isLRLocal_EG : (EG σ).IsLRLocal :=
  EpStrongBundle.proposition_8_4_3_isLRLocal (EG σ) isEffective_XG
    ((XG G n).proposition_7_4_22_of_isZhou isZhou_XG)

/-- **The strong polyfold bundle structure** `((P : ℝⁿ × ℝⁿ → ℝⁿ, μ), id, id)` over `G ⋉ ℝⁿ`
(Definition 16.3.1), for `p = |P|`. -/
def clStructure : StrongPolyfoldBundleStructure (AG σ).E.projFunctor.orbitMap where
  A := AG σ
  isZhou := isZhou_XG
  paracompact := hasParacompactOrbitSpace_XG
  isLRLocal := isLRLocal_EG σ
  Γ := Homeomorph.refl _
  γ := Homeomorph.refl _
  comm := rfl

/-- **The strong polyfold bundle `|ℝⁿ × ℝⁿ| → ℝⁿ/G`** (Definition 16.3.4). -/
def clBundle : StrongPolyfoldBundle (AG σ).E.projFunctor.orbitMap := ⟦clStructure σ⟧

variable {σ}

/-- `|f|` is well defined on `ℝⁿ/G`. -/
theorem π_fSec_eq {φ : (Fin n → ℝ) → (Fin n → ℝ)} (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    {x y : Fin n → ℝ} (h : (XG G n).π x = (XG G n).π y) :
    (AG σ).E.toEpGroupoid.π (fSec φ x) = (AG σ).E.toEpGroupoid.π (fSec φ y) := by
  obtain ⟨k, rfl⟩ := (action_π_eq_π_iff isScSmoothMap_smul).1 h
  refine (GroupoidStr.π_eq_π_iff _).2 ⟨⟨((k, x), fSec φ x), rfl⟩, rfl, ?_⟩
  exact (fSec_smul heq k x).symm

variable (σ) in
/-- **The representative `(clStructure σ, f)`** of the section `|x| ↦ |(x, φ x)|`
(Definition 16.3.18). -/
def clRep {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) : SectionRep (clBundle σ) where
  S := clStructure σ
  hS := rfl
  F := fSec φ
  hF := (isScFredholmSectionFunctor_fSec hφ heq).1
  f := Quotient.lift (fun x : Fin n → ℝ => (AG σ).E.toEpGroupoid.π (fSec φ x))
    fun _ _ h => π_fSec_eq heq (Quotient.sound h)
  continuous_f := Continuous.quotient_lift ((AG σ).E.toEpGroupoid.continuous_π.comp
    (continuous_id.prodMk hφ.continuous)) _
  isSection z := Quotient.inductionOn z fun _ => rfl
  comm _ := rfl

variable (σ) in
/-- **The sc-Fredholm section `|x| ↦ |(x, φ x)|`** of `clBundle σ` (Definition 16.6.1). -/
def clFredholmSection {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) : FredholmSection (clBundle σ) :=
  ⟨⟦clRep σ hφ heq⟧, clRep σ hφ heq, rfl, isScFredholmSectionFunctor_fSec hφ heq⟩

variable (σ) in
/-- **`ℝⁿ/G` has no boundary.** -/
theorem clBundle_boundary_eq_empty : (clBundle σ).polyfold.boundary = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨x, rfl⟩ := (clStructure σ).surjective_γπ z
  have hx := (mem_boundary_iff_obj (c := clBundle σ) rfl x).1 hz
  have h : (0 : ℕ) < (rnPolyfold n).degIndex x := hx
  have h0 : (rnPolyfold n).degIndex x = 0 := MPolyfold.degIndex_rn x
  omega

/-! ### The standing data of Theorem 16.6.6 -/

variable (σ) in
theorem mem_smoothSet_AG (x : (AG σ).Obj) : x ∈ (AG σ).X.PObj.smoothSet := by
  have h : (rnPolyfold n).smoothSet = univ := rnPolyfold_smoothSet
  exact h ▸ mem_univ x

variable (σ) in
theorem isTame_AG : (AG σ).X.PObj.IsTame := rnPolyfold_isTame

variable (σ) in
theorem admitsBumpFunctions_AG : (AG σ).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_rn n

variable (σ) in
theorem hasScPlusSectionsThrough_AG : (AG σ).B.HasScPlusSectionsThrough :=
  hasScPlusSectionsThrough_epSEP n n

variable (σ) in
/-- `f` has tame germ data (Definition 3.6.4). -/
theorem isScFredholmSectionTame_fSec {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ) :
    (AG σ).B.IsScFredholmSectionTame (fSec φ) :=
  isScFredholmSectionTame_graphSection hφ

variable (σ) in
/-- **The Fredholm index of `f` is `0`** at every point. -/
theorem isIndexAt_fSec {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ) (x : (AG σ).Obj) :
    (AG σ).B.IsIndexAt (fSec φ) x 0 := by
  have h := isIndexAt_graphSection_epSEP (n := n) (k := n) hφ x
  have h0 : ((n : ℕ) : ℤ) - ((n : ℕ) : ℤ) = 0 := by omega
  rw [h0] at h
  exact h

end Polyfold.Examples.Classical
