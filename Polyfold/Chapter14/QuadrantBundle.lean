import Polyfold.Chapter14.HalfSpaceConstSection
import Polyfold.Chapter11.EpEquivalenceGeometryFaces

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 14, §14.6
(pp. 680–682): a strong bundle over an ep-groupoid **with corners**, on which the statements
about faces and their intersections can be tested.

# The trivial bundle over a quadrant as a strong bundle over an ep-groupoid

## What is formalized (namespace `Polyfold.QuadrantBundle`)

* `Q n m = [0, ∞)ⁿ × ℝᵐ` with the M-polyfold structure `quadrantPolyfold n ℝᵐ`, the trivial
  strong bundle `bundle n m k : Q × ℝᵏ → Q` (one chart, the identity strong bundle retraction)
  and `quadSEP n m k`, the bundle over the trivial ep-groupoid of `Q` as an object of `SEP`.
* `isTame_quadSEP`, `hasParacompactOrbitSpace_quadSEP`, `admitsScPartitionsOfUnity_quadSEP`,
  `isTameChart_chart₀` (the one chart is a tame strong bundle chart, with the trivial
  presentation of its partial quadrant, `hT₀`).
* `graphSec φ`: the section `x ↦ (x, φ(x))` of a map `φ : ℝⁿ × ℝᵐ → ℝᵏ`;
  `isScPlusSectionOn_graphSec`: for `φ` of class `C^∞` it is an sc⁺-section, hence sc⁺ on every
  local face (`isFaceScPlusSectionOn_graphSec`).
* `fibAct_quadSEP`, `Φ_eq_self`: over the trivial ep-groupoid the fibre action and the natural
  actions are trivial.
* `continuousOn_snd_comp_of_isFaceScPlusSectionOn`: if `s` satisfies (1) of Definition 14.1.3 on
  `U ⊆ ∂Q`, then along every continuous path in `U` which stays in one coordinate face
  `{xᵢ = 0}` the fibre part of `s` is continuous.
* `isEpFace_subset_coord`: every face of `Q` (Definition 11.1.3) lies in a coordinate face
  `{xᵢ = 0}`; `exists_isEpFace_mem_of_part`: a point with exactly one vanishing coordinate lies
  in a face.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace QuadrantBundle

open SBLocalization StrongBundle EpGroupoid MPolyfold TameBoundaryExample

variable (n m k : ℕ)

/-- The sc-Banach space `ℝⁿ ⊕ ℝᵐ` (constant structure). -/
abbrev ESc : ScBanach := (ScBanach.const (Fin n → ℝ)).prod (rnSc m)

/-- The quadrant `Q = [0, ∞)ⁿ × ℝᵐ ⊆ ℝⁿ ⊕ ℝᵐ`. -/
abbrev Q : Set ((ESc n m) 0) := quadrant n (rnSc m) 0

lemma relOpen_Q : IsRelOpenInQuadrant (ESc n m) (Q n m) (Q n m) :=
  isRelOpenInQuadrant_quadrant n (rnSc m)

/-- **The quadrant as an M-polyfold** (one chart, the inclusion). -/
abbrev basePoly : MPolyfold (Q n m) := quadrantPolyfold n (rnSc m)

/-- The chart of `basePoly`: the inclusion `Q → ℝⁿ ⊕ ℝᵐ`. -/
abbrev baseChart : MChart (Q n m) :=
  (LocalModel.ofRelOpen (relOpen_Q n m)).selfChart (quadrant_nonempty n (rnSc m))

/-- The projection `Q × ℝᵏ → Q`. -/
def proj : Q n m × (Fin k → ℝ) → Q n m := Prod.fst

variable {n m k}

@[simp] lemma proj_apply (y : Q n m × (Fin k → ℝ)) : proj n m k y = y.1 := rfl

lemma bijective_toBase_E (j : ℕ) : Bijective ((ESc n m).toBase j) :=
  bijective_toBase_prod (bijective_toBase_const _) (bijective_toBase_const _) j

lemma baseChart_symm_val {z : (ESc n m) 0} (hz : z ∈ Q n m) :
    (((baseChart n m).symm z : Q n m) : (ESc n m) 0) = z :=
  (baseChart n m).toPartialEquiv.right_inv hz

/-- The fibre `proj⁻¹(x) ≃ ℝᵏ`. -/
def fibEquiv (x : Q n m) : proj n m k ⁻¹' {x} ≃ (Fin k → ℝ) where
  toFun y := y.1.2
  invFun v := ⟨(x, v), rfl⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    simp only [mem_preimage, proj_apply, mem_singleton_iff] at h
    subst h; rfl
  right_inv _ := rfl

instance (x : Q n m) : AddCommGroup (proj n m k ⁻¹' {x}) := (fibEquiv x).addCommGroup

instance (x : Q n m) : Module ℝ (proj n m k ⁻¹' {x}) := (fibEquiv x).module ℝ

lemma isStrongBundleRetraction_id_Q :
    IsStrongBundleRetraction (E := ESc n m) (F := rnSc k) (Q n m) id where
  mapsTo := mapsTo_id _
  fst_independent _ _ _ _ := rfl
  fiber_linear _ _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  preserves_filtration _ _ _ _ _ hu _ hh := ⟨hu, hh⟩
  isScSmooth_zero := isScSmooth_id ((relOpen_Q n m).prod_univ (rnSc k)).isScDomain
  isScSmooth_one := by
    refine (isScSmooth_id ((relOpen_Q n m).prod_univ (rnSc k).shift).isScDomain).congr
      ((relOpen_Q n m).prod_univ (rnSc k).shift).isScDomain fun p _ => ?_
    change p = (p.1, invFun ((rnSc k).toBase 1) ((rnSc k).toBase 1 p.2))
    rw [leftInverse_invFun ((rnSc k).toBase_injective 1)]
  idem _ _ := rfl

/-- **The strong bundle chart** `Q × ℝᵏ → Q ◁ ℝᵏ`, `(x, v) ↦ (x, v)`, with the identity strong
bundle retraction. -/
def chart₀ : StrongBundleChart (basePoly n m) (proj n m k) where
  φ := baseChart n m
  isChart := (basePoly n m).isChart_of_mem (mem_singleton _)
  F := rnSc k
  U := Q n m
  R := id
  relOpen := relOpen_Q n m
  isRetraction := isStrongBundleRetraction_id_Q
  base_retract := image_id _
  toPartialEquiv := (baseChart n m).toPartialEquiv.prod (PartialEquiv.refl (Fin k → ℝ))
  source_eq := by
    change (univ : Set (Q n m)) ×ˢ (univ : Set (Fin k → ℝ)) = proj n m k ⁻¹' univ
    rw [univ_prod_univ, preimage_univ]
  target_eq := by
    change Q n m ×ˢ (univ : Set (Fin k → ℝ)) = id '' (Q n m ×ˢ univ)
    rw [image_id]
  continuousOn_toFun := (baseChart n m).continuousOn_toFun.prodMap continuousOn_id
  continuousOn_invFun := (baseChart n m).continuousOn_invFun.prodMap continuousOn_id
  covers _ _ := rfl
  fiber_linear x _ := ((fibEquiv x).linearEquiv ℝ).toLinearMap.isLinear

@[simp] lemma chart₀_apply (y : Q n m × (Fin k → ℝ)) :
    chart₀ y = (((y.1 : Q n m) : (ESc n m) 0), y.2) := rfl

variable (n m k) in
/-- **The trivial strong bundle** `Q × ℝᵏ → Q` over the quadrant. -/
def bundle : StrongBundle (basePoly n m) (proj n m k) where
  continuous := continuous_fst
  surjective x := ⟨(x, 0), rfl⟩
  banachable x := ⟨Fin k → ℝ, inferInstance, inferInstance, inferInstance,
    ⟨{ toLinearEquiv := (fibEquiv x).linearEquiv ℝ
       continuous_toFun := continuous_snd.comp continuous_subtype_val
       continuous_invFun :=
        (continuous_const.prodMk continuous_id).subtype_mk fun _ => rfl }⟩⟩
  atlas :=
    { charts := {chart₀}
      compatible := by
        rintro _ h _ h'
        rw [mem_singleton_iff.1 h, mem_singleton_iff.1 h']
        exact chart₀.compatible_self
      cover := fun y => ⟨chart₀, mem_singleton _, mem_univ y, mem_univ _⟩ }

lemma isChart_chart₀ : (bundle n m k).IsChart chart₀ :=
  StrongBundle.isChart_of_mem (B := bundle n m k) (mem_singleton _)

/-- `C = T⁻¹(quadrant)` for the trivial presentation `T = 1`. -/
lemma hT₀ : (chart₀ (n := n) (m := m) (k := k)).φ.model.C =
    (ScIso.refl (ESc n m)) 0 ⁻¹' quadrant n (rnSc m) 0 := by
  ext; rfl

/-- The one chart is a tame strong bundle chart (its base retraction is the identity). -/
lemma isTameChart_chart₀ : (bundle n m k).IsTameChart chart₀ :=
  StrongBundle.isTameChart_of_eqOn_id isChart_chart₀ fun _ _ => rfl

variable (n m k)

/-- `𝐗 ₛ×_P W` for the quadrant bundle over the trivial ep-groupoid of `Q` is paracompact. -/
instance instParacompactPullback :
    ParacompactSpace (pullbackSpace (proj n m k) (EpGroupoid.trivial (basePoly n m)).src) :=
  (bundle n m k).paracompactSpace_pullback (basePoly n m) _

/-- **The quadrant bundle `Q × ℝᵏ → Q` over the trivial ep-groupoid of `Q`** (Definition 8.3.1).
-/
def epBundle : EpStrongBundle (EpGroupoid.trivial (basePoly n m)) (bundle n m k) :=
  EpStrongBundle.trivial (bundle n m k)

/-- `Q × ℝᵏ → Q = [0, ∞)ⁿ × ℝᵐ` as an object of `SEP` (Definition 10.4.11). -/
def quadSEP : SEP.{0} :=
  ⟨_, _, EpGroupoid.trivial (basePoly n m), _, proj n m k, bundle n m k, epBundle n m k⟩

/-- `Q` is a tame M-polyfold. -/
theorem isTame_quadSEP : (quadSEP n m k).X.IsTame :=
  MPolyfold.quadrantPolyfold_isTame n (rnSc m)

/-- The orbit space of the trivial ep-groupoid is `Q`, which is paracompact. -/
theorem hasParacompactOrbitSpace_quadSEP : (quadSEP n m k).X.HasParacompactOrbitSpace :=
  EpGroupoid.hasParacompactOrbitSpace_trivial (basePoly n m)

/-- **`Q` admits sc-smooth partitions of unity** (Theorem 5.5.10 and Proposition 5.5.11: its one
chart has a finite-dimensional model). -/
theorem admitsScPartitionsOfUnity_quadSEP :
    (quadSEP n m k).X.PObj.AdmitsScPartitionsOfUnity := by
  change (basePoly n m).AdmitsScPartitionsOfUnity
  refine theorem_5_5_10.2 ⟨{baseChart n m}, ?_,
    fun x => ⟨baseChart n m, mem_singleton _, mem_univ x⟩, ?_⟩
  · rintro _ rfl
    exact (basePoly n m).isChart_of_mem (mem_singleton _)
  · rintro _ rfl
    have : FiniteDimensional ℝ ((baseChart n m).model.E 0) := by
      change FiniteDimensional ℝ ((Fin n → ℝ) × (Fin m → ℝ))
      infer_instance
    exact proposition_5_5_11 _ (admitsContDiffPartitionsOfUnity_of_finiteDimensional _)

variable {n m k}

/-- Over the trivial ep-groupoid the fibre action is trivial. -/
theorem fibAct_quadSEP (φ : (quadSEP n m k).Mor) (w : (quadSEP n m k).W) : fibAct φ w = w := by
  unfold fibAct; split <;> rfl

/-- Over the trivial ep-groupoid the natural actions are trivial. -/
theorem Φ_eq_self {x : (quadSEP n m k).Obj} (V : (quadSEP n m k).X.NatNbhd x)
    (g : (quadSEP n m k).X.Isotropy x) {y : (quadSEP n m k).Obj} (hy : y ∈ V.U) :
    V.rep.Φ g y = y :=
  (V.tgt_Γ g hy).symm.trans (V.src_Γ g hy)

/-! ### Graph sections -/

/-- **The section** `x ↦ (x, φ(x))` of `Q × ℝᵏ → Q`. -/
def graphSec (φ : (ESc n m) 0 → (Fin k → ℝ)) :
    (quadSEP n m k).Obj → (quadSEP n m k).W :=
  fun x : Q n m => ((x, φ x.1) : Q n m × (Fin k → ℝ))

theorem graphSec_snd (φ : (ESc n m) 0 → (Fin k → ℝ)) (x : Q n m) :
    (show Q n m × (Fin k → ℝ) from graphSec φ x).2 = φ x.1 := rfl

@[simp] theorem P_graphSec (φ : (ESc n m) 0 → (Fin k → ℝ)) (x : (quadSEP n m k).Obj) :
    (quadSEP n m k).P (graphSec φ x) = x := rfl

/-- **The graph section of a `C^∞` map is an sc⁺-section** (in the one chart of the atlas its
representative is `u ↦ (u, φ(u))` on `Q`, a `C^∞` map between finite-dimensional spaces). -/
theorem isScPlusSectionOn_graphSec {φ : (ESc n m) 0 → (Fin k → ℝ)} (hφ : ContDiff ℝ ∞ φ) :
    IsScPlusSectionOn (quadSEP n m k) (graphSec φ) univ := by
  have hι : ∀ w : Fin k → ℝ, Function.invFun ((rnSc k).toBase 1) w = w := fun w =>
    leftInverse_invFun ((rnSc k).toBase_injective 1) w
  refine isScPlusSectionOn_of_localRepOne isOpen_univ (fun _ _ => rfl) fun x _ =>
    ⟨chart₀, mem_singleton _, mem_univ _, fun _ _ => (bijective_toBase_const _ 1).2 _, ?_⟩
  set c : StrongBundleChart (quadSEP n m k).X.PObj (quadSEP n m k).P := chart₀ with hcdef
  have himg : c.φ '' (univ ∩ c.φ.source) = Q n m := by
    rw [univ_inter]
    change (baseChart n m).toPartialEquiv '' univ = Q n m
    rw [image_univ]; exact Subtype.range_coe
  rw [himg]
  have hval : ∀ u ∈ Q n m, localRepOne c (graphSec φ) u = (u, φ u) :=
    fun u hu => by
      change ((((baseChart n m).symm u : Q n m) : (ESc n m) 0), Function.invFun
        ((rnSc k).toBase 1) (φ (((baseChart n m).symm u : Q n m) : (ESc n m) 0))) = (u, φ u)
      rw [baseChart_symm_val hu, hι]
  refine (isScSmoothRetractMap_iff_exists (relOpen_Q n m).isScRetract).2
    ⟨fun u hu => ?_, ScRetraction.id (relOpen_Q n m), image_id _, ?_⟩
  · rw [hval u hu]
    exact ⟨(u, (rnSc k).toBase 1 (φ u)), ⟨hu, mem_univ _⟩, rfl⟩
  · refine (isScSmooth_of_bijective_toBase bijective_toBase_E
      (bijective_toBase_prod bijective_toBase_E (bijective_toBase_shift (bijective_toBase_const _)))
      (relOpen_Q n m).isScDomain (f := fun u : (ESc n m) 0 => (u, φ u))
      (contDiff_id.prodMk hφ).contDiffOn).congr (relOpen_Q n m).isScDomain
        fun u hu => ?_
    exact (hval u hu).symm

/-- The graph section of a `C^∞` map satisfies (1) of Definition 14.1.3 on every set. -/
theorem isFaceScPlusSectionOn_graphSec {φ : (ESc n m) 0 → (Fin k → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (U : Set (quadSEP n m k).Obj) : IsFaceScPlusSectionOn (quadSEP n m k) (graphSec φ) U :=
  isFaceScPlusSectionOn_of_isScPlusSectionOn (isScPlusSectionOn_graphSec hφ) U

/-! ### Continuity along the coordinate faces -/

/-- **Sections which are sc⁺ on the local faces are continuous along the coordinate faces**: if
`s` satisfies (1) of Definition 14.1.3 on `U`, and `γ` is a continuous map into `Q` which on `S`
takes values in `U ∩ {xᵢ = 0}`, then the fibre part of `s ∘ γ` is continuous on `S`. -/
theorem continuousOn_snd_comp_of_isFaceScPlusSectionOn
    {s : (quadSEP n m k).Obj → (quadSEP n m k).W} {U : Set (quadSEP n m k).Obj}
    (hs : IsFaceScPlusSectionOn (quadSEP n m k) s U) {α : Type*} [TopologicalSpace α]
    {γ : α → Q n m} (hγ : Continuous γ) {S : Set α} (i : Fin n)
    (hγU : ∀ a ∈ S, γ a ∈ U ∧ coord i (γ a) = 0) :
    ContinuousOn (fun a => (show Q n m × (Fin k → ℝ) from s (γ a)).2) S := by
  have hι : ∀ w : Fin k → ℝ, Function.invFun ((rnSc k).toBase 1) w = w := fun w =>
    leftInverse_invFun ((rnSc k).toBase_injective 1) w
  intro a ha
  set c : StrongBundleChart (quadSEP n m k).X.PObj (quadSEP n m k).P := chart₀ with hcdef
  have hi : i ∈ zeroSet (ScIso.refl (ESc n m)) (c.φ (γ a)) :=
    (mem_zeroSet _).2 (hγU a ha).2
  obtain ⟨V, hV, hxV, hret, hsec⟩ := hs.2 c isTameChart_chart₀ n (rnSc m) (ScIso.refl (ESc n m)) hT₀
    (γ a) ⟨(hγU a ha).1, mem_univ _⟩ i hi
  have hg := hsec.isScSmooth.continuousOn hret
  set h : α → (ESc n m) 0 := fun a => ((γ a : Q n m) : (ESc n m) 0) with hh
  have hhc : Continuous h := continuous_subtype_val.comp hγ
  have hmaps : MapsTo h (S ∩ h ⁻¹' V)
      (c.φ.model.O ∩ V ∩ coordHyper (ScIso.refl (ESc n m)) i) := fun b hb =>
    ⟨⟨(γ b).2, hb.2⟩, (hγU b hb.1).2⟩
  have h1 : ContinuousWithinAt (localRepOne c s ∘ h) (S ∩ h ⁻¹' V) a :=
    (hg (h a) (hmaps ⟨ha, hxV⟩)).comp hhc.continuousWithinAt hmaps
  have h2 : ContinuousWithinAt (fun b => (localRepOne c s (h b)).2) (S ∩ h ⁻¹' V) a :=
    continuous_snd.continuousAt.comp_continuousWithinAt h1
  have hsymm : ∀ b, (baseChart n m).symm (h b) = γ b := fun b =>
    Subtype.ext (baseChart_symm_val (γ b).2)
  have heq : ∀ b, (localRepOne c s (h b)).2 = (show Q n m × (Fin k → ℝ) from s (γ b)).2 :=
    fun b => by
      change Function.invFun ((rnSc k).toBase 1)
        (show Q n m × (Fin k → ℝ) from s ((baseChart n m).symm (h b))).2 = _
      rw [hsymm, hι]
  have h3 : ContinuousWithinAt (fun b => (show Q n m × (Fin k → ℝ) from s (γ b)).2)
      (S ∩ h ⁻¹' V) a := h2.congr (fun b _ => (heq b).symm) (heq a).symm
  exact h3.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin S ((hV.preimage hhc).mem_nhds hxV))

/-! ### The faces of the quadrant -/

/-- **Every face of `Q` lies in a coordinate face** `{xᵢ = 0}` (Definition 11.1.3: a face is the
closure of a connected component of `{d = 1}`, and such a component lies in one stratum
`{xᵢ = 0, x_l > 0 for l ≠ i}`). -/
theorem isEpFace_subset_coord {F : Set (quadSEP n m k).Obj}
    (hF : (quadSEP n m k).X.IsEpFace F) : ∃ i : Fin n, F ⊆ {p : Q n m | coord i p = 0} := by
  obtain ⟨θ, hθ, rfl⟩ := hF
  have h := TameBoundary.exists_isFaceIn_univ_preimage (dS := dq n (rnSc m))
    (EpGroupoid.Examples.isHomeomorph_π_trivial (basePoly n m)) (fun _ => rfl)
    (EpGroupoid.isOrbitFace_iff_isFaceIn.1 hθ)
  obtain ⟨p, -, hp1, hp⟩ := h
  obtain ⟨i, hi⟩ := dq_eq_one_iff.1 hp1
  refine ⟨i, ?_⟩
  change (EpGroupoid.trivial (basePoly n m)).π ⁻¹' θ ⊆ _
  rw [hp]
  exact faceAt_subset_coord_eq_zero univ hi

/-- **A point with exactly one vanishing coordinate `xᵢ` lies in a face**, and that face lies in
`{xᵢ = 0}`. -/
theorem exists_isEpFace_mem_of_part {p : Q n m} {i : Fin n} (hp : p ∈ part i) :
    ∃ F : Set (quadSEP n m k).Obj, (quadSEP n m k).X.IsEpFace F ∧ p ∈ F ∧
      F ⊆ {q : Q n m | coord i q = 0} := by
  have hd : (EpGroupoid.trivial (basePoly n m)).degIndexOrbit
      ((EpGroupoid.trivial (basePoly n m)).π p) = 1 := dq_eq_one_iff.2 ⟨i, hp⟩
  have hF : (quadSEP n m k).X.IsEpFace ((EpGroupoid.trivial (basePoly n m)).faceObj
      (closure (connectedComponentIn {w | (EpGroupoid.trivial (basePoly n m)).degIndexOrbit w = 1}
        ((EpGroupoid.trivial (basePoly n m)).π p)))) := ⟨_, ⟨_, hd, rfl⟩, rfl⟩
  have hpF : p ∈ (EpGroupoid.trivial (basePoly n m)).faceObj
      (closure (connectedComponentIn {w | (EpGroupoid.trivial (basePoly n m)).degIndexOrbit w = 1}
        ((EpGroupoid.trivial (basePoly n m)).π p))) :=
    subset_closure (mem_connectedComponentIn hd)
  refine ⟨_, hF, hpF, ?_⟩
  obtain ⟨j, hj⟩ := isEpFace_subset_coord hF
  have hji : j = i := by
    by_contra hne
    exact (hp.2 j hne).ne' (hj hpF)
  rw [← hji]; exact hj

end QuadrantBundle

end Polyfold
