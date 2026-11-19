import Polyfold.Chapter9.DimensionJumpIntegral
import Polyfold.Chapter9.DimensionZeroIntegral
import Polyfold.Chapter11.BoundaryMeasureEquivalenceDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.5,
**Remark 9.5.20** (pp. 451–452; 2017: Remark 9.8), point G.110: the boundary integral of
`Θ(t, z) = δ₀(z)` read in the ep-groupoid `∂X`.

# `∮_{∂Θ̂} f` in `∂X` is `φ(1) − φ(−1)`

## The text, paraphrased
(p. 452) `∂X = {(−1, 0), (1, 0)}` is a smooth submanifold and a sub-ep-groupoid of `ℤ/3 ⋉ X`;
`G^eff_x = ℤ/3` for `x ∈ ∂X` read in `X`, but `G^eff_x = {1}` read in `∂X`.  With the weights of
`X` the boundary integral of `f(t, z) = φ(t)` over `∂Θ̂` is `(1/3)(φ(1) − φ(−1))`, consistent with
Stokes' theorem; read in `∂X` it is `φ(1) − φ(−1)`.

## What is formalized
* `ABd`: the ep-groupoid `∂X` (`DimensionJump.εB`) as an object of `EP`; its two points `bm = (−1, 0)`,
  `b₀ = (1, 0)` are isolated and smooth for the induced structure; `isLUC_εB`: `∂X` has the local
  unique continuation property; `tangentMor_εB`: the tangent maps of its morphisms are the
  identity (`s = t` on the morphisms of `∂X`).
* `thetaB = ∂Θ` on `∂X` (`thetaB_eq`: `= 1` at both points, `boundaryTheta_xm`,
  `boundaryTheta_x₀`), with the orientation `TB` of sign `+` at `(1, 0)` and `−` at `(−1, 0)`;
  `frameSign_oB`: these are the signs of the boundary orientation of `M = [−1, 1] × {0}`.
  **`isBranchedEpSubgroupoid_thetaB`**, `isCompactBranched_thetaB`, **`isOrientation_thetaB`**,
  **`isTameOfDimZero_thetaB`** (Definitions 9.1.2, 9.1.6, 9.3.2, 9.3.6 for `n = 0`).
* `restrictB a`: the `0`-form `a|∂X`, the pull-back along the inclusion `∂X → X`.
* **`remark_9_5_20_boundary_in_boundary`**: the `0`-dimensional effective branched integral of
  `∂Θ̂` in `∂X` (`EP.branchedIntegralEffDimZero`, weights `1/♯G^eff = 1`) is
  `a(1, 0) − a(−1, 0)`; `remark_9_5_20_boundary_in_boundary_noneff`: the non-effective one
  (weights `1/♯G = 1/3`) is `(1/3)(a(1, 0) − a(−1, 0))`.
* **`remark_9_5_20_two_readings`**: for every `φ` smooth near `[−1, 1]` and `f(t, z) = φ(t)`:
  `∮_Θ̂ df = ∮_{∂Θ̂} f = (1/3)(φ(1) − φ(−1))` with the weights of `X`, and `φ(1) − φ(−1)` for the
  integral in `∂X`; **`remark_9_5_20_two_readings_ne`**: for `φ(t) = 2 cos θ − 2 sin θ` the values
  are `−4/3` and `−4`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory
open scoped ContDiff Real

noncomputable section

namespace Polyfold

namespace DimensionJump

open DimensionJump
open ScOneExample hiding E

open RemarkFourThree MPolyfold EpGroupoid EpGroupoid.Examples

/-! ### The ep-groupoid `∂X` -/

/-- **The ep-groupoid `∂X`** (the full subcategory of `ℤ/3 ⋉ X` on `∂X`) as an object of `EP`. -/
abbrev ABd : EP.{0} := EP.mk P.boundary (ε.morOn P.boundary) εB

lemma boundary_eq_pair : P.boundary = {xm, x₀} := by
  ext y
  rw [mem_boundary_iff']
  simp only [mem_insert_iff, mem_singleton_iff]

lemma finite_boundary : P.boundary.Finite := by
  rw [boundary_eq_pair]
  exact (finite_singleton _).insert _

instance : Finite P.boundary := finite_boundary.to_subtype

/-- The point `(−1, 0)` of `∂X`. -/
def bm : P.boundary := ⟨xm, xm_mem_boundary⟩

/-- The point `(1, 0)` of `∂X`. -/
def b₀ : P.boundary := ⟨x₀, x₀_mem_boundary⟩

lemma boundary_cases (a : P.boundary) : a = bm ∨ a = b₀ := by
  rcases (mem_boundary_iff' a.1).1 a.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

lemma bm_ne_b₀ : bm ≠ b₀ := fun h => by
  have := congrArg (fun a : P.boundary => a.1.1.1) h
  simp only [bm, b₀, xm, x₀] at this
  norm_num at this

/-- The points of `∂X` are isolated. -/
lemma isOpen_singleton_boundary (a : P.boundary) : IsOpen ({a} : Set P.boundary) :=
  isOpen_discrete _

/-- **Every point of `∂X` is smooth for the induced structure** (Proposition 4.2.3 (1), `∂X` being
a smooth submanifold). -/
lemma mem_smoothSet_εB (a : P.boundary) : a ∈ εB.PObj.smoothSet :=
  isSmoothSubmanifold_boundary.proposition_4_2_3_one.2 a

/-- `s = t` on the morphisms of `∂X` (every `k ∈ ℤ/3` fixes the points of `∂X`). -/
lemma src_eq_tgt_εB : εB.src = εB.tgt := funext fun φ => Subtype.ext (by
  change φ.1.2 = φ.1.1 • φ.1.2
  exact (smul_eq_self_of_snd_eq_zero φ.1.1 (snd_eq_zero_of_mem_boundary φ.2.1)).symm)

/-- **The tangent maps of the morphisms of `∂X` are the identity.** -/
lemma tangentMor_εB (φ : ε.morOn P.boundary) : εB.tangentMor φ = id := by
  funext h
  unfold EpGroupoid.tangentMor
  split_ifs with hv
  · have key : ∀ {f g : ε.morOn P.boundary → P.boundary}
        (hf : εB.PMor.IsScSmoothMap εB.PObj f) (hg : εB.PMor.IsScSmoothMap εB.PObj g),
        f = g → ∀ v, MPolyfold.tangentMap hf v = MPolyfold.tangentMap hg v := by
      rintro f g hf hg rfl v; rfl
    rw [key εB.isScSmoothMap_tgt εB.isScSmoothMap_src src_eq_tgt_εB.symm, hv.choose_spec.2]
    rfl
  · rfl

lemma grHatPush_εB (φ : ε.morOn P.boundary) (w : εB.PObj.OrTangent →₀ ℚ) :
    εB.grHatPush φ w = w := by
  rw [grHatPush, tangentMor_εB]
  rw [show (OrTangent.push id : εB.PObj.OrTangent → εB.PObj.OrTangent) = id from
    funext OrTangent.push_id]
  exact Finsupp.mapDomain_id

/-- **`∂X` has the local unique continuation property** (Definition 7.2.18): on `U(x) = {x}`
every `ĝ` is the identity. -/
theorem isLUC_εB : εB.IsLUC := fun a =>
  ⟨εB.isolatedRep a (isOpen_singleton_boundary a), isolatedRep_hasLUC _⟩

/-! ### `∂Θ` in `∂X` and its orientation -/

/-- **`∂Θ` read in the ep-groupoid `∂X`.** -/
def thetaB (a : P.boundary) : ℚ := ε.boundaryTheta thetaM a.1

lemma thetaB_eq (a : P.boundary) : thetaB a = 1 := by
  rcases boundary_cases a with rfl | rfl
  exacts [boundaryTheta_xm, boundaryTheta_x₀]

lemma thetaB_pos (a : P.boundary) : 0 < thetaB a := by rw [thetaB_eq]; norm_num

lemma supp_thetaB : supp thetaB = univ :=
  eq_univ_of_forall thetaB_pos

/-- The orientation of the point `{a}` of `∂X`: `+` at `(1, 0)`, `−` at `(−1, 0)`. -/
def oB (a : P.boundary) : εB.PObj.SubmanifoldOrientation {a} 0 :=
  pointOrientation (mem_smoothSet_εB a) (decide (a = b₀))

/-- **The orientation `T̂(∂Θ)` in `∂X`**: `T(a) = ∂Θ(a) · T_a({a}, ±)`. -/
def TB (a : P.boundary) : εB.PObj.OrTangent →₀ ℚ :=
  Finsupp.single ((oB a).tangent a) (thetaB a)

/-- The oriented tame structure of dimension `0` at `a ∈ ∂X`. -/
def CB (a : P.boundary) : εB.OrientedTameStructure 0 thetaB a :=
  isolatedStructure (isOpen_singleton_boundary a) (mem_smoothSet_εB a) (thetaB_pos a) (oB a)

lemma CB_represents (a : P.boundary) : (CB a).Represents TB :=
  isolatedStructure_represents _ _ _ _ rfl

lemma frameSign_oB_b₀ : frameSign (X := εB) ((oB b₀).tangent b₀) = 1 := by
  rw [oB, frameSign_pointOrientation]
  simp

lemma frameSign_oB_bm : frameSign (X := εB) ((oB bm).tangent bm) = -1 := by
  rw [oB, frameSign_pointOrientation]
  simp [bm_ne_b₀]

/-- **The orientation of `∂Θ` in `∂X` is the boundary orientation of `M`**: at both points of
`∂X` its sign is that of the boundary orientation of `(M, o)` in `X`
(`frames_boundaryOp_x₀`, `frames_boundaryOp_xm`). -/
theorem frameSign_oB (a : P.boundary) :
    frameSign (X := εB) ((oB a).tangent a) =
      frameSign (X := ε) (P.boundaryOp (oM.tangent a.1)) := by
  rcases boundary_cases a with rfl | rfl
  · rw [frameSign_oB_bm]
    exact (if_neg frames_boundaryOp_xm).symm
  · rw [frameSign_oB_b₀]
    exact (if_pos frames_boundaryOp_x₀).symm

lemma isCompact_orbitSupp_thetaB : IsCompact (εB.orbitSupp thetaB) := by
  unfold orbitSupp
  exact ((toFinite _).image _).isCompact

/-- **`∂Θ` is a branched ep⁺-subgroupoid of `∂X`** (Definition 9.1.2). -/
theorem isBranchedEpSubgroupoid_thetaB : εB.IsBranchedEpSubgroupoid thetaB where
  nonneg a := (thetaB_pos a).le
  isFunctorial φ := by rw [thetaB_eq, thetaB_eq]
  support_subset a _ := mem_smoothSet_εB a
  paracompactSpace_orbitSupp := by
    have := isCompact_iff_compactSpace.1 isCompact_orbitSupp_thetaB
    infer_instance
  localBranching a _ := ⟨(CB a).toLocalBranchingStructure⟩

/-- **`∂Θ` is compact** (Definition 9.1.6 (2)). -/
theorem isCompactBranched_thetaB : εB.IsCompactBranched thetaB := isCompact_orbitSupp_thetaB

/-- **`T̂` is an orientation of `∂Θ`** (Definition 9.3.2). -/
theorem isOrientation_thetaB : εB.IsOrientation thetaB TB := by
  refine IsOrientation.mk' (hasIndependentTangentSums_of_subset_goodSet fun a ha =>
      (mem_goodSet_iff isBranchedEpSubgroupoid_thetaB).2
        ⟨ha, univ, univ_mem, fun z _ _ => by rw [thetaB_eq, thetaB_eq]⟩)
    (fun a _ => ?_) (fun φ _ => ?_) (fun a _ ha => absurd (supp_thetaB ▸ mem_univ a) ha)
    fun a _ => ⟨(CB a).toOriented, fun y hy hys => CB_represents a y hy hys⟩
  · rw [CB_represents a a (CB a).mem_U (mem_smoothSet_εB a)]
    exact OrientedBranchingStructure.orientedSum_mem _ a
  · rw [grHatPush_εB, congrFun src_eq_tgt_εB φ]

/-- **`∂Θ̂` is tame of dimension `0`** (Definition 9.3.6 for `n = 0`). -/
theorem isTameOfDimZero_thetaB : εB.IsTameOfDimZero thetaB TB := fun a _ =>
  ⟨CB a, isolatedStructure_mem_pointSheets _ _ _ _, CB_represents a⟩

/-! ### The integrals over `∂Θ̂` in `∂X` -/

/-- **The `0`-form `a|∂X`**: the pull-back of `a ∈ Ω⁰_{ep,∞}(X)` along the inclusion `∂X → X`. -/
def restrictB (a : AX.epFormsInfty 0) : ABd.epFormsInfty 0 :=
  EP.epFormsInftyPullback (A := ABd) (B := AX) (subEpFunctor isEpSubgroupoid_boundary) 0 a

lemma zeroFormEval_restrictB (a : AX.epFormsInfty 0) (b : P.boundary) :
    ABd.zeroFormEval (restrictB a) b = AX.zeroFormEval a b.1 :=
  EP.zeroFormEval_epFormsInftyPullback (A := ABd) (B := AX) (subEpFunctor isEpSubgroupoid_boundary)
    a (mem_smoothSet_εB b) (mem_smoothSet_of_snd_eq_zero (snd_eq_zero_of_mem_boundary b.2))

/-- The part of `|supp ∂Θ|` over the orbit of `b`. -/
def KB (b : P.boundary) : Set (ABd.X.orbitSupp thetaB) := Subtype.val ⁻¹' (ABd.X.π '' {b})

lemma measurableSet_KB (b : P.boundary) :
    MeasurableSet[ABd.X.lebesgueSigma (SheetNullSets.point (pointSheets ABd.X)) thetaB] (KB b) :=
  borel_le_borelNullSigma _ _ (MeasurableSpace.measurableSet_generateFrom
    ((proposition_7_1_8 εB _ (isOpen_singleton_boundary b)).preimage continuous_subtype_val))

lemma KB_subset (b : P.boundary) : Subtype.val '' KB b ⊆ ABd.X.π '' (CB b).U := by
  rw [show (CB b).U = {b} from isolatedStructure_U _ _ _ _]
  exact image_preimage_subset _ _

lemma π_mem_KB (b : P.boundary) : ABd.X.π b ∈ Subtype.val '' KB b :=
  ⟨⟨ABd.X.π b, b, by rw [supp_thetaB]; exact mem_univ b, rfl⟩, ⟨b, rfl, rfl⟩, rfl⟩

lemma disjoint_KB : Disjoint (KB bm) (KB b₀) := by
  refine Set.disjoint_left.2 fun q h1 h2 => ?_
  obtain ⟨y, hy, hyq⟩ := h1
  obtain ⟨y', hy', hyq'⟩ := h2
  rw [mem_singleton_iff.1 hy] at hyq
  rw [mem_singleton_iff.1 hy'] at hyq'
  obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff (G := εB.toGroupoidStr)).1 (hyq.trans hyq'.symm)
  have h := congrFun src_eq_tgt_εB φ
  rw [hs] at h
  exact bm_ne_b₀ (h.trans ht)

lemma KB_union : KB bm ∪ KB b₀ = univ := by
  refine eq_univ_of_forall fun q => ?_
  obtain ⟨y, -, hy⟩ := q.2
  rcases boundary_cases y with rfl | rfl
  · exact Or.inl ⟨bm, rfl, hy⟩
  · exact Or.inr ⟨b₀, rfl, hy⟩

/-- A signed measure on `|supp ∂Θ|` is the sum of its values on the two orbits. -/
lemma signedMeasure_univ_KB
    (Φ : @SignedMeasure (ABd.X.orbitSupp thetaB)
      (ABd.X.lebesgueSigma (SheetNullSets.point (pointSheets ABd.X)) thetaB)) :
    Φ univ = Φ (KB bm) + Φ (KB b₀) := by
  let _ : MeasurableSpace (ABd.X.orbitSupp thetaB) :=
    ABd.X.lebesgueSigma (SheetNullSets.point (pointSheets ABd.X)) thetaB
  rw [← KB_union]
  exact VectorMeasure.of_union disjoint_KB (measurableSet_KB bm) (measurableSet_KB b₀)

/-- **Remark 9.5.20 (p. 452), `∮_{∂Θ̂} a` read in `∂X`**: the `0`-dimensional effective branched
integral of `∂Θ̂` in the ep-groupoid `∂X` (Definition 9.5.6 (2) for `n = 0`, weights
`1/♯G^eff_x = 1` of `∂X`) of `a|∂X` is `a(1, 0) − a(−1, 0)`. -/
theorem remark_9_5_20_boundary_in_boundary (a : AX.epFormsInfty 0) :
    ABd.branchedIntegralEffDimZero isLUC_εB isBranchedEpSubgroupoid_thetaB
        isCompactBranched_thetaB isOrientation_thetaB isTameOfDimZero_thetaB (restrictB a) =
      AX.zeroFormEval a x₀ - AX.zeroFormEval a xm := by
  have hloc := isTameOfDimZero_thetaB
  have h : ∀ b : P.boundary, branchedMeasureEff ABd.zeroFormIntegration
      isBranchedEpSubgroupoid_thetaB isCompactBranched_thetaB isOrientation_thetaB
      (hloc.hasLUC isLUC_εB) (restrictB a) (KB b) =
        frameSign (X := εB) ((oB b).tangent b) * AX.zeroFormEval a b.1 := fun b => by
    rw [EP.branchedMeasureEffDimZero_apply ABd isLUC_εB isBranchedEpSubgroupoid_thetaB
      isCompactBranched_thetaB isOrientation_thetaB hloc (restrictB a) (CB b)
      (isolatedStructure_mem_pointSheets _ _ _ _) (CB_represents b) (measurableSet_KB b)
      (KB_subset b)]
    rw [CB, EP.isolatedStructure_localMeasureEff _ _ _ _ _ (π_mem_KB b), card_effIsotropy_εB,
      thetaB_eq, zeroFormEval_restrictB]
    push_cast
    ring
  change branchedMeasureEff ABd.zeroFormIntegration isBranchedEpSubgroupoid_thetaB
    isCompactBranched_thetaB isOrientation_thetaB (hloc.hasLUC isLUC_εB) (restrictB a) univ = _
  rw [signedMeasure_univ_KB, h, h, frameSign_oB_bm, frameSign_oB_b₀]
  change -1 * AX.zeroFormEval a xm + 1 * AX.zeroFormEval a x₀ = _
  ring

/-- **The non-effective integral of `∂Θ̂` in `∂X`** (Definition 9.5.6 (1) for `n = 0`, weights
`1/♯G_x = 1/3`: the isotropy of `∂X` is still `ℤ/3`) is `(1/3)(a(1, 0) − a(−1, 0))`. -/
theorem remark_9_5_20_boundary_in_boundary_noneff (a : AX.epFormsInfty 0) :
    ABd.branchedIntegralDimZero isBranchedEpSubgroupoid_thetaB isCompactBranched_thetaB
        isOrientation_thetaB isTameOfDimZero_thetaB (restrictB a) =
      (1 / 3 : ℝ) * (AX.zeroFormEval a x₀ - AX.zeroFormEval a xm) := by
  have hloc := isTameOfDimZero_thetaB
  have h : ∀ b : P.boundary, branchedMeasure ABd.zeroFormIntegration
      isBranchedEpSubgroupoid_thetaB isCompactBranched_thetaB isOrientation_thetaB hloc
      (restrictB a) (KB b) =
        (1 / 3 : ℝ) * (frameSign (X := εB) ((oB b).tangent b) * AX.zeroFormEval a b.1) :=
    fun b => by
    rw [EP.branchedMeasureDimZero_apply ABd isBranchedEpSubgroupoid_thetaB
      isCompactBranched_thetaB isOrientation_thetaB hloc (restrictB a) (CB b)
      (isolatedStructure_mem_pointSheets _ _ _ _) (CB_represents b) (measurableSet_KB b)
      (KB_subset b)]
    rw [CB, EP.isolatedStructure_localMeasure _ _ _ _ _ (π_mem_KB b), card_isotropy_εB,
      thetaB_eq, zeroFormEval_restrictB]
    push_cast
    ring
  change branchedMeasure ABd.zeroFormIntegration isBranchedEpSubgroupoid_thetaB
    isCompactBranched_thetaB isOrientation_thetaB hloc (restrictB a) univ = _
  rw [signedMeasure_univ_KB, h, h, frameSign_oB_bm, frameSign_oB_b₀]
  change (1 / 3 : ℝ) * (-1 * AX.zeroFormEval a xm) + 1 / 3 * (1 * AX.zeroFormEval a x₀) = _
  ring

/-! ### The two readings for `f(t, z) = φ(t)` -/

/-- **Remark 9.5.20 (p. 452), the two readings of the boundary integral**: for every `φ` smooth
on an open `U ⊇ [−1, 1]` there is a `0`-form `f` with `f(t, z) = φ(t)` at the smooth points such
that `∮_Θ̂ df = ∮_{∂Θ̂} f = (1/3)(φ(1) − φ(−1))` with the weights of `X` (Stokes' theorem), while
the effective integral of `∂Θ̂` in the ep-groupoid `∂X` gives `φ(1) − φ(−1)`. -/
theorem remark_9_5_20_two_readings {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hIU : Icc (-1 : ℝ) 1 ⊆ U) (hφ : ContDiffOn ℝ ∞ φ U) :
    ∃ f : AX.epFormsInfty 0, (∀ y ∈ AX.X.PObj.smoothSet, AX.zeroFormEval f y = φ y.1.1) ∧
      (AX.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0)
          isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM isOrientation_thetaM m_hloc_LUC
          (AX.epFormsInftyD 0 f) = (1 / 3 : ℝ) * (φ 1 - φ (-1)) ∧
      AX.boundaryBranchedMeasureEffDim1 isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM
          isOrientation_thetaM m_hloc_LUC f univ = (1 / 3 : ℝ) * (φ 1 - φ (-1)) ∧
      ABd.branchedIntegralEffDimZero isLUC_εB isBranchedEpSubgroupoid_thetaB
          isCompactBranched_thetaB isOrientation_thetaB isTameOfDimZero_thetaB (restrictB f) =
        φ 1 - φ (-1) := by
  obtain ⟨ψ, hψ, hf, hdf⟩ := remark_9_5_20_df_of_contDiffOn hU hIU hφ
  have h0 := hf x₀ (mem_smoothSet_of_snd_eq_zero x₀_mem_M)
  have h1 := hf xm (mem_smoothSet_of_snd_eq_zero xm_mem_M)
  refine ⟨fForm hψ, hf, hdf, ?_, ?_⟩
  · rw [remark_9_5_20_boundary, h0, h1]; rfl
  · rw [remark_9_5_20_boundary_in_boundary, h0, h1]; rfl

/-- **The two readings differ** (Remark 9.5.20, p. 452): for `φ(t) = 2 cos θ − 2 sin θ`
(`θ = π(1 + t)/4`, `φ(1) − φ(−1) = −4`), `∮_Θ̂ df = ∮_{∂Θ̂} f = −4/3` with the weights of `X`, while
the effective integral of `∂Θ̂` in `∂X` is `−4`. -/
theorem remark_9_5_20_two_readings_ne :
    (AX.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0)
        isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM isOrientation_thetaM m_hloc_LUC
        (AX.epFormsInftyD 0 (fForm contDiff_id)) = -4 / 3 ∧
      AX.boundaryBranchedMeasureEffDim1 isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM
        isOrientation_thetaM m_hloc_LUC (fForm contDiff_id) univ = -4 / 3 ∧
      ABd.branchedIntegralEffDimZero isLUC_εB isBranchedEpSubgroupoid_thetaB
        isCompactBranched_thetaB isOrientation_thetaB isTameOfDimZero_thetaB
        (restrictB (fForm contDiff_id)) = -4 := by
  obtain ⟨h1, h2, h3⟩ := remark_9_5_20_nondegenerate
  exact ⟨h1, h2, by rw [remark_9_5_20_boundary_in_boundary, h3]⟩

end DimensionJump

end Polyfold
