import Polyfold.Chapter15.KernelChartChange

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4, p. 701,
**Theorem 15.4.1** (2017: Theorem 15.6): the canonical lift does not depend on the local
sc⁺-section structure.

# The formula of Theorem 15.4.1 does not depend on the local structure

## The text, paraphrased

(p. 701) "This definition does not depend on the choice of the local sc⁺-section structure since
the occurring operators are independent of such choices": the formal sum
`∑_{i : f(y) = sᵢ(y)} σᵢ · (f − sᵢ)'(y)` is the same for every local sc⁺-section structure
(Theorem 15.1.1), and the orientation of each summand is induced by `o_y`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `linOrTangent`: the oriented tangent set `(ker L, o(L))` of an onto member `L` of `Lin(f, y)`,
  in a chart point; `KernelBranching.orTangent_eq_linOrTangent` (for `L = (f − sᵢ)'(y)` it is
  `(T_yMᵢ, o_{i,y})`, in any chart with domain in `O`).
* `linW_chartPtOf_eq`: the formal sums of operators of two local sc⁺-section structures of `Λ`
  agree in the chart points of Part I (Theorem 15.1.1 through `linSumChart_eq`).
* `KernelBranching.canonSum_apply_eq`: the formula of Theorem 15.4.1 in `Ĝr(y)` is the image of
  the formal sum of operators under `L ↦ (ker L, o(L))`.
* **`canonIndependent`**: `CanonIndependent`, the independence of the local structure, holds:
  two structures described by kernels give the same sum `∑ σᵢ · (T_yMᵢ, o_{i,y})` at every
  common smooth point.
* **`theorem_15_4_1_of_natural_continuous`**: Theorem 15.4.1 in `Ĝr(X)` from the naturality and
  the continuity of the formula; `IsCanonicalFor.loc` (the oriented tame structures that
  Theorem 15.4.3 uses), **`IsCanonicalFor.unique`** (the canonical orientation is unique), and
  `IsCanonicalPerturbation`, the predicate `Can` of Corollary 15.4.4.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W} {y : A.Obj}

/-! ### The oriented kernel of an onto member of `Lin(f, y)` -/

open Classical in
/-- **`(ker L, o(L))` as an oriented tangent set of Chapter 9**, for an onto `L ∈ Lin(f, y)` in the
chart point `p`: the tangent vectors over `y` with chart vector in `ker L`, with the frames
positive for the orientation induced by `o` (`orKerOrientation`). -/
def linOrTangent (hf : A.B.IsScFredholmSection f) (p : ChartPoint A.B y) (o : p.Or f hf)
    (L : p.linSet f) : A.X.PObj.OrTangent :=
  if h : Surjective (L.1 : ↥p.T →L[ℝ] ↥p.K) then
    haveI := p.finiteDimensional_of_mem_linSet hf L.2 rfl
    ⟨finrank ℝ ↥((LinearMap.ker ((L.1 : ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K)).map
        (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)),
      {α | A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y ∧ chartVec p.c.isChart α ∈
        (LinearMap.ker ((L.1 : ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K)).map
          (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)},
      chartFrames p.c.isChart
        {α | A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y ∧ chartVec p.c.isChart α ∈
          (LinearMap.ker ((L.1 : ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K)).map
            (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)} _
        (p.orKerOrientation o L.2 h rfl rfl)⟩
  else ⟨0, ∅, ∅⟩

/-- Two descriptions of the same oriented kernel: with the dimension `n` and the set `T`, or with
`finrank` and a set `T' = T`. -/
theorem orTangent_mk_congr (hf : A.B.IsScFredholmSection f) (p : ChartPoint A.B y)
    (o : p.Or f hf) {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) (hsurj : Surjective L)
    [FiniteDimensional ℝ ↥((LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0))] {n : ℕ}
    (hn : finrank ℝ ↥((LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)) = n) {T T' : Set A.X.PObj.TangentSpace}
    (hT : T = T') :
    (⟨n, T, chartFrames p.c.isChart T _ (p.orKerOrientation o hL hsurj rfl hn)⟩ :
        A.X.PObj.OrTangent) =
      ⟨finrank ℝ ↥((LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
          (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)), T',
        chartFrames p.c.isChart T' _ (p.orKerOrientation o hL hsurj rfl rfl)⟩ := by
  subst hn; subst hT; rfl

/-- **`(T_yMᵢ, o_{i,y}) = (ker L, o(L))` for `L = (f − sᵢ)'(y)`**, read in any strong bundle chart
`c` at `y` with domain in `O`. -/
theorem KernelBranching.orTangent_eq_linOrTangent {Λ : A.W → ℚ≥0} {x : A.Obj}
    (K : KernelBranching A f Λ x) (hf : A.B.IsScFredholmSection f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy) {i : K.ι} (hy : y ∈ K.M i)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hyc : y ∈ c.φ.source)
    (hsub : c.φ.source ⊆ K.O) (hys : y ∈ A.X.PObj.smoothSet) (hfs : f y = K.s i y) :
    K.orTangent hf hsec o i y =
      linOrTangent hf (chartPtOf c hc hyc hys) (toChartOr hf hys c hc hyc (o y hys))
        ⟨subOp hf.isScSmooth (K.isScPlus i) (chartPtOf c hc hyc hys) hsub hfs,
          subOp_mem_linSet hf K.isOpen_O (K.isScPlus i) (chartPtOf c hc hyc hys) hsub hfs hys
            hsec⟩ := by
  have hsurj : Surjective (subOp hf.isScSmooth (K.isScPlus i) (chartPtOf c hc hyc hys) hsub
      hfs) :=
    (surjective_subOp_iff hf.isScSmooth (K.isScPlus i) _ hsub hfs).2
      (K.onto i y hy c hc hsub hyc _ (chartPtOf c hc hyc hys).toBase_z)
  have hker := K.tangent_eq i y hy c hc hsub hyc _ (chartPtOf c hc hyc hys).toBase_z
  have hfin := (chartPtOf c hc hyc hys).finiteDimensional_of_mem_linSet hf
    (subOp_mem_linSet hf K.isOpen_O (K.isScPlus i) (chartPtOf c hc hyc hys) hsub hfs hys hsec) rfl
  have hcoe := (kerSet_eq_coe_map_ker hf.isScSmooth (K.isScPlus i)
    (chartPtOf c hc hyc hys) hsub hfs).symm.trans hker.symm
  have hn : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth (K.isScPlus i)
      (chartPtOf c hc hyc hys) hsub hfs : ↥(chartPtOf c hc hyc hys).T →L[ℝ]
        ↥(chartPtOf c hc hyc hys).K) : ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ]
          ↥(chartPtOf c hc hyc hys).K)).map
      ((chartPtOf c hc hyc hys).T.subtypeL : ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ]
        (chartPtOf c hc hyc hys).c.φ.model.E 0)) = K.dim i := by
    obtain ⟨N', hN', -, hn⟩ := exists_submodule_chartVec_image c.isChart
      (K.isSubmanifoldOfDim i).1 ((K.isSubmanifoldOfDim i).2 y hy) hyc
    rw [SetLike.coe_injective (hcoe.trans hN'.symm)]
    exact hn
  have hT : A.X.PObj.submanifoldTangent (K.M i) y =
      {α | A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y ∧
        chartVec (chartPtOf c hc hyc hys).c.isChart α ∈
        (LinearMap.ker ((subOp hf.isScSmooth (K.isScPlus i) (chartPtOf c hc hyc hys) hsub hfs :
          ↥(chartPtOf c hc hyc hys).T →L[ℝ] ↥(chartPtOf c hc hyc hys).K) :
            ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ] ↥(chartPtOf c hc hyc hys).K)).map
          ((chartPtOf c hc hyc hys).T.subtypeL : ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ]
            (chartPtOf c hc hyc hys).c.φ.model.E 0)} := by
    ext α
    constructor
    · intro hα
      exact ⟨hα.1, (Set.ext_iff.1 hcoe _).2 (mem_image_of_mem _ hα)⟩
    · rintro ⟨hov, hN⟩
      obtain ⟨β, hβ, hβα⟩ := (Set.ext_iff.1 hcoe _).1 hN
      rwa [← chartVec_injOn c.isChart hyc hβ.1 hov hβα]
  unfold linOrTangent KernelBranching.orTangent
  rw [dif_pos hsurj, K.frames_eq_chart hf hsec o hy hc hyc hsub hsurj hn]
  exact orTangent_mk_congr hf (chartPtOf c hc hyc hys) _ _ hsurj hn hT

/-! ### The formal sums of operators of two local structures -/

/-- The chart point of Part I at a smooth point is the chart point of `linSumChart`. -/
theorem chartPtOf_eq_liftPt {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hyc : y ∈ c.φ.source) (hys : y ∈ A.X.PObj.smoothSet) :
    chartPtOf c hc hyc hys = liftPt c hc hyc (smoothSet_subset_levelSet 1 hys) := by
  have hz : (exists_lift_of_smooth c hyc hys).choose = levelLift c.φ 1 y :=
    c.φ.model.E.toBase_injective 1 ((exists_lift_of_smooth c hyc hys).choose_spec.trans
      (A.X.PObj.toBase_levelLift c.isChart hyc (smoothSet_subset_levelSet 1 hys)).symm)
  unfold chartPtOf liftPt chartPt
  congr 1

/-- **The formal sum of operators does not depend on the local sc⁺-section structure**, in a
chart point equal to the chart point of `linSumChart` (Theorem 15.1.1, `linSumChart_eq`). -/
theorem linW_eq_of_eq_liftPt {Λ : A.W → ℚ≥0} (hf : A.B.IsScFredholmSection f) {O O' : Set A.Obj}
    (hO : IsOpen O) (hO' : IsOpen O') {k l : ℕ} {sb : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    {tb : Fin l → A.Obj → A.W} {τ : Fin l → ℚ≥0} (hrep : IsLocalRepOn A Λ O sb σ)
    (hrep' : IsLocalRepOn A Λ O' tb τ) (hys : y ∈ A.X.PObj.smoothSet)
    (hsec : A.B.HasScPlusSectionsThrough) (p : ChartPoint A.B y)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hyc : y ∈ c.φ.source)
    (hp : p = liftPt c hc hyc (smoothSet_subset_levelSet 1 hys)) (hsub : p.c.φ.source ⊆ O)
    (hsub' : p.c.φ.source ⊆ O') :
    linW hf hO hrep p hsub hys hsec = linW hf hO' hrep' p hsub' hys hsec := by
  subst hp
  have hz : c.φ.model.E.toBase 1 (levelLift c.φ 1 y) ∈ c.φ.model.O := by
    rw [A.X.PObj.toBase_levelLift c.isChart hyc (smoothSet_subset_levelSet 1 hys)]
    exact c.φ.mapsTo_model y hyc
  have heq := linSumChart_eq hf.isScSmooth hrep hrep' hc (fun x hx => ⟨hsub hx, hsub' hx⟩) hz
  have h1 := mapDomain_toF_linW hf hO hrep c hc hyc hsub hys hsec
  have h2 := mapDomain_toF_linW hf hO' hrep' c hc hyc hsub' hys hsec
  have hinj : Injective (Finsupp.mapDomain
      (fun L : (liftPt c hc hyc (smoothSet_subset_levelSet 1 hys)).linSet f => toF _ L.1) :
      ((liftPt c hc hyc (smoothSet_subset_levelSet 1 hys)).linSet f →₀ ℚ≥0) → _) :=
    Finsupp.mapDomain_injective ((toF_injective _).comp Subtype.val_injective)
  exact hinj (h1.trans (heq.trans h2.symm))

/-- **The formal sums of operators of two local sc⁺-section structures agree** in the chart points
of Part I. -/
theorem linW_chartPtOf_eq {Λ : A.W → ℚ≥0} (hf : A.B.IsScFredholmSection f) {O O' : Set A.Obj}
    (hO : IsOpen O) (hO' : IsOpen O') {k l : ℕ} {sb : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    {tb : Fin l → A.Obj → A.W} {τ : Fin l → ℚ≥0} (hrep : IsLocalRepOn A Λ O sb σ)
    (hrep' : IsLocalRepOn A Λ O' tb τ) (hys : y ∈ A.X.PObj.smoothSet)
    (hsec : A.B.HasScPlusSectionsThrough) {c : StrongBundleChart A.X.PObj A.P}
    (hc : A.B.IsChart c) (hyc : y ∈ c.φ.source) (hsub : c.φ.source ⊆ O)
    (hsub' : c.φ.source ⊆ O') :
    linW hf hO hrep (chartPtOf c hc hyc hys) hsub hys hsec =
      linW hf hO' hrep' (chartPtOf c hc hyc hys) hsub' hys hsec :=
  linW_eq_of_eq_liftPt hf hO hO' hrep hrep' hys hsec _ hc hyc (chartPtOf_eq_liftPt hc hyc hys)
    hsub hsub'

/-! ### The formula in `Ĝr(y)` as the image of the formal sum of operators -/

open Classical in
/-- **The formula of Theorem 15.4.1 in `Ĝr(y)` is the image of the formal sum of operators**
`∑_{j : f(y) = s_j(y)} σ_j · (f − s_j)'(y)` under `L ↦ (ker L, o(L))`, in any strong bundle chart
at `y` with domain in `O`. -/
theorem KernelBranching.canonSum_apply_eq {Λ : A.W → ℚ≥0} {x : A.Obj}
    (K : KernelBranching A f Λ x) (hf : A.B.IsScFredholmSection f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy) (hyU : y ∈ K.U)
    (hys : y ∈ A.X.PObj.smoothSet) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hyc : y ∈ c.φ.source) (hsub : c.φ.source ⊆ K.O) (g : A.X.PObj.OrTangent) :
    K.canonSum hf hsec o y g =
      (((linW hf K.isOpen_O K.isLocalRep (chartPtOf c hc hyc hys) hsub hys hsec).mapDomain
        (linOrTangent hf (chartPtOf c hc hyc hys) (toChartOr hf hys c hc hyc (o y hys))) g :
          ℚ≥0) : ℚ) := by
  have hR : (linW hf K.isOpen_O K.isLocalRep (chartPtOf c hc hyc hys) hsub hys hsec).mapDomain
      (linOrTangent hf (chartPtOf c hc hyc hys) (toChartOr hf hys c hc hyc (o y hys))) g =
      ∑ j, if h : K.sAll j y = f y then
        (if linOrTangent hf (chartPtOf c hc hyc hys) (toChartOr hf hys c hc hyc (o y hys))
          ⟨subOp hf.isScSmooth (K.isLocalRep.2.1 j) (chartPtOf c hc hyc hys) hsub h.symm,
            subOp_mem_linSet hf K.isOpen_O (K.isLocalRep.2.1 j) (chartPtOf c hc hyc hys) hsub
              h.symm hys hsec⟩ = g then K.σAll j else 0) else 0 := by
    unfold linW
    rw [Finsupp.mapDomain_finsetSum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h h'
    · rw [Finsupp.mapDomain_single, h', Finsupp.single_eq_same]
    · rw [Finsupp.mapDomain_single, Finsupp.single_eq_of_ne (Ne.symm h')]
    · rw [Finsupp.mapDomain_zero]; rfl
  have hmem : ∀ i, y ∈ K.M i ↔ K.sAll (K.idx i) y = f y := fun i => by
    rw [K.M_eq i]
    exact ⟨fun h => h.2.symm, fun h => ⟨hyU, h.symm⟩⟩
  rw [hR, K.canonSum_apply, NNRat.cast_sum]
  rw [← Finset.sum_filter_of_ne (p := fun j => K.sAll j y = f y) (fun j _ hne => by
    by_contra h
    exact hne (by rw [dif_neg h]; rfl))]
  refine Finset.sum_bij (fun i _ => K.idx i) (fun i hi => ?_) (fun i _ i' _ h => K.idx_injective h)
    (fun j hj => ?_) (fun i hi => ?_)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hmem i).1 (Finset.mem_filter.1 hi).2⟩
  · obtain ⟨i, rfl⟩ := K.mem_range j y hyU (Finset.mem_filter.1 hj).2.symm
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hmem i).2 (Finset.mem_filter.1 hj).2⟩, rfl⟩
  · have hyi : y ∈ K.M i := (Finset.mem_filter.1 hi).2
    rw [dif_pos ((hmem i).1 hyi),
      K.orTangent_eq_linOrTangent hf hsec o hyi hc hyc hsub hys ((hmem i).1 hyi).symm]
    split_ifs
    · exact K.σ_eq i
    · exact NNRat.cast_zero.symm

/-! ### Independence of the local structure -/

/-- **Theorem 15.4.1, independence of the local sc⁺-section structure, in `Ĝr(X)`** (2021 p. 701):
two local branching structures described by kernels give the same oriented sum
`∑ σᵢ · (T_yMᵢ, o_{i,y})` at every common smooth point, for every family `o_y ∈ Or_y^f`. -/
theorem canonIndependent (Λ : A.W → ℚ≥0) (hf : A.B.IsScFredholmSection f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy) : CanonIndependent Λ hf hsec o := by
  intro x x' K K' y hy hy' hys
  have hOO := K.isOpen_O.inter K'.isOpen_O
  have hc := StrongBundle.IsChart.restrictInter hOO (isChart_orChart (B := A.B) y)
  have hyc : y ∈ ((orChart A.B y).restrictInter hOO).φ.source :=
    StrongBundleChart.mem_restrictInter_source _ hOO (mem_orChart y)
      ⟨K.U_subset hy, K'.U_subset hy'⟩
  have hsub : ((orChart A.B y).restrictInter hOO).φ.source ⊆ K.O := fun z hz =>
    (StrongBundleChart.restrictInter_source_subset _ hOO hz).1
  have hsub' : ((orChart A.B y).restrictInter hOO).φ.source ⊆ K'.O := fun z hz =>
    (StrongBundleChart.restrictInter_source_subset _ hOO hz).2
  ext g
  rw [K.canonSum_apply_eq hf hsec o hy hys hc hyc hsub g,
    K'.canonSum_apply_eq hf hsec o hy' hys hc hyc hsub' g,
    linW_chartPtOf_eq hf K.isOpen_O K'.isOpen_O K.isLocalRep K'.isLocalRep hys hsec hc hyc hsub
      hsub']

/-! ### Theorem 15.4.1 from naturality and continuity; uniqueness -/

section Canonical

variable {Λ : A.W → ℚ≥0} {hf : A.B.IsScFredholmSection f} {hsec : A.B.HasScPlusSectionsThrough}
  {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy}

/-- The sum (9.9) of the oriented tame structure of `K` is the formula of Theorem 15.4.1. -/
theorem KernelBranching.orientedSum_toOrientedTame {x : A.Obj} (K : KernelBranching A f Λ x)
    (hc : K.FramesContinuous hf hsec o) {n : ℕ} (hn : ∀ i, K.dim i = n) (y : A.Obj) :
    (K.toOrientedTame hc hn).toOriented.orientedSum y = K.canonSum hf hsec o y := by
  classical
  change (∑ i with y ∈ K.M i, Finsupp.single ((hn i ▸ K.orient hc i).tangent y) (K.σ i)) = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [KernelBranching.tangent_cast_aux]
  rfl

/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6) in `Ĝr(X)`, from naturality and
continuity**: as `theorem_15_4_1_of_local`, with the independence of the local sc⁺-section
structure proved (`canonIndependent`). -/
theorem theorem_15_4_1_of_natural_continuous (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hΛ : IsScPlusMultisection A Λ) {n : ℕ}
    (hdim : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ K : KernelBranching A f Λ x, ∀ i, K.dim i = n)
    (hTS : A.X.HasIndependentTangentSums (fun z => (Λ (f z) : ℚ)))
    (hnat : CanonNatural Λ hf hsec o) (hcont : CanonContinuous Λ hf hsec o) :
    IsCanonicalFor Λ hf hsec o n (canonicalOrientation Λ hf hsec o) :=
  theorem_15_4_1_of_local hF hft hΛ hdim hTS (canonIndependent Λ hf hsec o) hnat hcont

/-- A canonical orientation is described by oriented tame structures of dimension `n` (the
input `hloc` of Theorem 15.4.3, `theorem_15_4_3_hyp`). -/
theorem IsCanonicalFor.loc {n : ℕ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}
    (h : IsCanonicalFor Λ hf hsec o n T) :
    ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ C : A.X.OrientedTameStructure n (fun z => (Λ (f z) : ℚ)) x, C.Represents T :=
  fun x hx => by
    obtain ⟨K, hc, hn, hR⟩ := h.2 x hx
    exact ⟨_, hR⟩

/-- **Definition 15.4.2: the canonical orientation is unique.**  Two orientations of `Θ = Λ ∘ f`
which are canonical for the same `(f, o)` agree at every smooth point. -/
theorem IsCanonicalFor.unique {n n' : ℕ} {T T' : A.Obj → A.X.PObj.OrTangent →₀ ℚ}
    (h : IsCanonicalFor Λ hf hsec o n T) (h' : IsCanonicalFor Λ hf hsec o n' T') {y : A.Obj}
    (hys : y ∈ A.X.PObj.smoothSet) : T y = T' y := by
  by_cases hy : y ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ))
  · obtain ⟨K, hc, hn, hR⟩ := h.2 y hy
    obtain ⟨K', hc', hn', hR'⟩ := h'.2 y hy
    rw [hR y K.mem_U hys, hR' y K'.mem_U hys, K.orientedSum_toOrientedTame,
      K'.orientedSum_toOrientedTame]
    exact canonIndependent Λ hf hsec o y y K K' y K.mem_U K'.mem_U hys
  · rw [h.1.eq_zero_of_not_mem hys hy, h'.1.eq_zero_of_not_mem hys hy]

variable (hf hsec o) in
/-- **The predicate `Can` of Corollary 15.4.4**: the orientation of the oriented regular
perturbation `P` is the canonical one for `(f, o)` (Definition 15.4.2). -/
def IsCanonicalPerturbation {m : ℕ} (P : OrientedRegularPerturbation A f m) : Prop :=
  IsCanonicalFor P.Λ hf hsec o (m + 1) P.T

end Canonical

end SBLocalization

end Polyfold
