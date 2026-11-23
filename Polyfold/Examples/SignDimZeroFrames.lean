import Polyfold.Examples.SignDimZeroPush
import Polyfold.Chapter15.CanonicalLiftIndependence
import Polyfold.Examples.PointCountFiniteSupport

/-!
# The sign of the canonical orientation in dimension `0`

For an oriented sc-Fredholm section functor `(f, o)` and an sc⁺-multisection `Λ` whose perturbed
solution set has dimension `0`, the canonical orientation `T̂` of Theorem 15.4.1
(Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory*, Springer 2021, pp. 701–702) is, at a
point `y`, the formal sum `∑ σᵢ · ({0}, ±)`; the sign of the branch `sᵢ` is `+` iff `o_y` is
positive at the isomorphism `(f − sᵢ)'(y)` (`IsPosOr`, `SignDimZeroPush.lean`).

## What is formalized

* `SBLocalization.chartFrames_nonempty_iff`: in dimension `0` the set of positive frames is
  non-empty iff the orienting ray is the ray of the empty wedge.
* **`SBLocalization.frameSign_linOrTangent_eq_one_iff`**: for an isomorphism `L ∈ Lin(f, y)`,
  the sign of the oriented tangent set `(ker L, o(L))` is `+1` iff `o` is positive at `L`.
* `SBLocalization.subOp_eq_stabT`: `(f − s)'(y) = (f + S)'(y)` when `f + S = f − s` near `y`.
* `SBLocalization.KernelBranching.exists_subOp_eq`: the operator of a sheet of a structure
  described by kernels is the operator of a branch of any other local representation of `Λ`
  (Theorem 15.1.1).
* **`SBLocalization.KernelBranching.frameSign_orTangent_eq_one_iff`** (the sign lemma): for a
  sheet `Mᵢ` of dimension `0` through `y`, the sign of `(T_yMᵢ, o_{i,y})` is `+1` iff `o_y` is
  positive at `(f − sᵢ)'(y)`.
* **`SBLocalization.IsCanonicalFor.signedWeight_eq`**: if `o_y` is positive at the operators of
  all branches through `y` of a local representation of `Λ`, the signed weight of the canonical
  orientation at `y` is `Λ(f(y))`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace ChartPoint

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {x : X} (p : ChartPoint B x) {hf : B.IsScFredholmSection f}

/-- Positivity read with any name `N` of the image of the kernel. -/
theorem orKer_eq_emptyRay_iff_isPos (o : p.Or f hf) {L : ↥p.T →L[ℝ] ↥p.K}
    (hL : L ∈ p.linSet f) (hLs : Surjective L) {N : Submodule ℝ (p.c.φ.model.E 0)}
    (hN : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N) (hbot : N = ⊥)
    [FiniteDimensional ℝ N] (h0 : finrank ℝ N = 0) :
    p.orKer o hL hLs hN = emptyRay N h0 ↔ p.IsPos o L := by
  subst hbot
  exact (isPos_iff hL hLs hN).symm

end ChartPoint

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

/-- **In dimension `0` there is a positive frame iff the orienting ray is the ray of the empty
wedge.** -/
theorem chartFrames_nonempty_iff {X : Type*} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {PX : MPolyfold X} {φ : MChart X} (hφ : PX.IsChart φ)
    (L : Set PX.TangentSpace) (N : Submodule ℝ (φ.model.E 0)) [FiniteDimensional ℝ N] {n : ℕ}
    (hn : finrank ℝ N = n) (h0 : n = 0) (r : Module.Ray ℝ (maxPow N)) :
    (chartFrames hφ L N (pullOr hn (LinearEquiv.refl ℝ N) r)).Nonempty ↔
      r = emptyRay N (hn.trans h0) := by
  subst h0
  constructor
  · rintro ⟨v, -, b, -, hbo⟩
    rw [(orientation_eq_pullOr_iff hn (LinearEquiv.refl ℝ N) r b).1 hbo]
    exact rayOfNeZero_congr (wedge_eq_emptyWedge rfl _ _) _ _
  · intro hr
    refine ⟨Fin.elim0, fun i => i.elim0, pullBasis hn, fun i => i.elim0, ?_⟩
    rw [orientation_eq_pullOr_iff, hr]
    exact rayOfNeZero_congr (wedge_eq_emptyWedge rfl _ _).symm _ _

variable {A : SEP.{u}} {f : A.Obj → A.W} {y : A.Obj}

/-- **The sign of `(ker L, o(L))` for an isomorphism `L ∈ Lin(f, y)`** is `+1` iff `o` is
positive at `L`. -/
theorem frameSign_linOrTangent_eq_one_iff (hf : A.B.IsScFredholmSection f)
    (p : ChartPoint A.B y) (o : p.Or f hf) (L : p.linSet f)
    (hLb : Bijective (L.1 : ↥p.T →L[ℝ] ↥p.K)) :
    frameSign (X := A.X) (linOrTangent hf p o L) = 1 ↔ p.IsPos o L.1 := by
  have hN := p.map_ker_eq_bot hLb.1
  have := p.finiteDimensional_of_mem_linSet hf L.2 rfl
  have h0 : finrank ℝ ↥((LinearMap.ker ((L.1 : ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)) = 0 := by
    rw [hN]
    exact finrank_bot ℝ _
  have hne : (linOrTangent hf p o L).frames.Nonempty ↔ p.IsPos o L.1 := by
    unfold linOrTangent
    rw [dif_pos hLb.2]
    exact (chartFrames_nonempty_iff p.c.isChart _ _ rfl h0 _).trans
      (p.orKer_eq_emptyRay_iff_isPos o L.2 hLb.2 rfl hN h0)
  unfold frameSign
  split_ifs with h
  · exact iff_of_true rfl (hne.1 h)
  · exact iff_of_false (by norm_num) fun h' => h (hne.2 h')

/-- **`(f − s)'(y) = (f + S)'(y)`** in a chart point with domain in `O`, when the sections
`f + S` and `f − s` agree on the domain of the chart. -/
theorem subOp_eq_stabT (hf : A.B.IsScFredholmSection f) {s : A.Obj → A.W} {O : Set A.Obj}
    (hs : IsScPlusSectionOn A s O) (p : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O)
    (hfs : f y = s y) {S : A.Obj → A.W} (hS : A.B.IsScPlusSection S)
    (hx : IsZeroAt A.P (sectionAdd A.P f S) y)
    (hSs : ∀ x' ∈ p.c.φ.source, sectionAdd A.P f S x' = subSec f s O x') :
    subOp hf.isScSmooth hs p hsub hfs = p.stabT hf hS hx := by
  refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
  rw [coe_subOp, ChartPoint.coe_stabT, linAt_apply,
    subDeriv_eq_scDeriv_subSec hf.isScSmooth hs p.isChart hsub p.mem_U]
  refine congrArg (fun M : p.c.φ.model.E 0 →L[ℝ] p.c.F 0 => M (v : p.c.φ.model.E 0)) ?_
  refine scDeriv_eq_of_eqOn_relOpen p.c.relOpen
    (isSc1_principal_subSec_comp_r hf.isScSmooth hs p.isChart hsub)
    ((hf.isScSmooth.sectionAdd hS).isSc1_principal_comp_r p.isChart) subset_rfl subset_rfl
    (fun u hu => ?_) p.mem_U
  have hO' : r p.c.R u ∈ p.c.φ.model.O := p.c.r_mem_O hu
  have hzV : p.c.φ.symm (r p.c.R u) ∈ p.c.φ.source := p.c.φ.symm_mapsTo hO'
  change p.c.principal (subSec f s O) (r p.c.R u) =
    p.c.principal (sectionAdd A.P f S) (r p.c.R u)
  unfold StrongBundleChart.principal
  rw [hSs _ hzV]

namespace KernelBranching

variable {Λ : A.W → ℚ≥0} {x : A.Obj} (K : KernelBranching A f Λ x)

/-- **The operator of a sheet is the operator of a branch of any local representation**
(Theorem 15.1.1, `linW_chartPtOf_eq`): for `y ∈ Mᵢ` and a local representation `(s'_j, σ'_j)`
of `Λ` on `O'`, in a chart at `y` with domain in `O ∩ O'`, `(f − sᵢ)'(y) = (f − s'_j)'(y)` for
some `j` with `s'_j(y) = f(y)`. -/
theorem exists_subOp_eq (hf : A.B.IsScFredholmSection f) (hsec : A.B.HasScPlusSectionsThrough)
    {i : K.ι} (hy : y ∈ K.M i) (hys : y ∈ A.X.PObj.smoothSet) {O' : Set A.Obj}
    (hO' : IsOpen O') {k : ℕ} {sb : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    (hrep : IsLocalRepOn A Λ O' sb σ) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hyc : y ∈ c.φ.source) (hsub : c.φ.source ⊆ K.O) (hsub' : c.φ.source ⊆ O') :
    ∃ (j : Fin k) (h : sb j y = f y),
      subOp hf.isScSmooth (K.isScPlus i) (chartPtOf c hc hyc hys) hsub (K.eq_of_mem hy) =
        subOp hf.isScSmooth (hrep.2.1 j) (chartPtOf c hc hyc hys) hsub' h.symm := by
  classical
  set p := chartPtOf c hc hyc hys with hp
  have hfy : K.sAll (K.idx i) y = f y := (K.eq_of_mem hy).symm
  set L₀ : p.linSet f := ⟨subOp hf.isScSmooth (K.isScPlus i) p hsub (K.eq_of_mem hy),
    subOp_mem_linSet hf K.isOpen_O (K.isScPlus i) p hsub (K.eq_of_mem hy) hys hsec⟩ with hL₀
  -- `L₀` has positive weight in the formal sum of `K`
  have hmem : L₀ ∈ (linW hf K.isOpen_O K.isLocalRep p hsub hys hsec).support := by
    rw [Finsupp.mem_support_iff]
    unfold linW
    rw [Finsupp.finsetSum_apply]
    have hle : (if h : K.sAll (K.idx i) y = f y then
        Finsupp.single (⟨subOp hf.isScSmooth (K.isLocalRep.2.1 (K.idx i)) p hsub h.symm,
          subOp_mem_linSet hf K.isOpen_O (K.isLocalRep.2.1 (K.idx i)) p hsub h.symm hys hsec⟩ :
            p.linSet f) (K.σAll (K.idx i)) else 0) L₀ ≤ _ :=
      Finset.single_le_sum (f := fun j => (if h : K.sAll j y = f y then
        Finsupp.single (⟨subOp hf.isScSmooth (K.isLocalRep.2.1 j) p hsub h.symm,
          subOp_mem_linSet hf K.isOpen_O (K.isLocalRep.2.1 j) p hsub h.symm hys hsec⟩ :
            p.linSet f) (K.σAll j) else 0) L₀) (fun _ _ => zero_le) (Finset.mem_univ (K.idx i))
    rw [dif_pos hfy, Finsupp.single_eq_same] at hle
    exact (lt_of_lt_of_le (K.isLocalRep.1 (K.idx i)) hle).ne'
  rw [linW_chartPtOf_eq hf K.isOpen_O hO' K.isLocalRep hrep hys hsec hc hyc hsub hsub'] at hmem
  unfold linW at hmem
  obtain ⟨j, -, hj⟩ := Finsupp.mem_support_finsetSum L₀ hmem
  by_cases h : sb j y = f y
  · rw [dif_pos h] at hj
    have := Finsupp.support_single_subset hj
    rw [Finset.mem_singleton] at this
    exact ⟨j, h, congrArg Subtype.val this⟩
  · rw [dif_neg h] at hj
    exact absurd hj (by simp)

/-- **The sign lemma in dimension `0`** (Theorem 15.4.1, 2021 pp. 701–702): for a sheet `Mᵢ` of
dimension `0` of a structure described by kernels and `y ∈ Mᵢ`, the sign of the oriented
tangent set `(T_yMᵢ, o_{i,y})` is `+1` iff `o_y` is positive at `(f − sᵢ)'(y)`; here
`(f − sᵢ)'(y)` is read as `(f + S)'(y)` for a global sc⁺-section `S` with `f + S = f − sᵢ` on
`O`. -/
theorem frameSign_orTangent_eq_one_iff (hf : A.B.IsScFredholmSection f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy) {i : K.ι} (hy : y ∈ K.M i)
    (hd : K.dim i = 0) {S : A.Obj → A.W} (hS : A.B.IsScPlusSection S)
    (hx : IsZeroAt A.P (sectionAdd A.P f S) y)
    (hSs : ∀ x' ∈ K.O, sectionAdd A.P f S x' = subSec f (K.s i) K.O x') :
    frameSign (X := A.X) (K.orTangent hf hsec o i y) = 1 ↔
      IsPosOr hf (K.smooth i y hy) (o y (K.smooth i y hy)) S hS hx := by
  have hys := K.smooth i y hy
  have hyc := K.mem_chart (K.mem_O hy)
  have hsub := K.chart_subset y
  rw [K.orTangent_eq_linOrTangent hf hsec o hy (K.isChart_chart y) hyc hsub hys (K.eq_of_mem hy),
    isPosOr_iff_chart hf hys _ hS hx (K.chart y) (K.isChart_chart y) hyc]
  have hsurj := K.surj hf hy
  have hfin := (K.pt (K.mem_O hy) hys).finiteDimensional_of_mem_linSet hf
    (subOp_mem_linSet hf K.isOpen_O (K.isScPlus i) (K.pt (K.mem_O hy) hys) hsub (K.eq_of_mem hy)
      hys hsec) rfl
  have hinj : Injective (subOp hf.isScSmooth (K.isScPlus i) (K.pt (K.mem_O hy) hys) hsub
      (K.eq_of_mem hy)) :=
    (K.pt (K.mem_O hy) hys).injective_of_map_ker_eq_bot
      (Submodule.finrank_eq_zero.1 ((K.finrank_ker hf hy).trans hd))
  have he := subOp_eq_stabT hf (K.isScPlus i) (K.pt (K.mem_O hy) hys) hsub (K.eq_of_mem hy) hS hx
    (fun x' hx' => hSs x' (hsub hx'))
  rw [frameSign_linOrTangent_eq_one_iff hf _ _ _ ⟨hinj, hsurj⟩]
  exact iff_of_eq (congrArg _ he)

end KernelBranching

/-- **The signed weight of the canonical orientation at a point where `o` is positive**
(Theorem 15.4.1, dimension `0`): let `T̂` be the canonical orientation of `Θ = Λ ∘ f` for
`(f, o)`, of dimension `0`, `y` a smooth point of the support, and `(s_j, σ_j)` a local
representation of `Λ` on an open `O' ∋ y`, with global sc⁺-sections `S_j` such that
`f + S_j = f − s_j` on `O'`.  If `o_y` is positive at `(f − s_j)'(y)` for every branch through
`y`, the signed weight of `T̂(y)` is `Λ(f(y))`. -/
theorem IsCanonicalFor.signedWeight_eq {Λ : A.W → ℚ≥0} {hf : A.B.IsScFredholmSection f}
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy}
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (h : IsCanonicalFor Λ hf hsec o 0 T)
    (hy : y ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ))) (hys : y ∈ A.X.PObj.smoothSet)
    {O' : Set A.Obj} (hO' : IsOpen O') (hyO' : y ∈ O') {k : ℕ} {sb : Fin k → A.Obj → A.W}
    {σ : Fin k → ℚ≥0} (hrep : IsLocalRepOn A Λ O' sb σ) (S : Fin k → A.Obj → A.W)
    (hS : ∀ j, A.B.IsScPlusSection (S j))
    (hSs : ∀ j, ∀ x' ∈ O', sectionAdd A.P f (S j) x' = subSec f (sb j) O' x')
    (hpos : ∀ j, sb j y = f y → ∃ hx : IsZeroAt A.P (sectionAdd A.P f (S j)) y,
      IsPosOr hf hys (o y hys) (S j) (hS j) hx) :
    signedWeight (X := A.X) (T y) = ((Λ (f y) : ℚ) : ℝ) := by
  classical
  obtain ⟨K, hc, hn, hR⟩ := h.2 y hy
  rw [hR y K.mem_U hys, K.orientedSum_toOrientedTame]
  -- a chart at `y` with domain in `O ∩ O'`
  have hOO := K.isOpen_O.inter hO'
  have hcc := StrongBundle.IsChart.restrictInter hOO (isChart_orChart (B := A.B) y)
  have hyc : y ∈ ((orChart A.B y).restrictInter hOO).φ.source :=
    StrongBundleChart.mem_restrictInter_source _ hOO (mem_orChart y) ⟨K.U_subset K.mem_U, hyO'⟩
  have hsub : ((orChart A.B y).restrictInter hOO).φ.source ⊆ K.O := fun z hz =>
    (StrongBundleChart.restrictInter_source_subset _ hOO hz).1
  have hsub' : ((orChart A.B y).restrictInter hOO).φ.source ⊆ O' := fun z hz =>
    (StrongBundleChart.restrictInter_source_subset _ hOO hz).2
  have hsign : ∀ i, y ∈ K.M i → frameSign (X := A.X) (K.orTangent hf hsec o i y) = 1 := by
    intro i hyi
    obtain ⟨j, hj, hjeq⟩ := K.exists_subOp_eq hf hsec hyi hys hO' hrep hcc hyc hsub hsub'
    obtain ⟨hx, hp⟩ := hpos j hj
    rw [isPosOr_iff_chart hf hys _ (hS j) hx _ hcc hyc] at hp
    have he := subOp_eq_stabT hf (hrep.2.1 j) (chartPtOf _ hcc hyc hys) hsub' hj.symm (hS j) hx
      (fun x' hx' => hSs j x' (hsub' hx'))
    rw [← he, ← hjeq] at hp
    rw [K.orTangent_eq_linOrTangent hf hsec o hyi hcc hyc hsub hys (K.eq_of_mem hyi)]
    exact (frameSign_linOrTangent_eq_one_iff hf _ _ _ hp.bijective).2 hp
  unfold KernelBranching.canonSum
  rw [signedWeight_sum, K.eq_sum y K.mem_U, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [signedWeight_single, hsign i (Finset.mem_filter.1 hi).2, mul_one]

end SBLocalization

end Polyfold
