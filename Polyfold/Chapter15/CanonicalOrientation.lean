import Polyfold.Chapter15.KernelBranching
import Polyfold.Chapter15.PerturbedStokesInvariants

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702: **Theorem 15.4.1** and **Definition 15.4.2** (2017: Theorem 15.6, Definition 15.7),
the canonical lift `T̂_((f, o), Λ)` as a section of Chapter 9's `Ĝr(X)`.

# The canonical orientation of `Θ = Λ ∘ f` in `Ĝr(X)`

## The text, paraphrased

(Theorem 15.4.1) For an oriented sc-Fredholm section functor `(f, o)` and an sc⁺-multisection
`Λ` in good position, the tangent functor `T_Θ` of `Θ = Λ ∘ f` has a canonical lift to `Ĝr(X)`:
in a local sc⁺-section structure, `T̂(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ · (ker (f − sᵢ)'(y), o_{i,y})`,
`ker (f − sᵢ)'(y) = T_yMᵢ`, with `o_{i,y}` induced by `o_y`.  (Definition 15.4.2) It is the
canonical orientation of `Θ`.

## What is formalized (namespace `Polyfold.SBLocalization`)

For a local branching structure `K` described by kernels (`KernelBranching`) and a family
`o_y ∈ Or_y^f`:

* `KernelBranching.frames`: the frames of `T_yMᵢ` whose chart vectors are a basis of
  `ker (f − sᵢ)'(y)` positive for the orientation induced by `o_y` (`orKerOrientation`), read in
  a chart at `y` with domain in `O`;
  **`KernelBranching.isOrientedAt`**: `(T_yMᵢ, o_{i,y})` is an oriented tangent set of
  Chapter 9 (`IsOrientedAt`).
* `KernelBranching.canonSum`: `∑_{i : y ∈ Mᵢ} σᵢ · (T_yMᵢ, o_{i,y})`, the formula of
  Theorem 15.4.1 in Chapter 9's formal sums; **`canonSum_mem`** (it lies in `Ĝr(y)`),
  **`grForget_canonSum`** (it lifts `∑ σᵢ · T_yMᵢ`), `canonSum_eq_zero` (zero off the support).
* `KernelBranching.FramesContinuous`: the continuity of `y ↦ o_{i,y}` along `Mᵢ` in the sense of
  Definition 9.3.2 (a continuous positive frame field near every point);
  `KernelBranching.orient`, `toOriented`, `toOrientedTame`: under it, the oriented (tame) local
  branching structure, with `orientedSum_toOriented` (its sum (9.9) is `canonSum`).
* `canonicalOrientation`: the section `y ↦ T̂(y)` of `Ĝr(X)`; `CanonIndependent` (the sum does
  not depend on the structure), `CanonNatural` (it is carried by morphisms), `CanonContinuous`.
* **`theorem_15_4_1_of_local`**: under these three properties and the independence of
  Theorem 9.2.1, with sheets of one dimension `n`, `canonicalOrientation` is an orientation of
  `Θ = Λ ∘ f` (Definition 9.3.2), represented near every point of the support by an oriented
  tame branching structure whose sheets are the `Mᵢ` oriented by `o` (`IsCanonicalFor`).

## Reading

The three properties are the content of "canonical" in the text: the operators of the sum do
not depend on the local structure, `o` is continuous and invariant under morphisms.  They are
stated here for the sums in `Ĝr(X)`; they are not derived from Definition 12.5.4 in this file.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}}

/-! ### Frames of a kernel positive for the induced orientation -/

/-- **The positive frames of `ker (f − s)'(y)` for the orientation induced by `o`** (2021
pp. 701–702), as frames of a set `L ⊆ TX`: the frames of `L` whose chart vectors, in the chart
of the chart point `p`, are a basis of the kernel positive for `orKerOrientation o`. -/
def kerFrames {f s : A.Obj → A.W} {O : Set A.Obj} {y : A.Obj} (hf : A.B.IsScFredholmSection f)
    (hO : IsOpen O) (hs : IsScPlusSectionOn A s O) (p : ChartPoint A.B y)
    (hsub : p.c.φ.source ⊆ O) (hfs : f y = s y) (hys : y ∈ A.X.PObj.smoothSet)
    (hsec : A.B.HasScPlusSectionsThrough)
    (hsurj : Surjective (subOp hf.isScSmooth hs p hsub hfs)) (o : p.Or f hf)
    (L : Set A.X.PObj.TangentSpace) {n : ℕ}
    (hn : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth hs p hsub hfs : ↥p.T →L[ℝ] ↥p.K) :
      ↥p.T →ₗ[ℝ] ↥p.K)).map (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)) = n) :
    Set (Fin n → A.X.PObj.TangentSpace) :=
  haveI := p.finiteDimensional_of_mem_linSet hf
    (subOp_mem_linSet hf hO hs p hsub hfs hys hsec) rfl
  chartFrames p.c.isChart L _
    (p.orKerOrientation o (subOp_mem_linSet hf hO hs p hsub hfs hys hsec) hsurj rfl hn)

/-- **`(L, kerFrames)` is an oriented tangent set over `y`** (Chapter 9's `IsOrientedAt`) when `L`
lies over `y` and its chart vectors are the kernel of `(f − s)'(y)`. -/
theorem isOrientedAt_kerFrames {f s : A.Obj → A.W} {O : Set A.Obj} {y : A.Obj}
    (hf : A.B.IsScFredholmSection f) (hO : IsOpen O) (hs : IsScPlusSectionOn A s O)
    (p : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O) (hfs : f y = s y)
    (hys : y ∈ A.X.PObj.smoothSet) (hsec : A.B.HasScPlusSectionsThrough)
    (hsurj : Surjective (subOp hf.isScSmooth hs p hsub hfs)) (o : p.Or f hf)
    {L : Set A.X.PObj.TangentSpace}
    (hL : ∀ α ∈ L, A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y)
    (hker : chartVec p.c.isChart '' L = kerSet p.c f s p.z) {n : ℕ}
    (hn : finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth hs p hsub hfs : ↥p.T →L[ℝ] ↥p.K) :
      ↥p.T →ₗ[ℝ] ↥p.K)).map (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)) = n) :
    A.X.PObj.IsOrientedAt y ⟨n, L, kerFrames hf hO hs p hsub hfs hys hsec hsurj o L hn⟩ :=
  ⟨hL, p.c.φ, p.c.isChart, p.mem_source, _,
    (kerSet_eq_coe_map_ker hf.isScSmooth hs p hsub hfs).symm.trans hker.symm,
    p.finiteDimensional_of_mem_linSet hf (subOp_mem_linSet hf hO hs p hsub hfs hys hsec) rfl,
    hn, _, rfl⟩

namespace KernelBranching

variable {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} {x : A.Obj} (K : KernelBranching A f Λ x)

/-! ### The chart point at a point of a sheet -/

/-- A chart at `y` with domain in `O`: the chosen chart of Part I restricted to `O`. -/
def chart (y : A.Obj) : StrongBundleChart A.X.PObj A.P :=
  (orChart A.B y).restrictInter K.isOpen_O

theorem isChart_chart (y : A.Obj) : A.B.IsChart (K.chart y) :=
  StrongBundle.IsChart.restrictInter K.isOpen_O (isChart_orChart y)

theorem chart_subset (y : A.Obj) : (K.chart y).φ.source ⊆ K.O :=
  StrongBundleChart.restrictInter_source_subset _ K.isOpen_O

theorem mem_chart {y : A.Obj} (hy : y ∈ K.O) : y ∈ (K.chart y).φ.source :=
  StrongBundleChart.mem_restrictInter_source _ K.isOpen_O (mem_orChart y) hy

theorem mem_O {i : K.ι} {y : A.Obj} (hy : y ∈ K.M i) : y ∈ K.O := K.U_subset (K.subset_U i hy)

theorem eq_of_mem {i : K.ι} {y : A.Obj} (hy : y ∈ K.M i) : f y = K.s i y := by
  have h := hy
  rw [K.M_eq i] at h
  exact h.2

/-- **The chart point at `y ∈ O`** in the chart `K.chart y`. -/
abbrev pt {y : A.Obj} (hyO : y ∈ K.O) (hys : y ∈ A.X.PObj.smoothSet) : ChartPoint A.B y :=
  chartPtOf (K.chart y) (K.isChart_chart y) (K.mem_chart hyO) hys

theorem surj (hf : A.B.IsScFredholmSection f) {i : K.ι} {y : A.Obj} (hy : y ∈ K.M i) :
    Surjective (subOp hf.isScSmooth (K.isScPlus i) (K.pt (K.mem_O hy) (K.smooth i y hy))
      (K.chart_subset y) (K.eq_of_mem hy)) :=
  (surjective_subOp_iff hf.isScSmooth (K.isScPlus i) _ (K.chart_subset y) (K.eq_of_mem hy)).2
    (K.onto i y hy _ (K.isChart_chart y) (K.chart_subset y) (K.mem_chart (K.mem_O hy)) _
      (K.pt (K.mem_O hy) (K.smooth i y hy)).toBase_z)

theorem ker_eq {i : K.ι} {y : A.Obj} (hy : y ∈ K.M i) :
    chartVec (K.pt (K.mem_O hy) (K.smooth i y hy)).c.isChart ''
        A.X.PObj.submanifoldTangent (K.M i) y =
      kerSet (K.pt (K.mem_O hy) (K.smooth i y hy)).c f (K.s i)
        (K.pt (K.mem_O hy) (K.smooth i y hy)).z :=
  K.tangent_eq i y hy _ (K.isChart_chart y) (K.chart_subset y) (K.mem_chart (K.mem_O hy)) _
    (K.pt (K.mem_O hy) (K.smooth i y hy)).toBase_z

theorem finrank_ker (hf : A.B.IsScFredholmSection f) {i : K.ι} {y : A.Obj} (hy : y ∈ K.M i) :
    finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth (K.isScPlus i)
        (K.pt (K.mem_O hy) (K.smooth i y hy)) (K.chart_subset y) (K.eq_of_mem hy) :
          ↥(K.pt (K.mem_O hy) (K.smooth i y hy)).T →L[ℝ] ↥(K.pt (K.mem_O hy) (K.smooth i y hy)).K) :
        ↥(K.pt (K.mem_O hy) (K.smooth i y hy)).T →ₗ[ℝ]
          ↥(K.pt (K.mem_O hy) (K.smooth i y hy)).K)).map
      ((K.pt (K.mem_O hy) (K.smooth i y hy)).T.subtypeL :
        ↥(K.pt (K.mem_O hy) (K.smooth i y hy)).T →ₗ[ℝ]
          (K.pt (K.mem_O hy) (K.smooth i y hy)).c.φ.model.E 0)) = K.dim i := by
  obtain ⟨N', hN', -, hn⟩ := exists_submodule_chartVec_image
    (K.pt (K.mem_O hy) (K.smooth i y hy)).c.isChart (K.isSubmanifoldOfDim i).1
    ((K.isSubmanifoldOfDim i).2 y hy) (K.mem_chart (K.mem_O hy))
  have h := (kerSet_eq_coe_map_ker hf.isScSmooth (K.isScPlus i)
    (K.pt (K.mem_O hy) (K.smooth i y hy)) (K.chart_subset y) (K.eq_of_mem hy)).symm.trans
    ((K.ker_eq hy).symm.trans hN'.symm)
  rw [SetLike.coe_injective h]
  exact hn

/-! ### The oriented tangent sets `(T_yMᵢ, o_{i,y})` -/

variable (hf : A.B.IsScFredholmSection f) (hsec : A.B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy)

/-- **The positive frames of `T_yMᵢ` for `o_{i,y}`** (2021 pp. 701–702): the frames of `T_yMᵢ`
whose chart vectors are a basis of `ker (f − sᵢ)'(y)` positive for the orientation induced by
`o_y`, read in the chart `K.chart y`; empty for `y ∉ Mᵢ`. -/
def frames (i : K.ι) (y : A.Obj) : Set (Fin (K.dim i) → A.X.PObj.TangentSpace) :=
  {v | ∃ hy : y ∈ K.M i, v ∈ kerFrames hf K.isOpen_O (K.isScPlus i)
    (K.pt (K.mem_O hy) (K.smooth i y hy)) (K.chart_subset y) (K.eq_of_mem hy) (K.smooth i y hy)
    hsec (K.surj hf hy)
    (toChartOr hf (K.smooth i y hy) (K.chart y) (K.isChart_chart y) (K.mem_chart (K.mem_O hy))
      (o y (K.smooth i y hy)))
    (A.X.PObj.submanifoldTangent (K.M i) y) (K.finrank_ker hf hy)}

theorem frames_eq {i : K.ι} {y : A.Obj} (hy : y ∈ K.M i) :
    K.frames hf hsec o i y = kerFrames hf K.isOpen_O (K.isScPlus i)
      (K.pt (K.mem_O hy) (K.smooth i y hy)) (K.chart_subset y) (K.eq_of_mem hy) (K.smooth i y hy)
      hsec (K.surj hf hy)
      (toChartOr hf (K.smooth i y hy) (K.chart y) (K.isChart_chart y) (K.mem_chart (K.mem_O hy))
        (o y (K.smooth i y hy)))
      (A.X.PObj.submanifoldTangent (K.M i) y) (K.finrank_ker hf hy) := by
  ext v
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hy, h⟩⟩

/-- **`(T_yMᵢ, o_{i,y})`**, the oriented tangent space of the sheet `Mᵢ` at `y` with the
orientation induced by `o_y`. -/
def orTangent (i : K.ι) (y : A.Obj) : A.X.PObj.OrTangent :=
  ⟨K.dim i, A.X.PObj.submanifoldTangent (K.M i) y, K.frames hf hsec o i y⟩

/-- **`(T_yMᵢ, o_{i,y})` is an oriented finite-dimensional subspace of `T_yX`** (2021 p. 422,
Chapter 9's `IsOrientedAt`). -/
theorem isOrientedAt {i : K.ι} {y : A.Obj} (hy : y ∈ K.M i) :
    A.X.PObj.IsOrientedAt y (K.orTangent hf hsec o i y) := by
  unfold orTangent
  rw [K.frames_eq hf hsec o hy]
  exact isOrientedAt_kerFrames hf K.isOpen_O (K.isScPlus i) _ (K.chart_subset y) (K.eq_of_mem hy)
    (K.smooth i y hy) hsec (K.surj hf hy) _ (fun α hα => hα.1) (K.ker_eq hy) (K.finrank_ker hf hy)

/-! ### The formula of Theorem 15.4.1 in `Ĝr(y)` -/

open scoped Classical in
/-- **`T̂(y) = ∑_{i : y ∈ Mᵢ} σᵢ · (T_yMᵢ, o_{i,y})`**, the formula of Theorem 15.4.1 in
Chapter 9's oriented formal sums. -/
def canonSum (y : A.Obj) : A.X.PObj.OrTangent →₀ ℚ :=
  ∑ i with y ∈ K.M i, Finsupp.single (K.orTangent hf hsec o i y) (K.σ i)

open scoped Classical in
theorem canonSum_apply (y : A.Obj) (g : A.X.PObj.OrTangent) :
    K.canonSum hf hsec o y g =
      ∑ i with y ∈ K.M i, if K.orTangent hf hsec o i y = g then K.σ i else 0 := by
  rw [canonSum, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => Finsupp.single_apply

/-- **`T̂(y) ∈ Ĝr(y)`** (Theorem 15.4.1: the lift takes values in `Ĝr(X)`). -/
theorem canonSum_mem (y : A.Obj) : K.canonSum hf hsec o y ∈ A.X.GrHat y := by
  classical
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · rw [K.canonSum_apply]
    exact Finset.sum_nonneg fun i _ => by split_ifs; exacts [(K.σ_pos i).le, le_rfl]
  · have : ∃ i, y ∈ K.M i ∧ K.orTangent hf hsec o i y = g := by
      by_contra h
      push Not at h
      exact (Finsupp.mem_support_iff.1 hg) (by
        rw [K.canonSum_apply]
        exact Finset.sum_eq_zero fun i hi => if_neg (h i (Finset.mem_filter.1 hi).2))
    obtain ⟨i, hyi, rfl⟩ := this
    exact K.isOrientedAt hf hsec o hyi

open scoped Classical in
/-- **`f(T̂(y)) = ∑_{i : y ∈ Mᵢ} σᵢ · T_yMᵢ`**: the sum lifts the tangent sum of `Θ`
(Theorem 15.4.1: `T̂` is a lift of `T_Θ`). -/
theorem grForget_canonSum (y : A.Obj) :
    A.X.grForget (K.canonSum hf hsec o y) =
      ∑ i with y ∈ K.M i, Finsupp.single (A.X.PObj.submanifoldTangent (K.M i) y) (K.σ i) := by
  rw [canonSum, grForget, Finsupp.mapDomain_finsetSum]
  exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_single

/-- **Off the support the sum is zero**: for `y ∈ U(x)` with `Θ(y) = 0` no sheet contains `y`. -/
theorem canonSum_eq_zero {y : A.Obj} (hy : y ∈ K.U)
    (hΘ : y ∉ EpGroupoid.supp (fun z => (Λ (f z) : ℚ))) : K.canonSum hf hsec o y = 0 := by
  classical
  have hsum := K.eq_sum y hy
  have h0 : (∑ i with y ∈ K.M i, K.σ i) = 0 := by
    have hle : ((Λ (f y) : ℚ≥0) : ℚ) ≤ 0 := not_lt.1 hΘ
    exact le_antisymm (hsum ▸ hle) (Finset.sum_nonneg fun i _ => (K.σ_pos i).le)
  have hempty : (Finset.univ.filter fun i => y ∈ K.M i) = ∅ := by
    by_contra hne
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => (K.σ_pos j).le).1 h0 i hi
    exact (K.σ_pos i).ne' this
  rw [canonSum, hempty, Finset.sum_empty]

/-! ### Continuity and the oriented structure -/

/-- **Continuity of `y ↦ o_{i,y}` along the sheets** (Definition 9.3.2, Remark 9.3.3): near every
point of a sheet `Mᵢ` of positive dimension there are a chart and a frame field of `T_yMᵢ`,
positive for `o_{i,y}`, whose chart vectors depend continuously on `y`. -/
def FramesContinuous : Prop :=
  ∀ i, 0 < K.dim i → ∀ y ∈ K.M i, ∃ (φ : MChart A.Obj) (hφ : A.X.PObj.IsChart φ) (V : Set A.Obj),
    IsOpen V ∧ y ∈ V ∧ V ⊆ φ.source ∧ ∃ e : A.Obj → Fin (K.dim i) → A.X.PObj.TangentSpace,
      (∀ z ∈ K.M i ∩ V, e z ∈ K.frames hf hsec o i z) ∧
        ContinuousOn (fun z j => chartVec hφ (e z j)) (K.M i ∩ V)

variable {hf hsec o}

/-- **The orientation `oᵢ` of the sheet `Mᵢ` induced by `o`** (Definition 15.4.2), a
`SubmanifoldOrientation` of Chapter 9, given the continuity along the sheets. -/
def orient (hc : K.FramesContinuous hf hsec o) (i : K.ι) :
    A.X.PObj.SubmanifoldOrientation (K.M i) (K.dim i) where
  frames := K.frames hf hsec o i
  isOrientedAt _ hy := K.isOrientedAt hf hsec o hy
  continuous hn y hy := hc i hn y hy

/-- The oriented local branching structure `(Mᵢ, oᵢ)`, `(σᵢ)`. -/
def toOriented (hc : K.FramesContinuous hf hsec o) :
    A.X.OrientedBranchingStructure (fun z => (Λ (f z) : ℚ)) x where
  toLocalBranchingStructure := K.toLocalBranchingStructure
  dim := K.dim
  isSubmanifoldOfDim := K.isSubmanifoldOfDim
  orient := K.orient hc

/-- **The sum (9.9) of the oriented structure is the formula of Theorem 15.4.1.** -/
theorem orientedSum_toOriented (hc : K.FramesContinuous hf hsec o) (y : A.Obj) :
    (K.toOriented hc).orientedSum y = K.canonSum hf hsec o y := rfl

/-- The oriented tame branching structure of dimension `n` when all sheets have dimension `n`. -/
def toOrientedTame (hc : K.FramesContinuous hf hsec o) {n : ℕ} (hn : ∀ i, K.dim i = n) :
    A.X.OrientedTameStructure n (fun z => (Λ (f z) : ℚ)) x where
  toTameBranchingStructure := K.toTameBranchingStructure
  isSubmanifoldOfDim i := hn i ▸ K.isSubmanifoldOfDim i
  orient i := hn i ▸ K.orient hc i

theorem tangent_cast_aux {M : Set A.Obj} {d n : ℕ} (h : d = n)
    (so : A.X.PObj.SubmanifoldOrientation M d) (y : A.Obj) :
    (h ▸ so).tangent y = so.tangent y := by
  subst h; rfl

/-- **The oriented tame structure represents every `T` given on `U(x)` by the formula of
Theorem 15.4.1** (`OrientedTameStructure.Represents`, (9.9)). -/
theorem represents_toOrientedTame (hc : K.FramesContinuous hf hsec o) {n : ℕ}
    (hn : ∀ i, K.dim i = n) {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}
    (hT : ∀ y ∈ K.U, y ∈ A.X.PObj.smoothSet → T y = K.canonSum hf hsec o y) :
    (K.toOrientedTame hc hn).Represents T := by
  classical
  intro y hy hys
  rw [hT y hy hys]
  change _ = ∑ i with y ∈ K.M i, Finsupp.single ((hn i ▸ K.orient hc i).tangent y) (K.σ i)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tangent_cast_aux]
  rfl

end KernelBranching

/-! ### The canonical orientation as a section of `Ĝr(X)` -/

section Global

variable {f : A.Obj → A.W} (Λ : A.W → ℚ≥0) (hf : A.B.IsScFredholmSection f)
  (hsec : A.B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy)

open Classical in
/-- **Definition 15.4.2 (2021 p. 702; 2017: Definition 15.7), in `Ĝr(X)`**: the canonical lift
`T̂_((f, o), Λ)`, `y ↦ ∑_{i : y ∈ Mᵢ} σᵢ · (T_yMᵢ, o_{i,y})` computed in a local branching
structure described by kernels around `y`, and `0` where there is none. -/
def canonicalOrientation (y : A.Obj) : A.X.PObj.OrTangent →₀ ℚ :=
  if h : ∃ (x : A.Obj) (K : KernelBranching A f Λ x), y ∈ K.U then
    h.choose_spec.choose.canonSum hf hsec o y
  else 0

/-- **The formula of Theorem 15.4.1 does not depend on the local structure**: two structures
described by kernels give the same sum at a common smooth point. -/
def CanonIndependent : Prop :=
  ∀ (x x' : A.Obj) (K : KernelBranching A f Λ x) (K' : KernelBranching A f Λ x') (y : A.Obj),
    y ∈ K.U → y ∈ K'.U → y ∈ A.X.PObj.smoothSet →
      K.canonSum hf hsec o y = K'.canonSum hf hsec o y

/-- **The formula of Theorem 15.4.1 is carried by morphisms**: `Tφ` maps the sum at `s(φ)` to the
sum at `t(φ)` (the naturality of a section functor of `Ĝr(X)`). -/
def CanonNatural : Prop :=
  ∀ (φ : A.Mor), A.X.src φ ∈ A.X.PObj.smoothSet → ∀ (x x' : A.Obj)
    (K : KernelBranching A f Λ x) (K' : KernelBranching A f Λ x'), A.X.src φ ∈ K.U →
      A.X.tgt φ ∈ K'.U →
        A.X.grHatPush φ (K.canonSum hf hsec o (A.X.src φ)) = K'.canonSum hf hsec o (A.X.tgt φ)

/-- **`y ↦ o_{i,y}` is continuous along the sheets** of every structure described by kernels. -/
def CanonContinuous : Prop :=
  ∀ (x : A.Obj) (K : KernelBranching A f Λ x), K.FramesContinuous hf hsec o

variable {Λ hf hsec o}

theorem canonicalOrientation_eq (hind : CanonIndependent Λ hf hsec o) {x : A.Obj}
    (K : KernelBranching A f Λ x) {y : A.Obj} (hy : y ∈ K.U) (hys : y ∈ A.X.PObj.smoothSet) :
    canonicalOrientation Λ hf hsec o y = K.canonSum hf hsec o y := by
  have h : ∃ (x : A.Obj) (K : KernelBranching A f Λ x), y ∈ K.U := ⟨x, K, hy⟩
  unfold canonicalOrientation
  rw [dif_pos h]
  exact hind _ _ _ K y h.choose_spec.choose_spec hy hys

theorem canonicalOrientation_mem (y : A.Obj) :
    canonicalOrientation Λ hf hsec o y ∈ A.X.GrHat y := by
  unfold canonicalOrientation
  split_ifs with h
  · exact KernelBranching.canonSum_mem _ hf hsec o y
  · exact A.X.zero_mem_GrHat y

theorem canonicalOrientation_eq_zero {y : A.Obj}
    (hΘ : y ∉ EpGroupoid.supp (fun z => (Λ (f z) : ℚ))) :
    canonicalOrientation Λ hf hsec o y = 0 := by
  unfold canonicalOrientation
  split_ifs with h
  · exact KernelBranching.canonSum_eq_zero _ hf hsec o h.choose_spec.choose_spec hΘ
  · rfl

variable (Λ hf hsec o) in
/-- **`T` is the canonical orientation of `Θ = Λ ∘ f` for `(f, o)`** (Definition 15.4.2): it is an
orientation of `Θ` (Definition 9.3.2), and near every point of the support it is represented by
the oriented tame branching structure of dimension `n` of a structure `K` described by kernels:
the sheets are the solution sets `Mᵢ = {f = sᵢ}`, oriented by the frames `o_{i,y}` induced by
`o`. -/
def IsCanonicalFor (n : ℕ) (T : A.Obj → A.X.PObj.OrTangent →₀ ℚ) : Prop :=
  A.X.IsOrientation (fun z => (Λ (f z) : ℚ)) T ∧
    ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ (K : KernelBranching A f Λ x) (hc : K.FramesContinuous hf hsec o)
        (hn : ∀ i, K.dim i = n), (K.toOrientedTame hc hn).Represents T

/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6) in `Ĝr(X)`, from the three properties of
the formula**: let `f` be an sc-Fredholm section functor with tame germ data, `o_y ∈ Or_y^f` a
family of orientations, and `Λ` an sc⁺-multisection such that every point of `supp(Λ ∘ f)` has a
local branching structure described by kernels with all sheets of dimension `n` (`hdim`; such
structures exist at points of good position, `exists_kernelBranching`).  If the formula
`∑ σᵢ · (T_yMᵢ, o_{i,y})` does not depend on the local structure (`CanonIndependent`), is carried
by morphisms (`CanonNatural`) and `o_{i,y}` is continuous along the sheets (`CanonContinuous`),
then, with the independence of Theorem 9.2.1 (`hTS`), `canonicalOrientation` is an orientation of
`Θ = Λ ∘ f` (Definition 9.3.2), and it is the canonical one (`IsCanonicalFor`). -/
theorem theorem_15_4_1_of_local (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hΛ : IsScPlusMultisection A Λ) {n : ℕ}
    (hdim : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ K : KernelBranching A f Λ x, ∀ i, K.dim i = n)
    (hTS : A.X.HasIndependentTangentSums (fun z => (Λ (f z) : ℚ)))
    (hind : CanonIndependent Λ hf hsec o) (hnat : CanonNatural Λ hf hsec o)
    (hcont : CanonContinuous Λ hf hsec o) :
    IsCanonicalFor Λ hf hsec o n (canonicalOrientation Λ hf hsec o) := by
  have hloc : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ K : KernelBranching A f Λ x, (∀ i, K.dim i = n) ∧ ∀ y ∈ K.U, y ∈ A.X.PObj.smoothSet →
        canonicalOrientation Λ hf hsec o y = K.canonSum hf hsec o y := fun x hx => by
    obtain ⟨K, hK⟩ := hdim x hx
    exact ⟨K, hK, fun y hy hys => canonicalOrientation_eq hind K hy hys⟩
  have hfun := isFunctorial_comp hF hΛ
  refine ⟨IsOrientation.mk' hTS (fun x _ => canonicalOrientation_mem x) (fun φ hφ => ?_)
    (fun x _ hx => canonicalOrientation_eq_zero hx) (fun x hx => ?_), fun x hx => ?_⟩
  · by_cases hs : A.X.src φ ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ))
    · have ht : A.X.tgt φ ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)) := by
        change (0 : ℚ) < _
        rw [← hfun φ]; exact hs
      obtain ⟨K, -, hK⟩ := hloc _ hs
      obtain ⟨K', -, hK'⟩ := hloc _ ht
      have hts : A.X.tgt φ ∈ A.X.PObj.smoothSet :=
        mem_smoothSet_of_pos hft hΛ (by exact_mod_cast ht)
      rw [hK _ K.mem_U hφ, hK' _ K'.mem_U hts]
      exact hnat φ hφ _ _ K K' K.mem_U K'.mem_U
    · have ht : A.X.tgt φ ∉ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)) := fun h => hs (by
        change (0 : ℚ) < _
        rw [hfun φ]; exact h)
      rw [canonicalOrientation_eq_zero hs, canonicalOrientation_eq_zero ht, grHatPush,
        Finsupp.mapDomain_zero]
  · obtain ⟨K, -, hK⟩ := hloc x hx
    exact ⟨K.toOriented (hcont x K), fun y hy hys => hK y hy hys⟩
  · obtain ⟨K, hn, hK⟩ := hloc x hx
    exact ⟨K, hcont x K, hn, K.represents_toOrientedTame _ _ hK⟩

end Global

end SBLocalization

end Polyfold
