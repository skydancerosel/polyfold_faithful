import Polyfold.Chapter15.GoodPositionBranches
import Polyfold.Chapter11.FaceIntersectionCounterexample

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.2, p. 690:
**Theorem 15.2.5**, closing sentence (2017: Theorem 15.3), the general position variant.

# The boundary local perturbation theorem under general position

## The text, paraphrased

(Theorem 15.2.5, last sentence) The conclusion of Theorem 15.2.5 also holds if the good position
requirement (2) is replaced by the general position requirement that the restrictions of
`T(f,Λ)(y)` to the reduced tangent spaces `T^R_yX` are surjective (cf. Definition 15.3.5).

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IsReducedOntoAtLevel f Λ x` and `IsInGeneralPositionAt f Λ x`: Definition 15.3.5 at one point
  (every operator of `T(f,Λ)(x)` is onto `W_x` on `T^R_xX`, in every chart and presentation);
  `isInGeneralPosition_iff_forall_at`: Definition 15.3.5 is this condition at every point of
  `supp(Λ ∘ f)`.
* Part I, `StrongBundle.linKer_sup_reduced_eq_of_isGeneralPositionAt`: if the solution set of a
  section contains a smooth submanifold in general position at `y` (Definition 4.2.10), then in
  **every** strong bundle chart around `y`, `ker Lin(z) + T^R_zO = T_zO` (the converse direction
  of the chart criterion `isGeneralPositionGerm_of_sup_eq`).
* `isGeneralPositionGerm_branch_at`, `isGoodPositionAt_of_isInGeneralPositionAt`: general position
  at one point gives Part I's general position of every branch `(f − sᵢ)|O` through `f(x)`, and
  good position (Definition 15.2.4) at `x` (the pointwise form of wave 3's Remark 15.3.6).
* `isReducedOntoAtLevel_of_isGeneralPositionGerm`: conversely, if every branch through `f(y)` of a
  local section structure is in general position at `y` in Part I's sense, then `(f, Λ)` is in
  general position at `y` (Definition 15.3.5): the reduced operators are onto in every chart.
* **`theorem_15_2_5_generalPosition_hyp`**: over a tame ep-groupoid, if `Λ(f(x)) > 0` and `(f, Λ)`
  is in general position at `x`, then all conclusions of `theorem_15_2_5_hyp` hold on a natural
  representation `U(x)`, and in addition `(f, Λ)` is in general position at every
  `y ∈ U(x)` with `Λ(f(y)) > 0` (the clause (2) of the text's variant).

## Reading

* "The same conclusion holds if (2) is replaced by general position" is read: the hypothesis
  "good position at `x`" is replaced by "general position at `x`" (reduced linearization onto at
  `x`), and the conclusion (2) by "general position at every point of `M_{U(x)}`". Good position at
  `x` and on `M_{U(x)}` still holds (Part I's Lemma 5.26), so both forms of (2) are given.
* The text asks for a tame ep-groupoid in Definition 15.3.5; the tameness of `X` enters through the
  openness of general position along the solution set (Part I's
  `exists_isOpen_isGeneralPositionGerm`, Theorem 4.2.11 (3)).
* As in §15.2 the section has germ data in tame charts (`IsScFredholmSectionTame`, the inherited
  Part I hypothesis of Theorem 3.6.8).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u v

/-! ### Part I: general position of a submanifold of zeros, in every chart -/

section PartI

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr MPolyfold

/-- **`ker Lin(z) + T^R_zO = T_zO` in every chart** (the converse of the chart criterion
`isGeneralPositionGerm_of_sup_eq`, at level `0`): if a smooth submanifold `A` of the solution set
of `f` (Definition 4.2.1) is in general position at `y` (Definition 4.2.10), then in every strong
bundle chart `c` around `y`, at every level-`1` point `z` over `φ(y)` and for every presentation
`T` of the partial quadrant, `ker Lin(z) + T^R_zO = T_zO`.  *Proof*: as in
`isGoodPositionGermTame_of_isGeneralPositionAt`: `T_zA ⊆ ker Lin(z)` and `T_zA + B = T_zO` with
`B ⊆ T^R_zO`. -/
theorem StrongBundle.linKer_sup_reduced_eq_of_isGeneralPositionAt (hf : B.IsScSmoothSection f)
    {y : X} {A : Set X} (hA : PX.IsSmoothSubmanifold A) (hAS : A ⊆ solutionSet P f)
    (hgpA : PX.IsGeneralPositionAt A y) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyV : y ∈ c.φ.source) {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y) {n : ℕ}
    {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) :
    c.linKer f z ⊔ reducedTangentSpaceWith (c.isRetraction.baseRetraction c.relOpen) T z =
      LinearMap.range (scDeriv (c.isRetraction.baseRetraction c.relOpen).U
        (c.isRetraction.baseRetraction c.relOpen) z :
          c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) := by
  have hyA : y ∈ A := hgpA.1
  set d := hA.data hyA with hd
  obtain ⟨N, M, Bs, hN, hM, hBM, -, hsplit⟩ :=
    hgpA.isGeneralPositionChart d c.isChart T hT (hA.mem_data_V hyA) hyV hz
  set R := c.isRetraction.baseRetraction c.relOpen with hRdef
  have hyO : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model y hyV
  have hzR : z ∈ c.φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, c.base_retract, hz]; exact hyO
  have hTO : tangentSpace c.φ.model.E c.φ.model.C c.φ.model.O z =
      ↑(LinearMap.range (scDeriv R.U R z : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0)) := by
    rw [← c.base_retract]; exact tangentSpace_eq_coe_submodule R hzR
  have hMeq : M = LinearMap.range (scDeriv R.U R z : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) :=
    SetLike.coe_injective (hM.trans hTO)
  have hQ := d.toSubData.isScRetract_image c.φ c.isChart
  have hQO : c.φ '' (d.toSubData.shrink c.φ ∩ A) ⊆ c.φ.model.O := by
    rintro _ ⟨y', hy', rfl⟩; exact c.φ.mapsTo_model y' (d.toSubData.shrink_subset_source c.φ hy'.1)
  have hQ0 : ∀ u ∈ c.φ '' (d.toSubData.shrink c.φ ∩ A), c.principal f u = 0 := by
    rintro _ ⟨y', hy', rfl⟩
    exact (c.isZeroAt_iff hf.1 (d.toSubData.shrink_subset_source c.φ hy'.1)).1 (hAS hy'.2)
  have hzQ : z ∈ c.φ.model.E.lvlSet (c.φ '' (d.toSubData.shrink c.φ ∩ A)) 1 := by
    rw [ScBanach.mem_lvlSet, hz]
    exact ⟨y, ⟨d.toSubData.mem_shrink c.φ hyA (hA.mem_data_V hyA) hyV, hyA⟩, rfl⟩
  have hNK : N ≤ c.linKer f z := fun v hv =>
    tangentSpace_subset_linKer hf hc hQ hQO hQ0 hzQ (by rw [← hN]; exact hv)
  have hKM : c.linKer f z ≤ M := by rw [hMeq]; exact c.linKer_le f z
  have h0 := hsplit 0
  rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero, ScBanach.levelSub_zero] at h0
  have hBT : Bs ≤ reducedTangentSpaceWith R T z := by
    rw [reducedTangentSpaceWith, ← hMeq]; exact hBM
  have hTM : reducedTangentSpaceWith R T z ≤ M := by
    rw [reducedTangentSpaceWith, ← hMeq]; exact inf_le_left
  rw [← hMeq]
  refine le_antisymm (sup_le hKM hTM) ?_
  rw [← h0.2]
  exact sup_le_sup hNK hBT

end PartI

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### Definition 15.3.5 at one point -/

/-- **The reduced linearization is onto at `x ∈ X₁`** (Definition 15.3.5 at one point): every
operator `L` of `T(f,Λ)(x)` restricted to `T^R_xX` is onto `W_x`, with `T^R_xX` read in any chart
and presentation. -/
def IsReducedOntoAtLevel (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) (x : A.X.PObj.Level 1) : Prop :=
  ∀ L ∈ (linearization f Λ x).support, ∀ (φ : MChart A.Obj) (hφ : A.X.PObj.IsChart φ)
    (hx : A.X.PObj.levelVal 1 x ∈ φ.source) (k : ℕ) (V : ScBanach)
    (T : ScIso φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V)),
    φ.model.C = T 0 ⁻¹' quadrant k V 0 →
      Surjective (L.domRestrict (reducedTangentFiber hφ hx T))

/-- **`(f, Λ)` is in general position at `x`** (Definition 15.3.5 at one point, the requirement
of the closing sentence of Theorem 15.2.5): `x ∈ X₁` and the reduced linearization is onto. -/
def IsInGeneralPositionAt (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) (x : A.Obj) : Prop :=
  ∃ hx : x ∈ A.X.PObj.levelSet 1, IsReducedOntoAtLevel f Λ (A.X.PObj.levelMk 1 x hx)

/-- **Definition 15.3.5 is general position at every point of `supp(Λ ∘ f)`.** -/
theorem isInGeneralPosition_iff_forall_at {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) :
    IsInGeneralPosition A f Λ ↔ ∀ x, 0 < Λ (f x) → IsInGeneralPositionAt f Λ x := by
  constructor
  · intro h x hx
    exact ⟨mem_levelSet_one_of_pos hf hΛ hx, h _ hx⟩
  · intro h x hx
    obtain ⟨_, hred⟩ := h _ hx
    exact hred

/-! ### General position at one point gives good position -/

/-- **Every branch through `f(x)` is in general position** (Part I's Definition 5.3.9 for
`(f − sᵢ)|O`) at a point `x` where `(f, Λ)` is in general position: the pointwise form of
`isGeneralPositionGerm_branch`. -/
theorem isGeneralPositionGerm_branch_at {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} {x : A.X.PObj.Level 1}
    (hgp : IsReducedOntoAtLevel f Λ x) {O : Set A.Obj} (hO : IsOpen O) {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (hrep : IsLocalRepOn A Λ O s σ)
    (hxO : A.X.PObj.levelVal 1 x ∈ O) {i : Fin k}
    (hi : s i (A.X.PObj.levelVal 1 x) = f (A.X.PObj.levelVal 1 x)) [Nonempty O]
    [ParacompactSpace O] [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))] :
    (A.B.restrictOpen hO).IsGeneralPositionGerm
      (subRestrict (O := O) f (s i) hft.isScSmooth.1) ⟨A.X.PObj.levelVal 1 x, hxO⟩ := by
  classical
  set y := A.X.PObj.levelVal 1 x with hy
  have hxs : y ∈ A.X.PObj.smoothSet := mem_smoothSet_of_eq hft hO (hrep.2.1 i) hxO hi.symm
  obtain ⟨-, c₀, hc₀, hxc₀, hφ0, -⟩ := hft.germTame y hxs
  set c := c₀.restrictInter hO with hcdef
  have hc : A.B.IsTameChart c := hc₀.restrictInter hO
  have hsub : c.φ.source ⊆ O := c₀.restrictInter_source_subset hO
  have hxc : y ∈ c.φ.source := ⟨hxc₀, hxO⟩
  have hφ0c : c.φ y = 0 := hφ0
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  let d : LocalLinData A Λ x := ⟨O, hO, k, s, σ, hrep, c, hc.1, hsub, hxc⟩
  have hL : toIntr c hxc (subDeriv c f (s i) (levelLift c.φ 1 y)) ∈
      (linearization f Λ x).support := by
    rw [linearization_eq hf d]
    exact (mem_support_linSumIntr_iff hf.1.1.1 hrep.1 (fun j => (hrep.2.1 j).1) hsub hxc _).2
      ⟨i, hi, rfl⟩
  exact isGeneralPositionGerm_subRestrict hft hO (hrep.2.1 i) hc hsub hxc hφ0c hi.symm T hT
    (hgp _ hL c.φ c.isChart hxc n Wq T hT)

/-- **General position at `x` gives good position at `x`** (Definition 15.2.4), the pointwise form
of `remark_15_3_6_goodPosition_hyp` (a): Part I's Lemma 5.26 per branch. -/
theorem isGoodPositionAt_of_isInGeneralPositionAt {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) {x : A.Obj} (hpos : 0 < Λ (f x))
    (hgp : IsInGeneralPositionAt f Λ x) : IsGoodPositionAt f Λ x := by
  obtain ⟨hx1, hred⟩ := hgp
  refine ⟨hpos, ⟨hx1, fun L hL w => ?_⟩, ?_⟩
  · obtain ⟨φ, hφ, hxφ, k, V, T, hT⟩ :=
      exists_chart_presentation (A := A) (A.X.PObj.levelMk 1 x hx1)
    obtain ⟨α, hα⟩ := hred L hL φ hφ hxφ k V T hT w
    exact ⟨α, hα⟩
  · obtain ⟨O, k, s, σ, hO, hxO, hrep⟩ := hΛ.exists_isLocalRepOn x
    refine ⟨O, hO, hxO, k, s, σ, hrep, fun i hi => ?_⟩
    have : Nonempty O := ⟨⟨x, hxO⟩⟩
    have := A.X.PObj.paracompactSpace_subtype O
    have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
      (A.X.PObj.restrictOpen hO) A.B
    have hg := isGeneralPositionGerm_branch_at (x := A.X.PObj.levelMk 1 x hx1) hf hft hred hO
      hrep hxO hi
    have h0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
        (subRestrict (O := O) f (s i) hft.isScSmooth.1) ⟨x, hxO⟩ := by
      unfold subRestrict
      rw [isZeroAt_restrictSection_iff]
      exact (isZeroAt_subSec_iff hft.isScSmooth.1 (hrep.2.1 i).1 hxO).2 hi.symm
    exact ⟨hft.isScSmooth.1,
      hg.isGoodPositionGermTame (isScFredholmSectionTame_subRestrict hO hft (hrep.2.1 i)) h0⟩

/-! ### Part I general position of the branches gives Definition 15.3.5 -/

section Converse

variable {O : Set A.Obj} (hO : IsOpen O) [Nonempty O] [ParacompactSpace O]
  [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))]

include hO in
set_option maxHeartbeats 1600000 in
-- the chart assembly of the converse of `isGeneralPositionGerm_subRestrict`
/-- **One branch, in a chart**: if `(f − s)|O` is in general position at `y` (Part I's
Definition 5.3.9 on `W|O`) and `c` is a chart of `W` around `y` with domain in `O`, then the
chart operator `D((f̂ − ŝ) ∘ r)(z)` maps `T_zO ∩ T^R_zO` onto the fibre `K_z`. -/
theorem exists_reduced_preimage_of_isGeneralPositionGerm {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) {s : A.Obj → A.W} (hs : IsScPlusSectionOn A s O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O)
    {y : A.Obj} (hy : y ∈ c.φ.source) (hfs : f y = s y)
    (hG : (A.B.restrictOpen hO).IsGeneralPositionGerm (subRestrict (O := O) f s hft.isScSmooth.1)
      ⟨y, hsub hy⟩)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) {k : c.F 0} (hk : (c.φ y, k) ∈ c.K) :
    ∃ w ∈ reducedTangentSpaceWith (c.isRetraction.baseRetraction c.relOpen) T z,
      w ∈ rangeS (scDeriv c.U (r c.R) z) ∧ subDeriv c f s z w = k := by
  classical
  set g := subRestrict (O := O) f s hft.isScSmooth.1 with hg
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs
  have hy0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj)) g ⟨y, hsub hy⟩ := by
    rw [hg]
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hft.isScSmooth.1 hs.1 (hsub hy)).2 hfs
  have hgood := hG.isGoodPositionGermTame hgO hy0
  obtain ⟨V, -, hyV, -, hA, hiff, -⟩ := exists_isGeneralPositionGerm_iff hgO hgood hy0
  have hgpA := (hiff _ hyV hy0).1 hG
  set q₀ := g ⟨y, hsub hy⟩ with hq₀
  set c' := c.restrictTo A.B.continuous hO hsub q₀ with hc'
  have hc'c : (A.B.restrictOpen hO).IsChart c' := restrictOpen_isChart_restrictTo hO hc hsub q₀
  have hyc' : (⟨y, hsub hy⟩ : O) ∈ c'.φ.source := hy
  have hz' : c'.φ.model.E.toBase 1 z = c'.φ ⟨y, hsub hy⟩ := hz
  have hsup := linKer_sup_reduced_eq_of_isGeneralPositionAt hgO.isScSmooth hA inter_subset_left
    hgpA hc'c hyc' hz' T hT
  have hsurj := hG.isLinSurjAt.linAt_surjective hgO.isScSmooth hy0 hc'c hyc' hz'
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model _ hy
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have hD : scDeriv c.U (c'.principal g ∘ r c.R) z = subDeriv c f s z :=
    scDeriv_restrictTo_subRestrict hO hft hs hc hsub q₀ hzU
  obtain ⟨⟨v, hv⟩, hvk⟩ := hsurj k hk
  have hv' : v ∈ c'.linKer g z ⊔ reducedTangentSpaceWith
      (c.isRetraction.baseRetraction c.relOpen) T z :=
    (congrArg (fun S : Submodule ℝ (c.φ.model.E 0) => v ∈ S) hsup).mpr hv
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv'
  obtain ⟨haR, ha0⟩ := (c'.mem_linKer_iff g z a).1 ha
  have hbR : b ∈ rangeS (scDeriv c.U (r c.R) z) := hb.1
  refine ⟨b, hb, hbR, ?_⟩
  have e1 : linAt c'.U c'.R (c'.principal g) z ⟨v, hv⟩ =
      linAt c'.U c'.R (c'.principal g) z ⟨a, haR⟩ +
        linAt c'.U c'.R (c'.principal g) z ⟨b, hbR⟩ := by
    rw [← map_add]
    congr 1
    exact Subtype.ext hab.symm
  rw [ha0, zero_add, hvk] at e1
  rw [e1]
  exact (congrArg (fun L : c.φ.model.E 0 →L[ℝ] c.F 0 => L b) hD).symm

include hO in
/-- **The intrinsic reduced operator of one branch is onto**: under the hypotheses of
`exists_reduced_preimage_of_isGeneralPositionGerm`, at `y ∈ X₁`, the operator
`(f − s)'(y) = toIntr c hy (D((f̂ − ŝ) ∘ r)(z))` of §15.1 is onto `W_y` on `T^R_yX`. -/
theorem surjective_reduced_toIntr_of_isGeneralPositionGerm {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) {s : A.Obj → A.W} (hs : IsScPlusSectionOn A s O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O)
    {y : A.X.PObj.Level 1} (hy : A.X.PObj.levelVal 1 y ∈ c.φ.source)
    (hfs : f (A.X.PObj.levelVal 1 y) = s (A.X.PObj.levelVal 1 y))
    (hG : (A.B.restrictOpen hO).IsGeneralPositionGerm (subRestrict (O := O) f s hft.isScSmooth.1)
      ⟨A.X.PObj.levelVal 1 y, hsub hy⟩) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) :
    Surjective ((toIntr c hy (subDeriv c f s (levelLift c.φ 1 (A.X.PObj.levelVal 1 y)))).domRestrict
      (reducedTangentFiber c.isChart hy T)) := by
  classical
  set z := levelLift c.φ 1 (A.X.PObj.levelVal 1 y) with hzdef
  have ha : c.φ.model.E.toBase 1 z = c.φ (A.X.PObj.levelVal 1 y) :=
    A.X.PObj.toBase_levelLift c.isChart hy (levelVal_mem y)
  set R := c.isRetraction.baseRetraction c.relOpen with hR
  have hR' : R.retract = c.φ '' c.φ.source := by rw [c.base_retract, c.φ.image_source]
  intro w
  by_cases hrange : ∀ α, chartOp c hy (subDeriv c f s z) α ∈ LinearMap.range (c.fiberLin hy)
  · have hk : (c.φ (A.X.PObj.levelVal 1 y), c.fiberLin hy w) ∈ c.K := by
      rw [← c.apply_fiberLin hy w, ← c.image_source]
      exact ⟨_, c.fiberLin_src hy w, rfl⟩
    obtain ⟨v, hvR, hv, hvk⟩ :=
      exists_reduced_preimage_of_isGeneralPositionGerm hO hft hs hc hsub hy hfs hG ha T hT hk
    have hvT : v ∈ tangentFiberModel c.isChart hy := (c.mem_tangentFiberModel_iff_rangeS hy v).2 hv
    set α := (tangentFiberEquiv c.isChart hy).symm ⟨v, hvT⟩ with hα
    have hαR : α ∈ reducedTangentFiber c.isChart hy T := by
      refine (mem_reducedTangentFiber_iff c.isChart hy T subset_rfl c.φ.isOpen_source hy R hR').2
        ?_
      rw [fiberCoord_eq_coe, hα, Equiv.apply_symm_apply]
      exact hvR
    refine ⟨⟨α, hαR⟩, c.fiberLin_injective hy ?_⟩
    change c.fiberLin hy (toIntr c hy (subDeriv c f s z) α) = c.fiberLin hy w
    rw [fiberLin_toIntr c hy hrange, chartOp_apply, hα, Equiv.apply_symm_apply]
    exact hvk
  · -- `toIntr = 0`; the full operator is onto, so the fibre is `0`
    have h0 : toIntr c hy (subDeriv c f s z) = 0 := by rw [toIntr, dif_neg hrange]
    have hon : ChartOnto c (subDeriv c f s z) z := by
      intro k hk
      rw [ha] at hk
      obtain ⟨v, -, hv, hvk⟩ :=
        exists_reduced_preimage_of_isGeneralPositionGerm hO hft hs hc hsub hy hfs hG ha T hT hk
      exact ⟨v, hv, hvk⟩
    have hfull := (surjective_toIntr_subDeriv_iff hft.isScSmooth hs hc hsub hy hfs).2 hon
    obtain ⟨β, hβ⟩ := hfull w
    rw [h0, LinearMap.zero_apply] at hβ
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact hβ

end Converse

/-- **Part I general position of the branches through `f(y)` gives Definition 15.3.5 at `y`**: for
a local section structure `(sᵢ, σᵢ)` of `Λ` on an open `O ∋ y` and a chart `c` around `y` with
domain in `O`, if every `(f − sⱼ)|O` with `sⱼ(y) = f(y)` is in general position at `y`
(Definition 5.3.9 on `W|O`), then `(f, Λ)` is in general position at `y`. -/
theorem isReducedOntoAtLevel_of_isGeneralPositionGerm {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} {O : Set A.Obj} (hO : IsOpen O) [Nonempty O] [ParacompactSpace O]
    [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))] {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (hrep : IsLocalRepOn A Λ O s σ)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O)
    {y : A.X.PObj.Level 1} (hy : A.X.PObj.levelVal 1 y ∈ c.φ.source)
    (hG : ∀ j, s j (A.X.PObj.levelVal 1 y) = f (A.X.PObj.levelVal 1 y) →
      (A.B.restrictOpen hO).IsGeneralPositionGerm
        (subRestrict (O := O) f (s j) hft.isScSmooth.1) ⟨A.X.PObj.levelVal 1 y, hsub hy⟩) :
    IsReducedOntoAtLevel f Λ y := by
  classical
  intro L hL φ hφ hxφ m V T hT
  obtain ⟨n, Wq, T₀, hT₀⟩ := c.φ.model.isPartialQuadrant
  have e := reducedTangentFiber_eq (hφ := c.isChart) (hx := hy) (T := T₀) (hψ := hφ)
    (hx' := hxφ) (T' := T) hT₀ hT
  rw [← e]
  let d : LocalLinData A Λ y := ⟨O, hO, k, s, σ, hrep, c, hc, hsub, hy⟩
  rw [linearization_eq hf d] at hL
  obtain ⟨j, hj, rfl⟩ :=
    (mem_support_linSumIntr_iff hf.1.1.1 hrep.1 (fun j => (hrep.2.1 j).1) hsub hy _).1 hL
  exact surjective_reduced_toIntr_of_isGeneralPositionGerm hO hft (hrep.2.1 j) hc hsub hy hj.symm
    (hG j hj) T₀ hT₀

/-! ### Theorem 15.2.5 under general position -/

open Classical in
/-- **Theorem 15.2.5 (2017: Theorem 15.3), p. 690, closing sentence: the general position
variant**, with the inherited hypothesis that `f` has germ data in tame charts (`hft`, as in
`theorem_15_2_5_hyp`). Over a tame ep-groupoid (Definition 15.3.5 asks for it), if
`Λ(f(x)) > 0` and `(f, Λ)` is in general position at `x` (the reduced linearization is onto), there
are a natural representation `U(x)`, a local sc⁺-section structure `(sᵢ, σᵢ)` on `O ⊇ U(x)` and a
chart `c` with `U(x) ⊆ dom(c) ⊆ O` such that, with `Mᵢ = {y ∈ U(x) | f(y) = sᵢ(y)}`: the `Mᵢ` are
smooth submanifolds (Definition 4.2.1), (1) properly embedded; `M_{U(x)} = ⋃ᵢ Mᵢ`; (2) at every
`y ∈ M_{U(x)}`, `(f, Λ)` is in general position (Definition 15.3.5 at `y`), and in good position
(Definition 15.2.4); (3) `Λ(f(y)) = ∑_{i : y ∈ Mᵢ} σᵢ` on `U(x)`; `T(f,Λ)` is read in `c`; only
branches through `f(x)` meet `U(x)`. -/
theorem theorem_15_2_5_generalPosition_hyp {f : A.Obj → A.W} (hX : A.X.IsTame)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) {x : A.Obj} (hpos : 0 < Λ (f x))
    (hgp : IsInGeneralPositionAt f Λ x) :
    ∃ (R : A.X.NaturalRep x) (O : Set A.Obj) (k : ℕ) (s : Fin k → A.Obj → A.W)
      (σ : Fin k → ℚ≥0) (c : StrongBundleChart A.X.PObj A.P),
      IsOpen O ∧ IsLocalRepOn A Λ O s σ ∧ A.B.IsChart c ∧ R.U ⊆ c.φ.source ∧ c.φ.source ⊆ O ∧
      (∀ i, A.X.PObj.IsSmoothSubmanifold {y ∈ R.U | f y = s i y}) ∧
      (∀ i, IsProperMap (inclusion (sep_subset R.U fun y => f y = s i y))) ∧
      {y ∈ R.U | 0 < Λ (f y)} = ⋃ i, {y ∈ R.U | f y = s i y} ∧
      (∀ y ∈ R.U, 0 < Λ (f y) → IsInGeneralPositionAt f Λ y ∧ IsGoodPositionAt f Λ y) ∧
      (∀ y ∈ R.U, Λ (f y) = ∑ i with f y = s i y, σ i) ∧
      (∀ (y : A.X.PObj.Level 1) (hy : A.X.PObj.levelVal 1 y ∈ c.φ.source),
        linearization f Λ y = linSumIntr c hy f s σ) ∧
      ∀ i, ∀ y ∈ R.U, f y = s i y → s i x = f x := by
  classical
  have hgx := isGoodPositionAt_of_isInGeneralPositionAt hf hft hΛ hpos hgp
  obtain ⟨R, O, k, s, σ, c, hO, hrep, hc, hRc, hsub, hS, -, hU, hG2, hcount, hlin, hthrough⟩ :=
    theorem_15_2_5_hyp hf hft hΛ hgx
  have hxO : x ∈ O := hsub (hRc R.mem_U)
  have : Nonempty O := ⟨⟨x, hxO⟩⟩
  have := A.X.PObj.paracompactSpace_subtype O
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
    (A.X.PObj.restrictOpen hO) A.B
  have hXO : (A.X.PObj.restrictOpen hO).IsTame := MPolyfold.isTame_restrictOpen _ hO hX
  obtain ⟨hx1, hred⟩ := hgp
  -- openness of Part I general position along each branch through `f(x)`
  have hW : ∀ i, ∃ Wi : Set A.Obj, IsOpen Wi ∧ x ∈ Wi ∧ ∀ y ∈ Wi, ∀ hyO : y ∈ O,
      f y = s i y → s i x = f x → (A.B.restrictOpen hO).IsGeneralPositionGerm
        (subRestrict (O := O) f (s i) hft.isScSmooth.1) ⟨y, hyO⟩ := by
    intro i
    by_cases hi : s i x = f x
    · have hg := isGeneralPositionGerm_branch_at (x := A.X.PObj.levelMk 1 x hx1) hf hft hred hO
        hrep hxO hi
      have hgO := isScFredholmSectionTame_subRestrict hO hft (hrep.2.1 i)
      have h0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
          (subRestrict (O := O) f (s i) hft.isScSmooth.1) ⟨x, hxO⟩ := by
        unfold subRestrict
        rw [isZeroAt_restrictSection_iff]
        exact (isZeroAt_subSec_iff hft.isScSmooth.1 (hrep.2.1 i).1 hxO).2 hi.symm
      obtain ⟨W, hWo, hxW, -, hall⟩ := exists_isOpen_isGeneralPositionGerm hXO hgO h0 hg
      refine ⟨Subtype.val '' W, hO.isOpenMap_subtype_val W hWo, ⟨_, hxW, rfl⟩, ?_⟩
      rintro y ⟨p, hpW, rfl⟩ hyO hfy -
      have h0y : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
          (subRestrict (O := O) f (s i) hft.isScSmooth.1) p := by
        unfold subRestrict
        rw [isZeroAt_restrictSection_iff]
        exact (isZeroAt_subSec_iff hft.isScSmooth.1 (hrep.2.1 i).1 p.2).2 hfy
      exact (hall p hpW h0y).2.1
    · exact ⟨univ, isOpen_univ, mem_univ _, fun y _ _ _ h => absurd h hi⟩
  choose W hWo hxW hWgp using hW
  have hU'o : IsOpen (R.U ∩ ⋂ i, W i) := R.isOpen_U.inter (isOpen_iInter_of_finite hWo)
  have hxU' : x ∈ R.U ∩ ⋂ i, W i := ⟨R.mem_U, mem_iInter.2 hxW⟩
  obtain ⟨R', hR'U, -, -⟩ := A.X.exists_naturalRep_shrink R hU'o hxU'
  have hR'R : R'.U ⊆ R.U := fun y hy => (hR'U hy).2
  have hR'W : ∀ i, R'.U ⊆ W i := fun i y hy => mem_iInter.1 (hR'U hy).1.2 i
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  refine ⟨R', O, k, s, σ, c, hO, hrep, hc, hR'R.trans hRc, hsub, ?_, ?_, ?_, ?_,
    fun y hy => hcount y (hR'R hy), hlin, fun i y hy hi => hthrough i y (hR'R hy) hi⟩
  · -- the `Mᵢ` are submanifolds
    intro i
    have e : {y ∈ R'.U | f y = s i y} = {y ∈ R.U | f y = s i y} ∩ R'.U := by
      ext y
      constructor
      · rintro ⟨hy, he⟩
        exact ⟨⟨hR'R hy, he⟩, hy⟩
      · rintro ⟨⟨-, he⟩, hy⟩
        exact ⟨hy, he⟩
    rw [e]
    exact (hS i).inter_isOpen R'.isOpen_U
  · -- (1)
    intro i
    rw [isProperMap_inclusion_iff]
    have hcs : ContinuousOn (s i) R'.U :=
      (hrep.2.1 i).continuousOn.mono ((hR'R.trans hRc).trans hsub)
    have h1 : Continuous fun p : R'.U => f p := hfc.comp continuous_subtype_val
    have h2 : Continuous fun p : R'.U => s i p :=
      hcs.comp_continuous continuous_subtype_val fun p => p.2
    convert isClosed_eq h1 h2 using 1
    ext p
    simp
  · -- `M_{U(x)} = ⋃ Mᵢ`
    ext y
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨hy, hp⟩
      have h : y ∈ {y ∈ R.U | 0 < Λ (f y)} := ⟨hR'R hy, hp⟩
      rw [hU] at h
      obtain ⟨i, -, hi⟩ := mem_iUnion.1 h
      exact ⟨i, hy, hi⟩
    · rintro ⟨i, hy, hi⟩
      have h : y ∈ ⋃ i, {y ∈ R.U | f y = s i y} := mem_iUnion.2 ⟨i, hR'R hy, hi⟩
      rw [← hU] at h
      exact ⟨hy, h.2⟩
  · -- (2): general position and good position on `M_{U(x)}`
    intro y hy hpy
    refine ⟨?_, hG2 y (hR'R hy) hpy⟩
    have hy1 : y ∈ A.X.PObj.levelSet 1 := mem_levelSet_one_of_pos hf hΛ hpy
    refine ⟨hy1, isReducedOntoAtLevel_of_isGeneralPositionGerm hf hft hO hrep hc hsub
      (y := A.X.PObj.levelMk 1 y hy1) (hRc (hR'R hy)) fun j hj => ?_⟩
    exact hWgp j y (hR'W j hy) _ hj.symm (hthrough j y (hR'R hy) hj.symm)

end SBLocalization

end Polyfold
