import Polyfold.Chapter15.OrientedLinearizations
import Polyfold.Chapter15.Transversality

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702: **Theorem 15.4.1** and **Definition 15.4.2** (2017: Theorem 15.6, Definition 15.7),
the canonical lift `T̂_((f, o), Λ)` of `T(f, Λ)` to oriented formal sums, read in a chart point.

# The canonical oriented lift of `T(f, Λ)`

## The text, paraphrased

(pp. 701–702) Let `(f, o)` be an oriented sc-Fredholm section functor and `Λ` an
sc⁺-multisection.  At `y` in the domain of a local sc⁺-section structure `(sᵢ, σᵢ)`,
`T(f,Λ)(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ · (f − sᵢ)'(y)`, independently of the structure.  Since `f`
is oriented, every `(f − sᵢ)'(y)` inherits an orientation `o_{i,y}`, and
`T̂_((f,o),Λ)(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ · ((f − sᵢ)'(y), o_{i,y})` does not depend on the
structure, since the operators of the sum do not.  For `y ∈ supp(Λ ∘ f)` the operators are onto
and `o_{i,y}` orients `ker (f − sᵢ)'(y)`.  (Theorem 15.4.1) `T_Θ` has a canonical lift
characterized by this formula.  (Definition 15.4.2) It is the canonical orientation of `Θ`.

## What is formalized (namespace `Polyfold.SBLocalization`)

The operators are read in the chart point `liftPt c hc hy hy1` of Part I (chart `c`, level-`1`
point `levelLift c.φ 1 y`), the chart point at which `linSumChart` and `linearization` are made.

* `subDeriv_mem_K`, `subOp`: at a zero of `f − s`, `(f − s)'(y) = D((f̂ − ŝ) ∘ r)(z)` maps `T_zO`
  into `K_z`, an operator `T_zO → K_z`; `toF_subOp` (as an operator `T_zO → F` it is the
  operator of `linSumChart`).
* **`subOp_mem_linSet`**: for a local sc⁺-section `s` on `O ⊇ dom(c)` with `f(y) = s(y)`,
  `(f − s)'(y) ∈ Lin(f, y)` (Part I's Definition 6.2.1), with the standing hypothesis
  `HasScPlusSectionsThrough` of §12.5.  So `o_y ∈ Or_y^f` orients every summand of `T(f,Λ)(y)`.
* `linW`: the formal sum `∑_{i : f(y) = sᵢ(y)} σᵢ · (f − sᵢ)'(y)` with its operators as members of
  `Lin(f, y)`; `mapDomain_toF_linW` (it is `linSumChart c f s σ z`, the formal sum of
  Theorem 15.1.1 (2)).
* **`canonicalLift`** (Definition 15.4.2 in the chart point) `= canonLift o linW`, and
  **`canonLift_linW_eq_sum`**: the formula
  `∑_{i : f(y) = sᵢ(y)} σᵢ · ((f − sᵢ)'(y), o(f − sᵢ)'(y))`.
* **`theorem_15_4_1_lift`** (Theorem 15.4.1 in `Ĝr_F`): `f_F(T̂) = T(f,Λ)(y)` (in the chart),
  every summand carries the orientation induced by `o`, and `T̂` is the only formal sum of
  oriented operators with these two properties.
* **`theorem_15_4_1_indep`**: two local sc⁺-section structures of `Λ` give the same `T̂` (from
  Theorem 15.1.1, `linSumChart_eq`).
* `surjective_subOp_iff` (onto as an operator `T_zO → K_z` iff `ChartOnto`), `branchOr`: the
  orientation `o_{i,y}` of `ker (f − sᵢ)'(y)` for an onto summand, `branchOr_injective`
  (`o_y` is recovered from it).

## Not formalized here

The passage from `Ĝr_F` to `Ĝr(X)` of Chapter 9 (the oriented tangent spaces
`T_y(Mᵢ, oᵢ)`), continuity of `y ↦ o_{i,y}` along `Mᵢ` and the naturality under morphisms: see
the hand-over note (gap text of G.159).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### The chart point of `linSumChart` -/

/-- **The chart point at `y ∈ X₁` with the level-`1` lift `levelLift c.φ 1 y`** (the point at
which `linSumChart` and `linearization` read `T(f,Λ)(y)`). -/
def liftPt (c : StrongBundleChart A.X.PObj A.P) (hc : A.B.IsChart c) {y : A.Obj}
    (hy : y ∈ c.φ.source) (hy1 : y ∈ A.X.PObj.levelSet 1) : ChartPoint A.B y :=
  ⟨c, hc, hy, levelLift c.φ 1 y, A.X.PObj.toBase_levelLift c.isChart hy hy1⟩

@[simp] theorem liftPt_c (c : StrongBundleChart A.X.PObj A.P) (hc : A.B.IsChart c) {y : A.Obj}
    (hy : y ∈ c.φ.source) (hy1 : y ∈ A.X.PObj.levelSet 1) : (liftPt c hc hy hy1).c = c := rfl

@[simp] theorem liftPt_z (c : StrongBundleChart A.X.PObj A.P) (hc : A.B.IsChart c) {y : A.Obj}
    (hy : y ∈ c.φ.source) (hy1 : y ∈ A.X.PObj.levelSet 1) :
    (liftPt c hc hy hy1).z = levelLift c.φ 1 y := rfl

/-! ### `(f − s)'(y)` as an operator `T_zO → K_z` -/

variable {f : A.Obj → A.W} {s : A.Obj → A.W} {O : Set A.Obj} {y : A.Obj}

/-- `f̂(φ(y)) = ŝ(φ(y))` when `f(y) = s(y)`. -/
theorem principal_eq_of_eq (c : StrongBundleChart A.X.PObj A.P) (hy : y ∈ c.φ.source)
    (hfs : f y = s y) : c.principal f (c.φ y) = c.principal s (c.φ y) := by
  unfold StrongBundleChart.principal
  rw [c.φ.symm_apply_apply hy, hfs]

/-- **At a zero of `f − s`, `D((f̂ − ŝ) ∘ r)(z)` takes values in `K_z`** (`rho_scDeriv_comp_r`),
for a local sc⁺-section `s` on `O ⊇ dom(c)`. -/
theorem subDeriv_mem_K (hf : A.B.IsScSmoothSection f) (hs : IsScPlusSectionOn A s O)
    (p : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O) (hfs : f y = s y)
    (v : p.c.φ.model.E 0) : subDeriv p.c f s p.z v ∈ p.K := by
  have hfr := isSc1_sub_comp_r hf hs p.isChart hsub
  have hfK : ∀ x ∈ r p.c.R '' p.c.U,
      (x, p.c.principal f x - p.c.principal s x) ∈ p.c.R '' (p.c.U ×ˢ univ) := by
    intro x hx
    have hxO : x ∈ p.c.φ.model.O := p.c.r_image ▸ hx
    have h := p.c.principal_mem_K (isSection_sectionSubOn (s := s) hf.1 O) hxO
    rwa [principal_sectionSubOn hf.1 hs.1 hsub hxO] at h
  have hzero : p.c.principal f (p.c.φ.model.E.toBase 1 p.z) -
      p.c.principal s (p.c.φ.model.E.toBase 1 p.z) = 0 := by
    rw [p.toBase_z, principal_eq_of_eq p.c p.mem_source hfs, sub_self]
  exact ⟨_, rho_scDeriv_comp_r p.c.relOpen p.c.isRetraction hfr hfK p.mem_O hzero v⟩

/-- **`(f − s)'(y) : T_zO → K_z`** in the chart point `p`, at a zero of `f − s`. -/
def subOp (hf : A.B.IsScSmoothSection f) (hs : IsScPlusSectionOn A s O) (p : ChartPoint A.B y)
    (hsub : p.c.φ.source ⊆ O) (hfs : f y = s y) : ↥p.T →L[ℝ] ↥p.K :=
  ((subDeriv p.c f s p.z).comp p.T.subtypeL).codRestrict p.K fun v =>
    subDeriv_mem_K hf hs p hsub hfs v

theorem coe_subOp (hf : A.B.IsScSmoothSection f) (hs : IsScPlusSectionOn A s O)
    (p : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O) (hfs : f y = s y) (v : ↥p.T) :
    (subOp hf hs p hsub hfs v : p.c.F 0) = subDeriv p.c f s p.z v := rfl

/-- An operator `T_zO → K_z` read as an operator `T_zO → F`. -/
def toF (p : ChartPoint A.B y) (L : ↥p.T →L[ℝ] ↥p.K) : ↥p.T →L[ℝ] p.c.F 0 :=
  p.K.subtypeL.comp L

theorem toF_injective (p : ChartPoint A.B y) : Injective (toF p) := fun _ _ h =>
  ContinuousLinearMap.ext fun v => Subtype.ext (congrArg (fun M => M v) h)

/-- **As an operator `T_zO → F`, `subOp` is the operator `(f̂ − ŝ)'(z)` of `linSumChart`.** -/
theorem toF_subOp (hf : A.B.IsScSmoothSection f) (hs : IsScPlusSectionOn A s O)
    (p : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O) (hfs : f y = s y) :
    toF p (subOp hf hs p hsub hfs) =
      linAt p.c.U p.c.R (fun z => p.c.principal f z - p.c.principal s z) p.z :=
  ContinuousLinearMap.ext fun _ => rfl

/-! ### `(f − s)'(y) ∈ Lin(f, y)` -/

/-- **`(f − s)'(y)` is a member of `Lin(f, y)`** (Part I's Definition 6.2.1) for a local
sc⁺-section `s` on the open `O ⊇ dom(c)` with `f(y) = s(y)`, `y` smooth, under the standing
hypothesis of §12.5 (sc⁺-sections through points).  With an sc⁺-section `s₀` through `−f(y)`,
`(f + s₀)'(y) = (f − s)'(y) + ι ∘ D((ŝ₁ + ŝ₀,₁) ∘ r)(z)`, and the last term is an sc⁺-operator. -/
theorem subOp_mem_linSet (hf : A.B.IsScFredholmSection f) (hO : IsOpen O)
    (hs : IsScPlusSectionOn A s O) (p : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O)
    (hfs : f y = s y) (hys : y ∈ A.X.PObj.smoothSet) (hsec : A.B.HasScPlusSectionsThrough) :
    subOp hf.isScSmooth hs p hsub hfs ∈ p.linSet f := by
  obtain ⟨L₀, s₀, hs₀, hz₀, -⟩ := p.linSet_nonempty hf hys hsec
  rw [p.mem_linSet_iff hf hs₀ hz₀]
  have hUd := p.c.relOpen.isScDomain
  have hl₀ : IsScSmooth (F := p.c.F.shift) p.c.U (p.c.principalLift s₀ ∘ r p.c.R) :=
    ((((hs₀.isScSmoothRetractMap_one p.isChart).comp_isScSmooth
      (p.c.isRetraction.baseRetraction p.c.relOpen) p.c.base_retract).snd hUd).congr hUd
      fun _ _ => rfl)
  have hl : IsScSmooth (F := p.c.F.shift) p.c.U (p.c.principalLift s ∘ r p.c.R) := by
    have h1 := hs.isScSmoothRetractMap_localRepOne_of_isChart hO p.isChart hsub
    have h2 : IsScSmoothRetractMap p.c.φ.model.E p.c.φ.model.C p.c.φ.model.O
        (p.c.φ.model.E.prod p.c.F.shift) (p.c.φ.model.C ×ˢ univ) (strongShiftOne p.c.K)
        (fun z => (z, p.c.principalLift s z)) :=
      h1.congr fun z hz => localRepOne_eq_of_sub hs.1 hsub hz
    exact ((h2.comp_isScSmooth (p.c.isRetraction.baseRetraction p.c.relOpen)
      p.c.base_retract).snd hUd).congr hUd fun _ _ => rfl
  set h : p.c.φ.model.E 0 → p.c.F.shift 0 :=
    fun u => p.c.principalLift s (r p.c.R u) + p.c.principalLift s₀ (r p.c.R u) with hh_def
  have hh : IsScSmooth (F := p.c.F.shift) p.c.U h := hl.add hUd hl₀
  have hfs' := hf.isScSmooth
  have hg := isSc1_sub_comp_r hfs' hs p.isChart hsub
  have hg' := (hfs'.sectionAdd hs₀).isSc1_principal_comp_r p.isChart
  have heq : ∀ u ∈ p.c.U, (p.c.principal (sectionAdd A.P f s₀) ∘ r p.c.R) u =
      ((fun z => p.c.principal f z - p.c.principal s z) ∘ r p.c.R) u +
        p.c.F.toBase 1 (h u) := by
    intro u hu
    have hO' := p.c.r_mem_O hu
    have hzV : p.c.φ.symm (r p.c.R u) ∈ p.c.φ.source := p.c.φ.symm_mapsTo hO'
    have e1 : p.c.F.toBase 1 (p.c.principalLift s (r p.c.R u)) = p.c.principal s (r p.c.R u) :=
      Function.invFun_eq (hs.principal_mem_range_of_isChart p.isChart hsub hzV)
    have e2 := hs₀.toBase_principalLift p.isChart hO'
    simp only [Function.comp_apply, hh_def, map_add, e1, e2]
    rw [p.c.principal_sectionAdd hfs'.1 hs₀.1 hO']
    abel
  have hder := scDeriv_add_toBase_one_apply p.c.relOpen hg hg' hh.isSc1 heq p.mem_U
  set D := scDeriv (F := p.c.F.shift) p.c.U h p.z with hD_def
  have hDop : IsScOperator (E := p.c.φ.model.E) (F := p.c.F.shift) D :=
    hh.isSc1.isSc1With_scDeriv.scOperator_deriv p.mem_U (p.z_mem_smoothLvl hys)
  have hDK : ∀ v, p.c.F.toBase 1 (D v) ∈ p.K := fun v => by
    have e : p.c.F.toBase 1 (D v) =
        scDeriv p.c.U (p.c.principal (sectionAdd A.P f s₀) ∘ r p.c.R) p.z v -
          subDeriv p.c f s p.z v := by
      rw [hder v]; unfold subDeriv; abel
    rw [e]
    exact sub_mem (p.scDeriv_mem_K (hfs'.sectionAdd hs₀) hz₀ v)
      (subDeriv_mem_K hfs' hs p hsub hfs v)
  let b : ↥p.T →L[ℝ] ↥p.K :=
    (((p.c.F.toBase 1).comp D).comp p.T.subtypeL).codRestrict p.K fun v => hDK v
  have hb : p.IsScPlusOp b := p.isScPlusOp_of_shift (p.isScSubspace_T hys)
    (p.isScSubspace_K hys) hDop (fun v _ => hDK v) (fun _ => rfl)
  refine ⟨(-1 : ℝ) • b, hb.smul (-1), fun v => ?_⟩
  rw [coe_subOp, linAt_apply, smul_apply, Submodule.coe_smul, neg_one_smul,
    hder v]
  change subDeriv p.c f s p.z v = subDeriv p.c f s p.z v + p.c.F.toBase 1 (D v) +
    -p.c.F.toBase 1 (D v)
  abel

/-! ### The formal sum of `T(f, Λ)(y)` with operators in `Lin(f, y)` -/

/-- `f(y) = s(y)` iff `f̂(φ(y)) = ŝ(φ(y))`, for `y` in the domain of `c` inside `O`. -/
theorem eq_iff_principal_eq (hf : IsSection A.P f) (hsec : ∀ x ∈ O, A.P (s x) = x)
    (c : StrongBundleChart A.X.PObj A.P) (hsub : c.φ.source ⊆ O) (hy : y ∈ c.φ.source) :
    s y = f y ↔ c.principal s (c.φ y) = c.principal f (c.φ y) := by
  refine ⟨fun h => (principal_eq_of_eq c hy h.symm).symm, fun h => ?_⟩
  have hz : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model y hy
  have h1 : c (s y) = (c.φ y, c.principal s (c.φ y)) := by
    have := apply_localSection hsec hsub hz
    rwa [c.φ.symm_apply_apply hy] at this
  have h2 : c (f y) = (c.φ y, c.principal f (c.φ y)) := by
    have := apply_localSection (fun x _ => hf x) hsub hz
    rwa [c.φ.symm_apply_apply hy] at this
  exact c.toPartialEquiv.injOn (c.mem_source_of_proj (by rw [hsec y (hsub hy)]; exact hy))
    (c.mem_source_of_proj (by rw [hf y]; exact hy)) (by rw [h1, h2, h])

variable {Λ : A.W → ℚ≥0} {k : ℕ} {sb : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}

open Classical in
/-- **`T(f,Λ)(y)` with its operators as members of `Lin(f, y)`**:
`∑_{i : f(y) = sᵢ(y)} σᵢ · (f − sᵢ)'(y)` in the chart point `p`. -/
def linW (hf : A.B.IsScFredholmSection f) (hO : IsOpen O) (hrep : IsLocalRepOn A Λ O sb σ)
    (p : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O) (hys : y ∈ A.X.PObj.smoothSet)
    (hsec : A.B.HasScPlusSectionsThrough) : p.linSet f →₀ ℚ≥0 :=
  ∑ i, if h : sb i y = f y then
    Finsupp.single ⟨subOp hf.isScSmooth (hrep.2.1 i) p hsub h.symm,
      subOp_mem_linSet hf hO (hrep.2.1 i) p hsub h.symm hys hsec⟩ (σ i) else 0

/-- **`linW` is the formal sum of Theorem 15.1.1 (2)** in the chart: its image under
`L ↦ (T_zO → K_z ⊆ F)` is `linSumChart c f s σ z`. -/
theorem mapDomain_toF_linW (hf : A.B.IsScFredholmSection f) (hO : IsOpen O)
    (hrep : IsLocalRepOn A Λ O sb σ) (c : StrongBundleChart A.X.PObj A.P) (hc : A.B.IsChart c)
    (hy : y ∈ c.φ.source) (hsub : c.φ.source ⊆ O) (hys : y ∈ A.X.PObj.smoothSet)
    (hsec : A.B.HasScPlusSectionsThrough) :
    Finsupp.mapDomain (fun L : (liftPt c hc hy (smoothSet_subset_levelSet 1 hys)).linSet f =>
        toF _ L.1)
        (linW hf hO hrep (liftPt c hc hy (smoothSet_subset_levelSet 1 hys)) hsub hys hsec) =
      linSumChart c f sb σ (levelLift c.φ 1 y) := by
  classical
  set p := liftPt c hc hy (smoothSet_subset_levelSet 1 hys)
  have hz : c.φ.model.E.toBase 1 (levelLift c.φ 1 y) = c.φ y :=
    A.X.PObj.toBase_levelLift c.isChart hy (smoothSet_subset_levelSet 1 hys)
  unfold linW
  rw [Finsupp.mapDomain_finsetSum, linSumChart, linSumModel]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hiff := eq_iff_principal_eq hf.isScSmooth.1 (hrep.2.1 i).1 c hsub hy
  by_cases h : sb i y = f y
  · rw [dif_pos h, Finsupp.mapDomain_single, hz, if_pos (hiff.1 h)]
    exact congrArg (fun L => Finsupp.single L (σ i))
      (toF_subOp hf.isScSmooth (hrep.2.1 i) p hsub h.symm)
  · rw [dif_neg h, Finsupp.mapDomain_zero, hz, if_neg (fun h' => h (hiff.2 h'))]
    rfl

open Classical in
/-- **The formula of Theorem 15.4.1** in any chart point `p`: the canonical lift of `linW` is
`∑_{i : f(y) = sᵢ(y)} σᵢ · ((f − sᵢ)'(y), o((f − sᵢ)'(y)))`. -/
theorem canonLift_linW_eq_sum (hf : A.B.IsScFredholmSection f) (hO : IsOpen O)
    (hrep : IsLocalRepOn A Λ O sb σ) (p : ChartPoint A.B y) (hsub : p.c.φ.source ⊆ O)
    (hys : y ∈ A.X.PObj.smoothSet) (hsec : A.B.HasScPlusSectionsThrough) (o : p.Or f hf) :
    p.canonLift o (linW hf hO hrep p hsub hys hsec) =
      ∑ i, if h : sb i y = f y then
        Finsupp.single (p.orLin o ⟨subOp hf.isScSmooth (hrep.2.1 i) p hsub h.symm,
            subOp_mem_linSet hf hO (hrep.2.1 i) p hsub h.symm hys hsec⟩) (σ i) else 0 := by
  unfold linW
  rw [ChartPoint.canonLift_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · exact ChartPoint.canonLift_single _ _ _ _
  · exact Finsupp.mapDomain_zero

/-! ### Theorem 15.4.1 and Definition 15.4.2 in the chart point -/

variable (hf : A.B.IsScFredholmSection f) (hO : IsOpen O) (hrep : IsLocalRepOn A Λ O sb σ)
  (c : StrongBundleChart A.X.PObj A.P) (hc : A.B.IsChart c) (hy : y ∈ c.φ.source)
  (hsub : c.φ.source ⊆ O) (hys : y ∈ A.X.PObj.smoothSet) (hsec : A.B.HasScPlusSectionsThrough)

/-- **Definition 15.4.2 (2021 p. 702; 2017: Definition 15.7), in the chart point**: the canonical
oriented lift `T̂_((f,o),Λ)(y) ∈ Ĝr_F(y)` for an orientation `o ∈ Or_y^f` (read in the chart
point). -/
def canonicalLift (o : (liftPt c hc hy (smoothSet_subset_levelSet 1 hys)).Or f hf) :
    (liftPt c hc hy (smoothSet_subset_levelSet 1 hys)).GrFHat f hf :=
  (liftPt c hc hy (smoothSet_subset_levelSet 1 hys)).canonLift o
    (linW hf hO hrep (liftPt c hc hy (smoothSet_subset_levelSet 1 hys)) hsub hys hsec)

/-- The characterization of the canonical lift of a formal sum `w` of members of `Lin(f, y)` whose
image in `(T_zO → F)` is `T`: `f_F(canonLift o w) = T`, every summand carries the orientation
induced by `o`, and it is the only formal sum of oriented operators with these two properties. -/
theorem canonLift_spec (hf : A.B.IsScFredholmSection f) (p : ChartPoint A.B y) (o : p.Or f hf)
    (w : p.linSet f →₀ ℚ≥0) (T : (↥p.T →L[ℝ] p.c.F 0) →₀ ℚ≥0)
    (hW : Finsupp.mapDomain (fun L : p.linSet f => toF p L.1) w = T) :
    Finsupp.mapDomain (toF p) (p.forgetOr f hf (p.canonLift o w)) = T ∧
      (∀ q ∈ (p.canonLift o w).support, q = p.orLin o q.1) ∧
      ∀ W : p.GrFHat f hf, Finsupp.mapDomain (toF p) (p.forgetOr f hf W) = T →
        (∀ q ∈ W.support, q = p.orLin o q.1) → W = p.canonLift o w := by
  have hcomp : ∀ w : p.linSet f →₀ ℚ≥0, Finsupp.mapDomain (toF p)
      (Finsupp.mapDomain Subtype.val w) =
        Finsupp.mapDomain (fun L : p.linSet f => toF p L.1) w := fun w =>
    (Finsupp.mapDomain_comp).symm
  refine ⟨?_, fun q hq => p.snd_eq_of_mem_support_canonLift o _ hq, fun W h1 h2 => ?_⟩
  · rw [p.forgetOr_canonLift, hcomp, hW]
  · refine p.canonLift_unique o _ W ?_ h2
    have hinj : Injective (Finsupp.mapDomain (fun L : p.linSet f => toF p L.1) :
        (p.linSet f →₀ ℚ≥0) → _) :=
      Finsupp.mapDomain_injective ((toF_injective p).comp Subtype.val_injective)
    apply hinj
    rw [hW, ← hcomp, ← h1, ChartPoint.forgetOr, ← Finsupp.mapDomain_comp,
      ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_comp.symm

/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6), in `Ĝr_F(y)` read in the chart point**:
for an sc-Fredholm section `f` oriented at `y` by `o ∈ Or_y^f`, a local sc⁺-section structure of
`Λ` and a smooth `y`, the canonical lift `T̂ = canonicalLift o` satisfies
(1) `f_F(T̂) = T(f,Λ)(y)` (the formal sum of Theorem 15.1.1 (2), `linSumChart`);
(2) every summand of `T̂` carries the orientation induced by `o`;
and `T̂` is the only formal sum of oriented members of `Lin(f, y)` with (1) and (2). -/
theorem theorem_15_4_1_lift (o : (liftPt c hc hy (smoothSet_subset_levelSet 1 hys)).Or f hf) :
    let p := liftPt c hc hy (smoothSet_subset_levelSet 1 hys)
    Finsupp.mapDomain (toF p) (p.forgetOr f hf (canonicalLift hf hO hrep c hc hy hsub hys hsec o))
        = linSumChart c f sb σ (levelLift c.φ 1 y) ∧
      (∀ q ∈ (canonicalLift hf hO hrep c hc hy hsub hys hsec o).support, q = p.orLin o q.1) ∧
      ∀ W : p.GrFHat f hf,
        Finsupp.mapDomain (toF p) (p.forgetOr f hf W) = linSumChart c f sb σ (levelLift c.φ 1 y) →
        (∀ q ∈ W.support, q = p.orLin o q.1) →
        W = canonicalLift hf hO hrep c hc hy hsub hys hsec o :=
  canonLift_spec hf _ o _ _ (mapDomain_toF_linW hf hO hrep c hc hy hsub hys hsec)

/-- **Theorem 15.4.1, independence of the local sc⁺-section structure** (2021 p. 701: "this
definition does not depend on the choice of the local sc⁺-section structure since the occurring
operators … are independent of such choices"): two local sc⁺-section structures of `Λ` on `O`,
`O'` with `dom(c) ⊆ O ∩ O'` give the same canonical lift (Theorem 15.1.1, `linSumChart_eq`). -/
theorem theorem_15_4_1_indep {O' : Set A.Obj} (hO' : IsOpen O') {l : ℕ}
    {tb : Fin l → A.Obj → A.W} {τ : Fin l → ℚ≥0} (hrep' : IsLocalRepOn A Λ O' tb τ)
    (hsub' : c.φ.source ⊆ O')
    (o : (liftPt c hc hy (smoothSet_subset_levelSet 1 hys)).Or f hf) :
    canonicalLift hf hO hrep c hc hy hsub hys hsec o =
      canonicalLift hf hO' hrep' c hc hy hsub' hys hsec o := by
  set p := liftPt c hc hy (smoothSet_subset_levelSet 1 hys)
  have hz : c.φ.model.E.toBase 1 (levelLift c.φ 1 y) ∈ c.φ.model.O := by
    rw [A.X.PObj.toBase_levelLift c.isChart hy (smoothSet_subset_levelSet 1 hys)]
    exact c.φ.mapsTo_model y hy
  have heq := linSumChart_eq hf.isScSmooth hrep hrep' hc (fun x hx => ⟨hsub hx, hsub' hx⟩) hz
  have h1 := mapDomain_toF_linW hf hO hrep c hc hy hsub hys hsec
  have h2 := mapDomain_toF_linW hf hO' hrep' c hc hy hsub' hys hsec
  have hinj : Injective (Finsupp.mapDomain (fun L : p.linSet f => toF p L.1) :
      (p.linSet f →₀ ℚ≥0) → _) :=
    Finsupp.mapDomain_injective ((toF_injective p).comp Subtype.val_injective)
  unfold canonicalLift
  rw [hinj (h1.trans (heq.trans h2.symm))]

/-! ### The orientation of the kernel of an onto summand -/

/-- **`(f − s)'(y)` onto `K_z` iff `ChartOnto`** (Definition 15.2.1's surjectivity read in the
chart, `LocalIFT`). -/
theorem surjective_subOp_iff (hfs' : A.B.IsScSmoothSection f) (hs : IsScPlusSectionOn A s O)
    (p : ChartPoint A.B y) (hsub' : p.c.φ.source ⊆ O) (hfs : f y = s y) :
    Surjective (subOp hfs' hs p hsub' hfs) ↔ ChartOnto p.c (subDeriv p.c f s p.z) p.z := by
  constructor
  · intro h k hk
    have hkK : k ∈ p.K := by
      have := (mem_rangeS_ρCLM_iff p.c.isRetraction p.mem_O p.mem_U).2 hk
      exact this
    obtain ⟨v, hv⟩ := h ⟨k, hkK⟩
    exact ⟨v.1, v.2, congrArg Subtype.val hv⟩
  · rintro h ⟨k, hk⟩
    have hk' := (mem_rangeS_ρCLM_iff p.c.isRetraction p.mem_O p.mem_U).1 hk
    obtain ⟨v, hv, hvk⟩ := h k hk'
    exact ⟨⟨v, hv⟩, Subtype.ext hvk⟩

/-- **The orientation `o_{i,y}` of `ker (f − sᵢ)'(y)`** induced by `o_y` for an onto summand
(2021 pp. 701–702), read in `Λ^max N`, `N ⊆ E₀` the kernel of `(f − sᵢ)'(y)` on `T_zO`. -/
def branchOr (hs : IsScPlusSectionOn A s O) (p : ChartPoint A.B y) (hsub' : p.c.φ.source ⊆ O)
    (hfs : f y = s y) (hsurj : Surjective (subOp hf.isScSmooth hs p hsub' hfs))
    (o : p.Or f hf) :
    Module.Ray ℝ (maxPow ((LinearMap.ker ((subOp hf.isScSmooth hs p hsub' hfs :
      ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K)).map (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0))) :=
  p.orKer o (subOp_mem_linSet hf hO hs p hsub' hfs hys hsec) hsurj rfl

/-- **`o_y` is recovered from `o_{i,y}`**: `o ↦ branchOr o` is injective (a bijection onto the
two orientations of the kernel, `ChartPoint.orKerEquiv`). -/
theorem branchOr_injective (hs : IsScPlusSectionOn A s O) (p : ChartPoint A.B y)
    (hsub' : p.c.φ.source ⊆ O) (hfs : f y = s y)
    (hsurj : Surjective (subOp hf.isScSmooth hs p hsub' hfs)) :
    Injective (branchOr hf hO hys hsec hs p hsub' hfs hsurj) :=
  (p.orKerEquiv hf (subOp_mem_linSet hf hO hs p hsub' hfs hys hsec) hsurj rfl).injective

end SBLocalization

end Polyfold
