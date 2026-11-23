import Polyfold.Chapter16.StokesUnconditional
import Polyfold.Chapter15.CollarCobordismUnconditional
import Polyfold.Chapter16.InheritedPerturbationExists

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.4, p. 732 (the
integrals and Theorem 16.4.6) and §16.6, p. 739: **Theorem 16.6.6** (2017: Theorem 16.8), with
Stokes from Remark 9.5.19 (p. 451).  Numbers and pages are the 2021 text's.

# The invariant of Theorem 16.6.6 with no sc-smooth partitions of unity

Stokes holds on every polyfold (`PolyfoldClass.OrientedRep.theorem_16_4_6_all` and its
companions, `Chapter16/StokesUnconditional.lean`).  The results of §16.4 and §16.6 that assumed
sc-smooth partitions of unity on `Z`, or on `[0, 1] × X` in the model of the orientation, only for
Stokes are restated here without them.

* p. 732: `OrientedRep.boundaryIntegral_eq_of_rel_all`, `boundaryIntegralEff_eq_of_rel_all`,
  `boundaryIntegralDim1_eq_of_rel_all` (the boundary integrals do not depend on the
  representative), `theorem_16_4_6_both_all`.
* "depends only on `[τ]`": `OrientedRep.integral_d_eq_zero_of_boundary_all` and its companions.
* `CompactOrientedSuborbifold.HasCobordism_all`, `HasCobordismEff_all`: the cobordisms with no
  partitions of unity on `Y`; `integral_eq_of_hasCobordism_all`, `hasCobordism_refl_all`.
* `theorem_16_6_6_hyp_all`, `theorem_16_6_6_of_model_all`, `theorem_16_6_6_of_cylinder_all`.
* `CanonicalInput_all o k`: `CanonicalInput o k` without its field `pu` (partitions of unity on
  `[0, 1] × X`).
* **`theorem_16_6_6_canonical_all`**, `theorem_16_6_6_canonical_of_forall_all`,
  **`theorem_16_6_6_canonical_wellDefined_all`**, **`theorem_16_6_6_canonical_solutionSet_all`**:
  Theorem 16.6.6 for the orientation inherited from `(f, o)`; the cobordism is the collar
  extension of `corollary_15_4_4_collar_all`.

## Reading

In the forms for the canonical orientation, the partitions of unity on `Z` had a second use: they
gave sc-smooth bump functions in the model (Theorem 15.4.1, the collar construction, the
existence of regular perturbations, the continuity of `o`).  That use is kept, as the hypothesis
`hbump : c.polyfold.AdmitsBumpFunctions` (Definition 16.1.5 (1); it follows from partitions of
unity).  The field `pu` of `CanonicalInput` was used only for Stokes on `[0, 1] × X` and for the
construction of the cobordism by Theorem 15.3.9; the collar extension needs neither.  The field
`pu` of `CylinderInput` is kept: there it constructs the cobordism (Theorem 15.3.9 on
`[0, 1] × X`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter CategoryTheory MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization EPLocalization.EPLoc EpGroupoid MPolyfold

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z}

namespace OrientedRep

variable {m : ℕ}

/-- **The boundary integral does not depend on the representative** (2021 p. 732, `n ≥ 2`), with
no sc-smooth partitions of unity: `boundaryIntegral_eq_of_rel` without `hPU`. -/
theorem boundaryIntegral_eq_of_rel_all {a b : OrientedRep c}
    (h : Rel a b) (hm : 0 < m)
    (hcpta : a.p.X.X.IsCompactBranched a.A.Θ) (hloca : a.IsTameOriented (m + 1))
    (hcptb : b.p.X.X.IsCompactBranched b.A.Θ) (hlocb : b.IsTameOriented (m + 1))
    (τ : ScForm c m) :
    a.boundaryIntegral hm hcpta hloca τ = b.boundaryIntegral hm hcptb hlocb τ := by
  rw [← theorem_16_4_6_all a hm, ← theorem_16_4_6_all b hm]
  exact integral_eq_of_rel h _ _ _ _ _ _

/-- **The effective boundary integral does not depend on the representative** (2021 p. 732,
`n ≥ 2`), with no sc-smooth partitions of unity: `boundaryIntegralEff_eq_of_rel` without
`hPU`. -/
theorem boundaryIntegralEff_eq_of_rel_all {a b : OrientedRep c}
    (h : Rel a b) (hm : 0 < m)
    (hcpta : a.p.X.X.IsCompactBranched a.A.Θ) (hloca : a.IsTameOriented (m + 1))
    (hcptb : b.p.X.X.IsCompactBranched b.A.Θ) (hlocb : b.IsTameOriented (m + 1))
    (τ : ScForm c m) :
    a.boundaryIntegralEff hm hcpta hloca τ = b.boundaryIntegralEff hm hcptb hlocb τ := by
  rw [← theorem_16_4_6_eff_all a hm, ← theorem_16_4_6_eff_all b hm]
  exact integralEff_eq_of_rel h _ _ _ _ _ _

/-- **The boundary integrals for `n = 1` do not depend on the representative** (2021 p. 732),
with no sc-smooth partitions of unity: `boundaryIntegralDim1_eq_of_rel` without `hPU`. -/
theorem boundaryIntegralDim1_eq_of_rel_all {a b : OrientedRep c}
    (h : Rel a b)
    (hcpta : a.p.X.X.IsCompactBranched a.A.Θ) (hloca : a.IsTameOriented (0 + 1))
    (hcptb : b.p.X.X.IsCompactBranched b.A.Θ) (hlocb : b.IsTameOriented (0 + 1))
    (τ : ScForm c 0) :
    a.boundaryIntegralDim1 hcpta hloca τ = b.boundaryIntegralDim1 hcptb hlocb τ ∧
      a.boundaryIntegralEffDim1 hcpta hloca τ = b.boundaryIntegralEffDim1 hcptb hlocb τ := by
  refine ⟨?_, ?_⟩
  · rw [← theorem_16_4_6_dim1_all a, ← theorem_16_4_6_dim1_all b]
    exact integral_eq_of_rel h _ _ _ _ _ _
  · rw [← theorem_16_4_6_eff_dim1_all a, ← theorem_16_4_6_eff_dim1_all b]
    exact integralEff_eq_of_rel h _ _ _ _ _ _

/-- **Theorem 16.4.6 (2021 p. 732), the identities for `∫` and `∮`, with no sc-smooth partitions
of unity**: `theorem_16_4_6_both_hyp` without `hPU`. -/
theorem theorem_16_4_6_both_all (a : OrientedRep c)
    (hm : 0 < m) (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (τ : ScForm c m) :
    a.integral (Nat.succ_pos m) hcpt hloc (ScForm.d τ) = a.boundaryIntegral hm hcpt hloc τ ∧
      a.integralEff (Nat.succ_pos m) hcpt hloc (ScForm.d τ) =
        a.boundaryIntegralEff hm hcpt hloc τ :=
  ⟨theorem_16_4_6_all a hm hcpt hloc τ, theorem_16_4_6_eff_all a hm hcpt hloc τ⟩

/-- **`∫_θ̂ dη = 0` when `∂Z = ∅`** (Theorem 16.6.6, 2021 p. 739, "only depends on `[τ]`"), with
no sc-smooth partitions of unity: `integral_d_eq_zero_of_boundary` without `hPU`. -/
theorem integral_d_eq_zero_of_boundary_all (hbd : c.boundary = ∅) (a : OrientedRep c)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (η : ScForm c m) : a.integral (Nat.succ_pos m) hcpt hloc (ScForm.d η) = 0 := by
  have hemp : ∀ x, x ∉ a.p.X.X.PObj.boundary ∩ EpGroupoid.supp a.A.Θ := fun x hx =>
    not_mem_boundary_of_eq_empty hbd a.p a.mem x hx.1
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [theorem_16_4_6_dim1_all a hcpt hloc η, boundaryIntegralDim1]
    exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _
  · rw [theorem_16_4_6_all a hm hcpt hloc η, boundaryIntegral]
    exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _

/-- **`∮_θ̂ dη = 0` when `∂Z = ∅`** (2021 p. 739), with no sc-smooth partitions of unity:
`integralEff_d_eq_zero_of_boundary` without `hPU`. -/
theorem integralEff_d_eq_zero_of_boundary_all (hbd : c.boundary = ∅) (a : OrientedRep c)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (η : ScForm c m) : a.integralEff (Nat.succ_pos m) hcpt hloc (ScForm.d η) = 0 := by
  have hemp : ∀ x, x ∉ a.p.X.X.PObj.boundary ∩ EpGroupoid.supp a.A.Θ := fun x hx =>
    not_mem_boundary_of_eq_empty hbd a.p a.mem x hx.1
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [theorem_16_4_6_eff_dim1_all a hcpt hloc η, boundaryIntegralEffDim1]
    exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _
  · rw [theorem_16_4_6_eff_all a hm hcpt hloc η, boundaryIntegralEff]
    exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _

end OrientedRep

namespace OrientedSuborbifold

variable {m : ℕ}

/-- **`∫_θ̂ dη = 0` for `∂Z = ∅`** (2021 p. 739), with no sc-smooth partitions of unity. -/
theorem integral_d_eq_zero_all (hbd : c.boundary = ∅)
    (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented (m + 1)) (η : ScForm c m) :
    θ.integral (Nat.succ_pos m) hcpt htame (ScForm.d η) = 0 :=
  OrientedRep.integral_d_eq_zero_of_boundary_all hbd _ _ _ η

/-- **`∮_θ̂ dη = 0` for `∂Z = ∅`** (2021 p. 739), with no sc-smooth partitions of unity. -/
theorem integralEff_d_eq_zero_all (hbd : c.boundary = ∅)
    (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented (m + 1)) (η : ScForm c m) :
    θ.integralEff (Nat.succ_pos m) hcpt htame (ScForm.d η) = 0 :=
  OrientedRep.integralEff_d_eq_zero_of_boundary_all hbd _ _ _ η

/-- **`∫_θ̂ τ` depends only on `[τ]`** (`∂Z = ∅`, 2021 p. 739), with no sc-smooth partitions of
unity: `integral_add_d` without `hPU`. -/
theorem integral_add_d_all (hbd : c.boundary = ∅)
    (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented (m + 1)) (τ : ScForm c (m + 1)) (η : ScForm c m) :
    θ.integral (Nat.succ_pos m) hcpt htame (τ + ScForm.d η) =
      θ.integral (Nat.succ_pos m) hcpt htame τ := by
  rw [integral_add, integral_d_eq_zero_all hbd, add_zero]

/-- **`∮_θ̂ τ` depends only on `[τ]`** (`∂Z = ∅`, 2021 p. 739), with no sc-smooth partitions of
unity: `integralEff_add_d` without `hPU`. -/
theorem integralEff_add_d_all (hbd : c.boundary = ∅)
    (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented (m + 1)) (τ : ScForm c (m + 1)) (η : ScForm c m) :
    θ.integralEff (Nat.succ_pos m) hcpt htame (τ + ScForm.d η) =
      θ.integralEff (Nat.succ_pos m) hcpt htame τ := by
  rw [integralEff_add, integralEff_d_eq_zero_all hbd, add_zero]

end OrientedSuborbifold

namespace CompactOrientedSuborbifold

variable {m : ℕ}

/-- `P₀` and `P₁` are joined by an **oriented compact cobordism** (the proof of Corollary 15.4.4,
2021 p. 703, in a model `(X, β) ∈ c`), with no partitions of unity on `Y`: `HasCobordism` without
the field `Y.X.HasScPartitionsOfUnity`. -/
def HasCobordism_all (P₀ P₁ : CompactOrientedSuborbifold c m) : Prop :=
  ∃ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) (Y : EP.{u}) (F : EpFunctor Y.X q.X.X)
    (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryMeasure (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F (m + 1) ω) univ =
        P₁.integral (ScForm.mk q hq ω) - P₀.integral (ScForm.mk q hq ω)

/-- The effective form of `HasCobordism_all`: `HasCobordismEff` without the field
`Y.X.HasScPartitionsOfUnity`. -/
def HasCobordismEff_all (P₀ P₁ : CompactOrientedSuborbifold c m) : Prop :=
  ∃ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) (Y : EP.{u}) (F : EpFunctor Y.X q.X.X)
    (hLUC : Y.X.IsLUC) (Θ' : Y.Obj → ℚ)
    (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryMeasureEff (Nat.succ_pos m) hLUC hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F (m + 1) ω) univ =
        P₁.integralEff (ScForm.mk q hq ω) - P₀.integralEff (ScForm.mk q hq ω)

/-- A cobordism with partitions of unity on `Y` is one in the sense of `HasCobordism_all`. -/
theorem HasCobordism.to_all {P₀ P₁ : CompactOrientedSuborbifold c m} (h : HasCobordism P₀ P₁) :
    HasCobordism_all P₀ P₁ := by
  obtain ⟨q, hq, Y, F, -, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  exact ⟨q, hq, Y, F, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩

/-- The effective form of `HasCobordism.to_all`. -/
theorem HasCobordismEff.to_all {P₀ P₁ : CompactOrientedSuborbifold c m}
    (h : HasCobordismEff P₀ P₁) : HasCobordismEff_all P₀ P₁ := by
  obtain ⟨q, hq, Y, F, -, hLUC, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  exact ⟨q, hq, Y, F, hLUC, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩

/-- **Cobordant perturbations have the same integrals of closed forms** (Corollary 15.4.4's
argument, 2021 p. 703, on the polyfold), with no partitions of unity on `Y`:
`integral_eq_of_hasCobordism` for `HasCobordism_all`. -/
theorem integral_eq_of_hasCobordism_all {P₀ P₁ : CompactOrientedSuborbifold c m}
    (h : HasCobordism_all P₀ P₁) (τ : ScForm c (m + 1)) (hτ : ScForm.d τ = 0) :
    P₀.integral τ = P₁.integral τ := by
  obtain ⟨q, hq, Y, F, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  have hω : q.X.epFormsInftyD (m + 1) (ScForm.toStructure q hq τ) = 0 := by
    rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
  have := SBLocalization.integral_eq_of_cobordism_all F hΘ' hcpt' hT' hloc'
    (fun ω => P₀.integral (ScForm.mk q hq ω)) (fun ω => P₁.integral (ScForm.mk q hq ω)) hbd
    (ScForm.toStructure q hq τ) hω
  simpa only [ScForm.mk_toStructure] using this

/-- **Cobordant perturbations have the same effective integrals of closed forms** (2021 p. 703),
with no partitions of unity on `Y`: `integralEff_eq_of_hasCobordismEff` for
`HasCobordismEff_all`. -/
theorem integralEff_eq_of_hasCobordismEff_all {P₀ P₁ : CompactOrientedSuborbifold c m}
    (h : HasCobordismEff_all P₀ P₁) (τ : ScForm c (m + 1)) (hτ : ScForm.d τ = 0) :
    P₀.integralEff τ = P₁.integralEff τ := by
  obtain ⟨q, hq, Y, F, hLUC, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  have hω : q.X.epFormsInftyD (m + 1) (ScForm.toStructure q hq τ) = 0 := by
    rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
  have := SBLocalization.integralEff_eq_of_cobordism_all F hLUC hΘ' hcpt' hT' hloc'
    (fun ω => P₀.integralEff (ScForm.mk q hq ω)) (fun ω => P₁.integralEff (ScForm.mk q hq ω))
    hbd (ScForm.toStructure q hq τ) hω
  simpa only [ScForm.mk_toStructure] using this

/-- **Every `P` is cobordant to itself** (`Y = X`, `F = id`, `Θ̃ = 0`), with no partitions of
unity: `hasCobordism_refl` without `hPU`. -/
theorem hasCobordism_refl_all (P : CompactOrientedSuborbifold c m) : HasCobordism_all P P := by
  set q := c.out
  have hq : (⟦q⟧ : PolyfoldClass Z) = c := Quotient.out_eq c
  have hemp : ∀ x, x ∉ q.X.X.PObj.boundary ∩ EpGroupoid.supp (0 : q.X.Obj → ℚ) := fun x hx =>
    lt_irrefl (0 : ℚ) hx.2
  have hcpt0 : q.X.X.IsCompactBranched (0 : q.X.Obj → ℚ) := by
    have : q.X.X.orbitSupp (0 : q.X.Obj → ℚ) = ∅ := by
      rw [orbitSupp, image_eq_empty, eq_empty_iff_forall_notMem]
      exact fun x hx => lt_irrefl (0 : ℚ) hx
    rw [IsCompactBranched, this]; exact isCompact_empty
  have hloc0 : ∀ x ∈ EpGroupoid.supp (0 : q.X.Obj → ℚ),
      ∃ C : q.X.X.OrientedTameStructure (m + 1 + 1) 0 x, C.Represents fun _ => 0 :=
    fun x hx => absurd hx (lt_irrefl (0 : ℚ))
  refine ⟨q, hq, q.X, EpFunctor.id _, 0, fun _ => 0, q.X.X.isBranchedEpSubgroupoid_zero,
    hcpt0, q.X.X.isOrientation_zero, hloc0, fun ω => ?_⟩
  rw [sub_self]
  exact SBLocalization.boundaryMeasure_univ_eq_zero (B := q.X) (Nat.succ_pos m)
    q.X.X.isBranchedEpSubgroupoid_zero hcpt0 q.X.X.isOrientation_zero hloc0 hemp _

/-- **Every `P` is cobordant to itself for the effective integral** (`Y = X`, which has (LUC) by
(ZHOU)), with no partitions of unity: `hasCobordismEff_refl` without `hPU`. -/
theorem hasCobordismEff_refl_all (P : CompactOrientedSuborbifold c m) :
    HasCobordismEff_all P P := by
  set q := c.out
  have hq : (⟦q⟧ : PolyfoldClass Z) = c := Quotient.out_eq c
  have hemp : ∀ x, x ∉ q.X.X.PObj.boundary ∩ EpGroupoid.supp (0 : q.X.Obj → ℚ) := fun x hx =>
    lt_irrefl (0 : ℚ) hx.2
  have hcpt0 : q.X.X.IsCompactBranched (0 : q.X.Obj → ℚ) := by
    have : q.X.X.orbitSupp (0 : q.X.Obj → ℚ) = ∅ := by
      rw [orbitSupp, image_eq_empty, eq_empty_iff_forall_notMem]
      exact fun x hx => lt_irrefl (0 : ℚ) hx
    rw [IsCompactBranched, this]; exact isCompact_empty
  have hloc0 : ∀ x ∈ EpGroupoid.supp (0 : q.X.Obj → ℚ),
      ∃ C : q.X.X.OrientedTameStructure (m + 1 + 1) 0 x, C.Represents fun _ => 0 :=
    fun x hx => absurd hx (lt_irrefl (0 : ℚ))
  refine ⟨q, hq, q.X, EpFunctor.id _, q.X.X.proposition_7_4_10_of_isZhou q.isZhou, 0,
    fun _ => 0, q.X.X.isBranchedEpSubgroupoid_zero, hcpt0, q.X.X.isOrientation_zero, hloc0,
    fun ω => ?_⟩
  rw [sub_self]
  exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _

end CompactOrientedSuborbifold

end PolyfoldClass

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization SEP

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **2021 Theorem 16.6.6 from the cobordism** (p. 739; 2017: Theorem 16.8), with no sc-smooth
partitions of unity: `theorem_16_6_6_hyp` without `hPU`, for cobordisms in the sense of
`HasCobordism_all`, `HasCobordismEff_all`. -/
theorem theorem_16_6_6_hyp_all (s : FredholmSection c)
    (n : Y → ℝ) (U : Set Z) (m : ℕ)
    (IsInherited : OrientationRep s → OrientedPerturbation s.1 m → Prop)
    (hcob : ∀ o P₀ P₁, P₀.IsAdmissible n U → IsInherited o P₀ → P₁.IsAdmissible n U →
      IsInherited o P₁ →
      P₀.toCompactOrientedSuborbifold.HasCobordism_all P₁.toCompactOrientedSuborbifold)
    (hcobEff : ∀ o P₀ P₁, P₀.IsAdmissible n U → IsInherited o P₀ → P₁.IsAdmissible n U →
      IsInherited o P₁ →
      P₀.toCompactOrientedSuborbifold.HasCobordismEff_all P₁.toCompactOrientedSuborbifold) :
    theorem_16_6_6_statement s n U m IsInherited := by
  intro hbd _ _ _ _ o
  refine ⟨fun P _ _ τ η => ⟨?_, ?_⟩, fun P₀ P₁ h₀ i₀ h₁ i₁ τ hτ => ?_⟩
  · exact OrientedSuborbifold.integral_add_d_all hbd _ _ _ τ η
  · exact OrientedSuborbifold.integralEff_add_d_all hbd _ _ _ τ η
  exact ⟨CompactOrientedSuborbifold.integral_eq_of_hasCobordism_all
      (hcob o P₀ P₁ h₀ i₀ h₁ i₁) τ hτ,
    CompactOrientedSuborbifold.integralEff_eq_of_hasCobordismEff_all
      (hcobEff o P₀ P₁ h₀ i₀ h₁ i₁) τ hτ⟩

/-- **The cobordism hypotheses of `theorem_16_6_6_hyp_all` are satisfiable** (2021 p. 739): for
the predicate that singles out one perturbation `P` they hold, with no partitions of unity. -/
theorem theorem_16_6_6_hyp_hcob_witness_all
    {s : FredholmSection c} {m : ℕ} (P : OrientedPerturbation s.1 m) (n : Y → ℝ) (U : Set Z) :
    ∀ (o : OrientationRep s) (P₀ P₁ : OrientedPerturbation s.1 m), P₀.IsAdmissible n U →
      (fun _ Q => Q = P) o P₀ → P₁.IsAdmissible n U → (fun _ Q => Q = P) o P₁ →
      P₀.toCompactOrientedSuborbifold.HasCobordism_all P₁.toCompactOrientedSuborbifold ∧
        P₀.toCompactOrientedSuborbifold.HasCobordismEff_all P₁.toCompactOrientedSuborbifold := by
  rintro o P₀ P₁ - rfl - rfl
  exact ⟨CompactOrientedSuborbifold.hasCobordism_refl_all _,
    CompactOrientedSuborbifold.hasCobordismEff_refl_all _⟩

namespace ModelPerturbation

variable {a : SectionRep c} {m : ℕ}

/-- **A cobordism in the model is a cobordism on the polyfold** (2021 p. 739), with no partitions
of unity: `hasCobordism` for `HasOrientedCobordism_all`. -/
theorem hasCobordism_all (M₀ M₁ : ModelPerturbation a m)
    (h : M₀.toOrientedRegularPerturbation.HasOrientedCobordism_all
      M₁.toOrientedRegularPerturbation) :
    M₀.toCompact.HasCobordism_all M₁.toCompact := by
  obtain ⟨Y', F, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  refine ⟨a.S.toPolyfoldStructure, toPolyfoldStructure_mem a.hS, Y', F, Θ', T', hΘ', hcpt',
    hT', hloc', fun ω => ?_⟩
  exact (hbd ω).trans
    (congrArg₂ (· - ·) (M₁.integral_toCompact ω).symm (M₀.integral_toCompact ω).symm)

/-- **An effective cobordism in the model is one on the polyfold**, with no partitions of
unity. -/
theorem hasCobordismEff_all (M₀ M₁ : ModelPerturbation a m)
    (h : M₀.toOrientedRegularPerturbation.HasOrientedCobordismEff_all
      (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou) M₁.toOrientedRegularPerturbation) :
    M₀.toCompact.HasCobordismEff_all M₁.toCompact := by
  obtain ⟨Y', F, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  refine ⟨a.S.toPolyfoldStructure, toPolyfoldStructure_mem a.hS, Y', F, hLUCY, Θ', T', hΘ',
    hcpt', hT', hloc', fun ω => ?_⟩
  exact (hbd ω).trans
    (congrArg₂ (· - ·) (M₁.integralEff_toCompact ω).symm (M₀.integralEff_toCompact ω).symm)

/-- **A cobordism between regular perturbations of the model is a cobordism on the polyfold**
between their classes, with no partitions of unity. -/
theorem hasCobordism_ofRegular_all {P₀ P₁ : OrientedRegularPerturbation a.S.A a.F m}
    (h : P₀.HasOrientedCobordism_all P₁) :
    (ofRegular P₀).toCompact.HasCobordism_all (ofRegular P₁).toCompact := by
  refine hasCobordism_all _ _ ?_
  obtain ⟨Y', F, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  refine ⟨Y', F, Θ', T', hΘ', hcpt', hT', hloc', fun ω => ?_⟩
  rw [integral_ofRegular, integral_ofRegular]
  exact hbd ω

/-- The effective form of `hasCobordism_ofRegular_all`. -/
theorem hasCobordismEff_ofRegular_all {P₀ P₁ : OrientedRegularPerturbation a.S.A a.F m}
    (h : P₀.HasOrientedCobordismEff_all (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou) P₁) :
    (ofRegular P₀).toCompact.HasCobordismEff_all (ofRegular P₁).toCompact := by
  refine hasCobordismEff_all _ _ ?_
  obtain ⟨Y', F, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  refine ⟨Y', F, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', fun ω => ?_⟩
  rw [integralEff_ofRegular, integralEff_ofRegular]
  exact hbd ω

end ModelPerturbation

/-- **2021 Theorem 16.6.6 from the cobordisms in the model of the orientation** (p. 739; 2017:
Theorem 16.8), with no sc-smooth partitions of unity: `theorem_16_6_6_of_model` without `hPU`,
for cobordisms in the sense of `HasOrientedCobordism_all`, `HasOrientedCobordismEff_all`. -/
theorem theorem_16_6_6_of_model_all
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) (m : ℕ)
    (Can : ∀ o : OrientationRep s, OrientedRegularPerturbation o.a.S.A o.a.F m → Prop)
    (hcob : c.polyfold.boundary = ∅ → s.1.HasCompactSolutionSet → ∀ (o : OrientationRep s)
      (P₀ P₁ : OrientedRegularPerturbation o.a.S.A o.a.F m), Can o P₀ → Can o P₁ →
      P₀.HasOrientedCobordism_all P₁ ∧
        P₀.HasOrientedCobordismEff_all (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou)
          P₁) :
    theorem_16_6_6_statement s n U m (IsInheritedFrom Can) := by
  intro hbd hcs _ _ _ o
  refine ⟨fun P _ _ τ η => ⟨?_, ?_⟩, ?_⟩
  · exact OrientedSuborbifold.integral_add_d_all hbd _ _ _ τ η
  · exact OrientedSuborbifold.integralEff_add_d_all hbd _ _ _ τ η
  rintro P₀ P₁ - ⟨M₀, c₀, rfl⟩ - ⟨M₁, c₁, rfl⟩ τ hτ
  obtain ⟨h, he⟩ := hcob hbd hcs o _ _ c₀ c₁
  exact ⟨CompactOrientedSuborbifold.integral_eq_of_hasCobordism_all
      (ModelPerturbation.hasCobordism_ofRegular_all h) τ hτ,
    CompactOrientedSuborbifold.integralEff_eq_of_hasCobordismEff_all
      (ModelPerturbation.hasCobordismEff_ofRegular_all he) τ hτ⟩

/-- **2021 Theorem 16.6.6 along the text's argument** (p. 739; 2017: Theorem 16.8), with no
sc-smooth partitions of unity on `Z`: `theorem_16_6_6_of_cylinder` without `hPU`.  The field `pu`
of `CylinderInput` is kept: it constructs the cobordism (Theorem 15.3.9 on `[0, 1] × X`). -/
theorem theorem_16_6_6_of_cylinder_all
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) (m : ℕ)
    (Can : ∀ o : OrientationRep s, OrientedRegularPerturbation o.a.S.A o.a.F m → Prop)
    (H : ∀ o : OrientationRep s, CylinderInput Can o) :
    theorem_16_6_6_statement s n U m (IsInheritedFrom Can) :=
  theorem_16_6_6_of_model_all s n U m Can fun hbd hcs o P₀ P₁ h₀ h₁ =>
    have h := hasOrientedCobordism_of_cylinderInput hbd hcs (H o) P₀ P₁ h₀ h₁
    ⟨h.1.to_all, h.2.to_all⟩

/-- **The cobordism hypotheses of `theorem_16_6_6_of_model_all` are satisfiable** (2021 p. 739):
every perturbation of the model is cobordant to itself, with no partitions of unity. -/
theorem theorem_16_6_6_of_model_hcob_witness_all
    {s : FredholmSection c} {m : ℕ} (o : OrientationRep s)
    (P : OrientedRegularPerturbation o.a.S.A o.a.F m) :
    P.HasOrientedCobordism_all P ∧
      P.HasOrientedCobordismEff_all (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou) P :=
  ⟨OrientedRegularPerturbation.hasOrientedCobordism_refl_all P,
    OrientedRegularPerturbation.hasOrientedCobordismEff_refl_all _ P⟩

/-! ### The canonical orientation -/

/-- **The orientation of Definition 16.6.5 is one of Definition 6.6.16 when `∂Z = ∅`** (2021
p. 739), from sc-smooth bump functions on `Z`: `isSectionOrientation_of_boundary_eq_empty` with
`hPU` replaced by `hbump`, the property it was used for. -/
theorem OrientationRep.isSectionOrientation_of_boundary_eq_empty_all
    (hbump : c.polyfold.AdmitsBumpFunctions) (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} (o : OrientationRep s)
    (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F) :
    haveI := paracompactSpace_rn_prod o.a.S.A.X.PObj
    haveI := paracompactSpace_rn_pullback o.a.S.A.B
    IsSectionOrientation o.a.F o.hF.2 o.o := by
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  exact o.isSectionOrientation (o.a.S.A.X.isTame_of_degIndex_eq_zero hd)
    ((c.polyfold.definition_16_1_5_one).1 hbump o.a.S.toPolyfoldStructure
      (toPolyfoldStructure_mem o.a.hS)) hft

/-- **The standing hypotheses of Theorem 16.6.6 in the model of an orientation `o`** (2021
p. 739), Fredholm index `k`, with no partitions of unity: `CanonicalInput o k` without the field
`pu`.  Tame germ data of the representative `F`, and index `k` at every smooth point. -/
structure CanonicalInput_all {s : FredholmSection c} (o : OrientationRep s) (k : ℕ) : Prop where
  tame : o.a.S.A.B.IsScFredholmSectionTame o.a.F
  index : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x (k : ℤ)

/-- `CanonicalInput` gives `CanonicalInput_all`. -/
theorem CanonicalInput.to_all {s : FredholmSection c} {o : OrientationRep s} {k : ℕ}
    (H : CanonicalInput o k) : CanonicalInput_all o k :=
  ⟨H.tame, H.index⟩

/-- **The cobordisms of Corollary 15.4.4 in the model of `o` from the collar extension** (2021
pp. 699, 703): for `∂Z = ∅` and `Z` with sc-smooth bump functions, any two regular perturbations
of the model with the canonical orientation of `(F, o)` are joined by an oriented compact
cobordism and by an effective one, with no partitions of unity. -/
theorem hasOrientedCobordism_of_canonicalInput_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} {m : ℕ} {o : OrientationRep s}
    (H : CanonicalInput_all o (m + 1)) (P₀ P₁ : OrientedRegularPerturbation o.a.S.A o.a.F m)
    (h₀ : IsCanonicalPerturbation o.hF.2 o.hsec o.o P₀)
    (h₁ : IsCanonicalPerturbation o.hF.2 o.hsec o.o P₁) :
    P₀.HasOrientedCobordism_all P₁ ∧
      P₀.HasOrientedCobordismEff_all (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou)
        P₁ := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) o.a.S.A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) o.a.S.A.X.PMor
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hpara := o.a.S.paracompact
  have hbumpq : o.a.S.A.X.PObj.AdmitsBumpFunctions :=
    (c.polyfold.definition_16_1_5_one).1 hbump o.a.S.toPolyfoldStructure
      (toPolyfoldStructure_mem o.a.hS)
  have hbumpC : (o.a.S.A.cubeSEP 1).X.PObj.AdmitsBumpFunctions :=
    admitsBumpFunctions_prod_cube hbumpq
  have hsec' : (o.a.S.A.cubeSEP 1).B.HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbumpC
  have ho := o.isSectionOrientation_of_boundary_eq_empty_all hbump hbd H.tame
  have hinvC := isOrInvariant_cubeOrientation o.hF H.tame o.hsec hsec' o.o o.isOrientation.2
  have hLUC := o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou
  exact ⟨hasOrientedCobordism_collar_all hd o.hF H.tame o.hsec hsec' o.o ho hinvC H.index hpara
      (o.a.S.A.X.theorem_12_3_2_1.2 hbumpq) h₀ h₁,
    hasOrientedCobordismEff_collar_all hd o.hF H.tame o.hsec hsec' o.o ho hinvC H.index hpara
      (o.a.S.A.X.theorem_12_3_2_1.2 hbumpq) hLUC (isLUC_cubeSEP hLUC) h₀ h₁⟩

/-- **2021 Theorem 16.6.6, p. 739 (2017: Theorem 16.8), for the orientation inherited from
`(f, o)`, with no sc-smooth partitions of unity.**  Let `Z` admit sc-smooth bump functions.  For
`∂Z = ∅`, `f` with compact solution set and `(n, U)` controlling compactness, and for every
orientation `o` of `f` (Definition 16.6.5) whose model has tame germ data and Fredholm index
`m + 1` (`CanonicalInput_all`): over the admissible perturbed solution sets `θ̂ = λ ∘ f` with the
orientation inherited from `(f, o)`, `∫_θ̂ τ` and `∮_θ̂ τ` depend only on `[τ]`, and a closed `τ`
has the same `∫_θ̂ τ` and `∮_θ̂ τ` for any two of them.  This is `theorem_16_6_6_canonical` with
`hPU` replaced by `hbump` (its use other than Stokes) and `CanonicalInput` by
`CanonicalInput_all`; the cobordism is the collar extension. -/
theorem theorem_16_6_6_canonical_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) (m : ℕ) :
    theorem_16_6_6_statement s n U m (fun o Q => CanonicalInput_all o (m + 1) ∧
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q) := by
  intro hbd _ _ _ _ o
  refine ⟨fun P _ _ τ η => ⟨?_, ?_⟩, ?_⟩
  · exact OrientedSuborbifold.integral_add_d_all hbd _ _ _ τ η
  · exact OrientedSuborbifold.integralEff_add_d_all hbd _ _ _ τ η
  rintro P₀ P₁ - ⟨H, M₀, c₀, rfl⟩ - ⟨-, M₁, c₁, rfl⟩ τ hτ
  obtain ⟨h, he⟩ := hasOrientedCobordism_of_canonicalInput_all hbump hbd H _ _ c₀ c₁
  exact ⟨CompactOrientedSuborbifold.integral_eq_of_hasCobordism_all
      (ModelPerturbation.hasCobordism_ofRegular_all h) τ hτ,
    CompactOrientedSuborbifold.integralEff_eq_of_hasCobordismEff_all
      (ModelPerturbation.hasCobordismEff_ofRegular_all he) τ hτ⟩

/-- **2021 Theorem 16.6.6 (p. 739) with the standing hypotheses in the model of every
orientation, with no sc-smooth partitions of unity**: `theorem_16_6_6_canonical_of_forall` with
`hPU` replaced by `hbump` and `CanonicalInput` by `CanonicalInput_all`. -/
theorem theorem_16_6_6_canonical_of_forall_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) (m : ℕ)
    (H : ∀ o : OrientationRep s, CanonicalInput_all o (m + 1)) :
    theorem_16_6_6_statement s n U m
      (IsInheritedFrom fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) :=
  theorem_16_6_6_of_model_all s n U m _ fun hbd _ o P₀ P₁ h₀ h₁ =>
    hasOrientedCobordism_of_canonicalInput_all hbump hbd (H o) P₀ P₁ h₀ h₁

/-- **Regular perturbations in general position exist in the model of an orientation** (2021
Corollary 15.3.10 (1), p. 699), from sc-smooth bump functions on `Z`:
`OrientationRep.exists_isRegularPerturbation` with `hPU` replaced by `hbump`, the property it was
used for. -/
theorem OrientationRep.exists_isRegularPerturbation_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) (o : OrientationRep s)
    (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F) :
    ∃ Λ : o.a.S.A.W → ℚ≥0, IsRegularPerturbation o.a.S.A o.a.F (o.a.S.normOf n) (o.a.g ⁻¹' U) Λ ∧
      IsInGeneralPosition o.a.S.A o.a.F Λ := by
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hbumpq : o.a.S.A.X.PObj.AdmitsBumpFunctions :=
    (c.polyfold.definition_16_1_5_one).1 hbump o.a.S.toPolyfoldStructure
      (toPolyfoldStructure_mem o.a.hS)
  have hSa : o.a.S.A.E.HasCompactSolutionSetEp o.a.F := by
    rw [← o.a.hasCompactSolutionSet_iff, o.ha]; exact hcs
  have hcca := (o.a.controlsCompactness_iff hn hU).1 (by rw [o.ha]; exact hcc)
  obtain ⟨Λ, hreg, hgp, -⟩ := corollary_15_3_10_1 hd o.a.S.paracompact
    (o.a.S.A.X.theorem_12_3_2_1.2 hbumpq) o.hF hft hSa hcca
  exact ⟨Λ, hreg, hgp⟩

/-- **2021 Theorem 16.6.6, p. 739, the admissible perturbations exist**, from sc-smooth bump
functions on `Z`: `theorem_16_6_6_canonical_exists` with `hPU` replaced by `hbump` and
`CanonicalInput` by `CanonicalInput_all`. -/
theorem theorem_16_6_6_canonical_exists_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalInput_all o (m + 1)) :
    ∃ Q : OrientedPerturbation s.1 m, Q.IsAdmissible n U ∧
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q := by
  obtain ⟨Λ, hreg, hgp⟩ := o.exists_isRegularPerturbation_all hbump hbd hcs hn hU hcc H.tame
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have hbumpq : o.a.S.A.X.PObj.AdmitsBumpFunctions :=
    (c.polyfold.definition_16_1_5_one).1 hbump o.a.S.toPolyfoldStructure
      (toPolyfoldStructure_mem o.a.hS)
  have ho := o.isSectionOrientation_of_boundary_eq_empty_all hbump hbd H.tame
  have hgood : ∀ x ∈ o.a.S.A.X.PObj.boundary, 0 < Λ (o.a.F x) →
      SBLocalization.IsGoodPositionAt o.a.F Λ x :=
    fun x _ hpos => isGoodPositionAt_of_isInGeneralPosition o.hF H.tame hreg.2.1.1 hgp hpos
  have hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (o.a.F z) : ℚ)),
      o.a.S.A.B.IsIndexAt o.a.F x (m + 1 : ℕ) := fun x hx =>
    H.index x (mem_smoothSet_of_pos H.tame hreg.2.1.1 (by exact_mod_cast hx))
  set P := OrientedRegularPerturbation.canonical hX hbumpq o.hF H.tame o.hsec o.o
    o.isOrientation.2 ho hreg hgood hidx
  refine ⟨(ModelPerturbation.ofRegular P).toOrientedPerturbation o.ha,
    ⟨isControlledBy_of_isRegularPerturbation o.a hreg.2.1.1 (fun x => (hreg.2.2.2.1 x).le)
      hreg.2.2.1, o.a, Λ, hreg.2.1.1, o.ha, rfl, hgp⟩, P, ?_, rfl⟩
  exact isCanonicalPerturbation_canonical hX hbumpq o.hF H.tame o.hsec o.o o.isOrientation.2 ho
    hreg hgood hidx

/-- **2021 Theorem 16.6.6, p. 739, existence and independence, with no sc-smooth partitions of
unity**: admissible perturbed solution sets with the orientation inherited from `(f, o)` exist,
and a closed `τ` has the same `∫_θ̂ τ` and `∮_θ̂ τ` for any two of them.  This is
`theorem_16_6_6_canonical_wellDefined` with `hPU` replaced by `hbump` and `CanonicalInput` by
`CanonicalInput_all`. -/
theorem theorem_16_6_6_canonical_wellDefined_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalInput_all o (m + 1)) :
    (∃ Q : OrientedPerturbation s.1 m, Q.IsAdmissible n U ∧
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q) ∧
    ∀ Q₀ Q₁ : OrientedPerturbation s.1 m, Q₀.IsAdmissible n U →
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q₀ →
      Q₁.IsAdmissible n U →
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q₁ →
      ∀ τ : ScForm c.polyfold (m + 1), ScForm.d τ = 0 →
        Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ :=
  ⟨theorem_16_6_6_canonical_exists_all hbump hbd hcs hn hU hcc H,
    fun Q₀ Q₁ h₀ i₀ h₁ i₁ => (theorem_16_6_6_canonical_all hbump s n U m hbd hcs hn hU hcc o).2
      Q₀ Q₁ h₀ ⟨H, i₀⟩ h₁ ⟨H, i₁⟩⟩

section SolutionSet

open EpGroupoid

/-- **Every admissible `Λ` in the model gives a canonically oriented solution set** (2021
Theorems 15.4.1, 15.4.3), from sc-smooth bump functions on `Z`:
`exists_modelSolutionSet_canonical` with `hPU` replaced by `hbump` (it was used for bump functions
only) and `CanonicalInput` by `CanonicalInput_all`. -/
theorem exists_modelSolutionSet_canonical_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n)
    {U : Set Z} (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) {m : ℕ}
    {o : OrientationRep s} (H : CanonicalInput_all o (m + 1)) {Λ : o.a.S.A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection o.a.S.A Λ)
    (ht : ScPlusMultisection.IsControlledBy (c := c) ⟦ofFunctor o.a.S o.a.hS Λ hΛ⟧ n U)
    (hgp : IsInGeneralPosition o.a.S.A o.a.F Λ) :
    ∃ M : ModelSolutionSet o.a m, M.Λ = Λ ∧ IsCanonicalFor M.Λ o.hF.2 o.hsec o.o (m + 1) M.T ∧
      (∀ x, pointwiseNorm (o.a.S.normOf n) Λ x ≤ 1) ∧ domSupp Λ ⊆ o.a.g ⁻¹' U ∧
      IsTransversal o.a.F Λ := by
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have hbumpq : o.a.S.A.X.PObj.AdmitsBumpFunctions :=
    (c.polyfold.definition_16_1_5_one).1 hbump o.a.S.toPolyfoldStructure
      (toPolyfoldStructure_mem o.a.hS)
  have ho := o.isSectionOrientation_of_boundary_eq_empty_all hbump hbd H.tame
  have hcca := (o.a.controlsCompactness_iff hn hU).1 (by rw [o.ha]; exact hcc)
  set b := ofFunctor o.a.S o.a.hS Λ hΛ
  have hN1 : ∀ x, pointwiseNorm (o.a.S.normOf n) Λ x ≤ 1 := by
    intro x
    rw [← normLam_eq o.a.hS n Λ b.lam x fun w _ => b.comm w]
    exact ht.1 _
  have hdom : domSupp Λ ⊆ o.a.g ⁻¹' U := by
    intro x hx
    apply ht.2
    rw [← remark_16_5_3 b]
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have htr := IsInGeneralPosition.isTransversal o.hF hΛ hgp
  have hgood : ∀ x, 0 < Λ (o.a.F x) → SBLocalization.IsGoodPositionAt o.a.F Λ x :=
    fun x hpos => isGoodPositionAt_of_isInGeneralPosition o.hF H.tame hΛ hgp hpos
  obtain ⟨hbr, hcpt⟩ := theorem_15_4_3_isBranched_hyp o.hF H.tame hcca hΛ hdom hN1 htr
    fun x _ => hgood x
  have hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (o.a.F z) : ℚ)),
      o.a.S.A.B.IsIndexAt o.a.F x (m + 1 : ℕ) := fun x hx =>
    H.index x (mem_smoothSet_of_pos H.tame hΛ (by exact_mod_cast hx))
  have hcan := theorem_15_4_1 hX hbumpq o.hF H.tame hΛ o.hsec o.o o.isOrientation.2 ho
    (fun x hx => hgood x (by exact_mod_cast hx)) hidx
  exact ⟨⟨Λ, hΛ, canonicalOrientation Λ o.hF.2 o.hsec o.o, hbr, hcpt, hcan.1, hcan.loc⟩, rfl, hcan,
    hN1, hdom, htr⟩

/-- **2021 Theorem 16.6.6, p. 739: every admissible `λ` gives a canonically oriented `θ̂`**, from
sc-smooth bump functions on `Z`: `theorem_16_6_6_canonical_solutionSet` with `hPU` replaced by
`hbump` (it was used for bump functions only, not for Stokes) and `CanonicalInput` by
`CanonicalInput_all`. -/
theorem theorem_16_6_6_canonical_solutionSet_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n)
    {U : Set Z} (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) {m : ℕ}
    {o : OrientationRep s} (H : CanonicalInput_all o (m + 1)) (t : ScPlusMultisection c)
    (ht : t.IsControlledBy n U) (hgp : s.1.IsInGeneralPositionWith t) :
    ∃ Q : OrientedPerturbation s.1 m, Q.t = t ∧ Q.IsAdmissible n U ∧
      IsCanonicalSolutionSet o Q := by
  obtain ⟨Λ, hΛ, hl⟩ := exists_functor_rep t o.a.hS
  have ht' : (⟦ofFunctor o.a.S o.a.hS Λ hΛ⟧ : ScPlusMultisection c) = t :=
    mk_ofFunctor_eq t o.a.hS hΛ hl
  have hgpΛ := (ScSection.isInGeneralPositionWith_iff_of_rep s.1 s.2 t o.a o.ha hΛ hl).1 hgp
  rw [← ht'] at ht
  obtain ⟨M, rfl, hcan, -⟩ := exists_modelSolutionSet_canonical_all hbump hbd hn hU hcc H hΛ ht
    hgpΛ
  exact ⟨M.toOrientedPerturbation o.ha, ht', ⟨ht, o.a, M.Λ, hΛ, o.ha, rfl, hgpΛ⟩, M, hcan, rfl⟩

/-- **Admissible structurable perturbations have the inherited orientation** (2021 p. 739), from
sc-smooth bump functions on `Z`: `theorem_16_6_6_canonical_solutionSet_of_isStructurable` with
`hPU` replaced by `hbump` and `CanonicalInput` by `CanonicalInput_all`. -/
theorem theorem_16_6_6_canonical_solutionSet_of_isStructurable_all
    (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n)
    {U : Set Z} (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) {m : ℕ}
    {o : OrientationRep s} (H : CanonicalInput_all o (m + 1)) {Λ : o.a.S.A.W → ℚ≥0}
    (hstr : IsStructurable o.a.S.A Λ)
    (ht : ScPlusMultisection.IsControlledBy (c := c) ⟦ofFunctor o.a.S o.a.hS Λ hstr.1⟧ n U)
    (hlt : ∀ z, c.normLam n (ofFunctor o.a.S o.a.hS Λ hstr.1).lam z < 1)
    (hgp : s.1.IsInGeneralPositionWith ⟦ofFunctor o.a.S o.a.hS Λ hstr.1⟧) :
    ∃ Q : OrientedPerturbation s.1 m, Q.t = ⟦ofFunctor o.a.S o.a.hS Λ hstr.1⟧ ∧
      Q.IsAdmissible n U ∧ IsCanonicalSolutionSet o Q ∧
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q := by
  have hgpΛ := (ScSection.isInGeneralPositionWith_iff_of_rep s.1 s.2 _ o.a o.ha hstr.1
    (toFun_of_mk_ofFunctor_eq rfl)).1 hgp
  have hcca := (o.a.controlsCompactness_iff hn hU).1 (by rw [o.ha]; exact hcc)
  obtain ⟨M, rfl, hcan, -, hdom, htr⟩ :=
    exists_modelSolutionSet_canonical_all hbump hbd hn hU hcc H hstr.1 ht hgpΛ
  have hlt' : ∀ x, pointwiseNorm (o.a.S.normOf n) M.Λ x < 1 := fun x => by
    rw [← normLam_eq o.a.hS n M.Λ (ofFunctor o.a.S o.a.hS M.Λ hstr.1).lam x
      fun w _ => (ofFunctor o.a.S o.a.hS M.Λ hstr.1).comm w]
    exact hlt _
  exact ⟨M.toOrientedPerturbation o.ha, rfl, ⟨ht, hgp⟩, ⟨M, hcan, rfl⟩,
    isInheritedFrom_of_isRegularPerturbation M hcan ⟨hcca, hstr, hdom, hlt', htr⟩⟩

end SolutionSet

end StrongPolyfoldBundle

end Polyfold
