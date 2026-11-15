import Polyfold.Chapter16.PointTameShrinking

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.6, p. 739: **Theorem 16.6.6** (2017: Theorem 16.8) **for Fredholm index `0`, on the
polyfold**: the weighted counts `∫_θ̂ τ`, `∮_θ̂ τ` of closed `0`-forms over the perturbed solution
sets `θ̂ = λ ∘ f` of dimension `0`.  Numbers and pages are the 2021 text's.

## The text, paraphrased

(Theorem 16.6.6) Let `p : Y → Z` be a strong polyfold bundle with `∂Z = ∅`, `f` an oriented
sc-Fredholm section with compact solution set, `(n, U)` controlling compactness.  For
sc⁺-multisections `λ` controlled by `(n, U)` with `(f, λ)` in general position, `θ = λ ∘ f`
with the inherited orientation is a compact oriented branched suborbifold of dimension the
Fredholm index; for closed `τ` the integrals `∫_θ̂ τ`, `∮_θ̂ τ` do not depend on `λ`.  For
index `0` they are weighted signed counts (Definition 9.5.6 for `n = 0`).

## What is formalized

Polyfold level (namespace `Polyfold.PolyfoldClass`):
* `PointSuborbifold c`: a compact oriented branched suborbifold of `Z`, tame of dimension `0`
  (`IsTameOriented θ 0`); `count`, `countEff` (`OrientedSuborbifold.pointIntegralOfTame`,
  `pointIntegralEffOfTame`); `count_mk_rep`, `countEff_mk_rep` (the count in any model).
* `PointSuborbifold.HasCobordism`, `HasCobordismEff` (an oriented compact cobordism of dimension
  `1` in some model `(X, β) ∈ c`), **`count_eq_of_hasCobordism`**,
  **`countEff_eq_of_hasCobordismEff`**, `hasCobordism_refl`, `hasCobordismEff_refl`.

Strong polyfold bundles (namespace `Polyfold.StrongPolyfoldBundle`):
* `PointOrientedPerturbation s`: a `PointSuborbifold` whose function is `λ ∘ f`; `IsAdmissible`.
* **`theorem_16_6_6_index_zero_polyfold_statement`**: Theorem 16.6.6 for index `0` on the
  polyfold, with `OrientedSuborbifold.pointIntegralOfTame`;
  **`theorem_16_6_6_index_zero_polyfold_hyp`**: it holds given the cobordisms.
* From the models: `pointSuborbifold`, `pointMultisection`, `toPointOrientedPerturbation` (the
  class `[(Λ ∘ F, T̂), (X, γ)]` of a regular perturbation of dimension `0` of a model,
  `SBLocalization.PointPerturbation`); **`count_pointSuborbifold`**,
  `countEff_pointSuborbifold` (the counts on the polyfold are the counts in the model);
  `hasCobordism_pointSuborbifold`, `hasCobordismEff_pointSuborbifold`; `IsInheritedFromPoint`.
* **`theorem_16_6_6_index_zero_polyfold_of_model_statement`**: the model form
  `theorem_16_6_6_index_zero_statement` gives the polyfold form for the orientation inherited
  in the model; **`theorem_16_6_6_index_zero_polyfold_of_model`**: the polyfold form from the
  cobordisms in the model of the orientation (the hypotheses of
  `theorem_16_6_6_index_zero_of_model`).

## Reading

* As in dimension `≥ 1` (`IsInheritedFrom`), the orientation of `θ̂` inherited from `o` is read
  in the model that carries `o`, through a predicate `Can o` on the perturbations of that model.
* "Depends only on `[τ]`" has no content in degree `0`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z}

/-- A **compact oriented branched suborbifold of dimension `0`** of `(Z, c)` (Definitions
16.4.2, 16.4.4 with Definition 9.5.6 for `n = 0`). -/
structure PointSuborbifold (c : PolyfoldClass Z) : Type (u + 1) where
  /-- The oriented branched suborbifold `θ̂`. -/
  θ : OrientedSuborbifold c
  isCompact : θ.toBranched.IsCompact
  isTame : θ.IsTameOriented 0

namespace PointSuborbifold

/-- **The weighted signed count `∫_θ̂ τ`** of a `0`-form `τ` (2021 p. 732 for dimension `0`). -/
def count (P : PointSuborbifold c) (τ : ScForm c 0) : ℝ :=
  P.θ.pointIntegralOfTame P.isCompact P.isTame τ

/-- **The effective weighted count `∮_θ̂ τ`** of a `0`-form `τ`. -/
def countEff (P : PointSuborbifold c) (τ : ScForm c 0) : ℝ :=
  P.θ.pointIntegralEffOfTame P.isCompact P.isTame τ

/-- **The count is the count in every model**: for a representative `((Θ, T̂), (X, α))` of `θ̂`
and `ω ∈ Ω⁰_{ep,∞}(X)`, `∫_θ̂ [(ω, (X, α))] = ∫_{(Θ, T̂)} ω` (Definition 9.5.6 for `n = 0`). -/
theorem count_mk_rep (P : PointSuborbifold c) (a : OrientedRep c) (ha : ⟦a⟧ = P.θ)
    (ω : a.p.X.epFormsInfty 0) :
    P.count (ScForm.mk a.p a.mem ω) =
      a.p.X.pointBranchedIntegral a.A.isBranchedEpSubgroupoid
        (OrientedSuborbifold.isCompactBranched_of_mk P.isCompact a ha) a.A.isOrientation
        ((a.isPointTame_iff_isTameOriented).2
          ((OrientedSuborbifold.isTameOriented_iff P.θ).1 P.isTame a ha)) ω := by
  rw [count, OrientedSuborbifold.pointIntegralOfTame_eq P.θ P.isCompact P.isTame _ a ha,
    OrientedRep.pointIntegral, ScForm.toStructure_mk]

/-- **The effective count is the effective count in every model.** -/
theorem countEff_mk_rep (P : PointSuborbifold c) (a : OrientedRep c) (ha : ⟦a⟧ = P.θ)
    (ω : a.p.X.epFormsInfty 0) :
    P.countEff (ScForm.mk a.p a.mem ω) =
      a.p.X.pointBranchedIntegralEff (a.p.X.X.proposition_7_4_10_of_isZhou a.p.isZhou)
        a.A.isBranchedEpSubgroupoid
        (OrientedSuborbifold.isCompactBranched_of_mk P.isCompact a ha) a.A.isOrientation
        ((a.isPointTame_iff_isTameOriented).2
          ((OrientedSuborbifold.isTameOriented_iff P.θ).1 P.isTame a ha)) ω := by
  rw [countEff, OrientedSuborbifold.pointIntegralEffOfTame_eq P.θ P.isCompact P.isTame _ a ha,
    OrientedRep.pointIntegralEff, ScForm.toStructure_mk]

/-- `P₀` and `P₁` are joined by an **oriented compact cobordism of dimension `1`** (the proof of
Corollary 15.4.4 for index `0`, in a model `(X, β) ∈ c`): an ep-groupoid `Y` with partitions of
unity, an sc-smooth functor `F : Y → X` and a compact branched `Θ̃` on `Y`, oriented and tame of
dimension `1`, with `μ^{∂Θ̃}_{F^*ω}(∂S) = ∫_{P₁} [ω] − ∫_{P₀} [ω]` for every `0`-form `ω`. -/
def HasCobordism (P₀ P₁ : PointSuborbifold c) : Prop :=
  ∃ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) (Y : EP.{u}) (F : EpFunctor Y.X q.X.X)
    (_ : Y.X.HasScPartitionsOfUnity) (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F 0 ω) univ =
        P₁.count (ScForm.mk q hq ω) - P₀.count (ScForm.mk q hq ω)

/-- The effective form of `HasCobordism` (with the local unique continuation property on `Y`). -/
def HasCobordismEff (P₀ P₁ : PointSuborbifold c) : Prop :=
  ∃ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) (Y : EP.{u}) (F : EpFunctor Y.X q.X.X)
    (_ : Y.X.HasScPartitionsOfUnity) (hLUC : Y.X.IsLUC) (Θ' : Y.Obj → ℚ)
    (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT' (Y.hloc_hasLUC_dim1 hLUC hloc')
      (EP.epFormsInftyPullback F 0 ω) univ =
        P₁.countEff (ScForm.mk q hq ω) - P₀.countEff (ScForm.mk q hq ω)

/-- **Cobordant perturbations have the same counts of closed `0`-forms** (Corollary 15.4.4's
argument on the polyfold, read in the model of the cobordism: Stokes for `n = 1`). -/
theorem count_eq_of_hasCobordism {P₀ P₁ : PointSuborbifold c} (h : HasCobordism P₀ P₁)
    (τ : ScForm c 0) (hτ : ScForm.d τ = 0) : P₀.count τ = P₁.count τ := by
  obtain ⟨q, hq, Y, F, hPUY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  have hω : q.X.epFormsInftyD 0 (ScForm.toStructure q hq τ) = 0 := by
    rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
  have := EP.pointIntegral_eq_of_cobordism F hPUY hΘ' hcpt' hT' hloc'
    (fun ω => P₀.count (ScForm.mk q hq ω)) (fun ω => P₁.count (ScForm.mk q hq ω)) hbd
    (ScForm.toStructure q hq τ) hω
  simpa only [ScForm.mk_toStructure] using this

/-- **Cobordant perturbations have the same effective counts of closed `0`-forms.** -/
theorem countEff_eq_of_hasCobordismEff {P₀ P₁ : PointSuborbifold c} (h : HasCobordismEff P₀ P₁)
    (τ : ScForm c 0) (hτ : ScForm.d τ = 0) : P₀.countEff τ = P₁.countEff τ := by
  obtain ⟨q, hq, Y, F, hPUY, hLUC, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  have hω : q.X.epFormsInftyD 0 (ScForm.toStructure q hq τ) = 0 := by
    rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
  have := EP.pointIntegralEff_eq_of_cobordism F hPUY hLUC hΘ' hcpt' hT' hloc'
    (fun ω => P₀.countEff (ScForm.mk q hq ω)) (fun ω => P₁.countEff (ScForm.mk q hq ω)) hbd
    (ScForm.toStructure q hq τ) hω
  simpa only [ScForm.mk_toStructure] using this

private theorem zero_data (q : PolyfoldStructure Z) :
    (∀ x, x ∉ q.X.X.PObj.boundary ∩ EpGroupoid.supp (0 : q.X.Obj → ℚ)) ∧
      q.X.X.IsCompactBranched (0 : q.X.Obj → ℚ) ∧
      ∀ x ∈ EpGroupoid.supp (0 : q.X.Obj → ℚ),
        ∃ C : q.X.X.OrientedTameStructure (0 + 1) 0 x, C.Represents fun _ => 0 := by
  refine ⟨fun x hx => lt_irrefl (0 : ℚ) hx.2, ?_, fun x hx => absurd hx (lt_irrefl (0 : ℚ))⟩
  have : q.X.X.orbitSupp (0 : q.X.Obj → ℚ) = ∅ := by
    rw [orbitSupp, image_eq_empty, eq_empty_iff_forall_notMem]
    exact fun x hx => lt_irrefl (0 : ℚ) hx
  rw [IsCompactBranched, this]; exact isCompact_empty

/-- **The cobordism hypothesis is satisfiable**: every `P` is cobordant to itself (`Y = X`,
`F = id`, `Θ̃ = 0`), when `c` admits sc-smooth partitions of unity. -/
theorem hasCobordism_refl (hPU : c.AdmitsScPartitionsOfUnity) (P : PointSuborbifold c) :
    HasCobordism P P := by
  set q := c.out
  have hq : (⟦q⟧ : PolyfoldClass Z) = c := Quotient.out_eq c
  have hPUq := (c.definition_16_1_5_two).1 hPU q hq
  obtain ⟨hemp, hcpt0, hloc0⟩ := zero_data q
  refine ⟨q, hq, q.X, EpFunctor.id _, hPUq, 0, fun _ => 0, q.X.X.isBranchedEpSubgroupoid_zero,
    hcpt0, q.X.X.isOrientation_zero, hloc0, fun ω => ?_⟩
  rw [sub_self]
  exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary (B := q.X) hemp _

/-- **The effective cobordism hypothesis is satisfiable** (`Y = X` has (LUC) by (ZHOU)). -/
theorem hasCobordismEff_refl (hPU : c.AdmitsScPartitionsOfUnity) (P : PointSuborbifold c) :
    HasCobordismEff P P := by
  set q := c.out
  have hq : (⟦q⟧ : PolyfoldClass Z) = c := Quotient.out_eq c
  have hPUq := (c.definition_16_1_5_two).1 hPU q hq
  obtain ⟨hemp, hcpt0, hloc0⟩ := zero_data q
  refine ⟨q, hq, q.X, EpFunctor.id _, hPUq, q.X.X.proposition_7_4_10_of_isZhou q.isZhou, 0,
    fun _ => 0, q.X.X.isBranchedEpSubgroupoid_zero, hcpt0, q.X.X.isOrientation_zero, hloc0,
    fun ω => ?_⟩
  rw [sub_self]
  exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary (B := q.X) hemp _

end PointSuborbifold

end PolyfoldClass

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- An **oriented perturbed solution set of dimension `0`** of `f` (2021 p. 739, Fredholm index
`0`): a compact oriented branched suborbifold of dimension `0` of `Z` whose function is `λ ∘ f`
for an sc⁺-multisection `λ`. -/
structure PointOrientedPerturbation (s : ScSection c) : Type (u + 1) extends
    PointSuborbifold c.polyfold where
  /-- The sc⁺-multisection `λ`. -/
  t : ScPlusMultisection c
  isPerturbed : IsPerturbedSuborbifold s t toPointSuborbifold.θ.toBranched

/-- The perturbation is **admissible** in the sense of Theorem 16.6.6: `λ` is controlled by
`(n, U)` and `(f, λ)` is in general position. -/
def PointOrientedPerturbation.IsAdmissible {s : ScSection c} (P : PointOrientedPerturbation s)
    (n : Y → ℝ) (U : Set Z) : Prop :=
  P.t.IsControlledBy n U ∧ s.IsInGeneralPositionWith P.t

/-- **2021 Theorem 16.6.6, p. 739, for Fredholm index `0`, on the polyfold**, as a
proposition.  `IsInherited o P` is the condition that the orientation of `θ̂` is the one
inherited from the orientation `o` of `f`.  Under the text's hypotheses (`∂Z = ∅`, `f` with
compact solution set, `(n, U)` controlling compactness), a closed `0`-form `τ` on `Z` has the
same count `∫_θ̂ τ` and the same effective count `∮_θ̂ τ` for any two admissible perturbations
with the inherited orientation. -/
def theorem_16_6_6_index_zero_polyfold_statement (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) (IsInherited : OrientationRep s → PointOrientedPerturbation s.1 → Prop) : Prop :=
  c.polyfold.boundary = ∅ → s.1.HasCompactSolutionSet → c.IsAuxNorm n → IsOpen U →
    s.1.ControlsCompactness n U → ∀ o : OrientationRep s,
    ∀ P₀ P₁ : PointOrientedPerturbation s.1, P₀.IsAdmissible n U → IsInherited o P₀ →
      P₁.IsAdmissible n U → IsInherited o P₁ →
      ∀ τ : ScForm c.polyfold 0, ScForm.d τ = 0 →
        P₀.count τ = P₁.count τ ∧ P₀.countEff τ = P₁.countEff τ

/-- **2021 Theorem 16.6.6 for index `0` on the polyfold, from the cobordisms**: for every
predicate `IsInherited`, the statement holds when any two admissible perturbations with the
inherited orientation are joined by oriented compact cobordisms of dimension `1`. -/
theorem theorem_16_6_6_index_zero_polyfold_hyp (s : FredholmSection c) (n : Y → ℝ) (U : Set Z)
    (IsInherited : OrientationRep s → PointOrientedPerturbation s.1 → Prop)
    (hcob : ∀ o P₀ P₁, P₀.IsAdmissible n U → IsInherited o P₀ → P₁.IsAdmissible n U →
      IsInherited o P₁ →
      P₀.toPointSuborbifold.HasCobordism P₁.toPointSuborbifold ∧
        P₀.toPointSuborbifold.HasCobordismEff P₁.toPointSuborbifold) :
    theorem_16_6_6_index_zero_polyfold_statement s n U IsInherited := by
  intro _ _ _ _ _ o P₀ P₁ h₀ i₀ h₁ i₁ τ hτ
  obtain ⟨h, he⟩ := hcob o P₀ P₁ h₀ i₀ h₁ i₁
  exact ⟨PointSuborbifold.count_eq_of_hasCobordism h τ hτ,
    PointSuborbifold.countEff_eq_of_hasCobordismEff he τ hτ⟩

/-! ### From the models -/

section Models

variable (a : SectionRep c) (P : PointPerturbation a.S.A a.F)

/-- **The compact oriented branched suborbifold `θ̂ = [(Λ ∘ F, T̂), (X, γ)]` of dimension `0`**
of a regular perturbation of dimension `0` in the model of `a`. -/
def pointSuborbifold : PointSuborbifold c.polyfold where
  θ := ⟦pointOrientedRep a P⟧
  isCompact := ⟨(pointOrientedRep a P).toBranchedRep, rfl, P.isCompact⟩
  isTame := ⟨pointOrientedRep a P, rfl,
    ((pointOrientedRep a P).isPointTame_iff_isTameOriented).1 (isPointTame_pointOrientedRep a P)⟩

/-- **The sc⁺-multisection `λ = [Λ]`** of `p` (Definition 16.5.2). -/
def pointMultisection : ScPlusMultisection c :=
  ⟦ofFunctor a.S a.hS P.Λ P.isRegular.2.1.1⟧

/-- **The oriented perturbed solution set `λ ∘ f` of dimension `0` on the polyfold** (2021
p. 739): the function of `θ̂` is `λ ∘ f`. -/
def toPointOrientedPerturbation {s : ScSection c} (ha : ⟦a⟧ = s) :
    PointOrientedPerturbation s where
  toPointSuborbifold := pointSuborbifold a P
  t := pointMultisection a P
  isPerturbed :=
    (perturbedRep_toFun_ofFunctor a P.Λ P.isRegular.2.1.1 P.isBranched).trans
      (by rw [ha]; rfl)

/-- **The count on the polyfold is the count in the model**: `∫_θ̂ τ = ∫_{(Λ ∘ F, T̂)} ω` for the
representative `ω` of `τ` in the model. -/
theorem count_pointSuborbifold (τ : ScForm c.polyfold 0) :
    (pointSuborbifold a P).count τ =
      P.count (ScForm.toStructure a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) τ) :=
  ((pointSuborbifold a P).θ.pointIntegralOfTame_eq _ _ τ _ rfl).trans
    (count_eq_pointIntegral a P τ).symm

/-- **The effective count on the polyfold is the effective count in the model.** -/
theorem countEff_pointSuborbifold (τ : ScForm c.polyfold 0) :
    (pointSuborbifold a P).countEff τ =
      P.countEff (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou)
        (ScForm.toStructure a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) τ) :=
  ((pointSuborbifold a P).θ.pointIntegralEffOfTame_eq _ _ τ _ rfl).trans
    (countEff_eq_pointIntegralEff a P τ).symm

variable {a}

/-- **A cobordism in the model is a cobordism on the polyfold.** -/
theorem hasCobordism_pointSuborbifold {P₀ P₁ : PointPerturbation a.S.A a.F}
    (h : P₀.HasOrientedCobordism P₁) :
    (pointSuborbifold a P₀).HasCobordism (pointSuborbifold a P₁) := by
  obtain ⟨Y', F, hPUY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  refine ⟨a.S.toPolyfoldStructure, toPolyfoldStructure_mem a.hS, Y', F, hPUY, Θ', T', hΘ', hcpt',
    hT', hloc', fun ω => ?_⟩
  rw [count_pointSuborbifold, count_pointSuborbifold]
  convert hbd ω using 3 <;> first | rfl | (congr 1; exact ScForm.toStructure_mk _ _ ω)

/-- **An effective cobordism in the model is one on the polyfold.** -/
theorem hasCobordismEff_pointSuborbifold {P₀ P₁ : PointPerturbation a.S.A a.F}
    (h : P₀.HasOrientedCobordismEff (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou) P₁) :
    (pointSuborbifold a P₀).HasCobordismEff (pointSuborbifold a P₁) := by
  obtain ⟨Y', F, hPUY, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  refine ⟨a.S.toPolyfoldStructure, toPolyfoldStructure_mem a.hS, Y', F, hPUY, hLUCY, Θ', T', hΘ',
    hcpt', hT', hloc', fun ω => ?_⟩
  rw [countEff_pointSuborbifold, countEff_pointSuborbifold]
  convert hbd ω using 3 <;> first | rfl | (congr 1; exact ScForm.toStructure_mk _ _ ω)

end Models

/-- **`θ̂` of dimension `0` has the orientation inherited from `(f, o)`**, read in the model of
`o`: `Q` is the class of a regular perturbation of dimension `0` of the representative `F` that
carries `o`, whose orientation is singled out by `Can o` (the canonical orientation of
Definition 15.4.2). -/
def IsInheritedFromPoint {s : FredholmSection c}
    (Can : ∀ o : OrientationRep s, PointPerturbation o.a.S.A o.a.F → Prop)
    (o : OrientationRep s) (Q : PointOrientedPerturbation s.1) : Prop :=
  ∃ P : PointPerturbation o.a.S.A o.a.F, Can o P ∧ toPointOrientedPerturbation o.a P o.ha = Q

/-- **The model form of Theorem 16.6.6 for index `0` gives the polyfold form**: if the counts
in the model of every orientation agree (`theorem_16_6_6_index_zero_statement`), so do the
counts `∫_θ̂ τ`, `∮_θ̂ τ` on the polyfold over the perturbations with the inherited orientation
(`count_pointSuborbifold`). -/
theorem theorem_16_6_6_index_zero_polyfold_of_model_statement (s : FredholmSection c)
    (n : Y → ℝ) (U : Set Z)
    (Can : ∀ o : OrientationRep s, PointPerturbation o.a.S.A o.a.F → Prop)
    (h : theorem_16_6_6_index_zero_statement s n U Can) :
    theorem_16_6_6_index_zero_polyfold_statement s n U (IsInheritedFromPoint Can) := by
  rintro hbd hcs hn hU hcc o P₀ P₁ - ⟨M₀, c₀, rfl⟩ - ⟨M₁, c₁, rfl⟩ τ hτ
  obtain ⟨e, e'⟩ := h hbd hcs hn hU hcc o M₀ M₁ c₀ c₁ τ hτ
  refine ⟨?_, ?_⟩
  · change (pointSuborbifold o.a M₀).count τ = (pointSuborbifold o.a M₁).count τ
    rw [count_pointSuborbifold, count_pointSuborbifold]
    exact e
  · change (pointSuborbifold o.a M₀).countEff τ = (pointSuborbifold o.a M₁).countEff τ
    rw [countEff_pointSuborbifold, countEff_pointSuborbifold]
    exact e'

/-- **2021 Theorem 16.6.6 for index `0` on the polyfold, from the cobordisms in the model of
the orientation**: the hypotheses of `theorem_16_6_6_index_zero_of_model` give the polyfold
statement for the orientation inherited in the model. -/
theorem theorem_16_6_6_index_zero_polyfold_of_model (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) (Can : ∀ o : OrientationRep s, PointPerturbation o.a.S.A o.a.F → Prop)
    (hcob : c.polyfold.boundary = ∅ → s.1.HasCompactSolutionSet → ∀ (o : OrientationRep s)
      (P₀ P₁ : PointPerturbation o.a.S.A o.a.F), Can o P₀ → Can o P₁ →
      P₀.HasOrientedCobordism P₁ ∧
        P₀.HasOrientedCobordismEff (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou) P₁) :
    theorem_16_6_6_index_zero_polyfold_statement s n U (IsInheritedFromPoint Can) := by
  rintro hbd hcs - - - o P₀ P₁ - ⟨M₀, c₀, rfl⟩ - ⟨M₁, c₁, rfl⟩ τ hτ
  obtain ⟨h, he⟩ := hcob hbd hcs o _ _ c₀ c₁
  exact ⟨PointSuborbifold.count_eq_of_hasCobordism (hasCobordism_pointSuborbifold h) τ hτ,
    PointSuborbifold.countEff_eq_of_hasCobordismEff (hasCobordismEff_pointSuborbifold he) τ hτ⟩

/-- **The cobordism hypotheses of `theorem_16_6_6_index_zero_polyfold_hyp` are satisfiable**:
for the predicate that singles out one perturbation they hold, when `Z` admits sc-smooth
partitions of unity. -/
theorem theorem_16_6_6_index_zero_polyfold_hcob_witness
    (hPU : c.polyfold.AdmitsScPartitionsOfUnity) {s : FredholmSection c}
    (P : PointOrientedPerturbation s.1) (n : Y → ℝ) (U : Set Z) :
    ∀ (o : OrientationRep s) (P₀ P₁ : PointOrientedPerturbation s.1), P₀.IsAdmissible n U →
      (fun _ Q => Q = P) o P₀ → P₁.IsAdmissible n U → (fun _ Q => Q = P) o P₁ →
      P₀.toPointSuborbifold.HasCobordism P₁.toPointSuborbifold ∧
        P₀.toPointSuborbifold.HasCobordismEff P₁.toPointSuborbifold := by
  rintro o P₀ P₁ - rfl - rfl
  exact ⟨PointSuborbifold.hasCobordism_refl hPU _, PointSuborbifold.hasCobordismEff_refl hPU _⟩

end StrongPolyfoldBundle

end Polyfold
