import Polyfold.Chapter16.PerturbedIntegralIndependence
import Polyfold.Chapter15.CylinderCobordism

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.6, p. 739: **Theorem 16.6.6** (2017: Theorem 16.8), read in the model of the orientation.
Numbers and pages are the 2021 text's.

## The text, paraphrased

(Definition 16.6.5) An orientation of an sc-Fredholm section `f` of `p : Y → Z` is an orientation
of a representative `(W, F)`.  (p. 739) For a generic `λ`, `θ = λ ∘ f` is a branched suborbifold
of `Z`, and if `f` is oriented `θ` has a natural orientation (Theorem 15.4.1, Definition 15.4.2).
(Theorem 16.6.6) For `∂Z = ∅`, `f` oriented with compact solution set and `(n, U)` controlling
compactness, the integrals `∫_θ̂ τ`, `∮_θ̂ τ` of closed forms do not depend on `λ` and depend only
on `[τ]`.

## What is formalized

The orientation `o` of `f` lives on a representative `(W, F)` (`OrientationRep.a`).  The oriented
perturbed solution sets of §15.4 in that model (`SBLocalization.OrientedRegularPerturbation`) are
carried to the polyfold, and Theorem 16.6.6 is deduced from Corollary 15.4.4's cobordism in the
model.

* `PolyfoldClass.CompactOrientedSuborbifold.integralEff_mk_rep`: in every model the polyfold
  integral `∮_θ̂` is the effective ep-groupoid integral of Definition 9.5.6 (2).
* `StrongPolyfoldBundle.ModelPerturbation a m`: an oriented regular perturbation `(N, U, Λ, T̂)`
  of the representative `F` of the model `a`, with `T̂ = 0` off `X_∞` (the convention of
  Definition 16.4.4's representatives).
* `ModelPerturbation.orientedRep`, `toCompact`, `multisection`, `toOrientedPerturbation`: the
  oriented branched suborbifold `[(Λ ∘ F, T̂), (X, γ)]` of `Z`, the sc⁺-multisection `λ = [Λ]`,
  and the oriented perturbed solution set `λ ∘ f` (`OrientedPerturbation`).  The independence of
  the tangent sums needed for Definition 16.4.4 is Theorem 9.2.1 (1).
* **`ModelPerturbation.integral_toCompact`**, **`integralEff_toCompact`**:
  `∫_θ̂ [(ω, (X, γ))] = ∫_{(Λ ∘ F, T̂)} ω` and the same for `∮`.
* **`ModelPerturbation.hasCobordism`**, **`hasCobordismEff`**: an oriented compact cobordism in
  the model (`HasOrientedCobordism`, the proof of Corollary 15.4.4) is one on the polyfold
  (`HasCobordism`).
* `IsInheritedFrom Can o Q`: `Q` is the class of a model perturbation in the model of `o` whose
  orientation is the one singled out by `Can o` (the canonical orientation `T̂_((F, o), Λ)` of
  Definition 15.4.2).
* **`theorem_16_6_6_of_model`**: Theorem 16.6.6 for `IsInheritedFrom Can`, when `Z` admits
  sc-smooth partitions of unity and any two `Can o`-perturbations of the model are joined by
  oriented compact cobordisms there.
* `CylinderInput Can o` and **`theorem_16_6_6_of_cylinder`**: Theorem 16.6.6 along the text's
  argument (Corollary 15.3.10 (3) and Corollary 15.4.4 on `[0, 1] × X`), from the inputs of the
  cylinder construction in the model of each orientation.

## Reading

* "The orientation inherited from `f`" is read in the model `(W, F)` that carries the
  orientation `o` (Definition 16.6.5): `θ̂` is represented there by `(Λ ∘ F, T̂)` with `T̂` the
  orientation `Can o` singles out.  The perturbations compared are the structurable regular
  perturbations of that model (Corollary 15.3.10), as in Corollary 15.4.4.
* That the class of perturbations does not depend on the model of `o` (transport of `o` and of
  `T̂` along generalized strong bundle isomorphisms) is not part of this file.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter CategoryTheory MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization EPLocalization.EPLoc EpGroupoid MPolyfold

namespace PolyfoldClass.CompactOrientedSuborbifold

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z} {m : ℕ}

/-- **The effective polyfold integral is the effective ep-groupoid integral in every model**
(2021 p. 732): `∮_θ̂ [(ω, (X, α))] = ∮_{(Θ, T̂)} ω` (Definition 9.5.6 (2)). -/
theorem integralEff_mk_rep (P : CompactOrientedSuborbifold c m) (a : OrientedRep c)
    (ha : ⟦a⟧ = P.θ) (ω : a.p.X.epFormsInfty (m + 1)) :
    P.integralEff (ScForm.mk a.p a.mem ω) =
      (a.p.X.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m)
        a.A.isBranchedEpSubgroupoid (OrientedSuborbifold.isCompactBranched_of_mk P.isCompact a ha)
        a.A.isOrientation
        (a.p.X.hloc_hasLUC (a.p.X.X.proposition_7_4_10_of_isZhou a.p.isZhou)
          ((OrientedSuborbifold.isTameOriented_iff P.θ).1 P.isTame a ha)) ω := by
  rw [integralEff, OrientedSuborbifold.integralEff_eq P.θ _ P.isCompact P.isTame _ a ha,
    OrientedRep.integralEff, ScForm.toStructure_mk]

end PolyfoldClass.CompactOrientedSuborbifold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {T T' : Obj → X.PObj.OrTangent →₀ ℚ}

open scoped Classical in
variable (X) in
/-- **The section `T̂` cut off outside `X_∞`**: `T̂` on the smooth points, `0` elsewhere.  An
orientation is only read on `X_∞` (Definition 9.3.2). -/
def smoothPart (T : Obj → X.PObj.OrTangent →₀ ℚ) : Obj → X.PObj.OrTangent →₀ ℚ :=
  fun x => if x ∈ X.PObj.smoothSet then T x else 0

theorem smoothPart_of_mem {x : Obj} (hx : x ∈ X.PObj.smoothSet) : X.smoothPart T x = T x :=
  if_pos hx

theorem smoothPart_of_notMem {x : Obj} (hx : x ∉ X.PObj.smoothSet) : X.smoothPart T x = 0 :=
  if_neg hx

/-- **The cut-off of an orientation is an orientation** (Definition 9.3.2 reads `T̂` on `X_∞`). -/
theorem IsOrientation.smoothPart (hT : X.IsOrientation Θ T) :
    X.IsOrientation Θ (X.smoothPart T) where
  mem x hx := by rw [smoothPart_of_mem hx]; exact hT.mem x hx
  natural φ hφ := by
    rw [smoothPart_of_mem hφ, smoothPart_of_mem (tgt_mem_smoothSet_of_src hφ)]
    exact hT.natural φ hφ
  lifts x hx := by rw [smoothPart_of_mem hx]; exact hT.lifts x hx
  locallyOriented x hx := by
    obtain ⟨B, hB⟩ := hT.locallyOriented x hx
    exact ⟨B, fun y hy hys => by rw [smoothPart_of_mem hys]; exact hB y hy hys⟩

/-- A structure describing `T̂` describes every section that agrees with `T̂` on `X_∞`. -/
theorem OrientedTameStructure.represents_congr {n : ℕ} {x : Obj}
    (C : X.OrientedTameStructure n Θ x) (h : ∀ y ∈ X.PObj.smoothSet, T y = T' y)
    (hC : C.Represents T) : C.Represents T' :=
  fun y hy hys => (h y hys).symm.trans (hC y hy hys)

section Measure

variable {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
  (𝓘 : X.SheetIntegration G Ω) {n : ℕ}

/-- **The measure `μ_ω^Θ̂` of Theorem 9.5.4 depends on `T̂` only through its values on `X_∞`.** -/
theorem branchedMeasure_congr_orientation (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T) (hT' : X.IsOrientation Θ T')
    (h : ∀ y ∈ X.PObj.smoothSet, T y = T' y)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T)
    (hcov' : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T') :
    branchedMeasure 𝓘 hΘ hcpt hT hcov = branchedMeasure 𝓘 hΘ hcpt hT' hcov' :=
  (theorem_9_5_4 𝓘 hΘ hcpt hT' hcov').unique
    (fun ω _ C hC _ hK hKU => branchedMeasure_apply 𝓘 hΘ hcpt hT hcov ω C hC.1
      (C.represents_congr (fun y hy => (h y hy).symm) hC.2) hK hKU)
    (fun ω _ C hC _ hK hKU => branchedMeasure_apply 𝓘 hΘ hcpt hT' hcov' ω C hC.1 hC.2 hK hKU)

/-- **The effective measure of Theorem 9.5.5 depends on `T̂` only through its values on `X_∞`.** -/
theorem branchedMeasureEff_congr_orientation (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T) (hT' : X.IsOrientation Θ T')
    (h : ∀ y ∈ X.PObj.smoothSet, T y = T' y)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T ∧ C.rep.HasLUC)
    (hcov' : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T' ∧ C.rep.HasLUC) :
    branchedMeasureEff 𝓘 hΘ hcpt hT hcov = branchedMeasureEff 𝓘 hΘ hcpt hT' hcov' :=
  (theorem_9_5_5 𝓘 hΘ hcpt hT' hcov').unique
    (fun ω _ C hC _ hK hKU => branchedMeasureEff_apply 𝓘 hΘ hcpt hT hcov ω C hC.1
      (C.represents_congr (fun y hy => (h y hy).symm) hC.2.1) hC.2.2 hK hKU)
    (fun ω _ C hC _ hK hKU =>
      branchedMeasureEff_apply 𝓘 hΘ hcpt hT' hcov' ω C hC.1 hC.2.1 hC.2.2 hK hKU)

end Measure

end EpGroupoid

namespace EP

variable (B : EP.{u}) {Θ : B.Obj → ℚ} {T T' : B.Obj → B.X.PObj.OrTangent →₀ ℚ} {n : ℕ}

/-- **`∫_Θ̂ ω` depends on `T̂` only through its values on `X_∞`** (Definition 9.5.6 (1)). -/
theorem tameBranchedIntegral_congr_orientation (hn : 0 < n)
    (hΘ : B.X.IsBranchedEpSubgroupoid Θ) (hcpt : B.X.IsCompactBranched Θ)
    (hT : B.X.IsOrientation Θ T) (hT' : B.X.IsOrientation Θ T')
    (h : ∀ y ∈ B.X.PObj.smoothSet, T y = T' y)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : B.X.OrientedTameStructure n Θ x, C.Represents T)
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : B.X.OrientedTameStructure n Θ x, C.Represents T')
    (ω : B.epFormsInfty n) :
    (B.epFormsInftyEval n).tameBranchedIntegral hn hΘ hcpt hT hloc ω =
      (B.epFormsInftyEval n).tameBranchedIntegral hn hΘ hcpt hT' hloc' ω := by
  simp only [FormEval.tameBranchedIntegral, FormEval.concreteBranchedIntegral, branchedIntegral]
  rw [branchedMeasure_congr_orientation _ hΘ hcpt hT hT' h]

/-- **`∮_Θ̂ ω` depends on `T̂` only through its values on `X_∞`** (Definition 9.5.6 (2)). -/
theorem tameBranchedIntegralEff_congr_orientation (hn : 0 < n)
    (hΘ : B.X.IsBranchedEpSubgroupoid Θ) (hcpt : B.X.IsCompactBranched Θ)
    (hT : B.X.IsOrientation Θ T) (hT' : B.X.IsOrientation Θ T')
    (h : ∀ y ∈ B.X.PObj.smoothSet, T y = T' y)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : B.X.OrientedTameStructure n Θ x,
      C.Represents T ∧ C.rep.HasLUC)
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : B.X.OrientedTameStructure n Θ x,
      C.Represents T' ∧ C.rep.HasLUC)
    (ω : B.epFormsInfty n) :
    (B.epFormsInftyEval n).tameBranchedIntegralEff hn hΘ hcpt hT hloc ω =
      (B.epFormsInftyEval n).tameBranchedIntegralEff hn hΘ hcpt hT' hloc' ω := by
  simp only [FormEval.tameBranchedIntegralEff, FormEval.concreteBranchedIntegralEff,
    branchedIntegralEff]
  rw [branchedMeasureEff_congr_orientation _ hΘ hcpt hT hT' h]

end EP

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization SEP

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- An **oriented regular perturbation in the model `a`** (Corollary 15.3.10, Definition 15.4.2,
for the representative `(W, F)` of `f`): `(N, U, Λ)` with `Θ = Λ ∘ F` compact and branched and an
orientation `T̂` of `Θ` described by oriented tame structures of dimension `m + 1`, with `T̂ = 0`
off `X_∞` (the convention for the representatives of Definition 16.4.4). -/
structure ModelPerturbation (a : SectionRep c) (m : ℕ) extends
    OrientedRegularPerturbation a.S.A a.F m where
  smooth : ∀ x, x ∉ a.S.A.X.PObj.smoothSet → T x = 0

namespace ModelPerturbation

variable {a : SectionRep c} {m : ℕ} (M : ModelPerturbation a m)

/-- `Λ` is an sc⁺-multisection functor (it is structurable). -/
theorem isScPlusMultisection : IsScPlusMultisection a.S.A M.Λ := M.isRegular.2.1.1

/-- **The representative `((Λ ∘ F, T̂), (X, γ))`** of an oriented branched suborbifold of `Z`
(Definition 16.4.4).  The tangent sums of `Λ ∘ F` do not depend on the local branching structure
by Theorem 9.2.1 (1). -/
def orientedRep : OrientedRep c.polyfold where
  p := a.S.toPolyfoldStructure
  mem := toPolyfoldStructure_mem a.hS
  A := ⟨fun z => (M.Λ (a.F z) : ℚ), M.T, M.isBranched,
    EpGroupoid.hasIndependentTangentSums _, M.isOrientation⟩
  smooth := M.smooth

/-- **The tame compact oriented branched suborbifold `θ̂ = [(Λ ∘ F, T̂), (X, γ)]`** of `Z`. -/
def toCompact : CompactOrientedSuborbifold c.polyfold m where
  θ := ⟦M.orientedRep⟧
  isCompact := ⟨M.orientedRep.toBranchedRep, rfl, M.isCompact⟩
  isTame := ⟨M.orientedRep, rfl, M.loc⟩

/-- **The sc⁺-multisection `λ = [Λ]`** of `p` (Definition 16.5.2). -/
def multisection : ScPlusMultisection c :=
  ⟦ofFunctor a.S a.hS M.Λ M.isScPlusMultisection⟧

/-- **The oriented perturbed solution set `λ ∘ f` on the polyfold** (2021 p. 739): the function
of `θ̂` is `λ ∘ f`. -/
def toOrientedPerturbation {s : ScSection c} (ha : ⟦a⟧ = s) : OrientedPerturbation s m where
  toCompactOrientedSuborbifold := M.toCompact
  t := M.multisection
  isPerturbed :=
    (perturbedRep_toFun_ofFunctor a M.Λ M.isScPlusMultisection M.isBranched).trans (by rw [ha]; rfl)

@[simp] theorem toOrientedPerturbation_t {s : ScSection c} (ha : ⟦a⟧ = s) :
    (M.toOrientedPerturbation ha).t = M.multisection := rfl

/-- **`∫_θ̂ [(ω, (X, γ))] = ∫_{(Λ ∘ F, T̂)} ω`**: the polyfold integral over the class of a model
perturbation is the ep-groupoid integral of §15.4 in the model. -/
theorem integral_toCompact (ω : a.S.A.baseEP.epFormsInfty (m + 1)) :
    M.toCompact.integral (ScForm.mk a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) ω) =
      M.toOrientedRegularPerturbation.integral ω :=
  M.toCompact.integral_mk_rep M.orientedRep rfl ω

/-- **`∮_θ̂ [(ω, (X, γ))] = ∮_{(Λ ∘ F, T̂)} ω`**; (ZHOU) gives the local unique continuation
property in the model (Proposition 7.4.10). -/
theorem integralEff_toCompact (ω : a.S.A.baseEP.epFormsInfty (m + 1)) :
    M.toCompact.integralEff
        (ScForm.mk a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) ω) =
      M.toOrientedRegularPerturbation.integralEff
        (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou) ω :=
  M.toCompact.integralEff_mk_rep M.orientedRep rfl ω

/-- **A cobordism in the model is a cobordism on the polyfold** (the proof of Corollary 15.4.4
read for Theorem 16.6.6). -/
theorem hasCobordism (M₀ M₁ : ModelPerturbation a m)
    (h : M₀.toOrientedRegularPerturbation.HasOrientedCobordism
      M₁.toOrientedRegularPerturbation) :
    M₀.toCompact.HasCobordism M₁.toCompact := by
  obtain ⟨Y', F, hPUY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  refine ⟨a.S.toPolyfoldStructure, toPolyfoldStructure_mem a.hS, Y', F, hPUY, Θ', T', hΘ', hcpt',
    hT', hloc', fun ω => ?_⟩
  exact (hbd ω).trans
    (congrArg₂ (· - ·) (M₁.integral_toCompact ω).symm (M₀.integral_toCompact ω).symm)

/-- **An effective cobordism in the model is one on the polyfold.** -/
theorem hasCobordismEff (M₀ M₁ : ModelPerturbation a m)
    (h : M₀.toOrientedRegularPerturbation.HasOrientedCobordismEff
      (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou) M₁.toOrientedRegularPerturbation) :
    M₀.toCompact.HasCobordismEff M₁.toCompact := by
  obtain ⟨Y', F, hPUY, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  refine ⟨a.S.toPolyfoldStructure, toPolyfoldStructure_mem a.hS, Y', F, hPUY, hLUCY, Θ', T', hΘ',
    hcpt', hT', hloc', fun ω => ?_⟩
  exact (hbd ω).trans
    (congrArg₂ (· - ·) (M₁.integralEff_toCompact ω).symm (M₀.integralEff_toCompact ω).symm)

/-- **Every oriented regular perturbation of the model gives a model perturbation**: replace
`T̂` by its cut-off outside `X_∞`. -/
def ofRegular (P : OrientedRegularPerturbation a.S.A a.F m) : ModelPerturbation a m where
  N := P.N
  U := P.U
  Λ := P.Λ
  isRegular := P.isRegular
  T := a.S.A.X.smoothPart P.T
  isBranched := P.isBranched
  isCompact := P.isCompact
  isOrientation := P.isOrientation.smoothPart
  loc := fun x hx => (P.loc x hx).imp fun C hC =>
    C.represents_congr (fun _ hy => (smoothPart_of_mem hy).symm) hC
  smooth := fun _ hx => smoothPart_of_notMem hx

/-- The cut-off does not change the integral `∫_{(Λ ∘ F, T̂)} ω`. -/
theorem integral_ofRegular (P : OrientedRegularPerturbation a.S.A a.F m)
    (ω : a.S.A.baseEP.epFormsInfty (m + 1)) :
    (ofRegular P).toOrientedRegularPerturbation.integral ω = P.integral ω :=
  a.S.A.baseEP.tameBranchedIntegral_congr_orientation (Nat.succ_pos m) P.isBranched P.isCompact
    P.isOrientation.smoothPart P.isOrientation (fun _ hy => smoothPart_of_mem hy) _ P.loc ω

/-- The cut-off does not change the effective integral `∮_{(Λ ∘ F, T̂)} ω`. -/
theorem integralEff_ofRegular (hLUC : a.S.A.X.IsLUC)
    (P : OrientedRegularPerturbation a.S.A a.F m) (ω : a.S.A.baseEP.epFormsInfty (m + 1)) :
    (ofRegular P).toOrientedRegularPerturbation.integralEff hLUC ω = P.integralEff hLUC ω :=
  a.S.A.baseEP.tameBranchedIntegralEff_congr_orientation (Nat.succ_pos m) P.isBranched
    P.isCompact P.isOrientation.smoothPart P.isOrientation (fun _ hy => smoothPart_of_mem hy) _
    _ ω

/-- **A cobordism between regular perturbations of the model is a cobordism on the polyfold**
between their classes. -/
theorem hasCobordism_ofRegular {P₀ P₁ : OrientedRegularPerturbation a.S.A a.F m}
    (h : P₀.HasOrientedCobordism P₁) :
    (ofRegular P₀).toCompact.HasCobordism (ofRegular P₁).toCompact := by
  refine hasCobordism _ _ ?_
  obtain ⟨Y', F, hPUY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  refine ⟨Y', F, hPUY, Θ', T', hΘ', hcpt', hT', hloc', fun ω => ?_⟩
  rw [integral_ofRegular, integral_ofRegular]
  exact hbd ω

/-- The effective form of `hasCobordism_ofRegular`. -/
theorem hasCobordismEff_ofRegular {P₀ P₁ : OrientedRegularPerturbation a.S.A a.F m}
    (h : P₀.HasOrientedCobordismEff (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou) P₁) :
    (ofRegular P₀).toCompact.HasCobordismEff (ofRegular P₁).toCompact := by
  refine hasCobordismEff _ _ ?_
  obtain ⟨Y', F, hPUY, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  refine ⟨Y', F, hPUY, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', fun ω => ?_⟩
  rw [integralEff_ofRegular, integralEff_ofRegular]
  exact hbd ω

end ModelPerturbation

/-! ### Theorem 16.6.6 in the model of the orientation -/

/-- **`θ̂` has the orientation inherited from `(f, o)`** (2021 p. 739), read in the model of `o`:
`Q` is the class of an oriented regular perturbation `(N, U, Λ, T̂)` of the representative `F`
that carries `o`, whose orientation `T̂` is the one singled out by `Can o` (the canonical
orientation of Definition 15.4.2). -/
def IsInheritedFrom {s : FredholmSection c} {m : ℕ}
    (Can : ∀ o : OrientationRep s, OrientedRegularPerturbation o.a.S.A o.a.F m → Prop)
    (o : OrientationRep s) (Q : OrientedPerturbation s.1 m) : Prop :=
  ∃ P : OrientedRegularPerturbation o.a.S.A o.a.F m,
    Can o P ∧ (ModelPerturbation.ofRegular P).toOrientedPerturbation o.ha = Q

/-- **2021 Theorem 16.6.6 from the cobordisms in the model of the orientation** (p. 739; 2017:
Theorem 16.8).  If `Z` admits sc-smooth partitions of unity and, for `∂Z = ∅` and `f` with compact
solution set, any two perturbations of the model of `o` with the orientation `Can o` are joined
by oriented compact cobordisms in that model (Corollary 15.4.4's proof), then the statement of
Theorem 16.6.6 holds for the orientation inherited in the model. -/
theorem theorem_16_6_6_of_model (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) (m : ℕ)
    (Can : ∀ o : OrientationRep s, OrientedRegularPerturbation o.a.S.A o.a.F m → Prop)
    (hcob : c.polyfold.boundary = ∅ → s.1.HasCompactSolutionSet → ∀ (o : OrientationRep s)
      (P₀ P₁ : OrientedRegularPerturbation o.a.S.A o.a.F m), Can o P₀ → Can o P₁ →
      P₀.HasOrientedCobordism P₁ ∧
        P₀.HasOrientedCobordismEff (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou) P₁) :
    theorem_16_6_6_statement s n U m (IsInheritedFrom Can) := by
  intro hbd hcs _ _ _ o
  refine ⟨fun P _ _ τ η => ⟨?_, ?_⟩, ?_⟩
  · exact OrientedSuborbifold.integral_add_d hbd hPU _ _ _ τ η
  · exact OrientedSuborbifold.integralEff_add_d hbd hPU _ _ _ τ η
  rintro P₀ P₁ - ⟨M₀, c₀, rfl⟩ - ⟨M₁, c₁, rfl⟩ τ hτ
  obtain ⟨h, he⟩ := hcob hbd hcs o _ _ c₀ c₁
  exact ⟨CompactOrientedSuborbifold.integral_eq_of_hasCobordism
      (ModelPerturbation.hasCobordism_ofRegular h) τ hτ,
    CompactOrientedSuborbifold.integralEff_eq_of_hasCobordismEff
      (ModelPerturbation.hasCobordismEff_ofRegular he) τ hτ⟩

/-- **The inputs of the cylinder construction in the model of `o`** (proofs of Corollaries
15.3.10 (3) and 15.4.4 on `[0, 1] × X`): the relative general position step on the cylinder
(`rel`), sc-smooth partitions of unity on its object M-polyfold (`pu`), the local unique
continuation property there (`luc`), tame germ data of `F` (`tame`), and for any two
perturbations with the orientation `Can o`: the glued boundary data are structurable and satisfy
the face condition (`glue`), and the perturbation on the cylinder carries an orientation with
the end identities (`orient`, `orientEff`). -/
structure CylinderInput {s : FredholmSection c} {m : ℕ}
    (Can : ∀ o : OrientationRep s, OrientedRegularPerturbation o.a.S.A o.a.F m → Prop)
    (o : OrientationRep s) : Prop where
  rel : theorem_15_3_7_relative_statement (o.a.S.A.cubeSEP 1)
  pu : (o.a.S.A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity
  luc : (o.a.S.A.cubeSEP 1).X.IsLUC
  tame : o.a.S.A.B.IsScFredholmSectionTame o.a.F
  glue : ∀ P₀ P₁ : OrientedRegularPerturbation o.a.S.A o.a.F m, Can o P₀ → Can o P₁ →
    IsBoundaryStructurable (o.a.S.A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
      IsBoundaryFaceOnto (cubeLiftEp (n := 1) o.a.F o.hF.1.1.1) (cubeGlue P₀.Λ P₁.Λ)
  orient : ∀ P₀ P₁ : OrientedRegularPerturbation o.a.S.A o.a.F m, Can o P₀ → Can o P₁ →
    CylinderOrientationStatement o.hF.1.1.1 P₀ P₁
  orientEff : ∀ P₀ P₁ : OrientedRegularPerturbation o.a.S.A o.a.F m, Can o P₀ → Can o P₁ →
    CylinderOrientationEffStatement o.hF.1.1.1
      (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou) luc P₀ P₁

/-- For `∂Z = ∅` every object of a model has degeneracy index `0`. -/
theorem degIndex_eq_zero_of_boundary_eq_empty (hbd : c.polyfold.boundary = ∅)
    {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c) (x : S.A.Obj) :
    S.A.X.PObj.degIndex x = 0 := by
  by_contra h
  have hx : x ∈ S.A.X.PObj.boundary := Nat.one_le_iff_ne_zero.2 h
  have := (mem_boundary_iff_obj hS x).2 hx
  rw [hbd] at this
  exact this

/-- **The cobordisms of Corollary 15.4.4 in the model of `o`**, from the inputs of the cylinder
construction: for `∂Z = ∅` and `f` with compact solution set, any two perturbations with the
orientation `Can o` are joined by an oriented compact cobordism and by an effective one. -/
theorem hasOrientedCobordism_of_cylinderInput (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet) {m : ℕ}
    {Can : ∀ o : OrientationRep s, OrientedRegularPerturbation o.a.S.A o.a.F m → Prop}
    {o : OrientationRep s} (H : CylinderInput Can o)
    (P₀ P₁ : OrientedRegularPerturbation o.a.S.A o.a.F m) (h₀ : Can o P₀) (h₁ : Can o P₁) :
    P₀.HasOrientedCobordism P₁ ∧
      P₀.HasOrientedCobordismEff (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou) P₁ := by
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hpara := o.a.S.paracompact
  have hS : o.a.S.A.E.HasCompactSolutionSetEp o.a.F := by
    rw [← o.a.hasCompactSolutionSet_iff, o.ha]; exact hcs
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) o.a.S.A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) o.a.S.A.X.PMor
  have hXC : (o.a.S.A.cubeSEP 1).X.IsTame :=
    o.a.S.A.X.isTame_cubeProd 1 (o.a.S.A.X.isTame_of_degIndex_eq_zero hd)
  have hBC := (o.a.S.A.cubeSEP 1).exists_isTameChart hXC
  have h159 := theorem_15_3_9_charged_hyp H.rel
  obtain ⟨Λ', hreg, e0, e1, hΘ', hcpt'⟩ := corollary_15_3_10_3_charged h159 hBC hd hpara H.pu
    o.hF H.tame hS P₀.isRegular P₁.isRegular (H.glue P₀ P₁ h₀ h₁).1 (H.glue P₀ P₁ h₀ h₁).2
  constructor
  · obtain ⟨T', hT', hloc', hends⟩ := H.orient P₀ P₁ h₀ h₁ Λ' hreg e0 e1 hΘ' hcpt'
    exact hasOrientedCobordism_of_cylinder hd (hasScPartitionsOfUnity_cyl hpara H.pu) hΘ' hcpt'
      hT' hloc' hends
  · obtain ⟨T', hT', hloc', hends⟩ := H.orientEff P₀ P₁ h₀ h₁ Λ' hreg e0 e1 hΘ' hcpt'
    exact hasOrientedCobordismEff_of_cylinder hd _ (hasScPartitionsOfUnity_cyl hpara H.pu) H.luc
      hΘ' hcpt' hT' hloc' hends

/-- **2021 Theorem 16.6.6 along the text's argument** (p. 739; 2017: Theorem 16.8): if `Z`
admits sc-smooth partitions of unity (Theorem 16.4.6's hypothesis) and the inputs of the cylinder
construction hold in the model of every orientation, then the integrals `∫_θ̂ τ`, `∮_θ̂ τ` over
`θ̂ = λ ∘ f` with the orientation inherited in the model depend only on `[τ]` and, for closed
`τ`, not on the perturbation. -/
theorem theorem_16_6_6_of_cylinder (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) (m : ℕ)
    (Can : ∀ o : OrientationRep s, OrientedRegularPerturbation o.a.S.A o.a.F m → Prop)
    (H : ∀ o : OrientationRep s, CylinderInput Can o) :
    theorem_16_6_6_statement s n U m (IsInheritedFrom Can) :=
  theorem_16_6_6_of_model hPU s n U m Can fun hbd hcs o P₀ P₁ h₀ h₁ =>
    hasOrientedCobordism_of_cylinderInput hbd hcs (H o) P₀ P₁ h₀ h₁

/-! ### The perturbations of the model and the text's hypotheses on `λ` -/

/-- **An admissible `λ` is a regular perturbation in the model** (Theorem 16.6.6's hypotheses on
`λ` against Corollary 15.3.10's): let `(n, U)` control compactness of `f`, `Λ` be a structurable
sc⁺-multisection functor on the model of `a` whose class `λ` is controlled by `(n, U)`, with
`N(Λ) < 1` and `(F, Λ)` in general position.  Then `(N, γπ⁻¹(U), Λ)` with `N` the model form of
`n` is a regular perturbation of `F` (Corollary 15.3.10 (1)). -/
theorem isRegularPerturbation_of_admissible (s : FredholmSection c) {n : Y → ℝ}
    (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U)
    (a : SectionRep c) (ha : ⟦a⟧ = s.1) (Λ : a.S.A.W → ℚ≥0) (hst : IsStructurable a.S.A Λ)
    (ht : ScPlusMultisection.IsControlledBy (c := c) ⟦ofFunctor a.S a.hS Λ hst.1⟧ n U)
    (hlt : ∀ x, pointwiseNorm (a.S.normOf n) Λ x < 1)
    (hgp : IsInGeneralPosition a.S.A a.F Λ) :
    IsRegularPerturbation a.S.A a.F (a.S.normOf n) (a.g ⁻¹' U) Λ := by
  have hFa := (s.1.isFredholm_iff.1 s.2) a ha
  have hcca := (a.controlsCompactness_iff hn hU).1 (by rw [ha]; exact hcc)
  refine ⟨hcca, hst, fun x hx => ?_, hlt, IsInGeneralPosition.isTransversal hFa hst.1 hgp⟩
  apply ht.2
  rw [← remark_16_5_3 (ofFunctor a.S a.hS Λ hst.1)]
  exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

/-- **The class of a model perturbation is controlled by `(n, U)`** when the perturbation is
controlled by the model forms of `n` and `U`: `N` is the model form of `n` and the controlling
neighbourhood lies in `γπ⁻¹(U)`. -/
theorem ModelPerturbation.isControlledBy {a : SectionRep c} {m : ℕ} (M : ModelPerturbation a m)
    {n : Y → ℝ} {U : Set Z} (hN : M.N = a.S.normOf n) (hsub : M.U ⊆ a.g ⁻¹' U) :
    M.multisection.IsControlledBy n U := by
  set b := ofFunctor a.S a.hS M.Λ M.isScPlusMultisection
  refine ⟨fun z => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := a.S.surjective_γπ z
    have h := normLam_eq a.hS n M.Λ b.lam x fun w _ => b.comm w
    change c.normLam n b.lam (a.S.γ (a.S.A.X.π x)) ≤ 1
    rw [h, ← hN]
    exact (M.isRegular.2.2.2.1 x).le
  · change ScPlusMultisection.domSupp (c := c) ⟦b⟧ ⊆ U
    rw [← remark_16_5_3 b]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hsub (M.isRegular.2.2.1 hx)

/-- **The cobordism hypotheses of `theorem_16_6_6_of_model` are satisfiable**: for the predicate
that singles out one perturbation of the model they hold, when `Z` admits sc-smooth partitions
of unity (every perturbation is cobordant to itself). -/
theorem theorem_16_6_6_of_model_hcob_witness (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    {s : FredholmSection c} {m : ℕ} (o : OrientationRep s)
    (P : OrientedRegularPerturbation o.a.S.A o.a.F m) :
    P.HasOrientedCobordism P ∧
      P.HasOrientedCobordismEff (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou) P := by
  have hPUq := (c.polyfold.definition_16_1_5_two).1 hPU o.a.S.toPolyfoldStructure
    (toPolyfoldStructure_mem o.a.hS)
  exact ⟨OrientedRegularPerturbation.hasOrientedCobordism_refl hPUq P,
    OrientedRegularPerturbation.hasOrientedCobordismEff_refl hPUq _ P⟩

end StrongPolyfoldBundle

end Polyfold
