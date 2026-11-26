import GWMemoir.Bundle
import GWMemoir.CauchyRiemann
import GWMemoir.FredholmGerm
import Polyfold.Chapter16.FibreZero
import Polyfold.Chapter16.NormLamContinuous

/-!
Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I: The Polyfolds of Gromov–Witten
Theory*, Memoirs AMS 248 (2017), §4.1 (pp. 101–104): **the Cauchy–Riemann section on the
bundle model**, compared with the book (*Polyfold and Fredholm Theory*, Springer 2021):
Definitions 8.3.4, 16.3.18, 16.6.1, 17.7.4.

## The memoir, paraphrased

(p. 101) The section `∂̄_J` of `p : W → Z` is induced from a section functor `F` of the model
bundle `P : E → X`: on objects `F(α) = (α, ∂̄_J(α))`; the pair `(f, F)` is the nonlinear
Cauchy–Riemann section.  (Proposition 4.7) `∂̄_J` is sc-smooth and regularizing.

## What is formalized (namespace `GWMemoir`)

* For a structure `S` of a strong polyfold bundle and a section functor `F` of `S`
  (Definition 8.3.4): the section `f(γ|x|) = Γ|F(x)|` of `p` (`sectionOfFunctor`, well defined
  by functoriality), continuous and a section of `p`, hence a representative
  `sectionRepOfFunctor` (Definition 16.3.18) and, for an sc-Fredholm section functor, an
  sc-Fredholm section `fredholmSectionOfFunctor` (Definition 16.6.1).  Its solution set is
  `γ|{x | F(x) = 0_x}|` (`solutionSet_fredholmSectionOfFunctor`).
* For a strong polyfold bundle construction `Q` (Definition 17.7.4) and a natural section
  `σ(α) ∈ μ(α)` of the Banach functor (`IsNaturalSection`: `μ(φ)σ(s φ) = σ(t φ)`): the functor
  `x ↦ Γ̄_x⁻¹ σ(Γ_Ψ x)` of the model `W_Ψ̄ → X_Ψ` (`modelSection`), a section with
  `Γ̄(F x) = (Γ_Ψ x, σ(Γ_Ψ x))`, functorial (`isFunctorialSection_modelSection`).
* The Fredholm property in the interior form (`IsScFredholmGermInterior`, Definition 3.1.11 in a
  chart with `0 ∈ int C`) from Propositions 4.7, 4.23, 4.25 chart by chart
  (`isScFredholmGermInterior_of_prop_4_8`), as in the Gromov–Witten charts, which are open
  subsets of sc-Banach spaces (`C = E`); this gives tameness (`isScFredholmSectionTame_of_interior`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace GWMemoir

open Polyfold

universe u

/-! ### Sections of strong polyfold bundles from section functors -/

section Generic

open StrongPolyfoldBundle

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-- **The section `f` of `p` induced by a section functor `F`** (Definition 16.3.18, the text's
`f ∘ γ = Γ ∘ |F|`): `f(z) = Γ|F(x)|` for a representative `x` of `γ⁻¹(z)`. -/
def sectionOfFunctor (S : StrongPolyfoldBundleStructure p) (F : S.A.Obj → S.A.W) (z : Z) : Y :=
  S.Γ (S.A.E.toEpGroupoid.π (F (S.γ.symm z).out))

variable (S : StrongPolyfoldBundleStructure p) {F : S.A.Obj → S.A.W}

/-- `f(γ|x|) = Γ|F(x)|` for every `x`: `|F(x)|` depends only on `|x|` (`F` is functorial). -/
theorem sectionOfFunctor_eq (hF : F ∈ S.A.E.sectionFunctors) {x : S.A.Obj} {z : Z}
    (h : S.γ (S.A.X.π x) = z) :
    sectionOfFunctor S F z = S.Γ (S.A.E.toEpGroupoid.π (F x)) := by
  obtain ⟨hf, hfun⟩ := hF
  unfold sectionOfFunctor
  congr 1
  apply EpStrongBundle.π_eq_π_of_isFunctorialSection hfun
  rw [← h, Homeomorph.symm_apply_apply]
  exact Quotient.out_eq _

theorem continuous_sectionOfFunctor (hF : F ∈ S.A.E.sectionFunctors) :
    Continuous (sectionOfFunctor S F) := by
  refine (StrongPolyfoldBundle.isQuotientMap_γπ S).continuous_iff.2 ?_
  have e : (sectionOfFunctor S F ∘ fun x => S.γ (S.A.X.π x)) =
      fun x => S.Γ (S.A.E.toEpGroupoid.π (F x)) :=
    funext fun x => sectionOfFunctor_eq S hF rfl
  rw [e]
  exact S.Γ.continuous.comp (S.A.E.toEpGroupoid.continuous_π.comp
    (continuousOn_univ.1 hF.1.2.continuousOn))

theorem p_sectionOfFunctor (hF : F ∈ S.A.E.sectionFunctors) (z : Z) :
    p (sectionOfFunctor S F z) = z := by
  obtain ⟨ξ, rfl⟩ := S.γ.surjective z
  induction ξ using Quotient.inductionOn with | h x => ?_
  change p (sectionOfFunctor S F (S.γ (S.A.X.π x))) = S.γ (S.A.X.π x)
  rw [sectionOfFunctor_eq S hF rfl, S.p_Γ]
  change S.γ (S.A.X.π (S.A.P (F x))) = _
  rw [hF.1.1 x]

variable {c : StrongPolyfoldBundle p}

/-- **The representative `(f, Γ, W, F)`** of the section induced by a section functor
(Definition 16.3.18). -/
def sectionRepOfFunctor (hS : ⟦S⟧ = c) (F : S.A.Obj → S.A.W) (hF : F ∈ S.A.E.sectionFunctors) :
    SectionRep c where
  S := S
  hS := hS
  F := F
  hF := hF
  f := sectionOfFunctor S F
  continuous_f := continuous_sectionOfFunctor S hF
  isSection := p_sectionOfFunctor S hF
  comm _ := sectionOfFunctor_eq S hF rfl

/-- **The sc-Fredholm section induced by an sc-Fredholm section functor** (Definition 16.6.1). -/
def fredholmSectionOfFunctor (hS : ⟦S⟧ = c) (F : S.A.Obj → S.A.W)
    (hF : F ∈ S.A.E.fredholmSectionFunctors) : FredholmSection c :=
  ⟨Quotient.mk _ (sectionRepOfFunctor S hS F hF.1), _, rfl, hF⟩

/-- **The solution set** (Definition 16.6.2): `S_f = γ|{x | F(x) = 0_x}|`. -/
theorem solutionSet_fredholmSectionOfFunctor (hS : ⟦S⟧ = c) (F : S.A.Obj → S.A.W)
    (hF : F ∈ S.A.E.fredholmSectionFunctors) :
    (fredholmSectionOfFunctor S hS F hF).1.solutionSet =
      (fun x => S.γ (S.A.X.π x)) '' {x | F x = fiberZero S.A.P x} := by
  ext z
  change sectionOfFunctor S F z = c.zeroAt z ↔ _
  rw [StrongPolyfoldBundle.zeroAt_eq_of_mem hS]
  obtain ⟨ξ, rfl⟩ := S.γ.surjective z
  induction ξ using Quotient.inductionOn with | h x => ?_
  change sectionOfFunctor S F (S.γ (S.A.X.π x)) = S.zeroAt (S.γ (S.A.X.π x)) ↔ _
  have hp : p (S.Γ (S.A.E.toEpGroupoid.π (F x))) = S.γ (S.A.X.π x) := by
    rw [← sectionOfFunctor_eq S hF.1 rfl]
    exact p_sectionOfFunctor S hF.1 _
  have hPx : S.A.P (F x) = x := hF.1.1.1 x
  rw [sectionOfFunctor_eq S hF.1 rfl]
  conv_lhs => rw [← hp]
  rw [S.Γ_π_eq_zeroAt_iff, hPx]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hxy : S.A.X.π y = S.A.X.π x := S.γ.injective hyx
    have h1 : S.A.E.toEpGroupoid.π (F y) = S.A.E.toEpGroupoid.π (F x) :=
      EpStrongBundle.π_eq_π_of_isFunctorialSection hF.1.2 hxy
    have h2 : S.A.E.toEpGroupoid.π (fiberZero S.A.P y) =
        S.A.E.toEpGroupoid.π (fiberZero S.A.P x) :=
      SBLocalization.π_fiberZero_eq_of_π_eq hxy
    have h3 : S.Γ (S.A.E.toEpGroupoid.π (F x)) =
        S.zeroAt (p (S.Γ (S.A.E.toEpGroupoid.π (F x)))) := by
      rw [hp, S.zeroAt_eq rfl, ← h1, hy, h2]
    rw [S.Γ_π_eq_zeroAt_iff, hPx] at h3
    exact h3

end Generic

/-! ### Natural sections of a Banach functor on the bundle model -/

section Model

open GroupoidalCategory GroupoidalCategory.BanachFunctor
  GCT.VectorBundle.StrongPolyfoldBundleConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}

/-- **A natural section of the Banach functor** `μ`: `σ(α) ∈ μ(α)` with `μ(φ)σ(s φ) = σ(t φ)`
(the fibre part of a section functor of `P : E_μ → C` on objects, Definition 8.3.4). -/
def IsNaturalSection (σ : ∀ a : C.Obj, V.V a) : Prop :=
  ∀ φ : C.Mor, V.map φ (σ (C.toGroupoidStr.src φ)) = σ (C.toGroupoidStr.tgt φ)

/-- `μ(φ)(a, σ(a)) = (t φ, σ(t φ))` for a natural section. -/
theorem act_objMk_of_isNaturalSection {σ : ∀ a : C.Obj, V.V a} (hσ : IsNaturalSection σ)
    (φ : C.Mor) {a : C.Obj} (h : V.base (V.objMk a (σ a)) = C.toGroupoidStr.src φ) :
    V.act φ (V.objMk a (σ a)) h = V.objMk _ (σ (C.toGroupoidStr.tgt φ)) := by
  have h' : a = C.toGroupoidStr.src φ := h
  subst h'
  rw [act_objMk, hσ φ]

variable (Q : V.StrongPolyfoldBundleConstruction S) {ι : Type u} (Ψb : ι → Q.Unif)

/-- **The section functor of the model induced by a natural section** (memoir p. 101: on objects
`F(α) = (α, ∂̄_J(α))`): `F(x) = Γ̄_x⁻¹ σ(Γ_Ψ x)`, with `Γ̄_x : W_x ≅ μ(Γ_Ψ x)` the fibre map of
`Γ̄_Ψ̄` (Definition 17.7.2 (2)). -/
def modelSection (σ : ∀ a : C.Obj, V.V a) (x : S.ModelObj (Q.modelBase Ψb)) : Q.ModelW Ψb :=
  ((Q.bundleModelFiber Ψb x).symm (σ ((S.modelFunctor (Q.modelBase Ψb)).obj x))).1

theorem modelP_modelSection (σ : ∀ a : C.Obj, V.V a) (x : S.ModelObj (Q.modelBase Ψb)) :
    Q.modelP Ψb (modelSection Q Ψb σ x) = x :=
  ((Q.bundleModelFiber Ψb x).symm (σ ((S.modelFunctor (Q.modelBase Ψb)).obj x))).2

/-- `Γ̄(F(x)) = (Γ_Ψ x, σ(Γ_Ψ x))`. -/
theorem bundleModelObj_modelSection (σ : ∀ a : C.Obj, V.V a) (x : S.ModelObj (Q.modelBase Ψb)) :
    Q.bundleModelObj Ψb (modelSection Q Ψb σ x) =
      V.objMk _ (σ ((S.modelFunctor (Q.modelBase Ψb)).obj x)) := by
  rw [modelSection, ← objMk_bundleModelFiber, ContinuousLinearEquiv.apply_symm_apply]

/-- `F` is a section of `P : W_Ψ̄ → X_Ψ`. -/
theorem isSection_modelSection (σ : ∀ a : C.Obj, V.V a) :
    IsSection (Q.modelSEP Ψb).P (modelSection Q Ψb σ) :=
  modelP_modelSection Q Ψb σ

/-- **`F` is functorial** (Definition 8.3.4): `F(t φ) = μ(φ, F(s φ))`, since `Γ̄` is injective
on fibres and `Γ̄(μ(φ, F(s φ))) = μ(Γ_Ψ φ)(Γ_Ψ(s φ), σ) = (Γ_Ψ(t φ), σ)`. -/
theorem isFunctorialSection_modelSection {σ : ∀ a : C.Obj, V.V a} (hσ : IsNaturalSection σ) :
    (Q.modelSEP Ψb).E.IsFunctorialSection (isSection_modelSection Q Ψb σ) := by
  intro φ
  set q := EpStrongBundle.sectionPair (P := (Q.modelSEP Ψb).P) (isSection_modelSection Q Ψb σ) φ
  have hP : Q.modelP Ψb (modelSection Q Ψb σ ((S.modelEpGroupoid (Q.modelBase Ψb)).tgt φ)) =
      Q.modelP Ψb (Q.modelMu Ψb q) := by
    rw [modelP_modelSection]
    exact (EpStrongBundle.P_μ (E := (Q.modelSEP Ψb).E) q).symm
  refine bundleModelObj_injective Q Ψb hP ?_
  change Q.bundleModelObj Ψb (modelSection Q Ψb σ ((S.modelEpGroupoid (Q.modelBase Ψb)).tgt φ)) =
    Q.bundleModelObj Ψb (Q.modelMu Ψb q)
  rw [bundleModelObj_modelSection]
  refine Eq.trans ?_ (Q.bundleModelObj_modelMu Ψb q).symm
  have he : (Q.bundleModelMor Ψb q).e =
      V.objMk _ (σ ((S.modelFunctor (Q.modelBase Ψb)).obj
        ((S.modelEpGroupoid (Q.modelBase Ψb)).src φ))) :=
    bundleModelObj_modelSection Q Ψb σ _
  rw [act_congr rfl he _ ((Q.bundleModelMor Ψb q).2.symm.trans (congrArg V.base he)).symm,
    act_objMk_of_isNaturalSection hσ]
  exact congrArg (fun a => V.objMk a (σ a))
    ((S.modelFunctor (Q.modelBase Ψb)).tgt_mor φ).symm

/-- **`F` is an sc-smooth section functor** once it is sc-smooth as a section (the sc-smoothness
of Proposition 4.7). -/
theorem modelSection_mem_sectionFunctors {σ : ∀ a : C.Obj, V.V a} (hσ : IsNaturalSection σ)
    (hsm : (Q.modelSEP Ψb).B.IsScSmoothSection (modelSection Q Ψb σ)) :
    modelSection Q Ψb σ ∈ (Q.modelSEP Ψb).E.sectionFunctors :=
  ⟨hsm, isFunctorialSection_modelSection Q Ψb hσ⟩

end Model

/-! ### The Fredholm property in the interior form -/

section Interior

open Polyfold.StrongRetr Polyfold.StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **Memoir Proposition 4.8 in an interior chart gives an interior sc-Fredholm germ**: the
argument of `isScFredholmGerm2021_of_prop_4_8` in a chart with `0 ∈ int C` (the chart is shrunk
on the base only, so `C` is kept). -/
theorem isScFredholmGermInterior_of_prop_4_8 {c : StrongBundleChart PX P} (hc : B.IsChart c)
    {x₀ : X} (hxs : x₀ ∈ PX.smoothSet) (hxV : x₀ ∈ c.φ.source) (hφ0 : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) {g : c.φ.model.E 0 → c.F 0}
    (hfill : IsFilling2021 c.relOpen c.isRetraction h0 (c.principal f) g)
    (h48 : Prop_4_8 c.U g) (hint : (0 : c.φ.model.E 0) ∈ interior c.φ.model.C) :
    B.IsScFredholmGermInterior f x₀ := by
  obtain ⟨hgs, V, hVo, h0V, hconj⟩ := h48
  have hrcont : ContinuousOn (r c.R) c.U :=
    (c.isRetraction.baseRetraction c.relOpen).isSc1.isSc0.continuousOn_base
  obtain ⟨O', hO'o, hO'⟩ := (continuousOn_iff'.1 hrcont) V hVo
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := zero_mem_O_of_chart hxV hφ0
  have hr0 : r c.R 0 = 0 := r_eq_self c.isRetraction h0O
  set W : Set (c.φ.model.E 0) := V ∩ O' with hWdef
  have hW : IsOpen W := hVo.inter hO'o
  have hmaps : MapsTo (r c.R) (c.U ∩ W) W := by
    rintro y ⟨hyU, hyV, hyO'⟩
    have hry : r c.R y ∈ V := by
      have : y ∈ r c.R ⁻¹' V ∩ c.U := by rw [hO']; exact ⟨hyO', hyU⟩
      exact this.1
    have hrU : r c.R y ∈ c.U := r_mem c.isRetraction hyU
    refine ⟨hry, ?_⟩
    have : r c.R y ∈ r c.R ⁻¹' V ∩ c.U := ⟨by
      change r c.R (r c.R y) ∈ V
      rw [r_r c.isRetraction hyU]; exact hry, hrU⟩
    rw [hO'] at this
    exact this.1
  have h0W : (0 : c.φ.model.E 0) ∈ W := by
    refine ⟨h0V, ?_⟩
    have : (0 : c.φ.model.E 0) ∈ r c.R ⁻¹' V ∩ c.U := ⟨by
      change r c.R 0 ∈ V
      rw [hr0]; exact h0V, h0⟩
    rw [hO'] at this
    exact this.1
  set c' := c.shrink hW hmaps
  have h0' : (0 : c'.φ.model.E 0) ∈ c'.U := ⟨h0, h0W⟩
  have hsub : c'.U ⊆ c.U := inter_subset_left
  have hxV' : x₀ ∈ c'.φ.source := ⟨hxV, by
    change c.φ x₀ ∈ W
    rw [hφ0]; exact h0W⟩
  obtain ⟨y, hy⟩ := c.F.mem_smooth_iff.1 (mem_smooth_of_isScSmooth hgs h0) 1
  have hys : y ∈ c.F.shift.smooth := mem_shift_smooth (hy ▸ mem_smooth_of_isScSmooth hgs h0)
  have hsm1 : IsScSmooth (E := c'.φ.model.E) (F := c.F.shift) c'.U (fun _ => y) :=
    isScSmooth_const_of_mem_smooth c'.relOpen.isScDomain hys
  have hplus : IsScPlusGerm (F := c.F) c'.φ.model.C c'.U (fun _ => y) :=
    ⟨ScNbhdGerm.ofSet c'.relOpen.relOpen h0', fun _ hu => hu,
      hsm1.isScSmoothGerm c'.isQuadrantLike c'.relOpen.relOpen h0'⟩
  have hUV : IsRelOpenInQuadrant c.φ.model.E c.φ.model.C (c.U ∩ V) := c.relOpen.inter_isOpen hVo
  have hconj' : IsConjugateToBasicGerm c'.U (fun u => g u - c.F.toBase 1 y) :=
    (hconj.of_subset hUV ⟨h0, h0V⟩ c'.relOpen
      (fun _ hu => ⟨hu.1, hu.2.1⟩) h0').congr fun u _ => by rw [hy]
  refine ⟨hxs, c', hc.shrink hW hmaps, hxV', hφ0, h0', g, fun _ => y, ?_, hplus, hy, hconj',
    hint⟩
  exact (hfill.isFillingGerm.of_subset c.relOpen c.isRetraction c'.relOpen c'.isRetraction hsub
    h0 h0').isFilling2021 (zero_mem_O_of_chart hxV' hφ0)

/-- **Propositions 4.7, 4.23 and 4.25 at a smooth point, in an interior chart** (memoir §4.2,
pp. 104–118): the chart data of `isScFredholmGerm2021_of_prop_4_23` together with `0 ∈ int C`. -/
def ChartProps (f : X → Y) (x₀ : X) : Prop :=
  ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (_ : IsOpen c.U) (g : c.φ.model.E 0 → c.F 0)
    (_ : IsFilling2021 c.relOpen c.isRetraction h0 (c.principal f) g)
    (A H : Submodule ℝ (c.φ.model.E 0)) (h47 : Prop_4_7 c.U g)
    (_ : Prop_4_23 c.U g A H h47.1) (_ : Prop_4_25 c.U g A H)
    (_ : c.φ.model.E.IsScSplitting A H) (_ : FiniteDimensional ℝ A)
    (B' X' : Submodule ℝ (c.φ.model.E 0)) (_ : c.φ.model.E.IsScSplitting B' X')
    (_ : FiniteDimensional ℝ B') (_ : A ≤ B') (_ : X' ≤ H),
    LinearMap.ker (scDeriv c.U g 0 : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ≤ B' ∧
      (0 : c.φ.model.E 0) ∈ interior c.φ.model.C

variable (B) in
/-- **Memoir Proposition 4.7** (p. 102), first part: the section is sc-smooth and regularizing
(2021 Definition 3.1.16 (1), (2)). -/
def Prop_4_7_section (f : X → Y) : Prop :=
  B.IsScSmoothSection f ∧
    ∀ m, ∀ x ∈ PX.levelSet m, f x ∈ B.doubleLevel m (m + 1) → x ∈ PX.levelSet (m + 1)

/-- **The Fredholm property of Memoir Theorem 4.6 from Propositions 4.7, 4.23, 4.25**: an
sc-smooth regularizing section with the chart data of `ChartProps` at every smooth point is an
sc-Fredholm section (2021 Definition 3.1.16) whose germs are tame (2021 Definition 3.6.4, through
`isScFredholmSectionTame_of_interior`). -/
theorem isScFredholmSection_of_chartProps (h47 : Prop_4_7_section B f)
    (h : ∀ x₀ ∈ PX.smoothSet, ChartProps (B := B) f x₀) :
    B.IsScFredholmSection f ∧ B.IsScFredholmSectionTame f := by
  have hgerm : ∀ x₀ ∈ PX.smoothSet, B.IsScFredholmGermInterior f x₀ := by
    intro x₀ hx
    obtain ⟨c, hc, hxV, hφ0, h0, hUo, g, hfill, A, H, h47c, h423, h425, hAH, hA, B', X', hBX, hB',
      hAB, hXH, hker, hint⟩ := h x₀ hx
    have := hA
    have := hB'
    exact isScFredholmGermInterior_of_prop_4_8 hc hx hxV hφ0 h0 hfill
      (memoir_proposition_4_8_of_4_23 hUo h0 h47c h423 h425 hAH hBX hAB hXH hker) hint
  have h2021 : B.IsScFredholmSection2021 f :=
    { isScSmooth := h47.1
      regularizing := h47.2
      germ := fun x hx => by
        obtain ⟨hxs, c, hc, hxV, hφ0, h0, g, s, h1, h2, h3, h4, -⟩ := hgerm x hx
        exact ⟨hxs, c, hc, hxV, hφ0, h0, g, s, h1, h2, h3, h4⟩ }
  exact ⟨isScFredholmSection2021_iff.1 h2021, isScFredholmSectionTame_of_interior h2021 hgerm⟩

end Interior

end GWMemoir
