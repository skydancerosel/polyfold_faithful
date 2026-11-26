import GWMemoir.CauchyRiemannSection

/-!
Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I: The Polyfolds of Gromov–Witten
Theory*, Memoirs AMS 248 (2017), Theorem 1.11 (p. 8) = Theorem 4.6 (p. 101) and
Proposition 4.7 (p. 102): **`∂̄_J` as an sc-Fredholm section of `W → Z`**, compared with the
book (*Polyfold and Fredholm Theory*, Springer 2021): Definitions 3.1.16, 3.6.4, 16.3.18,
16.6.1, 16.6.2.

## The memoir, paraphrased

(Theorem 1.11) The Cauchy–Riemann section `∂̄_J` of `p : W → Z` is an sc-smooth
component-proper Fredholm section; on the component `Z_{A,g,k}` its index is
`2c₁(A) + (2n − 6)(1 − g) + 2k`, and it has a natural orientation.  (p. 101) It is induced
from the section functor `F(α) = (α, ∂̄_J(α))` of the model bundle.

## What is formalized (namespace `GWMemoir`)

* `StableMapLabel C`: a groupoidal category whose objects are labelled by stable maps and whose
  morphisms by isomorphisms of stable maps; `gwLabel` for the category of all stable maps
  (`gwCategory`).  A component (for instance the stable maps of a given energy, closed under
  isomorphism) is a full subcategory with the inclusion as label.
* `FibreIdentification`: linear maps `ι_a` from the `(0,1)`-forms along `L(a)` to the Banach
  fibre `μ(a)`, natural under isomorphisms and injective on fibre elements of class `(k, δ)`.
  This is the identification of the fibre of `W` (memoir p. 7) with the Banach functor; the
  Banach fibres themselves are not constructed here.
* `dbarNatural`: `a ↦ ι_a(∂̄_J L(a))` is a natural section (chain rule `Iso.pullbackForm_dbar`).
* **`memoir_theorem_1_11`**: with the hypotheses of `memoir_theorem_1_10`, a fibre
  identification and, for the model functor of a covering family, Proposition 4.7 (sc-smooth,
  regularizing) and Propositions 4.7, 4.23, 4.25 in interior charts at smooth points:
  `∂̄_J` is an sc-Fredholm section of the strong polyfold bundle of Theorem 1.10 whose model
  functor has tame germs, and its solution set is the set of classes of `J`-holomorphic stable
  maps.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped Manifold ContDiff

noncomputable section

namespace GWMemoir

open Polyfold Polyfold.StrongPolyfoldBundle

/-! ### Labels and fibre identifications -/

section Label

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ}

variable (om m k δ) in
/-- **A labelling of a groupoidal category by stable maps**: objects `a ↦ L(a)`, morphisms
`φ ↦ L(φ) : L(s φ) ≅ L(t φ)`. -/
structure StableMapLabel (C : GroupoidalCategory.{1}) where
  obj : C.Obj → StableMap om m k δ
  iso : ∀ φ : C.Mor, StableMap.Iso (obj (C.toGroupoidStr.src φ)) (obj (C.toGroupoidStr.tgt φ))

/-- The label of the category of all stable maps (witness): `L = id`. -/
def gwLabel (hfin : FiniteIsos' (om := om) m k δ) : StableMapLabel om m k δ (gwCategory hfin) where
  obj α := α
  iso φ := φ.2.2

variable {C : GroupoidalCategory.{1}}

/-- **The fibre of `W` and the Banach functor** (memoir p. 7: the fibre over `α` consists of the
`(0,1)`-forms along `u` of class `(k + 2, δ_k)` on bi-level `(m, k)`): linear maps `ι_a` from the
forms along `L(a)` to `μ(a)`, natural (`μ(φ) ι(f^*ξ') = ι(ξ')` for `f = L(φ)`) and injective on
fibre elements of class `(k', δ')`. -/
structure FibreIdentification (L : StableMapLabel om m k δ C) (V : GroupoidalCategory.BanachFunctor C)
    (J : AlmostComplexStructure E Q) (k' : ℕ) (δ' : ℝ) where
  ι : ∀ a : C.Obj, ((L.obj a).dom.S → E2 →L[ℝ] E) →ₗ[ℝ] V.V a
  natural : ∀ (φ : C.Mor) (ξ' : (L.obj (C.toGroupoidStr.tgt φ)).dom.S → E2 →L[ℝ] E),
    V.map φ (ι _ ((L.iso φ).φ.pullbackForm ξ')) = ι _ ξ'
  injOn : ∀ a, InjOn (ι a) {ξ | IsFibreElement J (L.obj a) k' δ' ξ}

variable {L : StableMapLabel om m k δ C} {V : GroupoidalCategory.BanachFunctor C}
  {J : AlmostComplexStructure E Q} {k' : ℕ} {δ' : ℝ}

/-- `a ↦ ι_a(∂̄_J L(a))`, the fibre part of `F(α) = (α, ∂̄_J(α))`. -/
def FibreIdentification.dbar (ι : FibreIdentification L V J k' δ') (a : C.Obj) : V.V a :=
  ι.ι a ((L.obj a).dbar J)

/-- **Memoir Theorem 4.6, the regularity of `∂̄_J`** (p. 101; memoir p. 7): `∂̄_J(α)` is a fibre
element of class `(k', δ')` for every label `α = L(a)`. -/
def DbarRegular (L : StableMapLabel om m k δ C) (J : AlmostComplexStructure E Q) (k' : ℕ)
    (δ' : ℝ) : Prop :=
  ∀ a, IsFibreElement J (L.obj a) k' δ' ((L.obj a).dbar J)

/-- `∂̄_J` is natural: `μ(φ) ι(∂̄_J L(s φ)) = ι(∂̄_J L(t φ))`, from the chain rule
(`StableMap.Iso.pullbackForm_dbar`). -/
theorem FibreIdentification.dbar_natural (ι : FibreIdentification L V J k' δ') (φ : C.Mor) :
    V.map φ (ι.dbar (C.toGroupoidStr.src φ)) = ι.dbar (C.toGroupoidStr.tgt φ) := by
  unfold FibreIdentification.dbar
  rw [← (L.iso φ).pullbackForm_dbar J]
  exact ι.natural φ _

/-- The zeros of `a ↦ ι_a(∂̄_J L(a))` are the `J`-holomorphic labels. -/
theorem FibreIdentification.dbar_eq_zero_iff (ι : FibreIdentification L V J k' δ')
    (hreg : DbarRegular L J k' δ') (a : C.Obj) :
    ι.dbar a = 0 ↔ (L.obj a).IsHolomorphic J := by
  unfold FibreIdentification.dbar StableMap.IsHolomorphic
  constructor
  · intro h x
    have h0 : (L.obj a).dbar J = 0 :=
      ι.injOn a (hreg a) (isFibreElement_zero J (L.obj a) k' δ') (by rw [h, map_zero])
    rw [h0]
    rfl
  · intro h
    have h0 : (L.obj a).dbar J = 0 := funext h
    rw [h0, map_zero]

end Label

/-! ### The section functor of the model and the sc-Fredholm section -/

section Model

open GroupoidalCategory GCT.VectorBundle.StrongPolyfoldBundleConstruction

variable {Cg : GCT.{1}} {V : Cg.VectorBundle} {S : Cg.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S) {ι : Type 1} (Ψb : ι → Q.Unif)

/-- The model functor `x ↦ Γ̄_x⁻¹ σ(Γ_Ψ x)` is `0_x` exactly when `σ(Γ_Ψ x) = 0`. -/
theorem modelSection_eq_fiberZero_iff (σ : ∀ a : Cg.Obj, V.V a)
    (x : S.ModelObj (Q.modelBase Ψb)) :
    modelSection Q Ψb σ x = fiberZero (Q.modelSEP Ψb).P x ↔
      σ ((S.modelFunctor (Q.modelBase Ψb)).obj x) = 0 := by
  unfold modelSection fiberZero
  exact Subtype.coe_inj.trans (Q.bundleModelFiber Ψb x).symm.map_eq_zero_iff

end Model

section GW

open GroupoidalCategory GroupoidalCategory.BasicConstruction
  GCT.VectorBundle.StrongPolyfoldBundleConstruction

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ} {J : AlmostComplexStructure E Q} {k' : ℕ} {δ' : ℝ}

variable {C : GroupoidalCategory.{1}} {U : C.UniformizerConstruction} {CS : CSPred U}
  {h310 : U.HasClassUniformizers} {H : Theorem_3_13 U CS} {hCS : CSClosed U CS}
  {hPF : PointFinite U}
  {h322 : Theorem_3_22 U (gwTransitionData H hCS hPF)}
  {h16 : Theorem_1_6_sc U (gwTransitionData H hCS hPF) h310}
  (hTF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, ∀ y : Ψ.P.SmoothLevel, IsTangentFaithfulAt Ψ y)
  (hLF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, IsLocallyFaithful Ψ)
  {V : (gwGCT h310 H hCS hPF h322 h16).VectorBundle}
  (Fb : V.StrongBundleUniformizerConstruction (gwPolyfoldConstruction h310 H hCS hPF h322 h16))
  (h339 : Proposition_3_39 Fb)

include hTF in
/-- The polyfold construction of `Z` satisfies Zhou's condition (Theorem 19.5.3, from the
faithfulness of the actions). -/
theorem gwZhou : (gwPolyfoldConstruction h310 H hCS hPF h322 h16).IsZhou :=
  proposition_19_5_7 (gwMetrizable h310 H hCS hPF h322 h16)
    (isZhou_of_forall_isTangentFaithfulAt (basicOf U (gwTransitionData H hCS hPF)) h310 hTF)

/-- **The strong polyfold bundle `p : W → Z` of Theorem 1.10** for a covering family. -/
abbrev gwBundle (c : (ofProposition_3_39 Fb h339).BundleCoveringFamily) :
    StrongPolyfoldBundle V.proj.orbitMap :=
  bundleOf (gwZhou hTF) (isEffective_toPolyfoldConstruction _ hLF) _ c

variable {L : StableMapLabel om m k δ C}

/-- **The model functor `F(x) = (x, ∂̄_J(Γ_Ψ x))`** of the covering family `c` (memoir p. 101). -/
abbrev dbarFunctor (ιV : FibreIdentification L V.toBanachFunctor J k' δ')
    (c : (ofProposition_3_39 Fb h339).BundleCoveringFamily) :
    ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).Obj → ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).W :=
  modelSection (ofProposition_3_39 Fb h339) c.Ψ ιV.dbar

variable (ιV : FibreIdentification L V.toBanachFunctor J k' δ')
  (c : (ofProposition_3_39 Fb h339).BundleCoveringFamily)

/-- **Memoir Proposition 4.7 and Propositions 4.7, 4.23, 4.25 for the model functor** (pp. 102,
104–118): `F` is sc-smooth and regularizing, and at every smooth point of the model it has an
interior chart with a filling satisfying Propositions 4.7, 4.23, 4.25. -/
def CRProps : Prop :=
  Prop_4_7_section ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).B (dbarFunctor Fb h339 ιV c) ∧
    ∀ x₀ ∈ ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).X.PObj.smoothSet,
      ChartProps (B := ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).B) (dbarFunctor Fb h339 ιV c) x₀

variable {Fb h339 ιV c}

theorem dbarFunctor_mem_fredholm (h : CRProps Fb h339 ιV c) :
    dbarFunctor Fb h339 ιV c ∈
      ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).E.fredholmSectionFunctors :=
  ⟨modelSection_mem_sectionFunctors _ _ ιV.dbar_natural h.1.1,
    (isScFredholmSection_of_chartProps h.1 h.2).1⟩

variable (Fb h339 ιV c)

/-- The structure `((P : W_Ψ̄ → X_Ψ, μ), Γ, γ)` of `gwBundle` (Definition 16.3.1). -/
abbrev gwStructure : StrongPolyfoldBundleStructure V.proj.orbitMap :=
  (ofProposition_3_39 Fb h339).bundleModelStructure (gwZhou hTF) c
    (GCT.VectorBundle.StrongPolyfoldBundleConstruction.isLRLocal_of_isEffective (gwZhou hTF)
      (isEffective_toPolyfoldConstruction _ hLF) c)

/-- **The Cauchy–Riemann section `∂̄_J` of `p : W → Z`** (Definition 16.6.1 from the model
functor, memoir p. 101). -/
def dbarSection (h : CRProps Fb h339 ιV c) : FredholmSection (gwBundle hTF hLF Fb h339 c) :=
  fredholmSectionOfFunctor (gwStructure hTF hLF Fb h339 c) rfl _ (dbarFunctor_mem_fredholm h)

/-- **Memoir Theorem 1.11 = Theorem 4.6, Fredholm part, from the named propositions** (pp. 8,
101–104; 2021 Definitions 3.1.16, 3.6.4, 16.6.1, 16.6.2): with the hypotheses of
`memoir_theorem_1_10`, a fibre identification `ι` and, for the model functor `F` of a covering
family, Propositions 4.7, 4.23, 4.25: `∂̄_J` is an sc-Fredholm section of `W → Z` represented by
`F`, the germs of `F` are tame, and the solution set is the set of classes `γ|x|` of the objects
whose label is `J`-holomorphic (for `∂̄_J` regular of the class of `ι`). -/
theorem memoir_theorem_1_11 (h : CRProps Fb h339 ιV c) :
    ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).B.IsScFredholmSectionTame
        (dbarFunctor Fb h339 ιV c) ∧
      (DbarRegular L J k' δ' →
        (dbarSection hTF hLF Fb h339 ιV c h).1.solutionSet =
          (fun x => (gwStructure hTF hLF Fb h339 c).γ ((gwStructure hTF hLF Fb h339 c).A.X.π x)) ''
            {x | (L.obj (((gwPolyfoldConstruction h310 H hCS hPF h322 h16).modelFunctor
              ((ofProposition_3_39 Fb h339).modelBase c.Ψ)).obj x)).IsHolomorphic J}) := by
  refine ⟨(isScFredholmSection_of_chartProps h.1 h.2).2, fun hreg => ?_⟩
  refine (solutionSet_fredholmSectionOfFunctor (gwStructure hTF hLF Fb h339 c) rfl _
    (dbarFunctor_mem_fredholm h)).trans ?_
  congr 1
  ext x
  exact (modelSection_eq_fiberZero_iff _ _ _ x).trans (ιV.dbar_eq_zero_iff hreg _)

end GW

end GWMemoir
