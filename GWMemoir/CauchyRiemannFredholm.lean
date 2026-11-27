import GWMemoir.CauchyRiemannSection
import GWMemoir.FibreRepresentation

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

* `StableMapLabel C` and `FibreRepresentation L V J k' δ'` (`GWMemoir.FibreRepresentation`): the
  label of a groupoidal category by stable maps, and the identification of the fibre of `W`
  (memoir p. 7) with the Banach functor `V`, on the forms with representatives, natural, and
  injective on the continuous fibre elements.  With `DbarInDom` (Theorem 4.6, regularity),
  `a ↦ ι_a(∂̄_J L(a))` is a natural section (chain rule `Iso.pullbackForm_dbar`); with
  `DbarRegularC` its zeros are the `J`-holomorphic labels.
* **`memoir_theorem_1_11`**: with the hypotheses of `memoir_theorem_1_10`, a fibre
  representation with `DbarInDom` and, for the model functor of a covering family, Proposition
  4.7 (sc-smooth, regularizing) and Propositions 4.7, 4.23, 4.25 in interior charts at smooth
  points:
  `∂̄_J` is an sc-Fredholm section of the strong polyfold bundle of Theorem 1.10 whose model
  functor has tame germs, and its solution set is the set of classes of `J`-holomorphic stable
  maps (given `DbarRegularC`).

## Readings

* An identification injective on all fibre elements (functions on `S`) does not factor through
  the fibre spaces, whose norms do not see a change on a null set
  (`not_factor_of_injOn_fibreElements`, `GWMemoir.FibreInstance`).  The fibre representation
  asks the injectivity on continuous forms; the GW instance on the constant maps from the
  three-pointed sphere is `constFibreRepresentation`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped Manifold ContDiff

noncomputable section

namespace GWMemoir

open Polyfold Polyfold.StrongPolyfoldBundle

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
abbrev dbarFunctor (ιV : FibreRepresentation om m k δ L V.toBanachFunctor J k' δ')
    (hd : DbarInDom ιV) (c : (ofProposition_3_39 Fb h339).BundleCoveringFamily) :
    ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).Obj →
      ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).W :=
  modelSection (ofProposition_3_39 Fb h339) c.Ψ (ιV.dbar hd)

variable (ιV : FibreRepresentation om m k δ L V.toBanachFunctor J k' δ') (hd : DbarInDom ιV)
  (c : (ofProposition_3_39 Fb h339).BundleCoveringFamily)

/-- **Memoir Proposition 4.7 and Propositions 4.7, 4.23, 4.25 for the model functor** (pp. 102,
104–118): `F` is sc-smooth and regularizing, and at every smooth point of the model it has an
interior chart with a filling satisfying Propositions 4.7, 4.23, 4.25. -/
def CRProps : Prop :=
  Prop_4_7_section ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).B (dbarFunctor Fb h339 ιV hd c) ∧
    ∀ x₀ ∈ ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).X.PObj.smoothSet,
      ChartProps (B := ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).B)
        (dbarFunctor Fb h339 ιV hd c) x₀

variable {Fb h339 ιV hd c}

theorem dbarFunctor_mem_fredholm (h : CRProps Fb h339 ιV hd c) :
    dbarFunctor Fb h339 ιV hd c ∈
      ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).E.fredholmSectionFunctors :=
  ⟨modelSection_mem_sectionFunctors _ _ (ιV.dbar_natural hd) h.1.1,
    (isScFredholmSection_of_chartProps h.1 h.2).1⟩

variable (Fb h339 ιV hd c)

/-- The structure `((P : W_Ψ̄ → X_Ψ, μ), Γ, γ)` of `gwBundle` (Definition 16.3.1). -/
abbrev gwStructure : StrongPolyfoldBundleStructure V.proj.orbitMap :=
  (ofProposition_3_39 Fb h339).bundleModelStructure (gwZhou hTF) c
    (GCT.VectorBundle.StrongPolyfoldBundleConstruction.isLRLocal_of_isEffective (gwZhou hTF)
      (isEffective_toPolyfoldConstruction _ hLF) c)

/-- **The Cauchy–Riemann section `∂̄_J` of `p : W → Z`** (Definition 16.6.1 from the model
functor, memoir p. 101). -/
def dbarSection (h : CRProps Fb h339 ιV hd c) : FredholmSection (gwBundle hTF hLF Fb h339 c) :=
  fredholmSectionOfFunctor (gwStructure hTF hLF Fb h339 c) rfl _ (dbarFunctor_mem_fredholm h)

/-- **Memoir Theorem 1.11 = Theorem 4.6, Fredholm part, from the named propositions** (pp. 8,
101–104; 2021 Definitions 3.1.16, 3.6.4, 16.6.1, 16.6.2): with the hypotheses of
`memoir_theorem_1_10`, a fibre representation `ι` with `∂̄_J L(a)` in its domain (`DbarInDom`)
and, for the model functor `F` of a covering family, Propositions 4.7, 4.23, 4.25: `∂̄_J` is an
sc-Fredholm section of `W → Z` represented by `F`, the germs of `F` are tame, and the solution
set is the set of classes `γ|x|` of the objects whose label is `J`-holomorphic (for `∂̄_J` a
continuous fibre element of the class of `ι`, `DbarRegularC`). -/
theorem memoir_theorem_1_11 (h : CRProps Fb h339 ιV hd c) :
    ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).B.IsScFredholmSectionTame
        (dbarFunctor Fb h339 ιV hd c) ∧
      (DbarRegularC L J k' δ' →
        (dbarSection hTF hLF Fb h339 ιV hd c h).1.solutionSet =
          (fun x => (gwStructure hTF hLF Fb h339 c).γ ((gwStructure hTF hLF Fb h339 c).A.X.π x)) ''
            {x | (L.obj (((gwPolyfoldConstruction h310 H hCS hPF h322 h16).modelFunctor
              ((ofProposition_3_39 Fb h339).modelBase c.Ψ)).obj x)).IsHolomorphic J}) := by
  refine ⟨(isScFredholmSection_of_chartProps h.1 h.2).2, fun hreg => ?_⟩
  refine (solutionSet_fredholmSectionOfFunctor (gwStructure hTF hLF Fb h339 c) rfl _
    (dbarFunctor_mem_fredholm h)).trans ?_
  congr 1
  ext x
  exact (modelSection_eq_fiberZero_iff _ _ _ x).trans (ιV.dbar_eq_zero_iff hd hreg _)

end GW

end GWMemoir
