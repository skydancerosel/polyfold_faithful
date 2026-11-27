import GWMemoir.ConstantBase

/-!
# Theorems 1.10 and 1.11 on the constant maps from the three-pointed sphere

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, Theorem 1.10 (p. 7) and
Theorem 1.11 = Theorem 4.6 (pp. 8, 101), on the category `constCat` of `GWMemoir.ConstantBase`,
read against the 2021 book, Definitions 17.7.1–17.7.4, 16.3.1, 16.6.1.

## What is formalized

* `constGCT`, `constPC`: the GCT `Z` and its polyfold construction built from `constU`, every
  named proposition of the base proved (`GWMemoir.ConstantBase`).
* **`memoir_theorem_1_10_const`**: Theorem 1.10 on this base, the base hypotheses discharged;
  the vector bundle GCT `V`, the strong bundle uniformizers, Proposition 3.39 and
  `HasBundleUniformizers` remain.
* **`memoir_theorem_1_11_const`**: Theorem 1.11 on this base for every vector bundle GCT whose
  Banach functor is `fibreFunctor`: the base hypotheses, the fibre representation, `DbarInDom`
  and `DbarRegularC` are discharged; `Fb`, Proposition 3.39 and `CRProps` remain.
* `memoir_polyfold_structure_const_E2`: on `Q = ℝ²` with `ω₀`, the base category is nonempty and
  the polyfold structure holds.

## Readings

* This category has no nodes, no gluing and no Deligne–Mumford parameters: the statements test
  how the named propositions are wired to the book, not the analysis of the memoir.
* `CRProps` (Propositions 4.7, 4.23, 4.25) has no instance on this data as we read it.  The model
  base is an open set of the finite-dimensional `Q`, while the fibre over a constant map contains
  the anti-linear forms supported in a disc chart, an infinite-dimensional space.  By the
  filling conditions (2021 Definition 3.1.4 (3)), the cokernel of the linearization of a filling
  at `0` is the cokernel of the linearization along the retract, a map from the tangent space of
  the finite-dimensional base into the fibre; it is infinite-dimensional, while Proposition
  4.23 (1) asks a Fredholm operator.  In the memoir the base contains all maps of class
  `(3, δ₀)` near a constant map, and the linearization is the Cauchy–Riemann operator `D_u`,
  which is Fredholm.  So the theorem with
  `CRProps` checks that the remaining hypotheses fit together, and nothing more.
* A vector bundle GCT `V` with `V.toBanachFunctor = fibreFunctor` (Definition 17.7.1) is not built
  here.  `fibreFunctor` uses an atlas chosen at each object (`noNodeAtlas`); a topology on
  `|E_μ|` with `|P|` open needs linear isomorphisms between the fibres over nearby objects.  For
  `Q = ℝ²` with `J₀` the forms and the anti-linearity do not depend on the point `q`, and what is
  missing is the change of atlas: `PullbackBounded J δs h0 hmono A B (Iso.refl _)` for two
  section atlases `A`, `B` of the same map from `sphere3` (boundedness in `H^{2,δ₀}` of the change
  of disc charts).  The strong bundle uniformizers ask moreover the fibre as an sc-Banach space,
  i.e. `FormsDense` (`fibreSc`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped Manifold ContDiff

noncomputable section

namespace GWMemoir

open Polyfold Polyfold.GroupoidalCategory Polyfold.GroupoidalCategory.BasicConstruction
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  [T2Space Q] [ParacompactSpace Q] [SecondCountableTopology Q] [Nonempty Q]

section Base

variable (om : SymplecticForm E Q) (k : ℕ) (δ : ℝ)

/-- The GCT `Z` of the constant maps (Theorem 19.5.3 (1)), from `constU`. -/
abbrev constGCT : GCT.{1} :=
  gwGCT (constU_hasClassUniformizers om k δ) constU_theorem_3_13 constU_csClosed
    constU_pointFinite (constU_theorem_3_22 _) (constU_theorem_1_6_sc _)

/-- The polyfold construction of `Z` on the constant maps (Theorem 19.5.3 (2)). -/
abbrev constPC : (constGCT om k δ).PolyfoldConstruction :=
  gwPolyfoldConstruction (constU_hasClassUniformizers om k δ) constU_theorem_3_13 constU_csClosed
    constU_pointFinite (constU_theorem_3_22 _) (constU_theorem_1_6_sc _)

variable {om k δ}

/-- **Memoir Theorem 1.10 on the constant maps from the three-pointed sphere** (p. 7; 2021
Definitions 17.7.4, 16.3.1): Proposition 3.10, Theorems 3.13, 3.22, 1.6 and the faithfulness of
the actions hold (`GWMemoir.ConstantBase`), so for every vector bundle GCT `V` over `Z` with
strong bundle uniformizers satisfying Proposition 3.39 and `HasBundleUniformizers`, there is the
strong polyfold bundle `W → Z` of the book, the same for every covering family.

This category has no nodes and no gluing: the statement tests the wiring, not the analysis. -/
theorem memoir_theorem_1_10_const {V : (constGCT om k δ).VectorBundle}
    (Fb : V.StrongBundleUniformizerConstruction (constPC om k δ)) (h339 : Proposition_3_39 Fb)
    (hF : HasBundleUniformizers Fb) :
    ∃ (hZ : (constPC om k δ).IsZhou) (W : StrongPolyfoldBundle V.proj.orbitMap),
      W.polyfold = (constPC om k δ).polyfoldClass hZ ∧
      ∀ c : (ofProposition_3_39 Fb h339).BundleCoveringFamily,
        W = bundleOf hZ (isEffective_toPolyfoldConstruction _ constU_locallyFaithful) _ c :=
  memoir_theorem_1_10 constU_tangentFaithful constU_locallyFaithful Fb h339 hF

end Base

section Fredholm

variable {om : SymplecticForm E Q} {k : ℕ} {δ : ℝ} (J : AlmostComplexStructure E Q)
  (δs : ℕ → ℝ) (h0 : 0 ≤ δs 0) (hmono : StrictMono δs) (k' : ℕ) (δ' : ℝ)

/-- **Memoir Theorem 1.11 = Theorem 4.6 on the constant maps from the three-pointed sphere**
(pp. 8, 101; 2021 Definitions 3.1.16, 16.6.1, 16.6.2).  Discharged: every hypothesis of the base
(Proposition 3.10, Theorems 3.13, 3.22, 1.6, faithfulness), the label, the fibre representation
`ιV`, `DbarInDom ιV` and `DbarRegularC`.  Kept: a vector bundle GCT `V` whose Banach functor is
`fibreFunctor`, its strong bundle uniformizers `Fb` with Proposition 3.39, and `CRProps`.  Then,
given `CRProps`, `∂̄_J` is an sc-Fredholm section with tame germs and its solution set is the set
of classes of `J`-holomorphic labels.

This category has no nodes and no gluing: the statement tests the wiring, not the analysis.
`CRProps` has no instance here as we read it (finite-dimensional base, infinite-dimensional
fibre; see the module docstring), so the last part checks only that the hypotheses fit. -/
theorem memoir_theorem_1_11_const (V : (constGCT om k δ).VectorBundle)
    (hV : V.toBanachFunctor = fibreFunctor (constOb_pullbackBounded J δs h0 hmono))
    (Fb : V.StrongBundleUniformizerConstruction (constPC om k δ)) (h339 : Proposition_3_39 Fb)
    (c : (ofProposition_3_39 Fb h339).BundleCoveringFamily) :
    ∃ (ιV : FibreRepresentation om 3 k δ (subLabel (constOb om k δ) constOb_finite)
        V.toBanachFunctor J k' δ') (hd : DbarInDom ιV),
      DbarRegularC (subLabel (constOb om k δ) constOb_finite) J k' δ' ∧
      ∀ h : CRProps Fb h339 ιV hd c,
        ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).B.IsScFredholmSectionTame
            (dbarFunctor Fb h339 ιV hd c) ∧
          (dbarSection constU_tangentFaithful constU_locallyFaithful Fb h339 ιV hd c
              h).1.solutionSet =
            (fun x => (gwStructure constU_tangentFaithful constU_locallyFaithful Fb h339 c).γ
                ((gwStructure constU_tangentFaithful constU_locallyFaithful Fb h339 c).A.X.π x)) ''
              {x | ((subLabel (constOb om k δ) constOb_finite).obj
                (((constPC om k δ).modelFunctor
                  ((ofProposition_3_39 Fb h339).modelBase c.Ψ)).obj x)).IsHolomorphic J} := by
  obtain ⟨ιV, hd, hreg⟩ := memoir_theorem_1_11_fibre_const (k' := k') (δ' := δ') V hV
  exact ⟨ιV, hd, hreg, fun h =>
    let H := memoir_theorem_1_11 constU_tangentFaithful constU_locallyFaithful Fb h339 ιV hd c h
    ⟨H.1, H.2 hreg⟩⟩

end Fredholm

/-- **Witness on `Q = ℝ²`** with `ω₀ = dx ∧ dy`: the category of the constant maps is nonempty
and `memoir_polyfold_structure_const` applies, with no named proposition. -/
theorem memoir_polyfold_structure_const_E2 (k : ℕ) (δ : ℝ) :
    Nonempty (constCat omE2 k δ).Obj ∧
    ∃ (hm : @TopologicalSpace.MetrizableSpace (constCat omE2 k δ).OrbitSpace
        ((basicOf (constU omE2 k δ) (constT omE2 k δ)).natTop
          (constU_hasClassUniformizers omE2 k δ))),
      (basicOf (constU omE2 k δ) (constT omE2 k δ)).IsZhou ∧
      (BasicConstruction.toPolyfoldConstruction hm).IsZhou ∧
      (BasicConstruction.toPolyfoldConstruction hm).IsEffective ∧
        Nonempty (PolyfoldClass ((basicOf (constU omE2 k δ) (constT omE2 k δ)).toGCTOfMetrizable
          (constU_hasClassUniformizers omE2 k δ) hm).toGroupoidStr.OrbitSpace) :=
  ⟨⟨constObj 0⟩, memoir_polyfold_structure_const omE2 k δ⟩

end GWMemoir
