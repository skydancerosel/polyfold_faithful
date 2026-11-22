import Polyfold.Chapter17.ModelComparison
import Polyfold.Chapter10.LocalizationLR
import Polyfold.Chapter10.LocalizationLRCounterexample
import Polyfold.Chapter8.SmoothRegularAssembly
import Polyfold.Chapter16.PolyfoldMaps

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 758–759): **Definition 17.1.22**, **Propositions 17.1.23, 17.1.24, 17.1.25** and
**Theorem 17.1.26**.  Numbers and pages are the 2021 text's.

# Properties of a polyfold `C = (C, F, M)` through its models `X_Ψ`

## The text, paraphrased

(p. 758) By Theorem 17.1.18 any two models `X_Ψ`, `X_Ψ'` of covering sets are related by the
generalized isomorphism `f_{Ψ,Ψ'}` with `|Γ_Ψ'| ∘ |f_{Ψ,Ψ'}| = |Γ_Ψ|`; since (ZHOU), (LUC), (LR),
(SLUC), (SLR) are invariant under generalized isomorphisms (Theorem 10.3.21), if one `X_Ψ` has
such a property, all have it.  (Definition 17.1.22) `C` has (LR), (SLR), (LUC), (SLUC) or (ZHOU)
if some covering set `Ψ` has `X_Ψ` with that property.  (Proposition 17.1.23) (ZHOU) implies
(LUC), (SLUC), (LR), (SLR) (Theorems 7.4.13, 7.4.24).  (Proposition 17.1.24) If `C` has one of
these properties, every `X_Ψ` has it (Theorem 10.3.21).  (Proposition 17.1.25) If `C` has "the
local regularity property (LUC)", every generalized isomorphism `h : X_Ψ → X_Ψ'` with
`|Γ_Ψ'| ∘ |h| = |Γ_Ψ|` equals `f_{Ψ,Ψ'}`.  *Proof* (text): every `X_Ψ` has the local regularity
property, so by Theorem 10.3.19 a generalized isomorphism is determined by its orbit map, and
`|f_{Ψ,Ψ'}| = |Γ_Ψ'|⁻¹ ∘ |Γ_Ψ| = |h|`.  (Theorem 17.1.26, p. 759) Under (ZHOU), each
`(X_Ψ, |Γ_Ψ|)` is a polyfold structure on the metrizable space `|C|` (Definition 16.1.1), any two
are equivalent, and the class `c_C` gives the natural assignment `(C, F, M) ↦ (|C|, c_C)`.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `IsGenIsoInvariant P` (a property of ep-groupoids invariant under generalized isomorphisms),
  `HasModelProperty P` (some covering family `Ψ` has `P(X_Ψ)`), `HasModelProperty.forall`,
  `hasModelProperty_iff` (one covering family suffices and determines it).
* **Definition 17.1.22**: `IsLR`, `IsSLR`, `IsLUC`, `IsSLUC`, `IsZhou` for the polyfold
  construction `S = (F, M)` on `C`; `definition_17_1_22`.  `IsEffective` (the same with
  effectiveness, Definition 7.2.1, used in the effective form of Proposition 17.1.25).
  The invariance: `isGenIsoInvariant_isLR`, …, `isGenIsoInvariant_isEffective`.
* **Proposition 17.1.23**: `proposition_17_1_23`.
* **Proposition 17.1.24**: `proposition_17_1_24` (all five properties, every covering family).
* **Proposition 17.1.25**: the statement `Proposition_17_1_25` (as printed, with (LUC)) and
  `Proposition_17_1_25_LR` (with (LR), the property the proof uses); both do not hold as we read
  them (`ModelPropertiesExamples.lean`).  The forms we prove
  `proposition_17_1_25_of_isEffective` (target model effective),
  `proposition_17_1_25_of_isEffective'` (`C` effective), `proposition_17_1_25_of_isZhou`, and
  `orbitMap_eq_comparison` (the step `|h| = |f_{Ψ,Ψ'}|`, which holds without hypotheses).
* **Theorem 17.1.26**: `modelPolyfoldStructure_equiv` (any two structures `(X_Ψ, |Γ_Ψ|)` are
  equivalent, via `f_{Ψ,Ψ'}`), `polyfoldClass` (`c_C`), `polyfoldClass_eq` (every covering family
  represents it), `theorem_17_1_26`.

## Readings

* "There exists a covering set `Ψ`" is a covering family `c : S.CoveringFamily` (p. 752).
* Proposition 17.1.25 names "the local regularity property (LUC)"; (LUC) is the local unique
  continuation property (Definition 7.2.19), and the local regularity property is (LR)
  (Definition 7.4.19), which Theorem 10.3.19 uses.  We state both readings; the counterexample
  (`ModelPropertiesExamples.lean`) satisfies (LUC), (LR) and even (ZHOU), so neither reading
  holds.  What does not hold as we read it is Theorem 10.3.19 itself (`not_theorem_10_3_19`);
  with an effective target it holds (`theorem_10_3_19_of_isEffective`), and so does
  Proposition 17.1.25.
* `c_C` is defined from a chosen covering family (one exists under (ZHOU) by definition);
  `polyfoldClass_eq` shows that every covering family gives the same class.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

universe u

namespace Polyfold

open EPLocalization EPLocalization.EPLoc

namespace GCT.PolyfoldConstruction

/-! ### Properties invariant under generalized isomorphisms -/

/-- A property of ep-groupoids is **invariant under generalized isomorphisms** (the form of
Theorem 10.3.21). -/
def IsGenIsoInvariant (P : EP.{u} → Prop) : Prop :=
  ∀ {X Y : EP.{u}} {f : EPLoc.of X ⟶ EPLoc.of Y}, IsGeneralizedIso f → (P X ↔ P Y)

theorem isGenIsoInvariant_isLR : IsGenIsoInvariant fun X : EP.{u} => X.X.IsLR :=
  fun hf => (theorem_10_3_21_all hf).1

theorem isGenIsoInvariant_isLUC : IsGenIsoInvariant fun X : EP.{u} => X.X.IsLUC :=
  fun hf => (theorem_10_3_21_all hf).2.1

theorem isGenIsoInvariant_isSLR : IsGenIsoInvariant EP.IsSLR.{u} :=
  fun hf => (theorem_10_3_21_all hf).2.2.1

theorem isGenIsoInvariant_isSLUC : IsGenIsoInvariant EP.IsSLUC.{u} :=
  fun hf => (theorem_10_3_21_all hf).2.2.2.1

theorem isGenIsoInvariant_isZhou : IsGenIsoInvariant fun X : EP.{u} => X.X.IsZhou :=
  fun hf => (theorem_10_3_21_all hf).2.2.2.2

theorem isGenIsoInvariant_isEffective : IsGenIsoInvariant fun X : EP.{u} => X.X.IsEffective :=
  fun hf => EPLoc.isEffective_iff_of_isGeneralizedIso hf

variable {C : GCT.{u}} (S : C.PolyfoldConstruction)

/-- **`C` has the model property `P`**: the model `X_Ψ` of some covering set `Ψ` has `P`
(the form of Definition 17.1.22). -/
def HasModelProperty (P : EP.{u} → Prop) : Prop := ∃ c : S.CoveringFamily, P (S.modelEP c.Ψ)

variable {S}

/-- **If one model has an invariant property, every model has it** (p. 758, from
Theorem 17.1.18): `f_{Ψ,Ψ'}` is a generalized isomorphism. -/
theorem HasModelProperty.forall {P : EP.{u} → Prop} (hP : IsGenIsoInvariant P)
    (h : S.HasModelProperty P) (c : S.CoveringFamily) : P (S.modelEP c.Ψ) := by
  obtain ⟨c₀, h₀⟩ := h
  exact (hP (S.isGeneralizedIso_comparison c₀ c)).1 h₀

/-- For an invariant property, any one covering family decides it. -/
theorem hasModelProperty_iff {P : EP.{u} → Prop} (hP : IsGenIsoInvariant P)
    (c : S.CoveringFamily) : S.HasModelProperty P ↔ P (S.modelEP c.Ψ) :=
  ⟨fun h => h.forall hP c, fun h => ⟨c, h⟩⟩

variable (S)

/-! ### Definition 17.1.22 -/

/-- **2021 Definition 17.1.22, p. 758**: `C = (C, F, M)` has the **local regularity property
(LR)** if `X_Ψ` has (LR) (Definition 7.4.19) for some covering set `Ψ`. -/
def IsLR : Prop := S.HasModelProperty fun X => X.X.IsLR

/-- **2021 Definition 17.1.22, p. 758**: `C` has **(SLR)** (Definition 7.4.23) if some `X_Ψ` has
it. -/
def IsSLR : Prop := S.HasModelProperty EP.IsSLR

/-- **2021 Definition 17.1.22, p. 758**: `C` has **(LUC)** (Definition 7.2.19) if some `X_Ψ` has
it. -/
def IsLUC : Prop := S.HasModelProperty fun X => X.X.IsLUC

/-- **2021 Definition 17.1.22, p. 758**: `C` has **(SLUC)** (Definition 7.4.12) if some `X_Ψ` has
it. -/
def IsSLUC : Prop := S.HasModelProperty EP.IsSLUC

/-- **2021 Definition 17.1.22, p. 758**: `C` satisfies **(ZHOU)** (Definition 7.4.5) if some
`X_Ψ` does. -/
def IsZhou : Prop := S.HasModelProperty fun X => X.X.IsZhou

/-- `C` is **effective** if some `X_Ψ` is effective (Definition 7.2.1).  Not in the text; it is
the hypothesis of the effective form of Proposition 17.1.25. -/
def IsEffective : Prop := S.HasModelProperty fun X => X.X.IsEffective

/-- **2021 Definition 17.1.22, p. 758**, in full: each of (LR), (SLR), (LUC), (SLUC), (ZHOU) holds
for `C` iff it holds for the model of some covering set, iff it holds for the model of a given
covering set `c`. -/
theorem definition_17_1_22 (c : S.CoveringFamily) :
    (S.IsLR ↔ (S.modelEP c.Ψ).X.IsLR) ∧ (S.IsSLR ↔ (S.modelEP c.Ψ).IsSLR) ∧
      (S.IsLUC ↔ (S.modelEP c.Ψ).X.IsLUC) ∧ (S.IsSLUC ↔ (S.modelEP c.Ψ).IsSLUC) ∧
      (S.IsZhou ↔ (S.modelEP c.Ψ).X.IsZhou) :=
  ⟨hasModelProperty_iff isGenIsoInvariant_isLR c, hasModelProperty_iff isGenIsoInvariant_isSLR c,
    hasModelProperty_iff isGenIsoInvariant_isLUC c,
    hasModelProperty_iff isGenIsoInvariant_isSLUC c,
    hasModelProperty_iff isGenIsoInvariant_isZhou c⟩

/-! ### Propositions 17.1.23 and 17.1.24 -/

/-- **2021 Proposition 17.1.23, p. 758**: if `C` satisfies (ZHOU), it has (LUC), (SLUC), (LR)
and (SLR) (Theorems 7.4.13 and 7.4.24, on the same model). -/
theorem proposition_17_1_23 (h : S.IsZhou) : S.IsLUC ∧ S.IsSLUC ∧ S.IsLR ∧ S.IsSLR := by
  obtain ⟨c, hc⟩ := h
  have hSLUC := (S.modelEP c.Ψ).theorem_7_4_13_all_of_isZhou hc
  have hSLR := (S.modelEP c.Ψ).theorem_7_4_24_all_of_isZhou hc
  exact ⟨⟨c, hSLUC 0⟩, ⟨c, hSLUC⟩, ⟨c, hSLR 0⟩, ⟨c, hSLR⟩⟩

/-- **2021 Proposition 17.1.24, p. 758**: if `C` has one of (LR), (SLR), (LUC), (SLUC), (ZHOU),
then the model `X_Ψ` of every covering set `Ψ` has it (Theorem 10.3.21 along `f_{Ψ',Ψ}`). -/
theorem proposition_17_1_24 (c : S.CoveringFamily) :
    (S.IsLR → (S.modelEP c.Ψ).X.IsLR) ∧ (S.IsSLR → (S.modelEP c.Ψ).IsSLR) ∧
      (S.IsLUC → (S.modelEP c.Ψ).X.IsLUC) ∧ (S.IsSLUC → (S.modelEP c.Ψ).IsSLUC) ∧
      (S.IsZhou → (S.modelEP c.Ψ).X.IsZhou) :=
  ⟨fun h => h.forall isGenIsoInvariant_isLR c, fun h => h.forall isGenIsoInvariant_isSLR c,
    fun h => h.forall isGenIsoInvariant_isLUC c, fun h => h.forall isGenIsoInvariant_isSLUC c,
    fun h => h.forall isGenIsoInvariant_isZhou c⟩

theorem IsZhou.model {S : C.PolyfoldConstruction} (h : S.IsZhou) (c : S.CoveringFamily) :
    (S.modelEP c.Ψ).X.IsZhou :=
  h.forall isGenIsoInvariant_isZhou c

theorem IsLR.model {S : C.PolyfoldConstruction} (h : S.IsLR) (c : S.CoveringFamily) :
    (S.modelEP c.Ψ).X.IsLR :=
  h.forall isGenIsoInvariant_isLR c

theorem IsEffective.model {S : C.PolyfoldConstruction} (h : S.IsEffective)
    (c : S.CoveringFamily) : (S.modelEP c.Ψ).X.IsEffective :=
  h.forall isGenIsoInvariant_isEffective c

/-! ### Proposition 17.1.25 -/

/-- **The step `|h| = |f_{Ψ,Ψ'}|` of the proof of Proposition 17.1.25**: a generalized map `h`
with `|Γ_Ψ'| ∘ |h| = |Γ_Ψ|` has the orbit map of `f_{Ψ,Ψ'}` (`|Γ_Ψ'|` is a homeomorphism).  No
hypothesis on `C`. -/
theorem orbitMap_eq_comparison (c c' : S.CoveringFamily)
    {h : localizationFunctor.obj (S.modelEP c.Ψ) ⟶ localizationFunctor.obj (S.modelEP c'.Ψ)}
    (hh : (S.modelFunctor c'.Ψ).orbitMap ∘ EPLoc.orbitMap h = (S.modelFunctor c.Ψ).orbitMap) :
    EPLoc.orbitMap h = EPLoc.orbitMap (S.comparison c c') := by
  funext q
  apply (S.modelOrbitHomeomorph c').injective
  change (S.modelFunctor c'.Ψ).orbitMap (EPLoc.orbitMap h q) =
    (S.modelFunctor c'.Ψ).orbitMap (EPLoc.orbitMap (S.comparison c c') q)
  exact (congrFun hh q).trans (congrFun (S.orbitMap_comparison c c') q).symm

/-- The statement of **2021 Proposition 17.1.25, p. 758**, as printed, in universe `u`: if the
polyfold `(C, F, M)` has (LUC), every generalized isomorphism `h : X_Ψ → X_Ψ'` with
`|Γ_Ψ'| ∘ |h| = |Γ_Ψ|` is `f_{Ψ,Ψ'}`.  It does not hold as we read it:
`not_proposition_17_1_25`. -/
def Proposition_17_1_25 : Prop :=
  ∀ (C : GCT.{u}) (S : C.PolyfoldConstruction), S.IsLUC → ∀ (c c' : S.CoveringFamily)
    (h : localizationFunctor.obj (S.modelEP c.Ψ) ⟶ localizationFunctor.obj (S.modelEP c'.Ψ)),
    IsGeneralizedIso h →
    (S.modelFunctor c'.Ψ).orbitMap ∘ EPLoc.orbitMap h = (S.modelFunctor c.Ψ).orbitMap →
    h = S.comparison c c'

/-- **Proposition 17.1.25 with (LR)** in place of (LUC) (the local regularity property used in
its proof through Theorem 10.3.19), in universe `u`.  It does not hold as we read it either:
`not_proposition_17_1_25_LR`. -/
def Proposition_17_1_25_LR : Prop :=
  ∀ (C : GCT.{u}) (S : C.PolyfoldConstruction), S.IsLR → ∀ (c c' : S.CoveringFamily)
    (h : localizationFunctor.obj (S.modelEP c.Ψ) ⟶ localizationFunctor.obj (S.modelEP c'.Ψ)),
    IsGeneralizedIso h →
    (S.modelFunctor c'.Ψ).orbitMap ∘ EPLoc.orbitMap h = (S.modelFunctor c.Ψ).orbitMap →
    h = S.comparison c c'

/-- **Proposition 17.1.25 for an effective target model** (the effective form): if `C` has (LR)
and the model `X_Ψ'` is effective, every generalized isomorphism `h : X_Ψ → X_Ψ'` with
`|Γ_Ψ'| ∘ |h| = |Γ_Ψ|` is `f_{Ψ,Ψ'}` (Theorem 10.3.19 for an effective target,
`theorem_10_3_19_of_isEffective`). -/
theorem proposition_17_1_25_of_isEffective (hLR : S.IsLR) (c c' : S.CoveringFamily)
    (hc' : (S.modelEP c'.Ψ).X.IsEffective)
    {h : localizationFunctor.obj (S.modelEP c.Ψ) ⟶ localizationFunctor.obj (S.modelEP c'.Ψ)}
    (hgen : IsGeneralizedIso h)
    (hh : (S.modelFunctor c'.Ψ).orbitMap ∘ EPLoc.orbitMap h = (S.modelFunctor c.Ψ).orbitMap) :
    h = S.comparison c c' :=
  theorem_10_3_19_of_isEffective hc' (Or.inl (hLR.model c)) hgen
    (S.isGeneralizedIso_comparison c c') (S.orbitMap_eq_comparison c c' hh)

/-- **Proposition 17.1.25 for an effective polyfold**: if `C` has (LR) and is effective (some, hence
every, model is effective), the conclusion of Proposition 17.1.25 holds for all covering sets. -/
theorem proposition_17_1_25_of_isEffective' (hLR : S.IsLR) (hE : S.IsEffective)
    (c c' : S.CoveringFamily)
    {h : localizationFunctor.obj (S.modelEP c.Ψ) ⟶ localizationFunctor.obj (S.modelEP c'.Ψ)}
    (hgen : IsGeneralizedIso h)
    (hh : (S.modelFunctor c'.Ψ).orbitMap ∘ EPLoc.orbitMap h = (S.modelFunctor c.Ψ).orbitMap) :
    h = S.comparison c c' :=
  S.proposition_17_1_25_of_isEffective hLR c c' (hE.model c') hgen hh

/-- **Proposition 17.1.25 under (ZHOU) for an effective polyfold** ((ZHOU) gives (LR),
Proposition 17.1.23). -/
theorem proposition_17_1_25_of_isZhou (hZ : S.IsZhou) (hE : S.IsEffective)
    (c c' : S.CoveringFamily)
    {h : localizationFunctor.obj (S.modelEP c.Ψ) ⟶ localizationFunctor.obj (S.modelEP c'.Ψ)}
    (hgen : IsGeneralizedIso h)
    (hh : (S.modelFunctor c'.Ψ).orbitMap ∘ EPLoc.orbitMap h = (S.modelFunctor c.Ψ).orbitMap) :
    h = S.comparison c c' :=
  S.proposition_17_1_25_of_isEffective' (S.proposition_17_1_23 hZ).2.2.1 hE c c' hgen hh

/-! ### Theorem 17.1.26 -/

/-- **Any two polyfold structures `(X_Ψ, |Γ_Ψ|)`, `(X_Ψ', |Γ_Ψ'|)` on `|C|` are equivalent**
(Definition 16.1.2), via `f_{Ψ,Ψ'}` (Theorem 17.1.18). -/
theorem modelPolyfoldStructure_equiv (c c' : S.CoveringFamily)
    (hZ : (S.modelEP c.Ψ).X.IsZhou) (hZ' : (S.modelEP c'.Ψ).X.IsZhou) :
    PolyfoldStructure.Equiv (S.modelPolyfoldStructure c hZ) (S.modelPolyfoldStructure c' hZ') :=
  ⟨S.comparison c c', S.isGeneralizedIso_comparison c c', (S.orbitMap_comparison c c').symm⟩

/-- **The class `c_C` of polyfold structures on `|C|`** (Theorem 17.1.26), defined from a covering
family whose model satisfies (ZHOU). -/
def polyfoldClass (h : S.IsZhou) : PolyfoldClass C.toGroupoidStr.OrbitSpace :=
  ⟦S.modelPolyfoldStructure h.choose h.choose_spec⟧

/-- **Every covering family represents `c_C`**: `[(X_Ψ, |Γ_Ψ|)] = c_C`. -/
theorem polyfoldClass_eq (h : S.IsZhou) (c : S.CoveringFamily) :
    (⟦S.modelPolyfoldStructure c (h.model c)⟧ : PolyfoldClass C.toGroupoidStr.OrbitSpace) =
      S.polyfoldClass h :=
  Quotient.sound (S.modelPolyfoldStructure_equiv c h.choose (h.model c) h.choose_spec)

/-- **2021 Theorem 17.1.26, p. 759**: for a polyfold `(C, F, M)` satisfying (ZHOU), the metrizable
orbit space `|C|` carries the natural class `c_C` of polyfold structures (Definition 16.1.1):
for every covering set `Ψ`, `X_Ψ` satisfies (ZHOU), `(X_Ψ, |Γ_Ψ|)` is a polyfold structure on `|C|`
with `X_Ψ` the model and `|Γ_Ψ|` the homeomorphism, and its class is `c_C`. -/
theorem theorem_17_1_26 (h : S.IsZhou) :
    TopologicalSpace.MetrizableSpace C.toGroupoidStr.OrbitSpace ∧
      ∀ c : S.CoveringFamily, ∃ hZ : (S.modelEP c.Ψ).X.IsZhou,
        (S.modelPolyfoldStructure c hZ).X = S.modelEP c.Ψ ∧
        ⇑(S.modelPolyfoldStructure c hZ).β = (S.modelFunctor c.Ψ).orbitMap ∧
        (⟦S.modelPolyfoldStructure c hZ⟧ : PolyfoldClass C.toGroupoidStr.OrbitSpace) =
          S.polyfoldClass h :=
  ⟨inferInstance, fun c => ⟨h.model c, rfl, rfl, S.polyfoldClass_eq h c⟩⟩

end GCT.PolyfoldConstruction

end Polyfold
