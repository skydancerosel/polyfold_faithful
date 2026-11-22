import Polyfold.Chapter17.ProperCoveringGlobalFunctor
import Polyfold.Chapter17.ModelComparison

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8,
(17.104) (p. 838): **different covering families give Morita-equivalent sc-smooth models**
`τ̂ : E → X` of a proper polyfold covering functor `P : A → B` (Definition 17.8.13, p. 836).
Numbers and pages are the 2021 text's.

# The models of different covering families are Morita equivalent

## The text, paraphrased

(p. 838) "Of course, a different covering family produces a different proper covering functor
and the different choices are related by some kind Morita equivalence.  We leave it to the reader
to work out the straightforward, but somewhat lengthy details."  For the base `B` the comparison
is Theorem 17.1.18 (p. 756): for covering families `Ψ`, `Ψ'` the inclusions
`X_Ψ → X_{Ψ ⊔ Ψ'} ← X_Ψ'` are sc-smooth equivalences, and the weak fibred product gives the
generalized isomorphism `f_{Ψ,Ψ'} : X_Ψ → X_Ψ'` with `f_{Ψ,Ψ} = 1`, the cocycle identity and
`|Γ_Ψ'| ∘ |f_{Ψ,Ψ'}| = |Γ_Ψ|`.

## What is formalized (namespace `Polyfold.ProperPolyfoldCoveringStructure`)

* The reindexing functors of the models: `hatMap Uf σ : E_{Uf ∘ σ} → E_Uf` (on objects
  `e_k ↦ e_{σ(k)}`, on morphisms `(e, φ, e') ↦ (e, φ, e')`), `hatFunctor_comp_hatMap`
  (`Γ̂_Uf ∘ hatMap = Γ̂_{Uf ∘ σ}`), **`hatMap_comp_hatModel`** (the square
  `τ̂_Uf ∘ hatMap = (X_{Ψ ∘ σ} → X_Ψ) ∘ τ̂_{Uf ∘ σ}` commutes strictly), and
  **`isEquivalence_hatMap`** (an sc-smooth equivalence when the base family of `Uf ∘ σ` covers).
* `hatIncl` (the same for `Uf ∘ σ = Vf`), `hatIncl_comp`, `hatIncl_id`, `hatIncl_obj`,
  `isEquivalence_hatIncl`, `hatIncl_comp_hatModel`; the inclusions `hatInclLeft`,
  `hatInclRight` into `E_{Uf ⊔ Uf'}`, the weak fibred product `hatFibredProduct`, the diagram
  `hatCompareDiagram` and **`hatCompare Uf Uf' = [d̂] : E_Uf → E_Uf'`**, characterized by
  `hatCompare_comp_incl`.
* `CoveringFamily` (p. 838: a family `(Ψ̂_λ, Ψ_λ)` whose `Ψ_λ` cover `|B|`), `toBase`, and for
  covering families **`hatComparison c c'`** with `hatComparison_self`, `hatComparison_comp`,
  `isGeneralizedIso_hatComparison`, `orbitMap_hatComparison`,
  `isHomeomorph_orbitMap_hatComparison`, and **`hatComparison_comp_hatModel`**:
  `[τ̂'] ∘ f̂ = f ∘ [τ̂]` in `EP(E⁻¹)`, `f = f_{Ψ,Ψ'}` the comparison of Theorem 17.1.18 for `B`.
* **`hatModel_morita`**: the statement of p. 838 in the form of Theorem 17.1.18.
* **`hatModel_morita_strict`**: the zigzag `E_Uf → E_{Uf ⊔ Uf'} ← E_Uf'` over
  `X_Ψ → X_{Ψ ⊔ Ψ'} ← X_Ψ'` of sc-smooth equivalences, with strictly commuting squares, the
  three `τ̂` proper covering functors (Definition 8.5.1) and the `Γ̂` compatible.
* Witness: `reflectionHatModel_morita` (`ProperCoveringReflection`), on the two sheets over the
  reflection `ℤ/2 ⋉ ℝ` with an effective action, for the families with one and two copies of the
  sheet uniformizer.

## Readings

* "Related by some kind of Morita equivalence" is read as Theorem 17.1.18 reads the comparison
  of the models `X_Ψ`: a generalized isomorphism `f̂ : E → E'` (a morphism of `EP(E⁻¹)`,
  Definition 10.3.12, invertible) with `f̂ = 1` for equal families, the cocycle identity and
  `|Γ̂'| ∘ |f̂| = |Γ̂|`, which in addition intertwines the two proper covering functors with the
  comparison `f` of the bases: `[τ̂'] ∘ f̂ = f ∘ [τ̂]`.  The strict form behind it is the zigzag
  through the union of the two families.
* The union of two families is `Sum.elim Uf Uf'`, as for Theorem 17.1.18.
* A covering family (p. 838) is a family of proper covering uniformizers whose base
  uniformizers form a covering family of `B`; the models are built for any family.
-/

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace ProperPolyfoldCoveringStructure

open EPLocalization EPLocalization.EPLoc WeakFibredProduct GCT GCT.PolyfoldConstruction
  ProperCoveringUniformizer ProperCoveringUniformizerConstruction

variable {A B : GCT.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
  (S : ProperPolyfoldCoveringStructure P) (hPc : P.IsProperCoveringGCT)

/-- `τ̂ : E → X` of (17.104) as a morphism of `EP`. -/
abbrev hatModelHom {ι : Type u} (Uf : ι → S.toC.Unif) : S.hatEP Uf hPc ⟶ S.baseEP Uf :=
  S.hatModelFunctor Uf hPc

/-! ### Reindexing the models -/

section Reindex

variable {ι κ μ : Type u}

/-- **The reindexing functor `E_{Uf ∘ σ} → E_Uf`** along `σ : κ → ι`: `e_k ↦ e_{σ(k)}`,
`(e, φ, e') ↦ (e, φ, e')`. -/
def hatMap (Uf : ι → S.toC.Unif) (σ : κ → ι) :
    EpFunctor (S.hatEpGroupoid (Uf ∘ σ) hPc) (S.hatEpGroupoid Uf hPc) where
  obj := Sigma.map σ fun _ e => e
  mor := Sigma.map (Prod.map σ σ) fun _ a => a
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp φ ψ h := by
    obtain ⟨⟨j', k⟩, a⟩ := φ
    obtain ⟨⟨i, j⟩, b⟩ := ψ
    have hc : A.toGroupoidStr.src a.mor = A.toGroupoidStr.tgt b.mor := by
      rw [a.src_mor, b.tgt_mor]
      exact congrArg (S.hatObjMap (Uf ∘ σ)) h
    have e₁ := hatGroupoid_comp_of (S := S) (Uf := Uf ∘ σ) a b hc
    have e₂ := hatGroupoid_comp_of (S := S) (Uf := Uf) (i := σ i) (j := σ j) (j' := σ j')
      (k := σ k) a b hc
    change Sigma.map (Prod.map σ σ) (fun _ a => a)
        ((S.hatGroupoid (Uf ∘ σ)).comp ⟨(j', k), a⟩ ⟨(i, j), b⟩) =
      (S.hatGroupoid Uf).comp ⟨(σ j', σ k), a⟩ ⟨(σ i, σ j), b⟩
    rw [e₁, e₂]
    rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_sigmaMap _ fun _ => MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := MPolyfold.isScSmoothMap_sigmaMap _ fun _ => MPolyfold.isScSmoothMap_id

@[simp] theorem hatMap_obj (Uf : ι → S.toC.Unif) (σ : κ → ι) (x : S.HatObj (Uf ∘ σ)) :
    (S.hatMap hPc Uf σ).obj x = ⟨σ x.1, x.2⟩ := rfl

@[simp] theorem hatMap_mor (Uf : ι → S.toC.Unif) (σ : κ → ι) (φ : S.HatMor (Uf ∘ σ)) :
    (S.hatMap hPc Uf σ).mor φ = ⟨(σ φ.1.1, σ φ.1.2), φ.2⟩ := rfl

/-- `hatMap` as a morphism of `EP`. -/
abbrev hatMapHom (Uf : ι → S.toC.Unif) (σ : κ → ι) : S.hatEP (Uf ∘ σ) hPc ⟶ S.hatEP Uf hPc :=
  S.hatMap hPc Uf σ

/-- `Γ̂_Uf ∘ (E_{Uf ∘ σ} → E_Uf) = Γ̂_{Uf ∘ σ}`. -/
theorem hatFunctor_comp_hatMap (Uf : ι → S.toC.Unif) (σ : κ → ι) :
    (S.hatFunctor Uf hPc).comp (S.hatMap hPc Uf σ).toGroupoidFunctor =
      S.hatFunctor (Uf ∘ σ) hPc := rfl

/-- **The reindexing square commutes strictly**: `τ̂_Uf ∘ (E_{Uf ∘ σ} → E_Uf) =
(X_{Ψ ∘ σ} → X_Ψ) ∘ τ̂_{Uf ∘ σ}`, with `X_{Ψ ∘ σ} → X_Ψ` the reindexing functor of the models
of `B` (p. 755). -/
theorem hatMap_comp_hatModel (Uf : ι → S.toC.Unif) (σ : κ → ι) :
    S.hatMapHom hPc Uf σ ≫ S.hatModelHom hPc Uf =
      S.hatModelHom hPc (Uf ∘ σ) ≫ S.SB.modelMap (S.baseFam Uf) σ :=
  EpFunctor.ext rfl rfl

/-- **The reindexing functor is an sc-smooth equivalence if the base family of `Uf ∘ σ`
covers `|B|`**: `Γ̂_Uf` and `Γ̂_Uf ∘ hatMap = Γ̂_{Uf ∘ σ}` are equivalences of categories
(`hatFunctor_isEquivalence`), and on objects it is the identity of every `E_k`. -/
theorem isEquivalence_hatMap {Uf : ι → S.toC.Unif} {σ : κ → ι}
    (h : S.SB.IsCoveringFamily (S.baseFam (Uf ∘ σ))) : (S.hatMapHom hPc Uf σ).IsEquivalence := by
  have hU : S.SB.IsCoveringFamily (S.baseFam Uf) :=
    GCT.PolyfoldConstruction.IsCoveringFamily.of_comp (Φ := S.baseFam Uf) (σ := σ) h
  change (S.hatMap hPc Uf σ).IsEquivalence
  have := hatFunctor_isEquivalence hPc hU
  have : ((S.hatMap hPc Uf σ).toFunctor ⋙ (S.hatFunctor Uf hPc).toFunctor).IsEquivalence :=
    hatFunctor_isEquivalence hPc h
  exact EpFunctor.lemma_10_1_2 _
    (Functor.isEquivalence_of_comp_right _ (S.hatFunctor Uf hPc).toFunctor)
    (by
      change (MPolyfold.sigma fun k => ((Uf ∘ σ) k).unif.E.PObj).IsLocalScDiffeo
        (MPolyfold.sigma fun i => (Uf i).unif.E.PObj) (Sigma.map σ fun _ e => e)
      exact MPolyfold.isLocalScDiffeo_sigmaMap _ fun _ => MPolyfold.isLocalScDiffeo_id)

/-- **The inclusion `E_Vf → E_Uf`** of a family `Vf = Uf ∘ σ`. -/
def hatIncl (Vf : κ → S.toC.Unif) (Uf : ι → S.toC.Unif) (σ : κ → ι) (h : Uf ∘ σ = Vf) :
    S.hatEP Vf hPc ⟶ S.hatEP Uf hPc :=
  eqToHom (congrArg (fun W : κ → S.toC.Unif => S.hatEP W hPc) h.symm) ≫ S.hatMapHom hPc Uf σ

theorem hatIncl_rfl (Uf : ι → S.toC.Unif) (σ : κ → ι) :
    S.hatIncl hPc (Uf ∘ σ) Uf σ rfl = S.hatMapHom hPc Uf σ := by
  rw [hatIncl, eqToHom_refl, Category.id_comp]

/-- `hatIncl` on objects, followed by `Γ̂`. -/
theorem hatIncl_obj {Vf : κ → S.toC.Unif} {Uf : ι → S.toC.Unif} {σ : κ → ι} (h : Uf ∘ σ = Vf)
    (x : S.HatObj Vf) : (S.hatFunctor Uf hPc).obj ((S.hatIncl hPc Vf Uf σ h).obj x) =
      (S.hatFunctor Vf hPc).obj x := by
  subst h
  rw [hatIncl_rfl]
  rfl

/-- `Γ̂_Uf ∘ incl = Γ̂_Vf`. -/
theorem hatFunctor_comp_hatIncl {Vf : κ → S.toC.Unif} {Uf : ι → S.toC.Unif} {σ : κ → ι}
    (h : Uf ∘ σ = Vf) :
    (S.hatFunctor Uf hPc).comp (S.hatIncl hPc Vf Uf σ h).toGroupoidFunctor =
      S.hatFunctor Vf hPc := by
  subst h
  rw [hatIncl_rfl]
  rfl

/-- The inclusion of a covering family is an sc-smooth equivalence. -/
theorem isEquivalence_hatIncl {Vf : κ → S.toC.Unif} {Uf : ι → S.toC.Unif} {σ : κ → ι}
    (h : Uf ∘ σ = Vf) (hV : S.SB.IsCoveringFamily (S.baseFam Vf)) :
    (S.hatIncl hPc Vf Uf σ h).IsEquivalence := by
  subst h
  rw [hatIncl_rfl]
  exact S.isEquivalence_hatMap hPc hV

/-- Inclusions compose. -/
theorem hatIncl_comp {Vf : κ → S.toC.Unif} {Uf : ι → S.toC.Unif} {Wf : μ → S.toC.Unif}
    {σ : κ → ι} {τ : ι → μ} {ρ : κ → μ} (h₁ : Uf ∘ σ = Vf) (h₂ : Wf ∘ τ = Uf)
    (h₃ : Wf ∘ ρ = Vf) (hρ : τ ∘ σ = ρ) :
    S.hatIncl hPc Vf Uf σ h₁ ≫ S.hatIncl hPc Uf Wf τ h₂ = S.hatIncl hPc Vf Wf ρ h₃ := by
  subst hρ h₂ h₁
  rw [hatIncl_rfl, hatIncl_rfl, show S.hatIncl hPc ((Wf ∘ τ) ∘ σ) Wf (τ ∘ σ) h₃ =
    S.hatMapHom hPc Wf (τ ∘ σ) from S.hatIncl_rfl hPc Wf (τ ∘ σ)]
  rfl

/-- The inclusion of a family into itself is the identity. -/
theorem hatIncl_id (Uf : κ → S.toC.Unif) : S.hatIncl hPc Uf Uf id rfl = 𝟙 (S.hatEP Uf hPc) := by
  change S.hatIncl hPc (Uf ∘ id) Uf id rfl = _
  rw [hatIncl_rfl]
  rfl

/-- **The inclusion square commutes strictly**: `τ̂_Uf ∘ incl = incl ∘ τ̂_Vf`. -/
theorem hatIncl_comp_hatModel {Vf : κ → S.toC.Unif} {Uf : ι → S.toC.Unif} {σ : κ → ι}
    (h : Uf ∘ σ = Vf) :
    S.hatIncl hPc Vf Uf σ h ≫ S.hatModelHom hPc Uf =
      S.hatModelHom hPc Vf ≫ S.SB.incl (S.baseFam Vf) (S.baseFam Uf) σ
        (congrArg (fun W : κ → S.toC.Unif => S.baseFam W) h) := by
  subst h
  rw [hatIncl_rfl, show S.SB.incl (S.baseFam (Uf ∘ σ)) (S.baseFam Uf) σ _ =
    S.SB.modelMap (S.baseFam Uf) σ from S.SB.incl_rfl (S.baseFam Uf) σ]
  exact S.hatMap_comp_hatModel hPc Uf σ

end Reindex

/-! ### The comparison `f̂ : E_Uf → E_Uf'` -/

section Union

variable {ι ι' : Type u} (Uf : ι → S.toC.Unif) (Uf' : ι' → S.toC.Unif)

/-- `Â : E_Uf → E_{Uf ⊔ Uf'}`. -/
abbrev hatInclLeft : S.hatEP Uf hPc ⟶ S.hatEP (Sum.elim Uf Uf') hPc :=
  S.hatIncl hPc Uf (Sum.elim Uf Uf') Sum.inl rfl

/-- `Â' : E_Uf' → E_{Uf ⊔ Uf'}`. -/
abbrev hatInclRight : S.hatEP Uf' hPc ⟶ S.hatEP (Sum.elim Uf Uf') hPc :=
  S.hatIncl hPc Uf' (Sum.elim Uf Uf') Sum.inr rfl

variable {Uf Uf'}

/-- `Â` is an sc-smooth equivalence. -/
theorem isEquivalence_hatInclLeft (h : S.SB.IsCoveringFamily (S.baseFam Uf)) :
    (S.hatInclLeft hPc Uf Uf').IsEquivalence :=
  S.isEquivalence_hatIncl hPc rfl h

/-- `Â'` is an sc-smooth equivalence. -/
theorem isEquivalence_hatInclRight (h' : S.SB.IsCoveringFamily (S.baseFam Uf')) :
    (S.hatInclRight hPc Uf Uf').IsEquivalence :=
  S.isEquivalence_hatIncl hPc rfl h'

/-- The weak fibred product of `Â` and `Â'` is defined (`Â'` is an equivalence). -/
theorem admissible_hatIncl (h' : S.SB.IsCoveringFamily (S.baseFam Uf')) :
    Admissible (S.hatInclLeft hPc Uf Uf') (S.hatInclRight hPc Uf Uf') :=
  .of_isEquivalence_right (S.isEquivalence_hatInclRight hPc h')

variable (Uf Uf')

/-- **The weak fibred product `E_Uf ×_{E_{Uf ⊔ Uf'}} E_Uf'`**. -/
abbrev hatFibredProduct (h' : S.SB.IsCoveringFamily (S.baseFam Uf')) : EP.{u} :=
  wfp (S.hatInclLeft hPc Uf Uf') (S.hatInclRight hPc Uf Uf') (S.admissible_hatIncl hPc h')

/-- **The diagram** `d̂ : E_Uf ←π₁ E_Uf ×_{E_{Uf ⊔ Uf'}} E_Uf' →π₂ E_Uf'`. -/
def hatCompareDiagram (h' : S.SB.IsCoveringFamily (S.baseFam Uf')) :
    Diagram (S.hatEP Uf hPc) (S.hatEP Uf' hPc) where
  A := S.hatFibredProduct hPc Uf Uf' h'
  F := projLeft (S.hatInclLeft hPc Uf Uf') (S.hatInclRight hPc Uf Uf')
    (S.admissible_hatIncl hPc h')
  isEquivalence_F := isEquivalence_projLeft (S.isEquivalence_hatInclRight hPc h') _
  Φ := projRight (S.hatInclLeft hPc Uf Uf') (S.hatInclRight hPc Uf Uf')
    (S.admissible_hatIncl hPc h')

/-- **The generalized map `f̂ = [d̂] : E_Uf → E_Uf'`**. -/
def hatCompare (h' : S.SB.IsCoveringFamily (S.baseFam Uf')) :
    localizationFunctor.obj (S.hatEP Uf hPc) ⟶ localizationFunctor.obj (S.hatEP Uf' hPc) :=
  EPLoc.homMk (S.hatCompareDiagram hPc Uf Uf' h')

variable {Uf Uf'} in
/-- **`f̂` through any family containing `Uf` and `Uf'`**: if `Uf = Wf ∘ σ` and `Uf' = Wf ∘ σ'`,
then `i(E_Uf' → E_Wf) ∘ f̂ = i(E_Uf → E_Wf)` in `EP(E⁻¹)`. -/
theorem hatCompare_comp_incl {κ : Type u} (Wf : κ → S.toC.Unif) {σ : ι → κ} {σ' : ι' → κ}
    (h : Wf ∘ σ = Uf) (h' : Wf ∘ σ' = Uf') (hc' : S.SB.IsCoveringFamily (S.baseFam Uf')) :
    S.hatCompare hPc Uf Uf' hc' ≫ localizationFunctor.map (S.hatIncl hPc Uf' Wf σ' h') =
      localizationFunctor.map (S.hatIncl hPc Uf Wf σ h) := by
  have hK : Wf ∘ Sum.elim σ σ' = Sum.elim Uf Uf' := by
    funext x
    cases x with
    | inl a => exact congrFun h a
    | inr a => exact congrFun h' a
  have hA : S.hatInclLeft hPc Uf Uf' ≫ S.hatIncl hPc (Sum.elim Uf Uf') Wf (Sum.elim σ σ') hK =
      S.hatIncl hPc Uf Wf σ h :=
    S.hatIncl_comp hPc _ _ _ rfl
  have hA' : S.hatInclRight hPc Uf Uf' ≫ S.hatIncl hPc (Sum.elim Uf Uf') Wf (Sum.elim σ σ') hK =
      S.hatIncl hPc Uf' Wf σ' h' :=
    S.hatIncl_comp hPc _ _ _ rfl
  let dF : S.hatFibredProduct hPc Uf Uf' hc' ⟶ S.hatEP Uf hPc :=
    projLeft (S.hatInclLeft hPc Uf Uf') (S.hatInclRight hPc Uf Uf') (S.admissible_hatIncl hPc hc')
  let dΦ : S.hatFibredProduct hPc Uf Uf' hc' ⟶ S.hatEP Uf' hPc :=
    projRight (S.hatInclLeft hPc Uf Uf') (S.hatInclRight hPc Uf Uf') (S.admissible_hatIncl hPc hc')
  have hπ : EP.equivalences dF := isEquivalence_projLeft (S.isEquivalence_hatInclRight hPc hc') _
  have : IsIso (localizationFunctor.map dF) := isInvertedBy_localizationFunctor dF hπ
  have hnat : localizationFunctor.map (dF ≫ S.hatInclLeft hPc Uf Uf') =
      localizationFunctor.map (dΦ ≫ S.hatInclRight hPc Uf Uf') :=
    map_eq_of_naturallyEquivalent localizationFunctor isInvertedBy_localizationFunctor
      (naturallyEquivalent (S.admissible_hatIncl hPc hc'))
  have key : localizationFunctor.map dF ≫ localizationFunctor.map (S.hatIncl hPc Uf Wf σ h) =
      localizationFunctor.map dΦ ≫ localizationFunctor.map (S.hatIncl hPc Uf' Wf σ' h') := by
    rw [← hA, ← hA', ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← Category.assoc, ← Category.assoc, CategoryTheory.Functor.map_comp, hnat,
      ← CategoryTheory.Functor.map_comp]
  have e : S.hatCompare hPc Uf Uf' hc' =
      inv (localizationFunctor.map dF) ≫ localizationFunctor.map dΦ :=
    EPLoc.homMk_eq _
  rw [e, Category.assoc, IsIso.inv_comp_eq, key]

variable {Uf Uf'} in
/-- **`f̂` intertwines the models with the comparison of the bases**:
`[τ̂_Uf'] ∘ f̂ = f_{Ψ,Ψ'} ∘ [τ̂_Uf]` in `EP(E⁻¹)`, `f_{Ψ,Ψ'}` the generalized map of (17.14) for
the base families. -/
theorem hatCompare_comp_hatModel (hc' : S.SB.IsCoveringFamily (S.baseFam Uf')) :
    S.hatCompare hPc Uf Uf' hc' ≫ localizationFunctor.map (S.hatModelHom hPc Uf') =
      localizationFunctor.map (S.hatModelHom hPc Uf) ≫
        S.SB.compare (S.baseFam Uf) (S.baseFam Uf') hc' := by
  have hI' := S.SB.isEquivalence_incl (Ψ := S.baseFam Uf') (Φ := S.baseFam (Sum.elim Uf Uf'))
    (σ := Sum.inr) rfl hc'
  have : IsIso (localizationFunctor.map
      (S.SB.incl (S.baseFam Uf') (S.baseFam (Sum.elim Uf Uf')) Sum.inr rfl)) :=
    isInvertedBy_localizationFunctor _ hI'
  refine (cancel_mono (localizationFunctor.map
    (S.SB.incl (S.baseFam Uf') (S.baseFam (Sum.elim Uf Uf')) Sum.inr rfl))).1 ?_
  have sq := S.hatIncl_comp_hatModel hPc (Vf := Uf) (Uf := Sum.elim Uf Uf') (σ := Sum.inl) rfl
  have sq' := S.hatIncl_comp_hatModel hPc (Vf := Uf') (Uf := Sum.elim Uf Uf') (σ := Sum.inr) rfl
  have e₁ : localizationFunctor.map (S.hatModelHom hPc Uf') ≫ localizationFunctor.map
      (S.SB.incl (S.baseFam Uf') (S.baseFam (Sum.elim Uf Uf')) Sum.inr rfl) =
      localizationFunctor.map (S.hatInclRight hPc Uf Uf') ≫
        localizationFunctor.map (S.hatModelHom hPc (Sum.elim Uf Uf')) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, sq']
  have e₂ : localizationFunctor.map (S.hatInclLeft hPc Uf Uf') ≫
      localizationFunctor.map (S.hatModelHom hPc (Sum.elim Uf Uf')) =
      localizationFunctor.map (S.hatModelHom hPc Uf) ≫ localizationFunctor.map
        (S.SB.incl (S.baseFam Uf) (S.baseFam (Sum.elim Uf Uf')) Sum.inl rfl) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, sq]
  have e₃ := S.SB.compare_comp_incl (Ψ := S.baseFam Uf) (Ψ' := S.baseFam Uf')
    (S.baseFam (Sum.elim Uf Uf')) (σ := Sum.inl) (σ' := Sum.inr) rfl rfl hc'
  have e₄ := S.hatCompare_comp_incl hPc (Uf := Uf) (Uf' := Uf') (Sum.elim Uf Uf')
    (σ := Sum.inl) (σ' := Sum.inr) rfl rfl hc'
  rw [Category.assoc, Category.assoc, e₁, e₃, ← Category.assoc, e₄, e₂]

end Union

/-! ### Covering families -/

/-- **A covering family of proper covering uniformizers** (2021 p. 838): a family
`(Ψ̂_λ, Ψ_λ)_{λ ∈ Λ}` such that `(Ψ_λ)_{λ ∈ Λ}` is a covering family for `B`. -/
structure CoveringFamily : Type (u + 1) where
  /-- The index set `Λ`. -/
  ι : Type u
  /-- The proper covering uniformizers `(Ψ̂_λ, Ψ_λ)`. -/
  Uf : ι → S.toC.Unif
  /-- The `Ψ_λ` cover `|B|`. -/
  cover : S.SB.IsCoveringFamily (S.baseFam Uf)

variable {S}

/-- The covering family `(Ψ_λ)` of `B`. -/
def CoveringFamily.toBase (c : S.CoveringFamily) : S.SB.CoveringFamily :=
  ⟨c.ι, S.baseFam c.Uf, c.cover⟩

variable (S)

/-- **The comparison `f̂_{c,c'} : E_c → E_c'`** of the models of two covering families. -/
def hatComparison (c c' : S.CoveringFamily) :
    localizationFunctor.obj (S.hatEP c.Uf hPc) ⟶ localizationFunctor.obj (S.hatEP c'.Uf hPc) :=
  S.hatCompare hPc c.Uf c'.Uf c'.cover

theorem hatComparison_comp_incl (c c' : S.CoveringFamily) {κ : Type u} (Wf : κ → S.toC.Unif)
    {σ : c.ι → κ} {σ' : c'.ι → κ} (h : Wf ∘ σ = c.Uf) (h' : Wf ∘ σ' = c'.Uf) :
    S.hatComparison hPc c c' ≫ localizationFunctor.map (S.hatIncl hPc c'.Uf Wf σ' h') =
      localizationFunctor.map (S.hatIncl hPc c.Uf Wf σ h) :=
  S.hatCompare_comp_incl hPc Wf h h' c'.cover

/-- **`f̂_{c,c} = 1`**. -/
theorem hatComparison_self (c : S.CoveringFamily) : S.hatComparison hPc c c = 𝟙 _ := by
  have := S.hatComparison_comp_incl hPc c c c.Uf (σ := id) (σ' := id) rfl rfl
  rwa [hatIncl_id, CategoryTheory.Functor.map_id, Category.comp_id] at this

/-- **The cocycle identity** `f̂_{c',c''} ∘ f̂_{c,c'} = f̂_{c,c''}`. -/
theorem hatComparison_comp (c c' c'' : S.CoveringFamily) :
    S.hatComparison hPc c c' ≫ S.hatComparison hPc c' c'' = S.hatComparison hPc c c'' := by
  let Wf := Sum.elim c.Uf (Sum.elim c'.Uf c''.Uf)
  have e₁ := S.hatComparison_comp_incl hPc c c' Wf (σ := Sum.inl) (σ' := Sum.inr ∘ Sum.inl)
    rfl rfl
  have e₂ := S.hatComparison_comp_incl hPc c' c'' Wf (σ := Sum.inr ∘ Sum.inl)
    (σ' := Sum.inr ∘ Sum.inr) rfl rfl
  have e₃ := S.hatComparison_comp_incl hPc c c'' Wf (σ := Sum.inl) (σ' := Sum.inr ∘ Sum.inr)
    rfl rfl
  have := isInvertedBy_localizationFunctor _
    (S.isEquivalence_hatIncl hPc (Vf := c''.Uf) (Uf := Wf) (σ := Sum.inr ∘ Sum.inr) rfl
      c''.cover)
  refine (cancel_mono (localizationFunctor.map
    (S.hatIncl hPc c''.Uf Wf (Sum.inr ∘ Sum.inr) rfl))).1 ?_
  rw [Category.assoc, e₂, e₁, e₃]

/-- **`f̂_{c,c'}` is a generalized isomorphism**: `π₂` is an equivalence since `Â` is one
(Theorem 10.2.2), and Theorem 10.3.10 applies. -/
theorem isGeneralizedIso_hatComparison (c c' : S.CoveringFamily) :
    IsGeneralizedIso (S.hatComparison hPc c c') :=
  (theorem_10_3_10 (S.hatCompareDiagram hPc c.Uf c'.Uf c'.cover)).1.2
    (isEquivalence_projRight (S.isEquivalence_hatInclLeft hPc c.cover) _)

/-- **`[τ̂_c'] ∘ f̂_{c,c'} = f_{c,c'} ∘ [τ̂_c]`**: the comparison of the models intertwines the
proper covering functors `τ̂` with the comparison `f_{Ψ,Ψ'}` of Theorem 17.1.18 for `B`. -/
theorem hatComparison_comp_hatModel (c c' : S.CoveringFamily) :
    S.hatComparison hPc c c' ≫ localizationFunctor.map (S.hatModelHom hPc c'.Uf) =
      localizationFunctor.map (S.hatModelHom hPc c.Uf) ≫ S.SB.comparison c.toBase c'.toBase :=
  S.hatCompare_comp_hatModel hPc c'.cover

/-- **`|Γ̂_c'| ∘ |f̂_{c,c'}| = |Γ̂_c|`**: on an object `(x, φ'', z)` of the weak fibred product,
`Γ̂_{c ⊔ c'}(φ'') : Γ̂_c(x) → Γ̂_c'(z)`. -/
theorem orbitMap_hatComparison (c c' : S.CoveringFamily) :
    (S.hatFunctor c'.Uf hPc).orbitMap ∘ EPLoc.orbitMap (S.hatComparison hPc c c') =
      (S.hatFunctor c.Uf hPc).orbitMap := by
  funext q
  set d := S.hatCompareDiagram hPc c.Uf c'.Uf c'.cover
  obtain ⟨r, hr⟩ := d.isEquivalence_F.isHomeomorph_orbitMap.bijective.2 q
  change (S.hatFunctor c'.Uf hPc).orbitMap (d.orbitMap q) = (S.hatFunctor c.Uf hPc).orbitMap q
  rw [Diagram.orbitMap_eq_of hr, ← hr]
  induction r using Quotient.inductionOn with
  | h p =>
    change A.toGroupoidStr.π ((S.hatFunctor c'.Uf hPc).obj p.z) =
      A.toGroupoidStr.π ((S.hatFunctor c.Uf hPc).obj p.x)
    refine ((GroupoidStr.π_eq_π_iff _).2
      ⟨(S.hatFunctor (Sum.elim c.Uf c'.Uf) hPc).mor p.φ, ?_, ?_⟩).symm
    · exact ((S.hatFunctor (Sum.elim c.Uf c'.Uf) hPc).src_mor p.φ).trans
        ((congrArg (S.hatFunctor (Sum.elim c.Uf c'.Uf) hPc).obj p.src_φ).trans
          (S.hatIncl_obj hPc _ _))
    · exact ((S.hatFunctor (Sum.elim c.Uf c'.Uf) hPc).tgt_mor p.φ).trans
        ((congrArg (S.hatFunctor (Sum.elim c.Uf c'.Uf) hPc).obj p.tgt_φ).trans
          (S.hatIncl_obj hPc _ _))

/-- **`|f̂_{c,c'}| : |E_c| → |E_c'|` is a homeomorphism**, `|Γ̂_c'|⁻¹ ∘ |Γ̂_c|`. -/
theorem isHomeomorph_orbitMap_hatComparison (c c' : S.CoveringFamily) :
    IsHomeomorph (EPLoc.orbitMap (S.hatComparison hPc c c')) := by
  set e := (isHomeomorph_hatOrbitMap hPc c.cover).homeomorph
  set e' := (isHomeomorph_hatOrbitMap hPc c'.cover).homeomorph
  have he : EPLoc.orbitMap (S.hatComparison hPc c c') = e'.symm ∘ e := by
    funext q
    refine e'.injective ?_
    change (S.hatFunctor c'.Uf hPc).orbitMap (EPLoc.orbitMap (S.hatComparison hPc c c') q) =
      e' (e'.symm (e q))
    rw [Homeomorph.apply_symm_apply]
    exact congrFun (S.orbitMap_hatComparison hPc c c') q
  rw [he]
  exact (e.trans e'.symm).isHomeomorph

/-- **2021 (17.104), p. 838: the models of different covering families are Morita
equivalent.**  For covering families `c`, `c'`, `c''`: `f̂_{c,c'} : E_c → E_c'` is a generalized
isomorphism, `f̂_{c,c} = 1`, `f̂_{c',c''} ∘ f̂_{c,c'} = f̂_{c,c''}`,
`|Γ̂_c'| ∘ |f̂_{c,c'}| = |Γ̂_c|`, `|f̂_{c,c'}|` is a homeomorphism, and `f̂` intertwines the
proper covering functors with the comparison of the bases of Theorem 17.1.18:
`[τ̂_c'] ∘ f̂_{c,c'} = f_{c,c'} ∘ [τ̂_c]`, with `f_{c,c'}` a generalized isomorphism and
`|f_{c,c'}|` a homeomorphism. -/
theorem hatModel_morita (c c' c'' : S.CoveringFamily) :
    IsGeneralizedIso (S.hatComparison hPc c c') ∧ S.hatComparison hPc c c = 𝟙 _ ∧
      S.hatComparison hPc c c' ≫ S.hatComparison hPc c' c'' = S.hatComparison hPc c c'' ∧
      (S.hatFunctor c'.Uf hPc).orbitMap ∘ EPLoc.orbitMap (S.hatComparison hPc c c') =
        (S.hatFunctor c.Uf hPc).orbitMap ∧
      IsHomeomorph (EPLoc.orbitMap (S.hatComparison hPc c c')) ∧
      S.hatComparison hPc c c' ≫ localizationFunctor.map (S.hatModelHom hPc c'.Uf) =
        localizationFunctor.map (S.hatModelHom hPc c.Uf) ≫
          S.SB.comparison c.toBase c'.toBase ∧
      IsGeneralizedIso (S.SB.comparison c.toBase c'.toBase) ∧
      IsHomeomorph (EPLoc.orbitMap (S.SB.comparison c.toBase c'.toBase)) :=
  ⟨S.isGeneralizedIso_hatComparison hPc c c', S.hatComparison_self hPc c,
    S.hatComparison_comp hPc c c' c'', S.orbitMap_hatComparison hPc c c',
    S.isHomeomorph_orbitMap_hatComparison hPc c c', S.hatComparison_comp_hatModel hPc c c',
    S.SB.isGeneralizedIso_comparison _ _, S.SB.isHomeomorph_orbitMap_comparison _ _⟩

/-- **The strict form of the Morita equivalence (p. 838)**: for covering families `c`, `c'` the
zigzag `E_c → E_{c ⊔ c'} ← E_c'` over `X_c → X_{c ⊔ c'} ← X_c'` consists of sc-smooth
equivalences (Definition 10.1.1), the two squares with the `τ̂` commute, the three `τ̂` are
proper covering functors (Definition 8.5.1), and the inclusions are compatible with the
equivalences `Γ̂ : E → A`. -/
theorem hatModel_morita_strict (c c' : S.CoveringFamily) :
    (S.hatInclLeft hPc c.Uf c'.Uf).IsEquivalence ∧
      (S.hatInclRight hPc c.Uf c'.Uf).IsEquivalence ∧
      (S.SB.incl (S.baseFam c.Uf) (S.baseFam (Sum.elim c.Uf c'.Uf)) Sum.inl rfl).IsEquivalence ∧
      (S.SB.incl (S.baseFam c'.Uf) (S.baseFam (Sum.elim c.Uf c'.Uf)) Sum.inr rfl).IsEquivalence ∧
      S.hatInclLeft hPc c.Uf c'.Uf ≫ S.hatModelHom hPc (Sum.elim c.Uf c'.Uf) =
        S.hatModelHom hPc c.Uf ≫
          S.SB.incl (S.baseFam c.Uf) (S.baseFam (Sum.elim c.Uf c'.Uf)) Sum.inl rfl ∧
      S.hatInclRight hPc c.Uf c'.Uf ≫ S.hatModelHom hPc (Sum.elim c.Uf c'.Uf) =
        S.hatModelHom hPc c'.Uf ≫
          S.SB.incl (S.baseFam c'.Uf) (S.baseFam (Sum.elim c.Uf c'.Uf)) Sum.inr rfl ∧
      (S.hatModelFunctor c.Uf hPc).IsProperCovering ∧
      (S.hatModelFunctor c'.Uf hPc).IsProperCovering ∧
      (S.hatModelFunctor (Sum.elim c.Uf c'.Uf) hPc).IsProperCovering ∧
      (S.hatFunctor (Sum.elim c.Uf c'.Uf) hPc).comp
          (S.hatInclLeft hPc c.Uf c'.Uf).toGroupoidFunctor = S.hatFunctor c.Uf hPc ∧
      (S.hatFunctor (Sum.elim c.Uf c'.Uf) hPc).comp
          (S.hatInclRight hPc c.Uf c'.Uf).toGroupoidFunctor = S.hatFunctor c'.Uf hPc :=
  ⟨S.isEquivalence_hatIncl hPc rfl c.cover, S.isEquivalence_hatIncl hPc rfl c'.cover,
    S.SB.isEquivalence_incl rfl c.cover, S.SB.isEquivalence_incl rfl c'.cover,
    S.hatIncl_comp_hatModel hPc rfl, S.hatIncl_comp_hatModel hPc rfl,
    S.hatModelFunctor_isProperCovering c.Uf hPc, S.hatModelFunctor_isProperCovering c'.Uf hPc,
    S.hatModelFunctor_isProperCovering _ hPc, S.hatFunctor_comp_hatIncl hPc rfl,
    S.hatFunctor_comp_hatIncl hPc rfl⟩

end ProperPolyfoldCoveringStructure

end Polyfold
