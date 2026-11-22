import Polyfold.Chapter17.ModelEquivalence
import Polyfold.Chapter10.LocalizationUniversal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 755–761): the comparison of the ep-groupoids `X_Ψ` of two covering sets of
uniformizers, **Theorem 17.1.18**, **Remark 17.1.19**, **Definitions 17.1.20, 17.1.21** and
**Theorem 17.1.27**.  Numbers and pages are the 2021 text's.

# Comparing the models `X_Ψ`

## The text, paraphrased

(p. 755) For covering sets `Ψ`, `Ψ'` the disjoint union `Ψ'' = Ψ ⊔ Ψ'` is a covering set, with
inclusion functors `A : X_Ψ → X_Ψ''` and `A' : X_Ψ' → X_Ψ''`; they are sc-smooth equivalences
and `Γ_Ψ = Γ_Ψ'' ∘ A`, `Γ_Ψ' = Γ_Ψ'' ∘ A'`.  The weak fibred product of `X_Ψ → X_Ψ'' ← X_Ψ'`
gives the diagram `d : X_Ψ ←π₁ X_Ψ ×_X_Ψ'' X_Ψ' →π₂ X_Ψ'` (17.15) and the generalized
isomorphism `f_{Ψ,Ψ'} = [d]`, with `|Γ_Ψ'| ∘ |[d]| = |Γ_Ψ|`.
(Theorem 17.1.18, p. 756) `f_{Ψ,Ψ'}` is a generalized isomorphism, `f_{Ψ,Ψ} = 1`,
`f_{Ψ',Ψ''} ∘ f_{Ψ,Ψ'} = f_{Ψ,Ψ''}` and `|Γ_Ψ'| ∘ |f_{Ψ,Ψ'}| = |Γ_Ψ|`; `|f_{Ψ,Ψ'}|` is a
homeomorphism.
(Remark 17.1.19, p. 757) For a representative `X_Ψ ←F A →G X_Ψ'` of `f` and `x ∈ X_Ψ` there are
`a ∈ A` and `φ : F(a) → x`, and `Γ_Ψ(x)` is isomorphic to `Γ_Ψ'(G(a))`.
(Theorem 17.1.27, pp. 759–761) `τ(q_λ, (q_λ, φ'', q_μ'), q_μ') = φ''` (17.19) is a natural
transformation `Γ ∘ π₁ → Γ' ∘ π₂`; the objects of the weak fibred product are identified with
`⊔_{λ, μ'} M(Ψ_λ, Ψ_μ')` (17.18).

## What is formalized

* `modelMap Φ σ : X_{Φ ∘ σ} → X_Φ` (reindexing along `σ : κ → ι`), `incl Ψ Φ σ h` (the same for
  `Φ ∘ σ = Ψ`), `incl_comp`, `incl_id`, `modelFunctor_comp_incl` (`Γ_Φ ∘ incl = Γ_Ψ`),
  `isEquivalence_incl` (an equivalence when `Ψ` covers).
* The inclusions `inclLeft = A`, `inclRight = A'` into `X_{Ψ ⊔ Ψ'}` (p. 755),
  `isEquivalence_inclLeft`, `isEquivalence_inclRight`, `modelFunctor_comp_inclLeft`,
  `modelFunctor_comp_inclRight`.
* `compareDiagram` (17.15) and `compare Ψ Ψ' = [d]`; the characterization
  **`compare_comp_incl`**: for every family `Φ` containing `Ψ` and `Ψ'`,
  `i(Ψ' → Φ) ∘ f_{Ψ,Ψ'} = i(Ψ → Φ)` in `EP(E⁻¹)` (`i` the localization functor), so
  `f_{Ψ,Ψ'} = i(Ψ' → Φ)⁻¹ ∘ i(Ψ → Φ)` whenever `Ψ'` covers.
* For covering families: `comparison c c'`, `comparison_self`, `comparison_comp`,
  `isGeneralizedIso_comparison`, `orbitMap_comparison`, `isHomeomorph_orbitMap_comparison` and
  **`theorem_17_1_18`**; **`remark_17_1_19`**.
* **`theorem_17_1_27`**: `canonicalNatTrans`, a natural transformation of the functors
  `Γ ∘ π₁`, `Γ' ∘ π₂` (equivalences of categories) with `τ(p) = φ''`; and
  `fibredProductObjEquiv` (17.18), `canonicalNatTrans_app_eq`.
* **Definition 17.1.20**: `CoveringCategory` (`COV_C`, Mathlib's codiscrete category on the
  covering families), `IsConnectedSimpleSystem`, `definition_17_1_20`.
* **Definition 17.1.21**: `coveringEmbedding : COV_C ⥤ EP(E⁻¹)`, `definition_17_1_21`.

## Readings

* `Ψ ⊔ Ψ'` is the family indexed by the disjoint union `ι ⊕ ι'` (`Sum.elim Ψ Ψ'`); for `Ψ = Ψ'`
  it contains every uniformizer twice, which the text's `Ψ ⊔_Ψ Ψ'` presumably also intends.
* "`f_{Ψ,Ψ} = 1_{X_Ψ}`" and the cocycle identity are equalities in `EP(E⁻¹)` (Definition
  10.3.12); "`f' ∘ f`" is Mathlib's `f ≫ f'`.
* `C` carries no M-polyfold structure, so the natural transformation `τ` of Theorem 17.1.27 is one
  of functors of categories (Mathlib's `NatTrans` between the functors of the Mathlib bridges
  `GroupoidStr.Ob`); `Γ ∘ π₁` and `Γ' ∘ π₂` are equivalences of categories.
* The objects of `EP(E⁻¹)` are written `i(X_Ψ)` (`localizationFunctor.obj`), which is `X_Ψ`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

universe u

namespace Polyfold

open EPLocalization EPLocalization.EPLoc WeakFibredProduct

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction)

/-! ### Reindexing functors -/

section Reindex

variable {ι κ μ : Type u}

/-- **The reindexing functor `X_{Φ ∘ σ} → X_Φ`** along `σ : κ → ι`: `q_k ↦ q_{σ(k)}`,
`(q_k, φ, q_l) ↦ (q_{σ(k)}, φ, q_{σ(l)})`. -/
def modelMap (Φ : ι → S.Unif) (σ : κ → ι) : EpFunctor (S.modelEP (Φ ∘ σ)).X (S.modelEP Φ).X where
  obj := Sigma.map σ fun _ q => q
  mor := Sigma.map (Prod.map σ σ) fun _ a => a
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp φ ψ h := by
    obtain ⟨⟨j', k⟩, a⟩ := φ
    obtain ⟨⟨i, j⟩, b⟩ := ψ
    have hc : C.toGroupoidStr.src a.mor = C.toGroupoidStr.tgt b.mor := by
      rw [a.src_mor, b.tgt_mor]
      exact congrArg (S.modelObjMap (Φ ∘ σ)) h
    have e₁ := modelGroupoid_comp_of (Ψ := Φ ∘ σ) a b hc
    have e₂ := modelGroupoid_comp_of (Ψ := Φ) (i := σ i) (j := σ j) (j' := σ j') (k := σ k) a b hc
    change Sigma.map (Prod.map σ σ) (fun _ a => a)
        ((S.modelGroupoid (Φ ∘ σ)).comp ⟨(j', k), a⟩ ⟨(i, j), b⟩) =
      (S.modelGroupoid Φ).comp ⟨(σ j', σ k), a⟩ ⟨(σ i, σ j), b⟩
    rw [e₁, e₂]
    rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_sigmaMap _ fun _ => MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := MPolyfold.isScSmoothMap_sigmaMap _ fun _ => MPolyfold.isScSmoothMap_id

@[simp] theorem modelMap_obj (Φ : ι → S.Unif) (σ : κ → ι) (x : S.ModelObj (Φ ∘ σ)) :
    (S.modelMap Φ σ).obj x = ⟨σ x.1, x.2⟩ := rfl

@[simp] theorem modelMap_mor (Φ : ι → S.Unif) (σ : κ → ι) (φ : S.ModelMor (Φ ∘ σ)) :
    (S.modelMap Φ σ).mor φ = ⟨(σ φ.1.1, σ φ.1.2), φ.2⟩ := rfl

/-- `Γ_Φ ∘ (X_{Φ ∘ σ} → X_Φ) = Γ_{Φ ∘ σ}`. -/
theorem modelFunctor_comp_modelMap (Φ : ι → S.Unif) (σ : κ → ι) :
    (S.modelFunctor Φ).comp (S.modelMap Φ σ).toGroupoidFunctor = S.modelFunctor (Φ ∘ σ) := rfl

variable {S} in
/-- A family containing a covering family covers. -/
theorem IsCoveringFamily.of_comp {Φ : ι → S.Unif} {σ : κ → ι}
    (h : S.IsCoveringFamily (Φ ∘ σ)) : S.IsCoveringFamily Φ :=
  eq_univ_of_forall fun z => by
    obtain ⟨k, hk⟩ := mem_iUnion.1 (h.symm ▸ mem_univ z : z ∈ ⋃ k, ((Φ ∘ σ) k).1.footprint)
    exact mem_iUnion.2 ⟨σ k, hk⟩

/-- The reindexing functor is an equivalence if `Φ ∘ σ` covers: `Γ_Φ` and `Γ_Φ ∘ modelMap`
are equivalences of categories (Lemma 17.1.15), and on objects it is the identity of every
`O_k`. -/
theorem isEquivalence_modelMap {Φ : ι → S.Unif} {σ : κ → ι}
    (h : S.IsCoveringFamily (Φ ∘ σ)) : (S.modelMap Φ σ).IsEquivalence := by
  have := (lemma_17_1_15_of_isCovering h.of_comp).1
  have : ((S.modelMap Φ σ).toFunctor ⋙ (S.modelFunctor Φ).toFunctor).IsEquivalence :=
    (lemma_17_1_15_of_isCovering h).1
  exact EpFunctor.lemma_10_1_2 _
    (Functor.isEquivalence_of_comp_right _ (S.modelFunctor Φ).toFunctor)
    (by
      change (MPolyfold.sigma fun k => ((Φ ∘ σ) k).1.P).IsLocalScDiffeo
        (MPolyfold.sigma fun i => (Φ i).1.P) (Sigma.map σ fun _ q => q)
      exact MPolyfold.isLocalScDiffeo_sigmaMap _ fun _ => MPolyfold.isLocalScDiffeo_id)

/-- **The inclusion `X_Ψ → X_Φ`** of a family `Ψ = Φ ∘ σ` (the inclusion functors of p. 755). -/
def incl (Ψ : κ → S.Unif) (Φ : ι → S.Unif) (σ : κ → ι) (h : Φ ∘ σ = Ψ) :
    S.modelEP Ψ ⟶ S.modelEP Φ :=
  eqToHom (congrArg (fun Θ : κ → S.Unif => S.modelEP Θ) h.symm) ≫ S.modelMap Φ σ

theorem incl_rfl (Φ : ι → S.Unif) (σ : κ → ι) : S.incl (Φ ∘ σ) Φ σ rfl = S.modelMap Φ σ := by
  rw [incl, eqToHom_refl, Category.id_comp]

/-- `incl` on objects. -/
theorem incl_obj {Ψ : κ → S.Unif} {Φ : ι → S.Unif} {σ : κ → ι} (h : Φ ∘ σ = Ψ)
    (x : S.ModelObj Ψ) : (S.modelFunctor Φ).obj ((S.incl Ψ Φ σ h).obj x) =
      (S.modelFunctor Ψ).obj x := by
  subst h
  rw [incl_rfl]
  rfl

/-- **`Γ_Φ ∘ incl = Γ_Ψ`** (p. 756: `Γ_Ψ = Γ_Ψ'' ∘ A`). -/
theorem modelFunctor_comp_incl {Ψ : κ → S.Unif} {Φ : ι → S.Unif} {σ : κ → ι} (h : Φ ∘ σ = Ψ) :
    (S.modelFunctor Φ).comp (S.incl Ψ Φ σ h).toGroupoidFunctor = S.modelFunctor Ψ := by
  subst h
  rw [incl_rfl]
  rfl

/-- **The inclusion of a covering family is an sc-smooth equivalence** (p. 756). -/
theorem isEquivalence_incl {Ψ : κ → S.Unif} {Φ : ι → S.Unif} {σ : κ → ι} (h : Φ ∘ σ = Ψ)
    (hΨ : S.IsCoveringFamily Ψ) : (S.incl Ψ Φ σ h).IsEquivalence := by
  subst h
  rw [incl_rfl]
  exact S.isEquivalence_modelMap hΨ

/-- Inclusions compose. -/
theorem incl_comp {Ψ : κ → S.Unif} {Φ : ι → S.Unif} {Θ : μ → S.Unif} {σ : κ → ι}
    {τ : ι → μ} {ρ : κ → μ} (h₁ : Φ ∘ σ = Ψ) (h₂ : Θ ∘ τ = Φ) (h₃ : Θ ∘ ρ = Ψ)
    (hρ : τ ∘ σ = ρ) : S.incl Ψ Φ σ h₁ ≫ S.incl Φ Θ τ h₂ = S.incl Ψ Θ ρ h₃ := by
  subst hρ h₂ h₁
  rw [incl_rfl, incl_rfl, show S.incl ((Θ ∘ τ) ∘ σ) Θ (τ ∘ σ) h₃ = S.modelMap Θ (τ ∘ σ) from
    S.incl_rfl Θ (τ ∘ σ)]
  rfl

/-- The inclusion of a family into itself is the identity. -/
theorem incl_id (Ψ : κ → S.Unif) : S.incl Ψ Ψ id rfl = 𝟙 (S.modelEP Ψ) := by
  change S.incl (Ψ ∘ id) Ψ id rfl = _
  rw [incl_rfl]
  rfl

end Reindex

/-! ### The inclusions `A`, `A'` (p. 755) -/

section Union

variable {ι ι' : Type u} (Ψ : ι → S.Unif) (Ψ' : ι' → S.Unif)

/-- **`A : X_Ψ → X_Ψ''`**, `Ψ'' = Ψ ⊔ Ψ'` (p. 755). -/
abbrev inclLeft : S.modelEP Ψ ⟶ S.modelEP (Sum.elim Ψ Ψ') :=
  S.incl Ψ (Sum.elim Ψ Ψ') Sum.inl rfl

/-- **`A' : X_Ψ' → X_Ψ''`** (p. 755). -/
abbrev inclRight : S.modelEP Ψ' ⟶ S.modelEP (Sum.elim Ψ Ψ') :=
  S.incl Ψ' (Sum.elim Ψ Ψ') Sum.inr rfl

variable {Ψ Ψ'}

/-- `A` is an sc-smooth equivalence (p. 756). -/
theorem isEquivalence_inclLeft (hΨ : S.IsCoveringFamily Ψ) :
    (S.inclLeft Ψ Ψ').IsEquivalence :=
  S.isEquivalence_incl rfl hΨ

/-- `A'` is an sc-smooth equivalence (p. 756). -/
theorem isEquivalence_inclRight (hΨ' : S.IsCoveringFamily Ψ') :
    (S.inclRight Ψ Ψ').IsEquivalence :=
  S.isEquivalence_incl rfl hΨ'

variable (Ψ Ψ')

/-- `Γ_Ψ = Γ_Ψ'' ∘ A` (p. 756). -/
theorem modelFunctor_comp_inclLeft :
    (S.modelFunctor (Sum.elim Ψ Ψ')).comp (S.inclLeft Ψ Ψ').toGroupoidFunctor =
      S.modelFunctor Ψ :=
  S.modelFunctor_comp_incl rfl

/-- `Γ_Ψ' = Γ_Ψ'' ∘ A'` (p. 756). -/
theorem modelFunctor_comp_inclRight :
    (S.modelFunctor (Sum.elim Ψ Ψ')).comp (S.inclRight Ψ Ψ').toGroupoidFunctor =
      S.modelFunctor Ψ' :=
  S.modelFunctor_comp_incl rfl

variable {Ψ Ψ'}

/-- The weak fibred product of `A` and `A'` is defined (`A'` is an equivalence). -/
theorem admissible_incl (hΨ' : S.IsCoveringFamily Ψ') :
    Admissible (S.inclLeft Ψ Ψ') (S.inclRight Ψ Ψ') :=
  .of_isEquivalence_right (S.isEquivalence_inclRight hΨ')

variable (Ψ Ψ')

/-- **The weak fibred product `X_Ψ ×_{X_Ψ''} X_Ψ'`** (p. 756). -/
abbrev modelFibredProduct (hΨ' : S.IsCoveringFamily Ψ') : EP.{u} :=
  wfp (S.inclLeft Ψ Ψ') (S.inclRight Ψ Ψ') (S.admissible_incl hΨ')

/-- `π₁ : X_Ψ ×_{X_Ψ''} X_Ψ' → X_Ψ`. -/
abbrev modelProjLeft (hΨ' : S.IsCoveringFamily Ψ') :
    EpFunctor (S.modelFibredProduct Ψ Ψ' hΨ').X (S.modelEP Ψ).X :=
  projLeft (S.inclLeft Ψ Ψ') (S.inclRight Ψ Ψ') (S.admissible_incl hΨ')

/-- `π₂ : X_Ψ ×_{X_Ψ''} X_Ψ' → X_Ψ'`. -/
abbrev modelProjRight (hΨ' : S.IsCoveringFamily Ψ') :
    EpFunctor (S.modelFibredProduct Ψ Ψ' hΨ').X (S.modelEP Ψ').X :=
  projRight (S.inclLeft Ψ Ψ') (S.inclRight Ψ Ψ') (S.admissible_incl hΨ')

/-- **The diagram (17.15)** `d : X_Ψ ←π₁ X_Ψ ×_{X_Ψ''} X_Ψ' →π₂ X_Ψ'`. -/
def compareDiagram (hΨ' : S.IsCoveringFamily Ψ') : Diagram (S.modelEP Ψ) (S.modelEP Ψ') where
  A := S.modelFibredProduct Ψ Ψ' hΨ'
  F := S.modelProjLeft Ψ Ψ' hΨ'
  isEquivalence_F := isEquivalence_projLeft (S.isEquivalence_inclRight hΨ') _
  Φ := S.modelProjRight Ψ Ψ' hΨ'

/-- **The generalized map `f_{Ψ,Ψ'} = [d] : X_Ψ → X_Ψ'`** of (17.14), (17.15). -/
def compare (hΨ' : S.IsCoveringFamily Ψ') :
    localizationFunctor.obj (S.modelEP Ψ) ⟶ localizationFunctor.obj (S.modelEP Ψ') :=
  EPLoc.homMk (S.compareDiagram Ψ Ψ' hΨ')

variable {Ψ Ψ'} in
/-- **`f_{Ψ,Ψ'}` through any family containing `Ψ` and `Ψ'`**: if `Ψ = Φ ∘ σ` and `Ψ' = Φ ∘ σ'`,
then `i(Ψ' → Φ) ∘ f_{Ψ,Ψ'} = i(Ψ → Φ)` in `EP(E⁻¹)`.  The square `A ∘ π₁ ≃ A' ∘ π₂` of the weak
fibred product, followed by `X_Ψ'' → X_Φ`, gives this. -/
theorem compare_comp_incl {κ : Type u} (Φ : κ → S.Unif) {σ : ι → κ} {σ' : ι' → κ}
    (h : Φ ∘ σ = Ψ) (h' : Φ ∘ σ' = Ψ') (hΨ' : S.IsCoveringFamily Ψ') :
    S.compare Ψ Ψ' hΨ' ≫ localizationFunctor.map (S.incl Ψ' Φ σ' h') =
      localizationFunctor.map (S.incl Ψ Φ σ h) := by
  have hK : Φ ∘ Sum.elim σ σ' = Sum.elim Ψ Ψ' := by
    funext x
    cases x with
    | inl a => exact congrFun h a
    | inr a => exact congrFun h' a
  have hA : S.inclLeft Ψ Ψ' ≫ S.incl (Sum.elim Ψ Ψ') Φ (Sum.elim σ σ') hK = S.incl Ψ Φ σ h :=
    S.incl_comp _ _ _ rfl
  have hA' : S.inclRight Ψ Ψ' ≫ S.incl (Sum.elim Ψ Ψ') Φ (Sum.elim σ σ') hK =
      S.incl Ψ' Φ σ' h' :=
    S.incl_comp _ _ _ rfl
  let dF : S.modelFibredProduct Ψ Ψ' hΨ' ⟶ S.modelEP Ψ := S.modelProjLeft Ψ Ψ' hΨ'
  let dΦ : S.modelFibredProduct Ψ Ψ' hΨ' ⟶ S.modelEP Ψ' := S.modelProjRight Ψ Ψ' hΨ'
  have hπ : EP.equivalences dF := isEquivalence_projLeft (S.isEquivalence_inclRight hΨ') _
  have : IsIso (localizationFunctor.map dF) := isInvertedBy_localizationFunctor dF hπ
  have hnat : localizationFunctor.map (dF ≫ S.inclLeft Ψ Ψ') =
      localizationFunctor.map (dΦ ≫ S.inclRight Ψ Ψ') :=
    map_eq_of_naturallyEquivalent localizationFunctor isInvertedBy_localizationFunctor
      (naturallyEquivalent (S.admissible_incl hΨ'))
  have key : localizationFunctor.map dF ≫ localizationFunctor.map (S.incl Ψ Φ σ h) =
      localizationFunctor.map dΦ ≫ localizationFunctor.map (S.incl Ψ' Φ σ' h') := by
    rw [← hA, ← hA', ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← Category.assoc, ← Category.assoc, CategoryTheory.Functor.map_comp, hnat,
      ← CategoryTheory.Functor.map_comp]
  have e : S.compare Ψ Ψ' hΨ' = inv (localizationFunctor.map dF) ≫ localizationFunctor.map dΦ :=
    EPLoc.homMk_eq _
  rw [e, Category.assoc, IsIso.inv_comp_eq, key]

end Union

/-! ### Theorem 17.1.18 -/

/-- **`f_{Ψ,Ψ'} : X_Ψ → X_Ψ'`** for covering families `Ψ`, `Ψ'` (2021 (17.14), Theorem 17.1.18). -/
def comparison (c c' : S.CoveringFamily) :
    localizationFunctor.obj (S.modelEP c.Ψ) ⟶ localizationFunctor.obj (S.modelEP c'.Ψ) :=
  S.compare c.Ψ c'.Ψ c'.cover

theorem comparison_comp_incl (c c' : S.CoveringFamily) {κ : Type u} (Φ : κ → S.Unif)
    {σ : c.ι → κ} {σ' : c'.ι → κ} (h : Φ ∘ σ = c.Ψ) (h' : Φ ∘ σ' = c'.Ψ) :
    S.comparison c c' ≫ localizationFunctor.map (S.incl c'.Ψ Φ σ' h') =
      localizationFunctor.map (S.incl c.Ψ Φ σ h) :=
  S.compare_comp_incl Φ h h' c'.cover

/-- **`f_{Ψ,Ψ} = 1_{X_Ψ}`** (Theorem 17.1.18). -/
theorem comparison_self (c : S.CoveringFamily) : S.comparison c c = 𝟙 _ := by
  have := S.comparison_comp_incl c c c.Ψ (σ := id) (σ' := id) rfl rfl
  rwa [incl_id, CategoryTheory.Functor.map_id, Category.comp_id] at this

/-- **The cocycle identity** `f_{Ψ',Ψ''} ∘ f_{Ψ,Ψ'} = f_{Ψ,Ψ''}` (Theorem 17.1.18). -/
theorem comparison_comp (c c' c'' : S.CoveringFamily) :
    S.comparison c c' ≫ S.comparison c' c'' = S.comparison c c'' := by
  let Φ := Sum.elim c.Ψ (Sum.elim c'.Ψ c''.Ψ)
  have e₁ := S.comparison_comp_incl c c' Φ (σ := Sum.inl) (σ' := Sum.inr ∘ Sum.inl) rfl rfl
  have e₂ := S.comparison_comp_incl c' c'' Φ (σ := Sum.inr ∘ Sum.inl)
    (σ' := Sum.inr ∘ Sum.inr) rfl rfl
  have e₃ := S.comparison_comp_incl c c'' Φ (σ := Sum.inl) (σ' := Sum.inr ∘ Sum.inr) rfl rfl
  have := isInvertedBy_localizationFunctor _
    (S.isEquivalence_incl (Ψ := c''.Ψ) (Φ := Φ) (σ := Sum.inr ∘ Sum.inr) rfl c''.cover)
  refine (cancel_mono (localizationFunctor.map (S.incl c''.Ψ Φ (Sum.inr ∘ Sum.inr) rfl))).1 ?_
  rw [Category.assoc, e₂, e₁, e₃]

/-- **`f_{Ψ,Ψ'}` is a generalized isomorphism** (Theorem 17.1.18): `π₂` is an equivalence, since
`A` is one (Theorem 10.2.2), and Theorem 10.3.10 applies. -/
theorem isGeneralizedIso_comparison (c c' : S.CoveringFamily) :
    IsGeneralizedIso (S.comparison c c') :=
  (theorem_10_3_10 (S.compareDiagram c.Ψ c'.Ψ c'.cover)).1.2
    (isEquivalence_projRight (S.isEquivalence_inclLeft c.cover) _)

/-- **`|Γ_Ψ'| ∘ |f_{Ψ,Ψ'}| = |Γ_Ψ|`** (Theorem 17.1.18): on an object `(x, φ'', z)` of the weak
fibred product, `Γ_Ψ''(φ'') : Γ_Ψ(x) → Γ_Ψ'(z)`. -/
theorem orbitMap_comparison (c c' : S.CoveringFamily) :
    (S.modelFunctor c'.Ψ).orbitMap ∘ EPLoc.orbitMap (S.comparison c c') =
      (S.modelFunctor c.Ψ).orbitMap := by
  funext q
  set d := S.compareDiagram c.Ψ c'.Ψ c'.cover
  obtain ⟨r, hr⟩ := d.isEquivalence_F.isHomeomorph_orbitMap.bijective.2 q
  change (S.modelFunctor c'.Ψ).orbitMap (d.orbitMap q) = (S.modelFunctor c.Ψ).orbitMap q
  rw [Diagram.orbitMap_eq_of hr, ← hr]
  induction r using Quotient.inductionOn with
  | h p =>
    change C.toGroupoidStr.π ((S.modelFunctor c'.Ψ).obj p.z) =
      C.toGroupoidStr.π ((S.modelFunctor c.Ψ).obj p.x)
    refine ((GroupoidStr.π_eq_π_iff _).2
      ⟨(S.modelFunctor (Sum.elim c.Ψ c'.Ψ)).mor p.φ, ?_, ?_⟩).symm
    · rw [GroupoidFunctor.src_mor, p.src_φ]
      exact S.incl_obj _ _
    · rw [GroupoidFunctor.tgt_mor, p.tgt_φ]
      exact S.incl_obj _ _

/-- **`|f_{Ψ,Ψ'}| : |X_Ψ| → |X_Ψ'|` is a homeomorphism**, `|Γ_Ψ'|⁻¹ ∘ |Γ_Ψ|`
(Theorem 17.1.18). -/
theorem isHomeomorph_orbitMap_comparison (c c' : S.CoveringFamily) :
    IsHomeomorph (EPLoc.orbitMap (S.comparison c c')) := by
  have he : EPLoc.orbitMap (S.comparison c c') =
      (S.modelOrbitHomeomorph c').symm ∘ S.modelOrbitHomeomorph c := by
    funext q
    refine (S.modelOrbitHomeomorph c').injective ?_
    change (S.modelFunctor c'.Ψ).orbitMap (EPLoc.orbitMap (S.comparison c c') q) =
      S.modelOrbitHomeomorph c' ((S.modelOrbitHomeomorph c').symm (S.modelOrbitHomeomorph c q))
    rw [Homeomorph.apply_symm_apply]
    exact congrFun (S.orbitMap_comparison c c') q
  rw [he]
  exact ((S.modelOrbitHomeomorph c).trans (S.modelOrbitHomeomorph c').symm).isHomeomorph

/-- **2021 Theorem 17.1.18, p. 756**: for covering sets `Ψ`, `Ψ'`, `Ψ''` of uniformizers,
`f_{Ψ,Ψ'} = [d] : X_Ψ → X_Ψ'` of (17.15) is a generalized isomorphism; `f_{Ψ,Ψ} = 1_{X_Ψ}`;
`f_{Ψ',Ψ''} ∘ f_{Ψ,Ψ'} = f_{Ψ,Ψ''}`; `|Γ_Ψ'| ∘ |f_{Ψ,Ψ'}| = |Γ_Ψ|`; and `|f_{Ψ,Ψ'}|` is a
homeomorphism. -/
theorem theorem_17_1_18 (c c' c'' : S.CoveringFamily) :
    IsGeneralizedIso (S.comparison c c') ∧ S.comparison c c = 𝟙 _ ∧
      S.comparison c c' ≫ S.comparison c' c'' = S.comparison c c'' ∧
      (S.modelFunctor c'.Ψ).orbitMap ∘ EPLoc.orbitMap (S.comparison c c') =
        (S.modelFunctor c.Ψ).orbitMap ∧
      IsHomeomorph (EPLoc.orbitMap (S.comparison c c')) :=
  ⟨S.isGeneralizedIso_comparison c c', S.comparison_self c, S.comparison_comp c c' c'',
    S.orbitMap_comparison c c', S.isHomeomorph_orbitMap_comparison c c'⟩

/-! ### Remark 17.1.19 -/

/-- **2021 Remark 17.1.19, p. 757**: for any representative `X_Ψ ←F A →G X_Ψ'` of
`f_{Ψ,Ψ'}` and any object `x` of `X_Ψ`, there are an object `a` of `A` and a morphism
`φ : F(a) → x`, and `Γ_Ψ(x)` and `Γ_Ψ'(G(a))` are isomorphic objects of `C`. -/
theorem remark_17_1_19 (c c' : S.CoveringFamily) (d : Diagram (S.modelEP c.Ψ) (S.modelEP c'.Ψ))
    (hd : EPLoc.homMk d = S.comparison c c') (x : S.ModelObj c.Ψ) :
    ∃ (a : d.A.Obj) (φ : S.ModelMor c.Ψ), (S.modelEP c.Ψ).X.src φ = d.F.obj a ∧
      (S.modelEP c.Ψ).X.tgt φ = x ∧
      C.toGroupoidStr.Isomorphic ((S.modelFunctor c.Ψ).obj x)
        ((S.modelFunctor c'.Ψ).obj (d.Φ.obj a)) := by
  obtain ⟨r, hr⟩ := d.isEquivalence_F.isHomeomorph_orbitMap.bijective.2 ((S.modelEP c.Ψ).X.π x)
  induction r using Quotient.inductionOn with
  | h a =>
    obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hr
    refine ⟨a, φ, hs, ht, (GroupoidStr.π_eq_π_iff _).1 ?_⟩
    have h2 : EPLoc.orbitMap (S.comparison c c') = d.orbitMap := (congrArg EPLoc.orbitMap hd).symm
    have h1 : (S.modelFunctor c'.Ψ).orbitMap (d.orbitMap ((S.modelEP c.Ψ).X.π x)) =
        (S.modelFunctor c.Ψ).orbitMap ((S.modelEP c.Ψ).X.π x) := by
      rw [← h2]
      exact congrFun (S.orbitMap_comparison c c') ((S.modelEP c.Ψ).X.π x)
    rw [Diagram.orbitMap_eq_of hr] at h1
    exact h1.symm

/-! ### Theorem 17.1.27 and (17.18) -/

section CanonicalNatTrans

variable {ι ι' : Type u} (Ψ : ι → S.Unif) (Ψ' : ι' → S.Unif) (hΨ' : S.IsCoveringFamily Ψ')

/-- `Γ ∘ π₁ : X ×_{X''} X' → C`. -/
abbrev modelFunctorLeft : GroupoidFunctor (S.modelFibredProduct Ψ Ψ' hΨ').X.toGroupoidStr
    C.toGroupoidStr :=
  (S.modelFunctor Ψ).comp (S.modelProjLeft Ψ Ψ' hΨ').toGroupoidFunctor

/-- `Γ' ∘ π₂ : X ×_{X''} X' → C`. -/
abbrev modelFunctorRight : GroupoidFunctor (S.modelFibredProduct Ψ Ψ' hΨ').X.toGroupoidStr
    C.toGroupoidStr :=
  (S.modelFunctor Ψ').comp (S.modelProjRight Ψ Ψ' hΨ').toGroupoidFunctor

theorem src_canonical (p : (S.modelFibredProduct Ψ Ψ' hΨ').Obj) :
    C.toGroupoidStr.src ((S.modelFunctor (Sum.elim Ψ Ψ')).mor p.φ) =
      (S.modelFunctorLeft Ψ Ψ' hΨ').obj p := by
  rw [GroupoidFunctor.src_mor, p.src_φ]
  exact S.incl_obj _ _

theorem tgt_canonical (p : (S.modelFibredProduct Ψ Ψ' hΨ').Obj) :
    C.toGroupoidStr.tgt ((S.modelFunctor (Sum.elim Ψ Ψ')).mor p.φ) =
      (S.modelFunctorRight Ψ Ψ' hΨ').obj p := by
  rw [GroupoidFunctor.tgt_mor, p.tgt_φ]
  exact S.incl_obj _ _

/-- **The canonical natural transformation `τ : Γ ∘ π₁ → Γ' ∘ π₂`** (2021 (17.19)):
`τ(q_λ, (q_λ, φ'', q_μ'), q_μ') = φ''`, i.e. `Γ_Ψ''` applied to the natural transformation
`A ∘ π₁ → A' ∘ π₂` of the weak fibred product. -/
def canonicalNatTrans :
    (S.modelFunctorLeft Ψ Ψ' hΨ').toFunctor ⟶ (S.modelFunctorRight Ψ Ψ' hΨ').toFunctor where
  app p := ⟨(S.modelFunctor (Sum.elim Ψ Ψ')).mor p.φ, S.src_canonical Ψ Ψ' hΨ' p,
    S.tgt_canonical Ψ Ψ' hΨ' p⟩
  naturality := by
    rintro p p' ⟨m, rfl, rfl⟩
    apply Subtype.ext
    have hn := (natTrans (S.inclLeft Ψ Ψ') (S.inclRight Ψ Ψ') (S.admissible_incl hΨ')).naturality m
    have e := congrArg (S.modelFunctor (Sum.elim Ψ Ψ')).mor hn
    rw [GroupoidFunctor.mor_comp _ _ _ ?h₁, GroupoidFunctor.mor_comp _ _ _ ?h₂] at e
    · exact e
    case h₁ =>
      rw [(natTrans _ _ (S.admissible_incl hΨ')).src_app]
      exact ((S.inclLeft Ψ Ψ').tgt_mor _).symm
    case h₂ =>
      rw [(natTrans _ _ (S.admissible_incl hΨ')).tgt_app]
      exact (S.inclRight Ψ Ψ').src_mor _

@[simp] theorem canonicalNatTrans_app (p : (S.modelFibredProduct Ψ Ψ' hΨ').Obj) :
    ((S.canonicalNatTrans Ψ Ψ' hΨ').app p).1 = p.φ.2.mor := rfl

variable {Ψ} in
/-- `Γ ∘ π₁` is an equivalence of categories. -/
theorem isEquivalence_modelFunctorLeft (hΨ : S.IsCoveringFamily Ψ) :
    (S.modelFunctorLeft Ψ Ψ' hΨ').toFunctor.IsEquivalence :=
  @Functor.isEquivalence_trans _ _ _ _ _ _ _ _
    (isEquivalence_projLeft (S.isEquivalence_inclRight (Ψ := Ψ) hΨ')
      (S.admissible_incl (Ψ := Ψ) hΨ')).isEquivalence_toFunctor
    (lemma_17_1_15_of_isCovering hΨ).1

variable {Ψ} in
/-- `Γ' ∘ π₂` is an equivalence of categories. -/
theorem isEquivalence_modelFunctorRight (hΨ : S.IsCoveringFamily Ψ) :
    (S.modelFunctorRight Ψ Ψ' hΨ').toFunctor.IsEquivalence :=
  @Functor.isEquivalence_trans _ _ _ _ _ _ _ _
    (isEquivalence_projRight (S.isEquivalence_inclLeft (Ψ' := Ψ') hΨ)
      (S.admissible_incl (Ψ := Ψ) hΨ')).isEquivalence_toFunctor
    (lemma_17_1_15_of_isCovering hΨ').1

/-- **2021 Theorem 17.1.27, pp. 759–761**: for covering sets `Ψ`, `Ψ'` with `Ψ'' = Ψ ⊔ Ψ'`, the
functors `Γ ∘ π₁` and `Γ' ∘ π₂ : X ×_{X''} X' → C` are equivalences of categories and
`τ(q_λ, (q_λ, φ'', q_μ'), q_μ') = φ''` (17.19) is a natural transformation `Γ ∘ π₁ → Γ' ∘ π₂`
(a natural isomorphism, `C` being a groupoid). -/
theorem theorem_17_1_27 (c c' : S.CoveringFamily) :
    (S.modelFunctorLeft c.Ψ c'.Ψ c'.cover).toFunctor.IsEquivalence ∧
      (S.modelFunctorRight c.Ψ c'.Ψ c'.cover).toFunctor.IsEquivalence ∧
      ∃ τ : (S.modelFunctorLeft c.Ψ c'.Ψ c'.cover).toFunctor ⟶
          (S.modelFunctorRight c.Ψ c'.Ψ c'.cover).toFunctor,
        IsIso τ ∧ ∀ p, (τ.app p).1 = p.φ.2.mor :=
  ⟨S.isEquivalence_modelFunctorLeft c'.Ψ c'.cover c.cover,
    S.isEquivalence_modelFunctorRight c'.Ψ c'.cover c.cover,
    S.canonicalNatTrans c.Ψ c'.Ψ c'.cover, NatIso.isIso_of_isIso_app _, fun _ => rfl⟩

/-- **(17.18)**: the objects of `X ×_{X''} X'` are the elements of `⊔_{λ, μ'} M(Ψ_λ, Ψ_μ')`,
`(q_λ, (q_λ, φ'', q_μ'), q_μ') ↦ (q_λ, φ'', q_μ')`. -/
def fibredProductObjEquiv :
    (S.modelFibredProduct Ψ Ψ' hΨ').Obj ≃ Σ p : ι × ι', S.Tr (Ψ p.1) (Ψ' p.2) where
  toFun p := ⟨(p.x.1, p.z.1), ⟨p.x.2, p.φ.2.mor, p.z.2, S.src_canonical Ψ Ψ' hΨ' p,
    S.tgt_canonical Ψ Ψ' hΨ' p⟩⟩
  invFun a := Obj.mk (S.inclLeft Ψ Ψ') (S.inclRight Ψ Ψ') ⟨a.1.1, a.2.src⟩
    ⟨(Sum.inl a.1.1, Sum.inr a.1.2), a.2⟩ ⟨a.1.2, a.2.tgt⟩ rfl rfl
  left_inv p := Obj.ext rfl ((S.modelMorEquiv (Sum.elim Ψ Ψ')).injective
    (GroupoidStr.TransitionSet.ext p.src_φ.symm rfl p.tgt_φ.symm)) rfl
  right_inv _ := rfl

/-- Under (17.18), `τ` is `(q_λ, φ'', q_μ') ↦ φ''`. -/
theorem canonicalNatTrans_app_eq (p : (S.modelFibredProduct Ψ Ψ' hΨ').Obj) :
    ((S.canonicalNatTrans Ψ Ψ' hΨ').app p).1 = (S.fibredProductObjEquiv Ψ Ψ' hΨ' p).2.mor := rfl

end CanonicalNatTrans

/-! ### Definitions 17.1.20 and 17.1.21 -/

/-- **2021 Definition 17.1.20, p. 757**: the covering category `COV_C`, with the covering families
as objects and exactly one morphism `Ψ → Ψ'` for every ordered pair (Mathlib's codiscrete
category). -/
abbrev CoveringCategory : Type (u + 1) := Codiscrete S.CoveringFamily

end GCT.PolyfoldConstruction

/-- **A connected simple system** (2021 p. 757): a category with exactly one morphism between any
two objects. -/
def IsConnectedSimpleSystem (D : Type*) [Category D] : Prop :=
  ∀ X Y : D, Nonempty (Unique (X ⟶ Y))

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction)

/-- **2021 Definition 17.1.20, p. 757**: `COV_C` is a connected simple system; every morphism is
an isomorphism and the morphism `Ψ → Ψ` is the identity. -/
theorem definition_17_1_20 :
    IsConnectedSimpleSystem S.CoveringCategory ∧
      (∀ (c c' : S.CoveringCategory) (f : c ⟶ c'), IsIso f) ∧
      ∀ (c : S.CoveringCategory) (f : c ⟶ c), f = 𝟙 c :=
  ⟨fun _ _ => ⟨inferInstance⟩, fun _ _ _ => ⟨⟨(), rfl, rfl⟩⟩, fun _ _ => rfl⟩

/-- **The natural embedding `COV_C → EP(E⁻¹)`** (2021 Definition 17.1.21, p. 757): `Ψ ↦ X_Ψ`,
`(Ψ → Ψ') ↦ f_{Ψ,Ψ'}`; functoriality is Theorem 17.1.18. -/
def coveringEmbedding : S.CoveringCategory ⥤ EPLoc.{u} where
  obj c := localizationFunctor.obj (S.modelEP c.as.Ψ)
  map {c c'} _ := S.comparison c.as c'.as
  map_id c := S.comparison_self c.as
  map_comp {c c' c''} _ _ := (S.comparison_comp c.as c'.as c''.as).symm

/-- **2021 Definition 17.1.21, p. 757**: the natural embedding `COV_C → EP(E⁻¹)` takes `Ψ` to
`X_Ψ` and the morphism `Ψ → Ψ'` to the generalized isomorphism `f_{Ψ,Ψ'}`. -/
theorem definition_17_1_21 :
    (∀ c : S.CoveringCategory,
        S.coveringEmbedding.obj c = localizationFunctor.obj (S.modelEP c.as.Ψ)) ∧
      ∀ (c c' : S.CoveringCategory) (f : c ⟶ c'),
        S.coveringEmbedding.map f = S.comparison c.as c'.as ∧
          IsGeneralizedIso (S.coveringEmbedding.map f) :=
  ⟨fun _ => rfl, fun c c' _ => ⟨rfl, S.isGeneralizedIso_comparison c.as c'.as⟩⟩

end GCT.PolyfoldConstruction

end Polyfold
