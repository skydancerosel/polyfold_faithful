import Polyfold.Chapter17.BundleModel
import Polyfold.Chapter17.ModelComparison
import Polyfold.Chapter10.StrongBundleWeakFibredProduct
import Polyfold.Chapter10.StrongBundleLocalizationCategory
import Polyfold.Chapter8.BundleOrbitParacompactOne
import Polyfold.Chapter10.StrongBundleIsoConverse
import Polyfold.Chapter10.StrongBundleWeakFibredProductPullback

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.7 "Strong Bundle Structures", pp. 826–828: **the comparison of strong bundle models**
`f̄_{Ψ̄,Ψ̄'} : W_Ψ̄ → W_Ψ̄'`, the strong bundle analogue of Theorem 17.1.18, which §17.7 leaves to
the reader.  Numbers and pages are the 2021 text's.

# Comparison of strong bundle models

## The text, paraphrased

(§17.7, pp. 827–828) The transition sets `M(Ψ̄, Ψ̄')` carry strong bundle structures over
`M(Ψ, Ψ')` for which source, target, inversion, unit and multiplication are sc-smooth strong
bundle maps covering those of the base; the section ends there.  We read it as leaving to the
reader the strong bundle analogue of Theorem 17.1.18: for two families `Ψ̄`, `Ψ̄'` whose
footprints cover, the inclusions of `W_Ψ̄` and `W_Ψ̄'` into `W_{Ψ̄ ⊔ Ψ̄'}` are strong bundle
equivalences, and the weak fibred product gives a generalized strong bundle isomorphism
`W_Ψ̄ → W_Ψ̄'` covering `f_{Ψ,Ψ'}`, which is the identity for `Ψ̄ = Ψ̄'` and satisfies the
cocycle identity.

## What is formalized (namespace `Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction`)

* `bundleModelMap Φb σ : W_{Φ̄ ∘ σ} → W_Φ̄` (`Sigma.map σ id` on the total spaces, covering
  `modelMap`), `bundleIncl` (the inclusion of a family `Ψ̄ = Φ̄ ∘ σ`), `bundleIncl_comp`,
  `bundleIncl_id`, `bundleIncl_ϕ` (it covers `incl`), `bundleModelFunctor_comp_bundleIncl`
  (`Γ̄_Φ̄ ∘ incl = Γ̄_Ψ̄`), and `equivalences_bundleIncl`: **the inclusion of a family whose base
  family covers is a strong bundle equivalence** (Definition 10.4.1).
* `bundleCompareDiagram`, the diagram `W_Ψ̄ ← W_Ψ̄ ×_{W_{Ψ̄ ⊔ Ψ̄'}} W_Ψ̄' → W_Ψ̄'` from the weak
  fibred product of strong bundles (Theorem 10.2.2), `bundleCompare` its class in `SEP(F⁻¹)`,
  and `bundleCompare_comp_incl`: `i(Ψ̄' → Φ̄) ∘ f̄_{Ψ̄,Ψ̄'} = i(Ψ̄ → Φ̄)` for any `Φ̄` containing
  both families.
* For covering families (`BundleCoveringFamily`): `bundleComparison`, `bundleComparison_self`,
  `bundleComparison_comp` (the cocycle identity), `isGeneralizedIso_bundleComparison`
  (Definition 10.5.2), `isIso_bundleComparison`, `baseFunctor_map_bundleComparison`
  (`f̄_{Ψ̄,Ψ̄'}` covers `f_{Ψ,Ψ'}` of Theorem 17.1.18), `orbitMap_bundleComparison`
  (`|Γ̄_Ψ̄'| ∘ |f̄_{Ψ̄,Ψ̄'}| = |Γ̄_Ψ̄|`), `isHomeomorph_orbitMap_bundleComparison`, all packaged
  as `theorem_17_1_18_bundle`.
* Two general facts used on the way: `SEP.equivalences_of_isStrongBundleIsoOn` (a strong bundle
  functor covering an equivalence, injective on the fibres, a local strong bundle isomorphism on
  objects and reflecting `W_{0,1}` is a strong bundle equivalence) and
  `SBLocalization.SEPLoc.map_eq_of_natEquiv`, `SBLocalization.SEPLoc.map_comp_homMk`.

## Readings

* "Covering" for a family `Ψ̄` is read, as in `BundleModel.lean`, as: the base family covers `|C|`.
* The weak fibred product of Theorem 10.2.2 in its strong bundle form takes the equivalence as
  its left leg; we take `W_Ψ̄' → W_{Ψ̄ ⊔ Ψ̄'}` there, so the leg
  `W_Ψ̄ ×_{W_{Ψ̄ ⊔ Ψ̄'}} W_Ψ̄' → W_Ψ̄` of the diagram is the projection `ΠZ` and the leg to
  `W_Ψ̄'` is `ΠX`.  The class in `SEP(F⁻¹)`
  does not depend on this choice: `bundleCompare_comp_incl` characterizes it.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace SEP

open EpStrongBundle

variable {A A' : SEP.{u}}

/-- A strong bundle functor covering an equivalence, injective on the fibres, a local strong
bundle isomorphism on objects and reflecting `W_{0,1}` is a strong bundle equivalence. -/
theorem equivalences_of_isStrongBundleIsoOn (Ψ : A ⟶ A') (hψ : (Hom.ϕ Ψ).IsEquivalence)
    (hinj : FibInj Ψ)
    (hloc : ∀ x : A.Obj, ∃ (U : Set A.Obj) (U' : Set A'.Obj), x ∈ U ∧
      A.B.IsStrongBundleIsoOn A'.B (Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_obj U U')
    (hrefl : ∀ w, (Hom.Φ Ψ).obj w ∈ A'.B.oneSet → w ∈ A.B.oneSet) : equivalences Ψ := by
  have hΨ := Hom.isStrongBundleFunctor Ψ
  have hfull := full_total Ψ hψ hinj
  have heq := isEquivalence_total Ψ hψ hinj hloc
  set F := A.E.oneOrbitMap A'.E (Hom.Φ Ψ) hΨ.isStrongBundleMap_obj.mapsTo_oneSet with hF
  set Φ₁ := StrongBundle.oneRestrict A.B A'.B (Hom.Φ Ψ).obj
    hΨ.isStrongBundleMap_obj.mapsTo_oneSet with hΦ₁
  have hcF : Continuous F := continuous_oneOrbitMap (continuousOn_univ.1
    hΨ.isStrongBundleMap_obj.isScSmoothMap_one.continuousOn)
  have hinjF : Injective F := fun a b hab => by
    induction a using Quotient.inductionOn with | h a => ?_
    induction b using Quotient.inductionOn with | h b => ?_
    obtain ⟨q', hs, ht⟩ := Quotient.exact hab
    obtain ⟨q, hqs, hqt, -⟩ := (GroupoidFunctor.full_iff _).1 hfull _ _ q' hs ht
    exact Quotient.sound ⟨q, hqs, hqt⟩
  have hsurj : Surjective F := fun c => by
    induction c using Quotient.inductionOn with | h w => ?_
    obtain ⟨v, ψ, hs, ht⟩ :=
      (GroupoidFunctor.essSurj_iff _).1 heq.essSurj (A'.B.oneVal w)
    have hs' : (ψ : A'.Mor × A'.W).2 = (Hom.Φ Ψ).obj v := hs
    have ht' : A'.E.μ ψ = A'.B.oneVal w := ht
    have hv : v ∈ A.B.oneSet :=
      hrefl v (hs' ▸ A'.E.mem_oneSet_of_mor ψ (ht' ▸ A'.B.oneVal_mem w))
    exact ⟨Quotient.mk _ (A.B.oneMk v hv), Quotient.sound ⟨ψ, hs, ht⟩⟩
  have hΦ₁o : IsOpenMap Φ₁ := by
    refine MPolyfold.IsLocalScDiffeo.isOpenMap (P := A.B.toMPolyfold1)
      (Q := A'.B.toMPolyfold1) fun w => ?_
    obtain ⟨U, U', hx, hi⟩ := hloc (A.P (A.B.oneVal w))
    obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
    exact ⟨_, _, Ψ₁, hx, hΨ₁⟩
  have hopen : IsOpenMap F := by
    intro O hO
    have he : F '' O = A'.E.πOne '' (Φ₁ '' (A.E.πOne ⁻¹' O)) := by
      ext z
      constructor
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨b, rfl⟩ := A.E.surjective_πOne c
        exact ⟨Φ₁ b, ⟨b, hc, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨_, hb, rfl⟩
    rw [he]
    exact A'.E.isOpenMap_πOne _ (hΦ₁o _ (hO.preimage A.E.continuous_πOne))
  exact
    { isStrongBundleFunctor := hΨ
      isEquivalence_base := hψ
      isEquivalence := heq
      isHomeomorph_oneOrbitMap := ⟨hcF, hopen, hinjF, hsurj⟩
      isLocalStrongBundleIso_obj := hloc
      isLocalStrongBundleIso_mor := isLocalStrongBundleIso_mor_of_obj Ψ hloc }

end SEP

namespace SBLocalization.SEPLoc

variable {A A' : SEP.{u}}

/-- Naturally equivalent strong bundle functors have the same image in `SEP(F⁻¹)`. -/
theorem map_eq_of_natEquiv {F G : A ⟶ A'} (h : SEP.NatEquiv F G) :
    localizationFunctor.map F = localizationFunctor.map G :=
  homMk_eq_homMk_iff.2 (SDiagram.isRefinement_of_natEquiv (SDiagram.ofHom G) (𝟙 A)
    (SEP.equivalences.id_mem A) F (.refl _) h).equiv

/-- `i(Φ) ∘ [W ←Φ W'' →Ψ W'] = i(Ψ)`. -/
theorem map_comp_homMk (D : SDiagram A A') :
    localizationFunctor.map D.Φ ≫ homMk D = localizationFunctor.map D.Ψ := by
  refine homMk_eq_homMk_iff.2 ⟨_, SDiagram.isRefinement_comp_of_sectionLeft
    (SDiagram.ofHom D.Φ) D (𝟙 D.B) (Category.id_comp _) (SEP.equivalences.id_mem _), ?_⟩
  exact SDiagram.isRefinement_of_natEquiv (SDiagram.ofHom D.Ψ) _ _ D.Ψ
    (.of_eq (Category.id_comp _)) (.refl _)

end SBLocalization.SEPLoc

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor StrongBundleUniformizerConstruction
  StrongBundleUniformizerData PolyfoldConstruction EpStrongBundle

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S)

section Reindex

variable {ι κ μ : Type u}

/-- `Sigma.map σ id` on the total spaces. -/
abbrev bundleReindex (Φb : ι → Q.Unif) (σ : κ → ι) : Q.ModelW (Φb ∘ σ) → Q.ModelW Φb :=
  Sigma.map σ fun _ v => v

theorem isStrongBundleMap_bundleReindex (Φb : ι → Q.Unif) (σ : κ → ι) :
    (Q.modelBundle (Φb ∘ σ)).IsStrongBundleMap (Q.modelBundle Φb)
      (S.modelMap (Q.modelBase Φb) σ).obj (Q.bundleReindex Φb σ) :=
  StrongBundle.isStrongBundleMap_sigmaMap (fun k => (Φb (σ k)).1.B) (fun i => (Φb i).1.B)
    fun k => StrongBundle.IsStrongBundleMap.id (Φb (σ k)).1.B

theorem isMap_bundleReindex (Φb : ι → Q.Unif) (σ : κ → ι) :
    (Q.modelEpStrongBundle (Φb ∘ σ)).IsMap (Q.modelEpStrongBundle Φb)
      (S.modelMap (Q.modelBase Φb) σ) (Q.bundleReindex Φb σ) where
  isStrongBundleMap := Q.isStrongBundleMap_bundleReindex Φb σ
  map_μ γ w h := by
    obtain ⟨⟨k, k'⟩, a⟩ := γ
    obtain ⟨i, v⟩ := w
    change (⟨i, (Φb (σ i)).1.p v⟩ : S.ModelObj (Q.modelBase (Φb ∘ σ))) = ⟨k, a.src⟩ at h
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 h
    rfl

/-- **The reindexing strong bundle functor `W_{Φ̄ ∘ σ} → W_Φ̄`** covering `X_{Φ ∘ σ} → X_Φ`:
`k_k ↦ k_{σ(k)}`, `((q_k, φ, q_l), k) ↦ ((q_{σ k}, φ, q_{σ l}), k)`. -/
def bundleModelMap (Φb : ι → Q.Unif) (σ : κ → ι) : Q.modelSEP (Φb ∘ σ) ⟶ Q.modelSEP Φb :=
  ⟨S.modelMap (Q.modelBase Φb) σ, (Q.isMap_bundleReindex Φb σ).liftFunctor,
    (Q.isMap_bundleReindex Φb σ).isStrongBundleFunctor_liftFunctor⟩

@[simp] theorem bundleModelMap_ϕ (Φb : ι → Q.Unif) (σ : κ → ι) :
    SEP.Hom.ϕ (Q.bundleModelMap Φb σ) = S.modelMap (Q.modelBase Φb) σ := rfl

@[simp] theorem bundleModelMap_obj (Φb : ι → Q.Unif) (σ : κ → ι) (w : Q.ModelW (Φb ∘ σ)) :
    (SEP.Hom.Φ (Q.bundleModelMap Φb σ)).obj w = ⟨σ w.1, w.2⟩ := rfl

/-- `Γ̄_Φ̄ ∘ (W_{Φ̄ ∘ σ} → W_Φ̄) = Γ̄_{Φ̄ ∘ σ}`. -/
theorem bundleModelFunctor_comp_bundleModelMap (Φb : ι → Q.Unif) (σ : κ → ι) :
    (Q.bundleModelFunctor Φb).comp (SEP.Hom.Φ (Q.bundleModelMap Φb σ)).toGroupoidFunctor =
      Q.bundleModelFunctor (Φb ∘ σ) := rfl

theorem mem_oneSet_bundleReindex_iff (Φb : ι → Q.Unif) (σ : κ → ι) (w : Q.ModelW (Φb ∘ σ)) :
    Q.bundleReindex Φb σ w ∈ (Q.modelBundle Φb).oneSet ↔ w ∈ (Q.modelBundle (Φb ∘ σ)).oneSet := by
  obtain ⟨k, v⟩ := w
  exact (StrongBundle.mem_oneSet_sigma_iff (B := fun i => (Φb i).1.B) v).trans
    (StrongBundle.mem_oneSet_sigma_iff (B := fun k => (Φb (σ k)).1.B) v).symm

theorem isLocalStrongBundleIso_bundleReindex (Φb : ι → Q.Unif) (σ : κ → ι)
    (x : S.ModelObj (Q.modelBase (Φb ∘ σ))) :
    ∃ (U : Set (S.ModelObj (Q.modelBase (Φb ∘ σ)))) (U' : Set (S.ModelObj (Q.modelBase Φb))),
      x ∈ U ∧ (Q.modelBundle (Φb ∘ σ)).IsStrongBundleIsoOn (Q.modelBundle Φb)
        (Q.isStrongBundleMap_bundleReindex Φb σ) U U' :=
  StrongBundle.isStrongBundleIsoOn_sigmaMap (fun k => (Φb (σ k)).1.B) (fun i => (Φb i).1.B)
    (fun k => StrongBundle.IsStrongBundleMap.id (Φb (σ k)).1.B)
    (fun k y => ⟨univ, univ, mem_univ y, (Φb (σ k)).1.B.isStrongBundleIsoOn_id isOpen_univ⟩) x

theorem fibInj_bundleModelMap (Φb : ι → Q.Unif) (σ : κ → ι) :
    SEP.FibInj (Q.bundleModelMap Φb σ) := by
  rintro ⟨k, v⟩ ⟨k', v'⟩ hP he
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 hP
  exact Sigma.ext rfl (heq_of_eq (eq_of_heq (Sigma.mk.inj_iff.1 he).2))

variable {Q} in
/-- **The reindexing functor is a strong bundle equivalence if the base family `Φ ∘ σ` covers.** -/
theorem equivalences_bundleModelMap {Φb : ι → Q.Unif} {σ : κ → ι}
    (h : S.IsCoveringFamily (Q.modelBase (Φb ∘ σ))) :
    SEP.equivalences (Q.bundleModelMap Φb σ) :=
  SEP.equivalences_of_isStrongBundleIsoOn _ (S.isEquivalence_modelMap h)
    (Q.fibInj_bundleModelMap Φb σ) (Q.isLocalStrongBundleIso_bundleReindex Φb σ)
    fun w hw => (Q.mem_oneSet_bundleReindex_iff Φb σ w).1 hw

/-- **The inclusion `W_Ψ̄ → W_Φ̄`** of a family `Ψ̄ = Φ̄ ∘ σ`. -/
def bundleIncl (Ψb : κ → Q.Unif) (Φb : ι → Q.Unif) (σ : κ → ι) (h : Φb ∘ σ = Ψb) :
    Q.modelSEP Ψb ⟶ Q.modelSEP Φb :=
  eqToHom (congrArg (fun Θ : κ → Q.Unif => Q.modelSEP Θ) h.symm) ≫ Q.bundleModelMap Φb σ

theorem bundleIncl_rfl (Φb : ι → Q.Unif) (σ : κ → ι) :
    Q.bundleIncl (Φb ∘ σ) Φb σ rfl = Q.bundleModelMap Φb σ := by
  rw [bundleIncl, eqToHom_refl, Category.id_comp]

/-- The inclusion covers the base inclusion `X_Ψ → X_Φ`. -/
theorem bundleIncl_ϕ {Ψb : κ → Q.Unif} {Φb : ι → Q.Unif} {σ : κ → ι} (h : Φb ∘ σ = Ψb) :
    SEP.Hom.ϕ (Q.bundleIncl Ψb Φb σ h) =
      S.incl (Q.modelBase Ψb) (Q.modelBase Φb) σ (h ▸ rfl) := by
  subst h
  rfl

/-- `Γ̄_Φ̄ ∘ incl = Γ̄_Ψ̄`. -/
theorem bundleModelFunctor_comp_bundleIncl {Ψb : κ → Q.Unif} {Φb : ι → Q.Unif} {σ : κ → ι}
    (h : Φb ∘ σ = Ψb) :
    (Q.bundleModelFunctor Φb).comp (SEP.Hom.Φ (Q.bundleIncl Ψb Φb σ h)).toGroupoidFunctor =
      Q.bundleModelFunctor Ψb := by
  subst h
  rw [bundleIncl_rfl]
  rfl

/-- **The inclusion of a covering family is a strong bundle equivalence.** -/
theorem equivalences_bundleIncl {Ψb : κ → Q.Unif} {Φb : ι → Q.Unif} {σ : κ → ι}
    (h : Φb ∘ σ = Ψb) (hΨ : S.IsCoveringFamily (Q.modelBase Ψb)) :
    SEP.equivalences (Q.bundleIncl Ψb Φb σ h) := by
  subst h
  rw [bundleIncl_rfl]
  exact equivalences_bundleModelMap hΨ

/-- Inclusions compose. -/
theorem bundleIncl_comp {Ψb : κ → Q.Unif} {Φb : ι → Q.Unif} {Θb : μ → Q.Unif} {σ : κ → ι}
    {τ : ι → μ} {ρ : κ → μ} (h₁ : Φb ∘ σ = Ψb) (h₂ : Θb ∘ τ = Φb) (h₃ : Θb ∘ ρ = Ψb)
    (hρ : τ ∘ σ = ρ) :
    Q.bundleIncl Ψb Φb σ h₁ ≫ Q.bundleIncl Φb Θb τ h₂ = Q.bundleIncl Ψb Θb ρ h₃ := by
  subst hρ h₂ h₁
  rw [bundleIncl_rfl, bundleIncl_rfl, show Q.bundleIncl ((Θb ∘ τ) ∘ σ) Θb (τ ∘ σ) h₃ =
    Q.bundleModelMap Θb (τ ∘ σ) from Q.bundleIncl_rfl Θb (τ ∘ σ)]
  rfl

/-- The inclusion of a family into itself is the identity. -/
theorem bundleIncl_id (Ψb : κ → Q.Unif) : Q.bundleIncl Ψb Ψb id rfl = 𝟙 (Q.modelSEP Ψb) := by
  change Q.bundleIncl (Ψb ∘ id) Ψb id rfl = _
  rw [bundleIncl_rfl]
  rfl

end Reindex

/-! ### The inclusions into `W_{Ψ̄ ⊔ Ψ̄'}` and the comparison diagram -/

section Union

open SBLocalization SBLocalization.SEPLoc

variable {ι ι' : Type u} (Ψb : ι → Q.Unif) (Ψb' : ι' → Q.Unif)

/-- `W_Ψ̄ → W_{Ψ̄ ⊔ Ψ̄'}`. -/
abbrev bundleInclLeft : Q.modelSEP Ψb ⟶ Q.modelSEP (Sum.elim Ψb Ψb') :=
  Q.bundleIncl Ψb (Sum.elim Ψb Ψb') Sum.inl rfl

/-- `W_Ψ̄' → W_{Ψ̄ ⊔ Ψ̄'}`. -/
abbrev bundleInclRight : Q.modelSEP Ψb' ⟶ Q.modelSEP (Sum.elim Ψb Ψb') :=
  Q.bundleIncl Ψb' (Sum.elim Ψb Ψb') Sum.inr rfl

variable {Ψb Ψb'}

theorem equivalences_bundleInclLeft (hΨ : S.IsCoveringFamily (Q.modelBase Ψb)) :
    SEP.equivalences (Q.bundleInclLeft Ψb Ψb') :=
  Q.equivalences_bundleIncl rfl hΨ

theorem equivalences_bundleInclRight (hΨ' : S.IsCoveringFamily (Q.modelBase Ψb')) :
    SEP.equivalences (Q.bundleInclRight Ψb Ψb') :=
  Q.equivalences_bundleIncl rfl hΨ'

variable (Ψb Ψb')

/-- **The diagram `W_Ψ̄ ← W_Ψ̄ ×_{W_{Ψ̄ ⊔ Ψ̄'}} W_Ψ̄' → W_Ψ̄'`**, the strong bundle analogue of
(17.15), built from the weak fibred product of strong bundles of Theorem 10.2.2 along the
equivalence `W_Ψ̄' → W_{Ψ̄ ⊔ Ψ̄'}`. -/
def bundleCompareDiagram (hΨ' : S.IsCoveringFamily (Q.modelBase Ψb')) :
    SDiagram (Q.modelSEP Ψb) (Q.modelSEP Ψb') where
  B := SBWeakFibredProduct.wfpSEP (Q.equivalences_bundleInclRight hΨ') (Q.bundleInclLeft Ψb Ψb')
  Φ := SBWeakFibredProduct.projZ _ _
  isEquivalence_Φ := (SBWeakFibredProduct.theorem_10_2_2 _ _).1
  Ψ := SBWeakFibredProduct.projX _ _

/-- **The generalized strong bundle map `f̄_{Ψ̄,Ψ̄'} : W_Ψ̄ → W_Ψ̄'`**. -/
def bundleCompare (hΨ' : S.IsCoveringFamily (Q.modelBase Ψb')) :
    localizationFunctor.obj (Q.modelSEP Ψb) ⟶ localizationFunctor.obj (Q.modelSEP Ψb') :=
  homMk (Q.bundleCompareDiagram Ψb Ψb' hΨ')

variable {Ψb Ψb'} in
/-- **`f̄_{Ψ̄,Ψ̄'}` through any family containing `Ψ̄` and `Ψ̄'`**: if `Ψ̄ = Φ̄ ∘ σ` and
`Ψ̄' = Φ̄ ∘ σ'`, then `i(Ψ̄' → Φ̄) ∘ f̄_{Ψ̄,Ψ̄'} = i(Ψ̄ → Φ̄)` in `SEP(F⁻¹)`. -/
theorem bundleCompare_comp_incl {κ : Type u} (Φb : κ → Q.Unif) {σ : ι → κ} {σ' : ι' → κ}
    (h : Φb ∘ σ = Ψb) (h' : Φb ∘ σ' = Ψb') (hΨ' : S.IsCoveringFamily (Q.modelBase Ψb')) :
    Q.bundleCompare Ψb Ψb' hΨ' ≫ localizationFunctor.map (Q.bundleIncl Ψb' Φb σ' h') =
      localizationFunctor.map (Q.bundleIncl Ψb Φb σ h) := by
  have hK : Φb ∘ Sum.elim σ σ' = Sum.elim Ψb Ψb' := by
    funext x
    cases x with
    | inl a => exact congrFun h a
    | inr a => exact congrFun h' a
  have hA : Q.bundleInclLeft Ψb Ψb' ≫ Q.bundleIncl (Sum.elim Ψb Ψb') Φb (Sum.elim σ σ') hK =
      Q.bundleIncl Ψb Φb σ h :=
    Q.bundleIncl_comp _ _ _ rfl
  have hA' : Q.bundleInclRight Ψb Ψb' ≫ Q.bundleIncl (Sum.elim Ψb Ψb') Φb (Sum.elim σ σ') hK =
      Q.bundleIncl Ψb' Φb σ' h' :=
    Q.bundleIncl_comp _ _ _ rfl
  set D := Q.bundleCompareDiagram Ψb Ψb' hΨ' with hD
  have hnat : localizationFunctor.map (D.Ψ ≫ Q.bundleInclRight Ψb Ψb') =
      localizationFunctor.map (D.Φ ≫ Q.bundleInclLeft Ψb Ψb') :=
    map_eq_of_natEquiv (SBWeakFibredProduct.theorem_10_2_2 _ _).2.1
  have key : localizationFunctor.map D.Φ ≫ localizationFunctor.map (Q.bundleIncl Ψb Φb σ h) =
      localizationFunctor.map D.Ψ ≫ localizationFunctor.map (Q.bundleIncl Ψb' Φb σ' h') := by
    rw [← hA, ← hA', ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← Category.assoc, ← Category.assoc, CategoryTheory.Functor.map_comp, ← hnat,
      ← CategoryTheory.Functor.map_comp]
  have := isInvertedBy_localizationFunctor _ D.isEquivalence_Φ
  refine (cancel_epi (localizationFunctor.map D.Φ)).1 ?_
  rw [key, ← Category.assoc]
  exact congrArg (· ≫ _) (map_comp_homMk D)

end Union

/-! ### The strong bundle analogue of Theorem 17.1.18 -/

section Comparison

open SBLocalization SBLocalization.SEPLoc

/-- A family of strong bundle uniformizers whose base family covers `|C|`. -/
structure BundleCoveringFamily : Type (u + 1) where
  /-- The index set. -/
  ι : Type u
  /-- The strong bundle uniformizers `Ψ̄_λ`. -/
  Ψ : ι → Q.Unif
  /-- The base uniformizers cover `|C|`. -/
  cover : S.IsCoveringFamily (Q.modelBase Ψ)

variable {Q}

/-- The underlying covering family of base uniformizers. -/
def BundleCoveringFamily.base (c : Q.BundleCoveringFamily) : S.CoveringFamily :=
  ⟨c.ι, Q.modelBase c.Ψ, c.cover⟩

variable (Q)

/-- **`f̄_{Ψ̄,Ψ̄'} : W_Ψ̄ → W_Ψ̄'`** for covering families. -/
def bundleComparison (c c' : Q.BundleCoveringFamily) :
    localizationFunctor.obj (Q.modelSEP c.Ψ) ⟶ localizationFunctor.obj (Q.modelSEP c'.Ψ) :=
  Q.bundleCompare c.Ψ c'.Ψ c'.cover

theorem bundleComparison_comp_incl (c c' : Q.BundleCoveringFamily) {κ : Type u}
    (Φb : κ → Q.Unif) {σ : c.ι → κ} {σ' : c'.ι → κ} (h : Φb ∘ σ = c.Ψ) (h' : Φb ∘ σ' = c'.Ψ) :
    Q.bundleComparison c c' ≫ localizationFunctor.map (Q.bundleIncl c'.Ψ Φb σ' h') =
      localizationFunctor.map (Q.bundleIncl c.Ψ Φb σ h) :=
  Q.bundleCompare_comp_incl Φb h h' c'.cover

/-- **`f̄_{Ψ̄,Ψ̄} = 1`.** -/
theorem bundleComparison_self (c : Q.BundleCoveringFamily) : Q.bundleComparison c c = 𝟙 _ := by
  have := Q.bundleComparison_comp_incl c c c.Ψ (σ := id) (σ' := id) rfl rfl
  rwa [bundleIncl_id, CategoryTheory.Functor.map_id, Category.comp_id] at this

/-- **The cocycle identity** `f̄_{Ψ̄',Ψ̄''} ∘ f̄_{Ψ̄,Ψ̄'} = f̄_{Ψ̄,Ψ̄''}`. -/
theorem bundleComparison_comp (c c' c'' : Q.BundleCoveringFamily) :
    Q.bundleComparison c c' ≫ Q.bundleComparison c' c'' = Q.bundleComparison c c'' := by
  let Φb := Sum.elim c.Ψ (Sum.elim c'.Ψ c''.Ψ)
  have e₁ := Q.bundleComparison_comp_incl c c' Φb (σ := Sum.inl) (σ' := Sum.inr ∘ Sum.inl)
    rfl rfl
  have e₂ := Q.bundleComparison_comp_incl c' c'' Φb (σ := Sum.inr ∘ Sum.inl)
    (σ' := Sum.inr ∘ Sum.inr) rfl rfl
  have e₃ := Q.bundleComparison_comp_incl c c'' Φb (σ := Sum.inl) (σ' := Sum.inr ∘ Sum.inr)
    rfl rfl
  have := isInvertedBy_localizationFunctor _
    (Q.equivalences_bundleIncl (Ψb := c''.Ψ) (Φb := Φb) (σ := Sum.inr ∘ Sum.inr) rfl c''.cover)
  refine (cancel_mono (localizationFunctor.map
    (Q.bundleIncl c''.Ψ Φb (Sum.inr ∘ Sum.inr) rfl))).1 ?_
  rw [Category.assoc, e₂, e₁, e₃]

/-- **`f̄_{Ψ̄,Ψ̄'}` is a generalized strong bundle isomorphism** (Definition 10.5.2): the leg
`W_Ψ̄ ×_{W_{Ψ̄ ⊔ Ψ̄'}} W_Ψ̄' → W_Ψ̄'` is a strong bundle equivalence, since `W_Ψ̄ → W_{Ψ̄ ⊔ Ψ̄'}`
is one (Theorem 10.2.2). -/
theorem isGeneralizedIso_bundleComparison (c c' : Q.BundleCoveringFamily) :
    GenSBMap.IsGeneralizedIso (Q.bundleComparison c c') :=
  ⟨Q.bundleCompareDiagram c.Ψ c'.Ψ c'.cover, rfl,
    SBWeakFibredProduct.theorem_10_2_2_right _ _ (Q.equivalences_bundleInclLeft c.cover)⟩

/-- `f̄_{Ψ̄,Ψ̄'}` is an isomorphism of `SEP(F⁻¹)` (Theorem 10.3.10). -/
theorem isIso_bundleComparison (c c' : Q.BundleCoveringFamily) :
    IsIso (Q.bundleComparison c c') :=
  isIso_of_isGeneralizedIso (Q.isGeneralizedIso_bundleComparison c c')

/-- The base functor sends the image of a strong bundle functor to the image of the functor
of base ep-groupoids it covers. -/
theorem baseFunctor_map_localizationFunctor_map {A A' : SEP.{u}} (F : A ⟶ A') :
    baseFunctor.map (localizationFunctor.map F) =
      EPLocalization.EPLoc.localizationFunctor.map (SEP.Hom.ϕ F) := rfl

/-- **`f̄_{Ψ̄,Ψ̄'}` covers `f_{Ψ,Ψ'}`**: the functor `SEP(F⁻¹) → EP(E⁻¹)` sends `f̄_{Ψ̄,Ψ̄'}` to
the generalized map `f_{Ψ,Ψ'}` of Theorem 17.1.18 of the base covering families. -/
theorem baseFunctor_map_bundleComparison (c c' : Q.BundleCoveringFamily) :
    baseFunctor.map (Q.bundleComparison c c') = S.comparison c.base c'.base := by
  have e := congrArg baseFunctor.map (Q.bundleComparison_comp_incl c c' (Sum.elim c.Ψ c'.Ψ)
    (σ := Sum.inl) (σ' := Sum.inr) rfl rfl)
  rw [CategoryTheory.Functor.map_comp, baseFunctor_map_localizationFunctor_map,
    baseFunctor_map_localizationFunctor_map] at e
  have e' := S.comparison_comp_incl c.base c'.base (Q.modelBase (Sum.elim c.Ψ c'.Ψ))
    (σ := Sum.inl) (σ' := Sum.inr) rfl rfl
  have := EPLocalization.EPLoc.isInvertedBy_localizationFunctor _
    (S.isEquivalence_incl (Ψ := Q.modelBase c'.Ψ) (Φ := Q.modelBase (Sum.elim c.Ψ c'.Ψ))
      (σ := Sum.inr) rfl c'.cover)
  refine (cancel_mono (EPLocalization.EPLoc.localizationFunctor.map
    (S.incl (Q.modelBase c'.Ψ) (Q.modelBase (Sum.elim c.Ψ c'.Ψ)) Sum.inr rfl))).1 ?_
  exact e.trans e'.symm

/-- **`|Γ̄_Ψ̄'| ∘ |f̄_{Ψ̄,Ψ̄'}| = |Γ̄_Ψ̄|`**. -/
theorem orbitMap_bundleComparison (c c' : Q.BundleCoveringFamily) :
    (Q.bundleModelFunctor c'.Ψ).orbitMap ∘ GenSBMap.orbitMap (Q.bundleComparison c c') =
      (Q.bundleModelFunctor c.Ψ).orbitMap := by
  funext q
  set D := Q.bundleCompareDiagram c.Ψ c'.Ψ c'.cover with hD
  obtain ⟨r, rfl⟩ := D.hΦ.isEquivalence.isHomeomorph_orbitMap.surjective q
  change (Q.bundleModelFunctor c'.Ψ).orbitMap (D.orbitMap ((SEP.Hom.Φ D.Φ).orbitMap r)) = _
  rw [SDiagram.orbitMap_orbitMap_Φ]
  induction r using Quotient.inductionOn with | h w => ?_
  have hnat := congrArg (Q.bundleModelFunctor (Sum.elim c.Ψ c'.Ψ)).orbitMap
    (congrFun (SEP.NatEquiv.orbitMap_eq (SBWeakFibredProduct.theorem_10_2_2
      (Q.equivalences_bundleInclRight c'.cover) (Q.bundleInclLeft c.Ψ c'.Ψ)).2.1)
      (D.B.E.toEpGroupoid.π w))
  have hR := congrArg (fun F : GroupoidFunctor _ _ => V.groupoid.π (F.obj
    ((SEP.Hom.Φ D.Ψ).obj w))) (Q.bundleModelFunctor_comp_bundleIncl
      (Ψb := c'.Ψ) (Φb := Sum.elim c.Ψ c'.Ψ) (σ := Sum.inr) rfl)
  have hL := congrArg (fun F : GroupoidFunctor _ _ => V.groupoid.π (F.obj
    ((SEP.Hom.Φ D.Φ).obj w))) (Q.bundleModelFunctor_comp_bundleIncl
      (Ψb := c.Ψ) (Φb := Sum.elim c.Ψ c'.Ψ) (σ := Sum.inl) rfl)
  exact hR.symm.trans (hnat.trans hL)

/-- **`|f̄_{Ψ̄,Ψ̄'}| : |W_Ψ̄| → |W_Ψ̄'|` is a homeomorphism** (Remark 10.5.3). -/
theorem isHomeomorph_orbitMap_bundleComparison (c c' : Q.BundleCoveringFamily) :
    IsHomeomorph (GenSBMap.orbitMap (Q.bundleComparison c c')) :=
  (GenSBMap.remark_10_5_3 (Q.isGeneralizedIso_bundleComparison c c')).2.2

/-- **The strong bundle analogue of Theorem 17.1.18** (2021 §17.7, p. 828, which leaves it to the
reader): for families `Ψ̄`, `Ψ̄'`, `Ψ̄''` of strong bundle uniformizers whose base families cover
`|C|`, `f̄_{Ψ̄,Ψ̄'} : W_Ψ̄ → W_Ψ̄'` is a generalized strong bundle isomorphism covering
`f_{Ψ,Ψ'}`; `f̄_{Ψ̄,Ψ̄} = 1`; `f̄_{Ψ̄',Ψ̄''} ∘ f̄_{Ψ̄,Ψ̄'} = f̄_{Ψ̄,Ψ̄''}`;
`|Γ̄_Ψ̄'| ∘ |f̄_{Ψ̄,Ψ̄'}| = |Γ̄_Ψ̄|`; and `|f̄_{Ψ̄,Ψ̄'}|` is a homeomorphism. -/
theorem theorem_17_1_18_bundle (c c' c'' : Q.BundleCoveringFamily) :
    GenSBMap.IsGeneralizedIso (Q.bundleComparison c c') ∧
      baseFunctor.map (Q.bundleComparison c c') = S.comparison c.base c'.base ∧
      Q.bundleComparison c c = 𝟙 _ ∧
      Q.bundleComparison c c' ≫ Q.bundleComparison c' c'' = Q.bundleComparison c c'' ∧
      (Q.bundleModelFunctor c'.Ψ).orbitMap ∘ GenSBMap.orbitMap (Q.bundleComparison c c') =
        (Q.bundleModelFunctor c.Ψ).orbitMap ∧
      IsHomeomorph (GenSBMap.orbitMap (Q.bundleComparison c c')) :=
  ⟨Q.isGeneralizedIso_bundleComparison c c', Q.baseFunctor_map_bundleComparison c c',
    Q.bundleComparison_self c, Q.bundleComparison_comp c c' c'',
    Q.orbitMap_bundleComparison c c', Q.isHomeomorph_orbitMap_bundleComparison c c'⟩

end Comparison

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
