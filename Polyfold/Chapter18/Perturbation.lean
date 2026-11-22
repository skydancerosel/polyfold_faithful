import Polyfold.Chapter18.Orientations
import Polyfold.Chapter15.GeneralPositionExistence
import Polyfold.Chapter15.TameBranched
import Polyfold.Chapter15.CanonicalOrientationOrientedSection
import Polyfold.Chapter17.CategoryStokes
import Polyfold.Chapter16.ModelPerturbations

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.6 "Perturbation Theory", pp. 860–861: **Theorem 18.6.1** and the list (1)–(4) before it.
Numbers and pages are the 2021 text's.

## The text, paraphrased

(Theorem 18.6.1) Let `P : E → C` be a strong polyfold bundle over a tame `C` admitting sc-smooth
bump functions, `f` an sc-smooth section functor with compact `|S_f|`, `N` an auxiliary norm and
`U` an open neighbourhood of `|S_f|` with `(N, U)` controlling compactness, `h : C → (0, 1]` a
continuous functor.  Then there is an sc⁺-multisection functor `Λ : E → ℚ⁺` with (1)
`N(Λ)(α) < h(α)`, (2) domain support in `C_U`, (3) `T(f, Λ)` onto at the objects of
`supp(Λ ∘ f)`, (4) the kernels in general position to `∂C`.  "Proof: this follows directly from
Theorem 15.3.7 by studying the question in a smooth model."

## What is formalized

* `PolyfoldConstruction.IsContinuousFunctionFunctor`: a continuous functor `h : C → ℝ`
  (constant along morphisms, continuous in every uniformizer); continuous on every model.
* `SPBC.IsTransversalIn`, `SPBC.IsInGeneralPositionIn`: (3) and (4) in a model `W_Ψ̄ → X_Ψ`
  (Definitions 15.2.1, 15.3.5 for `(f^Ψ̄_Ψ, Γ̄^*Λ)`).
* `SPBC.controlsCompactness_model`: `(N, U)` controlling compactness (Definition 18.2.3) gives
  `(N ∘ Γ̄, |Γ|⁻¹(U))` controlling compactness in every covering model.
* **`SPBC.theorem_18_6_1_existence`**: (1)–(4), from `theorem_15_3_7_existence` in the model
  `c` and the push-forward `Γ̄_*` of the model multisection.
* `SPBC.exists_push_of_model`: a model multisection with (1), (2) in the model pushes forward
  (`Γ̄_*`) to a functor `Λ` with (1), (2) on `C` and `Γ̄^*Λ` the model multisection.
* **`SPBC.theorem_18_6_1_structurable`**: "Λ can be taken to be structurable"
  (Definition 18.3.3), with (1)–(4): `theorem_15_3_7_of_paracompact` in the model (paracompact
  `|X_Ψ|`, `hasParacompactOrbitSpace_model`).
* `SPBC.domSupp_model_subset`, `SPBC.modelPull_comp` (`Γ^*(Λ ∘ f) = Γ̄^*Λ ∘ f^Ψ̄_Ψ`),
  `SPBC.isFunctorial_comp_sectionFunctor`.
* **`SPBC.theorem_18_6_1_in_particular`**: "In particular `Λ ∘ f` is a compact, tame,
  branched ep⁺-subcategory" (Definitions 17.5.1, 17.5.3 (1), (2)), from
  `theorem_15_3_7_in_particular_tame_hyp` in the model.
* **`SPBC.theorem_18_6_1`**: Theorem 18.6.1 without the orientation clause: a structurable
  `Λ` with (1)–(4) and `Λ ∘ f` a compact, tame, branched ep⁺-subcategory.
* `SPBC.perturbation_orbifoldType`, `SPBC.perturbation_manifoldType`: the paragraph
  after the list (1)–(4) (p. 860): for `{0, 1}`-valued `Θ = Λ ∘ f` the compact `|supp(Θ)|` has
  the orbifold structure of Proposition 17.5.5 (2), and with at most one morphism between
  objects of the support the manifold structure of Proposition 17.5.5 (1).
* `SBLocalization.isOrientationTopology_orTopology`: `orTopology` is the topology of Theorem
  6.6.17.
* **`SPBC.theorem_18_6_1_oriented`**: "if in addition `f` is oriented by `o_f`, `Θ = Λ ∘ f`
  is naturally oriented": an `OrientedSubcategory` (Chapter 17's oriented branched
  ep⁺-subcategory, read through the models) with underlying `Θ`, whose orientation in the model
  `c` is, on `X_∞`, the canonical orientation `T̂_((f^Ψ̄, Ψ̄^*o), Γ̄^*Λ)` of Definition 15.4.2,
  which is canonical in the sense of Theorem 15.4.1 (`IsCanonicalFor`).

The orientation clause names the dimension, `hidx`: `f` has index `n` at the points of
`supp(Λ ∘ f)` in the model (Theorem 15.4.1 orients `Θ` as an `n`-dimensional branched
ep⁺-subgroupoid).  The text leaves the dimension implicit; Theorem 15.4.3 states it ("an oriented
sc-Fredholm section of Fredholm index `k`"), and Part III's `theorem_15_4_1_of_definition_12_5_4`
carries the same hypothesis.

## Reading

* `f` is sc-Fredholm: the §18.6 preamble (l. 42415, "We study sc-Fredholm section functors
  `f`") makes it the standing assumption of the section, and the proof cites Theorem 15.3.7.
* As in Theorem 15.3.7 (and §15.2), `f` carries germ data in tame charts
  (`IsScFredholmSectionFunctorTame`, Definition 18.1.1 tame form): the standing reading of tame
  polyfolds (README: the germ data of §§3.6, 6.2, 6.6 and 12.5 are taken in a tame chart), which
  Part III's `theorem_15_3_7_existence` carries without a suffix; so do the statements here.
* "Admitting sc-smooth bump functions" is Definition 18.4.1 (`AdmitsModelBumpFunctions`).
* "Continuous functor `h`": constant along morphisms and `h ∘ Ψ` continuous for every
  uniformizer `Ψ`.  `N(Λ)(α) < h(α)` is read in `[0, ∞]`.
* "The domain support of `Λ` is contained in `C_U`" is `|dom-supp(Λ)| ⊆ U` (`orbitDomSupp`).
* (3) and (4) are read in a covering model `c` (the text: "by studying the question in a smooth
  model"); the theorem holds for every covering model `c`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory
open scoped ENNReal

noncomputable section

namespace Polyfold

universe u

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction)

/-- **A continuous functor `h : C → ℝ`** (Theorem 18.6.1, 2021 p. 860): constant along the
morphisms of `C` and continuous in every uniformizer, `h ∘ Ψ : O → ℝ`. -/
def IsContinuousFunctionFunctor (h : C.Obj → ℝ) : Prop :=
  (∀ φ : C.Mor, h (C.toGroupoidStr.tgt φ) = h (C.toGroupoidStr.src φ)) ∧
    ∀ Ψ : S.Unif, Continuous (h ∘ Ψ.1.obj)

variable {S}

/-- A continuous functor is continuous on every model `X_Ψ` (continuous on every piece). -/
theorem IsContinuousFunctionFunctor.continuous_model {h : C.Obj → ℝ}
    (hh : S.IsContinuousFunctionFunctor h) {κ : Type u} (Ψ : κ → S.Unif) :
    Continuous (h ∘ (S.modelFunctor Ψ).obj) :=
  continuous_sigma fun i => hh.2 (Ψ i)

/-- A continuous functor is a functor on every model: `h ∘ Γ` is constant along morphisms. -/
theorem IsContinuousFunctionFunctor.mor_model {h : C.Obj → ℝ}
    (hh : S.IsContinuousFunctionFunctor h) {κ : Type u} (Ψ : κ → S.Unif) (φ : S.ModelMor Ψ) :
    h ((S.modelFunctor Ψ).obj ((S.modelEpGroupoid Ψ).src φ)) =
      h ((S.modelFunctor Ψ).obj ((S.modelEpGroupoid Ψ).tgt φ)) :=
  ((congrArg h ((S.modelFunctor Ψ).src_mor φ)).symm.trans (hh.1 _).symm).trans
    (congrArg h ((S.modelFunctor Ψ).tgt_mor φ))

end GCT.PolyfoldConstruction

namespace SBLocalization

variable {A : SEP.{u}}

/-- The topology `orTopology` of `O_f` built from the local transport (Theorem 6.6.17) has the
properties (1)–(3) of Theorem 6.6.17 (it is the unique such topology). -/
theorem isOrientationTopology_orTopology (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough) :
    haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    haveI := paracompactSpace_rn_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A.B
    IsOrientationTopology f hft.toIsScFredholmSection
      (orTopology (orLocalTransport hX hbump hft hsec)) := by
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_rn_prod A.X.PObj
  have := paracompactSpace_rn_rn_pullback A.B
  obtain ⟨t, ht, -⟩ := theorem_6_6_17 hX hbump hft
  rwa [← eq_orTopology_of hX hbump hft hsec ht.isLocalHomeomorph ht.propagation]

end SBLocalization

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory.BanachFunctor SBLocalization StrongBundle PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S) {ι : Type u} (Ψb : ι → Q.Unif)

/-- **(3) of Theorem 18.6.1 in a model**: `(f^Ψ̄_Ψ, Γ̄^*Λ)` is transversal (Definition 15.2.1):
`T(f, Λ)` is onto at the objects of `supp(Λ ∘ f)`. -/
def IsTransversalIn (f : V.SectionFunctor) (Λ : V.EObj → ℚ≥0) : Prop :=
  IsTransversal (A := Q.modelSEP Ψb) (Q.modelSection Ψb f) (Q.bundlePull Ψb Λ)

/-- **(4) of Theorem 18.6.1 in a model**: `(f^Ψ̄_Ψ, Γ̄^*Λ)` is in general position to the
boundary (Definition 15.3.5). -/
def IsInGeneralPositionIn (f : V.SectionFunctor) (Λ : V.EObj → ℚ≥0) : Prop :=
  IsInGeneralPosition (Q.modelSEP Ψb) (Q.modelSection Ψb f) (Q.bundlePull Ψb Λ)

variable {Q}

/-- **Controlling compactness transfers to a covering model**: if `(N, U)` controls compactness
for `f` (Definition 18.2.3), then `(N ∘ Γ̄, |Γ|⁻¹(U))` controls compactness for `f^Ψ̄_Ψ`
(Definition 15.3.1 as formalized, `ControlsCompactness`). -/
theorem controlsCompactness_model (c : Q.BundleCoveringFamily) {f : V.SectionFunctor}
    {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormIn c.Ψ N) {U : Set C.toGroupoidStr.OrbitSpace}
    (hcc : f.ControlsCompactness N U) :
    ControlsCompactness (Q.modelSEP c.Ψ) (Q.modelSection c.Ψ f) (Q.modelNorm c.Ψ N)
      ((Q.modelSEP c.Ψ).X.π ⁻¹' ((S.modelFunctor (Q.modelBase c.Ψ)).orbitMap ⁻¹' U)) := by
  set X := (Q.modelSEP c.Ψ).X
  set h := (S.modelFunctor (Q.modelBase c.Ψ)).orbitMap
  have hhc : Continuous h := (isHomeomorph_modelOrbitMap c.cover).continuous
  obtain ⟨hUo, hSU, hC⟩ := hcc
  set Ut := X.π ⁻¹' (h ⁻¹' U)
  have hUt : h '' (X.π '' Ut) = U := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact hy
    · intro hz
      obtain ⟨q, rfl⟩ := (isHomeomorph_modelOrbitMap c.cover).surjective z
      obtain ⟨y, rfl⟩ := X.surjective_π q
      exact ⟨_, ⟨y, hz, rfl⟩, rfl⟩
  refine ⟨hN.isAuxNorm, (hUo.preimage hhc).preimage X.continuous_π, ?_, ?_, ?_⟩
  · change X.π ⁻¹' (X.π '' (X.π ⁻¹' _)) = X.π ⁻¹' _
    rw [image_preimage_eq _ X.surjective_π]
  · intro x hx
    have h0 := (Q.mem_modelSolutionSet_iff c.Ψ f x).1 hx
    exact hSU ⟨_, h0, rfl⟩
  · refine (isCompact_closure_modelImage_iff c hN Ut zero_le_one).1 ?_
    rw [hUt, ENNReal.ofReal_one]
    exact hC

/-- **2021 Theorem 18.6.1, (1)–(4), p. 860**, with tame germ data (`hfT`, the standing reading), in
a covering model `c`: over a tame `C` admitting sc-smooth bump functions (Definition 18.4.1), for an
sc-Fredholm section functor `f` (tame form) with compact `|S_f|`, an auxiliary norm `N`, an open
`U ⊇ |S_f|` with `(N, U)` controlling compactness and a continuous functor `h : C → (0, 1]`, there
is an sc⁺-multisection functor `Λ : E → ℚ⁺` with (1) `N(Λ)(α) < h(α)` for all `α`, (2)
`|dom-supp(Λ)| ⊆ U`, (3) `T(f, Λ)` onto on `supp(Λ ∘ f)` and (4) the kernels in general position
to `∂C`, (3) and (4) read in the model `c` (Theorem 15.3.7 in `W_Ψ̄ → X_Ψ`, the push-forward
`Γ̄_*` of the model multisection). -/
theorem theorem_18_6_1_existence (c : Q.BundleCoveringFamily) (hT : S.IsTame)
    (hbump : S.AdmitsModelBumpFunctions) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) (hfT : Q.IsScFredholmSectionFunctorTame f)
    (hS : f.HasCompactModuliSpace) {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormFunctor N)
    {U : Set C.toGroupoidStr.OrbitSpace} (hcc : f.ControlsCompactness N U) {h : C.Obj → ℝ}
    (hh : S.IsContinuousFunctionFunctor h) (hh01 : ∀ α, 0 < h α ∧ h α ≤ 1) :
    ∃ Λ : V.EObj → ℚ≥0, Q.IsScPlusMultisectionFunctor Λ ∧
      (∀ α, pointwiseNormFunctor N Λ α < ENNReal.ofReal (h α)) ∧ orbitDomSupp Λ ⊆ U ∧
      Q.IsTransversalIn c.Ψ f Λ ∧ Q.IsInGeneralPositionIn c.Ψ f Λ := by
  set A := Q.modelSEP c.Ψ
  set Γ := S.modelFunctor (Q.modelBase c.Ψ)
  have hNc := hN c
  obtain ⟨c₀, hb⟩ := hbump
  have hbA : A.X.AdmitsBumpFunctionsPointwise :=
    (S.admitsBumpFunctionsPointwise_model_iff c₀ c.base).1 hb
  obtain ⟨Λm, hΛm, hle, hdomm, htr, hgp⟩ := theorem_15_3_7_existence (A := A)
    (Q.modelTame c.Ψ hT) hbA (Q.modelSection c.Ψ f) (Q.modelFred c.Ψ hf) (Q.modelFredTame c.Ψ hfT)
    ((Q.isCompact_zeroSet_iff c.Ψ f c.cover).1 hS) (Q.modelNorm c.Ψ N) _
    (controlsCompactness_model c hNc hcc) (h ∘ Γ.obj) (hh.continuous_model _)
    (hh.mor_model _) (fun x => hh01 _)
  have hiso := Q.eq_of_isomorphic_of_isWFunctor hΛm.1
  set Λ := Q.bundlePush c.cover Λm hiso
  have hpull : Q.bundlePull c.Ψ Λ = Λm := Q.bundlePull_bundlePush c.cover _ _
  have hinv : IsMorInvariant Λ := Q.isMorInvariant_bundlePush c.cover _ hiso
  have hms : Q.IsScPlusMultisectionIn c.Ψ Λ := by
    unfold IsScPlusMultisectionIn; rw [hpull]; exact hΛm
  refine ⟨Λ, ⟨hinv, c, hms⟩, ?_, ?_, ?_, ?_⟩
  · intro α
    obtain ⟨x, ψ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (modelFunctor_essSurj c.cover) α
    rw [← pointwiseNormFunctor_eq_of_isomorphic hNc.isMorInvariant hinv ⟨ψ, hs, ht⟩]
    have hα : h α = h (Γ.obj x) := by rw [← ht, ← hs, hh.1]
    rw [hα]
    obtain ⟨hnt, heq⟩ := Q.pointwiseNorm_bundlePull hNc hms x
    rw [ENNReal.lt_ofReal_iff_toReal_lt hnt, heq, hpull]
    exact hle x
  · intro y hy
    obtain ⟨z, rfl⟩ := (isHomeomorph_modelOrbitMap c.cover).surjective y
    obtain ⟨x, rfl⟩ := A.X.surjective_π z
    have h2 := Q.preimage_orbitDomSupp_subset c hinv (show x ∈ _ from hy)
    rw [hpull] at h2
    exact hdomm h2
  · unfold IsTransversalIn; rw [hpull]; exact htr
  · unfold IsInGeneralPositionIn; rw [hpull]; exact hgp

/-- **The push-forward of a model multisection with (1), (2) in the model** has (1), (2) on `C`:
for an sc⁺-multisection `Λm` of the covering model `c` with `N(Λm) < h ∘ Γ` and
`dom-supp(Λm) ⊆ |Γ|⁻¹(U)`, the functor `Λ = Γ̄_*Λm` satisfies `Γ̄^*Λ = Λm`,
`N(Λ)(α) < h(α)` and `|dom-supp(Λ)| ⊆ U`. -/
theorem exists_push_of_model (c : Q.BundleCoveringFamily) {N : V.EObj → ℝ≥0∞}
    (hNc : Q.IsAuxNormIn c.Ψ N) {U : Set C.toGroupoidStr.OrbitSpace} {h : C.Obj → ℝ}
    (hh : S.IsContinuousFunctionFunctor h) {Λm : (Q.modelSEP c.Ψ).W → ℚ≥0}
    (hΛm : IsScPlusMultisection (Q.modelSEP c.Ψ) Λm)
    (hle : ∀ x, pointwiseNorm (Q.modelNorm c.Ψ N) Λm x <
      h ((S.modelFunctor (Q.modelBase c.Ψ)).obj x))
    (hdomm : domSupp Λm ⊆
      (Q.modelSEP c.Ψ).X.π ⁻¹' ((S.modelFunctor (Q.modelBase c.Ψ)).orbitMap ⁻¹' U)) :
    ∃ Λ : V.EObj → ℚ≥0, IsMorInvariant Λ ∧ Q.bundlePull c.Ψ Λ = Λm ∧
      (∀ α, pointwiseNormFunctor N Λ α < ENNReal.ofReal (h α)) ∧ orbitDomSupp Λ ⊆ U := by
  have hiso := Q.eq_of_isomorphic_of_isWFunctor hΛm.1
  set Λ := Q.bundlePush c.cover Λm hiso
  have hpull : Q.bundlePull c.Ψ Λ = Λm := Q.bundlePull_bundlePush c.cover _ _
  have hinv : IsMorInvariant Λ := Q.isMorInvariant_bundlePush c.cover _ hiso
  have hms : Q.IsScPlusMultisectionIn c.Ψ Λ := by
    unfold IsScPlusMultisectionIn; rw [hpull]; exact hΛm
  refine ⟨Λ, hinv, hpull, ?_, ?_⟩
  · intro α
    obtain ⟨x, ψ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (modelFunctor_essSurj c.cover) α
    rw [← pointwiseNormFunctor_eq_of_isomorphic hNc.isMorInvariant hinv ⟨ψ, hs, ht⟩]
    have hα : h α = h ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) := by rw [← ht, ← hs, hh.1]
    rw [hα]
    obtain ⟨hnt, heq⟩ := Q.pointwiseNorm_bundlePull hNc hms x
    rw [ENNReal.lt_ofReal_iff_toReal_lt hnt, heq, hpull]
    exact hle x
  · intro y hy
    obtain ⟨z, rfl⟩ := (isHomeomorph_modelOrbitMap c.cover).surjective y
    obtain ⟨x, rfl⟩ := (Q.modelSEP c.Ψ).X.surjective_π z
    have h2 := Q.preimage_orbitDomSupp_subset c hinv (show x ∈ _ from hy)
    rw [hpull] at h2
    exact hdomm h2

/-- **2021 Theorem 18.6.1, p. 860–861, "the perturbation `Λ` can be taken to be structurable"**,
with tame germ data (`hfT`, the standing reading), in a covering model `c`: under the hypotheses of
Theorem 18.6.1 there is a **structurable** sc⁺-multisection functor `Λ` (Definition 18.3.3) with
(1)–(4) (Theorem 15.3.7 in the model `c`, whose orbit space is paracompact, so a good system
exists, Theorem 13.1.8). -/
theorem theorem_18_6_1_structurable (c : Q.BundleCoveringFamily) (hT : S.IsTame)
    (hbump : S.AdmitsModelBumpFunctions) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) (hfT : Q.IsScFredholmSectionFunctorTame f)
    (hS : f.HasCompactModuliSpace) {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormFunctor N)
    {U : Set C.toGroupoidStr.OrbitSpace} (hcc : f.ControlsCompactness N U) {h : C.Obj → ℝ}
    (hh : S.IsContinuousFunctionFunctor h) (hh01 : ∀ α, 0 < h α ∧ h α ≤ 1) :
    ∃ Λ : V.EObj → ℚ≥0, Q.IsStructurableFunctor Λ ∧
      (∀ α, pointwiseNormFunctor N Λ α < ENNReal.ofReal (h α)) ∧ orbitDomSupp Λ ⊆ U ∧
      Q.IsTransversalIn c.Ψ f Λ ∧ Q.IsInGeneralPositionIn c.Ψ f Λ := by
  set A := Q.modelSEP c.Ψ
  set Γ := S.modelFunctor (Q.modelBase c.Ψ)
  have hNc := hN c
  obtain ⟨c₀, hb⟩ := hbump
  have hbA : A.X.AdmitsBumpFunctionsPointwise :=
    (S.admitsBumpFunctionsPointwise_model_iff c₀ c.base).1 hb
  obtain ⟨Λm, hΛm, hle, hdomm, htr, hgp⟩ := theorem_15_3_7_of_paracompact (A := A)
    (Q.hasParacompactOrbitSpace_model c)
    (Q.modelTame c.Ψ hT) hbA (Q.modelSection c.Ψ f) (Q.modelFred c.Ψ hf) (Q.modelFredTame c.Ψ hfT)
    ((Q.isCompact_zeroSet_iff c.Ψ f c.cover).1 hS) (Q.modelNorm c.Ψ N) _
    (controlsCompactness_model c hNc hcc) (h ∘ Γ.obj) (hh.continuous_model _)
    (hh.mor_model _) (fun x => hh01 _)
  obtain ⟨Λ, hinv, hpull, h1, h2⟩ := exists_push_of_model c hNc hh hΛm.1 hle hdomm
  refine ⟨Λ, ⟨hinv, c, ?_⟩, h1, h2, ?_, ?_⟩
  · unfold IsStructurableIn; rw [hpull]; exact hΛm
  · unfold IsTransversalIn; rw [hpull]; exact htr
  · unfold IsInGeneralPositionIn; rw [hpull]; exact hgp

/-- The domain support of `Γ̄^*Λ` in the model lies over `|dom-supp(Λ)|`. -/
theorem domSupp_model_subset (c : Q.BundleCoveringFamily) (Λ : V.EObj → ℚ≥0) :
    domSupp (A := Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ) ⊆
      (fun x : S.ModelObj (Q.modelBase c.Ψ) =>
        C.toGroupoidStr.π ((S.modelFunctor (Q.modelBase c.Ψ)).obj x)) ⁻¹' orbitDomSupp Λ := by
  have hg : Continuous fun x : S.ModelObj (Q.modelBase c.Ψ) =>
      C.toGroupoidStr.π ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) :=
    (isHomeomorph_modelOrbitMap c.cover).continuous.comp (Q.modelSEP c.Ψ).X.continuous_π
  refine (closure_mono ?_).trans (hg.closure_preimage_subset _)
  rintro _ ⟨w, rfl, hw0, hpos⟩
  refine ⟨_, ⟨Q.bundleModelFiber c.Ψ _ ⟨w, rfl⟩, ?_, ?_⟩, rfl⟩
  · intro h0
    exact hw0 (congrArg Subtype.val ((Q.bundleModelFiber c.Ψ _).map_eq_zero_iff.1 h0))
  · rw [Q.objMk_bundleModelFiber c.Ψ]; exact hpos

/-- `Θ = Λ ∘ f` read in the model: `Γ^*Θ = Γ̄^*Λ ∘ f^Ψ̄_Ψ` ((18.3)). -/
theorem modelPull_comp (c : Q.BundleCoveringFamily) (f : V.SectionFunctor) (Λ : V.EObj → ℚ≥0) :
    S.modelPull (Q.modelBase c.Ψ) (fun α => (Λ (f.toFun α) : ℚ)) =
      fun z => ((Q.bundlePull c.Ψ Λ (Q.modelSection c.Ψ f z) : ℚ≥0) : ℚ) := by
  funext z
  change ((Λ (f.toFun ((S.modelFunctor (Q.modelBase c.Ψ)).obj z)) : ℚ≥0) : ℚ) =
    ((Λ ((Q.bundleModelFunctor c.Ψ).obj (Q.modelSection c.Ψ f z)) : ℚ≥0) : ℚ)
  rw [Q.bundleModelFunctor_obj_modelSection]

/-- `Θ = Λ ∘ f` is a functor `C → ℚ⁺` for a functor `Λ`. -/
theorem isFunctorial_comp_sectionFunctor (f : V.SectionFunctor) {Λ : V.EObj → ℚ≥0}
    (hΛ : IsMorInvariant Λ) :
    C.toGroupoidStr.IsFunctorial (fun α => (Λ (f.toFun α) : ℚ)) := fun φ =>
  congrArg _ (f.comp_eq_of_isomorphic hΛ ⟨φ, rfl, rfl⟩)

/-- **2021 Theorem 18.6.1, "In particular" (p. 861)**, with tame germ data (`hfT`, the standing
reading): for an sc⁺-multisection functor `Λ` with `N(Λ) ≤ 1`, `|dom-supp(Λ)| ⊆ U` and (4) in a
covering model `c`, where `(N, U)` controls compactness, `Θ = Λ ∘ f : C → ℚ⁺` is a **compact, tame,
branched ep⁺-subcategory** (Definitions 17.5.1, 17.5.3 (1), (2)): Theorem 15.3.7's "in
particular" (with Remark 15.3.6) in the model, carried to `C` by Proposition 17.5.2. -/
theorem theorem_18_6_1_in_particular (c : Q.BundleCoveringFamily) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) (hfT : Q.IsScFredholmSectionFunctorTame f)
    {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormFunctor N) {U : Set C.toGroupoidStr.OrbitSpace}
    (hcc : f.ControlsCompactness N U) {Λ : V.EObj → ℚ≥0} (hinv : IsMorInvariant Λ)
    (hΛ : Q.IsScPlusMultisectionIn c.Ψ Λ) (hN1 : ∀ α, pointwiseNormFunctor N Λ α ≤ 1)
    (hdom : orbitDomSupp Λ ⊆ U) (hgp : Q.IsInGeneralPositionIn c.Ψ f Λ) :
    S.IsBranchedSubcategory (fun α => (Λ (f.toFun α) : ℚ)) ∧
      C.IsCompactBranched (fun α => (Λ (f.toFun α) : ℚ)) ∧
      S.IsTameModel (fun α => (Λ (f.toFun α) : ℚ)) := by
  set Θ : C.Obj → ℚ := fun α => (Λ (f.toFun α) : ℚ)
  have hNc := hN c
  have hΘ : C.toGroupoidStr.IsFunctorial Θ := isFunctorial_comp_sectionFunctor f hinv
  have h0 : ∀ α, 0 ≤ Θ α := fun α => by positivity
  have hN1m : ∀ x, pointwiseNorm (Q.modelNorm c.Ψ N) (Q.bundlePull c.Ψ Λ) x ≤ 1 := by
    intro x
    obtain ⟨hnt, heq⟩ := Q.pointwiseNorm_bundlePull hNc hΛ x
    rw [← heq]
    have := (ENNReal.toReal_le_toReal hnt ENNReal.one_ne_top).2 (hN1 _)
    rwa [ENNReal.toReal_one] at this
  have hdomm : domSupp (A := Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ) ⊆
      (Q.modelSEP c.Ψ).X.π ⁻¹' ((S.modelFunctor (Q.modelBase c.Ψ)).orbitMap ⁻¹' U) :=
    fun x hx => hdom (domSupp_model_subset c Λ hx)
  obtain ⟨hB, hK, hTB⟩ := theorem_15_3_7_in_particular_tame_hyp (A := Q.modelSEP c.Ψ)
    (Q.modelFred c.Ψ hf) (Q.modelFredTame c.Ψ hfT) (controlsCompactness_model c hNc hcc) hΛ
    hN1m hdomm hgp
  have hpull := modelPull_comp c f Λ
  refine ⟨(definition_17_5_1_covering c.cover).2 ⟨h0, hΘ,
    (isBranchedEpSubgroupoid_modelPull_iff h0 hΘ).1 ?_⟩, ?_, ⟨c.base, ?_⟩⟩
  · rw [hpull]; exact hB
  · refine (S.isCompactBranched_iff_model c.base hΘ).2 ?_
    change (S.modelEP (Q.modelBase c.Ψ)).X.IsCompactBranched (S.modelPull _ Θ)
    rw [hpull]; exact hK
  · change (S.modelEP (Q.modelBase c.Ψ)).X.IsTameBranched (S.modelPull _ Θ)
    rw [hpull]; exact hTB

/-- **2021 Theorem 18.6.1, pp. 860–861** (all clauses except the orientation), with tame germ
data (`hfT`, the standing reading) and `f` sc-Fredholm (the §18.6 preamble, l. 42415), in a
covering model `c`: over a tame `C` admitting sc-smooth bump
functions, for an sc-Fredholm section functor `f` (tame form) with compact `|S_f|`, an auxiliary
norm `N`, an open `U ⊇ |S_f|` with `(N, U)` controlling compactness and a continuous functor
`h : C → (0, 1]`, there is a structurable sc⁺-multisection functor `Λ` with (1) `N(Λ) < h`,
(2) `|dom-supp(Λ)| ⊆ U`, (3) `T(f, Λ)` onto on `supp(Λ ∘ f)`, (4) general position to `∂C`, and
`Λ ∘ f` is a compact, tame, branched ep⁺-subcategory. -/
theorem theorem_18_6_1 (c : Q.BundleCoveringFamily) (hT : S.IsTame)
    (hbump : S.AdmitsModelBumpFunctions) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) (hfT : Q.IsScFredholmSectionFunctorTame f)
    (hS : f.HasCompactModuliSpace) {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormFunctor N)
    {U : Set C.toGroupoidStr.OrbitSpace} (hcc : f.ControlsCompactness N U) {h : C.Obj → ℝ}
    (hh : S.IsContinuousFunctionFunctor h) (hh01 : ∀ α, 0 < h α ∧ h α ≤ 1) :
    ∃ Λ : V.EObj → ℚ≥0, Q.IsStructurableFunctor Λ ∧
      (∀ α, pointwiseNormFunctor N Λ α < ENNReal.ofReal (h α)) ∧ orbitDomSupp Λ ⊆ U ∧
      Q.IsTransversalIn c.Ψ f Λ ∧ Q.IsInGeneralPositionIn c.Ψ f Λ ∧
      S.IsBranchedSubcategory (fun α => (Λ (f.toFun α) : ℚ)) ∧
      C.IsCompactBranched (fun α => (Λ (f.toFun α) : ℚ)) ∧
      S.IsTameModel (fun α => (Λ (f.toFun α) : ℚ)) := by
  obtain ⟨Λ, hΛ, h1, h2, h3, h4⟩ :=
    theorem_18_6_1_structurable c hT hbump hf hfT hS hN hcc hh hh01
  have hms : Q.IsScPlusMultisectionIn c.Ψ Λ := ((Q.remark_18_3_4 c).1 hΛ).2.1
  refine ⟨Λ, hΛ, h1, h2, h3, h4,
    theorem_18_6_1_in_particular c hf hfT hN hcc hΛ.1 hms (fun α => ?_) h2 h4⟩
  refine (h1 α).le.trans ?_
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (hh01 α).2

/-- **2021 Theorem 18.6.1, last sentence (p. 861)**, with tame germ data (the standing reading)
and the dimension `n` (`hidx`, which the text leaves implicit; Theorem 15.4.3: index `k`): if in
addition `f` is oriented by `o` (Definition 18.5.4), `Θ = Λ ∘ f` is **naturally oriented**: for
an sc⁺-multisection functor `Λ` with `N(Λ) ≤ 1`, `|dom-supp(Λ)| ⊆ U` and (4) in the covering
model `c`, and `f` of index `n` along `supp(Λ ∘ f)` (`hidx`, the index hypothesis of Theorem
15.4.1), there is an oriented branched ep⁺-subcategory `Θ̂ = (Θ, T̂_Θ)` (read through the models,
`OrientedSubcategory`) whose orientation in the model `c` is the canonical orientation
`T̂_((f^Ψ̄, Ψ̄^*o), Γ̄^*Λ)` of Definition 15.4.2 (Theorem 15.4.1 in the model, with the model
orientation `Ψ̄^*o` of Proposition 18.5.6 (2)), and in every other model its pull-back by
`f_{Ψ,Ψ'}` (Theorem 11.3.5). -/
theorem theorem_18_6_1_oriented (c : Q.BundleCoveringFamily) (hT : S.IsTame)
    (hbump : S.AdmitsModelBumpFunctions) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) (hfT : Q.IsScFredholmSectionFunctorTame f)
    (hF : Q.HasStrongBundleUniformizers) {o : Q.OrSection hf hF}
    (ho : Q.IsOrientation hf hbump hT hfT hF o) {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormFunctor N)
    {U : Set C.toGroupoidStr.OrbitSpace} (hcc : f.ControlsCompactness N U) {Λ : V.EObj → ℚ≥0}
    (hinv : IsMorInvariant Λ) (hΛ : Q.IsScPlusMultisectionIn c.Ψ Λ)
    (hN1 : ∀ α, pointwiseNormFunctor N Λ α ≤ 1) (hdom : orbitDomSupp Λ ⊆ U)
    (hgp : Q.IsInGeneralPositionIn c.Ψ f Λ) {n : ℕ}
    (hidx : ∀ x, 0 < Q.bundlePull c.Ψ Λ (Q.modelSection c.Ψ f x) →
      (Q.modelSEP c.Ψ).B.IsIndexAt (Q.modelSection c.Ψ f) x n) :
    ∃ O : S.OrientedSubcategory, O.Θ = (fun α => (Λ (f.toFun α) : ℚ)) ∧
      (∀ x ∈ (Q.modelSEP c.Ψ).X.PObj.smoothSet,
        O.T c.base x = canonicalOrientation (A := Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ)
          (Q.modelFred c.Ψ hf).2 (Q.modelSec hbump c) (Q.pullCat hf hbump hF c o) x) ∧
      IsCanonicalFor (A := Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ) (Q.modelFred c.Ψ hf).2
        (Q.modelSec hbump c) (Q.pullCat hf hbump hF c o) n
        (canonicalOrientation (A := Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ)
          (Q.modelFred c.Ψ hf).2 (Q.modelSec hbump c) (Q.pullCat hf hbump hF c o)) := by
  set Θ : C.Obj → ℚ := fun α => (Λ (f.toFun α) : ℚ)
  obtain ⟨hΘB, -, -⟩ := theorem_18_6_1_in_particular c hf hfT hN hcc hinv hΛ hN1 hdom hgp
  have hmo := Q.isModelOrientation_pullCat hf hbump hT hfT hF ho c
  have hTop := isOrientationTopology_orTopology (A := Q.modelSEP c.Ψ) (Q.modelTame c.Ψ hT)
    (Q.modelBump hbump c) (Q.modelFredTame c.Ψ hfT) (Q.modelSec hbump c)
  have hD := (Q.isModelOrientation_iff hf hbump hT hfT c _).1 hmo _ hTop
  have hgp' : ∀ x : (Q.modelSEP c.Ψ).Obj, x ∈ EpGroupoid.supp (fun z =>
      ((Q.bundlePull c.Ψ Λ (Q.modelSection c.Ψ f z) : ℚ≥0) : ℚ)) →
      SBLocalization.IsGoodPositionAt (A := Q.modelSEP c.Ψ) (Q.modelSection c.Ψ f)
        (Q.bundlePull c.Ψ Λ) x := by
    intro x hx
    have hx' : 0 < Q.bundlePull c.Ψ Λ (Q.modelSection c.Ψ f x) := by exact_mod_cast hx
    exact (remark_15_3_6_goodPosition_hyp (Q.modelFred c.Ψ hf) (Q.modelFredTame c.Ψ hfT) hΛ
      hgp hx').1
  have hidx' : ∀ x : (Q.modelSEP c.Ψ).Obj, x ∈ EpGroupoid.supp (fun z =>
      ((Q.bundlePull c.Ψ Λ (Q.modelSection c.Ψ f z) : ℚ≥0) : ℚ)) →
      (Q.modelSEP c.Ψ).B.IsIndexAt (Q.modelSection c.Ψ f) x n := by
    intro x hx
    exact hidx x (by exact_mod_cast hx)
  have hcan := theorem_15_4_1_of_definition_12_5_4 (Q.modelTame c.Ψ hT) (Q.modelBump hbump c)
    (Q.modelFred c.Ψ hf) (Q.modelFredTame c.Ψ hfT) hΛ (Q.modelSec hbump c) _ hD hgp' hidx'
  have hT₀ : (S.modelEP c.base.Ψ).X.IsOrientation (S.modelPull c.base.Ψ Θ)
      (canonicalOrientation (A := Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ)
        (Q.modelFred c.Ψ hf).2 (Q.modelSec hbump c) (Q.pullCat hf hbump hF c o)) := by
    change (S.modelEP (Q.modelBase c.Ψ)).X.IsOrientation (S.modelPull (Q.modelBase c.Ψ) Θ) _
    rw [modelPull_comp c f Λ]
    exact hcan.1
  have hT₁ := hT₀.smoothPart
  have hmem : (S.modelEP c.base.Ψ).X.smoothPart (canonicalOrientation (A := Q.modelSEP c.Ψ)
      (Q.bundlePull c.Ψ Λ) (Q.modelFred c.Ψ hf).2 (Q.modelSec hbump c)
      (Q.pullCat hf hbump hF c o)) ∈ (S.modelEP c.base.Ψ).X.GrHatSections :=
    ⟨hT₁.isGrHatSection, fun x hx => EpGroupoid.smoothPart_of_notMem hx⟩
  refine ⟨OrientedSubcategory.ofModel S c.base Θ hΘB _ hT₁, rfl, fun x hx => ?_, hcan⟩
  rw [OrientedSubcategory.ofModel_T_self c.base Θ hΘB _ hT₁ hmem]
  exact EpGroupoid.smoothPart_of_mem hx

/-- **§18.6, p. 860, the paragraph after the list (1)–(4), orbifold case**: if moreover
`Λ ∘ f` only takes the values `0` and `1` (orbifold-type, Definition 17.5.4 (2)), `|supp(Θ)|`
is compact and has the structure of an orbifold: in every covering model `supp(Γ^*Θ)` is an
ep-subgroupoid and a smooth submanifold whose orbit space is homeomorphic to `|supp(Θ)|`
through `|Γ|` (Proposition 17.5.5 (2) with the "in particular" of Theorem 18.6.1). -/
theorem perturbation_orbifoldType (c : Q.BundleCoveringFamily) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) (hfT : Q.IsScFredholmSectionFunctorTame f)
    {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormFunctor N) {U : Set C.toGroupoidStr.OrbitSpace}
    (hcc : f.ControlsCompactness N U) {Λ : V.EObj → ℚ≥0} (hinv : IsMorInvariant Λ)
    (hΛ : Q.IsScPlusMultisectionIn c.Ψ Λ) (hN1 : ∀ α, pointwiseNormFunctor N Λ α ≤ 1)
    (hdom : orbitDomSupp Λ ⊆ U) (hgp : Q.IsInGeneralPositionIn c.Ψ f Λ)
    (ho : C.IsOrbifoldTypeBranched (fun α => (Λ (f.toFun α) : ℚ))) :
    C.IsCompactBranched (fun α => (Λ (f.toFun α) : ℚ)) ∧ ∀ c' : S.CoveringFamily,
      ∃ hA : (S.modelEP c'.Ψ).X.IsEpSubgroupoid
          (EpGroupoid.supp (S.modelPull c'.Ψ (fun α => (Λ (f.toFun α) : ℚ)))),
        (S.modelEP c'.Ψ).X.PObj.IsSmoothSubmanifold
          (EpGroupoid.supp (S.modelPull c'.Ψ (fun α => (Λ (f.toFun α) : ℚ)))) ∧
        haveI := (S.modelEP c'.Ψ).X.PObj.paracompactSpace_subtype
          (EpGroupoid.supp (S.modelPull c'.Ψ (fun α => (Λ (f.toFun α) : ℚ))))
        ∃ e : (EpGroupoid.subEpGroupoid hA).OrbitSpace ≃ₜ
            C.toGroupoidStr.orbitSupp (fun α => (Λ (f.toFun α) : ℚ)),
          ∀ x : EpGroupoid.supp (S.modelPull c'.Ψ (fun α => (Λ (f.toFun α) : ℚ))),
            (e ((EpGroupoid.subEpGroupoid hA).π x) : C.toGroupoidStr.OrbitSpace) =
              C.toGroupoidStr.π ((S.modelFunctor c'.Ψ).obj x.1) := by
  obtain ⟨hB, hK, -⟩ := theorem_18_6_1_in_particular c hf hfT hN hcc hinv hΛ hN1 hdom hgp
  exact ⟨hK, (proposition_17_5_5_two hB ho).1⟩

/-- **§18.6, p. 860, the paragraph after the list (1)–(4), manifold case**: if moreover
between any two objects of `supp(Θ)` there is at most one morphism and `Θ` takes the values `0`,
`1` (manifold-type, Definition 17.5.4 (1)), `|supp(Θ)|` is compact and every covering family
induces on it the structure of Proposition 9.1.9 (1) (a smooth manifold with boundary and
corners), any two of them related by the identity as an sc-diffeomorphism (Proposition
17.5.5 (1)). -/
theorem perturbation_manifoldType (c : Q.BundleCoveringFamily) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) (hfT : Q.IsScFredholmSectionFunctorTame f)
    {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormFunctor N) {U : Set C.toGroupoidStr.OrbitSpace}
    (hcc : f.ControlsCompactness N U) {Λ : V.EObj → ℚ≥0} (hinv : IsMorInvariant Λ)
    (hΛ : Q.IsScPlusMultisectionIn c.Ψ Λ) (hN1 : ∀ α, pointwiseNormFunctor N Λ α ≤ 1)
    (hdom : orbitDomSupp Λ ⊆ U) (hgp : Q.IsInGeneralPositionIn c.Ψ f Λ)
    (hm : C.IsManifoldTypeBranched (fun α => (Λ (f.toFun α) : ℚ))) :
    C.IsCompactBranched (fun α => (Λ (f.toFun α) : ℚ)) ∧ ∀ c' : S.CoveringFamily,
      ∃ PZ : MPolyfold ((S.modelEP c'.Ψ).X.orbitSupp
          (S.modelPull c'.Ψ (fun α => (Λ (f.toFun α) : ℚ)))),
        (S.modelEP c'.Ψ).X.IsSuppStructure _ PZ := by
  obtain ⟨hB, hK, -⟩ := theorem_18_6_1_in_particular c hf hfT hN hcc hinv hΛ hN1 hdom hgp
  exact ⟨hK, (proposition_17_5_5_one hB hm).1⟩

end GCT.VectorBundle.StrongPolyfoldBundleConstruction



end Polyfold
