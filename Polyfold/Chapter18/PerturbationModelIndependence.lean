import Polyfold.Chapter18.Perturbation
import Polyfold.Chapter15.TransversalityEquivalence
import Polyfold.Chapter15.RelativeLocalFamilies
import Polyfold.Chapter15.BoundaryExtensionIndependence
import Polyfold.Chapter14.FacePush

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18:
**Theorem 18.6.1** (3), (4) (pp. 860–861) and **Theorem 18.4.4** (p. 855) without a chosen
sc-smooth model, and **Theorem 15.3.9 in the polyfold context** (p. 861, the paragraph after the
proof of Theorem 18.6.1).  Numbers and pages are the 2021 text's.

# Perturbations of section functors, independent of the model

## The text, paraphrased

(Theorem 18.6.1) "(3) `T(f, Λ)` is surjective for objects in `supp(Λ ∘ f)`. (4) For an object in
`supp(Λ ∘ f)` the kernels of the operators `T(f, Λ)(α)` are in general position to `∂C`."
"Proof. This follows directly from Theorem 15.3.7 by studying the question in a smooth model."
(Theorem 18.4.4) the ∂-Extension Theorem for a structurable `Λ : E|∂C → ℚ⁺`, "by using a model".
(p. 861) "We can also easily bring Theorem 15.3.9 into the polyfold context."

## What is formalized

* (3), (4) of Theorem 18.6.1 do not depend on the model: `isTransversalIn_incl_iff`,
  `isInGeneralPositionIn_incl_iff` (Part III's `isTransversal_pullback_iff`,
  `isInGeneralPosition_pullback_iff` along the strong bundle equivalence `bundleIncl`, with
  `pullback_modelSection` and `pullMult_bundleIncl_bundlePull`), and for any two covering
  families **`isTransversalIn_iff`**, **`isInGeneralPositionIn_iff`** (through
  `W_Ψ̄ → W_{Ψ̄ ⊔ Ψ̄'} ← W_Ψ̄'`, the comparison iso of Theorem 17.1.18).
* The model-free predicates `IsTransversalFunctor`, `IsInGeneralPositionFunctor` with
  `isTransversalFunctor_iff`, `isInGeneralPositionFunctor_iff` (one model) and `…_iff_forall`
  (every model); **`theorem_18_6_1_modelFree`**, `theorem_18_6_1_in_particular_modelFree`,
  `theorem_18_6_1_oriented_modelFree`.
* Boundary structurability through the models: `IsBoundaryStructurableIn`,
  `IsBoundaryStructurableFunctor`, `IsBoundaryStructurableIn.of_comparison` (Part III's
  Proposition 14.1.8, class level, which needs no hypothesis beyond the text),
  `isBoundaryStructurableFunctor_iff`; `HasModelMPolyfoldPartitionsOfUnity`;
  **`theorem_18_4_4_modelFree`**.
* The boundary hypothesis of Theorem 15.3.9 under strong bundle equivalences:
  `SBLocalization.isBoundaryFaceOnto_pullback_iff`, `isBoundaryFaceOnto_incl_iff`,
  `isBoundaryFaceOntoIn_iff`; `IsBoundaryFaceOntoFunctor`, `isBoundaryFaceOntoFunctor_iff`.
* **`theorem_15_3_9_categorical`**: Theorem 15.3.9 for strong polyfold bundles.

## Reading

* "`Λ : E|∂C → ℚ⁺` structurable" (Theorems 18.4.4, 15.3.9) is a functor `Λ : E → ℚ⁺` whose
  pull-back to a covering model is structurable over `∂X_Ψ` (Definition 14.1.7); only its values
  over `∂C` enter.
* "`C` admits sc-smooth partitions of unity" in Theorems 18.4.4 and 15.3.9 is read as Theorem
  14.1.9 uses it: the M-polyfold of objects of some covering model admits sc-smooth partitions of
  unity (Definition 5.5.1).  This is the one hypothesis that stays attached to a model: Part III
  compares partitions of unity between models only in the ep-groupoid sense (Definition 7.5.5,
  Proposition 16.1.4 (2), `remark_18_4_2`), and Theorem 14.1.9 needs the M-polyfold sense.  Every
  other hypothesis and conclusion of Theorems 18.4.4 and 15.3.9 is model-free.
* "Continuous functor `β`" (Theorem 18.4.4) and `h` (Theorem 15.3.9) are read as in Theorem
  18.6.1 (`IsContinuousFunctionFunctor`: constant along morphisms, continuous in every
  uniformizer); this gives the continuity of `β ∘ Γ` on every model that `theorem_18_4_4` uses.
* The boundary hypothesis of Theorem 15.3.9 ("`T(f|∂X, Λ)(x)` surjective with respect to
  intersections of local faces for every smooth `x ∈ ∂X`") is Part III's `IsBoundaryFaceOnto`
  read in a model; "(N, U)-admissible over `∂C`" is `|dom-supp(Λ|∂C)| ⊆ U` and `N(Λ) ≤ 1` on `∂C`.
* `theorem_18_6_1_modelFree` uses `F̄(α) ≠ ∅` for every object
  (`HasStrongBundleUniformizers`, the standing reading of §18.5) to have a covering model.
* As in Theorem 18.6.1, `f` is sc-Fredholm (the §18.6 preamble, l. 42415) and carries tame germ
  data (`IsScFredholmSectionFunctorTame`), the standing reading of tame polyfolds (README), as in
  Part III's `theorem_15_3_7_existence` and `theorem_15_3_9`; the index hypothesis `hidx` of the
  oriented form names the dimension the text leaves implicit (Theorem 15.4.3: index `k`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory
open scoped ENNReal

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

variable {A A' : SEP.{u}}

/-- **The boundary hypothesis of Theorem 15.3.9 is invariant under strong bundle equivalences**:
for a strong bundle equivalence `F : W → W'`, an sc-Fredholm section functor `f'` of `W'` and a
functor `Λ' : W' → ℚ⁺`, `(F^* f', F^* Λ')` satisfies `IsBoundaryFaceOnto` iff `(f', Λ')` does.
Extensions of `F^*Λ'` are pushed forward (`F_*`, Lemma 11.5.2) and extensions of `Λ'` pulled back
(Proposition 11.5.3); general position at a point is carried by `isReducedOntoAtLevel_pullback_iff`
and along morphisms by `isReducedOntoAtLevel_of_mor`; `F` preserves `∂X` and `X_∞`. -/
theorem isBoundaryFaceOnto_pullback_iff {F : A ⟶ A'} (hF : SEP.equivalences F)
    {f' : A'.Obj → A'.W} (hf' : A'.E.IsScFredholmSectionFunctor f') {Λ' : A'.W → ℚ≥0}
    (hW : IsWFunctor A' Λ') :
    IsBoundaryFaceOnto ((sbe hF).pullback f') (pullMult F Λ') ↔ IsBoundaryFaceOnto f' Λ' := by
  set M := PullMap.ofEquivalence hF
  have hbd : ∀ a : A.Obj, (SEP.Hom.ϕ F).obj a ∈ A'.X.PObj.boundary ↔ a ∈ A.X.PObj.boundary :=
    fun a => M.mem_boundary_iff a
  have hsm : ∀ a : A.Obj, (SEP.Hom.ϕ F).obj a ∈ A'.X.PObj.smoothSet ↔
      a ∈ A.X.PObj.smoothSet :=
    fun a => M.isLocalScDiffeo_obj.mem_smoothSet_iff a
  have hcov : ∀ w : A.W, A'.P ((SEP.Hom.Φ F).obj w) = (SEP.Hom.ϕ F).obj (A.P w) :=
    fun w => (sbe hF).isStrongBundleFunctor.isMap.isStrongBundleMap.covers w
  have hval : ∀ a : A.Obj, pullMult F Λ' ((sbe hF).pullback f' a) = Λ' (f' ((SEP.Hom.ϕ F).obj a)) :=
    fun a => congrArg Λ' ((sbe hF).obj_pullback hf'.1.1.1 a)
  constructor
  · intro H Λ'' hΛ'' hext x' hx'b hx's hpos
    set y' := A'.X.PObj.levelVal 1 x'
    set a := (sbe hF).preObj y'
    set σ' := (sbe hF).preMor y'
    have hsrc : A'.X.src σ' = (SEP.Hom.ϕ F).obj a := (sbe hF).src_preMor y'
    have htgt : A'.X.tgt σ' = y' := (sbe hF).tgt_preMor y'
    have hϕab : (SEP.Hom.ϕ F).obj a ∈ A'.X.PObj.boundary := by
      rw [← hsrc, mem_boundary_src_iff, htgt]; exact hx'b
    have hϕas : (SEP.Hom.ϕ F).obj a ∈ A'.X.PObj.smoothSet := by
      rw [← hsrc]; exact A'.X.src_mem_smoothSet_of_tgt (htgt ▸ hx's)
    have has : a ∈ A.X.PObj.smoothSet := (hsm a).1 hϕas
    have ha1 : a ∈ A.X.PObj.levelSet 1 := A.X.mem_levelSet_one_of_mem_smoothSet has
    have hϕa1 : (SEP.Hom.ϕ F).obj a ∈ A'.X.PObj.levelSet 1 :=
      A'.X.mem_levelSet_one_of_mem_smoothSet hϕas
    set x := A.X.PObj.levelMk 1 a ha1
    set x'' := A'.X.PObj.levelMk 1 ((SEP.Hom.ϕ F).obj a) hϕa1
    have hx : A.X.PObj.levelVal 1 x = a := A.X.PObj.levelVal_levelMk 1 _ ha1
    have hx'' : A'.X.PObj.levelVal 1 x'' = (SEP.Hom.ϕ F).obj a :=
      A'.X.PObj.levelVal_levelMk 1 _ hϕa1
    have hposa : 0 < pullMult F Λ' ((sbe hF).pullback f' a) := by
      rw [hval, ← hsrc]
      have e : Λ' (f' (A'.X.tgt σ')) = Λ' (f' (A'.X.src σ')) := by
        rw [hf'.1.2 σ']; exact hW _
      rw [← e, htgt]; exact hpos
    have hΛa := isScPlusMultisection_pullMult hF hΛ''
    have hexta : ∀ w, A.P w ∈ A.X.PObj.boundary → pullMult F Λ'' w = pullMult F Λ' w :=
      fun w hw => hext _ (by rw [hcov]; exact (hbd _).2 hw)
    have h1 := H _ hΛa hexta x (by rw [hx]; exact (hbd a).1 hϕab) (by rw [hx]; exact has)
      (by rw [hx]; exact hposa)
    have h2 : IsReducedOntoAtLevel f' Λ'' x'' :=
      (isReducedOntoAtLevel_pullback_iff hF hf' hΛ'' (by rw [hx, hx''])).1 h1
    exact isReducedOntoAtLevel_of_mor hf' hΛ'' σ' (hx''.trans hsrc.symm) htgt.symm h2
  · intro H Λa hΛa hexta x hxb hxs hpos
    set Λ'' := pushMult F hF Λa
    have hΛ'' : IsScPlusMultisection A' Λ'' := lemma_11_5_2_book hF hΛa
    have hext'' : ∀ w', A'.P w' ∈ A'.X.PObj.boundary → Λ'' w' = Λ' w' := by
      intro w' hw'
      set w := ((sbe hF).isEquivalence.exists_iso w').choose
      have hw := π_obj_choose hF w'
      have e1 : Λ'' w' = Λa w := pushMult_eq hF hΛa.1 hw
      have hPw : A.P w ∈ A.X.PObj.boundary := by
        rw [← hbd, ← hcov]; exact mem_boundary_of_π_eq hw.symm hw'
      rw [e1, hexta w hPw]
      exact hW.eq_of_π_eq hw
    set a := A.X.PObj.levelVal 1 x
    have hϕa1 : (SEP.Hom.ϕ F).obj a ∈ A'.X.PObj.levelSet 1 :=
      A'.X.mem_levelSet_one_of_mem_smoothSet ((hsm a).2 hxs)
    set x' := A'.X.PObj.levelMk 1 ((SEP.Hom.ϕ F).obj a) hϕa1
    have hx' : A'.X.PObj.levelVal 1 x' = (SEP.Hom.ϕ F).obj a :=
      A'.X.PObj.levelVal_levelMk 1 _ hϕa1
    have h1 := H Λ'' hΛ'' hext'' x' (by rw [hx']; exact (hbd a).2 hxb)
      (by rw [hx']; exact (hsm a).2 hxs) (by rw [hx', ← hval]; exact hpos)
    have h2 := (isReducedOntoAtLevel_pullback_iff hF hf' hΛ'' hx'.symm).2 h1
    rw [pullMult_pushMult hF hΛa.1] at h2
    exact h2

end SBLocalization

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory.BanachFunctor SBLocalization StrongBundle PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  {Q : V.StrongPolyfoldBundleConstruction S}

/-- `incl^*(Γ̄_Φ̄^*Λ) = Γ̄_Ψ̄^*Λ` for the inclusion `W_Ψ̄ → W_Φ̄` of a family `Ψ̄ = Φ̄ ∘ σ`
(`Γ̄_Φ̄ ∘ incl = Γ̄_Ψ̄`). -/
theorem pullMult_bundleIncl_bundlePull {κ ι : Type u} {Ψb : κ → Q.Unif} {Φb : ι → Q.Unif}
    {σ : κ → ι} (h : Φb ∘ σ = Ψb) {β : Type*} (Λ : V.EObj → β) :
    pullMult (Q.bundleIncl Ψb Φb σ h) (Q.bundlePull Φb Λ) = Q.bundlePull Ψb Λ := by
  funext w
  change Λ ((Q.bundleModelFunctor Φb).obj ((SEP.Hom.Φ (Q.bundleIncl Ψb Φb σ h)).obj w)) =
    Λ ((Q.bundleModelFunctor Ψb).obj w)
  rw [← Q.bundleModelFunctor_comp_bundleIncl h]
  rfl

/-- **(3) of Theorem 18.6.1 along an inclusion of covering families**: for `Ψ̄ = Φ̄ ∘ σ`,
`(f^Ψ̄, Γ̄_Ψ̄^*Λ)` is transversal iff `(f^Φ̄, Γ̄_Φ̄^*Λ)` is (Part III's
`isTransversal_pullback_iff` along the strong bundle equivalence `bundleIncl`). -/
theorem isTransversalIn_incl_iff {c d : Q.BundleCoveringFamily} (σ : c.ι → d.ι)
    (h : d.Ψ ∘ σ = c.Ψ) {f : V.SectionFunctor} (hf : Q.IsScFredholmSectionFunctor f)
    {Λ : V.EObj → ℚ≥0} (hΛ : Q.IsScPlusMultisectionIn d.Ψ Λ) :
    Q.IsTransversalIn c.Ψ f Λ ↔ Q.IsTransversalIn d.Ψ f Λ := by
  have hΨ := Q.equivalences_bundleIncl h c.cover
  have e := isTransversal_pullback_iff hΨ (Q.modelFred d.Ψ hf) hΛ
  rw [Q.pullback_modelSection f d.Ψ h c.cover, pullMult_bundleIncl_bundlePull h] at e
  exact e

/-- **(4) of Theorem 18.6.1 along an inclusion of covering families**: for `Ψ̄ = Φ̄ ∘ σ`,
`(f^Ψ̄, Γ̄_Ψ̄^*Λ)` is in general position iff `(f^Φ̄, Γ̄_Φ̄^*Λ)` is (Part III's
`isInGeneralPosition_pullback_iff` along `bundleIncl`). -/
theorem isInGeneralPositionIn_incl_iff {c d : Q.BundleCoveringFamily} (σ : c.ι → d.ι)
    (h : d.Ψ ∘ σ = c.Ψ) {f : V.SectionFunctor} (hf : Q.IsScFredholmSectionFunctor f)
    {Λ : V.EObj → ℚ≥0} (hΛ : Q.IsScPlusMultisectionIn d.Ψ Λ) :
    Q.IsInGeneralPositionIn c.Ψ f Λ ↔ Q.IsInGeneralPositionIn d.Ψ f Λ := by
  have hΨ := Q.equivalences_bundleIncl h c.cover
  have e := isInGeneralPosition_pullback_iff hΨ (Q.modelFred d.Ψ hf) hΛ
  rw [Q.pullback_modelSection f d.Ψ h c.cover, pullMult_bundleIncl_bundlePull h] at e
  exact e

/-- **(3) of Theorem 18.6.1 does not depend on the model**: for an sc-Fredholm section functor
`f` and an sc⁺-multisection functor `Λ`, `T(f, Λ)` is onto on `supp(Λ ∘ f)` in the model of
`Ψ̄` iff it is in the model of `Ψ̄'` (through `W_Ψ̄ → W_{Ψ̄ ⊔ Ψ̄'} ← W_Ψ̄'`, which represents the
comparison iso `f̄_{Ψ̄,Ψ̄'}` of Theorem 17.1.18). -/
theorem isTransversalIn_iff (c c' : Q.BundleCoveringFamily) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) {Λ : V.EObj → ℚ≥0}
    (hΛ : Q.IsScPlusMultisectionFunctor Λ) :
    Q.IsTransversalIn c.Ψ f Λ ↔ Q.IsTransversalIn c'.Ψ f Λ := by
  have hΛs := ((Q.remark_18_3_2 (Q.sumFamily c c')).1 hΛ).2
  exact (isTransversalIn_incl_iff (d := Q.sumFamily c c') Sum.inl rfl hf hΛs).trans
    (isTransversalIn_incl_iff (d := Q.sumFamily c c') Sum.inr rfl hf hΛs).symm

/-- **(4) of Theorem 18.6.1 does not depend on the model**: general position of
`(f^Ψ̄, Γ̄^*Λ)` for one covering family is equivalent to that for any other. -/
theorem isInGeneralPositionIn_iff (c c' : Q.BundleCoveringFamily) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) {Λ : V.EObj → ℚ≥0}
    (hΛ : Q.IsScPlusMultisectionFunctor Λ) :
    Q.IsInGeneralPositionIn c.Ψ f Λ ↔ Q.IsInGeneralPositionIn c'.Ψ f Λ := by
  have hΛs := ((Q.remark_18_3_2 (Q.sumFamily c c')).1 hΛ).2
  exact (isInGeneralPositionIn_incl_iff (d := Q.sumFamily c c') Sum.inl rfl hf hΛs).trans
    (isInGeneralPositionIn_incl_iff (d := Q.sumFamily c c') Sum.inr rfl hf hΛs).symm


/-- `Γ̄^*Λ(f^Ψ̄(x)) = Λ(f(Γ x))` ((18.3)). -/
theorem bundlePull_modelSection_eq (c : Q.BundleCoveringFamily) (f : V.SectionFunctor)
    {β : Type*} (Λ : V.EObj → β) (x : S.ModelObj (Q.modelBase c.Ψ)) :
    Q.bundlePull c.Ψ Λ (Q.modelSection c.Ψ f x) =
      Λ (f.toFun ((S.modelFunctor (Q.modelBase c.Ψ)).obj x)) := by
  change Λ ((Q.bundleModelFunctor c.Ψ).obj (Q.modelSection c.Ψ f x)) = _
  rw [Q.bundleModelFunctor_obj_modelSection]

/-- `x ∈ ∂X_Ψ` iff `Γ(x) ∈ ∂C` (Definition 17.1.30: `d_{X_Ψ}(x) = d(Γ x)`). -/
theorem mem_boundary_model_iff_obj (c : Q.BundleCoveringFamily)
    (x : S.ModelObj (Q.modelBase c.Ψ)) :
    x ∈ (Q.modelSEP c.Ψ).X.PObj.boundary ↔
      (S.modelFunctor (Q.modelBase c.Ψ)).obj x ∈ S.boundarySet := by
  change 1 ≤ _ ↔ 1 ≤ _
  rw [degIndex_modelFunctor_obj]
  rfl


/-- The boundary hypothesis of Theorem 15.3.9 along an inclusion of covering families
(`isBoundaryFaceOnto_pullback_iff` for `bundleIncl`). -/
theorem isBoundaryFaceOnto_incl_iff {c d : Q.BundleCoveringFamily} (σ : c.ι → d.ι)
    (h : d.Ψ ∘ σ = c.Ψ) {f : V.SectionFunctor} (hf : Q.IsScFredholmSectionFunctor f)
    {Λ : V.EObj → ℚ≥0} (hΛ : IsMorInvariant Λ) :
    IsBoundaryFaceOnto (A := Q.modelSEP c.Ψ) (Q.modelSection c.Ψ f) (Q.bundlePull c.Ψ Λ) ↔
      IsBoundaryFaceOnto (A := Q.modelSEP d.Ψ) (Q.modelSection d.Ψ f) (Q.bundlePull d.Ψ Λ) := by
  have e := isBoundaryFaceOnto_pullback_iff (Q.equivalences_bundleIncl h c.cover)
    (Q.modelFred d.Ψ hf) (Q.isWFunctor_bundlePull d.Ψ hΛ)
  rw [Q.pullback_modelSection f d.Ψ h c.cover, pullMult_bundleIncl_bundlePull h] at e
  exact e


/-- **The boundary hypothesis of Theorem 15.3.9 does not depend on the model**: for a functor
`Λ`, `(f^Ψ̄, Γ̄^*Λ)` satisfies `IsBoundaryFaceOnto` for one covering family iff for any other. -/
theorem isBoundaryFaceOntoIn_iff (c c' : Q.BundleCoveringFamily) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) {Λ : V.EObj → ℚ≥0} (hΛ : IsMorInvariant Λ) :
    IsBoundaryFaceOnto (A := Q.modelSEP c.Ψ) (Q.modelSection c.Ψ f) (Q.bundlePull c.Ψ Λ) ↔
      IsBoundaryFaceOnto (A := Q.modelSEP c'.Ψ) (Q.modelSection c'.Ψ f) (Q.bundlePull c'.Ψ Λ) :=
  (isBoundaryFaceOnto_incl_iff (d := Q.sumFamily c c') Sum.inl rfl hf hΛ).trans
    (isBoundaryFaceOnto_incl_iff (d := Q.sumFamily c c') Sum.inr rfl hf hΛ).symm

variable (Q) in
/-- **(3) of Theorem 18.6.1, model-free** ("`T(f, Λ)` is surjective for objects in
`supp(Λ ∘ f)`", 2021 p. 860): transversal in an sc-smooth model.  By `isTransversalFunctor_iff`
it is equivalent to transversality in any given model. -/
def IsTransversalFunctor (f : V.SectionFunctor) (Λ : V.EObj → ℚ≥0) : Prop :=
  ∃ c : Q.BundleCoveringFamily, Q.IsTransversalIn c.Ψ f Λ

variable (Q) in
/-- **(4) of Theorem 18.6.1, model-free** ("the kernels of `T(f, Λ)(α)` are in general position
to `∂C`", 2021 p. 861): in general position in an sc-smooth model; by
`isInGeneralPositionFunctor_iff` equivalent to general position in any given model. -/
def IsInGeneralPositionFunctor (f : V.SectionFunctor) (Λ : V.EObj → ℚ≥0) : Prop :=
  ∃ c : Q.BundleCoveringFamily, Q.IsInGeneralPositionIn c.Ψ f Λ

variable (Q) in
/-- **The boundary hypothesis of Theorem 15.3.9 in the polyfold context** (p. 861, "bring
Theorem 15.3.9 into the polyfold context"): `T(f|∂C, Λ)(α)` is surjective with respect to
intersections of local faces at every smooth `α ∈ ∂C`, read in an sc-smooth model as Part III's
`IsBoundaryFaceOnto`; by `isBoundaryFaceOntoFunctor_iff` the model does not matter. -/
def IsBoundaryFaceOntoFunctor (f : V.SectionFunctor) (Λ : V.EObj → ℚ≥0) : Prop :=
  ∃ c : Q.BundleCoveringFamily,
    IsBoundaryFaceOnto (A := Q.modelSEP c.Ψ) (Q.modelSection c.Ψ f) (Q.bundlePull c.Ψ Λ)

/-- (3) of Theorem 18.6.1 holds model-free iff it holds in the model `c`. -/
theorem isTransversalFunctor_iff (c : Q.BundleCoveringFamily) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) {Λ : V.EObj → ℚ≥0}
    (hΛ : Q.IsScPlusMultisectionFunctor Λ) :
    Q.IsTransversalFunctor f Λ ↔ Q.IsTransversalIn c.Ψ f Λ :=
  ⟨fun ⟨_, h'⟩ => (isTransversalIn_iff _ _ hf hΛ).1 h', fun h => ⟨c, h⟩⟩

/-- (4) of Theorem 18.6.1 holds model-free iff it holds in the model `c`. -/
theorem isInGeneralPositionFunctor_iff (c : Q.BundleCoveringFamily) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) {Λ : V.EObj → ℚ≥0}
    (hΛ : Q.IsScPlusMultisectionFunctor Λ) :
    Q.IsInGeneralPositionFunctor f Λ ↔ Q.IsInGeneralPositionIn c.Ψ f Λ :=
  ⟨fun ⟨_, h'⟩ => (isInGeneralPositionIn_iff _ _ hf hΛ).1 h', fun h => ⟨c, h⟩⟩

/-- (3) of Theorem 18.6.1 model-free is (3) in every covering model. -/
theorem isTransversalFunctor_iff_forall {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) {Λ : V.EObj → ℚ≥0}
    (hΛ : Q.IsScPlusMultisectionFunctor Λ) :
    Q.IsTransversalFunctor f Λ ↔ ∀ c : Q.BundleCoveringFamily, Q.IsTransversalIn c.Ψ f Λ :=
  ⟨fun h c => (isTransversalFunctor_iff c hf hΛ).1 h, fun h => ⟨hΛ.2.choose, h _⟩⟩

/-- (4) of Theorem 18.6.1 model-free is (4) in every covering model. -/
theorem isInGeneralPositionFunctor_iff_forall {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) {Λ : V.EObj → ℚ≥0}
    (hΛ : Q.IsScPlusMultisectionFunctor Λ) :
    Q.IsInGeneralPositionFunctor f Λ ↔
      ∀ c : Q.BundleCoveringFamily, Q.IsInGeneralPositionIn c.Ψ f Λ :=
  ⟨fun h c => (isInGeneralPositionFunctor_iff c hf hΛ).1 h, fun h => ⟨hΛ.2.choose, h _⟩⟩

/-- The boundary hypothesis of Theorem 15.3.9 holds model-free iff it holds in the model `c`. -/
theorem isBoundaryFaceOntoFunctor_iff (c : Q.BundleCoveringFamily) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) {Λ : V.EObj → ℚ≥0} (hΛ : IsMorInvariant Λ) :
    Q.IsBoundaryFaceOntoFunctor f Λ ↔
      IsBoundaryFaceOnto (A := Q.modelSEP c.Ψ) (Q.modelSection c.Ψ f) (Q.bundlePull c.Ψ Λ) :=
  ⟨fun ⟨_, h'⟩ => (isBoundaryFaceOntoIn_iff _ _ hf hΛ).1 h', fun h => ⟨c, h⟩⟩

/-! ### Boundary structurability -/

variable (Q) in
/-- `Γ̄_Ψ̄^*Λ` is structurable over `∂X_Ψ` (Definition 14.1.7) in the model of `Ψ̄`. -/
def IsBoundaryStructurableIn {ι : Type u} (Ψb : ι → Q.Unif) (Λ : V.EObj → ℚ≥0) : Prop :=
  IsBoundaryStructurable (Q.modelSEP Ψb) (Q.bundlePull Ψb Λ)

variable (Q) in
/-- **A structurable sc⁺-multisection functor `Λ : E|∂C → ℚ⁺`** (Theorem 18.4.4, 2021 p. 855):
a functor `Λ : E → ℚ⁺` (only its values over `∂C` enter) whose pull-back to an sc-smooth model
is structurable over the boundary (Definition 14.1.7).  By `isBoundaryStructurableFunctor_iff`
the model does not matter (Proposition 14.1.8). -/
def IsBoundaryStructurableFunctor (Λ : V.EObj → ℚ≥0) : Prop :=
  IsMorInvariant Λ ∧ ∃ c : Q.BundleCoveringFamily, Q.IsBoundaryStructurableIn c.Ψ Λ

/-- **Boundary structurability does not depend on the model** (Proposition 14.1.8, class level,
`GenSBMap.proposition_14_1_8_pullMult`, for the comparison iso `f̄_{Ψ̄,Ψ̄'}` of Theorem 17.1.18
between models over the tame `X_Ψ`). -/
theorem IsBoundaryStructurableIn.of_comparison (hT : S.IsTame) {Λ : V.EObj → ℚ≥0}
    (hΛ : IsMorInvariant Λ) (c c' : Q.BundleCoveringFamily)
    (h : Q.IsBoundaryStructurableIn c'.Ψ Λ) : Q.IsBoundaryStructurableIn c.Ψ Λ := by
  unfold IsBoundaryStructurableIn
  rw [bundlePull_eq_pullMult hΛ c c']
  exact GenSBMap.proposition_14_1_8_pullMult _
    (S.isTame_modelEpGroupoid (Ψ := Q.modelBase c.Ψ) hT) h

/-- For tame `C` and every covering family `c`: `Λ` is a structurable sc⁺-multisection functor
over `∂C` iff it is a functor and `Γ̄_c^*Λ` is structurable over `∂X_c`. -/
theorem isBoundaryStructurableFunctor_iff (hT : S.IsTame) (c : Q.BundleCoveringFamily)
    {Λ : V.EObj → ℚ≥0} :
    Q.IsBoundaryStructurableFunctor Λ ↔ IsMorInvariant Λ ∧ Q.IsBoundaryStructurableIn c.Ψ Λ :=
  ⟨fun ⟨hΛ, c', h⟩ => ⟨hΛ, h.of_comparison hT hΛ c c'⟩, fun ⟨hΛ, h⟩ => ⟨hΛ, c, h⟩⟩

variable (Q) in
/-- **"`C` admits sc-smooth partitions of unity" as Theorem 14.1.9 uses it** (Theorems 18.4.4 and
15.3.9 in the polyfold context): the M-polyfold of objects of some covering model `X_Ψ` admits
sc-smooth partitions of unity (Definition 5.5.1).  It implies Definition 18.4.1
(`remark_18_4_2`); Part III does not compare the M-polyfold notion between two models. -/
def HasModelMPolyfoldPartitionsOfUnity : Prop :=
  ∃ c : Q.BundleCoveringFamily, (Q.modelSEP c.Ψ).X.PObj.AdmitsScPartitionsOfUnity

/-- **2021 Theorem 18.4.4, p. 855 (∂-Extension Theorem), model-free form**: over a tame `C`
whose objects admit sc-smooth partitions of unity in some covering model, for an auxiliary norm
`N`, a structurable sc⁺-multisection functor `Λ : E|∂C → ℚ⁺` (in any model,
`IsBoundaryStructurableFunctor`), an open `V ⊇ |dom-supp(Λ)|` and a continuous functor
`β : C → [0, ∞)` with `|supp β| ⊂ V` and `N(Λ) < β` on `dom-supp(Λ)`, there is a structurable
`Λ' : E → ℚ⁺` with (1) `N(Λ') ≤ β`, (2) `|dom-supp(Λ')| ⊂ V`, (3) `Λ' = Λ` on `E|∂C`.
`theorem_18_4_4` in the model with partitions of unity, after moving the boundary
structurability of `Λ` to that model (Proposition 14.1.8). -/
theorem theorem_18_4_4_modelFree (hT : S.IsTame) (hPU : Q.HasModelMPolyfoldPartitionsOfUnity)
    {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormFunctor N) {Λ : V.EObj → ℚ≥0}
    (hΛ : Q.IsBoundaryStructurableFunctor Λ)
    {U : Set C.toGroupoidStr.OrbitSpace} (hUo : IsOpen U)
    (hΛU : orbitBoundaryDomSupp S Λ ⊆ U) {β : C.Obj → ℝ} (hβ : S.IsContinuousFunctionFunctor β)
    (hβ0 : ∀ α, 0 ≤ β α) (hβU : closure (C.toGroupoidStr.π '' {α | β α ≠ 0}) ⊆ U)
    (hNβ : ∀ α, C.toGroupoidStr.π α ∈ orbitBoundaryDomSupp S Λ →
      pointwiseNormFunctor N Λ α < ENNReal.ofReal (β α)) :
    ∃ Λ' : V.EObj → ℚ≥0, Q.IsStructurableFunctor Λ' ∧
      (∀ α, pointwiseNormFunctor N Λ' α ≤ ENNReal.ofReal (β α)) ∧
      orbitDomSupp Λ' ⊆ U ∧ ∀ e : V.EObj, V.base e ∈ S.boundarySet → Λ' e = Λ e := by
  obtain ⟨c, hc⟩ := hPU
  exact Q.theorem_18_4_4 c hT hc (hN c) hΛ.1 ((isBoundaryStructurableFunctor_iff hT c).1 hΛ).2
    hUo hΛU hβ.1 hβ0 (hβ.continuous_model _) hβU hNβ

/-! ### Theorem 18.6.1, model-free -/

/-- **2021 Theorem 18.6.1, pp. 860–861, model-free form** (all clauses except the orientation),
with tame germ data (`hfT`, the standing reading): under the hypotheses of Theorem 18.6.1 and
`F̄(α) ≠ ∅` for every object (the standing reading `HasStrongBundleUniformizers`, which provides a
covering model), there is a structurable sc⁺-multisection functor `Λ` with (1) `N(Λ) < h`,
(2) `|dom-supp(Λ)| ⊆ U`, (3) `T(f, Λ)` onto on `supp(Λ ∘ f)` and (4) general position to `∂C`,
(3) and (4) in every model (`isTransversalFunctor_iff_forall`,
`isInGeneralPositionFunctor_iff_forall`), and `Λ ∘ f` a compact, tame, branched
ep⁺-subcategory. -/
theorem theorem_18_6_1_modelFree (hF : Q.HasStrongBundleUniformizers) (hT : S.IsTame)
    (hbump : S.AdmitsModelBumpFunctions) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) (hfT : Q.IsScFredholmSectionFunctorTame f)
    (hS : f.HasCompactModuliSpace) {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormFunctor N)
    {U : Set C.toGroupoidStr.OrbitSpace} (hcc : f.ControlsCompactness N U) {h : C.Obj → ℝ}
    (hh : S.IsContinuousFunctionFunctor h) (hh01 : ∀ α, 0 < h α ∧ h α ≤ 1) :
    ∃ Λ : V.EObj → ℚ≥0, Q.IsStructurableFunctor Λ ∧
      (∀ α, pointwiseNormFunctor N Λ α < ENNReal.ofReal (h α)) ∧ orbitDomSupp Λ ⊆ U ∧
      Q.IsTransversalFunctor f Λ ∧ Q.IsInGeneralPositionFunctor f Λ ∧
      S.IsBranchedSubcategory (fun α => (Λ (f.toFun α) : ℚ)) ∧
      C.IsCompactBranched (fun α => (Λ (f.toFun α) : ℚ)) ∧
      S.IsTameModel (fun α => (Λ (f.toFun α) : ℚ)) := by
  obtain ⟨Λ, hΛ, h1, h2, h3, h4, h5⟩ :=
    theorem_18_6_1 (Q.refCoveringFamily hF) hT hbump hf hfT hS hN hcc hh hh01
  exact ⟨Λ, hΛ, h1, h2, ⟨_, h3⟩, ⟨_, h4⟩, h5⟩

/-- **2021 Theorem 18.6.1, "In particular" (p. 861), model-free form**: for an sc⁺-multisection
functor `Λ` with `N(Λ) ≤ 1`, `|dom-supp(Λ)| ⊆ U` and (4) (in any model), `Λ ∘ f` is a compact,
tame, branched ep⁺-subcategory. -/
theorem theorem_18_6_1_in_particular_modelFree {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) (hfT : Q.IsScFredholmSectionFunctorTame f)
    {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormFunctor N) {U : Set C.toGroupoidStr.OrbitSpace}
    (hcc : f.ControlsCompactness N U) {Λ : V.EObj → ℚ≥0}
    (hΛ : Q.IsScPlusMultisectionFunctor Λ) (hN1 : ∀ α, pointwiseNormFunctor N Λ α ≤ 1)
    (hdom : orbitDomSupp Λ ⊆ U) (hgp : Q.IsInGeneralPositionFunctor f Λ) :
    S.IsBranchedSubcategory (fun α => (Λ (f.toFun α) : ℚ)) ∧
      C.IsCompactBranched (fun α => (Λ (f.toFun α) : ℚ)) ∧
      S.IsTameModel (fun α => (Λ (f.toFun α) : ℚ)) := by
  obtain ⟨c, hc⟩ := hgp
  exact theorem_18_6_1_in_particular c hf hfT hN hcc hΛ.1 ((Q.remark_18_3_2 c).1 hΛ).2 hN1
    hdom hc

/-- **2021 Theorem 18.6.1, last sentence (p. 861), with (4) model-free**: as
`theorem_18_6_1_oriented`, with `Λ` an sc⁺-multisection functor and (4) in any model; the
orientation is then described in every covering model `c` (the index hypothesis `hidx` is read
in `c`). -/
theorem theorem_18_6_1_oriented_modelFree (c : Q.BundleCoveringFamily) (hT : S.IsTame)
    (hbump : S.AdmitsModelBumpFunctions) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) (hfT : Q.IsScFredholmSectionFunctorTame f)
    (hF : Q.HasStrongBundleUniformizers) {o : Q.OrSection hf hF}
    (ho : Q.IsOrientation hf hbump hT hfT hF o) {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormFunctor N)
    {U : Set C.toGroupoidStr.OrbitSpace} (hcc : f.ControlsCompactness N U) {Λ : V.EObj → ℚ≥0}
    (hΛ : Q.IsScPlusMultisectionFunctor Λ)
    (hN1 : ∀ α, pointwiseNormFunctor N Λ α ≤ 1) (hdom : orbitDomSupp Λ ⊆ U)
    (hgp : Q.IsInGeneralPositionFunctor f Λ) {n : ℕ}
    (hidx : ∀ x, 0 < Q.bundlePull c.Ψ Λ (Q.modelSection c.Ψ f x) →
      (Q.modelSEP c.Ψ).B.IsIndexAt (Q.modelSection c.Ψ f) x n) :
    ∃ O : S.OrientedSubcategory, O.Θ = (fun α => (Λ (f.toFun α) : ℚ)) ∧
      (∀ x ∈ (Q.modelSEP c.Ψ).X.PObj.smoothSet,
        O.T c.base x = canonicalOrientation (A := Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ)
          (Q.modelFred c.Ψ hf).2 (Q.modelSec hbump c) (Q.pullCat hf hbump hF c o) x) ∧
      IsCanonicalFor (A := Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ) (Q.modelFred c.Ψ hf).2
        (Q.modelSec hbump c) (Q.pullCat hf hbump hF c o) n
        (canonicalOrientation (A := Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ)
          (Q.modelFred c.Ψ hf).2 (Q.modelSec hbump c) (Q.pullCat hf hbump hF c o)) :=
  theorem_18_6_1_oriented c hT hbump hf hfT hF ho hN hcc hΛ.1 ((Q.remark_18_3_2 c).1 hΛ).2
    hN1 hdom ((isInGeneralPositionFunctor_iff c hf hΛ).1 hgp) hidx

/-! ### Theorem 15.3.9 in the polyfold context -/

/-- **Theorem 15.3.9 (Transversal Extension Theorem) in the polyfold context** (2021 p. 861, "We
can also easily bring Theorem 15.3.9 into the polyfold context"), with tame germ data (`hfT`, the
standing reading). Over a tame `C` whose objects admit sc-smooth partitions of unity in some
covering model, let `f` be an sc-Fredholm section functor (tame form) with compact `|S_f|`, `N` an
auxiliary norm and `U` with `(N, U)` controlling compactness, `Λ : E|∂C → ℚ⁺` structurable
(`IsBoundaryStructurableFunctor`) and `(N, U)`-admissible over `∂C` (`|dom-supp(Λ|∂C)| ⊆ U`,
`N(Λ) ≤ 1` on `∂C`), `h : C → (0, 1]` a continuous functor with `N(Λ) < h` on `∂C`, and
`T(f|∂C, Λ)` surjective with respect to intersections of local faces at the smooth objects of
`∂C` (`IsBoundaryFaceOntoFunctor`).  Then there is a structurable sc⁺-multisection functor `Λ'`
with (1) `Λ' = Λ` on `E|∂C`, (2) `|dom-supp(Λ')| ⊆ U` and `N(Λ') < h`, (3) `T(f, Λ')` onto on
`supp(Λ' ∘ f)` (in every model), and `Λ' ∘ f` a compact branched ep⁺-subcategory.  Proof:
Part III's `theorem_15_3_9` in the model with partitions of unity, the hypotheses moved there by
`isBoundaryStructurableFunctor_iff` and `isBoundaryFaceOntoFunctor_iff`, and the push-forward
`Γ̄_*` of the model multisection. -/
theorem theorem_15_3_9_categorical (hT : S.IsTame)
    (hPU : Q.HasModelMPolyfoldPartitionsOfUnity) {f : V.SectionFunctor}
    (hf : Q.IsScFredholmSectionFunctor f) (hfT : Q.IsScFredholmSectionFunctorTame f)
    (hS : f.HasCompactModuliSpace) {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormFunctor N)
    {U : Set C.toGroupoidStr.OrbitSpace} (hcc : f.ControlsCompactness N U)
    {Λ : V.EObj → ℚ≥0} (hΛ : Q.IsBoundaryStructurableFunctor Λ)
    (hdomU : orbitBoundaryDomSupp S Λ ⊆ U)
    (hN1 : ∀ α ∈ S.boundarySet, pointwiseNormFunctor N Λ α ≤ 1) {h : C.Obj → ℝ}
    (hh : S.IsContinuousFunctionFunctor h) (hh01 : ∀ α, 0 < h α ∧ h α ≤ 1)
    (hNh : ∀ α ∈ S.boundarySet, pointwiseNormFunctor N Λ α < ENNReal.ofReal (h α))
    (hon : Q.IsBoundaryFaceOntoFunctor f Λ) :
    ∃ Λ' : V.EObj → ℚ≥0, Q.IsStructurableFunctor Λ' ∧
      (∀ e : V.EObj, V.base e ∈ S.boundarySet → Λ' e = Λ e) ∧ orbitDomSupp Λ' ⊆ U ∧
      (∀ α, pointwiseNormFunctor N Λ' α < ENNReal.ofReal (h α)) ∧
      Q.IsTransversalFunctor f Λ' ∧
      S.IsBranchedSubcategory (fun α => (Λ' (f.toFun α) : ℚ)) ∧
      C.IsCompactBranched (fun α => (Λ' (f.toFun α) : ℚ)) := by
  obtain ⟨c, hc⟩ := hPU
  set A := Q.modelSEP c.Ψ
  set Γ := S.modelFunctor (Q.modelBase c.Ψ)
  have hNc := hN c
  have hΛc : IsBoundaryStructurable A (Q.bundlePull c.Ψ Λ) :=
    ((isBoundaryStructurableFunctor_iff hT c).1 hΛ).2
  have honc := (isBoundaryFaceOntoFunctor_iff c hf hΛ.1).1 hon
  have hdom : boundaryDomSupp (A := A) (Q.bundlePull c.Ψ Λ) ⊆
      A.X.π ⁻¹' (Γ.orbitMap ⁻¹' U) :=
    fun x hx => hdomU (Q.mem_orbitBoundaryDomSupp_of_model c Λ hx)
  have hN1m : ∀ x ∈ A.X.PObj.boundary,
      pointwiseNorm (A := A) (Q.modelNorm c.Ψ N) (Q.bundlePull c.Ψ Λ) x ≤ 1 := by
    intro x hx
    have h1 := hN1 _ ((mem_boundary_model_iff_obj c x).1 hx)
    have hne := ne_top_of_le_ne_top ENNReal.one_ne_top h1
    rw [← Q.pointwiseNorm_bundlePull_of_ne_top hNc Λ x hne]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])
  have hNhm : ∀ x ∈ A.X.PObj.boundary,
      pointwiseNorm (A := A) (Q.modelNorm c.Ψ N) (Q.bundlePull c.Ψ Λ) x < h (Γ.obj x) := by
    intro x hx
    have h1 := hNh _ ((mem_boundary_model_iff_obj c x).1 hx)
    have hne := ne_top_of_lt h1
    rw [← Q.pointwiseNorm_bundlePull_of_ne_top hNc Λ x hne]
    exact (ENNReal.lt_ofReal_iff_toReal_lt hne).1 h1
  obtain ⟨Λm, hΛm, hbd, hdomm, hle, -, htr, hB, hK⟩ := theorem_15_3_9 (A := A)
    (S.isTame_modelEpGroupoid (Ψ := Q.modelBase c.Ψ) hT) (Q.hasParacompactOrbitSpace_model c) hc
    (Q.modelSection c.Ψ f) (Q.modelFred c.Ψ hf) (Q.modelFredTame c.Ψ hfT)
    ((Q.isCompact_zeroSet_iff c.Ψ f c.cover).1 hS) (Q.modelNorm c.Ψ N) _
    (controlsCompactness_model c hNc hcc) _ hΛc hdom hN1m (h ∘ Γ.obj) (hh.continuous_model _)
    (hh.mor_model _) (fun x => hh01 _) hNhm honc
  obtain ⟨Λ', hinv, hpull, h1, h2⟩ := exists_push_of_model c hNc hh hΛm.1 hle hdomm
  set Θ : C.Obj → ℚ := fun α => (Λ' (f.toFun α) : ℚ)
  have hΘ : C.toGroupoidStr.IsFunctorial Θ := isFunctorial_comp_sectionFunctor f hinv
  have h0 : ∀ α, 0 ≤ Θ α := fun α => by positivity
  have hpullΘ := modelPull_comp c f Λ'
  refine ⟨Λ', ⟨hinv, c, ?_⟩, ?_, h2, h1, ⟨c, ?_⟩, ?_, ?_⟩
  · unfold IsStructurableIn; rw [hpull]; exact hΛm
  · intro e he
    obtain ⟨z, hz⟩ := (isHomeomorph_bundleModelOrbitMap c.cover).surjective (V.groupoid.π e)
    induction z using Quotient.inductionOn with
    | h w =>
    have hwe : V.groupoid.Isomorphic (Q.bundleModelObj c.Ψ w) e :=
      V.groupoid.π_eq_π_iff.1 hz
    rw [← hinv.eq_of_isomorphic hwe, ← hΛ.1.eq_of_isomorphic hwe]
    have hPw : A.P w ∈ A.X.PObj.boundary := by
      refine (Q.mem_boundary_model_iff c _).2 ⟨V.base e, he, ?_⟩
      obtain ⟨a, has, hat⟩ := hwe
      have h1 : C.toGroupoidStr.src a.φ = V.base (Q.bundleModelObj c.Ψ w) :=
        a.2.symm.trans (congrArg V.base has)
      have h2 : C.toGroupoidStr.tgt a.φ = V.base e := congrArg V.base hat
      have h3 : V.base (Q.bundleModelObj c.Ψ w) = Γ.obj (A.P w) := by
        rw [Q.bundleModelObj_eq_objMk c.Ψ w]; rfl
      refine (C.toGroupoidStr.π_eq_π_iff.2 ⟨a.φ, h1.trans h3, h2⟩).symm
    change Q.bundlePull c.Ψ Λ' w = Q.bundlePull c.Ψ Λ w
    rw [hpull]
    exact hbd w hPw
  · unfold IsTransversalIn; rw [hpull]; exact htr
  · refine (definition_17_5_1_covering c.cover).2 ⟨h0, hΘ,
      (isBranchedEpSubgroupoid_modelPull_iff h0 hΘ).1 ?_⟩
    rw [hpullΘ, hpull]; exact hB
  · refine (S.isCompactBranched_iff_model c.base hΘ).2 ?_
    change (S.modelEP (Q.modelBase c.Ψ)).X.IsCompactBranched (S.modelPull _ Θ)
    rw [hpullΘ, hpull]; exact hK

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
