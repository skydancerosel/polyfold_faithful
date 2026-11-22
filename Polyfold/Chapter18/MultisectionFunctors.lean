import Polyfold.Chapter18.AuxiliaryNorms
import Polyfold.Chapter13.MultisectionPushforward
import Polyfold.Chapter13.MultisectionPullback
import Polyfold.Chapter13.StructurableMultisection
import Polyfold.Chapter13.MultisectionSupport
import Polyfold.Chapter13.MultisectionAlgebra

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.3 "Sc⁺-Multisection Functors" (pp. 851–853): **Definition 18.3.1, Remark 18.3.2, the
point-wise norm `N(Λ)`, Definition 18.3.3, Remark 18.3.4, the sum `Λ₁ ⊕ Λ₂` and the product
`β ⊙ Λ`, Theorems 18.3.5 and 18.3.6**.  Numbers and pages are the 2021 text's.

## The text, paraphrased

A strong polyfold bundle `P : E → C` has an sc-smooth model `p : W → X` with equivalences
`Γ̄ : W → E` over `Γ : X → C` (p. 852).  (18.3.1) An sc⁺-multisection functor is a functor
`Λ : E → ℚ⁺` with `Γ̄^*Λ = Λ ∘ Γ̄` an sc⁺-multisection functor in the sense of Definition 13.2.1;
(18.3.2) this does not depend on the model.  The point-wise norm is
`N(Λ)(α) = max{N(α, e) | Λ(α, e) > 0}`.  (18.3.3) `Λ` is structurable if `Γ̄^*Λ` is structurable
for a suitable model; (18.3.4) the model does not matter (§13.4).  The sum
`(Λ₁ ⊕ Λ₂)(α, e) = ∑_{e' + e'' = e} Λ₁(α, e')·Λ₂(α, e'')` and, for a functor `β : C → ℝ`,
`(β ⊙ Λ)(α, e) = Λ(α, β(α)⁻¹e)` if `β(α) ≠ 0`, `1_{e = 0}` if `β(α) = 0`.  (18.3.5) Sums and
products with sc-smooth `β` of structurable sc⁺-multisection functors are structurable (§13.3).
(18.3.6) Pull-backs by sc-smooth strong bundle proper covering functors preserve structurability
(Theorem 13.4.4).

## What is formalized (namespace `Polyfold.GCT.VectorBundle`)

* `IsMorInvariant.apply_map`, `isMorInvariant_iff` (a functor `E → β` in terms of `μ(φ)`).
* `multisectionFunctorAdd` (`Λ₁ ⊕ Λ₂`), `multisectionFunctorSmul` (`β ⊙ Λ`),
  `pointwiseNormFunctor` (`N(Λ)`), and that they are functors:
  `isMorInvariant_multisectionFunctorAdd`,
  `isMorInvariant_multisectionFunctorSmul`, `pointwiseNormFunctor_tgt`.
* In `StrongPolyfoldBundleConstruction`: `IsScPlusMultisectionIn`, **`IsScPlusMultisectionFunctor`
  (Definition 18.3.1)**, `bundlePull_eq_pullMult` (`Γ̄_Ψ̄^*Λ = [f̄_{Ψ̄,Ψ̄'}]^* Γ̄_Ψ̄'^*Λ`),
  **`remark_18_3_2`**; `IsStructurableIn`, **`IsStructurableFunctor` (Definition 18.3.3)**,
  **`remark_18_3_4`**; `bundlePull_multisectionFunctorAdd`, `bundlePull_multisectionFunctorSmul`
  (`Γ̄^*` commutes with `⊕` and `β ⊙ ·`); `pointwiseNorm_bundlePull` (`N(Λ) ∘ Γ` is the
  point-wise norm of Definition 13.2.3 of `Γ̄^*Λ`), **`pointwiseNormFunctor_isGreatest`** (the
  maximum is attained and finite); `IsScSmoothFunctionFunctor` (an sc-smooth functor `C → ℝ`),
  **`theorem_18_3_5`**; `StrongBundleProperCovering` (an sc-smooth strong bundle proper covering
  functor read through models, §17.8 pp. 840–842), **`theorem_18_3_6`**.

## Readings

* "Functor `Λ : E → ℚ⁺`" is `IsMorInvariant Λ` (`ℚ⁺` discrete); "an sc-smooth model" is the model
  `W_Ψ̄ → X_Ψ` of a covering family `Ψ̄` (`BundleCoveringFamily`, Chapter 17).  Definitions 18.3.1
  and 18.3.3 say "for an (a suitable) sc-smooth model": we take "there is a covering family", and
  Remarks 18.3.2 and 18.3.4 show that then it holds for every covering family.
* `N(Λ)` is read with `N : E → [0, ∞]` a functor; `max` is read as a supremum in `[0, ∞]` and the
  theorem `pointwiseNormFunctor_isGreatest` shows that it is a finite maximum when `Λ` is an
  sc⁺-multisection functor and `N` an auxiliary norm (Definition 18.1.7 read through a model).
* "`β : C → ℝ` an sc-smooth functor" (Theorem 18.3.5) is read as: constant along morphisms and
  sc-smooth in every uniformizer, `β ∘ Ψ : O → ℝ` (`IsScSmoothFunctionFunctor`); it is then
  sc-smooth on every model `X_Ψ` (`isScSmoothMap_model`).  `β Λ₁` is read as `β ⊙ Λ₁`.
* Theorem 18.3.6: the text leaves the definition of an sc-smooth strong bundle proper covering
  functor between strong polyfold bundles to the reader (§17.8, p. 842: "`W̃` and `W` are strong
  bundles over ep-groupoids and `A : W̃ → W` is a proper strong bundle covering functor in the
  sense of Definition 8.5.9 … We leave the remaining details to the reader").  We read it as a
  functor `P̃ : E' → E` together with sc-smooth models `W̃ → X̃` of `E'` and `W → X` of `E` and a
  proper strong bundle covering `A : W̃ → W` of Definition 8.5.9 for which the square
  `Γ̄ ∘ A ≅ P̃ ∘ Γ̄'` commutes up to isomorphism in `E` (`StrongBundleProperCovering`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory
open scoped ENNReal

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor SBLocalization StrongBundle

variable {C : GCT.{u}} {V : C.VectorBundle}

/-! ### Functors on `E` in terms of `μ(φ)` -/

/-- A functor `N : E → β` is invariant under `μ(φ) : μ(s φ) → μ(t φ)`. -/
theorem IsMorInvariant.apply_map {β : Type*} {N : V.EObj → β} (hN : IsMorInvariant N)
    (φ : C.Mor) (v : V.V (C.toGroupoidStr.src φ)) :
    N (V.objMk (C.toGroupoidStr.tgt φ) (V.map φ v)) = N (V.objMk (C.toGroupoidStr.src φ) v) :=
  hN ⟨(φ, V.objMk _ v), rfl⟩

/-- **A functor `N : E → β`** is the same as a function invariant under every `μ(φ)`. -/
theorem isMorInvariant_iff {β : Type*} {N : V.EObj → β} :
    IsMorInvariant N ↔ ∀ (φ : C.Mor) (v : V.V (C.toGroupoidStr.src φ)),
      N (V.objMk (C.toGroupoidStr.tgt φ) (V.map φ v)) = N (V.objMk (C.toGroupoidStr.src φ) v) := by
  refine ⟨fun h => h.apply_map, fun h a => ?_⟩
  obtain ⟨⟨φ, ⟨α, v⟩⟩, hα⟩ := a
  change α = C.toGroupoidStr.src φ at hα
  subst hα
  exact h φ v

/-! ### The sum and the product with a function (p. 852–853) -/

open scoped Classical in
/-- **The sum `Λ₁ ⊕ Λ₂`** (p. 852): `(Λ₁ ⊕ Λ₂)(α, e) = ∑_{e' + e'' = e} Λ₁(α, e')·Λ₂(α, e'')`
(a finite sum for sc⁺-multisection functors; `∑ᶠ` is `0` on an infinite support). -/
def multisectionFunctorAdd (Λ₁ Λ₂ : V.EObj → ℚ≥0) (e : V.EObj) : ℚ≥0 :=
  ∑ᶠ p : V.V e.1 × V.V e.1, if p.1 + p.2 = e.2 then Λ₁ (V.objMk e.1 p.1) * Λ₂ (V.objMk e.1 p.2)
    else 0

open scoped Classical in
/-- **The product `β ⊙ Λ`** with a function `β : C → ℝ` (p. 853): `Λ(α, β(α)⁻¹·e)` if
`β(α) ≠ 0`; `1` if `β(α) = 0` and `e = 0`; `0` if `β(α) = 0` and `e ≠ 0`. -/
def multisectionFunctorSmul (β : C.Obj → ℝ) (Λ : V.EObj → ℚ≥0) (e : V.EObj) : ℚ≥0 :=
  if β e.1 = 0 then (if e.2 = 0 then 1 else 0) else Λ (V.objMk e.1 ((β e.1)⁻¹ • e.2))

/-- `Λ₁ ⊕ Λ₂` is a functor if `Λ₁`, `Λ₂` are (`μ(φ)` is a linear isomorphism). -/
theorem isMorInvariant_multisectionFunctorAdd {Λ₁ Λ₂ : V.EObj → ℚ≥0} (h₁ : IsMorInvariant Λ₁)
    (h₂ : IsMorInvariant Λ₂) : IsMorInvariant (multisectionFunctorAdd Λ₁ Λ₂) := by
  classical
  refine isMorInvariant_iff.2 fun φ v => ?_
  change (∑ᶠ p : V.V _ × V.V _, _) = ∑ᶠ p : V.V _ × V.V _, _
  set L := V.map φ
  rw [← finsum_comp_equiv (L.toEquiv.prodCongr L.toEquiv)]
  refine finsum_congr fun p => ?_
  change (if L p.1 + L p.2 = L v then Λ₁ (V.objMk _ (L p.1)) * Λ₂ (V.objMk _ (L p.2)) else 0) = _
  rw [← map_add, L.injective.eq_iff, h₁.apply_map, h₂.apply_map]

/-- `β ⊙ Λ` is a functor if `Λ` is and `β` is constant along morphisms. -/
theorem isMorInvariant_multisectionFunctorSmul {β : C.Obj → ℝ}
    (hβ : ∀ φ : C.Mor, β (C.toGroupoidStr.tgt φ) = β (C.toGroupoidStr.src φ))
    {Λ : V.EObj → ℚ≥0} (hΛ : IsMorInvariant Λ) :
    IsMorInvariant (multisectionFunctorSmul β Λ) := by
  classical
  refine isMorInvariant_iff.2 fun φ v => ?_
  unfold multisectionFunctorSmul
  change (if β (C.toGroupoidStr.tgt φ) = 0 then (if V.map φ v = 0 then 1 else 0) else
      Λ (V.objMk _ ((β (C.toGroupoidStr.tgt φ))⁻¹ • V.map φ v))) =
    (if β (C.toGroupoidStr.src φ) = 0 then (if v = 0 then 1 else 0) else
      Λ (V.objMk _ ((β (C.toGroupoidStr.src φ))⁻¹ • v)))
  rw [hβ φ, ← map_smul, hΛ.apply_map, (V.map φ).map_eq_zero_iff]

/-! ### The point-wise norm (p. 852) -/

/-- **The point-wise norm `N(Λ)(α) = max{N(α, e) | Λ(α, e) > 0}`** (p. 852), as a supremum in
`[0, ∞]`; for sc⁺-multisection functors and auxiliary norms it is a finite maximum
(`pointwiseNormFunctor_isGreatest`). -/
def pointwiseNormFunctor (N : V.EObj → ℝ≥0∞) (Λ : V.EObj → ℚ≥0) (α : C.Obj) : ℝ≥0∞ :=
  sSup ((fun v => N (V.objMk α v)) '' {v | 0 < Λ (V.objMk α v)})

/-- **`N(Λ)` is a functor `C → [0, ∞]`**: `N(Λ)(t φ) = N(Λ)(s φ)`. -/
theorem pointwiseNormFunctor_tgt {N : V.EObj → ℝ≥0∞} {Λ : V.EObj → ℚ≥0} (hN : IsMorInvariant N)
    (hΛ : IsMorInvariant Λ) (φ : C.Mor) :
    pointwiseNormFunctor N Λ (C.toGroupoidStr.tgt φ) =
      pointwiseNormFunctor N Λ (C.toGroupoidStr.src φ) := by
  unfold pointwiseNormFunctor
  congr 1
  ext r
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨(V.map φ).symm v, ?_, ?_⟩
    · change 0 < Λ _
      rw [← hΛ.apply_map, ContinuousLinearEquiv.apply_symm_apply]; exact hv
    · change N _ = N _
      rw [← hN.apply_map, ContinuousLinearEquiv.apply_symm_apply]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨V.map φ v, ?_, hN.apply_map φ v⟩
    change 0 < Λ _
    rw [hΛ.apply_map]; exact hv

/-- `N(Λ)` is constant on isomorphism classes. -/
theorem pointwiseNormFunctor_eq_of_isomorphic {N : V.EObj → ℝ≥0∞} {Λ : V.EObj → ℚ≥0}
    (hN : IsMorInvariant N) (hΛ : IsMorInvariant Λ) {α α' : C.Obj}
    (h : C.toGroupoidStr.Isomorphic α α') :
    pointwiseNormFunctor N Λ α = pointwiseNormFunctor N Λ α' := by
  obtain ⟨φ, hs, ht⟩ := h
  rw [← hs, ← ht, pointwiseNormFunctor_tgt hN hΛ]

namespace StrongPolyfoldBundleConstruction

open StrongBundleUniformizerConstruction StrongBundleUniformizerData PolyfoldConstruction

variable {S : C.PolyfoldConstruction} (Q : V.StrongPolyfoldBundleConstruction S) {ι : Type u}
  (Ψb : ι → Q.Unif)

/-! ### `Γ̄` on the fibres -/

/-- `Γ̄(w) = (Γ(p w), Γ̄_{p w}(w))`. -/
theorem bundleModelObj_eq_objMk (w : Q.ModelW Ψb) :
    Q.bundleModelObj Ψb w = V.objMk _ (Q.bundleModelFiber Ψb (Q.modelP Ψb w) ⟨w, rfl⟩) :=
  (Q.objMk_bundleModelFiber Ψb _ ⟨w, rfl⟩).symm

/-- `N ∘ Γ̄` on a fibre `W_x` is `N(Γ(x), Γ̄_x(·))`. -/
theorem bundlePull_fiber {β : Type*} (N : V.EObj → β) (x : S.ModelObj (Q.modelBase Ψb))
    (u : Q.modelP Ψb ⁻¹' {x}) :
    Q.bundlePull Ψb N u = N (V.objMk _ (Q.bundleModelFiber Ψb x u)) := by
  change N (Q.bundleModelObj Ψb u.1) = _
  rw [← Q.objMk_bundleModelFiber Ψb x u]

/-- `N ∘ Γ̄` is a functor on `W_Ψ̄` (Definition 11.5.1's `IsWFunctor`). -/
theorem isWFunctor_bundlePull {β : Type*} {N : V.EObj → β} (hN : IsMorInvariant N) :
    IsWFunctor (Q.modelSEP Ψb) (Q.bundlePull Ψb N) :=
  fun q => Q.bundlePull_μ Ψb hN q

/-! ### Definition 18.3.1 and Remark 18.3.2 -/

/-- `Γ̄_Ψ̄^*Λ = Λ ∘ Γ̄_Ψ̄` is an sc⁺-multisection functor (Definition 13.2.1) in the model of the
family `Ψ̄`. -/
def IsScPlusMultisectionIn (Λ : V.EObj → ℚ≥0) : Prop :=
  IsScPlusMultisection (Q.modelSEP Ψb) (Q.bundlePull Ψb Λ)

/-- **2021 Definition 18.3.1, p. 852 (sc⁺-multisection functor)**: a functor `Λ : E → ℚ⁺` such
that, for an sc-smooth model `Γ̄ : W → E` (a covering family `Ψ̄`), `Γ̄^*Λ = Λ ∘ Γ̄` is an
sc⁺-multisection functor in the ep-groupoid sense (Definition 13.2.1). -/
def IsScPlusMultisectionFunctor (Λ : V.EObj → ℚ≥0) : Prop :=
  IsMorInvariant Λ ∧ ∃ c : Q.BundleCoveringFamily, Q.IsScPlusMultisectionIn c.Ψ Λ

variable {Q}

/-- `[f̄_{Ψ̄,Ψ̄'}]^*` sends the orbit of `w` to an object `w'` with `Γ̄'(w') ≅ Γ̄(w)`. -/
theorem orbitMap_bundleComparison_eq (c c' : Q.BundleCoveringFamily) {w : Q.ModelW c.Ψ}
    {w' : Q.ModelW c'.Ψ}
    (hw : V.groupoid.π (Q.bundleModelObj c'.Ψ w') = V.groupoid.π (Q.bundleModelObj c.Ψ w)) :
    SBLocalization.GenSBMap.orbitMap (Q.bundleComparison c c')
        ((Q.modelSEP c.Ψ).E.toEpGroupoid.π w) = (Q.modelSEP c'.Ψ).E.toEpGroupoid.π w' := by
  apply (isHomeomorph_bundleModelOrbitMap c'.cover).injective
  have h := congrFun (Q.orbitMap_bundleComparison c c') ((Q.modelSEP c.Ψ).E.toEpGroupoid.π w)
  exact h.trans hw.symm

/-- **`Γ̄_Ψ̄^*Λ = [f̄_{Ψ̄,Ψ̄'}]^*(Γ̄_Ψ̄'^*Λ)`** for a functor `Λ` and covering families `Ψ̄`, `Ψ̄'`:
the pull-backs to two models correspond under the generalized strong bundle isomorphism of
Theorem 17.1.18 (bundle form). -/
theorem bundlePull_eq_pullMult {α : Type*} {Λ : V.EObj → α} (hΛ : IsMorInvariant Λ)
    (c c' : Q.BundleCoveringFamily) :
    Q.bundlePull c.Ψ Λ =
      GenSBMap.pullMult (Q.isGeneralizedIso_bundleComparison c c') (Q.bundlePull c'.Ψ Λ) := by
  funext w
  set hf := Q.isGeneralizedIso_bundleComparison c c'
  obtain ⟨w', hw'⟩ := exists_bundleModelObj_iso c c' w
  have ho : (GenSBMap.rep hf).orbitMap ((Q.modelSEP c.Ψ).E.toEpGroupoid.π w) =
      (Q.modelSEP c'.Ψ).E.toEpGroupoid.π w' := by
    rw [← GenSBMap.orbitMap_cls, GenSBMap.cls_rep]
    exact orbitMap_bundleComparison_eq c c' hw'
  change _ = (GenSBMap.rep hf).pullMult (GenSBMap.isEquivalence_rep_Ψ hf) _ w
  have h := SDiagram.pullMult_eq (D := GenSBMap.rep hf) (hΨ := GenSBMap.isEquivalence_rep_Ψ hf)
    (Q.isWFunctor_bundlePull c'.Ψ hΛ) ho
  exact (hΛ.eq_of_isomorphic ((GroupoidStr.π_eq_π_iff _).1 hw')).symm.trans h.symm

/-- Independence of the model for sc⁺-multisection functors (Proposition 11.5.3 for
`f̄_{Ψ̄,Ψ̄'}`). -/
theorem IsScPlusMultisectionIn.of_comparison {Λ : V.EObj → ℚ≥0} (hΛ : IsMorInvariant Λ)
    (c c' : Q.BundleCoveringFamily) (h : Q.IsScPlusMultisectionIn c'.Ψ Λ) :
    Q.IsScPlusMultisectionIn c.Ψ Λ := by
  unfold IsScPlusMultisectionIn
  rw [bundlePull_eq_pullMult hΛ c c']
  exact (GenSBMap.proposition_11_5_3_book _).2.1 _ h

variable (Q)

/-- **2021 Remark 18.3.2, p. 852**: Definition 18.3.1 does not depend on the sc-smooth model:
for every covering family `Ψ̄`, `Λ` is an sc⁺-multisection functor iff it is a functor and
`Γ̄_Ψ̄^*Λ` is an sc⁺-multisection functor in the model `W_Ψ̄`. -/
theorem remark_18_3_2 (c : Q.BundleCoveringFamily) {Λ : V.EObj → ℚ≥0} :
    Q.IsScPlusMultisectionFunctor Λ ↔ IsMorInvariant Λ ∧ Q.IsScPlusMultisectionIn c.Ψ Λ :=
  ⟨fun ⟨hΛ, c', h⟩ => ⟨hΛ, h.of_comparison hΛ c c'⟩, fun ⟨hΛ, h⟩ => ⟨hΛ, c, h⟩⟩

/-! ### Definition 18.3.3 and Remark 18.3.4 -/

/-- `Γ̄_Ψ̄^*Λ` is structurable (Definition 13.3.7) in the model of `Ψ̄`. -/
def IsStructurableIn (Λ : V.EObj → ℚ≥0) : Prop :=
  IsStructurable (Q.modelSEP Ψb) (Q.bundlePull Ψb Λ)

/-- **2021 Definition 18.3.3, p. 852 (structurable)**: an sc⁺-multisection functor `Λ : E → ℚ⁺`
whose pull-back `Γ̄^*Λ` to a suitable sc-smooth model is structurable (Definition 13.3.7). -/
def IsStructurableFunctor (Λ : V.EObj → ℚ≥0) : Prop :=
  IsMorInvariant Λ ∧ ∃ c : Q.BundleCoveringFamily, Q.IsStructurableIn c.Ψ Λ

variable {Q}

/-- Independence of the model for structurability (Theorems 13.4.1 and 13.4.3 for
`f̄_{Ψ̄,Ψ̄'}`). -/
theorem IsStructurableIn.of_comparison {Λ : V.EObj → ℚ≥0} (hΛ : IsMorInvariant Λ)
    (c c' : Q.BundleCoveringFamily) (h : Q.IsStructurableIn c'.Ψ Λ) :
    Q.IsStructurableIn c.Ψ Λ := by
  unfold IsStructurableIn
  rw [bundlePull_eq_pullMult hΛ c c']
  exact GenSBMap.isStructurable_pullMult _ h

variable (Q)

/-- **2021 Remark 18.3.4, p. 852**: it does not matter which sc-smooth model is taken in
Definition 18.3.3 (§13.4: pull-backs and push-forwards by generalized strong bundle isomorphisms
preserve structurability). -/
theorem remark_18_3_4 (c : Q.BundleCoveringFamily) {Λ : V.EObj → ℚ≥0} :
    Q.IsStructurableFunctor Λ ↔ IsMorInvariant Λ ∧ Q.IsStructurableIn c.Ψ Λ :=
  ⟨fun ⟨hΛ, c', h⟩ => ⟨hΛ, h.of_comparison hΛ c c'⟩, fun ⟨hΛ, h⟩ => ⟨hΛ, c, h⟩⟩

/-- A structurable functor is an sc⁺-multisection functor. -/
theorem IsStructurableFunctor.isScPlusMultisectionFunctor {Λ : V.EObj → ℚ≥0}
    (h : Q.IsStructurableFunctor Λ) : Q.IsScPlusMultisectionFunctor Λ :=
  ⟨h.1, h.2.choose, h.2.choose_spec.1⟩

/-! ### `Γ̄^*` commutes with `⊕` and `β ⊙ ·` -/

/-- **`Γ̄^*(Λ₁ ⊕ Λ₂) = Γ̄^*Λ₁ ⊕ Γ̄^*Λ₂`** (Definition 13.2.9 in the model): `Γ̄` is a linear
isomorphism on the fibres. -/
theorem bundlePull_multisectionFunctorAdd (Λ₁ Λ₂ : V.EObj → ℚ≥0) :
    Q.bundlePull Ψb (multisectionFunctorAdd Λ₁ Λ₂) =
      multisectionAdd (A := Q.modelSEP Ψb) (Q.bundlePull Ψb Λ₁) (Q.bundlePull Ψb Λ₂) := by
  classical
  funext w
  set x := Q.modelP Ψb w
  set L := Q.bundleModelFiber Ψb x
  change multisectionFunctorAdd Λ₁ Λ₂ (Q.bundleModelObj Ψb w) =
    ∑ᶠ p : Q.modelP Ψb ⁻¹' {x} × Q.modelP Ψb ⁻¹' {x}, _
  rw [Q.bundleModelObj_eq_objMk Ψb w]
  change (∑ᶠ p : V.V _ × V.V _, _) = _
  rw [← finsum_comp_equiv (L.toEquiv.prodCongr L.toEquiv)]
  refine finsum_congr fun p => ?_
  change (if L p.1 + L p.2 = L ⟨w, rfl⟩ then Λ₁ (V.objMk _ (L p.1)) * Λ₂ (V.objMk _ (L p.2))
      else 0) = _
  rw [← map_add, L.injective.eq_iff, Q.bundlePull_fiber Ψb Λ₁ x p.1,
    Q.bundlePull_fiber Ψb Λ₂ x p.2]
  by_cases h : p.1 + p.2 = ⟨w, rfl⟩
  · rw [if_pos h]; exact (if_pos (congrArg Subtype.val h)).symm
  · rw [if_neg h]; exact (if_neg fun h' => h (Subtype.ext h')).symm

/-- **`Γ̄^*(β ⊙ Λ) = (β ∘ Γ) ⊙ Γ̄^*Λ`** (Lemma 13.2.11's `β ⊙ ·` in the model). -/
theorem bundlePull_multisectionFunctorSmul (β : C.Obj → ℝ) (Λ : V.EObj → ℚ≥0) :
    Q.bundlePull Ψb (multisectionFunctorSmul β Λ) =
      multisectionSmulFun (A := Q.modelSEP Ψb) (β ∘ (S.modelFunctor (Q.modelBase Ψb)).obj)
        (Q.bundlePull Ψb Λ) := by
  classical
  funext w
  set x := Q.modelP Ψb w
  set L := Q.bundleModelFiber Ψb x
  change multisectionFunctorSmul β Λ (Q.bundleModelObj Ψb w) =
    smulAt (A := Q.modelSEP Ψb) (β ((S.modelFunctor (Q.modelBase Ψb)).obj x))
      (Q.bundlePull Ψb Λ) x ⟨w, rfl⟩
  rw [Q.bundleModelObj_eq_objMk Ψb w]
  unfold multisectionFunctorSmul smulAt
  change (if β ((S.modelFunctor (Q.modelBase Ψb)).obj x) = 0 then
      (if L ⟨w, rfl⟩ = 0 then 1 else 0) else
      Λ (V.objMk _ ((β ((S.modelFunctor (Q.modelBase Ψb)).obj x))⁻¹ • L ⟨w, rfl⟩))) = _
  rw [← map_smul, ← Q.bundlePull_fiber Ψb Λ x, L.map_eq_zero_iff]
  by_cases hb : β ((S.modelFunctor (Q.modelBase Ψb)).obj x) = 0
  · rw [if_pos hb, if_pos hb]
    by_cases hu : (⟨w, rfl⟩ : Q.modelP Ψb ⁻¹' {x}) = 0
    · rw [if_pos hu]; exact (if_pos hu).symm
    · rw [if_neg hu]; exact (if_neg hu).symm
  · rw [if_neg hb]; exact (if_neg hb).symm

/-! ### The point-wise norm in a model -/

/-- The fibre `{v | Λ(Γ(x), v) > 0}` is the image of `supp(Γ̄^*Λ)(x)` under `Γ̄_x`. -/
theorem image_suppAt_bundlePull (Λ : V.EObj → ℚ≥0) (x : S.ModelObj (Q.modelBase Ψb)) :
    (fun w : Q.ModelW Ψb => Q.bundleModelObj Ψb w) '' suppAt (A := Q.modelSEP Ψb)
        (Q.bundlePull Ψb Λ) x =
      V.objMk _ '' {v | 0 < Λ (V.objMk ((S.modelFunctor (Q.modelBase Ψb)).obj x) v)} := by
  ext e
  constructor
  · rintro ⟨w, ⟨hw, hpos⟩, rfl⟩
    have hw' : Q.modelP Ψb w = x := hw
    subst hw'
    refine ⟨Q.bundleModelFiber Ψb _ ⟨w, rfl⟩, ?_, (Q.bundleModelObj_eq_objMk Ψb w).symm⟩
    change 0 < Λ _
    rw [← Q.bundleModelObj_eq_objMk Ψb w]
    exact hpos
  · rintro ⟨v, hv, rfl⟩
    set u := (Q.bundleModelFiber Ψb x).symm v
    refine ⟨u.1, ⟨u.2, ?_⟩, ?_⟩
    · change 0 < Λ (Q.bundleModelObj Ψb u.1)
      rw [← Q.objMk_bundleModelFiber Ψb x u, ContinuousLinearEquiv.apply_symm_apply]
      exact hv
    · change Q.bundleModelObj Ψb u.1 = _
      rw [← Q.objMk_bundleModelFiber Ψb x u, ContinuousLinearEquiv.apply_symm_apply]

variable {Q Ψb}

/-- **`N(Λ)(Γ(x))` is the point-wise norm of Definition 13.2.3 of `Γ̄^*Λ` at `x`** for an
auxiliary norm `N` in the model and an sc⁺-multisection functor `Γ̄^*Λ`; in particular
`N(Λ)(Γ(x)) < ∞`. -/
theorem pointwiseNorm_bundlePull {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormIn Ψb N)
    {Λ : V.EObj → ℚ≥0} (hΛ : Q.IsScPlusMultisectionIn Ψb Λ) (x : S.ModelObj (Q.modelBase Ψb)) :
    pointwiseNormFunctor N Λ ((S.modelFunctor (Q.modelBase Ψb)).obj x) ≠ ⊤ ∧
    (pointwiseNormFunctor N Λ ((S.modelFunctor (Q.modelBase Ψb)).obj x)).toReal =
      pointwiseNorm (A := Q.modelSEP Ψb) (Q.modelNorm Ψb N) (Q.bundlePull Ψb Λ) x := by
  have hsub := hΛ.suppAt_subset_oneSet x
  have hfin := hΛ.finite_suppAt x
  have himg : (fun v => N (V.objMk ((S.modelFunctor (Q.modelBase Ψb)).obj x) v)) ''
        {v | 0 < Λ (V.objMk ((S.modelFunctor (Q.modelBase Ψb)).obj x) v)} =
      (fun w => N (Q.bundleModelObj Ψb w)) ''
        suppAt (A := Q.modelSEP Ψb) (Q.bundlePull Ψb Λ) x := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨w, hw, hwe⟩ : V.objMk _ v ∈ (fun w => Q.bundleModelObj Ψb w) ''
          suppAt (A := Q.modelSEP Ψb) (Q.bundlePull Ψb Λ) x := by
        rw [Q.image_suppAt_bundlePull]; exact ⟨v, hv, rfl⟩
      exact ⟨w, hw, congrArg N hwe⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨v, hv, hve⟩ : Q.bundleModelObj Ψb w ∈ V.objMk _ ''
          {v | 0 < Λ (V.objMk ((S.modelFunctor (Q.modelBase Ψb)).obj x) v)} := by
        rw [← Q.image_suppAt_bundlePull]; exact ⟨w, hw, rfl⟩
      exact ⟨v, hv, congrArg N hve⟩
  have hnt : ∀ r ∈ (fun w => N (Q.bundleModelObj Ψb w)) ''
      suppAt (A := Q.modelSEP Ψb) (Q.bundlePull Ψb Λ) x, r ≠ ⊤ := by
    rintro _ ⟨w, hw, rfl⟩
    exact hN.ne_top w (hsub hw)
  have hfin' := hfin.image (fun w => N (Q.bundleModelObj Ψb w))
  unfold pointwiseNormFunctor
  rw [himg]
  refine ⟨?_, ?_⟩
  · rcases Set.eq_empty_or_nonempty ((fun w => N (Q.bundleModelObj Ψb w)) ''
      suppAt (A := Q.modelSEP Ψb) (Q.bundlePull Ψb Λ) x) with he | hne
    · rw [he, sSup_empty]; exact ENNReal.zero_ne_top
    · exact hnt _ (hne.csSup_mem hfin')
  · rw [ENNReal.toReal_sSup _ hnt]
    unfold pointwiseNorm
    congr 1
    ext r
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, by rw [normW_of_mem _ (hsub hw)]; rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨_, ⟨w, hw, rfl⟩, by rw [normW_of_mem _ (hsub hw)]; rfl⟩

variable (Q) in
/-- **The point-wise norm is a finite maximum** (p. 852, `N(Λ) : C → [0, ∞)`): for an auxiliary
norm `N` (read in the model of a covering family, Lemma 18.1.8) and an sc⁺-multisection functor
`Λ`, at every object `α` the value `N(Λ)(α)` is finite and attained,
`N(Λ)(α) = N(α, e)` for some `e` with `Λ(α, e) > 0`, and `N(α, e) ≤ N(Λ)(α)` whenever
`Λ(α, e) > 0`. -/
theorem pointwiseNormFunctor_isGreatest (c : Q.BundleCoveringFamily) {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsAuxNormIn c.Ψ N) {Λ : V.EObj → ℚ≥0} (hΛ : Q.IsScPlusMultisectionFunctor Λ)
    (α : C.Obj) :
    pointwiseNormFunctor N Λ α ≠ ⊤ ∧
      (∃ v, 0 < Λ (V.objMk α v) ∧ N (V.objMk α v) = pointwiseNormFunctor N Λ α) ∧
      ∀ v, 0 < Λ (V.objMk α v) → N (V.objMk α v) ≤ pointwiseNormFunctor N Λ α := by
  have hNinv := hN.isMorInvariant
  have hΛc := ((Q.remark_18_3_2 c).1 hΛ).2
  refine ⟨?_, ?_, fun v hv => le_sSup ⟨v, hv, rfl⟩⟩
  · obtain ⟨x, φ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (modelFunctor_essSurj c.cover) α
    have hx : C.toGroupoidStr.Isomorphic ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) α :=
      ⟨φ, hs, ht⟩
    rw [← pointwiseNormFunctor_eq_of_isomorphic hNinv hΛ.1 hx]
    exact (pointwiseNorm_bundlePull hN hΛc x).1
  · -- the property is invariant along morphisms
    have htr : ∀ φ : C.Mor,
        (∃ v, 0 < Λ (V.objMk (C.toGroupoidStr.src φ) v) ∧
          N (V.objMk _ v) = pointwiseNormFunctor N Λ (C.toGroupoidStr.src φ)) →
        ∃ v, 0 < Λ (V.objMk (C.toGroupoidStr.tgt φ) v) ∧
          N (V.objMk _ v) = pointwiseNormFunctor N Λ (C.toGroupoidStr.tgt φ) := by
      rintro φ ⟨v, hv, hNv⟩
      refine ⟨V.map φ v, by rw [hΛ.1.apply_map]; exact hv, ?_⟩
      rw [hNinv.apply_map, hNv, pointwiseNormFunctor_tgt hNinv hΛ.1]
    obtain ⟨x, φ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (modelFunctor_essSurj c.cover) α
    rw [← ht]
    apply htr
    rw [hs]
    -- at `Γ(x)`: the maximum of Definition 13.2.3 in the model
    obtain ⟨⟨w, ⟨hwx, hpos⟩, hmax⟩, -⟩ :=
      (hΛc.isGreatest_pointwiseNorm (Q.modelNorm c.Ψ N) x)
    have hwx' : Q.modelP c.Ψ w = x := hwx
    subst hwx'
    refine ⟨Q.bundleModelFiber c.Ψ _ ⟨w, rfl⟩, ?_, ?_⟩
    · rw [← Q.bundleModelObj_eq_objMk c.Ψ w]; exact hpos
    · rw [← Q.bundleModelObj_eq_objMk c.Ψ w]
      obtain ⟨hne, heq⟩ := pointwiseNorm_bundlePull hN hΛc (Q.modelP c.Ψ w)
      have hw1 := hΛc.suppAt_subset_oneSet _ ⟨rfl, hpos⟩
      have hNw : N (Q.bundleModelObj c.Ψ w) ≠ ⊤ := hN.ne_top w hw1
      rw [← ENNReal.toReal_eq_toReal_iff' hNw hne, heq, ← hmax, normW_of_mem _ hw1]
      rfl

/-! ### sc-smooth functions `C → ℝ` and Theorem 18.3.5 -/

/-- **An sc-smooth functor `β : C → ℝ`** (Theorem 18.3.5): constant along the morphisms of `C`
and sc-smooth in every uniformizer, `β ∘ Ψ : O → ℝ` (the categorical form of Lemma 13.2.11's
hypothesis). -/
def _root_.Polyfold.GCT.PolyfoldConstruction.IsScSmoothFunctionFunctor (S : C.PolyfoldConstruction)
    (β : C.Obj → ℝ) : Prop :=
  (∀ φ : C.Mor, β (C.toGroupoidStr.tgt φ) = β (C.toGroupoidStr.src φ)) ∧
    ∀ Ψ : S.Unif, Ψ.1.P.IsScSmoothMap realPolyfold (β ∘ Ψ.1.obj)

omit Q in
/-- An sc-smooth functor `β : C → ℝ` is a functor on every model: `β ∘ Γ` is constant along the
morphisms of `X_Ψ`. -/
theorem _root_.Polyfold.GCT.PolyfoldConstruction.IsScSmoothFunctionFunctor.mor_model
    {β : C.Obj → ℝ} (hβ : S.IsScSmoothFunctionFunctor β)
    {κ : Type u} (Ψ : κ → S.Unif) (φ : S.ModelMor Ψ) :
    β ((S.modelFunctor Ψ).obj ((S.modelEpGroupoid Ψ).tgt φ)) =
      β ((S.modelFunctor Ψ).obj ((S.modelEpGroupoid Ψ).src φ)) := by
  exact ((congrArg β ((S.modelFunctor Ψ).tgt_mor φ)).symm.trans (hβ.1 _)).trans
    (congrArg β ((S.modelFunctor Ψ).src_mor φ))

omit Q in
/-- An sc-smooth functor `β : C → ℝ` is sc-smooth on every model `X_Ψ` (smooth on every piece). -/
theorem _root_.Polyfold.GCT.PolyfoldConstruction.IsScSmoothFunctionFunctor.isScSmoothMap_model
    {β : C.Obj → ℝ}
    (hβ : S.IsScSmoothFunctionFunctor β) {κ : Type u} (Ψ : κ → S.Unif) :
    (S.modelEpGroupoid Ψ).PObj.IsScSmoothMap realPolyfold (β ∘ (S.modelFunctor Ψ).obj) :=
  (MPolyfold.isScSmoothMap_sigma_iff _).2 fun i => hβ.2 (Ψ i)

variable (Q) in
/-- **Sums and products of sc⁺-multisection functors** (Definitions 13.2.9, Lemma 13.2.11 read
through a model): `Λ₁ ⊕ Λ₂` and `β ⊙ Λ₁` are sc⁺-multisection functors. -/
theorem isScPlusMultisectionFunctor_add_smul {Λ₁ Λ₂ : V.EObj → ℚ≥0}
    (h₁ : Q.IsScPlusMultisectionFunctor Λ₁) (h₂ : Q.IsScPlusMultisectionFunctor Λ₂)
    {β : C.Obj → ℝ} (hβ : S.IsScSmoothFunctionFunctor β) :
    Q.IsScPlusMultisectionFunctor (multisectionFunctorAdd Λ₁ Λ₂) ∧
      Q.IsScPlusMultisectionFunctor (multisectionFunctorSmul β Λ₁) := by
  obtain ⟨hinv₁, c, hc₁⟩ := h₁
  have hc₂ := ((Q.remark_18_3_2 c).1 h₂).2
  refine ⟨⟨isMorInvariant_multisectionFunctorAdd hinv₁ h₂.1, c, ?_⟩,
    ⟨isMorInvariant_multisectionFunctorSmul hβ.1 hinv₁, c, ?_⟩⟩
  · unfold IsScPlusMultisectionIn
    rw [Q.bundlePull_multisectionFunctorAdd]
    exact definition_13_2_9 hc₁ hc₂
  · unfold IsScPlusMultisectionIn
    rw [Q.bundlePull_multisectionFunctorSmul]
    exact lemma_13_2_11 (hβ.mor_model _) (hβ.isScSmoothMap_model _) hc₁

variable (Q) in
/-- **2021 Theorem 18.3.5, p. 853**: for structurable sc⁺-multisection functors `Λ₁, Λ₂ : E → ℚ⁺`
and an sc-smooth functor `β : C → ℝ`, `Λ₁ ⊕ Λ₂` and `β ⊙ Λ₁` are structurable sc⁺-multisection
functors (Proposition 13.3.12 and Lemma 13.3.14 in a model). -/
theorem theorem_18_3_5 {Λ₁ Λ₂ : V.EObj → ℚ≥0} (h₁ : Q.IsStructurableFunctor Λ₁)
    (h₂ : Q.IsStructurableFunctor Λ₂) {β : C.Obj → ℝ} (hβ : S.IsScSmoothFunctionFunctor β) :
    Q.IsStructurableFunctor (multisectionFunctorAdd Λ₁ Λ₂) ∧
      Q.IsStructurableFunctor (multisectionFunctorSmul β Λ₁) := by
  obtain ⟨hinv₁, c, hc₁⟩ := h₁
  have hc₂ := ((Q.remark_18_3_4 c).1 h₂).2
  refine ⟨⟨isMorInvariant_multisectionFunctorAdd hinv₁ h₂.1, c, ?_⟩,
    ⟨isMorInvariant_multisectionFunctorSmul hβ.1 hinv₁, c, ?_⟩⟩
  · unfold IsStructurableIn
    rw [Q.bundlePull_multisectionFunctorAdd]
    exact proposition_13_3_12 hc₁ hc₂
  · unfold IsStructurableIn
    rw [Q.bundlePull_multisectionFunctorSmul]
    exact lemma_13_3_14_fun hc₁ (hβ.mor_model _) (hβ.isScSmoothMap_model _)

/-! ### Theorem 18.3.6 -/

/-- **An sc-smooth strong bundle proper covering functor `P̃ : E' → E`** between strong polyfold
bundles over `C'` and `C` (§17.8, pp. 840–842, Theorem 18.3.6), read through models as the text
indicates (p. 842): a functor `P̃` covering a functor `P : C' → C` of the bases, sc-smooth models
`Γ̄' : W' → E'`, `Γ̄ : W → E` (covering families), and a proper strong bundle covering
`A : W' → W` of Definition 8.5.9 with `Γ̄ ∘ A ≅ P̃ ∘ Γ̄'` (the square of (17.106) commutes up to
isomorphism in `E`). -/
structure StrongBundleProperCovering {C' : GCT.{u}} {V' : C'.VectorBundle}
    {S' : C'.PolyfoldConstruction} (Q' : V'.StrongPolyfoldBundleConstruction S')
    (Q : V.StrongPolyfoldBundleConstruction S) where
  /-- The functor `P̃ : E' → E`. -/
  functor : GroupoidFunctor V'.groupoid V.groupoid
  /-- The functor `P : C' → C` of the bases. -/
  base : GroupoidFunctor C'.toGroupoidStr C.toGroupoidStr
  /-- `P̃` covers `P`. -/
  proj_functor : ∀ e, V.base (functor.obj e) = base.obj (V'.base e)
  /-- The model of `E'`. -/
  c' : Q'.BundleCoveringFamily
  /-- The model of `E`. -/
  c : Q.BundleCoveringFamily
  /-- The covered functor `X' → X` of the models. -/
  F : EpFunctor (Q'.modelSEP c'.Ψ).X (Q.modelSEP c.Ψ).X
  /-- The strong bundle map `A : W' → W` of the models. -/
  A : Q'.ModelW c'.Ψ → Q.ModelW c.Ψ
  /-- `A` is a proper strong bundle covering functor (Definition 8.5.9). -/
  isProper : (Q'.modelSEP c'.Ψ).E.IsProperStrongBundleCovering2021 (Q.modelSEP c.Ψ).E F A
  /-- `Γ̄ ∘ A ≅ P̃ ∘ Γ̄'`. -/
  comm : ∀ w, V.groupoid.Isomorphic (Q.bundleModelObj c.Ψ (A w))
    (functor.obj (Q'.bundleModelObj c'.Ψ w))

/-- **2021 Theorem 18.3.6, p. 853**: the pull-back `P̃^*Λ = Λ ∘ P̃` of a structurable
sc⁺-multisection functor by an sc-smooth strong bundle proper covering functor is a structurable
sc⁺-multisection functor (Theorem 13.4.4 in the models). -/
theorem theorem_18_3_6 {C' : GCT.{u}} {V' : C'.VectorBundle} {S' : C'.PolyfoldConstruction}
    {Q' : V'.StrongPolyfoldBundleConstruction S'} (P : StrongBundleProperCovering Q' Q)
    {Λ : V.EObj → ℚ≥0} (h : Q.IsStructurableFunctor Λ) :
    Q'.IsStructurableFunctor (Λ ∘ P.functor.obj) := by
  have hinv : IsMorInvariant (Λ ∘ P.functor.obj) := fun a => by
    change Λ (P.functor.obj _) = Λ (P.functor.obj _)
    rw [← P.functor.tgt_mor, ← P.functor.src_mor]
    exact h.1 _
  refine ⟨hinv, P.c', ?_⟩
  have hc := ((Q.remark_18_3_4 P.c).1 h).2
  have heq : Q'.bundlePull P.c'.Ψ (Λ ∘ P.functor.obj) = Q.bundlePull P.c.Ψ Λ ∘ P.A := by
    funext w
    exact (h.1.eq_of_isomorphic (P.comm w)).symm
  unfold IsStructurableIn
  rw [heq]
  exact theorem_13_4_4 P.isProper hc

end StrongPolyfoldBundleConstruction

end GCT.VectorBundle

end Polyfold
