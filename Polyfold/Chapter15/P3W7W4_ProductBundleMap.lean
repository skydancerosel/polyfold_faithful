import Polyfold.Chapter15.P3W7W4_ProductBundleLevels
import Polyfold.Chapter8.StrongBundleMap

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), §15.3, products remark after
**Definition 15.3.3** (pp. 692–693): products of strong bundle maps (gap G.160, a step towards
(b), the structure map `μ × μ'` of the product of strong bundles over ep-groupoids).

# Products of strong bundle maps

## What is formalized

* `StrongBundle.isScSmoothMap_prodMap_zero`, `isScSmoothMap_prodMap_one`: products of sc-smooth
  maps between total spaces, on `[0]` and on `[1]` (through `prodOneHomeomorph`).
* `StrongBundle.IsStrongBundleMap.prod`: if `Φ` covers `g` and `Φ'` covers `g'` (strong bundle maps
  in the sense of §8.3, `StrongBundle.IsStrongBundleMap`), then `Φ × Φ'` is a strong bundle map
  `W₁ × W₁' → W₂ × W₂'` covering `g × g'`.
-/

open Set Function

noncomputable section

namespace Polyfold

namespace StrongBundle

variable {X₁ : Type*} [TopologicalSpace X₁] [T2Space X₁] [ParacompactSpace X₁] {PX₁ : MPolyfold X₁}
  {Y₁ : Type*} [TopologicalSpace Y₁] [T2Space Y₁] [ParacompactSpace Y₁] {P₁ : Y₁ → X₁}
  [∀ x, AddCommGroup (P₁ ⁻¹' {x})] [∀ x, Module ℝ (P₁ ⁻¹' {x})]
  {X₁' : Type*} [TopologicalSpace X₁'] [T2Space X₁'] [ParacompactSpace X₁']
  {PX₁' : MPolyfold X₁'}
  {Y₁' : Type*} [TopologicalSpace Y₁'] [T2Space Y₁'] [ParacompactSpace Y₁'] {P₁' : Y₁' → X₁'}
  [∀ x, AddCommGroup (P₁' ⁻¹' {x})] [∀ x, Module ℝ (P₁' ⁻¹' {x})]
  {X₂ : Type*} [TopologicalSpace X₂] [T2Space X₂] [ParacompactSpace X₂] {PX₂ : MPolyfold X₂}
  {Y₂ : Type*} [TopologicalSpace Y₂] [T2Space Y₂] [ParacompactSpace Y₂] {P₂ : Y₂ → X₂}
  [∀ x, AddCommGroup (P₂ ⁻¹' {x})] [∀ x, Module ℝ (P₂ ⁻¹' {x})]
  {X₂' : Type*} [TopologicalSpace X₂'] [T2Space X₂'] [ParacompactSpace X₂']
  {PX₂' : MPolyfold X₂'}
  {Y₂' : Type*} [TopologicalSpace Y₂'] [T2Space Y₂'] [ParacompactSpace Y₂'] {P₂' : Y₂' → X₂'}
  [∀ x, AddCommGroup (P₂' ⁻¹' {x})] [∀ x, Module ℝ (P₂' ⁻¹' {x})]
  [ParacompactSpace (X₁ × X₁')] [ParacompactSpace (Y₁ × Y₁')]
  [ParacompactSpace (X₂ × X₂')] [ParacompactSpace (Y₂ × Y₂')]
  {B₁ : StrongBundle PX₁ P₁} {B₁' : StrongBundle PX₁' P₁'}
  {B₂ : StrongBundle PX₂ P₂} {B₂' : StrongBundle PX₂' P₂'}

/-- Products of sc-smooth maps between total spaces, on `[0]`. -/
theorem isScSmoothMap_prodMap_zero {Φ : Y₁ → Y₂} {Φ' : Y₁' → Y₂'}
    (h : B₁.toMPolyfold0.IsScSmoothMap B₂.toMPolyfold0 Φ)
    (h' : B₁'.toMPolyfold0.IsScSmoothMap B₂'.toMPolyfold0 Φ') :
    (B₁.prod B₁').toMPolyfold0.IsScSmoothMap (B₂.prod B₂').toMPolyfold0 (Prod.map Φ Φ') := by
  have hm : (B₁.toMPolyfold0.prod B₁'.toMPolyfold0).IsScSmoothMap
      (B₂.toMPolyfold0.prod B₂'.toMPolyfold0) (fun y => ((Φ ∘ Prod.fst) y, (Φ' ∘ Prod.snd) y)) :=
    MPolyfold.IsScSmoothOn.prodMk
      (h.comp (MPolyfold.isScSmoothMap_fst _ _))
      (h'.comp (MPolyfold.isScSmoothMap_snd _ _))
  exact (B₂.isScSmoothMap_id_prod_zero_symm B₂').comp
    (hm.comp (B₁.isScSmoothMap_id_prod_zero B₁'))

/-- Products of sc-smooth maps between the `[1]`-levels. -/
theorem isScSmoothMap_prodMap_one {Φ : B₁.One → B₂.One} {Φ' : B₁'.One → B₂'.One}
    (h : B₁.toMPolyfold1.IsScSmoothMap B₂.toMPolyfold1 Φ)
    (h' : B₁'.toMPolyfold1.IsScSmoothMap B₂'.toMPolyfold1 Φ') :
    (B₁.prod B₁').toMPolyfold1.IsScSmoothMap (B₂.prod B₂').toMPolyfold1
      ((B₂.prodOneHomeomorph B₂').symm ∘ Prod.map Φ Φ' ∘ B₁.prodOneHomeomorph B₁') := by
  have := B₁.paracompactSpace_prod_one B₁'
  have := B₂.paracompactSpace_prod_one B₂'
  have hm : (B₁.toMPolyfold1.prod B₁'.toMPolyfold1).IsScSmoothMap
      (B₂.toMPolyfold1.prod B₂'.toMPolyfold1) (fun y => ((Φ ∘ Prod.fst) y, (Φ' ∘ Prod.snd) y)) :=
    MPolyfold.IsScSmoothOn.prodMk
      (h.comp (MPolyfold.isScSmoothMap_fst _ _))
      (h'.comp (MPolyfold.isScSmoothMap_snd _ _))
  exact (B₂.isScSmoothMap_prodOneHomeomorph_symm B₂').comp
    (hm.comp (B₁.isScSmoothMap_prodOneHomeomorph B₁'))

/-- The `[1]`-restriction of `Φ × Φ'` is the product of the `[1]`-restrictions. -/
lemma oneRestrict_prodMap {Φ : Y₁ → Y₂} {Φ' : Y₁' → Y₂'} (hΦ : MapsTo Φ B₁.oneSet B₂.oneSet)
    (hΦ' : MapsTo Φ' B₁'.oneSet B₂'.oneSet)
    (hp : MapsTo (Prod.map Φ Φ') (B₁.prod B₁').oneSet (B₂.prod B₂').oneSet) :
    oneRestrict (B₁.prod B₁') (B₂.prod B₂') (Prod.map Φ Φ') hp =
      (B₂.prodOneHomeomorph B₂').symm ∘ Prod.map (oneRestrict B₁ B₂ Φ hΦ)
        (oneRestrict B₁' B₂' Φ' hΦ') ∘ B₁.prodOneHomeomorph B₁' := rfl

/-- **Products of strong bundle maps** (§8.3's strong bundle maps covering a map of the bases):
if `Φ : W₁ → W₂` covers `g` and `Φ' : W₁' → W₂'` covers `g'`, then `Φ × Φ'` is a strong bundle
map `W₁ × W₁' → W₂ × W₂'` covering `g × g'`. -/
theorem IsStrongBundleMap.prod {g : X₁ → X₂} {g' : X₁' → X₂'} {Φ : Y₁ → Y₂} {Φ' : Y₁' → Y₂'}
    (h : B₁.IsStrongBundleMap B₂ g Φ) (h' : B₁'.IsStrongBundleMap B₂' g' Φ') :
    (B₁.prod B₁').IsStrongBundleMap (B₂.prod B₂') (Prod.map g g') (Prod.map Φ Φ') where
  covers y := Prod.ext (h.covers y.1) (h'.covers y.2)
  fiber_linear x := by
    have l₁ := h.fiber_linear x.1
    have l₂ := h'.fiber_linear x.2
    constructor
    · intro v w
      have e₁ := congrArg Subtype.val
        (l₁.map_add (prodFiberEquiv P₁ P₁' x v).1 (prodFiberEquiv P₁ P₁' x w).1)
      have e₂ := congrArg Subtype.val
        (l₂.map_add (prodFiberEquiv P₁ P₁' x v).2 (prodFiberEquiv P₁ P₁' x w).2)
      apply Subtype.ext
      exact Prod.ext e₁ e₂
    · intro a v
      have e₁ := congrArg Subtype.val (l₁.map_smul a (prodFiberEquiv P₁ P₁' x v).1)
      have e₂ := congrArg Subtype.val (l₂.map_smul a (prodFiberEquiv P₁ P₁' x v).2)
      apply Subtype.ext
      exact Prod.ext e₁ e₂
  isScSmoothMap := isScSmoothMap_prodMap_zero h.isScSmoothMap h'.isScSmoothMap
  mapsTo_oneSet y hy := by
    have hy' := (B₁.mem_oneSet_prod B₁').1 hy
    exact (B₂.mem_oneSet_prod B₂').2 ⟨h.mapsTo_oneSet hy'.1, h'.mapsTo_oneSet hy'.2⟩
  isScSmoothMap_one := isScSmoothMap_prodMap_one h.isScSmoothMap_one h'.isScSmoothMap_one

end StrongBundle

end Polyfold
