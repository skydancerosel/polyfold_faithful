import Polyfold.Chapter19.StrongBundleTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.6 "A Strong Bundle Version", the end of the **"Alternative Approach"** (pp. 901–905): the
`H`- and `H'`-structures, and the comparison **I = II** of the two approaches (p. 905).  Numbers
and pages are the 2021 text's.

# The `H`-, `H'`-structures and the comparison of the two approaches

## The text, paraphrased

(p. 901) `H` as well as `H'` define uniquely determined strong bundle structures for `p`, the
`H`-structure and the `H'`-structure, characterized by: `H` (resp. `H'`) is a strong bundle
isomorphism covering the identity; they agree iff `C = H'⁻¹ ∘ H` is a strong bundle isomorphism.
(p. 902) "It follows immediately that the strong bundle structures for `p`, defined by the
requirement that either `H` or `H'` is a strong bundle map, is the same."
(p. 905) In the first approach (`F̄` with bundle transition data `F̄`) and in the second (`F̄`
with `F` and coherence) `M(Ψ, Ψ')` is the same M-polyfold; denote by `I M(Ψ̄, Ψ̄')` and
`II M(Ψ̄, Ψ̄')` the strong bundles obtained.  Since the source maps `I s`, `II s` to `K` are local
strong bundle isomorphisms, the identity `I M(Ψ̄, Ψ̄') → II M(Ψ̄, Ψ̄')` is a local strong bundle
isomorphism, hence a strong bundle isomorphism.

## What is formalized (namespace `Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction`)

For bundle transition data `F̄` and `Ψ̄, Ψ̄' ∈ F̄`:

* `coinduced_altHE`: the topology of `M(Ψ̄, Ψ̄')` used by the second approach (the one making `H`
  a homeomorphism) is the natural topology `T̄` of the first approach.
* `isStrongBundleIso_id_of_altH` (**the `H`-structure is uniquely determined**: a strong bundle
  structure on `p` for which `H` is a strong bundle isomorphism agrees with `bundleBar`).
* `isStrongBundleMap_altCinv`, `isStrongBundleIso_altC` (`C` is a strong bundle isomorphism with
  inverse `C⁻¹ = H⁻¹ ∘ H'`), `altH'E`, `altH'inv`, `isStrongBundleIso_altH'` (**`H'` is a strong
  bundle isomorphism onto `bundleBar`**: the `H'`-structure is the `H`-structure),
  `isStrongBundleIso_id_of_altH'` (uniqueness of the `H'`-structure),
  `isStrongBundleIso_id_of_altH_altH'` (the two structures agree, p. 902).
* **`comparison_I_II`**: every strong bundle structure `I` on `p` for which the source map is a
  locally diffeomorphic strong bundle map (as in Theorem 19.6.13) agrees with `II = bundleBar`:
  the identity is a strong bundle isomorphism; `comparison_I_II_total` (then the total space of
  `I` is the natural M-polyfold `M(Ψ̄, Ψ̄')`); `comparison_I_II_book` (with the coherence
  hypothesis of the second approach).
* Witnesses: `bundleBar` satisfies the hypotheses of `comparison_I_II` (`theorem_19_6_13_s`,
  `theorem_19_6_13_s_local`), of `isStrongBundleIso_id_of_altH` (`theorem_19_6_13_H`) and of
  `isStrongBundleIso_id_of_altH'` (`isStrongBundleIso_altH'`); `reflBan_comparison_I_II`.

## Readings

* As PLAN-19 asks, the comparison is stated with both the bundle transition data `F̄` (which gives
  the natural topology `T̄` and the M-polyfold `M(Ψ̄, Ψ̄')` of the first approach) and coherence
  (the assumption of the second); the coherence hypothesis is derivable from `F̄`
  (`isCoherent_of_bundleTransitionData`), so `comparison_I_II` does not take it.
* We read `I M(Ψ̄, Ψ̄')` as any strong bundle structure on `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` (over the
  natural M-polyfold `M(Ψ, Ψ')`, with the linear structure of the fibres given by `H`) for which
  `s : M(Ψ̄, Ψ̄') → K` is a strong bundle map covering `s` and, near every fibre, a strong bundle
  isomorphism: this is the property of the first approach used by the text ("by construction").
* We read "the source map" for the printed "target maps" in the comparison diagram, whose
  vertical arrows are `I s` and `II s`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

universe u

variable {C : GroupoidalCategory.{u}}

open GroupoidStr (TransitionSet)

namespace StrongBundleUniformizerConstruction

variable {μ : C.BanFunctor} {Fb : StrongBundleUniformizerConstruction μ}

section Comparison

variable (Fbar : Fb.BundleTransitionData) (Ψ Ψ' : Fb.Unif)

/-- **The topology of the second approach is `T̄`**: the topology on `M(Ψ̄, Ψ̄')` coinduced by `H`
from the fibred product is the natural topology `T̄_{Ψ̄,Ψ̄'}`. -/
theorem coinduced_altHE :
    TopologicalSpace.coinduced (altHE Fbar Ψ Ψ') inferInstance =
      (inferInstance : TopologicalSpace (MB Fbar Ψ Ψ')) :=
  (altHHomeo Fbar Ψ Ψ').coinduced_eq

/-- **2021 p. 901: the `H`-structure is uniquely determined**: a strong bundle structure on
`p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` for which `H` is a strong bundle isomorphism covering the identity
agrees with `bundleBar` (the identity is a strong bundle isomorphism). -/
theorem isStrongBundleIso_id_of_altH
    (B₁ : StrongBundle (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
      (projBar Fbar Ψ Ψ'))
    (h : (srcBundle Fbar.toTD Ψ Ψ').IsStrongBundleIso B₁ id (altHHomeo Fbar Ψ Ψ') id
      (altHHomeo Fbar Ψ Ψ').symm) :
    B₁.IsStrongBundleIso (bundleBar Fbar Ψ Ψ') id id id id :=
  StrongBundle.isStrongBundleIso_id_of_isStrongBundleIsoOn B₁ (bundleBar Fbar Ψ Ψ') h.invMap
    (theorem_19_6_13_H Fbar Ψ Ψ').invMap
    (fun _ => ⟨univ, univ, mem_univ _, h.symm.isStrongBundleIsoOn_univ⟩)
    fun _ => ⟨univ, univ, mem_univ _, isStrongBundleIsoOn_altHinv Fbar Ψ Ψ'⟩

/-- **`C⁻¹ = (π', t ∘ H_{Ψ̄'Ψ̄} ∘ A)` is a strong bundle map covering the identity.** -/
theorem isStrongBundleMap_altCinv :
    (tgtBundle Fbar.toTD Ψ Ψ').IsStrongBundleMap (srcBundle Fbar.toTD Ψ Ψ') id
      (altCinv Fbar.toTD Ψ Ψ') :=
  StrongBundle.isStrongBundleMap_pullbackPair (Fb.strU Ψ).B (isScSmoothMap_trSrc Fbar.toTD Ψ Ψ')
    (l := id) MPolyfold.isScSmoothMap_id
    ((isStrongBundleMap_altTheta Fbar Ψ' Ψ).comp (isStrongBundleIso_altA Fbar.toTD Ψ Ψ').toMap)

/-- **`C` is a strong bundle isomorphism covering the identity**, with inverse `C⁻¹`. -/
theorem isStrongBundleIso_altC :
    (srcBundle Fbar.toTD Ψ Ψ').IsStrongBundleIso (tgtBundle Fbar.toTD Ψ Ψ') id
      (altC Fbar.toTD Ψ Ψ') id (altCinv Fbar.toTD Ψ Ψ') :=
  ⟨isStrongBundleMap_altC Fbar Ψ Ψ', isStrongBundleMap_altCinv Fbar Ψ Ψ',
    altCinv_altC Fbar.toTD Ψ Ψ', altC_altCinv Fbar.toTD Ψ Ψ'⟩

/-- `H'` of (19.16) as a map into `M(Ψ̄, Ψ̄')`. -/
def altH'E (y : TgtPB Fbar.toTD Ψ Ψ') : MB Fbar Ψ Ψ' :=
  Fbar.toETD.toTr (altH' Fbar.toTD Ψ Ψ' y)

/-- **`H'⁻¹(h̄) = (p(h̄), t(h̄))`.** -/
def altH'inv (g : MB Fbar Ψ Ψ') : TgtPB Fbar.toTD Ψ Ψ' :=
  ⟨(projBar Fbar Ψ Ψ' g, (g : Ψ.1.Trans Ψ'.1).tgt), rfl⟩

theorem altH'E_eq : altH'E Fbar Ψ Ψ' = altHHomeo Fbar Ψ Ψ' ∘ altCinv Fbar.toTD Ψ Ψ' :=
  funext fun y => (altH_altCinv Fbar.toTD Ψ Ψ' y).symm

theorem altH'inv_eq : altH'inv Fbar Ψ Ψ' = altC Fbar.toTD Ψ Ψ' ∘ (altHHomeo Fbar Ψ Ψ').symm :=
  funext fun g => Subtype.ext (Prod.ext rfl
    (congrArg TransitionSet.tgt (altHE_altHinv Fbar Ψ Ψ' g).symm))

/-- **2021 p. 902: `H'` is a strong bundle isomorphism onto `bundleBar`**, i.e. the
`H'`-structure is the `H`-structure. -/
theorem isStrongBundleIso_altH' :
    (tgtBundle Fbar.toTD Ψ Ψ').IsStrongBundleIso (bundleBar Fbar Ψ Ψ') id (altH'E Fbar Ψ Ψ') id
      (altH'inv Fbar Ψ Ψ') := by
  rw [altH'E_eq, altH'inv_eq]
  have hH := theorem_19_6_13_H Fbar Ψ Ψ'
  have hC := isStrongBundleIso_altC Fbar Ψ Ψ'
  exact ⟨hH.toMap.comp hC.invMap, hC.toMap.comp hH.invMap,
    fun y => by simp only [Function.comp_apply, hH.left_inv, hC.right_inv],
    fun g => by simp only [Function.comp_apply, hC.left_inv, hH.right_inv]⟩

/-- **2021 p. 901: the `H'`-structure is uniquely determined**: a strong bundle structure on `p`
for which `H'` is a strong bundle isomorphism covering the identity agrees with `bundleBar`. -/
theorem isStrongBundleIso_id_of_altH'
    (B₂ : StrongBundle (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
      (projBar Fbar Ψ Ψ'))
    (h : (tgtBundle Fbar.toTD Ψ Ψ').IsStrongBundleIso B₂ id (altH'E Fbar Ψ Ψ') id
      (altH'inv Fbar Ψ Ψ')) :
    B₂.IsStrongBundleIso (bundleBar Fbar Ψ Ψ') id id id id :=
  StrongBundle.isStrongBundleIso_id_of_isStrongBundleIsoOn B₂ (bundleBar Fbar Ψ Ψ') h.invMap
    (isStrongBundleIso_altH' Fbar Ψ Ψ').invMap
    (fun _ => ⟨univ, univ, mem_univ _, h.symm.isStrongBundleIsoOn_univ⟩)
    fun _ => ⟨univ, univ, mem_univ _,
      (isStrongBundleIso_altH' Fbar Ψ Ψ').symm.isStrongBundleIsoOn_univ⟩

/-- **2021 p. 902: the strong bundle structures for `p` defined by "`H` is a strong bundle
isomorphism" and by "`H'` is a strong bundle isomorphism" are the same.** -/
theorem isStrongBundleIso_id_of_altH_altH'
    (B₁ B₂ : StrongBundle (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
      (projBar Fbar Ψ Ψ'))
    (h₁ : (srcBundle Fbar.toTD Ψ Ψ').IsStrongBundleIso B₁ id (altHHomeo Fbar Ψ Ψ') id
      (altHHomeo Fbar Ψ Ψ').symm)
    (h₂ : (tgtBundle Fbar.toTD Ψ Ψ').IsStrongBundleIso B₂ id (altH'E Fbar Ψ Ψ') id
      (altH'inv Fbar Ψ Ψ')) :
    B₁.IsStrongBundleIso B₂ id id id id := by
  have e₁ := isStrongBundleIso_id_of_altH Fbar Ψ Ψ' B₁ h₁
  have e₂ := isStrongBundleIso_id_of_altH' Fbar Ψ Ψ' B₂ h₂
  exact ⟨e₂.invMap.comp e₁.toMap, e₁.invMap.comp e₂.toMap, fun _ => rfl, fun _ => rfl⟩

/-- **2021 p. 905: the comparison I = II**: a strong bundle structure `I` on
`p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` for which the source map `I s : M(Ψ̄, Ψ̄') → K` is a strong bundle map
covering `s` and near every fibre a strong bundle isomorphism agrees with the structure
`II = bundleBar` of the alternative approach: the identity is a strong bundle isomorphism. -/
theorem comparison_I_II
    (BI : StrongBundle (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
      (projBar Fbar Ψ Ψ'))
    (hs : BI.IsStrongBundleMap (Fb.strU Ψ).B (trSrc Fbar.toTD Ψ Ψ')
      fun g : MB Fbar Ψ Ψ' => (g : Ψ.1.Trans Ψ'.1).src)
    (hloc : ∀ x, ∃ (U : Set (MS Fbar Ψ Ψ')) (U' : Set (Fb.strU Ψ).O), x ∈ U ∧
      BI.IsStrongBundleIsoOn (Fb.strU Ψ).B hs U U') :
    BI.IsStrongBundleIso (bundleBar Fbar Ψ Ψ') id id id id :=
  StrongBundle.isStrongBundleIso_id_of_isStrongBundleIsoOn BI (bundleBar Fbar Ψ Ψ') hs
    (theorem_19_6_13_s Fbar Ψ Ψ') hloc (theorem_19_6_13_s_local Fbar Ψ Ψ')

/-- Under the hypotheses of `comparison_I_II`, the total space of `I` is the natural M-polyfold
`M(Ψ̄, Ψ̄')`. -/
theorem comparison_I_II_total
    (BI : StrongBundle (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
      (projBar Fbar Ψ Ψ'))
    (hs : BI.IsStrongBundleMap (Fb.strU Ψ).B (trSrc Fbar.toTD Ψ Ψ')
      fun g : MB Fbar Ψ Ψ' => (g : Ψ.1.Trans Ψ'.1).src)
    (hloc : ∀ x, ∃ (U : Set (MS Fbar Ψ Ψ')) (U' : Set (Fb.strU Ψ).O), x ∈ U ∧
      BI.IsStrongBundleIsoOn (Fb.strU Ψ).B hs U U') :
    BI.toMPolyfold0.IsScDiffeoOn (MBpoly Fbar Ψ Ψ') id id univ univ := by
  have hi := comparison_I_II Fbar Ψ Ψ' BI hs hloc
  have ht := theorem_19_6_13_total Fbar Ψ Ψ'
  exact ⟨MPolyfold.IsScSmoothOn.comp ht.isScSmoothOn hi.toMap.isScSmoothMap (mapsTo_univ _ _),
    MPolyfold.IsScSmoothOn.comp hi.invMap.isScSmoothMap ht.isScSmoothOn_inv (mapsTo_univ _ _),
    mapsTo_univ _ _, mapsTo_univ _ _, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **2021 p. 905, as printed**: with the bundle transition data `F̄` of the first approach and
the coherence of `(F̄, F)` assumed in the second, `I = II`. -/
theorem comparison_I_II_book (_hcoh : IsCoherent Fbar.toTD)
    (BI : StrongBundle (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
      (projBar Fbar Ψ Ψ'))
    (hs : BI.IsStrongBundleMap (Fb.strU Ψ).B (trSrc Fbar.toTD Ψ Ψ')
      fun g : MB Fbar Ψ Ψ' => (g : Ψ.1.Trans Ψ'.1).src)
    (hloc : ∀ x, ∃ (U : Set (MS Fbar Ψ Ψ')) (U' : Set (Fb.strU Ψ).O), x ∈ U ∧
      BI.IsStrongBundleIsoOn (Fb.strU Ψ).B hs U U') :
    BI.IsStrongBundleIso (bundleBar Fbar Ψ Ψ') id id id id :=
  comparison_I_II Fbar Ψ Ψ' BI hs hloc

/-- **The hypotheses of `comparison_I_II` are satisfiable**: `bundleBar` itself satisfies them. -/
theorem comparison_I_II_hyp_witness :
    ∃ hs : (bundleBar Fbar Ψ Ψ').IsStrongBundleMap (Fb.strU Ψ).B (trSrc Fbar.toTD Ψ Ψ')
        (fun g : MB Fbar Ψ Ψ' => (g : Ψ.1.Trans Ψ'.1).src),
      ∀ x, ∃ (U : Set (MS Fbar Ψ Ψ')) (U' : Set (Fb.strU Ψ).O), x ∈ U ∧
        (bundleBar Fbar Ψ Ψ').IsStrongBundleIsoOn (Fb.strU Ψ).B hs U U' :=
  ⟨theorem_19_6_13_s Fbar Ψ Ψ', theorem_19_6_13_s_local Fbar Ψ Ψ'⟩

end Comparison

end StrongBundleUniformizerConstruction

open StrongBundleUniformizerConstruction in
/-- **The witness**: for the reflection bundle, the coherence hypothesis of
`comparison_I_II_book` holds, and `bundleBar` satisfies the hypotheses of `comparison_I_II`
(the source map is a locally diffeomorphic strong bundle map, part of
`Theorem_19_6_13_Statement`). -/
theorem reflBan_comparison_I_II :
    IsCoherent reflBanBTD.toTD ∧ Theorem_19_6_13_Statement reflBanBTD reflΨ reflΨ :=
  ⟨reflBan_isCoherent, theorem_19_6_13_of_bundleTransitionData reflBanBTD reflΨ reflΨ⟩

end GroupoidalCategory

end Polyfold
