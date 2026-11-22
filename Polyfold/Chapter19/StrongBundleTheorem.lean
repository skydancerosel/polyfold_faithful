import Polyfold.Chapter19.StrongBundleCoherence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.6 "A Strong Bundle Version", **Theorem 19.6.13** (p. 900), proved along the "Alternative
Approach" (pp. 901–904).  Numbers and pages are the 2021 text's.

# The strong bundle `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`

## The text, paraphrased

(Theorem 19.6.13) For a basic bundle construction `(F̄, 𝓕̄)` with underlying `(F, 𝓕)`, `T`
metrizable, the natural map `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` admits a natural structure of an M-polyfold
bundle (a strong bundle), the structure on the base being the natural M-polyfold structure of
`M(Ψ, Ψ')`; `s` and `t` are locally diffeomorphic strong bundle maps, the unit map is a strong
bundle map and the inversion is a strong bundle isomorphism.  (pp. 901–904) The structure is the
one for which `H : M(Ψ, Ψ') ₛ×ₚ K → M(Ψ̄, Ψ̄')` (19.16) is a strong bundle isomorphism; `s = π_K ∘
H⁻¹` (19.20), `t = π_K' ∘ C ∘ H⁻¹`, `u = H ∘ (u, Id)`, and `ῑ = ((ι ∘ π), C)` (p. 904).

## What is formalized (namespace `Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction`)

For bundle transition data `F̄` (Definition 19.6.4) and `Ψ̄, Ψ̄' ∈ F̄`:

* `MB` (`M(Ψ̄, Ψ̄')` with its natural topology, the transition set of the transition data
  `F̄.toETD` of `E_μ`), `MBpoly` (its M-polyfold structure, Theorem 19.5.1 for `E_μ`), `projBar`
  (`p`), `altHE` (`H` as a map into `MB`), `altHinv` (`H⁻¹(h̄) = (p(h̄), s(h̄))`).
* `isScSmoothMap_projBar` (`p` is sc-smooth), `isScDiffeoOn_altH` (**`H` is an sc-diffeomorphism**
  from the fibred product, with its pull-back structure, onto `M(Ψ̄, Ψ̄')`), `altHHomeo`
  (`H` as a homeomorphism).
* `fiberEquivBar`, the linear structure of the fibres `p⁻¹(h)` transported by `H`,
  `fiberLinBar`, and **`bundleBar`**: the strong bundle `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`, the transport
  of `π` along `H` (`StrongBundle.transport`), over `F.transPolyfold` (the natural M-polyfold
  structure of the base).
* **Theorem 19.6.13**: `theorem_19_6_13_H` (`H` is a strong bundle isomorphism covering `Id`),
  `theorem_19_6_13_total` (the total space structure is the natural M-polyfold structure of
  `M(Ψ̄, Ψ̄')`), `theorem_19_6_13_s`, `theorem_19_6_13_s_local` (`s` is a strong bundle map
  covering `s`, near every fibre a strong bundle isomorphism), `theorem_19_6_13_t`,
  `theorem_19_6_13_t_local` (the same for `t`), `theorem_19_6_13_u` (the unit map is a strong
  bundle map covering `u`), `theorem_19_6_13_inv` (the inversion is a strong bundle isomorphism
  covering `ι`), and `theorem_19_6_13` (the statement for a basic bundle construction) with
  `theorem_19_6_13_book` (with the hypotheses of the text).

## Readings

* We read "natural structure of an M-polyfold bundle" as a strong bundle structure on
  `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` over `F.transPolyfold` whose total space structure is the natural
  M-polyfold structure of `M(Ψ̄, Ψ̄')`; we read "natural" as: `H` of (19.16) is a strong bundle
  isomorphism (p. 901).  The fibres `p⁻¹(h)` carry the linear structure of `K_{s(h)}` via `H`.
* We read "locally diffeomorphic strong bundle maps" as: a strong bundle map which is, near every
  fibre, a strong bundle isomorphism onto an open set (Chapter 8's `IsStrongBundleIsoOn`).
* The hypothesis "`T` metrizable" is part of `theorem_19_6_13_book`; in this formalization the
  transition sets of any transition data are metrizable, so the main statements do not use it.
* The multiplication, "a strong bundle map" on `M(Ψ̄', Ψ̄'') ₛ×ₜ M(Ψ̄, Ψ̄')`, is in
  `StrongBundleMultiplication` (`theorem_19_6_13_m`), with the domain read there.
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

section Theorem

variable (Fbar : Fb.BundleTransitionData) (Ψ Ψ' : Fb.Unif)

/-- `M(Ψ̄, Ψ̄')` with its natural topology (the transition data `F̄.toETD` of `E_μ`). -/
abbrev MB : Type u := Fbar.toETD.Tr (Fb.toEUnif Ψ) (Fb.toEUnif Ψ')

/-- The natural M-polyfold structure of `M(Ψ̄, Ψ̄')` (Theorem 19.5.1 for `E_μ`). -/
abbrev MBpoly : MPolyfold (MB Fbar Ψ Ψ') :=
  Fbar.toETD.transPolyfold (Fb.toEUnif Ψ) (Fb.toEUnif Ψ')

/-- The base `M(Ψ, Ψ')`. -/
abbrev MS : Type u := Fbar.toTD.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ')

/-- **2021 (19.13), p. 900: `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`.** -/
def projBar (g : MB Fbar Ψ Ψ') : MS Fbar Ψ Ψ' :=
  Fbar.toTD.toTr ((Fb.strU Ψ).proj (Fb.strU Ψ') g)

/-- `H` of (19.16) as a map into `M(Ψ̄, Ψ̄')`. -/
def altHE (x : SrcPB Fbar.toTD Ψ Ψ') : MB Fbar Ψ Ψ' :=
  Fbar.toETD.toTr (altH Fbar.toTD Ψ Ψ' x)

/-- **`H⁻¹(h̄) = (p(h̄), s(h̄))`.** -/
def altHinv (g : MB Fbar Ψ Ψ') : SrcPB Fbar.toTD Ψ Ψ' :=
  ⟨(projBar Fbar Ψ Ψ' g, (g : Ψ.1.Trans Ψ'.1).src), rfl⟩

theorem altHE_altHinv (g : MB Fbar Ψ Ψ') : altHE Fbar Ψ Ψ' (altHinv Fbar Ψ Ψ' g) = g :=
  (Fb.strU Ψ).lift_proj (Fb.strU Ψ') (g : Ψ.1.Trans Ψ'.1)

theorem altHinv_altHE (x : SrcPB Fbar.toTD Ψ Ψ') : altHinv Fbar Ψ Ψ' (altHE Fbar Ψ Ψ' x) = x :=
  Subtype.ext (Prod.ext (proj_altH Fbar.toTD Ψ Ψ' x) rfl)

theorem src_altHE (x : SrcPB Fbar.toTD Ψ Ψ') :
    (altHE Fbar Ψ Ψ' x : Ψ.1.Trans Ψ'.1).src = x.1.2 := rfl

theorem projBar_altHE (x : SrcPB Fbar.toTD Ψ Ψ') :
    projBar Fbar Ψ Ψ' (altHE Fbar Ψ Ψ' x) = x.1.1 := proj_altH Fbar.toTD Ψ Ψ' x

/-- The M-polyfold `K` of `Ψ̄` is the level-`0` structure of `p : K → O`. -/
theorem toMPolyfold0_strU (Ψ : Fb.Unif) : (Fb.strU Ψ).B.toMPolyfold0 = Ψ.1.P :=
  (Fb.strU Ψ).toMPolyfold0_eq

/-- On the sheet `F̄_{h̄₀}(K|V)` of `M(Ψ̄, Ψ̄')`, `p = F_{p(h̄₀)} ∘ p ∘ s`. -/
theorem projBar_eq_of_mem {g₀ g : MB Fbar Ψ Ψ'}
    (hg : (g : Ψ.1.Trans Ψ'.1) ∈ Fbar.toETD.map _ _ (g₀ : Ψ.1.Trans Ψ'.1) ''
      Fbar.toETD.dom _ _ (g₀ : Ψ.1.Trans Ψ'.1)) :
    (Fb.strU Ψ).p (g : Ψ.1.Trans Ψ'.1).src ∈
        Fbar.toTD.dom (Fb.baseUnif Ψ) (Fb.baseUnif Ψ')
          ((Fb.strU Ψ).proj (Fb.strU Ψ') (g₀ : Ψ.1.Trans Ψ'.1)) ∧
      projBar Fbar Ψ Ψ' g = Fbar.toTD.toTr (Fbar.toTD.map (Fb.baseUnif Ψ) (Fb.baseUnif Ψ')
        ((Fb.strU Ψ).proj (Fb.strU Ψ') (g₀ : Ψ.1.Trans Ψ'.1))
        ((Fb.strU Ψ).p (g : Ψ.1.Trans Ψ'.1).src)) := by
  obtain ⟨a, ha, e⟩ := hg
  have ha' : (Fb.strU Ψ).p a ∈
      Fbar.toTD.dom (Fb.baseUnif Ψ) (Fb.baseUnif Ψ')
        ((Fb.strU Ψ).proj (Fb.strU Ψ') (g₀ : Ψ.1.Trans Ψ'.1)) := ha
  have hs : (g : Ψ.1.Trans Ψ'.1).src = a := by
    rw [← e]; exact definition_19_6_4_A_src ha'
  rw [hs]
  refine ⟨ha', ?_⟩
  change (Fb.strU Ψ).proj (Fb.strU Ψ') (g : Ψ.1.Trans Ψ'.1) = _
  rw [← e]
  exact proj_mapBar

/-- **`p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` is sc-smooth** (on the sheet of `h̄₀` it is
`F_{p(h̄₀)} ∘ p ∘ s`). -/
theorem isScSmoothMap_projBar :
    (MBpoly Fbar Ψ Ψ').IsScSmoothMap (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
      (projBar Fbar Ψ Ψ') := by
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun g₀ _ => ?_
  have hd := Fbar.toETD.isScDiffeoOn_map (Fb.toEUnif Ψ) (Fb.toEUnif Ψ') (g₀ : Ψ.1.Trans Ψ'.1)
  set k := (Fb.strU Ψ).proj (Fb.strU Ψ') (g₀ : Ψ.1.Trans Ψ'.1)
  have hm := Fbar.toTD.isScDiffeoOn_map (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k
  have hp : Ψ.1.P.IsScSmoothMap (Fb.strU Ψ).PO (Fb.strU Ψ).p := by
    rw [← toMPolyfold0_strU]; exact (Fb.strU Ψ).B.isScSmoothMap_proj
  have hs := (Fbar.toETD.isLocalScDiffeo_src (Fb.toEUnif Ψ) (Fb.toEUnif Ψ')).isScSmoothMap
  have hT : IsOpen (X := MB Fbar Ψ Ψ') (Fbar.toETD.map _ _ (g₀ : Ψ.1.Trans Ψ'.1) ''
      Fbar.toETD.dom _ _ (g₀ : Ψ.1.Trans Ψ'.1)) := hd.isOpen_target
  refine ⟨_, hT, ⟨_, Fbar.toETD.mem_dom _ _ _, Fbar.toETD.map_src _ _ _⟩, subset_univ _, ?_⟩
  have h2 : Ψ.1.P.IsScSmoothOn (Fb.strU Ψ).PO (Fb.strU Ψ).p
      ((Fb.strU Ψ).p ⁻¹' Fbar.toTD.dom (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k) :=
    hp.mono ((Fbar.toTD.isOpen_dom (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k).preimage
      (Fb.strU Ψ).continuous_p) (subset_univ _)
  have h3 := MPolyfold.IsScSmoothOn.comp h2 (hs.mono hT (subset_univ _))
    fun g hg => (projBar_eq_of_mem Fbar Ψ Ψ' hg).1
  have h1 := MPolyfold.IsScSmoothOn.comp hm.isScSmoothOn h3
    fun g hg => (projBar_eq_of_mem Fbar Ψ Ψ' hg).1
  exact h1.congr fun g hg => (projBar_eq_of_mem Fbar Ψ Ψ' hg).2.symm

/-- **`H` is sc-smooth** (on the sheet over `F_k(V(o))` it is `F̄_k ∘ π_K`). -/
theorem isScSmoothMap_altHE :
    (srcBundle Fbar.toTD Ψ Ψ').toMPolyfold0.IsScSmoothMap (MBpoly Fbar Ψ Ψ') (altHE Fbar Ψ Ψ') := by
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x₀ _ => ?_
  set k : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1 := x₀.1.1
  set g₀ : Ψ.1.Trans Ψ'.1 := altH Fbar.toTD Ψ Ψ' x₀
  have hk : (Fb.strU Ψ).proj (Fb.strU Ψ') g₀ = k := proj_altH Fbar.toTD Ψ Ψ' x₀
  have hd := Fbar.toETD.isScDiffeoOn_map (Fb.toEUnif Ψ) (Fb.toEUnif Ψ') g₀
  have hπ : (srcBundle Fbar.toTD Ψ Ψ').toMPolyfold0.IsScSmoothMap Ψ.1.P
      (pullbackProj' (Fb.strU Ψ).p (trSrc Fbar.toTD Ψ Ψ')) := by
    rw [← toMPolyfold0_strU]
    exact ((Fb.strU Ψ).B.isStrongBundleMap_pullbackProj'
      (isScSmoothMap_trSrc Fbar.toTD Ψ Ψ')).isScSmoothMap
  have hV : IsOpen (X := MS Fbar Ψ Ψ') (Fbar.toTD.map (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k ''
      Fbar.toTD.dom (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k) :=
    (Fbar.toTD.isScDiffeoOn_map (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k).isOpen_target
  have hU : IsOpen (pullbackProj (Fb.strU Ψ).p (trSrc Fbar.toTD Ψ Ψ') ⁻¹'
      (Fbar.toTD.map (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k ''
        Fbar.toTD.dom (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k)) :=
    hV.preimage (continuous_pullbackProj _ _)
  have hmaps : MapsTo (pullbackProj' (Fb.strU Ψ).p (trSrc Fbar.toTD Ψ Ψ'))
      (pullbackProj (Fb.strU Ψ).p (trSrc Fbar.toTD Ψ Ψ') ⁻¹'
        (Fbar.toTD.map (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k ''
          Fbar.toTD.dom (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k))
      (Fbar.toETD.dom (Fb.toEUnif Ψ) (Fb.toEUnif Ψ') g₀) := fun x hx => by
    change (Fb.strU Ψ).p x.1.2 ∈
      Fbar.toTD.dom (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') ((Fb.strU Ψ).proj (Fb.strU Ψ') g₀)
    rw [hk, show (Fb.strU Ψ).p x.1.2 = _ from x.2]
    exact (mem_image_map hx).1
  refine ⟨_, hU, mem_image_map_self k, subset_univ _,
    (MPolyfold.IsScSmoothOn.comp hd.isScSmoothOn (hπ.mono hU (subset_univ _)) hmaps).congr
      fun x hx => ?_⟩
  change Fb.mapBar Fbar.toTD Ψ Ψ' ((Fb.strU Ψ).proj (Fb.strU Ψ') g₀) x.1.2 =
    altH Fbar.toTD Ψ Ψ' x
  rw [hk]
  exact (altH_eq_mapBar x hx).symm

/-- **`H⁻¹ = (p, s)` is sc-smooth.** -/
theorem isScSmoothMap_altHinv :
    (MBpoly Fbar Ψ Ψ').IsScSmoothMap (srcBundle Fbar.toTD Ψ Ψ').toMPolyfold0
      (altHinv Fbar Ψ Ψ') := by
  have hs : (MBpoly Fbar Ψ Ψ').IsScSmoothMap (Fb.strU Ψ).B.toMPolyfold0
      fun g : MB Fbar Ψ Ψ' => (g : Ψ.1.Trans Ψ'.1).src := by
    rw [toMPolyfold0_strU]
    exact (Fbar.toETD.isLocalScDiffeo_src (Fb.toEUnif Ψ) (Fb.toEUnif Ψ')).isScSmoothMap
  exact StrongBundle.isScSmoothOn_to_pullback (Fb.strU Ψ).B (isScSmoothMap_trSrc Fbar.toTD Ψ Ψ')
    (isScSmoothMap_projBar Fbar Ψ Ψ') hs

/-- **`H : M(Ψ, Ψ') ₛ×ₚ K → M(Ψ̄, Ψ̄')` is an sc-diffeomorphism** for the pull-back structure and
the natural M-polyfold structure of `M(Ψ̄, Ψ̄')`. -/
theorem isScDiffeoOn_altH :
    (srcBundle Fbar.toTD Ψ Ψ').toMPolyfold0.IsScDiffeoOn (MBpoly Fbar Ψ Ψ') (altHE Fbar Ψ Ψ')
      (altHinv Fbar Ψ Ψ') univ univ :=
  ⟨isScSmoothMap_altHE Fbar Ψ Ψ', isScSmoothMap_altHinv Fbar Ψ Ψ', mapsTo_univ _ _,
    mapsTo_univ _ _, fun x _ => altHinv_altHE Fbar Ψ Ψ' x, fun g _ => altHE_altHinv Fbar Ψ Ψ' g⟩

/-- **`H` as a homeomorphism `M(Ψ, Ψ') ₛ×ₚ K ≃ M(Ψ̄, Ψ̄')`.** -/
def altHHomeo : SrcPB Fbar.toTD Ψ Ψ' ≃ₜ MB Fbar Ψ Ψ' where
  toFun := altHE Fbar Ψ Ψ'
  invFun := altHinv Fbar Ψ Ψ'
  left_inv := altHinv_altHE Fbar Ψ Ψ'
  right_inv := altHE_altHinv Fbar Ψ Ψ'
  continuous_toFun := continuousOn_univ.1 (isScSmoothMap_altHE Fbar Ψ Ψ').continuousOn
  continuous_invFun := continuousOn_univ.1 (isScSmoothMap_altHinv Fbar Ψ Ψ').continuousOn

/-! ### The fibres of `p` and the strong bundle structure -/

/-- `H` identifies the fibre `p⁻¹(h)` with the fibre `π⁻¹(h) ≅ K_{s(h)}`. -/
def fiberEquivBar (x : MS Fbar Ψ Ψ') :
    projBar Fbar Ψ Ψ' ⁻¹' {x} ≃ pullbackProj (Fb.strU Ψ).p (trSrc Fbar.toTD Ψ Ψ') ⁻¹' {x} where
  toFun g := ⟨altHinv Fbar Ψ Ψ' g, g.2⟩
  invFun v := ⟨altHE Fbar Ψ Ψ' v, (projBar_altHE Fbar Ψ Ψ' v).trans v.2⟩
  left_inv g := Subtype.ext (altHE_altHinv Fbar Ψ Ψ' g)
  right_inv v := Subtype.ext (altHinv_altHE Fbar Ψ Ψ' v)

/-- The linear structure of the fibres of `p`, transported by `H`. -/
instance instAddCommGroupFiberBar (x : MS Fbar Ψ Ψ') :
    AddCommGroup (projBar Fbar Ψ Ψ' ⁻¹' {x}) :=
  (fiberEquivBar Fbar Ψ Ψ' x).addCommGroup

instance instModuleFiberBar (x : MS Fbar Ψ Ψ') : Module ℝ (projBar Fbar Ψ Ψ' ⁻¹' {x}) :=
  (fiberEquivBar Fbar Ψ Ψ' x).module ℝ

/-- `H : π⁻¹(h) → p⁻¹(h)` is linear. -/
def fiberLinBar (x : MS Fbar Ψ Ψ') :
    pullbackProj (Fb.strU Ψ).p (trSrc Fbar.toTD Ψ Ψ') ⁻¹' {x} ≃ₗ[ℝ]
      projBar Fbar Ψ Ψ' ⁻¹' {x} :=
  ((fiberEquivBar Fbar Ψ Ψ' x).linearEquiv ℝ).symm

theorem fiberLinBar_apply (x : MS Fbar Ψ Ψ')
    (v : pullbackProj (Fb.strU Ψ).p (trSrc Fbar.toTD Ψ Ψ') ⁻¹' {x}) :
    (fiberLinBar Fbar Ψ Ψ' x v : MB Fbar Ψ Ψ') = altHHomeo Fbar Ψ Ψ' v := rfl

/-- **2021 Theorem 19.6.13, p. 900: the strong bundle `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`**, the
structure for which `H` is a strong bundle isomorphism (p. 901), over the natural M-polyfold
structure of `M(Ψ, Ψ')`. -/
def bundleBar : StrongBundle (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
    (projBar Fbar Ψ Ψ') :=
  (srcBundle Fbar.toTD Ψ Ψ').transport (altHHomeo Fbar Ψ Ψ') (fiberLinBar Fbar Ψ Ψ')
    (fiberLinBar_apply Fbar Ψ Ψ')

/-! ### Theorem 19.6.13 -/

/-- **2021 Theorem 19.6.13 (p. 901): `H` is a strong bundle isomorphism** covering the identity
of `M(Ψ, Ψ')` (this characterizes the structure). -/
theorem theorem_19_6_13_H :
    (srcBundle Fbar.toTD Ψ Ψ').IsStrongBundleIso (bundleBar Fbar Ψ Ψ') id (altHHomeo Fbar Ψ Ψ')
      id (altHHomeo Fbar Ψ Ψ').symm :=
  (srcBundle Fbar.toTD Ψ Ψ').isStrongBundleIso_transport

/-- **2021 Theorem 19.6.13: the total space structure is the natural M-polyfold structure of
`M(Ψ̄, Ψ̄')`** (Theorem 19.5.1 for `E_μ`): the identity is an sc-diffeomorphism. -/
theorem theorem_19_6_13_total :
    (bundleBar Fbar Ψ Ψ').toMPolyfold0.IsScDiffeoOn (MBpoly Fbar Ψ Ψ') id id univ univ := by
  have hi := theorem_19_6_13_H Fbar Ψ Ψ'
  exact ⟨((isScSmoothMap_altHE Fbar Ψ Ψ').comp hi.invMap.isScSmoothMap).congr
      fun g _ => altHE_altHinv Fbar Ψ Ψ' g,
    (hi.toMap.isScSmoothMap.comp (isScSmoothMap_altHinv Fbar Ψ Ψ')).congr
      fun g _ => altHE_altHinv Fbar Ψ Ψ' g,
    mapsTo_univ _ _, mapsTo_univ _ _, fun _ _ => rfl, fun _ _ => rfl⟩

/-- `H⁻¹` is a strong bundle isomorphism over the whole base. -/
theorem isStrongBundleIsoOn_altHinv :
    (bundleBar Fbar Ψ Ψ').IsStrongBundleIsoOn (srcBundle Fbar.toTD Ψ Ψ')
      (theorem_19_6_13_H Fbar Ψ Ψ').invMap univ univ :=
  (theorem_19_6_13_H Fbar Ψ Ψ').symm.isStrongBundleIsoOn_univ

/-- **2021 Theorem 19.6.13: the source map `s : M(Ψ̄, Ψ̄') → K` is a strong bundle map covering
`s : M(Ψ, Ψ') → O`** (`s = π_K ∘ H⁻¹`, (19.20)). -/
theorem theorem_19_6_13_s :
    (bundleBar Fbar Ψ Ψ').IsStrongBundleMap (Fb.strU Ψ).B (trSrc Fbar.toTD Ψ Ψ')
      fun g : MB Fbar Ψ Ψ' => (g : Ψ.1.Trans Ψ'.1).src :=
  ((Fb.strU Ψ).B.isStrongBundleMap_pullbackProj' (isScSmoothMap_trSrc Fbar.toTD Ψ Ψ')).comp
    (theorem_19_6_13_H Fbar Ψ Ψ').invMap

/-- **2021 Theorem 19.6.13: `s` is locally diffeomorphic**: near every fibre it is a strong bundle
isomorphism onto an open set. -/
theorem theorem_19_6_13_s_local (x : MS Fbar Ψ Ψ') :
    ∃ (U : Set (MS Fbar Ψ Ψ')) (U' : Set (Fb.strU Ψ).O), x ∈ U ∧
      (bundleBar Fbar Ψ Ψ').IsStrongBundleIsoOn (Fb.strU Ψ).B (theorem_19_6_13_s Fbar Ψ Ψ') U U' :=
  StrongBundle.IsStrongBundleIsoOn.exists_comp
    (StrongBundle.isStrongBundleIsoOn_pullbackProj' (Fb.strU Ψ).B
      (isScSmoothMap_trSrc Fbar.toTD Ψ Ψ')
      (Fbar.toTD.isScDiffeoOn_map (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') x).symm x)
    (isStrongBundleIsoOn_altHinv Fbar Ψ Ψ') (mem_univ x) (mem_image_map_self x)

theorem tgt_eq_altTheta_comp :
    (fun g : MB Fbar Ψ Ψ' => (g : Ψ.1.Trans Ψ'.1).tgt) =
      (fun x => (altH Fbar.toTD Ψ Ψ' x).tgt) ∘ (altHHomeo Fbar Ψ Ψ').symm :=
  funext fun g => congrArg TransitionSet.tgt (altHE_altHinv Fbar Ψ Ψ' g).symm

/-- **2021 Theorem 19.6.13: the target map `t : M(Ψ̄, Ψ̄') → K'` is a strong bundle map covering
`t : M(Ψ, Ψ') → O'`** (`t = π_K' ∘ C ∘ H⁻¹`). -/
theorem theorem_19_6_13_t :
    (bundleBar Fbar Ψ Ψ').IsStrongBundleMap (Fb.strU Ψ').B (trTgt Fbar.toTD Ψ Ψ')
      fun g : MB Fbar Ψ Ψ' => (g : Ψ.1.Trans Ψ'.1).tgt := by
  rw [tgt_eq_altTheta_comp]
  exact (isStrongBundleMap_altTheta Fbar Ψ Ψ').comp (theorem_19_6_13_H Fbar Ψ Ψ').invMap

/-- **2021 Theorem 19.6.13: `t` is locally diffeomorphic.** -/
theorem theorem_19_6_13_t_local (x : MS Fbar Ψ Ψ') :
    ∃ (U : Set (MS Fbar Ψ Ψ')) (U' : Set (Fb.strU Ψ').O), x ∈ U ∧
      (bundleBar Fbar Ψ Ψ').IsStrongBundleIsoOn (Fb.strU Ψ').B (theorem_19_6_13_t Fbar Ψ Ψ') U
        U' := by
  obtain ⟨g, Ψinv, hl⟩ := isLocalIso₂_altTheta Fbar Ψ Ψ' x
  obtain ⟨U, U', hx, hi⟩ := StrongBundle.IsStrongBundleIsoOn.exists_comp
    (hl.isStrongBundleIsoOn (isStrongBundleMap_altTheta Fbar Ψ Ψ'))
    (isStrongBundleIsoOn_altHinv Fbar Ψ Ψ') (mem_univ x) (mem_image_map_self x)
  exact ⟨U, U', hx, hi.of_eq_map (tgt_eq_altTheta_comp Fbar Ψ Ψ').symm _⟩

/-- `H ∘ (u ∘ p, Id) = u`: `H((u(p(a)), a)) = (a, 1, a)`. -/
theorem unitBar_eq (Ψ : Fb.Unif) :
    (fun a : Ψ.1.O => (Fbar.toETD.toTr (TransitionSet.unit a : Ψ.1.Trans Ψ.1) : MB Fbar Ψ Ψ)) =
      altHHomeo Fbar Ψ Ψ ∘ pullbackPair (Fb.strU Ψ).p (trSrc Fbar.toTD Ψ Ψ)
        ((fun o => Fbar.toTD.toTr (TransitionSet.unit o :
          (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ).1)) ∘ (Fb.strU Ψ).p) id (fun _ => rfl) :=
  funext fun a => (Fb.strU Ψ).eq_of_proj (Fb.strU Ψ) rfl
    (((Fb.strU Ψ).proj_unit a).trans ((Fb.strU Ψ).proj_lift (Fb.strU Ψ) _ _ _).symm)

/-- **2021 Theorem 19.6.13: the unit map `u : K → M(Ψ̄, Ψ̄)` is a strong bundle map covering
`u : O → M(Ψ, Ψ)`** (`u = H ∘ (u ∘ p, Id)`, p. 904). -/
theorem theorem_19_6_13_u (Ψ : Fb.Unif) :
    (Fb.strU Ψ).B.IsStrongBundleMap (bundleBar Fbar Ψ Ψ)
      (fun o => Fbar.toTD.toTr (TransitionSet.unit o :
        (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ).1))
      fun a : Ψ.1.O => (Fbar.toETD.toTr (TransitionSet.unit a : Ψ.1.Trans Ψ.1) : MB Fbar Ψ Ψ) := by
  rw [unitBar_eq]
  exact (theorem_19_6_13_H Fbar Ψ Ψ).toMap.comp
    (StrongBundle.isStrongBundleMap_pullbackPair (Fb.strU Ψ).B (isScSmoothMap_trSrc Fbar.toTD Ψ Ψ)
      (Fbar.toTD.isScSmoothMap_unit (Fb.baseUnif Ψ)) (StrongBundle.IsStrongBundleMap.id _))

/-- The inversion `ι : M(Ψ̄, Ψ̄') → M(Ψ̄', Ψ̄)`. -/
abbrev invBar (g : MB Fbar Ψ Ψ') : MB Fbar Ψ' Ψ :=
  Fbar.toETD.toTr (g : Ψ.1.Trans Ψ'.1).inv

/-- **`ι = H ∘ (A ∘ C) ∘ H⁻¹`** (p. 904: `ῑ((q, φ, q'), k) = (ι(q, φ, q'), C(k))`). -/
theorem invBar_eq :
    invBar Fbar Ψ Ψ' = altHHomeo Fbar Ψ' Ψ ∘
      ((altA Fbar.toTD Ψ Ψ' ∘ altC Fbar.toTD Ψ Ψ') ∘ (altHHomeo Fbar Ψ Ψ').symm) :=
  funext fun g => (Fb.strU Ψ').eq_of_proj (Fb.strU Ψ)
    (congrArg TransitionSet.tgt (altHE_altHinv Fbar Ψ Ψ' g).symm)
    ((Fb.strU Ψ').proj_lift (Fb.strU Ψ) _ _ _).symm

/-- `ι : M(Ψ̄, Ψ̄') → M(Ψ̄', Ψ̄)` is a strong bundle map covering `ι`. -/
theorem isStrongBundleMap_invBar :
    (bundleBar Fbar Ψ Ψ').IsStrongBundleMap (bundleBar Fbar Ψ' Ψ) (trInv Fbar.toTD Ψ Ψ')
      (invBar Fbar Ψ Ψ') := by
  rw [invBar_eq]
  exact (theorem_19_6_13_H Fbar Ψ' Ψ).toMap.comp
    (((isStrongBundleIso_altA Fbar.toTD Ψ Ψ').toMap.comp (isStrongBundleMap_altC Fbar Ψ Ψ')).comp
      (theorem_19_6_13_H Fbar Ψ Ψ').invMap)

/-- **2021 Theorem 19.6.13: the inversion map `ι : M(Ψ̄, Ψ̄') → M(Ψ̄', Ψ̄)` is a strong bundle
isomorphism covering `ι : M(Ψ, Ψ') → M(Ψ', Ψ)`** (p. 904). -/
theorem theorem_19_6_13_inv :
    (bundleBar Fbar Ψ Ψ').IsStrongBundleIso (bundleBar Fbar Ψ' Ψ) (trInv Fbar.toTD Ψ Ψ')
      (invBar Fbar Ψ Ψ') (trInv Fbar.toTD Ψ' Ψ) (invBar Fbar Ψ' Ψ) :=
  ⟨isStrongBundleMap_invBar Fbar Ψ Ψ', isStrongBundleMap_invBar Fbar Ψ' Ψ,
    fun g => TransitionSet.inv_inv (g : Ψ.1.Trans Ψ'.1),
    fun g => TransitionSet.inv_inv (g : Ψ'.1.Trans Ψ.1)⟩

/-- **The conclusions of 2021 Theorem 19.6.13** for `Ψ̄, Ψ̄'`, for the strong bundle
`bundleBar : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` over the natural M-polyfold structure of `M(Ψ, Ψ')`: `H` is a
strong bundle isomorphism; the total space structure is the natural M-polyfold structure of
`M(Ψ̄, Ψ̄')`; `s` and `t` are locally diffeomorphic strong bundle maps; the unit map is a strong
bundle map; the inversion is a strong bundle isomorphism (the multiplication:
`theorem_19_6_13_m`). -/
def Theorem_19_6_13_Statement : Prop :=
  (srcBundle Fbar.toTD Ψ Ψ').IsStrongBundleIso (bundleBar Fbar Ψ Ψ') id (altHHomeo Fbar Ψ Ψ')
      id (altHHomeo Fbar Ψ Ψ').symm ∧
    (bundleBar Fbar Ψ Ψ').toMPolyfold0.IsScDiffeoOn (MBpoly Fbar Ψ Ψ') id id univ univ ∧
    (∃ h : (bundleBar Fbar Ψ Ψ').IsStrongBundleMap (Fb.strU Ψ).B (trSrc Fbar.toTD Ψ Ψ')
        (fun g : MB Fbar Ψ Ψ' => (g : Ψ.1.Trans Ψ'.1).src),
      ∀ x, ∃ (U : Set (MS Fbar Ψ Ψ')) (U' : Set (Fb.strU Ψ).O), x ∈ U ∧
        (bundleBar Fbar Ψ Ψ').IsStrongBundleIsoOn (Fb.strU Ψ).B h U U') ∧
    (∃ h : (bundleBar Fbar Ψ Ψ').IsStrongBundleMap (Fb.strU Ψ').B (trTgt Fbar.toTD Ψ Ψ')
        (fun g : MB Fbar Ψ Ψ' => (g : Ψ.1.Trans Ψ'.1).tgt),
      ∀ x, ∃ (U : Set (MS Fbar Ψ Ψ')) (U' : Set (Fb.strU Ψ').O), x ∈ U ∧
        (bundleBar Fbar Ψ Ψ').IsStrongBundleIsoOn (Fb.strU Ψ').B h U U') ∧
    (Fb.strU Ψ).B.IsStrongBundleMap (bundleBar Fbar Ψ Ψ)
      (fun o => Fbar.toTD.toTr (TransitionSet.unit o :
        (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ).1))
      (fun a : Ψ.1.O => (Fbar.toETD.toTr (TransitionSet.unit a : Ψ.1.Trans Ψ.1) : MB Fbar Ψ Ψ)) ∧
    (bundleBar Fbar Ψ Ψ').IsStrongBundleIso (bundleBar Fbar Ψ' Ψ) (trInv Fbar.toTD Ψ Ψ')
      (invBar Fbar Ψ Ψ') (trInv Fbar.toTD Ψ' Ψ) (invBar Fbar Ψ' Ψ)

/-- **2021 Theorem 19.6.13, p. 900**, for bundle transition data `F̄`. -/
theorem theorem_19_6_13_of_bundleTransitionData : Theorem_19_6_13_Statement Fbar Ψ Ψ' :=
  ⟨theorem_19_6_13_H Fbar Ψ Ψ', theorem_19_6_13_total Fbar Ψ Ψ',
    ⟨theorem_19_6_13_s Fbar Ψ Ψ', theorem_19_6_13_s_local Fbar Ψ Ψ'⟩,
    ⟨theorem_19_6_13_t Fbar Ψ Ψ', theorem_19_6_13_t_local Fbar Ψ Ψ'⟩,
    theorem_19_6_13_u Fbar Ψ, theorem_19_6_13_inv Fbar Ψ Ψ'⟩

end Theorem

end StrongBundleUniformizerConstruction

namespace BasicStrongBundleConstruction

open StrongBundleUniformizerConstruction

variable {μ : C.BanFunctor} (B : C.BasicStrongBundleConstruction μ)

/-- `M(Ψ̄, Ψ̄')` of the representative `F̄` is `MBar` of Lemma 19.6.12. -/
theorem MB_eq_MBar (Ψ Ψ' : B.U.Unif) :
    MB B.rep Ψ Ψ' = B.MBar (B.U.toEUnif Ψ) (B.U.toEUnif Ψ') := rfl

/-- **2021 Theorem 19.6.13, p. 900**: for a basic bundle construction `(F̄, 𝓕̄)` and `Ψ̄, Ψ̄'`,
`p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` is a strong bundle (over the natural M-polyfold structure of
`M(Ψ, Ψ')`, with the natural M-polyfold structure on `M(Ψ̄, Ψ̄')`), `s`, `t` are locally
diffeomorphic strong bundle maps, the unit map is a strong bundle map and the inversion is a
strong bundle isomorphism.  (The representative `F̄` of `𝓕̄` is `B.rep`.) -/
theorem theorem_19_6_13 (Ψ Ψ' : B.U.Unif) : Theorem_19_6_13_Statement B.rep Ψ Ψ' :=
  theorem_19_6_13_of_bundleTransitionData B.rep Ψ Ψ'

/-- **2021 Theorem 19.6.13, p. 900**, with the hypotheses of the text: every class of `S` meets
`F` and the natural topology `T` of `|S|` is metrizable. -/
theorem theorem_19_6_13_book (hB : B.base.U.HasClassUniformizers)
    (_hT : @MetrizableSpace _ (B.topS hB)) (Ψ Ψ' : B.U.Unif) :
    Theorem_19_6_13_Statement B.rep Ψ Ψ' :=
  B.theorem_19_6_13 Ψ Ψ'

end BasicStrongBundleConstruction

open StrongBundleUniformizerConstruction in
/-- **The witness**: the conclusions of Theorem 19.6.13 for the reflection bundle, with the
hypotheses of the text satisfied (`reflBanBasic_hB`, `reflBanBasic_metrizable`). -/
theorem reflBan_theorem_19_6_13 : Theorem_19_6_13_Statement reflBanBasic.rep reflΨ reflΨ :=
  reflBanBasic.theorem_19_6_13_book reflBanBasic_hB reflBanBasic_metrizable.1 reflΨ reflΨ

end GroupoidalCategory

end Polyfold
