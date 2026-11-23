import Polyfold.Examples.OrbifoldSquareAlgebra
import Polyfold.Chapter16.FibreNegationStructure
import Polyfold.Chapter19.CoveringSquareExamples

/-!
# The orbifold `ℂ/ℤ₅` and the section `z ↦ z²`: the strong bundle over the ep-groupoid

A worked example for Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021),
Theorem 16.6.6, 2021 p. 739.

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquare`)

* `instMulActionBase`: `ℤ/5` acts on `ℝ² = ℂ` by `g · z = ζ^g z`; `X5 = ℤ/5 ⋉ ℂ`, the
  translation ep-groupoid (Chapter 7's `actionEpGroupoid`).
* `actW`: `g · (z, w) = (ζ^g z, ζ^{2g} w)` on `ℂ × ℂ`; `E5`: the strong bundle `ℂ × ℂ → ℂ` over
  `X5` with `μ((g, z), w) = g · w` (Definition 8.3.1); `A5`: the object of `SEP`.
* `sqSection`: the section `z ↦ (z, z²)`; `sqSection_mem_sectionFunctors`,
  `isScFredholmSectionFunctor_sqSection`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.OrbifoldSquare

open TrivialBundle EpGroupoid.Examples StrongBundle

/-- `ℤ/5`, written multiplicatively. -/
abbrev G5 : Type := Multiplicative (ZMod 5)

/-- `ℤ/5` acts on `ℝ² = ℂ` by `g · z = ζ^g z`. -/
scoped instance instMulActionBase : MulAction G5 (Fin 2 → ℝ) where
  smul g x := rot (χ g) x
  one_smul x := by
    change rot (χ 1) x = x
    rw [χ_one, rot_one]
  mul_smul g h x := by
    change rot (χ (g * h)) x = rot (χ g) (rot (χ h) x)
    rw [χ_mul, rot_mul]

theorem smul_def (g : G5) (x : Fin 2 → ℝ) : g • x = rot (χ g) x := rfl

theorem smul_eq_self_iff {g : G5} (hg : g ≠ 1) (x : Fin 2 → ℝ) : g • x = x ↔ x = 0 :=
  rot_eq_self_iff (fun h => hg ((χ_eq_one_iff g).1 h)) x

theorem smul_zero5 (g : G5) : g • (0 : Fin 2 → ℝ) = 0 := map_zero (rot (χ g))

theorem contDiff_smul (g : G5) : ContDiff ℝ ∞ fun x : Fin 2 → ℝ => g • x :=
  (rot (χ g)).contDiff

theorem isScSmoothMap_smul (g : G5) :
    (rnPolyfold 2).IsScSmoothMap (rnPolyfold 2) fun y : Fin 2 → ℝ => g • y :=
  isScSmoothMap_rn_of_contDiff (contDiff_smul g)

/-- **`ℤ/5 ⋉ ℂ`**: the translation ep-groupoid of `g · z = ζ^g z`. -/
def X5 : EpGroupoid (Fin 2 → ℝ) (G5 × (Fin 2 → ℝ)) := actionEpGroupoid isScSmoothMap_smul

/-- The action on `ℂ × ℂ`: `g · (z, w) = (ζ^g z, ζ^{2g} w)` (weight `2` on the fibre). -/
def actW (g : G5) : (Fin 2 → ℝ) × (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  prodLinMap (fun x => g • x) (rot (χ g ^ 2))

theorem actW_apply (g : G5) (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    actW g w = (g • w.1, rot (χ g ^ 2) w.2) := rfl

theorem actW_one (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : actW 1 w = w := by
  rw [actW_apply, one_smul, χ_one, one_pow, rot_one]

theorem actW_mul (g h : G5) (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    actW (g * h) w = actW g (actW h w) := by
  rw [actW_apply, actW_apply, actW_apply, mul_smul, χ_mul, mul_pow, rot_mul]

theorem actW_inv_actW (g : G5) (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : actW g⁻¹ (actW g w) = w := by
  rw [← actW_mul, inv_mul_cancel, actW_one]

theorem actW_actW_inv (g : G5) (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : actW g (actW g⁻¹ w) = w := by
  rw [← actW_mul, mul_inv_cancel, actW_one]

/-- **`g · ` is a strong bundle map of `ℂ × ℂ → ℂ`** covering `g ·`. -/
theorem isStrongBundleMap_actW (g : G5) :
    (bundle 2 2).IsStrongBundleMap (bundle 2 2) (fun x => g • x) (actW g) :=
  isStrongBundleMap_prodLinMap (contDiff_smul g) _

instance : ParacompactSpace (pullbackSpace (proj 2 2) X5.src) :=
  (bundle 2 2).paracompactSpace_pullback X5.PMor _

/-- `μ((g, z), w) = g · w`. -/
def mu (q : pullbackSpace (proj 2 2) X5.src) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  actW (q : (G5 × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))).1.1
    (q : (G5 × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))).2

theorem isStrongBundleMap_mu :
    ((bundle 2 2).pullback X5.isScSmoothMap_src).IsStrongBundleMap (bundle 2 2) X5.tgt mu := by
  refine StrongBundle.isStrongBundleMap_of_locally_eqOn (fun q => ?_) fun x => ?_
  · obtain ⟨⟨⟨g, o⟩, w⟩, hq⟩ := q
    have hq' : w.1 = o := hq
    change g • w.1 = g • o
    rw [hq']
  · refine ⟨Prod.fst ⁻¹' {x.1}, (isOpen_discrete _).preimage continuous_fst, rfl, _, _,
      (isStrongBundleMap_actW x.1).comp ((bundle 2 2).isStrongBundleMap_pullbackProj'
        X5.isScSmoothMap_src), fun q hq => ?_⟩
    have hq' : (q : (G5 × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))).1.1 = x.1 := hq
    change actW (q : (G5 × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))).1.1 _ = actW x.1 _
    rw [hq']
    rfl

theorem isLocalScDiffeo_mu :
    ((bundle 2 2).pullback X5.isScSmoothMap_src).toMPolyfold0.IsLocalScDiffeo
      (bundle 2 2).toMPolyfold0 mu := by
  have hπ := (bundle 2 2).isLocalScDiffeo_pullbackProj' X5.isScSmoothMap_src
    X5.isLocalScDiffeo_src
  intro q
  set g := (q : (G5 × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))).1.1
  have hg : (bundle 2 2).toMPolyfold0.IsLocalScDiffeo (bundle 2 2).toMPolyfold0 (actW g) :=
    GroupoidalCategory.CoveringBasicConstruction.isLocalScDiffeo_of_isScDiffeoOn_univ
      (g := actW g⁻¹)
      ⟨(isStrongBundleMap_actW g).isScSmoothMap, (isStrongBundleMap_actW g⁻¹).isScSmoothMap,
        mapsTo_univ _ _, mapsTo_univ _ _, fun w _ => actW_inv_actW g w,
        fun w _ => actW_actW_inv g w⟩
  have hN : IsOpen {q' : pullbackSpace (proj 2 2) X5.src |
      (q' : (G5 × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))).1.1 = g} :=
    (isOpen_discrete {g}).preimage
      (continuous_fst.comp (continuous_fst.comp continuous_subtype_val))
  obtain ⟨U, V, σ, hqU, hUN, hd⟩ := (hg.comp hπ).exists_isScDiffeoOn_subset hN rfl
  refine ⟨U, V, σ, hqU, hd.congr fun q' hq' => ?_⟩
  have h' : (q' : (G5 × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))).1.1 = g := hUN hq'
  change actW g _ = actW (q' : (G5 × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))).1.1 _
  rw [h']
  rfl

/-- **`ℂ × ℂ → ℂ` as a strong bundle over `ℤ/5 ⋉ ℂ`** (Definition 8.3.1), with
`μ((g, z), w) = g · w`, weight `1` on the base and weight `2` on the fibre. -/
def E5 : EpStrongBundle X5 (bundle 2 2) where
  μ := mu
  isStrongBundleMap := isStrongBundleMap_mu
  surjective w := ⟨⟨((1, w.1), w), rfl⟩, actW_one w⟩
  isLocalScDiffeo := isLocalScDiffeo_mu
  μ_unit w := actW_one w
  μ_comp ψ γ w _ _ := actW_mul ψ.1 γ.1 w

@[simp] theorem E5_μ (q : pullbackSpace (proj 2 2) X5.src) :
    E5.μ q = actW (q : (G5 × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))).1.1
      (q : (G5 × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))).2 := rfl

/-- `ℂ × ℂ → ℂ` over `ℤ/5 ⋉ ℂ` as an object of `SEP`. -/
def A5 : SEP.{0} := ⟨_, _, X5, _, proj 2 2, bundle 2 2, E5⟩

/-! ### The section `z ↦ (z, z²)` -/

/-- The section `f(z) = (z, z²)`. -/
abbrev sqSection : (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ) := graphSection sq

/-- `f` is equivariant: `f(g · z) = g · f(z)`. -/
theorem sqSection_smul (g : G5) (x : Fin 2 → ℝ) : sqSection (g • x) = actW g (sqSection x) := by
  change (g • x, sq (g • x)) = (g • x, rot (χ g ^ 2) (sq x))
  rw [smul_def, sq_rot]

/-- `f(z) = 0` iff `z = 0`. -/
theorem isZeroAt_sqSection_iff {x : Fin 2 → ℝ} : IsZeroAt (proj 2 2) sqSection x ↔ x = 0 :=
  isZeroAt_graphSection_iff.trans (sq_eq_zero_iff x)

/-- **`f` is an sc-Fredholm section functor** of `ℂ × ℂ → ℂ` over `ℤ/5 ⋉ ℂ`. -/
theorem isScFredholmSectionFunctor_sqSection : E5.IsScFredholmSectionFunctor sqSection := by
  obtain ⟨⟨hs, -⟩, hfred⟩ :=
    graphSection_mem_fredholmSectionFunctors_epBundle (n := 2) (k := 2) contDiff_sq
  refine ⟨⟨hs, fun φ => ?_⟩, hfred⟩
  exact sqSection_smul φ.1 φ.2

end Polyfold.Examples.OrbifoldSquare
