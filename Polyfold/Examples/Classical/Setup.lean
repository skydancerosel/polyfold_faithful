import Polyfold.Chapter3.NonVacuity
import Polyfold.Chapter16.FibreNegationStructure
import Polyfold.Chapter19.CoveringSquareExamples

/-!
# The classical reduction: a finite group acting linearly on `ℝⁿ`

Setting for the comparison of Theorem 16.6.6, 2021 p. 739 (index `0`) with the classical count
of a proper equivariant map in finite dimensions.

`G` is a finite group with the discrete topology acting linearly on `V = ℝⁿ` (a
`DistribMulAction` commuting with the scalars; `V` carries the orientation of the standard
basis).  A second linear action `σ : G →* End(W)`, `W = ℝⁿ`, acts on the fibre.

## What is formalized (namespace `Polyfold.Examples.Classical`)

* `rhoL g`: `x ↦ g • x` as a continuous linear map; `XG G n = G ⋉ ℝⁿ`, the translation
  ep-groupoid (Chapter 7's `actionEpGroupoid`).
* `actW σ g (x, w) = (g • x, σ g w)`; `EG σ`: the strong bundle `ℝⁿ × ℝⁿ → ℝⁿ` over `G ⋉ ℝⁿ`
  with `μ((g, x), w) = actW σ g w` (Definition 8.3.1); `AG σ`: the object of `SEP`.
* `fSec φ = graphSection φ`, and **`isScFredholmSectionFunctor_fSec`**: for a `C^∞` map
  `φ : ℝⁿ → ℝⁿ` with `φ (g • x) = σ g (φ x)`, the graph section is an sc-Fredholm section
  functor.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical

open TrivialBundle EpGroupoid.Examples StrongBundle

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]

/-! ### The base action -/

/-- `x ↦ g • x` as a continuous linear map of `ℝⁿ`. -/
def rhoL (g : G) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (DistribSMul.toLinearMap ℝ (Fin n → ℝ) g)

@[simp] theorem rhoL_apply (g : G) (x : Fin n → ℝ) : rhoL g x = g • x := rfl

theorem rhoL_one : rhoL (n := n) (1 : G) = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  ext x : 1
  exact one_smul G x

theorem rhoL_mul (g h : G) : rhoL (n := n) (g * h) = (rhoL g).comp (rhoL h) := by
  ext x : 1
  exact mul_smul g h x

theorem contDiff_smul (g : G) : ContDiff ℝ ∞ fun x : Fin n → ℝ => g • x :=
  (rhoL g).contDiff

theorem isScSmoothMap_smul (g : G) :
    (rnPolyfold n).IsScSmoothMap (rnPolyfold n) fun y : Fin n → ℝ => g • y :=
  isScSmoothMap_rn_of_contDiff (contDiff_smul g)

variable (G n) in
/-- **`G ⋉ ℝⁿ`**: the translation ep-groupoid of the linear action. -/
def XG : EpGroupoid (Fin n → ℝ) (G × (Fin n → ℝ)) := actionEpGroupoid (isScSmoothMap_smul (G := G))

/-! ### The fibre action -/

variable (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))

/-- The action on `ℝⁿ × ℝⁿ`: `g · (x, w) = (g • x, σ g w)`. -/
def actW (g : G) : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  prodLinMap (fun x => g • x) (σ g)

theorem actW_apply (g : G) (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    actW σ g w = (g • w.1, σ g w.2) := rfl

theorem actW_one (w : (Fin n → ℝ) × (Fin n → ℝ)) : actW σ 1 w = w := by
  rw [actW_apply, one_smul, map_one]
  rfl

theorem actW_mul (g h : G) (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    actW σ (g * h) w = actW σ g (actW σ h w) := by
  rw [actW_apply, actW_apply, actW_apply, mul_smul, map_mul]
  rfl

theorem actW_inv_actW (g : G) (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    actW σ g⁻¹ (actW σ g w) = w := by
  rw [← actW_mul, inv_mul_cancel, actW_one]

theorem actW_actW_inv (g : G) (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    actW σ g (actW σ g⁻¹ w) = w := by
  rw [← actW_mul, mul_inv_cancel, actW_one]

/-- `σ g⁻¹ (σ g w) = w`. -/
theorem σ_inv_apply (g : G) (w : Fin n → ℝ) : σ g⁻¹ (σ g w) = w := by
  have h := congrArg Prod.snd (actW_inv_actW σ g (0, w))
  exact h

theorem σ_apply_inv (g : G) (w : Fin n → ℝ) : σ g (σ g⁻¹ w) = w := by
  have h := congrArg Prod.snd (actW_actW_inv σ g (0, w))
  exact h

/-- **`g · ` is a strong bundle map of `ℝⁿ × ℝⁿ → ℝⁿ`** covering `g •`. -/
theorem isStrongBundleMap_actW (g : G) :
    (bundle n n).IsStrongBundleMap (bundle n n) (fun x => g • x) (actW σ g) :=
  isStrongBundleMap_prodLinMap (contDiff_smul g) _

instance : ParacompactSpace (pullbackSpace (proj n n) (XG G n).src) :=
  (bundle n n).paracompactSpace_pullback (XG G n).PMor _

/-- `μ((g, x), w) = g · w`. -/
def mu (q : pullbackSpace (proj n n) (XG G n).src) : (Fin n → ℝ) × (Fin n → ℝ) :=
  actW σ (q : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).1.1
    (q : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).2

theorem isStrongBundleMap_mu :
    ((bundle n n).pullback (XG G n).isScSmoothMap_src).IsStrongBundleMap (bundle n n)
      (XG G n).tgt (mu σ) := by
  refine StrongBundle.isStrongBundleMap_of_locally_eqOn (fun q => ?_) fun x => ?_
  · obtain ⟨⟨⟨g, o⟩, w⟩, hq⟩ := q
    have hq' : w.1 = o := hq
    change g • w.1 = g • o
    rw [hq']
  · refine ⟨Prod.fst ⁻¹' {x.1}, (isOpen_discrete _).preimage continuous_fst, rfl, _, _,
      (isStrongBundleMap_actW σ x.1).comp ((bundle n n).isStrongBundleMap_pullbackProj'
        (XG G n).isScSmoothMap_src), fun q hq => ?_⟩
    have hq' : (q : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).1.1 = x.1 := hq
    change actW σ (q : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).1.1 _ = actW σ x.1 _
    rw [hq']
    rfl

theorem isLocalScDiffeo_mu :
    ((bundle n n).pullback (XG G n).isScSmoothMap_src).toMPolyfold0.IsLocalScDiffeo
      (bundle n n).toMPolyfold0 (mu σ) := by
  have hπ := (bundle n n).isLocalScDiffeo_pullbackProj' (XG G n).isScSmoothMap_src
    (XG G n).isLocalScDiffeo_src
  intro q
  set g := (q : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).1.1
  have hg : (bundle n n).toMPolyfold0.IsLocalScDiffeo (bundle n n).toMPolyfold0 (actW σ g) :=
    GroupoidalCategory.CoveringBasicConstruction.isLocalScDiffeo_of_isScDiffeoOn_univ
      (g := actW σ g⁻¹)
      ⟨(isStrongBundleMap_actW σ g).isScSmoothMap, (isStrongBundleMap_actW σ g⁻¹).isScSmoothMap,
        mapsTo_univ _ _, mapsTo_univ _ _, fun w _ => actW_inv_actW σ g w,
        fun w _ => actW_actW_inv σ g w⟩
  have hN : IsOpen {q' : pullbackSpace (proj n n) (XG G n).src |
      (q' : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).1.1 = g} :=
    (isOpen_discrete {g}).preimage
      (continuous_fst.comp (continuous_fst.comp continuous_subtype_val))
  obtain ⟨U, V, s, hqU, hUN, hd⟩ := (hg.comp hπ).exists_isScDiffeoOn_subset hN rfl
  refine ⟨U, V, s, hqU, hd.congr fun q' hq' => ?_⟩
  have h' : (q' : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).1.1 = g := hUN hq'
  change actW σ g _ = actW σ (q' : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).1.1 _
  rw [h']
  rfl

/-- **`ℝⁿ × ℝⁿ → ℝⁿ` as a strong bundle over `G ⋉ ℝⁿ`** (Definition 8.3.1), with
`μ((g, x), w) = (g • x, σ g w)`. -/
def EG : EpStrongBundle (XG G n) (bundle n n) where
  μ := mu σ
  isStrongBundleMap := isStrongBundleMap_mu σ
  surjective w := ⟨⟨((1, w.1), w), rfl⟩, actW_one σ w⟩
  isLocalScDiffeo := isLocalScDiffeo_mu σ
  μ_unit w := actW_one σ w
  μ_comp ψ γ w _ _ := actW_mul σ ψ.1 γ.1 w

@[simp] theorem EG_μ (q : pullbackSpace (proj n n) (XG G n).src) :
    (EG σ).μ q = actW σ (q : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).1.1
      (q : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).2 := rfl

/-- `ℝⁿ × ℝⁿ → ℝⁿ` over `G ⋉ ℝⁿ` as an object of `SEP`. -/
def AG : SEP.{0} := ⟨_, _, XG G n, _, proj n n, bundle n n, EG σ⟩

/-! ### The graph section of an equivariant map -/

/-- The section `x ↦ (x, φ x)`. -/
abbrev fSec (φ : (Fin n → ℝ) → (Fin n → ℝ)) : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  graphSection φ

variable {σ}

/-- The graph section of an equivariant map is equivariant: `f(g • x) = g · f(x)`. -/
theorem fSec_smul {φ : (Fin n → ℝ) → (Fin n → ℝ)} (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (g : G) (x : Fin n → ℝ) : fSec φ (g • x) = actW σ g (fSec φ x) := by
  change (g • x, φ (g • x)) = (g • x, σ g (φ x))
  rw [heq]

/-- **The graph section of a `C^∞` equivariant map is an sc-Fredholm section functor** of
`ℝⁿ × ℝⁿ → ℝⁿ` over `G ⋉ ℝⁿ`. -/
theorem isScFredholmSectionFunctor_fSec {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) :
    (AG (G := G) σ).E.IsScFredholmSectionFunctor (fSec φ) := by
  obtain ⟨⟨hs, -⟩, hfred⟩ :=
    graphSection_mem_fredholmSectionFunctors_epBundle (n := n) (k := n) hφ
  refine ⟨⟨hs, fun ψ => ?_⟩, hfred⟩
  exact fSec_smul heq ψ.1 ψ.2

end Polyfold.Examples.Classical
