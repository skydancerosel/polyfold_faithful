import Polyfold.Chapter10.StrongBundleEquivalenceNat

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.4 "Strong Bundles and Equivalences" (pp. 495–503; 2017: pp. 357–363):
witnesses for **Definitions 10.4.1, 10.4.8, 10.4.10, 10.4.11** and an instance of
**Theorem 10.4.5**.  The text gives no examples.

# Strong bundle equivalences: examples

## The text, paraphrased

The text does not discuss examples of strong bundle equivalences.

## What is formalized

* Part I's trivial strong bundle `W' = ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ`
  (`TrivialBundle.epBundle`), its pull-back `W = (-id)*W'` along `x ↦ -x` (`negBundle`,
  `negEpBundle`), and the functor `-id` of the trivial ep-groupoid (`trivialNeg`).
* `isStrongBundleEquivalence_pullbackProj'`: the projection `P' : (-id)*W' → W'`, `(x, w') ↦ w'`,
  is a **strong bundle equivalence** (Definition 10.4.1) covering `-id`, with inverse
  `w' ↦ (-P(w'), w')` (`negInv`, `isStrongBundleMap_negInv`); `trivialNeg_obj_ne_id` (`ϕ ≠ id`
  for `n ≥ 1`).  `isStrongBundleEquivalence_id_epBundle`: the identity.
* `bijOn_pushforward_example` (Theorem 10.4.5 for the example), `strongBundleNatEquiv_example`
  (Definition 10.4.8), and `negSEPHom_mem_equivalences` (the example as a morphism in the class
  `F` of `SEP`, Definition 10.4.11).

## What the text leaves implicit, and the choices made

* The example is an isomorphism of strong bundles over ep-groupoids
  (`EpStrongBundle.isStrongBundleEquivalence_of_inverse`); `W` and `W'` are different bundles.

## Not formalized

* Nothing.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

namespace StrongBundleEquivalenceExamples

open TrivialBundle

variable (n k : ℕ)

/-- `x ↦ -x` on `ℝⁿ`. -/
def negMap : (Fin n → ℝ) → (Fin n → ℝ) := fun x => -x

theorem isScSmoothMap_negMap : (rnPolyfold n).IsScSmoothMap (rnPolyfold n) (negMap n) :=
  (isLocalScDiffeo_rn_neg n).isScSmoothMap

/-- **The functor `-id`** of the trivial ep-groupoid of `ℝⁿ` (objects and morphisms `ℝⁿ`). -/
def trivialNeg : EpFunctor (EpGroupoid.trivial (rnPolyfold n)) (EpGroupoid.trivial (rnPolyfold n))
    where
  obj := negMap n
  mor := negMap n
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := isScSmoothMap_negMap n
  isScSmoothMap_mor := isScSmoothMap_negMap n

instance : ParacompactSpace (pullbackSpace (proj n k) (negMap n)) :=
  (bundle n k).paracompactSpace_pullback (rnPolyfold n) (negMap n)

/-- The pull-back `(-id)*(ℝⁿ × ℝᵏ)` of Part I's trivial strong bundle along `x ↦ -x`. -/
def negBundle : StrongBundle (rnPolyfold n) (pullbackProj (proj n k) (negMap n)) :=
  (bundle n k).pullback (isScSmoothMap_negMap n)

instance : ParacompactSpace (pullbackSpace (pullbackProj (proj n k) (negMap n))
    (EpGroupoid.trivial (rnPolyfold n)).src) :=
  (negBundle n k).paracompactSpace_pullback (rnPolyfold n) _

/-- `(-id)*(ℝⁿ × ℝᵏ)` as a strong bundle over the trivial ep-groupoid of `ℝⁿ`. -/
def negEpBundle : EpStrongBundle (EpGroupoid.trivial (rnPolyfold n)) (negBundle n k) :=
  EpStrongBundle.trivial (negBundle n k)

/-- `Φ = P' : (-id)*W' → W'`, `(x, w') ↦ w'`, covering `-id`. -/
theorem isMap_pullbackProj' : (negEpBundle n k).IsMap (epBundle n k) (trivialNeg n)
    (pullbackProj' (proj n k) (negMap n)) where
  isStrongBundleMap := (bundle n k).isStrongBundleMap_pullbackProj' (isScSmoothMap_negMap n)
  map_μ _ _ _ := rfl

/-- The inverse `w' ↦ (-P(w'), w')`. -/
def negInv (w : (Fin n → ℝ) × (Fin k → ℝ)) : pullbackSpace (proj n k) (negMap n) :=
  ⟨(-w.1, w), (neg_neg w.1).symm⟩

theorem isStrongBundleMap_negInv :
    (bundle n k).IsStrongBundleMap (negBundle n k) (negMap n) (negInv n k) where
  covers _ := rfl
  fiber_linear x := by
    let L : proj n k ⁻¹' {x} →ₗ[ℝ] pullbackProj (proj n k) (negMap n) ⁻¹' {negMap n x} :=
      ((pullbackFiberLinearEquiv (proj n k) (negMap n) (negMap n x)).symm.toLinearMap).comp
        (fiberCast (proj n k) (neg_neg x).symm)
    have hL : fiberRestrict (proj n k) (pullbackProj (proj n k) (negMap n)) (negMap n)
        (negInv n k) (fun _ => rfl) x = L := by
      funext v
      apply Subtype.ext; apply Subtype.ext
      have hv : (v : (Fin n → ℝ) × (Fin k → ℝ)).1 = x := v.2
      change (-(v : (Fin n → ℝ) × (Fin k → ℝ)).1, (v : (Fin n → ℝ) × (Fin k → ℝ))) =
        (negMap n x, ((fiberCast (proj n k) (neg_neg x).symm v :
          proj n k ⁻¹' {negMap n (negMap n x)}) : (Fin n → ℝ) × (Fin k → ℝ)))
      rw [fiberCast_val, hv]
      rfl
    rw [hL]; exact L.isLinear
  isScSmoothMap := (bundle n k).isScSmoothMap_pullbackPair (isScSmoothMap_negMap n)
    (a := negMap n ∘ proj n k) (b := id)
    ((isScSmoothMap_negMap n).comp (bundle n k).isScSmoothMap_proj) MPolyfold.isScSmoothMap_id
    fun w => (neg_neg w.1).symm
  mapsTo_oneSet _ hy := ((bundle n k).mem_oneSet_pullback_iff (isScSmoothMap_negMap n) _).2 hy
  isScSmoothMap_one := by
    refine (bundle n k).isScSmoothMap_to_pullback_one (isScSmoothMap_negMap n) ?_ ?_
    · exact (isScSmoothMap_negMap n).comp (bundle n k).isScSmoothMap_proj1
    · exact MPolyfold.IsScSmoothOn.congr MPolyfold.isScSmoothMap_id fun a _ =>
        (bundle n k).oneVal_injective rfl

theorem isMap_negInv : (epBundle n k).IsMap (negEpBundle n k) (trivialNeg n) (negInv n k) where
  isStrongBundleMap := isStrongBundleMap_negInv n k
  map_μ _ _ _ := rfl

/-- **A non-identity strong bundle equivalence** (Definition 10.4.1): `P' : (-id)*W' → W'`
covering `-id`, from the pull-back of `W' = ℝⁿ × ℝᵏ` along `x ↦ -x` to `W'`, both over the
trivial ep-groupoid of `ℝⁿ` (an isomorphism of strong bundles over ep-groupoids). -/
theorem isStrongBundleEquivalence_pullbackProj' :
    (negEpBundle n k).IsStrongBundleEquivalence (epBundle n k) (trivialNeg n)
      (isMap_pullbackProj' n k).liftFunctor :=
  EpStrongBundle.isStrongBundleEquivalence_of_inverse (isMap_pullbackProj' n k)
    (isMap_negInv n k) (fun x => neg_neg x) (fun x => neg_neg x) (fun x => neg_neg x)
    (fun x => neg_neg x)
    (fun q => Subtype.ext (Prod.ext (by
      have hq : (q : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin k → ℝ))).2.1 =
          -(q : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin k → ℝ))).1 := q.2
      change -(q : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin k → ℝ))).2.1 = _
      rw [hq, neg_neg]) rfl))
    fun _ => rfl

/-- The equivalence is not the identity: `ϕ = -id ≠ id` for `n ≥ 1`. -/
theorem trivialNeg_obj_ne_id [NeZero n] : (trivialNeg n).obj ≠ id := fun h => by
  have h1 := congrFun h (fun _ => 1)
  have h2 := congrFun h1 0
  change -(1 : ℝ) = 1 at h2
  norm_num at h2

/-- **The identity is a strong bundle equivalence** of `ℝⁿ × ℝᵏ → ℝⁿ` (the second witness). -/
theorem isStrongBundleEquivalence_id_epBundle :
    (epBundle n k).IsStrongBundleEquivalence (epBundle n k) (EpFunctor.id _) (EpFunctor.id _) :=
  EpStrongBundle.isStrongBundleEquivalence_id (epBundle n k)

/-- **Theorem 10.4.5 for the example**: the push-forward along `P'` gives mutually inverse
bijections `Γ((-id)*W') ≅ Γ(W')`. -/
theorem bijOn_pushforward_example :
    BijOn (isStrongBundleEquivalence_pullbackProj' n k).pushforward
      (negEpBundle n k).sectionFunctors (epBundle n k).sectionFunctors :=
  (EpStrongBundle.theorem_10_4_5 (isStrongBundleEquivalence_pullbackProj' n k)).1.2.2.2

/-- **Witness for Definitions 10.4.8 and 10.4.10**: `Φ ≃ Φ` for the example. -/
theorem strongBundleNatEquiv_example :
    (negEpBundle n k).StrongBundleNatEquiv (epBundle n k) (trivialNeg n) (trivialNeg n)
      (isMap_pullbackProj' n k).liftFunctor (isMap_pullbackProj' n k).liftFunctor :=
  ⟨EpStrongBundle.StrongBundleNatTrans.refl
    (isMap_pullbackProj' n k).isStrongBundleFunctor_liftFunctor⟩

/-- `(-id)*W'` as an object of `SEP` (Definition 10.4.11). -/
def negSEP : SEP.{0} :=
  ⟨_, _, EpGroupoid.trivial (rnPolyfold n), _, pullbackProj (proj n k) (negMap n), negBundle n k,
    negEpBundle n k⟩

/-- `W' = ℝⁿ × ℝᵏ` as an object of `SEP`. -/
def epSEP : SEP.{0} :=
  ⟨_, _, EpGroupoid.trivial (rnPolyfold n), _, proj n k, bundle n k, epBundle n k⟩

/-- The example as a morphism of `SEP`. -/
def negSEPHom : negSEP n k ⟶ epSEP n k :=
  ⟨trivialNeg n, (isMap_pullbackProj' n k).liftFunctor,
    (isMap_pullbackProj' n k).isStrongBundleFunctor_liftFunctor⟩

/-- The example lies in the class `F` of strong bundle equivalences (Definition 10.4.11). -/
theorem negSEPHom_mem_equivalences : SEP.equivalences (negSEPHom n k) :=
  isStrongBundleEquivalence_pullbackProj' n k

end StrongBundleEquivalenceExamples

end Polyfold
