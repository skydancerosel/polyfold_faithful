import Polyfold.Chapter12.OrientationGeneralizedIsoExample
import Polyfold.Chapter12.OrientationGeneralizedIsoUnique
import Polyfold.Chapter6.OrientationBundle
import Polyfold.Chapter1.ExpositionLemmas

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7 (2)** (2017: Theorem 12.12 (2)), with **Definition 12.5.4**,
p. 594, and **Definitions 6.6.14–6.6.16**, p. 274: an example with an orientation.

## The text, paraphrased

An sc-Fredholm section `f` is orientable if the functor `Γ_f` of Theorem 6.6.13 takes the same
value on any two classes of paths with the same end points; an orientation is a map `x ↦ o_x`
carried along by `Γ_f`.  For an sc-Fredholm section functor an orientation is moreover invariant
under the morphisms (Definition 12.5.4).  An orientation `o` of `f` has a push-forward
orientation `o' = f̄_* o` of `f' = f̄_* f` for a generalized strong bundle isomorphism `f̄`
(Theorem 12.5.7 (2)).  The text gives no example.

## What is formalized

* `contDiff_of_isScSmoothMap_rn_rn`: an sc-smooth map `ℝᵐ → ℝⁿ` of M-polyfolds is `C^∞`.
* `scHomotopic_rn`: two sc-smooth paths in `ℝⁿ` with the same end points are sc-smoothly
  homotopic with end points fixed, by the straight-line homotopy
  `(τ, t) ↦ (1 − τ) γ₀(t) + τ γ₁(t)`; `PathCat.hom_eq_rn`: the path category of `ℝⁿ` has at most
  one morphism between two points.
* `isOrientableSection_of_hom_eq`, `exists_continuous_orSec_of_hom_eq`: if the path category of
  an M-polyfold has at most one morphism between two points, every sc-Fredholm section (with
  Part I's hypotheses) is orientable (Definition 6.6.14) and has an orientation
  (Definition 6.6.16), a continuous global section of `σ : O_f → X_∞` for the topology of
  Theorem 6.6.17.
* `isOrientableSection_rn`, `exists_isSectionOrientation_rn`: this for strong bundles over
  `ℝⁿ`.
* `negOrientation`: an orientation of `f = (P')^* f'` on `W = (-id)^*(ℝⁿ × ℝᵏ)`, `f'` the graph
  section of a `C^∞` map `φ : ℝⁿ → ℝᵏ`, chosen among the continuous sections of `σ`;
  `definition_12_5_4_negOrientation`: it is an orientation in the sense of Definition 12.5.4.
* `theorem_12_5_7_two_cls_oriented_witness`: Theorem 12.5.7 (2) for this orientation and the
  representative `W ←1 W →P' W'`, for all `n`, `k` (so with fibres `ℝᵏ ≠ 0` and base `ℝⁿ ≠ 0`);
  `theorem_12_5_7_two_cls_unique_oriented_witness`: the same over all representatives of the
  class.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

open scoped ContDiff

noncomputable section

namespace Polyfold

universe v

/-! ### Paths in `ℝⁿ` -/

/-- **An sc-smooth map `ℝᵐ → ℝⁿ` of M-polyfolds is `C^∞`** (finite dimensions, constant
sc-structures). -/
theorem contDiff_of_isScSmoothMap_rn_rn {m n : ℕ} {σ : (Fin m → ℝ) → Fin n → ℝ}
    (hσ : (rnPolyfold m).IsScSmoothMap (rnPolyfold n) σ) : ContDiff ℝ ∞ σ := by
  have h := hσ.smooth (rnChart m 0) (rnChart n 0) (isChart_rnChart 0) (isChart_rnChart 0) univ
    isOpen_univ (fun _ _ => ⟨mem_univ _, mem_univ _⟩) (mapsTo_univ _ _)
  have himg : rnChart m 0 '' univ = univ :=
    eq_univ_of_forall fun (r : Fin m → ℝ) => ⟨r, mem_univ _, show r - 0 = r from sub_zero r⟩
  rw [himg, rnChart_model_O] at h
  have h' : IsScSmoothRetractMap (rnSc m) univ univ (rnSc n) univ univ (fun r => σ (r + 0) - 0) :=
    h
  have hU : IsRelOpenInQuadrant (rnSc m) univ univ := rn_relOpen_univ m
  obtain ⟨-, R, hR, hs⟩ := (isScSmoothRetractMap_iff_exists hU.isScRetract).1 h'
  have hsub : R.retract ⊆ R.U := R.retract_subset
  rw [hR] at hsub
  have hRU : R.U = univ := eq_univ_of_univ_subset hsub
  have hc : ContDiffOn ℝ ∞ ((fun r => σ (r + 0) - 0) ∘ R) R.U :=
    (isScSmooth_iff_contDiffOn_const (V := Fin m → ℝ) (W := Fin n → ℝ) R.isScDomain _).1 hs
  rw [hRU] at hc
  have e : ((fun r => σ (r + 0) - 0) ∘ R) = σ := by
    funext r
    have hr : R r = r := R.apply_eq_self_of_mem_retract (by rw [hR]; exact mem_univ r)
    change σ (R r + 0) - 0 = σ r
    rw [hr, add_zero, sub_zero]
  rw [e] at hc
  exact contDiffOn_univ.1 hc

/-- **Two sc-smooth paths in `ℝⁿ` with the same end points are sc-smoothly homotopic with end
points fixed**, by the straight-line homotopy `(τ, t) ↦ (1 − τ) γ₀(t) + τ γ₁(t)`. -/
theorem scHomotopic_rn {n : ℕ} {γ₀ γ₁ : (Fin 1 → ℝ) → Fin n → ℝ}
    (h₀ : (rnPolyfold 1).IsScSmoothMap (rnPolyfold n) γ₀)
    (h₁ : (rnPolyfold 1).IsScSmoothMap (rnPolyfold n) γ₁) (hs : γ₀ (pt1 0) = γ₁ (pt1 0))
    (ht : γ₀ (pt1 1) = γ₁ (pt1 1)) : ScHomotopic (rnPolyfold n) γ₀ γ₁ := by
  have c₀ := contDiff_of_isScSmoothMap_rn_rn h₀
  have c₁ := contDiff_of_isScSmoothMap_rn_rn h₁
  have hp : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => pt1 (q 1) :=
    contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ (1 : Fin 2)
  have hq : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 0 := contDiff_apply ℝ ℝ (0 : Fin 2)
  refine ⟨fun q => (1 - q 0) • γ₀ (pt1 (q 1)) + q 0 • γ₁ (pt1 (q 1)),
    isScSmoothMap_rn_rn_of_contDiff
      (((contDiff_const.sub hq).smul (c₀.comp hp)).add (hq.smul (c₁.comp hp))), ?_, ?_, ?_, ?_⟩
  · intro t _
    simp only [pt2_apply_zero, pt2_apply_one, sub_zero, one_smul, zero_smul, add_zero]
  · intro t _
    simp only [pt2_apply_zero, pt2_apply_one, sub_self, one_smul, zero_smul, zero_add]
  · intro τ _
    simp only [pt2_apply_zero, pt2_apply_one]
    rw [← hs, ← add_smul, sub_add_cancel, one_smul]
  · intro τ _
    simp only [pt2_apply_zero, pt2_apply_one]
    rw [← ht, ← add_smul, sub_add_cancel, one_smul]

/-- **The path category of `ℝⁿ` has at most one morphism between two points.** -/
theorem PathCat.hom_eq_rn {n : ℕ} {x y : PathCat (rnPolyfold n)} (a b : x ⟶ y) : a = b := by
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  obtain ⟨ψ, rfl⟩ := PathCat.exists_eq_mk b
  exact PathCat.mk_eq_mk_iff.2 (scHomotopic_rn φ.isScSmoothMap ψ.isScSmoothMap
    (φ.source.trans ψ.source.symm) (φ.target.trans ψ.target.symm))

/-! ### Orientability of sc-Fredholm sections over `ℝⁿ` -/

section Orientable

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}
  [∀ m : ℕ, ParacompactSpace ((Fin m → ℝ) × X)]
  [∀ m : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
  [∀ k m : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin m → ℝ) × X))]
  [∀ k m : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin m → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin m → ℝ) × X) → (Fin m → ℝ) × X))]
  (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)

/-- **If any two sc-smooth paths of `X` with the same end points are sc-smoothly homotopic with
end points fixed, every sc-Fredholm section over `X` is orientable** (Definition 6.6.14,
p. 274): `Γ_f` takes the same value on equal classes. -/
theorem isOrientableSection_of_hom_eq (hP : ∀ {x y : PathCat PX} (a b : x ⟶ y), a = b) :
    IsOrientableSection hX hbump hf hsec := fun _ _ a b =>
  congrArg (fun c => orFunctorMap hX hbump hf hsec c) (hP a b)

/-- **Under the same hypothesis the map `σ : O_f → X_∞` has a continuous global section** for
the topology of Theorem 6.6.17: an orientation of `f` (Definition 6.6.16, p. 274). -/
theorem exists_continuous_orSec_of_hom_eq (hP : ∀ {x y : PathCat PX} (a b : x ⟶ y), a = b) :
    ∃ o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy,
      IsSectionOrientation f hf.toIsScFredholmSection o ∧
        @Continuous _ _ _ (orTopology (orLocalTransport hX hbump hf hsec)) (orSec o) :=
  let ⟨o, ho⟩ := (exists_isSectionOrientation_iff hX hbump hf hsec).2
    (isOrientableSection_of_hom_eq hX hbump hf hsec hP)
  ⟨o, ho, (isSectionOrientation_iff_continuous hX hbump hf hsec o).1 ho⟩

end Orientable

section Rn

variable {n : ℕ} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → (Fin n → ℝ)} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle (rnPolyfold n) P} {f : (Fin n → ℝ) → Y}
  [∀ m : ℕ, ParacompactSpace ((Fin m → ℝ) × (Fin n → ℝ))]
  [∀ m : ℕ, ParacompactSpace
    (pullbackSpace P (Prod.snd : (Fin m → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)))]
  [∀ k m : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)))]
  [∀ k m : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin m → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)))
    (Prod.snd : (Fin k → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) → (Fin m → ℝ) × (Fin n → ℝ)))]
  (hX : (rnPolyfold n).IsTame) (hbump : (rnPolyfold n).AdmitsBumpFunctions)
  (hf : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough)

/-- **Every sc-Fredholm section over `ℝⁿ` is orientable** (Definition 6.6.14, p. 274): two
classes of paths with the same end points are equal, so `Γ_f` takes the same value on them. -/
theorem isOrientableSection_rn : IsOrientableSection hX hbump hf hsec :=
  isOrientableSection_of_hom_eq hX hbump hf hsec PathCat.hom_eq_rn

/-- **Every sc-Fredholm section over `ℝⁿ` has an orientation** (Definition 6.6.16, p. 274),
and it is a continuous global section of `σ : O_f → X_∞` for the topology of Theorem 6.6.17. -/
theorem exists_isSectionOrientation_rn :
    ∃ o : ∀ y (hy : y ∈ (rnPolyfold n).smoothSet), Orx f hf.toIsScFredholmSection y hy,
      IsSectionOrientation f hf.toIsScFredholmSection o ∧
        @Continuous _ _ _ (orTopology (orLocalTransport hX hbump hf hsec)) (orSec o) :=
  exists_continuous_orSec_of_hom_eq hX hbump hf hsec PathCat.hom_eq_rn

end Rn

/-! ### The orientation of the example and Theorem 12.5.7 (2) -/

namespace StrongBundleLocalizationExamples

open SBLocalization StrongBundleEquivalenceExamples TrivialBundle EpStrongBundle

variable {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)}

/-- **`σ : O_f → X_∞` has a continuous global section for `f = (P')^* f'`** on
`W = (-id)^*(ℝⁿ × ℝᵏ)`, `f'` the graph section of a `C^∞` map. -/
theorem exists_continuous_orSec_negSection (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (negSEP n k).X.PObj
    haveI := paracompactSpace_rn_pullback (negSEP n k).B
    haveI := paracompactSpace_rn_rn_prod (negSEP n k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (negSEP n k).B
    ∃ o : ∀ a (hs : a ∈ (negSEP n k).X.PObj.smoothSet),
        Orx (negSection φ) (isScFredholmSectionFunctor_negSection (k := k) hφ).2 a hs,
      @Continuous _ _ _ (orTopology (orLocalTransport (isTame_negSEP n k)
        (admitsBumpFunctions_negSEP n k) (isScFredholmSectionTame_negSection hφ)
        (hasScPlusSectionsThrough_negSEP n k))) (orSec o) := by
  have := paracompactSpace_rn_prod (negSEP n k).X.PObj
  have := paracompactSpace_rn_pullback (negSEP n k).B
  have := paracompactSpace_rn_rn_prod (negSEP n k).X.PObj
  have := paracompactSpace_rn_rn_pullback (negSEP n k).B
  obtain ⟨o, -, ho⟩ := exists_continuous_orSec_of_hom_eq (isTame_negSEP n k)
    (admitsBumpFunctions_negSEP n k) (isScFredholmSectionTame_negSection hφ)
    (hasScPlusSectionsThrough_negSEP n k) (fun a b => PathCat.hom_eq_rn (n := n) a b)
  exact ⟨o, ho⟩

/-- **An orientation of `f = (P')^* f'`** on `W = (-id)^*(ℝⁿ × ℝᵏ)`: a continuous section of
`σ : O_f → X_∞` (`exists_continuous_orSec_negSection`; there are two, and one is chosen). -/
def negOrientation (hφ : ContDiff ℝ ∞ φ) : ∀ a (hs : a ∈ (negSEP n k).X.PObj.smoothSet),
    Orx (negSection φ) (isScFredholmSectionFunctor_negSection (k := k) hφ).2 a hs :=
  (exists_continuous_orSec_negSection hφ).choose

/-- **`negOrientation` is an orientation of `f = (P')^* f'`** in the sense of Definition 12.5.4:
continuous for Part I's topology on `O_f` and invariant under the morphisms (the ep-groupoid is
the trivial one of `ℝⁿ`, its morphisms are units, and `(1_x)_* = Id`). -/
theorem definition_12_5_4_negOrientation (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (negSEP n k).X.PObj
    haveI := paracompactSpace_rn_pullback (negSEP n k).B
    haveI := paracompactSpace_rn_rn_prod (negSEP n k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (negSEP n k).B
    (negSEP n k).E.definition_12_5_4 (isScFredholmSectionFunctor_negSection hφ)
      (hasScPlusSectionsThrough_negSEP n k)
      (orTopology (orLocalTransport (isTame_negSEP n k) (admitsBumpFunctions_negSEP n k)
        (isScFredholmSectionTame_negSection hφ) (hasScPlusSectionsThrough_negSEP n k)))
      (negOrientation hφ) :=
  ⟨(exists_continuous_orSec_negSection hφ).choose_spec, fun σ x x' hx hx' hs hs' => by
    obtain rfl : σ = x := hx
    obtain rfl : σ = x' := hx'
    exact congrFun (congrArg DFunLike.coe ((negSEP n k).E.orMor_unit
      (isScFredholmSectionFunctor_negSection hφ) (hasScPlusSectionsThrough_negSEP n k) rfl rfl
      rfl hs)) (negOrientation hφ σ hs)⟩

/-- **Theorem 12.5.7 (2) in an example with an orientation**, for the representative
`W ←1 W →P' W'`: for `W = (-id)^*(ℝⁿ × ℝᵏ)`, `W' = ℝⁿ × ℝᵏ`, `f'` the graph section of a `C^∞`
map and `f = (P')^* f'` with the orientation `o = negOrientation`, there is exactly one
orientation `o'` of `f'` corresponding to `o` over the middle `W`. -/
theorem theorem_12_5_7_two_cls_oriented_witness (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (negSEP n k).X.PObj
    haveI := paracompactSpace_rn_pullback (negSEP n k).B
    haveI := paracompactSpace_rn_rn_prod (negSEP n k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (negSEP n k).B
    haveI := paracompactSpace_rn_prod (epSEP n k).X.PObj
    haveI := paracompactSpace_rn_pullback (epSEP n k).B
    haveI := paracompactSpace_rn_rn_prod (epSEP n k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (epSEP n k).B
    ∃! o' : ∀ x (hs : x ∈ (epSEP n k).X.PObj.smoothSet),
        Orx (B := (epSEP n k).B) (graphSection φ)
          (isScFredholmSectionFunctor_graphSection hφ).2 x hs,
      (epSEP n k).E.definition_12_5_4 (isScFredholmSectionFunctor_graphSection hφ)
          (hasScPlusSectionsThrough_epSEP n k)
          (orTopology (orLocalTransport (isTame_epSEP n k) (admitsBumpFunctions_epSEP n k)
            (isScFredholmSectionTame_graphSection_epSEP hφ)
            (hasScPlusSectionsThrough_epSEP n k))) o' ∧
        ∀ v (hv : v ∈ (negDiagram n k).B.X.PObj.smoothSet),
          (sbe (GenSBMap.equivalences_Ψ_of_cls (isGeneralizedIso_negDiagram n k)
              (D := negDiagram n k) rfl)).orEqv
              ((negDiagram n k).isScFredholm_pullback (isScFredholmSectionFunctor_negSection hφ))
              (isScFredholmSectionFunctor_graphSection hφ)
              (GenSBMap.pullback_eq_of_cls' (isGeneralizedIso_negDiagram n k) rfl
                (isScFredholmSectionFunctor_negSection hφ).1 (graphSection_eq_pushforward hφ))
              ((negDiagram n k).hasScPlusSectionsThrough_B (hasScPlusSectionsThrough_negSEP n k))
              (hasScPlusSectionsThrough_epSEP n k) v hv
              (o' ((negDiagram n k).Ψ.ϕ.obj v)
                ((sbe (GenSBMap.equivalences_Ψ_of_cls (isGeneralizedIso_negDiagram n k)
                  (D := negDiagram n k) rfl)).smooth_obj hv)) =
            (negDiagram n k).hΦ.orEqv
              ((negDiagram n k).isScFredholm_pullback (isScFredholmSectionFunctor_negSection hφ))
              (isScFredholmSectionFunctor_negSection hφ) rfl
              ((negDiagram n k).hasScPlusSectionsThrough_B (hasScPlusSectionsThrough_negSEP n k))
              (hasScPlusSectionsThrough_negSEP n k) v hv
              (negOrientation hφ ((negDiagram n k).Φ.ϕ.obj v)
                ((negDiagram n k).hΦ.smooth_obj hv)) :=
  theorem_12_5_7_two_cls_witness hφ (definition_12_5_4_negOrientation hφ)

/-- **Theorem 12.5.7 (2) in an example with an orientation**, for the class
`f̄ = [W ←1 W →P' W']`: there is exactly one orientation `o'` of the graph section `f'` which
corresponds to `o = negOrientation` over the middle of every diagram representing `f̄`. -/
theorem theorem_12_5_7_two_cls_unique_oriented_witness (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (negSEP n k).X.PObj
    haveI := paracompactSpace_rn_pullback (negSEP n k).B
    haveI := paracompactSpace_rn_rn_prod (negSEP n k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (negSEP n k).B
    haveI := paracompactSpace_rn_prod (epSEP n k).X.PObj
    haveI := paracompactSpace_rn_pullback (epSEP n k).B
    haveI := paracompactSpace_rn_rn_prod (epSEP n k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (epSEP n k).B
    ∃! o' : ∀ x (hs : x ∈ (epSEP n k).X.PObj.smoothSet),
        Orx (B := (epSEP n k).B) (graphSection φ)
          (isScFredholmSectionFunctor_graphSection hφ).2 x hs,
      (epSEP n k).E.definition_12_5_4 (isScFredholmSectionFunctor_graphSection hφ)
          (hasScPlusSectionsThrough_epSEP n k)
          (orTopology (orLocalTransport (isTame_epSEP n k) (admitsBumpFunctions_epSEP n k)
            (isScFredholmSectionTame_graphSection_epSEP hφ)
            (hasScPlusSectionsThrough_epSEP n k))) o' ∧
        ∀ (D : SDiagram (negSEP n k) (epSEP n k)) (hD : D.cls = (negDiagram n k).cls) v
          (hv : v ∈ D.B.X.PObj.smoothSet),
          (sbe (GenSBMap.equivalences_Ψ_of_cls (isGeneralizedIso_negDiagram n k) hD)).orEqv
              (D.isScFredholm_pullback (isScFredholmSectionFunctor_negSection hφ))
              (isScFredholmSectionFunctor_graphSection hφ)
              (GenSBMap.pullback_eq_of_cls' (isGeneralizedIso_negDiagram n k) hD
                (isScFredholmSectionFunctor_negSection hφ).1 (graphSection_eq_pushforward hφ))
              (D.hasScPlusSectionsThrough_B (hasScPlusSectionsThrough_negSEP n k))
              (hasScPlusSectionsThrough_epSEP n k) v hv
              (o' (D.Ψ.ϕ.obj v)
                ((sbe (GenSBMap.equivalences_Ψ_of_cls (isGeneralizedIso_negDiagram n k)
                  hD)).smooth_obj hv)) =
            D.hΦ.orEqv (D.isScFredholm_pullback (isScFredholmSectionFunctor_negSection hφ))
              (isScFredholmSectionFunctor_negSection hφ) rfl
              (D.hasScPlusSectionsThrough_B (hasScPlusSectionsThrough_negSEP n k))
              (hasScPlusSectionsThrough_negSEP n k) v hv
              (negOrientation hφ (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) :=
  GenSBMap.theorem_12_5_7_two_cls_unique (isGeneralizedIso_negDiagram n k)
    (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionFunctor_graphSection hφ)
    (graphSection_eq_pushforward hφ) (hasScPlusSectionsThrough_negSEP n k)
    (hasScPlusSectionsThrough_epSEP n k) (isTame_negSEP n k) (admitsBumpFunctions_negSEP n k)
    (isScFredholmSectionTame_negSection hφ) (isTame_epSEP n k) (admitsBumpFunctions_epSEP n k)
    (isScFredholmSectionTame_graphSection_epSEP hφ) (definition_12_5_4_negOrientation hφ)

end StrongBundleLocalizationExamples

end Polyfold
