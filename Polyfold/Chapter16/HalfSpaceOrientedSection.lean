import Polyfold.Chapter16.OrientationOrbitMapIndependence
import Polyfold.Chapter6.OrientationBundle
import Polyfold.Chapter1.ExpositionLemmas

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §16.6,
**Definition 16.6.5** (p. 739; 2017: Definition 16.42), with **Definitions 6.6.14–6.6.16**
(p. 274) and **Definition 12.5.4** (p. 594): an oriented sc-Fredholm section of a strong
polyfold bundle over a polyfold with boundary.

# An oriented sc-Fredholm section over the half-space

## The text, paraphrased

(Definition 16.6.5) An sc-Fredholm section `f` of a strong polyfold bundle is orientable if a
representative `(W, F)` is orientable (Definition 12.5.4); an orientation of one representative
determines orientations of all others.  The text gives no example.

## What is formalized (namespace `Polyfold.HalfSpaceBundle`)

The bundle is `H × ℝᵏ → H` over the trivial ep-groupoid of the half-space `H = [0, ∞) × ℝᵐ`
(`halfSEP m k`), with `∂H ≠ ∅` and fibres `ℝᵏ`; `F` is the graph section of a `C^∞` map `φ`.

* `contDiff_val_of_isScSmoothMap_rn_halfSpace`, `isScSmoothMap_rn_halfSpace_of_contDiff`: a map
  `ℝⁿ → H` is sc-smooth iff it is `C^∞` as a map into `ℝ ⊕ ℝᵐ`.
* `scHomotopic_halfSpace`: two sc-smooth paths in `H` with the same end points are sc-smoothly
  homotopic with end points fixed, by `(τ, t) ↦ (1 − χ(τ)) γ₀(t) + χ(τ) γ₁(t)` with a `C^∞`
  cut-off `χ : ℝ → [0, 1]`, `χ(0) = 0`, `χ(1) = 1` (`H` is convex);
  `PathCat.hom_eq_halfSpace`: the path category of `H` has at most one morphism between two
  points.
* `halfOrientation`: an orientation of `F` (Definition 6.6.16: every sc-Fredholm section over
  `H` is orientable, Definition 6.6.14), a continuous section of `σ : O_F → H`;
  `definition_12_5_4_halfOrientation`: it is an orientation in the sense of Definition 12.5.4.
* `halfStructure`, `halfPolyfoldBundle`: the strong polyfold bundle structure `(W, id, id)` and
  its strong polyfold bundle (Definitions 16.3.1, 16.3.4); `halfGraphRep`,
  `halfFredholmSection`: the sc-Fredholm section `|x| ↦ |(x, φ(x))|` (Definition 16.6.1).
* **`halfOrientationRep`**: an orientation of this sc-Fredholm section (Definition 16.6.5), so
  `isOrientable_halfFredholmSection`.
* **`exists_unique_transport_halfSpace`**: every hypothesis of
  `OrientationRep.exists_unique_transport_of_isLRLocal` holds for it (tame, sc-smooth bump
  functions, tame germ data, the local regularity property), with `∂H ≠ ∅` and non-zero fibres
  for `k ≥ 1`; hence for every representative `b` of the section the orientation transported
  to `b` exists, is unique and does not depend on the generalized isomorphism.
* `polyfold_hypotheses_halfSpace`: the hypotheses of the polyfold-level forms
  (`OrientationRep.exists_unique_transport_of_polyfold`,
  `OrientationRep.exists_unique_transport_of_isLRLocal_polyfold`) hold for `halfOrientationRep`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open SBLocalization StrongBundle EpGroupoid

/-! ### Sc-smooth maps `ℝⁿ → H` -/

/-- **An sc-smooth map `ℝⁿ → H` is `C^∞` as a map into `ℝ ⊕ ℝᵐ`** (finite dimensions, constant
sc-structures). -/
theorem contDiff_val_of_isScSmoothMap_rn_halfSpace {n m : ℕ} {σ : (Fin n → ℝ) → H m}
    (hσ : (rnPolyfold n).IsScSmoothMap (basePoly m) σ) :
    ContDiff ℝ ∞ (fun r => ((σ r : (halfSpaceSc m) 0) : Pm m)) := by
  have h := hσ.smooth (rnChart n 0) (baseChart m) (isChart_rnChart 0)
    ((basePoly m).isChart_of_mem (mem_singleton _)) univ isOpen_univ
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩) (mapsTo_univ _ _)
  have himg : rnChart n 0 '' univ = univ :=
    eq_univ_of_forall fun (r : Fin n → ℝ) => ⟨r, mem_univ _, show r - 0 = r from sub_zero r⟩
  rw [himg] at h
  have h' : IsScSmoothRetractMap (rnSc n) univ univ (halfSpaceSc m) (H m) (H m)
      (fun r => ((σ (r + 0) : H m) : (halfSpaceSc m) 0)) := h
  have hU : IsRelOpenInQuadrant (rnSc n) univ univ := rn_relOpen_univ n
  obtain ⟨-, R, hR, hs⟩ := (isScSmoothRetractMap_iff_exists hU.isScRetract).1 h'
  have hsub : R.retract ⊆ R.U := R.retract_subset
  rw [hR] at hsub
  have hRU : R.U = univ := eq_univ_of_univ_subset hsub
  have hc : ContDiffOn ℝ ∞ ((fun r => ((σ (r + 0) : H m) : (halfSpaceSc m) 0)) ∘ R) R.U := by
    rw [contDiffOn_infty]
    intro j
    have := (hs j).contDiffOn_base R.isScDomain
    have hid : ⇑((rnSc n).toBase j) = id := funext (ScBanach.const_toBase _ j)
    rwa [ScBanach.lvlSet_const, hid, Function.comp_id] at this
  rw [hRU] at hc
  have e : ((fun r => ((σ (r + 0) : H m) : (halfSpaceSc m) 0)) ∘ R) =
      fun r => ((σ r : (halfSpaceSc m) 0) : Pm m) := by
    funext r
    have hr : R r = r := R.apply_eq_self_of_mem_retract (by rw [hR]; exact mem_univ r)
    change ((σ (R r + 0) : H m) : (halfSpaceSc m) 0) = _
    rw [hr, add_zero]
  rw [e] at hc
  exact contDiffOn_univ.1 hc

/-- **A `C^∞` map `ℝⁿ → ℝ ⊕ ℝᵐ` with values in `H` is an sc-smooth map `ℝⁿ → H`.** -/
theorem isScSmoothMap_rn_halfSpace_of_contDiff {n m : ℕ} {G : (Fin n → ℝ) → Pm m}
    (hG : ContDiff ℝ ∞ G) (hH : ∀ r, G r ∈ H m) :
    (rnPolyfold n).IsScSmoothMap (basePoly m) (fun r => (⟨G r, hH r⟩ : H m)) := by
  refine MPolyfold.isScSmoothMap_of_local fun x => ⟨rnChart n 0, baseChart m, univ,
    isChart_rnChart 0, (basePoly m).isChart_of_mem (mem_singleton _), isOpen_univ, mem_univ x,
    subset_univ _, mapsTo_univ _ _, ?_⟩
  have himg : rnChart n 0 '' univ = univ :=
    eq_univ_of_forall fun (r : Fin n → ℝ) => ⟨r, mem_univ _, show r - 0 = r from sub_zero r⟩
  rw [himg]
  change IsScSmoothRetractMap (rnSc n) univ univ (halfSpaceSc m) (H m) (H m)
    (fun r => G (r + 0))
  have hU : IsRelOpenInQuadrant (rnSc n) univ univ := rn_relOpen_univ n
  refine (isScSmoothRetractMap_iff_exists hU.isScRetract).2
    ⟨fun r _ => hH _, ScRetraction.id hU, image_id _, ?_⟩
  exact isScSmooth_of_bijective_toBase (bijective_toBase_const _) bijective_toBase_E
    hU.isScDomain (f := fun r => G (r + 0))
    (hG.comp (contDiff_id.add contDiff_const)).contDiffOn

/-! ### Paths in `H` -/

/-- **Two sc-smooth paths in `H` with the same end points are sc-smoothly homotopic with end
points fixed**: `(τ, t) ↦ (1 − χ(τ)) γ₀(t) + χ(τ) γ₁(t)` stays in the convex set `H`, for a
`C^∞` cut-off `χ` with values in `[0, 1]`, `χ(0) = 0`, `χ(1) = 1`. -/
theorem scHomotopic_halfSpace {m : ℕ} {γ₀ γ₁ : (Fin 1 → ℝ) → H m}
    (h₀ : (rnPolyfold 1).IsScSmoothMap (basePoly m) γ₀)
    (h₁ : (rnPolyfold 1).IsScSmoothMap (basePoly m) γ₁) (hs : γ₀ (pt1 0) = γ₁ (pt1 0))
    (ht : γ₀ (pt1 1) = γ₁ (pt1 1)) : ScHomotopic (basePoly m) γ₀ γ₁ := by
  have c₀ := contDiff_val_of_isScSmoothMap_rn_halfSpace h₀
  have c₁ := contDiff_val_of_isScSmoothMap_rn_halfSpace h₁
  have hp : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => pt1 (q 1) :=
    contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ (1 : Fin 2)
  have hq : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => Real.smoothTransition (q 0) :=
    Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 2))
  set G : (Fin 2 → ℝ) → Pm m := fun q =>
    (1 - Real.smoothTransition (q 0)) • ((γ₀ (pt1 (q 1)) : (halfSpaceSc m) 0) : Pm m) +
      Real.smoothTransition (q 0) • ((γ₁ (pt1 (q 1)) : (halfSpaceSc m) 0) : Pm m) with hGdef
  have hG : ContDiff ℝ ∞ G :=
    ((contDiff_const.sub hq).smul (c₀.comp hp)).add (hq.smul (c₁.comp hp))
  have hH : ∀ q, G q ∈ H m := fun q => by
    refine mem_quadrant_one_iff.2 ?_
    have a₀ : 0 ≤ ((γ₀ (pt1 (q 1)) : (halfSpaceSc m) 0) : Pm m).1 0 :=
      mem_quadrant_one_iff.1 (γ₀ (pt1 (q 1))).2
    have a₁ : 0 ≤ ((γ₁ (pt1 (q 1)) : (halfSpaceSc m) 0) : Pm m).1 0 :=
      mem_quadrant_one_iff.1 (γ₁ (pt1 (q 1))).2
    have b₀ : 0 ≤ 1 - Real.smoothTransition (q 0) :=
      sub_nonneg.2 (Real.smoothTransition.le_one _)
    have b₁ : 0 ≤ Real.smoothTransition (q 0) := Real.smoothTransition.nonneg _
    change 0 ≤ (1 - Real.smoothTransition (q 0)) *
        ((γ₀ (pt1 (q 1)) : (halfSpaceSc m) 0) : Pm m).1 0 +
      Real.smoothTransition (q 0) * ((γ₁ (pt1 (q 1)) : (halfSpaceSc m) 0) : Pm m).1 0
    exact add_nonneg (mul_nonneg b₀ a₀) (mul_nonneg b₁ a₁)
  have z0 : Real.smoothTransition 0 = 0 := Real.smoothTransition.zero_of_nonpos le_rfl
  have z1 : Real.smoothTransition 1 = 1 := Real.smoothTransition.one_of_one_le le_rfl
  refine ⟨fun q => ⟨G q, hH q⟩, isScSmoothMap_rn_halfSpace_of_contDiff hG hH, ?_, ?_, ?_, ?_⟩
  · intro t _
    refine Subtype.ext ?_
    change G (pt2 0 t) = _
    simp only [hGdef, pt2_apply_zero, pt2_apply_one, z0, sub_zero, one_smul, zero_smul, add_zero]
  · intro t _
    refine Subtype.ext ?_
    change G (pt2 1 t) = _
    simp only [hGdef, pt2_apply_zero, pt2_apply_one, z1, sub_self, one_smul, zero_smul, zero_add]
  · intro τ _
    refine Subtype.ext ?_
    change G (pt2 τ 0) = _
    simp only [hGdef, pt2_apply_zero, pt2_apply_one]
    rw [← hs, ← add_smul, sub_add_cancel, one_smul]
  · intro τ _
    refine Subtype.ext ?_
    change G (pt2 τ 1) = _
    simp only [hGdef, pt2_apply_zero, pt2_apply_one]
    rw [← ht, ← add_smul, sub_add_cancel, one_smul]

/-- **The path category of `H` has at most one morphism between two points.** -/
theorem _root_.Polyfold.PathCat.hom_eq_halfSpace {m : ℕ} {x y : PathCat (basePoly m)}
    (a b : x ⟶ y) : a = b := by
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  obtain ⟨ψ, rfl⟩ := PathCat.exists_eq_mk b
  exact PathCat.mk_eq_mk_iff.2 (scHomotopic_halfSpace φ.isScSmoothMap ψ.isScSmoothMap
    (φ.source.trans ψ.source.symm) (φ.target.trans ψ.target.symm))

/-! ### The orientation of the graph section -/

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

theorem admitsBumpFunctions_halfSEP (m k : ℕ) : (halfSEP m k).X.PObj.AdmitsBumpFunctions :=
  (admitsScPartitionsOfUnity_halfSEP m k).admitsBumpFunctions

theorem hasScPlusSectionsThrough_halfSEP (m k : ℕ) : (halfSEP m k).B.HasScPlusSectionsThrough :=
  MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough (admitsBumpFunctions_halfSEP m k)

/-- **`σ : O_F → H` has a continuous global section** for the graph section `F` of a `C^∞` map,
for the topology of Theorem 6.6.17: `F` is orientable (Definition 6.6.14) since two paths of `H`
with the same end points are homotopic, and an orientation (Definition 6.6.16) is a continuous
section. -/
theorem exists_continuous_orSec_graphSection_halfSEP (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_pullback (halfSEP m k).B
    haveI := paracompactSpace_rn_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (halfSEP m k).B
    ∃ o : ∀ a (hs : a ∈ (halfSEP m k).X.PObj.smoothSet),
        Orx (B := (halfSEP m k).B) (graphSection φ)
          (isScFredholmSectionFunctor_graphSection_halfSEP hφ).2 a hs,
      @Continuous _ _ _ (orTopology (orLocalTransport (isTame_halfSEP m k)
        (admitsBumpFunctions_halfSEP m k) (isScFredholmSectionTame_graphSection_halfSEP hφ)
        (hasScPlusSectionsThrough_halfSEP m k))) (orSec o) := by
  have := paracompactSpace_rn_prod (halfSEP m k).X.PObj
  have := paracompactSpace_rn_pullback (halfSEP m k).B
  have := paracompactSpace_rn_rn_prod (halfSEP m k).X.PObj
  have := paracompactSpace_rn_rn_pullback (halfSEP m k).B
  obtain ⟨o, ho⟩ := (exists_isSectionOrientation_iff (isTame_halfSEP m k)
    (admitsBumpFunctions_halfSEP m k) (isScFredholmSectionTame_graphSection_halfSEP hφ)
    (hasScPlusSectionsThrough_halfSEP m k)).2 fun _ _ a b =>
      congrArg (fun c => orFunctorMap (isTame_halfSEP m k) (admitsBumpFunctions_halfSEP m k)
        (isScFredholmSectionTame_graphSection_halfSEP hφ) (hasScPlusSectionsThrough_halfSEP m k)
        c) (PathCat.hom_eq_halfSpace (m := m) a b)
  exact ⟨o, (isSectionOrientation_iff_continuous (isTame_halfSEP m k)
    (admitsBumpFunctions_halfSEP m k) (isScFredholmSectionTame_graphSection_halfSEP hφ)
    (hasScPlusSectionsThrough_halfSEP m k) o).1 ho⟩

/-- **An orientation of the graph section `F` over the half-space**: a continuous section of
`σ : O_F → H` (there are two, and one is chosen). -/
def halfOrientation (hφ : ContDiff ℝ ∞ φ) : ∀ a (hs : a ∈ (halfSEP m k).X.PObj.smoothSet),
    Orx (B := (halfSEP m k).B) (graphSection φ)
      (isScFredholmSectionFunctor_graphSection_halfSEP hφ).2 a hs :=
  (exists_continuous_orSec_graphSection_halfSEP hφ).choose

/-- **`halfOrientation` is an orientation in the sense of Definition 12.5.4**: continuous for
Part I's topology on `O_F` and invariant under the morphisms (the ep-groupoid is the trivial one
of `H`, its morphisms are units, and `(1_x)_* = Id`). -/
theorem definition_12_5_4_halfOrientation (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_pullback (halfSEP m k).B
    haveI := paracompactSpace_rn_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (halfSEP m k).B
    (halfSEP m k).E.definition_12_5_4 (isScFredholmSectionFunctor_graphSection_halfSEP hφ)
      (hasScPlusSectionsThrough_halfSEP m k)
      (orTopology (orLocalTransport (isTame_halfSEP m k) (admitsBumpFunctions_halfSEP m k)
        (isScFredholmSectionTame_graphSection_halfSEP hφ)
        (hasScPlusSectionsThrough_halfSEP m k)))
      (halfOrientation hφ) :=
  ⟨(exists_continuous_orSec_graphSection_halfSEP hφ).choose_spec,
    fun σ x x' hx hx' hs hs' => by
      obtain rfl : σ = x := hx
      obtain rfl : σ = x' := hx'
      exact congrFun (congrArg DFunLike.coe ((halfSEP m k).E.orMor_unit
        (isScFredholmSectionFunctor_graphSection_halfSEP hφ)
        (hasScPlusSectionsThrough_halfSEP m k) rfl rfl rfl hs)) (halfOrientation hφ σ hs)⟩

/-- Part I's topology on `O_F` is a topology with the properties of Theorem 12.5.3. -/
theorem isOrientationTopology_graphSection_halfSEP (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_pullback (halfSEP m k).B
    haveI := paracompactSpace_rn_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (halfSEP m k).B
    IsOrientationTopology (B := (halfSEP m k).B) (graphSection φ)
      (isScFredholmSectionFunctor_graphSection_halfSEP hφ).2
      (orTopology (orLocalTransport (isTame_halfSEP m k) (admitsBumpFunctions_halfSEP m k)
        (isScFredholmSectionTame_graphSection_halfSEP hφ)
        (hasScPlusSectionsThrough_halfSEP m k))) := by
  have := paracompactSpace_rn_prod (halfSEP m k).X.PObj
  have := paracompactSpace_rn_pullback (halfSEP m k).B
  have := paracompactSpace_rn_rn_prod (halfSEP m k).X.PObj
  have := paracompactSpace_rn_rn_pullback (halfSEP m k).B
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 (isTame_halfSEP m k) (admitsBumpFunctions_halfSEP m k)
    (isScFredholmSectionTame_graphSection_halfSEP hφ)).exists
  exact eq_orTopology_of (isTame_halfSEP m k) (admitsBumpFunctions_halfSEP m k)
    (isScFredholmSectionTame_graphSection_halfSEP hφ) (hasScPlusSectionsThrough_halfSEP m k)
    ht₀.isLocalHomeomorph ht₀.propagation ▸ ht₀

/-! ### The strong polyfold bundle and the oriented sc-Fredholm section -/

variable (m k) in
/-- **The strong polyfold bundle structure `((P : W → X, μ), id, id)`** for
`|P| : |H × ℝᵏ| → |H|` over the trivial ep-groupoid of the half-space (Definition 16.3.1). -/
def halfStructure : StrongPolyfoldBundleStructure (halfSEP m k).E.projFunctor.orbitMap where
  A := halfSEP m k
  isZhou := isZhou_trivial _
  paracompact := hasParacompactOrbitSpace_halfSEP m k
  isLR := EpStrongBundle.isLR_trivial _
  Γ := Homeomorph.refl _
  γ := Homeomorph.refl _
  comm := rfl

variable (m k) in
/-- The strong polyfold bundle of `halfStructure` (Definition 16.3.4). -/
def halfPolyfoldBundle : StrongPolyfoldBundle (halfSEP m k).E.projFunctor.orbitMap :=
  ⟦halfStructure m k⟧

theorem injective_π_halfSEP (m k : ℕ) : Function.Injective (halfSEP m k).X.π := fun a b h => by
  obtain ⟨σ, h1, h2⟩ := (halfSEP m k).X.π_eq_π_iff.1 h
  exact h1.symm.trans h2

open StrongPolyfoldBundle in
/-- **The representative `(halfStructure, graph φ)`** of the section `|x| ↦ |(x, φ(x))|`
(Definition 16.3.18). -/
def halfGraphRep (hφ : ContDiff ℝ ∞ φ) : SectionRep (halfPolyfoldBundle m k) where
  S := halfStructure m k
  hS := rfl
  F := graphSection φ
  hF := (isScFredholmSectionFunctor_graphSection_halfSEP hφ).1
  f := Quotient.lift
    (fun x : (halfSEP m k).Obj => (halfSEP m k).E.toEpGroupoid.π (graphSection φ x))
    fun x y h => by
      have e : x = y := injective_π_halfSEP m k (Quotient.sound h)
      rw [e]
  continuous_f := Continuous.quotient_lift ((halfSEP m k).E.toEpGroupoid.continuous_π.comp
    (continuous_id.prodMk (hφ.continuous.comp continuous_subtype_val))) _
  isSection z := Quotient.inductionOn z fun _ => rfl
  comm _ := rfl

open StrongPolyfoldBundle in
/-- **The sc-Fredholm section `|x| ↦ |(x, φ(x))|`** of the strong polyfold bundle over the
half-space (Definition 16.6.1). -/
def halfFredholmSection (hφ : ContDiff ℝ ∞ φ) : FredholmSection (halfPolyfoldBundle m k) :=
  ⟨⟦halfGraphRep hφ⟧, halfGraphRep hφ, rfl, isScFredholmSectionFunctor_graphSection_halfSEP hφ⟩

open StrongPolyfoldBundle in
/-- **An orientation of the sc-Fredholm section over the half-space** (Definition 16.6.5): the
representative `(halfStructure, graph φ)` with Part I's topology on `O_F` and the orientation
`halfOrientation`. -/
def halfOrientationRep (hφ : ContDiff ℝ ∞ φ) : OrientationRep (halfFredholmSection hφ) where
  a := halfGraphRep hφ
  ha := rfl
  hF := isScFredholmSectionFunctor_graphSection_halfSEP hφ
  hsec := hasScPlusSectionsThrough_halfSEP m k
  t := haveI := paracompactSpace_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_pullback (halfSEP m k).B
    haveI := paracompactSpace_rn_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (halfSEP m k).B
    orTopology (orLocalTransport (isTame_halfSEP m k) (admitsBumpFunctions_halfSEP m k)
      (isScFredholmSectionTame_graphSection_halfSEP hφ) (hasScPlusSectionsThrough_halfSEP m k))
  isOrientationTopology := isOrientationTopology_graphSection_halfSEP hφ
  o := halfOrientation hφ
  isOrientation := definition_12_5_4_halfOrientation hφ

open StrongPolyfoldBundle in
/-- **The sc-Fredholm section over the half-space is orientable** (Definition 16.6.5). -/
theorem isOrientable_halfFredholmSection (hφ : ContDiff ℝ ∞ φ) :
    (halfFredholmSection (m := m) (k := k) hφ).IsOrientable :=
  ⟨halfOrientationRep hφ⟩

open StrongPolyfoldBundle in
/-- **Definition 16.6.5 in an example with boundary and non-zero fibres**: for the oriented
sc-Fredholm section `|x| ↦ |(x, φ(x))|` over the half-space `H = [0, ∞) × ℝᵐ` (`∂H ≠ ∅`, fibres
`ℝᵏ`, `k ≥ 1`), the hypotheses of `OrientationRep.exists_unique_transport_of_isLRLocal` hold
(tame, sc-smooth bump functions, tame germ data, the local regularity property), and so for
every representative `b` of the section exactly one orientation of `F_b` corresponds to the
orientation over every diagram of every generalized strong bundle isomorphism `𝔄` with
`Γ_b ∘ |𝔄| = Γ` and `𝔄_* F = F_b`. -/
theorem exists_unique_transport_halfSpace [NeZero k] (hφ : ContDiff ℝ ∞ φ) :
    (halfSEP m k).X.PObj.boundary.Nonempty ∧
    (∀ y : (halfSEP m k).Obj, Nontrivial ((halfSEP m k).P ⁻¹' {y})) ∧
    (halfSEP m k).X.PObj.IsTame ∧ (halfSEP m k).X.PObj.AdmitsBumpFunctions ∧
    (halfSEP m k).B.IsScFredholmSectionTame (graphSection φ) ∧ (halfSEP m k).E.IsLRLocal ∧
    ∀ (b : SectionRep (halfPolyfoldBundle m k)) (_ : ⟦b⟧ = (halfFredholmSection hφ).1),
      ∃ (hFb : b.S.A.E.IsScFredholmSectionFunctor b.F)
        (hsec' : b.S.A.B.HasScPlusSectionsThrough),
        ∃! o' : ∀ x (hs : x ∈ b.S.A.X.PObj.smoothSet), Orx b.F hFb.2 x hs,
          (∀ t' : TopologicalSpace (OrSpace b.F hFb.2),
            (haveI := paracompactSpace_rn_prod b.S.A.X.PObj
             haveI := paracompactSpace_rn_pullback b.S.A.B
             IsOrientationTopology b.F hFb.2 t') →
              b.S.A.E.definition_12_5_4 hFb hsec' t' o') ∧
          ∀ (𝔄 : GenSBMap (halfOrientationRep hφ).a.S.A b.S.A) (h𝔄 : 𝔄.IsGeneralizedIso)
            (_ : ⇑b.S.Γ ∘ 𝔄.orbitMap = ⇑(halfOrientationRep hφ).a.S.Γ)
            (hpush : b.F = GenSBMap.pushforward h𝔄 (halfOrientationRep hφ).a.F)
            (D : SDiagram (halfOrientationRep hφ).a.S.A b.S.A) (hD : D.cls = 𝔄) v
            (hv : v ∈ D.B.X.PObj.smoothSet),
            (sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).orEqv
                (D.isScFredholm_pullback (halfOrientationRep hφ).hF) hFb
                (GenSBMap.pullback_eq_of_cls' h𝔄 hD (halfOrientationRep hφ).hF.1 hpush)
                (D.hasScPlusSectionsThrough_B (halfOrientationRep hφ).hsec) hsec' v hv
                (o' (D.Ψ.ϕ.obj v)
                  ((sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).smooth_obj hv)) =
              D.hΦ.orEqv (D.isScFredholm_pullback (halfOrientationRep hφ).hF)
                (halfOrientationRep hφ).hF rfl
                (D.hasScPlusSectionsThrough_B (halfOrientationRep hφ).hsec)
                (halfOrientationRep hφ).hsec v hv
                ((halfOrientationRep hφ).o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) :=
  ⟨⟨_, zero_mem_boundary_halfSEP m k⟩, nontrivial_fibre_halfSEP m k, isTame_halfSEP m k,
    admitsBumpFunctions_halfSEP m k, isScFredholmSectionTame_graphSection_halfSEP hφ,
    isLRLocal_halfSEP m k, fun b hb =>
      (halfOrientationRep hφ).exists_unique_transport_of_isLRLocal b hb (isTame_halfSEP m k)
        (admitsBumpFunctions_halfSEP m k) (isScFredholmSectionTame_graphSection_halfSEP hφ)
        (isLRLocal_halfSEP m k)⟩

/-- **The hypotheses of the polyfold-level forms of Definition 16.6.5 hold over the
half-space**: the strong polyfold bundle is tame (Definition 16.3.5 (1)), its polyfold admits
sc-smooth bump functions (Definition 16.1.5 (1)) and is effective, the oriented representative
has tame germ data and the local regularity property, `∂H ≠ ∅` and the fibres are non-zero.
These are the hypotheses of `OrientationRep.exists_unique_transport_of_polyfold` and of
`OrientationRep.exists_unique_transport_of_isLRLocal_polyfold` for `halfOrientationRep`. -/
theorem polyfold_hypotheses_halfSpace [NeZero k] (hφ : ContDiff ℝ ∞ φ) :
    (halfPolyfoldBundle m k).IsTame ∧ (halfPolyfoldBundle m k).polyfold.AdmitsBumpFunctions ∧
    (halfPolyfoldBundle m k).polyfold.IsEffective ∧
    (halfOrientationRep hφ).a.S.A.B.IsScFredholmSectionTame (halfOrientationRep hφ).a.F ∧
    (halfOrientationRep hφ).a.S.A.E.IsLRLocal ∧
    (halfOrientationRep hφ).a.S.A.X.PObj.boundary.Nonempty ∧
    ∀ y : (halfOrientationRep hφ).a.S.A.Obj,
      Nontrivial ((halfOrientationRep hφ).a.S.A.P ⁻¹' {y}) :=
  ⟨⟨(halfStructure m k).toPolyfoldStructure, rfl, isTame_halfSEP m k⟩,
    ⟨(halfStructure m k).toPolyfoldStructure, rfl, admitsBumpFunctions_halfSEP m k⟩,
    ⟨(halfStructure m k).toPolyfoldStructure, rfl, EpGroupoid.isEffective_trivial _⟩,
    isScFredholmSectionTame_graphSection_halfSEP hφ, isLRLocal_halfSEP m k,
    ⟨_, zero_mem_boundary_halfSEP m k⟩, nontrivial_fibre_halfSEP m k⟩

end HalfSpaceBundle

end Polyfold
