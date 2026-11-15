import Polyfold.Chapter16.IndexZeroTwoModels
import Polyfold.Chapter10.StrongBundleLocalizationExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
**Theorem 16.6.6** (p. 739) for Fredholm index `0`, the independence of the count from the model,
with two different strong polyfold bundle structures (Definitions 16.3.1, 16.3.3) on one section
(Definition 16.3.18).  Numbers and pages are the 2021 text's.

# One section, two structures

## The statement checked

`StrongPolyfoldBundle.count_eq_of_mk_eq` says: if regular perturbations of dimension `0` in the
models of two representatives `a`, `b` give the same oriented branched suborbifold of `Z`, the
weighted counts of every `0`-form agree.  Here its hypothesis is met by two representatives of
the **same** sc-smooth section (`⟦a⟧ = ⟦b⟧`) on two **different** strong polyfold bundle
structures (`a.S ≠ b.S`), with non-zero fibres and a non-empty perturbed solution set.

## The example

`W = ℝ × ℝ → ℝ` over the trivial ep-groupoid of `ℝ` (`epSEP 1 1`).

* `TrivialBundle.isStrongBundleMap_prodLinMap`: for a `C^∞` map `g : ℝⁿ → ℝⁿ'` and a linear map
  `L : ℝᵏ → ℝᵏ'`, `(x, v) ↦ (g(x), L v)` is a strong bundle map of the trivial bundles covering
  `g` (sc-smooth on `W[0]` and on `W[1]`, read in the translation charts centred at `0`).
* The fibre negation `N(x, v) = (x, −v)` (`fibNeg`) covers `1_X`, is compatible with `μ`
  (`isMap_fibNeg`), and is its own inverse, so it is a strong bundle equivalence
  (`fibNegHom_mem_equivalences`); `[W ←1 W →N W]` is a generalized strong bundle isomorphism
  (`isGeneralizedIso_fibNegGen`) whose orbit map `|N|` is an involutive homeomorphism of `|W|`
  (`fibNegHomeo`).
* `negStructure = ((P, μ), Γ' = |N|, γ = id)`; `equiv_negStructure_epStructure`: it is
  equivalent to `epStructure = ((P, μ), id, id)` through `[N]` (`Γ ∘ |[N]| = Γ'`), and
  `epStructure_ne_negStructure`: the two structures differ (`Γ ≠ Γ'` at `|(0, 1)|`).
* `negGraphRep`: the representative `(negStructure, F'(x) = (x, −x))` of the section
  `|x| ↦ |(x, x)|`, whose other representative is `graphRep id = (epStructure, F(x) = (x, x))`
  (`mk_graphRep_id_eq_mk_negGraphRep`).
* `pointOrientedRep_graphRep_id_eq_negGraphRep`: with the zero multisection `Λ₀` in both models
  and the orientation `+` of the point `0`, the oriented branched suborbifold representatives
  `((Λ₀ ∘ F, +), (X, γ))` and `((Λ₀ ∘ F', +), (X, γ))` are equal.
* **`StrongPolyfoldBundle.count_eq_of_mk_eq_two_structures`**: the witness, with the conclusion
  of `count_eq_of_mk_eq`.

The base is `ℝ`, so `∂X = ∅`; `count_eq_of_mk_eq` does not involve the boundary.  The isotropy
is trivial, and the two structures share the strong bundle `(P, μ)` and differ in `Γ`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter CategoryTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace TrivialBundle

open StrongBundle

variable {n n' k k' : ℕ}

/-- The map `(x, v) ↦ (g(x), L v)` of trivial bundles. -/
def prodLinMap (g : (Fin n → ℝ) → (Fin n' → ℝ)) (L : (Fin k → ℝ) →L[ℝ] (Fin k' → ℝ))
    (w : (Fin n → ℝ) × (Fin k → ℝ)) : (Fin n' → ℝ) × (Fin k' → ℝ) :=
  (g w.1, L w.2)

/-- `(x, v) ↦ (g(x), L v)` is sc-smooth `W[0] → W'[0]`: in the charts centred at `0` it is the
`C^∞` map `(u, v) ↦ (g(u), L v)`. -/
theorem isScSmoothMap_zero_prodLinMap {g : (Fin n → ℝ) → (Fin n' → ℝ)} (hg : ContDiff ℝ ∞ g)
    (L : (Fin k → ℝ) →L[ℝ] (Fin k' → ℝ)) :
    (bundle n k).toMPolyfold0.IsScSmoothMap (bundle n' k').toMPolyfold0 (prodLinMap g L) := by
  refine MPolyfold.isScSmoothMap_of_local fun w => ⟨(chart 0).toMChart continuous_fst,
    (chart 0).toMChart continuous_fst, univ, (bundle n k).isChart_toMChart (mem_range_self 0),
    (bundle n' k').isChart_toMChart (mem_range_self 0), isOpen_univ, mem_univ w,
    fun _ _ => mem_univ _, fun _ _ => mem_univ _, ?_⟩
  have himg : ((chart (k := k) (0 : Fin n → ℝ)).toMChart continuous_fst) '' univ = univ :=
    image_univ_of_surjective (Equiv.surjective _)
  rw [himg]
  refine (isScSmoothRetractMap_of_bijective_toBase bijective_toBase_model bijective_toBase_model
    relOpen_model ?_
    (g := fun p : (Fin n → ℝ) × (Fin k → ℝ) => (g (p.1 + 0) - 0, L p.2))
    (((hg.comp (contDiff_fst.add contDiff_const)).sub contDiff_const).prodMk
      (L.contDiff.comp contDiff_snd))).congr fun p _ => ?_
  · exact fun u _ => ⟨_, ⟨mem_univ _, mem_univ _⟩, rfl⟩
  · rfl

/-- `(x, v) ↦ (g(x), L v)` maps `W_{0,1}` into `W'_{0,1}` (every point lies in `W_{0,1}`). -/
theorem mapsTo_oneSet_prodLinMap (g : (Fin n → ℝ) → (Fin n' → ℝ))
    (L : (Fin k → ℝ) →L[ℝ] (Fin k' → ℝ)) :
    MapsTo (prodLinMap g L) (bundle n k).oneSet (bundle n' k').oneSet := by
  rintro y - _ ⟨a, rfl⟩ -
  exact (bijective_toBase_const _ 1).2 _

/-- `(x, v) ↦ (g(x), L v)` is sc-smooth `W[1] → W'[1]`: in the charts `Φ[1]` centred at `0` it
is again `(u, v) ↦ (g(u), L v)`. -/
theorem isScSmoothMap_one_prodLinMap {g : (Fin n → ℝ) → (Fin n' → ℝ)} (hg : ContDiff ℝ ∞ g)
    (L : (Fin k → ℝ) →L[ℝ] (Fin k' → ℝ)) :
    (bundle n k).toMPolyfold1.IsScSmoothMap (bundle n' k').toMPolyfold1
      (oneRestrict (bundle n k) (bundle n' k') (prodLinMap g L)
        (mapsTo_oneSet_prodLinMap g L)) := by
  refine MPolyfold.isScSmoothMap_of_local fun y => ⟨oneChart (mem_range_self 0) y,
    oneChart (mem_range_self 0) (oneRestrict (bundle n k) (bundle n' k') (prodLinMap g L)
        (mapsTo_oneSet_prodLinMap g L) y), univ,
    (bundle n k).isChart_oneChart (mem_range_self 0) y,
    (bundle n' k').isChart_oneChart (mem_range_self 0) _, isOpen_univ, mem_univ y,
    fun _ _ => mem_univ _, fun _ _ => mem_univ _, ?_⟩
  have hK : ∀ (m j : ℕ) (z : ((rnSc m).prod (rnSc j).shift) 0),
      z ∈ strongShiftOne (chart (k := j) (0 : Fin m → ℝ)).K :=
    fun m j z => ⟨_, ⟨mem_univ _, mem_univ _⟩, rfl⟩
  have himg : (oneChart (mem_range_self 0) y) '' univ = univ :=
    eq_univ_of_forall fun z => ⟨(oneChart (mem_range_self 0) y).symm z, mem_univ _,
      (oneChart (mem_range_self 0) y).toPartialEquiv.right_inv (hK n k z)⟩
  rw [himg]
  have hb : ∀ (m j : ℕ) (i : ℕ), Bijective (((rnSc m).prod (rnSc j).shift).toBase i) :=
    fun m j => bijective_toBase_prod (bijective_toBase_const _)
      (bijective_toBase_shift (bijective_toBase_const _))
  refine (isScSmoothRetractMap_of_bijective_toBase (hb n k) (hb n' k')
    relOpen_model (fun u _ => hK n' k' _)
    (g := fun p : (Fin n → ℝ) × (Fin k → ℝ) => (g (p.1 + 0) - 0, L p.2))
    (((hg.comp (contDiff_fst.add contDiff_const)).sub contDiff_const).prodMk
      (L.contDiff.comp contDiff_snd))).congr fun p _ => ?_
  have e : ∀ v : Fin k' → ℝ, invFun ((rnSc k').toBase 1) v = v := fun v => by
    conv_lhs => rw [← ScBanach.const_toBase (Fin k' → ℝ) 1 v]
    exact leftInverse_invFun ((rnSc k').toBase_injective 1) v
  have hc0 : chart (k := k) (0 : Fin n → ℝ) ∈ (bundle n k).atlas.charts := mem_range_self 0
  have hp := oneChart_symm_apply (B := bundle n k) hc0 y (hK n k p)
  change _ = (chart 0).liftOne (prodLinMap g L ((bundle n k).oneVal
    ((oneChart hc0 y).symm p)))
  rw [hp]
  unfold StrongBundleChart.liftOne
  refine Prod.ext rfl ?_
  change L p.2 = invFun ((rnSc k').toBase 1) (L ((rnSc k).toBase 1 p.2))
  rw [e, ScBanach.const_toBase]

/-- **`(x, v) ↦ (g(x), L v)` is a strong bundle map** of the trivial bundles covering `g`, for a
`C^∞` map `g` and a linear map `L` (sc-smooth at the levels `[0]` and `[1]`, read in the
translation charts centred at `0`). -/
theorem isStrongBundleMap_prodLinMap {g : (Fin n → ℝ) → (Fin n' → ℝ)} (hg : ContDiff ℝ ∞ g)
    (L : (Fin k → ℝ) →L[ℝ] (Fin k' → ℝ)) :
    (bundle n k).IsStrongBundleMap (bundle n' k') g (prodLinMap g L) where
  covers _ := rfl
  fiber_linear x := by
    let e := (fibEquiv (n := n) (k := k) x).linearEquiv ℝ
    let e' := (fibEquiv (n := n') (k := k') (g x)).linearEquiv ℝ
    have h : fiberRestrict (proj n k) (proj n' k') g (prodLinMap g L) (fun _ => rfl) x =
        e'.symm.toLinearMap.comp (L.toLinearMap.comp e.toLinearMap) := by
      funext v
      apply Subtype.ext
      change (g (v : (Fin n → ℝ) × (Fin k → ℝ)).1, L (v : (Fin n → ℝ) × (Fin k → ℝ)).2) =
        (g x, L (v : (Fin n → ℝ) × (Fin k → ℝ)).2)
      rw [show (v : (Fin n → ℝ) × (Fin k → ℝ)).1 = x from v.2]
    rw [h]; exact LinearMap.isLinear _
  isScSmoothMap := isScSmoothMap_zero_prodLinMap hg L
  mapsTo_oneSet := mapsTo_oneSet_prodLinMap g L
  isScSmoothMap_one := isScSmoothMap_one_prodLinMap hg L

variable (n k) in
/-- **The fibre negation** `N(x, v) = (x, −v)` of `ℝⁿ × ℝᵏ → ℝⁿ`. -/
def fibNeg : (Fin n → ℝ) × (Fin k → ℝ) → (Fin n → ℝ) × (Fin k → ℝ) :=
  prodLinMap _root_.id (-ContinuousLinearMap.id ℝ (Fin k → ℝ))

@[simp] theorem fibNeg_apply (w : (Fin n → ℝ) × (Fin k → ℝ)) : fibNeg n k w = (w.1, -w.2) := rfl

/-- `N ∘ N = 1`. -/
theorem fibNeg_fibNeg (w : (Fin n → ℝ) × (Fin k → ℝ)) : fibNeg n k (fibNeg n k w) = w :=
  Prod.ext rfl (neg_neg w.2)

variable (n k) in
/-- `N` is a strong bundle map covering the identity, compatible with `μ` (Definition 8.3.2). -/
theorem isMap_fibNeg :
    (epBundle n k).IsMap (epBundle n k) (EpFunctor.id _) (fibNeg n k) where
  isStrongBundleMap := isStrongBundleMap_prodLinMap contDiff_id _
  map_μ _ _ _ := rfl

end TrivialBundle

namespace StrongBundleEquivalenceExamples

open TrivialBundle SBLocalization

variable (n k : ℕ)

/-- The fibre negation as a morphism of `SEP` (a strong bundle functor covering `1_X`). -/
def fibNegHom : epSEP n k ⟶ epSEP n k :=
  ⟨EpFunctor.id _, (isMap_fibNeg n k).liftFunctor,
    (isMap_fibNeg n k).isStrongBundleFunctor_liftFunctor⟩

/-- **`N` is a strong bundle equivalence** (Definition 10.4.1): it is its own inverse. -/
theorem fibNegHom_mem_equivalences : SEP.equivalences (fibNegHom n k) :=
  EpStrongBundle.isStrongBundleEquivalence_of_inverse (isMap_fibNeg n k) (isMap_fibNeg n k)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) fibNeg_fibNeg fibNeg_fibNeg

/-- The generalized strong bundle isomorphism `[W ←1 W →N W]` (Definition 10.5.2). -/
def fibNegGen : GenSBMap (epSEP n k) (epSEP n k) := (SDiagram.ofHom (fibNegHom n k)).cls

/-- `[N]` is a generalized strong bundle isomorphism. -/
theorem isGeneralizedIso_fibNegGen : (fibNegGen n k).IsGeneralizedIso :=
  GenSBMap.isGeneralizedIso_ofHom (fibNegHom_mem_equivalences n k)

/-- `|[N]|(|w|) = |N(w)|`. -/
theorem orbitMap_fibNegGen_π (w : (epSEP n k).W) :
    (fibNegGen n k).orbitMap ((epSEP n k).E.toEpGroupoid.π w) =
      (epSEP n k).E.toEpGroupoid.π (fibNeg n k w) := by
  rw [fibNegGen, GenSBMap.orbitMap_cls, SDiagram.orbitMap_ofHom]
  rfl

/-- `|N| ∘ |N| = 1`. -/
theorem orbitMap_fibNegGen_involutive (q : (epSEP n k).E.toEpGroupoid.OrbitSpace) :
    (fibNegGen n k).orbitMap ((fibNegGen n k).orbitMap q) = q :=
  Quotient.inductionOn q fun w => by
    change (fibNegGen n k).orbitMap ((fibNegGen n k).orbitMap
      ((epSEP n k).E.toEpGroupoid.π w)) = (epSEP n k).E.toEpGroupoid.π w
    rw [orbitMap_fibNegGen_π]
    exact (orbitMap_fibNegGen_π n k (fibNeg n k w)).trans
      (congrArg (epSEP n k).E.toEpGroupoid.π (fibNeg_fibNeg w))

/-- **The homeomorphism `|N| : |W| → |W|`** (an involution). -/
def fibNegHomeo : (epSEP n k).E.toEpGroupoid.OrbitSpace ≃ₜ (epSEP n k).E.toEpGroupoid.OrbitSpace
    where
  toFun := (fibNegGen n k).orbitMap
  invFun := (fibNegGen n k).orbitMap
  left_inv := orbitMap_fibNegGen_involutive n k
  right_inv := orbitMap_fibNegGen_involutive n k
  continuous_toFun := (fibNegGen n k).continuous_orbitMap
  continuous_invFun := (fibNegGen n k).continuous_orbitMap

end StrongBundleEquivalenceExamples

namespace TrivialBundle

open StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples SBLocalization EpGroupoid

/-- **The second strong polyfold bundle structure `((P, μ), |N|, id)`** for
`|P| : |ℝ × ℝ| → |ℝ|`: the same strong bundle as `epStructure`, with `Γ' = |N|`. -/
def negStructure : StrongPolyfoldBundleStructure (epSEP 1 1).E.projFunctor.orbitMap where
  A := epSEP 1 1
  isZhou := isZhou_trivial _
  paracompact := hasParacompactOrbitSpace_trivial _
  isLRLocal := EpStrongBundle.isLRLocal_trivial _
  Γ := fibNegHomeo 1 1
  γ := Homeomorph.refl _
  comm := funext fun q => Quotient.inductionOn q fun w => by
    change (epSEP 1 1).E.projFunctor.orbitMap
      ((fibNegGen 1 1).orbitMap ((epSEP 1 1).E.toEpGroupoid.π w)) = _
    rw [orbitMap_fibNegGen_π]
    rfl

/-- **`negStructure ∼ epStructure`** (Definition 16.3.3): through `[W ←1 W →N W]`,
`Γ ∘ |[N]| = |N| = Γ'`. -/
theorem equiv_negStructure_epStructure : Equiv negStructure epStructure :=
  equiv_iff_exists_Γ.2 ⟨fibNegGen 1 1, isGeneralizedIso_fibNegGen 1 1, rfl⟩

/-- `negStructure` lies in the class `epPolyfoldBundle` (Definition 16.3.4). -/
theorem mk_negStructure : (⟦negStructure⟧ : StrongPolyfoldBundle _) = epPolyfoldBundle :=
  Quotient.sound equiv_negStructure_epStructure

/-- The point `(0, 1)` of `ℝ × ℝ`. -/
def pointZeroOne : (epSEP 1 1).W := ((0 : Fin 1 → ℝ), fun _ => (1 : ℝ))

/-- **The two structures differ**: `Γ = id` and `Γ' = |N|` differ at `|(0, 1)|`. -/
theorem epStructure_ne_negStructure : epStructure ≠ negStructure := by
  intro h
  have hΓ : HEq epStructure.Γ negStructure.Γ := by rw [h]
  have hΓ' : (Homeomorph.refl _ : (epSEP 1 1).E.toEpGroupoid.OrbitSpace ≃ₜ _) =
      fibNegHomeo 1 1 := eq_of_heq hΓ
  have h1 := congrArg (fun Γ : (epSEP 1 1).E.toEpGroupoid.OrbitSpace ≃ₜ _ =>
    Γ ((epSEP 1 1).E.toEpGroupoid.π pointZeroOne)) hΓ'
  change (epSEP 1 1).E.toEpGroupoid.π pointZeroOne =
    (fibNegGen 1 1).orbitMap ((epSEP 1 1).E.toEpGroupoid.π pointZeroOne) at h1
  rw [orbitMap_fibNegGen_π] at h1
  obtain ⟨q, hq1, hq2⟩ := (GroupoidStr.π_eq_π_iff _).1 h1
  have e := congrArg (fun w : (epSEP 1 1).W => (w : (Fin 1 → ℝ) × (Fin 1 → ℝ)).2 0)
    (hq1.symm.trans hq2)
  norm_num [pointZeroOne] at e

/-- `F' = N ∘ F`: the section functor `x ↦ (x, −x)` of `b` is the push-forward of `x ↦ (x, x)`
along the fibre negation. -/
theorem antidiagSection_eq_fibNeg_diagSection (x : (epSEP 1 1).Obj) :
    antidiagSection x = fibNeg 1 1 (diagSection x) := rfl

open StrongPolyfoldBundle in
/-- **The representative `(negStructure, F')`** of the section `|x| ↦ |(x, x)|`, with
`F'(x) = (x, −x)`: `Γ'(|F'(x)|) = |N(x, −x)| = |(x, x)|`. -/
def negGraphRep : SectionRep epPolyfoldBundle where
  S := negStructure
  hS := mk_negStructure
  F := antidiagSection
  hF := isScFredholmSectionFunctor_antidiagSection.1
  f := (graphRep _root_.id contDiff_id).f
  continuous_f := (graphRep _root_.id contDiff_id).continuous_f
  isSection := (graphRep _root_.id contDiff_id).isSection
  comm x := by
    change (epSEP 1 1).E.toEpGroupoid.π (graphSection _root_.id x) =
      (fibNegGen 1 1).orbitMap ((epSEP 1 1).E.toEpGroupoid.π (antidiagSection x))
    rw [orbitMap_fibNegGen_π]
    exact congrArg (epSEP 1 1).E.toEpGroupoid.π (Prod.ext rfl (neg_neg _).symm)

end TrivialBundle

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization TrivialBundle
open StrongBundleEquivalenceExamples EpGroupoid

/-- The representatives `graphRep id` (on `epStructure`, `F(x) = (x, x)`) and `negGraphRep`
(on `negStructure`, `F'(x) = (x, −x)`) represent the same sc-smooth section
(Definition 16.3.18). -/
theorem mk_graphRep_id_eq_mk_negGraphRep :
    (⟦graphRep _root_.id contDiff_id⟧ : ScSection epPolyfoldBundle) = ⟦negGraphRep⟧ :=
  Quotient.sound (SectionRep.rel_of_f_eq _ _ rfl)

/-- **The oriented branched suborbifold representatives agree literally**:
`((Λ₀ ∘ F, +), (X, γ)) = ((Λ₀ ∘ F', +), (X, γ))`, since `Λ₀ ∘ F = Λ₀ ∘ F' = 1_{0}` and the
underlying polyfold structures `(X, γ)` of the two structures coincide. -/
theorem pointOrientedRep_graphRep_id_eq_negGraphRep :
    pointOrientedRep (graphRep _root_.id contDiff_id) diagPointPerturbation =
      pointOrientedRep negGraphRep antidiagPointPerturbation := by
  have hΘ := (zeroMultisection_comp_eq (fun _ h => eq_zero_of_zeroMultisection_diagSection_pos h)
    zeroMultisection_diagSection_zero).trans
    (zeroMultisection_comp_eq (fun _ h => eq_zero_of_zeroMultisection_antidiagSection_pos h)
      zeroMultisection_antidiagSection_zero).symm
  unfold pointOrientedRep
  congr 1
  congr 1

/-- **`count_eq_of_mk_eq` for one section and two different structures** (Theorem 16.6.6 for
Fredholm index `0`): on `ℝ × ℝ → ℝ` (non-zero fibres) the representatives `a = (epStructure,
F)` and `b = (negStructure, F')` of the same section `|x| ↦ |(x, x)|` have different
structures (`Γ = id`, `Γ' = |N|` for the fibre negation `N`) and different section functors
(`F(x) = (x, x)`, `F'(x) = (x, −x)`, `F' = N ∘ F`), the regular perturbations `(N, U, Λ₀)` of
dimension `0` in their models give the same oriented branched suborbifold, with support `{0}`;
so the two counts of every `0`-form agree. -/
theorem count_eq_of_mk_eq_two_structures :
    ∃ (a b : SectionRep epPolyfoldBundle) (Pa : PointPerturbation a.S.A a.F)
      (Pb : PointPerturbation b.S.A b.F),
      (⟦a⟧ : ScSection epPolyfoldBundle) = ⟦b⟧ ∧ a.S ≠ b.S ∧
      (⟦a.S⟧ : StrongPolyfoldBundle _) = ⟦b.S⟧ ∧
      pointOrientedRep a Pa = pointOrientedRep b Pb ∧
      (∀ y : (epSEP 1 1).Obj, Nontrivial ((epSEP 1 1).P ⁻¹' {y})) ∧
      (supp (pointOrientedRep a Pa).A.Θ).Nonempty ∧
      ∀ τ : ScForm epPolyfoldBundle.polyfold 0,
        Pa.count (ScForm.toStructure a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) τ) =
          Pb.count
            (ScForm.toStructure b.S.toPolyfoldStructure (toPolyfoldStructure_mem b.hS) τ) ∧
        Pa.countEff (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou)
            (ScForm.toStructure a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) τ) =
          Pb.countEff (b.S.A.X.proposition_7_4_10_of_isZhou b.S.isZhou)
            (ScForm.toStructure b.S.toPolyfoldStructure (toPolyfoldStructure_mem b.hS) τ) := by
  refine ⟨graphRep _root_.id contDiff_id, negGraphRep, diagPointPerturbation,
    antidiagPointPerturbation, mk_graphRep_id_eq_mk_negGraphRep, epStructure_ne_negStructure,
    mk_negStructure.symm, pointOrientedRep_graphRep_id_eq_negGraphRep,
    corollary_15_3_10_1_hypotheses_epSEP.1, ?_, fun τ =>
      count_eq_of_mk_eq _ _ _ _ (congrArg _ pointOrientedRep_graphRep_id_eq_negGraphRep) τ⟩
  refine ⟨(0 : Fin 1 → ℝ), ?_⟩
  change (0 : ℚ) < ((zeroMultisection (epSEP 1 1)
    (diagSection (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ))) : ℚ≥0) : ℚ)
  rw [zeroMultisection_diagSection_zero]
  exact one_pos

end StrongPolyfoldBundle

end Polyfold
