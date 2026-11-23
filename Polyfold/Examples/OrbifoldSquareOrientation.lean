import Polyfold.Examples.OrbifoldSquareStructure
import Polyfold.Chapter18.OrientationWitness
import Polyfold.Chapter16.OrientationNonEffectiveWitness
import Polyfold.Chapter16.CircleSectionCobordism
import Polyfold.Chapter16.IndexZeroNoBumpsUnconditional

/-!
# The orbifold `ℂ/ℤ₅` and the section `z ↦ z²`: the orientation

A worked example for Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021),
Theorem 16.6.6, 2021 p. 739, with Definitions 12.5.4 (p. 594) and 16.6.5 (p. 739).

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquare`)

* `equiv_apply_apply_of_two`: a permutation of a set with two elements is an involution.
* `orMor_zero`: every isotropy morphism `(g, 0)` acts as the identity on `Or^f_0` (it has order
  dividing `5`, and `Or^f_0` has two elements).  The linearization `f'(0) = 0` is not an
  isomorphism, so `EpStrongBundle.orMor_eq_self_of_bijective` does not apply here.
* `exists_isContOrOn_sqSection`: a continuous orientation over all of `ℂ`.
* `isOrInvariant_of_isContOrOn`: it is invariant under every morphism `(g, z)`: the invariance
  is locally constant along the connected sheet `{(g, z)}`, and holds at `(g, 0)`.
* `sqOrientation`, `definition_12_5_4_sqOrientation`, **`sqOrientationRep`**: an orientation of
  the sc-Fredholm section `|z| ↦ |(z, z²)|` (Definition 16.6.5).
* **`canonicalGermInput_sqOrientationRep`**: the standing hypotheses of Theorem 16.6.6 for
  index `0` (tame germ data, Fredholm index `0`) in the model of `sqOrientationRep`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.OrbifoldSquare

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples SBLocalization

/-- **A permutation of a set with two elements is an involution.** -/
theorem equiv_apply_apply_of_two {α : Type*} (h2 : ∃ a b : α, a ≠ b ∧ ∀ c, c = a ∨ c = b)
    (e : α ≃ α) (o : α) : e (e o) = o := by
  by_contra hne
  obtain ⟨a, b, -, hall⟩ := h2
  have h0 : e o ≠ o := fun h => hne (by rw [h, h])
  have h1 : e (e o) ≠ e o := fun h => h0 (e.injective h)
  rcases hall o with ho | ho <;> rcases hall (e o) with h1' | h1' <;>
    rcases hall (e (e o)) with h2' | h2' <;>
    first
      | exact h0 (h1'.trans ho.symm)
      | exact h1 (h2'.trans h1'.symm)
      | exact hne (h2'.trans ho.symm)

/-! ### The standing data -/

theorem mem_smoothSet_A5 (x : A5.Obj) : x ∈ A5.X.PObj.smoothSet := by
  have h : (rnPolyfold 2).smoothSet = univ := rnPolyfold_smoothSet
  exact h ▸ mem_univ x

theorem isTame_A5 : A5.X.PObj.IsTame := rnPolyfold_isTame

theorem admitsBumpFunctions_A5 : A5.X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_rn 2

theorem hasScPlusSectionsThrough_A5 : A5.B.HasScPlusSectionsThrough :=
  hasScPlusSectionsThrough_epSEP 2 2

/-- `f` has tame germ data (Definition 3.6.4). -/
theorem isScFredholmSectionTame_sqSection : A5.B.IsScFredholmSectionTame sqSection :=
  isScFredholmSectionTame_graphSection contDiff_sq

/-- **The Fredholm index of `f` is `0`** at every point. -/
theorem isIndexAt_sqSection (x : A5.Obj) : A5.B.IsIndexAt sqSection x 0 := by
  have h := isIndexAt_graphSection_epSEP (n := 2) (k := 2) contDiff_sq x
  have h0 : ((2 : ℕ) : ℤ) - ((2 : ℕ) : ℤ) = 0 := by norm_num
  rw [h0] at h
  exact h

/-! ### The isotropy of `0` acts trivially on `Or^f_0` -/

/-- **Every isotropy morphism `(g, 0)` acts as the identity on `Or^f_0`**: `g⁵ = 1` and
`Or^f_0` has two elements. -/
theorem orMor_zero (g : G5) (hs : (0 : Fin 2 → ℝ) ∈ A5.X.PObj.smoothSet)
    (o : Orx (B := A5.B) sqSection isScFredholmSectionFunctor_sqSection.2
      (0 : Fin 2 → ℝ) hs) :
    A5.E.orMor isScFredholmSectionFunctor_sqSection hasScPlusSectionsThrough_A5
      ((g, 0) : A5.Mor) rfl (smul_zero5 g) hs hs o = o := by
  have hF := isScFredholmSectionFunctor_sqSection
  have hsec := hasScPlusSectionsThrough_A5
  let e : G5 → (Orx (B := A5.B) sqSection hF.2 (0 : Fin 2 → ℝ) hs ≃
      Orx (B := A5.B) sqSection hF.2 (0 : Fin 2 → ℝ) hs) :=
    fun a => A5.E.orMor hF hsec ((a, 0) : A5.Mor) rfl (smul_zero5 a) hs hs
  have key : ∀ a b : G5, (e b).trans (e a) = e (a * b) := fun a b =>
    A5.E.orMor_comp hF hsec (φ := ((b, 0) : A5.Mor)) (ψ := ((a, 0) : A5.Mor)) rfl
      (smul_zero5 b) rfl (smul_zero5 a) hs hs hs
  have hone : e 1 = Equiv.refl _ :=
    A5.E.orMor_unit hF hsec (σ := ((1, 0) : A5.Mor)) (x := (0 : Fin 2 → ℝ)) rfl rfl
      (smul_zero5 1) hs
  have hg : ∀ a : G5, a * (a * (a * (a * a))) = 1 := by decide
  have two := exists_two_orx hF.2 hs hsec
  have h5 : e g (e g (e g (e g (e g o)))) = o := by
    have k1 := DFunLike.congr_fun (key g g) o
    have k2 := DFunLike.congr_fun (key g (g * g)) o
    have k3 := DFunLike.congr_fun (key g (g * (g * g))) o
    have k4 := DFunLike.congr_fun (key g (g * (g * (g * g)))) o
    rw [Equiv.trans_apply] at k1 k2 k3 k4
    rw [k1, k2, k3, k4, hg g, hone]
    rfl
  have h2 : ∀ p, e g (e g p) = p := equiv_apply_apply_of_two two (e g)
  rw [h2, h2] at h5
  exact h5

/-! ### A continuous orientation, and its invariance -/

/-- **`f` has a continuous orientation over all of `ℂ`** (Theorem 6.6.17 and
Definition 6.6.16: two paths of `ℝ²` with the same end points are homotopic). -/
theorem exists_isContOrOn_sqSection :
    haveI := paracompactSpace_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_pullback A5.B
    haveI := paracompactSpace_rn_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A5.B
    ∃ o : ∀ a (hs : a ∈ A5.X.PObj.smoothSet),
        Orx (B := A5.B) sqSection isScFredholmSectionFunctor_sqSection.2 a hs,
      IsSectionOrientation (B := A5.B) sqSection isScFredholmSectionFunctor_sqSection.2 o ∧
      @Continuous _ _ _ (orTopology (orLocalTransport isTame_A5 admitsBumpFunctions_A5
        isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5)) (orSec o) ∧
      IsContOrOn (orLocalTransport isTame_A5 admitsBumpFunctions_A5
        isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5) univ o := by
  have := paracompactSpace_rn_prod A5.X.PObj
  have := paracompactSpace_rn_pullback A5.B
  have := paracompactSpace_rn_rn_prod A5.X.PObj
  have := paracompactSpace_rn_rn_pullback A5.B
  obtain ⟨o, ho, hc⟩ := exists_continuous_orSec_of_hom_eq isTame_A5 admitsBumpFunctions_A5
    isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5
    (fun {_ _} a b => PathCat.hom_eq_rn (n := 2) a b)
  exact ⟨o, ho, hc, isContOrOn_univ_of_continuous_orSec
    (fun _ hy => exists_two_orx _ hy hasScPlusSectionsThrough_A5)
    A5.X.PObj.hasConnectedSmoothNbhds hc⟩

/-- **Every continuous orientation of `f` over all of `ℂ` is invariant under the morphisms**
(Definition 12.5.4): the invariance at `(g, z)` is locally constant in `z`
(`EpStrongBundle.eventually_isOrInvariantAt_iff`, from Theorem 12.5.3), `ℂ` is connected, and
at `(g, 0)` it holds by `orMor_zero`. -/
theorem isOrInvariant_of_isContOrOn
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × A5.Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace A5.P (Prod.snd : (Fin n → ℝ) × A5.Obj → A5.Obj))]
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × A5.Obj))]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace
      (pullbackProj A5.P (Prod.snd : (Fin n → ℝ) × A5.Obj → A5.Obj))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × A5.Obj) → (Fin n → ℝ) × A5.Obj))]
    {o : ∀ a (hs : a ∈ A5.X.PObj.smoothSet),
      Orx (B := A5.B) sqSection isScFredholmSectionFunctor_sqSection.2 a hs}
    (ho : IsContOrOn (orLocalTransport isTame_A5 admitsBumpFunctions_A5
      isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5) univ o) :
    A5.E.IsOrInvariant isScFredholmSectionFunctor_sqSection hasScPlusSectionsThrough_A5 o := by
  have hF := isScFredholmSectionFunctor_sqSection
  have hsec := hasScPlusSectionsThrough_A5
  refine (A5.E.isOrInvariant_iff_forall_isOrInvariantAt hF hsec).2 fun m => ?_
  have hloc : ∀ g : G5, IsLocallyConstant fun q : Fin 2 → ℝ =>
      A5.E.IsOrInvariantAt hF hsec o ((g, q) : A5.Mor) := fun g =>
    (IsLocallyConstant.iff_eventually_eq _).2 fun q => by
      have h := A5.E.eventually_isOrInvariantAt_iff hF hsec isTame_A5 admitsBumpFunctions_A5
        isScFredholmSectionTame_sqSection mem_smoothSet_A5 ho ((g, q) : A5.Mor)
      have hc : Continuous fun q : Fin 2 → ℝ => ((g, q) : A5.Mor) :=
        continuous_const.prodMk continuous_id
      filter_upwards [hc.continuousAt.eventually h] with q' hq'
      exact propext hq'
  have h0 : ∀ g : G5, A5.E.IsOrInvariantAt hF hsec o ((g, 0) : A5.Mor) := fun g => by
    refine (A5.E.isOrInvariantAt_iff' hF hsec).2 fun {x x'} hx hx' hs₁ hs₂ => ?_
    obtain rfl : (0 : Fin 2 → ℝ) = x := hx
    obtain rfl : (0 : Fin 2 → ℝ) = x' := (smul_zero5 g).symm.trans hx'
    exact orMor_zero g hs₁ _
  obtain ⟨g, q⟩ := m
  have e := (hloc g).apply_eq_of_preconnectedSpace q 0
  exact e ▸ h0 g

/-- **An orientation of `f`** (one of the two continuous orientations is chosen). -/
def sqOrientation : ∀ a (hs : a ∈ A5.X.PObj.smoothSet),
    Orx (B := A5.B) sqSection isScFredholmSectionFunctor_sqSection.2 a hs :=
  exists_isContOrOn_sqSection.choose

theorem isSectionOrientation_sqOrientation :
    haveI := paracompactSpace_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_pullback A5.B
    IsSectionOrientation (B := A5.B) sqSection isScFredholmSectionFunctor_sqSection.2
      sqOrientation :=
  exists_isContOrOn_sqSection.choose_spec.1

/-- **`sqOrientation` is an orientation in the sense of Definition 12.5.4**: continuous for
Part I's topology on `O_f` and invariant under the morphisms `(g, z)`. -/
theorem definition_12_5_4_sqOrientation :
    haveI := paracompactSpace_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_pullback A5.B
    haveI := paracompactSpace_rn_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A5.B
    A5.E.definition_12_5_4 isScFredholmSectionFunctor_sqSection hasScPlusSectionsThrough_A5
      (orTopology (orLocalTransport isTame_A5 admitsBumpFunctions_A5
        isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5)) sqOrientation := by
  have := paracompactSpace_rn_prod A5.X.PObj
  have := paracompactSpace_rn_pullback A5.B
  have := paracompactSpace_rn_rn_prod A5.X.PObj
  have := paracompactSpace_rn_rn_pullback A5.B
  exact ⟨exists_isContOrOn_sqSection.choose_spec.2.1,
    isOrInvariant_of_isContOrOn exists_isContOrOn_sqSection.choose_spec.2.2⟩

/-- Part I's topology on `O_f` is a topology with the properties of Theorem 12.5.3. -/
theorem isOrientationTopology_sqSection :
    haveI := paracompactSpace_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_pullback A5.B
    haveI := paracompactSpace_rn_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A5.B
    IsOrientationTopology (B := A5.B) sqSection isScFredholmSectionFunctor_sqSection.2
      (orTopology (orLocalTransport isTame_A5 admitsBumpFunctions_A5
        isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5)) := by
  have := paracompactSpace_rn_prod A5.X.PObj
  have := paracompactSpace_rn_pullback A5.B
  have := paracompactSpace_rn_rn_prod A5.X.PObj
  have := paracompactSpace_rn_rn_pullback A5.B
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 isTame_A5 admitsBumpFunctions_A5
    isScFredholmSectionTame_sqSection).exists
  exact eq_orTopology_of isTame_A5 admitsBumpFunctions_A5 isScFredholmSectionTame_sqSection
    hasScPlusSectionsThrough_A5 ht₀.isLocalHomeomorph ht₀.propagation ▸ ht₀

/-- **An orientation of the sc-Fredholm section `|z| ↦ |(z, z²)|` over `ℂ/ℤ₅`**
(Definition 16.6.5). -/
def sqOrientationRep : OrientationRep sqFredholmSection where
  a := sqRep
  ha := rfl
  hF := isScFredholmSectionFunctor_sqSection
  hsec := hasScPlusSectionsThrough_A5
  t := haveI := paracompactSpace_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_pullback A5.B
    haveI := paracompactSpace_rn_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A5.B
    orTopology (orLocalTransport isTame_A5 admitsBumpFunctions_A5
      isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5)
  isOrientationTopology := isOrientationTopology_sqSection
  o := sqOrientation
  isOrientation := definition_12_5_4_sqOrientation

/-- **The standing hypotheses of Theorem 16.6.6 (2021 p. 739) for index `0` hold in the model
of `sqOrientationRep`**: tame germ data and Fredholm index `0`. -/
theorem canonicalGermInput_sqOrientationRep : CanonicalGermInput sqOrientationRep 0 :=
  ⟨isScFredholmSectionTame_sqSection, fun x _ => by exact_mod_cast isIndexAt_sqSection x⟩

end Polyfold.Examples.OrbifoldSquare
