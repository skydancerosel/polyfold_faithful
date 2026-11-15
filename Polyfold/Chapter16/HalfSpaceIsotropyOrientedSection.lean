import Polyfold.Chapter16.HalfSpaceOrientedSection
import Polyfold.Chapter16.TrivialIsotropyBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §16.6,
**Definition 16.6.5** (p. 739; 2017: Definition 16.42) with Theorem 12.5.7: an oriented
sc-Fredholm section over a polyfold which is **not effective and has boundary**.

# An oriented section over `|ℤ/3 × H ⇉ H|`

The strong bundle `H × ℝᵏ → H`, `H = [0, ∞) × ℝᵐ`, over the translation groupoid of the trivial
action of `ℤ/3` on `H` (`TrivialIsotropy.z3SEPOf`): `∂H ≠ ∅`, every fibre is non-zero for
`k ≥ 1`, and every point has isotropy `ℤ/3`, so the ep-groupoid is not effective.  The graph
section `f(x) = (x, φ(x))` of a `C^∞` map is oriented by the orientation `halfOrientation` of
the trivial ep-groupoid of `H` (`O_f` depends on the bundle and `f` only), which is invariant
under the morphisms `(g, x)` (their third power is `1_x` and `Or^f_x` has two elements).

## What is formalized (namespace `Polyfold.HalfSpaceBundle`)

* `halfZ3SEP m k`; `not_isEffective_halfZ3SEP`, `zero_mem_boundary_halfZ3SEP`,
  `nontrivial_fibre_halfZ3SEP`, `isScFredholmSectionFunctor_graphSection_halfZ3`.
* `definition_12_5_4_halfOrientation_z3`: `halfOrientation` is an orientation in the sense of
  Definition 12.5.4 over `ℤ/3 × H ⇉ H`.
* `halfZ3Structure` (Definition 16.3.1: (ZHOU), paracompact `|X|`, the local regularity
  property), `halfZ3PolyfoldBundle`, `halfZ3GraphRep`, `halfZ3FredholmSection`,
  **`halfZ3OrientationRep`** (Definition 16.6.5).
* **`exists_unique_transport_halfZ3`**: `¬ IsEffective`, `∂X ≠ ∅`, non-zero fibres, and the
  hypotheses and conclusion of `OrientationRep.exists_unique_transport_of_isLRLocal`: for every
  representative `b` of the section exactly one orientation of `F_b` corresponds to the given
  one over every diagram of every generalized strong bundle isomorphism `𝔄` with
  `Γ_b ∘ |𝔄| = Γ` and `𝔄_* F = F_b`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open SBLocalization StrongBundle EpGroupoid TrivialIsotropy

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

variable (m k) in
/-- **`H × ℝᵏ → H` over `ℤ/3 × H ⇉ H`** (the trivial action of `ℤ/3`). -/
abbrev halfZ3SEP : SEP.{0} := z3SEPOf (basePoly m) (bundle m k)

theorem not_isEffective_halfZ3SEP : ¬ (halfZ3SEP m k).X.IsEffective :=
  not_isEffective_z3SEPOf (bundle m k) ⟨0, fun _ => le_rfl⟩

theorem zero_mem_boundary_halfZ3SEP :
    (⟨0, fun _ => le_rfl⟩ : (halfZ3SEP m k).Obj) ∈ (halfZ3SEP m k).X.PObj.boundary :=
  zero_mem_boundary_halfSEP m k

theorem nontrivial_fibre_halfZ3SEP [NeZero k] (x : (halfZ3SEP m k).Obj) :
    Nontrivial ((halfZ3SEP m k).P ⁻¹' {x}) :=
  nontrivial_fibre_halfSEP m k x

theorem isScFredholmSectionFunctor_graphSection_halfZ3 (hφ : ContDiff ℝ ∞ φ) :
    (halfZ3SEP m k).E.IsScFredholmSectionFunctor (graphSection φ) :=
  isScFredholmSectionFunctor_z3SEPOf (bundle m k)
    (isScFredholmSectionFunctor_graphSection_halfSEP hφ).1.1
    (isScFredholmSectionFunctor_graphSection_halfSEP hφ).2

/-- **`halfOrientation` is an orientation over `ℤ/3 × H ⇉ H`** (Definition 12.5.4): continuous
for Part I's topology on `O_f` (which depends on the bundle and `f` only), and invariant under
the morphisms `(g, x)`, which act as the identity on `Or^f_x`. -/
theorem definition_12_5_4_halfOrientation_z3 (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_pullback (halfSEP m k).B
    haveI := paracompactSpace_rn_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (halfSEP m k).B
    (halfZ3SEP m k).E.definition_12_5_4 (isScFredholmSectionFunctor_graphSection_halfZ3 hφ)
      (hasScPlusSectionsThrough_halfSEP m k)
      (orTopology (orLocalTransport (isTame_halfSEP m k) (admitsBumpFunctions_halfSEP m k)
        (isScFredholmSectionTame_graphSection_halfSEP hφ)
        (hasScPlusSectionsThrough_halfSEP m k)))
      (halfOrientation hφ) :=
  ⟨(exists_continuous_orSec_graphSection_halfSEP hφ).choose_spec,
    fun σ x x' hx hx' hs hs' => by
      obtain rfl : (halfZ3SEP m k).X.src σ = x := hx
      obtain rfl : (halfZ3SEP m k).X.src σ = x' := hx'
      exact orMor_z3SEPOf (bundle m k) (isScFredholmSectionFunctor_graphSection_halfZ3 hφ)
        (hasScPlusSectionsThrough_halfSEP m k) σ hs (halfOrientation hφ _ hs)⟩

/-! ### The strong polyfold bundle and the oriented sc-Fredholm section -/

variable (m k) in
/-- **The strong polyfold bundle structure `((P : W → X, μ), id, id)`** for
`|P| : |W| → |ℤ/3 × H ⇉ H|` (Definition 16.3.1). -/
def halfZ3Structure : StrongPolyfoldBundleStructure (halfZ3SEP m k).E.projFunctor.orbitMap where
  A := halfZ3SEP m k
  isZhou := isZhou_z3SEPOf (bundle m k)
  paracompact := hasParacompactOrbitSpace_z3SEPOf (bundle m k)
  isLRLocal := isLRLocal_z3SEPOf (bundle m k)
  Γ := Homeomorph.refl _
  γ := Homeomorph.refl _
  comm := rfl

variable (m k) in
/-- The strong polyfold bundle of `halfZ3Structure` (Definition 16.3.4). -/
def halfZ3PolyfoldBundle : StrongPolyfoldBundle (halfZ3SEP m k).E.projFunctor.orbitMap :=
  ⟦halfZ3Structure m k⟧

open StrongPolyfoldBundle in
/-- **The representative `(halfZ3Structure, graph φ)`** of the section `|x| ↦ |(x, φ(x))|`
(Definition 16.3.18). -/
def halfZ3GraphRep (hφ : ContDiff ℝ ∞ φ) : SectionRep (halfZ3PolyfoldBundle m k) where
  S := halfZ3Structure m k
  hS := rfl
  F := graphSection φ
  hF := (isScFredholmSectionFunctor_graphSection_halfZ3 hφ).1
  f := Quotient.lift
    (fun x : (halfZ3SEP m k).Obj => (halfZ3SEP m k).E.toEpGroupoid.π (graphSection φ x))
    fun x y h => by
      have e : x = y := injective_π_z3SEPOf (bundle m k) (Quotient.sound h)
      rw [e]
  continuous_f := Continuous.quotient_lift ((halfZ3SEP m k).E.toEpGroupoid.continuous_π.comp
    (continuous_id.prodMk (hφ.continuous.comp continuous_subtype_val))) _
  isSection z := Quotient.inductionOn z fun _ => rfl
  comm _ := rfl

open StrongPolyfoldBundle in
/-- **The sc-Fredholm section `|x| ↦ |(x, φ(x))|`** over `|ℤ/3 × H ⇉ H|` (Definition 16.6.1). -/
def halfZ3FredholmSection (hφ : ContDiff ℝ ∞ φ) : FredholmSection (halfZ3PolyfoldBundle m k) :=
  ⟨⟦halfZ3GraphRep hφ⟧, halfZ3GraphRep hφ, rfl, isScFredholmSectionFunctor_graphSection_halfZ3 hφ⟩

open StrongPolyfoldBundle in
/-- **An orientation of the sc-Fredholm section over `|ℤ/3 × H ⇉ H|`** (Definition 16.6.5): the
representative `(halfZ3Structure, graph φ)`, Part I's topology on `O_f`, and `halfOrientation`. -/
def halfZ3OrientationRep (hφ : ContDiff ℝ ∞ φ) : OrientationRep (halfZ3FredholmSection hφ) where
  a := halfZ3GraphRep hφ
  ha := rfl
  hF := isScFredholmSectionFunctor_graphSection_halfZ3 hφ
  hsec := hasScPlusSectionsThrough_halfSEP m k
  t := haveI := paracompactSpace_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_pullback (halfSEP m k).B
    haveI := paracompactSpace_rn_rn_prod (halfSEP m k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (halfSEP m k).B
    orTopology (orLocalTransport (isTame_halfSEP m k) (admitsBumpFunctions_halfSEP m k)
      (isScFredholmSectionTame_graphSection_halfSEP hφ) (hasScPlusSectionsThrough_halfSEP m k))
  isOrientationTopology := isOrientationTopology_graphSection_halfSEP hφ
  o := halfOrientation hφ
  isOrientation := definition_12_5_4_halfOrientation_z3 hφ

open StrongPolyfoldBundle in
/-- **Definition 16.6.5 over a polyfold which is not effective and has boundary**: for the
oriented sc-Fredholm section `|x| ↦ |(x, φ(x))|` over `|ℤ/3 × H ⇉ H|` (`¬ IsEffective`,
`∂H ≠ ∅`, fibres `ℝᵏ ≠ 0` for `k ≥ 1`) the hypotheses of
`OrientationRep.exists_unique_transport_of_isLRLocal` hold (tame, sc-smooth bump functions, tame
germ data, the local regularity property), and so for every representative `b` of the section
exactly one orientation of `F_b` corresponds to the orientation over every diagram of every
generalized strong bundle isomorphism `𝔄` with `Γ_b ∘ |𝔄| = Γ` and `𝔄_* F = F_b`. -/
theorem exists_unique_transport_halfZ3 [NeZero k] (hφ : ContDiff ℝ ∞ φ) :
    ¬ (halfZ3SEP m k).X.IsEffective ∧ (halfZ3SEP m k).X.PObj.boundary.Nonempty ∧
    (∀ y : (halfZ3SEP m k).Obj, Nontrivial ((halfZ3SEP m k).P ⁻¹' {y})) ∧
    (halfZ3SEP m k).X.PObj.IsTame ∧ (halfZ3SEP m k).X.PObj.AdmitsBumpFunctions ∧
    (halfZ3SEP m k).B.IsScFredholmSectionTame (graphSection φ) ∧ (halfZ3SEP m k).E.IsLRLocal ∧
    ∀ (b : SectionRep (halfZ3PolyfoldBundle m k)) (_ : ⟦b⟧ = (halfZ3FredholmSection hφ).1),
      ∃ (hFb : b.S.A.E.IsScFredholmSectionFunctor b.F)
        (hsec' : b.S.A.B.HasScPlusSectionsThrough),
        ∃! o' : ∀ x (hs : x ∈ b.S.A.X.PObj.smoothSet), Orx b.F hFb.2 x hs,
          (∀ t' : TopologicalSpace (OrSpace b.F hFb.2),
            (haveI := paracompactSpace_rn_prod b.S.A.X.PObj
             haveI := paracompactSpace_rn_pullback b.S.A.B
             IsOrientationTopology b.F hFb.2 t') →
              b.S.A.E.definition_12_5_4 hFb hsec' t' o') ∧
          ∀ (𝔄 : GenSBMap (halfZ3OrientationRep hφ).a.S.A b.S.A) (h𝔄 : 𝔄.IsGeneralizedIso)
            (_ : ⇑b.S.Γ ∘ 𝔄.orbitMap = ⇑(halfZ3OrientationRep hφ).a.S.Γ)
            (hpush : b.F = GenSBMap.pushforward h𝔄 (halfZ3OrientationRep hφ).a.F)
            (D : SDiagram (halfZ3OrientationRep hφ).a.S.A b.S.A) (hD : D.cls = 𝔄) v
            (hv : v ∈ D.B.X.PObj.smoothSet),
            (sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).orEqv
                (D.isScFredholm_pullback (halfZ3OrientationRep hφ).hF) hFb
                (GenSBMap.pullback_eq_of_cls' h𝔄 hD (halfZ3OrientationRep hφ).hF.1 hpush)
                (D.hasScPlusSectionsThrough_B (halfZ3OrientationRep hφ).hsec) hsec' v hv
                (o' (D.Ψ.ϕ.obj v)
                  ((sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).smooth_obj hv)) =
              D.hΦ.orEqv (D.isScFredholm_pullback (halfZ3OrientationRep hφ).hF)
                (halfZ3OrientationRep hφ).hF rfl
                (D.hasScPlusSectionsThrough_B (halfZ3OrientationRep hφ).hsec)
                (halfZ3OrientationRep hφ).hsec v hv
                ((halfZ3OrientationRep hφ).o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) :=
  ⟨not_isEffective_halfZ3SEP, ⟨_, zero_mem_boundary_halfZ3SEP⟩, nontrivial_fibre_halfZ3SEP,
    isTame_halfSEP m k, admitsBumpFunctions_halfSEP m k,
    isScFredholmSectionTame_graphSection_halfSEP hφ, isLRLocal_z3SEPOf (bundle m k), fun b hb =>
      (halfZ3OrientationRep hφ).exists_unique_transport_of_isLRLocal b hb (isTame_halfSEP m k)
        (admitsBumpFunctions_halfSEP m k) (isScFredholmSectionTame_graphSection_halfSEP hφ)
        (isLRLocal_z3SEPOf (bundle m k))⟩

end HalfSpaceBundle

end Polyfold
