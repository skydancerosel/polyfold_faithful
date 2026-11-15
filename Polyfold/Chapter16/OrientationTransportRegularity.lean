import Polyfold.Chapter16.HalfSpaceOrientedSection
import Polyfold.Chapter16.OrientationNonEffectiveWitness
import Polyfold.Chapter12.OrientationEqualOrbitMapsGerm
import Polyfold.Chapter10.StrongBundleCutOff

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §16.6,
**Definition 16.6.5** (p. 739; 2017: Definition 16.42) with **Theorem 12.5.7 (2)** (p. 595;
2017: Theorem 12.12 (2)), **Definition 8.4.2** (p. 382) and **Definition 16.3.1** (pp. 721–722).
Numbers and pages are the 2021 text's.

# The transported orientation with the regularity carried by a strong polyfold bundle structure

`StrongPolyfoldBundleStructure.isLR` is the formal `EpStrongBundle.IsLR` (Definition 8.4.2 asked
of the strong bundle maps defined on all of `W`).  `Chapter16/OrientationOrbitMapIndependence`
proves that the transported orientation of Definition 16.6.5 does not depend on the generalized
strong bundle isomorphism under `EpStrongBundle.IsLRLocal` (Definition 8.4.2 as printed, for
strong bundle isomorphisms of `W|U(x)`).  Here the same is proved from the field `isLR`:

* Part I's hypotheses of those theorems contain sc-smooth bump functions on the base; with them
  a strong bundle isomorphism of `W|U` agrees near a point with a strong bundle map of `W`
  (`MPolyfold.AdmitsBumpFunctions.hasLocalIsoExtension`, `Chapter10/StrongBundleCutOff`), so
  `IsLR` gives the germ form `IsLRGerm` of Definition 8.4.2
  (`EpStrongBundle.IsLR.isLRGerm`, `Chapter10/LocalRegularityGerm`), and Proposition 10.4.7,
  hence Theorem 12.5.7 for equal orbit maps, needs only the germ form
  (`Chapter12/OrientationEqualOrbitMapsGerm`).
* **`SBLocalization.GenSBMap.theorem_12_5_7_two_orbitMap_unique_of_isLR`**,
  **`StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLR`** and
  `exists_unique_transport_of_isLR_polyfold`: the statements of
  `theorem_12_5_7_two_orbitMap_unique_of_isLRLocal`, `exists_unique_transport_of_isLRLocal`,
  `exists_unique_transport_of_isLRLocal_polyfold` without the hypothesis `IsLRLocal`.

Witnesses: `HalfSpaceBundle.exists_unique_transport_halfSpace_of_isLR` (boundary, non-zero
fibres) and `StrongBundleLocalizationExamples.exists_unique_transport_z3_of_isLR` (a base which
is not effective); for the hypotheses of `EpStrongBundle.IsLR.isLRGerm_of_admitsBumpFunctions`,
`HalfSpaceBundle.isLRGerm_of_admitsBumpFunctions_halfSEP` and
`StrongBundleLocalizationExamples.isLRGerm_of_admitsBumpFunctions_z3SEP`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open SEP EpStrongBundle EpStrongBundle.IsStrongBundleEquivalence

variable {A A' : SEP.{u}}

namespace GenSBMap

variable {𝔄 : GenSBMap A A'} (h𝔄 : 𝔄.IsGeneralizedIso)

variable {f : A.Obj → A.W} {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hf' : f' = pushforward h𝔄 f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)
  (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
  (hfT : A.B.IsScFredholmSectionTame f)

include hf' hX hbump hfT in
/-- **Theorem 12.5.7 (2): the push-forward orientation depends only on `|𝔄|`**, p. 595 (2017:
Theorem 12.12 (2)), with Part I's hypotheses on `W`, the formal local regularity property
`EpStrongBundle.IsLR` of `W'` and no effectiveness: an orientation `o` of `f` has exactly one
family `o'` which is an orientation of `f'` and corresponds to `o` over the middle of every
diagram representing **any** generalized strong bundle isomorphism `𝔄'` with `|𝔄'| = |𝔄|` and
`𝔄'_* f = f'`.  (`W'` admits sc-smooth bump functions as `W` does, so `IsLR` gives the germ form
`IsLRGerm` of Definition 8.4.2, which is what Proposition 10.4.7 uses.) -/
theorem theorem_12_5_7_two_orbitMap_unique_of_isLR (hLR' : A'.E.IsLR)
    {t : TopologicalSpace (OrSpace f hF.2)}
    {o : ∀ a (hs : a ∈ A.X.PObj.smoothSet), Orx f hF.2 a hs} :
    haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    IsOrientationTopology f hF.2 t → A.E.definition_12_5_4 hF hsec t o →
    ∃! o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs,
      (∀ t' : TopologicalSpace (OrSpace f' hF'.2),
        (haveI := paracompactSpace_rn_prod A'.X.PObj
         haveI := paracompactSpace_rn_pullback A'.B
         IsOrientationTopology f' hF'.2 t') → A'.E.definition_12_5_4 hF' hsec' t' o') ∧
        ∀ (𝔄' : GenSBMap A A') (h𝔄' : 𝔄'.IsGeneralizedIso) (_ : 𝔄'.orbitMap = 𝔄.orbitMap)
          (hf'' : f' = pushforward h𝔄' f) (D : SDiagram A A') (hD : D.cls = 𝔄') v
          (hv : v ∈ D.B.X.PObj.smoothSet),
          (sbe (equivalences_Ψ_of_cls h𝔄' hD)).orEqv (D.isScFredholm_pullback hF) hF'
              (pullback_eq_of_cls' h𝔄' hD hF.1 hf'') (D.hasScPlusSectionsThrough_B hsec) hsec'
              v hv (o' (D.Ψ.ϕ.obj v) ((sbe (equivalences_Ψ_of_cls h𝔄' hD)).smooth_obj hv)) =
            D.hΦ.orEqv (D.isScFredholm_pullback hF) hF rfl (D.hasScPlusSectionsThrough_B hsec)
              hsec v hv (o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) := by
  intro ht ho
  have := paracompactSpace_rn_prod A'.X.PObj
  have := paracompactSpace_rn_pullback A'.B
  have := paracompactSpace_rn_rn_prod A'.X.PObj
  have := paracompactSpace_rn_rn_pullback A'.B
  have hX' : A'.X.PObj.IsTame := (isTame_iff_of_isGeneralizedIso h𝔄).1 hX
  have hbump' : A'.X.PObj.AdmitsBumpFunctions :=
    (admitsBumpFunctions_iff_of_isGeneralizedIso h𝔄).1 hbump
  have hfT' : A'.B.IsScFredholmSectionTame f' := by
    rw [hf']; exact GenSBMap.isScFredholmSectionTame_pushforward h𝔄 hF hfT
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 hX' hbump' hfT').exists
  obtain ⟨o', ⟨ho', hc⟩, huniq⟩ := theorem_12_5_7_two_cls_unique_left h𝔄 hF hF' hf' hsec hsec'
    hX hbump hfT ht ho
  refine ⟨o', ⟨ho', fun 𝔄' h𝔄' horb hf'' D hD v hv => ?_⟩,
    fun o'' ⟨ho'', hc''⟩ => huniq o'' ⟨ho'', hc'' 𝔄 h𝔄 rfl hf'⟩⟩
  exact theorem_12_5_7_two_corr_indep_of_isLRGerm h𝔄 h𝔄' hF hF' hf' hf'' hsec hsec'
    horb.symm (hLR'.isLRGerm hbump'.hasLocalIsoExtension) (cls_rep h𝔄) hD ho.2 (ho' t₀ ht₀).2
    (hc (rep h𝔄) (cls_rep h𝔄)) v hv

end GenSBMap

end SBLocalization

namespace StrongPolyfoldBundle

open SBLocalization StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

namespace OrientationRep

variable {s : FredholmSection c}

/-- **2021 Definition 16.6.5, p. 739: the transported orientation does not depend on the
generalized isomorphism.**  Let `R` be an orientation of `s` on `R.a`, with Part I's hypotheses
on `W_a`, and `b` another representative.  There is exactly one orientation `o'` of `F_b`
(Definition 12.5.4, for every topology of Theorem 12.5.3) corresponding to `R.o` over the middle
of every diagram representing **any** generalized strong bundle isomorphism `𝔄 : W_a → W_b`
with `Γ_b ∘ |𝔄| = Γ_a` and `𝔄_* F_a = F_b`.  The base need not be effective, and the only
regularity used is the field `StrongPolyfoldBundleStructure.isLR` of `b`. -/
theorem exists_unique_transport_of_isLR (R : OrientationRep s) (b : SectionRep c)
    (hb : ⟦b⟧ = s.1) (hX : R.a.S.A.X.PObj.IsTame) (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hfT : R.a.S.A.B.IsScFredholmSectionTame R.a.F) :
    ∃ (hFb : b.S.A.E.IsScFredholmSectionFunctor b.F) (hsec' : b.S.A.B.HasScPlusSectionsThrough),
      ∃! o' : ∀ x (hs : x ∈ b.S.A.X.PObj.smoothSet), Orx b.F hFb.2 x hs,
        (∀ t' : TopologicalSpace (OrSpace b.F hFb.2),
          (haveI := paracompactSpace_rn_prod b.S.A.X.PObj
           haveI := paracompactSpace_rn_pullback b.S.A.B
           IsOrientationTopology b.F hFb.2 t') → b.S.A.E.definition_12_5_4 hFb hsec' t' o') ∧
        ∀ (𝔄 : GenSBMap R.a.S.A b.S.A) (h𝔄 : 𝔄.IsGeneralizedIso)
          (_ : ⇑b.S.Γ ∘ 𝔄.orbitMap = ⇑R.a.S.Γ) (hpush : b.F = GenSBMap.pushforward h𝔄 R.a.F)
          (D : SDiagram R.a.S.A b.S.A) (hD : D.cls = 𝔄) v (hv : v ∈ D.B.X.PObj.smoothSet),
          (sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).orEqv (D.isScFredholm_pullback R.hF) hFb
              (GenSBMap.pullback_eq_of_cls' h𝔄 hD R.hF.1 hpush)
              (D.hasScPlusSectionsThrough_B R.hsec) hsec' v hv
              (o' (D.Ψ.ϕ.obj v) ((sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).smooth_obj hv)) =
            D.hΦ.orEqv (D.isScFredholm_pullback R.hF) R.hF rfl
              (D.hasScPlusSectionsThrough_B R.hsec) R.hsec v hv
              (R.o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) := by
  obtain ⟨-, 𝔄₀, h𝔄₀, hΓ₀, hpush₀⟩ :=
    (Quotient.exact (R.ha.trans hb.symm) : SectionRep.Rel R.a b)
  have hFb : b.S.A.E.IsScFredholmSectionFunctor b.F := (ScSection.isFredholm_iff s.1).1 s.2 b hb
  have hsec' : b.S.A.B.HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough
      ((GenSBMap.admitsBumpFunctions_iff_of_isGeneralizedIso h𝔄₀).1 hbump)
  obtain ⟨o', ⟨ho', hc⟩, huniq⟩ := GenSBMap.theorem_12_5_7_two_orbitMap_unique_of_isLR
    h𝔄₀ R.hF hFb hpush₀.symm R.hsec hsec' hX hbump hfT b.S.isLR R.isOrientationTopology
    R.isOrientation
  have horb : ∀ 𝔄 : GenSBMap R.a.S.A b.S.A, ⇑b.S.Γ ∘ 𝔄.orbitMap = ⇑R.a.S.Γ →
      𝔄.orbitMap = 𝔄₀.orbitMap := fun 𝔄 hΓ => by
    funext q
    exact b.S.Γ.injective ((congrFun hΓ q).trans (congrFun hΓ₀ q).symm)
  refine ⟨hFb, hsec', o', ⟨ho', fun 𝔄 h𝔄 hΓ hpush D hD v hv =>
    hc 𝔄 h𝔄 (horb 𝔄 hΓ) hpush D hD v hv⟩, fun o'' ⟨ho'', hc''⟩ => huniq o'' ⟨ho'',
      fun 𝔄 h𝔄 horb' hpush D hD v hv => hc'' 𝔄 h𝔄 ?_ hpush D hD v hv⟩⟩
  rw [horb']
  exact hΓ₀

/-- **Definition 16.6.5 with tameness and bump functions read on the polyfold**: if the strong
polyfold bundle is tame (Definition 16.3.5 (1)), its polyfold admits sc-smooth bump functions
(Definition 16.1.5 (1)) and `F_a` has tame germ data, the conclusion of
`exists_unique_transport_of_isLR` holds for every representative `b`. -/
theorem exists_unique_transport_of_isLR_polyfold (R : OrientationRep s) (b : SectionRep c)
    (hb : ⟦b⟧ = s.1) (hc : c.IsTame) (hbump : c.polyfold.AdmitsBumpFunctions)
    (hfT : R.a.S.A.B.IsScFredholmSectionTame R.a.F) :
    ∃ (hFb : b.S.A.E.IsScFredholmSectionFunctor b.F) (hsec' : b.S.A.B.HasScPlusSectionsThrough),
      ∃! o' : ∀ x (hs : x ∈ b.S.A.X.PObj.smoothSet), Orx b.F hFb.2 x hs,
        (∀ t' : TopologicalSpace (OrSpace b.F hFb.2),
          (haveI := paracompactSpace_rn_prod b.S.A.X.PObj
           haveI := paracompactSpace_rn_pullback b.S.A.B
           IsOrientationTopology b.F hFb.2 t') → b.S.A.E.definition_12_5_4 hFb hsec' t' o') ∧
        ∀ (𝔄 : GenSBMap R.a.S.A b.S.A) (h𝔄 : 𝔄.IsGeneralizedIso)
          (_ : ⇑b.S.Γ ∘ 𝔄.orbitMap = ⇑R.a.S.Γ) (hpush : b.F = GenSBMap.pushforward h𝔄 R.a.F)
          (D : SDiagram R.a.S.A b.S.A) (hD : D.cls = 𝔄) v (hv : v ∈ D.B.X.PObj.smoothSet),
          (sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).orEqv (D.isScFredholm_pullback R.hF) hFb
              (GenSBMap.pullback_eq_of_cls' h𝔄 hD R.hF.1 hpush)
              (D.hasScPlusSectionsThrough_B R.hsec) hsec' v hv
              (o' (D.Ψ.ϕ.obj v) ((sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).smooth_obj hv)) =
            D.hΦ.orEqv (D.isScFredholm_pullback R.hF) R.hF rfl
              (D.hasScPlusSectionsThrough_B R.hsec) R.hsec v hv
              (R.o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) := by
  have hq : ⟦R.a.S.toPolyfoldStructure⟧ = c.polyfold :=
    congrArg StrongPolyfoldBundle.polyfold R.a.hS
  exact R.exists_unique_transport_of_isLR b hb ((c.isTame_iff).1 hc R.a.S R.a.hS)
    ((c.polyfold.definition_16_1_5_one).1 hbump _ hq) hfT

end OrientationRep

end StrongPolyfoldBundle

/-! ### Witnesses -/

namespace HalfSpaceBundle

open SBLocalization StrongBundle EpGroupoid

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

variable (m k) in
/-- **The hypotheses of `EpStrongBundle.IsLR.isLRGerm_of_admitsBumpFunctions` hold over the
half-space** `H = [0, ∞) × ℝᵐ` with fibre `ℝᵏ`, `k ≥ 1` (`∂H ≠ ∅`, non-zero fibres): the formal
`IsLR` and sc-smooth bump functions; so strong bundle isomorphisms of `W|U` can be cut off and
the germ form of Definition 8.4.2 holds. -/
theorem isLRGerm_of_admitsBumpFunctions_halfSEP [NeZero k] :
    (halfSEP m k).X.PObj.boundary.Nonempty ∧
    (∀ y : (halfSEP m k).Obj, Nontrivial ((halfSEP m k).P ⁻¹' {y})) ∧
    (halfSEP m k).E.IsLR ∧ (halfSEP m k).X.PObj.AdmitsBumpFunctions ∧
    (halfSEP m k).B.HasLocalIsoExtension ∧ (halfSEP m k).E.IsLRGerm :=
  ⟨⟨_, zero_mem_boundary_halfSEP m k⟩, nontrivial_fibre_halfSEP m k,
    EpStrongBundle.isLR_trivial _, admitsBumpFunctions_halfSEP m k,
    (admitsBumpFunctions_halfSEP m k).hasLocalIsoExtension,
    (EpStrongBundle.isLR_trivial _).isLRGerm_of_admitsBumpFunctions
      (admitsBumpFunctions_halfSEP m k)⟩

open StrongPolyfoldBundle in
/-- **Definition 16.6.5 in an example with boundary and non-zero fibres**: for the oriented
sc-Fredholm section `|x| ↦ |(x, φ(x))|` over the half-space `H = [0, ∞) × ℝᵐ` (`∂H ≠ ∅`, fibres
`ℝᵏ`, `k ≥ 1`), the hypotheses of `OrientationRep.exists_unique_transport_of_isLR` hold
(tame, sc-smooth bump functions, tame germ data), and so for
every representative `b` of the section exactly one orientation of `F_b` corresponds to the
orientation over every diagram of every generalized strong bundle isomorphism `𝔄` with
`Γ_b ∘ |𝔄| = Γ` and `𝔄_* F = F_b`. -/
theorem exists_unique_transport_halfSpace_of_isLR [NeZero k] (hφ : ContDiff ℝ ∞ φ) :
    (halfSEP m k).X.PObj.boundary.Nonempty ∧
    (∀ y : (halfSEP m k).Obj, Nontrivial ((halfSEP m k).P ⁻¹' {y})) ∧
    (halfSEP m k).X.PObj.IsTame ∧ (halfSEP m k).X.PObj.AdmitsBumpFunctions ∧
    (halfSEP m k).B.IsScFredholmSectionTame (graphSection φ) ∧
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
    fun b hb =>
      (halfOrientationRep hφ).exists_unique_transport_of_isLR b hb (isTame_halfSEP m k)
        (admitsBumpFunctions_halfSEP m k) (isScFredholmSectionTame_graphSection_halfSEP hφ)⟩

end HalfSpaceBundle

namespace StrongBundleLocalizationExamples

open SBLocalization StrongBundleEquivalenceExamples TrivialBundle EpStrongBundle
open LocalizationLRBundleBaseExamples EpGroupoid.Examples
open StrongPolyfoldBundle StrongPolyfoldBundleStructure

variable {k : ℕ} {φ : (Fin 1 → ℝ) → (Fin k → ℝ)}

variable (k) in
/-- **The hypotheses of `EpStrongBundle.IsLR.isLRGerm_of_admitsBumpFunctions` hold over a base
which is not effective**, `ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ`. -/
theorem isLRGerm_of_admitsBumpFunctions_z3SEP :
    ¬ (z3SEP k).X.IsEffective ∧ (z3SEP k).E.IsLR ∧ (z3SEP k).X.PObj.AdmitsBumpFunctions ∧
    (z3SEP k).E.IsLRGerm :=
  ⟨not_isEffective_trivialZ3, LocalizationLRCounterexample.isLR_z3EpBundle k,
    admitsBumpFunctions_z3SEP k,
    (LocalizationLRCounterexample.isLR_z3EpBundle k).isLRGerm_of_admitsBumpFunctions
      (admitsBumpFunctions_z3SEP k)⟩

/-- **Definition 16.6.5 over a polyfold which is not effective**: for the oriented sc-Fredholm
section `|x| ↦ |(x, φ(x))|` over `|ℤ/3 × ℝ ⇉ ℝ|` the base is not effective, and the hypotheses of
`OrientationRep.exists_unique_transport_of_isLR` hold (tame, sc-smooth bump functions, tame
germ data); so for every representative `b` of the section
exactly one orientation of `F_b` corresponds to the orientation over every diagram of every
generalized strong bundle isomorphism `𝔄` with `Γ_b ∘ |𝔄| = Γ` and `𝔄_* F = F_b`. -/
theorem exists_unique_transport_z3_of_isLR (hφ : ContDiff ℝ ∞ φ) :
    ¬ (z3SEP k).X.IsEffective ∧ (z3SEP k).X.PObj.IsTame ∧
    (z3SEP k).X.PObj.AdmitsBumpFunctions ∧
    (z3SEP k).B.IsScFredholmSectionTame (graphSection φ) ∧
    ∀ (b : SectionRep (z3Bundle k)) (_ : ⟦b⟧ = (z3FredholmSection hφ).1),
      ∃ (hFb : b.S.A.E.IsScFredholmSectionFunctor b.F)
        (hsec' : b.S.A.B.HasScPlusSectionsThrough),
        ∃! o' : ∀ x (hs : x ∈ b.S.A.X.PObj.smoothSet), Orx b.F hFb.2 x hs,
          (∀ t' : TopologicalSpace (OrSpace b.F hFb.2),
            (haveI := paracompactSpace_rn_prod b.S.A.X.PObj
             haveI := paracompactSpace_rn_pullback b.S.A.B
             IsOrientationTopology b.F hFb.2 t') →
              b.S.A.E.definition_12_5_4 hFb hsec' t' o') ∧
          ∀ (𝔄 : GenSBMap (z3OrientationRep hφ).a.S.A b.S.A) (h𝔄 : 𝔄.IsGeneralizedIso)
            (_ : ⇑b.S.Γ ∘ 𝔄.orbitMap = ⇑(z3OrientationRep hφ).a.S.Γ)
            (hpush : b.F = GenSBMap.pushforward h𝔄 (z3OrientationRep hφ).a.F)
            (D : SDiagram (z3OrientationRep hφ).a.S.A b.S.A) (hD : D.cls = 𝔄) v
            (hv : v ∈ D.B.X.PObj.smoothSet),
            (sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).orEqv
                (D.isScFredholm_pullback (z3OrientationRep hφ).hF) hFb
                (GenSBMap.pullback_eq_of_cls' h𝔄 hD (z3OrientationRep hφ).hF.1 hpush)
                (D.hasScPlusSectionsThrough_B (z3OrientationRep hφ).hsec) hsec' v hv
                (o' (D.Ψ.ϕ.obj v)
                  ((sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).smooth_obj hv)) =
              D.hΦ.orEqv (D.isScFredholm_pullback (z3OrientationRep hφ).hF)
                (z3OrientationRep hφ).hF rfl
                (D.hasScPlusSectionsThrough_B (z3OrientationRep hφ).hsec)
                (z3OrientationRep hφ).hsec v hv
                ((z3OrientationRep hφ).o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) :=
  ⟨not_isEffective_trivialZ3, isTame_z3SEP k, admitsBumpFunctions_z3SEP k,
    isScFredholmSectionTame_graphSection_z3 hφ, fun b hb =>
      (z3OrientationRep hφ).exists_unique_transport_of_isLR b hb (isTame_z3SEP k)
        (admitsBumpFunctions_z3SEP k) (isScFredholmSectionTame_graphSection_z3 hφ)⟩

end StrongBundleLocalizationExamples

end Polyfold
