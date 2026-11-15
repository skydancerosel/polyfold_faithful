import Polyfold.Chapter16.OrientationClassIndependence
import Polyfold.Chapter12.OrientationGeneralizedIsoOrbitMap

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §16.6,
**Definition 16.6.5** (p. 739; 2017: Definition 16.42) with **Theorem 12.5.7 (2)** (p. 595;
2017: Theorem 12.12 (2)), **Definition 8.4.2** (p. 382) and **Definition 16.3.1** (p. 721): the
orientation of one representative of an sc-Fredholm section determines the orientations of all
others, also where the polyfold is not effective.

# The transported orientation does not depend on the generalized isomorphism

## The text, paraphrased

(Definition 16.3.1) A strong polyfold bundle structure consists of a strong bundle over an
ep-groupoid with the local regularity property and homeomorphisms `Γ`, `γ`.
(Definition 16.6.5) An orientation of one representative `(W, F)` of `f` determines orientations
of all other representatives `(W', F')`, by Theorem 12.5.7, along the generalized strong bundle
isomorphism `𝔄 : W → W'` with `Γ' ∘ |𝔄| = Γ` and `𝔄_* F = F'`.

For a base which is not effective `𝔄` is not determined by `Γ' ∘ |𝔄| = Γ`
(`StrongPolyfoldBundleStructure.not_uniqueness_16_3_3`).  The transported orientation is.

## What is formalized

The local regularity property is Definition 8.4.2 read with strong bundle isomorphisms of
`W|U(x)` (`EpStrongBundle.IsLRLocal`).

* `GenSBMap.isLRLocal_iff_of_isGeneralizedIso`: the property passes along a generalized strong
  bundle isomorphism (Proposition 10.4.6 for both legs).
* **`GenSBMap.theorem_12_5_7_two_orbitMap_unique_of_isLRLocal`**: Theorem 12.5.7 (2) with Part
  I's hypotheses and the local regularity property on `W`: an orientation `o` of `f` has exactly
  one orientation `o'` of `f' = 𝔄_* f` corresponding to `o` over every diagram of **every**
  generalized strong bundle isomorphism `𝔄'` with `|𝔄'| = |𝔄|` and `𝔄'_* f = f'`.  No
  effectiveness is assumed.
* **`OrientationRep.exists_unique_transport_of_isLRLocal`**: for an orientation `R` of `s` on
  `R.a` and a representative `b`, exactly one orientation of `F_b` corresponds to `R.o` over
  every diagram of every `𝔄` with `Γ_b ∘ |𝔄| = Γ_a` and `𝔄_* F_a = F_b`.
* `OrientationRep.exists_unique_transport_of_isLRLocal_polyfold`: the same with tameness and
  bump functions read on the polyfold (Definitions 16.3.5 (1), 16.1.5 (1)).

Witness (namespace `Polyfold.HalfSpaceBundle`): `isLRLocal_halfSEP`, the local regularity
property of `H × ℝᵏ → H` over the half-space `H = [0, ∞) × ℝᵐ` (`∂H ≠ ∅`, non-zero fibres; the
other hypotheses are in `orbitMap_unique_hypotheses_halfSEP`).  The property also holds in a
case where the base is not effective and `𝔄` is not unique
(`LocalizationLRBundleBaseExamples.isLRLocal_z3EpBundle`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open SEP EpStrongBundle EpStrongBundle.IsStrongBundleEquivalence

variable {A A' : SEP.{u}}

namespace GenSBMap

variable {𝔄 : GenSBMap A A'} (h𝔄 : 𝔄.IsGeneralizedIso)

include h𝔄 in
/-- **The local regularity property passes along a generalized strong bundle isomorphism**
(Proposition 10.4.6 for both legs of a representative). -/
theorem isLRLocal_iff_of_isGeneralizedIso : A.E.IsLRLocal ↔ A'.E.IsLRLocal :=
  (EpStrongBundle.proposition_10_4_6 (rep h𝔄).hΦ).symm.trans
    (EpStrongBundle.proposition_10_4_6 (sbe (isEquivalence_rep_Ψ h𝔄)))

variable {f : A.Obj → A.W} {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hf' : f' = pushforward h𝔄 f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)
  (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
  (hfT : A.B.IsScFredholmSectionTame f)

include hf' hX hbump hfT in
/-- **Theorem 12.5.7 (2): the push-forward orientation depends only on `|𝔄|`**, p. 595 (2017:
Theorem 12.12 (2)), for a strong bundle with the local regularity property (Definition 8.4.2 as
`IsLRLocal`) and no effectiveness: an orientation `o` of `f` has exactly one family `o'` which
is an orientation of `f'` and corresponds to `o` over the middle of every diagram representing
**any** generalized strong bundle isomorphism `𝔄'` with `|𝔄'| = |𝔄|` and `𝔄'_* f = f'`. -/
theorem theorem_12_5_7_two_orbitMap_unique_of_isLRLocal (hLR : A.E.IsLRLocal)
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
  have hLR' : A'.E.IsLRLocal := (isLRLocal_iff_of_isGeneralizedIso h𝔄).1 hLR
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
  exact theorem_12_5_7_two_corr_indep_of_orbitMap_eq h𝔄 h𝔄' hF hF' hf' hf'' hsec hsec'
    horb.symm hLR' (cls_rep h𝔄) hD ho.2 (ho' t₀ ht₀).2 (hc (rep h𝔄) (cls_rep h𝔄)) v hv

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
on `W_a` and the local regularity property of `W_a` (Definition 8.4.2 as `IsLRLocal`), and `b`
another representative.  There is exactly one orientation `o'` of `F_b` (Definition 12.5.4, for
every topology of Theorem 12.5.3) corresponding to `R.o` over the middle of every diagram
representing **any** generalized strong bundle isomorphism `𝔄 : W_a → W_b` with
`Γ_b ∘ |𝔄| = Γ_a` and `𝔄_* F_a = F_b`.  The base need not be effective. -/
theorem exists_unique_transport_of_isLRLocal (R : OrientationRep s) (b : SectionRep c)
    (hb : ⟦b⟧ = s.1) (hX : R.a.S.A.X.PObj.IsTame) (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hfT : R.a.S.A.B.IsScFredholmSectionTame R.a.F) (hLR : R.a.S.A.E.IsLRLocal) :
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
  obtain ⟨o', ⟨ho', hc⟩, huniq⟩ := GenSBMap.theorem_12_5_7_two_orbitMap_unique_of_isLRLocal
    h𝔄₀ R.hF hFb hpush₀.symm R.hsec hsec' hX hbump hfT hLR R.isOrientationTopology
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
(Definition 16.1.5 (1)), `W_a` has the local regularity property (Definition 8.4.2 as
`IsLRLocal`) and `F_a` has tame germ data, the conclusion of
`exists_unique_transport_of_isLRLocal` holds for every representative `b`. -/
theorem exists_unique_transport_of_isLRLocal_polyfold (R : OrientationRep s) (b : SectionRep c)
    (hb : ⟦b⟧ = s.1) (hc : c.IsTame) (hbump : c.polyfold.AdmitsBumpFunctions)
    (hfT : R.a.S.A.B.IsScFredholmSectionTame R.a.F) (hLR : R.a.S.A.E.IsLRLocal) :
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
  exact R.exists_unique_transport_of_isLRLocal b hb ((c.isTame_iff).1 hc R.a.S R.a.hS)
    ((c.polyfold.definition_16_1_5_one).1 hbump _ hq) hfT hLR

end OrientationRep

end StrongPolyfoldBundle

/-! ### Witness: the half-space bundle -/

namespace HalfSpaceBundle

/-- **The half-space bundle `H × ℝᵏ → H` over the trivial ep-groupoid of `H = [0, ∞) × ℝᵐ` has
the local regularity property** (Definition 8.4.2 as `IsLRLocal`): its orbits are points. -/
theorem isLRLocal_halfSEP (m k : ℕ) : (halfSEP m k).E.IsLRLocal :=
  EpStrongBundle.isLRLocal_trivial _

end HalfSpaceBundle

end Polyfold
