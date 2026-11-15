import Polyfold.Chapter16.OrientationRepresentatives
import Polyfold.Chapter16.PolyfoldBump
import Polyfold.Chapter16.PolyfoldMaps
import Polyfold.Chapter10.LocalizationLREffectiveBundle
import Polyfold.Chapter15.HalfSpaceBoundaryWeightWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §16.6,
**Definition 16.6.5** (p. 739; 2017: Definition 16.42) with **Theorem 12.5.7 (2)** (p. 595;
2017: Theorem 12.12 (2)): the orientation of one representative of an sc-Fredholm section
determines the orientations of all others.

# The transported orientation: hypotheses on one side, and independence of `𝔄`

## The text, paraphrased

(Definition 16.6.5) An orientation of one representative `(W, F)` of `f` determines orientations
of all other representatives, by Theorem 12.5.7: for `(W', F')` the push-forward along the
generalized strong bundle isomorphism `𝔄 : W → W'` with `Γ' ∘ |𝔄| = Γ` and `𝔄_* F = F'`.

## What is formalized

Along a generalized strong bundle isomorphism `𝔄 : W → W'` (namespace
`Polyfold.SBLocalization.GenSBMap`):

* `isTame_iff_of_isGeneralizedIso`, `admitsBumpFunctions_iff_of_isGeneralizedIso`,
  `isEffective_base_iff_of_isGeneralizedIso`: tameness, sc-smooth bump functions and
  effectiveness of the base pass between `W` and `W'` (through the middle bundle of a diagram,
  Proposition 16.1.4 (1), the invariance of tameness and of effectiveness under equivalences);
  `isScFredholmSectionTame_pushforward`: tame germ data of `F` pass to `𝔄_* F` (Theorem 10.4.5,
  pull-back and push-forward).
* **`theorem_12_5_7_two_cls_unique_left`**: Theorem 12.5.7 (2) for the class with Part I's
  hypotheses (tame, bump functions, tame germ data) on `W` only.
* **`theorem_12_5_7_two_orbitMap_unique`**: if the base of `W` is effective, the push-forward
  orientation is the same for **every** generalized strong bundle isomorphism `𝔄'` with
  `|𝔄'| = |𝔄|` (by Theorem 10.5.7 for an effective base, `𝔄' = 𝔄`).

For the representatives of an sc-Fredholm section (namespace
`Polyfold.StrongPolyfoldBundle.OrientationRep`):

* **`exists_unique_transport_left`**, **`transport_left`**: Definition 16.6.5 with Part I's
  hypotheses on the representative `R.a` carrying the orientation only.
* **`exists_unique_transport_of_isEffective`**: for an effective base, exactly one orientation of
  `F_b` corresponds to `R.o` over every diagram of every `𝔄` with `Γ_b ∘ |𝔄| = Γ_a` and
  `𝔄_* F_a = F_b`: the transported orientation does not depend on `𝔄`.
* **`exists_unique_transport_of_polyfold`**: the same with the hypotheses read on the polyfold
  (tame, sc-smooth bump functions, effective; Definitions 16.1.5, 16.1.20, 16.3.5) and tame germ
  data of `F_a`.

Witness (namespace `Polyfold.HalfSpaceBundle`): `orbitMap_unique_hypotheses_halfSEP`, every
hypothesis of `theorem_12_5_7_two_orbitMap_unique` on `H × ℝᵏ → H` over the trivial ep-groupoid
of the half-space `H = [0, ∞) × ℝᵐ`, `𝔄 = [1]`, `F` the graph section of a `C^∞` map, with
`∂H ≠ ∅` and non-zero fibres; the orientation itself is the datum of the theorem.

## Non-effective bases

For a non-effective base two generalized isomorphisms with the same `|𝔄|` can differ (the
counterexample `StrongPolyfoldBundleStructure.not_uniqueness_16_3_3`); their push-forward
orientations agree by the local regularity property: `exists_unique_transport_of_isLRLocal`
(`OrientationOrbitMapIndependence`), `exists_unique_transport_of_isLR`
(`OrientationTransportRegularity`).
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
/-- **Tameness passes along a generalized strong bundle isomorphism**: through the middle bundle
`W''` of a representative, both legs being equivalences on the bases. -/
theorem isTame_iff_of_isGeneralizedIso : A.X.PObj.IsTame ↔ A'.X.PObj.IsTame :=
  ((rep h𝔄).hΦ.isEquivalence_base.isTame_iff).symm.trans
    (sbe (isEquivalence_rep_Ψ h𝔄)).isEquivalence_base.isTame_iff

include h𝔄 in
/-- **Sc-smooth bump functions pass along a generalized strong bundle isomorphism** (the proof
of Proposition 16.1.4 (1) for the bases). -/
theorem admitsBumpFunctions_iff_of_isGeneralizedIso :
    A.X.PObj.AdmitsBumpFunctions ↔ A'.X.PObj.AdmitsBumpFunctions :=
  ((rep h𝔄).hΦ.isEquivalence_base.admitsBumpFunctions_iff).symm.trans
    (sbe (isEquivalence_rep_Ψ h𝔄)).isEquivalence_base.admitsBumpFunctions_iff

include h𝔄 in
/-- **Effectiveness of the base passes along a generalized strong bundle isomorphism**
(Remark 10.1.12 for both legs). -/
theorem isEffective_base_iff_of_isGeneralizedIso : A.X.IsEffective ↔ A'.X.IsEffective :=
  ((EpFunctor.IsEquivalence.isEffective_iff (A := (rep h𝔄).B.baseEP) (B := A.baseEP)
      (rep h𝔄).hΦ.isEquivalence_base).symm).trans
    (EpFunctor.IsEquivalence.isEffective_iff (A := (rep h𝔄).B.baseEP) (B := A'.baseEP)
      (sbe (isEquivalence_rep_Ψ h𝔄)).isEquivalence_base)

/-- **Tame germ data pass to `𝔄_* F`** (Definition 3.6.4): `𝔄_* F = Ψ_* Φ^* F`, and `Φ^*`,
`Ψ_*` keep tame germ data (Theorem 10.4.5). -/
theorem isScFredholmSectionTame_pushforward {f : A.Obj → A.W}
    (hF : A.E.IsScFredholmSectionFunctor f) (hfT : A.B.IsScFredholmSectionTame f) :
    A'.B.IsScFredholmSectionTame (pushforward h𝔄 f) := by
  have hF'' : (rep h𝔄).B.E.IsScFredholmSectionFunctor ((rep h𝔄).hΦ.pullback f) :=
    (EpStrongBundle.theorem_10_4_5_fred (rep h𝔄).hΦ).2.1 hF
  exact (sbe (isEquivalence_rep_Ψ h𝔄)).isScFredholmSectionTame_pushforward hF''.1
    ((rep h𝔄).hΦ.isScFredholmSectionTame_pullback hfT)

variable {f : A.Obj → A.W} {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hf' : f' = pushforward h𝔄 f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)
  (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
  (hfT : A.B.IsScFredholmSectionTame f)

include hX hbump hfT in
/-- **Theorem 12.5.7 (2) for the class, with Part I's hypotheses on `W` only**, p. 595 (2017:
Theorem 12.12 (2)): an orientation `o` of `f` (Definition 12.5.4 for a topology with the
properties of Theorem 12.5.3) has exactly one family `o'` which is an orientation of
`f' = 𝔄_* f` for every such topology and corresponds to `o` over the middle of every diagram
representing `𝔄`.  Tameness, bump functions and tame germ data of `f'` follow from those of `f`. -/
theorem theorem_12_5_7_two_cls_unique_left {t : TopologicalSpace (OrSpace f hF.2)}
    {o : ∀ a (hs : a ∈ A.X.PObj.smoothSet), Orx f hF.2 a hs} :
    haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    IsOrientationTopology f hF.2 t → A.E.definition_12_5_4 hF hsec t o →
    ∃! o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs,
      (∀ t' : TopologicalSpace (OrSpace f' hF'.2),
        (haveI := paracompactSpace_rn_prod A'.X.PObj
         haveI := paracompactSpace_rn_pullback A'.B
         IsOrientationTopology f' hF'.2 t') → A'.E.definition_12_5_4 hF' hsec' t' o') ∧
        ∀ (D : SDiagram A A') (hD : D.cls = 𝔄) v (hv : v ∈ D.B.X.PObj.smoothSet),
          (sbe (equivalences_Ψ_of_cls h𝔄 hD)).orEqv (D.isScFredholm_pullback hF) hF'
              (pullback_eq_of_cls' h𝔄 hD hF.1 hf') (D.hasScPlusSectionsThrough_B hsec) hsec' v hv
              (o' (D.Ψ.ϕ.obj v) ((sbe (equivalences_Ψ_of_cls h𝔄 hD)).smooth_obj hv)) =
            D.hΦ.orEqv (D.isScFredholm_pullback hF) hF rfl (D.hasScPlusSectionsThrough_B hsec)
              hsec v hv (o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) := by
  intro ht ho
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_rn_prod A.X.PObj
  have := paracompactSpace_rn_rn_pullback A.B
  have := paracompactSpace_rn_prod A'.X.PObj
  have := paracompactSpace_rn_pullback A'.B
  have := paracompactSpace_rn_rn_prod A'.X.PObj
  have := paracompactSpace_rn_rn_pullback A'.B
  have hX' : A'.X.PObj.IsTame := (isTame_iff_of_isGeneralizedIso h𝔄).1 hX
  have hbump' : A'.X.PObj.AdmitsBumpFunctions :=
    (admitsBumpFunctions_iff_of_isGeneralizedIso h𝔄).1 hbump
  have hfT' : A'.B.IsScFredholmSectionTame f' := by
    rw [hf']; exact GenSBMap.isScFredholmSectionTame_pushforward h𝔄 hF hfT
  have heq := eq_orTopology_of hX hbump hfT hsec ht.isLocalHomeomorph ht.propagation
  have ho₀ : A.E.definition_12_5_4 hF hsec
      (orTopology (orLocalTransport hX hbump hfT hsec)) o := heq ▸ ho
  have htop : ∀ t' : TopologicalSpace (OrSpace f' hF'.2), IsOrientationTopology f' hF'.2 t' →
      t' = orTopology (orLocalTransport hX' hbump' hfT' hsec') := fun t' ht' =>
    eq_orTopology_of hX' hbump' hfT' hsec' ht'.isLocalHomeomorph ht'.propagation
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 hX' hbump' hfT').exists
  have ht₀' : IsOrientationTopology f' hF'.2
      (orTopology (orLocalTransport hX' hbump' hfT' hsec')) := htop t₀ ht₀ ▸ ht₀
  obtain ⟨o', ⟨ho', hc⟩, huniq⟩ := theorem_12_5_7_two_cls_unique h𝔄 hF hF' hf' hsec hsec'
    hX hbump hfT hX' hbump' hfT' ho₀
  refine ⟨o', ⟨fun t' ht' => ?_, hc⟩, fun o'' ⟨ho'', hc''⟩ => huniq o'' ⟨ho'' _ ht₀', hc''⟩⟩
  rw [htop t' ht']
  exact ho'

include hf' hX hbump hfT in
/-- **Theorem 12.5.7 (2): the push-forward orientation depends only on `|𝔄|`, for an effective
base**, p. 595 (2017: Theorem 12.12 (2)).  With the local regularity properties of the text
(Definition 8.4.2 for `W`, `W'`; (LR) of Definition 7.4.19 for the base of `W`) and an effective
base of `W`: an orientation `o` of `f` has exactly one family `o'` which is an orientation of `f'`
and corresponds to `o` over the middle of every diagram representing **any** generalized strong
bundle isomorphism `𝔄'` with `|𝔄'| = |𝔄|` and `𝔄'_* f = f'`.  (Theorem 10.5.7 for an effective
base gives `𝔄' = 𝔄`.) -/
theorem theorem_12_5_7_two_orbitMap_unique (hLR : A.E.IsLR) (hLR' : A'.E.IsLR)
    (hXLR : A.X.IsLR) (hEff : A.X.IsEffective) {t : TopologicalSpace (OrSpace f hF.2)}
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
  have hEff' : A'.X.IsEffective := (isEffective_base_iff_of_isGeneralizedIso h𝔄).1 hEff
  obtain ⟨o', ⟨ho', hc⟩, huniq⟩ := theorem_12_5_7_two_cls_unique_left h𝔄 hF hF' hf' hsec hsec'
    hX hbump hfT ht ho
  refine ⟨o', ⟨ho', fun 𝔄' h𝔄' horb hf'' D hD v hv => ?_⟩,
    fun o'' ⟨ho'', hc''⟩ => huniq o'' ⟨ho'', hc'' 𝔄 h𝔄 rfl hf'⟩⟩
  obtain rfl : 𝔄' = 𝔄 :=
    theorem_10_5_7_of_isEffective hLR hLR' (Or.inl hXLR) hEff' h𝔄' h𝔄 horb
  exact hc D hD v hv

end GenSBMap

end SBLocalization

namespace StrongPolyfoldBundle

open SBLocalization StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

namespace OrientationRep

variable {s : FredholmSection c}

/-- **2021 Definition 16.6.5, p. 739 (2017: Definition 16.42), with Part I's hypotheses on the
oriented representative only**: for an orientation `R` of `s` on `R.a` (tame, bump functions,
tame germ data) and a representative `b`, the generalized strong bundle isomorphism `𝔄` of the
relation of representatives carries exactly one orientation `o'` of `F_b` corresponding to
`R.o` over every diagram representing `𝔄`. -/
theorem exists_unique_transport_left (R : OrientationRep s) (b : SectionRep c) (hb : ⟦b⟧ = s.1)
    (hX : R.a.S.A.X.PObj.IsTame) (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hfT : R.a.S.A.B.IsScFredholmSectionTame R.a.F) :
    ∃ (𝔄 : GenSBMap R.a.S.A b.S.A) (h𝔄 : 𝔄.IsGeneralizedIso)
      (_ : ⇑b.S.Γ ∘ 𝔄.orbitMap = ⇑R.a.S.Γ) (hpush : b.F = GenSBMap.pushforward h𝔄 R.a.F)
      (hFb : b.S.A.E.IsScFredholmSectionFunctor b.F) (hsec' : b.S.A.B.HasScPlusSectionsThrough),
      ∃! o' : ∀ x (hs : x ∈ b.S.A.X.PObj.smoothSet), Orx b.F hFb.2 x hs,
        (∀ t' : TopologicalSpace (OrSpace b.F hFb.2),
          (haveI := paracompactSpace_rn_prod b.S.A.X.PObj
           haveI := paracompactSpace_rn_pullback b.S.A.B
           IsOrientationTopology b.F hFb.2 t') → b.S.A.E.definition_12_5_4 hFb hsec' t' o') ∧
        ∀ (D : SDiagram R.a.S.A b.S.A) (hD : D.cls = 𝔄) v (hv : v ∈ D.B.X.PObj.smoothSet),
          (sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).orEqv (D.isScFredholm_pullback R.hF) hFb
              (GenSBMap.pullback_eq_of_cls' h𝔄 hD R.hF.1 hpush)
              (D.hasScPlusSectionsThrough_B R.hsec) hsec' v hv
              (o' (D.Ψ.ϕ.obj v) ((sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).smooth_obj hv)) =
            D.hΦ.orEqv (D.isScFredholm_pullback R.hF) R.hF rfl
              (D.hasScPlusSectionsThrough_B R.hsec) R.hsec v hv
              (R.o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) := by
  obtain ⟨-, 𝔄, h𝔄, -, hpush⟩ := (Quotient.exact (R.ha.trans hb.symm) : SectionRep.Rel R.a b)
  have hX' : b.S.A.X.PObj.IsTame := (GenSBMap.isTame_iff_of_isGeneralizedIso h𝔄).1 hX
  have hbump' : b.S.A.X.PObj.AdmitsBumpFunctions :=
    (GenSBMap.admitsBumpFunctions_iff_of_isGeneralizedIso h𝔄).1 hbump
  have hfT' : b.S.A.B.IsScFredholmSectionTame b.F := by
    rw [← hpush]; exact GenSBMap.isScFredholmSectionTame_pushforward h𝔄 R.hF hfT
  exact R.exists_unique_transport b hb hX hbump hfT hX' hbump' hfT'

/-- **2021 Definition 16.6.5, p. 739: an orientation of one representative gives an orientation
of every other representative**, with Part I's hypotheses on the oriented representative only. -/
theorem transport_left (R : OrientationRep s) (b : SectionRep c) (hb : ⟦b⟧ = s.1)
    (hX : R.a.S.A.X.PObj.IsTame) (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hfT : R.a.S.A.B.IsScFredholmSectionTame R.a.F) : ∃ R' : OrientationRep s, R'.a = b := by
  obtain ⟨-, 𝔄, h𝔄, -, hpush⟩ := (Quotient.exact (R.ha.trans hb.symm) : SectionRep.Rel R.a b)
  have hX' : b.S.A.X.PObj.IsTame := (GenSBMap.isTame_iff_of_isGeneralizedIso h𝔄).1 hX
  have hbump' : b.S.A.X.PObj.AdmitsBumpFunctions :=
    (GenSBMap.admitsBumpFunctions_iff_of_isGeneralizedIso h𝔄).1 hbump
  have hfT' : b.S.A.B.IsScFredholmSectionTame b.F := by
    rw [← hpush]; exact GenSBMap.isScFredholmSectionTame_pushforward h𝔄 R.hF hfT
  exact R.transport b hb hX hbump hfT hX' hbump' hfT'

/-- **2021 Definition 16.6.5, p. 739: the transported orientation does not depend on the
generalized isomorphism, for an effective base.**  Let `R` be an orientation of `s` on `R.a`
with Part I's hypotheses on `W_a`, whose base is effective, and `b` another representative.
There is exactly one orientation `o'` of `F_b` (Definition 12.5.4, for every topology of
Theorem 12.5.3) corresponding to `R.o` over the middle of every diagram representing **any**
generalized strong bundle isomorphism `𝔄 : W_a → W_b` with `Γ_b ∘ |𝔄| = Γ_a` and
`𝔄_* F_a = F_b`. -/
theorem exists_unique_transport_of_isEffective (R : OrientationRep s) (b : SectionRep c)
    (hb : ⟦b⟧ = s.1) (hX : R.a.S.A.X.PObj.IsTame) (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hfT : R.a.S.A.B.IsScFredholmSectionTame R.a.F) (hEff : R.a.S.A.X.IsEffective) :
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
  obtain ⟨𝔄₀, h𝔄₀, hΓ₀, hpush₀, hFb, hsec', o', ⟨ho', hc⟩, huniq⟩ :=
    R.exists_unique_transport_left b hb hX hbump hfT
  have hEff' : b.S.A.X.IsEffective := (GenSBMap.isEffective_base_iff_of_isGeneralizedIso h𝔄₀).1 hEff
  have hXLR : R.a.S.A.X.IsLR := R.a.S.A.X.proposition_7_4_22_of_isZhou R.a.S.isZhou
  refine ⟨hFb, hsec', o', ⟨ho', fun 𝔄 h𝔄 hΓ hpush D hD v hv => ?_⟩,
    fun o'' ⟨ho'', hc''⟩ => huniq o'' ⟨ho'', hc'' 𝔄₀ h𝔄₀ hΓ₀ hpush₀⟩⟩
  have horb : 𝔄.orbitMap = 𝔄₀.orbitMap := by
    funext q
    exact b.S.Γ.injective ((congrFun hΓ q).trans (congrFun hΓ₀ q).symm)
  obtain rfl : 𝔄 = 𝔄₀ :=
    theorem_10_5_7_of_isEffective R.a.S.isLR b.S.isLR (Or.inl hXLR) hEff' h𝔄 h𝔄₀ horb
  exact hc D hD v hv

/-- **Definition 16.6.5 with the hypotheses read on the polyfold**: if the strong polyfold
bundle is tame (Definition 16.3.5 (1)), its polyfold admits sc-smooth bump functions
(Definition 16.1.5 (1)) and is effective, and `F_a` has tame germ data, the conclusion of
`exists_unique_transport_of_isEffective` holds for every representative `b`. -/
theorem exists_unique_transport_of_polyfold (R : OrientationRep s) (b : SectionRep c)
    (hb : ⟦b⟧ = s.1) (hc : c.IsTame) (hbump : c.polyfold.AdmitsBumpFunctions)
    (hEff : c.polyfold.IsEffective) (hfT : R.a.S.A.B.IsScFredholmSectionTame R.a.F) :
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
  exact R.exists_unique_transport_of_isEffective b hb ((c.isTame_iff).1 hc R.a.S R.a.hS)
    ((c.polyfold.definition_16_1_5_one).1 hbump _ hq) hfT
    ((c.polyfold.isEffective_iff).1 hEff _ hq)

end OrientationRep

end StrongPolyfoldBundle

/-! ### Witness: the half-space bundle, with boundary and non-zero fibres -/

namespace HalfSpaceBundle

open SBLocalization LocalizationLREffectiveBundleExamples
open scoped ContDiff

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

/-- **Every hypothesis of `GenSBMap.theorem_12_5_7_two_orbitMap_unique` holds in an example
with `∂X ≠ ∅` and non-zero fibres**: `W = W' = H × ℝᵏ → H` over the trivial ep-groupoid of the
half-space `H = [0, ∞) × ℝᵐ` (`halfSEP m k`, `k ≥ 1`), `𝔄 = [1_W]`, `f = f'` the graph section of
a `C^∞` map `φ`.  The bundle has the local regularity property, the base has (LR) and is
effective, `H` is tame and admits sc-smooth bump functions, `f` is an sc-Fredholm section functor
with tame germ data, `𝔄_* f = f`, and a topology with the properties of Theorem 12.5.3 exists on
`O_f`.  (The orientation `o` is the datum the theorem transports.) -/
theorem orbitMap_unique_hypotheses_halfSEP [NeZero k] (hφ : ContDiff ℝ ∞ φ) :
    (halfSEP m k).X.PObj.boundary.Nonempty ∧
    (∀ y : (halfSEP m k).Obj, Nontrivial ((halfSEP m k).P ⁻¹' {y})) ∧
    (halfSEP m k).E.IsLR ∧ (halfSEP m k).X.IsLR ∧ (halfSEP m k).X.IsEffective ∧
    (halfSEP m k).X.PObj.IsTame ∧ (halfSEP m k).X.PObj.AdmitsBumpFunctions ∧
    (halfSEP m k).B.HasScPlusSectionsThrough ∧
    (halfSEP m k).E.IsScFredholmSectionFunctor (graphSection φ) ∧
    (halfSEP m k).B.IsScFredholmSectionTame (graphSection φ) ∧
    ∃ h𝔄 : (SDiagram.id (halfSEP m k)).cls.IsGeneralizedIso,
      graphSection φ = GenSBMap.pushforward h𝔄 (graphSection φ) ∧
      ∃ t : TopologicalSpace (OrSpace (B := (halfSEP m k).B) (graphSection φ)
          (isScFredholmSectionFunctor_graphSection_halfSEP hφ).2),
        haveI := paracompactSpace_rn_prod (halfSEP m k).X.PObj
        haveI := paracompactSpace_rn_pullback (halfSEP m k).B
        IsOrientationTopology (B := (halfSEP m k).B) (graphSection φ)
          (isScFredholmSectionFunctor_graphSection_halfSEP hφ).2 t := by
  have hF := isScFredholmSectionFunctor_graphSection_halfSEP (m := m) (k := k) hφ
  have hfT := isScFredholmSectionTame_graphSection_halfSEP (m := m) (k := k) hφ
  have hX : (halfSEP m k).X.PObj.IsTame := isTame_halfSEP m k
  have hbump : (halfSEP m k).X.PObj.AdmitsBumpFunctions :=
    (admitsScPartitionsOfUnity_halfSEP m k).admitsBumpFunctions
  have h𝔄 : (SDiagram.id (halfSEP m k)).cls.IsGeneralizedIso :=
    ⟨SDiagram.id _, rfl, SEP.equivalences.id_mem _⟩
  have hpush : graphSection φ = GenSBMap.pushforward h𝔄 (graphSection φ) :=
    ((GenSBMap.pushforward_eq h𝔄 rfl (SEP.equivalences.id_mem _) hF.1).trans
      (SDiagram.pushforward_id _ hF.1)).symm
  have := paracompactSpace_rn_prod (halfSEP m k).X.PObj
  have := paracompactSpace_rn_pullback (halfSEP m k).B
  have := paracompactSpace_rn_rn_prod (halfSEP m k).X.PObj
  have := paracompactSpace_rn_rn_pullback (halfSEP m k).B
  have h617 := (theorem_6_6_17 hX hbump hfT).exists
  exact ⟨⟨_, zero_mem_boundary_halfSEP m k⟩, nontrivial_fibre_halfSEP m k,
    EpStrongBundle.isLR_trivial _, isLR_trivial _, EpGroupoid.isEffective_trivial _, hX, hbump,
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump, hF, hfT, h𝔄, hpush,
    h617⟩

end HalfSpaceBundle

end Polyfold
