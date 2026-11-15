import Polyfold.Chapter16.OrientationTransport
import Polyfold.Chapter12.OrientationGeneralizedIsoUnique

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §16.6,
**Definition 16.6.5** (p. 739; 2017: Definition 16.42): orientations of an sc-Fredholm section of
a strong polyfold bundle, and the passage from one representative to another.

# Orientations of the representatives of an sc-Fredholm section

## The text, paraphrased

(Definition 16.6.5) An sc-Fredholm section `f` of a strong polyfold bundle is orientable if a
representative `F` is orientable in the sense of Definition 12.5.4; an orientation of one
representative determines orientations of all others, by Theorem 12.5.7.

## What is formalized (namespace `Polyfold.StrongPolyfoldBundle.OrientationRep`)

For an orientation `R` of `s` on the representative `R.a` and another representative `b` of `s`,
with Part I's hypotheses (tame, bump functions, tame sc-Fredholm germs) on `W_a` and `W_b` only:

* **`exists_unique_transport`**: for the generalized strong bundle isomorphism `𝔄 : W_a → W_b`
  of the relation of representatives (`Γ_b ∘ |𝔄| = Γ_a`, `𝔄_* F_a = F_b`), there is exactly one
  orientation `o'` of `F_b` (Definition 12.5.4, for every topology of Theorem 12.5.3) which
  corresponds to `R.o` over the middle bundle of **every** diagram `W_a ← W'' → W_b` representing
  `𝔄`.  So the transported orientation does not depend on the diagram.
* **`transport`**: an orientation of `s` on `b`.

Both are Theorem 12.5.7 (2) for a class of diagrams
(`GenSBMap.theorem_12_5_7_two_cls_unique`), read for the representatives of `s`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

open EPLocalization

namespace StrongPolyfoldBundle

open SBLocalization StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

namespace OrientationRep

variable {s : FredholmSection c}

/-- **2021 Definition 16.6.5, p. 739 (2017: Definition 16.42): the orientation of one
representative determines one of every other representative, independently of the diagram.**
Let `R` be an orientation of `s` on `R.a` and `b` a representative of `s`, with Part I's
hypotheses on `W_a` and `W_b`.  For the generalized strong bundle isomorphism `𝔄 : W_a → W_b` of
the relation of representatives there is exactly one family `o'_x ∈ Or_x^{F_b}` which is an
orientation of `F_b` (Definition 12.5.4) for every topology with the properties of
Theorem 12.5.3 and corresponds to `R.o` over the middle bundle of every diagram representing
`𝔄`. -/
theorem exists_unique_transport (R : OrientationRep s) (b : SectionRep c) (hb : ⟦b⟧ = s.1)
    (hX : R.a.S.A.X.PObj.IsTame) (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hfT : R.a.S.A.B.IsScFredholmSectionTame R.a.F)
    (hX' : b.S.A.X.PObj.IsTame) (hbump' : b.S.A.X.PObj.AdmitsBumpFunctions)
    (hfT' : b.S.A.B.IsScFredholmSectionTame b.F) :
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
  have := paracompactSpace_rn_prod R.a.S.A.X.PObj
  have := paracompactSpace_rn_pullback R.a.S.A.B
  have := paracompactSpace_rn_rn_prod R.a.S.A.X.PObj
  have := paracompactSpace_rn_rn_pullback R.a.S.A.B
  have := paracompactSpace_rn_prod b.S.A.X.PObj
  have := paracompactSpace_rn_pullback b.S.A.B
  have := paracompactSpace_rn_rn_prod b.S.A.X.PObj
  have := paracompactSpace_rn_rn_pullback b.S.A.B
  obtain ⟨-, 𝔄, h𝔄, hΓ, hpush⟩ := (Quotient.exact (R.ha.trans hb.symm) : SectionRep.Rel R.a b)
  have hFb : b.S.A.E.IsScFredholmSectionFunctor b.F := (ScSection.isFredholm_iff s.1).1 s.2 b hb
  have hsec' : b.S.A.B.HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump'
  have ht := eq_orTopology_of hX hbump hfT R.hsec R.isOrientationTopology.isLocalHomeomorph
    R.isOrientationTopology.propagation
  have ho : R.a.S.A.E.definition_12_5_4 R.hF R.hsec
      (orTopology (orLocalTransport hX hbump hfT R.hsec)) R.o := ht ▸ R.isOrientation
  have htop : ∀ t' : TopologicalSpace (OrSpace b.F hFb.2), IsOrientationTopology b.F hFb.2 t' →
      t' = orTopology (orLocalTransport hX' hbump' hfT' hsec') := fun t' ht' =>
    eq_orTopology_of hX' hbump' hfT' hsec' ht'.isLocalHomeomorph ht'.propagation
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 hX' hbump' hfT').exists
  have ht₀' : IsOrientationTopology b.F hFb.2
      (orTopology (orLocalTransport hX' hbump' hfT' hsec')) := htop t₀ ht₀ ▸ ht₀
  obtain ⟨o', ⟨ho', hc⟩, huniq⟩ := GenSBMap.theorem_12_5_7_two_cls_unique h𝔄 R.hF hFb hpush.symm
    R.hsec hsec' hX hbump hfT hX' hbump' hfT' ho
  refine ⟨𝔄, h𝔄, hΓ, hpush.symm, hFb, hsec', o', ⟨fun t' ht' => ?_, hc⟩,
    fun o'' ⟨ho'', hc''⟩ => huniq o'' ⟨ho'' _ ht₀', hc''⟩⟩
  rw [htop t' ht']
  exact ho'

/-- **2021 Definition 16.6.5, p. 739 (2017: Definition 16.42): an orientation of one
representative gives an orientation of every other representative**, with Part I's hypotheses on
the two representatives only. -/
theorem transport (R : OrientationRep s) (b : SectionRep c) (hb : ⟦b⟧ = s.1)
    (hX : R.a.S.A.X.PObj.IsTame) (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hfT : R.a.S.A.B.IsScFredholmSectionTame R.a.F)
    (hX' : b.S.A.X.PObj.IsTame) (hbump' : b.S.A.X.PObj.AdmitsBumpFunctions)
    (hfT' : b.S.A.B.IsScFredholmSectionTame b.F) : ∃ R' : OrientationRep s, R'.a = b := by
  obtain ⟨-, -, -, -, hFb, hsec', o', ⟨ho', -⟩, -⟩ :=
    R.exists_unique_transport b hb hX hbump hfT hX' hbump' hfT'
  have := paracompactSpace_rn_prod b.S.A.X.PObj
  have := paracompactSpace_rn_pullback b.S.A.B
  have := paracompactSpace_rn_rn_prod b.S.A.X.PObj
  have := paracompactSpace_rn_rn_pullback b.S.A.B
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 hX' hbump' hfT').exists
  exact ⟨⟨b, hb, hFb, hsec', t₀, ht₀, o', ho' t₀ ht₀⟩, rfl⟩

end OrientationRep

end StrongPolyfoldBundle

end Polyfold
