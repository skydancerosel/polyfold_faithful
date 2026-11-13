import Polyfold.Chapter12.P3W6O6_ContOr
import Polyfold.Chapter12.P3W5OR_EquivCont
import Polyfold.Chapter16.P3W4PB_FredholmSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Definition 16.6.5** (2017: Definition 16.42), orientations of sc-Fredholm sections of strong
polyfold bundles: the orientation chosen on one representative `(W, F)` carries over to every
other representative, by Theorem 12.5.7 (gap PB-4 of the wave-4 note of block PB).

# Transport of an orientation to another representative

## What is formalized

* **`SDiagram.orientation_transport_hyp`** (a diagram `W ←Φ W'' →Ψ W'` of strong bundle
  equivalences, `F' = [D]_* F = Ψ_* Φ^* F`): an orientation of `F` in the sense of Definition
  12.5.4 (for any topology on `O_F` with the properties of Theorem 6.6.17) has exactly one
  invariant transport `o'` to `F'` compatible over `W''`, and `o'` is an orientation of `F'` in the
  sense of Definition 12.5.4 for **every** topology on `O_{F'}` with the properties of Theorem
  6.6.17.  From OR's `theorem_12_5_7_two_cont` and `isContOrOn_univ_iff_continuous`
  (`Chapter12/P3W6O6_ContOr`, the two readings of "continuous" agree).
* **`OrientationRep.transport_hyp`** (Definition 16.6.5): for an orientation `R` of the
  sc-Fredholm section `s` on the representative `R.a` and any other representative `b` of `s`, a
  diagram `D` with `[D]_* F = F_b` gives an orientation `R'` of `s` on `b`, with the transported
  orientation of `D` above.  Such a `D` exists for every `b` (`exists_diagram`, from the relation of
  representatives).

## Hypotheses (Part I's standing hypotheses of §12.5)

Tameness, sc-smooth bump functions and tame sc-Fredholm germs on `W`, `W'` and the middle bundle
`W''` of the diagram, as in Theorem 12.5.7 (`theorem_12_5_7_two_cont`).  `HasScPlusSectionsThrough`
follows from the bump functions.  They are stated for the given bundles, not for all diagrams.

## Not formalized

Independence of the transport from the diagram `D` (the generalized isomorphism `𝔉̄` of the text):
see the hand-over note (gap PB-4, remainder).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

open EPLocalization

namespace SBLocalization

namespace SDiagram

variable {A A' : SEP.{u}}

/-- **Transport of an orientation along a diagram of strong bundle equivalences** (Theorem 12.5.7
(2) with continuity, for Definition 16.6.5): `F' = [D]_* F`.  An orientation `o` of `F`
(Definition 12.5.4, topology `t` with the properties of Theorem 6.6.17) has exactly one invariant
`o'` on `F'` corresponding to `o` over the middle bundle `W''`, and `o'` is an orientation of `F'`
(Definition 12.5.4) for every topology `t'` with the properties of Theorem 6.6.17.  Part I's
hypotheses on the three bundles. -/
theorem orientation_transport_hyp (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    [ParacompactSpace (pullbackSpace A.P A.X.src)] [ParacompactSpace (pullbackSpace A'.P A'.X.src)]
    [ParacompactSpace (pullbackSpace D.B.P D.B.X.src)]
    {f : A.Obj → A.W} (hF : A.E.IsScFredholmSectionFunctor f)
    (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hfT : A.B.IsScFredholmSectionTame f)
    (hX' : A'.X.PObj.IsTame) (hbump' : A'.X.PObj.AdmitsBumpFunctions)
    (hX'' : D.B.X.PObj.IsTame) (hbump'' : D.B.X.PObj.AdmitsBumpFunctions)
    (hfT'' : D.B.B.IsScFredholmSectionTame (D.hΦ.pullback f))
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)
    (hsec'' : D.B.B.HasScPlusSectionsThrough)
    {t : TopologicalSpace (OrSpace f hF.2)}
    (ht : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsOrientationTopology f hF.2 t)
    {o : ∀ x (hs : x ∈ A.X.PObj.smoothSet), Orx f hF.2 x hs}
    (ho : A.E.definition_12_5_4 hF hsec t o) :
    let hF'' : D.B.E.IsScFredholmSectionFunctor (D.hΦ.pullback f) :=
      (EpStrongBundle.theorem_10_4_5_fred D.hΦ).2.1 hF
    let hF' : A'.E.IsScFredholmSectionFunctor (D.pushforward hΨ f) :=
      (EpStrongBundle.theorem_10_4_5_fred (sbe hΨ)).1 hF''
    let hpb₂ : D.hΦ.pullback f = (sbe hΨ).pullback (D.pushforward hΨ f) :=
      ((EpStrongBundle.theorem_10_4_5_fred (sbe hΨ)).2.2.1.1 hF'').symm
    ∃! o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx (D.pushforward hΨ f) hF'.2 x hs,
      A'.E.IsOrInvariant hF' hsec' o' ∧
      (∀ v (hv : v ∈ D.B.X.PObj.smoothSet),
        (sbe hΨ).orEqv hF'' hF' hpb₂ hsec'' hsec' v hv (o' _ ((sbe hΨ).smooth_obj hv)) =
          D.hΦ.orEqv hF'' hF rfl hsec'' hsec v hv (o _ (D.hΦ.smooth_obj hv))) ∧
      ∀ t' : TopologicalSpace (OrSpace (D.pushforward hΨ f) hF'.2),
        (haveI := paracompactSpace_rn_prod A'.X.PObj; haveI := paracompactSpace_rn_pullback A'.B
          IsOrientationTopology (D.pushforward hΨ f) hF'.2 t') →
        A'.E.definition_12_5_4 hF' hsec' t' o' := by
  intro hF'' hF' hpb₂
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_rn_prod A.X.PObj
  have := paracompactSpace_rn_rn_pullback A.B
  have := paracompactSpace_rn_prod A'.X.PObj
  have := paracompactSpace_rn_pullback A'.B
  have := paracompactSpace_rn_rn_prod A'.X.PObj
  have := paracompactSpace_rn_rn_pullback A'.B
  have hfT' : A'.B.IsScFredholmSectionTame (D.pushforward hΨ f) :=
    (sbe hΨ).isScFredholmSectionTame_pushforward hF''.1 hfT''
  have hcont : IsContOrOn (orLocalTransport hX hbump hfT hsec) univ o :=
    (isContOrOn_univ_iff_continuous hX hbump hfT hsec ht).1 ho.1
  obtain ⟨o', ⟨hinv', hcomp', hcont'⟩, huniq⟩ :=
    theorem_12_5_7_two_cont (h₁ := D.hΦ) (h₂ := sbe hΨ) (hF := hF) (hF' := hF') (hF'' := hF'')
      (hpb₁ := rfl) (hpb₂ := hpb₂) (hsec := hsec) (hsec' := hsec') (hsec'' := hsec'')
      (hX := hX) (hbump := hbump) (hfT := hfT) (hX' := hX') (hbump' := hbump') (hfT' := hfT')
      (hX'' := hX'') (hbump'' := hbump'') (hfT'' := hfT'') ho.2 hcont
  refine ⟨o', ⟨hinv', hcomp', fun t' ht' =>
    ⟨(isContOrOn_univ_iff_continuous hX' hbump' hfT' hsec' ht').2 hcont', hinv'⟩⟩,
    fun o'' ⟨hinv'', hcomp'', hdef''⟩ => ?_⟩
  -- uniqueness: `o''` is continuous for the topology of Theorem 6.6.17, so it is `o'`
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 hX' hbump' hfT').exists
  exact huniq o'' ⟨hinv'', hcomp'',
    (isContOrOn_univ_iff_continuous hX' hbump' hfT' hsec' ht₀).1 (hdef'' t₀ ht₀).1⟩

/-- An orientation for every topology of Theorem 6.6.17 carries over along `f₁ = f₂`. -/
theorem exists_orientation_of_eq {A : SEP.{u}} {f₁ f₂ : A.Obj → A.W} (h : f₁ = f₂)
    (hF₁ : A.E.IsScFredholmSectionFunctor f₁) (hF₂ : A.E.IsScFredholmSectionFunctor f₂)
    (hsec : A.B.HasScPlusSectionsThrough)
    (H : ∃ o : ∀ x (hs : x ∈ A.X.PObj.smoothSet), Orx f₁ hF₁.2 x hs,
      ∀ t : TopologicalSpace (OrSpace f₁ hF₁.2),
        (haveI := paracompactSpace_rn_prod A.X.PObj; haveI := paracompactSpace_rn_pullback A.B
          IsOrientationTopology f₁ hF₁.2 t) → A.E.definition_12_5_4 hF₁ hsec t o) :
    ∃ o : ∀ x (hs : x ∈ A.X.PObj.smoothSet), Orx f₂ hF₂.2 x hs,
      ∀ t : TopologicalSpace (OrSpace f₂ hF₂.2),
        (haveI := paracompactSpace_rn_prod A.X.PObj; haveI := paracompactSpace_rn_pullback A.B
          IsOrientationTopology f₂ hF₂.2 t) → A.E.definition_12_5_4 hF₂ hsec t o := by
  subst h
  exact H

end SDiagram

end SBLocalization

namespace StrongPolyfoldBundle

open SBLocalization StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

namespace OrientationRep

variable {s : FredholmSection c}

/-- **Every other representative is reached by a diagram**: for an orientation `R` of `s` on
`R.a` and a representative `b` of `s`, a diagram `D : W_a ←Φ W'' →Ψ W_b` of strong bundle
equivalences has `[D]_* F_a = F_b` (the relation of representatives before Definition 16.3.18). -/
theorem exists_diagram (R : OrientationRep s) (b : SectionRep c) (hb : ⟦b⟧ = s.1) :
    ∃ (D : SDiagram R.a.S.A b.S.A) (hΨ : SEP.equivalences D.Ψ), D.pushforward hΨ R.a.F = b.F := by
  obtain ⟨-, 𝔄, h𝔄, -, hpush⟩ := (Quotient.exact (R.ha.trans hb.symm) : SectionRep.Rel R.a b)
  exact ⟨GenSBMap.rep h𝔄, GenSBMap.isEquivalence_rep_Ψ h𝔄, hpush⟩

/-- **2021 Definition 16.6.5, p. 739 (2017: Definition 16.42): the orientation of one
representative determines one of every other representative** (Theorem 12.5.7 with continuity).
For an orientation `R` of `s` on `R.a`, a representative `b` of `s` and a diagram `D` with
`[D]_* F_a = F_b`, there is an orientation of `s` on `b`; its `o` is the transport of `R.o`
along `D` (`SDiagram.orientation_transport_hyp`).  Part I's hypotheses (tame, bump functions,
tame sc-Fredholm germs) on `W_a`, `W_b` and the middle bundle of `D`, as in Theorem 12.5.7. -/
theorem transport_hyp (R : OrientationRep s) (b : SectionRep c) (hb : ⟦b⟧ = s.1)
    (D : SDiagram R.a.S.A b.S.A) (hΨ : SEP.equivalences D.Ψ) (hD : D.pushforward hΨ R.a.F = b.F)
    (hX : R.a.S.A.X.PObj.IsTame) (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hfT : R.a.S.A.B.IsScFredholmSectionTame R.a.F)
    (hX' : b.S.A.X.PObj.IsTame) (hbump' : b.S.A.X.PObj.AdmitsBumpFunctions)
    (hX'' : D.B.X.PObj.IsTame) (hbump'' : D.B.X.PObj.AdmitsBumpFunctions)
    (hfT'' : D.B.B.IsScFredholmSectionTame (D.hΦ.pullback R.a.F)) :
    ∃ R' : OrientationRep s, R'.a = b := by
  have := R.a.S.A.B.paracompactSpace_pullback R.a.S.A.X.PMor R.a.S.A.X.src
  have := b.S.A.B.paracompactSpace_pullback b.S.A.X.PMor b.S.A.X.src
  have := D.B.B.paracompactSpace_pullback D.B.X.PMor D.B.X.src
  have hsec' : b.S.A.B.HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump'
  have hsec'' : D.B.B.HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump''
  have H := SDiagram.orientation_transport_hyp D hΨ R.hF hX hbump hfT hX' hbump' hX'' hbump''
    hfT'' R.hsec hsec' hsec'' R.isOrientationTopology R.isOrientation
  obtain ⟨o', ⟨-, -, ho'⟩, -⟩ := H
  have hFb : b.S.A.E.IsScFredholmSectionFunctor b.F :=
    (ScSection.isFredholm_iff s.1).1 s.2 b hb
  have hF'' : D.B.E.IsScFredholmSectionFunctor (D.hΦ.pullback R.a.F) :=
    (EpStrongBundle.theorem_10_4_5_fred D.hΦ).2.1 R.hF
  have hfTb : b.S.A.B.IsScFredholmSectionTame b.F :=
    hD ▸ (sbe hΨ).isScFredholmSectionTame_pushforward hF''.1 hfT''
  obtain ⟨o, ho⟩ := SDiagram.exists_orientation_of_eq hD _ hFb hsec' ⟨o', ho'⟩
  have := paracompactSpace_rn_prod b.S.A.X.PObj
  have := paracompactSpace_rn_pullback b.S.A.B
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 hX' hbump' hfTb).exists
  exact ⟨⟨b, hb, hFb, hsec', t₀, ht₀, o, ho t₀ ht₀⟩, rfl⟩

end OrientationRep

end StrongPolyfoldBundle

end Polyfold
