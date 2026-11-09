import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_66

set_option maxSynthPendingDepth 3

/-!
Round trip for V10_66 (2021 Theorem 10.3.19, pp. 493–494, with an effective target).

The item lists six theorems; `A` is the conjunction of their types, universes at `0`:
`EPLoc.theorem_10_3_19_of_isEffective` (with `Y` effective and (LR) on one side, generalized
isomorphisms `f, f' : of X ⟶ of Y` with the same orbit map are equal), the three lemmas of its
proof `EpFunctor.naturallyEquivalent_of_isEffective` (equivalences `H, H'` with `|H| = |H'|`, `X`
with (LR), `Y` effective, are naturally equivalent), `EpFunctor.eqOn_of_isEffective` (uniqueness
of continuous families `α_z : H(z) → H'(z)` over an effective target),
`EpGroupoid.eqOn_unit_of_isEffective` (a continuous family of isotropy elements over an open set
of an effective ep-groupoid is the unit family), and two witnesses on the point ep-groupoid.

`B`: for `X, Y : EPLoc.{0}` with `Y` effective and (LR) on one side, generalized isomorphisms
`f, f' : X ⟶ Y` with `orbitMap f = orbitMap f'` are equal.

* `A_to_B`: `theorem_10_3_19_of_isEffective` at `X.toEP`, `Y.toEP`.
* `B_to_A`: the main conjunct is `B` at `of X`, `of Y`.  The three lemmas are statements about
  ep-groupoids and functors, not about classes of diagrams, and are not consequences of `B`;
  they are re-proved outright below (the project's proofs, copied: `eqOn_unit_of_isEffective'`,
  `eqOn_of_isEffective'`, and `naturallyEquivalent_of_isEffective'`, which uses the non-item
  `EpFunctor.proposition_10_1_10_one`).  The two witnesses are re-proved from the non-item
  `isEffective_pointEP`, `isSLR_pointEP`.
-/

namespace RoundTrip.V10_66
open Polyfold Polyfold.EPLocalization CategoryTheory Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EPLocalization.EPLoc.theorem_10_3_19_of_isEffective.{0} ∧
  type_of% @Polyfold.EpFunctor.naturallyEquivalent_of_isEffective.{0, 0} ∧
  type_of% @Polyfold.EpFunctor.eqOn_of_isEffective.{0, 0} ∧
  type_of% @Polyfold.EpGroupoid.eqOn_unit_of_isEffective.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.theorem_10_3_19_of_isEffective_hypotheses ∧
  type_of% @Polyfold.EquivalenceLREffectiveExamples.naturallyEquivalent_of_isEffective_hypotheses

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.EPLoc.theorem_10_3_19_of_isEffective.{0},
    @Polyfold.EpFunctor.naturallyEquivalent_of_isEffective.{0, 0},
    @Polyfold.EpFunctor.eqOn_of_isEffective.{0, 0},
    @Polyfold.EpGroupoid.eqOn_unit_of_isEffective.{0},
    Polyfold.EPLocalization.EPLoc.theorem_10_3_19_of_isEffective_hypotheses,
    Polyfold.EquivalenceLREffectiveExamples.naturallyEquivalent_of_isEffective_hypotheses⟩

theorem A_to_B : A → B := by
  rintro ⟨h, -⟩ X Y hY hLR f f' hf hf' heq
  exact h (X := X.toEP) (Y := Y.toEP) hY hLR hf hf' heq

/-! ### The three lemmas, re-proved outright (the project's proofs) -/

section Lemmas

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

theorem eqOn_unit_of_isEffective' (hY : Y.IsEffective) {V : Set Obj'} (hV : IsOpen V)
    {k : Obj' → Mor'} (hk : ContinuousOn k V) (hs : ∀ v ∈ V, Y.src (k v) = v)
    (ht : ∀ v ∈ V, Y.tgt (k v) = v) : EqOn k Y.unit V := by
  intro v hv
  by_contra hne
  obtain ⟨N, S, σ, hN, hσ⟩ := Y.isLocalScDiffeo_src (k v)
  have hg : (⟨k v, hs v hv, ht v hv⟩ : Y.Isotropy v) ≠ 1 := fun h =>
    hne (congrArg GroupoidStr.Isotropy.val h)
  have hV₀ : IsOpen (V ∩ k ⁻¹' N) := hk.isOpen_inter_preimage hV hσ.isOpen_source
  have hW : IsOpen (N ∩ Y.src ⁻¹' (V ∩ k ⁻¹' N)) :=
    hσ.isOpen_source.inter (hV₀.preimage Y.continuous_src)
  obtain ⟨ψ, ⟨hψN, hψV, hψk⟩, hψ⟩ := hY v _ hg _ hW
    ⟨hN, by rw [mem_preimage, hs v hv]; exact ⟨hv, hN⟩⟩
  apply hψ
  have h1 : k (Y.src ψ) = ψ := by
    rw [← hσ.left_inv _ hψk, hs _ hψV, hσ.left_inv _ hψN]
  rw [← h1, ht _ hψV]
  exact hs _ hψV

theorem eqOn_of_isEffective' {H H' : EpFunctor X Y}
    (hH : X.PObj.IsLocalScDiffeo Y.PObj H.obj) (hY : Y.IsEffective) {U : Set Obj} (hU : IsOpen U)
    {α α' : Obj → Mor'} (hα : ContinuousOn α U) (hα' : ContinuousOn α' U)
    (hsα : ∀ z ∈ U, Y.src (α z) = H.obj z) (htα : ∀ z ∈ U, Y.tgt (α z) = H'.obj z)
    (hsα' : ∀ z ∈ U, Y.src (α' z) = H.obj z) (htα' : ∀ z ∈ U, Y.tgt (α' z) = H'.obj z) :
    EqOn α α' U := by
  intro z₀ hz₀
  obtain ⟨W, W', Hinv, hz₀W, hd⟩ := hH z₀
  have hd₁ := hd.restrict (hd.isOpen_source.inter hU) inter_subset_left
  set V := W' ∩ Hinv ⁻¹' (W ∩ U)
  have hVo : IsOpen V := hd₁.isOpen_target
  have hmem : ∀ v ∈ V, Hinv v ∈ U := fun v hv => (hd₁.mapsTo_inv hv).2
  have hHH : ∀ v ∈ V, H.obj (Hinv v) = v := fun v hv => hd₁.right_inv v hv
  have hc : ∀ v ∈ V, Y.src (Y.inv (α' (Hinv v))) = Y.tgt (α (Hinv v)) := fun v hv => by
    rw [Y.src_inv, htα' _ (hmem v hv), htα _ (hmem v hv)]
  have hcont : ContinuousOn Hinv V := hd₁.isScSmoothOn_inv.continuousOn
  have hk : ContinuousOn (fun v => Y.comp (Y.inv (α' (Hinv v))) (α (Hinv v))) V :=
    Y.continuousOn_comp_of (Y.continuous_inv.comp_continuousOn (hα'.comp hcont hmem))
      (hα.comp hcont hmem) hc
  have hz₀V : H.obj z₀ ∈ V := hd₁.mapsTo ⟨hz₀W, hz₀⟩
  have h := eqOn_unit_of_isEffective' hY hVo hk
    (fun v hv => by rw [Y.src_comp _ _ (hc v hv), hsα _ (hmem v hv), hHH v hv])
    (fun v hv => by rw [Y.tgt_comp _ _ (hc v hv), Y.tgt_inv, hsα' _ (hmem v hv), hHH v hv])
    hz₀V
  simp only [hd₁.left_inv z₀ ⟨hz₀W, hz₀⟩] at h
  have h2 := GroupoidStr.eq_inv_of_comp_eq_unit (G := Y.toGroupoidStr)
    (by rw [Y.src_inv, htα' _ hz₀, htα _ hz₀]) (h.trans (by rw [hsα _ hz₀]))
  rw [← GroupoidStr.inv_inv (G := Y.toGroupoidStr) (α z₀), ← h2, GroupoidStr.inv_inv]

theorem naturallyEquivalent_of_isEffective' {H H' : EpFunctor X Y}
    (hH : H.IsEquivalence) (hH' : H'.IsEquivalence) (hHH' : H.orbitMap = H'.orbitMap)
    (hX : X.IsLR) (hY : Y.IsEffective) : H.NaturallyEquivalent H' := by
  choose R _ α hα hαst using fun x =>
    EpFunctor.proposition_10_1_10_one hH hH' hHH' hX x isOpen_univ (mem_univ x)
  set a : Obj → Mor' := fun z => α z z
  have hloc : ∀ x, ∀ z ∈ (R x).U, a z = α x z := fun x z hz =>
    eqOn_of_isEffective' hH.isLocalScDiffeo_obj hY ((R z).isOpen_U.inter (R x).isOpen_U)
      ((hα z).continuousOn.mono inter_subset_left) ((hα x).continuousOn.mono inter_subset_right)
      (fun w hw => (hαst z w hw.1).1) (fun w hw => (hαst z w hw.1).2)
      (fun w hw => (hαst x w hw.2).1) (fun w hw => (hαst x w hw.2).2) ⟨(R z).mem_U, hz⟩
  have hsa : ∀ z, Y.src (a z) = H.obj z := fun z => (hαst z z (R z).mem_U).1
  have hta : ∀ z, Y.tgt (a z) = H'.obj z := fun z => (hαst z z (R z).mem_U).2
  have hsm : X.PObj.IsScSmoothMap Y.PMor a :=
    MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x _ => ⟨(R x).U, (R x).isOpen_U,
      (R x).mem_U, subset_univ _, (hα x).congr fun z hz => (hloc x z hz).symm⟩
  have hca : Continuous a := continuousOn_univ.1 hsm.continuousOn
  refine ⟨⟨a, hsm, hsa, hta, fun h => ?_⟩⟩
  obtain ⟨N, S, σ, hN, hσ⟩ := X.isLocalScDiffeo_src h
  have hσS : ∀ z ∈ S, X.src (σ z) = z := hσ.right_inv
  have hσc : ContinuousOn σ S := hσ.isScSmoothOn_inv.continuousOn
  have hSa : X.src h ∈ S := hσ.mapsTo hN
  have hσh : σ (X.src h) = h := hσ.left_inv h hN
  have hc1 : ∀ φ, Y.src (Y.inv (H'.mor φ)) = Y.tgt (a (X.tgt φ)) := fun φ => by
    rw [Y.src_inv, H'.tgt_mor, hta]
  have hc2 : ∀ φ, Y.src (Y.comp (Y.inv (H'.mor φ)) (a (X.tgt φ))) = Y.tgt (H.mor φ) :=
    fun φ => by rw [Y.src_comp _ _ (hc1 φ), hsa, H.tgt_mor]
  have hβ : ContinuousOn (fun z => Y.comp (Y.comp (Y.inv (H'.mor (σ z))) (a (X.tgt (σ z))))
      (H.mor (σ z))) S :=
    Y.continuousOn_comp_of (Y.continuousOn_comp_of
      (Y.continuous_inv.comp_continuousOn (H'.continuous_mor.comp_continuousOn hσc))
      (hca.comp_continuousOn (X.continuous_tgt.comp_continuousOn hσc)) fun z _ => hc1 (σ z))
      (H.continuous_mor.comp_continuousOn hσc) fun z _ => hc2 (σ z)
  have he := eqOn_of_isEffective' hH.isLocalScDiffeo_obj hY hσ.isOpen_target
    hca.continuousOn hβ (fun z _ => hsa z) (fun z _ => hta z)
    (fun z hz => by rw [Y.src_comp _ _ (hc2 (σ z)), H.src_mor, hσS z hz])
    (fun z hz => by
      rw [Y.tgt_comp _ _ (hc2 (σ z)), Y.tgt_comp _ _ (hc1 (σ z)), Y.tgt_inv, H'.src_mor,
        hσS z hz]) hSa
  simp only [hσh] at he
  have hcan := GroupoidStr.inv_comp_cancel_left (G := Y.toGroupoidStr)
    (φ := Y.inv (H'.mor h)) (ψ := Y.comp (a (X.tgt h)) (H.mor h))
    (by rw [Y.src_inv, Y.tgt_comp _ _ (by rw [hsa, H.tgt_mor]), H'.tgt_mor, hta])
  rw [GroupoidStr.inv_inv] at hcan
  rw [he, Y.comp_assoc _ _ _ (hc1 h) (by rw [hsa, H.tgt_mor])]
  exact hcan.symm

end Lemmas

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {X Y} hY hLR {f f'} hf hf' h => hB (EPLoc.of X) (EPLoc.of Y) hY hLR f f' hf hf' h,
    @naturallyEquivalent_of_isEffective', @eqOn_of_isEffective', @eqOn_unit_of_isEffective',
    ⟨EquivalenceLREffectiveExamples.isEffective_pointEP, EpGroupoid.Examples.isSLR_pointEP 0,
      ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩,
    ⟨EpFunctor.IsEquivalence.id _, EpGroupoid.Examples.isSLR_pointEP 0,
      EquivalenceLREffectiveExamples.isEffective_pointEP⟩⟩

#rt_check RoundTrip.V10_66.A_to_B [
  Polyfold.EPLocalization.EPLoc.theorem_10_3_19_of_isEffective,
  Polyfold.EpFunctor.naturallyEquivalent_of_isEffective, Polyfold.EpFunctor.eqOn_of_isEffective,
  Polyfold.EpGroupoid.eqOn_unit_of_isEffective,
  Polyfold.EPLocalization.EPLoc.theorem_10_3_19_of_isEffective_hypotheses,
  Polyfold.EquivalenceLREffectiveExamples.naturallyEquivalent_of_isEffective_hypotheses]
#rt_check RoundTrip.V10_66.B_to_A [
  Polyfold.EPLocalization.EPLoc.theorem_10_3_19_of_isEffective,
  Polyfold.EpFunctor.naturallyEquivalent_of_isEffective, Polyfold.EpFunctor.eqOn_of_isEffective,
  Polyfold.EpGroupoid.eqOn_unit_of_isEffective,
  Polyfold.EPLocalization.EPLoc.theorem_10_3_19_of_isEffective_hypotheses,
  Polyfold.EquivalenceLREffectiveExamples.naturallyEquivalent_of_isEffective_hypotheses]
#rt_overlap RoundTrip.V10_66.B_to_A [
  Polyfold.EPLocalization.EPLoc.theorem_10_3_19_of_isEffective,
  Polyfold.EpFunctor.naturallyEquivalent_of_isEffective, Polyfold.EpFunctor.eqOn_of_isEffective,
  Polyfold.EpGroupoid.eqOn_unit_of_isEffective,
  Polyfold.EPLocalization.EPLoc.theorem_10_3_19_of_isEffective_hypotheses,
  Polyfold.EquivalenceLREffectiveExamples.naturallyEquivalent_of_isEffective_hypotheses]

end RoundTrip.V10_66
