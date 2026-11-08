import Polyfold.Chapter10.EquivalenceLR

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.1 and §10.3: a natural transformation from the families of
**Proposition 10.1.10 (1)** (p. 470; 2017: Proposition 10.4) when the target is effective.  This
is the step of the proof of **Theorem 10.3.19** (p. 494; 2017: Theorem 10.7) that does not hold as
we read it in general (`LocalizationLRCounterexample.lean`); here it is proved under the
additional hypothesis that the target is effective.  Numbers and pages are the 2021 text's.

# Natural transformations from local families over effective ep-groupoids

## The text, paraphrased

(Proof of Theorem 10.3.19, p. 494) For equivalences `H, H' : A → Y` with `|H| = |H'|` and (LR),
Proposition 10.1.10 (1) gives near every `a ∈ A` an sc-smooth family `α_a(b) : H(b) → H'(b)`,
and from these local families a natural transformation `H → H'` is obtained (on the ep-groupoid
of a cover of `A`).

## What is formalized

* `EpGroupoid.eqOn_unit_of_isEffective`: in an effective ep-groupoid (`EpGroupoid.IsEffective`),
  a continuous family `v ↦ k(v) ∈ G_v` over an open set of objects is the family of units.
* `EpFunctor.eqOn_of_isEffective`: over an effective target, two continuous families
  `α_z, α'_z : H(z) → H'(z)` on an open set agree, when `H` is a local sc-diffeomorphism on
  objects.
* `EpFunctor.naturallyEquivalent_of_isEffective`: if `H, H'` are equivalences with `|H| = |H'|`,
  `X` has (LR) and `Y` is effective, then `H ≃ H'` (natural equivalence, Definition 8.1.13),
  by an sc-smooth natural transformation defined on all of `X`.  Hypotheses satisfiable: the point
  ep-groupoid, `EquivalenceLREffectiveExamples.naturallyEquivalent_of_isEffective_hypotheses`.

## What the text leaves implicit, and the choices made

* Effectiveness makes the families of Proposition 10.1.10 (1) unique, so they glue on `X` itself
  and no cover `A_𝒰` is needed; naturality at a morphism `h` follows since
  `z ↦ H'(σ(z))⁻¹ ∘ α(t(σ(z))) ∘ H(σ(z))`, with `σ` the local inverse of `s` through `h`, is
  another such family.  Without effectiveness the conclusion fails
  (`LocalizationLRCounterexample.not_naturallyEquivalent_id_inv`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v

section Effective

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- **In an effective ep-groupoid a continuous family of isotropy elements over an open set of
objects is the family of units**: near `k(v) ≠ 1_v`, every morphism would be some `k(u)`, with
`s = t`. -/
theorem EpGroupoid.eqOn_unit_of_isEffective (hY : Y.IsEffective) {V : Set Obj'} (hV : IsOpen V)
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

/-- **Uniqueness of families `α_z : H(z) → H'(z)` over an effective target**: if `H` is a local
homeomorphism on objects, two continuous families on an open set agree (`α'_z⁻¹ ∘ α_z` is a
continuous family of isotropy elements over the open set `H(U)`). -/
theorem EpFunctor.eqOn_of_isEffective {H H' : EpFunctor X Y}
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
  have h := Y.eqOn_unit_of_isEffective hY hVo hk
    (fun v hv => by rw [Y.src_comp _ _ (hc v hv), hsα _ (hmem v hv), hHH v hv])
    (fun v hv => by rw [Y.tgt_comp _ _ (hc v hv), Y.tgt_inv, hsα' _ (hmem v hv), hHH v hv])
    hz₀V
  simp only [hd₁.left_inv z₀ ⟨hz₀W, hz₀⟩] at h
  have h2 := GroupoidStr.eq_inv_of_comp_eq_unit (G := Y.toGroupoidStr)
    (by rw [Y.src_inv, htα' _ hz₀, htα _ hz₀]) (h.trans (by rw [hsα _ hz₀]))
  rw [← GroupoidStr.inv_inv (G := Y.toGroupoidStr) (α z₀), ← h2, GroupoidStr.inv_inv]

/-- **A natural transformation from the families of Proposition 10.1.10 (1)** over an effective
target: if `H, H' : X → Y` are equivalences with `|H| = |H'|`, `X` has (LR) and `Y` is
effective, the local families `α_z : H(z) → H'(z)` are unique, so they glue to an sc-smooth
`α : X → 𝐘`, and `α` is natural (both sides of the naturality square at `h` are values of
continuous families near `s(h)`), hence `H ≃ H'`. -/
theorem EpFunctor.naturallyEquivalent_of_isEffective {H H' : EpFunctor X Y}
    (hH : H.IsEquivalence) (hH' : H'.IsEquivalence) (hHH' : H.orbitMap = H'.orbitMap)
    (hX : X.IsLR) (hY : Y.IsEffective) : H.NaturallyEquivalent H' := by
  choose R _ α hα hαst using fun x =>
    proposition_10_1_10_one hH hH' hHH' hX x isOpen_univ (mem_univ x)
  set a : Obj → Mor' := fun z => α z z
  have hloc : ∀ x, ∀ z ∈ (R x).U, a z = α x z := fun x z hz =>
    EpFunctor.eqOn_of_isEffective hH.isLocalScDiffeo_obj hY ((R z).isOpen_U.inter (R x).isOpen_U)
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
  have he := EpFunctor.eqOn_of_isEffective hH.isLocalScDiffeo_obj hY hσ.isOpen_target
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

end Effective

/-! ### Witnesses -/

namespace EquivalenceLREffectiveExamples

open EpGroupoid.Examples

/-- The point ep-groupoid is effective (its isotropy groups are trivial). -/
theorem isEffective_pointEP : pointEP.X.IsEffective :=
  fun _ _ hg => absurd (GroupoidStr.Isotropy.ext (Subsingleton.elim (α := Unit) _ _)) hg

/-- **Witness** for `EpFunctor.naturallyEquivalent_of_isEffective`: `H = H' = 1` on the point
ep-groupoid. -/
theorem naturallyEquivalent_of_isEffective_hypotheses :
    (EpFunctor.id pointEP.X).IsEquivalence ∧ pointEP.X.IsLR ∧ pointEP.X.IsEffective :=
  ⟨EpFunctor.IsEquivalence.id _, isSLR_pointEP 0, isEffective_pointEP⟩

end EquivalenceLREffectiveExamples

end Polyfold
