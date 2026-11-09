import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_56

/-!
Round trip for V9_56 (Lemma 9.5.11, 2021 p. 445; 2017: Lemma 9.19, p. 326): morphism
invariance, the isotropy and set part.

`A` (universes at `0`) is the conjunction of the types of `card_isotropy_eq_of_mor`,
`card_effIsotropy_eq_of_mor`, `IsFunctorial.eq_of_π_eq`, `image_π_MU_eq` and
`NaturalRep.Φ_hyps`.

* `A ⇒ B` (`A_to_B`): the conjugation isomorphism is the project's `isotropyConj` (its value is
  `isotropyConj_val`); `♯G_x = ♯G_{x'}` and `♯G^eff_x = ♯G^eff_{x'}` are A's first two
  conjuncts; `|M_U| = |M_{U'}|` is A's `image_π_MU_eq` for `f = t ∘ σ`, whose hypotheses come from
  B's `IsLocalHatB` (the sc-diffeomorphism `t ∘ σ : U → U'` gives `MapsTo`/`SurjOn`, and
  `s ∘ σ = id` gives `|t σ(z)| = |z|`); the correspondence of the preimages uses A's
  `IsFunctorial.eq_of_π_eq`.  The `T_x ↔ T_{x'}` clause is the (non-item) project lemma
  `isotropyConj_mem_trivialSet_iff` (Lemma 7.2.6), which needs no LUC.
* `B ⇒ A` is not proved: `A` is more general.  `card_isotropy_eq_of_mor` holds for every
  morphism, `B` only for morphisms with the full data of a natural `φ̂` between connected natural
  representations carrying local branching structures; `card_effIsotropy_eq_of_mor` holds without
  LUC, `B` states it only under LUC; `image_π_MU_eq` is for every onto map `f : U → U'` with
  `|f z| = |z|`, `B` for `f = t ∘ σ`; `eq_of_π_eq` and `Φ_hyps` are lemmas `B` does not state.
-/

namespace RoundTrip.V9_56
open Polyfold Set

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.card_isotropy_eq_of_mor.{0} ∧
  type_of% @Polyfold.EpGroupoid.card_effIsotropy_eq_of_mor.{0} ∧
  type_of% @Polyfold.EpGroupoid.IsFunctorial.eq_of_π_eq.{0} ∧
  type_of% @Polyfold.EpGroupoid.image_π_MU_eq.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.Φ_hyps.{0}

theorem A_holds : A :=
  ⟨@EpGroupoid.card_isotropy_eq_of_mor, @EpGroupoid.card_effIsotropy_eq_of_mor,
    @EpGroupoid.IsFunctorial.eq_of_π_eq, @EpGroupoid.image_π_MU_eq,
    @EpGroupoid.NaturalRep.Φ_hyps⟩

theorem A_to_B : A → B := by
  intro hA
  obtain ⟨hcard, hcardEff, heqπ, himg, -⟩ := hA
  intro Obj Mor _ _ _ _ _ _ X Θ hΘ φ U U' σ hσ Φ Γ Φ' Γ' _ _ _ _ B B' hBU hB'U
  have hF : X.IsFunctorial Θ := hΘ.isFunctorial
  obtain ⟨ψ, hψ⟩ := hσ.diffeo
  set f : Obj → Obj := fun y => X.tgt (σ y) with hf
  have hmaps : MapsTo f B.U B'.U := by rw [hBU, hB'U]; exact hψ.mapsTo
  have hsurj : SurjOn f B.U B'.U := by
    rw [hBU, hB'U]
    intro w hw
    exact ⟨ψ w, hψ.mapsTo_inv hw, hψ.right_inv w hw⟩
  have hπ : ∀ z ∈ B.U, X.π (f z) = X.π z := fun z hz =>
    ((X.π_eq_π_iff).2 ⟨σ z, hσ.sect z (hBU ▸ hz), rfl⟩).symm
  refine ⟨⟨X.isotropyConj φ rfl rfl, fun g => X.isotropyConj_val φ rfl rfl g⟩,
    hcard φ rfl rfl, himg hF B B' hmaps hsurj hπ, fun K _ => ?_, fun _ => ⟨?_, hcardEff φ rfl rfl⟩⟩
  · -- the preimages correspond under `φ̂ = t ∘ σ`
    ext w
    constructor
    · rintro ⟨hwM, hwK⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 hwM
      have hwU : w ∈ B'.U := B'.subset_U j hj
      obtain ⟨z, hzU, rfl⟩ := hsurj hwU
      have hz : z ∈ EpGroupoid.supp Θ := by
        have h1 : f z ∈ EpGroupoid.supp Θ := (B'.mem_supp_iff hwU).2 ⟨j, hj⟩
        change 0 < Θ z
        rw [← heqπ hF (hπ z hzU)]
        exact h1
      obtain ⟨i, hi⟩ := (B.mem_supp_iff hzU).1 hz
      refine ⟨z, ⟨mem_iUnion.2 ⟨i, hi⟩, ?_⟩, rfl⟩
      rw [mem_preimage, ← hπ z hzU]
      exact hwK
    · rintro ⟨z, ⟨hzM, hzK⟩, rfl⟩
      obtain ⟨i, hi⟩ := mem_iUnion.1 hzM
      have hzU : z ∈ B.U := B.subset_U i hi
      have hfz : f z ∈ EpGroupoid.supp Θ := by
        have h1 : z ∈ EpGroupoid.supp Θ := (B.mem_supp_iff hzU).2 ⟨i, hi⟩
        change 0 < Θ (f z)
        rw [heqπ hF (hπ z hzU)]
        exact h1
      obtain ⟨j, hj⟩ := (B'.mem_supp_iff (hmaps hzU)).1 hfz
      refine ⟨mem_iUnion.2 ⟨j, hj⟩, ?_⟩
      rw [mem_preimage, hπ z hzU]
      exact hzK
  · -- `T_x ↔ T_{x'}` under the conjugation (Lemma 7.2.6, no LUC needed)
    intro c hc g
    have hce : c g = X.isotropyConj φ rfl rfl g :=
      GroupoidStr.Isotropy.ext ((hc g).trans (X.isotropyConj_val φ rfl rfl g).symm)
    rw [hce, EpGroupoid.mem_trivialSubgroup, EpGroupoid.mem_trivialSubgroup,
      X.isotropyConj_mem_trivialSet_iff φ rfl rfl g]

#rt_check RoundTrip.V9_56.A_to_B [Polyfold.EpGroupoid.card_isotropy_eq_of_mor,
  Polyfold.EpGroupoid.card_effIsotropy_eq_of_mor, Polyfold.EpGroupoid.IsFunctorial.eq_of_π_eq,
  Polyfold.EpGroupoid.image_π_MU_eq, Polyfold.EpGroupoid.NaturalRep.Φ_hyps]
#rt_overlap RoundTrip.V9_56.A_to_B [Polyfold.EpGroupoid.card_isotropy_eq_of_mor,
  Polyfold.EpGroupoid.card_effIsotropy_eq_of_mor, Polyfold.EpGroupoid.IsFunctorial.eq_of_π_eq,
  Polyfold.EpGroupoid.image_π_MU_eq, Polyfold.EpGroupoid.NaturalRep.Φ_hyps]
#print axioms RoundTrip.V9_56.A_to_B

end RoundTrip.V9_56
