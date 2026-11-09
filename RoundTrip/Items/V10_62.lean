import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_62

set_option maxSynthPendingDepth 3

/-!
Round trip for V10_62 (2021 Proposition 10.1.9, pp. 468–470: (LR) under equivalences).

The item lists the definitions `EpFunctor.TransportChart`, `TransportChart.conj`,
`NaturalRep.HasLR` (vocabulary) and eleven theorems; `A` is the conjunction of their types,
universes at `0`: the main statement `EpFunctor.proposition_10_1_9` (`F` an equivalence ⇒
`X.IsLR ↔ Y.IsLR`), and the lemmas of its proof: `exists_transportChart` (the chart
`Q = ψ̂ ∘ F` along `ψ : F(x) → y`), `TransportChart.bijective_conj` (`g ↦ ψ ∘ F(g) ∘ ψ⁻¹` is
bijective), `TransportChart.Q_Φ` (`Q(g ∗ u) = (ψ F(g) ψ⁻¹) ∗ Q(u)`), `exists_naturalRep_push`,
`exists_naturalRep_pull` (natural representations transported along `Q`), `isLR_iff_hasLR`,
`NaturalRep.hasLR_iff_of_equivariant` (the two conjugation arguments), `NaturalRep.eqOn_Γ`,
`NaturalRep.eqOn_Φ` (uniqueness of `Γ`, `Φ` on preconnected sets), and the witness
`nonempty_transportChart_pointEP`.

`B`: for `X, Y : EP.{0}` and an equivalence `F : EpFunctor X.X Y.X`, `X.X.IsLR ↔ Y.X.IsLR`.

* `A_to_B`: `proposition_10_1_9` at `X.X`, `Y.X`.
* `B_to_A`: `proposition_10_1_9` is `B` at `EP.mk Obj Mor X`, `EP.mk Obj' Mor' Y`.  The ten
  proof lemmas are statements about charts, natural representations and isotropy maps, not
  consequences of `B`; they are re-proved outright below (the project's proofs, copied, with the
  banned lemmas replaced by the primed copies; the non-item helpers `Γ_conj`, `π_Q`,
  `π_eq_π_iff`, `isScDiffeoOn_image`, `exists_naturalRep_restrict`, `theorem_7_1`, ... are used).
-/

namespace RoundTrip.V10_62
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EpFunctor.proposition_10_1_9.{0, 0} ∧
  type_of% @Polyfold.EpFunctor.exists_transportChart.{0, 0} ∧
  type_of% @Polyfold.EpFunctor.TransportChart.bijective_conj.{0, 0} ∧
  type_of% @Polyfold.EpFunctor.TransportChart.Q_Φ.{0, 0} ∧
  type_of% @Polyfold.EpFunctor.TransportChart.exists_naturalRep_push.{0, 0} ∧
  type_of% @Polyfold.EpFunctor.TransportChart.exists_naturalRep_pull.{0, 0} ∧
  type_of% @Polyfold.EpGroupoid.isLR_iff_hasLR.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.hasLR_iff_of_equivariant.{0, 0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.eqOn_Γ.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.eqOn_Φ.{0} ∧
  type_of% @Polyfold.EquivalenceLRExamples.nonempty_transportChart_pointEP

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.proposition_10_1_9.{0, 0},
    @Polyfold.EpFunctor.exists_transportChart.{0, 0},
    @Polyfold.EpFunctor.TransportChart.bijective_conj.{0, 0},
    @Polyfold.EpFunctor.TransportChart.Q_Φ.{0, 0},
    @Polyfold.EpFunctor.TransportChart.exists_naturalRep_push.{0, 0},
    @Polyfold.EpFunctor.TransportChart.exists_naturalRep_pull.{0, 0},
    @Polyfold.EpGroupoid.isLR_iff_hasLR.{0},
    @Polyfold.EpGroupoid.NaturalRep.hasLR_iff_of_equivariant.{0, 0},
    @Polyfold.EpGroupoid.NaturalRep.eqOn_Γ.{0},
    @Polyfold.EpGroupoid.NaturalRep.eqOn_Φ.{0},
    Polyfold.EquivalenceLRExamples.nonempty_transportChart_pointEP⟩

theorem A_to_B : A → B := by
  rintro ⟨h, -⟩ X Y F hF
  exact h hF

/-! ### The proof lemmas, re-proved outright (the project's proofs) -/

section Lemmas

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

theorem eqOn_Γ' {x : Obj} (R R₂ : X.NaturalRep x) {V : Set Obj} (hV : IsPreconnected V)
    (hxV : x ∈ V) (hV₁ : V ⊆ R.U) (hV₂ : V ⊆ R₂.U) (g : X.Isotropy x) :
    EqOn (R.Γ g) (R₂.Γ g) V :=
  eqOn_sections_of_isPreconnected X.isLocalScDiffeo_src.isLocallyInjective hV
    ((R.isScSmoothOn_Γ g).continuousOn.mono hV₁) ((R₂.isScSmoothOn_Γ g).continuousOn.mono hV₂)
    (fun y hy => R.src_Γ g y (hV₁ hy)) (fun y hy => R₂.src_Γ g y (hV₂ hy)) hxV
    ((R.Γ_self g).trans (R₂.Γ_self g).symm)

theorem eqOn_Φ' {x : Obj} (R R₂ : X.NaturalRep x) {V : Set Obj} (hV : IsPreconnected V)
    (hxV : x ∈ V) (hV₁ : V ⊆ R.U) (hV₂ : V ⊆ R₂.U) (g : X.Isotropy x) :
    EqOn (R.Φ g) (R₂.Φ g) V :=
  fun y hy => by
    rw [← R.tgt_Γ g y (hV₁ hy), ← R₂.tgt_Γ g y (hV₂ hy), eqOn_Γ' R R₂ hV hxV hV₁ hV₂ g hy]

theorem hasLR_iff_of_equivariant' {x : Obj} {y : Obj'}
    (R : X.NaturalRep x) (R' : Y.NaturalRep y) {Q : Obj → Obj'} {Q' : Obj' → Obj}
    (hQ : X.PObj.IsScDiffeoOn Y.PObj Q Q' R.U R'.U) (e : X.Isotropy x → Y.Isotropy y)
    (he : Surjective e) (hQΦ : ∀ g, ∀ u ∈ R.U, Q (R.Φ g u) = R'.Φ (e g) (Q u))
    (hπ : ∀ a ∈ R.U, ∀ b ∈ R.U, X.π a = X.π b ↔ Y.π (Q a) = Y.π (Q b)) :
    R.HasLR ↔ R'.HasLR := by
  constructor
  · intro h γ γ' hγ hγπ
    obtain ⟨g, hg⟩ := h _ _ (hQ.symm.comp (hγ.comp hQ)) fun u hu => by
      have hQu := hQ.mapsTo hu
      have hγu := hγ.mapsTo hQu
      refine (hπ _ (hQ.mapsTo_inv hγu) u hu).2 ?_
      rw [hQ.right_inv _ hγu]
      exact hγπ _ hQu
    refine ⟨e g, fun z hz => ?_⟩
    have hz' := hQ.mapsTo_inv hz
    have h1 := hg _ hz'
    simp only [Function.comp_apply, hQ.right_inv z hz] at h1
    calc γ z = Q (Q' (γ z)) := (hQ.right_inv _ (hγ.mapsTo hz)).symm
      _ = Q (R.Φ g (Q' z)) := by rw [h1]
      _ = R'.Φ (e g) (Q (Q' z)) := hQΦ g _ hz'
      _ = R'.Φ (e g) z := by rw [hQ.right_inv z hz]
  · intro h β β' hβ hβπ
    obtain ⟨k, hk⟩ := h _ _ (hQ.comp (hβ.comp hQ.symm)) fun z hz => by
      have hz' := hQ.mapsTo_inv hz
      have h1 := (hπ _ (hβ.mapsTo hz') _ hz').1 (hβπ _ hz')
      simp only [Function.comp_apply]
      rwa [hQ.right_inv z hz] at h1
    obtain ⟨g, rfl⟩ := he k
    refine ⟨g, fun u hu => ?_⟩
    have h1 := hk _ (hQ.mapsTo hu)
    simp only [Function.comp_apply, hQ.left_inv u hu] at h1
    rw [← hQΦ g u hu] at h1
    calc β u = Q' (Q (β u)) := (hQ.left_inv _ (hβ.mapsTo hu)).symm
      _ = Q' (Q (R.Φ g u)) := by rw [h1]
      _ = R.Φ g u := hQ.left_inv _ (R.mapsTo_Φ g hu)

theorem exists_transportChart' {F : EpFunctor X Y} (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj)
    {x : Obj} {y : Obj'} {ψ₀ : Mor'} (hs : Y.src ψ₀ = F.obj x) (ht : Y.tgt ψ₀ = y) :
    ∃ T : EpFunctor.TransportChart F x y, T.ψ₀ = ψ₀ := by
  obtain ⟨N, S, σ, hψN, hσ⟩ := Y.isLocalScDiffeo_src ψ₀
  have hFxS : F.obj x ∈ S := hs ▸ hσ.mapsTo hψN
  have hσx : σ (F.obj x) = ψ₀ := by rw [← hs]; exact hσ.left_inv ψ₀ hψN
  have h1 : X.PObj.IsLocalScDiffeoAt Y.PMor (σ ∘ F.obj) x :=
    (hσ.symm.isLocalScDiffeoAt hFxS).comp (hF.at x)
  have h2 : X.PObj.IsLocalScDiffeoAt Y.PObj (Y.tgt ∘ (σ ∘ F.obj)) x := by
    refine MPolyfold.IsLocalScDiffeoAt.comp ?_ h1
    rw [Function.comp_apply, hσx]
    exact Y.isLocalScDiffeo_tgt.at ψ₀
  obtain ⟨W₁, W₁', Qinv, hxW₁, hd⟩ := h2
  have hWo : IsOpen (W₁ ∩ F.obj ⁻¹' S) :=
    hd.isOpen_source.inter (hσ.isOpen_target.preimage F.continuous_obj')
  refine ⟨⟨ψ₀, hs, ht, W₁ ∩ F.obj ⁻¹' S, _, Y.tgt ∘ (σ ∘ F.obj), Qinv, σ ∘ F.obj, ⟨hxW₁, hFxS⟩,
    hd.restrict hWo inter_subset_left, ?_, fun u hu => hσ.right_inv _ hu.2, fun u _ => rfl,
    hσx⟩, rfl⟩
  exact MPolyfold.IsScSmoothOn.comp hσ.isScSmoothOn_inv
    (F.isScSmoothMap_obj.mono hWo (subset_univ _)) fun u hu => hu.2

variable {F : EpFunctor X Y} {x : Obj} {y : Obj'}

theorem bijective_conj' (T : EpFunctor.TransportChart F x y) (hF : F.IsEquivalence) :
    Bijective T.conj :=
  (Y.isotropyConj T.ψ₀ T.src_ψ₀ T.tgt_ψ₀).bijective.comp (hF.bijective_isotropyHom x)

theorem Q_Φ' (T : EpFunctor.TransportChart F x y) (R : X.NaturalRep x) (R' : Y.NaturalRep y)
    {V : Set Obj} (g : X.Isotropy x) (hVU : V ⊆ R.U) (hVW : V ⊆ T.W)
    (hgW : ∀ u ∈ V, R.Φ g u ∈ T.W) (hV : IsPreconnected V) (hxV : x ∈ V)
    (hQV : ∀ u ∈ V, T.Q u ∈ R'.U) :
    ∀ u ∈ V, T.Q (R.Φ g u) = R'.Φ (T.conj g) (T.Q u) := fun u hu => by
  have h := congrArg Y.tgt (T.Γ_conj R R' g hVU hVW hgW hV hxV hQV u hu)
  rw [R'.tgt_Γ _ _ (hQV u hu), Y.tgt_comp _ _ (T.src_comp_ψ_Φ R g hVU hVW hgW hu),
    Y.tgt_comp _ _ (T.src_ψ_Φ R g hVU hgW hu), T.tgt_ψ _ (hgW u hu)] at h
  exact h.symm

theorem Q_Φ_of_subset' (T : EpFunctor.TransportChart F x y) (R : X.NaturalRep x)
    (R' : Y.NaturalRep y) (hR : R.U ⊆ T.W ∩ T.Q ⁻¹' R'.U) (g : X.Isotropy x) :
    ∀ u ∈ R.U, T.Q (R.Φ g u) = R'.Φ (T.conj g) (T.Q u) :=
  Q_Φ' T R R' g subset_rfl (fun _ hu => (hR hu).1) (fun _ hu => (hR (R.mapsTo_Φ g hu)).1)
    R.isConnected_U.isPreconnected R.mem_U fun _ hu => (hR hu).2

theorem exists_naturalRep_push' (T : EpFunctor.TransportChart F x y) (hF : F.IsEquivalence)
    (R : X.NaturalRep x) (R'₀ : Y.NaturalRep y) (hR : R.U ⊆ T.W ∩ T.Q ⁻¹' R'₀.U) :
    ∃ R' : Y.NaturalRep y, R'.U = T.Q '' R.U ∧ R'.Φ = R'₀.Φ ∧ R'.Γ = R'₀.Γ ∧
      ∀ g, ∀ u ∈ R.U, T.Q (R.Φ g u) = R'.Φ (T.conj g) (T.Q u) := by
  have hRW : R.U ⊆ T.W := fun u hu => (hR hu).1
  have hd := T.isScDiffeoOn_image R.isOpen_U hRW
  have heq := Q_Φ_of_subset' T R R'₀ hR
  obtain ⟨R', h1, h2, h3⟩ := Y.exists_naturalRep_restrict R'₀ hd.isOpen_target
    (R.isConnected_U.image _ (T.continuousOn_Q.mono hRW)) ⟨x, R.mem_U, T.Q_self⟩
    (image_subset_iff.2 fun u hu => (hR hu).2) fun k => by
      obtain ⟨g, rfl⟩ := (bijective_conj' T hF).2 k
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨R.Φ g u, R.mapsTo_Φ g hu, heq g u hu⟩
  exact ⟨R', h1, h2, h3, fun g u hu => by rw [h2]; exact heq g u hu⟩

theorem exists_naturalRep_pull' (T : EpFunctor.TransportChart F x y) (R₀ : X.NaturalRep x)
    (R'₁ : Y.NaturalRep y) (hR₀ : R₀.U ⊆ T.W ∩ T.Q ⁻¹' R'₁.U) (R' : Y.NaturalRep y)
    (hR' : R'.U ⊆ T.Q '' R₀.U) :
    ∃ R : X.NaturalRep x, R.U = R₀.U ∩ T.Q ⁻¹' R'.U ∧ T.Q '' R.U = R'.U ∧ R.Φ = R₀.Φ ∧
      R.Γ = R₀.Γ ∧ ∀ g, ∀ u ∈ R.U, T.Q (R.Φ g u) = R'.Φ (T.conj g) (T.Q u) := by
  have hR₀W : R₀.U ⊆ T.W := fun u hu => (hR₀ hu).1
  have heq₁ := Q_Φ_of_subset' T R₀ R'₁ hR₀
  have hR'R'₁ : R'.U ⊆ R'₁.U := hR'.trans (image_subset_iff.2 fun u hu => (hR₀ hu).2)
  have hΦ : ∀ k, EqOn (R'₁.Φ k) (R'.Φ k) R'.U := fun k =>
    eqOn_Φ' R'₁ R' R'.isConnected_U.isPreconnected R'.mem_U hR'R'₁ subset_rfl k
  have hUo : IsOpen (R₀.U ∩ T.Q ⁻¹' R'.U) :=
    (T.continuousOn_Q.mono hR₀W).isOpen_inter_preimage R₀.isOpen_U R'.isOpen_U
  have hUimg : T.Q '' (R₀.U ∩ T.Q ⁻¹' R'.U) = R'.U := by
    refine Subset.antisymm (image_subset_iff.2 fun u hu => hu.2) fun z hz => ?_
    obtain ⟨u, hu, rfl⟩ := hR' hz
    exact ⟨u, ⟨hu, hz⟩, rfl⟩
  have hd := T.isScDiffeoOn_image hUo fun u hu => hR₀W hu.1
  rw [hUimg] at hd
  have hUc : IsConnected (R₀.U ∩ T.Q ⁻¹' R'.U) := by
    have himg : T.Qinv '' R'.U = R₀.U ∩ T.Q ⁻¹' R'.U := hd.symm.image_eq
    rw [← himg]
    exact R'.isConnected_U.image _ hd.isScSmoothOn_inv.continuousOn
  have hinv : ∀ g, MapsTo (R₀.Φ g) (R₀.U ∩ T.Q ⁻¹' R'.U) (R₀.U ∩ T.Q ⁻¹' R'.U) :=
    fun g u hu => ⟨R₀.mapsTo_Φ g hu.1, by
      rw [mem_preimage, heq₁ g u hu.1, hΦ _ hu.2]
      exact R'.mapsTo_Φ _ hu.2⟩
  obtain ⟨R, h1, h2, h3⟩ := X.exists_naturalRep_restrict R₀ hUo hUc
    ⟨R₀.mem_U, by rw [mem_preimage, T.Q_self]; exact R'.mem_U⟩ inter_subset_left hinv
  refine ⟨R, h1, h1 ▸ hUimg, h2, h3, fun g u hu => ?_⟩
  rw [h1] at hu
  rw [h2, heq₁ g u hu.1, hΦ _ hu.2]

end Lemmas

/-- The witness, re-proved from `exists_transportChart'`. -/
theorem nonempty_transportChart_pointEP' (x : EpGroupoid.Examples.pointEP.Obj) :
    Nonempty ((EpFunctor.id EpGroupoid.Examples.pointEP.X).TransportChart x x) :=
  let ⟨T, _⟩ := exists_transportChart' (EpFunctor.IsEquivalence.id _).isLocalScDiffeo_obj
    (EpGroupoid.Examples.pointEP.X.src_unit _) (EpGroupoid.Examples.pointEP.X.tgt_unit _)
  ⟨T⟩

theorem B_to_A : B → A := by
  intro hB
  exact ⟨fun {Obj Mor} _ _ _ _ _ _ {Obj' Mor'} _ _ _ _ _ _ {X Y F} hF =>
      hB (EP.mk Obj Mor X) (EP.mk Obj' Mor' Y) F hF,
    @exists_transportChart', @bijective_conj', @Q_Φ', @exists_naturalRep_push',
    @exists_naturalRep_pull', fun {_ _ _ _ _ _ _ _ _} => Iff.rfl, @hasLR_iff_of_equivariant',
    @eqOn_Γ', @eqOn_Φ', nonempty_transportChart_pointEP'⟩

#rt_check RoundTrip.V10_62.A_to_B [Polyfold.EpFunctor.proposition_10_1_9,
  Polyfold.EpFunctor.exists_transportChart, Polyfold.EpFunctor.TransportChart.bijective_conj,
  Polyfold.EpFunctor.TransportChart.Q_Φ, Polyfold.EpFunctor.TransportChart.exists_naturalRep_push,
  Polyfold.EpFunctor.TransportChart.exists_naturalRep_pull, Polyfold.EpGroupoid.isLR_iff_hasLR,
  Polyfold.EpGroupoid.NaturalRep.hasLR_iff_of_equivariant, Polyfold.EpGroupoid.NaturalRep.eqOn_Γ,
  Polyfold.EpGroupoid.NaturalRep.eqOn_Φ,
  Polyfold.EquivalenceLRExamples.nonempty_transportChart_pointEP]
#rt_check RoundTrip.V10_62.B_to_A [Polyfold.EpFunctor.proposition_10_1_9,
  Polyfold.EpFunctor.exists_transportChart, Polyfold.EpFunctor.TransportChart.bijective_conj,
  Polyfold.EpFunctor.TransportChart.Q_Φ, Polyfold.EpFunctor.TransportChart.exists_naturalRep_push,
  Polyfold.EpFunctor.TransportChart.exists_naturalRep_pull, Polyfold.EpGroupoid.isLR_iff_hasLR,
  Polyfold.EpGroupoid.NaturalRep.hasLR_iff_of_equivariant, Polyfold.EpGroupoid.NaturalRep.eqOn_Γ,
  Polyfold.EpGroupoid.NaturalRep.eqOn_Φ,
  Polyfold.EquivalenceLRExamples.nonempty_transportChart_pointEP]
#rt_overlap RoundTrip.V10_62.B_to_A [Polyfold.EpFunctor.proposition_10_1_9,
  Polyfold.EpFunctor.exists_transportChart, Polyfold.EpFunctor.TransportChart.bijective_conj,
  Polyfold.EpFunctor.TransportChart.Q_Φ, Polyfold.EpFunctor.TransportChart.exists_naturalRep_push,
  Polyfold.EpFunctor.TransportChart.exists_naturalRep_pull, Polyfold.EpGroupoid.isLR_iff_hasLR,
  Polyfold.EpGroupoid.NaturalRep.hasLR_iff_of_equivariant, Polyfold.EpGroupoid.NaturalRep.eqOn_Γ,
  Polyfold.EpGroupoid.NaturalRep.eqOn_Φ,
  Polyfold.EquivalenceLRExamples.nonempty_transportChart_pointEP]

end RoundTrip.V10_62
