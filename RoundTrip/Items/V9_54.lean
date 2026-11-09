import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_54

/-!
Round trip for V9_54 (Lemma 9.5.9, 2021 p. 442; 2017: Lemma 9.18, p. 326): restrictions in the
`G_x`-case, the isotropy and set part.

`A` (universes at `0`) is the conjunction of the types of `NaturalRep.π_Φ`,
`NaturalRep.mem_stabilizer_iff_Φ`, `NaturalRep.card_quotient_stabilizer_mul_card_isotropy`,
`NaturalRep.exists_slice`, `NaturalRep.mapsTo_Φ_MU`, `NaturalRep.MU_inter_preimage_eq_iUnion`,
`NaturalRep.MU_inter_preimage_eq_iUnion_quotient` and `NaturalRep.pairwise_disjoint_image_Φ_out`.

* `A ⇒ B` (`A_to_B`): B's natural action on the connected `U(x)` is a project `NaturalRep`
  (`toNaturalRep`, as in V7_66).  `H ≅ G_y` is the project's `stabilizerEquivIsotropy` (with
  `H = stabB` by A's `mem_stabilizer_iff_Φ`); representatives exist (`reps_out`, the
  `Quotient.out` of the cosets); `♯R = ♯G/♯H` is A's `card_quotient_stabilizer_mul_card_isotropy`
  with `♯R = ♯(G/H)` (`card_reps`).  B's small `W` is the slice `V₀` of A's `exists_slice`; the
  disjointness of a `V ⊆ V₀` from its translates follows from that of `V₀`.  The
  `H`-invariance of an **arbitrary** connected `V ⊆ V₀` with the natural `G_y`-action is not in
  `A` (`exists_slice` produces one invariant `V`): it is proved here from the uniqueness of
  sections of `s` over a connected set (`eqOn_sections_of_isPreconnected`, a non-item
  Chapter 7 lemma): `Γ(h, ·)` and `Γ'(e h, ·)` agree on `V`, so `Φ(h) = Φ'(e h)` maps `V` to
  itself.  The preimage formula over any set of representatives is A's
  `MU_inter_preimage_eq_iUnion` reduced to `R` with A's `mapsTo_Φ_MU`, `π_Φ` and that invariance.
* `B ⇒ A` is not proved: `A` is more general.  Its `mapsTo_Φ_MU` and the preimage identities
  need only a functor `Θ` (B: a branched ep⁺-subgroupoid), `MU_inter_preimage_eq_iUnion` holds
  for every `V ⊆ U` (B: small natural `V(y)`), `exists_slice` gives slices inside every open `W`
  (B: one `W`), and `π_Φ`, `mem_stabilizer_iff_Φ`, `pairwise_disjoint_image_Φ_out` are not
  statements of `B`.
-/

namespace RoundTrip.V9_54
open Polyfold Set

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.NaturalRep.π_Φ.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.mem_stabilizer_iff_Φ.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.card_quotient_stabilizer_mul_card_isotropy.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.exists_slice.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.mapsTo_Φ_MU.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.MU_inter_preimage_eq_iUnion.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.MU_inter_preimage_eq_iUnion_quotient.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.pairwise_disjoint_image_Φ_out.{0}

theorem A_holds : A :=
  ⟨@EpGroupoid.NaturalRep.π_Φ, @EpGroupoid.NaturalRep.mem_stabilizer_iff_Φ,
    @EpGroupoid.NaturalRep.card_quotient_stabilizer_mul_card_isotropy,
    @EpGroupoid.NaturalRep.exists_slice, @EpGroupoid.NaturalRep.mapsTo_Φ_MU,
    @EpGroupoid.NaturalRep.MU_inter_preimage_eq_iUnion,
    @EpGroupoid.NaturalRep.MU_inter_preimage_eq_iUnion_quotient,
    @EpGroupoid.NaturalRep.pairwise_disjoint_image_Φ_out⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `Φ(1) = id` on `V` for B's natural action. -/
theorem Φ_one_of {X : EpGroupoid Obj Mor} {x : Obj} {V : Set Obj} {Φ : X.Isotropy x → Obj → Obj}
    {Γ : X.Isotropy x → Obj → Mor} (h : IsNatAction X x V Φ Γ) {y : Obj} (hy : y ∈ V) :
    Φ 1 y = y := by
  obtain ⟨ψ, hψ⟩ := h.diffeo 1
  have hz : ψ y ∈ V := hψ.mapsTo_inv hy
  have h1 : Φ 1 (ψ y) = y := hψ.right_inv y hy
  calc Φ 1 y = Φ 1 (Φ 1 (ψ y)) := by rw [h1]
    _ = Φ (1 * 1) (ψ y) := (h.hom 1 1 _ hz).symm
    _ = y := by rw [mul_one, h1]

/-- B's natural action on a **connected** `V` is a project `NaturalRep` (as in V7_66). -/
def toNaturalRep {X : EpGroupoid Obj Mor} {x : Obj} {V : Set Obj}
    {Φ : X.Isotropy x → Obj → Obj} {Γ : X.Isotropy x → Obj → Mor} (h : IsNatAction X x V Φ Γ)
    (hc : IsConnected V) : X.NaturalRep x where
  U := V
  isOpen_U := h.isOpen
  isConnected_U := hc
  mem_U := h.mem
  Φ := Φ
  Γ := Γ
  isScDiffeoOn_Φ g :=
    { isScSmoothOn := (h.diffeo g).choose_spec.isScSmoothOn
      isScSmoothOn_inv := (h.diffeo g⁻¹).choose_spec.isScSmoothOn
      mapsTo := (h.diffeo g).choose_spec.mapsTo
      mapsTo_inv := (h.diffeo g⁻¹).choose_spec.mapsTo
      left_inv := fun y hy => by rw [← h.hom g⁻¹ g y hy, inv_mul_cancel, Φ_one_of h hy]
      right_inv := fun y hy => by rw [← h.hom g g⁻¹ y hy, mul_inv_cancel, Φ_one_of h hy] }
  Φ_mul := h.hom
  isScSmoothOn_Γ := h.smooth
  Γ_self := h.Γ_x
  src_Γ g y hy := (h.src_tgt g y hy).1
  tgt_Γ g y hy := (h.src_tgt g y hy).2
  existsUnique_Γ := h.unique

end

/-- A set of left coset representatives of `H` is in bijection with `G ⧸ H`. -/
theorem card_reps {G : Type} [Group G] (H : Subgroup G) {R : Set G}
    (hR : IsLeftCosetRepsB (H : Set G) R) : Nat.card R = Nat.card (G ⧸ H) := by
  refine Nat.card_congr (Equiv.ofBijective (fun r : R => (r.1 : G ⧸ H)) ⟨?_, ?_⟩)
  · rintro ⟨r, hr⟩ ⟨r', hr'⟩ he
    have hmem : r⁻¹ * r' ∈ H := QuotientGroup.eq.1 he
    obtain ⟨r₀, -, huniq⟩ := hR r'
    have h1 := huniq r' ⟨hr', 1, H.one_mem, (mul_one r').symm⟩
    have h2 := huniq r ⟨hr, r⁻¹ * r', hmem, by group⟩
    exact Subtype.ext (h2.trans h1.symm)
  · intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨r, ⟨hr, h, hh, rfl⟩, -⟩ := hR g
      exact ⟨⟨r, hr⟩, QuotientGroup.eq.2 (by simpa using hh)⟩

/-- `Quotient.out` gives a set of left coset representatives. -/
theorem reps_out {G : Type} [Group G] (H : Subgroup G) :
    IsLeftCosetRepsB (H : Set G) (range (Quotient.out : G ⧸ H → G)) := by
  intro g
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  refine ⟨Quotient.out (g : G ⧸ H), ⟨mem_range_self _, h⁻¹, H.inv_mem h.2, ?_⟩, ?_⟩
  · rw [hh, mul_inv_cancel_right]
  · rintro r ⟨⟨q, rfl⟩, k, hk, hgk⟩
    have h1 : (g : G ⧸ H) = q := by
      rw [hgk]
      exact (QuotientGroup.eq.2 (by simpa using hk)).trans (QuotientGroup.out_eq' q)
    rw [h1]

theorem A_to_B : A → B := by
  intro hA
  obtain ⟨hπΦ, hmemstab, hcard, hslice, hmapsMU, hpre, -, -⟩ := hA
  intro Obj Mor _ _ _ _ _ _ X Θ hΘ x Φ Γ B hN hc y hy
  let R := toNaturalRep hN hc
  let a : R.U := ⟨y, hy⟩
  have hF : X.IsFunctorial Θ := hΘ.isFunctorial
  have hstab : ((MulAction.stabilizer (X.Isotropy x) a : Subgroup (X.Isotropy x)) :
      Set (X.Isotropy x)) = stabB Φ y := by
    ext g
    exact hmemstab R
  have hHpos : 0 < Nat.card (MulAction.stabilizer (X.Isotropy x) a) := Nat.card_pos
  refine ⟨⟨_, R.stabilizerEquivIsotropy a, hstab, fun h => rfl⟩,
    ⟨_, hstab ▸ reps_out (MulAction.stabilizer (X.Isotropy x) a)⟩, ?_, ?_⟩
  · -- `♯R = ♯G/♯H`
    intro R' hR'
    rw [← hstab] at hR' ⊢
    rw [card_reps _ hR']
    have h1 := hcard R a
    rw [← Nat.card_congr (R.stabilizerEquivIsotropy a).toEquiv] at h1
    exact (Nat.div_eq_of_eq_mul_left hHpos h1.symm).symm
  · -- the small `V(y)`
    obtain ⟨V₀, hV₀o, hyV₀, hV₀U, -, -, hdisj₀⟩ := hslice R a isOpen_univ (mem_univ _)
    refine ⟨V₀, hV₀o, hyV₀, hV₀U, fun V Φ' Γ' hN' hc' hVW => ?_⟩
    let R' := toNaturalRep hN' hc'
    have hVU : V ⊆ B.U := hVW.trans hV₀U
    -- `Φ(h)` maps `V` into itself for `h ∈ H`: it is `Φ'(e h)` on `V`
    have hsub : ∀ h ∈ stabB Φ y, MapsTo (Φ h) V V := by
      intro h hh v hv
      let k : X.Isotropy y := ⟨Γ h y, (hN.src_tgt h y hy).1, (hN.src_tgt h y hy).2.trans hh⟩
      have heq : EqOn (Γ h) (Γ' k) V :=
        eqOn_sections_of_isPreconnected X.isLocalScDiffeo_src.isLocallyInjective
          hc'.isPreconnected ((R.continuousOn_Γ h).mono hVU) (R'.continuousOn_Γ k)
          (fun z hz => (hN.src_tgt h z (hVU hz)).1) (fun z hz => (hN'.src_tgt k z hz).1)
          hN'.mem (hN'.Γ_x k).symm
      have hΦ : Φ h v = Φ' k v := by
        rw [← (hN.src_tgt h v (hVU hv)).2, heq hv, (hN'.src_tgt k v hv).2]
      rw [hΦ]
      exact (hN'.diffeo k).choose_spec.mapsTo hv
    have hinv : ∀ h ∈ stabB Φ y, Φ h '' V = V := by
      intro h hh
      have hh' : h⁻¹ ∈ stabB Φ y := by
        show Φ h⁻¹ y = y
        calc Φ h⁻¹ y = Φ h⁻¹ (Φ h y) := by rw [hh]
          _ = y := R.Φ_inv_Φ h hy
      exact (hsub h hh).image_subset.antisymm fun v hv =>
        ⟨Φ h⁻¹ v, hsub h⁻¹ hh' hv, R.Φ_Φ_inv h (hVU hv)⟩
    refine ⟨hinv, fun g hg => ?_, fun Rr hRr K hK => ?_⟩
    · exact (hdisj₀ g fun h => hg ((hmemstab R).1 h)).mono (image_mono hVW) hVW
    · have h1 := hpre R hF B rfl hK
      change B.MU ∩ X.π ⁻¹' K = ⋃ r ∈ Rr, Φ r '' (B.MU ∩ V ∩ X.π ⁻¹' K)
      rw [h1]
      refine Subset.antisymm (iUnion_subset fun g => ?_)
        (iUnion₂_subset fun r _ => subset_iUnion (fun g => R.Φ g '' (B.MU ∩ V ∩ X.π ⁻¹' K)) r)
      rintro _ ⟨w, ⟨⟨hwM, hwV⟩, hwK⟩, rfl⟩
      obtain ⟨r, ⟨hr, h, hh, rfl⟩, -⟩ := hRr g
      have hhw : Φ h w ∈ V := hinv h hh ▸ mem_image_of_mem _ hwV
      refine mem_iUnion₂.2 ⟨r, hr, Φ h w, ⟨⟨hmapsMU R hF B rfl h hwM, hhw⟩, ?_⟩, ?_⟩
      · rw [mem_preimage]
        rw [show Φ h w = R.Φ h w from rfl, hπΦ R h (hVU hwV)]
        exact hwK
      · exact (hN.hom r h w (hVU hwV)).symm

#rt_check RoundTrip.V9_54.A_to_B [Polyfold.EpGroupoid.NaturalRep.π_Φ,
  Polyfold.EpGroupoid.NaturalRep.mem_stabilizer_iff_Φ,
  Polyfold.EpGroupoid.NaturalRep.card_quotient_stabilizer_mul_card_isotropy,
  Polyfold.EpGroupoid.NaturalRep.exists_slice, Polyfold.EpGroupoid.NaturalRep.mapsTo_Φ_MU,
  Polyfold.EpGroupoid.NaturalRep.MU_inter_preimage_eq_iUnion,
  Polyfold.EpGroupoid.NaturalRep.MU_inter_preimage_eq_iUnion_quotient,
  Polyfold.EpGroupoid.NaturalRep.pairwise_disjoint_image_Φ_out]
#rt_overlap RoundTrip.V9_54.A_to_B [Polyfold.EpGroupoid.NaturalRep.π_Φ,
  Polyfold.EpGroupoid.NaturalRep.mem_stabilizer_iff_Φ,
  Polyfold.EpGroupoid.NaturalRep.card_quotient_stabilizer_mul_card_isotropy,
  Polyfold.EpGroupoid.NaturalRep.exists_slice, Polyfold.EpGroupoid.NaturalRep.mapsTo_Φ_MU,
  Polyfold.EpGroupoid.NaturalRep.MU_inter_preimage_eq_iUnion,
  Polyfold.EpGroupoid.NaturalRep.MU_inter_preimage_eq_iUnion_quotient,
  Polyfold.EpGroupoid.NaturalRep.pairwise_disjoint_image_Φ_out]
#print axioms RoundTrip.V9_54.A_to_B

end RoundTrip.V9_54
