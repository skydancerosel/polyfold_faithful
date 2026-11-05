import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_46

/-! Round trip for V2_46 (Lemma 2.40: the faces of a tame retract are the connected components of
the sets `f ∩ O`, `f` an extended face; components through `x` agree iff `f = f'`).

`A` is the conjunction of the types of `Polyfold.lemma_2_40`, `lemma_2_40_injective`,
`closure_connectedComponentIn_faceStratum`, `connectedComponentIn_coordHyper_eq`,
`LocalModel.isFace_toMPolyfold_iff` and `subset_of_relClopen_of_isPreconnected` (universe `0`).
`ScRetraction.IsRetractFace` is a definition (vocabulary).

Glue (`coordHyper_indep`, new, elementary): for two presentations `T, T'` of the same partial
quadrant `C`, every coordinate hyperplane `{λ'_j = 0}` of `T'` is a coordinate hyperplane
`{λ_i = 0}` of `T` (at `p = T'⁻¹(a, 0)` with `a_j = 0`, `a_k = 1` otherwise, `d_C(p) = 1`, so `p`
has a single vanishing `T`-coordinate `i`; near `p`, `C` is the half-space `{λ_i ≥ 0}` and also
`{λ'_j ≥ 0}`, so `ker λ_i = ker λ'_j`).  B's extended faces range over all presentations; A's are
the hyperplanes of one presentation `T`.

`A → B`: the first claim is `isFace_toMPolyfold_iff` + `lemma_2_40` (the latter for the
presentation of `f`, `r` being tame for all presentations); the second is `lemma_2_40_injective`
after moving `f'` to the presentation of `f` (`coordHyper_indep`).

`B → A`: `lemma_2_40`, `lemma_2_40_injective`, `closure_connectedComponentIn_faceStratum` and
`connectedComponentIn_coordHyper_eq` are derived from `B` (for the retract `r(U)`, tame by
`IsTameWith.isTame`), through `coordHyper_indep`, the injectivity of `i ↦ f_i`, and `d_C = 1` on
the stratum `S`.  `isFace_toMPolyfold_iff` (the transfer of faces between the subtype `↥O` and
`E₀`, i.e. between B's vocabulary `MPolyfold.IsFace` and the project's `IsRetractFace`) and the
point-set lemma `subset_of_relClopen_of_isPreconnected` are proved directly (copies of the
project's short proofs, from non-banned lemmas: Prop. 2.36 `degIndex_toMPolyfold_of_isTameWith`,
`image_val_closure`, `image_val_connectedComponentIn`), without `B`. -/

namespace RoundTrip.V2_46
open Polyfold Set Filter Topology

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.lemma_2_40) ∧ (type_of% @Polyfold.lemma_2_40_injective) ∧
    (type_of% @Polyfold.closure_connectedComponentIn_faceStratum) ∧
    (type_of% @Polyfold.connectedComponentIn_coordHyper_eq) ∧
    (type_of% @Polyfold.LocalModel.isFace_toMPolyfold_iff) ∧
    (type_of% @Polyfold.subset_of_relClopen_of_isPreconnected.{0})

theorem A_holds : A :=
  ⟨@Polyfold.lemma_2_40, @Polyfold.lemma_2_40_injective,
    @Polyfold.closure_connectedComponentIn_faceStratum,
    @Polyfold.connectedComponentIn_coordHyper_eq, @Polyfold.LocalModel.isFace_toMPolyfold_iff,
    @Polyfold.subset_of_relClopen_of_isPreconnected.{0}⟩

/-! ### Glue: extended faces do not depend on the presentation -/

section Glue

variable {E : ScBanach} {C : Set (E 0)} {n n' : ℕ} {W W' : ScBanach}

/-- Near a point `p ∈ C` whose `T`-coordinates other than `i` are positive, `C` is the half-space
`{λ_i ≥ 0}`; hence a `T'`-coordinate `λ'_j` vanishing at `p` vanishes on `ker λ_i`. -/
theorem ker_subset (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT' : C = T' 0 ⁻¹' quadrant n' W' 0)
    {p : E 0} (hpC : p ∈ C) {i : Fin n} (hpos : ∀ k, k ≠ i → 0 < (T 0 p).1 k) {j : Fin n'}
    (hpj : (T' 0 p).1 j = 0) {v : E 0} (hv : (T 0 v).1 i = 0) : (T' 0 v).1 j = 0 := by
  have hev : ∀ᶠ z in 𝓝 p, ∀ k, k ≠ i → 0 < (T 0 z).1 k := by
    refine Filter.eventually_all.2 fun k => ?_
    by_cases hk : k = i
    · exact Filter.Eventually.of_forall fun _ h => absurd hk h
    · exact ((continuous_coord T k).continuousAt.eventually (lt_mem_nhds (hpos k hk))).mono
        fun z hz _ => hz
  have htend : Tendsto (fun t : ℝ => p + t • v) (𝓝 0) (𝓝 p) := by
    have : Continuous (fun t : ℝ => p + t • v) := continuous_const.add (continuous_id.smul continuous_const)
    simpa using this.tendsto 0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (htend.eventually hev)
  have hpi : 0 ≤ (T 0 p).1 i := by
    have : T 0 p ∈ quadrant n W 0 := by rw [hT] at hpC; exact hpC
    exact this i
  have hmem : ∀ t : ℝ, |t| < ε → p + t • v ∈ C := by
    intro t ht
    have hz := hball (y := t) (by rw [Real.dist_eq, sub_zero]; exact ht)
    rw [hT]
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, hv, mul_zero, add_zero]
      exact hpi
    · exact (hz k hk).le
  have hq : ∀ t : ℝ, |t| < ε → 0 ≤ t * (T' 0 v).1 j := by
    intro t ht
    have h := hmem t ht
    rw [hT'] at h
    have := h j
    simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hpj, zero_add] at this
    exact this
  have hε2 : |ε / 2| < ε := by rw [abs_of_pos (half_pos hε)]; linarith
  have hε2' : |-(ε / 2)| < ε := by rw [abs_neg]; exact hε2
  have h1 := hq _ hε2
  have h2 := hq _ hε2'
  have h3 : 0 < ε / 2 := half_pos hε
  nlinarith

/-- **Extended faces do not depend on the presentation**: every `T'`-hyperplane is a
`T`-hyperplane. -/
theorem coordHyper_indep (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT' : C = T' 0 ⁻¹' quadrant n' W' 0)
    (j : Fin n') : ∃ i : Fin n, coordHyper T i = coordHyper T' j := by
  classical
  set a : Fin n' → ℝ := fun k => if k = j then 0 else 1 with ha
  set p : E 0 := (T' 0).symm (a, 0) with hp
  have hTp : T' 0 p = (a, 0) := (T' 0).apply_symm_apply _
  have hpC : p ∈ C := by
    rw [hT']; change T' 0 p ∈ quadrant n' W' 0; rw [hTp]
    intro k; simp only [ha]; split_ifs <;> norm_num
  have hzs' : zeroSet T' p = {j} := by
    ext k
    rw [mem_zeroSet, hTp, Finset.mem_singleton]
    simp only [ha]
    split_ifs with h <;> simp [h]
  have hd : degIndexWith T p = 1 := by
    rw [← degIndex_eq T hT hpC, degIndex_eq T' hT' hpC, degIndexWith_eq_card_zeroSet, hzs',
      Finset.card_singleton]
  obtain ⟨i, hi⟩ := Finset.card_eq_one.1 ((degIndexWith_eq_card_zeroSet T p).symm.trans hd)
  have hposT : ∀ k, k ≠ i → 0 < (T 0 p).1 k := by
    intro k hk
    have hk' : k ∉ zeroSet T p := by rw [hi, Finset.mem_singleton]; exact hk
    rw [mem_zeroSet] at hk'
    exact lt_of_le_of_ne (coord_nonneg hT hpC k) (Ne.symm hk')
  have hposT' : ∀ k, k ≠ j → 0 < (T' 0 p).1 k := by
    intro k hk
    have hk' : k ∉ zeroSet T' p := by rw [hzs', Finset.mem_singleton]; exact hk
    rw [mem_zeroSet] at hk'
    exact lt_of_le_of_ne (coord_nonneg hT' hpC k) (Ne.symm hk')
  have hpi : (T 0 p).1 i = 0 := (mem_zeroSet T).1 (by rw [hi]; exact Finset.mem_singleton_self i)
  have hpj : (T' 0 p).1 j = 0 := (mem_zeroSet T').1 (by rw [hzs']; exact Finset.mem_singleton_self j)
  refine ⟨i, Set.Subset.antisymm (fun v hv => ?_) (fun v hv => ?_)⟩
  · exact ker_subset T hT T' hT' hpC hposT hpj hv
  · exact ker_subset T' hT' T hT hpC hposT' hpi hv

/-- `i ↦ f_i` is injective. -/
theorem coordHyper_injective (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {i j : Fin n}
    (h : coordHyper T i = coordHyper T j) : i = j := by
  classical
  by_contra hij
  set z : E 0 := (T 0).symm (Pi.single j 1, 0)
  have hTz : T 0 z = (Pi.single j 1, 0) := (T 0).apply_symm_apply _
  have hz : z ∈ coordHyper T i := by
    change (T 0 z).1 i = 0
    rw [hTz]; simp [hij]
  rw [h] at hz
  change (T 0 z).1 j = 0 at hz
  rw [hTz] at hz
  simp at hz

end Glue

theorem A_to_B : A → B := by
  intro hA E C O hO hne htame
  obtain ⟨h240, hinj, -, -, hiff, -⟩ := hA
  obtain ⟨R, hRO, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := R.relOpen.isPartialQuadrant
  have hR := hRt n W T hT
  refine ⟨fun G => ?_, fun f f' hf hf' x hx => ?_⟩
  · rw [hiff (LocalModel.mk E C O hO) hne R hRO hT hR G]
    constructor
    · intro hG
      obtain ⟨i, e, he, hei, hGe⟩ := (h240 hT hR _).1 hG
      refine ⟨coordHyper T i, ⟨n, W, T, hT, i, rfl⟩, e, ⟨hei, hRO ▸ he⟩, ?_⟩
      rw [hGe, hRO]
    · rintro ⟨f, ⟨n', W', T', hT', i, rfl⟩, x, ⟨hxf, hxO⟩, hG⟩
      have hR' := hRt n' W' T' hT'
      refine (h240 hT' hR' _).2 ⟨i, x, hRO ▸ hxO, hxf, ?_⟩
      rw [hG, hRO]; rfl
  · constructor
    · intro hcc
      obtain ⟨n1, W1, T1, hT1, i, rfl⟩ := hf
      obtain ⟨n2, W2, T2, hT2, j, rfl⟩ := hf'
      obtain ⟨k, hk⟩ := coordHyper_indep T1 hT1 T2 hT2 j
      have hk' : {z | ((T2.lvl 0) z).1 j = 0} = coordHyper T1 k := hk.symm
      rw [hk'] at hcc ⊢
      have hxO : x ∈ R.retract := by rw [hRO]; exact hx.2
      have hik := hinj hT1 (hRt _ _ _ hT1) hxO (i := i) (j := k) hx.1.1 (by rw [hRO]; exact hcc)
      rw [hik]; rfl
    · rintro rfl; rfl

/-! ### `B → A` -/

/-- `LocalModel.isFace_toMPolyfold_iff`, proved directly (the project's proof: a transfer of
definitions along `Subtype.val`, with `d_O = d_C`, Proposition 2.36). -/
theorem isFace_iff' : type_of% @Polyfold.LocalModel.isFace_toMPolyfold_iff := by
  intro M hne n W R hRM T hT hR F
  have hd := M.degIndex_toMPolyfold_of_isTameWith hne R hRM hT hR
  have hSO : R.faceStratum ⊆ M.O := fun z hz => by rw [← hRM]; exact hz.1
  have hset : {y : M.O | (M.toMPolyfold hne).degIndex y = 1} =
      (Subtype.val ⁻¹' R.faceStratum : Set M.O) := by
    ext y
    simp only [mem_ofPred_eq, mem_preimage, ScRetraction.faceStratum, hd]
    exact ⟨fun h => ⟨by rw [hRM]; exact y.2, h⟩, fun h => h.2⟩
  constructor
  · rintro ⟨x, hx1, rfl⟩
    have hxS : (x : M.E 0) ∈ R.faceStratum := by
      rw [← mem_preimage, ← hset]; exact hx1
    refine ⟨x, hxS, ?_⟩
    rw [hset, image_val_closure, image_val_connectedComponentIn hSO, hRM]
  · rintro ⟨x, hxS, hG⟩
    refine ⟨⟨x, hSO hxS⟩, by rw [hd]; exact hxS.2, ?_⟩
    apply Set.image_injective.2 Subtype.val_injective
    rw [hG, hset, image_val_closure, image_val_connectedComponentIn hSO, hRM]

/-- `subset_of_relClopen_of_isPreconnected` (point-set topology), proved directly. -/
theorem relClopen' : type_of% @Polyfold.subset_of_relClopen_of_isPreconnected.{0} := by
  intro α _ c F G K hc hcF hK hGK hopen x hx hxG
  set u : Set α := {z | ∃ V ∈ 𝓝 z, F ∩ V ⊆ G} with hu
  have huo : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨V, hV, hVG⟩
    obtain ⟨V', hV'V, hV'o, hzV'⟩ := mem_nhds_iff.1 hV
    exact Filter.mem_of_superset (hV'o.mem_nhds hzV') fun w hw =>
      ⟨V', hV'o.mem_nhds hw, fun t ht => hVG ⟨ht.1, hV'V ht.2⟩⟩
  have hGu : G ⊆ u := fun e he => hopen e he
  have hFu : F ∩ u ⊆ G := fun z ⟨hzF, V, hV, hVG⟩ => hVG ⟨hzF, mem_of_mem_nhds hV⟩
  have hcover : c ⊆ u ∪ Kᶜ := by
    intro z hz
    by_cases hzK : z ∈ K
    · exact Or.inl (hGu (hGK ▸ ⟨hcF hz, hzK⟩))
    · exact Or.inr hzK
  have hdisj : c ∩ (u ∩ Kᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z ⟨hz, hzu, hzK⟩ => hzK ?_
    have : z ∈ G := hFu ⟨hcF hz, hzu⟩
    rw [hGK] at this; exact this.2
  rcases isPreconnected_iff_subset_of_disjoint.1 hc u Kᶜ huo hK.isOpen_compl hcover hdisj with h | h
  · exact fun z hz => hFu ⟨hcF hz, h hz⟩
  · exact absurd (by rw [hGK] at hxG; exact hxG.2) (h hx)

section FromB

variable (hB : B)
include hB

/-- **Lemma 2.40** in the project's form, from `B`. -/
theorem B_lemma_2_40 : type_of% @Polyfold.lemma_2_40 := by
  intro E n W C R T hT hR G
  have hO : IsScRetract E C R.retract := ⟨R, rfl⟩
  have htame : IsTameRetract E C R.retract := ⟨R, rfl, hR.isTame hT⟩
  constructor
  · intro hG
    obtain ⟨x, hxS, hGx⟩ := hG
    have hne : R.retract.Nonempty := ⟨x, hxS.1⟩
    have hGO : G ⊆ R.retract := by rw [hGx]; exact inter_subset_right
    have himg : Subtype.val '' (Subtype.val ⁻¹' G : Set R.retract) = G := by
      rw [Subtype.image_preimage_coe, inter_eq_right.2 hGO]
    have hface : ((LocalModel.mk E C R.retract hO).toMPolyfold hne).IsFace
        (Subtype.val ⁻¹' G : Set R.retract) := by
      rw [isFace_iff' (LocalModel.mk E C R.retract hO) hne R rfl hT hR, himg]
      exact ⟨x, hxS, hGx⟩
    obtain ⟨f, ⟨n', W', T', hT', j, rfl⟩, y, ⟨hyf, hyO⟩, hGy⟩ :=
      ((hB E C R.retract hO hne htame).1 _).1 hface
    obtain ⟨i, hi⟩ := coordHyper_indep T hT T' hT' j
    refine ⟨i, y, hyO, ?_, ?_⟩
    · have : y ∈ coordHyper T i := by rw [hi]; exact hyf
      exact this
    · rw [← himg, hGy]
      change connectedComponentIn (coordHyper T' j ∩ R.retract) y = _
      rw [hi]
  · rintro ⟨i, e, he, hei, rfl⟩
    have hne : R.retract.Nonempty := ⟨e, he⟩
    set G := connectedComponentIn (coordHyper T i ∩ R.retract) e with hGdef
    have hGO : G ⊆ R.retract := (connectedComponentIn_subset _ _).trans inter_subset_right
    have himg : Subtype.val '' (Subtype.val ⁻¹' G : Set R.retract) = G := by
      rw [Subtype.image_preimage_coe, inter_eq_right.2 hGO]
    have hface : ((LocalModel.mk E C R.retract hO).toMPolyfold hne).IsFace
        (Subtype.val ⁻¹' G : Set R.retract) := by
      refine ((hB E C R.retract hO hne htame).1 _).2
        ⟨coordHyper T i, ⟨n, W, T, hT, i, rfl⟩, e, ⟨hei, he⟩, ?_⟩
      rw [himg]
    rw [isFace_iff' (LocalModel.mk E C R.retract hO) hne R rfl hT hR, himg] at hface
    exact hface

/-- The second statement of Lemma 2.40 in the project's form, from `B`. -/
theorem B_lemma_2_40_injective : type_of% @Polyfold.lemma_2_40_injective := by
  intro E n W C R T hT hR x hx i j hxi h
  have hO : IsScRetract E C R.retract := ⟨R, rfl⟩
  have htame : IsTameRetract E C R.retract := ⟨R, rfl, hR.isTame hT⟩
  have hne : R.retract.Nonempty := ⟨x, hx⟩
  have hxj : x ∈ coordHyper T j := by
    have : x ∈ connectedComponentIn (coordHyper T j ∩ R.retract) x := by
      rw [← h]; exact mem_connectedComponentIn ⟨hxi, hx⟩
    exact (connectedComponentIn_subset _ _ this).1
  have heq := ((hB E C R.retract hO hne htame).2 (coordHyper T i) (coordHyper T j)
    ⟨n, W, T, hT, i, rfl⟩ ⟨n, W, T, hT, j, rfl⟩ x ⟨⟨hxi, hxj⟩, hx⟩).1 h
  exact coordHyper_injective T heq

/-- `closure_connectedComponentIn_faceStratum`, from `B`. -/
theorem B_closure : type_of% @Polyfold.closure_connectedComponentIn_faceStratum := by
  intro E n W C R T hT hR x hx i hxi
  obtain ⟨k, e, he, hek, hG⟩ := (B_lemma_2_40 hB hT hR _).1 ⟨x, hx, rfl⟩
  have hxG : x ∈ closure (connectedComponentIn R.faceStratum x) ∩ R.retract :=
    ⟨subset_closure (mem_connectedComponentIn hx), hx.1⟩
  rw [hG] at hxG ⊢
  have hxk : (T 0 x).1 k = 0 := (connectedComponentIn_subset _ _ hxG).1
  have hzs := zeroSet_eq_singleton (faceStratum_degIndexWith hT hx) hxi
  have hk : k ∈ zeroSet T x := (mem_zeroSet T).2 hxk
  rw [hzs, Finset.mem_singleton] at hk
  rw [hk] at hxG ⊢
  exact connectedComponentIn_eq hxG

/-- `connectedComponentIn_coordHyper_eq`, from `B`. -/
theorem B_cc : type_of% @Polyfold.connectedComponentIn_coordHyper_eq := by
  intro E n W C R T hT hR e he i hei
  obtain ⟨p, hpS, hp⟩ := (B_lemma_2_40 hB hT hR _).2 ⟨i, e, he, hei, rfl⟩
  have hpG : p ∈ closure (connectedComponentIn R.faceStratum p) ∩ R.retract :=
    ⟨subset_closure (mem_connectedComponentIn hpS), hpS.1⟩
  rw [← hp] at hpG
  exact ⟨p, hpS, (connectedComponentIn_subset _ _ hpG).1, hp⟩

end FromB

theorem B_to_A : B → A := fun hB =>
  ⟨B_lemma_2_40 hB, B_lemma_2_40_injective hB, B_closure hB, B_cc hB, isFace_iff', relClopen'⟩

#rt_check RoundTrip.V2_46.A_to_B [Polyfold.lemma_2_40, Polyfold.lemma_2_40_injective,
  Polyfold.closure_connectedComponentIn_faceStratum, Polyfold.connectedComponentIn_coordHyper_eq,
  Polyfold.LocalModel.isFace_toMPolyfold_iff, Polyfold.subset_of_relClopen_of_isPreconnected]
#rt_check RoundTrip.V2_46.B_to_A [Polyfold.lemma_2_40, Polyfold.lemma_2_40_injective,
  Polyfold.closure_connectedComponentIn_faceStratum, Polyfold.connectedComponentIn_coordHyper_eq,
  Polyfold.LocalModel.isFace_toMPolyfold_iff, Polyfold.subset_of_relClopen_of_isPreconnected]
#rt_overlap RoundTrip.V2_46.B_to_A [Polyfold.lemma_2_40, Polyfold.lemma_2_40_injective,
  Polyfold.closure_connectedComponentIn_faceStratum, Polyfold.connectedComponentIn_coordHyper_eq,
  Polyfold.LocalModel.isFace_toMPolyfold_iff, Polyfold.subset_of_relClopen_of_isPreconnected]

end RoundTrip.V2_46
