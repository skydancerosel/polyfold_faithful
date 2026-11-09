import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_25

/-! Round trip for V7_25 (Proposition 7.5, pp. 233–234: natural representations of finitely many
isomorphic objects).

`A` is the conjunction of the types of the three listed theorems, universes at `0`:
`NatRepFinite.exists_star` (the star data of the proof: a base object `x`, a natural
representation at `x` and sheets of morphisms `x → y` whose transports land disjointly in `V`),
`proposition_7_1_15_2017` (open `V ⊇ Y`) and `proposition_7_1_15_of_mem_nhdsSet` (`V ∈ 𝓝ˢ Y`).  The others
(`NaturalRepFinite`, `transportRep`, `Star`, `emptyNaturalRepFinite`) are definitions.

* The project's conclusion `Nonempty (X.NaturalRepFinite Y V)` and `B`'s `∃ U F,
  IsNatRepFinB X Y V U F` are interchangeable: `isNatRepFinB_of` and `exists_natRepFinite` (the
  comparison of V7_26: sheets = connected components, `F (ψ⁻¹)` inverts `F ψ`, the natural
  representation at `y` from `B`'s natural action plus connectedness of `U(y)`).
* `A → B`: `proposition_7_1_15_of_mem_nhdsSet` and `isNatRepFinB_of`.
* `B → A`: `proposition_7_1_15_of_mem_nhdsSet` and `proposition_7_1_15_2017` (an open `V ⊇ Y` is in
  `𝓝ˢ Y`) from `B` and `exists_natRepFinite`.  `exists_star` is a lemma about the proof's
  construction, not a consequence of `B`; it is re-proved outright here (from Theorem 7.1,
  `theorem_7_1_13`, and the sheets of Definition 7.4, as in the project). -/

namespace RoundTrip.V7_25
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.NatRepFinite.exists_star.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_7_1_15_2017.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_7_1_15_of_mem_nhdsSet.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.NatRepFinite.exists_star.{0}, @Polyfold.EpGroupoid.proposition_7_1_15_2017.{0},
    @Polyfold.EpGroupoid.proposition_7_1_15_of_mem_nhdsSet.{0}⟩

section Glue
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Y : Finset Obj} {V : Set Obj}

/-- `IsScDiffeoOn` is insensitive to changing the map on its source. -/
theorem diffeo_congr {A B : Type} [TopologicalSpace A] [T2Space A] [ParacompactSpace A]
    [TopologicalSpace B] [T2Space B] [ParacompactSpace B] {P : MPolyfold A} {Q : MPolyfold B}
    {f f' : A → B} {g : B → A} {S : Set A} {T : Set B} (h : P.IsScDiffeoOn Q f g S T)
    (hf : EqOn f f' S) : P.IsScDiffeoOn Q f' g S T where
  isScSmoothOn := h.isScSmoothOn.congr hf
  isScSmoothOn_inv := h.isScSmoothOn_inv
  mapsTo a ha := hf ha ▸ h.mapsTo ha
  mapsTo_inv := h.mapsTo_inv
  left_inv a ha := by rw [← hf ha, h.left_inv a ha]
  right_inv b hb := by rw [← hf (h.mapsTo_inv hb), h.right_inv b hb]

/-- ... and the inverse on its target. -/
theorem diffeo_congr_inv {A B : Type} [TopologicalSpace A] [T2Space A] [ParacompactSpace A]
    [TopologicalSpace B] [T2Space B] [ParacompactSpace B] {P : MPolyfold A} {Q : MPolyfold B}
    {f : A → B} {g g' : B → A} {S : Set A} {T : Set B} (h : P.IsScDiffeoOn Q f g S T)
    (hg : EqOn g g' T) : P.IsScDiffeoOn Q f g' S T :=
  (diffeo_congr h.symm hg).symm

theorem mem_bigU {U : Obj → Set Obj} (hU : ∀ y ∈ Y, y ∈ U y) {ψ : Mor}
    (hψ : ψ ∈ X.morOn (Y : Set Obj)) : ψ ∈ bigU X Y U :=
  ⟨mem_biUnion hψ.1 (hU _ hψ.1), mem_biUnion hψ.2 (hU _ hψ.2)⟩

theorem inv_mem_morOn {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) :
    X.inv ψ ∈ X.morOn (Y : Set Obj) :=
  ⟨by rw [X.src_inv]; exact hψ.2, by rw [X.tgt_inv]; exact hψ.1⟩

theorem val_mem_morOn {y : Obj} (hy : y ∈ Y) (g : X.Isotropy y) :
    g.val ∈ X.morOn (Y : Set Obj) :=
  ⟨by rw [g.src_val]; exact hy, by rw [g.tgt_val]; exact hy⟩

/-- **From the project's structure to `B`'s property.** -/
theorem isNatRepFinB_of (N : X.NaturalRepFinite Y V) : IsNatRepFinB X Y V N.U N.F := by
  have hcc : ∀ ψ ∈ X.morOn (Y : Set Obj), connectedComponentIn (bigU X Y N.U) ψ = N.sheet ψ :=
    fun ψ hψ => EpGroupoid.NatRepFinite.connectedComponentIn_morOn N hψ (N.mem_sheet ψ hψ)
  refine ⟨fun y hy => ⟨N.isOpen_U y hy, N.isConnected_U y hy, N.mem_U y hy, N.U_subset y hy⟩,
    N.pairwiseDisjoint_U, fun ψ hψ => ⟨_, N.isScDiffeoOn_F ψ hψ⟩, N.F_comp, N.F_unit, ?_, ?_, ?_,
    ?_, ?_⟩
  · change X.morOn (⋃ y ∈ Y, N.U y) = _
    rw [N.morOn_eq]
    exact iUnion₂_congr fun ψ hψ => (hcc ψ hψ).symm
  · intro a ha b hb hab
    change Disjoint (connectedComponentIn _ a) (connectedComponentIn _ b)
    rw [hcc a ha, hcc b hb]
    exact N.pairwiseDisjoint_sheet ha hb hab
  · intro y hy
    obtain ⟨R, hRU, hRΦ⟩ := N.natural y hy
    refine ⟨R.Γ, ?_⟩
    exact
      { isOpen := N.isOpen_U y hy
        mem := N.mem_U y hy
        diffeo := fun g => ⟨_, by
          have h := N.isScDiffeoOn_F g.val (val_mem_morOn hy g)
          rwa [g.src_val, g.tgt_val] at h⟩
        hom := fun g h z hz => by
          have := N.F_comp g.val (val_mem_morOn hy g) h.val (val_mem_morOn hy h)
            (g.src_val.trans h.tgt_val.symm) z (by rw [h.src_val]; exact hz)
          exact this
        smooth := fun g => hRU ▸ R.isScSmoothOn_Γ g
        Γ_x := R.Γ_self
        src_tgt := fun g z hz => ⟨R.src_Γ g z (hRU ▸ hz),
          (R.tgt_Γ g z (hRU ▸ hz)).trans (hRΦ g z hz)⟩
        unique := fun h hs ht => R.existsUnique_Γ h (hRU ▸ hs) (hRU ▸ ht) }
  · intro ψ hψ
    rw [hcc ψ hψ]
    exact ⟨⟨_, N.isScDiffeoOn_src ψ hψ⟩, N.isScDiffeoOn_tgt ψ hψ⟩
  · intro ψ hψ φ hφ
    rw [hcc ψ hψ] at hφ
    have hs := (N.isScDiffeoOn_src ψ hψ).mapsTo hφ
    rw [N.F_eq ψ hψ _ hs, (N.isScDiffeoOn_src ψ hψ).left_inv φ hφ]

/-- **From `B`'s property to the project's structure**, with the same `U` and `F`. -/
theorem exists_natRepFinite {U : Obj → Set Obj} {F : Mor → Obj → Obj}
    (h : IsNatRepFinB X Y V U F) : ∃ N : X.NaturalRepFinite Y V, N.U = U ∧ N.F = F := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  -- `F (ψ⁻¹)` is the inverse of `F ψ`
  have hinv : ∀ ψ ∈ X.morOn (Y : Set Obj),
      X.PObj.IsScDiffeoOn X.PObj (F ψ) (F (X.inv ψ)) (U (X.src ψ)) (U (X.tgt ψ)) := by
    intro ψ hψ
    obtain ⟨G, hG⟩ := h3 ψ hψ
    refine diffeo_congr_inv hG fun w hw => ?_
    have hGw := hG.mapsTo_inv hw
    have hc := h4 (X.inv ψ) (inv_mem_morOn hψ) ψ hψ (X.src_inv ψ) (G w) hGw
    rw [X.inv_comp, h5 _ hψ.1 _ hGw, hG.right_inv w hw] at hc
    exact hc
  let σ : Mor → Obj → Mor := fun ψ =>
    if hψ : ψ ∈ X.morOn (Y : Set Obj) then Classical.choose (h9 ψ hψ).1 else fun _ => ψ
  have hσ : ∀ ψ (hψ : ψ ∈ X.morOn (Y : Set Obj)), X.PMor.IsScDiffeoOn X.PObj X.src (σ ψ)
      (connectedComponentIn (bigU X Y U) ψ) (U (X.src ψ)) := fun ψ hψ => by
    simp only [σ, dif_pos hψ]
    exact Classical.choose_spec (h9 ψ hψ).1
  have hmemU : ∀ y ∈ Y, y ∈ U y := fun y hy => (h1 y hy).2.2.1
  refine ⟨
    { U := U
      F := F
      sheet := fun ψ => connectedComponentIn (bigU X Y U) ψ
      srcInv := σ
      isOpen_U := fun y hy => (h1 y hy).1
      isConnected_U := fun y hy => (h1 y hy).2.1
      mem_U := hmemU
      U_subset := fun y hy => (h1 y hy).2.2.2
      pairwiseDisjoint_U := h2
      isScDiffeoOn_F := hinv
      F_comp := h4
      F_unit := h5
      isOpen_sheet := fun ψ hψ => (hσ ψ hψ).isScSmoothOn.isOpen
      isConnected_sheet := fun ψ hψ =>
        isConnected_connectedComponentIn_iff.2 (mem_bigU hmemU hψ)
      mem_sheet := fun ψ hψ => mem_connectedComponentIn (mem_bigU hmemU hψ)
      pairwiseDisjoint_sheet := h7
      morOn_eq := h6
      isScDiffeoOn_src := hσ
      isScDiffeoOn_tgt := fun ψ hψ => (h9 ψ hψ).2
      F_eq := fun ψ hψ z hz => by
        have hm := (hσ ψ hψ).mapsTo_inv hz
        have := h10 ψ hψ (σ ψ z) hm
        rwa [(hσ ψ hψ).right_inv z hz] at this
      natural := fun y hy => by
        obtain ⟨Γ, hΓ⟩ := h8 y hy
        refine ⟨
          { U := U y
            isOpen_U := hΓ.isOpen
            isConnected_U := (h1 y hy).2.1
            mem_U := hΓ.mem
            Φ := fun g => F g.val
            Γ := Γ
            isScDiffeoOn_Φ := fun g => by
              have h := hinv g.val (val_mem_morOn hy g)
              rw [g.src_val, g.tgt_val] at h
              exact h
            Φ_mul := hΓ.hom
            isScSmoothOn_Γ := hΓ.smooth
            Γ_self := hΓ.Γ_x
            src_Γ := fun g z hz => (hΓ.src_tgt g z hz).1
            tgt_Γ := fun g z hz => (hΓ.src_tgt g z hz).2
            existsUnique_Γ := hΓ.unique }, rfl, fun g z _ => rfl⟩ }, rfl, rfl⟩

end Glue

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X Y hY V hV
  obtain ⟨N⟩ := hA.2.2 X Y hY hV
  exact ⟨N.U, N.F, isNatRepFinB_of N⟩

/-! ### `B → A` -/

/-- `exists_star`, re-proved outright (the project's argument: Theorem 7.1 inside the
intersection of the transported neighbourhoods). -/
theorem exists_star' {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Y : Finset Obj} {V : Set Obj} (hV : IsOpen V) (hYV : (Y : Set Obj) ⊆ V)
    {x : Obj} (hx : ∀ y ∈ Y, X.Isomorphic x y) :
    Nonempty (EpGroupoid.NatRepFinite.Star X Y V) := by
  have key : ∀ y : Obj, ∃ S : X.Sheet, y ∈ Y → x ∈ S.srcSet ∧ S.hat x = y := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨φ, hφs, hφt⟩ := hx y hy
      obtain ⟨S, hφS⟩ := X.exists_sheet φ
      refine ⟨S, fun _ => ⟨hφs ▸ S.isScDiffeoOn_src.mapsTo hφS, ?_⟩⟩
      change X.tgt (S.srcInv x) = y
      rw [← hφs, S.isScDiffeoOn_src.left_inv φ hφS, hφt]
    · exact ⟨X.sheetAt (X.unit x), fun h => absurd h hy⟩
  choose K hK using key
  obtain ⟨W, hW, hWdisj⟩ := Y.finite_toSet.t2_separation
  have hU₀ : IsOpen (⋂ y ∈ Y, ((K y).srcSet ∩ (K y).hat ⁻¹' (W y ∩ V))) :=
    isOpen_biInter_finset fun y _ =>
      (K y).isScDiffeoOn_hat.isScSmoothOn.continuousOn.isOpen_inter_preimage
        (K y).isScDiffeoOn_src.isOpen_target ((hW y).2.inter hV)
  have hxU₀ : x ∈ ⋂ y ∈ Y, ((K y).srcSet ∩ (K y).hat ⁻¹' (W y ∩ V)) :=
    mem_iInter₂.2 fun y hy => ⟨(hK y hy).1, by
      rw [mem_preimage, (hK y hy).2]
      exact ⟨(hW y).1, hYV hy⟩⟩
  obtain ⟨R, hRU⟩ := EpGroupoid.theorem_7_1_13 X x hU₀ hxU₀
  have hR : ∀ y ∈ Y, ∀ u ∈ R.U, u ∈ (K y).srcSet ∧ (K y).hat u ∈ W y ∩ V :=
    fun y hy u hu => mem_iInter₂.1 (hRU hu) y hy
  refine ⟨⟨x, R, K, fun y hy u hu => (hR y hy u hu).1, fun y hy => (hK y hy).2, ?_, ?_⟩⟩
  · rintro y hy _ ⟨u, hu, rfl⟩
    exact (hR y hy u hu).2.2
  · refine hWdisj.mono_on fun y hy => ?_
    rintro _ ⟨u, hu, rfl⟩
    exact (hR y hy u hu).2.1

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X Y V hV hYV x hx
    exact exists_star' hV hYV hx
  · intro Obj Mor _ _ _ _ _ _ X Y hY V hV hYV
    obtain ⟨U, F, h⟩ := hB Obj Mor X Y hY V (hV.mem_nhdsSet.2 hYV)
    obtain ⟨N, -, -⟩ := exists_natRepFinite h
    exact ⟨N⟩
  · intro Obj Mor _ _ _ _ _ _ X Y hY V hV
    obtain ⟨U, F, h⟩ := hB Obj Mor X Y hY V hV
    obtain ⟨N, -, -⟩ := exists_natRepFinite h
    exact ⟨N⟩

#rt_check RoundTrip.V7_25.A_to_B [Polyfold.EpGroupoid.NatRepFinite.exists_star,
  Polyfold.EpGroupoid.proposition_7_1_15_2017, Polyfold.EpGroupoid.proposition_7_1_15_of_mem_nhdsSet]
#rt_check RoundTrip.V7_25.B_to_A [Polyfold.EpGroupoid.NatRepFinite.exists_star,
  Polyfold.EpGroupoid.proposition_7_1_15_2017, Polyfold.EpGroupoid.proposition_7_1_15_of_mem_nhdsSet]
#rt_overlap RoundTrip.V7_25.B_to_A [Polyfold.EpGroupoid.NatRepFinite.exists_star,
  Polyfold.EpGroupoid.proposition_7_1_15_2017, Polyfold.EpGroupoid.proposition_7_1_15_of_mem_nhdsSet]

end RoundTrip.V7_25
