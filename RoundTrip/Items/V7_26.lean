import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_26

/-! Round trip for V7_26 (Definition 7.8, p. 236: the natural representation of `𝐘`).

The item lists only definitions: the structure `EpGroupoid.NaturalRepFinite` (Definition 7.8)
and `NatRepFinite.mono` (a definition: enlarging `V`).  So `A = True`, and the comparison is `B`
itself, which says that `B`'s reading of "a functor `f` as constructed in Proposition 7.5 with its
stated properties" (`IsNatRepFinB`, the readings recorded in `RoundTrip/Blind/V7_25.lean`) is
exactly what the project's `NaturalRepFinite` carries.  `B_holds` proves this:

* `exists_natRepFinite`: from `IsNatRepFinB X Y V U F` a `NaturalRepFinite` with the same `U`
  and `F`: the sheets are the connected components `connectedComponentIn 𝐔 ψ`, `srcInv` is a
  chosen inverse of `s` on them, the inverse of `F ψ` is `F (ψ⁻¹)` (functoriality), and the
  natural representation at `y` is assembled from `B`'s natural action plus `U(y)` connected.
* `isNatRepFinB_of`: conversely, the project's sheets are the connected components of `𝐔`
  (`NatRepFinite.connectedComponentIn_morOn`), and the fields give `IsNatRepFinB`;
  `isNatRepFinB_congr` transports along `B`'s agreement conditions.

The project's structure carries data that `B` leaves existential (the sheets `𝐔(ψ)` as a field,
the inverse `(s|𝐔(ψ))⁻¹`, the inverse `F (ψ⁻¹)` of `F ψ`, the natural representation `R` at
each `y`); all of it is recovered, so the two notions agree. -/

namespace RoundTrip.V7_26
open Polyfold Set

/-- The project's statement: the item lists only definitions. -/
def A : Prop := True

theorem A_holds : A := trivial

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

/-- `B`'s property only depends on `U` on `Y` and on `F ψ` on `U(s ψ)`. -/
theorem isNatRepFinB_congr {U U' : Obj → Set Obj} {F F' : Mor → Obj → Obj}
    (h : IsNatRepFinB X Y V U F) (hU : ∀ y ∈ Y, U' y = U y)
    (hF : ∀ ψ ∈ X.morOn (Y : Set Obj), ∀ z ∈ U (X.src ψ), F' ψ z = F ψ z) :
    IsNatRepFinB X Y V U' F' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have hbig : bigU X Y U' = bigU X Y U := by
    change X.morOn (⋃ y ∈ Y, U' y) = X.morOn (⋃ y ∈ Y, U y)
    rw [iUnion₂_congr fun y (hy : y ∈ Y) => hU y hy]
  have hsrc : ∀ ψ ∈ X.morOn (Y : Set Obj), U' (X.src ψ) = U (X.src ψ) := fun ψ hψ => hU _ hψ.1
  have htgt : ∀ ψ ∈ X.morOn (Y : Set Obj), U' (X.tgt ψ) = U (X.tgt ψ) := fun ψ hψ => hU _ hψ.2
  have hmaps : ∀ ψ ∈ X.morOn (Y : Set Obj), MapsTo (F ψ) (U (X.src ψ)) (U (X.tgt ψ)) :=
    fun ψ hψ => (h3 ψ hψ).choose_spec.mapsTo
  refine ⟨fun y hy => hU y hy ▸ h1 y hy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    change Disjoint (U' a) (U' b)
    rw [hU a ha, hU b hb]
    exact h2 ha hb hab
  · intro ψ hψ
    obtain ⟨G, hG⟩ := h3 ψ hψ
    rw [hsrc ψ hψ, htgt ψ hψ]
    exact ⟨G, diffeo_congr hG fun z hz => (hF ψ hψ z hz).symm⟩
  · intro φ hφ ψ hψ hc z hz
    rw [hsrc ψ hψ] at hz
    have hcomp : X.comp φ ψ ∈ X.morOn (Y : Set Obj) :=
      ⟨by rw [X.src_comp _ _ hc]; exact hψ.1, by rw [X.tgt_comp _ _ hc]; exact hφ.2⟩
    have hz' : F ψ z ∈ U (X.src φ) := hc ▸ hmaps ψ hψ hz
    rw [hF _ hcomp z (by rw [X.src_comp _ _ hc]; exact hz), hF ψ hψ z hz, hF φ hφ _ hz']
    exact h4 φ hφ ψ hψ hc z hz
  · intro y hy z hz
    have hu : X.unit y ∈ X.morOn (Y : Set Obj) :=
      ⟨by rw [X.src_unit]; exact hy, by rw [X.tgt_unit]; exact hy⟩
    rw [hU y hy] at hz
    rw [hF _ hu z (by rw [X.src_unit]; exact hz)]
    exact h5 y hy z hz
  · rw [hbig]; exact h6
  · rw [hbig]; exact h7
  · intro y hy
    obtain ⟨Γ, hΓ⟩ := h8 y hy
    have hFg : ∀ g : X.Isotropy y, ∀ z ∈ U y, F' g.val z = F g.val z := fun g z hz =>
      hF _ (val_mem_morOn hy g) z (by rw [g.src_val]; exact hz)
    refine ⟨Γ, ?_⟩
    rw [hU y hy]
    exact
      { isOpen := hΓ.isOpen
        mem := hΓ.mem
        diffeo := fun g => by
          obtain ⟨G, hG⟩ := hΓ.diffeo g
          exact ⟨G, diffeo_congr hG fun z hz => (hFg g z hz).symm⟩
        hom := fun g h z hz => by
          have hmz : F h.val z ∈ U y := by
            have := hmaps h.val (val_mem_morOn hy h) (by rw [h.src_val]; exact hz)
            rwa [h.tgt_val] at this
          change F' (g * h).val z = F' g.val (F' h.val z)
          rw [hFg _ z hz, hFg h z hz, hFg g _ hmz]
          exact hΓ.hom g h z hz
        smooth := hΓ.smooth
        Γ_x := hΓ.Γ_x
        src_tgt := fun g z hz => ⟨(hΓ.src_tgt g z hz).1,
          (hΓ.src_tgt g z hz).2.trans (hFg g z hz).symm⟩
        unique := hΓ.unique }
  · intro ψ hψ
    rw [hbig, hsrc ψ hψ, htgt ψ hψ]
    exact h9 ψ hψ
  · intro ψ hψ φ hφ
    rw [hbig] at hφ
    obtain ⟨σ, hσ⟩ := (h9 ψ hψ).1
    rw [hF ψ hψ _ (hσ.mapsTo hφ)]
    exact h10 ψ hψ φ hφ

end Glue

/-- **`B` holds**: the project's `NaturalRepFinite Y V` is the text's natural representation. -/
theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X Y _ V _ U F
  constructor
  · intro h
    obtain ⟨N, hU, hF⟩ := exists_natRepFinite h
    exact ⟨N, fun y _ => by rw [hU], fun ψ _ z _ => by rw [hF]⟩
  · rintro ⟨N, hU, hF⟩
    exact isNatRepFinB_congr (isNatRepFinB_of N) (fun y hy => (hU y hy).symm)
      fun ψ hψ z hz => (hF ψ hψ z (by rw [← hU _ hψ.1]; exact hz)).symm

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V7_26.A_to_B [Polyfold.EpGroupoid.NatRepFinite.mono]
#rt_check RoundTrip.V7_26.B_to_A [Polyfold.EpGroupoid.NatRepFinite.mono]
#rt_overlap RoundTrip.V7_26.A_to_B [Polyfold.EpGroupoid.NatRepFinite.mono]

end RoundTrip.V7_26
