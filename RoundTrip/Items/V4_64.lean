import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_64

/-! Round trip for V4_64 (proof of Theorem 4.23: the finite cover of `{z ∈ A : |p(z)| ≤ ε}`).

`A` is the type of `Polyfold.theorem_4_3_1_of_subset`, universe `0`.

`B` (the blind author's reading, flagged by them as false) says that every choice of open
neighbourhoods `U(z)` of the points of `K = {z ∈ A : |p(z)| ≤ ε}` has a finite subcover, i.e.
that `K` is compact.  `not_B` proves `B` false with the blind author's counterexample:
`X = ℝ` (`rnPolyfold 1`, tame), `m = 1`, `ε = 1`, `A = ((−2, 2) × {0}) ∪ ((0, 2) × {1})`.
`A` is a smooth submanifold of `ℝ × ℝ` (sc⁺-retractions `(r, x) ↦ (r, c)` on open boxes, through
`isScPlusRetractionOn_of_chart`), in general position at every point (`d_Z ≡ 0`: every chart
presentation of `ℝ × ℝ` has no quadrant coordinates, so `E_z = E` and
`isGeneralPositionRetractAt_of_sup_eq_top` applies), its induced structure is tame (Theorem 4.18,
good position being automatic where `d = 0`), `cl A` is compact, every fibre over `|λ| ≤ 1` is
finite and nonempty; but `K ⊇ (0, 1] × {1}` accumulates at `(0, 1) ∉ A`, and the neighbourhoods
`U(λ, 1) = {r > λ/2}`, `U(λ, 0) = {x < 1/2}` have no finite subcover.

Consequently `A → B` is false (`not_A_to_B`: `A` holds), and `B → A` holds only ex falso.  The
project's `theorem_4_3_1_of_subset` replaces the text's finite cover by a countable one (`A` is
second countable), which is what the text's argument needs. -/

open Set Polyfold

noncomputable section

namespace RoundTrip.V4_64

/-- The project's statement, universe `0`. -/
def A : Prop := type_of% @Polyfold.theorem_4_3_1_of_subset.{0}

theorem A_holds : A := @Polyfold.theorem_4_3_1_of_subset.{0}

namespace CE

/-- `ℝ` as `Fin 1 → ℝ`. -/
abbrev R1 := Fin 1 → ℝ

/-- `Z = ℝ × ℝ`. -/
abbrev Z := R1 × R1

/-- The product M-polyfold `ℝ × ℝ`. -/
abbrev PZ : MPolyfold Z := (rnPolyfold 1).prod (rnPolyfold 1)

/-- The product chart `χ = id × id`. -/
abbrev χ : MChart Z := (rnChart 1 0).prod (rnChart 1 0)

theorem hχ : PZ.IsChart χ := MPolyfold.IsChart.prod (isChart_rnChart 0) (isChart_rnChart 0)

/-- The model sc-Banach space `ℝ ⊕ ℝ` of `χ`. -/
abbrev EE : ScBanach := (rnSc 1).prod (rnSc 1)

theorem hPQ : IsPartialQuadrant EE ((univ : Set R1) ×ˢ (univ : Set R1)) :=
  χ.model.isPartialQuadrant

/-- Every presentation of the partial quadrant `ℝ × ℝ` has no quadrant coordinates. -/
theorem no_coord {n : ℕ} {W : ScBanach} (T : ScIso EE ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : ((univ : Set R1) ×ˢ (univ : Set R1)) = T 0 ⁻¹' quadrant n W 0) (i : Fin n) : False := by
  set p : ((ScBanach.const (Fin n → ℝ)).prod W) 0 := (fun j => if j = i then -1 else 0, 0)
  have hx : (T 0).symm p ∈ ((univ : Set R1) ×ˢ (univ : Set R1)) := ⟨mem_univ _, mem_univ _⟩
  rw [hT, mem_preimage, ContinuousLinearEquiv.apply_symm_apply] at hx
  have := hx i
  simp [p] at this
  linarith

/-- All points of `ℝ ⊕ ℝ` are smooth. -/
theorem mem_smooth (w : EE 0) : w ∈ EE.smooth := by
  refine EE.mem_smooth_iff.2 fun k => ⟨(w.1, w.2), ?_⟩
  rw [ScBanach.prod_toBase]
  exact Prod.ext (ScBanach.const_toBase _ k _) (ScBanach.const_toBase _ k _)

theorem rn_mem_smooth (c : R1) : c ∈ (rnSc 1).smooth :=
  (rnSc 1).mem_smooth_iff.2 fun k => ⟨c, ScBanach.const_toBase _ k _⟩

/-- `d_Z ≡ 0`. -/
theorem degIndex_zero (z : Z) : PZ.degIndex z = 0 := by
  have h := PZ.degIndex_le hχ (show z ∈ χ.source from ⟨mem_univ _, mem_univ _⟩)
  obtain ⟨n, W, T, hT⟩ := hPQ
  have hC : χ z ∈ ((univ : Set R1) ×ˢ (univ : Set R1)) := ⟨mem_univ _, mem_univ _⟩
  have h' : PZ.degIndex z ≤ Polyfold.degIndex EE ((univ : Set R1) ×ˢ (univ : Set R1)) (χ z) := h
  have hu : (Finset.univ : Finset (Fin n)) = ∅ :=
    Finset.univ_eq_empty_iff.2 ⟨fun i => no_coord T hT i⟩
  have h0 : degIndexWith T (χ z) = 0 := by
    simp [degIndexWith, quadrantDeg, hu]
  rw [degIndex_eq T hT hC, h0] at h'
  omega

/-! ### The sc⁺-retractions `(r, x) ↦ (r, c)` -/

section Retraction

variable (c : R1) {I J : Set R1} (hI : IsOpen I) (hJ : IsOpen J) (hc : c ∈ J)
include hI hJ hc

omit hc in
theorem relOpen_box : IsRelOpenInQuadrant EE ((univ : Set R1) ×ˢ (univ : Set R1)) (I ×ˢ J) :=
  ⟨hPQ, I ×ˢ J, hI.prod hJ, by rw [univ_prod_univ, inter_univ]⟩

omit hJ hc in
theorem isScDomain_I : IsScDomain (rnSc 1) I :=
  (show IsRelOpenInQuadrant (rnSc 1) univ I from
    ⟨isPartialQuadrant_univ _, I, hI, (inter_univ _).symm⟩).isScDomain

omit hc in
theorem isScPlus_box : IsScPlus (E := EE) (F := EE) (I ×ˢ J) (fun w : EE 0 => (w.1, c)) := by
  have hUd := (relOpen_box hI hJ).isScDomain
  have hId := isScDomain_I hI
  have hΓ : IsScSmooth (E := rnSc 1) (F := EE) I (scPair (E := rnSc 1) (F := rnSc 1) (G := rnSc 1)
      _root_.id (fun _ => c)) :=
    IsScSmooth.scPair hId (isScSmooth_id hId) (isScSmooth_const_of_mem_smooth hId (rn_mem_smooth c))
  have hΓp := isScPlus_of_isScSmooth_const hId hΓ
  have hπ : IsScSmooth (E := EE) (F := rnSc 1) (I ×ˢ J) ((ScBanach.prodFstOp (rnSc 1) (rnSc 1)) 0) :=
    ScOperator.isScSmooth _ hUd
  exact IsScPlus.comp_isScSmooth hUd hId hΓp hπ (fun w hw => hw.1)

/-- The sc⁺-retraction of `ℝ ⊕ ℝ` onto `I × {c}`. -/
def boxRetraction : ScRetraction χ.model.E χ.model.C where
  U := I ×ˢ J
  toFun := fun w => (w.1, c)
  relOpen := relOpen_box hI hJ
  mapsTo := fun _ hw => ⟨hw.1, hc⟩
  isScSmooth := (isScPlus_box c hI hJ).isScSmooth (relOpen_box hI hJ).isScDomain
  idem := fun _ _ => rfl

theorem boxRetraction_isScPlus : (boxRetraction c hI hJ hc).IsScPlus :=
  isScPlus_box c hI hJ

/-- On `ℝ × ℝ`: `(r, x) ↦ (r, c)` is an sc⁺-retraction on the open box `I × J` onto `I × {c}`. -/
theorem isScPlusRetractionOn_box :
    PZ.IsScPlusRetractionOn (fun z : Z => (z.1, c)) (I ×ˢ J) ∧
      (fun z : Z => (z.1, c)) '' (I ×ˢ J) = {z : Z | z.1 ∈ I ∧ z.2 = c} := by
  obtain ⟨-, h2, h3⟩ := MPolyfold.isScPlusRetractionOn_of_chart hχ (boxRetraction c hI hJ hc)
    (boxRetraction_isScPlus c hI hJ hc) (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  have hfun : (χ.symm ∘ (boxRetraction c hI hJ hc) ∘ χ) = fun z : Z => (z.1, c) := by
    funext z
    change ((z.1 - 0) + 0, c + 0) = (z.1, c)
    simp
  have hV : χ.source ∩ χ ⁻¹' (boxRetraction c hI hJ hc).U = I ×ˢ J := by
    ext z
    change (True ∧ True) ∧ (z.1 - 0 ∈ I ∧ z.2 - 0 ∈ J) ↔ z.1 ∈ I ∧ z.2 ∈ J
    simp
  rw [hfun, hV] at h2 h3
  refine ⟨h2, ?_⟩
  rw [h3]
  ext z
  change (True ∧ True) ∧ (z.1 - 0, z.2 - 0) ∈ (fun w : EE 0 => (w.1, c)) '' (I ×ˢ J) ↔ _
  simp only [true_and, sub_zero, mem_image, mem_prod, Prod.mk.injEq, mem_ofPred_eq]
  constructor
  · rintro ⟨w, ⟨hw1, -⟩, h1, h2⟩
    exact ⟨h1 ▸ hw1, h2.symm⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨(z.1, z.2), ⟨h1, hc⟩, rfl, rfl⟩

end Retraction

/-! ### The submanifold `A = ((−2, 2) × {0}) ∪ ((0, 2) × {1})` -/

/-- The counterexample `A = ((−2, 2) × {0}) ∪ ((0, 2) × {1}) ⊆ ℝ × ℝ`. -/
def Aset : Set Z := {z | (z.2 = 0 ∧ |z.1 0| < 2) ∨ (z.2 = 1 ∧ 0 < z.1 0 ∧ z.1 0 < 2)}

def I0 : Set R1 := {r | |r 0| < 2}
def J0 : Set R1 := {r | |r 0| < 1 / 2}
def I1 : Set R1 := {r | 0 < r 0 ∧ r 0 < 2}
def J1 : Set R1 := {r | 1 / 2 < r 0 ∧ r 0 < 3 / 2}

theorem hI0 : IsOpen I0 := isOpen_lt (continuous_apply 0).abs continuous_const
theorem hJ0 : IsOpen J0 := isOpen_lt (continuous_apply 0).abs continuous_const
theorem hI1 : IsOpen I1 :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter (isOpen_lt (continuous_apply 0) continuous_const)
theorem hJ1 : IsOpen J1 :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter (isOpen_lt (continuous_apply 0) continuous_const)
theorem hc0 : (0 : R1) ∈ J0 := by simp [J0]
theorem hc1 : (1 : R1) ∈ J1 := by
  refine ⟨?_, ?_⟩ <;> simp <;> norm_num

theorem zero_ne_one' : (0 : R1) ≠ 1 := fun h => by
  have := congrFun h 0
  simp at this

theorem box0 :
    PZ.IsScPlusRetractionOn (fun z : Z => (z.1, (0 : R1))) (I0 ×ˢ J0) ∧
      (fun z : Z => (z.1, (0 : R1))) '' (I0 ×ˢ J0) = Aset ∩ (I0 ×ˢ J0) := by
  obtain ⟨h1, h2⟩ := isScPlusRetractionOn_box 0 hI0 hJ0 hc0
  refine ⟨h1, h2.trans ?_⟩
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, Aset]
  constructor
  · rintro ⟨hz1, h2⟩
    exact ⟨Or.inl ⟨h2, hz1⟩, hz1, by rw [h2]; exact hc0⟩
  · rintro ⟨h | h, hz1, hz2⟩
    · exact ⟨hz1, h.1⟩
    · exfalso
      have : z.2 0 = 1 := by rw [h.1]; rfl
      have h2 : |z.2 0| < 1 / 2 := hz2
      rw [this] at h2
      norm_num at h2

theorem box1 :
    PZ.IsScPlusRetractionOn (fun z : Z => (z.1, (1 : R1))) (I1 ×ˢ J1) ∧
      (fun z : Z => (z.1, (1 : R1))) '' (I1 ×ˢ J1) = Aset ∩ (I1 ×ˢ J1) := by
  obtain ⟨h1, h2⟩ := isScPlusRetractionOn_box 1 hI1 hJ1 hc1
  refine ⟨h1, h2.trans ?_⟩
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, Aset]
  constructor
  · rintro ⟨hz1, h2⟩
    exact ⟨Or.inr ⟨h2, hz1⟩, hz1, by rw [h2]; exact hc1⟩
  · rintro ⟨h | h, hz1, hz2⟩
    · exfalso
      have : z.2 0 = 0 := by rw [h.1]; rfl
      have h2 : 1 / 2 < z.2 0 := hz2.1
      rw [this] at h2
      norm_num at h2
    · exact ⟨hz1, h.1⟩

theorem isSmoothSubmanifold : PZ.IsSmoothSubmanifold Aset := by
  rintro a (⟨h2, h1⟩ | ⟨h2, h1, h1'⟩)
  · exact ⟨I0 ×ˢ J0, hI0.prod hJ0, ⟨h1, by rw [h2]; exact hc0⟩, _, box0.1, box0.2⟩
  · exact ⟨I1 ×ˢ J1, hI1.prod hJ1, ⟨⟨h1, h1'⟩, by rw [h2]; exact hc1⟩, _, box1.1, box1.2⟩

/-- General position at every point (`d_Z ≡ 0`, `E_z = E`). -/
theorem isGeneralPositionAt {z : Z} (hz : z ∈ Aset) : PZ.IsGeneralPositionAt Aset z := by
  obtain ⟨d, hzd⟩ := (MPolyfold.isSmoothSubmanifold_iff.1 isSmoothSubmanifold) z hz
  have hzχ : z ∈ χ.source := ⟨mem_univ _, mem_univ _⟩
  obtain ⟨n, W, T, hT⟩ := χ.model.isPartialQuadrant
  obtain ⟨y, hy, hys⟩ := exists_smoothLvl_one_of_mem_smooth (d.apply_mem_smooth hχ hz hzd hzχ)
  refine ⟨hz, d, χ, n, W, T, y, hzd, hχ, hzχ, hT, hy, ?_⟩
  obtain ⟨-, -, -, N, hN, hfin⟩ := d.remark_4_2_2 hχ hz hzd hzχ hy
  have hU : IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O :=
    ⟨hPQ, univ, isOpen_univ, by rw [univ_inter]; rfl⟩
  set R := ScRetraction.id hU with hRdef
  have hR : R.retract = χ.model.O := image_id _
  have hRT : R.IsTameWith T := ScRetraction.id_isTame hU n W T hT
  have hmin : minimalSubspaceWith T 0 = ⊤ := by
    ext v
    simp only [Submodule.mem_top, iff_true]
    rw [mem_minimalSubspaceWith]
    intro i
    exact (no_coord T hT i).elim
  unfold MPolyfold.SubmanifoldData.IsGeneralPositionChart
  rw [← hR]
  refine isGeneralPositionRetractAt_of_sup_eq_top T hT hRT (d.toSubData.isScRetract_image χ hχ)
    (fun w _ => by rw [hR]; exact ⟨mem_univ _, mem_univ _⟩) ?_ hys hN (fun v _ => mem_smooth v) ?_
  · rw [ScBanach.mem_lvlSet, hy]
    exact ⟨z, ⟨d.toSubData.mem_shrink χ hz hzd hzχ, hz⟩, rfl⟩
  · rw [hmin, sup_top_eq]

theorem isTameSubmanifold : PZ.IsTameSubmanifold Aset :=
  (MPolyfold.theorem_4_2_7 (prod_rn_isTame rnPolyfold_isTame) isSmoothSubmanifold
    fun a ha => MPolyfold.isGoodPositionAt_of_degIndex_eq_zero isSmoothSubmanifold ha
      (degIndex_zero a)).2

theorem fin_one_eq (i : Fin 1) : i = 0 := Subsingleton.elim i 0

theorem isCompact_closure : IsCompact (closure Aset) := by
  set K : Set Z := (Set.pi univ fun _ => Icc (-2 : ℝ) 2) ×ˢ (Set.pi univ fun _ => Icc (0 : ℝ) 1)
    with hKdef
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hAK : Aset ⊆ K := by
    rintro z (⟨h2, h1⟩ | ⟨h2, h1, h1'⟩)
    · refine ⟨fun i _ => ?_, fun i _ => ?_⟩
      · rw [fin_one_eq i]
        exact ⟨by linarith [(abs_lt.1 h1).1], by linarith [(abs_lt.1 h1).2]⟩
      · rw [h2]; exact ⟨le_refl _, zero_le_one⟩
    · refine ⟨fun i _ => ?_, fun i _ => ?_⟩
      · rw [fin_one_eq i]
        exact ⟨by linarith, h1'.le⟩
      · rw [h2]; exact ⟨zero_le_one, le_refl _⟩
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hAK hK.isClosed)

theorem eucNorm_eq (l : R1) : eucNorm l = |l 0| := by
  unfold eucNorm
  rw [Fin.sum_univ_one, Real.sqrt_sq_eq_abs]

theorem fibres (l : R1) (hl : eucNorm l ≤ 1) :
    IsCompact {z : Z | z ∈ Aset ∧ z.1 = l} ∧ {z : Z | z ∈ Aset ∧ z.1 = l}.Nonempty := by
  rw [eucNorm_eq] at hl
  refine ⟨?_, ⟨(l, 0), Or.inl ⟨rfl, by linarith⟩, rfl⟩⟩
  have hsub : {z : Z | z ∈ Aset ∧ z.1 = l} ⊆ {(l, (0 : R1)), (l, (1 : R1))} := by
    rintro z ⟨h | h, rfl⟩
    · left; exact Prod.ext rfl h.1
    · right; exact Prod.ext rfl h.1
  exact ((Set.toFinite _).subset hsub).isCompact

open Classical in
/-- The neighbourhoods: `U(λ, 1) = {r > λ/2}`, `U(λ, 0) = {x < 1/2}`. -/
def Ucov (z : Z) : Set Z :=
  if z.2 = 1 then {w | z.1 0 / 2 < w.1 0} else {w | w.2 0 < 1 / 2}

theorem pos_of_snd_eq_one {z : Z} (hz : z ∈ Aset) (h : z.2 = 1) : 0 < z.1 0 := by
  rcases hz with h' | h'
  · exact absurd (h'.1.symm.trans h) zero_ne_one'
  · exact h'.2.1

theorem Ucov_spec (z : Z) (hz : z ∈ Aset) : IsOpen (Ucov z) ∧ z ∈ Ucov z := by
  by_cases h : z.2 = 1
  · simp only [Ucov, h, if_true]
    refine ⟨isOpen_lt continuous_const ((continuous_apply 0).comp continuous_fst), ?_⟩
    have := pos_of_snd_eq_one hz h
    change z.1 0 / 2 < z.1 0
    linarith
  · simp only [Ucov, h, if_false]
    refine ⟨isOpen_lt ((continuous_apply 0).comp continuous_snd) continuous_const, ?_⟩
    rcases hz with h' | h'
    · change z.2 0 < 1 / 2
      rw [h'.1]
      norm_num
    · exact absurd h'.1 h

end CE

/-! ### `B` is false -/

theorem not_B : ¬ B := by
  classical
  intro hB
  obtain ⟨S, hS, hcov⟩ := hB CE.R1 (rnPolyfold 1) 1 CE.Aset 1 rnPolyfold_isTame
    ⟨inferInstance, CE.isTameSubmanifold⟩ CE.isCompact_closure one_pos CE.fibres
    (fun z hz => CE.isGeneralPositionAt hz) CE.Ucov (fun z hz _ => CE.Ucov_spec z hz)
  -- a point `(t, 1)`, `0 < t ≤ 1`, below all the `λ/2` of `S`
  set F : Finset ℝ := insert 1 ((S.filter fun z => z.2 = 1).image fun z => z.1 0 / 2) with hF
  have hFne : F.Nonempty := Finset.insert_nonempty _ _
  set t := F.min' hFne with ht
  have htpos : 0 < t := by
    refine (Finset.lt_min'_iff F hFne).2 fun y hy => ?_
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨hzS, hz1⟩ := Finset.mem_filter.1 hz
      have := CE.pos_of_snd_eq_one (hS z hzS).1 hz1
      linarith
  have ht1 : t ≤ 1 := Finset.min'_le F 1 (Finset.mem_insert_self _ _)
  set w : CE.Z := (fun _ => t, 1) with hw
  have hwA : w ∈ CE.Aset := Or.inr ⟨rfl, htpos, by linarith⟩
  have hwε : eucNorm w.1 ≤ 1 := by
    rw [CE.eucNorm_eq]
    change |t| ≤ 1
    rw [abs_of_pos htpos]; exact ht1
  have := hcov ⟨hwA, hwε⟩
  obtain ⟨z, hzS, hwz⟩ := mem_iUnion₂.1 this
  by_cases h : z.2 = 1
  · simp only [CE.Ucov, h, if_true, mem_ofPred_eq] at hwz
    have hle : t ≤ z.1 0 / 2 :=
      Finset.min'_le F _ (Finset.mem_insert_of_mem (Finset.mem_image.2
        ⟨z, Finset.mem_filter.2 ⟨hzS, h⟩, rfl⟩))
    change z.1 0 / 2 < t at hwz
    linarith
  · simp only [CE.Ucov, h, if_false, mem_ofPred_eq] at hwz
    change (1 : ℝ) < 1 / 2 at hwz
    norm_num at hwz

/-- `A → B` is false, since `A` holds. -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B → A` only ex falso. -/
theorem B_to_A : B → A := fun h => (not_B h).elim

#rt_check RoundTrip.V4_64.not_B [Polyfold.theorem_4_3_1_of_subset]
#rt_check RoundTrip.V4_64.B_to_A [Polyfold.theorem_4_3_1_of_subset]
#rt_overlap RoundTrip.V4_64.B_to_A [Polyfold.theorem_4_3_1_of_subset]

end RoundTrip.V4_64
