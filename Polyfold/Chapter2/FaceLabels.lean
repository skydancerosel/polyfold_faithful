import Polyfold.Chapter2.TameBoundary
import Polyfold.Chapter2.FibredProduct

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §2.5,
**Definition 2.5.10** (faces, face-structured M-polyfolds, p. 60).

# Recognising face-structured spaces by labels

## The text

A face of `X` is the closure of a connected component of `{d_X = 1}`; `X` is face-structured if
every `x` lies in exactly `d_X(x)` faces (Definition 2.5.10).

## What is formalized

The criterion is stated for a function `d : X → ℕ` satisfying the corner axioms
(`TameBoundary.IsCornerIndex`, which the degeneracy index of a tame M-polyfold satisfies).

* `TameBoundary.IsFaceLabel d Λ`: `Λ : X → β` is constant on every preconnected subset of
  `{d = 1}` (so it is constant on the components of `{d = 1}`, hence on the faces).
* `TameBoundary.HasRealizedLabels d Λ`: every `x` has `d(x)` distinct labels each of which is
  taken, arbitrarily near `x`, by points with `d = 1`.
* **`TameBoundary.LocalPieces.injective_label`**: under both, the local pieces of `{d = 1}` at `x`
  carry pairwise distinct labels (pigeonhole: `d(x)` pieces cover `{d = 1}` near `x`, and they
  carry all of the `d(x)` labels).
* **`TameBoundary.encard_facesThrough_univ_of_label`**: then every `x` lies in exactly `d(x)`
  faces.  Conversely, if every `x` lies in exactly `d(x)` faces, the component label
  `x ↦ cc_{d = 1}(x)` has both properties (`isFaceLabel_ccLabel`,
  `hasRealizedLabels_ccLabel`).
* `MPolyfold.isFaceStructured_iff_facesThrough`, **`MPolyfold.isFaceStructured_of_label`**,
  `MPolyfold.isFaceStructured_iff_label`: the same for tame M-polyfolds.
* **`MPolyfold.exists_degIndex_eq_zero_of_isTame`**: in a tame M-polyfold the points with
  `d_X = 0` are dense (in a tame chart, `r(φ(x) + t v)` for a vector `v` with positive
  half-line coordinates: tameness (1) of Definition 2.5.2 keeps `d = 0`).
* **`MPolyfold.isFaceStructured_prod`**: the product of two tame face-structured M-polyfolds is
  face-structured, with the label `inl(cc(x))` on `{d_X = 1} × {d_Y = 0}` and `inr(cc(y))` on
  `{d_X = 0} × {d_Y = 1}`.
* `MPolyfold.isFaceStructured_of_degIndex_le_one`: a tame M-polyfold with `d ≤ 1` is
  face-structured (the constant label).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace TameBoundary

universe u v

variable {X : Type u} [TopologicalSpace X] {β : Type v}

section Labels

variable (d : X → ℕ)

/-- `Λ` is **a face label for `d`**: it is constant on every preconnected subset of `{d = 1}`. -/
def IsFaceLabel (Λ : X → β) : Prop :=
  ∀ S ⊆ {y | d y = 1}, IsPreconnected S → ∀ p ∈ S, ∀ q ∈ S, Λ p = Λ q

/-- **The labels at every point are realized**: every `x` has `d(x)` distinct labels, each
taken arbitrarily near `x` by points with `d = 1`. -/
def HasRealizedLabels (Λ : X → β) : Prop :=
  ∀ x, ∃ L : Finset β, L.card = d x ∧ ∀ a ∈ L, ∀ N ∈ 𝓝 x, ∃ w ∈ N, d w = 1 ∧ Λ w = a

variable {d}

/-- A face label is constant on each local piece. -/
theorem IsFaceLabel.eq_of_mem_piece {Λ : X → β} (hΛ : IsFaceLabel d Λ) {x : X} {N : Set X}
    (L : LocalPieces d x N) (i : Fin (d x)) {w : X} (hw : w ∈ L.piece i) :
    Λ w = Λ (L.pt i) :=
  hΛ _ (fun _ hz => (L.piece_subset i hz).2) (L.isPreconnected i) w hw _ (L.pt_mem i)

/-- **The local pieces carry distinct labels** (pigeonhole). -/
theorem LocalPieces.injective_label {Λ : X → β} (hΛ : IsFaceLabel d Λ)
    (hr : HasRealizedLabels d Λ) {x : X} {N : Set X} (L : LocalPieces d x N) :
    Injective fun i => Λ (L.pt i) := by
  classical
  obtain ⟨Ls, hcard, hreal⟩ := hr x
  have hsub : Ls ⊆ Finset.univ.image fun i => Λ (L.pt i) := by
    intro a ha
    obtain ⟨w, hwB, hw1, hwa⟩ := hreal a ha L.B (L.isOpen_B.mem_nhds L.mem_B)
    obtain ⟨i, hi⟩ := mem_iUnion.1 (L.cover ⟨hwB, hw1⟩)
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, by rw [← hwa, hΛ.eq_of_mem_piece L i hi]⟩
  have hle : (Finset.univ : Finset (Fin (d x))).card ≤
      (Finset.univ.image fun i => Λ (L.pt i)).card := by
    have h1 := Finset.card_le_card hsub
    rw [hcard] at h1
    rw [Finset.card_univ, Fintype.card_fin]
    exact h1
  have heq := le_antisymm Finset.card_image_le hle
  exact fun i j hij => Finset.card_image_iff.1 heq (Finset.mem_coe.2 (Finset.mem_univ i))
    (Finset.mem_coe.2 (Finset.mem_univ j)) hij

variable (hd : IsCornerIndex d)
include hd

/-- **Distinct labels give distinct faces**: if `Λ` is a face label whose labels are realized at
every point, then every `x` lies in exactly `d(x)` faces of `X`. -/
theorem encard_facesThrough_univ_of_label {Λ : X → β} (hΛ : IsFaceLabel d Λ)
    (hr : HasRealizedLabels d Λ) (x : X) :
    (facesThrough d univ x).encard = d x := by
  obtain ⟨L⟩ := hd.exists_localPieces (univ_mem : univ ∈ 𝓝 x)
  rw [L.encard_facesThrough_eq_iff hd isOpen_univ (mem_univ x)]
  intro i j hij
  have hj1 : d (L.pt j) = 1 := (L.piece_subset j (L.pt_mem j)).2
  have hmem := (faceAt_eq_faceAt_iff hd isOpen_univ (mem_univ _) hj1).1 hij
  refine L.injective_label hΛ hr ?_
  exact hΛ _ (fun _ hz => (connectedComponentIn_subset _ _ hz).2)
    isPreconnected_connectedComponentIn _
    (mem_connectedComponentIn (show L.pt i ∈ univ ∩ {y | d y = 1} from
      ⟨mem_univ _, (L.piece_subset i (L.pt_mem i)).2⟩)) _ hmem

omit hd

/-- The component label `x ↦ cc_{d = 1}(x)`. -/
def ccLabel (d : X → ℕ) (x : X) : Set X := connectedComponentIn {y | d y = 1} x

theorem isFaceLabel_ccLabel : IsFaceLabel d (ccLabel d) := by
  intro S hS hSc p hp q hq
  change connectedComponentIn _ p = connectedComponentIn _ q
  exact connectedComponentIn_eq (hSc.subset_connectedComponentIn hp hS hq)

include hd in
/-- **Face-structured ⇒ the component labels are realized.** -/
theorem hasRealizedLabels_ccLabel (h : ∀ x, (facesThrough d univ x).encard = d x) :
    HasRealizedLabels d (ccLabel d) := by
  classical
  intro x
  obtain ⟨L⟩ := hd.exists_localPieces (univ_mem : univ ∈ 𝓝 x)
  have hinj := (L.encard_facesThrough_eq_iff hd isOpen_univ (mem_univ x)).1 (h x)
  have hinj' : Injective fun i => ccLabel d (L.pt i) := by
    intro i j hij
    refine hinj ?_
    simp only [faceAt, univ_inter]
    exact congrArg closure hij
  refine ⟨Finset.univ.image fun i => ccLabel d (L.pt i), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj', Finset.card_univ, Fintype.card_fin]
  · intro a ha N hN
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨w, hwN, hwi⟩ := mem_closure_iff_nhds.1 (L.mem_closure i) N hN
    exact ⟨w, hwN, (L.piece_subset i hwi).2, isFaceLabel_ccLabel.eq_of_mem_piece L i hwi⟩

end Labels

end TameBoundary

namespace MPolyfold

open TameBoundary

universe u v w

section FaceStructured

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- Definition 2.5.10 in the form of `TameBoundary.facesThrough` for the open set `X`. -/
theorem isFaceStructured_iff_facesThrough :
    P.IsFaceStructured ↔ ∀ x, (facesThrough P.degIndex univ x).encard = P.degIndex x := by
  have : ∀ x, {F : Set X | P.IsFace F ∧ x ∈ F} = facesThrough P.degIndex univ x := fun x => by
    ext F
    simp only [facesThrough, mem_ofPred_eq, isFaceIn_univ_iff]
  simp only [IsFaceStructured, this]

/-- **A face label with realized labels shows that a tame M-polyfold is face-structured.** -/
theorem isFaceStructured_of_label (hP : P.IsTame) {β : Type v} {Λ : X → β}
    (hΛ : IsFaceLabel P.degIndex Λ) (hr : HasRealizedLabels P.degIndex Λ) :
    P.IsFaceStructured :=
  isFaceStructured_iff_facesThrough.2
    (encard_facesThrough_univ_of_label (P.isCornerIndex_degIndex hP) hΛ hr)

/-- A tame M-polyfold is face-structured iff the component labels are realized. -/
theorem isFaceStructured_iff_label (hP : P.IsTame) :
    P.IsFaceStructured ↔ HasRealizedLabels P.degIndex (ccLabel P.degIndex) :=
  ⟨fun h => hasRealizedLabels_ccLabel (P.isCornerIndex_degIndex hP)
      (isFaceStructured_iff_facesThrough.1 h),
    fun h => isFaceStructured_of_label hP isFaceLabel_ccLabel h⟩

/-- **A tame M-polyfold with `d ≤ 1` is face-structured**: the constant label (a point with
`d = 1` has one local piece, so it lies in one face). -/
theorem isFaceStructured_of_degIndex_le_one (hP : P.IsTame) (hle : ∀ x, P.degIndex x ≤ 1) :
    P.IsFaceStructured := by
  classical
  refine isFaceStructured_of_label hP (Λ := fun _ : X => ()) (fun _ _ _ _ _ _ _ => rfl) ?_
  intro x
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hle x) with h0 | h1
  · exact ⟨∅, by rw [h0]; rfl, fun a ha => absurd ha (Finset.notMem_empty a)⟩
  · refine ⟨{()}, by rw [h1]; rfl, fun a _ N hN => ⟨x, mem_of_mem_nhds hN, h1, rfl⟩⟩

end FaceStructured

/-! ### Density of the points with `d = 0` -/

section Density

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **In a tame M-polyfold the points with `d_X = 0` are dense**: every neighbourhood of `x`
contains a point `y` with `d_X(y) = 0`.  *Proof*: in a tame chart `φ` with tame retraction `r`
and presentation `T` of `C`, the points `e_t = φ(x) + t T⁻¹(1, 0)` (`t > 0`) lie in `C` with no
vanishing half-line coordinate; `r` keeps `d_C` (Definition 2.5.2 (1)), and
`φ⁻¹(r(e_t)) → x`. -/
theorem exists_degIndex_eq_zero_of_isTame (hP : P.IsTame) (x : X) {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ y ∈ N, P.degIndex y = 0 := by
  obtain ⟨φ, hφ, hx, R, hRO, hRt⟩ := IsTame.exists_chart P hP x
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hR := hRt n W T hT
  set e := φ x with he
  have heO : e ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model x hx
  have heU : e ∈ R.U := R.retract_subset heO
  have hRe : R e = e := R.apply_eq_self_of_mem_retract heO
  have hRc : ContinuousOn R R.U := R.isSc1.isSc0.continuousOn_base
  have hRO' : ∀ z ∈ R.U, R z ∈ φ.model.O := fun z hz => by rw [← hRO]; exact R.apply_mem_retract hz
  have hcomp : ContinuousWithinAt (fun z => φ.symm (R z)) R.U e :=
    (φ.continuousOn_invFun (R e) (hRO' e heU)).comp (hRc e heU) hRO'
  have hsy : φ.symm (R e) = x := by rw [hRe]; exact φ.symm_apply_apply hx
  obtain ⟨O₀, hO₀, hUO₀⟩ := R.relOpen.relOpen
  have hG4 : ∀ᶠ z in 𝓝 e, z ∈ R.U → φ.symm (R z) ∈ N := by
    have := hcomp.tendsto (hsy.symm ▸ hN : N ∈ 𝓝 (φ.symm (R e)))
    obtain ⟨t, ht, hte, hts⟩ := mem_nhdsWithin.1 this
    exact Filter.mem_of_superset (ht.mem_nhds hte) fun z hz hzU => hts ⟨hz, hzU⟩
  have heO₀ : e ∈ O₀ := (hUO₀ ▸ heU).1
  set v : φ.model.E 0 := coordVec T fun _ => 1 with hv
  set g : ℝ → φ.model.E 0 := fun t => e + t • v with hg
  have hgc : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
  have hg0 : g 0 = e := by simp [hg]
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t ∈ O₀ ∧ (g t ∈ R.U → φ.symm (R (g t)) ∈ N) := by
    have h1 : ∀ᶠ z in 𝓝 e, z ∈ O₀ ∧ (z ∈ R.U → φ.symm (R z) ∈ N) :=
      (show ∀ᶠ z in 𝓝 e, z ∈ O₀ from hO₀.mem_nhds heO₀).and hG4
    exact nhdsWithin_le_nhds ((hg0 ▸ hgc.tendsto 0).eventually h1)
  obtain ⟨t, ⟨htO, htN⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht0' : (0 : ℝ) < t := ht0
  have hcoord : ∀ l, (T 0 (g t)).1 l = (T 0 e).1 l + t := fun l => by
    have h := coord_coordVec (T := T) (fun _ : Fin n => (1 : ℝ)) l
    simp only [hg, map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at h ⊢
    rw [h, mul_one]
  have heC : e ∈ φ.model.C := φ.apply_mem_C hx
  have hgC : g t ∈ φ.model.C := by
    rw [hT]
    intro l
    rw [hcoord l]
    exact add_nonneg (coord_nonneg hT heC l) ht0'.le
  have hgU : g t ∈ R.U := hUO₀ ▸ ⟨htO, hgC⟩
  refine ⟨φ.symm (R (g t)), htN hgU, ?_⟩
  have hys : φ.symm (R (g t)) ∈ φ.source := φ.symm_mapsTo (hRO' _ hgU)
  rw [P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hys, chartDegIndex,
    φ.apply_symm_apply (hRO' _ hgU), hR.degIndex_apply _ hgU, degIndex_eq T hT hgC,
    degIndexWith_eq_card_zeroSet, Finset.card_eq_zero]
  refine Finset.eq_empty_of_forall_notMem fun l hl => ?_
  rw [mem_zeroSet, hcoord l] at hl
  linarith [coord_nonneg hT heC l]

end Density

/-! ### Products -/

section Product

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type w} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  [ParacompactSpace (X × Y)]

omit [T2Space X] [ParacompactSpace X] in
lemma isOpen_degIndex_le_of_eventually {d : X → ℕ} (h : ∀ x, ∀ᶠ y in 𝓝 x, d y ≤ d x) (k : ℕ) :
    IsOpen {x | d x ≤ k} :=
  isOpen_iff_mem_nhds.2 fun x hx => (h x).mono fun _ hy => le_trans hy hx

/-- The product label: `inl(cc(x))` where `d_X(x) = 1`, else `inr(cc(y))`. -/
def prodLabel (P : MPolyfold X) (Q : MPolyfold Y) (p : X × Y) : Set X ⊕ Set Y :=
  if P.degIndex p.1 = 1 then Sum.inl (ccLabel P.degIndex p.1) else Sum.inr (ccLabel Q.degIndex p.2)

theorem isFaceLabel_prodLabel (hP : P.IsTame) (hQ : Q.IsTame) :
    IsFaceLabel (P.prod Q).degIndex (prodLabel P Q) := by
  have hd := (isTame_prod P Q hP hQ).2
  intro S hS hSc p hp q hq
  have hK1 : IsClosed {r : X × Y | 1 ≤ P.degIndex r.1} := by
    have := (isOpen_degIndex_le_of_eventually (d := P.degIndex)
      (fun x => lemma_2_4_3 P x) 0).preimage
      (continuous_fst : Continuous (Prod.fst : X × Y → X))
    convert this.isClosed_compl using 1
    ext r
    change 1 ≤ P.degIndex r.1 ↔ ¬ (P.degIndex r.1 ≤ 0)
    omega
  have hK2 : IsClosed {r : X × Y | 1 ≤ Q.degIndex r.2} := by
    have := (isOpen_degIndex_le_of_eventually (d := Q.degIndex)
      (fun x => lemma_2_4_3 Q x) 0).preimage
      (continuous_snd : Continuous (Prod.snd : X × Y → Y))
    convert this.isClosed_compl using 1
    ext r
    change 1 ≤ Q.degIndex r.2 ↔ ¬ (Q.degIndex r.2 ≤ 0)
    omega
  have hsum : ∀ r ∈ S, P.degIndex r.1 + Q.degIndex r.2 = 1 := fun r hr => by
    rw [← hd r.1 r.2]; exact hS hr
  have hcov : S ⊆ {r : X × Y | 1 ≤ P.degIndex r.1} ∪ {r : X × Y | 1 ≤ Q.degIndex r.2} := by
    intro r hr
    have := hsum r hr
    by_cases h : 1 ≤ P.degIndex r.1
    · exact Or.inl h
    · exact Or.inr (show 1 ≤ Q.degIndex r.2 by omega)
  have hdisj : S ∩ ({r : X × Y | 1 ≤ P.degIndex r.1} ∩ {r : X × Y | 1 ≤ Q.degIndex r.2}) = ∅ := by
    refine eq_empty_of_forall_notMem fun r ⟨hr, h1, h2⟩ => ?_
    have := hsum r hr
    simp only [mem_ofPred_eq] at h1 h2
    omega
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hSc _ _ hK1 hK2 hcov hdisj with h | h
  · have h1 : ∀ r ∈ S, P.degIndex r.1 = 1 := fun r hr => by
      have := hsum r hr; have := h hr; simp only [mem_ofPred_eq] at this; omega
    have hS1 : Prod.fst '' S ⊆ {x | P.degIndex x = 1} := by
      rintro _ ⟨r, hr, rfl⟩; exact h1 r hr
    simp only [prodLabel, h1 p hp, h1 q hq, if_true]
    exact congrArg Sum.inl (isFaceLabel_ccLabel _ hS1 (hSc.image _ continuous_fst.continuousOn)
      _ (mem_image_of_mem _ hp) _ (mem_image_of_mem _ hq))
  · have h1 : ∀ r ∈ S, Q.degIndex r.2 = 1 := fun r hr => by
      have := hsum r hr; have := h hr; simp only [mem_ofPred_eq] at this; omega
    have h0 : ∀ r ∈ S, P.degIndex r.1 ≠ 1 := fun r hr => by
      have := hsum r hr; have := h1 r hr; omega
    have hS1 : Prod.snd '' S ⊆ {y | Q.degIndex y = 1} := by
      rintro _ ⟨r, hr, rfl⟩; exact h1 r hr
    simp only [prodLabel, h0 p hp, h0 q hq, if_false]
    exact congrArg Sum.inr (isFaceLabel_ccLabel _ hS1 (hSc.image _ continuous_snd.continuousOn)
      _ (mem_image_of_mem _ hp) _ (mem_image_of_mem _ hq))

theorem hasRealizedLabels_prodLabel (hP : P.IsTame) (hQ : Q.IsTame) (hPf : P.IsFaceStructured)
    (hQf : Q.IsFaceStructured) : HasRealizedLabels (P.prod Q).degIndex (prodLabel P Q) := by
  classical
  have hd := (isTame_prod P Q hP hQ).2
  have hPc := P.isCornerIndex_degIndex hP
  have hQc := Q.isCornerIndex_degIndex hQ
  rintro ⟨x, y⟩
  obtain ⟨LP⟩ := hPc.exists_localPieces (univ_mem : univ ∈ 𝓝 x)
  obtain ⟨LQ⟩ := hQc.exists_localPieces (univ_mem : univ ∈ 𝓝 y)
  have hiP : Injective fun i => ccLabel P.degIndex (LP.pt i) :=
    LP.injective_label isFaceLabel_ccLabel
      (hasRealizedLabels_ccLabel hPc (isFaceStructured_iff_facesThrough.1 hPf))
  have hiQ : Injective fun j => ccLabel Q.degIndex (LQ.pt j) :=
    LQ.injective_label isFaceLabel_ccLabel
      (hasRealizedLabels_ccLabel hQc (isFaceStructured_iff_facesThrough.1 hQf))
  set g : Fin (P.degIndex x) ⊕ Fin (Q.degIndex y) → Set X ⊕ Set Y :=
    Sum.map (fun i => ccLabel P.degIndex (LP.pt i)) (fun j => ccLabel Q.degIndex (LQ.pt j))
    with hg
  have hginj : Injective g := Sum.map_injective.2 ⟨hiP, hiQ⟩
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hginj, Finset.card_univ, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin, hd]
  · intro a ha N hN
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 hN
    rcases c with i | j
    · obtain ⟨x', hx'U, hx'i⟩ := mem_closure_iff_nhds.1 (LP.mem_closure i) U hU
      obtain ⟨y', hy'V, hy'0⟩ := exists_degIndex_eq_zero_of_isTame Q hQ y hV
      have hx'1 : P.degIndex x' = 1 := (LP.piece_subset i hx'i).2
      refine ⟨(x', y'), hUV ⟨hx'U, hy'V⟩, by rw [hd, hx'1, hy'0], ?_⟩
      simp only [prodLabel, hx'1, if_true, hg, Sum.map_inl]
      exact congrArg Sum.inl (isFaceLabel_ccLabel.eq_of_mem_piece LP i hx'i)
    · obtain ⟨y', hy'V, hy'j⟩ := mem_closure_iff_nhds.1 (LQ.mem_closure j) V hV
      obtain ⟨x', hx'U, hx'0⟩ := exists_degIndex_eq_zero_of_isTame P hP x hU
      have hy'1 : Q.degIndex y' = 1 := (LQ.piece_subset j hy'j).2
      refine ⟨(x', y'), hUV ⟨hx'U, hy'V⟩, by rw [hd, hx'0, hy'1], ?_⟩
      simp only [prodLabel, hx'0, zero_ne_one, if_false, hg, Sum.map_inr]
      exact congrArg Sum.inr (isFaceLabel_ccLabel.eq_of_mem_piece LQ j hy'j)

/-- **The product of two tame face-structured M-polyfolds is face-structured** (Definition
2.5.10): the faces of `X × Y` are `F × Y` and `X × G` for the faces `F` of `X` and `G` of `Y`
(here only the count is proved, through `prodLabel`). -/
theorem isFaceStructured_prod (hP : P.IsTame) (hQ : Q.IsTame) (hPf : P.IsFaceStructured)
    (hQf : Q.IsFaceStructured) : (P.prod Q).IsFaceStructured :=
  isFaceStructured_of_label (isTame_prod P Q hP hQ).1 (isFaceLabel_prodLabel hP hQ)
    (hasRealizedLabels_prodLabel hP hQ hPf hQf)

end Product

end MPolyfold

end Polyfold
