import Polyfold.Chapter7.ZhouSigma
import Polyfold.Chapter10.ZhouExample

set_option maxSynthPendingDepth 3

/-!
# Remark 10.1.8 (2021, p. 467) and Appendix 10.6.3 (2021, p. 519), on the real scale

The appendix: on `F = ℝ ⊕ L²(ℝ)`, `F_m = ℝ ⊕ H^{m,δ_m}(ℝ)` (`ZhouLine.lineSc`), the retraction
`r(s, f) = (s, π_{|s|} f)` with the `π_t` of Subsection 1.4.4 (`ZhouLine.zhouFam`), its image `Y`,
`G = ℤ/2 = {1, −1}` acting by `(−1) ∗ (s, f) = (s, −f)`, `X = G ⋉ Y`, and
`η(s, f) = (s, f)` for `s ≤ 0`, `(s, −f)` for `s > 0`.

* `isLossFamily_piAbs`: `π_{|s|} = π_s + π_{−s}` is a loss family (F-ch10's `IsLossFamily.add`,
  `IsLossFamily.comp_neg`); `Rt₂` is the sc-smooth retraction `r`, `O₂` its image `Y`.
* `famη s = π_{−s} − π_s` (a loss family, `IsLossFamily.sub`) is `η` in the fibres:
  `ηO_of_nonpos`, `ηO_of_pos` give the printed formula.
* `remark_10_1_8`: `η` is an sc-diffeomorphism of `Y` (its own inverse), fixes `0`,
  `|η(y)| = |y|`, and on no neighbourhood of `0` is it `y ↦ g ∗ y` for one `g ∈ ℤ/2`.
* `not_isLR`: `ℤ/2 ⋉ Y` does not have (LR) (Definition 7.4.19).

F-ch10's `ZhouSigma.remark_10_1_8` is the same statement with Remark 4.1.3's moving projections in
place of `π_t`, and with `η` of the opposite sign convention.
-/

open Set Filter Topology
open scoped InnerProductSpace

namespace Polyfold.EpGroupoid.Examples.ZhouTenSix

open Polyfold.ZhouLine Polyfold.GapP1Sobolev Polyfold.EpGroupoid.Examples.ZhouRetract

noncomputable section

variable (D : Data)

/-! ### `π_{|s|}` and `η` in the fibres -/

/-- `π_{|s|}` on `E_m` (2021 Appendix 10.6.3). -/
def piAbs (s : ℝ) (m : ℕ) : Z D m →L[ℝ] Z D m := zhouFam D.h0 D.hmono D.β |s| m

/-- `η` in the fibres: `π_{−s} − π_s`. -/
def famη (s : ℝ) (m : ℕ) : Z D m →L[ℝ] Z D m :=
  zhouFam D.h0 D.hmono D.β (-s) m - zhouFam D.h0 D.hmono D.β s m

lemma piAbs_eq (s : ℝ) (m : ℕ) :
    piAbs D s m = zhouFam D.h0 D.hmono D.β s m + zhouFam D.h0 D.hmono D.β (-s) m := by
  rcases le_or_gt s 0 with h | h
  · rw [piAbs, abs_of_nonpos h, zhouFam_nonpos D.h0 D.hmono h, zero_add]
  · rw [piAbs, abs_of_pos h, zhouFam_nonpos D.h0 D.hmono (show -s ≤ 0 by linarith), add_zero]

/-- **`π_{|s|}` is a loss family**, so `r(s, f) = (s, π_{|s|} f)` is sc-smooth. -/
theorem isLossFamily_piAbs : IsLossFamily (piAbs D) := by
  have e : piAbs D = fun s m => zhouFam D.h0 D.hmono D.β s m + zhouFam D.h0 D.hmono D.β (-s) m :=
    funext fun s => funext fun m => piAbs_eq D s m
  rw [e]
  exact (isLossFamily_zhouFam D.h0 D.hmono D.hβ).add (isLossFamily_zhouFam D.h0 D.hmono D.hβ).comp_neg

theorem isLossFamily_famη : IsLossFamily (famη D) :=
  (isLossFamily_zhouFam D.h0 D.hmono D.hβ).comp_neg.sub (isLossFamily_zhouFam D.h0 D.hmono D.hβ)

lemma famη_of_nonpos {s : ℝ} (h : s ≤ 0) (m : ℕ) : famη D s m = piAbs D s m := by
  rw [famη, piAbs, abs_of_nonpos h, zhouFam_nonpos D.h0 D.hmono h, sub_zero]

lemma famη_of_pos {s : ℝ} (h : 0 < s) (m : ℕ) : famη D s m = -piAbs D s m := by
  rw [famη, piAbs, abs_of_pos h, zhouFam_nonpos D.h0 D.hmono (show -s ≤ 0 by linarith), zero_sub]

lemma piAbs_idem (s : ℝ) (f : Z D 0) : piAbs D s 0 (piAbs D s 0 f) = piAbs D s 0 f :=
  zhouFam_idem D.h0 D.hmono D.hβ D.hβ2 |s| f

lemma piAbs_famη (s : ℝ) (f : Z D 0) : piAbs D s 0 (famη D s 0 f) = famη D s 0 f := by
  rcases le_or_gt s 0 with h | h
  · rw [famη_of_nonpos D h]; exact piAbs_idem D s f
  · rw [famη_of_pos D h, neg_apply, map_neg, piAbs_idem]

/-! ### The retract `Y` and `X = ℤ/2 ⋉ Y` -/

/-- **The sc-smooth retraction `r(s, f) = (s, π_{|s|} f)`** of `F = ℝ ⊕ E`. -/
def Rt₂ : ScRetraction (E D) univ := (isLossFamily_piAbs D).retraction (piAbs_idem D)

/-- Its image `Y`. -/
abbrev O₂ : Set (E D 0) := (Rt₂ D).retract

lemma mem_O₂_iff (q : E D 0) : q ∈ O₂ D ↔ piAbs D q.1 0 q.2 = q.2 := by
  constructor
  · rintro ⟨p, -, rfl⟩
    exact piAbs_idem D p.1 p.2
  · intro h
    exact ⟨q, mem_univ _, Prod.ext rfl h⟩

lemma smul_mem₂ (k : ℤˣ) (y : O₂ D) : ((y.1.1, c k • y.1.2) : E D 0) ∈ O₂ D := by
  rw [mem_O₂_iff]
  change piAbs D y.1.1 0 (c k • y.1.2) = c k • y.1.2
  rw [map_smul, (mem_O₂_iff D _).1 y.2]

instance : MulAction ℤˣ (O₂ D) where
  smul k y := ⟨(y.1.1, c k • y.1.2), smul_mem₂ D k y⟩
  one_smul y := Subtype.ext (Prod.ext rfl (show c 1 • y.1.2 = y.1.2 by simp [c]))
  mul_smul k l y := Subtype.ext (Prod.ext rfl
    (show c (k * l) • y.1.2 = c k • c l • y.1.2 by simp [c, mul_smul]))

lemma zero_mem₂ : (0 : E D 0) ∈ O₂ D := by rw [mem_O₂_iff]; exact map_zero _

/-- The base point `(0, 0)`. -/
def o₂ : O₂ D := ⟨0, zero_mem₂ D⟩

/-- `Y` as an M-polyfold, with its one chart. -/
def P₂ : MPolyfold (O₂ D) := retractPolyfold (Rt₂ D).isScRetract (o₂ D)

lemma retractChart_symm₂ (q : E D 0) (hq : q ∈ O₂ D) :
    (retractChart (Rt₂ D).isScRetract (o₂ D)).symm q = ⟨q, hq⟩ := by
  classical
  change (if h : q ∈ O₂ D then (⟨q, h⟩ : O₂ D) else o₂ D) = ⟨q, hq⟩
  rw [dif_pos hq]

/-- A self-map of `Y` induced by an sc-smooth map of `F` preserving `Y` is sc-smooth. -/
theorem isScSmoothMap_of_retractMap {f : O₂ D → O₂ D} (hf : Continuous f)
    {g : E D 0 → E D 0} (hg : IsScSmoothRetractMap (E D) univ (O₂ D) (E D) univ (O₂ D) g)
    (hfg : ∀ y : O₂ D, (f y : E D 0) = g y) : (P₂ D).IsScSmoothMap (P₂ D) f := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ hf.continuousOn
    fun y _ => ⟨retractChart (Rt₂ D).isScRetract (o₂ D), retractChart (Rt₂ D).isScRetract (o₂ D),
      univ, isChart_retractChart _ _, isChart_retractChart _ _, isOpen_univ, mem_univ _,
      fun z _ => ⟨mem_univ _, mem_univ _⟩, fun z _ => mem_univ _, ?_⟩
  have heq : EqOn g (⇑(retractChart (Rt₂ D).isScRetract (o₂ D)) ∘ f ∘
      (retractChart (Rt₂ D).isScRetract (o₂ D)).symm) (O₂ D) := by
    intro q hq
    change g q = (f ((retractChart (Rt₂ D).isScRetract (o₂ D)).symm q) : E D 0)
    rw [retractChart_symm₂ D q hq, hfg]
  have h2 : IsScSmoothRetractMap (E D) univ (Subtype.val '' (univ : Set (O₂ D))) (E D) univ
      (O₂ D) (⇑(retractChart (Rt₂ D).isScRetract (o₂ D)) ∘ f ∘
        (retractChart (Rt₂ D).isScRetract (o₂ D)).symm) := by
    rw [Subtype.coe_image_univ]
    exact hg.congr heq
  exact h2

lemma continuous_smul₂ (k : ℤˣ) : Continuous fun y : O₂ D => k • y := by
  change Continuous fun y : O₂ D => (⟨(y.1.1, c k • y.1.2), smul_mem₂ D k y⟩ : O₂ D)
  exact Continuous.subtype_mk ((continuous_subtype_val (p := (· ∈ O₂ D))).fst.prodMk
    ((continuous_subtype_val (p := (· ∈ O₂ D))).snd.const_smul (c k))) _

/-- `ℤ/2` acts on `Y` sc-smoothly. -/
theorem isScSmoothMap_smul₂ (k : ℤˣ) : (P₂ D).IsScSmoothMap (P₂ D) fun y : O₂ D => k • y :=
  isScSmoothMap_of_retractMap D (continuous_smul₂ D k)
    ((scaleOp D (c k)).isScSmoothRetractMap (Rt₂ D).isScRetract
      fun q hq => smul_mem₂ D k ⟨q, hq⟩)
    fun _ => rfl

/-- **The ep-groupoid `X = G ⋉ Y`** (2021 Appendix 10.6.3). -/
abbrev X₂ : EpGroupoid (O₂ D) (ℤˣ × O₂ D) :=
  Examples.actionEpGroupoid (P := P₂ D) (isScSmoothMap_smul₂ D)

/-! ### The map `η` -/

lemma famη_mem (y : E D 0) : ((y.1, famη D y.1 0 y.2) : E D 0) ∈ O₂ D := by
  rw [mem_O₂_iff]; exact piAbs_famη D y.1 y.2

/-- **`η`** (2021 Appendix 10.6.3): `(s, f) ↦ (s, f)` for `s ≤ 0`, `(s, −f)` for `s > 0`. -/
def ηO (y : O₂ D) : O₂ D := ⟨(y.1.1, famη D y.1.1 0 y.1.2), famη_mem D y.1⟩

lemma ηO_of_nonpos (y : O₂ D) (hy : y.1.1 ≤ 0) : ηO D y = y :=
  Subtype.ext (Prod.ext rfl (by
    change famη D y.1.1 0 y.1.2 = y.1.2
    rw [famη_of_nonpos D hy]; exact (mem_O₂_iff D _).1 y.2))

lemma ηO_of_pos (y : O₂ D) (hy : 0 < y.1.1) : ηO D y = (-1 : ℤˣ) • y :=
  Subtype.ext (Prod.ext rfl (by
    change famη D y.1.1 0 y.1.2 = c (-1) • y.1.2
    rw [famη_of_pos D hy, neg_apply, (mem_O₂_iff D _).1 y.2]
    simp [c]))

lemma ηO_ηO (y : O₂ D) : ηO D (ηO D y) = y := by
  rcases le_or_gt y.1.1 0 with hy | hy
  · rw [ηO_of_nonpos D y hy, ηO_of_nonpos D y hy]
  · rw [ηO_of_pos D y hy, ηO_of_pos D _ (show 0 < ((-1 : ℤˣ) • y).1.1 from hy), smul_smul]
    simp

lemma ηO_o₂ : ηO D (o₂ D) = o₂ D := ηO_of_nonpos D _ le_rfl

lemma exists_smul_eq_ηO (y : O₂ D) : ∃ k : ℤˣ, k • y = ηO D y := by
  rcases le_or_gt y.1.1 0 with hy | hy
  · exact ⟨1, by rw [one_smul, ηO_of_nonpos D y hy]⟩
  · exact ⟨-1, (ηO_of_pos D y hy).symm⟩

theorem continuous_ηO : Continuous (ηO D) := by
  have h : Continuous fun q : E D 0 => famη D q.1 0 q.2 := (isLossFamily_famη D).continuous 0
  exact Continuous.subtype_mk ((continuous_subtype_val (p := (· ∈ O₂ D))).fst.prodMk
    (h.comp continuous_subtype_val)) _

theorem isScSmoothMap_ηO : (P₂ D).IsScSmoothMap (P₂ D) (ηO D) := by
  refine isScSmoothMap_of_retractMap D (continuous_ηO D)
    ((isScSmoothRetractMap_iff_exists (Rt₂ D).isScRetract).2
      ⟨fun q _ => famη_mem D q, Rt₂ D, rfl, ?_⟩) fun _ => rfl
  exact IsScSmooth.comp (isScDomain_univ _) (isScDomain_univ _)
    (isLossFamily_famη D).isScSmooth_famRetr (Rt₂ D).isScSmooth (mapsTo_univ _ _)

/-- `η` is an sc-diffeomorphism of `Y`, its own inverse. -/
theorem isScDiffeoOn_ηO : (P₂ D).IsScDiffeoOn (P₂ D) (ηO D) (ηO D) univ univ :=
  ⟨isScSmoothMap_ηO D, isScSmoothMap_ηO D, mapsTo_univ _ _, mapsTo_univ _ _,
    fun y _ => ηO_ηO D y, fun y _ => ηO_ηO D y⟩

/-- `|η(y)| = |y|`. -/
theorem π_ηO (y : O₂ D) : (X₂ D).π (ηO D y) = (X₂ D).π y := by
  obtain ⟨k, hk⟩ := exists_smul_eq_ηO D y
  exact (X₂ D).π_eq_π_iff.2 (GroupoidStr.Isomorphic.symm ⟨(k, y), rfl, hk⟩)

/-! ### `η` is not given by the group near `0` -/

lemma neg_smul_ne {y : O₂ D} (hz : y.1.2 ≠ 0) : (-1 : ℤˣ) • y ≠ y := fun h => hz <| by
  have h1 : c (-1) • y.1.2 = y.1.2 := congrArg (fun p : O₂ D => p.1.2) h
  have h2 : (2 : ℝ) • y.1.2 = 0 := by
    rw [two_smul]; nth_rw 1 [← h1]; simp [c]
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- `1/(n+1)`. -/
def node (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma node_pos (n : ℕ) : 0 < node n := by unfold node; positivity

/-- The points `(±1/(n+1), (1/(n+1)) β(· + e^{n+1}))` of `Y`. -/
def ptσ (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (n : ℕ) : O₂ D :=
  ⟨(σ * node n, node n • w D (node n)), by
    rw [mem_O₂_iff]
    have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
    change zhouFam D.h0 D.hmono D.β |σ * node n| 0 (node n • w D (node n)) = node n • w D (node n)
    rw [abs_mul, hσ1, one_mul, abs_of_pos (node_pos n), map_smul]
    change node n • pi D (node n) (w D (node n)) = _
    rw [pi_w D (node_pos n)]⟩

lemma ptσ_snd_ne (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (n : ℕ) : (ptσ D σ hσ n).1.2 ≠ 0 := fun h =>
  w_ne_zero D (node n) ((smul_eq_zero.1 h).resolve_left (node_pos n).ne')

lemma tendsto_ptσ (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) : Tendsto (ptσ D σ hσ) atTop (𝓝 (o₂ D)) := by
  rw [tendsto_subtype_rng]
  have hnode : Tendsto node atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n => node n • w D (node n)) atTop (𝓝 (0 : Z D 0)) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    have he : (fun n => ‖node n • w D (node n)‖) = node := funext fun n => by
      rw [norm_smul, norm_w, mul_one, Real.norm_eq_abs, abs_of_pos (node_pos n)]
    rw [he]; exact hnode
  have h := (hnode.const_mul σ).prodMk_nhds h2
  rw [mul_zero] at h
  exact h

/-- On no neighbourhood of `0` is `η` the action of one `g ∈ ℤ/2`. -/
theorem exists_ηO_ne_smul {V : Set (O₂ D)} (hV : V ∈ 𝓝 (o₂ D)) (k : ℤˣ) :
    ∃ y ∈ V, ηO D y ≠ k • y := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · obtain ⟨n, hn⟩ := ((tendsto_ptσ D 1 (Or.inl rfl)).eventually hV).exists
    refine ⟨_, hn, ?_⟩
    have hpos : 0 < (ptσ D 1 (Or.inl rfl) n).1.1 := by
      change 0 < 1 * node n; rw [one_mul]; exact node_pos n
    rw [ηO_of_pos D _ hpos, one_smul]
    exact neg_smul_ne D (ptσ_snd_ne D 1 (Or.inl rfl) n)
  · obtain ⟨n, hn⟩ := ((tendsto_ptσ D (-1) (Or.inr rfl)).eventually hV).exists
    refine ⟨_, hn, ?_⟩
    have hneg : (ptσ D (-1) (Or.inr rfl) n).1.1 ≤ 0 := by
      change -1 * node n ≤ 0; have := node_pos n; linarith
    rw [ηO_of_nonpos D _ hneg]
    exact (neg_smul_ne D (ptσ_snd_ne D (-1) (Or.inr rfl) n)).symm

/-- **2021 Remark 10.1.8, p. 467, and Appendix 10.6.3, p. 519, as printed**: for `ℤ/2` acting on
the image `Y` of `r(s, f) = (s, π_{|s|} f)` on `ℝ ⊕ L²(ℝ)`, `F_m = ℝ ⊕ H^{m,δ_m}(ℝ)`, the map
`η` (`f` over `s ≤ 0`, `−f` over `s > 0`) is an sc-diffeomorphism of `Y` fixing `0` with
`|η(y)| = |y|`, and on no neighbourhood of `0` is it `y ↦ g ∗ y` for one `g ∈ ℤ/2`. -/
theorem remark_10_1_8 :
    (P₂ D).IsScDiffeoOn (P₂ D) (ηO D) (ηO D) univ univ ∧ ηO D (o₂ D) = o₂ D ∧
      (∀ y, (X₂ D).π (ηO D y) = (X₂ D).π y) ∧
      ∀ V ∈ 𝓝 (o₂ D), ∀ k : ℤˣ, ∃ y ∈ V, ηO D y ≠ k • y :=
  ⟨isScDiffeoOn_ηO D, ηO_o₂ D, π_ηO D, fun _ hV k => exists_ηO_ne_smul D hV k⟩

/-! ### `ℤ/2 ⋉ Y` does not have (LR) -/

lemma naturalRep_Φ_eq (R : (X₂ D).NaturalRep (o₂ D)) (g : (X₂ D).Isotropy (o₂ D)) {y : O₂ D}
    (hy : y ∈ R.U) : R.Φ g y = g.val.1 • y := by
  have hc : ContinuousOn (fun z => (R.Γ g z).1) R.U :=
    continuous_fst.comp_continuousOn (R.isScSmoothOn_Γ g).continuousOn
  have h1 : (R.Γ g y).1 = (R.Γ g (o₂ D)).1 :=
    R.isConnected_U.isPreconnected.constant hc hy R.mem_U
  rw [R.Γ_self] at h1
  have h2 : (R.Γ g y).2 = y := R.src_Γ g y hy
  rw [← R.tgt_Γ g y hy]
  change (R.Γ g y).1 • (R.Γ g y).2 = _
  rw [h1, h2]

/-- **`ℤ/2 ⋉ Y` does not have the local regularity property** (Definition 7.4.19). -/
theorem not_isLR : ¬ (X₂ D).IsLR := by
  intro h
  obtain ⟨R, -, hR⟩ := h (o₂ D) univ isOpen_univ (mem_univ _)
  let gm : (X₂ D).Isotropy (o₂ D) := ⟨((-1 : ℤˣ), o₂ D), rfl, by
    change (-1 : ℤˣ) • o₂ D = o₂ D
    exact Subtype.ext (Prod.ext rfl (by change c (-1) • (0 : Z D 0) = 0; rw [smul_zero]))⟩
  have hmaps : MapsTo (ηO D) R.U R.U := fun y hy => by
    rcases le_or_gt y.1.1 0 with hy0 | hy0
    · rwa [ηO_of_nonpos D y hy0]
    · rw [ηO_of_pos D y hy0, ← naturalRep_Φ_eq D R gm hy]
      exact R.mapsTo_Φ gm hy
  have hd : (X₂ D).PObj.IsScDiffeoOn (X₂ D).PObj (ηO D) (ηO D) R.U R.U :=
    ⟨(isScSmoothMap_ηO D).mono R.isOpen_U (subset_univ _),
      (isScSmoothMap_ηO D).mono R.isOpen_U (subset_univ _), hmaps, hmaps,
      fun y _ => ηO_ηO D y, fun y _ => ηO_ηO D y⟩
  obtain ⟨g, hg⟩ := hR (ηO D) (ηO D) hd fun y _ => π_ηO D y
  obtain ⟨y, hy, hne⟩ := exists_ηO_ne_smul D (R.isOpen_U.mem_nhds R.mem_U) g.val.1
  exact hne ((hg y hy).trans (naturalRep_Φ_eq D R g hy))

end

end Polyfold.EpGroupoid.Examples.ZhouTenSix
