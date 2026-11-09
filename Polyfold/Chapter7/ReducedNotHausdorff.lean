import Polyfold.Chapter4.RemarkFourThreeFamily
import Polyfold.Chapter7.NonVacuity
import Polyfold.Chapter7.Reduced

-- the instances of `c₀ →L[ℝ] c₀` need a deeper instance search (as in `RemarkFourThreeFamily.lean`)
set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 7: **Propositions 7.9 and 7.10** (pp. 242–244), "the subset `𝐗^R` … has a natural
M-polyfold structure" and "`X_R` is an effective ep-groupoid".  There is no 2014 preprint of
Part II; numbers and pages are the 2017 text's.

# `𝐗^R` need not be Hausdorff

## The text, paraphrased

(Definition 7.2.7 (2017: 7.12), p. 310 (2017 p. 241)) `𝐗^T ⊆ 𝐗` is the set of morphisms `φ` near which `s = t`, i.e.
`φ ∈ T_{s(φ)}`; `φ ∼ ψ` if `s(φ) = s(ψ)` and `ψ = φ ∘ τ` for some `τ ∈ 𝐗^T`; `𝐗^R = 𝐗/∼` with
the quotient topology.  (Proposition 7.2.10 (2017: 7.9), p. 313 (2017 p. 242)) `𝐗^R` has a natural M-polyfold structure for
which the quotient map is a local sc-diffeomorphism.  (Proposition 7.10, p. 244) `X_R = (X, 𝐗^R)`
is an effective ep-groupoid.

## What is formalized

An M-polyfold is Hausdorff (Part I, Definition 2.3.4 (2017: 2.8)).  `Reduced.lean` proves Propositions 7.2.10 (2017: 7.9) and
7.10 with `[T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]` as hypotheses (gap G.71).  This
file shows that the Hausdorff hypothesis cannot be dropped:

* `O` (`JumpingRetract.O`) is the sc-retract of Remark 4.3's family of moving rank-one projections
  (`RemarkFourThree.fam`, `RemarkFourThreeFamily.lean`): `O = {(t, z) | L(t) z = z}` in `ℝ ⊕ X`,
  which is `{(t, 0)}` over `t ≤ 0` and a line over each `t > 0`, a retract whose dimension jumps.
  It is an M-polyfold with its one chart (`retractPolyfold`).
* `ℤ/2 = ℤˣ` acts on `O` by `(t, z) ↦ (t, ±z)`, the restriction of an sc-operator, hence
  sc-smoothly (`isScSmoothMap_smul`); `JumpingRetract.X` is the translation ep-groupoid
  `ℤ/2 ⋉ O` (`Examples.actionEpGroupoid`).
* Over `t < 0` both elements act trivially, so `(−1, y_n) ∈ 𝐗^T` for `y_n = (−1/(n+1), 0)` and
  `[(−1, y_n)] = [(1, y_n)]` in `𝐗^R` (`reducedπ_eq`).  But `(−1, (0, 0)) ∉ 𝐗^T`, because the
  points `o_k = (1/(k+1), (1/(k+1)) e_{n_k}) ∈ O` tend to `0` and are moved by `−1`
  (`not_mem_nonEffectivePart`), so `[(−1, 0)] ≠ [(1, 0)]` (`reducedπ_ne`).  The sequence
  `[(±1, y_n)]` converges to both: `𝐗^R` is not Hausdorff (`not_t2Space_reducedMor`).
* `exists_not_t2Space_reducedMor`: an ep-groupoid whose `𝐗^R` is not Hausdorff.  As we read
  them, Propositions 7.9 and 7.10 therefore need a hypothesis the text does not state; the
  hypotheses of `Reduced.lean` (satisfiable, e.g. for effective `X`,
  `t2Space_reducedMor_of_isEffective`) are exactly what is missing (`RoundTrip/Items/V7_40.lean`,
  `A_to_B_of_hyp`).

## What the text leaves implicit, and the choices made

* The example is the one sketched in `PLAN.md`, II.6, item 2; it was first proved in the
  round-trip audit (`RoundTrip/Items/V7_40.lean`, namespace `NotB`) and moved here unchanged.
* Whether `𝐗^R` is always paracompact is not decided; without Hausdorffness it is not an
  M-polyfold either way.
-/

open Set Filter Topology

namespace Polyfold

namespace EpGroupoid

namespace Examples

namespace JumpingRetract

open Polyfold.RemarkFourThree

noncomputable section

/-- The sc-Banach space `ℝ ⊕ X` of Remark 4.3's example. -/
abbrev E : ScBanach := (ScBanach.const ℝ).prod ScOneExample.X

/-- The sc-smooth retraction `(t, z) ↦ (t, L(t) z)` (Remark 4.3's moving projections). -/
def Rt : ScRetraction E univ := isLossFamily_fam.retraction fun t y => fam_idem t y

/-- The retract `O = r(ℝ ⊕ X)`: `{(t, 0)}` over `t ≤ 0`, a line over each `t > 0`. -/
abbrev O : Set (E 0) := Rt.retract

lemma Rt_apply (q : E 0) : Rt q = (q.1, fam q.1 0 q.2) := rfl

lemma mem_O_iff (q : E 0) : q ∈ O ↔ fam q.1 0 q.2 = q.2 := by
  constructor
  · rintro ⟨p, -, rfl⟩
    exact fam_idem p.1 p.2
  · intro h
    exact ⟨q, mem_univ _, Prod.ext rfl h⟩

example : T2Space O := inferInstance
example : ParacompactSpace O := inferInstance

/-- `±1` as a real number. -/
def c (k : ℤˣ) : ℝ := ((k : ℤ) : ℝ)

lemma smul_mem (k : ℤˣ) (y : O) : ((y.1.1, c k • y.1.2) : E 0) ∈ O := by
  rw [mem_O_iff]
  change fam y.1.1 0 (c k • y.1.2) = c k • y.1.2
  rw [map_smul, (mem_O_iff _).1 y.2]

/-- `k • (t, z) = (t, ±z)`. -/
def smulO (k : ℤˣ) (y : O) : O := ⟨(y.1.1, c k • y.1.2), smul_mem k y⟩

instance : MulAction ℤˣ O where
  smul := smulO
  one_smul y := Subtype.ext (Prod.ext rfl (show c 1 • y.1.2 = y.1.2 by simp [c]))
  mul_smul k l y := Subtype.ext (Prod.ext rfl
    (show c (k * l) • y.1.2 = c k • c l • y.1.2 by simp [c, mul_smul]))

lemma smul_val (k : ℤˣ) (y : O) : ((k • y : O) : E 0) = (y.1.1, c k • y.1.2) := rfl

lemma zero_mem : (0 : E 0) ∈ O := by rw [mem_O_iff]; exact map_zero _

/-- The base point `(0, 0)` of `O`. -/
def o₀ : O := ⟨0, zero_mem⟩

/-- `O` as an M-polyfold, with its one chart. -/
def P : MPolyfold O := retractPolyfold Rt.isScRetract o₀

/-- `(t, z) ↦ (t, r z)` on `E`. -/
def scaleOp (r : ℝ) : ScOperator E E :=
  ScOperator.prodMap (ScOperator.id _)
    { lvl := fun m => r • ContinuousLinearMap.id ℝ _
      incl_comm := fun m x => by simp }

example (r : ℝ) (q : E 0) : scaleOp r 0 q = (q.1, r • q.2) := rfl

lemma continuous_smulO (k : ℤˣ) : Continuous fun y : O => k • y := by
  change Continuous fun y : O => (⟨(y.1.1, c k • y.1.2), smul_mem k y⟩ : O)
  exact Continuous.subtype_mk ((continuous_subtype_val (p := (· ∈ O))).fst.prodMk
    ((continuous_subtype_val (p := (· ∈ O))).snd.const_smul (c k))) _

/-- `ℤ/2` acts on `O` sc-smoothly: `(t, z) ↦ (t, ±z)` is the restriction of an sc-operator. -/
theorem isScSmoothMap_smul (k : ℤˣ) : P.IsScSmoothMap P fun y : O => k • y := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ (continuous_smulO k).continuousOn
    fun y _ => ⟨retractChart Rt.isScRetract o₀, retractChart Rt.isScRetract o₀, univ,
      isChart_retractChart _ _, isChart_retractChart _ _, isOpen_univ, mem_univ _,
      fun z _ => ⟨mem_univ _, mem_univ _⟩, fun z _ => mem_univ _, ?_⟩
  have key : IsScSmoothRetractMap E univ O E univ O (scaleOp (c k) 0) :=
    (scaleOp (c k)).isScSmoothRetractMap Rt.isScRetract (fun q hq => smul_mem k ⟨q, hq⟩)
  have heq : EqOn (scaleOp (c k) 0) (⇑(retractChart Rt.isScRetract o₀) ∘ (fun y : O => k • y) ∘
      (retractChart Rt.isScRetract o₀).symm) O := by
    intro q hq
    have hs : (retractChart Rt.isScRetract o₀).symm q = ⟨q, hq⟩ := by
      classical
      change (if h : q ∈ O then (⟨q, h⟩ : O) else o₀) = ⟨q, hq⟩
      rw [dif_pos hq]
    change (q.1, c k • q.2) = ((k • (retractChart Rt.isScRetract o₀).symm q : O) : E 0)
    rw [hs]
    rfl
  have h2 : IsScSmoothRetractMap E univ (Subtype.val '' (univ : Set O)) E univ O
      (⇑(retractChart Rt.isScRetract o₀) ∘ (fun y : O => k • y) ∘
        (retractChart Rt.isScRetract o₀).symm) := by
    rw [Subtype.coe_image_univ]
    exact key.congr heq
  exact h2

/-- **The ep-groupoid `ℤ/2 ⋉ O`**: `ℤ/2 = ℤˣ` acting on the retract `O` by `(t, z) ↦ (t, ±z)`. -/
abbrev X : EpGroupoid O (ℤˣ × O) :=
  Examples.actionEpGroupoid (P := P) isScSmoothMap_smul

/-- Over `t ≤ 0` the retract is `{(t, 0)}`, where `±1` act trivially. -/
lemma smul_eq_self_of_nonpos (k : ℤˣ) (p : O) (hp : p.1.1 ≤ 0) : k • p = p := by
  have h2 : p.1.2 = 0 := by
    rw [← (mem_O_iff _).1 p.2, fam_of_nonpos hp]
    rfl
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change c k • p.1.2 = p.1.2
  rw [h2, smul_zero]

/-- The points `y_n = (−1/(n+1), 0)` of `O`. -/
def yn (n : ℕ) : O := ⟨(-(node n), 0), by rw [mem_O_iff]; exact map_zero _⟩

lemma tendsto_yn : Tendsto yn atTop (𝓝 o₀) := by
  rw [tendsto_subtype_rng]
  have hnode : Tendsto node atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have := hnode.neg.prodMk_nhds (tendsto_const_nhds (x := (0 : ScOneExample.X 0)))
  rw [neg_zero] at this
  exact this

/-- `(−1, y_n) ∈ 𝐗^T`: `s = t` near it. -/
lemma mem_nonEffectivePart (n : ℕ) : ((-1 : ℤˣ), yn n) ∈ X.nonEffectivePart := by
  rw [EpGroupoid.mem_nonEffectivePart_iff]
  have ho : IsOpen {q : ℤˣ × O | q.2.1.1 < 0} :=
    isOpen_lt (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)) continuous_const
  filter_upwards [ho.mem_nhds (show (yn n).1.1 < 0 from neg_neg_of_pos (node_pos n))] with q hq
  exact (smul_eq_self_of_nonpos q.1 q.2 (le_of_lt hq)).symm

/-- `(−1, 0) ∉ 𝐗^T`: the points `o_k = (1/(k+1), (1/(k+1)) e_{n_k}) ∈ O` tend to `0`, and `−1`
moves them. -/
lemma not_mem_nonEffectivePart : ((-1 : ℤˣ), o₀) ∉ X.nonEffectivePart := by
  rw [EpGroupoid.mem_nonEffectivePart_iff]
  intro h
  have hmem : ∀ k, pt k ∈ O := fun k =>
    ⟨pt k, mem_univ _, Prod.ext rfl (fam_node_smul_δv k (node k))⟩
  have hnode : Tendsto node atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpt : Tendsto (fun k => (⟨pt k, hmem k⟩ : O)) atTop (𝓝 o₀) := by
    rw [tendsto_subtype_rng]
    refine (hnode.prodMk_nhds ?_)
    refine tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun k => ?_) hnode)
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (node_pos k)]
    exact mul_le_of_le_one_right (node_pos k).le (norm_δv_le _)
  have h2 : Tendsto (fun k => ((-1 : ℤˣ), (⟨pt k, hmem k⟩ : O))) atTop
      (𝓝 ((-1 : ℤˣ), o₀)) := tendsto_const_nhds.prodMk_nhds hpt
  obtain ⟨k, hk⟩ := (h2.eventually h).exists
  have hk' : (pt k).2 = c (-1) • (pt k).2 := congrArg (fun p : O => p.1.2) hk
  have hv := congrArg (fun z : ScOneExample.c0 => z (nk k)) hk'
  simp only [pt, c, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_smul, one_smul,
    ZeroAtInftyContinuousMap.coe_neg, ZeroAtInftyContinuousMap.coe_smul, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, δv_apply] at hv
  simp only [ite_true, mul_one] at hv
  have := node_pos k
  linarith

lemma reducedπ_eq (n : ℕ) :
    X.reducedπ ((-1 : ℤˣ), yn n) = X.reducedπ ((1 : ℤˣ), yn n) := by
  rw [EpGroupoid.reducedπ_eq_iff, EpGroupoid.reducedRel_iff]
  refine ⟨((-1 : ℤˣ), yn n), mem_nonEffectivePart n, ?_, ?_⟩
  · change yn n = (-1 : ℤˣ) • yn n
    exact (smul_eq_self_of_nonpos _ _ (neg_nonpos.2 (node_pos n).le)).symm
  · change ((-1 : ℤˣ), yn n) = ((1 : ℤˣ) * (-1), yn n)
    rw [one_mul]

lemma reducedπ_ne : X.reducedπ ((-1 : ℤˣ), o₀) ≠ X.reducedπ ((1 : ℤˣ), o₀) := by
  rw [Ne, EpGroupoid.reducedπ_eq_iff, EpGroupoid.reducedRel_iff]
  rintro ⟨k, hk, -, he⟩
  have he' : ((-1 : ℤˣ), o₀) = ((1 : ℤˣ) * k.1, k.2) := he
  rw [one_mul] at he'
  have hk' : k = ((-1 : ℤˣ), o₀) := he'.symm
  exact not_mem_nonEffectivePart (hk' ▸ hk)

/-- **`𝐗^R` is not Hausdorff** for `ℤ/2 ⋉ O`: the classes of `(±1, y_n)` converge to both
`[(−1, 0)] ≠ [(1, 0)]`. -/
theorem not_t2Space_reducedMor : ¬ T2Space X.ReducedMor := by
  intro _
  have h1 : Tendsto (fun n => X.reducedπ ((-1 : ℤˣ), yn n)) atTop
      (𝓝 (X.reducedπ ((-1 : ℤˣ), o₀))) :=
    (X.continuous_reducedπ.tendsto _).comp (tendsto_const_nhds.prodMk_nhds tendsto_yn)
  have h2 : Tendsto (fun n => X.reducedπ ((1 : ℤˣ), yn n)) atTop
      (𝓝 (X.reducedπ ((1 : ℤˣ), o₀))) :=
    (X.continuous_reducedπ.tendsto _).comp (tendsto_const_nhds.prodMk_nhds tendsto_yn)
  have h1' : Tendsto (fun n => X.reducedπ ((1 : ℤˣ), yn n)) atTop
      (𝓝 (X.reducedπ ((-1 : ℤˣ), o₀))) := h1.congr fun n => reducedπ_eq n
  exact reducedπ_ne (tendsto_nhds_unique h1' h2)

end

end JumpingRetract

/-- **Propositions 7.9–7.10 need `𝐗^R` Hausdorff**: there is an ep-groupoid (`ℤ/2` acting on the
dimension-jumping retract of Remark 4.3) whose reduced morphism space `𝐗^R` is not Hausdorff, so
not an M-polyfold (gap G.71). -/
theorem exists_not_t2Space_reducedMor :
    ∃ (Obj Mor : Type) (_ : TopologicalSpace Obj) (_ : T2Space Obj) (_ : ParacompactSpace Obj)
      (_ : TopologicalSpace Mor) (_ : T2Space Mor) (_ : ParacompactSpace Mor)
      (X : EpGroupoid Obj Mor), ¬ T2Space X.ReducedMor :=
  ⟨_, _, _, inferInstance, inferInstance, _, inferInstance, inferInstance, JumpingRetract.X,
    JumpingRetract.not_t2Space_reducedMor⟩

end Examples

end EpGroupoid

end Polyfold
