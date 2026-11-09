import Polyfold.Chapter2.LocalTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part I, Chapter 2, §2.1: **Remark 2.1.6** (p. 23, new in the 2021 edition), the strictness of
"weaker".

# The modified local completeness of Remark 2.1.6 is strictly weaker

## The text, paraphrased

(Remark 2.1.6, p. 23) The condition `cl_X(V(x)) ⊆ W(x)` of Definition 2.1.5 is of a global
nature.  Replacing `cl_X(V(x))` by the closure `cl_{W(x)}(V(x))` of `V(x)` in `W(x)` gives a
weaker definition, because `cl_X(V(x)) ⊆ W(x)` implies `cl_{W(x)}(V(x)) = cl_X(V(x))`.

## What is formalized

`Chapter2/LocalTopology.lean` has the modified definition (`IsLocallyCompleteRel`) and the
implication (`IsLocallyComplete.isLocallyCompleteRel`).  Here the implication is shown to be
strict, among Hausdorff spaces (Definition 2.1.5 assumes `X` Hausdorff):

* `isLocallyCompleteRel_of_forall_isCompletelyMetrizable`: if every point has a completely
  metrizable open neighbourhood `W(x)`, the modified definition holds (`V(x) = W(x)`, so
  `cl_{W(x)}(V(x)) = W(x)`).
* `isCompletelyMetrizableSpace_of_isEmbedding_compl_range`: a space embedded in `ℝ` onto the
  complement of a sequence `(aₙ)` is completely metrizable (`y ↦ (y, ((y − aₙ)⁻¹)ₙ)` is a closed
  embedding into `ℝ × ℝ^ℕ`).
* `RealKTop`: the real line with the **K-topology** (`kTop`): the usual open sets together with
  the complement of `K = {1/(n+1) | n ∈ ℕ}` (`kSeq`) generate it.  `RealKTop` is Hausdorff
  (finer than the usual topology), `RealKTop.isLocallyCompleteRel` (the open sets `ℝ \ K` and
  `ℝ \ {0}` carry the usual subspace topology and are completely metrizable), and
  `RealKTop.not_regularSpace`: the point `0` and the closed set `K` are not separated (every
  closed neighbourhood of `0` meets `K`, through irrational points near `1/(n+1)`), so
  `RealKTop.not_isLocallyComplete` by `IsLocallyComplete.regularSpace`.
* `remark_2_1_6_strict` (**Remark 2.1.6**, strictness): a Hausdorff space satisfying the
  modified definition but not Definition 2.1.5.

## Comments

* The remark holds as we read it; "weaker" is strict.  The example shows that the global
  condition `cl_X(V(x)) ⊆ W(x)` is what makes a locally complete space regular
  (`IsLocallyComplete.regularSpace`): `RealKTop` is locally completely metrizable but not regular.
* Mathlib has no "`G_δ` subsets of complete metric spaces are completely metrizable"; the
  neighbourhood `ℝ \ K` of `0` is such a set, handled by the explicit closed embedding above.
-/

open Set Filter Topology TopologicalSpace

noncomputable section

namespace Polyfold

/-! ### Two criteria -/

section Criterion

variable {X : Type*} [TopologicalSpace X]

/-- **A sufficient condition for the modified definition of Remark 2.1.6**: every point has an
open, completely metrizable neighbourhood `W(x)`; then `V(x) = W(x)` works, its closure in `W(x)`
being all of `W(x)`. -/
theorem isLocallyCompleteRel_of_forall_isCompletelyMetrizable
    (h : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ IsCompletelyMetrizableSpace W) :
    IsLocallyCompleteRel X := fun x => by
  obtain ⟨W, hW, hxW, hc⟩ := h x
  obtain ⟨m, hm, hcomp⟩ := hc.complete
  refine ⟨W, W, hW, hW, hxW, subset_rfl, m, hm, ?_⟩
  have : (Subtype.val ⁻¹' W : Set W) = univ := eq_univ_of_forall fun w => w.2
  rw [this, closure_univ]
  exact @isComplete_univ W m.toUniformSpace hcomp

/-- **The complement of a sequence in `ℝ` is completely metrizable**: if `j : Y → ℝ` is an
embedding onto `ℝ \ {aₙ | n ∈ ℕ}`, then `Y` is completely metrizable, because
`y ↦ (j y, ((j y − aₙ)⁻¹)ₙ)` is a closed embedding into `ℝ × ℝ^ℕ` with range
`{(u, z) | ∀ n, zₙ (u − aₙ) = 1}`. -/
theorem isCompletelyMetrizableSpace_of_isEmbedding_compl_range {Y : Type*} [TopologicalSpace Y]
    {j : Y → ℝ} (hj : IsEmbedding j) (a : ℕ → ℝ) (hr : range j = (range a)ᶜ) :
    IsCompletelyMetrizableSpace Y := by
  have hne : ∀ y n, j y - a n ≠ 0 := fun y n h => by
    have : j y ∈ (range a)ᶜ := hr ▸ mem_range_self y
    exact this ⟨n, (sub_eq_zero.1 h).symm⟩
  let f : Y → ℝ × (ℕ → ℝ) := fun y => (j y, fun n => (j y - a n)⁻¹)
  have hfc : Continuous f := hj.continuous.prodMk (continuous_pi fun n =>
    (hj.continuous.sub continuous_const).inv₀ (hne · n))
  have hfe : IsEmbedding f :=
    ⟨IsInducing.of_comp hfc continuous_fst hj.isInducing,
      fun y y' h => hj.injective (congrArg Prod.fst h)⟩
  have hrange : range f = {p | ∀ n, p.2 n * (p.1 - a n) = 1} := by
    ext ⟨u, z⟩
    constructor
    · rintro ⟨y, hy⟩
      simp only [f, Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      intro n
      exact inv_mul_cancel₀ (hne y n)
    · intro h
      have hu : u ∈ range j := by
        rw [hr]
        rintro ⟨n, rfl⟩
        simpa using h n
      obtain ⟨y, rfl⟩ := hu
      refine ⟨y, ?_⟩
      simp only [f, Prod.mk.injEq, true_and]
      funext n
      exact (eq_inv_of_mul_eq_one_left (h n)).symm
  have hcl : IsClosed (range f) := by
    rw [hrange, ofPred_forall]
    exact isClosed_iInter fun n => isClosed_eq (by fun_prop) continuous_const
  exact IsClosedEmbedding.IsCompletelyMetrizableSpace ⟨hfe, hcl⟩

end Criterion

/-! ### The K-topology on `ℝ` -/

section KTopology

/-- The sequence `1/(n+1)`; its range is the set `K` of the K-topology. -/
def kSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem kSeq_pos (n : ℕ) : 0 < kSeq n := by unfold kSeq; positivity

/-- The **K-topology** on `ℝ`: generated by the usual open sets and `ℝ \ K`,
`K = {1/(n+1) | n ∈ ℕ}`.  (Mathlib orders topologies by fineness reversed, so the generated
topology is the infimum.) -/
@[instance_reducible]
def kTop : TopologicalSpace ℝ :=
  (inferInstance : TopologicalSpace ℝ) ⊓ generateFrom {(range kSeq)ᶜ}

/-- The real line with the K-topology, a type synonym of `ℝ`. -/
def RealKTop : Type := ℝ

instance : TopologicalSpace RealKTop := kTop

namespace RealKTop

/-- The identity `ℝ_K → ℝ`. -/
def toReal : RealKTop → ℝ := id

/-- The identity `ℝ → ℝ_K`. -/
def ofReal : ℝ → RealKTop := id

@[simp] theorem toReal_ofReal (y : ℝ) : toReal (ofReal y) = y := rfl

@[simp] theorem ofReal_toReal (x : RealKTop) : ofReal (toReal x) = x := rfl

/-- The K-topology is finer than the usual one. -/
theorem continuous_toReal : Continuous toReal :=
  continuous_id_of_le (show kTop ≤ _ from inf_le_left)

/-- **`ℝ_K` is Hausdorff** (it is finer than the usual topology). -/
instance : T2Space RealKTop :=
  t2Space_antitone (show kTop ≤ _ from inf_le_left) (inferInstance : T2Space ℝ)

/-- `ℝ \ K` is open in `ℝ_K`, i.e. `K` is closed. -/
theorem isOpen_compl_range : IsOpen (toReal ⁻¹' (range kSeq)ᶜ) :=
  TopologicalSpace.le_def.1 (show kTop ≤ generateFrom {(range kSeq)ᶜ} from inf_le_right) _
    (isOpen_generateFrom_of_mem rfl)

/-- A neighbourhood of `x` in `ℝ_K` contains the points outside `K` of a usual neighbourhood of
`x`. -/
theorem mem_nhds {x : RealKTop} {s : Set RealKTop} (hs : s ∈ 𝓝 x) :
    {y : ℝ | y ∉ range kSeq → ofReal y ∈ s} ∈ 𝓝 (toReal x) := by
  have h1 : @nhds ℝ kTop (toReal x) =
      𝓝 (toReal x) ⊓ @nhds ℝ (generateFrom {(range kSeq)ᶜ}) (toReal x) :=
    nhds_inf
  have h2 : 𝓟 (range kSeq)ᶜ ≤ @nhds ℝ (generateFrom {(range kSeq)ᶜ}) (toReal x) := by
    rw [nhds_generateFrom]
    refine le_iInf₂ fun t ht => ?_
    rw [mem_singleton_iff.1 ht.2]
  have hs' : s ∈ @nhds ℝ kTop (toReal x) := hs
  rw [h1] at hs'
  have := (inf_le_inf_left _ h2) hs'
  exact mem_inf_principal.1 this

/-- **`ℝ_K` is not regular**: a closed neighbourhood `C ⊆ ℝ \ K` of `0` would contain the
irrational points of some `(−ε, ε)`, and the open `ℝ_K \ C ∋ 1/(n+1)`, `1/(n+1) < ε`, the
irrational points of some `(1/(n+1) − δ, 1/(n+1) + δ)`. -/
theorem not_regularSpace : ¬ RegularSpace RealKTop := by
  intro hreg
  have h0 : toReal ⁻¹' (range kSeq)ᶜ ∈ 𝓝 (ofReal 0) := by
    refine isOpen_compl_range.mem_nhds ?_
    rintro ⟨n, hn⟩
    exact (kSeq_pos n).ne' hn
  obtain ⟨C, hC, hCc, hCK⟩ := exists_mem_nhds_isClosed_subset h0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_nhds hC)
  obtain ⟨n, hn⟩ : ∃ n, kSeq n < ε := exists_nat_one_div_lt hε
  have hnC : ofReal (kSeq n) ∉ C := fun h => hCK h (mem_range_self n)
  obtain ⟨δ, hδ, hball'⟩ := Metric.mem_nhds_iff.1 (mem_nhds (hCc.isOpen_compl.mem_nhds hnC))
  have hk : kSeq n ∈ Metric.ball (kSeq n) δ ∩ Metric.ball 0 ε := by
    refine ⟨Metric.mem_ball_self hδ, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (kSeq_pos n)]
    exact hn
  obtain ⟨y, hy, hyirr⟩ := dense_irrational.inter_open_nonempty _
    (Metric.isOpen_ball.inter Metric.isOpen_ball) ⟨_, hk⟩
  have hyK : y ∉ range kSeq := by
    rintro ⟨m, rfl⟩
    exact hyirr ⟨1 / ((m : ℚ) + 1), by push_cast [kSeq]; rfl⟩
  exact hball' hy.1 hyK (hball hy.2 hyK)

/-- **`ℝ_K` is not locally complete** in the sense of Definition 2.1.5 (a locally complete space
is regular). -/
theorem not_isLocallyComplete : ¬ IsLocallyComplete RealKTop := fun h =>
  not_regularSpace h.regularSpace

/-- On a subset `S` of `ℝ` on which `ℝ \ K` is relatively open for the usual topology, the
K-topology and the usual topology agree. -/
theorem isEmbedding_subtype {S O : Set ℝ} (hO : IsOpen O) (hSO : S ∩ O = S ∩ (range kSeq)ᶜ) :
    IsEmbedding (fun w : (toReal ⁻¹' S : Set RealKTop) => toReal w) := by
  refine ⟨⟨?_⟩, fun w w' h => Subtype.ext h⟩
  change TopologicalSpace.induced Subtype.val kTop = _
  unfold kTop
  rw [induced_inf, induced_generateFrom_eq, image_singleton, inf_eq_left.2]
  · rfl
  refine le_generateFrom fun s hs => ?_
  rw [mem_singleton_iff.1 hs]
  refine isOpen_induced_iff.2 ⟨O, hO, ?_⟩
  ext ⟨w, hw⟩
  have := congrArg (fun T => w ∈ T) hSO
  simp only [mem_inter_iff, eq_iff_iff] at this
  simp only [mem_preimage]
  exact ⟨fun h => (this.1 ⟨hw, h⟩).2, fun h => (this.2 ⟨hw, h⟩).2⟩

theorem range_subtype (S : Set ℝ) :
    range (fun w : (toReal ⁻¹' S : Set RealKTop) => toReal w) = S := by
  ext y
  exact ⟨by rintro ⟨w, rfl⟩; exact w.2, fun hy => ⟨⟨ofReal y, hy⟩, rfl⟩⟩

/-- **`ℝ_K` satisfies the modified definition of Remark 2.1.6**: the points outside `K` lie in
the open set `ℝ \ K`, the points of `K` in the open set `ℝ \ {0}`; both carry the usual subspace
topology and are complements of sequences, hence completely metrizable. -/
theorem isLocallyCompleteRel : IsLocallyCompleteRel RealKTop := by
  refine isLocallyCompleteRel_of_forall_isCompletelyMetrizable fun x => ?_
  by_cases hx : toReal x ∈ range kSeq
  · obtain ⟨n, hn⟩ := hx
    have hcl : IsClosed (insert 0 (range kSeq)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat.isCompact_insert_range).isClosed
    refine ⟨toReal ⁻¹' {0}ᶜ, isOpen_compl_singleton.preimage continuous_toReal, ?_, ?_⟩
    · change toReal x ≠ 0
      rw [← hn]
      exact (kSeq_pos n).ne'
    · refine isCompletelyMetrizableSpace_of_isEmbedding_compl_range
        (isEmbedding_subtype hcl.isOpen_compl ?_) (fun _ => 0) ?_
      · ext y
        simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, mem_insert_iff]
        tauto
      · rw [range_subtype, range_const]
  · refine ⟨toReal ⁻¹' (range kSeq)ᶜ, isOpen_compl_range, hx, ?_⟩
    exact isCompletelyMetrizableSpace_of_isEmbedding_compl_range
      (isEmbedding_subtype isOpen_univ (by rw [inter_univ, inter_self])) kSeq (range_subtype _)

end RealKTop

/-- **Remark 2.1.6 (2021), strictness**: the modified definition (closure of `V(x)` in `W(x)`) is
strictly weaker than Definition 2.1.5: the Hausdorff space `ℝ_K` satisfies it but is not locally
complete.  (The implication is `IsLocallyComplete.isLocallyCompleteRel`.) -/
theorem remark_2_1_6_strict :
    ∃ (X : Type) (_ : TopologicalSpace X), T2Space X ∧ IsLocallyCompleteRel X ∧
      ¬ IsLocallyComplete X :=
  ⟨RealKTop, inferInstance, inferInstance, RealKTop.isLocallyCompleteRel,
    RealKTop.not_isLocallyComplete⟩

end KTopology

end Polyfold
