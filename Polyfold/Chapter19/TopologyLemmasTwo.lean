import Polyfold.Chapter2.Metrizable

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.5: the point-set topology of **Remark 19.5.4** (p. 888), stated for arbitrary topological
spaces.

# Metrizable neighbourhoods of compact sets

## The text, paraphrased

(Remark 19.5.4) After checking the properness condition one concludes that `T` is completely
regular, Hausdorff and locally metrizable.  These facts imply that a given compact `K ⊂ |S|` has an
open neighbourhood `U = U(K)` which is paracompact and hence metrizable.

## What is formalized

* `exists_bump_of_isOpen`: in a completely regular space, for `x ∈ W` open there is a continuous
  `ρ ≥ 0` with `ρ(x) > 0` and `supp ρ ⊆ W`.
* **`exists_isOpen_metrizableSpace_of_isCompact`**: in a completely regular, locally metrizable
  space every compact `K` has an open neighbourhood `U` which is metrizable and paracompact.

## Reading

* The step the text leaves to the reader is a finite form of Smirnov's metrization theorem:
  cover `K` by finitely many sets `{ρ_k > 0}`, `ρ_k` bump functions supported in open metrizable
  `W_k`, and let `U = ⋃ {ρ_k > 0}`.  The `ρ_k` restricted to `U` satisfy the hypotheses of the
  metrization lemma `Polyfold.metrizableSpace_of_partition` (Chapter 2: open metrizable `W_k ∩ U`,
  supports in `W_k ∩ U`, finitely many, and some `ρ_k > 0` at every point of `U`), so `U` is
  metrizable, hence paracompact (A. H. Stone).  The text has "paracompact and hence metrizable";
  the argument gives both properties.
* The Hausdorff property is not used beyond complete regularity (a metrizable `U` is Hausdorff).
-/

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

namespace Chapter19

variable {X : Type*} [TopologicalSpace X]

/-- **A bump function in a completely regular space**: for `x ∈ W`, `W` open, a continuous
`ρ ≥ 0` with `ρ(x) > 0` and `tsupport ρ ⊆ W` (`ρ = max(1/2 − f, 0)` for an Urysohn function `f`
with `f(x) = 0`, `f = 1` off `W`). -/
theorem exists_bump_of_isOpen [CompletelyRegularSpace X] {W : Set X} (hW : IsOpen W) {x : X}
    (hx : x ∈ W) :
    ∃ ρ : X → ℝ, Continuous ρ ∧ (∀ y, 0 ≤ ρ y) ∧ 0 < ρ x ∧ tsupport ρ ⊆ W := by
  obtain ⟨f, hf, hfx, hf1⟩ :=
    CompletelyRegularSpace.completely_regular x Wᶜ hW.isClosed_compl (not_not_intro hx)
  have hfc : Continuous fun y => (f y : ℝ) := continuous_subtype_val.comp hf
  refine ⟨fun y => max (1 / 2 - (f y : ℝ)) 0, (continuous_const.sub hfc).max continuous_const,
    fun y => le_max_right _ _, ?_, ?_⟩
  · simp only [hfx, Set.Icc.coe_zero, sub_zero]
    norm_num
  · have hsub : support (fun y => max (1 / 2 - (f y : ℝ)) 0) ⊆ {y | (f y : ℝ) ≤ 1 / 2} := by
      intro y hy
      by_contra hc
      apply hy
      have hc : 1 / 2 < (f y : ℝ) := not_le.1 hc
      exact max_eq_right (by linarith)
    refine (closure_minimal hsub (isClosed_le hfc continuous_const)).trans fun y hy => ?_
    by_contra hyW
    have h1 : (f y : ℝ) = 1 := by
      have := hf1 (show y ∈ Wᶜ from hyW)
      simp only [Pi.one_apply] at this
      rw [this]
      rfl
    have : (f y : ℝ) ≤ 1 / 2 := hy
    linarith

/-- **Remark 19.5.4 (p. 888), the topology**: in a completely regular space in which every point
has an open metrizable neighbourhood, every compact `K` has an open neighbourhood `U` which is
metrizable and paracompact. -/
theorem exists_isOpen_metrizableSpace_of_isCompact [CompletelyRegularSpace X]
    (h : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ MetrizableSpace W) {K : Set X}
    (hK : IsCompact K) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ MetrizableSpace U ∧ ParacompactSpace U := by
  choose W hWo hxW hWm using h
  choose ρ hρc hρ0 hρx hρW using fun x => exists_bump_of_isOpen (hWo x) (hxW x)
  have hUo : ∀ x, IsOpen {y | 0 < ρ x y} := fun x => isOpen_lt continuous_const (hρc x)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => {y | 0 < ρ x y}) hUo
    fun y _ => mem_iUnion.2 ⟨y, hρx y⟩
  set U := ⋃ i ∈ t, {y | 0 < ρ i y} with hU
  have hUopen : IsOpen U := isOpen_biUnion fun i _ => hUo i
  have hm : MetrizableSpace U := by
    let V : t → Set U := fun i => Subtype.val ⁻¹' W i.1
    have hVo : ∀ i, IsOpen (V i) := fun i => (hWo i.1).preimage continuous_subtype_val
    have hVm : ∀ i, MetrizableSpace (V i) := fun i => by
      have := hWm i.1
      let e : V i → W i.1 := fun v => ⟨v.1.1, v.2⟩
      have he : IsEmbedding e := by
        refine IsEmbedding.of_comp (g := Subtype.val) ?_ continuous_subtype_val ?_
        · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
        · change IsEmbedding fun v : V i => (v.1.1 : X)
          exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
      exact he.metrizableSpace
    refine metrizableSpace_of_partition V hVo (fun i => ρ i.1 ∘ Subtype.val)
      (fun i => (hρc i.1).comp continuous_subtype_val) (fun i y => hρ0 i.1 y)
      (fun i => (tsupport_comp_subset_preimage _ continuous_subtype_val).trans
        (preimage_mono (hρW i.1))) (locallyFinite_of_finite _) fun y => ?_
    obtain ⟨i, hi, hy⟩ := mem_iUnion₂.1 y.2
    exact ⟨⟨i, hi⟩, hy⟩
  exact ⟨U, hUopen, ht, hm, paracompactSpace_of_metrizableSpace U⟩

end Chapter19

end Polyfold
