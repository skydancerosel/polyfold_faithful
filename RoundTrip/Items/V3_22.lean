import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_22

/-! Round trip for V3_22 (Definition 3.25: the `n`-dimensional tangent germ property).

`A` is the conjunction of the types of the two theorems in the declaration list,
`IsScSmoothGerm.isScInftyGermAt` and `IsScSmooth.isScInftyGermAt` (no universe parameters); the
other listed declarations (`TangentGermChart`, `HasTangentGermProperty`, `IsScInftyGermAt`,
`TangentGermChart.π`) are definitions.  `B` is the vocabulary check
`HasTangentGermProperty ↔ HasTangentGermPropertyB` in a tame M-polyfold.

* Proved, using `A` (`IsScSmoothGerm.isScInftyGermAt`): the text's notion implies the project's
  (`mpr_of_A`).  Glue: `B`'s sc-complement `Y` is a closed algebraic good complement; `δ` is
  redefined as `0` off `V` (the project wants `δ v ∈ Y` for all `v`); `B`'s fixed sc-smooth germ
  on `G` (with `G₀ ⊆ V`) gives the project's `k`-dependent `IsScInftyGermAt` by `A`; `B`'s
  `Dδ(0) = 0` (a derivative family of the sc¹-germ vanishing at `0`) gives the project's
  `fderivWithin δ (N ∩ C) 0 = 0` (`G₁` is a neighbourhood of `0` in `N ∩ C`, which is a partial
  quadrant of `N` by Proposition 3.22, so derivatives are unique).  Tameness is not used.
* Not proved: project ⇒ text.  Two gaps, both believed true (effort, not a genuine difference):
  (1) the project's good complement is algebraic + closed, the text's an sc-complement — a closed
  complement of a smooth finite-dimensional `N` is an sc-complement (proved in
  `RoundTrip/Items/V3_20.lean`, `isScSplitting_of_isClosed`);
  (2) the project's reading of "sc^∞-germ" has neighbourhoods `V_{m,k}` depending on the level
  `m` and the order `k` (`IsScInftyGermAt`), the text/`B` a single germ of neighbourhoods
  `O(N ∩ C, 0)`; the diagonal germ `U_j = V ∩ ⋂_{m+i ≤ j} V_{m,i}` should work, but needs the germ
  version of Proposition 1.19 on a finite-dimensional domain (`C^i` into `E_m` on `U_{m+i}` ⇒
  sc^k-germ), which the project does not have (it has the set version
  `IsScSmooth.of_contDiffOn_levels`).
* `B → A` is not derivable: `A`'s two lemmas are general facts about germs on arbitrary
  finite-dimensional partial quadrants; `B` speaks only of subsets of M-polyfolds.
-/

namespace RoundTrip.V3_22
open Polyfold Set Filter Topology

/-- The project's statement: the two bridging theorems. -/
def A : Prop :=
  (type_of% @Polyfold.IsScSmoothGerm.isScInftyGermAt) ∧
    (type_of% @Polyfold.IsScSmooth.isScInftyGermAt)

theorem A_holds : A := ⟨@Polyfold.IsScSmoothGerm.isScInftyGermAt, @Polyfold.IsScSmooth.isScInftyGermAt⟩

section Glue

variable {E : ScBanach} {C : Set (E 0)} {N P : Submodule ℝ (E 0)}

theorem isGoodComplement_of_B (h : IsGoodComplementB E C N P) : IsGoodComplement E C N P := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h3⟩
  by_cases hN : N ≤ E.smooth
  · have := (h1 hN).2.2 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  · exact (h2 hN).1

theorem isClosed_of_B (h : IsGoodComplementB E C N P) : IsClosed (P : Set (E 0)) := by
  by_cases hN : N ≤ E.smooth
  · exact (h.1 hN).2.1.1
  · exact (h.2.1 hN).2

end Glue

/-- **The text's tangent germ property implies the project's**, using `A`. -/
theorem mpr_of_A (hA : A) {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (M : Set X) (n : ℕ) (hB : HasTangentGermPropertyB PX M n) :
    PX.HasTangentGermProperty M n := by
  classical
  obtain ⟨hMs, hx⟩ := hB
  refine ⟨hMs, fun x hxM => ?_⟩
  obtain ⟨φ, hφ, hxs, hφ0, htame, N, Yc, hfin, hrank, hsmooth, hint, hYc, V, ⟨O', hO', hV⟩, h0V,
    δ, hδY, hδc, himg, hδ0, G, hGV, hGs, D, hD, hD0⟩ := hx x hxM
  -- `N ∩ C` is a partial quadrant of `N` (Proposition 3.22, a project lemma not in this item)
  have hgp : IsInGoodPosition φ.model.E φ.model.C N := ⟨hint, Yc, isGoodComplement_of_B hYc⟩
  have hQ : IsQuadrantLike (ScBanach.const N) (Subtype.val ⁻¹' φ.model.C) :=
    (proposition_3_1_25 φ.model.isPartialQuadrant hgp).isQuadrantLike
  -- `δ` redefined off `V`
  let δ' : N → φ.model.E 0 := fun v => if v ∈ V then δ v else 0
  have hδδ' : EqOn δ δ' V := fun v hv => by simp only [δ', if_pos hv]
  have hGs' : IsScSmoothGerm (F := φ.model.E) G δ' := fun k =>
    IsSckGerm.congr hQ (fun v hv => hδδ' (hGV v hv)) (hGs k)
  -- `Dδ(0) = 0`
  have hderiv : HasFDerivWithinAt δ (0 : N →L[ℝ] φ.model.E 0)
      (Subtype.val ⁻¹' φ.model.C) 0 := by
    have h1 := hD.hasFDerivWithinAt 0 (G.zero_mem 1)
    rw [hD0, ContinuousLinearMap.zero_comp] at h1
    obtain ⟨O1, hO1, hU1⟩ := G.relOpen 1
    rw [hU1, ScBanach.lvlSet_const, inter_comm] at h1
    have h0O1 : (0 : N) ∈ O1 := by
      have := G.zero_mem 1
      rw [hU1] at this
      exact this.1
    have h2 : HasFDerivWithinAt (δ ∘ (ScBanach.const N).toBase 1) (0 : N →L[ℝ] φ.model.E 0)
        (Subtype.val ⁻¹' φ.model.C) 0 :=
      (hasFDerivWithinAt_inter (hO1.mem_nhds h0O1)).1 h1
    exact h2
  have hV0 : V ∈ 𝓝[Subtype.val ⁻¹' φ.model.C] (0 : N) := by
    rw [hV, inter_comm]
    exact inter_mem_nhdsWithin _ (hO'.mem_nhds (by have := h0V; rw [hV] at this; exact this.1))
  have hderiv' : HasFDerivWithinAt δ' (0 : N →L[ℝ] φ.model.E 0)
      (Subtype.val ⁻¹' φ.model.C) 0 :=
    hderiv.congr_of_eventuallyEq (Filter.mem_of_superset hV0 fun v hv => (hδδ' hv).symm)
      (hδδ' h0V).symm
  have huniq : UniqueDiffWithinAt ℝ (Subtype.val ⁻¹' φ.model.C : Set N) 0 := by
    have := hQ.uniqueDiffWithinAt (m := 0) isOpen_univ
      (x := (0 : N)) ⟨mem_univ _, by rw [ScBanach.lvlSet_const]; exact hQ.zero_mem⟩
    rwa [univ_inter, ScBanach.lvlSet_const] at this
  refine ⟨{
    φ := φ
    isChart := hφ
    mem_source := hxs
    φ_zero := hφ0
    tame := htame
    N := N
    finiteDimensional := hfin
    finrank_eq := hrank
    smooth := hsmooth
    goodPosition := hgp
    Y := Yc
    goodComplement := isGoodComplement_of_B hYc
    isClosed_Y := isClosed_of_B hYc
    V := V
    V_relOpen := ⟨O', hO', hV⟩
    zero_mem_V := h0V
    δ := δ'
    δ_mem_Y := fun v => by
      by_cases hv : v ∈ V
      · simp only [δ', if_pos hv]; exact hδY v hv
      · simp only [δ', if_neg hv]; exact Yc.zero_mem
    continuousOn := hδc.congr fun v hv => (hδδ' hv).symm
    image_eq := by rw [himg]; exact image_congr fun v hv => by rw [hδδ' hv]
    germ := hA.1 hQ G hGs'
    δ_zero := by rw [← hδδ' h0V]; exact hδ0
    fderivWithin_zero := hderiv'.fderivWithin huniq }⟩

#rt_check RoundTrip.V3_22.mpr_of_A [Polyfold.IsScSmoothGerm.isScInftyGermAt,
  Polyfold.IsScSmooth.isScInftyGermAt]
#rt_overlap RoundTrip.V3_22.mpr_of_A [Polyfold.IsScSmoothGerm.isScInftyGermAt,
  Polyfold.IsScSmooth.isScInftyGermAt]

end RoundTrip.V3_22
