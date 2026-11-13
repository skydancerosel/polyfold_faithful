import Polyfold.Chapter3.GapP1_Lemma3813
import Polyfold.Chapter3.TangentGerm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.2: **Theorem 3.2.3**
(preprint 3.27), p. 106, with **Lemma 3.8.13** (preprint 3.70): the degeneracy index of a set
with the tangent germ property and that of the ambient M-polyfold.

# `d_M = d_X` off the lineality space, near the centre of a datum

For a datum `(φ, N, Y, V, δ)` of Definition 3.2.1 at `x ∈ M` (regular, `IsRegular`), the chart
`y ↦ π ∘ φ(y)` of `M` gives `d_M(y) = d_{N ∩ C}(π φ(y))` (`theorem_3_2_3_degIndex`), and the
tame chart `φ` of `X` gives `d_X(y) = d_C(φ(y))` (Proposition 2.5.6).  Since
`φ(y) = v + δ(v)` with `v = π φ(y)`, Lemma 3.8.13 in a general presentation, local form
(`lemma_3_8_13_local`), gives `d_{N ∩ C}(v) = d_C(v + δ(v))` for `v` close to `0` outside the
lineality space `C ∩ (−C)`.  Hence `d_M(y) = d_X(y)` there
(`Polyfold.MPolyfold.theorem_3_2_3_degIndex_eq`).

Some restriction is needed: for `X = [0, ∞)²` and the diagonal `M`, `d_M(0) = 1 ≠ 2 = d_X(0)`
(here `v = 0` lies in the lineality space `{0}`).
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
  {M : Set X} {n : ℕ}

/-- **Theorem 3.2.3 (preprint 3.27) with Lemma 3.8.13 (preprint 3.70): `d_M = d_X` near the centre,
off the lineality space.**  Let `M` have the `n`-dimensional tangent germ property with regular data
at every point, and `d` a regular datum `(φ, N, Y, V, δ)` at `x`.  There is `ρ > 0` such that for
every `y ∈ M` in the chart domain `U₀` of `d` with `v = π φ(y)` of norm `< ρ` and `−v ∉ C` (the
text's `v ∉ N ∩ W`): `d_M(y) = d_X(y)`, the degeneracy index of `y` in the induced structure of
`M` equals its degeneracy index in `X`. -/
theorem theorem_3_2_3_degIndex_eq [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ d : P.TangentGermChart M x n, d.IsRegular) {x : X}
    (d : P.TangentGermChart M x n) (hreg : d.IsRegular) :
    ∃ ρ > 0, ∀ y : M, y.1 ∈ d.U₀ → ‖d.π (d.φ y.1)‖ < ρ →
      -((d.π (d.φ y.1) : d.N) : d.φ.model.E 0) ∉ d.φ.model.C →
        (subPolyfold (theorem_3_2_3_isSubMPolyfold P hM)).degIndex y = P.degIndex y.1 := by
  -- `δ` is `C¹` on a relatively open neighbourhood `V'` of `0` in `N ∩ C`
  obtain ⟨V', ⟨O', hO', hV'eq⟩, h0V', -, hC1⟩ := d.germ 0 1
  have hlev : levelMap (E := ScBanach.const d.N) (F := d.φ.model.E) d.δ 0 = d.δ :=
    funext fun v => levelMap_zero (E := ScBanach.const d.N) (F := d.φ.model.E) d.δ v
  rw [hlev] at hC1
  have hC1' : ContDiffOn ℝ 1 d.δ V' := by exact_mod_cast hC1
  have h0O' : (0 : d.N) ∈ O' := (hV'eq ▸ h0V' : (0 : d.N) ∈ O' ∩ _).1
  have hD0 : fderivWithin ℝ d.δ V' 0 = 0 := by
    rw [hV'eq, inter_comm, fderivWithin_inter (hO'.mem_nhds h0O'), d.fderivWithin_zero]
  obtain ⟨ρ₁, hρ₁, hmain⟩ := lemma_3_8_13_local d.φ.model.isPartialQuadrant d.goodPosition
    d.goodComplement ⟨O', hO', hV'eq⟩ h0V' d.δ d.δ_mem_Y hC1' d.δ_zero hD0
  obtain ⟨ρ₂, hρ₂, hball⟩ := Metric.isOpen_iff.1 hO' 0 h0O'
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun y hy hyρ hlin => ?_⟩
  have hys : y.1 ∈ M ∩ d.φ.source := ⟨y.2, hy.1⟩
  obtain ⟨hvV, hφy⟩ := d.exists_eq_Γ hys
  set v := d.π (d.φ y.1) with hv
  have hvC : (v : d.φ.model.E 0) ∈ d.φ.model.C := by
    obtain ⟨O, -, hVeq⟩ := d.V_relOpen
    rw [hVeq] at hvV; exact hvV.2
  have hvV' : v ∈ V' := by
    rw [hV'eq]
    exact ⟨hball (mem_ball_zero_iff.2 (hyρ.trans_le (min_le_right _ _))), hvC⟩
  have hdeg := (hmain v hvV' (hyρ.trans_le (min_le_left _ _))).2 hlin
  rw [theorem_3_2_3_degIndex P hM d hreg y hy, hdeg,
    P.degIndex_eq_chartDegIndex_of_isTameRetract d.isChart d.tame hy.1, chartDegIndex, hφy,
    TangentGermChart.Γ_apply]

end MPolyfold

end Polyfold
