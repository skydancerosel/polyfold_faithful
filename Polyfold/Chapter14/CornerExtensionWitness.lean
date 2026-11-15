import Polyfold.Chapter14.FaceSectionCompatible

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.6, p. 682:
**Theorem 14.6.3** (2017: Theorem 14.4), the extension part, on an example with a corner.

# The extension of Theorem 14.6.3 at a corner

The bundle is `W = X × ℝ² → X` over `X = [0, ∞)² × ℝ` (`quadSEP 2 1 2`, points `(x₁, x₂, t)`),
the assignment is `cornerSectionCompatible`: the sections `±(h(t), x₂)` on the faces in
`{x₁ = 0}` and `±(h(t), x₁)` on the others, which agree on the corner stratum `{x₁ = x₂ = 0}`
(`d = 2` there).

## What is formalized (namespace `Polyfold.FaceCorner`)

* `continuous_normW_sec`: `x ↦ N(x, ± v(x))` is continuous for a `C^∞` map `v` and an auxiliary
  norm `N` (the graph section is an sc⁺-section).
* `cornerBound N`, `continuous_cornerBound`: the continuous function
  `x ↦ Σ_± N(x, ± φ₁(x)) + Σ_± N(x, ± φ₃(x)) + 1`.
* `pointwiseNorm_cornerΛ_lt`: `N(Λ)(x) < cornerBound N x` for the glued functor `Λ` at every `x`.
* **`theorem_14_6_3_extension_corner`**: the hypotheses of
  `SectionCompatibleFaceData.theorem_14_6_3_extension` hold for `cornerSectionCompatible` with an
  auxiliary norm (Theorem 12.2.2), `Ũ = X` and `f = cornerBound N`; so there is a structurable
  `Λ'` on all of `W` with `N(Λ') ≤ f`, equal to `Λ_F` over every face `F`, and `Λ'` charges a
  non-zero point of the fibre over the corner point `(0, 0, 1)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace FaceCorner

open SBLocalization StrongBundle EpGroupoid MPolyfold QuadrantBundle

/-- `x ↦ N(x, ± v(x))` is continuous: the graph section of a `C^∞` map is an sc⁺-section, so it
is continuous into `W[1]`, where `N` is continuous. -/
theorem continuous_normW_sec {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) {v : E₀ → Fin 2 → ℝ}
    (hv : ContDiff ℝ ∞ v) (b : Bool) : Continuous fun x => normW N (sec v b x) := by
  have hs := isScPlusSectionOn_graphSec (n := 2) (m := 1) (k := 2) (contDiff_sgn_smul hv b)
  obtain ⟨-, G, hG, hGs⟩ := hs
  have e : (fun x => normW N (sec v b x)) = N ∘ G := funext fun x => by
    have hmem := (isScPlusSectionOn_graphSec (n := 2) (m := 1) (k := 2)
      (contDiff_sgn_smul hv b)).mem_oneSet (mem_univ x)
    change normW N (graphSec (fun u => sgn b • v u) x) = N (G x)
    rw [normW_of_mem N hmem]
    congr 1
    exact A.B.oneVal_injective (by rw [oneVal_oneMk, hG x (mem_univ x)])
  rw [e]
  exact hN.continuous.comp (continuousOn_univ.1 hGs.continuousOn)

/-- The bound `x ↦ Σ_± N(x, ± φ₁(x)) + Σ_± N(x, ± φ₃(x)) + 1`. -/
def cornerBound (N : A.B.One → ℝ) (x : A.Obj) : ℝ :=
  normW N (sec φ₁ true x) + normW N (sec φ₁ false x) + normW N (sec φ₃ true x) +
    normW N (sec φ₃ false x) + 1

theorem continuous_cornerBound {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) :
    Continuous (cornerBound N) :=
  ((((continuous_normW_sec hN contDiff_φ₁ true).add (continuous_normW_sec hN contDiff_φ₁ false)).add
    (continuous_normW_sec hN contDiff_φ₃ true)).add
      (continuous_normW_sec hN contDiff_φ₃ false)).add continuous_const

theorem cornerBound_pos {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) (x : A.Obj) :
    0 < cornerBound N x := by
  have := normW_nonneg hN (sec φ₁ true x)
  have := normW_nonneg hN (sec φ₁ false x)
  have := normW_nonneg hN (sec φ₃ true x)
  have := normW_nonneg hN (sec φ₃ false x)
  unfold cornerBound
  linarith

/-- The glued functor of `cornerSectionCompatible`. -/
abbrev cornerΛ : A.W → ℚ≥0 := (cornerSectionCompatible.toCompatible isEpFaceStructured_A).Λg

theorem cornerΛ_eq {F : Set A.Obj} (hF : A.X.IsEpFace F) {w : A.W} (hw : A.P w ∈ F) :
    cornerΛ w = signMulti (germMapEq F) w :=
  (cornerSectionCompatible.toCompatible isEpFaceStructured_A).Λg_eq hF hw

/-- **`N(Λ)(x) < cornerBound N x`** at every `x`: over a face `F ∋ x` the points of `supp(Λ)(x)`
are `(x, ± v(x))` with `v = φ₁` or `v = φ₃`; off the faces `supp(Λ)(x) = ∅`. -/
theorem pointwiseNorm_cornerΛ_lt {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) (x : A.Obj) :
    pointwiseNorm N cornerΛ x < cornerBound N x := by
  classical
  have hpos := cornerBound_pos hN x
  have h1 := normW_nonneg hN (sec φ₁ true x)
  have h2 := normW_nonneg hN (sec φ₁ false x)
  have h3 := normW_nonneg hN (sec φ₃ true x)
  have h4 := normW_nonneg hN (sec φ₃ false x)
  have hle : pointwiseNorm N cornerΛ x ≤ cornerBound N x - 1 := by
    refine Real.sSup_le ?_ (by unfold cornerBound; linarith)
    rintro _ ⟨w, ⟨hwx, hwpos⟩, rfl⟩
    by_cases hface : ∃ F, A.X.IsEpFace F ∧ A.P w ∈ F
    · obtain ⟨F, hF, hwF⟩ := hface
      rw [cornerΛ_eq hF hwF] at hwpos
      obtain ⟨b, hb⟩ := exists_sign_of_signMulti_ne_zero hwpos.ne'
      have hw : w = sec (germMapEq F) b x := by
        rw [← hwx]
        exact Prod.ext rfl hb
      rw [hw]
      have key : ∀ (v : E₀ → Fin 2 → ℝ), (v = φ₁ ∨ v = φ₃) →
          normW N (sec v b x) ≤ cornerBound N x - 1 := by
        rintro v (rfl | rfl) <;> cases b <;> unfold cornerBound <;> linarith
      refine key _ ?_
      unfold germMapEq
      split_ifs
      exacts [Or.inl rfl, Or.inr rfl]
    · exfalso
      have h0 : cornerΛ w = 0 := by
        change (if h : ∃ F, A.X.IsEpFace F ∧ A.P w ∈ F then _ else 0) = 0
        rw [dif_neg hface]
      rw [h0] at hwpos
      exact lt_irrefl _ hwpos
  linarith

/-- **Theorem 14.6.3, the extension part, at a corner** (2021 p. 682): for the assignment
`cornerSectionCompatible` on `quadSEP 2 1 2` (a tame face-structured ep-groupoid with
paracompact orbit space and sc-smooth partitions of unity, `∂X` with a corner stratum `d = 2`,
fibre `ℝ²`), an auxiliary norm `N` (Theorem 12.2.2), `Ũ = X` and `f = cornerBound N`, all
hypotheses of `SectionCompatibleFaceData.theorem_14_6_3_extension` hold.  Hence there is a
structurable `Λ'` on `W` with `N(Λ') ≤ f`, `dom-supp(Λ') ⊆ X`, `Λ' = Λ_F` over every face `F`;
and `Λ'` charges a non-zero point of the fibre over the corner point `(0, 0, 1)`. -/
theorem theorem_14_6_3_extension_corner :
    ∃ N : A.B.One → ℝ, A.E.IsAuxNorm N ∧
      ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ x, pointwiseNorm N Λ' x ≤ cornerBound N x) ∧
        (∀ F (hF : A.X.IsEpFace F) w, A.P w ∈ F →
          Λ' w = (cornerSectionCompatible.T F hF).Λ w) ∧
        ∃ y : A.Obj, A.X.PObj.degIndex y = 2 ∧ ∃ w, A.P w = y ∧ w ≠ fiberZero A.P y ∧
          0 < Λ' w := by
  have hpara := hasParacompactOrbitSpace_quadSEP 2 1 2
  obtain ⟨N, hN⟩ := EpStrongBundle.theorem_12_2_2 A.E hpara
  have hN1 : A.B.IsAuxNorm N := hN.isAuxNorm
  obtain ⟨Λ', h1, h2, -, h4⟩ := cornerSectionCompatible.theorem_14_6_3_extension
    isEpFaceStructured_A hpara (admitsScPartitionsOfUnity_quadSEP 2 1 2) N hN univ isOpen_univ
    (GroupoidStr.isSaturated_univ _) (subset_univ _) (cornerBound N) (continuous_cornerBound hN1)
    (fun x => (cornerBound_pos hN1 x).le) (fun _ => rfl) (subset_univ _)
    fun x _ => pointwiseNorm_cornerΛ_lt hN1 x
  obtain ⟨-, -, y, hy, w, hwy, hw0, hwpos⟩ := theorem_14_6_3_corner_witness
  refine ⟨N, hN, Λ', h1, h2, h4, y, hy, w, hwy, hw0, ?_⟩
  have hb : y ∈ A.X.PObj.boundary := by
    change (0 : ℕ) < A.X.PObj.degIndex y
    rw [hy]; norm_num
  obtain ⟨F, hFace, hyF⟩ := exists_isEpFace_mem isEpFaceStructured_A hb
  have hwF : A.P w ∈ F := hwy ▸ hyF
  rw [h4 F hFace w hwF]
  rw [cornerFaceData.Λg_eq hFace hwF] at hwpos
  exact hwpos

end FaceCorner

end Polyfold
