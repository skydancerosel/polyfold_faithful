import Polyfold.Examples.SignDimZeroFrames

/-!
# The signed weight of the canonical orientation for a common sign

`SBLocalization.IsCanonicalFor.signedWeight_eq` (`SignDimZeroFrames.lean`) computes the signed
weight of the canonical orientation `T̂` of Theorem 15.4.1, 2021 pp. 701–702 (dimension `0`) at a
point `y` where `o_y` is positive at the operators `(f − s_j)'(y)` of all branches through `y`.
Here the sign is any common sign: if all these operators are isomorphisms and `o_y` is positive
at each of them iff a fixed proposition `P` holds, the signed weight is `± Λ(f(y))`.

## What is formalized (namespace `Polyfold.Examples.Classical`)

* `frameSign_eq_neg_one_of_ne_one`: a frame sign different from `1` is `-1`.
* **`IsCanonicalFor.signedWeight_eq_sign`**: if every operator `(f − s_j)'(y)` of a branch
  through `y` is an isomorphism (read in one chart point) and `o_y` is positive at it iff `P`,
  the signed weight of `T̂(y)` is `(if P then 1 else -1) · Λ(f(y))`.
* **`IsCanonicalFor.signedWeight_eq_neg`**: the case `P = False`, signed weight `-Λ(f(y))`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold.Examples.Classical

open Polyfold Polyfold.SBLocalization StrongBundle StrongRetr MPolyfold Linearization15
  EpGroupoid

universe u

/-- A frame sign different from `1` is `-1`. -/
theorem frameSign_eq_neg_one_of_ne_one {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    {X : EpGroupoid Obj Mor} {g : X.PObj.OrTangent}
    (h : frameSign (X := X) g ≠ 1) : frameSign (X := X) g = -1 := by
  unfold frameSign at h ⊢
  by_cases hne : g.frames.Nonempty
  · rw [if_pos hne] at h
    exact absurd rfl h
  · rw [if_neg hne]

variable {A : SEP.{u}} {f : A.Obj → A.W} {y : A.Obj}

/-- **The signed weight of the canonical orientation for a common sign** (Theorem 15.4.1,
2021 pp. 701–702, dimension `0`): let `T̂` be the canonical orientation of `Θ = Λ ∘ f` for
`(f, o)`, of dimension `0`, `y` a smooth point of the support, and `(s_j, σ_j)` a local
representation of `Λ` on an open `O' ∋ y`, with global sc⁺-sections `S_j` such that
`f + S_j = f − s_j` on `O'`.  If for every branch through `y` the operator `(f − s_j)'(y)` is an
isomorphism (in some chart point at `y`) and `o_y` is positive at it iff `P`, the signed weight
of `T̂(y)` is `(if P then 1 else -1) · Λ(f(y))`. -/
theorem IsCanonicalFor.signedWeight_eq_sign {Λ : A.W → ℚ≥0} {hf : A.B.IsScFredholmSection f}
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy}
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (h : IsCanonicalFor Λ hf hsec o 0 T)
    (hy : y ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ))) (hys : y ∈ A.X.PObj.smoothSet)
    {O' : Set A.Obj} (hO' : IsOpen O') (hyO' : y ∈ O') {k : ℕ} {sb : Fin k → A.Obj → A.W}
    {σ : Fin k → ℚ≥0} (hrep : IsLocalRepOn A Λ O' sb σ) (S : Fin k → A.Obj → A.W)
    (hS : ∀ j, A.B.IsScPlusSection (S j))
    (hSs : ∀ j, ∀ x' ∈ O', sectionAdd A.P f (S j) x' = subSec f (sb j) O' x')
    (P : Prop) [Decidable P]
    (hsgn : ∀ j, sb j y = f y → ∃ hx : IsZeroAt A.P (sectionAdd A.P f (S j)) y,
      (∃ p : ChartPoint A.B y, Bijective (p.stabT hf (hS j) hx)) ∧
      (IsPosOr hf hys (o y hys) (S j) (hS j) hx ↔ P)) :
    signedWeight (X := A.X) (T y) = (if P then 1 else -1) * ((Λ (f y) : ℚ) : ℝ) := by
  classical
  obtain ⟨K, hc, hn, hR⟩ := h.2 y hy
  rw [hR y K.mem_U hys, K.orientedSum_toOrientedTame]
  -- a chart at `y` with domain in `O ∩ O'`
  have hOO := K.isOpen_O.inter hO'
  have hcc := StrongBundle.IsChart.restrictInter hOO (isChart_orChart (B := A.B) y)
  have hyc : y ∈ ((orChart A.B y).restrictInter hOO).φ.source :=
    StrongBundleChart.mem_restrictInter_source _ hOO (mem_orChart y) ⟨K.U_subset K.mem_U, hyO'⟩
  have hsub : ((orChart A.B y).restrictInter hOO).φ.source ⊆ K.O := fun z hz =>
    (StrongBundleChart.restrictInter_source_subset _ hOO hz).1
  have hsub' : ((orChart A.B y).restrictInter hOO).φ.source ⊆ O' := fun z hz =>
    (StrongBundleChart.restrictInter_source_subset _ hOO hz).2
  have hsign : ∀ i, y ∈ K.M i →
      frameSign (X := A.X) (K.orTangent hf hsec o i y) = if P then 1 else -1 := by
    intro i hyi
    obtain ⟨j, hj, hjeq⟩ := K.exists_subOp_eq hf hsec hyi hys hO' hrep hcc hyc hsub hsub'
    obtain ⟨hx, ⟨p₀, hb₀⟩, hiff⟩ := hsgn j hj
    have hb := ChartPoint.bijective_stabT_of_bijective (p := p₀) (chartPtOf _ hcc hyc hys) hf
      (hS j) hx hb₀
    rw [isPosOr_iff_chart hf hys _ (hS j) hx _ hcc hyc] at hiff
    have he := subOp_eq_stabT hf (hrep.2.1 j) (chartPtOf _ hcc hyc hys) hsub' hj.symm (hS j) hx
      (fun x' hx' => hSs j x' (hsub' hx'))
    rw [← he, ← hjeq] at hiff hb
    rw [K.orTangent_eq_linOrTangent hf hsec o hyi hcc hyc hsub hys (K.eq_of_mem hyi)]
    split_ifs with hP
    · exact (frameSign_linOrTangent_eq_one_iff hf _ _ _ (by exact hb)).2 (hiff.2 hP)
    · exact frameSign_eq_neg_one_of_ne_one fun h1 =>
        hP (hiff.1 ((frameSign_linOrTangent_eq_one_iff hf _ _ _ (by exact hb)).1 h1))
  unfold KernelBranching.canonSum
  rw [signedWeight_sum, K.eq_sum y K.mem_U, Rat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [signedWeight_single, hsign i (Finset.mem_filter.1 hi).2, mul_comm]

/-- **The signed weight of the canonical orientation at a point where `o` is negative**
(Theorem 15.4.1, 2021 pp. 701–702, dimension `0`): under the hypotheses of
`IsCanonicalFor.signedWeight_eq_sign`, if every operator `(f − s_j)'(y)` of a branch through `y`
is an isomorphism at which `o_y` is not positive, the signed weight of `T̂(y)` is `-Λ(f(y))`. -/
theorem IsCanonicalFor.signedWeight_eq_neg {Λ : A.W → ℚ≥0} {hf : A.B.IsScFredholmSection f}
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy}
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (h : IsCanonicalFor Λ hf hsec o 0 T)
    (hy : y ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ))) (hys : y ∈ A.X.PObj.smoothSet)
    {O' : Set A.Obj} (hO' : IsOpen O') (hyO' : y ∈ O') {k : ℕ} {sb : Fin k → A.Obj → A.W}
    {σ : Fin k → ℚ≥0} (hrep : IsLocalRepOn A Λ O' sb σ) (S : Fin k → A.Obj → A.W)
    (hS : ∀ j, A.B.IsScPlusSection (S j))
    (hSs : ∀ j, ∀ x' ∈ O', sectionAdd A.P f (S j) x' = subSec f (sb j) O' x')
    (hneg : ∀ j, sb j y = f y → ∃ hx : IsZeroAt A.P (sectionAdd A.P f (S j)) y,
      (∃ p : ChartPoint A.B y, Bijective (p.stabT hf (hS j) hx)) ∧
      ¬ IsPosOr hf hys (o y hys) (S j) (hS j) hx) :
    signedWeight (X := A.X) (T y) = -((Λ (f y) : ℚ) : ℝ) := by
  rw [IsCanonicalFor.signedWeight_eq_sign h hy hys hO' hyO' hrep S hS hSs False
    (fun j hj => let ⟨hx, hb, hn⟩ := hneg j hj; ⟨hx, hb, iff_false_intro hn⟩), if_neg not_false,
    neg_one_mul]

end Polyfold.Examples.Classical
