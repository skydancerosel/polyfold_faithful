import Polyfold.Chapter9.BranchingGeometryManifold
import Polyfold.Chapter9.OrientationExample

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.4 "The Geometry of Local Branching Structures" (2021 pp. 430–436; 2017
pp. 316–321): Property (T) (p. 430), **Lemma 9.4.4** (p. 431; 2017: Lemma 9.13), **Definition
9.4.7** (p. 432; 2017: Definition 9.14), **Lemma 9.4.8** (p. 432; 2017: Lemma 9.15),
**Proposition 9.4.9** (p. 434; 2017: Proposition 9.5) and **Proposition 9.4.10** (p. 435; 2017:
Proposition 9.6).  Numbers and pages are the 2021 text's, the 2017 ones in parentheses.

# `y`-equivalence of sheets, the set `M_U^*`, and the comparison of two structures

## The text, paraphrased

Fix an oriented local branching structure `(Mᵢ, oᵢ)_{i ∈ I}, (σᵢ)` on `U(x)`.  Property (T): if
two sheets have the same tangent space at a common point `y₀` and their orientations there differ
by `ε = ±1`, they differ by `ε` at every common point with the same tangent space (Lemma 9.4.3:
(T) holds after shrinking `U(x)`).  `K(i, i') = Mᵢ ∩ Mᵢ'`; (Lemma 9.4.4) a point of `K(i, i')` is
essential for `K(i, i') ⊆ Mᵢ` iff it is for `K(i, i') ⊆ Mᵢ'`; (Lemma 9.4.6) `K(i, i')^{ne}` has
measure zero.  (Definition 9.4.7) For `y ∈ M_U = ⋃ Mᵢ` and `I_y = {i | y ∈ Mᵢ}`, `i ∼_y i'` if a
chain in `I_y` from `i` to `i'` has `y ∈ K(i_{p-1}, i_p)^e` at every step; then `T_yMᵢ = T_yMᵢ'`;
`P_y = I_y/∼_y`.  (Lemma 9.4.8) `{y ∈ M_U | ♯P_y ≥ 2}` has measure zero.  (Proposition 9.4.9)
`M_U^* = {♯P_y = 1}` differs from `M_U` by a null set and is the disjoint union of the
`M_U^J = {I_y = J}`, on which `Θ = σ_J`, `TΘ = σ_J · T^J`, `T̂Θ = a_J (T^J, o_a) + b_J (T^J, o_b)`
with `a_J + b_J = σ_J` and `o_a = -o_b`.  (Proposition 9.4.10) Two oriented structures on
`U(x)` with the same weighted sums (a) and oriented sums (b) are compared on a full-measure
`M_U^† = A₁ ⊔ … ⊔ A_ℓ` with constant index sets, equal tangent spaces, equal total weights and
matching orientation classes (1)–(5).

## What is formalized

* `MPolyfold.SheetGeometry P S`: for a class `S` of submanifolds of the M-polyfold `P`, the
  essential points `ess N K` (Definition 9.4.1 (2)) and the null sets `IsNull N A`
  (Definition 9.4.5) of the sheets, with **Lemma 9.4.4** (`ess_comm`), **Lemma 9.4.6**
  (`isNull_diff_ess`) and the note of Definition 9.4.7 (`submanifoldTangent_eq`) as fields, and
  two non-degeneracy fields (`ess_self`, `not_isNull_self`).  Satisfiability:
  `graphSheetGeometry` (pieces of graphs of smooth `β : ℝ → ℝ` in `ℝ²`, `graphSheets`, with the
  `essentialSet` and `IsMeasureZero` of `BranchingGeometryManifold` read in the chart `z ↦ z 0`;
  Lemma 9.4.6 there is `lemma_9_4_6`).
* **Definition 9.4.7**: `IsLink` (`y ∈ K(i, j)^e`), `YEquiv` (chains), `equivalence_yEquiv`,
  `ySetoid` (`ySetoid_iff`), `numClasses` (`♯P_y`), `submanifoldTangent_eq_of_yEquiv` (the note);
  `MStar` (`M_U^*`), `MStarPart` (`M_U^J`), `IsNullIn` (measure zero in `M_U`).
* **`lemma_9_4_8`**, `isNullIn_diff_MStar`, **`proposition_9_4_9`** (with Property (T),
  `OrientedBranchingStructure.PropertyT`), `tangent_eq_iff_of_mem_ess` (the sign map
  `K(i, i')^e → {±1}` is constant under (T), 2021 p. 431), **`proposition_9_4_10`**.
* **`lemma_9_4_4_mixed_dim`**: Lemma 9.4.4 does not hold as we read it for sheets of different
  dimensions (`ℝ × 0` inside `ℝ` and inside `ℝ²`).
* Tools: `OrTangent.eq_or_eq_or_eq_of_isOrientedAt` (of three orientations of one tangent set two
  coincide), `OrTangent.eq_of_iff_eq`, `exists_ne_isOrientedAt`, `tangentValue_eq_sum`
  (`TΘ(y) = ∑_{I_y} σᵢ T_yMᵢ`), `sum_pos_iff`.
* Witnesses from Example 9.3.5 (`example935B1`, `example935B2`, sheets in `graphSheets`):
  `propertyT_example935B1`; `example935_two_le_numClasses` (at the origin the sheets `G⁺⁺, G⁻⁻`
  are tangent but not `0`-equivalent, so the set of Lemma 9.4.8 is not empty);
  `orientedLift1_const_eq_orientedLift2`, `example935_hypotheses_9_4_10` and `example935_MU_eq`
  (the two different decompositions `G⁺⁺, G⁻⁻` and `G⁺⁻, G⁻⁺` with all signs `+` satisfy (a)
  and (b) of Proposition 9.4.10).

## The choices made

* Definitions 9.4.1 and 9.4.5 are about smooth finite-dimensional manifolds (formalized in
  `BranchingGeometryManifold` for Mathlib manifolds); the sheets `Mᵢ` here are submanifolds of an
  M-polyfold, which the repository does not equip with a Mathlib manifold structure.  The essential
  points and null sets of the sheets are therefore the data of a `SheetGeometry`, and Lemmas 9.4.4
  and 9.4.6 its fields; the witness `graphSheetGeometry` takes them from
  `BranchingGeometryManifold`.
* Lemma 9.4.4 and the note "`i ∼_y i'` implies `T_yMᵢ = T_yMᵢ'`" need sheets of equal dimension
  (`lemma_9_4_4_mixed_dim`), as for an `n`-dimensional `Θ`.
* "Measure zero" for subsets of `M_U` (the text refers forward, in a footnote, to Definition 9.5.1
  and Lemma 9.5.2, 2021 p. 437, where independence of the structure is shown; as we read it the
  reference is consistent) is `IsNullIn`: measure zero in every sheet.
* Lemma 9.4.8: as we read it, the last step "`⋃_{j, j' ∈ I} K(j, j')^{ne}` has measure zero" needs
  care, `K(j, j')^{ne}` being null in `Mⱼ` and `Mⱼ'` only; the proof uses, inside `Mᵢ`, the sets
  `K(i, j)^{ne}`.
* `o_a = -o_b` in Proposition 9.4.9 is `o_a ≠ o_b` on the same tangent set (it has exactly two
  orientations; for `B_J = ∅`, `o_b` is the other one); (2) uses Theorem 9.2.1's independence
  (`HasIndependentTangentSums`), as in `Tangent.lean`.
* Proposition 9.4.10: the two structures may have different `Θ, Θ'` ((a) is a hypothesis, as in
  the text) and live on the same `U(x)`; `M_U^†` is `M_U''^*` of the union `B ⊔ B'` (the text
  intersects it with `M_U^*` and `M_U'^*`, not needed for (1)–(5)); Property (T) is not used, the
  pieces being cut out by the finitely many values of `y ↦ (I_y, I'_y, J₊(y), J'₊(y))`.
* Lemma 9.4.3 is not in this file: it is `OrientedBranchingStructure.lemma_9_4_3`
  (`Chapter9/PropertyTShrinking2021.lean`, 2026-11-09); Lemma 9.4.4 for M-polyfold sheets, in the
  reading through M-polyfold charts, is `lemma_9_4_4_chart`
  (`Chapter9/SheetEssentialChart2021.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-! ### At most two orientations of one tangent set -/

/-- Two oriented tangent sets over `y` with the same carrier have the same dimension. -/
theorem OrTangent.dim_eq_of_isOrientedAt {y : X} {g g' : OrTangent P} (h : P.IsOrientedAt y g)
    (h' : P.IsOrientedAt y g') (hc : g.carrier = g'.carrier) : g.dim = g'.dim := by
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨N, hN, -, hr, -⟩ := h.isChartOrientation hφ hyφ
  obtain ⟨N', hN', -, hr', -⟩ := h'.isChartOrientation hφ hyφ
  have hNN : N = N' := SetLike.coe_injective (by rw [hN, hN', hc])
  subst hNN
  rw [← hr, ← hr']

/-- **Of three orientations of one tangent set two coincide** (a linear space has exactly two
orientations). -/
theorem OrTangent.eq_or_eq_or_eq_of_isOrientedAt {y : X} {g₁ g₂ g₃ : OrTangent P}
    (h₁ : P.IsOrientedAt y g₁) (h₂ : P.IsOrientedAt y g₂) (h₃ : P.IsOrientedAt y g₃)
    (h₁₂ : g₁.carrier = g₂.carrier) (h₁₃ : g₁.carrier = g₃.carrier) :
    g₁ = g₂ ∨ g₁ = g₃ ∨ g₂ = g₃ := by
  have e₂ := OrTangent.dim_eq_of_isOrientedAt h₁ h₂ h₁₂
  have e₃ := OrTangent.dim_eq_of_isOrientedAt h₁ h₃ h₁₃
  obtain ⟨n₁, L, O₁⟩ := g₁
  obtain ⟨n₂, L₂, O₂⟩ := g₂
  obtain ⟨n₃, L₃, O₃⟩ := g₃
  simp only at h₁₂ h₁₃ e₂ e₃
  subst h₁₂ h₁₃ e₂ e₃
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨N, hN, hfin, hr, -⟩ := h₁.isChartOrientation hφ hyφ
  have := hfin
  obtain ⟨A, B, -, hAB⟩ := exists_two_orientations hφ hyφ h₁.1 hN hr
  rcases (hAB _).1 h₁ with rfl | rfl <;> rcases (hAB _).1 h₂ with rfl | rfl <;>
    rcases (hAB _).1 h₃ with rfl | rfl <;> simp

/-- Two oriented tangent sets `h₁`, `h₂` over `y` with the carrier of `g` agree if each equals `g`
exactly when the other does. -/
theorem OrTangent.eq_of_iff_eq {y : X} {g h₁ h₂ : OrTangent P} (hg : P.IsOrientedAt y g)
    (hh₁ : P.IsOrientedAt y h₁) (hh₂ : P.IsOrientedAt y h₂) (hc₁ : g.carrier = h₁.carrier)
    (hc₂ : g.carrier = h₂.carrier) (h : h₁ = g ↔ h₂ = g) : h₁ = h₂ := by
  by_cases h₁g : h₁ = g
  · rw [h₁g, h.1 h₁g]
  · have h₂g : h₂ ≠ g := fun e => h₁g (h.2 e)
    rcases OrTangent.eq_or_eq_or_eq_of_isOrientedAt hg hh₁ hh₂ hc₁ hc₂ with e | e | e
    · exact (h₁g e.symm).elim
    · exact (h₂g e.symm).elim
    · exact e

/-- **The other orientation** of `T_yA`, `A` an `n`-dimensional submanifold through `y`. -/
theorem exists_ne_isOrientedAt {A : Set X} {n : ℕ} (hA : P.IsSubmanifoldOfDim A n) {y : X}
    (hy : y ∈ A) (O : Set (Fin n → P.TangentSpace)) :
    ∃ O', O' ≠ O ∧ P.IsOrientedAt y ⟨n, P.submanifoldTangent A y, O'⟩ := by
  obtain ⟨O₁, O₂, h12, hO⟩ := exists_two_orientations_submanifoldTangent hA hy
  by_cases h : O = O₁
  · exact ⟨O₂, fun e => h12 (h.symm.trans e.symm), (hO _).2 (Or.inr rfl)⟩
  · exact ⟨O₁, fun e => h e.symm, (hO _).2 (Or.inl rfl)⟩

/-! ### The geometry of the sheets -/

variable (P) in
/-- **The geometry of a class `S` of submanifolds used in §9.4** (2021 pp. 430–432): for
`N ∈ S` and `K ⊆ N` the essential points `ess N K` of `K` as a subset of `N` (Definition 9.4.1
(2)), and the sets `A` of measure zero in `N`, `IsNull N A` (Definition 9.4.5), with the
properties Lemmas 9.4.4 (`ess_comm`) and 9.4.6 (`isNull_diff_ess`) and the note in Definition
9.4.7 (`submanifoldTangent_eq`: `T_zN = T_zN'` at essential points of `N ∩ N'`), together with
two non-degeneracy conditions (`ess_self`: every point of `N` is essential for `N ⊆ N`;
`not_isNull_self`: a nonempty `N` does not have measure zero in itself). -/
structure SheetGeometry (S : Set (Set X)) where
  /-- The essential points `K^e` of `K` as a subset of `N`. -/
  ess : Set X → Set X → Set X
  ess_subset : ∀ N K, ess N K ⊆ K
  ess_self : ∀ N ∈ S, ess N N = N
  /-- Lemma 9.4.4. -/
  ess_comm : ∀ N ∈ S, ∀ N' ∈ S, ess N (N ∩ N') = ess N' (N' ∩ N)
  /-- The note in Definition 9.4.7. -/
  submanifoldTangent_eq : ∀ N ∈ S, ∀ N' ∈ S, ∀ z ∈ ess N (N ∩ N'),
    P.submanifoldTangent N z = P.submanifoldTangent N' z
  /-- `A` has measure zero in `N`. -/
  IsNull : Set X → Set X → Prop
  isNull_empty : ∀ N, IsNull N ∅
  isNull_mono : ∀ {N A A'}, IsNull N A' → A ⊆ A' → IsNull N A
  isNull_union : ∀ {N A A'}, IsNull N A → IsNull N A' → IsNull N (A ∪ A')
  not_isNull_self : ∀ N ∈ S, N.Nonempty → ¬ IsNull N N
  /-- Lemma 9.4.6. -/
  isNull_diff_ess : ∀ N ∈ S, ∀ N' ∈ S, IsNull N ((N ∩ N') \ ess N (N ∩ N'))

namespace SheetGeometry

variable {S : Set (Set X)} (G : P.SheetGeometry S)

theorem isNull_iUnion {κ : Type*} [Finite κ] {N : Set X} {A : κ → Set X}
    (h : ∀ k, G.IsNull N (A k)) : G.IsNull N (⋃ k, A k) := by
  classical
  cases nonempty_fintype κ
  suffices ∀ s : Finset κ, G.IsNull N (⋃ k ∈ s, A k) by simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using G.isNull_empty N
  | insert k s hk ih =>
    rw [Finset.set_biUnion_insert]
    exact G.isNull_union (h k) ih

/-! ### Definition 9.4.7 -/

variable {ι : Type*} (M : ι → Set X)

/-- One link of a chain: `y ∈ K(i, j)^e`, `K(i, j) = Mᵢ ∩ Mⱼ`. -/
def IsLink (y : X) (i j : {i // y ∈ M i}) : Prop := y ∈ G.ess (M i) (M i ∩ M j)

/-- **Definition 9.4.7, 2021 p. 432 (2017: Definition 9.14) (`y`-equivalence)**: `i ∼_y i'` for
`i, i' ∈ I_y = {i | y ∈ Mᵢ}` if a chain `i = i₀, i₁, …, i_k = i'` in `I_y` has
`y ∈ K(i_{p-1}, i_p)^e` for every `p`. -/
def YEquiv (y : X) (i j : {i // y ∈ M i}) : Prop := Relation.ReflTransGen (G.IsLink M y) i j

theorem equivalence_yEquiv (hM : ∀ i, M i ∈ S) (y : X) : Equivalence (G.YEquiv M y) := by
  have hsymm : ∀ i j, G.IsLink M y i j → G.IsLink M y j i := fun i j h => by
    unfold IsLink at *
    rw [← G.ess_comm _ (hM i) _ (hM j)]
    exact h
  refine ⟨fun _ => Relation.ReflTransGen.refl, fun h => ?_, Relation.ReflTransGen.trans⟩
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih

/-- The equivalence relation `∼_y` as a setoid on `I_y` (the equivalence closure of the links;
it is `YEquiv` by `ySetoid_iff`). -/
def ySetoid (y : X) : Setoid {i // y ∈ M i} := Relation.EqvGen.setoid (G.IsLink M y)

theorem ySetoid_iff (hM : ∀ i, M i ∈ S) {y : X} {i j : {i // y ∈ M i}} :
    G.ySetoid M y i j ↔ G.YEquiv M y i j := by
  change Relation.EqvGen _ i j ↔ _
  constructor
  · intro h
    exact (G.equivalence_yEquiv M hM y).eqvGen_iff.1
      (h.mono fun a b hab => Relation.ReflTransGen.single hab)
  · intro h
    induction h with
    | refl => exact Relation.EqvGen.refl _
    | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)

/-- **The note in Definition 9.4.7**: `i ∼_y i'` implies `T_yMᵢ = T_yMᵢ'`. -/
theorem submanifoldTangent_eq_of_yEquiv (hM : ∀ i, M i ∈ S) {y : X} {i j : {i // y ∈ M i}}
    (h : G.YEquiv M y i j) : P.submanifoldTangent (M i) y = P.submanifoldTangent (M j) y := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (G.submanifoldTangent_eq _ (hM _) _ (hM _) y hbc)

/-- `♯P_y`, the number of classes of the partition `P_y = I_y / ∼_y`. -/
def numClasses (y : X) : ℕ := Nat.card (Quotient (G.ySetoid M y))

/-- **`M_U^* = {y ∈ M_U | ♯P_y = 1}`** (2021 p. 433), the points where all of `I_y` is one
class. -/
def MStar : Set X := {y | y ∈ ⋃ i, M i ∧ G.numClasses M y = 1}

/-- **Measure zero in `M_U = ⋃ Mᵢ`**: `A ∩ Mᵢ` has measure zero in `Mᵢ` for every `i`. -/
def IsNullIn (A : Set X) : Prop := ∀ i, G.IsNull (M i) (A ∩ M i)

theorem IsNullIn.mono {M : ι → Set X} {A A' : Set X} (h : G.IsNullIn M A') (hA : A ⊆ A') :
    G.IsNullIn M A := fun i => G.isNull_mono (h i) (inter_subset_inter_left _ hA)

theorem one_le_numClasses [Finite ι] {y : X} (hy : y ∈ ⋃ i, M i) : 1 ≤ G.numClasses M y := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 hy
  have : Nonempty (Quotient (G.ySetoid M y)) := ⟨Quotient.mk _ ⟨i, hi⟩⟩
  exact Nat.card_pos

/-- **Lemma 9.4.8, 2021 p. 432 (2017: Lemma 9.15)**: `{y ∈ M_U | ♯(I_y / ∼_y) ≥ 2}` has measure
zero (in every `Mᵢ`).  As we read it, the text's last step, "`⋃_{j, j' ∈ I} K(j, j')^{ne}` has
measure zero", needs care: `K(j, j')^{ne}` has measure zero in `Mⱼ`, not in an arbitrary `Mᵢ`;
the proof here uses, inside `Mᵢ`, only the sets `K(i, j)^{ne}` (if `♯P_y ≥ 2`, some `j ∈ I_y` is
not `y`-equivalent to `i`, so `y ∈ K(i, j)^{ne}`). -/
theorem lemma_9_4_8 [Finite ι] (hM : ∀ i, M i ∈ S) :
    G.IsNullIn M {y | y ∈ ⋃ i, M i ∧ 2 ≤ G.numClasses M y} := by
  intro i
  refine G.isNull_mono (G.isNull_iUnion fun j => G.isNull_diff_ess _ (hM i) _ (hM j)) ?_
  rintro y ⟨⟨-, h2⟩, hyi⟩
  have : Nontrivial (Quotient (G.ySetoid M y)) := Finite.one_lt_card_iff_nontrivial.1 h2
  obtain ⟨q, hq⟩ := exists_ne (Quotient.mk _ ⟨i, hyi⟩ : Quotient (G.ySetoid M y))
  induction q using Quotient.inductionOn with
  | h j =>
    refine mem_iUnion.2 ⟨j.1, ⟨hyi, j.2⟩, fun hess => hq ?_⟩
    exact (Quotient.sound (Relation.EqvGen.rel _ _ hess)).symm

/-- `M_U ∖ M_U^*` has measure zero (the first claim of Proposition 9.4.9). -/
theorem isNullIn_diff_MStar [Finite ι] (hM : ∀ i, M i ∈ S) :
    G.IsNullIn M ((⋃ i, M i) \ G.MStar M) := by
  refine IsNullIn.mono G (G.lemma_9_4_8 M hM) ?_
  rintro y ⟨hy, hns⟩
  refine ⟨hy, ?_⟩
  have h1 := G.one_le_numClasses M hy
  have h2 : G.numClasses M y ≠ 1 := fun h => hns ⟨hy, h⟩
  omega

/-- On `M_U^*` all indices of `I_y` are `y`-equivalent. -/
theorem yEquiv_of_mem_MStar (hM : ∀ i, M i ∈ S) {y : X} (hy : y ∈ G.MStar M)
    (i j : {i // y ∈ M i}) : G.YEquiv M y i j := by
  have : Subsingleton (Quotient (G.ySetoid M y)) := (Nat.card_eq_one_iff_unique.1 hy.2).1
  exact (G.ySetoid_iff M hM).1
    (Quotient.exact (Subsingleton.elim (Quotient.mk _ i) (Quotient.mk _ j)))

/-- On `M_U^*` all the tangent spaces `T_yMᵢ`, `i ∈ I_y`, agree. -/
theorem submanifoldTangent_eq_of_mem_MStar (hM : ∀ i, M i ∈ S) {y : X} (hy : y ∈ G.MStar M)
    {i j : ι} (hi : y ∈ M i) (hj : y ∈ M j) :
    P.submanifoldTangent (M i) y = P.submanifoldTangent (M j) y :=
  G.submanifoldTangent_eq_of_yEquiv M hM (G.yEquiv_of_mem_MStar M hM hy ⟨i, hi⟩ ⟨j, hj⟩)

open scoped Classical in
/-- **`M_U^J = {y ∈ M_U^* | I_y = J}`** (2021 p. 433). -/
def MStarPart [Fintype ι] (J : Finset ι) : Set X :=
  {y | y ∈ G.MStar M ∧ Finset.univ.filter (fun i => y ∈ M i) = J}

theorem MStar_eq_iUnion [Fintype ι] : G.MStar M = ⋃ J, G.MStarPart M J := by
  ext y
  simp only [MStarPart, mem_iUnion]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

theorem pairwise_disjoint_MStarPart [Fintype ι] :
    Pairwise (Function.onFun Disjoint (G.MStarPart M)) :=
  fun _ _ hJ => Set.disjoint_left.2 fun _ h h' => hJ (h.2.symm.trans h'.2)

end SheetGeometry

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

namespace LocalBranchingStructure

variable {Θ : Obj → ℚ} {x : Obj}

open scoped Classical in
/-- `TΘ(y) = ∑_{i ∈ I_y} σᵢ · T_yMᵢ` at every `y ∈ U(x)` (Theorem 9.2.1's independence). -/
theorem tangentValue_eq_sum (B : X.LocalBranchingStructure Θ x)
    (hind : X.HasIndependentTangentSums Θ) {y : Obj} (hy : y ∈ B.U) :
    X.tangentValue Θ y =
      ∑ i with y ∈ B.M i, Finsupp.single (X.PObj.submanifoldTangent (B.M i) y) (B.σ i) := by
  rw [X.tangentValue_eq hind (B.restrictAt hy), LocalBranchingStructure.tangentSum,
    Finset.sum_subtype (Finset.univ.filter fun i => y ∈ B.M i) (p := fun i => y ∈ B.M i)
      (F := (B.restrictAt hy).fintype) (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LocalBranchingStructure.restrictAt_M,
    MPolyfold.submanifoldTangent_inter_isOpen (B.isOpen_nbhdAt y) (B.mem_nbhdAt_self hy)]
  rfl

open scoped Classical in
/-- `∑_{i ∈ I_y} σᵢ > 0` exactly on `M_U`. -/
theorem sum_pos_iff (B : X.LocalBranchingStructure Θ x) (y : Obj) :
    0 < ∑ i with y ∈ B.M i, B.σ i ↔ ∃ i, y ∈ B.M i := by
  refine ⟨fun h => ?_, fun ⟨i, hi⟩ => Finset.sum_pos (fun j _ => B.σ_pos j) ⟨i, by simp [hi]⟩⟩
  by_contra hn
  push Not at hn
  rw [Finset.filter_false_of_mem fun i _ => hn i, Finset.sum_empty] at h
  exact lt_irrefl 0 h

end LocalBranchingStructure

namespace OrientedBranchingStructure

variable {Θ : Obj → ℚ} {x : Obj} (B : X.OrientedBranchingStructure Θ x)

/-- **Property (T)** (2021 p. 430) on a set `V`: if `y₀ ∈ Mᵢ ∩ Mᵢ'` has `T_{y₀}Mᵢ = T_{y₀}Mᵢ'` and
`o_{i,y₀} = ε · o_{i',y₀}`, then `T_y(Mᵢ, oᵢ) = T_y(Mᵢ', ε · oᵢ')` at every `y ∈ Mᵢ ∩ Mᵢ'` with
`T_yMᵢ = T_yMᵢ'`.  A tangent set has exactly two orientations, so for `ε = 1` this says "equal at
`y₀` implies equal at `y`" and for `ε = -1` "different at `y₀` implies different at `y`"; together,
over all pairs `y₀, y`, the iff below. -/
def PropertyT (V : Set Obj) : Prop :=
  ∀ i i' : B.ι, ∀ y₀ ∈ V ∩ B.M i ∩ B.M i', ∀ y ∈ V ∩ B.M i ∩ B.M i',
    X.PObj.submanifoldTangent (B.M i) y₀ = X.PObj.submanifoldTangent (B.M i') y₀ →
    X.PObj.submanifoldTangent (B.M i) y = X.PObj.submanifoldTangent (B.M i') y →
    ((B.orient i).tangent y₀ = (B.orient i').tangent y₀ ↔
      (B.orient i).tangent y = (B.orient i').tangent y)

theorem isOrientedAt_tangent {i : B.ι} {y : Obj} (hy : y ∈ B.M i) :
    X.PObj.IsOrientedAt y ((B.orient i).tangent y) :=
  (B.orient i).isOrientedAt_tangent hy

end OrientedBranchingStructure

open MPolyfold OrientedBranchingStructure

variable {Θ : Obj → ℚ} {x : Obj}

open scoped Classical in
/-- **Proposition 9.4.9, 2021 p. 434 (2017: Proposition 9.5)**: for an oriented local branching
structure with Property (T) whose sheets carry a `SheetGeometry`, `M_U^* = {y ∈ M_U | ♯P_y = 1}`
differs from `M_U` by a set of measure zero and is the disjoint union of the `M_U^J`,
`J ⊆ I`; on `M_U^J`, for a partition `J = A_J ⊔ B_J` not depending on `y` (it is fixed by
Property (T)):
(1) `Θ(y) = σ_J = ∑_{i ∈ J} σᵢ`; (2) `TΘ(y) = σ_J · T_y^J` (`T_y^J = T_yMᵢ` for any `i ∈ J`);
(3) `T̂Θ(y) = a_J · (T_y^J, o_a) + b_J · (T_y^J, o_b)`, `a_J = ∑_{A_J} σᵢ`, `b_J = ∑_{B_J} σᵢ`;
(4) `a_J + b_J = σ_J` and `o_a = -o_b` (`o_a ≠ o_b` are the two orientations of `T_y^J`; if
`B_J = ∅`, `o_b` is the orientation opposite to `o_a`). -/
theorem proposition_9_4_9 {S : Set (Set Obj)} (G : X.PObj.SheetGeometry S)
    (B : X.OrientedBranchingStructure Θ x) (hS : ∀ i, B.M i ∈ S)
    (hind : X.HasIndependentTangentSums Θ) (hT : B.PropertyT B.U) :
    G.IsNullIn B.M (B.MU \ G.MStar B.M) ∧ G.MStar B.M = ⋃ J, G.MStarPart B.M J ∧
    Pairwise (Function.onFun Disjoint (G.MStarPart B.M)) ∧
    ∀ J : Finset B.ι, ∃ AJ ⊆ J, ∀ y ∈ G.MStarPart B.M J,
      Θ y = ∑ i ∈ J, B.σ i ∧
      (∀ i ∈ J, X.tangentValue Θ y =
        Finsupp.single (X.PObj.submanifoldTangent (B.M i) y) (∑ j ∈ J, B.σ j)) ∧
      ∃ ga gb : X.PObj.OrTangent, X.PObj.IsOrientedAt y ga ∧ X.PObj.IsOrientedAt y gb ∧
        ga ≠ gb ∧ (∀ i ∈ J, ga.carrier = X.PObj.submanifoldTangent (B.M i) y ∧
          gb.carrier = X.PObj.submanifoldTangent (B.M i) y) ∧
        (∀ i ∈ AJ, (B.orient i).tangent y = ga) ∧ (∀ i ∈ J \ AJ, (B.orient i).tangent y = gb) ∧
        B.orientedSum y =
          Finsupp.single ga (∑ i ∈ AJ, B.σ i) + Finsupp.single gb (∑ i ∈ J \ AJ, B.σ i) ∧
        (∑ i ∈ AJ, B.σ i) + (∑ i ∈ J \ AJ, B.σ i) = ∑ i ∈ J, B.σ i := by
  refine ⟨G.isNullIn_diff_MStar B.M hS, G.MStar_eq_iUnion B.M, G.pairwise_disjoint_MStarPart B.M,
    fun J => ?_⟩
  have hU : ∀ {y}, y ∈ G.MStar B.M → y ∈ B.U := fun hy => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hy.1
    exact B.subset_U i hi
  have hJmem : ∀ {y}, y ∈ G.MStarPart B.M J → ∀ {i}, i ∈ J ↔ y ∈ B.M i := fun hy i => by
    rw [← hy.2]
    simp
  rcases J.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · refine ⟨∅, Finset.empty_subset _, fun y hy => ?_⟩
    exfalso
    obtain ⟨i, hi⟩ := mem_iUnion.1 hy.1.1
    exact Finset.notMem_empty i ((hJmem hy).2 hi)
  set AJ := J.filter (fun i => ∃ y₀ ∈ G.MStarPart B.M J,
    (B.orient i).tangent y₀ = (B.orient i₀).tangent y₀) with hAJ
  have hAJJ : AJ ⊆ J := Finset.filter_subset _ _
  refine ⟨AJ, hAJJ, fun y hy => ?_⟩
  have hyU := hU hy.1
  have hMi : ∀ {i}, i ∈ J → y ∈ B.M i := fun hi => (hJmem hy).1 hi
  have hTeq : ∀ {i j}, i ∈ J → j ∈ J →
      X.PObj.submanifoldTangent (B.M i) y = X.PObj.submanifoldTangent (B.M j) y :=
    fun hi hj => G.submanifoldTangent_eq_of_mem_MStar B.M hS hy.1 (hMi hi) (hMi hj)
  refine ⟨(B.eq_sum y hyU).trans (by rw [hy.2]), fun i hi => ?_, ?_⟩
  · rw [B.toLocalBranchingStructure.tangentValue_eq_sum hind hyU, hy.2, Finsupp.single_finsetSum]
    exact Finset.sum_congr rfl fun j hj => by rw [hTeq hj hi]
  set ga := (B.orient i₀).tangent y with hga
  have hA : ∀ i ∈ AJ, (B.orient i).tangent y = ga := by
    intro i hi
    obtain ⟨hiJ, y₀, hy₀, he⟩ := Finset.mem_filter.1 hi
    exact (hT i i₀ y₀ ⟨⟨hU hy₀.1, (hJmem hy₀).1 hiJ⟩, (hJmem hy₀).1 hi₀⟩ y
      ⟨⟨hyU, hMi hiJ⟩, hMi hi₀⟩
      (G.submanifoldTangent_eq_of_mem_MStar B.M hS hy₀.1 ((hJmem hy₀).1 hiJ) ((hJmem hy₀).1 hi₀))
      (hTeq hiJ hi₀)).1 he
  have hB : ∀ i ∈ J \ AJ, (B.orient i).tangent y ≠ ga := by
    intro i hi he
    obtain ⟨hiJ, hiA⟩ := Finset.mem_sdiff.1 hi
    exact hiA (Finset.mem_filter.2 ⟨hiJ, y, hy, he⟩)
  obtain ⟨gb, hgb, hgbne, hgbc⟩ : ∃ gb : X.PObj.OrTangent, X.PObj.IsOrientedAt y gb ∧ gb ≠ ga ∧
      gb.carrier = ga.carrier := by
    rcases (J \ AJ).eq_empty_or_nonempty with h | ⟨i, hi⟩
    · obtain ⟨O', hO', hO'o⟩ := exists_ne_isOrientedAt (B.isSubmanifoldOfDim i₀) (hMi hi₀)
        ((B.orient i₀).frames y)
      refine ⟨⟨B.dim i₀, X.PObj.submanifoldTangent (B.M i₀) y, O'⟩, hO'o, fun e => hO' ?_, rfl⟩
      rw [hga] at e
      change (⟨B.dim i₀, _, O'⟩ : X.PObj.OrTangent) =
        ⟨B.dim i₀, X.PObj.submanifoldTangent (B.M i₀) y, (B.orient i₀).frames y⟩ at e
      simpa using e
    · exact ⟨_, B.isOrientedAt_tangent (hMi (Finset.mem_sdiff.1 hi).1), hB i hi,
        hTeq (Finset.mem_sdiff.1 hi).1 hi₀⟩
  have hBgb : ∀ i ∈ J \ AJ, (B.orient i).tangent y = gb := by
    intro i hi
    have hiJ := (Finset.mem_sdiff.1 hi).1
    rcases OrTangent.eq_or_eq_or_eq_of_isOrientedAt (B.isOrientedAt_tangent (hMi hi₀))
      (B.isOrientedAt_tangent (hMi hiJ)) hgb (hTeq hi₀ hiJ) hgbc.symm with e | e | e
    · exact (hB i hi e.symm).elim
    · exact (hgbne e.symm).elim
    · exact e
  refine ⟨ga, gb, B.isOrientedAt_tangent (hMi hi₀), hgb, fun e => hgbne e.symm,
    fun i hi => ⟨hTeq hi₀ hi, hgbc.trans (hTeq hi₀ hi)⟩, hA, hBgb, ?_, ?_⟩
  · rw [OrientedBranchingStructure.orientedSum, hy.2, ← Finset.sum_sdiff hAJJ, add_comm,
      Finsupp.single_finsetSum, Finsupp.single_finsetSum]
    congr 1
    · exact Finset.sum_congr rfl fun i hi => by rw [hA i hi]
    · exact Finset.sum_congr rfl fun i hi => by rw [hBgb i hi]
  · rw [add_comm]
    exact Finset.sum_sdiff hAJJ

/-- **The sign map `K(i, i')^e → {±1}` (2021 p. 431) is constant under Property (T)**: at any two
essential points of `K(i, i') = Mᵢ ∩ Mᵢ'` the oriented tangents of `(Mᵢ, oᵢ)` and `(Mᵢ', oᵢ')`
agree at both or at neither. -/
theorem tangent_eq_iff_of_mem_ess {S : Set (Set Obj)} (G : X.PObj.SheetGeometry S)
    {B : X.OrientedBranchingStructure Θ x} (hS : ∀ i, B.M i ∈ S) (hT : B.PropertyT B.U)
    {i i' : B.ι} {y₀ y : Obj} (hy₀ : y₀ ∈ G.ess (B.M i) (B.M i ∩ B.M i'))
    (hy : y ∈ G.ess (B.M i) (B.M i ∩ B.M i')) :
    ((B.orient i).tangent y₀ = (B.orient i').tangent y₀ ↔
      (B.orient i).tangent y = (B.orient i').tangent y) := by
  have m₀ := G.ess_subset _ _ hy₀
  have m := G.ess_subset _ _ hy
  exact hT i i' y₀ ⟨⟨B.subset_U i m₀.1, m₀.1⟩, m₀.2⟩ y ⟨⟨B.subset_U i m.1, m.1⟩, m.2⟩
    (G.submanifoldTangent_eq _ (hS i) _ (hS i') y₀ hy₀)
    (G.submanifoldTangent_eq _ (hS i) _ (hS i') y hy)

open scoped Classical in
/-- **Proposition 9.4.10, 2021 p. 435 (2017: Proposition 9.6)**: two oriented local branching
structures `(Mᵢ, oᵢ)_{i ∈ I}, (σᵢ)` and `(M'ᵢ', o'ᵢ')_{i' ∈ I'}, (σ'ᵢ')` on the same `U(x)` with
(a) `∑_{y ∈ Mᵢ} σᵢ = ∑_{y ∈ M'ᵢ'} σ'ᵢ'` and (b) `∑_{y ∈ Mᵢ} σᵢ · T_y(Mᵢ, oᵢ) =
∑_{y ∈ M'ᵢ'} σ'ᵢ' · T_y(M'ᵢ', o'ᵢ')` on `U(x)`.  Then `M_U = ⋃ Mᵢ = ⋃ M'ᵢ'`, and there are
`M_U^† ⊆ M_U` and a finite partition `M_U^† = A₁ ⊔ … ⊔ A_ℓ` with: (1) `M_U ∖ M_U^†` has measure
zero; (2) on every `A_p`, `I_y = J` and `I'_y = J'` are constant and all `T_yMᵢ`, `T_yM'ᵢ'`
(`i ∈ J`, `i' ∈ J'`) agree; (3) `∑_{J} σᵢ = ∑_{J'} σ'ᵢ'`; (4) partitions `J = J₊ ⊔ J₋`,
`J' = J'₊ ⊔ J'₋` (constant on `A_p`) such that all `T_y(Mᵢ, oᵢ)`, `i ∈ J₊`, and `T_y(M'ᵢ', o'ᵢ')`,
`i' ∈ J'₊`, agree, and likewise for `J₋, J'₋`; (5) `[∑_{J±} σⱼ] · T_y(M_{i±}, o_{i±}) =
[∑_{J'±} σ'ⱼ'] · T_y(M'_{i'±}, o'_{i'±})`.

As in the text, `M_U^†` is built from the union structure `B'' = B ⊔ B'` (here `M_U^† = M_U''^*`;
the text intersects it with `M_U^*` and `M_U'^*`, which is not needed for (1)–(5)).  The text
assumes Property (T) for both structures; the proof here does not use it: the pieces `A_p` are
cut out by the values of `y ↦ (I_y, I'_y, J₊(y), J'₊(y))`, finitely many. -/
theorem proposition_9_4_10 {S : Set (Set Obj)} (G : X.PObj.SheetGeometry S) {Θ' : Obj → ℚ}
    (B : X.OrientedBranchingStructure Θ x) (B' : X.OrientedBranchingStructure Θ' x)
    (hS : ∀ i, B.M i ∈ S) (hS' : ∀ i, B'.M i ∈ S) (hU : B.U = B'.U)
    (ha : ∀ y ∈ B.U, ∑ i with y ∈ B.M i, B.σ i = ∑ i with y ∈ B'.M i, B'.σ i)
    (hb : ∀ y ∈ B.U, B.orientedSum y = B'.orientedSum y) :
    B.MU = B'.MU ∧ ∃ (MUd : Set Obj) (ℓ : ℕ) (A : Fin ℓ → Set Obj), MUd ⊆ B.MU ∧
      G.IsNullIn B.M (B.MU \ MUd) ∧ G.IsNullIn B'.M (B.MU \ MUd) ∧
      Pairwise (Function.onFun Disjoint A) ∧ (⋃ p, A p) = MUd ∧
      ∀ p, ∃ (J : Finset B.ι) (J' : Finset B'.ι) (Jp : Finset B.ι) (Jp' : Finset B'.ι),
        Jp ⊆ J ∧ Jp' ⊆ J' ∧ ∀ y ∈ A p,
          Finset.univ.filter (fun i => y ∈ B.M i) = J ∧
          Finset.univ.filter (fun i => y ∈ B'.M i) = J' ∧
          (∀ i ∈ J, ∀ j ∈ J,
            X.PObj.submanifoldTangent (B.M i) y = X.PObj.submanifoldTangent (B.M j) y) ∧
          (∀ i ∈ J, ∀ i' ∈ J',
            X.PObj.submanifoldTangent (B.M i) y = X.PObj.submanifoldTangent (B'.M i') y) ∧
          (∀ i' ∈ J', ∀ j' ∈ J',
            X.PObj.submanifoldTangent (B'.M i') y = X.PObj.submanifoldTangent (B'.M j') y) ∧
          ∑ i ∈ J, B.σ i = ∑ i ∈ J', B'.σ i ∧
          (∀ i ∈ J, ∀ j ∈ J, (i ∈ Jp ↔ j ∈ Jp) →
            (B.orient i).tangent y = (B.orient j).tangent y) ∧
          (∀ i ∈ J, ∀ i' ∈ J', (i ∈ Jp ↔ i' ∈ Jp') →
            (B.orient i).tangent y = (B'.orient i').tangent y) ∧
          (∀ i' ∈ J', ∀ j' ∈ J', (i' ∈ Jp' ↔ j' ∈ Jp') →
            (B'.orient i').tangent y = (B'.orient j').tangent y) ∧
          (∀ i ∈ Jp, ∀ i' ∈ Jp', Finsupp.single ((B.orient i).tangent y) (∑ j ∈ Jp, B.σ j) =
            Finsupp.single ((B'.orient i').tangent y) (∑ j ∈ Jp', B'.σ j)) ∧
          (∀ i ∈ J \ Jp, ∀ i' ∈ J' \ Jp',
            Finsupp.single ((B.orient i).tangent y) (∑ j ∈ J \ Jp, B.σ j) =
              Finsupp.single ((B'.orient i').tangent y) (∑ j ∈ J' \ Jp', B'.σ j)) := by
  -- `M_U = M_U'`
  have hMU : B.MU = B'.MU := by
    ext y
    simp only [LocalBranchingStructure.MU, mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      have hyU := B.subset_U i hi
      exact (B'.toLocalBranchingStructure.sum_pos_iff y).1
        ((ha y hyU) ▸ (B.toLocalBranchingStructure.sum_pos_iff y).2 ⟨i, hi⟩)
    · rintro ⟨i, hi⟩
      have hyU : y ∈ B.U := hU ▸ B'.subset_U i hi
      exact (B.toLocalBranchingStructure.sum_pos_iff y).1
        ((ha y hyU).symm ▸ (B'.toLocalBranchingStructure.sum_pos_iff y).2 ⟨i, hi⟩)
  refine ⟨hMU, ?_⟩
  -- the union structure
  set M'' : B.ι ⊕ B'.ι → Set Obj := Sum.elim B.M B'.M with hM''
  have hS'' : ∀ k, M'' k ∈ S := by
    rintro (i | i)
    exacts [hS i, hS' i]
  have hsub : G.MStar M'' ⊆ B.MU := by
    intro y hy
    obtain ⟨k, hk⟩ := mem_iUnion.1 hy.1
    rcases k with i | i
    · exact mem_iUnion.2 ⟨i, hk⟩
    · rw [hMU]
      exact mem_iUnion.2 ⟨i, hk⟩
  have hnull := G.isNullIn_diff_MStar M'' hS''
  have hdiff : B.MU \ G.MStar M'' ⊆ (⋃ k, M'' k) \ G.MStar M'' := by
    rintro y ⟨hy, hns⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    exact ⟨mem_iUnion.2 ⟨Sum.inl i, hi⟩, hns⟩
  -- the pieces
  let g : Obj → X.PObj.OrTangent := fun y =>
    if h : ∃ i, y ∈ B.M i then (B.orient h.choose).tangent y else ⟨0, ∅, ∅⟩
  let key : Obj → Finset B.ι × Finset B'.ι × Finset B.ι × Finset B'.ι := fun y =>
    (Finset.univ.filter (fun i => y ∈ B.M i), Finset.univ.filter (fun i => y ∈ B'.M i),
      (Finset.univ.filter (fun i => y ∈ B.M i)).filter (fun i => (B.orient i).tangent y = g y),
      (Finset.univ.filter (fun i => y ∈ B'.M i)).filter (fun i => (B'.orient i).tangent y = g y))
  let Akey : Finset B.ι × Finset B'.ι × Finset B.ι × Finset B'.ι → Set Obj := fun k =>
    {y | y ∈ G.MStar M'' ∧ key y = k}
  let e := Fintype.equivFin (Finset B.ι × Finset B'.ι × Finset B.ι × Finset B'.ι)
  refine ⟨G.MStar M'', _, fun p => Akey (e.symm p), hsub,
    fun i => G.isNull_mono (hnull (Sum.inl i)) (inter_subset_inter_left _ hdiff),
    fun i => G.isNull_mono (hnull (Sum.inr i)) (inter_subset_inter_left _ hdiff), ?_, ?_, ?_⟩
  · intro p q hpq
    refine Set.disjoint_left.2 fun y hp hq => hpq (e.symm.injective ?_)
    exact hp.2.symm.trans hq.2
  · ext y
    simp only [mem_iUnion]
    refine ⟨fun ⟨_, hy⟩ => hy.1, fun hy => ⟨e (key y), hy, by simp⟩⟩
  intro p
  generalize hk : e.symm p = k
  refine ⟨k.1, k.2.1, k.1 ∩ k.2.2.1, k.2.1 ∩ k.2.2.2, Finset.inter_subset_left,
    Finset.inter_subset_left, ?_⟩
  rintro y ⟨hy, hky⟩
  rw [hk] at hky
  subst hky
  simp only [key]
  rw [Finset.inter_eq_right.2 (Finset.filter_subset _ _),
    Finset.inter_eq_right.2 (Finset.filter_subset _ _)]
  -- pointwise facts at `y ∈ M_U''^*`
  have hyU : y ∈ B.U := by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hsub hy)
    exact B.subset_U i hi
  have hT'' : ∀ {k l}, y ∈ M'' k → y ∈ M'' l →
      X.PObj.submanifoldTangent (M'' k) y = X.PObj.submanifoldTangent (M'' l) y :=
    fun hk hl => G.submanifoldTangent_eq_of_mem_MStar M'' hS'' hy hk hl
  have hex : ∃ i, y ∈ B.M i := mem_iUnion.1 (hsub hy)
  have hr : y ∈ B.M hex.choose := hex.choose_spec
  have hg : g y = (B.orient hex.choose).tangent y := dif_pos hex
  have hgo : X.PObj.IsOrientedAt y (g y) := hg ▸ B.isOrientedAt_tangent hr
  have hgc : ∀ {i}, y ∈ B.M i → (g y).carrier = X.PObj.submanifoldTangent (B.M i) y :=
    fun hi => by rw [hg]; exact hT'' (k := Sum.inl _) (l := Sum.inl _) hr hi
  have hgc' : ∀ {i}, y ∈ B'.M i → (g y).carrier = X.PObj.submanifoldTangent (B'.M i) y :=
    fun hi => by rw [hg]; exact hT'' (k := Sum.inl _) (l := Sum.inr _) hr hi
  have mem1 : ∀ {i}, i ∈ Finset.univ.filter (fun i => y ∈ B.M i) ↔ y ∈ B.M i := by simp
  have mem2 : ∀ {i}, i ∈ Finset.univ.filter (fun i => y ∈ B'.M i) ↔ y ∈ B'.M i := by simp
  have memp : ∀ {i}, i ∈ (Finset.univ.filter (fun i => y ∈ B.M i)).filter
      (fun i => (B.orient i).tangent y = g y) ↔ y ∈ B.M i ∧ (B.orient i).tangent y = g y := by
    simp
  have memp' : ∀ {i}, i ∈ (Finset.univ.filter (fun i => y ∈ B'.M i)).filter
      (fun i => (B'.orient i).tangent y = g y) ↔ y ∈ B'.M i ∧ (B'.orient i).tangent y = g y := by
    simp
  have h4 : ∀ {i j}, y ∈ B.M i → y ∈ B.M j →
      ((B.orient i).tangent y = g y ↔ (B.orient j).tangent y = g y) →
      (B.orient i).tangent y = (B.orient j).tangent y := fun hi hj h =>
    OrTangent.eq_of_iff_eq hgo (B.isOrientedAt_tangent hi) (B.isOrientedAt_tangent hj) (hgc hi)
      (hgc hj) h
  have h4' : ∀ {i i'}, y ∈ B.M i → y ∈ B'.M i' →
      ((B.orient i).tangent y = g y ↔ (B'.orient i').tangent y = g y) →
      (B.orient i).tangent y = (B'.orient i').tangent y := fun hi hj h =>
    OrTangent.eq_of_iff_eq hgo (B.isOrientedAt_tangent hi) (B'.isOrientedAt_tangent hj)
      (hgc hi) (hgc' hj) h
  have h4'' : ∀ {i i'}, y ∈ B'.M i → y ∈ B'.M i' →
      ((B'.orient i).tangent y = g y ↔ (B'.orient i').tangent y = g y) →
      (B'.orient i).tangent y = (B'.orient i').tangent y := fun hi hj h =>
    OrTangent.eq_of_iff_eq hgo (B'.isOrientedAt_tangent hi) (B'.isOrientedAt_tangent hj)
      (hgc' hi) (hgc' hj) h
  -- the sums `∑_{T_y(Mᵢ, oᵢ) = h} σᵢ`
  have hsum : ∀ h, ∑ i ∈ (Finset.univ.filter (fun i => y ∈ B.M i)).filter
      (fun i => (B.orient i).tangent y = h), B.σ i =
      ∑ i ∈ (Finset.univ.filter (fun i => y ∈ B'.M i)).filter
        (fun i => (B'.orient i).tangent y = h), B'.σ i := fun h => by
    rw [Finset.sum_filter (fun i => (B.orient i).tangent y = h),
      Finset.sum_filter (fun i => (B'.orient i).tangent y = h), ← B.orientedSum_apply,
      ← B'.orientedSum_apply, hb y hyU]
  refine ⟨True.intro, True.intro,
    fun i hi j hj => hT'' (k := Sum.inl i) (l := Sum.inl j) (mem1.1 hi) (mem1.1 hj),
    fun i hi j hj => hT'' (k := Sum.inl i) (l := Sum.inr j) (mem1.1 hi) (mem2.1 hj),
    fun i hi j hj => hT'' (k := Sum.inr i) (l := Sum.inr j) (mem2.1 hi) (mem2.1 hj),
    ha y hyU, fun i hi j hj h => h4 (mem1.1 hi) (mem1.1 hj) ?_,
    fun i hi j hj h => h4' (mem1.1 hi) (mem2.1 hj) ?_,
    fun i hi j hj h => h4'' (mem2.1 hi) (mem2.1 hj) ?_, fun i hi j hj => ?_,
    fun i hi j hj => ?_⟩
  · simpa [memp, mem1.1 hi, mem1.1 hj] using h
  · simpa [memp, memp', mem1.1 hi, mem2.1 hj] using h
  · simpa [memp', mem2.1 hi, mem2.1 hj] using h
  · rw [(memp.1 hi).2, (memp'.1 hj).2, hsum (g y)]
  · obtain ⟨hiJ, hiJp⟩ := Finset.mem_sdiff.1 hi
    obtain ⟨hjJ, hjJp⟩ := Finset.mem_sdiff.1 hj
    have hi' : (B.orient i).tangent y ≠ g y := fun e => hiJp (memp.2 ⟨mem1.1 hiJ, e⟩)
    have hj' : (B'.orient j).tangent y ≠ g y := fun e => hjJp (memp'.2 ⟨mem2.1 hjJ, e⟩)
    have hij := h4' (mem1.1 hiJ) (mem2.1 hjJ) (iff_of_false hi' hj')
    have e1 : (Finset.univ.filter (fun i => y ∈ B.M i)).filter
        (fun k => (B.orient k).tangent y = (B.orient i).tangent y) =
        Finset.univ.filter (fun i => y ∈ B.M i) \ (Finset.univ.filter (fun i => y ∈ B.M i)).filter
          (fun i => (B.orient i).tangent y = g y) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, not_and]
      refine ⟨fun ⟨hk, he⟩ => ⟨hk, fun _ hg' => hi' (he.symm.trans hg')⟩,
        fun ⟨hk, hn⟩ => ⟨hk, h4 hk (mem1.1 hiJ) (iff_of_false (hn hk) hi')⟩⟩
    have e2 : (Finset.univ.filter (fun i => y ∈ B'.M i)).filter
        (fun k => (B'.orient k).tangent y = (B.orient i).tangent y) =
        Finset.univ.filter (fun i => y ∈ B'.M i) \ (Finset.univ.filter (fun i => y ∈ B'.M i)).filter
          (fun i => (B'.orient i).tangent y = g y) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, not_and]
      exact ⟨fun ⟨hk, he⟩ => ⟨hk, fun _ hg' => hi' (he.symm.trans hg')⟩,
        fun ⟨hk, hn⟩ => ⟨hk, (h4'' hk (mem2.1 hjJ) (iff_of_false (hn hk) hj')).trans hij.symm⟩⟩
    rw [← hij, ← e1, ← e2, hsum]

end EpGroupoid

end Polyfold

namespace Polyfold

open EpGroupoid MPolyfold

/-! ### Lemma 9.4.4 between manifolds of different dimensions -/

/-- **Lemma 9.4.4 does not hold as we read it when `dim Mᵢ ≠ dim Mᵢ'`**: for `Mᵢ = ℝ × 0` (a
line, here `ℝ` itself) and `Mᵢ' = ℝ²`, `K = Mᵢ ∩ Mᵢ' = ℝ × 0` (`lineH`, the image of `ℝ` under
`s ↦ (s, 0)`): every point is essential for `K ⊆ Mᵢ`, none for `K ⊆ Mᵢ'`.  (With equal dimensions,
the standing assumption of §9.5, the two notions agree; see `SheetGeometry.ess_comm`.) -/
theorem lemma_9_4_4_mixed_dim :
    essentialSet 𝓘(ℝ, ℝ) (univ : Set ℝ) = univ ∧
      essentialSet 𝓘(ℝ, Fin 2 → ℝ) (lineH : Set (Fin 2 → ℝ)) = ∅ ∧
      range (fun s : ℝ => (Pi.single 0 s : Fin 2 → ℝ)) = lineH := by
  refine ⟨?_, ?_, ?_⟩
  · refine eq_univ_of_forall fun s => ⟨mem_univ s, fun _ => s, fun _ => ⟨mem_univ s, ?_⟩,
      tendsto_const_nhds⟩
    rw [relTangent_self, tangentConeAt_univ, Submodule.span_univ]
  · refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨-, u, hu, -⟩ := hz
    have h := (hu 0).2
    rw [relTangent_self] at h
    have hle : Submodule.span ℝ (tangentConeAt ℝ (lineH : Set (Fin 2 → ℝ)) (u 0)) ≤ lineH :=
      Submodule.span_le.2 (tangentConeAt_subset_submodule isClosed_lineH (hu 0).1)
    rw [h] at hle
    exact lineH_ne_top (top_le_iff.1 hle)
  · ext v
    simp only [mem_range, SetLike.mem_coe, mem_lineH]
    constructor
    · rintro ⟨s, rfl⟩
      simp
    · intro hv
      refine ⟨v 0, ?_⟩
      funext i
      fin_cases i
      · simp
      · simp [hv]

/-! ### Witness: graphs over the first axis of `ℝ²` -/

section GraphSheets

/-- In the real line, `T^A_sℝ = T_sℝ` means unique differentiability of `A` at `s`. -/
theorem relTangent_real_eq_top_iff {A : Set ℝ} {s : ℝ} (hs : s ∈ A) :
    relTangent 𝓘(ℝ, ℝ) A s = ⊤ ↔ UniqueDiffWithinAt ℝ A s := by
  rw [relTangent_self, uniqueDiffWithinAt_iff]
  constructor
  · intro h
    refine ⟨?_, subset_closure hs⟩
    rw [h, Submodule.top_coe]
    exact dense_univ
  · rintro ⟨hd, -⟩
    have hc : IsClosed (Submodule.span ℝ (tangentConeAt ℝ A s) : Set ℝ) :=
      Submodule.closed_of_finiteDimensional _
    refine SetLike.coe_injective ?_
    rw [Submodule.top_coe, ← hc.closure_eq, hd.closure_eq]

theorem continuous_graphPt {β : ℝ → ℝ} (hβ : Continuous β) :
    Continuous fun s : ℝ => (![s, β s] : Fin 2 → ℝ) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simpa using continuous_id'
  · simpa using hβ

theorem image_graph2_inter {β : ℝ → ℝ} {V : Set (Fin 2 → ℝ)} :
    (fun w : Fin 2 → ℝ => w 0) '' (graph2 β ∩ V) = (fun s => ![s, β s]) ⁻¹' V := by
  ext s
  constructor
  · rintro ⟨w, ⟨hw, hwV⟩, rfl⟩
    have hw' : (![w 0, β (w 0)] : Fin 2 → ℝ) = w := by
      funext i
      fin_cases i
      · rfl
      · exact hw.symm
    change (![w 0, β (w 0)] : Fin 2 → ℝ) ∈ V
    rw [hw']
    exact hwV
  · intro hs
    exact ⟨![s, β s], ⟨by simp [mem_graph2_iff], hs⟩, by simp⟩

/-- The sheets of the witness: pieces `graph(β) ∩ V` of graphs of smooth `β : ℝ → ℝ`, `V ⊆ ℝ²`
open. -/
def graphSheets : Set (Set (Fin 2 → ℝ)) :=
  {N | ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ ∃ V, IsOpen V ∧ N = graph2 β ∩ V}

/-- The essential points of `K` in a graph over the first axis, read in the common chart
`z ↦ z 0` (Definition 9.4.1 (2) in `ℝ`). -/
def graphEss (_N K : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  {z | z ∈ K ∧ z 0 ∈ essentialSet 𝓘(ℝ, ℝ) ((fun w : Fin 2 → ℝ => w 0) '' K)}

/-- Measure zero in a graph over the first axis, read in the chart `z ↦ z 0`
(Definition 9.4.5 in `ℝ`). -/
def graphIsNull (_N A : Set (Fin 2 → ℝ)) : Prop :=
  IsMeasureZero 𝓘(ℝ, ℝ) ((fun w : Fin 2 → ℝ => w 0) '' A)

/-- **Satisfiability of `SheetGeometry`**: the graphs of smooth functions over the first axis of
`ℝ²`, with the essential points and null sets of Definitions 9.4.1 and 9.4.5 read in the chart
`z ↦ z 0`; `T_zN = T_zN'` at essential points of `N ∩ N'` since there the slopes agree. -/
def graphSheetGeometry : (rnPolyfold 2).SheetGeometry graphSheets where
  ess := graphEss
  ess_subset _ _ _ hz := hz.1
  ess_self N hN := by
    obtain ⟨β, hβ, V, hV, rfl⟩ := hN
    refine Subset.antisymm (fun z hz => hz.1) fun z hz => ?_
    have hmem : z 0 ∈ (fun w : Fin 2 → ℝ => w 0) '' (graph2 β ∩ V) := ⟨z, hz, rfl⟩
    have htop : relTangent 𝓘(ℝ, ℝ) ((fun w : Fin 2 → ℝ => w 0) '' (graph2 β ∩ V)) (z 0) = ⊤ := by
      rw [relTangent_real_eq_top_iff hmem]
      rw [image_graph2_inter] at hmem ⊢
      exact (hV.preimage (continuous_graphPt hβ.continuous)).uniqueDiffWithinAt hmem
    exact ⟨hz, hmem, fun _ => z 0, fun _ => ⟨hmem, htop⟩, tendsto_const_nhds⟩
  ess_comm N _ N' _ := by simp only [graphEss, inter_comm]
  submanifoldTangent_eq N hN N' hN' z hz := by
    obtain ⟨β, hβ, V, hV, rfl⟩ := hN
    obtain ⟨β', hβ', V', hV', rfl⟩ := hN'
    obtain ⟨⟨⟨hzβ, hzV⟩, hzβ', hzV'⟩, -, u, hu, hlim⟩ := hz
    have hA : ∀ s ∈ (fun w : Fin 2 → ℝ => w 0) '' ((graph2 β ∩ V) ∩ (graph2 β' ∩ V')),
        β s - β' s = 0 := by
      rintro _ ⟨w, ⟨⟨hw, -⟩, hw', -⟩, rfl⟩
      exact sub_eq_zero.2 (hw.symm.trans hw')
    have hd : ∀ k, deriv β (u k) = deriv β' (u k) := by
      intro k
      obtain ⟨huk, htop⟩ := hu k
      have hud := (relTangent_real_eq_top_iff huk).1 htop
      have h1 : HasDerivWithinAt (fun s => β s - β' s) (deriv β (u k) - deriv β' (u k))
          ((fun w : Fin 2 → ℝ => w 0) '' ((graph2 β ∩ V) ∩ (graph2 β' ∩ V'))) (u k) :=
        ((hβ.differentiable (by simp) (u k)).hasDerivAt.sub
          (hβ'.differentiable (by simp) (u k)).hasDerivAt).hasDerivWithinAt
      have h0 : HasDerivWithinAt (fun s => β s - β' s) 0
          ((fun w : Fin 2 → ℝ => w 0) '' ((graph2 β ∩ V) ∩ (graph2 β' ∩ V'))) (u k) :=
        (hasDerivWithinAt_const (u k) _ (0 : ℝ)).congr (fun s hs => hA s hs) (hA _ huk)
      exact sub_eq_zero.1 (UniqueDiffWithinAt.eq_deriv _ hud h1 h0)
    have hc := hβ.continuous_deriv (by simp)
    have hc' := hβ'.continuous_deriv (by simp)
    have hdz : deriv β (z 0) = deriv β' (z 0) := by
      refine tendsto_nhds_unique ((hc.tendsto _).comp hlim) ?_
      have : deriv β ∘ u = deriv β' ∘ u := funext hd
      rw [this]
      exact (hc'.tendsto _).comp hlim
    rw [submanifoldTangent_inter_isOpen hV hzV, submanifoldTangent_inter_isOpen hV' hzV']
    exact submanifoldTangent_graph2_eq hβ hβ' hzβ hzβ' hdz
  IsNull := graphIsNull
  isNull_empty _ := by
    simp only [graphIsNull, image_empty]
    exact isMeasureZero_empty
  isNull_mono h hA := IsMeasureZero.mono h (image_mono hA)
  isNull_union h h' := by
    simp only [graphIsNull, image_union]
    exact h.union h'
  not_isNull_self N hN hne h := by
    obtain ⟨β, hβ, V, hV, rfl⟩ := hN
    obtain ⟨z, hz⟩ := hne
    have h0 := h (chartAt ℝ (z 0)) (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, ℝ)) (n := ∞)
      (z 0))
    rw [chartImage_chartAt_self, image_graph2_inter] at h0
    refine ((hV.preimage (continuous_graphPt hβ.continuous)).measure_pos volume
      ⟨z 0, ?_⟩).ne' h0
    rw [← image_graph2_inter]
    exact ⟨z, hz, rfl⟩
  isNull_diff_ess N _ N' _ := by
    refine IsMeasureZero.mono (lemma_9_4_6 ((fun w : Fin 2 → ℝ => w 0) '' (N ∩ N'))) ?_
    rintro _ ⟨w, ⟨hw, hne⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, fun h => hne ⟨hw, h⟩⟩

/-! ### Witness: Example 9.3.5 -/

section Example935

/-- **Example 9.3.5's first oriented local branching structure** at `x`: the graphs
`G⁺⁺, G⁻⁻` (`beta1`), weights `1`, orientations with signs `ε`. -/
def example935B1 (ε : Bool → Bool) (x : Fin 2 → ℝ) :=
  orientedBranchingStructure_sum_rn (fun b => graph2 (beta1 b)) (fun _ => (1 : ℚ))
    (fun _ => one_pos) (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b))
    (fun b => isClosed_graph2 (contDiff_beta1 b).continuous) (orient1 ε) x

/-- **Example 9.3.5's second oriented local branching structure** at `x`: the graphs
`G⁺⁻, G⁻⁺` (`beta2`), weights `1`, orientations with signs `ε`. -/
def example935B2 (ε : Bool → Bool) (x : Fin 2 → ℝ) :=
  orientedBranchingStructure_sum_rn (fun b => graph2 (beta2 b)) (fun _ => (1 : ℚ))
    (fun _ => one_pos) (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta2 b))
    (fun b => isClosed_graph2 (contDiff_beta2 b).continuous) (orient2 ε) x

theorem example935B1_mem (ε : Bool → Bool) (x : Fin 2 → ℝ) (i : (example935B1 ε x).ι) :
    (example935B1 ε x).M i ∈ graphSheets :=
  ⟨beta1 i.1, contDiff_beta1 _, _, (example935B1 ε x).isOpen_U, rfl⟩

theorem example935B2_mem (ε : Bool → Bool) (x : Fin 2 → ℝ) (i : (example935B2 ε x).ι) :
    (example935B2 ε x).M i ∈ graphSheets :=
  ⟨beta2 i.1, contDiff_beta2 _, _, (example935B2 ε x).isOpen_U, rfl⟩

/-- `G⁺⁺ ∩ G⁻⁻ = {0}`. -/
theorem eq_zero_of_mem_graph2_beta1 {b b' : Bool} (h : b ≠ b') {y : Fin 2 → ℝ}
    (hy : y ∈ graph2 (beta1 b)) (hy' : y ∈ graph2 (beta1 b')) : y = 0 := by
  have key : ∀ {y : Fin 2 → ℝ}, y ∈ graph2 (beta1 true) → y ∈ graph2 (beta1 false) → y = 0 := by
    intro y h1 h2
    change y 1 = betaPP (y 0) at h1
    change y 1 = betaMM (y 0) at h2
    have hp : betaPP (y 0) = 0 := by rw [betaMM] at h2; linarith
    have h0 : y 0 = 0 := by
      by_contra hne
      exact (betaPP_pos hne).ne' hp
    funext i
    fin_cases i
    · simpa using h0
    · simp [h1, hp]
  cases b <;> cases b' <;> simp at h
  · exact key hy' hy
  · exact key hy hy'

/-- **Property (T) holds for Example 9.3.5's first structure on `U(0) = ℝ²`** (two different
sheets meet only at `0`). -/
theorem propertyT_example935B1 (ε : Bool → Bool) :
    (example935B1 ε 0).PropertyT (example935B1 ε 0).U := by
  intro i i' y₀ hy₀ y hy _ _
  by_cases h : i = i'
  · subst h
    simp
  · have hne : i.1 ≠ i'.1 := fun e => h (Subtype.ext e)
    rw [eq_zero_of_mem_graph2_beta1 hne hy₀.1.2.1 hy₀.2.1,
      eq_zero_of_mem_graph2_beta1 hne hy.1.2.1 hy.2.1]

/-- A subset of `{0}` of `ℝ` has no essential points. -/
theorem essentialSet_subset_zero {A : Set ℝ} (hA : A ⊆ {0}) : essentialSet 𝓘(ℝ, ℝ) A = ∅ := by
  refine eq_empty_of_forall_notMem fun s hs => ?_
  obtain ⟨-, u, hu, -⟩ := hs
  have hud := (relTangent_real_eq_top_iff (hu 0).1).1 (hu 0).2
  have hacc := (uniqueDiffWithinAt_iff_accPt.1 hud).mono (principal_mono.2 hA)
  obtain ⟨t, ⟨-, ht⟩, hne⟩ := accPt_iff_nhds.1 hacc univ univ_mem
  rw [mem_singleton_iff.1 ht, mem_singleton_iff.1 (hA (hu 0).1)] at hne
  exact hne rfl

/-- **A point with two classes (Definition 9.4.7, Lemma 9.4.8)**: at the origin, where `G⁺⁺` and
`G⁻⁻` touch with the same tangent line, the two sheets of Example 9.3.5 are not `0`-equivalent,
`♯P₀ = 2`, so `0` lies in the null set of Lemma 9.4.8 and not in `M_U^*`. -/
theorem example935_two_le_numClasses (ε : Bool → Bool) :
    2 ≤ graphSheetGeometry.numClasses (example935B1 ε 0).M 0 ∧
      (0 : Fin 2 → ℝ) ∉ graphSheetGeometry.MStar (example935B1 ε 0).M := by
  set B := example935B1 ε 0
  have hmem : ∀ b, (0 : Fin 2 → ℝ) ∈ B.M ⟨b, zero_mem_graph2_beta1 b⟩ :=
    fun b => ⟨zero_mem_graph2_beta1 b, fun _ h => h⟩
  have hlink : ∀ i j : {i // (0 : Fin 2 → ℝ) ∈ B.M i},
      graphSheetGeometry.IsLink B.M 0 i j → i = j := by
    intro i j hij
    by_contra hne
    have hne' : i.1.1 ≠ j.1.1 := fun e => hne (Subtype.ext (Subtype.ext e))
    have hsub : (fun w : Fin 2 → ℝ => w 0) '' (B.M i ∩ B.M j) ⊆ {0} := by
      rintro _ ⟨w, ⟨hwi, hwj⟩, rfl⟩
      rw [eq_zero_of_mem_graph2_beta1 hne' hwi.1 hwj.1]
      rfl
    have h := hij.2
    rw [essentialSet_subset_zero hsub] at h
    exact h
  have hcls : ∀ i j : {i // (0 : Fin 2 → ℝ) ∈ B.M i},
      Quotient.mk (graphSheetGeometry.ySetoid B.M 0) i =
        Quotient.mk (graphSheetGeometry.ySetoid B.M 0) j → i = j := by
    intro i j h
    have h' := Quotient.exact h
    clear h
    change Relation.EqvGen _ i j at h'
    induction h' with
    | rel a b hab => exact hlink a b hab
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  have hnt : Nontrivial (Quotient (graphSheetGeometry.ySetoid B.M 0)) :=
    ⟨⟨Quotient.mk _ ⟨_, hmem true⟩, Quotient.mk _ ⟨_, hmem false⟩, fun h => by
      have := congrArg (fun i => i.1.1) (hcls _ _ h)
      simp at this⟩⟩
  have h2 : 2 ≤ graphSheetGeometry.numClasses B.M 0 := Finite.one_lt_card_iff_nontrivial.2 hnt
  refine ⟨h2, fun h => ?_⟩
  rw [h.2] at h2
  omega

open scoped Classical in
/-- `G⁺⁺, G⁻⁻` and `G⁺⁻, G⁻⁺` with the signs `+, +`: the two structures give the same oriented
sum at every point (`ε ≡ +` in both; compare `example_9_3_5_cannot_coincide` for `T̂¹`). -/
theorem orientedLift1_const_eq_orientedLift2 :
    orientedLift1 (fun _ => true) = orientedLift2 (fun _ => true) := by
  funext y
  have hterm : ∀ {b b' : Bool}, (y ∈ graph2 (beta1 b) ↔ y ∈ graph2 (beta2 b')) →
      (y ∈ graph2 (beta1 b) → deriv (beta1 b) (y 0) = deriv (beta2 b') (y 0)) →
      (if y ∈ graph2 (beta1 b) then
        Finsupp.single ((orient1 (fun _ => true) b).tangent y) (1 : ℚ) else 0) =
      (if y ∈ graph2 (beta2 b') then
        Finsupp.single ((orient2 (fun _ => true) b').tangent y) (1 : ℚ) else 0) := by
    intro b b' hm hd
    by_cases h : y ∈ graph2 (beta1 b)
    · rw [if_pos h, if_pos (hm.1 h)]
      exact congrArg (fun g => Finsupp.single g (1 : ℚ))
        (graphOrientation_tangent_eq (contDiff_beta1 b) (contDiff_beta2 b')
          (boolSign_ne_zero true) h (hm.1 h) (hd h))
    · rw [if_neg h, if_neg fun h' => h (hm.2 h')]
  rw [orientedLift1, orientedLift2, orientedSumRn_bool, orientedSumRn_bool]
  rcases lt_trichotomy (y 0) 0 with hs | hs | hs
  · have h1 : y ∈ graph2 (beta1 true) ↔ y ∈ graph2 (beta2 true) := by
      change y 1 = betaPP (y 0) ↔ y 1 = betaPM (y 0)
      rw [betaPM_of_nonpos hs.le]
    have h2 : y ∈ graph2 (beta1 false) ↔ y ∈ graph2 (beta2 false) := by
      change y 1 = betaMM (y 0) ↔ y 1 = betaMP (y 0)
      rw [betaMP_of_nonpos hs.le]
    exact congrArg₂ (· + ·)
      (hterm h1 fun _ => deriv_eq_of_eqOn_Iio (fun t ht => (betaPM_of_nonpos ht.le).symm) hs)
      (hterm h2 fun _ => deriv_eq_of_eqOn_Iio (fun t ht => (betaMP_of_nonpos ht.le).symm) hs)
  · have h1 : y ∈ graph2 (beta1 true) ↔ y ∈ graph2 (beta2 true) := by
      change y 1 = betaPP (y 0) ↔ y 1 = betaPM (y 0)
      rw [betaPM_of_nonpos hs.le]
    have h2 : y ∈ graph2 (beta1 false) ↔ y ∈ graph2 (beta2 false) := by
      change y 1 = betaMM (y 0) ↔ y 1 = betaMP (y 0)
      rw [betaMP_of_nonpos hs.le]
    exact congrArg₂ (· + ·)
      (hterm h1 fun _ => by rw [hs, deriv_beta1_zero, deriv_beta2_zero])
      (hterm h2 fun _ => by rw [hs, deriv_beta1_zero, deriv_beta2_zero])
  · have h1 : y ∈ graph2 (beta1 true) ↔ y ∈ graph2 (beta2 false) := by
      change y 1 = betaPP (y 0) ↔ y 1 = betaMP (y 0)
      rw [betaMP_of_pos hs]
    have h2 : y ∈ graph2 (beta1 false) ↔ y ∈ graph2 (beta2 true) := by
      change y 1 = betaMM (y 0) ↔ y 1 = betaPM (y 0)
      rw [betaPM_of_pos hs]
    rw [add_comm (if y ∈ graph2 (beta2 true) then _ else _)]
    exact congrArg₂ (· + ·)
      (hterm h1 fun _ => deriv_eq_of_eqOn_Ioi (fun t ht => (betaMP_of_pos ht).symm) hs)
      (hterm h2 fun _ => deriv_eq_of_eqOn_Ioi (fun t ht => (betaPM_of_pos ht).symm) hs)

theorem example935B1_U (ε : Bool → Bool) : (example935B1 ε 0).U = univ :=
  eq_univ_of_forall fun _ b _ => zero_mem_graph2_beta1 b

theorem example935B2_U (ε : Bool → Bool) : (example935B2 ε 0).U = univ :=
  eq_univ_of_forall fun _ b _ => zero_mem_graph2_beta2 b

open scoped Classical in
/-- **Satisfiability of the hypotheses of Proposition 9.4.10 with two different structures**:
Example 9.3.5's structures `G⁺⁺, G⁻⁻` and `G⁺⁻, G⁻⁺` (all signs `+`) on `U(0) = ℝ²` satisfy (a) and
(b); consequently (Proposition 9.4.10) `M_U = M_U'`. -/
theorem example935_hypotheses_9_4_10 :
    (example935B1 (fun _ => true) 0).U = (example935B2 (fun _ => true) 0).U ∧
    (∀ y ∈ (example935B1 (fun _ => true) 0).U,
      ∑ i with y ∈ (example935B1 (fun _ => true) 0).M i, (example935B1 (fun _ => true) 0).σ i =
        ∑ i with y ∈ (example935B2 (fun _ => true) 0).M i,
          (example935B2 (fun _ => true) 0).σ i) ∧
    (∀ y ∈ (example935B1 (fun _ => true) 0).U,
      (example935B1 (fun _ => true) 0).orientedSum y =
        (example935B2 (fun _ => true) 0).orientedSum y) := by
  have hU := (example935B1_U (fun _ => true)).trans (example935B2_U (fun _ => true)).symm
  refine ⟨hU, fun y hy => ?_, fun y hy => ?_⟩
  · rw [← (example935B1 (fun _ => true) 0).eq_sum y hy,
      ← (example935B2 (fun _ => true) 0).eq_sum y (hU ▸ hy)]
    exact example_9_3_5_count y
  · rw [example935B1, example935B2, orientedSum_sum_rn_eq _ _ _ _ _ _ hy,
      orientedSum_sum_rn_eq _ _ _ _ _ _ (hU ▸ hy)]
    exact congrFun orientedLift1_const_eq_orientedLift2 y

theorem example935_MU_eq :
    (example935B1 (fun _ => true) 0).MU = (example935B2 (fun _ => true) 0).MU :=
  (proposition_9_4_10 graphSheetGeometry _ _ (example935B1_mem _ 0) (example935B2_mem _ 0)
    example935_hypotheses_9_4_10.1 example935_hypotheses_9_4_10.2.1
    example935_hypotheses_9_4_10.2.2).1

end Example935

end GraphSheets

end Polyfold
