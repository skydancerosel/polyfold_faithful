import Polyfold
/-! Blind formalization of V9_45 (the 2021 book's Part II, §9.4, Definition 9.4.7, p. 432;
2017: Definition 9.14, p. 318): `y`-equivalence.

Text: `i ∼_y i'` if there is a chain `i = i₀, …, i_k = i'` in `I_y` with
`y ∈ K(i_{p-1}, i_p)^e`; then `T_yMᵢ = T_yMᵢ'`; `P_y = I_y/∼_y`.

Choices:
- Setting (the local model, the same in my V9_42, V9_44–V9_48).  The text's sheets `Mᵢ` are
  smooth finite-dimensional submanifolds of the object M-polyfold, all of one dimension `n` (the
  standing assumption of §9.4: `Θ` is `n`-dimensional; it is needed, e.g. Lemma 9.4.4 fails for a
  line inside a plane), with boundary and corners (`Θ` tame), and Definitions 9.4.1 and 9.4.5 use
  their structure as smooth manifolds with corners.  The project's vocabulary has no smooth charts
  on such sheets; its `SheetGeometry` / `SheetNullSets` take the essential points and the null sets
  of sheets as abstract data, with Lemmas 9.4.4 and 9.4.6 among the fields, so they do not express
  the text's notions and I did not use them.  I state the claim in the classical local model of a
  chart instead: the ambient is a real Banach space `F : Type` (the level-`0` space of a chart);
  a sheet (`SheetB`) is a Mathlib `n`-manifold with boundary and corners `N`
  (`ChartedSpace (EuclideanQuadrant n) N`, `IsManifold (modelWithCornersEuclideanQuadrant n) ∞ N`)
  with a `C^∞` immersion `j : N → F` (injective `mfderiv`) that is a homeomorphism onto its image
  `M = j(N)`; `T_yM = Dj(T_wN) ⊆ F` for `j(w) = y`.  Essential points and null sets of subsets
  `A ⊆ M` are those of `j⁻¹(A)` in `N`, with the project's `essentialSet` and `IsMeasureZero`
  (read with `#print`; they are Definitions 9.4.1 (2) and 9.4.5 literally, see my V9_39, V9_43).
  A local branching structure at `x` (`LocalStrB`): an open `U ∋ x`, a finite family of sheets
  `Mᵢ ⊆ U` through `x`, closed in `U`, weights `σᵢ > 0`; `Θ(y) = ∑_{y ∈ Mᵢ} σᵢ`.  The text's
  setting (the M-polyfold, the ep-groupoid, the natural `G_x`-action on `U(x)`) does not enter
  these local statements.
- "Measure zero" of a subset `A ⊆ M_U = ⋃ Mᵢ`: `A ∩ Mᵢ` has measure zero in `Mᵢ` for every `i`
  (as in Definition 9.5.1).  `K(i, i')^e` is computed with the reference sheet `Mᵢ` (first index);
  `K^{ne} = K ∖ K^e`.
- This item is a definition with two embedded claims.  `∼_y` is `LocalStrB.YEquivB` (the
  reflexive-transitive closure of the links `y ∈ K(i, i')^e` on `I_y`, chains of length `k ≥ 0`;
  each link computed with the reference sheet of its first index).  "`P_y = I_y/∼_y`" presupposes
  that `∼_y` is an equivalence relation on `I_y` (symmetry is where Lemma 9.4.4 enters): claim (1).
  "then `T_yMᵢ = T_yMᵢ'`": claim (2), tangent spaces as subspaces of `F`.
- The project's `SheetGeometry.YEquiv` is defined over its abstract `SheetGeometry`, so I do not
  characterize it.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_45
open Polyfold
open scoped Manifold ContDiff
noncomputable section

/-- The model with corners `[0, ∞)ⁿ ⊆ ℝⁿ` (`n`-dimensional manifolds with boundary and corners). -/
abbrev Q (n : ℕ) := modelWithCornersEuclideanQuadrant n

/-- **An `n`-dimensional sheet in `F`** (the local model of a sheet `Mᵢ`): an `n`-dimensional
smooth manifold with boundary and corners `N` with a smooth immersion `j : N → F` which is a
homeomorphism onto its image `M = j(N)`. -/
structure SheetB (n : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  N : Type
  [topN : TopologicalSpace N]
  [chartedN : ChartedSpace (EuclideanQuadrant n) N]
  [mfdN : IsManifold (Q n) ∞ N]
  j : N → F
  smooth : ContMDiff (Q n) 𝓘(ℝ, F) ∞ j
  immersion : ∀ w, Function.Injective (mfderiv (Q n) 𝓘(ℝ, F) j w)
  embedding : Topology.IsEmbedding j

attribute [instance] SheetB.topN SheetB.chartedN SheetB.mfdN

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SheetB
variable (S : SheetB n F)

/-- The sheet `M = j(N) ⊆ F`. -/
def M : Set F := Set.range S.j

/-- The derivative `T_wN = ℝⁿ → F` of `j` at `w`. -/
def D (w : S.N) : EuclideanSpace ℝ (Fin n) →L[ℝ] F := mfderiv (Q n) 𝓘(ℝ, F) S.j w

/-- `T_yM ⊆ F`: the image of `T_wN` for the point `w` with `j(w) = y` (`⊥` if `y ∉ M`). -/
def T (y : F) : Submodule ℝ F :=
  ⨆ (w : S.N) (_ : S.j w = y), LinearMap.range (S.D w).toLinearMap

/-- The essential points `K^e` of `K ⊆ M`, `M ≅ N` the reference sheet (Definition 9.4.1 (2) in
`N`: the project's `essentialSet`), as a subset of `F`. -/
def ess (K : Set F) : Set F := S.j '' essentialSet (Q n) (S.j ⁻¹' K)

/-- `A ∩ M` has measure zero in `M ≅ N` (Definition 9.4.5 in `N`: the project's
`IsMeasureZero`). -/
def IsNull (A : Set F) : Prop := IsMeasureZero (Q n) (S.j ⁻¹' A)

end SheetB

/-- **A local branching structure at `x`** in the local model: an open `U ∋ x` and finitely many
`n`-dimensional sheets `Mᵢ ⊆ U` through `x`, closed in `U` (the inclusions `Mᵢ → U` are proper),
with weights `σᵢ > 0`; `Θ(y) = ∑_{y ∈ Mᵢ} σᵢ` (`LocalStrB.Θ`). -/
structure LocalStrB (n : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (x : F) where
  U : Set F
  isOpen_U : IsOpen U
  mem_U : x ∈ U
  ι : Type
  [fin : Fintype ι]
  [dec : DecidableEq ι]
  S : ι → SheetB n F
  subset_U : ∀ i, (S i).M ⊆ U
  mem_M : ∀ i, x ∈ (S i).M
  isClosed_M : ∀ i, IsClosed (((↑) : U → F) ⁻¹' (S i).M)
  σ : ι → ℚ
  σ_pos : ∀ i, 0 < σ i

attribute [instance] LocalStrB.fin LocalStrB.dec

namespace LocalStrB
variable {x : F} (L : LocalStrB n F x)

/-- `M_U = ⋃ᵢ Mᵢ`. -/
def MU : Set F := ⋃ i, (L.S i).M

open Classical in
/-- `I_y = {i ∈ I | y ∈ Mᵢ}`. -/
def Iy (y : F) : Finset L.ι := Finset.univ.filter (fun i => y ∈ (L.S i).M)

/-- `K(i, i') = Mᵢ ∩ Mᵢ'`. -/
def K (i i' : L.ι) : Set F := (L.S i).M ∩ (L.S i').M

/-- `A ⊆ M_U` has measure zero: `A ∩ Mᵢ` has measure zero in `Mᵢ` for every `i`. -/
def IsNullB (A : Set F) : Prop := ∀ i, (L.S i).IsNull A

/-- `Θ(y) = ∑_{i ∈ I_y} σᵢ`. -/
def Θ (y : F) : ℚ := ∑ i ∈ L.Iy y, L.σ i

/-- `TΘ(y) = ∑_{i ∈ I_y} σᵢ · T_yMᵢ`, a formal sum of subspaces of `F`. -/
def TΘ (y : F) : Submodule ℝ F →₀ ℚ := ∑ i ∈ L.Iy y, Finsupp.single ((L.S i).T y) (L.σ i)

/-- One link of a chain in `I_y`: `y ∈ K(i, i')^e` (essential points w.r.t. the sheet `Mᵢ`). -/
def link (y : F) (a b : {i : L.ι // y ∈ (L.S i).M}) : Prop := y ∈ (L.S a).ess (L.K a b)

/-- **Definition 9.4.7**: `i ∼_y i'` if there is a chain `i = i₀, i₁, …, i_k = i'` (`k ≥ 0`) in
`I_y` with `y ∈ K(i_{p-1}, i_p)^e` for `p = 1, …, k`. -/
def YEquivB (y : F) : {i : L.ι // y ∈ (L.S i).M} → {i : L.ι // y ∈ (L.S i).M} → Prop :=
  Relation.ReflTransGen (L.link y)

/-- `♯P_y = ♯(I_y / ∼_y)`, the number of classes (of the equivalence relation generated by the
chains; it is `∼_y` itself, an equivalence relation by my V9_45). -/
def numClasses (y : F) : ℕ := Nat.card (Quot (L.YEquivB y))

end LocalStrB

/-- Definition 9.4.7: `∼_y` is an equivalence relation on `I_y`, and `i ∼_y i'` implies
`T_yMᵢ = T_yMᵢ'`. -/
def B : Prop :=
  ∀ (n : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (x : F)
    (L : LocalStrB n F x) (y : F),
    Equivalence (L.YEquivB y) ∧
      ∀ a b : {i : L.ι // y ∈ (L.S i).M}, L.YEquivB y a b → (L.S a).T y = (L.S b).T y

end
end RoundTrip.V9_45
