import Polyfold
/-! Blind formalization of V9_48 (the 2021 book's Part II, §9.4, Proposition 9.4.10, p. 435;
2017: Proposition 9.6, p. 321): comparing two oriented structures.

Text: for two oriented local branching structures on `U(x)` with Property (T) and (a) equal weight
sums, (b) equal oriented sums at every `y`: `M_U = M'_U`, and there are `M^†_U` and a finite
partition `A₁ ⊔ ⋯ ⊔ A_ℓ` with (1) `M_U ∖ M^†_U` null, (2) `I_y`, `I'_y` constant and all tangent
spaces equal on each `A_p`, (3) equal weight sums, (4) partitions `J_±`, `J'_±` with equal oriented
tangent spaces, (5) equal oriented weighted sums.

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
- Oriented setting (`OrLocalStrB`) as in my V9_47: orientations of the sheets, oriented
  subspaces of `F` as sets of positive frames (`posFramesB`), `T̂Θ(y) = ∑_{I_y} σᵢ T_y(Mᵢ, oᵢ)`.
  The two structures `(Mᵢ, oᵢ, σᵢ)_{i ∈ I}`, `(M'ᵢ', o'ᵢ', σ'ᵢ')_{i' ∈ I'}` are at the same `x`
  with the same `U(x)`; both have Property (T) on `U(x)` (`OrLocalStrB.PropT`, literally with
  `ε = ±1`).
- (a): `∑_{I_y} σᵢ = ∑_{I'_y} σ'ᵢ'` and (b): `T̂Θ(y) = T̂Θ'(y)`, for every `y ∈ U(x)`.
- Conclusion: `M^†_U ⊆ M_U` and `A : Fin ℓ → Set F` pairwise disjoint with union `M^†_U` (no
  measurability of the `A_p` is asserted: the quoted statement has none).  (1) `M_U ∖ M^†_U` has
  measure zero in every `Mᵢ` and in every `M'ᵢ'`.  (2) on `A_p`: `I_y = I_p`, `I'_y = I'_p` and, at
  each `y`, all `T_yMᵢ` (`i ∈ I_p`) and `T_yM'ᵢ'` (`i' ∈ I'_p`) are one subspace.
  (3) `∑_{I_p} σᵢ = ∑_{I'_p} σ'ᵢ'`.  (4) `I_p = J₊ ⊔ J₋`, `I'_p = J'₊ ⊔ J'₋` (constant on `A_p`)
  and, at each `y ∈ A_p`, an orientation `P` of the common tangent space with
  `T_y(Mᵢ, oᵢ) = P` for `i ∈ J₊`, `= -P` for `i ∈ J₋`, and the same for `J'₊`, `J'₋` (the signs `±`
  read as "`P` and its opposite").  (5) `∑_{J₊} σ = ∑_{J'₊} σ'`, `∑_{J₋} σ = ∑_{J'₋} σ'`.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_48
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

/-- The positively oriented frames of the oriented subspace `(D(ℝⁿ), D_* ori)` of `F`, for an
injective `D : ℝⁿ → F` and an orientation `ori` of `ℝⁿ`: the frames `D ∘ b`, `b` a basis of `ℝⁿ`
in the class `ori`.  I represent an oriented `n`-dimensional subspace of `F` by this set; it
determines the subspace (for `n ≥ 1`, as the span of any of its frames) and the orientation, also
for `n = 0` (`{()}` for `+`, `∅` for `-`). -/
def posFramesB (D : EuclideanSpace ℝ (Fin n) →L[ℝ] F)
    (ori : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) : Set (Fin n → F) :=
  {f | ∃ b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), b.orientation = ori ∧
    f = ⇑D ∘ ⇑b}

/-- **An oriented local branching structure at `x`** `(Mᵢ, oᵢ)`, `(σᵢ)`: orientations `oᵢ` of the
sheets, given as an orientation `oᵢ(w)` of `T_wNᵢ = ℝⁿ` at every point `w`, continuous in the usual
sense: for `n ≥ 1`, near every point there is a continuous frame field `e` (frames in `F`) with
`e(w)` positive for `oᵢ(w)`. -/
structure OrLocalStrB (n : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (x : F)
    extends LocalStrB n F x where
  o : ∀ i, (S i).N → Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)
  continuous_o : 0 < n → ∀ (i : ι) (w₀ : (S i).N), ∃ V : Set (S i).N, IsOpen V ∧ w₀ ∈ V ∧
    ∃ e : (S i).N → Fin n → F, ContinuousOn e V ∧ ∀ w ∈ V, e w ∈ posFramesB ((S i).D w) (o i w)

namespace OrLocalStrB
variable {x : F} (L : OrLocalStrB n F x)

/-- The oriented tangent space `T_y(Mᵢ, ε · oᵢ)` (`ε = +1` for `true`, `-1` for `false`), as its
set of positive frames in `F` (empty if `y ∉ Mᵢ`). -/
def OT (ε : Bool) (i : L.ι) (y : F) : Set (Fin n → F) :=
  {f | ∃ w, (L.S i).j w = y ∧ f ∈ posFramesB ((L.S i).D w) (if ε then L.o i w else -L.o i w)}

/-- `T̂Θ(y) = ∑_{i ∈ I_y} σᵢ · T_y(Mᵢ, oᵢ)`, a formal sum of oriented subspaces of `F`. -/
def That (y : F) : Set (Fin n → F) →₀ ℚ :=
  ∑ i ∈ L.Iy y, Finsupp.single (L.OT true i y) (L.σ i)

/-- **Property (T)** (2021 p. 430) on `V`: if `y₀ ∈ V ∩ Mᵢ ∩ Mᵢ'`, `T_{y₀}Mᵢ = T_{y₀}Mᵢ'` and
`o_{i,y₀} = ε · o_{i',y₀}` (`ε = ±1`), then `T_y(Mᵢ, oᵢ) = T_y(Mᵢ', ε · oᵢ')` for every
`y ∈ V ∩ Mᵢ ∩ Mᵢ'` with `T_yMᵢ = T_yMᵢ'`. -/
def PropT (V : Set F) : Prop :=
  ∀ (i i' : L.ι) (ε : Bool), ∀ y₀ ∈ V ∩ L.K i i', ∀ y ∈ V ∩ L.K i i',
    (L.S i).T y₀ = (L.S i').T y₀ → L.OT true i y₀ = L.OT ε i' y₀ →
    (L.S i).T y = (L.S i').T y → L.OT true i y = L.OT ε i' y

end OrLocalStrB

/-- Proposition 9.4.10: two oriented local branching structures with the same `Θ` and the same
`T̂Θ` agree, up to a null set, piece by piece. -/
def B : Prop :=
  ∀ (n : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (x : F)
    (L L' : OrLocalStrB n F x), L.U = L'.U → L.PropT L.U → L'.PropT L'.U →
    (∀ y ∈ L.U, L.Θ y = L'.Θ y) → (∀ y ∈ L.U, L.That y = L'.That y) →
    L.MU = L'.MU ∧
    ∃ Mdag : Set F, Mdag ⊆ L.MU ∧ ∃ (ℓ : ℕ) (A : Fin ℓ → Set F),
      (∀ p q, p ≠ q → Disjoint (A p) (A q)) ∧ (⋃ p, A p) = Mdag ∧
      -- (1)
      L.IsNullB (L.MU \ Mdag) ∧ L'.IsNullB (L.MU \ Mdag) ∧
      ∀ p, ∃ (I : Finset L.ι) (I' : Finset L'.ι),
        -- (2)
        (∀ y ∈ A p, L.Iy y = I ∧ L'.Iy y = I') ∧
        (∀ y ∈ A p, ∃ T : Submodule ℝ F,
          (∀ i ∈ I, (L.S i).T y = T) ∧ ∀ i' ∈ I', (L'.S i').T y = T) ∧
        -- (3)
        ∑ i ∈ I, L.σ i = ∑ i' ∈ I', L'.σ i' ∧
        ∃ (Jp Jm : Finset L.ι) (Jp' Jm' : Finset L'.ι),
          Disjoint Jp Jm ∧ Jp ∪ Jm = I ∧ Disjoint Jp' Jm' ∧ Jp' ∪ Jm' = I' ∧
          -- (4)
          (∀ y ∈ A p, ∃ P Q : Set (Fin n → F),
            (∃ i ∈ I, ∃ w : (L.S i).N, (L.S i).j w = y ∧
              ∃ ori : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n),
                P = posFramesB ((L.S i).D w) ori ∧ Q = posFramesB ((L.S i).D w) (-ori)) ∧
            (∀ i ∈ Jp, L.OT true i y = P) ∧ (∀ i ∈ Jm, L.OT true i y = Q) ∧
            (∀ i' ∈ Jp', L'.OT true i' y = P) ∧ (∀ i' ∈ Jm', L'.OT true i' y = Q)) ∧
          -- (5)
          ∑ i ∈ Jp, L.σ i = ∑ i' ∈ Jp', L'.σ i' ∧ ∑ i ∈ Jm, L.σ i = ∑ i' ∈ Jm', L'.σ i'

end
end RoundTrip.V9_48
