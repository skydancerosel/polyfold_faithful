import Polyfold.Chapter4.Submanifolds
import Polyfold.Chapter2.CornerGerms
import Polyfold.Chapter2.PartialCone

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §4.2–4.3,
Theorem 4.2.11 (preprint 4.22) and Remark 4.3.2 (preprint 4.24) *(book 2017: Theorem 4.3 and Remark 4.5; see `BookConcordance.md`)*.

# The local structure of smooth submanifolds in general position

## The text, paraphrased

(Theorem 4.2.11 (preprint 4.22)) Let `A` be a smooth finite-dimensional submanifold of the tame M-polyfold `X`, in
general position at `x ∈ A` (Definition 4.2.10 (preprint 4.21): `T_xA` has in `T_xX` an sc-complement contained in
`T_x^R X`).  There is an open `U ∋ x` such that (1) there are precisely `d = d_X(x)` local faces
`F_1, …, F_d` in `U`; (2) `d_X(a) = d_A(a)` for `a ∈ A ∩ U`; (3) `A` is in general position at every
`a ∈ A ∩ U`; (4) for `σ ⊆ {1, …, d}`, `F_σ = ⋂_{i ∈ σ} F_i` is a tame M-polyfold, `A ∩ F_σ` is a
tame smooth submanifold of `F_σ`, in general position in `F_σ` at every point of `A ∩ U ∩ F_σ`.
*Proof*: in a tame chart `(O, C, E)` with `x = 0`, `C = [0, ∞)ⁿ ⊕ W`, `n = d_O(0)`; `T₀^R O =
T₀O ∩ ({0} ⊕ W)` (Definition 2.27); `E = T₀O ⊕ Z = T₀A ⊕ Ã ⊕ Z` with `Ã ⊆ T₀^R O` and `Z ⊆ W`
(tameness), so `E = T₀A ⊕ Y` with `Y ⊆ W`; `T₀A` is in good position to `C` with good complement
`Y`, `T₀A ∩ C` is a partial quadrant (Proposition 3.1.25 (preprint 3.22)), and by Proposition 4.1.9 (preprint 4.9) `A` is near `0` the
graph `{v + δ(v)}` of `δ : V → Y`, `V ⊆ T₀A ∩ C`.  (2): `p : A → V` is an sc-diffeomorphism, so
`d_A(a) = d_{T₀A ∩ C}(p(a))` (Proposition 2.4.4 (preprint 2.24)), `= d_C(a)` (since `δ` takes values in `W`),
`= d_O(a)` (Proposition 2.5.6 (preprint 2.36)).  (3): `T_aA = {h + Dδ(v)h}` and `T₀A + W = E` give `T_aA + W = E`,
hence `T_aO = T_aA + (W ∩ T_aO) = T_aA + T_a^R O`.  (4): "in view of the arguments in the proof of
Proposition 2.43 the `F_σ` are tame M-polyfolds; `A ∩ F_σ` are smooth submanifolds of `F_σ`; the
previous arguments, applied to `A ∩ F_σ`, conclude the proof."  (Remark 4.3.2 (preprint 4.24)) By Proposition 2.5.6 (preprint 2.36),
`codim T_x^R X = d_X(x)`; so in Theorem 4.3.1 (preprint 4.23) a point `x ∈ A_λ` can lie in a corner only if
`d_X(x) ≤ dim A_λ`.

## What is formalized

* **Linear algebra at the corner `0`** of a presented partial quadrant
  `C = T⁻¹([0, ∞)ⁿ ⊕ W)` with `0 ∈ C`: every coordinate vanishes at `0`, so the minimal subspace
  `E_0` (the text's `{0} ⊕ W`) is `{λ = 0}` and lies in every `E_x`
  (`mem_minimalSubspaceWith_zero`, `minimalSubspaceWith_zero_le`); adding a vector of `E_0` changes
  neither membership in `C` nor `d_C` (`add_mem_iff_of_mem_zero`, `degIndexWith_add_of_mem_zero`).
  For finite-dimensional `N` with `N + E_0 = E`: `λ|_N` is onto `ℝⁿ` (`coordsOn_surjective`), `N`
  is in good position to `C` with a **closed good complement `Y ⊆ E_0`**
  (`exists_goodComplement_le_zero`, from `exists_isClosed_isCompl_le`), the projection along `Y`
  is continuous (`exists_proj_of_isCompl`), and **`d_{N ∩ C}(v) = d_C(v)`** on the slice, through
  the explicit presentation `v ↦ (λ(v), v − s(λ(v)))` of `N ∩ C` (`degIndex_slice`).
* **An sc-complement inside an sc-subspace** (`exists_scComplement_le`): for `N ⊆ E_∞`
  finite-dimensional and an sc-subspace `TR`, `N` has in `N + TR` an sc-complement contained in
  `TR` (via Proposition 1.1.7 (preprint 1.6) and the sc-projection of Lemma 2.B).
* **General position in a chart from `T_yQ + E_0 = E`** (`isGeneralPositionRetractAt_of_sup_eq_top`,
  the modular law and Proposition 2.5.6 (preprint 2.36): `T_y^R O` is an sc-subspace).
* **Theorem 4.2.11 (preprint 4.22) in a tame chart centred at the point** (`theorem_4_2_11_chart`): from general
  position at `0`, `T₀A + E_0 = E` (`sup_minimalSubspaceWith_eq_top`, with Proposition 2.5.3 (preprint 2.35));
  Proposition 4.1.9 (preprint 4.9) with the good complement `Y ⊆ E_0`; `d_{T₀A ∩ C}(v) = d_C(Γ(v))`; general position
  at every point of the graph (`sup_minimalSubspaceWith_eq_top_graph`: `T_yA = DΓ(v)T₀A` with
  `DΓ(v)h − h ∈ ker p = Y`).
* **Theorem 4.2.11 (preprint 4.22) (4) in the chart**: `κ_σ` killing the coordinates in `σ` on `T₀A` (`killOn`,
  through a linear section of `λ|_{T₀A}`), continuous linear maps into finite-dimensional spaces as
  sc-operators (`opToConst`); the **sc⁺-retraction `t_σ = Γ ∘ κ_σ ∘ p ∘ t` onto `A ∩ F_σ`**
  (`exists_scPlus_retraction_corner`, with `T_yA ∩ f_σ ⊆ T_y(A ∩ F_σ)` by the chain rule), its
  corner model (`exists_cornerModel_retraction`: `π_σ ∘ S ∘ ι_σ`, sc⁺ if `S` is), and
  `theorem_4_2_11_four_chart`: `F_σ` near `0` with its tame corner model (Proposition 2.5.16 (preprint 2.44),
  `corner_retraction`, `corner_tameModel`), `A ∩ F_σ` an sc⁺-retract inside it, in general position
  in the corner model.
* **General position implies good position** (`IsGeneralPositionRetractAt.isGoodPositionRetractAt`).
* **sc⁺-retractions in a chart are sc⁺-retractions on open subsets** of the M-polyfold
  (`MPolyfold.isScPlusRetractionOn_of_chart`).
* **Theorem 4.2.11 (preprint 4.22) (1)–(4)** on the M-polyfold: `MPolyfold.theorem_4_2_11_preprint`, with (4) for one `σ` in
  `MPolyfold.theorem_4_2_11_four_of_chart` (`F_σ = ψ⁻¹(G ∩ ⋂_{i ∈ σ} F_i)`,
  `MChart.cornerPreimage`).
* **Remark 4.3.2 (preprint 4.24)**: `MPolyfold.remark_4_3_2_codim` (`codim T_x^R X = d_X(x)` in a tame chart),
  `MPolyfold.remark_4_3_2` (general position at `a` gives `d_X(a) ≤ dim T_aA`),
  `MPolyfold.remark_4_3_2_not_mem_boundary`; in a chart `remark_4_3_2_chart`
  (with `quotDim_le_finrank_of_eq_sup`).

## What the text leaves implicit, and the choices made

* The chart `(O, C, E)` with `x = 0` and `C = [0, ∞)ⁿ ⊕ W`, `n = d_O(0)`, is the tame chart
  re-centred at the smooth point `x` (`IsTame.exists_centredChart`, Findings Chapter 4, item 1); in
  it every half-line coordinate vanishes at `0`, so `n = d_X(x)` for any presentation of `C`.
* The good complement `Y ⊆ W` of `T₀A` is chosen closed (Proposition 4.1.9 (preprint 4.9) needs it, Findings
  Chapter 4, item 21): any closed complement of `T₀A` inside the closed `E_0 = {0} ⊕ W`; it is good
  with every `ε`, since adding a vector of `E_0` changes no coordinate.  The text's further
  splitting `T₀A = N ⊕ (T₀A ∩ W)`, `E = N ⊕ W`, is replaced by the presentation of `T₀A ∩ C`
  through the coordinates `λ|_{T₀A}`, which are onto `ℝⁿ`.
* (2) uses the corner chart `p ∘ ψ` of `A` (Theorem 4.1.2 (preprint 4.2)'s `CornerChartData`, for the induced chart
  of `A` and the complement `Y ⊆ E_0`), which is tame and hence realizes `d_A`
  (`degIndex_eq_chartDegIndex_of_isTameRetract`); the text's "by Proposition 2.24" is this.  The
  identity `d_{T₀A ∩ C}(p(a)) = d_C(a)` holds because `a − p(a) ∈ Y ⊆ E_0` has vanishing
  coordinates; and `d_C(ψ(a)) = d_X(a)` because the chart is tame (the text: Proposition 2.5.6 (preprint 2.36)).
* (3): "`T_aA + W = E` by the particular form of `α`" needs `Dδ(v)h ∈ W`, which follows from
  `p ∘ DΓ(v) = 1` (`tangentSpace_eq_range_graph`) and `ker p = Y ⊆ W`; "`T_aA` has in `T_aO` an
  sc-complement contained in `T_a^R O`" needs `T_a^R O` to be an sc-subspace (Proposition 2.5.6 (preprint 2.36), for
  tame retracts) and the construction of `exists_scComplement_le`.
* (1) is read as: `d_X(x)` equals the number of half-line coordinates of the centred tame chart,
  all vanishing at `0` (the local faces are `F_i = O ∩ {λ_i = 0}`), and `x` lies in exactly
  `d_X(x)` faces of the chart model (Corollary 2.5.13 (preprint 2.41)).  It does not involve `A`.
* (4) has no proof in the text ("the previous arguments, but now applied to `A ∩ F_σ`").  `F_σ` is
  the germ `ψ⁻¹(G ∩ ⋂_{i ∈ σ} F_i)`, `F_i` the faces of the chart model through `0`, with `G` chosen
  inside the submanifold chart so that `F_σ ⊆ U` and `A ∩ F_σ` is exactly the retract of `t_σ`; it
  is a tame sub-M-polyfold by Proposition 2.5.16 (preprint 2.44) (second sentence, `CornerGerms.lean`) in the centred
  chart.  `A ∩ F_σ` is a smooth submanifold of `F_σ` through the sc⁺-retraction `t_σ`, read in the
  face chart `π_σ ∘ ψ` of `F_σ`; general position in `F_σ` comes from `T_yA + E_0 = E` restricted to
  `f_σ`; tameness of `A ∩ F_σ` is Theorem 4.2.7 (preprint 4.18) in `F_σ`, good position following from general
  position.
* No hypothesis is added; `[ParacompactSpace A]` is the instance argument of the induced structure
  (`subPolyfold`), as in `Submanifolds.lean`; the paracompactness of `F_σ` and of `A ∩ F_σ` is
  supplied by `MPolyfold.paracompactSpace_subtype`.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### Linear algebra: complements inside a closed subspace -/

section Complement

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **A closed complement inside a closed subspace**: if `N` is finite-dimensional, `K` closed and
`N + K = V`, then `N` has a closed complement `Y ⊆ K` (`Y = K ∩ ker q` for a continuous projection
`q` onto `N ∩ K`). -/
theorem exists_isClosed_isCompl_le {N K : Submodule ℝ V} [FiniteDimensional ℝ N]
    (hK : IsClosed (K : Set V)) (h : N ⊔ K = ⊤) :
    ∃ Y : Submodule ℝ V, Y ≤ K ∧ IsClosed (Y : Set V) ∧ IsCompl N Y := by
  set L : Submodule ℝ V := N ⊓ K with hL
  have : FiniteDimensional ℝ L := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨q, hq⟩ := Submodule.ClosedComplemented.of_finiteDimensional L
  have hqL : ∀ l ∈ L, (q l : V) = l := fun l hl => congrArg Subtype.val (hq ⟨l, hl⟩)
  refine ⟨K ⊓ LinearMap.ker (q : V →ₗ[ℝ] L), inf_le_left, hK.inter q.isClosed_ker, ?_⟩
  refine IsCompl.of_eq ?_ ?_
  · rw [eq_bot_iff]
    rintro x ⟨hxN, hxK, hxq⟩
    have hxq' : q x = 0 := hxq
    have := hqL x ⟨hxN, hxK⟩
    rw [hxq'] at this
    rw [Submodule.mem_bot, ← this]
    rfl
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ N ⊔ K := by rw [h]; exact Submodule.mem_top
    obtain ⟨a, ha, k, hk, rfl⟩ := Submodule.mem_sup.1 hx
    set l : V := (q k : V) with hl
    have hlL : l ∈ L := (q k).2
    refine Submodule.mem_sup.2 ⟨a + l, N.add_mem ha hlL.1, k - l, ⟨K.sub_mem hk hlL.2, ?_⟩, by abel⟩
    change q (k - l) = 0
    rw [map_sub]
    apply Subtype.ext
    rw [Submodule.coe_sub, hqL l hlL, sub_self]
    rfl

/-- **The continuous projection along a closed complement** of a finite-dimensional subspace. -/
theorem exists_proj_of_isCompl {N Y : Submodule ℝ V} [FiniteDimensional ℝ N]
    (hY : IsClosed (Y : Set V)) (h : IsCompl N Y) :
    ∃ p : V →L[ℝ] N, (∀ x : N, p x = x) ∧ (∀ y ∈ Y, p y = 0) ∧ ∀ x, p x = 0 → x ∈ Y := by
  have htop : Submodule.IsTopCompl N Y :=
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional h.symm hY).symm
  exact ⟨N.projectionOntoL Y htop, fun x => Submodule.projectionOntoL_apply_left htop x,
    fun y hy => (Submodule.projectionOntoL_apply_eq_zero_iff htop).2 hy,
    fun x hx => (Submodule.projectionOntoL_apply_eq_zero_iff htop).1 hx⟩

end Complement

/-! ### Coordinates of a partial quadrant at a centre -/

section Coordinates

variable {E : ScBanach} {n : ℕ} {Wq : ScBanach}
  (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq))

/-- At `0` every coordinate vanishes, so `E_0 = {v | (Tv)_i = 0 for all i}` (the minimal subspace
at the corner `0`; in the text's coordinates `C = [0, ∞)ⁿ ⊕ W`, `E_0 = {0} ⊕ W`). -/
lemma mem_minimalSubspaceWith_zero {v : E 0} :
    v ∈ minimalSubspaceWith T 0 ↔ ∀ i, (T 0 v).1 i = 0 := by
  rw [mem_minimalSubspaceWith]
  constructor
  · intro h i
    exact h i (by rw [map_zero]; rfl)
  · intro h i _
    exact h i

/-- `E_0 ⊆ E_x` for every `x`. -/
lemma minimalSubspaceWith_zero_le (x : E 0) :
    minimalSubspaceWith T 0 ≤ minimalSubspaceWith T x := fun v hv => by
  rw [mem_minimalSubspaceWith]
  intro i _
  exact (mem_minimalSubspaceWith_zero T).1 hv i

/-- Adding a vector of `E_0` changes no coordinate. -/
lemma coord_add_of_mem_zero {x k : E 0} (hk : k ∈ minimalSubspaceWith T 0) (i : Fin n) :
    (T 0 (x + k)).1 i = (T 0 x).1 i := by
  rw [map_add, Prod.fst_add, Pi.add_apply, (mem_minimalSubspaceWith_zero T).1 hk i, add_zero]

/-- Adding a vector of `E_0` does not change the degeneracy index. -/
lemma degIndexWith_add_of_mem_zero {x k : E 0} (hk : k ∈ minimalSubspaceWith T 0) :
    degIndexWith T (x + k) = degIndexWith T x := by
  simp only [degIndexWith, quadrantDeg, coord_add_of_mem_zero T hk]

variable {C : Set (E 0)}

/-- Adding a vector of `E_0` does not change membership in `C`. -/
lemma add_mem_iff_of_mem_zero (hT : C = T 0 ⁻¹' quadrant n Wq 0) {x k : E 0}
    (hk : k ∈ minimalSubspaceWith T 0) : x + k ∈ C ↔ x ∈ C := by
  rw [hT, mem_preimage, mem_preimage]
  change (∀ i, 0 ≤ (T 0 (x + k)).1 i) ↔ ∀ i, 0 ≤ (T 0 x).1 i
  simp only [coord_add_of_mem_zero T hk]

/-- The coordinates `λ = (λ_1, …, λ_n)` restricted to a subspace `N`. -/
def coordsOn (N : Submodule ℝ (E 0)) : N →ₗ[ℝ] (Fin n → ℝ) where
  toFun u := (T 0 (u : E 0)).1
  map_add' u v := by simp
  map_smul' c u := by simp

@[simp] lemma coordsOn_apply (N : Submodule ℝ (E 0)) (u : N) : coordsOn T N u = (T 0 (u : E 0)).1 :=
  rfl

/-- If `N + E_0 = E`, the coordinates map `N` onto `ℝⁿ`. -/
lemma coordsOn_surjective {N : Submodule ℝ (E 0)} (h : N ⊔ minimalSubspaceWith T 0 = ⊤) :
    Surjective (coordsOn T N) := by
  intro a
  have hx : (T 0).symm (a, 0) ∈ N ⊔ minimalSubspaceWith T 0 := by rw [h]; exact Submodule.mem_top
  obtain ⟨u, hu, k, hk, huk⟩ := Submodule.mem_sup.1 hx
  refine ⟨⟨u, hu⟩, funext fun i => ?_⟩
  have h1 := congrArg (fun z => (T 0 z).1 i) huk
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h1
  rw [coord_add_of_mem_zero T hk] at h1
  exact h1

/-- If `N + E_0 = E` then `N ∩ C` has nonempty interior in `N`: the points with all coordinates
positive. -/
lemma interior_nonempty_of_sup_eq_top (hT : C = T 0 ⁻¹' quadrant n Wq 0)
    {N : Submodule ℝ (E 0)} (h : N ⊔ minimalSubspaceWith T 0 = ⊤) :
    (interior (Subtype.val ⁻¹' C : Set N)).Nonempty := by
  obtain ⟨u, hu⟩ := coordsOn_surjective T h (fun _ => 1)
  set G : Set N := ⋂ i, {v : N | 0 < (T 0 (v : E 0)).1 i} with hG
  have hGo : IsOpen G := by
    refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ?_
    exact (continuous_apply i).comp
      (continuous_fst.comp ((T 0).continuous.comp continuous_subtype_val))
  have hGC : G ⊆ Subtype.val ⁻¹' C := by
    intro v hv
    rw [mem_preimage, hT, mem_preimage]
    intro i
    exact (mem_iInter.1 hv i).le
  have huG : u ∈ G := mem_iInter.2 fun i => by
    have := congrFun hu i
    simp only [coordsOn_apply] at this
    change 0 < (T 0 (u : E 0)).1 i
    rw [this]; exact one_pos
  exact ⟨u, interior_maximal hGC hGo huG⟩

/-- **A complement inside `E_0` is a good complement** (Definition 3.1.24 (preprint 3.21), with any `ε`): adding a
vector of `E_0` does not change membership in `C`. -/
lemma isGoodComplement_of_le_zero (hT : C = T 0 ⁻¹' quadrant n Wq 0) {N Y : Submodule ℝ (E 0)}
    (hNY : IsCompl N Y) (hY : Y ≤ minimalSubspaceWith T 0) : IsGoodComplement E C N Y :=
  ⟨hNY, 1, one_pos, fun _ _ _ hp _ => (add_mem_iff_of_mem_zero T hT (hY hp)).symm⟩

/-- **Good position from `N + E_0 = E`**: a finite-dimensional `N` with `N + E_0 = E` is in good
position to `C`, with a closed good complement `Y ⊆ E_0`. -/
theorem exists_goodComplement_le_zero (hT : C = T 0 ⁻¹' quadrant n Wq 0)
    {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N] (h : N ⊔ minimalSubspaceWith T 0 = ⊤) :
    IsInGoodPosition E C N ∧ ∃ Y : Submodule ℝ (E 0), Y ≤ minimalSubspaceWith T 0 ∧
      IsClosed (Y : Set (E 0)) ∧ IsGoodComplement E C N Y := by
  obtain ⟨Y, hYK, hYc, hNY⟩ := exists_isClosed_isCompl_le (isClosed_minimalSubspaceWith T 0) h
  have hgood := isGoodComplement_of_le_zero T hT hNY hYK
  exact ⟨⟨interior_nonempty_of_sup_eq_top T hT h, Y, hgood⟩, Y, hYK, hYc, hgood⟩

/-- **The degeneracy index on the slice `N ∩ C`**: if `N` is finite-dimensional with `N + E_0 = E`,
then `N ∩ C` is a partial quadrant in `N` (with the constant sc-structure) presented by
`v ↦ (λ(v), v − s(λ(v)))`, `s` a linear section of `λ|_N`, and `d_{N ∩ C}(v) = d_C(v)` for
`v ∈ N ∩ C`: both count the vanishing coordinates `λ_i(v)`. -/
theorem degIndex_slice (hT : C = T 0 ⁻¹' quadrant n Wq 0) {N : Submodule ℝ (E 0)}
    [FiniteDimensional ℝ N] (h : N ⊔ minimalSubspaceWith T 0 = ⊤) {v : N} (hv : (v : E 0) ∈ C) :
    degIndex (ScBanach.const N) (Subtype.val ⁻¹' C) v = degIndexWith T v := by
  classical
  set lam := coordsOn T N with hlam
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective lam
    (LinearMap.range_eq_top.2 (coordsOn_surjective T h))
  have hs' : ∀ a, lam (s a) = a := fun a => congrArg (fun f => f a) hs
  set K₀ : Submodule ℝ N := LinearMap.ker lam with hK₀
  have hmemK : ∀ u : N, u - s (lam u) ∈ K₀ := fun u => by
    rw [hK₀, LinearMap.mem_ker, map_sub, hs', sub_self]
  let e : N ≃ₗ[ℝ] (Fin n → ℝ) × K₀ :=
    { toFun := fun u => (lam u, ⟨u - s (lam u), hmemK u⟩)
      map_add' := fun u w => by
        refine Prod.ext (map_add _ _ _) (Subtype.ext ?_)
        change (u + w) - s (lam (u + w)) = (u - s (lam u)) + (w - s (lam w))
        rw [map_add, map_add]
        abel
      map_smul' := fun c u => by
        refine Prod.ext (map_smul _ _ _) (Subtype.ext ?_)
        change c • u - s (lam (c • u)) = c • (u - s (lam u))
        rw [map_smul, map_smul, smul_sub]
      invFun := fun p => s p.1 + p.2
      left_inv := fun u => by simp
      right_inv := fun p => by
        have h0 : lam (p.2 : N) = 0 := p.2.2
        refine Prod.ext ?_ (Subtype.ext ?_)
        · change lam (s p.1 + p.2) = p.1
          rw [map_add, hs', h0, add_zero]
        · change s p.1 + (p.2 : N) - s (lam (s p.1 + p.2)) = p.2
          rw [map_add, hs', h0, add_zero]
          abel }
  have hpres : (Subtype.val ⁻¹' C : Set N) =
      scIsoOfLinearEquiv e 0 ⁻¹' quadrant n (ScBanach.const K₀) 0 := by
    ext u
    rw [mem_preimage, hT, mem_preimage, mem_preimage, scIsoOfLinearEquiv_apply]
    rfl
  rw [degIndex_eq (scIsoOfLinearEquiv e) hpres (show v ∈ (Subtype.val ⁻¹' C : Set N) from hv)]
  rfl

end Coordinates

/-! ### An sc-complement inside an sc-subspace -/

section ScComplement

variable {E : ScBanach}

/-- **An sc-complement inside an sc-subspace** (the last step of the proof of Theorem 4.2.11 (preprint 4.22) (3)):
let `N ⊆ E_∞` be finite-dimensional, `TR` an sc-subspace and `M = N + TR`.  Then `N` has in `M` an
sc-complement `B ⊆ TR`: an sc-subspace with `M_m = N_m ⊕ B_m` on every level.  *Proof*:
`K = N ∩ TR` is finite-dimensional and smooth, so it has an sc-complement `G` in `E`
(Proposition 1.1.7 (preprint 1.6)); `B = TR ∩ G`.  The smooth points of `B_m` are dense: for `x ∈ B_m` and smooth
`u ∈ TR_m` close to `x`, `u − P_m u ∈ B_m` is smooth and close to `x − P_m x = x` (`P` the
sc-projection onto `K` along `G`, Lemma 2.B). -/
theorem exists_scComplement_le {N M TR : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
    (hNs : N ≤ E.smooth) (hTR : E.IsScSubspace TR) (hM : M = N ⊔ TR) :
    ∃ B : Submodule ℝ (E 0), B ≤ TR ∧ E.IsScSubspace B ∧
      ∀ m, Disjoint (E.levelSub N m) (E.levelSub B m) ∧
        E.levelSub N m ⊔ E.levelSub B m = E.levelSub M m := by
  set K : Submodule ℝ (E 0) := N ⊓ TR with hKdef
  have : FiniteDimensional ℝ K := Submodule.finiteDimensional_of_le inf_le_left
  have hKs : K ≤ E.smooth := inf_le_left.trans hNs
  obtain ⟨G, hG⟩ := E.proposition_1_1_7 K hKs
  have hKG : K ⊓ G = ⊥ := by
    have := (hG.2.2 0).inf_eq_bot
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  set P := hG.scProj with hP
  -- `P_m u ∈ K_m`, `u − P_m u ∈ G_m`
  have hPK : ∀ m (u : E m), E.toBase m (P m u) ∈ K := fun m u => by
    have : P m u ∈ LinearMap.range (P m : E m →ₗ[ℝ] E m) := ⟨u, rfl⟩
    rw [hG.range_scProj m] at this
    exact this
  have hPG : ∀ m (u : E m), E.toBase m (u - P m u) ∈ G := fun m u => by
    have : u - P m u ∈ LinearMap.ker (P m : E m →ₗ[ℝ] E m) := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hG.scProj_idem, sub_self]
    rw [hG.ker_scProj m] at this
    exact this
  have hPzero : ∀ m (u : E m), E.toBase m u ∈ G → P m u = 0 := fun m u hu => by
    have : u ∈ LinearMap.ker (P m : E m →ₗ[ℝ] E m) := by rw [hG.ker_scProj m]; exact hu
    exact this
  refine ⟨TR ⊓ G, inf_le_left, ⟨hTR.1.inter hG.2.1.1, fun m x hx => ?_⟩, fun m => ⟨?_, ?_⟩⟩
  · -- density of the smooth points of `B_m`
    have hx' : E.toBase m x ∈ TR ⊓ G := hx
    have hcl := hTR.2 m (show x ∈ E.levelSub TR m from hx'.1)
    set Qm : E m →L[ℝ] E m := ContinuousLinearMap.id ℝ (E m) - P m with hQm
    have hQx : Qm x = x := by
      simp only [hQm, sub_apply, ContinuousLinearMap.id_apply,
        hPzero m x hx'.2, sub_zero]
    have hQmaps : MapsTo Qm (E.levelSub TR m ∩ E.smoothLvl m)
        (E.levelSub (TR ⊓ G) m ∩ E.smoothLvl m) := by
      rintro u ⟨huTR, hus⟩
      have hQu : Qm u = u - P m u := rfl
      refine ⟨?_, ?_⟩
      · rw [SetLike.mem_coe, ScBanach.mem_levelSub, hQu]
        refine ⟨?_, hPG m u⟩
        rw [map_sub]
        exact TR.sub_mem huTR (hPK m u).2
      · rw [hQu]
        exact E.smoothLvl_submodule_closed_sub hus (hKs (hPK m u))
    rw [← hQx]
    exact closure_mono (image_subset_iff.2 hQmaps)
      (image_closure_subset_closure_image Qm.continuous ⟨x, hcl, rfl⟩)
  · rw [Submodule.disjoint_def]
    intro w hwN hwB
    have hwN' : E.toBase m w ∈ N := hwN
    have hwB' : E.toBase m w ∈ TR ⊓ G := hwB
    have h0 : E.toBase m w ∈ K ⊓ G := ⟨⟨hwN', hwB'.1⟩, hwB'.2⟩
    rw [hKG, Submodule.mem_bot] at h0
    exact E.toBase_injective m (by rw [h0, map_zero])
  · refine le_antisymm (sup_le ?_ ?_) ?_
    · exact Submodule.comap_mono (hM ▸ le_sup_left)
    · exact Submodule.comap_mono (inf_le_left.trans (hM ▸ le_sup_right))
    · intro w hw
      have hw' : E.toBase m w ∈ N ⊔ TR := by rw [← hM]; exact hw
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hw'
      obtain ⟨am, ham⟩ := (E.mem_smooth_iff).1 (hNs ha) m
      set bm := w - am with hbm
      have hbm0 : E.toBase m bm = b := by rw [hbm, map_sub, ham, ← hab]; abel
      have h1 : am + P m bm ∈ E.levelSub N m := by
        rw [ScBanach.mem_levelSub, map_add, ham]
        exact N.add_mem ha (hPK m bm).1
      have h2 : bm - P m bm ∈ E.levelSub (TR ⊓ G) m := by
        rw [ScBanach.mem_levelSub]
        refine ⟨?_, hPG m bm⟩
        rw [map_sub, hbm0]
        exact TR.sub_mem hb (hPK m bm).2
      have : w = (am + P m bm) + (bm - P m bm) := by rw [hbm]; abel
      rw [this]
      exact Submodule.add_mem_sup h1 h2

end ScComplement

/-! ### General position in a tame chart (Definition 4.2.10 (preprint 4.21), chart level) -/

section GeneralPositionChart

variable {E : ScBanach} {n : ℕ} {Wq : ScBanach}
  (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) {C : Set (E 0)}
  (hT : C = T 0 ⁻¹' quadrant n Wq 0)

include hT in
/-- **General position from `T_yQ + E_0 = E`** (the core of Theorem 4.2.11 (preprint 4.22) (3)): let `r` be a tame
retraction onto `O`, `Q ⊆ O` a retract and `y ∈ Q₁` smooth, and suppose the tangent space
`T_yQ` (finite-dimensional, smooth) satisfies `T_yQ + E_0 = E`, `E_0` the minimal subspace at the
corner `0` (in the text: `T_aA + W = E`).  Then `T_yQ` has in `T_yO` an sc-complement contained in
`T_y^R O`.  *Proof* (the text's): `E_0 ⊆ E_y`, and intersecting `T_yQ + E_0 = E` with `T_yO ⊇ T_yQ`
gives `T_yO = T_yQ + (T_yO ∩ E_0) = T_yQ + T_y^R O` (modular law); `T_y^R O` is an sc-subspace
(Proposition 2.5.6 (preprint 2.36)), and `exists_scComplement_le` gives the sc-complement. -/
theorem isGeneralPositionRetractAt_of_sup_eq_top {R : ScRetraction E C} (hR : R.IsTameWith T)
    {Q : Set (E 0)} (hQ : IsScRetract E C Q) (hQR : Q ⊆ R.retract) {y : E 1}
    (hy : y ∈ E.lvlSet Q 1) (hys : y ∈ E.smoothLvl 1) {N' : Submodule ℝ (E 0)}
    [FiniteDimensional ℝ N'] (hN' : (N' : Set (E 0)) = tangentSpace E C Q y)
    (hN's : N' ≤ E.smooth) (hsup : N' ⊔ minimalSubspaceWith T 0 = ⊤) :
    IsGeneralPositionRetractAt E C R.retract Q T y := by
  have hyR : y ∈ E.lvlSet R.retract 1 := hQR hy
  set M : Submodule ℝ (E 0) := LinearMap.range (scDeriv R.U R y : E 0 →ₗ[ℝ] E 0) with hMdef
  have hM : (M : Set (E 0)) = tangentSpace E C R.retract y :=
    (tangentSpace_eq_coe_submodule R hyR).symm
  have hNM : N' ≤ M := fun v hv => by
    have hv' : v ∈ tangentSpace E C Q y := by rw [← hN']; exact hv
    have := tangentSpace_subset_of_subset R hQ hQR hy hv'
    rw [← hM] at this; exact this
  obtain ⟨-, hTR, -⟩ := proposition_2_5_6_partialCone hT hR hyR hys
  have hMeq : M = N' ⊔ reducedTangentSpaceWith R T y := by
    refine le_antisymm (fun v hv => ?_) (sup_le hNM inf_le_left)
    have hv' : v ∈ N' ⊔ minimalSubspaceWith T 0 := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨a, ha, k, hk, rfl⟩ := Submodule.mem_sup.1 hv'
    refine Submodule.add_mem_sup ha ⟨?_, minimalSubspaceWith_zero_le T _ hk⟩
    have : k = (a + k) - a := by abel
    rw [this]
    exact M.sub_mem hv (hNM ha)
  obtain ⟨B, hBTR, hB, hsplit⟩ := exists_scComplement_le hN's hTR hMeq
  exact ⟨N', M, B, hN', hM, hBTR, hB, hsplit⟩

end GeneralPositionChart

/-! ### Theorem 4.2.11 (preprint 4.22) in a tame chart centred at the point -/

section ChartTheorem

variable {E : ScBanach} {n : ℕ} {Wq : ScBanach}
  (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) {C : Set (E 0)}
  (hT : C = T 0 ⁻¹' quadrant n Wq 0)

include hT in
/-- **`T₀A + E_0 = E` from general position at the centre** (the first step of the proof of
Theorem 4.2.11 (preprint 4.22)): if `T₀Q` has in `T₀O` an sc-complement `B ⊆ T₀^R O ⊆ E_0` and `r` is tame, then
`E = T₀O ⊕ (1 − Dr(0))E` with `(1 − Dr(0))E ⊆ E_0` (Proposition 2.5.3 (preprint 2.35)), so
`E = T₀Q + B + (1 − Dr(0))E ⊆ T₀Q + E_0`.  (The text: "`E = T₀O ⊕ Z = T₀A ⊕ Ã ⊕ Z`, so `T₀A` has
in `E` an sc-complement `Y` contained in `W`".) -/
theorem sup_minimalSubspaceWith_eq_top {R : ScRetraction E C} (hR : R.IsTameWith T)
    (h0O : (0 : E 0) ∈ R.retract) {Q : Set (E 0)} {N : Submodule ℝ (E 0)}
    (hN : (N : Set (E 0)) = tangentSpace E C Q 0)
    (hgp : IsGeneralPositionRetractAt E C R.retract Q T 0) :
    N ⊔ minimalSubspaceWith T 0 = ⊤ := by
  obtain ⟨N', M, B, hN', hM, hBM, -, hsplit⟩ := hgp
  have hNN' : N' = N := SetLike.coe_injective (hN'.trans hN.symm)
  subst hNN'
  have h01 : (0 : E 1) ∈ E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0O
  have hs0 : (0 : E 1) ∈ E.smoothLvl 1 := by
    change E.toBase 1 0 ∈ (E.smooth : Set (E 0))
    rw [map_zero]; exact E.smooth.zero_mem
  have hK := (proposition_2_5_3 hT hR h01 hs0).1
  rw [map_zero] at hK hBM
  have hMeq : M = LinearMap.range (scDeriv R.U R 0 : E 0 →ₗ[ℝ] E 0) :=
    SetLike.coe_injective (hM.trans (tangentSpace_eq_coe_submodule R h01))
  have hMNB : M = N' ⊔ B := by
    have := (hsplit 0).2
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero, ScBanach.levelSub_zero, eq_comm] at this
  rw [eq_top_iff]
  intro x _
  set D := scDeriv R.U R 0 with hD
  have hDx : D x ∈ N' ⊔ B := by rw [← hMNB, hMeq]; exact ⟨x, rfl⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hDx
  have hrest : x - D x ∈ minimalSubspaceWith T 0 := hK ⟨x, rfl⟩
  have : x = a + (b + (x - D x)) := by rw [← add_assoc, hab]; abel
  rw [this]
  exact Submodule.add_mem_sup ha (Submodule.add_mem _ (hBM hb).2 hrest)

/-- **`T_aA + E_0 = E` along the graph** (the text: "by means of the particular form of the map
`α : h ↦ h + Dδ(v)h`, also `T_aA + W = E` for all `a ∈ A ∩ U`"): if `Γ : V → Q ∩ W` is the graph
map of Proposition 4.1.9 (preprint 4.9) for a projection `p` onto `N` whose kernel lies in `Y ⊆ E_0`, and
`N + E_0 = E`, then at `y` over `Γ(v)` the tangent space `T_yQ = DΓ(v)N` satisfies
`T_yQ + E_0 = E`: `DΓ(v)n − n ∈ ker p ⊆ E_0` because `p ∘ DΓ(v) = 1`. -/
theorem sup_minimalSubspaceWith_eq_top_graph {Q : Set (E 0)} (hQ : IsScRetract E C Q)
    {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N] (hsup : N ⊔ minimalSubspaceWith T 0 = ⊤)
    {Y : Submodule ℝ (E 0)} (hY : Y ≤ minimalSubspaceWith T 0) {p : E 0 →L[ℝ] N}
    (hpN : ∀ x : N, p x = x) (hker : ∀ x, p x = 0 → x ∈ Y) {W : Set (E 0)} (hW : IsOpen W)
    {V : Set N} (hV : IsRelOpenInQuadrant (ScBanach.const N) (Subtype.val ⁻¹' C) V) {Γ : N → E 0}
    (hpmap : IsScSmoothRetractMap E C (Q ∩ W) (ScBanach.const N) (Subtype.val ⁻¹' C) V p)
    (hΓmap : IsScSmoothRetractMap (ScBanach.const N) (Subtype.val ⁻¹' C) V E C (Q ∩ W) Γ)
    (hΓp : ∀ u ∈ Q ∩ W, Γ (p u) = u) (hpΓ : ∀ a ∈ V, p (Γ a) = a) {v : N} (hv : v ∈ V)
    {y : E 1} (hy : E.toBase 1 y = Γ v) {N' : Submodule ℝ (E 0)}
    (hN' : (N' : Set (E 0)) = tangentSpace E C Q y) :
    N' ⊔ minimalSubspaceWith T 0 = ⊤ := by
  have hQW : IsScRetract E C (Q ∩ W) := proposition_2_3_1_one hQ hW
  obtain ⟨-, hTy, hpD⟩ := tangentSpace_eq_range_graph hQW hV hpmap hΓmap hΓp hpΓ hv hy
  have hyQW : E.toBase 1 y ∈ Q ∩ W := by rw [hy]; exact hΓmap.mapsTo hv
  rw [tangentSpace_inter_isOpen hQ hW hyQW] at hTy
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ N ⊔ minimalSubspaceWith T 0 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨a, ha, k, hk, rfl⟩ := Submodule.mem_sup.1 hx
  set D := scDeriv (E := ScBanach.const N) V Γ v with hD
  have hDa : D ⟨a, ha⟩ ∈ N' := by
    rw [← SetLike.mem_coe, hN', hTy]; exact ⟨_, rfl⟩
  have hdiff : a - D ⟨a, ha⟩ ∈ minimalSubspaceWith T 0 := by
    refine hY (hker _ ?_)
    rw [map_sub, hpD, sub_eq_zero]
    exact hpN ⟨a, ha⟩
  have : a + k = D ⟨a, ha⟩ + ((a - D ⟨a, ha⟩) + k) := by abel
  rw [this]
  exact Submodule.add_mem_sup hDa (Submodule.add_mem _ hdiff hk)

include hT in
/-- **Theorem 4.2.11 (preprint 4.22) in a tame chart centred at the point** (the chart form of (2) and (3), and the
graph description of `A` used in the text's proof).  Let `r` be a tame retraction onto `O ∋ 0`
(presentation `T`, `C = T⁻¹([0, ∞)ⁿ ⊕ W)`, so that all coordinates vanish at `0`: `d_C(0) = n`), `t`
an sc⁺-retraction onto `Q ⊆ O` with `0 ∈ Q` (the chart model of the submanifold `A`), and
`N = T₀Q`.  If `T₀Q` has in `T₀O` an sc-complement contained in `T₀^R O` (Definition 4.2.10 (preprint 4.21) at `0`),
then:
* `N + E_0 = E`, `N` is in good position to `C`, and `N` has a closed (good) complement
  `Y ⊆ E_0` (the text's `Y ⊆ W`), with the projection `p : E → N` along `Y`;
* Proposition 4.1.9 (preprint 4.9) for this `Y`: `Q ∩ W'` is the graph `Γ(V)`, `Γ(v) − v ∈ Y`, of an sc-smooth
  `Γ` on a relatively open `V ∋ 0` of the partial quadrant `N ∩ C`, with inverse `p`;
* (2) **`d_{N ∩ C}(v) = d_C(Γ(v))`** for `v ∈ V` (the text: `d_A(a) = d_{T₀A ∩ C}(p(a)) = d_C(a)`);
* (3) **general position at every point of `Q ∩ W'`**: at every level-`1` point `y` over
  `u ∈ Q ∩ W'`, `T_yQ` has in `T_yO` an sc-complement contained in `T_y^R O`. -/
theorem theorem_4_2_11_chart {R : ScRetraction E C} (hR : R.IsTameWith T)
    (h0O : (0 : E 0) ∈ R.retract) (t : ScRetraction E C) (ht : t.IsScPlus)
    (htR : t.retract ⊆ R.retract) (h0 : (0 : E 0) ∈ t.retract) {N : Submodule ℝ (E 0)}
    [FiniteDimensional ℝ N] (hN : (N : Set (E 0)) = tangentSpace E C t.retract 0)
    (hgp : IsGeneralPositionRetractAt E C R.retract t.retract T 0) :
    N ⊔ minimalSubspaceWith T 0 = ⊤ ∧ IsInGoodPosition E C N ∧
    ∃ (Y : Submodule ℝ (E 0)) (p : E 0 →L[ℝ] N) (W : Set (E 0)) (V : Set N) (Γ : N → E 0),
      Y ≤ minimalSubspaceWith T 0 ∧ IsClosed (Y : Set (E 0)) ∧ IsGoodComplement E C N Y ∧
      (∀ x : N, p x = x) ∧ (∀ y ∈ Y, p y = 0) ∧ (∀ x, p x = 0 → x ∈ Y) ∧
      IsOpen W ∧ (0 : E 0) ∈ W ∧
      IsRelOpenInQuadrant (ScBanach.const N) (Subtype.val ⁻¹' C) V ∧ (0 : N) ∈ V ∧
      IsScSmooth (E := ScBanach.const N) (F := E) V Γ ∧
      (∀ a ∈ V, p (Γ a) = a) ∧ (∀ a ∈ V, Γ a - a ∈ Y) ∧ Γ '' V = t.retract ∩ W ∧
      (∀ u ∈ t.retract ∩ W, Γ (p u) = u) ∧ Γ 0 = 0 ∧
      IsScSmoothRetractMap E C (t.retract ∩ W) (ScBanach.const N) (Subtype.val ⁻¹' C) V p ∧
      IsScSmoothRetractMap (ScBanach.const N) (Subtype.val ⁻¹' C) V E C (t.retract ∩ W) Γ ∧
      (∀ a ∈ V, degIndex (ScBanach.const N) (Subtype.val ⁻¹' C) a = degIndex E C (Γ a)) ∧
      (∀ u ∈ t.retract ∩ W, ∀ y : E 1, E.toBase 1 y = u →
        IsGeneralPositionRetractAt E C R.retract t.retract T y) := by
  have hsup := sup_minimalSubspaceWith_eq_top T hT hR h0O hN hgp
  obtain ⟨hgood, Y, hYE, hYc, hYgood⟩ := exists_goodComplement_le_zero T hT hsup
  obtain ⟨p, hpN, hpY, hker⟩ := exists_proj_of_isCompl hYc hYgood.isCompl
  obtain ⟨W, V, Γ, hW, h0W, hV, h0V, hΓs, hpΓ, hΓY, hΓV, hΓp, hΓ0, hpmap, hΓmap⟩ :=
    proposition_4_1_9 t ht h0 hN hgood hYgood hYc p hpN hpY
  refine ⟨hsup, hgood, Y, p, W, V, Γ, hYE, hYc, hYgood, hpN, hpY, hker, hW, h0W, hV, h0V, hΓs, hpΓ,
    hΓY, hΓV, hΓp, hΓ0, hpmap, hΓmap, fun a ha => ?_, fun u hu y hy => ?_⟩
  · -- (2): `d_{N ∩ C}(a) = d_C(a) = d_C(Γ a)`
    have haC : (a : E 0) ∈ C := by
      obtain ⟨O', -, hO'⟩ := hV.relOpen
      rw [hO'] at ha; exact ha.2
    have hΓC : Γ a ∈ C := t.retract_subset_C (hΓmap.mapsTo ha).1
    rw [degIndex_slice T hT hsup haC, degIndex_eq T hT hΓC,
      show Γ a = (a : E 0) + (Γ a - a) by abel, degIndexWith_add_of_mem_zero T (hYE (hΓY a ha))]
  · -- (3): general position at `y`
    have huS : u ∈ Γ '' V := by rw [hΓV]; exact hu
    obtain ⟨v, hv, rfl⟩ := huS
    have hyt : y ∈ E.lvlSet t.retract 1 := by rw [ScBanach.mem_lvlSet, hy]; exact hu.1
    have hys : y ∈ E.smoothLvl 1 := by
      change E.toBase 1 y ∈ (E.smooth : Set (E 0))
      rw [hy]; exact lemma_4_1_7_i ht hu.1
    set N' : Submodule ℝ (E 0) := LinearMap.range (scDeriv t.U t y : E 0 →ₗ[ℝ] E 0) with hN'def
    have : FiniteDimensional ℝ N' := lemma_4_1_7_ii ht hyt
    have hN' : (N' : Set (E 0)) = tangentSpace E C t.retract y :=
      (tangentSpace_eq_coe_submodule t hyt).symm
    have hN's : N' ≤ E.smooth :=
      (E.proposition_1_1_7_iff N').1 (t.isScSplitting_range_scDeriv hyt hys).1
    have hsup' := sup_minimalSubspaceWith_eq_top_graph T t.isScRetract hsup hYE hpN hker hW hV
      hpmap hΓmap hΓp hpΓ hv hy hN'
    exact isGeneralPositionRetractAt_of_sup_eq_top T hT hR t.isScRetract htR hyt hys hN' hN's hsup'

/-- `dim(M/K) ≤ dim N` when `M = N + B` with `B ⊆ K` (the image of `N` spans `M/K`). -/
theorem quotDim_le_finrank_of_eq_sup {V : Type*} [AddCommGroup V] [Module ℝ V]
    {M N B K : Submodule ℝ V} [FiniteDimensional ℝ N] (hNM : N ≤ M) (hM : M = N ⊔ B)
    (hBK : B ≤ K) : quotDim M K ≤ finrank ℝ N := by
  set f : N →ₗ[ℝ] M ⧸ K.comap M.subtype :=
    (K.comap M.subtype).mkQ ∘ₗ Submodule.inclusion hNM with hf
  refine LinearMap.finrank_le_finrank_of_surjective (f := f) fun q => ?_
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ q
  have hm : (m : V) ∈ N ⊔ B := hM ▸ m.2
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hm
  refine ⟨⟨a, ha⟩, ?_⟩
  rw [hf, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub, Submodule.coe_inclusion]
  have : (a : V) - m = -b := by rw [← hab]; abel
  rw [this]
  exact K.neg_mem (hBK hb)

include hT in
/-- **Remark 4.3.2 (preprint 4.24) in a chart**: at a smooth point `z` of a tame retract, `codim T_z^R O = d_C(z)`
(Proposition 2.5.6 (preprint 2.36)), and if `T_zQ` has in `T_zO` an sc-complement contained in `T_z^R O`, then
`d_C(z) ≤ dim T_zQ` (`T_zO = T_zQ + T_z^R O`). -/
theorem remark_4_3_2_chart {R : ScRetraction E C} (hR : R.IsTameWith T) {Q : Set (E 0)} {z : E 1}
    (hz : z ∈ E.lvlSet R.retract 1) (hzs : z ∈ E.smoothLvl 1)
    (hgp : IsGeneralPositionRetractAt E C R.retract Q T z) {N : Submodule ℝ (E 0)}
    [FiniteDimensional ℝ N] (hN : (N : Set (E 0)) = tangentSpace E C Q z) :
    quotDim (LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0)) (reducedTangentSpaceWith R T z) =
        degIndex E C (E.toBase 1 z) ∧
      degIndex E C (E.toBase 1 z) ≤ finrank ℝ N := by
  have hq : quotDim (LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0))
      (reducedTangentSpaceWith R T z) = degIndex E C (E.toBase 1 z) := by
    rw [quotDim_reducedTangentSpaceWith_eq hR hz hzs, degIndex_eq T hT (R.retract_subset_C hz)]
  refine ⟨hq, ?_⟩
  obtain ⟨N', M, B, hN', hM, hBM, -, hsplit⟩ := hgp
  have hNN' : N' = N := SetLike.coe_injective (hN'.trans hN.symm)
  subst hNN'
  have hMeq : M = LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0) :=
    SetLike.coe_injective (hM.trans (tangentSpace_eq_coe_submodule R hz))
  subst hMeq
  have hMNB : LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0) = N' ⊔ B := by
    have := (hsplit 0).2
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero, ScBanach.levelSub_zero, eq_comm] at this
  rw [← hq]
  exact quotDim_le_finrank_of_eq_sup (hMNB ▸ le_sup_left) hMNB hBM

/-- **General position implies good position** (in a chart, at a smooth point of a tame retract):
if `T_zQ` has in `T_zO` an sc-complement `B ⊆ T_z^R O = T_zO ∩ E_z`, then `T_zQ` is in good position
to the partial cone `C_zO` inside `T_zO`, with good complement `B` (adding a vector of `E_z` does
not change membership in `C_z`); the interior points come from the coordinates `λ_i`, `i ∈ I(z)`,
which map `T_zO` onto `ℝ^{I(z)}` (`dim T_zO/T_z^R O = d_C(z)`, Proposition 2.5.6 (preprint 2.36)) and vanish on
`B`.  This is what makes `A ∩ F_σ` tame in Theorem 4.2.11 (preprint 4.22) (4), through Theorem 4.2.7 (preprint 4.18). -/
theorem IsGeneralPositionRetractAt.isGoodPositionRetractAt {R : ScRetraction E C}
    (hR : R.IsTameWith T) {Q : Set (E 0)} {z : E 1} (hz : z ∈ E.lvlSet R.retract 1)
    (hzs : z ∈ E.smoothLvl 1) (hgp : IsGeneralPositionRetractAt E C R.retract Q T z) :
    IsGoodPositionRetractAt E C R.retract Q T z := by
  classical
  obtain ⟨N, M, B, hN, hM, hBM, -, hsplit⟩ := hgp
  set e := E.toBase 1 z with he
  have hMeq : M = LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0) :=
    SetLike.coe_injective (hM.trans (tangentSpace_eq_coe_submodule R hz))
  subst hMeq
  have hMNB : N ⊔ B = LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0) := by
    have := (hsplit 0).2
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  have hNB : N ⊓ B = ⊥ := by
    have := (hsplit 0).1
    rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
    exact this.eq_bot
  have hBE : ∀ b ∈ B, ∀ i, (T 0 e).1 i = 0 → (T 0 b).1 i = 0 := fun b hb i hi =>
    (mem_minimalSubspaceWith T).1 (hBM hb).2 i hi
  refine ⟨N, _, hN, hM, ⟨hMNB ▸ le_sup_left, ?_, B, fun b hb => (hBM hb).1, hNB, hMNB, 1, one_pos,
    fun x _ b hb _ => ?_⟩⟩
  · -- interior points: `λ_{I(z)}` maps `M` onto `ℝ^{I(z)}`
    set M := LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0) with hMdef
    set f : M →ₗ[ℝ] ({i : Fin n // (T 0 e).1 i = 0} → ℝ) :=
      (coordMapL T e : E 0 →ₗ[ℝ] _) ∘ₗ M.subtype with hf
    have hker : LinearMap.ker f = (reducedTangentSpaceWith R T z).comap M.subtype := by
      ext ⟨v, hv⟩
      simp only [hf, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
        Submodule.mem_comap, reducedTangentSpaceWith, Submodule.mem_inf]
      exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩
    have hq := quotDim_reducedTangentSpaceWith_eq hR hz hzs
    rw [quotDim, ← hker] at hq
    have hrange : LinearMap.range f = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← (LinearMap.quotKerEquivRange f).finrank_eq, hq, Module.finrank_fintype_fun_eq_card,
        Fintype.card_subtype]
      rfl
    obtain ⟨m, hm⟩ : (fun _ => (1 : ℝ)) ∈ LinearMap.range f := by
      rw [hrange]; exact Submodule.mem_top
    have hmM : (m : E 0) ∈ N ⊔ B := by rw [hMNB]; exact m.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmM
    have ha1 : ∀ i, (T 0 e).1 i = 0 → (T 0 a).1 i = 1 := fun i hi => by
      have h1 := congrFun hm ⟨i, hi⟩
      simp only [hf, LinearMap.comp_apply, Submodule.coe_subtype, ContinuousLinearMap.coe_coe,
        coordMapL_apply] at h1
      rw [← hab, map_add, Prod.fst_add, Pi.add_apply, hBE b hb i hi, add_zero] at h1
      exact h1
    set G : Set N := ⋂ i : {i : Fin n // (T 0 e).1 i = 0}, {u : N | 0 < (T 0 (u : E 0)).1 i}
      with hG
    have hGo : IsOpen G := by
      refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ?_
      exact (continuous_apply _).comp
        (continuous_fst.comp ((T 0).continuous.comp continuous_subtype_val))
    have hGC : G ⊆ Subtype.val ⁻¹' partialQuadrantAtWith T e := fun u hu i hi =>
      (mem_iInter.1 hu ⟨i, hi⟩).le
    have haG : (⟨a, ha⟩ : N) ∈ G := mem_iInter.2 fun i => by
      change 0 < (T 0 a).1 i.1
      rw [ha1 i.1 i.2]; exact one_pos
    exact ⟨_, interior_maximal hGC hGo haG⟩
  · -- `B ⊆ E_z` is a good complement
    change (∀ i, (T 0 e).1 i = 0 → 0 ≤ (T 0 x).1 i) ↔ ∀ i, (T 0 e).1 i = 0 → 0 ≤ (T 0 (x + b)).1 i
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [map_add, Prod.fst_add, Pi.add_apply, hBE b hb i hi, add_zero]

end ChartTheorem

/-! ### Theorem 4.2.11 (preprint 4.22) (4) in the chart: the retraction onto `A ∩ F_σ` -/

section CornerSubmanifold

variable {E : ScBanach} {n : ℕ} {Wq : ScBanach}
  (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) {C : Set (E 0)}
  (hT : C = T 0 ⁻¹' quadrant n Wq 0)

open scoped Classical in
/-- `a ↦ a · 1_σ`: keep the coordinates in `σ`, kill the others. -/
def maskL (σ : Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i => if i ∈ σ then LinearMap.proj i else 0

lemma maskL_apply_mem {σ : Finset (Fin n)} (a : Fin n → ℝ) {i : Fin n} (hi : i ∈ σ) :
    maskL σ a i = a i := by
  classical
  simp [maskL, hi]

lemma maskL_apply_not_mem {σ : Finset (Fin n)} (a : Fin n → ℝ) {i : Fin n} (hi : i ∉ σ) :
    maskL σ a i = 0 := by
  classical
  simp [maskL, hi]

/-- **`κ_σ`, killing the coordinates in `σ` on `N`** (the text's `κ_σ`): for a linear section `s` of
the coordinates `λ|_N : N → ℝⁿ`, `κ_σ(v) = v − s(λ(v)·1_σ)`, so that `λ_i(κ_σ v) = 0` for `i ∈ σ`
and `λ_j(κ_σ v) = λ_j(v)` for `j ∉ σ`. -/
def killOn (N : Submodule ℝ (E 0)) (s : (Fin n → ℝ) →ₗ[ℝ] N) (σ : Finset (Fin n)) : N →ₗ[ℝ] N :=
  LinearMap.id - s ∘ₗ maskL σ ∘ₗ coordsOn T N

variable {T}

lemma coordsOn_killOn {N : Submodule ℝ (E 0)} {s : (Fin n → ℝ) →ₗ[ℝ] N}
    (hs : ∀ a, coordsOn T N (s a) = a) (σ : Finset (Fin n)) (v : N) (i : Fin n) :
    coordsOn T N (killOn T N s σ v) i = if i ∈ σ then 0 else coordsOn T N v i := by
  simp only [killOn, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs,
    Pi.sub_apply]
  split_ifs with hi
  · rw [maskL_apply_mem _ hi, sub_self]
  · rw [maskL_apply_not_mem _ hi, sub_zero]

lemma killOn_eq_self {N : Submodule ℝ (E 0)} {s : (Fin n → ℝ) →ₗ[ℝ] N} (σ : Finset (Fin n))
    {v : N} (hv : ∀ i ∈ σ, coordsOn T N v i = 0) : killOn T N s σ v = v := by
  have : maskL σ (coordsOn T N v) = 0 := by
    funext i
    by_cases hi : i ∈ σ
    · rw [maskL_apply_mem _ hi, hv i hi]; rfl
    · rw [maskL_apply_not_mem _ hi]; rfl
  simp only [killOn, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, this, map_zero,
    sub_zero]

lemma killOn_idem {N : Submodule ℝ (E 0)} {s : (Fin n → ℝ) →ₗ[ℝ] N}
    (hs : ∀ a, coordsOn T N (s a) = a) (σ : Finset (Fin n)) (v : N) :
    killOn T N s σ (killOn T N s σ v) = killOn T N s σ v :=
  killOn_eq_self σ fun i hi => by rw [coordsOn_killOn hs, if_pos hi]

include hT in
lemma killOn_mem {N : Submodule ℝ (E 0)} {s : (Fin n → ℝ) →ₗ[ℝ] N}
    (hs : ∀ a, coordsOn T N (s a) = a) (σ : Finset (Fin n)) {v : N} (hv : (v : E 0) ∈ C) :
    (killOn T N s σ v : E 0) ∈ C := by
  rw [hT] at hv ⊢
  intro i
  have h1 := coordsOn_killOn hs σ v i
  simp only [coordsOn_apply] at h1
  change 0 ≤ (T 0 (killOn T N s σ v : E 0)).1 i
  rw [h1]
  split_ifs
  · exact le_rfl
  · exact hv i

/-- A continuous linear map `L : E₀ → N` into a finite-dimensional space, as an sc-operator
`E → N` (constant structure on `N`), `L_m = L ∘ ι_{m,0}`. -/
def opToConst {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (L : E 0 →L[ℝ] N) : ScOperator E (ScBanach.const N) where
  lvl m := L.comp (E.toBase m)
  incl_comm m x := by
    change L (E.toBase (m + 1) x) = L (E.toBase m (E.incl m x))
    rw [E.toBase_succ]

@[simp] lemma opToConst_zero_apply {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (L : E 0 →L[ℝ] N) (x : E 0) : opToConst L 0 x = L x := rfl

include hT in
/-- **Theorem 4.2.11 (preprint 4.22) (4) in the chart, the sc⁺-retraction onto `A ∩ F_σ`** (the brief's
`Γ ∘ κ_σ ∘ p ∘ s`; the text gives no argument).  In the situation of `theorem_4_2_11_chart`, for
`σ ⊆ {1, …, n}` and an open `B ∋ 0`, there are an open `G ∋ 0`, `G ⊆ W ∩ B`, and an
**sc⁺-retraction `t_σ = Γ ∘ κ_σ ∘ p ∘ t`** (on `U ∩ t⁻¹(G)`) onto
`Q_σ = Q ∩ G ∩ f_σ`, `f_σ = {λ_i = 0, i ∈ σ}` (the chart form of `A ∩ F_σ`).  At every point `y` of
`Q_σ` the tangent vectors of `Q` lying in `f_σ` are tangent to `Q_σ`: `T_yQ ∩ f_σ ⊆ T_yQ_σ`
(`Dt_σ(y) = DΓ(w) ∘ κ_σ ∘ p ∘ Dt(y)` fixes `T_yQ ∩ f_σ = DΓ(w)(N ∩ f_σ)`). -/
theorem exists_scPlus_retraction_corner (t : ScRetraction E C) (ht : t.IsScPlus)
    {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N] (hsup : N ⊔ minimalSubspaceWith T 0 = ⊤)
    {Y : Submodule ℝ (E 0)} (hYE : Y ≤ minimalSubspaceWith T 0) {p : E 0 →L[ℝ] N}
    (hpN : ∀ x : N, p x = x) (hker : ∀ x, p x = 0 → x ∈ Y) {W : Set (E 0)} (hW : IsOpen W)
    (h0W : (0 : E 0) ∈ W)
    {V : Set N} (hV : IsRelOpenInQuadrant (ScBanach.const N) (Subtype.val ⁻¹' C) V)
    (h0V : (0 : N) ∈ V) {Γ : N → E 0} (hΓs : IsScSmooth (E := ScBanach.const N) (F := E) V Γ)
    (hpΓ : ∀ a ∈ V, p (Γ a) = a) (hΓY : ∀ a ∈ V, Γ a - a ∈ Y)
    (hΓp : ∀ u ∈ t.retract ∩ W, Γ (p u) = u) (hΓ0 : Γ 0 = 0)
    (hpmap : IsScSmoothRetractMap E C (t.retract ∩ W) (ScBanach.const N) (Subtype.val ⁻¹' C) V p)
    (hΓmap : IsScSmoothRetractMap (ScBanach.const N) (Subtype.val ⁻¹' C) V E C (t.retract ∩ W) Γ)
    (σ : Finset (Fin n)) {B : Set (E 0)} (hB : IsOpen B) (h0B : (0 : E 0) ∈ B) :
    ∃ (G : Set (E 0)) (tσ : ScRetraction E C), IsOpen G ∧ (0 : E 0) ∈ G ∧ G ⊆ W ∩ B ∧
      tσ.IsScPlus ∧ tσ.U ⊆ t.U ∧
      tσ.retract = t.retract ∩ G ∩ {z | ∀ i ∈ σ, (T 0 z).1 i = 0} ∧
      ∀ y : E 1, E.toBase 1 y ∈ tσ.retract → ∀ a ∈ tangentSpace E C t.retract y,
        (∀ i ∈ σ, (T 0 a).1 i = 0) → a ∈ tangentSpace E C tσ.retract y := by
  classical
  -- the section `s` of the coordinates and `κ = κ_σ`
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (coordsOn T N)
    (LinearMap.range_eq_top.2 (coordsOn_surjective T hsup))
  have hs' : ∀ a, coordsOn T N (s a) = a := fun a => congrArg (fun f => f a) hs
  set κL : N →L[ℝ] N := LinearMap.toContinuousLinearMap (killOn T N s σ) with hκL
  have hκ : ∀ v, κL v = killOn T N s σ v := fun _ => rfl
  have hκκ : ∀ v, κL (κL v) = κL v := fun v => killOn_idem hs' σ v
  -- coordinates along the graph and on `Q ∩ W`
  have hcoordΓ : ∀ a ∈ V, ∀ i, (T 0 (Γ a)).1 i = (T 0 (a : E 0)).1 i := fun a ha i => by
    have := coord_add_of_mem_zero T (x := (a : E 0)) (hYE (hΓY a ha)) i
    rwa [add_sub_cancel] at this
  have hVC : ∀ a ∈ V, (a : E 0) ∈ C := fun a ha => by
    obtain ⟨O', -, hO'⟩ := hV.relOpen
    rw [hO'] at ha; exact ha.2
  -- `V ∩ Γ⁻¹(B)` is relatively open
  obtain ⟨OV, hOV, hVeq⟩ := hV.relOpen
  obtain ⟨O₂, hO₂, hO₂eq⟩ := continuousOn_iff'.1 hΓs.isSc1.isSc0.continuousOn_base B hB
  set O₃ : Set N := OV ∩ O₂ with hO₃def
  have hO₃ : IsOpen O₃ := hOV.inter hO₂
  have hmemV : ∀ w : N, w ∈ O₃ → (w : E 0) ∈ C → w ∈ V ∧ Γ w ∈ B := fun w hw hwC => by
    have hwV : w ∈ V := by rw [hVeq]; exact ⟨hw.1, hwC⟩
    have : w ∈ Γ ⁻¹' B ∩ V := by rw [hO₂eq]; exact ⟨hw.2, hwV⟩
    exact ⟨hwV, this.1⟩
  -- the open set `G`
  set G : Set (E 0) := (W ∩ B) ∩ p ⁻¹' (κL ⁻¹' O₃) with hGdef
  have hG : IsOpen G := (hW.inter hB).inter ((hO₃.preimage κL.continuous).preimage p.continuous)
  have h0G : (0 : E 0) ∈ G := by
    refine ⟨⟨h0W, h0B⟩, ?_⟩
    rw [mem_preimage, mem_preimage, map_zero, map_zero]
    have h0 : (0 : N) ∈ Γ ⁻¹' B ∩ V := ⟨by rw [mem_preimage, hΓ0]; exact h0B, h0V⟩
    rw [hO₂eq] at h0
    have h0' : (0 : N) ∈ OV := by
      have := h0V; rw [hVeq] at this; exact this.1
    exact ⟨h0', h0.1⟩
  set R₁ := t.restrict hG with hR₁
  -- the point `w = κ(p(t u))` and its image `Γ w`
  have hkey : ∀ u ∈ R₁.U, κL (p (t u)) ∈ V ∧ Γ (κL (p (t u))) ∈ t.retract ∩ W ∧
      Γ (κL (p (t u))) ∈ G ∧ Γ (κL (p (t u))) ∈ R₁.U := by
    intro u hu
    have htu : t u ∈ t.retract ∩ W := ⟨t.apply_mem_retract hu.1, hu.2.1.1⟩
    have hptV : p (t u) ∈ V := hpmap.mapsTo htu
    have hwC : (κL (p (t u)) : E 0) ∈ C := killOn_mem hT hs' σ (hVC _ hptV)
    obtain ⟨hwV, hwB⟩ := hmemV _ hu.2.2 hwC
    have hΓw := hΓmap.mapsTo hwV
    have hΓwG : Γ (κL (p (t u))) ∈ G := by
      refine ⟨⟨hΓw.2, hwB⟩, ?_⟩
      rw [mem_preimage, mem_preimage, hpΓ _ hwV, hκκ]
      exact hu.2.2
    refine ⟨hwV, hΓw, hΓwG, t.retract_subset hΓw.1, ?_⟩
    change t (Γ (κL (p (t u)))) ∈ G
    rw [t.apply_eq_self_of_mem_retract hΓw.1]; exact hΓwG
  -- the sc-smooth map `g = κ ∘ p ∘ t : U ∩ t⁻¹(G) → V`
  set g : E 0 → N := fun u => κL (p (t u)) with hgdef
  set op : ScOperator E (ScBanach.const N) := opToConst (κL.comp p) with hop
  have hg : IsScSmooth (F := ScBanach.const N) R₁.U g := by
    have := IsScSmooth.comp R₁.isScDomain (isScDomain_univ _) (op.isScSmooth (isScDomain_univ _))
      R₁.isScSmooth (mapsTo_univ _ _)
    exact this
  have hgV : MapsTo g R₁.U V := fun u hu => (hkey u hu).1
  -- the retraction `t_σ`
  let tσ : ScRetraction E C :=
    { U := R₁.U
      toFun := fun u => Γ (g u)
      relOpen := R₁.relOpen
      mapsTo := fun u hu => (hkey u hu).2.2.2
      isScSmooth := IsScSmooth.comp R₁.isScDomain hV.isScDomain hΓs hg hgV
      idem := fun u hu => by
        obtain ⟨hwV, hΓw, -, -⟩ := hkey u hu
        change Γ (κL (p (t (Γ (κL (p (t u))))))) = Γ (κL (p (t u)))
        rw [t.apply_eq_self_of_mem_retract hΓw.1, hpΓ _ hwV, hκκ] }
  have htσU : tσ.U ⊆ t.U := fun u hu => hu.1
  -- sc⁺
  have hplus : tσ.IsScPlus := by
    have h1 := IsScPlus.comp_isScSmooth R₁.isScDomain t.isScDomain ht tσ.isScSmooth
      fun u hu => htσU (tσ.mapsTo hu)
    refine h1.congr R₁.isScDomain fun u hu => ?_
    exact t.apply_eq_self_of_mem_retract (hkey u hu).2.1.1
  -- the retract
  have hret : tσ.retract = t.retract ∩ G ∩ {z | ∀ i ∈ σ, (T 0 z).1 i = 0} := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨hwV, hΓw, hΓwG, -⟩ := hkey u hu
      refine ⟨⟨hΓw.1, hΓwG⟩, fun i hi => ?_⟩
      change (T 0 (Γ (κL (p (t u))))).1 i = 0
      rw [hcoordΓ _ hwV i]
      have := coordsOn_killOn hs' σ (p (t u)) i
      rw [if_pos hi] at this
      exact this
    · rintro ⟨⟨hzQ, hzG⟩, hzσ⟩
      have hzU : z ∈ R₁.U := ⟨t.retract_subset hzQ, by
        rw [mem_preimage, t.apply_eq_self_of_mem_retract hzQ]; exact hzG⟩
      refine ⟨z, hzU, ?_⟩
      change Γ (κL (p (t z))) = z
      have hzQW : z ∈ t.retract ∩ W := ⟨hzQ, hzG.1.1⟩
      have hpzV := hpmap.mapsTo hzQW
      rw [t.apply_eq_self_of_mem_retract hzQ, hκ, killOn_eq_self σ fun i hi => ?_, hΓp z hzQW]
      have h1 := hcoordΓ _ hpzV i
      rw [hΓp z hzQW] at h1
      rw [coordsOn_apply, ← h1]
      exact hzσ i hi
  refine ⟨G, tσ, hG, h0G, fun z hz => hz.1, hplus, htσU, hret, ?_⟩
  -- the tangent spaces
  intro y hy a ha haσ
  have hy' : E.toBase 1 y ∈ t.retract ∩ G ∩ {z | ∀ i ∈ σ, (T 0 z).1 i = 0} := hret ▸ hy
  set q := E.toBase 1 y with hq
  have hqQW : q ∈ t.retract ∩ W := ⟨hy'.1.1, hy'.1.2.1.1⟩
  set w := p q with hw
  have hwV : w ∈ V := hpmap.mapsTo hqQW
  have hΓw : Γ w = q := hΓp q hqQW
  have hyt : y ∈ E.lvlSet t.retract 1 := hy'.1.1
  have hyU : y ∈ E.lvlSet R₁.U 1 := tσ.retract_subset hy
  -- `T_yQ = DΓ(w)N` and `p ∘ DΓ(w) = 1`
  have hQW := proposition_2_3_1_one t.isScRetract hW
  obtain ⟨-, hTy, hpD⟩ := tangentSpace_eq_range_graph hQW hV hpmap hΓmap hΓp hpΓ hwV
    (y := y) (by rw [hΓw])
  rw [tangentSpace_inter_isOpen t.isScRetract hW hqQW] at hTy
  have ha' := ha
  rw [hTy] at ha'
  obtain ⟨m, hm⟩ := ha'
  have hpa : p a = m := by rw [← hm, hpD]
  -- `a − m ∈ E_0`, so `m ∈ f_σ` and `κ m = m`
  have hdiff : a - (m : E 0) ∈ minimalSubspaceWith T 0 :=
    hYE (hker _ (by rw [map_sub, hpa, hpN, sub_self]))
  have hmσ : ∀ i ∈ σ, coordsOn T N m i = 0 := fun i hi => by
    have h1 := coord_add_of_mem_zero T (x := (m : E 0)) hdiff i
    rw [add_sub_cancel] at h1
    rw [coordsOn_apply, ← h1]; exact haσ i hi
  have hmκ : κL m = m := killOn_eq_self σ hmσ
  -- `Dt(y)a = a`
  have hDta : scDeriv t.U t y a = a := by
    rw [tangentSpace_eq_range t hyt] at ha
    obtain ⟨b, rfl⟩ := ha
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L b) (t.scDeriv_comp_self hyt)
  have hDt1 : scDeriv R₁.U R₁ y = scDeriv t.U t y :=
    scDeriv_eq_of_eqOn_relOpen R₁.relOpen R₁.isSc1 t.isSc1 subset_rfl (fun u hu => hu.1)
      (fun _ _ => rfl) hyU
  -- `Dg(y)a = κ(p(Dt(y)a)) = m`
  have hDg : scDeriv R₁.U g y a = m := by
    have c := scDeriv_comp_apply_of_isScDomain R₁.isScDomain (isScDomain_univ _) R₁.isSc1
      (op.isScSmooth (isScDomain_univ _)).isSc1 (mapsTo_univ _ _) hyU a
    rw [op.scDeriv_eq (isScDomain_univ _) (mem_univ _)] at c
    change scDeriv R₁.U (op 0 ∘ R₁) y a = m
    rw [← c, hDt1, hDta]
    change κL (p a) = m
    rw [hpa, hmκ]
  -- `g(y) = w`
  have hκw : κL w = w := killOn_eq_self σ fun i hi => by
    rw [coordsOn_apply, ← hcoordΓ w hwV i, hΓw]; exact hy'.2 i hi
  have hlev : levelMap (F := ScBanach.const N) g 1 y = w := by
    apply levelMap_eq_of_toBase_eq
    rw [ScBanach.const_toBase]
    change w = κL (p (t q))
    rw [t.apply_eq_self_of_mem_retract hqQW.1, hκw]
  have c2 := scDeriv_comp_apply_of_isScDomain R₁.isScDomain hV.isScDomain hg.isSc1 hΓs.isSc1 hgV
    hyU a
  rw [hDg, hlev] at c2
  rw [tangentSpace_eq_range tσ hy]
  refine ⟨a, ?_⟩
  change scDeriv R₁.U (Γ ∘ g) y a = a
  rw [← c2, hm]

include hT in
/-- **The corner model of a retraction onto a subset of `f_σ`** (the model `π_σ(…)` of
Proposition 2.5.16 (preprint 2.44), `corner_tameModel`, without tameness): for a retraction `S` with
`S(U) ⊆ f_σ = {λ_i = 0, i ∈ σ}`, the map `π_σ ∘ S ∘ ι_σ` on `ι_σ⁻¹(S.U)` is a retraction of
`C' = [0, ∞)^{n − #σ} ⊕ W` onto `π_σ(S(U))`, sc⁺ if `S` is. -/
theorem exists_cornerModel_retraction (σ : Finset (Fin n)) (S : ScRetraction E C)
    (hSσ : ∀ y ∈ S.retract, ∀ l ∈ σ, (T 0 y).1 l = 0) :
    ∃ S' : ScRetraction ((ScBanach.const (Fin σᶜ.card → ℝ)).prod Wq) (quadrant σᶜ.card Wq 0),
      S'.retract = cornerProj σ T 0 '' S.retract ∧ (S.IsScPlus → S'.IsScPlus) ∧
      MapsTo (cornerIncl σ T 0) S'.U S.U ∧
      ∀ z ∈ S'.U, S' z = cornerProj σ T 0 (S (cornerIncl σ T 0 z)) := by
  classical
  set F := S.retract with hFdef
  have hFS : F ⊆ S.U := S.retract_subset
  obtain ⟨W₀, hW₀, hSW⟩ := S.relOpen.relOpen
  set E' := (ScBanach.const (Fin σᶜ.card → ℝ)).prod Wq with hE'
  set ι := cornerIncl σ T with hι
  set π := cornerProj σ T with hπ
  have hT' : quadrant σᶜ.card Wq 0 = (ScIso.refl E') 0 ⁻¹' quadrant σᶜ.card Wq 0 := by ext; rfl
  have hιC : ∀ z ∈ quadrant σᶜ.card Wq 0, ι 0 z ∈ C := fun z hz => cornerIncl_mem σ T hT hz
  set U' : Set (E' 0) := ι 0 ⁻¹' W₀ ∩ quadrant σᶜ.card Wq 0 with hU'
  have hιU : ∀ z ∈ U', ι 0 z ∈ S.U := fun z hz => by rw [hSW]; exact ⟨hz.1, hιC z hz.2⟩
  have hSιF : ∀ z ∈ U', S (ι 0 z) ∈ F := fun z hz => S.apply_mem_retract (hιU z hz)
  have hιπ : ∀ y ∈ F, ι 0 (π 0 y) = y := fun y hy => cornerIncl_cornerProj σ T (hSσ y hy)
  have hFU' : ∀ y ∈ F, π 0 y ∈ U' := fun y hy => by
    have hyS := hFS hy
    rw [hSW] at hyS
    refine ⟨?_, cornerProj_mem σ T hT hyS.2⟩
    rw [mem_preimage, hιπ y hy]; exact hyS.1
  have hU'rel : IsRelOpenInQuadrant E' (quadrant σᶜ.card Wq 0) U' :=
    ⟨⟨σᶜ.card, Wq, ScIso.refl E', hT'⟩, ι 0 ⁻¹' W₀, hW₀.preimage (ι 0).continuous, rfl⟩
  have hSι : IsScSmooth U' (S ∘ ι 0) :=
    IsScSmooth.comp hU'rel.isScDomain S.isScDomain S.isScSmooth (ι.isScSmooth hU'rel.isScDomain)
      hιU
  have hsm : IsScSmooth U' (π 0 ∘ (S ∘ ι 0)) :=
    IsScSmooth.comp hU'rel.isScDomain (isScDomain_univ _) (π.isScSmooth (isScDomain_univ _)) hSι
      (mapsTo_univ _ _)
  let S' : ScRetraction E' (quadrant σᶜ.card Wq 0) :=
    { U := U'
      toFun := fun z => π 0 (S (ι 0 z))
      relOpen := hU'rel
      mapsTo := fun z hz => hFU' _ (hSιF z hz)
      isScSmooth := hsm
      idem := fun z hz => by
        change π 0 (S (ι 0 (π 0 (S (ι 0 z))))) = π 0 (S (ι 0 z))
        rw [hιπ _ (hSιF z hz), S.apply_eq_self_of_mem_retract (hSιF z hz)] }
  have hS'ret : S'.retract = π 0 '' F := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩; exact ⟨_, hSιF z hz, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨π 0 y, hFU' y hy, ?_⟩
      change π 0 (S (ι 0 (π 0 y))) = π 0 y
      rw [hιπ y hy, S.apply_eq_self_of_mem_retract hy]
  refine ⟨S', hS'ret, fun hS => ?_, hιU, fun _ _ => rfl⟩
  have h1 : IsScPlus U' (S ∘ ι 0) :=
    IsScPlus.comp_isScSmooth hU'rel.isScDomain S.isScDomain hS (ι.isScSmooth hU'rel.isScDomain) hιU
  have h2 : IsScPlus U' (π 0 ∘ (S ∘ ι 0)) :=
    IsScSmooth.comp_isScPlus hU'rel.isScDomain (isScDomain_univ _)
      (π.isScSmooth (isScDomain_univ _)) h1 (mapsTo_univ _ _)
  exact h2

include hT in
/-- **Theorem 4.2.11 (preprint 4.22) (4) in a tame chart centred at the point.**  With the data of
`theorem_4_2_11_chart` (tame `r` onto `O ∋ 0`, sc⁺ `t` onto `Q ∋ 0`, `T₀Q + E_0 = E`, the graph
`Γ : V → Q ∩ W` over `N = T₀Q` with `Γ(v) − v ∈ Y ⊆ E_0`), for every `σ ⊆ {1, …, n}` and every
open `B₀ ∋ 0` there are the faces `F_i ∋ 0` (`i ∈ σ`) of `O` and an open `G ∋ 0`, `G ⊆ W ∩ B₀`,
with:
* **`F_σ` near `0` is a tame retract**: an sc-smooth retraction `S` onto
  `O ∩ G ∩ f_σ = O ∩ G ∩ ⋂_{i ∈ σ} F_i` (`corner_retraction`, restricted to `G`) whose corner model
  `π_σ(O ∩ G ∩ f_σ) ⊆ [0, ∞)^{n − #σ} ⊕ W` is the retract of a **tame** retraction `r'`, with
  `d_{C'}(π_σ y) + #σ = d_C(y)` (`corner_tameModel`, Proposition 2.5.16 (preprint 2.44));
* **`A ∩ F_σ` near `0` is an sc⁺-retract**: `Q ∩ G ∩ f_σ` is the retract of an sc⁺-retraction
  `t_σ`, and its corner model `π_σ(Q ∩ G ∩ f_σ)` is the retract of an sc⁺-retraction `t'` and lies
  in the retract of `r'`;
* **general position in `F_σ`**: at every level-`1` point `y'` of `π_σ(Q ∩ G ∩ f_σ)`, its tangent
  space has in the tangent space of the model of `F_σ` an sc-complement contained in the reduced
  tangent space (Definition 4.2.10 (preprint 4.21) in the corner model, with the presentation `id`).
*Proof*: `T_yQ + E_0 = E` at `y = ι_σ(y')` (`sup_minimalSubspaceWith_eq_top_graph`) gives, for
every `b ∈ ℝ^{n − #σ}`, a `v ∈ T_yQ` with `λ(v) = ι(b)` (zero on `σ`); `v ∈ f_σ`, so `v` is tangent
to `Q_σ` (`exists_scPlus_retraction_corner`), and `π_σ v` is tangent to `π_σ(Q_σ)` at `y'`
(`scDeriv_mem_tangentSpace_of_subset` for `π_σ`), with first component `b`; so
`T_{y'}π_σ(Q_σ) + E'_0 = E'` and `isGeneralPositionRetractAt_of_sup_eq_top` applies in the corner
model. -/
theorem theorem_4_2_11_four_chart {R : ScRetraction E C} (hR : R.IsTameWith T)
    (h0O : (0 : E 0) ∈ R.retract) (t : ScRetraction E C) (ht : t.IsScPlus)
    (htR : t.retract ⊆ R.retract) {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
    (hsup : N ⊔ minimalSubspaceWith T 0 = ⊤) {Y : Submodule ℝ (E 0)}
    (hYE : Y ≤ minimalSubspaceWith T 0) {p : E 0 →L[ℝ] N} (hpN : ∀ x : N, p x = x)
    (hker : ∀ x, p x = 0 → x ∈ Y) {W : Set (E 0)} (hW : IsOpen W) (h0W : (0 : E 0) ∈ W)
    {V : Set N} (hV : IsRelOpenInQuadrant (ScBanach.const N) (Subtype.val ⁻¹' C) V)
    (h0V : (0 : N) ∈ V) {Γ : N → E 0} (hΓs : IsScSmooth (E := ScBanach.const N) (F := E) V Γ)
    (hpΓ : ∀ a ∈ V, p (Γ a) = a) (hΓY : ∀ a ∈ V, Γ a - a ∈ Y)
    (hΓp : ∀ u ∈ t.retract ∩ W, Γ (p u) = u) (hΓ0 : Γ 0 = 0)
    (hpmap : IsScSmoothRetractMap E C (t.retract ∩ W) (ScBanach.const N) (Subtype.val ⁻¹' C) V p)
    (hΓmap : IsScSmoothRetractMap (ScBanach.const N) (Subtype.val ⁻¹' C) V E C (t.retract ∩ W) Γ)
    (σ : Finset (Fin n)) {B₀ : Set (E 0)} (hB₀ : IsOpen B₀) (h0B₀ : (0 : E 0) ∈ B₀) :
    ∃ (Fc : σ → Set (E 0)) (G : Set (E 0)) (S : ScRetraction E C)
      (R' : ScRetraction ((ScBanach.const (Fin σᶜ.card → ℝ)).prod Wq) (quadrant σᶜ.card Wq 0))
      (tσ : ScRetraction E C)
      (t' : ScRetraction ((ScBanach.const (Fin σᶜ.card → ℝ)).prod Wq) (quadrant σᶜ.card Wq 0)),
      (∀ i, R.IsRetractFace (Fc i) ∧ (0 : E 0) ∈ Fc i ∧ Fc i ⊆ coordHyper T i) ∧
      IsOpen G ∧ (0 : E 0) ∈ G ∧ G ⊆ W ∩ B₀ ∧
      S.retract = R.retract ∩ G ∩ {z | ∀ i ∈ σ, (T 0 z).1 i = 0} ∧
      S.retract = R.retract ∩ G ∩ ⋂ i, Fc i ∧
      R'.IsTameWith (ScIso.refl _) ∧ R'.retract = cornerProj σ T 0 '' S.retract ∧
      (∀ y ∈ S.retract,
        degIndex _ (quadrant σᶜ.card Wq 0) (cornerProj σ T 0 y) + σ.card = degIndex E C y) ∧
      tσ.IsScPlus ∧ tσ.retract = t.retract ∩ G ∩ {z | ∀ i ∈ σ, (T 0 z).1 i = 0} ∧
      t'.IsScPlus ∧ t'.retract = cornerProj σ T 0 '' tσ.retract ∧ t'.retract ⊆ R'.retract ∧
      ∀ y' : ((ScBanach.const (Fin σᶜ.card → ℝ)).prod Wq) 1,
        ((ScBanach.const (Fin σᶜ.card → ℝ)).prod Wq).toBase 1 y' ∈ t'.retract →
        IsGeneralPositionRetractAt _ (quadrant σᶜ.card Wq 0) R'.retract t'.retract
          (ScIso.refl _) y' := by
  classical
  -- the faces `F_i` and the corner retraction near `0`
  obtain ⟨Fc, hFc, -, B, hB, h0B, S₀, hSU₀, hSeq₀, hSret1₀, hSret2₀⟩ :=
    corner_retraction σ hT hR h0O (fun i _ => by rw [map_zero]; rfl)
  -- `A ∩ F_σ` near `0`
  obtain ⟨G, tσ, hG, h0G, hGWB, hplus, -, htσret, htan⟩ :=
    exists_scPlus_retraction_corner hT t ht hsup hYE hpN hker hW h0W hV h0V hΓs hpΓ hΓY hΓp hΓ0
      hpmap hΓmap σ (hB.inter hB₀) ⟨h0B, h0B₀⟩
  -- `F_σ` near `0`, restricted to `G`
  set S := S₀.restrict hG with hSdef
  have hGB : G ⊆ B := fun z hz => (hGWB hz).2.1
  have hSret1 : S.retract = R.retract ∩ G ∩ {z | ∀ i ∈ σ, (T 0 z).1 i = 0} := by
    rw [hSdef, S₀.restrict_retract, hSret1₀]
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨h.1.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨⟨h.1.1, hGB h.1.2⟩, h.2⟩, h.1.2⟩⟩
  have hSret2 : S.retract = R.retract ∩ G ∩ ⋂ i, Fc i := by
    rw [hSdef, S₀.restrict_retract, hSret2₀]
    ext z
    simp only [mem_inter_iff]
    exact ⟨fun h => ⟨⟨h.1.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨⟨h.1.1, hGB h.1.2⟩, h.2⟩, h.1.2⟩⟩
  have hSU : S.U ⊆ R.U := fun z hz => hSU₀ hz.1
  have hSeq : EqOn S (R ∘ cornerKill T σ 0) S.U := fun z hz => hSeq₀ hz.1
  have hSO : S.retract ⊆ R.retract := by rw [hSret1]; exact fun y hy => hy.1.1
  have hSσ : ∀ y ∈ S.retract, ∀ l ∈ σ, (T 0 y).1 l = 0 := by rw [hSret1]; exact fun y hy => hy.2
  obtain ⟨R', hR'tame, hR'ret, hdeg⟩ := corner_tameModel σ hT hR S hSσ hSO hSU hSeq
  have htσσ : ∀ y ∈ tσ.retract, ∀ l ∈ σ, (T 0 y).1 l = 0 := by
    rw [htσret]; exact fun y hy => hy.2
  obtain ⟨t', ht'ret, ht'plus, -, -⟩ := exists_cornerModel_retraction hT σ tσ htσσ
  have ht'p := ht'plus hplus
  have hsub : tσ.retract ⊆ S.retract := by
    rw [htσret, hSret1]
    rintro z ⟨⟨hzQ, hzG⟩, hzσ⟩
    exact ⟨⟨htR hzQ, hzG⟩, hzσ⟩
  have ht'R' : t'.retract ⊆ R'.retract := by rw [ht'ret, hR'ret]; exact image_mono hsub
  refine ⟨Fc, G, S, R', tσ, t', hFc, hG, h0G, fun z hz => ⟨(hGWB hz).1, (hGWB hz).2.2⟩, hSret1,
    hSret2, hR'tame, hR'ret, hdeg, hplus, htσret, ht'p, ht'ret, ht'R', fun y' hy' => ?_⟩
  -- general position in the corner model
  let E' := (ScBanach.const (Fin σᶜ.card → ℝ)).prod Wq
  set ι := cornerIncl σ T with hι
  set π := cornerProj σ T with hπ
  have hT' : quadrant σᶜ.card Wq 0 = (ScIso.refl E') 0 ⁻¹' quadrant σᶜ.card Wq 0 := by ext; rfl
  have hy's : y' ∈ E'.smoothLvl 1 := lemma_4_1_7_i ht'p hy'
  have hy'2 := hy'
  rw [ht'ret] at hy'2
  obtain ⟨q₀, hq₀, hq₀y⟩ := hy'2
  have hιq : ι 0 (π 0 q₀) = q₀ := cornerIncl_cornerProj σ T (htσσ q₀ hq₀)
  set y : E 1 := ι 1 y' with hydef
  have hy : E.toBase 1 y = q₀ := by rw [hydef, ι.toBase_comm, ← hq₀y, hιq]
  have hyσ : y ∈ E.lvlSet tσ.retract 1 := by rw [ScBanach.mem_lvlSet, hy]; exact hq₀
  have hq₀' := hq₀
  rw [htσret] at hq₀'
  have hq₀QW : q₀ ∈ t.retract ∩ W := ⟨hq₀'.1.1, (hGWB hq₀'.1.2).1⟩
  have hwV : p q₀ ∈ V := hpmap.mapsTo hq₀QW
  have hΓw : Γ (p q₀) = q₀ := hΓp q₀ hq₀QW
  have hyt : y ∈ E.lvlSet t.retract 1 := by rw [ScBanach.mem_lvlSet, hy]; exact hq₀QW.1
  set NQ : Submodule ℝ (E 0) := LinearMap.range (scDeriv t.U t y : E 0 →ₗ[ℝ] E 0) with hNQdef
  have hNQ : (NQ : Set (E 0)) = tangentSpace E C t.retract y :=
    (tangentSpace_eq_coe_submodule t hyt).symm
  have hsupy := sup_minimalSubspaceWith_eq_top_graph T t.isScRetract hsup hYE hpN hker hW hV hpmap
    hΓmap hΓp hpΓ hwV (y := y) (by rw [hy, hΓw]) hNQ
  have hy't : y' ∈ E'.lvlSet t'.retract 1 := hy'
  set N'' : Submodule ℝ (E' 0) := LinearMap.range (scDeriv t'.U t' y' : E' 0 →ₗ[ℝ] E' 0)
    with hN''def
  have : FiniteDimensional ℝ N'' := lemma_4_1_7_ii ht'p hy'
  have hN'' : (N'' : Set (E' 0)) = tangentSpace E' (quadrant σᶜ.card Wq 0) t'.retract y' :=
    (tangentSpace_eq_coe_submodule t' hy't).symm
  have hN''s : N'' ≤ E'.smooth :=
    (E'.proposition_1_1_7_iff N'').1 (t'.isScSplitting_range_scDeriv hy't hy's).1
  refine isGeneralPositionRetractAt_of_sup_eq_top (ScIso.refl E') hT' hR'tame t'.isScRetract ht'R'
    hy't hy's hN'' hN''s ?_
  rw [eq_top_iff]
  intro z' _
  obtain ⟨v, hv⟩ := coordsOn_surjective T hsupy (cornerInsertL σ z'.1)
  have hvT : (T 0 (v : E 0)).1 = cornerInsertL σ z'.1 := hv
  have hvσ : ∀ i ∈ σ, (T 0 (v : E 0)).1 i = 0 := fun i hi => by
    rw [hvT, cornerInsertL_apply_mem σ _ hi]
  have hvQ : (v : E 0) ∈ tangentSpace E C t.retract y := by rw [← hNQ]; exact v.2
  have hvQσ : (v : E 0) ∈ tangentSpace E C tσ.retract y := htan y (by rw [hy]; exact hq₀) _ hvQ hvσ
  -- `π_σ v` is tangent to `π_σ(Q_σ)` at `y'`
  have hπv : π 0 v ∈ N'' := by
    have hFQ : MapsTo (π 0) tσ.retract (π 0 '' tσ.retract) := mapsTo_image _ _
    have hQ' : IsScRetract E' (quadrant σᶜ.card Wq 0) (π 0 '' tσ.retract) := ⟨t', ht'ret⟩
    have hπs : IsScSmooth tσ.U (π 0 ∘ tσ) :=
      IsScSmooth.comp tσ.isScDomain (isScDomain_univ _) (π.isScSmooth (isScDomain_univ _))
        tσ.isScSmooth (mapsTo_univ _ _)
    have h := scDeriv_mem_tangentSpace_of_subset tσ hπs tσ.isScRetract hQ' subset_rfl hFQ hyσ hvQσ
    have hlev : levelMap (π 0 ∘ tσ) 1 y = y' := by
      apply levelMap_eq_of_toBase_eq
      rw [hy]
      change E'.toBase 1 y' = π 0 (tσ q₀)
      rw [tσ.apply_eq_self_of_mem_retract hq₀, hq₀y]

    have hD : scDeriv tσ.U (π 0 ∘ tσ) y v = π 0 v := by
      have c := scDeriv_comp_apply_of_isScDomain tσ.isScDomain (isScDomain_univ _) tσ.isSc1
        (π.isScSmooth (isScDomain_univ _)).isSc1 (mapsTo_univ _ _) (tσ.lvlSet_retract_subset 1 hyσ)
        (v : E 0)
      rw [π.scDeriv_eq (isScDomain_univ _) (mem_univ _)] at c
      rw [← c]
      congr 1
      have hv' := hvQσ
      rw [tangentSpace_eq_range tσ hyσ] at hv'
      obtain ⟨b, hb⟩ := hv'
      rw [← hb]
      exact congrArg (fun L : E 0 →L[ℝ] E 0 => L b) (tσ.scDeriv_comp_self hyσ)
    rw [hlev, hD, ← ht'ret] at h
    rw [← SetLike.mem_coe, hN'']
    exact h
  have hz'0 : z' - π 0 v ∈ minimalSubspaceWith (ScIso.refl E') 0 := by
    rw [mem_minimalSubspaceWith_zero]
    intro i
    change (z' - π 0 v).1 i = 0
    rw [Prod.fst_sub, Pi.sub_apply, hπ, cornerProj_apply, hvT, cornerRemoveL_cornerInsertL,
      sub_self]
  have : z' = π 0 v + (z' - π 0 v) := by abel
  rw [this]
  exact Submodule.add_mem_sup hπv hz'0

end CornerSubmanifold

/-! ### Theorem 4.2.11 (preprint 4.22) (1)–(3) on the M-polyfold -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}


/-! ### sc⁺-retractions on open subsets from sc⁺-retractions in a chart -/

/-- **An sc⁺-retraction in a chart is an sc⁺-retraction on an open subset of the M-polyfold**
(Definition 4.1.4 (preprint 4.4) read in a chart; the converse of `SubmanifoldData.isScSmoothRetractMap_lift`): for
a chart `χ` and an sc⁺-retraction `τ` of the model with `τ(U) ⊆ O`, the map `s = χ⁻¹ ∘ τ ∘ χ` is an
sc⁺-retraction on the open set `V = χ⁻¹(τ.U)` with `s(V) = χ⁻¹(τ(U))`.  *Proof*: sc-smoothness of
`s` and of `1₀¹ ∘ s` are read in the charts `χ` of `X` and `levelChart χ` of `X¹`, where they are
`τ` and its lift `U → E¹` (`levelChart_toLevelOne`). -/
theorem isScPlusRetractionOn_of_chart {χ : MChart X} (hχ : P.IsChart χ)
    (τ : ScRetraction χ.model.E χ.model.C) (hτ : τ.IsScPlus) (hτO : τ.retract ⊆ χ.model.O) :
    IsOpen (χ.source ∩ χ ⁻¹' τ.U) ∧
      P.IsScPlusRetractionOn (χ.symm ∘ τ ∘ χ) (χ.source ∩ χ ⁻¹' τ.U) ∧
      (χ.symm ∘ τ ∘ χ) '' (χ.source ∩ χ ⁻¹' τ.U) = χ.source ∩ χ ⁻¹' τ.retract := by
  set V := χ.source ∩ χ ⁻¹' τ.U with hVdef
  have hVo : IsOpen V := by
    obtain ⟨O', hO', hUO'⟩ := τ.relOpen.relOpen
    have : V = χ.source ∩ χ ⁻¹' O' := by
      ext y
      refine ⟨fun hy => ⟨hy.1, (hUO' ▸ hy.2 : χ y ∈ O' ∩ χ.model.C).1⟩, fun hy => ⟨hy.1, ?_⟩⟩
      rw [mem_preimage, hUO']; exact ⟨hy.2, χ.apply_mem_C hy.1⟩
    rw [this]
    exact χ.continuousOn_toFun.isOpen_inter_preimage χ.isOpen_source hO'
  set s := χ.symm ∘ τ ∘ χ with hsdef
  have hτO' : ∀ x ∈ V, τ (χ x) ∈ χ.model.O := fun x hx => hτO (τ.apply_mem_retract hx.2)
  have hsrc : ∀ x ∈ V, s x ∈ χ.source := fun x hx => χ.symm_mapsTo (hτO' x hx)
  have hχs : ∀ x ∈ V, χ (s x) = τ (χ x) := fun x hx => χ.apply_symm_apply (hτO' x hx)
  have hmaps : MapsTo s V V := fun x hx =>
    ⟨hsrc x hx, by rw [mem_preimage, hχs x hx]; exact τ.mapsTo hx.2⟩
  have hlev1 : ∀ x ∈ V, s x ∈ P.levelSet 1 := fun x hx => by
    rw [P.mem_levelSet_iff hχ (hsrc x hx), hχs x hx]
    obtain ⟨y, hy⟩ := (χ.model.E.mem_smooth_iff).1 (lemma_4_1_7_i hτ (τ.apply_mem_retract hx.2)) 1
    exact ⟨y, hy⟩
  have hcont : ContinuousOn s V :=
    χ.continuousOn_invFun.comp ((τ.isSc1.isSc0.continuousOn_base).comp
      (χ.continuousOn_toFun.mono fun _ hy => hy.1) fun _ hy => hy.2) fun x hx => hτO' x hx
  have himVU : χ '' V ⊆ τ.U := by rintro _ ⟨x, hx, rfl⟩; exact hx.2
  have hrep : EqOn τ (χ ∘ s ∘ χ.symm) (χ '' V) := by
    rintro _ ⟨x, hx, rfl⟩
    show τ (χ x) = χ (s (χ.symm (χ x)))
    rw [χ.symm_apply_apply hx.1]
    exact (hχs x hx).symm
  have hsmooth : P.IsScSmoothOn P s V := by
    refine IsScSmoothOn.of_exists_charts hVo hcont ?_
    intro x hx
    refine ⟨χ, χ, V, hχ, hχ, hVo, hx, fun y hy => ⟨hy, hy.1⟩, hsrc, ?_⟩
    refine (IsScSmooth.isScSmoothRetractMap_of_subset τ.relOpen τ.isScSmooth himVU ?_).congr hrep
    rintro _ ⟨y, hy, rfl⟩; exact hτO' y hy
  refine ⟨hVo, ⟨hsmooth, hmaps, fun x hx => ?_, hlev1, fun x₀ => ?_⟩, ?_⟩
  · -- `s ∘ s = s`
    change χ.symm (τ (χ (s x))) = χ.symm (τ (χ x))
    rw [hχs x hx, τ.idem _ hx.2]
  · -- `1₀¹ ∘ s` is sc-smooth: in the charts `χ`, `levelChart χ` it is the lift of `τ`
    have hL := P.shift_isChart hχ x₀
    have hmapsL : MapsTo (P.toLevelOne x₀ ∘ s) V (levelChart hχ x₀).source := fun x hx => by
      change P.levelVal 1 (P.toLevelOne x₀ (s x)) ∈ χ.source
      rw [levelVal_toLevelOne x₀ (hlev1 x hx)]; exact hsrc x hx
    have hlift : ∀ x ∈ V, levelChart hχ x₀ (P.toLevelOne x₀ (s x)) =
        χ.model.E.liftOne (τ (χ x)) := fun x hx => by
      rw [levelChart_toLevelOne hχ x₀ x₀ (hlev1 x hx), hχs x hx]
    have hliftC : ContinuousOn (χ.model.E.liftOne ∘ τ) τ.U :=
      hτ.isScSmooth_lift.isSc1.isSc0.continuousOn_base
    have hliftO : ∀ z ∈ τ.U, χ.model.E.liftOne (τ z) ∈ (levelChart hχ x₀).model.O := fun z hz => by
      change χ.model.E.toBase 1 (χ.model.E.liftOne (τ z)) ∈ χ.model.O
      rw [hτ.toBase_lift hz]; exact hτO (τ.apply_mem_retract hz)
    have hcont1 : ContinuousOn (P.toLevelOne x₀ ∘ s) V := by
      refine ((levelChart hχ x₀).continuousOn_invFun.comp (hliftC.comp
        (χ.continuousOn_toFun.mono fun _ hy => hy.1) fun _ hy => hy.2)
        fun x hx => hliftO _ hx.2).congr fun x hx => ?_
      show P.toLevelOne x₀ (s x) = (levelChart hχ x₀).symm (χ.model.E.liftOne (τ (χ x)))
      rw [← hlift x hx]
      exact ((levelChart hχ x₀).symm_apply_apply (hmapsL hx)).symm
    refine IsScSmoothOn.of_exists_charts hVo hcont1 ?_
    intro x hx
    refine ⟨χ, levelChart hχ x₀, V, hχ, hL, hVo, hx, fun y hy => ⟨hy, hy.1⟩, hmapsL, ?_⟩
    have hrep1 : EqOn (χ.model.E.liftOne ∘ τ)
        (levelChart hχ x₀ ∘ (P.toLevelOne x₀ ∘ s) ∘ χ.symm) (χ '' V) := by
      rintro _ ⟨y, hy, rfl⟩
      show χ.model.E.liftOne (τ (χ y)) = levelChart hχ x₀ (P.toLevelOne x₀ (s (χ.symm (χ y))))
      rw [χ.symm_apply_apply hy.1]
      exact (hlift y hy).symm
    refine (IsScSmooth.isScSmoothRetractMap_of_subset τ.relOpen hτ.isScSmooth_lift himVU ?_).congr
      hrep1
    rintro _ ⟨y, hy, rfl⟩; exact hliftO _ hy.2
  · -- the image
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hsrc x hx, by rw [mem_preimage, hχs x hx]; exact τ.apply_mem_retract hx.2⟩
    · rintro ⟨hy, hyr⟩
      refine ⟨y, ⟨hy, τ.retract_subset hyr⟩, ?_⟩
      change χ.symm (τ (χ y)) = y
      rw [τ.apply_eq_self_of_mem_retract hyr, χ.symm_apply_apply hy]


/-- The preimage under a chart `ψ` of `G ∩ ⋂_i F_i` (the germ `F_σ` of an intersection of local
faces, `ψ⁻¹(G ∩ ⋂_{i ∈ σ} F_i)`). -/
def _root_.Polyfold.MChart.cornerPreimage (ψ : MChart X) (G : Set (ψ.model.E 0)) {ι : Type*}
    (F : ι → Set (ψ.model.E 0)) : Set X :=
  {y | y ∈ ψ.source ∧ ψ y ∈ G ∧ ∀ i, ψ y ∈ F i}

/-- **Theorem 4.2.11 (preprint 4.22) (4), for one `σ`, from the chart data** (the M-polyfold form of
`theorem_4_2_11_four_chart`): in a tame chart `ψ` centred at `x` with the data of
`theorem_4_2_11_chart` for the chart retraction `t` of `A`, for `σ ⊆ {1, …, n}` there are the faces
`F_i ∋ 0` (`i ∈ σ`) of the model and an open `G ∋ 0` such that `F_σ = ψ⁻¹(G ∩ ⋂_{i ∈ σ} F_i)`
(which contains `x` and lies in the domain `W` of the submanifold chart) is a sub-M-polyfold of
`X`, **tame**, with `d_{F_σ} + #σ = d_X` (Proposition 2.5.16 (preprint 2.44)), and **`A ∩ F_σ` is a smooth
finite-dimensional submanifold of `F_σ`, in general position at each of its points, and tame**.
*Proof*: the chart of `F_σ` is the face chart `π_σ ∘ ψ` modelled on the tame corner model;
`A ∩ F_σ` is in it the retract of the sc⁺-retraction `t'` of `theorem_4_2_11_four_chart`, which
`isScPlusRetractionOn_of_chart` turns into an sc⁺-retraction on an open subset of `F_σ`; general
position is that of `theorem_4_2_11_four_chart` read in this chart; tameness is Theorem 4.2.7 (preprint 4.18) for the
tame M-polyfold `F_σ`, good position following from general position
(`IsGeneralPositionRetractAt.isGoodPositionRetractAt`). -/
theorem theorem_4_2_11_four_of_chart {A : Set X} {ψ : MChart X} (hψ : P.IsChart ψ) {x : X}
    (hxψ : x ∈ ψ.source) (hψ0 : ψ x = 0) {R : ScRetraction ψ.model.E ψ.model.C}
    (hR : R.retract = ψ.model.O) {n : ℕ} {Wq : ScBanach}
    {T : ScIso ψ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)}
    (hT : ψ.model.C = T 0 ⁻¹' quadrant n Wq 0) (hRT : R.IsTameWith T)
    (d : P.SubmanifoldData A) (t : ScRetraction ψ.model.E ψ.model.C)
    (ht : t.retract = ψ '' (d.toSubData.shrink ψ ∩ A)) (htp : t.IsScPlus)
    {N : Submodule ℝ (ψ.model.E 0)} [FiniteDimensional ℝ N]
    (hsup : N ⊔ minimalSubspaceWith T 0 = ⊤) {Y : Submodule ℝ (ψ.model.E 0)}
    (hYE : Y ≤ minimalSubspaceWith T 0) {p : ψ.model.E 0 →L[ℝ] N} (hpN : ∀ z : N, p z = z)
    (hker : ∀ z, p z = 0 → z ∈ Y) {W : Set (ψ.model.E 0)} (hW : IsOpen W)
    (h0W : (0 : ψ.model.E 0) ∈ W) {V : Set N}
    (hV : IsRelOpenInQuadrant (ScBanach.const N) (Subtype.val ⁻¹' ψ.model.C) V)
    (h0V : (0 : N) ∈ V) {Γ : N → ψ.model.E 0}
    (hΓs : IsScSmooth (E := ScBanach.const N) (F := ψ.model.E) V Γ)
    (hpΓ : ∀ a ∈ V, p (Γ a) = a) (hΓY : ∀ a ∈ V, Γ a - a ∈ Y)
    (hΓp : ∀ u ∈ t.retract ∩ W, Γ (p u) = u) (hΓ0 : Γ 0 = 0)
    (hpmap : IsScSmoothRetractMap ψ.model.E ψ.model.C (t.retract ∩ W) (ScBanach.const N)
      (Subtype.val ⁻¹' ψ.model.C) V p)
    (hΓmap : IsScSmoothRetractMap (ScBanach.const N) (Subtype.val ⁻¹' ψ.model.C) V ψ.model.E
      ψ.model.C (t.retract ∩ W) Γ)
    (σ : Finset (Fin n)) :
    ∃ (Fc : σ → Set (ψ.model.E 0)) (G : Set (ψ.model.E 0)),
      (∀ i, R.IsRetractFace (Fc i) ∧ (0 : ψ.model.E 0) ∈ Fc i ∧ Fc i ⊆ coordHyper T i) ∧
      IsOpen G ∧ (0 : ψ.model.E 0) ∈ G ∧ G ⊆ W ∧
      x ∈ ψ.cornerPreimage G Fc ∧ ψ.cornerPreimage G Fc ⊆ d.toSubData.shrink ψ ∧
      ∃ hF : P.IsSubMPolyfold (ψ.cornerPreimage G Fc),
        haveI := P.paracompactSpace_subtype (ψ.cornerPreimage G Fc)
        (subPolyfold hF).IsTame ∧
        (∀ a, (subPolyfold hF).degIndex a + σ.card = P.degIndex a) ∧
        (subPolyfold hF).IsSmoothSubmanifold {b | (b : X) ∈ A} ∧
        (∀ b : ψ.cornerPreimage G Fc, (b : X) ∈ A →
          (subPolyfold hF).IsGeneralPositionAt {b | (b : X) ∈ A} b) ∧
        haveI := (subPolyfold hF).paracompactSpace_subtype {b | (b : X) ∈ A}
        (subPolyfold hF).IsTameSubmanifold {b | (b : X) ∈ A} := by
  classical
  -- `ψ(W_d) = O ∩ K`
  obtain ⟨K, hK, hKeq⟩ := ψ.exists_isOpen_image_eq (d.toSubData.shrink_subset_source ψ)
    (d.toSubData.isOpen_shrink ψ)
  have htR : t.retract ⊆ R.retract := by
    rw [ht, hR]; exact ψ.image_subset_model fun _ hy => d.toSubData.shrink_subset_source ψ hy.1
  have h0t : (0 : ψ.model.E 0) ∈ t.retract := by
    have := (hΓmap.mapsTo h0V).1; rwa [hΓ0] at this
  have h0K : (0 : ψ.model.E 0) ∈ K := by
    have h0t' := h0t
    rw [ht] at h0t'
    obtain ⟨y, hy, hy0⟩ := h0t'
    have : (0 : ψ.model.E 0) ∈ ψ '' d.toSubData.shrink ψ := ⟨y, hy.1, hy0⟩
    rw [hKeq] at this; exact this.2
  have h0O : (0 : ψ.model.E 0) ∈ R.retract := htR h0t
  obtain ⟨Fc, G, S, R', tσ, t', hFc, hG, h0G, hGWK, hSret1, hSret2, hR'tame, hR'ret, hdeg, -,
    htσret, ht'p, ht'ret, ht'R', hgen'⟩ :=
    theorem_4_2_11_four_chart hT hRT h0O t htp htR hsup hYE hpN hker hW h0W hV h0V hΓs hpΓ hΓY
      hΓp hΓ0 hpmap hΓmap σ hK h0K
  set Fσ := ψ.cornerPreimage G Fc with hFσ
  have hψFσ : ψ '' Fσ = S.retract := by
    rw [hSret2]
    ext z
    constructor
    · rintro ⟨y, ⟨hy, hyG, hyF⟩, rfl⟩
      exact ⟨⟨by rw [hR]; exact ψ.mapsTo_model y hy, hyG⟩, mem_iInter.2 hyF⟩
    · rintro ⟨⟨hzO, hzG⟩, hzF⟩
      have hzO' : z ∈ ψ.model.O := by rw [← hR]; exact hzO
      refine ⟨ψ.symm z, ⟨ψ.symm_mapsTo hzO', ?_, ?_⟩, ψ.apply_symm_apply hzO'⟩
      · rw [ψ.apply_symm_apply hzO']; exact hzG
      · intro i; rw [ψ.apply_symm_apply hzO']; exact mem_iInter.1 hzF i
  have hxF : x ∈ Fσ := ⟨hxψ, by rw [hψ0]; exact h0G, fun i => by rw [hψ0]; exact (hFc i).2.1⟩
  have hFshrink : Fσ ⊆ d.toSubData.shrink ψ := fun y hy => by
    have : ψ y ∈ ψ '' d.toSubData.shrink ψ := by
      rw [hKeq]; exact ⟨ψ.mapsTo_model y hy.1, (hGWK hy.2.1).2⟩
    obtain ⟨y', hy', hyy'⟩ := this
    have := ψ.toPartialEquiv.injOn (d.toSubData.shrink_subset_source ψ hy') hy.1 hyy'
    rw [← this]; exact hy'
  refine ⟨Fc, G, hFc, hG, h0G, fun z hz => (hGWK hz).1, hxF, hFshrink, ?_⟩
  -- `F_σ` is a sub-M-polyfold
  have hSO : S.retract ⊆ ψ.model.O := by rw [hSret1, ← hR]; exact fun z hz => hz.1.1
  have hFψ : Fσ ∩ ψ.source = Fσ := inter_eq_left.2 fun y hy => hy.1
  have hF : P.IsSubMPolyfold Fσ := by
    refine P.isSubMPolyfold_of_local ?_
    intro a ha
    exact ⟨ψ, hψ, ha.1, S, univ, isOpen_univ, mem_univ _, hSO, by
      rw [inter_univ, inter_univ, hFψ, hψFσ]⟩
  refine ⟨hF, ?_⟩
  have : ParacompactSpace Fσ := P.paracompactSpace_subtype Fσ
  -- the face chart `π_σ ∘ ψ` of `F_σ`
  set ι := cornerIncl σ T with hι
  set π := cornerProj σ T with hπ
  set V₁ : Set X := ψ.source ∩ ψ ⁻¹' G with hV₁
  have hV₁o : IsOpen V₁ := ψ.continuousOn_toFun.isOpen_inter_preimage ψ.isOpen_source hG
  have hFV₁ : Fσ ⊆ V₁ := fun y hy => ⟨hy.1, hy.2.1⟩
  have hFV : ψ '' (Fσ ∩ V₁) = S.retract := by
    rw [inter_eq_left.2 hFV₁, hψFσ]
  have hSσ : ∀ y ∈ S.retract, ∀ l ∈ σ, (T 0 y).1 l = 0 := by
    rw [hSret1]; exact fun y hy => hy.2
  have hιπ : ∀ y ∈ ψ '' (Fσ ∩ V₁), ι 0 (π 0 y) = y := fun y hy => by
    rw [hFV] at hy; exact cornerIncl_cornerProj σ T (hSσ y hy)
  have hπι : ∀ z, π 0 (ι 0 z) = z := cornerProj_cornerIncl σ T
  have hR'O : R'.retract = π 0 '' (ψ '' (Fσ ∩ V₁)) := by rw [hR'ret, hFV]
  have hret : IsScRetract _ (quadrant σᶜ.card Wq 0) (π 0 '' (ψ '' (Fσ ∩ V₁))) := ⟨R', hR'O⟩
  set χ := faceChart ⟨x, hxF⟩ ψ V₁ (quadrant σᶜ.card Wq 0) ι π hV₁o (fun _ h => h.1) hιπ hπι hret
    with hχ
  have hχQ : (subPolyfold hF).IsChart χ :=
    isChart_subPolyfold_of_compatible hF hψ (fun _ hy => hy.1) fun d' b₀ =>
      faceChart_compatible_subChart hψ hV₁o (fun _ h => h.1) hιπ hπι hret d' b₀
  have hsrc : ∀ a : Fσ, a ∈ χ.source := fun a => show (a : X) ∈ V₁ from ⟨a.2.1, a.2.2.1⟩
  have hχa : ∀ a : Fσ, χ a = π 0 (ψ a) := fun _ => rfl
  have hT' : quadrant σᶜ.card Wq 0 =
      (ScIso.refl ((ScBanach.const (Fin σᶜ.card → ℝ)).prod Wq)) 0 ⁻¹' quadrant σᶜ.card Wq 0 := by
    ext; rfl
  have hχO : χ.model.O = π 0 '' (ψ '' (Fσ ∩ V₁)) := rfl
  have hFtame : (subPolyfold hF).IsTame :=
    isTame_of_forall_exists_chart _ fun a => ⟨χ, hχQ, hsrc a, R', hR'O, hR'tame.isTame hT'⟩
  have hdegF : ∀ a : Fσ, (subPolyfold hF).degIndex a + σ.card = P.degIndex a := fun a => by
    rw [(subPolyfold hF).degIndex_eq_chartDegIndex_of_isTameWith hχQ R' hR'O hT' hR'tame (hsrc a),
      P.degIndex_eq_chartDegIndex_of_isTameWith hψ R hR hT hRT a.2.1]
    have haS : ψ a ∈ S.retract := by rw [← hψFσ]; exact ⟨a, a.2, rfl⟩
    exact hdeg _ haS
  -- `A ∩ F_σ` in the chart `χ`: the retract of `t'`
  set Aσ : Set Fσ := {b | (b : X) ∈ A} with hAσ
  have ht'O : t'.retract ⊆ χ.model.O := by rw [hχO, ← hR'O]; exact ht'R'
  have hmemA : ∀ b : Fσ, χ b ∈ t'.retract ↔ (b : X) ∈ A := by
    intro b
    have hbS : ψ b ∈ S.retract := by rw [← hψFσ]; exact ⟨b, b.2, rfl⟩
    have hbσ := hSσ _ hbS
    rw [hχa, ht'ret, htσret]
    constructor
    · rintro ⟨q, ⟨⟨hqQ, -⟩, hqσ⟩, hqb⟩
      have hψb : ψ b = q := by
        rw [← cornerIncl_cornerProj σ T hbσ, ← hqb, cornerIncl_cornerProj σ T hqσ]
      rw [ht] at hqQ
      obtain ⟨y, hy, hyq⟩ := hqQ
      have := ψ.toPartialEquiv.injOn (d.toSubData.shrink_subset_source ψ hy.1) b.2.1
        (hyq.trans hψb.symm)
      rw [← this]; exact hy.2
    · intro hbA
      refine ⟨ψ b, ⟨⟨?_, b.2.2.1⟩, hbσ⟩, rfl⟩
      rw [ht]; exact ⟨b, ⟨hFshrink b.2, hbA⟩, rfl⟩
  obtain ⟨hVo, hplusOn, himage⟩ := isScPlusRetractionOn_of_chart hχQ t' ht'p ht'O
  have hAV : ∀ b ∈ Aσ, b ∈ χ.source ∩ χ ⁻¹' t'.U := fun b hb =>
    ⟨hsrc b, t'.retract_subset ((hmemA b).2 hb)⟩
  have himage' : (χ.symm ∘ t' ∘ χ) '' (χ.source ∩ χ ⁻¹' t'.U) =
      Aσ ∩ (χ.source ∩ χ ⁻¹' t'.U) := by
    refine himage.trans ?_
    ext b
    constructor
    · rintro ⟨hb, hbr⟩; exact ⟨(hmemA b).1 hbr, hb, t'.retract_subset hbr⟩
    · rintro ⟨hbA, hbV⟩; exact ⟨hbV.1, (hmemA b).2 hbA⟩
  let d' : (subPolyfold hF).SubmanifoldData Aσ := ⟨_, _, hVo, hplusOn, himage'⟩
  have hAσsub : (subPolyfold hF).IsSmoothSubmanifold Aσ := fun b hb =>
    ⟨_, hVo, hAV b hb, _, hplusOn, himage'⟩
  have hχA : χ '' (d'.toSubData.shrink χ ∩ Aσ) = t'.retract := by
    rw [inter_eq_right.2 fun b hb => d'.toSubData.mem_shrink χ hb (hAV b hb) (hsrc b)]
    ext z
    constructor
    · rintro ⟨b, hb, rfl⟩; exact (hmemA b).2 hb
    · intro hz
      have hzO := ht'O hz
      refine ⟨χ.symm z, (hmemA _).1 ?_, χ.apply_symm_apply hzO⟩
      rw [χ.apply_symm_apply hzO]; exact hz
  -- general position in `F_σ`
  have hgenF : ∀ b : Fσ, (b : X) ∈ A → (subPolyfold hF).IsGeneralPositionAt Aσ b := by
    intro b hb
    have hbr : χ b ∈ t'.retract := (hmemA b).2 hb
    obtain ⟨y', hy', -⟩ := exists_smoothLvl_one_of_mem_smooth (lemma_4_1_7_i ht'p hbr)
    refine ⟨hb, d', χ, σᶜ.card, Wq, ScIso.refl _, y', hAV b hb, hχQ, hsrc b, hT', hy', ?_⟩
    have := hgen' y' (by rw [hy']; exact hbr)
    show IsGeneralPositionRetractAt _ _ χ.model.O (χ '' (d'.toSubData.shrink χ ∩ Aσ))
      (ScIso.refl _) y'
    rw [hχA, hχO, ← hR'O]
    exact this
  -- tameness of `A ∩ F_σ` (Theorem 4.2.7 (preprint 4.18) in `F_σ`)
  have : ParacompactSpace Aσ := (subPolyfold hF).paracompactSpace_subtype Aσ
  have hgoodF : ∀ b ∈ Aσ, (subPolyfold hF).IsGoodPositionAt Aσ b := by
    intro b hb
    have hbr : χ b ∈ t'.retract := (hmemA b).2 hb
    obtain ⟨y', hy', hy's⟩ := exists_smoothLvl_one_of_mem_smooth (lemma_4_1_7_i ht'p hbr)
    refine ⟨hb, d', χ, σᶜ.card, Wq, ScIso.refl _, y', hAV b hb, hχQ, hsrc b, hT', hy', ?_⟩
    have hgp' := hgen' y' (by rw [hy']; exact hbr)
    have hy'R : y' ∈ ((ScBanach.const (Fin σᶜ.card → ℝ)).prod Wq).lvlSet R'.retract 1 := by
      rw [ScBanach.mem_lvlSet, hy']; exact ht'R' hbr
    have := hgp'.isGoodPositionRetractAt (ScIso.refl _) hR'tame hy'R hy's
    show IsGoodPositionRetractAt _ _ χ.model.O (χ '' (d'.toSubData.shrink χ ∩ Aσ))
      (ScIso.refl _) y'
    rw [hχA, hχO, ← hR'O]
    exact this
  exact ⟨hFtame, hdegF, hAσsub, hgenF, (theorem_4_2_7 hFtame hAσsub hgoodF).2⟩

/-- **Theorem 4.2.11 (preprint 4.22) (Local structure of smooth submanifolds).**  Let `X` be a tame M-polyfold,
`A ⊆ X` a smooth finite-dimensional submanifold (Definition 4.2.1 (preprint 4.13)) and `x ∈ A` a point at which `A`
is in general position (Definition 4.2.10 (preprint 4.21)).  Then there are a tame chart `ψ : V → O` of `X` with
`ψ(x) = 0` (tame retraction `r` onto `O`, presentation `T : E ≅ ℝⁿ ⊕ W` of the partial quadrant)
and an open neighbourhood `U ⊆ V` of `x` such that:
(1) `d_X(x) = n`, the number of half-line coordinates of `C = T⁻¹([0, ∞)ⁿ ⊕ W)`, all of which
vanish at `ψ(x) = 0`, and `x` lies in exactly `d_X(x)` faces of the M-polyfold `O ≅ V`
(Corollary 2.5.13 (preprint 2.41) in the chart);
(2) **`d_X(a) = d_A(a)`** for every `a ∈ A ∩ U`, `d_A` the degeneracy index of the M-polyfold `A`
with its induced structure (Proposition 2.3.19 (preprint 2.21));
(3) **`A` is in general position at every `a ∈ A ∩ U`**;
(4) for every `σ ⊆ {1, …, n}`, with the faces `F_i` (`i ∈ σ`) of `O` through `0` and an open
`G ∋ 0`, the intersection of local faces **`F_σ = ψ⁻¹(G ∩ ⋂_{i ∈ σ} F_i) ⊆ U`** is a sub-M-polyfold,
**tame**, with `d_{F_σ} + #σ = d_X`, and **`A ∩ F_σ` is a tame smooth finite-dimensional
submanifold of `F_σ`, in general position (in `F_σ`) at each of its points**.
*Proof* (the text's, in the chart `ψ`, completed): `theorem_4_2_11_chart` for the tame retraction `r`
and the sc⁺ chart retraction `t = ψ ∘ s ∘ ψ⁻¹ ∘ r` onto `ψ(W ∩ A)`.  For (2), the corner chart
`p ∘ ψ` of `A` (`CornerChartData.chart` for the induced chart of `A`, with the good complement
`Y ⊆ E_0`) is a chart of `A` modelled on `(V, N ∩ C, N)`, tame, so `d_A(a) = d_{N ∩ C}(p(ψ a))`
(the text: "by Proposition 2.24"), and `d_{N ∩ C}(p(ψ a)) = d_C(ψ a) = d_X(a)` (the text: "in view
of Proposition 2.36, `d_C(a) = d_O(a)`"; here the tame chart realizes `d_X`).  (4), for which the
text gives no argument, is `theorem_4_2_11_four_of_chart`. -/
theorem theorem_4_2_11_preprint (hP : P.IsTame) {A : Set X} (hA : P.IsSmoothSubmanifold A)
    [ParacompactSpace A] {x : X} (hgp : P.IsGeneralPositionAt A x) :
    ∃ ψ : MChart X, P.IsChart ψ ∧ ∃ hx : x ∈ ψ.source, ψ x = 0 ∧
      ∃ (R : ScRetraction ψ.model.E ψ.model.C) (n : ℕ) (Wq : ScBanach)
        (T : ScIso ψ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
        R.retract = ψ.model.O ∧ ψ.model.C = T 0 ⁻¹' quadrant n Wq 0 ∧ R.IsTameWith T ∧
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ ψ.source ∧
        -- (1)
        P.degIndex x = n ∧
        {F | (ψ.model.toMPolyfold ⟨_, ψ.mapsTo_model x hx⟩).IsFace F ∧
          (⟨ψ x, ψ.mapsTo_model x hx⟩ : ψ.model.O) ∈ F}.encard = (P.degIndex x : ℕ∞) ∧
        -- (2)
        (∀ a : A, (a : X) ∈ U → (subPolyfold hA.isSubMPolyfold).degIndex a = P.degIndex a) ∧
        -- (3)
        (∀ a ∈ U ∩ A, P.IsGeneralPositionAt A a) ∧
        -- (4)
        ∀ σ : Finset (Fin n), ∃ (Fc : σ → Set (ψ.model.E 0)) (G : Set (ψ.model.E 0)),
          (∀ i, R.IsRetractFace (Fc i) ∧ (0 : ψ.model.E 0) ∈ Fc i ∧ Fc i ⊆ coordHyper T i) ∧
          IsOpen G ∧ (0 : ψ.model.E 0) ∈ G ∧ x ∈ ψ.cornerPreimage G Fc ∧
          ψ.cornerPreimage G Fc ⊆ U ∧
          ∃ hF : P.IsSubMPolyfold (ψ.cornerPreimage G Fc),
            haveI := P.paracompactSpace_subtype (ψ.cornerPreimage G Fc)
            (subPolyfold hF).IsTame ∧
            (∀ a, (subPolyfold hF).degIndex a + σ.card = P.degIndex a) ∧
            (subPolyfold hF).IsSmoothSubmanifold {b | (b : X) ∈ A} ∧
            (∀ b : ψ.cornerPreimage G Fc, (b : X) ∈ A →
              (subPolyfold hF).IsGeneralPositionAt {b | (b : X) ∈ A} b) ∧
            haveI := (subPolyfold hF).paracompactSpace_subtype {b | (b : X) ∈ A}
            (subPolyfold hF).IsTameSubmanifold {b | (b : X) ∈ A} := by
  have haA : x ∈ A := hgp.1
  obtain ⟨ψ, hψ, hxψ, hψ0, htame⟩ := hP.exists_centredChart (hA.subset_smoothSet haA)
  obtain ⟨R, hR, hRt⟩ := htame
  obtain ⟨n, Wq, T, hT⟩ := ψ.model.isPartialQuadrant
  have hRT := hRt n Wq T hT
  set d := hA.data haA with hd
  have hxd : x ∈ d.V := hA.mem_data_V haA
  have hxW : x ∈ d.toSubData.shrink ψ := d.toSubData.mem_shrink ψ haA hxd hxψ
  obtain ⟨t, ht, htp, -⟩ :=
    d.exists_chartRetraction hψ (P.levelMk 1 x (hA.mem_levelSet_one haA)) R hR
  have htR : t.retract ⊆ R.retract := by
    rw [ht, hR]; exact ψ.image_subset_model fun _ hy => d.toSubData.shrink_subset_source ψ hy.1
  have h0 : (0 : ψ.model.E 0) ∈ t.retract := by rw [ht, ← hψ0]; exact ⟨x, ⟨hxW, haA⟩, rfl⟩
  have h0O : (0 : ψ.model.E 0) ∈ R.retract := htR h0
  have h01 : ψ.model.E.toBase 1 (0 : ψ.model.E 1) ∈ t.retract := by rw [map_zero]; exact h0
  set N : Submodule ℝ (ψ.model.E 0) :=
    LinearMap.range (scDeriv t.U t 0 : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0) with hNdef
  have : FiniteDimensional ℝ N := lemma_4_1_7_ii htp h01
  have hN : (N : Set (ψ.model.E 0)) = tangentSpace ψ.model.E ψ.model.C t.retract 0 :=
    (tangentSpace_eq_coe_submodule t h01).symm
  have hz0 : ψ.model.E.toBase 1 0 = ψ x := by rw [map_zero, hψ0]
  have hgp0 : IsGeneralPositionRetractAt ψ.model.E ψ.model.C R.retract t.retract T 0 := by
    have := hgp.isGeneralPositionChart d hψ T hT hxd hxψ hz0
    rw [SubmanifoldData.IsGeneralPositionChart, ← hR, ← ht] at this
    exact this
  obtain ⟨hsup, -, Y, p, W₁, V, Γ, hYE, hYc, hYgood, hpN, hpY, hker, hW₁, h0W₁, hV, h0V, hΓs,
    hpΓ, hΓY, -, hΓp, hΓ0, hpmap, hΓmap, hdeg, hgen⟩ :=
    theorem_4_2_11_chart T hT hRT h0O t htp htR h0 hN hgp0
  -- the neighbourhood `U`
  set U : Set X := d.toSubData.shrink ψ ∩ ψ ⁻¹' W₁ with hUdef
  have hUo : IsOpen U :=
    (ψ.continuousOn_toFun.mono (d.toSubData.shrink_subset_source ψ)).isOpen_inter_preimage
      (d.toSubData.isOpen_shrink ψ) hW₁
  have hxU : x ∈ U := ⟨hxW, by rw [mem_preimage, hψ0]; exact h0W₁⟩
  have hUψ : U ⊆ ψ.source := fun y hy => d.toSubData.shrink_subset_source ψ hy.1
  have htameψ : IsTameRetract ψ.model.E ψ.model.C ψ.model.O := ⟨R, hR, hRt⟩
  have hUt : ∀ b ∈ U ∩ A, ψ b ∈ t.retract ∩ W₁ := fun b hb => by
    rw [ht]; exact ⟨⟨b, ⟨hb.1.1, hb.2⟩, rfl⟩, hb.1.2⟩
  refine ⟨ψ, hψ, hxψ, hψ0, R, n, Wq, T, hR, hT, hRT, U, hUo, hxU, hUψ, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1): `d_X(x) = d_C(0) = n`
    rw [P.degIndex_eq_chartDegIndex_of_isTameWith hψ R hR hT hRT hxψ, chartDegIndex, hψ0,
      degIndex_eq T hT (by rw [← hψ0]; exact ψ.apply_mem_C hxψ), degIndexWith, map_zero,
      quadrantDeg_zero]
  · -- (1): Corollary 2.5.13 (preprint 2.41) in the chart
    set hne : ψ.model.O.Nonempty := ⟨_, ψ.mapsTo_model x hxψ⟩
    have hdx : (ψ.model.toMPolyfold hne).degIndex ⟨ψ x, ψ.mapsTo_model x hxψ⟩ = P.degIndex x :=
      (ψ.model.degIndex_toMPolyfold_of_isTameWith hne R hR hT hRT _).trans
        (P.degIndex_eq_chartDegIndex_of_isTameWith hψ R hR hT hRT hxψ).symm
    rw [ψ.model.isFaceStructured_toMPolyfold hne R hR hT hRT, hdx]
  · -- (2): the corner chart `p ∘ ψ` of `A`
    intro a haU
    set χ := subChart d.toSubData hψ ⟨x, haA⟩ with hχ
    have hχO : χ.model.O = t.retract := ht.symm
    have hfinN := this
    let N' : Submodule ℝ (χ.model.E 0) := N
    have : FiniteDimensional ℝ N' := hfinN
    let cd : CornerChartData χ N' :=
      { Y := Y
        isGoodComplement := hYgood
        isClosed_Y := hYc
        p := p
        p_N := hpN
        p_Y := hpY
        W := W₁
        isOpen_W := hW₁
        zero_mem_W := h0W₁
        V := V
        V_relOpen := hV
        zero_mem_V := h0V
        Γ := Γ
        p_map := by rw [hχO]; exact hpmap
        Γ_map := by rw [hχO]; exact hΓmap
        Γ_p := by rw [hχO]; exact hΓp
        p_Γ := hpΓ }
    have hcd : (subPolyfold hA.isSubMPolyfold).IsChart cd.chart :=
      cd.chart_isChart (subPolyfold_isChart hA.isSubMPolyfold d.toSubData hψ ⟨x, haA⟩)
    have haχ : a ∈ cd.chart.source := ⟨haU.1, haU.2⟩
    have hψa : ψ a ∈ t.retract ∩ W₁ := hUt a ⟨haU, a.2⟩
    rw [(subPolyfold hA.isSubMPolyfold).degIndex_eq_chartDegIndex_of_isTameRetract hcd
      cd.chart_isCornerChart.isTameRetract haχ,
      P.degIndex_eq_chartDegIndex_of_isTameRetract hψ htameψ (hUψ haU), chartDegIndex,
      chartDegIndex]
    have hv : p (ψ a) ∈ V := hpmap.mapsTo hψa
    have := hdeg _ hv
    rw [hΓp _ hψa] at this
    exact this
  · -- (3)
    rintro b ⟨hbU, hbA⟩
    have hbV : b ∈ d.V := d.toSubData.shrink_subset_V ψ hbU.1
    have hbψ : b ∈ ψ.source := hUψ hbU
    obtain ⟨y, hy, -⟩ := exists_smoothLvl_one_of_mem_smooth (d.apply_mem_smooth hψ hbA hbV hbψ)
    refine ⟨hbA, d, ψ, n, Wq, T, y, hbV, hψ, hbψ, hT, hy, ?_⟩
    have := hgen (ψ b) (hUt b ⟨hbU, hbA⟩) y hy
    rw [hR, ht] at this
    exact this
  · -- (4)
    intro σ
    obtain ⟨Fc, G, hFc, hG, h0G, hGW, hxF, hFsh, hF, hrest⟩ :=
      theorem_4_2_11_four_of_chart hψ hxψ hψ0 hR hT hRT d t ht htp hsup hYE hpN hker hW₁ h0W₁ hV h0V
        hΓs hpΓ hΓY hΓp hΓ0 hpmap hΓmap σ
    exact ⟨Fc, G, hFc, hG, h0G, hxF, fun y hy => ⟨hFsh hy, hGW hy.2.1⟩, hF, hrest⟩

/-- **Remark 4.3.2 (preprint 4.24)**, first sentence: at a smooth point `x` of a tame M-polyfold, in a tame chart
`φ` (tame retraction `r`, presentation `T`) and at the level-`1` point `z` over `φ(x)`, the
reduced tangent space has codimension `dim(T_zO / T_z^R O) = d_X(x)` (Proposition 2.5.6 (preprint 2.36), with
`d_X(x) = d_C(φ x)` in a tame chart). -/
theorem remark_4_3_2_codim (hP : P.IsTame) {x : X} (hx : x ∈ P.smoothSet) :
    ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧ ∃ (R : ScRetraction φ.model.E φ.model.C) (n : ℕ)
      (Wq : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
      R.retract = φ.model.O ∧ φ.model.C = T 0 ⁻¹' quadrant n Wq 0 ∧ R.IsTameWith T ∧
      ∀ z : φ.model.E 1, φ.model.E.toBase 1 z = φ x →
        quotDim (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0))
          (reducedTangentSpaceWith R T z) = P.degIndex x := by
  obtain ⟨φ, hφ, hxφ, R, hR, hRt⟩ := MPolyfold.IsTame.exists_chart P hP x
  obtain ⟨n, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  have hRT := hRt n Wq T hT
  refine ⟨φ, hφ, hxφ, R, n, Wq, T, hR, hT, hRT, fun z hz => ?_⟩
  have hz1 : z ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hR]; exact φ.mapsTo_model x hxφ
  have hzs : z ∈ φ.model.E.smoothLvl 1 := by
    change φ.model.E.toBase 1 z ∈ (φ.model.E.smooth : Set (φ.model.E 0))
    rw [hz]; exact (mem_smoothSet_iff hφ hxφ).1 hx
  rw [quotDim_reducedTangentSpaceWith_eq hRT hz1 hzs, ← degIndex_eq T hT (R.retract_subset_C hz1),
    hz, P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hR hT hRT hxφ, chartDegIndex]

/-- **Remark 4.3.2 (preprint 4.24)**, second sentence: if `A` is in general position at `a`, then
`d_X(a) ≤ dim T_aA` (since `T_aX = T_aA + T_a^R X` and `codim T_a^R X = d_X(a)`); so `a` can lie
in a corner (`d_X(a) ≥ 2`) only if `d_X(a) ≤ dim A` near `a`, a zero-dimensional `A` in general
position lies in `X ∖ ∂X`, a one-dimensional one meets only `{d_X = 1}`, etc.  Stated in any
tame chart `φ` at `a`, for the tangent space `T_zA = T_z(φ(W ∩ A))` of Remark 4.2.2 (preprint 4.14). -/
theorem remark_4_3_2 {A : Set X} {a : X}
    (hgp : P.IsGeneralPositionAt A a) (d : P.SubmanifoldData A) (had : a ∈ d.V) {φ : MChart X}
    (hφ : P.IsChart φ) (haφ : a ∈ φ.source)
    (htame : IsTameRetract φ.model.E φ.model.C φ.model.O) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ a) {N : Submodule ℝ (φ.model.E 0)} [FiniteDimensional ℝ N]
    (hN : (N : Set (φ.model.E 0)) =
      tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) z) :
    P.degIndex a ≤ finrank ℝ N := by
  obtain ⟨R, hR, hRt⟩ := htame
  obtain ⟨n, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  have hRT := hRt n Wq T hT
  have hchart := hgp.isGeneralPositionChart d hφ T hT had haφ hz
  rw [SubmanifoldData.IsGeneralPositionChart, ← hR] at hchart
  have hz1 : z ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hR]; exact φ.mapsTo_model a haφ
  have hzs : z ∈ φ.model.E.smoothLvl 1 := by
    change φ.model.E.toBase 1 z ∈ (φ.model.E.smooth : Set (φ.model.E 0))
    rw [hz]; exact d.apply_mem_smooth hφ hgp.1 had haφ
  have := (remark_4_3_2_chart T hT hRT hz1 hzs hchart hN).2
  rwa [hz, ← chartDegIndex, ← P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hR hT hRT haφ] at this

/-- **Remark 4.3.2 (preprint 4.24)**, the example: a smooth submanifold in general position at `a` with
`T_aA = 0` (zero-dimensional near `a`) does not meet the boundary at `a`. -/
theorem remark_4_3_2_not_mem_boundary {A : Set X} {a : X}
    (hgp : P.IsGeneralPositionAt A a) (d : P.SubmanifoldData A) (had : a ∈ d.V) {φ : MChart X}
    (hφ : P.IsChart φ) (haφ : a ∈ φ.source)
    (htame : IsTameRetract φ.model.E φ.model.C φ.model.O) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ a)
    (h0 : tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) z = {0}) :
    a ∉ P.boundary := by
  have h := remark_4_3_2 hgp d had hφ haφ htame hz (N := ⊥) (by rw [Submodule.bot_coe, h0])
  rw [finrank_bot] at h
  change ¬ (1 ≤ P.degIndex a)
  omega

end MPolyfold

end Polyfold
