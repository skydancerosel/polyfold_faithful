import Mathlib

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.1 (pp. 684–687): the topological part of the proof of **Theorem 15.1.1**:
**Proposition 15.1.3**, **Lemma 15.1.4**, **Lemma 15.1.5**, **Remark 15.1.6**
(2017 text: Proposition 15.1, Lemma 15.1, Lemma 15.2; Remark 15.1.6 has no 2017 number), and the
limit step at the end of the proof of Theorem 15.1.1.

# Separation of finitely many local branches, and limits of finite formal sums

## The text, paraphrased

(Lemma 15.1.4) If a ball `B_ε(y)` of the local model `O` (metric of `E₀`) is a finite union of
closed subsets, one of them has nonempty interior.  (Lemma 15.1.5) For finitely many local
sections `sᵢ` and a ball `B_ε(y)` there are `z`, `δ` with `B_δ(z) ⊆ B_ε(y)` and a partition
`I = I₁ ⊔ … ⊔ I_p` such that on `B_δ(z)` the sections of one piece coincide and sections of
different pieces are pointwise different.  (Proposition 15.1.3) There is a sequence `x_k → 0`,
`x_k ≠ 0`, and one partition such that `sᵢ(x_k) = sᵢ'(x_k)` iff `i, i'` lie in one piece, and
then `sᵢ = sᵢ'` near `x_k`.  (Remark 15.1.6) The sequence can be obtained from any sequence
`x'_k → 0` by small moves and a subsequence, and small moves of a good sequence stay good.  (End of
the proof of Theorem 15.1.1) The formal sums at `x_k` agree for two structures and converge
"in the weak topology"; hence their limits agree.

## What is formalized (namespace `Polyfold.Linearization15`)

* `wsum a σ q = ∑_{i : aᵢ = q} σᵢ`, the coefficient of `q` in the finite formal sum `∑ σᵢ · aᵢ`
  (weights in any additive commutative monoid), and `mass a σ N = ∑_{i : aᵢ ∈ N} σᵢ`;
  `mass_eq_of_wsum_eq`, `wsum_map_eq_of_wsum_eq` (equal formal sums have equal images).
* **The limit step**: `wsum_eq_of_frequently` — if two finite formal sums of points depending
  continuously on `z` agree for `z` frequently near `x₀` (values in a Hausdorff space), they agree
  at `x₀`.  This is the "convergence in the weak topology" of the text.
* **Lemma 15.1.4**: `lemma_15_1_4` (book form, in any pseudo-metric space; the closed sets are
  closed in the ball) and `exists_nonempty_interior_of_finite_closed_cover` (topological form).
* **Lemma 15.1.5**: `lemma_15_1_5` (book form, in any pseudo-metric space, maps continuous on the
  ball into a Hausdorff space), from `exists_isOpen_dichotomy` (topological form: inside any
  nonempty open set there is a nonempty open set on which each pair of maps coincides or is
  pointwise different).
* **Proposition 15.1.3**: `proposition_15_1_3_hyp` in any first countable `T₁` space, for a point
  that is not isolated; `IsSeparatedAt s e z` is the conclusion at one point (`e : I → Fin p` the
  partition).  `not_proposition_15_1_3_of_isolated`: if `0` is isolated in `O` (e.g. `O` a
  point) no sequence `x_k ≠ 0` with `x_k → 0` exists.
* **Remark 15.1.6**: `remark_15_1_6` (from any sequence `x'_k → x₀` in a metric space: points
  `x''_k` with `d(x'_k, x''_k) < 1/(k+1)` and a subsequence) and `IsSeparatedAt.eventually` (the
  property is open: small moves keep it).
* **The core of Theorem 15.1.1**: `wsum_pair_eq_of_isLocal` — for two finite families of
  branches `aᵢ`, `bⱼ` with the same weighted counts at every point near `x₀`, and "derivatives"
  `Dᵢ`, `D'ⱼ` continuous at `x₀` and determined by the branch on open sets, the formal sums of
  the pairs `(value, derivative)` at `x₀` agree.

## Reading

The text works with the metric of `E₀`.  The separation lemmas hold in any topological space
(the proofs here use only continuity of the branches and the Hausdorff property of the target),
so they can be applied in the level-`1` topology, where the derivatives `x ↦ (f − sᵢ)'(x)` are
continuous (pointwise on `E₀`, Definition 1.1.15 (3)); this is how `P3T_Linearization.lean` uses
them (see the reading there).  Lemma 15.1.4 is not needed for Lemma 15.1.5 in this form: if the
set where two branches differ is empty on an open set they agree there.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace Linearization15

open scoped Classical

/-! ### Finite formal sums -/

section FormalSums

variable {ι κ Q Q' M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M]

/-- `if` along an equivalence of conditions, for any decidability instances. -/
theorem ite_iff_congr {α : Type*} {p q : Prop} {hp : Decidable p} {hq : Decidable q} (h : p ↔ q)
    (x y : α) : (if p then x else y) = if q then x else y := by
  by_cases hp' : p
  · rw [if_pos hp', if_pos (h.1 hp')]
  · rw [if_neg hp', if_neg (mt h.2 hp')]

/-- The coefficient of `q` in the finite formal sum `∑ σᵢ · aᵢ`. -/
def wsum (a : ι → Q) (σ : ι → M) (q : Q) : M := ∑ i, if a i = q then σ i else 0

/-- The mass of `N` under the finite formal sum `∑ σᵢ · aᵢ`. -/
def mass (a : ι → Q) (σ : ι → M) (N : Set Q) : M := ∑ i, if a i ∈ N then σ i else 0

theorem mass_eq_sum_wsum (a : ι → Q) (σ : ι → M) (N : Set Q) (S : Finset Q)
    (hS : ∀ i, a i ∈ S) : mass a σ N = ∑ q ∈ S.filter (· ∈ N), wsum a σ q := by
  unfold mass wsum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_filter, hS i, true_and]

/-- Equal formal sums give equal masses. -/
theorem mass_eq_of_wsum_eq {a : ι → Q} {σ : ι → M} {b : κ → Q} {τ : κ → M}
    (h : ∀ q, wsum a σ q = wsum b τ q) (N : Set Q) : mass a σ N = mass b τ N := by
  set S : Finset Q := Finset.univ.image a ∪ Finset.univ.image b
  rw [mass_eq_sum_wsum a σ N S
      (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem a (Finset.mem_univ i))),
    mass_eq_sum_wsum b τ N S
      (fun j => Finset.mem_union_right _ (Finset.mem_image_of_mem b (Finset.mem_univ j)))]
  exact Finset.sum_congr rfl fun q _ => h q

theorem wsum_map (ψ : Q → Q') (a : ι → Q) (σ : ι → M) (q' : Q') :
    wsum (fun i => ψ (a i)) σ q' = mass a σ (ψ ⁻¹' {q'}) := rfl

/-- Equal formal sums have equal images under any map. -/
theorem wsum_map_eq_of_wsum_eq {a : ι → Q} {σ : ι → M} {b : κ → Q} {τ : κ → M}
    (h : ∀ q, wsum a σ q = wsum b τ q) (ψ : Q → Q') (q' : Q') :
    wsum (fun i => ψ (a i)) σ q' = wsum (fun j => ψ (b j)) τ q' := by
  rw [wsum_map, wsum_map]; exact mass_eq_of_wsum_eq h _

/-- If all `aᵢ` with first component `v` have second component `L₀`, the coefficient of `(v, L)`
is that of `v` when `L = L₀` and `0` otherwise. -/
theorem wsum_pair_of_const {Y : Type*} (a : ι → Y) (D : ι → Q) (σ : ι → M) (v : Y) (L L₀ : Q)
    (h : ∀ i, a i = v → D i = L₀) :
    wsum (fun i => (a i, D i)) σ (v, L) = if L₀ = L then wsum a σ v else 0 := by
  unfold wsum
  split_ifs with hL
  · refine Finset.sum_congr rfl fun i _ => ite_iff_congr ?_ _ _
    constructor
    · intro e; exact congrArg Prod.fst e
    · intro e; exact Prod.ext e ((h i e).trans hL)
  · refine Finset.sum_eq_zero fun i _ => if_neg fun e => hL ?_
    exact (h i (congrArg Prod.fst e)).symm.trans (congrArg Prod.snd e)

/-- **The limit step of the proof of Theorem 15.1.1** ("convergence in the weak topology"): two
finite formal sums of points `aᵢ(z)`, `bⱼ(z)` of a Hausdorff space, continuous at `x₀`, which
agree for `z` frequently near `x₀`, agree at `x₀`. -/
theorem wsum_eq_of_frequently {Z : Type*} [TopologicalSpace Z] [TopologicalSpace Q] [T2Space Q]
    {a : ι → Z → Q} {b : κ → Z → Q} {σ : ι → M} {τ : κ → M} {x₀ : Z}
    (ha : ∀ i, ContinuousAt (a i) x₀) (hb : ∀ j, ContinuousAt (b j) x₀)
    (h : ∃ᶠ z in 𝓝 x₀, ∀ q, wsum (fun i => a i z) σ q = wsum (fun j => b j z) τ q) (q : Q) :
    wsum (fun i => a i x₀) σ q = wsum (fun j => b j x₀) τ q := by
  have key : ∀ p : Q, ∃ N ∈ 𝓝 q, ∃ V ∈ 𝓝 p, p ≠ q → Disjoint N V := by
    intro p
    by_cases hp : p = q
    · exact ⟨univ, univ_mem, univ, univ_mem, fun h => (h hp).elim⟩
    · obtain ⟨N, hN, V, hV, hd⟩ := Filter.disjoint_iff.1 (disjoint_nhds_nhds.2 (Ne.symm hp))
      exact ⟨N, hN, V, hV, fun _ => hd⟩
  choose N hN V hV hd using key
  set N₀ : Set Q := (⋂ i, N (a i x₀)) ∩ ⋂ j, N (b j x₀) with hN₀def
  have hN₀ : N₀ ∈ 𝓝 q := inter_mem (iInter_mem.2 fun i => hN _) (iInter_mem.2 fun j => hN _)
  have hA : ∀ᶠ z in 𝓝 x₀, ∀ i, (a i z ∈ N₀ ↔ a i x₀ = q) := by
    rw [eventually_all]
    intro i
    by_cases hi : a i x₀ = q
    · have hm : N₀ ∈ 𝓝 (a i x₀) := by rw [hi]; exact hN₀
      filter_upwards [ha i hm] with z hz
      exact ⟨fun _ => hi, fun _ => hz⟩
    · filter_upwards [ha i (hV (a i x₀))] with z hz
      refine ⟨fun hzN => (Set.disjoint_left.1 (hd _ hi) ?_ hz).elim, fun h' => (hi h').elim⟩
      exact (mem_iInter.1 hzN.1) i
  have hB : ∀ᶠ z in 𝓝 x₀, ∀ j, (b j z ∈ N₀ ↔ b j x₀ = q) := by
    rw [eventually_all]
    intro j
    by_cases hj : b j x₀ = q
    · have hm : N₀ ∈ 𝓝 (b j x₀) := by rw [hj]; exact hN₀
      filter_upwards [hb j hm] with z hz
      exact ⟨fun _ => hj, fun _ => hz⟩
    · filter_upwards [hb j (hV (b j x₀))] with z hz
      refine ⟨fun hzN => (Set.disjoint_left.1 (hd _ hj) ?_ hz).elim, fun h' => (hj h').elim⟩
      exact (mem_iInter.1 hzN.2) j
  obtain ⟨z, hz, hzA, hzB⟩ := (h.and_eventually (hA.and hB)).exists
  have e1 : mass (fun i => a i z) σ N₀ = wsum (fun i => a i x₀) σ q :=
    Finset.sum_congr rfl fun i _ => ite_iff_congr (hzA i) _ _
  have e2 : mass (fun j => b j z) τ N₀ = wsum (fun j => b j x₀) τ q :=
    Finset.sum_congr rfl fun j _ => ite_iff_congr (hzB j) _ _
  rw [← e1, ← e2]
  exact mass_eq_of_wsum_eq hz N₀

end FormalSums

/-! ### Lemma 15.1.4 -/

section Baire

variable {Z : Type*} [TopologicalSpace Z]

/-- A finite union of closed sets with empty interiors has empty interior (no Baire property is
needed for finite unions). -/
theorem interior_biUnion_eq_empty {ι : Type*} (S : Finset ι) (A : ι → Set Z)
    (hcl : ∀ i ∈ S, IsClosed (A i)) (hint : ∀ i ∈ S, interior (A i) = ∅) :
    interior (⋃ i ∈ S, A i) = ∅ := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.set_biUnion_insert,
      interior_union_isClosed_of_interior_empty (hcl a (Finset.mem_insert_self a S))
        (ih (fun i hi => hcl i (Finset.mem_insert_of_mem hi))
          fun i hi => hint i (Finset.mem_insert_of_mem hi))]
    exact hint a (Finset.mem_insert_self a S)

/-- **Lemma 15.1.4, topological form**: a nonempty open set covered by finitely many closed sets
meets the interior of one of them. -/
theorem exists_nonempty_interior_of_finite_closed_cover {ι : Type*} [Finite ι] (A : ι → Set Z)
    (hcl : ∀ i, IsClosed (A i)) {V : Set Z} (hV : IsOpen V) (hne : V.Nonempty)
    (hcov : V ⊆ ⋃ i, A i) : ∃ i, (interior (A i)).Nonempty := by
  have := Fintype.ofFinite ι
  by_contra hcon
  simp only [not_exists, Set.not_nonempty_iff_eq_empty] at hcon
  have h0 := interior_biUnion_eq_empty Finset.univ A (fun i _ => hcl i) fun i _ => hcon i
  have hU : (⋃ i ∈ (Finset.univ : Finset ι), A i) = ⋃ i, A i := by simp
  rw [hU] at h0
  obtain ⟨x, hx⟩ := hne
  have : x ∈ interior (⋃ i, A i) := interior_mono hcov (hV.interior_eq.symm ▸ hx)
  rw [h0] at this
  exact this

/-- **Lemma 15.1.4 (2017: Lemma 15.1), p. 685**: if a ball `B_ε(y)` of a (pseudo-)metric space is
the union of finitely many sets `Σᵢ` closed in `B_ε(y)`, one of them has nonempty interior.  The
text's `O` with the metric of `E₀` is a special case; the statement holds in every pseudo-metric
space. -/
theorem lemma_15_1_4 {Z : Type*} [PseudoMetricSpace Z] {ι : Type*} [Finite ι] (y : Z) {ε : ℝ}
    (hε : 0 < ε) (A : ι → Set Z)
    (hcl : ∀ i, IsClosed ((Subtype.val : Metric.ball y ε → Z) ⁻¹' A i))
    (hcov : ⋃ i, A i = Metric.ball y ε) : ∃ i, (interior (A i)).Nonempty := by
  have hne : (univ : Set (Metric.ball y ε)).Nonempty :=
    ⟨⟨y, Metric.mem_ball_self hε⟩, mem_univ _⟩
  obtain ⟨i, x, hx⟩ := exists_nonempty_interior_of_finite_closed_cover
    (fun i => (Subtype.val : Metric.ball y ε → Z) ⁻¹' A i) hcl isOpen_univ hne
    (fun z _ => by
      have : (z : Z) ∈ ⋃ i, A i := by rw [hcov]; exact z.2
      obtain ⟨i, hi⟩ := mem_iUnion.1 this
      exact mem_iUnion.2 ⟨i, hi⟩)
  refine ⟨i, x, ?_⟩
  have hopen : IsOpen ((Subtype.val : Metric.ball y ε → Z) ''
      interior ((Subtype.val : Metric.ball y ε → Z) ⁻¹' A i)) :=
    Metric.isOpen_ball.isOpenMap_subtype_val _ isOpen_interior
  refine interior_maximal ?_ hopen ⟨x, hx, rfl⟩
  rintro _ ⟨w, hw, rfl⟩
  have hw' := interior_subset hw
  exact hw'

end Baire

/-! ### Lemma 15.1.5 -/

section Separation

variable {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [T2Space Y]

/-- **Lemma 15.1.5, topological form**: for finitely many maps continuous on a nonempty open `V`
(values in a Hausdorff space) there is a nonempty open `W ⊆ V` on which each pair of the maps
either coincides or is pointwise different. -/
theorem exists_isOpen_dichotomy {ι : Type*} [Finite ι] (s : ι → Z → Y) {V : Set Z}
    (hV : IsOpen V) (hne : V.Nonempty) (hs : ∀ i, ContinuousOn (s i) V) :
    ∃ W ⊆ V, IsOpen W ∧ W.Nonempty ∧
      ∀ i j, EqOn (s i) (s j) W ∨ ∀ w ∈ W, s i w ≠ s j w := by
  have := Fintype.ofFinite ι
  suffices H : ∀ S : Finset (ι × ι), ∃ W ⊆ V, IsOpen W ∧ W.Nonempty ∧
      ∀ p ∈ S, EqOn (s p.1) (s p.2) W ∨ ∀ w ∈ W, s p.1 w ≠ s p.2 w by
    obtain ⟨W, hWV, hW, hWne, hWp⟩ := H Finset.univ
    exact ⟨W, hWV, hW, hWne, fun i j => hWp (i, j) (Finset.mem_univ _)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨V, subset_rfl, hV, hne, fun p hp => absurd hp (Finset.notMem_empty p)⟩
  | insert p S _ ih =>
    obtain ⟨W, hWV, hW, hWne, hWp⟩ := ih
    have hc : ContinuousOn (fun w => (s p.1 w, s p.2 w)) W :=
      ((hs p.1).mono hWV).prodMk ((hs p.2).mono hWV)
    set W' := W ∩ (fun w => (s p.1 w, s p.2 w)) ⁻¹' (diagonal Y)ᶜ with hW'def
    have hW' : IsOpen W' := hc.isOpen_inter_preimage hW isClosed_diagonal.isOpen_compl
    have hmemW' : ∀ w, w ∈ W' ↔ w ∈ W ∧ s p.1 w ≠ s p.2 w := fun w => by
      simp [hW'def, mem_diagonal_iff]
    rcases W'.eq_empty_or_nonempty with h0 | hne'
    · refine ⟨W, hWV, hW, hWne, fun q hq => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hq
      · left
        intro w hw
        by_contra hne''
        have : w ∈ W' := (hmemW' w).2 ⟨hw, hne''⟩
        rw [h0] at this; exact this
      · exact hWp q hq
    · refine ⟨W', fun w hw => hWV ((hmemW' w).1 hw).1, hW', hne', fun q hq => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact Or.inr fun w hw => ((hmemW' w).1 hw).2
      · rcases hWp q hq with h | h
        · exact Or.inl (h.mono fun w hw => ((hmemW' w).1 hw).1)
        · exact Or.inr fun w hw => h w ((hmemW' w).1 hw).1

omit [TopologicalSpace Y] [T2Space Y] in
/-- A partition of a finite index set by the values of a map: `e i = e j ↔ vᵢ = vⱼ`. -/
theorem exists_fin_partition {ι : Type*} [Finite ι] (v : ι → Y) :
    ∃ (p : ℕ) (e : ι → Fin p), Surjective e ∧ ∀ i j, e i = e j ↔ v i = v j := by
  have := Fintype.ofFinite ι
  set S : Finset Y := Finset.univ.image v
  let e : ι → Fin S.card := fun i => S.equivFin ⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i)⟩
  refine ⟨S.card, e, fun k => ?_, fun i j => ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (S.equivFin.symm k).2
    refine ⟨i, ?_⟩
    have : (⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i)⟩ : S) = S.equivFin.symm k :=
      Subtype.ext hi
    simp only [e, this, Equiv.apply_symm_apply]
  · simp only [e, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]

/-- **Lemma 15.1.5 (2017: Lemma 15.2), pp. 685–686**: for finitely many maps `sᵢ` continuous on a
ball `B_ε(y)` of a pseudo-metric space (values in a Hausdorff space) there are `z` with
`d(z, y) < ε`, `δ > 0` and a partition `e : I → Fin p` (pieces `I_e = e⁻¹(e)`) with (1)
`B_δ(z) ⊆ B_ε(y)`, (2) `sᵢ = sᵢ'` on `B_δ(z)` for `i, i'` in one piece, (3) `sᵢ(w) ≠ sⱼ(w)` on
`B_δ(z)` for `i, j` in different pieces.  The text's setting (`O` with the metric of `E₀`,
sc⁺-sections) is a special case. -/
theorem lemma_15_1_5 {Z : Type*} [PseudoMetricSpace Z] {ι : Type*} [Finite ι]
    (s : ι → Z → Y) (y : Z) {ε : ℝ} (hε : 0 < ε)
    (hs : ∀ i, ContinuousOn (s i) (Metric.ball y ε)) :
    ∃ z : Z, dist z y < ε ∧ ∃ δ > 0, ∃ (p : ℕ) (e : ι → Fin p), Surjective e ∧
      Metric.ball z δ ⊆ Metric.ball y ε ∧
      (∀ i i', e i = e i' → ∀ w ∈ Metric.ball z δ, s i w = s i' w) ∧
      (∀ i j, e i ≠ e j → ∀ w ∈ Metric.ball z δ, s i w ≠ s j w) := by
  have := Fintype.ofFinite ι
  obtain ⟨W, hWV, hW, ⟨z, hz⟩, hWp⟩ := exists_isOpen_dichotomy s Metric.isOpen_ball
    ⟨y, Metric.mem_ball_self hε⟩ hs
  obtain ⟨δ, hδ, hδW⟩ := Metric.isOpen_iff.1 hW z hz
  obtain ⟨p, e, he, hev⟩ := exists_fin_partition fun i => s i z
  refine ⟨z, hWV hz, δ, hδ, p, e, he, hδW.trans hWV, fun i i' hii' w hw => ?_,
    fun i j hij w hw => ?_⟩
  · rcases hWp i i' with h | h
    · exact h (hδW hw)
    · exact absurd ((hev i i').1 hii') (h z hz)
  · rcases hWp i j with h | h
    · exact absurd ((hev i j).2 (h hz)) hij
    · exact h w (hδW hw)

end Separation

/-! ### Proposition 15.1.3 and Remark 15.1.6 -/

section Sequence

variable {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [T2Space Y]

/-- At `z` each pair of the maps either coincides near `z` or differs at `z`. -/
def IsLocDich {α : Type*} (s : α → Z → Y) (z : Z) : Prop :=
  ∀ i j, s i =ᶠ[𝓝 z] s j ∨ s i z ≠ s j z

/-- **The conclusion of Proposition 15.1.3 at one point `z`**, for the partition `e : I → κ`
(pieces `e⁻¹(·)`): (1) `sᵢ(z) = sⱼ(z)` iff `i, j` lie in one piece, (2) then `sᵢ = sⱼ` near
`z`. -/
def IsSeparatedAt {ι κ : Type*} (s : ι → Z → Y) (e : ι → κ) (z : Z) : Prop :=
  (∀ i j, s i z = s j z ↔ e i = e j) ∧ ∀ i j, e i = e j → s i =ᶠ[𝓝 z] s j

/-- Every nonempty open set on which the maps are continuous contains a point where they are
locally dichotomous (Lemma 15.1.5). -/
theorem exists_isLocDich_mem {α : Type*} [Finite α] (s : α → Z → Y) {G : Set Z} (hG : IsOpen G)
    (hne : G.Nonempty) (hs : ∀ i, ContinuousOn (s i) G) : ∃ z ∈ G, IsLocDich s z := by
  have := Fintype.ofFinite α
  obtain ⟨W, hWG, hW, ⟨z, hz⟩, hWp⟩ := exists_isOpen_dichotomy s hG hne hs
  refine ⟨z, hWG hz, fun i j => ?_⟩
  rcases hWp i j with h | h
  · exact Or.inl (Filter.eventuallyEq_of_mem (hW.mem_nhds hz) h)
  · exact Or.inr (h z hz)

/-- **Remark 15.1.6, second part**: the separation property is open, so a small move of a point
(of a sequence) with the property of Proposition 15.1.3 keeps it. -/
theorem IsSeparatedAt.eventually {ι κ : Type*} [Finite ι] {s : ι → Z → Y} {e : ι → κ} {z : Z}
    (h : IsSeparatedAt s e z) (hs : ∀ i, ContinuousAt (s i) z) :
    ∀ᶠ z' in 𝓝 z, IsSeparatedAt s e z' := by
  have h1 : ∀ᶠ z' in 𝓝 z, ∀ i j, (s i z' = s j z' ↔ e i = e j) := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    by_cases hij : e i = e j
    · filter_upwards [h.2 i j hij] with z' hz'
      exact ⟨fun _ => hij, fun _ => hz'⟩
    · have hne : (s i z, s j z) ∈ (diagonal Y)ᶜ := fun hd => hij ((h.1 i j).1 hd)
      filter_upwards [((hs i).prodMk (hs j)) (isClosed_diagonal.isOpen_compl.mem_nhds hne)]
        with z' hz'
      exact ⟨fun hd => (hz' hd).elim, fun he => (hij he).elim⟩
  have h2 : ∀ᶠ z' in 𝓝 z, ∀ i j, e i = e j → s i =ᶠ[𝓝 z'] s j := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    by_cases hij : e i = e j
    · filter_upwards [(h.2 i j hij).eventually_nhds] with z' hz' _ using hz'
    · exact Eventually.of_forall fun _ he => (hij he).elim
  filter_upwards [h1, h2] with z' h1' h2' using ⟨h1', h2'⟩

omit [TopologicalSpace Y] [T2Space Y] in
/-- The subsequence step of the proof of Proposition 15.1.3: along a subsequence the pattern of
coincidences is constant. -/
theorem exists_isSeparatedAt_subseq {ι : Type*} [Finite ι] (s : ι → Z → Y) (z : ℕ → Z)
    (hz : ∀ k, IsLocDich s (z k)) : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (p : ℕ) (e : ι → Fin p), Surjective e ∧ ∀ k, IsSeparatedAt s e (z (φ k)) := by
  have := Fintype.ofFinite ι
  let pat : ℕ → (ι → ι → Prop) := fun k i j => s i (z k) = s j (z k)
  obtain ⟨P, hP⟩ := Finite.exists_infinite_fiber pat
  have hfreq : ∃ᶠ k in atTop, pat k = P := by
    rw [Nat.frequently_atTop_iff_infinite]; exact Set.infinite_coe_iff.1 hP
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨p, e, he, hev⟩ := exists_fin_partition fun i => s i (z (φ 0))
  refine ⟨φ, hφ, p, e, he, fun k => ?_⟩
  have hpat : ∀ i j, s i (z (φ k)) = s j (z (φ k)) ↔ e i = e j := by
    intro i j
    rw [hev]
    have h1 := congrFun (congrFun (hφP k) i) j
    have h0 := congrFun (congrFun (hφP 0) i) j
    simp only [pat] at h1 h0
    rw [h1, h0]
  refine ⟨hpat, fun i j hij => ?_⟩
  rcases hz (φ k) i j with h | h
  · exact h
  · exact absurd ((hpat i j).2 hij) h

/-- **Proposition 15.1.3 (2017: Proposition 15.1), p. 684**: for finitely many maps `sᵢ`
continuous on an open `V ∋ x₀` (values in a Hausdorff space) of a first countable `T₁` space, where
`x₀` is not isolated, there is a sequence `x_k ∈ V`, `x_k ≠ x₀`, `x_k → x₀`, and one partition
`e : I → Fin p` such that (1) `sᵢ(x_k) = sⱼ(x_k)` iff `e i = e j`, (2) then `sᵢ = sⱼ` near
`x_k`.  The text states it on the local model `O` (metric of `E₀`, `x₀ = 0`) for the sections of
a local sc⁺-section structure; the added hypothesis that `0` is not isolated is implicit there
(see `not_proposition_15_1_3_of_isolated`; witness `proposition_15_1_3_hyp_witness`). -/
theorem proposition_15_1_3_hyp [FirstCountableTopology Z] [T1Space Z] {ι : Type*} [Finite ι]
    (s : ι → Z → Y)
    {V : Set Z} (hV : IsOpen V) (hs : ∀ i, ContinuousOn (s i) V) {x₀ : Z} (hx₀ : x₀ ∈ V)
    (hiso : (𝓝[≠] x₀).NeBot) :
    ∃ x : ℕ → Z, (∀ k, x k ≠ x₀) ∧ (∀ k, x k ∈ V) ∧ Tendsto x atTop (𝓝 x₀) ∧
      ∃ (p : ℕ) (e : ι → Fin p), Surjective e ∧ ∀ k, IsSeparatedAt s e (x k) := by
  have := Fintype.ofFinite ι
  obtain ⟨u, hu⟩ := (𝓝 x₀).exists_antitone_basis
  have hpt : ∀ k, ∃ z ∈ interior (u k) ∩ V ∩ {x₀}ᶜ, IsLocDich s z := by
    intro k
    have hG : IsOpen (interior (u k) ∩ V ∩ {x₀}ᶜ) :=
      (isOpen_interior.inter hV).inter isOpen_compl_singleton
    have h1 : interior (u k) ∩ V ∈ 𝓝[≠] x₀ :=
      nhdsWithin_le_nhds (inter_mem (interior_mem_nhds.2 (hu.mem k)) (hV.mem_nhds hx₀))
    exact exists_isLocDich_mem s hG (hiso.nonempty_of_mem (inter_mem h1 self_mem_nhdsWithin))
      fun i => (hs i).mono fun z hz => hz.1.2
  choose z hzG hz using hpt
  obtain ⟨φ, hφ, p, e, he, hsep⟩ := exists_isSeparatedAt_subseq s z hz
  refine ⟨z ∘ φ, fun k => (hzG (φ k)).2, fun k => (hzG (φ k)).1.2, ?_, p, e, he, hsep⟩
  exact (hu.tendsto fun k => interior_subset (hzG k).1.1).comp hφ.tendsto_atTop

/-- **Proposition 15.1.3 needs `0` not isolated in `O`**: if `{x₀}` is open (e.g. `O` a point,
the local model of a zero-dimensional `X`) there is no sequence `x_k ≠ x₀` with `x_k → x₀`. -/
theorem not_proposition_15_1_3_of_isolated {x₀ : Z} (hiso : IsOpen ({x₀} : Set Z)) :
    ¬ ∃ x : ℕ → Z, (∀ k, x k ≠ x₀) ∧ Tendsto x atTop (𝓝 x₀) := by
  rintro ⟨x, hx, ht⟩
  obtain ⟨k, hk⟩ := (ht.eventually (hiso.mem_nhds rfl)).exists
  exact hx k hk

/-- **Witness for `proposition_15_1_3_hyp`**: all hypotheses hold for two maps on `ℝ` at
`x₀ = 0` (not isolated). -/
theorem proposition_15_1_3_hyp_witness :
    ∃ x : ℕ → ℝ, (∀ k, x k ≠ 0) ∧ (∀ k, x k ∈ (univ : Set ℝ)) ∧ Tendsto x atTop (𝓝 0) ∧
      ∃ (p : ℕ) (e : Fin 2 → Fin p), Surjective e ∧
        ∀ k, IsSeparatedAt (fun (i : Fin 2) (z : ℝ) => (i : ℝ) * z) e (x k) :=
  proposition_15_1_3_hyp _ isOpen_univ (fun _ => by fun_prop) (mem_univ 0) inferInstance

/-- **Proposition 15.1.3 for a one-point local model**: there is no sequence `x_k ≠ 0`, `x_k → 0`
in a one-point `O` (`O = {0}`, a zero-dimensional `X`). -/
theorem not_proposition_15_1_3_point :
    ¬ ∃ x : ℕ → Unit, (∀ k, x k ≠ ()) ∧ Tendsto x atTop (𝓝 ()) :=
  not_proposition_15_1_3_of_isolated (isOpen_discrete _)

/-- **Remark 15.1.6, first part (no 2017 number), p. 686**: starting from any sequence
`x'_k → x₀` in `V`, there are points `x''_k ∈ V` with `d(x'_k, x''_k) < 1/(k+1)` (so
`d(x'_k, x''_k) → 0` and `x''_k → x₀`) and a subsequence of `(x''_k)` with the properties of
Proposition 15.1.3. -/
theorem remark_15_1_6 {Z : Type*} [MetricSpace Z] {ι : Type*} [Finite ι] (s : ι → Z → Y)
    {V : Set Z} (hV : IsOpen V) (hs : ∀ i, ContinuousOn (s i) V) {x₀ : Z} {x' : ℕ → Z}
    (hx' : Tendsto x' atTop (𝓝 x₀)) (hx'V : ∀ k, x' k ∈ V) :
    ∃ x'' : ℕ → Z, (∀ k, dist (x' k) (x'' k) < 1 / ((k : ℝ) + 1)) ∧ (∀ k, x'' k ∈ V) ∧
      Tendsto x'' atTop (𝓝 x₀) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ (p : ℕ) (e : ι → Fin p), Surjective e ∧ ∀ k, IsSeparatedAt s e (x'' (φ k)) := by
  have := Fintype.ofFinite ι
  have hpt : ∀ k : ℕ, ∃ z ∈ Metric.ball (x' k) (1 / ((k : ℝ) + 1)) ∩ V, IsLocDich s z :=
    fun k => exists_isLocDich_mem s (Metric.isOpen_ball.inter hV)
      ⟨x' k, Metric.mem_ball_self (by positivity), hx'V k⟩ fun i => (hs i).mono inter_subset_right
  choose z hzG hz using hpt
  have hd : ∀ k, dist (x' k) (z k) < 1 / ((k : ℝ) + 1) := fun k => by
    rw [dist_comm]; exact (hzG k).1
  refine ⟨z, hd, fun k => (hzG k).2, ?_, exists_isSeparatedAt_subseq s z hz⟩
  rw [tendsto_iff_dist_tendsto_zero] at hx' ⊢
  refine squeeze_zero (fun _ => dist_nonneg) (fun k => dist_triangle (z k) (x' k) x₀) ?_
  have h1 : Tendsto (fun k : ℕ => dist (z k) (x' k)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun k => by rw [dist_comm]; exact (hd k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using h1.add hx'

end Sequence

/-! ### The core of Theorem 15.1.1 -/

section Core

variable {Z Y Q M : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace Q] [T2Space Q] [AddCommMonoid M]

omit [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Q] [T2Space Q] in
/-- At a point where the branches are locally dichotomous, branches through a common value have
the same "derivative" (locality), so the formal sums of the pairs agree when the weighted counts
of the values agree. -/
theorem wsum_pair_eq_at_of_isLocDich {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ι ⊕ κ → Z → Y)
    (D : ι ⊕ κ → Z → Q) (σ : ι → M) (τ : κ → M) {u : Z} (hu : IsLocDich c u)
    (hloc : ∀ α β, c α =ᶠ[𝓝 u] c β → D α u = D β u)
    (hΛ : ∀ v, wsum (fun i => c (.inl i) u) σ v = wsum (fun j => c (.inr j) u) τ v)
    (q : Y × Q) :
    wsum (fun i => (c (.inl i) u, D (.inl i) u)) σ q =
      wsum (fun j => (c (.inr j) u, D (.inr j) u)) τ q := by
  obtain ⟨v, L⟩ := q
  have hsame : ∀ α β, c α u = v → c β u = v → D α u = D β u := fun α β hα hβ => by
    rcases hu α β with h | h
    · exact hloc α β h
    · exact absurd (hα.trans hβ.symm) h
  obtain ⟨L₀, hL₀⟩ : ∃ L₀, ∀ α, c α u = v → D α u = L₀ := by
    by_cases h : ∃ α, c α u = v
    · obtain ⟨α₀, h₀⟩ := h
      exact ⟨D α₀ u, fun α hα => hsame α α₀ hα h₀⟩
    · exact ⟨L, fun α hα => (h ⟨α, hα⟩).elim⟩
  rw [wsum_pair_of_const _ _ σ v L L₀ (fun i hi => hL₀ _ hi),
    wsum_pair_of_const _ _ τ v L L₀ (fun j hj => hL₀ _ hj), hΛ v]

/-- **The core of Theorem 15.1.1 (2017: Theorem 15.1), pp. 684–687**: two finite families of
branches `c (inl i)`, `c (inr j)` continuous on an open `V`, with weights `σ`, `τ` giving the same
weighted count of every value at every point of `V` (the two local section structures describe
the same `Λ`), and "derivatives" `D α` continuous on `V` and depending only on the germ of the
branch (`c α = c β` near `z` gives `D α z = D β z`): then at every `x₀ ∈ V` the finite formal
sums `∑ σᵢ · (value, derivative)` of the two families agree.  The proof is the text's: points
`u` near `x₀` where the branches are separated (Lemma 15.1.5), equality of the sums there, and
the limit (`wsum_eq_of_frequently`). -/
theorem wsum_pair_eq_of_isLocal {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ι ⊕ κ → Z → Y)
    (D : ι ⊕ κ → Z → Q) (σ : ι → M) (τ : κ → M) {V : Set Z} (hV : IsOpen V)
    (hc : ∀ α, ContinuousOn (c α) V) (hD : ∀ α, ContinuousOn (D α) V)
    (hΛ : ∀ z ∈ V, ∀ v, wsum (fun i => c (.inl i) z) σ v = wsum (fun j => c (.inr j) z) τ v)
    (hloc : ∀ z ∈ V, ∀ α β, c α =ᶠ[𝓝 z] c β → D α z = D β z) {x₀ : Z} (hx₀ : x₀ ∈ V)
    (q : Y × Q) :
    wsum (fun i => (c (.inl i) x₀, D (.inl i) x₀)) σ q =
      wsum (fun j => (c (.inr j) x₀, D (.inr j) x₀)) τ q := by
  have hcont : ∀ α, ContinuousAt (fun z => (c α z, D α z)) x₀ := fun α =>
    ((hc α).continuousAt (hV.mem_nhds hx₀)).prodMk ((hD α).continuousAt (hV.mem_nhds hx₀))
  refine wsum_eq_of_frequently (a := fun i z => (c (.inl i) z, D (.inl i) z))
    (b := fun j z => (c (.inr j) z, D (.inr j) z)) (fun i => hcont _) (fun j => hcont _) ?_ q
  rw [Filter.frequently_iff]
  intro N hN
  obtain ⟨u, ⟨huN, huV⟩, hu⟩ := exists_isLocDich_mem c (isOpen_interior.inter hV)
    ⟨x₀, mem_of_mem_nhds (interior_mem_nhds.2 hN), hx₀⟩ fun α => (hc α).mono inter_subset_right
  exact ⟨u, interior_subset huN, wsum_pair_eq_at_of_isLocDich c D σ τ hu (hloc u huV) (hΛ u huV)⟩

end Core

end Linearization15

end Polyfold
