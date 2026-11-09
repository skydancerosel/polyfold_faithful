import Polyfold.Chapter1.ScSmooth

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.3,
Definition 1.3.3 (preprint 1.23) and Lemma 1.3.4 (preprint 1.24), with the proof of Appendix §1.4.3.

# The degeneracy index of a partial quadrant

## The text, paraphrased

Let `C` be a partial quadrant in `E` and `T : E → ℝᵏ ⊕ W` an sc-isomorphism with
`T(C) = [0,∞)ᵏ ⊕ W`.  For `x ∈ C` write `T(x) = (a₁, …, a_k, w)` and set
`d_C(x) = #{i | a_i = 0}`.  (Definition 1.3.3 (preprint 1.23)) `d_C : C → ℕ₀` is the degeneracy index; points with
`d_C = 0` are interior, `d_C = 1` boundary points, `d_C ≥ 2` corners.  (Lemma 1.3.4 (preprint 1.24)) `d_C` does not
depend on `T`.  (§1.4.3) *Proof*: for a second `T' : E → ℝᵏ' ⊕ W'`, `S = T' ∘ T⁻¹` is an
sc-isomorphism with `S([0,∞)ᵏ ⊕ W) = [0,∞)ᵏ' ⊕ W'`.  Since `S(0, tw) = t S(0, w)` lies in the
quadrant for all `t ∈ ℝ`, `S({0} ⊕ W) = {0} ⊕ W'`, and comparing codimensions `k = k'`.  For
`x ∈ [0,∞)ᵏ ⊕ W` let `I(x) = {i | x_i = 0}` and `E_x = {(b, v) | b_i = 0 for i ∈ I(x)}`, of
codimension `#I(x)`.  For `u ∈ E_x`, `x + tu` is in the quadrant for `|t|` small, so
`S(x) + tS(u)` is in the quadrant, which forces `S(u)_i = 0` for `i ∈ I'(S x)`.  Hence
`S(E_x) ⊆ E'_{S x}`, so `S(E_x) = E'_{S x}`, and the codimensions agree: `#I(x) = #I'(S x)`.

## What is formalized

* `Polyfold.quadrantDeg p = #{i | p.1 i = 0}` for `p ∈ ℝⁿ ⊕ W`, and
  `Polyfold.degIndexWith T x = quadrantDeg (T x)` for an sc-isomorphism `T` presenting `C`.
* `Polyfold.lemma_1_3_4` (**Lemma 1.3.4 (preprint 1.24)**): `degIndexWith T x = degIndexWith T' x` for `x ∈ C` and
  any two presentations `T`, `T'` of `C`.  `Polyfold.lemma_1_3_4_dim`: the number `k` of
  half-line factors is also independent of `T` (the text's `k = k'`).
* `Polyfold.degIndex E C x` (**Definition 1.3.3 (preprint 1.23)**): `d_C(x)`, defined through an arbitrary
  presentation; `Polyfold.degIndex_eq` identifies it with `degIndexWith T x` for every `T`.

## What the text leaves implicit, and the choices made

* The proof of the index equality does not use `k = k'`; the latter is the index at `x = 0`
  (`I(0)` is everything), so it is derived from the main statement rather than proved first.
* The codimension of `E_x` is made precise as `finrank (V ⧸ E_x) = #I(x)`, `E_x` being the kernel
  of the surjection `(b, v) ↦ (b_i)_{i ∈ I(x)}`; `S` induces a linear isomorphism of the quotients
  (`Submodule.Quotient.equiv`).
* "`x + tu` in the quadrant for `|t|` small" is proved as an `∀ᶠ t in 𝓝 0` statement, coordinate
  by coordinate (finitely many coordinates), rather than with an explicit bound.
* Only the base level of the sc-isomorphisms is used: Lemma 1.3.4 (preprint 1.24) holds for any continuous linear
  equivalence `S` of `ℝⁿ × W₀` onto `ℝⁿ' × W'₀` carrying the quadrant onto the quadrant; the
  sc-structure plays no role in it.
* Theorem 1.3.5 (preprint 1.25) (boundary recognition under local sc-diffeomorphisms), for which the text cites
  [20, Theorem 1.19], is proved in `Polyfold/Chapter2/DegeneracyIndex.lean`
  (`Polyfold.theorem_1_3_5`, for sc¹ germs), by the argument of §2.3 for the identity retraction,
  on top of the degeneracy index and Lemma 1.3.4 (preprint 1.24) of this file.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

variable {E : ScBanach}

/-- The number of vanishing half-line coordinates of `p ∈ ℝⁿ ⊕ W`. -/
def quadrantDeg {n : ℕ} {W : ScBanach} (p : ((ScBanach.const (Fin n → ℝ)).prod W) 0) : ℕ :=
  (Finset.univ.filter fun i => p.1 i = 0).card

/-- The degeneracy index of `x` computed with the presentation `T : E ≅ ℝⁿ ⊕ W` of a partial
quadrant. -/
def degIndexWith {n : ℕ} {W : ScBanach} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (x : E 0) : ℕ :=
  quadrantDeg (T 0 x)

section Core

variable {n n' : ℕ} {W W' : ScBanach}

/-- The base level `ℝⁿ × W₀` of `ℝⁿ ⊕ W`. -/
local macro "V" n:term:max W:term:max : term => `((((ScBanach.const (Fin $n → ℝ)).prod $W) 0))

/-- `E_p = {(b, v) | b_i = 0 whenever p_i = 0}`, as the kernel of `(b, v) ↦ (b_i)_{i ∈ I(p)}`. -/
private def coordMap (p : V n W) : (V n W) →ₗ[ℝ] ({i : Fin n // p.1 i = 0} → ℝ) where
  toFun u i := u.1 i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma coordMap_surjective (p : V n W) : Surjective (coordMap p) := by
  intro v
  classical
  refine ⟨((fun i => if h : p.1 i = 0 then v ⟨i, h⟩ else 0), 0), ?_⟩
  funext i
  change (if h : p.1 i.1 = 0 then v ⟨i.1, h⟩ else 0) = v i
  rw [dif_pos i.2]

/-- `finrank (V / E_p) = #I(p)`: `E_p` has codimension `quadrantDeg p`. -/
private lemma finrank_quotient_ker_coordMap (p : V n W) :
    finrank ℝ ((V n W) ⧸ LinearMap.ker (coordMap p)) = quadrantDeg p := by
  classical
  rw [(LinearMap.quotKerEquivRange (coordMap p)).finrank_eq,
    LinearMap.range_eq_top.2 (coordMap_surjective p), finrank_top,
    Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]
  rfl

private lemma mem_ker_coordMap {p u : V n W} :
    u ∈ LinearMap.ker (coordMap p) ↔ ∀ i, p.1 i = 0 → u.1 i = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.1 i.2

/-- If `0 ≤ t * c` for all `t` near `0` then `c = 0`. -/
private lemma eq_zero_of_eventually_nonneg_mul {c : ℝ} (h : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ t * c) :
    c = 0 := by
  obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.1 h
  have h1 := hε' (y := ε / 2)
    (by rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith)
  have h2 := hε' (y := -(ε / 2))
    (by rw [dist_zero_right, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]; linarith)
  rw [neg_mul] at h2
  nlinarith

/-- The sign argument of §1.4.3: for `p` in the quadrant and `u ∈ E_p`, `p + tu` is in the quadrant
for `|t|` small. -/
private lemma eventually_add_smul_mem_quadrant {p u : V n W} (hp : p ∈ quadrant n W 0)
    (hu : u ∈ LinearMap.ker (coordMap p)) :
    ∀ᶠ t : ℝ in 𝓝 0, p + t • u ∈ quadrant n W 0 := by
  rw [mem_ker_coordMap] at hu
  have : ∀ i : Fin n, ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ (p + t • u).1 i := by
    intro i
    by_cases hi : p.1 i = 0
    · exact Eventually.of_forall fun t => by
        change 0 ≤ p.1 i + t * u.1 i
        rw [hi, hu i hi, mul_zero, add_zero]
    · have hpos : 0 < p.1 i := lt_of_le_of_ne (hp i) (Ne.symm hi)
      have hcont : Tendsto (fun t : ℝ => p.1 i + t * u.1 i) (𝓝 0) (𝓝 (p.1 i)) := by
        have := (by fun_prop : Continuous fun t : ℝ => p.1 i + t * u.1 i).tendsto (0 : ℝ)
        simpa using this
      exact (hcont.eventually (lt_mem_nhds hpos)).mono fun t ht => le_of_lt ht
  exact (eventually_all.2 this).mono fun t ht i => ht i

/-- The key step: a linear equivalence carrying the quadrant onto the quadrant maps `E_p` into
`E'_{S p}`. -/
private lemma map_ker_coordMap_le (S : (V n W) ≃L[ℝ] (V n' W'))
    (hS : ∀ q, q ∈ quadrant n W 0 ↔ S q ∈ quadrant n' W' 0) {p : V n W} (hp : p ∈ quadrant n W 0)
    {u : V n W} (hu : u ∈ LinearMap.ker (coordMap p)) :
    S u ∈ LinearMap.ker (coordMap (S p)) := by
  rw [mem_ker_coordMap]
  intro i hi
  apply eq_zero_of_eventually_nonneg_mul
  refine (eventually_add_smul_mem_quadrant hp hu).mono fun t ht => ?_
  have := (hS _).1 ht i
  rw [map_add, map_smul] at this
  change 0 ≤ t * (S u).1 i
  have h' : (S p + t • S u).1 i = (S p).1 i + t * (S u).1 i := rfl
  rw [h', hi, zero_add] at this
  exact this

/-- **Lemma 1.3.4 (preprint 1.24)**, core form: a linear equivalence `S : ℝⁿ ⊕ W → ℝⁿ' ⊕ W'` carrying the quadrant
onto the quadrant preserves the number of vanishing half-line coordinates. -/
theorem quadrantDeg_eq_of_equiv (S : (V n W) ≃L[ℝ] (V n' W'))
    (hS : ∀ q, q ∈ quadrant n W 0 ↔ S q ∈ quadrant n' W' 0) {p : V n W}
    (hp : p ∈ quadrant n W 0) : quadrantDeg p = quadrantDeg (S p) := by
  have hmap : (LinearMap.ker (coordMap p)).map (S : (V n W) →ₗ[ℝ] (V n' W')) =
      LinearMap.ker (coordMap (S p)) := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact map_ker_coordMap_le S hS hp hu
    · intro v hv
      have hp' : S p ∈ quadrant n' W' 0 := (hS p).1 hp
      have hS' : ∀ q, q ∈ quadrant n' W' 0 ↔ S.symm q ∈ quadrant n W 0 := fun q => by
        rw [hS (S.symm q), ContinuousLinearEquiv.apply_symm_apply]
      have := map_ker_coordMap_le S.symm hS' hp' hv
      rw [ContinuousLinearEquiv.symm_apply_apply] at this
      exact ⟨S.symm v, this, by simp⟩
  rw [← finrank_quotient_ker_coordMap, ← finrank_quotient_ker_coordMap]
  exact (Submodule.Quotient.equiv _ _ S.toLinearEquiv hmap).finrank_eq

/-- The index of the origin is the number of half-line factors. -/
lemma quadrantDeg_zero : quadrantDeg (0 : V n W) = n := by
  simp [quadrantDeg]

end Core

/-- **Lemma 1.3.4 (preprint 1.24)**: the degeneracy index of `x ∈ C` does not depend on the sc-isomorphism `T`
presenting the partial quadrant `C`. -/
theorem lemma_1_3_4 {C : Set (E 0)} {n n' : ℕ} {W W' : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (T' : ScIso E ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hT' : C = T' 0 ⁻¹' quadrant n' W' 0) {x : E 0} (hx : x ∈ C) :
    degIndexWith T x = degIndexWith T' x := by
  let S := (T 0).symm.trans (T' 0)
  have hS : ∀ q, q ∈ quadrant n W 0 ↔ S q ∈ quadrant n' W' 0 := by
    intro q
    have h1 : (T 0).symm q ∈ C ↔ q ∈ quadrant n W 0 := by
      rw [hT, mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
    rw [← h1, hT', mem_preimage]
    rfl
  have hp : T 0 x ∈ quadrant n W 0 := by rwa [hT] at hx
  have := quadrantDeg_eq_of_equiv S hS hp
  rw [degIndexWith, degIndexWith, this]
  change quadrantDeg (T' 0 ((T 0).symm (T 0 x))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- The number `n` of half-line factors of a partial quadrant does not depend on the presentation
(the text's `k = k'`). -/
theorem lemma_1_3_4_dim {C : Set (E 0)} {n n' : ℕ} {W W' : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (T' : ScIso E ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hT' : C = T' 0 ⁻¹' quadrant n' W' 0) : n = n' := by
  have hx : (T 0).symm 0 ∈ C := by
    rw [hT, mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
    intro i; exact le_rfl
  have h := lemma_1_3_4 T T' hT hT' hx
  have hT0 : T 0 ((T 0).symm 0) = 0 := ContinuousLinearEquiv.apply_symm_apply _ _
  have hT'0 : T' 0 ((T 0).symm 0) = 0 := by
    have hx' := hx
    rw [hT'] at hx'
    -- `T'(T⁻¹ 0) = S 0 = 0` since `S` is linear
    change ((T 0).symm.trans (T' 0)) 0 = 0
    exact map_zero _
  rw [degIndexWith, degIndexWith, hT0, hT'0, quadrantDeg_zero, quadrantDeg_zero] at h
  exact h

open scoped Classical in
/-- **Definition 1.3.3 (preprint 1.23)**: the degeneracy index `d_C : C → ℕ₀` of a partial quadrant `C`, computed
with an arbitrary presentation `T : E ≅ ℝⁿ ⊕ W` (`0` if `C` is not a partial quadrant).  It is
independent of the presentation by Lemma 1.3.4 (preprint 1.24) (`degIndex_eq`). -/
def degIndex (E : ScBanach) (C : Set (E 0)) (x : E 0) : ℕ :=
  if h : IsPartialQuadrant E C then degIndexWith h.choose_spec.choose_spec.choose x else 0

theorem degIndex_eq {C : Set (E 0)} {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    {x : E 0} (hx : x ∈ C) : degIndex E C x = degIndexWith T x := by
  have h : IsPartialQuadrant E C := ⟨n, W, T, hT⟩
  rw [degIndex, dif_pos h]
  exact lemma_1_3_4 _ T h.choose_spec.choose_spec.choose_spec hT hx

/-- The degeneracy index of a point of the quadrant `[0,∞)ⁿ ⊕ W` itself. -/
lemma degIndex_quadrant {n : ℕ} {W : ScBanach} {p : ((ScBanach.const (Fin n → ℝ)).prod W) 0}
    (hp : p ∈ quadrant n W 0) :
    degIndex _ (quadrant n W 0) p = quadrantDeg p :=
  degIndex_eq (ScIso.refl _) (by ext; rfl) hp

end Polyfold
