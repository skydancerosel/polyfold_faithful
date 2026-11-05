import Polyfold.Chapter1.Degeneracy
import Polyfold.Chapter1.ExpositionLemmas

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1–3.2 and
Appendix 3.8.1: Definition 3.21 (good position), Proposition 3.22 (`N ∩ C` is a partial quadrant
in `N`), Lemma 3.45 (good position under linear isomorphisms), Lemma 3.65 and Proposition 3.69
(the degeneracy index of `N ∩ C`).

# Good position of a finite-dimensional subspace to a partial quadrant

## The text, paraphrased

(Definition 3.21) Let `C ⊆ E` be a partial quadrant and `N ⊆ E` a finite-dimensional sc-subspace.
`N` is **in good position** to `C` if the interior of `N ∩ C` in `N` is nonempty and `N` has an
sc-complement `P` (a **good complement**) with: for some `ε > 0`, `|p|₀ ≤ ε|n|₀` implies that
`n ∈ C` and `n + p ∈ C` are equivalent.  A finite-dimensional `N` which is not necessarily smooth
is called in good position if there is a merely topological complement with this property.
(Proposition 3.22, proof in Appendix 3.8.1) If `N` is in good position to `C` then `N ∩ C` is a
partial quadrant in `N`.  (Lemma 3.45) `Tϕ(0)` carries good position to good position.
(Lemma 3.65) A good complement lies in `ℝ^{Σᶜ} ⊕ W`, where `Σ = ⋃_{a ∈ C ∩ N, a ≠ 0} σ_a` is the set
of indices vanishing at some nonzero point of `N ∩ C`.  (Proposition 3.69) For `x ∈ N ∩ C`:
`d_{N ∩ C}(x) = d_C(x)` if `x ∉ N ∩ W`, and `d_{N ∩ C}(x) = dim N − dim(N ∩ W)` if `x ∈ N ∩ W`.

## What is formalized

* `Polyfold.IsGoodComplement`, `Polyfold.IsInGoodPosition` (**Definition 3.21**), with an algebraic
  complement (the weakest form; see below), finite-dimensionality as an instance argument.
* `Polyfold.exists_quadrantNormalForm` (the core, in coordinates): for functionals `ℓ_1, …, ℓ_n`
  on a normed space cutting out `C = {ℓ_i ≥ 0}`, and `N` in good position, a linear isomorphism
  `e : N ≅ ℝᵏ × N₀` with `N ∩ C = e⁻¹([0,∞)ᵏ × N₀)`, together with the degeneracy counts and
  `k = dim N − dim(N ∩ W)` (`Polyfold.QuadrantNormalForm`).
* `Polyfold.proposition_3_22` (**Proposition 3.22**): `N ∩ C` is a partial quadrant in `N`, as
  `IsPartialQuadrant (ScBanach.const N) (Subtype.val ⁻¹' C)`.
* `Polyfold.lemma_3_65` (**Lemma 3.65**), `Polyfold.sigmaCoord_surjective` (the surjectivity of
  the map (55), p. 125), `Polyfold.IsGoodComplement.map`, `Polyfold.IsInGoodPosition.map`
  (**Lemma 3.45**, for any continuous linear isomorphism carrying `C` onto `C'`),
  `Polyfold.proposition_3_69` (**Proposition 3.69**, in the model `E = ℝⁿ ⊕ W`, `C = [0,∞)ⁿ ⊕ W`
  as in the text; (2) stated additively).

## What the text leaves implicit, and the choices made (the findings)

* **The extreme-ray lemmas are not needed.**  The text's proof of Proposition 3.22 (Appendix 3.8.1)
  rests on Lemmas 3.62–3.64 (Krein–Milman for cones, quadrants have `dim N` extreme rays, cited
  from [21] without proof) and Lemmas 3.66–3.68.  The proof here follows the same two cases
  (`Ñ ∩ (ℝ^{Σᶜ} ⊕ W) = {0}` or not, Lemma 3.68) but replaces the extreme rays by a direct
  argument: in the first case `N ∩ C = {x ∈ N | ℓ_i(x) ≥ 0, i ∈ Σ}` (`mem_quadCone_of_vanIdx`:
  moving from such an `x` towards an interior point `y` along `x + s·y`, the first point of `N ∩ C`
  met is nonzero, hence has positive coordinates outside `Σ`, so it was not the first), and the
  surjectivity of `Q : N → ℝ^Σ` from Lemma 3.65 gives `N ≅ ℝ^Σ × ker Q`; in the second case
  (`Σ = ∅`) every nonzero point of `N ∩ C` has all coordinates positive and a line argument shows
  `dim N = 1` (`quadrantNormalForm_of_vanIdx_empty`).  The case `N ∩ C = N` (all `ℓ_i` vanish on
  `N`, e.g. `N ⊆ W`), which the text's case distinction does not single out, is treated first.
* **Only the algebraic splitting `E₀ = N ⊕ P` is used**: neither the sc-structure of `P` nor its
  closedness enters Proposition 3.22, Lemma 3.45, Lemma 3.65 or Proposition 3.69.  The text's
  Lemma 3.66 (`Ñ` is in good position with good complement `(N ∩ W) ⊕ N^⊥`) is not needed either.
* **Proposition 3.69 (2)** `d_{N ∩ C}(x) = dim N − dim(N ∩ W)` is stated as
  `d_{N ∩ C}(x) + dim(N ∩ W) = dim N`; the subspace `N ∩ W` is `ker((x ↦ x.1) ∘ ι_N)`.  In the
  normal form the `ℝᵏ`-component of `e` vanishes on `N ∩ W` and `k = dim N − dim(N ∩ W)`.
* **Lemma 3.45** is stated for `Tϕ(0)`; it holds for any continuous linear isomorphism `S` with
  `S(C) = C'`, with `ε' = ε/(‖S‖‖S⁻¹‖ + 1)`.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

section Core

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}

/-- The cone `{x ∈ N | ℓ_i(x) ≥ 0 for all i}` of a subspace `N`, cut out by the functionals
`ℓ_i`: the set `N ∩ C` of Proposition 3.22 seen inside `N`. -/
def quadCone (ℓ : Fin n → V →ₗ[ℝ] ℝ) (N : Submodule ℝ V) : Set N := {x | ∀ i, 0 ≤ ℓ i (x : V)}

variable (ℓ : Fin n → V →ₗ[ℝ] ℝ) (N : Submodule ℝ V)

lemma mem_quadCone {x : N} : x ∈ quadCone ℓ N ↔ ∀ i, 0 ≤ ℓ i (x : V) := Iff.rfl

lemma zero_mem_quadCone : (0 : N) ∈ quadCone ℓ N := fun i => by simp

lemma smul_mem_quadCone {x : N} (hx : x ∈ quadCone ℓ N) {t : ℝ} (ht : 0 ≤ t) :
    t • x ∈ quadCone ℓ N :=
  fun i => by rw [Submodule.coe_smul, map_smul]; exact mul_nonneg ht (hx i)

lemma add_mem_quadCone {x y : N} (hx : x ∈ quadCone ℓ N) (hy : y ∈ quadCone ℓ N) :
    x + y ∈ quadCone ℓ N :=
  fun i => by rw [Submodule.coe_add, map_add]; exact add_nonneg (hx i) (hy i)

/-- The functional `ℓ_i` restricted to `N`. -/
def restrFun (i : Fin n) : N →ₗ[ℝ] ℝ := (ℓ i).comp N.subtype

@[simp] lemma restrFun_apply (i : Fin n) (x : N) : restrFun ℓ N i x = ℓ i (x : V) := rfl

lemma continuous_restrFun [FiniteDimensional ℝ N] (i : Fin n) : Continuous (restrFun ℓ N i) :=
  LinearMap.continuous_of_finiteDimensional _

lemma quadCone_isClosed [FiniteDimensional ℝ N] : IsClosed (quadCone ℓ N) := by
  have : quadCone ℓ N = ⋂ i, {x : N | 0 ≤ restrFun ℓ N i x} := by ext x; simp [quadCone]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_restrFun ℓ N i)

open scoped Classical in
/-- The set `Σ` of the proof of Proposition 3.22 (p. 123): the indices `i` for which some nonzero
`a ∈ N ∩ C` has `ℓ_i(a) = 0`. -/
def vanIdx : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x ∈ quadCone ℓ N, x ≠ 0 ∧ ℓ i (x : V) = 0

lemma mem_vanIdx {i : Fin n} :
    i ∈ vanIdx ℓ N ↔ ∃ x ∈ quadCone ℓ N, x ≠ 0 ∧ ℓ i (x : V) = 0 := by
  classical
  simp [vanIdx]

/-- Outside `Σ`, every nonzero element of the cone has a strictly positive coordinate. -/
lemma pos_of_not_mem_vanIdx {x : N} (hx : x ∈ quadCone ℓ N) (hx0 : x ≠ 0) {i : Fin n}
    (hi : i ∉ vanIdx ℓ N) : 0 < ℓ i (x : V) := by
  rcases (hx i).lt_or_eq with h | h
  · exact h
  · exact absurd ((mem_vanIdx ℓ N).2 ⟨x, hx, hx0, h.symm⟩) hi

/-- **Lemma 3.65**: a good complement `P` of `N` lies in `{x | ℓ_i(x) = 0 for all i ∈ Σ}`. -/
lemma lemma_3_65 (P : Submodule ℝ V) {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ x ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ →
      ((∀ i, 0 ≤ ℓ i x) ↔ ∀ i, 0 ≤ ℓ i (x + p)))
    {p : V} (hp : p ∈ P) {i : Fin n} (hi : i ∈ vanIdx ℓ N) : ℓ i p = 0 := by
  obtain ⟨a, ha, ha0, hai⟩ := (mem_vanIdx ℓ N).1 hi
  have hna : 0 < ‖(a : V)‖ := by
    rw [norm_pos_iff]; exact fun h => ha0 (Subtype.ext h)
  set lam : ℝ := ε * ‖(a : V)‖ / (‖p‖ + 1) with hlam
  have hlampos : 0 < lam := by rw [hlam]; positivity
  have hbound : ∀ q : V, ‖q‖ = ‖p‖ → ‖lam • q‖ ≤ ε * ‖(a : V)‖ := by
    intro q hq
    rw [norm_smul, Real.norm_of_nonneg hlampos.le, hq, hlam, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity)]
    have : 0 ≤ ε * ‖(a : V)‖ := by positivity
    nlinarith [norm_nonneg p]
  have h1 := (hgood a a.2 (lam • p) (P.smul_mem _ hp) (hbound p rfl)).1 ha i
  have h2 := (hgood a a.2 (lam • (-p)) (P.smul_mem _ (P.neg_mem hp)) (hbound (-p) (norm_neg p))).1
    ha i
  rw [map_add, hai, zero_add, map_smul, smul_eq_mul] at h1 h2
  rw [map_neg, mul_neg] at h2
  have h3 : lam * ℓ i p = 0 := le_antisymm (by linarith) h1
  exact (mul_eq_zero.1 h3).resolve_left hlampos.ne'

/-- The coordinates in `Σ`: `Q : N → ℝ^Σ`, `Q(x)_i = ℓ_i(x)` (the map (55) of the text, p. 125). -/
def sigmaCoord : N →ₗ[ℝ] (vanIdx ℓ N → ℝ) := LinearMap.pi fun i => restrFun ℓ N i.1

@[simp] lemma sigmaCoord_apply (x : N) (i : vanIdx ℓ N) : sigmaCoord ℓ N x i = ℓ i.1 (x : V) := rfl

/-- The subspace `N ∩ W = {x ∈ N | ℓ_i(x) = 0 for all i}` (the text identifies `W` with
`{0} ⊕ W`). -/
def nullSpace : Submodule ℝ N := ⨅ i, LinearMap.ker (restrFun ℓ N i)

lemma mem_nullSpace {x : N} : x ∈ nullSpace ℓ N ↔ ∀ i, ℓ i (x : V) = 0 := by
  simp [nullSpace, Submodule.mem_iInf, LinearMap.mem_ker]

/-- Surjectivity of `Q` (p. 125): for `k ∈ ℝ^Σ` write `(k, 0) = n + m ∈ N ⊕ N^⊥`; by Lemma 3.65,
`Q(n) = k`.  The hypothesis `hℓ` says that the `ℓ_i` are jointly surjective (coordinates). -/
lemma sigmaCoord_surjective (P : Submodule ℝ V) (hNP : IsCompl N P) {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ x ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ →
      ((∀ i, 0 ≤ ℓ i x) ↔ ∀ i, 0 ≤ ℓ i (x + p)))
    (hℓ : ∀ (s : Finset (Fin n)) (k : Fin n → ℝ), ∃ v : V, ∀ i ∈ s, ℓ i v = k i) :
    Function.Surjective (sigmaCoord ℓ N) := by
  intro k
  classical
  obtain ⟨v, hv⟩ := hℓ (vanIdx ℓ N) (fun i => if h : i ∈ vanIdx ℓ N then k ⟨i, h⟩ else 0)
  have hv' : v ∈ N ⊔ P := by rw [hNP.sup_eq_top]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv'
  refine ⟨⟨y, hy⟩, ?_⟩
  funext i
  have := hv i.1 i.2
  rw [map_add, lemma_3_65 ℓ N P hε hgood hz i.2, add_zero, dif_pos i.2] at this
  simpa using this

/-- An interior point of the cone with `ℓ_i(y) = 0` forces `ℓ_i = 0` on `N`. -/
lemma restrFun_eq_zero_of_interior {y : N} (hy : y ∈ interior (quadCone ℓ N)) {i : Fin n}
    (hyi : ℓ i (y : V) = 0) (u : N) : ℓ i (u : V) = 0 := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), y + t • u ∈ quadCone ℓ N := by
    have hc : Continuous fun t : ℝ => y + t • u := by fun_prop
    have h0 : (fun t : ℝ => y + t • u) 0 = y := by simp
    exact (hc.continuousAt (x := 0)).preimage_mem_nhds
      (by simpa using mem_interior_iff_mem_nhds.1 hy)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
  have hmem : ∀ t : ℝ, |t| < δ → 0 ≤ t * ℓ i (u : V) := by
    intro t ht
    have := hδ' (y := t) (by rwa [dist_zero_right, Real.norm_eq_abs]) i
    rwa [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, smul_eq_mul, hyi,
      zero_add] at this
  have h1 := hmem (δ / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  have h2 := hmem (-(δ / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
  nlinarith

/-- `N ∩ C = {x ∈ N | ℓ_i(x) ≥ 0 for i ∈ Σ}` when `Σ ≠ ∅` (the first case of the proof of
Proposition 3.22, p. 125, proved here directly instead of through extreme rays: move from `x`
towards an interior point `y` along `x + s·y`; the first point of the cone met on the way has all
coordinates outside `Σ` positive, so it was not the first). -/
lemma mem_quadCone_of_vanIdx [FiniteDimensional ℝ N] (hS : (vanIdx ℓ N).Nonempty)
    (hsurj : Function.Surjective (sigmaCoord ℓ N))
    (hint : (interior (quadCone ℓ N)).Nonempty) {x : N}
    (hx : ∀ i ∈ vanIdx ℓ N, 0 ≤ ℓ i (x : V)) : x ∈ quadCone ℓ N := by
  classical
  obtain ⟨i₀, hi₀⟩ := hS
  obtain ⟨u, hu⟩ := hsurj (Pi.single ⟨i₀, hi₀⟩ 1)
  have hu1 : ℓ i₀ (u : V) = 1 := by
    have := congrFun hu ⟨i₀, hi₀⟩
    simpa using this
  obtain ⟨y, hy⟩ := hint
  have hyD : y ∈ quadCone ℓ N := interior_subset hy
  have hy0 : 0 < ℓ i₀ (y : V) := by
    rcases (hyD i₀).lt_or_eq with h | h
    · exact h
    · have := restrFun_eq_zero_of_interior ℓ N hy h.symm u
      rw [hu1] at this; exact absurd this one_ne_zero
  have hyne : y ≠ 0 := fun h => by rw [h] at hy0; simp at hy0
  -- the set of parameters `s ≥ 0` with `x + s y` in the cone
  set T : Set ℝ := Ici (0 : ℝ) ∩ (fun s : ℝ => x + s • y) ⁻¹' quadCone ℓ N with hT
  have hcoord : ∀ (s : ℝ) (j : Fin n),
      ℓ j ((x + s • y : N) : V) = ℓ j (x : V) + s * ℓ j (y : V) := by
    intro s j
    rw [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, smul_eq_mul]
  have hT_ne : T.Nonempty := by
    have hev : ∀ᶠ s in atTop, ∀ j, j ∉ vanIdx ℓ N → 0 ≤ ℓ j (x : V) + s * ℓ j (y : V) := by
      rw [eventually_all]
      intro j
      by_cases hj : j ∈ vanIdx ℓ N
      · exact Eventually.of_forall fun _ h => absurd hj h
      · have hpos := pos_of_not_mem_vanIdx ℓ N hyD hyne hj
        filter_upwards [eventually_ge_atTop (-ℓ j (x : V) / ℓ j (y : V))] with s hs _
        rw [div_le_iff₀ hpos] at hs
        linarith
    obtain ⟨s, hs0, hs⟩ := ((eventually_ge_atTop (0 : ℝ)).and hev).exists
    refine ⟨s, hs0, fun j => ?_⟩
    rw [hcoord]
    by_cases hj : j ∈ vanIdx ℓ N
    · exact add_nonneg (hx j hj) (mul_nonneg hs0 (hyD j))
    · exact hs j hj
  have hT_closed : IsClosed T := by
    rw [hT]
    exact isClosed_Ici.inter ((quadCone_isClosed ℓ N).preimage
      (by fun_prop : Continuous fun s : ℝ => x + s • y))
  have hT_bdd : BddBelow T := ⟨0, fun s hs => hs.1⟩
  have hsT : sInf T ∈ T := hT_closed.csInf_mem hT_ne hT_bdd
  have hs_eq : sInf T = 0 := by
    by_contra hne
    have hpos : 0 < sInf T := lt_of_le_of_ne hsT.1 (Ne.symm hne)
    have hz0 : x + sInf T • y ≠ 0 := by
      intro hz
      have h1 := hx i₀ hi₀
      have h2 := hcoord (sInf T) i₀
      rw [hz, Submodule.coe_zero, map_zero] at h2
      nlinarith
    have hev : ∀ᶠ s in 𝓝 (sInf T), ∀ j, j ∉ vanIdx ℓ N → 0 < ℓ j ((x + s • y : N) : V) := by
      rw [eventually_all]
      intro j
      by_cases hj : j ∈ vanIdx ℓ N
      · exact Eventually.of_forall fun _ h => absurd hj h
      · have hpos' := pos_of_not_mem_vanIdx ℓ N hsT.2 hz0 hj
        have hc : Continuous fun s : ℝ => ℓ j ((x + s • y : N) : V) :=
          (continuous_restrFun ℓ N j).comp (by fun_prop : Continuous fun s : ℝ => x + s • y)
        exact ((hc.tendsto (sInf T)).eventually_const_lt hpos').mono fun s hs _ => hs
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
    set s₁ : ℝ := max 0 (sInf T - δ / 2) with hs₁
    have hs₁lt : s₁ < sInf T := max_lt hpos (by linarith)
    have hdist : dist s₁ (sInf T) < δ := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith)]
      linarith [le_max_right 0 (sInf T - δ / 2)]
    have hs₁T : s₁ ∈ T := by
      refine ⟨show (0 : ℝ) ≤ s₁ from le_max_left _ _, fun j => ?_⟩
      by_cases hj : j ∈ vanIdx ℓ N
      · rw [hcoord]; exact add_nonneg (hx j hj) (mul_nonneg (le_max_left _ _) (hyD j))
      · exact (hδ' hdist j hj).le
    exact absurd (csInf_le hT_bdd hs₁T) (not_le.2 hs₁lt)
  have := hsT.2
  rw [hs_eq] at this
  simpa using this

/-- The splitting `M₁ ≅ M₂ × ker Q` given by a linear right inverse `g` of `Q`. -/
def splitEquiv {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℝ M₁] [AddCommGroup M₂] [Module ℝ M₂]
    (Q : M₁ →ₗ[ℝ] M₂) (g : M₂ →ₗ[ℝ] M₁) (hg : Q ∘ₗ g = LinearMap.id) :
    M₁ ≃ₗ[ℝ] M₂ × LinearMap.ker Q :=
  have hk : ∀ k, Q (g k) = k := fun k => by
    have := congrArg (fun f => f k) hg
    simpa using this
  LinearEquiv.ofLinearMap
    (Q.prod ((LinearMap.id - g ∘ₗ Q).codRestrict (LinearMap.ker Q) fun x => by
      simp [hk]))
    (g ∘ₗ LinearMap.fst ℝ M₂ (LinearMap.ker Q) +
      (LinearMap.ker Q).subtype ∘ₗ LinearMap.snd ℝ M₂ (LinearMap.ker Q))
    (by
      refine LinearMap.ext fun p => ?_
      refine Prod.ext ?_ (Subtype.ext ?_)
      · simp [hk, LinearMap.mem_ker.1 p.2.2]
      · simp [hk, LinearMap.mem_ker.1 p.2.2])
    (by refine LinearMap.ext fun x => ?_; simp)

@[simp] lemma splitEquiv_apply_fst {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℝ M₁] [AddCommGroup M₂]
    [Module ℝ M₂] (Q : M₁ →ₗ[ℝ] M₂) (g : M₂ →ₗ[ℝ] M₁) (hg : Q ∘ₗ g = LinearMap.id) (x : M₁) :
    (splitEquiv Q g hg x).1 = Q x := rfl

/-- The conclusion of the core of Proposition 3.22, in coordinates: `N ≅ ℝᵏ × N₀` carrying the
cone onto `[0,∞)ᵏ × N₀`, with the degeneracy counts (Proposition 3.69) and
`k = dim N − dim(N ∩ W)`. -/
def QuadrantNormalForm [FiniteDimensional ℝ N] : Prop :=
  ∃ (k : ℕ) (N₀ : Submodule ℝ N) (e : N ≃ₗ[ℝ] (Fin k → ℝ) × N₀),
    (∀ x : N, x ∈ quadCone ℓ N ↔ ∀ j, 0 ≤ (e x).1 j) ∧
    (∀ x ∈ quadCone ℓ N, x ∉ nullSpace ℓ N →
      (Finset.univ.filter fun j => (e x).1 j = 0).card =
        (Finset.univ.filter fun i => ℓ i (x : V) = 0).card) ∧
    (∀ x : N, (e x).1 = 0 ↔ x ∈ nullSpace ℓ N) ∧
    k + finrank ℝ (nullSpace ℓ N) = finrank ℝ N

/-- The first case of the proof of Proposition 3.22: `N ∩ C = {ℓ_i ≥ 0, i ∈ Σ}` and `Q : N → ℝ^Σ`
is onto; then `N ≅ ℝ^Σ × ker Q` carries `N ∩ C` onto `[0,∞)^Σ × ker Q`. -/
lemma quadrantNormalForm_of_vanIdx [FiniteDimensional ℝ N]
    (hsurj : Function.Surjective (sigmaCoord ℓ N))
    (hD : ∀ x : N, (∀ i ∈ vanIdx ℓ N, 0 ≤ ℓ i (x : V)) → x ∈ quadCone ℓ N)
    (hker : LinearMap.ker (sigmaCoord ℓ N) = nullSpace ℓ N) : QuadrantNormalForm ℓ N := by
  classical
  obtain ⟨g, hg⟩ := (sigmaCoord ℓ N).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hsurj)
  let ι : Fin (Fintype.card (vanIdx ℓ N)) ≃ vanIdx ℓ N := (Fintype.equivFin (vanIdx ℓ N)).symm
  let e : N ≃ₗ[ℝ] (Fin (Fintype.card (vanIdx ℓ N)) → ℝ) × LinearMap.ker (sigmaCoord ℓ N) :=
    (splitEquiv (sigmaCoord ℓ N) g hg).trans
      ((LinearEquiv.funCongrLeft ℝ ℝ ι).prodCongr (LinearEquiv.refl ℝ _))
  have he : ∀ (x : N) (j), (e x).1 j = ℓ (ι j).1 (x : V) := fun x j => rfl
  refine ⟨Fintype.card (vanIdx ℓ N), LinearMap.ker (sigmaCoord ℓ N), e, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx j; rw [he]; exact hx _
    · intro hx
      refine hD x fun i hi => ?_
      have := hx (ι.symm ⟨i, hi⟩)
      rwa [he, Equiv.apply_symm_apply] at this
  · intro x hx hxW
    have hx0 : x ≠ 0 := fun h => hxW (by rw [h]; exact Submodule.zero_mem _)
    rw [Finset.card_equiv ι (t := Finset.univ.filter fun i : vanIdx ℓ N => ℓ i.1 (x : V) = 0)
      (fun j => by simp [he])]
    refine Finset.card_bij (fun i _ => i.1) (fun i hi => ?_) (fun i₁ _ i₂ _ h => Subtype.ext h)
      (fun i hi => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hiS : i ∈ vanIdx ℓ N := by
        by_contra h
        exact absurd hi (pos_of_not_mem_vanIdx ℓ N hx hx0 h).ne'
      exact ⟨⟨i, hiS⟩, by simpa using hi, rfl⟩
  · intro x
    rw [← hker, LinearMap.mem_ker]
    constructor
    · intro hx
      funext i
      have := congrFun hx (ι.symm i)
      rw [he, Equiv.apply_symm_apply] at this
      simpa using this
    · intro hx
      funext j
      rw [he]
      have := congrFun hx (ι j)
      simpa using this
  · have h1 := e.finrank_eq
    rw [Module.finrank_prod, Module.finrank_fin_fun, hker] at h1
    exact h1.symm

/-- The case `N ∩ C = N` (all `ℓ_i` vanish on `N`): `k = 0`. -/
lemma quadrantNormalForm_of_eq_univ [FiniteDimensional ℝ N]
    (hDN : ∀ x : N, x ∈ quadCone ℓ N) : QuadrantNormalForm ℓ N := by
  have hvan : ∀ (x : N) (i : Fin n), ℓ i (x : V) = 0 := by
    intro x i
    have h1 := hDN x i
    have h2 := hDN (-x) i
    rw [Submodule.coe_neg, map_neg] at h2
    linarith
  refine ⟨0, ⊤, (LinearEquiv.ofTop ⊤ rfl).symm.trans
    (LinearEquiv.uniqueProd (R := ℝ) (M := (⊤ : Submodule ℝ N)) (M₂ := Fin 0 → ℝ)).symm,
    fun x => ⟨fun _ j => j.elim0, fun _ => hDN x⟩, fun x _ hx => ?_,
    fun x => ⟨fun _ => (mem_nullSpace ℓ N).2 (hvan x), fun _ => Subsingleton.elim _ _⟩, ?_⟩
  · exact absurd ((mem_nullSpace ℓ N).2 (hvan x)) hx
  · have : nullSpace ℓ N = ⊤ := by
      rw [eq_top_iff]; intro x _; exact (mem_nullSpace ℓ N).2 (hvan x)
    rw [this, finrank_top, zero_add]

/-- The second case of the proof of Proposition 3.22 (`Σ = ∅`, Lemma 3.68): every nonzero element
of `N ∩ C` has all coordinates positive, and then `N` is a line and `N ∩ C` a half-line. -/
lemma quadrantNormalForm_of_vanIdx_empty [FiniteDimensional ℝ N] (hS : vanIdx ℓ N = ∅)
    (j₀ : Fin n) (hint : (interior (quadCone ℓ N)).Nonempty)
    (hDN : ¬ ∀ x : N, x ∈ quadCone ℓ N) : QuadrantNormalForm ℓ N := by
  classical
  have hpos : ∀ x ∈ quadCone ℓ N, x ≠ 0 → ∀ j, 0 < ℓ j (x : V) := fun x hx hx0 j =>
    pos_of_not_mem_vanIdx ℓ N hx hx0 (by rw [hS]; exact Finset.notMem_empty j)
  obtain ⟨y, hy⟩ := hint
  have hyD : y ∈ quadCone ℓ N := interior_subset hy
  have hyne : y ≠ 0 := by
    rintro rfl
    apply hDN
    intro x
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), t • x ∈ quadCone ℓ N := by
      have hc : Continuous fun t : ℝ => t • x := by fun_prop
      exact (hc.continuousAt (x := 0)).preimage_mem_nhds
        (by simpa using mem_interior_iff_mem_nhds.1 hy)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
    have h := hδ' (y := δ / 2)
      (by rw [dist_zero_right, Real.norm_of_nonneg (by positivity)]; linarith)
    have := smul_mem_quadCone ℓ N h (t := (δ / 2)⁻¹) (by positivity)
    rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at this
  -- the ray lemma: a line through `y` avoiding `0` stays in the cone
  have hray : ∀ v : N, (∀ t : ℝ, y + t • v ≠ 0) → ∀ t : ℝ, 0 ≤ t → y + t • v ∈ quadCone ℓ N := by
    intro v hv
    by_contra hcon
    push Not at hcon
    obtain ⟨t₁, ht₁, ht₁D⟩ := hcon
    set T : Set ℝ := Icc 0 t₁ ∩ (fun t : ℝ => y + t • v) ⁻¹' quadCone ℓ N with hT
    have hT_closed : IsClosed T := by
      rw [hT]
      exact isClosed_Icc.inter ((quadCone_isClosed ℓ N).preimage
        (by fun_prop : Continuous fun t : ℝ => y + t • v))
    have hT_ne : T.Nonempty := ⟨0, ⟨le_rfl, ht₁⟩, by simpa using hyD⟩
    have hT_bdd : BddAbove T := ⟨t₁, fun t ht => ht.1.2⟩
    have hsT : sSup T ∈ T := hT_closed.csSup_mem hT_ne hT_bdd
    have hlt : sSup T < t₁ := lt_of_le_of_ne hsT.1.2 fun h => ht₁D (h ▸ hsT.2)
    have hz0 : y + sSup T • v ≠ 0 := hv _
    have hev : ∀ᶠ t in 𝓝 (sSup T), y + t • v ∈ quadCone ℓ N := by
      have : ∀ᶠ t in 𝓝 (sSup T), ∀ j, 0 < ℓ j ((y + t • v : N) : V) := by
        rw [eventually_all]
        intro j
        have hc : Continuous fun t : ℝ => ℓ j ((y + t • v : N) : V) :=
          (continuous_restrFun ℓ N j).comp (by fun_prop : Continuous fun t : ℝ => y + t • v)
        exact (hc.tendsto (sSup T)).eventually_const_lt (hpos _ hsT.2 hz0 j)
      exact this.mono fun t ht j => (ht j).le
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
    set t₂ := min t₁ (sSup T + δ / 2) with ht₂
    have ht₂gt : sSup T < t₂ := lt_min hlt (by linarith)
    have ht₂T : t₂ ∈ T := by
      refine ⟨⟨hsT.1.1.trans ht₂gt.le, min_le_left _ _⟩, hδ' ?_⟩
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [min_le_right t₁ (sSup T + δ / 2)]
    exact absurd (le_csSup hT_bdd ht₂T) (not_le.2 ht₂gt)
  -- every element of `N` is a multiple of `y`
  have hspan : ∀ v : N, ∃ t : ℝ, v = t • y := by
    intro v
    by_contra hcon
    push Not at hcon
    have hv0 : v ≠ 0 := fun h => hcon 0 (by rw [h, zero_smul])
    have hv : ∀ t : ℝ, y + t • v ≠ 0 := by
      intro t h
      have ht : t ≠ 0 := by
        rintro rfl
        rw [zero_smul, add_zero] at h
        exact hyne h
      apply hcon (-t⁻¹)
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      calc v + t⁻¹ • y = t⁻¹ • (y + t • v) := by
            rw [smul_add, smul_smul, inv_mul_cancel₀ ht, one_smul, add_comm]
        _ = 0 := by rw [h, smul_zero]
    have hv' : ∀ t : ℝ, y + t • (-v) ≠ 0 := fun t => by
      rw [smul_neg, ← neg_smul]; exact hv (-t)
    have hcoord : ∀ j, ℓ j (v : V) = 0 := by
      intro j
      have h1 : ∀ t : ℝ, 0 ≤ t → 0 ≤ ℓ j (y : V) + t * ℓ j (v : V) := fun t ht => by
        have := hray v hv t ht j
        rwa [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, smul_eq_mul] at this
      have h2 : ∀ t : ℝ, 0 ≤ t → 0 ≤ ℓ j (y : V) - t * ℓ j (v : V) := fun t ht => by
        have := hray (-v) hv' t ht j
        rwa [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_neg, map_add, map_smul, map_neg,
          smul_eq_mul, mul_neg, ← sub_eq_add_neg] at this
      by_contra hne
      have hy0 : 0 ≤ ℓ j (y : V) := hyD j
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have ht : 0 ≤ (ℓ j (y : V) + 1) / (-ℓ j (v : V)) := by
          apply div_nonneg <;> linarith
        have := h1 _ ht
        have hne' : -ℓ j (v : V) ≠ 0 := by linarith
        have hid : (ℓ j (y : V) + 1) / (-ℓ j (v : V)) * ℓ j (v : V) = -(ℓ j (y : V) + 1) := by
          field_simp
        rw [hid] at this
        linarith
      · have ht : 0 ≤ (ℓ j (y : V) + 1) / ℓ j (v : V) := by
          apply div_nonneg <;> linarith
        have := h2 _ ht
        rw [div_mul_cancel₀ _ hgt.ne'] at this
        linarith
    have hvD : v ∈ quadCone ℓ N := fun j => (hcoord j).ge
    have := hpos v hvD hv0 j₀
    rw [hcoord j₀] at this
    exact lt_irrefl _ this
  -- the line `ℝ ≅ N`, `t ↦ t • y`
  let f : ℝ →ₗ[ℝ] N := LinearMap.id.smulRight y
  have hf : Function.Bijective f := by
    refine ⟨fun t₁ t₂ h => smul_left_injective ℝ hyne (by simpa [f] using h), fun v => ?_⟩
    obtain ⟨t, ht⟩ := hspan v
    exact ⟨t, by simp [f, ht]⟩
  obtain ⟨eq, heqf⟩ : ∃ eq : ℝ ≃ₗ[ℝ] N, ∀ t, eq t = t • y :=
    ⟨LinearEquiv.ofBijective f hf, fun t => by simp [f]⟩
  have heq : ∀ x : N, x = eq.symm x • y := fun x => by rw [← heqf, eq.apply_symm_apply]
  have hy₀ : 0 < ℓ j₀ (y : V) := hpos y hyD hyne j₀
  have hcoord_eq : ∀ (x : N) (j : Fin n), ℓ j (x : V) = eq.symm x * ℓ j (y : V) := fun x j => by
    conv_lhs => rw [heq x]
    rw [Submodule.coe_smul, map_smul, smul_eq_mul]
  have hnull : nullSpace ℓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hx0
    have hxD : x ∈ quadCone ℓ N := fun j => ((mem_nullSpace ℓ N).1 hx j).ge
    have := hpos x hxD hx0 j₀
    rw [(mem_nullSpace ℓ N).1 hx j₀] at this
    exact lt_irrefl _ this
  let e : N ≃ₗ[ℝ] (Fin 1 → ℝ) × (⊥ : Submodule ℝ N) :=
    eq.symm.trans ((LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans
      (LinearEquiv.prodUnique (R := ℝ) (M := Fin 1 → ℝ) (M₂ := (⊥ : Submodule ℝ N))).symm)
  have he : ∀ (x : N) (j : Fin 1), (e x).1 j = eq.symm x := fun x j => rfl
  refine ⟨1, ⊥, e, fun x => ?_, fun x hx hxW => ?_, fun x => ?_, ?_⟩
  · constructor
    · intro hxD j
      rw [he]
      have := hxD j₀
      rw [hcoord_eq] at this
      by_contra hneg
      push Not at hneg
      nlinarith
    · intro h
      have ht := h 0
      rw [he] at ht
      rw [heq x]
      exact smul_mem_quadCone ℓ N hyD ht
  · have hx0 : x ≠ 0 := fun h => hxW (by rw [h]; exact Submodule.zero_mem _)
    have ht : eq.symm x ≠ 0 := fun h => hx0 (by rw [heq x, h, zero_smul])
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun j _ => by rw [he]; exact ht),
      Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun j _ => (hpos x hx hx0 j).ne')]
  · rw [hnull, Submodule.mem_bot]
    constructor
    · intro hx
      have := congrFun hx 0
      rw [he] at this
      rw [heq x, show eq.symm x = 0 from this, zero_smul]
    · intro hx; rw [hx]; simp
  · rw [hnull, finrank_bot, add_zero]
    have := eq.finrank_eq
    rw [Module.finrank_self] at this
    exact this

/-- **The core of Proposition 3.22 (and of Proposition 3.69), in coordinates.**  Let `V` be a real
normed space with functionals `ℓ_1, …, ℓ_n` which are jointly onto `ℝⁿ` (coordinates),
`C = {ℓ_i ≥ 0}`, and `N ⊆ V` a finite-dimensional subspace with an algebraic complement `P` such
that for some `ε > 0`, `‖p‖ ≤ ε‖x‖` (`x ∈ N`, `p ∈ P`) implies `x ∈ C ↔ x + p ∈ C`, and `N ∩ C` has nonempty
interior in `N`.  Then there are `k` and a subspace `N₀` of `N` and a linear isomorphism
`e : N ≅ ℝᵏ × N₀` with `N ∩ C = e⁻¹([0,∞)ᵏ × N₀)`; moreover, for `x ∈ N ∩ C` not in `N ∩ W`
the number of vanishing coordinates of `e(x)` is that of `x`, `e` vanishes on `N ∩ W` in the
`ℝᵏ`-component, and `k = dim N − dim(N ∩ W)`, where `N ∩ W = {x ∈ N | ℓ_i(x) = 0 ∀ i}`.

The proof follows the two cases of the text (p. 125: `Ñ ∩ (ℝ^{Σᶜ} ⊕ W) = {0}` or not) but avoids
Lemmas 3.62–3.64 and 3.66–3.68 (extreme rays): in the first case `N ∩ C = {ℓ_i ≥ 0, i ∈ Σ}` is
shown directly by a segment argument (`mem_quadCone_of_vanIdx`), and the surjectivity of
`Q : N → ℝ^Σ` (Lemma 3.65) gives the splitting; in the second case `N` is a line
(`quadrantNormalForm_of_vanIdx_empty`). -/
theorem exists_quadrantNormalForm [FiniteDimensional ℝ N] (P : Submodule ℝ V) (hNP : IsCompl N P)
    {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ x ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ →
      ((∀ i, 0 ≤ ℓ i x) ↔ ∀ i, 0 ≤ ℓ i (x + p)))
    (hℓ : ∀ (s : Finset (Fin n)) (k : Fin n → ℝ), ∃ v : V, ∀ i ∈ s, ℓ i v = k i)
    (hint : (interior (quadCone ℓ N)).Nonempty) : QuadrantNormalForm ℓ N := by
  classical
  by_cases hDN : ∀ x : N, x ∈ quadCone ℓ N
  · exact quadrantNormalForm_of_eq_univ ℓ N hDN
  have hsurj := sigmaCoord_surjective ℓ N P hNP hε hgood hℓ
  by_cases hcase : (vanIdx ℓ N).Nonempty ∨ ∀ i, i ∈ vanIdx ℓ N
  · have hD : ∀ x : N, (∀ i ∈ vanIdx ℓ N, 0 ≤ ℓ i (x : V)) → x ∈ quadCone ℓ N := by
      rcases hcase with hS | hall
      · exact fun x hx => mem_quadCone_of_vanIdx ℓ N hS hsurj hint hx
      · exact fun x hx i => hx i (hall i)
    have hker : LinearMap.ker (sigmaCoord ℓ N) = nullSpace ℓ N := by
      apply le_antisymm
      · intro x hx
        rw [LinearMap.mem_ker] at hx
        have hx' : ∀ i ∈ vanIdx ℓ N, ℓ i (x : V) = 0 := fun i hi => by
          have := congrFun hx ⟨i, hi⟩
          simpa using this
        rw [mem_nullSpace]
        by_cases hall : ∀ i, i ∈ vanIdx ℓ N
        · exact fun i => hx' i (hall i)
        · push Not at hall
          obtain ⟨j₀, hj₀⟩ := hall
          have hxD : x ∈ quadCone ℓ N := hD x fun i hi => (hx' i hi).ge
          have hxD' : -x ∈ quadCone ℓ N := hD (-x) fun i hi => by
            rw [Submodule.coe_neg, map_neg, hx' i hi, neg_zero]
          have hx0 : x = 0 := by
            by_contra h0
            have h1 := pos_of_not_mem_vanIdx ℓ N hxD h0 hj₀
            have h2 := pos_of_not_mem_vanIdx ℓ N hxD' (neg_ne_zero.2 h0) hj₀
            rw [Submodule.coe_neg, map_neg] at h2
            linarith
          intro i; rw [hx0]; simp
      · intro x hx
        rw [LinearMap.mem_ker]
        funext i
        exact (mem_nullSpace ℓ N).1 hx i.1
    exact quadrantNormalForm_of_vanIdx ℓ N hsurj hD hker
  · push Not at hcase
    obtain ⟨hS, j₀, -⟩ := hcase
    exact quadrantNormalForm_of_vanIdx_empty ℓ N hS j₀ hint hDN

end Core

section ScLevel

variable {E : ScBanach}

/-! ### Definition 3.21: good position -/

/-- **Definition 3.21**, the complement: `P` is a **good complement** of `N` with respect to
`C ⊆ E₀`: `E₀ = N ⊕ P` and there is `ε > 0` such that for `n ∈ N`, `p ∈ P` with `|p|₀ ≤ ε|n|₀`
the statements `n ∈ C` and `n + p ∈ C` are equivalent.  (The text asks for an sc-complement, or
"merely a topological complement" in the remark after the definition; the proofs use only the
algebraic splitting `E₀ = N ⊕ P`, which is what is required here.) -/
structure IsGoodComplement (E : ScBanach) (C : Set (E 0)) (N P : Submodule ℝ (E 0)) : Prop where
  isCompl : IsCompl N P
  exists_eps : ∃ ε > 0, ∀ x ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + p ∈ C)

/-- **Definition 3.21**: the subspace `N` is **in good position** to `C`: the interior of `N ∩ C`
in `N` is nonempty and `N` has a good complement.  Finite-dimensionality of `N` is a separate
instance argument of the theorems. -/
structure IsInGoodPosition (E : ScBanach) (C : Set (E 0)) (N : Submodule ℝ (E 0)) : Prop where
  interior_nonempty : (interior (Subtype.val ⁻¹' C : Set N)).Nonempty
  exists_goodComplement : ∃ P, IsGoodComplement E C N P

/-! ### Coordinates of a presentation -/

variable {n : ℕ} {W : ScBanach}

/-- The coordinate functionals `x ↦ (Tx)_i` of a presentation `T : E₀ ≅ ℝⁿ × W₀`. -/
def coordFun (T : E 0 ≃L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0) (i : Fin n) : E 0 →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp ((LinearMap.fst ℝ (Fin n → ℝ) (W 0)).comp (T : E 0 →ₗ[ℝ] _))

@[simp] lemma coordFun_apply (T : E 0 ≃L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0) (i : Fin n)
    (x : E 0) : coordFun T i x = (T x).1 i := rfl

lemma coordFun_surj (T : E 0 ≃L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0) (s : Finset (Fin n))
    (k : Fin n → ℝ) : ∃ v : E 0, ∀ i ∈ s, coordFun T i v = k i :=
  ⟨T.symm (k, 0), fun i _ => by simp⟩

lemma quadCone_coordFun (T : E 0 ≃L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0)
    (N : Submodule ℝ (E 0)) :
    quadCone (coordFun T) N = (Subtype.val ⁻¹' (T ⁻¹' quadrant n W 0) : Set N) := rfl

/-- A linear isomorphism `A ≅ ℝᵏ × B` of finite-dimensional spaces, as an sc-isomorphism of the
constant sc-structures. -/
def scIsoOfLinearEquiv {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] {k : ℕ}
    (e : A ≃ₗ[ℝ] (Fin k → ℝ) × B) :
    ScIso (ScBanach.const A) ((ScBanach.const (Fin k → ℝ)).prod (ScBanach.const B)) where
  lvl _ := e.toContinuousLinearEquiv
  incl_comm _ _ := rfl

@[simp] lemma scIsoOfLinearEquiv_apply {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] {k : ℕ}
    (e : A ≃ₗ[ℝ] (Fin k → ℝ) × B) (m : ℕ) (x : A) : scIsoOfLinearEquiv e m x = e x := rfl

/-- Good position in a presentation gives the normal form of `exists_quadrantNormalForm`. -/
theorem IsInGoodPosition.quadrantNormalForm (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
    (hN : IsInGoodPosition E (T 0 ⁻¹' quadrant n W 0) N) :
    QuadrantNormalForm (coordFun (T 0)) N := by
  obtain ⟨P, hP⟩ := hN.exists_goodComplement
  obtain ⟨ε, hε, hgood⟩ := hP.exists_eps
  exact exists_quadrantNormalForm (coordFun (T 0)) N P hP.isCompl hε hgood (coordFun_surj (T 0))
    hN.interior_nonempty

/-- The set `N ∩ C` in the normal form coordinates. -/
lemma preimage_eq_of_normalForm (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N] {k : ℕ} {N₀ : Submodule ℝ N}
    (e : N ≃ₗ[ℝ] (Fin k → ℝ) × N₀)
    (h1 : ∀ x : N, x ∈ quadCone (coordFun (T 0)) N ↔ ∀ j, 0 ≤ (e x).1 j) :
    (Subtype.val ⁻¹' (T 0 ⁻¹' quadrant n W 0) : Set N) =
      scIsoOfLinearEquiv e 0 ⁻¹' quadrant k (ScBanach.const N₀) 0 := by
  ext x
  rw [← quadCone_coordFun, h1 x]
  rfl

/-- **Proposition 3.22**: if the finite-dimensional subspace `N` is in good position to the partial
quadrant `C` in `E`, then `N ∩ C` is a partial quadrant in `N`.  (Proof in Appendix 3.8.1; here by
`exists_quadrantNormalForm`, without the extreme-ray Lemmas 3.62–3.64.) -/
theorem proposition_3_22 {C : Set (E 0)} (hC : IsPartialQuadrant E C) {N : Submodule ℝ (E 0)}
    [FiniteDimensional ℝ N] (hN : IsInGoodPosition E C N) :
    IsPartialQuadrant (ScBanach.const N) (Subtype.val ⁻¹' C) := by
  obtain ⟨n, W, T, rfl⟩ := hC
  obtain ⟨k, N₀, e, h1, -, -, -⟩ := hN.quadrantNormalForm T
  exact ⟨k, ScBanach.const N₀, scIsoOfLinearEquiv e, preimage_eq_of_normalForm T e h1⟩

/-! ### Lemma 3.45: good position is carried by linear isomorphisms -/

/-- **Lemma 3.45** (in its linear form): a continuous linear isomorphism `S : E₀ → E'₀` with
`S(C) = C'` carries a good complement of `N` to a good complement of `S(N)`; the constant is
`ε' = ε / (‖S‖‖S⁻¹‖ + 1)` (the text: `ε'‖Tϕ(0)‖‖Tϕ(0)⁻¹‖ ≤ ε`). -/
theorem IsGoodComplement.map {E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}
    (S : E 0 ≃L[ℝ] E' 0) (hS : ∀ x, x ∈ C ↔ S x ∈ C') {N P : Submodule ℝ (E 0)}
    (h : IsGoodComplement E C N P) :
    IsGoodComplement E' C' (N.map (S : E 0 →ₗ[ℝ] E' 0)) (P.map (S : E 0 →ₗ[ℝ] E' 0)) where
  isCompl := by
    have hinj : Function.Injective (S : E 0 →ₗ[ℝ] E' 0) := S.injective
    refine IsCompl.of_eq ?_ ?_
    · rw [← Submodule.map_inf _ hinj, h.isCompl.inf_eq_bot, Submodule.map_bot]
    · rw [← Submodule.map_sup, h.isCompl.sup_eq_top, Submodule.map_top]
      exact LinearMap.range_eq_top.2 S.surjective
  exists_eps := by
    obtain ⟨ε, hε, hgood⟩ := h.exists_eps
    set c : ℝ := ‖(S : E 0 →L[ℝ] E' 0)‖ * ‖(S.symm : E' 0 →L[ℝ] E 0)‖ + 1 with hc
    have hcpos : 0 < c := by positivity
    refine ⟨ε / c, by positivity, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨p, hp, rfl⟩ hle
    change ‖S p‖ ≤ ε / c * ‖S x‖ at hle
    have hp' : ‖p‖ ≤ ε * ‖x‖ := by
      have h1 : ‖p‖ ≤ ‖(S.symm : E' 0 →L[ℝ] E 0)‖ * ‖S p‖ := by
        have := (S.symm : E' 0 →L[ℝ] E 0).le_opNorm (S p)
        simpa using this
      have h2 : ‖S x‖ ≤ ‖(S : E 0 →L[ℝ] E' 0)‖ * ‖x‖ := (S : E 0 →L[ℝ] E' 0).le_opNorm x
      have h3 : ‖(S.symm : E' 0 →L[ℝ] E 0)‖ * (ε / c * ‖(S : E 0 →L[ℝ] E' 0)‖) ≤ ε := by
        have heq : ‖(S.symm : E' 0 →L[ℝ] E 0)‖ * (ε / c * ‖(S : E 0 →L[ℝ] E' 0)‖) =
            ε / c * (‖(S : E 0 →L[ℝ] E' 0)‖ * ‖(S.symm : E' 0 →L[ℝ] E 0)‖) := by ring
        rw [heq]
        calc ε / c * (‖(S : E 0 →L[ℝ] E' 0)‖ * ‖(S.symm : E' 0 →L[ℝ] E 0)‖) ≤ ε / c * c := by
              gcongr; rw [hc]; linarith
          _ = ε := div_mul_cancel₀ ε hcpos.ne'
      calc ‖p‖ ≤ ‖(S.symm : E' 0 →L[ℝ] E 0)‖ * ‖S p‖ := h1
        _ ≤ ‖(S.symm : E' 0 →L[ℝ] E 0)‖ * (ε / c * (‖(S : E 0 →L[ℝ] E' 0)‖ * ‖x‖)) := by
          gcongr
          exact hle.trans (by gcongr)
        _ = ‖(S.symm : E' 0 →L[ℝ] E 0)‖ * (ε / c * ‖(S : E 0 →L[ℝ] E' 0)‖) * ‖x‖ := by ring
        _ ≤ ε * ‖x‖ := by gcongr
    have := hgood x hx p hp hp'
    rw [hS, hS, map_add] at this
    exact this

/-- **Lemma 3.45**, second part: good position is carried by `S`. -/
theorem IsInGoodPosition.map {E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}
    (S : E 0 ≃L[ℝ] E' 0) (hS : ∀ x, x ∈ C ↔ S x ∈ C') {N : Submodule ℝ (E 0)}
    [FiniteDimensional ℝ N] (h : IsInGoodPosition E C N) :
    IsInGoodPosition E' C' (N.map (S : E 0 →ₗ[ℝ] E' 0)) where
  interior_nonempty := by
    obtain ⟨y, hy⟩ := h.interior_nonempty
    let φ : N ≃ₗ[ℝ] N.map (S : E 0 →ₗ[ℝ] E' 0) :=
      Submodule.equivMapOfInjective (S : E 0 →ₗ[ℝ] E' 0) S.injective N
    let ψ := φ.toContinuousLinearEquiv.toHomeomorph
    have hpre : ψ ⁻¹' (Subtype.val ⁻¹' C' : Set (N.map (S : E 0 →ₗ[ℝ] E' 0))) =
        (Subtype.val ⁻¹' C : Set N) := by
      ext z
      simp only [mem_preimage]
      rw [hS]
      rfl
    refine ⟨ψ y, ?_⟩
    rw [← mem_preimage, ψ.preimage_interior, hpre]
    exact hy
  exists_goodComplement :=
    let ⟨P, hP⟩ := h.exists_goodComplement
    ⟨P.map (S : E 0 →ₗ[ℝ] E' 0), hP.map S hS⟩

/-! ### Proposition 3.69: the degeneracy index of `N ∩ C` -/

/-- **Proposition 3.69**: for `N` in good position to `C = [0,∞)ⁿ ⊕ W` in `E = ℝⁿ ⊕ W` and
`x ∈ N ∩ C`: (1) `d_{N ∩ C}(x) = d_C(x)` if `x ∉ N ∩ W`; (2) `d_{N ∩ C}(x) = dim N − dim(N ∩ W)` if
`x ∈ N ∩ W` (here `W` is identified with `{0} ⊕ W`, and (2) is stated additively). -/
theorem proposition_3_69 {N : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)}
    [FiniteDimensional ℝ N] (hN : IsInGoodPosition _ (quadrant n W 0) N) {x : N}
    (hx : (x : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈ quadrant n W 0) :
    ((x : (Fin n → ℝ) × W 0).1 ≠ 0 →
      degIndex (ScBanach.const N) (Subtype.val ⁻¹' quadrant n W 0) x =
        degIndex _ (quadrant n W 0) x) ∧
    ((x : (Fin n → ℝ) × W 0).1 = 0 →
      degIndex (ScBanach.const N) (Subtype.val ⁻¹' quadrant n W 0) x +
        finrank ℝ (LinearMap.ker ((LinearMap.fst ℝ (Fin n → ℝ) (W 0)).comp N.subtype)) =
          finrank ℝ N) := by
  classical
  set E := (ScBanach.const (Fin n → ℝ)).prod W
  have hN' : IsInGoodPosition E ((ScIso.refl E) 0 ⁻¹' quadrant n W 0) N := hN
  obtain ⟨k, N₀, e, h1, h2, h3, h4⟩ := hN'.quadrantNormalForm (ScIso.refl E)
  have hT := preimage_eq_of_normalForm (ScIso.refl E) e h1
  have hdeg : degIndex (ScBanach.const N) (Subtype.val ⁻¹' quadrant n W 0) x =
      (Finset.univ.filter fun j => (e x).1 j = 0).card := by
    rw [show (Subtype.val ⁻¹' quadrant n W 0 : Set N) =
      Subtype.val ⁻¹' ((ScIso.refl E) 0 ⁻¹' quadrant n W 0) from rfl,
      degIndex_eq (scIsoOfLinearEquiv e) hT hx]
    rfl
  have hnull : nullSpace (coordFun ((ScIso.refl E) 0)) N =
      LinearMap.ker ((LinearMap.fst ℝ (Fin n → ℝ) (W 0)).comp N.subtype) := by
    ext z
    rw [mem_nullSpace, LinearMap.mem_ker]
    change (∀ i, (z : (Fin n → ℝ) × W 0).1 i = 0) ↔ (z : (Fin n → ℝ) × W 0).1 = 0
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  refine ⟨fun hx1 => ?_, fun hx1 => ?_⟩
  · rw [hdeg, degIndex_quadrant hx]
    refine h2 x hx fun hmem => hx1 ?_
    rw [hnull, LinearMap.mem_ker] at hmem
    exact hmem
  · have hmem : x ∈ nullSpace (coordFun ((ScIso.refl E) 0)) N := by
      rw [hnull, LinearMap.mem_ker]; exact hx1
    rw [hdeg, (h3 x).2 hmem, ← hnull, ← h4]
    congr 1
    simp

end ScLevel

end Polyfold
