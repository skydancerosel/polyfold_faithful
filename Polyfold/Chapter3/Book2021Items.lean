import Polyfold.Chapter3.GoodPosition
import Polyfold.Chapter3.NonVacuityCorner

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Chapter 3, Appendix 3.8.1.3 "Cones and Partial Quadrants in Infinite Dimensions" (pp. 145–149):
**Lemma 3.8.4** (p. 147), **Lemma 3.8.5** (p. 147), **Lemma 3.8.6** (p. 148) and **Corollary
3.8.7** (p. 149), all new in the 2021 edition, with the notions of p. 145 (closed convex cone,
extreme ray).  Numbers and pages are the 2021 text's.

# Good position and closed convex cones: the 2021 appendix lemmas

## The text, paraphrased

(p. 145) A closed convex cone `P` in a finite-dimensional `N` is a closed convex set with
`P ∩ (−P) = {0}` and `ℝ₊P = P`; an extreme ray is `ℝ₊x` with `x ∈ P ∖ {0}` such that `y ∈ P` and
`x − y ∈ P` imply `y ∈ ℝ₊x`.  In `E = ℝⁿ ⊕ W` with `C = [0, ∞)ⁿ ⊕ W`, for `a ∈ C` let `σ_a` be the
set of indices `i ≤ n` with `a_i = 0`.  Let `N` be a smooth finite-dimensional subspace in good
position to `C` with good complement `N^⊥`, and `Γ` the union of the `σ_a` over `0 ≠ a ∈ C ∩ N`.

(Lemma 3.8.4, p. 147) If `N ∩ C` is a closed convex cone: (1) `y ∈ N^⊥` has `y_i = 0` whenever
`i ∈ σ_a` for a generator `a` of an extreme ray; (2) `Γ` is the union `Γ'` of the `σ_a` over
generators of extreme rays; (3) `y_i = 0` for `y ∈ N^⊥` and `i ∈ Γ`.

(Lemma 3.8.5, p. 147) If `N ∩ C` is a closed convex cone, then either `N ⊆ ℝ^{Γᶜ} ⊕ W`, in which
case `dim N = 1` and `Γ = ∅`, or `N ∩ (ℝ^{Γᶜ} ⊕ W) = {0}`.

(Lemma 3.8.6, p. 148) With `P : N → ℝ^Γ` the coordinate projection: (1) if
`N ∩ (ℝ^{Γᶜ} ⊕ W) = {0}`, then `P` is a linear isomorphism carrying `N ∩ C` onto the quadrant
`Q_Γ`; (2) if `N ⊆ ℝ^{Γᶜ} ⊕ W`, then `(N, N ∩ C) ≅ (ℝ, ℝ₊)`.

(Corollary 3.8.7, p. 149) If `N` is in good position and `N ∩ C` is a closed convex cone, then
`N ∩ C` is a partial quadrant in `N`.

## What is formalized

* `Polyfold.IsClosedConvexCone`, `Polyfold.IsExtremeRayGen` (p. 145), with witnesses
  `isClosedConvexCone_Ici`, `isExtremeRayGen_one`.
* The setting: `E` with a presentation `T : E ≅ ℝⁿ ⊕ W` of `C = T⁻¹([0, ∞)ⁿ ⊕ W)` (the text's case
  is `T = id`); the coordinates `a_i = (Ta)_i` are `coordFun (T 0) i`, `N ∩ C ⊆ N` is
  `quadCone (coordFun (T 0)) N`, `Γ` is `vanIdx (coordFun (T 0)) N`, `P : N → ℝ^Γ` is
  `sigmaCoord (coordFun (T 0)) N`, and `N ∩ (ℝ^{Γᶜ} ⊕ W)` is its kernel.
* `Polyfold.exists_quadrantEquiv_of_pointed`: for `N` in good position with `N ∩ C` pointed,
  a linear isomorphism `N ≅ ℝ^{dim N}` carrying `N ∩ C` onto `[0, ∞)^{dim N}` (from the normal
  form `IsInGoodPosition.quadrantNormalForm`), and the generators `e⁻¹(e_j)` of its extreme rays.
* `Polyfold.lemma_3_8_4` (**Lemma 3.8.4**), `Polyfold.lemma_3_8_5`
  (**Lemma 3.8.5**, as the dichotomy), `Polyfold.lemma_3_8_6` (**Lemma 3.8.6 (1)**),
  `Polyfold.lemma_3_8_6_two` (**Lemma 3.8.6 (2)** for `N ≠ 0`),
  `Polyfold.corollary_3_8_7` (**Corollary 3.8.7**, with the sharper conclusion that
  `N ∩ C` is a quadrant of `N`).
* `Polyfold.lemma_3_8_5_not_literal`: the reading "`N ⊆ ℝ^{Γᶜ} ⊕ W` implies `dim N = 1`" of
  Lemma 3.8.5, and Lemma 3.8.6 (2) as printed, **do not hold as we read them for `N = {0}`** (which
  is in good position, with `N ∩ C = {0}` a closed convex cone and `N ⊆ ℝ^{Γᶜ} ⊕ W`).
* `Polyfold.halfLine_witness`: the hypotheses of Lemma 3.8.6 (2) with `N ≠ 0` are satisfiable
  (`N = E = ℝ`, `C = [0, ∞)`).

## What the text leaves implicit, and the choices made

* **Lemma 3.8.4 (1) and (3)** do not need the cone hypothesis: they are preprint Lemma 3.65
  (= 2021 Lemma 3.8.8, `lemma_3_8_8`).  **(2)** uses only `N ∩ C ∩ −(N ∩ C) = {0}`: the text's
  proof writes `a` as a sum of extreme-ray generators (Krein–Milman, Lemma 3.8.1, not formalized);
  here the normal form gives `N ∩ C ≅ [0, ∞)^{dim N}` directly, and for `0 ≠ a ∈ N ∩ C` with
  `a_i = 0` a generator `b = e⁻¹(e_j)` with `e(a)_j > 0` has `a − e(a)_j b ∈ N ∩ C`, which forces
  `b_i = 0`.
* **Lemma 3.8.5** is stated as the dichotomy `N ∩ (ℝ^{Γᶜ} ⊕ W) = {0}` or (`N ⊆ ℝ^{Γᶜ} ⊕ W`,
  `dim N = 1`, `Γ = ∅`), which is what the proof shows (it assumes `N ∩ (ℝ^{Γᶜ} ⊕ W) ≠ {0}`).
  If `Γ ≠ ∅`, a point of `N` with `x_i = 0` for `i ∈ Γ` lies in `N ∩ C` together with `−x`
  (`mem_quadCone_of_vanIdx`), so it is `0`; if `Γ = ∅` and `dim N ≥ 2`, two generators `b₀, b₁`
  have all coordinates positive, so `b₀ − t b₁ ∈ N ∩ C` for small `t > 0`, contradicting
  `N ∩ C ≅ [0, ∞)^{dim N}`.
* **Lemma 3.8.6 (1)** does not need the cone hypothesis; **(2)** needs `N ≠ 0`.
* "Smooth" subspaces and sc-complements: as in `IsInGoodPosition`, only the algebraic splitting
  `E₀ = N ⊕ N^⊥` is used.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### Closed convex cones and extreme rays (p. 145) -/

section Cones

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- **2021, p. 145 (new in the 2021 edition; preprint Appendix 3.8)**: a **closed convex cone** `K`
in a finite-dimensional space: a closed convex subset with `K ∩ (−K) = {0}` and `ℝ₊K = K`. -/
structure IsClosedConvexCone [TopologicalSpace M] (K : Set M) : Prop where
  isClosed : IsClosed K
  convex : Convex ℝ K
  inter_neg : K ∩ -K = {0}
  smul_mem : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K, t • x ∈ K

/-- **2021, p. 145**: `a` **generates an extreme ray** `ℝ₊a` of `K`: `a ∈ K ∖ {0}`, and `y ∈ K`,
`a − y ∈ K` imply `y ∈ ℝ₊a`. -/
def IsExtremeRayGen (K : Set M) (a : M) : Prop :=
  a ∈ K ∧ a ≠ 0 ∧ ∀ y ∈ K, a - y ∈ K → ∃ t : ℝ, 0 ≤ t ∧ y = t • a

lemma IsClosedConvexCone.eq_zero [TopologicalSpace M] {K : Set M} (hK : IsClosedConvexCone K)
    {x : M} (hx : x ∈ K) (hx' : -x ∈ K) : x = 0 := by
  have : x ∈ K ∩ -K := ⟨hx, by rwa [Set.mem_neg]⟩
  rw [hK.inter_neg] at this
  exact this

/-- Satisfiability: `[0, ∞)` is a closed convex cone in `ℝ`. -/
theorem isClosedConvexCone_Ici : IsClosedConvexCone (Ici (0 : ℝ)) where
  isClosed := isClosed_Ici
  convex := convex_Ici 0
  inter_neg := by
    ext x
    simp only [mem_inter_iff, mem_Ici, Set.mem_neg, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩; linarith
    · rintro rfl; simp
  smul_mem t ht x hx := mem_Ici.2 (smul_nonneg ht (mem_Ici.1 hx))

/-- Satisfiability: `1` generates the extreme ray `[0, ∞)` of `[0, ∞)`. -/
theorem isExtremeRayGen_one : IsExtremeRayGen (Ici (0 : ℝ)) 1 :=
  ⟨mem_Ici.2 zero_le_one, one_ne_zero,
    fun y hy _ => ⟨y, mem_Ici.1 hy, by rw [smul_eq_mul, mul_one]⟩⟩

variable {k : ℕ} (e : M ≃ₗ[ℝ] (Fin k → ℝ)) {K : Set M} (he : ∀ x, x ∈ K ↔ ∀ j, 0 ≤ e x j)
include he

/-- In a quadrant `K = e⁻¹[0, ∞)ᵏ`, `e⁻¹(e_j)` generates an extreme ray. -/
lemma isExtremeRayGen_symm_single (j : Fin k) : IsExtremeRayGen K (e.symm (Pi.single j 1)) := by
  classical
  refine ⟨(he _).2 fun j' => ?_, fun h => ?_, fun y hy hby => ⟨e y j, (he y).1 hy j, ?_⟩⟩
  · rw [LinearEquiv.apply_symm_apply, Pi.single_apply]
    split_ifs <;> norm_num
  · have := congrArg (fun z => e z j) h
    simp at this
  · apply e.injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    funext j'
    have h1 := (he y).1 hy j'
    have h2 := (he _).1 hby j'
    rw [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply, Pi.single_apply] at h2
    rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs with hj
    · rw [hj, mul_one]
    · rw [if_neg hj] at h2
      rw [mul_zero]; linarith

/-- In a quadrant `K = e⁻¹[0, ∞)ᵏ`, a nonzero `a ∈ K` has a coordinate `e(a)_j > 0` with
`a − e(a)_j e⁻¹(e_j) ∈ K`. -/
lemma exists_sub_single_mem {a : M} (ha : a ∈ K) (ha0 : a ≠ 0) :
    ∃ j, 0 < e a j ∧ a - e a j • e.symm (Pi.single j 1) ∈ K := by
  classical
  have hea : e a ≠ 0 := fun h => ha0 (e.injective (h.trans (map_zero e).symm))
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hea
  refine ⟨j, lt_of_le_of_ne ((he a).1 ha j) (Ne.symm hj), (he _).2 fun j' => ?_⟩
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  split_ifs with h
  · rw [h, mul_one, sub_self]
  · rw [mul_zero, sub_zero]; exact (he a).1 ha j'

end Cones

/-! ### The setting of Appendix 3.8.1.3 -/

section Appendix

variable {E : ScBanach} {n : ℕ} {W : ScBanach} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
  {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]

/-- **`N ∩ C` is a quadrant of `N` when it is pointed**: for `N` in good position to
`C = T⁻¹([0, ∞)ⁿ ⊕ W)` with `x, −x ∈ N ∩ C ⟹ x = 0`, a linear isomorphism `e : N ≅ ℝᵏ`,
`k = dim N`, carrying `N ∩ C` onto `[0, ∞)ᵏ` (the normal form `IsInGoodPosition.quadrantNormalForm`
with trivial `N₀`). -/
theorem exists_quadrantEquiv_of_pointed (hN : IsInGoodPosition E (T 0 ⁻¹' quadrant n W 0) N)
    (hpt : ∀ x : N, x ∈ quadCone (coordFun (T 0)) N → -x ∈ quadCone (coordFun (T 0)) N → x = 0) :
    ∃ e : N ≃ₗ[ℝ] (Fin (finrank ℝ N) → ℝ),
      ∀ x : N, x ∈ quadCone (coordFun (T 0)) N ↔ ∀ j, 0 ≤ e x j := by
  obtain ⟨k, N₀, e, h1, -, -, -⟩ := hN.quadrantNormalForm T
  -- `N₀ = 0`: `(0, z)` and `−(0, z)` both lie in the cone
  have hN₀ : ∀ z : N₀, z = 0 := by
    intro z
    have hx : e.symm (0, z) ∈ quadCone (coordFun (T 0)) N :=
      (h1 _).2 fun j => by rw [LinearEquiv.apply_symm_apply]; exact le_rfl
    have hx' : -e.symm (0, z) ∈ quadCone (coordFun (T 0)) N :=
      (h1 _).2 fun j => by
        rw [map_neg, LinearEquiv.apply_symm_apply]; simp
    have h0 := hpt _ hx hx'
    have := congrArg (fun x => (e x).2) h0
    simpa using this
  let L : N →ₗ[ℝ] (Fin k → ℝ) := (LinearMap.fst ℝ (Fin k → ℝ) N₀).comp e.toLinearMap
  have hL : Bijective L := by
    refine ⟨fun x y hxy => e.injective (Prod.ext hxy ?_), fun v => ⟨e.symm (v, 0), ?_⟩⟩
    · rw [hN₀ (e x).2, hN₀ (e y).2]
    · change (e (e.symm (v, 0))).1 = v
      rw [LinearEquiv.apply_symm_apply]
  let e' := LinearEquiv.ofBijective L hL
  have hk : finrank ℝ N = k := by rw [e'.finrank_eq, Module.finrank_fin_fun]
  subst hk
  exact ⟨e', fun x => h1 x⟩

/-- **2021 Lemma 3.8.4, p. 147 (new in the 2021 edition)**: `N` in good position to
`C = T⁻¹([0, ∞)ⁿ ⊕ W)` with good complement `N^⊥`, and `N ∩ C` a closed convex cone.  Then
(1) `y_i = 0` for `y ∈ N^⊥` and `i ∈ σ_a`, `a` a generator of an extreme ray of `N ∩ C`;
(2) `Γ = ⋃_{0 ≠ a ∈ N ∩ C} σ_a` equals `Γ' = ⋃_{a generator} σ_a`;
(3) `y_i = 0` for `y ∈ N^⊥` and `i ∈ Γ`.
((1) and (3) hold without the cone hypothesis: `lemma_3_8_8`.) -/
theorem lemma_3_8_4 (hN : IsInGoodPosition E (T 0 ⁻¹' quadrant n W 0) N)
    (hQ : IsClosedConvexCone (quadCone (coordFun (T 0)) N)) {P : Submodule ℝ (E 0)}
    (hP : IsGoodComplement E (T 0 ⁻¹' quadrant n W 0) N P) :
    (∀ y ∈ P, ∀ i, (∃ a, IsExtremeRayGen (quadCone (coordFun (T 0)) N) a ∧
      (T 0 (a : E 0)).1 i = 0) → (T 0 y).1 i = 0) ∧
    (∀ i, i ∈ vanIdx (coordFun (T 0)) N ↔
      ∃ a, IsExtremeRayGen (quadCone (coordFun (T 0)) N) a ∧ (T 0 (a : E 0)).1 i = 0) ∧
    (∀ y ∈ P, ∀ i ∈ vanIdx (coordFun (T 0)) N, (T 0 y).1 i = 0) := by
  obtain ⟨ε, hε, hgood⟩ := hP.exists_eps
  have h3 : ∀ y ∈ P, ∀ i ∈ vanIdx (coordFun (T 0)) N, (T 0 y).1 i = 0 := fun y hy i hi =>
    lemma_3_8_8 (coordFun (T 0)) N P hε hgood hy hi
  have hgen : ∀ i, (∃ a, IsExtremeRayGen (quadCone (coordFun (T 0)) N) a ∧
      (T 0 (a : E 0)).1 i = 0) → i ∈ vanIdx (coordFun (T 0)) N := by
    rintro i ⟨a, ⟨ha, ha0, -⟩, hai⟩
    exact (mem_vanIdx _ _).2 ⟨a, ha, ha0, hai⟩
  refine ⟨fun y hy i hi => h3 y hy i (hgen i hi), fun i => ⟨fun hi => ?_, hgen i⟩, h3⟩
  -- `Γ ⊆ Γ'`, through the quadrant normal form
  obtain ⟨a, ha, ha0, hai⟩ := (mem_vanIdx _ _).1 hi
  obtain ⟨e, he⟩ := exists_quadrantEquiv_of_pointed T hN fun _ hx hx' => hQ.eq_zero hx hx'
  obtain ⟨j, hj, hsub⟩ := exists_sub_single_mem e he ha ha0
  refine ⟨e.symm (Pi.single j 1), isExtremeRayGen_symm_single e he j, ?_⟩
  set b : N := e.symm (Pi.single j 1)
  have hb : 0 ≤ (T 0 (b : E 0)).1 i := (isExtremeRayGen_symm_single e he j).1 i
  have h2 : 0 ≤ (T 0 ((a - e a j • b : N) : E 0)).1 i := hsub i
  rw [Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul, Prod.fst_sub, Prod.smul_fst,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h2
  change 0 ≤ (T 0 (a : E 0)).1 i - e a j * (T 0 (b : E 0)).1 i at h2
  have hai' : (T 0 (a : E 0)).1 i = 0 := hai
  rw [hai'] at h2
  have : e a j * (T 0 (b : E 0)).1 i = 0 := le_antisymm (by linarith) (mul_nonneg hj.le hb)
  exact (mul_eq_zero.1 this).resolve_left hj.ne'

/-- **2021 Lemma 3.8.5, p. 147 (new in the 2021 edition)**, as the dichotomy the proof shows:
for `N` in good position to `C` with `N ∩ C` a closed convex cone, either
`N ∩ (ℝ^{Γᶜ} ⊕ W) = {0}` (the kernel of `P : N → ℝ^Γ` is trivial), or `N ⊆ ℝ^{Γᶜ} ⊕ W`, `dim N = 1`
and `Γ = ∅`. -/
theorem lemma_3_8_5 (hN : IsInGoodPosition E (T 0 ⁻¹' quadrant n W 0) N)
    (hQ : IsClosedConvexCone (quadCone (coordFun (T 0)) N)) :
    LinearMap.ker (sigmaCoord (coordFun (T 0)) N) = ⊥ ∨
      (LinearMap.ker (sigmaCoord (coordFun (T 0)) N) = ⊤ ∧ finrank ℝ N = 1 ∧
        vanIdx (coordFun (T 0)) N = ∅) := by
  classical
  obtain ⟨P, hP⟩ := hN.exists_goodComplement
  obtain ⟨ε, hε, hgood⟩ := hP.exists_eps
  have hsurj := sigmaCoord_surjective (coordFun (T 0)) N P hP.isCompl hε hgood
    (coordFun_surj (T 0))
  have hint : (interior (quadCone (coordFun (T 0)) N)).Nonempty := hN.interior_nonempty
  by_cases hS : (vanIdx (coordFun (T 0)) N).Nonempty
  · -- `Γ ≠ ∅`: a point of `N` with `x_i = 0` on `Γ` lies in the cone together with `−x`
    left
    rw [eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hx' : ∀ i ∈ vanIdx (coordFun (T 0)) N, coordFun (T 0) i (x : E 0) = 0 := fun i hi => by
      have := congrFun hx ⟨i, hi⟩
      simpa using this
    have h1 := mem_quadCone_of_vanIdx (coordFun (T 0)) N hS hsurj hint (x := x)
      fun i hi => (hx' i hi).ge
    have h2 := mem_quadCone_of_vanIdx (coordFun (T 0)) N hS hsurj hint (x := -x)
      fun i hi => by rw [Submodule.coe_neg, map_neg, hx' i hi, neg_zero]
    rw [Submodule.mem_bot]
    exact hQ.eq_zero h1 h2
  · have hS' : vanIdx (coordFun (T 0)) N = ∅ := Finset.not_nonempty_iff_eq_empty.1 hS
    have hnot : ∀ i, i ∉ vanIdx (coordFun (T 0)) N := by
      rw [hS']; exact fun i => Finset.notMem_empty i
    have hker : LinearMap.ker (sigmaCoord (coordFun (T 0)) N) = ⊤ :=
      eq_top_iff.2 fun x _ => LinearMap.mem_ker.2 (funext fun i => absurd i.2 (hnot i.1))
    by_cases hN0 : finrank ℝ N = 0
    · left
      have : Subsingleton N := Module.finrank_zero_iff.1 hN0
      exact eq_bot_iff.2 fun x _ => by rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _
    · right
      refine ⟨hker, ?_, hS'⟩
      obtain ⟨e, he⟩ := exists_quadrantEquiv_of_pointed T hN fun _ hx hx' => hQ.eq_zero hx hx'
      by_contra hne
      have h2 : 2 ≤ finrank ℝ N := by omega
      set j₀ : Fin (finrank ℝ N) := ⟨0, by omega⟩
      set j₁ : Fin (finrank ℝ N) := ⟨1, by omega⟩
      have hj : j₀ ≠ j₁ := by simp [j₀, j₁, Fin.ext_iff]
      set b₀ : N := e.symm (Pi.single j₀ 1)
      set b₁ : N := e.symm (Pi.single j₁ 1)
      have hg₀ := isExtremeRayGen_symm_single e he j₀
      -- all coordinates of `b₀` are positive (`Γ = ∅`)
      have hpos : ∀ i, 0 < coordFun (T 0) i (b₀ : E 0) := fun i =>
        pos_of_not_mem_vanIdx (coordFun (T 0)) N hg₀.1 hg₀.2.1 (hnot i)
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i,
          0 < coordFun (T 0) i (b₀ : E 0) - t * coordFun (T 0) i (b₁ : E 0) := by
        rw [eventually_all]
        intro i
        have hc : Continuous fun t : ℝ =>
            coordFun (T 0) i (b₀ : E 0) - t * coordFun (T 0) i (b₁ : E 0) := by fun_prop
        exact (hc.tendsto 0).eventually_const_lt (by simpa using hpos i)
      obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
      have ht := hδ' (y := δ / 2)
        (by rw [dist_zero_right, Real.norm_of_nonneg (by positivity)]; linarith)
      have hmem : b₀ - (δ / 2) • b₁ ∈ quadCone (coordFun (T 0)) N := fun i => by
        rw [Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul, smul_eq_mul]
        exact (ht i).le
      have := (he _).1 hmem j₁
      rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hj.symm,
        smul_eq_mul, mul_one] at this
      linarith

/-- **2021 Lemma 3.8.6 (1), p. 148 (new in the 2021 edition)**: if `N` is in good position to `C`
and `N ∩ (ℝ^{Γᶜ} ⊕ W) = {0}`, then `P : N → ℝ^Γ` is a linear isomorphism carrying `N ∩ C` onto the
quadrant `Q_Γ = [0, ∞)^Γ`.  (The cone hypothesis of the text is not needed.) -/
theorem lemma_3_8_6 (hN : IsInGoodPosition E (T 0 ⁻¹' quadrant n W 0) N)
    (hker : LinearMap.ker (sigmaCoord (coordFun (T 0)) N) = ⊥) :
    Bijective (sigmaCoord (coordFun (T 0)) N) ∧
      sigmaCoord (coordFun (T 0)) N '' quadCone (coordFun (T 0)) N =
        {k | ∀ i, 0 ≤ k i} := by
  classical
  obtain ⟨P, hP⟩ := hN.exists_goodComplement
  obtain ⟨ε, hε, hgood⟩ := hP.exists_eps
  have hsurj := sigmaCoord_surjective (coordFun (T 0)) N P hP.isCompl hε hgood
    (coordFun_surj (T 0))
  have hinj : Injective (sigmaCoord (coordFun (T 0)) N) := LinearMap.ker_eq_bot.1 hker
  refine ⟨⟨hinj, hsurj⟩, ?_⟩
  ext k
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact hx i.1
  · intro hk
    obtain ⟨x, rfl⟩ := hsurj k
    refine ⟨x, ?_, rfl⟩
    by_cases hS : (vanIdx (coordFun (T 0)) N).Nonempty
    · exact mem_quadCone_of_vanIdx (coordFun (T 0)) N hS hsurj hN.interior_nonempty
        fun i hi => hk ⟨i, hi⟩
    · -- `Γ = ∅`: then `ℝ^Γ = 0`, `P = 0` is injective, so `N = 0`
      have hS' : vanIdx (coordFun (T 0)) N = ∅ := Finset.not_nonempty_iff_eq_empty.1 hS
      have hnot : ∀ i, i ∉ vanIdx (coordFun (T 0)) N := by
        rw [hS']; exact fun i => Finset.notMem_empty i
      have hx0 : x = 0 := hinj (funext fun i => absurd i.2 (hnot i.1))
      rw [hx0]
      exact zero_mem_quadCone _ _

/-- **2021 Lemma 3.8.6 (2), p. 148 (new in the 2021 edition)**, for `N ≠ 0`: if `N` is in good
position to `C`, `N ∩ C` is a closed convex cone and `N ⊆ ℝ^{Γᶜ} ⊕ W`, then `(N, N ∩ C) ≅ (ℝ, ℝ₊)`.
(For `N = 0` the statement does not hold as we read it: `lemma_3_8_5_not_literal`.) -/
theorem lemma_3_8_6_two (hN : IsInGoodPosition E (T 0 ⁻¹' quadrant n W 0) N)
    (hQ : IsClosedConvexCone (quadCone (coordFun (T 0)) N))
    (hker : LinearMap.ker (sigmaCoord (coordFun (T 0)) N) = ⊤) (hN0 : N ≠ ⊥) :
    ∃ e : N ≃ₗ[ℝ] ℝ, ∀ x : N, x ∈ quadCone (coordFun (T 0)) N ↔ 0 ≤ e x := by
  have hnt : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN0
  have hdim : finrank ℝ N = 1 := by
    rcases lemma_3_8_5 T hN hQ with h | h
    · rw [h] at hker
      exact absurd hker.symm (by simp)
    · exact h.2.1
  obtain ⟨e, he⟩ := exists_quadrantEquiv_of_pointed T hN fun _ hx hx' => hQ.eq_zero hx hx'
  have : Unique (Fin (finrank ℝ N)) := by rw [hdim]; infer_instance
  refine ⟨e.trans (LinearEquiv.funUnique (Fin (finrank ℝ N)) ℝ ℝ), fun x => ?_⟩
  rw [he x, LinearEquiv.trans_apply, LinearEquiv.funUnique_apply]
  constructor
  · intro h; exact h _
  · intro h j; rw [Unique.eq_default j]; exact h

/-- **2021 Corollary 3.8.7, p. 149 (new in the 2021 edition)**: if `N` is in good position to `C`
and `N ∩ C` is a closed convex cone in `N`, then `N ∩ C` is a partial quadrant in `N`; indeed
(p. 149) `(N, N ∩ C) ≅ (ℝ^{dim N}, [0, ∞)^{dim N})`. -/
theorem corollary_3_8_7 (hN : IsInGoodPosition E (T 0 ⁻¹' quadrant n W 0) N)
    (hQ : IsClosedConvexCone (quadCone (coordFun (T 0)) N)) :
    IsPartialQuadrant (ScBanach.const N) (Subtype.val ⁻¹' (T 0 ⁻¹' quadrant n W 0)) ∧
      ∃ e : N ≃ₗ[ℝ] (Fin (finrank ℝ N) → ℝ),
        ∀ x : N, x ∈ quadCone (coordFun (T 0)) N ↔ ∀ j, 0 ≤ e x j :=
  ⟨proposition_3_1_25 ⟨n, W, T, rfl⟩ hN,
    exists_quadrantEquiv_of_pointed T hN fun _ hx hx' => hQ.eq_zero hx hx'⟩

end Appendix

/-! ### `N = {0}` and a nontrivial witness -/

section Witnesses

/-- The model `ℝ ⊕ ℝ⁰` with `C = [0, ∞) ⊕ ℝ⁰`, presented by the identity. -/
abbrev E₁ : ScBanach := halfSpaceSc 0

/-- **Lemma 3.8.5 read as "`N ⊆ ℝ^{Γᶜ} ⊕ W` implies `dim N = 1`", and Lemma 3.8.6 (2) as printed,
do not hold as we read them for `N = {0}`** (2021 pp. 147–148): in `E = ℝ`, `C = [0, ∞)`, the
subspace `N = 0` is in good position, `N ∩ C = {0}` is a closed convex cone, the kernel of
`P : N → ℝ^Γ` is all of `N` (`N ⊆ ℝ^{Γᶜ} ⊕ W`), but `dim N = 0` and `N ≇ ℝ`.  (The dichotomy of
`lemma_3_8_5` holds: here also `N ∩ (ℝ^{Γᶜ} ⊕ W) = {0}`.) -/
theorem lemma_3_8_5_not_literal :
    IsInGoodPosition E₁ ((ScIso.refl E₁) 0 ⁻¹' quadrant 1 (rnSc 0) 0) ⊥ ∧
    IsClosedConvexCone (quadCone (coordFun ((ScIso.refl E₁) 0)) (⊥ : Submodule ℝ (E₁ 0))) ∧
    LinearMap.ker (sigmaCoord (coordFun ((ScIso.refl E₁) 0)) (⊥ : Submodule ℝ (E₁ 0))) = ⊤ ∧
    finrank ℝ (⊥ : Submodule ℝ (E₁ 0)) = 0 ∧
    IsEmpty ((⊥ : Submodule ℝ (E₁ 0)) ≃ₗ[ℝ] ℝ) := by
  have hsub : ∀ x : (⊥ : Submodule ℝ (E₁ 0)), x = 0 := fun x => Subsingleton.elim x 0
  have huniv : ∀ S : Set (⊥ : Submodule ℝ (E₁ 0)), (0 : (⊥ : Submodule ℝ (E₁ 0))) ∈ S →
      S = univ := fun S h0 => eq_univ_of_forall fun x => by rw [hsub x]; exact h0
  have h0C : (0 : (⊥ : Submodule ℝ (E₁ 0))) ∈ quadCone (coordFun ((ScIso.refl E₁) 0)) ⊥ :=
    zero_mem_quadCone _ _
  refine ⟨⟨?_, ⊤, isCompl_bot_top, 1, one_pos, fun x hx p _ hp => ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_,
    finrank_bot ℝ (E₁ 0), ⟨fun e => ?_⟩⟩
  · have : (Subtype.val ⁻¹' ((ScIso.refl E₁) 0 ⁻¹' quadrant 1 (rnSc 0) 0) :
        Set (⊥ : Submodule ℝ (E₁ 0))) = univ := huniv _ h0C
    rw [this, interior_univ]
    exact ⟨0, mem_univ _⟩
  · rw [(Submodule.mem_bot ℝ).1 hx, norm_zero, mul_zero] at hp
    rw [norm_le_zero_iff.1 hp, add_zero]
  · rw [huniv _ h0C]; exact isClosed_univ
  · rw [huniv _ h0C]; exact convex_univ
  · ext x
    rw [hsub x]
    simp only [mem_singleton_iff, iff_true]
    exact ⟨h0C, by rw [Set.mem_neg, neg_zero]; exact h0C⟩
  · intro t _ x _
    rw [hsub (t • x)]; exact h0C
  · exact eq_top_iff.2 fun x _ => by rw [hsub x]; exact Submodule.zero_mem _
  · have := e.finrank_eq
    rw [finrank_bot, Module.finrank_self] at this
    exact zero_ne_one this

/-- **The hypotheses of Lemma 3.8.6 (2) with `N ≠ 0` are satisfiable**: in `E = ℝ ⊕ ℝ⁰`,
`C = [0, ∞) ⊕ ℝ⁰`, the subspace `N = E` is in good position, `N ∩ C` is a closed convex cone,
`Γ = ∅`, so `N ⊆ ℝ^{Γᶜ} ⊕ W`. -/
theorem halfLine_witness :
    IsInGoodPosition E₁ ((ScIso.refl E₁) 0 ⁻¹' quadrant 1 (rnSc 0) 0) ⊤ ∧
    IsClosedConvexCone (quadCone (coordFun ((ScIso.refl E₁) 0)) (⊤ : Submodule ℝ (E₁ 0))) ∧
    LinearMap.ker (sigmaCoord (coordFun ((ScIso.refl E₁) 0)) (⊤ : Submodule ℝ (E₁ 0))) = ⊤ ∧
    (⊤ : Submodule ℝ (E₁ 0)) ≠ ⊥ := by
  classical
  -- pointedness: `x₁ ≥ 0` and `−x₁ ≥ 0` force `x = 0`
  have hpt : ∀ x : (⊤ : Submodule ℝ (E₁ 0)),
      x ∈ quadCone (coordFun ((ScIso.refl E₁) 0)) ⊤ →
        -x ∈ quadCone (coordFun ((ScIso.refl E₁) 0)) ⊤ → x = 0 := by
    intro x h1 h2
    have a1 := h1 0
    have a2 := h2 0
    rw [Submodule.coe_neg, map_neg] at a2
    change 0 ≤ (x : E₁ 0).1 0 at a1
    change 0 ≤ -(x : E₁ 0).1 0 at a2
    refine Subtype.ext (Prod.ext (funext fun i => ?_) (funext fun i => i.elim0))
    rw [Subsingleton.elim i 0]
    change (x : E₁ 0).1 0 = 0
    linarith
  have hvan : vanIdx (coordFun ((ScIso.refl E₁) 0)) (⊤ : Submodule ℝ (E₁ 0)) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
    obtain ⟨x, hx, hx0, hxi⟩ := (mem_vanIdx _ _).1 hi
    refine hx0 (hpt x hx fun j => ?_)
    rw [Subsingleton.elim j i, Submodule.coe_neg, map_neg, hxi, neg_zero]
  refine ⟨(isInGoodPositionIn_top_iff).1 (isInGoodPositionIn_halfSpace ⊤
      ⟨((fun _ => 1 : Fin 1 → ℝ), 0), Submodule.mem_top, one_ne_zero⟩),
    ⟨quadCone_isClosed _ _, ?_, ?_, fun t ht x hx => smul_mem_quadCone _ _ hx ht⟩, ?_,
    bot_lt_top.ne'⟩
  · intro x hx y hy a b ha hb _ i
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, map_add, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  · ext x
    simp only [mem_inter_iff, Set.mem_neg, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact hpt x h1 h2
    · rintro rfl; rw [neg_zero]; exact ⟨zero_mem_quadCone _ _, zero_mem_quadCone _ _⟩
  · have hnot : ∀ i, i ∉ vanIdx (coordFun ((ScIso.refl E₁) 0)) (⊤ : Submodule ℝ (E₁ 0)) := by
      rw [hvan]; exact fun i => Finset.notMem_empty i
    exact eq_top_iff.2 fun x _ => LinearMap.mem_ker.2 (funext fun i => absurd i.2 (hnot i.1))

end Witnesses

end Polyfold
