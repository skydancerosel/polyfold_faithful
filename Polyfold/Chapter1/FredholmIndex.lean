import Polyfold.Chapter1.ScFredholm
import Polyfold.Chapter1.ExpositionLemmas

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.1: the index
of Definition 1.8, the remark after it that `T : E_m → F_m` is Fredholm "with the same index" on
every level (Lemma 2.D of `Exposition/Chapter1.md`), and the index statement of Proposition 1.10,
`ind(T + S) = ind(T)`, which the exposition adds to the text and derives from the classical
invariance of the Fredholm index under compact perturbations (its (F2), Kato IV.5.26).

# The Fredholm index and its invariance under compact perturbations

## What is formalized

For linear maps over a field `K`:

* `Polyfold.linIndex u = dim ker u − dim (F / range u)` (as an integer), and the predicate
  `Polyfold.HasFiniteIndex u` (kernel and cokernel finite-dimensional) under which it is meaningful.
* `Polyfold.HasFiniteIndex.comp`, `Polyfold.linIndex_comp`: for `u : E → F`, `v : F → G` with finite
  index, `v ∘ u` has finite index and `ind(v ∘ u) = ind(u) + ind(v)`.
* `Polyfold.linIndex_eq_zero_of_finiteRange_sub_id`: if `w − 1` has finite rank then `w` has finite
  index and `ind(w) = 0`; `Polyfold.linIndex_equiv`: a linear equivalence has index `0`;
  `Polyfold.HasFiniteIndex.of_bijective_add_and_linIndex`: a bijection plus a finite-rank
  map has index `0`; `Polyfold.HasFiniteIndex.of_comp_of_comp`: if `v ∘ u` and `u ∘ v` have finite
  index, so has `u`.

For real Banach spaces `E`, `F`:

* `Polyfold.fredholmIndex (u : E →L[ℝ] F) : ℤ`, the index of a Fredholm operator
  (`Polyfold.IsFredholm.hasFiniteIndex`).
* `Polyfold.fredholmIndex_add_of_norm_lt`: **stability under small perturbations**: if `v` is a
  quasi-inverse of `u` (`vu − 1` and `uv − 1` of finite rank) and `‖v‖ ‖s‖ < 1`, then `u + s` has
  finite index and `ind(u + s) = ind(u)`.
* `Polyfold.fredholmIndex_add_isCompactOperator`: **invariance under compact perturbations**: if `u`
  is Fredholm and `k` is compact then `ind(u + k) = ind(u)` (by the homotopy `u + t k`,
  `t ∈ [0, 1]`, along which the index is locally constant).

For sc-Fredholm operators:

* `Polyfold.ScBanach.finrank_levelSub_of_le_smooth`: a subspace `A ⊆ E_∞` has `dim A_m = dim A`;
  `Polyfold.ScFredholmSplitting.C_le_smooth`: the complement `C` lies in `F_∞`.
* `Polyfold.ScFredholmSplitting.fredholmIndex_lvl`, `Polyfold.IsScFredholm.fredholmIndex_lvl`
  (**Lemma 2.D** of the exposition, the remark after Definition 1.8): every level map
  `T_m : E_m → F_m` of an sc-Fredholm operator is Fredholm with index `ind(T) = dim K − dim C`;
  `Polyfold.scIndex_eq_fredholmIndex`: `scIndex T` is the index of `T₀`.
* `Polyfold.proposition_1_10_index` (**Proposition 1.10**, the index): `ind(T + S) = ind(T)` for an
  sc⁺-operator `S`; `Polyfold.proposition_1_10_index_lvl`: on every level, `(T + S)_m` is Fredholm
  of index `ind(T)`.

## Proofs

* Additivity is the dimension count along the exact sequence
  `0 → ker u → ker(vu) → range u ∩ ker v → F/range u → G/range(vu) → G/range v → 0`, done with
  the rank–nullity theorem for four linear maps between finite-dimensional spaces: `u` restricted to
  `ker(vu)` (image `range u ∩ ker v`, kernel `ker u`), the quotient map restricted to `ker v`
  (image `B' = (ker v + range u)/range u`, kernel `range u ∩ ker v`), the third isomorphism
  theorem for `range u ≤ range u + ker v` (so `dim F/range u = dim F/(range u + ker v) + dim B'`),
  and `v` followed by the quotient map `G → G/range(vu)`, whose kernel is `range u + ker v` and
  whose image `V'` satisfies `dim G/range(vu) = dim V' + dim G/range v`.
* `ind(1 + k) = 0` for `k` of finite rank with range `R`: `ker(1+k) ⊆ R`, `range(1+k) + R = E` and
  `R ∩ range(1+k) = (1+k)(R)`, so both `dim ker(1+k)` and `dim E/range(1+k)` equal
  `dim R − dim (1+k)(R)`.
* Stability: with a quasi-inverse `v` of `u`, `1 + v s` and `1 + s v` are invertible (Neumann
  series, `‖v s‖, ‖s v‖ < 1`), so `v(u + s) = (1 + v s) + (vu − 1)` and
  `(u + s)v = (1 + s v) + (uv − 1)` are bijections plus finite-rank maps, of index `0`; hence
  `u + s` has finite index and `ind(u + s) + ind(v) = 0 = ind(u) + ind(v)`.
* Compact perturbations: `t ↦ ind(u + t k)` is locally constant on `ℝ` (each `u + t₀ k` is Fredholm
  by `isFredholm_add_isCompactOperator`, and the stability lemma applies near `t₀`), hence constant.
* Lemma 2.D: `ker T_m = K_m ≅ K` and `F_m / range T_m = F_m / Y_m ≅ C_m ≅ C`, since `K, C ⊆ E_∞`.
* Proposition 1.10, index: `ind(T + S) = ind((T + S)₀) = ind(T₀ + S₀) = ind(T₀)` by the compact
  perturbation theorem on level `0`; on level `m`, Lemma 2.D for the sc-Fredholm `T + S`
  (Proposition 1.10).

(This file imports `Polyfold.Chapter1.ExpositionLemmas` only so that that file is part of the
build; nothing here uses it.)
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### The index of a linear map with finite-dimensional kernel and cokernel -/

section Algebra

variable {K : Type*} [Field K] {E F G : Type*} [AddCommGroup E] [Module K E] [AddCommGroup F]
  [Module K F] [AddCommGroup G] [Module K G]

/-- The index `dim ker u − dim (F / range u)` of a linear map, as an integer (meaningful when both
dimensions are finite, `HasFiniteIndex u`). -/
def linIndex (u : E →ₗ[K] F) : ℤ :=
  (finrank K (LinearMap.ker u) : ℤ) - finrank K (F ⧸ LinearMap.range u)

/-- A linear map has **finite index** if its kernel and its cokernel are finite-dimensional. -/
structure HasFiniteIndex (u : E →ₗ[K] F) : Prop where
  finite_ker : FiniteDimensional K (LinearMap.ker u)
  finite_coker : FiniteDimensional K (F ⧸ LinearMap.range u)

/-- A module with a finite-dimensional submodule and finite-dimensional quotient by it is
finite-dimensional. -/
theorem finite_of_finite_quotient (N : Submodule K E) [FiniteDimensional K N]
    [FiniteDimensional K (E ⧸ N)] : FiniteDimensional K E := by
  refine Module.finite_def.2 ?_
  refine Submodule.fg_of_fg_map_of_fg_inf_ker N.mkQ ?_ ?_
  · rw [Submodule.map_top, Submodule.range_mkQ]; exact Module.finite_def.1 ‹_›
  · rw [top_inf_eq, Submodule.ker_mkQ]; exact (Submodule.fg_iff_finiteDimensional N).2 ‹_›

/-- A linear map with finite-dimensional kernel and range has finite-dimensional domain. -/
theorem finite_of_finite_ker_range (f : E →ₗ[K] F) [FiniteDimensional K (LinearMap.ker f)]
    [FiniteDimensional K (LinearMap.range f)] : FiniteDimensional K E := by
  refine Module.finite_def.2 ?_
  refine Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_
  · rw [Submodule.map_top]; exact (Submodule.fg_iff_finiteDimensional _).2 ‹_›
  · rw [top_inf_eq]; exact (Submodule.fg_iff_finiteDimensional _).2 ‹_›

/-- `comap p.subtype q = comap p.subtype (q ⊓ p)`. -/
private lemma comap_subtype_eq_comap_inf (p q : Submodule K E) :
    Submodule.comap p.subtype q = Submodule.comap p.subtype (q ⊓ p) := by
  ext x; simp

/-- `dim (comap p.subtype q) = dim (q ⊓ p)`. -/
private lemma finrank_comap_subtype (p q : Submodule K E) :
    finrank K (Submodule.comap p.subtype q) = finrank K (q ⊓ p : Submodule K E) := by
  rw [comap_subtype_eq_comap_inf]
  exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq

/-- `dim (comap p.subtype q) = dim q` when `q ≤ p`. -/
private lemma finrank_comap_subtype_of_le {p q : Submodule K E} (h : q ≤ p) :
    finrank K (Submodule.comap p.subtype q) = finrank K q :=
  (Submodule.comapSubtypeEquivOfLe h).finrank_eq

section Comp

/-- If `v ∘ u` has finite-dimensional kernel, so has `u`. -/
theorem finiteDimensional_ker_of_comp (u : E →ₗ[K] F) (v : F →ₗ[K] G)
    [FiniteDimensional K (LinearMap.ker (v ∘ₗ u))] :
    FiniteDimensional K (LinearMap.ker u) :=
  Submodule.finiteDimensional_of_le (LinearMap.ker_le_ker_comp u v)

/-- If `u ∘ v` has finite-dimensional cokernel, so has `u`. -/
theorem finiteDimensional_coker_of_comp (u : F →ₗ[K] G) (v : E →ₗ[K] F)
    [FiniteDimensional K (G ⧸ LinearMap.range (u ∘ₗ v))] :
    FiniteDimensional K (G ⧸ LinearMap.range u) :=
  Module.Finite.of_surjective (Submodule.factor (LinearMap.range_comp_le_range v u))
    (Submodule.factor_surjective _)

variable {u : E →ₗ[K] F} {v : F →ₗ[K] G}

/-- The composition of two linear maps of finite index has finite index, and the index is
additive: `ind(v ∘ u) = ind(u) + ind(v)`. -/
theorem HasFiniteIndex.comp_and_linIndex (hu : HasFiniteIndex u) (hv : HasFiniteIndex v) :
    HasFiniteIndex (v ∘ₗ u) ∧ linIndex (v ∘ₗ u) = linIndex u + linIndex v := by
  have := hu.finite_ker; have := hu.finite_coker; have := hv.finite_ker; have := hv.finite_coker
  set A := LinearMap.range u with hA
  set B := LinearMap.ker v with hB
  -- `α := u` restricted to `ker (v ∘ u)`: kernel `≅ ker u`, range `A ⊓ B`
  set α := u.domRestrict (LinearMap.ker (v ∘ₗ u)) with hα
  have hαker : finrank K (LinearMap.ker α) = finrank K (LinearMap.ker u) := by
    rw [hα, LinearMap.ker_domRestrict]
    exact finrank_comap_subtype_of_le (LinearMap.ker_le_ker_comp u v)
  have hαrange : LinearMap.range α = A ⊓ B := by
    rw [hα, LinearMap.range_domRestrict, LinearMap.ker_comp, Submodule.map_comap_eq]
  have hAB : FiniteDimensional K (A ⊓ B : Submodule K F) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hkvu : FiniteDimensional K (LinearMap.ker (v ∘ₗ u)) := by
    have h1 : FiniteDimensional K (LinearMap.ker α) := by
      rw [hα, LinearMap.ker_domRestrict]
      exact (Submodule.comapSubtypeEquivOfLe (LinearMap.ker_le_ker_comp u v)).symm.finiteDimensional
    have h2 : FiniteDimensional K (LinearMap.range α) := by rw [hαrange]; exact hAB
    exact finite_of_finite_ker_range α
  have eα := α.finrank_range_add_finrank_ker
  rw [hαrange, hαker] at eα
  -- `β := mkQ` restricted to `B = ker v`: kernel `≅ A ⊓ B`, range `B' = image of B in F/A`
  set β := A.mkQ.domRestrict B with hβ
  set B' := Submodule.map A.mkQ B with hB'
  have hβker : finrank K (LinearMap.ker β) = finrank K (A ⊓ B : Submodule K F) := by
    rw [hβ, LinearMap.ker_domRestrict, Submodule.ker_mkQ, finrank_comap_subtype]
  have hβrange : LinearMap.range β = B' := by rw [hβ, LinearMap.range_domRestrict]
  have eβ := β.finrank_range_add_finrank_ker
  rw [hβrange, hβker] at eβ
  -- the third isomorphism theorem for `A ≤ A ⊔ B`: `dim F/A = dim F/(A ⊔ B) + dim B'`
  have hmap : (A ⊔ B).map A.mkQ = B' := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  have eγ := Submodule.finrank_quotient_add_finrank ((A ⊔ B).map A.mkQ) (M := F ⧸ A)
  rw [(Submodule.quotientQuotientEquivQuotient A (A ⊔ B) le_sup_left).finrank_eq, hmap] at eγ
  have hFAB : FiniteDimensional K (F ⧸ (A ⊔ B)) :=
    Module.Finite.of_surjective (Submodule.factor (le_sup_left : A ≤ A ⊔ B))
      (Submodule.factor_surjective _)
  -- `δ := mkQ ∘ v : F → G/range(vu)`: kernel `A ⊔ B`, range `V'` = image of `range v`
  set δ := (LinearMap.range (v ∘ₗ u)).mkQ ∘ₗ v with hδ
  set V' := Submodule.map (LinearMap.range (v ∘ₗ u)).mkQ (LinearMap.range v) with hV'
  have hδker : LinearMap.ker δ = A ⊔ B := by
    rw [hδ, LinearMap.ker_comp, Submodule.ker_mkQ, LinearMap.range_comp, Submodule.comap_map_eq]
  have hδrange : LinearMap.range δ = V' := LinearMap.range_comp v _
  have eδ : finrank K V' = finrank K (F ⧸ (A ⊔ B)) := by
    rw [← hδrange, ← hδker]; exact δ.quotKerEquivRange.finrank_eq.symm
  have hV'fin : FiniteDimensional K V' := by
    have : FiniteDimensional K (F ⧸ LinearMap.ker δ) := by rw [hδker]; exact hFAB
    rw [← hδrange]; exact δ.quotKerEquivRange.finiteDimensional
  -- the third isomorphism theorem for `range(vu) ≤ range v`
  have hle : LinearMap.range (v ∘ₗ u) ≤ LinearMap.range v := LinearMap.range_comp_le_range u v
  have hGfin : FiniteDimensional K (G ⧸ LinearMap.range (v ∘ₗ u)) := by
    have : FiniteDimensional K ((G ⧸ LinearMap.range (v ∘ₗ u)) ⧸ V') :=
      (Submodule.quotientQuotientEquivQuotient _ _ hle).symm.finiteDimensional
    exact finite_of_finite_quotient V'
  have eε := Submodule.finrank_quotient_add_finrank V' (M := G ⧸ LinearMap.range (v ∘ₗ u))
  rw [(Submodule.quotientQuotientEquivQuotient _ _ hle).finrank_eq, eδ] at eε
  refine ⟨⟨hkvu, hGfin⟩, ?_⟩
  unfold linIndex
  rw [← hA, ← hB]
  omega

theorem HasFiniteIndex.comp (hu : HasFiniteIndex u) (hv : HasFiniteIndex v) :
    HasFiniteIndex (v ∘ₗ u) := (hu.comp_and_linIndex hv).1

theorem linIndex_comp (hu : HasFiniteIndex u) (hv : HasFiniteIndex v) :
    linIndex (v ∘ₗ u) = linIndex u + linIndex v := (hu.comp_and_linIndex hv).2

end Comp

/-- The quotient by the whole space is trivial. -/
private lemma subsingleton_quotient_top : Subsingleton (F ⧸ (⊤ : Submodule K F)) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact (Submodule.Quotient.eq _).2 Submodule.mem_top

/-- A linear equivalence has finite index `0`. -/
theorem HasFiniteIndex.equiv (e : E ≃ₗ[K] F) : HasFiniteIndex (e : E →ₗ[K] F) := by
  constructor
  · rw [LinearEquiv.ker]; infer_instance
  · rw [LinearEquiv.range]
    have := subsingleton_quotient_top (K := K) (F := F)
    infer_instance

theorem linIndex_equiv (e : E ≃ₗ[K] F) : linIndex (e : E →ₗ[K] F) = 0 := by
  unfold linIndex
  rw [LinearEquiv.ker, LinearEquiv.range, finrank_bot]
  have := subsingleton_quotient_top (K := K) (F := F)
  rw [finrank_zero_of_subsingleton]; simp

section OneAddFiniteRank

variable (w : E →ₗ[K] E) (hw : FiniteDimensional K (LinearMap.range (w - LinearMap.id)))
include hw

/-- If `w − 1` has finite rank then `w` has finite index and `ind(w) = 0`. -/
theorem HasFiniteIndex.of_finiteRange_sub_id_and_linIndex :
    HasFiniteIndex w ∧ linIndex w = 0 := by
  set R := LinearMap.range (w - LinearMap.id) with hR
  -- `ker w ⊆ R`
  have hker : LinearMap.ker w ≤ R := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    refine ⟨-x, ?_⟩
    simp [hx]
  -- `range w ⊔ R = ⊤`
  have hsup : LinearMap.range w ⊔ R = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine Submodule.mem_sup.2 ⟨w x, LinearMap.mem_range_self _ _, -(w - LinearMap.id : E →ₗ[K] E) x,
      R.neg_mem (LinearMap.mem_range_self _ _), ?_⟩
    simp
  -- `R ⊓ range w = w(R)`
  have hinf : R ⊓ LinearMap.range w = R.map w := by
    ext y
    constructor
    · rintro ⟨hyR, x, rfl⟩
      refine ⟨x, ?_, rfl⟩
      have : x = w x - (w - LinearMap.id : E →ₗ[K] E) x := by simp
      rw [this]
      exact R.sub_mem hyR (LinearMap.mem_range_self _ _)
    · rintro ⟨r, hr, rfl⟩
      refine ⟨?_, LinearMap.mem_range_self _ _⟩
      have : w r = r + (w - LinearMap.id : E →ₗ[K] E) r := by simp
      rw [this]
      exact R.add_mem hr (LinearMap.mem_range_self _ _)
  have hwR : R.map w ≤ R := hinf ▸ inf_le_left
  -- `ρ := mkQ` restricted to `R`: surjective onto `E / range w`, kernel `≅ w(R)`
  set ρ := (LinearMap.range w).mkQ.domRestrict R with hρ
  have hρsurj : Surjective ρ := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    have hx : x ∈ LinearMap.range w ⊔ R := hsup ▸ Submodule.mem_top
    obtain ⟨y, hy, r, hr, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨⟨r, hr⟩, ?_⟩
    change (LinearMap.range w).mkQ r = (LinearMap.range w).mkQ (y + r)
    have hy0 : (LinearMap.range w).mkQ y = 0 := (Submodule.Quotient.mk_eq_zero _).2 hy
    rw [map_add, hy0, zero_add]
  have hcoker : FiniteDimensional K (E ⧸ LinearMap.range w) := Module.Finite.of_surjective ρ hρsurj
  have eρ := ρ.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hρsurj, finrank_top, hρ, LinearMap.ker_domRestrict,
    Submodule.ker_mkQ, finrank_comap_subtype, inf_comm, hinf] at eρ
  -- `w` restricted to `R`: range `w(R)`, kernel `≅ ker w`
  have eσ := (w.domRestrict R).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, finrank_comap_subtype_of_le hker] at eσ
  refine ⟨⟨Submodule.finiteDimensional_of_le hker, hcoker⟩, ?_⟩
  unfold linIndex
  omega

theorem HasFiniteIndex.of_finiteRange_sub_id : HasFiniteIndex w :=
  (HasFiniteIndex.of_finiteRange_sub_id_and_linIndex w hw).1

theorem linIndex_eq_zero_of_finiteRange_sub_id : linIndex w = 0 :=
  (HasFiniteIndex.of_finiteRange_sub_id_and_linIndex w hw).2

end OneAddFiniteRank

/-- A bijective linear map plus a finite-rank one has finite index `0`:
`a + r = a ∘ (1 + a⁻¹ r)`, and `1 + a⁻¹ r` has index `0`. -/
theorem HasFiniteIndex.of_bijective_add_and_linIndex (a r : E →ₗ[K] F) (ha : Bijective a)
    (hr : FiniteDimensional K (LinearMap.range r)) :
    HasFiniteIndex (a + r) ∧ linIndex (a + r) = 0 := by
  set e := LinearEquiv.ofBijective a ha with he
  set w : E →ₗ[K] E := LinearMap.id + (e.symm : F →ₗ[K] E) ∘ₗ r with hw
  have hwr : LinearMap.range (w - LinearMap.id) = (LinearMap.range r).map (e.symm : F →ₗ[K] E) := by
    rw [hw, add_sub_cancel_left, LinearMap.range_comp]
  have hwfin : FiniteDimensional K (LinearMap.range (w - LinearMap.id)) := by
    rw [hwr]; infer_instance
  obtain ⟨hw1, hw2⟩ := HasFiniteIndex.of_finiteRange_sub_id_and_linIndex w hwfin
  have hdec : a + r = (e : E →ₗ[K] F) ∘ₗ w := by
    ext x
    simp only [hw, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_add,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, he, LinearEquiv.ofBijective_apply]
  rw [hdec]
  exact ⟨hw1.comp (HasFiniteIndex.equiv e), by rw [linIndex_comp hw1 (HasFiniteIndex.equiv e),
    hw2, linIndex_equiv, add_zero]⟩

/-- A linear map `u` with a map `v` such that `v ∘ u` and `u ∘ v` have finite index has finite
index. -/
theorem HasFiniteIndex.of_comp_of_comp {u : E →ₗ[K] F} {v : F →ₗ[K] E}
    (h₁ : HasFiniteIndex (v ∘ₗ u)) (h₂ : HasFiniteIndex (u ∘ₗ v)) : HasFiniteIndex u := by
  have := h₁.finite_ker; have := h₂.finite_coker
  exact ⟨finiteDimensional_ker_of_comp u v, finiteDimensional_coker_of_comp u v⟩

end Algebra

/-! ### The index of a Fredholm operator between Banach spaces -/

section Banach

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The **index** `dim ker u − dim (F / range u)` of a continuous linear map (of a Fredholm
operator, `IsFredholm.hasFiniteIndex`). -/
def fredholmIndex (u : E →L[ℝ] F) : ℤ := linIndex (u : E →ₗ[ℝ] F)

omit [CompleteSpace E] [CompleteSpace F] in
/-- A Fredholm operator has finite-dimensional kernel and cokernel. -/
theorem IsFredholm.hasFiniteIndex {u : E →L[ℝ] F} (hu : IsFredholm u) :
    HasFiniteIndex (u : E →ₗ[ℝ] F) :=
  ⟨hu.finite_ker, hu.finite_coker⟩

omit [CompleteSpace E] in
open scoped LinearMap.FiniteRangeSetoid in
/-- If `w ≈ 1` (finite-rank difference), the range of `w − 1` is finite-dimensional. -/
private lemma finiteDimensional_range_sub_id_of_equiv {w : E →L[ℝ] E}
    (h : (w : E →ₗ[ℝ] E) ≈ LinearMap.id) :
    FiniteDimensional ℝ (LinearMap.range ((w : E →ₗ[ℝ] E) - LinearMap.id)) := by
  rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange] at h
  exact (Submodule.fg_iff_finiteDimensional _).1 h

/-- `1 + t` is bijective when `‖t‖ < 1` (Neumann series). -/
private lemma bijective_one_add_of_norm_lt {t : E →L[ℝ] E} (ht : ‖t‖ < 1) :
    Bijective (1 + t : E →L[ℝ] E) := by
  have hu : IsUnit (1 - (-t) : E →L[ℝ] E) := isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg])
  rw [sub_neg_eq_add] at hu
  obtain ⟨a, ha⟩ := hu
  refine ⟨fun x y hxy => ?_, fun y => ⟨(a.inv : E →L[ℝ] E) y, ?_⟩⟩
  · have h1 := congrArg (fun z => (a.inv : E →L[ℝ] E) z) hxy
    have hinv : ∀ z, (a.inv : E →L[ℝ] E) ((1 + t : E →L[ℝ] E) z) = z := fun z => by
      rw [← ha]
      exact congrArg (fun f : E →L[ℝ] E => f z) a.inv_val
    rwa [hinv, hinv] at h1
  · rw [← ha]
    exact congrArg (fun f : E →L[ℝ] E => f y) a.val_inv

/-- If `w − 1` has finite rank and `‖t‖ < 1`, then `w + t` has finite index `0`. -/
private lemma hasFiniteIndex_comp_add_of_norm_lt {w : E →L[ℝ] E}
    (hw : FiniteDimensional ℝ (LinearMap.range ((w : E →ₗ[ℝ] E) - LinearMap.id)))
    {t : E →L[ℝ] E} (ht : ‖t‖ < 1) :
    HasFiniteIndex ((w + t : E →L[ℝ] E) : E →ₗ[ℝ] E) ∧
      linIndex ((w + t : E →L[ℝ] E) : E →ₗ[ℝ] E) = 0 := by
  have hdec : ((w + t : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      ((1 + t : E →L[ℝ] E) : E →ₗ[ℝ] E) + ((w : E →ₗ[ℝ] E) - LinearMap.id) := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, ContinuousLinearMap.coe_coe,
      LinearMap.id_apply, add_apply, one_apply_eq_self]
    abel
  rw [hdec]
  exact HasFiniteIndex.of_bijective_add_and_linIndex _ _
    (bijective_one_add_of_norm_lt ht) hw

/-- **Stability of the index under small perturbations.** If `v` is a quasi-inverse of `u` and
`‖v‖ ‖s‖ < 1`, then `u + s` has finite index and `ind(u + s) = ind(u)`. -/
theorem fredholmIndex_add_of_norm_lt {u : E →L[ℝ] F} {v : F →L[ℝ] E} (hvu : v.IsQuasiInverse u)
    {s : E →L[ℝ] F} (hs : ‖v‖ * ‖s‖ < 1) :
    HasFiniteIndex ((u + s : E →L[ℝ] F) : E →ₗ[ℝ] F) ∧ fredholmIndex (u + s) = fredholmIndex u := by
  have h₁ := finiteDimensional_range_sub_id_of_equiv (w := v ∘L u) hvu.1
  have h₂ := finiteDimensional_range_sub_id_of_equiv (w := u ∘L v) hvu.2
  have hvs : ‖v ∘L s‖ < 1 := lt_of_le_of_lt (opNorm_comp_le v s) hs
  have hsv : ‖s ∘L v‖ < 1 := lt_of_le_of_lt (opNorm_comp_le s v) (by rwa [mul_comm])
  -- `v (u + s) = v u + v s` and `(u + s) v = u v + s v` have index `0`
  obtain ⟨hA, hA0⟩ := hasFiniteIndex_comp_add_of_norm_lt h₁ hvs
  obtain ⟨hB, -⟩ := hasFiniteIndex_comp_add_of_norm_lt h₂ hsv
  obtain ⟨hvu0, hvu00⟩ := hasFiniteIndex_comp_add_of_norm_lt (t := 0) h₁ (by simp)
  obtain ⟨huv0, -⟩ := hasFiniteIndex_comp_add_of_norm_lt (t := 0) h₂ (by simp)
  rw [add_zero] at hvu0 hvu00 huv0
  have eA : ((v ∘L u + v ∘L s : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      (v : F →ₗ[ℝ] E) ∘ₗ ((u + s : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
    ext x; simp
  have eB : ((u ∘L v + s ∘L v : F →L[ℝ] F) : F →ₗ[ℝ] F) =
      ((u + s : E →L[ℝ] F) : E →ₗ[ℝ] F) ∘ₗ (v : F →ₗ[ℝ] E) := by
    ext x; simp
  have eC : ((v ∘L u : E →L[ℝ] E) : E →ₗ[ℝ] E) = (v : F →ₗ[ℝ] E) ∘ₗ (u : E →ₗ[ℝ] F) := rfl
  have eD : ((u ∘L v : F →L[ℝ] F) : F →ₗ[ℝ] F) = (u : E →ₗ[ℝ] F) ∘ₗ (v : F →ₗ[ℝ] E) := rfl
  rw [eA] at hA hA0
  rw [eB] at hB
  rw [eC] at hvu0 hvu00
  rw [eD] at huv0
  have hus : HasFiniteIndex ((u + s : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
    HasFiniteIndex.of_comp_of_comp hA hB
  have hu : HasFiniteIndex (u : E →ₗ[ℝ] F) := HasFiniteIndex.of_comp_of_comp hvu0 huv0
  have hv : HasFiniteIndex (v : F →ₗ[ℝ] E) := HasFiniteIndex.of_comp_of_comp huv0 hvu0
  refine ⟨hus, ?_⟩
  have i1 := linIndex_comp hus hv
  have i2 := linIndex_comp hu hv
  unfold fredholmIndex
  omega

/-- **Invariance of the index under compact perturbations** (the classical fact behind the
exposition's (F2), Kato IV.5.26): if `u` is Fredholm and `k` is compact, then
`ind(u + k) = ind(u)`. -/
theorem fredholmIndex_add_isCompactOperator {u : E →L[ℝ] F} (hu : IsFredholm u)
    {k : E →L[ℝ] F} (hk : IsCompactOperator k) : fredholmIndex (u + k) = fredholmIndex u := by
  set φ : ℝ → ℤ := fun t => fredholmIndex (u + t • k) with hφ
  have hloc : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    have hk₀ : IsCompactOperator (t₀ • k : E →L[ℝ] F) := by
      exact hk.smul t₀
    obtain ⟨v, hv⟩ := (isFredholm_add_isCompactOperator hu hk₀).exists_isQuasiInverse
    have hcont : Continuous fun t : ℝ => ‖v‖ * ‖(t - t₀) • k‖ := by fun_prop
    have h0 : ‖v‖ * ‖(t₀ - t₀) • k‖ < 1 := by simp
    filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const h0] with t ht
    have := (fredholmIndex_add_of_norm_lt hv ht).2
    have he : u + t₀ • k + (t - t₀) • k = u + t • k := by
      rw [sub_smul, add_assoc, add_sub_cancel]
    rw [he] at this
    exact this
  have := hloc.apply_eq_of_preconnectedSpace 1 0
  simpa [hφ] using this

end Banach

/-! ### The index of an sc-Fredholm operator on every level (Lemma 2.D, Proposition 1.10) -/

section ScFredholmIndex

variable {E F : ScBanach}

/-- For a subspace `A ⊆ E_∞`, its level-`m` part `A_m` has the dimension of `A`. -/
theorem ScBanach.finrank_levelSub_of_le_smooth (E : ScBanach) {A : Submodule ℝ (E 0)}
    (hA : A ≤ E.smooth) (m : ℕ) : finrank ℝ (E.levelSub A m) = finrank ℝ A := by
  let r : E.levelSub A m →ₗ[ℝ] A := (E.toBase m : E m →ₗ[ℝ] E 0).restrict fun _ hx => hx
  have hr : Bijective r := by
    refine ⟨fun x y hxy => Subtype.ext (E.toBase_injective m (congrArg Subtype.val hxy)),
      fun y => ?_⟩
    obtain ⟨x, hx⟩ := (ScScale.mem_smooth_iff E.toScScale).1 (hA y.2) m
    exact ⟨⟨x, by rw [ScBanach.mem_levelSub, hx]; exact y.2⟩, Subtype.ext hx⟩
  exact (LinearEquiv.ofBijective r hr).finrank_eq

/-- The finite-dimensional complement `C` of the range of an sc-Fredholm operator consists of
smooth points (Lemma 2.D of the exposition, by Proposition 1.6). -/
theorem ScFredholmSplitting.C_le_smooth {T : ScOperator E F} (s : ScFredholmSplitting T) :
    s.C ≤ F.smooth :=
  haveI := s.finite_C
  (F.proposition_1_6_iff s.C).1 s.splitF.1

/-- **Lemma 2.D** of the exposition (the remark after Definition 1.8): for an sc-Fredholm
splitting of `T`, every level map `T_m : E_m → F_m` is Fredholm with kernel `K_m ≅ K`, cokernel
`F_m / Y_m ≅ C_m ≅ C`, and index `ind(T_m) = dim K − dim C`. -/
theorem ScFredholmSplitting.fredholmIndex_lvl {T : ScOperator E F} (s : ScFredholmSplitting T)
    (m : ℕ) : (T m).IsFredholm ∧ fredholmIndex (T m) = s.index := by
  refine ⟨s.isFredholm m, ?_⟩
  have := s.finite_C
  unfold fredholmIndex linIndex ScFredholmSplitting.index
  rw [s.ker_lvl m, s.range_lvl m, E.finrank_levelSub_of_le_smooth s.K_le_smooth m,
    (Submodule.quotientEquivOfIsCompl _ _ (s.splitF.2.2 m).symm).finrank_eq,
    F.finrank_levelSub_of_le_smooth s.C_le_smooth m]

/-- The index of an sc-Fredholm operator is the index of each of its level maps. -/
theorem IsScFredholm.fredholmIndex_lvl {T : ScOperator E F} (hT : IsScFredholm T) (m : ℕ) :
    (T m).IsFredholm ∧ fredholmIndex (T m) = scIndex T := by
  obtain ⟨s⟩ := hT
  rw [← s.index_eq]
  exact s.fredholmIndex_lvl m

/-- `scIndex T` is the Fredholm index of the base map `T₀`. -/
theorem scIndex_eq_fredholmIndex (T : ScOperator E F) : scIndex T = fredholmIndex (T 0) := rfl

/-- **Proposition 1.10, the index** (stated in the exposition, not in the text): for an
sc-Fredholm `T` and an sc⁺-operator `S`, `ind(T + S) = ind(T)`. -/
theorem proposition_1_10_index {T : ScOperator E F} (hT : IsScFredholm T) (S : ScPlus E F) :
    scIndex (T + S.toScOperator) = scIndex T := by
  obtain ⟨s⟩ := hT
  rw [scIndex_eq_fredholmIndex, scIndex_eq_fredholmIndex]
  exact fredholmIndex_add_isCompactOperator (s.isFredholm 0) (S.isCompactOperator 0)

/-- **Proposition 1.10 on every level**: `(T + S)_m : E_m → F_m` is Fredholm of index `ind(T)`
for every `m`. -/
theorem proposition_1_10_index_lvl {T : ScOperator E F} (hT : IsScFredholm T) (S : ScPlus E F)
    (m : ℕ) : ((T + S.toScOperator) m).IsFredholm ∧
      fredholmIndex ((T + S.toScOperator) m) = scIndex T := by
  rw [← proposition_1_10_index hT S]
  exact (proposition_1_10 hT S).fredholmIndex_lvl m

end ScFredholmIndex

end Polyfold
