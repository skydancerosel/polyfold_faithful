import Polyfold.Chapter2.PartialCone

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.3,
**Remark 2.4.8 (preprint 2.28)** (p. 47 (preprint p. 33)): for an sc-smooth retract `(O, C, E)` and a smooth point `x ∈ O`, one has
`T_x^R O ⊂ C_xO ⊂ T_xO`, "and naively one might expect that `C_xO` is a partial quadrant in
`T_xO`.  However, this is in general not the case."

# The partial cone of every sc-smooth retract is a partial quadrant

## The text, paraphrased

(Remark 2.4.8 (preprint 2.28)) `T_x^R O ⊆ C_xO ⊆ T_xO`; in general `C_xO` is *not* a partial quadrant in `T_xO`.
(Proposition 2.5.6 (preprint 2.36)) For a *tame* retract it is.

## What is formalized

The negative claim of Remark 2.4.8 (preprint 2.28) is **refuted**: `C_xO` is a partial quadrant in `T_xO` for every
sc-smooth retract and every smooth `x ∈ O` (with the sc-structure of `T_xO` induced from `E`),
without tameness.  No hypothesis of the remark is dropped, and the definitions are the project's
(`partialConeWith`, `reducedTangentSpaceWith`, `IsPartialQuadrant`, round-trip item V2.33).

* `Polyfold.flor_nonnegRange_simplicial` — the finite-dimensional core, the needed case of
  **Flor's theorem** on nonnegative idempotent matrices: for a linear `M : ℝ^ι → ℝ^ι` with
  `M ∘ M = M` mapping the orthant `[0,∞)^ι` into itself, the cone `range M ∩ [0,∞)^ι = M([0,∞)^ι)`
  is **simplicial**: it is `{Σ_s t_s c_s | t ≥ 0}` for a linearly independent family
  `c_1, …, c_r` (of columns of `M`).  Self-contained, by an elementary support argument (below).
* `Polyfold.ScRetraction.scDeriv_mapsTo_partialQuadrant`: `Dr(x)C_x ⊆ C_x` at `x ∈ O₁`
  (the one-sided sign argument, `Boundary.lean`); `Polyfold.partialConeWith_eq_image_scDeriv`:
  `C_xO = Dr(x)(C_x)`.
* `Polyfold.coneMatrix R T x` — the matrix `M = Λ ∘ Dr(x) ∘ σ` of `Dr(x)` on `E/E_x ≅ ℝ^{I(x)}`
  (`Λ = coordMapL`, `σ` the lift by zero); `coneMatrix_idem`, `coneMatrix_mapsTo_orthant`,
  `coordMapL_scDeriv` (`Λ ∘ Dr(x) = M ∘ Λ`).
* `Polyfold.remark_2_4_8_quotient_simplicial`: for `x ∈ O₁` (no smoothness needed), the image
  `Λ(C_xO) ≅ C_xO / T_x^R O` is a simplicial cone in `ℝ^{I(x)}`.
* `Polyfold.ScRetraction.isScSubspace_reducedTangentSpaceWith`: `T_x^R O` is an sc-subspace at
  every smooth `x ∈ O` (the proof of `proposition_2_5_6_partialCone`, which did not use tameness).
* `Polyfold.remark_2_4_8_isPartialQuadrant` — **the main theorem**: for every sc-smooth retraction
  `r`, presentation `T` of `C`, and smooth `x ∈ O`: `T_xO` and `T_x^R O` are sc-subspaces and
  `C_xO = {v ∈ T_xO | v ∈ C_x}` is a partial quadrant in the sc-Banach space `T_xO`.
  `Polyfold.remark_2_4_8_partialConeWith`: the same in the shape of the audit's statement `B2`
  (`RoundTrip/Items/V2_33.lean`), for an arbitrary proof that `T_xO` is an sc-subspace; its
  negation is exactly the inner statement of `B2`, so `B2` is false.

## The mathematics (worked out before formalizing)

Setting: `C = T⁻¹([0,∞)ⁿ ⊕ W)`, `I(x) = {i | λ_i(x) = 0}` (`λ_i = (T ·)_i`),
`E_x = ⋂_{i∈I(x)} ker λ_i`, `C_x = ⋂_{i∈I(x)} {λ_i ≥ 0}`, `P = Dr(x)` (idempotent, `T_xO = PE`),
`Λ : E → ℝ^{I(x)}`,
`Λv = (λ_i v)_{i∈I(x)}` (surjective, `ker Λ = E_x`), and `σ : ℝ^{I(x)} → E`, `σa = T⁻¹(ã, 0)`
(`ã` the extension by zero), a right inverse of `Λ`.

1. `P(E_x) ⊆ E_x` (two-sided sign argument, `scDeriv_mapsTo_minimalSubspace`) and `P(C_x) ⊆ C_x`
   (one-sided sign argument, `IsSc1With.mapsTo_partialQuadrant` applied to `r` itself, `r(x) = x`;
   both hold at every `x ∈ O₁`).  Hence `C_xO = T_xO ∩ C_x = P(C_x)`.
2. Let `M = Λ P σ : ℝ^{I(x)} → ℝ^{I(x)}`.  Since `v − σΛv ∈ E_x` and `P E_x ⊆ ker Λ`,
   `Λ P = M Λ`; hence `M M = Λ P σ Λ P σ = Λ P P σ = M` (`M` is idempotent) and, as `σ` maps the
   orthant into `C_x` and `P C_x ⊆ C_x`, `M` maps the orthant `[0,∞)^{I(x)}` into itself (`M` is a
   nonnegative matrix).  Also `Λ(T_xO) = range M` and, for `v ∈ T_xO`: `v ∈ C_x ⟺ Λv ≥ 0`.
3. **Flor's theorem (the needed case).**  For `M ≥ 0` idempotent on `ℝ^ι`, let
   `K = range M ∩ [0,∞)^ι` (`= M([0,∞)^ι)`, since `My = y` on `range M`).  Write `M_{ij}` for the
   entries and `B(j) = {i | M_{ij} > 0}` for the support of column `j`.  From `M² = M` and
   `M ≥ 0`: `M_{im} ≥ M_{ij} M_{jm}` (transitivity: `m ∈ B(j) ⟹ B(m) ⊆ B(j)`).  For `y ∈ K`,
   `y = My`, so `y_i = Σ_m M_{im} y_m`; if `y_i > 0` there is `m` with `y_m > 0`, `i ∈ B(m)`, and
   then `B(m) ⊆ supp y` (`y_{i'} ≥ M_{i'm} y_m > 0`).  Call `j` *minimal* if `B(j) ≠ ∅` is minimal
   among the nonempty column supports.  (a) *Generation:* every `y ∈ K` is a nonnegative
   combination of minimal columns, by induction on `|supp y|`: pick `i ∈ supp y`, then `m` as
   above and a minimal `j` with `B(j) ⊆ B(m) ⊆ supp y`; with `t = min_{l∈B(j)} y_l / M_{lj} ≥ 0`
   the vector `w = y − t·(column j)` is `≥ 0`, lies in `range M`, and has strictly smaller support
   (it vanishes at the minimizer).  (b) *Independence:* a minimal `j` has a private index: pick
   `i ∈ B(j)`, so `M_{ij} = Σ_m M_{im} M_{mj} > 0` gives `m ∈ B(j)` with `i ∈ B(m) ⊆ B(j)`, hence
   `B(m) = B(j)` by minimality; if `m ∈ B(j')` for another minimal `j'` then `B(j) = B(m) ⊆ B(j')`,
   so `B(j') = B(j)`.  Taking one column per minimal support, the private indices show the chosen
   columns are linearly independent (evaluate a vanishing combination at the private index).
4. With `c_1, …, c_r` from 3 for `M` of 2: `ê_s = P σ(c_s) ∈ T_xO` are smooth with `Λ ê_s = c_s`
   (`c_s ∈ range M`, `M c_s = c_s`), and for a linear left inverse `ρ` of `t ↦ Σ_s t_s c_s`, the
   functionals `ℓ_s = (ρ ∘ Λ)_s` satisfy `ℓ_s(ê_t) = δ_{st}`; `T_x^R O = T_xO ∩ ⋂_s ker ℓ_s`
   (`Λ(T_xO) = range M ⊆ span c`), and for `v ∈ T_xO`:
   `v ∈ C_x ⟺ Λv ∈ K ⟺ ρ(Λv) ≥ 0 ⟺ ∀s, ℓ_s v ≥ 0`.
   The sc-isomorphism `T_xO ≅ ℝ^r ⊕ T_x^R O` of `Polyfold.splitIso` (the map `S` of Theorem 2.4.12 (preprint 2.31))
   carries `C_xO` onto `[0,∞)^r ⊕ T_x^R O` (`isPartialQuadrant_ofSubspace`).

## What the text leaves implicit, and the choices made

* "Partial quadrant in `T_xO`" is read with the sc-structure of `T_xO` induced from `E`
  (`ScBanach.ofSubspace`, as in `proposition_2_5_6_partialCone`), the only reading in the project.
* The dimension `r` of the quadrant is `rank M = dim(T_xO / T_x^R O) ≤ d_C(x)`, with equality iff
  `M` has full rank `|I(x)|`, which is the tame case (Proposition 2.5.3 (preprint 2.35): `M = id`); for a
  non-tame retraction `r` may be smaller than `d_C(x)` (Theorem 2.4.12 (preprint 2.31)), but the cone is still a
  partial quadrant.  So the remark's negative claim fails for every retract; what can fail is only
  `r = d_C(x)`.
* Flor's theorem is used only in the form "the column cone of a nonnegative idempotent is
  simplicial"; the structure theorem itself (block form `[J, JU; VJ, VJU]`) is not formalized.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### Flor's theorem: the column cone of a nonnegative idempotent is simplicial -/

section Flor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The nonnegative orthant `[0,∞)^ι`. -/
def orthant (ι : Type*) : Set (ι → ℝ) := {y | ∀ i, 0 ≤ y i}

omit [Fintype ι] [DecidableEq ι] in
lemma mem_orthant {y : ι → ℝ} : y ∈ orthant ι ↔ ∀ i, 0 ≤ y i := Iff.rfl

variable (M : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-- The `j`-th column `M e_j` of `M`. -/
def column (j : ι) : ι → ℝ := M (Pi.single j 1)

/-- The matrix entry `M_{ij} = (M e_j)_i`. -/
def matEntry (i j : ι) : ℝ := M (Pi.single j 1) i

omit [Fintype ι] in
lemma column_apply (i j : ι) : column M j i = matEntry M i j := rfl

omit [Fintype ι] in
lemma column_mem_range (j : ι) : column M j ∈ LinearMap.range M := ⟨_, rfl⟩

lemma apply_eq_sum_smul_column (v : ι → ℝ) : M v = ∑ j, v j • column M j := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [column, ← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]

lemma apply_eq_sum (v : ι → ℝ) (i : ι) : M v i = ∑ j, matEntry M i j * v j := by
  rw [apply_eq_sum_smul_column, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

/-- The cone `range M ∩ [0,∞)^ι`. -/
def nonnegRange : Set (ι → ℝ) := (LinearMap.range M : Set (ι → ℝ)) ∩ orthant ι

/-- The support `{i | M_{ij} > 0}` of the `j`-th column. -/
def colSupp (j : ι) : Finset ι := Finset.univ.filter fun i => 0 < matEntry M i j

lemma mem_colSupp {i j : ι} : i ∈ colSupp M j ↔ 0 < matEntry M i j := by simp [colSupp]

/-- The support `{i | y_i > 0}` of a vector. -/
def posSupp (y : ι → ℝ) : Finset ι := Finset.univ.filter fun i => 0 < y i

omit [DecidableEq ι] in
lemma mem_posSupp {y : ι → ℝ} {i : ι} : i ∈ posSupp y ↔ 0 < y i := by simp [posSupp]

/-- `j` is a **minimal column**: its support is nonempty and minimal among the nonempty column
supports. -/
def IsMinCol (j : ι) : Prop :=
  (colSupp M j).Nonempty ∧
    ∀ j', (colSupp M j').Nonempty → colSupp M j' ⊆ colSupp M j → colSupp M j' = colSupp M j

/-- The minimal column supports. -/
def MinSupp : Type _ := {S : Finset ι // ∃ j, IsMinCol M j ∧ colSupp M j = S}

instance : Fintype (MinSupp M) := by classical exact Subtype.fintype _

instance : DecidableEq (MinSupp M) := by unfold MinSupp; infer_instance

/-- A representative column for a minimal support. -/
def MinSupp.rep (S : MinSupp M) : ι := S.2.choose

lemma MinSupp.isMinCol_rep (S : MinSupp M) : IsMinCol M S.rep := S.2.choose_spec.1

lemma MinSupp.colSupp_rep (S : MinSupp M) : colSupp M S.rep = S.1 := S.2.choose_spec.2

/-- The generators of the cone: one column for each minimal support. -/
def coneGen (S : MinSupp M) : ι → ℝ := column M S.rep

variable (hMM : ∀ v, M (M v) = M v) (hpos : MapsTo M (orthant ι) (orthant ι))

omit [Fintype ι] [DecidableEq ι] in
include hMM in
lemma apply_eq_self_of_mem_range {y : ι → ℝ} (hy : y ∈ LinearMap.range M) : M y = y := by
  obtain ⟨v, rfl⟩ := hy
  exact hMM v

omit [Fintype ι] [DecidableEq ι] in
include hMM hpos in
/-- `M([0,∞)^ι) = range M ∩ [0,∞)^ι`. -/
lemma image_orthant_eq_nonnegRange : M '' orthant ι = nonnegRange M := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, hpos hv⟩
  · rintro ⟨hy, hy'⟩
    exact ⟨y, hy', apply_eq_self_of_mem_range M hMM hy⟩

omit [Fintype ι] in
include hpos in
lemma matEntry_nonneg (i j : ι) : 0 ≤ matEntry M i j :=
  hpos (fun l => by rw [Pi.single_apply]; split_ifs <;> norm_num) i

omit [Fintype ι] in
include hpos in
lemma column_mem_nonnegRange (j : ι) : column M j ∈ nonnegRange M :=
  ⟨column_mem_range M j, fun i => matEntry_nonneg M hpos i j⟩

include hMM hpos in
/-- Transitivity: `M_{im} ≥ M_{ij} M_{jm}` (from `M² = M`, `M ≥ 0`). -/
lemma matEntry_mul_le (i j m : ι) : matEntry M i j * matEntry M j m ≤ matEntry M i m := by
  have h : matEntry M i m = ∑ l, matEntry M i l * matEntry M l m := by
    change M (Pi.single m 1) i = _
    rw [← hMM (Pi.single m 1), apply_eq_sum]
    rfl
  rw [h]
  exact Finset.single_le_sum
    (fun l _ => mul_nonneg (matEntry_nonneg M hpos i l) (matEntry_nonneg M hpos l m))
    (Finset.mem_univ j)

include hMM hpos in
lemma colSupp_subset {j m : ι} (hm : m ∈ colSupp M j) : colSupp M m ⊆ colSupp M j := by
  intro i hi
  rw [mem_colSupp] at hi hm ⊢
  exact lt_of_lt_of_le (mul_pos hi hm) (matEntry_mul_le M hMM hpos i m j)

include hMM hpos in
/-- For `y ∈ range M ∩ [0,∞)^ι` and `y_i > 0`, there is `m` with `y_m > 0`, `M_{im} > 0`, and
the support of column `m` contained in the support of `y`. -/
lemma exists_colSupp_subset_posSupp {y : ι → ℝ} (hy : y ∈ nonnegRange M) {i : ι} (hi : 0 < y i) :
    ∃ m, 0 < y m ∧ i ∈ colSupp M m ∧ colSupp M m ⊆ posSupp y := by
  have hyM : M y = y := apply_eq_self_of_mem_range M hMM hy.1
  have hsum : ∀ l, y l = ∑ j, matEntry M l j * y j := fun l => by rw [← apply_eq_sum, hyM]
  have hnn : ∀ l j, 0 ≤ matEntry M l j * y j := fun l j =>
    mul_nonneg (matEntry_nonneg M hpos l j) (hy.2 j)
  obtain ⟨m, -, hm⟩ :=
    (Finset.sum_pos_iff_of_nonneg fun j _ => hnn i j).1 (by rw [← hsum]; exact hi)
  have hm1 : 0 < matEntry M i m := pos_of_mul_pos_left hm (hy.2 m)
  have hm2 : 0 < y m := pos_of_mul_pos_right hm (matEntry_nonneg M hpos i m)
  refine ⟨m, hm2, (mem_colSupp M).2 hm1, fun l hl => ?_⟩
  rw [mem_colSupp] at hl
  rw [mem_posSupp, hsum l]
  exact lt_of_lt_of_le (mul_pos hl hm2)
    (Finset.single_le_sum (fun j _ => hnn l j) (Finset.mem_univ m))

/-- Every nonempty column support contains a minimal one. -/
lemma exists_isMinCol_subset {m : ι} (hm : (colSupp M m).Nonempty) :
    ∃ j, IsMinCol M j ∧ colSupp M j ⊆ colSupp M m := by
  obtain ⟨S, hSm, hS⟩ := exists_minimal_le_of_wellFoundedLT
    (fun S : Finset ι => ∃ j, S.Nonempty ∧ colSupp M j = S) (colSupp M m) ⟨m, hm, rfl⟩
  obtain ⟨j, hjne, rfl⟩ := hS.1
  refine ⟨j, ⟨hjne, fun j' hj' hsub => ?_⟩, hSm⟩
  exact le_antisymm hsub (hS.2 ⟨j', hj', rfl⟩ hsub)

include hMM hpos in
/-- A minimal column `j` has a **private index** `m ∈ B(j)` with `B(m) = B(j)`. -/
lemma IsMinCol.exists_private {j : ι} (hj : IsMinCol M j) :
    ∃ m ∈ colSupp M j, colSupp M m = colSupp M j := by
  obtain ⟨i, hi⟩ := hj.1
  obtain ⟨m, hm, him, -⟩ := exists_colSupp_subset_posSupp M hMM hpos
    (column_mem_nonnegRange M hpos j) ((mem_colSupp M).1 hi)
  have hmj : m ∈ colSupp M j := (mem_colSupp M).2 hm
  exact ⟨m, hmj, hj.2 m ⟨i, him⟩ (colSupp_subset M hMM hpos hmj)⟩

include hMM hpos in
/-- **Generation**: every `y ∈ range M ∩ [0,∞)^ι` is a nonnegative combination of the generators
(induction on the size of the support of `y`). -/
lemma exists_nonneg_comb_coneGen (N : ℕ) :
    ∀ y : ι → ℝ, y ∈ nonnegRange M → (posSupp y).card ≤ N →
      ∃ t : MinSupp M → ℝ, (∀ S, 0 ≤ t S) ∧ y = ∑ S, t S • coneGen M S := by
  induction N with
  | zero =>
    intro y hy hcard
    refine ⟨0, fun _ => le_rfl, funext fun i => ?_⟩
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    by_contra h
    have hi : i ∈ posSupp y := (mem_posSupp).2 (lt_of_le_of_ne (hy.2 i) (Ne.symm h))
    have := Finset.card_pos.2 ⟨i, hi⟩
    omega
  | succ N ih =>
    intro y hy hcard
    by_cases hle : (posSupp y).card ≤ N
    · exact ih y hy hle
    have hne : (posSupp y).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨i, hi⟩ := hne
    rw [mem_posSupp] at hi
    obtain ⟨m, -, him, hsub⟩ := exists_colSupp_subset_posSupp M hMM hpos hy hi
    obtain ⟨j, hj, hjm⟩ := exists_isMinCol_subset M ⟨i, him⟩
    let S : MinSupp M := ⟨colSupp M j, j, hj, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = coneGen M S := ⟨_, rfl⟩
    have hcS : colSupp M S.rep = colSupp M j := S.colSupp_rep
    have hcnn : ∀ l, 0 ≤ c l := fun l => by rw [hc]; exact matEntry_nonneg M hpos l _
    have hcpos : ∀ l ∈ colSupp M j, 0 < c l := fun l hl => by
      rw [← hcS, mem_colSupp] at hl; rw [hc]; exact hl
    have hczero : ∀ l, l ∉ colSupp M j → c l = 0 := fun l hl => by
      rw [← hcS, mem_colSupp, not_lt] at hl
      rw [hc]; exact le_antisymm hl (matEntry_nonneg M hpos l _)
    have hcM : c ∈ LinearMap.range M := by rw [hc]; exact column_mem_range M _
    obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image (colSupp M j) (fun l => y l / c l) hj.1
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, t₀ = y i₀ / c i₀ := ⟨_, rfl⟩
    have ht₀nn : 0 ≤ t₀ := by rw [ht₀]; exact div_nonneg (hy.2 i₀) (hcnn i₀)
    obtain ⟨w, hw⟩ : ∃ w, w = y - t₀ • c := ⟨_, rfl⟩
    have hwl : ∀ l, w l = y l - t₀ * c l := fun l => by
      rw [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hwnn : ∀ l, 0 ≤ w l := fun l => by
      rw [hwl, sub_nonneg]
      by_cases hl : l ∈ colSupp M j
      · have := hmin l hl
        rw [← ht₀, le_div_iff₀ (hcpos l hl)] at this
        exact this
      · rw [hczero l hl, mul_zero]; exact hy.2 l
    have hwi₀ : w i₀ = 0 := by
      rw [hwl, ht₀, div_mul_cancel₀ _ (hcpos i₀ hi₀).ne', sub_self]
    have hwM : w ∈ nonnegRange M :=
      ⟨by rw [hw]; exact Submodule.sub_mem _ hy.1 (Submodule.smul_mem _ _ hcM), hwnn⟩
    have hwsupp : posSupp w ⊂ posSupp y := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨fun l hl => ?_, fun heq => ?_⟩
      · rw [mem_posSupp] at hl ⊢
        refine lt_of_lt_of_le hl ?_
        rw [hwl]
        exact sub_le_self _ (mul_nonneg ht₀nn (hcnn l))
      · have : i₀ ∈ posSupp y := hsub (hjm hi₀)
        rw [← heq, mem_posSupp, hwi₀] at this
        exact lt_irrefl _ this
    have hwcard : (posSupp w).card ≤ N := by
      have := Finset.card_lt_card hwsupp; omega
    obtain ⟨t', ht'nn, ht'⟩ := ih w hwM hwcard
    refine ⟨t' + Pi.single S t₀, fun S' => ?_, ?_⟩
    · rw [Pi.add_apply]
      refine add_nonneg (ht'nn S') ?_
      rw [Pi.single_apply]
      split_ifs
      · exact ht₀nn
      · exact le_rfl
    · have hy' : y = w + t₀ • c := by rw [hw, sub_add_cancel]
      rw [hy', ht']
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single S]
      · rw [Pi.single_eq_same, hc]
      · intro b _ hb
        rw [Pi.single_apply, if_neg hb, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ _) h

include hMM hpos in
/-- **Independence**: the generators are linearly independent (evaluate at the private indices). -/
lemma linearIndependent_coneGen : LinearIndependent ℝ (coneGen M) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg S
  obtain ⟨m, hmS, hm⟩ := IsMinCol.exists_private M hMM hpos S.isMinCol_rep
  have hval := congrFun hg m
  rw [Finset.sum_apply, Finset.sum_eq_single S] at hval
  · rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hval
    have hpos' : 0 < coneGen M S m := (mem_colSupp M).1 hmS
    exact (mul_eq_zero.1 hval).resolve_right hpos'.ne'
  · intro S' _ hS'
    rw [Pi.smul_apply, smul_eq_mul]
    have : coneGen M S' m = 0 := by
      by_contra h
      have hpos' : 0 < coneGen M S' m :=
        lt_of_le_of_ne (matEntry_nonneg M hpos m S'.rep) (Ne.symm h)
      have hmS' : m ∈ colSupp M S'.rep := (mem_colSupp M).2 hpos'
      have h1 : colSupp M S.rep ⊆ colSupp M S'.rep := hm ▸ colSupp_subset M hMM hpos hmS'
      have h2 := S'.isMinCol_rep.2 _ S.isMinCol_rep.1 h1
      exact hS' (Subtype.ext (by rw [← S'.colSupp_rep, ← S.colSupp_rep, h2]))
    rw [this, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

include hMM hpos in
/-- **Flor's theorem, the needed case**: for a linear `M : ℝ^ι → ℝ^ι` with `M ∘ M = M` mapping
the orthant into itself (a nonnegative idempotent matrix), the cone `range M ∩ [0,∞)^ι`
(`= M([0,∞)^ι)`, the column cone of `M`) is **simplicial**: it is the set of nonnegative
combinations of a linearly independent family `c_1, …, c_r` (of columns of `M`). -/
theorem flor_nonnegRange_simplicial :
    ∃ (r : ℕ) (c : Fin r → ι → ℝ), LinearIndependent ℝ c ∧
      nonnegRange M = {y | ∃ t : Fin r → ℝ, (∀ s, 0 ≤ t s) ∧ y = ∑ s, t s • c s} := by
  refine ⟨Fintype.card (MinSupp M), coneGen M ∘ (Fintype.equivFin (MinSupp M)).symm,
    (linearIndependent_coneGen M hMM hpos).comp _ (Equiv.injective _), ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht, hyt⟩ := exists_nonneg_comb_coneGen M hMM hpos _ y hy le_rfl
    refine ⟨t ∘ (Fintype.equivFin (MinSupp M)).symm, fun s => ht _, ?_⟩
    rw [hyt]
    exact (Equiv.sum_comp (Fintype.equivFin (MinSupp M)).symm fun S => t S • coneGen M S).symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (column_mem_range M _),
      fun i => ?_⟩
    rw [Finset.sum_apply]
    exact Finset.sum_nonneg fun s _ => by
      rw [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (ht s) (matEntry_nonneg M hpos i _)

end Flor

/-! ### `Dr(x)` maps `C_x` into `C_x`; `C_xO = Dr(x)(C_x)` -/

section Cone

variable {E : ScBanach} {n : ℕ} {W : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}
  {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}

/-- `Dr(x)` maps `C_x` into `C_x` at a point `x ∈ O₁` (the one-sided sign argument for `r`, with
`r(x) = x`); the companion of `ScRetraction.scDeriv_mapsTo_minimalSubspace`.  Tameness is not
needed. -/
theorem ScRetraction.scDeriv_mapsTo_partialQuadrant (R : ScRetraction E C)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) :
    MapsTo (scDeriv R.U R x) (partialQuadrantAtWith T (E.toBase 1 x))
      (partialQuadrantAtWith T (E.toBase 1 x)) := by
  have h := IsSc1With.mapsTo_partialQuadrant T hT T hT R.relOpen R.isSc1.isSc1With_scDeriv
    (fun _ hz => R.U_subset_C (R.mapsTo hz)) (R.lvlSet_retract_subset 1 hx)
  rwa [R.apply_eq_self_of_mem_retract hx] at h

/-- `C_xO = Dr(x)(C_x)` for `x ∈ O₁`. -/
theorem partialConeWith_eq_image_scDeriv (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) :
    partialConeWith R T x = scDeriv R.U R x '' partialQuadrantAtWith T (E.toBase 1 x) := by
  ext v
  constructor
  · rintro ⟨⟨u, rfl⟩, hv⟩
    exact ⟨_, hv, congrArg (fun L : E 0 →L[ℝ] E 0 => L u) (R.scDeriv_comp_self hx)⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, R.scDeriv_mapsTo_partialQuadrant T hT hx hu⟩

end Cone

/-! ### The matrix of `Dr(x)` on `E/E_x ≅ ℝ^{I(x)}` -/

section Matrix

variable {E : ScBanach} {n : ℕ} {W : ScBanach}

/-- The extension by zero `ℝ^{I(x)} → ℝⁿ`. -/
def extZero (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x0 : E 0) :
    ({i : Fin n // (T 0 x0).1 i = 0} → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i : Fin n =>
    if h : (T 0 x0).1 i = 0 then LinearMap.proj (⟨i, h⟩ : {i : Fin n // (T 0 x0).1 i = 0}) else 0

lemma extZero_apply (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x0 : E 0)
    (a : {i : Fin n // (T 0 x0).1 i = 0} → ℝ) (i : Fin n) :
    extZero T x0 a i = if h : (T 0 x0).1 i = 0 then a ⟨i, h⟩ else 0 := by
  simp only [extZero, LinearMap.pi_apply]
  split_ifs <;> rfl

/-- The lift `σ : ℝ^{I(x)} → E`, `σ a = T⁻¹(ã, 0)`, a right inverse of `Λ = coordMapL T x`. -/
def liftCoord (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x0 : E 0) :
    ({i : Fin n // (T 0 x0).1 i = 0} → ℝ) →ₗ[ℝ] E 0 :=
  (((T 0).symm : ((ScBanach.const (Fin n → ℝ)).prod W) 0 →L[ℝ] E 0) : _ →ₗ[ℝ] E 0) ∘ₗ
    LinearMap.inl ℝ (Fin n → ℝ) (W 0) ∘ₗ extZero T x0

variable (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x0 : E 0)

lemma liftCoord_eq_coordVec (a : {i : Fin n // (T 0 x0).1 i = 0} → ℝ) :
    liftCoord T x0 a = coordVec T (extZero T x0 a) := rfl

lemma coord_liftCoord (a : {i : Fin n // (T 0 x0).1 i = 0} → ℝ) (i : Fin n) :
    (T 0 (liftCoord T x0 a)).1 i = extZero T x0 a i := by
  rw [liftCoord_eq_coordVec, coord_coordVec]

lemma coordMapL_liftCoord (a : {i : Fin n // (T 0 x0).1 i = 0} → ℝ) :
    coordMapL T x0 (liftCoord T x0 a) = a := by
  funext i
  rw [coordMapL_apply, coord_liftCoord, extZero_apply, dif_pos i.2]

lemma sub_liftCoord_mem (v : E 0) :
    v - liftCoord T x0 (coordMapL T x0 v) ∈ minimalSubspaceWith T x0 := by
  rw [minimalSubspaceWith, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub,
    coordMapL_liftCoord, sub_self]

lemma liftCoord_mem_partialQuadrant {a : {i : Fin n // (T 0 x0).1 i = 0} → ℝ} (ha : ∀ i, 0 ≤ a i) :
    liftCoord T x0 a ∈ partialQuadrantAtWith T x0 := by
  intro i hi
  rw [coord_liftCoord, extZero_apply, dif_pos hi]
  exact ha _

/-- `v ∈ C_x ⟺ Λ v ≥ 0`. -/
lemma mem_partialQuadrantAtWith_iff_coordMapL (v : E 0) :
    v ∈ partialQuadrantAtWith T x0 ↔
      ∀ i : {i : Fin n // (T 0 x0).1 i = 0}, 0 ≤ coordMapL T x0 v i :=
  ⟨fun h i => h i.1 i.2, fun h i hi => h ⟨i, hi⟩⟩

lemma coordMapL_eq_zero_iff (v : E 0) : coordMapL T x0 v = 0 ↔ v ∈ minimalSubspaceWith T x0 := by
  rw [minimalSubspaceWith, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

variable {C : Set (E 0)} (R : ScRetraction E C)

/-- The matrix `M = Λ ∘ Dr(x) ∘ σ` of `Dr(x)` on `E/E_x ≅ ℝ^{I(x)}`. -/
def coneMatrix (x : E 1) :
    ({i : Fin n // (T 0 (E.toBase 1 x)).1 i = 0} → ℝ) →ₗ[ℝ]
      ({i : Fin n // (T 0 (E.toBase 1 x)).1 i = 0} → ℝ) :=
  (coordMapL T (E.toBase 1 x) : E 0 →ₗ[ℝ] _) ∘ₗ (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0) ∘ₗ
    liftCoord T (E.toBase 1 x)

lemma coneMatrix_apply (x : E 1) (a : {i : Fin n // (T 0 (E.toBase 1 x)).1 i = 0} → ℝ) :
    coneMatrix T R x a =
      coordMapL T (E.toBase 1 x) (scDeriv R.U R x (liftCoord T (E.toBase 1 x) a)) :=
  rfl

variable {T R}

/-- `Λ ∘ Dr(x) = M ∘ Λ` at `x ∈ O₁`: `M` represents `Dr(x)` on `E/E_x`. -/
theorem coordMapL_scDeriv (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (v : E 0) :
    coordMapL T (E.toBase 1 x) (scDeriv R.U R x v) =
      coneMatrix T R x (coordMapL T (E.toBase 1 x) v) := by
  set x0 := E.toBase 1 x
  set P := scDeriv R.U R x
  have h1 : P v = P (v - liftCoord T x0 (coordMapL T x0 v)) +
      P (liftCoord T x0 (coordMapL T x0 v)) := by
    rw [← map_add, sub_add_cancel]
  have h2 : coordMapL T x0 (P (v - liftCoord T x0 (coordMapL T x0 v))) = 0 :=
    (coordMapL_eq_zero_iff T x0 _).2
      (R.scDeriv_mapsTo_minimalSubspace T hT hx (sub_liftCoord_mem T x0 v))
  rw [h1, map_add, h2, zero_add, coneMatrix_apply]

/-- `M` is idempotent. -/
theorem coneMatrix_idem (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (a : {i : Fin n // (T 0 (E.toBase 1 x)).1 i = 0} → ℝ) :
    coneMatrix T R x (coneMatrix T R x a) = coneMatrix T R x a := by
  have hPP : ∀ v, scDeriv R.U R x (scDeriv R.U R x v) = scDeriv R.U R x v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hx)
  have := coordMapL_scDeriv hT hx (scDeriv R.U R x (liftCoord T (E.toBase 1 x) a))
  rw [hPP] at this
  exact this.symm

/-- `M` maps the orthant into itself (`M ≥ 0`). -/
theorem coneMatrix_mapsTo_orthant (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) :
    MapsTo (coneMatrix T R x) (orthant {i : Fin n // (T 0 (E.toBase 1 x)).1 i = 0})
      (orthant {i : Fin n // (T 0 (E.toBase 1 x)).1 i = 0}) := by
  intro a ha i
  have h1 := liftCoord_mem_partialQuadrant T (E.toBase 1 x) ha
  have h2 := R.scDeriv_mapsTo_partialQuadrant T hT hx h1
  exact h2 i.1 i.2

/-- `Λ(T_xO) ⊆ range M`. -/
theorem coordMapL_mem_range_coneMatrix (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) {v : E 0}
    (hv : v ∈ LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) :
    coordMapL T (E.toBase 1 x) v ∈ LinearMap.range (coneMatrix T R x) := by
  obtain ⟨u, rfl⟩ := hv
  exact ⟨coordMapL T (E.toBase 1 x) u, (coordMapL_scDeriv hT hx u).symm⟩

/-- `Λ(C_xO) = range M ∩ [0,∞)^{I(x)}`, the column cone of `M`. -/
theorem coordMapL_image_partialConeWith (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) :
    coordMapL T (E.toBase 1 x) '' partialConeWith R T x = nonnegRange (coneMatrix T R x) := by
  ext y
  constructor
  · rintro ⟨v, ⟨⟨u, hu⟩, hvC⟩, rfl⟩
    exact ⟨coordMapL_mem_range_coneMatrix hT hx ⟨u, hu⟩,
      (mem_partialQuadrantAtWith_iff_coordMapL T _ v).1 hvC⟩
  · rintro ⟨⟨a, ha⟩, hy⟩
    refine ⟨scDeriv R.U R x (liftCoord T (E.toBase 1 x) a), ⟨⟨_, rfl⟩, ?_⟩, ha⟩
    rw [mem_partialQuadrantAtWith_iff_coordMapL]
    change ∀ i, 0 ≤ coneMatrix T R x a i
    rw [ha]
    exact hy

/-- **Remark 2.4.8 (preprint 2.28), the quotient cone**: at every `x ∈ O₁`, the image of `C_xO` in
`E/E_x ≅ ℝ^{I(x)}` (that is, `C_xO / T_x^R O`) is a simplicial cone: the nonnegative combinations
of a linearly independent family. -/
theorem remark_2_4_8_quotient_simplicial (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) :
    ∃ (r : ℕ) (c : Fin r → {i : Fin n // (T 0 (E.toBase 1 x)).1 i = 0} → ℝ),
      LinearIndependent ℝ c ∧
      coordMapL T (E.toBase 1 x) '' partialConeWith R T x =
        {y | ∃ t : Fin r → ℝ, (∀ s, 0 ≤ t s) ∧ y = ∑ s, t s • c s} := by
  classical
  obtain ⟨r, c, hc, hK⟩ := flor_nonnegRange_simplicial (coneMatrix T R x) (coneMatrix_idem hT hx)
    (coneMatrix_mapsTo_orthant hT hx)
  exact ⟨r, c, hc, by rw [coordMapL_image_partialConeWith hT hx, hK]⟩

end Matrix

/-! ### The main theorem: `C_xO` is a partial quadrant in `T_xO` for every sc-smooth retract -/

section Main

variable {E : ScBanach} {n : ℕ} {W : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}
  {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}

/-- At a smooth point `x ∈ O` of any sc-smooth retract, the reduced tangent space `T_x^R O` is an
sc-subspace of `E` (the step of `proposition_2_5_6_partialCone`, which does not use tameness): for
`u ∈ T_x^R O ∩ E_m` with `T u = (a, w)`, the smooth points `Dr(x)(T⁻¹(a, w'))`, `w' ∈ W_∞`, lie in
`T_x^R O` (`Dr(x) E_x ⊆ E_x`) and tend to `Dr(x) u = u`. -/
theorem ScRetraction.isScSubspace_reducedTangentSpaceWith (R : ScRetraction E C)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) :
    E.IsScSubspace (reducedTangentSpaceWith R T x) := by
  classical
  set P := scDeriv R.U R x with hPdef
  have hA := (R.isScSplitting_range_scDeriv hx hs).1
  have hop := R.isScOperator_scDeriv (R.lvlSet_retract_subset 1 hx) hs
  set Pop := hop.toScOperator with hPop
  have hP0 : ∀ v, Pop 0 v = P v := fun v => by rw [hPop, hop.toScOperator_zero]
  have hPP : ∀ v, P (P v) = P v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hx)
  have hPfix : ∀ v ∈ LinearMap.range (P : E 0 →ₗ[ℝ] E 0), P v = v := by
    rintro _ ⟨u, rfl⟩; exact hPP u
  set x0 := E.toBase 1 x with hx0
  refine ⟨(hA.1.inter (isClosed_minimalSubspaceWith T x0)), fun m u hu => ?_⟩
  have huP : E.toBase m u ∈ LinearMap.range (P : E 0 →ₗ[ℝ] E 0) := (Submodule.mem_inf.1 hu).1
  have huE : E.toBase m u ∈ minimalSubspaceWith T x0 := (Submodule.mem_inf.1 hu).2
  set a := (T m u).1 with ha
  have ha0 : (T 0 (E.toBase m u)).1 = a := by
    rw [← T.toBase_comm, ScBanach.prod_toBase, ScBanach.const_toBase]
  let φ : W m → E m := fun w' => Pop m ((T m).symm (a, w'))
  have hφc : Continuous φ := (Pop m).continuous.comp
    ((T m).symm.continuous.comp (continuous_const.prodMk continuous_id))
  have hPopu : Pop m u = u := E.toBase_injective m (by
    rw [Pop.toBase_comm, hP0]; exact hPfix _ huP)
  have hφw : φ (T m u).2 = u := by
    change Pop m ((T m).symm ((T m u).1, (T m u).2)) = u
    rw [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply, hPopu]
  have hφS : MapsTo φ (W.smoothLvl m)
      ((E.levelSub (reducedTangentSpaceWith R T x) m : Set (E m)) ∩ E.smoothLvl m) := by
    intro w' hw'
    have hbase : E.toBase m (φ w') = P ((T 0).symm (a, W.toBase m w')) := by
      change E.toBase m (Pop m ((T m).symm (a, w'))) = _
      rw [Pop.toBase_comm, hP0, T.symm_toBase_comm, ScBanach.prod_toBase,
        ScBanach.const_toBase]
    refine ⟨?_, ?_⟩
    · change E.toBase m (φ w') ∈ reducedTangentSpaceWith R T x
      rw [hbase]
      refine Submodule.mem_inf.2 ⟨⟨_, rfl⟩, ?_⟩
      refine R.scDeriv_mapsTo_minimalSubspace T hT hx
        ((mem_minimalSubspaceWith T).2 fun i hi => ?_)
      have := (mem_minimalSubspaceWith T).1 huE i hi
      rw [ha0] at this
      rw [ContinuousLinearEquiv.apply_symm_apply]; exact this
    · have hp : ((a, w') : ((ScBanach.const (Fin n → ℝ)).prod W) m) ∈
          ((ScBanach.const (Fin n → ℝ)).prod W).smoothLvl m := by
        rw [ScBanach.prod_smoothLvl]
        exact ⟨by rw [ScBanach.constScale_smoothLvl]; exact mem_univ _, hw'⟩
      exact Pop.mapsTo_smoothLvl m (T.symm.toScOperator.mapsTo_smoothLvl m hp)
  rw [← hφw]
  exact map_mem_closure hφc ((W.dense_smooth m).closure_eq ▸ mem_univ _) hφS

/-- **Remark 2.4.8 (preprint 2.28), refuted**: at every smooth point `x` of every sc-smooth retract `(O, C, E)`
(no tameness), `T_xO = Dr(x)E` is an sc-subspace, `T_x^R O` is an sc-subspace, and the partial
cone `C_xO = {v ∈ T_xO | v ∈ C_x}` **is** a partial quadrant in the sc-Banach space `T_xO` (with
the sc-structure induced from `E`), of dimension `r = rank M ≤ d_C(x)`.  This contradicts the
text's "this is in general not the case" (round-trip item V2.33).

*Proof.* With `P = Dr(x)`, `Λ = coordMapL`, `σ = liftCoord`, the matrix `M = Λ P σ` of `P` on
`E/E_x` is nonnegative and idempotent (`coneMatrix_idem`, `coneMatrix_mapsTo_orthant`), so by
Flor's theorem (`flor_nonnegRange_simplicial`) the cone `range M ∩ [0,∞)^{I(x)}` is generated by
linearly independent `c_1, …, c_r`.  The smooth vectors `ê_s = P σ(c_s) ∈ T_xO` and the
functionals `ℓ_s = (ρ ∘ Λ)_s` (`ρ` a left inverse of `t ↦ Σ t_s c_s`) satisfy `ℓ_s(ê_t) = δ_{st}`,
`T_x^R O = T_xO ∩ ⋂_s ker ℓ_s`, and `C_xO = {v ∈ T_xO | ℓ_s v ≥ 0 ∀ s}`; the sc-isomorphism
`T_xO ≅ ℝ^r ⊕ T_x^R O` of `isPartialQuadrant_ofSubspace` finishes. -/
theorem remark_2_4_8_isPartialQuadrant (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) :
    ∃ hA : E.IsScSubspace (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)),
      E.IsScSubspace (reducedTangentSpaceWith R T x) ∧
      IsPartialQuadrant (E.ofSubspace hA)
        {v : E.levelSub (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) 0 |
          (v : E 0) ∈ partialQuadrantAtWith T (E.toBase 1 x)} := by
  classical
  set P := scDeriv R.U R x with hPdef
  have hA := (R.isScSplitting_range_scDeriv hx hs).1
  have hB := R.isScSubspace_reducedTangentSpaceWith T hT hx hs
  refine ⟨hA, hB, ?_⟩
  have hop := R.isScOperator_scDeriv (R.lvlSet_retract_subset 1 hx) hs
  set Pop := hop.toScOperator with hPop
  have hP0 : ∀ v, Pop 0 v = P v := fun v => by rw [hPop, hop.toScOperator_zero]
  set x0 := E.toBase 1 x with hx0
  set Λ := coordMapL T x0 with hΛ
  set M := coneMatrix T R x with hM
  have hMM : ∀ a, M (M a) = M a := coneMatrix_idem hT hx
  have hpos : MapsTo M (orthant _) (orthant _) := coneMatrix_mapsTo_orthant hT hx
  obtain ⟨r, c, hc, hK⟩ := flor_nonnegRange_simplicial M hMM hpos
  -- the coordinate functionals of the basis `c` of `range M`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin r → ℝ) →ₗ[ℝ] _, Φ = Fintype.linearCombination ℝ c := ⟨_, rfl⟩
  have hΦapp : ∀ t, Φ t = ∑ s, t s • c s := fun t => by
    rw [hΦ, Fintype.linearCombination_apply]
  have hΦc : ∀ j, Φ (Pi.single j 1) = c j := fun j => by
    rw [hΦ, Fintype.linearCombination_apply_single, one_smul]
  have hΦker : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro t ht
    rw [hΦapp] at ht
    exact funext (Fintype.linearIndependent_iff.1 hc t ht)
  obtain ⟨ρ, hρ⟩ := Φ.exists_leftInverse_of_injective hΦker
  have hρΦ : ∀ t, ρ (Φ t) = t := fun t => LinearMap.congr_fun hρ t
  have hMΦ : ∀ a, M a ∈ LinearMap.range Φ := fun a => by
    rw [apply_eq_sum_smul_column]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    have hcol := column_mem_nonnegRange M hpos j
    rw [hK] at hcol
    obtain ⟨t, -, ht⟩ := hcol
    exact ⟨t, by rw [hΦapp]; exact ht.symm⟩
  have hcM : ∀ j, M (c j) = c j := fun j => by
    have hcj : c j ∈ nonnegRange M := by
      rw [hK]
      refine ⟨Pi.single j 1, fun s => by rw [Pi.single_apply]; split_ifs <;> norm_num, ?_⟩
      rw [← hΦapp, hΦc]
    obtain ⟨b, hb⟩ := hcj.1
    rw [← hb, hMM]
  -- the functionals `ℓ_s = (ρ ∘ Λ)_s` and the smooth vectors `ê_s = P σ(c_s)`
  let ℓ : Fin r → E 0 →L[ℝ] ℝ := fun j =>
    (LinearMap.toContinuousLinearMap ((LinearMap.proj j) ∘ₗ ρ)).comp Λ
  have hℓ : ∀ j v, ℓ j v = ρ (Λ v) j := fun j v => rfl
  let e : Fin r → E 0 := fun j => P (liftCoord T x0 (c j))
  have hes : ∀ j, e j ∈ E.smooth := fun j => by
    have h1 : liftCoord T x0 (c j) ∈ E.smoothLvl 0 := by
      rw [liftCoord_eq_coordVec]; exact coordVec_mem_smooth (T := T) (extZero T x0 (c j))
    have := Pop.mapsTo_smoothLvl 0 h1
    have h2 : P (liftCoord T x0 (c j)) ∈ E.smoothLvl 0 := hP0 _ ▸ this
    exact h2
  have he : ∀ j, e j ∈ LinearMap.range (P : E 0 →ₗ[ℝ] E 0) := fun j => ⟨_, rfl⟩
  have hΛe : ∀ j, Λ (e j) = c j := fun j => hcM j
  have hℓe : ∀ i j, ℓ i (e j) = if i = j then 1 else 0 := fun i j => by
    rw [hℓ, hΛe, ← hΦc, hρΦ, Pi.single_apply]
  have hBiff : ∀ v, v ∈ reducedTangentSpaceWith R T x ↔
      v ∈ LinearMap.range (P : E 0 →ₗ[ℝ] E 0) ∧ ∀ j, ℓ j v = 0 := fun v => by
    unfold reducedTangentSpaceWith
    rw [Submodule.mem_inf]
    refine and_congr_right fun hvP => ⟨fun hv j => ?_, fun h => ?_⟩
    · rw [hℓ, (coordMapL_eq_zero_iff T x0 v).2 hv, map_zero]
      rfl
    · obtain ⟨a, ha⟩ := coordMapL_mem_range_coneMatrix hT hx hvP
      obtain ⟨b, hb⟩ := hMΦ a
      have hΛv : Λ v = Φ b := by rw [hb, ha]
      have hb0 : b = 0 := funext fun j => by
        have := h j
        rwa [hℓ, hΛv, hρΦ] at this
      rw [← coordMapL_eq_zero_iff, hΛv, hb0, map_zero]
  have hq := isPartialQuadrant_ofSubspace hA hB ℓ e hes he hℓe hBiff
  convert hq using 1
  ext ⟨w, hw⟩
  have hwP : w ∈ LinearMap.range (P : E 0 →ₗ[ℝ] E 0) := hw
  obtain ⟨a, ha⟩ := coordMapL_mem_range_coneMatrix hT hx hwP
  obtain ⟨b, hb⟩ := hMΦ a
  have hΛw : Λ w = Φ b := by rw [hb, ha]
  have hρw : ρ (Λ w) = b := by rw [hΛw, hρΦ]
  change w ∈ partialQuadrantAtWith T x0 ↔ ∀ j, 0 ≤ ℓ j w
  simp only [hℓ, hρw]
  constructor
  · intro hwC
    have hmem : Λ w ∈ nonnegRange M :=
      ⟨⟨a, ha⟩, (mem_partialQuadrantAtWith_iff_coordMapL T x0 w).1 hwC⟩
    rw [hK] at hmem
    obtain ⟨t, ht, hwt⟩ := hmem
    have : b = t := by rw [← hρw, hwt, ← hΦapp, hρΦ]
    rw [this]; exact ht
  · intro hb0
    refine (mem_partialQuadrantAtWith_iff_coordMapL T x0 w).2 ?_
    have hmem : Λ w ∈ nonnegRange M := by
      rw [hK]; exact ⟨b, hb0, by rw [hΛw, hΦapp]⟩
    exact hmem.2

/-- **Remark 2.4.8 (preprint 2.28), refuted, in the audit's shape** (`B2` of `RoundTrip/Items/V2_33.lean`): for
every sc-smooth retraction `r` in `C = T⁻¹([0,∞)ⁿ ⊕ W)`, every smooth `x ∈ O₁`, and every proof
`h` that `T_xO` is an sc-subspace, the preimage of `C_xO` in `T_xO` is a partial quadrant in the
sc-Banach space `T_xO`.  So the text's "in general this is not the case" is false. -/
theorem remark_2_4_8_partialConeWith (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1)
    (h : E.IsScSubspace (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0))) :
    IsPartialQuadrant (E.ofSubspace h) {v | Subtype.val v ∈ partialConeWith R T x} := by
  obtain ⟨hA, -, hq⟩ := remark_2_4_8_isPartialQuadrant hT hx hs
  convert hq using 2
  ext ⟨w, hw⟩
  constructor
  · intro hv; exact hv.2
  · intro hv
    refine ⟨?_, hv⟩
    obtain ⟨u, hu⟩ := (hw : w ∈ LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0))
    exact ⟨u, hu⟩

end Main

end Polyfold
