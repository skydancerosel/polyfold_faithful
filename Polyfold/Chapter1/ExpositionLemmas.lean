import Polyfold.Chapter1.Levels
import Polyfold.Chapter1.ScFredholm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.1–§1.2:
the lemmas that `Exposition/Chapter1.md` adds to the text in order to make its definitions and
remarks precise (Lemmas 1.A(2)–(3), 2.B, 2.C, 3.F of the exposition), and the remark after
Definition 1.1.15 (preprint 1.14) that in finite dimensions sc¹ is `C¹`, for relatively open subsets of quadrants
(with one-sided derivatives at boundary points).

# Lemmas of the exposition of Chapter 1

## What is formalized

* **Lemma 1.A(2)** (Definition 1.1.1 (preprint 1.1): "a finite-dimensional Banach space has exactly one
  sc-structure, the constant one"): `Polyfold.ScBanach.smooth_eq_top_of_finiteDimensional`,
  `Polyfold.ScBanach.toBase_bijective_of_finiteDimensional` and
  `Polyfold.ScBanach.isoConstOfFiniteDimensional`: if `E₀` is finite-dimensional, every inclusion
  `E_m → E₀` is bijective, every point is smooth, and the inclusions form an sc-isomorphism
  `E ≅ E₀` with the constant structure (so the norms on the levels are all equivalent).
  **Lemma 1.A(3)**: `Polyfold.ScScale.finiteDimensional_of_surjective_incl`: if one inclusion
  `E_{m+1} → E_m` is onto, `E_m` is finite-dimensional; so the constant family on an
  infinite-dimensional space is not an sc-structure.
* **Lemma 2.B** (sc-splittings are sc-projections): `Polyfold.ScBanach.IsScSplitting.scProj`
  (the projection `P` onto `F` along `G`, an sc-operator, level `m` the continuous projection
  onto `F_m` along `G_m`), with `scProj_idem`, `range_scProj`, `ker_scProj`; conversely
  `Polyfold.ScBanach.isScSplitting_of_idem`: for an sc-operator `P` with `P² = P`,
  `E = P(E) ⊕ ker P` is an sc-splitting; `Polyfold.ScBanach.isScSplitting_iff_exists_scProj`.
* **Lemma 2.C** (the smooth points of a quotient, the equality the text asserts in the proof of
  Proposition 1.1.8 (preprint 1.7)): `Polyfold.ScBanach.exists_smooth_mem_coset`: if `A` is an sc-subspace and the
  coset `x + A` meets every `E_j`, it meets `E_∞`; `Polyfold.ScBanach.mk_mem_quotient_smooth_iff`:
  the smooth points of `E/A` are exactly the classes of smooth points of `E`.
* Lemma 3.A(2) (`C¹` is a partial quadrant in `E¹`, `U¹` relatively open in it) and Lemma 3.B
  (`TC` is a partial quadrant in `TE`, `TU` relatively open in it) are proved with Chapter 2, where
  they are first needed: `Polyfold.IsPartialQuadrant.shift`, `Polyfold.IsRelOpenInQuadrant.shift`
  (`Chapter2/LevelPolyfold.lean`) and `Polyfold.IsPartialQuadrant.tangentSet`,
  `Polyfold.IsRelOpenInQuadrant.tangentSet` (`Chapter2/TangentBundle.lean`).
* **Lemma 3.F** (what continuity of the derivative means):
  `Polyfold.continuousOn_apply_iff_uniformOnCompact`: for `A : X → L(Y, Z)` the map
  `(x, h) ↦ A(x)h` is continuous on `s × Y` iff `x ↦ A(x)` is continuous on `s` for the topology of
  uniform convergence on compact subsets of `Y`; `Polyfold.IsSc1With.deriv_uniformOnCompact`
  applies it to `Df` on `U₁` (level `0` of condition (3) of Definition 1.1.15 (preprint 1.14)).
* **The finite-dimensional remark after Definition 1.1.15 (preprint 1.14)**, on sc-domains (in particular on
  relatively open subsets of partial quadrants, with boundary):
  `Polyfold.isSc1_iff_contDiffOn_const`, `Polyfold.isSc1_iff_fderivWithin_const`,
  `Polyfold.isScSmooth_iff_contDiffOn_const`,
  `Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant`:
  for `f : V → W` between finite-dimensional spaces with their constant structures, `f` is sc¹ on
  `U` iff it is `C¹` within `U` in Mathlib's sense (differentiable within `U` at every point, with
  `x ↦ fderivWithin f U x` continuous on `U`; at a boundary point of a quadrant this derivative is
  the one-sided one), and sc-smooth iff `C^∞` within `U`.

## What is not formalized

* Lemma 3.F's last sentence (operator-norm continuity can fail): the counterexample is the shift
  map of the exposition's §6, which needs the weighted Sobolev spaces of Example 1.1.3 (preprint 1.2).
  Those spaces are formalized since (`Polyfold.GapP1Sobolev.example_1_1_3`, `CylinderWeakDerivatives`–`13`);
  the shift map on them is not.
-/

open Set Filter Topology Function Metric Module

noncomputable section

namespace Polyfold

/-! ### Lemma 1.A(2)–(3): finite-dimensional spaces -/

namespace ScScale

/-- **Lemma 1.A(3)**: if an inclusion `E_{m+1} → E_m` of a scale is onto, then `E_m` is
finite-dimensional (it is then an isomorphism by the open mapping theorem, so the identity of
`E_m` is compact). Hence the constant family `E_m = E` on an infinite-dimensional Banach space is
not an sc-structure (Definition 1.1.1 (preprint 1.1)). -/
theorem finiteDimensional_of_surjective_incl (E : ScScale) (m : ℕ)
    (h : Surjective (E.incl m)) : FiniteDimensional ℝ (E m) := by
  set e := ContinuousLinearEquiv.ofBijective (E.incl m)
    (LinearMap.ker_eq_bot.2 (E.incl_injective m)) (LinearMap.range_eq_top.2 h) with he
  have hid : (E.incl m).comp (e.symm : E m →L[ℝ] E (m + 1)) = ContinuousLinearMap.id ℝ (E m) := by
    ext x
    change E.incl m (e.symm x) = x
    have : E.incl m (e.symm x) = e (e.symm x) := rfl
    rw [this, ContinuousLinearEquiv.apply_symm_apply]
  have hc : IsCompactOperator ((E.incl m).comp (e.symm : E m →L[ℝ] E (m + 1))) :=
    (E.incl_isCompactOperator m).comp_clm _
  rw [hid] at hc
  exact FiniteDimensional.of_isCompactOperator_id hc

end ScScale

namespace ScBanach

variable (E : ScBanach)

/-- **Lemma 1.A(2)**, first part: if `E₀` is finite-dimensional, every point is smooth. -/
theorem smooth_eq_top_of_finiteDimensional [FiniteDimensional ℝ (E 0)] : E.smooth = ⊤ := by
  have hcl : IsClosed (E.smooth : Set (E 0)) := Submodule.closed_of_finiteDimensional _
  have hd : Dense (E.smooth : Set (E 0)) := E.dense_smooth 0
  rw [← Submodule.coe_eq_univ, ← hcl.closure_eq, hd.closure_eq]

/-- **Lemma 1.A(2)**: if `E₀` is finite-dimensional, every inclusion `E_m → E₀` is bijective. -/
theorem toBase_bijective_of_finiteDimensional [FiniteDimensional ℝ (E 0)] (m : ℕ) :
    Bijective (E.toBase m) := by
  refine ⟨E.toBase_injective m, fun x => ?_⟩
  have hx : x ∈ E.smooth := by rw [E.smooth_eq_top_of_finiteDimensional]; exact Submodule.mem_top
  exact (ScScale.mem_smooth_iff _).1 hx m

/-- **Lemma 1.A(2)**: a finite-dimensional space has only the constant sc-structure: if `E₀` is
finite-dimensional, the inclusions `E_m → E₀` are continuous linear equivalences and form an
sc-isomorphism of `E` onto `E₀` with the constant structure. -/
def isoConstOfFiniteDimensional [FiniteDimensional ℝ (E 0)] : ScIso E (ScBanach.const (E 0)) where
  lvl m := ContinuousLinearEquiv.ofBijective (E.toBase m)
    (LinearMap.ker_eq_bot.2 (E.toBase_bijective_of_finiteDimensional m).1)
    (LinearMap.range_eq_top.2 (E.toBase_bijective_of_finiteDimensional m).2)
  incl_comm _ _ := rfl

theorem isoConstOfFiniteDimensional_apply [FiniteDimensional ℝ (E 0)] (m : ℕ) (x : E m) :
    E.isoConstOfFiniteDimensional m x = E.toBase m x := rfl

end ScBanach

/-! ### Lemma 2.B: sc-splittings are sc-projections -/

namespace ScBanach

variable {E : ScBanach} {A B : Submodule ℝ (E 0)}

lemma IsScSplitting.isTopCompl (h : E.IsScSplitting A B) (m : ℕ) :
    (E.levelSub A m).IsTopCompl (E.levelSub B m) :=
  Submodule.IsCompl.isTopCompl_of_isClosed (h.2.2 m) (E.isClosed_levelSub h.1.1 m)
    (E.isClosed_levelSub h.2.1.1 m)

/-- **Lemma 2.B (i)**: the projection `P : E → E` onto `A` along `B` of an sc-splitting
`E = A ⊕ B`, an sc-operator whose level-`m` map is the continuous projection onto `A_m` along
`B_m`. -/
def IsScSplitting.scProj (h : E.IsScSplitting A B) : ScOperator E E where
  lvl m := (E.levelSub A m).projectionL (E.levelSub B m) (h.isTopCompl m)
  incl_comm m x := by
    set P := (E.levelSub A (m + 1)).projectionL (E.levelSub B (m + 1)) (h.isTopCompl (m + 1))
    set P' := (E.levelSub A m).projectionL (E.levelSub B m) (h.isTopCompl m)
    have hyA : P x ∈ E.levelSub A (m + 1) := Submodule.projectionL_apply_mem _ x
    have hzB : x - P x ∈ E.levelSub B (m + 1) := by
      rw [← Submodule.projectionL_eq_self_sub_projectionL (h.isTopCompl (m + 1))]
      exact Submodule.projectionL_apply_mem _ x
    have h1 : P' (E.incl m (P x)) = E.incl m (P x) :=
      (Submodule.projectionL_eq_self_iff _ _).2 (E.incl_mem_levelSub hyA)
    have h2 : P' (E.incl m (x - P x)) = 0 :=
      (Submodule.projectionL_apply_eq_zero_iff _).2 (E.incl_mem_levelSub hzB)
    rw [map_sub, map_sub, h1, sub_eq_zero] at h2
    exact h2.symm

lemma IsScSplitting.scProj_apply (h : E.IsScSplitting A B) (m : ℕ) (x : E m) :
    h.scProj m x = (E.levelSub A m).projectionL (E.levelSub B m) (h.isTopCompl m) x := rfl

/-- **Lemma 2.B (i)**: `P² = P` on every level. -/
theorem IsScSplitting.scProj_idem (h : E.IsScSplitting A B) (m : ℕ) (x : E m) :
    h.scProj m (h.scProj m x) = h.scProj m x :=
  (Submodule.projectionL_eq_self_iff _ _).2 (Submodule.projectionL_apply_mem _ x)

/-- **Lemma 2.B (i)**: `P(E_m) = A_m`. -/
theorem IsScSplitting.range_scProj (h : E.IsScSplitting A B) (m : ℕ) :
    LinearMap.range (h.scProj m : E m →ₗ[ℝ] E m) = E.levelSub A m := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩; exact Submodule.projectionL_apply_mem _ y
  · intro hx; exact ⟨x, (Submodule.projectionL_eq_self_iff _ _).2 hx⟩

/-- **Lemma 2.B (i)**: `ker P_m = B_m`. -/
theorem IsScSplitting.ker_scProj (h : E.IsScSplitting A B) (m : ℕ) :
    LinearMap.ker (h.scProj m : E m →ₗ[ℝ] E m) = E.levelSub B m := by
  ext x
  exact Submodule.projectionL_apply_eq_zero_iff _

variable (P : ScOperator E E)

/-- An sc-operator idempotent on level `0` is idempotent on every level. -/
lemma _root_.Polyfold.ScOperator.idem_lvl (hP : ∀ x, P 0 (P 0 x) = P 0 x) (m : ℕ) (x : E m) :
    P m (P m x) = P m x := by
  apply E.toBase_injective m
  rw [P.toBase_comm, P.toBase_comm, hP]

lemma _root_.Polyfold.ScOperator.levelSub_range_eq (hP : ∀ x, P 0 (P 0 x) = P 0 x) (m : ℕ) :
    E.levelSub (LinearMap.range (P 0 : E 0 →ₗ[ℝ] E 0)) m =
      LinearMap.range (P m : E m →ₗ[ℝ] E m) := by
  ext x
  rw [mem_levelSub]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨x, E.toBase_injective m ?_⟩
    change E.toBase m (P m x) = E.toBase m x
    rw [P.toBase_comm, ← hy]
    exact hP y
  · rintro ⟨y, rfl⟩
    exact ⟨E.toBase m y, (P.toBase_comm m y).symm⟩

/-- **Lemma 2.B (ii)**: an sc-operator `P` with `P² = P` defines the sc-splitting
`E = P(E) ⊕ ker P`. -/
theorem isScSplitting_of_idem (hP : ∀ x, P 0 (P 0 x) = P 0 x) :
    E.IsScSplitting (LinearMap.range (P 0 : E 0 →ₗ[ℝ] E 0))
      (LinearMap.ker (P 0 : E 0 →ₗ[ℝ] E 0)) := by
  have hidem : ∀ m, IsIdempotentElem (P m : E m →ₗ[ℝ] E m) := fun m =>
    LinearMap.ext fun x => P.idem_lvl hP m x
  have hcl : ∀ m x, x ∈ closure (E.smoothLvl m) := fun m x => by
    rw [(E.dense_smooth m).closure_eq]; exact mem_univ _
  refine ⟨⟨?_, fun m x hx => ?_⟩, ⟨(P 0).isClosed_ker, fun m x hx => ?_⟩, fun m => ?_⟩
  · have : (LinearMap.range (P 0 : E 0 →ₗ[ℝ] E 0) : Set (E 0)) = {x | P 0 x = x} := by
      ext x
      exact ⟨fun ⟨y, hy⟩ => by rw [← hy]; exact hP y, fun h => ⟨x, h⟩⟩
    rw [this]
    exact isClosed_eq (P 0).continuous continuous_id
  · -- `x = P_m x` is a limit of `P_m` of smooth points
    rw [SetLike.mem_coe, P.levelSub_range_eq hP m] at hx
    obtain ⟨y, rfl⟩ := hx
    refine closure_mono ?_ (image_closure_subset_closure_image (P m).continuous ⟨y, hcl m y, rfl⟩)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨?_, P.mapsTo_smoothLvl m hz⟩
    rw [SetLike.mem_coe, P.levelSub_range_eq hP m]
    exact LinearMap.mem_range_self _ _
  · -- `x = x − P_m x` is a limit of `z − P_m z` for smooth `z`
    rw [SetLike.mem_coe, ← ScOperator.ker_lvl] at hx
    have hx0 : P m x = 0 := hx
    let Q : E m →L[ℝ] E m := ContinuousLinearMap.id ℝ (E m) - P m
    have hQx : Q x = x := by simp [Q, hx0]
    rw [← hQx]
    refine closure_mono ?_ (image_closure_subset_closure_image Q.continuous ⟨x, hcl m x, rfl⟩)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, ← ScOperator.ker_lvl, LinearMap.mem_ker]
      simp [Q, P.idem_lvl hP m z]
    · exact E.smoothLvl_submodule_closed_sub hz (P.mapsTo_smoothLvl m hz)
  · rw [P.levelSub_range_eq hP m, ← ScOperator.ker_lvl]
    exact LinearMap.IsIdempotentElem.isCompl (hidem m)

/-- **Lemma 2.B**: `E = A ⊕ B` is an sc-splitting iff there is an sc-operator `P` with `P² = P`,
`P(E) = A` and `ker P = B`. -/
theorem isScSplitting_iff_exists_scProj :
    E.IsScSplitting A B ↔ ∃ P : ScOperator E E, (∀ x, P 0 (P 0 x) = P 0 x) ∧
      LinearMap.range (P 0 : E 0 →ₗ[ℝ] E 0) = A ∧ LinearMap.ker (P 0 : E 0 →ₗ[ℝ] E 0) = B := by
  constructor
  · intro h
    refine ⟨h.scProj, h.scProj_idem 0, ?_, ?_⟩
    · rw [h.range_scProj 0, levelSub_zero]
    · rw [h.ker_scProj 0, levelSub_zero]
  · rintro ⟨P, hP, rfl, rfl⟩
    exact isScSplitting_of_idem P hP

end ScBanach

/-! ### Lemma 2.C: the smooth points of a quotient -/

namespace ScBanach

variable (E : ScBanach)

/-- `∏_{i<j} max 1 ‖incl_i‖`, a bound for the norms of the inclusions `E_j → E_i`, `i ≤ j`. -/
private def inclBound (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, max 1 ‖E.incl i‖

private lemma one_le_inclBound : ∀ j, 1 ≤ E.inclBound j
  | 0 => by simp [inclBound]
  | j + 1 => by
    rw [inclBound, Finset.prod_range_succ]
    exact one_le_mul_of_one_le_of_one_le (one_le_inclBound j) (le_max_left _ _)

private lemma norm_incl_le (j : ℕ) (v : E (j + 1)) : ‖E.incl j v‖ ≤ max 1 ‖E.incl j‖ * ‖v‖ :=
  ((E.incl j).le_opNorm v).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

private lemma norm_toBase_le : ∀ (j : ℕ) (v : E j), ‖E.toBase j v‖ ≤ E.inclBound j * ‖v‖
  | 0, v => by simp [inclBound]
  | j + 1, v => by
    rw [ScScale.toBase_succ]
    calc ‖E.toBase j (E.incl j v)‖ ≤ E.inclBound j * ‖E.incl j v‖ := norm_toBase_le j _
      _ ≤ E.inclBound j * (max 1 ‖E.incl j‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (E.norm_incl_le j v) (by linarith [E.one_le_inclBound j])
      _ = E.inclBound (j + 1) * ‖v‖ := by
        simp only [inclBound, Finset.prod_range_succ]; ring

private lemma norm_inclK_le (J : ℕ) : ∀ (k : ℕ) (v : E (J + k)),
    ‖E.inclK J k v‖ ≤ E.inclBound (J + k) * ‖v‖
  | 0, v => by
    simp only [ScScale.inclK_zero]
    exact le_mul_of_one_le_left (norm_nonneg _) (E.one_le_inclBound _)
  | k + 1, v => by
    rw [ScScale.inclK_succ]
    calc ‖E.inclK J k (E.incl (J + k) v)‖ ≤ E.inclBound (J + k) * ‖E.incl (J + k) v‖ :=
          norm_inclK_le J k _
      _ ≤ E.inclBound (J + k) * (max 1 ‖E.incl (J + k)‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (E.norm_incl_le _ v) (by linarith [E.one_le_inclBound (J + k)])
      _ = E.inclBound (J + (k + 1)) * ‖v‖ := by
        have hP : E.inclBound (J + (k + 1)) = E.inclBound (J + k) * max 1 ‖E.incl (J + k)‖ :=
          Finset.prod_range_succ _ _
        rw [hP, mul_assoc]

/-- **Lemma 2.C** (a Mittag-Leffler argument): if `A` is an sc-subspace and the coset `x + A`
meets every level `E_j`, then it contains a smooth point. -/
theorem exists_smooth_mem_coset {A : Submodule ℝ (E 0)} (hA : E.IsScSubspace A) {x : E 0}
    (hx : ∀ j, ∃ y : E j, E.toBase j y - x ∈ A) : ∃ y ∈ E.smooth, y - x ∈ A := by
  choose xs hxs using hx
  -- the differences `d_j = x_{j+1} − x_j ∈ A_j`
  set d : ∀ j, E j := fun j => E.incl j (xs (j + 1)) - xs j with hd
  have htd : ∀ j, E.toBase j (d j) = E.toBase (j + 1) (xs (j + 1)) - E.toBase j (xs j) := by
    intro j; rw [hd, map_sub, ScScale.toBase_succ]
  have hdA : ∀ j, d j ∈ E.levelSub A j := fun j => by
    rw [mem_levelSub, htd]
    have := A.sub_mem (hxs (j + 1)) (hxs j)
    rwa [sub_sub_sub_cancel_right] at this
  -- smooth approximations `c_j ∈ A_j ∩ E_∞` with `‖d_j − c_j‖ ≤ 2^{-j} / inclBound j`
  have hc : ∀ j, ∃ c ∈ (E.levelSub A j : Set (E j)) ∩ E.smoothLvl j,
      ‖d j - c‖ ≤ (1 / 2 : ℝ) ^ j / E.inclBound j := by
    intro j
    have hpos : 0 < (1 / 2 : ℝ) ^ j / E.inclBound j :=
      div_pos (by positivity) (by linarith [E.one_le_inclBound j])
    obtain ⟨c, hc, hdc⟩ := Metric.mem_closure_iff.1 (hA.2 j (hdA j)) _ hpos
    exact ⟨c, hc, by rw [← dist_eq_norm]; exact hdc.le⟩
  choose c hcmem hcnorm using hc
  set b : ∀ j, E j := fun j => d j - c j with hb
  have hbA : ∀ j, E.toBase j (b j) ∈ A := fun j => (E.levelSub A j).sub_mem (hdA j) (hcmem j).1
  have hbound : ∀ j, E.inclBound j * ‖b j‖ ≤ (1 / 2 : ℝ) ^ j := fun j => by
    have h1 := E.one_le_inclBound j
    have := mul_le_mul_of_nonneg_left (hcnorm j) (by linarith : 0 ≤ E.inclBound j)
    rwa [mul_div_cancel₀ _ (by linarith : E.inclBound j ≠ 0)] at this
  set g : ℕ → E 0 := fun j => E.toBase j (b j) with hg
  have hgeom := summable_geometric_two
  have hsum0 : Summable g :=
    Summable.of_norm_bounded hgeom fun j => (E.norm_toBase_le j (b j)).trans (hbound j)
  set S := ∑' j, g j with hS
  refine ⟨xs 0 + S, ?_, ?_⟩
  · rw [ScScale.mem_smooth_iff]
    intro J
    -- the tail `∑_{j ≥ J} b_j` converges in `E_J`
    have hsumJ : Summable fun k => E.inclK J k (b (J + k)) := by
      refine Summable.of_norm_bounded (hgeom.mul_left ((1 / 2 : ℝ) ^ J)) fun k => ?_
      rw [← pow_add]
      exact (E.norm_inclK_le J k _).trans (hbound (J + k))
    set t := ∑' k, E.inclK J k (b (J + k)) with ht
    have htJ : E.toBase J t = ∑' k, g (k + J) := by
      rw [ht, ContinuousLinearMap.map_tsum _ hsumJ]
      congr 1; funext k
      rw [E.toBase_inclK J k, add_comm k J]
    -- the head: telescoping
    have htel : ∑ j ∈ Finset.range J, E.toBase j (d j) = E.toBase J (xs J) - xs 0 := by
      rw [Finset.sum_congr rfl fun j _ => htd j,
        Finset.sum_range_sub (fun j => E.toBase j (xs j)) J]
      rfl
    have hhead : ∑ j ∈ Finset.range J, g j =
        (E.toBase J (xs J) - xs 0) - ∑ j ∈ Finset.range J, E.toBase j (c j) := by
      rw [← htel, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hg, hb]; simp only; rw [map_sub]
    have hcs : (∑ j ∈ Finset.range J, E.toBase j (c j)) ∈ E.smooth :=
      Submodule.sum_mem _ fun j _ => (hcmem j).2
    obtain ⟨w, hw⟩ := (ScScale.mem_smooth_iff _).1 hcs J
    refine ⟨xs J - w + t, ?_⟩
    rw [map_add, map_sub, hw, htJ, hS, ← hsum0.sum_add_tsum_nat_add J, hhead]
    abel
  · have hSA : S ∈ A := by
      refine hA.isClosed.mem_of_tendsto hsum0.hasSum.tendsto_sum_nat
        (Eventually.of_forall fun n => ?_)
      exact A.sum_mem fun j _ => hbA j
    have := A.add_mem (hxs 0) hSA
    convert this using 1
    rw [ScScale.toBase_zero]; abel

/-- **Lemma 2.C**, as the description of `(E/A)_∞` in the proof of Proposition 1.1.8 (preprint 1.7): the class of
`x ∈ E₀` is a smooth point of `E/A` iff `x + A` contains a smooth point of `E`. -/
theorem mk_mem_quotient_smooth_iff {A : Submodule ℝ (E 0)} (hA : E.IsScSubspace A) (x : E 0) :
    (Submodule.Quotient.mk x : (E.quotient hA.isClosed) 0) ∈ (E.quotient hA.isClosed).smooth ↔
      ∃ y ∈ E.smooth, y - x ∈ A := by
  refine (ScScale.mem_smooth_iff _).trans ?_
  constructor
  · intro h
    refine E.exists_smooth_mem_coset hA fun j => ?_
    obtain ⟨z, hz⟩ := h j
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨y, ?_⟩
    have hz' := (E.quotientScale_toBase_mk hA.isClosed j y).symm.trans hz
    exact (Submodule.Quotient.eq _).1 hz'
  · rintro ⟨y, hy, hyx⟩ j
    obtain ⟨z, hz⟩ := (ScScale.mem_smooth_iff _).1 hy j
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    refine (E.quotientScale_toBase_mk hA.isClosed j z).trans ?_
    rw [hz]
    exact (Submodule.Quotient.eq _).2 hyx

end ScBanach

/-! ### Lemma 3.F: joint continuity is compact-open continuity -/

/-- **Lemma 3.F**: for `A : X → L(Y, Z)` and `s ⊆ X`, the map `(x, h) ↦ A(x)h` is continuous on
`s × Y` iff `x ↦ A(x)` is continuous on `s` for the topology of uniform convergence on compact
subsets of `Y`: for `x ∈ s`, `K ⊆ Y` compact and `ε > 0`, `‖A(x')w − A(x)w‖ < ε` for all `w ∈ K`
and all `x' ∈ s` near `x`. -/
theorem continuousOn_apply_iff_uniformOnCompact {X Y Z : Type*} [MetricSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {A : X → Y →L[ℝ] Z} {s : Set X} :
    ContinuousOn (fun p : X × Y => A p.1 p.2) {p | p.1 ∈ s} ↔
      ∀ x ∈ s, ∀ K : Set Y, IsCompact K → ∀ ε > 0,
        ∀ᶠ x' in 𝓝[s] x, ∀ w ∈ K, ‖A x' w - A x w‖ < ε := by
  constructor
  · intro hc x hx K hK ε hε
    let Θ : s × Y → Z := fun q => A q.1.1 q.2 - A x q.2
    have hΘ : Continuous Θ := by
      have h1 : Continuous fun q : s × Y => A q.1.1 q.2 := by
        refine hc.comp_continuous (f := fun q : s × Y => ((q.1 : X), q.2)) (by fun_prop) ?_
        intro q; exact q.1.2
      exact h1.sub ((A x).continuous.comp continuous_snd)
    have key : ∀ᶠ y in 𝓝 (⟨x, hx⟩ : s), ∀ w ∈ K, ‖Θ (y, w)‖ < ε := by
      refine hK.eventually_forall_of_forall_eventually fun w _ => ?_
      have h0 : Θ (⟨x, hx⟩, w) = 0 := sub_self _
      have := hΘ.tendsto (⟨x, hx⟩, w)
      rw [h0] at this
      exact (this.eventually (Metric.ball_mem_nhds 0 hε)).mono fun q hq => by
        simpa [dist_eq_norm] using hq
    have key' : ∀ᶠ y : s in 𝓝 (⟨x, hx⟩ : s),
        (fun x' : X => ∀ w ∈ K, ‖A x' w - A x w‖ < ε) (y : X) := key
    rw [eventually_nhds_subtype_iff s ⟨x, hx⟩ (fun x' : X => ∀ w ∈ K, ‖A x' w - A x w‖ < ε)] at key'
    exact key'
  · intro h p hp
    obtain ⟨x, w⟩ := p
    change x ∈ s at hp
    rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
    intro q hq
    rw [tendsto_nhdsWithin_iff] at hq
    have hq1 : Tendsto (fun n => (q n).1) atTop (𝓝[s] x) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto _).comp hq.1, hq.2⟩
    have hq2 : Tendsto (fun n => (q n).2) atTop (𝓝 w) := (continuous_snd.tendsto _).comp hq.1
    have hK := hq2.isCompact_insert_range
    have hA : Tendsto (fun n => A (q n).1 (q n).2 - A x (q n).2) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hq1.eventually (h x hp _ hK ε hε)] with n hn
      rw [dist_zero_right]
      exact hn _ (mem_insert_of_mem _ ⟨n, rfl⟩)
    have hB : Tendsto (fun n => A x (q n).2) atTop (𝓝 (A x w)) :=
      ((A x).continuous.tendsto w).comp hq2
    have := hA.add hB
    simp only [sub_add_cancel, zero_add] at this
    exact this

/-- **Lemma 3.F** for an sc¹ map: level `0` of condition (3) of Definition 1.1.15 (preprint 1.14) (the continuity of
`(x, h) ↦ Df(x)h` on `U₁ × E₀`) makes `x ↦ Df(x)` continuous on `U₁` for the topology of uniform
convergence on compact subsets of `E₀`. -/
theorem IsSc1With.deriv_uniformOnCompact {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0}
    {D : E 1 → E 0 →L[ℝ] F 0} (h : IsSc1With U f D) {x : E 1} (hx : x ∈ E.lvlSet U 1)
    {K : Set (E 0)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝[E.lvlSet U 1] x, ∀ w ∈ K, ‖D x' w - D x w‖ < ε :=
  continuousOn_apply_iff_uniformOnCompact.1 h.continuousOn_deriv x hx K hK ε hε

/-! ### Finite dimensions: sc¹ is `C¹` on relatively open subsets of quadrants -/

section FiniteDimensional

open scoped ContDiff

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- The level sets of the constant structure are the set itself. -/
lemma ScBanach.lvlSet_const (U : Set V) (m : ℕ) : (ScBanach.const V).lvlSet U m = U := by
  ext x
  rw [ScBanach.mem_lvlSet, ScBanach.const_toBase]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
private lemma comp_toBase_const (f : V → W) (m : ℕ) : f ∘ (ScBanach.const V).toBase m = f :=
  funext fun x => congrArg f (ScBanach.const_toBase V m x)

/-- **Finite dimensions: sc¹ is `C¹`** (the remark after Definition 1.1.15 (preprint 1.14)), on every sc-domain `U`
of `V` with its constant structure, in particular on every relatively open subset of a partial
quadrant: `f` is sc¹ on `U` iff it is `C¹` within `U`. -/
theorem isSc1_iff_contDiffOn_const {U : Set V} (hU : IsScDomain (ScBanach.const V) U)
    (f : (ScBanach.const V) 0 → (ScBanach.const W) 0) : IsSc1 U f ↔ ContDiffOn ℝ 1 f U := by
  constructor
  · rintro ⟨D, hD⟩
    have := hD.contDiffOn_base
    rwa [ScBanach.lvlSet_const, comp_toBase_const] at this
  · intro hf
    refine corollary_1_2_5_zero hU fun m => ?_
    rw [ScBanach.lvlSet_const, comp_toBase_const]
    exact hf

/-- The same, with the meaning of `C¹` on a set with boundary spelled out: `f` is sc¹ on `U` iff it
is differentiable within `U` at every point of `U` (at a boundary point of a quadrant: with the
one-sided derivative along `U`) and `x ↦ fderivWithin f U x` is continuous on `U`. -/
theorem isSc1_iff_fderivWithin_const {U : Set V} (hU : IsScDomain (ScBanach.const V) U)
    (f : (ScBanach.const V) 0 → (ScBanach.const W) 0) :
    IsSc1 U f ↔ DifferentiableOn ℝ f U ∧ ContinuousOn (fderivWithin ℝ f U) U := by
  rw [isSc1_iff_contDiffOn_const hU]
  have hUD : UniqueDiffOn ℝ U := fun x hx => by
    have := hU.uniqueDiffWithinAt 0 x (by rwa [ScBanach.lvlSet_const])
    rwa [ScBanach.lvlSet_const] at this
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderivWithin hUD]
  simp [contDiffOn_zero]

/-- **Finite dimensions: sc-smooth is `C^∞`**, on every sc-domain. -/
theorem isScSmooth_iff_contDiffOn_const {U : Set V} (hU : IsScDomain (ScBanach.const V) U)
    (f : (ScBanach.const V) 0 → (ScBanach.const W) 0) :
    IsScSmooth U f ↔ ContDiffOn ℝ ∞ f U := by
  constructor
  · intro hf
    rw [contDiffOn_infty]
    intro k
    have := (hf k).contDiffOn_base hU
    rwa [ScBanach.lvlSet_const, comp_toBase_const] at this
  · intro hf
    exact IsScSmooth.of_contDiffOn_finiteDimensional hU hf

/-- The finite-dimensional remark for the text's tuples: on a relatively open subset `U` of a
partial quadrant `C` of `V`, sc¹ is `C¹` within `U`. -/
theorem isSc1_iff_contDiffOn_of_isRelOpenInQuadrant {C U : Set V}
    (hU : IsRelOpenInQuadrant (ScBanach.const V) C U)
    (f : (ScBanach.const V) 0 → (ScBanach.const W) 0) : IsSc1 U f ↔ ContDiffOn ℝ 1 f U :=
  isSc1_iff_contDiffOn_const hU.isScDomain f

/-- The same for sc-smooth and `C^∞`. -/
theorem isScSmooth_iff_contDiffOn_of_isRelOpenInQuadrant {C U : Set V}
    (hU : IsRelOpenInQuadrant (ScBanach.const V) C U)
    (f : (ScBanach.const V) 0 → (ScBanach.const W) 0) : IsScSmooth U f ↔ ContDiffOn ℝ ∞ f U :=
  isScSmooth_iff_contDiffOn_const hU.isScDomain f

end FiniteDimensional

end Polyfold
