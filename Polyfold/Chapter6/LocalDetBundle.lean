import Polyfold.Chapter6.ProjectionSequence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.4,
pp. 214–217: **Lemma 6.5.1 (preprint 6.17)** (`P ∈ Π_S` and `P S|_Y` an isomorphism for `S` near `T`),
**Lemma 6.5.2 (preprint 6.18)** (the kernel bundle `⋃ {S} × ker(P S)` is trivial), **Lemma 6.5.3 (preprint 6.19)** (in the case
used), **Proposition 6.5.4 (preprint 6.20)** (the local determinant bundle `DET(T, P, ε)`) and **Lemma 6.5.5 (preprint 6.21)**
(`γ^Q_{PS}` is continuous in `S`) *(book 2017: Lemmas 6.7–6.9, Proposition 6.8, Lemma 6.10; see
`BookConcordance.md`)*.

# Local determinant bundles

## The text, paraphrased

(Lemma 6.5.1 (preprint 6.17)) For `T` Fredholm, `P ∈ Π_T` and a topological complement `Y` of `ker(P T)`, there is
`ε > 0` such that for `‖S − T‖ < ε`: `P ∈ Π_S`, and `P S|_Y : Y → R(P)` is a topological
isomorphism.  Writing `e = k + y`, `P S (k + y) = 0` is solved by
`y(k, S) = −(P S|_Y)⁻¹(P S k)`, continuous in `(k, S)`.  (Lemma 6.5.2 (preprint 6.18))
`⋃_{‖S − T‖ < ε} {S} × ker(P S) ⊂ L(E, F) ⊕ E` is a trivial vector bundle, trivialized by
`(S, k) ↦ (S, k + y(k, S))` on `{S} × ker(P T)`, with inverse the restriction of
`(S, k + y) ↦ (S, k)`.  (Lemma 6.5.3 (preprint 6.19), cited) `λ`, `λ*`, `⊕`, `⊗` of finite-dimensional
topological vector bundles are topological vector bundles.  (Proposition 6.5.4 (preprint 6.20)) Hence
`DET(T, P, ε) = ⋃_{‖S − T‖ < ε} {S} × det(P S)` is a topological line bundle in a natural way.
(Lemma 6.5.5 (preprint 6.21)) For `Q ≤ P` in `Π_T`, `(S, h) ↦ (S, γ^Q_{PS}(h))` is an isomorphism of line bundles
`DET(T, P, ε) → DET(T, Q, ε)`.

## What is formalized

* `Polyfold.FredholmOp E F`, the Fredholm operators with the norm topology;
  `Polyfold.projRestrict P S Y` (`P S|_Y : Y → R(P)`) and **Lemma 6.5.1 (preprint 6.17)** (`lemma_6_5_1`), without
  the hypothesis that `T` is Fredholm (not used); a topological complement is Mathlib's
  `Submodule.IsTopCompl` (algebraic complement with continuous projection).
* `Polyfold.LocalDetChart`: the data `(T, P, Y, ε)` of the text with the conclusions of
  Lemma 6.5.1 (preprint 6.17); `ySol` (`y(·, S)`), `kerMap` (`k ↦ k + y(k, S)`), `kerProj` (the projection onto
  `ker(P T)` along `Y`) and **Lemma 6.5.2 (preprint 6.18)** (`lemma_6_5_2`), stated concretely: the trivialization is
  continuous, maps `ker(P T)` onto `ker(P S)`, and is inverted by the continuous `kerProj`.
* `LocalDetChart.kerFrame`, `LocalDetChart.frame` (`ω(S) = (k₁(S) ∧ … ∧ kₙ(S)) ⊗ (e₁ ∧ … ∧ e_l)*`,
  the frame of `DET(T, P, ε)` over the ball), `frame_ne_zero`.
* **Proposition 6.5.4 (preprint 6.20)** (`proposition_6_5_4`): the structure is natural — the frames of two charts
  with the same `P` differ by a continuous nowhere-zero factor.
* **Lemma 6.5.5 (preprint 6.21)** (`lemma_6_5_5`): for `Q ≤ P`, `γ^Q_{PS}` maps the `P`-frame to a continuous
  nowhere-zero multiple of the `Q`-frame, on the common ball (of any two charts).

## Reading

Lemma 6.5.3 (preprint 6.19) is not formalized in general (Mathlib has no exterior powers or tensor products of
vector bundles); the only bundles it is applied to are trivial, and Proposition 6.5.4 (preprint 6.20) is proved
with explicit frames: the wedge of the kernel frame `kᵢ + y(kᵢ, S)` and a constant basis of
`F / R(P) = F / R(P S)`.  "In a natural way" is read as: the frames of two charts with the same `P`
are related by a continuous nowhere-zero function.  Lemma 6.5.5 (preprint 6.21) is stated for two charts (different
centres and radii), which is the form Lemma 6.5.9 (preprint 6.25) uses; the text's sketch ("extend the kernel
sections for the `P S` to … sections spanning `ker(Q S)`") is the proof.
-/

open Module TensorProduct

noncomputable section

namespace Polyfold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

variable (E F) in
/-- The Fredholm operators `F(E, F) ⊂ L(E, F)`, with the norm topology. -/
abbrev FredholmOp : Type _ := {T : E →L[ℝ] F // T.IsFredholm}

/-- `P S|_Y : Y → R(P)`, `y ↦ P S y`. -/
def projRestrict (P : F →L[ℝ] F) (S : E →L[ℝ] F) (Y : Submodule ℝ E) :
    Y →L[ℝ] LinearMap.range (P : F →ₗ[ℝ] F) :=
  ((P ∘L S).comp Y.subtypeL).codRestrict _ (fun y => ⟨S y, rfl⟩)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem coe_projRestrict_apply (P : F →L[ℝ] F) (S : E →L[ℝ] F) (Y : Submodule ℝ E)
    (y : Y) : (projRestrict P S Y y : F) = P (S y) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- `‖P S|_Y − P S'|_Y‖ ≤ ‖P‖ ‖S − S'‖`. -/
theorem norm_projRestrict_sub_le (P : F →L[ℝ] F) (S S' : E →L[ℝ] F) (Y : Submodule ℝ E) :
    ‖projRestrict P S Y - projRestrict P S' Y‖ ≤ ‖P‖ * ‖S - S'‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have h : ((projRestrict P S Y - projRestrict P S' Y) y : F) = P ((S - S') y) := by
    simp [map_sub]
  calc ‖(projRestrict P S Y - projRestrict P S' Y) y‖ = ‖P ((S - S') y)‖ := by
        rw [← h]; rfl
    _ ≤ ‖P‖ * ‖(S - S') y‖ := P.le_opNorm _
    _ ≤ ‖P‖ * (‖S - S'‖ * ‖(y : E)‖) := by gcongr; exact (S - S').le_opNorm _
    _ = ‖P‖ * ‖S - S'‖ * ‖y‖ := by rw [mul_assoc]; rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- `S ↦ P S|_Y` is continuous (it is `‖P‖`-Lipschitz). -/
theorem continuous_projRestrict (P : F →L[ℝ] F) (Y : Submodule ℝ E) :
    Continuous fun S : E →L[ℝ] F => projRestrict P S Y :=
  (LipschitzWith.of_dist_le_mul (K := ‖P‖₊) fun S S' => by
    rw [dist_eq_norm, dist_eq_norm, coe_nnnorm]
    exact norm_projRestrict_sub_le P S S' Y).continuous

/-- `(a v)* = a⁻¹ v*` in a line, also for `a = 0` (both sides vanish). -/
theorem dualVec_smul_eq_inv_smul {L : Type*} [AddCommGroup L] [Module ℝ L]
    (h1 : finrank ℝ L = 1) {v : L} (hv : v ≠ 0) (a : ℝ) :
    dualVec (a • v) = a⁻¹ • dualVec v := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_smul, inv_zero, zero_smul]
    unfold dualVec
    exact dif_neg fun h => h.1 rfl
  · exact dualVec_smul h1 hv ha

/-- A determinant in a basis of a finite-dimensional normed space is continuous in the family. -/
theorem continuous_basis_det {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [FiniteDimensional ℝ M] {k : ℕ} (u : Basis (Fin k) ℝ M) :
    Continuous fun v : Fin k → M => u.det v := by
  simp_rw [Basis.det_apply]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  simp_rw [Basis.toMatrix_apply]
  exact (u.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)

/-- `F / q → F / r` after `F / p → F / q` (all three quotient identifications) is
`F / p → F / r`. -/
theorem quotEquivOfEq_apply_symm_apply {G : Type*} [AddCommGroup G] [Module ℝ G]
    {p q r : Submodule ℝ G} (hqp : q = p) (hqr : q = r) (hpr : p = r) (x : G ⧸ p) :
    Submodule.quotEquivOfEq q r hqr ((Submodule.quotEquivOfEq q p hqp).symm x) =
      Submodule.quotEquivOfEq p r hpr x := by
  induction x using Submodule.Quotient.induction_on
  rfl

/-- **Lemma 6.5.1 (preprint 6.17)**: for `P ∈ Π_T` and a topological complement `Y` of `ker(P T)` there is
`ε > 0` such that for every `S` with `‖S − T‖ < ε`: (1) `P ∈ Π_S`; (2) `P S|_Y : Y → R(P)` is a
topological isomorphism. -/
theorem lemma_6_5_1 {T : E →L[ℝ] F} {P : F →L[ℝ] F} (hP : IsGoodLeftProj T P)
    {Y : Submodule ℝ E} (hY : (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).IsTopCompl Y) :
    ∃ ε > 0, ∀ S : E →L[ℝ] F, ‖S - T‖ < ε →
      IsGoodLeftProj S P ∧
        ∃ e : Y ≃L[ℝ] LinearMap.range (P : F →ₗ[ℝ] F),
          (e : Y →L[ℝ] LinearMap.range (P : F →ₗ[ℝ] F)) = projRestrict P S Y := by
  have : CompleteSpace (LinearMap.range (P : F →ₗ[ℝ] F)) := hP.isClosed_range.completeSpace_coe
  have : CompleteSpace Y := hY.isClosed'.completeSpace_coe
  have hinj : Function.Injective (projRestrict P T Y) := by
    refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    have hK : (y : E) ∈ LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
      have := congrArg Subtype.val hy
      simpa using this
    exact Subtype.ext (Submodule.disjoint_def.1 hY.isCompl.disjoint _ hK y.2)
  have hsurj : Function.Surjective (projRestrict P T Y) := by
    rintro ⟨r, hr⟩
    rw [← hP.range_comp] at hr
    obtain ⟨x, hx⟩ := hr
    set k := (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).projection Y hY.isCompl x
    have hk : k ∈ LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
      Submodule.projection_apply_mem _ _
    have hy : x - k ∈ Y := Submodule.sub_projection_mem hY.isCompl x
    refine ⟨⟨x - k, hy⟩, Subtype.ext ?_⟩
    have hk' : P (T k) = 0 := hk
    have hx' : P (T x) = r := hx
    simp [map_sub, hk', hx']
  set eT := ContinuousLinearEquiv.ofBijective (projRestrict P T Y)
    (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj)
  have heT : (eT : Y →L[ℝ] LinearMap.range (P : F →ₗ[ℝ] F)) = projRestrict P T Y :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (ContinuousLinearEquiv.isOpen (𝕜 := ℝ)
    (E := Y) (F := LinearMap.range (P : F →ₗ[ℝ] F))) _ ⟨eT, heT⟩
  refine ⟨δ / (‖P‖ + 1), by positivity, fun S hS => ?_⟩
  have hdist : ‖projRestrict P S Y - projRestrict P T Y‖ < δ := by
    have h1 := norm_projRestrict_sub_le P S T Y
    have h2 : ‖S - T‖ * (‖P‖ + 1) < δ := (lt_div_iff₀ (by positivity)).1 hS
    nlinarith [norm_nonneg (S - T), norm_nonneg P]
  obtain ⟨e, he⟩ := hball (mem_ball_iff_norm.2 hdist)
  refine ⟨⟨hP.isProj, hP.finite_coker, ?_⟩, e, he⟩
  refine le_antisymm ?_ fun r hr => ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨S x, rfl⟩
  · obtain ⟨y, hy⟩ := e.surjective ⟨r, hr⟩
    refine ⟨y, ?_⟩
    have := congrArg Subtype.val ((DFunLike.congr_fun he y).symm.trans hy)
    simpa using this

variable (E F) in
/-- The data of a local determinant bundle `DET(T, P, ε)`: a Fredholm operator `T`, `P ∈ Π_T`, a
topological complement `Y` of `ker(P T)` and a radius `ε` for which the conclusions of Lemma 6.5.1 (preprint 6.17)
hold. -/
structure LocalDetChart where
  /-- The centre `T`. -/
  T : E →L[ℝ] F
  isFredholm : T.IsFredholm
  /-- The good left-projection `P ∈ Π_T`. -/
  P : F →L[ℝ] F
  isGoodLeftProj : IsGoodLeftProj T P
  /-- The complement `Y` of `ker(P T)`. -/
  Y : Submodule ℝ E
  isTopCompl : (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).IsTopCompl Y
  /-- The radius `ε`. -/
  ε : ℝ
  ε_pos : 0 < ε
  isGoodLeftProj_of_lt : ∀ S : E →L[ℝ] F, ‖S - T‖ < ε → IsGoodLeftProj S P
  exists_equiv_of_lt : ∀ S : E →L[ℝ] F, ‖S - T‖ < ε →
    ∃ e : Y ≃L[ℝ] LinearMap.range (P : F →ₗ[ℝ] F),
      (e : Y →L[ℝ] LinearMap.range (P : F →ₗ[ℝ] F)) = projRestrict P S Y

namespace LocalDetChart

variable (c : LocalDetChart E F)

/-- `ker(P T)`. -/
abbrev K : Submodule ℝ E := LinearMap.ker ((c.P ∘L c.T : E →L[ℝ] F) : E →ₗ[ℝ] F)

instance : FiniteDimensional ℝ c.K := (c.isGoodLeftProj.isFredholm_comp c.isFredholm).finite_ker

instance : FiniteDimensional ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) :=
  c.isGoodLeftProj.finite_coker

/-- `e ↦ P S e`, as a map into `R(P)`. -/
def projComp (S : E →L[ℝ] F) : E →L[ℝ] LinearMap.range (c.P : F →ₗ[ℝ] F) :=
  (c.P ∘L S).codRestrict _ (fun x => ⟨S x, rfl⟩)

/-- **`y(·, S) = −(P S|_Y)⁻¹ ∘ P S : E → Y ⊂ E`** (defined for every `S`; it solves
`P S (k + y) = 0` when `‖S − T‖ < ε`). -/
def ySol (S : E →L[ℝ] F) : E →L[ℝ] E :=
  -(c.Y.subtypeL ∘L ContinuousLinearMap.inverse (projRestrict c.P S c.Y) ∘L c.projComp S)

/-- `k ↦ k + y(k, S)`. -/
def kerMap (S : E →L[ℝ] F) : E →L[ℝ] E := ContinuousLinearMap.id ℝ E + c.ySol S

/-- The projection `k + y ↦ k` of `E = ker(P T) ⊕ Y` onto `ker(P T)` along `Y`. -/
def kerProj : E →L[ℝ] c.K := Submodule.projectionOntoL c.K c.Y c.isTopCompl

omit [CompleteSpace F] in
/-- `Y` is complete (it is closed). -/
theorem completeSpace_Y : CompleteSpace c.Y := c.isTopCompl.isClosed'.completeSpace_coe

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem coe_projComp_apply (S : E →L[ℝ] F) (x : E) :
    (c.projComp S x : F) = c.P (S x) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- `S ↦ (e ↦ P S e)` is continuous. -/
theorem continuous_projComp : Continuous c.projComp := by
  refine (LipschitzWith.of_dist_le_mul (K := ‖c.P‖₊) fun S S' => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, coe_nnnorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have h : ((c.projComp S - c.projComp S') x : F) = c.P ((S - S') x) := by
    simp [map_sub]
  calc ‖(c.projComp S - c.projComp S') x‖ = ‖c.P ((S - S') x)‖ := by
        rw [← h]; rfl
    _ ≤ ‖c.P‖ * ‖(S - S') x‖ := c.P.le_opNorm _
    _ ≤ ‖c.P‖ * (‖S - S'‖ * ‖x‖) := by gcongr; exact (S - S').le_opNorm _
    _ = ‖c.P‖ * ‖S - S'‖ * ‖x‖ := by rw [mul_assoc]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `P S|_Y ((P S|_Y)⁻¹ r) = r` for `‖S − T‖ < ε`. -/
theorem projRestrict_inverse_apply (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε)
    (r : LinearMap.range (c.P : F →ₗ[ℝ] F)) :
    projRestrict c.P S c.Y (ContinuousLinearMap.inverse (projRestrict c.P S c.Y) r) = r := by
  obtain ⟨e, he⟩ := c.exists_equiv_of_lt S hS
  rw [← he, ContinuousLinearMap.inverse_equiv]
  exact e.apply_symm_apply r

omit [CompleteSpace E] [CompleteSpace F] in
/-- `(P S|_Y)⁻¹ (P S|_Y y) = y` for `‖S − T‖ < ε`. -/
theorem inverse_projRestrict_apply (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) (y : c.Y) :
    ContinuousLinearMap.inverse (projRestrict c.P S c.Y) (projRestrict c.P S c.Y y) = y := by
  obtain ⟨e, he⟩ := c.exists_equiv_of_lt S hS
  rw [← he, ContinuousLinearMap.inverse_equiv]
  exact e.symm_apply_apply y

omit [CompleteSpace E] [CompleteSpace F] in
/-- `P S ((P S|_Y)⁻¹ r) = r` for `‖S − T‖ < ε`. -/
theorem proj_apply_inverse (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε)
    (r : LinearMap.range (c.P : F →ₗ[ℝ] F)) :
    c.P (S (ContinuousLinearMap.inverse (projRestrict c.P S c.Y) r : E)) = r :=
  congrArg Subtype.val (c.projRestrict_inverse_apply S hS r)

omit [CompleteSpace F] in
/-- `S ↦ (P S|_Y)⁻¹` is continuous at every `S` with `‖S − T‖ < ε` (inversion is continuous at
invertible operators). -/
theorem continuousAt_inverse (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    ContinuousAt (fun S' : E →L[ℝ] F => ContinuousLinearMap.inverse (projRestrict c.P S' c.Y))
      S := by
  have := c.completeSpace_Y
  obtain ⟨e, he⟩ := c.exists_equiv_of_lt S hS
  have h := (contDiffAt_map_inverse (n := 0) e).continuousAt
  rw [he] at h
  exact h.comp (continuous_projRestrict c.P c.Y).continuousAt

omit [CompleteSpace F] in
/-- `S ↦ y(·, S)` is continuous at every `S` with `‖S − T‖ < ε`. -/
theorem continuousAt_ySol (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    ContinuousAt c.ySol S :=
  (continuousAt_const.clm_comp ((c.continuousAt_inverse S hS).clm_comp
    c.continuous_projComp.continuousAt)).neg

omit [CompleteSpace F] in
/-- `S ↦ (k ↦ k + y(k, S))` is continuous at every `S` with `‖S − T‖ < ε`. -/
theorem continuousAt_kerMap (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    ContinuousAt c.kerMap S :=
  continuousAt_const.add (c.continuousAt_ySol S hS)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `y(x, S) ∈ Y`. -/
theorem ySol_mem (S : E →L[ℝ] F) (x : E) : c.ySol S x ∈ c.Y := by
  simp only [ySol, neg_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]
  exact c.Y.neg_mem (Subtype.mem _)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `P S (y(x, S)) = −P S x` for `‖S − T‖ < ε`. -/
theorem proj_apply_ySol (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) (x : E) :
    c.P (S (c.ySol S x)) = -c.P (S x) := by
  simp only [ySol, neg_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, map_neg]
  rw [c.proj_apply_inverse S hS]
  rfl

set_option linter.unusedSectionVars false in
/-- **Lemma 6.5.2 (preprint 6.18)**: `(S, k) ↦ (S, k + y(k, S))` is continuous on `{‖S − T‖ < ε} × E`, maps
`ker(P T)` into `ker(P S)`, and is inverted on `ker(P S)` by the continuous projection
`k + y ↦ k`: so `⋃_{‖S − T‖ < ε} {S} × ker(P S)` is a trivial vector bundle with fibre
`ker(P T)`. -/
theorem lemma_6_5_2 :
    ContinuousOn (fun p : (E →L[ℝ] F) × E => c.kerMap p.1 p.2) {p | ‖p.1 - c.T‖ < c.ε} ∧
      (∀ S : E →L[ℝ] F, ‖S - c.T‖ < c.ε → ∀ k ∈ c.K,
        c.kerMap S k ∈ LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) ∧
      (∀ S : E →L[ℝ] F, ‖S - c.T‖ < c.ε →
        ∀ x ∈ LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F), c.kerMap S (c.kerProj x) = x) ∧
      (∀ S : E →L[ℝ] F, ∀ k : c.K, c.kerProj (c.kerMap S k) = k) := by
  refine ⟨fun p hp => ?_, fun S hS k _ => ?_, fun S hS x hx => ?_, fun S k => ?_⟩
  · exact (ContinuousAt.clm_apply ((c.continuousAt_kerMap p.1 hp).comp continuousAt_fst)
      continuousAt_snd).continuousWithinAt
  · change c.P (S (c.kerMap S k)) = 0
    simp only [kerMap, add_apply, ContinuousLinearMap.id_apply, map_add]
    rw [c.proj_apply_ySol S hS, add_neg_cancel]
  · have hx' : c.P (S x) = 0 := hx
    set k : E := (c.kerProj x : E) with hk_def
    have hk : c.P (c.T k) = 0 := (c.kerProj x).2
    have hy : x - k ∈ c.Y := Submodule.sub_projection_mem c.isTopCompl.isCompl x
    have hPk : c.projComp S k = projRestrict c.P S c.Y (-⟨x - k, hy⟩) := by
      apply Subtype.ext
      simp [map_sub, hx']
    have : c.ySol S k = x - k := by
      simp only [ySol, neg_apply, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply]
      rw [hPk, c.inverse_projRestrict_apply S hS]
      simp
    change k + c.ySol S k = x
    rw [this]
    abel
  · simp only [kerMap, add_apply, ContinuousLinearMap.id_apply, map_add]
    rw [kerProj, Submodule.projectionOntoL_apply_left,
      (Submodule.projectionOntoL_apply_eq_zero_iff _).2 (c.ySol_mem S k), add_zero]

/-- `ker(P T) ≅ ker(P S)`, `k ↦ k + y(k, S)` (Lemma 6.5.2 (preprint 6.18)). -/
def kerEquiv (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    c.K ≃ₗ[ℝ] LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) where
  toFun k := ⟨c.kerMap S k, (c.lemma_6_5_2).2.1 S hS k k.2⟩
  map_add' x y := Subtype.ext ((congrArg (c.kerMap S) (Submodule.coe_add x y)).trans
    (map_add (c.kerMap S) (x : E) (y : E)))
  map_smul' a x := Subtype.ext ((congrArg (c.kerMap S) (Submodule.coe_smul a x)).trans
    (map_smul (c.kerMap S) a (x : E)))
  invFun x := c.kerProj x
  left_inv k := (c.lemma_6_5_2).2.2.2 S k
  right_inv x := Subtype.ext ((c.lemma_6_5_2).2.2.1 S hS x x.2)

@[simp] theorem coe_kerEquiv_apply (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) (k : c.K) :
    (c.kerEquiv S hS k : E) = c.kerMap S k := rfl

/-- The kernel frame `kᵢ(S) = kᵢ + y(kᵢ, S)` of `ker(P S)`, for the basis `Module.finBasis` of
`ker(P T)`. -/
def kerFrame (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    Fin (finrank ℝ c.K) → LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
  c.kerEquiv S hS ∘ Module.finBasis ℝ c.K

/-- The cokernel basis `e₁, …, e_l` of `F / R(P) = F / R(P S)` (`Module.finBasis` of `F / R(P)`,
read in `F / R(P S)`). -/
def cokerFrame (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    Fin (finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))) →
      F ⧸ LinearMap.range ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
  (cokerCompEquiv (c.isGoodLeftProj_of_lt S hS)).symm ∘
    Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))

/-- **The frame of `DET(T, P, ε)`**: `ω(S) = (k₁(S) ∧ … ∧ kₙ(S)) ⊗ (e₁ ∧ … ∧ e_l)* ∈ det(P S)`. -/
def frame (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) : fredholmDet (c.P ∘L S) :=
  wedge (c.kerFrame S hS) (c.kerEquiv S hS).finrank_eq ⊗ₜ
    dualVec (wedge (c.cokerFrame S hS)
      (cokerCompEquiv (c.isGoodLeftProj_of_lt S hS)).symm.finrank_eq)

/-- The kernel frame is linearly independent. -/
theorem kerFrame_linearIndependent (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    LinearIndependent ℝ (c.kerFrame S hS) :=
  (Module.finBasis ℝ c.K).linearIndependent.map' _ (c.kerEquiv S hS).ker

/-- The kernel frame spans `ker(P S)`. -/
theorem span_kerFrame (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    Submodule.span ℝ (Set.range (c.kerFrame S hS)) = ⊤ := by
  have := ((Module.finBasis ℝ c.K).map (c.kerEquiv S hS)).span_eq
  rwa [Basis.coe_map] at this

omit [CompleteSpace E] [CompleteSpace F] in
/-- The cokernel frame is linearly independent. -/
theorem cokerFrame_linearIndependent (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    LinearIndependent ℝ (c.cokerFrame S hS) :=
  (Module.finBasis ℝ _).linearIndependent.map' _
    (cokerCompEquiv (c.isGoodLeftProj_of_lt S hS)).symm.ker

/-- `ker(P S)` is finite-dimensional for `‖S − T‖ < ε`. -/
theorem finiteDimensional_ker (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    FiniteDimensional ℝ (LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
  (c.kerEquiv S hS).finiteDimensional

omit [CompleteSpace E] [CompleteSpace F] in
/-- `F / R(P S)` is finite-dimensional for `‖S − T‖ < ε`. -/
theorem finiteDimensional_coker (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    FiniteDimensional ℝ (F ⧸ LinearMap.range ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
  (cokerCompEquiv (c.isGoodLeftProj_of_lt S hS)).symm.finiteDimensional

/-- The wedge of the kernel frame is not zero. -/
theorem wedge_kerFrame_ne_zero (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    wedge (c.kerFrame S hS) (c.kerEquiv S hS).finrank_eq ≠ 0 := by
  have := c.finiteDimensional_ker S hS
  exact (wedge_ne_zero_iff _).2 (c.kerFrame_linearIndependent S hS)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The wedge of the cokernel frame is not zero. -/
theorem wedge_cokerFrame_ne_zero (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    wedge (c.cokerFrame S hS) (cokerCompEquiv (c.isGoodLeftProj_of_lt S hS)).symm.finrank_eq ≠
      0 := by
  have := c.finiteDimensional_coker S hS
  exact (wedge_ne_zero_iff _).2 (c.cokerFrame_linearIndependent S hS)

/-- The frame is not zero. -/
theorem frame_ne_zero (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) : c.frame S hS ≠ 0 := by
  have := c.finiteDimensional_coker S hS
  exact tmul_ne_zero_of_ne_zero (c.wedge_kerFrame_ne_zero S hS)
    (dualVec_ne_zero finrank_maxPow (c.wedge_cokerFrame_ne_zero S hS))

/-- **Kernel part of the frame comparison**: a family `v` of `dim ker(P S)` vectors of `ker(P S)`
has wedge `det(kerProj ∘ v) · (k₁(S) ∧ … ∧ kₙ(S))`, the determinant taken in the basis
`Module.finBasis` of `ker(P T)`. -/
theorem wedge_eq_det_smul_wedge_kerFrame (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) {k : ℕ}
    (v : Fin k → LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F))
    (hk : k = finrank ℝ (LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    (h1 : finrank ℝ c.K = k) :
    wedge v hk = ((Module.finBasis ℝ c.K).reindex (finCongr h1)).det (fun i => c.kerProj (v i)) •
      wedge (c.kerFrame S hS) (c.kerEquiv S hS).finrank_eq := by
  have e2 : (⇑((c.kerEquiv S hS : c.K →ₗ[ℝ] _)) ∘ fun i => c.kerProj (v i)) = v :=
    funext fun i => Subtype.ext ((c.lemma_6_5_2).2.2.1 S hS _ (v i).2)
  have e3 : (⇑((c.kerEquiv S hS : c.K →ₗ[ℝ] _)) ∘
      ⇑((Module.finBasis ℝ c.K).reindex (finCongr h1))) = c.kerFrame S hS ∘ Fin.cast h1.symm := by
    funext i
    simp only [kerFrame, Function.comp_apply, Basis.reindex_apply, finCongr_symm, finCongr_apply]
    rfl
  calc wedge v hk = wedge (⇑((c.kerEquiv S hS : c.K →ₗ[ℝ] _)) ∘ fun i => c.kerProj (v i)) hk :=
        congrArg (fun w => wedge w hk) e2.symm
    _ = _ • wedge (⇑((c.kerEquiv S hS : c.K →ₗ[ℝ] _)) ∘
          ⇑((Module.finBasis ℝ c.K).reindex (finCongr h1))) hk := wedge_comp_basis _ _ _ hk
    _ = _ := by
        rw [e3]
        exact congrArg _ (wedge_cast (c.kerFrame S hS) (c.kerEquiv S hS).finrank_eq h1.symm)

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Cokernel part of the frame comparison**: for a family `w` of `dim F / R(P S)` vectors of
`F / R(P S)`, `(w₁ ∧ … ∧ w_l)* = det(w)⁻¹ · (e₁ ∧ … ∧ e_l)*`, the determinant taken in the basis
`Module.finBasis` of `F / R(P)` (both sides vanish when `w` is dependent). -/
theorem dualVec_wedge_eq_inv_det_smul (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) {l : ℕ}
    (w : Fin l → F ⧸ LinearMap.range ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F))
    (hl : l = finrank ℝ (F ⧸ LinearMap.range ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    (h2 : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = l) :
    dualVec (wedge w hl) =
      (((Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).reindex (finCongr h2)).det
        (fun i => cokerCompEquiv (c.isGoodLeftProj_of_lt S hS) (w i)))⁻¹ •
      dualVec (wedge (c.cokerFrame S hS)
        (cokerCompEquiv (c.isGoodLeftProj_of_lt S hS)).symm.finrank_eq) := by
  have := c.finiteDimensional_coker S hS
  set Φ := cokerCompEquiv (c.isGoodLeftProj_of_lt S hS) with hΦ
  have e2 : (⇑(Φ.symm : _ →ₗ[ℝ] _) ∘ fun i => Φ (w i)) = w :=
    funext fun i => Φ.symm_apply_apply (w i)
  have e3 : (⇑(Φ.symm : _ →ₗ[ℝ] _) ∘
      ⇑((Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).reindex (finCongr h2))) =
      c.cokerFrame S hS ∘ Fin.cast h2.symm := by
    funext i
    simp only [cokerFrame, Function.comp_apply, Basis.reindex_apply, finCongr_symm,
      finCongr_apply, hΦ]
    rfl
  have hw : wedge w hl =
      ((Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).reindex (finCongr h2)).det
        (fun i => Φ (w i)) • wedge (c.cokerFrame S hS) Φ.symm.finrank_eq := by
    calc wedge w hl = wedge (⇑(Φ.symm : _ →ₗ[ℝ] _) ∘ fun i => Φ (w i)) hl :=
          congrArg (fun w => wedge w hl) e2.symm
      _ = _ • wedge (⇑(Φ.symm : _ →ₗ[ℝ] _) ∘ ⇑((Module.finBasis ℝ
            (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).reindex (finCongr h2))) hl :=
          wedge_comp_basis _ _ _ hl
      _ = _ := by
          rw [e3]
          exact congrArg _ (wedge_cast (c.cokerFrame S hS) Φ.symm.finrank_eq h2.symm)
  rw [hw, dualVec_smul_eq_inv_smul finrank_maxPow (c.wedge_cokerFrame_ne_zero S hS)]

/-- **Frame comparison**: an element `(v₁ ∧ … ∧ vₖ) ⊗ (w₁ ∧ … ∧ w_l)*` of `det(T₀)`, for an operator
`T₀ = P S` (read in `det(P S)`), is `det(kerProj ∘ v) · det(w)⁻¹` times the frame `ω(S)`. -/
theorem linDetEquivOfEq_wedge_tmul (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) {T₀ : E →ₗ[ℝ] F}
    (h : T₀ = ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) {k l : ℕ} (v : Fin k → LinearMap.ker T₀)
    (hk : k = finrank ℝ (LinearMap.ker T₀)) (w : Fin l → F ⧸ LinearMap.range T₀)
    (hl : l = finrank ℝ (F ⧸ LinearMap.range T₀)) (h1 : finrank ℝ c.K = k)
    (h2 : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = l)
    (hR : LinearMap.range T₀ = LinearMap.range (c.P : F →ₗ[ℝ] F)) :
    linDetEquivOfEq h (wedge v hk ⊗ₜ dualVec (wedge w hl)) =
      (((Module.finBasis ℝ c.K).reindex (finCongr h1)).det (fun i => c.kerProj (v i)) *
        (((Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).reindex
          (finCongr h2)).det (fun i => Submodule.quotEquivOfEq _ _ hR (w i)))⁻¹) •
        c.frame S hS := by
  subst h
  rw [linDetEquivOfEq_self, LinearEquiv.refl_apply, c.wedge_eq_det_smul_wedge_kerFrame S hS v hk h1,
    c.dualVec_wedge_eq_inv_det_smul S hS w hl h2, TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul', smul_smul, mul_comm]
  rfl

omit [CompleteSpace F] in
/-- `S ↦ k + y(k, S)` is continuous on the ball, for fixed `k`. -/
theorem continuousOn_kerMap_apply (x : E) :
    ContinuousOn (fun S => c.kerMap S x) {S | ‖S - c.T‖ < c.ε} := fun S hS =>
  ((c.continuousAt_kerMap S hS).clm_apply continuousAt_const).continuousWithinAt

end LocalDetChart

/-- **Proposition 6.5.4 (preprint 6.20)**: the local determinant bundle `DET(T, P, ε)` is a topological line bundle
in a natural way: for two charts with the same projection `P` (any centres and radii), the frames
differ on the common ball by a continuous nowhere-zero factor `g`. -/
theorem proposition_6_5_4 (c c' : LocalDetChart E F) (hP : c'.P = c.P) :
    ∃ g : (E →L[ℝ] F) → ℝ, ContinuousOn g {S | ‖S - c.T‖ < c.ε ∧ ‖S - c'.T‖ < c'.ε} ∧
      ∀ (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) (hS' : ‖S - c'.T‖ < c'.ε), g S ≠ 0 ∧
        linDetEquivOfEq (congrArg (fun A : F →L[ℝ] F => ((A ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) hP)
          (c'.frame S hS') = g S • c.frame S hS := by
  by_cases hne : ∃ S : E →L[ℝ] F, ‖S - c.T‖ < c.ε ∧ ‖S - c'.T‖ < c'.ε
  swap
  · exact ⟨0, fun S hS => absurd ⟨S, hS⟩ hne, fun S hS hS' => absurd ⟨S, hS, hS'⟩ hne⟩
  obtain ⟨S₀, hS₀, hS₀'⟩ := hne
  have h1 : finrank ℝ c.K = finrank ℝ c'.K := by
    have e1 := (c.kerEquiv S₀ hS₀).finrank_eq
    have e2 := (c'.kerEquiv S₀ hS₀').finrank_eq
    rw [hP] at e2
    exact e1.trans e2.symm
  have hR' : LinearMap.range (c'.P : F →ₗ[ℝ] F) = LinearMap.range (c.P : F →ₗ[ℝ] F) := by
    rw [hP]
  have h2 : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) =
      finrank ℝ (F ⧸ LinearMap.range (c'.P : F →ₗ[ℝ] F)) :=
    (Submodule.quotEquivOfEq _ _ hR').finrank_eq.symm
  set u := (Module.finBasis ℝ c.K).reindex (finCongr h1) with hu
  set u2 := (Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).reindex (finCongr h2)
    with hu2
  set C₂ := u2.det (fun i => Submodule.quotEquivOfEq _ _ hR'
    (Module.finBasis ℝ (F ⧸ LinearMap.range (c'.P : F →ₗ[ℝ] F)) i)) with hC₂
  refine ⟨fun S => u.det (fun i => c.kerProj (c'.kerMap S (Module.finBasis ℝ c'.K i))) * C₂⁻¹,
    ?_, fun S hS hS' => ?_⟩
  · refine ContinuousOn.mul ?_ continuousOn_const
    refine (continuous_basis_det u).comp_continuousOn ?_
    refine continuousOn_pi.2 fun i => c.kerProj.continuous.comp_continuousOn ?_
    exact (c'.continuousOn_kerMap_apply _).mono fun S hS => hS.2
  have hR : LinearMap.range ((c'.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) =
      LinearMap.range (c.P : F →ₗ[ℝ] F) :=
    (c'.isGoodLeftProj_of_lt S hS').range_comp.trans hR'
  have hcok : u2.det (fun i => Submodule.quotEquivOfEq _ _ hR (c'.cokerFrame S hS' i)) = C₂ :=
    congrArg u2.det (funext fun i => quotEquivOfEq_apply_symm_apply _ _ _ _)
  have key : linDetEquivOfEq
      (congrArg (fun A : F →L[ℝ] F => ((A ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) hP) (c'.frame S hS') =
      (u.det (fun i => c.kerProj (c'.kerMap S (Module.finBasis ℝ c'.K i))) * C₂⁻¹) •
        c.frame S hS := by
    refine (c.linDetEquivOfEq_wedge_tmul S hS _ (c'.kerFrame S hS') _ (c'.cokerFrame S hS') _
      h1 h2 hR).trans ?_
    rw [← hcok]
    rfl
  refine ⟨fun h0 => ?_, key⟩
  beta_reduce at h0
  rw [h0, zero_smul] at key
  exact c'.frame_ne_zero S hS' ((LinearEquiv.map_eq_zero_iff _).1 key)

namespace LocalDetChart

variable (c c' : LocalDetChart E F)

/-- `R(P) ∩ ker Q`, for the projections `P` of `c` and `Q` of `c'`: for `Q ≤ P` and `S` in the ball
of `c`, `(P S|_Y)⁻¹` maps a basis of it to vectors completing a basis of `ker(P S)` to one of
`ker(Q S)`. -/
abbrev rangeInfKer : Submodule ℝ F :=
  LinearMap.range (c.P : F →ₗ[ℝ] F) ⊓ LinearMap.ker (c'.P : F →ₗ[ℝ] F)

instance : FiniteDimensional ℝ (rangeInfKer c c') := by
  have := c'.isGoodLeftProj.finiteDimensional_ker
  exact Submodule.finiteDimensional_of_le inf_le_right

/-- `z_m(S) = (P S|_Y)⁻¹ f_m ∈ Y` for the basis `f = Module.finBasis` of `R(P) ∩ ker Q`. -/
def zSol (S : E →L[ℝ] F) (m : Fin (finrank ℝ (rangeInfKer c c'))) : E :=
  (ContinuousLinearMap.inverse (projRestrict c.P S c.Y)
    ⟨(Module.finBasis ℝ (rangeInfKer c c') m : F),
      (Module.finBasis ℝ (rangeInfKer c c') m).2.1⟩ : E)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `P S z_m(S) = f_m`. -/
theorem proj_apply_zSol (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε)
    (m : Fin (finrank ℝ (rangeInfKer c c'))) :
    c.P (S (zSol c c' S m)) = (Module.finBasis ℝ (rangeInfKer c c') m : F) :=
  c.proj_apply_inverse S hS _

omit [CompleteSpace E] [CompleteSpace F] in
/-- `z_m(S) ∈ ker(Q P S)`. -/
theorem zSol_mem_ker (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε)
    (m : Fin (finrank ℝ (rangeInfKer c c'))) :
    zSol c c' S m ∈ LinearMap.ker ((c'.P ∘L (c.P ∘L S) : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
  change c'.P (c.P (S (zSol c c' S m))) = 0
  rw [proj_apply_zSol c c' S hS]
  exact (Module.finBasis ℝ (rangeInfKer c c') m).2.2

omit [CompleteSpace F] in
/-- `S ↦ z_m(S)` is continuous on the ball of `c`. -/
theorem continuousOn_zSol (m : Fin (finrank ℝ (rangeInfKer c c'))) :
    ContinuousOn (fun S => zSol c c' S m) {S | ‖S - c.T‖ < c.ε} := fun S hS =>
  (continuous_subtype_val.continuousAt.comp
    ((c.continuousAt_inverse S hS).clm_apply continuousAt_const)).continuousWithinAt

/-- `S ↦ det_u(kerProj'(k₁(S)), …, kerProj'(kₙ(S)), kerProj'(z₁(S)), …)` is continuous on the
ball of `c`, for a basis `u` of `ker(Q T')`. -/
theorem continuousOn_det_append
    (u : Basis (Fin (finrank ℝ c.K + finrank ℝ (rangeInfKer c c'))) ℝ c'.K) :
    ContinuousOn (fun S => u.det (fun i => c'.kerProj (Fin.append
      (fun i => c.kerMap S (Module.finBasis ℝ c.K i)) (zSol c c' S) i)))
      {S | ‖S - c.T‖ < c.ε} := by
  refine (continuous_basis_det u).comp_continuousOn
    (continuousOn_pi.2 fun i => c'.kerProj.continuous.comp_continuousOn ?_)
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact c.continuousOn_kerMap_apply _
  | right m =>
    simp only [Fin.append_right]
    exact continuousOn_zSol c c' m

/-- The vectors `z_m(S)` of `ker(Q P S)`. -/
def bSol (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    Fin (finrank ℝ (rangeInfKer c c')) →
      LinearMap.ker ((c'.P ∘L (c.P ∘L S) : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
  fun m => ⟨zSol c c' S m, zSol_mem_ker c c' S hS m⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- `Φ(z_m(S)) = [P S z_m(S)] = [f_m]` in `F / R(Q)`. -/
theorem projSeqPhi_bSol (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε)
    (m : Fin (finrank ℝ (rangeInfKer c c'))) :
    projSeqPhi (c.P ∘L S) c'.P (bSol c c' S hS m) =
      Submodule.Quotient.mk (Module.finBasis ℝ (rangeInfKer c c') m : F) := by
  change Submodule.Quotient.mk (c.P (S (zSol c c' S m))) = _
  rw [proj_apply_zSol c c' S hS]

/-- The kernel frame of `c` at `S` followed by the `z_m(S)` is linearly independent in
`ker(Q P S)`. -/
theorem linearIndependent_append_bSol (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    LinearIndependent ℝ
      (Fin.append (projSeqJ (c.P ∘L S) c'.P ∘ c.kerFrame S hS) (bSol c c' S hS)) := by
  let L : LinearMap.ker ((c'.P ∘L (c.P ∘L S) : E →L[ℝ] F) : E →ₗ[ℝ] F) →ₗ[ℝ] F :=
    ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) ∘ₗ (LinearMap.ker _).subtype
  have hLa : ∀ i, L ((projSeqJ (c.P ∘L S) c'.P ∘ c.kerFrame S hS) i) = 0 :=
    fun i => (c.kerFrame S hS i).2
  have hLb : ∀ m, L (bSol c c' S hS m) = (Module.finBasis ℝ (rangeInfKer c c') m : F) :=
    fun m => proj_apply_zSol c c' S hS m
  have hfb : LinearIndependent ℝ (fun m => (Module.finBasis ℝ (rangeInfKer c c') m : F)) :=
    (Module.finBasis ℝ (rangeInfKer c c')).linearIndependent.map' (rangeInfKer c c').subtype
      (Submodule.ker_subtype _)
  have hJa : LinearIndependent ℝ (projSeqJ (c.P ∘L S) c'.P ∘ c.kerFrame S hS) :=
    (c.kerFrame_linearIndependent S hS).map' _
      (LinearMap.ker_eq_bot.2 (Submodule.inclusion_injective _))
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_add] at hg
  simp only [Fin.append_left, Fin.append_right] at hg
  have h2 : ∀ m, g (Fin.natAdd (finrank ℝ c.K) m) = 0 := by
    refine Fintype.linearIndependent_iff.1 hfb _ ?_
    have := congrArg L hg
    rw [map_add, map_sum, map_sum, map_zero] at this
    simpa only [map_smul, hLa, hLb, smul_zero, Finset.sum_const_zero, zero_add] using this
  have h1 : ∀ i, g (Fin.castAdd (finrank ℝ (rangeInfKer c c')) i) = 0 := by
    refine Fintype.linearIndependent_iff.1 hJa _ ?_
    simpa only [h2, zero_smul, Finset.sum_const_zero, add_zero] using hg
  intro i
  induction i using Fin.addCases with
  | left i => exact h1 i
  | right m => exact h2 m

/-- The kernel frame of `c` at `S` followed by the `z_m(S)` spans `ker(Q P S)`. -/
theorem span_append_bSol (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    ⊤ ≤ Submodule.span ℝ
      (Set.range (Fin.append (projSeqJ (c.P ∘L S) c'.P ∘ c.kerFrame S hS) (bSol c c' S hS))) := by
  rintro x -
  rw [span_range_append]
  have hxW : c.P (S x) ∈ rangeInfKer c c' := ⟨⟨S x, rfl⟩, x.2⟩
  have hsum : (∑ m, (Module.finBasis ℝ (rangeInfKer c c')).repr ⟨c.P (S x), hxW⟩ m •
      (Module.finBasis ℝ (rangeInfKer c c') m : F)) = c.P (S x) := by
    have h := congrArg Subtype.val
      ((Module.finBasis ℝ (rangeInfKer c c')).sum_repr ⟨c.P (S x), hxW⟩)
    rw [Submodule.coe_sum] at h
    exact h
  have hb : ∀ m, c.P (S (bSol c c' S hS m : E)) = (Module.finBasis ℝ (rangeInfKer c c') m : F) :=
    fun m => proj_apply_zSol c c' S hS m
  have hy : c.P (S ((x - ∑ m, (Module.finBasis ℝ (rangeInfKer c c')).repr ⟨c.P (S x), hxW⟩ m •
      bSol c c' S hS m : LinearMap.ker ((c'.P ∘L (c.P ∘L S) : E →L[ℝ] F) : E →ₗ[ℝ] F)) : E)) =
      0 := by
    rw [Submodule.coe_sub, Submodule.coe_sum, map_sub, map_sub, map_sum, map_sum]
    simp only [Submodule.coe_smul, map_smul, hb]
    rw [hsum, sub_self]
  rw [← sub_add_cancel x (∑ m, (Module.finBasis ℝ (rangeInfKer c c')).repr ⟨c.P (S x), hxW⟩ m •
      bSol c c' S hS m)]
  refine Submodule.add_mem_sup ?_ (Submodule.sum_mem _ fun m _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))
  rw [show x - ∑ m, (Module.finBasis ℝ (rangeInfKer c c')).repr ⟨c.P (S x), hxW⟩ m •
      bSol c c' S hS m = projSeqJ (c.P ∘L S) c'.P ⟨_, hy⟩ from rfl, Set.range_comp,
    Submodule.span_image, c.span_kerFrame S hS]
  exact Submodule.mem_map_of_mem Submodule.mem_top

/-- `dim ker(Q P S) = dim ker(P T) + dim(R(P) ∩ ker Q)`. -/
theorem finrank_ker_comp_comp (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    finrank ℝ c.K + finrank ℝ (rangeInfKer c c') =
      finrank ℝ (LinearMap.ker ((c'.P ∘L (c.P ∘L S) : E →L[ℝ] F) : E →ₗ[ℝ] F)) := by
  have b := Basis.mk (linearIndependent_append_bSol c c' S hS) (span_append_bSol c c' S hS)
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

/-- `dim F / R(Q P S) = dim F / R(P) + dim(R(P) ∩ ker Q)` (from the exact sequence
`0 → ker(P S) → ker(Q P S) → F / R(Q) → F / R(P S) → 0`). -/
theorem finrank_coker_comp_comp (hQP : ProjLE c'.P c.P) (S : E →L[ℝ] F) (hSF : S.IsFredholm)
    (hS : ‖S - c.T‖ < c.ε) (hS' : ‖S - c'.T‖ < c'.ε) :
    finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) + finrank ℝ (rangeInfKer c c') =
      finrank ℝ (F ⧸ LinearMap.range ((c'.P ∘L (c.P ∘L S) : E →L[ℝ] F) : E →ₗ[ℝ] F)) := by
  have hT := (c.isGoodLeftProj_of_lt S hS).isFredholm_comp hSF
  have hQ := (c'.isGoodLeftProj_of_lt S hS').of_projLE hQP
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    hT.finite_coker
  have := hQ.finite_coker
  have := (hQ.isFredholm_comp hT).finite_ker
  exact ((projSeq hQ).finrank_eq_of_families (c.kerEquiv S hS).finrank_eq
    (cokerCompEquiv (c.isGoodLeftProj_of_lt S hS)).symm.finrank_eq
    (finrank_ker_comp_comp c c' S hS)).trans (cokerCompEquiv hQ).finrank_eq.symm

/-- A lift `d_i ∈ F` of the basis vector `Module.finBasis (F / R(P)) i`. -/
def cokerLift (i : Fin (finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)))) : F :=
  Function.surjInv (Submodule.Quotient.mk_surjective _)
    (Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) i)

/-- `π([d_i]_Q) = e_i` in `F / R(P S)`: the classes `[d_i] ∈ F / R(Q)` lift the cokernel frame of
`c` through `π : F / R(Q) → F / R(P S)` (for `Q ≤ P`). -/
theorem projSeqPi_cokerLift (hQP : ProjLE c'.P c.P) (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε)
    (hQ : c'.P ∘L c'.P = c'.P) (i : Fin (finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)))) :
    projSeqPi (T := c.P ∘L S) hQ (Submodule.Quotient.mk (cokerLift c i)) = c.cokerFrame S hS i := by
  have hdli : (Submodule.Quotient.mk (cokerLift c i) : F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) =
      Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) i :=
    Function.surjInv_eq _ _
  rw [projSeqPi_mk]
  change _ = (cokerCompEquiv (c.isGoodLeftProj_of_lt S hS)).symm
    (Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) i)
  rw [← hdli, LinearEquiv.eq_symm_apply, cokerCompEquiv, Submodule.quotEquivOfEq_mk,
    Submodule.Quotient.eq, sub_sub_cancel_left]
  have hQd : c'.P (cokerLift c i) = c.P (c'.P (cokerLift c i)) :=
    DFunLike.congr_fun hQP.2 (cokerLift c i)
  rw [hQd]
  exact Submodule.neg_mem _ ⟨_, rfl⟩

/-- **`γ^Q_{PS}` on the frame** (formula (91) for `E(P S, Q)` with the kernel vectors `kᵢ(S)`,
`z_m(S)` and the cokernel vectors `[d_i]`, `[f_m]`), read in the frame of `c'`. -/
theorem gammaProj_frame_eq (hQP : ProjLE c'.P c.P)
    (hdim : finrank ℝ c'.K = finrank ℝ c.K + finrank ℝ (rangeInfKer c c'))
    (hdim2 : finrank ℝ (F ⧸ LinearMap.range (c'.P : F →ₗ[ℝ] F)) =
      finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) + finrank ℝ (rangeInfKer c c'))
    (S : E →L[ℝ] F) (hSF : S.IsFredholm) (hS : ‖S - c.T‖ < c.ε) (hS' : ‖S - c'.T‖ < c'.ε) :
    linDetEquivOfEq (congrArg (fun A : E →L[ℝ] F => (A : E →ₗ[ℝ] F))
        (comp_comp_eq_of_projLE (T := S) hQP))
      (gammaProj ((c.isGoodLeftProj_of_lt S hS).isFredholm_comp hSF)
        ((c'.isGoodLeftProj_of_lt S hS').of_projLE hQP) (c.frame S hS)) =
    (((Module.finBasis ℝ c'.K).reindex (finCongr hdim)).det (fun i => c'.kerProj (Fin.append
        (fun i => c.kerMap S (Module.finBasis ℝ c.K i)) (zSol c c' S) i)) *
      (((Module.finBasis ℝ (F ⧸ LinearMap.range (c'.P : F →ₗ[ℝ] F))).reindex
        (finCongr hdim2)).det (Fin.append (fun i => Submodule.Quotient.mk (cokerLift c i))
          (fun m => Submodule.Quotient.mk (Module.finBasis ℝ (rangeInfKer c c') m : F))))⁻¹) •
      c'.frame S hS' := by
  have hT := (c.isGoodLeftProj_of_lt S hS).isFredholm_comp hSF
  have hQ := (c'.isGoodLeftProj_of_lt S hS').of_projLE hQP
  have e1 := gammaProj_wedge_tmul hT hQ (c.kerFrame_linearIndependent S hS)
    (c.kerEquiv S hS).finrank_eq (c.cokerFrame_linearIndependent S hS)
    (cokerCompEquiv (c.isGoodLeftProj_of_lt S hS)).symm.finrank_eq
    (linearIndependent_append_bSol c c' S hS) (finrank_ker_comp_comp c c' S hS)
    (projSeqPi_cokerLift c c' hQP S hS hQ.isProj)
    (finrank_coker_comp_comp c c' hQP S hSF hS hS')
  have hTQ := congrArg (fun A : E →L[ℝ] F => (A : E →ₗ[ℝ] F))
    (comp_comp_eq_of_projLE (T := S) hQP)
  have e2 := c'.linDetEquivOfEq_wedge_tmul S hS' hTQ
    (Fin.append (projSeqJ (c.P ∘L S) c'.P ∘ c.kerFrame S hS) (bSol c c' S hS))
    (finrank_ker_comp_comp c c' S hS)
    ((cokerCompEquiv hQ).symm ∘ Fin.append (fun i => Submodule.Quotient.mk (cokerLift c i))
      (projSeqPhi (c.P ∘L S) c'.P ∘ bSol c c' S hS))
    (finrank_coker_comp_comp c c' hQP S hSF hS hS') hdim hdim2 hQ.range_comp
  have hker : ∀ i, ((Fin.append (projSeqJ (c.P ∘L S) c'.P ∘ c.kerFrame S hS)
      (bSol c c' S hS) i : _) : E) =
      Fin.append (fun i => c.kerMap S (Module.finBasis ℝ c.K i)) (zSol c c' S) i := by
    intro i
    induction i using Fin.addCases with
    | left i => simp only [Fin.append_left]; rfl
    | right m => simp only [Fin.append_right]; rfl
  have hcok : ∀ i, (cokerCompEquiv hQ) (((cokerCompEquiv hQ).symm ∘
      Fin.append (fun i => Submodule.Quotient.mk (cokerLift c i))
        (projSeqPhi (c.P ∘L S) c'.P ∘ bSol c c' S hS)) i) =
      Fin.append (fun i => Submodule.Quotient.mk (cokerLift c i))
        (fun m => Submodule.Quotient.mk (Module.finBasis ℝ (rangeInfKer c c') m : F)) i := by
    intro i
    refine ((cokerCompEquiv hQ).apply_symm_apply _).trans ?_
    induction i using Fin.addCases with
    | left i => simp only [Fin.append_left]
    | right m =>
      simp only [Fin.append_right, Function.comp_apply]
      exact projSeqPhi_bSol c c' S hS m
  refine ((congrArg (linDetEquivOfEq hTQ) e1).trans e2).trans ?_
  exact congrArg (fun a : ℝ => a • c'.frame S hS')
    (congrArg₂ (fun a b : ℝ => a * b⁻¹)
      (congrArg ((Module.finBasis ℝ c'.K).reindex (finCongr hdim)).det
        (funext fun i => congrArg c'.kerProj (hker i)))
      (congrArg ((Module.finBasis ℝ (F ⧸ LinearMap.range (c'.P : F →ₗ[ℝ] F))).reindex
        (finCongr hdim2)).det (funext hcok)))

end LocalDetChart

/-- **Lemma 6.5.5 (preprint 6.21)**: for charts `c` (projection `P`) and `c'` (projection `Q ≤ P`), the isomorphism
`γ^Q_{PS} : det(P S) → det(Q P S) = det(Q S)` maps the frame of `c` to a continuous nowhere-zero
multiple `g(S)` of the frame of `c'`, for Fredholm `S` in both balls; so
`(S, h) ↦ (S, γ^Q_{PS}(h))` is an isomorphism of topological line bundles. -/
theorem lemma_6_5_5 (c c' : LocalDetChart E F) (hQP : ProjLE c'.P c.P) :
    ∃ g : (E →L[ℝ] F) → ℝ,
      ContinuousOn g {S | S.IsFredholm ∧ ‖S - c.T‖ < c.ε ∧ ‖S - c'.T‖ < c'.ε} ∧
      ∀ (S : E →L[ℝ] F) (hSF : S.IsFredholm) (hS : ‖S - c.T‖ < c.ε) (hS' : ‖S - c'.T‖ < c'.ε),
        g S ≠ 0 ∧
          linDetEquivOfEq (congrArg (fun A : E →L[ℝ] F => (A : E →ₗ[ℝ] F))
              (comp_comp_eq_of_projLE (T := S) hQP))
            (gammaProj ((c.isGoodLeftProj_of_lt S hS).isFredholm_comp hSF)
              ((c'.isGoodLeftProj_of_lt S hS').of_projLE hQP) (c.frame S hS)) =
          g S • c'.frame S hS' := by
  by_cases hne : ∃ S : E →L[ℝ] F, S.IsFredholm ∧ ‖S - c.T‖ < c.ε ∧ ‖S - c'.T‖ < c'.ε
  swap
  · exact ⟨0, fun S hS => absurd ⟨S, hS⟩ hne, fun S hSF hS hS' => absurd ⟨S, hSF, hS, hS'⟩ hne⟩
  obtain ⟨S₀, hS₀F, hS₀, hS₀'⟩ := hne
  have hdim : finrank ℝ c'.K = finrank ℝ c.K + finrank ℝ (LocalDetChart.rangeInfKer c c') := by
    refine (c'.kerEquiv S₀ hS₀').finrank_eq.trans ?_
    rw [LocalDetChart.finrank_ker_comp_comp c c' S₀ hS₀, comp_comp_eq_of_projLE hQP]
  have hdim2 : finrank ℝ (F ⧸ LinearMap.range (c'.P : F →ₗ[ℝ] F)) =
      finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) +
        finrank ℝ (LocalDetChart.rangeInfKer c c') :=
    ((cokerCompEquiv ((c'.isGoodLeftProj_of_lt S₀ hS₀').of_projLE hQP)).finrank_eq.symm.trans
      (LocalDetChart.finrank_coker_comp_comp c c' hQP S₀ hS₀F hS₀ hS₀').symm)
  refine ⟨fun S => ((Module.finBasis ℝ c'.K).reindex (finCongr hdim)).det
      (fun i => c'.kerProj (Fin.append (fun i => c.kerMap S (Module.finBasis ℝ c.K i))
        (LocalDetChart.zSol c c' S) i)) *
      (((Module.finBasis ℝ (F ⧸ LinearMap.range (c'.P : F →ₗ[ℝ] F))).reindex
        (finCongr hdim2)).det (Fin.append
          (fun i => Submodule.Quotient.mk (LocalDetChart.cokerLift c i))
          (fun m => Submodule.Quotient.mk
            (Module.finBasis ℝ (LocalDetChart.rangeInfKer c c') m : F))))⁻¹,
    ((LocalDetChart.continuousOn_det_append c c' _).mono fun S hS => hS.2.1).mul
      continuousOn_const, fun S hSF hS hS' => ?_⟩
  have key := LocalDetChart.gammaProj_frame_eq c c' hQP hdim hdim2 S hSF hS hS'
  refine ⟨fun h0 => ?_, key⟩
  beta_reduce at h0
  rw [h0, zero_smul] at key
  exact c.frame_ne_zero S hS ((LinearEquiv.map_eq_zero_iff _).1
    ((LinearEquiv.map_eq_zero_iff _).1 key))

end Polyfold
