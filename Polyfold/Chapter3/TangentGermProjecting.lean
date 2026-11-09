import Polyfold.Chapter3.SolutionGermRecentre
import Polyfold.Chapter3.GoodComplementProjection
import Polyfold.Chapter3.QuadrantInverse
import Polyfold.Chapter3.GoodComplementClosed

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2014 preprint), §3.2:
**Theorem 3.2.3** (p. 106; preprint: Theorem 3.27) **under the tangent germ property alone**, i.e.
without the regularity conditions `TangentGermChart.IsRegular` added in `TangentGerm.lean`
(comparison rows V3.24, V3.72, V3.74; top-ten item #10).  Numbers and pages are the 2021 text's,
the preprint ones in parentheses.

# Re-graphing over a projecting good complement

## The text, paraphrased

(Theorem 3.2.3, p. 106) If `X` is a tame M-polyfold and `M ⊆ X` has the `n`-dimensional tangent
germ property (Definition 3.2.1), then (1) `M` is a sub-M-polyfold of `X` whose induced structure
is tame and sc-smoothly equivalent to a manifold with boundary with corners, and (2) `y ↦ π ∘ ϕ(y)`
is a smooth chart of `M` around `x`.  (Proof, p. 106–108) The set `Σ = {v + y ∈ C | v ∈ V, y ∈ Y}`
is relatively open in `C` and `t(v + w) = v + δ(v)` is an sc-smooth retraction onto `ϕ(M ∩ U)`;
`δ` is an sc^∞-germ near every `v₀ ∈ V` by re-centring.

## What is formalized

`TangentGerm.lean` proves Theorem 3.2.3 under two added conditions (`IsRegular`): (a) `δ` is
sc-smooth on `V` in the set sense, and (b) the projection `π` along `Y` maps `O` into `C`.
`SolutionGermRecentre.lean` removes (a) given (b) (`exists_isRegular_of_locally`, row V3.74).
This file removes (b):

* `Polyfold.interior_quadCone`: the interior of the cone `{ℓ_i ≥ 0} ⊆ N` is `{ℓ_i > 0}` over the
  coordinates not vanishing on `N`.
* `Polyfold.IsGoodComplement.coordFun_eq_zero`: Lemma 3.8.8 (preprint Lemma 3.65) for a
  presentation of `C`: the coordinates in `Σ` vanish on a good complement.
* `MPolyfold.TangentGermChart.ProjData`, `exists_projData`: a continuous projection `π' : E → N`
  with `π'(C) ⊆ N ∩ C` whose kernel `Y'` is a (closed) good complement
  (`exists_proj_goodComplement`, Finding 83).
* `MPolyfold.TangentGermChart.regraphMap`: **the re-graphing map** `g(v) = π'(v + δ(v))`,
  `V → N ∩ C`, with `g(0) = 0`, `Dg(0) = 1` (`hasFDerivWithinAt_regraphMap_zero`), preserving
  the coordinates `ℓ_i`, `i ∈ Σ` (`coordFun_regraphMap`), hence the interior of `N ∩ C`
  (`regraphMap_interior_iff`).  `exists_invData_ball`: on small balls `g` satisfies the
  hypotheses `InvData` of the quadrant inverse function theorem (Proposition 3.8.14 = preprint
  Proposition 3.73, `QuadrantInverse.lean`), for every finite order `k` on a `k`-dependent ball.
* `MPolyfold.TangentGermChart.regraph`: **the re-graphed datum**: same chart, `N`, the complement
  `Y' = ker π'`, `V' = g(V)` and `δ' = (1 − π') ∘ (1 + δ) ∘ g⁻¹`, which describes the same set
  (`ϕ(M ∩ U) = {w + δ'(w) | w ∈ V'}`); `π_eq_of_ker`: its projection is `π'`.
* `MPolyfold.TangentGermChart.exists_projecting` (**the key lemma**): every datum of Definition
  3.2.1 (b) at `x` can be replaced by one, on a smaller chart domain, whose projection maps `O`
  into `C` — condition (b) of `IsRegular`.
* `MPolyfold.TangentGermChart.exists_isRegular`: `exists_isRegular_of_locally` without its
  hypothesis `hπ` (row V3.74); `MPolyfold.HasTangentGermProperty.exists_isRegular`: under the
  tangent germ property, every point has regular data.
* `Polyfold.theorem_3_2_3` (**Theorem 3.2.3 as stated**, rows V3.24 and V3.72: the
  hypothesis `IsRegular` of `theorem_3_2_3_of_isRegular` is removed), `theorem_3_2_3_loc` (with the
  dimension depending on the point, `theorem_3_2_3_loc_of_isRegular`), and `theorem_3_2_3_2021def` (with the
  data of Definition 3.2.1 as written, `HasTangentGermProperty2021`).

## What the text leaves implicit, and the choices made

* **Condition (b) is a choice of the good complement** (Finding 130).  For an arbitrary datum the
  set `ϕ(M ∩ U)` has to be re-written as a graph over `N` along a projecting complement `Y'`.  The
  new graph map is `g⁻¹`, where `g = π' ∘ (1 + δ)`; `g` is a local diffeomorphism of `N ∩ C` at
  `0` by the quadrant inverse function theorem, whose hypothesis "`d_C(x) = d_C(g(x))`" is used
  only as "`x` interior ⟺ `g(x)` interior" (`InvData.interior_iff`), which holds because `g`
  preserves the coordinates `ℓ_i`, `i ∈ Σ` (they vanish on `Y` and on `Y'`, Lemma 3.8.8), and
  `g(x) = 0 ⟺ x = 0` on the ball (bi-Lipschitz).
* **`k`-dependent neighbourhoods.**  `δ` is `C^k` into `E_m` only near `0`, on a neighbourhood
  depending on `(m, k)` (the reading `IsScInftyGermAt` of "sc^∞-germ"); accordingly `g⁻¹` is
  obtained as a `C^k` map on `g(U_k)` for a `k`-dependent ball `U_k`, and `δ'` is an sc^∞-germ in
  the same reading.  The inverse is the same map (`InvData.inv`) on all these balls.
* **The chart domain is shrunk** to `{y ∈ U | π ∘ ϕ(y) ∈ B(0, r)}`, so that `ϕ(M ∩ U') = Γ(B ∩ N ∩ C)`
  with a convex `B ∩ N ∩ C` (the quadrant inverse function theorem needs a convex domain).
* Condition (a) is then obtained from (b) by `exists_isRegular_of_locally` (row V3.74), whose
  hypothesis that every nearby point of `M` has a datum is the tangent germ property itself.
-/

open Set Filter Topology Function Module
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### `C^k` on level `0` from the `k`-dependent germ property -/

section FinGerm

variable {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] {E : ScBanach}

/-- The `C^k`-part of the germ property on level `0`: `δ` is `C^k` into `E₀` near `0` in `D`
(`IsScInftyGermAt.contDiffOn_one` for every `k`). -/
theorem IsScInftyGermAt.contDiffOn_level_zero {D : Set N} {δ : N → E 0} (h : IsScInftyGermAt D δ)
    (k : ℕ) : ∃ V : Set N, (∃ O : Set N, IsOpen O ∧ V = O ∩ D) ∧ (0 : N) ∈ V ∧
      ContDiffOn ℝ k δ V := by
  obtain ⟨V, hV, h0, -, hc⟩ := h 0 k
  refine ⟨V, hV, h0, hc.congr fun v _ => ?_⟩
  change δ v = Function.invFun (E.toBase 0) (δ ((ScBanach.const N).toBase 0 v))
  rw [ScBanach.const_toBase]
  exact (Function.leftInverse_invFun (E.toBase_injective 0) (δ v)).symm

end FinGerm

/-! ### The interior of the cone `{ℓ_i ≥ 0}` in `N` -/

section Interior

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ} (ℓ : Fin n → V →ₗ[ℝ] ℝ)
  (N : Submodule ℝ V) [FiniteDimensional ℝ N]

omit [FiniteDimensional ℝ N] in
/-- A nonzero functional on `N` is onto `ℝ`. -/
lemma restrFun_surjective {i : Fin n} (hi : restrFun ℓ N i ≠ 0) :
    Surjective (restrFun ℓ N i) := by
  obtain ⟨a, ha⟩ : ∃ a, restrFun ℓ N i a ≠ 0 := by
    by_contra h
    exact hi (LinearMap.ext fun a => Classical.not_not.1 fun h' => h ⟨a, h'⟩)
  intro c
  refine ⟨(c / restrFun ℓ N i a) • a, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ ha]

/-- **The interior of the cone `N ∩ C = {x ∈ N | ℓ_i(x) ≥ 0 ∀ i}` in `N`**: the points with
`ℓ_i(x) > 0` for every coordinate `ℓ_i` not vanishing identically on `N`. -/
theorem interior_quadCone :
    interior (quadCone ℓ N) = {x : N | ∀ i, restrFun ℓ N i ≠ 0 → 0 < ℓ i (x : V)} := by
  have h1 : quadCone ℓ N = ⋂ i, {x : N | 0 ≤ restrFun ℓ N i x} := by ext x; simp [quadCone]
  rw [h1, interior_iInter_of_finite]
  ext x
  simp only [mem_iInter, mem_ofPred_eq]
  refine forall_congr' fun i => ?_
  by_cases hi : restrFun ℓ N i = 0
  · simp [hi]
  · have : CompleteSpace N := FiniteDimensional.complete ℝ N
    set L : N →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (restrFun ℓ N i) with hL
    have hLapp : ∀ y : N, L y = ℓ i (y : V) := fun y => rfl
    have hs : {x : N | 0 ≤ restrFun ℓ N i x} = L ⁻¹' Ici 0 := rfl
    rw [hs, L.interior_preimage (restrFun_surjective ℓ N hi), interior_Ici]
    simp [hi, hLapp]

end Interior

/-! ### Coordinates of a presentation and good complements (Lemma 3.8.8) -/

section Coord

variable {E : ScBanach} {q : ℕ} {W : ScBanach}

/-- Membership in `C = T⁻¹([0,∞)^q ⊕ W)` in the coordinates `ℓ_i = (T·)_i`. -/
lemma mem_iff_coordFun (T : ScIso E ((ScBanach.const (Fin q → ℝ)).prod W)) {C : Set (E 0)}
    (hT : C = T 0 ⁻¹' quadrant q W 0) (z : E 0) : z ∈ C ↔ ∀ i, 0 ≤ coordFun (T 0) i z := by
  rw [hT]; exact Iff.rfl

/-- **2021 Lemma 3.8.8, p. 150** (preprint: Lemma 3.65, `lemma_3_8_8`), for a presentation `T` of
the partial quadrant `C`: the coordinates `ℓ_i`, `i ∈ Σ` (those vanishing at some nonzero point of
`N ∩ C`), vanish on every good complement `Y` of `N`. -/
lemma IsGoodComplement.coordFun_eq_zero (T : ScIso E ((ScBanach.const (Fin q → ℝ)).prod W))
    {C : Set (E 0)} (hT : C = T 0 ⁻¹' quadrant q W 0) {N Y : Submodule ℝ (E 0)}
    (hY : IsGoodComplement E C N Y) {p : E 0} (hp : p ∈ Y) {i : Fin q}
    (hi : i ∈ vanIdx (coordFun (T 0)) N) : coordFun (T 0) i p = 0 := by
  obtain ⟨ε, hε, hgood⟩ := hY.exists_eps
  exact lemma_3_8_8 (coordFun (T 0)) N Y hε (fun x hx p hp hle =>
    (mem_iff_coordFun T hT x).symm.trans ((hgood x hx p hp hle).trans (mem_iff_coordFun T hT _)))
    hp hi

end Coord

/-! ### A bi-Lipschitz estimate -/

section Lipschitz

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Lemma 3.8.15 (preprint Lemma 3.74), (70), as an injectivity statement: a map on a convex set
whose derivative stays within `1/2` of the identity is injective. -/
theorem injOn_of_deriv_bound {g : V → V} {U : Set V} (hconv : Convex ℝ U)
    (hdiff : ∀ v ∈ U, HasFDerivWithinAt g (fderivWithin ℝ g U v) U v)
    (hbound : ∀ v ∈ U, ‖fderivWithin ℝ g U v - 1‖ ≤ 1 / 2) : InjOn g U := by
  intro a ha b hb hab
  have h1 : ‖(g b - b) - (g a - a)‖ ≤ 1 / 2 * ‖b - a‖ :=
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun z => g z - z)
      (f' := fun z => fderivWithin ℝ g U z - 1)
      (fun z hz => (hdiff z hz).sub (hasFDerivWithinAt_id z U)) hbound hconv ha hb
  rw [hab, sub_sub_sub_cancel_left, norm_sub_rev b a] at h1
  have : ‖a - b‖ ≤ 0 := by linarith
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end Lipschitz

/-! ### Re-graphing a datum of Definition 3.2.1 (b) over a projecting complement -/

namespace MPolyfold.TangentGermChart

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} {x : X} {n : ℕ} (D : P.TangentGermChart M x n)

/-- The partial quadrant `K = N ∩ C` of `N` (Proposition 3.1.25). -/
abbrev cone : Set D.N := Subtype.val ⁻¹' D.φ.model.C

lemma zero_mem_cone : (0 : D.N) ∈ D.cone := D.V_subset D.zero_mem_V

/-- `N ∩ C` has unique differentiability (convex with nonempty interior). -/
theorem uniqueDiffOn_cone : UniqueDiffOn ℝ D.cone :=
  uniqueDiffOn_convex D.isPartialQuadrant.convex D.goodPosition.interior_nonempty

/-- **The data of a projecting complement**: a continuous projection `π' : E → N` (`π' = 1` on
`N`) with `π'(C) ⊆ C` whose kernel is a good complement of `N` (`exists_proj_goodComplement`,
Finding 83). -/
structure ProjData (π' : D.φ.model.E 0 →L[ℝ] D.N) : Prop where
  apply_coe : ∀ v : D.N, π' v = v
  mapsTo : ∀ z ∈ D.φ.model.C, (π' z : D.φ.model.E 0) ∈ D.φ.model.C
  goodComplement :
    IsGoodComplement D.φ.model.E D.φ.model.C D.N (LinearMap.ker (π' : D.φ.model.E 0 →ₗ[ℝ] D.N))

/-- A projecting complement exists (`exists_proj_goodComplement`). -/
theorem exists_projData : ∃ π' : D.φ.model.E 0 →L[ℝ] D.N, D.ProjData π' := by
  obtain ⟨π', h1, h2, h3⟩ :=
    exists_proj_goodComplement D.φ.model.isPartialQuadrant D.goodPosition
  exact ⟨π', h1, h2, h3⟩

/-- **The re-graphing map** `g(v) = π'(v + δ(v))`. -/
def regraphMap (π' : D.φ.model.E 0 →L[ℝ] D.N) : D.N → D.N :=
  fun v => π' ((v : D.φ.model.E 0) + D.δ v)

variable {D}

section Regraph

variable {π' : D.φ.model.E 0 →L[ℝ] D.N}

lemma regraphMap_apply (v : D.N) : D.regraphMap π' v = π' (D.Γ v) := rfl

lemma regraphMap_zero : D.regraphMap π' 0 = 0 := by
  simp [regraphMap, D.δ_zero]

lemma regraphMap_mem_cone (hπ : D.ProjData π') {v : D.N} (hv : v ∈ D.V) :
    D.regraphMap π' v ∈ D.cone :=
  hπ.mapsTo _ (D.φ.model.O_subset_C (D.Γ_mem_O hv))

lemma sub_coe_mem_ker (hπ : D.ProjData π') (z : D.φ.model.E 0) :
    z - (π' z : D.φ.model.E 0) ∈ LinearMap.ker (π' : D.φ.model.E 0 →ₗ[ℝ] D.N) := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hπ.apply_coe, sub_self]

lemma contDiffOn_regraphMap {k : ℕ} {S : Set D.N} (hδ : ContDiffOn ℝ k D.δ S) :
    ContDiffOn ℝ k (D.regraphMap π') S :=
  π'.contDiff.comp_contDiffOn (D.N.subtypeL.contDiff.contDiffOn.add hδ)

variable {q : ℕ} {W : ScBanach}

/-- **`g` preserves the coordinates in `Σ`**: `ℓ_i ∘ g = ℓ_i` on `N` for `i ∈ Σ`, since `ℓ_i`
vanishes on `Y` (where `δ` takes values) and on `Y' = ker π'` (Lemma 3.8.8). -/
lemma coordFun_regraphMap (hπ : D.ProjData π')
    (T : ScIso D.φ.model.E ((ScBanach.const (Fin q → ℝ)).prod W))
    (hT : D.φ.model.C = T 0 ⁻¹' quadrant q W 0) (v : D.N) {i : Fin q}
    (hi : i ∈ vanIdx (coordFun (T 0)) D.N) :
    coordFun (T 0) i (D.regraphMap π' v : D.φ.model.E 0) =
      coordFun (T 0) i (v : D.φ.model.E 0) := by
  have h1 := hπ.goodComplement.coordFun_eq_zero T hT (sub_coe_mem_ker hπ (D.Γ v)) hi
  have h2 := D.goodComplement.coordFun_eq_zero T hT (D.δ_mem_Y v) hi
  rw [map_sub, sub_eq_zero] at h1
  rw [regraphMap_apply, ← h1, Γ_apply, map_add, h2, add_zero]

/-- **`g` preserves the interior of `N ∩ C`** on a set `U ∋ 0` on which it is injective: the
coordinates in `Σ` are preserved, and for `i ∉ Σ` positivity of `ℓ_i` on the cone is "`≠ 0`"
(`pos_of_not_mem_vanIdx`), which `g` preserves (`g(0) = 0`, injectivity). -/
theorem regraphMap_interior_iff (hπ : D.ProjData π') {U : Set D.N} (hU : U ⊆ D.cone)
    (hUV : U ⊆ D.V) (h0U : (0 : D.N) ∈ U) (hinj : InjOn (D.regraphMap π') U) {v : D.N}
    (hv : v ∈ U) : v ∈ interior D.cone ↔ D.regraphMap π' v ∈ interior D.cone := by
  obtain ⟨q, W, T, hT⟩ := D.φ.model.isPartialQuadrant
  have hK : D.cone = quadCone (coordFun (T 0)) D.N := by
    ext w; exact mem_iff_coordFun T hT (w : D.φ.model.E 0)
  have hvK : v ∈ quadCone (coordFun (T 0)) D.N := by rw [← hK]; exact hU hv
  have hgK : D.regraphMap π' v ∈ quadCone (coordFun (T 0)) D.N := by
    rw [← hK]; exact regraphMap_mem_cone hπ (hUV hv)
  have hne : v ≠ 0 ↔ D.regraphMap π' v ≠ 0 := by
    constructor
    · intro h h'; exact h (hinj hv h0U (h'.trans regraphMap_zero.symm))
    · intro h h'; exact h (by rw [h', regraphMap_zero])
  rw [hK, interior_quadCone]
  simp only [mem_ofPred_eq]
  refine forall_congr' fun i => ?_
  by_cases hi : i ∈ vanIdx (coordFun (T 0)) D.N
  · rw [coordFun_regraphMap hπ T hT v hi]
  · have key : ∀ w ∈ quadCone (coordFun (T 0)) D.N,
        (0 < coordFun (T 0) i (w : D.φ.model.E 0) ↔ w ≠ 0) := by
      intro w hw
      constructor
      · intro h hw0; rw [hw0] at h; simp at h
      · intro hw0; exact pos_of_not_mem_vanIdx _ _ hw hw0 hi
    rw [key v hvK, key _ hgK, hne]

/-- `Dδ(0) = 0` within `N ∩ C`, as a derivative statement. -/
theorem hasFDerivWithinAt_δ_zero (D : P.TangentGermChart M x n) :
    HasFDerivWithinAt D.δ (0 : D.N →L[ℝ] D.φ.model.E 0) D.cone 0 := by
  obtain ⟨V₁, ⟨O₁, hO₁, hV₁⟩, h0V₁, hC1⟩ := D.germ.contDiffOn_one
  have h0O₁ : (0 : D.N) ∈ O₁ := (hV₁ ▸ h0V₁ : (0 : D.N) ∈ O₁ ∩ _).1
  have hd : HasFDerivWithinAt D.δ (fderivWithin ℝ D.δ V₁ 0) V₁ 0 :=
    ((hC1.differentiableOn one_ne_zero) 0 h0V₁).hasFDerivWithinAt
  have hV₁' : V₁ = D.cone ∩ O₁ := by rw [hV₁, inter_comm]
  rw [hV₁', fderivWithin_inter (hO₁.mem_nhds h0O₁), hasFDerivWithinAt_inter (hO₁.mem_nhds h0O₁)]
    at hd
  rwa [D.fderivWithin_zero] at hd

/-- `DΓ(0) = ι : N → E` within `N ∩ C`. -/
theorem hasFDerivWithinAt_Γ_zero (D : P.TangentGermChart M x n) :
    HasFDerivWithinAt D.Γ D.N.subtypeL D.cone 0 := by
  have h := (D.N.subtypeL.hasFDerivWithinAt (s := D.cone) (x := (0 : D.N))).add
    D.hasFDerivWithinAt_δ_zero
  rw [add_zero] at h
  exact h

/-- **`Dg(0) = 1`** within `N ∩ C`. -/
theorem hasFDerivWithinAt_regraphMap_zero (hπ : D.ProjData π') :
    HasFDerivWithinAt (D.regraphMap π') (1 : D.N →L[ℝ] D.N) D.cone 0 := by
  have h := π'.hasFDerivAt.comp_hasFDerivWithinAt (0 : D.N) D.hasFDerivWithinAt_Γ_zero
  have he : π'.comp D.N.subtypeL = 1 := by ext v; simp [hπ.apply_coe]
  rw [he] at h
  exact h

theorem fderivWithin_regraphMap_zero (hπ : D.ProjData π') :
    fderivWithin ℝ (D.regraphMap π') D.cone 0 = 1 :=
  (hasFDerivWithinAt_regraphMap_zero hπ).fderivWithin (D.uniqueDiffOn_cone 0 D.zero_mem_cone)

/-- **The hypotheses of the quadrant inverse function theorem for `g` on a ball**: `g` of class
`C^k` on `O_k ∩ (N ∩ C)`, with `‖Dg − 1‖ ≤ 1/2` on `B(0, r) ∩ (N ∩ C) ⊆ V`, `B(0, r) ⊆ O_k`. -/
theorem invData_ball (hπ : D.ProjData π') {k : ℕ} (hk : 1 ≤ k) {Ok : Set D.N}
    (hgk : ContDiffOn ℝ k (D.regraphMap π') (Ok ∩ D.cone)) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball 0 r ⊆ Ok) (hV : Metric.ball 0 r ∩ D.cone ⊆ D.V)
    (hbound : ∀ v ∈ Metric.ball (0 : D.N) r ∩ D.cone,
      ‖fderivWithin ℝ (D.regraphMap π') D.cone v - 1‖ ≤ 1 / 2) :
    InvData D.cone (Metric.ball 0 r ∩ D.cone) (D.regraphMap π') k := by
  set U : Set D.N := Metric.ball 0 r ∩ D.cone with hUdef
  have hUK : U ⊆ D.cone := inter_subset_right
  have hUO : U ⊆ Ok ∩ D.cone := inter_subset_inter_left _ hball
  have hgU : ContDiffOn ℝ k (D.regraphMap π') U := hgk.mono hUO
  have hconv : Convex ℝ U := (convex_ball 0 r).inter D.isPartialQuadrant.convex
  have hfd : ∀ v ∈ U, fderivWithin ℝ (D.regraphMap π') U v =
      fderivWithin ℝ (D.regraphMap π') D.cone v := fun v hv => by
    rw [hUdef, inter_comm]; exact fderivWithin_inter (Metric.isOpen_ball.mem_nhds hv.1)
  have hkne : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hdiff : ∀ v ∈ U, HasFDerivWithinAt (D.regraphMap π')
      (fderivWithin ℝ (D.regraphMap π') U v) U v := fun v hv =>
    ((hgU.differentiableOn hkne) v hv).hasFDerivWithinAt
  have hbound' : ∀ v ∈ U, ‖fderivWithin ℝ (D.regraphMap π') U v - 1‖ ≤ 1 / 2 := fun v hv => by
    rw [hfd v hv]; exact hbound v hv
  have hinj : InjOn (D.regraphMap π') U := injOn_of_deriv_bound hconv hdiff hbound'
  exact { isPartialQuadrant := D.isPartialQuadrant
          relOpen := ⟨_, Metric.isOpen_ball, rfl⟩
          convex := hconv
          mapsTo := fun v hv => regraphMap_mem_cone hπ (hV hv)
          one_le := hk
          contDiffOn := hgU
          deriv_bound := hbound'
          interior_iff := fun v hv => regraphMap_interior_iff hπ hUK hV
            ⟨Metric.mem_ball_self hr, D.zero_mem_cone⟩ hinj hv }

/-- **The balls on which `g` is a quadrant diffeomorphism**: a radius `r` with
`B(0, r) ∩ (N ∩ C) ⊆ V` and `InvData` of order `1`, and for every `k` and every open `O ∋ 0` a
radius `r' ≤ r` with `B(0, r') ⊆ O` and `InvData` of order `max k 1`. -/
theorem exists_invData_ball (hπ : D.ProjData π') :
    ∃ r > 0, Metric.ball (0 : D.N) r ∩ D.cone ⊆ D.V ∧
      InvData D.cone (Metric.ball 0 r ∩ D.cone) (D.regraphMap π') 1 ∧
      ∀ (k : ℕ) (O : Set D.N), IsOpen O → (0 : D.N) ∈ O → ∃ r' ∈ Ioc 0 r,
        Metric.ball (0 : D.N) r' ⊆ O ∧
        InvData D.cone (Metric.ball 0 r' ∩ D.cone) (D.regraphMap π') (max k 1) := by
  obtain ⟨V₁, ⟨O₁, hO₁, hV₁⟩, h0V₁, hC1⟩ := D.germ.contDiffOn_level_zero 1
  have h0O₁ : (0 : D.N) ∈ O₁ := (hV₁ ▸ h0V₁ : (0 : D.N) ∈ O₁ ∩ _).1
  obtain ⟨OV, hOV, hVeq⟩ := D.V_relOpen
  have h0OV : (0 : D.N) ∈ OV := (hVeq ▸ D.zero_mem_V : (0 : D.N) ∈ OV ∩ _).1
  have hg1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (D.regraphMap π') (O₁ ∩ D.cone) := by
    rw [← hV₁]; exact contDiffOn_regraphMap hC1
  have hUD : UniqueDiffOn ℝ (O₁ ∩ D.cone) := by
    rw [inter_comm]; exact D.uniqueDiffOn_cone.inter hO₁
  have hfd : ∀ v ∈ O₁, fderivWithin ℝ (D.regraphMap π') (O₁ ∩ D.cone) v =
      fderivWithin ℝ (D.regraphMap π') D.cone v := fun v hv => by
    rw [inter_comm]; exact fderivWithin_inter (hO₁.mem_nhds hv)
  have hcont : ContinuousWithinAt (fderivWithin ℝ (D.regraphMap π') (O₁ ∩ D.cone))
      (O₁ ∩ D.cone) 0 :=
    hg1.continuousOn_fderivWithin hUD (by norm_num) 0 ⟨h0O₁, D.zero_mem_cone⟩
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ :=
    (Metric.continuousWithinAt_iff (α := D.N) (β := D.N →L[ℝ] D.N)).1 hcont (1 / 2) (by norm_num)
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.isOpen_iff.1 (hO₁.inter hOV) 0 ⟨h0O₁, h0OV⟩
  set r : ℝ := min δ₀ r₁ with hr
  have hrpos : 0 < r := lt_min hδ₀ hr₁
  have hball : Metric.ball (0 : D.N) r ⊆ O₁ ∩ OV :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans hball₁
  have hV : Metric.ball (0 : D.N) r ∩ D.cone ⊆ D.V := fun v hv => by
    rw [hVeq]; exact ⟨(hball hv.1).2, hv.2⟩
  have hbound : ∀ v ∈ Metric.ball (0 : D.N) r ∩ D.cone,
      ‖fderivWithin ℝ (D.regraphMap π') D.cone v - 1‖ ≤ 1 / 2 := by
    intro v hv
    have hvO₁ : v ∈ O₁ := (hball hv.1).1
    have hdist : dist v 0 < δ₀ := lt_of_lt_of_le (Metric.mem_ball.1 hv.1) (min_le_left _ _)
    have := hδ₀' ⟨hvO₁, hv.2⟩ hdist
    have e : dist (fderivWithin ℝ (D.regraphMap π') (O₁ ∩ D.cone) v)
        (fderivWithin ℝ (D.regraphMap π') (O₁ ∩ D.cone) 0) =
        ‖fderivWithin ℝ (D.regraphMap π') (O₁ ∩ D.cone) v -
          fderivWithin ℝ (D.regraphMap π') (O₁ ∩ D.cone) 0‖ :=
      dist_eq_norm (fderivWithin ℝ (D.regraphMap π') (O₁ ∩ D.cone) v)
        (fderivWithin ℝ (D.regraphMap π') (O₁ ∩ D.cone) 0)
    rw [e, hfd v hvO₁, hfd 0 h0O₁, fderivWithin_regraphMap_zero hπ] at this
    exact this.le
  refine ⟨r, hrpos, hV, invData_ball hπ le_rfl hg1 hrpos (fun v hv => (hball hv).1) hV hbound,
    fun k O hO h0O => ?_⟩
  obtain ⟨Vk, ⟨Ok, hOk, hVk⟩, h0Vk, hCk⟩ := D.germ.contDiffOn_level_zero (max k 1)
  have h0Ok : (0 : D.N) ∈ Ok := (hVk ▸ h0Vk : (0 : D.N) ∈ Ok ∩ _).1
  have hgk : ContDiffOn ℝ (max k 1 : ℕ) (D.regraphMap π') (Ok ∩ D.cone) := by
    rw [← hVk]; exact contDiffOn_regraphMap hCk
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.1 (hO.inter hOk) 0 ⟨h0O, h0Ok⟩
  have hsub : Metric.ball (0 : D.N) (min r r₂) ⊆ O ∩ Ok :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans hball₂
  have hsub' : Metric.ball (0 : D.N) (min r r₂) ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left _ _)
  refine ⟨min r r₂, ⟨lt_min hrpos hr₂, min_le_left _ _⟩, fun v hv => (hsub hv).1, ?_⟩
  exact invData_ball hπ (le_max_right _ _) hgk (lt_min hrpos hr₂) (fun v hv => (hsub hv).2)
    (fun v hv => hV ⟨hsub' hv.1, hv.2⟩) (fun v hv => hbound v ⟨hsub' hv.1, hv.2⟩)

/-! #### The re-graphed datum -/

/-- The inverse `g⁻¹ : g(V) → V` of the re-graphing map (`InvData.inv`). -/
def regraphInv (D : P.TangentGermChart M x n) (π' : D.φ.model.E 0 →L[ℝ] D.N) : D.N → D.N :=
  InvData.inv D.V (D.regraphMap π')

/-- **The re-graphed `δ`**: `δ'(w) = (1 − π')(v + δ(v))` at `v = g⁻¹(w)`, i.e.
`δ'(w) = Γ(g⁻¹ w) − g(g⁻¹ w)`. -/
def regraphδ (D : P.TangentGermChart M x n) (π' : D.φ.model.E 0 →L[ℝ] D.N) :
    D.N → D.φ.model.E 0 :=
  fun w => D.Γ (D.regraphInv π' w) - (D.regraphMap π' (D.regraphInv π' w) : D.φ.model.E 0)

lemma regraphδ_mem_ker (hπ : D.ProjData π') (w : D.N) :
    D.regraphδ π' w ∈ LinearMap.ker (π' : D.φ.model.E 0 →ₗ[ℝ] D.N) :=
  sub_coe_mem_ker hπ _

lemma regraphδ_regraphMap (hInv : InvData D.cone D.V (D.regraphMap π') 1) {u : D.N}
    (hu : u ∈ D.V) :
    D.regraphδ π' (D.regraphMap π' u) = D.Γ u - (D.regraphMap π' u : D.φ.model.E 0) := by
  simp only [regraphδ, regraphInv, hInv.inv_apply hu]

lemma coe_regraphMap_add_regraphδ (hInv : InvData D.cone D.V (D.regraphMap π') 1) {u : D.N}
    (hu : u ∈ D.V) :
    (D.regraphMap π' u : D.φ.model.E 0) + D.regraphδ π' (D.regraphMap π' u) = D.Γ u := by
  rw [regraphδ_regraphMap hInv hu]; abel

lemma regraphInv_zero (hInv : InvData D.cone D.V (D.regraphMap π') 1) :
    D.regraphInv π' 0 = 0 := by
  have h := hInv.inv_apply D.zero_mem_V
  rw [regraphMap_zero] at h
  exact h

/-- **The re-graphed datum** (the key construction): from a datum `D` of Definition 3.2.1 (b)
whose `V` is a convex ball on which `g = π' ∘ (1 + δ)` satisfies the hypotheses of the quadrant
inverse function theorem (`hInv`), with `k`-dependent sub-balls on which `δ` is `C^k` into `E_m`
and `g` is a `C^{max k 1}` quadrant diffeomorphism (`hgerm`), the datum with the same chart and
`N`, the projecting complement `Y' = ker π'`, `V' = g(V)` and `δ' = (1 − π') ∘ Γ ∘ g⁻¹`. -/
def regraph (hπ : D.ProjData π') (hInv : InvData D.cone D.V (D.regraphMap π') 1)
    (hgerm : ∀ m k : ℕ, ∃ U' : Set D.N, (∃ O : Set D.N, IsOpen O ∧ U' = O ∩ D.cone) ∧
      (0 : D.N) ∈ U' ∧ U' ⊆ D.V ∧ (∀ v ∈ U', D.δ v ∈ range (D.φ.model.E.toBase m)) ∧
      ContDiffOn ℝ k (levelMap (E := ScBanach.const D.N) (F := D.φ.model.E) D.δ m) U' ∧
      InvData D.cone U' (D.regraphMap π') (max k 1)) :
    P.TangentGermChart M x n where
  φ := D.φ
  isChart := D.isChart
  mem_source := D.mem_source
  φ_zero := D.φ_zero
  tame := D.tame
  N := D.N
  finiteDimensional := D.finiteDimensional
  finrank_eq := D.finrank_eq
  smooth := D.smooth
  goodPosition := D.goodPosition
  Y := LinearMap.ker (π' : D.φ.model.E 0 →ₗ[ℝ] D.N)
  goodComplement := hπ.goodComplement
  isClosed_Y := π'.isClosed_ker
  V := D.regraphMap π' '' D.V
  V_relOpen := hInv.image_relOpen
  zero_mem_V := ⟨0, D.zero_mem_V, regraphMap_zero⟩
  δ := D.regraphδ π'
  δ_mem_Y := fun w => regraphδ_mem_ker hπ w
  continuousOn := by
    have h1 : ContinuousOn (D.regraphInv π') (D.regraphMap π' '' D.V) := hInv.continuousOn_inv
    have h2 : ContinuousOn (fun u => D.Γ u - (D.regraphMap π' u : D.φ.model.E 0)) D.V :=
      D.Γ_continuousOn.sub (continuous_subtype_val.comp_continuousOn hInv.continuousOn)
    exact h2.comp h1 fun w hw => hInv.inv_mem hw
  image_eq := by
    rw [D.image_eq, image_image]
    exact image_congr fun u hu => (coe_regraphMap_add_regraphδ hInv hu).symm
  germ := by
    intro m k
    obtain ⟨U', hU'rel, h0U', hU'V, hmem, hC, hInv'⟩ := hgerm m k
    have hinv_eq : ∀ w ∈ D.regraphMap π' '' U',
        InvData.inv U' (D.regraphMap π') w = D.regraphInv π' w := by
      rintro _ ⟨u, hu, rfl⟩
      rw [hInv'.inv_apply hu, regraphInv, hInv.inv_apply (hU'V hu)]
    have hinvB : ContDiffOn ℝ k (D.regraphInv π') (D.regraphMap π' '' U') :=
      (hInv'.contDiffOn_inv.congr fun w hw => (hinv_eq w hw).symm).of_le
        (by exact_mod_cast le_max_left k 1)
    have hmaps : MapsTo (D.regraphInv π') (D.regraphMap π' '' U') U' := fun w hw => by
      rw [← hinv_eq w hw]; exact hInv'.inv_mem hw
    have hval : ∀ u ∈ U', D.regraphδ π' (D.regraphMap π' u) ∈ range (D.φ.model.E.toBase m) := by
      intro u hu
      rw [regraphδ_regraphMap hInv (hU'V hu)]
      obtain ⟨y, hy⟩ := hmem u hu
      refine ⟨y + finSmoothLift D.smooth m u - finSmoothLift D.smooth m (D.regraphMap π' u), ?_⟩
      rw [map_sub, map_add, hy, toBase_finSmoothLift, toBase_finSmoothLift, Γ_apply]
      abel
    refine ⟨D.regraphMap π' '' U', hInv'.image_relOpen, ⟨0, h0U', regraphMap_zero⟩, ?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact hval u hu
    · have hlift : ContDiffOn ℝ k (finSmoothLift D.smooth m) univ :=
        (LinearMap.toContinuousLinearMap (finSmoothLift D.smooth m)).contDiff.contDiffOn
      have hFsmooth : ContDiffOn ℝ k (fun w =>
          levelMap (E := ScBanach.const D.N) (F := D.φ.model.E) D.δ m (D.regraphInv π' w) +
            finSmoothLift D.smooth m (D.regraphInv π' w) - finSmoothLift D.smooth m w)
          (D.regraphMap π' '' U') :=
        ((hC.comp hinvB hmaps).add (hlift.comp hinvB (mapsTo_univ _ _))).sub
          (hlift.mono (subset_univ _))
      refine hFsmooth.congr ?_
      rintro _ ⟨u, hu, rfl⟩
      have hu' : D.regraphInv π' (D.regraphMap π' u) = u := hInv.inv_apply (hU'V hu)
      apply D.φ.model.E.toBase_injective m
      rw [toBase_levelMap (by rw [ScBanach.const_toBase]; exact hval u hu), ScBanach.const_toBase,
        map_sub, map_add, hu', toBase_levelMap (by rw [ScBanach.const_toBase]; exact hmem u hu),
        ScBanach.const_toBase, toBase_finSmoothLift, toBase_finSmoothLift,
        regraphδ_regraphMap hInv (hU'V hu), Γ_apply]
      abel
  δ_zero := by
    simp only [regraphδ, regraphInv_zero hInv, regraphMap_zero, Γ_apply, D.δ_zero,
      Submodule.coe_zero, add_zero, sub_zero]
  fderivWithin_zero := by
    have hg0 : HasFDerivWithinAt (D.regraphMap π') (1 : D.N →L[ℝ] D.N) D.V 0 :=
      (hasFDerivWithinAt_regraphMap_zero hπ).mono D.V_subset
    have hfd : fderivWithin ℝ (D.regraphMap π') D.V 0 = 1 :=
      hg0.fderivWithin (hInv.uniqueDiffOn_U 0 D.zero_mem_V)
    have h0V' : (0 : D.N) ∈ D.regraphMap π' '' D.V := ⟨0, D.zero_mem_V, regraphMap_zero⟩
    have hinvD : HasFDerivWithinAt (D.regraphInv π') (1 : D.N →L[ℝ] D.N)
        (D.regraphMap π' '' D.V) 0 := by
      have h := hInv.hasFDerivWithinAt_inv h0V'
      rw [show InvData.inv D.V (D.regraphMap π') 0 = 0 from regraphInv_zero hInv, hfd,
        Ring.inverse_one] at h
      exact h
    have hF : HasFDerivWithinAt (fun u => D.Γ u - (D.regraphMap π' u : D.φ.model.E 0))
        (D.N.subtypeL - D.N.subtypeL.comp (1 : D.N →L[ℝ] D.N)) D.V (D.regraphInv π' 0) := by
      rw [regraphInv_zero hInv]
      exact (D.hasFDerivWithinAt_Γ_zero.mono D.V_subset).sub
        (D.N.subtypeL.hasFDerivAt.comp_hasFDerivWithinAt 0 hg0)
    have hcomp := hF.comp (0 : D.N) hinvD fun w hw => hInv.inv_mem hw
    obtain ⟨O', hO', hV'⟩ := hInv.image_relOpen
    have h0O' : (0 : D.N) ∈ O' := (hV' ▸ h0V' : (0 : D.N) ∈ O' ∩ _).1
    rw [hV', inter_comm, hasFDerivWithinAt_inter (hO'.mem_nhds h0O')] at hcomp
    have hcomp' : HasFDerivWithinAt (D.regraphδ π')
        ((D.N.subtypeL - D.N.subtypeL.comp (1 : D.N →L[ℝ] D.N)).comp (1 : D.N →L[ℝ] D.N))
        D.cone 0 := hcomp
    rw [hcomp'.fderivWithin (D.uniqueDiffOn_cone 0 D.zero_mem_cone)]
    ext v; simp

/-- **The projection of a datum whose good complement is `ker π'`** (for a projection `π'` with
`π' = 1` on `N`) is `π'` itself. -/
theorem π_eq_of_ker {D' : P.TangentGermChart M x n} (π' : D'.φ.model.E 0 →L[ℝ] D'.N)
    (happ : ∀ v : D'.N, π' v = v)
    (hY : D'.Y = LinearMap.ker (π' : D'.φ.model.E 0 →ₗ[ℝ] D'.N)) (z : D'.φ.model.E 0) :
    D'.π z = π' z := by
  have hz : z = ((π' z : D'.N) : D'.φ.model.E 0) + (z - (π' z : D'.φ.model.E 0)) := by abel
  have hmem : z - (π' z : D'.φ.model.E 0) ∈ D'.Y := by
    rw [hY, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, happ, sub_self]
  conv_lhs => rw [hz]
  rw [map_add, D'.π_apply_coe, D'.π_apply_Y hmem, add_zero]

end Regraph

/-! #### The key lemma -/

/-- **The key lemma (top-ten item #10)**: every datum `D` of Definition 3.2.1 (b) at `x` can be
replaced by a datum `D'` on a smaller chart domain whose projection `π'` along the good
complement maps the retract `O` into `C` — condition (b) of `IsRegular`.  Construction: a
projecting complement `Y' = ker π'` (`exists_projData`), the chart domain shrunk to
`{y | π ∘ ϕ(y) ∈ B(0, r)}` so that `V` becomes the convex ball `B(0, r) ∩ N ∩ C` on which
`g = π' ∘ (1 + δ)` is a quadrant diffeomorphism (`exists_invData_ball`), and the re-graphed
datum `regraph`. -/
theorem exists_projecting (D : P.TangentGermChart M x n) :
    ∃ D' : P.TangentGermChart M x n, D'.φ.source ⊆ D.φ.source ∧
      ∀ z ∈ D'.φ.model.O, (D'.π z : D'.φ.model.E 0) ∈ D'.φ.model.C := by
  obtain ⟨π', hπ⟩ := D.exists_projData
  obtain ⟨r, hr, hUV, hInv, hk⟩ := exists_invData_ball hπ
  set U : Set D.N := Metric.ball 0 r ∩ D.cone with hUdef
  have hUrel : ∃ O : Set D.N, IsOpen O ∧ U = O ∩ Subtype.val ⁻¹' D.φ.model.C :=
    ⟨_, Metric.isOpen_ball, rfl⟩
  have h0U : (0 : D.N) ∈ U := ⟨Metric.mem_ball_self hr, D.zero_mem_cone⟩
  -- the chart domain `s = {y ∈ U | π ϕ(y) ∈ B(0, r)}`
  set s : Set X := D.φ.source ∩ D.φ ⁻¹' (D.π ⁻¹' Metric.ball 0 r) with hsdef
  have hs : s ⊆ D.φ.source := inter_subset_left
  have hso : IsOpen s :=
    D.φ.continuousOn_toFun.isOpen_inter_preimage D.φ.isOpen_source
      (Metric.isOpen_ball.preimage D.π.continuous)
  have hxs : x ∈ s := ⟨D.mem_source, by
    change D.π (D.φ x) ∈ Metric.ball 0 r
    rw [D.φ_zero, map_zero]; exact Metric.mem_ball_self hr⟩
  have himage : D.φ '' (M ∩ s) = (fun v : D.N => (v : D.φ.model.E 0) + D.δ v) '' U := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyM, hysrc, hyB⟩, rfl⟩
      obtain ⟨hv, hyΓ⟩ := D.exists_eq_Γ ⟨hyM, hysrc⟩
      exact ⟨D.π (D.φ y), ⟨hyB, D.V_subset hv⟩, hyΓ.symm⟩
    · rintro ⟨v, hv, rfl⟩
      have hvV : v ∈ D.V := hUV hv
      have hmem := D.symm_Γ_mem hvV
      refine ⟨D.φ.symm (D.Γ v), ⟨hmem.1, hmem.2, ?_⟩, D.φ.apply_symm_apply (D.Γ_mem_O hvV)⟩
      change D.π (D.φ (D.φ.symm (D.Γ v))) ∈ Metric.ball 0 r
      rw [D.φ.apply_symm_apply (D.Γ_mem_O hvV), D.π_Γ]
      exact hv.1
  -- the shrunk datum `D₁` with `V = U`, and the transferred data
  set D₁ := D.shrink M hs hso hxs hUrel h0U hUV himage with hD₁
  have hπ₁ : D₁.ProjData π' := ⟨hπ.apply_coe, hπ.mapsTo, hπ.goodComplement⟩
  have hInv₁ : InvData D₁.cone D₁.V (D₁.regraphMap π') 1 := hInv
  have hgerm₁ : ∀ m k : ℕ, ∃ U' : Set D₁.N, (∃ O : Set D₁.N, IsOpen O ∧ U' = O ∩ D₁.cone) ∧
      (0 : D₁.N) ∈ U' ∧ U' ⊆ D₁.V ∧ (∀ v ∈ U', D₁.δ v ∈ range (D₁.φ.model.E.toBase m)) ∧
      ContDiffOn ℝ k (levelMap (E := ScBanach.const D₁.N) (F := D₁.φ.model.E) D₁.δ m) U' ∧
      InvData D₁.cone U' (D₁.regraphMap π') (max k 1) := by
    intro m k
    obtain ⟨Vmk, ⟨Omk, hOmk, hVmk⟩, h0mk, hmem, hC⟩ := D.germ m k
    have h0Omk : (0 : D.N) ∈ Omk := (hVmk ▸ h0mk : (0 : D.N) ∈ Omk ∩ _).1
    obtain ⟨r', ⟨hr'0, hr'r⟩, hball, hInv'⟩ := hk k Omk hOmk h0Omk
    have hsub : Metric.ball (0 : D.N) r' ∩ D.cone ⊆ Vmk := fun v hv => by
      rw [hVmk]; exact ⟨hball hv.1, hv.2⟩
    exact ⟨Metric.ball 0 r' ∩ D.cone, ⟨_, Metric.isOpen_ball, rfl⟩,
      ⟨Metric.mem_ball_self hr'0, D.zero_mem_cone⟩,
      fun v hv => ⟨Metric.ball_subset_ball hr'r hv.1, hv.2⟩, fun v hv => hmem v (hsub hv),
      hC.mono hsub, hInv'⟩
  refine ⟨D₁.regraph hπ₁ hInv₁ hgerm₁, hs, fun z hz => ?_⟩
  rw [π_eq_of_ker (D' := D₁.regraph hπ₁ hInv₁ hgerm₁) π' hπ₁.apply_coe rfl]
  exact hπ.mapsTo z (D.φ.model.O_subset_C (D.φ.image_subset_model hs hz))

/-- **`exists_isRegular_of_locally` without condition (b)** (row V3.74): if every point of `M`
near `x` has a datum of Definition 3.2.1 (b), then `D` can be replaced by regular data at `x` on a
chart with source in `U`, and the dimension is locally constant along `M`. -/
theorem exists_isRegular (D : P.TangentGermChart M x n) {U : Set X} (hU : IsOpen U) (hxU : x ∈ U)
    (hM : ∀ y ∈ M ∩ U, ∃ n' : ℕ, Nonempty (P.TangentGermChart M y n')) :
    ∃ D' : P.TangentGermChart M x n, D'.IsRegular ∧ D'.φ.source ⊆ U ∧
      ∀ y ∈ M ∩ D'.φ.source, ∀ (n' : ℕ) (_ : P.TangentGermChart M y n'), n' = n := by
  obtain ⟨D₁, -, hπ⟩ := D.exists_projecting
  exact D₁.exists_isRegular_of_locally hπ hU hxU hM

end MPolyfold.TangentGermChart

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **Under the tangent germ property every point has regular data**: the two conditions of
`TangentGermChart.IsRegular` are consequences of Definition 3.2.1 (rows V3.24, V3.72, V3.74). -/
theorem HasTangentGermProperty.exists_isRegular {M : Set X} {n : ℕ}
    (hM : P.HasTangentGermProperty M n) {y : X} (hy : y ∈ M) :
    ∃ d : P.TangentGermChart M y n, d.IsRegular := by
  obtain ⟨D⟩ := hM.2 y hy
  obtain ⟨D', hreg, -, -⟩ :=
    D.exists_isRegular isOpen_univ (mem_univ y) fun z hz => ⟨n, hM.2 z hz.1⟩
  exact ⟨D', hreg⟩

end MPolyfold

/-! ### Theorem 3.2.3 under the tangent germ property alone -/

section Thm323

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- **2021 Theorem 3.2.3, p. 106** (preprint: Theorem 3.27), **under the `n`-dimensional tangent
germ property alone** (`theorem_3_2_3_of_isRegular` without its hypothesis `IsRegular`; rows V3.24, V3.72): a
nonempty subset `M` of an M-polyfold `X` with the `n`-dimensional tangent germ property is a
sub-M-polyfold of `X` whose induced structure is tame and equivalent to that of an
`n`-dimensional manifold with boundary with corners; at every `x ∈ M` the maps `y ↦ π ∘ ϕ(y)` of
the regular data are charts of `M` (part (2)). -/
theorem theorem_3_2_3 (P : MPolyfold X) {M : Set X} {n : ℕ} (hne : M.Nonempty)
    (hM : P.HasTangentGermProperty M n) :
    ∃ hsub : P.IsSubMPolyfold M,
      haveI := P.paracompactSpace_subtype M
      (MPolyfold.subPolyfold hsub).IsTame ∧ (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n ∧
      ∀ x (hx : x ∈ M) (d : P.TangentGermChart M x n) (hreg : d.IsRegular) (a₀ : M),
        (MPolyfold.subPolyfold hsub).IsChart (d.chart hreg a₀) ∧
          (⟨x, hx⟩ : M) ∈ (d.chart hreg a₀).source :=
  theorem_3_2_3_of_isRegular P hne fun _ hx => hM.exists_isRegular hx

/-- **Theorem 3.2.3 with the data of Definition 3.2.1 as written** (`HasTangentGermProperty2021`:
good position and good complement in the sense of Definition 3.1.24, no added closedness), under
the tangent germ property alone. -/
theorem theorem_3_2_3_2021def (P : MPolyfold X) {M : Set X} {n : ℕ} (hne : M.Nonempty)
    (hM : P.HasTangentGermProperty2021 M n) :
    ∃ hsub : P.IsSubMPolyfold M,
      haveI := P.paracompactSpace_subtype M
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n := by
  obtain ⟨hsub, h1, h2, -⟩ :=
    theorem_3_2_3 P hne ((MPolyfold.hasTangentGermProperty2021_iff P).1 hM)
  exact ⟨hsub, h1, h2⟩

/-- **Theorem 3.2.3 with the dimension depending on the point** (`theorem_3_2_3_loc_of_isRegular` without
`IsRegular`; row V3.72): if `M ⊆ X_∞` is nonempty and every point of `M` has data of Definition
3.2.1 (b) of some dimension, then `M` is a sub-M-polyfold whose induced structure is tame and
that of a manifold with boundary with corners of locally constant dimension. -/
theorem theorem_3_2_3_loc (P : MPolyfold X) {M : Set X} (hne : M.Nonempty)
    (hM : ∀ x ∈ M, ∃ n : ℕ, Nonempty (P.TangentGermChart M x n)) :
    ∃ hsub : P.IsSubMPolyfold M,
      haveI := P.paracompactSpace_subtype M
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc := by
  have hreg : ∀ x ∈ M, ∃ (n : ℕ) (d : P.TangentGermChart M x n), d.IsRegular := by
    intro x hx
    obtain ⟨n, ⟨D⟩⟩ := hM x hx
    obtain ⟨D', hreg', -, -⟩ :=
      D.exists_isRegular isOpen_univ (mem_univ x) fun z hz => hM z hz.1
    exact ⟨n, D', hreg'⟩
  obtain ⟨hsub, h1, h2, -⟩ := theorem_3_2_3_loc_of_isRegular P hne hreg
  exact ⟨hsub, h1, h2⟩

end Thm323

end Polyfold
