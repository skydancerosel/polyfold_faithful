import Polyfold.Chapter9.Propositions
import Polyfold.Chapter2.TameSub
import Polyfold.Chapter4.Characterization
import Polyfold.Chapter5.Transversality

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9: from §9.2 "The Tangent and Boundary of `Θ`" **Lemma 9.2.13** and
**Remark 9.2.14** (p. 419; 2017: Lemma 9.9 and Remark 9.5, p. 307), and from §9.3 "Orientations"
**Definition 9.3.6** (pp. 425–426; 2017: Definition 9.10, p. 314) and **Lemma 9.3.7** (p. 426,
new in the 2021 edition).  Numbers and pages are the 2021 text's, the 2017 ones in parentheses.

# The position of a submanifold relative to the boundary; tame branched ep⁺-subgroupoids

## The text, paraphrased

(Lemma 9.2.13) For a finite-dimensional submanifold `M` of an M-polyfold `X` the following are
equivalent: (1) `x ∈ M ∩ ∂X` with `d_M(x) = 0`; (2) `T_xM ⊆ T_x^R X`.  (Remark 9.2.14) A point
`x ∈ M ∩ ∂X` need not lie in `∂M`; by the lemma this happens exactly when `T_xM ⊆ T_x^R X`, so
`x ∈ ∂M` iff `x ∈ ∂X` and `T_xM ⊄ T_x^R X` (2017: "not contained in the partial cone `C_xX`").
*Proof* (text): locally `X = O = r(U)`, `x = 0`, `M = s(U)` for an sc⁺-retraction `s`.  (1) ⇒ (2):
an sc-diffeomorphism `Φ : (ℝⁿ, 0) → (W, 0)` onto an open piece of `M` has `Φ(h) ∈ C`, hence
`TΦ(0)h ∈ C` for all `h`, so `T_0M ⊆ T_0O ∩ C`, i.e. `T_0M ⊆ T_0^R O`.  (2) ⇒ (1): with
`C = [0,∞)ᵏ ⊕ W`, `T_0M ⊆ {0} ⊕ W`, so `s` is defined on small vectors of `T_0M`; correcting
`s|_{T_0M}` by the inverse of `Ψ = P ∘ s` (`P` the projection onto `T_0M`) and adding a complement
`Y` gives a local sc-diffeomorphism of `E`, and `M` is realized near `0` as an sc⁺-retract of an
open subset of `E` (with `C = E`), so `d_M(0) = 0`.

(Definition 9.3.6) `Θ : X → ℚ⁺` is *tame* if every `x ∈ supp(Θ)` has an open neighbourhood `U(x)`
admitting the natural `G_x`-action and having the properness property, with a local branching
structure `(Mᵢ)`, `(σᵢ)` on `U(x)` all of whose `Mᵢ` have an equivalent tame structure (in
particular, the text adds, the structure of a manifold with boundary with corners).

(Lemma 9.3.7) For a tame M-polyfold `Y`, submanifolds `M₁`, `M₂` of the same dimension with tame
induced structures, and `y ∈ M₁ ∩ M₂`: `T_yM₁ = T_yM₂` implies `d_{M₁}(y) = d_{M₂}(y)`.  *Proof*
(text): for a tame `M`, `d_M(y) = dim(T_yM/T_y^R M) = d_{C_yM}(0_y)` (Remark 2.5.9); paths
`γ : [0, ε) → M₁` pushed into `M₂` by an sc⁺-retraction `s` onto `M₂` (`Ts(y)` is the identity
on `T_yM₂ = T_yM₁`) give `C_yM₁ ⊆ C_yM₂`, symmetrically `C_yM₁ = C_yM₂`, and likewise (two-sided
paths) `T_y^R M₁ = T_y^R M₂`.

## What is formalized

* **The chart form of `T_xM ⊆ T_x^R X`.**  `Polyfold.IsReducedTangentAt E C Q T z`: the tangent
  space `T_zQ` of a retract lies in `E_z` (Definition 2.33 for the presentation `T`).  For
  `Q ⊆ O` this is `T_zQ ⊆ T_z^R O = T_zO ∩ E_z` (`isReducedTangentAt_iff_subset_reduced`), and,
  `T_zQ` being linear, it is the 2017 wording `T_zQ ⊆ C_zO` with the partial cone
  `C_zO = T_zO ∩ C_z` (`isReducedTangentAt_iff_subset_partialCone`,
  `isReducedTangentAt_iff_subset_partialQuadrant`).  It is carried by germs of
  sc-diffeomorphisms (`IsReducedTangentAt.transport`), hence chart independent
  (`isReducedTangentAt_chart_change`).  On submanifolds: `SubmanifoldData.IsReducedChart`,
  `MPolyfold.IsTangentReducedAt` (some chart) with `IsTangentReducedAt.isReducedChart` (then every
  chart) and `isTangentReducedAt_iff_forall`.
* `MPolyfold.subDegIndex hA a` (`d_M(a)`, the degeneracy index of the induced structure).
* **Lemma 9.2.13, (1) ⇒ (2)**, in every chart: `lemma_9_2_13_chart` and `lemma_9_2_13` (from
  Theorem 2.31 for the induced structure, `theorem_2_31`: in the chart of `M` induced by `φ` the
  partial quadrant is that of `φ`, so `dim(T_xM / T_xM ∩ E_x) ≤ d_M(x) = 0`).
* **Lemma 9.2.13, (2) ⇒ (1), as printed, does not hold as we read it**:
  `not_lemma_9_2_13_two_one` (a point of `ℝⁿ`: (2) holds, `x ∉ ∂ℝⁿ`).  The intended reading is
  for `x ∈ M ∩ ∂X`, or equivalently for every `x ∈ M`: `d_M(x) = 0 ⟺ T_xM ⊆ T_x^R X` (for
  `x ∉ ∂X` both sides hold, `lemma_9_2_13_of_not_mem_boundary`).
* **Remark 9.2.14**, the parts not using (2) ⇒ (1): `remark_9_2_14` ("⇐": `x ∈ ∂X` and
  `T_xM ⊄ T_x^R X` give `x ∈ ∂M`) and `remark_9_2_14_mem_boundary` (`∂M ⊆ ∂X`, Lemma 2.26);
  `x ∈ ∂M` is `1 ≤ d_M(x)` (`mem_boundary_subPolyfold_iff`).
* **Definition 9.3.6**: `EpGroupoid.TameBranchingStructure`, `EpGroupoid.IsTameBranched`, with
  the witnesses `isTameBranched_zero` and `isTameBranched_indicator` (the indicator of a point of
  `ℝⁿ`, a branched ep⁺-subgroupoid by `isBranchedEpSubgroupoid_indicator`);
  `MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero` (a submanifold avoiding `∂X` has a tame
  induced structure).
* **Lemma 9.3.7**: `lemma_9_3_7`, from `subDegIndex_eq_quotDim_of_hasTameInducedStructure`
  (for a tame induced structure, `d_M(y) = dim(T_yM / T_yM ∩ E_y)` in every chart of `X`), which
  rests on `ScRetraction.IsDiffeoGerm.quotDim_eq` (germs of sc-diffeomorphisms preserve
  `dim(T_xO/T_x^R O)`), `MPolyfold.quotDim_eq_of_isChart` and
  `MPolyfold.degIndex_eq_quotDim_of_isTame`; the stronger `subDegIndex_eq_of_tangentSpace_eq`
  needs neither the tameness of `Y` nor the equality of dimensions.

## What the text leaves implicit, and the choices made

* `T_xX` carries no linear structure in Part I (gap G.7), so `T_xM ⊆ T_x^R X` and `T_yM₁ = T_yM₂`
  are stated in a chart `φ` of `X`: `T_xM` is the tangent space at the level-`1` point `z` over
  `φ(x)` of the chart model `φ(W ∩ M)` of `M` (Remark 4.14), `T_x^R X` is `T_zO ∩ E_z`
  (Definition 2.38 in a chart, `reducedTangentSpaceWith`).  The reduced-tangent condition is
  proved chart independent; Lemma 9.2.13 (1) ⇒ (2) concludes it in every chart, Lemma 9.3.7
  assumes the tangent equality in one chart only (the strongest form).
* `d_M` is the degeneracy index of the induced M-polyfold structure (Proposition 2.21,
  `subPolyfold`), with the paracompactness of `M` from `paracompactSpace_subtype`.
* "Equivalent tame structure" in Definition 9.3.6 is `HasTameInducedStructure` (2021 Definition
  2.5.18: the induced structure has an equivalent tame atlas).  "Admitting the natural
  `G_x`-action" is a natural representation (Theorem 7.1, `NaturalRep`) with domain `U(x)`;
  "the properness property" is Definition 7.17 (`HasPropernessProperty`).  `IsTameBranched` is a
  condition on `Θ`, to be combined with `IsBranchedEpSubgroupoid`.
* Lemma 9.3.7: `d_M(y) = dim(T_yM/T_y^R M)` holds in every chart of `X` because the chart of `M`
  induced by `φ` has the partial quadrant of `φ`, so the reduced tangent space of `M` there is
  `T_yM ∩ E_y`; the text's path argument (2021 Lemma 2.4.9, preprint 2.29, in its path form gap
  G.10) is not needed.  The text's Remark 2.5.9 (`d_X(x) = dim(T_xX/T_x^R X)` for tame `X`) is a
  consequence of 2021 Proposition 2.5.6 (13) (preprint 2.36, `proposition_2_36`), here
  `degIndex_eq_quotDim_of_isTame`.
* Lemma 9.2.13 (1) ⇒ (2): the text's step `T_0M ⊆ T_0O ∩ C = T_0^R O` is read with `T_0M`
  linear: `T_0M ⊆ C_0` forces `T_0M ⊆ C_0 ∩ (−C_0) = E_0`
  (`isReducedTangentAt_iff_subset_partialQuadrant`).  The proof here goes through Theorem 2.31
  for the induced structure instead of a diffeomorphism `(ℝⁿ, 0) → (W, 0)`.

## Not formalized, and why

* **Lemma 9.2.13 (2) ⇒ (1)** (for `x ∈ M ∩ ∂X`: `T_xM ⊆ T_x^R X ⇒ d_M(x) = 0`) and the direction
  `x ∈ ∂M ⇒ T_xM ⊄ T_x^R X` of Remark 9.2.14 are in `Chapter9/BoundaryPositionConverse.lean`
  (`lemma_9_2_13_iff`, `remark_9_2_14_iff`): the chart of `M` without boundary is built by the
  inverse function theorem, and the step "has image `M` (near `0`)", which the text does not spell
  out, by the local injectivity of `P` on `M` (`ScRetraction.IsScPlus.exists_injOn_proj`).
* The sentence of Definition 9.3.6 "in particular, every `Mᵢ` has an equivalent structure of a
  smooth manifold with boundary with corners" (a tame finite-dimensional M-polyfold is a manifold
  with corners).
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology Function

noncomputable section

namespace Polyfold

universe u

/-! ### `T_zQ ⊆ E_z`: the chart form of `T_xM ⊆ T_x^R X` -/

/-- **The chart form of `T_xM ⊆ T_x^R X`** (Lemma 9.2.13 (2)): for a retract `Q` (the chart model
of `M`), a presentation `T` of the partial quadrant `C` and a level-`1` point `z`, the tangent
space `T_zQ` lies in the minimal subspace `E_z` (Definition 2.33).  For `Q ⊆ O` it is
`T_zQ ⊆ T_z^R O = T_zO ∩ E_z` (`isReducedTangentAt_iff_subset_reduced`). -/
def IsReducedTangentAt (E : ScBanach) (C Q : Set (E 0)) {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (z : E 1) : Prop :=
  tangentSpace E C Q z ⊆ (minimalSubspaceWith T (E.toBase 1 z) : Set (E 0))

section ReducedTangent

variable {E E' : ScBanach} {C Q : Set (E 0)} {C' : Set (E' 0)} {n n' : ℕ} {W W' : ScBanach}

/-- For `Q ⊆ O = r(U)`, `T_zQ ⊆ E_z` iff `T_zQ ⊆ T_z^R O = T_zO ∩ E_z`. -/
theorem isReducedTangentAt_iff_subset_reduced (R : ScRetraction E C) (hQ : IsScRetract E C Q)
    (hQR : Q ⊆ R.retract) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {z : E 1}
    (hz : z ∈ E.lvlSet Q 1) :
    IsReducedTangentAt E C Q T z ↔
      tangentSpace E C Q z ⊆ (reducedTangentSpaceWith R T z : Set (E 0)) := by
  have hzR : z ∈ E.lvlSet R.retract 1 := hQR hz
  constructor
  · intro h v hv
    have hvO := tangentSpace_subset_of_subset R hQ hQR hz hv
    rw [tangentSpace_eq_range R hzR] at hvO
    obtain ⟨u, hu⟩ := hvO
    exact Submodule.mem_inf.2 ⟨⟨u, hu⟩, h hv⟩
  · intro h v hv
    exact (Submodule.mem_inf.1 (h hv)).2

/-- **The 2017 wording of Remark 9.2.14** (2017 Remark 9.5: "not contained in the partial cone
`C_xX`"): since `T_zQ` is linear, `T_zQ ⊆ C_z` iff `T_zQ ⊆ E_z = C_z ∩ (−C_z)`. -/
theorem isReducedTangentAt_iff_subset_partialQuadrant (hQ : IsScRetract E C Q)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {z : E 1} (hz : z ∈ E.lvlSet Q 1) :
    IsReducedTangentAt E C Q T z ↔
      tangentSpace E C Q z ⊆ partialQuadrantAtWith T (E.toBase 1 z) := by
  obtain ⟨S, rfl⟩ := hQ
  constructor
  · exact fun h _ hv => minimalSubspaceWith_subset_partialQuadrantAtWith T _ (h hv)
  · intro h v hv
    have hv' : -v ∈ tangentSpace E C S.retract z := by
      rw [tangentSpace_eq_coe_submodule S hz] at hv ⊢
      exact neg_mem hv
    refine (mem_minimalSubspaceWith T).2 fun i hi => ?_
    have h1 := h hv i hi
    have h2 := h hv' i hi
    simp only [map_neg, Prod.fst_neg, Pi.neg_apply, neg_nonneg] at h2
    exact le_antisymm h2 h1

/-- **The 2017 wording, with the partial cone `C_zO = T_zO ∩ C_z`** (Definition 2.27): for
`Q ⊆ O = r(U)`, `T_zQ ⊆ E_z` iff `T_zQ ⊆ C_zO`. -/
theorem isReducedTangentAt_iff_subset_partialCone (R : ScRetraction E C) (hQ : IsScRetract E C Q)
    (hQR : Q ⊆ R.retract) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {z : E 1}
    (hz : z ∈ E.lvlSet Q 1) :
    IsReducedTangentAt E C Q T z ↔ tangentSpace E C Q z ⊆ partialConeWith R T z := by
  rw [isReducedTangentAt_iff_subset_partialQuadrant hQ T hz]
  constructor
  · intro h v hv
    have hvO := tangentSpace_subset_of_subset R hQ hQR hz hv
    rw [tangentSpace_eq_range R (hQR hz)] at hvO
    exact ⟨hvO, h hv⟩
  · intro h v hv
    exact (h hv).2

/-- The condition depends only on the tangent space `T_zQ`. -/
theorem IsReducedTangentAt.congr {Q₂ : Set (E 0)}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} {z : E 1}
    (hQ : tangentSpace E C Q z = tangentSpace E C Q₂ z) (h : IsReducedTangentAt E C Q T z) :
    IsReducedTangentAt E C Q₂ T z := by
  unfold IsReducedTangentAt at *
  rw [← hQ]
  exact h

/-- **`T_zQ ⊆ E_z` is carried by germs of sc-diffeomorphisms** (the chart independence of
Lemma 9.2.13 (2)): with `D = D(F ∘ r)(z)` and `D' = D(G ∘ r')(F(z))`, every `w ∈ T_{F(z)}Q'` is
`w = D(D'w)` with `D'w ∈ T_zQ ⊆ E_z`, and `D(E_z) ⊆ E'_{F(z)}` (the two-sided sign argument). -/
theorem IsReducedTangentAt.transport {R : ScRetraction E C} {R' : ScRetraction E' C'}
    {F : E 0 → E' 0} {G : E' 0 → E 0} (h : R.IsDiffeoGerm R' F G)
    (hGs : IsScSmooth R'.U (G ∘ R')) {Q' : Set (E' 0)} (hQ : IsScRetract E C Q)
    (hQ' : IsScRetract E' C' Q') (hQ'R : Q' ⊆ R'.retract) (hFQ : MapsTo F Q Q')
    (hGQ : MapsTo G Q' Q) {z : E 1} (hz : z ∈ E.lvlSet Q 1) (hQR : Q ⊆ R.retract)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0) (hred : IsReducedTangentAt E C Q T z) :
    IsReducedTangentAt E' C' Q' T' (levelMap (F ∘ R) 1 z) := by
  intro w hw
  have hx : z ∈ E.lvlSet R.retract 1 := hQR hz
  have hy' : levelMap (F ∘ R) 1 z ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  have hzQ' : levelMap (F ∘ R) 1 z ∈ E'.lvlSet Q' 1 := by
    rw [ScBanach.mem_lvlSet, h.toBase_image hx]; exact hFQ hz
  have hv : scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) w ∈ tangentSpace E C Q z := by
    have := scDeriv_mem_tangentSpace_of_subset R' hGs hQ' hQ hQ'R hGQ hzQ' hw
    rwa [h.image_image hx] at this
  have hD := h.deriv_mapsTo_minimalSubspace hx T hT T' hT' (hred hv)
  rw [h.deriv_deriv_inv hx] at hD
  have hwO := tangentSpace_subset_of_subset R' hQ' hQ'R hzQ' hw
  rw [tangentSpace_eq_range R' hy'] at hwO
  obtain ⟨u, rfl⟩ := hwO
  have hPP := congrArg (fun L : E' 0 →L[ℝ] E' 0 => L u) (R'.scDeriv_comp_self hy')
  simp only [ContinuousLinearMap.comp_apply] at hPP
  change _ ∈ minimalSubspaceWith T' (E'.toBase 1 (levelMap (F ∘ R) 1 z))
  rw [h.toBase_image hx, ← hPP]
  exact hD

end ReducedTangent

/-! ### `dim(T_xO / T_x^R O)` is preserved by germs of sc-diffeomorphisms -/

namespace ScRetraction.IsDiffeoGerm

variable {E E' : ScBanach} {n n' : ℕ} {W W' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}
  {R : ScRetraction E C} {R' : ScRetraction E' C'} {F : E 0 → E' 0} {G : E' 0 → E 0}

/-- **A germ of sc-diffeomorphisms preserves `dim(T_xO / T_x^R O)`**: `D = D(F ∘ r)(x)` induces
`T_xO / T_x^R O ≅ T_yO' / T_y^R O'` (the isomorphism in the proof of `quotDim_le`). -/
theorem quotDim_eq (h : R.IsDiffeoGerm R' F G) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0) {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) :
    quotDim (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) (reducedTangentSpaceWith R T x) =
      quotDim (LinearMap.range (scDeriv R'.U R' (levelMap (F ∘ R) 1 x) : E' 0 →ₗ[ℝ] E' 0))
        (reducedTangentSpaceWith R' T' (levelMap (F ∘ R) 1 x)) := by
  classical
  set ι := E.toBase 1 with hι
  set y : E' 1 := levelMap (F ∘ R) 1 x with hy
  have hy' : y ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  have hιy : E'.toBase 1 y = F (ι x) := h.toBase_image hx
  set D : E 0 →L[ℝ] E' 0 := scDeriv R.U (F ∘ R) x with hD
  set D' : E' 0 →L[ℝ] E 0 := scDeriv R'.U (G ∘ R') y with hD'
  set P : E 0 →L[ℝ] E 0 := scDeriv R.U R x with hP
  set P' : E' 0 →L[ℝ] E' 0 := scDeriv R'.U R' y with hP'
  have hD'D : ∀ v, D' (D v) = P v := h.deriv_inv_deriv hx
  have hDD' : ∀ w, D (D' w) = P' w := h.deriv_deriv_inv hx
  have hPP : ∀ v, P (P v) = P v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hx)
  have hP'P' : ∀ w, P' (P' w) = P' w := fun w =>
    congrArg (fun L : E' 0 →L[ℝ] E' 0 => L w) (R'.scDeriv_comp_self hy')
  set Ex : Submodule ℝ (E 0) := minimalSubspaceWith T (ι x) with hEx
  set Ey : Submodule ℝ (E' 0) := minimalSubspaceWith T' (F (ι x)) with hEy
  have hDmaps : MapsTo D Ex Ey := h.deriv_mapsTo_minimalSubspace hx T hT T' hT'
  have hD'maps : MapsTo D' Ey Ex := by
    have := h.symm.deriv_mapsTo_minimalSubspace hy' T' hT' T hT
    rw [hιy, h.left_inv _ hx] at this
    exact this
  set Tx : Submodule ℝ (E 0) := LinearMap.range (P : E 0 →ₗ[ℝ] E 0) with hTx
  set Ty : Submodule ℝ (E' 0) := LinearMap.range (P' : E' 0 →ₗ[ℝ] E' 0) with hTy
  have hTxP : ∀ v ∈ Tx, P v = v := by
    rintro _ ⟨u, rfl⟩; exact hPP u
  have hTyP' : ∀ w ∈ Ty, P' w = w := by
    rintro _ ⟨u, rfl⟩; exact hP'P' u
  have hDTy : ∀ v ∈ Tx, D v ∈ Ty := by
    rintro _ ⟨u, rfl⟩
    exact ⟨D u, by change P' (D u) = D (P u); rw [← hD'D, hDD']⟩
  have hTR : reducedTangentSpaceWith R T x = Tx ⊓ Ex := rfl
  have hTR' : reducedTangentSpaceWith R' T' y = Ty ⊓ Ey := by
    change Ty ⊓ minimalSubspaceWith T' (E'.toBase 1 y) = Ty ⊓ Ey
    rw [hιy]
  let Dt : Tx →ₗ[ℝ] Ty := (D : E 0 →ₗ[ℝ] E' 0).restrict hDTy
  let Φ : Tx →ₗ[ℝ] Ty ⧸ (Ty ⊓ Ey).comap Ty.subtype := ((Ty ⊓ Ey).comap Ty.subtype).mkQ.comp Dt
  have hΦsurj : Surjective Φ := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := ((Ty ⊓ Ey).comap Ty.subtype).mkQ_surjective q
    have hD'Tx : D' w ∈ Tx := by
      obtain ⟨u, rfl⟩ := hw
      exact ⟨D' u, by change P (D' u) = D' (P' u); rw [← hDD', hD'D]⟩
    refine ⟨⟨D' w, hD'Tx⟩, ?_⟩
    simp only [Φ, Dt, LinearMap.comp_apply, Submodule.mkQ_apply]
    congr 1
    apply Subtype.ext
    change D (D' w) = w
    rw [hDD', hTyP' w hw]
  have hΦker : LinearMap.ker Φ = (Tx ⊓ Ex).comap Tx.subtype := by
    ext ⟨v, hv⟩
    simp only [Φ, Dt, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.mem_inf, LinearMap.restrict_apply]
    constructor
    · rintro ⟨_, hh⟩
      refine ⟨hv, ?_⟩
      have h1 : D' (D v) ∈ Ex := hD'maps hh
      rwa [hD'D, hTxP v hv] at h1
    · rintro ⟨_, hh⟩
      exact ⟨hDTy v hv, hDmaps hh⟩
  have hiso : (Tx ⧸ (Tx ⊓ Ex).comap Tx.subtype) ≃ₗ[ℝ] (Ty ⧸ (Ty ⊓ Ey).comap Ty.subtype) :=
    hΦker ▸ Φ.quotKerEquivOfSurjective hΦsurj
  calc quotDim Tx (reducedTangentSpaceWith R T x)
      = finrank ℝ (Tx ⧸ (Tx ⊓ Ex).comap Tx.subtype) := by rw [hTR]; rfl
    _ = finrank ℝ (Ty ⧸ (Ty ⊓ Ey).comap Ty.subtype) := hiso.finrank_eq
    _ = quotDim Ty (reducedTangentSpaceWith R' T' y) := by rw [hTR']; rfl

end ScRetraction.IsDiffeoGerm

/-- A finite-dimensional subspace `L` with `dim(L / (B ∩ L)) = 0` lies in `B`. -/
theorem le_of_quotDim_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V] {L B : Submodule ℝ V}
    [FiniteDimensional ℝ L] (h : quotDim L B = 0) : L ≤ B := by
  have hs : Subsingleton (L ⧸ B.comap L.subtype) := Module.finrank_zero_iff.1 h
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top] at hs
  exact hs

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-! ### `dim(T_xO / T_x^R O)` in two charts; tame M-polyfolds -/

/-- **`dim(T_xO / T_x^R O)` does not depend on the chart**: for two charts `φ`, `ψ` around `x`,
retractions onto their models, presentations of their partial quadrants and level-`1` points over
`φ(x)`, `ψ(x)` (the germ `ψ ∘ φ⁻¹` on the overlap, `IsDiffeoGerm.quotDim_eq`). -/
theorem quotDim_eq_of_isChart {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ)
    (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ.model.O)
    (R' : ScRetraction ψ.model.E ψ.model.C) (hR' : R'.retract = ψ.model.O)
    {n n' : ℕ} {W W' : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso ψ.model.E ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : ψ.model.C = T' 0 ⁻¹' quadrant n' W' 0) {x : X} (hx : x ∈ φ.source)
    (hx' : x ∈ ψ.source) {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z = φ x)
    {z' : ψ.model.E 1} (hz' : ψ.model.E.toBase 1 z' = ψ x) :
    quotDim (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0))
        (reducedTangentSpaceWith R T z) =
      quotDim (LinearMap.range (scDeriv R'.U R' z' : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0))
        (reducedTangentSpaceWith R' T' z') := by
  obtain ⟨W₀, hW₀, hW₀eq⟩ := φ.exists_isOpen_image_eq (s := φ.source ∩ ψ.source) inter_subset_left
    (φ.isOpen_source.inter ψ.isOpen_source)
  obtain ⟨W₀', hW₀', hW₀'eq⟩ := ψ.exists_isOpen_image_eq (s := ψ.source ∩ φ.source)
    inter_subset_left (ψ.isOpen_source.inter φ.isOpen_source)
  have germ := (hφ.compatible hψ (P := P)).isDiffeoGerm R hR R' hR' hW₀ hW₀eq hW₀' hW₀'eq
  have hzO : z ∈ φ.model.E.lvlSet (R.restrict hW₀).retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, R.restrict_retract, hR, ← hW₀eq]
    exact φ.mem_overlap ψ hx hx'
  have key := germ.quotDim_eq T hT T' hT' hzO
  have hlev : levelMap (φ.transition ψ ∘ R.restrict hW₀) 1 z = z' := by
    apply ψ.model.E.toBase_injective 1
    rw [germ.toBase_image hzO, hz, φ.transition_apply ψ hx, hz']
  rw [hlev] at key
  have hzU : z ∈ φ.model.E.lvlSet (R.restrict hW₀).U 1 :=
    (R.restrict hW₀).lvlSet_retract_subset 1 hzO
  have hz'O : z' ∈ ψ.model.E.lvlSet (R'.restrict hW₀').retract 1 := by
    rw [ScBanach.mem_lvlSet, hz', R'.restrict_retract, hR', ← hW₀'eq]
    exact ψ.mem_overlap φ hx' hx
  have hz'U : z' ∈ ψ.model.E.lvlSet (R'.restrict hW₀').U 1 :=
    (R'.restrict hW₀').lvlSet_retract_subset 1 hz'O
  rw [reducedTangentSpaceWith_restrict R hW₀ T hzU,
    reducedTangentSpaceWith_restrict R' hW₀' T' hz'U,
    R.scDeriv_restrict hW₀ hzU, R'.scDeriv_restrict hW₀' hz'U] at key
  exact key

variable (P) in
/-- **In a tame M-polyfold, `d_X(x) = dim(T_xO / T_x^R O)` in every chart** at a smooth point
(2021 Remark 2.5.9, i.e. Proposition 2.36 (13), transported to an arbitrary chart): a chart with
a tame model realizes `d_X(x)` (`degIndex_eq_chartDegIndex_of_isTameRetract`) and has
`dim(T/T^R) = d_C` (`quotDim_reducedTangentSpaceWith_eq`), and the quotient dimension is chart
independent (`quotDim_eq_of_isChart`). -/
theorem degIndex_eq_quotDim_of_isTame (hP : P.IsTame) {φ : MChart X} (hφ : P.IsChart φ)
    (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ.model.O) {n : ℕ} {W : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) {x : X} (hx : x ∈ φ.source)
    (hxs : x ∈ P.smoothSet) {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z = φ x) :
    P.degIndex x = quotDim (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0))
      (reducedTangentSpaceWith R T z) := by
  obtain ⟨ψ, hψ, hxψ, R', hR', hR't⟩ := IsTame.exists_chart P hP x
  obtain ⟨n', W', T', hT'⟩ := ψ.model.isPartialQuadrant
  have hs : ψ x ∈ ψ.model.E.smooth := (mem_smoothSet_iff hψ hxψ).1 hxs
  obtain ⟨z', hz', hz's⟩ := exists_smoothLvl_one_of_mem_smooth hs
  have hz'O : z' ∈ ψ.model.E.lvlSet R'.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz', hR']; exact ψ.mapsTo_model x hxψ
  rw [quotDim_eq_of_isChart hφ hψ R hR R' hR' T hT T' hT' hx hxψ hz hz',
    quotDim_reducedTangentSpaceWith_eq (hR't n' W' T' hT') hz'O hz's,
    P.degIndex_eq_chartDegIndex_of_isTameRetract hψ ⟨R', hR', hR't⟩ hxψ, chartDegIndex,
    degIndex_eq T' hT' (ψ.apply_mem_C hxψ), hz']

/-! ### The degeneracy index `d_M` of a submanifold -/

variable (P) in
/-- **`d_M(a)`**: the degeneracy index (Definition 2.22) of the sub-M-polyfold `A` with its induced
structure (Proposition 2.21, `subPolyfold`; `A` is paracompact by `paracompactSpace_subtype`). -/
def subDegIndex {A : Set X} (hA : P.IsSubMPolyfold A) (a : A) : ℕ :=
  letI := P.paracompactSpace_subtype A
  (subPolyfold hA).degIndex a

/-- `d_M(a) ≤ d_X(a)` (Lemma 2.26). -/
theorem subDegIndex_le {A : Set X} (hA : P.IsSubMPolyfold A) (a : A) :
    P.subDegIndex hA a ≤ P.degIndex a.1 := by
  let := P.paracompactSpace_subtype A
  exact lemma_2_26 hA a

/-! ### Lemma 9.2.13 (2) in charts, and its chart independence -/

namespace SubmanifoldData

variable {A : Set X}

/-- **Lemma 9.2.13 (2) in a chart**: for the data `d` of Definition 4.13, a chart `φ` of `X`, a
presentation `T` of its partial quadrant and a level-`1` point `z`, the tangent space
`T_z(φ(W ∩ A))` (the chart form of `T_aA`, Remark 4.14) lies in `E_z`; equivalently in
`T_z^R O`, the chart form of `T_a^R X` (`isReducedTangentAt_iff_subset_reduced`). -/
def IsReducedChart (d : P.SubmanifoldData A) (φ : MChart X) {n : ℕ} {W : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) (z : φ.model.E 1) : Prop :=
  IsReducedTangentAt φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) T z

end SubmanifoldData

variable (P) in
/-- **Lemma 9.2.13 (2)**: `T_aA ⊆ T_a^R X` at `a ∈ A`, for a smooth finite-dimensional submanifold
`A`.  As `T_aX` has no linear structure here (gap G.7), the condition is stated in a chart
(`IsReducedChart`), for some data, chart, presentation and lift; it then holds for all of them
(`IsTangentReducedAt.isReducedChart`). -/
def IsTangentReducedAt (A : Set X) (a : X) : Prop :=
  a ∈ A ∧ ∃ (d : P.SubmanifoldData A) (φ : MChart X) (n : ℕ) (W : ScBanach)
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) (z : φ.model.E 1),
    a ∈ d.V ∧ P.IsChart φ ∧ a ∈ φ.source ∧ φ.model.C = T 0 ⁻¹' quadrant n W 0 ∧
    φ.model.E.toBase 1 z = φ a ∧ d.IsReducedChart φ T z

/-- **The chart change for `T_zQ ⊆ E_z`** (`chart_change_of_transport` with
`IsReducedTangentAt.transport`). -/
theorem isReducedTangentAt_chart_change {φ φ' : MChart X} (hφ : P.IsChart φ)
    (hφ' : P.IsChart φ') {A G G' : Set X} (hG : IsOpen G) (hG' : IsOpen G')
    (hGφ : G ⊆ φ.source) (hGφ' : G' ⊆ φ'.source)
    (hQ : IsScRetract φ.model.E φ.model.C (φ '' (G ∩ A)))
    (hQ' : IsScRetract φ'.model.E φ'.model.C (φ' '' (G' ∩ A))) {a : X} (haA : a ∈ A)
    (haG : a ∈ G) (haG' : a ∈ G') {z : φ.model.E 1} {z' : φ'.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ a) (hz' : φ'.model.E.toBase 1 z' = φ' a)
    (hzs : z ∈ φ.model.E.smoothLvl 1) {n n' : ℕ} {W W' : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso φ'.model.E ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : φ'.model.C = T' 0 ⁻¹' quadrant n' W' 0)
    (h : IsReducedTangentAt φ.model.E φ.model.C (φ '' (G ∩ A)) T z) :
    IsReducedTangentAt φ'.model.E φ'.model.C (φ' '' (G' ∩ A)) T' z' :=
  chart_change_of_transport (fun E C _ Q _ _ T z => IsReducedTangentAt E C Q T z)
    (fun _ _ _ _ _ _ _ _ _ _ hQ _ h => h.congr hQ)
    (fun _ _ _ _ _ _ _ _ h _ hG _ _ hQ hQ' hQR hQ'R hFQ hGQ _ hz _ _ _ T hT _ _ T' hT' hred =>
      hred.transport h hG hQ hQ' hQ'R hFQ hGQ hz hQR T hT T' hT')
    hφ hφ' hG hG' hGφ hGφ' hQ hQ' haA haG haG' hz hz' hzs T hT T' hT' h

/-- **Lemma 9.2.13 (2) is independent of the choices** (the chart, the data of Definition 4.13,
the presentation): if `T_aA ⊆ T_a^R X` in one chart, then in every chart. -/
theorem IsTangentReducedAt.isReducedChart {A : Set X} {a : X} (h : P.IsTangentReducedAt A a)
    (d' : P.SubmanifoldData A) {φ' : MChart X} (hφ' : P.IsChart φ') {n' : ℕ} {W' : ScBanach}
    (T' : ScIso φ'.model.E ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : φ'.model.C = T' 0 ⁻¹' quadrant n' W' 0) {z' : φ'.model.E 1} (ha' : a ∈ d'.V)
    (haφ' : a ∈ φ'.source) (hz' : φ'.model.E.toBase 1 z' = φ' a) :
    d'.IsReducedChart φ' T' z' := by
  obtain ⟨haA, d, φ, n, W, T, z, ha, hφ, haφ, hT, hz, hred⟩ := h
  have hzs : z ∈ φ.model.E.smoothLvl 1 := by
    change φ.model.E.toBase 1 z ∈ (φ.model.E.smooth : Set (φ.model.E 0))
    rw [hz]; exact d.apply_mem_smooth hφ haA ha haφ
  exact isReducedTangentAt_chart_change hφ hφ' (d.toSubData.isOpen_shrink φ)
    (d'.toSubData.isOpen_shrink φ') (d.toSubData.shrink_subset_source φ)
    (d'.toSubData.shrink_subset_source φ') (d.toSubData.isScRetract_image φ hφ)
    (d'.toSubData.isScRetract_image φ' hφ') haA (d.toSubData.mem_shrink φ haA ha haφ)
    (d'.toSubData.mem_shrink φ' haA ha' haφ') hz hz' hzs T hT T' hT' hred

/-- **Lemma 9.2.13 (2), the chart-free form**: `T_aA ⊆ T_a^R X` iff the chart condition holds for
all data, charts, presentations and lifts. -/
theorem isTangentReducedAt_iff_forall {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : X}
    (haA : a ∈ A) :
    P.IsTangentReducedAt A a ↔ ∀ (d : P.SubmanifoldData A) (φ : MChart X), P.IsChart φ →
      ∀ (n : ℕ) (W : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
        φ.model.C = T 0 ⁻¹' quadrant n W 0 → ∀ z : φ.model.E 1, a ∈ d.V → a ∈ φ.source →
          φ.model.E.toBase 1 z = φ a → d.IsReducedChart φ T z := by
  refine ⟨fun h d φ hφ n W T hT z ha haφ hz => h.isReducedChart d hφ T hT ha haφ hz,
    fun h => ?_⟩
  obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hs : φ a ∈ φ.model.E.smooth := (mem_smoothSet_iff hφ haφ).1 (hA.subset_smoothSet haA)
  obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
  exact ⟨haA, hA.data haA, φ, n, W, T, z, hA.mem_data_V haA, hφ, haφ, hT, hz,
    h _ φ hφ n W T hT z (hA.mem_data_V haA) haφ hz⟩

/-! ### Lemma 9.2.13 and Remark 9.2.14 -/

/-- **2021 Lemma 9.2.13, (1) ⇒ (2), p. 419 (2017: Lemma 9.9), in every chart**: if `d_M(a) = 0`,
then `T_aM ⊆ T_a^R X` in every chart `φ` of `X`, for all data of Definition 4.13 and every
presentation `T` of the partial quadrant.  *Proof*: the chart of `M` induced by `φ` has the
retract `Q = φ(W ∩ M)` and the partial quadrant `C` of `φ`, so Theorem 2.31 for `M` gives
`dim(T_zQ / T_zQ ∩ E_z) ≤ d_M(a) = 0`, and `T_zQ` is finite-dimensional (Remark 4.14). -/
theorem lemma_9_2_13_chart {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (d : P.SubmanifoldData A) {φ : MChart X} (hφ : P.IsChart φ) {n : ℕ} {W : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) {a : A} (haV : a.1 ∈ d.V)
    (haφ : a.1 ∈ φ.source) {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z = φ a)
    (h0 : P.subDegIndex hA.isSubMPolyfold a = 0) : d.IsReducedChart φ T z := by
  let := P.paracompactSpace_subtype A
  have hψ := subPolyfold_isChart hA.isSubMPolyfold d.toSubData hφ a
  obtain ⟨R, hR⟩ := d.toSubData.isScRetract_image φ hφ
  have haψ : a ∈ (subChart d.toSubData hφ a).source := d.toSubData.mem_shrink φ a.2 haV haφ
  have key := theorem_2_31 (subPolyfold hA.isSubMPolyfold) hψ R hR T hT haψ hz
  have h0' : (subPolyfold hA.isSubMPolyfold).degIndex a = 0 := h0
  rw [h0', Nat.le_zero] at key
  have hzR : z ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hR]
    exact mem_image_of_mem φ ⟨d.toSubData.mem_shrink φ a.2 haV haφ, a.2⟩
  have hTS : tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) z =
      (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) : Set (φ.model.E 0)) := by
    rw [← hR]; exact tangentSpace_eq_coe_submodule R hzR
  obtain ⟨-, -, -, N, hN, hfin⟩ := d.remark_4_14 hφ a.2 haV haφ hz
  have hNeq : N = LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) :=
    SetLike.coe_injective (hN.trans hTS)
  subst hNeq
  have hle := @le_of_quotDim_eq_zero _ _ _ _ _ hfin key
  intro v hv
  have hv' : v ∈ LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) := by
    rw [← SetLike.mem_coe, ← hTS]; exact hv
  have hB : v ∈ reducedTangentSpaceWith R T z := hle hv'
  unfold reducedTangentSpaceWith at hB
  exact (Submodule.mem_inf.1 hB).2

/-- **2021 Lemma 9.2.13, (1) ⇒ (2), p. 419 (2017: Lemma 9.9)**: for a (finite-dimensional, smooth)
submanifold `M` of `X` and `x ∈ M ∩ ∂X` with `d_M(x) = 0`, `T_xM ⊆ T_x^R X`
(`IsTangentReducedAt`; the hypothesis `x ∈ ∂X` is not used). -/
theorem lemma_9_2_13 {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : A}
    (h : a.1 ∈ P.boundary ∧ P.subDegIndex hA.isSubMPolyfold a = 0) :
    P.IsTangentReducedAt A a :=
  (isTangentReducedAt_iff_forall hA a.2).2 fun d _ hφ _ _ T hT _ ha haφ hz =>
    lemma_9_2_13_chart hA d hφ T hT ha haφ hz h.2

/-- **Lemma 9.2.13 off the boundary**: at `x ∈ M \ ∂X` both `d_M(x) = 0` (Lemma 2.26) and
`T_xM ⊆ T_x^R X` hold (in a chart realizing `d_X(x) = 0`, `E_z` is the whole space).  So, for every
`x ∈ M`, `d_M(x) = 0` iff `T_xM ⊆ T_x^R X` is the reading of the lemma that is consistent with
`not_lemma_9_2_13_two_one`. -/
theorem lemma_9_2_13_of_not_mem_boundary {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : A}
    (ha : a.1 ∉ P.boundary) :
    P.IsTangentReducedAt A a ∧ P.subDegIndex hA.isSubMPolyfold a = 0 := by
  have h0 : P.degIndex a.1 = 0 := by
    have : ¬ 1 ≤ P.degIndex a.1 := ha
    omega
  refine ⟨?_, Nat.le_zero.1 (h0 ▸ subDegIndex_le hA.isSubMPolyfold a)⟩
  obtain ⟨φ, hφ, haφ, hd⟩ := P.exists_isChart_degIndex_eq a.1
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hs : φ a ∈ φ.model.E.smooth := (mem_smoothSet_iff hφ haφ).1 (hA.subset_smoothSet a.2)
  obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
  refine ⟨a.2, hA.data a.2, φ, n, W, T, z, hA.mem_data_V a.2, hφ, haφ, hT, hz, ?_⟩
  intro v _
  refine (mem_minimalSubspaceWith T).2 fun i hi => ?_
  exfalso
  rw [chartDegIndex, degIndex_eq T hT (φ.apply_mem_C haφ), h0, degIndexWith, quadrantDeg] at hd
  rw [hz] at hi
  have hmem : i ∈ Finset.univ.filter fun j => (T 0 (φ a)).1 j = 0 :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
  rw [Finset.card_eq_zero.1 hd.symm] at hmem
  exact Finset.notMem_empty _ hmem

/-- **Lemma 9.2.13, (2) ⇒ (1), as printed, does not hold as we read it**: for a point `p` of
`ℝⁿ` (a `0`-dimensional submanifold, `rnPolyfold_isSmoothSubmanifold_singleton`), (2)
`T_p{p} ⊆ T_p^R ℝⁿ` holds, but `p ∉ ∂ℝⁿ`, so (1) fails.  The direction is meant for
`x ∈ M ∩ ∂X` (the text's proof places `x = 0` in the boundary). -/
theorem not_lemma_9_2_13_two_one (n : ℕ) (p : Fin n → ℝ) :
    (rnPolyfold n).IsTangentReducedAt {p} p ∧ p ∉ (rnPolyfold n).boundary := by
  have hb : p ∉ (rnPolyfold n).boundary := by
    simp [MPolyfold.boundary, rnPolyfold_degIndex]
  exact ⟨(lemma_9_2_13_of_not_mem_boundary (rnPolyfold_isSmoothSubmanifold_singleton n p)
    (a := ⟨p, mem_singleton p⟩) hb).1, hb⟩

/-- `a ∈ ∂M` (the boundary of the induced structure, Definition 2.25) is `1 ≤ d_M(a)`. -/
theorem mem_boundary_subPolyfold_iff {A : Set X} (hA : P.IsSubMPolyfold A) (a : A) :
    (letI := P.paracompactSpace_subtype A; a ∈ (subPolyfold hA).boundary) ↔
      1 ≤ P.subDegIndex hA a :=
  Iff.rfl

/-- **2021 Remark 9.2.14, p. 419 (2017: Remark 9.5), "⇐"**: if `x ∈ ∂X` and `T_xM ⊄ T_x^R X`
(equivalently, `T_xM ⊄ C_xX`, `isReducedTangentAt_iff_subset_partialQuadrant`), then `x ∈ ∂M`
(Lemma 9.2.13 (1) ⇒ (2)). -/
theorem remark_9_2_14 {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : A}
    (h : a.1 ∈ P.boundary ∧ ¬ P.IsTangentReducedAt A a) :
    1 ≤ P.subDegIndex hA.isSubMPolyfold a := by
  by_contra h0
  exact h.2 (lemma_9_2_13 hA ⟨h.1, by omega⟩)

/-- **2021 Remark 9.2.14, "⇒", first half**: `∂M ⊆ ∂X` (`d_M ≤ d_X`, Lemma 2.26). -/
theorem remark_9_2_14_mem_boundary {A : Set X} (hA : P.IsSubMPolyfold A) {a : A}
    (h : 1 ≤ P.subDegIndex hA a) : a.1 ∈ P.boundary :=
  h.trans (subDegIndex_le hA a)

/-! ### Lemma 9.3.7 -/

/-- A smooth submanifold of `X` avoiding `∂X` (for instance any submanifold of an M-polyfold
without boundary) has a tame induced structure (2021 Definition 2.5.18): its induced structure
has the structure of a manifold with corners (`hasCornerStructure_of_degIndex_eq_zero`), hence is
tame (`HasCornerStructure.isTame`). -/
theorem hasTameInducedStructure_of_degIndex_eq_zero {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (h0 : ∀ a ∈ A, P.degIndex a = 0) : P.HasTameInducedStructure A := by
  let := P.paracompactSpace_subtype A
  exact ⟨hA.isSubMPolyfold, (hasCornerStructure_of_degIndex_eq_zero hA h0).isTame⟩

/-- **`d_M(a) = dim(T_aM / T_aM ∩ E_a)` for a tame induced structure, in every chart of `X`**
(2021 Remark 2.5.9 for `M`, as used in the proof of Lemma 9.3.7): the chart of `M` induced by `φ`
has the retract `Q = φ(W ∩ M)` and the partial quadrant of `φ`, and `M` is tame, so
`degIndex_eq_quotDim_of_isTame` applies (every point of `M` is smooth, Proposition 4.15 (1)). -/
theorem subDegIndex_eq_quotDim_of_hasTameInducedStructure {A : Set X}
    (hA : P.IsSmoothSubmanifold A) (htame : P.HasTameInducedStructure A)
    (d : P.SubmanifoldData A) {φ : MChart X} (hφ : P.IsChart φ)
    (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ '' (d.toSubData.shrink φ ∩ A))
    {n : ℕ} {W : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) {a : A} (haV : a.1 ∈ d.V)
    (haφ : a.1 ∈ φ.source) {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z = φ a) :
    P.subDegIndex hA.isSubMPolyfold a =
      quotDim (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0))
        (reducedTangentSpaceWith R T z) := by
  let := P.paracompactSpace_subtype A
  obtain ⟨_, hY⟩ := htame
  have hψ := subPolyfold_isChart hA.isSubMPolyfold d.toSubData hφ a
  have haψ : a ∈ (subChart d.toSubData hφ a).source := d.toSubData.mem_shrink φ a.2 haV haφ
  have hs : a ∈ (subPolyfold hA.isSubMPolyfold).smoothSet := hA.proposition_4_15_1.2 a
  exact (subPolyfold hA.isSubMPolyfold).degIndex_eq_quotDim_of_isTame hY hψ R hR T hT haψ hs hz

/-- **Lemma 9.3.7, the general form**: for smooth submanifolds `M₁`, `M₂` of `X` with tame induced
structures and `y ∈ M₁ ∩ M₂`, `T_yM₁ = T_yM₂` (in one chart `φ` of `X`) implies
`d_{M₁}(y) = d_{M₂}(y)`.  Neither the tameness of `X` nor the equality of the dimensions is
needed: `d_{Mᵢ}(y) = dim(T_yMᵢ / T_yMᵢ ∩ E_y)` with the same `E_y`. -/
theorem subDegIndex_eq_of_tangentSpace_eq {A₁ A₂ : Set X} (hA₁ : P.IsSmoothSubmanifold A₁)
    (hA₂ : P.IsSmoothSubmanifold A₂) (ht₁ : P.HasTameInducedStructure A₁)
    (ht₂ : P.HasTameInducedStructure A₂) {y : X} (hy₁ : y ∈ A₁) (hy₂ : y ∈ A₂)
    (d₁ : P.SubmanifoldData A₁) (d₂ : P.SubmanifoldData A₂) {φ : MChart X} (hφ : P.IsChart φ)
    (hyV₁ : y ∈ d₁.V) (hyV₂ : y ∈ d₂.V) (hyφ : y ∈ φ.source) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ y)
    (heq : tangentSpace φ.model.E φ.model.C (φ '' (d₁.toSubData.shrink φ ∩ A₁)) z =
      tangentSpace φ.model.E φ.model.C (φ '' (d₂.toSubData.shrink φ ∩ A₂)) z) :
    P.subDegIndex hA₁.isSubMPolyfold ⟨y, hy₁⟩ = P.subDegIndex hA₂.isSubMPolyfold ⟨y, hy₂⟩ := by
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  obtain ⟨R₁, hR₁⟩ := d₁.toSubData.isScRetract_image φ hφ
  obtain ⟨R₂, hR₂⟩ := d₂.toSubData.isScRetract_image φ hφ
  have hz₁ : z ∈ φ.model.E.lvlSet R₁.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hR₁]
    exact mem_image_of_mem φ ⟨d₁.toSubData.mem_shrink φ hy₁ hyV₁ hyφ, hy₁⟩
  have hz₂ : z ∈ φ.model.E.lvlSet R₂.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hR₂]
    exact mem_image_of_mem φ ⟨d₂.toSubData.mem_shrink φ hy₂ hyV₂ hyφ, hy₂⟩
  have hrange : LinearMap.range (scDeriv R₁.U R₁ z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) =
      LinearMap.range (scDeriv R₂.U R₂ z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) := by
    apply SetLike.coe_injective
    rw [← tangentSpace_eq_coe_submodule R₁ hz₁, ← tangentSpace_eq_coe_submodule R₂ hz₂, hR₁, hR₂]
    exact heq
  rw [subDegIndex_eq_quotDim_of_hasTameInducedStructure hA₁ ht₁ d₁ hφ R₁ hR₁ T hT
      (a := ⟨y, hy₁⟩) hyV₁ hyφ hz,
    subDegIndex_eq_quotDim_of_hasTameInducedStructure hA₂ ht₂ d₂ hφ R₂ hR₂ T hT
      (a := ⟨y, hy₂⟩) hyV₂ hyφ hz]
  unfold reducedTangentSpaceWith
  rw [hrange]

/-- **2021 Lemma 9.3.7, p. 426 (new in the 2021 edition)**: for a tame M-polyfold `Y`, submanifolds
`M₁`, `M₂` of the same dimension `k` with tame induced structures and `y ∈ M₁ ∩ M₂`,
`T_yM₁ = T_yM₂` (stated in a chart `φ` of `Y`, gap G.7) implies `d_{M₁}(y) = d_{M₂}(y)`.  The
tameness of `Y` and the dimension hypothesis are not used (`subDegIndex_eq_of_tangentSpace_eq`). -/
theorem lemma_9_3_7 (_hP : P.IsTame) {A₁ A₂ : Set X} {k : ℕ} (hA₁ : P.IsSubmanifoldOfDim A₁ k)
    (hA₂ : P.IsSubmanifoldOfDim A₂ k) (ht₁ : P.HasTameInducedStructure A₁)
    (ht₂ : P.HasTameInducedStructure A₂) {y : X} (hy₁ : y ∈ A₁) (hy₂ : y ∈ A₂)
    (d₁ : P.SubmanifoldData A₁) (d₂ : P.SubmanifoldData A₂) {φ : MChart X} (hφ : P.IsChart φ)
    (hyV₁ : y ∈ d₁.V) (hyV₂ : y ∈ d₂.V) (hyφ : y ∈ φ.source) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ y)
    (heq : tangentSpace φ.model.E φ.model.C (φ '' (d₁.toSubData.shrink φ ∩ A₁)) z =
      tangentSpace φ.model.E φ.model.C (φ '' (d₂.toSubData.shrink φ ∩ A₂)) z) :
    P.subDegIndex hA₁.1.isSubMPolyfold ⟨y, hy₁⟩ = P.subDegIndex hA₂.1.isSubMPolyfold ⟨y, hy₂⟩ :=
  subDegIndex_eq_of_tangentSpace_eq hA₁.1 hA₂.1 ht₁ ht₂ hy₁ hy₂ d₁ d₂ hφ hyV₁ hyV₂ hyφ hz heq

end MPolyfold

/-! ### Definition 9.3.6: tame branched ep⁺-subgroupoids -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **A tame local branching structure at `x`** (2021 Definition 9.3.6, pp. 425–426; 2017:
Definition 9.10): a local branching structure `(Mᵢ)`, `(σᵢ)` representing `Θ` on `U(x)`
(Definition 9.1.2), where `U(x)` admits the natural `G_x`-action (it is the domain of a natural
representation, Theorem 7.1) and has the properness property (Definition 7.17), and every `Mᵢ`
has an equivalent tame structure (its induced structure is tame, 2021 Definition 2.5.18). -/
structure TameBranchingStructure (Θ : Obj → ℚ) (x : Obj) extends
    X.LocalBranchingStructure Θ x where
  /-- The natural representation of `G_x` on `U(x)`. -/
  rep : X.NaturalRep x
  U_eq : U = rep.U
  hasPropernessProperty : X.HasPropernessProperty U
  hasTameInducedStructure : ∀ i, X.PObj.HasTameInducedStructure (M i)

/-- **2021 Definition 9.3.6, pp. 425–426 (2017: Definition 9.10)**: `Θ : X → ℚ⁺` is **tame** if
every `x ∈ supp(Θ)` has a tame local branching structure (`TameBranchingStructure`).  Used for
branched ep⁺-subgroupoids (`IsBranchedEpSubgroupoid`). -/
def IsTameBranched (Θ : Obj → ℚ) : Prop :=
  ∀ x ∈ supp Θ, Nonempty (X.TameBranchingStructure Θ x)

/-- `Θ = 0` is tame (empty support). -/
theorem isTameBranched_zero : X.IsTameBranched 0 := fun _ hx => (lt_irrefl (0 : ℚ) hx).elim

/-- **Satisfiability of Definition 9.3.6 with nonempty support**: the indicator of a point `p` of
`ℝⁿ`, a branched ep⁺-subgroupoid of the trivial ep-groupoid of `ℝⁿ`
(`isBranchedEpSubgroupoid_indicator`), is tame: restrict its local branching structure to the
domain of a natural representation (Theorem 7.1); every subset of `ℝⁿ` has the properness
property in the trivial ep-groupoid, and `{p}` has a tame induced structure (`ℝⁿ` has no
boundary). -/
theorem isTameBranched_indicator (n : ℕ) (p : Fin n → ℝ) :
    (trivial (rnPolyfold n)).IsTameBranched (({p} : Set (Fin n → ℝ)).indicator 1) := by
  intro y hy
  have hyp : y = p := by
    rw [supp_indicator_singleton] at hy; exact hy
  subst hyp
  obtain ⟨R, -⟩ := theorem_7_1 (trivial (rnPolyfold n)) y isOpen_univ (mem_univ y)
  let B := (localBranchingStructure_indicator n y).restrict R.isOpen_U R.mem_U (subset_univ _)
  exact ⟨{ toLocalBranchingStructure := B
           rep := R
           U_eq := rfl
           hasPropernessProperty := hasPropernessProperty_trivial (rnPolyfold n) R.isOpen_U
           hasTameInducedStructure := fun i =>
             MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero (B.isSmoothSubmanifold i)
               fun a _ => rnPolyfold_degIndex n a }⟩

end EpGroupoid

end Polyfold
