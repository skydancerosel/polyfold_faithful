import Polyfold.Chapter8.TangentEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 8, §8.1: **Lemma 8.8** (p. 263) and the tameness clauses of **Theorem 8.1** (p. 259) and
**Theorem 8.3** (p. 266).  There is no 2014 preprint of Part II; numbers and pages are the 2017
text's.  Part I items carry their 2017 numbers, with the preprint number of the Lean name in
brackets: Definition 2.3 [2.5] (the tangent `(TO, TC, TE)` of a retract, `LocalModel.tangent`,
`ScRetraction.tangentRetraction`), Definition 2.11 [2.18] (`MPolyfold.TangentSpace`,
`MPolyfold.tangentPolyfold`), Definition 2.17 [2.34] (`ScRetraction.IsTame`, `IsTameRetract`),
Definition 2.19 [2.37] (`MPolyfold.IsTame`).  The ep-groupoid `TX` and the functor `T : EP → EP`
are `tangentEpGroupoid` and `tangentFunctor` of `TangentEp.lean`; an ep-groupoid is tame if its
object M-polyfold is (Definition 7.6, `EpGroupoid.IsTame`).

# The tangent of a tame ep-groupoid is tame

## The text, paraphrased

(**Lemma 8.8**) If the ep-groupoid `(X, 𝐗)` is tame, so is `(TX, T𝐗)`.  *Proof*: if
`φ : U → O`, `O = (O, C, E)`, is a tame chart of the object M-polyfold `X` and `O = r(U) ⊆ C` is a
tame retract, then `Tr : TU → TU` is also a tame retraction.  Hence if `(X, 𝐗)` has a tame object
space, so does `(TX, T𝐗)`, which is then a tame ep-groupoid by definition.  (**Theorem 8.1**, second
sentence) If `(X, 𝐗)` is tame, then so is `T(X, 𝐗)`.  (**Theorem 8.3**, last sentence) `T`
preserves tameness: if `X` is a tame ep-groupoid, so is `TX`.

## What is formalized

* **The presentation of `TC`** (namespace `Polyfold`): `ScIso.tangentPres T`, the sc-isomorphism
  `TE ≅ ℝⁿ ⊕ (W¹ ⊕ (ℝⁿ ⊕ W))`, `(a, b) ↦ ((T a)₁, ((T a)₂, T b))`, of Part I's
  `IsPartialQuadrant.tangentSet`, as a definition; `tangentSet_eq_tangentPres`
  (`TC = C¹ ⊕ E` is the preimage of the quadrant), `tangentPres_apply_fst` (its `ℝⁿ`-coordinates
  are those of `a`), `degIndex_tangentSet` (`d_{TC}(a, b) = d_C(a)`),
  `mem_minimalSubspaceWith_tangentPres` (`(TE)_{(a, b)} = (E_a ∩ E₁) ⊕ E`).
* **The derivative of `Tr`** at a level-`1` point `p = (a, b)` of `TU`, with `L = D(Tr)(p)`:
  `ScRetraction.scDeriv_tangentRetraction_fst` (the first component of `L(k, l)` is `Dr(a)k`) and
  `ScRetraction.scDeriv_tangentRetraction_inr` (`L(0, l) = (0, Dr(a)l)`).
* **`Tr` is tame**: `ScRetraction.IsTameWith.tangent` (`Tr` is tame for the presentation
  `tangentPres T` of `TC` if `r` is tame for `T`), `ScRetraction.IsTame.tangentRetraction`
  (`Tr` is tame), `IsTameRetract.tangent` (`(TO, TC, TE)` is a tame retract if `(O, C, E)` is).
* **`TX` is tame**: `MPolyfold.IsTame.tangent` (the tangent M-polyfold of a tame M-polyfold is
  tame).
* **Lemma 8.8 and the tameness clauses**: `EpGroupoid.lemma_8_8`, `EpGroupoid.theorem_8_1_tame`
  (`X.IsTame → X.tangentEpGroupoid.IsTame`) and `theorem_8_3_tame` (for `A : EP`,
  `(tangentFunctor.obj A).X.IsTame` if `A.X.IsTame`), and
  `EpGroupoid.isTame_tangentEpGroupoid_trivial_rn` (the tangent of the trivial ep-groupoid of
  `ℝⁿ` is tame).

## What the text leaves implicit, and the choices made

* **"`Tr` is a tame retraction"** is asserted without argument.  It is proved here from
  Definition 2.17 [2.34].  Write `TC = C¹ ⊕ E` with the presentation `tangentPres T`, whose
  `ℝⁿ`-coordinates at `(a, b)` are those of `a`.  Condition (1): `d_{TC}(a, b) = d_C(a)`, and
  `Tr(a, b) = (r(a), Dr(a)b)`, so it is condition (1) for `r` at `a`.  Condition (2) at a smooth
  point `p = (a, b) ∈ TO`: `a ∈ O` is smooth; take the sc-complement `A ⊆ E_a` of `T_aO = Dr(a)E`
  given by tameness of `r`, and set `A' = (A ∩ E₁) ⊕ A ⊆ (E_a ∩ E₁) ⊕ E = (TE)_p`.  With
  `L = D(Tr)(p)`, `TE = LTE ⊕ A'` holds on every level.  The proof uses only three facts about
  `L`, never the second derivative `D²r(a)` of the text's matrix
  `L = [[Dr(a), 0], [D²r(a)(·, b), Dr(a)]]`:
  - `L` is a projection, since `Tr ∘ Tr = Tr` (Part I's `scDeriv_comp_self`);
  - its first row is `(Dr(a), 0)`, obtained by differentiating `pr₁ ∘ Tr = r ∘ pr₁` on `TU₁`;
  - `L(0, l) = (0, Dr(a)l)`, obtained by differentiating the affine map `w ↦ Tr(a, w)`.

  Both derivatives are first identified on `TE₁` and `E₁` by uniqueness of derivatives, and then
  extended by density and continuity.  Directness: if `(k, l) ∈ LTE ∩ A'` then `L(k, l) = (k, l)`,
  so `k ∈ T_aO ∩ A = 0`, and then `l = Dr(a)l ∈ T_aO ∩ A = 0`.  Sum: write `k = c₁ + α` with
  `c₁ ∈ T_aO` and `α ∈ A`, then `l − (L(c₁, 0))₂ = c₂ + β` with `c₂ ∈ T_aO` and `β ∈ A`; this
  gives `(k, l) = L(c₁, 0) + (0, c₂) + (α, β)`, where `(0, c₂) = L(0, c₂)`.  The same works on
  every level `m`, using the level-`m` operator of the sc-operator `L` and the level-`m` splittings
  of `E`.
* **Presentation independence.**  Tameness quantifies over all presentations of `TC`.  The formal
  proof checks it for the single presentation `tangentPres T` and concludes with Part I's
  `ScRetraction.IsTameWith.isTame` (Lemma 1.24, the presentation independence of `d_C`).
* **From charts to `TX`.**  Around `α ∈ TX` the chart `Tφ` of a tame chart `φ` around
  `p(α) ∈ X₁` is modelled on `T(O, C, E)`, which is a tame retract.  So the atlas of such charts
  is an equivalent tame atlas (`MPolyfold.isTame_of_forall_exists_chart`).  The text's "tame
  chart" is read as a chart of the structure modelled on a tame retract, as in
  `MPolyfold.IsTame.exists_chart`.
* **Hypotheses.**  No hypothesis is added.  `X.IsTame` is satisfiable: the trivial ep-groupoid of
  `ℝⁿ` is tame (`isTame_trivial_rn`), and so is its tangent
  (`isTame_tangentEpGroupoid_trivial_rn`).
-/

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

/-! ### The presentation of `TC = C¹ ⊕ E` -/

section TangentPres

variable {E : ScBanach} {n : ℕ} {W : ScBanach}

/-- `(A ∩ E₁)_m = A ∩ E_{m+1}`: the filtration of `A ∩ E₁` in `E¹` (as in `Lift.lean`). -/
private theorem levelSub_shift_levelSub (A : Submodule ℝ (E 0)) (m : ℕ) :
    E.shift.levelSub (E.levelSub A 1) m = E.levelSub A (m + 1) := by
  ext v
  change E.toBase 1 (E.shift.toBase m v) ∈ A ↔ E.toBase (m + 1) v ∈ A
  rw [E.shift_toBase m v]

/-- An sc-subspace `A ⊆ E` gives the sc-subspace `A ∩ E₁ ⊆ E¹` (as in `Lift.lean`). -/
private theorem isScSubspace_levelSub_one {A : Submodule ℝ (E 0)} (h : E.IsScSubspace A) :
    E.shift.IsScSubspace (E.levelSub A 1) := by
  refine ⟨E.isClosed_levelSub h.1 1, fun m => ?_⟩
  rw [levelSub_shift_levelSub, E.shift_smoothLvl]
  exact h.2 (m + 1)

/-- The presentation `T' = assoc ∘ (T¹ × T) : TE ≅ ℝⁿ ⊕ (W¹ ⊕ (ℝⁿ ⊕ W))` of `TC = C¹ ⊕ E`
induced by a presentation `T : E ≅ ℝⁿ ⊕ W` of `C` (the one of `IsPartialQuadrant.tangentSet`). -/
def ScIso.tangentPres (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    ScIso E.tangent ((ScBanach.const (Fin n → ℝ)).prod
      (W.shift.prod ((ScBanach.const (Fin n → ℝ)).prod W))) :=
  ScIso.trans
    { lvl := fun m => (T (m + 1)).prodCongr (T m)
      incl_comm := fun m x => Prod.ext (T.incl_comm (m + 1) x.1) (T.incl_comm m x.2) }
    (tangentQuadrantIso n W)

/-- The `ℝⁿ`-coordinates of `T'(a, b)` are those of `T(a)`. -/
theorem tangentPres_apply_fst (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (p : E.tangent 0) : (T.tangentPres 0 p).1 = (T 0 (E.toBase 1 p.1)).1 := by
  change (T 1 p.1).1 = _
  rw [← T.toBase_comm, ScBanach.prod_toBase, ScBanach.const_toBase]

/-- `TC = C¹ ⊕ E` is presented by `T'`. -/
theorem tangentSet_eq_tangentPres {C : Set (E 0)}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0) :
    E.tangentSet C =
      T.tangentPres 0 ⁻¹' quadrant n (W.shift.prod ((ScBanach.const (Fin n → ℝ)).prod W)) 0 := by
  subst hT
  ext p
  change p.1 ∈ E.lvlSet (T 0 ⁻¹' quadrant n W 0) 1 ↔ _
  rw [IsPartialQuadrant.lvlSet_eq T 1]
  rfl

/-- `d_{TC}(a, b) = d_C(a)`. -/
theorem degIndex_tangentSet {C : Set (E 0)}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    {p : E.tangent 0} (hp : p ∈ E.tangentSet C) :
    degIndex E.tangent (E.tangentSet C) p = degIndex E C (E.toBase 1 p.1) := by
  rw [degIndex_eq T.tangentPres (tangentSet_eq_tangentPres hT) hp,
    degIndex_eq T hT (x := E.toBase 1 p.1) hp, degIndexWith, degIndexWith, quadrantDeg,
    quadrantDeg, tangentPres_apply_fst]

/-- `(TE)_{(a, b)} = (E_a ∩ E₁) ⊕ E` for the presentation `T'`. -/
theorem mem_minimalSubspaceWith_tangentPres
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {p v : E.tangent 0} :
    v ∈ minimalSubspaceWith T.tangentPres p ↔
      E.toBase 1 v.1 ∈ minimalSubspaceWith T (E.toBase 1 p.1) := by
  rw [mem_minimalSubspaceWith, mem_minimalSubspaceWith, tangentPres_apply_fst,
    tangentPres_apply_fst]

end TangentPres

/-! ### The derivative of `Tr` -/

section TangentDeriv

variable {E : ScBanach} {C : Set (E 0)}

/-- **The first row of `D(Tr)(a, b)`**: for `p = (a, b) ∈ TU₁` and `L = D(Tr)(p)`, the first
component of `L(k, l)` is `Dr(a)k` (differentiate `pr₁ ∘ Tr = r ∘ pr₁` on `TU₁`, then extend by
density). -/
theorem ScRetraction.scDeriv_tangentRetraction_fst (R : ScRetraction E C) {x : E.tangent 1}
    (hx : x ∈ E.tangent.lvlSet R.tangentRetraction.U 1) (q : E.tangent 0) :
    E.toBase 1 (scDeriv R.tangentRetraction.U R.tangentRetraction x q).1 =
      scDeriv R.U R (E.shift.toBase 1 x.1) (E.toBase 1 q.1) := by
  set L := scDeriv R.tangentRetraction.U R.tangentRetraction x
  set y : E 1 := E.shift.toBase 1 x.1
  set P := scDeriv R.U R y
  have hy : y ∈ E.lvlSet R.U 1 := by
    change E.toBase 1 (E.shift.toBase 1 x.1) ∈ R.U
    rw [← E.shift_toBase 1 x.1]
    exact E.mem_lvlSet_tangentSet.1 hx
  let π : E.tangent 0 →L[ℝ] E 0 :=
    (E.toBase 1).comp (ContinuousLinearMap.fst ℝ (E 1) (E 0))
  let σ : E.tangent 1 →L[ℝ] E 1 :=
    (E.shift.toBase 1).comp (ContinuousLinearMap.fst ℝ (E 2) (E 1))
  have h1 := (π.hasFDerivAt.comp_hasFDerivWithinAt x
    (R.tangentRetraction.isSc1.isSc1With_scDeriv.hasFDerivWithinAt x hx))
  have hσ : MapsTo σ (E.tangent.lvlSet R.tangentRetraction.U 1) (E.lvlSet R.U 1) := by
    intro q hq
    change E.toBase 1 (E.shift.toBase 1 q.1) ∈ R.U
    rw [← E.shift_toBase 1 q.1]
    exact E.mem_lvlSet_tangentSet.1 hq
  have h2 := (R.isSc1.isSc1With_scDeriv.hasFDerivWithinAt y hy).comp x
    σ.hasFDerivAt.hasFDerivWithinAt hσ
  -- `pr₁ ∘ Tr = r ∘ pr₁` on `TU₁`
  have heq : EqOn (π ∘ (R.tangentRetraction ∘ E.tangent.toBase 1))
      ((R ∘ E.toBase 1) ∘ σ) (E.tangent.lvlSet R.tangentRetraction.U 1) := by
    intro q hq
    change E.toBase 1 (tangentMap R.U R (E.tangent.toBase 1 q)).1 = R (E.toBase 1 (σ q))
    rw [ScBanach.tangent_toBase]
    exact R.isSc1.isSc0.toBase_levelMap (hσ hq)
  have hcl := (R.tangentRetraction.isScDomain.uniqueDiffWithinAt 1 x hx).eq
    (h1.congr' (fun q hq => (heq hq).symm) hx) h2
  -- extend from the dense range of `TE₁ → TE₀`
  have hd : Dense (Submodule.span ℝ (range (E.tangent.toBase 1)) : Set (E.tangent 0)) :=
    Dense.mono Submodule.subset_span (E.tangent.denseRange_inclK 0 1)
  have hext : π.comp L = (P.comp (E.toBase 1)).comp
      (ContinuousLinearMap.fst ℝ (E 1) (E 0)) := by
    refine ContinuousLinearMap.ext_on hd ?_
    rintro _ ⟨w, rfl⟩
    have := congrArg (fun M : E.tangent 1 →L[ℝ] E 0 => M w) hcl
    simp only [ContinuousLinearMap.comp_apply] at this ⊢
    rw [this, ScBanach.tangent_toBase]
    rfl
  exact congrArg (fun M : E.tangent 0 →L[ℝ] E 0 => M q) hext

/-- **The vertical part of `D(Tr)(a, b)`**: `L(0, l) = (0, Dr(a)l)` (differentiate the affine map
`w ↦ Tr(a, w) = (r(a), Dr(a)w)`, then extend by density). -/
theorem ScRetraction.scDeriv_tangentRetraction_inr (R : ScRetraction E C) {x : E.tangent 1}
    (hx : x ∈ E.tangent.lvlSet R.tangentRetraction.U 1) (l : E 0) :
    scDeriv R.tangentRetraction.U R.tangentRetraction x ((0, l) : E.tangent 0) =
      ((0, scDeriv R.U R (E.shift.toBase 1 x.1) l) : E.tangent 0) := by
  set L := scDeriv R.tangentRetraction.U R.tangentRetraction x
  set y : E 1 := E.shift.toBase 1 x.1
  set P := scDeriv R.U R y
  let ι : E 1 → E.tangent 1 := fun w => (x.1, w)
  have hι : HasFDerivAt ι ((0 : E 1 →L[ℝ] E 2).prod (ContinuousLinearMap.id ℝ (E 1))) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have hιmaps : MapsTo ι univ (E.tangent.lvlSet R.tangentRetraction.U 1) := fun _ _ =>
    E.mem_lvlSet_tangentSet.2 (E.mem_lvlSet_tangentSet.1 hx)
  have h1 := (R.tangentRetraction.isSc1.isSc1With_scDeriv.hasFDerivWithinAt x hx).comp x.2
    hι.hasFDerivWithinAt hιmaps
  have h2 : HasFDerivAt (fun w : E 1 => ((levelMap R 1 y, P (E.toBase 1 w)) : E.tangent 0))
      ((0 : E 1 →L[ℝ] E 1).prod (P.comp (E.toBase 1))) x.2 :=
    (hasFDerivAt_const _ x.2).prodMk (P.comp (E.toBase 1)).hasFDerivAt
  have hfun : (R.tangentRetraction ∘ E.tangent.toBase 1) ∘ ι =
      fun w : E 1 => ((levelMap R 1 y, P (E.toBase 1 w)) : E.tangent 0) := by
    funext w
    change tangentMap R.U R (E.tangent.toBase 1 (x.1, w)) = _
    rw [ScBanach.tangent_toBase]
    rfl
  rw [hfun] at h1
  have hcl := uniqueDiffWithinAt_univ.eq h1 h2.hasFDerivWithinAt
  -- extend from the dense range of `E₁ → E₀`
  have hd : Dense (Submodule.span ℝ (range (E.toBase 1)) : Set (E 0)) :=
    Dense.mono Submodule.subset_span (E.denseRange_inclK 0 1)
  have hext : L.comp (ContinuousLinearMap.inr ℝ (E 1) (E 0)) =
      (ContinuousLinearMap.inr ℝ (E 1) (E 0)).comp P := by
    refine ContinuousLinearMap.ext_on hd ?_
    rintro _ ⟨w, rfl⟩
    have := congrArg (fun M : E 1 →L[ℝ] E.tangent 0 => M w) hcl
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      zero_apply, ContinuousLinearMap.id_apply] at this
    rw [ScBanach.tangent_toBase, map_zero] at this
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact this
  exact congrArg (fun M : E 0 →L[ℝ] E.tangent 0 => M l) hext

end TangentDeriv

/-! ### `Tr` is tame -/

section TangentTame

variable {E : ScBanach} {n : ℕ} {W : ScBanach} {C : Set (E 0)}

/-- **The tangent of a tame retraction is tame** (with respect to the presentation `T'` of `TC`):
(1) `d_{TC}(Tr(a, b)) = d_C(r(a)) = d_C(a) = d_{TC}(a, b)`; (2) at a smooth `p = (a, b) ∈ TO`,
`(A ∩ E₁) ⊕ A ⊆ (TE)_p` is an sc-complement of `T_pTO = D(Tr)(p)TE`, for `A ⊆ E_a` an
sc-complement of `T_aO`. -/
theorem ScRetraction.IsTameWith.tangent {R : ScRetraction E C}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    (h : R.IsTameWith T) : R.tangentRetraction.IsTameWith T.tangentPres := by
  refine ⟨fun p hp => ?_, fun x hx hs => ?_⟩
  · -- condition (1)
    have hpC : p ∈ E.tangentSet C := R.tangentRetraction.U_subset_C hp
    have hrpC : R.tangentRetraction p ∈ E.tangentSet C :=
      R.tangentRetraction.U_subset_C (R.tangentRetraction.mapsTo hp)
    rw [degIndex_tangentSet hT hpC, degIndex_tangentSet hT hrpC]
    have hp1 : p.1 ∈ E.lvlSet R.U 1 := hp
    change degIndex E C (E.toBase 1 (levelMap R 1 p.1)) = _
    rw [R.isSc1.isSc0.toBase_levelMap hp1]
    exact h.degIndex_apply _ hp1
  · -- condition (2)
    have hxU : x ∈ E.tangent.lvlSet R.tangentRetraction.U 1 :=
      R.tangentRetraction.lvlSet_retract_subset 1 hx
    set L := scDeriv R.tangentRetraction.U R.tangentRetraction x
    set y : E 1 := E.shift.toBase 1 x.1
    set P := scDeriv R.U R y
    have hyO : y ∈ E.lvlSet R.retract 1 := by
      have h0 : E.tangent.toBase 1 x ∈ R.tangent := hx
      have := R.fst_mem_of_mem_tangent h0
      rwa [ScBanach.tangent_toBase] at this
    have hys : y ∈ E.smoothLvl 1 := by
      rw [ScBanach.prod_smoothLvl] at hs
      have h2 : x.1 ∈ E.smoothLvl 2 := by
        rw [← E.shift_smoothLvl 1]; exact hs.1
      change E.toBase 1 (E.shift.toBase 1 x.1) ∈ E.smooth
      rw [← E.shift_toBase 1 x.1]
      exact h2
    obtain ⟨A, hA, hAE⟩ := h.exists_complement y hyO hys
    have hPP : ∀ v, P (P v) = P v := fun v =>
      congrArg (fun M : E 0 →L[ℝ] E 0 => M v) (R.scDeriv_comp_self hyO)
    have hLL : ∀ v, L (L v) = L v := fun v =>
      congrArg (fun M : E.tangent 0 →L[ℝ] E.tangent 0 => M v)
        (R.tangentRetraction.scDeriv_comp_self hx)
    have hb : ∀ q : E.tangent 0, E.toBase 1 (L q).1 = P (E.toBase 1 q.1) :=
      R.scDeriv_tangentRetraction_fst hxU
    have hc : ∀ l : E 0, L ((0, l) : E.tangent 0) = ((0, P l) : E.tangent 0) :=
      R.scDeriv_tangentRetraction_inr hxU
    have hfix : ∀ v ∈ LinearMap.range (P : E 0 →ₗ[ℝ] E 0), P v = v := by
      rintro _ ⟨u, rfl⟩; exact hPP u
    have hcompl0 : IsCompl (LinearMap.range (P : E 0 →ₗ[ℝ] E 0)) A := by
      have := hA.2.2 0
      rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
    have hop := R.tangentRetraction.isScOperator_scDeriv hxU hs
    refine ⟨(E.levelSub A 1).prod A, ⟨(R.tangentRetraction.isScSplitting_range_scDeriv hx hs).1,
      IsScSubspace.prod (isScSubspace_levelSub_one hA.2.1) hA.2.1, fun m => ?_⟩, ?_⟩
    · refine isCompl_iff.2 ⟨?_, ?_⟩
      · -- directness, computed on level `0`
        rw [Submodule.disjoint_def]
        intro z hzL hzA
        have hwL : E.tangent.toBase m z ∈ LinearMap.range (L : E.tangent 0 →ₗ[ℝ] E.tangent 0) :=
          hzL
        have hwA : E.tangent.toBase m z ∈ (E.levelSub A 1).prod A := hzA
        generalize hw : E.tangent.toBase m z = w at hwL hwA
        have hLw : L w = w := by
          obtain ⟨u, hu⟩ := hwL
          have hu' : L u = w := hu
          rw [← hu', hLL]
        have h1 : E.toBase 1 w.1 = 0 := by
          have hmem : E.toBase 1 w.1 ∈ LinearMap.range (P : E 0 →ₗ[ℝ] E 0) := by
            refine ⟨E.toBase 1 w.1, ?_⟩
            change P (E.toBase 1 w.1) = E.toBase 1 w.1
            rw [← hb w, hLw]
          exact (Submodule.disjoint_def.1 hcompl0.disjoint) _ hmem hwA.1
        have hw1 : w.1 = 0 := E.toBase_injective 1 (by rw [h1, map_zero])
        have hw2 : w.2 = 0 := by
          have hw' : w = ((0, w.2) : E.tangent 0) := Prod.ext hw1 rfl
          have hPw : P w.2 = w.2 := by
            have := hc w.2
            rw [← hw', hLw] at this
            exact (congrArg Prod.snd this).symm
          have hmem : w.2 ∈ LinearMap.range (P : E 0 →ₗ[ℝ] E 0) := ⟨w.2, hPw⟩
          exact (Submodule.disjoint_def.1 hcompl0.disjoint) _ hmem hwA.2
        have hw0 : w = 0 := Prod.ext hw1 hw2
        exact E.tangent.toBase_injective m (by rw [hw, hw0, map_zero])
      · -- the sum `(k, l) = L(c₁, 0) + (0, c₂) + (α, β)` on level `m`
        rw [codisjoint_iff, eq_top_iff]
        intro z _
        rw [Submodule.mem_sup]
        obtain ⟨Lm, hLm⟩ := hop m
        have hk : z.1 ∈ E.levelSub (LinearMap.range (P : E 0 →ₗ[ℝ] E 0)) (m + 1) ⊔
            E.levelSub A (m + 1) := by
          rw [(hA.2.2 (m + 1)).sup_eq_top]; exact Submodule.mem_top
        obtain ⟨a, ha, α, hα, hak⟩ := Submodule.mem_sup.1 hk
        have hu0 : E.tangent.toBase m (Lm ((a, 0) : E.tangent m)) =
            L ((E.shift.toBase m a, 0) : E.tangent 0) := by
          rw [hLm, ScBanach.tangent_toBase, map_zero]
        have hu1 : (Lm ((a, 0) : E.tangent m)).1 = a := by
          apply E.toBase_injective (m + 1)
          have e1 : E.shift.toBase m (Lm ((a, 0) : E.tangent m)).1 =
              (L ((E.shift.toBase m a, 0) : E.tangent 0)).1 := by
            have := congrArg Prod.fst hu0
            rw [ScBanach.tangent_toBase] at this
            exact this
          rw [E.shift_toBase m, e1, hb, ← E.shift_toBase m a]
          exact hfix _ ha
        have hl : z.2 - (Lm ((a, 0) : E.tangent m)).2 ∈
            E.levelSub (LinearMap.range (P : E 0 →ₗ[ℝ] E 0)) m ⊔ E.levelSub A m := by
          rw [(hA.2.2 m).sup_eq_top]; exact Submodule.mem_top
        obtain ⟨c, hcP, β, hβ, hcl⟩ := Submodule.mem_sup.1 hl
        refine ⟨Lm ((a, 0) : E.tangent m) + ((0, c) : E.tangent m), ?_, ((α, β) : E.tangent m),
          ?_, ?_⟩
        · refine Submodule.add_mem _ ⟨_, hu0.symm⟩ ?_
          change E.tangent.toBase m ((0, c) : E.tangent m) ∈
            LinearMap.range (L : E.tangent 0 →ₗ[ℝ] E.tangent 0)
          rw [ScBanach.tangent_toBase, map_zero]
          refine ⟨((0, E.toBase m c) : E.tangent 0), ?_⟩
          change L (0, E.toBase m c) = (0, E.toBase m c)
          rw [hc, hfix (E.toBase m c) hcP]
        · change E.tangent.toBase m ((α, β) : E.tangent m) ∈ (E.levelSub A 1).prod A
          rw [ScBanach.tangent_toBase]
          refine ⟨?_, hβ⟩
          change E.toBase 1 (E.shift.toBase m α) ∈ A
          rw [← E.shift_toBase m α]
          exact hα
        · refine Prod.ext ?_ ?_
          · simp only [Prod.fst_add, hu1, add_zero, hak]
          · simp only [Prod.snd_add]
            rw [add_assoc, hcl, add_sub_cancel]
    · -- `(A ∩ E₁) ⊕ A ⊆ (E_a ∩ E₁) ⊕ E = (TE)_p`
      intro v hv
      rw [mem_minimalSubspaceWith_tangentPres, ScBanach.tangent_toBase]
      exact hAE (x := E.toBase 1 v.1) hv.1

/-- **`Tr : TU → TU` is a tame retraction** if `r` is (the proof of Lemma 8.8; Definition 2.17
[2.34] for all presentations of `TC`, by `ScRetraction.IsTameWith.isTame`). -/
theorem ScRetraction.IsTame.tangentRetraction {R : ScRetraction E C} (hR : R.IsTame) :
    R.tangentRetraction.IsTame := by
  obtain ⟨n, W, T, hT⟩ := R.relOpen.isPartialQuadrant
  exact (ScRetraction.IsTameWith.tangent hT (hR n W T hT)).isTame (tangentSet_eq_tangentPres hT)

/-- **The tangent `T(O, C, E) = (TO, TC, TE)` of a tame retract is a tame retract.** -/
theorem IsTameRetract.tangent {O : Set (E 0)} (h : IsTameRetract E C O) :
    IsTameRetract E.tangent (E.tangentSet C) (retractTangent E C O) := by
  obtain ⟨R, rfl, hR⟩ := h
  exact ⟨R.tangentRetraction, R.tangentRetraction_retract, hR.tangentRetraction⟩

end TangentTame

/-! ### `TX` is tame -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **The tangent M-polyfold of a tame M-polyfold is tame**: around `α ∈ TX`, the chart `Tφ` of a
tame chart `φ` around `p(α) ∈ X₁` is modelled on the tame retract `T(O, C, E)`. -/
theorem IsTame.tangent [ParacompactSpace P.TangentSpace] (hP : P.IsTame) :
    P.tangentPolyfold.IsTame :=
  isTame_of_forall_exists_chart P.tangentPolyfold fun α => by
    obtain ⟨φ, hφ, hx, ht⟩ := IsTame.exists_chart P hP (P.levelVal 1 (P.tangentProj α))
    exact ⟨tangentChart hφ α, P.tangentPolyfold_isChart hφ α, hx, ht.tangent⟩

end MPolyfold

/-! ### Lemma 8.8 and the tameness clauses of Theorems 8.1 and 8.3 -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **Lemma 8.8**: if the ep-groupoid `(X, 𝐗)` is tame, so is `(TX, T𝐗)` (its object M-polyfold
`TX` is tame, `MPolyfold.IsTame.tangent`). -/
theorem lemma_8_8 (hX : X.IsTame) : X.tangentEpGroupoid.IsTame :=
  MPolyfold.IsTame.tangent hX

/-- **Theorem 8.1, the tameness sentence**: if `(X, 𝐗)` is tame, then `T(X, 𝐗)` is tame. -/
theorem theorem_8_1_tame : X.IsTame → X.tangentEpGroupoid.IsTame :=
  X.lemma_8_8

/-- The tangent of the trivial ep-groupoid of `ℝⁿ` is tame (the hypothesis of Lemma 8.8 is
satisfiable). -/
theorem isTame_tangentEpGroupoid_trivial_rn (n : ℕ) :
    (trivial (rnPolyfold n)).tangentEpGroupoid.IsTame :=
  (trivial (rnPolyfold n)).lemma_8_8 (isTame_trivial_rn n)

end EpGroupoid

/-- **Theorem 8.3, the tameness sentence**: `T : EP → EP` preserves tameness; if `X` is a tame
ep-groupoid, so is `TX = tangentFunctor.obj X`. -/
theorem theorem_8_3_tame (A : EP.{max u 1}) (hA : A.X.IsTame) :
    (tangentFunctor.obj A).X.IsTame :=
  A.X.lemma_8_8 hA

end Polyfold
