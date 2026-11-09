import Polyfold.Chapter2.TameRetracts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.4,
**Proposition 2.5.6 (preprint 2.36)** (the remaining statements): for a tame retract and a smooth point `x`, the
reduced tangent space `T_x^R O` is an sc-subspace and the partial cone `C_xO` is a partial quadrant
in `T_xO`.

# The partial cone of a tame retract

## The text, paraphrased

(Proposition 2.5.6 (preprint 2.36)) Let `(O, C, E)` be a tame retract and `x ∈ O_∞`.  Then `T_x^R O` is an
sc-subspace of codimension `d_O(x)` in `T_xO`, `dim(T_xO/T_x^R O) = d_O(x)`, and `C_xO` is a
partial quadrant in `T_xO` (by the equality case of Theorem 2.4.12 (preprint 2.31)).

## What is formalized

* `Polyfold.splitIso`: for sc-subspaces `B ≤ A` of `E` with `B = A ∩ ⋂_j ker ℓ_j` and smooth
  `e_j ∈ A` dual to continuous functionals `ℓ_1, …, ℓ_d`, the sc-isomorphism
  `A ≅ ℝᵈ ⊕ B`, `v ↦ ((ℓ_j v)_j, v − Σ_j ℓ_j(v) e_j)` (the map `S` of the proof of Theorem 2.4.12 (preprint 2.31),
  with the `e_j` smooth as the exposition requires); `Polyfold.isPartialQuadrant_ofSubspace`.
* `Polyfold.proposition_2_5_6_partialCone`: `T_x O = Dr(x)E` is an sc-subspace, `T_x^R O` is an
  sc-subspace, and `{v ∈ T_xO | v ∈ C_x} = C_xO` is a partial quadrant in the sc-Banach space
  `T_xO`.  (The dimension statement `dim(T_xO/T_x^R O) = d_O(x)` is `Polyfold.proposition_2_5_6`.)

## What the text leaves implicit, and the choices made

* `T_xO` carries the sc-structure induced from `E` (`ScBanach.ofSubspace`); the partial cone is
  the subset of `T_xO` lying in `C_x`.
* For a tame retraction the vectors of the proof of Theorem 2.4.12 (preprint 2.31) can be taken explicitly:
  `ê_j = Dr(x)(T⁻¹(e_{i_j}, 0))`, smooth because `Dr(x)` is an sc-operator at the smooth point `x`,
  with `λ_{i_k}(ê_j) = δ_{jk}` by Proposition 2.5.3 (preprint 2.35); the general equality case of Theorem 2.4.12 (preprint 2.31) is not
  needed.  That `T_x^R O` is an sc-subspace (exposition Lemma 3.A (1)) is proved directly: for
  `u ∈ T_x^R O ∩ E_m` with `T u = (a, w)`, the smooth points `Dr(x)(T⁻¹(a, w'))`, `w' ∈ W_∞`, lie in
  `T_x^R O` and tend to `u`.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### Splitting off finitely many coordinates of an sc-subspace -/

section Split

variable {E : ScBanach} {A B : Submodule ℝ (E 0)} (hA : E.IsScSubspace A) (hB : E.IsScSubspace B)
  {d : ℕ} (ℓ : Fin d → E 0 →L[ℝ] ℝ) (e : Fin d → E 0)

/-- A lift of the smooth vector `e j` to level `m`. -/
def smoothLift (hes : ∀ j, e j ∈ E.smooth) (m : ℕ) (j : Fin d) : E m :=
  ((E.mem_smooth_iff).1 (hes j) m).choose

lemma toBase_smoothLift (hes : ∀ j, e j ∈ E.smooth) (m : ℕ) (j : Fin d) :
    E.toBase m (smoothLift e hes m j) = e j :=
  ((E.mem_smooth_iff).1 (hes j) m).choose_spec

lemma incl_smoothLift (hes : ∀ j, e j ∈ E.smooth) (m : ℕ) (j : Fin d) :
    E.incl m (smoothLift e hes (m + 1) j) = smoothLift e hes m j :=
  E.toBase_injective m (by rw [← E.toBase_succ, toBase_smoothLift, toBase_smoothLift])

variable (hes : ∀ j, e j ∈ E.smooth) (he : ∀ j, e j ∈ A)
  (hℓe : ∀ i j, ℓ i (e j) = if i = j then 1 else 0)
  (hBiff : ∀ v, v ∈ B ↔ v ∈ A ∧ ∀ j, ℓ j v = 0)

include hBiff in
lemma le_of_mem_iff : B ≤ A := fun v hv => ((hBiff v).1 hv).1

include he hℓe hBiff in
lemma sub_sum_mem (v : E 0) (hv : v ∈ A) : v - ∑ j, ℓ j v • e j ∈ B := by
  rw [hBiff]
  refine ⟨A.sub_mem hv (A.sum_mem fun j _ => A.smul_mem _ (he j)), fun i => ?_⟩
  rw [map_sub, map_sum]
  simp only [map_smul, hℓe, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, sub_self]

/-- The level-`m` map `v ↦ ((ℓ_j(v))_j, v − Σ_j ℓ_j(v) e_j)`. -/
def splitFwd (m : ℕ) : E.levelSub A m →L[ℝ] (Fin d → ℝ) × E.levelSub B m :=
  (ContinuousLinearMap.pi fun j => ((ℓ j).comp (E.toBase m)).comp (E.levelSub A m).subtypeL).prod
    (ContinuousLinearMap.codRestrict ((E.levelSub A m).subtypeL -
        ∑ j, (((ℓ j).comp (E.toBase m)).comp (E.levelSub A m).subtypeL).smulRight
          (smoothLift e hes m j)) (E.levelSub B m) fun v => by
      change E.toBase m _ ∈ B
      simp only [sub_apply, FunLike.coe_sum,
        Finset.sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply, map_sub, map_sum, map_smul, toBase_smoothLift]
      exact sub_sum_mem ℓ e he hℓe hBiff _ v.2)

/-- The level-`m` map `(a, u) ↦ u + Σ_j a_j e_j`. -/
def splitBwd (m : ℕ) : (Fin d → ℝ) × E.levelSub B m →L[ℝ] E.levelSub A m :=
  ContinuousLinearMap.codRestrict
    ((E.levelSub B m).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _) +
      ∑ j, ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ _ _)).smulRight
        (smoothLift e hes m j)) (E.levelSub A m) fun p => by
    change E.toBase m _ ∈ A
    simp only [add_apply, FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, map_add, map_sum, map_smul, toBase_smoothLift,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst']
    exact A.add_mem (le_of_mem_iff ℓ hBiff p.2.2) (A.sum_mem fun j _ => A.smul_mem _ (he j))

lemma splitFwd_fst (m : ℕ) (v : E.levelSub A m) (j : Fin d) :
    (splitFwd ℓ e hes he hℓe hBiff m v).1 j = ℓ j (E.toBase m v) := rfl

lemma splitFwd_snd (m : ℕ) (v : E.levelSub A m) :
    ((splitFwd ℓ e hes he hℓe hBiff m v).2 : E m) =
      (v : E m) - ∑ j, ℓ j (E.toBase m v) • smoothLift e hes m j := by
  simp [splitFwd]

lemma splitBwd_val (m : ℕ) (p : (Fin d → ℝ) × E.levelSub B m) :
    (splitBwd ℓ e hes he hBiff m p : E m) = (p.2 : E m) + ∑ j, p.1 j • smoothLift e hes m j := by
  simp [splitBwd]

include hℓe hBiff in
lemma ell_toBase_splitBwd (m : ℕ) (p : (Fin d → ℝ) × E.levelSub B m) (i : Fin d) :
    ℓ i (E.toBase m (splitBwd ℓ e hes he hBiff m p)) = p.1 i := by
  rw [splitBwd_val, map_add, map_sum, map_add, map_sum]
  have h0 : ℓ i (E.toBase m (p.2 : E m)) = 0 := ((hBiff _).1 p.2.2).2 i
  simp only [map_smul, toBase_smoothLift, hℓe, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, h0, zero_add]

lemma splitBwd_splitFwd (m : ℕ) (v : E.levelSub A m) :
    splitBwd ℓ e hes he hBiff m (splitFwd ℓ e hes he hℓe hBiff m v) = v := by
  apply Subtype.ext
  rw [splitBwd_val, splitFwd_snd]
  simp only [splitFwd_fst, sub_add_cancel]

lemma splitFwd_splitBwd (m : ℕ) (p : (Fin d → ℝ) × E.levelSub B m) :
    splitFwd ℓ e hes he hℓe hBiff m (splitBwd ℓ e hes he hBiff m p) = p := by
  refine Prod.ext (funext fun i => ?_) (Subtype.ext ?_)
  · rw [splitFwd_fst]; exact ell_toBase_splitBwd ℓ e hes he hℓe hBiff m p i
  · rw [splitFwd_snd]
    simp only [ell_toBase_splitBwd ℓ e hes he hℓe hBiff m p]
    rw [splitBwd_val, add_sub_cancel_right]

/-- The sc-isomorphism `A ≅ ℝᵈ ⊕ B`, `v ↦ ((ℓ_j(v))_j, v − Σ_j ℓ_j(v) e_j)`, for an sc-subspace
`B = A ∩ ⋂_j ker ℓ_j` and smooth `e_j ∈ A` dual to the `ℓ_j` (the map `S` of the proof of
Theorem 2.4.12 (preprint 2.31)). -/
def splitIso : ScIso (E.ofSubspace hA) ((ScBanach.const (Fin d → ℝ)).prod (E.ofSubspace hB)) where
  lvl m := ContinuousLinearEquiv.equivOfInverse (splitFwd ℓ e hes he hℓe hBiff m)
    (splitBwd ℓ e hes he hBiff m) (splitBwd_splitFwd ℓ e hes he hℓe hBiff m)
    (splitFwd_splitBwd ℓ e hes he hℓe hBiff m)
  incl_comm m v := by
    obtain ⟨w, hw⟩ := v
    refine Prod.ext (funext fun j => ?_) (Subtype.ext ?_)
    · rfl
    · change E.incl m ((splitFwd ℓ e hes he hℓe hBiff (m + 1) ⟨w, hw⟩).2 : E (m + 1)) =
        ((splitFwd ℓ e hes he hℓe hBiff m ⟨E.incl m w, E.incl_mem_levelSub hw⟩).2 : E m)
      rw [splitFwd_snd, splitFwd_snd, map_sub, map_sum]
      simp only [map_smul, incl_smoothLift, ← E.toBase_succ]

lemma splitIso_fst (v : E.levelSub A 0) (j : Fin d) :
    (splitIso hA hB ℓ e hes he hℓe hBiff 0 v).1 j = ℓ j v := rfl

include hB e hes he hℓe hBiff in
/-- `{v ∈ A | ℓ_j(v) ≥ 0 ∀ j}` is a partial quadrant in the sc-Banach space `A`. -/
theorem isPartialQuadrant_ofSubspace :
    IsPartialQuadrant (E.ofSubspace hA) {v : E.levelSub A 0 | ∀ j, 0 ≤ ℓ j v} :=
  ⟨d, E.ofSubspace hB, splitIso hA hB ℓ e hes he hℓe hBiff, by ext v; rfl⟩

end Split

/-! ### Proposition 2.5.6 (preprint 2.36): `C_xO` is a partial quadrant in `T_xO` -/

section TameCone

variable {E : ScBanach} {n : ℕ} {W : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}
  {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}

/-- `T⁻¹(b, 0)` is a smooth point. -/
lemma coordVec_mem_smooth (b : Fin n → ℝ) : coordVec T b ∈ E.smooth := by
  have hp : ((b, 0) : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈
      ((ScBanach.const (Fin n → ℝ)).prod W).smoothLvl 0 := by
    rw [ScBanach.prod_smoothLvl]
    refine ⟨by rw [ScBanach.constScale_smoothLvl]; exact mem_univ _, ?_⟩
    change W.toBase 0 0 ∈ W.smooth
    rw [map_zero]; exact W.smooth.zero_mem
  exact T.symm.toScOperator.mapsTo_smoothLvl 0 hp

/-- **Proposition 2.5.6 (preprint 2.36)**, the remaining statements: at a smooth point `x` of a tame retract, the
reduced tangent space `T_x^R O` is an sc-subspace, and the partial cone `C_xO = T_xO ∩ C_x` is a
partial quadrant in the sc-Banach space `T_xO` (with the sc-structure induced from `E`).

*Proof.* With `P = Dr(x)` and `I(x) = {i_1, …, i_d}`, the smooth vectors `ê_j = P(T⁻¹(e_{i_j}, 0))`
lie in `T_xO` and satisfy `λ_{i_k}(ê_j) = δ_{jk}` (Proposition 2.5.3 (preprint 2.35): `λ_i ∘ P = λ_i` for
`i ∈ I(x)`); `T_x^R O = T_xO ∩ ⋂_k ker λ_{i_k}`, and `v ↦ ((λ_{i_k} v)_k, v − Σ_k λ_{i_k}(v) ê_k)`
is an sc-isomorphism `T_xO ≅ ℝᵈ ⊕ T_x^R O` carrying `C_xO` onto `[0,∞)ᵈ ⊕ T_x^R O` (the map `S`
of Theorem 2.4.12 (preprint 2.31), with the `ê_j` smooth).  The smooth points of `T_x^R O ∩ E_m` are dense: for
`u ∈ T_x^R O ∩ E_m` with `T u = (a, w)`, the points `P(T⁻¹(a, w'))`, `w' ∈ W_∞`, are smooth, lie in
`T_x^R O` (`P E_x ⊆ E_x`) and tend to `P u = u`. -/
theorem proposition_2_5_6_partialCone (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T)
    {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) :
    ∃ hA : E.IsScSubspace (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)),
      E.IsScSubspace (reducedTangentSpaceWith R T x) ∧
      IsPartialQuadrant (E.ofSubspace hA)
        {v : E.levelSub (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) 0 |
          (v : E 0) ∈ partialQuadrantAtWith T (E.toBase 1 x)} := by
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
  set I := zeroSet T x0 with hI
  set d := I.card with hd
  let ι : Fin d → Fin n := fun j => (I.equivFin.symm j : Fin n)
  have hιI : ∀ j, ι j ∈ I := fun j => (I.equivFin.symm j).2
  have hιinj : Injective ι := fun a b h => I.equivFin.symm.injective (Subtype.ext h)
  have hιsurj : ∀ i ∈ I, ∃ j, ι j = i := fun i hi =>
    ⟨I.equivFin ⟨i, hi⟩, by simp only [ι, Equiv.symm_apply_apply]⟩
  let ℓ : Fin d → E 0 →L[ℝ] ℝ := fun j => coordL T (ι j)
  let e : Fin d → E 0 := fun j => P (coordVec T (Pi.single (ι j) 1))
  have hes : ∀ j, e j ∈ E.smooth := fun j => by
    have := Pop.mapsTo_smoothLvl 0 (coordVec_mem_smooth (T := T) (Pi.single (ι j) 1))
    have h2 : P (coordVec T (Pi.single (ι j) 1)) ∈ E.smoothLvl 0 := hP0 _ ▸ this
    exact h2
  have he : ∀ j, e j ∈ LinearMap.range (P : E 0 →ₗ[ℝ] E 0) := fun j => ⟨_, rfl⟩
  have hℓe : ∀ i j, ℓ i (e j) = if i = j then 1 else 0 := fun i j => by
    change (T 0 (P (coordVec T (Pi.single (ι j) 1)))).1 (ι i) = _
    rw [coord_scDeriv_eq hT hR hx hs ((mem_zeroSet T).1 (hιI i)), coord_coordVec,
      Pi.single_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (fun h => hij (hιinj h)), if_neg hij]
  have hBiff : ∀ v, v ∈ reducedTangentSpaceWith R T x ↔
      v ∈ LinearMap.range (P : E 0 →ₗ[ℝ] E 0) ∧ ∀ j, ℓ j v = 0 := fun v => by
    unfold reducedTangentSpaceWith
    rw [Submodule.mem_inf, mem_minimalSubspaceWith]
    refine and_congr Iff.rfl ⟨fun h j => h _ ((mem_zeroSet T).1 (hιI j)), fun h i hi => ?_⟩
    obtain ⟨j, rfl⟩ := hιsurj i ((mem_zeroSet T).2 hi)
    exact h j
  -- `T_x^R O` is an sc-subspace
  have hB : E.IsScSubspace (reducedTangentSpaceWith R T x) := by
    refine ⟨(hA.1.inter (isClosed_minimalSubspaceWith T x0)), fun m u hu => ?_⟩
    have hu' := (hBiff _).1 hu
    have huE : E.toBase m u ∈ minimalSubspaceWith T x0 := (Submodule.mem_inf.1 hu).2
    set a := (T m u).1 with ha
    have ha0 : (T 0 (E.toBase m u)).1 = a := by
      rw [← T.toBase_comm, ScBanach.prod_toBase, ScBanach.const_toBase]
    let φ : W m → E m := fun w' => Pop m ((T m).symm (a, w'))
    have hφc : Continuous φ := (Pop m).continuous.comp
      ((T m).symm.continuous.comp (continuous_const.prodMk continuous_id))
    have hPopu : Pop m u = u := E.toBase_injective m (by
      rw [Pop.toBase_comm, hP0]; exact hPfix _ hu'.1)
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
  refine ⟨hA, hB, ?_⟩
  have hq := isPartialQuadrant_ofSubspace hA hB ℓ e hes he hℓe hBiff
  convert hq using 1
  ext v
  obtain ⟨w, hw⟩ := v
  change (∀ i, (T 0 x0).1 i = 0 → 0 ≤ (T 0 w).1 i) ↔ ∀ j, 0 ≤ (T 0 w).1 (ι j)
  refine ⟨fun h j => h _ ((mem_zeroSet T).1 (hιI j)), fun h i hi => ?_⟩
  obtain ⟨j, rfl⟩ := hιsurj i ((mem_zeroSet T).2 hi)
  exact h j

end TameCone

end Polyfold
