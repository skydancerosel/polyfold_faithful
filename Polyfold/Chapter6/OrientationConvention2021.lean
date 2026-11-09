import Polyfold.Chapter6.ProductOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230), the orientation of `f̂(x, t) = f(x) + s(x, t)`
over `X × [0, 1]`, **with the 2021 convention `h̃ = (e ∧ a₁ ∧ … ∧ aₙ) ⊗ (b₁ ∧ … ∧ b_l)*`**.

# Remark 6.6.19 in the 2021 convention (`e` first)

## The text, paraphrased

(2021, Remark 6.6.19) For `L = (f − t)'(x)` oriented by `h = (a₁ ∧ … ∧ aₙ) ⊗ (b₁ ∧ … ∧ b_l)*`, the
operator `L̃(a, b) = La` on `T_{(x, t)}(X × [0, 1])` is oriented by
`h̃ = (e ∧ a₁ ∧ … ∧ aₙ) ⊗ (b₁ ∧ … ∧ b_l)*`, where `e` orients `[0, 1]`; `L̃` lies in the
linearization space of `f̂` at `(x, t)`, which is thereby oriented.  The 2014 preprint
(Remark 6.42) puts `e` **last**; `ProductOrientation.lean` follows the preprint.

## What is formalized

* `wedge_snoc_eq_smul_wedge_cons`: `a₁ ∧ … ∧ aₙ ∧ e = (−1)ⁿ e ∧ a₁ ∧ … ∧ aₙ`.
* `kerSign T = (−1)^{dim ker T}`, `indSign T = (−1)^{ind T}`, and
  `kerSign_eq_indSign_mul_stabSign`: `(−1)^{dim ker} = (−1)^{ind} (−1)^{dim coker}`.
* **The 2021 map** `extDetFirst : det(L) ≅ det(L̃)` and `extDetFirst_wedge_tmul`:
  `(a₁ ∧ … ∧ aₙ) ⊗ d* ↦ (e ∧ (a₁, 0) ∧ … ∧ (aₙ, 0)) ⊗ d*`, exactly the text's `h ↦ h̃`.
* `extDetFirst_eq_indSign_smul_extDetN`: **`extDetFirst = (−1)^{ind L} · extDetN`**, where
  `extDetN` is the sign-normalized map of `ProductOrientation.lean`.
* **The index is locally constant** (`eventually_fredholmIndex_eq`, from Mathlib's
  quasi-inverses and `fredholmIndex_add_of_norm_lt`), so `(−1)^{ind L}` is locally constant
  (`eventually_indSign_eq`), and a line orientation multiplied by a locally constant sign is a line
  orientation (`IsLineOrientation.units_smul`, through `continuousOn_const_smul_section`).
* Hence the 2021 map pulls continuous orientations back (`isLineOrientation_extPullFirst`,
  `LineOrientation.extPullFirst`): the restatement of `isLineOrientation_extPull` with the 2021
  map, for **any** set `C` of Fredholm operators.
* `extConjDetFirst` (the 2021 map after the swap of the factors), `extConjDetFirst_wedge_tmul`,
  `extConjDetFirst_eq_indSign_smul`, and `existsUnique_extConjOrFirst`.
* **Remark 6.6.19 (2021)**: `ChartPoint.existsUnique_prodOrFirst`, `ChartPoint.prodOrFirst`,
  `ChartPoint.prodOrFirst_apply`: an orientation `o` of `DET(f, x)` gives exactly one orientation
  `ô` of `DET(f̂, (t, x))` with `ô(L̂)` the 2021 image `h̃ = e ∧ h` of `o(L)` for **every**
  `L ∈ Lin(f, x)`.  `ChartPoint.exists_extConjDetFirst_eq_sign_smul`: on `Lin(f, x)` the 2021 map
  is the map of `ProductOrientation.lean` times **one** constant sign `(−1)^{ind(f, x)}`
  (`exists_index_linSet`).

## What this makes unnecessary

* Row V6.62: the sign deviation "`(−1)^{dim coker L}`" (Findings, Chapter 6, item 95).  With the
  2021 convention no sign is changed: the text's own map `h ↦ e ∧ h` is continuous in `L`, because
  it differs from the continuous `extDetN` by `(−1)^{ind L}`, which is locally constant.  The row
  can be read *as printed (2021)*; "at a point" (gap G.66) and "`X × [0, 1]` as `ℝ × X`" remain.

## Reading

As in `ProductOrientation.lean`: `X × [0, 1]` is read as `ℝ¹ × X` (decision D2), `L̃` is
conjugated by the swap `A(σ, v) = (v, σ)`, and `e = (0, 1)`.
-/

open Module TensorProduct Bundle Topology Set

noncomputable section

namespace Polyfold

universe u v

/-! ### Moving the last vector of a wedge to the front -/

section Reorder

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- **`a₁ ∧ … ∧ aₙ ∧ e = (−1)ⁿ e ∧ a₁ ∧ … ∧ aₙ`**: the cyclic permutation moving the last place
to the front has sign `(−1)ⁿ` (`Fin.sign_cycleRange`). -/
theorem wedge_snoc_eq_smul_wedge_cons {n : ℕ} (a : Fin n → M) (e : M)
    (h : n + 1 = finrank ℝ M) :
    wedge (Fin.snoc (α := fun _ => M) a e) h =
      (-1 : ℝ) ^ n • wedge (Fin.cons (α := fun _ => M) e a) h := by
  apply Subtype.ext
  have hσ : (Fin.snoc (α := fun _ => M) a e) =
      (Fin.cons (α := fun _ => M) e a) ∘ (Fin.last n).cycleRange := by
    rw [Fin.cons_comp_cycleRange, Fin.insertNth_last']
  change ExteriorAlgebra.ιMulti ℝ (n + 1) _ = (-1 : ℝ) ^ n • ExteriorAlgebra.ιMulti ℝ (n + 1) _
  rw [hσ, AlternatingMap.map_perm, Fin.sign_cycleRange, Fin.val_last, Units.smul_def,
    ← Int.cast_smul_eq_zsmul ℝ]
  push_cast
  rfl

end Reorder

/-! ### The 2021 map `h ↦ e ∧ h` -/

section ExtFirst

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {T : E →L[ℝ] F}

omit [CompleteSpace E] [CompleteSpace F] in
/-- **`(−1)^{dim ker L}`**, the sign of moving `e` past `a₁ ∧ … ∧ aₙ`. -/
def kerSign (T : E →L[ℝ] F) : ℝˣ := (-1) ^ finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))

omit [CompleteSpace E] [CompleteSpace F] in
/-- **`(−1)^{ind L}`** (an integer power of the unit `−1`). -/
def indSign (T : E →L[ℝ] F) : ℝˣ := (-1) ^ fredholmIndex T

omit [CompleteSpace E] [CompleteSpace F] in
/-- `(−1)^{dim ker L} = (−1)^{ind L} (−1)^{dim coker L}`. -/
theorem kerSign_eq_indSign_mul_stabSign (T : E →L[ℝ] F) :
    kerSign T = indSign T * stabSign T := by
  rw [kerSign, indSign, stabSign, fredholmIndex, linIndex, ← zpow_natCast, ← zpow_natCast,
    ← zpow_add, sub_add_cancel]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `(−1)^{ind L}` squares to `1`. -/
theorem indSign_mul_self (T : E →L[ℝ] F) : indSign T * indSign T = 1 := by
  rw [indSign, ← zpow_add, ← two_mul, zpow_mul]
  norm_num

omit [CompleteSpace E] [CompleteSpace F] in
/-- `(−1)^{ind L}` is its own inverse. -/
theorem inv_indSign (T : E →L[ℝ] F) : (indSign T)⁻¹ = indSign T :=
  inv_eq_of_mul_eq_one_left (indSign_mul_self T)

/-- **The map `h ↦ h̃ = e ∧ h` of 2021 Remark 6.6.19**, `det(L) ≅ det(L̃)`:
`(a₁ ∧ … ∧ aₙ) ⊗ ξ ↦ (e ∧ (a₁, 0) ∧ … ∧ (aₙ, 0)) ⊗ ξ` (`extDetFirst_wedge_tmul`), i.e.
`(−1)^{dim ker L}` times the preprint's `extDet`. -/
def extDetFirst (hT : T.IsFredholm) : fredholmDet T ≃ₗ[ℝ] fredholmDet (extOp T) :=
  (LinearEquiv.smulOfUnit (kerSign T)).trans (extDet hT)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `extDetFirst = (−1)^{dim ker L} · extDet`. -/
theorem extDetFirst_apply (hT : T.IsFredholm) (x : fredholmDet T) :
    extDetFirst hT x = ((kerSign T : ℝˣ) : ℝ) • extDet hT x := by
  change extDet hT ((kerSign T : ℝˣ) • x) = _
  rw [Units.smul_def]
  exact (extDet hT).map_smul _ _

omit [CompleteSpace E] [CompleteSpace F] in
/-- **`extDetFirst` on generators is the text's `h ↦ h̃`**: `(a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)* ↦
(e ∧ (a₁, 0) ∧ … ∧ (aₙ, 0)) ⊗ (d₁ ∧ … ∧ d_l)*`, with `e = (0, 1)` placed **first**. -/
theorem extDetFirst_wedge_tmul (hT : T.IsFredholm) {n l : ℕ}
    (a : Fin n → LinearMap.ker (T : E →ₗ[ℝ] F))
    (hn : n = finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))
    {d : Fin l → F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)} (hd : LinearIndependent ℝ d)
    (hl : l = finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))) :
    extDetFirst hT (wedge a hn ⊗ₜ dualVec (wedge d hl)) =
      wedge (Fin.cons (α := fun _ => LinearMap.ker (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F))
          (extE T) (stabJ T 0 ∘ a)) (by rw [hn]; exact finrank_ker_extOp hT) ⊗ₜ
        dualVec (wedge ((extCoker T).symm ∘ d) (hl.trans (extCoker T).symm.finrank_eq)) := by
  have hk : n + 1 = finrank ℝ (LinearMap.ker (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) := by
    rw [hn]; exact finrank_ker_extOp hT
  have hw : wedge (Fin.append (stabJ T 0 ∘ a) ![extE T]) hk =
      (-1 : ℝ) ^ n • wedge (Fin.cons (α := fun _ => LinearMap.ker (extOp T :
        E × (Fin 1 → ℝ) →ₗ[ℝ] F)) (extE T) (stabJ T 0 ∘ a)) hk := by
    rw [Fin.append_right_eq_snoc]
    exact wedge_snoc_eq_smul_wedge_cons _ _ hk
  have h1 : ((kerSign T : ℝˣ) : ℝ) * (-1 : ℝ) ^ n = 1 := by
    rw [kerSign, ← hn, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow]
    norm_num
  rw [extDetFirst_apply, extDet_wedge_tmul hT a hn hd hl]
  refine (congrArg (fun w => ((kerSign T : ℝˣ) : ℝ) • (w ⊗ₜ[ℝ] dualVec (wedge ((extCoker T).symm ∘ d)
    (hl.trans (extCoker T).symm.finrank_eq)))) hw).trans ?_
  rw [← TensorProduct.smul_tmul', smul_smul, h1, one_smul]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **`extDetFirst = (−1)^{ind L} · extDetN`**: the 2021 map and the sign-normalized map of
`ProductOrientation.lean` differ by the sign of the index. -/
theorem extDetFirst_eq_indSign_smul_extDetN (hT : T.IsFredholm) (x : fredholmDet T) :
    extDetFirst hT x = ((indSign T : ℝˣ) : ℝ) • extDetN hT x := by
  rw [extDetFirst_apply, extDetN_apply, smul_smul]
  exact congrArg (· • extDet hT x) (by rw [kerSign_eq_indSign_mul_stabSign, Units.val_mul])

/-- **The index is locally constant** on the Fredholm operators: near a Fredholm `T`, every `S`
has `ind S = ind T` (a quasi-inverse `v` of `T` and `‖v‖ ‖S − T‖ < 1`,
`fredholmIndex_add_of_norm_lt`). -/
theorem eventually_fredholmIndex_eq (hT : T.IsFredholm) :
    ∀ᶠ S in 𝓝 T, fredholmIndex S = fredholmIndex T := by
  obtain ⟨v, hv⟩ := hT.exists_isQuasiInverse
  have hopen : IsOpen {S : E →L[ℝ] F | ‖v‖ * ‖S - T‖ < 1} :=
    isOpen_lt (continuous_const.mul (continuous_id.sub continuous_const).norm) continuous_const
  filter_upwards [hopen.mem_nhds (by simp)] with S hS
  have h := (fredholmIndex_add_of_norm_lt hv (s := S - T) hS).2
  rwa [add_sub_cancel] at h

/-- `(−1)^{ind S}` is locally constant on the Fredholm operators. -/
theorem eventually_indSign_eq (hT : T.IsFredholm) : ∀ᶠ S in 𝓝 T, indSign S = indSign T :=
  (eventually_fredholmIndex_eq hT).mono fun S hS => by rw [indSign, indSign, hS]

end ExtFirst

/-! ### Multiplying a line orientation by a locally constant sign -/

section SmulOrientation

variable {B : Type*} [TopologicalSpace B] {L : B → Type*} [∀ b, AddCommMonoid (L b)]
  [∀ b, Module ℝ (L b)] [TopologicalSpace (TotalSpace ℝ L)] [∀ b, TopologicalSpace (L b)]
  [FiberBundle ℝ L] [VectorBundle ℝ ℝ L]

/-- A constant multiple of a continuous section of a vector bundle is continuous. -/
theorem continuousOn_const_smul_section {U : Set B} {σ : ∀ b, L b}
    (h : ContinuousOn (fun b => TotalSpace.mk' ℝ b (σ b)) U) (k : ℝ) :
    ContinuousOn (fun b => TotalSpace.mk' ℝ b (k • σ b)) U := by
  intro b₀ hb₀
  have h₀ := h b₀ hb₀
  rw [FiberBundle.continuousWithinAt_totalSpace] at h₀ ⊢
  refine ⟨h₀.1, ?_⟩
  have hb : b₀ ∈ (trivializationAt ℝ L b₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt ℝ L b₀
  refine (h₀.2.const_smul k).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds ((trivializationAt ℝ L b₀).open_baseSet.mem_nhds hb)]
      with b hb'
    exact ((trivializationAt ℝ L b₀).linear ℝ hb').map_smul k (σ b)
  · exact ((trivializationAt ℝ L b₀).linear ℝ hb).map_smul k (σ b₀)

/-- **A line orientation times a locally constant sign is a line orientation.** -/
theorem IsLineOrientation.units_smul {o : ∀ b, Module.Ray ℝ (L b)} (ho : IsLineOrientation L o)
    {u : B → ℝˣ} (hu : ∀ b₀, ∀ᶠ b in 𝓝 b₀, u b = u b₀) :
    IsLineOrientation L fun b => u b • o b := by
  intro b₀
  obtain ⟨U, hU, σ, hσc, hσ⟩ := ho b₀
  refine ⟨U ∩ {b | u b = u b₀}, Filter.inter_mem hU (hu b₀), fun b => u b₀ • σ b,
    (continuousOn_const_smul_section hσc ((u b₀ : ℝˣ) : ℝ)).mono inter_subset_left,
    fun b hb => ?_⟩
  obtain ⟨hne, hray⟩ := hσ b hb.1
  refine ⟨(smul_ne_zero_iff_ne _).2 hne, ?_⟩
  change u b • o b = _
  rw [hray, show u b = u b₀ from hb.2, smul_rayOfNeZero]

end SmulOrientation

/-! ### Pulling an orientation back along `L ↦ L̃` with the 2021 map -/

section ExtPullFirst

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {C : Set (E →L[ℝ] F)} {hC : ∀ T ∈ C, T.IsFredholm}
  {C' : Set (E × (Fin 1 → ℝ) →L[ℝ] F)} {hC' : ∀ T ∈ C', T.IsFredholm}

omit [CompleteSpace E] [CompleteSpace F] in
/-- The 2021 map read on the fibres `DetFiber` of `DET`, for `S' = S ⊕ 0`. -/
def extDetFirstFiber {S : FredholmOp E F} {S' : FredholmOp (E × (Fin 1 → ℝ)) F}
    (h : S'.1 = extOp S.1) : DetFiber S ≃ₗ[ℝ] DetFiber S' :=
  (extDetFirst S.2).trans (linDetEquivOfEq (congrArg ContinuousLinearMap.toLinearMap h.symm))

omit [CompleteSpace E] [CompleteSpace F] in
/-- `extDetFirstFiber = (−1)^{ind S} · extDetFiber`. -/
theorem extDetFirstFiber_apply {S : FredholmOp E F} {S' : FredholmOp (E × (Fin 1 → ℝ)) F}
    (h : S'.1 = extOp S.1) (x : DetFiber S) :
    extDetFirstFiber h x = ((indSign S.1 : ℝˣ) : ℝ) • extDetFiber h x := by
  show linDetEquivOfEq (congrArg ContinuousLinearMap.toLinearMap h.symm) (extDetFirst S.2 x) =
    ((indSign S.1 : ℝˣ) : ℝ) •
      linDetEquivOfEq (congrArg ContinuousLinearMap.toLinearMap h.symm) (extDetN S.2 x)
  refine (congrArg (linDetEquivOfEq (congrArg ContinuousLinearMap.toLinearMap h.symm))
    (extDetFirst_eq_indSign_smul_extDetN S.2 (x : fredholmDet S.1))).trans ?_
  exact LinearEquiv.map_smul _ _ _

omit [CompleteSpace E] [CompleteSpace F] in
/-- `extDetFirstFiber` along `S' = S ⊕ 0` is `extDetFirst`. -/
theorem extDetFirstFiber_rfl_apply {T : E →L[ℝ] F} (hS : T.IsFredholm)
    (hS' : (extOp T).IsFredholm) (y : fredholmDet T) :
    extDetFirstFiber (S := ⟨T, hS⟩) (S' := ⟨extOp T, hS'⟩) rfl y = extDetFirst hS y :=
  DFunLike.congr_fun (linDetEquivOfEq_self
    ((extOp T : E × (Fin 1 → ℝ) →L[ℝ] F) : E × (Fin 1 → ℝ) →ₗ[ℝ] F) rfl) (extDetFirst hS y)

omit [CompleteSpace E] [CompleteSpace F] in
/-- On rays, `extDetFirstFiber⁻¹ = (−1)^{ind S} · extDetFiber⁻¹`. -/
theorem ray_map_extDetFirstFiber_symm {S : FredholmOp E F}
    {S' : FredholmOp (E × (Fin 1 → ℝ)) F} (h : S'.1 = extOp S.1) (r : Module.Ray ℝ (DetFiber S')) :
    Module.Ray.map (extDetFirstFiber h).symm r =
      (indSign S.1)⁻¹ • Module.Ray.map (extDetFiber h).symm r := by
  induction r using Module.Ray.ind with
  | h w hw =>
    rw [Module.Ray.map_apply, Module.Ray.map_apply, smul_rayOfNeZero]
    congr 1
    apply (extDetFirstFiber h).injective
    rw [LinearEquiv.apply_symm_apply, extDetFirstFiber_apply, Units.smul_def,
      LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, smul_smul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_smul]

/-- **The pulled-back rays with the 2021 map**: `L ↦ h(L)` with `e ∧ h(L) = o'(L̃)`, i.e.
`extDetFirst⁻¹ (o'(L̃))`. -/
def extPullRayFirst (hmem : ∀ S ∈ C, extOp S ∈ C') (o' : ∀ b, Module.Ray ℝ (DetOn C' hC' b))
    (b : C) : Module.Ray ℝ (DetOn C hC b) :=
  Module.Ray.map (extDetFirstFiber (S := fredholmIncl hC b)
    (S' := fredholmIncl hC' (extMap hmem b)) rfl).symm (o' (extMap hmem b))

omit [CompleteSpace E] [CompleteSpace F] in
/-- The 2021 pull-back is the pull-back of `ProductOrientation.lean` times `(−1)^{ind L}`. -/
theorem extPullRayFirst_eq (hmem : ∀ S ∈ C, extOp S ∈ C')
    (o' : ∀ b, Module.Ray ℝ (DetOn C' hC' b)) (b : C) :
    extPullRayFirst (hC := hC) hmem o' b =
      (indSign (b : E →L[ℝ] F))⁻¹ • extPullRay (hC := hC) hmem o' b :=
  ray_map_extDetFirstFiber_symm _ _

/-- **`isLineOrientation_extPull` with the 2021 map**: for any set `C` of Fredholm operators with
`L̃ ∈ C'` for `L ∈ C`, the rays `L ↦ extDetFirst⁻¹ (o'(L̃))` form an orientation of `DET` over
`C`.  *Proof*: they are `(−1)^{ind L}` times the rays of `isLineOrientation_extPull`, and the
index is locally constant (`eventually_indSign_eq`, `IsLineOrientation.units_smul`). -/
theorem isLineOrientation_extPullFirst (hmem : ∀ S ∈ C, extOp S ∈ C')
    (o' : LineOrientation (DetOn C' hC')) :
    IsLineOrientation (DetOn C hC) (extPullRayFirst hmem o'.1) := by
  have h := (isLineOrientation_extPull (hC := hC) hmem o').units_smul
    (u := fun b : C => (indSign (b : E →L[ℝ] F))⁻¹) fun b₀ => by
      have := continuous_subtype_val.continuousAt.eventually
        (eventually_indSign_eq (hC _ b₀.2))
      exact this.mono fun b hb => by simp only [hb]
  have he : extPullRayFirst (hC := hC) hmem o'.1 =
      fun b : C => (indSign (b : E →L[ℝ] F))⁻¹ • extPullRay (hC := hC) hmem o'.1 b :=
    funext fun b => extPullRayFirst_eq hmem o'.1 b
  rw [he]
  exact h

/-- **The 2021 pulled-back orientation** of `DET` over `C`: `L ↦ extDetFirst⁻¹ (o'(L̃))`. -/
def LineOrientation.extPullFirst (hmem : ∀ S ∈ C, extOp S ∈ C')
    (o' : LineOrientation (DetOn C' hC')) : LineOrientation (DetOn C hC) :=
  ⟨extPullRayFirst hmem o'.1, isLineOrientation_extPullFirst hmem o'⟩

/-- `o'.extPullFirst` at `L` is `extDetFirst⁻¹ (o'(L̃))`. -/
theorem LineOrientation.extPullFirst_apply (hmem : ∀ S ∈ C, extOp S ∈ C')
    (o' : LineOrientation (DetOn C' hC')) {S : E →L[ℝ] F} (hS : S ∈ C) :
    o'.extPullFirst (hC := hC) hmem ⟨S, hS⟩ =
      Module.Ray.map (extDetFirstFiber (S := ⟨S, hC S hS⟩)
        (S' := ⟨extOp S, hC' _ (hmem S hS)⟩) rfl).symm (o' ⟨extOp S, hmem S hS⟩) :=
  rfl

/-- **Multiplying an orientation by `(−1)^{ind L}`** gives an orientation (the index is locally
constant). -/
def LineOrientation.indSignSmul (o : LineOrientation (DetOn C hC)) :
    LineOrientation (DetOn C hC) :=
  ⟨fun b => indSign (b : E →L[ℝ] F) • o b, o.2.units_smul fun b₀ =>
    (continuous_subtype_val.continuousAt.eventually (eventually_indSign_eq (hC _ b₀.2)))⟩

theorem LineOrientation.indSignSmul_apply (o : LineOrientation (DetOn C hC)) (b : C) :
    o.indSignSmul b = indSign (b : E →L[ℝ] F) • o b :=
  rfl

end ExtPullFirst

/-! ### The 2021 map after the swap of the factors -/

section ExtConjFirst

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  (A : E' ≃L[ℝ] E × (Fin 1 → ℝ)) (Γ : F' ≃L[ℝ] F)

/-- **The determinant isomorphism `h ↦ h̃ = e ∧ h` of 2021 Remark 6.6.19**, `det(L) ≅ det(L̂)`:
`extDetFirst` followed by the conjugation `det(L ⊕ 0) ≅ det(L̂)` (`conjDet`). -/
def extConjDetFirst {L : E →L[ℝ] F} (hL : L.IsFredholm) (hL' : (extConjOp A Γ L).IsFredholm) :
    DetFiber (⟨L, hL⟩ : FredholmOp E F) ≃ₗ[ℝ]
      DetFiber (⟨extConjOp A Γ L, hL'⟩ : FredholmOp E' F') :=
  (extDetFirstFiber (S := ⟨L, hL⟩) (S' := ⟨extOp L, isFredholm_extOp hL⟩) rfl).trans
    (conjDetFiber (S := ⟨extConjOp A Γ L, hL'⟩) (S' := ⟨extOp L, isFredholm_extOp hL⟩) A Γ
      (extConjOp_conj A Γ L)).symm

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- `extConjDetFirst = conjDet⁻¹ ∘ extDetFirst`. -/
theorem extConjDetFirst_apply {L : E →L[ℝ] F} (hL : L.IsFredholm)
    (hL' : (extConjOp A Γ L).IsFredholm) (y : fredholmDet L) :
    extConjDetFirst A Γ hL hL' y =
      (conjDet A Γ (extConjOp_conj A Γ L)).symm (extDetFirst hL y) :=
  congrArg (conjDetFiber (S := ⟨extConjOp A Γ L, hL'⟩) (S' := ⟨extOp L, isFredholm_extOp hL⟩) A Γ
    (extConjOp_conj A Γ L)).symm (extDetFirstFiber_rfl_apply hL _ y)

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- **`extConjDetFirst` on generators is the text's `h ↦ h̃`**: for
`h = (a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*` the image is the conjugate of
`(e ∧ (a₁, 0) ∧ … ∧ (aₙ, 0)) ⊗ (d₁ ∧ … ∧ d_l)*`, `e = (0, 1)`, with no sign. -/
theorem extConjDetFirst_wedge_tmul {L : E →L[ℝ] F} (hL : L.IsFredholm)
    (hL' : (extConjOp A Γ L).IsFredholm) {n l : ℕ}
    (a : Fin n → LinearMap.ker (L : E →ₗ[ℝ] F))
    (hn : n = finrank ℝ (LinearMap.ker (L : E →ₗ[ℝ] F)))
    {d : Fin l → F ⧸ LinearMap.range (L : E →ₗ[ℝ] F)} (hd : LinearIndependent ℝ d)
    (hl : l = finrank ℝ (F ⧸ LinearMap.range (L : E →ₗ[ℝ] F))) :
    extConjDetFirst A Γ hL hL' (wedge a hn ⊗ₜ dualVec (wedge d hl)) =
      (conjDet A Γ (extConjOp_conj A Γ L)).symm
        (wedge (Fin.cons (α := fun _ => LinearMap.ker (extOp L : E × (Fin 1 → ℝ) →ₗ[ℝ] F))
            (extE L) (stabJ L 0 ∘ a)) (by rw [hn]; exact finrank_ker_extOp hL) ⊗ₜ
          dualVec (wedge ((extCoker L).symm ∘ d) (hl.trans (extCoker L).symm.finrank_eq))) := by
  rw [extConjDetFirst_apply, extDetFirst_wedge_tmul hL a hn hd hl]

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- **`extConjDetFirst = (−1)^{ind L} · extConjDet`**. -/
theorem extConjDetFirst_eq_indSign_smul {L : E →L[ℝ] F} (hL : L.IsFredholm)
    (hL' : (extConjOp A Γ L).IsFredholm) (y : fredholmDet L) :
    extConjDetFirst A Γ hL hL' y = ((indSign L : ℝˣ) : ℝ) • extConjDet A Γ hL hL' y := by
  rw [extConjDetFirst_apply, extConjDet_apply, extDetFirst_eq_indSign_smul_extDetN]
  exact LinearEquiv.map_smul _ _ _

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- `extConjDetFirst = ε · extConjDet` for `ε = (−1)^i`, `i = ind L`. -/
theorem extConjDetFirst_eq_zpow_smul {L : E →L[ℝ] F} (hL : L.IsFredholm)
    (hL' : (extConjOp A Γ L).IsFredholm) {i : ℤ} (hi : fredholmIndex L = i) (y : fredholmDet L) :
    extConjDetFirst A Γ hL hL' y = (((-1 : ℝˣ) ^ i : ℝˣ) : ℝ) • extConjDet A Γ hL hL' y := by
  have hs : indSign L = (-1) ^ i := by rw [indSign, hi]
  rw [extConjDetFirst_eq_indSign_smul, hs]

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- On rays: `extConjDetFirst(r) = extConjDet((−1)^{ind L} r)`. -/
theorem ray_map_extConjDetFirst {L : E →L[ℝ] F} (hL : L.IsFredholm)
    (hL' : (extConjOp A Γ L).IsFredholm) (r : Module.Ray ℝ (DetFiber ⟨L, hL⟩)) :
    Module.Ray.map (extConjDetFirst A Γ hL hL') r =
      Module.Ray.map (extConjDet A Γ hL hL') (indSign L • r) := by
  induction r using Module.Ray.ind with
  | h w hw =>
    rw [smul_rayOfNeZero, Module.Ray.map_apply, Module.Ray.map_apply]
    congr 1
    refine (extConjDetFirst_eq_indSign_smul A Γ hL hL' w).trans ?_
    rw [Units.smul_def]
    exact (LinearEquiv.map_smul _ _ _).symm

/-- **One orientation for all `L̂`, with the 2021 map**: for a preconnected `C` and a simply
connected, locally path-connected `Ĉ` with `L̂ ∈ Ĉ` for `L ∈ C`, an orientation `o` of `DET`
over a nonempty `C` gives exactly one orientation `ô` over `Ĉ` with `ô(L̂) = extConjDetFirst(o(L))`
for every `L ∈ C`.  *Proof*: `existsUnique_extConjOr` for the orientation `(−1)^{ind L} o`
(`LineOrientation.indSignSmul`). -/
theorem existsUnique_extConjOrFirst {C : Set (E →L[ℝ] F)} (hC : ∀ T ∈ C, T.IsFredholm)
    {Ĉ : Set (E' →L[ℝ] F')} (hĈ : ∀ T ∈ Ĉ, T.IsFredholm)
    (hmem : ∀ L ∈ C, extConjOp A Γ L ∈ Ĉ) [PreconnectedSpace C] [SimplyConnectedSpace Ĉ]
    [LocallyPathConnectedSpace Ĉ] (hne : C.Nonempty) (o : LineOrientation (DetOn C hC)) :
    ∃! ô : LineOrientation (DetOn Ĉ hĈ), ∀ (L : E →L[ℝ] F) (hL : L ∈ C),
      ô ⟨extConjOp A Γ L, hmem L hL⟩ =
        Module.Ray.map (extConjDetFirst A Γ (hC L hL) (hĈ _ (hmem L hL))) (o ⟨L, hL⟩) := by
  obtain ⟨ô, hô, huniq⟩ := existsUnique_extConjOr A Γ hC hĈ hmem hne o.indSignSmul
  have key : ∀ (L : E →L[ℝ] F) (hL : L ∈ C),
      Module.Ray.map (extConjDet A Γ (hC L hL) (hĈ _ (hmem L hL))) (o.indSignSmul ⟨L, hL⟩) =
        Module.Ray.map (extConjDetFirst A Γ (hC L hL) (hĈ _ (hmem L hL))) (o ⟨L, hL⟩) :=
    fun L hL => (ray_map_extConjDetFirst A Γ (hC L hL) _ _).symm
  exact ⟨ô, fun L hL => (hô L hL).trans (key L hL),
    fun ô' hô' => huniq ô' fun L hL => (hô' L hL).trans (key L hL).symm⟩

end ExtConjFirst

/-! ### 2021 Remark 6.6.19 in a chart point -/

section ProdOrFirst

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (t : Fin 1 → ℝ)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- **2021 Remark 6.6.19: the natural orientation of `f̂ = f̃ + S`** at `(t, x)`, with the 2021
convention `h̃ = e ∧ h`, read in the product chart point `prodPt`.  For an sc-Fredholm `f`, an
sc⁺-section `S` of `π*P` over `ℝ¹ × X`, a smooth point `x` with `Lin(f, x)` nonempty and an
orientation `o` of `DET(f, x)`, there is exactly one orientation `ô` of `DET(f̂, (t, x))` with
`ô(L̂) = extConjDetFirst(o(L))` for **every** `L ∈ Lin(f, x)`: the orientation `h̃ = e ∧ h` of
`det(L̂)` orients `DET(f̂, (t, x))`, independently of the choice of `L`. -/
theorem existsUnique_prodOrFirst (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) :
    ∃! ô : (p.prodPt t q₀).Or
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
        (theorem_3_15 hf.param hS),
      ∀ (L : ↥p.T →L[ℝ] ↥p.K) (hL : L ∈ p.linSet f),
        ô ⟨p.prodLin t q₀ L, p.prodLin_mem_linSet t q₀ hf hx hS hL⟩ =
          Module.Ray.map (extConjDetFirst (p.prodT t q₀) (p.prodK t q₀)
            (p.isFredholm_of_mem_linSet hf L hL)
            ((p.prodPt t q₀).isFredholm_of_mem_linSet (theorem_3_15 hf.param hS) _
              (p.prodLin_mem_linSet t q₀ hf hx hS hL))) (o ⟨L, hL⟩) := by
  obtain ⟨L₀, hL₀⟩ := hne
  have : PreconnectedSpace (p.linSet f) :=
    isPreconnected_iff_preconnectedSpace.1 (p.convex_linSet hf).isPreconnected
  have : ContractibleSpace ((p.prodPt t q₀).linSet
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)) :=
    ((p.prodPt t q₀).convex_linSet (theorem_3_15 hf.param hS)).contractibleSpace
      ⟨_, p.prodLin_mem_linSet t q₀ hf hx hS hL₀⟩
  have : LocallyPathConnectedSpace ((p.prodPt t q₀).linSet
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)) :=
    ((p.prodPt t q₀).convex_linSet (theorem_3_15 hf.param hS)).locallyPathConnectedSpace
  exact existsUnique_extConjOrFirst (p.prodT t q₀) (p.prodK t q₀) (p.isFredholm_of_mem_linSet hf)
    ((p.prodPt t q₀).isFredholm_of_mem_linSet (theorem_3_15 hf.param hS))
    (fun L hL => p.prodLin_mem_linSet t q₀ hf hx hS hL) ⟨L₀, hL₀⟩ o

/-- **The product orientation of 2021 Remark 6.6.19** at `(t, x)` (`e` first): the orientation
`ô` of `DET(f̂, (t, x))` determined by `o` (`existsUnique_prodOrFirst`). -/
def prodOrFirst (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) :
    (p.prodPt t q₀).Or (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
      (theorem_3_15 hf.param hS) :=
  (p.existsUnique_prodOrFirst t q₀ hf hx hS hne o).exists.choose

/-- **`prodOrFirst` at `L̂`** is `h ↦ h̃ = e ∧ h` (`extConjDetFirst`) of `o(L)`, for every
`L ∈ Lin(f, x)`. -/
theorem prodOrFirst_apply (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) (L : ↥p.T →L[ℝ] ↥p.K)
    (hL : L ∈ p.linSet f) :
    p.prodOrFirst t q₀ hf hx hS hne o ⟨p.prodLin t q₀ L, p.prodLin_mem_linSet t q₀ hf hx hS hL⟩ =
      Module.Ray.map (extConjDetFirst (p.prodT t q₀) (p.prodK t q₀)
        (p.isFredholm_of_mem_linSet hf L hL)
        ((p.prodPt t q₀).isFredholm_of_mem_linSet (theorem_3_15 hf.param hS) _
          (p.prodLin_mem_linSet t q₀ hf hx hS hL))) (o ⟨L, hL⟩) :=
  (p.existsUnique_prodOrFirst t q₀ hf hx hS hne o).exists.choose_spec L hL

/-- **On `Lin(f, x)` the 2021 map is the map of `ProductOrientation.lean` times one constant
sign**: there is `ε = ±1` (`ε = (−1)^{ind(f, x)}`, `exists_index_linSet`) with
`extConjDetFirst = ε · extConjDet` at every `L ∈ Lin(f, x)`. -/
theorem exists_extConjDetFirst_eq_sign_smul (hf : B.IsScFredholmSection f)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hx : x ∈ PX.smoothSet) :
    ∃ ε : ℝˣ, (ε = 1 ∨ ε = -1) ∧ ∀ (L : ↥p.T →L[ℝ] ↥p.K) (hL : L ∈ p.linSet f) y,
      extConjDetFirst (p.prodT t q₀) (p.prodK t q₀) (p.isFredholm_of_mem_linSet hf L hL)
          ((p.prodPt t q₀).isFredholm_of_mem_linSet (theorem_3_15 hf.param hS) _
            (p.prodLin_mem_linSet t q₀ hf hx hS hL)) y =
        (ε : ℝ) • extConjDet (p.prodT t q₀) (p.prodK t q₀) (p.isFredholm_of_mem_linSet hf L hL)
          ((p.prodPt t q₀).isFredholm_of_mem_linSet (theorem_3_15 hf.param hS) _
            (p.prodLin_mem_linSet t q₀ hf hx hS hL)) y := by
  have hidx := p.exists_index_linSet hf
  obtain ⟨i, hi⟩ := hidx
  refine ⟨(-1) ^ i, ?_, fun L hL y => ?_⟩
  · rcases Int.even_or_odd i with h | h
    · exact Or.inl (h.neg_one_zpow)
    · exact Or.inr (h.neg_one_zpow)
  · exact extConjDetFirst_eq_zpow_smul (p.prodT t q₀) (p.prodK t q₀)
      (p.isFredholm_of_mem_linSet hf L hL)
      ((p.prodPt t q₀).isFredholm_of_mem_linSet (theorem_3_15 hf.param hS) _
        (p.prodLin_mem_linSet t q₀ hf hx hS hL)) (hi L hL).2 y

end ChartPoint

end ProdOrFirst

end Polyfold
