import Polyfold.Chapter6.DetNonOrientableHilbert
import Polyfold.Chapter6.ProductOrientation
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), the end of §6.5 (p. 262;
preprint p. 219): the remark that **the line bundle `DET(E, F)` is non-orientable**.  Gap G.60,
transport along isomorphisms of `E` and `F`.

# Orientability of `DET(E, F)` depends only on the isomorphism classes of `E` and `F`

## What is formalized

* `IsLineOrientation.pullback`: an orientation of a line bundle gives one of every pull-back.
* `detOnFredholmOfDet`, `detOfDetOnFredholm`: the orientations of `DET(E, F)` and of its
  restriction `DetOn` to the set of all Fredholm operators correspond.
* `nonempty_lineOrientation_det_of_equiv`: for isomorphisms `A : E ≅ E'`, `Γ : F ≅ F'`, an
  orientation of `DET(E, F)` gives one of `DET(E', F')` (`LineOrientation.conj` of
  `ChartTransfer.lean`: the fibres are identified by `conjDet`);
  `nonempty_lineOrientation_det_iff_of_equiv`, `isEmpty_lineOrientation_det_of_equiv`.
* `isEmpty_lineOrientation_det_of_equiv_prod`: `DET(E, F)` has no orientation when `E` and `F`
  are isomorphic to `H × H`, for a Banach space `H` with a surjective `S : H → H` whose kernel
  has odd finite dimension.
* `isEmpty_lineOrientation_det_of_equiv_ellTwo`: `DET(E, F)` has no orientation when `E` and `F`
  are isomorphic to `ℓ² × ℓ²`.
* `wcomp`: the weighted composition operators `x ↦ (s_i x_{g(i)})_i` of `ℓ²(ι)` for injective
  `g` and `|s| ≤ 1`.  For an infinite index set they give a complex structure
  (`exists_complexStructure_ltwo`) and a surjective operator with one-dimensional kernel
  (`exists_shift_ltwo`), hence `isEmpty_lineOrientation_det_ltwo`: `DET(ℓ²(ι), ℓ²(ι))` has no
  orientation for every infinite `ι`.
* **`isEmpty_lineOrientation_det_hilbert`**: `DET(H, H)` has no orientation for every
  infinite-dimensional real Hilbert space `H` (separable or not; a Hilbert basis identifies `H`
  with `ℓ²(ι)`).  `isEmpty_lineOrientation_det_of_equiv_hilbert`: the same for `DET(E, F)` when
  the Banach spaces `E` and `F` are isomorphic to one infinite-dimensional Hilbert space.
-/

open Module Bundle Topology Set
open scoped ENNReal Cardinal

noncomputable section

namespace Polyfold

/-! ### Pull-backs of orientations -/

section Pullback

variable {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B'] {L : B → Type*}
  [∀ b, AddCommMonoid (L b)] [∀ b, Module ℝ (L b)] [TopologicalSpace (TotalSpace ℝ L)]

/-- **An orientation of a line bundle gives an orientation of every pull-back.** -/
theorem IsLineOrientation.pullback {o : ∀ b, Module.Ray ℝ (L b)} (ho : IsLineOrientation L o)
    {f : B' → B} (hf : Continuous f) :
    IsLineOrientation (f *ᵖ L) fun b' => o (f b') := by
  intro b₀
  obtain ⟨U, hU, σ, hσ, hσo⟩ := ho (f b₀)
  refine ⟨f ⁻¹' U, hf.continuousAt.preimage_mem_nhds hU, fun b' => σ (f b'), ?_,
    fun b' hb' => hσo (f b') hb'⟩
  rw [(inducing_pullbackTotalSpaceEmbedding ℝ L f).continuousOn_iff]
  exact continuousOn_id.prodMk (hσ.comp hf.continuousOn fun _ h => h)

end Pullback

section Transport

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']

variable (E F) in
/-- The set of all Fredholm operators `E → F`. -/
def fredholmSet : Set (E →L[ℝ] F) := {T | T.IsFredholm}

omit [CompleteSpace E] [CompleteSpace F] in
theorem isFredholm_of_mem_fredholmSet : ∀ T ∈ fredholmSet E F, T.IsFredholm := fun _ h => h

/-- An orientation of `DET(E, F)` restricts to the set of all Fredholm operators. -/
def detOnFredholmOfDet (o : LineOrientation (DetFiber (E := E) (F := F))) :
    LineOrientation (DetOn (fredholmSet E F) isFredholm_of_mem_fredholmSet) :=
  ⟨fun b => o (fredholmIncl isFredholm_of_mem_fredholmSet b),
    o.2.pullback (fredholmIncl isFredholm_of_mem_fredholmSet).continuous⟩

/-- An orientation of `DET` over the set of all Fredholm operators is one of `DET(E, F)`. -/
def detOfDetOnFredholm
    (o : LineOrientation (DetOn (fredholmSet E F) isFredholm_of_mem_fredholmSet)) :
    LineOrientation (DetFiber (E := E) (F := F)) :=
  ⟨fun b => o.1 ⟨b.1, b.2⟩, fun b₀ => by
    obtain ⟨U, hU, σ, hσ, hσo⟩ := o.2 ⟨b₀.1, b₀.2⟩
    exact ⟨U, hU, σ, (Pullback.continuous_lift ℝ (DetFiber (E := E) (F := F))
      (fredholmIncl (isFredholm_of_mem_fredholmSet (E := E) (F := F)))).comp_continuousOn hσ,
      hσo⟩⟩

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- `Γ⁻¹ S' A` is Fredholm when `S'` is. -/
theorem isFredholm_conj_symm (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F') {S' : E' →L[ℝ] F'}
    (hS' : S'.IsFredholm) :
    ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')).IsFredholm := by
  refine isFredholm_of_conj A.symm Γ.symm ?_
  have h : ((Γ.symm.symm : F →L[ℝ] F') ∘L ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∘L
      (A.symm : E' →L[ℝ] E)) = S' := by
    ext v
    simp
  rw [h]
  exact hS'

/-- **Transport of orientations of `DET` along isomorphisms**: for `A : E ≅ E'`, `Γ : F ≅ F'`,
an orientation of `DET(E, F)` gives one of `DET(E', F')`, by `det(Γ⁻¹ S' A) ≅ det(S')`. -/
theorem nonempty_lineOrientation_det_of_equiv (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F')
    (h : Nonempty (LineOrientation (DetFiber (E := E) (F := F)))) :
    Nonempty (LineOrientation (DetFiber (E := E') (F := F'))) := by
  obtain ⟨o⟩ := h
  exact ⟨detOfDetOnFredholm ((detOnFredholmOfDet o).conj A Γ
    (C' := fredholmSet E' F') (hC' := isFredholm_of_mem_fredholmSet)
    fun S' hS' => isFredholm_conj_symm A Γ hS')⟩

/-- Orientability of `DET(E, F)` depends only on the isomorphism classes of `E` and `F`. -/
theorem nonempty_lineOrientation_det_iff_of_equiv (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F') :
    Nonempty (LineOrientation (DetFiber (E := E) (F := F))) ↔
      Nonempty (LineOrientation (DetFiber (E := E') (F := F'))) :=
  ⟨nonempty_lineOrientation_det_of_equiv A Γ,
    nonempty_lineOrientation_det_of_equiv A.symm Γ.symm⟩

/-- If `DET(E, F)` has no orientation, neither has `DET(E', F')` for `E' ≅ E`, `F' ≅ F`. -/
theorem isEmpty_lineOrientation_det_of_equiv (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F')
    (h : IsEmpty (LineOrientation (DetFiber (E := E) (F := F)))) :
    IsEmpty (LineOrientation (DetFiber (E := E') (F := F'))) :=
  not_nonempty_iff.1 fun h' =>
    not_nonempty_iff.2 h (nonempty_lineOrientation_det_of_equiv A.symm Γ.symm h')

end Transport

section Instances

variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- **(2021, p. 262) `DET(E, F)` is not orientable** when `E` and `F` are isomorphic to `H × H`
for a Banach space `H` with a surjective `S : H → H` whose kernel has odd finite dimension. -/
theorem isEmpty_lineOrientation_det_of_equiv_prod (A : (H × H) ≃L[ℝ] E) (Γ : (H × H) ≃L[ℝ] F)
    {S : H →L[ℝ] H} (hS : Function.Surjective S)
    [FiniteDimensional ℝ (LinearMap.ker (S : H →ₗ[ℝ] H))]
    (hodd : Odd (finrank ℝ (LinearMap.ker (S : H →ₗ[ℝ] H)))) :
    IsEmpty (LineOrientation (DetFiber (E := E) (F := F))) :=
  isEmpty_lineOrientation_det_of_equiv A Γ (isEmpty_lineOrientation_det_prod hS hodd)

/-- **(2021, p. 262) `DET(E, F)` is not orientable** when `E` and `F` are isomorphic to
`ℓ² × ℓ²`. -/
theorem isEmpty_lineOrientation_det_of_equiv_ellTwo (A : (EllTwo × EllTwo) ≃L[ℝ] E)
    (Γ : (EllTwo × EllTwo) ≃L[ℝ] F) :
    IsEmpty (LineOrientation (DetFiber (E := E) (F := F))) :=
  isEmpty_lineOrientation_det_of_equiv A Γ isEmpty_lineOrientation_det_ellTwo

end Instances

/-! ### `ℓ²(ι)` for an infinite index set, and Hilbert spaces -/

section LTwo

variable {ι : Type*}

/-- `ℓ²(ι) = ℓ²(ι, ℝ)`. -/
abbrev LTwo (ι : Type*) : Type _ := lp (fun _ : ι => ℝ) 2

theorem norm_mul_rpow_le {s : ι → ℝ} (hs : ∀ i, |s i| ≤ 1) (g : ι → ι) (x : LTwo ι) (i : ι) :
    ‖s i * x (g i)‖ ^ (2 : ℝ≥0∞).toReal ≤ ‖x (g i)‖ ^ (2 : ℝ≥0∞).toReal := by
  refine Real.rpow_le_rpow (norm_nonneg _) ?_ ellTwo_toReal_pos.le
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hs i)

/-- `(s_i x_{g(i)})_i` is in `ℓ²` for injective `g` and `|s| ≤ 1`. -/
theorem memℓp_wcomp {g : ι → ι} (hg : Function.Injective g) {s : ι → ℝ} (hs : ∀ i, |s i| ≤ 1)
    (x : LTwo ι) : Memℓp (fun i => s i * x (g i)) 2 :=
  memℓp_gen (Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (norm_mul_rpow_le hs g x) (((lp.memℓp x).summable ellTwo_toReal_pos).comp_injective hg))

/-- The weighted composition operator as a linear map. -/
def wcompₗ {g : ι → ι} (hg : Function.Injective g) {s : ι → ℝ} (hs : ∀ i, |s i| ≤ 1) :
    LTwo ι →ₗ[ℝ] LTwo ι where
  toFun x := ⟨fun i => s i * x (g i), memℓp_wcomp hg hs x⟩
  map_add' x y := lp.ext (funext fun i => by
    change s i * (x + y) (g i) = s i * x (g i) + s i * y (g i)
    rw [lp.coeFn_add, Pi.add_apply, mul_add])
  map_smul' c x := lp.ext (funext fun i => by
    change s i * (c • x) (g i) = c * (s i * x (g i))
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring)

theorem norm_wcompₗ_le {g : ι → ι} (hg : Function.Injective g) {s : ι → ℝ}
    (hs : ∀ i, |s i| ≤ 1) (x : LTwo ι) : ‖wcompₗ hg hs x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  refine lp.norm_le_of_forall_sum_le ellTwo_toReal_pos (norm_nonneg x) fun t => ?_
  have h := lp.sum_rpow_le_norm_rpow ellTwo_toReal_pos x (t.map ⟨g, hg⟩)
  rw [Finset.sum_map] at h
  exact (Finset.sum_le_sum fun i _ => norm_mul_rpow_le hs g x i).trans h

/-- **The weighted composition operator** `x ↦ (s_i x_{g(i)})_i` of `ℓ²(ι)`. -/
def wcomp {g : ι → ι} (hg : Function.Injective g) {s : ι → ℝ} (hs : ∀ i, |s i| ≤ 1) :
    LTwo ι →L[ℝ] LTwo ι :=
  (wcompₗ hg hs).mkContinuous 1 (norm_wcompₗ_le hg hs)

theorem wcomp_apply {g : ι → ι} (hg : Function.Injective g) {s : ι → ℝ} (hs : ∀ i, |s i| ≤ 1)
    (x : LTwo ι) (i : ι) : wcomp hg hs x i = s i * x (g i) := rfl

/-- **A complex structure on `ℓ²(ι)`** for infinite `ι`: split `ι` into two copies of itself
and rotate. -/
theorem exists_complexStructure_ltwo [Infinite ι] :
    ∃ J : LTwo ι →L[ℝ] LTwo ι, ∀ x, J (J x) = -x := by
  have hc : #ι = #(ι ⊕ ι) := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.add_eq_self (Cardinal.aleph0_le_mk ι)]
  obtain ⟨u⟩ := Cardinal.eq.1 hc
  let τ : ι → ι := fun i => u.symm (u i).swap
  let s : ι → ℝ := fun i => if (u i).isLeft then 1 else -1
  have hτ : Function.Injective τ := fun i j h =>
    u.injective (Sum.swap_rightInverse.injective (u.symm.injective h))
  have hττ : ∀ i, τ (τ i) = i := fun i => by simp [τ]
  have hs : ∀ i, |s i| ≤ 1 := fun i => by
    by_cases h : (u i).isLeft <;> simp [s, h]
  have hss : ∀ i, s i * s (τ i) = -1 := fun i => by
    rcases h : u i with a | b <;> simp [s, τ, h]
  refine ⟨wcomp hτ hs, fun x => lp.ext (funext fun i => ?_)⟩
  change s i * (s (τ i) * x (τ (τ i))) = (-x) i
  rw [lp.coeFn_neg, Pi.neg_apply, hττ, ← mul_assoc, hss, neg_one_mul]

/-- **A surjective operator on `ℓ²(ι)` with one-dimensional kernel** for infinite `ι`: the shift
along an injection `ι → ι` that misses exactly one point. -/
theorem exists_shift_ltwo [Infinite ι] :
    ∃ T : LTwo ι →L[ℝ] LTwo ι, Function.Surjective T ∧
      Nonempty (LinearMap.ker (T : LTwo ι →ₗ[ℝ] LTwo ι) ≃ₗ[ℝ] ℝ) := by
  classical
  have hc : #(Option ι) = #ι := by
    rw [Cardinal.mk_option, Cardinal.add_one_eq (Cardinal.aleph0_le_mk ι)]
  obtain ⟨e⟩ := Cardinal.eq.1 hc
  let f : ι → ι := fun i => e (some i)
  have hf : Function.Injective f := fun i j h => Option.some_injective _ (e.injective h)
  have hne : ∀ i, f i ≠ e none := fun i h => by simpa using e.injective h
  have hex : ∀ j, j ≠ e none → ∃ i, f i = j := fun j hj => by
    rcases h : e.symm j with _ | i
    · exact absurd ((e.symm_apply_eq.1 h)) hj
    · exact ⟨i, (e.symm_apply_eq.1 h).symm⟩
  have h1 : ∀ i : ι, |(1 : ℝ)| ≤ 1 := fun _ => by simp
  set T := wcomp hf h1 with hT
  have hTapp : ∀ x i, T x i = x (f i) := fun x i => one_mul _
  refine ⟨T, fun y => ?_, ?_⟩
  · have hmem : Memℓp (Function.extend f y 0) 2 := by
      refine memℓp_gen ((hf.summable_iff fun j hj => ?_).1 ?_)
      · rw [Function.extend_apply' _ _ _ (by simpa using hj)]
        simp
      · have h := (lp.memℓp y).summable ellTwo_toReal_pos
        refine h.congr fun i => ?_
        simp [hf.extend_apply]
    refine ⟨⟨_, hmem⟩, lp.ext (funext fun i => ?_)⟩
    rw [hTapp]
    exact hf.extend_apply _ _ i
  · let φ : LinearMap.ker (T : LTwo ι →ₗ[ℝ] LTwo ι) →ₗ[ℝ] ℝ :=
      { toFun := fun x => (x : LTwo ι) (e none)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine ⟨LinearEquiv.ofBijective φ ⟨?_, fun t => ?_⟩⟩
    · refine (injective_iff_map_eq_zero φ).2 fun x hx => Subtype.ext (lp.ext (funext fun j => ?_))
      by_cases hj : j = e none
      · rw [hj]
        exact hx
      · obtain ⟨i, rfl⟩ := hex j hj
        have hx0 : T (x : LTwo ι) = 0 := x.2
        have := congrArg (fun z : LTwo ι => z i) hx0
        rw [← hTapp]
        exact this
    · refine ⟨⟨lp.single 2 (e none) t, lp.ext (funext fun i => ?_)⟩, ?_⟩
      · change T (lp.single 2 (e none) t) i = 0
        rw [hTapp]
        exact lp.single_apply_ne (E := fun _ : ι => ℝ) 2 (e none) t (hne i)
      · exact lp.single_apply_self (E := fun _ : ι => ℝ) 2 (e none) t

/-- **(2021, p. 262) `DET(ℓ²(ι), ℓ²(ι))` is not orientable** for every infinite index set
`ι`. -/
theorem isEmpty_lineOrientation_det_ltwo [Infinite ι] :
    IsEmpty (LineOrientation (DetFiber (E := LTwo ι) (F := LTwo ι))) := by
  obtain ⟨J, hJ⟩ := exists_complexStructure_ltwo (ι := ι)
  obtain ⟨T, hT, ⟨φ⟩⟩ := exists_shift_ltwo (ι := ι)
  have : FiniteDimensional ℝ (LinearMap.ker (T : LTwo ι →ₗ[ℝ] LTwo ι)) :=
    φ.symm.finiteDimensional
  refine isEmpty_lineOrientation_det_of_complexStructure hJ hJ hT ?_
  rw [φ.finrank_eq, Module.finrank_self]
  exact odd_one

end LTwo

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **(2021, p. 262) `DET(H, H)` is not orientable for every infinite-dimensional real Hilbert
space `H`.** -/
theorem isEmpty_lineOrientation_det_hilbert (hH : ¬ FiniteDimensional ℝ H) :
    IsEmpty (LineOrientation (DetFiber (E := H) (F := H))) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ H
  have : Infinite w := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    have := Fintype.ofFinite w
    exact hH (Module.Finite.of_basis b.toOrthonormalBasis.toBasis)
  exact isEmpty_lineOrientation_det_of_equiv b.repr.symm.toContinuousLinearEquiv
    b.repr.symm.toContinuousLinearEquiv isEmpty_lineOrientation_det_ltwo

/-- **(2021, p. 262) `DET(E, F)` is not orientable** when the Banach spaces `E` and `F` are
isomorphic to one infinite-dimensional real Hilbert space `H`. -/
theorem isEmpty_lineOrientation_det_of_equiv_hilbert {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (hH : ¬ FiniteDimensional ℝ H) (A : H ≃L[ℝ] E) (Γ : H ≃L[ℝ] F) :
    IsEmpty (LineOrientation (DetFiber (E := E) (F := F))) :=
  isEmpty_lineOrientation_det_of_equiv A Γ (isEmpty_lineOrientation_det_hilbert hH)

end Hilbert

end Polyfold
