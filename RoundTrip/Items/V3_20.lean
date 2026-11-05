import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_20

/-! Round trip for V3_20 (Definition 3.21: good position, good complements).
Refreshed 2026-11-02 against HEAD (new: the text's sc good complement and its dictionary).

`A` is the conjunction of the types of the listed theorems
`Polyfold.IsInGoodPositionSc.toIsInGoodPosition`, `Polyfold.IsGoodComplement.isScGoodComplementIn`,
`Polyfold.IsInGoodPosition.isInGoodPositionSc`, `Polyfold.isScGoodComplement_iff`,
`Polyfold.isInGoodPositionSc_iff` (no universe parameters).  `IsGoodComplement`,
`IsInGoodPosition`, and (new) `IsScGoodComplement`, `IsInGoodPositionSc` (Definition 3.21 as written:
an sc-splitting `E = N ⊕ P`) are definitions.  `B` claims that the project's notions
`IsInGoodPosition`/`IsGoodComplement` (unchanged at HEAD: algebraic complement) are the text's
(`IsInGoodPositionB`, `IsGoodComplementB`), on every partial quadrant.

* **`B` is false** (`not_B`, unchanged): its second conjunct `IsGoodComplement E C N P ↔
  IsGoodComplementB E C N P` fails for a non-closed algebraic complement.  Counter-model: the
  sc-Banach space `Model.G` (`ℓ²` on every level, compact inclusions `diag(2^{-k})`, copied from
  `RoundTrip/Items/V1_29.lean`), `C = E₀`, `N = ℝ v`, `P = ker ψ` for a discontinuous linear
  functional `ψ` with `ψ(v) ≠ 0`.  Hence `A → B` is false (`not_A_to_B`), and `B → A` holds
  ex falso (`B_to_A`, through `not_B`).
* **The first conjunct of `B` is true** (`goodPosition_iff`): on a partial quadrant the project's
  good position (algebraic good complement) is equivalent to B's reading of the text (sc-complement
  for smooth `N`, closed complement otherwise).
* The corrected dictionary `IsGoodComplementB ↔ IsGoodComplement ∧ IsClosed P`
  (`isGoodComplementB_iff`, `B_corrected_holds`) is now also in the project, for the text's notion
  as written: `isScGoodComplement_iff` (for smooth `N`: good sc-complement ↔ good complement ∧
  closed) and `isInGoodPositionSc_iff` (Definition 3.21 as written ↔ project's good position ∧
  `N ⊆ E_∞`).  These new conjuncts of A do not touch B's claim about `IsGoodComplement`, which
  remains false; B's reading of the remark after Definition 3.21 (a topological complement for a
  non-smooth `N`) is not formalized in A, so `IsInGoodPositionB` agrees with the project's
  `IsInGoodPosition` (no smoothness of `N`), not with `IsInGoodPositionSc`.
-/

namespace RoundTrip.V3_20
open Polyfold Set Module


namespace Model
open Filter Topology
open scoped ENNReal

/-- `ℓ²(ℕ)`. -/
abbrev H : Type := lp (fun _ : ℕ => ℝ) 2

theorem two_ne_zero' : (2 : ℝ≥0∞) ≠ 0 := by norm_num

theorem norm_coord_le (x : H) (k : ℕ) : ‖x k‖ ≤ ‖x‖ := lp.norm_apply_le_norm two_ne_zero' x k

/-- The coordinate `x ↦ x k` as a continuous linear functional. -/
noncomputable def coord (k : ℕ) : H →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun x => x k
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp [lp.coeFn_smul] } 1
    fun x => by rw [one_mul]; exact norm_coord_le x k

@[simp] theorem coord_apply (k : ℕ) (x : H) : coord k x = x k := rfl

/-- Multiplication by a sequence bounded by `1`. -/
noncomputable def mulLin (c : ℕ → ℝ) (hc : ∀ k, |c k| ≤ 1) : H →ₗ[ℝ] H where
  toFun x := ⟨fun k => c k * x k, (lp.memℓp x).norm.mono fun k => by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hc k)⟩
  map_add' x y := lp.ext (funext fun k => by simp [mul_add]; rfl)
  map_smul' a x := lp.ext (funext fun k => by
    simp [lp.coeFn_smul]; ring)

theorem mulLin_apply (c : ℕ → ℝ) (hc : ∀ k, |c k| ≤ 1) (x : H) (k : ℕ) :
    mulLin c hc x k = c k * x k := rfl

theorem norm_le_of_coord_le {y x : H} {M : ℝ} (hM : 0 ≤ M) (h : ∀ k, |y k| ≤ M * |x k|) :
    ‖y‖ ≤ M * ‖x‖ := by
  have : ‖y‖ ≤ ‖M • x‖ := lp.norm_mono two_ne_zero' fun k => by
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hM]
    exact h k
  rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hM] at this

noncomputable def mulOp (c : ℕ → ℝ) (hc : ∀ k, |c k| ≤ 1) : H →L[ℝ] H :=
  LinearMap.mkContinuous (mulLin c hc) 1 fun x => norm_le_of_coord_le zero_le_one fun k => by
    rw [mulLin_apply, abs_mul]
    exact mul_le_mul_of_nonneg_right (hc k) (abs_nonneg _)

theorem mulOp_apply (c : ℕ → ℝ) (hc : ∀ k, |c k| ≤ 1) (x : H) (k : ℕ) :
    mulOp c hc x k = c k * x k := rfl

/-- The weights `2^{-k}`. -/
noncomputable def w (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

theorem w_pos (k : ℕ) : 0 < w k := by unfold w; positivity

theorem abs_w_le (k : ℕ) : |w k| ≤ 1 := by
  rw [abs_of_pos (w_pos k)]; unfold w; exact pow_le_one₀ (by norm_num) (by norm_num)

/-- The diagonal operator `diag(2^{-k})`. -/
noncomputable def D : H →L[ℝ] H := mulOp w abs_w_le

theorem D_apply (x : H) (k : ℕ) : D x k = w k * x k := rfl

theorem D_injective : Function.Injective D := by
  intro x y h
  refine lp.ext (funext fun k => ?_)
  have := congrArg (fun z : H => z k) h
  simp only [D_apply] at this
  exact mul_left_cancel₀ (w_pos k).ne' this

/-- The rank-one pieces `x ↦ 2^{-i} x_i e_i`. -/
noncomputable def R (i : ℕ) : H →L[ℝ] H :=
  (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 i).comp (w i • coord i)

theorem R_compact (i : ℕ) : IsCompactOperator (R i) := by
  rw [R, ContinuousLinearMap.coe_comp']
  exact (isCompactOperator_of_locallyCompactSpace_dom (w i • coord i)).clm_comp _

/-- The truncations `D_n = Σ_{i<n} R_i`. -/
noncomputable def Dn (n : ℕ) : H →L[ℝ] H := ∑ i ∈ Finset.range n, R i

theorem Dn_compact (n : ℕ) : IsCompactOperator (Dn n) := by
  have : Dn n ∈ compactOperator (RingHom.id ℝ) H H :=
    Submodule.sum_mem _ fun i _ => R_compact i
  exact this

theorem Dn_apply (n : ℕ) (x : H) (k : ℕ) :
    Dn n x k = if k ∈ Finset.range n then w k * x k else 0 := by
  simp only [Dn, ContinuousLinearMap.sum_apply, lp.coeFn_sum, Finset.sum_apply, R,
    ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply, lp.coeFn_single]
  rw [Finset.sum_pi_single]
  simp [coord_apply]

theorem norm_D_sub_Dn_le (n : ℕ) : ‖D - Dn n‖ ≤ (1 / 2 : ℝ) ^ n := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  refine norm_le_of_coord_le (by positivity) fun k => ?_
  rw [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply, D_apply, Dn_apply]
  split_ifs with hk
  · simp
  · rw [sub_zero, abs_mul, abs_of_pos (w_pos k)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    unfold w
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by simpa using hk)

theorem D_compact : IsCompactOperator D := by
  refine isCompactOperator_of_tendsto (l := atTop) (F := Dn) ?_ (Eventually.of_forall Dn_compact)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [norm_sub_rev]
  exact norm_D_sub_Dn_le n

/-- The scale: every level `ℓ²`, all inclusions `D`. -/
noncomputable def scale : ScScale where
  lvl _ := H
  incl _ := D
  incl_injective _ := D_injective
  incl_isCompactOperator _ := D_compact

/-- The finitely supported sequences. -/
def S : Submodule ℝ H where
  carrier := {x | ∃ n, ∀ k, n ≤ k → x k = 0}
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨n', hn'⟩
    exact ⟨max n n', fun k hk => by
      rw [lp.coeFn_add, Pi.add_apply, hn k (le_of_max_le_left hk),
        hn' k (le_of_max_le_right hk), add_zero]⟩
  zero_mem' := ⟨0, fun k _ => by rw [lp.coeFn_zero]; rfl⟩
  smul_mem' := by
    rintro c x ⟨n, hn⟩
    exact ⟨n, fun k hk => by rw [lp.coeFn_smul, Pi.smul_apply, hn k hk, smul_zero]⟩

theorem D_mem_S {x : H} (hx : x ∈ S) : D x ∈ S := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, fun k hk => by rw [D_apply, hn k hk, mul_zero]⟩

theorem exists_D_eq {z : H} (hz : z ∈ S) : ∃ y ∈ S, D y = z := by
  obtain ⟨n, hn⟩ := hz
  have hmem : Memℓp (fun k => (2 : ℝ) ^ k * z k) 2 := by
    refine (memℓp_zero ?_).of_exponent_ge (by norm_num)
    refine (Set.finite_lt_nat n).subset fun k hk => ?_
    by_contra h
    exact hk (by rw [hn k (not_lt.1 h), mul_zero])
  refine ⟨⟨_, hmem⟩, ⟨n, fun k hk => ?_⟩, lp.ext (funext fun k => ?_)⟩
  · change (2 : ℝ) ^ k * z k = 0
    rw [hn k hk, mul_zero]
  · change w k * ((2 : ℝ) ^ k * z k) = z k
    unfold w
    rw [← mul_assoc, ← mul_pow]
    norm_num

theorem toBase_mem_S : ∀ (m : ℕ) {x : H}, x ∈ S → scale.toBase m x ∈ S
  | 0, _, hx => hx
  | m + 1, _, hx => toBase_mem_S m (D_mem_S hx)

theorem exists_toBase_eq : ∀ (j : ℕ) {z : H}, z ∈ S → ∃ y ∈ S, scale.toBase j y = z
  | 0, z, hz => ⟨z, hz, rfl⟩
  | j + 1, _, hz => by
    obtain ⟨y', hy', hy'z⟩ := exists_toBase_eq j hz
    obtain ⟨y, hy, rfl⟩ := exists_D_eq hy'
    exact ⟨y, hy, hy'z⟩

theorem S_dense : Dense (S : Set H) := by
  intro f
  have hs := (lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 2) (by norm_num) f).tendsto_sum_nat
  refine mem_closure_of_tendsto hs (Eventually.of_forall fun n => ?_)
  refine Submodule.sum_mem _ fun i _ => ⟨i + 1, fun k hk => ?_⟩
  rw [lp.single_apply, Pi.single_apply, if_neg (by omega)]

/-- An infinite-dimensional sc-Banach space: `ℓ²` on every level, inclusions `diag(2^{-k})`. -/
noncomputable def G : ScBanach where
  toScScale := scale
  dense_smooth m := Dense.mono (fun x hx => by
    rw [ScScale.mem_smoothLvl_iff]
    intro j
    obtain ⟨y, -, hy⟩ := exists_toBase_eq j (toBase_mem_S m hx)
    exact ⟨y, hy⟩) S_dense

/-- `E₁ → E₀` is not onto: `(2^{-k})_k ∈ ℓ²` would need the preimage `(1, 1, …) ∉ ℓ²`. -/
theorem not_surj : ¬ Function.Surjective (G.toBase 1) := by
  intro h
  have hs : Summable (fun i => ‖w i‖ ^ (1 : ℝ≥0∞).toReal) := by
    simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs]
    refine summable_geometric_two.congr fun i => ?_
    rw [abs_of_pos (w_pos i)]
    rfl
  have hmem : Memℓp w 2 := (memℓp_gen hs).of_exponent_ge (by norm_num)
  obtain ⟨y, hy⟩ := h ⟨w, hmem⟩
  change H at y
  have h1 : ∀ k, y k = 1 := fun k => by
    have := congrArg (fun z : H => z k) hy
    change w k * y k = w k at this
    exact mul_left_cancel₀ (w_pos k).ne' (this.trans (mul_one _).symm)
  have ht := ((lp.memℓp y).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).tendsto_atTop_zero
  simp only [h1, norm_one, Real.one_rpow] at ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

end Model


/-! ### A discontinuous linear functional on an infinite-dimensional normed space -/

theorem exists_discontinuous {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : ¬ FiniteDimensional ℝ V) :
    ∃ (ψ : V →ₗ[ℝ] ℝ) (v : V), ψ v ≠ 0 ∧ ¬ Continuous ψ := by
  classical
  let b := Module.Basis.ofVectorSpace ℝ V
  have : Infinite (Module.Basis.ofVectorSpaceIndex ℝ V) := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    exact hV b.finiteDimensional_of_finite
  let j := Infinite.natEmbedding (Module.Basis.ofVectorSpaceIndex ℝ V)
  let c : Module.Basis.ofVectorSpaceIndex ℝ V → ℝ :=
    fun i => Function.extend j (fun n : ℕ => (n : ℝ)) 0 i * ‖b i‖
  let ψ : V →ₗ[ℝ] ℝ := b.constr ℝ c
  have hψ : ∀ n : ℕ, ψ (b (j n)) = n * ‖b (j n)‖ := fun n => by
    simp only [ψ, Module.Basis.constr_basis, c]
    rw [j.injective.extend_apply]
  have hb : ∀ i, 0 < ‖b i‖ := fun i => norm_pos_iff.2 (b.ne_zero i)
  refine ⟨ψ, b (j 1), ?_, fun hc => ?_⟩
  · rw [hψ]
    simpa using (hb (j 1)).ne'
  · let ψc : V →L[ℝ] ℝ := ⟨ψ, hc⟩
    obtain ⟨n, hn⟩ := exists_nat_gt ‖ψc‖
    have h1 := ψc.le_opNorm (b (j n))
    change ‖ψ (b (j n))‖ ≤ ‖ψc‖ * ‖b (j n)‖ at h1
    rw [hψ, norm_mul, Real.norm_natCast, norm_norm] at h1
    have := le_of_mul_le_mul_right h1 (hb _)
    linarith

theorem G_not_finiteDimensional : ¬ FiniteDimensional ℝ (Model.G 0) := fun _ =>
  Model.not_surj (ScBanach.toBase_bijective_of_finiteDimensional (E := Model.G) 1).2

/-! ### A closed complement of a smooth finite-dimensional subspace is an sc-complement -/

section Split

variable {E : ScBanach} {N Y : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]

/-- The level-`m` projection `x ↦ lift_m(π x)` onto `N_m` along `Y_m`. -/
noncomputable def projLvl (hN : N ≤ E.smooth) (h : Submodule.IsTopCompl N Y) (m : ℕ) :
    E m →L[ℝ] E m :=
  (LinearMap.toContinuousLinearMap (finSmoothLift hN m)).comp
    ((N.projectionOntoL Y h).comp (E.toBase m))

lemma toBase_projLvl (hN : N ≤ E.smooth) (h : Submodule.IsTopCompl N Y) (m : ℕ) (x : E m) :
    E.toBase m (projLvl hN h m x) = (N.projectionOntoL Y h (E.toBase m x) : E 0) :=
  toBase_finSmoothLift hN m _

noncomputable def projOp (hN : N ≤ E.smooth) (h : Submodule.IsTopCompl N Y) : ScOperator E E where
  lvl := projLvl hN h
  incl_comm m x := by
    apply E.toBase_injective m
    rw [← ScScale.toBase_succ, toBase_projLvl, toBase_projLvl, ScScale.toBase_succ]

lemma projOp_zero (hN : N ≤ E.smooth) (h : Submodule.IsTopCompl N Y) (x : E 0) :
    projOp hN h 0 x = (N.projectionOntoL Y h x : E 0) :=
  toBase_projLvl hN h 0 x

/-- A closed complement `Y` of a smooth finite-dimensional `N` is an sc-complement. -/
theorem isScSplitting_of_isClosed (hN : N ≤ E.smooth) (hNY : IsCompl N Y)
    (hY : IsClosed (Y : Set (E 0))) : E.IsScSplitting N Y := by
  have h : Submodule.IsTopCompl N Y :=
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hNY.symm hY).symm
  have hidem : ∀ x, projOp hN h 0 (projOp hN h 0 x) = projOp hN h 0 x := fun x => by
    rw [projOp_zero hN h (projOp hN h 0 x), projOp_zero hN h x,
      Submodule.projectionOntoL_apply_left]
  have hS := ScBanach.isScSplitting_of_idem (projOp hN h) hidem
  have hr : LinearMap.range (projOp hN h 0 : E 0 →ₗ[ℝ] E 0) = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change projOp hN h 0 y ∈ N
      rw [projOp_zero]
      exact (N.projectionOntoL Y h y).2
    · intro hx
      refine ⟨x, ?_⟩
      change projOp hN h 0 x = x
      rw [projOp_zero, Submodule.projectionOntoL_apply_left h ⟨x, hx⟩]
  have hk : LinearMap.ker (projOp hN h 0 : E 0 →ₗ[ℝ] E 0) = Y := by
    ext x
    rw [LinearMap.mem_ker]
    change projOp hN h 0 x = 0 ↔ x ∈ Y
    rw [projOp_zero, ← Submodule.projectionOntoL_apply_eq_zero_iff h]
    exact ⟨fun h0 => Subtype.ext h0, fun h0 => by rw [h0]; rfl⟩
  rwa [hr, hk] at hS

end Split

/-! ### The dictionary -/

section Dictionary

variable {E : ScBanach} {C : Set (E 0)} {N P : Submodule ℝ (E 0)}

theorem isGoodComplement_of_B (h : IsGoodComplementB E C N P) : IsGoodComplement E C N P := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h3⟩
  by_cases hN : N ≤ E.smooth
  · have := (h1 hN).2.2 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  · exact (h2 hN).1

theorem isClosed_of_B (h : IsGoodComplementB E C N P) : IsClosed (P : Set (E 0)) := by
  by_cases hN : N ≤ E.smooth
  · exact (h.1 hN).2.1.1
  · exact (h.2.1 hN).2

/-- The corrected dictionary: the text's good complement is the project's plus closedness. -/
theorem isGoodComplementB_iff [FiniteDimensional ℝ N] :
    IsGoodComplementB E C N P ↔ IsGoodComplement E C N P ∧ IsClosed (P : Set (E 0)) :=
  ⟨fun h => ⟨isGoodComplement_of_B h, isClosed_of_B h⟩, fun ⟨h, hP⟩ =>
    ⟨fun hs => isScSplitting_of_isClosed hs h.isCompl hP, fun _ => ⟨h.isCompl, hP⟩,
      h.exists_eps⟩⟩

/-- **The first conjunct of `B` holds**: good position is the text's, on a partial quadrant. -/
theorem goodPosition_iff [FiniteDimensional ℝ N] (hC : IsPartialQuadrant E C) :
    IsInGoodPosition E C N ↔ IsInGoodPositionB E C N := by
  constructor
  · intro h
    obtain ⟨Y, hY, hYc, -⟩ := exists_goodComplement_projectsInto hC h
    exact ⟨h.interior_nonempty, Y, isGoodComplementB_iff.2 ⟨hY, hYc⟩⟩
  · rintro ⟨h1, Q, hQ⟩
    exact ⟨h1, Q, isGoodComplement_of_B hQ⟩

end Dictionary

/-- The project's statement (the listed theorems; no universe parameters). -/
def A : Prop :=
  (type_of% @Polyfold.IsInGoodPositionSc.toIsInGoodPosition) ∧
  (type_of% @Polyfold.IsGoodComplement.isScGoodComplementIn) ∧
  (type_of% @Polyfold.IsInGoodPosition.isInGoodPositionSc) ∧
  (type_of% @Polyfold.isScGoodComplement_iff) ∧
  (type_of% @Polyfold.isInGoodPositionSc_iff)

theorem A_holds : A :=
  ⟨@Polyfold.IsInGoodPositionSc.toIsInGoodPosition, @Polyfold.IsGoodComplement.isScGoodComplementIn,
    @Polyfold.IsInGoodPosition.isInGoodPositionSc, @Polyfold.isScGoodComplement_iff,
    @Polyfold.isInGoodPositionSc_iff⟩

/-- The corrected form of `B` that holds: good position agrees, and the text's good complements
are the project's closed good complements. -/
def B_corrected : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0)) [FiniteDimensional ℝ N],
    IsPartialQuadrant E C →
      (IsInGoodPosition E C N ↔ IsInGoodPositionB E C N) ∧
      (∀ P : Submodule ℝ (E.lvl 0),
        IsGoodComplementB E C N P ↔ IsGoodComplement E C N P ∧ IsClosed (P : Set (E.lvl 0)))

theorem B_corrected_holds : B_corrected := fun _ _ _ _ hC =>
  ⟨goodPosition_iff hC, fun _ => isGoodComplementB_iff⟩

/-- **`B` is false**: a non-closed algebraic complement is a good complement for the project but
not for the text. -/
theorem not_B : ¬ B := by
  intro hB
  obtain ⟨ψ, v, hv, hψ⟩ := exists_discontinuous G_not_finiteDimensional
  have hsurj : Function.Surjective ψ :=
    (LinearMap.surjective_or_eq_zero ψ).resolve_right fun h0 => hv (by rw [h0]; rfl)
  have hvk : v ∉ LinearMap.ker ψ := fun h0 => hv h0
  have hcompl : IsCompl (ℝ ∙ v) (LinearMap.ker ψ) :=
    (Submodule.isCompl_span_singleton_of_isCoatom_of_notMem
      (LinearMap.isCoatom_ker_of_surjective hsurj) hvk).symm
  have hgood : IsGoodComplement Model.G Set.univ (ℝ ∙ v) (LinearMap.ker ψ) :=
    ⟨hcompl, 1, one_pos, fun _ _ _ _ _ => by simp⟩
  have hB' := ((hB Model.G Set.univ (ℝ ∙ v) (isPartialQuadrant_univ _)).2
    (LinearMap.ker ψ)).1 hgood
  exact hψ (ψ.continuous_of_isClosed_ker (isClosed_of_B hB'))

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- Ex falso: `B` is false. -/
theorem B_to_A : B → A := fun h => (not_B h).elim

#rt_check RoundTrip.V3_20.B_to_A [Polyfold.IsInGoodPositionSc.toIsInGoodPosition,
  Polyfold.IsGoodComplement.isScGoodComplementIn, Polyfold.IsInGoodPosition.isInGoodPositionSc,
  Polyfold.isScGoodComplement_iff, Polyfold.isInGoodPositionSc_iff]
#rt_overlap RoundTrip.V3_20.B_to_A [Polyfold.IsInGoodPositionSc.toIsInGoodPosition,
  Polyfold.IsGoodComplement.isScGoodComplementIn, Polyfold.IsInGoodPosition.isInGoodPositionSc,
  Polyfold.isScGoodComplement_iff, Polyfold.isInGoodPositionSc_iff]
#rt_check RoundTrip.V3_20.not_B [Polyfold.IsInGoodPositionSc.toIsInGoodPosition,
  Polyfold.IsGoodComplement.isScGoodComplementIn, Polyfold.IsInGoodPosition.isInGoodPositionSc,
  Polyfold.isScGoodComplement_iff, Polyfold.isInGoodPositionSc_iff]
#rt_check RoundTrip.V3_20.B_corrected_holds [Polyfold.IsInGoodPositionSc.toIsInGoodPosition,
  Polyfold.IsGoodComplement.isScGoodComplementIn, Polyfold.IsInGoodPosition.isInGoodPositionSc,
  Polyfold.isScGoodComplement_iff, Polyfold.isInGoodPositionSc_iff]

end RoundTrip.V3_20
