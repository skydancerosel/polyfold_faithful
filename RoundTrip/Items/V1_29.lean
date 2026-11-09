import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_29

/-! Round trip for V1_29 (the sentences after Definition 1.8: `K ⊂ E_∞`, `T(X_m) = Y_m`,
`E_m = K ⊕ X_m`, `F = C ⊕ T(E_m)`, index `dim K − dim C`).

`A` is the conjunction of the types of the theorems in the item's declaration list:
`ScFredholmSplitting.C_le_smooth`, `ScBanach.finrank_levelSub_of_le_smooth`,
`ScFredholmSplitting.fredholmIndex_lvl`, `IsScFredholm.fredholmIndex_lvl`,
`scIndex_eq_fredholmIndex`.  None has universe parameters (`ScBanach` lives in `Type`).

The blind data `IsFredholmData T K X C Y` are exactly the fields of the project's
`ScFredholmSplitting T` (`toSplitting`, `isFredholmData`).

* `B` is FALSE (`not_B`), as its author predicted: its clause `F = C ⊕ T(E_m)` taken literally in
  `F₀` forces (identity operator, `K = C = 0`) the inclusion `E_m → E₀` to be onto for every
  sc-Banach space (`B_surj`), which fails for the sc-Banach space `ℓ²` with all levels `ℓ²` and
  inclusions the compact diagonal operator `diag(2^{-k})` (`Model.G`, `Model.not_surj`).  So
  `A → B` is false, and `B → A` holds ex falso.
* The intended reading `B_intended` (`F_m = C_m ⊕ T(E_m)` inside `F_m`): `A → B_intended` is proved
  (`A_to_Bint`), using `A` for the index (`fredholmIndex_lvl` at level `0` for two splittings) and
  for `K ⊂ E_∞` (a dimension count: `A` gives `dim K_m − dim C_m = dim K − dim C` and
  `dim C_m = dim C`, so `K_m ≅ K`); the clauses `T(X_m) = Y_m`, `E_m = K_m ⊕ X_m`,
  `F_m = C_m ⊕ T(E_m)` are unpackings of Definition 1.8.  `B_intended → A` is proved only outright
  (`Bint_to_A`, not using `B_intended`): `A`'s content — `T_m : E_m → F_m` is Fredholm with index
  `dim K − dim C` on every level, `C ⊂ F_∞` — is not stated in the text, and follows from the
  definitions (Proposition 1.6 and the project's Fredholm criterion `ScFredholmSplitting.isFredholm`,
  which are not item theorems). -/

namespace RoundTrip.V1_29
open Polyfold Set Module

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScFredholmSplitting.C_le_smooth) ∧
    (type_of% @Polyfold.ScBanach.finrank_levelSub_of_le_smooth) ∧
    (type_of% @Polyfold.ScFredholmSplitting.fredholmIndex_lvl) ∧
    (type_of% @Polyfold.IsScFredholm.fredholmIndex_lvl) ∧
    (type_of% @Polyfold.scIndex_eq_fredholmIndex)

theorem A_holds : A :=
  ⟨@Polyfold.ScFredholmSplitting.C_le_smooth, @Polyfold.ScBanach.finrank_levelSub_of_le_smooth,
    @Polyfold.ScFredholmSplitting.fredholmIndex_lvl, @Polyfold.IsScFredholm.fredholmIndex_lvl,
    @Polyfold.scIndex_eq_fredholmIndex⟩

section Dictionary

variable {E F : ScBanach} {T : ScOperator E F}

/-- The blind data of Definition 1.8 are the project's `ScFredholmSplitting`. -/
def toSplitting {K X : Submodule ℝ (E 0)} {C Y : Submodule ℝ (F 0)}
    (h : IsFredholmData T K X C Y) : ScFredholmSplitting T :=
  ⟨K, X, C, Y, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem isFredholmData (s : ScFredholmSplitting T) : IsFredholmData T s.K s.X s.C s.Y :=
  ⟨s.splitE, s.splitF, s.ker_eq, s.finite_K, s.finite_C, s.range_eq, s.bijOn⟩

/-- `T(X_m) = Y_m` (from `T : X_m → Y_m` bijective). -/
theorem map_eq {K X : Submodule ℝ (E 0)} {C Y : Submodule ℝ (F 0)}
    (h : IsFredholmData T K X C Y) (m : ℕ) :
    Submodule.map (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m) (E.levelSub X m) = F.levelSub Y m := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h.2.2.2.2.2.2 m).mapsTo hx
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (h.2.2.2.2.2.2 m).surjOn hy
    exact ⟨x, hx, rfl⟩

/-- `F_m = C_m ⊕ T(E_m)` inside `F_m` (the intended reading). -/
theorem compl_intended {K X : Submodule ℝ (E 0)} {C Y : Submodule ℝ (F 0)}
    (h : IsFredholmData T K X C Y) (m : ℕ) : IsCompl (F.levelSub C m) (imageLevel T m) := by
  have hr : imageLevel T m = F.levelSub Y m := (toSplitting h).range_lvl m
  rw [hr]
  exact h.2.1.2.2 m

end Dictionary

/-! ### `A → B_intended` -/

/-- From `A`: the index `dim K − dim C` does not depend on the data. -/
theorem index_wd_of_A (hA : A) {E F : ScBanach} {T : ScOperator E F} {K X : Submodule ℝ (E 0)}
    {C Y : Submodule ℝ (F 0)} (h : IsFredholmData T K X C Y) : IndexWellDefined T K C := by
  intro K' X' C' Y' h'
  have e1 := (hA.2.2.1 (toSplitting h) 0).2
  have e2 := (hA.2.2.1 (toSplitting h') 0).2
  exact e1.symm.trans e2

/-- From `A`: `K ⊂ E_∞`, by the dimension count `dim K_m = dim K` on every level. -/
theorem K_le_smooth_of_A (hA : A) {E F : ScBanach} {T : ScOperator E F}
    (s : ScFredholmSplitting T) : s.K ≤ E.smooth := by
  have := s.finite_K
  have := s.finite_C
  intro k hk
  rw [ScScale.mem_smooth_iff]
  intro m
  have h1 := (hA.2.2.1 s m).2
  unfold fredholmIndex linIndex ScFredholmSplitting.index at h1
  rw [s.ker_lvl m, s.range_lvl m,
    (Submodule.quotientEquivOfIsCompl _ _ (s.splitF.2.2 m).symm).finrank_eq,
    hA.2.1 F (hA.1 s) m] at h1
  have hdim : finrank ℝ (E.levelSub s.K m) = finrank ℝ s.K := by omega
  let r : E.levelSub s.K m →ₗ[ℝ] s.K := (E.toBase m : E m →ₗ[ℝ] E 0).restrict fun _ hx => hx
  have hr : Function.Injective r := fun x y hxy =>
    Subtype.ext (E.toBase_injective m (congrArg Subtype.val hxy))
  have : FiniteDimensional ℝ (E.levelSub s.K m) := FiniteDimensional.of_injective r hr
  have hsurj : Function.Surjective r :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hr
  obtain ⟨x, hx⟩ := hsurj ⟨k, hk⟩
  exact ⟨x.1, congrArg Subtype.val hx⟩

theorem A_to_Bint : A → B_intended := by
  intro hA E F T K X C Y h
  exact ⟨K_le_smooth_of_A hA (toSplitting h), fun m => ⟨map_eq h m, h.1.2.2 m, compl_intended h m⟩,
    index_wd_of_A hA h⟩

/-! ### `A` from the definitions (used for `B_intended → A`, outright) -/

theorem finrank_levelSub' (E : ScBanach) {A' : Submodule ℝ (E 0)} (hA : A' ≤ E.smooth) (m : ℕ) :
    finrank ℝ (E.levelSub A' m) = finrank ℝ A' := by
  let r : E.levelSub A' m →ₗ[ℝ] A' := (E.toBase m : E m →ₗ[ℝ] E 0).restrict fun _ hx => hx
  have hr : Function.Bijective r := by
    refine ⟨fun x y hxy => Subtype.ext (E.toBase_injective m (congrArg Subtype.val hxy)),
      fun y => ?_⟩
    obtain ⟨x, hx⟩ := (ScScale.mem_smooth_iff E.toScScale).1 (hA y.2) m
    exact ⟨⟨x, by rw [ScBanach.mem_levelSub, hx]; exact y.2⟩, Subtype.ext hx⟩
  exact (LinearEquiv.ofBijective r hr).finrank_eq

theorem C_le_smooth' {E F : ScBanach} {T : ScOperator E F} (s : ScFredholmSplitting T) :
    s.C ≤ F.smooth :=
  haveI := s.finite_C
  (F.proposition_1_1_7_iff s.C).1 s.splitF.1

theorem fredholmIndex_lvl' {E F : ScBanach} {T : ScOperator E F} (s : ScFredholmSplitting T)
    (m : ℕ) : (T m).IsFredholm ∧ fredholmIndex (T m) = s.index := by
  refine ⟨s.isFredholm m, ?_⟩
  have := s.finite_C
  unfold fredholmIndex linIndex ScFredholmSplitting.index
  rw [s.ker_lvl m, s.range_lvl m, finrank_levelSub' E s.K_le_smooth m,
    (Submodule.quotientEquivOfIsCompl _ _ (s.splitF.2.2 m).symm).finrank_eq,
    finrank_levelSub' F (C_le_smooth' s) m]

/-- `A`, outright from the definitions (no hypothesis): `B_intended → A` is vacuous. -/
theorem A_outright : A := by
  refine ⟨fun s => C_le_smooth' s, finrank_levelSub', fredholmIndex_lvl', ?_, fun _ => rfl⟩
  intro E F T hT m
  obtain ⟨s⟩ := hT
  rw [← s.index_eq]
  exact fredholmIndex_lvl' s m

theorem Bint_to_A : B_intended → A := fun _ => A_outright

/-! ### `B` (literal) is false -/

/-- `B` forces every inclusion `E_m → E₀` to be onto (identity operator, `K = C = 0`). -/
theorem B_surj (hB : B) (G : ScBanach) (m : ℕ) : Function.Surjective (G.toBase m) := by
  have hbot : ∀ j, G.levelSub (⊥ : Submodule ℝ (G 0)) j = ⊥ := fun j => by
    ext x
    rw [ScBanach.mem_levelSub, Submodule.mem_bot, Submodule.mem_bot]
    constructor
    · intro hx; exact G.toBase_injective j (by rw [hx, map_zero])
    · intro hx; rw [hx, map_zero]
  have htop : ∀ j, G.levelSub (⊤ : Submodule ℝ (G 0)) j = ⊤ := fun j => by
    ext x; simp [ScBanach.mem_levelSub]
  have hsub_bot : G.IsScSubspace ⊥ := by
    refine ⟨by simp, fun j x hx => subset_closure ⟨hx, ?_⟩⟩
    rw [hbot j, SetLike.mem_coe, Submodule.mem_bot] at hx
    rw [hx]
    change G.toBase j 0 ∈ (G.smooth : Set (G 0))
    rw [map_zero]; exact G.smooth.zero_mem
  have hsub_top : G.IsScSubspace ⊤ := by
    refine ⟨by simp, fun j x _ => ?_⟩
    rw [htop j, Submodule.top_coe, univ_inter]
    exact G.dense_smooth j x
  have hsplit : G.IsScSplitting ⊥ ⊤ :=
    ⟨hsub_bot, hsub_top, fun j => by rw [hbot j, htop j]; exact isCompl_bot_top⟩
  have hd : IsFredholmData (ScOperator.id G) ⊥ ⊤ ⊥ ⊤ := by
    refine ⟨hsplit, hsplit, ?_, inferInstance, inferInstance, ?_, fun j => ?_⟩
    · exact (LinearMap.ker_id).symm
    · exact (LinearMap.range_id).symm
    · rw [htop j]; exact bijOn_id _
  have h := ((hB G G (ScOperator.id G) ⊥ ⊤ ⊥ ⊤ hd).2.1 m).2.2
  have htop' := eq_top_of_bot_isCompl h
  intro y
  have hy : y ∈ imageLevelBase (ScOperator.id G) m := by rw [htop']; trivial
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx⟩

/-! ### The counter-model: an infinite-dimensional sc-Banach space -/

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

/-- **`B` is false**: on the sc-Banach space `Model.G` (`ℓ²` with compact inclusions
`diag(2^{-k})`) the identity is sc-Fredholm with `K = C = 0`, and `B`'s clause `F = C ⊕ T(E₁)`
(in `F₀`) would make `E₁ → E₀` onto. -/
theorem not_B : ¬ B := fun hB => Model.not_surj (B_surj hB Model.G 1)

theorem B_to_A : B → A := fun hB => (not_B hB).elim

/-- Hence `A → B` is false (`A` holds). -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

#rt_check RoundTrip.V1_29.A_to_Bint [Polyfold.ScFredholmSplitting.C_le_smooth,
  Polyfold.ScBanach.finrank_levelSub_of_le_smooth, Polyfold.ScFredholmSplitting.fredholmIndex_lvl,
  Polyfold.IsScFredholm.fredholmIndex_lvl, Polyfold.scIndex_eq_fredholmIndex]
#rt_check RoundTrip.V1_29.Bint_to_A [Polyfold.ScFredholmSplitting.C_le_smooth,
  Polyfold.ScBanach.finrank_levelSub_of_le_smooth, Polyfold.ScFredholmSplitting.fredholmIndex_lvl,
  Polyfold.IsScFredholm.fredholmIndex_lvl, Polyfold.scIndex_eq_fredholmIndex]
#rt_check RoundTrip.V1_29.B_to_A [Polyfold.ScFredholmSplitting.C_le_smooth,
  Polyfold.ScBanach.finrank_levelSub_of_le_smooth, Polyfold.ScFredholmSplitting.fredholmIndex_lvl,
  Polyfold.IsScFredholm.fredholmIndex_lvl, Polyfold.scIndex_eq_fredholmIndex]
#rt_overlap RoundTrip.V1_29.B_to_A [Polyfold.ScFredholmSplitting.C_le_smooth,
  Polyfold.ScBanach.finrank_levelSub_of_le_smooth, Polyfold.ScFredholmSplitting.fredholmIndex_lvl,
  Polyfold.IsScFredholm.fredholmIndex_lvl, Polyfold.scIndex_eq_fredholmIndex]
#rt_check RoundTrip.V1_29.not_B [Polyfold.ScFredholmSplitting.C_le_smooth,
  Polyfold.ScBanach.finrank_levelSub_of_le_smooth, Polyfold.ScFredholmSplitting.fredholmIndex_lvl,
  Polyfold.IsScFredholm.fredholmIndex_lvl, Polyfold.scIndex_eq_fredholmIndex]
#rt_check RoundTrip.V1_29.B_surj [Polyfold.ScFredholmSplitting.C_le_smooth,
  Polyfold.ScBanach.finrank_levelSub_of_le_smooth, Polyfold.ScFredholmSplitting.fredholmIndex_lvl,
  Polyfold.IsScFredholm.fredholmIndex_lvl, Polyfold.scIndex_eq_fredholmIndex]

end RoundTrip.V1_29
