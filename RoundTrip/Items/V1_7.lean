import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_7

/-! Round trip for V1_7 (Definition 1.8 and the remarks after it: sc-Fredholm operators, `K ⊂ E_∞`,
`T(X_m) = Y_m`, `E_m = K ⊕ X_m`, `F = C ⊕ T(E_m)`, the index `dim K − dim C`).

`A` is the conjunction of the types of the theorems `ScFredholmSplitting.index_eq`,
`ScFredholmSplitting.K_le_smooth`, `ScFredholmSplitting.ker_lvl`, `ScFredholmSplitting.range_lvl`
and `ScFredholmSplitting.isFredholm` (the definitions `ScFredholmSplitting`, `IsScFredholm`,
`ScFredholmSplitting.index`, `scIndex` are vocabulary).  None has universe parameters.

The blind `IsFredholmData T K X C Y` has exactly the fields of the project's
`ScFredholmSplitting T` (`toSplitting`, `toData`).

* `B → A` (proved): `K_le_smooth` is `B`'s first conjunct and `range_lvl` follows from `B`'s
  `T(X_m) = Y_m`; `index_eq`, `ker_lvl` and `isFredholm` are elementary consequences of the
  splitting data themselves (re-proved here, without the banned theorems).
* `A → B` is false, because `B` is false (`not_B`, `not_A_to_B`): `B` states `F = C ⊕ T(E_m)`
  literally inside `F₀` for every `m`, which for `T = id` forces `E_m = E₀`.  We prove
  `B_implies_toBase_surjective` (`B` makes every inclusion `E_m → E₀` onto) and
  `B_implies_finiteDimensional` (then the compact inclusion `E₁ → E₀` is invertible, so every
  sc-Banach space is finite-dimensional), and `Example.exB` (`E_m = ℓ²`, inclusions
  `diag(2⁻ⁿ)`) is an infinite-dimensional sc-Banach space.
* With the blind author's intended reading `B_intended` (`F_m = C_m ⊕ T(E_m)` inside `F_m`), both
  directions are proved (`A_to_B_intended`, `B_intended_to_A`). -/

namespace RoundTrip.V1_7
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScFredholmSplitting.index_eq) ∧
    (type_of% @Polyfold.ScFredholmSplitting.K_le_smooth) ∧
    (type_of% @Polyfold.ScFredholmSplitting.ker_lvl) ∧
    (type_of% @Polyfold.ScFredholmSplitting.range_lvl) ∧
    (type_of% @Polyfold.ScFredholmSplitting.isFredholm)

theorem A_holds : A :=
  ⟨@Polyfold.ScFredholmSplitting.index_eq, @Polyfold.ScFredholmSplitting.K_le_smooth,
    @Polyfold.ScFredholmSplitting.ker_lvl, @Polyfold.ScFredholmSplitting.range_lvl,
    @Polyfold.ScFredholmSplitting.isFredholm⟩

section Glue

variable {E F : ScBanach} {T : ScOperator E F}

/-- Blind data ⇒ project splitting. -/
def toSplitting {K X : Submodule ℝ (E.lvl 0)} {C Y : Submodule ℝ (F.lvl 0)}
    (h : IsFredholmData T K X C Y) : ScFredholmSplitting T :=
  ⟨K, X, C, Y, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Project splitting ⇒ blind data. -/
theorem toData (s : ScFredholmSplitting T) : IsFredholmData T s.K s.X s.C s.Y :=
  ⟨s.splitE, s.splitF, s.ker_eq, s.finite_K, s.finite_C, s.range_eq, s.bijOn⟩

/-- `T(X_m) = Y_m`, from the level-wise bijectivity. -/
theorem map_X (s : ScFredholmSplitting T) (m : ℕ) :
    Submodule.map (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m) (E.levelSub s.X m) = F.levelSub s.Y m := by
  apply SetLike.coe_injective
  rw [Submodule.map_coe]
  exact (s.bijOn m).image_eq

/-- `range T_m = Y_m` from `T(X_m) = Y_m`. -/
theorem range_lvl_of_map (s : ScFredholmSplitting T) {m : ℕ}
    (h : Submodule.map (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m) (E.levelSub s.X m) = F.levelSub s.Y m) :
    LinearMap.range (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m) = F.levelSub s.Y m := by
  refine le_antisymm (s.range_eq ▸ T.range_lvl_le m) ?_
  rw [← h]
  exact LinearMap.map_le_range

/-- `index_eq`, re-proved from the splitting data. -/
theorem index_eq' (s : ScFredholmSplitting T) : s.index = scIndex T := by
  unfold ScFredholmSplitting.index scIndex
  have h := (s.splitF.2.2 0).symm
  rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at h
  rw [s.ker_eq, ← s.range_eq, (Submodule.quotientEquivOfIsCompl _ _ h).finrank_eq]

/-- `ker_lvl`, from `ScOperator.ker_lvl`. -/
theorem ker_lvl' (s : ScFredholmSplitting T) (m : ℕ) :
    LinearMap.ker (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m) = E.levelSub s.K m := by
  rw [T.ker_lvl, s.ker_eq]

/-- `isFredholm`, from the splitting data and the level ranges. -/
theorem isFredholm' (s : ScFredholmSplitting T)
    (hr : ∀ m, LinearMap.range (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m) = F.levelSub s.Y m) (m : ℕ) :
    (T.lvl m).IsFredholm := by
  have := s.finite_K
  have := s.finite_C
  refine isFredholm_of_banach (T.lvl m) ?_ ?_ ?_
  · rw [ker_lvl' s m]
    exact FiniteDimensional.of_injective ((E.toBase m : E.lvl m →ₗ[ℝ] E.lvl 0).restrict
      (p := E.levelSub s.K m) (q := s.K) fun _ hx => hx)
      fun x y hxy => Subtype.ext (E.toBase_injective m (congrArg Subtype.val hxy))
  · rw [hr m]
    exact F.isClosed_levelSub s.splitF.2.1.1 m
  · rw [hr m]
    have hfin : FiniteDimensional ℝ (F.levelSub s.C m) :=
      FiniteDimensional.of_injective ((F.toBase m : F.lvl m →ₗ[ℝ] F.lvl 0).restrict
        (p := F.levelSub s.C m) (q := s.C) fun _ hx => hx)
        fun x y hxy => Subtype.ext (F.toBase_injective m (congrArg Subtype.val hxy))
    exact Submodule.FG.cofg_of_isCompl (s.splitF.2.2 m)
      ((Submodule.fg_iff_finiteDimensional _).2 hfin)

end Glue

/-- `A` from the two conjuncts that `B` and `B_intended` share (`K ⊂ E_∞`, `T(X_m) = Y_m`). -/
theorem A_of (hK : ∀ {E F : ScBanach} {T : ScOperator E F} (s : ScFredholmSplitting T),
      s.K ≤ E.smooth)
    (hmap : ∀ {E F : ScBanach} {T : ScOperator E F} (s : ScFredholmSplitting T) (m : ℕ),
      Submodule.map (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m) (E.levelSub s.X m) = F.levelSub s.Y m) :
    A := by
  have hr : ∀ {E F : ScBanach} {T : ScOperator E F} (s : ScFredholmSplitting T) (m : ℕ),
      LinearMap.range (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m) = F.levelSub s.Y m :=
    fun s m => range_lvl_of_map s (hmap s m)
  exact ⟨fun s => index_eq' s, hK, fun s m => ker_lvl' s m, hr, fun s m => isFredholm' s (hr s) m⟩

theorem B_to_A : B → A := by
  intro hB
  exact A_of (fun s => (hB _ _ _ _ _ _ _ (toData s)).1)
    (fun s m => ((hB _ _ _ _ _ _ _ (toData s)).2.1 m).1)

/-- The intended reading, `B_intended → A`. -/
theorem B_intended_to_A : B_intended → A := by
  intro hB
  exact A_of (fun s => (hB _ _ _ _ _ _ _ (toData s)).1)
    (fun s m => ((hB _ _ _ _ _ _ _ (toData s)).2.1 m).1)

/-- The intended reading, `A → B_intended`. -/
theorem A_to_B_intended : A → B_intended := by
  intro hA E F T K X C Y hd
  let s := toSplitting hd
  refine ⟨hA.2.1 s, fun m => ⟨map_X s m, hd.1.2.2 m, ?_⟩, ?_⟩
  · have h : imageLevel T m = F.levelSub Y m := hA.2.2.2.1 s m
    rw [h]
    exact hd.2.1.2.2 m
  · intro K' X' C' Y' hd'
    have h1 := hA.1 s
    have h2 := hA.1 (toSplitting hd')
    simp only [ScFredholmSplitting.index] at h1 h2
    exact h1.trans h2.symm

/-! ### The literal `B` is false: it trivializes every sc-Banach space -/

/-- The trivial Fredholm data `E = 0 ⊕ E`, `E = 0 ⊕ E` of the identity. -/
theorem idData (E : ScBanach) : IsFredholmData (ScOperator.id E) ⊥ ⊤ ⊥ ⊤ := by
  have hbot : E.IsScSubspace ⊥ := (E.proposition_1_6_iff ⊥).2 bot_le
  have htop : E.IsScSubspace ⊤ := by
    refine ⟨by simp, fun m x _ => ?_⟩
    have : (E.levelSub ⊤ m : Set (E.lvl m)) ∩ E.smoothLvl m = E.smoothLvl m := by
      simp [ScBanach.levelSub]
    rw [this]
    exact E.dense_smooth m x
  have hlvl : ∀ m, IsCompl (E.levelSub ⊥ m) (E.levelSub ⊤ m) := fun m => by
    have h1 : E.levelSub ⊥ m = ⊥ := by
      rw [ScBanach.levelSub, Submodule.comap_bot]
      exact LinearMap.ker_eq_bot.2 (E.toBase_injective m)
    have h2 : E.levelSub ⊤ m = ⊤ := by rw [ScBanach.levelSub, Submodule.comap_top]
    rw [h1, h2]
    exact isCompl_bot_top
  refine ⟨⟨hbot, htop, hlvl⟩, ⟨hbot, htop, hlvl⟩, ?_, inferInstance, inferInstance, ?_, ?_⟩
  · exact (LinearMap.ker_id).symm
  · exact (LinearMap.range_id).symm
  · intro m
    have h2 : (E.levelSub ⊤ m : Set (E.lvl m)) = Set.univ := by
      simp [ScBanach.levelSub]
    rw [h2]
    exact Set.bijOn_id _

/-- `B` forces `T(E_m) = T(E₀)` for the identity, i.e. every inclusion `E_m → E₀` is onto. -/
theorem B_implies_toBase_surjective (hB : B) (E : ScBanach) (m : ℕ) :
    Function.Surjective (E.toBase m) := by
  have h := ((hB E E (ScOperator.id E) ⊥ ⊤ ⊥ ⊤ (idData E)).2.1 m).2.2
  have h' : imageLevelBase (ScOperator.id E) m = ⊤ := by
    have := h.sup_eq_top
    rwa [bot_sup_eq] at this
  intro y
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 h' y
  exact ⟨x, hx⟩

/-- Hence `B` forces every sc-Banach space to be finite-dimensional: the compact inclusion
`E₁ → E₀` would be bijective, so `id_{E₀}` would be compact. -/
theorem B_implies_finiteDimensional (hB : B) (E : ScBanach) : FiniteDimensional ℝ (E.lvl 0) := by
  have hsurj : Function.Surjective (E.incl 0) := B_implies_toBase_surjective hB E 1
  let e : E.lvl 1 ≃L[ℝ] E.lvl 0 := ContinuousLinearEquiv.ofBijective (E.incl 0)
    (LinearMap.ker_eq_bot.2 (E.incl_injective 0)) (LinearMap.range_eq_top.2 hsurj)
  have hc := (E.incl_isCompactOperator 0).comp_clm (e.symm : E.lvl 0 →L[ℝ] E.lvl 1)
  have hid : (E.incl 0 : E.lvl 1 → E.lvl 0) ∘ (e.symm : E.lvl 0 →L[ℝ] E.lvl 1) = id := by
    funext y
    exact e.apply_symm_apply y
  rw [hid] at hc
  exact FiniteDimensional.of_isCompactOperator_id hc

/-! ### An infinite-dimensional sc-Banach space: `E_m = ℓ²`, inclusions `diag(2⁻ⁿ)` -/

namespace Example
open Filter Topology

noncomputable section

/-- `ℓ²(ℕ, ℝ)`. -/
abbrev H := lp (fun _ : ℕ => ℝ) 2

/-- The weights `w n = 2⁻ⁿ`. -/
def w (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

theorem w_pos (n : ℕ) : 0 < w n := pow_pos (by norm_num) n

theorem abs_w_le (n : ℕ) : |w n| ≤ 1 := by
  rw [abs_of_pos (w_pos n)]; exact pow_le_one₀ (by norm_num) (by norm_num)

theorem memℓp_diag (c : ℕ → ℝ) {B : ℝ} (hc : ∀ n, |c n| ≤ B) (x : H) :
    Memℓp (fun n => c n * x n) 2 :=
  ((lp.memℓp x).norm.const_mul B).mono fun n => by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)

/-- The diagonal operator `x ↦ (c n x n)`. -/
def diagL (c : ℕ → ℝ) {B : ℝ} (hc : ∀ n, |c n| ≤ B) : H →ₗ[ℝ] H where
  toFun x := ⟨fun n => c n * x n, memℓp_diag c hc x⟩
  map_add' x y := lp.ext <| funext fun n => by
    change c n * (x + y) n = c n * x n + c n * y n
    rw [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' a x := lp.ext <| funext fun n => by
    change c n * (a • x) n = a * (c n * x n)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring

theorem diagL_apply (c : ℕ → ℝ) {B : ℝ} (hc : ∀ n, |c n| ≤ B) (x : H) (n : ℕ) :
    diagL c hc x n = c n * x n := rfl

theorem norm_diagL_le (c : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hc : ∀ n, |c n| ≤ B) (x : H) :
    ‖diagL c hc x‖ ≤ B * ‖x‖ := by
  calc ‖diagL c hc x‖ ≤ ‖B • x‖ := lp.norm_mono two_ne_zero fun i => by
          rw [diagL_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul,
            Real.norm_eq_abs, Real.norm_of_nonneg hB]
          exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
    _ = B * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hB]

/-- The diagonal operator as a continuous linear map. -/
def diag (c : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hc : ∀ n, |c n| ≤ B) : H →L[ℝ] H :=
  (diagL c hc).mkContinuous B (norm_diagL_le c hB hc)

theorem diag_apply (c : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hc : ∀ n, |c n| ≤ B) (x : H) (n : ℕ) :
    diag c hB hc x n = c n * x n := rfl

/-- The inclusion `D = diag w`. -/
def D : H →L[ℝ] H := diag w zero_le_one abs_w_le

/-- Truncated weights. -/
def cut (N n : ℕ) : ℝ := if n < N then w n else 0

theorem abs_cut_le (N n : ℕ) : |cut N n| ≤ 1 := by
  unfold cut; split_ifs
  · exact abs_w_le n
  · simp

def DN (N : ℕ) : H →L[ℝ] H := diag (cut N) zero_le_one (abs_cut_le N)

theorem norm_DN_sub_le (N : ℕ) : ‖DN N - D‖ ≤ w N := by
  refine ContinuousLinearMap.opNorm_le_bound _ (w_pos N).le fun x => ?_
  calc ‖(DN N - D) x‖ ≤ ‖w N • x‖ := lp.norm_mono two_ne_zero fun n => by
          change ‖(DN N x - D x) n‖ ≤ _
          rw [lp.coeFn_sub, Pi.sub_apply, DN, D, diag_apply,
            diag_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ← sub_mul, norm_mul, norm_mul,
            Real.norm_eq_abs, Real.norm_of_nonneg (w_pos N).le]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          unfold cut
          split_ifs with h
          · simp [(w_pos N).le]
          · rw [zero_sub, abs_neg, abs_of_pos (w_pos n)]
            exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (not_lt.1 h)
    _ = w N * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg (w_pos N).le]

theorem tendsto_DN : Tendsto DN atTop (𝓝 D) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) norm_DN_sub_le
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-- Sequences vanishing from `N` on. -/
def V (N : ℕ) : Submodule ℝ H where
  carrier := {y | ∀ n, N ≤ n → y n = 0}
  add_mem' {a b} ha hb n hn := by rw [lp.coeFn_add, Pi.add_apply, ha n hn, hb n hn, add_zero]
  zero_mem' n _ := by rw [lp.coeFn_zero]; rfl
  smul_mem' c y hy n hn := by rw [lp.coeFn_smul, Pi.smul_apply, hy n hn, smul_zero]

instance (N : ℕ) : FiniteDimensional ℝ (V N) := by
  let f : V N →ₗ[ℝ] (Fin N → ℝ) :=
    { toFun := fun y i => (y : H) i
      map_add' := fun a b => funext fun i => by
        change ((a : H) + (b : H)) i = _; rw [lp.coeFn_add]; rfl
      map_smul' := fun c a => funext fun i => by
        change (c • (a : H)) i = _; rw [lp.coeFn_smul]; rfl }
  refine FiniteDimensional.of_injective f fun a b hab => ?_
  apply Subtype.ext
  apply lp.ext
  funext n
  by_cases h : n < N
  · exact congrFun hab ⟨n, h⟩
  · rw [a.2 n (not_lt.1 h), b.2 n (not_lt.1 h)]

theorem isCompactOperator_DN (N : ℕ) : IsCompactOperator (DN N) := by
  have hr : ∀ x, DN N x ∈ V N := fun x n hn => by
    change cut N n * x n = 0
    simp [cut, not_lt.2 hn]
  let f' : H →L[ℝ] V N := (DN N).codRestrict (V N) hr
  have h1 : IsCompactOperator (f' : H → V N) := by
    have := (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ) (E := V N)).2 inferInstance
    exact this.comp_clm f'
  exact h1.clm_comp (V N).subtypeL

theorem isCompactOperator_D : IsCompactOperator D :=
  isCompactOperator_of_tendsto tendsto_DN (Eventually.of_forall isCompactOperator_DN)

theorem D_injective : Function.Injective D := by
  intro x y hxy
  apply lp.ext
  funext n
  have := congrArg (fun z : H => z n) hxy
  change w n * x n = w n * y n at this
  exact mul_left_cancel₀ (w_pos n).ne' this

theorem D_single (i : ℕ) (c : ℝ) : D (lp.single 2 i c) = lp.single 2 i (w i * c) := by
  apply lp.ext
  funext n
  change w n * (lp.single 2 i c : H) n = (lp.single 2 i (w i * c) : H) n
  rw [lp.coeFn_single, lp.coeFn_single]
  by_cases h : n = i
  · subst h; simp
  · simp [h]

/-- The scale `E_m = ℓ²` with inclusions `D`. -/
abbrev exScale : ScScale where
  lvl _ := H
  incl _ := D
  incl_injective _ := D_injective
  incl_isCompactOperator _ := isCompactOperator_D

theorem toBase_single (i : ℕ) (c : ℝ) : ∀ k,
    exScale.toBase k (lp.single 2 i c : H) = (lp.single 2 i (w i ^ k * c) : H)
  | 0 => by rw [pow_zero, one_mul]; rfl
  | k + 1 => by
    rw [ScScale.toBase_succ]
    change exScale.toBase k (D (lp.single 2 i c)) = _
    rw [D_single, toBase_single i (w i * c) k]
    congr 1; ring

theorem single_mem_smoothLvl (m i : ℕ) (c : ℝ) :
    (lp.single 2 i c : H) ∈ exScale.smoothLvl m := by
  rw [ScScale.mem_smoothLvl_iff]
  intro j
  refine ⟨(lp.single 2 i (w i ^ m * c / w i ^ j) : H), ?_⟩
  rw [toBase_single, toBase_single]
  congr 1
  have : w i ^ j ≠ 0 := pow_ne_zero _ (w_pos i).ne'
  field_simp

/-- An infinite-dimensional sc-Banach space: `E_m = ℓ²`, `E_{m+1} → E_m` the compact diagonal
operator `diag(2⁻ⁿ)`. -/
def exB : ScBanach where
  toScScale := exScale
  dense_smooth m := by
    let S : Submodule ℝ (exScale.lvl m) :=
      exScale.smooth.comap (exScale.toBase m : exScale.lvl m →ₗ[ℝ] exScale.lvl 0)
    have hS : (S : Set (exScale.lvl m)) = exScale.smoothLvl m := rfl
    rw [← hS]
    intro x
    exact mem_closure_of_tendsto (lp.hasSum_single (by simp) (x : H))
      (Eventually.of_forall fun s => S.sum_mem fun i _ => single_mem_smoothLvl m i _)

theorem coeFn_sum_apply (f : ℕ → H) (s : Finset ℕ) (n : ℕ) :
    (∑ j ∈ s, f j : H) n = ∑ j ∈ s, f j n := by
  rw [lp.coeFn_sum]
  exact Finset.sum_apply n s (fun j => ⇑(f j))

theorem not_finiteDimensional : ¬ FiniteDimensional ℝ H := by
  intro h
  apply Module.Finite.not_linearIndependent_of_infinite (R := ℝ)
    (fun i : ℕ => (lp.single 2 i (1 : ℝ) : H))
  rw [linearIndependent_iff']
  intro s g hg i hi
  have := congrArg (fun z : H => z i) hg
  simp only [coeFn_sum_apply, lp.coeFn_smul, lp.coeFn_single, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, if_pos hi, lp.coeFn_zero,
    Pi.zero_apply] at this
  exact this

theorem exB_not_finiteDimensional : ¬ FiniteDimensional ℝ (exB.lvl 0) := not_finiteDimensional

end

end Example

/-- **The literal `B` is false.** -/
theorem not_B : ¬ B := fun hB =>
  Example.exB_not_finiteDimensional (B_implies_finiteDimensional hB Example.exB)

/-- Hence `A → B` is false (`A` holds). -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

#rt_check RoundTrip.V1_7.B_to_A [Polyfold.ScFredholmSplitting.index_eq,
  Polyfold.ScFredholmSplitting.K_le_smooth, Polyfold.ScFredholmSplitting.ker_lvl,
  Polyfold.ScFredholmSplitting.range_lvl, Polyfold.ScFredholmSplitting.isFredholm]
#rt_overlap RoundTrip.V1_7.B_to_A [Polyfold.ScFredholmSplitting.index_eq,
  Polyfold.ScFredholmSplitting.K_le_smooth, Polyfold.ScFredholmSplitting.ker_lvl,
  Polyfold.ScFredholmSplitting.range_lvl, Polyfold.ScFredholmSplitting.isFredholm]
#rt_check RoundTrip.V1_7.not_B [Polyfold.ScFredholmSplitting.index_eq,
  Polyfold.ScFredholmSplitting.K_le_smooth, Polyfold.ScFredholmSplitting.ker_lvl,
  Polyfold.ScFredholmSplitting.range_lvl, Polyfold.ScFredholmSplitting.isFredholm]
#rt_check RoundTrip.V1_7.A_to_B_intended [Polyfold.ScFredholmSplitting.index_eq,
  Polyfold.ScFredholmSplitting.K_le_smooth, Polyfold.ScFredholmSplitting.ker_lvl,
  Polyfold.ScFredholmSplitting.range_lvl, Polyfold.ScFredholmSplitting.isFredholm]
#rt_check RoundTrip.V1_7.B_intended_to_A [Polyfold.ScFredholmSplitting.index_eq,
  Polyfold.ScFredholmSplitting.K_le_smooth, Polyfold.ScFredholmSplitting.ker_lvl,
  Polyfold.ScFredholmSplitting.range_lvl, Polyfold.ScFredholmSplitting.isFredholm]

end RoundTrip.V1_7
