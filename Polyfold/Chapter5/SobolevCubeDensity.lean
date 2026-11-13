import Polyfold.Chapter5.SobolevCubeRellich

/-!
# The sc-structure `W^{1+m,p}` on a cube, part 5: density of `E_∞`; the remark for `W^{1,4}`

Continuation of `SobolevCubeVolterra–4`.  Hofer–Wysocki–Zehnder, 2021 §5.5, the remark after
Theorem 5.5.5 (p. 231; preprint p. 194): for `Ω` a bounded domain in `ℝⁿ`, `E = W^{1,4}(Ω)`
equipped with the sc-structure `E_m = W^{1+m,4}(Ω)` admits sc-smooth bump functions.

* `exists_smooth_approx`: a chain `g_j = c_j + V g_{j+1}` (`j < k`) in `Lᵖ(I)` is approximated by
  the derivatives `f^{(j)}` of one smooth `f` (approximate `g_k` by a polynomial and integrate);
* **`dense_smoothLvl_cube`**: smooth functions are dense in every `W^{m+1,p}(Ω1)`, so `E_∞` is
  dense in every level;
* **`cubeSc p hp`** (`p > 1`): the sc-Banach space `E_m = W^{1+m,p}(Ω1)` on the open unit cube
  `Ω1 = (0,1)¹`, i.e. `sobolevSc` of `SobolevRemarkScStructures` with both of its hypotheses proved
  (`isCompactOperator_inclW_cube`, `dense_smoothLvl_cube`);
* **`remark_5_5_5_W14_cube`**: the claim of the remark for this sc-structure with `p = 4`, and
  `remark_5_5_5_W14_instance`: the hypothesis of `remark_5_5_5_W14` is satisfied (an sc-Banach space
  with `E₀ = W^{1,4}(Ω1)`); `remark_5_5_5_W1_3_2_cube`: the `W^{1,3/2}` statement on the cube.
-/

open MeasureTheory Set Function Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Polyfold

namespace SobolevCube

open SobolevRemark

variable {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)]

lemma toLpS_congr {f g : ℝ → ℝ} (h : f = g) (hf : Continuous f) (hg : Continuous g) :
    toLpS (p := p) f hf = toLpS g hg := by
  subst h; rfl

/-- **Smooth approximation of a chain**: if `g_j = c_j + V g_{j+1}` for `j < k`, then for every
`ε > 0` there is a smooth `f` with `‖g_j − f^{(j)}‖_{Lᵖ(I)} < ε` for all `j ≤ k`. -/
theorem exists_smooth_approx (k : ℕ) :
    ∀ (g : Fin (k + 1) → L p) (c : Fin k → ℝ),
      (∀ j : Fin k, g j.castSucc = cst (c j) + V (g j.succ)) →
      ∀ ε > 0, ∃ (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f),
        ∀ j : Fin (k + 1), ‖g j - toLpS (iteratedDeriv j f) (cont_iter hf j)‖ < ε := by
  induction k with
  | zero =>
    intro g _ _ ε hε
    obtain ⟨P, hP⟩ := Metric.denseRange_iff.1 (denseRange_poly (p := p)) (g 0) ε hε
    refine ⟨fun x => P.eval x, poly_contDiff P, fun j => ?_⟩
    rw [Fin.fin_one_eq_zero j, ← dist_eq_norm]
    rwa [toLpS_congr (show iteratedDeriv ((0 : Fin 1) : ℕ) (fun x => P.eval x) =
      fun x => P.eval x by simp) _ P.continuous]
  | succ k ih =>
    intro g c hg ε hε
    obtain ⟨f', hf', hf'ε⟩ := ih (fun j => g j.succ) (fun j => c j.succ)
      (fun j => by show g j.castSucc.succ = _; rw [Fin.succ_castSucc]; exact hg j.succ) ε hε
    set f : ℝ → ℝ := fun x => c 0 + prim f' x
    have hf : ContDiff ℝ ∞ f := contDiff_const.add (contDiff_prim hf')
    have hdf : deriv f = f' := by
      funext x
      exact ((hasDerivAt_prim hf'.continuous x).const_add (c 0)).deriv
    refine ⟨f, hf, fun j => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) j
    · -- the component `0`
      have e1 : toLpS (p := p) (iteratedDeriv ((0 : Fin (k + 2)) : ℕ) f) (cont_iter hf _) =
          cst (c 0) + V (toLpS f' hf'.continuous) := by
        rw [V_toLpS, cst, ← toLpS_add]
        exact toLpS_congr (by simp; rfl) _ _
      have e2 : g 0 = cst (c 0) + V (g 1) := hg 0
      rw [e1, e2, add_sub_add_left_eq_sub, ← map_sub]
      refine (norm_V_le _).trans_lt ?_
      have := hf'ε 0
      rwa [toLpS_congr (show iteratedDeriv ((0 : Fin (k + 1)) : ℕ) f' = f' by simp) _
        hf'.continuous, Fin.succ_zero_eq_one] at this
    · -- the components `i + 1`
      have := hf'ε i
      rwa [toLpS_congr (show iteratedDeriv (i : ℕ) f' = iteratedDeriv ((i.succ : Fin (k + 2)) : ℕ) f
        by rw [Fin.val_succ, iteratedDeriv_succ', hdf]) _ (cont_iter hf _)] at this

/-! ### Density of `E_∞` in `W^{m+1,p}(Ω1)` -/

lemma norm_Dop_sub_eq {k : ℕ} (u v : W 1 k p Ω1) (a : MIdx 1 k) :
    ‖Dop a (u - v)‖ = ‖comp u (a.1 0) - comp v (a.1 0)‖ := by
  rw [comp, comp, ← map_sub, ← map_sub, T.norm_map, ← eq_midx]

lemma card_MIdx_pos (k : ℕ) : 0 < Fintype.card (MIdx 1 k) :=
  Fintype.card_pos_iff.2 ⟨MIdx.zero 1 k⟩

/-- If every component of `u − v` has norm `< r / N`, `N` the number of multi-indices, then
`‖u − v‖ < r`. -/
lemma norm_sub_lt_of_comp {k : ℕ} (u v : W 1 k p Ω1) {r : ℝ} (hr : 0 < r)
    (h : ∀ j : Fin (k + 1),
      ‖comp u j - comp v j‖ < r / Fintype.card (MIdx 1 k)) : ‖u - v‖ < r := by
  set N : ℝ := (Fintype.card (MIdx 1 k) : ℝ)
  have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (card_MIdx_pos k)
  have hp0 := p_pos (p := p)
  have hsum : ‖u - v‖ ^ p < N * (r / N) ^ p := by
    rw [norm_rpow_W]
    calc ∑ a, ‖Dop a (u - v)‖ ^ p < ∑ _a : MIdx 1 k, (r / N) ^ p := by
          refine Finset.sum_lt_sum_of_nonempty ⟨MIdx.zero 1 k, Finset.mem_univ _⟩ fun a _ => ?_
          rw [norm_Dop_sub_eq]
          exact Real.rpow_lt_rpow (norm_nonneg _) (h _) hp0
      _ = N * (r / N) ^ p := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hle : N * (r / N) ^ p ≤ r ^ p := by
    rw [Real.div_rpow hr.le (by linarith), mul_div_assoc', div_le_iff₀ (by positivity),
      mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ p := Real.rpow_le_rpow_of_exponent_le hN one_le_p
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hr.le hp0).1 (hsum.trans_le hle)

variable (p) in
/-- The compactness hypothesis of `sobolevSc` for the cube. -/
lemma hc_cube (hp : 1 < p) :
    ∀ m, IsCompactOperator (inclW (n := 1) (k := m + 1) (p := p) (Ω := Ω1)) :=
  fun m => isCompactOperator_inclW_cube hp (m + 1)

lemma toBase_ofSmooth (hp : 1 < p) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ∀ j, (sobolevScale 1 p Ω1 isOpen_Ω1 (hc_cube p hp)).toBase j (ofSmooth f hf (j + 1)) =
      ofSmooth f hf 1
  | 0 => rfl
  | j + 1 =>
    (congrArg (fun y => (sobolevScale 1 p Ω1 isOpen_Ω1 (hc_cube p hp)).toBase j y)
      (inclW_ofSmooth f hf (j + 1))).trans (toBase_ofSmooth hp f hf j)

lemma ofSmooth_mem_smoothLvl (hp : 1 < p) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    (ofSmooth f hf (m + 1) : W 1 (m + 1) p Ω1) ∈
      (sobolevScale 1 p Ω1 isOpen_Ω1 (hc_cube p hp)).smoothLvl m :=
  (ScScale.mem_smoothLvl_iff _).2 fun j =>
    ⟨ofSmooth f hf (j + 1), (toBase_ofSmooth hp f hf j).trans (toBase_ofSmooth hp f hf m).symm⟩

/-- **`E_∞` is dense in every level `W^{m+1,p}(Ω1)`** (`p > 1`): the functions `f(x₀)`, `f`
smooth, are dense. -/
theorem dense_smoothLvl_cube (hp : 1 < p) (m : ℕ) :
    Dense ((sobolevScale 1 p Ω1 isOpen_Ω1 (hc_cube p hp)).smoothLvl m) := by
  refine Metric.dense_iff.2 fun u r hr => ?_
  change W 1 (m + 1) p Ω1 at u
  set N : ℝ := (Fintype.card (MIdx 1 (m + 1)) : ℝ)
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (card_MIdx_pos (m + 1))
  have hc := fun j : Fin (m + 1) => comp_eq_cst_add_V u j
  choose c hc using hc
  obtain ⟨f, hf, hfε⟩ := exists_smooth_approx (m + 1) (comp u) c hc (r / N) (by positivity)
  refine ⟨ofSmooth f hf (m + 1), ?_, ofSmooth_mem_smoothLvl hp f hf m⟩
  change dist (ofSmooth f hf (m + 1) : W 1 (m + 1) p Ω1) u < r
  rw [dist_comm, dist_eq_norm]
  refine norm_sub_lt_of_comp _ _ hr fun j => ?_
  rw [comp_ofSmooth]
  exact hfε j

/-! ### The sc-structure `E_m = W^{1+m,p}(Ω1)` and the remark for `W^{1,4}` -/

variable (p) in
/-- **The sc-Banach space `E_m = W^{1+m,p}(Ω1)`** on the open unit cube `Ω1 = (0,1)¹`, `p > 1`:
`sobolevSc` with both hypotheses (Rellich, density of `E_∞`) proved. -/
def cubeSc (hp : 1 < p) : ScBanach :=
  sobolevSc 1 p Ω1 isOpen_Ω1 (hc_cube p hp) (dense_smoothLvl_cube hp)

lemma cubeSc_zero (hp : 1 < p) : (cubeSc p hp).lvl 0 = W 1 1 p Ω1 := rfl

/-- **2021, p. 231: `W^{1,4}(Ω)` with the sc-structure `E_m = W^{1+m,4}(Ω)` admits sc-smooth bump
functions**, for `Ω` the open unit cube `(0,1)¹`: the sc-structure exists (`cubeSc 4`), as an
M-polyfold it admits sc-smooth bump functions, and every local model on it has the sc-smooth bump
function property. -/
theorem remark_5_5_5_W14_cube :
    (scPolyfold (cubeSc 4 (by norm_num))).AdmitsBumpFunctions ∧
      ∀ M : LocalModel, M.E = cubeSc 4 (by norm_num) → M.HasBumpProperty := by
  have h4 : ∃ j : ℕ, (4 : ℝ) = 2 * j := ⟨2, by norm_num⟩
  exact ⟨sobolevSc_admitsBumpFunctions 1 4 Ω1 h4 isOpen_Ω1 _ _,
    fun M hM => sobolevSc_hasBumpProperty 1 4 Ω1 h4 isOpen_Ω1 _ _ M hM⟩

/-- **The hypothesis of `remark_5_5_5_W14` is satisfiable**: there is an sc-Banach space
(`cubeSc 4`, levels `W^{1+m,4}(Ω1)`) whose `0`-level is `W^{1,4}(Ω1)`, and it admits sc-smooth
bump functions. -/
theorem remark_5_5_5_W14_instance :
    ∃ E : ScBanach, Nonempty (E 0 ≃L[ℝ] W 1 1 4 Ω1) ∧ (scPolyfold E).AdmitsBumpFunctions :=
  ⟨cubeSc 4 (by norm_num), ⟨ContinuousLinearEquiv.refl ℝ _⟩,
    (remark_5_5_5_W14.{0} (n := 1) (Ω := Ω1)).1 _ (ContinuousLinearEquiv.refl ℝ _)⟩

/-- **2021, p. 231: on `W^{1,3/2}(Ω)` with `E_m = W^{1+m,3/2}(Ω)` the straightforward bump is
sc¹**, for `Ω` the open unit cube: the sc-structure exists (`cubeSc (3/2)`), and `β(‖x‖^{3/2})`
is sc¹, nonzero, of bounded support. -/
theorem remark_5_5_5_W1_3_2_cube :
    ∃ f : W 1 1 (3 / 2) Ω1 → ℝ, IsSck 1 (cubeSc (3 / 2) (by norm_num)) realSc univ f ∧
      f ≠ 0 ∧ Bornology.IsBounded (support f) :=
  sobolevSc_exists_sc1_bump 1 Ω1 isOpen_Ω1 _ _

end SobolevCube

end Polyfold
