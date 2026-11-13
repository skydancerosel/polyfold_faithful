import Polyfold.Chapter15.GeneralPositionBranched

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.7** (General Position; 2017: Theorem 15.4), pp. 694–696: the parameter families
`t ↦ Λ_t` and the step "From local to global".

# Parameter families of sc⁺-multisections

## The text, paraphrased

At `x ∈ S_f` the proof picks sc⁺-sections `s¹_j` (small, supported near `x`) and the symmetric
family `s^{x,g}_t = Σ_j t_j · s^g_j`, `t ∈ ℝ^ℓ`; for fixed `t` this is an atomic, hence
structurable, sc⁺-multisection `Λ^x_t`, and `T_{(f̃,Λ̃)}(0, y)` is onto (on the reduced tangent
space at boundary points) for `y ∈ S_f` near `x`.  After a finite cover of `|S_f|`,
`Λ_t = ⊕_i Λ^{x_i}_{t_i}`, `t ∈ ℝ^{ℓ_1 + ⋯ + ℓ_k}`; every `Λ_t` is structurable, and (15.1)
holds at every `x ∈ S_f`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `paramSec s t = Σ_j t_j · s_j` (fibrewise), **`IsLinearFamily Λ`**: around every point the
  `Λ_t` have local section structures `(Σ_j t_j s_{ij}, σ_i)` with the same domain, sections and
  weights for all `t` (the branches are linear in `t`, as in the proof).
* **`IsParamOntoAt f Λ x`** (the surjectivity in (15.1)): in such a structure around `x ∈ S_f`,
  for every branch `i`, `(v, τ) ↦ f'(x) v + Σ_j τ_j s_{ij}(x)` maps `T^R_xX × ℝ^ℓ` onto `W_x`.
  Here `f'(x)` is the operator of `T(f,Λ₀)(x)` (Definition 15.1.7 for the trivial multisection);
  at `t = 0` all branches vanish, and the `t`-derivative of `f − Σ_j t_j s_{ij}` is
  `τ ↦ −Σ_j τ_j s_{ij}(x)`.
* The sum of two parameter families, `famAdd Λ Λ' (t, t') = Λ_t ⊕ Λ'_{t'}`:
  `IsLinearFamily.famAdd`, `IsParamOntoAt.famAdd_left`, `IsParamOntoAt.famAdd_right`.
* Sums of sc⁺-multisections (Definition 13.2.9): `exists_of_multisectionAdd_pos` (every point of
  `supp(Λ ⊕ Λ')` is `a + b` with `a ∈ supp Λ`, `b ∈ supp Λ'`), `normW_add_le`,
  **`pointwiseNorm_multisectionAdd_le`** (`N(Λ ⊕ Λ') ≤ N(Λ) + N(Λ')`),
  **`domSupp_multisectionAdd_subset`**.
* `normW_paramSec_le`, `pointwiseNorm_le_of_isLocalRepOn`, **`pointwiseNorm_le_of_linear`**
  (`N(Λ_t)(x) ≤ |t|₁ · b` from `N(s_{ij}(x)) ≤ b`, the bound used in the proof).
* **`GPFamily A f N U h Q`**: the data of the proof on a set `Q`: a linear family of
  structurable sc⁺-multisections with `N(Λ_t) ≤ |t|₁ · h`, `dom-supp(Λ_t) ⊆ U`, and (15.1) at the
  points of `S_f ∩ Q`.  `GPFamily.zero` (on `Q = ∅`, given a good system), `GPFamily.add` (on
  `Q ∪ Q'`), `GPFamily.mono`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold

variable {A : SEP.{u}}

/-! ### Linear combinations of sections -/

open scoped Classical in
/-- The fibrewise linear combination `Σ_j t_j · s_j` of sections (the value `0_y` where one of
the `s_j` is not a section). -/
def paramSec {ℓ : ℕ} (s : Fin ℓ → A.Obj → A.W) (t : Fin ℓ → ℝ) (y : A.Obj) : A.W :=
  if h : ∀ j, A.P (s j y) = y then
    ((∑ j, t j • (⟨s j y, h j⟩ : A.P ⁻¹' {y}) : A.P ⁻¹' {y}) : A.W)
  else fiberZero A.P y

theorem paramSec_apply {ℓ : ℕ} {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsSection A.P (s j))
    (t : Fin ℓ → ℝ) (y : A.Obj) :
    paramSec s t y = ((∑ j, t j • (⟨s j y, hs j y⟩ : A.P ⁻¹' {y}) : A.P ⁻¹' {y}) : A.W) := by
  rw [paramSec, dif_pos fun j => hs j y]

theorem isSection_paramSec {ℓ : ℕ} (s : Fin ℓ → A.Obj → A.W) (t : Fin ℓ → ℝ) :
    IsSection A.P (paramSec s t) := fun y => by
  unfold paramSec
  split_ifs with h
  · exact (∑ j, t j • (⟨s j y, h j⟩ : A.P ⁻¹' {y}) : A.P ⁻¹' {y}).2
  · exact proj_fiberZero A.P y

/-- `paramSec` as a vector of the fibre. -/
theorem paramFib {ℓ : ℕ} {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsSection A.P (s j))
    (t : Fin ℓ → ℝ) (y : A.Obj) :
    (⟨paramSec s t y, isSection_paramSec s t y⟩ : A.P ⁻¹' {y}) =
      ∑ j, t j • (⟨s j y, hs j y⟩ : A.P ⁻¹' {y}) :=
  Subtype.ext (paramSec_apply hs t y)

/-- The parameter-free combination is the zero section. -/
theorem paramSec_fin_zero (s : Fin 0 → A.Obj → A.W) (t : Fin 0 → ℝ) :
    paramSec s t = fiberZero A.P := by
  funext y
  rw [paramSec_apply (fun j => j.elim0), Finset.univ_eq_empty, Finset.sum_empty]
  rfl

/-- `Fin.append` of two families of sections is a family of sections. -/
theorem isSection_append {ℓ ℓ' : ℕ} {s : Fin ℓ → A.Obj → A.W} {s' : Fin ℓ' → A.Obj → A.W}
    (hs : ∀ j, IsSection A.P (s j)) (hs' : ∀ j, IsSection A.P (s' j)) :
    ∀ j, IsSection A.P (Fin.append s s' j) := fun j =>
  Fin.addCases (fun i => by simpa using hs i) (fun i => by simpa using hs' i) j

/-- The two parts of a parameter `t ∈ ℝ^{ℓ+ℓ'}`. -/
def parL {ℓ ℓ' : ℕ} (t : Fin (ℓ + ℓ') → ℝ) : Fin ℓ → ℝ := fun j => t (Fin.castAdd ℓ' j)

/-- The second part of a parameter `t ∈ ℝ^{ℓ+ℓ'}`. -/
def parR {ℓ ℓ' : ℕ} (t : Fin (ℓ + ℓ') → ℝ) : Fin ℓ' → ℝ := fun j => t (Fin.natAdd ℓ j)

/-- **Concatenating parameters adds the combinations**:
`Σ_{j ≤ ℓ+ℓ'} t_j (s ⧺ s')_j = Σ_j t_j s_j + Σ_j t_{ℓ+j} s'_j`. -/
theorem paramSec_append {ℓ ℓ' : ℕ} {s : Fin ℓ → A.Obj → A.W} {s' : Fin ℓ' → A.Obj → A.W}
    (hs : ∀ j, IsSection A.P (s j)) (hs' : ∀ j, IsSection A.P (s' j))
    (t : Fin (ℓ + ℓ') → ℝ) :
    paramSec (Fin.append s s') t =
      Polyfold.sectionAdd A.P (paramSec s (parL t)) (paramSec s' (parR t)) := by
  funext y
  rw [sectionAdd_apply (isSection_paramSec _ _) (isSection_paramSec _ _),
    paramSec_apply (isSection_append hs hs')]
  congr 1
  rw [Fin.sum_univ_add]
  congr 1
  · refine Eq.trans ?_ (paramFib hs _ y).symm
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact Subtype.ext (by simp)
  · refine Eq.trans ?_ (paramFib hs' _ y).symm
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact Subtype.ext (by simp)

/-! ### Norm bounds for linear branches -/

/-- **`N(Σ_j t_j s_j(y)) ≤ Σ_j |t_j| N(s_j(y))`** for an auxiliary norm (Definition 5.1.1 (1)), when
the `s_j(y)` lie in `W_{0,1}`. -/
theorem normW_paramSec_le {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) {ℓ : ℕ}
    {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsSection A.P (s j)) (t : Fin ℓ → ℝ) {y : A.Obj}
    (h1 : ∀ j, s j y ∈ A.B.oneSet) :
    normW N (paramSec s t y) ≤ ∑ j, |t j| * normW N (s j y) := by
  let v : Fin ℓ → A.B.oneFiber y := fun j => ⟨⟨s j y, hs j y⟩, h1 j⟩
  have hv : paramSec s t y = (((∑ j, t j • v j : A.B.oneFiber y) : A.P ⁻¹' {y}) : A.W) := by
    rw [paramSec_apply hs]
    congr 1
    rw [Submodule.coe_sum]
    rfl
  have hmem : paramSec s t y ∈ A.B.oneSet := by rw [hv]; exact (∑ j, t j • v j).2
  rw [normW_of_mem N hmem]
  have e : A.B.oneMk (paramSec s t y) hmem = A.B.toOne (∑ j, t j • v j) :=
    A.B.oneVal_injective (by rw [A.B.oneVal_oneMk, A.B.oneVal_toOne, hv])
  rw [e]
  refine (Finset.le_sum_of_subadditive (fun w : A.B.oneFiber y => N (A.B.toOne w))
    (hN.fiber y).map_zero.le (hN.fiber y).add_le _ _).trans_eq
    (Finset.sum_congr rfl fun j _ => ?_)
  rw [(hN.fiber y).smul, normW_of_mem N (h1 j)]
  rfl

/-- **A bound for the pointwise norm from a local representation**: if the branches at `x` have
`N(sᵢ(x)) ≤ b`, then `N(Λ)(x) ≤ b` (Definition 13.2.3). -/
theorem pointwiseNorm_le_of_isLocalRepOn {N : A.B.One → ℝ} {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) {O : Set A.Obj} {k : ℕ} {s : Fin k → A.Obj → A.W}
    {σ : Fin k → ℚ≥0} (hrep : IsLocalRepOn A Λ O s σ) {x : A.Obj} (hx : x ∈ O) {b : ℝ}
    (hb : ∀ i, normW N (s i x) ≤ b) : pointwiseNorm N Λ x ≤ b := by
  obtain ⟨w, hw, hwN⟩ := (hΛ.isGreatest_pointwiseNorm N x).1
  rw [hrep.suppAt_eq hx] at hw
  obtain ⟨i, rfl⟩ := hw
  rw [← hwN]
  exact hb i

/-- **The bound `N(Λ_t)(x) ≤ |t|₁ · b(x)` of a linear family** (the bound of the proof of Theorem
15.3.7 from `N(s¹_j) ≤ min{1, h}`): if in a linear local representation around `x` every
`s_{ij}(x)` lies in `W_{0,1}` with `N(s_{ij}(x)) ≤ b`, then `N(Λ_t)(x) ≤ |t|₁ · b`. -/
theorem pointwiseNorm_le_of_linear {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) {ℓ : ℕ}
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) {O : Set A.Obj} {k : ℕ}
    {s : Fin k → Fin ℓ → A.Obj → A.W} {σ : Fin k → ℚ≥0} (hs : ∀ i j, IsSection A.P (s i j))
    {t : Fin ℓ → ℝ} (hrep : IsLocalRepOn A Λ O (fun i => paramSec (s i) t) σ) {x : A.Obj}
    (hx : x ∈ O) (h1 : ∀ i j, s i j x ∈ A.B.oneSet) {b : ℝ}
    (hb : ∀ i j, normW N (s i j x) ≤ b) : pointwiseNorm N Λ x ≤ (∑ j, |t j|) * b := by
  refine pointwiseNorm_le_of_isLocalRepOn hΛ hrep hx fun i => ?_
  refine (normW_paramSec_le hN (hs i) t (h1 i)).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hb i j) (abs_nonneg _)

/-! ### Linear families and the parametrized surjectivity (15.1) -/

/-- **A linear family** `t ↦ Λ_t`, `t ∈ ℝ^ℓ`, of functors `W → ℚ⁺` (the families of the proof
of Theorem 15.3.7): around every object there are an open `O`, sections `s_{ij}` (`i ≤ k`,
`j ≤ ℓ`) and weights `σ_i` such that for every `t` the sections `Σ_j t_j s_{ij}` with the
weights `σ_i` are a local representation of `Λ_t` on `O` (Definition 13.2.1). -/
def IsLinearFamily {ℓ : ℕ} (Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0) : Prop :=
  ∀ x₀ : A.Obj, ∃ (O : Set A.Obj) (k : ℕ) (s : Fin k → Fin ℓ → A.Obj → A.W)
    (σ : Fin k → ℚ≥0), IsOpen O ∧ x₀ ∈ O ∧ (∀ i j, IsSection A.P (s i j)) ∧
      ∀ t, IsLocalRepOn A (Λ t) O (fun i => paramSec (s i) t) σ

/-- **The parametrized reduced surjectivity at `(0, x)`** ((15.1) in the proof of Theorem 15.3.7,
p. 696): in a linear local representation `(Σ_j t_j s_{ij}, σ_i)` of the family around `x`, for
every branch `i`, every operator `L` of `T(f,Λ₀)(x)` (the linearization `f'(x)`, Definition
15.1.7 for the trivial multisection) and every chart presentation of the reduced tangent space
`T^R_xX` (Definition 2.5.8), `(v, τ) ↦ L v + Σ_j τ_j s_{ij}(x)` maps `T^R_xX × ℝ^ℓ` onto `W_x`. -/
def IsParamOntoAt (f : A.Obj → A.W) {ℓ : ℕ} (Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0)
    (x : A.X.PObj.Level 1) : Prop :=
  ∃ (O : Set A.Obj) (k : ℕ) (s : Fin k → Fin ℓ → A.Obj → A.W) (σ : Fin k → ℚ≥0)
    (hs : ∀ i j, IsSection A.P (s i j)), IsOpen O ∧ A.X.PObj.levelVal 1 x ∈ O ∧
      (∀ t, IsLocalRepOn A (Λ t) O (fun i => paramSec (s i) t) σ) ∧
      ∀ L ∈ (linearization f (zeroMultisection A) x).support, ∀ (φ : MChart A.Obj)
        (hφ : A.X.PObj.IsChart φ) (hx : A.X.PObj.levelVal 1 x ∈ φ.source) (m : ℕ)
        (V : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin m → ℝ)).prod V)),
        φ.model.C = T 0 ⁻¹' quadrant m V 0 →
          ∀ i (w : A.P ⁻¹' {A.X.PObj.levelVal 1 x}), ∃ v ∈ reducedTangentFiber hφ hx T,
            ∃ τ : Fin ℓ → ℝ, L v + ∑ j, τ j •
              (⟨s i j (A.X.PObj.levelVal 1 x), hs i j _⟩ : A.P ⁻¹' {A.X.PObj.levelVal 1 x}) = w

/-! ### The sum of two families -/

/-- **The sum of two parameter families**: `(t, t') ↦ Λ_t ⊕ Λ'_{t'}` on `ℝ^{ℓ+ℓ'}`
(Definition 13.2.9; the `Λ_t = ⊕_i Λ^{x_i}_{t_i}` of the proof). -/
def famAdd {ℓ ℓ' : ℕ} (Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0) (Λ' : (Fin ℓ' → ℝ) → A.W → ℚ≥0)
    (t : Fin (ℓ + ℓ') → ℝ) : A.W → ℚ≥0 :=
  multisectionAdd (Λ (parL t)) (Λ' (parR t))

/-- **The sum of two linear local representations on the same domain** is linear: the sections
`Σ_j t_j (s_i ⧺ s'_{i'})_j` with the weights `σ_i σ'_{i'}`, reindexed by `Fin`. -/
theorem isLocalRepOn_famAdd {ℓ ℓ' : ℕ} {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0}
    {Λ' : (Fin ℓ' → ℝ) → A.W → ℚ≥0} {O : Set A.Obj} (hO : IsOpen O) {k k' : ℕ}
    {s : Fin k → Fin ℓ → A.Obj → A.W} {σ : Fin k → ℚ≥0} {s' : Fin k' → Fin ℓ' → A.Obj → A.W}
    {σ' : Fin k' → ℚ≥0} (hs : ∀ i j, IsSection A.P (s i j))
    (hs' : ∀ i j, IsSection A.P (s' i j))
    (h : ∀ t, IsLocalRepOn A (Λ t) O (fun i => paramSec (s i) t) σ)
    (h' : ∀ t, IsLocalRepOn A (Λ' t) O (fun i => paramSec (s' i) t) σ') (t : Fin (ℓ + ℓ') → ℝ) :
    IsLocalRepOn A (famAdd Λ Λ' t)
      O (fun n => paramSec (Fin.append (s ((Fintype.equivFin (Fin k × Fin k')).symm n).1)
        (s' ((Fintype.equivFin (Fin k × Fin k')).symm n).2)) t)
      (fun n => σ ((Fintype.equivFin (Fin k × Fin k')).symm n).1 *
        σ' ((Fintype.equivFin (Fin k × Fin k')).symm n).2) := by
  classical
  refine isLocalRepOn_of_fintype (K := Fin k × Fin k')
    (fun κ => paramSec (Fin.append (s κ.1) (s' κ.2)) t) (fun κ => σ κ.1 * σ' κ.2)
    (fun κ => mul_pos ((h (parL t)).1 κ.1) ((h' (parR t)).1 κ.2)) (fun κ => ?_) ?_ (fun w hw => ?_)
  · rw [paramSec_append (hs κ.1) (hs' κ.2)]
    exact IsScPlusSectionOn.sectionAdd hO ((h (parL t)).2.1 κ.1) ((h' (parR t)).2.1 κ.2)
      (isSection_paramSec _ _) (isSection_paramSec _ _)
  · rw [Fintype.sum_prod_type, ← (h (parL t)).2.2.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ∑ j, σ i * σ' j = σ i
    rw [← Finset.mul_sum, (h' (parR t)).2.2.1, mul_one]
  · rw [famAdd, multisectionAdd_eq_sum_of_isLocalRepOn (h (parL t)) (h' (parR t))
      (fun i => isSection_paramSec _ _) (fun j => isSection_paramSec _ _) hw,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [paramSec_append (hs i) (hs' j)]

/-- **The sum of two linear families is linear.** -/
theorem IsLinearFamily.famAdd {ℓ ℓ' : ℕ} {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0}
    {Λ' : (Fin ℓ' → ℝ) → A.W → ℚ≥0} (h : IsLinearFamily Λ) (h' : IsLinearFamily Λ') :
    IsLinearFamily (famAdd Λ Λ') := by
  intro x₀
  obtain ⟨O, k, s, σ, hO, hx, hs, hr⟩ := h x₀
  obtain ⟨O', k', s', σ', hO', hx', hs', hr'⟩ := h' x₀
  refine ⟨O ∩ O', _, _, _, hO.inter hO', ⟨hx, hx'⟩, fun n j => isSection_append (hs _) (hs' _) j,
    isLocalRepOn_famAdd (hO.inter hO') hs hs' (fun t => (hr t).mono (hO.inter hO')
      inter_subset_left) (fun t => (hr' t).mono (hO.inter hO') inter_subset_right)⟩

/-- **(15.1) passes to sums, from the first summand**: if `(f, Λ)` is parametrically onto at `x`
and `Λ'` is a linear family, then so is `(f, Λ ⊕ Λ')` (put `τ' = 0` on the new parameters). -/
theorem IsParamOntoAt.famAdd_left {f : A.Obj → A.W} {ℓ ℓ' : ℕ} {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0}
    {Λ' : (Fin ℓ' → ℝ) → A.W → ℚ≥0} {x : A.X.PObj.Level 1} (hp : IsParamOntoAt f Λ x)
    (h' : IsLinearFamily Λ') : IsParamOntoAt f (famAdd Λ Λ') x := by
  classical
  obtain ⟨O, k, s, σ, hs, hO, hx, hr, hon⟩ := hp
  obtain ⟨O', k', s', σ', hO', hx', hs', hr'⟩ := h' (A.X.PObj.levelVal 1 x)
  refine ⟨O ∩ O', _, _, _, fun n j => isSection_append (hs _) (hs' _) j, hO.inter hO', ⟨hx, hx'⟩,
    isLocalRepOn_famAdd (hO.inter hO') hs hs' (fun t => (hr t).mono (hO.inter hO')
      inter_subset_left) (fun t => (hr' t).mono (hO.inter hO') inter_subset_right), ?_⟩
  intro L hL φ hφ hxφ m V T hT n w
  obtain ⟨v, hv, τ, hτ⟩ :=
    hon L hL φ hφ hxφ m V T hT ((Fintype.equivFin (Fin k × Fin k')).symm n).1 w
  refine ⟨v, hv, Fin.append τ 0, ?_⟩
  rw [← hτ, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_smul,
    Finset.sum_const_zero, add_zero]

/-- **(15.1) passes to sums, from the second summand.** -/
theorem IsParamOntoAt.famAdd_right {f : A.Obj → A.W} {ℓ ℓ' : ℕ} {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0}
    {Λ' : (Fin ℓ' → ℝ) → A.W → ℚ≥0} {x : A.X.PObj.Level 1} (h : IsLinearFamily Λ)
    (hp : IsParamOntoAt f Λ' x) : IsParamOntoAt f (famAdd Λ Λ') x := by
  classical
  obtain ⟨O', k', s', σ', hs', hO', hx', hr', hon⟩ := hp
  obtain ⟨O, k, s, σ, hO, hx, hs, hr⟩ := h (A.X.PObj.levelVal 1 x)
  refine ⟨O ∩ O', _, _, _, fun n j => isSection_append (hs _) (hs' _) j, hO.inter hO', ⟨hx, hx'⟩,
    isLocalRepOn_famAdd (hO.inter hO') hs hs' (fun t => (hr t).mono (hO.inter hO')
      inter_subset_left) (fun t => (hr' t).mono (hO.inter hO') inter_subset_right), ?_⟩
  intro L hL φ hφ hxφ m V T hT n w
  obtain ⟨v, hv, τ, hτ⟩ :=
    hon L hL φ hφ hxφ m V T hT ((Fintype.equivFin (Fin k × Fin k')).symm n).2 w
  refine ⟨v, hv, Fin.append 0 τ, ?_⟩
  rw [← hτ, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_smul,
    Finset.sum_const_zero, zero_add]

/-! ### Supports and pointwise norms of sums (Definition 13.2.9) -/

/-- **Every point of `supp(Λ ⊕ Λ')` over `x` is a sum `a + b`** with `Λ(a) > 0`, `Λ'(b) > 0`. -/
theorem exists_of_multisectionAdd_pos {Λ Λ' : A.W → ℚ≥0} {w : A.W}
    (h : 0 < multisectionAdd Λ Λ' w) :
    ∃ a b : A.P ⁻¹' {A.P w}, 0 < Λ a ∧ 0 < Λ' b ∧ ((a + b : A.P ⁻¹' {A.P w}) : A.W) = w := by
  classical
  by_contra H
  push Not at H
  refine h.ne' (finsum_eq_zero_of_forall_eq_zero fun p => ?_)
  split_ifs with hc
  · rcases eq_or_ne (Λ p.1) 0 with h1 | h1
    · rw [h1, zero_mul]
    rcases eq_or_ne (Λ' p.2) 0 with h2 | h2
    · rw [h2, mul_zero]
    exact absurd hc (H p.1 p.2 (pos_iff_ne_zero.2 h1) (pos_iff_ne_zero.2 h2))
  · rfl

/-- **The triangle inequality for an auxiliary norm read on `W`**, in one fibre of `W_{0,1}`. -/
theorem normW_add_le {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) {x : A.Obj}
    (a b : A.P ⁻¹' {x}) (ha : (a : A.W) ∈ A.B.oneSet) (hb : (b : A.W) ∈ A.B.oneSet) :
    normW N ((a + b : A.P ⁻¹' {x}) : A.W) ≤ normW N a + normW N b := by
  set va : A.B.oneFiber x := ⟨a, ha⟩
  set vb : A.B.oneFiber x := ⟨b, hb⟩
  have hab : ((a + b : A.P ⁻¹' {x}) : A.W) ∈ A.B.oneSet := (va + vb).2
  rw [normW_of_mem N hab, normW_of_mem N ha, normW_of_mem N hb]
  exact (hN.fiber x).add_le va vb

/-- **`N(Λ ⊕ Λ')(x) ≤ N(Λ)(x) + N(Λ')(x)`** (Definitions 13.2.3, 13.2.9). -/
theorem pointwiseNorm_multisectionAdd_le {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N)
    {Λ Λ' : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (hΛ' : IsScPlusMultisection A Λ')
    (x : A.Obj) :
    pointwiseNorm N (multisectionAdd Λ Λ') x ≤ pointwiseNorm N Λ x + pointwiseNorm N Λ' x := by
  obtain ⟨w, ⟨hwx, hpos⟩, hw⟩ :=
    ((definition_13_2_9 hΛ hΛ').isGreatest_pointwiseNorm N x).1
  subst hwx
  obtain ⟨a, b, ha, hb, hab⟩ := exists_of_multisectionAdd_pos hpos
  have hsa : (a : A.W) ∈ suppAt Λ (A.P w) := ⟨a.2, ha⟩
  have hsb : (b : A.W) ∈ suppAt Λ' (A.P w) := ⟨b.2, hb⟩
  have e : normW N w = normW N ((a + b : A.P ⁻¹' {A.P w}) : A.W) := by rw [hab]
  rw [← hw, e]
  refine (normW_add_le hN a b (hΛ.suppAt_subset_oneSet _ hsa)
    (hΛ'.suppAt_subset_oneSet _ hsb)).trans (add_le_add ?_ ?_)
  · exact (hΛ.isGreatest_pointwiseNorm N _).2 ⟨_, hsa, rfl⟩
  · exact (hΛ'.isGreatest_pointwiseNorm N _).2 ⟨_, hsb, rfl⟩

/-- **`dom-supp(Λ ⊕ Λ') ⊆ dom-supp(Λ) ∪ dom-supp(Λ')`** (Definitions 13.2.2, 13.2.9). -/
theorem domSupp_multisectionAdd_subset (Λ Λ' : A.W → ℚ≥0) :
    domSupp (multisectionAdd Λ Λ') ⊆ domSupp Λ ∪ domSupp Λ' := by
  unfold domSupp
  rw [← closure_union]
  refine closure_mono ?_
  rintro x ⟨w, rfl, hw0, hpos⟩
  obtain ⟨a, b, ha, hb, hab⟩ := exists_of_multisectionAdd_pos hpos
  by_cases ha0 : a = 0
  · refine Or.inr ⟨b, b.2, fun hb0 => hw0 ?_, hb⟩
    have e : (a + b : A.P ⁻¹' {A.P w}) = 0 := by rw [ha0, zero_add]; exact Subtype.ext hb0
    exact hab.symm.trans ((congrArg Subtype.val e).trans rfl)
  · refine Or.inl ⟨a, a.2, fun ha0' => ha0 (Subtype.ext ha0'), ha⟩

/-! ### The data of the proof on a set `Q` -/

variable (A) in
/-- **The parameter families of the proof of Theorem 15.3.7 on a set `Q`** (pp. 694–696): a
linear family `t ↦ Λ_t`, `t ∈ ℝ^ℓ`, of structurable sc⁺-multisections (Definition 13.3.6) with
`N(Λ_t)(x) ≤ |t|₁ · h(x)` (from `N(s¹_j) ≤ min{1, h}`), `dom-supp(Λ_t) ⊆ U`, and the
parametrized reduced surjectivity (15.1) at every `x ∈ S_f ∩ Q`. -/
structure GPFamily (f : A.Obj → A.W) (N : A.B.One → ℝ) (U : Set A.Obj) (h : A.Obj → ℝ)
    (Q : Set A.Obj) where
  /-- The number of parameters. -/
  ℓ : ℕ
  /-- The family. -/
  Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0
  isStructurable : ∀ t, IsStructurable A (Λ t)
  isLinear : IsLinearFamily Λ
  norm_le : ∀ t x, pointwiseNorm N (Λ t) x ≤ (∑ j, |t j|) * h x
  domSupp_subset : ∀ t, domSupp (Λ t) ⊆ U
  paramOnto : ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ Q →
    A.X.PObj.levelVal 1 x ∈ solutionSet A.P f → IsParamOntoAt f Λ x

variable {f : A.Obj → A.W} {N : A.B.One → ℝ} {U : Set A.Obj} {h : A.Obj → ℝ}

/-- A family on `Q` is a family on every `Q' ⊆ Q`. -/
def GPFamily.mono {Q Q' : Set A.Obj} (F : GPFamily A f N U h Q) (hQ : Q' ⊆ Q) :
    GPFamily A f N U h Q' where
  ℓ := F.ℓ
  Λ := F.Λ
  isStructurable := F.isStructurable
  isLinear := F.isLinear
  norm_le := F.norm_le
  domSupp_subset := F.domSupp_subset
  paramOnto x hx := F.paramOnto x (hQ hx)

/-- The zero section with weight one is a local representation of `Λ₀` on every open set. -/
theorem isLocalRepOn_zeroMultisection {O : Set A.Obj} (hO : IsOpen O) :
    IsLocalRepOn A (zeroMultisection A) O (k := 1) (fun _ => fiberZero A.P) (fun _ => 1) := by
  classical
  exact ⟨fun _ => one_pos, fun _ => IsScPlusSectionOn.of_isScPlusSection
    StrongBundle.isScPlusSection_fiberZero hO, by simp, fun w _ => by simp [zeroMultisection]⟩

/-- `Λ₀` is structurable once a good system exists (D's `Decoration.zeroTau`). -/
theorem isStructurable_zeroMultisection_of_goodSystem (h𝒰 : Nonempty A.X.GoodSystem) :
    IsStructurable A (zeroMultisection A) :=
  ⟨isScPlusMultisection_zeroMultisection A, _, ⟨Decoration.zeroTau h𝒰.some⟩⟩

/-- **The empty family** (`ℓ = 0`, `Λ = Λ₀`) on `Q = ∅`, given a good system. -/
def GPFamily.zero (h𝒰 : Nonempty A.X.GoodSystem) (hN : A.B.IsAuxNorm N) (hU : ∅ ⊆ U) :
    GPFamily A f N U h ∅ where
  ℓ := 0
  Λ _ := zeroMultisection A
  isStructurable _ := isStructurable_zeroMultisection_of_goodSystem h𝒰
  isLinear x₀ := ⟨univ, 1, fun _ j => j.elim0, fun _ => 1, isOpen_univ, mem_univ _,
    fun _ j => j.elim0, fun t => by
      simp only [paramSec_fin_zero]
      exact isLocalRepOn_zeroMultisection isOpen_univ⟩
  norm_le t x := by rw [pointwiseNorm_zeroMultisection hN]; simp
  domSupp_subset _ := by rw [domSupp_zeroMultisection]; exact hU
  paramOnto _ hx := hx.elim

/-- **The sum of two families** (the step "From local to global", p. 696): `Λ_t ⊕ Λ'_{t'}` is a
family on `Q ∪ Q'`: structurable (Proposition 13.3.12), linear, `N(Λ_t ⊕ Λ'_{t'}) ≤ |(t,t')|₁ h`,
domain support in `U`, and (15.1) at the points of `S_f ∩ (Q ∪ Q')`. -/
def GPFamily.add (hN : A.B.IsAuxNorm N) {Q Q' : Set A.Obj}
    (F : GPFamily A f N U h Q) (F' : GPFamily A f N U h Q') : GPFamily A f N U h (Q ∪ Q') where
  ℓ := F.ℓ + F'.ℓ
  Λ := famAdd F.Λ F'.Λ
  isStructurable t := proposition_13_3_12 (F.isStructurable _) (F'.isStructurable _)
  isLinear := IsLinearFamily.famAdd F.isLinear F'.isLinear
  norm_le t x := by
    refine (pointwiseNorm_multisectionAdd_le hN (F.isStructurable _).1
      (F'.isStructurable _).1 x).trans ?_
    refine (add_le_add (F.norm_le _ x) (F'.norm_le _ x)).trans_eq ?_
    rw [← add_mul, Fin.sum_univ_add]
    rfl
  domSupp_subset t := (domSupp_multisectionAdd_subset _ _).trans
    (union_subset (F.domSupp_subset _) (F'.domSupp_subset _))
  paramOnto x hx hS := by
    rcases hx with hx | hx
    · exact (F.paramOnto x hx hS).famAdd_left F'.isLinear
    · exact IsParamOntoAt.famAdd_right F.isLinear (F'.paramOnto x hx hS)

end SBLocalization

end Polyfold
