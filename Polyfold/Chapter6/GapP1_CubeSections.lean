import Polyfold.Chapter6.GapP1_UnitIntervalSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6,
**Proposition 6.6.3 (3) and (4)** (p. 263; preprint Proposition 6.28) **for families on
`[0, 1]ⁿ`**.  Gap G.65 (a), row V6.32.

# sc⁺-sections over `[0, 1]ⁿ × X` along a family

## The text, paraphrased

For an sc-smooth family `φ : [0, 1]ⁿ → U` in the domain of strong bundle coordinates (paths,
`n = 1`, and homotopies of paths, `n = 2`, in §6.6), `s(y, t) = R(y, f(φ(t)))` is an sc⁺-section
of the pull-back of `Y → X` to `U × [0, 1]ⁿ` with `s(φ(t), t) = f(φ(t))`.

## What is formalized

The project reads the families of §6.6 on `ℝⁿ` (decision D2); `GapP1_UnitIntervalSections`
treats `n = 1` on the M-polyfold `[0, 1]`.  Here the parameter space is `[0, 1]ⁿ` itself:

* `cubePolyfold n`: `[0, 1]ⁿ` (`Fin n → unitInterval`) as an M-polyfold with corners, with the
  `2ⁿ` corner charts `q ↦ (fl (bᵢ) (qᵢ))ᵢ` (`fl true x = x`, `fl false x = 1 − x`) onto
  `[0, 1)ⁿ ⊆ [0, ∞)ⁿ`; it is tame (`cubePolyfold_isTame`), its degeneracy index counts the
  coordinates in `{0, 1}` (`cubePolyfold_degIndex`), `[0, 1]ⁿ × X` is tame when `X` is
  (`prod_cube_isTame`), and the inclusion into `ℝⁿ` is sc-smooth (`UnitCube.isScSmoothMap_val`).
* The partition of unity `a_b(q) = ∏ᵢ cut (bᵢ) (qᵢ)` of the corner charts (`UnitCube.sum_pou`,
  `UnitCube.tsupport_pou_subset`), with `cut true + cut false = 1` from the cut-offs on `[0, 1]`.
* `exists_levelOne_lift_cube`: the principal part along `φ` lifts to `F¹` in each corner chart.
* `exists_isScPlusSection_cube_sum`: for a set `A` of corners, an sc⁺-section of `pr₂*P` over
  `[0, 1]ⁿ × X` with fibre part `(Σ_{b ∈ A} a_b(q)) β(y)·(−R(φ_c(y), f̂(φ(q))))`, by induction
  over `A` with one `exists_isScPlusSection_prodChart` per corner chart.
* **`proposition_6_6_3_three_cube`** (Proposition 6.6.3 (3) on `[0, 1]ⁿ`): an sc⁺-section `S`
  of `pr₂*P` over `[0, 1]ⁿ × X` whose fibre part over `y ∈ dom φ_c` is the text's
  `−β(y)·R(y, f(φ(q)))` (`β = 1` near `φ([0, 1]ⁿ)`, sign of `sectionAdd`), and
  `(f + S)(q, φ(q)) = 0` for **every** `q ∈ [0, 1]ⁿ`.
* `admitsBumpFunctions_prod_cube` and **`proposition_6_6_3_four_cube`** (Proposition 6.6.3 (4)
  on `[0, 1]ⁿ`): `[0, 1]ⁿ × X` admits sc-smooth bump functions when `X` does, so the pull-back of
  `P` has sc⁺-sections through every smooth point of a fibre over a smooth point.

The paracompactness of `[0, 1]ⁿ × X` is Mathlib's instance for a compact factor; that of the
pull-back is an instance argument, as in the `ℝⁿ` forms (`paracompactSpace_pullbackSpace`).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle

/-! ### The M-polyfold `[0, 1]ⁿ` -/

namespace UnitCube

variable (n : ℕ)

/-- The quadrant `[0, ∞)ⁿ` of `ℝⁿ`. -/
def halfC : Set (Fin n → ℝ) := {v | ∀ i, 0 ≤ v i}

/-- `[0, 1)ⁿ` in `ℝⁿ`. -/
def modelO : Set (Fin n → ℝ) := {v | ∀ i, v i < 1} ∩ halfC n

variable {n}

lemma mem_modelO {v : Fin n → ℝ} : v ∈ modelO n ↔ ∀ i, 0 ≤ v i ∧ v i < 1 :=
  ⟨fun h i => ⟨h.2 i, h.1 i⟩, fun h => ⟨fun i => (h i).2, fun i => (h i).1⟩⟩

variable (n)

/-- `ℝⁿ ≅ ℝⁿ ⊕ ℝ⁰` with the constant structures. -/
def quadIso : ScIso (rnSc n) ((ScBanach.const (Fin n → ℝ)).prod (ScBanach.const (Fin 0 → ℝ))) where
  lvl _ := (ContinuousLinearEquiv.prodUnique ℝ (Fin n → ℝ) (Fin 0 → ℝ)).symm
  incl_comm _ _ := Prod.ext rfl (funext fun i => i.elim0)

/-- `[0, ∞)ⁿ` is a partial quadrant of `ℝⁿ` (2021 Definition 1.1.12, preprint 1.11). -/
theorem isPartialQuadrant_halfC : IsPartialQuadrant (rnSc n) (halfC n) :=
  ⟨n, ScBanach.const (Fin 0 → ℝ), quadIso n, by ext v; rfl⟩

lemma isOpen_lt_one : IsOpen {v : Fin n → ℝ | ∀ i, v i < 1} := by
  rw [ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const

/-- `[0, 1)ⁿ` is relatively open in `[0, ∞)ⁿ`. -/
theorem isRelOpen_modelO : IsRelOpenInQuadrant (rnSc n) (halfC n) (modelO n) :=
  ⟨isPartialQuadrant_halfC n, _, isOpen_lt_one n, rfl⟩

/-- The local model `([0, 1)ⁿ, [0, ∞)ⁿ, ℝⁿ)` (identity retraction). -/
def model : LocalModel := LocalModel.ofRelOpen (isRelOpen_modelO n)

/-! ### The `2ⁿ` corner charts -/

/-- `fl true x = x`, `fl false x = 1 − x`. -/
def fl (b : Bool) (x : ℝ) : ℝ := if b then x else 1 - x

lemma fl_fl (b : Bool) (x : ℝ) : fl b (fl b x) = x := by
  cases b <;> simp [fl]

lemma contDiff_fl (b : Bool) : ContDiff ℝ ∞ (fl b) := by
  cases b
  · exact contDiff_const.sub contDiff_id
  · exact contDiff_id

lemma fl_mem_Icc (b : Bool) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : fl b x ∈ Icc (0 : ℝ) 1 := by
  cases b
  · simp only [fl, Bool.false_eq_true, if_false]
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · exact hx

lemma projIcc_fl (b : Bool) {x : ℝ} (hx : 0 ≤ x ∧ x < 1) :
    ((projIcc (0 : ℝ) 1 zero_le_one (fl b x) : unitInterval) : ℝ) = fl b x := by
  rw [projIcc_of_mem _ (fl_mem_Icc b ⟨hx.1, hx.2.le⟩)]

variable {n}

/-- **The corner chart of `[0, 1]ⁿ` at the corner `b`**: `q ↦ (fl (bᵢ) (qᵢ))ᵢ` on the set where
every coordinate is `< 1` after the flip, onto `[0, 1)ⁿ`. -/
def chart (b : Fin n → Bool) : MChart (Fin n → unitInterval) where
  model := model n
  toPartialEquiv :=
    { toFun := fun q i => fl (b i) (q i)
      invFun := fun v i => projIcc (0 : ℝ) 1 zero_le_one (fl (b i) (v i))
      source := {q | ∀ i, fl (b i) (q i) < 1}
      target := modelO n
      map_source' := fun q hq => mem_modelO.2 fun i => ⟨(fl_mem_Icc (b i) (q i).2).1, hq i⟩
      map_target' := fun v hv i => by
        change fl (b i) ((projIcc (0 : ℝ) 1 zero_le_one (fl (b i) (v i)) : unitInterval) : ℝ) < 1
        rw [projIcc_fl (b i) (mem_modelO.1 hv i), fl_fl]
        exact (mem_modelO.1 hv i).2
      left_inv' := fun q _ => funext fun i => by
        change projIcc (0 : ℝ) 1 zero_le_one (fl (b i) (fl (b i) (q i))) = q i
        rw [fl_fl, projIcc_val]
      right_inv' := fun v hv => funext fun i => by
        change fl (b i) ((projIcc (0 : ℝ) 1 zero_le_one (fl (b i) (v i)) : unitInterval) : ℝ) =
          v i
        rw [projIcc_fl (b i) (mem_modelO.1 hv i), fl_fl] }
  isOpen_source := by
    change IsOpen {q : Fin n → unitInterval | ∀ i, fl (b i) (q i) < 1}
    rw [ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt
      ((contDiff_fl (b i)).continuous.comp (continuous_subtype_val.comp (continuous_apply i)))
      continuous_const
  target_eq := rfl
  continuousOn_toFun := (continuous_pi fun i => (contDiff_fl (b i)).continuous.comp
    (continuous_subtype_val.comp (continuous_apply i))).continuousOn
  continuousOn_invFun := (continuous_pi fun i =>
    (continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).comp
      ((contDiff_fl (b i)).continuous.comp (continuous_apply i))).continuousOn

lemma chart_source (b : Fin n → Bool) :
    (chart b).source = {q : Fin n → unitInterval | ∀ i, fl (b i) (q i) < 1} := rfl

lemma chart_apply (b : Fin n → Bool) (q : Fin n → unitInterval) :
    @Eq (Fin n → ℝ) (chart b q) (fun i => fl (b i) (q i)) := rfl

/-- The coordinate change `v ↦ (fl (b'ᵢ) (fl (bᵢ) (vᵢ)))ᵢ`. -/
def trans (b b' : Fin n → Bool) (v : Fin n → ℝ) : Fin n → ℝ := fun i => fl (b' i) (fl (b i) (v i))

lemma contDiff_trans (b b' : Fin n → Bool) : ContDiff ℝ ∞ (trans b b') :=
  contDiff_pi.2 fun i => (contDiff_fl (b' i)).comp ((contDiff_fl (b i)).comp
    (contDiff_apply ℝ ℝ i))

lemma chart_transition_eqOn (b b' : Fin n → Bool) :
    EqOn ((chart b).transition (chart b')) (trans b b') (modelO n) := by
  intro v hv
  funext i
  change fl (b' i) ((projIcc (0 : ℝ) 1 zero_le_one (fl (b i) (v i)) : unitInterval) : ℝ) = _
  rw [projIcc_fl (b i) (mem_modelO.1 hv i)]
  rfl

/-- **The corner charts are sc-smoothly compatible**: the transition maps are the affine maps
`trans b b'`, which are `C^∞`. -/
theorem chart_compatible (b b' : Fin n → Bool) : (chart b).Compatible (chart b') := by
  refine ⟨?_, ?_⟩
  · have hsub : (chart b).overlap (chart b') ⊆ modelO n := (chart b).overlap_subset (chart b')
    refine (isScSmoothRetractMap_const_of_contDiff_of_mapsTo (V := Fin n → ℝ) (V' := Fin n → ℝ)
      ((chart b).isScRetract_overlap (chart b')) (contDiff_trans b b') ?_).congr ?_
    · intro v hv
      rw [← chart_transition_eqOn b b' (hsub hv)]
      exact (chart b).transition_mapsTo (chart b') hv
    · exact fun v hv => (chart_transition_eqOn b b' (hsub hv)).symm
  · have hsub : (chart b').overlap (chart b) ⊆ modelO n := (chart b').overlap_subset (chart b)
    refine (isScSmoothRetractMap_const_of_contDiff_of_mapsTo (V := Fin n → ℝ) (V' := Fin n → ℝ)
      ((chart b').isScRetract_overlap (chart b)) (contDiff_trans b' b) ?_).congr ?_
    · intro v hv
      rw [← chart_transition_eqOn b' b (hsub hv)]
      exact (chart b').transition_mapsTo (chart b) hv
    · exact fun v hv => (chart_transition_eqOn b' b (hsub hv)).symm

/-- The corner of the chart around `q`: `bᵢ = true` iff `qᵢ < 1`. -/
def corner (q : Fin n → unitInterval) : Fin n → Bool := fun i => decide ((q i : ℝ) < 1)

lemma mem_chart_corner (q : Fin n → unitInterval) : q ∈ (chart (corner q)).source := by
  intro i
  by_cases h : ((q i : unitInterval) : ℝ) < 1
  · rw [show corner q i = true by simp [corner, h]]
    exact h
  · have h0 : (0 : ℝ) < q i := by linarith [not_lt.1 h]
    rw [show corner q i = false by simp [corner, h]]
    change 1 - ((q i : unitInterval) : ℝ) < 1
    linarith

end UnitCube

open UnitCube

/-- **`[0, 1]ⁿ` as an M-polyfold with corners** (2021 Definition 2.3.4, preprint 2.13; the
parameter space of the families of §6.6): the atlas of the `2ⁿ` corner charts
`q ↦ (fl (bᵢ) (qᵢ))ᵢ`, all onto `[0, 1)ⁿ ⊆ [0, ∞)ⁿ` with the identity retraction. -/
def cubePolyfold (n : ℕ) : MPolyfold (Fin n → unitInterval) where
  atlas :=
    { charts := range (chart (n := n))
      compatible := by
        rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
        exact chart_compatible b b'
      cover := fun q => ⟨chart (corner q), ⟨_, rfl⟩, mem_chart_corner q⟩ }

namespace UnitCube

variable {n : ℕ}

lemma isChart_chart (b : Fin n → Bool) : (cubePolyfold n).IsChart (chart b) :=
  (cubePolyfold n).isChart_of_mem ⟨b, rfl⟩

/-- **The inclusion `[0, 1]ⁿ → ℝⁿ` is sc-smooth**: in the corner chart `b` its representative is
`v ↦ (fl (bᵢ) (vᵢ))ᵢ` on `[0, 1)ⁿ`. -/
theorem isScSmoothMap_val :
    (cubePolyfold n).IsScSmoothMap (rnPolyfold n) fun q i => (q i : ℝ) := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ
    (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)).continuousOn
    fun q _ => ?_
  set b := corner q
  refine ⟨chart b, rnChart n 0, (chart b).source, isChart_chart b, isChart_rnChart 0,
    (chart b).isOpen_source, mem_chart_corner q, fun _ hs => ⟨mem_univ _, hs⟩,
    fun _ _ => mem_univ _, ?_⟩
  rw [(chart b).image_source]
  refine (isScSmoothRetractMap_const_of_contDiff_of_mapsTo (V := Fin n → ℝ) (V' := Fin n → ℝ)
    (g := fun v i => fl (b i) (v i)) (chart b).model.isScRetract
    (contDiff_pi.2 fun i => (contDiff_fl (b i)).comp (contDiff_apply ℝ ℝ i))
    (mapsTo_univ _ _)).congr ?_
  intro (v : Fin n → ℝ) hv
  funext i
  change fl (b i) (v i) =
    ((projIcc (0 : ℝ) 1 zero_le_one (fl (b i) (v i)) : unitInterval) : ℝ) - 0
  rw [projIcc_fl (b i) (mem_modelO.1 hv i), sub_zero]

/-- A `C^∞` function of the coordinates is sc-smooth on `[0, 1]ⁿ`. -/
theorem isScSmoothMap_cube_real_of_contDiff {g : (Fin n → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) :
    (cubePolyfold n).IsScSmoothMap realPolyfold fun q => g fun i => (q i : ℝ) :=
  (isScSmoothMap_rn_real_of_contDiff hg).comp isScSmoothMap_val

end UnitCube

/-! ### Tameness and the corners of `[0, 1]ⁿ` -/

namespace UnitCube

variable {n : ℕ}

/-- The model `([0, 1)ⁿ, [0, ∞)ⁿ, ℝⁿ)` is a tame retract (the identity retraction is tame). -/
lemma isTameRetract_model : IsTameRetract (rnSc n) (halfC n) (modelO n) :=
  ⟨ScRetraction.id (isRelOpen_modelO n), image_id _, ScRetraction.id_isTame (isRelOpen_modelO n)⟩

/-- The degeneracy index in a corner chart: the number of vanishing coordinates. -/
lemma degIndex_model {v : Fin n → ℝ} (hv : v ∈ halfC n) :
    Polyfold.degIndex (rnSc n) (halfC n) v = (Finset.univ.filter fun i => v i = 0).card := by
  rw [Polyfold.degIndex_eq (quadIso n) (by ext; rfl) hv]
  rfl

end UnitCube

open UnitCube in
/-- `[0, 1]ⁿ` is a **tame** M-polyfold (2021 Definition 2.5.7, preprint 2.37). -/
theorem cubePolyfold_isTame (n : ℕ) : (cubePolyfold n).IsTame :=
  MPolyfold.isTame_of_forall_exists_chart _ fun q =>
    ⟨chart (corner q), isChart_chart _, mem_chart_corner q, isTameRetract_model⟩

open UnitCube in
/-- **The corners of `[0, 1]ⁿ`**: the degeneracy index (2021 Definition 2.4.1, preprint 2.22) of
`q` is the number of coordinates `qᵢ ∈ {0, 1}` (so `[0, 1]ⁿ` is the M-polyfold with corners of
the text's families, with `∂[0, 1]ⁿ` the points with some `qᵢ ∈ {0, 1}`). -/
theorem cubePolyfold_degIndex {n : ℕ} (q : Fin n → unitInterval) :
    (cubePolyfold n).degIndex q =
      (Finset.univ.filter fun i => (q i : ℝ) = 0 ∨ (q i : ℝ) = 1).card := by
  rw [(cubePolyfold n).degIndex_eq_chartDegIndex_of_isTameRetract (isChart_chart (corner q))
    isTameRetract_model (mem_chart_corner q)]
  change Polyfold.degIndex (rnSc n) (halfC n) (fun i => fl (corner q i) (q i)) = _
  rw [degIndex_model fun i => (fl_mem_Icc _ (q i).2).1]
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  by_cases h : ((q i : unitInterval) : ℝ) < 1
  · rw [show corner q i = true by simp [corner, h]]
    change ((q i : unitInterval) : ℝ) = 0 ↔ _
    exact ⟨Or.inl, fun h' => h'.resolve_right (ne_of_lt h)⟩
  · rw [show corner q i = false by simp [corner, h]]
    have h1 : ((q i : unitInterval) : ℝ) = 1 := le_antisymm (q i).2.2 (not_lt.1 h)
    change 1 - ((q i : unitInterval) : ℝ) = 0 ↔ _
    rw [h1]
    norm_num

/-- `[0, 1]ⁿ × X` is tame when `X` is, with `d(q, x) = d(q) + d_X(x)` (exposition Lemma 4.D,
`MPolyfold.isTame_prod`). -/
theorem prod_cube_isTame {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {n : ℕ} (hX : PX.IsTame) : ((cubePolyfold n).prod PX).IsTame :=
  (MPolyfold.isTame_prod (cubePolyfold n) PX (cubePolyfold_isTame n) hX).1

/-! ### The partition of unity of the corner charts -/

namespace UnitCube

/-- `cut true = a_L` (`= 0` for `t ≥ 2/3`), `cut false = a_R` (`= 0` for `t ≤ 1/3`). -/
def cut (b : Bool) (t : ℝ) : ℝ := if b then intervalCutL t else intervalCutR t

lemma contDiff_cut (b : Bool) : ContDiff ℝ ∞ (cut b) := by
  cases b
  · exact contDiff_intervalCutR
  · exact contDiff_const.sub contDiff_intervalCutR

lemma cut_true_add_cut_false (t : ℝ) : cut true t + cut false t = 1 := by
  simp only [cut, if_true, Bool.false_eq_true, if_false, intervalCutL]
  ring

/-- Where `cut b` does not vanish, the flipped coordinate is `≤ 2/3`. -/
lemma fl_le_of_cut_ne_zero {b : Bool} {t : ℝ} (h : cut b t ≠ 0) : fl b t ≤ 2 / 3 := by
  cases b
  · simp only [cut, Bool.false_eq_true, if_false] at h
    simp only [fl, Bool.false_eq_true, if_false]
    by_contra h'
    exact h (intervalCutR_eq_zero (by linarith))
  · simp only [cut, if_true] at h
    simp only [fl, if_true]
    by_contra h'
    exact h (intervalCutL_eq_zero (by linarith))

variable {n : ℕ}

/-- The partition function of the corner `b`: `a_b(q) = ∏ᵢ cut (bᵢ) (qᵢ)`. -/
def pou (b : Fin n → Bool) (v : Fin n → ℝ) : ℝ := ∏ i, cut (b i) (v i)

lemma contDiff_pou (b : Fin n → Bool) : ContDiff ℝ ∞ (pou b) :=
  contDiff_prod fun i _ => (contDiff_cut (b i)).comp (contDiff_apply ℝ ℝ i)

/-- **`Σ_b a_b = 1`**: `∏ᵢ (a_L + a_R)(qᵢ) = 1`, expanded over the corners. -/
lemma sum_pou (v : Fin n → ℝ) : ∑ b, pou b v = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
    (fun i c => cut c (v i))
  rw [Fintype.piFinset_univ] at h
  rw [show (∑ b, pou b v) = ∑ b : Fin n → Bool, ∏ i, cut (b i) (v i) from rfl, ← h]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Fintype.sum_bool, cut_true_add_cut_false]

/-- The closed set `{q | ∀ i, fl (bᵢ) (qᵢ) ≤ 2/3}` inside the chart `b`. -/
def inner (b : Fin n → Bool) : Set (Fin n → unitInterval) :=
  {q | ∀ i, fl (b i) (q i) ≤ 2 / 3}

lemma isClosed_inner (b : Fin n → Bool) : IsClosed (inner b) := by
  rw [inner, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le
    ((contDiff_fl (b i)).continuous.comp (continuous_subtype_val.comp (continuous_apply i)))
    continuous_const

lemma inner_subset (b : Fin n → Bool) : inner b ⊆ (chart b).source :=
  fun _ hq i => lt_of_le_of_lt (hq i) (by norm_num)

lemma mem_inner_of_pou_ne_zero {b : Fin n → Bool} {q : Fin n → unitInterval}
    (h : pou b (fun i => (q i : ℝ)) ≠ 0) : q ∈ inner b := fun i =>
  fl_le_of_cut_ne_zero ((Finset.prod_ne_zero_iff.1 h) i (Finset.mem_univ _))

lemma tsupport_pou_subset (b : Fin n → Bool) :
    tsupport (fun q : Fin n → unitInterval => pou b fun i => (q i : ℝ)) ⊆ (chart b).source :=
  (closure_minimal (fun _ hq => mem_inner_of_pou_ne_zero hq) (isClosed_inner b)).trans
    (inner_subset b)

end UnitCube

/-! ### Proposition 6.6.3 (3) on `[0, 1]ⁿ` -/

section CubeSections

open UnitCube

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {n : ℕ}

/-- **The principal part along a family on `[0, 1]ⁿ` lifts to `F¹`**: for an sc-smooth section
`f`, an sc-smooth `φ : [0, 1]ⁿ → dom φ_c` and a chart `χ` of `[0, 1]ⁿ` on the model `[0, 1)ⁿ`
(the corner charts), `v ↦ Φ(f(φ(χ⁻¹(v))))₂` lifts to an sc-smooth `ê : O_χ → F¹` (the parameter
space is finite-dimensional with the constant sc-structure; as
`exists_levelOne_lift_unitInterval`). -/
theorem exists_levelOne_lift_cube (hf : B.IsScSmoothSection f)
    {φ : (Fin n → unitInterval) → X} (hφ : (cubePolyfold n).IsScSmoothMap PX φ)
    {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts) (hφc : ∀ q, φ q ∈ c.φ.source)
    {χ : MChart (Fin n → unitInterval)} (hχ : (cubePolyfold n).IsChart χ)
    (hm : χ.model = UnitCube.model n) :
    ∃ ê : χ.model.E 0 → c.F 1,
      IsScSmoothRetractMap χ.model.E χ.model.C χ.model.O c.F.shift univ univ ê ∧
      ∀ q ∈ χ.source, c.F.toBase 1 (ê (χ q)) = (c (f (φ q))).2 := by
  have hfs : IsSection P f := hf.1
  have hfφ : (cubePolyfold n).IsScSmoothMap B.toMPolyfold0 (f ∘ φ) := hf.2.comp hφ
  have h1 := hfφ.smooth χ (c.toMChart B.continuous) hχ (B.isChart_toMChart hc) χ.source
    χ.isOpen_source (fun _ ht => ⟨mem_univ _, ht⟩)
    (fun t _ => c.mem_source_of_proj (by rw [Function.comp_apply, hfs]; exact hφc t))
  rw [χ.image_source] at h1
  rcases χ with ⟨m, e, h₁, h₂, h₃, h₄⟩
  subst hm
  set g : (Fin n → ℝ) → (c.φ.model.E.prod c.F) 0 := fun v => c (f (φ (e.symm v))) with hgdef
  have hU : IsScDomain (rnSc n) (modelO n) := (isRelOpen_modelO n).isScDomain
  have hg : IsScSmooth (E := rnSc n) (F := c.φ.model.E.prod c.F) (modelO n) g :=
    h1.comp_isScSmooth (ScRetraction.id (isRelOpen_modelO n)) (image_id _)
  have hg1 := hg.shift hU
  have hlv : (rnSc n).lvlSet (modelO n) 1 = modelO n := by
    ext v
    rw [ScBanach.mem_lvlSet, ScBanach.const_toBase]
  rw [hlv] at hg1
  have hg1' : IsScSmooth (E := rnSc n) (F := c.φ.model.E.shift.prod c.F.shift) (modelO n)
      (fun v => levelMap (E := rnSc n) (F := c.φ.model.E.prod c.F) g 1 v) := hg1
  set ê : (Fin n → ℝ) → c.F 1 :=
    fun v => (levelMap (E := rnSc n) (F := c.φ.model.E.prod c.F) g 1 v).2 with hêdef
  have hê : IsScSmooth (E := rnSc n) (F := c.F.shift) (modelO n) ê := hg1'.snd hU
  have hêbase : ∀ v ∈ modelO n, c.F.toBase 1 (ê v) = (g v).2 := fun v hv => by
    have h := IsSc0.toBase_levelMap (hg 0) (m := 1) (x := v)
      (by rw [ScBanach.mem_lvlSet, ScBanach.const_toBase]; exact hv)
    rw [ScBanach.prod_toBase, ScBanach.const_toBase] at h
    exact congrArg Prod.snd h
  refine ⟨ê, ⟨mapsTo_univ _ _, fun R hR => ?_⟩, fun t ht => ?_⟩
  · refine IsScSmooth.comp R.isScDomain hU hê R.isScSmooth fun w hw => ?_
    have := R.apply_mem_retract hw
    rw [hR] at this
    exact this
  · have hv : e t ∈ modelO n := by
      have := e.map_source ht
      rw [h₂] at this
      exact this
    change c.F.toBase 1 (ê (e t)) = _
    rw [hêbase _ hv]
    change (c (f (φ (e.symm (e t))))).2 = _
    rw [e.left_inv ht]

variable [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]

/-- **The sum over a set `A` of corners**: an sc⁺-section of `pr₂*P` over `[0, 1]ⁿ × X` with fibre
part `(Σ_{b ∈ A} a_b(q)) β(y)·(−R(φ_c(y), f̂(φ(q))))` over `dom φ_c` (induction over `A`, one
`exists_isScPlusSection_prodChart` per corner chart). -/
theorem exists_isScPlusSection_cube_sum (hf : B.IsScSmoothSection f)
    {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts)
    {φ : (Fin n → unitInterval) → X} (hφ : (cubePolyfold n).IsScSmoothMap PX φ)
    (hφc : ∀ q, φ q ∈ c.φ.source) {β₂ : X → ℝ} (hβ₂ : PX.IsScSmoothMap realPolyfold β₂)
    (hβ₂s : tsupport β₂ ⊆ c.φ.source) (A : Finset (Fin n → Bool)) :
    ∃ S : (Fin n → unitInterval) × X →
        pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X),
      (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S ∧
      ∀ q y, y ∈ c.φ.source → (c (S (q, y)).1.2).2 =
        (∑ b ∈ A, pou b (fun i => (q i : ℝ)) * β₂ y) • -(c.R (c.φ y, (c (f (φ q))).2)).2 := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨fiberZero (pullbackProj P Prod.snd), isScPlusSection_fiberZero, fun q y hy => ?_⟩
    rw [Finset.sum_empty, zero_smul]
    exact c.snd_fiberZero hy
  | insert b A hb ih =>
    obtain ⟨SA, hSA, hvA⟩ := ih
    obtain ⟨ê, hê, hêb⟩ := exists_levelOne_lift_cube hf hφ hc hφc (isChart_chart b) rfl
    have hβ : ((cubePolyfold n).prod PX).IsScSmoothMap realPolyfold
        (fun p : (Fin n → unitInterval) × X => pou b (fun i => (p.1 i : ℝ)) * β₂ p.2) :=
      ((isScSmoothMap_cube_real_of_contDiff (contDiff_pou b)).comp
        (MPolyfold.isScSmoothMap_fst (cubePolyfold n) PX)).mul
        (hβ₂.comp (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX))
    have hβs : tsupport (fun p : (Fin n → unitInterval) × X =>
        pou b (fun i => (p.1 i : ℝ)) * β₂ p.2) ⊆ (chart b).source ×ˢ c.φ.source :=
      (tsupport_prod_mul_subset (fun q : Fin n → unitInterval => pou b fun i => (q i : ℝ))
        β₂).trans (prod_mono (tsupport_pou_subset b) hβ₂s)
    set q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X) :=
      ⟨((fun _ => 0, φ fun _ => 0), fiberZero P (φ fun _ => 0)),
        proj_fiberZero P (φ fun _ => 0)⟩
    obtain ⟨Sb, hSb, hvb⟩ := exists_isScPlusSection_prodChart (B := B) (isChart_chart b)
      (ScRetraction.id (isRelOpen_modelO n)) (image_id _) hc hê hβ hβs q₀
    refine ⟨sectionAdd (pullbackProj P Prod.snd) Sb SA, hSb.add hSA, fun q y hy => ?_⟩
    have hb' : (pou b (fun i => (q i : ℝ)) * β₂ y) •
          -(c.R (c.φ y, c.F.toBase 1 (ê (chart b q)))).2 =
        (pou b (fun i => (q i : ℝ)) * β₂ y) • -(c.R (c.φ y, (c (f (φ q))).2)).2 := by
      by_cases hq : q ∈ (chart b).source
      · rw [hêb q hq]
      · have h0 : pou b (fun i => (q i : ℝ)) = 0 := by
          by_contra h
          exact hq (inner_subset b (mem_inner_of_pou_ne_zero h))
        rw [h0, zero_mul, zero_smul, zero_smul]
    rw [sectionAdd_pullback_snd_apply hSb.1 hSA.1 (q, y), c.snd_add hy]
    change (c (Sb (q, y)).1.2).2 + (c (SA (q, y)).1.2).2 = _
    rw [hvb q y hy, hvA q y hy, hb', Finset.sum_insert hb, add_smul]

/-- **2021 Proposition 6.6.3 (3), p. 263, for families on `[0, 1]ⁿ`** (preprint Proposition
6.28 (3)): with sc-smooth bump functions, for an sc-smooth section `f`, a strong bundle chart `c`
of the atlas and an sc-smooth family `φ : [0, 1]ⁿ → dom φ_c`, there are an sc-smooth cut-off `β`
with `supp β ⊆ dom φ_c` and `β = 1` on `φ([0, 1]ⁿ)`, and an sc⁺-section `S` of `pr₂*P` over the
M-polyfold `[0, 1]ⁿ × X` with
* fibre part `−β(y)·R(φ_c(y), f̂(φ(q)))` over `y ∈ dom φ_c` (the text's `s(y, q) = R(y, f(φ(q)))`
  with the sign of `sectionAdd` and the cut-off), and
* `(f + S)(q, φ(q)) = 0` for **every** `q ∈ [0, 1]ⁿ`.
The `2ⁿ` corner charts of `[0, 1]ⁿ` are glued with the partition `Σ_b a_b = 1`
(`exists_isScPlusSection_cube_sum`); for `n = 1` this is `proposition_6_6_3_three_interval` on
`[0, 1]¹`. -/
theorem proposition_6_6_3_three_cube (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScSmoothSection f) {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts)
    {φ : (Fin n → unitInterval) → X} (hφ : (cubePolyfold n).IsScSmoothMap PX φ)
    (hφc : ∀ q, φ q ∈ c.φ.source) :
    ∃ (β₂ : X → ℝ) (S : (Fin n → unitInterval) × X →
        pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)),
      PX.IsScSmoothMap realPolyfold β₂ ∧ tsupport β₂ ⊆ c.φ.source ∧ (∀ q, β₂ (φ q) = 1) ∧
      (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S ∧
      (∀ q y, y ∈ c.φ.source →
        (c (S (q, y)).1.2).2 = -(β₂ y • (c.R (c.φ y, (c (f (φ q))).2)).2)) ∧
      ∀ q, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd)
          (pullbackLift Prod.snd (f ∘ Prod.snd) fun z => hf.1 z.2) S) (q, φ q) := by
  have hfs : IsSection P f := hf.1
  have hφcont : Continuous φ := continuousOn_univ.1 hφ.continuousOn
  obtain ⟨β₂, hβ₂, hβ₂s, hβ₂1⟩ := exists_isScSmoothMap_eq_one_nhdsSet hbump
    (isCompact_range hφcont) c.φ.isOpen_source (range_subset_iff.2 hφc)
  have hβ₂φ : ∀ q, β₂ (φ q) = 1 := fun q => hβ₂1.self_of_nhdsSet (φ q) ⟨q, rfl⟩
  obtain ⟨S, hS, hv⟩ := exists_isScPlusSection_cube_sum hf hc hφ hφc hβ₂ hβ₂s Finset.univ
  have hval : ∀ q y, y ∈ c.φ.source →
      (c (S (q, y)).1.2).2 = -(β₂ y • (c.R (c.φ y, (c (f (φ q))).2)).2) := by
    intro q y hy
    rw [hv q y hy, ← Finset.sum_mul, sum_pou, one_mul, smul_neg]
  refine ⟨β₂, S, hβ₂, hβ₂s, hβ₂φ, hS, hval, fun t => ?_⟩
  -- `(f + S)(q, φ(q)) = 0`
  have hL : IsSection (pullbackProj P Prod.snd)
      (pullbackLift Prod.snd (f ∘ Prod.snd) fun z : (Fin n → unitInterval) × X => hfs z.2) :=
    isSection_pullbackLift _
  have hG : IsSection (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (pullbackLift Prod.snd (f ∘ Prod.snd) fun z : (Fin n → unitInterval) × X => hfs z.2) S) :=
    hL.sectionAdd hS.1
  rw [isZeroAt_pullback_snd_iff hG]
  set σ : X → Y := fun x => (sectionAdd (pullbackProj P Prod.snd)
      (pullbackLift Prod.snd (f ∘ Prod.snd) fun z : (Fin n → unitInterval) × X => hfs z.2) S
        (t, x)).1.2 with hσdef
  have hσ : IsSection P σ := fun x => mem_fiber_of_isSection_pullback_snd hG (t, x)
  have hxt : φ t ∈ c.φ.source := hφc t
  change IsZeroAt P σ (φ t)
  refine (c.isZeroAt_iff hσ hxt).2 ?_
  change (c (σ (c.φ.symm (c.φ (φ t))))).2 = 0
  rw [c.φ.symm_apply_apply hxt, hσdef]
  simp only
  rw [sectionAdd_pullback_snd_apply hL hS.1 (t, φ t), c.snd_add hxt]
  change (c (f (φ t))).2 + (c (S (t, φ t)).1.2).2 = 0
  rw [hval t (φ t) hxt, hβ₂φ t, one_smul]
  have hK : (c.φ (φ t), (c (f (φ t))).2) ∈ c.R '' (c.U ×ˢ univ) := by
    have h := c.toPartialEquiv.map_source (c.mem_source_of_proj (by rw [hfs]; exact hxt))
    rw [c.target_eq] at h
    have e : c (f (φ t)) = (c.φ (φ t), (c (f (φ t))).2) :=
      Prod.ext (by rw [c.fst_apply (by rw [hfs]; exact hxt), hfs]) rfl
    exact e ▸ h
  have hρ := StrongRetr.ρ_eq_self_of_mem_K c.isRetraction
    (StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ c.φ.mapsTo_model _ hxt)) hK
  change (c.R (c.φ (φ t), (c (f (φ t))).2)).2 = (c (f (φ t))).2 at hρ
  rw [hρ]
  exact add_neg_cancel _

/-! ### Proposition 6.6.3 (4) on `[0, 1]ⁿ` -/

/-- **`[0, 1]ⁿ × X` admits sc-smooth bump functions when `X` does** (Definition 5.3.1, preprint
5.9): around `(q, x)`, the product `b(q')β(x')` of a `C^∞` bump `b` of `ℝⁿ` restricted to
`[0, 1]ⁿ` and a bump `β` of `X` (as `admitsBumpFunctions_prod_unitInterval`). -/
theorem admitsBumpFunctions_prod_cube (hbump : PX.AdmitsBumpFunctions) :
    ((cubePolyfold n).prod PX).AdmitsBumpFunctions := by
  rintro ⟨r, x⟩ U hU hxU
  obtain ⟨U₁, U₂, hU₁, hU₂, hr, hx, hsub⟩ := isOpen_prod_iff.1 hU r x hxU
  obtain ⟨β₂, hβ₂, hβ₂x, hβ₂s⟩ := hbump x U₂ hU₂ hx
  set e : (Fin n → unitInterval) → (Fin n → ℝ) := fun q i => (q i : ℝ) with he
  have hind : Topology.IsInducing e :=
    Topology.IsInducing.piMap (f := fun _ : Fin n => (Subtype.val : unitInterval → ℝ))
      fun _ => Topology.IsInducing.subtypeVal
  obtain ⟨W, hW, hWU⟩ := hind.isOpen_iff.1 hU₁
  have hrW : e r ∈ W := by
    rw [← hWU] at hr
    exact hr
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW (e r) hrW
  let b : ContDiffBump (e r) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨fun p => b (e p.1) * β₂ p.2, ?_, ?_, ?_⟩
  · exact ((isScSmoothMap_cube_real_of_contDiff b.contDiff).comp
      (MPolyfold.isScSmoothMap_fst (cubePolyfold n) PX)).mul
      (hβ₂.comp (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX))
  · change b (e r) * β₂ x ≠ 0
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)), one_mul]
    exact hβ₂x
  · refine (tsupport_prod_mul_subset (fun q => b (e q)) β₂).trans
      ((prod_mono ?_ hβ₂s).trans hsub)
    have hcl : IsClosed (e ⁻¹' Metric.closedBall (e r) (ε / 2)) :=
      Metric.isClosed_closedBall.preimage hind.continuous
    refine (closure_minimal (fun q hq => ?_) hcl).trans fun q hq => ?_
    · have h : e q ∈ Function.support b := hq
      rw [b.support_eq] at h
      exact Metric.ball_subset_closedBall h
    · rw [← hWU]
      exact hball (Metric.closedBall_subset_ball (by linarith) hq)

/-- **2021 Proposition 6.6.3 (4), p. 263, on `[0, 1]ⁿ`** (preprint Proposition 6.28 (4)): with
sc-smooth bump functions, the pull-back of `P` to `[0, 1]ⁿ × X` has sc⁺-sections through every
smooth point of a fibre over a smooth point (Lemma 5.3.3, preprint 5.11, for `[0, 1]ⁿ × X`). -/
theorem proposition_6_6_3_four_cube (hbump : PX.AdmitsBumpFunctions) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).HasScPlusSectionsThrough :=
  MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough (admitsBumpFunctions_prod_cube hbump)

end CubeSections

end Polyfold
