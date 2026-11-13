import Polyfold.Chapter6.PathsInterval

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, pp. 272–273
(preprint §6.5, pp. 227–228): **the path category `PX` with paths on `[0, 1]`**.
Gap G.65, row V6.52.

# The category of classes of sc-smooth paths `[0, 1] → X`

## The text, paraphrased

For an sc-smooth `φ : [0, 1] → X`, `[φ]` is its sc-smooth homotopy class with end points fixed.
For `t([φ]) = s([ψ])`, `[ψ] ∗ [φ]` is the class of `γ(s) = φ(β(s))` on `[0, 1/2]` and
`γ(s) = ψ(β(s) − 1)` on `[1/2, 1]`, where `β : [0, 1] → [0, 2]` is smooth, `β(0) = 0`,
`β = 1` near `1/2`, `β' ≥ 0`, `β([0, 1/2]) = [0, 1]`, `β([1/2, 1]) = [1, 2]`, `β(1) = 2`.  This
gives a category `PX` whose objects are the smooth points of `X`.

## What is formalized

The project reads the paths of the category on `ℝ` (`PathCat`, decision D2).  Here:

* Maps out of `[0, 1]` and `[0, 1]²`: `isScSmoothMap_toUnitInterval_of_rn` (a map into `ℝ` with
  values in `[0, 1]` is sc-smooth into the M-polyfold `[0, 1]` when it is sc-smooth into `ℝ`),
  `isScSmoothMap_interval_of_contDiff`, `isScSmoothMap_square_of_contDiff` (restrictions of
  `C^∞` maps preserving `[0, 1]`, `[0, 1]²` are sc-smooth), `isScSmoothMap_square_pt2`.
* `IsScHomotopyRelI`, `ScHomotopicI`: sc-smooth homotopies `[0, 1]² → X` (`unitSquarePolyfold`)
  with the end points fixed, an equivalence relation (`ScHomotopicI.refl`, `.symm`, `.trans`).
* `scHomotopicI_iff`: two paths on `[0, 1]` are homotopic in this sense iff their paths
  `unitPath φ = φ ∘ sin²(π · /2)` on `ℝ` are homotopic in the sense of `PathCat`.
* `ScPathI`, `ScPathI.concat` (**the text's `γ`**, with `β(s) = κ(3s) + κ(3s − 2)`,
  `concat_toFun_of_le`, `concat_toFun_of_ge`, `betaConcat` and its properties), `ScPathI.const`,
  `ScPathI.reverse`; **`PathCatI`**, a category (`PathCatI.category`) and a groupoid
  (`PathCatI.groupoid`) with `[φ] ≫ [ψ] = [ψ] ∗ [φ]` (`PathCatI.comp_mk`).
* `PathCatI.toPathCat`: the functor `[φ] ↦ [unitPath φ]` to the category of decision D2; it is
  full and faithful (`PathCatI.toPathCat_full`, `PathCatI.toPathCat_faithful`), bijective on
  objects, so the two readings give isomorphic categories.
-/

open Set Filter Topology Function CategoryTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

open UnitInterval

local notation "κ" => Real.smoothTransition

/-! ### Sc-smooth maps out of `[0, 1]` and `[0, 1]²` -/

section Maps

/-- A `C^∞` map `ℝ¹ × ℝ¹ → ℝᵐ` is sc-smooth on the product M-polyfold `ℝ¹ × ℝ¹`. -/
theorem isScSmoothMap_rnProd_of_contDiff {m : ℕ} {G : (Fin 1 → ℝ) × (Fin 1 → ℝ) → Fin m → ℝ}
    (hG : ContDiff ℝ ∞ G) :
    ((rnPolyfold 1).prod (rnPolyfold 1)).IsScSmoothMap (rnPolyfold m) G := by
  refine MPolyfold.isScSmoothMap_of_local fun x => ⟨(rnChart 1 0).prod (rnChart 1 0),
    rnChart m 0, univ, MPolyfold.IsChart.prod (isChart_rnChart 0) (isChart_rnChart 0),
    isChart_rnChart 0, isOpen_univ, mem_univ x, fun _ _ => ⟨mem_univ _, mem_univ _⟩,
    mapsTo_univ _ _, ?_⟩
  have hF : ContDiff ℝ ∞ fun w : (Fin 1 → ℝ) × (Fin 1 → ℝ) => G (w.1 + 0, w.2 + 0) - 0 :=
    (hG.comp ((contDiff_fst.add contDiff_const).prodMk (contDiff_snd.add contDiff_const))).sub
      contDiff_const
  refine ⟨fun _ _ => mem_univ _, fun R _ => ?_⟩
  exact IsScSmooth.comp R.isScDomain (isScDomain_univ _)
    (IsScSmooth.of_contDiffOn_finiteDimensional (V := Fin m → ℝ) (isScDomain_univ _)
      hF.contDiffOn) R.isScSmooth (mapsTo_univ _ _)

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}

/-- **Corestriction to `[0, 1]`**: a map `f : Z → [0, 1]` is sc-smooth into the M-polyfold
`[0, 1]` if it is sc-smooth into `ℝ`; in the charts `t` and `1 − t` its representatives are those
into `ℝ` composed with `v ↦ v` and `v ↦ 1 − v`. -/
theorem isScSmoothMap_toUnitInterval_of_rn {f : Z → unitInterval}
    (hf : PZ.IsScSmoothMap (rnPolyfold 1) fun z _ => (f z : ℝ)) :
    PZ.IsScSmoothMap unitIntervalPolyfold f := by
  have hfc : Continuous f :=
    continuous_induced_rng.2 ((continuous_apply 0).comp (continuousOn_univ.1 hf.continuousOn))
  refine MPolyfold.isScSmoothMap_of_local fun z => ?_
  obtain ⟨φ, hφ, hzφ⟩ := PZ.exists_isChart_mem_source z
  rcases mem_leftChart_or_rightChart (f z) with hl | hr
  · set V := φ.source ∩ f ⁻¹' leftChart.source with hV
    have hVo : IsOpen V := φ.isOpen_source.inter (leftChart.isOpen_source.preimage hfc)
    have h1 := hf.smooth φ (rnChart 1 0) hφ (isChart_rnChart 0) V hVo
      (fun _ hy => ⟨mem_univ _, hy.1⟩) (fun _ _ => mem_univ _)
    refine ⟨φ, leftChart, V, hφ, isChart_leftChart, hVo, ⟨hzφ, hl⟩, fun _ hy => hy.1,
      fun _ hy => hy.2, ⟨?_, fun R hR => ?_⟩⟩
    · rintro _ ⟨y, hy, rfl⟩
      change leftChart (f (φ.symm (φ y))) ∈ _
      rw [φ.symm_apply_apply hy.1]
      exact leftChart.mapsTo_model _ hy.2
    · have hA : IsScSmooth (E := rnSc 1) (F := rnSc 1) univ (fun v : Fin 1 → ℝ => v + 0) :=
        IsScSmooth.of_contDiffOn_finiteDimensional (isScDomain_univ _)
          (contDiff_id.add contDiff_const).contDiffOn
      refine (IsScSmooth.comp R.isScDomain (isScDomain_univ _) hA (h1.comp_isScSmooth R hR)
        (mapsTo_univ _ _)).congr R.isScDomain fun w _ => ?_
      change (fun _ : Fin 1 => (f (φ.symm (R w)) : ℝ)) - 0 + 0 =
        fun _ : Fin 1 => (f (φ.symm (R w)) : ℝ)
      rw [sub_zero, add_zero]
  · set V := φ.source ∩ f ⁻¹' rightChart.source with hV
    have hVo : IsOpen V := φ.isOpen_source.inter (rightChart.isOpen_source.preimage hfc)
    have h1 := hf.smooth φ (rnChart 1 0) hφ (isChart_rnChart 0) V hVo
      (fun _ hy => ⟨mem_univ _, hy.1⟩) (fun _ _ => mem_univ _)
    refine ⟨φ, rightChart, V, hφ, isChart_rightChart, hVo, ⟨hzφ, hr⟩, fun _ hy => hy.1,
      fun _ hy => hy.2, ⟨?_, fun R hR => ?_⟩⟩
    · rintro _ ⟨y, hy, rfl⟩
      change rightChart (f (φ.symm (φ y))) ∈ _
      rw [φ.symm_apply_apply hy.1]
      exact rightChart.mapsTo_model _ hy.2
    · have hA : IsScSmooth (E := rnSc 1) (F := rnSc 1) univ
          (fun v : Fin 1 → ℝ => (fun _ => (1 : ℝ)) - v) :=
        IsScSmooth.of_contDiffOn_finiteDimensional (isScDomain_univ _)
          (contDiff_const.sub contDiff_id).contDiffOn
      refine (IsScSmooth.comp R.isScDomain (isScDomain_univ _) hA (h1.comp_isScSmooth R hR)
        (mapsTo_univ _ _)).congr R.isScDomain fun w _ => ?_
      change (fun _ : Fin 1 => (1 : ℝ)) - ((fun _ : Fin 1 => (f (φ.symm (R w)) : ℝ)) - 0) =
        fun _ : Fin 1 => 1 - (f (φ.symm (R w)) : ℝ)
      rw [sub_zero]
      rfl

/-- `p ↦ (p₁, p₂) ∈ ℝ¹ × ℝ¹` is sc-smooth on `[0, 1]²`. -/
theorem isScSmoothMap_squareVal :
    unitSquarePolyfold.IsScSmoothMap ((rnPolyfold 1).prod (rnPolyfold 1))
      fun p : unitInterval × unitInterval => ((fun _ => (p.1 : ℝ)), (fun _ => (p.2 : ℝ))) :=
  MPolyfold.IsScSmoothOn.prodMk
    (isScSmoothMap_unitInterval_val.comp (MPolyfold.isScSmoothMap_fst _ _))
    (isScSmoothMap_unitInterval_val.comp (MPolyfold.isScSmoothMap_snd _ _))

/-- **Restrictions of `C^∞` maps `ℝ² → ℝ` preserving `[0, 1]²` are sc-smooth `[0, 1]² → [0, 1]`.**
-/
theorem isScSmoothMap_square_of_contDiff {g : ℝ → ℝ → ℝ}
    (hg : ContDiff ℝ ∞ fun p : ℝ × ℝ => g p.1 p.2)
    (h01 : ∀ τ t : unitInterval, g τ t ∈ Icc (0 : ℝ) 1) :
    unitSquarePolyfold.IsScSmoothMap unitIntervalPolyfold
      fun p => (⟨g p.1 p.2, h01 p.1 p.2⟩ : unitInterval) := by
  refine isScSmoothMap_toUnitInterval_of_rn ?_
  have hG := isScSmoothMap_rnProd_of_contDiff (m := 1)
    (G := fun w _ => g (w.1 0) (w.2 0)) (contDiff_pi.2 fun _ => hg.comp
      (((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_fst).prodMk
        ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd)))
  exact hG.comp isScSmoothMap_squareVal

/-- **Restrictions of `C^∞` maps `ℝ → ℝ` preserving `[0, 1]` are sc-smooth `[0, 1] → [0, 1]`.** -/
theorem isScSmoothMap_interval_of_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (h01 : ∀ t : unitInterval, g t ∈ Icc (0 : ℝ) 1) :
    unitIntervalPolyfold.IsScSmoothMap unitIntervalPolyfold
      fun t => (⟨g t, h01 t⟩ : unitInterval) :=
  isScSmoothMap_toUnitInterval_of_rn ((isScSmoothMap_rn_rn_of_contDiff
    (σ := fun v _ => g (v 0)) (contDiff_pi.2 fun _ => hg.comp (contDiff_apply ℝ ℝ 0))).comp
      isScSmoothMap_unitInterval_val)

/-- `p ↦ (p₁, p₂) ∈ ℝ²` is sc-smooth on `[0, 1]²`. -/
theorem isScSmoothMap_square_pt2 :
    unitSquarePolyfold.IsScSmoothMap (rnPolyfold 2)
      fun p : unitInterval × unitInterval => pt2 p.1 p.2 := by
  have h : ContDiff ℝ ∞ fun w : (Fin 1 → ℝ) × (Fin 1 → ℝ) => pt2 (w.1 0) (w.2 0) := by
    have h₁ : ContDiff ℝ ∞ fun w : (Fin 1 → ℝ) × (Fin 1 → ℝ) => w.1 0 :=
      (contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_fst
    have h₂ : ContDiff ℝ ∞ fun w : (Fin 1 → ℝ) × (Fin 1 → ℝ) => w.2 0 :=
      (contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · simpa only [Fin.zero_eta, Fin.isValue, pt2_apply_zero] using h₁
    · simpa only [Fin.mk_one, Fin.isValue, pt2_apply_one] using h₂
  exact (isScSmoothMap_rnProd_of_contDiff h).comp isScSmoothMap_squareVal

/-! ### Reparametrizations of `[0, 1]` -/

/-- `τ ↦ 1 − τ` on `[0, 1]`. -/
def oneSubI (τ : unitInterval) : unitInterval := ⟨1 - τ, Set.Icc.mem_iff_one_sub_mem.mp τ.2⟩

@[simp] lemma coe_oneSubI (τ : unitInterval) : (oneSubI τ : ℝ) = 1 - τ := rfl

lemma oneSubI_zero : oneSubI 0 = 1 := Subtype.ext (by simp)

lemma oneSubI_one : oneSubI 1 = 0 := Subtype.ext (by simp)

theorem isScSmoothMap_oneSubI : unitIntervalPolyfold.IsScSmoothMap unitIntervalPolyfold oneSubI :=
  isScSmoothMap_interval_of_contDiff (g := fun t => 1 - t) (contDiff_const.sub contDiff_id)
    fun τ => (oneSubI τ).2

/-- `τ ↦ κ(3τ − c)` on `[0, 1]` (`κ` the smooth transition function). -/
def kapI (c : ℝ) (τ : unitInterval) : unitInterval :=
  ⟨κ (3 * τ - c), Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma kapI_eq_zero {c : ℝ} {τ : unitInterval} (h : 3 * (τ : ℝ) - c ≤ 0) : kapI c τ = 0 :=
  Subtype.ext (Real.smoothTransition.zero_of_nonpos h)

lemma kapI_eq_one {c : ℝ} {τ : unitInterval} (h : 1 ≤ 3 * (τ : ℝ) - c) : kapI c τ = 1 :=
  Subtype.ext (Real.smoothTransition.one_of_one_le h)

lemma contDiff_kap (c : ℝ) : ContDiff ℝ ∞ fun t : ℝ => κ (3 * t - c) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem isScSmoothMap_kapI (c : ℝ) :
    unitIntervalPolyfold.IsScSmoothMap unitIntervalPolyfold (kapI c) :=
  isScSmoothMap_interval_of_contDiff (contDiff_kap c) fun τ => (kapI c τ).2

/-- `(τ, t) ↦ (k(τ), t)` is sc-smooth on `[0, 1]²` for sc-smooth `k`. -/
theorem isScSmoothMap_mapFst {k : unitInterval → unitInterval}
    (hk : unitIntervalPolyfold.IsScSmoothMap unitIntervalPolyfold k) :
    unitSquarePolyfold.IsScSmoothMap unitSquarePolyfold fun p => (k p.1, p.2) :=
  MPolyfold.IsScSmoothOn.prodMk (hk.comp (MPolyfold.isScSmoothMap_fst _ _))
    (MPolyfold.isScSmoothMap_snd _ _)

end Maps

/-! ### Sc-smooth homotopies `[0, 1]² → X` with the end points fixed -/

section Homotopy

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **A map in two pieces** on any M-polyfold `W`: if `A`, `B` are sc-smooth and agree where
`1/3 < σ < 2/3`, the map equal to `A` on `{σ ≤ 1/2}` and to `B` elsewhere is sc-smooth. -/
theorem isScSmoothMap_ite_half {W : Type*} [TopologicalSpace W] [T2Space W] [ParacompactSpace W]
    {PW : MPolyfold W} {σ : W → ℝ} (hσ : Continuous σ) {A B : W → X}
    (hA : PW.IsScSmoothMap PX A) (hB : PW.IsScSmoothMap PX B)
    (hAB : ∀ w, 1 / 3 < σ w → σ w < 2 / 3 → A w = B w) :
    PW.IsScSmoothMap PX fun w => if σ w ≤ 1 / 2 then A w else B w := by
  refine MPolyfold.isScSmoothMap_of_eventuallyEq fun w => ?_
  rcases lt_or_ge (σ w) (2 / 3) with hw | hw
  · refine ⟨A, hA, ?_⟩
    filter_upwards [(isOpen_lt hσ continuous_const).mem_nhds hw] with q hq
    change σ q < 2 / 3 at hq
    split_ifs with h
    · rfl
    · exact (hAB q (by linarith [not_le.1 h]) hq).symm
  · refine ⟨B, hB, ?_⟩
    filter_upwards [(isOpen_lt continuous_const hσ).mem_nhds
      (show (1 / 3 : ℝ) < σ w by linarith)] with q hq
    change 1 / 3 < σ q at hq
    split_ifs with h
    · exact hAB q hq (by linarith)
    · rfl

variable (PX) in
/-- **An sc-smooth homotopy `H : [0, 1]² → X` from `φ₀` to `φ₁` with the end points fixed**
(p. 272): `H` is sc-smooth on the M-polyfold `[0, 1]²`, `H(0, ·) = φ₀`, `H(1, ·) = φ₁`,
`H(·, 0) = φ₀(0)`, `H(·, 1) = φ₀(1)`. -/
structure IsScHomotopyRelI (φ₀ φ₁ : unitInterval → X) (H : unitInterval × unitInterval → X) :
    Prop where
  isScSmoothMap : unitSquarePolyfold.IsScSmoothMap PX H
  zero : ∀ t, H (0, t) = φ₀ t
  one : ∀ t, H (1, t) = φ₁ t
  start : ∀ τ, H (τ, 0) = φ₀ 0
  finish : ∀ τ, H (τ, 1) = φ₀ 1

variable (PX) in
/-- **Sc-smoothly homotopic with end points fixed**, for paths on `[0, 1]`. -/
def ScHomotopicI (φ₀ φ₁ : unitInterval → X) : Prop := ∃ H, IsScHomotopyRelI PX φ₀ φ₁ H

variable {φ φ₀ φ₁ φ₂ : unitInterval → X}

theorem ScHomotopicI.refl (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) :
    ScHomotopicI PX φ φ :=
  ⟨fun p => φ p.2, ⟨hφ.comp (MPolyfold.isScSmoothMap_snd _ _), fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl⟩⟩

theorem ScHomotopicI.symm (h : ScHomotopicI PX φ₀ φ₁) : ScHomotopicI PX φ₁ φ₀ := by
  obtain ⟨H, hH⟩ := h
  have h10 : φ₁ 0 = φ₀ 0 := (hH.one 0).symm.trans (hH.start 1)
  have h11 : φ₁ 1 = φ₀ 1 := (hH.one 1).symm.trans (hH.finish 1)
  refine ⟨fun p => H (oneSubI p.1, p.2), ⟨hH.isScSmoothMap.comp
    (isScSmoothMap_mapFst isScSmoothMap_oneSubI), fun t => ?_, fun t => ?_, fun τ => ?_,
    fun τ => ?_⟩⟩
  · change H (oneSubI 0, t) = φ₁ t
    rw [oneSubI_zero]; exact hH.one t
  · change H (oneSubI 1, t) = φ₀ t
    rw [oneSubI_one]; exact hH.zero t
  · change H (oneSubI τ, 0) = φ₁ 0
    rw [h10]; exact hH.start _
  · change H (oneSubI τ, 1) = φ₁ 1
    rw [h11]; exact hH.finish _

theorem ScHomotopicI.trans (h₁ : ScHomotopicI PX φ₀ φ₁) (h₂ : ScHomotopicI PX φ₁ φ₂) :
    ScHomotopicI PX φ₀ φ₂ := by
  obtain ⟨H₁, hH₁⟩ := h₁
  obtain ⟨H₂, hH₂⟩ := h₂
  set A : unitInterval × unitInterval → X := fun p => H₁ (kapI 0 p.1, p.2) with hA
  set B : unitInterval × unitInterval → X := fun p => H₂ (kapI 2 p.1, p.2) with hB
  have hAs : unitSquarePolyfold.IsScSmoothMap PX A :=
    hH₁.isScSmoothMap.comp (isScSmoothMap_mapFst (isScSmoothMap_kapI 0))
  have hBs : unitSquarePolyfold.IsScSmoothMap PX B :=
    hH₂.isScSmoothMap.comp (isScSmoothMap_mapFst (isScSmoothMap_kapI 2))
  have hAB : ∀ p : unitInterval × unitInterval, 1 / 3 < (p.1 : ℝ) → (p.1 : ℝ) < 2 / 3 →
      A p = B p := fun p h1 h2 => by
    change H₁ (kapI 0 p.1, p.2) = H₂ (kapI 2 p.1, p.2)
    rw [kapI_eq_one (by linarith), kapI_eq_zero (by linarith), hH₁.one, hH₂.zero]
  have h10 : φ₁ 0 = φ₀ 0 := (hH₁.one 0).symm.trans (hH₁.start 1)
  have h11 : φ₁ 1 = φ₀ 1 := (hH₁.one 1).symm.trans (hH₁.finish 1)
  refine ⟨fun p => if (p.1 : ℝ) ≤ 1 / 2 then A p else B p, ⟨isScSmoothMap_ite_half
    (continuous_subtype_val.comp continuous_fst) hAs hBs hAB, fun t => ?_, fun t => ?_,
    fun τ => ?_, fun τ => ?_⟩⟩
  · change (if ((0 : unitInterval) : ℝ) ≤ 1 / 2 then A (0, t) else B (0, t)) = φ₀ t
    rw [if_pos (by norm_num)]
    change H₁ (kapI 0 0, t) = φ₀ t
    rw [kapI_eq_zero (by norm_num)]
    exact hH₁.zero t
  · change (if ((1 : unitInterval) : ℝ) ≤ 1 / 2 then A (1, t) else B (1, t)) = φ₂ t
    rw [if_neg (by norm_num)]
    change H₂ (kapI 2 1, t) = φ₂ t
    rw [kapI_eq_one (by norm_num)]
    exact hH₂.one t
  · change (if (τ : ℝ) ≤ 1 / 2 then A (τ, 0) else B (τ, 0)) = φ₀ 0
    split_ifs
    · exact hH₁.start _
    · exact (hH₂.start _).trans h10
  · change (if (τ : ℝ) ≤ 1 / 2 then A (τ, 1) else B (τ, 1)) = φ₀ 1
    split_ifs
    · exact hH₁.finish _
    · exact (hH₂.finish _).trans h11

/-! ### Comparison with the paths on `ℝ` of decision D2 -/

/-- A homotopy on `[0, 1]²` gives a homotopy on `ℝ²` between the paths `unitPath φᵢ` on `ℝ`:
`(τ, t) ↦ H(sin²(πτ/2), sin²(πt/2))`. -/
theorem ScHomotopicI.toReal (h : ScHomotopicI PX φ₀ φ₁) :
    ScHomotopic PX (unitPath φ₀) (unitPath φ₁) := by
  obtain ⟨H, hH⟩ := h
  set g : (Fin 2 → ℝ) → unitInterval × unitInterval :=
    fun q => (sinSqUnit (q 0), sinSqUnit (q 1)) with hg
  have hgs : (rnPolyfold 2).IsScSmoothMap unitSquarePolyfold g :=
    MPolyfold.IsScSmoothOn.prodMk
      (isScSmoothMap_toUnitInterval (contDiff_sinSqHalf.comp (contDiff_apply ℝ ℝ 0)) _)
      (isScSmoothMap_toUnitInterval (contDiff_sinSqHalf.comp (contDiff_apply ℝ ℝ 1)) _)
  refine ⟨H ∘ g, ⟨hH.isScSmoothMap.comp hgs, fun t _ => ?_, fun t _ => ?_, fun τ _ => ?_,
    fun τ _ => ?_⟩⟩
  · simp only [Function.comp_apply, hg, unitPath, unitReparam_zero_one, pt2_apply_zero,
      pt2_apply_one, sinSqUnit_zero, hH.zero]
    rfl
  · simp only [Function.comp_apply, hg, unitPath, unitReparam_zero_one, pt2_apply_zero,
      pt2_apply_one, sinSqUnit_one, hH.one]
    rfl
  · simp only [Function.comp_apply, hg, unitPath, unitReparam_zero_one, pt2_apply_one,
      pt1_apply, sinSqUnit_zero, hH.start]
  · simp only [Function.comp_apply, hg, unitPath, unitReparam_zero_one, pt2_apply_one,
      pt1_apply, sinSqUnit_one, hH.finish]

/-- **A reparametrization of `[0, 1]` fixing the end points gives a homotopic path**:
`(τ, t) ↦ φ((1 − τ)t + τ g(t))`. -/
theorem scHomotopicI_reparam (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (h01 : ∀ t : unitInterval, g t ∈ Icc (0 : ℝ) 1) (hg0 : g 0 = 0)
    (hg1 : g 1 = 1) : ScHomotopicI PX φ fun t => φ ⟨g t, h01 t⟩ := by
  have hmem : ∀ τ t : unitInterval, (1 - (τ : ℝ)) * t + τ * g t ∈ Icc (0 : ℝ) 1 := by
    intro τ t
    obtain ⟨hτ0, hτ1⟩ := τ.2
    obtain ⟨ht0, ht1⟩ := t.2
    obtain ⟨hg0', hg1'⟩ := h01 t
    constructor <;> nlinarith
  have hm := isScSmoothMap_square_of_contDiff (g := fun τ t => (1 - τ) * t + τ * g t)
    (((contDiff_const.sub contDiff_fst).mul contDiff_snd).add
      (contDiff_fst.mul (hg.comp contDiff_snd))) hmem
  refine ⟨fun p => φ ⟨(1 - (p.1 : ℝ)) * p.2 + p.1 * g p.2, hmem p.1 p.2⟩,
    ⟨hφ.comp hm, fun t => ?_, fun t => ?_, fun τ => ?_, fun τ => ?_⟩⟩ <;>
    refine congrArg φ (Subtype.ext ?_) <;> simp [hg0, hg1]

/-- A homotopy on `ℝ²` between the paths `unitPath φᵢ` restricts to a homotopy on `[0, 1]²`
between the reparametrized paths `φᵢ(sin²(π · /2))`. -/
theorem ScHomotopic.toInterval (h : ScHomotopic PX (unitPath φ₀) (unitPath φ₁)) :
    ScHomotopicI PX (fun t => φ₀ (sinSqUnit t)) (fun t => φ₁ (sinSqUnit t)) := by
  obtain ⟨G, hG⟩ := h
  refine ⟨fun p => G (pt2 p.1 p.2), ⟨hG.isScSmoothMap.comp isScSmoothMap_square_pt2,
    fun t => ?_, fun t => ?_, fun τ => ?_, fun τ => ?_⟩⟩
  · have := hG.zero t t.2
    simp only [unitPath, Function.comp_apply, unitReparam_zero_one, pt1_apply] at this
    simpa using this
  · have := hG.one t t.2
    simp only [unitPath, Function.comp_apply, unitReparam_zero_one, pt1_apply] at this
    simpa using this
  · have := hG.start τ τ.2
    rw [unitPath_zero] at this
    simpa using this
  · have := hG.finish τ τ.2
    rw [unitPath_one] at this
    simpa using this

/-- **The two readings of "homotopic" agree**: paths on `[0, 1]` are sc-smoothly homotopic on
`[0, 1]²` with the end points fixed iff their paths `unitPath φᵢ` on `ℝ` are homotopic in the
sense of decision D2. -/
theorem scHomotopicI_iff (hφ₀ : unitIntervalPolyfold.IsScSmoothMap PX φ₀)
    (hφ₁ : unitIntervalPolyfold.IsScSmoothMap PX φ₁) :
    ScHomotopicI PX φ₀ φ₁ ↔ ScHomotopic PX (unitPath φ₀) (unitPath φ₁) := by
  refine ⟨ScHomotopicI.toReal, fun h => ?_⟩
  have r₀ := scHomotopicI_reparam hφ₀ contDiff_sinSqHalf (fun t => sinSqHalf_mem t)
    sinSqHalf_zero sinSqHalf_one
  have r₁ := scHomotopicI_reparam hφ₁ contDiff_sinSqHalf (fun t => sinSqHalf_mem t)
    sinSqHalf_zero sinSqHalf_one
  exact (r₀.trans h.toInterval).trans r₁.symm

/-- **Every path on `ℝ` is homotopic to the path on `ℝ` of its restriction to `[0, 1]`**:
`(σ, t) ↦ γ((1 − σ) sin²(πt/2) + σt)`. -/
theorem scHomotopic_unitPath_restrict {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) :
    ScHomotopic PX (unitPath (restrictUnitPath γ)) γ := by
  set H : (Fin 2 → ℝ) → X := fun q => γ (pt1 ((1 - q 0) * sinSqHalf (q 1) + q 0 * q 1))
    with hH
  have hHs : (rnPolyfold 2).IsScSmoothMap PX H :=
    hγ.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pi.2 fun _ =>
      ((contDiff_const.sub (contDiff_apply ℝ ℝ 0)).mul
        (contDiff_sinSqHalf.comp (contDiff_apply ℝ ℝ 1))).add
        ((contDiff_apply ℝ ℝ 0).mul (contDiff_apply ℝ ℝ 1))))
  exact ⟨H,
    { isScSmoothMap := hHs
      zero := fun t _ => by
        simp only [hH, unitPath, restrictUnitPath, Function.comp_apply, unitReparam_zero_one,
          pt2_apply_zero, pt2_apply_one, pt1_apply, sinSqUnit]
        congr 2; ring
      one := fun t _ => by
        simp only [hH, pt2_apply_zero, pt2_apply_one]
        congr 2; ring
      start := fun τ _ => by
        simp only [hH, unitPath, restrictUnitPath, Function.comp_apply, unitReparam_zero_one,
          pt2_apply_zero, pt2_apply_one, pt1_apply, sinSqUnit, sinSqHalf_zero]
        congr 2; ring
      finish := fun τ _ => by
        simp only [hH, unitPath, restrictUnitPath, Function.comp_apply, unitReparam_zero_one,
          pt2_apply_zero, pt2_apply_one, pt1_apply, sinSqUnit, sinSqHalf_one]
        congr 2; ring }⟩

end Homotopy

/-! ### The text's `β` -/

/-- **The text's `β`** (p. 272): `β(s) = κ(3s) + κ(3s − 2)`, smooth and monotone, `β(0) = 0`,
`β = 1` on `[1/3, 2/3]` (near `1/2`), `β(1) = 2`, `β([0, 1/2]) ⊆ [0, 1]`,
`β([1/2, 1]) ⊆ [1, 2]`. -/
def betaConcat (s : ℝ) : ℝ := κ (3 * s) + κ (3 * s - 2)

lemma contDiff_betaConcat : ContDiff ℝ ∞ betaConcat := by
  have h := (contDiff_kap 0).add (contDiff_kap 2)
  change ContDiff ℝ ∞ fun s : ℝ => κ (3 * s) + κ (3 * s - 2)
  simpa only [sub_zero] using h

lemma monotone_betaConcat : Monotone betaConcat := fun a b hab =>
  add_le_add (Real.smoothTransition.monotone (by linarith))
    (Real.smoothTransition.monotone (by linarith))

lemma betaConcat_zero : betaConcat 0 = 0 := by
  simp only [betaConcat, mul_zero, Real.smoothTransition.zero, zero_sub, zero_add]
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)

lemma betaConcat_one : betaConcat 1 = 2 := by
  simp only [betaConcat, mul_one, show (3 : ℝ) - 2 = 1 by norm_num, Real.smoothTransition.one]
  rw [Real.smoothTransition.one_of_one_le (by norm_num)]
  norm_num

lemma betaConcat_of_le {s : ℝ} (hs : s ≤ 2 / 3) : betaConcat s = κ (3 * s) := by
  rw [betaConcat, Real.smoothTransition.zero_of_nonpos (x := 3 * s - 2) (by linarith), add_zero]

lemma betaConcat_of_ge {s : ℝ} (hs : 1 / 3 ≤ s) : betaConcat s = 1 + κ (3 * s - 2) := by
  rw [betaConcat, Real.smoothTransition.one_of_one_le (by linarith)]

lemma betaConcat_eq_one {s : ℝ} (h₁ : 1 / 3 ≤ s) (h₂ : s ≤ 2 / 3) : betaConcat s = 1 := by
  rw [betaConcat_of_ge h₁, Real.smoothTransition.zero_of_nonpos (x := 3 * s - 2) (by linarith),
    add_zero]

/-! ### Paths on `[0, 1]` and their classes -/

section Paths

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

variable (PX) in
/-- **An sc-smooth path `φ : [0, 1] → X` from `x` to `y`** (p. 272). -/
@[ext]
structure ScPathI (x y : X) where
  /-- The path. -/
  toFun : unitInterval → X
  /-- It is sc-smooth on the M-polyfold `[0, 1]`. -/
  isScSmoothMap : unitIntervalPolyfold.IsScSmoothMap PX toFun
  /-- It starts at `x`. -/
  source : toFun 0 = x
  /-- It ends at `y`. -/
  target : toFun 1 = y

namespace ScPathI

variable {w x y z : X}

variable (PX) in
/-- Sc-smooth homotopy on `[0, 1]²` with end points fixed, as a setoid. -/
instance setoid (x y : X) : Setoid (ScPathI PX x y) where
  r a b := ScHomotopicI PX a.toFun b.toFun
  iseqv :=
    { refl := fun a => ScHomotopicI.refl a.isScSmoothMap
      symm := fun h => h.symm
      trans := fun h₁ h₂ => h₁.trans h₂ }

theorem equiv_iff {a b : ScPathI PX x y} : a ≈ b ↔ ScHomotopicI PX a.toFun b.toFun := Iff.rfl

/-- **The path on `ℝ` of a path on `[0, 1]`** (`unitPath`), a path of decision D2. -/
def toScPath (a : ScPathI PX x y) : ScPath PX x y where
  toFun := unitPath a.toFun
  isScSmoothMap := isScSmoothMap_unitPath a.isScSmoothMap
  source := (unitPath_zero _).trans a.source
  target := (unitPath_one _).trans a.target

/-- **The restriction to `[0, 1]`** of a path on `ℝ`. -/
def ofScPath (a : ScPath PX x y) : ScPathI PX x y where
  toFun := restrictUnitPath a.toFun
  isScSmoothMap := isScSmoothMap_restrictUnitPath a.isScSmoothMap
  source := by
    change a.toFun (pt1 ((0 : unitInterval) : ℝ)) = x
    rw [Set.Icc.coe_zero]; exact a.source
  target := by
    change a.toFun (pt1 ((1 : unitInterval) : ℝ)) = y
    rw [Set.Icc.coe_one]; exact a.target

/-- Paths on `[0, 1]` are homotopic iff their paths on `ℝ` are. -/
theorem equiv_iff_toScPath {a b : ScPathI PX x y} : a ≈ b ↔ a.toScPath ≈ b.toScPath :=
  scHomotopicI_iff a.isScSmoothMap b.isScSmoothMap

theorem toScPath_ofScPath (a : ScPath PX x y) : (ofScPath a).toScPath ≈ a :=
  scHomotopic_unitPath_restrict a.isScSmoothMap

variable (x) in
/-- **The constant path** at a smooth point. -/
def const (hx : x ∈ PX.smoothSet) : ScPathI PX x x where
  toFun _ := x
  isScSmoothMap := (isScSmoothMap_const_of_mem_smoothSet (m := 1) hx).comp
    isScSmoothMap_unitInterval_val
  source := rfl
  target := rfl

theorem toScPath_const (hx : x ∈ PX.smoothSet) : (const x hx).toScPath = ScPath.const x hx :=
  ScPath.ext rfl

/-- **The reversed path** `t ↦ φ(1 − t)`. -/
def reverse (a : ScPathI PX x y) : ScPathI PX y x where
  toFun t := a.toFun (oneSubI t)
  isScSmoothMap := a.isScSmoothMap.comp isScSmoothMap_oneSubI
  source := by rw [oneSubI_zero]; exact a.target
  target := by rw [oneSubI_one]; exact a.source

lemma sinSqHalf_one_sub (u : ℝ) : sinSqHalf (1 - u) = 1 - sinSqHalf u := by
  simp only [sinSqHalf]
  rw [mul_one_sub, Real.sin_pi_div_two_sub, ← Real.sin_sq_add_cos_sq (Real.pi / 2 * u)]
  ring

theorem toScPath_reverse (a : ScPathI PX x y) : a.reverse.toScPath = a.toScPath.reverse := by
  refine ScPath.ext (funext fun r => ?_)
  change a.toFun (oneSubI (unitReparam 0 1 r)) = a.toFun (unitReparam 0 1 (pt1 (1 - r 0)))
  refine congrArg a.toFun (Subtype.ext ?_)
  simp only [coe_oneSubI, unitReparam, pt1_apply, Set.Icc.coe_zero, Set.Icc.coe_one, sub_zero,
    mul_one, zero_add, sinSqHalf_one_sub]

/-- **The text's concatenation** `γ(s) = φ(β(s))` on `[0, 1/2]`, `γ(s) = ψ(β(s) − 1)` on
`[1/2, 1]` (p. 272; with `β = betaConcat`, `concat_toFun_of_le`, `concat_toFun_of_ge`). -/
def concat (a : ScPathI PX x y) (b : ScPathI PX y z) : ScPathI PX x z where
  toFun s := if (s : ℝ) ≤ 1 / 2 then a.toFun (kapI 0 s) else b.toFun (kapI 2 s)
  isScSmoothMap := by
    refine isScSmoothMap_ite_half continuous_subtype_val
      (a.isScSmoothMap.comp (isScSmoothMap_kapI 0)) (b.isScSmoothMap.comp (isScSmoothMap_kapI 2))
      fun s h₁ h₂ => ?_
    rw [kapI_eq_one (by linarith), kapI_eq_zero (by linarith), a.target, b.source]
  source := by
    rw [if_pos (by norm_num), kapI_eq_zero (by norm_num)]
    exact a.source
  target := by
    rw [if_neg (by norm_num), kapI_eq_one (by norm_num)]
    exact b.target

lemma betaConcat_mem_of_le {s : unitInterval} (hs : (s : ℝ) ≤ 1 / 2) :
    betaConcat s ∈ Icc (0 : ℝ) 1 := by
  rw [betaConcat_of_le (by linarith)]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma betaConcat_sub_one_mem_of_ge {s : unitInterval} (hs : 1 / 2 ≤ (s : ℝ)) :
    betaConcat s - 1 ∈ Icc (0 : ℝ) 1 := by
  rw [betaConcat_of_ge (by linarith), add_sub_cancel_left]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- On `[0, 1/2]` the concatenation is `φ(β(s))`. -/
theorem concat_toFun_of_le (a : ScPathI PX x y) (b : ScPathI PX y z) {s : unitInterval}
    (hs : (s : ℝ) ≤ 1 / 2) :
    (a.concat b).toFun s = a.toFun ⟨betaConcat s, betaConcat_mem_of_le hs⟩ := by
  change (if (s : ℝ) ≤ 1 / 2 then a.toFun (kapI 0 s) else b.toFun (kapI 2 s)) = _
  rw [if_pos hs]
  refine congrArg a.toFun (Subtype.ext ?_)
  change κ (3 * (s : ℝ) - 0) = betaConcat s
  rw [sub_zero, betaConcat_of_le (by linarith)]

/-- On `[1/2, 1]` the concatenation is `ψ(β(s) − 1)`. -/
theorem concat_toFun_of_ge (a : ScPathI PX x y) (b : ScPathI PX y z) {s : unitInterval}
    (hs : 1 / 2 ≤ (s : ℝ)) :
    (a.concat b).toFun s = b.toFun ⟨betaConcat s - 1, betaConcat_sub_one_mem_of_ge hs⟩ := by
  change (if (s : ℝ) ≤ 1 / 2 then a.toFun (kapI 0 s) else b.toFun (kapI 2 s)) = _
  split_ifs with h
  · have hs' : (s : ℝ) = 1 / 2 := le_antisymm h hs
    have e : (⟨betaConcat s - 1, betaConcat_sub_one_mem_of_ge hs⟩ : unitInterval) = 0 :=
      Subtype.ext (by
        change betaConcat s - 1 = 0
        rw [betaConcat_eq_one (by linarith) (by linarith), sub_self])
    rw [kapI_eq_one (by linarith), a.target, e, b.source]
  · refine congrArg b.toFun (Subtype.ext ?_)
    change κ (3 * (s : ℝ) - 2) = betaConcat s - 1
    rw [betaConcat_of_ge (by linarith), add_sub_cancel_left]

/-- `(τ, t) ↦ (1 − τ)κ(3t − c) + τ sin²(πκ(3t − c)/2)`. -/
def lerpI (c : ℝ) (τ t : unitInterval) : unitInterval :=
  ⟨(1 - (τ : ℝ)) * κ (3 * t - c) + τ * sinSqHalf (κ (3 * t - c)), by
    obtain ⟨hτ0, hτ1⟩ := τ.2
    have h0 := Real.smoothTransition.nonneg (3 * t - c)
    have h1 := Real.smoothTransition.le_one (3 * t - c)
    obtain ⟨hs0, hs1⟩ := sinSqHalf_mem (κ (3 * t - c))
    constructor <;> nlinarith⟩

theorem isScSmoothMap_lerpI (c : ℝ) :
    unitSquarePolyfold.IsScSmoothMap unitIntervalPolyfold fun p => lerpI c p.1 p.2 :=
  isScSmoothMap_square_of_contDiff
    (g := fun τ t => (1 - τ) * κ (3 * t - c) + τ * sinSqHalf (κ (3 * t - c)))
    (((contDiff_const.sub contDiff_fst).mul ((contDiff_kap c).comp contDiff_snd)).add
      (contDiff_fst.mul ((contDiff_sinSqHalf.comp (contDiff_kap c)).comp contDiff_snd)))
    fun τ t => (lerpI c τ t).2

lemma lerpI_eq_one {c : ℝ} (τ : unitInterval) {t : unitInterval} (h : 1 ≤ 3 * (t : ℝ) - c) :
    lerpI c τ t = 1 :=
  Subtype.ext (by simp [lerpI, Real.smoothTransition.one_of_one_le h])

lemma lerpI_eq_zero {c : ℝ} (τ : unitInterval) {t : unitInterval} (h : 3 * (t : ℝ) - c ≤ 0) :
    lerpI c τ t = 0 :=
  Subtype.ext (by simp [lerpI, Real.smoothTransition.zero_of_nonpos h])

/-- **The path on `ℝ` of a concatenation** is homotopic to the concatenation (decision D2) of the
paths on `ℝ`: `(τ, t) ↦ φ((1 − τ)κ(3t) + τ sin²(πκ(3t)/2))` on `t ≤ 1/2`, and the same with `ψ`
and `κ(3t − 2)` on `t > 1/2`, compares `concat` with the restriction of `concatPath`. -/
theorem toScPath_concat (a : ScPathI PX x y) (b : ScPathI PX y z) :
    (a.concat b).toScPath ≈ a.toScPath.concat b.toScPath := by
  set γ := a.toScPath.concat b.toScPath with hγ
  refine Setoid.trans ?_ (toScPath_ofScPath γ)
  refine equiv_iff_toScPath.1 ?_
  set A : unitInterval × unitInterval → X := fun p => a.toFun (lerpI 0 p.1 p.2) with hA
  set B : unitInterval × unitInterval → X := fun p => b.toFun (lerpI 2 p.1 p.2) with hB
  have hAs : unitSquarePolyfold.IsScSmoothMap PX A := a.isScSmoothMap.comp (isScSmoothMap_lerpI 0)
  have hBs : unitSquarePolyfold.IsScSmoothMap PX B := b.isScSmoothMap.comp (isScSmoothMap_lerpI 2)
  have hAB : ∀ p : unitInterval × unitInterval, 1 / 3 < (p.2 : ℝ) → (p.2 : ℝ) < 2 / 3 →
      A p = B p := fun p h₁ h₂ => by
    change a.toFun (lerpI 0 p.1 p.2) = b.toFun (lerpI 2 p.1 p.2)
    rw [lerpI_eq_one _ (by linarith), lerpI_eq_zero _ (by linarith), a.target, b.source]
  refine ⟨fun p => if (p.2 : ℝ) ≤ 1 / 2 then A p else B p, ⟨isScSmoothMap_ite_half
    (continuous_subtype_val.comp continuous_snd) hAs hBs hAB, fun t => ?_, fun t => ?_,
    fun τ => ?_, fun τ => ?_⟩⟩
  · change (if (t : ℝ) ≤ 1 / 2 then a.toFun (lerpI 0 0 t) else b.toFun (lerpI 2 0 t)) =
      (if (t : ℝ) ≤ 1 / 2 then a.toFun (kapI 0 t) else b.toFun (kapI 2 t))
    have e : ∀ c, lerpI c 0 t = kapI c t := fun c => Subtype.ext (by simp [lerpI, kapI])
    rw [e, e]
  · change (if (t : ℝ) ≤ 1 / 2 then a.toFun (lerpI 0 1 t) else b.toFun (lerpI 2 1 t)) =
      concatPath (unitPath a.toFun) (unitPath b.toFun) (pt1 (t : ℝ))
    split_ifs with h
    · rw [concatPath_of_le (s := pt1 (t : ℝ)) h]
      refine congrArg a.toFun (Subtype.ext ?_)
      simp [lerpI, unitReparam]
    · rw [concatPath_of_gt (s := pt1 (t : ℝ)) (not_le.1 h)]
      refine congrArg b.toFun (Subtype.ext ?_)
      simp [lerpI, unitReparam]
  · change (if ((0 : unitInterval) : ℝ) ≤ 1 / 2 then A (τ, 0) else B (τ, 0)) =
      (if ((0 : unitInterval) : ℝ) ≤ 1 / 2 then a.toFun (kapI 0 0) else b.toFun (kapI 2 0))
    rw [if_pos (by norm_num), if_pos (by norm_num), kapI_eq_zero (by norm_num)]
    change a.toFun (lerpI 0 τ 0) = _
    rw [lerpI_eq_zero _ (by norm_num)]
  · change (if ((1 : unitInterval) : ℝ) ≤ 1 / 2 then A (τ, 1) else B (τ, 1)) =
      (if ((1 : unitInterval) : ℝ) ≤ 1 / 2 then a.toFun (kapI 0 1) else b.toFun (kapI 2 1))
    rw [if_neg (by norm_num), if_neg (by norm_num), kapI_eq_one (by norm_num)]
    change b.toFun (lerpI 2 τ 1) = _
    rw [lerpI_eq_one _ (by norm_num)]

theorem concat_congr ⦃a a' : ScPathI PX x y⦄ (ha : a ≈ a') ⦃b b' : ScPathI PX y z⦄
    (hb : b ≈ b') : a.concat b ≈ a'.concat b' :=
  equiv_iff_toScPath.2 (Setoid.trans (toScPath_concat a b) (Setoid.trans
    (ScPath.concat_congr (equiv_iff_toScPath.1 ha) (equiv_iff_toScPath.1 hb))
    (Setoid.symm (toScPath_concat a' b'))))

theorem const_concat (hx : x ∈ PX.smoothSet) (a : ScPathI PX x y) :
    (const x hx).concat a ≈ a := by
  refine equiv_iff_toScPath.2 (Setoid.trans (toScPath_concat _ a) ?_)
  rw [toScPath_const]
  exact ScPath.const_concat hx a.toScPath

theorem concat_const (hy : y ∈ PX.smoothSet) (a : ScPathI PX x y) :
    a.concat (const y hy) ≈ a := by
  refine equiv_iff_toScPath.2 (Setoid.trans (toScPath_concat a _) ?_)
  rw [toScPath_const]
  exact ScPath.concat_const hy a.toScPath

theorem concat_assoc (a : ScPathI PX w x) (b : ScPathI PX x y) (c : ScPathI PX y z) :
    (a.concat b).concat c ≈ a.concat (b.concat c) :=
  equiv_iff_toScPath.2 (Setoid.trans (toScPath_concat _ c) (Setoid.trans
    (ScPath.concat_congr (toScPath_concat a b) (Setoid.refl _)) (Setoid.trans
      (ScPath.concat_assoc _ _ _) (Setoid.trans
        (ScPath.concat_congr (Setoid.refl _) (Setoid.symm (toScPath_concat b c)))
        (Setoid.symm (toScPath_concat a _))))))

theorem reverse_congr ⦃a a' : ScPathI PX x y⦄ (h : a ≈ a') : a.reverse ≈ a'.reverse := by
  refine equiv_iff_toScPath.2 ?_
  rw [toScPath_reverse, toScPath_reverse]
  exact ScPath.reverse_congr (equiv_iff_toScPath.1 h)

theorem concat_reverse (hx : x ∈ PX.smoothSet) (a : ScPathI PX x y) :
    a.concat a.reverse ≈ const x hx := by
  refine equiv_iff_toScPath.2 (Setoid.trans (toScPath_concat _ _) ?_)
  rw [toScPath_reverse, toScPath_const]
  exact ScPath.concat_reverse hx a.toScPath

theorem reverse_concat (hy : y ∈ PX.smoothSet) (a : ScPathI PX x y) :
    a.reverse.concat a ≈ const y hy := by
  refine equiv_iff_toScPath.2 (Setoid.trans (toScPath_concat _ _) ?_)
  rw [toScPath_reverse, toScPath_const]
  exact ScPath.reverse_concat hy a.toScPath

end ScPathI

/-! ### The category `PX` with paths on `[0, 1]` -/

variable (PX) in
/-- The objects of the path category: the smooth points of `X`. -/
structure PathCatI where
  /-- The point. -/
  pt : X
  /-- It is a smooth point. -/
  smooth : pt ∈ PX.smoothSet

namespace PathCatI

/-- **The path category `PX` of the text** (p. 272), with paths on `[0, 1]`: morphisms `x ⟶ y`
are the classes `[φ]` of sc-smooth paths `φ : [0, 1] → X` from `x` to `y` modulo sc-smooth
homotopies `[0, 1]² → X` with end points fixed, and `[φ] ≫ [ψ]` is the text's `[ψ] ∗ [φ]`, the
class of `γ = φ ∘ β` on `[0, 1/2]`, `ψ ∘ (β − 1)` on `[1/2, 1]`. -/
instance category : Category (PathCatI PX) where
  Hom x y := Quotient (ScPathI.setoid PX x.pt y.pt)
  id x := ⟦ScPathI.const x.pt x.smooth⟧
  comp f g := Quotient.map₂ ScPathI.concat ScPathI.concat_congr f g
  id_comp {x _} f :=
    Quotient.inductionOn f fun a => Quotient.sound (ScPathI.const_concat x.smooth a)
  comp_id {_ y} f :=
    Quotient.inductionOn f fun a => Quotient.sound (ScPathI.concat_const y.smooth a)
  assoc f g h :=
    Quotient.inductionOn₃ f g h fun a b c => Quotient.sound (ScPathI.concat_assoc a b c)

variable {x y z : PathCatI PX}

/-- The morphism `[φ] : x ⟶ y`. -/
def homMk (a : ScPathI PX x.pt y.pt) : x ⟶ y := (⟦a⟧ : Quotient (ScPathI.setoid PX x.pt y.pt))

/-- `[φ] ≫ [ψ]` is the class of the text's concatenation (the text's `[ψ] ∗ [φ]`). -/
@[simp] theorem comp_mk (a : ScPathI PX x.pt y.pt) (b : ScPathI PX y.pt z.pt) :
    homMk a ≫ homMk b = homMk (a.concat b) := rfl

theorem id_eq_mk (x : PathCatI PX) : 𝟙 x = homMk (ScPathI.const x.pt x.smooth) := rfl

theorem mk_eq_mk_iff {a b : ScPathI PX x.pt y.pt} :
    homMk a = homMk b ↔ ScHomotopicI PX a.toFun b.toFun :=
  Quotient.eq

/-- **The path category on `[0, 1]` is a groupoid**, the inverse of `[φ]` being `[φ(1 − ·)]`. -/
instance groupoid : Groupoid (PathCatI PX) where
  toCategory := category
  inv f := Quotient.map ScPathI.reverse ScPathI.reverse_congr f
  inv_comp {_ y} f :=
    Quotient.inductionOn f fun a => Quotient.sound (ScPathI.reverse_concat y.smooth a)
  comp_inv {x _} f :=
    Quotient.inductionOn f fun a => Quotient.sound (ScPathI.concat_reverse x.smooth a)

variable (PX) in
/-- **The comparison functor** to the path category of decision D2: the identity on objects and
`[φ] ↦ [unitPath φ]` on morphisms. -/
def toPathCat : PathCatI PX ⥤ PathCat PX where
  obj x := ⟨x.pt, x.smooth⟩
  map f := Quotient.map ScPathI.toScPath (fun _ _ h => ScPathI.equiv_iff_toScPath.1 h) f
  map_id x := by
    change (⟦(ScPathI.const x.pt x.smooth).toScPath⟧ : ScPathClass PX x.pt x.pt) = _
    rw [ScPathI.toScPath_const]
    rfl
  map_comp f g :=
    Quotient.inductionOn₂ f g fun a b => Quotient.sound (ScPathI.toScPath_concat a b)

/-- **The comparison functor is faithful**: homotopy on `[0, 1]²` is homotopy on `ℝ²` of the
paths on `ℝ` (`scHomotopicI_iff`). -/
instance toPathCat_faithful : (toPathCat PX).Faithful where
  map_injective {_ _} f g h := by
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    exact Quotient.sound (ScPathI.equiv_iff_toScPath.2 (Quotient.exact h))

/-- **The comparison functor is full**: every path on `ℝ` is homotopic to the path on `ℝ` of its
restriction to `[0, 1]`. -/
instance toPathCat_full : (toPathCat PX).Full where
  map_surjective {_ _} f := by
    induction f using Quotient.inductionOn with
    | h γ => exact ⟨⟦ScPathI.ofScPath γ⟧, Quotient.sound (ScPathI.toScPath_ofScPath γ)⟩

/-- **The two readings give equivalent (indeed isomorphic) categories**: the comparison functor is
full, faithful and the identity on objects. -/
instance toPathCat_essSurj : (toPathCat PX).EssSurj where
  mem_essImage y := ⟨⟨y.pt, y.smooth⟩, ⟨Iso.refl _⟩⟩

instance toPathCat_isEquivalence : (toPathCat PX).IsEquivalence where

end PathCatI

end Paths

end Polyfold
