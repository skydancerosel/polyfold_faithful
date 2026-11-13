import Polyfold.Chapter4.ScFormsPullback2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), proof of the Poincaré
Lemma 4.4.8 (§4.5.3, p. 203–204): "we apply Lemma 4.5.2 working with `Cⁱ ⊂ Eⁱ`".  Auxiliary
file of `Poincare448.lean`.

# The level `m` of a retract, and transport of the Poincaré property

## The text, paraphrased

In the proof of Lemma 4.4.8 a form on the level `i` of the set `B_δ(x) ∩ C` is treated as a form on
the convex set `(B_δ(x) ∩ C)ⁱ` of the sc-Banach space `Eⁱ`, to which Lemma 4.5.2 applies.

## What is formalized

* `LocalModel.shiftEquiv M hne hne1 : ScEquiv (M.toMPolyfold hne).shift (M.shift.toMPolyfold hne1)`:
  the level `1` of the M-polyfold of a nonempty retract `(O, C, E)` is the M-polyfold of the
  retract `(O¹, C¹, E¹)` (both have one chart, and the map is the identity in these charts).
* `LocalModel.shiftIter M m` (the model `(Oᵐ, Cᵐ, Eᵐ)`) and `LocalModel.liftEquiv`: the `m`-th
  lift of the bundled M-polyfold of `O` is the M-polyfold of `Oᵐ`.
* `MPolyfold.HasPoincare P k` (every closed `(k+1)`-form on `P` is `d` of a `k`-form on `P¹`,
  i.e. `dτ = ι^*σ`) and `HasPoincare.of_scEquiv`: the property passes along sc-diffeomorphisms.
-/

open Set Function

noncomputable section

namespace Polyfold

/-! ### `HasPoincare` and its invariance -/

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

variable (P) in
/-- **The Poincaré property in degree `k + 1`**: every closed sc-differential `(k+1)`-form `σ`
on `X` has a primitive `τ ∈ Ωᵏ(X)` with `dτ = σ` on `X¹` (Lemma 4.5.2's conclusion). -/
def HasPoincare (k : ℕ) : Prop :=
  ∀ σ ∈ P.scForms (k + 1), extD σ = 0 → ∃ τ ∈ P.scForms k, extD τ = formLower σ

lemma formPullback_zeroForm {k : ℕ} {f : X → Y} (hf : P.IsScSmoothMap Q f) :
    formPullback (k := k) hf 0 = 0 := by
  funext x
  ext α
  rfl

/-- **The Poincaré property is invariant under sc-diffeomorphisms.** -/
theorem HasPoincare.of_scEquiv {k : ℕ} (e : ScEquiv P Q) (h : Q.HasPoincare k) :
    P.HasPoincare k := by
  intro σ hσ hdσ
  set σ' := formPullback e.isScSmoothMap_invFun σ with hσ'
  have hσ'm : σ' ∈ Q.scForms (k + 1) := formPullback_mem_scForms _ hσ
  have hdσ' : extD σ' = 0 := by
    rw [hσ', extD_formPullback _ hσ, hdσ, formPullback_zeroForm]
  obtain ⟨τ', hτ', hdτ'⟩ := h σ' hσ'm hdσ'
  refine ⟨formPullback e.isScSmoothMap_toFun τ', formPullback_mem_scForms _ hτ', ?_⟩
  rw [extD_formPullback _ hτ', hdτ',
    formLower_formPullback e.isScSmoothMap_toFun (fun _ => rfl)
      (isScSmoothMap_liftLevelOneMap e.isScSmoothMap_toFun),
    hσ', ← formPullback_comp]
  have hid : ∀ x, (e.invFun ∘ e.toFun) x = id x := fun x => e.left_inv x
  rw [formPullback_congr _ isScSmoothMap_id hid, formPullback_id]

end MPolyfold

/-! ### The level `1` of a retract -/

namespace LocalModel

open MPolyfold

variable (M : LocalModel)

/-- The chart `id` of the M-polyfold of a retract. -/
lemma selfChart_isChart' (hne : M.O.Nonempty) : (M.toMPolyfold hne).IsChart (M.selfChart hne) :=
  (M.toMPolyfold hne).isChart_of_mem (mem_singleton _)

variable {M}

lemma mem_levelSet_toMPolyfold_iff (hne : M.O.Nonempty) {m : ℕ} (x : M.O) :
    x ∈ (M.toMPolyfold hne).levelSet m ↔ (x : M.E 0) ∈ range (M.E.toBase m) :=
  (M.toMPolyfold hne).mem_levelSet_iff (M.selfChart_isChart' hne) (mem_univ x)

lemma toBase_levelLift_selfChart (hne : M.O.Nonempty) (x : (M.toMPolyfold hne).Level 1) :
    M.E.toBase 1 (levelLift (M.selfChart hne) 1 ((M.toMPolyfold hne).levelVal 1 x)) =
      ((M.toMPolyfold hne).levelVal 1 x : M.E 0) :=
  (M.toMPolyfold hne).toBase_levelLift (M.selfChart_isChart' hne) (mem_univ _)
    ((M.toMPolyfold hne).levelVal_mem x)

/-- `X¹ → O¹`, `x ↦` the level-`1` vector of `x`. -/
def shiftEquivFun (hne : M.O.Nonempty) (x : (M.toMPolyfold hne).Level 1) : M.shift.O :=
  ⟨levelLift (M.selfChart hne) 1 ((M.toMPolyfold hne).levelVal 1 x), by
    change M.E.toBase 1 _ ∈ M.O
    rw [toBase_levelLift_selfChart]
    exact ((M.toMPolyfold hne).levelVal 1 x).2⟩

/-- `O¹ → X¹`, `z ↦ z` (as a point of `O` on level `1`). -/
def shiftEquivInv (hne : M.O.Nonempty) (z : M.shift.O) : (M.toMPolyfold hne).Level 1 :=
  (M.toMPolyfold hne).levelMk 1 ⟨M.E.toBase 1 z.1, z.2⟩
    ((mem_levelSet_toMPolyfold_iff hne _).2 ⟨z.1, rfl⟩)

lemma shiftEquivInv_shiftEquivFun (hne : M.O.Nonempty) (x : (M.toMPolyfold hne).Level 1) :
    shiftEquivInv hne (shiftEquivFun hne x) = x := by
  apply level_ext
  apply Subtype.ext
  change M.E.toBase 1 (levelLift (M.selfChart hne) 1 ((M.toMPolyfold hne).levelVal 1 x)) = _
  exact toBase_levelLift_selfChart hne x

lemma shiftEquivFun_shiftEquivInv (hne : M.O.Nonempty) (z : M.shift.O) :
    shiftEquivFun hne (shiftEquivInv hne z) = z := by
  apply Subtype.ext
  apply M.E.toBase_injective 1
  exact (toBase_levelLift_selfChart hne (shiftEquivInv hne z)).trans rfl

/-- The level chart of `X¹` built from the chart `id` of `X`. -/
abbrev shiftChart (hne : M.O.Nonempty) (x₀ : (M.toMPolyfold hne).Level 1) :
    MChart ((M.toMPolyfold hne).Level 1) :=
  levelChart (M.selfChart_isChart' hne) x₀

lemma mem_shiftChart_source (hne : M.O.Nonempty) (x₀ : (M.toMPolyfold hne).Level 1)
    (x : (M.toMPolyfold hne).Level 1) : x ∈ (shiftChart hne x₀).source :=
  show (M.toMPolyfold hne).levelVal 1 x ∈ (M.selfChart hne).source from mem_univ _

lemma shiftChart_apply (hne : M.O.Nonempty) (x₀ : (M.toMPolyfold hne).Level 1)
    (x : (M.toMPolyfold hne).Level 1) : shiftChart hne x₀ x = (shiftEquivFun hne x).1 := rfl

lemma continuous_shiftChart (hne : M.O.Nonempty) (x₀ : (M.toMPolyfold hne).Level 1) :
    Continuous (shiftChart hne x₀) := by
  refine continuousOn_univ.1 ((shiftChart hne x₀).continuousOn_toFun.mono fun x _ => ?_)
  exact mem_shiftChart_source hne x₀ x

theorem isScSmoothMap_shiftEquivFun (hne : M.O.Nonempty) (hne1 : M.shift.O.Nonempty) :
    (M.toMPolyfold hne).shift.IsScSmoothMap (M.shift.toMPolyfold hne1) (shiftEquivFun hne) := by
  set x₀ := shiftEquivInv hne ⟨hne1.some, hne1.some_mem⟩
  have hχ := (M.toMPolyfold hne).shift_isChart (M.selfChart_isChart' hne) x₀
  have hψ := M.shift.selfChart_isChart' hne1
  have hcont : Continuous (shiftEquivFun hne) :=
    (continuous_shiftChart hne x₀).subtype_mk _
  refine IsScSmoothOn.of_exists_charts isOpen_univ hcont.continuousOn fun x _ =>
    ⟨shiftChart hne x₀, M.shift.selfChart hne1, univ, hχ, hψ, isOpen_univ, mem_univ x,
      fun y _ => ⟨mem_univ y, mem_shiftChart_source hne x₀ y⟩, fun y _ => mem_univ _, ?_⟩
  refine ((isScSmoothRetractMap_id _).mono_target
    fun z hz => (shiftChart hne x₀).image_subset_model (fun y _ => mem_shiftChart_source hne x₀ y)
      hz).congr ?_
  rintro _ ⟨y, -, rfl⟩
  simp only [Function.comp_apply, id,
    (shiftChart hne x₀).symm_apply_apply (mem_shiftChart_source hne x₀ y)]
  rfl

theorem isScSmoothMap_shiftEquivInv (hne : M.O.Nonempty) (hne1 : M.shift.O.Nonempty) :
    (M.shift.toMPolyfold hne1).IsScSmoothMap (M.toMPolyfold hne).shift (shiftEquivInv hne) := by
  set x₀ := shiftEquivInv hne ⟨hne1.some, hne1.some_mem⟩
  set χ := shiftChart hne x₀
  have hχ := (M.toMPolyfold hne).shift_isChart (M.selfChart_isChart' hne) x₀
  have hψ := M.shift.selfChart_isChart' hne1
  have hχinv : ∀ z : M.shift.O, χ.symm z.1 = shiftEquivInv hne z := by
    intro z
    have h1 : χ (shiftEquivInv hne z) = z.1 := by
      rw [shiftChart_apply, shiftEquivFun_shiftEquivInv]
    rw [← h1, χ.symm_apply_apply (mem_shiftChart_source hne x₀ _)]
  have hcont : Continuous (shiftEquivInv hne) := by
    have : ContinuousOn χ.symm χ.model.O := χ.continuousOn_invFun
    refine (this.comp_continuous continuous_subtype_val fun z => z.2).congr fun z => ?_
    exact hχinv z
  refine IsScSmoothOn.of_exists_charts isOpen_univ hcont.continuousOn fun z _ =>
    ⟨M.shift.selfChart hne1, χ, univ, hψ, hχ, isOpen_univ, mem_univ z,
      fun y _ => ⟨mem_univ y, mem_univ y⟩, fun y _ => mem_shiftChart_source hne x₀ _, ?_⟩
  refine ((isScSmoothRetractMap_id _).mono_target
    fun w hw => (M.shift.selfChart hne1).image_subset_model (fun y _ => mem_univ y) hw).congr ?_
  rintro _ ⟨y, -, rfl⟩
  simp only [Function.comp_apply, id,
    (M.shift.selfChart hne1).symm_apply_apply (mem_univ y)]
  change y.1 = χ (shiftEquivInv hne y)
  rw [shiftChart_apply, shiftEquivFun_shiftEquivInv]

/-- **The level `1` of the M-polyfold of a retract `(O, C, E)` is the M-polyfold of
`(O¹, C¹, E¹)`.** -/
def shiftEquiv (hne : M.O.Nonempty) (hne1 : M.shift.O.Nonempty) :
    ScEquiv (M.toMPolyfold hne).shift (M.shift.toMPolyfold hne1) where
  toFun := shiftEquivFun hne
  invFun := shiftEquivInv hne
  left_inv := shiftEquivInv_shiftEquivFun hne
  right_inv := shiftEquivFun_shiftEquivInv hne
  isScSmoothMap_toFun := isScSmoothMap_shiftEquivFun hne hne1
  isScSmoothMap_invFun := isScSmoothMap_shiftEquivInv hne hne1

variable (M) in
/-- The model `(Oᵐ, Cᵐ, Eᵐ)`. -/
def shiftIter : ℕ → LocalModel
  | 0 => M
  | m + 1 => (shiftIter m).shift

/-- **The `m`-th lift of the M-polyfold of `O` is the M-polyfold of `Oᵐ`.** -/
def liftEquiv (hne : ∀ m, (M.shiftIter m).O.Nonempty) :
    ∀ m, ScEquiv ((BundledMPolyfold.of (M.toMPolyfold (hne 0))).lift m).P
      ((M.shiftIter m).toMPolyfold (hne m))
  | 0 => ScEquiv.refl _
  | m + 1 => (liftEquiv hne m).shift.trans (shiftEquiv (M := M.shiftIter m) (hne m) (hne (m + 1)))

end LocalModel

end Polyfold
