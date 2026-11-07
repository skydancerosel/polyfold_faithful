import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_60

/-! Round trip for V6_60 (Definition 6.40, orientations of sc-Fredholm sections, §6.5, p. 229).

A is `isSectionOrientation_iff ∧ exists_isSectionOrientation_iff ∧
IsSectionOrientation.apply_eq_iff ∧ IsSectionOrientation.exists_two` (universes at `0`).  These
theorems are stated under tameness, bump functions, tame germ data and sc⁺-sections through
points.  They describe the project's `IsSectionOrientation` through `Γ_f`.  B is the definitional
statement `IsSectionOrientation f hf o ↔ D640 f hf o` for every M-polyfold (no tameness).

* `A ⇒ B` is not proved.  `IsSectionOrientation → D640` is glue and IS proved below
  (`D640_of_isSectionOrientation`): a sc-smoothly contractible open `U` with the local
  propagation property is a project orientable neighbourhood `(U, V := U)`, since the contraction
  joins its smooth points by sc-smooth paths in `U` (`exists_path_of_contractible`).
  The converse `D640 → IsSectionOrientation` is the obstruction.  The project asks continuity over
  `V` for paths in `U`, for every pair `V ⊆ U`.  `D640` constrains `o` only on sc-smoothly
  contractible open sets.  To transport it to a pair one must cut a path in `U` into pieces lying
  in sc-smoothly contractible open subsets of `U`, then compose the push-forwards
  (`HasLocalPropagation.eq_trans`).  That needs a basis of sc-smoothly contractible neighbourhoods
  at smooth points, which neither A nor the project provides.  It is mathematics, not glue.  If
  such neighbourhoods are missing near some point, `D640` is vacuous there while
  `IsSectionOrientation` is not.  A cannot help: it says nothing about `D640`, and nothing without
  its extra hypotheses.
* `B ⇒ A` is not proved: B compares two definitions, while A's theorems relate the definition to
  `Γ_f`.  Getting A from B means re-proving A outright.
-/

namespace RoundTrip.V6_60
open Polyfold CategoryTheory Set
open scoped ContDiff

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.isSectionOrientation_iff.{0, 0} ∧
    type_of% @Polyfold.exists_isSectionOrientation_iff.{0, 0} ∧
    type_of% @Polyfold.IsSectionOrientation.apply_eq_iff.{0, 0} ∧
    type_of% @Polyfold.IsSectionOrientation.exists_two.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.isSectionOrientation_iff.{0, 0}, @Polyfold.exists_isSectionOrientation_iff.{0, 0},
    @Polyfold.IsSectionOrientation.apply_eq_iff.{0, 0},
    @Polyfold.IsSectionOrientation.exists_two.{0, 0}⟩

section Paths

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]

/-- A reparametrized contraction line `s ↦ H(κ(s), y)` is an sc-smooth path in `U`. -/
theorem contraction_path {U : Set X} {H : (Fin 1 → ℝ) × X → X} {W : Set ((Fin 1 → ℝ) × X)}
    (hWU : Icc (0 : Fin 1 → ℝ) 1 ×ˢ U ⊆ W) (hH : ((rnPolyfold 1).prod PX).IsScSmoothOn PX H W)
    (hHU : ∀ t ∈ Icc (0 : Fin 1 → ℝ) 1, ∀ y ∈ U, H (t, y) ∈ U) {κ : ℝ → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hκI : ∀ s, κ s ∈ Icc (0 : ℝ) 1) {y : X} (hy : y ∈ U)
    (hys : y ∈ PX.smoothSet) :
    (rnPolyfold 1).IsScSmoothMap PX (fun s : Fin 1 → ℝ => H (pt1 (κ (s 0)), y)) ∧
      ∀ s : Fin 1 → ℝ, H (pt1 (κ (s 0)), y) ∈ U := by
  refine ⟨?_, fun s => hHU _ (pt1_mem_Icc (hκI _)) y hy⟩
  have hin : (rnPolyfold 1).IsScSmoothMap ((rnPolyfold 1).prod PX)
      (fun s : Fin 1 → ℝ => (pt1 (κ (s 0)), y)) :=
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_rn_rn_of_contDiff (contDiff_pt1_comp hκ))
      (isScSmoothMap_const_of_mem_smoothSet hys)
  exact MPolyfold.IsScSmoothOn.comp hH hin (fun s _ => hWU ⟨pt1_mem_Icc (hκI _), hy⟩)

/-- **An sc-smoothly contractible set joins its smooth points by sc-smooth paths in it.** -/
theorem exists_path_of_contractible {U : Set X} (hU : IsScContractibleB PX U) {y₁ y₂ : X}
    (h₁ : y₁ ∈ U) (h₂ : y₂ ∈ U) (hs₁ : y₁ ∈ PX.smoothSet) (hs₂ : y₂ ∈ PX.smoothSet) :
    ∃ γ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ ∧ γ (pt1 0) = y₁ ∧
      γ (pt1 1) = y₂ ∧ ∀ t, γ t ∈ U := by
  obtain ⟨H, y₀, W, -, hWU, hH, hHU, hH1, hH0⟩ := hU
  have hκI : ∀ s, Real.smoothTransition s ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨Real.smoothTransition.nonneg s, Real.smoothTransition.le_one s⟩
  have hκ' : ContDiff ℝ ∞ fun s : ℝ => Real.smoothTransition (1 - s) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
  obtain ⟨hρs, hρU⟩ := contraction_path hWU hH hHU hκ' (fun s => hκI _) h₁ hs₁
  obtain ⟨hσs, hσU⟩ := contraction_path hWU hH hHU Real.smoothTransition.contDiff hκI h₂ hs₂
  refine ⟨concatPath (fun s : Fin 1 → ℝ => H (pt1 (Real.smoothTransition (1 - s 0)), y₁))
    (fun s : Fin 1 → ℝ => H (pt1 (Real.smoothTransition (s 0)), y₂)),
    isScSmoothMap_concatPath hρs hσs ?_, ?_, ?_, ?_⟩
  · simp only [pt1_apply, sub_self, Real.smoothTransition.zero]
    rw [hH0 y₁ h₁, hH0 y₂ h₂]
  · rw [concatPath_zero]
    simp only [pt1_apply, sub_zero, Real.smoothTransition.one]
    exact hH1 y₁ h₁
  · rw [concatPath_one]
    simp only [pt1_apply, Real.smoothTransition.one]
    exact hH1 y₂ h₂
  · intro t
    unfold concatPath
    split_ifs
    · exact hρU _
    · exact hσU _

end Paths

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **One implication of B**: a project orientation of `f` (continuity over every pair `V ⊆ U`) is
an orientation in the text's sense (continuity over every sc-smoothly contractible `U` with the
local propagation property), taking the pair `(U, U)`. -/
theorem D640_of_isSectionOrientation {Bd : StrongBundle PX P} {f : X → Y}
    {hf : Bd.IsScFredholmSection f} {o : (y : X) → (hy : y ∈ PX.smoothSet) → Orx f hf y hy}
    (ho : IsSectionOrientation f hf o) : D640 f hf o := by
  intro x hx U c hc _hUc hUo hxU hUcon hLP
  exact ho x hx c hc U U ⟨hLP, hUo, hUo, le_refl U, hxU,
    fun y₁ h₁ y₂ h₂ hs₁ hs₂ => exists_path_of_contractible hUcon h₁ h₂ hs₁ hs₂⟩

end Glue

#rt_check RoundTrip.V6_60.D640_of_isSectionOrientation [Polyfold.isSectionOrientation_iff,
  Polyfold.exists_isSectionOrientation_iff, Polyfold.IsSectionOrientation.apply_eq_iff,
  Polyfold.IsSectionOrientation.exists_two]

end RoundTrip.V6_60
