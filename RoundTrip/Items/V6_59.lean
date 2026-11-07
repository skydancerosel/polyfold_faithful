import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_59

/-! Round trip for V6_59 (Definition 6.39 and "an equivalent version", §6.5, p. 229).

A is `isOrientableSection'_iff_exists ∧ isOrientableSection_iff` (universes at `0`).

* `B ⇒ A` is proved: B's (2) applied to `Γ_f = orFunctorMap` (which has B's `IsGammaF`: the
  project's (∗) on all open sets restricts to the sc-smoothly contractible ones) gives
  `IsOrientableSection ↔ D639`, B's (1) gives `D639 ↔ IsOrientableSection'`; the first conjunct of
  A then follows with `isOrientableSection_iff_exists` (Definition 6.38, not an item theorem).
* `A ⇒ B` is not proved.  The obstruction is one implication of B's (1),
  `IsOrientableSection' f hf → D639 f hf`: the project's orientable neighbourhood is a pair
  `V ⊆ U` (paths between smooth points of `V` run in `U`), B's is a single open `U` which is
  sc-smoothly contractible.  From a pair one needs an sc-smoothly contractible open `U'` with
  `x ∈ U' ⊆ V` (then `U'` inherits the local propagation property from `U`, and the continuity
  over `V` restricts to `U'`): a basis of sc-smoothly contractible neighbourhoods at smooth points,
  which neither A nor the project provides (the retract `r(V')` of Proposition 6.28 is not shown
  contractible; `r(t·y)` contracts a small `V` inside a larger `U` only).  This is mathematics,
  not glue, and its truth for a general (even tame) M-polyfold is open here.  A also cannot be
  applied in B's (2) setting, which has neither bump functions, nor sc⁺-sections through points,
  nor tame germ data.
* The other implication of B's (1), `D639 → IsOrientableSection'`, IS proved below
  (`isOrientableSection'_of_D639`): an sc-smoothly contractible `U` joins any two of its smooth
  points by an sc-smooth path in `U` (`exists_path_of_contractible`: from `y₁` back along the
  contraction to `y₀`, then out to `y₂`), so `(U, V := U)` is a project orientable neighbourhood.
-/

namespace RoundTrip.V6_59
open Polyfold CategoryTheory Set
open scoped ContDiff

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.isOrientableSection'_iff_exists.{0, 0} ∧
    type_of% @Polyfold.isOrientableSection_iff.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.isOrientableSection'_iff_exists.{0, 0}, @Polyfold.isOrientableSection_iff.{0, 0}⟩

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
    (fun s : Fin 1 → ℝ => H (pt1 (Real.smoothTransition (s 0)), y₂)), isScSmoothMap_concatPath hρs hσs ?_,
    ?_, ?_, ?_⟩
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

/-- **One implication of B's (1)**: the text's Definition 6.39 (sc-smoothly contractible
orientable neighbourhoods) implies the project's (pairs `V ⊆ U`), with `V = U`. -/
theorem isOrientableSection'_of_D639 {Bd : StrongBundle PX P} {f : X → Y}
    {hf : Bd.IsScFredholmSection f} (h : D639 f hf) : IsOrientableSection' f hf := by
  obtain ⟨o, ho⟩ := h
  refine ⟨o, fun x hx => ?_⟩
  obtain ⟨U, c, hc, hUc, hUo, hxU, hUcon, hLP, hcont⟩ := ho x hx
  exact ⟨c, hc, U, U, ⟨hLP, hUo, hUo, le_refl U, hxU,
    fun y₁ h₁ y₂ h₂ hs₁ hs₂ => exists_path_of_contractible hUcon h₁ h₂ hs₁ hs₂⟩, hcont⟩

/-- **The project's `Γ_f` is a functor with B's property (∗)** on the sc-smoothly contractible
open sets (the project's (∗) holds on all open sets). -/
theorem isGammaF_orFunctorMap
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    {Bd : StrongBundle PX P} {f : X → Y} (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : Bd.IsScFredholmSectionTame f) (hsec : Bd.HasScPlusSectionsThrough) :
    IsGammaF f hf.toIsScFredholmSection (fun _ _ a => orFunctorMap hX hbump hf hsec a) :=
  ⟨orFunctorMap_id hX hbump hf hsec, fun _ _ _ a b => orFunctorMap_comp hX hbump hf hsec a b,
    fun c hc U hU => orFunctorMap_isStarProperty hX hbump hf hsec c hc U hU.1⟩

/-- From B: Definitions 6.38 (project) and 6.39 (project) agree, through the text's 6.39. -/
theorem iff_of_B (hB : B)
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    {Bd : StrongBundle PX P} {f : X → Y} (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : Bd.IsScFredholmSectionTame f) (hsec : Bd.HasScPlusSectionsThrough) :
    IsOrientableSection hX hbump hf hsec ↔ IsOrientableSection' f hf.toIsScFredholmSection :=
  (hB.2 PX P Bd f hf.toIsScFredholmSection hX _ (isGammaF_orFunctorMap hX hbump hf hsec)).trans
    (hB.1 PX P Bd f hf.toIsScFredholmSection).symm

/-- **Partial `A ⇒ B` for B's (2), direction 6.39 ⇒ 6.38**, under A's extra hypotheses (bump
functions, tame germ data, sc⁺-sections through points): a `Γ` with B's `IsGammaF` is `Γ_f`
(uniqueness from (∗) on the contractible sets, which cover `X_∞` by `D639`), and then A and
`isOrientableSection'_of_D639` give `D638 Γ`.  The converse `D638 Γ → D639` is exactly the
missing `IsOrientableSection' → D639`. -/
theorem D638_of_D639_of_A (hA : A)
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    {Bd : StrongBundle PX P} {f : X → Y} (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : Bd.IsScFredholmSectionTame f) (hsec : Bd.HasScPlusSectionsThrough)
    (Γ : (x y : PathCat PX) → (x ⟶ y) →
      Orx f hf.toIsScFredholmSection x.pt x.smooth ≃ Orx f hf.toIsScFredholmSection y.pt y.smooth)
    (hΓ : IsGammaF f hf.toIsScFredholmSection Γ) (h : D639 f hf.toIsScFredholmSection) :
    D638 Γ := by
  have hcov : ∀ x ∈ PX.smoothSet, ∃ U, (IsOpen U ∧ IsScContractibleB PX U) ∧ x ∈ U ∧
      ∃ (c : StrongBundleChart PX P) (hc : Bd.IsChart c),
        HasLocalPropagation f hf.toIsScFredholmSection c hc U := by
    obtain ⟨o, ho⟩ := h
    intro x hx
    obtain ⟨U, c, hc, -, hUo, hxU, hUcon, hLP, -⟩ := ho x hx
    exact ⟨U, ⟨hUo, hUcon⟩, hxU, c, hc, hLP⟩
  have hΓeq := orFunctorMap_unique_of_cover hX hbump hf hsec _ (fun hU => hU.1) hcov Γ hΓ.2.1
    hΓ.2.2
  subst hΓeq
  exact (hA.2 hX hbump hf hsec).2 (isOrientableSection'_of_D639 h)

end Glue

/-- `B ⇒ A`. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ Bd f _ _ _ _ hX hbump hf hsec
    exact (iff_of_B hB hX hbump hf hsec).symm.trans
      (isOrientableSection_iff_exists hX hbump hf hsec)
  · intro X _ _ _ PX Y _ _ _ P _ _ Bd f _ _ _ _ hX hbump hf hsec
    exact iff_of_B hB hX hbump hf hsec

#rt_check RoundTrip.V6_59.B_to_A [Polyfold.isOrientableSection'_iff_exists,
  Polyfold.isOrientableSection_iff]
#rt_overlap RoundTrip.V6_59.B_to_A [Polyfold.isOrientableSection'_iff_exists,
  Polyfold.isOrientableSection_iff]
#rt_check RoundTrip.V6_59.isOrientableSection'_of_D639 [Polyfold.isOrientableSection'_iff_exists,
  Polyfold.isOrientableSection_iff]
#rt_check RoundTrip.V6_59.D638_of_D639_of_A [Polyfold.isOrientableSection'_iff_exists,
  Polyfold.isOrientableSection_iff]

end RoundTrip.V6_59
