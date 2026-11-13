import Polyfold.Chapter5.Book2021
import Polyfold.Chapter8.StrongBundleMap

/-!
# Remark 5.3.14: generalized compact homotopies up to isomorphism

2021 Remark 5.3.14, p. 223 (2017: Remark 5.5; preprint: Remark 5.21).  Definition 5.3.13 asks that
the restrictions of `(f, P)` to `X_i = t⁻¹(i)` *be* the given compact sc-Fredholm problems
`(f_i, P_i)`.  The remark says one should rather ask that they be isomorphic, with the isomorphisms
part of the data.  This file formalizes that reading.

## What is formalized

* `StrongBundle.IsProblemIso`: an isomorphism of sc-Fredholm problems `(f, P) ≅ (f', P')`, a strong
  bundle isomorphism (`IsStrongBundleIso`, `Chapter8/StrongBundleMap.lean`) `Φ` covering `h` with
  `Φ ∘ f = f' ∘ h`.  It is reflexive, symmetric and transitive (`IsProblemIso.refl`, `symm`,
  `trans`), and it carries solution sets to solution sets (`IsProblemIso.image_solutionSet`), so it
  preserves their compactness (`IsProblemIso.isCompact_solutionSet_iff`).
* `StrongBundle.IsGenCompactHomotopyBetween`: a generalized compact homotopy (2021 Definition
  5.3.13, `IsSubmersiveGenCompactHomotopy`) between two given problems `(f₀, P₀)`, `(f₁, P₁)`,
  read through Remark 5.3.14: the end restrictions are isomorphic to the given problems.
* `IsSubmersiveGenCompactHomotopy.isGenCompactHomotopyBetween`: a generalized compact homotopy
  is one between its own end restrictions (Definition 5.3.13 as printed is the case of the
  identity isomorphisms).
* `IsGenCompactHomotopyBetween.congr_left`, `congr_right`: the notion depends only on the
  isomorphism classes of the end problems, which is the point of the remark.
* `IsGenCompactHomotopyBetween.isCompact_solutionSet_left`, `_right`: the given end problems are
  compact problems.
-/

open Set Function

noncomputable section

namespace Polyfold

universe u v u₀ v₀ u₁ v₁

section ProblemIso

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {X'' : Type*} [TopologicalSpace X''] [T2Space X''] [ParacompactSpace X''] {PX'' : MPolyfold X''}
  {Y'' : Type*} [TopologicalSpace Y''] [T2Space Y''] [ParacompactSpace Y''] {P'' : Y'' → X''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]

namespace StrongBundle

/-- **An isomorphism of sc-Fredholm problems** `(f, P) ≅ (f', P')` (2021 Remark 5.3.14, p. 223): a
strong bundle isomorphism `Φ : Y → Y'` covering `h : X → X'` (inverse `Ψ` covering `g`) with
`Φ ∘ f = f' ∘ h`. -/
def IsProblemIso (B : StrongBundle PX P) (f : X → Y) (B' : StrongBundle PX' P') (f' : X' → Y') :
    Prop :=
  ∃ (h : X → X') (Φ : Y → Y') (g : X' → X) (Ψ : Y' → Y),
    B.IsStrongBundleIso B' h Φ g Ψ ∧ ∀ x, Φ (f x) = f' (h x)

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {B'' : StrongBundle PX'' P''}

/-- A strong bundle map sends the zero of the fibre over `x` to the zero over `h(x)`. -/
lemma IsStrongBundleMap.map_fiberZero {h : X → X'} {Φ : Y → Y'}
    (hΦ : B.IsStrongBundleMap B' h Φ) (x : X) : Φ (fiberZero P x) = fiberZero P' (h x) := by
  have h0 := (hΦ.fiber_linear x).map_zero
  have := congrArg Subtype.val h0
  exact this

variable (B) in
theorem IsProblemIso.refl (f : X → Y) : B.IsProblemIso f B f :=
  ⟨id, id, id, id, IsStrongBundleIso.refl B, fun _ => rfl⟩

theorem IsProblemIso.symm {f : X → Y} {f' : X' → Y'} (hi : B.IsProblemIso f B' f') :
    B'.IsProblemIso f' B f := by
  obtain ⟨h, Φ, g, Ψ, hiso, hf⟩ := hi
  refine ⟨g, Ψ, h, Φ, hiso.symm, fun x' => ?_⟩
  have := congrArg Ψ (hf (g x'))
  rw [hiso.left_inv, hiso.base_right_inv] at this
  exact this.symm

theorem IsProblemIso.trans {f : X → Y} {f' : X' → Y'} {f'' : X'' → Y''}
    (hi : B.IsProblemIso f B' f') (hi' : B'.IsProblemIso f' B'' f'') :
    B.IsProblemIso f B'' f'' := by
  obtain ⟨h, Φ, g, Ψ, hiso, hf⟩ := hi
  obtain ⟨h', Φ', g', Ψ', hiso', hf'⟩ := hi'
  refine ⟨h' ∘ h, Φ' ∘ Φ, g ∘ g', Ψ ∘ Ψ', hiso.trans hiso', fun x => ?_⟩
  simp only [Function.comp_apply, hf, hf']

/-- An isomorphism of problems maps the zeros of `f` onto the zeros of `f'`. -/
theorem IsProblemIso.image_solutionSet {f : X → Y} {f' : X' → Y'}
    (hi : B.IsProblemIso f B' f') : ∃ g : X' → X, Continuous g ∧
      g '' solutionSet P' f' = solutionSet P f := by
  obtain ⟨h, Φ, g, Ψ, hiso, hf⟩ := hi
  refine ⟨g, continuousOn_univ.1 hiso.invMap.isScSmoothMap_base.continuousOn, ?_⟩
  ext x
  constructor
  · rintro ⟨x', hx', rfl⟩
    have h1 : Ψ (f' x') = f (g x') := by
      have := congrArg Ψ (hf (g x'))
      rw [hiso.left_inv, hiso.base_right_inv] at this
      exact this.symm
    change f (g x') = fiberZero P (g x')
    rw [← h1, show f' x' = fiberZero P' x' from hx', hiso.invMap.map_fiberZero]
  · intro hx
    refine ⟨h x, ?_, hiso.base_left_inv x⟩
    change f' (h x) = fiberZero P' (h x)
    rw [← hf, show f x = fiberZero P x from hx, hiso.toMap.map_fiberZero]

/-- Isomorphic problems have compact solution sets together. -/
theorem IsProblemIso.isCompact_solutionSet_iff {f : X → Y} {f' : X' → Y'}
    (hi : B.IsProblemIso f B' f') :
    IsCompact (solutionSet P f) ↔ IsCompact (solutionSet P' f') := by
  constructor
  · intro hc
    obtain ⟨g, hg, hgS⟩ := hi.symm.image_solutionSet
    rw [← hgS]; exact hc.image hg
  · intro hc
    obtain ⟨g, hg, hgS⟩ := hi.image_solutionSet
    rw [← hgS]; exact hc.image hg

end StrongBundle

end ProblemIso

section Between

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X₀ : Type u₀} [TopologicalSpace X₀] [T2Space X₀] [ParacompactSpace X₀] {PX₀ : MPolyfold X₀}
  {Y₀ : Type v₀} [TopologicalSpace Y₀] [T2Space Y₀] [ParacompactSpace Y₀] {P₀ : Y₀ → X₀}
  [∀ x, AddCommGroup (P₀ ⁻¹' {x})] [∀ x, Module ℝ (P₀ ⁻¹' {x})]
  {X₁ : Type u₁} [TopologicalSpace X₁] [T2Space X₁] [ParacompactSpace X₁] {PX₁ : MPolyfold X₁}
  {Y₁ : Type v₁} [TopologicalSpace Y₁] [T2Space Y₁] [ParacompactSpace Y₁] {P₁ : Y₁ → X₁}
  [∀ x, AddCommGroup (P₁ ⁻¹' {x})] [∀ x, Module ℝ (P₁ ⁻¹' {x})]

namespace StrongBundle

variable (B : StrongBundle PX P)

/-- The end `t⁻¹(i)` of `(f, P)` is isomorphic to the problem `(f', P')`: `t⁻¹(i)` is a
sub-M-polyfold and the restriction `f|t⁻¹(i)` of `f` (a section of the pull-back of `P` to
`t⁻¹(i)`, `restrictSection`) is isomorphic to `(f', P')`. -/
def EndIso (f : X → Y) (hf : IsSection P f) (A : Set X) {X' : Type*} [TopologicalSpace X']
    [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'} {Y' : Type*} [TopologicalSpace Y']
    [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'} [∀ x, AddCommGroup (P' ⁻¹' {x})]
    [∀ x, Module ℝ (P' ⁻¹' {x})] (B' : StrongBundle PX' P') (f' : X' → Y') : Prop :=
  ∃ hsub : PX.IsSubMPolyfold A,
    haveI := PX.paracompactSpace_subtype A
    haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : A → X))
      (MPolyfold.subPolyfold hsub) B
    (B.pullback (MPolyfold.subPolyfold_inclusion_isScSmooth hsub)).IsProblemIso
      (restrictSection P A f hf) B' f'

/-- **2021 Definition 5.3.13 with Remark 5.3.14, p. 223: a generalized compact homotopy between
the compact sc-Fredholm problems `(f₀, P₀)` and `(f₁, P₁)`.**  The data `(P, f, t)` form a
generalized compact homotopy (`IsSubmersiveGenCompactHomotopy`), and the restrictions of `(f, P)`
to `t⁻¹(0)` and `t⁻¹(1)` are isomorphic to `(f₀, P₀)` and `(f₁, P₁)` (`EndIso`), as Remark 5.3.14
proposes in place of the equalities `(f|Xᵢ, P|Yᵢ) = (fᵢ, Pᵢ)`. -/
def IsGenCompactHomotopyBetween (f : X → Y) (t : X → ℝ) (B₀ : StrongBundle PX₀ P₀)
    (f₀ : X₀ → Y₀) (B₁ : StrongBundle PX₁ P₁) (f₁ : X₁ → Y₁) : Prop :=
  ∃ h : B.IsSubmersiveGenCompactHomotopy f t,
    B.EndIso f h.isScFredholm.isScSmooth.1 (t ⁻¹' {0}) B₀ f₀ ∧
    B.EndIso f h.isScFredholm.isScSmooth.1 (t ⁻¹' {1}) B₁ f₁

variable {B}

/-- An end isomorphism can be composed with an isomorphism of the given problem. -/
theorem EndIso.trans {f : X → Y} {hf : IsSection P f} {A : Set X}
    {B₀ : StrongBundle PX₀ P₀} {f₀ : X₀ → Y₀} {B₁ : StrongBundle PX₁ P₁} {f₁ : X₁ → Y₁}
    (he : B.EndIso f hf A B₀ f₀) (hi : B₀.IsProblemIso f₀ B₁ f₁) : B.EndIso f hf A B₁ f₁ := by
  obtain ⟨hsub, he⟩ := he
  have := PX.paracompactSpace_subtype A
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : A → X))
    (MPolyfold.subPolyfold hsub) B
  exact ⟨hsub, he.trans hi⟩

/-- **The notion depends only on the isomorphism class of the first end problem** (the point of
Remark 5.3.14). -/
theorem IsGenCompactHomotopyBetween.congr_left {f : X → Y} {t : X → ℝ}
    {B₀ : StrongBundle PX₀ P₀} {f₀ : X₀ → Y₀} {B₁ : StrongBundle PX₁ P₁} {f₁ : X₁ → Y₁}
    {X₂ : Type*} [TopologicalSpace X₂] [T2Space X₂] [ParacompactSpace X₂] {PX₂ : MPolyfold X₂}
    {Y₂ : Type*} [TopologicalSpace Y₂] [T2Space Y₂] [ParacompactSpace Y₂] {P₂ : Y₂ → X₂}
    [∀ x, AddCommGroup (P₂ ⁻¹' {x})] [∀ x, Module ℝ (P₂ ⁻¹' {x})] {B₂ : StrongBundle PX₂ P₂}
    {f₂ : X₂ → Y₂} (h : B.IsGenCompactHomotopyBetween f t B₀ f₀ B₁ f₁)
    (hi : B₀.IsProblemIso f₀ B₂ f₂) : B.IsGenCompactHomotopyBetween f t B₂ f₂ B₁ f₁ := by
  obtain ⟨h, h₀, h₁⟩ := h
  exact ⟨h, h₀.trans hi, h₁⟩

/-- **The notion depends only on the isomorphism class of the second end problem.** -/
theorem IsGenCompactHomotopyBetween.congr_right {f : X → Y} {t : X → ℝ}
    {B₀ : StrongBundle PX₀ P₀} {f₀ : X₀ → Y₀} {B₁ : StrongBundle PX₁ P₁} {f₁ : X₁ → Y₁}
    {X₂ : Type*} [TopologicalSpace X₂] [T2Space X₂] [ParacompactSpace X₂] {PX₂ : MPolyfold X₂}
    {Y₂ : Type*} [TopologicalSpace Y₂] [T2Space Y₂] [ParacompactSpace Y₂] {P₂ : Y₂ → X₂}
    [∀ x, AddCommGroup (P₂ ⁻¹' {x})] [∀ x, Module ℝ (P₂ ⁻¹' {x})] {B₂ : StrongBundle PX₂ P₂}
    {f₂ : X₂ → Y₂} (h : B.IsGenCompactHomotopyBetween f t B₀ f₀ B₁ f₁)
    (hi : B₁.IsProblemIso f₁ B₂ f₂) : B.IsGenCompactHomotopyBetween f t B₀ f₀ B₂ f₂ := by
  obtain ⟨h, h₀, h₁⟩ := h
  exact ⟨h, h₀, h₁.trans hi⟩

/-- The solution set of an end problem isomorphic to the restriction `f|A`, `A` closed, is compact
when `S_f` is. -/
theorem EndIso.isCompact_solutionSet {f : X → Y} {hf : IsSection P f} {A : Set X}
    (hA : IsClosed A) (hS : IsCompact (solutionSet P f)) {B₀ : StrongBundle PX₀ P₀}
    {f₀ : X₀ → Y₀} (he : B.EndIso f hf A B₀ f₀) : IsCompact (solutionSet P₀ f₀) := by
  obtain ⟨hsub, he⟩ := he
  have := PX.paracompactSpace_subtype A
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : A → X))
    (MPolyfold.subPolyfold hsub) B
  refine he.isCompact_solutionSet_iff.1 ?_
  have heq : solutionSet (pullbackProj P (Subtype.val : A → X)) (restrictSection P A f hf) =
      Subtype.val ⁻¹' solutionSet P f := by
    ext a
    exact isZeroAt_restrictSection_iff hf a
  rw [heq]
  exact hA.isClosedEmbedding_subtypeVal.isCompact_preimage hS

/-- **The given end problems are compact sc-Fredholm problems** (the hypothesis of Definition
5.3.13 on `(fᵢ, Pᵢ)`), first end. -/
theorem IsGenCompactHomotopyBetween.isCompact_solutionSet_left {f : X → Y} {t : X → ℝ}
    {B₀ : StrongBundle PX₀ P₀} {f₀ : X₀ → Y₀} {B₁ : StrongBundle PX₁ P₁} {f₁ : X₁ → Y₁}
    (h : B.IsGenCompactHomotopyBetween f t B₀ f₀ B₁ f₁) : IsCompact (solutionSet P₀ f₀) := by
  obtain ⟨h, h₀, -⟩ := h
  have hcont : Continuous t := continuousOn_univ.1 h.isScSmooth_t.continuousOn
  exact h₀.isCompact_solutionSet (isClosed_singleton.preimage hcont) h.isCompact

/-- **The given end problems are compact sc-Fredholm problems**, second end. -/
theorem IsGenCompactHomotopyBetween.isCompact_solutionSet_right {f : X → Y} {t : X → ℝ}
    {B₀ : StrongBundle PX₀ P₀} {f₀ : X₀ → Y₀} {B₁ : StrongBundle PX₁ P₁} {f₁ : X₁ → Y₁}
    (h : B.IsGenCompactHomotopyBetween f t B₀ f₀ B₁ f₁) : IsCompact (solutionSet P₁ f₁) := by
  obtain ⟨h, -, h₁⟩ := h
  have hcont : Continuous t := continuousOn_univ.1 h.isScSmooth_t.continuousOn
  exact h₁.isCompact_solutionSet (isClosed_singleton.preimage hcont) h.isCompact

/-- **Definition 5.3.13 as printed is the case of the identity isomorphisms**: a generalized
compact homotopy is a generalized compact homotopy between its own end restrictions. -/
theorem IsSubmersiveGenCompactHomotopy.isGenCompactHomotopyBetween {f : X → Y} {t : X → ℝ}
    (h : B.IsSubmersiveGenCompactHomotopy f t) (hsub₀ : PX.IsSubMPolyfold (t ⁻¹' {0}))
    (hsub₁ : PX.IsSubMPolyfold (t ⁻¹' {1})) :
    haveI := PX.paracompactSpace_subtype (t ⁻¹' {0})
    haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : t ⁻¹' {0} → X))
      (MPolyfold.subPolyfold hsub₀) B
    haveI := PX.paracompactSpace_subtype (t ⁻¹' {1})
    haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : t ⁻¹' {1} → X))
      (MPolyfold.subPolyfold hsub₁) B
    B.IsGenCompactHomotopyBetween f t
      (B.pullback (MPolyfold.subPolyfold_inclusion_isScSmooth hsub₀))
      (restrictSection P (t ⁻¹' {0}) f h.isScFredholm.isScSmooth.1)
      (B.pullback (MPolyfold.subPolyfold_inclusion_isScSmooth hsub₁))
      (restrictSection P (t ⁻¹' {1}) f h.isScFredholm.isScSmooth.1) := by
  have := PX.paracompactSpace_subtype (t ⁻¹' {0})
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : t ⁻¹' {0} → X))
    (MPolyfold.subPolyfold hsub₀) B
  have := PX.paracompactSpace_subtype (t ⁻¹' {1})
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : t ⁻¹' {1} → X))
    (MPolyfold.subPolyfold hsub₁) B
  exact ⟨h, ⟨hsub₀, StrongBundle.IsProblemIso.refl _ _⟩,
    ⟨hsub₁, StrongBundle.IsProblemIso.refl _ _⟩⟩

end StrongBundle

end Between

end Polyfold
