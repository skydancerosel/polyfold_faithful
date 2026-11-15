import Polyfold.Chapter6.SolutionOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6, p. 275:
**Theorem 6.6.18** (preprint Theorem 6.41), the continuity of the tangent orientations along a
path of zeros, for a given continuous family of the kernels.

# The tangent orientations along a path of zeros with onto linearizations

## The text, paraphrased

(Theorem 6.6.18, proof) At `x ∈ S`, `ker f'(x) = T_xS`, and since `f'(x)` is onto, `T_xS` is
oriented by `o_f(x)`.  Since `o_f` has the local continuation property, the local prolongation of
the orientation of `S` is the Fredholm one.

## What is formalized

* **`isLineOrientation_tangentOr_of_family`**: for a continuous orientation `o` over `V ⊆ U`
  (Definition 6.6.12), an sc-smooth path `γ` with `γ([0, 1]) ⊆ V` through zeros of `f` at which
  `f'` is onto, and a continuous family `Λ` of subspaces with `Λ_q = ker f'(γ_q)`, the tangent
  orientations `q ↦ tangentOr(o_{γ_q})` form an orientation of the line bundle `λ(Λ)`.
* `isLineOrientation_tangentOr_of_family_of_isSectionOrientation`: the same for an orientation
  of `f` (Definition 6.6.16) and an orientable neighbourhood.

`isLineOrientation_tangentOr` (`SolutionOrientation.lean`) is the case of the family
`tangentFamily`, which exists along paths of zeros in general position.  Here the family is a
datum; only the surjectivity of `f'(γ_q)` is used, so the statement applies to paths through
boundary points at which the solution set is in good position.
-/

set_option maxSynthPendingDepth 3

open Module TensorProduct Bundle Topology Set

noncomputable section

namespace Polyfold

universe u v

section TangentFamily

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **Theorem 6.6.18, continuity of the tangent orientations for a given family of kernels**:
for a continuous orientation `o` over `V ⊆ U` (Definition 6.6.12), an sc-smooth path `γ` with
`γ([0, 1]) ⊆ V` through zeros of `f` with `f'(γ_q)` onto, and a continuous family `Λ` of
subspaces over `[0, 1]` with `Λ_q = ker f'(γ_q)`, the tangent orientations
`q ↦ tangentOr(o_{γ_q})` form an orientation of the line bundle `λ(Λ)`.  (The proof of
`isLineOrientation_tangentOr`, in which the family is `tangentFamily`.) -/
theorem isLineOrientation_tangentOr_of_family (hf : B.IsScFredholmSection f)
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {U V : Set X} {hUc : U ⊆ c.φ.source}
    {hVU : V ⊆ U}
    {o : ∀ y (hy : y ∈ V) (hys : y ∈ PX.smoothSet), (chartPtOf c hc (hUc (hVU hy)) hys).Or f hf}
    (ho : IsContinuousOrientation f hf c hc hUc hVU o)
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ V)
    (hγ0 : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f (γ q))
    (hγL : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, B.IsLinSurjAt f (γ q))
    (Λ : SubspaceFamily (Icc (0 : Fin 1 → ℝ) 1) (c.φ.model.E 0))
    (hΛ : ∀ q : Icc (0 : Fin 1 → ℝ) 1, Λ.L q = c.linKer f
      (chartPtOf c hc (hUc (hVU (hγV q q.2))) (hf.mem_smoothSet_of_isZeroAt (hγ0 q q.2))).z) :
    IsLineOrientation (Λ.congrL _ hΛ).det
      fun q => tangentOrAt f hf c hc (hUc (hVU (hγV q q.2)))
        (hf.mem_smoothSet_of_isZeroAt (hγ0 q q.2)) (hγ0 q q.2) (hγL q q.2)
        (o (γ q) (hγV q q.2) (hf.mem_smoothSet_of_isZeroAt (hγ0 q q.2))) := by
  set Λ₀ := Λ.congrL _ hΛ with hΛdef
  set τ : ∀ q, Module.Ray ℝ (Λ₀.det q) := fun q => tangentOrAt f hf c hc (hUc (hVU (hγV q q.2)))
    (hf.mem_smoothSet_of_isZeroAt (hγ0 q q.2)) (hγ0 q q.2) (hγL q q.2)
    (o (γ q) (hγV q q.2) (hf.mem_smoothSet_of_isZeroAt (hγ0 q q.2))) with hτdef
  obtain ⟨O, hO⟩ := exists_lineOrientation_apply_eq (L := Λ₀.det) iccZero (τ iccZero)
  suffices h : ∀ t, O t = τ t by
    have hτO : τ = O.1 := funext fun t => (h t).symm
    change IsLineOrientation Λ₀.det τ
    rw [hτO]
    exact O.2
  intro t
  have hκ : ∀ s : ℝ, pt1 (t.1 0 * Real.smoothTransition s) ∈ Icc (0 : Fin 1 → ℝ) 1 := fun s =>
    pt1_mem_Icc ⟨mul_nonneg (t.2.1 0) (Real.smoothTransition.nonneg s),
      mul_le_one₀ (t.2.2 0) (Real.smoothTransition.nonneg s) (Real.smoothTransition.le_one s)⟩
  let g : C(Icc (0 : Fin 1 → ℝ) 1, Icc (0 : Fin 1 → ℝ) 1) :=
    ⟨fun q => ⟨pt1 (t.1 0 * Real.smoothTransition (q.1 0)), hκ _⟩,
      (continuous_pi fun _ => continuous_const.mul (Real.smoothTransition.continuous.comp
        ((continuous_apply 0).comp continuous_subtype_val))).subtype_mk _⟩
  have hg0 : g iccZero = iccZero := Subtype.ext (by
    change pt1 (t.1 0 * Real.smoothTransition (pt1 0 0)) = pt1 0
    rw [pt1_apply, Real.smoothTransition.zero, mul_zero])
  have hg1 : g iccOne = t := Subtype.ext (by
    change pt1 (t.1 0 * Real.smoothTransition (pt1 1 0)) = t.1
    rw [pt1_apply, Real.smoothTransition.one, mul_one, pt1_apply_zero])
  have hδs : (rnPolyfold 1).IsScSmoothMap PX
      fun s => γ (pt1 (t.1 0 * Real.smoothTransition (s 0))) :=
    isScSmoothMap_reparam (κ := fun s => t.1 0 * Real.smoothTransition s) hγs
      (contDiff_const.mul Real.smoothTransition.contDiff)
  have hcore := cont_tangentOr hf ho hδs (fun q => hγV _ (hκ _)) (fun q => hγ0 _ (hκ _))
    (fun q => hγL _ (hκ _)) (Λ₀.comp g) (fun q => rfl)
  have hO0 : O (g iccZero) = τ (g iccZero) := by
    rw [hg0]
    exact hO
  have h1 : O (g iccOne) = τ (g iccOne) :=
    (Λ₀.cont_eq O _ _).symm.trans <| (congrArg (Λ₀.cont (g iccZero) (g iccOne)) hO0).trans <|
      (Λ₀.cont_comp g _ _ _).symm.trans hcore
  rw [hg1] at h1
  exact h1

/-- **The tangent orientations of an orientation of `f` along a path of zeros with onto
linearizations**: for an orientation `o` of `f` (Definition 6.6.16), an orientable neighbourhood
`V ⊆ U` of a smooth point in the chart `c` (Definition 6.6.12), an sc-smooth path `γ` with
`γ([0, 1]) ⊆ V` through zeros of `f` with `f'(γ_q)` onto and a continuous family `Λ` with
`Λ_q = ker f'(γ_q)`, the tangent orientations by `o_{γ_q}` form an orientation of `λ(Λ)`. -/
theorem isLineOrientation_tangentOr_of_family_of_isSectionOrientation
    (hf : B.IsScFredholmSection f) {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (ho : IsSectionOrientation f hf o) {x₀ : X} (hx₀ : x₀ ∈ PX.smoothSet)
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {U V : Set X}
    (hN : IsOrientableNbhd f hf c hc U V x₀)
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ V)
    (hγ0 : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f (γ q))
    (hγL : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, B.IsLinSurjAt f (γ q))
    (Λ : SubspaceFamily (Icc (0 : Fin 1 → ℝ) 1) (c.φ.model.E 0))
    (hΛ : ∀ q : Icc (0 : Fin 1 → ℝ) 1, Λ.L q = c.linKer f
      (chartPtOf c hc (hN.hasLocalPropagation.subset (hN.subset (hγV q q.2)))
        (hf.mem_smoothSet_of_isZeroAt (hγ0 q q.2))).z) :
    IsLineOrientation (Λ.congrL _ hΛ).det
      fun q => tangentOrAt f hf c hc (hN.hasLocalPropagation.subset (hN.subset (hγV q q.2)))
        (hf.mem_smoothSet_of_isZeroAt (hγ0 q q.2)) (hγ0 q q.2) (hγL q q.2)
        (restrictOr o hN (γ q) (hγV q q.2) (hf.mem_smoothSet_of_isZeroAt (hγ0 q q.2))) :=
  isLineOrientation_tangentOr_of_family hf (ho x₀ hx₀ c hc U V hN) hγs hγV hγ0 hγL Λ hΛ

end TangentFamily

end Polyfold
