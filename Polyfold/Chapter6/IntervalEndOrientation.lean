import Polyfold.Chapter6.IntervalProductSectionOrientation
import Polyfold.Chapter6.EndChartPointOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230) and the proof of Theorem 6.7.1 (p. 278): the
orientation `e ∧ o` over `[0, 1] × X` at the ends `{0} × X` and `{1} × X`.

# The orientation `e ∧ o` on the kernels, at the ends of `[0, 1] × X`

## What is formalized

* `surjRay_extConjDetFirst_of_smul`, `pullOr_surjRay_extConjDetFirst_iff_of_smul`: for `L` onto
  and `L̂ = Γ⁻¹ (L ⊕ 0) A`, with the kernels read through inclusions
  `j' = (a · pr₂ A, j pr₁ A)`, `a ≠ 0`: in coordinates `ι̂(s, w) = (a s, ι w)` of `ker L̂` the
  orientation `e ∧ o` is the standard orientation iff `o` is in the coordinates `ι` of `ker L`.
* `ChartPoint.linZero_ivPt_cubeLift`: `g̃'(t, x) = (g'(x))^` in the product chart point of
  `[0, 1] × X`.
* `ChartPoint.pullOr_tangentOrOf_ivOrFirst₀_iff`: the tangent orientation of `e ∧ o` on
  `ker G'(t, x) = ℝ × ker g'(x)`, at every `t ∈ [0, 1]`, is "the direction of increasing `t`
  first, then the orientation of `ker g'(x)`".
* `UnitCube.ivSign_corner_of_eq_zero`, `ivSign_corner_of_eq_one`, `chart_corner_of_eq_zero`,
  `chart_corner_of_eq_one`: at the end `t = 0` the corner chart is `t ↦ t` (sign `+1`), at
  `t = 1` it is `t ↦ 1 − t` (sign `−1`), and both ends are sent to the boundary point `0` of the
  model `[0, 1)`.  So the direction of increasing `t` is the inward direction at `{0} × X` and
  the outward direction at `{1} × X`: with the outward normal first, the boundary orientation of
  the end `{1} × S_g` is that of `o` and the boundary orientation of the end `{0} × S_g` is the
  opposite one (the signs of `∂[0, 1] = {1} − {0}`).

* `pullOr_tangentOrOf_ivOrLift_iff`: the same for chart points with given level-`1` lifts.
* `tangentOr_toChartOr_ivFirst`: at a zero `(t, x)` of `F = f̃ + S` with `F'(t, x)` onto the
  tangent orientation of `SectionOrientation.ivFirst`, read in a product chart, is that of
  `e ∧ (o_x` read in the chart of `X)`.
* `theorem_6_6_18_oriented_interval`: for a proper `F = f̃ + S` in general position over
  `[0, 1] × X`, the solution set is a compact manifold with boundary and corners with a
  continuous tangent orientation given by `e ∧ o` at every zero (Theorem 6.6.18 over
  `[0, 1] × X` with the orientation of Remark 6.6.19).

## Reading

`pullOr_tangentOrOf_ivOrFirst₀_iff` is at a zero where `G` agrees with the `t`-constant lift
`g̃` to first order (`hE`), as on the product ends of the cobordism in the proof of Theorem
6.7.1.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

/-! ### The statement for operators, with a scalar -/

section OperatorsSmul

variable {E F E' F' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- **`e ∧ o` read in the kernel of `L̂` is `ê ∧ (o` read in the kernel of `L)`** (2021
Remark 6.6.19, the vector `e` first), for `L` onto, `L̂ = Γ⁻¹ (L ⊕ 0) A`, and the kernels read
in `V` and `ℝ¹ × V` through `j` and `j' = (a · pr₂ A, j pr₁ A)`, `a ≠ 0`: the vector `ê` of the
kernel family is replaced by `a ê`. -/
theorem surjRay_extConjDetFirst_of_smul (a : ℝ) (ha : a ≠ 0)
    (A : E' ≃L[ℝ] E × (Fin 1 → ℝ)) (Γ : F' ≃L[ℝ] F)
    {T : E →L[ℝ] F} (hT : T.IsFredholm) (hT' : (extConjOp A Γ T).IsFredholm)
    (hTs : Function.Surjective T) (hTs' : Function.Surjective (extConjOp A Γ T))
    (j : E →L[ℝ] V) (hj : Function.Injective j) (j' : E' →L[ℝ] (Fin 1 → ℝ) × V)
    (hj' : Function.Injective j') (hjj : ∀ v, j' v = (a • (A v).2, j (A v).1))
    {N : Submodule ℝ V} (hN : (LinearMap.ker (T : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N)
    {N' : Submodule ℝ ((Fin 1 → ℝ) × V)}
    (hN' : (LinearMap.ker ((extConjOp A Γ T : E' →L[ℝ] F') : E' →ₗ[ℝ] F')).map
      (j' : E' →ₗ[ℝ] (Fin 1 → ℝ) × V) = N')
    (Λ : SubspaceFamily PUnit.{1} (V × (Fin 0 → ℝ)))
    (hΛ : Λ.L PUnit.unit = N.map
      (ContinuousLinearMap.inl ℝ V (Fin 0 → ℝ) : V →ₗ[ℝ] V × (Fin 0 → ℝ)))
    (hΛ' : N'.map (ContinuousLinearMap.inl ℝ ((Fin 1 → ℝ) × V) (Fin 0 → ℝ) :
      (Fin 1 → ℝ) × V →ₗ[ℝ] ((Fin 1 → ℝ) × V) × (Fin 0 → ℝ)) = Λ.prodLine.L PUnit.unit)
    (r : Module.Ray ℝ (fredholmDet T)) :
    Module.Ray.map (maxPowEquiv (inlEquiv hΛ'))
        (surjRay hTs' j' hj' hN' (Module.Ray.map (extConjDetFirst A Γ hT hT') r)) =
      Module.Ray.map (Λ.prodLineWedgeEquivS a ha PUnit.unit)
        (Module.Ray.map (maxPowEquiv (inlEquiv hΛ.symm)) (surjRay hTs j hj hN r)) := by
  obtain ⟨φ, hφdef⟩ : ∃ φ : (Fin 0 → ℝ) →L[ℝ] F, φ = 0 := ⟨0, rfl⟩
  obtain ⟨φ', hφ'def⟩ : ∃ φ' : (Fin 0 → ℝ) →L[ℝ] F', φ' = 0 := ⟨0, rfl⟩
  have hφφ : ∀ μ, φ μ = Γ (φ' μ) := fun μ => by simp [hφdef, hφ'def]
  have hφ : Function.Surjective (T.coprod φ) := fun w => by
    obtain ⟨v, hv⟩ := hTs w
    exact ⟨(v, 0), by rw [ContinuousLinearMap.coprod_apply, map_zero, add_zero, hv]⟩
  have hφ' : Function.Surjective ((extConjOp A Γ T).coprod φ') := fun w => by
    obtain ⟨v, hv⟩ := hTs' w
    exact ⟨(v, 0), by rw [ContinuousLinearMap.coprod_apply, map_zero, add_zero, hv]⟩
  have hL : Λ.L PUnit.unit = (LinearMap.ker ((T.coprod φ : E × (Fin 0 → ℝ) →L[ℝ] F) :
      E × (Fin 0 → ℝ) →ₗ[ℝ] F)).map ((j.prodMap (ContinuousLinearMap.id ℝ (Fin 0 → ℝ)) :
        E × (Fin 0 → ℝ) →L[ℝ] V × (Fin 0 → ℝ)) : E × (Fin 0 → ℝ) →ₗ[ℝ] V × (Fin 0 → ℝ)) := by
    rw [hΛ, map_ker_coprod_fin_zero, hN]
  have hL' : Λ.prodLine.L PUnit.unit = (LinearMap.ker (((extConjOp A Γ T).coprod φ' :
      E' × (Fin 0 → ℝ) →L[ℝ] F') : E' × (Fin 0 → ℝ) →ₗ[ℝ] F')).map
      ((j'.prodMap (ContinuousLinearMap.id ℝ (Fin 0 → ℝ)) :
        E' × (Fin 0 → ℝ) →L[ℝ] ((Fin 1 → ℝ) × V) × (Fin 0 → ℝ)) :
          E' × (Fin 0 → ℝ) →ₗ[ℝ] ((Fin 1 → ℝ) × V) × (Fin 0 → ℝ)) := by
    rw [← hΛ', map_ker_coprod_fin_zero, hN']
  have h1 := stabRayEquiv_extConjDetFirst A Γ hφφ hT hT' hφ hφ' (kerEquivMap j hj hL)
    (kerEquivMap j' hj' hL') (Λ.prodLineWedgeEquivS a ha PUnit.unit)
    (prodLineWedgeEquivS_compat a ha A Γ hT hφφ j hj j' hj' hjj Λ PUnit.unit hL hL') r
  have h2 := stabRayEquiv_eq_surjRay hT hTs hφ j hj hL hN (inlEquiv hΛ.symm)
    (coe_inlEquiv hΛ.symm) r
  have h3 := stabRayEquiv_eq_surjRay hT' hTs' hφ' j' hj' hL' hN' (inlEquiv hΛ')
    (coe_inlEquiv hΛ') (Module.Ray.map (extConjDetFirst A Γ hT hT') r)
  have h2' := (congrArg (stabRayEquiv hT hφ (kerEquivMap j hj hL))
    (stabSign_smul_of_surjective hTs _)).symm.trans h2
  have h3' := (congrArg (stabRayEquiv hT' hφ' (kerEquivMap j' hj' hL'))
    (stabSign_smul_of_surjective hTs' _)).symm.trans h3
  exact h3'.symm.trans (h1.trans (congrArg (Module.Ray.map
      (Λ.prodLineWedgeEquivS a ha PUnit.unit)) h2'))

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- **The product orientation in coordinates of the kernels**: for `L` onto,
`L̂ = Γ⁻¹ (L ⊕ 0) A`, and coordinates `ι : ℝ^k ≅ ker L`, `ι̂ : ℝ^{k+1} ≅ ker L̂` with
`ι̂(s, w) = (a s, ι w)` (the kernels read through `j' = (a · pr₂ A, j pr₁ A)`, `a ≠ 0`), the
orientation `e ∧ o` of `det L̂` reads in `ι̂` as the standard
orientation of `ℝ^{k+1}` iff `o` reads in `ι` as the standard orientation of `ℝ^k`. -/
theorem pullOr_surjRay_extConjDetFirst_iff_of_smul (a : ℝ) (ha : a ≠ 0)
    (A : E' ≃L[ℝ] E × (Fin 1 → ℝ)) (Γ : F' ≃L[ℝ] F)
    {T : E →L[ℝ] F} (hT : T.IsFredholm) (hT' : (extConjOp A Γ T).IsFredholm)
    (hTs : Function.Surjective T) (hTs' : Function.Surjective (extConjOp A Γ T))
    (j : E →L[ℝ] V) (hj : Function.Injective j) (j' : E' →L[ℝ] (Fin 1 → ℝ) × V)
    (hj' : Function.Injective j') (hjj : ∀ v, j' v = (a • (A v).2, j (A v).1))
    {N : Submodule ℝ V} (hN : (LinearMap.ker (T : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N)
    {N' : Submodule ℝ ((Fin 1 → ℝ) × V)}
    (hN' : (LinearMap.ker ((extConjOp A Γ T : E' →L[ℝ] F') : E' →ₗ[ℝ] F')).map
      (j' : E' →ₗ[ℝ] (Fin 1 → ℝ) × V) = N')
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] N)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N')
    (hι : ∀ s w, ((ι' (consE s w) : N') : (Fin 1 → ℝ) × V) = ((fun _ => a * s), (ι w : V)))
    (r : Module.Ray ℝ (fredholmDet T)) :
    pullOr finrank_euclideanSpace_fin ι'
        (surjRay hTs' j' hj' hN' (Module.Ray.map (extConjDetFirst A Γ hT hT') r)) =
        stdOrientation (k + 1) ↔
      pullOr finrank_euclideanSpace_fin ι (surjRay hTs j hj hN r) = stdOrientation k := by
  have := ι.finiteDimensional
  have := ι'.finiteDimensional
  set L₀ := N.map (ContinuousLinearMap.inl ℝ V (Fin 0 → ℝ) : V →ₗ[ℝ] V × (Fin 0 → ℝ))
    with hL₀
  have : FiniteDimensional ℝ L₀ := (inlEquiv (N := N) (L := L₀) rfl).finiteDimensional
  set Λ := SubspaceFamily.constUnit L₀ with hΛdef
  have hΛ : Λ.L PUnit.unit = L₀ := rfl
  have hLeq : Λ.L PUnit.unit = (LinearMap.ker ((T.coprod (0 : (Fin 0 → ℝ) →L[ℝ] F) :
      E × (Fin 0 → ℝ) →L[ℝ] F) : E × (Fin 0 → ℝ) →ₗ[ℝ] F)).map
      ((j.prodMap (ContinuousLinearMap.id ℝ (Fin 0 → ℝ)) :
        E × (Fin 0 → ℝ) →L[ℝ] V × (Fin 0 → ℝ)) : E × (Fin 0 → ℝ) →ₗ[ℝ] V × (Fin 0 → ℝ)) := by
    rw [hΛ, hL₀, map_ker_coprod_fin_zero, hN]
  have hΛ' : N'.map (ContinuousLinearMap.inl ℝ ((Fin 1 → ℝ) × V) (Fin 0 → ℝ) :
      (Fin 1 → ℝ) × V →ₗ[ℝ] ((Fin 1 → ℝ) × V) × (Fin 0 → ℝ)) = Λ.prodLine.L PUnit.unit := by
    rw [← hN', ← map_ker_coprod_fin_zero (extConjOp A Γ T) (0 : (Fin 0 → ℝ) →L[ℝ] F') j',
      ← map_ker_extConjOp_eq_of_smul a ha A Γ T (0 : (Fin 0 → ℝ) →L[ℝ] F) (0 : (Fin 0 → ℝ) →L[ℝ] F')
        (fun μ => by simp) j j' hjj, ← hLeq]
    rfl
  have key := surjRay_extConjDetFirst_of_smul a ha A Γ hT hT' hTs hTs' j hj j' hj' hjj hN hN' Λ hΛ
      hΛ' r
  have hdim : 1 + finrank ℝ (Λ.L PUnit.unit) = finrank ℝ (Λ.prodLine.L PUnit.unit) := by
    rw [Λ.finrank_eq, Λ.prodLine.finrank_eq]; rfl
  have hι2 : ∀ s w, (ι'.trans (inlEquiv hΛ')) (consE s w) =
      s • (a • Λ.prodLineEr PUnit.unit) + Λ.prodLineJr PUnit.unit ((ι.trans
          (inlEquiv hΛ.symm)) w) := by
    intro s w
    apply Subtype.ext
    change (((ι' (consE s w) : N') : (Fin 1 → ℝ) × V), (0 : Fin 0 → ℝ)) =
      s • (a • prodLineE V 0) + prodLineJ V 0 ((ι w : V), 0)
    rw [hι]
    refine Prod.ext (Prod.ext (funext fun i => ?_) ?_) (Subsingleton.elim _ _)
    · simp [prodLineE, mul_comm]
    · simp [prodLineE]
  rw [← pullOr_trans finrank_euclideanSpace_fin ι' (inlEquiv hΛ'), key,
    ← pullOr_trans finrank_euclideanSpace_fin ι (inlEquiv hΛ.symm) (surjRay hTs j hj hN r)]
  exact pullOr_wedgeExtLeft_eq_std_iff (ι.trans (inlEquiv hΛ.symm)) (ι'.trans (inlEquiv hΛ'))
    (Λ.prodLineJr PUnit.unit) (a • Λ.prodLineEr PUnit.unit) hdim hι2
    (Λ.prodLineWedgeEquivS a ha PUnit.unit) (fun w => (LinearMap.congr_fun
      (wedgeExtLeft_smul_single (Λ.prodLineJr PUnit.unit) a (Λ.prodLineEr PUnit.unit) hdim)
      w).symm) _

end OperatorsSmul

/-! ### The corner charts at the ends -/

namespace UnitCube

/-- At the end `t = 0` the corner chart is `t ↦ t`: its sign is `+1`. -/
lemma ivSign_corner_of_eq_zero {t : Fin 1 → unitInterval} (h : (t 0 : ℝ) = 0) :
    ivSign (corner t) = 1 := by
  have h1 : corner t 0 = true := by
    change decide ((t 0 : ℝ) < 1) = true
    rw [h]; simp
  unfold ivSign; rw [h1]; simp

/-- At the end `t = 1` the corner chart is `t ↦ 1 − t`: its sign is `−1`. -/
lemma ivSign_corner_of_eq_one {t : Fin 1 → unitInterval} (h : (t 0 : ℝ) = 1) :
    ivSign (corner t) = -1 := by
  have h1 : corner t 0 = false := by
    change decide ((t 0 : ℝ) < 1) = false
    rw [h]; simp
  unfold ivSign; rw [h1]; simp

/-- The end `t = 0` is sent to the boundary point `0` of the model `[0, 1)`. -/
lemma chart_corner_of_eq_zero {t : Fin 1 → unitInterval} (h : (t 0 : ℝ) = 0) :
    (chart (corner t) t : Fin 1 → ℝ) 0 = 0 := by
  have h1 : corner t 0 = true := by
    change decide ((t 0 : ℝ) < 1) = true
    rw [h]; simp
  rw [chart_apply]
  simp [fl, h1, h]

/-- The end `t = 1` is sent to the boundary point `0` of the model `[0, 1)`. -/
lemma chart_corner_of_eq_one {t : Fin 1 → unitInterval} (h : (t 0 : ℝ) = 1) :
    (chart (corner t) t : Fin 1 → ℝ) 0 = 0 := by
  have h1 : corner t 0 = false := by
    change decide ((t 0 : ℝ) < 1) = false
    rw [h]; simp
  rw [chart_apply]
  simp [fl, h1, h]

end UnitCube

/-! ### The statement in a chart point and its product chart point -/

section IvEnds

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (b : Fin 1 → Bool) {t : Fin 1 → unitInterval}
  (ht : t ∈ (chart b).source)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

/-- **`g̃'(t, x) = (g'(x))^`** in the product chart point of `[0, 1] × X`. -/
theorem linZero_ivPt_cubeLift {g : X → Y}
    (hg : B.IsScFredholmSection g)
    (hgc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) g hg.isScSmooth.1))
    (hx0 : IsZeroAt P g x)
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (cubeLift (n := 1) g hg.isScSmooth.1) (t, x)) :
    (p.ivPt b ht q₀).linZero hgc hz0 = p.ivLin b ht q₀ (p.linZero hg hx0) := by
  refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
  rw [coe_linZero]
  exact (p.linAt_ivPt_cubeLift b ht q₀ hg.isScSmooth v).trans
    ((p.coe_linZero hg hx0 _).symm.trans (p.coe_ivLin_apply b ht q₀ (p.linZero hg hx0) v).symm)

/-- **The tangent orientation of `e ∧ o` at a point of `[0, 1] × X`, the ends included** (2021
Remark 6.6.19, p. 276, and the proof of Theorem 6.7.1, p. 278): let `g` have a zero at `x` with
`g'(x)` onto and in `Lin(f, x)`, and let `G` over `[0, 1] × X` have a zero at `(t, x)` with
`G'(t, x) = (g'(x))^` in `Lin(f̃, (t, x))`.  In coordinates `ι̂(s, w) = (± s, ι w)` of
`ker G'(t, x) = ℝ × ker g'(x)` in the chart `χ_b × φ`, the sign that of `χ_b` (so that `s` is
the direction of increasing `t`), the orientation of `ker G'(t, x)` given by `e ∧ o` is the
standard orientation of `ℝ^{k+1}` iff the orientation of `ker g'(x)` given by `o` is the standard
orientation of `ℝ^k`.  At `t = 1` (chart `t ↦ 1 − t`, model `[0, 1)`) the vector `ι̂(1, 0)` has
the chart coordinate `−1` and points out of `[0, 1] × X`; at `t = 0` (chart `t ↦ t`) it has the
chart coordinate `+1` and points into `[0, 1] × X`. -/
theorem pullOr_tangentOrOf_ivOrFirst₀_iff (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet) (hne : (p.linSet f).Nonempty) (o : p.Or f hf) {g : X → Y}
    (hg : B.IsScFredholmSection g) (hx0 : IsZeroAt P g x) (hgL : B.IsLinSurjAt g x)
    (hmem : p.linZero hg hx0 ∈ p.linSet f)
    {G : (Fin 1 → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hG : (ivBundle B).IsScFredholmSection G)
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x))
    (hGL : (ivBundle B).IsLinSurjAt G (t, x))
    (hmem' : (p.ivPt b ht q₀).linZero hG hz0 ∈
      (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    (hE : (p.ivPt b ht q₀).linZero hG hz0 = p.ivLin b ht q₀ (p.linZero hg hx0))
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] p.c.linKer g p.z)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ]
      (p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z)
    (hι : ∀ s w, ((ι' (consE s w)).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
      ((fun _ => ivSign b * s), (ι w : p.c.φ.model.E 0))) :
    pullOr finrank_euclideanSpace_fin ι'
        ((p.ivPt b ht q₀).tangentOrOf hfc hG hz0 hGL hmem'
          (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o)) = stdOrientation (k + 1) ↔
      pullOr finrank_euclideanSpace_fin ι (p.tangentOrOf hf hg hx0 hgL hmem o) =
        stdOrientation k := by
  have aux : ∀ (T₁ : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K)
      (_ : T₁ = p.ivLin b ht q₀ (p.linZero hg hx0))
      (hT₁m : T₁ ∈ (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
      (hT₁s : Function.Surjective T₁) (N' : Submodule ℝ ((Fin 1 → ℝ) × p.c.φ.model.E 0))
      (hN' : (LinearMap.ker ((T₁ : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K) :
        ↥(p.ivPt b ht q₀).T →ₗ[ℝ] ↥(p.ivPt b ht q₀).K)).map
          (p.ivIncl b ht q₀ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] (Fin 1 → ℝ) × p.c.φ.model.E 0) = N')
      (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N')
      (_ : ∀ s w, ((ι' (consE s w) : N') : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
        ((fun _ => ivSign b * s), (ι w : p.c.φ.model.E 0))),
      (pullOr finrank_euclideanSpace_fin ι'
          (surjRay hT₁s (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN'
            ((p.ivPt b ht q₀).orEquivRay hfc hT₁m (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o))) =
          stdOrientation (k + 1) ↔
        pullOr finrank_euclideanSpace_fin ι
          (surjRay (p.linZero_surjective hg hx0 hgL) p.T.subtypeL Subtype.val_injective
            (p.map_ker_linZero hg hx0) (p.orEquivRay hf hmem o)) = stdOrientation k) := by
    intro T₁ hT₁e
    subst hT₁e
    intro hT₁m hT₁s N' hN' ι' hι'
    have hFr := p.isFredholm_of_mem_linSet hf _ hmem
    have hFr' := (p.ivPt b ht q₀).isFredholm_of_mem_linSet hfc _ hT₁m
    have hval : (p.ivPt b ht q₀).orEquivRay hfc hT₁m (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o) =
        Module.Ray.map (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀) hFr hFr')
          (p.orEquivRay hf hmem o) :=
      p.ivOrFirst₀_apply b ht q₀ hf hfc hxs hne o _ hmem
    refine (iff_of_eq (congrArg (fun r => pullOr finrank_euclideanSpace_fin ι'
      (surjRay hT₁s (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN' r) =
        stdOrientation (k + 1)) hval)).trans ?_
    exact pullOr_surjRay_extConjDetFirst_iff_of_smul (ivSign b) (ivSign_ne_zero b) (p.ivT b ht q₀)
        (p.ivK b ht q₀) hFr hFr'
      (p.linZero_surjective hg hx0 hgL) hT₁s p.T.subtypeL Subtype.val_injective
      (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) (fun v => Prod.ext (by
        have h : ivSign b • ivSign b • Prod.fst (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) v.1 =
            Prod.fst (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) v.1 := by
          rw [smul_smul, ivSign_mul_self, one_smul]
        exact h.symm) rfl) (p.map_ker_linZero hg hx0)
      hN' ι ι' hι' (p.orEquivRay hf hmem o)
  exact aux _ hE hmem' ((p.ivPt b ht q₀).linZero_surjective hG hz0 hGL) _
    ((p.ivPt b ht q₀).map_ker_linZero hG hz0) ι' hι

end ChartPoint

/-- **The tangent orientation of `e ∧ o`, for chart points with given lifts**
(`ChartPoint.pullOr_tangentOrOf_ivOrFirst₀_iff` for `ivOrLift`): `G` agrees with `g̃` to first
order at `(t, x)` (`hE`). -/
theorem pullOr_tangentOrOf_ivOrLift_iff (b : Fin 1 → Bool) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ x) {t : Fin 1 → unitInterval}
    (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hxc : ((t, x) : (Fin 1 → unitInterval) × X) ∈ (ivChart b c q₀).φ.source)
    (z' : (ivChart b c q₀).φ.model.E 1)
    (hz' : (ivChart b c q₀).φ.model.E.toBase 1 z' = (ivChart b c q₀).φ (t, x))
    (hzz : z' = ((chart b t : Fin 1 → ℝ), z)) (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet)
    (hne : ((chartPt c hc hx z hz).linSet f).Nonempty) (o : (chartPt c hc hx z hz).Or f hf)
    {g : X → Y} (hg : B.IsScFredholmSection g)
    (hgc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) g hg.isScSmooth.1))
    (hx0 : IsZeroAt P g x) (hgL : B.IsLinSurjAt g x)
    (hmem : (chartPt c hc hx z hz).linZero hg hx0 ∈ (chartPt c hc hx z hz).linSet f)
    {G : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hG : (ivBundle B).IsScFredholmSection G)
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x))
    (hGL : (ivBundle B).IsLinSurjAt G (t, x))
    (hmem' : (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
        hz').linZero hG hz0 ∈
      (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
        hz').linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    (hz0g : IsZeroAt (pullbackProj P Prod.snd) (cubeLift (n := 1) g hg.isScSmooth.1) (t, x))
    (hE : (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
        hz').linZero hG hz0 =
      (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
        hz').linZero hgc hz0g)
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] c.linKer g z)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] (ivChart b c q₀).linKer G z')
    (hι : ∀ s w, ((ι' (consE s w)).1 : (Fin 1 → ℝ) × c.φ.model.E 0) =
      ((fun _ => ivSign b * s), (ι w : c.φ.model.E 0))) :
    pullOr finrank_euclideanSpace_fin ι'
        ((chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
          hz').tangentOrOf hfc hG hz0 hGL hmem'
          (ivOrLift b hc hx z hz ht q₀ hxc z' hz' hzz hf hfc hxs hne o)) =
        stdOrientation (k + 1) ↔
      pullOr finrank_euclideanSpace_fin ι
        ((chartPt c hc hx z hz).tangentOrOf hf hg hx0 hgL hmem o) = stdOrientation k := by
  subst hzz
  exact (chartPt c hc hx z hz).pullOr_tangentOrOf_ivOrFirst₀_iff b ht q₀ hf hfc hxs hne o hg
    hx0 hgL hmem hG hz0 hGL hmem'
    (hE.trans ((chartPt c hc hx z hz).linZero_ivPt_cubeLift b ht q₀ hg hgc hx0 hz0g)) ι ι' hι


end IvEnds

/-! ### The oriented cobordism over `[0, 1] × X` -/

section IvCobordism

open MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

/-- **The tangent orientation of `SectionOrientation.ivFirst` in a product chart** (2021 Remark
6.6.19): at a zero `(t, x)` of `F = f̃ + S` over `[0, 1] × X` with `F'(t, x)` onto, `t = 0` and
`t = 1` included, the tangent orientation of the orientation `e ∧ o` of `F`, read in the product
chart `χ_b × φ_c`, is the orientation of `ker F'(t, x)` given by `e ∧ (o_x` read in `c)`
(`SectionOrientation.toChartOr_ivFirst₀`, `toChartOr_orSectionAdd`). -/
theorem tangentOr_toChartOr_ivFirst (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) {t : Fin 1 → unitInterval} {x : X}
    (hxs : x ∈ PX.smoothSet) (b : Fin 1 → Bool) (hb : t ∈ (chart b).source)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hxc : x ∈ c.φ.source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x))
    (hL : (ivBundle B).IsLinSurjAt (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x)) :
    (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
        (mem_ivChart_source q₀ hxc hb) (prod_cube_mem_smoothSet_iff.2 hxs)).tangentOr
        (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection hS) hz0 hL
        (toChartOr (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection hS)
          (prod_cube_mem_smoothSet_iff.2 hxs) (ivChart b c q₀) (isChart_ivChart b hc q₀)
          (mem_ivChart_source q₀ hxc hb)
          ((SectionOrientation.ivFirst hX hbump hf o hS).1 (t, x)
            (prod_cube_mem_smoothSet_iff.2 hxs))) =
      (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
        (mem_ivChart_source q₀ hxc hb) (prod_cube_mem_smoothSet_iff.2 hxs)).pertTangentOr
        (hf.paramCube (n := 1)).toIsScFredholmSection hS hz0 hL
        (ivOrOf b hc hxc hxs hb q₀ hf.toIsScFredholmSection
          (hf.paramCube (n := 1)).toIsScFredholmSection
          (ChartPoint.linSet_nonempty _ hf.toIsScFredholmSection hxs
            (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump))
          (toChartOr hf.toIsScFredholmSection hxs c hc hxc (o.1 x hxs))) := by
  have hzs : ((t, x) : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    prod_cube_mem_smoothSet_iff.2 hxs
  have e1 := toChartOr_orSectionAdd (hf.paramCube (n := 1)).toIsScFredholmSection hS hzs
    ((SectionOrientation.ivFirst₀ hX hbump hf o).1 (t, x) hzs) (ivChart b c q₀)
    (isChart_ivChart b hc q₀) (mem_ivChart_source q₀ hxc hb)
  have e2 := SectionOrientation.toChartOr_ivFirst₀ hX hbump hf o (t, x) hzs b hb hc hxc q₀
  exact (congrArg _ (e1.trans (congrArg _ e2))).trans
    (ChartPoint.tangentOr_orSectionAdd _ (hf.paramCube (n := 1)).toIsScFredholmSection hS hz0
      hL _)

/-- **The oriented cobordism over `[0, 1] × X`** (2021 Remark 6.6.19 and Theorem 6.6.18,
pp. 275–276): for an orientation `o` of a tame sc-Fredholm section `f` over a tame `X` with
sc-smooth bump functions and an sc⁺-section `S` of the pull-back of `P` to the M-polyfold with
boundary `[0, 1] × X`, let `F = f̃ + S` be proper, in general position at every zero (the zeros
on `{0, 1} × X` included) and of index `d`.  Then `S_F = F⁻¹(0) ⊆ [0, 1] × X` is compact and a
smooth manifold with boundary and corners, with a continuous tangent orientation which at every
zero `z` is the orientation `e ∧ o` (`SectionOrientation.ivFirst`) on `T_zS_F = ker F'(z)`:
`theorem_6_6_18_oriented` for `F` over `[0, 1] × X` and the orientation of Remark 6.6.19. -/
theorem theorem_6_6_18_oriented_interval (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hP : (ivBundle B).IsProper
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    {d : ℕ}
    (hidx : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsLinOfIndex
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z d) :
    IsCompact (solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) ∧
      letI := ((cubePolyfold 1).prod PX).paracompactSpace_subtype
        (solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
      letI := (MPolyfold.subPolyfold ((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
        (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isSubmanifoldOfDim
        (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hidx).1.isSubMPolyfold).cornerChartedSpace
        (((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
          (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isSubmanifoldOfDim
          (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hidx).hasCornerStructureOfDim_of_tame
          (prod_cube_isTame hX) ((theorem_6_6_18_solutionSet (prod_cube_isTame hX)
            (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp).isGoodPositionAt
            (prod_cube_isTame hX)))
      IsManifold (𝓠 d) ∞ (solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) ∧
      ∃ oS : TangentOrientation (𝓠 d) (solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) d,
        oS.IsContinuous (𝓠 d) ∞ ∧
        ∀ (z : solutionSet (pullbackProj P Prod.snd)
            (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
          (c : StrongBundleChart ((cubePolyfold 1).prod PX) (pullbackProj P Prod.snd))
          (hc : (ivBundle B).IsChart c) (hzc : z.1 ∈ c.φ.source),
          ∃ ι : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] c.linKer
              (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)
              (chartPtOf c hc hzc ((theorem_3_1_18_tame (hf.paramCube (n := 1))
                hS).toIsScFredholmSection.mem_smoothSet_of_isZeroAt z.2)).z,
            (∀ v, (ι v : c.φ.model.E 0) = derivIn (𝓠 d) (chartAt (EuclideanQuadrant d) z)
              (fun y : solutionSet (pullbackProj P Prod.snd)
                (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) =>
                c.φ y.1) z v) ∧
            ∀ b : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
              b.orientation = tangentOrToModel (oS z) ↔
                (chartPtOf c hc hzc ((theorem_3_1_18_tame (hf.paramCube (n := 1))
                    hS).toIsScFredholmSection.mem_smoothSet_of_isZeroAt z.2)).tangentOr
                  (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS).toIsScFredholmSection z.2
                  (hgp z.1 z.2).isLinSurjAt
                  (toChartOr (theorem_3_1_18_tame (hf.paramCube (n := 1))
                      hS).toIsScFredholmSection
                    ((theorem_3_1_18_tame (hf.paramCube (n := 1))
                      hS).toIsScFredholmSection.mem_smoothSet_of_isZeroAt z.2) c hc hzc
                    ((SectionOrientation.ivFirst hX hbump hf o hS).1 z.1
                      ((theorem_3_1_18_tame (hf.paramCube (n := 1))
                        hS).toIsScFredholmSection.mem_smoothSet_of_isZeroAt z.2))) =
                  rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι b) :=
  theorem_6_6_18_oriented (prod_cube_isTame hX) (admitsBumpFunctions_prod_cube hbump)
    (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp hidx
    (SectionOrientation.ivFirst hX hbump hf o hS)

end IvCobordism

end Polyfold
