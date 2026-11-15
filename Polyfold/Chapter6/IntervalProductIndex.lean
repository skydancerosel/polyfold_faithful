import Polyfold.Chapter6.IntervalProductKernels

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276 (**Remark
6.6.19**; preprint Remark 6.42) and Definition 6.2.1 (preprint 6.1): the Fredholm index of
`f̃(t, x) = f(x)` over `[0, 1] × X`.

# The index of `f̃` is the index of `f` plus one

## What is formalized

* `ChartPoint.fredholmIndex_ivLin`: for a Fredholm operator `L : T_xX → Y_x`, the operator
  `L̂(σ, v) = Lv` on `T_{(t, x)}([0, 1] × X) = ℝ × T_xX` has index `ind L + 1`.
* **`isIndexAt_cubeLift_interval`**: if `f` has index `i` at the smooth point `x`, then `f̃` has
  index `i + 1` at `(t, x)`, for every `t ∈ [0, 1]`.
-/

open Set Module

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

section IvIndex

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (b : Fin 1 → Bool) {t : Fin 1 → unitInterval}
  (ht : t ∈ (chart b).source)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

/-- **`ind L̂ = ind L + 1`** for `L̂(σ, v) = Lv`: the kernel gains the `ℝ`-direction and the
cokernel does not change. -/
theorem fredholmIndex_ivLin {L : ↥p.T →L[ℝ] ↥p.K} (hL : L.IsFredholm) :
    fredholmIndex (p.ivLin b ht q₀ L) = fredholmIndex L + 1 := by
  have hext : linIndex ((extOp L : ↥p.T × (Fin 1 → ℝ) →L[ℝ] ↥p.K) :
      ↥p.T × (Fin 1 → ℝ) →ₗ[ℝ] ↥p.K) = linIndex (L : ↥p.T →ₗ[ℝ] ↥p.K) + 1 := by
    unfold linIndex
    have h1 := finrank_ker_extOp hL
    have h2 := (extCoker L).finrank_eq
    rw [← h1, h2]
    push_cast
    ring
  have hA := HasFiniteIndex.equiv (p.ivT b ht q₀).toLinearEquiv
  have hΓ := HasFiniteIndex.equiv (p.ivK b ht q₀).symm.toLinearEquiv
  have hE := IsFredholm.hasFiniteIndex (isFredholm_extOp hL)
  have hcoe : ((p.ivLin b ht q₀ L : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K) :
      ↥(p.ivPt b ht q₀).T →ₗ[ℝ] ↥(p.ivPt b ht q₀).K) =
      ((p.ivK b ht q₀).symm.toLinearEquiv : ↥p.K →ₗ[ℝ] ↥(p.ivPt b ht q₀).K) ∘ₗ
        (((extOp L : ↥p.T × (Fin 1 → ℝ) →L[ℝ] ↥p.K) : ↥p.T × (Fin 1 → ℝ) →ₗ[ℝ] ↥p.K) ∘ₗ
          ((p.ivT b ht q₀).toLinearEquiv : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] ↥p.T × (Fin 1 → ℝ))) := rfl
  unfold fredholmIndex
  rw [hcoe, linIndex_comp (hA.comp hE) hΓ, linIndex_comp hA hE, linIndex_equiv, linIndex_equiv,
    hext]
  ring

end ChartPoint

/-- **The index of `f̃(t, x) = f(x)` over `[0, 1] × X`** (Definition 6.2.1 and Remark 6.6.19): if
`f` has index `i` at the smooth point `x`, then `f̃` has index `i + 1` at `(t, x)` for every
`t ∈ [0, 1]`: for `L ∈ Lin(f, x)` the operator `L̂(σ, v) = Lv` belongs to `Lin(f̃, (t, x))`. -/
theorem isIndexAt_cubeLift_interval (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1)) {x : X}
    (hxs : x ∈ PX.smoothSet) (hsec : B.HasScPlusSectionsThrough) {i : ℤ}
    (hi : B.IsIndexAt f x i) (t : Fin 1 → unitInterval) :
    (ivBundle B).IsIndexAt (cubeLift (n := 1) f hf.isScSmooth.1) (t, x) (i + 1) := by
  obtain ⟨p⟩ : Nonempty (ChartPoint B x) :=
    ⟨chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hxs⟩
  obtain ⟨L, hL⟩ := p.linSet_nonempty hf hxs hsec
  obtain ⟨hF, hLi⟩ := p.fredholmIndex_of_mem_linSet hf hi hL
  have hL' := p.ivLin_mem_linSet_cubeLift (corner t) (mem_chart_corner t)
    (cubeLift (n := 1) f hf.isScSmooth.1 (t, x)) hf hxs hL
  have h := ((p.ivPt (corner t) (mem_chart_corner t)
    (cubeLift (n := 1) f hf.isScSmooth.1 (t, x))).isFredholm_isIndexAt_of_mem_linSet hfc hL').2
  rw [p.fredholmIndex_ivLin (corner t) (mem_chart_corner t) _ hF, hLi] at h
  exact h

end IvIndex

end Polyfold
