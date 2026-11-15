import Polyfold.Chapter6.IntervalEndOrientation
import Polyfold.Chapter6.InvariantSingle2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6–6.7, pp. 275–278:
Theorem 5.3.10 (p. 220) on the tame M-polyfold `[0, 1] × X`, as used for the cobordism in
Remark 6.6.19 and in the proof of Theorem 6.7.1.

# Cobordisms over `[0, 1] × X` in general position exist

For a tame sc-Fredholm section `f` with compact solution set over a tame `X` with sc-smooth bump
functions, there is an sc⁺-section `S` of the pull-back of `P` to `[0, 1] × X` such that
`F = f̃ + S` is proper and in general position at every zero, the zeros on `\{0, 1\} × X`
included: Theorem 5.3.10 for `f̃` on `[0, 1] × X` (`exists_isAdmissible_nbhd`) and Theorem 5.2.2.

* `solutionSet_cubeLift`: `S_{f̃} = [0, 1]ⁿ × S_f`; `isCompact_solutionSet_cubeLift`.
* `exists_interval_cobordism`: the existence statement, for every auxiliary norm `N` on the
  pull-back bundle, with `N(S) ≤ 1` and the support of `S` in a given neighbourhood of
  `[0, 1] × S_f` if wanted.
* `exists_oriented_interval_cobordism`: the hypotheses of `theorem_6_6_18_oriented_interval`
  other than the index are satisfied by some `S`, for every proper tame `f`.
* `fredholmIndex_extOp`, `fredholmIndex_extConjOp`, `isLinOfIndex_interval_of_isIndexAt`: the
  index of `F = f̃ + S` at a zero `(t, x)` is the index of `(f, x)` plus one.
* `exists_oriented_interval_cobordism_of_index`: all hypotheses of
  `theorem_6_6_18_oriented_interval` are satisfied by some `S`, for every tame `f` with compact
  solution set and constant index.
-/

open Set Filter Topology

noncomputable section

namespace Polyfold

open StrongBundle UnitCube MPolyfold

universe u v

section Index

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']

omit [CompleteSpace E] [CompleteSpace F] in
/-- `ind (L ⊕ 0) = ind L + 1` on `E × ℝ¹`. -/
theorem fredholmIndex_extOp {T : E →L[ℝ] F} (hT : T.IsFredholm) :
    fredholmIndex (extOp T) = fredholmIndex T + 1 := by
  unfold fredholmIndex linIndex
  rw [range_extOp, ← finrank_ker_extOp hT]
  push_cast
  ring

/-- `ind (Γ⁻¹ (L ⊕ 0) A) = ind L + 1`. -/
theorem fredholmIndex_extConjOp (A : E' ≃L[ℝ] E × (Fin 1 → ℝ)) (Γ : F' ≃L[ℝ] F)
    {T : E →L[ℝ] F} (hT : T.IsFredholm) :
    fredholmIndex (extConjOp A Γ T) = fredholmIndex T + 1 := by
  have h1 := HasFiniteIndex.equiv A.toLinearEquiv
  have h2 := Polyfold.IsFredholm.hasFiniteIndex (isFredholm_extOp hT)
  have h3 := HasFiniteIndex.equiv Γ.symm.toLinearEquiv
  have e : ((extConjOp A Γ T : E' →L[ℝ] F') : E' →ₗ[ℝ] F') =
      (Γ.symm.toLinearEquiv : F →ₗ[ℝ] F') ∘ₗ
        ((extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F) ∘ₗ
          (A.toLinearEquiv : E' →ₗ[ℝ] E × (Fin 1 → ℝ))) := rfl
  unfold fredholmIndex
  rw [e, linIndex_comp (h1.comp h2) h3, linIndex_comp h1 h2, linIndex_equiv, linIndex_equiv,
    zero_add, add_zero]
  exact fredholmIndex_extOp hT

end Index

section Existence

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- **`S_{f̃} = [0, 1]ⁿ × S_f`** for the `t`-constant lift `f̃` of `f`. -/
theorem solutionSet_cubeLift {n : ℕ} (hf : IsSection P f) :
    solutionSet (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
      (cubeLift (n := n) f hf) = univ ×ˢ solutionSet P f := by
  ext ⟨t, x⟩
  have hsec : IsSection (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
      (cubeLift (n := n) f hf) := isSection_pullbackLift _
  have h := isZeroAt_iff_prodSlice hsec t x
  exact h.trans ⟨fun hx => ⟨mem_univ _, hx⟩, fun hx => hx.2⟩

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The solution set of `f̃` over `[0, 1]ⁿ × X` is compact when `S_f` is. -/
theorem isCompact_solutionSet_cubeLift {n : ℕ} (hf : IsSection P f)
    (hS : IsCompact (solutionSet P f)) :
    IsCompact (solutionSet (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
      (cubeLift (n := n) f hf)) := by
  rw [solutionSet_cubeLift hf]
  exact isCompact_univ.prod hS

variable [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]

/-- **Cobordisms in general position over `[0, 1] × X` exist** (2021 Theorem 5.3.10, p. 220, for
`f̃` over the tame M-polyfold `[0, 1] × X`; Remark 6.6.19 and the proof of Theorem 6.7.1): for a
tame sc-Fredholm section `f` with compact solution set over a tame `X` with sc-smooth bump
functions and an auxiliary norm `N` of the pull-back of `P` to `[0, 1] × X`, there are an open
`U ⊇ [0, 1] × S_f` and an sc⁺-section `S` over `[0, 1] × X` with support in `U` and `N(S) ≤ 1`
such that `F = f̃ + S` is proper and in general position at every zero, the zeros on
`\{0, 1\} × X` included. -/
theorem exists_interval_cobordism (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f))
    {N : (ivBundle B).One → ℝ} (hN : (ivBundle B).IsAuxNorm N) :
    ∃ (U : Set ((Fin 1 → unitInterval) × X))
      (S : (Fin 1 → unitInterval) × X →
        pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)),
      IsOpen U ∧ (univ : Set (Fin 1 → unitInterval)) ×ˢ solutionSet P f ⊆ U ∧
      S ∈ (ivBundle B).allowableSections N U ∧ (ivBundle B).IsScPlusSection S ∧
      (ivBundle B).IsProper
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) ∧
      ∀ z, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
        (ivBundle B).IsGeneralPositionGerm
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z := by
  have hfc := hf.paramCube (n := 1)
  have hcpt := isCompact_solutionSet_cubeLift (n := 1) hf.isScSmooth.1 hS
  obtain ⟨U, hUo, hSU, -, hc, S, hSadm⟩ := exists_isAdmissible_nbhd (prod_cube_isTame hX)
    (admitsBumpFunctions_prod_cube hbump) hfc hcpt hN
  refine ⟨U, S, hUo, ?_, hSadm.mem, hSadm.isScPlusSection, ?_, hSadm.gp⟩
  · rw [← solutionSet_cubeLift hf.isScSmooth.1]
    exact hSU
  · exact theorem_5_2_2_preprint
      (theorem_3_1_18_preprint hfc.toIsScFredholmSection hSadm.isScPlusSection) (hc S hSadm.mem)

/-- **The hypotheses of `theorem_6_6_18_oriented_interval` on `S`, other than the index, are
satisfiable** for every tame sc-Fredholm section `f` with compact solution set over a tame `X`
with sc-smooth bump functions: there is an sc⁺-section `S` over `[0, 1] × X` with `F = f̃ + S`
proper and in general position at every zero. -/
theorem exists_oriented_interval_cobordism (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) :
    ∃ S : (Fin 1 → unitInterval) × X →
        pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X),
      (ivBundle B).IsScPlusSection S ∧
      (ivBundle B).IsProper
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) ∧
      ∀ z, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
        (ivBundle B).IsGeneralPositionGerm
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z := by
  obtain ⟨N, hN⟩ := proposition_5_1_3_exists (B := ivBundle B)
  obtain ⟨U, S, -, -, -, hSp, hP, hgp⟩ := exists_interval_cobordism hX hbump hf hS hN
  exact ⟨S, hSp, hP, hgp⟩

/-- **The index over `[0, 1] × X`** (2021 Remark 6.6.19, p. 276): if `(f, x)` has index `i`
(Definition 6.2.1), then at a zero `(t, x)` of `F = f̃ + S`, `S` an sc⁺-section over
`[0, 1] × X`, the linearization `F'(t, x)` has index `i + 1` (`L̂ = Γ⁻¹ (L ⊕ 0) A` belongs to
`Lin(f̃, (t, x))` and has the index of `L` plus one). -/
theorem isLinOfIndex_interval_of_isIndexAt (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) {t : Fin 1 → unitInterval} {x : X}
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x)) {i : ℤ} (hi : B.IsIndexAt f x i) :
    (ivBundle B).IsLinOfIndex (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x) (i + 1) := by
  have hf' := hf.toIsScFredholmSection
  have hfc := (hf.paramCube (n := 1)).toIsScFredholmSection
  have hzs := (theorem_3_1_18_preprint hfc hS).mem_smoothSet_of_isZeroAt hz0
  have hxs : x ∈ PX.smoothSet := prod_cube_mem_smoothSet_iff.1 hzs
  have hne := ChartPoint.linSet_nonempty
    (chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hxs) hf' hxs
    (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump)
  obtain ⟨L, hL⟩ := hne
  have hT₀m := (chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x)
    hxs).ivLin_mem_linSet_cubeLift (corner t) (mem_chart_corner t)
    (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S (t, x)) hf' hxs hL
  have h1 := (ChartPoint.isFredholm_isIndexAt_of_mem_linSet _ hfc hT₀m).2
  have h2 := ChartPoint.fredholmIndex_of_mem_linSet _ hf' hi hL
  have h3 := fredholmIndex_extConjOp
    ((chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hxs).ivT (corner t)
      (mem_chart_corner t)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S (t, x)))
    ((chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hxs).ivK (corner t)
      (mem_chart_corner t)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S (t, x)))
    h2.1
  rw [h2.2] at h3
  rw [h3] at h1
  exact isLinOfIndex_sectionAdd_of_isIndexAt hfc hS hz0 h1

/-- **The hypotheses of `theorem_6_6_18_oriented_interval` are satisfiable** for every tame
sc-Fredholm section `f` with compact solution set and index `k` over a tame `X` with sc-smooth
bump functions: there is an sc⁺-section `S` over `[0, 1] × X` such that `F = f̃ + S` is proper,
in general position at every zero (the zeros on `\{0, 1\} × X` included) and of index `k + 1`
at every zero. -/
theorem exists_oriented_interval_cobordism_of_index (hX : PX.IsTame)
    (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
    (hS : IsCompact (solutionSet P f)) {k : ℕ} (hk : ∀ x ∈ PX.smoothSet, B.IsIndexAt f x k) :
    ∃ S : (Fin 1 → unitInterval) × X →
        pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X),
      (ivBundle B).IsScPlusSection S ∧
      (ivBundle B).IsProper
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) ∧
      (∀ z, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
        (ivBundle B).IsGeneralPositionGerm
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z) ∧
      ∀ z, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
        (ivBundle B).IsLinOfIndex
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z
          (k + 1 : ℕ) := by
  obtain ⟨S, hSp, hP, hgp⟩ := exists_oriented_interval_cobordism hX hbump hf hS
  refine ⟨S, hSp, hP, hgp, fun z hz => ?_⟩
  obtain ⟨t, x⟩ := z
  have hzs := (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection
    hSp).mem_smoothSet_of_isZeroAt hz
  have h := isLinOfIndex_interval_of_isIndexAt hbump hf hSp hz
    (hk x (prod_cube_mem_smoothSet_iff.1 hzs))
  have hc : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; rfl
  rw [hc]
  exact h

end Existence

end Polyfold
