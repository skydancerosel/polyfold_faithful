import Polyfold.Chapter6.IntervalEndManifolds

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.2, p. 189
(**Theorem 4.2.11**; preprint Theorem 4.22), §5.3, p. 220 (**Theorem 5.3.10**; preprint Theorem
5.18) and the proof of **Theorem 6.7.1**, p. 278: the boundary of the cobordism
`S_F ⊆ [0, 1] × X`, `F = f̃ + S`.

# The boundary of the cobordism over `[0, 1] × X`

## What is formalized

* `UnitCube.cubePolyfold_one_degIndex`: `d_{[0, 1]}(t) = 1` for `t ∈ \{0, 1\}` and `0`
  otherwise.
* **`degIndex_interval_cobordism`**: for `F` proper and in general position at every zero,
  `d_{S_F}(t, x) = d_{[0, 1]}(t) + d_X(x)` at every `(t, x) ∈ S_F` (the degeneracy index of the
  sub-M-polyfold `S_F`).
* **`mem_boundary_interval_cobordism_iff`**: `(t, x) ∈ ∂S_F` iff `t ∈ \{0, 1\}` or `x ∈ ∂X`:
  `∂S_F = (S_F ∩ (\{0, 1\} × X)) ∪ (S_F ∩ ([0, 1] × ∂X))`.
* **`degIndex_interval_cobordism_end`**: for `t ∈ \{0, 1\}` and `x ∈ S_{F_t}`,
  `d_{S_F}(t, x) = d_{S_{F_t}}(x) + 1`: the point `(t, x)` lies on one more face of `S_F` than
  `x` does of `S_{F_t}`.

## Reading

`∂S_F` is the boundary `\{d ≥ 1\}` of the sub-M-polyfold `S_F` of `[0, 1] × X` (Definition
2.4.5), whose corner structure gives the manifold with boundary and corners of
`theorem_6_6_18_oriented_interval`.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube MPolyfold

/-- **The degeneracy index of `[0, 1]`**: `1` at the end points and `0` in the interior. -/
theorem UnitCube.cubePolyfold_one_degIndex (t : Fin 1 → unitInterval) :
    (cubePolyfold 1).degIndex t = if (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1 then 1 else 0 := by
  rw [cubePolyfold_degIndex]
  split_ifs with h
  · rw [Finset.filter_true_of_mem fun i _ => by rw [Subsingleton.elim i 0]; exact h]
    rfl
  · rw [Finset.filter_false_of_mem fun i _ => by rw [Subsingleton.elim i 0]; exact h]
    rfl

section Degeneracy

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

/-- **The degeneracy index of the cobordism** (2021 Theorem 5.3.10, p. 220, with Theorem
4.2.11 (2), p. 189): let `X` be tame and `F = f̃ + S` over `[0, 1] × X` proper and in general
position at every zero.  Then at every `(t, x) ∈ S_F` the degeneracy index of the
sub-M-polyfold `S_F` is `d_{[0, 1]}(t) + d_X(x)`. -/
theorem degIndex_interval_cobordism (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hP : (ivBundle B).IsProper
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    (hSm : ((cubePolyfold 1).prod PX).IsSmoothSubmanifold (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)))
    (z : solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :
    haveI := ((cubePolyfold 1).prod PX).paracompactSpace_subtype
      (solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    (MPolyfold.subPolyfold hSm.isSubMPolyfold).degIndex z =
      (cubePolyfold 1).degIndex z.1.1 + PX.degIndex z.1.2 := by
  have := ((cubePolyfold 1).prod PX).paracompactSpace_subtype
    (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
  obtain ⟨-, -, -, hSm', -, -, -, hdeg⟩ := theorem_6_6_18_solutionSet (prod_cube_isTame hX)
    (theorem_3_1_18_tame (hf.paramCube (n := 1)) hS) hP hgp
  have h := hdeg z
  rw [(MPolyfold.isTame_prod (cubePolyfold 1) PX (cubePolyfold_isTame 1) hX).2 z.1.1 z.1.2] at h
  exact h

/-- **The boundary of the cobordism** (the proof of 2021 Theorem 6.7.1, p. 278): a point
`(t, x)` of `S_F` is a boundary point of the sub-M-polyfold `S_F` iff `t ∈ \{0, 1\}` or
`x ∈ ∂X`: `∂S_F = (S_F ∩ (\{0, 1\} × X)) ∪ (S_F ∩ ([0, 1] × ∂X))`. -/
theorem mem_boundary_interval_cobordism_iff (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hP : (ivBundle B).IsProper
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    (hSm : ((cubePolyfold 1).prod PX).IsSmoothSubmanifold (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)))
    (z : solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :
    haveI := ((cubePolyfold 1).prod PX).paracompactSpace_subtype
      (solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    z ∈ (MPolyfold.subPolyfold hSm.isSubMPolyfold).boundary ↔
      ((z.1.1 0 : ℝ) = 0 ∨ (z.1.1 0 : ℝ) = 1) ∨ z.1.2 ∈ PX.boundary := by
  have := ((cubePolyfold 1).prod PX).paracompactSpace_subtype
    (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
  change 1 ≤ (MPolyfold.subPolyfold hSm.isSubMPolyfold).degIndex z ↔
    ((z.1.1 0 : ℝ) = 0 ∨ (z.1.1 0 : ℝ) = 1) ∨ 1 ≤ PX.degIndex z.1.2
  rw [degIndex_interval_cobordism hX hf hS hP hgp hSm z, cubePolyfold_one_degIndex]
  split_ifs with h
  · exact ⟨fun _ => Or.inl h, fun _ => Nat.le_add_right 1 _⟩
  · rw [zero_add]
    exact ⟨fun h' => Or.inr h', fun h' => h'.resolve_left h⟩

/-- **The ends are faces of the cobordism** (the proof of 2021 Theorem 6.7.1, p. 278): let `F`
be proper and in general position at every zero, `t ∈ \{0, 1\}` and `x ∈ S_{F_t}`.  Then
`d_{S_F}(t, x) = d_{S_{F_t}}(x) + 1` for the sub-M-polyfolds `S_F ⊆ [0, 1] × X` and
`S_{F_t} ⊆ X`. -/
theorem degIndex_interval_cobordism_end (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hP : (ivBundle B).IsProper
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    (hSm : ((cubePolyfold 1).prod PX).IsSmoothSubmanifold (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)))
    {t : Fin 1 → unitInterval} (ht : (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1)
    (hSt : PX.IsSmoothSubmanifold (solutionSet P (sectionAdd P f (prodSlice S t))))
    (x : solutionSet P (sectionAdd P f (prodSlice S t))) :
    haveI := ((cubePolyfold 1).prod PX).paracompactSpace_subtype
      (solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    haveI := PX.paracompactSpace_subtype (solutionSet P (sectionAdd P f (prodSlice S t)))
    (MPolyfold.subPolyfold hSm.isSubMPolyfold).degIndex
        ⟨(t, x.1), isZeroAt_of_isZeroAt_slice hf.isScSmooth.1 hS.1 x.2⟩ =
      (MPolyfold.subPolyfold hSt.isSubMPolyfold).degIndex x + 1 := by
  have := ((cubePolyfold 1).prod PX).paracompactSpace_subtype
    (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
  have := PX.paracompactSpace_subtype (solutionSet P (sectionAdd P f (prodSlice S t)))
  have hPt : B.IsProper (sectionAdd P f (prodSlice S t)) := isProper_slice hf hS hP t
  have hgpt : ∀ y, IsZeroAt P (sectionAdd P f (prodSlice S t)) y →
      B.IsGeneralPositionGerm (sectionAdd P f (prodSlice S t)) y := fun y hy =>
    isGeneralPositionGerm_slice_of_end hf hS ht
      (isZeroAt_of_isZeroAt_slice hf.isScSmooth.1 hS.1 hy)
      (hgp _ (isZeroAt_of_isZeroAt_slice hf.isScSmooth.1 hS.1 hy))
  obtain ⟨-, -, -, hSt', -, -, -, hdeg⟩ := theorem_6_6_18_solutionSet hX
    (theorem_3_1_18_tame hf (hS.cubeSlice t)) hPt hgpt
  have h1 := degIndex_interval_cobordism hX hf hS hP hgp hSm
    ⟨(t, x.1), isZeroAt_of_isZeroAt_slice hf.isScSmooth.1 hS.1 x.2⟩
  rw [cubePolyfold_one_degIndex, if_pos ht] at h1
  rw [h1, hdeg x, add_comm]

end Degeneracy

end Polyfold
