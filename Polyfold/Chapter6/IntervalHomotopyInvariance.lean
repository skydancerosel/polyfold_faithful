import Polyfold.Chapter6.Theorem671Final
import Polyfold.Chapter6.IntervalCobordismExistence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.7, pp. 277–279:
**Theorem 6.7.1** (2) (preprint Theorem 6.43) for homotopies parametrized by `[0, 1]`.

# Theorem 6.7.1 (2) for homotopies over `[0, 1] × X`

`theorem_6_7_1` states the invariance (2) for homotopies `S` over `ℝ¹ × X`, restricted to the
slab `t ∈ [0, 1]`.  Here the homotopy is an sc⁺-section `S` of the pull-back of `P` to the
M-polyfold with boundary `[0, 1] × X`, with `S(0, ·) = 0` and `F = f̃₀ + S` of compact solution
set in `[0, 1] × X` (a cobordism between `S_{f₀}` and `S_{f₀ + S(1, ·)}` when `F` is in general
position).

* `sinSqCube_zero`, `sinSqCube_one`: the reparametrization `ψ(v) = sin²(π v / 2)` fixes the ends.
* `isZeroAt_homotopySection_cubeReparam_iff`: the zeros of the reparametrized homotopy
  `(v, x) ↦ f₀(x) + S(ψ(v), x)` over `ℝ¹ × X` are the `(v, x)` with `(ψ(v), x)` a zero of `F`.
* `isProperOrientedHomotopy_cubeReparam`: the reparametrized homotopy is a proper homotopy in
  the sense of `IsProperOrientedHomotopy`.
* `interval_homotopy_invariance`: an assignment `Ψ` that is invariant along proper oriented
  homotopies over `ℝ¹ × X` is invariant along homotopies over `[0, 1] × X`.
* `theorem_6_7_1_interval`: Theorem 6.7.1 with (2) also for homotopies over `[0, 1] × X`.

## Reading

The proof goes through the statement over `ℝ¹ × X` (reparametrization by `ψ`); Stokes' theorem
is not applied on `S_F ⊆ [0, 1] × X` itself.
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

open StrongBundle UnitCube MPolyfold

universe u v

namespace UnitCube

/-- `ψ(0) = 0`. -/
theorem sinSqCube_zero {n : ℕ} : sinSqCube (0 : Fin n → ℝ) = 0 := by
  funext i
  refine Subtype.ext ?_
  change Real.sin (Real.pi / 2 * 0) ^ 2 = 0
  rw [mul_zero, Real.sin_zero]
  norm_num

/-- `ψ(1) = 1`. -/
theorem sinSqCube_one {n : ℕ} : sinSqCube (1 : Fin n → ℝ) = 1 := by
  funext i
  refine Subtype.ext ?_
  change Real.sin (Real.pi / 2 * 1) ^ 2 = 1
  rw [mul_one, Real.sin_pi_div_two]
  norm_num

/-- `ψ` is continuous. -/
theorem continuous_sinSqCube {n : ℕ} : Continuous (sinSqCube (n := n)) :=
  continuous_pi fun i => (((continuous_apply i).comp
    (contDiff_sinSqCube (n := n)).continuous).subtype_mk fun r => (sinSqCube r i).2)

end UnitCube

section IntervalHomotopy

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- **The zeros of the reparametrized homotopy**: `(v, x)` is a zero of
`(v, x) ↦ f₀(x) + S(ψ(v), x)` over `ℝ¹ × X` iff `(ψ(v), x)` is a zero of `F = f̃₀ + S` over
`[0, 1] × X`. -/
theorem isZeroAt_homotopySection_cubeReparam_iff {f₀ : X → Y} (hf₀ : IsSection P f₀)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (v : Fin 1 → ℝ) (x : X) :
    IsZeroAt (pullbackProj P Prod.snd)
        (homotopySection f₀ hf₀ (cubeReparamSection sinSqCube S hS)) (v, x) ↔
      IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f₀ hf₀) S)
        (sinSqCube v, x) := by
  have hS' : IsSection (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
      (cubeReparamSection sinSqCube S hS) := isSection_pullbackLift _
  have hF' : IsSection (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
      (homotopySection f₀ hf₀ (cubeReparamSection sinSqCube S hS)) :=
    (isSection_pullbackLift _).sectionAdd hS'
  have hF : IsSection (pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X))
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f₀ hf₀) S) :=
    (isSection_pullbackLift _).sectionAdd hS
  have e1 : pullbackSlice (homotopySection f₀ hf₀ (cubeReparamSection sinSqCube S hS)) v =
      sectionAdd P f₀ (prodSlice S (sinSqCube v)) :=
    pullbackSlice_sectionAdd_paramLift hf₀ hS' v
  have e2 := prodSlice_sectionAdd_cubeLift hf₀ hS (sinSqCube v)
  rw [isZeroAt_pullback_iff_pullbackSlice hF' v x, isZeroAt_iff_prodSlice hF (sinSqCube v) x, e1,
    e2]

/-- **A homotopy over `[0, 1] × X` gives a proper homotopy over `ℝ¹ × X`** (2021 Theorem 6.7.1
(2), p. 277): for an sc⁺-section `S` over `[0, 1] × X` with `S(0, ·) = 0` such that `F = f̃₀ + S`
has a compact solution set in `[0, 1] × X`, the reparametrized section
`(v, x) ↦ S(ψ(v), x)`, `ψ(v) = sin²(π v / 2)`, is a proper homotopy from `f₀`
(`IsProperOrientedHomotopy`), ending at `f₀ + S(1, ·)`. -/
theorem isProperOrientedHomotopy_cubeReparam {f₀ : X → Y} (hf₀ : B.IsScFredholmSectionTame f₀)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) (h0 : prodSlice S 0 = fiberZero P)
    (hZ : IsCompact (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f₀ hf₀.isScSmooth.1) S))) :
    B.IsProperOrientedHomotopy f₀ hf₀ (cubeReparamSection sinSqCube S hS.1) := by
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  have hS' := hS.cubeReparam (m := 1) contDiff_sinSqCube
  have h0' : pullbackSlice (cubeReparamSection sinSqCube S hS.1) 0 = fiberZero P := by
    change prodSlice S (sinSqCube 0) = _
    rw [sinSqCube_zero]
    exact h0
  have hΦ : Continuous fun z : (Fin 1 → ℝ) × X => (sinSqCube z.1, z.2) :=
    (continuous_sinSqCube.comp continuous_fst).prodMk continuous_snd
  have hsol : solutionSet (pullbackProj P Prod.snd)
      (homotopySection f₀ hf₀.isScSmooth.1 (cubeReparamSection sinSqCube S hS.1)) =
      (fun z : (Fin 1 → ℝ) × X => (sinSqCube z.1, z.2)) ⁻¹'
        solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f₀ hf₀.isScSmooth.1) S) := by
    ext ⟨v, x⟩
    exact isZeroAt_homotopySection_cubeReparam_iff hf₀.isScSmooth.1 hS.1 v x
  have hclosed : IsClosed (solutionSet (pullbackProj P Prod.snd)
      (homotopySection f₀ hf₀.isScSmooth.1 (cubeReparamSection sinSqCube S hS.1))) := by
    rw [hsol]
    exact hZ.isClosed.preimage hΦ
  refine isProperOrientedHomotopy_of_isCompact hf₀ hS' h0'
    (isCompact_slabZeros_of_subset hclosed (hZ.image continuous_snd) fun z hz => ?_)
  have hz1 : z ∈ solutionSet (pullbackProj P Prod.snd)
      (homotopySection f₀ hf₀.isScSmooth.1 (cubeReparamSection sinSqCube S hS.1)) := hz.1
  rw [hsol] at hz1
  exact ⟨_, hz1, rfl⟩

/-- **Invariance along homotopies over `[0, 1] × X`** (2021 Theorem 6.7.1 (2), p. 277): an
assignment `Ψ` which is invariant along proper oriented homotopies over `ℝ¹ × X`
(`IsProperOrientedHomotopyBetween`) is invariant along every sc⁺-section `S` over the
M-polyfold with boundary `[0, 1] × X` with `S(0, ·) = 0` and `F = f̃₀ + S` of compact solution
set: `Ψ(f₀, o₀) = Ψ(f₀ + S(1, ·), o₁)`, `o₁` the orientation induced by `o₀`. -/
theorem interval_homotopy_invariance {Z : ℕ → Type*}
    (Ψ : ∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f), B.IsProper f →
      SectionOrientation f hf.toIsScFredholmSection → ∀ k : ℕ, Z k)
    (hΨ : ∀ (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀) (hP₀ : B.IsProper f₀)
      (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
      (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
      (hf₁ : B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)))
      (hP₁ : B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)))
      (o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) hf₁.toIsScFredholmSection),
      IsProperOrientedHomotopyBetween hf₀ o₀ S o₁ →
        ∀ k : ℕ, Ψ f₀ hf₀ hP₀ o₀ k = Ψ _ hf₁ hP₁ o₁ k)
    (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀) (hP₀ : B.IsProper f₀)
    (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
    (S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hS : (ivBundle B).IsScPlusSection S) (h0 : prodSlice S 0 = fiberZero P)
    (hZ : IsCompact (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f₀ hf₀.isScSmooth.1) S)))
    (hP₁ : B.IsProper (sectionAdd P f₀ (prodSlice S 1))) (k : ℕ) :
    Ψ f₀ hf₀ hP₀ o₀ k = Ψ (sectionAdd P f₀ (prodSlice S 1))
      (theorem_3_1_18_tame hf₀ (hS.cubeSlice 1)) hP₁ (o₀.sectionAdd (hS.cubeSlice 1)) k := by
  have hH := isProperOrientedHomotopy_cubeReparam hf₀ hS h0 hZ
  have key := hΨ f₀ hf₀ hP₀ o₀ (cubeReparamSection sinSqCube S hS.1)
    hH.isScFredholmSectionTame_one hH.isProper_one (o₀.sectionAdd hH.slice_one) ⟨hH, rfl⟩ k
  have aux : ∀ (s s' : X → Y) (_ : s = s') (hs : B.IsScPlusSection s)
      (hs' : B.IsScPlusSection s') (hQ : B.IsProper (sectionAdd P f₀ s))
      (hQ' : B.IsProper (sectionAdd P f₀ s')),
      Ψ (sectionAdd P f₀ s) (theorem_3_1_18_tame hf₀ hs) hQ (o₀.sectionAdd hs) k =
        Ψ (sectionAdd P f₀ s') (theorem_3_1_18_tame hf₀ hs') hQ' (o₀.sectionAdd hs') k := by
    intro s s' h hs hs' hQ hQ'
    subst h
    rfl
  have hsl : pullbackSlice (cubeReparamSection sinSqCube S hS.1) 1 = prodSlice S 1 := by
    change prodSlice S (sinSqCube 1) = _
    rw [sinSqCube_one]
  exact key.trans (aux _ _ hsl hH.slice_one (hS.cubeSlice 1) hH.isProper_one hP₁)

/-- **2021 Theorem 6.7.1** (p. 277; preprint Theorem 6.43), with part (2) also for homotopies
over `[0, 1] × X`: the `Ψ` of `theorem_6_7_1` satisfies (1), (2) for proper oriented homotopies
over `ℝ¹ × X`, and (2) for every sc⁺-section `S` over the M-polyfold with boundary `[0, 1] × X`
with `S(0, ·) = 0` such that `F = f̃₀ + S` has a compact solution set:
`Ψ_{(f₀, o₀)} = Ψ_{(f₁, o₁)}` for `f₁ = f₀ + S(1, ·)` proper and `o₁` induced by `o₀`. -/
theorem theorem_6_7_1_interval (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) :
    ∃ Ψ : ∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f), B.IsProper f →
        SectionOrientation f hf.toIsScFredholmSection → ∀ k : ℕ, relDeRham hX k →ₗ[ℝ] ℝ,
      (∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
          (o : SectionOrientation f hf.toIsScFredholmSection) (N : B.One → ℝ), B.IsAuxNorm N →
        (∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
          ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) ∧
        ∀ U : Set X, IsOpen U → solutionSet P f ⊆ U →
          (∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) →
          (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
          (∃ s, B.IsAdmissible f N U s) ∧
          ∀ (s : X → Y) (hs : B.IsAdmissible f N U s),
            IsCompact (solutionSet P (sectionAdd P f s)) ∧
            solutionSet P (sectionAdd P f s) = ⋃ k : ℕ, B.solPart f s k ∧
            ∀ k : ℕ, IsCompact (B.solPart f s k) ∧ SolPartIsOrientedManifold hX hf hs o k ∧
              ∀ c : LinearMap.ker (relD hX k),
                Ψ f hf hP o k (relDeRhamMk hX k c) =
                  solIntegral hX hbump hf hs o k c - solBoundaryIntegral hX hbump hf hs o k c) ∧
      (∀ (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀) (hP₀ : B.IsProper f₀)
        (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
        (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (hf₁ : B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)))
        (hP₁ : B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)))
        (o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) hf₁.toIsScFredholmSection),
        IsProperOrientedHomotopyBetween hf₀ o₀ S o₁ →
          ∀ k : ℕ, Ψ f₀ hf₀ hP₀ o₀ k = Ψ _ hf₁ hP₁ o₁ k) ∧
      ∀ (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀) (hP₀ : B.IsProper f₀)
        (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
        (S : (Fin 1 → unitInterval) × X →
          pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
        (hS : (ivBundle B).IsScPlusSection S),
        prodSlice S 0 = fiberZero P →
        IsCompact (solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f₀ hf₀.isScSmooth.1) S)) →
        ∀ (hP₁ : B.IsProper (sectionAdd P f₀ (prodSlice S 1))) (k : ℕ),
          Ψ f₀ hf₀ hP₀ o₀ k = Ψ (sectionAdd P f₀ (prodSlice S 1))
            (theorem_3_1_18_tame hf₀ (hS.cubeSlice 1)) hP₁ (o₀.sectionAdd (hS.cubeSlice 1)) k := by
  obtain ⟨Ψ, h1, h2⟩ := theorem_6_7_1 (B := B) hX hbump
  exact ⟨Ψ, h1, h2, interval_homotopy_invariance Ψ h2⟩

end IntervalHomotopy

end Polyfold
