import Polyfold.Chapter6.CubeReparam
import Polyfold.Chapter6.SliceGeneralPosition
import Polyfold.Chapter6.StabKernelsExist
import Polyfold.Chapter6.CubePropertyP
import Polyfold.Chapter6.PropagationWellDefined

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **Lemma 6.6.5**
(pp. 264–266; preprint Lemma 6.30): **the stabilized kernels along a family on `[0, 1]ⁿ`, with
sections over `[0, 1]ⁿ × X`**.  Gap G.65, row V6.42.

# The stabilized kernels over `[0, 1]ⁿ`

## The text, paraphrased

For an sc-smooth path `φ : [0, 1] → X`, an sc⁺-section `s` of the pull-back to `X × [0, 1]` with
`s(φ(t), t) = f(φ(t))` and sc⁺-sections `s₁, …, s_k` with property (P), the kernels
`L_t = ker F_t'(φ(t), 0)` form a (smooth, hence continuous) vector bundle over `[0, 1]`; the
push-forward of orientations along the path is taken along it.

## What is formalized

`exists_isStabKernels` (`StabKernelsExist.lean`) treats `Φ : ℝⁿ → X` with sections over
`ℝⁿ × X`.  Here the family and the sections live on the M-polyfold `[0, 1]ⁿ` itself
(`cubePolyfold n`, boundary and corners included):

* **`exists_isStabKernels_cube`**: for an sc-smooth `Φ : [0, 1]ⁿ → X` with `Φ([0, 1]ⁿ)` in the
  domain of a chart `c`, an sc⁺-section `S` of `pr₂*P → [0, 1]ⁿ × X` with `(f̃ + S)(q, Φ(q)) = 0`
  and sc⁺-sections `s₁, …, s_k` over `[0, 1]ⁿ × X` with `F` in general position at every
  `(0, (q, Φ(q)))` (the conclusion of `lemma_6_6_4_propertyP_cube`), the stabilized kernels of the
  slices `S(q, ·)`, `sᵢ(q, ·)` form a continuous family over `[0, 1]ⁿ` (`IsStabKernels`).
  `exists_isStabKernels_cube_of_propertyP`: the same from property (P) of the slices.
* **`exists_isStabKernels_cube_of_chart`**: for tame `X` with bump functions, the data `S`,
  `sᵢ` exist (`lemma_6_6_4_cube_family`), so the family exists with no hypothesis on sections.
* `[0, 1]ⁿ` is contractible and locally path-connected (`cubeHomeomorphIcc`), so the
  push-forward `IsStabKernels.push` applies to these families.

*Proof*: the family is read through `ψ = sinSqCube : ℝⁿ → [0, 1]ⁿ`, `ψ(v) = (sin²(π vᵢ/2))ᵢ`:
`Φ ∘ ψ` is sc-smooth, `S(ψ(·), ·)` and `sᵢ(ψ(·), ·)` are sc⁺-sections over `ℝⁿ × X`
(`IsScPlusSection.cubeReparam`) with the same slices, and general position transfers through
the slices (`isGeneralPositionGerm_cubeSlice_iff`, `isGeneralPositionGerm_of_slice`).
`exists_isStabKernels` gives the family over `[0, 1]ⁿ ⊆ ℝⁿ`, which is pulled back along the
continuous right inverse `arcCube` of `ψ` (`IsStabKernels.comp`, `sinSqCube_arcCube`).  The values
of the family are the stabilized kernels of the slices at `q`, so they do not depend on `ψ`.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

open UnitCube StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `paramSection` depends only on the sections, not on the proofs that they are sections. -/
lemma paramSection_congr {k : ℕ} {g g' : X → Y} (hg : IsSection P g) (hg' : IsSection P g')
    {t t' : Fin k → X → Y} (ht : ∀ i, IsSection P (t i)) (ht' : ∀ i, IsSection P (t' i))
    (e : g = g') (e' : t = t') :
    paramSection g hg t ht = paramSection g' hg' t' ht' := by
  subst e e'
  rfl

/-- **2021 Lemma 6.6.5 (pp. 264–266) for families on `[0, 1]ⁿ` with sections over `[0, 1]ⁿ × X`:
the stabilized kernels form a continuous family over `[0, 1]ⁿ`** (preprint Lemma 6.30).  For an
sc-smooth `Φ : [0, 1]ⁿ → X` with `Φ([0, 1]ⁿ)` in the domain of a chart `c`, an sc⁺-section `S` of
`pr₂*P → [0, 1]ⁿ × X` with `(f̃ + S)(q, Φ(q)) = 0` for all `q`, and sc⁺-sections `s₁, …, s_k` of
`pr₂*P` with `F = f̃ + S + Σ λᵢ sᵢ` in general position at every `(0, (q, Φ(q)))`, boundary and
corners of `[0, 1]ⁿ` included, the stabilized kernels of the slices `S(q, ·)`, `sᵢ(q, ·)` form a
continuous family over `[0, 1]ⁿ`. -/
theorem exists_isStabKernels_cube (hf : B.IsScFredholmSectionTame f) {n : ℕ}
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]
    {Φ : (Fin n → unitInterval) → X} (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hΦc : ∀ q, Φ q ∈ c.φ.source)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    (hz : ∀ q, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, Φ q))
    {k : ℕ} {s : Fin k → (Fin n → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection
      (s i))
    [ParacompactSpace ((Fin k → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
    [ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X))]
    [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))]
    (hP : ∀ q, ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((cubePolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q))) :
    ∃ Λ : SubspaceFamily (Fin n → unitInterval) (c.φ.model.E 0 × (Fin k → ℝ)),
      IsStabKernels f c hc Φ hΦc (fun q => prodSlice S q) (fun i q => prodSlice (s i) q) Λ := by
  have hfs := hf.isScSmooth
  -- the paracompactness of the spaces over `ℝⁿ`
  have : ParacompactSpace ((Fin n → ℝ) × X) := by
    have := PX.metrizableSpace
    exact paracompactSpace_of_metrizableSpace _
  have : ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) :=
    paracompactSpace_pullbackSpace ((rnPolyfold n).prod PX) B
  have : ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X)) := by
    have := ((rnPolyfold n).prod PX).metrizableSpace
    exact paracompactSpace_of_metrizableSpace _
  have : ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X)) :=
    paracompactSpace_pullbackSpace ((rnPolyfold k).prod ((rnPolyfold n).prod PX))
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX))
  -- the family and the sections read through `ψ = sinSqCube`
  set Φ' : (Fin n → ℝ) → X := Φ ∘ sinSqCube with hΦ'
  have hΦ'm : (rnPolyfold n).IsScSmoothMap PX Φ' := hΦ.comp isScSmoothMap_sinSqCube
  set S' := cubeReparamSection sinSqCube S hS.1 with hS'def
  have hS' : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S' :=
    hS.cubeReparam contDiff_sinSqCube
  set s' := fun i => cubeReparamSection sinSqCube (s i) (hs i).1 with hs'def
  have hs' : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection
      (s' i) := fun i => (hs i).cubeReparam contDiff_sinSqCube
  -- the slices agree
  have hslG : ∀ v : Fin n → ℝ,
      pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S') v =
        prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hfs.1) S) (sinSqCube v) :=
    fun v => (pullbackSlice_sectionAdd_paramLift hfs.1 hS'.1 v).trans
      (prodSlice_sectionAdd_cubeLift hfs.1 hS.1 (sinSqCube v)).symm
  have hzv : ∀ v : Fin n → ℝ, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S') (v, Φ' v) := fun v => by
    rw [isZeroAt_pullback_iff_pullbackSlice ((isSection_pullbackLift _).sectionAdd hS'.1), hslG]
    exact (isZeroAt_iff_prodSlice ((isSection_pullbackLift _).sectionAdd hS.1) _ _).1
      (hz (sinSqCube v))
  have hz' : ∀ᶠ v in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S') (v, Φ' v) :=
    Filter.Eventually.of_forall hzv
  have hP' : ∀ᶠ v in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S')
          ((isSection_pullbackLift _).sectionAdd hS'.1) s' fun i => (hs' i).1) (0, (v, Φ' v)) := by
    refine Filter.Eventually.of_forall fun v => ?_
    refine isGeneralPositionGerm_of_slice hf hS' hs' hΦ'm (Filter.Eventually.of_forall hzv) ?_
    have hsl := (isGeneralPositionGerm_cubeSlice_iff hf hS hs hΦ hz (sinSqCube v)).1
      (hP (sinSqCube v))
    rw [paramSection_congr _ _ _ _ (hslG v) rfl]
    exact hsl
  obtain ⟨Λ', hΛ'⟩ := exists_isStabKernels hf hΦ'm hc (fun v _ => hΦc _) hS' hz' hs' hP'
  -- pull back along `arcCube`
  refine ⟨Λ'.comp ⟨arcCube, continuous_arcCube⟩, ?_⟩
  refine IsStabKernels.congr_data hΦc (hΛ'.comp ⟨arcCube, continuous_arcCube⟩) ?_ ?_ ?_
  · funext q
    change Φ (sinSqCube (arcCube q : Fin n → ℝ)) = Φ q
    rw [sinSqCube_arcCube]
  · funext q
    change prodSlice S (sinSqCube (arcCube q : Fin n → ℝ)) = prodSlice S q
    rw [sinSqCube_arcCube]
  · funext i q
    change prodSlice (s i) (sinSqCube (arcCube q : Fin n → ℝ)) = prodSlice (s i) q
    rw [sinSqCube_arcCube]

/-- **The same from property (P)**: the hypothesis on `F` replaced by property (P) of the slices,
`F_q(λ, y) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)` in general position at `(0, Φ(q))` for every
`q ∈ [0, 1]ⁿ` (equivalent by `isGeneralPositionGerm_cubeSlice_iff`). -/
theorem exists_isStabKernels_cube_of_propertyP (hf : B.IsScFredholmSectionTame f) {n : ℕ}
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]
    {Φ : (Fin n → unitInterval) → X} (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hΦc : ∀ q, Φ q ∈ c.φ.source)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    (hz : ∀ q, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, Φ q))
    {k : ℕ} {s : Fin k → (Fin n → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection
      (s i))
    [ParacompactSpace ((Fin k → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
    [ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X))]
    [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))]
    (hP : ∀ q, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
        (paramSection
          (prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) q)
          (((isSection_pullbackLift _).sectionAdd hS.1).prodSlice q)
          (fun i => prodSlice (s i) q) fun i => (hs i).1.prodSlice q) (0, Φ q)) :
    ∃ Λ : SubspaceFamily (Fin n → unitInterval) (c.φ.model.E 0 × (Fin k → ℝ)),
      IsStabKernels f c hc Φ hΦc (fun q => prodSlice S q) (fun i q => prodSlice (s i) q) Λ :=
  exists_isStabKernels_cube hf hΦ hc hΦc hS hz hs fun q =>
    (isGeneralPositionGerm_cubeSlice_iff hf hS hs hΦ hz q).2 (hP q)

/-- **The data of `exists_isStabKernels_cube` exist** (2021 Proposition 6.6.3 (3) and
Lemmas 6.6.4–6.6.5 on `[0, 1]ⁿ`; preprint Proposition 6.28, Lemmas 6.29–6.30): for a tame `X`
with bump functions and an sc-smooth `Φ : [0, 1]ⁿ → X` in the domain of a chart `c` of the atlas,
there are an sc⁺-section `S` over `[0, 1]ⁿ × X` with `(f̃ + S)(q, Φ(q)) = 0` for all `q`,
sc⁺-sections `s₁, …, s_k` and a continuous family of stabilized kernels of the slices over
`[0, 1]ⁿ`.  No hypothesis on `S` or `sᵢ` remains. -/
theorem exists_isStabKernels_cube_of_chart (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {n : ℕ}
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]
    {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts)
    {Φ : (Fin n → unitInterval) → X} (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ)
    (hΦc : ∀ q, Φ q ∈ c.φ.source) :
    ∃ (S : (Fin n → unitInterval) × X →
        pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
      (_ : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S),
      (∀ q, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, Φ q)) ∧
      ∃ (k : ℕ) (s : Fin k → (Fin n → unitInterval) × X →
          pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
        (_ : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection
          (s i))
        (Λ : SubspaceFamily (Fin n → unitInterval) (c.φ.model.E 0 × (Fin k → ℝ))),
        IsStabKernels f c (B.isChart_of_mem hc) Φ hΦc (fun q => prodSlice S q)
          (fun i q => prodSlice (s i) q) Λ := by
  obtain ⟨S, hS, hz, k, s, hs, hP⟩ := lemma_6_6_4_cube_family hX hbump hf hc hΦ hΦc
  have : ParacompactSpace ((Fin k → ℝ) × X) := by
    have := PX.metrizableSpace
    exact paracompactSpace_of_metrizableSpace _
  have : ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X)) :=
    paracompactSpace_pullbackSpace ((rnPolyfold k).prod PX) B
  have : ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X)) := by
    have := ((cubePolyfold n).prod PX).metrizableSpace
    exact paracompactSpace_of_metrizableSpace _
  have : ParacompactSpace (pullbackSpace (pullbackProj P
      (Prod.snd : (Fin n → unitInterval) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X)) :=
    paracompactSpace_pullbackSpace ((rnPolyfold k).prod ((cubePolyfold n).prod PX))
      (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX))
  obtain ⟨Λ, hΛ⟩ := exists_isStabKernels_cube hf hΦ (B.isChart_of_mem hc) hΦc hS hz hs hP
  exact ⟨S, hS, hz, k, s, hs, Λ, hΛ⟩

/-! ### The push-forward along families on `[0, 1]ⁿ`

The push-forward of orientations along stabilized kernels (`IsStabKernels.push`, p. 224) needs a
simply connected, locally path-connected parameter space.  `[0, 1]ⁿ` is homeomorphic to the
convex set `[0, 1]ⁿ ⊆ ℝⁿ` (`cubeHomeomorphIcc`), hence contractible and locally path-connected, so
`push`, `push_trans`, `push_comp` apply to the families of `exists_isStabKernels_cube`. -/

/-- `[0, 1]ⁿ` (`Fin n → [0, 1]`) is homeomorphic to `[0, 1]ⁿ ⊆ ℝⁿ`. -/
def cubeHomeomorphIcc (n : ℕ) : (Fin n → unitInterval) ≃ₜ Icc (0 : Fin n → ℝ) 1 where
  toFun q := ⟨fun i => q i, fun i => (q i).2.1, fun i => (q i).2.2⟩
  invFun v i := ⟨v.1 i, v.2.1 i, v.2.2 i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_pi fun i =>
    continuous_subtype_val.comp (continuous_apply i)).subtype_mk _
  continuous_invFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

instance (n : ℕ) : ContractibleSpace (Fin n → unitInterval) :=
  (cubeHomeomorphIcc n).contractibleSpace

instance (n : ℕ) : LocallyPathConnectedSpace (Fin n → unitInterval) :=
  (cubeHomeomorphIcc n).symm.isQuotientMap.locallyPathConnectedSpace

example (n : ℕ) : SimplyConnectedSpace (Fin n → unitInterval) := inferInstance

end Polyfold
