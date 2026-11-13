import Polyfold.Chapter15.P3W4TX_Invariants
import Polyfold.Chapter15.P3W5TY_CylinderGlue

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3–15.4,
pp. 699–703: the cobordism `Θ̃ = Λ̃ ∘ f̃` over `[0, 1] × X` behind **Corollary 15.4.4**
(2017: Corollary 15.2), from the proof of **Corollary 15.3.10 (3)**: its restriction to the two
ends `{i} × X` and the splitting of the boundary measure of `Θ̃` over the two ends (gap TX-6,
in part).

# The ends of the cylinder cobordism

## The text, paraphrased

In the proof of Corollary 15.3.10 (p. 700), `Λ̃` on `W̃ → [0, 1] × X` restricts over `{i} × X`
to `Λⁱ`, so `Θ̃ = Λ̃ ∘ f̃` "restricts to `{i} × X = X` as `Θᵢ`", and `Θ̃` is "a compact cobordism
between `Θ₀` and `Θ₁`".  Corollary 15.4.4 (p. 703, proof left to the reader) uses it with
Stokes: `∫_{∂Θ̃} pr^*ω = ∫_{Θ₁} ω − ∫_{Θ₀} ω`, where `∂([0, 1] × X) = {0, 1} × X` when `d_X ≡ 0`.

## What is formalized

Namespace `Polyfold.EpGroupoid` (for any ep-groupoid `X`):
* `cylOrbitTime`: the time coordinate on `|[0, 1] × X|` (through TY's `cubeOrbitHomeomorph`),
  continuous, `cylOrbitTime |(t, x)| = t`.
* `cylEnd Θ i`: the part of `|supp(∂Θ)|` at time `i`, for `Θ` on `[0, 1] × X`; it is closed, so
  it lies in the σ-algebra `L(∂S)` of Definition 9.5.14 (`measurableSet_cylEnd`).
* **`signedMeasure_univ_eq_cylEnds`**: if `∂([0, 1] × X)` lies over `t ∈ {0, 1}`, every signed
  measure on `(∂S, L(∂S))` is the sum of its values on the two ends.
* `cylEndMap`: the map `|supp ∂Θ̃| ⊇ (end i) → |X|`, `|(i, x)| ↦ |x|`, continuous and injective.

Namespace `Polyfold.SBLocalization` (for `W̃ → [0, 1] × X` and `f̃(t, x) = (t, f(x))`):
* `theta_cyl_of_time_zero/one`, **`theta_cubeIncl_zero/one`**: `Θ̃(i, x) = Θᵢ(x)` (the text's
  "restricts to `{i} × X = X` as `Θᵢ`").
* **`mem_boundary_inter_supp_cyl_iff`**: for `d_X ≡ 0`,
  `∂([0, 1] × X) ∩ supp Θ̃ = {0} × supp Θ₀ ∪ {1} × supp Θ₁`.
* **`cylEndMap_mem_orbitSupp`**: the end `i` of `|supp ∂Θ̃|` lies over `|supp Θᵢ|`.
* **`boundaryMeasure_cyl_univ`**: for `d_X ≡ 0` the boundary measure of Theorem 9.5.15 of any
  compact oriented tame `Θ̃` on `[0, 1] × X` is the sum over the two ends (also the effective one,
  `boundaryMeasureEff_cyl_univ`).

The identification of each end with `±∫_{Θᵢ}` (the oriented boundary identification) is the
proposition `IsCylinderBoundaryOf` of `P3W7W2_CylinderCobordism`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  [ParacompactSpace ((Fin 1 → unitInterval) × Obj)]
  [ParacompactSpace ((Fin 1 → unitInterval) × Mor)]

/-! ### The time coordinate of `|[0, 1] × X|` -/

/-- The time coordinate `|(t, x)| ↦ t` of the orbit space of `[0, 1] × X`. -/
def cylOrbitTime (o : (X.cubeProd 1).OrbitSpace) : ℝ :=
  (((X.cubeOrbitHomeomorph 1).symm o).1 0 : ℝ)

theorem cylOrbitTime_π (z : (Fin 1 → unitInterval) × Obj) :
    X.cylOrbitTime ((X.cubeProd 1).π z) = (z.1 0 : ℝ) := by
  have e : (X.cubeOrbitHomeomorph 1) (z.1, X.π z.2) = (X.cubeProd 1).π z := rfl
  rw [cylOrbitTime, ← e, Homeomorph.symm_apply_apply]

theorem continuous_cylOrbitTime : Continuous X.cylOrbitTime :=
  continuous_subtype_val.comp
    ((continuous_apply 0).comp (continuous_fst.comp (X.cubeOrbitHomeomorph 1).symm.continuous))

/-! ### The two ends of `|supp ∂Θ|` -/

variable {X} in
/-- The **end at time `i`** of `∂S = |supp ∂Θ|`, for `Θ` on `[0, 1] × X`. -/
def cylEnd (Θ : (Fin 1 → unitInterval) × Obj → ℚ) (i : ℝ) :
    Set ((X.cubeProd 1).orbitSupp ((X.cubeProd 1).boundaryTheta Θ)) :=
  {p | X.cylOrbitTime p.1 = i}

theorem isClosed_cylEnd (Θ : (Fin 1 → unitInterval) × Obj → ℚ) (i : ℝ) :
    IsClosed (cylEnd (X := X) Θ i) :=
  isClosed_eq (X.continuous_cylOrbitTime.comp continuous_subtype_val) continuous_const

/-- The ends are closed, hence Borel, hence in `L(∂S)` (Definition 9.5.14). -/
theorem measurableSet_cylEnd (n : ℕ) (Θ : (Fin 1 → unitInterval) × Obj → ℚ) (i : ℝ) :
    MeasurableSet[(X.cubeProd 1).lebesgueSigmaBoundaryH n Θ] (cylEnd (X := X) Θ i) :=
  (X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH n Θ _
    (@MeasurableSet.of_compl _ _ (borel _)
      (MeasurableSpace.measurableSet_generateFrom (X.isClosed_cylEnd Θ i).isOpen_compl))

/-- Over a cylinder whose boundary lies over `t ∈ {0, 1}`, every point of `|supp ∂Θ|` is at time
`0` or `1` (`supp ∂Θ ⊆ ∂X ∩ supp Θ`, Definition 9.2.16). -/
theorem cylOrbitTime_eq_zero_or_one
    (hbd : ∀ z ∈ (X.cubeProd 1).PObj.boundary, (z.1 0 : ℝ) = 0 ∨ (z.1 0 : ℝ) = 1)
    {Θ : (Fin 1 → unitInterval) × Obj → ℚ}
    (p : (X.cubeProd 1).orbitSupp ((X.cubeProd 1).boundaryTheta Θ)) :
    X.cylOrbitTime p.1 = 0 ∨ X.cylOrbitTime p.1 = 1 := by
  obtain ⟨z, hz, hzp⟩ := p.2
  rw [← hzp, cylOrbitTime_π]
  exact hbd z ((X.cubeProd 1).supp_boundaryTheta_subset Θ hz).1

/-- **The boundary of the cobordism splits over the two ends**: if `∂([0, 1] × X)` lies over
`t ∈ {0, 1}`, then for every σ-algebra on `∂S` containing the Borel sets and every signed measure
`μ` on it, `μ(∂S) = μ(end 0) + μ(end 1)`. -/
theorem signedMeasure_univ_eq_cylEnds
    (hbd : ∀ z ∈ (X.cubeProd 1).PObj.boundary, (z.1 0 : ℝ) = 0 ∨ (z.1 0 : ℝ) = 1)
    {Θ : (Fin 1 → unitInterval) × Obj → ℚ}
    {mσ : MeasurableSpace ((X.cubeProd 1).orbitSupp ((X.cubeProd 1).boundaryTheta Θ))}
    (hle : borel _ ≤ mσ) (μ : @SignedMeasure _ mσ) :
    μ univ = μ (cylEnd (X := X) Θ 0) + μ (cylEnd (X := X) Θ 1) := by
  have hm : ∀ i, MeasurableSet[mσ] (cylEnd (X := X) Θ i) := fun i =>
    hle _ (@MeasurableSet.of_compl _ _ (borel _)
      (MeasurableSpace.measurableSet_generateFrom (X.isClosed_cylEnd Θ i).isOpen_compl))
  have hu : univ = cylEnd (X := X) Θ 0 ∪ cylEnd (X := X) Θ 1 :=
    (eq_univ_of_forall fun p => X.cylOrbitTime_eq_zero_or_one hbd p).symm
  have hdis : Disjoint (cylEnd (X := X) Θ 0) (cylEnd (X := X) Θ 1) :=
    Set.disjoint_left.2 fun p (h0 : _ = _) (h1 : _ = _) => zero_ne_one (h0.symm.trans h1)
  rw [hu]
  exact VectorMeasure.of_union hdis (hm 0) (hm 1)

/-! ### The ends lie over `|X|` -/

variable {X} in
/-- The map from the end at time `i` of `|supp ∂Θ|` to `|X|`, `|(i, x)| ↦ |x|`. -/
def cylEndMap {Θ : (Fin 1 → unitInterval) × Obj → ℚ} {i : ℝ} (p : cylEnd (X := X) Θ i) :
    X.OrbitSpace :=
  ((X.cubeOrbitHomeomorph 1).symm p.1.1).2

theorem cylEndMap_π {Θ : (Fin 1 → unitInterval) × Obj → ℚ} {i : ℝ} (p : cylEnd (X := X) Θ i)
    (z : (Fin 1 → unitInterval) × Obj) (hz : (X.cubeProd 1).π z = p.1.1) :
    cylEndMap p = X.π z.2 := by
  have e : (X.cubeOrbitHomeomorph 1) (z.1, X.π z.2) = (X.cubeProd 1).π z := rfl
  rw [cylEndMap, ← hz, ← e, Homeomorph.symm_apply_apply]

theorem continuous_cylEndMap (Θ : (Fin 1 → unitInterval) × Obj → ℚ) (i : ℝ) :
    Continuous (cylEndMap (X := X) (Θ := Θ) (i := i)) :=
  continuous_snd.comp ((X.cubeOrbitHomeomorph 1).symm.continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val))

/-- On one end the time is fixed, so `|(i, x)| ↦ |x|` is injective. -/
theorem injective_cylEndMap (Θ : (Fin 1 → unitInterval) × Obj → ℚ) (i : ℝ) :
    Injective (cylEndMap (X := X) (Θ := Θ) (i := i)) := by
  intro p p' h
  obtain ⟨z, -, hz⟩ := p.1.2
  obtain ⟨z', -, hz'⟩ := p'.1.2
  have ht : (z.1 0 : ℝ) = z'.1 0 := by
    have h0 : X.cylOrbitTime p.1.1 = i := p.2
    have h1 : X.cylOrbitTime p'.1.1 = i := p'.2
    rw [← hz, cylOrbitTime_π] at h0
    rw [← hz', cylOrbitTime_π] at h1
    rw [h0, h1]
  have hx : X.π z.2 = X.π z'.2 := by
    rw [← X.cylEndMap_π p z hz, ← X.cylEndMap_π p' z' hz']
    exact h
  have hq : z.1 = z'.1 := funext fun j => by
    rw [Subsingleton.elim j 0]
    exact Subtype.ext ht
  refine Subtype.ext (Subtype.ext ?_)
  exact hz.symm.trans (((X.cubeProd_π_eq_π_iff 1 z z').2 ⟨hq, hx⟩).trans hz')

end EpGroupoid

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-! ### `Θ̃` on the two ends -/

/-- Over `t = 0`, `Λ̃(f̃(t, x)) = Λ⁰(f(x))`. -/
theorem theta_cyl_of_time_zero {f : A.Obj → A.W} (hf : IsSection A.P f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ : A.W → ℚ≥0}
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    {z : (A.cubeSEP 1).Obj} (hz : (z.1 0 : ℝ) = 0) :
    Λ' (cubeLiftEp (n := 1) f hf z) = Λ₀ (f z.2) :=
  h0 _ hz

/-- Over `t = 1`, `Λ̃(f̃(t, x)) = Λ¹(f(x))`. -/
theorem theta_cyl_of_time_one {f : A.Obj → A.W} (hf : IsSection A.P f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₁ : A.W → ℚ≥0}
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    {z : (A.cubeSEP 1).Obj} (hz : (z.1 0 : ℝ) = 1) :
    Λ' (cubeLiftEp (n := 1) f hf z) = Λ₁ (f z.2) :=
  h1 _ hz

/-- **`Θ̃` restricts to `{0} × X = X` as `Θ₀`** (proof of Corollary 15.3.10, p. 700):
`Θ̃ ∘ i₀ = Θ₀` for the inclusion functor `i₀ : X → [0, 1] × X`, `x ↦ (0, x)`. -/
theorem theta_cubeIncl_zero {f : A.Obj → A.W} (hf : IsSection A.P f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ : A.W → ℚ≥0}
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) (x : A.Obj) :
    Λ' (cubeLiftEp (n := 1) f hf ((A.X.cubeIncl 1 fun _ => 0).obj x)) = Λ₀ (f x) :=
  theta_cyl_of_time_zero hf h0 (z := ((fun _ => 0), x)) rfl

/-- **`Θ̃` restricts to `{1} × X = X` as `Θ₁`**: `Θ̃ ∘ i₁ = Θ₁`. -/
theorem theta_cubeIncl_one {f : A.Obj → A.W} (hf : IsSection A.P f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₁ : A.W → ℚ≥0}
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) (x : A.Obj) :
    Λ' (cubeLiftEp (n := 1) f hf ((A.X.cubeIncl 1 fun _ => 1).obj x)) = Λ₁ (f x) :=
  theta_cyl_of_time_one hf h1 (z := ((fun _ => 1), x)) rfl

/-- **The boundary part of the support of `Θ̃`** (proof of Corollary 15.3.10, p. 700): for
`d_X ≡ 0`, `∂([0, 1] × X) ∩ supp Θ̃ = {0} × supp Θ₀ ∪ {1} × supp Θ₁`. -/
theorem mem_boundary_inter_supp_cyl_iff (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {f : A.Obj → A.W} (hf : IsSection A.P f) {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (z : (A.cubeSEP 1).Obj) :
    z ∈ (A.cubeSEP 1).X.PObj.boundary ∩
        EpGroupoid.supp (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) ↔
      ((z.1 0 : ℝ) = 0 ∧ z.2 ∈ EpGroupoid.supp (fun x => (Λ₀ (f x) : ℚ))) ∨
        ((z.1 0 : ℝ) = 1 ∧ z.2 ∈ EpGroupoid.supp (fun x => (Λ₁ (f x) : ℚ))) := by
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  rw [mem_inter_iff, mem_boundary_cubeSEP_iff hX hd z]
  constructor
  · rintro ⟨h | h, hs⟩
    · refine Or.inl ⟨h, ?_⟩
      have hs' : (0 : ℚ) < Λ' (cubeLiftEp (n := 1) f hf z) := hs
      rw [theta_cyl_of_time_zero hf h0 h] at hs'
      exact hs'
    · refine Or.inr ⟨h, ?_⟩
      have hs' : (0 : ℚ) < Λ' (cubeLiftEp (n := 1) f hf z) := hs
      rw [theta_cyl_of_time_one hf h1 h] at hs'
      exact hs'
  · rintro (⟨h, hs⟩ | ⟨h, hs⟩)
    · refine ⟨Or.inl h, ?_⟩
      change (0 : ℚ) < Λ' (cubeLiftEp (n := 1) f hf z)
      rw [theta_cyl_of_time_zero hf h0 h]
      exact hs
    · refine ⟨Or.inr h, ?_⟩
      change (0 : ℚ) < Λ' (cubeLiftEp (n := 1) f hf z)
      rw [theta_cyl_of_time_one hf h1 h]
      exact hs

/-- **The end `i` of `|supp ∂Θ̃|` lies over `|supp Θᵢ|`** (`i = 0`): `∂Θ̃ ⊆ Θ₀ ⊔ Θ₁` on the level
of orbit spaces, for `d_X ≡ 0`. -/
theorem cylEndMap_mem_orbitSupp_zero (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {f : A.Obj → A.W} (hf : IsSection A.P f) {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (p : cylEnd (X := A.X) (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) 0) :
    cylEndMap p ∈ A.X.orbitSupp (fun x => (Λ₀ (f x) : ℚ)) := by
  obtain ⟨⟨o, z, hz, rfl⟩, hpi⟩ := p
  have hzt : (z.1 0 : ℝ) = 0 := by
    have : A.X.cylOrbitTime ((A.X.cubeProd 1).π z) = 0 := hpi
    rwa [cylOrbitTime_π] at this
  have hzb := ((A.cubeSEP 1).X.supp_boundaryTheta_subset _ hz)
  rcases (mem_boundary_inter_supp_cyl_iff hd hf h0 h1 z).1 hzb with ⟨-, hs⟩ | ⟨h, -⟩
  · rw [A.X.cylEndMap_π _ z rfl]
    exact ⟨z.2, hs, rfl⟩
  · exact absurd (hzt.symm.trans h) zero_ne_one

/-- **The end `1` of `|supp ∂Θ̃|` lies over `|supp Θ₁|`.** -/
theorem cylEndMap_mem_orbitSupp_one (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {f : A.Obj → A.W} (hf : IsSection A.P f) {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (p : cylEnd (X := A.X) (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) 1) :
    cylEndMap p ∈ A.X.orbitSupp (fun x => (Λ₁ (f x) : ℚ)) := by
  obtain ⟨⟨o, z, hz, rfl⟩, hpi⟩ := p
  have hzt : (z.1 0 : ℝ) = 1 := by
    have : A.X.cylOrbitTime ((A.X.cubeProd 1).π z) = 1 := hpi
    rwa [cylOrbitTime_π] at this
  have hzb := ((A.cubeSEP 1).X.supp_boundaryTheta_subset _ hz)
  rcases (mem_boundary_inter_supp_cyl_iff hd hf h0 h1 z).1 hzb with ⟨h, -⟩ | ⟨-, hs⟩
  · exact absurd (h.symm.trans hzt) zero_ne_one
  · rw [A.X.cylEndMap_π _ z rfl]
    exact ⟨z.2, hs, rfl⟩

/-! ### The boundary measure of a cobordism over `[0, 1] × X` -/

/-- For `d_X ≡ 0`, `∂([0, 1] × X)` lies over `t ∈ {0, 1}`. -/
theorem boundary_cyl_time (hd : ∀ x, A.X.PObj.degIndex x = 0) :
    ∀ z ∈ (A.X.cubeProd 1).PObj.boundary, (z.1 0 : ℝ) = 0 ∨ (z.1 0 : ℝ) = 1 :=
  fun z hz => (mem_boundary_cubeSEP_iff (A.X.isTame_of_degIndex_eq_zero hd) hd z).1 hz

/-- **`μ^{∂Θ̃}_ω(∂S) = μ^{∂Θ̃}_ω(end 0) + μ^{∂Θ̃}_ω(end 1)`** for the boundary measure of
Theorem 9.5.15 of a compact, branched, oriented, tame `Θ̃` of dimension `m + 2` on `[0, 1] × X`,
`d_X ≡ 0`. -/
theorem boundaryMeasure_cyl_univ (hd : ∀ x, A.X.PObj.degIndex x = 0) {m : ℕ} (hm : 0 < m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1) Θ' x, C.Represents T')
    (ω : (A.cubeSEP 1).baseEP.epFormsInfty m) :
    (A.cubeSEP 1).baseEP.boundaryMeasure hm hΘ' hcpt' hT' hloc' ω univ =
      (A.cubeSEP 1).baseEP.boundaryMeasure hm hΘ' hcpt' hT' hloc' ω (cylEnd (X := A.X) Θ' 0) +
        (A.cubeSEP 1).baseEP.boundaryMeasure hm hΘ' hcpt' hT' hloc' ω
          (cylEnd (X := A.X) Θ' 1) :=
  A.X.signedMeasure_univ_eq_cylEnds (boundary_cyl_time hd)
    ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (m + 1) Θ') _

/-- The effective form of `boundaryMeasure_cyl_univ` (the boundary measure of Theorem 9.5.16). -/
theorem boundaryMeasureEff_cyl_univ (hd : ∀ x, A.X.PObj.degIndex x = 0) {m : ℕ} (hm : 0 < m)
    (hLUC : (A.cubeSEP 1).X.IsLUC)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1) Θ' x, C.Represents T')
    (ω : (A.cubeSEP 1).baseEP.epFormsInfty m) :
    (A.cubeSEP 1).baseEP.boundaryMeasureEff hm hLUC hΘ' hcpt' hT' hloc' ω univ =
      (A.cubeSEP 1).baseEP.boundaryMeasureEff hm hLUC hΘ' hcpt' hT' hloc' ω
          (cylEnd (X := A.X) Θ' 0) +
        (A.cubeSEP 1).baseEP.boundaryMeasureEff hm hLUC hΘ' hcpt' hT' hloc' ω
          (cylEnd (X := A.X) Θ' 1) :=
  A.X.signedMeasure_univ_eq_cylEnds (boundary_cyl_time hd)
    ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (m + 1) Θ') _

end SBLocalization

end Polyfold
