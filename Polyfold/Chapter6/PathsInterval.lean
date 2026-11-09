import Polyfold.Chapter3.UnitIntervalPolyfold
import Polyfold.Chapter6.OrientationSpace

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, pp. 263–276
(preprint: §6.5, pp. 220–230): **Theorems 6.6.11, 6.6.13 and 6.6.17 for sc-smooth paths
`φ : [0, 1] → X`** (preprint: Theorems 6.35, 6.37), and `X × [0, 1]` as an M-polyfold with
boundary.  Part of gap G.65 (decision D2: paths read on `ℝ`): rows V6.48 (Theorem 6.6.11),
V6.57 (Theorem 6.6.13, in part), V6.71 and V6.75 (Theorem 6.6.17 (3)).

# §6.6 on `[0, 1]`

## The text, paraphrased

(Theorem 6.6.11, p. 272) Every smooth `x` has an open neighbourhood `U` such that along every
sc-smooth path `φ : [0, 1] → U` an orientation of `DET(f, φ(0))` has a well-defined propagation
`φ_* o`, and two paths in `U` from the same start to the same end propagate alike.  (Theorem 6.6.13,
p. 273) The functor `Γ_f` takes the sc-smooth homotopy class `[φ]` of a path `φ : [0, 1] → X`
to a bijection `Or_{φ(0)}^f → Or_{φ(1)}^f`, equal to `φ_*` on paths in an orientable `U`.
(Theorem 6.6.17 (3), p. 275) For an sc-smooth path `φ : [0, 1] → X`, a continuous section
`α(t) = (φ(t), o_t)` of `φ*O_f` has `o_t` the local propagation of `o_{t₀}` for `t` near `t₀`.
The homotopies of Theorem 6.6.13 are maps on `[0, 1]²`, and Remark 6.6.19 works over
`X × [0, 1]`, an M-polyfold with boundary.

## What is formalized

* `Polyfold.unitReparam a b`: `r ↦ a + sin²(πr/2)(b − a)`, an sc-smooth map `ℝ → [0, 1]`
  (`isScSmoothMap_unitReparam`) from `a` (at `0`) to `b` (at `1`) with values in the segment
  `[a, b]` (`unitReparam_mem_uIcc`); `unitPath φ = φ ∘ unitReparam 0 1` is **the sc-smooth path
  on `ℝ` of a path `φ : [0, 1] → X`** (`isScSmoothMap_unitPath`), with the same end points and the
  same values on `[0, 1]`; `restrictUnitPath γ`, the restriction of a path `γ` on `ℝ` to `[0, 1]`
  (the reading of decision D2).
* **X × [0, 1]**: `isTame_prod_unitInterval` (for a tame `X`, `X × [0, 1]` with the product
  charts is tame and `d_{X × [0,1]}(x, t) = d_X(x) + d_{[0,1]}(t)`, so its boundary is
  `∂X × [0, 1] ∪ X × {0, 1}`); `unitSquarePolyfold`, `[0, 1]²`.
* **Theorem 6.6.11 on `[0, 1]`**: `IsPushI` (the push-forward along `φ : [0, 1] → X`, read as
  the push-forward `IsPush` along `unitPath φ`), `HasLocalPropagationI` (the local propagation
  property for paths on `[0, 1]`), `HasLocalPropagation.toInterval`, and
  **`theorem_6_6_11_interval`**.  `HasLocalPropagation.isPush_iff`: in a set with the local
  propagation property the push-forwards along a path depend only on its end points.  The
  reading does not depend on the reparametrization:
  `HasLocalPropagation.isPushI_iff` (for every sc-smooth `h : ℝ → [0, 1]` with `h(0) = 0`,
  `h(1) = 1`, the push-forwards along `φ ∘ h` are those along `φ`), and
  `HasLocalPropagation.isPush_iff_isPushI_restrict` (on the restriction of a path on `ℝ`, the
  reading of decision D2 gives the same push-forwards).
* **Theorem 6.6.13 on `[0, 1]`**: `orTransportI` (`Γ_f` on a path `φ : [0, 1] → X`, the
  transport along `unitPath φ`), `orTransportI_eq_of_homotopy` (**invariance under sc-smooth
  homotopies `[0, 1]² → X` with the end points fixed**), `orTransportI_star` (property (∗) on an
  open set with the local propagation property), `orTransportI_restrict` (on the restriction of a
  path `γ` on `ℝ`, it is `Γ_f([γ])` of decision D2, `orFunctorMap`).
* **Theorem 6.6.17 on `[0, 1]`**: `IsPropagationContinuousI` (property (3) for paths
  `φ : [0, 1] → X`), `isPropagationContinuousI_orTopology`, `IsPropagationContinuousI.toReal`
  (it implies the `ℝ`-form `IsPropagationContinuous`; with `orPush_eq_of_endpoints`),
  `existsUnique_orientationTopology_interval` (without (2)), and **`theorem_6_6_17_interval`**:
  there is exactly one Hausdorff topology on `O_f` with (1), (2) and (3) for paths on `[0, 1]`
  (under `HasConnectedSmoothNbhds`, as `theorem_6_6_17_2021`).

## What the text leaves implicit, and the choices made

* The push-forward along a path is built in the project from sections over `ℝ × X` near
  `[0, 1]` (`IsPush`, Proposition 6.6.3); along `φ : [0, 1] → X` it is read along the path
  `unitPath φ` on `ℝ`, which runs once through `φ` on `[0, 1]`.  In an open set with the local
  propagation property every sc-smooth reparametrization fixing the end points gives the same
  push-forwards (`isPushI_iff`), so the choice of `sin²(πr/2)` does not matter.
* "Local propagation of `o_{t₀}`" in (3) is the push-forward along the segment `φ|[t₀, t]`,
  run as the path `φ ∘ unitReparam t₀ t`, in an open set with the local propagation property
  containing `φ([t₀, t])`.
* Not covered here: the path category with `[0, 1]`-paths and the text's concatenation `β`
  (row V6.52), Proposition 6.6.3 (1′) and (3) and the families on `[0, 1]ⁿ` (row V6.32), and
  Remark 6.6.19 over `X × [0, 1]` (row V6.62); they keep the reading of decision D2.
-/

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### The reparametrization `r ↦ a + sin²(πr/2)(b − a)` -/

/-- `sin²(πr/2)`. -/
def sinSqHalf (r : ℝ) : ℝ := Real.sin (Real.pi / 2 * r) ^ 2

lemma contDiff_sinSqHalf : ContDiff ℝ ∞ sinSqHalf :=
  (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).pow 2

lemma sinSqHalf_mem (r : ℝ) : sinSqHalf r ∈ Icc (0 : ℝ) 1 :=
  ⟨sq_nonneg _, Real.sin_sq_le_one _⟩

@[simp] lemma sinSqHalf_zero : sinSqHalf 0 = 0 := by simp [sinSqHalf]

@[simp] lemma sinSqHalf_one : sinSqHalf 1 = 1 := by simp [sinSqHalf]

/-- `a + s(b − a) ∈ [0, 1]` for `a, b ∈ [0, 1]` and `s ∈ [0, 1]`. -/
lemma affine_mem_unitInterval (a b : unitInterval) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (a : ℝ) + s * ((b : ℝ) - a) ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨ha0, ha1⟩ := a.2
  obtain ⟨hb0, hb1⟩ := b.2
  obtain ⟨hs0, hs1⟩ := hs
  constructor <;> nlinarith

/-- `a + s(b − a)` lies in the segment `[a, b]` for `s ∈ [0, 1]`. -/
lemma affine_mem_uIcc (a b : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    a + s * (b - a) ∈ uIcc a b := by
  have : a + s * (b - a) = (1 - s) * a + s * b := by ring
  rw [this]
  exact (segment_eq_uIcc a b) ▸ ⟨1 - s, s, by linarith [hs.2], hs.1, by ring, rfl⟩

/-- **`r ↦ a + sin²(πr/2)(b − a)`**, a map `ℝ → [0, 1]` from `a` to `b`. -/
def unitReparam (a b : unitInterval) (r : Fin 1 → ℝ) : unitInterval :=
  ⟨(a : ℝ) + sinSqHalf (r 0) * ((b : ℝ) - a), affine_mem_unitInterval a b (sinSqHalf_mem _)⟩

theorem isScSmoothMap_unitReparam (a b : unitInterval) :
    (rnPolyfold 1).IsScSmoothMap unitIntervalPolyfold (unitReparam a b) :=
  isScSmoothMap_toUnitInterval (contDiff_const.add
    ((contDiff_sinSqHalf.comp (contDiff_apply ℝ ℝ (0 : Fin 1))).mul contDiff_const)) _

@[simp] lemma unitReparam_zero (a b : unitInterval) : unitReparam a b (pt1 0) = a :=
  Subtype.ext (by simp [unitReparam, pt1])

@[simp] lemma unitReparam_one (a b : unitInterval) : unitReparam a b (pt1 1) = b :=
  Subtype.ext (by simp [unitReparam, pt1])

lemma unitReparam_mem_uIcc (a b : unitInterval) (r : Fin 1 → ℝ) :
    (unitReparam a b r : ℝ) ∈ uIcc (a : ℝ) b :=
  affine_mem_uIcc _ _ (sinSqHalf_mem _)

lemma continuous_unitReparam (a b : unitInterval) : Continuous (unitReparam a b) :=
  continuousOn_univ.1 (isScSmoothMap_unitReparam a b).continuousOn

section Paths

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **The path on `ℝ` of a path `φ : [0, 1] → X`**: `r ↦ φ(sin²(πr/2))`. -/
def unitPath (φ : unitInterval → X) : (Fin 1 → ℝ) → X := φ ∘ unitReparam 0 1

theorem isScSmoothMap_unitPath {φ : unitInterval → X}
    (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) :
    (rnPolyfold 1).IsScSmoothMap PX (unitPath φ) :=
  hφ.comp (isScSmoothMap_unitReparam 0 1)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
@[simp] lemma unitPath_zero (φ : unitInterval → X) : unitPath φ (pt1 0) = φ 0 := by
  simp [unitPath]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
@[simp] lemma unitPath_one (φ : unitInterval → X) : unitPath φ (pt1 1) = φ 1 := by
  simp [unitPath]

/-- The restriction `t ↦ γ(t)` of a path `γ` on `ℝ` to `[0, 1]` (decision D2). -/
def restrictUnitPath (γ : (Fin 1 → ℝ) → X) : unitInterval → X := fun t => γ (pt1 (t : ℝ))

theorem isScSmoothMap_restrictUnitPath {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) :
    unitIntervalPolyfold.IsScSmoothMap PX (restrictUnitPath γ) :=
  hγ.restrictUnitInterval

end Paths

/-! ### `X × [0, 1]` and `[0, 1]²` -/

section Products

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)

/-- **`X × [0, 1]` is an M-polyfold with boundary, tame if `X` is** (the product charts,
`MPolyfold.prod`), with `d_{X × [0,1]}(x, t) = d_X(x) + d_{[0,1]}(t)`; with
`unitIntervalPolyfold_degIndex`, its boundary is `∂X × [0, 1] ∪ X × {0, 1}`. -/
theorem isTame_prod_unitInterval [ParacompactSpace (X × unitInterval)] (hX : PX.IsTame) :
    (PX.prod unitIntervalPolyfold).IsTame ∧ ∀ x t,
      (PX.prod unitIntervalPolyfold).degIndex (x, t) =
        PX.degIndex x + unitIntervalPolyfold.degIndex t :=
  MPolyfold.isTame_prod PX unitIntervalPolyfold hX unitIntervalPolyfold_isTame

include PX in
/-- `X × [0, 1]` is paracompact, so `PX.prod unitIntervalPolyfold` needs no further hypothesis. -/
theorem paracompactSpace_prod_unitInterval : ParacompactSpace (X × unitInterval) :=
  MPolyfold.paracompactSpace_prod PX unitIntervalPolyfold

/-- **`[0, 1]²`**, the domain of the homotopies of Theorem 6.6.13, as the product M-polyfold. -/
abbrev unitSquarePolyfold : MPolyfold (unitInterval × unitInterval) :=
  unitIntervalPolyfold.prod unitIntervalPolyfold

end Products

/-! ### Theorem 6.6.11 on `[0, 1]` -/

section Propagation

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

variable (f) in
/-- **`e` is a push-forward along the path `φ : [0, 1] → X`** (Theorem 6.6.11), read in the chart
`c`: a push-forward (`IsPush`) along the path `unitPath φ` on `ℝ`. -/
def IsPushI (hf : B.IsScFredholmSection f) (c : StrongBundleChart PX P) (hc : B.IsChart c)
    (φ : unitInterval → X) (hφ : ∀ t, φ t ∈ c.φ.source) {x₀ x₁ : X} (h₀ : φ 0 = x₀)
    (h₁ : φ 1 = x₁) (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet)
    (e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf) : Prop :=
  IsPush f hf c hc (unitPath φ) (fun _ _ => hφ _) ((unitPath_zero φ).trans h₀)
    ((unitPath_one φ).trans h₁) hx₀ hx₁ hs₀ hs₁ e

variable (f) in
/-- **The local propagation property of `U` in the chart `c` for paths on `[0, 1]`** (Theorem
6.6.11): along every sc-smooth path `φ : [0, 1] → U` with smooth end points there is a
push-forward, and push-forwards along two such paths with the same end points agree. -/
structure HasLocalPropagationI (hf : B.IsScFredholmSection f) (c : StrongBundleChart PX P)
    (hc : B.IsChart c) (U : Set X) : Prop where
  subset : U ⊆ c.φ.source
  exists_isPush : ∀ φ : unitInterval → X, unitIntervalPolyfold.IsScSmoothMap PX φ →
    ∀ (hφ : ∀ t, φ t ∈ U) {x₀ x₁ : X} (h₀ : φ 0 = x₀) (h₁ : φ 1 = x₁)
      (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source) (hs₀ : x₀ ∈ PX.smoothSet)
      (hs₁ : x₁ ∈ PX.smoothSet),
      ∃ e, IsPushI f hf c hc φ (fun t => subset (hφ t)) h₀ h₁ hx₀ hx₁ hs₀ hs₁ e
  eq : ∀ φ₀ φ₁ : unitInterval → X, unitIntervalPolyfold.IsScSmoothMap PX φ₀ →
    unitIntervalPolyfold.IsScSmoothMap PX φ₁ → ∀ (hφ₀ : ∀ t, φ₀ t ∈ U) (hφ₁ : ∀ t, φ₁ t ∈ U)
      {x₀ x₁ : X} (h₀₀ : φ₀ 0 = x₀) (h₀₁ : φ₀ 1 = x₁) (h₁₀ : φ₁ 0 = x₀) (h₁₁ : φ₁ 1 = x₁)
      (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source) (hs₀ : x₀ ∈ PX.smoothSet)
      (hs₁ : x₁ ∈ PX.smoothSet)
      (e₀ e₁ : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf),
      IsPushI f hf c hc φ₀ (fun t => subset (hφ₀ t)) h₀₀ h₀₁ hx₀ hx₁ hs₀ hs₁ e₀ →
      IsPushI f hf c hc φ₁ (fun t => subset (hφ₁ t)) h₁₀ h₁₁ hx₀ hx₁ hs₀ hs₁ e₁ → e₀ = e₁

variable {hf : B.IsScFredholmSection f} {c : StrongBundleChart PX P} {hc : B.IsChart c}
  {U : Set X}

/-- **The local propagation property for paths on `ℝ` gives it for paths on `[0, 1]`**: apply
it to the paths `unitPath φ`, which lie in `U` on `[0, 1]`. -/
theorem HasLocalPropagation.toInterval (h : HasLocalPropagation f hf c hc U) :
    HasLocalPropagationI f hf c hc U where
  subset := h.subset
  exists_isPush φ hφs hφ _ _ h₀ h₁ hx₀ hx₁ hs₀ hs₁ :=
    h.exists_isPush (unitPath φ) (isScSmoothMap_unitPath hφs) (fun _ _ => hφ _)
      ((unitPath_zero φ).trans h₀) ((unitPath_one φ).trans h₁) hx₀ hx₁ hs₀ hs₁
  eq φ₀ φ₁ hφ₀s hφ₁s hφ₀ hφ₁ _ _ h₀₀ h₀₁ h₁₀ h₁₁ hx₀ hx₁ hs₀ hs₁ e₀ e₁ he₀ he₁ :=
    h.eq (unitPath φ₀) (unitPath φ₁) (isScSmoothMap_unitPath hφ₀s)
      (isScSmoothMap_unitPath hφ₁s) (fun _ _ => hφ₀ _) (fun _ _ => hφ₁ _)
      ((unitPath_zero φ₀).trans h₀₀) ((unitPath_one φ₀).trans h₀₁)
      ((unitPath_zero φ₁).trans h₁₀) ((unitPath_one φ₁).trans h₁₁) hx₀ hx₁ hs₀ hs₁ e₀ e₁ he₀ he₁

/-- **In a set with the local propagation property the push-forwards along a path depend only on
its end points**: two sc-smooth paths on `ℝ` in `U` (on `[0, 1]`) with the same end points have the
same push-forwards. -/
theorem HasLocalPropagation.isPush_iff (h : HasLocalPropagation f hf c hc U)
    {γ γ' : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγ's : (rnPolyfold 1).IsScSmoothMap PX γ') (hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U)
    (hγ' : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ' q ∈ U) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (h₀' : γ' (pt1 0) = x₀) (h₁' : γ' (pt1 1) = x₁)
    (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet)
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf} :
    IsPush f hf c hc γ (fun q hq => h.subset (hγ q hq)) h₀ h₁ hx₀ hx₁ hs₀ hs₁ e ↔
      IsPush f hf c hc γ' (fun q hq => h.subset (hγ' q hq)) h₀' h₁' hx₀ hx₁ hs₀ hs₁ e := by
  constructor
  · intro he
    obtain ⟨e', he'⟩ := h.exists_isPush γ' hγ's hγ' h₀' h₁' hx₀ hx₁ hs₀ hs₁
    rwa [h.eq γ γ' hγs hγ's hγ hγ' h₀ h₁ h₀' h₁' hx₀ hx₁ hs₀ hs₁ e e' he he']
  · intro he
    obtain ⟨e', he'⟩ := h.exists_isPush γ hγs hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁
    rwa [h.eq γ' γ hγ's hγs hγ' hγ h₀' h₁' h₀ h₁ hx₀ hx₁ hs₀ hs₁ e e' he he']

/-- **The reading does not depend on the reparametrization**: in a set with the local propagation
property, for every sc-smooth `h : ℝ → [0, 1]` with `h(0) = 0` and `h(1) = 1`, the push-forwards
along `φ ∘ h` are those along `φ : [0, 1] → X` (`IsPushI`). -/
theorem HasLocalPropagation.isPushI_iff (hU : HasLocalPropagation f hf c hc U)
    {φ : unitInterval → X} (hφs : unitIntervalPolyfold.IsScSmoothMap PX φ) (hφ : ∀ t, φ t ∈ U)
    {h : (Fin 1 → ℝ) → unitInterval} (hh : (rnPolyfold 1).IsScSmoothMap unitIntervalPolyfold h)
    (hh0 : h (pt1 0) = 0) (hh1 : h (pt1 1) = 1) {x₀ x₁ : X} (h₀ : φ 0 = x₀) (h₁ : φ 1 = x₁)
    (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet)
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf} :
    IsPush f hf c hc (φ ∘ h) (fun _ _ => hU.subset (hφ _)) (by simp [hh0, h₀])
        (by simp [hh1, h₁]) hx₀ hx₁ hs₀ hs₁ e ↔
      IsPushI f hf c hc φ (fun t => hU.subset (hφ t)) h₀ h₁ hx₀ hx₁ hs₀ hs₁ e :=
  hU.isPush_iff (hφs.comp hh) (isScSmoothMap_unitPath hφs) (fun _ _ => hφ _) (fun _ _ => hφ _)
    _ _ _ _ hx₀ hx₁ hs₀ hs₁

/-- **The reading of decision D2 gives the same push-forwards**: in a set with the local
propagation property, the push-forwards along a path `γ` on `ℝ` are those along its restriction
`γ|[0, 1]` (`IsPushI`). -/
theorem HasLocalPropagation.isPush_iff_isPushI_restrict (hU : HasLocalPropagation f hf c hc U)
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγ : ∀ t : unitInterval, γ (pt1 (t : ℝ)) ∈ U) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet)
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf} :
    IsPush f hf c hc γ (fun q hq => hU.subset (forall_mem_of_forall_pt1_mem
        (fun t ht => hγ ⟨t, ht⟩) q hq)) h₀ h₁ hx₀ hx₁ hs₀ hs₁ e ↔
      IsPushI f hf c hc (restrictUnitPath γ) (fun t => hU.subset (hγ t)) h₀ h₁ hx₀ hx₁ hs₀ hs₁ e :=
  hU.isPush_iff hγs (isScSmoothMap_unitPath (isScSmoothMap_restrictUnitPath hγs))
    (forall_mem_of_forall_pt1_mem fun t ht => hγ ⟨t, ht⟩) (fun _ _ => hγ _) _ _ _ _ hx₀ hx₁ hs₀ hs₁

section Exists

variable [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

/-- **2021 Theorem 6.6.11, p. 272, for paths on `[0, 1]`** (preprint: Theorem 6.35): for a strong
bundle over a tame M-polyfold admitting sc-smooth bump functions and an sc-Fredholm section `f`
with tame germ data, every smooth `x` has an open neighbourhood `U`, in the domain of a chart
`c`, such that along every sc-smooth path `φ : [0, 1] → U` with smooth end points there is a
push-forward of the orientations of `DET(f, φ(0))`, and two such paths with the same end points
give the same push-forward.  From `theorem_6_35`. -/
theorem theorem_6_6_11_interval (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {x : X} (hx : x ∈ PX.smoothSet) :
    ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U : Set X), IsOpen U ∧ x ∈ U ∧
      HasLocalPropagationI f hf.toIsScFredholmSection c hc U := by
  obtain ⟨c, hc, U, hUo, hxU, hU⟩ := theorem_6_35 hX hbump hf hx
  exact ⟨c, hc, U, hUo, hxU, hU.toInterval⟩

end Exists

end Propagation

/-! ### Theorem 6.6.13 on `[0, 1]`: `Γ_f` along paths `φ : [0, 1] → X` -/

/-- `sin²(πr/2)` as a point of `[0, 1]`. -/
def sinSqUnit (r : ℝ) : unitInterval := ⟨sinSqHalf r, sinSqHalf_mem r⟩

@[simp] lemma sinSqUnit_zero : sinSqUnit 0 = 0 := Subtype.ext (by simp [sinSqUnit])

@[simp] lemma sinSqUnit_one : sinSqUnit 1 = 1 := Subtype.ext (by simp [sinSqUnit])

lemma unitReparam_zero_one (r : Fin 1 → ℝ) : unitReparam 0 1 r = sinSqUnit (r 0) :=
  Subtype.ext (by simp [unitReparam, sinSqUnit])

section Functor

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

variable (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)

include hX hbump hf hsec

/-- **`Γ_f` along a path `φ : [0, 1] → X`** (Theorem 6.6.13): the bijection
`Or_{φ(0)}^f ≃ Or_{φ(1)}^f` of the transport along `unitPath φ`. -/
def orTransportI {φ : unitInterval → X} (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ)
    {x₀ x₁ : X} (h₀ : φ 0 = x₀) (h₁ : φ 1 = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) :
    Orx f hf.toIsScFredholmSection x₀ hs₀ ≃ Orx f hf.toIsScFredholmSection x₁ hs₁ :=
  (orLocalTransport hX hbump hf hsec).transport (unitPath φ) (isScSmoothMap_unitPath hφ)
    ((unitPath_zero φ).trans h₀) ((unitPath_one φ).trans h₁) hs₀ hs₁

/-- **Property (∗) of Theorem 6.6.13 for paths on `[0, 1]`**: on an sc-smooth path
`φ : [0, 1] → U`, `U` open with the local propagation property in a chart `c`, `Γ_f` along `φ`
is every push-forward `e` along `φ` in `c` (`IsPushI`), read in the chosen charts. -/
theorem orTransportI_star {c : StrongBundleChart PX P} {hc : B.IsChart c} {U : Set X}
    (hU : HasLocalPropagation f hf.toIsScFredholmSection c hc U) (hUo : IsOpen U)
    {φ : unitInterval → X} (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) (hφU : ∀ t, φ t ∈ U)
    {x₀ x₁ : X} (h₀ : φ 0 = x₀) (h₁ : φ 1 = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf.toIsScFredholmSection ≃
      (chartPtOf c hc hx₁ hs₁).Or f hf.toIsScFredholmSection}
    (he : IsPushI f hf.toIsScFredholmSection c hc φ (fun t => hU.subset (hφU t)) h₀ h₁ hx₀ hx₁
      hs₀ hs₁ e) :
    orTransportI hX hbump hf hsec hφ h₀ h₁ hs₀ hs₁ =
      (toChartOr hf.toIsScFredholmSection hs₀ c hc hx₀).trans
        (e.trans (toChartOr hf.toIsScFredholmSection hs₁ c hc hx₁).symm) :=
  orLocalTransport_transport_eq hX hbump hf hsec hU hUo (isScSmoothMap_unitPath hφ)
    (fun _ _ => hφU _) _ _ hs₀ hs₁ hx₀ hx₁ he

/-- **`Γ_f` is invariant under sc-smooth homotopies `[0, 1]² → X` with the end points fixed**
(Theorem 6.6.13: `Γ_f` depends only on the class `[φ]`): if `H : [0, 1]² → X` is sc-smooth
(`unitSquarePolyfold`) with `H(0, ·) = φ₀`, `H(1, ·) = φ₁`, `H(·, 0) = φ₀(0)` and
`H(·, 1) = φ₀(1)`, then `Γ_f` along `φ₀` and along `φ₁` agree.  *Proof*:
`(τ, t) ↦ H(sin²(πτ/2), sin²(πt/2))` is a homotopy on `ℝ²` between `unitPath φ₀` and
`unitPath φ₁` (`transport_eq_of_isScHomotopyRel`). -/
theorem orTransportI_eq_of_homotopy {φ₀ φ₁ : unitInterval → X}
    (hφ₀ : unitIntervalPolyfold.IsScSmoothMap PX φ₀)
    (hφ₁ : unitIntervalPolyfold.IsScSmoothMap PX φ₁) {H : unitInterval × unitInterval → X}
    (hH : unitSquarePolyfold.IsScSmoothMap PX H) (hH0 : ∀ t, H (0, t) = φ₀ t)
    (hH1 : ∀ t, H (1, t) = φ₁ t) (hHs : ∀ τ, H (τ, 0) = φ₀ 0) (hHf : ∀ τ, H (τ, 1) = φ₀ 1)
    {x₀ x₁ : X} (h₀ : φ₀ 0 = x₀) (h₁ : φ₀ 1 = x₁) (h₀' : φ₁ 0 = x₀) (h₁' : φ₁ 1 = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    orTransportI hX hbump hf hsec hφ₀ h₀ h₁ hs₀ hs₁ =
      orTransportI hX hbump hf hsec hφ₁ h₀' h₁' hs₀ hs₁ := by
  set g : (Fin 2 → ℝ) → unitInterval × unitInterval :=
    fun q => (sinSqUnit (q 0), sinSqUnit (q 1)) with hg
  have hgs : (rnPolyfold 2).IsScSmoothMap unitSquarePolyfold g :=
    MPolyfold.IsScSmoothOn.prodMk
      (isScSmoothMap_toUnitInterval (contDiff_sinSqHalf.comp (contDiff_apply ℝ ℝ 0)) _)
      (isScSmoothMap_toUnitInterval (contDiff_sinSqHalf.comp (contDiff_apply ℝ ℝ 1)) _)
  have hΦ : IsScHomotopyRel PX (unitPath φ₀) (unitPath φ₁) (H ∘ g) :=
    { isScSmoothMap := hH.comp hgs
      zero := fun t _ => by
        simp only [Function.comp_apply, hg, unitPath, unitReparam_zero_one, pt2_apply_zero,
          pt2_apply_one, sinSqUnit_zero, hH0]
        rfl
      one := fun t _ => by
        simp only [Function.comp_apply, hg, unitPath, unitReparam_zero_one, pt2_apply_zero,
          pt2_apply_one, sinSqUnit_one, hH1]
        rfl
      start := fun τ _ => by
        simp only [Function.comp_apply, hg, unitPath, unitReparam_zero_one, pt2_apply_one,
          pt1_apply, sinSqUnit_zero, hHs]
      finish := fun τ _ => by
        simp only [Function.comp_apply, hg, unitPath, unitReparam_zero_one, pt2_apply_one,
          pt1_apply, sinSqUnit_one, hHf] }
  exact (orLocalTransport hX hbump hf hsec).transport_eq_of_isScHomotopyRel hΦ _ _ _ _ hs₀ hs₁

/-- **On the restriction of a path `γ` on `ℝ`, `Γ_f` is that of decision D2**: `Γ_f` along
`γ|[0, 1]` is `Γ_f([γ])` (`orFunctorMap`).  *Proof*: `(σ, t) ↦ γ((1 − σ) sin²(πt/2) + σt)` is a
homotopy on `ℝ²` with the end points fixed from `unitPath (γ|[0, 1])` to `γ`. -/
theorem orTransportI_restrict {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) :
    orTransportI hX hbump hf hsec (isScSmoothMap_restrictUnitPath hγ) h₀ h₁ hs₀ hs₁ =
      orFunctorMap hX hbump hf hsec (x := ⟨x₀, hs₀⟩) (y := ⟨x₁, hs₁⟩)
        (PathCat.homMk ⟨γ, hγ, h₀, h₁⟩) := by
  rw [orFunctorMap_mk]
  set H : (Fin 2 → ℝ) → X := fun q => γ (pt1 ((1 - q 0) * sinSqHalf (q 1) + q 0 * q 1)) with hH
  have hHs : (rnPolyfold 2).IsScSmoothMap PX H :=
    hγ.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pi.2 fun _ =>
      ((contDiff_const.sub (contDiff_apply ℝ ℝ 0)).mul
        (contDiff_sinSqHalf.comp (contDiff_apply ℝ ℝ 1))).add
        ((contDiff_apply ℝ ℝ 0).mul (contDiff_apply ℝ ℝ 1))))
  have hΦ : IsScHomotopyRel PX (unitPath (restrictUnitPath γ)) γ H :=
    { isScSmoothMap := hHs
      zero := fun t _ => by
        simp only [hH, unitPath, restrictUnitPath, Function.comp_apply, unitReparam_zero_one,
          pt2_apply_zero, pt2_apply_one, pt1_apply, sinSqUnit]
        congr 2; ring
      one := fun t _ => by
        simp only [hH, pt2_apply_zero, pt2_apply_one]
        congr 2; ring
      start := fun τ _ => by
        simp only [hH, unitPath, restrictUnitPath, Function.comp_apply, unitReparam_zero_one,
          pt2_apply_zero, pt2_apply_one, pt1_apply, sinSqUnit, sinSqHalf_zero]
        congr 2; ring
      finish := fun τ _ => by
        simp only [hH, unitPath, restrictUnitPath, Function.comp_apply, unitReparam_zero_one,
          pt2_apply_zero, pt2_apply_one, pt1_apply, sinSqUnit, sinSqHalf_one]
        congr 2; ring }
  exact (orLocalTransport hX hbump hf hsec).transport_eq_of_isScHomotopyRel hΦ _ hγ _ _ hs₀ hs₁

end Functor

/-! ### Theorem 6.6.17 on `[0, 1]` -/

section OrSpace

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **In a set with the local propagation property, `orPush` depends only on the end points**: two
sc-smooth paths in `U` (on `[0, 1]`) with the same end points have the same push-forward
(`HasLocalPropagation.isPush_iff`, `orPush_eq`). -/
theorem orPush_eq_of_endpoints {hf : B.IsScFredholmSection f} {U : Set X} (hU : IsPropagationNbhd f hf U)
    {γ γ' : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγ' : (rnPolyfold 1).IsScSmoothMap PX γ') (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U)
    (hγ'U : ∀ t ∈ Icc (0 : ℝ) 1, γ' (pt1 t) ∈ U) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (h₀' : γ' (pt1 0) = x₀) (h₁' : γ' (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    orPush hU γ hγ hγU h₀ h₁ hs₀ hs₁ = orPush hU γ' hγ' hγ'U h₀' h₁' hs₀ hs₁ := by
  obtain ⟨c, hc, -, hLP⟩ := id hU
  have hγ1 := forall_mem_of_forall_pt1_mem hγU
  have hγ2 := forall_mem_of_forall_pt1_mem hγ'U
  have hx₀ : x₀ ∈ c.φ.source := hLP.subset (h₀ ▸ hγ1 _ (pt1_mem_Icc ⟨le_rfl, zero_le_one⟩))
  have hx₁ : x₁ ∈ c.φ.source := hLP.subset (h₁ ▸ hγ1 _ (pt1_mem_Icc ⟨zero_le_one, le_rfl⟩))
  obtain ⟨e, he⟩ := hLP.exists_isPush γ hγ hγ1 h₀ h₁ hx₀ hx₁ hs₀ hs₁
  have he' := (hLP.isPush_iff hγ hγ' hγ1 hγ2 h₀ h₁ h₀' h₁' hx₀ hx₁ hs₀ hs₁).1 he
  rw [orPush_eq hU hγ hγU h₀ h₁ hs₀ hs₁ hLP hγ1 hx₀ hx₁ he,
    orPush_eq hU hγ' hγ'U h₀' h₁' hs₀ hs₁ hLP hγ2 hx₀ hx₁ he']

variable (f) in
/-- **The pull-back `φ*O_f` along a path `φ : [0, 1] → X`**: the pairs `(t, p) ∈ [0, 1] × O_f`
with `φ(t) = π_f(p)`. -/
def OrPullbackI (hf : B.IsScFredholmSection f) (φ : unitInterval → X) :
    Set (unitInterval × OrSpace f hf) :=
  {q | φ q.1 = PX.smoothVal q.2.1}

variable (f) in
/-- **Property (3) of 2021 Theorem 6.6.17 for paths on `[0, 1]`**, for a topology `t` on `O_f`:
for an sc-smooth path `φ : [0, 1] → X` and a continuous section `α(t) = (t, (φ(t), o_t))` of
`φ*O_f`, for `t` near `t₀` there is an open set `U ⊇ φ([t₀, t])` with the local propagation
property in which the push-forward along the segment `φ|[t₀, t]` (run as
`φ ∘ unitReparam t₀ t`) maps `o_{t₀}` to `o_t`. -/
def IsPropagationContinuousI (hf : B.IsScFredholmSection f)
    (t : TopologicalSpace (OrSpace f hf)) : Prop :=
  letI := t
  ∀ (φ : unitInterval → X) (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ)
    (α : unitInterval → OrPullbackI f hf φ), Continuous α → (∀ s, (α s).1.1 = s) →
    ∀ t₀ : unitInterval, ∀ᶠ t : unitInterval in 𝓝 t₀, ∃ (U : Set X)
      (hU : IsPropagationNbhd f hf U)
      (hseg : ∀ s : unitInterval, (s : ℝ) ∈ uIcc (t₀ : ℝ) t → φ s ∈ U)
      (h₀ : φ t₀ = PX.smoothVal (α t₀).1.2.1) (h₁ : φ t = PX.smoothVal (α t).1.2.1),
      orPush hU (φ ∘ unitReparam t₀ t) (hφ.comp (isScSmoothMap_unitReparam t₀ t))
        (fun _ _ => hseg _ (unitReparam_mem_uIcc t₀ t _))
        ((congrArg φ (unitReparam_zero t₀ t)).trans h₀)
        ((congrArg φ (unitReparam_one t₀ t)).trans h₁)
        (PX.smoothVal_mem _) (PX.smoothVal_mem _) (α t₀).1.2.2 = (α t).1.2.2

/-- **Property (3) for paths on `[0, 1]` implies it for paths on `ℝ`** (decision D2): the
restriction `φ|[0, 1]` of a path on `ℝ` is a path on `[0, 1]` with the same pull-back, and the
segment `φ|[t₀, t]` and `φ|[0,1] ∘ unitReparam t₀ t` have the same push-forward
(`orPush_eq_of_endpoints`). -/
theorem IsPropagationContinuousI.toReal {hf : B.IsScFredholmSection f}
    {t : TopologicalSpace (OrSpace f hf)} (h : IsPropagationContinuousI f hf t) :
    IsPropagationContinuous f hf t := by
  let := t
  intro φ hφ α hα hαs t₀
  let α' : unitInterval → OrPullbackI f hf (restrictUnitPath φ) := fun s => ⟨(α s).1, (α s).2⟩
  have hα' : Continuous α' := (continuous_subtype_val.comp hα).subtype_mk _
  filter_upwards [h (restrictUnitPath φ) (isScSmoothMap_restrictUnitPath hφ) α' hα' hαs t₀] with t
    ⟨U, hU, hseg, h₀, h₁, heq⟩
  have hseg' : ∀ s ∈ Icc (0 : ℝ) 1, segPath φ t₀ t (pt1 s) ∈ U := fun s hs =>
    hseg ⟨(t₀ : ℝ) + s * ((t : ℝ) - t₀), affine_mem_unitInterval t₀ t hs⟩ (affine_mem_uIcc _ _ hs)
  refine ⟨U, hU, hseg', (segPath_zero φ t₀ t).trans h₀, (segPath_one φ t₀ t).trans h₁, ?_⟩
  have key := orPush_eq_of_endpoints hU (isScSmoothMap_segPath hφ t₀ t)
    ((isScSmoothMap_restrictUnitPath hφ).comp (isScSmoothMap_unitReparam t₀ t)) hseg'
    (fun _ _ => hseg _ (unitReparam_mem_uIcc t₀ t _)) ((segPath_zero φ t₀ t).trans h₀)
    ((segPath_one φ t₀ t).trans h₁)
    ((congrArg (restrictUnitPath φ) (unitReparam_zero t₀ t)).trans h₀)
    ((congrArg (restrictUnitPath φ) (unitReparam_one t₀ t)).trans h₁)
    (PX.smoothVal_mem _) (PX.smoothVal_mem _)
  rw [key]
  exact heq

section Existence

variable [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

variable (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)

include hX hbump hf hsec

/-- **Property (3) for paths on `[0, 1]`** for the topology of `O_f` (`orTopology`): near `t₀`, a
continuous section of `φ*O_f` stays in one set `{(y, o_y)}` of a continuous orientation `o`, which
the transport carries along the segments `φ ∘ unitReparam t₀ t`. -/
theorem isPropagationContinuousI_orTopology :
    IsPropagationContinuousI f hf.toIsScFredholmSection
      (orTopology (orLocalTransport hX hbump hf hsec)) := by
  set L := orLocalTransport hX hbump hf hsec with hL
  let _ : TopologicalSpace (OrSpace f hf.toIsScFredholmSection) := orTopology L
  intro φ hφ α hα hαs t₀
  obtain ⟨U, o, ho, ⟨U', hU', hUU'⟩, hp⟩ := exists_isContOrOn L (α t₀).1.2
  have hφc : Continuous φ := continuousOn_univ.1 hφ.continuousOn
  have hev1 : ∀ᶠ t in 𝓝 t₀, (α t).1.2 ∈ orBasic U o :=
    (continuous_snd.comp (continuous_subtype_val.comp hα)).continuousAt
      ((isOpen_orBasic ho).mem_nhds hp)
  have hαφ : ∀ t : unitInterval, φ t = PX.smoothVal (α t).1.2.1 := fun t => by
    have := (α t).2
    change φ (α t).1.1 = PX.smoothVal (α t).1.2.1 at this
    rw [hαs] at this
    exact this
  have hφt₀ : φ t₀ ∈ U := by rw [hαφ]; exact hp.1
  -- near `t₀`, `φ([t₀, t]) ⊆ U`
  have hev2 : ∀ᶠ t : unitInterval in 𝓝 t₀,
      ∀ s : unitInterval, (s : ℝ) ∈ uIcc (t₀ : ℝ) t → φ s ∈ U := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (ho.1.preimage hφc) t₀ hφt₀
    refine Metric.eventually_nhds_iff.2 ⟨ε, hε, fun t ht s hs => hball ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    rw [Subtype.dist_eq, Real.dist_eq] at ht
    exact lt_of_le_of_lt (abs_sub_left_of_mem_uIcc hs) ht
  filter_upwards [hev1, hev2] with t ht hseg
  have h₀ : φ t₀ = PX.smoothVal (α t₀).1.2.1 := hαφ t₀
  have h₁ : φ t = PX.smoothVal (α t).1.2.1 := hαφ t
  have hsegU : ∀ r ∈ Icc (0 : ℝ) 1, (φ ∘ unitReparam t₀ t) (pt1 r) ∈ U := fun _ _ =>
    hseg _ (unitReparam_mem_uIcc t₀ t _)
  refine ⟨U', hU', fun s hs => hUU' (hseg s hs), h₀, h₁, ?_⟩
  have hγ := hφ.comp (isScSmoothMap_unitReparam t₀ t)
  have h₀' : (φ ∘ unitReparam t₀ t) (pt1 0) = PX.smoothVal (α t₀).1.2.1 :=
    (congrArg φ (unitReparam_zero t₀ t)).trans h₀
  have h₁' : (φ ∘ unitReparam t₀ t) (pt1 1) = PX.smoothVal (α t).1.2.1 :=
    (congrArg φ (unitReparam_one t₀ t)).trans h₁
  have hT := ho.2 _ hγ hsegU h₀' h₁' (PX.smoothVal_mem _) (PX.smoothVal_mem _)
  calc _ = L.transport _ hγ h₀' h₁' (PX.smoothVal_mem _) (PX.smoothVal_mem _) (α t₀).1.2.2 := by
          rw [L.transport_eq_push hU' _ (fun s hs => hUU' (hsegU s hs))]
          rfl
    _ = (α t).1.2.2 := by rw [hp.2, hT, ← ht.2]

/-- **2021 Theorem 6.6.17, p. 275, with property (3) for sc-smooth paths `φ : [0, 1] → X`**:
there is exactly one topology on `O_f` which is Hausdorff and has properties (1), (2) and (3)
(`IsPropagationContinuousI`); under `HasConnectedSmoothNbhds` (used for (2) only), as
`theorem_6_6_17_2021`.  Existence: `orTopology`; uniqueness: (3) for paths on `[0, 1]` gives (3)
for paths on `ℝ` (`IsPropagationContinuousI.toReal`), and `eq_orTopology_of`. -/
theorem theorem_6_6_17_interval (hC : PX.HasConnectedSmoothNbhds) :
    ∃! t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection),
      @T2Space _ t ∧ @IsLocalHomeomorph _ _ t _ (orProj f hf.toIsScFredholmSection) ∧
        HasTwoContSections f hf.toIsScFredholmSection t ∧
        IsPropagationContinuousI f hf.toIsScFredholmSection t :=
  ⟨orTopology (orLocalTransport hX hbump hf hsec),
    ⟨t2Space_orTopology _, isLocalHomeomorph_orProj _,
      hasTwoContSections_orTopology _ (fun _ hy => exists_two_orx _ hy hsec) hC,
      isPropagationContinuousI_orTopology hX hbump hf hsec⟩,
    fun _ ht => eq_orTopology_of hX hbump hf hsec ht.2.1 ht.2.2.2.toReal⟩

/-- **2021 Theorem 6.6.17 without property (2), for paths on `[0, 1]`**: exactly one Hausdorff
topology on `O_f` has properties (1) and (3) for paths on `[0, 1]`; no hypothesis on `X` beyond
those of Theorem 6.6.11. -/
theorem existsUnique_orientationTopology_interval :
    ∃! t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection), @T2Space _ t ∧
      @IsLocalHomeomorph _ _ t _ (orProj f hf.toIsScFredholmSection) ∧
      IsPropagationContinuousI f hf.toIsScFredholmSection t :=
  ⟨orTopology (orLocalTransport hX hbump hf hsec),
    ⟨t2Space_orTopology _, isLocalHomeomorph_orProj _,
      isPropagationContinuousI_orTopology hX hbump hf hsec⟩,
    fun _ ht => eq_orTopology_of hX hbump hf hsec ht.2.1 ht.2.2.toReal⟩

end Existence

end OrSpace

end Polyfold
