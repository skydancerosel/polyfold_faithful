import Polyfold.Chapter6.PropagationWellDefined

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
p. 227: the paragraph after **Theorem 6.35** and **Definition 6.36** (orientable neighbourhoods
and their two continuous orientations) *(book 2017: after Theorem 6.1, Definition 6.10; see
`BookConcordance.md`)*.

# Continuous orientations over an orientable neighbourhood

## The text, paraphrased

Fixing an orientation `o_x` of `DET(f, x)`, `o_y = φ_* o_x` for an sc-smooth path `φ` in `U` from
`x` to `y ∈ U_∞` does not depend on `φ`, and `ψ_* o_{y₁} = o_{y₂}` for every sc-smooth path `ψ`
from `y₁` to `y₂`.  (Definition 6.36) An open contractible neighbourhood `U(x)` on which the local
propagation construction can be carried out is an orientable neighbourhood of `(f, x)`; the two
possible families of orientations of `DET(f, y)`, `y ∈ U_∞`, with the propagation property are the
continuous orientations.  An orientable neighbourhood has precisely two continuous orientations.

## What is formalized

* `HasLocalPropagation.eq_trans`: push-forwards in `U` compose along concatenated paths
  (`concatPath`, `IsPush.split`).
* **Definition 6.36**: `IsContinuousOrientation` (orientations of `DET(f, y)`, `y ∈ V_∞`, carried
  into each other by the push-forwards along paths in `U`); `exists_two_isContinuousOrientation`
  (there are exactly two) and `exists_orientableNbhd` (every smooth point has such `V ⊆ U`).

## Reading

The neighbourhood `U` of Proposition 6.28 is not shown to be sc-smoothly contractible (see
`OrientableNbhd.lean`).  The paths from `x` to the points of a smaller neighbourhood `V` run in `U`
(`exists_nhds_scPath`), and the continuous orientations are defined over `V`, for paths in `U`.
"The propagation property" is read for all sc-smooth paths in `U` between smooth points of `V`.
-/

open Module Bundle Topology Set Filter

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### Proposition 6.32 and Theorem 6.35 -/

section Push

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **Push-forwards compose** (the paragraph after Theorem 6.35): for paths `γ₁` from `x₀` to
`x₁` and `γ₂` from `x₁` to `x₂` in `U`, a push-forward along any path in `U` from `x₀` to `x₂` is
the composite (`concatPath`, `IsPush.split`). -/
theorem HasLocalPropagation.eq_trans {hf : B.IsScFredholmSection f}
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {U : Set X}
    (hU : HasLocalPropagation f hf c hc U) {γ γ₁ γ₂ : (Fin 1 → ℝ) → X}
    (hγs : (rnPolyfold 1).IsScSmoothMap PX γ) (hγ₁s : (rnPolyfold 1).IsScSmoothMap PX γ₁)
    (hγ₂s : (rnPolyfold 1).IsScSmoothMap PX γ₂) (hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U)
    (hγ₁ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ₁ q ∈ U) (hγ₂ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ₂ q ∈ U)
    {x₀ x₁ x₂ : X} (h₀ : γ (pt1 0) = x₀) (h₂ : γ (pt1 1) = x₂) (h₁₀ : γ₁ (pt1 0) = x₀)
    (h₁₁ : γ₁ (pt1 1) = x₁) (h₂₀ : γ₂ (pt1 0) = x₁) (h₂₁ : γ₂ (pt1 1) = x₂)
    (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source) (hx₂ : x₂ ∈ c.φ.source)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) (hs₂ : x₂ ∈ PX.smoothSet)
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₂ hs₂).Or f hf}
    {e₁ : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf}
    {e₂ : (chartPtOf c hc hx₁ hs₁).Or f hf ≃ (chartPtOf c hc hx₂ hs₂).Or f hf}
    (he : IsPush f hf c hc γ (fun q hq => hU.subset (hγ q hq)) h₀ h₂ hx₀ hx₂ hs₀ hs₂ e)
    (he₁ : IsPush f hf c hc γ₁ (fun q hq => hU.subset (hγ₁ q hq)) h₁₀ h₁₁ hx₀ hx₁ hs₀ hs₁ e₁)
    (he₂ : IsPush f hf c hc γ₂ (fun q hq => hU.subset (hγ₂ q hq)) h₂₀ h₂₁ hx₁ hx₂ hs₁ hs₂ e₂) :
    e = e₁.trans e₂ := by
  have hpt : ∀ q : Fin 1 → ℝ, pt1 (q 0) = q := fun q => funext fun i => by
    rw [Subsingleton.elim i 0]; rfl
  have hIcc : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, q 0 ∈ Icc (0 : ℝ) 1 := fun q hq => ⟨hq.1 0, hq.2 0⟩
  -- the concatenation `γ₃` of `γ₁` and `γ₂`, a path in `U` from `x₀` to `x₂`
  have hγ₃s : (rnPolyfold 1).IsScSmoothMap PX (concatPath γ₁ γ₂) :=
    isScSmoothMap_concatPath hγ₁s hγ₂s (h₁₁.trans h₂₀.symm)
  have hγ₃t : ∀ t ∈ Icc (0 : ℝ) 1, concatPath γ₁ γ₂ (pt1 t) ∈ U :=
    concatPath_mem (fun t ht => hγ₁ _ (pt1_mem_Icc ht)) (fun t ht => hγ₂ _ (pt1_mem_Icc ht))
  have hγ₃U : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, concatPath γ₁ γ₂ q ∈ U := fun q hq =>
    hpt q ▸ hγ₃t _ (hIcc q hq)
  have h₃₀ : concatPath γ₁ γ₂ (pt1 0) = x₀ := concatPath_zero.trans h₁₀
  have h₃₁ : concatPath γ₁ γ₂ (pt1 1) = x₂ := concatPath_one.trans h₂₁
  obtain ⟨e₃, he₃⟩ := hU.exists_isPush _ hγ₃s hγ₃U h₃₀ h₃₁ hx₀ hx₂ hs₀ hs₂
  have hee₃ : e = e₃ := hU.eq γ _ hγs hγ₃s hγ hγ₃U h₀ h₂ h₃₀ h₃₁ hx₀ hx₂ hs₀ hs₂ e e₃ he he₃
  -- its two halves, paths in `U` from `x₀` to `x₁` and from `x₁` to `x₂`
  have hδ₁t : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, concatPath γ₁ γ₂ (pt1 (q 0 / 2)) ∈ U := fun q hq =>
    hγ₃t _ ⟨by linarith [(hIcc q hq).1], by linarith [(hIcc q hq).2]⟩
  have hδ₂t : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, concatPath γ₁ γ₂ (pt1 ((1 + q 0) / 2)) ∈ U :=
    fun q hq => hγ₃t _ ⟨by linarith [(hIcc q hq).1], by linarith [(hIcc q hq).2]⟩
  have hmid : concatPath γ₁ γ₂ (pt1 (1 / 2)) = x₁ := by
    rw [concatPath_of_le (s := pt1 (1 / 2)) le_rfl, pt1_apply,
      Real.smoothTransition.one_of_one_le (by norm_num), h₁₁]
  have h₀' : concatPath γ₁ γ₂ (pt1 ((pt1 0 : Fin 1 → ℝ) 0 / 2)) = x₀ := by
    rw [pt1_apply, zero_div]; exact h₃₀
  have h₁' : concatPath γ₁ γ₂ (pt1 ((pt1 1 : Fin 1 → ℝ) 0 / 2)) = x₁ := by
    rw [pt1_apply]; exact hmid
  have h₁'' : concatPath γ₁ γ₂ (pt1 ((1 + (pt1 0 : Fin 1 → ℝ) 0) / 2)) = x₁ := by
    rw [pt1_apply, add_zero]; exact hmid
  have h₂' : concatPath γ₁ γ₂ (pt1 ((1 + (pt1 1 : Fin 1 → ℝ) 0) / 2)) = x₂ := by
    rw [pt1_apply, show (1 + 1 : ℝ) / 2 = 1 by norm_num]; exact h₃₁
  obtain ⟨e₁', e₂', he₁', he₂', h₃⟩ := he₃.split hx₁ hs₁ (fun q hq => hU.subset (hδ₁t q hq))
    (fun q hq => hU.subset (hδ₂t q hq)) h₀' h₁' h₁'' h₂'
  have hδ₁s : (rnPolyfold 1).IsScSmoothMap PX fun q => concatPath γ₁ γ₂ (pt1 (q 0 / 2)) :=
    isScSmoothMap_reparam hγ₃s (κ := fun t => t / 2) (contDiff_id.div_const 2)
  have hδ₂s : (rnPolyfold 1).IsScSmoothMap PX fun q => concatPath γ₁ γ₂ (pt1 ((1 + q 0) / 2)) :=
    isScSmoothMap_reparam hγ₃s (κ := fun t => (1 + t) / 2)
      ((contDiff_const.add contDiff_id).div_const 2)
  have h₁ : e₁' = e₁ :=
    hU.eq _ γ₁ hδ₁s hγ₁s hδ₁t hγ₁ h₀' h₁' h₁₀ h₁₁ hx₀ hx₁ hs₀ hs₁ e₁' e₁ he₁' he₁
  have h₂ : e₂' = e₂ :=
    hU.eq _ γ₂ hδ₂s hγ₂s hδ₂t hγ₂ h₁'' h₂' h₂₀ h₂₁ hx₁ hx₂ hs₁ hs₂ e₂' e₂ he₂' he₂
  subst h₁ h₂
  exact hee₃.trans h₃

/-! ### Continuous orientations (Definition 6.36) -/

variable (f) in
/-- **Definition 6.36, continuous orientations**: orientations `o_y` of `DET(f, y)` for the smooth
points `y` of `V ⊆ U` such that `e(o_{y₁}) = o_{y₂}` for every push-forward `e` along an sc-smooth
path in `U` from `y₁` to `y₂`. -/
def IsContinuousOrientation (hf : B.IsScFredholmSection f) (c : StrongBundleChart PX P)
    (hc : B.IsChart c) {U V : Set X} (hUc : U ⊆ c.φ.source) (hVU : V ⊆ U)
    (o : ∀ y (hy : y ∈ V) (hys : y ∈ PX.smoothSet), (chartPtOf c hc (hUc (hVU hy)) hys).Or f hf) :
    Prop :=
  ∀ γ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ →
    ∀ (hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U) {y₁ y₂ : X} (hy₁ : y₁ ∈ V) (hy₂ : y₂ ∈ V)
      (hs₁ : y₁ ∈ PX.smoothSet) (hs₂ : y₂ ∈ PX.smoothSet) (h₀ : γ (pt1 0) = y₁)
      (h₁ : γ (pt1 1) = y₂) (e : (chartPtOf c hc (hUc (hVU hy₁)) hs₁).Or f hf ≃
        (chartPtOf c hc (hUc (hVU hy₂)) hs₂).Or f hf),
      IsPush f hf c hc γ (fun q hq => hUc (hγ q hq)) h₀ h₁ (hUc (hVU hy₁)) (hUc (hVU hy₂)) hs₁ hs₂
        e → e (o y₁ hy₁ hs₁) = o y₂ hy₂ hs₂

/-- **An orientable neighbourhood has precisely two continuous orientations** (Definition 6.36):
for `U` with the local propagation property and `V ⊆ U` whose smooth points are joined by
sc-smooth paths in `U`, with a smooth point in `V`. -/
theorem exists_two_isContinuousOrientation {hf : B.IsScFredholmSection f}
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {U V : Set X}
    (hU : HasLocalPropagation f hf c hc U) (hVU : V ⊆ U) {x : X} (hxV : x ∈ V)
    (hxs : x ∈ PX.smoothSet)
    (hpath : ∀ y₁ ∈ V, ∀ y₂ ∈ V, y₁ ∈ PX.smoothSet → y₂ ∈ PX.smoothSet →
      ∃ γ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ ∧ γ (pt1 0) = y₁ ∧
        γ (pt1 1) = y₂ ∧ ∀ t, γ t ∈ U)
    (hsec : B.HasScPlusSectionsThrough) :
    ∃ o₁ o₂ : ∀ y (hy : y ∈ V) (hys : y ∈ PX.smoothSet),
        (chartPtOf c hc (hU.subset (hVU hy)) hys).Or f hf,
      IsContinuousOrientation f hf c hc hU.subset hVU o₁ ∧
      IsContinuousOrientation f hf c hc hU.subset hVU o₂ ∧ o₁ ≠ o₂ ∧
      ∀ o, IsContinuousOrientation f hf c hc hU.subset hVU o → o = o₁ ∨ o = o₂ := by
  -- paths `γ_y` in `U` from `x` to `y` and push-forwards `E_y` along them
  choose γ hγs hγ0 hγ1 hγU using fun y (hy : y ∈ V) (hys : y ∈ PX.smoothSet) =>
    hpath x hxV y hy hxs hys
  choose E hE using fun y (hy : y ∈ V) (hys : y ∈ PX.smoothSet) =>
    hU.exists_isPush (γ y hy hys) (hγs y hy hys) (fun q _ => hγU y hy hys q) (hγ0 y hy hys)
      (hγ1 y hy hys) (hU.subset (hVU hxV)) (hU.subset (hVU hy)) hxs hys
  -- a push-forward along a path in `U` from `y₁` to `y₂` carries `E_{y₁}` to `E_{y₂}`
  have key : ∀ δ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX δ →
      ∀ (hδ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, δ q ∈ U) {y₁ y₂ : X} (hy₁ : y₁ ∈ V) (hy₂ : y₂ ∈ V)
        (hs₁ : y₁ ∈ PX.smoothSet) (hs₂ : y₂ ∈ PX.smoothSet) (h₀ : δ (pt1 0) = y₁)
        (h₁ : δ (pt1 1) = y₂) (e : (chartPtOf c hc (hU.subset (hVU hy₁)) hs₁).Or f hf ≃
          (chartPtOf c hc (hU.subset (hVU hy₂)) hs₂).Or f hf),
        IsPush f hf c hc δ (fun q hq => hU.subset (hδ q hq)) h₀ h₁ (hU.subset (hVU hy₁))
          (hU.subset (hVU hy₂)) hs₁ hs₂ e →
        ∀ o, e (E y₁ hy₁ hs₁ o) = E y₂ hy₂ hs₂ o := by
    intro δ hδs hδ y₁ y₂ hy₁ hy₂ hs₁ hs₂ h₀ h₁ e he o
    have h := hU.eq_trans (hγs y₂ hy₂ hs₂) (hγs y₁ hy₁ hs₁) hδs (fun q _ => hγU y₂ hy₂ hs₂ q)
      (fun q _ => hγU y₁ hy₁ hs₁ q) hδ (hγ0 y₂ hy₂ hs₂) (hγ1 y₂ hy₂ hs₂) (hγ0 y₁ hy₁ hs₁)
      (hγ1 y₁ hy₁ hs₁) h₀ h₁ (hU.subset (hVU hxV)) (hU.subset (hVU hy₁)) (hU.subset (hVU hy₂))
      hxs hs₁ hs₂ (hE y₂ hy₂ hs₂) (hE y₁ hy₁ hs₁) he
    exact (congrArg (fun F => F o) h).symm
  obtain ⟨a, b, hab, hall⟩ :=
    (chartPtOf c hc (hU.subset (hVU hxV)) hxs).exists_two_or hf hxs hsec
  have hcont : ∀ o', IsContinuousOrientation f hf c hc hU.subset hVU
      (fun y hy hys => E y hy hys o') :=
    fun o' δ hδs hδ _ _ hy₁ hy₂ hs₁ hs₂ h₀ h₁ e he => key δ hδs hδ hy₁ hy₂ hs₁ hs₂ h₀ h₁ e he o'
  refine ⟨fun y hy hys => E y hy hys a, fun y hy hys => E y hy hys b, hcont a, hcont b, ?_, ?_⟩
  · intro h
    exact hab ((E x hxV hxs).injective (congrFun (congrFun (congrFun h x) hxV) hxs))
  · -- a continuous orientation is determined by its value at `x`
    intro o ho
    have hoE : ∀ y hy hys, o y hy hys = E y hy hys (o x hxV hxs) := fun y hy hys =>
      (ho (γ y hy hys) (hγs y hy hys) (fun q _ => hγU y hy hys q) hxV hy hxs hys
        (hγ0 y hy hys) (hγ1 y hy hys) (E y hy hys) (hE y hy hys)).symm
    rcases hall (o x hxV hxs) with h | h
    · exact Or.inl (funext fun y => funext fun hy => funext fun hys =>
        (hoE y hy hys).trans (congrArg _ h))
    · exact Or.inr (funext fun y => funext fun hy => funext fun hys =>
        (hoE y hy hys).trans (congrArg _ h))

variable [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

/-- **Orientable neighbourhoods exist** (Theorem 6.35 and Definition 6.36): every smooth point `x`
has open `V ⊆ U` in the domain of a chart, `x ∈ V`, with `U` having the local propagation property
and exactly two continuous orientations over `V`. -/
theorem exists_orientableNbhd (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough) {x : X}
    (hx : x ∈ PX.smoothSet) :
    ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U V : Set X)
      (hU : HasLocalPropagation f hf.toIsScFredholmSection c hc U) (hVU : V ⊆ U),
      IsOpen U ∧ IsOpen V ∧ x ∈ V ∧
      ∃ o₁ o₂ : ∀ y (hy : y ∈ V) (hys : y ∈ PX.smoothSet),
          (chartPtOf c hc (hU.subset (hVU hy)) hys).Or f hf.toIsScFredholmSection,
        IsContinuousOrientation f hf.toIsScFredholmSection c hc hU.subset hVU o₁ ∧
        IsContinuousOrientation f hf.toIsScFredholmSection c hc hU.subset hVU o₂ ∧ o₁ ≠ o₂ ∧
        ∀ o, IsContinuousOrientation f hf.toIsScFredholmSection c hc hU.subset hVU o →
          o = o₁ ∨ o = o₂ := by
  obtain ⟨c, hc, U, hUo, hxU, hU⟩ := theorem_6_35 hX hbump hf hx
  obtain ⟨V, hVo, hxV, hVU, hpath⟩ := exists_nhds_scPath hc hUo hU.subset hxU
  exact ⟨c, hc, U, V, hU, hVU, hUo, hVo, hxV,
    exists_two_isContinuousOrientation hU hVU hxV hx hpath hsec⟩

end Push

end Polyfold
