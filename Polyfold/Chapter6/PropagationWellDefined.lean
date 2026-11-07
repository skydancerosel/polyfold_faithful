import Polyfold.Chapter6.PushData

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 224–227: **Proposition 6.32** (the push-forward does not depend on the choices),
**Lemma 6.33** (adding sections), **Lemma 6.34** (changing the section `s`) and **Theorem 6.35**
(local propagation, independent of the path) *(book 2017: Proposition 6.13, Lemmas 6.15–6.16,
Theorem 6.1; see `BookConcordance.md`)*.

# The push-forward of orientations is well defined

## The text, paraphrased

(Proposition 6.32) For `U` as in Proposition 6.28 and an sc-smooth path `φ : [0, 1] → U`, the
push-forward `o ↦ φ_* o` does not depend on the choices of `s` and `s₁, …, s_k`.  (Lemma 6.33)
Adding sc⁺-sections `s̄₁, …, s̄_l` does not change it: over the square, the kernel bundle at
`τ = 0` is `L ⊕ ℝˡ`, and the data at the end points vary continuously in `τ`.  (Lemma 6.34) For
two sections `s⁰, s¹` with `sⁱ(φ(t), t) = f(φ(t))`, the homotopy `s^τ = τ s¹ + (1 − τ) s⁰` with
sections `s^τ_j` satisfying (P) gives the same push-forward for all `τ`.  The proof of the
proposition: add sections on both sides to get the same number with (P) along the convex
homotopy.  For two paths `φ₀, φ₁` in `U` with the same end points, homotope them in `U`; with a
section `s(·, τ, t)` along the homotopy, every `φ_τ` gives the same push-forward.  (Theorem 6.35)
Hence every smooth `x` has an open sc-smoothly contractible `U(x)` such that the propagation
`o ↦ φ_* o` along sc-smooth paths in `U` is well defined and depends only on the end points.

## What is formalized

* **Proposition 6.32** (`proposition_6_32`): two push-forwards (`IsPush`) along the same sc-smooth
  path in the domain of a chart agree.  Lemma 6.33 is `IsStabKernels.push_append`, Lemma 6.34 the
  square argument `IsStabKernels.push_square`.
* `push_eq_of_homotopy`: push-forwards along the two edges `τ = 0, 1` of an sc-smooth homotopy in
  the domain of the chart, with the end points fixed and with a section as in Proposition 6.28
  (3), agree (the homotopy argument before Theorem 6.35).
* `HasLocalPropagation f hf c hc U`: push-forwards exist along sc-smooth paths in `U` and depend
  only on the end points; **Theorem 6.35** (`theorem_6_35`): every smooth point has such a `U`.
* Helpers for push-forwards: `IsStabKernels.congr_data`, `IsStabKernels.push_congr_data` (equal
  data, propositionally), `IsStabKernels.push_eq_of_prefix` (a family of sections containing
  `s₁, …, s_k` as its first `k` members gives the same push-forward, from `push_append`).
* Helpers for sections: `mk_sectionAdd`, `mk_sectionSmul`, `sectionAdd_sectionSmul_eq_left`,
  `sectionAdd_sectionSmul_eq_right`, `isZeroAt_sectionAdd_combo` (`f + (1 − τ)a + τb` vanishes
  where `f + a` and `f + b` do), `pullbackSlice_sectionAdd`, `pullbackSlice_sectionSmul`,
  `continuous_principal_pullbackSlice` (the values of an sc⁺-section of `π*P` at a point,
  read in a chart, are continuous in the parameter).
* Helpers for the linearization: `scDeriv_combo_apply` (the derivative of an affine combination)
  and `linAt_principal_combo` (`(f + (1 − τ)a + τb)'(x) = (1 − τ)(f + a)'(x) + τ(f + b)'(x)`).
* The square: `pt2_apply_zero`, `pt2_apply_one`, `pt1_apply_zero`, `pt2_mem_Icc`,
  `continuous_pt2`, the edges `sqEdge τ : t ↦ (τ, t)` and the paths `sqPath t : τ ↦ (τ, t)`.

## Reading

"Does not depend on the choices" is read as: any two data of `IsPush` along the same path give the
same push-forward.  In the proof the homotopy of Lemma 6.34 and the added sections of Lemma 6.33
are combined over one square: `S^τ = (1 − τ) S⁰ + τ S¹` and the sections
`(1 − τ) ŝ⁰ⱼ + τ ŝ¹ⱼ` (`j < k⁰ + k¹`, with `ŝⁱⱼ = sⁱⱼ` for `j < kⁱ` and `0` otherwise), followed by
the sections `C` of Lemma 6.29 on the square, which give property (P).  At `τ = 0` the sections
`s⁰` are the first `k⁰` members of the family, at `τ = 1` the sections `s¹` are the first `k¹`, so
Lemma 6.33 applies on both edges without reordering the sections; along the edges `t = 0, 1` the
operators `(f + S^τ)'(xᵢ)` are affine in `τ`.  The text's `U` is "sc-smoothly contractible";
Proposition 6.28 gives (1′) (two paths in `U` with the same end points are homotopic in `W`, see
`OrientableNbhd.lean`), which is what the proof of Theorem 6.35 uses; along the homotopy the
section of Proposition 6.28 (3) depends on the parameter only through the point, so the operators
at the fixed end points do not change.  The homotopy `Φ` of (1′) is `γᵢ` on the edges only for
`t ∈ [0, 1]`, while a datum of `IsPush` asks for `(f + S)(t, γ(t)) = 0` for `t` near `[0, 1]`; so
the proof passes through the reparametrized paths `γᵢ ∘ κ` (`κ` the smooth transition function,
with values in `[0, 1]`, `κ(0) = 0`, `κ(1) = 1`): `γᵢ` and `γᵢ ∘ κ` are joined by
`(σ, t) ↦ γᵢ((1 − σ)t + σκ(t))`, and `γ₀ ∘ κ`, `γ₁ ∘ κ` by `(τ, t) ↦ Φ(τ, κ(t))`, three
homotopies whose edges are exact for all `t`.
-/

open Module Bundle Topology Set Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### Push-forwards along equal data and along longer families of sections -/

namespace IsStabKernels

variable {Q : Type*} [TopologicalSpace Q] {c : StrongBundleChart PX P} {hc : B.IsChart c}

/-- Transport of stabilized kernels along equal data. -/
theorem congr_data {y y' : Q → X} {hy : ∀ q, y q ∈ c.φ.source} (hy' : ∀ q, y' q ∈ c.φ.source)
    {S S' : Q → X → Y} {k : ℕ} {s s' : Fin k → Q → X → Y}
    {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}
    (hΛ : IsStabKernels f c hc y hy S s Λ) (hyy : y = y') (hSS : S = S') (hss : s = s') :
    IsStabKernels f c hc y' hy' S' s' Λ := by
  subst hyy hSS hss; exact hΛ

variable [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]

/-- The push-forward depends only on the data (points, sections, family). -/
theorem push_congr_data {y y' : Q → X} {hy : ∀ q, y q ∈ c.φ.source}
    {hy' : ∀ q, y' q ∈ c.φ.source} {S S' : Q → X → Y} {k : ℕ} {s s' : Fin k → Q → X → Y}
    {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}
    (hΛ : IsStabKernels f c hc y hy S s Λ) (hΛ' : IsStabKernels f c hc y' hy' S' s' Λ)
    (hyy : y = y') (hSS : S = S') (hss : s = s')
    (hf : B.IsScFredholmSection f) (a b : Q) {x₀ x₁ : X} (ha : y a = x₀) (hb : y b = x₁)
    (ha' : y' a = x₀) (hb' : y' b = x₁) (hx₀ : x₀ ∈ PX.smoothSet) (hx₁ : x₁ ∈ PX.smoothSet)
    (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁) :
    hΛ.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ = hΛ'.push hf a b ha' hb' hx₀ hx₁ z₀ hz₀ z₁ hz₁ := by
  subst hyy hSS hss; rfl

/-- **Sections containing `s` as a prefix give the same push-forward** (`push_append`). -/
theorem push_eq_of_prefix [Nonempty Q] {y y' : Q → X} {hy : ∀ q, y q ∈ c.φ.source}
    {hy' : ∀ q, y' q ∈ c.φ.source} {S S' : Q → X → Y} {k n : ℕ} {s : Fin k → Q → X → Y}
    {s' : Fin n → Q → X → Y} {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}
    {Λ' : SubspaceFamily Q (c.φ.model.E 0 × (Fin n → ℝ))}
    (hΛ : IsStabKernels f c hc y hy S s Λ) (hΛ' : IsStabKernels f c hc y' hy' S' s' Λ')
    (hyy : y' = y) (hSS : S' = S) (hkn : k ≤ n) (hss : ∀ i : Fin k, s' (Fin.castLE hkn i) = s i)
    (hf : B.IsScFredholmSection f) (a b : Q) {x₀ x₁ : X} (ha : y a = x₀) (hb : y b = x₁)
    (ha' : y' a = x₀) (hb' : y' b = x₁) (hx₀ : x₀ ∈ PX.smoothSet) (hx₁ : x₁ ∈ PX.smoothSet)
    (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁) :
    hΛ'.push hf a b ha' hb' hx₀ hx₁ z₀ hz₀ z₁ hz₁ = hΛ.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  have hs' : s' = Fin.append s fun j => s' (Fin.natAdd k j) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; exact hss i
    · rw [Fin.append_right]
  have hΛ'' := hΛ'.congr_data hy hyy hSS hs'
  exact (push_congr_data hΛ' hΛ'' hyy hSS hs' hf a b ha' hb' ha hb hx₀ hx₁ z₀ hz₀ z₁
    hz₁).trans (hΛ.push_append hΛ'' hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁)

end IsStabKernels

/-! ### Sections: fibrewise computations -/

section Fibre

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `(g + s)(x)` in the fibre. -/
lemma mk_sectionAdd {g s : X → Y} (hg : IsSection P g) (hs : IsSection P s) (x : X) :
    (⟨sectionAdd P g s x, hg.sectionAdd hs x⟩ : P ⁻¹' {x}) = ⟨g x, hg x⟩ + ⟨s x, hs x⟩ :=
  Subtype.ext (sectionAdd_apply hg hs x)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `(a·s)(x)` in the fibre. -/
lemma mk_sectionSmul {a : X → ℝ} {s : X → Y} (hs : IsSection P s) (x : X) :
    (⟨sectionSmul P a s x, hs.sectionSmul x⟩ : P ⁻¹' {x}) = a x • ⟨s x, hs x⟩ :=
  Subtype.ext (sectionSmul_apply hs x)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `α·a + β·b` with `α = 1`, `β = 0` is `a`. -/
lemma sectionAdd_sectionSmul_eq_left {a b : X → Y} (ha : IsSection P a) (hb : IsSection P b)
    {α β : ℝ} (hα : α = 1) (hβ : β = 0) :
    sectionAdd P (sectionSmul P (fun _ => α) a) (sectionSmul P (fun _ => β) b) = a := by
  subst hα hβ
  funext x
  have h := mk_sectionAdd (ha.sectionSmul (f := fun _ => 1))
    (hb.sectionSmul (f := fun _ => 0)) x
  rw [mk_sectionSmul ha, mk_sectionSmul hb, one_smul, zero_smul, add_zero] at h
  exact congrArg Subtype.val h

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `α·a + β·b` with `α = 0`, `β = 1` is `b`. -/
lemma sectionAdd_sectionSmul_eq_right {a b : X → Y} (ha : IsSection P a) (hb : IsSection P b)
    {α β : ℝ} (hα : α = 0) (hβ : β = 1) :
    sectionAdd P (sectionSmul P (fun _ => α) a) (sectionSmul P (fun _ => β) b) = b := by
  subst hα hβ
  funext x
  have h := mk_sectionAdd (ha.sectionSmul (f := fun _ => 0))
    (hb.sectionSmul (f := fun _ => 1)) x
  rw [mk_sectionSmul ha, mk_sectionSmul hb, one_smul, zero_smul, zero_add] at h
  exact congrArg Subtype.val h

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `g + ((1 − τ)·a + τ·b)` vanishes where `g + a` and `g + b` do. -/
lemma isZeroAt_sectionAdd_combo {g a b : X → Y} (hg : IsSection P g) (ha : IsSection P a)
    (hb : IsSection P b) {x : X} (h₀ : IsZeroAt P (sectionAdd P g a) x)
    (h₁ : IsZeroAt P (sectionAdd P g b) x) (τ : ℝ) :
    IsZeroAt P (sectionAdd P g (sectionAdd P (sectionSmul P (fun _ => 1 - τ) a)
      (sectionSmul P (fun _ => τ) b))) x := by
  have e₀ := h₀.mk_eq_zero (hg.sectionAdd ha)
  have e₁ := h₁.mk_eq_zero (hg.sectionAdd hb)
  rw [mk_sectionAdd hg ha] at e₀
  rw [mk_sectionAdd hg hb] at e₁
  have hc := (ha.sectionSmul (f := fun _ => 1 - τ)).sectionAdd (hb.sectionSmul (f := fun _ => τ))
  have h := mk_sectionAdd hg hc x
  rw [mk_sectionAdd (ha.sectionSmul (f := fun _ => 1 - τ)) (hb.sectionSmul (f := fun _ => τ)) x,
    mk_sectionSmul ha, mk_sectionSmul hb] at h
  have h' : (⟨g x, hg x⟩ : P ⁻¹' {x}) + ((1 - τ) • ⟨a x, ha x⟩ + τ • ⟨b x, hb x⟩) =
      (1 - τ) • ((⟨g x, hg x⟩ : P ⁻¹' {x}) + ⟨a x, ha x⟩) + τ • (⟨g x, hg x⟩ + ⟨b x, hb x⟩) := by
    module
  rw [h', e₀, e₁, smul_zero, smul_zero, add_zero] at h
  exact congrArg Subtype.val h

end Fibre

/-! ### Slices of sums and products -/

section Slices

variable {n : ℕ}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The slice of a sum is the sum of the slices. -/
lemma pullbackSlice_sectionAdd {S₁ S₂ : (Fin n → ℝ) × X → pullbackSpace P Prod.snd}
    (h₁ : IsSection (pullbackProj P Prod.snd) S₁) (h₂ : IsSection (pullbackProj P Prod.snd) S₂)
    (t : Fin n → ℝ) :
    pullbackSlice (sectionAdd (pullbackProj P Prod.snd) S₁ S₂) t =
      sectionAdd P (pullbackSlice S₁ t) (pullbackSlice S₂ t) := by
  funext x
  set e := pullbackFiberEquiv P (Prod.snd : (Fin n → ℝ) × X → X) (t, x) with he
  have e1 : e ⟨S₁ (t, x), h₁ (t, x)⟩ = ⟨pullbackSlice S₁ t x, h₁.pullbackSlice t x⟩ :=
    Subtype.ext rfl
  have e2 : e ⟨S₂ (t, x), h₂ (t, x)⟩ = ⟨pullbackSlice S₂ t x, h₂.pullbackSlice t x⟩ :=
    Subtype.ext rfl
  have e3 := pullbackFiberEquiv_add P (Prod.snd : (Fin n → ℝ) × X → X) (t, x)
    ⟨S₁ (t, x), h₁ (t, x)⟩ ⟨S₂ (t, x), h₂ (t, x)⟩
  rw [e1, e2] at e3
  change (sectionAdd (pullbackProj P Prod.snd) S₁ S₂ (t, x)).1.2 = _
  rw [sectionAdd_apply h₁ h₂, sectionAdd_apply (h₁.pullbackSlice t) (h₂.pullbackSlice t)]
  exact congrArg Subtype.val e3

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- The slice of `a·S` is `a(t, ·)·S(t, ·)`. -/
lemma pullbackSlice_sectionSmul {a : (Fin n → ℝ) × X → ℝ}
    {S₁ : (Fin n → ℝ) × X → pullbackSpace P Prod.snd}
    (h₁ : IsSection (pullbackProj P Prod.snd) S₁) (t : Fin n → ℝ) :
    pullbackSlice (sectionSmul (pullbackProj P Prod.snd) a S₁) t =
      sectionSmul P (fun x => a (t, x)) (pullbackSlice S₁ t) := by
  funext x
  set e := pullbackFiberEquiv P (Prod.snd : (Fin n → ℝ) × X → X) (t, x) with he
  have e1 : e ⟨S₁ (t, x), h₁ (t, x)⟩ = ⟨pullbackSlice S₁ t x, h₁.pullbackSlice t x⟩ :=
    Subtype.ext rfl
  have e3 := pullbackFiberEquiv_smul P (Prod.snd : (Fin n → ℝ) × X → X) (t, x) (a (t, x))
    ⟨S₁ (t, x), h₁ (t, x)⟩
  rw [e1] at e3
  change (sectionSmul (pullbackProj P Prod.snd) a S₁ (t, x)).1.2 = _
  rw [sectionSmul_apply h₁, sectionSmul_apply (h₁.pullbackSlice t)]
  exact congrArg Subtype.val e3

end Slices

/-! ### The linearization along the convex homotopy -/

section Lin

open StrongRetr

/-- **The derivative of an affine combination**: if `g = a·g₀ + b·g₁` on `U`, then
`Dg(z) = a·Dg₀(z) + b·Dg₁(z)` (uniqueness of the derivative within `U₁`). -/
theorem scDeriv_combo_apply {E F : ScBanach} {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    {g g₀ g₁ : E 0 → F 0} (hg : IsSc1 U g) (hg₀ : IsSc1 U g₀) (hg₁ : IsSc1 U g₁) (a b : ℝ)
    (heq : ∀ u ∈ U, g u = a • g₀ u + b • g₁ u) {z : E 1} (hz : z ∈ E.lvlSet U 1) (v : E 0) :
    scDeriv U g z v = a • scDeriv U g₀ z v + b • scDeriv U g₁ z v := by
  have d := hg.isSc1With_scDeriv.hasFDerivWithinAt z hz
  have d₀ := hg₀.isSc1With_scDeriv.hasFDerivWithinAt z hz
  have d₁ := hg₁.isSc1With_scDeriv.hasFDerivWithinAt z hz
  set L : E 0 →L[ℝ] F 0 := a • scDeriv U g₀ z + b • scDeriv U g₁ z with hL
  have d₂ : HasFDerivWithinAt (g ∘ E.toBase 1) (L.comp (E.toBase 1)) (E.lvlSet U 1) z := by
    have := (d₀.const_smul a).add (d₁.const_smul b)
    refine (this.congr_fderiv ?_).congr (fun y hy => ?_) ?_
    · ext w
      simp [hL]
    · exact heq _ hy
    · exact heq _ hz
  have heq' := ContinuousLinearMap.ext_of_comp_toBase_one
    ((hU.isScDomain.uniqueDiffWithinAt 1 z hz).eq d d₂)
  rw [heq', hL]
  rfl

/-- **The linearization along the convex homotopy is affine**:
`(f + (1 − τ)a + τb)'(x) = (1 − τ)(f + a)'(x) + τ(f + b)'(x)`. -/
theorem linAt_principal_combo (hf : B.IsScSmoothSection f) {a b : X → Y}
    (ha : B.IsScPlusSection a) (hb : B.IsScPlusSection b) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z ∈ c.U) (τ : ℝ) :
    linAt c.U c.R (c.principal (sectionAdd P f (sectionAdd P (sectionSmul P (fun _ => 1 - τ) a)
        (sectionSmul P (fun _ => τ) b)))) z =
      (1 - τ) • linAt c.U c.R (c.principal (sectionAdd P f a)) z +
        τ • linAt c.U c.R (c.principal (sectionAdd P f b)) z := by
  have hab : B.IsScPlusSection (sectionAdd P (sectionSmul P (fun _ => 1 - τ) a)
      (sectionSmul P (fun _ => τ) b)) :=
    (ha.smul_left (isScSmoothMap_real_const _)).add (hb.smul_left (isScSmoothMap_real_const _))
  ext v
  simp only [linAt_apply, add_apply, smul_apply]
  refine scDeriv_combo_apply c.relOpen ((hf.sectionAdd hab).isSc1_principal_comp_r hc)
    ((hf.sectionAdd ha).isSc1_principal_comp_r hc) ((hf.sectionAdd hb).isSc1_principal_comp_r hc)
    (1 - τ) τ (fun u hu => ?_) hz v
  have hO := c.r_mem_O hu
  simp only [Function.comp_apply]
  rw [c.principal_sectionAdd hf.1 hab.1 hO, c.principal_sectionAdd hf.1 ha.1 hO,
    c.principal_sectionAdd hf.1 hb.1 hO,
    c.principal_sectionAdd (ha.1.sectionSmul) (hb.1.sectionSmul) hO,
    principal_sectionSmul_const c ha.1 _ hO, principal_sectionSmul_const c hb.1 _ hO]
  module

end Lin

/-! ### Continuity of the values of sections along the parameter -/

section Cont

variable {n : ℕ} [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **The values of an sc⁺-section of `π*P` at a point vary continuously with the parameter**,
read in a chart (`IsScPlusSection.continuousOn_source` in the product chart). -/
theorem continuous_principal_pullbackSlice
    {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection G)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {x₀ : X} (hx₀ : x₀ ∈ c.φ.source) :
    Continuous fun q : Fin n → ℝ => c.principal (pullbackSlice G q) (c.φ x₀) := by
  set pc := (PullbackChartData.ofProd c 0).toChart (G (0, x₀)) with hpc
  have hpcc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsChart pc :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc _
  have hcont := hG.continuousOn_source hpcc
  have h1 : Continuous fun q : Fin n → ℝ => G (q, x₀) :=
    hcont.comp_continuous (continuous_id.prodMk continuous_const) fun q => ⟨mem_univ _, hx₀⟩
  have h2 : Continuous fun q : Fin n → ℝ => pc (G (q, x₀)) := by
    refine pc.continuousOn_toFun.comp_continuous h1 fun q => ?_
    change (G (q, x₀)).1.1 ∈ pc.φ.source
    rw [show (G (q, x₀)).1.1 = (q, x₀) from hG.1 (q, x₀)]
    exact ⟨mem_univ _, hx₀⟩
  refine (continuous_snd.comp h2).congr fun q => ?_
  change (c (G (q, x₀)).1.2).2 = (c (G (q, c.φ.symm (c.φ x₀))).1.2).2
  rw [c.φ.symm_apply_apply hx₀]

end Cont

/-! ### The square `[0, 1]²` -/

section Square

@[simp] lemma pt2_apply_zero (τ t : ℝ) : pt2 τ t 0 = τ := by simp [pt2]

@[simp] lemma pt2_apply_one (τ t : ℝ) : pt2 τ t 1 = t := by simp [pt2]

lemma pt1_apply_zero (p : Fin 1 → ℝ) : pt1 (p 0) = p :=
  funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl

lemma pt2_mem_Icc {τ t : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    pt2 τ t ∈ Icc (0 : Fin 2 → ℝ) 1 :=
  ⟨fun i => by fin_cases i <;> simp [hτ.1, ht.1], fun i => by fin_cases i <;> simp [hτ.2, ht.2]⟩

lemma continuous_pt2 : Continuous fun p : ℝ × ℝ => pt2 p.1 p.2 :=
  continuous_pi fun i => by
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, pt2_apply_zero,
      pt2_apply_one] <;> fun_prop

/-- The edge `t ↦ (τ, t)` of the square. -/
def sqEdge (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    C(Icc (0 : Fin 1 → ℝ) 1, Icc (0 : Fin 2 → ℝ) 1) :=
  ⟨fun t => ⟨pt2 τ (t.1 0), pt2_mem_Icc hτ ⟨t.2.1 0, t.2.2 0⟩⟩,
    (continuous_pt2.comp (continuous_const.prodMk
      ((continuous_apply 0).comp continuous_subtype_val))).subtype_mk _⟩

/-- The path `τ ↦ (τ, t)` in the square. -/
def sqPath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Path (⟨pt2 0 t, pt2_mem_Icc (left_mem_Icc.2 zero_le_one) ht⟩ : Icc (0 : Fin 2 → ℝ) 1)
      ⟨pt2 1 t, pt2_mem_Icc (right_mem_Icc.2 zero_le_one) ht⟩ where
  toFun τ := ⟨pt2 τ t, pt2_mem_Icc τ.2 ht⟩
  continuous_toFun :=
    (continuous_pt2.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _
  source' := rfl
  target' := rfl

end Square
/-! ### Proposition 6.32 and Theorem 6.35 -/

section Push

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

variable [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

/-- **Proposition 6.32**: the push-forward along an sc-smooth path in the domain of a chart does
not depend on the choices (with Lemmas 6.33 and 6.34). -/
theorem proposition_6_32 (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet)
    {e e' : (chartPtOf c hc hx₀ hs₀).Or f hf.toIsScFredholmSection ≃
      (chartPtOf c hc hx₁ hs₁).Or f hf.toIsScFredholmSection}
    (he : IsPush f hf.toIsScFredholmSection c hc γ hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁ e)
    (he' : IsPush f hf.toIsScFredholmSection c hc γ hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁ e') : e = e' := by
  obtain ⟨Sa, hSa, hza, ka, sa, hsa, Λa, hΛa, rfl⟩ := he
  obtain ⟨Sb, hSb, hzb, kb, sb, hsb, Λb, hΛb, rfl⟩ := he'
  have hfs := hf.isScSmooth
  -- the square: `Φ(τ, t) = γ(t)`
  set A : (Fin 2 → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
    ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj 1 with hAdef
  have hA : ∀ τ t, A (pt2 τ t) + 0 = pt1 t := fun τ t => by
    funext i; simp [hAdef, pt1]
  have hAI : MapsTo (fun q => A q + 0) (Icc (0 : Fin 2 → ℝ) 1) (Icc (0 : Fin 1 → ℝ) 1) :=
    fun q hq => ⟨fun _ => by simpa [hAdef] using hq.1 1, fun _ => by simpa [hAdef] using hq.2 1⟩
  have hAc : Continuous fun q => A q + 0 := A.continuous.add continuous_const
  set Φ : (Fin 2 → ℝ) → X := fun q => γ (A q + 0) with hΦdef
  have hΦs : (rnPolyfold 2).IsScSmoothMap PX Φ :=
    hγs.comp (isScSmoothMap_rn_rn_of_contDiff (A.contDiff.add contDiff_const))
  have hΦc : ∀ q ∈ Icc (0 : Fin 2 → ℝ) 1, Φ q ∈ c.φ.source := fun q hq => hγ _ (hAI hq)
  -- the convex homotopy `S^τ = (1 − τ)·S⁰ + τ·S¹`
  set β₀ : (Fin 2 → ℝ) × X → ℝ := fun p => 1 - p.1 0 with hβ₀def
  set β₁ : (Fin 2 → ℝ) × X → ℝ := fun p => p.1 0 with hβ₁def
  have hβ₀ : ((rnPolyfold 2).prod PX).IsScSmoothMap realPolyfold β₀ :=
    (isScSmoothMap_rn_real_of_contDiff (contDiff_const.sub (contDiff_apply ℝ ℝ 0))).comp
      (MPolyfold.isScSmoothMap_fst (rnPolyfold 2) PX)
  have hβ₁ : ((rnPolyfold 2).prod PX).IsScSmoothMap realPolyfold β₁ :=
    (isScSmoothMap_rn_real_of_contDiff (contDiff_apply ℝ ℝ 0)).comp
      (MPolyfold.isScSmoothMap_fst (rnPolyfold 2) PX)
  set comb : ((Fin 2 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 2 → ℝ) × X → X)) →
      ((Fin 2 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 2 → ℝ) × X → X)) →
      (Fin 2 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 2 → ℝ) × X → X) :=
    fun G H => sectionAdd (pullbackProj P Prod.snd) (sectionSmul (pullbackProj P Prod.snd) β₀ G)
      (sectionSmul (pullbackProj P Prod.snd) β₁ H) with hcombdef
  have hcomb : ∀ {G H},
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 2) PX)).IsScPlusSection G →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 2) PX)).IsScPlusSection H →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 2) PX)).IsScPlusSection (comb G H) :=
    fun hG hH => (hG.smul_left hβ₀).add (hH.smul_left hβ₁)
  have hcombs : ∀ {G H : (Fin 2 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 2 → ℝ) × X → X)},
      IsSection (pullbackProj P Prod.snd) G → IsSection (pullbackProj P Prod.snd) H → ∀ q,
      pullbackSlice (comb G H) q = sectionAdd P (sectionSmul P (fun _ => 1 - q 0)
        (pullbackSlice G q)) (sectionSmul P (fun _ => q 0) (pullbackSlice H q)) := by
    intro G H hG hH q
    rw [hcombdef, pullbackSlice_sectionAdd hG.sectionSmul hH.sectionSmul,
      pullbackSlice_sectionSmul hG, pullbackSlice_sectionSmul hH]
  set Ssq := comb (reparamSection (fun q => A q + 0) Sa hSa.1)
    (reparamSection (fun q => A q + 0) Sb hSb.1) with hSsqdef
  have hSsq : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 2) PX)).IsScPlusSection Ssq :=
    hcomb (hSa.reparam A 0) (hSb.reparam A 0)
  have hslice : ∀ q, pullbackSlice Ssq q = sectionAdd P (sectionSmul P (fun _ => 1 - q 0)
      (pullbackSlice Sa (A q + 0))) (sectionSmul P (fun _ => q 0) (pullbackSlice Sb (A q + 0))) :=
    hcombs (hSa.reparam A 0).1 (hSb.reparam A 0).1
  -- `f + S^τ` vanishes along `Φ` near the square
  have hzsq : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin 2 → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) Ssq) (q, Φ q) := by
    have hT := hAc.tendsto_nhdsSet hAI
    filter_upwards [hT.eventually hza, hT.eventually hzb] with q ha hb
    rw [isZeroAt_pullback_iff_pullbackSlice ((isSection_pullbackLift _).sectionAdd hSa.1),
      pullbackSlice_sectionAdd_paramLift hfs.1 hSa.1] at ha
    rw [isZeroAt_pullback_iff_pullbackSlice ((isSection_pullbackLift _).sectionAdd hSb.1),
      pullbackSlice_sectionAdd_paramLift hfs.1 hSb.1] at hb
    rw [isZeroAt_pullback_iff_pullbackSlice ((isSection_pullbackLift _).sectionAdd hSsq.1),
      pullbackSlice_sectionAdd_paramLift hfs.1 hSsq.1, hslice q]
    exact isZeroAt_sectionAdd_combo hfs.1 (hSa.1.pullbackSlice _) (hSb.1.pullbackSlice _) ha hb _
  -- Lemma 6.29 on the square
  obtain ⟨m, C, hC, hGP⟩ := lemma_6_29 hX hbump hf hΦs hSsq hzsq
  -- the sections `ŝ⁰_j`, `ŝ¹_j` (zero beyond `k⁰`, `k¹`) and `u = ((1 − τ)ŝ⁰ + τŝ¹) ++ C`
  set sa' : Fin (ka + kb) → (Fin 2 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 2 → ℝ) × X → X) :=
    fun j => if h : (j : ℕ) < ka then reparamSection (fun q => A q + 0) (sa ⟨j, h⟩) (hsa _).1
      else fiberZero (pullbackProj P Prod.snd) with hsa'def
  set sb' : Fin (ka + kb) → (Fin 2 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 2 → ℝ) × X → X) :=
    fun j => if h : (j : ℕ) < kb then reparamSection (fun q => A q + 0) (sb ⟨j, h⟩) (hsb _).1
      else fiberZero (pullbackProj P Prod.snd) with hsb'def
  have hsa' : ∀ j, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 2) PX)).IsScPlusSection
      (sa' j) := fun j => by
    rw [hsa'def]; dsimp only; split_ifs
    · exact (hsa _).reparam A 0
    · exact StrongBundle.isScPlusSection_fiberZero
  have hsb' : ∀ j, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 2) PX)).IsScPlusSection
      (sb' j) := fun j => by
    rw [hsb'def]; dsimp only; split_ifs
    · exact (hsb _).reparam A 0
    · exact StrongBundle.isScPlusSection_fiberZero
  set u := Fin.append (fun j => comb (sa' j) (sb' j)) C with hudef
  have hu : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 2) PX)).IsScPlusSection
      (u i) := fun i => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [hudef, Fin.append_left]; exact hcomb (hsa' j) (hsb' j)
    · rw [hudef, Fin.append_right]; exact hC j
  -- property (P) for `u` (adding sections keeps general position)
  have hGPu : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin 2 → ℝ) 1),
      ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 2) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold ((ka + kb) + m))
          ((rnPolyfold 2).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) Ssq)
          ((isSection_pullbackLift _).sectionAdd hSsq.1) u fun i => (hu i).1) (0, (q, Φ q)) := by
    filter_upwards [hGP, hzsq] with q hq hq0
    exact StrongBundle.isGeneralPositionGerm_paramSection_of_comp (prod_rn_isTame hX)
      (theorem_3_15_tame hf.param hSsq) hC hu (Fin.natAdd (ka + kb))
      (fun i => (Fin.append_right _ C i).symm) hq0 hq
  -- the stabilized kernels over the square
  obtain ⟨Λ, hΛ⟩ := exists_isStabKernels hf hΦs hc hΦc hSsq hzsq hu hGPu
  -- the edges `τ = 0` and `τ = 1`
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have : Nonempty (Icc (0 : Fin 1 → ℝ) 1) := ⟨⟨0, left_mem_Icc.2 zero_le_one⟩⟩
  have hy : ∀ τ (hτ : τ ∈ Icc (0 : ℝ) 1),
      (fun q : Icc (0 : Fin 2 → ℝ) 1 => Φ q) ∘ sqEdge τ hτ =
        fun q : Icc (0 : Fin 1 → ℝ) 1 => γ q := by
    intro τ hτ; funext t
    change γ (A (pt2 τ (t.1 0)) + 0) = γ t
    rw [hA, pt1_apply_zero]
  have hSe0 : (fun q : Icc (0 : Fin 2 → ℝ) 1 => pullbackSlice Ssq q) ∘ sqEdge 0 h0I =
      fun q : Icc (0 : Fin 1 → ℝ) 1 => pullbackSlice Sa q := by
    funext t
    change pullbackSlice Ssq (pt2 0 (t.1 0)) = pullbackSlice Sa t
    rw [hslice, hA, pt1_apply_zero]
    exact sectionAdd_sectionSmul_eq_left (hSa.1.pullbackSlice _) (hSb.1.pullbackSlice _)
      (by simp) (by simp)
  have hSe1 : (fun q : Icc (0 : Fin 2 → ℝ) 1 => pullbackSlice Ssq q) ∘ sqEdge 1 h1I =
      fun q : Icc (0 : Fin 1 → ℝ) 1 => pullbackSlice Sb q := by
    funext t
    change pullbackSlice Ssq (pt2 1 (t.1 0)) = pullbackSlice Sb t
    rw [hslice, hA, pt1_apply_zero]
    exact sectionAdd_sectionSmul_eq_right (hSa.1.pullbackSlice _) (hSb.1.pullbackSlice _)
      (by simp) (by simp)
  have hka : ka ≤ ka + kb + m := by omega
  have hkb : kb ≤ ka + kb + m := by omega
  have hpa : ∀ i : Fin ka, (fun i => (fun q : Icc (0 : Fin 2 → ℝ) 1 => pullbackSlice (u i) q) ∘
      sqEdge 0 h0I) (Fin.castLE hka i) =
        fun q : Icc (0 : Fin 1 → ℝ) 1 => pullbackSlice (sa i) q := by
    intro i; funext t
    change pullbackSlice (u (Fin.castLE hka i)) (pt2 0 (t.1 0)) = pullbackSlice (sa i) t
    have hi : Fin.castLE hka i = Fin.castAdd m (Fin.castLE (Nat.le_add_right ka kb) i) := rfl
    have hsi : sa' (Fin.castLE (Nat.le_add_right ka kb) i) =
        reparamSection (fun q => A q + 0) (sa i) (hsa i).1 := dif_pos i.2
    rw [hi, hudef, Fin.append_left, hcombs (hsa' _).1 (hsb' _).1,
      sectionAdd_sectionSmul_eq_left ((hsa' _).1.pullbackSlice _) ((hsb' _).1.pullbackSlice _)
        (by simp) (by simp), hsi, pullbackSlice_reparamSection, hA, pt1_apply_zero]
  have hpb : ∀ i : Fin kb, (fun i => (fun q : Icc (0 : Fin 2 → ℝ) 1 => pullbackSlice (u i) q) ∘
      sqEdge 1 h1I) (Fin.castLE hkb i) =
        fun q : Icc (0 : Fin 1 → ℝ) 1 => pullbackSlice (sb i) q := by
    intro i; funext t
    change pullbackSlice (u (Fin.castLE hkb i)) (pt2 1 (t.1 0)) = pullbackSlice (sb i) t
    have hi : Fin.castLE hkb i = Fin.castAdd m (Fin.castLE (Nat.le_add_left kb ka) i) := rfl
    have hsi : sb' (Fin.castLE (Nat.le_add_left kb ka) i) =
        reparamSection (fun q => A q + 0) (sb i) (hsb i).1 := dif_pos i.2
    rw [hi, hudef, Fin.append_left, hcombs (hsa' _).1 (hsb' _).1,
      sectionAdd_sectionSmul_eq_right ((hsa' _).1.pullbackSlice _) ((hsb' _).1.pullbackSlice _)
        (by simp) (by simp), hsi, pullbackSlice_reparamSection, hA, pt1_apply_zero]
  -- the chain of push-forwards
  have hz₀ := (exists_lift_of_smooth c hx₀ hs₀).choose_spec
  have hz₁ := (exists_lift_of_smooth c hx₁ hs₁).choose_spec
  have hf' := hf.toIsScFredholmSection
  have h0' : Φ (pt2 0 0) = x₀ := by rw [hΦdef]; dsimp only; rw [hA]; exact h₀
  have h1' : Φ (pt2 0 1) = x₁ := by rw [hΦdef]; dsimp only; rw [hA]; exact h₁
  have h0'' : Φ (pt2 1 0) = x₀ := by rw [hΦdef]; dsimp only; rw [hA]; exact h₀
  have h1'' : Φ (pt2 1 1) = x₁ := by rw [hΦdef]; dsimp only; rw [hA]; exact h₁
  have ea := hΛa.push_eq_of_prefix (hΛ.comp (sqEdge 0 h0I)) (hy 0 h0I) hSe0 hka hpa hf'
    ⟨pt1 0, pt1_mem_Icc (left_mem_Icc.2 zero_le_one)⟩
    ⟨pt1 1, pt1_mem_Icc (right_mem_Icc.2 zero_le_one)⟩ h₀ h₁ h0' h1' hs₀ hs₁ _ hz₀ _ hz₁
  have eb := hΛb.push_eq_of_prefix (hΛ.comp (sqEdge 1 h1I)) (hy 1 h1I) hSe1 hkb hpb hf'
    ⟨pt1 0, pt1_mem_Icc (left_mem_Icc.2 zero_le_one)⟩
    ⟨pt1 1, pt1_mem_Icc (right_mem_Icc.2 zero_le_one)⟩ h₀ h₁ h0'' h1'' hs₀ hs₁ _ hz₀ _ hz₁
  have ca := hΛ.push_comp (sqEdge 0 h0I) hf' ⟨pt1 0, pt1_mem_Icc (left_mem_Icc.2 zero_le_one)⟩
    ⟨pt1 1, pt1_mem_Icc (right_mem_Icc.2 zero_le_one)⟩ h0' h1' hs₀ hs₁ _ hz₀ _ hz₁
  have cb := hΛ.push_comp (sqEdge 1 h1I) hf' ⟨pt1 0, pt1_mem_Icc (left_mem_Icc.2 zero_le_one)⟩
    ⟨pt1 1, pt1_mem_Icc (right_mem_Icc.2 zero_le_one)⟩ h0'' h1'' hs₀ hs₁ _ hz₀ _ hz₁
  -- the deformation: along `t = 0, 1` the points stay at `x₀, x₁`
  have hT : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) {x : X} (hx : x ∈ c.φ.source)
      (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x),
      Continuous fun τ => linAt c.U c.R (c.principal (sectionAdd P f
        ((fun q : Icc (0 : Fin 2 → ℝ) 1 => pullbackSlice Ssq q) (sqPath t ht τ)))) z := by
    intro t ht x hx z hz
    have heq : (fun τ : unitInterval => linAt c.U c.R (c.principal (sectionAdd P f
        ((fun q : Icc (0 : Fin 2 → ℝ) 1 => pullbackSlice Ssq q) (sqPath t ht τ)))) z) =
        fun τ : unitInterval => (1 - (τ : ℝ)) •
          linAt c.U c.R (c.principal (sectionAdd P f (pullbackSlice Sa (pt1 t)))) z +
          (τ : ℝ) • linAt c.U c.R (c.principal (sectionAdd P f (pullbackSlice Sb (pt1 t)))) z := by
      funext τ
      change linAt c.U c.R (c.principal (sectionAdd P f (pullbackSlice Ssq (pt2 τ t)))) z = _
      rw [hslice, hA, pt2_apply_zero]
      exact linAt_principal_combo hfs (hSa.pullbackSlice _) (hSb.pullbackSlice _) hc
        (chartPt c hc hx z hz).mem_U τ
    rw [heq]
    exact ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)
  have hU : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) {x : X} (hx : x ∈ c.φ.source)
      (i : Fin (ka + kb + m)), Continuous fun τ =>
        c.principal ((fun i (q : Icc (0 : Fin 2 → ℝ) 1) => pullbackSlice (u i) q) i
        (sqPath t ht τ)) (c.φ x) := fun t ht x hx i =>
    (continuous_principal_pullbackSlice (hu i) hc hx).comp
      (continuous_subtype_val.comp (sqPath t ht).continuous)
  have sq := hΛ.push_square hf' (sqPath 0 h0I) (sqPath 1 h1I)
    (fun τ => by change Φ (pt2 τ 0) = x₀; rw [hΦdef]; dsimp only; rw [hA]; exact h₀)
    (fun τ => by change Φ (pt2 τ 1) = x₁; rw [hΦdef]; dsimp only; rw [hA]; exact h₁)
    hs₀ hs₁ _ hz₀ _ hz₁ (hT 0 h0I hx₀ _ hz₀) (hT 1 h1I hx₁ _ hz₁) (hU 0 h0I hx₀) (hU 1 h1I hx₁)
  exact ea.symm.trans (ca.trans (sq.trans (cb.symm.trans eb)))

/-- **Push-forwards along the two edges of a homotopy agree** (the homotopy argument before
Theorem 6.35): for an sc-smooth `Φ : ℝ² → dom φ_c` with `Φ(0, ·) = γ₀`, `Φ(1, ·) = γ₁`, the end
points fixed at `x₀`, `x₁` along `[0, 1]`, and an sc⁺-section `S` with `(f + S)(q, Φ(q)) = 0` near
the square depending on `q ∈ [0, 1]²` only through `Φ(q)` (Proposition 6.28 (3)), push-forwards
along `γ₀` and `γ₁` agree (Lemma 6.29 and `exists_isStabKernels` on the square, Proposition 6.32
on the edges, `push_comp`, and `push_square` with constant operators at the end points). -/
theorem push_eq_of_homotopy (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    {γ₀ γ₁ : (Fin 1 → ℝ) → X} (hγ₀s : (rnPolyfold 1).IsScSmoothMap PX γ₀)
    (hγ₁s : (rnPolyfold 1).IsScSmoothMap PX γ₁)
    (hγ₀ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ₀ q ∈ c.φ.source)
    (hγ₁ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ₁ q ∈ c.φ.source)
    {Φ : (Fin 2 → ℝ) → X} (hΦs : (rnPolyfold 2).IsScSmoothMap PX Φ)
    (hΦc : ∀ q ∈ Icc (0 : Fin 2 → ℝ) 1, Φ q ∈ c.φ.source)
    (hΦ0 : ∀ t : Fin 1 → ℝ, Φ (pt2 0 (t 0)) = γ₀ t) (hΦ1 : ∀ t : Fin 1 → ℝ, Φ (pt2 1 (t 0)) = γ₁ t)
    {x₀ x₁ : X} (hΦa : ∀ τ ∈ Icc (0 : ℝ) 1, Φ (pt2 τ 0) = x₀)
    (hΦb : ∀ τ ∈ Icc (0 : ℝ) 1, Φ (pt2 τ 1) = x₁)
    {S : (Fin 2 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 2 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 2) PX)).IsScPlusSection S)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin 2 → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q))
    (hSΦ : ∀ q ∈ Icc (0 : Fin 2 → ℝ) 1, ∀ q' ∈ Icc (0 : Fin 2 → ℝ) 1, Φ q = Φ q' →
      ∀ y, (S (q, y)).1.2 = (S (q', y)).1.2)
    (h₀₀ : γ₀ (pt1 0) = x₀) (h₀₁ : γ₀ (pt1 1) = x₁) (h₁₀ : γ₁ (pt1 0) = x₀)
    (h₁₁ : γ₁ (pt1 1) = x₁) (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet)
    {e₀ e₁ : (chartPtOf c hc hx₀ hs₀).Or f hf.toIsScFredholmSection ≃
      (chartPtOf c hc hx₁ hs₁).Or f hf.toIsScFredholmSection}
    (he₀ : IsPush f hf.toIsScFredholmSection c hc γ₀ hγ₀ h₀₀ h₀₁ hx₀ hx₁ hs₀ hs₁ e₀)
    (he₁ : IsPush f hf.toIsScFredholmSection c hc γ₁ hγ₁ h₁₀ h₁₁ hx₀ hx₁ hs₀ hs₁ e₁) :
    e₀ = e₁ := by
  have hfs := hf.isScSmooth
  have hf' := hf.toIsScFredholmSection
  obtain ⟨m, C, hC, hGP⟩ := lemma_6_29 hX hbump hf hΦs hS hz
  obtain ⟨Λ, hΛ⟩ := exists_isStabKernels hf hΦs hc hΦc hS hz hC hGP
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have hz₀ := (exists_lift_of_smooth c hx₀ hs₀).choose_spec
  have hz₁ := (exists_lift_of_smooth c hx₁ hs₁).choose_spec
  -- the edge `t ↦ (τ, t)` as the affine map `t ↦ A₀t + (τ, 0)`
  set A₀ : (Fin 1 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    (ContinuousLinearMap.proj 0).smulRight (Pi.single 1 1) with hA₀def
  have hA₀ : ∀ (τ : ℝ) (t : Fin 1 → ℝ), A₀ t + pt2 τ 0 = pt2 τ (t 0) := by
    intro τ t; funext i; fin_cases i <;> simp [hA₀def]
  -- the restriction to an edge is a push-forward datum along it
  have edge : ∀ (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) (δ : (Fin 1 → ℝ) → X)
      (hδ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, δ q ∈ c.φ.source) (hΦδ : ∀ t, Φ (pt2 τ (t 0)) = δ t)
      (hδ0 : δ (pt1 0) = x₀) (hδ1 : δ (pt1 1) = x₁),
      IsPush f hf' c hc δ hδ hδ0 hδ1 hx₀ hx₁ hs₀ hs₁ ((hΛ.comp (sqEdge τ hτ)).push hf'
        ⟨pt1 0, pt1_mem_Icc h0I⟩ ⟨pt1 1, pt1_mem_Icc h1I⟩ (hΦa τ hτ) (hΦb τ hτ) hs₀ hs₁ _ hz₀ _
        hz₁) := by
    intro τ hτ δ hδ hΦδ hδ0 hδ1
    have hy : (fun q : Icc (0 : Fin 2 → ℝ) 1 => Φ q) ∘ sqEdge τ hτ =
        fun q : Icc (0 : Fin 1 → ℝ) 1 => δ q := funext fun t => hΦδ t.1
    have hSe : (fun q : Icc (0 : Fin 2 → ℝ) 1 => pullbackSlice S q) ∘ sqEdge τ hτ =
        fun q : Icc (0 : Fin 1 → ℝ) 1 =>
          pullbackSlice (reparamSection (fun t => A₀ t + pt2 τ 0) S hS.1) q := by
      funext t
      change pullbackSlice S (pt2 τ (t.1 0)) = pullbackSlice S (A₀ t + pt2 τ 0)
      rw [hA₀]
    have hse : (fun i => (fun q : Icc (0 : Fin 2 → ℝ) 1 => pullbackSlice (C i) q) ∘ sqEdge τ hτ) =
        fun i (q : Icc (0 : Fin 1 → ℝ) 1) =>
          pullbackSlice (reparamSection (fun t => A₀ t + pt2 τ 0) (C i) (hC i).1) q := by
      funext i t
      change pullbackSlice (C i) (pt2 τ (t.1 0)) = pullbackSlice (C i) (A₀ t + pt2 τ 0)
      rw [hA₀]
    have hΛe := (hΛ.comp (sqEdge τ hτ)).congr_data (fun q : Icc (0 : Fin 1 → ℝ) 1 => hδ q q.2)
      hy hSe hse
    refine ⟨reparamSection (fun t => A₀ t + pt2 τ 0) S hS.1, hS.reparam A₀ _, ?_, m,
      fun i => reparamSection (fun t => A₀ t + pt2 τ 0) (C i) (hC i).1,
      fun i => (hC i).reparam A₀ _, Λ.comp (sqEdge τ hτ), hΛe,
      IsStabKernels.push_congr_data _ _ hy hSe hse hf' _ _ _ _ _ _ hs₀ hs₁ _ hz₀ _ hz₁⟩
    have hT : Tendsto (fun t => A₀ t + pt2 τ 0) (𝓝ˢ (Icc (0 : Fin 1 → ℝ) 1))
        (𝓝ˢ (Icc (0 : Fin 2 → ℝ) 1)) :=
      (A₀.continuous.add continuous_const).tendsto_nhdsSet fun t ht => by
        change A₀ t + pt2 τ 0 ∈ Icc (0 : Fin 2 → ℝ) 1
        rw [hA₀]; exact pt2_mem_Icc hτ ⟨ht.1 0, ht.2 0⟩
    filter_upwards [hT.eventually hz] with t ht
    rw [isZeroAt_pullback_iff_pullbackSlice ((isSection_pullbackLift _).sectionAdd hS.1),
      pullbackSlice_sectionAdd_paramLift hfs.1 hS.1] at ht
    rw [isZeroAt_pullback_iff_pullbackSlice ((isSection_pullbackLift _).sectionAdd (hS.reparam A₀
      (pt2 τ 0)).1), pullbackSlice_sectionAdd_paramLift hfs.1 (hS.reparam A₀ (pt2 τ 0)).1,
      pullbackSlice_reparamSection, ← hΦδ t, ← hA₀]
    exact ht
  -- the push-forwards along the edges
  have ea := proposition_6_32 hX hbump hf hc hγ₀s hγ₀ h₀₀ h₀₁ hx₀ hx₁ hs₀ hs₁ he₀
    (edge 0 h0I γ₀ hγ₀ hΦ0 h₀₀ h₀₁)
  have eb := proposition_6_32 hX hbump hf hc hγ₁s hγ₁ h₁₀ h₁₁ hx₀ hx₁ hs₀ hs₁ he₁
    (edge 1 h1I γ₁ hγ₁ hΦ1 h₁₀ h₁₁)
  have ca := hΛ.push_comp (sqEdge 0 h0I) hf' ⟨pt1 0, pt1_mem_Icc h0I⟩ ⟨pt1 1, pt1_mem_Icc h1I⟩
    (hΦa 0 h0I) (hΦb 0 h0I) hs₀ hs₁ _ hz₀ _ hz₁
  have cb := hΛ.push_comp (sqEdge 1 h1I) hf' ⟨pt1 0, pt1_mem_Icc h0I⟩ ⟨pt1 1, pt1_mem_Icc h1I⟩
    (hΦa 1 h1I) (hΦb 1 h1I) hs₀ hs₁ _ hz₀ _ hz₁
  -- along `t = 0, 1` the point and hence the section `S(q, ·)` are constant
  have hT : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) {x : X} (_ : ∀ τ ∈ Icc (0 : ℝ) 1, Φ (pt2 τ t) = x)
      (z : c.φ.model.E 1),
      Continuous fun τ => linAt c.U c.R (c.principal (sectionAdd P f
        ((fun q : Icc (0 : Fin 2 → ℝ) 1 => pullbackSlice S q) (sqPath t ht τ)))) z := by
    intro t ht x hΦx z
    have heq : ∀ τ : unitInterval, pullbackSlice S (pt2 τ t) = pullbackSlice S (pt2 0 t) :=
      fun τ => funext fun y => hSΦ _ (pt2_mem_Icc τ.2 ht) _ (pt2_mem_Icc h0I ht)
        ((hΦx τ τ.2).trans (hΦx 0 h0I).symm) y
    have hc' : (fun τ : unitInterval => linAt c.U c.R (c.principal (sectionAdd P f
        ((fun q : Icc (0 : Fin 2 → ℝ) 1 => pullbackSlice S q) (sqPath t ht τ)))) z) =
        fun _ => linAt c.U c.R (c.principal (sectionAdd P f (pullbackSlice S (pt2 0 t)))) z :=
      funext fun τ => by
        change linAt c.U c.R (c.principal (sectionAdd P f (pullbackSlice S (pt2 τ t)))) z = _
        rw [heq τ]
    rw [hc']
    exact continuous_const
  have hU : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) {x : X} (hx : x ∈ c.φ.source) (i : Fin m),
      Continuous fun τ => c.principal ((fun i (q : Icc (0 : Fin 2 → ℝ) 1) => pullbackSlice (C i) q)
        i (sqPath t ht τ)) (c.φ x) := fun t ht x hx i =>
    (continuous_principal_pullbackSlice (hC i) hc hx).comp
      (continuous_subtype_val.comp (sqPath t ht).continuous)
  have sq := hΛ.push_square hf' (sqPath 0 h0I) (sqPath 1 h1I) (fun τ => hΦa τ τ.2)
    (fun τ => hΦb τ τ.2) hs₀ hs₁ _ hz₀ _ hz₁ (hT 0 h0I hΦa _) (hT 1 h1I hΦb _) (hU 0 h0I hx₀)
    (hU 1 h1I hx₁)
  exact ea.trans (ca.trans (sq.trans (cb.symm.trans eb.symm)))

variable (f) in
/-- **The local propagation property** of `U` in the chart `c` (Theorem 6.35): along every
sc-smooth path in `U` with smooth end points there is a push-forward, and push-forwards along two
paths in `U` with the same end points agree. -/
structure HasLocalPropagation (hf : B.IsScFredholmSection f) (c : StrongBundleChart PX P)
    (hc : B.IsChart c) (U : Set X) : Prop where
  subset : U ⊆ c.φ.source
  exists_isPush : ∀ γ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ →
    ∀ (hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
      (h₁ : γ (pt1 1) = x₁) (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
      (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
      ∃ e, IsPush f hf c hc γ (fun q hq => subset (hγ q hq)) h₀ h₁ hx₀ hx₁ hs₀ hs₁ e
  eq : ∀ γ₀ γ₁ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ₀ →
    (rnPolyfold 1).IsScSmoothMap PX γ₁ → ∀ (hγ₀ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ₀ q ∈ U)
      (hγ₁ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ₁ q ∈ U) {x₀ x₁ : X} (h₀₀ : γ₀ (pt1 0) = x₀)
      (h₀₁ : γ₀ (pt1 1) = x₁) (h₁₀ : γ₁ (pt1 0) = x₀) (h₁₁ : γ₁ (pt1 1) = x₁)
      (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source) (hs₀ : x₀ ∈ PX.smoothSet)
      (hs₁ : x₁ ∈ PX.smoothSet) (e₀ e₁ : (chartPtOf c hc hx₀ hs₀).Or f hf ≃
        (chartPtOf c hc hx₁ hs₁).Or f hf),
      IsPush f hf c hc γ₀ (fun q hq => subset (hγ₀ q hq)) h₀₀ h₀₁ hx₀ hx₁ hs₀ hs₁ e₀ →
      IsPush f hf c hc γ₁ (fun q hq => subset (hγ₁ q hq)) h₁₀ h₁₁ hx₀ hx₁ hs₀ hs₁ e₁ → e₀ = e₁

/-- **Theorem 6.35**: every smooth point `x` has an open neighbourhood `U` in the domain of a
chart with the local propagation property (Proposition 6.28, `exists_isPush`, Proposition 6.32
and the homotopy argument before Theorem 6.35). -/
theorem theorem_6_35 (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {x : X} (hx : x ∈ PX.smoothSet) :
    ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U : Set X), IsOpen U ∧ x ∈ U ∧
      HasLocalPropagation f hf.toIsScFredholmSection c hc U := by
  obtain ⟨U, W, c, hUo, -, hxU, hUW, hcA, hWc, h1', -, h3, -⟩ :=
    proposition_6_28 hbump hf.toIsScFredholmSection hx
  have hc : B.IsChart c := B.isChart_of_mem hcA
  have h3' : ∀ Φ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX Φ →
      (∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, Φ q ∈ W) →
      ∃ S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X),
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S ∧
        ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin 1 → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q) :=
    fun Φ hΦ hΦW => by
      obtain ⟨S, hS, hz, -⟩ := h3 1 Φ hΦ hΦW
      exact ⟨S, hS, hz⟩
  refine ⟨c, hc, U, hUo, hxU, ⟨hUW.trans hWc, fun γ hγs hγ x₀ x₁ h₀ h₁ hx₀ hx₁ hs₀ hs₁ =>
    exists_isPush hX hbump hf hc hWc h3' hγs (fun q hq => hUW (hγ q hq)) h₀ h₁ hx₀ hx₁ hs₀ hs₁,
    ?_⟩⟩
  intro γ₀ γ₁ hγ₀s hγ₁s hγ₀ hγ₁ x₀ x₁ h₀₀ h₀₁ h₁₀ h₁₁ hx₀ hx₁ hs₀ hs₁ e₀ e₁ he₀ he₁
  -- (1′): a homotopy from `γ₀` to `γ₁` in `W` with the end points fixed
  obtain ⟨Φ, hΦ, hΦW⟩ := h1' γ₀ γ₁ hγ₀s hγ₁s (fun t ht => hγ₀ _ (pt1_mem_Icc ht))
    (fun t ht => hγ₁ _ (pt1_mem_Icc ht)) (h₀₀.trans h₁₀.symm) (h₀₁.trans h₁₁.symm)
  -- the reparametrization `κ` of `ℝ` onto `[0, 1]`, with `κ(0) = 0`, `κ(1) = 1`
  set κ : ℝ → ℝ := Real.smoothTransition with hκdef
  have hκ : ContDiff ℝ ∞ κ := Real.smoothTransition.contDiff
  have hκI : ∀ s, κ s ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨Real.smoothTransition.nonneg s, Real.smoothTransition.le_one s⟩
  have hκ0 : κ 0 = 0 := Real.smoothTransition.zero
  have hκ1 : κ 1 = 1 := Real.smoothTransition.one
  set K : (Fin 1 → ℝ) → Fin 1 → ℝ := fun p => pt1 (κ (p 0)) with hKdef
  have hK : ContDiff ℝ ∞ K := contDiff_pi.2 fun _ => hκ.comp (contDiff_apply ℝ ℝ 0)
  have hqI : ∀ q ∈ Icc (0 : Fin 2 → ℝ) 1, q 0 ∈ Icc (0 : ℝ) 1 ∧ q 1 ∈ Icc (0 : ℝ) 1 :=
    fun q hq => ⟨⟨hq.1 0, hq.2 0⟩, ⟨hq.1 1, hq.2 1⟩⟩
  -- a path `γ` in `U` and its reparametrization `γ ∘ κ` give the same push-forward
  have rep : ∀ (γ : (Fin 1 → ℝ) → X) (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
      (hγU : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U) (h0 : γ (pt1 0) = x₀) (h1 : γ (pt1 1) = x₁)
      (h0' : (γ ∘ K) (pt1 0) = x₀) (h1' : (γ ∘ K) (pt1 1) = x₁)
      (e e' : (chartPtOf c hc hx₀ hs₀).Or f hf.toIsScFredholmSection ≃
        (chartPtOf c hc hx₁ hs₁).Or f hf.toIsScFredholmSection),
      IsPush f hf.toIsScFredholmSection c hc γ (fun q hq => hWc (hUW (hγU q hq))) h0 h1 hx₀
        hx₁ hs₀ hs₁ e →
      IsPush f hf.toIsScFredholmSection c hc (γ ∘ K)
        (fun q _ => hWc (hUW (hγU _ (pt1_mem_Icc (hκI _))))) h0' h1' hx₀ hx₁ hs₀ hs₁ e' →
      e = e' := by
    intro γ hγs hγU h0 h1 h0' h1' e e' he he'
    -- `H(σ, t) = γ((1 − σ)t + σκ(t))`
    set H : (Fin 2 → ℝ) → X := fun q => γ (pt1 ((1 - q 0) * q 1 + q 0 * κ (q 1))) with hHdef
    have hHs : (rnPolyfold 2).IsScSmoothMap PX H :=
      hγs.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pi.2 fun _ =>
        ((contDiff_const.sub (contDiff_apply ℝ ℝ 0)).mul (contDiff_apply ℝ ℝ 1)).add
          ((contDiff_apply ℝ ℝ 0).mul (hκ.comp (contDiff_apply ℝ ℝ 1)))))
    have hHW : ∀ q ∈ Icc (0 : Fin 2 → ℝ) 1, H q ∈ W := by
      intro q hq
      obtain ⟨⟨ha0, ha1⟩, ⟨ht0, ht1⟩⟩ := hqI q hq
      obtain ⟨hk0, hk1⟩ := hκI (q 1)
      refine hUW (hγU _ (pt1_mem_Icc ⟨?_, ?_⟩))
      · positivity
      · nlinarith
    obtain ⟨S, hS, hz, hSH⟩ := h3 2 H hHs hHW
    refine push_eq_of_homotopy hX hbump hf hc hγs (hγs.comp (isScSmoothMap_rn_rn_of_contDiff hK))
      _ _ hHs (fun q hq => hWc (hHW q hq)) (fun t => ?_) (fun t => ?_) (fun τ _ => ?_)
      (fun τ _ => ?_) hS hz hSH h0 h1 h0' h1' hx₀ hx₁ hs₀ hs₁ he he'
    · simp only [hHdef, pt2_apply_zero, pt2_apply_one, sub_zero, one_mul, zero_mul, add_zero,
        pt1_apply_zero]
    · simp only [hHdef, pt2_apply_zero, pt2_apply_one, sub_self, zero_mul, one_mul, zero_add,
        Function.comp_apply, hKdef]
    · simp only [hHdef, pt2_apply_zero, pt2_apply_one, mul_zero, hκ0, add_zero]
      exact h0
    · simp only [hHdef, pt2_apply_zero, pt2_apply_one, mul_one, hκ1, sub_add_cancel]
      exact h1
  have hK0 : ∀ γ : (Fin 1 → ℝ) → X, (γ ∘ K) (pt1 0) = γ (pt1 0) := fun γ => by
    simp only [Function.comp_apply, hKdef, pt1, hκ0]
  have hK1 : ∀ γ : (Fin 1 → ℝ) → X, (γ ∘ K) (pt1 1) = γ (pt1 1) := fun γ => by
    simp only [Function.comp_apply, hKdef, pt1, hκ1]
  have hδW : ∀ γ : (Fin 1 → ℝ) → X, (∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U) →
      ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, (γ ∘ K) q ∈ W := fun γ hγU q _ =>
    hUW (hγU _ (pt1_mem_Icc (hκI _)))
  obtain ⟨e₀', he₀'⟩ := exists_isPush hX hbump hf hc hWc h3'
    (hγ₀s.comp (isScSmoothMap_rn_rn_of_contDiff hK)) (hδW γ₀ hγ₀) ((hK0 γ₀).trans h₀₀)
    ((hK1 γ₀).trans h₀₁) hx₀ hx₁ hs₀ hs₁
  obtain ⟨e₁', he₁'⟩ := exists_isPush hX hbump hf hc hWc h3'
    (hγ₁s.comp (isScSmoothMap_rn_rn_of_contDiff hK)) (hδW γ₁ hγ₁) ((hK0 γ₁).trans h₁₀)
    ((hK1 γ₁).trans h₁₁) hx₀ hx₁ hs₀ hs₁
  have r₀ := rep γ₀ hγ₀s hγ₀ h₀₀ h₀₁ _ _ e₀ e₀' he₀ he₀'
  have r₁ := rep γ₁ hγ₁s hγ₁ h₁₀ h₁₁ _ _ e₁ e₁' he₁ he₁'
  -- the homotopy `Φ(τ, κ(t))` from `γ₀ ∘ κ` to `γ₁ ∘ κ`
  set Ψ : (Fin 2 → ℝ) → X := fun q => Φ (pt2 (q 0) (κ (q 1))) with hΨdef
  have hM : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => pt2 (q 0) (κ (q 1)) := by
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · convert contDiff_apply ℝ ℝ (0 : Fin 2) using 1
      funext q; simp
    · convert hκ.comp (contDiff_apply ℝ ℝ (1 : Fin 2)) using 1
      funext q; simp
  have hΨs : (rnPolyfold 2).IsScSmoothMap PX Ψ :=
    hΦ.isScSmoothMap.comp (isScSmoothMap_rn_rn_of_contDiff hM)
  have hΨW : ∀ q ∈ Icc (0 : Fin 2 → ℝ) 1, Ψ q ∈ W := fun q hq =>
    hΦW _ (hqI q hq).1 _ (hκI _)
  obtain ⟨S, hS, hz, hSΨ⟩ := h3 2 Ψ hΨs hΨW
  have mid := push_eq_of_homotopy hX hbump hf hc (hγ₀s.comp (isScSmoothMap_rn_rn_of_contDiff hK))
    (hγ₁s.comp (isScSmoothMap_rn_rn_of_contDiff hK)) _ _ hΨs (fun q hq => hWc (hΨW q hq))
    (fun t => by
      simp only [hΨdef, pt2_apply_zero, pt2_apply_one]
      exact hΦ.zero _ (hκI _))
    (fun t => by
      simp only [hΨdef, pt2_apply_zero, pt2_apply_one]
      exact hΦ.one _ (hκI _))
    (fun τ hτ => by
      simp only [hΨdef, pt2_apply_zero, pt2_apply_one, hκ0]
      exact (hΦ.start τ hτ).trans h₀₀)
    (fun τ hτ => by
      simp only [hΨdef, pt2_apply_zero, pt2_apply_one, hκ1]
      exact (hΦ.finish τ hτ).trans h₀₁)
    hS hz hSΨ _ _ _ _ hx₀ hx₁ hs₀ hs₁ he₀' he₁'
  exact r₀.trans (mid.trans r₁.symm)

end Push

end Polyfold
