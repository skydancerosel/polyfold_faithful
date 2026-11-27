import GWMemoir.Groupoid
import GWMemoir.Witnesses

/-!
# The Cauchy–Riemann operator on objects and the fibres of `W`

HWZ, *Applications of Polyfold Theory I* (Memoirs AMS 248, no. 1179), §1.2 (the bundle
`p : W → Z`, pp. 6–7) and §1.3 (the Cauchy–Riemann section, p. 8):

  `∂̄_{J,j}(u) = ½ (Tu + J(u) ∘ Tu ∘ j)`,

a complex anti-linear map `(T_zS, j) → (T_{u(z)}Q, J(u(z)))`; the fibre of `W` over `[α]`
consists of anti-linear forms `ξ` along `u` of class `H^{k+2}_loc` off the nodes and of class
`(k + 2, δ_k)` at the nodal points, read in polar coordinates as
`(s, t) ↦ Tψ(u(σ(s, t))) ξ(σ(s, t))(∂_s σ(s, t))` (p. 7), and two tuples
`(S, j, M, D, u, ξ)`, `(S', j', M', D', u', ξ')` are equivalent under an isomorphism `φ` with
`ξ' ∘ Tφ = ξ` and `u' ∘ φ = u`.

## What is formalized

* `Tu u x` (the derivative `mfderiv`, read in Mathlib's tangent identification) and
  `dbar J X u x = ½ (Tu + J(u x) ∘ Tu ∘ j_x)`.
* `antiLinearForms J X y x`: the anti-linear maps `(T_xS, j) → (T_yQ, J(y))`, a submodule;
  `dbar_mem_antiLinearForms` (**`∂̄_{J,j}(u)(x)` is anti-linear**, from `J² = j² = −1`).
* `dbar_eq_zero_iff`: `∂̄_{J,j}(u)(x) = 0` iff `Tu ∘ j = J ∘ Tu` at `x`.
* **Naturality (chain rule)**: `NodalSurface.Iso.dbar_comp` (`∂̄(u') (φ x) ∘ Tφ_x = ∂̄(u' ∘ φ)(x)`
  for every isomorphism `φ` of noded Riemann surfaces and every `u'`, differentiable or not) and
  `StableMap.Iso.dbar_comp` (`∂̄(u')(φ x) ∘ Tφ_x = ∂̄(u)(x)` for an isomorphism of stable maps:
  the section is well defined on the classes `[α]`).  `pullbackForm` (`ξ' ↦ ξ' ∘ Tφ`) preserves
  anti-linearity (`pullbackForm_mem`).
* The fibre: `formInPolar`, `IsFormClassNear` (class `(k, δ)` at a nodal point, p. 7),
  `IsFormHlocNear` (`H^k_loc`), `IsFibreElement α k δ ξ`; `isFibreElement_zero` (the zero
  section: `0` lies in every fibre, with the charts of `α` itself).
* `IsHolomorphic α`; the constant stable maps are holomorphic (`isHolomorphic_constStableMap`):
  the solution sets of `∂̄_J` are not empty.

## Readings

* `Tu` is Mathlib's `mfderiv`; for a map that is not differentiable at `x` it is `0`.  Stable
  maps of class `(3, δ₀)` are `C¹`; the naturality holds with no differentiability hypothesis
  (`u' ∘ φ` is differentiable at `x` iff `u'` is at `φ x`).
* The fibre element `ξ` is a function on all of `S`; the memoir defines it on `S ∖ |D|`, and
  anti-linearity is asked there only.  The fibre of class `(k + 2, δ_k)` is `IsFibreElement α
  (k + 2) (δ k)`.  The Banach space structure of the fibre (its norm) is not formalized here.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Set Function

noncomputable section

namespace GWMemoir

open Polyfold Polyfold.CylinderSobolev

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-! ### `J² = −1` pointwise -/

theorem AlmostComplexStructure.J_J {M : Type} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (J : AlmostComplexStructure E M) (x : M) (v : E) :
    J.J x (J.J x v) = -v := by
  have := congrArg (fun L => L v) (J.sq x)
  simpa using this

namespace NodalSurface

variable {m : ℕ}

/-! ### The operator on objects -/

/-- `Tu(x)` as a linear map `E2 → E` (Mathlib's identification of the tangent spaces with the
model spaces). -/
def Tu (X : NodalSurface m) (u : X.S → Q) (x : X.S) : E2 →L[ℝ] E :=
  mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) u x

/-- **The Cauchy–Riemann operator** (Memoir §1.3, p. 8): `∂̄_{J,j}(u) = ½ (Tu + J(u) ∘ Tu ∘ j)`. -/
def dbar (J : AlmostComplexStructure E Q) (X : NodalSurface m) (u : X.S → Q) (x : X.S) :
    E2 →L[ℝ] E :=
  (1 / 2 : ℝ) • (X.Tu u x + (J.J (u x)).comp ((X.Tu u x).comp (X.j.J x)))

/-- The anti-linear maps `(T_xS, j) → (T_yQ, J(y))`: `J(y) ∘ L = −L ∘ j_x`. -/
def antiLinearForms (J : AlmostComplexStructure E Q) (X : NodalSurface m) (y : Q) (x : X.S) :
    Submodule ℝ (E2 →L[ℝ] E) where
  carrier := {L | (J.J y).comp L = -(L.comp (X.j.J x))}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [ContinuousLinearMap.comp_add, ha, hb, ContinuousLinearMap.add_comp, neg_add]
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [ContinuousLinearMap.comp_smul, ha, ContinuousLinearMap.smul_comp, smul_neg]

variable (J : AlmostComplexStructure E Q) (X : NodalSurface m)

theorem mem_antiLinearForms {y : Q} {x : X.S} {L : E2 →L[ℝ] E} :
    L ∈ X.antiLinearForms J y x ↔ ∀ v, J.J y (L v) = -L (X.j.J x v) := by
  change (J.J y).comp L = -(L.comp (X.j.J x)) ↔ _
  constructor
  · intro h v; exact congrArg (fun T => T v) h
  · intro h; ext v; simpa using h v

/-- **`∂̄_{J,j}(u)(x)` is complex anti-linear** (p. 8): `J ∘ ∂̄ = −∂̄ ∘ j`. -/
theorem dbar_mem_antiLinearForms (u : X.S → Q) (x : X.S) :
    X.dbar J u x ∈ X.antiLinearForms J (u x) x := by
  rw [mem_antiLinearForms]
  intro v
  simp only [dbar, smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, map_smul, map_add, J.J_J, X.j.J_J, map_neg]
  module

/-- `∂̄_{J,j}(u)(x) = 0` iff `u` is `(j, J)`-holomorphic at `x`: `Tu ∘ j = J ∘ Tu`. -/
theorem dbar_eq_zero_iff (u : X.S → Q) (x : X.S) :
    X.dbar J u x = 0 ↔ (X.Tu u x).comp (X.j.J x) = (J.J (u x)).comp (X.Tu u x) := by
  constructor
  · intro h
    ext v
    have h1 := congrArg (fun L => J.J (u x) (L v)) h
    simp only [dbar, smul_apply, add_apply,
      ContinuousLinearMap.comp_apply, map_smul, map_add, J.J_J, zero_apply,
      map_zero, smul_eq_zero] at h1
    simp only [ContinuousLinearMap.comp_apply]
    rcases h1 with h1 | h1
    · norm_num at h1
    · rw [add_neg_eq_zero] at h1; exact h1.symm
  · intro h
    ext v
    have h1 := congrArg (fun L => J.J (u x) (L v)) h
    simp only [ContinuousLinearMap.comp_apply, J.J_J] at h1
    simp only [dbar, smul_apply, add_apply,
      ContinuousLinearMap.comp_apply, h1, zero_apply]
    simp

/-- The derivative of a constant map vanishes. -/
theorem Tu_const (q : Q) (x : X.S) : X.Tu (E := E) (fun _ => q) x = 0 := mfderiv_const

/-- The constant map has `∂̄ = 0`. -/
theorem dbar_const (q : Q) (x : X.S) : X.dbar J (fun _ => q) x = 0 := by
  simp [dbar, Tu_const]

end NodalSurface

/-! ### Naturality: the chain rule -/

namespace NodalSurface.Iso

variable {m : ℕ} {X Y : NodalSurface m} (J : AlmostComplexStructure E Q)

/-- `Tφ_x` as a linear map `E2 → E2`. -/
def T (f : Iso X Y) (x : X.S) : E2 →L[ℝ] E2 := mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ x

theorem T_j (f : Iso X Y) (x : X.S) (v : E2) : f.T x (X.j.J x v) = Y.j.J (f.φ x) (f.T x v) :=
  f.holo_apply rfl v

theorem symm_T_T (f : Iso X Y) (x : X.S) (v : E2) : f.symm.T (f.φ x) (f.T x v) = v :=
  f.mfderiv_symm_comp x v

theorem T_symm_T (f : Iso X Y) (x : X.S) (v : E2) : f.T x (f.symm.T (f.φ x) v) = v := by
  have key : ∀ (y : Y.S) (x' : X.S), f.φ.symm y = x' →
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ x' (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ.symm y v) = v := by
    rintro y x' rfl
    exact f.mfderiv_comp_symm y v
  exact key (f.φ x) x (f.φ.symm_apply_apply x)

/-- `T(u' ∘ φ)(x) = Tu'(φ x) ∘ Tφ(x)` for an isomorphism `φ`, whether or not `u'` is
differentiable at `φ x`. -/
theorem Tu_comp (f : Iso X Y) (u' : Y.S → Q) (x : X.S) :
    X.Tu (E := E) (u' ∘ f.φ) x = (Y.Tu u' (f.φ x)).comp (f.T x) := by
  by_cases hd : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) u' (f.φ x)
  · exact mfderiv_comp x hd (f.mdifferentiableAt x)
  · have hd' : ¬ MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) (u' ∘ f.φ) x := by
      intro h
      apply hd
      have hs : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ.symm (f.φ x) :=
        f.φ.symm.contMDiffAt.mdifferentiableAt (by simp)
      have h' : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) (u' ∘ f.φ) (f.φ.symm (f.φ x)) := by
        rwa [f.φ.symm_apply_apply]
      have h2 := h'.comp (f.φ x) hs
      have he : (u' ∘ f.φ) ∘ f.φ.symm = u' := funext fun y => by simp
      rwa [he] at h2
    simp only [Tu, mfderiv_zero_of_not_mdifferentiableAt hd,
      mfderiv_zero_of_not_mdifferentiableAt hd']
    rfl

/-- **Naturality of `∂̄` under isomorphisms of noded Riemann surfaces** (chain rule):
`∂̄_{J,j'}(u')(φ x) ∘ Tφ_x = ∂̄_{J,j}(u' ∘ φ)(x)`. -/
theorem dbar_comp (f : Iso X Y) (u' : Y.S → Q) (x : X.S) :
    (Y.dbar J u' (f.φ x)).comp (f.T x) = X.dbar J (u' ∘ f.φ) x := by
  ext v
  simp only [dbar, Tu_comp, ContinuousLinearMap.comp_apply, smul_apply,
    add_apply, Function.comp_apply, f.T_j]

/-- **The morphisms of `W`** (p. 7): `ξ' ↦ ξ' ∘ Tφ`. -/
def pullbackForm (f : Iso X Y) (ξ' : Y.S → E2 →L[ℝ] E) (x : X.S) : E2 →L[ℝ] E :=
  (ξ' (f.φ x)).comp (f.T x)

/-- `ξ' ∘ Tφ` is anti-linear at `x` if `ξ'` is at `φ x`. -/
theorem pullbackForm_mem (f : Iso X Y) {ξ' : Y.S → E2 →L[ℝ] E} {y : Q} {x : X.S}
    (h : ξ' (f.φ x) ∈ Y.antiLinearForms J y (f.φ x)) :
    f.pullbackForm ξ' x ∈ X.antiLinearForms J y x := by
  rw [NodalSurface.mem_antiLinearForms] at h ⊢
  intro v
  simp only [pullbackForm, ContinuousLinearMap.comp_apply, h, f.T_j]

/-- `∂̄(u')` pulls back to `∂̄(u' ∘ φ)`. -/
theorem pullbackForm_dbar (f : Iso X Y) (u' : Y.S → Q) :
    f.pullbackForm (Y.dbar J u') = X.dbar J (u' ∘ f.φ) :=
  funext fun x => f.dbar_comp J u' x

/-- `ξ' ∘ Tφ` determines `ξ'`: `Tφ` is invertible and `φ` surjective. -/
theorem pullbackForm_injective (f : Iso X Y) : Injective (f.pullbackForm (E := E)) := by
  intro ξ₁ ξ₂ h
  funext y
  rw [← f.φ.apply_symm_apply y]
  set x := f.φ.symm y
  ext v
  have h1 := congrArg (fun ξ => ξ x (f.symm.T (f.φ x) v)) h
  simpa only [pullbackForm, ContinuousLinearMap.comp_apply, f.T_symm_T] using h1

end NodalSurface.Iso

namespace StableMap

variable {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ} (J : AlmostComplexStructure E Q)

/-- `∂̄_J` of a stable map, on its domain. -/
abbrev dbar (α : StableMap om m k δ) : α.dom.S → E2 →L[ℝ] E := α.dom.dbar J α.u

/-- **`∂̄_J` is natural under isomorphisms of stable maps** (Memoir p. 8: `∂̄_J([α]) =
[α, ∂̄_{J,j}(u)]` is well defined): for `φ : α → α'`, `∂̄(u') ∘ Tφ = ∂̄(u)`. -/
theorem Iso.dbar_comp {α β : StableMap om m k δ} (f : Iso α β) (x : α.dom.S) :
    (β.dbar J (f.φ.φ x)).comp (f.φ.T x) = α.dbar J x := by
  have hu : α.u = β.u ∘ f.φ.φ := funext fun x => (f.comm x).symm
  rw [dbar, dbar, hu]
  exact f.φ.dbar_comp J β.u x

theorem Iso.pullbackForm_dbar {α β : StableMap om m k δ} (f : Iso α β) :
    f.φ.pullbackForm (β.dbar J) = α.dbar J :=
  funext (f.dbar_comp J)

/-- `α` is `J`-holomorphic: `∂̄_J(α) = 0`, the solutions of the Cauchy–Riemann section. -/
def IsHolomorphic (α : StableMap om m k δ) : Prop := ∀ x, α.dbar J x = 0

/-- Being holomorphic is invariant under isomorphisms. -/
theorem Iso.isHolomorphic_iff {α β : StableMap om m k δ} (f : Iso α β) :
    α.IsHolomorphic J ↔ β.IsHolomorphic J := by
  constructor
  · intro h y
    rw [← f.φ.φ.apply_symm_apply y]
    set x := f.φ.φ.symm y
    have h1 := f.dbar_comp J x
    rw [h x] at h1
    ext v
    have h2 := congrArg (fun L => L (f.φ.symm.T (f.φ.φ x) v)) h1
    simpa only [ContinuousLinearMap.comp_apply, f.φ.T_symm_T, zero_apply] using h2
  · intro h x
    rw [← f.dbar_comp J x, h]
    rfl

end StableMap

/-! ### The fibre of `W` -/

namespace NodalSurface

variable {m : ℕ} (X : NodalSurface m)

/-- `(s, t) ↦ Tψ(u(σ(s, t))) ξ(σ(s, t))(∂_s σ(s, t))`, `ψ` the chart of `Q` at `u(x)` and
`σ` the polar coordinates of `φ` (Memoir p. 7). -/
def formInPolar (u : X.S → Q) (ξ : X.S → E2 →L[ℝ] E) (φ : OpenPartialHomeomorph X.S ℂ)
    (x : X.S) (p : ℝ × ℝ) : E :=
  tangentCoordChange 𝓘(ℝ, E) (u (X.polar φ p)) (u x) (u (X.polar φ p))
    (ξ (X.polar φ p) (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar φ) p (1, 0)))

theorem formInPolar_zero (u : X.S → Q) (φ : OpenPartialHomeomorph X.S ℂ) (x : X.S) (p : ℝ × ℝ) :
    X.formInPolar u (fun _ => (0 : E2 →L[ℝ] E)) φ x p = 0 :=
  map_zero (tangentCoordChange 𝓘(ℝ, E) _ _ _)

/-- **`ξ` is of class `(k, δ)` at the nodal point `x`** (Memoir p. 7), as for maps
(`IsClassNear`): in honest holomorphic polar coordinates at `x` (`e^{-2π(s+it)}` in the image of
the chart for `s ≥ s₀`) and the chart of `Q` at `u(x)`, a cut-off of `formInPolar` lies in
`H^{k,δ}(ℝ × S¹)`. -/
def IsFormClassNear (k : ℕ) (δ : ℝ) (u : X.S → Q) (ξ : X.S → E2 →L[ℝ] E) (x : X.S) : Prop :=
  ∃ φ, X.IsHolChart φ x ∧ ∃ s₀ : ℝ,
    (∀ p : ℝ × ℝ, s₀ ≤ p.1 → expPolar p ∈ φ.target ∧
      u (X.polar φ p) ∈ (extChartAt 𝓘(ℝ, E) (u x)).source) ∧
    ∀ ℓ : E →L[ℝ] ℝ, MemH k δ fun p => Real.smoothTransition (p.1 - s₀) *
      ℓ (X.formInPolar u ξ φ x p)

/-- **`ξ` is of class `H^k_loc` near `x`**: in the chart of `S` at `x` (placed in the strip, as
for `IsHlocNear`) and the chart of `Q` at `u(x)`, the cut-offs of `ξ(∂_i)`, `i = 0, 1`, lie in
`H^{k,0}(ℝ × S¹)`. -/
def IsFormHlocNear (k : ℕ) (u : X.S → Q) (ξ : X.S → E2 →L[ℝ] E) (x : X.S) : Prop :=
  ∃ ε > 0, (∀ p : ℝ × ℝ, p.1 ^ 2 + (p.2 - 1/2) ^ 2 < 1/8 →
      X.place x ε p ∈ (extChartAt 𝓘(ℝ, E2) x).target ∧
      u ((extChartAt 𝓘(ℝ, E2) x).symm (X.place x ε p)) ∈ (extChartAt 𝓘(ℝ, E) (u x)).source) ∧
    ∀ (i : Fin 2) (ℓ : E →L[ℝ] ℝ), MemH k 0 fun p =>
      Real.smoothTransition (2 - 16 * (p.1 ^ 2 + (p.2 - 1/2) ^ 2)) *
      ℓ (let y := (extChartAt 𝓘(ℝ, E2) x).symm (X.place x ε p)
        tangentCoordChange 𝓘(ℝ, E) (u y) (u x) (u y)
          (ξ y (tangentCoordChange 𝓘(ℝ, E2) x y y (EuclideanSpace.single i 1))))

end NodalSurface

section Fibre

variable {om : SymplecticForm E Q} {m k' : ℕ} {δ' : ℝ} (J : AlmostComplexStructure E Q)

/-- **An element of the fibre of `W` over `α`, of class `(k, δ)`** (Memoir §1.2, p. 7): `ξ(z)`
anti-linear for `z ∉ |D|`, of class `H^k_loc` off the nodes and of class `(k, δ)` at the nodal
points.  The fibre on bi-level `(m, k)` is `IsFibreElement J α (k + 2) (δ_k)`. -/
def IsFibreElement (α : StableMap om m k' δ') (k : ℕ) (δ : ℝ) (ξ : α.dom.S → E2 →L[ℝ] E) :
    Prop :=
  (∀ x, (∀ p ∈ α.dom.nodes, x ∉ p) → ξ x ∈ α.dom.antiLinearForms J (α.u x) x) ∧
    (∀ p ∈ α.dom.nodes, ∀ x ∈ p, α.dom.IsFormClassNear k δ α.u ξ x) ∧
    ∀ x, (∀ p ∈ α.dom.nodes, x ∉ p) → α.dom.IsFormHlocNear k α.u ξ x

theorem memH_zero (k : ℕ) (δ : ℝ) : MemH k δ fun _ => 0 := by
  convert memH_cutoff_mul_const k δ 0 using 1
  funext p
  simp

/-- **The zero section**: `0` is an element of every fibre, for every `(k, δ)`; the charts are
those of `α` (Definition 1.4). -/
theorem isFibreElement_zero (α : StableMap om m k' δ') (k : ℕ) (δ : ℝ) :
    IsFibreElement J α k δ fun _ => 0 := by
  refine ⟨fun x _ => Submodule.zero_mem _, fun p hp x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨φ, hφ, s₀, hs, -⟩ := α.nodal p hp x hx
    refine ⟨φ, hφ, s₀, hs, fun ℓ => ?_⟩
    convert memH_zero k δ using 1
    funext p
    rw [NodalSurface.formInPolar_zero]
    simp
  · obtain ⟨ε, hε, hs, -⟩ := α.regular x hx
    refine ⟨ε, hε, hs, fun i ℓ => ?_⟩
    convert memH_zero k 0 using 1
    funext p
    simp

end Fibre

/-! ### Solutions exist -/

section Witness

variable (om : SymplecticForm E Q) (J : AlmostComplexStructure E Q)

/-- **The constant stable maps solve `∂̄_J = 0`**: the solution sets are not empty. -/
theorem isHolomorphic_constStableMap (q : Q) (k : ℕ) (δ : ℝ) :
    (constStableMap om q k δ).IsHolomorphic J := fun x =>
  (constStableMap om q k δ).dom.dbar_const J q x

/-- The constant map on the noded sphere solves `∂̄_J = 0`. -/
theorem isHolomorphic_nodalStableMap (q : Q) (k : ℕ) (δ : ℝ) :
    (nodalStableMap om q k δ).IsHolomorphic J := fun x =>
  (nodalStableMap om q k δ).dom.dbar_const J q x

end Witness

end GWMemoir
