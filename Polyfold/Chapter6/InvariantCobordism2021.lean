import Polyfold.Chapter6.InvariantSingle2021
import Polyfold.Chapter6.InvariantProductEnds2021b
import Polyfold.Chapter6.ProperHomotopy2021

/-!
# 2021 Theorem 6.7.1, the cobordism argument: `Ψ` does not depend on the choices

The proof of 2021 Theorem 6.7.1 (p. 277–279; preprint Theorem 6.43) compares the invariants of
two admissible sections `s₀`, `s₁` through the cobordism `S_F ⊆ ℝ¹ × X`, the solution set of
`F = f̃ + Ŝ` (`IsCobordismData`, Remark 5.3.8): with a cut-off `g(t)`, Stokes' theorem on `S_F`
and the product structure of its ends give, for a closed relative form `(ω, τ)`,

  `∫_{S₀} ω − ∫_{∂S₀} τ = ∫_{S₁} ω − ∫_{∂S₁} τ`.

This file proves that identity and, with it, parts (A) and (B) of the plan (`psiAt` of
`InvariantSingle2021` is the same for `s₀` and `s₁`, and is invariant under proper oriented
homotopies), modulo two inputs that are not in the library:

* the orientation of `S_F` (gap G.66, Remark 6.6.19) with its product form `e ∧ o` on the ends
  (`CobordismOrientation`);
* the relative form on `S_F`: a closed form `A = p₁^*ω − dβ` on `S_F` with vanishing face
  restriction that reads as `ω|_{S_i} − dβ_i` on the ends (`CobordismRelativeForms`). This needs
  the pull-back of forms on `∂X` to `∂(ℝ¹ × X)` (not in the library, see `w3b2-ends.md`).

Both are stated as `def`s so they can be discharged later; `psiAt_eq_of_admissible_hyp` and
`psiAt_eq_of_homotopy_hyp` are parts (A) and (B) under these hypotheses.

The route (which avoids a face-form Fubini on `∂S_F`): the invariant is the integral over `S_i`
of the closed form `a_i = ω|_{S_i} + dγ_i` with `γ_i` an extension of `−τ|_{∂S_i}`
(`IsPsiIntegrand`, `IsPsiIntegrand.psiAt_eq`). For the closed form `A` on `S_F` with `j^*A = 0`
reading as `a_i` on the ends, and the cut-off `g = g₀ − g₁` (`cutRise`),
`∫_{S_F} d(gA) = ∫_{∂S_F} gA = 0` (`boundaryIntegral_congr_face`), while
`∫_{S_F} d(g_i A) = ∫_{S_i} a_i` by `ProductEnd.integral_end_fubini`
(`integral_eq_of_cutCobordism`).
-/

open Set Filter Topology Manifold Module MeasureTheory

noncomputable section

namespace Polyfold

universe u v

local notation "𝓠" => modelWithCornersEuclideanQuadrant

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### The cut-off function -/

section CutRise

/-- **The cut-off `g` of the cobordism argument** (proof of 2021 Theorem 6.7.1, p. 278): a `C^∞`
function equal to `0` for `t ≤ (2a + b)/3` and to `1` for `t ≥ (a + 2b)/3`, so that `g′` is
supported in `(a, b)` and `∫ₐᵇ g′ = 1`. -/
def cutRise (a b t : ℝ) : ℝ := Real.smoothTransition ((3 * t - 2 * a - b) / (b - a))

theorem contDiff_cutRise (a b : ℝ) : ContDiff ℝ ∞ (cutRise a b) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)

theorem cutRise_eq_zero {a b t : ℝ} (hab : a < b) (ht : t ≤ (2 * a + b) / 3) :
    cutRise a b t = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem cutRise_eq_one {a b t : ℝ} (hab : a < b) (ht : (a + 2 * b) / 3 ≤ t) :
    cutRise a b t = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by linarith)).2 (by linarith))

/-- `∫ₐᵇ g′ = g(b) − g(a) = 1`. -/
theorem integral_deriv_cutRise {a b : ℝ} (hab : a < b) :
    ∫ t in Ioo a b, deriv (cutRise a b) t = 1 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_deriv_eq_sub' _ rfl
      (fun x _ => (contDiff_cutRise a b).differentiable (by simp) x)
      ((contDiff_cutRise a b).continuous_deriv (by simp)).continuousOn,
    cutRise_eq_one hab (by linarith), cutRise_eq_zero hab (by linarith), sub_zero]

end CutRise

/-! ### Locality of `d` and the support of `d(g(t) A)` -/

namespace ManifoldForm

section Locality

variable {n k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]

/-- **`d` is local**: two `C¹` forms that agree near `x` have the same `dω` at `x`. -/
theorem extDeriv_eq_of_eventuallyEq {ω ω' : ManifoldForm (𝓠 n) M k}
    (hω : ContMDiffForm (𝓠 n) 1 ω) (hω' : ContMDiffForm (𝓠 n) 1 ω') {x : M}
    (h : ∀ᶠ y in 𝓝 x, ω y = ω' y) : extDeriv ω x = extDeriv ω' x := by
  have h1 : ω' = ω + ((-1 : ℝ) • ω + ω') := by
    funext y
    rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply]
    module
  have h2 : ContMDiffForm (𝓠 n) 1 ((-1 : ℝ) • ω + ω') := (contMDiffForm_smul (-1) hω).add hω'
  have h3 : extDeriv ((-1 : ℝ) • ω + ω') x = 0 :=
    extDeriv_eq_zero_of_eventually_eq_zero (h.mono fun y hy => by
      rw [Pi.add_apply, Pi.smul_apply, hy]
      module)
  calc extDeriv ω x = extDeriv ω x + extDeriv ((-1 : ℝ) • ω + ω') x := by rw [h3, add_zero]
    _ = extDeriv (ω + ((-1 : ℝ) • ω + ω')) x := by rw [extDeriv_add hω h2, Pi.add_apply]
    _ = extDeriv ω' x := by rw [← h1]

/-- The closed support of `g ∘ τ` lies in `τ⁻¹[l, u]` when `g` vanishes outside `[l, u]`. -/
theorem tsupport_comp_subset {τ : M → ℝ} (hτ : Continuous τ) {g : ℝ → ℝ} {l u : ℝ}
    (hg : ∀ t, t ∉ Icc l u → g t = 0) :
    _root_.tsupport (fun p => g (τ p)) ⊆ τ ⁻¹' Icc l u :=
  closure_minimal (fun _ hp => by_contra fun h => Function.mem_support.1 hp (hg _ h))
    (isClosed_Icc.preimage hτ)

/-- **The support of `d(g(t) A)` for a closed form `A`** lies where `g ∘ τ` is neither `0` nor
`1`: `d(gA) = dg ∧ A` (the cut-off computation of 2021 p. 278). -/
theorem tsupport_extDeriv_smulFun_subset {τ : M → ℝ} (hτ : Continuous τ) {g : ℝ → ℝ} {l u : ℝ}
    (hg0 : ∀ t, t ≤ l → g t = 0) (hg1 : ∀ t, u ≤ t → g t = 1) {A : ManifoldForm (𝓠 n) M k}
    (hA : ContMDiffForm (𝓠 n) 1 A) (hA0 : extDeriv A = 0)
    (hgA : ContMDiffForm (𝓠 n) 1 (smulFun (fun p => g (τ p)) A)) :
    tsupport (extDeriv (smulFun (fun p => g (τ p)) A)) ⊆ τ ⁻¹' Icc l u := by
  refine closure_minimal (fun p hp => by_contra fun hp' => hp ?_) (isClosed_Icc.preimage hτ)
  show extDeriv (smulFun (fun p => g (τ p)) A) p = 0
  rcases not_and_or.1 hp' with h | h
  · refine extDeriv_eq_zero_of_eventually_eq_zero
      (((hτ.continuousAt.eventually_lt continuousAt_const (not_le.1 h))).mono fun y hy => ?_)
    rw [smulFun_apply, hg0 _ hy.le, zero_smul]
  · rw [extDeriv_eq_of_eventuallyEq hgA hA
      ((continuousAt_const.eventually_lt hτ.continuousAt (not_le.1 h)).mono fun y hy => by
        rw [smulFun_apply, hg1 _ hy.le, one_smul]), hA0, Pi.zero_apply]

end Locality

end ManifoldForm

/-! ### The cobordism identity on an abstract manifold with two product ends -/

section CutCobordism

open ManifoldForm

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (k + 1)) M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanQuadrant k) N] {a b : ℝ}

/-- **A cut end**: a product end `E ≅ (a, b) × N` of `M` on which `M` carries the product
orientation `e ∧ o_N`, the form `A` reads as the pull-back of `α`, and the time function `τ` is
the `(a, b)`-coordinate (with `τ⁻¹(a, b)` the end). -/
def ProductEnd.IsCutEnd (E : ProductEnd k N M a b) (τ : M → ℝ)
    (oM : TangentOrientation (𝓠 (k + 1)) M (k + 1)) (oN : TangentOrientation (𝓠 k) N k)
    (A : ManifoldForm (𝓠 (k + 1)) M k) (α : ManifoldForm (𝓠 k) N k) : Prop :=
  E.IsEndProductOrientation oM oN ∧ E.IsEndPullback A α ∧
    (∀ p ∈ E.φ.source, τ p = (E.φ p).1) ∧ ∀ p, τ p ∈ Ioo a b → p ∈ E.φ.source

/-- **`M` has a cut end over `N` on `τ⁻¹(a, b)`**: either `N = ∅` and `τ` does not take values in
`(a, b)`, or a product end `(a, b) × N` with the data of `ProductEnd.IsCutEnd`. The first case is
the end of the cobordism `S_F` at an empty `S_i`. -/
def HasCutEnd (a b : ℝ) (τ : M → ℝ) (oM : TangentOrientation (𝓠 (k + 1)) M (k + 1))
    (oN : TangentOrientation (𝓠 k) N k) (A : ManifoldForm (𝓠 (k + 1)) M k)
    (α : ManifoldForm (𝓠 k) N k) : Prop :=
  (IsEmpty N ∧ ∀ p : M, τ p ∉ Ioo a b) ∨ ∃ E : ProductEnd k N M a b, E.IsCutEnd τ oM oN A α

variable [IsManifold (𝓠 (k + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M]
  {oM : TangentOrientation (𝓠 (k + 1)) M (k + 1)}

/-- `∫_M 0 = 0`. -/
theorem integral_zero_form_of_isContinuous (hoM : oM.IsContinuous (𝓠 (k + 1)) ∞) :
    integral oM (0 : ManifoldForm (𝓠 (k + 1)) M (k + 1)) = 0 := by
  have := integral_finsetSum hoM (∅ : Finset ℕ)
    (ω := fun _ => (0 : ManifoldForm (𝓠 (k + 1)) M (k + 1))) (by simp) (by simp)
  simpa using this

/-- **`∫_M d(g(t) A) = ∫_N α` on a cut end** (the end computation of 2021 p. 278: with `g = cutRise`,
`d(gA) = g′(t) dt ∧ A` is supported in the end, where it is `g′(t) dt ∧ p₁^*α`, and
`∫ g′ = 1`; `ProductEnd.integral_end_fubini`). -/
theorem integral_extDeriv_smulFun_cutRise [IsManifold (𝓠 k) ∞ N] [T2Space N]
    [SigmaCompactSpace N] {oN : TangentOrientation (𝓠 k) N k}
    (hoM : oM.IsContinuous (𝓠 (k + 1)) ∞) (hoN : oN.IsContinuous (𝓠 k) ∞) {τ : M → ℝ}
    (hτ : ContMDiff (𝓠 (k + 1)) 𝓘(ℝ) ∞ τ) (hslab : ∀ c d : ℝ, IsCompact {p : M | τ p ∈ Icc c d})
    {A : ManifoldForm (𝓠 (k + 1)) M k} (hA : ContMDiffForm (𝓠 (k + 1)) ∞ A)
    (hA0 : extDeriv A = 0) {α : ManifoldForm (𝓠 k) N k} (hα : ContMDiffForm (𝓠 k) 1 α)
    (hαc : IsCompact (tsupport α)) (hab : a < b) (hE : HasCutEnd a b τ oM oN A α) :
    integral oM (extDeriv (smulFun (fun p => cutRise a b (τ p)) A)) = integral oN α := by
  have hg := contDiff_cutRise a b
  have hfA : ContMDiffForm (𝓠 (k + 1)) 1 (smulFun (fun p => cutRise a b (τ p)) A) :=
    (hA.smulFun le_rfl (hg.contMDiff.comp hτ)).of_le (by simp)
  have hsupp := tsupport_extDeriv_smulFun_subset hτ.continuous
    (fun t ht => cutRise_eq_zero hab ht) (fun t ht => cutRise_eq_one hab ht)
    (hA.of_le (by simp)) hA0 hfA
  rcases hE with ⟨hN, hτN⟩ | ⟨E, hor, hpull, hφτ, hsrc⟩
  · have h0 : extDeriv (smulFun (fun p => cutRise a b (τ p)) A) = 0 := by
      funext p
      refine eq_zero_of_notMem_tsupport fun hp => hτN p ?_
      have := hsupp hp
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    rw [h0, integral_zero_form_of_isContinuous hoM, ManifoldForm.integral_of_isEmpty]
  · have hΘc : IsCompact (tsupport (extDeriv (smulFun (fun p => cutRise a b (τ p)) A))) :=
      (hslab _ _).of_isClosed_subset isClosed_closure hsupp
    have hΘs : tsupport (extDeriv (smulFun (fun p => cutRise a b (τ p)) A)) ⊆ E.φ.source :=
      fun p hp => hsrc p ⟨lt_of_lt_of_le (by linarith) (hsupp hp).1,
        lt_of_le_of_lt (hsupp hp).2 (by linarith)⟩
    rw [E.integral_end_fubini hoM hoN hor (contMDiffForm_zero_extDeriv hfA) hΘc hΘs
      (hα.of_le (by simp)) hαc (deriv (cutRise a b)) (fun y₀ y hy =>
        E.chartForm_extDeriv_smulFun_stdFrame hα hpull (hg.differentiable (by simp))
          (fun p hp => by rw [hφτ p hp]) hfA y₀ hy),
      integral_deriv_cutRise hab, one_mul]

/-- **`∫_M d(fA) = 0`** for a compactly supported `f` and a `C^∞` form `A` whose restriction to
the faces vanishes: `∫_M d(fA) = ∫_{∂M} fA = 0` (Stokes, `boundaryIntegral_congr_face`). This is
the step `∫_{∂S_F} g (p₁^*ω − dβ) = 0` of 2021 p. 278. -/
theorem integral_extDeriv_smulFun_eq_zero_of_faces (hoM : oM.IsContinuous (𝓠 (k + 1)) ∞)
    {f : M → ℝ} (hf : ContMDiff (𝓠 (k + 1)) 𝓘(ℝ) ∞ f) (hfc : HasCompactSupport f)
    {A : ManifoldForm (𝓠 (k + 1)) M k} (hA : ContMDiffForm (𝓠 (k + 1)) ∞ A)
    (hface : ∀ x i, EqOn (faceRestriction A x i) 0
      (openFaceDomain (chartAt (EuclideanQuadrant (k + 1)) x) i)) :
    integral oM (extDeriv (smulFun f A)) = 0 := by
  have hfA : ContMDiffForm (𝓠 (k + 1)) 1 (smulFun f A) := (hA.smulFun le_rfl hf).of_le (by simp)
  have hc : IsCompact (tsupport (smulFun f A)) := hfc.isCompact.of_isClosed_subset
    isClosed_closure ((tsupport_smulFun_subset f A).trans inter_subset_left)
  have h0c : IsCompact (tsupport (0 : ManifoldForm (𝓠 (k + 1)) M k)) := by
    have : tsupport (0 : ManifoldForm (𝓠 (k + 1)) M k) = ∅ := by
      simp [ManifoldForm.tsupport, ManifoldForm.support]
    rw [this]; exact isCompact_empty
  have h0 : boundaryIntegral oM (0 : ManifoldForm (𝓠 (k + 1)) M k) = 0 := by
    have := boundaryIntegral_const_smul hoM (contMDiffForm_zero_form 1) h0c (0 : ℝ)
    rwa [zero_smul, zero_mul] at this
  rw [integral_extDeriv_eq_boundaryIntegral hoM hfA hc, ← h0]
  refine boundaryIntegral_congr_face hoM hfA (contMDiffForm_zero_form 1) hc h0c
    fun x i u hu => ?_
  rw [faceRestriction_smulFun, faceRestriction_zero]
  simp [smulFace, hface x i hu]

/-- **The cobordism identity** (the core of the proof of 2021 Theorem 6.7.1, p. 278; preprint
Theorem 6.43): if the `(k+1)`-manifold `M` has cut ends over `N₀` on `τ⁻¹(a₀, b₀)` and over `N₁`
on `τ⁻¹(a₁, b₁)`, the slabs `τ⁻¹[c, d]` are compact, and `A` is a closed `C^∞` `k`-form on `M`
with vanishing face restriction reading as `α₀`, `α₁` on the ends, then
`∫_{N₀} α₀ = ∫_{N₁} α₁`. Proof: with `g = g₀ − g₁` (`cutRise`), `gA` has compact support and
`∫_M d(gA) = ∫_{∂M} gA = 0`, while `∫_M d(g_i A) = ∫_{N_i} α_i`. -/
theorem integral_eq_of_cutCobordism {N₀ : Type*} [TopologicalSpace N₀]
    [ChartedSpace (EuclideanQuadrant k) N₀] [IsManifold (𝓠 k) ∞ N₀] [T2Space N₀]
    [SigmaCompactSpace N₀] {N₁ : Type*} [TopologicalSpace N₁]
    [ChartedSpace (EuclideanQuadrant k) N₁] [IsManifold (𝓠 k) ∞ N₁] [T2Space N₁]
    [SigmaCompactSpace N₁] {oN₀ : TangentOrientation (𝓠 k) N₀ k}
    {oN₁ : TangentOrientation (𝓠 k) N₁ k} {a₀ b₀ a₁ b₁ : ℝ} (hab₀ : a₀ < b₀) (hab₁ : a₁ < b₁)
    (hoM : oM.IsContinuous (𝓠 (k + 1)) ∞) (hoN₀ : oN₀.IsContinuous (𝓠 k) ∞)
    (hoN₁ : oN₁.IsContinuous (𝓠 k) ∞) {τ : M → ℝ} (hτ : ContMDiff (𝓠 (k + 1)) 𝓘(ℝ) ∞ τ)
    (hslab : ∀ c d : ℝ, IsCompact {p : M | τ p ∈ Icc c d}) {A : ManifoldForm (𝓠 (k + 1)) M k}
    (hA : ContMDiffForm (𝓠 (k + 1)) ∞ A) (hA0 : extDeriv A = 0)
    (hface : ∀ x i, EqOn (faceRestriction A x i) 0
      (openFaceDomain (chartAt (EuclideanQuadrant (k + 1)) x) i))
    {α₀ : ManifoldForm (𝓠 k) N₀ k} (hα₀ : ContMDiffForm (𝓠 k) 1 α₀)
    (hα₀c : IsCompact (tsupport α₀)) {α₁ : ManifoldForm (𝓠 k) N₁ k}
    (hα₁ : ContMDiffForm (𝓠 k) 1 α₁) (hα₁c : IsCompact (tsupport α₁))
    (hE₀ : HasCutEnd a₀ b₀ τ oM oN₀ A α₀) (hE₁ : HasCutEnd a₁ b₁ τ oM oN₁ A α₁) :
    integral oN₀ α₀ = integral oN₁ α₁ := by
  rw [← integral_extDeriv_smulFun_cutRise hoM hoN₀ hτ hslab hA hA0 hα₀ hα₀c hab₀ hE₀,
    ← integral_extDeriv_smulFun_cutRise hoM hoN₁ hτ hslab hA hA0 hα₁ hα₁c hab₁ hE₁]
  set g : ℝ → ℝ := fun t => cutRise a₀ b₀ t - cutRise a₁ b₁ t with hg_def
  have hg : ContDiff ℝ ∞ g := (contDiff_cutRise _ _).sub (contDiff_cutRise _ _)
  have hsplit : smulFun (fun p => cutRise a₀ b₀ (τ p)) A =
      smulFun (fun p => g (τ p)) A + smulFun (fun p => cutRise a₁ b₁ (τ p)) A := by
    funext p
    simp only [Pi.add_apply, smulFun_apply, hg_def]
    module
  have hfA : ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h →
      ContMDiffForm (𝓠 (k + 1)) 1 (smulFun (fun p => h (τ p)) A) :=
    fun h hh => (hA.smulFun le_rfl (hh.contMDiff.comp hτ)).of_le (by simp)
  set l := min ((2 * a₀ + b₀) / 3) ((2 * a₁ + b₁) / 3)
  set u := max ((a₀ + 2 * b₀) / 3) ((a₁ + 2 * b₁) / 3)
  have hg0 : ∀ t, t ∉ Icc l u → g t = 0 := by
    intro t ht
    rcases not_and_or.1 ht with h | h
    · have h := not_le.1 h
      rw [hg_def]
      show cutRise a₀ b₀ t - cutRise a₁ b₁ t = 0
      rw [cutRise_eq_zero hab₀ (le_trans h.le (min_le_left _ _)),
        cutRise_eq_zero hab₁ (le_trans h.le (min_le_right _ _)), sub_zero]
    · have h := not_le.1 h
      rw [hg_def]
      show cutRise a₀ b₀ t - cutRise a₁ b₁ t = 0
      rw [cutRise_eq_one hab₀ (le_trans (le_max_left _ _) h.le),
        cutRise_eq_one hab₁ (le_trans (le_max_right _ _) h.le), sub_self]
  have hgc : HasCompactSupport fun p => g (τ p) :=
    (hslab l u).of_isClosed_subset isClosed_closure (tsupport_comp_subset hτ.continuous hg0)
  rw [hsplit, extDeriv_add (hfA _ hg) (hfA _ (contDiff_cutRise _ _)),
    integral_add hoM (contMDiffForm_zero_extDeriv (hfA _ hg))
      (contMDiffForm_zero_extDeriv (hfA _ (contDiff_cutRise _ _)))
      (hgc.isCompact.of_isClosed_subset isClosed_closure
        ((tsupport_extDeriv_subset _).trans
          ((tsupport_smulFun_subset _ A).trans inter_subset_left)))
      ((hslab _ _).of_isClosed_subset isClosed_closure
        (tsupport_extDeriv_smulFun_subset hτ.continuous (fun t ht => cutRise_eq_zero hab₁ ht)
          (fun t ht => cutRise_eq_one hab₁ ht) (hA.of_le (by simp)) hA0
          (hfA _ (contDiff_cutRise _ _)))),
    integral_extDeriv_smulFun_eq_zero_of_faces hoM (f := fun p => g (τ p))
      (hg.contMDiff.comp hτ) hgc hA hface,
    zero_add]

end CutCobordism

/-! ### The integrand of `Ψ_s` as a closed form on `S_k` -/

section PsiIntegrand

open MPolyfold StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f s : X → Y} {N : B.One → ℝ} {U : Set X}
  (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hs : B.IsAdmissible f N U s) (o : SectionOrientation f hf.toIsScFredholmSection)

/-- **The integrand of `Ψ_s` on `S_k`** (proof of 2021 Theorem 6.7.1, p. 277–278, the
form `ω − dβ` with `j^*β = τ`): a form `a` on `S_k` is an integrand for the closed relative form
`c = (ω, τ)` if `a = ω|_{S_k}` in degree `0`, and in degree `m + 1` if `a = ω|_{S} + dγ` for a
`C^∞` compactly supported form `γ` on `S` extending `−τ|_{∂S}` (`solFaceForm`, `IsExtendedBy`).
Then `Ψ_s([c]) = ∫_{S_k} a` (`IsPsiIntegrand.psiAt_eq`). -/
def IsPsiIntegrand : ∀ (k : ℕ), LinearMap.ker (relD hX k) →
    (letI := solPartChartedSpace hX hf hs k; ManifoldForm (𝓠 k) ↥(B.solPart f s k) k) → Prop
  | 0, c, a =>
    letI := solPartChartedSpace hX hf hs 0
    a = formsInftyRestrict 0 (hasCornerStructureOfDim_solPart hX hf hs 0) (c : RelForms hX 0)
  | m + 1, c, a =>
    letI := solPartChartedSpace hX hf hs (m + 1)
    ∃ γ : ManifoldForm (𝓠 (m + 1)) ↥(B.solPart f s (m + 1)) m,
      ManifoldForm.ContMDiffForm (𝓠 (m + 1)) ∞ γ ∧ IsCompact (ManifoldForm.tsupport γ) ∧
      IsExtendedBy ((-1 : ℝ) • (solFaceForm (hasCornerStructureOfDim_solPart hX hf hs (m + 1)) hX
        (degIndex_solPart hX hf hs (m + 1)) rfl (c : RelForms hX (m + 1)).2 :
          FaceFormData ↥(B.solPart f s (m + 1)) m m)) γ ∧
      a = formsInftyRestrict (m + 1) (hasCornerStructureOfDim_solPart hX hf hs (m + 1))
        (c : RelForms hX (m + 1)).1 + ManifoldForm.extDeriv γ

/-- **Integrands exist** (`exists_extension` on the compact `S_{m+1}`). -/
theorem exists_isPsiIntegrand (hS : IsCompact (solutionSet P (sectionAdd P f s))) (k : ℕ)
    (c : LinearMap.ker (relD hX k)) :
    letI := solPartChartedSpace hX hf hs k
    ∃ a : ManifoldForm (𝓠 k) ↥(B.solPart f s k) k, IsPsiIntegrand hX hf hs k c a := by
  cases k with
  | zero => exact ⟨_, rfl⟩
  | succ m =>
    let := solPartChartedSpace hX hf hs (m + 1)
    have := isManifold_solPart hX hf hs (m + 1)
    have := isCompact_iff_compactSpace.1 (isCompact_solPart hf hs.isScPlusSection hs.gp hS (m + 1))
    obtain ⟨γ, hγ, hγc, hext⟩ := exists_extension
      (σ := (-1 : ℝ) • (solFaceForm (hasCornerStructureOfDim_solPart hX hf hs (m + 1)) hX
        (degIndex_solPart hX hf hs (m + 1)) rfl (c : RelForms hX (m + 1)).2 :
          FaceFormData ↥(B.solPart f s (m + 1)) m m))
      ((-1 : ℝ) • solFaceForm (hasCornerStructureOfDim_solPart hX hf hs (m + 1)) hX
        (degIndex_solPart hX hf hs (m + 1)) rfl (c : RelForms hX (m + 1)).2).2
      (hasCompactFaceSupport_of_compactSpace _)
    exact ⟨_, γ, hγ, hγc, hext, rfl⟩

/-- An integrand is `C^∞`. -/
theorem IsPsiIntegrand.contMDiffForm {k : ℕ} {c : LinearMap.ker (relD hX k)}
    {a : (letI := solPartChartedSpace hX hf hs k; ManifoldForm (𝓠 k) ↥(B.solPart f s k) k)}
    (h : IsPsiIntegrand hX hf hs k c a) :
    letI := solPartChartedSpace hX hf hs k
    ManifoldForm.ContMDiffForm (𝓠 k) ∞ a := by
  cases k with
  | zero =>
    let := solPartChartedSpace hX hf hs 0
    rw [h]
    exact contMDiffForm_formsInftyRestrict rfl _
  | succ m =>
    obtain ⟨γ, hγ, -, -, rfl⟩ := h
    let := solPartChartedSpace hX hf hs (m + 1)
    have := isManifold_solPart hX hf hs (m + 1)
    exact (contMDiffForm_formsInftyRestrict rfl _).add
      (ManifoldForm.ContMDiffForm.extDeriv (hγ.of_le (by simp)))

include hbump in
/-- **`Ψ_s([c]) = ∫_{S_k} a`** for an integrand `a` of `c` (2021 (6.35), p. 277): in degree
`m + 1`, `∫_{∂S} τ = −∫_{∂S} (−τ) = −∫_{∂S} j^*γ = −∫_S dγ` (`faceIntegral_eq`, Stokes). -/
theorem IsPsiIntegrand.psiAt_eq (hS : IsCompact (solutionSet P (sectionAdd P f s))) {k : ℕ}
    {c : LinearMap.ker (relD hX k)}
    {a : (letI := solPartChartedSpace hX hf hs k; ManifoldForm (𝓠 k) ↥(B.solPart f s k) k)}
    (h : IsPsiIntegrand hX hf hs k c a) :
    letI := solPartChartedSpace hX hf hs k
    haveI := isManifold_solPart hX hf hs k
    psiAt hX hbump hf hs o k (relDeRhamMk hX k c) =
      ManifoldForm.integral (solPartOr hX hf hs o k) a := by
  cases k with
  | zero =>
    rw [h]
    exact psiAt_mk_zero hX hbump hf hs o hS c
  | succ m =>
    obtain ⟨γ, hγ, hγc, hext, rfl⟩ := h
    let := solPartChartedSpace hX hf hs (m + 1)
    have := isManifold_solPart hX hf hs (m + 1)
    have := isCompact_iff_compactSpace.1 (isCompact_solPart hf hs.isScPlusSection hs.gp hS (m + 1))
    have ho := isContinuous_solPartOr hX hbump hf hs o (m + 1)
    have hσ : IsChartFaceForm (solFaceForm (hasCornerStructureOfDim_solPart hX hf hs (m + 1)) hX
        (degIndex_solPart hX hf hs (m + 1)) rfl (c : RelForms hX (m + 1)).2 :
          FaceFormData ↥(B.solPart f s (m + 1)) m m) :=
      (solFaceForm (hasCornerStructureOfDim_solPart hX hf hs (m + 1)) hX
        (degIndex_solPart hX hf hs (m + 1)) rfl (c : RelForms hX (m + 1)).2).2
    have h1 := faceIntegral_eq ho (hγ.of_le (by simp)) hγc hext
    rw [faceIntegral_smul ho hσ (hasCompactFaceSupport_of_compactSpace _)] at h1
    rw [psiAt_mk_succ hX hbump hf hs o hS m c]
    change _ - faceIntegral (solPartOr hX hf hs o (m + 1)) _ = _
    rw [ManifoldForm.integral_add ho ((contMDiffForm_formsInftyRestrict rfl _).of_le (by simp))
      (ManifoldForm.contMDiffForm_zero_extDeriv (hγ.of_le (by simp))) isClosed_closure.isCompact
      isClosed_closure.isCompact,
      ManifoldForm.integral_extDeriv_eq_boundaryIntegral ho (hγ.of_le (by simp)) hγc, ← h1]
    ring

end PsiIntegrand

/-! ### The index-`(k+1)` part of the cobordism `S_F` and its product ends -/

section Cobordism

open MPolyfold StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
  (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
  {f₀ : X → Y} (hf₀ : B.IsScFredholmSectionTame f₀) {N₀ : B.One → ℝ} {U₀ : Set X} {s₀ : X → Y}
  (hs₀ : B.IsAdmissible f₀ N₀ U₀ s₀) (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
  {f₁ : X → Y} (hf₁ : B.IsScFredholmSectionTame f₁) {N₁ : B.One → ℝ} {U₁ : Set X} {s₁ : X → Y}
  (hs₁ : B.IsAdmissible f₁ N₁ U₁ s₁) (o₁ : SectionOrientation f₁ hf₁.toIsScFredholmSection)
  {σ₁ : X → Y} {Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
  (hC : B.IsCobordismData f₀ hf₀.isScSmooth.1 s₀ σ₁ Ŝ)
  (h₁ : sectionAdd P f₀ σ₁ = sectionAdd P f₁ s₁) (k : ℕ)

variable (Ŝ) in
/-- The open set `V'` of `ℝ¹ × X` cutting out the index-`(k+1)` part of `S_F`
(`solIndexNbhd` of `InvariantSingle2021` for the pulled-back bundle and `F = f̃₀ + Ŝ`). -/
def cobIndexNbhd : Set ((Fin 1 → ℝ) × X) :=
  (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).solIndexNbhd
    (paramLift f₀ hf₀.isScSmooth.1) Ŝ (k + 1)

variable (Ŝ) in
/-- **The index-`(k+1)` part `S_F^{k+1}` of the cobordism** `S_F = {F = 0}`, `F = f̃₀ + Ŝ`
(proof of 2021 Theorem 6.7.1, p. 278, with reading R-c: the `(k+1)`-dimensional part of `S_F`
is the cobordism between the `k`-dimensional parts of the ends). It is `solPart` of
`InvariantSingle2021` for `(f̃₀, Ŝ)` on `ℝ¹ × X`. -/
def cobPart : Set ((Fin 1 → ℝ) × X) :=
  solutionSet (pullbackProj P Prod.snd) (homotopySection f₀ hf₀.isScSmooth.1 Ŝ) ∩
    cobIndexNbhd hf₀ Ŝ k

theorem cobPart_eq_solPart :
    cobPart hf₀ Ŝ k = (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).solPart
      (paramLift f₀ hf₀.isScSmooth.1) Ŝ (k + 1) :=
  rfl

instance paracompactSpace_cobPart : ParacompactSpace ↥(cobPart hf₀ Ŝ k) :=
  ((rnPolyfold 1).prod PX).paracompactSpace_subtype _

include hC in
theorem isOpen_cobIndexNbhd : IsOpen (cobIndexNbhd hf₀ Ŝ k) :=
  isOpen_solIndexNbhd hf₀.param hC.isScPlusSection hC.gp (k + 1)

include hC in
/-- Every zero of `F` in `V'` has index `k + 1`. -/
theorem cobIndexNbhd_isLinOfIndex :
    ∀ z ∈ cobIndexNbhd hf₀ Ŝ k,
      IsZeroAt (pullbackProj P Prod.snd) (homotopySection f₀ hf₀.isScSmooth.1 Ŝ) z →
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
          (homotopySection f₀ hf₀.isScSmooth.1 Ŝ) z (k + 1 : ℕ) :=
  fun _ hz hz0 => isLinOfIndex_sectionAdd_of_isIndexAt hf₀.param.toIsScFredholmSection
    hC.isScPlusSection hz0 (mem_solPart_iff.1 ⟨hz0, hz⟩).2

include hC in
/-- `S_F^{k+1}` is closed in `ℝ¹ × X`. -/
theorem isClosed_cobPart : IsClosed (cobPart hf₀ Ŝ k) :=
  isClosed_solPart hf₀.param hC.isScPlusSection hC.gp (k + 1)

include hC in
/-- **`S_F^{k+1}` is a `(k+1)`-dimensional submanifold of `ℝ¹ × X`** (Theorem 3.6.8 on the open
part `V'`, `isSubmanifoldOfDim_inter_open`). -/
theorem isSubmanifoldOfDim_cobPart :
    ((rnPolyfold 1).prod PX).IsSubmanifoldOfDim (cobPart hf₀ Ŝ k) (k + 1) :=
  isSubmanifoldOfDim_inter_open (hC.isScFredholmSectionTame_homotopySection hf₀)
    (isOpen_cobIndexNbhd hf₀ hC k) (fun z _ hz => hC.gp z hz) (cobIndexNbhd_isLinOfIndex hf₀ hC k)

include hC in
theorem isSubMPolyfold_cobPart : ((rnPolyfold 1).prod PX).IsSubMPolyfold (cobPart hf₀ Ŝ k) :=
  (isSubmanifoldOfDim_cobPart hf₀ hC k).1.isSubMPolyfold

include hX hC in
/-- **The corner structure of dimension `k + 1` of `S_F^{k+1}`** (Theorem 4.2.7 on the tame
`ℝ¹ × X`, `prod_rn_isTame`). -/
theorem hasCornerStructureOfDim_cobPart :
    (subPolyfold (isSubMPolyfold_cobPart hf₀ hC k)).HasCornerStructureOfDim (k + 1) :=
  (isSubmanifoldOfDim_cobPart hf₀ hC k).hasCornerStructureOfDim_of_tame (prod_rn_isTame hX)
    (isGoodPositionAt_inter_open (prod_rn_isTame hX)
      (hC.isScFredholmSectionTame_homotopySection hf₀) (isOpen_cobIndexNbhd hf₀ hC k)
      fun z _ hz => hC.gp z hz)

/-- **The charted space of `S_F^{k+1}`**: the corner charts of its corner structure. -/
abbrev cobChartedSpace : ChartedSpace (EuclideanQuadrant (k + 1)) ↥(cobPart hf₀ Ŝ k) :=
  (subPolyfold (isSubMPolyfold_cobPart hf₀ hC k)).cornerChartedSpace
    (hasCornerStructureOfDim_cobPart hX hf₀ hC k)

theorem isManifold_cobPart :
    letI := cobChartedSpace hX hf₀ hC k
    IsManifold (𝓠 (k + 1)) ∞ ↥(cobPart hf₀ Ŝ k) :=
  letI := cobChartedSpace hX hf₀ hC k
  isManifold_of_eq (hasCornerStructureOfDim_cobPart hX hf₀ hC k) rfl

variable (Ŝ) in
/-- **The time function `t` on `S_F^{k+1}`.** -/
def cobTime (p : ↥(cobPart hf₀ Ŝ k)) : ℝ := p.1.1 0

theorem contMDiff_cobTime :
    letI := cobChartedSpace hX hf₀ hC k
    ContMDiff (𝓠 (k + 1)) 𝓘(ℝ) ∞ (cobTime hf₀ Ŝ k) :=
  letI := cobChartedSpace hX hf₀ hC k
  contMDiff_comp_time (hasCornerStructureOfDim_cobPart hX hf₀ hC k) rfl contDiff_id

include hC in
/-- **The slabs of `S_F^{k+1}` are compact** (`IsCobordismData.isCompact_slab`, and `S_F^{k+1}`
closed). -/
theorem isCompact_cobSlab (c d : ℝ) :
    IsCompact {p : ↥(cobPart hf₀ Ŝ k) | cobTime hf₀ Ŝ k p ∈ Icc c d} := by
  rw [Subtype.isCompact_iff]
  have : Subtype.val '' {p : ↥(cobPart hf₀ Ŝ k) | cobTime hf₀ Ŝ k p ∈ Icc c d} =
      slabZeros (homotopySection f₀ hf₀.isScSmooth.1 Ŝ) c d ∩ cobPart hf₀ Ŝ k := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p.2.1, hp⟩, p.2⟩
    · rintro ⟨⟨-, hz⟩, hz'⟩
      exact ⟨⟨z, hz'⟩, hz, rfl⟩
  rw [this]
  exact (hC.isCompact_slab c d).inter_right (isClosed_cobPart hf₀ hC k)

include hC in
/-- `S_F^{k+1}` is σ-compact (the union of its slabs). -/
theorem sigmaCompactSpace_cobPart : SigmaCompactSpace ↥(cobPart hf₀ Ŝ k) := by
  refine isSigmaCompact_iff_sigmaCompactSpace.1
    ⟨fun n : ℕ => slabZeros (homotopySection f₀ hf₀.isScSmooth.1 Ŝ) (-(n : ℝ)) n ∩
      cobPart hf₀ Ŝ k,
      fun n => (hC.isCompact_slab _ _).inter_right (isClosed_cobPart hf₀ hC k), ?_⟩
  refine Subset.antisymm (iUnion_subset fun n => inter_subset_right) fun z hz => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge |z.1 0|
  exact mem_iUnion.2 ⟨n, ⟨hz.1, abs_le.1 hn⟩, hz⟩

omit [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- For an admissible `s`, `x ∈ S_{f+s}` lies in `V_k` iff `(f + s)'(x)` has index `k`. -/
theorem mem_solIndexNbhd_iff_isLinOfIndex {X : Type u} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {B : StrongBundle PX P} {f s : X → Y} (hf : B.IsScFredholmSection f)
    (hs : B.IsScPlusSection s) (k : ℕ) :
    ∀ x ∈ solutionSet P (sectionAdd P f s),
      x ∈ B.solIndexNbhd f s k ↔ B.IsLinOfIndex (sectionAdd P f s) x k := fun x hx =>
  ⟨fun hV => (isIndexAt_iff_isLinOfIndex hf hs hx).1 (mem_solPart_iff.1 ⟨hx, hV⟩).2,
    fun h => (mem_solPart_iff.2 ⟨hx, (isIndexAt_iff_isLinOfIndex hf hs hx).2 h⟩).2⟩

include hC in
/-- Over `(a, b)`, `V'` cuts out the zeros of `F` of index `k + 1`. -/
theorem cobIndexNbhd_iff {a b : ℝ} :
    ∀ z ∈ solutionSet (pullbackProj P Prod.snd) (homotopySection f₀ hf₀.isScSmooth.1 Ŝ),
      z.1 0 ∈ Ioo a b → (z ∈ cobIndexNbhd hf₀ Ŝ k ↔
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
          (homotopySection f₀ hf₀.isScSmooth.1 Ŝ) z (k + 1 : ℕ)) :=
  fun z hz _ =>
    mem_solIndexNbhd_iff_isLinOfIndex hf₀.param.toIsScFredholmSection hC.isScPlusSection
      (k + 1) z hz

include hs₀ hC in
/-- Over `(0, 1/8)`, `z ∈ S_F^{k+1}` iff `z.2 ∈ S₀ = S_{f₀+s₀} ∩ V_k` (`solutionSet_end_iff`,
`hVend_left`). -/
theorem cobPart_end_left (z : (Fin 1 → ℝ) × X) (hz : z.1 0 ∈ Ioo (0 : ℝ) (1 / 8)) :
    z ∈ cobPart hf₀ Ŝ k ↔ z.2 ∈ B.solPart f₀ s₀ k :=
  solutionSet_end_iff ((isSection_pullbackLift _).sectionAdd hC.isSection)
    (hC.slice_left_Ioo le_rfl)
    (hC.hVend_left hf₀ le_rfl (mem_solIndexNbhd_iff_isLinOfIndex hf₀.toIsScFredholmSection
      hs₀.isScPlusSection k) (cobIndexNbhd_iff hf₀ hC k)) z hz

include hf₁ hs₁ hC h₁ in
/-- Over `(7/8, 1)`, `z ∈ S_F^{k+1}` iff `z.2 ∈ S₁ = S_{f₁+s₁} ∩ V_k`. -/
theorem cobPart_end_right (z : (Fin 1 → ℝ) × X) (hz : z.1 0 ∈ Ioo (7 / 8 : ℝ) 1) :
    z ∈ cobPart hf₀ Ŝ k ↔ z.2 ∈ B.solPart f₁ s₁ k := by
  have hVk : ∀ x ∈ solutionSet P (sectionAdd P f₀ σ₁),
      x ∈ B.solIndexNbhd f₁ s₁ k ↔ B.IsLinOfIndex (sectionAdd P f₀ σ₁) x k := by
    rw [h₁]
    exact mem_solIndexNbhd_iff_isLinOfIndex hf₁.toIsScFredholmSection hs₁.isScPlusSection k
  have := solutionSet_end_iff ((isSection_pullbackLift _).sectionAdd hC.isSection)
    (hC.slice_right_Ioo le_rfl) (hC.hVend_right hf₀ le_rfl hVk (cobIndexNbhd_iff hf₀ hC k)) z hz
  rwa [h₁] at this

/-- **The left end `(0, 1/8) × S₀` of `S_F^{k+1}`** as a `ProductEnd` (`productEndOfSub`, with
the charted spaces of `S₀ = S_{f₀+s₀} ∩ V_k` and `S_F^{k+1}`). The point `x₀` only fixes junk
values. -/
abbrev cobEndLeft (x₀ : ↥(B.solPart f₀ s₀ k)) :
    letI := solPartChartedSpace hX hf₀ hs₀ k
    letI := cobChartedSpace hX hf₀ hC k
    ProductEnd k ↥(B.solPart f₀ s₀ k) ↥(cobPart hf₀ Ŝ k) 0 (1 / 8) :=
  letI := solPartChartedSpace hX hf₀ hs₀ k
  letI := cobChartedSpace hX hf₀ hC k
  productEndOfSub (isSubMPolyfold_cobPart hf₀ hC k) (by norm_num)
    (cobPart_end_left hf₀ hs₀ hC k) x₀ (hasCornerStructureOfDim_solPart hX hf₀ hs₀ k)
    (hasCornerStructureOfDim_cobPart hX hf₀ hC k) rfl rfl

/-- **The right end `(7/8, 1) × S₁` of `S_F^{k+1}`** as a `ProductEnd`, over
`S₁ = S_{f₁+s₁} ∩ V_k` (with `f₀ + σ₁ = f₁ + s₁`). -/
abbrev cobEndRight (x₀ : ↥(B.solPart f₁ s₁ k)) :
    letI := solPartChartedSpace hX hf₁ hs₁ k
    letI := cobChartedSpace hX hf₀ hC k
    ProductEnd k ↥(B.solPart f₁ s₁ k) ↥(cobPart hf₀ Ŝ k) (7 / 8) 1 :=
  letI := solPartChartedSpace hX hf₁ hs₁ k
  letI := cobChartedSpace hX hf₀ hC k
  productEndOfSub (isSubMPolyfold_cobPart hf₀ hC k) (by norm_num)
    (cobPart_end_right hf₀ hf₁ hs₁ hC h₁ k) x₀ (hasCornerStructureOfDim_solPart hX hf₁ hs₁ k)
    (hasCornerStructureOfDim_cobPart hX hf₀ hC k) rfl rfl

/-- **The orientation of the cobordism `S_F`** (2021 Remark 6.6.19, p. 276, and the proof of
Theorem 6.7.1, p. 278; gap G.66): a continuous orientation of `S_F^{k+1}` which on the ends is
the product `e ∧ o_{S_i}` of the time direction with the orientations `solPartOr` of
`S₀ = S_{f₀+s₀}` and `S₁ = S_{f₁+s₁}` induced by `o₀`, `o₁` (`ProductEnd.IsEndProductOrientation`
of `InvariantProductEnds2021`). Not proved here: it needs `SectionOrientation.prodFirst` (wave
1c). For the data of part (1), `o₁ = o₀`; for part (2), `o₁ = o₀.sectionAdd S(1, ·)` and
`σ₁ = S(1, ·) + s₁`, so the orientation `e ∧ o₀.sectionAdd σ₁` of `S_F` at the right end is
`e ∧ o₁.sectionAdd s₁` (`orSectionAdd_apply`). -/
def CobordismOrientation : Prop :=
  letI := solPartChartedSpace hX hf₀ hs₀ k
  letI := solPartChartedSpace hX hf₁ hs₁ k
  letI := cobChartedSpace hX hf₀ hC k
  ∃ oM : TangentOrientation (𝓠 (k + 1)) ↥(cobPart hf₀ Ŝ k) (k + 1),
    oM.IsContinuous (𝓠 (k + 1)) ∞ ∧
    (∀ x₀ : ↥(B.solPart f₀ s₀ k),
      (cobEndLeft hX hf₀ hs₀ hC k x₀).IsEndProductOrientation oM (solPartOr hX hf₀ hs₀ o₀ k)) ∧
    ∀ x₀ : ↥(B.solPart f₁ s₁ k),
      (cobEndRight hX hf₀ hf₁ hs₁ hC h₁ k x₀).IsEndProductOrientation oM
        (solPartOr hX hf₁ hs₁ o₁ k)

/-- **The relative form on the cobordism** (the form `p₁^*ω − dβ` on `S_F` of 2021 p. 278, with
`j^*β = p₁^*τ` on `∂S_F`): for every closed relative form `c = (ω, τ)` of degree `k` and
integrands `a₀`, `a₁` of `c` on the ends (`IsPsiIntegrand`), a closed `C^∞` `k`-form `A` on
`S_F^{k+1}` with vanishing face restriction which reads as `a₀` and `a₁` on the two product ends
(`ProductEnd.IsEndPullback`). Not proved here: `A = p₁^*ω|_{S_F} + dγ_F` with `γ_F` an extension
of `−(p₁^*τ)|_{∂S_F}` glued from `p₁^*γ_i` on the ends; this needs the pull-back of forms on
`∂X` to `∂(ℝ¹ × X)` (see `w3b2-ends.md`). The part `p₁^*ω|_{S_F}` is available
(`isEndPullback_formsInftyRestrict_snd`). -/
def CobordismRelativeForms : Prop :=
  letI := solPartChartedSpace hX hf₀ hs₀ k
  letI := solPartChartedSpace hX hf₁ hs₁ k
  letI := cobChartedSpace hX hf₀ hC k
  ∀ (c : LinearMap.ker (relD hX k)) (a₀ : ManifoldForm (𝓠 k) ↥(B.solPart f₀ s₀ k) k)
    (a₁ : ManifoldForm (𝓠 k) ↥(B.solPart f₁ s₁ k) k),
    IsPsiIntegrand hX hf₀ hs₀ k c a₀ → IsPsiIntegrand hX hf₁ hs₁ k c a₁ →
    ∃ A : ManifoldForm (𝓠 (k + 1)) ↥(cobPart hf₀ Ŝ k) k,
      ManifoldForm.ContMDiffForm (𝓠 (k + 1)) ∞ A ∧ ManifoldForm.extDeriv A = 0 ∧
      (∀ x i, EqOn (faceRestriction A x i) 0
        (openFaceDomain (chartAt (EuclideanQuadrant (k + 1)) x) i)) ∧
      (∀ x₀ : ↥(B.solPart f₀ s₀ k), (cobEndLeft hX hf₀ hs₀ hC k x₀).IsEndPullback A a₀) ∧
      ∀ x₀ : ↥(B.solPart f₁ s₁ k), (cobEndRight hX hf₀ hf₁ hs₁ hC h₁ k x₀).IsEndPullback A a₁

/-- The left end is a cut end (`HasCutEnd`): the product end if `S₀ ≠ ∅`, and no point of
`S_F^{k+1}` over `(0, 1/8)` if `S₀ = ∅`. -/
theorem hasCutEnd_left :
    letI := solPartChartedSpace hX hf₀ hs₀ k
    letI := cobChartedSpace hX hf₀ hC k
    ∀ {oM : TangentOrientation (𝓠 (k + 1)) ↥(cobPart hf₀ Ŝ k) (k + 1)}
      {A : ManifoldForm (𝓠 (k + 1)) ↥(cobPart hf₀ Ŝ k) k}
      {a₀ : ManifoldForm (𝓠 k) ↥(B.solPart f₀ s₀ k) k},
      (∀ x₀ : ↥(B.solPart f₀ s₀ k),
        (cobEndLeft hX hf₀ hs₀ hC k x₀).IsEndProductOrientation oM (solPartOr hX hf₀ hs₀ o₀ k)) →
      (∀ x₀ : ↥(B.solPart f₀ s₀ k), (cobEndLeft hX hf₀ hs₀ hC k x₀).IsEndPullback A a₀) →
      HasCutEnd 0 (1 / 8) (cobTime hf₀ Ŝ k) oM (solPartOr hX hf₀ hs₀ o₀ k) A a₀ := by
  intro oM A a₀ hor hpull
  rcases isEmpty_or_nonempty ↥(B.solPart f₀ s₀ k) with hN | ⟨⟨x₀⟩⟩
  · exact Or.inl ⟨hN, fun p hp => hN.false ⟨_, (cobPart_end_left hf₀ hs₀ hC k p.1 hp).1 p.2⟩⟩
  · exact Or.inr ⟨cobEndLeft hX hf₀ hs₀ hC k x₀, hor x₀, hpull x₀, fun _ _ => rfl, fun _ hp => hp⟩

/-- The right end is a cut end. -/
theorem hasCutEnd_right :
    letI := solPartChartedSpace hX hf₁ hs₁ k
    letI := cobChartedSpace hX hf₀ hC k
    ∀ {oM : TangentOrientation (𝓠 (k + 1)) ↥(cobPart hf₀ Ŝ k) (k + 1)}
      {A : ManifoldForm (𝓠 (k + 1)) ↥(cobPart hf₀ Ŝ k) k}
      {a₁ : ManifoldForm (𝓠 k) ↥(B.solPart f₁ s₁ k) k},
      (∀ x₀ : ↥(B.solPart f₁ s₁ k),
        (cobEndRight hX hf₀ hf₁ hs₁ hC h₁ k x₀).IsEndProductOrientation oM
          (solPartOr hX hf₁ hs₁ o₁ k)) →
      (∀ x₀ : ↥(B.solPart f₁ s₁ k), (cobEndRight hX hf₀ hf₁ hs₁ hC h₁ k x₀).IsEndPullback A a₁) →
      HasCutEnd (7 / 8) 1 (cobTime hf₀ Ŝ k) oM (solPartOr hX hf₁ hs₁ o₁ k) A a₁ := by
  intro oM A a₁ hor hpull
  rcases isEmpty_or_nonempty ↥(B.solPart f₁ s₁ k) with hN | ⟨⟨x₀⟩⟩
  · exact Or.inl ⟨hN, fun p hp =>
      hN.false ⟨_, (cobPart_end_right hf₀ hf₁ hs₁ hC h₁ k p.1 hp).1 p.2⟩⟩
  · exact Or.inr ⟨cobEndRight hX hf₀ hf₁ hs₁ hC h₁ k x₀, hor x₀, hpull x₀, fun _ _ => rfl,
      fun _ hp => hp⟩

include hbump in
/-- **The cobordism identity for `Ψ`** (the proof of 2021 Theorem 6.7.1 (1), p. 277–279, and the
"same homotopy argument" of (2), p. 279): for cobordism data `Ŝ` between `f₀ + s₀` and
`f₀ + σ₁ = f₁ + s₁`, an orientation of the cobordism of product form on the ends
(`CobordismOrientation`) and the relative forms on it (`CobordismRelativeForms`), the invariants
`Ψ_{s₀}(f₀, o₀)` and `Ψ_{s₁}(f₁, o₁)` agree in degree `k`. Proof: on a closed `c`, both are the
integrals of the integrands `a_i` (`IsPsiIntegrand.psiAt_eq`), which agree by
`integral_eq_of_cutCobordism` on `S_F^{k+1}` with the time function and its compact slabs. -/
theorem psiAt_eq_of_cobordism (hOr : CobordismOrientation hX hf₀ hs₀ o₀ hf₁ hs₁ o₁ hC h₁ k)
    (hRel : CobordismRelativeForms hX hf₀ hs₀ hf₁ hs₁ hC h₁ k) :
    psiAt hX hbump hf₀ hs₀ o₀ k = psiAt hX hbump hf₁ hs₁ o₁ k := by
  have hS₀ := hC.isCompact_solutionSet_left
  have hS₁ : IsCompact (solutionSet P (sectionAdd P f₁ s₁)) := h₁ ▸ hC.isCompact_solutionSet_right
  obtain ⟨oM, hoM, horL, horR⟩ := hOr
  refine Submodule.linearMap_qext _ (LinearMap.ext fun c => ?_)
  simp only [LinearMap.comp_apply]
  obtain ⟨a₀, ha₀⟩ := exists_isPsiIntegrand hX hf₀ hs₀ hS₀ k c
  obtain ⟨a₁, ha₁⟩ := exists_isPsiIntegrand hX hf₁ hs₁ hS₁ k c
  obtain ⟨A, hA, hA0, hface, hpullL, hpullR⟩ := hRel c a₀ a₁ ha₀ ha₁
  let := solPartChartedSpace hX hf₀ hs₀ k
  let := solPartChartedSpace hX hf₁ hs₁ k
  let := cobChartedSpace hX hf₀ hC k
  have := isManifold_solPart hX hf₀ hs₀ k
  have := isManifold_solPart hX hf₁ hs₁ k
  have := isManifold_cobPart hX hf₀ hC k
  have := sigmaCompactSpace_cobPart hf₀ hC k
  have := isCompact_iff_compactSpace.1 (isCompact_solPart hf₀ hs₀.isScPlusSection hs₀.gp hS₀ k)
  have := isCompact_iff_compactSpace.1 (isCompact_solPart hf₁ hs₁.isScPlusSection hs₁.gp hS₁ k)
  change psiAt hX hbump hf₀ hs₀ o₀ k (relDeRhamMk hX k c) =
    psiAt hX hbump hf₁ hs₁ o₁ k (relDeRhamMk hX k c)
  rw [ha₀.psiAt_eq hX hbump hf₀ hs₀ o₀ hS₀, ha₁.psiAt_eq hX hbump hf₁ hs₁ o₁ hS₁]
  exact integral_eq_of_cutCobordism (by norm_num) (by norm_num) hoM
    (isContinuous_solPartOr hX hbump hf₀ hs₀ o₀ k) (isContinuous_solPartOr hX hbump hf₁ hs₁ o₁ k)
    (contMDiff_cobTime hX hf₀ hC k) (isCompact_cobSlab hf₀ hC k) hA hA0 hface
    ((ha₀.contMDiffForm hX hf₀ hs₀).of_le (by simp)) isClosed_closure.isCompact
    ((ha₁.contMDiffForm hX hf₁ hs₁).of_le (by simp)) isClosed_closure.isCompact
    (hasCutEnd_left hX hf₀ hs₀ o₀ hC k horL hpullL)
    (hasCutEnd_right hX hf₀ hf₁ hs₁ o₁ hC h₁ k horR hpullR)

end Cobordism

end Polyfold
