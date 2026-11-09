import Polyfold.Chapter3.GlobalIFTCenter
import Polyfold.Chapter3.GlobalIFTNearbyGraph
import Polyfold.Chapter3.LinearizationCharts
import Mathlib.MeasureTheory.Function.Jacobian

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.2 and §3.6:
**the regularity of the solution germ away from the centre** — condition (a) of
`TangentGermChart.IsRegular` for the solution set of an sc-Fredholm section, by re-centring the
graph description of Theorem 3.6.8 (preprint 3.54) at the nearby zeros (the corrected form of the step "δ is an
sc^∞-germ near every `v₀ ∈ V`" of the proof of Theorem 3.2.3 (preprint 3.27), Finding 82).

# The re-centring argument

## The text, paraphrased

(Proof of Theorem 3.2.3 (preprint 3.27), p. 84) "We first show that `δ` is an sc^∞-germ near every point `v₀ ∈ V`.
Let `x₀ = ϕ⁻¹(v₀ + δ(v₀)) ∈ M` and take the chart `ψ` at `x₀` with the data `N', Y', V', τ` of
Definition 3.25.  The map `w ↦ π ∘ ϕ ∘ ψ⁻¹(w + τ(w))` is sc-smooth and its linearization at `0`,
`h ↦ π ∘ T(ϕ ∘ ψ⁻¹)(0)h : N' → N`, is a linear isomorphism, so it is a local sc-diffeomorphism near
`0` and `δ ∘ (π ∘ ϕ ∘ ψ⁻¹ ∘ (1 + τ)) = (1 − π) ∘ ϕ ∘ ψ⁻¹ ∘ (1 + τ)` shows that `δ` is sc-smooth
near `v₀`."  (Proof of Theorem 3.6.8 (preprint 3.54)) "Consequently the solution set `S` possesses the
`d`-dimensional tangent germ property.  Therefore we can apply Theorem 3.27."

## What is formalized

* `Polyfold.InvDataW`, `InvDataW.contDiffOn_inv`: the inverse function machinery of
  Proposition 3.8.17 (preprint 3.73) / Lemma 3.8.21 (preprint 3.77) (`QuadrantInverse.lean`) with the hypotheses that its proofs use:
  `U` convex with unique differentiability, `f : U → V` of class `C^j` with `‖Df − 1‖ ≤ 1/2`, and
  unique differentiability of the image `f(U)` (which is given here, not derived from the
  degeneracy index).  The inverse is `C^j` on `f(U)`.
* `Polyfold.finrank_le_of_interior_image_nonempty`: a `C¹` map from a finite-dimensional space
  whose image has nonempty interior does not lower the dimension (Sard's lemma in fixed
  dimension, `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`, after composing with a linear
  surjection).
* `Polyfold.exists_contDiffOn_inverse`: a `C^k` map `β` between relatively open subsets of convex
  sets in finite-dimensional spaces, with a continuous inverse and an invertible derivative at a
  point, has a `C^k` inverse near that point.
* `Polyfold.recentre_contDiffOn_levels` (the re-centring lemma): two graph descriptions of the same
  set `S` of an M-polyfold — one in the chart `χ₁` (graph of `σ₁ : V₁ → Y₁` over `K₁`, `σ₁` of
  class `C¹`), one in the chart `χ₂` centred at the point `y = χ₁⁻¹(v₀ + σ₁(v₀))` (graph of
  `σ₂ : V₂ → Y₂` over `K₂` with `C^k`-lifts `σ_{2,k} : V_{2,k} → E_{2,k}` at `0`) — give, for every
  level `m` and every `k`, a relatively open neighbourhood of `v₀` in `K₁ ∩ C₁` on which `σ₁` takes
  values in `E_{1,m}` and is `C^k` into `E_{1,m}`; and `dim K₁ = dim K₂`.
* `Polyfold.MPolyfold.TangentGermChart.shrink`, `exists_shrinkData`, `shrink_isRegular`: the
  data of Definition 3.2.1 (preprint 3.25) (2) restricted to an open subset of the chart domain and a smaller
  relatively open `V' ⊆ V` (same `N`, `Y`, `δ`); `ScRetraction.restrict_isTame`,
  `IsTameRetract.inter_isOpen`, `MChart.isTameRetract_image`: an open subset of a tame retract
  is a tame retract (Proposition 2.3.1 (preprint 2.10) (1) with tameness), used silently by the text.
* `Polyfold.MPolyfold.TangentGermChart.exists_isRegular_of_locally`: **condition (a) of
  `IsRegular` by re-centring**: if the data `D` of Definition 3.2.1 (preprint 3.25) (2) for `M` at `x` satisfy
  `π(O) ⊆ C` and every point of `M` near `x` has data of Definition 3.2.1 (preprint 3.25) (2) of some dimension,
  then `D` can be shrunk to regular data (`IsRegular`: `δ` sc-smooth on `V'` in the set sense),
  and the dimension is locally constant along `M`.  For the solution set this is Theorem 3.6.8 (preprint 3.54) (2)
  from Theorem 3.6.8 (preprint 3.54) (1) (`theorem_3_6_8_two_wholeChart`, `GlobalIFTTheorems.lean`).

## What the text leaves implicit, and the choices made (the findings)

* **The linearization of `w ↦ π ∘ ϕ ∘ ψ⁻¹(w + τ(w))` is an isomorphism only because `δ` is `C¹`
  at `v₀`** (Finding 82: the claim is false without it).  Here `δ = σ` is `C¹` on all of `V'`
  (Theorem 3.5.11 (preprint 3.47) (1)), which is exactly what the chain rule `T ∘ (1 + σ₂) = (1 + σ₁) ∘ β` needs at
  `v₀`.  Injectivity of `Dβ(0)` then follows from the chain rule for the transition `T = χ₁ ∘ χ₂⁻¹`
  and its inverse on level `1` (`D(T⁻¹ ∘ r₁)(T(0)) ∘ D(T ∘ r₂)(0) = Dr₂(0)`) and from `K₂ ⊆ T₀O₂`
  (the tangent vectors of the graph of `σ₂` at `0` lie in the tangent space of the retract,
  `scDeriv_apply_toBase_deriv_eq_of_fixed`).  Surjectivity does **not** follow from the symmetric
  argument, which would need `σ₁` differentiable into level `1` at `v₀` (available only near `0`);
  it is obtained from the dimension count `dim K₁ ≤ dim K₂`, which holds because `β` is a `C¹`-map
  from a `dim K₂`-dimensional space onto a relatively open subset of `K₁ ∩ C₁` (Sard's lemma in
  fixed dimension).  So `dim K₁ = dim K₂`: the dimension of the solution set is locally constant.
* **The inverse function theorem in the quadrant** (Theorem 3.8.15 (preprint 3.72)) needs `d_C(x) = d_C(f(x))`, which
  is not available for `β` (it would be the intrinsic degeneracy index of `S`).  The regularity of
  the inverse `β⁻¹` is proved instead from the bi-Lipschitz estimate and the bootstrapping of
  Lemma 3.8.21 (preprint 3.77) (`InvDataW`), using that `β⁻¹` is already known to be continuous and `β` to be a
  homeomorphism between relatively open sets, so that `β(U)` has unique differentiability.
* **The transition `T = χ₁ ∘ χ₂⁻¹` is only an sc-smooth map of retracts**; `w ↦ T(w + σ₂(w))`
  is `C^k` into `E_{1,m}` because `T ∘ r₂ : U_{2,m+k} → E_{1,m}` is `C^k` (Proposition 1.2.3 (preprint 1.18)) and
  `w ↦ w + σ_{2,m+k}(w)` is a `C^k`-lift into `E_{2,m+k}` (Theorem 3.5.11 (preprint 3.47) (1)).  The neighbourhood of
  `0` on which this holds depends on `m + k`; the neighbourhood of `v₀` obtained for `σ₁` depends
  on `(m, k)` too, which is harmless because sc-smoothness on `V''` is a local property of the
  level maps (`contDiffOn_of_locally_contDiffOn`).
-/

open Set Filter Topology Function Module
open scoped ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

/-! ### The inverse function machinery of Proposition 3.8.17 (preprint 3.73) with weak hypotheses -/

section InvW

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The hypotheses of Proposition 3.8.17 (preprint 3.73) / Lemma 3.8.21 (preprint 3.77) actually used by their proofs
(`QuadrantInverse.lean`), without the partial quadrant: `U ⊆ V` convex with unique
differentiability, `f : U → V` of class `C^j` (`j ≥ 1`) with `‖Df(x) − 1‖ ≤ 1/2` on `U`, and
unique differentiability of the image `f(U)` (in Proposition 3.8.17 (preprint 3.73) this is derived from
`d_C(x) = d_C(f(x))`; here it is a hypothesis). -/
structure InvDataW (U : Set V) (f : V → V) (j : ℕ) : Prop where
  convex : Convex ℝ U
  uniqueDiffOn_U : UniqueDiffOn ℝ U
  uniqueDiffOn_image : UniqueDiffOn ℝ (f '' U)
  one_le : 1 ≤ j
  contDiffOn : ContDiffOn ℝ j f U
  deriv_bound : ∀ x ∈ U, ‖fderivWithin ℝ f U x - 1‖ ≤ 1 / 2

namespace InvDataW

variable {U : Set V} {f : V → V} {j : ℕ} (h : InvDataW U f j)
include h

lemma j_ne_zero : (j : WithTop ℕ∞) ≠ 0 := by
  have := h.one_le; exact_mod_cast (show j ≠ 0 by omega)

lemma hasFDerivWithinAt {x : V} (hx : x ∈ U) : HasFDerivWithinAt f (fderivWithin ℝ f U x) U x :=
  ((h.contDiffOn.differentiableOn h.j_ne_zero) x hx).hasFDerivWithinAt

lemma continuousOn : ContinuousOn f U := h.contDiffOn.continuousOn

/-- Lemma 3.8.18 (preprint 3.74), (70), first step: `f − id` is a `1/2`-contraction on `U`. -/
lemma norm_sub_sub_le {x x' : V} (hx : x ∈ U) (hx' : x' ∈ U) :
    ‖(f x' - x') - (f x - x)‖ ≤ 1 / 2 * ‖x' - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun z => f z - z)
    (f' := fun z => fderivWithin ℝ f U z - 1)
    (fun z hz => (h.hasFDerivWithinAt hz).sub (hasFDerivWithinAt_id z U))
    (fun z hz => h.deriv_bound z hz) h.convex hx hx'

/-- Lemma 3.8.18 (preprint 3.74), (70): `|x − x'|/2 ≤ |f(x) − f(x')|`. -/
lemma half_norm_le {x x' : V} (hx : x ∈ U) (hx' : x' ∈ U) :
    1 / 2 * ‖x' - x‖ ≤ ‖f x' - f x‖ := by
  have h1 := h.norm_sub_sub_le hx hx'
  have h2 : ‖x' - x‖ ≤ ‖f x' - f x‖ + ‖(f x' - x') - (f x - x)‖ := by
    calc ‖x' - x‖ = ‖(f x' - f x) - ((f x' - x') - (f x - x))‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith

lemma injOn : InjOn f U := by
  intro x hx x' hx' hxx'
  have := h.half_norm_le hx hx'
  rw [hxx', sub_self, norm_zero] at this
  have h2 : ‖x' - x‖ ≤ 0 := by linarith
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h2)).symm

/-- `Df(x) = 1 − (1 − Df(x))` is a unit (`‖1 − Df(x)‖ ≤ 1/2`). -/
def derivUnit {x : V} (hx : x ∈ U) : (V →L[ℝ] V)ˣ :=
  Units.oneSub (1 - fderivWithin ℝ f U x)
    (by rw [norm_sub_rev]; exact (h.deriv_bound x hx).trans_lt (by norm_num))

lemma derivUnit_val {x : V} (hx : x ∈ U) : (h.derivUnit hx : V →L[ℝ] V) = fderivWithin ℝ f U x :=
  sub_sub_cancel _ _

lemma isUnit_deriv {x : V} (hx : x ∈ U) : IsUnit (fderivWithin ℝ f U x) := by
  have := (h.derivUnit hx).isUnit
  rwa [h.derivUnit_val hx] at this

omit h in
/-- The inverse `g = f⁻¹ : f(U) → U`. -/
def inv (U : Set V) (f : V → V) : V → V := Function.invFunOn f U

lemma inv_mem {y : V} (hy : y ∈ f '' U) : inv U f y ∈ U := Function.invFunOn_mem hy

lemma apply_inv {y : V} (hy : y ∈ f '' U) : f (inv U f y) = y := Function.invFunOn_eq hy

lemma inv_apply {x : V} (hx : x ∈ U) : inv U f (f x) = x := h.injOn.leftInvOn_invFunOn hx

lemma norm_inv_sub_le {y y' : V} (hy : y ∈ f '' U) (hy' : y' ∈ f '' U) :
    ‖inv U f y' - inv U f y‖ ≤ 2 * ‖y' - y‖ := by
  have := h.half_norm_le (h.inv_mem hy) (h.inv_mem hy')
  rw [h.apply_inv hy, h.apply_inv hy'] at this
  linarith

lemma continuousOn_inv : ContinuousOn (inv U f) (f '' U) :=
  (LipschitzOnWith.of_dist_le_mul (K := 2) fun y hy y' hy' => by
    rw [dist_eq_norm, dist_eq_norm]
    exact h.norm_inv_sub_le hy' hy).continuousOn

/-- **Lemma 3.8.21 (preprint 3.77)**: the inverse is differentiable within `f(U)` with `Dg(y) = [Df(g(y))]⁻¹`. -/
theorem hasFDerivWithinAt_inv {y : V} (hy : y ∈ f '' U) :
    HasFDerivWithinAt (inv U f) (Ring.inverse (fderivWithin ℝ f U (inv U f y))) (f '' U) y := by
  have hxU : inv U f y ∈ U := h.inv_mem hy
  have hf := h.hasFDerivWithinAt hxU
  rw [hasFDerivWithinAt_iff_isLittleO] at hf ⊢
  have htend : Tendsto (inv U f) (𝓝[f '' U] y) (𝓝[U] (inv U f y)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h.continuousOn_inv y hy, eventually_nhdsWithin_of_forall fun y' hy' => h.inv_mem hy'⟩
  have h1 := hf.comp_tendsto htend
  have h2 : (fun y' => inv U f y' - inv U f y) =O[𝓝[f '' U] y] (fun y' => y' - y) :=
    Asymptotics.IsBigO.of_bound 2
      (eventually_nhdsWithin_of_forall fun y' hy' => h.norm_inv_sub_le hy hy')
  have h3 := h1.trans_isBigO h2
  have hM : Ring.inverse (fderivWithin ℝ f U (inv U f y)) * fderivWithin ℝ f U (inv U f y) = 1 :=
    Ring.inverse_mul_cancel _ (h.isUnit_deriv hxU)
  have h4 := ((Ring.inverse (fderivWithin ℝ f U (inv U f y))).isBigO_comp _
    (𝓝[f '' U] y)).trans_isLittleO h3
  refine (Asymptotics.isLittleO_neg_left.2 h4).congr'
    (eventually_nhdsWithin_of_forall fun y' hy' => ?_) EventuallyEq.rfl
  simp only [Function.comp_apply]
  rw [h.apply_inv hy', h.apply_inv hy, map_sub, map_sub, ← mul_apply_eq_comp, hM,
    one_apply_eq_self]
  abel

/-- `x ↦ [Df(x)]⁻¹` is of class `C^{j−1}` on `U`. -/
theorem contDiffOn_inverse_deriv :
    ContDiffOn ℝ (j - 1 : ℕ) (fun x => Ring.inverse (fderivWithin ℝ f U x)) U := by
  have hD : ContDiffOn ℝ (j - 1 : ℕ) (fderivWithin ℝ f U) U :=
    h.contDiffOn.fderivWithin h.uniqueDiffOn_U
      (by have := h.one_le; exact_mod_cast (show (j - 1 : ℕ) + 1 ≤ j by omega))
  intro x hx
  have h2 : ContDiffAt ℝ (j - 1 : ℕ) (Ring.inverse : (V →L[ℝ] V) → (V →L[ℝ] V))
      ((h.derivUnit hx : (V →L[ℝ] V)ˣ) : V →L[ℝ] V) := contDiffAt_ringInverse ℝ _
  rw [h.derivUnit_val hx] at h2
  exact h2.contDiffWithinAt.comp x (hD x hx) (mapsTo_univ _ _)

/-- **Proposition 3.8.17 (preprint 3.73), the regularity of the inverse**, under the weak hypotheses: `g = f⁻¹` is
of class `C^j` on `f(U)` (bootstrapping `Dg = [Df]⁻¹ ∘ g`). -/
theorem contDiffOn_inv : ContDiffOn ℝ j (inv U f) (f '' U) := by
  have key : ∀ i : ℕ, i ≤ j → ContDiffOn ℝ i (inv U f) (f '' U) := by
    intro i
    induction i with
    | zero => intro _; exact contDiffOn_zero.2 h.continuousOn_inv
    | succ i ih =>
      intro hi
      rw [show ((i + 1 : ℕ) : WithTop ℕ∞) = (i : WithTop ℕ∞) + 1 by push_cast; rfl]
      refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn h.uniqueDiffOn_image).2
        ⟨fun hω => absurd hω (by simp), fun y => Ring.inverse (fderivWithin ℝ f U (inv U f y)), ?_,
          fun y hy => h.hasFDerivWithinAt_inv hy⟩
      have hΨ : ContDiffOn ℝ i (fun x => Ring.inverse (fderivWithin ℝ f U x)) U :=
        h.contDiffOn_inverse_deriv.of_le (by exact_mod_cast (show i ≤ j - 1 by omega))
      exact hΨ.comp (ih (by omega)) fun y hy => h.inv_mem hy
  exact key j le_rfl

end InvDataW

end InvW

/-! ### A `C¹` map onto a set with interior does not lower the dimension -/

section Dimension

variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [FiniteDimensional ℝ V₂]

/-- A linear surjection `V₂ → V₁` exists when `dim V₁ ≤ dim V₂`. -/
lemma exists_linearMap_surjective (h : finrank ℝ V₁ ≤ finrank ℝ V₂) :
    ∃ p : V₂ →ₗ[ℝ] V₁, Surjective p := by
  classical
  set b₁ := Module.finBasis ℝ V₁
  set b₂ := Module.finBasis ℝ V₂
  refine ⟨b₂.constr ℝ fun j : Fin (finrank ℝ V₂) =>
    if hj : (j : ℕ) < finrank ℝ V₁ then b₁ ⟨j, hj⟩ else 0, ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← b₁.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine ⟨b₂ (Fin.castLE h i), ?_⟩
  rw [Basis.constr_basis]
  simp only [Fin.val_castLE, Fin.is_lt, dif_pos, Fin.eta]

/-- **Sard's lemma in fixed dimension, for the dimension count**: if `f : V₁ → V₂` is
differentiable on `s` and `f(s)` has nonempty interior, then `dim V₂ ≤ dim V₁`.  (Compose `f` with
a linear surjection `p : V₂ → V₁`; `D(f ∘ p)` has rank `≤ dim V₁ < dim V₂`, so the image has
measure zero by `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`, while an open set has
positive Haar measure.) -/
theorem finrank_le_of_interior_image_nonempty {f : V₁ → V₂} {s : Set V₁}
    (hf : DifferentiableOn ℝ f s) (hs : (interior (f '' s)).Nonempty) :
    finrank ℝ V₂ ≤ finrank ℝ V₁ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨p, hp⟩ := exists_linearMap_surjective (V₁ := V₁) (V₂ := V₂) hlt.le
  set pL : V₂ →L[ℝ] V₁ := LinearMap.toContinuousLinearMap p with hpL
  borelize V₂
  set μ : MeasureTheory.Measure V₂ := MeasureTheory.Measure.addHaar with hμ
  -- the composition `f ∘ p` on `p⁻¹(s)` has a derivative of rank `< dim V₂`
  set s' : Set V₂ := pL ⁻¹' s with hs'
  have hderiv : ∀ x ∈ s', HasFDerivWithinAt (f ∘ pL) ((fderivWithin ℝ f s (pL x)).comp pL) s' x :=
    fun x hx => (hf (pL x) hx).hasFDerivWithinAt.comp x pL.hasFDerivWithinAt (mapsTo_preimage _ _)
  have hdet : ∀ x ∈ s', ((fderivWithin ℝ f s (pL x)).comp pL).det = 0 := by
    intro x _
    rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot]
    intro hker
    have hinj : Injective (((fderivWithin ℝ f s (pL x)).comp pL : V₂ →L[ℝ] V₂) : V₂ →ₗ[ℝ] V₂) :=
      LinearMap.ker_eq_bot.1 hker
    have h1 := LinearMap.finrank_range_of_inj hinj
    have h2 : LinearMap.range (((fderivWithin ℝ f s (pL x)).comp pL : V₂ →L[ℝ] V₂) : V₂ →ₗ[ℝ] V₂) ≤
        LinearMap.range (fderivWithin ℝ f s (pL x) : V₁ →ₗ[ℝ] V₂) := by
      rintro _ ⟨y, rfl⟩
      exact ⟨pL y, rfl⟩
    have h3 := Submodule.finrank_mono h2
    have h4 := LinearMap.finrank_range_le (fderivWithin ℝ f s (pL x) : V₁ →ₗ[ℝ] V₂)
    omega
  have hzero : μ ((f ∘ pL) '' s') = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ hderiv hdet
  have himage : f '' s ⊆ (f ∘ pL) '' s' := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨x, hx⟩ := hp u
    exact ⟨x, by rw [hs', mem_preimage]; change p x ∈ s; rw [hx]; exact hu,
      by simp only [Function.comp_apply]; change f (p x) = f u; rw [hx]⟩
  have hpos : 0 < μ (interior (f '' s)) := isOpen_interior.measure_pos μ hs
  have hle : μ (interior (f '' s)) ≤ μ ((f ∘ pL) '' s') :=
    MeasureTheory.measure_mono (interior_subset.trans himage)
  rw [hzero] at hle
  exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl _)

end Dimension

/-! ### A `C^k` homeomorphism with invertible derivative has a `C^k` inverse -/

section LocalInverse

variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [FiniteDimensional ℝ V₂]

/-- A relatively open subset of a convex set with nonempty interior has unique
differentiability. -/
lemma uniqueDiffOn_relOpen_convex {D A : Set V₁} (hD : Convex ℝ D) (hDi : (interior D).Nonempty)
    (hA : ∃ O : Set V₁, IsOpen O ∧ A = O ∩ D) : UniqueDiffOn ℝ A := by
  obtain ⟨O, hO, rfl⟩ := hA
  rw [inter_comm]
  exact (uniqueDiffOn_convex hD hDi).inter hO

/-- A nonempty relatively open subset of a convex set with nonempty interior has nonempty
interior (the open segment from an interior point to a point of the set lies in the interior). -/
lemma interior_nonempty_of_relOpen_convex {D A : Set V₁} (hD : Convex ℝ D)
    (hDi : (interior D).Nonempty) (hA : ∃ O : Set V₁, IsOpen O ∧ A = O ∩ D) (hne : A.Nonempty) :
    (interior A).Nonempty := by
  obtain ⟨O, hO, rfl⟩ := hA
  obtain ⟨a, haO, haD⟩ := hne
  obtain ⟨w, hw⟩ := hDi
  -- points `a + t (w − a)` for small `t > 0` lie in `O` and in the interior of `D`
  have hcont : Continuous fun t : ℝ => a + t • (w - a) := by fun_prop
  have hev : ∀ᶠ t : ℝ in 𝓝 0, a + t • (w - a) ∈ O := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hO.mem_nhds haO
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
  set t : ℝ := min (δ / 2) (1 / 2) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hmemO : a + t • (w - a) ∈ O := hδ' (y := t)
    (by rw [dist_zero_right, Real.norm_of_nonneg ht0.le]; exact htδ)
  have hmemD : a + t • (w - a) ∈ interior D := by
    have := hD.openSegment_closure_interior_subset_interior (subset_closure haD) hw
    apply this
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    simp only [smul_sub, sub_smul, one_smul]
    abel
  refine ⟨a + t • (w - a), ?_⟩
  rw [interior_inter, mem_inter_iff, hO.interior_eq]
  exact ⟨hmemO, hmemD⟩

/-- **The inverse of a `C^k` homeomorphism with invertible derivative is `C^k`**: let `D₁ ⊆ V₁`,
`D₂ ⊆ V₂` be convex with nonempty interior, `A` relatively open in `D₁`, `β : A → V₂` of class
`C^k` (`k ≥ 1`) with `β(A)` relatively open in `D₂`, `α` a continuous left inverse of `β` on
`β(A)`, and `Dβ(w₀) = L` a linear isomorphism at some `w₀ ∈ A`.  Then there is a relatively open
neighbourhood `B'` of `β(w₀)` in `D₂`, `B' ⊆ β(A)`, with `α` of class `C^k` on `B'`.  (Lemma 3.8.21 (preprint 3.77)
and Proposition 3.8.17 (preprint 3.73) through `InvDataW` for `L⁻¹ ∘ β` on a small convex neighbourhood of `w₀`.) -/
theorem exists_contDiffOn_inverse {D₁ : Set V₁} {D₂ : Set V₂} (hD₁ : Convex ℝ D₁)
    (hD₁i : (interior D₁).Nonempty) (hD₂ : Convex ℝ D₂) (hD₂i : (interior D₂).Nonempty)
    {A : Set V₁} (hA : ∃ O : Set V₁, IsOpen O ∧ A = O ∩ D₁) {β : V₁ → V₂} {α : V₂ → V₁}
    (hBrel : ∃ O : Set V₂, IsOpen O ∧ β '' A = O ∩ D₂) (hα : ContinuousOn α (β '' A))
    (hαβ : ∀ w ∈ A, α (β w) = w) {w₀ : V₁} (hw₀ : w₀ ∈ A) {k : ℕ} (hk : 1 ≤ k)
    (hβ : ContDiffOn ℝ k β A) (L : V₁ ≃L[ℝ] V₂) (hL : fderivWithin ℝ β A w₀ = L) :
    ∃ B' : Set V₂, (∃ O : Set V₂, IsOpen O ∧ B' = O ∩ D₂) ∧ β w₀ ∈ B' ∧ B' ⊆ β '' A ∧
      ContDiffOn ℝ k α B' := by
  classical
  obtain ⟨O, hO, hAO⟩ := hA
  have hAD : A ⊆ D₁ := by rw [hAO]; exact inter_subset_right
  have hw₀O : w₀ ∈ O := by rw [hAO] at hw₀; exact hw₀.1
  have hAuniq : UniqueDiffOn ℝ A := uniqueDiffOn_relOpen_convex hD₁ hD₁i ⟨O, hO, hAO⟩
  have hk' : (1 : WithTop ℕ∞) ≤ k := by exact_mod_cast hk
  have hkne : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  -- the normalized map `β̂ = L⁻¹ ∘ β`
  set βh : V₁ → V₁ := fun w => L.symm (β w) with hβh
  have hβhC : ContDiffOn ℝ k βh A := L.symm.contDiff.comp_contDiffOn hβ
  have hβhD : ∀ w ∈ A, fderivWithin ℝ βh A w = (L.symm : V₂ →L[ℝ] V₁).comp (fderivWithin ℝ β A w) :=
    fun w hw => L.symm.comp_fderivWithin (hAuniq w hw)
  have hβh0 : fderivWithin ℝ βh A w₀ = 1 := by
    rw [hβhD w₀ hw₀, hL]
    ext v
    simp
  -- continuity of the derivative: `‖Dβ̂ − 1‖ ≤ 1/2` near `w₀`
  have hDcont : ContinuousOn (fderivWithin ℝ βh A) A := hβhC.continuousOn_fderivWithin hAuniq hk'
  have hev : ∀ᶠ w in 𝓝[A] w₀, ‖fderivWithin ℝ βh A w - 1‖ ≤ 1 / 2 := by
    have h1 : Tendsto (fderivWithin ℝ βh A) (𝓝[A] w₀) (𝓝 1) := by
      have := hDcont w₀ hw₀; rwa [ContinuousWithinAt, hβh0] at this
    have h2 : Metric.closedBall (1 : V₁ →L[ℝ] V₁) (1 / 2) ∈ 𝓝 (1 : V₁ →L[ℝ] V₁) :=
      Metric.closedBall_mem_nhds _ (by norm_num)
    filter_upwards [h1 h2] with w hw
    rw [mem_preimage, Metric.mem_closedBall, dist_eq_norm] at hw
    exact hw
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhdsWithin_iff.1 hev
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.1 hO w₀ hw₀O
  set r := min r₁ r₂ with hr
  have hr0 : 0 < r := lt_min hr₁ hr₂
  -- the convex neighbourhood `U = D₁ ∩ B(w₀, r) ⊆ A`
  set U : Set V₁ := D₁ ∩ Metric.ball w₀ r with hU
  have hUA : U ⊆ A := by
    rintro w ⟨hwD, hwb⟩
    rw [hAO]
    exact ⟨hball₂ (Metric.ball_subset_ball (min_le_right _ _) hwb), hwD⟩
  have hUconv : Convex ℝ U := hD₁.inter (convex_ball w₀ r)
  have hw₀U : w₀ ∈ U := ⟨hAD hw₀, Metric.mem_ball_self hr0⟩
  have hUrel : ∃ O' : Set V₁, IsOpen O' ∧ U = O' ∩ D₁ :=
    ⟨Metric.ball w₀ r, Metric.isOpen_ball, by rw [hU, inter_comm]⟩
  have hUuniq : UniqueDiffOn ℝ U := uniqueDiffOn_relOpen_convex hD₁ hD₁i hUrel
  have hUeq : ∀ w ∈ U, fderivWithin ℝ βh U w = fderivWithin ℝ βh A w := by
    intro w hw
    have : U = A ∩ Metric.ball w₀ r := by
      ext z
      simp only [hU, mem_inter_iff]
      constructor
      · rintro ⟨hzD, hzb⟩; exact ⟨hUA ⟨hzD, hzb⟩, hzb⟩
      · rintro ⟨hzA, hzb⟩; exact ⟨hAD hzA, hzb⟩
    rw [this, fderivWithin_inter (Metric.isOpen_ball.mem_nhds hw.2)]
  have hbound : ∀ w ∈ U, ‖fderivWithin ℝ βh U w - 1‖ ≤ 1 / 2 := by
    intro w hw
    rw [hUeq w hw]
    exact hball₁ ⟨Metric.ball_subset_ball (min_le_left _ _) hw.2, hUA hw⟩
  -- `β(U) = β(A) ∩ α⁻¹(B(w₀, r))` is relatively open in `D₂`
  have hβU : β '' U = β '' A ∩ α ⁻¹' Metric.ball w₀ r := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hUA hw, rfl⟩, by rw [mem_preimage, hαβ w (hUA hw)]; exact hw.2⟩
    · rintro ⟨⟨w, hw, rfl⟩, hv⟩
      rw [mem_preimage, hαβ w hw] at hv
      exact ⟨w, ⟨hAD hw, hv⟩, rfl⟩
  have hβUrel : ∃ O' : Set V₂, IsOpen O' ∧ β '' U = O' ∩ D₂ := by
    obtain ⟨O₂, hO₂, hB⟩ := hBrel
    obtain ⟨u, hu, huB⟩ := (continuousOn_iff'.1 hα) (Metric.ball w₀ r) Metric.isOpen_ball
    refine ⟨u ∩ O₂, hu.inter hO₂, ?_⟩
    rw [hβU, inter_comm (β '' A), huB, hB, inter_assoc]
  have hβUuniq : UniqueDiffOn ℝ (β '' U) := uniqueDiffOn_relOpen_convex hD₂ hD₂i hβUrel
  have hβhU : βh '' U = L.symm '' (β '' U) := by
    rw [hβh, image_image]
  have hβhUuniq : UniqueDiffOn ℝ (βh '' U) := by
    rw [hβhU]; exact L.symm.uniqueDiffOn_image hβUuniq
  -- the inverse function machinery for `β̂` on `U`
  have hinv : InvDataW U βh k :=
    { convex := hUconv
      uniqueDiffOn_U := hUuniq
      uniqueDiffOn_image := hβhUuniq
      one_le := hk
      contDiffOn := hβhC.mono hUA
      deriv_bound := hbound }
  have hinvC : ContDiffOn ℝ k (InvDataW.inv U βh) (βh '' U) := hinv.contDiffOn_inv
  refine ⟨β '' U, hβUrel, ⟨w₀, hw₀U, rfl⟩, image_mono hUA, ?_⟩
  -- `α = (β̂)⁻¹ ∘ L⁻¹` on `β(U)`
  have hcomp : ContDiffOn ℝ k (InvDataW.inv U βh ∘ L.symm) (β '' U) := by
    refine hinvC.comp (L.symm.contDiff.contDiffOn) ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  refine hcomp.congr ?_
  rintro _ ⟨w, hw, rfl⟩
  simp only [Function.comp_apply]
  rw [hαβ w (hUA hw)]
  exact (hinv.inv_apply hw).symm

end LocalInverse

/-! ### The re-centring lemma -/

section Recentre

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

set_option maxHeartbeats 1600000 in
/-- **The re-centring lemma** (the corrected step "`δ` is an sc^∞-germ near every `v₀ ∈ V`" of
the proof of Theorem 3.2.3 (preprint 3.27), for two graph descriptions of the same set).  Let `χ₁`, `χ₂` be charts
of the M-polyfold `X` and `S ⊆ X`.  In `χ₁`, `S ∩ Vx₁` is the graph `{v + σ₁(v) | v ∈ V₁}` of a
`C¹`-map `σ₁ : V₁ → Y₁` over the finite-dimensional smooth subspace `K₁` (closed complement `Y₁`,
`V₁` relatively open in `K₁ ∩ C₁`, `K₁` in good position).  In `χ₂`, centred at the point
`y = χ₁⁻¹(v₀ + σ₁(v₀))` of `S`, `S ∩ Vx₂` is the graph of `σ₂ : V₂ → Y₂` over `K₂` with
`σ₂(0) = 0`, `Dσ₂(0) = 0`, and `σ₂` has `C^k`-lifts `σ_{2,k} : V_{2,k} → E_{2,k}` near `0` for
every `k` (Theorem 3.5.11 (preprint 3.47) (1)).  Then `dim K₁ = dim K₂`, and for every level `m` and every `k` there
is a relatively open neighbourhood `B'` of `v₀` in `K₁ ∩ C₁`, `B' ⊆ V₁`, on which `σ₁` takes
values in `E_{1,m}` and is of class `C^k` into `E_{1,m}`.

Proof.  `T = χ₁ ∘ χ₂⁻¹` is an sc-smooth map between the overlap retracts (the charts are
compatible), so `T ∘ r₂` is sc-smooth on a retraction `r₂` onto `χ₂(V ∩ V')`; with the lift
`Γ_{2,j} = ι + σ_{2,j}` into `E_{2,j}`, `T ∘ Γ₂ = (T ∘ r₂) ∘ Γ_{2,j}` is `C^k` into `E_{1,m}` for
`j = m + k + 2` (Proposition 1.2.3 (preprint 1.18)).  `β = π₁ ∘ T ∘ Γ₂` maps a neighbourhood of `0` in `K₂ ∩ C₂`
onto a neighbourhood of `v₀` in `K₁ ∩ C₁`, with continuous inverse `α = π₂ ∘ T⁻¹ ∘ Γ₁`, and
`T ∘ Γ₂ = Γ₁ ∘ β`.  Differentiating at `0` (`σ₁` is `C¹` at `v₀`, `Dσ₂(0) = 0`):
`D(T ∘ r₂)(0) n = Dβ(0) n + Dσ₁(v₀) Dβ(0) n`.  If `Dβ(0) n = 0` then `D(T ∘ r₂)(0) n = 0`, and the
chain rule for `(T⁻¹ ∘ r₁) ∘ (T ∘ r₂) = r₂` gives `Dr₂(0) n = 0`, while `Dr₂(0) n = n` because the
graph of `σ₂` lies in the retract (`scDeriv_apply_toBase_deriv_eq_of_fixed`); so `Dβ(0)` is
injective and `dim K₂ ≤ dim K₁`.  Conversely `β` is a `C¹`-map onto a set with nonempty interior
in `K₁`, so `dim K₁ ≤ dim K₂` (`finrank_le_of_interior_image_nonempty`).  Hence `Dβ(0)` is an
isomorphism, `α` is `C^k` near `v₀` (`exists_contDiffOn_inverse`), and
`σ₁ = ((1 − π₁) ∘ T ∘ Γ₂) ∘ α` is `C^k` into `E_{1,m}` near `v₀`. -/
theorem recentre_contDiffOn_levels {χ₁ χ₂ : MChart X} (hχ₁ : P.IsChart χ₁) (hχ₂ : P.IsChart χ₂)
    {K₁ Y₁ : Submodule ℝ (χ₁.model.E 0)} [FiniteDimensional ℝ K₁] (hK₁ : K₁ ≤ χ₁.model.E.smooth)
    (hY₁ : IsClosed (Y₁ : Set (χ₁.model.E 0))) (hKY₁ : IsCompl K₁ Y₁)
    (hpos₁ : IsInGoodPosition χ₁.model.E χ₁.model.C K₁)
    {V₁ : Set K₁} (hV₁ : ∃ O : Set K₁, IsOpen O ∧ V₁ = O ∩ Subtype.val ⁻¹' χ₁.model.C)
    {σ₁ : K₁ → χ₁.model.E 0} (hσ₁Y : ∀ v, σ₁ v ∈ Y₁) (hσ₁ : ContDiffOn ℝ 1 σ₁ V₁)
    {S Vx₁ : Set X} (hVx₁o : IsOpen Vx₁) (hVx₁ : Vx₁ ⊆ χ₁.source)
    (himage₁ : χ₁ '' (S ∩ Vx₁) = (fun v : K₁ => (v : χ₁.model.E 0) + σ₁ v) '' V₁)
    {K₂ Y₂ : Submodule ℝ (χ₂.model.E 0)} [FiniteDimensional ℝ K₂] (hK₂ : K₂ ≤ χ₂.model.E.smooth)
    (hY₂ : IsClosed (Y₂ : Set (χ₂.model.E 0))) (hKY₂ : IsCompl K₂ Y₂)
    (hpos₂ : IsInGoodPosition χ₂.model.E χ₂.model.C K₂)
    {V₂ : Set K₂} (hV₂ : ∃ O : Set K₂, IsOpen O ∧ V₂ = O ∩ Subtype.val ⁻¹' χ₂.model.C)
    (h0V₂ : (0 : K₂) ∈ V₂)
    {σ₂ : K₂ → χ₂.model.E 0} (hσ₂Y : ∀ w, σ₂ w ∈ Y₂) (hσ₂c : ContinuousOn σ₂ V₂) (hσ₂0 : σ₂ 0 = 0)
    (hDσ₂ : fderivWithin ℝ σ₂ V₂ 0 = 0)
    (hlift : ∀ k : ℕ, 1 ≤ k → ∃ Vk : Set K₂,
      (∃ O : Set K₂, IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' χ₂.model.C) ∧ (0 : K₂) ∈ Vk ∧ Vk ⊆ V₂ ∧
      ∃ σk : K₂ → χ₂.model.E k, ContDiffOn ℝ k σk Vk ∧ ∀ w ∈ Vk, χ₂.model.E.toBase k (σk w) = σ₂ w)
    {Vx₂ : Set X} (hVx₂o : IsOpen Vx₂) (hVx₂ : Vx₂ ⊆ χ₂.source)
    (himage₂ : χ₂ '' (S ∩ Vx₂) = (fun w : K₂ => (w : χ₂.model.E 0) + σ₂ w) '' V₂)
    {y : X} (hy₁ : y ∈ Vx₁) (hy₂ : y ∈ Vx₂) (hχ₂y : χ₂ y = 0)
    {v₀ : K₁} (hv₀ : v₀ ∈ V₁) (hχ₁y : χ₁ y = (v₀ : χ₁.model.E 0) + σ₁ v₀) :
    finrank ℝ K₁ = finrank ℝ K₂ ∧
    ∀ m k : ℕ, ∃ B' : Set K₁, (∃ O : Set K₁, IsOpen O ∧ B' = O ∩ Subtype.val ⁻¹' χ₁.model.C) ∧
      v₀ ∈ B' ∧ B' ⊆ V₁ ∧ (∀ v ∈ B', σ₁ v ∈ range (χ₁.model.E.toBase m)) ∧
      ContDiffOn ℝ k (levelMap (E := ScBanach.const K₁) (F := χ₁.model.E) σ₁ m) B' := by
  classical
  -- notation
  set Γ₁ : K₁ → χ₁.model.E 0 := fun v => (v : χ₁.model.E 0) + σ₁ v with hΓ₁
  set Γ₂ : K₂ → χ₂.model.E 0 := fun w => (w : χ₂.model.E 0) + σ₂ w with hΓ₂
  have hΓ₁a : ∀ v, Γ₁ v = (v : χ₁.model.E 0) + σ₁ v := fun v => rfl
  have hΓ₂a : ∀ w, Γ₂ w = (w : χ₂.model.E 0) + σ₂ w := fun w => rfl
  -- the projections
  have htc₁ : Submodule.IsTopCompl K₁ Y₁ :=
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hKY₁.symm hY₁).symm
  have htc₂ : Submodule.IsTopCompl K₂ Y₂ :=
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hKY₂.symm hY₂).symm
  set π₁ : χ₁.model.E 0 →L[ℝ] K₁ := K₁.projectionOntoL Y₁ htc₁ with hπ₁
  set π₂ : χ₂.model.E 0 →L[ℝ] K₂ := K₂.projectionOntoL Y₂ htc₂ with hπ₂
  have hπ₁Γ : ∀ v, π₁ (Γ₁ v) = v := fun v => by
    rw [hΓ₁a, map_add, hπ₁, Submodule.projectionOntoL_apply_left,
      (Submodule.projectionOntoL_apply_eq_zero_iff htc₁).2 (hσ₁Y v), add_zero]
  have hπ₂Γ : ∀ w, π₂ (Γ₂ w) = w := fun w => by
    rw [hΓ₂a, map_add, hπ₂, Submodule.projectionOntoL_apply_left,
      (Submodule.projectionOntoL_apply_eq_zero_iff htc₂).2 (hσ₂Y w), add_zero]
  -- the cones
  have hC₁conv : Convex ℝ (Subtype.val ⁻¹' χ₁.model.C : Set K₁) :=
    χ₁.model.isPartialQuadrant.convex.linear_preimage K₁.subtype
  have hC₂conv : Convex ℝ (Subtype.val ⁻¹' χ₂.model.C : Set K₂) :=
    χ₂.model.isPartialQuadrant.convex.linear_preimage K₂.subtype
  have hC₁int : (interior (Subtype.val ⁻¹' χ₁.model.C : Set K₁)).Nonempty := hpos₁.interior_nonempty
  have hC₂int : (interior (Subtype.val ⁻¹' χ₂.model.C : Set K₂)).Nonempty := hpos₂.interior_nonempty
  have hV₁C : V₁ ⊆ Subtype.val ⁻¹' χ₁.model.C := by obtain ⟨O, -, rfl⟩ := hV₁; exact inter_subset_right
  have hV₂C : V₂ ⊆ Subtype.val ⁻¹' χ₂.model.C := by obtain ⟨O, -, rfl⟩ := hV₂; exact inter_subset_right
  -- the points of `S` over the graphs
  have hq₁ : ∀ v ∈ V₁, χ₁.symm (Γ₁ v) ∈ S ∩ Vx₁ ∧ χ₁ (χ₁.symm (Γ₁ v)) = Γ₁ v := by
    intro v hv
    have : Γ₁ v ∈ χ₁ '' (S ∩ Vx₁) := by rw [himage₁]; exact ⟨v, hv, rfl⟩
    obtain ⟨q, hq, hqv⟩ := this
    rw [← hqv, χ₁.symm_apply_apply (hVx₁ hq.2)]
    exact ⟨hq, rfl⟩
  have hq₂ : ∀ w ∈ V₂, χ₂.symm (Γ₂ w) ∈ S ∩ Vx₂ ∧ χ₂ (χ₂.symm (Γ₂ w)) = Γ₂ w := by
    intro w hw
    have : Γ₂ w ∈ χ₂ '' (S ∩ Vx₂) := by rw [himage₂]; exact ⟨w, hw, rfl⟩
    obtain ⟨q, hq, hqw⟩ := this
    rw [← hqw, χ₂.symm_apply_apply (hVx₂ hq.2)]
    exact ⟨hq, rfl⟩
  have hΓ₁O : ∀ v ∈ V₁, Γ₁ v ∈ χ₁.model.O := fun v hv => by
    rw [← (hq₁ v hv).2]; exact χ₁.mapsTo_model _ (hVx₁ (hq₁ v hv).1.2)
  have hΓ₂O : ∀ w ∈ V₂, Γ₂ w ∈ χ₂.model.O := fun w hw => by
    rw [← (hq₂ w hw).2]; exact χ₂.mapsTo_model _ (hVx₂ (hq₂ w hw).1.2)
  have hΓ₂0 : Γ₂ 0 = 0 := by rw [hΓ₂a, Submodule.coe_zero, hσ₂0, add_zero]
  have hq₁v₀ : χ₁.symm (Γ₁ v₀) = y := by
    rw [hΓ₁a, ← hχ₁y, χ₁.symm_apply_apply (hVx₁ hy₁)]
  have hq₂0 : χ₂.symm (Γ₂ 0) = y := by
    rw [hΓ₂0, ← hχ₂y, χ₂.symm_apply_apply (hVx₂ hy₂)]
  -- the transitions `T = χ₁ ∘ χ₂⁻¹`, `T' = χ₂ ∘ χ₁⁻¹` and retractions onto the overlaps
  have hcompat := hχ₂.compatible hχ₁ (P := P)
  set T : χ₂.model.E 0 → χ₁.model.E 0 := χ₂.transition χ₁ with hT
  set T' : χ₁.model.E 0 → χ₂.model.E 0 := χ₁.transition χ₂ with hT'
  have hTmap : IsScSmoothRetractMap χ₂.model.E χ₂.model.C (χ₂.overlap χ₁) χ₁.model.E χ₁.model.C (χ₁.overlap χ₂) T := hcompat.1
  have hT'map : IsScSmoothRetractMap χ₁.model.E χ₁.model.C (χ₁.overlap χ₂) χ₂.model.E χ₂.model.C (χ₂.overlap χ₁) T' := hcompat.2
  obtain ⟨R₂, hR₂⟩ := χ₂.isScRetract_overlap χ₁
  obtain ⟨R₁, hR₁⟩ := χ₁.isScRetract_overlap χ₂
  have hTR : IsScSmooth R₂.U (T ∘ R₂) := hTmap.comp_isScSmooth R₂ hR₂
  have hT'R : IsScSmooth R₁.U (T' ∘ R₁) := hT'map.comp_isScSmooth R₁ hR₁
  have hTq : ∀ q ∈ χ₂.source, T (χ₂ q) = χ₁ q := fun q hq => χ₂.transition_apply χ₁ hq
  have hT'q : ∀ q ∈ χ₁.source, T' (χ₁ q) = χ₂ q := fun q hq => χ₁.transition_apply χ₂ hq
  have hT'T : ∀ z ∈ χ₂.overlap χ₁, T' (T z) = z := by
    rintro _ ⟨q, ⟨hq₂, hq₁⟩, rfl⟩
    rw [hTq q hq₂, hT'q q hq₁]
  -- the sets `A ⊆ V₂` and `Bs ⊆ V₁` where the points lie in both chart neighbourhoods
  set A : Set K₂ := {w | w ∈ V₂ ∧ χ₂.symm (Γ₂ w) ∈ Vx₁} with hA
  set Bs : Set K₁ := {v | v ∈ V₁ ∧ χ₁.symm (Γ₁ v) ∈ Vx₂} with hBs
  have hΓ₂cont : ContinuousOn Γ₂ V₂ := continuous_subtype_val.continuousOn.add hσ₂c
  have hΓ₁cont : ContinuousOn Γ₁ V₁ := continuous_subtype_val.continuousOn.add hσ₁.continuousOn
  have hq₂cont : ContinuousOn (fun w => χ₂.symm (Γ₂ w)) V₂ :=
    χ₂.continuousOn_invFun.comp hΓ₂cont fun w hw => hΓ₂O w hw
  have hq₁cont : ContinuousOn (fun v => χ₁.symm (Γ₁ v)) V₁ :=
    χ₁.continuousOn_invFun.comp hΓ₁cont fun v hv => hΓ₁O v hv
  obtain ⟨OA, hOA, hAeq⟩ := (continuousOn_iff'.1 hq₂cont) Vx₁ hVx₁o
  obtain ⟨OB, hOB, hBeq⟩ := (continuousOn_iff'.1 hq₁cont) Vx₂ hVx₂o
  have hAV : A = V₂ ∩ OA := by
    ext w
    have := congrArg (w ∈ ·) hAeq
    simp only [mem_inter_iff, mem_preimage, eq_iff_iff] at this
    exact ⟨fun hw => ⟨hw.1, (this.1 ⟨hw.2, hw.1⟩).1⟩, fun hw => ⟨hw.1, (this.2 ⟨hw.2, hw.1⟩).1⟩⟩
  have hBV : Bs = V₁ ∩ OB := by
    ext v
    have := congrArg (v ∈ ·) hBeq
    simp only [mem_inter_iff, mem_preimage, eq_iff_iff] at this
    exact ⟨fun hv => ⟨hv.1, (this.1 ⟨hv.2, hv.1⟩).1⟩, fun hv => ⟨hv.1, (this.2 ⟨hv.2, hv.1⟩).1⟩⟩
  have hArel : ∃ O : Set K₂, IsOpen O ∧ A = O ∩ Subtype.val ⁻¹' χ₂.model.C := by
    obtain ⟨O, hO, hV⟩ := hV₂
    exact ⟨O ∩ OA, hO.inter hOA, by rw [hAV, hV, inter_right_comm]⟩
  have hBrel : ∃ O : Set K₁, IsOpen O ∧ Bs = O ∩ Subtype.val ⁻¹' χ₁.model.C := by
    obtain ⟨O, hO, hV⟩ := hV₁
    exact ⟨O ∩ OB, hO.inter hOB, by rw [hBV, hV, inter_right_comm]⟩
  have hAV₂ : A ⊆ V₂ := fun w hw => hw.1
  have hBV₁ : Bs ⊆ V₁ := fun v hv => hv.1
  have h0A : (0 : K₂) ∈ A := ⟨h0V₂, by rw [hq₂0]; exact hy₁⟩
  have hv₀B : v₀ ∈ Bs := ⟨hv₀, by rw [hq₁v₀]; exact hy₂⟩
  -- the maps `β = π₁ ∘ T ∘ Γ₂` and `α = π₂ ∘ T' ∘ Γ₁`
  set β : K₂ → K₁ := fun w => π₁ (T (Γ₂ w)) with hβ
  set α : K₁ → K₂ := fun v => π₂ (T' (Γ₁ v)) with hα
  have hβa : ∀ w, β w = π₁ (T (Γ₂ w)) := fun w => rfl
  have hαa : ∀ v, α v = π₂ (T' (Γ₁ v)) := fun v => rfl
  -- for `w ∈ A`: `T(Γ₂ w) = Γ₁(β w)`, `β w ∈ Bs`, `α (β w) = w`, `Γ₂ w ∈ Ō₂`
  have hAfacts : ∀ w ∈ A, T (Γ₂ w) = Γ₁ (β w) ∧ β w ∈ Bs ∧ α (β w) = w ∧
      Γ₂ w ∈ χ₂.overlap χ₁ := by
    intro w hw
    obtain ⟨⟨hqS, hqVx₂⟩, hqχ⟩ := hq₂ w hw.1
    set q := χ₂.symm (Γ₂ w) with hqdef
    have hqVx₁ : q ∈ Vx₁ := hw.2
    have hTw : T (Γ₂ w) = χ₁ q := by rw [← hqχ, hTq q (hVx₂ hqVx₂)]
    have : χ₁ q ∈ χ₁ '' (S ∩ Vx₁) := ⟨q, ⟨hqS, hqVx₁⟩, rfl⟩
    rw [himage₁] at this
    obtain ⟨v, hv, hvq⟩ := this
    have hβw : β w = v := by rw [hβa, hTw, ← hvq, hπ₁Γ]
    have hq₁v : χ₁.symm (Γ₁ v) = q := by rw [hvq, χ₁.symm_apply_apply (hVx₁ hqVx₁)]
    refine ⟨by rw [hTw, hβw, hvq], ⟨hβw ▸ hv, by rw [hβw, hq₁v]; exact hqVx₂⟩, ?_, ?_⟩
    · rw [hαa, hβw, hvq, hT'q q (hVx₁ hqVx₁), hqχ, hπ₂Γ]
    · rw [← hqχ]; exact χ₂.mem_overlap χ₁ (hVx₂ hqVx₂) (hVx₁ hqVx₁)
  have hBfacts : ∀ v ∈ Bs, T' (Γ₁ v) = Γ₂ (α v) ∧ α v ∈ A ∧ β (α v) = v := by
    intro v hv
    obtain ⟨⟨hqS, hqVx₁⟩, hqχ⟩ := hq₁ v hv.1
    set q := χ₁.symm (Γ₁ v) with hqdef
    have hqVx₂ : q ∈ Vx₂ := hv.2
    have hT'v : T' (Γ₁ v) = χ₂ q := by rw [← hqχ, hT'q q (hVx₁ hqVx₁)]
    have : χ₂ q ∈ χ₂ '' (S ∩ Vx₂) := ⟨q, ⟨hqS, hqVx₂⟩, rfl⟩
    rw [himage₂] at this
    obtain ⟨w, hw, hwq⟩ := this
    have hαv : α v = w := by rw [hαa, hT'v, ← hwq, hπ₂Γ]
    have hq₂w : χ₂.symm (Γ₂ w) = q := by rw [hwq, χ₂.symm_apply_apply (hVx₂ hqVx₂)]
    refine ⟨by rw [hT'v, hαv, hwq], ⟨hαv ▸ hw, by rw [hαv, hq₂w]; exact hqVx₁⟩, ?_⟩
    rw [hβa, hαv, hwq, hTq q (hVx₂ hqVx₂), hqχ, hπ₁Γ]
  have hβ0 : β 0 = v₀ := by
    rw [hβa, hΓ₂0, ← hχ₂y, hTq y (hVx₂ hy₂), hχ₁y, ← hΓ₁a, hπ₁Γ]
  have hαcont : ContinuousOn α Bs := by
    have h1 : ContinuousOn (fun v => T' (Γ₁ v)) Bs := by
      have : ContinuousOn (fun v => χ₂ (χ₁.symm (Γ₁ v))) Bs :=
        χ₂.continuousOn_toFun.comp (hq₁cont.mono hBV₁) fun v hv => hVx₂ hv.2
      exact this
    exact π₂.continuous.comp_continuousOn h1
  -- `β(A') = Bs ∩ α⁻¹(A')` for `A' ⊆ A`, relatively open when `A'` is
  have hβimage : ∀ A' ⊆ A, β '' A' = {v | v ∈ Bs ∧ α v ∈ A'} := by
    intro A' hA'
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(hAfacts w (hA' hw)).2.1, by rw [(hAfacts w (hA' hw)).2.2.1]; exact hw⟩
    · rintro ⟨hv, hαv⟩
      exact ⟨α v, hαv, (hBfacts v hv).2.2⟩
  have hβimage_rel : ∀ A' ⊆ A, (∃ O : Set K₂, IsOpen O ∧ A' = O ∩ Subtype.val ⁻¹' χ₂.model.C) →
      ∃ O : Set K₁, IsOpen O ∧ β '' A' = O ∩ Subtype.val ⁻¹' χ₁.model.C := by
    intro A' hA' hA'rel
    obtain ⟨O', hO', hA'eq⟩ := hA'rel
    obtain ⟨u, hu, huB⟩ := (continuousOn_iff'.1 hαcont) O' hO'
    obtain ⟨OB', hOB', hBeq'⟩ := hBrel
    refine ⟨u ∩ OB', hu.inter hOB', ?_⟩
    rw [hβimage A' hA']
    ext v
    have h1 : v ∈ α ⁻¹' O' ∩ Bs ↔ v ∈ u ∩ Bs := by rw [huB]
    simp only [mem_inter_iff, mem_preimage] at h1
    simp only [mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨hvB, hαv⟩
      have hvO' : α v ∈ O' := (hA'eq ▸ hαv : α v ∈ O' ∩ _).1
      exact ⟨⟨(h1.1 ⟨hvO', hvB⟩).1, (hBeq' ▸ hvB : v ∈ OB' ∩ _).1⟩, (hBeq' ▸ hvB : v ∈ OB' ∩ _).2⟩
    · rintro ⟨⟨hvu, hvOB⟩, hvC⟩
      have hvB : v ∈ Bs := by rw [hBeq']; exact ⟨hvOB, hvC⟩
      have hαO' : α v ∈ O' := (h1.2 ⟨hvu, hvB⟩).1
      refine ⟨hvB, ?_⟩
      rw [hA'eq]
      exact ⟨hαO', hV₂C (hAV₂ (hBfacts v hvB).2.1)⟩
  -- the lifted graph maps: for `j ≥ 1`, `Γ_{2,j} = ι_j + σ_{2,j}` on `A_j = A ∩ V_j`
  have hliftΓ : ∀ j : ℕ, 1 ≤ j → ∃ (Aj : Set K₂) (Γj : K₂ → χ₂.model.E j),
      (∃ O : Set K₂, IsOpen O ∧ Aj = O ∩ Subtype.val ⁻¹' χ₂.model.C) ∧ (0 : K₂) ∈ Aj ∧ Aj ⊆ A ∧
      ContDiffOn ℝ j Γj Aj ∧ (∀ w ∈ Aj, χ₂.model.E.toBase j (Γj w) = Γ₂ w) ∧
      HasFDerivWithinAt Γj (χ₂.model.E.finLift hK₂ j) Aj 0 ∧
      MapsTo Γj Aj (χ₂.model.E.lvlSet R₂.U j) ∧ (∀ w ∈ Aj, R₂ (Γ₂ w) = Γ₂ w) := by
    intro j hj
    obtain ⟨Vj, ⟨Oj, hOj, hVjeq⟩, h0Vj, hVjV₂, σj, hσj, hσjeq⟩ := hlift j hj
    obtain ⟨OA', hOA', hAeq'⟩ := hArel
    set Aj := A ∩ Vj with hAj
    have hAjrel : ∃ O : Set K₂, IsOpen O ∧ Aj = O ∩ Subtype.val ⁻¹' χ₂.model.C :=
      ⟨OA' ∩ Oj, hOA'.inter hOj, by
        rw [hAj, hAeq', hVjeq]; ext w; simp only [mem_inter_iff, mem_preimage]; tauto⟩
    have hAjA : Aj ⊆ A := inter_subset_left
    have h0Aj : (0 : K₂) ∈ Aj := ⟨h0A, h0Vj⟩
    set Γj : K₂ → χ₂.model.E j := fun w => χ₂.model.E.finLift hK₂ j w + σj w with hΓj
    have hΓjeq : ∀ w ∈ Aj, χ₂.model.E.toBase j (Γj w) = Γ₂ w := fun w hw => by
      rw [hΓj]; simp only; rw [map_add, χ₂.model.E.toBase_finLift, hσjeq w hw.2, hΓ₂a]
    have hΓjC : ContDiffOn ℝ j Γj Aj :=
      ((χ₂.model.E.finLift hK₂ j).contDiff.contDiffOn).add (hσj.mono inter_subset_right)
    have hjne : (j : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    have huniq : UniqueDiffWithinAt ℝ Aj 0 :=
      uniqueDiffOn_relOpen_convex hC₂conv hC₂int hAjrel 0 h0Aj
    -- `Dσ_{2,j}(0) = 0`
    have hDσj : fderivWithin ℝ σj Aj 0 = 0 := by
      have h1 : fderivWithin ℝ (fun w => χ₂.model.E.toBase j (σj w)) Aj 0 =
          (χ₂.model.E.toBase j).comp (fderivWithin ℝ σj Aj 0) :=
        ((χ₂.model.E.toBase j).hasFDerivAt.comp_hasFDerivWithinAt 0
          ((hσj.differentiableOn hjne 0 h0Vj).mono
            (inter_subset_right (s := A))).hasFDerivWithinAt).fderivWithin huniq
      have h2 : fderivWithin ℝ (fun w => χ₂.model.E.toBase j (σj w)) Aj 0 = fderivWithin ℝ σ₂ Aj 0 :=
        fderivWithin_congr (fun w hw => hσjeq w hw.2) (hσjeq 0 h0Vj)
      have h3 : fderivWithin ℝ σ₂ Aj 0 = fderivWithin ℝ σ₂ V₂ 0 := by
        obtain ⟨O', hO', hAj'⟩ := hAjrel
        obtain ⟨O₂, hO₂, hV₂'⟩ := hV₂
        have : Aj = V₂ ∩ O' := by
          ext w
          constructor
          · intro hw; exact ⟨hVjV₂ hw.2, (hAj' ▸ hw : w ∈ O' ∩ _).1⟩
          · rintro ⟨hwV, hwO'⟩; rw [hAj']; exact ⟨hwO', hV₂C hwV⟩
        rw [this, fderivWithin_inter (hO'.mem_nhds (hAj' ▸ h0Aj : (0 : K₂) ∈ O' ∩ _).1)]
      rw [h3, hDσ₂] at h2
      rw [h2] at h1
      ext n
      apply χ₂.model.E.toBase_injective j
      have := congrArg (fun L : K₂ →L[ℝ] χ₂.model.E 0 => L n) h1
      simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply] at this
      rw [← this, ContinuousLinearMap.zero_apply, map_zero]
    have hΓjD : HasFDerivWithinAt Γj (χ₂.model.E.finLift hK₂ j) Aj 0 := by
      have h1 : HasFDerivWithinAt σj (0 : K₂ →L[ℝ] χ₂.model.E j) Aj 0 := by
        have := ((hσj.differentiableOn hjne 0 h0Vj).mono (inter_subset_right (s := A))).hasFDerivWithinAt
        rwa [hDσj] at this
      have h2 := (χ₂.model.E.finLift hK₂ j).hasFDerivWithinAt (s := Aj) (x := (0 : K₂))
      have := h2.add h1
      rwa [add_zero] at this
    have hfix : ∀ w ∈ Aj, R₂ (Γ₂ w) = Γ₂ w := fun w hw =>
      R₂.apply_eq_self_of_mem_retract (hR₂ ▸ (hAfacts w (hAjA hw)).2.2.2)
    have hmaps : MapsTo Γj Aj (χ₂.model.E.lvlSet R₂.U j) := fun w hw => by
      rw [ScBanach.mem_lvlSet, hΓjeq w hw]
      exact R₂.retract_subset (hR₂ ▸ (hAfacts w (hAjA hw)).2.2.2)
    exact ⟨Aj, Γj, hAjrel, h0Aj, hAjA, hΓjC, hΓjeq, hΓjD, hmaps, hfix⟩
  -- `β` on `A_j` through the lift: `β = π₁ ∘ ((T ∘ r₂) ∘ ι_j) ∘ Γ_j` is `C^j`
  have hβlift : ∀ (j : ℕ) (Aj : Set K₂) (Γj : K₂ → χ₂.model.E j), (∀ w ∈ Aj, χ₂.model.E.toBase j (Γj w) = Γ₂ w) →
      (∀ w ∈ Aj, R₂ (Γ₂ w) = Γ₂ w) → ∀ w ∈ Aj, β w = π₁ (((T ∘ R₂) ∘ χ₂.model.E.toBase j) (Γj w)) := by
    intro j Aj Γj hΓjeq hfix w hw
    rw [hβa]
    simp only [Function.comp_apply]
    rw [hΓjeq w hw, hfix w hw]
  have hβC : ∀ (j : ℕ) (Aj : Set K₂) (Γj : K₂ → χ₂.model.E j), ContDiffOn ℝ j Γj Aj →
      (∀ w ∈ Aj, χ₂.model.E.toBase j (Γj w) = Γ₂ w) → MapsTo Γj Aj (χ₂.model.E.lvlSet R₂.U j) →
      (∀ w ∈ Aj, R₂ (Γ₂ w) = Γ₂ w) → ContDiffOn ℝ j β Aj := by
    intro j Aj Γj hΓjC hΓjeq hmaps hfix
    have h1 : ContDiffOn ℝ j ((T ∘ R₂) ∘ χ₂.model.E.toBase j) (χ₂.model.E.lvlSet R₂.U j) :=
      (hTR j).contDiffOn_base R₂.isScDomain
    have h2 : ContDiffOn ℝ j (fun w => π₁ (((T ∘ R₂) ∘ χ₂.model.E.toBase j) (Γj w))) Aj :=
      π₁.contDiff.comp_contDiffOn (h1.comp hΓjC hmaps)
    exact h2.congr fun w hw => hβlift j Aj Γj hΓjeq hfix w hw
  -- Step 1: the derivative of `β` at `0` is injective, with `j = 2`
  obtain ⟨A₂, Γ₂₂, hA₂rel, h0A₂, hA₂A, hΓ₂₂C, hΓ₂₂eq, hΓ₂₂D, hΓ₂₂maps, hfix₂⟩ := hliftΓ 2 (by norm_num)
  have hβC₂ : ContDiffOn ℝ 2 β A₂ := hβC 2 A₂ Γ₂₂ hΓ₂₂C hΓ₂₂eq hΓ₂₂maps hfix₂
  have hβC₁ : ContDiffOn ℝ 1 β A₂ := hβC₂.of_le (by norm_num)
  have huniqA₂ : UniqueDiffWithinAt ℝ A₂ 0 := uniqueDiffOn_relOpen_convex hC₂conv hC₂int hA₂rel 0 h0A₂
  set Dβ : K₂ →L[ℝ] K₁ := fderivWithin ℝ β A₂ 0 with hDβ
  have hβD : HasFDerivWithinAt β Dβ A₂ 0 :=
    (hβC₁.differentiableOn one_ne_zero 0 h0A₂).hasFDerivWithinAt
  -- the level-`1` lift `Γ₂₁ = incl ∘ Γ₂₂`
  set Γ₂₁ : K₂ → χ₂.model.E 1 := fun w => χ₂.model.E.incl 1 (Γ₂₂ w) with hΓ₂₁
  have hΓ₂₁eq : ∀ w ∈ A₂, χ₂.model.E.toBase 1 (Γ₂₁ w) = Γ₂ w := fun w hw => by
    rw [hΓ₂₁]; simp only; rw [← ScScale.toBase_succ, hΓ₂₂eq w hw]
  have hΓ₂₁D : HasFDerivWithinAt Γ₂₁ ((χ₂.model.E.incl 1).comp (χ₂.model.E.finLift hK₂ 2)) A₂ 0 :=
    (χ₂.model.E.incl 1).hasFDerivAt.comp_hasFDerivWithinAt 0 hΓ₂₂D
  have hΓ₂₁maps : MapsTo Γ₂₁ A₂ (χ₂.model.E.lvlSet R₂.U 1) := fun w hw => by
    rw [ScBanach.mem_lvlSet, hΓ₂₁eq w hw]
    exact R₂.retract_subset (hR₂ ▸ (hAfacts w (hA₂A hw)).2.2.2)
  have hΓ₂₁0 : χ₂.model.E.toBase 1 (Γ₂₁ 0) = 0 := by rw [hΓ₂₁eq 0 h0A₂, hΓ₂0]
  have htb₁ : ∀ n : K₂, χ₂.model.E.toBase 1 (χ₂.model.E.incl 1 (χ₂.model.E.finLift hK₂ 2 n)) = n :=
    fun n => by rw [← ScScale.toBase_succ, χ₂.model.E.toBase_finLift]
  -- `D(T ∘ r₂)(0) n = Dβ n + Dσ₁(v₀)(Dβ n)`
  set D : χ₂.model.E 0 →L[ℝ] χ₁.model.E 0 := scDeriv R₂.U (T ∘ R₂) (Γ₂₁ 0) with hD
  have hderiv : ∀ n : K₂, D n = (Dβ n : χ₁.model.E 0) + fderivWithin ℝ σ₁ V₁ v₀ (Dβ n) := by
    have hF : HasFDerivWithinAt (((T ∘ R₂) ∘ χ₂.model.E.toBase 1) ∘ Γ₂₁)
        ((D.comp (χ₂.model.E.toBase 1)).comp ((χ₂.model.E.incl 1).comp (χ₂.model.E.finLift hK₂ 2))) A₂ 0 :=
      (hTR.isSc1.isSc1With_scDeriv.hasFDerivWithinAt (Γ₂₁ 0) (hΓ₂₁maps h0A₂)).comp 0 hΓ₂₁D hΓ₂₁maps
    have hΓ₁D : HasFDerivWithinAt Γ₁ (K₁.subtypeL + fderivWithin ℝ σ₁ V₁ v₀) V₁ v₀ :=
      K₁.subtypeL.hasFDerivWithinAt.add (hσ₁.differentiableOn one_ne_zero v₀ hv₀).hasFDerivWithinAt
    have hβmaps : MapsTo β A₂ V₁ := fun w hw => hBV₁ (hAfacts w (hA₂A hw)).2.1
    have hG : HasFDerivWithinAt (Γ₁ ∘ β)
        ((K₁.subtypeL + fderivWithin ℝ σ₁ V₁ v₀).comp Dβ) A₂ 0 := by
      have hΓ₁D' : HasFDerivWithinAt Γ₁ (K₁.subtypeL + fderivWithin ℝ σ₁ V₁ v₀) V₁ (β 0) := by
        rw [hβ0]; exact hΓ₁D
      exact hΓ₁D'.comp 0 hβD hβmaps
    have hFG : HasFDerivWithinAt (Γ₁ ∘ β)
        ((D.comp (χ₂.model.E.toBase 1)).comp ((χ₂.model.E.incl 1).comp (χ₂.model.E.finLift hK₂ 2))) A₂ 0 := by
      refine hF.congr (fun w hw => ?_) ?_
      · simp only [Function.comp_apply]
        rw [hΓ₂₁eq w hw, hfix₂ w hw, (hAfacts w (hA₂A hw)).1]
      · simp only [Function.comp_apply]
        rw [hΓ₂₁eq 0 h0A₂, hfix₂ 0 h0A₂, (hAfacts 0 (hA₂A h0A₂)).1]
    have heq := huniqA₂.eq hFG hG
    intro n
    have := congrArg (fun L : K₂ →L[ℝ] χ₁.model.E 0 => L n) heq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      Submodule.subtypeL_apply] at this
    rw [htb₁ n] at this
    exact this
  -- injectivity of `Dβ`: if `Dβ n = 0` then `D n = 0`, then `Dr₂(0) n = 0`, but `Dr₂(0) n = n`
  have hmapsTR : MapsTo (T ∘ R₂) R₂.U R₁.U := fun u hu => by
    have h1 : R₂ u ∈ χ₂.overlap χ₁ := hR₂ ▸ R₂.apply_mem_retract hu
    exact R₁.retract_subset (hR₁ ▸ hTmap.mapsTo h1)
  have heqR : EqOn ((T' ∘ R₁) ∘ (T ∘ R₂)) R₂ R₂.U := fun u hu => by
    have h1 : R₂ u ∈ χ₂.overlap χ₁ := hR₂ ▸ R₂.apply_mem_retract hu
    have h2 : T (R₂ u) ∈ R₁.retract := hR₁ ▸ hTmap.mapsTo h1
    simp only [Function.comp_apply]
    rw [R₁.apply_eq_self_of_mem_retract h2, hT'T _ h1]
  have hcompSc : IsSc1 R₂.U ((T' ∘ R₁) ∘ (T ∘ R₂)) :=
    (IsScSmooth.comp R₂.isScDomain R₁.isScDomain hT'R hTR hmapsTR).isSc1
  have hfix₁ : ∀ w ∈ A₂, R₂ (χ₂.model.E.toBase 1 (Γ₂₁ w)) = χ₂.model.E.toBase 1 (Γ₂₁ w) :=
    fun w hw => by rw [hΓ₂₁eq w hw]; exact hfix₂ w hw
  have hDR : ∀ n : K₂, scDeriv R₂.U R₂ (Γ₂₁ 0) n = n := fun n => by
    have := scDeriv_apply_toBase_deriv_eq_of_fixed R₂.isSc1 hΓ₂₁D huniqA₂ h0A₂ hΓ₂₁maps hfix₁ n
    rwa [ContinuousLinearMap.comp_apply, htb₁ n] at this
  have hDβinj : Injective Dβ := by
    intro n₁ n₂ hn
    have hn' : Dβ (n₁ - n₂) = 0 := by rw [map_sub, hn, sub_self]
    suffices h : n₁ - n₂ = 0 from sub_eq_zero.1 h
    set n := n₁ - n₂ with hndef
    have hDn : D n = 0 := by rw [hderiv n, hn', Submodule.coe_zero, map_zero, add_zero]
    have h1 := scDeriv_comp_apply R₂.relOpen R₁.relOpen hTR.isSc1 hT'R.isSc1 hmapsTR (hΓ₂₁maps h0A₂)
      (n : χ₂.model.E 0)
    rw [← hD, hDn, map_zero] at h1
    have h2 := scDeriv_eq_of_eqOn_relOpen R₂.relOpen hcompSc R₂.isSc1 subset_rfl subset_rfl heqR
      (hΓ₂₁maps h0A₂)
    have h3 : scDeriv R₂.U ((T' ∘ R₁) ∘ (T ∘ R₂)) (Γ₂₁ 0) n = n := by rw [h2]; exact hDR n
    rw [← h1] at h3
    exact Submodule.coe_eq_zero.1 h3.symm
  have hdim₂₁ : finrank ℝ K₂ ≤ finrank ℝ K₁ :=
    LinearMap.finrank_le_finrank_of_injective (f := (Dβ : K₂ →ₗ[ℝ] K₁)) hDβinj
  -- Step 2: `dim K₁ ≤ dim K₂` by Sard's lemma in fixed dimension
  have hdim₁₂ : finrank ℝ K₁ ≤ finrank ℝ K₂ := by
    refine finrank_le_of_interior_image_nonempty (f := β) (s := A₂)
      (hβC₁.differentiableOn one_ne_zero) ?_
    exact interior_nonempty_of_relOpen_convex hC₁conv hC₁int (hβimage_rel A₂ hA₂A hA₂rel)
      ⟨β 0, 0, h0A₂, rfl⟩
  have hdim : finrank ℝ K₁ = finrank ℝ K₂ := le_antisymm hdim₁₂ hdim₂₁
  have hDβsurj : Surjective Dβ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (Dβ : K₂ →ₗ[ℝ] K₁))
      hdim.symm).1 hDβinj
  -- the isomorphism `L = Dβ(0) : K₂ ≅ K₁`
  set L : K₂ ≃L[ℝ] K₁ :=
    (LinearEquiv.ofBijective (Dβ : K₂ →ₗ[ℝ] K₁) ⟨hDβinj, hDβsurj⟩).toContinuousLinearEquiv with hL
  have hLeq : (L : K₂ →L[ℝ] K₁) = Dβ := by ext n; rfl
  refine ⟨hdim, fun m k => ?_⟩
  -- Step 3: for `(m, k)`, the lift with `j = m + (k + 2)`
  obtain ⟨Aj, Γj, hAjrel, h0Aj, hAjA, hΓjC, hΓjeq, hΓjD, hΓjmaps, hfixj⟩ :=
    hliftΓ (m + (k + 2)) (by omega)
  have hβCj : ContDiffOn ℝ (m + (k + 2) : ℕ) β Aj := hβC _ Aj Γj hΓjC hΓjeq hΓjmaps hfixj
  have hk1 : 1 ≤ max k 1 := le_max_right _ _
  have hβCk : ContDiffOn ℝ (max k 1 : ℕ) β Aj :=
    hβCj.of_le (by exact_mod_cast (show max k 1 ≤ m + (k + 2) by omega))
  have hβAjBs : β '' Aj ⊆ Bs := by
    rintro _ ⟨w, hw, rfl⟩; exact (hAfacts w (hAjA hw)).2.1
  -- the derivative of `β` at `0` within `Aj` is `L`
  have hDβj : fderivWithin ℝ β Aj 0 = L := by
    rw [hLeq, hDβ]
    obtain ⟨O, hO, hAjO⟩ := hAjrel
    obtain ⟨O', hO', hA₂O⟩ := hA₂rel
    have h0O : (0 : K₂) ∈ O := (hAjO ▸ h0Aj : (0 : K₂) ∈ O ∩ _).1
    have h0O' : (0 : K₂) ∈ O' := (hA₂O ▸ h0A₂ : (0 : K₂) ∈ O' ∩ _).1
    rw [hAjO, hA₂O, inter_comm O, inter_comm O', fderivWithin_inter (hO.mem_nhds h0O),
      fderivWithin_inter (hO'.mem_nhds h0O')]
  -- the inverse `α` is `C^k` on a relatively open neighbourhood `B'` of `v₀ = β 0`
  obtain ⟨B', hB'rel, hv₀B', hB'sub, hαC⟩ := exists_contDiffOn_inverse hC₂conv hC₂int hC₁conv hC₁int
    hAjrel (hβimage_rel Aj hAjA hAjrel) (hαcont.mono hβAjBs)
    (fun w hw => (hAfacts w (hAjA hw)).2.2.1) h0Aj hk1 hβCk L hDβj
  have hαmaps : MapsTo α B' Aj := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := hB'sub hv
    rw [(hAfacts w (hAjA hw)).2.2.1]; exact hw
  -- the map `Ψ(w) = (T ∘ r₂)_m(ι Γ_j(w)) − ι_m(β w)` with `ι_m Ψ(w) = σ₁(β w)`
  set Ψ : K₂ → χ₁.model.E m := fun w =>
    levelMap (T ∘ R₂) m (χ₂.model.E.inclK m (k + 2) (Γj w)) - χ₁.model.E.finLift hK₁ m (β w) with hΨ
  have hΨC : ContDiffOn ℝ k Ψ Aj := by
    have h1 : ContDiffOn ℝ k (levelMap (T ∘ R₂) m ∘ χ₂.model.E.inclK m (k + 2))
        (χ₂.model.E.lvlSet R₂.U (m + (k + 2))) :=
      ((hTR (k + 2)).contDiffOn_levels R₂.isScDomain m).of_le
        (by exact_mod_cast (show k ≤ k + 2 by omega))
    have h2 : ContDiffOn ℝ k (fun w => levelMap (T ∘ R₂) m (χ₂.model.E.inclK m (k + 2) (Γj w))) Aj :=
      h1.comp (hΓjC.of_le (by exact_mod_cast (show k ≤ m + (k + 2) by omega))) hΓjmaps
    exact h2.sub ((χ₁.model.E.finLift hK₁ m).contDiff.comp_contDiffOn
      (hβCj.of_le (by exact_mod_cast (show k ≤ m + (k + 2) by omega))))
  have hΨeq : ∀ w ∈ Aj, χ₁.model.E.toBase m (Ψ w) = σ₁ (β w) := by
    intro w hw
    have hx : χ₂.model.E.inclK m (k + 2) (Γj w) ∈ χ₂.model.E.lvlSet R₂.U m := by
      rw [ScBanach.mem_lvlSet, ScScale.toBase_inclK]
      exact hΓjmaps hw
    have h1 : χ₁.model.E.toBase m (levelMap (T ∘ R₂) m (χ₂.model.E.inclK m (k + 2) (Γj w))) =
        Γ₁ (β w) := by
      rw [hTR.isSc1.isSc0.toBase_levelMap hx, ScScale.toBase_inclK, hΓjeq w hw]
      simp only [Function.comp_apply]
      rw [hfixj w hw, (hAfacts w (hAjA hw)).1]
    rw [hΨ]
    simp only
    rw [map_sub, h1, χ₁.model.E.toBase_finLift, hΓ₁a, add_sub_cancel_left]
  refine ⟨B', hB'rel, hβ0 ▸ hv₀B', fun v hv => hBV₁ (hβAjBs (hB'sub hv)), fun v hv => ?_, ?_⟩
  · obtain ⟨w, hw, rfl⟩ := hB'sub hv
    exact ⟨Ψ w, hΨeq w hw⟩
  · refine ((hΨC.comp (hαC.of_le (by exact_mod_cast (le_max_left k 1))) hαmaps).congr
      fun v hv => ?_)
    obtain ⟨w, hw, rfl⟩ := hB'sub hv
    apply levelMap_eq_of_toBase_eq
    rw [ScBanach.const_toBase, Function.comp_apply, (hAfacts w (hAjA hw)).2.2.1]
    exact hΨeq w hw

end Recentre

/-! ### Tameness of an open subset of a tame retract -/

section TameRestrict

variable {E : ScBanach} {C : Set (E 0)}

/-- The restriction `r : U ∩ r⁻¹(W) → U ∩ r⁻¹(W)` of a tame retraction to an open subset `W`
(Proposition 2.3.1 (preprint 2.10) (1)) is tame: the degeneracy index condition is inherited, and at the points of
`O ∩ W` the derivative of the restricted retraction is `Dr(x)` (uniqueness of the derivative on a
smaller relatively open domain). -/
theorem ScRetraction.restrict_isTame (R : ScRetraction E C) {W : Set (E 0)} (hW : IsOpen W)
    (h : R.IsTame) : (R.restrict hW).IsTame := by
  intro n W' T hT
  obtain ⟨hdeg, hcompl⟩ := h n W' T hT
  refine ⟨fun x hx => hdeg x hx.1, fun x hx hxs => ?_⟩
  rw [R.restrict_retract hW, ScBanach.lvlSet_inter] at hx
  obtain ⟨A, hA, hAle⟩ := hcompl x hx.1 hxs
  refine ⟨A, ?_, hAle⟩
  have hD : scDeriv (R.restrict hW).U (R.restrict hW) x = scDeriv R.U R x := by
    refine scDeriv_eq_of_eqOn_relOpen (R.restrict hW).relOpen (R.restrict hW).isSc1 R.isSc1
      subset_rfl (by rw [R.restrict_U]; exact inter_subset_left) (fun z _ => rfl) ?_
    rw [ScBanach.mem_lvlSet, R.restrict_U]
    refine ⟨R.retract_subset hx.1, ?_⟩
    change R (E.toBase 1 x) ∈ W
    rw [R.apply_eq_self_of_mem_retract hx.1]
    exact hx.2
  rw [hD]
  exact hA

/-- An open subset `O ∩ W` of a tame retract is a tame retract. -/
theorem IsTameRetract.inter_isOpen {O : Set (E 0)} (h : IsTameRetract E C O) {W : Set (E 0)}
    (hW : IsOpen W) : IsTameRetract E C (O ∩ W) := by
  obtain ⟨R, rfl, hR⟩ := h
  exact ⟨R.restrict hW, R.restrict_retract hW, R.restrict_isTame hW hR⟩

end TameRestrict

section ChartRestrict

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The model `φ(s)` of the restriction of a chart `φ` to an open subset `s` of its source is tame
when the model of `φ` is. -/
theorem MChart.isTameRetract_image (φ : MChart X) {s : Set X} (hs : s ⊆ φ.source) (hso : IsOpen s)
    (htame : IsTameRetract φ.model.E φ.model.C φ.model.O) :
    IsTameRetract φ.model.E φ.model.C (φ '' s) := by
  obtain ⟨W, hW, hWs⟩ := φ.exists_isOpen_image_eq hs hso
  rw [hWs]
  exact htame.inter_isOpen hW

end ChartRestrict

/-! ### Shrinking the data of Definition 3.2.1 (preprint 3.25) (2) -/

namespace MPolyfold.TangentGermChart

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} {x : X} {n : ℕ} (D : P.TangentGermChart M x n)

/-- **Shrinking the data of Definition 3.2.1 (preprint 3.25) (2)**: the chart `ϕ` restricted to an open `s ⊆ U`
containing `x`, with a relatively open `V' ⊆ V` containing `0` such that `ϕ(M' ∩ s) = Γ(V')`, and
the same `N`, `Y`, `δ`; the set `M'` may differ from `M` as long as the graph identity holds (used
to pass from the solution set in a neighbourhood to the global solution set). -/
def shrink (M' : Set X) {s : Set X} (hs : s ⊆ D.φ.source) (hso : IsOpen s) (hxs : x ∈ s)
    {V' : Set D.N} (hV' : ∃ O : Set D.N, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' D.φ.model.C)
    (h0 : (0 : D.N) ∈ V') (hV'V : V' ⊆ D.V)
    (himage : D.φ '' (M' ∩ s) = (fun v : D.N => (v : D.φ.model.E 0) + D.δ v) '' V') :
    P.TangentGermChart M' x n where
  φ := D.φ.restrict hs hso
  isChart := MPolyfold.IsChart.restrict P D.isChart hs hso
  mem_source := hxs
  φ_zero := D.φ_zero
  tame := D.φ.isTameRetract_image hs hso D.tame
  N := D.N
  finiteDimensional := D.finiteDimensional
  finrank_eq := D.finrank_eq
  smooth := D.smooth
  goodPosition := D.goodPosition
  Y := D.Y
  goodComplement := D.goodComplement
  isClosed_Y := D.isClosed_Y
  V := V'
  V_relOpen := hV'
  zero_mem_V := h0
  δ := D.δ
  δ_mem_Y := D.δ_mem_Y
  continuousOn := D.continuousOn.mono hV'V
  image_eq := himage
  germ := D.germ
  δ_zero := D.δ_zero
  fderivWithin_zero := D.fderivWithin_zero

variable (M' : Set X) {s : Set X} (hs : s ⊆ D.φ.source) (hso : IsOpen s) (hxs : x ∈ s)
  {V' : Set D.N} (hV' : ∃ O : Set D.N, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' D.φ.model.C)
  (h0 : (0 : D.N) ∈ V') (hV'V : V' ⊆ D.V)
  (himage : D.φ '' (M' ∩ s) = (fun v : D.N => (v : D.φ.model.E 0) + D.δ v) '' V')

@[simp] lemma shrink_φ_source : (D.shrink M' hs hso hxs hV' h0 hV'V himage).φ.source = s := rfl

lemma shrink_φ_model_O : (D.shrink M' hs hso hxs hV' h0 hV'V himage).φ.model.O = D.φ '' s := rfl

lemma shrink_φ_apply (z : X) : (D.shrink M' hs hso hxs hV' h0 hV'V himage).φ z = D.φ z := rfl

lemma shrink_N : (D.shrink M' hs hso hxs hV' h0 hV'V himage).N = D.N := rfl

lemma shrink_V : (D.shrink M' hs hso hxs hV' h0 hV'V himage).V = V' := rfl

lemma shrink_δ : (D.shrink M' hs hso hxs hV' h0 hV'V himage).δ = D.δ := rfl

lemma shrink_π : (D.shrink M' hs hso hxs hV' h0 hV'V himage).π = D.π := rfl

/-- The shrunk data are regular when `δ` is sc-smooth on `V'` and `π(O) ⊆ C` for the original
retract (condition (b) passes to the smaller retract `ϕ(s) ⊆ O`). -/
theorem shrink_isRegular
    (hδ : IsScSmooth (E := ScBanach.const D.N) (F := D.φ.model.E) V' D.δ)
    (hπ : ∀ z ∈ D.φ.model.O, (D.π z : D.φ.model.E 0) ∈ D.φ.model.C) :
    (D.shrink M' hs hso hxs hV' h0 hV'V himage).IsRegular where
  isScSmooth := hδ
  π_mem := fun z hz => hπ z (D.φ.image_subset_model hs hz)

/-- **The shrinking data**: for an open `W ∋ x` and an open `O'' ∋ 0` in `N`, the open set
`s = {y ∈ U ∩ W | π ϕ(y) ∈ O''}` and the relatively open `V' = {v ∈ V ∩ O'' | ϕ⁻¹(v + δ(v)) ∈ W}`
satisfy `ϕ(M ∩ s) = Γ(V')`. -/
theorem exists_shrinkData {W : Set X} (hW : IsOpen W) (hxW : x ∈ W) {O'' : Set D.N}
    (hO'' : IsOpen O'') (h0'' : (0 : D.N) ∈ O'') :
    ∃ (s : Set X) (V' : Set D.N), s ⊆ D.φ.source ∧ IsOpen s ∧ x ∈ s ∧ s ⊆ W ∧
      (∃ O : Set D.N, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' D.φ.model.C) ∧ (0 : D.N) ∈ V' ∧
      V' ⊆ D.V ∧ V' ⊆ O'' ∧
      D.φ '' (M ∩ s) = (fun v : D.N => (v : D.φ.model.E 0) + D.δ v) '' V' := by
  classical
  set s : Set X := (D.φ.source ∩ W) ∩ D.φ ⁻¹' (D.π ⁻¹' O'') with hsdef
  set V' : Set D.N := {v | v ∈ D.V ∧ v ∈ O'' ∧ D.φ.symm (D.Γ v) ∈ W} with hV'def
  have hso : IsOpen s := by
    rw [hsdef]
    exact (D.φ.continuousOn_toFun.mono inter_subset_left).isOpen_inter_preimage
      (D.φ.isOpen_source.inter hW) (hO''.preimage D.π.continuous)
  have hs : s ⊆ D.φ.source := fun y hy => hy.1.1
  have hxs : x ∈ s := ⟨⟨D.mem_source, hxW⟩, by
    change D.π (D.φ x) ∈ O''
    rw [D.φ_zero, map_zero]; exact h0''⟩
  have hcont : ContinuousOn (fun v => D.φ.symm (D.Γ v)) D.V :=
    D.φ.continuousOn_invFun.comp D.Γ_continuousOn fun v hv => D.Γ_mem_O hv
  obtain ⟨u, hu, huV⟩ := (continuousOn_iff'.1 hcont) W hW
  have hV'rel : ∃ O : Set D.N, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' D.φ.model.C := by
    obtain ⟨OV, hOV, hVeq⟩ := D.V_relOpen
    refine ⟨OV ∩ O'' ∩ u, (hOV.inter hO'').inter hu, ?_⟩
    ext v
    have h1 := congrArg (v ∈ ·) huV
    simp only [mem_inter_iff, mem_preimage, eq_iff_iff] at h1
    constructor
    · rintro ⟨hvV, hvO, hvW⟩
      exact ⟨⟨⟨(hVeq ▸ hvV : v ∈ OV ∩ _).1, hvO⟩, (h1.1 ⟨hvW, hvV⟩).1⟩, (hVeq ▸ hvV : v ∈ OV ∩ _).2⟩
    · rintro ⟨⟨⟨hvOV, hvO⟩, hvu⟩, hvC⟩
      have hvV : v ∈ D.V := by rw [hVeq]; exact ⟨hvOV, hvC⟩
      exact ⟨hvV, hvO, (h1.2 ⟨hvu, hvV⟩).1⟩
  have h0V' : (0 : D.N) ∈ V' := ⟨D.zero_mem_V, h0'', by
    change D.φ.symm (D.Γ 0) ∈ W
    rw [D.Γ_apply, Submodule.coe_zero, D.δ_zero, add_zero, ← D.φ_zero,
      D.φ.symm_apply_apply D.mem_source]
    exact hxW⟩
  refine ⟨s, V', hs, hso, hxs, fun y hy => hy.1.2, hV'rel, h0V', fun v hv => hv.1,
    fun v hv => hv.2.1, ?_⟩
  ext z
  constructor
  · rintro ⟨y, ⟨hyM, hys⟩, rfl⟩
    obtain ⟨hv, heq⟩ := D.exists_eq_Γ ⟨hyM, hs hys⟩
    refine ⟨D.π (D.φ y), ⟨hv, hys.2, ?_⟩, heq.symm⟩
    change D.φ.symm (D.Γ (D.π (D.φ y))) ∈ W
    rw [← heq, D.φ.symm_apply_apply (hs hys)]
    exact hys.1.2
  · rintro ⟨v, ⟨hvV, hvO, hvW⟩, rfl⟩
    have hmem := D.symm_Γ_mem hvV
    refine ⟨D.φ.symm (D.Γ v), ⟨hmem.1, ⟨⟨hmem.2, hvW⟩, ?_⟩⟩, D.φ.apply_symm_apply (D.Γ_mem_O hvV)⟩
    change D.π (D.φ (D.φ.symm (D.Γ v))) ∈ O''
    rw [D.φ.apply_symm_apply (D.Γ_mem_O hvV), D.π_Γ]
    exact hvO

end MPolyfold.TangentGermChart

/-! ### Condition (a) of `IsRegular` by re-centring -/

namespace MPolyfold.TangentGermChart

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} {x : X} {n : ℕ}

/-- The `C^k`-lifts of Theorem 3.5.11 (preprint 3.47) (1) from the sc^∞-germ property of Definition 3.2.1 (preprint 3.25) (ii): for
`k ≥ 1`, `levelMap δ k` on `V_{k,k} ∩ V`. -/
theorem exists_lift (D : P.TangentGermChart M x n) (k : ℕ) (_hk : 1 ≤ k) :
    ∃ Vk : Set D.N,
      (∃ O : Set D.N, IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' D.φ.model.C) ∧ (0 : D.N) ∈ Vk ∧
      Vk ⊆ D.V ∧ ∃ σk : D.N → D.φ.model.E k, ContDiffOn ℝ k σk Vk ∧
        ∀ w ∈ Vk, D.φ.model.E.toBase k (σk w) = D.δ w := by
  obtain ⟨Vk, ⟨Ok, hOk, hVk⟩, h0k, hmem, hC⟩ := D.germ k k
  obtain ⟨OV, hOV, hVeq⟩ := D.V_relOpen
  refine ⟨Vk ∩ D.V, ⟨Ok ∩ OV, hOk.inter hOV, ?_⟩, ⟨h0k, D.zero_mem_V⟩, inter_subset_right,
    levelMap (E := ScBanach.const D.N) (F := D.φ.model.E) D.δ k, hC.mono inter_subset_left,
    fun w hw => ?_⟩
  · rw [hVk, hVeq]; ext v; simp only [mem_inter_iff, mem_preimage]; tauto
  · have := hmem w hw.1
    rw [toBase_levelMap (by rw [ScBanach.const_toBase]; exact this), ScBanach.const_toBase]

/-- `Dδ(0) = 0` within `V`. -/
theorem fderivWithin_V_zero (D : P.TangentGermChart M x n) : fderivWithin ℝ D.δ D.V 0 = 0 := by
  obtain ⟨O, hO, hVeq⟩ := D.V_relOpen
  have h0O : (0 : D.N) ∈ O := (hVeq ▸ D.zero_mem_V : (0 : D.N) ∈ O ∩ _).1
  rw [hVeq, inter_comm, fderivWithin_inter (hO.mem_nhds h0O)]
  exact D.fderivWithin_zero

set_option maxHeartbeats 800000 in
/-- **Condition (a) of `IsRegular` by re-centring.**  Let `D` be the data of Definition 3.2.1 (preprint 3.25) (2)
for `M` at `x` with `π(O) ⊆ C` (condition (b)), and suppose that every point of `M` in an open
neighbourhood `U` of `x` has the data of Definition 3.2.1 (preprint 3.25) (2) (of some dimension).  Then the data
can be shrunk (same chart restricted to an open `s ⊆ U`, same `N`, `Y`, `δ`, smaller `V'`) to
regular data `D'` (`IsRegular`: `δ` is sc-smooth on `V'` in the set sense), and the dimension is
locally constant: every datum of Definition 3.2.1 (preprint 3.25) (2) at a point of `M ∩ s` has dimension `n`.
Proof: at `v₀ ∈ V'` the re-centring lemma `recentre_contDiffOn_levels` for `D'` and the data at
`y = ϕ⁻¹(v₀ + δ(v₀))` gives `δ` of class `C^k` into `E_m` near `v₀` for all `m`, `k`, and
`dim N = dim N_y`; sc-smoothness on `V'` is local (`contDiffOn_of_locally_contDiffOn`,
`IsScSmooth.of_contDiffOn_levels`). -/
theorem exists_isRegular_of_locally (D : P.TangentGermChart M x n)
    (hπ : ∀ z ∈ D.φ.model.O, (D.π z : D.φ.model.E 0) ∈ D.φ.model.C)
    {U : Set X} (hU : IsOpen U) (hxU : x ∈ U)
    (hM : ∀ y ∈ M ∩ U, ∃ n' : ℕ, Nonempty (P.TangentGermChart M y n')) :
    ∃ D' : P.TangentGermChart M x n, D'.IsRegular ∧ D'.φ.source ⊆ U ∧
      ∀ y ∈ M ∩ D'.φ.source, ∀ (n' : ℕ) (_ : P.TangentGermChart M y n'), n' = n := by
  classical
  -- the neighbourhood of `0` where `δ` is `C¹`, and the shrunk data `D₁`
  obtain ⟨V₁, ⟨O₁, hO₁, hV₁eq⟩, h0V₁, hC1⟩ := D.germ.contDiffOn_one
  have h0O₁ : (0 : D.N) ∈ O₁ := (hV₁eq ▸ h0V₁ : (0 : D.N) ∈ O₁ ∩ _).1
  obtain ⟨s, V', hs, hso, hxs, hsU, hV'rel, h0V', hV'V, hV'O₁, himage⟩ :=
    D.exists_shrinkData hU hxU hO₁ h0O₁
  have hV'V₁ : V' ⊆ V₁ := fun v hv => by rw [hV₁eq]; exact ⟨hV'O₁ hv, D.V_subset (hV'V hv)⟩
  set D₁ := D.shrink M hs hso hxs hV'rel h0V' hV'V himage with hD₁
  have hδC1 : ContDiffOn ℝ 1 D₁.δ D₁.V := hC1.mono hV'V₁
  have hVD₁ : D₁.V = V' := rfl
  have hδD₁ : D₁.δ = D.δ := rfl
  have hsrc : D₁.φ.source = s := rfl
  -- the key step: at every point `y ∈ M ∩ s`, with `v₀ = π ϕ(y)`
  have key : ∀ y ∈ M ∩ s, ∀ (n' : ℕ) (D'' : P.TangentGermChart M y n'),
      n = n' ∧ ∀ m k : ℕ, ∃ B' : Set D₁.N,
        (∃ O : Set D₁.N, IsOpen O ∧ B' = O ∩ Subtype.val ⁻¹' D₁.φ.model.C) ∧
        D₁.π (D₁.φ y) ∈ B' ∧ B' ⊆ D₁.V ∧
        (∀ v ∈ B', D₁.δ v ∈ range (D₁.φ.model.E.toBase m)) ∧
        ContDiffOn ℝ k (levelMap (E := ScBanach.const D₁.N) (F := D₁.φ.model.E) D₁.δ m) B' := by
    intro y hy n' D''
    obtain ⟨hv₀, hyΓ⟩ := D₁.exists_eq_Γ (show y ∈ M ∩ D₁.φ.source from hy)
    have hres := recentre_contDiffOn_levels (P := P) (S := M) D₁.isChart D''.isChart D₁.smooth
      D₁.isClosed_Y D₁.goodComplement.isCompl D₁.goodPosition D₁.V_relOpen D₁.δ_mem_Y hδC1
      D₁.φ.isOpen_source subset_rfl D₁.image_eq D''.smooth D''.isClosed_Y D''.goodComplement.isCompl
      D''.goodPosition D''.V_relOpen D''.zero_mem_V D''.δ_mem_Y D''.continuousOn D''.δ_zero
      D''.fderivWithin_V_zero D''.exists_lift D''.φ.isOpen_source subset_rfl D''.image_eq
      hy.2 D''.mem_source D''.φ_zero hv₀ hyΓ
    refine ⟨?_, hres.2⟩
    rw [← D₁.finrank_eq, ← D''.finrank_eq]
    exact hres.1
  -- sc-smoothness of `δ` on `V'`
  have hsc : IsScSmooth (E := ScBanach.const D₁.N) (F := D₁.φ.model.E) D₁.V D₁.δ := by
    have hdom := D₁.V_isRelOpenInQuadrant.isScDomain
    refine IsScSmooth.of_contDiffOn_levels hdom (fun m v hv => ?_) fun m => ?_
    · rw [ScBanach.lvlSet_const] at hv
      rw [ScBanach.const_toBase]
      have hy := D₁.symm_Γ_mem hv
      obtain ⟨n', ⟨D''⟩⟩ := hM _ ⟨hy.1, hsU hy.2⟩
      obtain ⟨-, hB⟩ := key _ hy n' D''
      obtain ⟨B', -, hvB', -, hmem, -⟩ := hB m 0
      rw [D₁.φ.apply_symm_apply (D₁.Γ_mem_O hv), D₁.π_Γ] at hvB'
      exact hmem v hvB'
    · rw [ScBanach.lvlSet_const, contDiffOn_infty]
      intro k
      refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
      have hy := D₁.symm_Γ_mem hv
      obtain ⟨n', ⟨D''⟩⟩ := hM _ ⟨hy.1, hsU hy.2⟩
      obtain ⟨-, hB⟩ := key _ hy n' D''
      obtain ⟨B', ⟨OB, hOB, hB'eq⟩, hvB', -, -, hC⟩ := hB m k
      rw [D₁.φ.apply_symm_apply (D₁.Γ_mem_O hv), D₁.π_Γ] at hvB'
      refine ⟨OB, hOB, (hB'eq ▸ hvB' : v ∈ OB ∩ _).1, hC.mono fun w hw => ?_⟩
      rw [hB'eq]
      exact ⟨hw.2, D₁.V_subset hw.1⟩
  refine ⟨D₁, D.shrink_isRegular M hs hso hxs hV'rel h0V' hV'V himage hsc hπ, hsU, ?_⟩
  intro y hy n' D''
  exact (key y hy n' D'').1.symm

end MPolyfold.TangentGermChart

end Polyfold
