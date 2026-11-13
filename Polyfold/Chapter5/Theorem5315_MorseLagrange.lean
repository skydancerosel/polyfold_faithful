import Polyfold.Chapter5.Theorem5315_ParametricMorse

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3, the proof of
**Theorem 5.3.15** (pp. 224–228; 2017: Theorem 5.8; preprint: Theorem 5.22), the classical
calculus behind (5.12)–(5.14).  Gap G.48.

# Critical points on level sets: Lagrange multipliers

## The text, paraphrased

(Proof of Theorem 5.3.15) The functions `t|S_λ` on the solution sets `S_λ` of `f + Σ λᵢ sᵢ` are
compared through a trivialization `Φ_λ : S → S_λ`; the map `(λ, y) ↦ d(t ∘ Φ_λ)(y)` is shown to be
transversal to the zero section, and a critical point of `t|S_λ` is of Morse type when the
Hessian of `t ∘ Φ_λ` is non-degenerate.

## What is formalized

The sets `S_λ` are, in a chart of a finite-dimensional manifold `M`, level sets `{h_λ = 0}` of a
map `h_λ : V → F` (`V`, `F` finite-dimensional).  Critical points of a function `T` on a level
set are handled with Lagrange multipliers instead of a trivialization:

* `lagrangian T h (v, c) = T(v) − c(h(v))` on `V × F*`, its derivative
  (`fderiv_lagrangian_apply`), its critical points (`fderiv_lagrangian_eq_zero_iff`: `h(v) = 0`
  and `dT(v) = c ∘ dh(v)`), and `IsLagrangeNondegenerate T h v c`: the Hessian of the Lagrangian
  at `(v, c)` is injective.
* `fderiv_fderiv_comp_apply`: the second-order chain rule.
* `injective_hessian_comp_of_lagrange` (**the bordered Hessian**): if `γ` parametrizes the level
  set `{h = 0}` near `γ(u)`, `dT = c ∘ dh` at `γ(u)` and the Lagrangian is non-degenerate at
  `(γ(u), c)`, then the Hessian of `T ∘ γ` at `u` is injective: `u` is a Morse-type critical
  point of `T` restricted to the level set, read in the parametrization `γ`.
* `exists_levelSet_param` (**the classical implicit function theorem for a level set**): near a
  point `v` with `h(v) = 0` and `dh(v)` onto, `{h = 0}` is the image of a `C^∞` map `γ` defined on
  an open subset of `ker dh(v)`, with an affine left inverse, and `im dγ(u) = ker dh(γ(u))`.

## What the text leaves implicit, and the choices made

* The trivialization `Φ_λ` of the text is replaced by the multiplier `c`; no second derivative of
  the trivialization is needed.
-/

open Set Function Module Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### The second-order chain rule -/

section SecondOrder

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **The second-order chain rule**:
`D²(L ∘ Ψ)(z)(x, y) = D²L(Ψ z)(DΨ x, DΨ y) + DL(Ψ z)(D²Ψ(z)(x, y))`. -/
theorem fderiv_fderiv_comp_apply {L : F → G} {Ψ : E → F} {z : E}
    (hL : ContDiffAt ℝ 2 L (Ψ z)) (hΨ : ContDiffAt ℝ 2 Ψ z) (x y : E) :
    fderiv ℝ (fderiv ℝ (L ∘ Ψ)) z x y =
      fderiv ℝ (fderiv ℝ L) (Ψ z) (fderiv ℝ Ψ z x) (fderiv ℝ Ψ z y) +
        fderiv ℝ L (Ψ z) (fderiv ℝ (fderiv ℝ Ψ) z x y) := by
  have hLev : ∀ᶠ z' in 𝓝 z, DifferentiableAt ℝ L (Ψ z') :=
    hΨ.continuousAt.eventually ((hL.eventually (by norm_num)).mono fun w hw =>
      hw.differentiableAt (by norm_num))
  have hΨev : ∀ᶠ z' in 𝓝 z, DifferentiableAt ℝ Ψ z' :=
    (hΨ.eventually (by norm_num)).mono fun w hw => hw.differentiableAt (by norm_num)
  have heq : fderiv ℝ (L ∘ Ψ) =ᶠ[𝓝 z] fun z' => (fderiv ℝ L (Ψ z')).comp (fderiv ℝ Ψ z') := by
    filter_upwards [hLev, hΨev] with z' h1 h2
    exact fderiv_comp z' h1 h2
  have hdL : HasFDerivAt (fderiv ℝ L) (fderiv ℝ (fderiv ℝ L) (Ψ z)) (Ψ z) :=
    ((hL.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hdΨ : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) z) z :=
    ((hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hΨ1 : HasFDerivAt Ψ (fderiv ℝ Ψ z) z := (hΨ.differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasFDerivAt (fun z' => fderiv ℝ L (Ψ z'))
      ((fderiv ℝ (fderiv ℝ L) (Ψ z)).comp (fderiv ℝ Ψ z)) z := hdL.comp z hΨ1
  rw [heq.fderiv_eq, (hc.clm_comp hdΨ).fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _

end SecondOrder

/-! ### Two facts of linear algebra -/

section LinearAlgebra

variable {V Fc : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Fc]
  [NormedSpace ℝ Fc] [FiniteDimensional ℝ Fc]

/-- A functional vanishing on `ker A` factors through `A`. -/
lemma exists_clm_comp_eq_of_ker_le (A : V →L[ℝ] Fc) (β : V →L[ℝ] ℝ)
    (h : ∀ κ, A κ = 0 → β κ = 0) : ∃ c : Fc →L[ℝ] ℝ, β = c.comp A := by
  have hmem : (β : V →ₗ[ℝ] ℝ) ∈ (LinearMap.ker (A : V →ₗ[ℝ] Fc)).dualAnnihilator :=
    (Submodule.mem_dualAnnihilator _).2 fun κ hκ => h κ hκ
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨LinearMap.toContinuousLinearMap c, ContinuousLinearMap.ext fun κ => ?_⟩
  have := congrArg (fun L : V →ₗ[ℝ] ℝ => L κ) hc
  exact this.symm

/-- A finite-dimensional space is reflexive: every functional on `F*` is an evaluation. -/
lemma exists_eq_apply_of_dual_dual (β : (Fc →L[ℝ] ℝ) →L[ℝ] ℝ) :
    ∃ r : Fc, ∀ ℓ : Fc →L[ℝ] ℝ, β ℓ = ℓ r := by
  set ev : Fc →ₗ[ℝ] ((Fc →L[ℝ] ℝ) →L[ℝ] ℝ) :=
    ((ContinuousLinearMap.apply ℝ ℝ : Fc →L[ℝ] (Fc →L[ℝ] ℝ) →L[ℝ] ℝ) :
      Fc →ₗ[ℝ] ((Fc →L[ℝ] ℝ) →L[ℝ] ℝ)) with hev
  have hinj : Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ => ?_
    have := congrArg (fun L : (Fc →L[ℝ] ℝ) →L[ℝ] ℝ => L ℓ) hr
    exact this
  have hdim : finrank ℝ Fc = finrank ℝ ((Fc →L[ℝ] ℝ) →L[ℝ] ℝ) := by
    rw [finrank_clm_real, finrank_clm_real]
  obtain ⟨r, hr⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj β
  exact ⟨r, fun ℓ => by rw [← hr]; rfl⟩

end LinearAlgebra

/-! ### The Lagrangian -/

section Lagrangian

variable {V Fc : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Fc]
  [NormedSpace ℝ Fc]

/-- **The Lagrangian** `(v, c) ↦ T(v) − c(h(v))` of the function `T` and the constraint `h = 0`,
on `V × F*`. -/
def lagrangian (T : V → ℝ) (h : V → Fc) (z : V × (Fc →L[ℝ] ℝ)) : ℝ := T z.1 - z.2 (h z.1)

variable {T : V → ℝ} {h : V → Fc} {v : V}

lemma hasFDerivAt_lagrangian {T' : V →L[ℝ] ℝ} {h' : V →L[ℝ] Fc} (hT : HasFDerivAt T T' v)
    (hh : HasFDerivAt h h' v) (c : Fc →L[ℝ] ℝ) :
    HasFDerivAt (lagrangian T h)
      (T'.comp (ContinuousLinearMap.fst ℝ V (Fc →L[ℝ] ℝ)) -
        (c.comp (h'.comp (ContinuousLinearMap.fst ℝ V (Fc →L[ℝ] ℝ))) +
          (ContinuousLinearMap.snd ℝ V (Fc →L[ℝ] ℝ)).flip (h v))) (v, c) := by
  have h1 : HasFDerivAt (fun z : V × (Fc →L[ℝ] ℝ) => T z.1)
      (T'.comp (ContinuousLinearMap.fst ℝ V (Fc →L[ℝ] ℝ))) (v, c) :=
    hT.comp (v, c) hasFDerivAt_fst
  have h2 : HasFDerivAt (fun z : V × (Fc →L[ℝ] ℝ) => h z.1)
      (h'.comp (ContinuousLinearMap.fst ℝ V (Fc →L[ℝ] ℝ))) (v, c) :=
    hh.comp (v, c) hasFDerivAt_fst
  have h3 : HasFDerivAt (fun z : V × (Fc →L[ℝ] ℝ) => z.2)
      (ContinuousLinearMap.snd ℝ V (Fc →L[ℝ] ℝ)) (v, c) := hasFDerivAt_snd
  exact h1.sub (h3.clm_apply h2)

/-- **The derivative of the Lagrangian**:
`DL(v, c)(δv, δc) = dT(v)δv − c(dh(v)δv) − δc(h(v))`. -/
theorem fderiv_lagrangian_apply (hT : DifferentiableAt ℝ T v) (hh : DifferentiableAt ℝ h v)
    (c : Fc →L[ℝ] ℝ) (w : V × (Fc →L[ℝ] ℝ)) :
    fderiv ℝ (lagrangian T h) (v, c) w =
      fderiv ℝ T v w.1 - c (fderiv ℝ h v w.1) - w.2 (h v) := by
  rw [(hasFDerivAt_lagrangian hT.hasFDerivAt hh.hasFDerivAt c).fderiv]
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_snd']
  ring

/-- **Critical points of the Lagrangian**: `h(v) = 0` and `dT(v) = c ∘ dh(v)` (`c` is a Lagrange
multiplier: `v` is a critical point of `T` on the level set). -/
theorem fderiv_lagrangian_eq_zero_iff [FiniteDimensional ℝ Fc] (hT : DifferentiableAt ℝ T v)
    (hh : DifferentiableAt ℝ h v) (c : Fc →L[ℝ] ℝ) :
    fderiv ℝ (lagrangian T h) (v, c) = 0 ↔
      h v = 0 ∧ fderiv ℝ T v = c.comp (fderiv ℝ h v) := by
  constructor
  · intro h0
    have key : ∀ w : V × (Fc →L[ℝ] ℝ),
        fderiv ℝ T v w.1 - c (fderiv ℝ h v w.1) - w.2 (h v) = 0 := fun w => by
      rw [← fderiv_lagrangian_apply hT hh c w, h0]; rfl
    refine ⟨SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ => ?_,
      ContinuousLinearMap.ext fun δ => ?_⟩
    · have := key (0, ℓ)
      simpa using this
    · have := key (δ, 0)
      simp only [zero_apply, sub_zero] at this
      rw [ContinuousLinearMap.comp_apply]
      linarith
  · rintro ⟨h0, hc⟩
    refine ContinuousLinearMap.ext fun w => ?_
    rw [fderiv_lagrangian_apply hT hh c w, h0, hc]
    simp

lemma contDiffAt_lagrangian {n : WithTop ℕ∞} (hT : ContDiffAt ℝ n T v) (hh : ContDiffAt ℝ n h v)
    (c : Fc →L[ℝ] ℝ) : ContDiffAt ℝ n (lagrangian T h) (v, c) := by
  have h1 : ContDiffAt ℝ n (fun z : V × (Fc →L[ℝ] ℝ) => T z.1) (v, c) :=
    hT.comp (v, c) contDiffAt_fst
  have h2 : ContDiffAt ℝ n (fun z : V × (Fc →L[ℝ] ℝ) => h z.1) (v, c) :=
    hh.comp (v, c) contDiffAt_fst
  have h3 : ContDiffAt ℝ n (fun z : V × (Fc →L[ℝ] ℝ) => z.2) (v, c) := contDiffAt_snd
  exact h1.sub (h3.clm_apply h2)

/-- **A non-degenerate critical point of the Lagrangian**: the Hessian of `(v, c) ↦ T(v) −
c(h(v))` at `(v, c)` is injective. -/
def IsLagrangeNondegenerate (T : V → ℝ) (h : V → Fc) (v : V) (c : Fc →L[ℝ] ℝ) : Prop :=
  Injective (fderiv ℝ (fderiv ℝ (lagrangian T h)) (v, c))

/-- **The Hessian of the Lagrangian in the direction of the multiplier**:
`D²L(v, c)((0, δc), (δv', δc')) = −δc(dh(v)δv')`. -/
theorem hessian_lagrangian_snd_apply (hT : ContDiffAt ℝ 2 T v) (hh : ContDiffAt ℝ 2 h v)
    (c δc : Fc →L[ℝ] ℝ) (w : V × (Fc →L[ℝ] ℝ)) :
    fderiv ℝ (fderiv ℝ (lagrangian T h)) (v, c) (0, δc) w = -δc (fderiv ℝ h v w.1) := by
  have hT1 : DifferentiableAt ℝ T v := hT.differentiableAt (by norm_num)
  have hh1 : DifferentiableAt ℝ h v := hh.differentiableAt (by norm_num)
  have hG : HasFDerivAt (fderiv ℝ (lagrangian T h))
      (fderiv ℝ (fderiv ℝ (lagrangian T h)) (v, c)) (v, c) :=
    (((contDiffAt_lagrangian hT hh c).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hpath : HasDerivAt (fun s : ℝ => ((v, c + s • δc) : V × (Fc →L[ℝ] ℝ))) (0, δc) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => c + s • δc) δc 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δc).const_add c
    exact (hasDerivAt_const 0 v).prodMk h1
  have hp0 : ((v, c + (0 : ℝ) • δc) : V × (Fc →L[ℝ] ℝ)) = (v, c) := by simp
  have hcomp : HasDerivAt (fun s : ℝ => fderiv ℝ (lagrangian T h) (v, c + s • δc) w)
      (fderiv ℝ (fderiv ℝ (lagrangian T h)) (v, c) (0, δc) w) 0 := by
    have hG' : HasFDerivAt (fderiv ℝ (lagrangian T h))
        (fderiv ℝ (fderiv ℝ (lagrangian T h)) (v, c)) (v, c + (0 : ℝ) • δc) := by
      rw [hp0]; exact hG
    have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ (lagrangian T h) (v, c + s • δc))
        (fderiv ℝ (fderiv ℝ (lagrangian T h)) (v, c) (0, δc)) 0 :=
      HasFDerivAt.comp_hasDerivAt (E := (V × (Fc →L[ℝ] ℝ)) →L[ℝ] ℝ) (F := V × (Fc →L[ℝ] ℝ))
        (l := fderiv ℝ (lagrangian T h)) (0 : ℝ) hG' hpath
    exact HasFDerivAt.comp_hasDerivAt (E := ℝ) (F := (V × (Fc →L[ℝ] ℝ)) →L[ℝ] ℝ)
      (l := fun A : (V × (Fc →L[ℝ] ℝ)) →L[ℝ] ℝ => A w) (0 : ℝ)
      (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt h1
  have hline : (fun s : ℝ => fderiv ℝ (lagrangian T h) (v, c + s • δc) w) = fun s =>
      fderiv ℝ (lagrangian T h) (v, c) w + s * (-δc (fderiv ℝ h v w.1)) := by
    funext s
    rw [fderiv_lagrangian_apply hT1 hh1, fderiv_lagrangian_apply hT1 hh1]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hcurve : HasDerivAt (fun s : ℝ => fderiv ℝ (lagrangian T h) (v, c + s • δc) w)
      (-δc (fderiv ℝ h v w.1)) 0 := by
    rw [hline]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (-δc (fderiv ℝ h v w.1))).const_add
      (fderiv ℝ (lagrangian T h) (v, c) w)
  exact hcomp.unique hcurve

end Lagrangian

/-! ### The bordered Hessian -/

section Bordered

variable {U V Fc : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [NormedAddCommGroup Fc] [NormedSpace ℝ Fc] [FiniteDimensional ℝ Fc]

/-- **The bordered Hessian** (the classical fact behind "`t ∘ Φ_λ` is a Morse function", proof
of 2021 Theorem 5.3.15, p. 224): let `γ` parametrize the level set `{h = 0}` near `γ(u)`
(`h ∘ γ = 0` near `u`, `dγ(u)` injective with image `ker dh(γ(u))`), let `c` be a Lagrange
multiplier at `γ(u)` (`dT = c ∘ dh`) and let the Lagrangian `T − c(h)` be non-degenerate at
`(γ(u), c)`.  Then the Hessian of `T ∘ γ` at `u` is injective. -/
theorem injective_hessian_comp_of_lagrange {T : V → ℝ} {h : V → Fc} {γ : U → V} {u : U}
    (hT : ContDiffAt ℝ 2 T (γ u)) (hh : ContDiffAt ℝ 2 h (γ u)) (hγ : ContDiffAt ℝ 2 γ u)
    (hzero : ∀ᶠ u' in 𝓝 u, h (γ u') = 0) (hinj : Injective (fderiv ℝ γ u))
    (hrange : ∀ w, fderiv ℝ h (γ u) w = 0 → ∃ a, fderiv ℝ γ u a = w) {c : Fc →L[ℝ] ℝ}
    (hc : fderiv ℝ T (γ u) = c.comp (fderiv ℝ h (γ u)))
    (hnd : IsLagrangeNondegenerate T h (γ u) c) :
    Injective (fderiv ℝ (fderiv ℝ (T ∘ γ)) u) := by
  have hT1 : DifferentiableAt ℝ T (γ u) := hT.differentiableAt (by norm_num)
  have hh1 : DifferentiableAt ℝ h (γ u) := hh.differentiableAt (by norm_num)
  have hγ1 : HasFDerivAt γ (fderiv ℝ γ u) u := (hγ.differentiableAt (by norm_num)).hasFDerivAt
  set Lg := lagrangian T h with hLg
  set Ψ : U × (Fc →L[ℝ] ℝ) → V × (Fc →L[ℝ] ℝ) := fun p => (γ p.1, p.2) with hΨ
  have hΨc : ContDiffAt ℝ 2 Ψ (u, c) :=
    (hγ.comp (u, c) contDiffAt_fst).prodMk contDiffAt_snd
  have hΨd : ∀ x : U × (Fc →L[ℝ] ℝ), fderiv ℝ Ψ (u, c) x = (fderiv ℝ γ u x.1, x.2) := by
    intro x
    have h1 : HasFDerivAt Ψ (((fderiv ℝ γ u).comp (ContinuousLinearMap.fst ℝ U (Fc →L[ℝ] ℝ))).prod
        (ContinuousLinearMap.snd ℝ U (Fc →L[ℝ] ℝ))) (u, c) :=
      (hγ1.comp (u, c) hasFDerivAt_fst).prodMk hasFDerivAt_snd
    rw [h1.fderiv]; rfl
  have hcrit : fderiv ℝ Lg (Ψ (u, c)) = 0 :=
    (fderiv_lagrangian_eq_zero_iff hT1 hh1 c).2 ⟨hzero.self_of_nhds, hc⟩
  -- `L ∘ Ψ = (T ∘ γ) ∘ fst` near `(u, c)`
  have heq : Lg ∘ Ψ =ᶠ[𝓝 (u, c)] (T ∘ γ) ∘ Prod.fst := by
    have hfst : Tendsto (Prod.fst : U × (Fc →L[ℝ] ℝ) → U) (𝓝 (u, c)) (𝓝 u) := continuousAt_fst
    have h1 : ∀ᶠ p : U × (Fc →L[ℝ] ℝ) in 𝓝 (u, c), h (γ p.1) = 0 := hfst.eventually hzero
    filter_upwards [h1] with p hp
    simp only [Function.comp_apply, hLg, hΨ, lagrangian, hp, map_zero, sub_zero]
  have hTγ : ContDiffAt ℝ 2 (T ∘ γ) u := hT.comp u hγ
  have hfst : ContDiffAt ℝ 2 (Prod.fst : U × (Fc →L[ℝ] ℝ) → U) (u, c) := contDiffAt_fst
  have key : ∀ x y : U × (Fc →L[ℝ] ℝ),
      fderiv ℝ (fderiv ℝ Lg) (γ u, c) (fderiv ℝ γ u x.1, x.2) (fderiv ℝ γ u y.1, y.2) =
        fderiv ℝ (fderiv ℝ (T ∘ γ)) u x.1 y.1 := by
    intro x y
    have h1 := fderiv_fderiv_comp_apply (L := Lg) (Ψ := Ψ) (z := (u, c))
      (contDiffAt_lagrangian hT hh c) hΨc x y
    have h2 := fderiv_fderiv_comp_apply (L := T ∘ γ) (Ψ := Prod.fst) (z := (u, c)) hTγ hfst x y
    rw [hcrit, hΨd, hΨd] at h1
    have h3 : fderiv ℝ (fderiv ℝ (Prod.fst : U × (Fc →L[ℝ] ℝ) → U)) (u, c) = 0 := by
      have : fderiv ℝ (Prod.fst : U × (Fc →L[ℝ] ℝ) → U) =
          fun _ => ContinuousLinearMap.fst ℝ U (Fc →L[ℝ] ℝ) := by
        funext p; exact (hasFDerivAt_fst (p := p)).fderiv
      rw [this]; exact fderiv_const_apply _
    have h4 : fderiv ℝ (Prod.fst : U × (Fc →L[ℝ] ℝ) → U) (u, c) =
        ContinuousLinearMap.fst ℝ U (Fc →L[ℝ] ℝ) := (hasFDerivAt_fst (p := (u, c))).fderiv
    rw [h3, h4] at h2
    have h5 : fderiv ℝ (fderiv ℝ (Lg ∘ Ψ)) (u, c) =
        fderiv ℝ (fderiv ℝ ((T ∘ γ) ∘ Prod.fst)) (u, c) := heq.fderiv.fderiv_eq
    rw [h5, h2] at h1
    simpa using h1.symm
  rw [injective_iff_map_eq_zero]
  intro a ha
  -- the functional `β = D²L(γ u, c)(dγ a, 0)` vanishes on `ker dh × F*`
  set β := fderiv ℝ (fderiv ℝ Lg) (γ u, c) (fderiv ℝ γ u a, 0) with hβ
  have hβ0 : ∀ (w : V) (δ : Fc →L[ℝ] ℝ), fderiv ℝ h (γ u) w = 0 → β (w, δ) = 0 := by
    intro w δ hw
    obtain ⟨b, hb⟩ := hrange w hw
    have := key (a, 0) (b, δ)
    rw [hb] at this
    rw [hβ, this, ha]; rfl
  obtain ⟨δc, hδc⟩ := exists_clm_comp_eq_of_ker_le (fderiv ℝ h (γ u))
    (β.comp (ContinuousLinearMap.inl ℝ V (Fc →L[ℝ] ℝ))) fun κ hκ => hβ0 κ 0 hκ
  have hsum : fderiv ℝ (fderiv ℝ Lg) (γ u, c) (fderiv ℝ γ u a, δc) = 0 := by
    refine ContinuousLinearMap.ext fun w => ?_
    have h1 : ((fderiv ℝ γ u a, δc) : V × (Fc →L[ℝ] ℝ)) = (fderiv ℝ γ u a, 0) + (0, δc) := by
      simp
    have h2 : w = (w.1, 0) + (0, w.2) := by simp
    have h3 : β (w.1, 0) = δc (fderiv ℝ h (γ u) w.1) :=
      congrArg (fun L : V →L[ℝ] ℝ => L w.1) hδc
    have h4 : β (0, w.2) = 0 := hβ0 0 w.2 (map_zero _)
    rw [h1, map_add, add_apply, hessian_lagrangian_snd_apply hT hh, ← hβ]
    conv_lhs => rw [h2, map_add, h3, h4]
    simp
  have h0 := hnd (hsum.trans (map_zero _).symm)
  exact hinj ((congrArg Prod.fst h0).trans (map_zero _).symm)

end Bordered

/-! ### The implicit function theorem for a level set -/

section LevelSet

variable {V Fc : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Fc] [NormedSpace ℝ Fc] [FiniteDimensional ℝ Fc]

omit [FiniteDimensional ℝ Fc] in
/-- **A level set near a regular point** (the classical implicit function theorem): let `h` be
`C^∞` on the open `Ω ⊆ V`, `h(v) = 0` and `dh(v)` onto.  Then near `v` the level set `{h = 0}` is
the image of a `C^∞` map `γ` defined on an open neighbourhood `Ωγ` of `0` in `K = ker dh(v)`
(a submodule `K` with `w ∈ K ↔ dh(v)w = 0`),
`γ(0) = v`, with the affine left inverse `x ↦ π(x − v)`, and `im dγ(u) = ker dh(γ(u))`. -/
theorem exists_levelSet_param {h : V → Fc} {Ω : Set V} (hΩ : IsOpen Ω)
    (hh : ContDiffOn ℝ ∞ h Ω) {v : V} (hv : v ∈ Ω) (h0 : h v = 0)
    (hsurj : Surjective (fderiv ℝ h v)) :
    ∃ (K : Submodule ℝ V) (Ωγ : Set K) (γ : K → V) (π : V →L[ℝ] K) (Ω' : Set V),
      (∀ w, w ∈ K ↔ fderiv ℝ h v w = 0) ∧
      IsOpen Ωγ ∧ IsOpen Ω' ∧ Ω' ⊆ Ω ∧ v ∈ Ω' ∧ (0 : K) ∈ Ωγ ∧
        γ 0 = v ∧ ContDiffOn ℝ ∞ γ Ωγ ∧ γ '' Ωγ = {x | x ∈ Ω' ∧ h x = 0} ∧
        (∀ u ∈ Ωγ, π (γ u - v) = u) ∧
        ∀ u ∈ Ωγ, ∀ w, fderiv ℝ h (γ u) w = 0 → ∃ a, fderiv ℝ γ u a = w := by
  obtain ⟨K, hKmem⟩ : ∃ K : Submodule ℝ V, ∀ w, w ∈ K ↔ fderiv ℝ h v w = 0 :=
    ⟨LinearMap.ker (fderiv ℝ h v : V →ₗ[ℝ] Fc), fun w => LinearMap.mem_ker⟩
  obtain ⟨π, hπ⟩ := Submodule.ClosedComplemented.of_finiteDimensional K
  set Φ : V → Fc × K := fun x => (h x, π (x - v)) with hΦ
  have hhat : ∀ x ∈ Ω, ContDiffAt ℝ ∞ h x := fun x hx => hh.contDiffAt (hΩ.mem_nhds hx)
  have hΦc : ∀ x ∈ Ω, ContDiffAt ℝ ∞ Φ x := fun x hx =>
    (hhat x hx).prodMk (π.contDiff.contDiffAt.comp x (contDiffAt_id.sub contDiffAt_const))
  have hΦd : ∀ x ∈ Ω, HasFDerivAt Φ ((fderiv ℝ h x).prod π) x := fun x hx => by
    have h1 : HasFDerivAt (fun y : V => π (y - v)) π x :=
      π.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const v)
    exact ((hhat x hx).differentiableAt (by simp)).hasFDerivAt.prodMk h1
  -- `(dh(v), π)` is an isomorphism
  have hbij : Bijective ((fderiv ℝ h v).prod π) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro w hw
      have h1 : fderiv ℝ h v w = 0 := congrArg Prod.fst hw
      have h2 : π w = 0 := congrArg Prod.snd hw
      have h3 : π w = ⟨w, (hKmem w).2 h1⟩ := hπ ⟨w, (hKmem w).2 h1⟩
      rw [h2] at h3
      exact (congrArg Subtype.val h3).symm
    · rintro ⟨y, k⟩
      obtain ⟨w₀, hw₀⟩ := hsurj y
      refine ⟨w₀ - (π w₀ : V) + (k : V), ?_⟩
      have hk1 : fderiv ℝ h v (π w₀ : V) = 0 := (hKmem _).1 (π w₀).2
      have hk2 : fderiv ℝ h v (k : V) = 0 := (hKmem _).1 k.2
      have hk3 : π (π w₀ : V) = π w₀ := hπ (π w₀)
      have hk4 : π (k : V) = k := hπ k
      change (fderiv ℝ h v (w₀ - (π w₀ : V) + (k : V)), π (w₀ - (π w₀ : V) + (k : V))) = (y, k)
      rw [map_add, map_sub, map_add, map_sub, hk1, hk2, hk3, hk4, hw₀]
      simp
  set e : V ≃L[ℝ] Fc × K :=
    (LinearEquiv.ofBijective ((fderiv ℝ h v).prod π : V →ₗ[ℝ] Fc × K)
      hbij).toContinuousLinearEquiv with he
  have hecoe : (e : V →L[ℝ] Fc × K) = (fderiv ℝ h v).prod π :=
    ContinuousLinearMap.ext fun _ => rfl
  have hstrict : HasStrictFDerivAt Φ (e : V →L[ℝ] Fc × K) v :=
    (hΦc v hv).hasStrictFDerivAt' (hecoe ▸ hΦd v hv) (by simp)
  set φ := hstrict.toOpenPartialHomeomorph Φ with hφ
  have hφcoe : (φ : V → Fc × K) = Φ := hstrict.toOpenPartialHomeomorph_coe
  -- `(dh(x), π)` is an isomorphism for `x` near `v`
  have hcont : ContinuousAt (fun x => (fderiv ℝ h x).prod π) v := by
    have hfun : (fun x => (fderiv ℝ h x).prod π) = fun x =>
        (ContinuousLinearMap.inl ℝ Fc K).comp (fderiv ℝ h x) +
          (ContinuousLinearMap.inr ℝ Fc K).comp π := by
      funext x; ext w <;> simp
    rw [hfun]
    exact (continuousAt_const.clm_comp ((hhat v hv).continuousAt_fderiv (by simp))).add
      continuousAt_const
  have hev : ∀ᶠ x in 𝓝 v, (fderiv ℝ h x).prod π ∈
      range ((↑) : (V ≃L[ℝ] Fc × K) → V →L[ℝ] Fc × K) :=
    hcont.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds ⟨e, hecoe⟩)
  obtain ⟨N₀, hN₀, hN₀o, hvN₀⟩ := eventually_nhds_iff.1 (hev.and (hΩ.eventually_mem hv))
  set Ω' := φ.source ∩ N₀ with hΩ'
  have hΩ'o : IsOpen Ω' := φ.open_source.inter hN₀o
  have hΩ'Ω : Ω' ⊆ Ω := fun x hx => (hN₀ x hx.2).2
  have hvΩ' : v ∈ Ω' := ⟨hstrict.mem_toOpenPartialHomeomorph_source, hvN₀⟩
  set Ωγ : Set K := (fun u : K => ((0 : Fc), u)) ⁻¹' (φ.target ∩ φ.symm ⁻¹' Ω') with hΩγ
  set γ : K → V := fun u => φ.symm (0, u) with hγ
  have hφv : φ v = (0, 0) := by rw [hφcoe, hΦ]; simp [h0]
  have hγ0 : γ 0 = v := by rw [hγ]; simp only; rw [← hφv]; exact φ.left_inv hvΩ'.1
  have hφγ : ∀ u ∈ Ωγ, φ (γ u) = (0, u) := fun u hu => φ.right_inv hu.1
  -- the derivative of `γ`
  have hγd : ∀ u ∈ Ωγ, ∃ e' : V ≃L[ℝ] Fc × K,
      (e' : V →L[ℝ] Fc × K) = (fderiv ℝ h (γ u)).prod π ∧
      HasFDerivAt γ ((e'.symm : Fc × K →L[ℝ] V).comp (ContinuousLinearMap.inr ℝ Fc K)) u ∧
      ContDiffAt ℝ ∞ γ u := by
    intro u hu
    obtain ⟨⟨e', he'⟩, hxΩ⟩ := hN₀ (γ u) hu.2.2
    have hd1 : HasFDerivAt φ (e' : V →L[ℝ] Fc × K) (φ.symm (0, u)) := by
      rw [hφcoe, he']; exact hΦd _ hxΩ
    have hd2 : HasFDerivAt φ.symm (e'.symm : Fc × K →L[ℝ] V) (0, u) :=
      φ.hasFDerivAt_symm hu.1 hd1
    have hc1 : ContDiffAt ℝ ∞ φ (φ.symm (0, u)) := by rw [hφcoe]; exact hΦc _ hxΩ
    have hc2 : ContDiffAt ℝ ∞ φ.symm (0, u) := φ.contDiffAt_symm hu.1 hd1 hc1
    refine ⟨e', he', hd2.comp u (hasFDerivAt_prodMk_right (0 : Fc) u), ?_⟩
    exact hc2.comp u (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨K, Ωγ, γ, π, Ω', hKmem, ?_, hΩ'o, hΩ'Ω, hvΩ', ?_, hγ0, ?_, ?_, ?_, ?_⟩
  · exact (φ.isOpen_inter_preimage_symm hΩ'o).preimage (Continuous.prodMk_right (0 : Fc))
  · change ((0 : Fc), (0 : K)) ∈ φ.target ∩ φ.symm ⁻¹' Ω'
    rw [← hφv]
    exact ⟨φ.map_source hvΩ'.1, by rw [mem_preimage, φ.left_inv hvΩ'.1]; exact hvΩ'⟩
  · exact fun u hu => (hγd u hu).choose_spec.2.2.contDiffWithinAt
  · ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h1 := hφγ u hu
      rw [hφcoe] at h1
      exact ⟨hu.2, congrArg Prod.fst h1⟩
    · rintro ⟨hx, hx0⟩
      have h1 : φ x = (0, π (x - v)) := by rw [hφcoe, hΦ]; simp only [hx0]
      have h2 : φ.symm (0, π (x - v)) = x := by rw [← h1]; exact φ.left_inv hx.1
      refine ⟨π (x - v), ⟨?_, ?_⟩, h2⟩
      · change ((0 : Fc), π (x - v)) ∈ φ.target
        rw [← h1]; exact φ.map_source hx.1
      · change φ.symm ((0 : Fc), π (x - v)) ∈ Ω'
        rw [h2]; exact hx
  · intro u hu
    have h1 := hφγ u hu
    rw [hφcoe] at h1
    exact congrArg Prod.snd h1
  · intro u hu w hw
    obtain ⟨e', he', hd, -⟩ := hγd u hu
    refine ⟨π w, ?_⟩
    rw [hd.fderiv]
    have h1 : e' w = (0, π w) := by
      have : (e' : V →L[ℝ] Fc × K) w = ((fderiv ℝ h (γ u)).prod π) w := by rw [he']
      rw [ContinuousLinearMap.prod_apply, hw] at this
      exact this
    change e'.symm ((0 : Fc), π w) = w
    rw [← h1, e'.symm_apply_apply]

end LevelSet

end Polyfold
