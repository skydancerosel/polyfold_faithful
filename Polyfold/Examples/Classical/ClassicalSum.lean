import Polyfold.Examples.Classical.Setup

/-!
# The classical count of a proper equivariant map

The classical side of the comparison with Theorem 16.6.6, 2021 p. 739 (index `0`): for a finite
group `G` acting linearly on `ℝⁿ`, a fibre action `σ`, and a proper equivariant `C¹` map
`φ : ℝⁿ → ℝⁿ` with regular value `c`, the weighted count over orbit representatives
`∑_{x ∈ s} (♯G_x)⁻¹ · sign det Dφ(x) · N(x)/♯G`, `N(x) = ♯{g | φ(x) = σ g c}`, equals
`(1/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)`.  Only Mathlib is used besides `rhoL` from `Setup`.

## What is formalized (namespace `Polyfold.Examples.Classical`)

* `finite_preimage_of_regular`: the fibre of a proper `C¹` map of `ℝⁿ` over a regular value is
  finite (inverse function theorem and compactness).
* `fderiv_smul_comp`: `Dφ(g • x) ∘ g = σ g ∘ Dφ(x)`; `surjective_fderiv_smul_iff`; and
  `sign_det_fderiv_smul`: `sign det Dφ(g • x) = sign det Dφ(x)` when
  `det(g) · det(σ g) > 0` for all `g`.
* For a finite group acting on `α`, a map `F : α → β` intertwining it with an action `τ` on `β`:
  `IsOrbitReps`, `hitSet`, `hitCount`, `finite_hitSet`, `exists_isOrbitReps`, and
  **`sum_orbitReps_eq`**: `∑_{x ∈ s} (♯G_x)⁻¹ · ε(x) · N(x)/♯G = (1/♯G) · ∑_{y ∈ F⁻¹(c)} ε(y)`
  for a `G`-invariant `ε` (orbit–stabilizer and double counting).
* `classicalCount G φ c = (1/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)`,
  `exists_isOrbitReps_of_finite`, and **`sum_orbitReps_eq_classicalCount`** (with the variant
  `sum_orbitReps_eq_classicalCount_of_regular` for a proper map at a regular value).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold.Examples.Classical

/-- A surjective endomorphism of `ℝⁿ`, as a continuous linear equivalence. -/
def equivOfSurjective {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (hA : Function.Surjective A) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr (LinearMap.injective_iff_surjective.mpr hA))
    (LinearMap.range_eq_top.mpr hA)

@[simp] theorem coe_equivOfSurjective {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hA : Function.Surjective A) :
    ((equivOfSurjective A hA : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) =
      A :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

/-- At a point where the derivative of a `C¹` map of `ℝⁿ` is surjective, the map is injective on
a neighbourhood (inverse function theorem). -/
theorem eventually_eq_of_surjective_fderiv {n : ℕ} {φ : (Fin n → ℝ) → (Fin n → ℝ)}
    (hφ : ContDiff ℝ 1 φ) {x : Fin n → ℝ} (hx : Function.Surjective (fderiv ℝ φ x)) :
    ∀ᶠ y in 𝓝 x, φ y = φ x → y = x := by
  have hs : HasStrictFDerivAt φ
      ((equivOfSurjective _ hx : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
      x := by
    rw [coe_equivOfSurjective]
    exact hφ.hasStrictFDerivAt one_ne_zero
  filter_upwards [hs.eventually_left_inverse] with y hy hyx
  rw [← hy, hyx, hs.localInverse_apply_image]

/-- **The fibre of a proper `C¹` map of `ℝⁿ` over a regular value is finite.** -/
theorem finite_preimage_of_regular {n : ℕ} {φ : (Fin n → ℝ) → (Fin n → ℝ)}
    (hφ : ContDiff ℝ 1 φ) (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Function.Surjective (fderiv ℝ φ x)) : (φ ⁻¹' {c}).Finite := by
  obtain ⟨t, htc, ht⟩ := (hprop {c} isCompact_singleton).elim_nhds_subcover
    (fun x => {y | φ y = φ x → y = x}) fun x hx => eventually_eq_of_surjective_fderiv hφ (hc x hx)
  refine t.finite_toSet.subset fun y hy => ?_
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
  have hxc : φ x = c := htc x hxt
  have hy' : φ y = c := hy
  rw [hyx (hy'.trans hxc.symm)]
  exact hxt

/-! ### Equivariance of the derivative -/

section Equivariance

variable {G : Type} [Group G] {n : ℕ} [DistribMulAction G (Fin n → ℝ)]
  [SMulCommClass G ℝ (Fin n → ℝ)] {σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))}
  {φ : (Fin n → ℝ) → (Fin n → ℝ)}

omit [SMulCommClass G ℝ (Fin n → ℝ)] [DistribMulAction G (Fin n → ℝ)] in
/-- `σ g⁻¹ (σ g w) = w`. -/
theorem σ_inv_apply' (g : G) (w : Fin n → ℝ) : σ g⁻¹ (σ g w) = w := by
  change (σ g⁻¹ * σ g) w = w
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

omit [SMulCommClass G ℝ (Fin n → ℝ)] [DistribMulAction G (Fin n → ℝ)] in
/-- `σ g (σ g⁻¹ w) = w`. -/
theorem σ_apply_inv' (g : G) (w : Fin n → ℝ) : σ g (σ g⁻¹ w) = w := by
  change (σ g * σ g⁻¹) w = w
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

/-- **`Dφ(g • x) ∘ g = σ g ∘ Dφ(x)`** for an equivariant differentiable map. -/
theorem fderiv_smul_comp (hφ : Differentiable ℝ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (g : G) (x : Fin n → ℝ) :
    (fderiv ℝ φ (g • x)).comp (rhoL g) = (σ g).comp (fderiv ℝ φ x) := by
  have h1 : HasFDerivAt (φ ∘ rhoL g) ((fderiv ℝ φ (g • x)).comp (rhoL g)) x :=
    (hφ (rhoL g x)).hasFDerivAt.comp x (rhoL g).hasFDerivAt
  have h2 : HasFDerivAt (fun y => σ g (φ y)) ((σ g).comp (fderiv ℝ φ x)) x :=
    (σ g).hasFDerivAt.comp x (hφ x).hasFDerivAt
  have hfun : (φ ∘ rhoL g) = fun y => σ g (φ y) := funext fun y => heq g y
  rw [hfun] at h1
  exact h1.unique h2

/-- **Surjectivity of the derivative is invariant**: `Dφ(g • x)` is onto iff `Dφ(x)` is. -/
theorem surjective_fderiv_smul_iff (hφ : Differentiable ℝ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) (g : G) (x : Fin n → ℝ) :
    Function.Surjective (fderiv ℝ φ (g • x)) ↔ Function.Surjective (fderiv ℝ φ x) := by
  have h := fderiv_smul_comp hφ heq g x
  constructor
  · intro hs w
    obtain ⟨v, hv⟩ := hs (σ g w)
    refine ⟨g⁻¹ • v, ?_⟩
    have := congrArg (fun A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => A (g⁻¹ • v)) h
    change fderiv ℝ φ (g • x) (g • g⁻¹ • v) = σ g (fderiv ℝ φ x (g⁻¹ • v)) at this
    rw [smul_inv_smul, hv] at this
    have h' := congrArg (σ g⁻¹) this
    rw [σ_inv_apply', σ_inv_apply'] at h'
    exact h'.symm
  · intro hs w
    obtain ⟨v, hv⟩ := hs (σ g⁻¹ w)
    refine ⟨g • v, ?_⟩
    have := congrArg (fun A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => A v) h
    change fderiv ℝ φ (g • x) (g • v) = σ g (fderiv ℝ φ x v) at this
    rw [this, hv, σ_apply_inv']

/-- `det Dφ(g • x) · det(g) = det(σ g) · det Dφ(x)`. -/
theorem det_fderiv_smul_mul (hφ : Differentiable ℝ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (g : G) (x : Fin n → ℝ) :
    LinearMap.det (fderiv ℝ φ (g • x) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
        LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
        LinearMap.det (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
  rw [← LinearMap.det_comp, ← LinearMap.det_comp]
  exact congrArg (fun A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) =>
    LinearMap.det (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) (fderiv_smul_comp hφ heq g x)

/-- **The sign of `det Dφ` is invariant** when every `g` has `det(g) · det(σ g) > 0`. -/
theorem sign_det_fderiv_smul (hφ : Differentiable ℝ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (g : G) (x : Fin n → ℝ) :
    SignType.sign (LinearMap.det (fderiv ℝ φ (g • x) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) =
      SignType.sign (LinearMap.det (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) := by
  have h := det_fderiv_smul_mul hφ heq g x
  set a := LinearMap.det (fderiv ℝ φ (g • x) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  set b := LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  set s := LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  set d := LinearMap.det (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  have hbs : 0 < b * s := hdet g
  have hb : b ≠ 0 := by
    rintro hb
    rw [hb, zero_mul] at hbs
    exact lt_irrefl _ hbs
  have hk : 0 < s * b / (b * b) := div_pos (by linarith [mul_comm b s]) (mul_self_pos.mpr hb)
  have ha : a = s * b / (b * b) * d :=
    calc a = a * b * b / (b * b) := by field_simp
      _ = s * d * b / (b * b) := by rw [h]
      _ = s * b / (b * b) * d := by ring
  rw [ha, sign_mul, sign_pos hk, one_mul]

end Equivariance

/-! ### The orbit count -/

section OrbitCount

variable (G : Type*) {α β : Type*} [Group G] [MulAction G α]

/-- `s` is a set of representatives of the `G`-orbits in `S`: `s ⊆ S`, no two points of `s` lie
in one orbit, and every point of `S` lies in the orbit of a point of `s`. -/
def IsOrbitReps (s : Finset α) (S : Set α) : Prop :=
  (∀ x ∈ s, x ∈ S) ∧ (∀ x ∈ s, ∀ y ∈ s, (∃ g : G, g • x = y) → x = y) ∧
    ∀ y ∈ S, ∃ x ∈ s, ∃ g : G, g • x = y

variable {G}

/-- The points whose image lies in the orbit of `c` under `τ`: `{x | ∃ g, F x = τ g c}`. -/
def hitSet (τ : G → β → β) (F : α → β) (c : β) : Set α := {x | ∃ g : G, F x = τ g c}

/-- `N x = ♯{g | F x = τ g c}`. -/
def hitCount (τ : G → β → β) (F : α → β) (c : β) (x : α) : ℕ := Nat.card {g : G // F x = τ g c}

/-- The number of `g` with `g • x = h • x` is `♯G_x`. -/
theorem natCard_smul_eq_smul (x : α) (h : G) :
    Nat.card {g : G // g • x = h • x} = Nat.card (MulAction.stabilizer G x) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨h⁻¹ * g.1, ?_⟩
      invFun := fun k => ⟨h * k.1, ?_⟩
      left_inv := fun g => ?_
      right_inv := fun k => ?_ }
  · rw [MulAction.mem_stabilizer_iff, mul_smul, g.2, inv_smul_smul]
  · rw [mul_smul, MulAction.mem_stabilizer_iff.mp k.2]
  · ext
    simp
  · ext
    simp

variable {τ : G → β → β} (hτ1 : ∀ w, τ 1 w = w) (hτmul : ∀ g h w, τ (g * h) w = τ g (τ h w))
  {F : α → β} (hF : ∀ (g : G) x, F (g • x) = τ g (F x)) {c : β}

include hτ1 hτmul in
/-- `τ g⁻¹ (τ g w) = w`. -/
theorem τ_inv_apply (g : G) (w : β) : τ g⁻¹ (τ g w) = w := by
  rw [← hτmul, inv_mul_cancel, hτ1]

include hτ1 hτmul hF in
/-- `N(h • x) = N(x)`. -/
theorem hitCount_smul (h : G) (x : α) : hitCount τ F c (h • x) = hitCount τ F c x := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft h⁻¹) fun g => ?_)
  rw [Equiv.coe_mulLeft, hF, hτmul]
  constructor
  · intro hg
    rw [← hg, τ_inv_apply hτ1 hτmul]
  · intro hg
    rw [hg, ← hτmul, mul_inv_cancel, hτ1]

include hτ1 hτmul hF in
/-- The number of `g` with `F(g • x) = c` is `N x`. -/
theorem natCard_fiber_smul (x : α) :
    Nat.card {g : G // F (g • x) = c} = hitCount τ F c x := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.inv G) fun g => ?_)
  rw [Equiv.inv_apply, hF]
  constructor
  · intro hg
    rw [← hg, τ_inv_apply hτ1 hτmul]
  · intro hg
    rw [hg, ← hτmul, mul_inv_cancel, hτ1]

include hτ1 hτmul hF in
/-- `hitSet` is `G`-invariant. -/
theorem smul_mem_hitSet {x : α} (hx : x ∈ hitSet τ F c) (h : G) : h • x ∈ hitSet τ F c := by
  obtain ⟨g, hg⟩ := hx
  exact ⟨h * g, by rw [hF, hg, hτmul]⟩

include hτ1 hτmul hF in
/-- `hitSet` is finite when the fibre `F⁻¹(c)` is finite and `G` is finite. -/
theorem finite_hitSet [Finite G] (hfin : (F ⁻¹' {c}).Finite) : (hitSet τ F c).Finite := by
  refine (Set.finite_iUnion fun g : G => hfin.image (g • ·)).subset fun y hy => ?_
  obtain ⟨g, hg⟩ := hy
  refine mem_iUnion.mpr ⟨g, g⁻¹ • y, ?_, smul_inv_smul g y⟩
  change F (g⁻¹ • y) = c
  rw [hF, hg, τ_inv_apply hτ1 hτmul]

include hτ1 hτmul hF in
/-- **Orbit representatives exist** for a finite `hitSet`. -/
theorem exists_isOrbitReps (hS : (hitSet τ F c).Finite) :
    ∃ s : Finset α, IsOrbitReps G s (hitSet τ F c) := by
  classical
  let r : α → α := fun y => (Quotient.mk (MulAction.orbitRel G α) y).out
  have hr : ∀ y, ∃ g : G, g • r y = y := fun y => by
    have : (Quotient.mk (MulAction.orbitRel G α) (r y)) = Quotient.mk _ y := Quotient.out_eq _
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact this.symm)
    exact ⟨g, hg⟩
  have hq : ∀ y, Quotient.mk (MulAction.orbitRel G α) (r y) = Quotient.mk _ y :=
    fun y => Quotient.out_eq _
  refine ⟨hS.toFinset.image r, ⟨fun x hx => ?_, fun x hx x' hx' hxx' => ?_, fun y hy => ?_⟩⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨g, hg⟩ := hr y
    have := smul_mem_hitSet hτ1 hτmul hF (hS.mem_toFinset.mp hy) g⁻¹
    rwa [← hg, inv_smul_smul] at this
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', -, rfl⟩ := Finset.mem_image.mp hx'
    obtain ⟨g, hg⟩ := hxx'
    have h1 : Quotient.mk (MulAction.orbitRel G α) (r y') = Quotient.mk _ (r y) :=
      Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g, hg⟩)
    rw [hq, hq] at h1
    change (Quotient.mk (MulAction.orbitRel G α) y).out = (Quotient.mk _ y').out
    rw [h1]
  · exact ⟨r y, Finset.mem_image.mpr ⟨y, hS.mem_toFinset.mpr hy, rfl⟩, hr y⟩

include hτ1 hτmul hF in
/-- **The orbit count.** For orbit representatives `s` of `hitSet τ F c` and a `G`-invariant
`ε`, `∑_{x ∈ s} (♯G_x)⁻¹ · ε(x) · N(x)/♯G = (1/♯G) · ∑_{y ∈ F⁻¹(c)} ε(y)`. -/
theorem sum_orbitReps_eq [Fintype G] {ε : α → ℝ} (hε : ∀ (g : G) x, ε (g • x) = ε x)
    (hfin : (F ⁻¹' {c}).Finite) {s : Finset α} (hs : IsOrbitReps G s (hitSet τ F c)) :
    ∑ x ∈ s, ((Nat.card (MulAction.stabilizer G x) : ℝ))⁻¹ *
        (ε x * ((hitCount τ F c x : ℝ) / Fintype.card G)) =
      (Fintype.card G : ℝ)⁻¹ * ∑ᶠ y ∈ F ⁻¹' {c}, ε y := by
  classical
  obtain ⟨-, hsd, hsc⟩ := hs
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  set t := hfin.toFinset with ht
  have hA : ∀ y ∈ t, ε y = ∑ x ∈ s, ∑ g : G,
      (if g • x = y then ((Nat.card (MulAction.stabilizer G x) : ℝ))⁻¹ * ε y else 0) := by
    intro y hy
    have hyF : F y = c := hfin.mem_toFinset.mp hy
    have hyS : y ∈ hitSet τ F c := ⟨1, by rw [hτ1, hyF]⟩
    obtain ⟨x0, hx0, g0, hg0⟩ := hsc y hyS
    rw [Finset.sum_eq_single x0]
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.univ.filter fun g : G => g • x0 = y).card =
          Nat.card (MulAction.stabilizer G x0) := by
        rw [← natCard_smul_eq_smul x0 g0, hg0, Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [hcard]
      have hpos : (0 : ℝ) < Nat.card (MulAction.stabilizer G x0) := by
        exact_mod_cast Nat.card_pos
      field_simp
    · intro x hx hne
      refine Finset.sum_eq_zero fun g _ => ?_
      rw [if_neg]
      intro hgx
      apply hne
      refine hsd x hx x0 hx0 ⟨g0⁻¹ * g, ?_⟩
      rw [mul_smul, hgx, ← hg0, inv_smul_smul]
    · intro h
      exact absurd hx0 h
  have hB : ∀ x ∈ s, ∑ y ∈ t, ∑ g : G,
      (if g • x = y then ((Nat.card (MulAction.stabilizer G x) : ℝ))⁻¹ * ε y else 0) =
        ((Nat.card (MulAction.stabilizer G x) : ℝ))⁻¹ * (ε x * hitCount τ F c x) := by
    intro x _
    rw [Finset.sum_comm]
    have h1 : ∀ g : G, ∑ y ∈ t,
        (if g • x = y then ((Nat.card (MulAction.stabilizer G x) : ℝ))⁻¹ * ε y else 0) =
          if F (g • x) = c then ((Nat.card (MulAction.stabilizer G x) : ℝ))⁻¹ * ε x else 0 := by
      intro g
      rw [Finset.sum_ite_eq, hε]
      exact if_congr hfin.mem_toFinset rfl rfl
    have hc : ((Finset.univ.filter fun g : G => F (g • x) = c).card : ℝ) = hitCount τ F c x := by
      rw [← natCard_fiber_smul hτ1 hτmul hF x, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, hc]
    ring
  rw [Finset.sum_congr rfl hA, Finset.sum_comm, Finset.sum_congr rfl hB, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

end OrbitCount

/-! ### The classical count of an equivariant map -/

section ClassicalCount

variable {G : Type} [Group G] [Fintype G] {n : ℕ} [DistribMulAction G (Fin n → ℝ)]
  [SMulCommClass G ℝ (Fin n → ℝ)] {σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))}
  {φ : (Fin n → ℝ) → (Fin n → ℝ)} {c : Fin n → ℝ}

variable (G) in
/-- **The classical count** `(1/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)`. -/
def classicalCount (φ : (Fin n → ℝ) → (Fin n → ℝ)) (c : Fin n → ℝ) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ *
    ∑ᶠ x ∈ φ ⁻¹' {c}, (SignType.sign (LinearMap.det
      (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) : ℝ)

omit [Fintype G] [SMulCommClass G ℝ (Fin n → ℝ)] [DistribMulAction G (Fin n → ℝ)] in
/-- `w ↦ σ g w` is an action: the unit. -/
theorem σ_one_apply (w : Fin n → ℝ) : (fun (g : G) (w : Fin n → ℝ) => σ g w) 1 w = w := by
  simp

omit [Fintype G] [SMulCommClass G ℝ (Fin n → ℝ)] [DistribMulAction G (Fin n → ℝ)] in
/-- `w ↦ σ g w` is an action: composition. -/
theorem σ_mul_apply (g h : G) (w : Fin n → ℝ) :
    (fun (g : G) (w : Fin n → ℝ) => σ g w) (g * h) w = σ g (σ h w) := by
  simp only [map_mul]
  rfl

omit [Fintype G] in
/-- **Orbit representatives of the solutions** exist when `φ⁻¹(c)` is finite. -/
theorem exists_isOrbitReps_of_finite [Finite G] (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hfin : (φ ⁻¹' {c}).Finite) :
    ∃ s : Finset (Fin n → ℝ), IsOrbitReps G s (hitSet (fun g w => σ g w) φ c) :=
  exists_isOrbitReps σ_one_apply σ_mul_apply heq
    (finite_hitSet σ_one_apply σ_mul_apply heq hfin)

/-- **The weighted count over orbit representatives is the classical count**:
`∑_{x ∈ s} (♯G_x)⁻¹ · sign det Dφ(x) · N(x)/♯G = (1/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)`,
with `N(x) = ♯{g | φ(x) = σ g c}`. -/
theorem sum_orbitReps_eq_classicalCount (hφ : Differentiable ℝ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hfin : (φ ⁻¹' {c}).Finite) {s : Finset (Fin n → ℝ)}
    (hs : IsOrbitReps G s (hitSet (fun g w => σ g w) φ c)) :
    ∑ x ∈ s, ((Nat.card (MulAction.stabilizer G x) : ℝ))⁻¹ *
        ((SignType.sign (LinearMap.det (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) : ℝ) *
          ((hitCount (fun g w => σ g w) φ c x : ℝ) / Fintype.card G)) =
      classicalCount G φ c :=
  sum_orbitReps_eq σ_one_apply σ_mul_apply heq
    (ε := fun x => (SignType.sign (LinearMap.det
      (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) : ℝ))
    (fun g x => by rw [sign_det_fderiv_smul hφ heq hdet g x]) hfin hs

/-- The same for a proper `C¹` equivariant map at a regular value `c`; the fibre is finite by
`finite_preimage_of_regular`. -/
theorem sum_orbitReps_eq_classicalCount_of_regular (hφ : ContDiff ℝ 1 φ)
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K))
    (hc : ∀ x, φ x = c → Function.Surjective (fderiv ℝ φ x))
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    {s : Finset (Fin n → ℝ)} (hs : IsOrbitReps G s (hitSet (fun g w => σ g w) φ c)) :
    ∑ x ∈ s, ((Nat.card (MulAction.stabilizer G x) : ℝ))⁻¹ *
        ((SignType.sign (LinearMap.det (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) : ℝ) *
          ((hitCount (fun g w => σ g w) φ c x : ℝ) / Fintype.card G)) =
      classicalCount G φ c :=
  sum_orbitReps_eq_classicalCount (hφ.differentiable one_ne_zero) heq hdet
    (finite_preimage_of_regular hφ hprop hc) hs

end ClassicalCount

end Polyfold.Examples.Classical
