import Polyfold.Chapter6.Continuation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 224–225: the linear algebra of **Lemma 6.33** (adding sc⁺-sections does not change the
push-forward; "one verifies by a simple computation") *(book 2017: Lemma 6.15; see
`BookConcordance.md`)*.

# Adding sections to a stabilization

## The text, paraphrased

Adding sections `s̄₁, …, s̄_l` to `s₁, …, s_k` replaces the stabilization `T ⊕ φ` by
`T ⊕ φ ⊕ ψ` and the kernel bundle `L` by a bundle `L̃`.  The text passes through a homotopy whose
end is `L ⊕ ([0, 1] × ℝˡ)` and says that "a simple computation" shows that this defines the same
propagation.

## What is formalized

* `wedgeExt M ℓ`: `λ(K) → λ(K')`, `w ↦ M(w) ∧ ℓ₁ ∧ … ∧ ℓ_d`; `wedgeExt_wedge`, `wedgeExt_congr`
  (only the classes of the `ℓⱼ` modulo `M(K)` matter), `wedgeExt_bijective`.
* `appendStab φ ψ`: the stabilization by the appended sections,
  `μ ↦ φ(μ ∘ castAdd) + ψ(μ ∘ natAdd)`;
  `kerAppend`: `ker(T ⊕ φ) → ker(T ⊕ (φ, ψ))`, `(v, λ) ↦ (v, λ ++ 0)`.
* `detEquiv_stabIota_append`: **the simple computation**: under `det(T ⊕ φ) ≅ λ(ker(T ⊕ φ))`, the
  stabilization isomorphism of `(φ, ψ)` is that of `φ` followed by `wedgeExt kerAppend ℓ`, for any
  `ℓⱼ ∈ ker(T ⊕ (φ, ψ))` whose `ψ`-coordinates are the standard basis (Proposition 6.15).
* `isLineOrientation_wedgeExt`: `wedgeExt` carries continuous orientations of a family `Λ` to
  continuous orientations of a family `Λ'` with `Λ' ⊇ M(Λ)` and `Λ'/M(Λ) ≅ ℝᵈ`.
* `propagate_append`: **adding sections does not change the push-forward** `propagate`.

## Reading

The text's homotopy `F̃(τ, ·)` is not needed: the comparison is made directly between `T ⊕ φ` and
`T ⊕ (φ, ψ)`, by Proposition 6.15 at the two end points and by `isLineOrientation_wedgeExt` along
the family.  The appended sections come last (`Fin.castAdd`, `Fin.natAdd`); with this order the two
isomorphisms agree exactly (no sign).
-/

open Module TensorProduct Bundle Topology Set

noncomputable section

namespace Polyfold

/-! ### `w ↦ M(w) ∧ ℓ₁ ∧ … ∧ ℓ_d` -/

section WedgeExt

variable {K K' : Type*} [AddCommGroup K] [Module ℝ K] [AddCommGroup K'] [Module ℝ K']

/-- **`λ(K) → λ(K')`, `w ↦ M(w) ∧ ℓ₁ ∧ … ∧ ℓ_d`** (the product in the exterior algebra), for
`dim K + d = dim K'`. -/
def wedgeExt (M : K →ₗ[ℝ] K') {d : ℕ} (ℓ : Fin d → K')
    (h : finrank ℝ K + d = finrank ℝ K') : maxPow K →ₗ[ℝ] maxPow K' :=
  (LinearEquiv.ofEq _ _ (by rw [h])).toLinearMap ∘ₗ
    exteriorPower.alternatingMapLinearEquiv
      ((appendLeftMap (exteriorPower.ιMulti ℝ (finrank ℝ K + d)) ℓ).compLinearMap M)

/-- `wedgeExt` on a wedge: `M(b₁) ∧ … ∧ M(bₙ) ∧ ℓ₁ ∧ … ∧ ℓ_d`. -/
theorem wedgeExt_wedge (M : K →ₗ[ℝ] K') {d : ℕ} (ℓ : Fin d → K')
    (h : finrank ℝ K + d = finrank ℝ K') {n : ℕ} (b : Fin n → K) (hb : n = finrank ℝ K) :
    wedgeExt M ℓ h (wedge b hb) = wedge (Fin.append (M ∘ b) ℓ) (by omega) := by
  subst hb
  apply Subtype.ext
  rw [wedge_eq_ιMulti]
  simp only [wedgeExt, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, LinearEquiv.coe_ofEq_apply,
    AlternatingMap.compLinearMap_apply, coe_wedge]
  rfl

/-- The wedge depends only on the family. -/
theorem wedge_congr_fun {k : ℕ} {v w : Fin k → K} (h : v = w) (hv : k = finrank ℝ K)
    (hw : k = finrank ℝ K) : wedge v hv = wedge w hw := by
  subst h
  rfl

/-- Only the classes of the `ℓⱼ` modulo `M(K)` matter. -/
theorem wedgeExt_congr [FiniteDimensional ℝ K] (M : K →ₗ[ℝ] K') {d : ℕ} {ℓ ℓ' : Fin d → K'}
    (h : finrank ℝ K + d = finrank ℝ K') (hℓ : ∀ j, ℓ j - ℓ' j ∈ LinearMap.range M) :
    wedgeExt M ℓ h = wedgeExt M ℓ' h := by
  set b := Module.finBasis ℝ K
  apply maxPow_linearMap_ext b rfl
  rw [wedgeExt_wedge, wedgeExt_wedge]
  have hrange : LinearMap.range M = Submodule.span ℝ (Set.range (M ∘ b)) := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top]
  have hsum : ℓ = ℓ' + (ℓ - ℓ') := by abel
  rw [wedge_congr_fun (congrArg (Fin.append (M ∘ b)) hsum) _ (by omega)]
  exact wedge_append_add_right _ _ _ (fun i => hrange ▸ hℓ i) _

/-- `Fin.append u w` is linearly independent if `u` and `w` are and their spans are disjoint. -/
theorem linearIndependent_fin_append_of_disjoint {p q : ℕ} {u : Fin p → K} {w : Fin q → K}
    (hu : LinearIndependent ℝ u) (hw : LinearIndependent ℝ w)
    (hd : Disjoint (Submodule.span ℝ (Set.range u)) (Submodule.span ℝ (Set.range w))) :
    LinearIndependent ℝ (Fin.append u w) := by
  have hs : LinearIndependent ℝ (Sum.elim u w) := linearIndependent_sum.2 ⟨hu, hw, hd⟩
  have : Fin.append u w = Sum.elim u w ∘ finSumFinEquiv.symm := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  rw [this]
  exact hs.comp _ finSumFinEquiv.symm.injective

/-- `Fin.append u ℓ` is linearly independent if `u` is, `p` kills the `uᵢ` and the `p(ℓⱼ)` are
linearly independent. -/
theorem linearIndependent_fin_append_of_map {N : Type*} [AddCommGroup N] [Module ℝ N]
    (p : K →ₗ[ℝ] N) {n d : ℕ} {u : Fin n → K} (hu : LinearIndependent ℝ u)
    (hpu : ∀ i, p (u i) = 0) {ℓ : Fin d → K} (hℓ : LinearIndependent ℝ (p ∘ ℓ)) :
    LinearIndependent ℝ (Fin.append u ℓ) := by
  refine linearIndependent_fin_append_of_disjoint hu (LinearIndependent.of_comp p hℓ) ?_
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hpx : p x = 0 := by
    have hle : Submodule.span ℝ (Set.range u) ≤ LinearMap.ker p := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hpu i
    exact hle hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx'
  rw [map_sum] at hpx
  simp only [map_smul] at hpx
  have hc := Fintype.linearIndependent_iff.1 hℓ c hpx
  simp [hc]

/-- `Fin.append u ℓ` is linearly independent if `u` is, `p` kills the `uᵢ` and `p(ℓⱼ) = eⱼ`. -/
theorem linearIndependent_fin_append_of_single {d : ℕ} (p : K →ₗ[ℝ] Fin d → ℝ) {n : ℕ}
    {u : Fin n → K} (hu : LinearIndependent ℝ u) (hpu : ∀ i, p (u i) = 0) {ℓ : Fin d → K}
    (hℓ : ∀ j, p (ℓ j) = Pi.single j 1) : LinearIndependent ℝ (Fin.append u ℓ) := by
  refine linearIndependent_fin_append_of_map p hu hpu ?_
  rw [show p ∘ ℓ = ⇑(Pi.basisFun ℝ (Fin d)) from
    funext fun j => by rw [Function.comp_apply, hℓ j, Pi.basisFun_apply]]
  exact (Pi.basisFun ℝ (Fin d)).linearIndependent

/-- A linear map of lines that is nonzero at one vector is bijective. -/
theorem bijective_of_apply_ne_zero_of_finrank_eq_one {L L' : Type*} [AddCommGroup L]
    [Module ℝ L] [AddCommGroup L'] [Module ℝ L'] (h1 : finrank ℝ L = 1) (h1' : finrank ℝ L' = 1)
    (f : L →ₗ[ℝ] L') {v : L} (hv : f v ≠ 0) : Function.Bijective f := by
  have : FiniteDimensional ℝ L := Module.finite_of_finrank_eq_succ h1
  have : FiniteDimensional ℝ L' := Module.finite_of_finrank_eq_succ h1'
  have hv0 : v ≠ 0 := fun h => hv (by rw [h, map_zero])
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one h1 hv0 x
    rw [map_smul, smul_eq_zero] at hx
    rcases hx with rfl | h
    · exact zero_smul _ _
    · exact absurd h hv
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (h1.trans h1'.symm)).1 hinj⟩

/-- `wedgeExt` is an isomorphism when `M` is injective and the `ℓⱼ` are independent modulo
`M(K)`. -/
theorem wedgeExt_bijective [FiniteDimensional ℝ K] [FiniteDimensional ℝ K']
    (M : K →ₗ[ℝ] K') (hM : Function.Injective M) {d : ℕ} (ℓ : Fin d → K')
    (hℓ : LinearIndependent ℝ ℓ)
    (hdisj : Disjoint (LinearMap.range M) (Submodule.span ℝ (Set.range ℓ)))
    (h : finrank ℝ K + d = finrank ℝ K') :
    Function.Bijective (wedgeExt M ℓ h) := by
  set b := Module.finBasis ℝ K
  have hrange : LinearMap.range M = Submodule.span ℝ (Set.range (M ∘ b)) := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top]
  have hli : LinearIndependent ℝ (Fin.append (M ∘ b) ℓ) :=
    linearIndependent_fin_append_of_disjoint
      (b.linearIndependent.map' M (LinearMap.ker_eq_bot.2 hM)) hℓ (hrange ▸ hdisj)
  refine bijective_of_apply_ne_zero_of_finrank_eq_one finrank_maxPow finrank_maxPow _
    (v := wedge b rfl) ?_
  rw [wedgeExt_wedge]
  exact (wedge_ne_zero_iff _).2 hli

/-- **The kernel of a projection**: for `M : K → K'` injective and `p : K' → ℝᵈ` onto with
`p ∘ M = 0` and `dim K + d = dim K'`, `M(K) = ker p`. -/
theorem range_eq_ker_of_proj [FiniteDimensional ℝ K] [FiniteDimensional ℝ K']
    (M : K →ₗ[ℝ] K') (hM : Function.Injective M) {d : ℕ} (p : K' →ₗ[ℝ] Fin d → ℝ)
    (hpM : ∀ v, p (M v) = 0) (hp : Function.Surjective p)
    (h : finrank ℝ K + d = finrank ℝ K') : LinearMap.range M = LinearMap.ker p := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨v, rfl⟩
    exact hpM v
  · have h1 := LinearMap.finrank_range_add_finrank_ker p
    rw [LinearMap.range_eq_top.2 hp, finrank_top, Module.finrank_fin_fun] at h1
    rw [LinearMap.finrank_range_of_inj hM]
    omega

/-- Only the `p`-images of the `ℓⱼ` matter. -/
theorem wedgeExt_congr_of_proj [FiniteDimensional ℝ K] [FiniteDimensional ℝ K']
    (M : K →ₗ[ℝ] K') (hM : Function.Injective M) {d : ℕ} (p : K' →ₗ[ℝ] Fin d → ℝ)
    (hpM : ∀ v, p (M v) = 0) (hp : Function.Surjective p)
    (h : finrank ℝ K + d = finrank ℝ K') {ℓ ℓ' : Fin d → K'} (hℓ : ∀ j, p (ℓ j) = p (ℓ' j)) :
    wedgeExt M ℓ h = wedgeExt M ℓ' h := by
  refine wedgeExt_congr M h fun j => ?_
  rw [range_eq_ker_of_proj M hM p hpM hp h, LinearMap.mem_ker, map_sub, hℓ j, sub_self]

/-- `wedgeExt` is bijective when `p ∘ M = 0` and `p(ℓⱼ) = eⱼ`. -/
theorem wedgeExt_bijective_of_proj [FiniteDimensional ℝ K] [FiniteDimensional ℝ K']
    (M : K →ₗ[ℝ] K') (hM : Function.Injective M) {d : ℕ} (p : K' →ₗ[ℝ] Fin d → ℝ)
    (hpM : ∀ v, p (M v) = 0) (ℓ : Fin d → K') (hℓ : ∀ j, p (ℓ j) = Pi.single j 1)
    (h : finrank ℝ K + d = finrank ℝ K') :
    Function.Bijective (wedgeExt M ℓ h) := by
  set b := Module.finBasis ℝ K
  refine bijective_of_apply_ne_zero_of_finrank_eq_one finrank_maxPow finrank_maxPow _
    (v := wedge b rfl) ?_
  rw [wedgeExt_wedge]
  exact (wedge_ne_zero_iff _).2 (linearIndependent_fin_append_of_single p
    (b.linearIndependent.map' M (LinearMap.ker_eq_bot.2 hM)) (fun i => hpM _) hℓ)

end WedgeExt

/-! ### The stabilization by appended sections -/

section Append

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k d : ℕ}

/-- `ℝ^{k+d} → ℝᵏ`, `μ ↦ μ ∘ castAdd`. -/
def restrictCastAdd (k d : ℕ) : (Fin (k + d) → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd d i)

/-- `ℝ^{k+d} → ℝᵈ`, `μ ↦ μ ∘ natAdd`. -/
def restrictNatAdd (k d : ℕ) : (Fin (k + d) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.natAdd k j)

/-- `(μ ∘ castAdd)ᵢ = μ(castAdd i)`. -/
@[simp] theorem restrictCastAdd_apply (μ : Fin (k + d) → ℝ) (i : Fin k) :
    restrictCastAdd k d μ i = μ (Fin.castAdd d i) := rfl

/-- `(μ ∘ natAdd)ⱼ = μ(natAdd j)`. -/
@[simp] theorem restrictNatAdd_apply (μ : Fin (k + d) → ℝ) (j : Fin d) :
    restrictNatAdd k d μ j = μ (Fin.natAdd k j) := rfl

/-- `(a ++ b) ∘ castAdd = a`. -/
@[simp] theorem restrictCastAdd_append (a : Fin k → ℝ) (b : Fin d → ℝ) :
    restrictCastAdd k d (Fin.append a b) = a :=
  funext fun i => Fin.append_left a b i

/-- `(a ++ b) ∘ natAdd = b`. -/
@[simp] theorem restrictNatAdd_append (a : Fin k → ℝ) (b : Fin d → ℝ) :
    restrictNatAdd k d (Fin.append a b) = b :=
  funext fun j => Fin.append_right a b j

/-- `ℝᵏ → ℝ^{k+d}`, `λ ↦ λ ++ 0`. -/
def appendZero (k d : ℕ) : (Fin k → ℝ) →L[ℝ] (Fin (k + d) → ℝ) :=
  ContinuousLinearMap.pi
    (Fin.append (fun i => ContinuousLinearMap.proj i) (0 : Fin d → (Fin k → ℝ) →L[ℝ] ℝ))

theorem appendZero_apply (k d : ℕ) (lam : Fin k → ℝ) :
    appendZero k d lam = Fin.append lam 0 := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [appendZero]

/-- **The stabilization by `s₁, …, s_k, s̄₁, …, s̄_d`**: `μ ↦ φ(μ ∘ castAdd) + ψ(μ ∘ natAdd)`. -/
def appendStab (φ : (Fin k → ℝ) →L[ℝ] F) (ψ : (Fin d → ℝ) →L[ℝ] F) :
    (Fin (k + d) → ℝ) →L[ℝ] F :=
  φ.comp (restrictCastAdd k d) + ψ.comp (restrictNatAdd k d)

variable {T : E →L[ℝ] F} {φ : (Fin k → ℝ) →L[ℝ] F} {ψ : (Fin d → ℝ) →L[ℝ] F}

omit [CompleteSpace F] in
/-- `(φ, ψ)(a ++ b) = φ(a) + ψ(b)`. -/
theorem appendStab_append (a : Fin k → ℝ) (b : Fin d → ℝ) :
    appendStab φ ψ (Fin.append a b) = φ a + ψ b := by
  simp [appendStab]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Adding sections keeps the stabilization onto. -/
theorem surjective_appendStab (hφ : Function.Surjective (T.coprod φ)) :
    Function.Surjective (T.coprod (appendStab φ ψ)) := by
  intro y
  obtain ⟨x, hx⟩ := hφ y
  refine ⟨(x.1, Fin.append x.2 0), ?_⟩
  rw [ContinuousLinearMap.coprod_apply] at hx ⊢
  rw [appendStab_append, map_zero, add_zero]
  exact hx

/-- **The inclusion `ker(T ⊕ φ) → ker(T ⊕ (φ, ψ))`**, `(v, λ) ↦ (v, λ ++ 0)`. -/
def kerAppend (T : E →L[ℝ] F) (φ : (Fin k → ℝ) →L[ℝ] F) (ψ : (Fin d → ℝ) →L[ℝ] F) :
    LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F) →ₗ[ℝ]
      LinearMap.ker ((T.coprod (appendStab φ ψ) : E × (Fin (k + d) → ℝ) →L[ℝ] F) :
        E × (Fin (k + d) → ℝ) →ₗ[ℝ] F) :=
  LinearMap.codRestrict _
    (LinearMap.prodMap LinearMap.id (appendZero k d : (Fin k → ℝ) →ₗ[ℝ] Fin (k + d) → ℝ) ∘ₗ
      (LinearMap.ker _).subtype)
    (fun x => by
      refine mem_ker_coprod.2 ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        LinearMap.prodMap_apply, LinearMap.id_coe, id_eq, ContinuousLinearMap.coe_coe,
        appendZero_apply, appendStab_append, map_zero, add_zero]
      exact mem_ker_coprod.1 x.2)

omit [CompleteSpace E] [CompleteSpace F] in
theorem coe_kerAppend (x : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
    E × (Fin k → ℝ) →ₗ[ℝ] F)) :
    (kerAppend T φ ψ x : E × (Fin (k + d) → ℝ)) =
      ((x : E × (Fin k → ℝ)).1, Fin.append (x : E × (Fin k → ℝ)).2 0) := by
  rw [← appendZero_apply]
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- `(v, λ) ↦ (v, λ ++ 0)` is injective. -/
theorem kerAppend_injective : Function.Injective (kerAppend T φ ψ) := by
  intro x y h
  have h' := congrArg Subtype.val h
  simp only [coe_kerAppend, Prod.mk.injEq] at h'
  have h2 := congrArg (restrictCastAdd k d) h'.2
  simp only [restrictCastAdd_append] at h2
  exact Subtype.ext (Prod.ext h'.1 h2)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `(e, 0) ↦ (e, 0 ++ 0) = (e, 0)`: `kerAppend ∘ j_φ = j_{(φ, ψ)}`. -/
theorem kerAppend_stabJ (x : LinearMap.ker (T : E →ₗ[ℝ] F)) :
    kerAppend T φ ψ (stabJ T φ x) = stabJ T (appendStab φ ψ) x := by
  apply Subtype.ext
  rw [coe_kerAppend, coe_stabJ, coe_stabJ]
  simp only [Prod.mk.injEq, true_and]
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

omit [CompleteSpace E] [CompleteSpace F] in
/-- The dimensions: `dim ker(T ⊕ (φ, ψ)) = dim ker(T ⊕ φ) + d`. -/
theorem finrank_ker_appendStab (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ)) :
    finrank ℝ (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
        E × (Fin k → ℝ) →ₗ[ℝ] F)) + d =
      finrank ℝ (LinearMap.ker ((T.coprod (appendStab φ ψ) : E × (Fin (k + d) → ℝ) →L[ℝ] F) :
        E × (Fin (k + d) → ℝ) →ₗ[ℝ] F)) := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  have := finiteDimensional_ker_coprod (T := T) (φ := appendStab φ ψ)
  have h1 := LinearMap.finrank_le_finrank_of_injective (stabJ_injective (T := T) (φ := φ))
  have h2 := LinearMap.finrank_le_finrank_of_injective
    (stabJ_injective (T := T) (φ := appendStab φ ψ))
  have e1 := stab_card_eq hT hφ rfl (Nat.add_sub_cancel' h1)
  have e2 := stab_card_eq hT (surjective_appendStab (ψ := ψ) hφ) rfl (Nat.add_sub_cancel' h2)
  omega

/-- The determinant of the block matrix `[[C, ρ], [0, 1]]` (columns `(Cᵢ, 0)` and `μⱼ`). -/
theorem det_append_appendZero (C : Fin k → Fin k → ℝ) (μ : Fin d → Fin (k + d) → ℝ)
    (hμ : ∀ j, restrictNatAdd k d (μ j) = Pi.single j 1) :
    (Pi.basisFun ℝ (Fin (k + d))).det (Fin.append (appendZero k d ∘ C) μ) =
      (Pi.basisFun ℝ (Fin k)).det C := by
  have hμ' : ∀ i j, μ j (Fin.natAdd k i) = if i = j then 1 else 0 := fun i j => by
    have := congrFun (hμ j) i
    simpa [Pi.single_apply] using this
  rw [Basis.det_apply, Basis.det_apply, ← Matrix.det_reindex_self finSumFinEquiv.symm]
  have hblk : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      ((Pi.basisFun ℝ (Fin (k + d))).toMatrix (Fin.append (appendZero k d ∘ C) μ)) =
      Matrix.fromBlocks ((Pi.basisFun ℝ (Fin k)).toMatrix C)
        (Matrix.of fun i j => μ j (Fin.castAdd d i)) 0 1 := by
    ext (i | i) (j | j) <;>
      simp [Basis.toMatrix_apply, appendZero_apply, Matrix.one_apply, hμ']
  rw [hblk, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- `det(c̄ ++ 0, r ++ 0, μ) = det(c̄, r)` when `μⱼ` has `natAdd`-part `eⱼ`. -/
theorem det_append_appendZero_cast {m l : ℕ} (h : m + l = k) (h' : m + (l + d) = k + d)
    (c : Fin m → Fin k → ℝ) (r : Fin l → Fin k → ℝ) (μ : Fin d → Fin (k + d) → ℝ)
    (hμ : ∀ j, restrictNatAdd k d (μ j) = Pi.single j 1) :
    (Pi.basisFun ℝ (Fin (k + d))).det
        (Fin.append (appendZero k d ∘ c) (Fin.append (appendZero k d ∘ r) μ) ∘
          Fin.cast h'.symm) =
      (Pi.basisFun ℝ (Fin k)).det (Fin.append c r ∘ Fin.cast h.symm) := by
  subst h
  have e1 : Fin.append (appendZero (m + l) d ∘ c) (Fin.append (appendZero (m + l) d ∘ r) μ) ∘
      Fin.cast h'.symm = Fin.append (appendZero (m + l) d ∘ Fin.append c r) μ := by
    rw [comp_append, Fin.append_assoc]
  rw [e1, det_append_appendZero _ _ hμ]
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- `det(T ⊕ χ) ≅ λ(ker(T ⊕ χ))` sends `w ⊗ 1*` to `w`. -/
theorem detEquivOfSurjective_tmul_stabOne {n : ℕ} {χ : (Fin n → ℝ) →L[ℝ] F}
    (hχ : Function.Surjective (T.coprod χ))
    (w : maxPow (LinearMap.ker ((T.coprod χ : E × (Fin n → ℝ) →L[ℝ] F) :
      E × (Fin n → ℝ) →ₗ[ℝ] F))) :
    detEquivOfSurjective hχ (w ⊗ₜ stabOne hχ) = w := by
  have := finiteDimensional_coker_coprod hχ
  rw [detEquivOfSurjective_tmul]
  have h1 : stabOne hχ (emptyWedge _ (finrank_coker_of_surjective hχ)) = 1 :=
    dualVec_self finrank_maxPow (emptyWedge_ne_zero _ (finrank_coker_of_surjective hχ))
  rw [h1, one_smul]

/-- Two linear maps out of a tensor product of lines agree if they agree at one `v₁ ⊗ v₂` with
`v₁, v₂ ≠ 0`. -/
theorem tensor_line_ext {L₁ L₂ N : Type*} [AddCommGroup L₁] [Module ℝ L₁] [AddCommGroup L₂]
    [Module ℝ L₂] [AddCommGroup N] [Module ℝ N] (h1 : finrank ℝ L₁ = 1)
    (h2 : finrank ℝ L₂ = 1) {v₁ : L₁} {v₂ : L₂} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    {f g : L₁ ⊗[ℝ] L₂ →ₗ[ℝ] N} (h : f (v₁ ⊗ₜ v₂) = g (v₁ ⊗ₜ v₂)) : f = g := by
  apply TensorProduct.ext'
  intro x y
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one h1 hv₁ x
  obtain ⟨c', rfl⟩ := exists_smul_eq_of_finrank_eq_one h2 hv₂ y
  rw [TensorProduct.smul_tmul_smul, map_smul, map_smul, h]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Vectors `c̄ᵢ ∈ ℝᵏ` whose classes `φ(c̄ᵢ) + R(T)` form a basis of `F / R(T)`. -/
theorem exists_stabClass_linearIndependent (hT : T.IsFredholm)
    (hφ : Function.Surjective (T.coprod φ)) :
    ∃ cbar : Fin (finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))) → Fin k → ℝ,
      LinearIndependent ℝ (stabClass T φ ∘ cbar) := by
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  choose cbar hcbar using fun i => stabClass_surjective hφ (Module.finBasis ℝ _ i)
  refine ⟨cbar, ?_⟩
  rw [show stabClass T φ ∘ cbar = ⇑(Module.finBasis ℝ _) from funext hcbar]
  exact (Module.finBasis ℝ _).linearIndependent

omit [CompleteSpace E] [CompleteSpace F] in
/-- Vectors `b̄₁, …, b̄_l` completing `(a₁, 0), …, (a_p, 0)` to a basis of `ker(T ⊕ φ)`. -/
theorem exists_stabJ_completion (hT : T.IsFredholm) {p : ℕ}
    (a : Basis (Fin p) ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))) :
    ∃ (l : ℕ) (bbar : Fin l → LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F)), LinearIndependent ℝ (Fin.append (stabJ T φ ∘ a) bbar) ∧
        p + l = finrank ℝ (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
          E × (Fin k → ℝ) →ₗ[ℝ] F)) := by
  have := hT.finite_ker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  obtain ⟨Z, hZ⟩ := Submodule.exists_isCompl (LinearMap.range (stabJ T φ))
  set bZ := Module.finBasis ℝ Z
  have hspanJ : Submodule.span ℝ (Set.range (stabJ T φ ∘ a)) = LinearMap.range (stabJ T φ) := by
    rw [Set.range_comp, Submodule.span_image, a.span_eq, Submodule.map_top]
  have hspanZ : Submodule.span ℝ (Set.range (Z.subtype ∘ bZ)) = Z := by
    rw [Set.range_comp, Submodule.span_image, bZ.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  refine ⟨finrank ℝ Z, Z.subtype ∘ bZ, linearIndependent_fin_append_of_disjoint
      (a.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 stabJ_injective))
      (bZ.linearIndependent.map' _ (Submodule.ker_subtype _))
      (by rw [hspanJ, hspanZ]; exact hZ.disjoint), ?_⟩
  rw [← Submodule.finrank_add_eq_of_isCompl hZ, LinearMap.finrank_range_of_inj stabJ_injective,
    Module.finrank_eq_card_basis a, Fintype.card_fin]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The simple computation of Lemma 6.33 at a generator** `(a₁ ∧ … ∧ a_p) ⊗ (d̄₁ ∧ … ∧ d̄_m)*`,
by Proposition 6.15 for `φ` (data `c̄`, `b̄`) and for `(φ, ψ)` (data `c̄ ++ 0`, `(b̄ ++ 0, ℓ)`). -/
theorem detEquiv_stabIota_append_wedge (hT : T.IsFredholm)
    (hφ : Function.Surjective (T.coprod φ))
    (ℓ : Fin d → LinearMap.ker ((T.coprod (appendStab φ ψ) : E × (Fin (k + d) → ℝ) →L[ℝ] F) :
        E × (Fin (k + d) → ℝ) →ₗ[ℝ] F))
    (hℓ : ∀ j, restrictNatAdd k d (ℓ j : E × (Fin (k + d) → ℝ)).2 = Pi.single j 1)
    {p l : ℕ} (a : Basis (Fin p) ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))
    (cbar : Fin (finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))) → Fin k → ℝ)
    (hd : LinearIndependent ℝ (stabClass T φ ∘ cbar))
    (bbar : Fin l → LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F))
    (hb : LinearIndependent ℝ (Fin.append (stabJ T φ ∘ a) bbar))
    (hkl : p + l = finrank ℝ (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F)))
    (hn : finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) + l = k) :
    detEquivOfSurjective (surjective_appendStab (ψ := ψ) hφ)
        (stabIota hT (surjective_appendStab (ψ := ψ) hφ)
          (wedge a (by rw [Module.finrank_eq_card_basis a, Fintype.card_fin]) ⊗ₜ
            dualVec (wedge (stabClass T φ ∘ cbar) rfl))) =
      wedgeExt (kerAppend T φ ψ) ℓ (finrank_ker_appendStab hT hφ)
        (detEquivOfSurjective hφ (stabIota hT hφ
          (wedge a (by rw [Module.finrank_eq_card_basis a, Fintype.card_fin]) ⊗ₜ
            dualVec (wedge (stabClass T φ ∘ cbar) rfl)))) := by
  have hcd' : stabClass T (appendStab φ ψ) ∘ (appendZero k d ∘ cbar) = stabClass T φ ∘ cbar :=
    funext fun i => by simp [appendZero_apply, appendStab_append]
  have hkl' : p + (l + d) =
      finrank ℝ (LinearMap.ker ((T.coprod (appendStab φ ψ) : E × (Fin (k + d) → ℝ) →L[ℝ] F) :
        E × (Fin (k + d) → ℝ) →ₗ[ℝ] F)) := by
    rw [← finrank_ker_appendStab (ψ := ψ) hT hφ]
    omega
  have hn' : finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) + (l + d) = k + d := by omega
  have hJ : stabJ T (appendStab φ ψ) ∘ a = kerAppend T φ ψ ∘ (stabJ T φ ∘ a) :=
    funext fun i => (kerAppend_stabJ (a i)).symm
  have hW : wedge (Fin.append (stabJ T (appendStab φ ψ) ∘ a)
      (Fin.append (kerAppend T φ ψ ∘ bbar) ℓ)) hkl' =
      wedgeExt (kerAppend T φ ψ) ℓ (finrank_ker_appendStab hT hφ)
        (wedge (Fin.append (stabJ T φ ∘ a) bbar) hkl) := by
    rw [wedgeExt_wedge, wedge_append_assoc _ _ _ hkl' (by omega)]
    refine wedge_congr_fun ?_ _ _
    rw [comp_append, hJ]
  have hb' : LinearIndependent ℝ (Fin.append (stabJ T (appendStab φ ψ) ∘ a)
      (Fin.append (kerAppend T φ ψ ∘ bbar) ℓ)) := by
    have := hT.finite_ker
    have := finiteDimensional_ker_coprod (T := T) (φ := appendStab φ ψ)
    rw [← wedge_ne_zero_iff hkl', hW, wedgeExt_wedge, wedge_ne_zero_iff]
    exact linearIndependent_fin_append_of_single ((restrictNatAdd k d :
      (Fin (k + d) → ℝ) →ₗ[ℝ] Fin d → ℝ) ∘ₗ LinearMap.snd ℝ E (Fin (k + d) → ℝ) ∘ₗ
        (LinearMap.ker _).subtype) (hb.map' _ (LinearMap.ker_eq_bot.2 kerAppend_injective))
      (fun i => by simp [coe_kerAppend]) hℓ
  have h615 := proposition_6_15 hT hφ a cbar hd rfl bbar hb hkl hn
  have h615' := proposition_6_15 hT (surjective_appendStab (ψ := ψ) hφ) a
    (appendZero k d ∘ cbar) (hcd' ▸ hd) rfl _ hb' hkl' hn'
  have hX := congrArg (fun w => wedge a (by rw [Module.finrank_eq_card_basis a,
    Fintype.card_fin]) ⊗ₜ[ℝ] dualVec w) (wedge_congr_fun hcd' rfl rfl)
  have hr : (fun i => (Fin.append (kerAppend T φ ψ ∘ bbar) ℓ i).1.2) =
      Fin.append (appendZero k d ∘ fun i => (bbar i).1.2) (fun j => (ℓ j).1.2) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left, Fin.append_left, Function.comp_apply, Function.comp_apply,
        coe_kerAppend, appendZero_apply]
    · rw [Fin.append_right, Fin.append_right]
  have hdet : (Pi.basisFun ℝ (Fin (k + d))).det (Fin.append (appendZero k d ∘ cbar)
      (fun i => (Fin.append (kerAppend T φ ψ ∘ bbar) ℓ i).1.2) ∘ Fin.cast hn'.symm) =
      (Pi.basisFun ℝ (Fin k)).det (Fin.append cbar (fun i => (bbar i).1.2) ∘ Fin.cast hn.symm) := by
    rw [hr]
    exact det_append_appendZero_cast hn hn' _ _ _ hℓ
  exact (congrArg (fun y => detEquivOfSurjective (surjective_appendStab (ψ := ψ) hφ)
      (stabIota hT (surjective_appendStab (ψ := ψ) hφ) y)) hX.symm).trans <|
    (congrArg (detEquivOfSurjective (surjective_appendStab (ψ := ψ) hφ)) h615').trans <|
    (LinearEquiv.map_smul _ _ _).trans <|
    (congrArg (_ • ·) (detEquivOfSurjective_tmul_stabOne _ _)).trans <|
    (congrArg (fun c : ℝ => c⁻¹ • _) hdet).trans <|
    (congrArg (_ • ·) hW).trans <|
    (LinearMap.map_smul _ _ _).symm.trans <|
    (congrArg (wedgeExt (kerAppend T φ ψ) ℓ (finrank_ker_appendStab hT hφ))
      ((congrArg (_ • ·) (detEquivOfSurjective_tmul_stabOne hφ _).symm).trans
        (LinearEquiv.map_smul _ _ _).symm)).trans <|
    congrArg (fun y => wedgeExt (kerAppend T φ ψ) ℓ (finrank_ker_appendStab hT hφ)
      (detEquivOfSurjective hφ y)) h615.symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The simple computation of Lemma 6.33**: for `ℓⱼ ∈ ker(T ⊕ (φ, ψ))` whose `ψ`-coordinates are
the standard basis vectors `eⱼ`, the stabilization isomorphism of `(φ, ψ)` is that of `φ` followed
by `w ↦ (w, 0) ∧ ℓ₁ ∧ … ∧ ℓ_d` (Proposition 6.15 for both: the determinant in (94) is unchanged). -/
theorem detEquiv_stabIota_append (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    (ℓ : Fin d → LinearMap.ker ((T.coprod (appendStab φ ψ) : E × (Fin (k + d) → ℝ) →L[ℝ] F) :
        E × (Fin (k + d) → ℝ) →ₗ[ℝ] F))
    (hℓ : ∀ j, restrictNatAdd k d (ℓ j : E × (Fin (k + d) → ℝ)).2 = Pi.single j 1)
    (x : fredholmDet T) :
    detEquivOfSurjective (surjective_appendStab (ψ := ψ) hφ)
        (stabIota hT (surjective_appendStab (ψ := ψ) hφ) x) =
      wedgeExt (kerAppend T φ ψ) ℓ (finrank_ker_appendStab hT hφ)
        (detEquivOfSurjective hφ (stabIota hT hφ x)) := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have hc := exists_stabClass_linearIndependent hT hφ
  have hbb := exists_stabJ_completion (φ := φ) hT (Module.finBasis ℝ (LinearMap.ker
    (T : E →ₗ[ℝ] F)))
  have hn := stab_card_eq hT hφ rfl hbb.choose_spec.choose_spec.2
  refine LinearMap.congr_fun (f := (detEquivOfSurjective
    (surjective_appendStab (ψ := ψ) hφ)).toLinearMap ∘ₗ
      stabIota hT (surjective_appendStab (ψ := ψ) hφ))
    (g := wedgeExt (kerAppend T φ ψ) ℓ (finrank_ker_appendStab hT hφ) ∘ₗ
      (detEquivOfSurjective hφ).toLinearMap ∘ₗ stabIota hT hφ) ?_ x
  exact tensor_line_ext finrank_maxPow finrank_maxPowDual (wedge_basis_ne_zero' _ _)
    (dualVec_ne_zero finrank_maxPow ((wedge_ne_zero_iff _).2 hc.choose_spec))
    (detEquiv_stabIota_append_wedge hT hφ ℓ hℓ _ hc.choose hc.choose_spec _
      hbb.choose_spec.choose_spec.1 hbb.choose_spec.choose_spec.2 hn)

end Append

/-! ### Along a family -/

section Family

variable {Q : Type*} [TopologicalSpace Q] {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W'] {d : ℕ}

/-- **Continuous lifts**: if `p : W' → ℝᵈ` maps every member of a continuous family `Λ'` onto
`ℝᵈ`, then near every point there are continuous `λⱼ(q) ∈ Λ'_q` with `p(λⱼ(q)) = eⱼ` (lift the
`eⱼ` at the point in a frame, and correct by the inverse of the matrix `p(λ(q))`). -/
theorem SubspaceFamily.exists_continuous_lifts (Λ' : SubspaceFamily Q W')
    (p : W' →L[ℝ] (Fin d → ℝ)) (hp : ∀ q, (Λ'.L q).map (p : W' →ₗ[ℝ] Fin d → ℝ) = ⊤) (q₀ : Q) :
    ∃ V : Set Q, IsOpen V ∧ q₀ ∈ V ∧ ∃ lam : Fin d → Q → W', (∀ j, ContinuousOn (lam j) V) ∧
      ∀ q ∈ V, ∀ j, lam j q ∈ Λ'.L q ∧ p (lam j q) = Pi.single j 1 := by
  set η := Λ'.frameAt q₀
  have hq₀ : q₀ ∈ η.U := Λ'.mem_frameAt q₀
  have hlift : ∀ j, ∃ v : Λ'.L q₀, p v = Pi.single j 1 := fun j => by
    have h : Pi.single j 1 ∈ (Λ'.L q₀).map (p : W' →ₗ[ℝ] Fin d → ℝ) := by
      rw [hp q₀]
      exact Submodule.mem_top
    obtain ⟨v, hv, hpv⟩ := h
    exact ⟨⟨v, hv⟩, hpv⟩
  choose v hv using hlift
  let w : Fin d → Q → W' := fun j q => ∑ i, (η.basis hq₀).repr (v j) i • η.e i q
  have hwc : ∀ j, ContinuousOn (w j) η.U := fun j =>
    continuousOn_finsetSum _ fun i _ => continuousOn_const.smul (η.continuousOn i)
  have hwm : ∀ j, ∀ q ∈ η.U, w j q ∈ Λ'.L q := fun j q hq =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (η.mem q hq i)
  have hw₀ : ∀ j, w j q₀ = v j := fun j => by
    have h := congrArg Subtype.val ((η.basis hq₀).sum_repr (v j))
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, η.coe_basis hq₀] at h
    exact h
  let P : Q → Matrix (Fin d) (Fin d) ℝ := fun q => Matrix.of fun i k => p (w k q) i
  have hPc : ContinuousOn P η.U := continuousOn_pi.2 fun i => continuousOn_pi.2 fun k =>
    ((continuous_apply i).comp p.continuous).comp_continuousOn (hwc k)
  have hP₀ : P q₀ = 1 := by
    ext i k
    simp only [P, Matrix.of_apply, hw₀, hv, Pi.single_apply, Matrix.one_apply]
  set V := η.U ∩ (fun q => (P q).det) ⁻¹' {0}ᶜ with hV
  have hVo : IsOpen V := ((continuous_id.matrix_det).comp_continuousOn hPc).isOpen_inter_preimage
    η.isOpen isOpen_compl_singleton
  have hdet : ∀ q ∈ V, (P q).det ≠ 0 := fun q hq => hq.2
  have hq₀V : q₀ ∈ V := ⟨hq₀, by simp [hP₀]⟩
  have hinv₀ : ∀ q ∈ V, ContinuousAt Ring.inverse (P q).det := fun q hq => by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hdet q hq)
  have hPinv : ContinuousOn (fun q => (P q)⁻¹) V := fun q hq =>
    (continuousAt_matrix_inv (P q) (hinv₀ q hq)).comp_continuousWithinAt
      ((hPc q hq.1).mono inter_subset_left)
  refine ⟨V, hVo, hq₀V, fun j q => ∑ k, (P q)⁻¹ k j • w k q, fun j => ?_,
    fun q hq j => ⟨?_, ?_⟩⟩
  · exact continuousOn_finsetSum _ fun k _ =>
      (((continuous_apply j).comp (continuous_apply k)).comp_continuousOn hPinv).smul
        ((hwc k).mono inter_subset_left)
  · exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hwm k q hq.1)
  · have hinv : P q * (P q)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdet q hq))
    funext i
    have := congrFun (congrFun hinv i) j
    rw [Matrix.mul_apply] at this
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Pi.single_apply, ← Matrix.one_apply, ← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **`wedgeExt` carries continuous orientations along a family**: for continuous families `Λ` in
`W` and `Λ'` in `W'`, a fixed injective `M : W → W'` with `M(Λ_q) ⊆ Λ'_q`, and a fixed
`p : W' → ℝᵈ` vanishing on `M(Λ_q)` and onto on `Λ'_q`, with `dim Λ' = dim Λ + d`, the rays
`q ↦ λ(M) ∧ ℓ(q)` (for any lifts `ℓⱼ(q) ∈ Λ'_q` of the standard basis) of a continuous orientation
of `λ(Λ)` are a continuous orientation of `λ(Λ')`. -/
theorem isLineOrientation_wedgeExt (Λ : SubspaceFamily Q W) (Λ' : SubspaceFamily Q W')
    (M : W →L[ℝ] W') (hMinj : Function.Injective M) (hM : ∀ q, ∀ v ∈ Λ.L q, M v ∈ Λ'.L q)
    (p : W' →L[ℝ] (Fin d → ℝ)) (hpM : ∀ q, ∀ v ∈ Λ.L q, p (M v) = 0)
    (hp : ∀ q, (Λ'.L q).map (p : W' →ₗ[ℝ] Fin d → ℝ) = ⊤) (hn : Λ.n + d = Λ'.n)
    (ℓ : ∀ q, Fin d → Λ'.L q) (hℓ : ∀ q j, p (ℓ q j) = Pi.single j 1)
    (hbij : ∀ q, Function.Bijective (wedgeExt ((M : W →ₗ[ℝ] W').restrict (hM q)) (ℓ q)
      (by rw [Λ.finrank_eq, Λ'.finrank_eq, hn])))
    (o : LineOrientation Λ.det) :
    IsLineOrientation Λ'.det fun q =>
      Module.Ray.map (LinearEquiv.ofBijective _ (hbij q)) (o q) := by
  have hpr : ∀ q, Function.Surjective ((p : W' →ₗ[ℝ] Fin d → ℝ) ∘ₗ (Λ'.L q).subtype) := fun q =>
    LinearMap.range_eq_top.1 (by rw [LinearMap.range_comp, Submodule.range_subtype]; exact hp q)
  have hMr : ∀ q, Function.Injective ((M : W →ₗ[ℝ] W').restrict (hM q)) := fun q x y h =>
    Subtype.ext (hMinj (congrArg Subtype.val h))
  have hprM : ∀ q v, ((p : W' →ₗ[ℝ] Fin d → ℝ) ∘ₗ (Λ'.L q).subtype)
      ((M : W →ₗ[ℝ] W').restrict (hM q) v) = 0 := fun q v => hpM q v v.2
  intro q₀
  obtain ⟨U, hU, σ, hσ, hσo⟩ := o.2 q₀
  refine ⟨U, hU, fun q => wedgeExt ((M : W →ₗ[ℝ] W').restrict (hM q)) (ℓ q)
    (by rw [Λ.finrank_eq, Λ'.finrank_eq, hn]) (σ q), fun q hq => ?_, fun q hq => ?_⟩
  · set ε := Λ.frameAt q
    have hqε : q ∈ ε.U := Λ.mem_frameAt q
    obtain ⟨V, hVo, hqV, lam, hlc, hl⟩ := Λ'.exists_continuous_lifts p hp q
    let ε' : Λ'.Frame :=
      { U := ε.U ∩ V
        isOpen := ε.isOpen.inter hVo
        e := fun i b => Fin.append (fun i => M (ε.e i b)) (fun j => lam j b) (Fin.cast hn.symm i)
        continuousOn := fun i => by
          generalize Fin.cast hn.symm i = t
          induction t using Fin.addCases with
          | left i =>
            simp only [Fin.append_left]
            exact M.continuous.comp_continuousOn ((ε.continuousOn i).mono inter_subset_left)
          | right j =>
            simp only [Fin.append_right]
            exact (hlc j).mono inter_subset_right
        mem := fun b hb i => by
          generalize Fin.cast hn.symm i = t
          induction t using Fin.addCases with
          | left i =>
            rw [Fin.append_left]
            exact hM b _ (ε.mem b hb.1 i)
          | right j =>
            rw [Fin.append_right]
            exact (hl b hb.2 j).1
        linearIndependent := fun b hb => by
          have h1 := linearIndependent_fin_append_of_single (p : W' →ₗ[ℝ] Fin d → ℝ)
            ((ε.linearIndependent b hb.1).map' (M : W →ₗ[ℝ] W') (LinearMap.ker_eq_bot.2 hMinj))
            (fun i => hpM b _ (ε.mem b hb.1 i)) (fun j => (hl b hb.2 j).2)
          exact h1.comp _ (Fin.cast_injective _) }
    have hqε' : q ∈ ε'.U := ⟨hqε, hqV⟩
    have hvec : ∀ b (hb : b ∈ ε'.U), ε'.vec hb =
        Fin.append ((M : W →ₗ[ℝ] W').restrict (hM b) ∘ ε.vec hb.1)
          (fun j => ⟨lam j b, (hl b hb.2 j).1⟩) ∘ Fin.cast hn.symm := fun b hb => by
      funext i
      apply Subtype.ext
      change _ = (Subtype.val ∘ Fin.append _ _) (Fin.cast hn.symm i)
      rw [comp_append]
      rfl
    have hkey : ∀ b (hb : b ∈ ε'.U), wedgeExt ((M : W →ₗ[ℝ] W').restrict (hM b)) (ℓ b)
        (by rw [Λ.finrank_eq, Λ'.finrank_eq, hn]) (σ b) = ε.coord b (σ b) • ε'.wedgeAt b := by
      intro b hb
      have h2 : wedgeExt ((M : W →ₗ[ℝ] W').restrict (hM b))
          (fun j => ⟨lam j b, (hl b hb.2 j).1⟩) (by rw [Λ.finrank_eq, Λ'.finrank_eq, hn])
            (ε.wedgeAt b) = ε'.wedgeAt b := by
        rw [ε.wedgeAt_of_mem hb.1, wedgeExt_wedge, ε'.wedgeAt_of_mem hb, hvec b hb, wedge_cast]
      exact (LinearMap.congr_fun (wedgeExt_congr_of_proj _ (hMr b) _ (hprM b) (hpr b) _
        (ℓ' := fun j => ⟨lam j b, (hl b hb.2 j).1⟩)
        (fun j => (hℓ b j).trans (hl b hb.2 j).2.symm)) (σ b)).trans <|
        (congrArg _ (ε.coord_smul_wedgeAt hb.1 (σ b))).symm.trans <|
        (LinearMap.map_smul _ _ _).trans (congrArg _ h2)
    refine (Λ'.continuousWithinAt_section_iff ε' hqε').2 ?_
    refine ((Λ.continuousWithinAt_section_iff ε hqε).1 (hσ q hq)).congr_of_eventuallyEq ?_ ?_
    · exact eventually_nhdsWithin_of_eventually_nhds (Filter.eventually_of_mem
        (ε'.isOpen.mem_nhds hqε') fun b hb => by
          change ε'.coord b (wedgeExt _ _ _ (σ b)) = _
          rw [hkey b hb, map_smul, ε'.coord_wedgeAt hb, smul_eq_mul, mul_one])
    · change ε'.coord q (wedgeExt _ _ _ (σ q)) = _
      rw [hkey q hqε', map_smul, ε'.coord_wedgeAt hqε', smul_eq_mul, mul_one]
  · obtain ⟨h0, hoq⟩ := hσo q hq
    exact ⟨(LinearEquiv.ofBijective _ (hbij q)).map_ne_zero_iff.2 h0,
      (congrArg (Module.Ray.map (LinearEquiv.ofBijective _ (hbij q))) hoq).trans
        (Module.Ray.map_apply _ _ _)⟩

end Family

/-! ### Adding sections does not change the push-forward -/

section Propagate

variable {Q : Type*} [TopologicalSpace Q] [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k d : ℕ}
  {E₀ F₀ E₁ F₁ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [CompleteSpace F₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [CompleteSpace F₁]

/-- `j × 1` is injective for `j` injective. -/
theorem prodMap_id_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (j : E →L[ℝ] V) (hj : Function.Injective j) :
    Function.Injective ((j.prodMap (ContinuousLinearMap.id ℝ (Fin m → ℝ)) :
      E × (Fin m → ℝ) →L[ℝ] V × (Fin m → ℝ)) : E × (Fin m → ℝ) →ₗ[ℝ] V × (Fin m → ℝ)) := by
  intro x y h
  have h1 : j x.1 = j y.1 := congrArg (fun z => z.1) h
  have h2 : x.2 = y.2 := congrArg (fun z => z.2) h
  exact Prod.ext (hj h1) h2

/-- The identification `ker(T ⊕ φ) ≅ L` of the kernel with a member `L = (j × 1)(ker(T ⊕ φ))` of
a family in `V × ℝᵏ`, for `j : E → V` injective. -/
def kerEquivMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ} {T : E →L[ℝ] F}
    {φ : (Fin m → ℝ) →L[ℝ] F} (j : E →L[ℝ] V) (hj : Function.Injective j)
    {L : Submodule ℝ (V × (Fin m → ℝ))}
    (hL : L = (LinearMap.ker ((T.coprod φ : E × (Fin m → ℝ) →L[ℝ] F) :
      E × (Fin m → ℝ) →ₗ[ℝ] F)).map ((j.prodMap (ContinuousLinearMap.id ℝ (Fin m → ℝ)) :
        E × (Fin m → ℝ) →L[ℝ] V × (Fin m → ℝ)) : E × (Fin m → ℝ) →ₗ[ℝ] V × (Fin m → ℝ))) :
    LinearMap.ker ((T.coprod φ : E × (Fin m → ℝ) →L[ℝ] F) : E × (Fin m → ℝ) →ₗ[ℝ] F) ≃ₗ[ℝ] L :=
  (Submodule.equivMapOfInjective _ (prodMap_id_injective j hj) _).trans
    (LinearEquiv.ofEq _ _ hL.symm)

theorem coe_kerEquivMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ} {T : E →L[ℝ] F}
    {φ : (Fin m → ℝ) →L[ℝ] F} (j : E →L[ℝ] V) (hj : Function.Injective j)
    {L : Submodule ℝ (V × (Fin m → ℝ))}
    (hL : L = (LinearMap.ker ((T.coprod φ : E × (Fin m → ℝ) →L[ℝ] F) :
      E × (Fin m → ℝ) →ₗ[ℝ] F)).map ((j.prodMap (ContinuousLinearMap.id ℝ (Fin m → ℝ)) :
        E × (Fin m → ℝ) →L[ℝ] V × (Fin m → ℝ)) : E × (Fin m → ℝ) →ₗ[ℝ] V × (Fin m → ℝ)))
    (x : LinearMap.ker ((T.coprod φ : E × (Fin m → ℝ) →L[ℝ] F) : E × (Fin m → ℝ) →ₗ[ℝ] F)) :
    (kerEquivMap j hj hL x : V × (Fin m → ℝ)) =
      (j (x : E × (Fin m → ℝ)).1, (x : E × (Fin m → ℝ)).2) := by
  rfl

variable (V k d) in
/-- `V × ℝᵏ → V × ℝ^{k+d}`, `(v, λ) ↦ (v, λ ++ 0)`. -/
def appendZeroMap : V × (Fin k → ℝ) →L[ℝ] V × (Fin (k + d) → ℝ) :=
  (ContinuousLinearMap.id ℝ V).prodMap (appendZero k d)

/-- `(v, λ) ↦ (v, λ ++ 0)`. -/
theorem appendZeroMap_apply (v : V × (Fin k → ℝ)) :
    appendZeroMap V k d v = (v.1, Fin.append v.2 0) :=
  Prod.ext rfl (appendZero_apply k d v.2)

/-- `(v, λ) ↦ (v, λ ++ 0)` is injective. -/
theorem appendZeroMap_injective : Function.Injective (appendZeroMap V k d) := by
  intro v w h
  rw [appendZeroMap_apply, appendZeroMap_apply, Prod.mk.injEq] at h
  have h2 := congrArg (restrictCastAdd k d) h.2
  simp only [restrictCastAdd_append] at h2
  exact Prod.ext h.1 h2

/-- A ray equality from an equality of vectors. -/
theorem rayOfNeZero_eq_of_eq {M : Type*} [AddCommMonoid M] [Module ℝ M] {v w : M} (hv : v ≠ 0)
    (hw : w ≠ 0) (h : v = w) : rayOfNeZero ℝ v hv = rayOfNeZero ℝ w hw := by
  subst h
  rfl

omit [CompleteSpace E₀] [CompleteSpace F₀] in
/-- **At an end point**: the stabilized ray of `(φ, ψ)` is that of `φ` followed by
`λ(L) → λ(L')`, `w ↦ (w, 0) ∧ ℓ₁ ∧ … ∧ ℓ_d` (`detEquiv_stabIota_append` read through `j × 1`). -/
theorem stabRayEquiv_append {T : E₀ →L[ℝ] F₀} {φ : (Fin k → ℝ) →L[ℝ] F₀}
    {ψ : (Fin d → ℝ) →L[ℝ] F₀} (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    (j : E₀ →L[ℝ] V) (hj : Function.Injective j)
    {L : Submodule ℝ (V × (Fin k → ℝ))} {L' : Submodule ℝ (V × (Fin (k + d) → ℝ))}
    [FiniteDimensional ℝ L] [FiniteDimensional ℝ L']
    (hL : L = (LinearMap.ker ((T.coprod φ : E₀ × (Fin k → ℝ) →L[ℝ] F₀) :
      E₀ × (Fin k → ℝ) →ₗ[ℝ] F₀)).map ((j.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E₀ × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : E₀ × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ)))
    (hL' : L' = (LinearMap.ker ((T.coprod (appendStab φ ψ) :
      E₀ × (Fin (k + d) → ℝ) →L[ℝ] F₀) : E₀ × (Fin (k + d) → ℝ) →ₗ[ℝ] F₀)).map
        ((j.prodMap (ContinuousLinearMap.id ℝ (Fin (k + d) → ℝ)) :
          E₀ × (Fin (k + d) → ℝ) →L[ℝ] V × (Fin (k + d) → ℝ)) :
            E₀ × (Fin (k + d) → ℝ) →ₗ[ℝ] V × (Fin (k + d) → ℝ)))
    (hML : ∀ v ∈ L, appendZeroMap V k d v ∈ L') (hn : finrank ℝ L + d = finrank ℝ L')
    (ℓ : Fin d → L') (hℓ : ∀ i, restrictNatAdd k d (ℓ i : V × (Fin (k + d) → ℝ)).2 =
      Pi.single i 1)
    (hbij : Function.Bijective (wedgeExt ((appendZeroMap V k d :
      V × (Fin k → ℝ) →ₗ[ℝ] V × (Fin (k + d) → ℝ)).restrict hML) ℓ hn))
    (r : Module.Ray ℝ (fredholmDet T)) :
    stabRayEquiv hT (surjective_appendStab (ψ := ψ) hφ) (kerEquivMap j hj hL') r =
      Module.Ray.map (LinearEquiv.ofBijective _ hbij)
        (stabRayEquiv hT hφ (kerEquivMap j hj hL) r) := by
  have := hT.finite_ker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  have hℓ₀ : ∀ i, restrictNatAdd k d (((kerEquivMap j hj hL').symm (ℓ i) :
      LinearMap.ker _) : E₀ × (Fin (k + d) → ℝ)).2 = Pi.single i 1 := fun i => by
    rw [← hℓ i, ← LinearEquiv.apply_symm_apply (kerEquivMap j hj hL') (ℓ i), coe_kerEquivMap,
      LinearEquiv.apply_symm_apply]
  have h1 : ⇑(kerEquivMap j hj hL') ∘ ⇑(kerAppend T φ ψ) =
      ⇑((appendZeroMap V k d : V × (Fin k → ℝ) →ₗ[ℝ] V × (Fin (k + d) → ℝ)).restrict hML) ∘
        ⇑(kerEquivMap j hj hL) := by
    funext x
    apply Subtype.ext
    simp only [Function.comp_apply, LinearMap.restrict_apply, coe_kerEquivMap, coe_kerAppend,
      ContinuousLinearMap.coe_coe, appendZeroMap_apply]
  have hsq : (maxPowEquiv (kerEquivMap j hj hL')).toLinearMap ∘ₗ
      wedgeExt (kerAppend T φ ψ) (fun i => (kerEquivMap j hj hL').symm (ℓ i))
        (finrank_ker_appendStab hT hφ) =
      wedgeExt ((appendZeroMap V k d : V × (Fin k → ℝ) →ₗ[ℝ] V × (Fin (k + d) → ℝ)).restrict
        hML) ℓ hn ∘ₗ (maxPowEquiv (kerEquivMap j hj hL)).toLinearMap := by
    apply maxPow_linearMap_ext (Module.finBasis ℝ _) rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wedgeExt_wedge, maxPowEquiv_wedge]
    refine wedge_congr_fun ?_ _ _
    rw [comp_append]
    exact congrArg₂ Fin.append (by rw [← Function.comp_assoc, h1]; rfl)
      (funext fun i => LinearEquiv.apply_symm_apply _ _)
  induction r using Module.Ray.ind with | h x hx => ?_
  simp only [stabRayEquiv, Equiv.trans_apply, Module.Ray.map_apply]
  refine rayOfNeZero_eq_of_eq _ _ ?_
  exact (congrArg (maxPowEquiv (kerEquivMap j hj hL'))
    (detEquiv_stabIota_append hT hφ _ hℓ₀ x)).trans (LinearMap.congr_fun hsq _)

omit [CompleteSpace E₀] [CompleteSpace F₀] [CompleteSpace E₁] [CompleteSpace F₁] in
/-- **Adding sections does not change the push-forward** (the core of Lemma 6.33): for continuous
families `Λ` of `ker(T_q ⊕ φ_q)` in `V × ℝᵏ` and `Λ'` of `ker(T_q ⊕ (φ_q, ψ_q))` in `V × ℝ^{k+d}`
with `(v, λ) ↦ (v, λ ++ 0)` mapping `Λ_q` into `Λ'_q`, and end points `q₀, q₁` where both are the
images of the kernels of `T₀ ⊕ φ₀`, `T₀ ⊕ (φ₀, ψ₀)` (resp. at `q₁`) under `jᵢ × 1`, the two
push-forwards agree. -/
theorem propagate_append (Λ : SubspaceFamily Q (V × (Fin k → ℝ)))
    (Λ' : SubspaceFamily Q (V × (Fin (k + d) → ℝ)))
    (hM : ∀ q, ∀ v ∈ Λ.L q, ((v.1, Fin.append v.2 0) : V × (Fin (k + d) → ℝ)) ∈ Λ'.L q)
    (hp : ∀ q, (Λ'.L q).map (((restrictNatAdd k d).comp
      (ContinuousLinearMap.snd ℝ V (Fin (k + d) → ℝ)) : V × (Fin (k + d) → ℝ) →L[ℝ] Fin d → ℝ) :
        V × (Fin (k + d) → ℝ) →ₗ[ℝ] Fin d → ℝ) = ⊤)
    (hn : Λ.n + d = Λ'.n) (q₀ q₁ : Q)
    {T₀ : E₀ →L[ℝ] F₀} {φ₀ : (Fin k → ℝ) →L[ℝ] F₀} {ψ₀ : (Fin d → ℝ) →L[ℝ] F₀}
    (hT₀ : T₀.IsFredholm) (hφ₀ : Function.Surjective (T₀.coprod φ₀))
    (j₀ : E₀ →L[ℝ] V) (hj₀ : Function.Injective j₀)
    (hΛ₀ : Λ.L q₀ = (LinearMap.ker ((T₀.coprod φ₀ : E₀ × (Fin k → ℝ) →L[ℝ] F₀) :
      E₀ × (Fin k → ℝ) →ₗ[ℝ] F₀)).map ((j₀.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E₀ × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : E₀ × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ)))
    (hΛ'₀ : Λ'.L q₀ = (LinearMap.ker ((T₀.coprod (appendStab φ₀ ψ₀) :
      E₀ × (Fin (k + d) → ℝ) →L[ℝ] F₀) : E₀ × (Fin (k + d) → ℝ) →ₗ[ℝ] F₀)).map
        ((j₀.prodMap (ContinuousLinearMap.id ℝ (Fin (k + d) → ℝ)) :
          E₀ × (Fin (k + d) → ℝ) →L[ℝ] V × (Fin (k + d) → ℝ)) :
            E₀ × (Fin (k + d) → ℝ) →ₗ[ℝ] V × (Fin (k + d) → ℝ)))
    {T₁ : E₁ →L[ℝ] F₁} {φ₁ : (Fin k → ℝ) →L[ℝ] F₁} {ψ₁ : (Fin d → ℝ) →L[ℝ] F₁}
    (hT₁ : T₁.IsFredholm) (hφ₁ : Function.Surjective (T₁.coprod φ₁))
    (j₁ : E₁ →L[ℝ] V) (hj₁ : Function.Injective j₁)
    (hΛ₁ : Λ.L q₁ = (LinearMap.ker ((T₁.coprod φ₁ : E₁ × (Fin k → ℝ) →L[ℝ] F₁) :
      E₁ × (Fin k → ℝ) →ₗ[ℝ] F₁)).map ((j₁.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E₁ × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : E₁ × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ)))
    (hΛ'₁ : Λ'.L q₁ = (LinearMap.ker ((T₁.coprod (appendStab φ₁ ψ₁) :
      E₁ × (Fin (k + d) → ℝ) →L[ℝ] F₁) : E₁ × (Fin (k + d) → ℝ) →ₗ[ℝ] F₁)).map
        ((j₁.prodMap (ContinuousLinearMap.id ℝ (Fin (k + d) → ℝ)) :
          E₁ × (Fin (k + d) → ℝ) →L[ℝ] V × (Fin (k + d) → ℝ)) :
            E₁ × (Fin (k + d) → ℝ) →ₗ[ℝ] V × (Fin (k + d) → ℝ)))
    (r : Module.Ray ℝ (fredholmDet T₀)) :
    propagate Λ' q₀ q₁ hT₀ (surjective_appendStab hφ₀) (kerEquivMap j₀ hj₀ hΛ'₀)
        hT₁ (surjective_appendStab hφ₁) (kerEquivMap j₁ hj₁ hΛ'₁) r =
      propagate Λ q₀ q₁ hT₀ hφ₀ (kerEquivMap j₀ hj₀ hΛ₀) hT₁ hφ₁ (kerEquivMap j₁ hj₁ hΛ₁) r := by
  have hM' : ∀ q, ∀ v ∈ Λ.L q, appendZeroMap V k d v ∈ Λ'.L q := fun q v hv => by
    rw [appendZeroMap_apply]
    exact hM q v hv
  have hpM : ∀ q, ∀ v ∈ Λ.L q, ((restrictNatAdd k d).comp
      (ContinuousLinearMap.snd ℝ V (Fin (k + d) → ℝ))) (appendZeroMap V k d v) = 0 :=
    fun q v _ => by simp [appendZeroMap_apply]
  have hlift : ∀ q j, ∃ v : Λ'.L q, ((restrictNatAdd k d).comp
      (ContinuousLinearMap.snd ℝ V (Fin (k + d) → ℝ))) v = Pi.single j 1 := fun q j => by
    have h : Pi.single j 1 ∈ (Λ'.L q).map (((restrictNatAdd k d).comp
        (ContinuousLinearMap.snd ℝ V (Fin (k + d) → ℝ)) :
          V × (Fin (k + d) → ℝ) →L[ℝ] Fin d → ℝ) : V × (Fin (k + d) → ℝ) →ₗ[ℝ] Fin d → ℝ) := by
      rw [hp q]
      exact Submodule.mem_top
    obtain ⟨v, hv, hpv⟩ := h
    exact ⟨⟨v, hv⟩, hpv⟩
  choose ℓ hℓ using hlift
  have hbij : ∀ q, Function.Bijective (wedgeExt ((appendZeroMap V k d :
      V × (Fin k → ℝ) →ₗ[ℝ] V × (Fin (k + d) → ℝ)).restrict (hM' q)) (ℓ q)
        (by rw [Λ.finrank_eq, Λ'.finrank_eq, hn])) := fun q =>
    wedgeExt_bijective_of_proj _ (fun x y h => Subtype.ext (appendZeroMap_injective
      (congrArg Subtype.val h))) ((((restrictNatAdd k d).comp
        (ContinuousLinearMap.snd ℝ V (Fin (k + d) → ℝ)) :
          V × (Fin (k + d) → ℝ) →L[ℝ] Fin d → ℝ) : V × (Fin (k + d) → ℝ) →ₗ[ℝ] Fin d → ℝ) ∘ₗ
            (Λ'.L q).subtype) (fun v => hpM q v v.2) (ℓ q) (hℓ q) _
  obtain ⟨o, ho⟩ := exists_lineOrientation_apply_eq (L := Λ.det) q₀
    (stabRayEquiv hT₀ hφ₀ (kerEquivMap j₀ hj₀ hΛ₀) r)
  have hor := isLineOrientation_wedgeExt Λ Λ' (appendZeroMap V k d) appendZeroMap_injective hM'
    _ hpM hp hn ℓ hℓ hbij o
  have hc' : Λ'.cont q₀ q₁ (Module.Ray.map (LinearEquiv.ofBijective _ (hbij q₀)) (o q₀)) =
      Module.Ray.map (LinearEquiv.ofBijective _ (hbij q₁)) (o q₁) :=
    Λ'.cont_eq ⟨_, hor⟩ q₀ q₁
  have hc := Λ.cont_eq o q₀ q₁
  have h0 := stabRayEquiv_append (ψ := ψ₀) hT₀ hφ₀ j₀ hj₀ hΛ₀ hΛ'₀ (hM' q₀) _ (ℓ q₀) (hℓ q₀)
    (hbij q₀)
  have h1 := stabRayEquiv_append (ψ := ψ₁) hT₁ hφ₁ j₁ hj₁ hΛ₁ hΛ'₁ (hM' q₁) _ (ℓ q₁) (hℓ q₁)
    (hbij q₁)
  change (stabRayEquiv hT₁ (surjective_appendStab hφ₁) (kerEquivMap j₁ hj₁ hΛ'₁)).symm
      (Λ'.cont q₀ q₁ (stabRayEquiv hT₀ (surjective_appendStab hφ₀) (kerEquivMap j₀ hj₀ hΛ'₀) r)) =
    (stabRayEquiv hT₁ hφ₁ (kerEquivMap j₁ hj₁ hΛ₁)).symm
      (Λ.cont q₀ q₁ (stabRayEquiv hT₀ hφ₀ (kerEquivMap j₀ hj₀ hΛ₀) r))
  have e3 : stabRayEquiv hT₁ (surjective_appendStab hφ₁) (kerEquivMap j₁ hj₁ hΛ'₁)
      ((stabRayEquiv hT₁ hφ₁ (kerEquivMap j₁ hj₁ hΛ₁)).symm (o q₁)) =
        Module.Ray.map (LinearEquiv.ofBijective _ (hbij q₁)) (o q₁) :=
    (h1 _).trans (congrArg _ (Equiv.apply_symm_apply _ _))
  exact (congrArg (fun t => (stabRayEquiv hT₁ (surjective_appendStab hφ₁)
      (kerEquivMap j₁ hj₁ hΛ'₁)).symm (Λ'.cont q₀ q₁ t))
      ((h0 r).trans (congrArg _ ho.symm))).trans <|
    (congrArg (stabRayEquiv hT₁ (surjective_appendStab hφ₁) (kerEquivMap j₁ hj₁ hΛ'₁)).symm
      (hc'.trans e3.symm)).trans <|
    (Equiv.symm_apply_apply _ _).trans <|
    congrArg (stabRayEquiv hT₁ hφ₁ (kerEquivMap j₁ hj₁ hΛ₁)).symm
      (hc.symm.trans (congrArg _ ho))

end Propagate

end Polyfold
