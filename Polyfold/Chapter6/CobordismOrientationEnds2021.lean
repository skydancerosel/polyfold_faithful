import Polyfold.Chapter6.CobordismOrientation2021
import Polyfold.Chapter6.CobordismRelativeForms2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.7, p. 278 (proof of
**Theorem 6.7.1**; preprint Theorem 6.43) and **Remark 6.6.19**, p. 276: the orientation of the
cobordism `S_F` on its product ends, linear algebra and the tangent map.

# The product orientation on an end: linear algebra and the tangent map of the inclusion

* `pullOr_wedgeExtLeft_eq_std_iff`: if the isomorphism `ι̂ : ℝ^{k+1} ≅ N'` is
  `(s, w) ↦ s e' + M(ι w)` for `ι : ℝ^k ≅ N`, then the orientation `e' ∧ M(r)` of `N'` reads as
  the standard orientation of `ℝ^{k+1}` exactly when `r` reads as the standard orientation of
  `ℝ^k` (the time vector first on both sides).
* `MPolyfold.derivIn_prodRn`: the tangent map of `A' ↪ ℝ¹ × X` on a product end `(a, b) × A`, in
  the corner coordinates `κ.prodRn` and a product chart, is `(s, w) ↦ (s, Tι(w))` for the tangent
  map `Tι` of `A ↪ X` in `κ`.
-/

open Set Filter Topology Manifold Module

noncomputable section

namespace Polyfold

universe u v

local notation "𝓠" => modelWithCornersEuclideanQuadrant

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### Linear algebra -/

section LinearAlgebra

variable {k : ℕ} {N N' : Type*} [AddCommGroup N] [Module ℝ N] [AddCommGroup N'] [Module ℝ N']

/-- The standard basis of `ℝ^{k+1}` is `e₀ = (1, 0)` followed by the `(0, eᵢ)`. -/
theorem basisFun_succ_eq_append (i : Fin (1 + k)) :
    (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis (Fin.cast (add_comm 1 k) i) =
      Fin.append ![consE 1 (0 : EuclideanSpace ℝ (Fin k))]
        (fun j => consE 0 ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis j)) i := by
  induction i using Fin.addCases with
  | left i =>
    fin_cases i
    have h0 : Fin.cast (add_comm 1 k) (Fin.castAdd k (0 : Fin 1)) = 0 := Fin.ext rfl
    simp only [Fin.append_left, Fin.zero_eta, Matrix.cons_val_zero]
    rw [h0]
    ext j
    refine Fin.cases ?_ (fun l => ?_) j
    · simp [consE]
    · simp [consE, Fin.succ_ne_zero]
  | right j =>
    have h1 : Fin.cast (add_comm 1 k) (Fin.natAdd 1 j) = j.succ :=
      Fin.ext (by simp)
    simp only [Fin.append_right]
    rw [h1]
    ext l
    refine Fin.cases ?_ (fun m => ?_) l
    · simp [consE, (Fin.succ_ne_zero j).symm]
    · simp [consE, Pi.single_apply]

/-- **The product orientation in coordinates** (the time vector first, 2021 Remark 6.6.19): if
`ι̂(s, w) = s e' + M(ι w)`, then the ray `e' ∧ M(r)` of `λ(N')` pulls back along `ι̂` to the
standard orientation of `ℝ^{k+1}` iff `r` pulls back along `ι` to that of `ℝ^k`. -/
theorem pullOr_wedgeExtLeft_eq_std_iff (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] N)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N') (M : N →ₗ[ℝ] N') (e' : N')
    (h : 1 + finrank ℝ N = finrank ℝ N')
    (hι : ∀ s w, ι' (consE s w) = s • e' + M (ι w)) (Ψ : maxPow N ≃ₗ[ℝ] maxPow N')
    (hΨ : ∀ w, Ψ w = wedgeExtLeft M ![e'] h w) (r : Module.Ray ℝ (maxPow N)) :
    pullOr finrank_euclideanSpace_fin ι' (Module.Ray.map Ψ r) = stdOrientation (k + 1) ↔
      pullOr finrank_euclideanSpace_fin ι r = stdOrientation k := by
  have hk : k = finrank ℝ N := finrank_euclideanSpace_fin.symm.trans ι.finrank_eq
  have hk' : k + 1 = finrank ℝ N' := finrank_euclideanSpace_fin.symm.trans ι'.finrank_eq
  set b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis with hb
  set b' := (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis with hb'
  have key : Ψ (wedge (fun i => ι (b i)) hk) = wedge (fun i => ι' (b' i)) hk' := by
    rw [hΨ, wedgeExtLeft_wedge, ← wedge_cast (fun i => ι' (b' i)) hk' (add_comm 1 k)]
    refine wedge_congr_fun (funext fun i => ?_) _ _
    simp only [Function.comp_apply]
    rw [hb', basisFun_succ_eq_append]
    induction i using Fin.addCases with
    | left i =>
      fin_cases i
      simp only [Fin.append_left]
      change e' = ι' (consE 1 0)
      rw [hι, map_zero, map_zero, one_smul, add_zero]
    | right j =>
      simp only [Fin.append_right, Function.comp_apply]
      rw [hι, zero_smul, zero_add]
  rw [eq_comm, eq_comm (b := stdOrientation k)]
  unfold stdOrientation
  rw [orientation_eq_pullOr_iff, orientation_eq_pullOr_iff]
  have hray : Module.Ray.map Ψ (rayOfNeZero ℝ _
      (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι b)) =
      rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι' b') := by
    rw [Module.Ray.map_apply]
    exact rayOfNeZero_eq_of_eq _ _ key
  rw [← hray, (Module.Ray.map Ψ).injective.eq_iff]

end LinearAlgebra

/-! ### The tangent map of the inclusion on a product end -/

section TangentEnd

open MPolyfold MPolyfold.CornerCoords

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [ParacompactSpace ((Fin 1 → ℝ) × X)] {A : Set X} [ParacompactSpace A]
  {hA : PX.IsSubMPolyfold A} {A' : Set ((Fin 1 → ℝ) × X)} [ParacompactSpace A']
  (hA' : ((rnPolyfold 1).prod PX).IsSubMPolyfold A') {a b : ℝ} (hab : a < b)
  (hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo a b → (z ∈ A' ↔ z.2 ∈ A)) (x₀ : A) {k : ℕ}

/-- The extended chart of `κ.prodRn` is `p ↦ (t − a, κ(x))`. -/
theorem MPolyfold.CornerCoords.prodRn_extend_apply (κ : CornerCoords (subPolyfold hA) k)
    {p : A'} (hp : p ∈ (κ.prodRn hA' hab hend x₀).s) :
    (κ.prodRn hA' hab hend x₀).toQuadrantChart.extend (𝓠 (k + 1)) p =
      consE (p.1.1 0 - a) (κ.toQuadrantChart.extend (𝓠 k) (endProj A x₀ p)) := by
  rw [(κ.prodRn hA' hab hend x₀).extend_apply hp,
    κ.extend_apply ((mem_prodRn_s hA' hab hend x₀ κ).1 hp).2, prodRn_coord]
  rfl

/-- **The tangent map on a product end** (proof of 2021 Theorem 6.7.1, p. 278): if
`h'(t, x) = (t, h(x))` on the end `(a, b) × A` of `A'`, then the tangent map of `h'` in the
corner coordinates `κ.prodRn` is `v ↦ (v₀, Th(v₁, …, v_k))` for the tangent map `Th` of `h` in
`κ`. -/
theorem MPolyfold.derivIn_prodRn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (κ : CornerCoords (subPolyfold hA) k) (h : A → F) (h' : A' → (Fin 1 → ℝ) × F)
    (hh : ∀ q : A', q.1.1 0 ∈ Ioo a b → h' q = (q.1.1, h (endProj A x₀ q)))
    {p : A'} (hp : p ∈ (κ.prodRn hA' hab hend x₀).s) {D : EuclideanSpace ℝ (Fin k) →L[ℝ] F}
    (hD : HasFDerivWithinAt (h ∘ (κ.toQuadrantChart.extend (𝓠 k)).symm) D (range (𝓠 k))
      (κ.toQuadrantChart.extend (𝓠 k) (endProj A x₀ p)))
    (v : EuclideanSpace ℝ (Fin (k + 1))) :
    derivIn (𝓠 (k + 1)) (κ.prodRn hA' hab hend x₀).toQuadrantChart h' p v =
      ((fun _ => v 0), D (tailE v)) := by
  set κ' := κ.prodRn hA' hab hend x₀ with hκ'
  set e := κ.toQuadrantChart with he
  set e' := κ'.toQuadrantChart with he'
  have hpe : p ∈ e'.source := hp
  set L : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] (Fin 1 → ℝ) :=
    ContinuousLinearMap.pi fun _ : Fin 1 => (EuclideanSpace.proj (0 : Fin (k + 1)) : _ →L[ℝ] ℝ)
    with hL
  set G : EuclideanSpace ℝ (Fin (k + 1)) → (Fin 1 → ℝ) × F :=
    fun y => ((fun _ => y 0 + a), (h ∘ (e.extend (𝓠 k)).symm) (tailE y)) with hG
  have hy₀ : e'.extend (𝓠 (k + 1)) p =
      consE (p.1.1 0 - a) (e.extend (𝓠 k) (endProj A x₀ p)) :=
    prodRn_extend_apply hA' hab hend x₀ κ hp
  have h1 : HasFDerivWithinAt (fun y : EuclideanSpace ℝ (Fin (k + 1)) =>
      (fun _ : Fin 1 => y 0 + a)) L (range (𝓠 (k + 1))) (e'.extend (𝓠 (k + 1)) p) := by
    have := (L.hasFDerivAt (x := e'.extend (𝓠 (k + 1)) p)).add_const (fun _ : Fin 1 => a)
    exact this.hasFDerivWithinAt
  have h2 : HasFDerivWithinAt (fun y : EuclideanSpace ℝ (Fin (k + 1)) =>
      (h ∘ (e.extend (𝓠 k)).symm) (tailE y)) (D.comp (tailCLM k)) (range (𝓠 (k + 1)))
      (e'.extend (𝓠 (k + 1)) p) := by
    have hD' : HasFDerivWithinAt (h ∘ (e.extend (𝓠 k)).symm) D (range (𝓠 k))
        (tailCLM k (e'.extend (𝓠 (k + 1)) p)) := by
      rw [hy₀, tailCLM_apply, tailE_consE]; exact hD
    exact hD'.comp _ (tailCLM k).hasFDerivAt.hasFDerivWithinAt mapsTo_tailE_range
  have hGd : HasFDerivWithinAt G (L.prod (D.comp (tailCLM k))) (range (𝓠 (k + 1)))
      (e'.extend (𝓠 (k + 1)) p) := h1.prodMk h2
  have hEq : ∀ y ∈ (e'.extend (𝓠 (k + 1))).target,
      (h' ∘ (e'.extend (𝓠 (k + 1))).symm) y = G y := by
    intro y hy
    set q := (e'.extend (𝓠 (k + 1))).symm y with hq
    have hqs : q ∈ κ'.s := by
      have := (e'.extend (𝓠 (k + 1))).map_target hy
      rwa [e'.extend_source] at this
    have hqy : e'.extend (𝓠 (k + 1)) q = y := (e'.extend (𝓠 (k + 1))).right_inv hy
    rw [prodRn_extend_apply hA' hab hend x₀ κ hqs] at hqy
    obtain ⟨hqt, hqκ⟩ := (mem_prodRn_s hA' hab hend x₀ κ).1 hqs
    have ht : q.1.1 0 = y 0 + a := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin (k + 1)) => w 0) hqy
      simp only [consE_zero] at this
      linarith
    have hx : endProj A x₀ q = (e.extend (𝓠 k)).symm (tailE y) := by
      rw [← hqy, tailE_consE, e.extend_left_inv (by exact hqκ)]
    change h' q = G y
    rw [hh q hqt, hG]
    refine Prod.ext (funext fun i => ?_) (by rw [hx]; rfl)
    rw [Subsingleton.elim i 0]
    exact ht
  have hfin : HasFDerivWithinAt (h' ∘ (e'.extend (𝓠 (k + 1))).symm)
      (L.prod (D.comp (tailCLM k))) (range (𝓠 (k + 1))) (e'.extend (𝓠 (k + 1)) p) :=
    hGd.congr_of_eventuallyEq
      (Filter.eventually_of_mem (e'.extend_target_mem_nhdsWithin hpe) hEq)
      (hEq _ ((e'.extend (𝓠 (k + 1))).map_source (by rwa [e'.extend_source])))
  have hder : derivIn (𝓠 (k + 1)) e' h' p = L.prod (D.comp (tailCLM k)) := by
    refine hfin.fderivWithin ?_
    rw [OpenPartialHomeomorph.extend_coe]
    exact (𝓠 (k + 1)).uniqueDiffWithinAt_image
  rw [hder]
  rfl

end TangentEnd

end Polyfold
