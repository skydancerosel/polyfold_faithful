import Polyfold.Chapter4.ScExteriorDerivative2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, p. 197
(2017 pp. 149–150; preprint: before Definition 4.27): the naturality of the local exterior
derivative of `ScExteriorDerivative2021`, the step from the local `d` to `d` on an M-polyfold.
Numbers and pages are the 2021 text's.

# Naturality of the local exterior derivative

## The text, paraphrased

(p. 197) `dω` of a form on `Xⁱ` is defined through vector fields by the invariant formula, and
"this defines the exterior derivative as a linear operator `Ωᵏ(Xⁱ) → Ωᵏ⁺¹(Xⁱ⁺¹)`".  That the
result is again an sc-form, and does not depend on choices, is not discussed.

## What is proved

The local `d` is `ambientD U Ω (y, h₀, …, h_k) = Σⱼ (-1)ʲ DΩ(y, h₀, …, ĥⱼ, …, h_k)(hⱼ, 0)` and,
on a retract `O = r(U)`, `retractD R ω = d(ω ∘ ⊕ₖ Tr)` (`ScExteriorDerivative2021`).
* `ambientD_comp_whitneyMap`: `d(Ω ∘ ⊕ₖ Tf) = dΩ ∘ ⊕_{k+1} Tf¹` for `f : U → V` sc-smooth between
  relatively open subsets of partial quadrants.
* `retractD_comp_retractWhitneyMap`: the same for `f : O → O'` sc-smooth between sc-retracts.
* `retractD_eq_of_subset`: `d_rω` does not depend on the retraction `r`, and restricts to
  sub-retracts.

## Method

The chosen derivative of `q ↦ DΩ(…)` is computed on level `1` (`scDeriv_eq_of_hasFDerivWithinAt`,
chain rule `scDeriv_comp`); its fibre part is `scDeriv_whitney_fiber`.  The terms with the second
derivative of `f` cancel by the symmetry `scSecondDeriv_symm` and the alternation
`sum_update_symm_eq_zero`.
-/

open Set Function

noncomputable section

namespace Polyfold

variable {E F G : ScBanach}

/-! ### Computing chosen derivatives -/

section Deriv

variable {U : Set (E 0)} {V : Set (F 0)}

/-- **The chosen derivative is determined by a derivative on level `1`**: if `f : U₁ → F₀` has
derivative `L ∘ ι` at `x ∈ U₁` (unique differentiability), then `Df(x) = L`. -/
theorem IsSc1.scDeriv_eq_of_hasFDerivWithinAt {f : E 0 → F 0} (hf : IsSc1 U f) {x : E 1}
    (hx : x ∈ E.lvlSet U 1) (hU : UniqueDiffWithinAt ℝ (E.lvlSet U 1) x) {L : E 0 →L[ℝ] F 0}
    (h : HasFDerivWithinAt (f ∘ E.toBase 1) (L.comp (E.toBase 1)) (E.lvlSet U 1) x) :
    scDeriv U f x = L := by
  have h1 := hU.eq (hf.isSc1With_scDeriv.hasFDerivWithinAt x hx) h
  have hd : Dense (Submodule.span ℝ (range (E.toBase 1)) : Set (E 0)) :=
    Dense.mono Submodule.subset_span (E.denseRange_inclK 0 1)
  refine ContinuousLinearMap.ext_on hd ?_
  rintro _ ⟨y, rfl⟩
  exact congrArg (fun T : E 1 →L[ℝ] F 0 => T y) h1

/-- **The chain rule for the chosen derivatives**: `D(g ∘ f)(x) = Dg(f(x)) ∘ Df(x)` on `U₁`. -/
theorem scDeriv_comp (hU : IsScDomain E U) (hV : IsScDomain F V) {f : E 0 → F 0}
    {g : F 0 → G 0} (hf : IsSc1 U f) (hg : IsSc1 V g) (hfV : MapsTo f U V) {x : E 1}
    (hx : x ∈ E.lvlSet U 1) :
    scDeriv U (g ∘ f) x = (scDeriv V g (levelMap f 1 x)).comp (scDeriv U f x) :=
  IsSc1.scDeriv_eqOn (hg.isSc1With_scDeriv.comp (hV.relOpenConvex 1) hf.isSc1With_scDeriv hfV)
    (hU.uniqueDiffWithinAt 1) hx

/-- The chosen derivative depends only on the values on `U`. -/
theorem scDeriv_congr (hU : IsScDomain E U) {f f' : E 0 → F 0} (hf : IsSc1 U f)
    (h : EqOn f f' U) {x : E 1} (hx : x ∈ E.lvlSet U 1) : scDeriv U f' x = scDeriv U f x :=
  IsSc1.scDeriv_eqOn (hf.isSc1With_scDeriv.congr h) (hU.uniqueDiffWithinAt 1) hx

end Deriv

/-! ### The derivative of a fibrewise multilinear map along the fibre -/

section Fiber

variable {V : Set (F 0)} {k : ℕ}

lemma whitney_toBase_fst (p : (F.whitney k) 1) :
    ((F.whitney k).toBase 1 p).1 = F.shift.toBase 1 p.1 := by
  rw [ScBanach.prod_toBase]

lemma mem_whitneySet_lvl_one {p : (F.whitney k) 1} :
    p ∈ (F.whitney k).lvlSet (F.whitneySet k V) 1 ↔ F.shift.toBase 1 p.1 ∈ F.lvlSet V 1 := by
  rw [ScBanach.mem_lvlSet, ScBanach.mem_whitneySet, whitney_toBase_fst]

lemma add_smul_single_eq_update (w : Fin k → F 0) (i : Fin k) (t : ℝ) (x : F 0) :
    w + t • (Pi.single i x : Fin k → F 0) = update w i (w i + t • x) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

variable {Ω : (F.whitney k) 0 → ℝ}
  (hΩ : IsSc1 (F := ScBanach.const ℝ) (F.whitneySet k V) Ω)
  (hA : ∀ z ∈ F.lvlSet V 1, ∃ a : MultilinearMap ℝ (fun _ : Fin k => F 0) ℝ,
    ∀ v, Ω (ScBanach.whitneyMk z v) = a v)
  {p : (F.whitney k) 1} (hp : p ∈ (F.whitney k).lvlSet (F.whitneySet k V) 1)

include hΩ hA hp

/-- The derivative along a fibre direction `(0, single i x)` with `x ∈ F₁`. -/
lemma scDeriv_whitney_fiber_single_one (i : Fin k) (x : F 1) :
    scDeriv (F := ScBanach.const ℝ) (F.whitneySet k V) Ω p
        ((0, F.fiberPackL 0 k (Pi.single i (F.toBase 1 x))) : (F.whitney k) 0) =
      Ω (ScBanach.whitneyMk (F.shift.toBase 1 p.1)
        (update (ScBanach.whitneyVec ((F.whitney k).toBase 1 p)) i (F.toBase 1 x))) := by
  classical
  set z := F.shift.toBase 1 p.1
  set w := ScBanach.whitneyVec ((F.whitney k).toBase 1 p)
  have hz : z ∈ F.lvlSet V 1 := mem_whitneySet_lvl_one.1 hp
  obtain ⟨a, ha⟩ := hA z hz
  set S := (F.whitney k).lvlSet (F.whitneySet k V) 1
  set e : (F.whitney k) 1 := (0, F.fiberPackL 1 k (Pi.single i x))
  have he : (F.whitney k).toBase 1 e =
      ((0, F.fiberPackL 0 k (Pi.single i (F.toBase 1 x))) : (F.whitney k) 0) := by
    rw [ScBanach.prod_toBase, map_zero, fiberPow_toBase_fiberPackL]
    congr 2
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  -- the line through `p` in the direction `e`
  set ℓ : ℝ → (F.whitney k) 1 := fun t => p + t • e
  have hℓ : ∀ t, (F.whitney k).toBase 1 (ℓ t) =
      ScBanach.whitneyMk z (w + t • (Pi.single i (F.toBase 1 x) : Fin k → F 0)) := fun t => by
    simp only [ℓ, map_add, map_smul, he]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]
      exact whitney_toBase_fst p
    · change ((F.whitney k).toBase 1 p).2 + t • F.fiberPackL 0 k (Pi.single i (F.toBase 1 x)) =
        F.fiberPackL 0 k (w + t • (Pi.single i (F.toBase 1 x) : Fin k → F 0))
      rw [map_add, map_smul, ScBanach.fiberPackL_fiberVecL]
  have hℓS : MapsTo ℓ univ S := fun t _ => by
    rw [ScBanach.mem_lvlSet, hℓ t, ScBanach.mem_whitneySet]; exact hz
  have h1 := hΩ.isSc1With_scDeriv.hasFDerivWithinAt p hp
  have h2 : HasDerivAt ℓ e 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add p
    simpa only [id, one_smul] using this
  have h3 := h1.comp_hasDerivWithinAt_of_eq (0 : ℝ) h2.hasDerivWithinAt hℓS (by simp [ℓ])
  -- the function along the line is affine
  set c := a (update w i (F.toBase 1 x))
  have hfun : ((Ω ∘ (F.whitney k).toBase 1) ∘ ℓ) = fun t => a w + t * c := by
    funext t
    simp only [Function.comp_apply, hℓ t, ha, add_smul_single_eq_update, a.map_update_add,
      a.map_update_smul, update_eq_self, smul_eq_mul, c]
  have h4 : HasDerivAt (fun t : ℝ => a w + t * c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add (a w)
  rw [hfun] at h3
  have huniq := (hasDerivWithinAt_univ.1 h3).unique h4
  simp only [ContinuousLinearMap.comp_apply, he] at huniq
  rw [huniq, ha]

/-- **The derivative of a fibrewise multilinear map along the fibre**: for `p ∈ (⊕ₖ TV)₁` over
`z` with vectors `w`, `DΩ(p)(0, single i x) = Ω(z, w with x in place i)`. -/
theorem scDeriv_whitney_fiber_single (i : Fin k) (x : F 0) :
    scDeriv (F := ScBanach.const ℝ) (F.whitneySet k V) Ω p
        ((0, F.fiberPackL 0 k (Pi.single i x)) : (F.whitney k) 0) =
      Ω (ScBanach.whitneyMk (F.shift.toBase 1 p.1)
        (update (ScBanach.whitneyVec ((F.whitney k).toBase 1 p)) i x)) := by
  classical
  set z := F.shift.toBase 1 p.1
  set w := ScBanach.whitneyVec ((F.whitney k).toBase 1 p)
  have hz : z ∈ F.lvlSet V 1 := mem_whitneySet_lvl_one.1 hp
  have hcont0 : ContinuousOn Ω (F.whitneySet k V) := by
    exact (hΩ.isSc0.continuousOn 0).congr fun q _ =>
      (levelMap_zero (E := F.whitney k) (F := ScBanach.const ℝ) Ω q).symm
  have hL : Continuous fun x : F 0 => scDeriv (F := ScBanach.const ℝ) (F.whitneySet k V) Ω p
      ((0, F.fiberPackL 0 k (Pi.single i x)) : (F.whitney k) 0) := by
    have : Continuous fun x : F 0 => ((0, F.fiberPackL 0 k (Pi.single i x)) : (F.whitney k) 0) :=
      continuous_const.prodMk ((F.fiberPackL 0 k).continuous.comp
        (continuous_single (A := fun _ : Fin k => F 0) i))
    exact (scDeriv (F := ScBanach.const ℝ) (F.whitneySet k V) Ω p).continuous.comp this
  have hR : Continuous fun x : F 0 => Ω (ScBanach.whitneyMk z (update w i x)) := by
    refine hcont0.comp_continuous (continuous_const.prodMk ((F.fiberPackL 0 k).continuous.comp
      (continuous_const.update i continuous_id))) fun x => ?_
    exact ScBanach.mem_whitneySet.2 hz
  have := (F.denseRange_inclK 0 1 : DenseRange (F.toBase 1)).equalizer hL hR
    (funext fun x => scDeriv_whitney_fiber_single_one hΩ hA hp i x)
  exact congrFun this x

/-- **The fibre part of the derivative**:
`DΩ(p)(0, u) = Σᵢ Ω(z, w₁, …, uᵢ, …, w_k)`. -/
theorem scDeriv_whitney_fiber (u : Fin k → F 0) :
    scDeriv (F := ScBanach.const ℝ) (F.whitneySet k V) Ω p
        ((0, F.fiberPackL 0 k u) : (F.whitney k) 0) =
      ∑ i, Ω (ScBanach.whitneyMk (F.shift.toBase 1 p.1)
        (update (ScBanach.whitneyVec ((F.whitney k).toBase 1 p)) i (u i))) := by
  classical
  have hu : ((0, F.fiberPackL 0 k u) : (F.whitney k) 0) =
      ∑ i, ((0, F.fiberPackL 0 k (Pi.single i (u i))) : (F.whitney k) 0) := by
    conv_lhs => rw [← Finset.univ_sum_single u]
    rw [map_sum]
    refine Prod.ext ?_ ?_ <;> simp [Prod.fst_sum, Prod.snd_sum]
  rw [hu, map_sum]
  exact Finset.sum_congr rfl fun i _ => scDeriv_whitney_fiber_single hΩ hA hp i (u i)

end Fiber

/-! ### The cancellation of the second derivatives -/

section Cancel

variable {M P : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup P] [Module ℝ P]

/-- `a(L w₁, …, x at i, …, L w_k) = (-1)^i a(x, L w₁, …, (no i), …)`. -/
lemma alt_update_eq {n : ℕ} (a : P [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ) (L : M →ₗ[ℝ] P) (w : Fin (n + 1) → M)
    (i : Fin (n + 1)) (x : P) :
    a (update (fun l => L (w l)) i x) =
      (-1 : ℝ) ^ (i : ℕ) * a (Matrix.vecCons x fun l => L (i.removeNth w l)) := by
  rw [← Fin.insertNth_removeNth, AlternatingMap.map_insertNth]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rfl

/-- **The cancellation behind `d(f^*ω) = f^*dω`**: for an alternating `a`, a linear `L` and a
symmetric bilinear `S`,
`Σⱼ (-1)ʲ Σᵢ a(L w₁, …, S(wᵢ, hⱼ), …, L w_k) = 0`, `w = (h₀, …, ĥⱼ, …, h_k)`. -/
theorem sum_update_symm_eq_zero {k : ℕ} (a : P [⋀^Fin k]→ₗ[ℝ] ℝ) (L : M →ₗ[ℝ] P)
    (S : M →ₗ[ℝ] M →ₗ[ℝ] P) (hS : ∀ u v, S u v = S v u) (h : Fin (k + 1) → M) :
    ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) * ∑ i : Fin k,
      a (update (fun l => L (j.removeNth h l)) i (S (j.removeNth h i) (h j))) = 0 := by
  cases k with
  | zero => simp
  | succ n =>
    let B : M →ₗ[ℝ] M →ₗ[ℝ] M [⋀^Fin n]→ₗ[ℝ] ℝ :=
      LinearMap.mk₂ ℝ (fun u v => (a.curryLeft (S u v)).compLinearMap L)
        (fun u u' v => by ext w; simp [AlternatingMap.curryLeft_apply_apply])
        (fun c u v => by ext w; simp [AlternatingMap.curryLeft_apply_apply])
        (fun u v v' => by ext w; simp [AlternatingMap.curryLeft_apply_apply])
        (fun c u v => by ext w; simp [AlternatingMap.curryLeft_apply_apply])
    have hB : ∀ u v, B u v = B v u := fun u v => by
      ext w; simp [B, hS u v]
    have h0 := congrArg (fun T => T h)
      (AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric hB)
    simp only [AlternatingMap.alternatizeUncurryFin_apply, LinearMap.coe_comp, comp_apply,
      AlternatingMap.alternatizeUncurryFinLM_apply, AlternatingMap.zero_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [alt_update_eq, hS]
    simp [B, AlternatingMap.curryLeft_apply_apply, Fin.removeNth]

end Cancel

/-! ### The derivative of `⊕ₖ Tf` -/

namespace ScBanach

variable (E) in
/-- The `i`-th vector `h ↦ hᵢ` of `E^k`, an sc-operator `E^k → E`. -/
def fiberProj (k : ℕ) (i : Fin k) : ScOperator (E.fiberPow k) E where
  lvl m := (ContinuousLinearMap.proj i).comp (E.fiberVecL m k)
  incl_comm _ q := (fiberVecL_incl q i).symm

lemma fiberProj_apply {k : ℕ} (i : Fin k) (m : ℕ) (q : (E.fiberPow k) m) :
    E.fiberProj k i m q = E.fiberVecL m k q i := rfl

variable (E) in
/-- `(y, h₁, …, h_k) ↦ (y, hᵢ)`, an sc-operator `E¹ ⊕ E^k → TE`. -/
def whitneyPick (k : ℕ) (i : Fin k) : ScOperator (E.whitney k) E.tangent where
  lvl m := (ContinuousLinearMap.id ℝ (E (m + 1))).prodMap ((E.fiberProj k i) m)
  incl_comm m q := Prod.ext rfl ((E.fiberProj k i).incl_comm m q.2)

lemma whitneyPick_apply {k : ℕ} (i : Fin k) (m : ℕ) (q : (E.whitney k) m) :
    E.whitneyPick k i m q = ((q.1, E.fiberVecL m k q.2 i) : E.tangent m) := rfl

end ScBanach

section WhitneyDeriv

variable {C U : Set (E 0)} {f : E 0 → F 0} {k : ℕ}

lemma whitneyMap_eq_scPair (U : Set (E 0)) (f : E 0 → F 0) (k : ℕ) :
    whitneyMap U f k = scPair ((levelMap f 1 : E.shift 0 → F.shift 0) ∘
      ScBanach.prodFstOp E.shift (E.fiberPow k) 0) (whitneyFib U f k) := rfl

lemma fiberProj_comp_whitneyFib (U : Set (E 0)) (f : E 0 → F 0) (k : ℕ) (i : Fin k) :
    F.fiberProj k i 0 ∘ whitneyFib U f k =
      ScBanach.prodSndOp F.shift F 0 ∘ (tangentMap U f ∘ E.whitneyPick k i 0) :=
  funext fun q => whitneyVec_whitneyFib U f k q i

variable (hU : IsRelOpenInQuadrant E C U) (hf : IsScSmooth U f)
include hU hf

/-- The fibre vectors of `D(⊕ₖ Tf)(p)v` are the second components of `D(Tf)(y, hᵢ)(vᵢ)`. -/
theorem fiberVecL_scDeriv_whitneyFib {p : (E.whitney k) 1}
    (hp : p ∈ (E.whitney k).lvlSet (E.whitneySet k U) 1) (v : (E.whitney k) 0) (i : Fin k) :
    F.fiberVecL 0 k (scDeriv (E.whitneySet k U) (whitneyFib U f k) p v) i =
      (scDeriv (E.tangentSet U) (tangentMap U f) (E.whitneyPick k i 1 p)
        (E.whitneyPick k i 0 v)).2 := by
  have hS := (hU.whitneySet k).isScDomain
  have hT := hU.isScDomain.tangentSet
  have hFib : IsSc1 (E.whitneySet k U) (whitneyFib U f k) := ((hf.whitneyFib hU k) 1).1
  have hTf : IsSc1 (E.tangentSet U) (tangentMap U f) := ((isScSmooth_iff.1 hf).2 1).1
  have hπ : IsSc1 (E.whitneySet k U) (E.whitneyPick k i 0) :=
    ((E.whitneyPick k i).isScSmooth hS 1).1
  have hπT : MapsTo (E.whitneyPick k i 0) (E.whitneySet k U) (E.tangentSet U) := fun q hq =>
    (ScBanach.mem_whitneySet.1 hq : _)
  have h1 := scDeriv_comp hS (isScDomain_univ _) hFib
    (((F.fiberProj k i).isScSmooth (isScDomain_univ _) 1).1) (mapsTo_univ _ _) hp
  rw [ScOperator.scDeriv_eq _ (isScDomain_univ _) (mem_univ _),
    fiberProj_comp_whitneyFib] at h1
  have h2 := scDeriv_comp hS (isScDomain_univ _) (theorem_1_3_1' hS hT hπ hTf hπT).1
    (((ScBanach.prodSndOp F.shift F).isScSmooth (isScDomain_univ _) 1).1) (mapsTo_univ _ _) hp
  rw [ScOperator.scDeriv_eq _ (isScDomain_univ _) (mem_univ _),
    scDeriv_comp hS hT hπ hTf hπT hp, ScOperator.scDeriv_eq _ hS hp,
    ScOperator.levelMap_eq] at h2
  exact congrArg (fun L => L v) (h1.symm.trans h2)

/-- **The derivative of `⊕ₖ Tf`** at `p = (y, w)` of level `1`:
`D(⊕ₖ Tf)(p)(η, u) = (Df¹(y)η, D(whitneyFib)(p)(η, u))`. -/
theorem scDeriv_whitneyMap_apply {p : (E.whitney k) 1}
    (hp : p ∈ (E.whitney k).lvlSet (E.whitneySet k U) 1) (v : (E.whitney k) 0) :
    scDeriv (E.whitneySet k U) (whitneyMap U f k) p v =
      (scDeriv (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) p.1 v.1,
        scDeriv (E.whitneySet k U) (whitneyFib U f k) p v) := by
  have hS := (hU.whitneySet k).isScDomain
  have hf1 : IsSc1 (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) :=
    ((hf.shift hU.isScDomain) 1).1
  have hfst : IsSc1 (E.whitneySet k U) (ScBanach.prodFstOp E.shift (E.fiberPow k) 0) :=
    ((ScBanach.prodFstOp E.shift (E.fiberPow k)).isScSmooth hS 1).1
  have hmaps : MapsTo (ScBanach.prodFstOp E.shift (E.fiberPow k) 0) (E.whitneySet k U)
      (E.lvlSet U 1) := fun q hq => (ScBanach.mem_whitneySet.1 hq : _)
  rw [whitneyMap_eq_scPair, scDeriv_scPair (hU.whitneySet k)
    (theorem_1_3_1' hS hU.isScDomain.shift hfst hf1 hmaps).1 ((hf.whitneyFib hU k) 1).1 hp,
    scDeriv_comp hS hU.isScDomain.shift hfst hf1 hmaps hp, ScOperator.scDeriv_eq _ hS hp,
    ScOperator.levelMap_eq]
  rfl

/-- **The derivative of `⊕ₖ Tf` in a base direction**:
`D(⊕ₖ Tf)(y, w)(η, 0) = (Df¹(y)η, 0) + (0, D²f(y)(w₁, η), …, D²f(y)(w_k, η))`. -/
theorem scDeriv_whitneyMap_whitneyMk {p : (E.whitney k) 1}
    (hp : p ∈ (E.whitney k).lvlSet (E.whitneySet k U) 1) (η : E 1) :
    scDeriv (E.whitneySet k U) (whitneyMap U f k) p (ScBanach.whitneyMk η 0) =
      ScBanach.whitneyMk (E := F)
          (scDeriv (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) p.1 η) 0 +
        ((0, F.fiberPackL 0 k fun i => scSecondDeriv U f p.1 (E.fiberVecL 1 k p.2 i) η) :
          (F.whitney k) 0) := by
  rw [scDeriv_whitneyMap_apply hU hf hp]
  refine Prod.ext (by simp) ?_
  refine ScBanach.fiberVecL_injective (funext fun i => ?_)
  rw [fiberVecL_scDeriv_whitneyFib hU hf hp, ScBanach.whitneyPick_apply,
    ScBanach.whitneyPick_apply]
  simp only [Prod.snd_add, ScBanach.fiberVecL_fiberPackL, map_zero,
    Pi.zero_apply, zero_add]
  rfl

end WhitneyDeriv

/-! ### Naturality of the local exterior derivative -/

section Naturality

variable {C U : Set (E 0)} {C' V : Set (F 0)} {f : E 0 → F 0} {k : ℕ}

lemma whitney_toBase_mk (y : E.shift 1) (v : Fin k → E 1) :
    (E.whitney k).toBase 1 ((y, E.fiberPackL 1 k v) : (E.whitney k) 1) =
      ScBanach.whitneyMk (E.shift.toBase 1 y) fun i => E.toBase 1 (v i) := by
  rw [ScBanach.prod_toBase, fiberPow_toBase_fiberPackL]

lemma mapsTo_whitneyMap (hf : IsSc0 E F U f) (hfV : MapsTo f U V) (k : ℕ) :
    MapsTo (whitneyMap U f k) (E.whitneySet k U) (F.whitneySet k V) := fun _ hq =>
  ScBanach.mem_whitneySet.2 (hf.levelMap_mapsTo hfV 1 (ScBanach.mem_whitneySet.1 hq))

/-- `ι(Df¹(y)a) = Df(y)(ιa)` for `y ∈ U₂`, `a ∈ E₁`. -/
lemma toBase_scDeriv_levelMap (hU : IsScDomain E U) (hf : IsSc1 U f) {y : E.shift 1}
    (hy : y ∈ E.shift.lvlSet (E.lvlSet U 1) 1) (a : E 1) :
    F.toBase 1 (scDeriv (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) y a) =
      scDeriv U f (E.shift.toBase 1 y) (E.toBase 1 a) := by
  rw [IsSc1.scDeriv_eqOn (hf.isSc1With_scDeriv.shift hU) (hU.shift.uniqueDiffWithinAt 1) hy]
  exact hf.isSc1With_scDeriv.toBase_levelDeriv (E.mem_lvlSet_shift_toBase.1 hy) a

lemma scSecondDeriv_add_right (z : E.shift 1) (a b b' : E 1) :
    scSecondDeriv U f z a (b + b') = scSecondDeriv U f z a b + scSecondDeriv U f z a b' := by
  unfold scSecondDeriv
  rw [show ((b + b', 0) : E.tangent 0) = (b, 0) + (b', 0) by simp, map_add]
  rfl

lemma scSecondDeriv_smul_right (z : E.shift 1) (a b : E 1) (c : ℝ) :
    scSecondDeriv U f z a (c • b) = c • scSecondDeriv U f z a b := by
  unfold scSecondDeriv
  rw [show ((c • b, 0) : E.tangent 0) = c • (b, 0) by simp, map_smul]
  rfl

/-- The second derivative `D²f(y)` at `y ∈ U₂` as a bilinear map on `E₁` (linear in the first
argument by the symmetry, `scSecondDeriv_symm`). -/
def scSecondDerivBilin (hU : IsRelOpenInQuadrant E C U) (hf : IsSck 2 E F U f) {y : E.shift 1}
    (hy : y ∈ E.lvlSet U 2) : E 1 →ₗ[ℝ] E 1 →ₗ[ℝ] F 0 :=
  LinearMap.mk₂ ℝ (fun a b => scSecondDeriv U f y a b)
    (fun a a' b => by
      rw [scSecondDeriv_symm hU hf hy, scSecondDeriv_symm hU hf hy a,
        scSecondDeriv_symm hU hf hy a', scSecondDeriv_add_right])
    (fun c a b => by
      rw [scSecondDeriv_symm hU hf hy, scSecondDeriv_symm hU hf hy a, scSecondDeriv_smul_right])
    (fun a b b' => scSecondDeriv_add_right y a b b')
    (fun c a b => scSecondDeriv_smul_right y a b c)

lemma scSecondDerivBilin_apply (hU : IsRelOpenInQuadrant E C U) (hf : IsSck 2 E F U f)
    {y : E.shift 1} (hy : y ∈ E.lvlSet U 2) (a b : E 1) :
    scSecondDerivBilin hU hf hy a b = scSecondDeriv U f y a b := rfl

/-- **Naturality of the local exterior derivative** (2021 p. 197): for `f : U → V` sc-smooth
between relatively open subsets of partial quadrants and an sc-form `Ω` on `V`,
`d(Ω ∘ ⊕ₖ Tf) = dΩ ∘ ⊕_{k+1} Tf¹` on `⊕_{k+1} T(U¹)`.  The second derivatives of `f` cancel by
their symmetry (`scSecondDeriv_symm`, `sum_update_symm_eq_zero`). -/
theorem ambientD_comp_whitneyMap (hU : IsRelOpenInQuadrant E C U)
    (hV : IsRelOpenInQuadrant F C' V) (hf : IsScSmooth U f) (hfV : MapsTo f U V)
    {Ω : (F.whitney k) 0 → ℝ} (hΩ : IsAmbientScForm F V k Ω)
    {q : (E.shift.whitney (k + 1)) 0} (hq : q ∈ E.shift.whitneySet (k + 1) (E.lvlSet U 1)) :
    ambientD U (Ω ∘ whitneyMap U f k) q =
      ambientD V Ω (whitneyMap (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1)
        (k + 1) q) := by
  classical
  set y := q.1
  set h := ScBanach.whitneyVec q
  have hy : y ∈ E.shift.lvlSet (E.lvlSet U 1) 1 := ScBanach.mem_whitneySet.1 hq
  have hy2 : y ∈ E.lvlSet U 2 := E.mem_lvlSet_shift_toBase.1 hy
  have hS := (hU.whitneySet k).isScDomain
  have hSV := (hV.whitneySet k).isScDomain
  have hG : IsSc1 (E.whitneySet k U) (whitneyMap U f k) := ((hf.whitneyMap hU k) 1).1
  have hG0 : IsSc0 _ _ (E.whitneySet k U) (whitneyMap U f k) := (hf.whitneyMap hU k) 0
  have hGV := mapsTo_whitneyMap (hf 0) hfV k
  have hΩ1 : IsSc1 (F := ScBanach.const ℝ) (F.whitneySet k V) Ω := (hΩ.isScSmooth 1).1
  have hA : ∀ z ∈ F.lvlSet V 1, ∃ a : MultilinearMap ℝ (fun _ : Fin k => F 0) ℝ,
      ∀ v, Ω (ScBanach.whitneyMk z v) = a v := fun z hz => by
    obtain ⟨a, ha⟩ := hΩ.alternating z hz
    exact ⟨a.toMultilinearMap, ha⟩
  set z₀ : E 1 := E.shift.toBase 1 y
  set z : F 1 := levelMap f 1 z₀
  have hz : z ∈ F.lvlSet V 1 := (hf 0).levelMap_mapsTo hfV 1 hy
  obtain ⟨a, ha⟩ := hΩ.alternating z hz
  let L : E 1 →ₗ[ℝ] F 0 := ((scDeriv U f z₀).comp (E.toBase 1) : E 1 →L[ℝ] F 0)
  let S := scSecondDerivBilin hU (hf 2) hy2
  let p : Fin (k + 1) → (E.whitney k) 1 := fun j => (y, E.fiberPackL 1 k (j.removeNth h))
  have hp : ∀ j, p j ∈ (E.whitney k).lvlSet (E.whitneySet k U) 1 := fun j =>
    mem_whitneySet_lvl_one.2 hy
  have hbase : ∀ j, (F.whitney k).toBase 1 (levelMap (whitneyMap U f k) 1 (p j)) =
      ScBanach.whitneyMk z fun i => L (j.removeNth h i) := fun j => by
    rw [hG0.toBase_levelMap (hp j), whitney_toBase_mk, whitneyMap_eq_mk, ScBanach.whitneyVec_mk]
    rfl
  set Q := whitneyMap (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) (k + 1) q
    with hQ
  have hQv : ∀ i, ScBanach.whitneyVec Q i =
      scDeriv (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) y (h i) := fun i =>
    whitneyVec_whitneyMap _ _ _ _ i
  have hP : ∀ j, levelMap (whitneyMap U f k) 1 (p j) =
      (Q.1, F.fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec Q))) := fun j => by
    apply (F.whitney k).toBase_injective 1
    rw [hbase j, whitney_toBase_mk]
    refine Prod.ext ?_ (congrArg (F.fiberPackL 0 k) (funext fun i => ?_))
    · change z = F.shift.toBase 1 (levelMap (E := E.shift) (F := F.shift) (levelMap f 1) 1 y)
      rw [((hf.shift hU.isScDomain) 0).toBase_levelMap hy]
    · change L (j.removeNth h i) = F.toBase 1 (ScBanach.whitneyVec Q (j.succAbove i))
      rw [hQv, toBase_scDeriv_levelMap hU.isScDomain (hf 1).1 hy]
      rfl
  have hterm : ∀ j : Fin (k + 1),
      scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) (Ω ∘ whitneyMap U f k) (p j)
          (ScBanach.whitneyMk (h j) 0) =
        scDeriv (F := ScBanach.const ℝ) (F.whitneySet k V) Ω
            (Q.1, F.fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec Q)))
            (ScBanach.whitneyMk (ScBanach.whitneyVec Q j) 0) +
          ∑ i, a (update (fun l => L (j.removeNth h l)) i (S (j.removeNth h i) (h j))) := by
    intro j
    rw [scDeriv_comp hS hSV hG hΩ1 hGV (hp j), ContinuousLinearMap.comp_apply,
      scDeriv_whitneyMap_whitneyMk hU hf (hp j), map_add]
    congr 1
    · rw [hP j, hQv]
    · rw [scDeriv_whitney_fiber hΩ1 hA (hG0.levelMap_mapsTo hGV 1 (hp j)), ← whitney_toBase_fst]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbase j, ScBanach.whitneyVec_mk, ha]
      simp [p, S, scSecondDerivBilin_apply]
  rw [ambientD_apply, ambientD_apply]
  rw [show (∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
      scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) (Ω ∘ whitneyMap U f k)
        (q.1, E.fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec q)))
        (ScBanach.whitneyMk (ScBanach.whitneyVec q j) 0)) =
      ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) * (scDeriv (F := ScBanach.const ℝ) (F.whitneySet k V) Ω
            (Q.1, F.fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec Q)))
            (ScBanach.whitneyMk (ScBanach.whitneyVec Q j) 0) +
          ∑ i, a (update (fun l => L (j.removeNth h l)) i (S (j.removeNth h i) (h j)))) from
    Finset.sum_congr rfl fun j _ => by rw [← hterm j]]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_update_symm_eq_zero a L S (fun u v => scSecondDeriv_symm hU (hf 2) hy2 u v) h, add_zero]

end Naturality

/-! ### The local exterior derivative on a retract: congruence, naturality, independence -/

section Retract

variable {C O : Set (E 0)} {C' O' : Set (F 0)} {k : ℕ}

/-- `ambientD U Ω` depends only on the values of `Ω` on `⊕ₖ TU`. -/
theorem ambientD_congr {U : Set (E 0)} (hU : IsScDomain (E.whitney k) (E.whitneySet k U))
    {Ω Ω' : (E.whitney k) 0 → ℝ} (hΩ : IsSc1 (F := ScBanach.const ℝ) (E.whitneySet k U) Ω)
    (h : EqOn Ω Ω' (E.whitneySet k U)) {q : (E.shift.whitney (k + 1)) 0}
    (hq : q ∈ E.shift.whitneySet (k + 1) (E.lvlSet U 1)) :
    ambientD U Ω' q = ambientD U Ω q := by
  have hp : ∀ j : Fin (k + 1),
      ((q.1, E.fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec q))) : (E.whitney k) 1) ∈
        (E.whitney k).lvlSet (E.whitneySet k U) 1 := fun _ =>
    mem_whitneySet_lvl_one.2 (ScBanach.mem_whitneySet.1 hq)
  rw [ambientD_apply, ambientD_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [scDeriv_congr hU hΩ h (hp j)]

/-- `⊕ₖ Tr` maps `⊕ₖ TU` into `⊕ₖ TO`. -/
lemma ScRetraction.whitney_mem (R : ScRetraction E C) {q : (E.whitney k) 0}
    (hq : q ∈ E.whitneySet k R.U) : R.whitney k q ∈ retractWhitney E C R.retract k := by
  rw [← R.whitney_retract]; exact (R.whitney k).apply_mem_retract hq

/-- A retraction-level point of `⊕_{k+1} T(O¹)` lies in `⊕_{k+1} T(U¹)`. -/
lemma ScRetraction.mem_whitneySet_of_mem (R : ScRetraction E C) {q : (E.shift.whitney (k + 1)) 0}
    (hq : q ∈ retractWhitney E.shift (E.lvlSet C 1) (E.lvlSet R.retract 1) (k + 1)) :
    q ∈ E.shift.whitneySet (k + 1) (E.lvlSet R.U 1) :=
  ScBanach.mem_whitneySet.2 (E.lvlSet_mono R.retract_subset 2 hq.1)

/-- `⊕ₖ Tg` depends only on `g` on `U`. -/
lemma whitneyMap_congr {U : Set (E 0)} (hU : IsScDomain E U) {g g' : E 0 → F 0} (hg : IsSc1 U g)
    (h : EqOn g g' U) {q : (E.whitney k) 0} (hq : q.1 ∈ E.lvlSet U 1) :
    whitneyMap U g' k q = whitneyMap U g k q := by
  rw [whitneyMap_eq_mk, whitneyMap_eq_mk, scDeriv_congr hU hg h hq, IsSc0.levelMap_congr h hq]

/-- **`retractD` depends only on the form on `⊕ₖ TO`.** -/
theorem retractD_congr (R : ScRetraction E C) {ω ω' : (E.whitney k) 0 → ℝ}
    (hω : IsRetractScForm E C R.retract k ω) (h : EqOn ω ω' (retractWhitney E C R.retract k))
    {q : (E.shift.whitney (k + 1)) 0} (hq : q ∈ E.shift.whitneySet (k + 1) (E.lvlSet R.U 1)) :
    retractD R ω' q = retractD R ω q :=
  ambientD_congr (R.relOpen.whitneySet k).isScDomain
    ((hω.isAmbientScForm_comp R).isScSmooth 1).1 (fun _ hq' => h (R.whitney_mem hq')) hq

/-- `TO' ⊆ TO` for sc-retracts `O' ⊆ O`. -/
theorem retractTangent_mono (hO : IsScRetract E C O) {O₁ : Set (E 0)} (hO₁ : IsScRetract E C O₁)
    (hsub : O₁ ⊆ O) : retractTangent E C O₁ ⊆ retractTangent E C O := fun p hp => by
  have h := ((isScSmoothRetractMap_id O).mono_source hO hsub).tangentMap_mapsTo hO₁ hO hp
  rwa [retractTangentMap_id hO₁ (fun _ _ => rfl) hp] at h

lemma retractWhitney_mono (hO : IsScRetract E C O) {O₁ : Set (E 0)} (hO₁ : IsScRetract E C O₁)
    (hsub : O₁ ⊆ O) : retractWhitney E C O₁ k ⊆ retractWhitney E C O k := fun _ hq =>
  ⟨E.lvlSet_mono hsub 1 hq.1, fun i => retractTangent_mono hO hO₁ hsub (hq.2 i)⟩

/-- **An sc-form restricts to a sub-retract.** -/
theorem IsRetractScForm.mono {ω : (E.whitney k) 0 → ℝ} (hω : IsRetractScForm E C O k ω)
    (hO : IsScRetract E C O) {O₁ : Set (E 0)} (hO₁ : IsScRetract E C O₁) (hsub : O₁ ⊆ O) :
    IsRetractScForm E C O₁ k ω where
  isScSmooth := hω.isScSmooth.mono_source (hO.whitney k) (retractWhitney_mono hO hO₁ hsub)
  alternating x hx := by
    obtain ⟨a, ha⟩ := hω.alternating x (E.lvlSet_mono hsub 1 hx)
    exact ⟨a, fun v hv => ha v fun i => retractTangent_mono hO hO₁ hsub (hv i)⟩

/-- `⊕ₖ Tg = id` on `⊕ₖ TO` for `g = id` on `O`. -/
lemma retractWhitneyMap_eq_self (hO : IsScRetract E C O) {g : E 0 → E 0} (hg : EqOn g _root_.id O)
    {q : (E.whitney k) 0} (hq : q ∈ retractWhitney E C O k) :
    retractWhitneyMap E C O g k q = q := by
  conv_rhs => rw [← whitneyMk_fst_vec q]
  refine Prod.ext ?_ (congrArg (E.fiberPackL 0 k) (funext fun i => ?_))
  · exact levelMap_eq_of_toBase_eq (hg hq.1).symm
  · exact congrArg Prod.snd (retractTangentMap_id hO hg (hq.2 i))

/-- **Naturality of the local exterior derivative on retracts** (2021 p. 197): for `f : O → O'`
sc-smooth between sc-retracts with retractions `r`, `r'` and an sc-form `ω` on `O'`,
`d_r(ω ∘ ⊕ₖ Tf) = d_{r'}ω ∘ ⊕_{k+1} Tf¹` on `⊕_{k+1} T(O¹)`. -/
theorem retractD_comp_retractWhitneyMap (R : ScRetraction E C) (hR : R.retract = O)
    (R' : ScRetraction F C') (hR' : R'.retract = O') {f : E 0 → F 0}
    (hf : IsScSmoothRetractMap E C O F C' O' f) {ω : (F.whitney k) 0 → ℝ}
    (hω : IsRetractScForm F C' O' k ω) {q : (E.shift.whitney (k + 1)) 0}
    (hq : q ∈ retractWhitney E.shift (E.lvlSet C 1) (E.lvlSet O 1) (k + 1)) :
    retractD R (ω ∘ retractWhitneyMap E C O f k) q =
      retractD R' ω (retractWhitneyMap E.shift (E.lvlSet C 1) (E.lvlSet O 1) (levelMap f 1)
        (k + 1) q) := by
  subst hR hR'
  set g := f ∘ R
  have hg : IsScSmooth R.U g := hf.comp_isScSmooth R rfl
  have hgV : MapsTo g R.U R'.U := fun y hy => R'.retract_subset (hf.mapsTo (R.apply_mem_retract hy))
  have hS := (R.relOpen.whitneySet k).isScDomain
  have hΩ := hω.isAmbientScForm_comp R'
  have hq' := R.mem_whitneySet_of_mem hq
  -- `ω ∘ ⊕ₖTf ∘ ⊕ₖTr = (ω ∘ ⊕ₖTr') ∘ ⊕ₖT(f ∘ r)` on `⊕ₖ TU`
  have heq : EqOn ((ω ∘ R'.whitney k) ∘ whitneyMap R.U g k)
      ((ω ∘ retractWhitneyMap E C R.retract f k) ∘ R.whitney k) (E.whitneySet k R.U) := by
    intro p hp
    have h1 := retractWhitneyMap_comp_whitney R hf k hp
    have h2 : whitneyMap R.U g k p ∈ retractWhitney F C' R'.retract k := by
      rw [← h1]
      exact (hf.whitney R.isScRetract R'.isScRetract k).mapsTo (R.whitney_mem hp)
    simp only [Function.comp_apply] at h1 ⊢
    rw [R'.whitney_apply, R'.whitneyMap_eq_self h2, ← h1]
  have hsc : IsSc1 (F := ScBanach.const ℝ) (E.whitneySet k R.U)
      ((ω ∘ R'.whitney k) ∘ whitneyMap R.U g k) :=
    (theorem_1_3_1' hS (R'.relOpen.whitneySet k).isScDomain ((hg.whitneyMap R.relOpen k) 1).1
      (hΩ.isScSmooth 1).1 (mapsTo_whitneyMap (hg 0) hgV k)).1
  have h3 : retractD R (ω ∘ retractWhitneyMap E C R.retract f k) q =
      ambientD R.U ((ω ∘ R'.whitney k) ∘ whitneyMap R.U g k) q :=
    ambientD_congr hS hsc heq hq'
  rw [h3, ambientD_comp_whitneyMap R.relOpen R'.relOpen hg hgV hΩ hq']
  -- `⊕_{k+1} T(f ∘ r)¹ = ⊕_{k+1} Tf¹` on `⊕_{k+1} T(O¹)`
  congr 1
  have hf1 := hf.shift R.isScRetract
  rw [← R.shift_retract] at hf1 hq
  have h4 := retractWhitneyMap_comp_whitney R.shift hf1 (k + 1) hq'
  have h5 : EqOn (levelMap (f ∘ R) 1) (levelMap f 1 ∘ R.shift) (E.lvlSet R.U 1) := fun y hy =>
    (hf.isSc0 R.isScRetract).levelMap_comp R.isSc1.isSc0 R.mapsTo_retract hy
  simp only [Function.comp_apply, R.shift.whitney_apply, R.shift.whitneyMap_eq_self hq] at h4
  rw [R.shift_retract] at h4
  rw [h4]
  exact (whitneyMap_congr R.isScDomain.shift ((hg.shift R.isScDomain) 1).1 h5
    (ScBanach.mem_whitneySet.1 hq')).symm

/-- **Independence of the retraction** (the step from the local `d` to `d` on an M-polyfold, 2021
p. 197): for a retraction `r` onto `O` and a retraction `r₁` onto a sub-retract `O₁ ⊆ O` (for
instance `O₁ = O`, or an open part `O ∩ W`), `d_{r₁}ω = d_rω` on `⊕_{k+1} T(O₁¹)`.  (Naturality
under the inclusion `O₁ → O`.) -/
theorem retractD_eq_of_subset (R : ScRetraction E C) (hR : R.retract = O) (R₁ : ScRetraction E C)
    {O₁ : Set (E 0)} (hR₁ : R₁.retract = O₁) (hsub : O₁ ⊆ O) {ω : (E.whitney k) 0 → ℝ}
    (hω : IsRetractScForm E C O k ω) {q : (E.shift.whitney (k + 1)) 0}
    (hq : q ∈ retractWhitney E.shift (E.lvlSet C 1) (E.lvlSet O₁ 1) (k + 1)) :
    retractD R₁ ω q = retractD R ω q := by
  have hO : IsScRetract E C O := hR ▸ R.isScRetract
  have hO₁ : IsScRetract E C O₁ := hR₁ ▸ R₁.isScRetract
  have hid : IsScSmoothRetractMap E C O₁ E C O _root_.id :=
    (isScSmoothRetractMap_id O).mono_source hO hsub
  have h1 := retractD_comp_retractWhitneyMap R₁ hR₁ R hR hid hω hq
  subst hR₁
  have h2 : retractD R₁ (ω ∘ retractWhitneyMap E C R₁.retract _root_.id k) q = retractD R₁ ω q :=
    retractD_congr R₁ (hω.mono hO hO₁ hsub)
      (fun p hp => by simp [retractWhitneyMap_eq_self hO₁ (fun _ _ => rfl) hp])
      (R₁.mem_whitneySet_of_mem hq)
  have h3 : retractWhitneyMap E.shift (E.lvlSet C 1) (E.lvlSet R₁.retract 1)
      (levelMap _root_.id 1) (k + 1) q = q :=
    retractWhitneyMap_eq_self hO₁.shift (g := levelMap (E := E) (F := E) _root_.id 1)
      (fun _ _ => levelMap_eq_of_toBase_eq rfl) hq
  rw [← h2, h1, h3]

end Retract

end Polyfold
