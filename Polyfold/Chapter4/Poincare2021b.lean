import Polyfold.Chapter4.Poincare2021
import Polyfold.Chapter4.Poincare448
import Polyfold.Chapter4.ScFormsNatural2021
import Polyfold.Chapter4.Characterization
import Polyfold.Chapter3.Germ

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.5.3, **Lemma 4.5.2**
(p. 202–203; the Poincaré lemma on a convex set).  Closes the part of gap G.80 on Lemma 4.5.2;
with `Poincare448.lean`, Lemma 4.4.8 (`lemma_4_4_8`).

# Lemma 4.5.2

## The text, paraphrased

(Lemma 4.5.2) Let `U ⊆ C` be relatively open and convex with `0 ∈ U`.  Every closed sc-form
`ω ∈ Ωᵏ(U)`, `k ≥ 1`, has a primitive: `dτ = ω` on `U¹` for some `τ ∈ Ωᵏ⁻¹(U)`, namely
`τ(y)(v₁, …, v_{k-1}) = ∫₀¹ t^{k-1} ω(ty)(y, v₁, …, v_{k-1}) dt`.

## What is formalized

* The homotopy operator in a local model, for a convex relatively open `D` of a partial
  quadrant `C ⊆ E` and a **smooth centre** `c ∈ D` (the text has `c = 0`):
  `τ(y)(v) = ∫₀¹ tᵏ ω(c + t(y − c))(y − c, v) dt` (`homotopyForm`).
* `lemma_4_5_2`: for `ω` sc-smooth on `⊕_{k+1} TD`, alternating on the fibres and closed
  (`d ω = 0` on `⊕_{k+2} T(D¹)`), `τ` is sc-smooth on `⊕ₖ TD`, alternating on the fibres, and
  `d τ = ω` on `⊕_{k+1} T(D¹)`.
* `ambientD_homotopyForm`: the homotopy formula `dτ = ω`, from closedness at
  `(c + t(y − c), y − c, h)` (`sum_scDeriv_poincareHomotopy_of_closed`), the alternation identity
  `sum_alternating_cons_removeNth` and the fundamental theorem of calculus for
  `t ↦ t^{k+1} ω(c + t(y − c))(h)` (`hasDerivWithinAt_poincarePrimitive`).
* `hasPoincare_relOpen`: Lemma 4.5.2 on the M-polyfold `O` of a convex relatively open local
  model (one chart `id`); the primitive is `relOpenForm`, with local representative `τ`.
* `localPoincare : LocalPoincare` (the statement used in `Poincare448.lean`), and
  `lemma_4_4_8 := lemma_4_4_8_of_local localPoincare` (2021 Lemma 4.4.8, p. 199).

## What the text leaves implicit, and the choices made

* The centre: the text takes `0 ∈ U`; in the proof of Lemma 4.4.8 the set is `B_δ(x) ∩ C` with
  `x` only of level `0`, so we allow any centre `c ∈ D ∩ E_∞` (`c` must be smooth for
  `t ↦ c + t(y − c)` to be sc-smooth).  `c = 0` is the case of the text.
* The sc-smoothness of `τ` (used without comment) is `isScSmooth_intervalIntegral`
  (`Poincare2021.lean`).
-/

open Set Function MeasureTheory

universe u

noncomputable section

namespace Polyfold

variable {E : ScBanach}

/-! ### Lifts of a smooth point -/

section Lift

variable {c : E 0} (hc : c ∈ E.smooth)

/-- A lift of the smooth point `c` to the level `m`. -/
def poincareLift (m : ℕ) : E m := (E.mem_smooth_iff.1 hc m).choose

@[simp] lemma toBase_poincareLift (m : ℕ) : E.toBase m (poincareLift hc m) = c :=
  (E.mem_smooth_iff.1 hc m).choose_spec

lemma poincareLift_zero : poincareLift hc 0 = c := toBase_poincareLift hc 0

lemma incl_poincareLift (m : ℕ) : E.incl m (poincareLift hc (m + 1)) = poincareLift hc m :=
  E.toBase_injective m (by rw [← ScScale.toBase_succ, toBase_poincareLift, toBase_poincareLift])

lemma shift_toBase_poincareLift (m : ℕ) :
    E.shift.toBase m (poincareLift hc (m + 1)) = poincareLift hc 1 :=
  E.toBase_injective 1 (by rw [← ScBanach.shift_toBase, toBase_poincareLift, toBase_poincareLift])

end Lift

/-! ### The homotopy `(t, y, v) ↦ (c + t(y − c), y − c, v)` -/

section Homotopy

variable {c : E 0} (hc : c ∈ E.smooth) {k : ℕ}

/-- The homotopy on level `m`: `(t, (y, v)) ↦ (c + t(y − c), (y − c, v))`, from
`ℝ ⊕ (E¹ ⊕ Eᵏ)` to `E¹ ⊕ E^{k+1}`. -/
def poincareHomotopyLvl (m : ℕ) (p : ((ScBanach.const ℝ).prod (E.whitney k)) m) :
    (E.whitney (k + 1)) m :=
  (poincareLift hc (m + 1) + p.1 • (p.2.1 - poincareLift hc (m + 1)),
    (E.incl m p.2.1 - poincareLift hc m, p.2.2))

lemma fiberPow_succ_toBase (m : ℕ) (a : E m) (b : (E.fiberPow k) m) :
    (E.fiberPow (k + 1)).toBase m ((a, b) : (E.prod (E.fiberPow k)) m) =
      ((E.toBase m a, (E.fiberPow k).toBase m b) : (E.prod (E.fiberPow k)) 0) :=
  ScBanach.prod_toBase E (E.fiberPow k) m (a, b)

lemma toBase_poincareHomotopyLvl (m : ℕ) (p : ((ScBanach.const ℝ).prod (E.whitney k)) m) :
    (E.whitney (k + 1)).toBase m (poincareHomotopyLvl hc m p) =
      poincareHomotopyLvl hc 0 (((ScBanach.const ℝ).prod (E.whitney k)).toBase m p) := by
  rw [ScBanach.prod_toBase, ScBanach.prod_toBase, ScBanach.prod_toBase E.shift (E.fiberPow k)]
  unfold poincareHomotopyLvl
  rw [fiberPow_succ_toBase]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · change E.shift.toBase m _ = poincareLift hc 1 + (ScBanach.const ℝ).toBase m p.1 •
      ((E.shift.toBase m p.2.1 : E 1) - poincareLift hc 1)
    rw [map_add, map_smul, map_sub, shift_toBase_poincareLift, ScBanach.const_toBase]
  · change E.toBase m (E.incl m p.2.1 - poincareLift hc m) =
      E.incl 0 (E.shift.toBase m p.2.1) - poincareLift hc 0
    rw [map_sub, toBase_poincareLift, poincareLift_zero, ← ScScale.toBase_succ,
      ScBanach.shiftScale_toBase]
    rfl

lemma contDiff_poincareHomotopyLvl (m : ℕ) :
    ContDiff ℝ ⊤ (fun p : ℝ × (E (m + 1) × (E.fiberPow k) m) =>
      ((poincareLift hc (m + 1) + p.1 • (p.2.1 - poincareLift hc (m + 1)),
        (E.incl m p.2.1 - poincareLift hc m, p.2.2)) :
          E (m + 1) × (E m × (E.fiberPow k) m))) := by
  fun_prop

/-- The homotopy on level `0`. -/
abbrev poincareHomotopy : ((ScBanach.const ℝ).prod (E.whitney k)) 0 → (E.whitney (k + 1)) 0 :=
  poincareHomotopyLvl hc 0

lemma levelMap_poincareHomotopy (m : ℕ) :
    levelMap (poincareHomotopy hc (k := k)) m = poincareHomotopyLvl hc m :=
  funext fun p => levelMap_eq_of_toBase_eq (toBase_poincareHomotopyLvl hc m p)

/-- **The homotopy is sc-smooth** (it is polynomial on every level). -/
theorem isScSmooth_poincareHomotopy {U : Set (((ScBanach.const ℝ).prod (E.whitney k)) 0)}
    (hU : IsScDomain _ U) : IsScSmooth U (poincareHomotopy hc (k := k)) := by
  refine IsScSmooth.of_contDiffOn_levels hU
    (fun m p _ => ⟨poincareHomotopyLvl hc m p, toBase_poincareHomotopyLvl hc m p⟩) fun m => ?_
  rw [levelMap_poincareHomotopy]
  exact ((contDiff_poincareHomotopyLvl hc m).of_le le_top).contDiffOn

end Homotopy

/-! ### Alternating integrands -/

/-- An integral over `[0, 1]` of alternating maps is alternating. -/
theorem exists_alternatingMap_intervalIntegral {M : Type} [AddCommGroup M] [Module ℝ M] {n : ℕ}
    {G : ℝ → (Fin n → M) → ℝ} (hG : ∀ t ∈ Icc (0 : ℝ) 1, ∃ a : M [⋀^Fin n]→ₗ[ℝ] ℝ, ∀ v, G t v = a v)
    (hint : ∀ v, IntervalIntegrable (fun t => G t v) volume 0 1) :
    ∃ a : M [⋀^Fin n]→ₗ[ℝ] ℝ, ∀ v, a v = ∫ t in (0 : ℝ)..1, G t v := by
  choose a ha using hG
  have hcongr : ∀ {F₁ F₂ : ℝ → ℝ}, (∀ t (ht : t ∈ Icc (0 : ℝ) 1), F₁ t = F₂ t) →
      ∫ t in (0 : ℝ)..1, F₁ t = ∫ t in (0 : ℝ)..1, F₂ t := fun h =>
    intervalIntegral.integral_congr fun t ht => h t (uIcc_zero_one ▸ ht)
  refine ⟨{ toFun := fun v => ∫ t in (0 : ℝ)..1, G t v
            map_update_add' := fun v i x y => ?_
            map_update_smul' := fun v i r x => ?_
            map_eq_zero_of_eq' := fun v i j hij hne => ?_ }, fun v => rfl⟩
  · rw [← intervalIntegral.integral_add (hint _) (hint _)]
    exact hcongr fun t ht => by
      rw [ha t ht, ha t ht, ha t ht]; exact (a t ht).map_update_add v i x y
  · rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    exact hcongr fun t ht => by
      rw [ha t ht, ha t ht, ← smul_eq_mul]; exact (a t ht).map_update_smul v i r x
  · change ∫ t in (0 : ℝ)..1, G t v = 0
    rw [hcongr (F₂ := fun _ => 0) fun t ht => by
      rw [ha t ht]; exact (a t ht).map_eq_zero_of_eq v hij hne]
    exact intervalIntegral.integral_zero

/-! ### The homotopy operator `τ` -/

section HomotopyForm

variable {c : E 0} (hc : c ∈ E.smooth) {k : ℕ} (ω : (E.whitney (k + 1)) 0 → ℝ)

/-- The integrand `tᵏ ω(c + t(y − c))(y − c, v)`. -/
def poincareIntegrand (p : ((ScBanach.const ℝ).prod (E.whitney k)) 0) : ℝ :=
  p.1 ^ k * ω (poincareHomotopy hc p)

/-- **The homotopy operator** (2021 p. 203): `τ(y)(v) = ∫₀¹ tᵏ ω(c + t(y − c))(y − c, v) dt`. -/
def homotopyForm (q : (E.whitney k) 0) : ℝ :=
  ∫ t in (0 : ℝ)..1, poincareIntegrand hc ω (t, q)

variable {C D : Set (E 0)} (hD : IsRelOpenInQuadrant E C D) (hconv : Convex ℝ D) (hcD : c ∈ D)

lemma toBase_poincareHomotopy_fst (p : ((ScBanach.const ℝ).prod (E.whitney k)) 0) :
    E.toBase 1 (poincareHomotopy hc p).1 = c + p.1 • (E.toBase 1 p.2.1 - c) := by
  change E.toBase 1 (poincareLift hc 1 + p.1 • (p.2.1 - poincareLift hc 1)) = _
  rw [map_add, map_smul, map_sub, toBase_poincareLift]

include hconv hcD in
lemma mapsTo_poincareHomotopy :
    MapsTo (poincareHomotopy hc (k := k)) (Icc (0 : ℝ) 1 ×ˢ E.whitneySet k D)
      (E.whitneySet (k + 1) D) := fun p hp => by
  rw [ScBanach.mem_whitneySet, ScBanach.mem_lvlSet, toBase_poincareHomotopy_fst]
  exact hconv.add_smul_sub_mem hcD (ScBanach.mem_whitneySet.1 hp.2) hp.1

include hD hconv hcD in
/-- The integrand is sc-smooth on `[0, 1] × ⊕ₖ TD`. -/
theorem isScSmooth_poincareIntegrand
    (hω : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω) :
    IsScSmooth (F := ScBanach.const ℝ) (Icc (0 : ℝ) 1 ×ˢ E.whitneySet k D)
      (poincareIntegrand hc ω) := by
  have hdom := (hD.whitneySet k).isScDomain.Icc_prod
  have h1 := (ScBanach.fstOp (ScBanach.const ℝ) (E.whitney k)).isScSmooth hdom
  have h2 : IsScSmooth (E := ScBanach.const ℝ) (F := ScBanach.const ℝ) univ
      fun x : ℝ => x ^ k :=
    IsScSmooth.of_contDiffOn_finiteDimensional (isScDomain_univ _) (contDiff_id.pow k).contDiffOn
  have hpow := IsScSmooth.comp hdom (isScDomain_univ _) h2 h1 (mapsTo_univ _ _)
  have hωH := IsScSmooth.comp hdom (hD.whitneySet (k + 1)).isScDomain hω
    (isScSmooth_poincareHomotopy hc hdom) (mapsTo_poincareHomotopy hc hconv hcD)
  exact IsScSmooth.smul hdom hpow hωH

include hD hconv hcD in
/-- **`τ` is sc-smooth** on `⊕ₖ TD` (`isScSmooth_intervalIntegral`). -/
theorem isScSmooth_homotopyForm
    (hω : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω) :
    IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet k D) (homotopyForm hc ω) :=
  isScSmooth_intervalIntegral (hD.whitneySet k).isScDomain
    (isScSmooth_poincareIntegrand hc ω hD hconv hcD hω)

lemma poincareHomotopy_whitneyMk (t : ℝ) (y : E 1) (v : Fin k → E 0) :
    poincareHomotopy hc ((t, ScBanach.whitneyMk y v) : ((ScBanach.const ℝ).prod (E.whitney k)) 0) =
      ScBanach.whitneyMk (poincareLift hc 1 + t • (y - poincareLift hc 1))
        (Fin.cons (E.toBase 1 y - c) v) := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · change E.incl 0 y - poincareLift hc 0 = _
    rw [ScBanach.fiberPackL_succ_fst, Fin.cons_zero, poincareLift_zero]; rfl
  · rw [ScBanach.fiberPackL_succ_snd, Fin.tail_cons]; rfl

include hD hconv hcD in
/-- **`τ` is alternating on the fibres.** -/
theorem homotopyForm_alternating
    (hω : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω)
    (halt : ∀ y ∈ E.lvlSet D 1, ∃ a : E 0 [⋀^Fin (k + 1)]→ₗ[ℝ] ℝ, ∀ v,
      ω (ScBanach.whitneyMk y v) = a v)
    {y : E 1} (hy : y ∈ E.lvlSet D 1) :
    ∃ a : E 0 [⋀^Fin k]→ₗ[ℝ] ℝ, ∀ v, homotopyForm hc ω (ScBanach.whitneyMk y v) = a v := by
  have hcont := (isScSmooth_poincareIntegrand hc ω hD hconv hcD hω 0).continuousOn_base
  obtain ⟨a, ha⟩ := exists_alternatingMap_intervalIntegral
    (G := fun t v => poincareIntegrand hc ω (t, ScBanach.whitneyMk y v)) (fun t ht => by
      have hz := mapsTo_poincareHomotopy hc hconv hcD
        (x := ((t, ScBanach.whitneyMk y (0 : Fin k → E 0)) :
          ((ScBanach.const ℝ).prod (E.whitney k)) 0)) ⟨ht, ScBanach.mem_whitneySet.2 hy⟩
      rw [ScBanach.mem_whitneySet, poincareHomotopy_whitneyMk] at hz
      obtain ⟨b, hb⟩ := halt _ hz
      refine ⟨t ^ k • b.curryLeft (E.toBase 1 y - c), fun v => ?_⟩
      rw [poincareIntegrand, poincareHomotopy_whitneyMk, hb]
      rfl)
    fun v => intervalIntegrable_of_continuousOn_Icc (hcont.comp
      (continuous_id.prodMk continuous_const).continuousOn fun t ht =>
        ⟨ht, ScBanach.mem_whitneySet.2 hy⟩)
  exact ⟨a, fun v => (ha v).symm⟩

end HomotopyForm

/-! ### The derivative of the integrand -/

section Deriv

variable {c : E 0} (hc : c ∈ E.smooth) {k : ℕ}

variable (E k) in
/-- The derivative of the homotopy on level `m` at a point `(t, y, v)`, with `a = y − c`:
`(s, (η, w)) ↦ (s a + t η, (η, w))`. -/
def poincareDHLvl (m : ℕ) (t : ℝ) (a : E (m + 1)) :
    ((ScBanach.const ℝ).prod (E.whitney k)) m →L[ℝ] (E.whitney (k + 1)) m :=
  ((ContinuousLinearMap.fst ℝ ℝ (E (m + 1) × (E.fiberPow k) m)).smulRight a +
      t • ((ContinuousLinearMap.fst ℝ (E (m + 1)) ((E.fiberPow k) m)).comp
        (ContinuousLinearMap.snd ℝ ℝ (E (m + 1) × (E.fiberPow k) m)))).prod
    (((E.incl m).comp ((ContinuousLinearMap.fst ℝ (E (m + 1)) ((E.fiberPow k) m)).comp
        (ContinuousLinearMap.snd ℝ ℝ (E (m + 1) × (E.fiberPow k) m)))).prod
      ((ContinuousLinearMap.snd ℝ (E (m + 1)) ((E.fiberPow k) m)).comp
        (ContinuousLinearMap.snd ℝ ℝ (E (m + 1) × (E.fiberPow k) m))))

lemma poincareDHLvl_apply (m : ℕ) (t : ℝ) (a : E (m + 1))
    (u : ℝ × (E (m + 1) × (E.fiberPow k) m)) :
    poincareDHLvl E k m t a u =
      ((u.1 • a + t • u.2.1, (E.incl m u.2.1, u.2.2)) : E (m + 1) × (E m × (E.fiberPow k) m)) :=
  rfl

lemma hasFDerivAt_poincareHomotopyLvl (m : ℕ) (p : ℝ × (E (m + 1) × (E.fiberPow k) m)) :
    HasFDerivAt (poincareHomotopyLvl hc (k := k) m)
      (poincareDHLvl E k m p.1 (p.2.1 - poincareLift hc (m + 1))) p := by
  have h1 : HasFDerivAt (fun q : ℝ × (E (m + 1) × (E.fiberPow k) m) => q.2.1)
      ((ContinuousLinearMap.fst ℝ (E (m + 1)) ((E.fiberPow k) m)).comp
        (ContinuousLinearMap.snd ℝ ℝ (E (m + 1) × (E.fiberPow k) m))) p :=
    hasFDerivAt_snd.fst
  have h := ((hasFDerivAt_const (poincareLift hc (m + 1)) p).add
      (hasFDerivAt_fst.smul (h1.sub_const (poincareLift hc (m + 1))))).prodMk
    ((((E.incl m).hasFDerivAt.comp p h1).sub_const (poincareLift hc m)).prodMk
      hasFDerivAt_snd.snd)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  change 0 + (p.1 • u.2.1 + u.1 • (p.2.1 - poincareLift hc (m + 1))) =
    u.1 • (p.2.1 - poincareLift hc (m + 1)) + p.1 • u.2.1
  rw [zero_add]
  exact add_comm _ _

variable {C D : Set (E 0)} (hD : IsRelOpenInQuadrant E C D) (hconv : Convex ℝ D) (hcD : c ∈ D)
  (ω : (E.whitney (k + 1)) 0 → ℝ)

include hD hconv hcD in
/-- **The partial derivative of the integrand**: at `(t, x)`, `x ∈ ⊕ₖ T(D¹)`, in a direction
`(0, δ)`, `D g(t, x)(0, δ) = tᵏ Dω(H(t, x))(t δ₀, δ₀, δ₁, …, δ_k)`. -/
theorem scDeriv_poincareIntegrand
    (hω : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : (E.whitney k) 1}
    (hx : x ∈ (E.whitney k).lvlSet (E.whitneySet k D) 1) (δ : (E.whitney k) 0) :
    scDeriv (F := ScBanach.const ℝ) (Icc (0 : ℝ) 1 ×ˢ E.whitneySet k D) (poincareIntegrand hc ω)
        ((t, x) : ((ScBanach.const ℝ).prod (E.whitney k)) 1)
        ((0, δ) : ((ScBanach.const ℝ).prod (E.whitney k)) 0) =
      t ^ k * scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω
        (poincareHomotopyLvl hc 1 ((t, x) : ((ScBanach.const ℝ).prod (E.whitney k)) 1))
        (ScBanach.whitneyMk (t • δ.1) (Fin.cons (E.toBase 1 δ.1) (ScBanach.whitneyVec δ))) := by
  set p : ((ScBanach.const ℝ).prod (E.whitney k)) 1 := (t, x) with hp_def
  set z := poincareHomotopyLvl hc 1 p with hz_def
  have hdom := (hD.whitneySet k).isScDomain.Icc_prod
  have hpS : p ∈ ((ScBanach.const ℝ).prod (E.whitney k)).lvlSet
      (Icc (0 : ℝ) 1 ×ˢ E.whitneySet k D) 1 := mk_mem_lvlSet_Icc_prod ht hx
  have hmaps : MapsTo (poincareHomotopyLvl hc 1) (((ScBanach.const ℝ).prod (E.whitney k)).lvlSet
      (Icc (0 : ℝ) 1 ×ˢ E.whitneySet k D) 1)
      ((E.whitney (k + 1)).lvlSet (E.whitneySet (k + 1) D) 1) := fun p' hp' => by
    rw [ScBanach.mem_lvlSet, toBase_poincareHomotopyLvl]
    exact mapsTo_poincareHomotopy hc hconv hcD hp'
  have hω1 := (hω.isSc1.isSc1With_scDeriv).hasFDerivWithinAt z (hmaps hpS)
  have hcomp := hω1.comp p (hasFDerivAt_poincareHomotopyLvl hc 1 p).hasFDerivWithinAt hmaps
  have hfst : HasFDerivAt (fun p' : ((ScBanach.const ℝ).prod (E.whitney k)) 1 => (p'.1 : ℝ))
      (ContinuousLinearMap.fst ℝ ℝ ((E.whitney k) 1)) p := hasFDerivAt_fst
  have hpow := (hfst.pow k).hasFDerivWithinAt (s :=
    ((ScBanach.const ℝ).prod (E.whitney k)).lvlSet (Icc (0 : ℝ) 1 ×ˢ E.whitneySet k D) 1)
  have hmul := hpow.mul hcomp
  set a₀ : E 1 := E.incl 1 (x.1 - poincareLift hc 2) with ha₀
  have hDH : ∀ u : ((ScBanach.const ℝ).prod (E.whitney k)) 1,
      (E.whitney (k + 1)).toBase 1 (poincareDHLvl E k 1 t (x.1 - poincareLift hc 2) u) =
        poincareDHLvl E k 0 t a₀ (((ScBanach.const ℝ).prod (E.whitney k)).toBase 1 u) := by
    intro u
    refine Prod.ext ?_ (Prod.ext rfl rfl)
    change E.incl 1 (u.1 • (x.1 - poincareLift hc 2) + t • u.2.1) =
      u.1 • E.incl 1 (x.1 - poincareLift hc 2) + t • E.incl 1 u.2.1
    rw [map_add, map_smul, map_smul]
  have key : scDeriv (F := ScBanach.const ℝ) (Icc (0 : ℝ) 1 ×ˢ E.whitneySet k D)
      (poincareIntegrand hc ω) p =
      t ^ k • (scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω z).comp
          (poincareDHLvl E k 0 t a₀) +
        (ω ((E.whitney (k + 1)).toBase 1 z) * (k * t ^ (k - 1))) •
          ContinuousLinearMap.fst ℝ ℝ ((E.whitney k) 0) := by
    refine (isScSmooth_poincareIntegrand hc ω hD hconv hcD hω).isSc1.scDeriv_eq_of_hasFDerivWithinAt
      hpS (hdom.uniqueDiffWithinAt 1 _ hpS) ?_
    have hfun : poincareIntegrand hc ω ∘ ((ScBanach.const ℝ).prod (E.whitney k)).toBase 1 =
        (fun p' : ((ScBanach.const ℝ).prod (E.whitney k)) 1 => p'.1 ^ k) *
          ((ω ∘ (E.whitney (k + 1)).toBase 1) ∘ poincareHomotopyLvl hc 1) := by
      funext p'
      change (((ScBanach.const ℝ).prod (E.whitney k)).toBase 1 p').1 ^ k *
          ω (poincareHomotopyLvl hc 0 (((ScBanach.const ℝ).prod (E.whitney k)).toBase 1 p')) =
        p'.1 ^ k * ω ((E.whitney (k + 1)).toBase 1 (poincareHomotopyLvl hc 1 p'))
      rw [toBase_poincareHomotopyLvl]
      rfl
    rw [hfun]
    refine hmul.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
    have h1 := hDH u
    simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul, nsmul_eq_mul, Function.comp_apply] at h1 ⊢
    rw [h1, ← hz_def]
    have hp1 : p.1 = t := rfl
    have hu1 : (ContinuousLinearMap.fst ℝ ℝ (E (1 + 1) × (E.fiberPow k) 1)) u =
        (((ScBanach.const ℝ).prod (E.whitney k)).toBase 1 u).1 := rfl
    rw [hp1, hu1]
    simp only [ContinuousLinearMap.coe_fst']
    ring
  rw [key]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', smul_eq_mul, mul_zero,
    add_zero]
  congr 2
  change ((0 : ℝ) • a₀ + t • δ.1, (E.incl 0 δ.1, δ.2)) = _
  rw [zero_smul, zero_add]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · rw [ScBanach.fiberPackL_succ_fst, Fin.cons_zero]; rfl
  · rw [ScBanach.fiberPackL_succ_snd, Fin.tail_cons, ScBanach.fiberPackL_fiberVecL]

lemma whitneyMk_smul_add_single (t : ℝ) (e : E 1) (x : E 0) :
    ScBanach.whitneyMk (t • e) (Fin.cons x (0 : Fin k → E 0)) =
      t • ScBanach.whitneyMk e 0 +
        ((0, E.fiberPackL 0 (k + 1) (Pi.single 0 x)) : (E.whitney (k + 1)) 0) := by
  have hv : (Fin.cons x (0 : Fin k → E 0) : Fin (k + 1) → E 0) =
      Pi.single (0 : Fin (k + 1)) x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.succ_ne_zero]
  refine Prod.ext ?_ ?_
  · change t • e = t • e + 0
    rw [add_zero]
  · change E.fiberPackL 0 (k + 1) (Fin.cons x 0) =
      t • E.fiberPackL 0 (k + 1) 0 + E.fiberPackL 0 (k + 1) (Pi.single 0 x)
    rw [map_zero, smul_zero, zero_add, hv]

include hD hconv hcD in
/-- **One term of `dτ`**: `D g(t, x)(0, (e, 0)) = tᵏ (t Dω(H(t, x))(e, 0) + ω(c + t(y − c))(e, v))`
for `x = (y, v)` on level `1`. -/
theorem scDeriv_poincareIntegrand_base
    (hω : IsAmbientScForm E D (k + 1) ω)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : (E.whitney k) 1}
    (hx : x ∈ (E.whitney k).lvlSet (E.whitneySet k D) 1) (e : E 1) :
    scDeriv (F := ScBanach.const ℝ) (Icc (0 : ℝ) 1 ×ˢ E.whitneySet k D) (poincareIntegrand hc ω)
        ((t, x) : ((ScBanach.const ℝ).prod (E.whitney k)) 1)
        ((0, ScBanach.whitneyMk e 0) : ((ScBanach.const ℝ).prod (E.whitney k)) 0) =
      t ^ k * (t * scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω
          (poincareHomotopyLvl hc 1 ((t, x) : ((ScBanach.const ℝ).prod (E.whitney k)) 1))
          (ScBanach.whitneyMk e 0) +
        ω (ScBanach.whitneyMk (E.incl 1 (poincareLift hc 2 + t • (x.1 - poincareLift hc 2)))
          (Fin.cons (E.toBase 1 e) (ScBanach.whitneyVec ((E.whitney k).toBase 1 x))))) := by
  rw [scDeriv_poincareIntegrand hc hD hconv hcD ω hω.isScSmooth ht hx]
  have hmaps : poincareHomotopyLvl hc 1 ((t, x) : ((ScBanach.const ℝ).prod (E.whitney k)) 1) ∈
      (E.whitney (k + 1)).lvlSet (E.whitneySet (k + 1) D) 1 := by
    rw [ScBanach.mem_lvlSet, toBase_poincareHomotopyLvl]
    exact mapsTo_poincareHomotopy hc hconv hcD (mk_mem_lvlSet_Icc_prod ht hx)
  have hA : ∀ z ∈ E.lvlSet D 1, ∃ a : MultilinearMap ℝ (fun _ : Fin (k + 1) => E 0) ℝ,
      ∀ v, ω (ScBanach.whitneyMk z v) = a v := fun z hz => by
    obtain ⟨a, ha⟩ := hω.alternating z hz
    exact ⟨a.toMultilinearMap, ha⟩
  have hfib := scDeriv_whitney_fiber_single hω.isScSmooth.isSc1 hA hmaps 0 (E.toBase 1 e)
  rw [ScBanach.whitneyVec_mk]
  change t ^ k * scDeriv (F := ScBanach.const ℝ) _ ω _
    (ScBanach.whitneyMk (t • e) (Fin.cons (E.toBase 1 e) (0 : Fin k → E 0))) = _
  rw [whitneyMk_smul_add_single, map_add, map_smul, hfib, smul_eq_mul]
  congr 3

end Deriv

/-! ### The homotopy formula `dτ = ω` -/

/-- Removing the `(j + 1)`-st entry of `(a, h₀, …, h_k)` gives `(a, h₀, …, ĥ_j, …, h_k)`. -/
lemma removeNth_succ_cons_eq {α : Type*} {n : ℕ} (j : Fin (n + 1)) (a : α)
    (h : Fin (n + 1) → α) :
    j.succ.removeNth (Fin.cons a h : Fin (n + 2) → α) = Fin.cons a (j.removeNth h) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Fin.removeNth]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

/-- `∑ⱼ (−1)ʲ A(wⱼ, w₀, …, ŵⱼ, …) = (n + 1) A(w)` for an alternating `A`. -/
lemma sum_alternating_cons_removeNth {M : Type*} [AddCommGroup M] [Module ℝ M] {n : ℕ}
    (A : M [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ) (w : Fin (n + 1) → M) :
    ∑ j : Fin (n + 1), (-1 : ℝ) ^ j.val * A (Fin.cons (w j) (j.removeNth w)) =
      (n + 1) * A w := by
  have h := congrArg (fun B : M [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ => B w)
    (AlternatingMap.alternatizeUncurryFin_curryLeft A)
  simp only [AlternatingMap.alternatizeUncurryFin_apply, AlternatingMap.curryLeft_apply_apply,
    AlternatingMap.smul_apply, nsmul_eq_mul] at h
  push_cast at h
  refine (Finset.sum_congr rfl fun j _ => ?_).trans h
  rw [zsmul_eq_mul]
  push_cast
  rfl

/-- The partial derivative `t ↦ Dg(t, x)(0, δ)` of an sc¹ map on `[0, 1] × U` is continuous. -/
lemma continuousOn_scDeriv_param {F : ScBanach} {U : Set (E 0)}
    {g : ((ScBanach.const ℝ).prod E) 0 → F 0} (hg : IsSc1 (Icc (0 : ℝ) 1 ×ˢ U) g) {x : E 1}
    (hx : x ∈ E.lvlSet U 1) (δ : E 0) :
    ContinuousOn (fun t : ℝ => scDeriv (Icc (0 : ℝ) 1 ×ˢ U) g
      ((t, x) : ((ScBanach.const ℝ).prod E) 1) ((0, δ) : ((ScBanach.const ℝ).prod E) 0))
      (Icc 0 1) := by
  have h := hg.tangentMap_isSc0.continuousOn_base
  have hc : Continuous (fun t : ℝ => ((((t, x) : ((ScBanach.const ℝ).prod E) 1),
      ((0, δ) : ((ScBanach.const ℝ).prod E) 0)) : ((ScBanach.const ℝ).prod E).tangent 0)) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  exact continuous_snd.comp_continuousOn
    (h.comp hc.continuousOn fun t ht => mk_mem_lvlSet_Icc_prod ht hx)

section Formula

variable {c : E 0} (hc : c ∈ E.smooth) {k : ℕ}

/-- The level-`1` path `s ↦ (c + s(y − c), h)` in `⊕_{k+1} TD`. -/
def poincarePath (y : E 2) (h : Fin (k + 1) → E 1) (s : ℝ) : (E.whitney (k + 1)) 1 :=
  (poincareLift hc 2 + s • (y - poincareLift hc 2), E.fiberPackL 1 (k + 1) h)

lemma toBase_poincareLift_path (y : E 2) (s : ℝ) :
    E.toBase 2 (poincareLift hc 2 + s • (y - poincareLift hc 2)) =
      c + s • (E.toBase 2 y - c) := by
  rw [map_add, map_smul, map_sub, toBase_poincareLift]

lemma poincareHomotopyLvl_one_mk (t : ℝ) (y : E 2) (v : Fin k → E 1) :
    poincareHomotopyLvl hc 1
        ((t, ((y, E.fiberPackL 1 k v) : (E.whitney k) 1)) :
          ((ScBanach.const ℝ).prod (E.whitney k)) 1) =
      ((poincareLift hc 2 + t • (y - poincareLift hc 2),
        E.fiberPackL 1 (k + 1) (Fin.cons (E.incl 1 y - poincareLift hc 1) v)) :
          (E.whitney (k + 1)) 1) := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  rw [ScBanach.fiberPackL_succ_snd, Fin.tail_cons]
  rfl

variable {C D : Set (E 0)} (hD : IsRelOpenInQuadrant E C D) (hconv : Convex ℝ D) (hcD : c ∈ D)
  (ω : (E.whitney (k + 1)) 0 → ℝ)

include hconv hcD in
lemma mapsTo_poincarePath {y : E 2} (hy : E.toBase 2 y ∈ D) (h : Fin (k + 1) → E 1) :
    MapsTo (poincarePath hc y h) (Icc 0 1)
      ((E.whitney (k + 1)).lvlSet (E.whitneySet (k + 1) D) 1) := fun s hs => by
  rw [mem_whitneySet_lvl_one, ScBanach.mem_lvlSet, ← ScBanach.shift_toBase]
  change E.toBase 2 (poincareLift hc 2 + s • (y - poincareLift hc 2)) ∈ D
  rw [toBase_poincareLift_path]
  exact hconv.add_smul_sub_mem hcD hy hs

include hconv hcD in
/-- **Closedness along the homotopy**: if `dω = 0`, then at `z = c + t(y − c)`,
`∑ⱼ (−1)ʲ Dω(z, a, h₀, …, ĥⱼ, …)(hⱼ, 0) = Dω(z, h)(a, 0)` with `a = y − c`. -/
theorem sum_scDeriv_poincareHomotopy_of_closed
    (hclosed : ∀ q' ∈ E.shift.whitneySet (k + 2) (E.lvlSet D 1), ambientD D ω q' = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {y : E 2} (hy : E.toBase 2 y ∈ D) (h : Fin (k + 1) → E 1) :
    ∑ j : Fin (k + 1), (-1 : ℝ) ^ j.val *
        scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω
          (poincareHomotopyLvl hc 1 ((t, ((y, E.fiberPackL 1 k (j.removeNth h)) :
            (E.whitney k) 1)) : ((ScBanach.const ℝ).prod (E.whitney k)) 1))
          (ScBanach.whitneyMk (h j) 0) =
      scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω (poincarePath hc y h t)
        (ScBanach.whitneyMk (E.incl 1 y - poincareLift hc 1) 0) := by
  have hmem : ScBanach.whitneyMk (E := E.shift) (poincareLift hc 2 + t • (y - poincareLift hc 2))
      (Fin.cons (E.incl 1 y - poincareLift hc 1) h) ∈
        E.shift.whitneySet (k + 2) (E.lvlSet D 1) :=
    ScBanach.mem_whitneySet.2 (mem_whitneySet_lvl_one.1 (mapsTo_poincarePath hc hconv hcD hy h ht))
  have hz := hclosed _ hmem
  rw [ambientD_apply, Fin.sum_univ_succ] at hz
  simp only [ScBanach.whitneyVec_mk, Fin.cons_zero, Fin.cons_succ, Fin.removeNth_zero,
    Fin.tail_cons, removeNth_succ_cons_eq, Fin.val_zero, pow_zero, one_mul, Fin.val_succ,
    pow_succ] at hz
  have hsum : ∀ j : Fin (k + 1), scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω
      (poincareHomotopyLvl hc 1 ((t, ((y, E.fiberPackL 1 k (j.removeNth h)) :
        (E.whitney k) 1)) : ((ScBanach.const ℝ).prod (E.whitney k)) 1)) =
      scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω
        ((poincareLift hc 2 + t • (y - poincareLift hc 2), E.fiberPackL 1 (k + 1)
          (Fin.cons (E.incl 1 y - poincareLift hc 1) (j.removeNth h))) : (E.whitney (k + 1)) 1) :=
    fun j => congrArg _ (poincareHomotopyLvl_one_mk hc t y _)
  simp only [hsum]
  have key : ∀ X : Fin (k + 1) → ℝ,
      ∑ j : Fin (k + 1), (-1 : ℝ) ^ j.val * -1 * X j = -∑ j : Fin (k + 1), (-1 : ℝ) ^ j.val * X j :=
    fun X => by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
  rw [key] at hz
  change _ = scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω
    ((poincareLift hc 2 + t • (y - poincareLift hc 2), E.fiberPackL 1 (k + 1) h) :
      (E.whitney (k + 1)) 1) _
  linarith

include hconv hcD in
/-- The derivative of the primitive `s ↦ s^{k+1} ω(c + s(y − c))(h)`. -/
lemma hasDerivWithinAt_poincarePrimitive
    (hω : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω)
    {y : E 2} (hy : E.toBase 2 y ∈ D) (h : Fin (k + 1) → E 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun s : ℝ => s ^ (k + 1) * ω ((E.whitney (k + 1)).toBase 1 (poincarePath hc y h s)))
      (((k : ℝ) + 1) * t ^ k * ω ((E.whitney (k + 1)).toBase 1 (poincarePath hc y h t)) +
        t ^ (k + 1) * scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω
          (poincarePath hc y h t) (ScBanach.whitneyMk (E.incl 1 y - poincareLift hc 1) 0))
      (Icc 0 1) t := by
  have hmaps := mapsTo_poincarePath hc hconv hcD hy h
  have hω1 := hω.isSc1.isSc1With_scDeriv.hasFDerivWithinAt _ (hmaps ht)
  have hpath : HasDerivAt (fun s : ℝ => ((poincareLift hc 2 + s • (y - poincareLift hc 2),
      E.fiberPackL 1 (k + 1) h) : E 2 × (E.fiberPow (k + 1)) 1))
      ((y - poincareLift hc 2, 0) : E 2 × (E.fiberPow (k + 1)) 1) t := by
    refine HasDerivAt.prodMk ?_ (hasDerivAt_const _ _)
    simpa using ((hasDerivAt_id' t).smul_const (y - poincareLift hc 2)).const_add
      (poincareLift hc 2)
  have hcomp := hω1.comp_hasDerivWithinAt t hpath.hasDerivWithinAt hmaps
  have hpow : HasDerivWithinAt (fun s : ℝ => s ^ (k + 1)) (((k : ℝ) + 1) * t ^ k) (Icc 0 1) t := by
    simpa using (hasDerivAt_pow (k + 1) t).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
  refine (hpow.mul hcomp).congr_deriv ?_
  have hv : (E.whitney (k + 1)).toBase 1 ((y - poincareLift hc 2, 0) : (E.whitney (k + 1)) 1) =
      ScBanach.whitneyMk (E.incl 1 y - poincareLift hc 1) 0 := by
    refine Prod.ext ?_ ?_
    · change E.incl 1 (y - poincareLift hc 2) = _
      rw [map_sub, incl_poincareLift]
    · change (E.fiberPow (k + 1)).toBase 1 0 = E.fiberPackL 0 (k + 1) 0
      rw [map_zero, map_zero]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  rw [hv]

include hD hconv hcD in
/-- **The homotopy formula** (2021 Lemma 4.5.2, p. 203): for a closed ambient sc-form `ω` of
degree `k + 1` on the convex set `D` with smooth centre `c`, the form `τ = homotopyForm hc ω`
satisfies `dτ = ω` on `⊕_{k+1} T(D¹)`. -/
theorem ambientD_homotopyForm (hω : IsAmbientScForm E D (k + 1) ω)
    (hclosed : ∀ q' ∈ E.shift.whitneySet (k + 2) (E.lvlSet D 1), ambientD D ω q' = 0)
    {q : (E.shift.whitney (k + 1)) 0} (hq : q ∈ E.shift.whitneySet (k + 1) (E.lvlSet D 1)) :
    ambientD D (homotopyForm hc ω) q = ω (E.whitneyIncl (k + 1) 0 q) := by
  set h := ScBanach.whitneyVec q with hh
  have hy : E.toBase 2 q.1 ∈ D := by
    have h0 := ScBanach.mem_whitneySet.1 hq
    rw [ScBanach.mem_lvlSet, ScBanach.mem_lvlSet, ← ScBanach.shift_toBase] at h0
    exact h0
  have hW := (hD.whitneySet k).isScDomain
  have hg := (isScSmooth_poincareIntegrand hc ω hD hconv hcD hω.isScSmooth).isSc1
  have hx : ∀ j : Fin (k + 1), ((q.1, E.fiberPackL 1 k (j.removeNth h)) : (E.whitney k) 1) ∈
      (E.whitney k).lvlSet (E.whitneySet k D) 1 := fun j => by
    rw [mem_whitneySet_lvl_one, ScBanach.mem_lvlSet, ← ScBanach.shift_toBase]
    exact hy
  set G : Fin (k + 1) → ℝ → ℝ := fun j t =>
    scDeriv (F := ScBanach.const ℝ) (Icc (0 : ℝ) 1 ×ˢ E.whitneySet k D) (poincareIntegrand hc ω)
      ((t, ((q.1, E.fiberPackL 1 k (j.removeNth h)) : (E.whitney k) 1)) :
        ((ScBanach.const ℝ).prod (E.whitney k)) 1)
      ((0, ScBanach.whitneyMk (h j) 0) : ((ScBanach.const ℝ).prod (E.whitney k)) 0) with hG
  have hGi : ∀ j, IntervalIntegrable (G j) MeasureTheory.volume 0 1 := fun j =>
    intervalIntegrable_of_continuousOn_Icc (continuousOn_scDeriv_param hg (hx j) _)
  have h1 : ∀ j : Fin (k + 1), scDeriv (F := ScBanach.const ℝ) (E.whitneySet k D)
      (homotopyForm hc ω) (q.1, E.fiberPackL 1 k (j.removeNth h)) (ScBanach.whitneyMk (h j) 0) =
        ∫ t in (0 : ℝ)..1, G j t :=
    fun j => scDeriv_intervalIntegral hW hg (hx j) _
  rw [ambientD_apply, ← hh]
  simp only [h1, ← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum fun j _ => (hGi j).const_mul _]
  have hint : IntervalIntegrable (fun t => ∑ j : Fin (k + 1), (-1 : ℝ) ^ j.val * G j t)
      MeasureTheory.volume 0 1 :=
    intervalIntegrable_of_continuousOn_Icc (continuousOn_finsetSum _ fun j _ =>
      continuousOn_const.mul (continuousOn_scDeriv_param hg (hx j) _))
  have hderiv := fun t (ht : t ∈ Icc (0 : ℝ) 1) =>
    hasDerivWithinAt_poincarePrimitive hc hconv hcD ω hω.isScSmooth hy h ht
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ∑ j : Fin (k + 1), (-1 : ℝ) ^ j.val * G j t =
      ((k : ℝ) + 1) * t ^ k * ω ((E.whitney (k + 1)).toBase 1 (poincarePath hc q.1 h t)) +
        t ^ (k + 1) * scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω
          (poincarePath hc q.1 h t) (ScBanach.whitneyMk (E.incl 1 q.1 - poincareLift hc 1) 0) := by
    intro t ht
    set z := poincareLift hc 2 + t • (q.1 - poincareLift hc 2) with hz
    have hzD : E.incl 1 z ∈ E.lvlSet D 1 := by
      change E.toBase 2 z ∈ D
      rw [hz, toBase_poincareLift_path]
      exact hconv.add_smul_sub_mem hcD hy ht
    obtain ⟨A, hA⟩ := hω.alternating _ hzD
    set w : Fin (k + 1) → E 0 := fun i => E.toBase 1 (h i) with hw
    have hterm : ∀ j : Fin (k + 1), G j t = t ^ k * (t *
        scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + 1) D) ω
          (poincareHomotopyLvl hc 1 ((t, ((q.1, E.fiberPackL 1 k (j.removeNth h)) :
            (E.whitney k) 1)) : ((ScBanach.const ℝ).prod (E.whitney k)) 1))
          (ScBanach.whitneyMk (h j) 0) + A (Fin.cons (w j) (j.removeNth w))) := fun j => by
      rw [hG]
      dsimp only
      rw [scDeriv_poincareIntegrand_base hc hD hconv hcD ω hω ht (hx j), whitney_toBase_mk]
      simp only [ScBanach.whitneyVec_mk]
      rw [hA]
      rfl
    have hP := sum_scDeriv_poincareHomotopy_of_closed hc hconv hcD ω hclosed ht hy h
    have hS := sum_alternating_cons_removeNth A w
    have hωp : ω ((E.whitney (k + 1)).toBase 1 (poincarePath hc q.1 h t)) = A w := by
      rw [poincarePath, whitney_toBase_mk]
      exact hA _
    rw [Finset.sum_congr rfl fun j _ => by rw [hterm j], hωp, ← hP,
      show ((k : ℝ) + 1) * t ^ k * A w = t ^ k * (((k : ℝ) + 1) * A w) by ring, ← hS,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (fun t ht => (hderiv t ht).continuousWithinAt)
    (fun t ht => ((hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)).congr_deriv (hpt t (Ioo_subset_Icc_self ht)).symm) hint]
  have hp1 : poincarePath hc q.1 h 1 =
      ((q.1, E.fiberPackL 1 (k + 1) h) : (E.whitney (k + 1)) 1) := by
    simp [poincarePath]
  rw [hp1, one_pow, one_mul, zero_pow (Nat.succ_ne_zero k), zero_mul, sub_zero,
    whitney_toBase_mk, ← whitneyMk_fst_vec (E.whitneyIncl (k + 1) 0 q),
    ScBanach.whitneyIncl_fst]
  congr 2
  funext i
  rw [ScBanach.whitneyVec_whitneyIncl]

include hc hD hconv hcD in
/-- **2021 Lemma 4.5.2 (p. 202)** in a local model, with a smooth centre `c` (`c = 0` in the
text): on a convex relatively open `D ⊆ C`, every closed sc-form `ω` of degree `k + 1`
(`IsAmbientScForm`, `dω = 0` on `⊕_{k+2} T(D¹)`) has a primitive `τ` of degree `k` with `dτ = ω`
on `⊕_{k+1} T(D¹)`, namely `τ = homotopyForm hc ω`. -/
theorem lemma_4_5_2 (hω : IsAmbientScForm E D (k + 1) ω)
    (hclosed : ∀ q' ∈ E.shift.whitneySet (k + 2) (E.lvlSet D 1), ambientD D ω q' = 0) :
    ∃ τ : (E.whitney k) 0 → ℝ, IsAmbientScForm E D k τ ∧
      ∀ q ∈ E.shift.whitneySet (k + 1) (E.lvlSet D 1),
        ambientD D τ q = ω (E.whitneyIncl (k + 1) 0 q) :=
  ⟨homotopyForm hc ω, ⟨isScSmooth_homotopyForm hc ω hD hconv hcD hω.isScSmooth,
    fun _ hy => homotopyForm_alternating hc ω hD hconv hcD hω.isScSmooth hω.alternating hy⟩,
    fun _ hq => ambientD_homotopyForm hc hD hconv hcD ω hω hclosed hq⟩

end Formula

/-! ### Relatively open sets: forms on the retract and ambient forms -/

section RelOpen

variable {C D : Set (E 0)} (hD : IsRelOpenInQuadrant E C D) {k : ℕ}

include hD in
/-- For a relatively open `D`, `⊕ₖ TD = D¹ ⊕ E^k`. -/
lemma retractWhitney_relOpen : retractWhitney E C D k = E.whitneySet k D := by
  ext q
  rw [ScBanach.mem_whitneySet]
  refine ⟨fun h => h.1, fun h => ⟨h, fun i => ?_⟩⟩
  change ScBanach.whitneyVec q i ∈ tangentSpace E C D q.1
  rw [tangentSpace_relOpen hD h]
  trivial

include hD in
lemma isScSmooth_of_isScSmoothRetractMap {f : (E.whitney k) 0 → ℝ}
    (h : IsScSmoothRetractMap (E.whitney k) (E.whitneySet k C) (retractWhitney E C D k)
      (ScBanach.const ℝ) univ univ f) :
    IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet k D) f :=
  h.comp_isScSmooth (ScRetraction.id (hD.whitneySet k))
    (by rw [retractWhitney_relOpen hD]; exact image_id _)

include hD in
lemma isScSmoothRetractMap_of_isScSmooth {f : (E.whitney k) 0 → ℝ}
    (h : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet k D) f) :
    IsScSmoothRetractMap (E.whitney k) (E.whitneySet k C) (retractWhitney E C D k)
      (ScBanach.const ℝ) univ univ f := by
  have hO : IsScRetract (E.whitney k) (E.whitneySet k C) (retractWhitney E C D k) := by
    rw [retractWhitney_relOpen hD]; exact (hD.whitneySet k).isScRetract
  exact (isScSmoothRetractMap_iff_exists hO).2 ⟨mapsTo_univ _ _,
    ScRetraction.id (hD.whitneySet k), by rw [retractWhitney_relOpen hD]; exact image_id _, h⟩

include hD in
/-- An sc-form on a relatively open retract `D` is an ambient sc-form on `D`. -/
theorem IsRetractScForm.isAmbientScForm_relOpen {ω : (E.whitney k) 0 → ℝ}
    (hω : IsRetractScForm E C D k ω) : IsAmbientScForm E D k ω where
  isScSmooth := isScSmooth_of_isScSmoothRetractMap hD hω.isScSmooth
  alternating z hz := by
    obtain ⟨a, ha⟩ := hω.alternating z hz
    exact ⟨a, fun v => ha v fun i => by rw [tangentSpace_relOpen hD hz]; trivial⟩

include hD in
/-- On a relatively open `D`, the local exterior derivative for any retraction onto `D` is the
ambient one. -/
theorem retractD_eq_ambientD (R : ScRetraction E C) (hR : R.retract = D)
    {ω : (E.whitney k) 0 → ℝ} (hω : IsRetractScForm E C D k ω)
    {q : (E.shift.whitney (k + 1)) 0} (hq : q ∈ E.shift.whitneySet (k + 1) (E.lvlSet D 1)) :
    retractD R ω q = ambientD D ω q := by
  have hR₀ : (ScRetraction.id hD).retract = D := image_id D
  have hq' : q ∈ retractWhitney E.shift (E.lvlSet C 1) (E.lvlSet D 1) (k + 1) := by
    rw [retractWhitney_relOpen hD.shift]; exact hq
  rw [← retractD_eq_of_subset R hR (ScRetraction.id hD) hR₀ subset_rfl hω hq']
  have hsm := (hω.isAmbientScForm_relOpen hD).isScSmooth
  change ambientD D (ω ∘ (ScRetraction.id hD).whitney k) q = _
  refine ambientD_congr (hD.whitneySet k).isScDomain hsm.isSc1 (fun p hp => ?_) hq
  have hp' : p ∈ retractWhitney E C (ScRetraction.id hD).retract k := by
    rw [hR₀, retractWhitney_relOpen hD]; exact hp
  change ω p = ω ((ScRetraction.id hD).whitney k p)
  rw [ScRetraction.whitney_apply, (ScRetraction.id hD).whitneyMap_eq_self hp']

end RelOpen

/-! ### Lemma 4.5.2 on the M-polyfold `D` -/

section MPolyfoldForm

open MPolyfold

variable {M : LocalModel} (hM : IsRelOpenInQuadrant M.E M.C M.O) (hne : M.O.Nonempty) {k : ℕ}

/-- The sc-form on the M-polyfold `O` of a relatively open local model (one chart `id`) with
local representative `τ₀`. -/
noncomputable def relOpenForm (τ₀ : (M.E.whitney k) 0 → ℝ) (hτ : IsAmbientScForm M.E M.O k τ₀) :
    ∀ x : (M.toMPolyfold hne).Level 1, (M.toMPolyfold hne).tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ :=
  fun x => (hτ.alternating _ (levelLift_mem_lvlSet_one (x := x) (M.selfChart_isChart' hne)
    (mem_univ _))).choose.compLinearMap
    ((tangentFiberModel (M.selfChart_isChart' hne)
      (mem_univ ((M.toMPolyfold hne).levelVal 1 x))).subtype ∘ₗ
      (tangentFiberLinearEquiv (M.selfChart_isChart' hne)
        (mem_univ ((M.toMPolyfold hne).levelVal 1 x))).toLinearMap)

lemma relOpenForm_apply (τ₀ : (M.E.whitney k) 0 → ℝ) (hτ : IsAmbientScForm M.E M.O k τ₀)
    (x : (M.toMPolyfold hne).Level 1) (α : Fin k → (M.toMPolyfold hne).tangentFiber x) :
    relOpenForm hne τ₀ hτ x α = τ₀ (ScBanach.whitneyMk
      (levelLift (M.selfChart hne) 1 ((M.toMPolyfold hne).levelVal 1 x))
      fun i => (tangentChartMap (M.selfChart_isChart' hne) (α i)).2) := by
  rw [relOpenForm, AlternatingMap.compLinearMap_apply]
  exact ((hτ.alternating _ (levelLift_mem_lvlSet_one (x := x) (M.selfChart_isChart' hne)
    (mem_univ _))).choose_spec _).symm

include hM in
lemma chartForm_relOpenForm (τ₀ : (M.E.whitney k) 0 → ℝ) (hτ : IsAmbientScForm M.E M.O k τ₀)
    {q : (M.E.whitney k) 0} (hq : q ∈ M.E.whitneySet k M.O) :
    chartForm (M.selfChart_isChart' hne) (relOpenForm hne τ₀ hτ) q = τ₀ q := by
  have hφ := M.selfChart_isChart' hne
  have hq' : q ∈ retractWhitney M.E M.C M.O k := by rw [retractWhitney_relOpen hM]; exact hq
  unfold chartForm
  split_ifs with h
  swap; · exact absurd hq' h
  rw [relOpenForm_apply]
  have e1 := levelLift_chartPoint hφ h.1
  have e2 : ∀ i, (tangentChartMap hφ (TangentSpace.mk (TangentPre.ofVec hφ (h.2 i)))).2 =
      ScBanach.whitneyVec q i := fun i =>
    congrArg Prod.snd (tangentChartMap_mk_ofVec hφ (h.2 i))
  exact congrArg τ₀ ((congrArg₂ (ScBanach.whitneyMk (E := M.E)) e1 (funext e2)).trans
    (whitneyMk_fst_vec q))

include hM in
lemma relOpenForm_mem_scForms (τ₀ : (M.E.whitney k) 0 → ℝ) (hτ : IsAmbientScForm M.E M.O k τ₀) :
    relOpenForm hne τ₀ hτ ∈ (M.toMPolyfold hne).scForms k :=
  isScForm_of_cover _ fun _ => ⟨_, M.selfChart_isChart' hne, mem_univ _,
    (isScSmoothRetractMap_of_isScSmooth hM hτ.isScSmooth).congr fun _ hq =>
      (chartForm_relOpenForm hM hne τ₀ hτ (by rwa [retractWhitney_relOpen hM] at hq)).symm⟩

include hM in
/-- **2021 Lemma 4.5.2 (p. 202) on the M-polyfold `O`**: for a convex relatively open `O ⊆ C`
with a smooth point `c`, every closed `σ ∈ Ωᵏ⁺¹(O)` has `τ ∈ Ωᵏ(O)` with `dτ = σ` on `O¹`. -/
theorem hasPoincare_relOpen (hconv : Convex ℝ M.O) {c : M.E 0} (hcD : c ∈ M.O)
    (hc : c ∈ M.E.smooth) (k : ℕ) : (M.toMPolyfold hne).HasPoincare k := by
  intro σ hσ hdσ
  have hφ := M.selfChart_isChart' hne
  have hσ' : (M.toMPolyfold hne).IsScForm (k + 1) σ := hσ
  set ω := chartForm hφ σ with hω_def
  have hωR : IsRetractScForm M.E M.C M.O (k + 1) ω := hσ'.isRetractScForm hφ
  have hωA := hωR.isAmbientScForm_relOpen hM
  have hclosed : ∀ q' ∈ M.E.shift.whitneySet (k + 2) (M.E.lvlSet M.O 1),
      ambientD M.O ω q' = 0 := by
    intro q' hq'
    let y₀ : (M.toMPolyfold hne).Level 1 := ⟨⟨c, hcD⟩,
      (LocalModel.mem_levelSet_toMPolyfold_iff hne _).2
        ⟨poincareLift hc 1, toBase_poincareLift hc 1⟩⟩
    have hq'' : q' ∈ retractWhitney M.E.shift (M.E.lvlSet M.C 1) (M.E.lvlSet M.O 1) (k + 2) := by
      rw [retractWhitney_relOpen hM.shift]; exact hq'
    have h1 := chartForm_extD hφ hσ' y₀ hq''
    rw [hdσ] at h1
    have h2 : chartD hφ σ q' = 0 := by
      rw [← h1]
      unfold chartForm
      split_ifs <;> rfl
    exact (retractD_eq_ambientD hM _ (chartRetraction_retract _) hωR hq').symm.trans h2
  have hτA : IsAmbientScForm M.E M.O k (homotopyForm hc ω) :=
    ⟨isScSmooth_homotopyForm hc ω hM hconv hcD hωA.isScSmooth,
      fun _ hy => homotopyForm_alternating hc ω hM hconv hcD hωA.isScSmooth hωA.alternating hy⟩
  have hτ := relOpenForm_mem_scForms hM hne _ hτA
  refine ⟨relOpenForm hne _ hτA, hτ, ?_⟩
  funext x
  ext α
  set y₀ := (M.toMPolyfold hne).shift.levelVal 1 x
  have hx : (M.toMPolyfold hne).shift.levelVal 1 x ∈ (levelChart hφ y₀).source := mem_univ _
  have hτ' : (M.toMPolyfold hne).IsScForm k (relOpenForm hne _ hτA) := hτ
  rw [extD_apply hφ hτ' y₀ hx α]
  have hmem := whitneyMk_tangentChartMap_mem hφ y₀ hx α
  have hQ := ScBanach.mem_whitneySet.2 hmem.1
  unfold chartD
  refine (retractD_eq_ambientD hM _ (chartRetraction_retract _) (hτ'.isRetractScForm hφ)
    hQ).trans ?_
  refine (ambientD_congr (hM.whitneySet k).isScDomain hτA.isScSmooth.isSc1
    (fun p hp => (chartForm_relOpenForm hM hne _ hτA hp).symm) hQ).trans ?_
  refine (ambientD_homotopyForm hc hM hconv hcD ω hωA hclosed hQ).trans ?_
  refine (chartForm_formLower hφ σ y₀ hmem).symm.trans ?_
  exact chartForm_eq ((M.toMPolyfold hne).shift_isChart hφ y₀) _ hx α rfl fun i =>
    congrFun (ScBanach.whitneyVec_mk (E := M.E.shift) _ _) i

include hM in
/-- **2021 Lemma 4.5.2 (p. 202) as printed**: the centre `0 ∈ O` (a smooth point). -/
theorem hasPoincare_relOpen_of_zero_mem (hconv : Convex ℝ M.O) (h0 : (0 : M.E 0) ∈ M.O)
    (k : ℕ) : (M.toMPolyfold hne).HasPoincare k :=
  hasPoincare_relOpen hM hne hconv h0 M.E.smooth.zero_mem k

end MPolyfoldForm

/-- **2021 Lemma 4.5.2 in the form used for Lemma 4.4.8** (`Poincare448.lean`): every convex
relatively open subset of a partial quadrant with a smooth point has the Poincaré property in
every degree. -/
theorem localPoincare : LocalPoincare := fun _ _ _ hD hne hconv ⟨_, hcD, hc⟩ k =>
  hasPoincare_relOpen (M := LocalModel.ofRelOpen hD) hD hne hconv hcD hc k

/-- **2021 Lemma 4.4.8 (Poincaré Lemma), p. 199**: every `x ∈ X` has open neighbourhoods
`V(x) ⊆ U(x)` such that for every `k`, every closed `[ω] ∈ Ω^{k+1}_∞(U(x))` has
`[τ] ∈ Ωᵏ_∞(V(x))` with `d[τ] = [ω]` on `V(x)` (the text's `k ≥ 1` is `k + 1`).
`lemma_4_4_8_of_local` with Lemma 4.5.2 (`localPoincare`). -/
theorem lemma_4_4_8 (A : BundledMPolyfold.{u}) (x : A.carrier) :
    ∃ (U V : Set A.carrier) (hU : IsOpen U) (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ U),
      ∀ (k : ℕ) (a : (A.openSub hU ⟨x, hVU hxV⟩).formsInfty (k + 1)),
        (A.openSub hU ⟨x, hVU hxV⟩).formsInftyD (k + 1) a = 0 →
        ∃ b : (A.openSub hV ⟨x, hxV⟩).formsInfty k,
          (A.openSub hV ⟨x, hxV⟩).formsInftyD k b =
            A.formsInftyResOpenOpen (k + 1) hU ⟨x, hVU hxV⟩ hV ⟨x, hxV⟩ hVU a :=
  lemma_4_4_8_of_local localPoincare A x

end Polyfold
