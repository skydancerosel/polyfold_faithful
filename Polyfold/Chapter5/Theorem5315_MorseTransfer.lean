import Polyfold.Chapter5.Theorem5315_MorseParam

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3, the proof of
**Theorem 5.3.15** (pp. 224–228; 2017: Theorem 5.8; preprint: Theorem 5.22): comparison of
smooth parametrizations.  Gap G.48.

# Regular points, and the transversality in a larger family

## The text, paraphrased

(Proof of Theorem 5.3.15, p. 227) "Since the section is smooth, there exists an open
neighborhood `U(x)` of `x` in `S` so that, if at `(0, y)` we have `d(t|S)(y) = 0`, then the
linearization of `(λ, z) ↦ d(t|S_λ)(z)` at `(0, y)` is surjective. […] we find finitely many such
points `x₁, …, x_k` […] we denote the union of these sections by `s₁, …, s_d` […] By construction,
the smooth map has, at every point `(0, y)` satisfying `d(t|S)(y) = 0`, a linearization which is
surjective."

## What is formalized

All statements are about smooth parametrizations (`MPolyfold.IsSmoothParam`); two of them are
compared through the transition maps `q' ∘ p`, which are `C^∞`.

* `IsSmoothParam.contDiffOn_comp`, `IsSmoothParam.restrict`.
* `IsSmoothParam.exists_isOpen_regular`: the regular points of `t|A` form an open subset of `A`.
* `IsSmoothParam.isMorseOrRegularPoint_of_regular`, `…_of_regular_of_eq`: a regular point
  satisfies the clause of `HasOnlyMorseCriticalPoints`, also for a set `A'` which coincides with
  `A` near the point.
* `IsSmoothParam.fderivWithin_eq_zero_of_multiplier`: if `A = ι⁻¹(M)` and `t ∘ p_M` has a
  Lagrange multiplier at `ι(x)` with respect to a map `μ` vanishing on `ι(X)`, then `x` is a
  critical point of `t|A`.
* `exists_spanning_of_group` (**the transversality survives in the larger family**): let
  `M₁ ⊆ ℝ × X` be the `j`-th one-parameter slice of `M ⊆ ℝᵏ × X`, both smoothly parametrized
  near `(0, y)`; let the functions `a₀ = 1`, `aᵢ = arctan(i-th coordinate of q₁(0, ·))/2` be built
  from the left inverse `q₁` of the parametrization of `M₁`; and suppose that every Lagrange
  multiplier of `t` on `M₁` at `(0, y)` is non-zero.  Then for every Lagrange multiplier `c` of
  `t` on `M` at `(0, y)`, `c_j ≠ 0` and the forms `Σ δᵢ c_j d(aᵢ ∘ p)`, `Σ δᵢ aᵢ(y) = 0`, restrict
  onto the dual of `ker d(μ ∘ p)`: the hypothesis of `ae_isMorseOrRegularPoint_famSlice`.
-/

open Set Function MeasureTheory Module Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

section Basic

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {A : Set X} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set E} {p : E → X}
  {q : X → E} {G : Set X}

namespace MPolyfold.IsSmoothParam

/-- A map into a finite-dimensional space with sc-smooth components pulls back to a `C^∞` map. -/
lemma contDiffOn_comp {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (h : PX.IsSmoothParam A Ω p q G) {ψ : X → N}
    (hψ : ∀ ℓ : N →L[ℝ] ℝ, PX.IsScSmoothMap realPolyfold fun y => ℓ (ψ y)) :
    ContDiffOn ℝ ∞ (ψ ∘ p) Ω := by
  classical
  set b := Module.finBasis ℝ N with hb
  have heq : ψ ∘ p = fun u =>
      ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)) (ψ (p u)) • b i := by
    funext u
    exact (b.sum_repr (ψ (p u))).symm
  rw [heq]
  exact ContDiffOn.sum fun i _ =>
    (h.smooth_p _ (hψ (LinearMap.toContinuousLinearMap (b.coord i)))).smul contDiffOn_const

lemma exists_isOpen_preimage (h : PX.IsSmoothParam A Ω p q G) {O : Set X} (hO : IsOpen O) :
    ∃ OE : Set E, IsOpen OE ∧ Ω ∩ p ⁻¹' O = Ω ∩ OE := by
  obtain ⟨OE, hOE, heq⟩ := (continuousOn_iff'.1 h.continuousOn_p) O hO
  exact ⟨OE, hOE, by rw [inter_comm, heq, inter_comm]⟩

/-- A smooth parametrization restricted to an open set, for a set `A'` that coincides with `A`
there. -/
lemma restrict (h : PX.IsSmoothParam A Ω p q G) {O : Set X} (hO : IsOpen O) {A' : Set X}
    (hA : A' ∩ (G ∩ O) = A ∩ (G ∩ O)) : PX.IsSmoothParam A' (Ω ∩ p ⁻¹' O) p q (G ∩ O) where
  isOpen_G := h.isOpen_G.inter hO
  continuousOn_p := h.continuousOn_p.mono inter_subset_left
  image_eq := by rw [image_inter_preimage, h.image_eq, hA, inter_assoc]
  left_inv u hu := h.left_inv u hu.1
  smooth_q := h.smooth_q
  smooth_p f hf := (h.smooth_p f hf).mono inter_subset_left

variable [FiniteDimensional ℝ E]

/-- **The regular points of `t|A` form an open subset of `A`.** -/
theorem exists_isOpen_regular (h : PX.IsSmoothParam A Ω p q G) (hΩ : UniqueDiffOn ℝ Ω)
    {t : X → ℝ} (ht : PX.IsScSmoothMap realPolyfold t) {u : E} (hu : u ∈ Ω)
    (hreg : fderivWithin ℝ (t ∘ p) Ω u ≠ 0) :
    ∃ O : Set X, IsOpen O ∧ p u ∈ O ∧ O ⊆ G ∧
      ∀ y ∈ A ∩ O, ∃ u' ∈ Ω, p u' = y ∧ fderivWithin ℝ (t ∘ p) Ω u' ≠ 0 := by
  have hc : ContinuousOn (fderivWithin ℝ (t ∘ p) Ω) Ω :=
    (h.smooth_p t ht).continuousOn_fderivWithin hΩ (by simp)
  obtain ⟨O₁, hO₁, heq⟩ := (continuousOn_iff'.1 hc) {0}ᶜ isOpen_compl_singleton
  have hu₁ : u ∈ O₁ := ((Set.ext_iff.1 heq u).1 ⟨hreg, hu⟩).1
  refine ⟨G ∩ q ⁻¹' O₁, h.isOpen_G.inter (hO₁.preimage h.continuous_q),
    ⟨h.mem_G hu, by rw [mem_preimage, h.left_inv u hu]; exact hu₁⟩, inter_subset_left, ?_⟩
  rintro y ⟨hyA, hyG, hyO⟩
  obtain ⟨u', hu', rfl⟩ : y ∈ p '' Ω := h.image_eq ▸ ⟨hyA, hyG⟩
  rw [mem_preimage, h.left_inv u' hu'] at hyO
  exact ⟨u', hu', rfl, ((Set.ext_iff.1 heq u').2 ⟨hyO, hu'⟩).1⟩

/-- A regular point of `t|A` satisfies the clause of `HasOnlyMorseCriticalPoints`. -/
theorem isMorseOrRegularPoint_of_regular (h : PX.IsSmoothParam A Ω p q G)
    (hΩ : UniqueDiffOn ℝ Ω) {t : X → ℝ} {u : E} (hu : u ∈ Ω)
    (hreg : fderivWithin ℝ (t ∘ p) Ω u ≠ 0) : PX.IsMorseOrRegularPoint A t (p u) := by
  set n := finrank ℝ E with hn
  set e : (Fin n → ℝ) ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [hn]) with he
  have hΩ' : UniqueDiffOn ℝ (e ⁻¹' Ω) := e.uniqueDiffOn_preimage_iff.2 hΩ
  have hmem : e.symm u ∈ e ⁻¹' Ω := by simpa using hu
  refine ⟨n, e ⁻¹' Ω, p ∘ e, e.symm ∘ q, G, e.symm u, h.comp_equiv e, hΩ', hmem, by simp,
    fun h0 => absurd ?_ hreg⟩
  have h1 : fderivWithin ℝ ((t ∘ p) ∘ e) (e ⁻¹' Ω) (e.symm u) =
      (fderivWithin ℝ (t ∘ p) Ω (e (e.symm u))).comp (e : (Fin n → ℝ) →L[ℝ] E) :=
    e.comp_right_fderivWithin (hΩ' _ hmem)
  rw [e.apply_symm_apply] at h1
  refine ContinuousLinearMap.ext fun w => ?_
  have := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (e.symm w)) (h1.symm.trans h0)
  simpa using this

/-- A regular point of `t|A` satisfies the clause of `HasOnlyMorseCriticalPoints` for every set
`A'` that coincides with `A` near the point. -/
theorem isMorseOrRegularPoint_of_regular_of_eq (h : PX.IsSmoothParam A Ω p q G)
    (hΩ : UniqueDiffOn ℝ Ω) {t : X → ℝ} {u : E} (hu : u ∈ Ω)
    (hreg : fderivWithin ℝ (t ∘ p) Ω u ≠ 0) {A' O : Set X} (hO : IsOpen O) (hyO : p u ∈ O)
    (hA : A' ∩ O = A ∩ O) : PX.IsMorseOrRegularPoint A' t (p u) := by
  have hA' : A' ∩ (G ∩ O) = A ∩ (G ∩ O) := by
    rw [inter_comm G O, ← inter_assoc, ← inter_assoc, hA]
  obtain ⟨OE, hOE, heq⟩ := h.exists_isOpen_preimage hO
  have hu' : u ∈ Ω ∩ p ⁻¹' O := ⟨hu, hyO⟩
  have hΩ' : UniqueDiffOn ℝ (Ω ∩ p ⁻¹' O) := by rw [heq]; exact hΩ.inter hOE
  refine (h.restrict hO hA').isMorseOrRegularPoint_of_regular hΩ' hu' ?_
  rw [heq, fderivWithin_inter (hOE.mem_nhds ((Set.ext_iff.1 heq u).1 hu').2)]
  exact hreg

end MPolyfold.IsSmoothParam

end Basic

/-! ### Critical points and Lagrange multipliers -/

section Multiplier

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Z : Type v} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}

lemma MPolyfold.IsSmoothParam.p_q {M : Set Z} {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {ΩM : Set N} {pM : N → Z} {qM : Z → N} {GM : Set Z}
    (hM : PZ.IsSmoothParam M ΩM pM qM GM) {z : Z} (hz : z ∈ M) (hzG : z ∈ GM) :
    qM z ∈ ΩM ∧ pM (qM z) = z := by
  obtain ⟨w, hw, rfl⟩ : z ∈ pM '' ΩM := hM.image_eq ▸ ⟨hz, hzG⟩
  rw [hM.left_inv w hw]
  exact ⟨hw, rfl⟩

/-- **A Lagrange multiplier makes the point critical**: let `A ⊆ X` and `M ⊆ Z` be smoothly
parametrized, `ι : X → Z` sc-smooth with `ι(A) ⊆ M`, and `μ : Z → F` a map with sc-smooth
components vanishing on `ι(X)`.  If at `v` with `p_M(v) = ι(p(u))` the function `T ∘ p_M` has a
Lagrange multiplier with respect to `μ ∘ p_M`, then `u` is a critical point of `(T ∘ ι) ∘ p`. -/
theorem MPolyfold.IsSmoothParam.fderivWithin_eq_zero_of_multiplier {A : Set X} {M : Set Z}
    {E N F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {Ω : Set E} {p : E → X} {q : X → E} {G : Set X}
    (hS : PX.IsSmoothParam A Ω p q G) (hΩ : UniqueDiffOn ℝ Ω) {ΩM : Set N} {pM : N → Z}
    {qM : Z → N} {GM : Set Z} (hM : PZ.IsSmoothParam M ΩM pM qM GM) (hΩM : IsOpen ΩM)
    {ι : X → Z} (hι : PX.IsScSmoothMap PZ ι) (hAM : ∀ y ∈ A, ι y ∈ M) {T : Z → ℝ}
    (hT : PZ.IsScSmoothMap realPolyfold T) {μ : Z → F}
    (hμ : ∀ ℓ : F →L[ℝ] ℝ, PZ.IsScSmoothMap realPolyfold fun z => ℓ (μ z))
    (hμι : ∀ y, μ (ι y) = 0) {u : E} (hu : u ∈ Ω) {v : N} (hv : v ∈ ΩM)
    (hpv : pM v = ι (p u)) {c : F →L[ℝ] ℝ}
    (hc : fderiv ℝ (T ∘ pM) v = c.comp (fderiv ℝ (μ ∘ pM) v)) :
    fderivWithin ℝ ((T ∘ ι) ∘ p) Ω u = 0 := by
  set θ : E → N := (qM ∘ ι) ∘ p with hθ
  have hθc : ContDiffOn ℝ ∞ θ Ω :=
    hS.contDiffOn_comp (ψ := qM ∘ ι) fun ℓ => (hM.smooth_q ℓ).comp hι
  have hθu : θ u = v := by
    change qM (ι (p u)) = v
    rw [← hpv, hM.left_inv v hv]
  have hιc : Continuous ι := continuousOn_univ.1 hι.continuousOn
  have hGev : ∀ᶠ u' in 𝓝[Ω] u, ι (p u') ∈ GM := by
    have hcw : ContinuousWithinAt (ι ∘ p) Ω u :=
      (hιc.comp_continuousOn hS.continuousOn_p).continuousWithinAt hu
    exact hcw.preimage_mem_nhdsWithin
      (hM.isOpen_G.mem_nhds (show ι (p u) ∈ GM from hpv ▸ hM.mem_G hv))
  have hev : ∀ᶠ u' in 𝓝[Ω] u, pM (θ u') = ι (p u') := by
    filter_upwards [hGev, self_mem_nhdsWithin] with u' h1 h2
    exact (hM.p_q (hAM _ (hS.mem_A h2)) h1).2
  have h1 : ((T ∘ ι) ∘ p) =ᶠ[𝓝[Ω] u] (T ∘ pM) ∘ θ := by
    filter_upwards [hev] with u' h
    simp only [Function.comp_apply, h]
  have h2 : (μ ∘ pM) ∘ θ =ᶠ[𝓝[Ω] u] fun _ => (0 : F) := by
    filter_upwards [hev] with u' h
    simp only [Function.comp_apply, h, hμι]
  have hdT : DifferentiableAt ℝ (T ∘ pM) (θ u) := by
    rw [hθu]
    exact ((hM.smooth_p T hT).contDiffAt (hΩM.mem_nhds hv)).differentiableAt (by simp)
  have hdμ : DifferentiableAt ℝ (μ ∘ pM) (θ u) := by
    rw [hθu]
    exact ((hM.contDiffOn_comp hμ).contDiffAt (hΩM.mem_nhds hv)).differentiableAt (by simp)
  have hdθ : DifferentiableWithinAt ℝ θ Ω u := hθc.differentiableOn (by simp) u hu
  have e1 : fderivWithin ℝ ((T ∘ ι) ∘ p) Ω u = fderivWithin ℝ ((T ∘ pM) ∘ θ) Ω u :=
    h1.fderivWithin_eq (by simp only [Function.comp_apply, hθ, ← hpv, hM.left_inv v hv])
  have e2 : fderivWithin ℝ ((μ ∘ pM) ∘ θ) Ω u = 0 := by
    rw [h2.fderivWithin_eq (by simp only [Function.comp_apply, hθu, hpv, hμι])]
    exact fderivWithin_const_apply _
  rw [e1, fderiv_comp_fderivWithin u hdT hdθ (hΩ u hu), hθu, hc, ContinuousLinearMap.comp_assoc]
  have e3 := fderiv_comp_fderivWithin u hdμ hdθ (hΩ u hu)
  rw [hθu] at e3
  rw [← e3, e2, ContinuousLinearMap.comp_zero]

end Multiplier

/-! ### The transversality in a larger family -/

section Group

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {k : ℕ} [ParacompactSpace ((Fin 1 → ℝ) × X)] [ParacompactSpace ((Fin k → ℝ) × X)]

/-- The inclusion `ℝ × X → ℝᵏ × X` of the `j`-th parameter line. -/
def inclJ (j : Fin k) (z : (Fin 1 → ℝ) × X) : (Fin k → ℝ) × X :=
  ((Pi.single j (z.1 0) : Fin k → ℝ), z.2)

/-- The map `ℝᵏ × X → ℝ × X`, `(μ, y) ↦ (0, y)`. -/
def zeroJ (z : (Fin k → ℝ) × X) : (Fin 1 → ℝ) × X := (0, z.2)

omit [ParacompactSpace ((Fin 1 → ℝ) × X)] [ParacompactSpace ((Fin k → ℝ) × X)] in
lemma isScSmoothMap_real_rn_coord (n : ℕ) (i : Fin n) [ParacompactSpace ((Fin n → ℝ) × X)] :
    ((rnPolyfold n).prod PX).IsScSmoothMap realPolyfold fun z => z.1 i :=
  (isScSmoothMap_rn_real_of_contDiff (contDiff_apply ℝ ℝ i)).comp
    (MPolyfold.isScSmoothMap_fst (rnPolyfold n) PX)

lemma isScSmoothMap_inclJ (j : Fin k) :
    ((rnPolyfold 1).prod PX).IsScSmoothMap ((rnPolyfold k).prod PX) (inclJ (X := X) j) := by
  refine MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_rn_of_components fun i => ?_)
    (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)
  by_cases h : i = j
  · have : (fun z : (Fin 1 → ℝ) × X => (Pi.single j (z.1 0) : Fin k → ℝ) i) = fun z => z.1 0 := by
      funext z; rw [h, Pi.single_eq_same]
    rw [this]
    exact isScSmoothMap_real_rn_coord 1 0
  · have : (fun z : (Fin 1 → ℝ) × X => (Pi.single j (z.1 0) : Fin k → ℝ) i) = fun _ => 0 := by
      funext z; rw [Pi.single_eq_of_ne h]
    rw [this]
    exact isScSmoothMap_real_const 0

lemma isScSmoothMap_zeroJ :
    ((rnPolyfold k).prod PX).IsScSmoothMap ((rnPolyfold 1).prod PX) (zeroJ (X := X) (k := k)) :=
  MPolyfold.IsScSmoothOn.prodMk
    (isScSmoothMap_rn_of_components fun _ => isScSmoothMap_real_const 0)
    (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)

/-- **The transversality of one group of sections survives in the larger family** (proof of
2021 Theorem 5.3.15, p. 227: "by construction, the smooth map has at every point `(0, y)`
satisfying `d(t|S)(y) = 0` a linearization which is surjective").  See the header. -/
theorem exists_spanning_of_group {j : Fin k} {M₁ : Set ((Fin 1 → ℝ) × X)}
    {M : Set ((Fin k → ℝ) × X)}
    (hrel : ∀ (μ : Fin 1 → ℝ) (y : X),
      (μ, y) ∈ M₁ ↔ ((Pi.single j (μ 0) : Fin k → ℝ), y) ∈ M)
    {N₁ N : Type*} [NormedAddCommGroup N₁] [NormedSpace ℝ N₁] [FiniteDimensional ℝ N₁]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {Ω₁ : Set N₁} {p₁ : N₁ → (Fin 1 → ℝ) × X} {q₁ : (Fin 1 → ℝ) × X → N₁}
    {G₁ : Set ((Fin 1 → ℝ) × X)} (h₁ : ((rnPolyfold 1).prod PX).IsSmoothParam M₁ Ω₁ p₁ q₁ G₁)
    (hΩ₁ : IsOpen Ω₁) {Ω : Set N} {p : N → (Fin k → ℝ) × X} {q : (Fin k → ℝ) × X → N}
    {G : Set ((Fin k → ℝ) × X)} (hM : ((rnPolyfold k).prod PX).IsSmoothParam M Ω p q G)
    (hΩ : IsOpen Ω) {t : X → ℝ} (ht : PX.IsScSmoothMap realPolyfold t) {v₁ : N₁} (hv₁ : v₁ ∈ Ω₁)
    {v : N} (hv : v ∈ Ω) {y : X} (hp₁ : p₁ v₁ = (0, y)) (hp : p v = (0, y))
    (hmult₁ : ∀ c₁ : (Fin 1 → ℝ) →L[ℝ] ℝ,
      fderiv ℝ (fun w => t (p₁ w).2) v₁ = c₁.comp (fderiv ℝ (fun w => (p₁ w).1) v₁) → c₁ ≠ 0)
    (hsurj : Surjective (fderiv ℝ (fun w => (p w).1) v)) {m : ℕ} (b : Basis (Fin m) ℝ N₁)
    (a : Fin (m + 1) → X → ℝ) (ha0 : a 0 = fun _ => 1)
    (has : ∀ i : Fin m, a i.succ = fun y' => Real.arctan (b.coord i (q₁ (0, y'))) / 2)
    {c : (Fin k → ℝ) →L[ℝ] ℝ}
    (hc : fderiv ℝ (fun w => t (p w).2) v = c.comp (fderiv ℝ (fun w => (p w).1) v))
    (β : N →L[ℝ] ℝ) :
    ∃ δ : Fin (m + 1) → ℝ, ∑ i, δ i * a i y = 0 ∧
      ∀ κ, fderiv ℝ (fun w => (p w).1) v κ = 0 →
        β κ = ∑ i, δ i * (c (Pi.single j 1) * fderiv ℝ (fun w => a i (p w).2) v κ) := by
  classical
  have hsndk := MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX
  have hsnd1 := MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX
  -- the transition maps
  set θ : N₁ → N := (q ∘ inclJ j) ∘ p₁ with hθ
  set ρ : N → N₁ := (q₁ ∘ zeroJ) ∘ p with hρ
  have hθc : ContDiffOn ℝ ∞ θ Ω₁ :=
    h₁.contDiffOn_comp (ψ := q ∘ inclJ j) fun ℓ => (hM.smooth_q ℓ).comp (isScSmoothMap_inclJ j)
  have hρc : ContDiffOn ℝ ∞ ρ Ω :=
    hM.contDiffOn_comp (ψ := q₁ ∘ zeroJ) fun ℓ => (h₁.smooth_q ℓ).comp isScSmoothMap_zeroJ
  have hincl0 : ∀ y' : X, inclJ j ((0 : Fin 1 → ℝ), y') = ((0 : Fin k → ℝ), y') := fun y' => by
    simp [inclJ]
  have hθv : θ v₁ = v := by
    change q (inclJ j (p₁ v₁)) = v
    rw [hp₁, hincl0, ← hp, hM.left_inv v hv]
  have hρv : ρ v = v₁ := by
    change q₁ (zeroJ (p v)) = v₁
    rw [hp]; change q₁ (0, y) = v₁
    rw [← hp₁, h₁.left_inv v₁ hv₁]
  have hθd : HasFDerivAt θ (fderiv ℝ θ v₁) v₁ :=
    ((hθc.contDiffAt (hΩ₁.mem_nhds hv₁)).differentiableAt (by simp)).hasFDerivAt
  have hρd : HasFDerivAt ρ (fderiv ℝ ρ v) v :=
    ((hρc.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)).hasFDerivAt
  have hinclc : Continuous (inclJ (X := X) j) :=
    continuousOn_univ.1 (isScSmoothMap_inclJ (PX := PX) j).continuousOn
  have hzeroc : Continuous (zeroJ (X := X) (k := k)) :=
    continuousOn_univ.1 (isScSmoothMap_zeroJ (PX := PX)).continuousOn
  -- `p ∘ θ = inclJ ∘ p₁` near `v₁`
  have hθev : ∀ᶠ w in 𝓝 v₁, p (θ w) = inclJ j (p₁ w) := by
    have hcw : ContinuousAt (inclJ j ∘ p₁) v₁ :=
      (hinclc.comp_continuousOn h₁.continuousOn_p).continuousAt (hΩ₁.mem_nhds hv₁)
    have hG : (inclJ j ∘ p₁) v₁ ∈ G := by
      change inclJ j (p₁ v₁) ∈ G
      rw [hp₁, hincl0, ← hp]; exact hM.mem_G hv
    filter_upwards [hcw.preimage_mem_nhds (hM.isOpen_G.mem_nhds hG), hΩ₁.mem_nhds hv₁]
      with w hwG hwΩ
    have hwM : inclJ j (p₁ w) ∈ M := (hrel (p₁ w).1 (p₁ w).2).1 (h₁.mem_A hwΩ)
    exact (hM.p_q hwM hwG).2
  -- `θ ∘ ρ = id` on the level set `{μ = 0}` near `v`
  have hρev : ∀ᶠ w in 𝓝 v, (p w).1 = 0 → θ (ρ w) = w := by
    have hcw : ContinuousAt (zeroJ ∘ p) v :=
      (hzeroc.comp_continuousOn hM.continuousOn_p).continuousAt (hΩ.mem_nhds hv)
    have hG : (zeroJ ∘ p) v ∈ G₁ := by
      change zeroJ (p v) ∈ G₁
      rw [hp]; change ((0 : Fin 1 → ℝ), y) ∈ G₁
      rw [← hp₁]; exact h₁.mem_G hv₁
    filter_upwards [hcw.preimage_mem_nhds (h₁.isOpen_G.mem_nhds hG), hΩ.mem_nhds hv]
      with w hwG hwΩ hw0
    have hpw : p w = (0, (p w).2) := Prod.ext hw0 rfl
    have hwM₁ : zeroJ (p w) ∈ M₁ := by
      change ((0 : Fin 1 → ℝ), (p w).2) ∈ M₁
      rw [hrel]
      simp only [Pi.zero_apply, Pi.single_zero]
      rw [← hpw]; exact hM.mem_A hwΩ
    have h3 := (h₁.p_q hwM₁ hwG).2
    change q (inclJ j (p₁ (q₁ (zeroJ (p w))))) = w
    rw [h3]
    change q (inclJ j ((0 : Fin 1 → ℝ), (p w).2)) = w
    rw [hincl0, ← hpw, hM.left_inv w hwΩ]
  -- derivatives transported by `θ`
  have hμ1 : ContDiffOn ℝ ∞ (fun w => (p₁ w).1) Ω₁ := contDiffOn_pi.2 fun i =>
    h₁.smooth_p (fun z => z.1 i) (isScSmoothMap_real_rn_coord 1 i)
  have hμk : ContDiffOn ℝ ∞ (fun w => (p w).1) Ω := contDiffOn_pi.2 fun i =>
    hM.smooth_p (fun z => z.1 i) (isScSmoothMap_real_rn_coord k i)
  have hμkd : DifferentiableAt ℝ (fun w => (p w).1) v :=
    (hμk.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  have hμ1d : DifferentiableAt ℝ (fun w => (p₁ w).1) v₁ :=
    (hμ1.contDiffAt (hΩ₁.mem_nhds hv₁)).differentiableAt (by simp)
  have hTk : DifferentiableAt ℝ (fun w => t (p w).2) v :=
    ((hM.smooth_p (t ∘ Prod.snd) (ht.comp hsndk)).contDiffAt
      (hΩ.mem_nhds hv)).differentiableAt (by simp)
  set Lj : (Fin 1 → ℝ) →L[ℝ] (Fin k → ℝ) :=
    (ContinuousLinearMap.single ℝ (fun _ : Fin k => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) with hLj
  have hLj1 : ∀ μ : Fin 1 → ℝ, Lj μ = (Pi.single j (μ 0) : Fin k → ℝ) := fun μ => rfl
  have a1 : ∀ w, fderiv ℝ (fun w => (p w).1) v (fderiv ℝ θ v₁ w) =
      (Pi.single j (fderiv ℝ (fun w => (p₁ w).1) v₁ w 0) : Fin k → ℝ) := by
    intro w
    have e1 : (fun w => (p w).1) ∘ θ =ᶠ[𝓝 v₁] Lj ∘ fun w => (p₁ w).1 := by
      filter_upwards [hθev] with w' hw'
      simp only [Function.comp_apply, hw', hLj1]; rfl
    have e2 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) e1
    rw [fderiv_comp v₁ (hθv ▸ hμkd) hθd.differentiableAt, hθv,
      (Lj.hasFDerivAt.comp v₁ hμ1d.hasFDerivAt).fderiv] at e2
    have := congrArg (fun L : N₁ →L[ℝ] (Fin k → ℝ) => L w) e2
    simpa [hLj1] using this
  have a2 : ∀ w, fderiv ℝ (fun w => t (p w).2) v (fderiv ℝ θ v₁ w) =
      fderiv ℝ (fun w => t (p₁ w).2) v₁ w := by
    intro w
    have e1 : (fun w => t (p w).2) ∘ θ =ᶠ[𝓝 v₁] fun w => t (p₁ w).2 := by
      filter_upwards [hθev] with w' hw'
      simp only [Function.comp_apply, hw']; rfl
    have e2 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) e1
    rw [fderiv_comp v₁ (hθv ▸ hTk) hθd.differentiableAt, hθv] at e2
    exact congrArg (fun L : N₁ →L[ℝ] ℝ => L w) e2
  -- the `j`-th component of the multiplier is not zero
  have hcj : c (Pi.single j 1) ≠ 0 := by
    intro h0
    refine hmult₁ (c (Pi.single j 1) • ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 1 => ℝ) 0) (ContinuousLinearMap.ext fun w => ?_) (by rw [h0, zero_smul])
    rw [← a2 w, hc, ContinuousLinearMap.comp_apply, a1 w]
    have hs : (Pi.single j (fderiv ℝ (fun w => (p₁ w).1) v₁ w 0) : Fin k → ℝ) =
        (fderiv ℝ (fun w => (p₁ w).1) v₁ w 0) • (Pi.single j (1 : ℝ) : Fin k → ℝ) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hs, c.map_smul]
    simp [mul_comm]
  -- the level set `{μ = 0}` near `v`
  have hv0 : (p v).1 = 0 := by rw [hp]
  obtain ⟨K, Ωγ, γ, π, Ω'', hK, hΩγ, -, hΩ''Ω, -, h0γ, hγ0, hγc, himg, -, hrange⟩ :=
    exists_levelSet_param hΩ hμk hv hv0 hsurj
  have hγd : HasFDerivAt γ (fderiv ℝ γ 0) 0 :=
    ((hγc.contDiffAt (hΩγ.mem_nhds h0γ)).differentiableAt (by simp)).hasFDerivAt
  have hfix : ∀ κ, fderiv ℝ (fun w => (p w).1) v κ = 0 →
      fderiv ℝ θ v₁ (fderiv ℝ ρ v κ) = κ := by
    intro κ hκ
    obtain ⟨a', ha'⟩ := hrange 0 h0γ κ (by rw [hγ0]; exact hκ)
    have hev : (θ ∘ ρ) ∘ γ =ᶠ[𝓝 0] γ := by
      have h1 : ∀ᶠ u in 𝓝 (0 : K), (p (γ u)).1 = 0 → θ (ρ (γ u)) = γ u :=
        hγd.continuousAt.eventually (by rw [hγ0]; exact hρev)
      filter_upwards [h1, hΩγ.mem_nhds h0γ] with u hu huΩ
      exact hu (himg ▸ mem_image_of_mem γ huΩ : γ u ∈ {x | x ∈ Ω'' ∧ (p x).1 = 0}).2
    have e1 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev
    have hθρ : HasFDerivAt (θ ∘ ρ) ((fderiv ℝ θ v₁).comp (fderiv ℝ ρ v)) (γ 0) := by
      rw [hγ0]
      exact (hρv.symm ▸ hθd : HasFDerivAt θ (fderiv ℝ θ v₁) (ρ v)).comp v hρd
    rw [(hθρ.comp 0 hγd).fderiv] at e1
    have := congrArg (fun L : K →L[ℝ] N => L a') e1
    simpa [ha'] using this
  -- the coefficients
  set βt : N₁ →L[ℝ] ℝ := β.comp (fderiv ℝ θ v₁) with hβt
  set xi : Fin m → ℝ := fun i => b.coord i v₁ with hxi
  set dd : Fin m → ℝ := fun i => βt (b i) * (2 * (1 + xi i ^ 2)) / c (Pi.single j 1) with hdd
  refine ⟨Fin.cons (-∑ i, dd i * a i.succ y) dd, ?_, fun κ hκ => ?_⟩
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, ha0]
    ring
  · have hd0 : fderiv ℝ (fun w => a 0 (p w).2) v κ = 0 := by
      rw [ha0]; simp
    have hds : ∀ i : Fin m, fderiv ℝ (fun w => a i.succ (p w).2) v κ =
        (1 / (1 + xi i ^ 2) / 2) * b.coord i (fderiv ℝ ρ v κ) := by
      intro i
      set ℓ : N₁ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i) with hℓ
      have hfun : (fun w => a i.succ (p w).2) = (fun r => Real.arctan r / 2) ∘ (ℓ ∘ ρ) := by
        funext w; rw [has i]; rfl
      have h1 : HasFDerivAt (ℓ ∘ ρ) (ℓ.comp (fderiv ℝ ρ v)) v := ℓ.hasFDerivAt.comp v hρd
      have h2 := ((Real.hasDerivAt_arctan ((ℓ ∘ ρ) v)).div_const 2).comp_hasFDerivAt v h1
      rw [hfun, h2.fderiv]
      have hval : (ℓ ∘ ρ) v = xi i := by
        change b.coord i (ρ v) = b.coord i v₁
        rw [hρv]
      rw [hval]
      rfl
    have hβκ : β κ = ∑ i, βt (b i) * b.coord i (fderiv ℝ ρ v κ) := by
      have h1 : β κ = βt (fderiv ℝ ρ v κ) := by
        rw [hβt, ContinuousLinearMap.comp_apply, hfix κ hκ]
      rw [h1]
      conv_lhs => rw [← b.sum_repr (fderiv ℝ ρ v κ)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, hd0, hds, mul_zero, zero_add]
    rw [hβκ]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpos : (1 + xi i ^ 2) ≠ 0 := by positivity
    simp only [hdd]
    field_simp

end Group

end Polyfold
