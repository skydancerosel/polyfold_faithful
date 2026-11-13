import Polyfold.Chapter5.Theorem5315_MorseFamily
import Polyfold.Chapter5.CylinderPerturbation2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3,
**Theorem 5.3.15 (2)** (p. 223; 2017: Theorem 5.8; preprint: Theorem 5.22): the notion
"`t : S → [0, 1]` has only Morse-type critical points" for a finite-dimensional submanifold `S`
of an M-polyfold, and the local genericity statement behind it.  Gap G.48.

# Morse-type critical points on a submanifold of an M-polyfold

## The text, paraphrased

(Theorem 5.3.15 (2)) The smooth function `t : S_{f+s₀} → [0, 1]` has only Morse-type critical
points.  (Proof, p. 224) "`t ∘ Φ_λ` will be a Morse function on `S`; since `Φ_λ : S → S_λ` is a
diffeomorphism, `t|S_λ` is a Morse function."

## What is formalized

* `MPolyfold.IsSmoothParam A Ω p q G` (**a smooth parametrization of `A ∩ G`**): `G ⊆ X` open,
  `p : E → X` maps `Ω ⊆ E` (`E` a finite-dimensional normed space) onto `A ∩ G`, `q : X → E` is a
  left inverse of `p` on `Ω` whose components are sc-smooth functions on `X`, and `h ∘ p` is
  `C^∞` on `Ω` for every sc-smooth function `h : X → ℝ`.
* `MPolyfold.IsMorseOrRegularPoint A t x`: there is a smooth parametrization of `A` around
  `x = p(u₀)` by a set `Ω ⊆ ℝⁿ` with unique derivatives, such that if `u₀` is a critical point of
  `t ∘ p` on `Ω` then `u₀` is an interior point of `Ω` and the Hessian of `t ∘ p` at `u₀` is
  injective.  `MPolyfold.HasOnlyMorseCriticalPoints A t`: this holds at every point of `A`.
* `MPolyfold.IsSmoothParam.of_levelSet`: a parametrization of a level set inside a parametrized
  set `M ⊆ Z` gives a parametrization of `Φ⁻¹(M)` for a section `Φ : X → Z` of an sc-smooth
  `pr : Z → X`.
* `ae_isMorseOrRegularPoint_famSlice` (**the local statement of the proof**): let `M ⊆ ℝᵏ × X`
  be parametrized near `(0, y₀)`, and `S_λ = {y | (Λ(λ, y), y) ∈ M}` with
  `Λ(λ, y)_j = Σ_{g(i) = j} λᵢ aᵢ(y)` (`famShift`; this is the solution set of
  `f + Σ λᵢ aᵢ σ_{g(i)}` when `M` is the solution set of `(μ, y) ↦ f(y) + Σ μ_j σ_j(y)`).  If `μ`
  is a submersion on `M` at `(0, y₀)` and the transversality condition of
  `ae_isLagrangeNondegenerate_family` holds there, then there are `ε > 0` and an open `O ∋ y₀`
  such that for almost every `λ` with `|λ| < ε` every point of `S_λ ∩ O` is a regular point or a
  Morse-type critical point of `t|S_λ`.

## What the text leaves implicit, and the choices made

* "Morse-type critical point" is not defined in the text; `S` is a manifold with boundary and
  `t|S` has no critical points on `∂S`, so the notion is the usual one at interior points:
  non-degenerate Hessian in a chart.  A chart of `S` is here a smooth parametrization
  (`IsSmoothParam`): `p` is a bijection of `Ω` onto the open piece `A ∩ G` of `A`, its inverse is
  the restriction of an sc-smooth map `q` on `X`, and `p` is smooth in the sense that it pulls
  sc-smooth functions back to `C^∞` functions.  Two such parametrizations differ by a `C^∞`
  diffeomorphism (`q' ∘ p`), and non-degeneracy of the Hessian at a critical point does not depend
  on the chart.  At a boundary point the set `Ω` is not open and the clause asks that the point is
  not critical.
-/

open Set Function MeasureTheory Module Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### Smooth parametrizations -/

section Param

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- **A smooth parametrization of an open piece `A ∩ G` of a subset `A` of an M-polyfold** by a
subset `Ω` of a normed space `E`: `p` is continuous on `Ω` and maps it onto `A ∩ G` (`G` open in
`X`), `q : X → E` is a
left inverse of `p` on `Ω` with sc-smooth components, and `p` pulls sc-smooth functions on `X`
back to `C^∞` functions on `Ω`. -/
structure MPolyfold.IsSmoothParam (PX : MPolyfold X) (A : Set X) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : Set E) (p : E → X) (q : X → E) (G : Set X) :
    Prop where
  isOpen_G : IsOpen G
  continuousOn_p : ContinuousOn p Ω
  image_eq : p '' Ω = A ∩ G
  left_inv : ∀ u ∈ Ω, q (p u) = u
  smooth_q : ∀ ℓ : E →L[ℝ] ℝ, PX.IsScSmoothMap realPolyfold fun y => ℓ (q y)
  smooth_p : ∀ h : X → ℝ, PX.IsScSmoothMap realPolyfold h → ContDiffOn ℝ ∞ (h ∘ p) Ω

variable {PX : MPolyfold X} {A : Set X}

namespace MPolyfold.IsSmoothParam

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set E} {p : E → X}
  {q : X → E} {G : Set X}

lemma mem_A (h : PX.IsSmoothParam A Ω p q G) {u : E} (hu : u ∈ Ω) : p u ∈ A :=
  (h.image_eq ▸ mem_image_of_mem p hu : p u ∈ A ∩ G).1

lemma mem_G (h : PX.IsSmoothParam A Ω p q G) {u : E} (hu : u ∈ Ω) : p u ∈ G :=
  (h.image_eq ▸ mem_image_of_mem p hu : p u ∈ A ∩ G).2

/-- The left inverse `q` is continuous. -/
lemma continuous_q [FiniteDimensional ℝ E] (h : PX.IsSmoothParam A Ω p q G) : Continuous q := by
  classical
  set b := Module.finBasis ℝ E with hb
  have hq : q = fun y => ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)) (q y) • b i := by
    funext y
    exact (b.sum_repr (q y)).symm
  rw [hq]
  exact continuous_finsetSum _ fun i _ =>
    (continuousOn_univ.1
      (h.smooth_q (LinearMap.toContinuousLinearMap (b.coord i))).continuousOn).smul
      continuous_const

/-- A smooth parametrization read through a linear isomorphism of the parameter space. -/
lemma comp_equiv {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (h : PX.IsSmoothParam A Ω p q G) (e : E' ≃L[ℝ] E) :
    PX.IsSmoothParam A (e ⁻¹' Ω) (p ∘ e) (e.symm ∘ q) G where
  isOpen_G := h.isOpen_G
  continuousOn_p := h.continuousOn_p.comp e.continuous.continuousOn fun u hu => hu
  image_eq := by
    rw [image_comp, image_preimage_eq _ e.surjective]
    exact h.image_eq
  left_inv u hu := by
    change e.symm (q (p (e u))) = u
    rw [h.left_inv (e u) hu, e.symm_apply_apply]
  smooth_q ℓ := h.smooth_q (ℓ.comp (e.symm : E →L[ℝ] E'))
  smooth_p f hf := (h.smooth_p f hf).comp e.contDiff.contDiffOn fun u hu => hu

end MPolyfold.IsSmoothParam

/-- **A regular point or a Morse-type critical point of `t|A`** (2021 Theorem 5.3.15 (2),
p. 223): there is a smooth parametrization `p` of `A` around `x = p(u₀)`, defined on a set
`Ω ⊆ ℝⁿ` with unique derivatives, such that if `d(t ∘ p)(u₀) = 0` then `Ω` is a neighbourhood of
`u₀` (an interior point of the manifold `A`) and the Hessian of `t ∘ p` at `u₀` is injective. -/
def MPolyfold.IsMorseOrRegularPoint (PX : MPolyfold X) (A : Set X) (t : X → ℝ) (x : X) : Prop :=
  ∃ (n : ℕ) (Ω : Set (Fin n → ℝ)) (p : (Fin n → ℝ) → X) (q : X → Fin n → ℝ) (G : Set X)
    (u₀ : Fin n → ℝ), PX.IsSmoothParam A Ω p q G ∧ UniqueDiffOn ℝ Ω ∧ u₀ ∈ Ω ∧ p u₀ = x ∧
      (fderivWithin ℝ (t ∘ p) Ω u₀ = 0 →
        Ω ∈ 𝓝 u₀ ∧ Injective (fderiv ℝ (fderiv ℝ (t ∘ p)) u₀))

/-- **2021 Theorem 5.3.15 (2), p. 223**: the function `t` on the submanifold `A` has only
Morse-type critical points. -/
def MPolyfold.HasOnlyMorseCriticalPoints (PX : MPolyfold X) (A : Set X) (t : X → ℝ) : Prop :=
  ∀ x ∈ A, PX.IsMorseOrRegularPoint A t x

/-- The clause `IsMorseOrRegularPoint` from a parametrization by an open subset of any
finite-dimensional space. -/
theorem MPolyfold.isMorseOrRegularPoint_of_param {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Ω : Set E} {p : E → X} {q : X → E} {G : Set X}
    (hpar : PX.IsSmoothParam A Ω p q G) (hΩ : IsOpen Ω) {u₀ : E} (hu : u₀ ∈ Ω) {t : X → ℝ}
    (ht : PX.IsScSmoothMap realPolyfold t)
    (hcrit : fderiv ℝ (t ∘ p) u₀ = 0 → Injective (fderiv ℝ (fderiv ℝ (t ∘ p)) u₀)) :
    PX.IsMorseOrRegularPoint A t (p u₀) := by
  set n := finrank ℝ E with hn
  set e : (Fin n → ℝ) ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [hn]) with he
  have hΩ' : IsOpen (e ⁻¹' Ω) := hΩ.preimage e.continuous
  have hmem : e.symm u₀ ∈ e ⁻¹' Ω := by simpa using hu
  refine ⟨n, e ⁻¹' Ω, p ∘ e, e.symm ∘ q, G, e.symm u₀, hpar.comp_equiv e, hΩ'.uniqueDiffOn, hmem,
    by simp, fun h0 => ⟨hΩ'.mem_nhds hmem, ?_⟩⟩
  set g := t ∘ p with hg
  have hgc : ContDiffAt ℝ 2 g (e (e.symm u₀)) := by
    rw [e.apply_symm_apply]
    exact ((hpar.smooth_p t ht).contDiffAt (hΩ.mem_nhds hu)).of_le (by decide)
  have hec : ContDiffAt ℝ 2 (e : (Fin n → ℝ) → E) (e.symm u₀) := e.contDiff.contDiffAt
  have hed : ∀ x : Fin n → ℝ, fderiv ℝ (e : (Fin n → ℝ) → E) (e.symm u₀) x = e x := fun x => by
    rw [e.fderiv]; rfl
  have hcomp : t ∘ (p ∘ e) = g ∘ e := rfl
  rw [hcomp] at h0 ⊢
  rw [fderivWithin_of_isOpen hΩ' hmem] at h0
  have h1 : fderiv ℝ (g ∘ e) (e.symm u₀) =
      (fderiv ℝ g (e (e.symm u₀))).comp (fderiv ℝ (e : (Fin n → ℝ) → E) (e.symm u₀)) :=
    fderiv_comp _ (hgc.differentiableAt (by norm_num)) (hec.differentiableAt (by norm_num))
  have hg0 : fderiv ℝ g (e (e.symm u₀)) = 0 := by
    refine ContinuousLinearMap.ext fun w => ?_
    have := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (e.symm w)) (h1.symm.trans h0)
    simpa [hed] using this
  have hinj := hcrit (by rw [← e.apply_symm_apply u₀]; exact hg0)
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h2 : fderiv ℝ (fderiv ℝ g) u₀ (e x) = 0 := by
    refine ContinuousLinearMap.ext fun w => ?_
    have h3 := fderiv_fderiv_comp_apply hgc hec x (e.symm w)
    rw [hx, hg0, hed, hed, e.apply_symm_apply] at h3
    simpa using h3.symm
  have h4 := hinj (h2.trans (map_zero _).symm)
  exact e.injective (h4.trans (map_zero e).symm)

/-- **A parametrization of a level set gives a parametrization of the slice**: let `M ⊆ Z` be
parametrized by `p : Ω → M ∩ G`, let `Φ : X → Z` be an sc-smooth section of the sc-smooth
`pr : Z → X`, and let `γ : Ωγ → Ω''` (with affine left inverse `x ↦ π(x − v)`) parametrize the set
of the `x ∈ Ω''` with `p(x) ∈ Φ(X)`.  Then `pr ∘ p ∘ γ` parametrizes `Φ⁻¹(M)`. -/
theorem MPolyfold.IsSmoothParam.of_levelSet {Z : Type v} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] {PZ : MPolyfold Z} {M : Set Z} {N K : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] [NormedAddCommGroup K] [NormedSpace ℝ K]
    {Ω : Set N} {p : N → Z} {q : Z → N} {G : Set Z} (hpar : PZ.IsSmoothParam M Ω p q G)
    {Φ : X → Z} (hΦ : PX.IsScSmoothMap PZ Φ) {pr : Z → X} (hpr : PZ.IsScSmoothMap PX pr)
    (hprΦ : ∀ y, pr (Φ y) = y) {Ωγ : Set K} {γ : K → N} (π : N →L[ℝ] K) (v : N) {Ω'' : Set N}
    (hΩ'' : IsOpen Ω'') (hΩ''Ω : Ω'' ⊆ Ω) (hγ : ContDiffOn ℝ ∞ γ Ωγ)
    (himg : γ '' Ωγ = {x | x ∈ Ω'' ∧ Φ (pr (p x)) = p x})
    (hleft : ∀ u ∈ Ωγ, π (γ u - v) = u) :
    PX.IsSmoothParam (Φ ⁻¹' M) Ωγ (pr ∘ p ∘ γ) (fun y => π (q (Φ y) - v))
      (Φ ⁻¹' (G ∩ q ⁻¹' Ω'')) where
  isOpen_G := (hpar.isOpen_G.inter (hΩ''.preimage hpar.continuous_q)).preimage
    (continuousOn_univ.1 hΦ.continuousOn)
  continuousOn_p :=
    (continuousOn_univ.1 hpr.continuousOn).comp_continuousOn
      (hpar.continuousOn_p.comp hγ.continuousOn fun u hu =>
        hΩ''Ω (himg ▸ mem_image_of_mem γ hu : γ u ∈ {x | x ∈ Ω'' ∧ Φ (pr (p x)) = p x}).1)
  image_eq := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨hx, hfix⟩ : γ u ∈ {x | x ∈ Ω'' ∧ Φ (pr (p x)) = p x} := himg ▸ mem_image_of_mem γ hu
      change Φ (pr (p (γ u))) ∈ M ∧ Φ (pr (p (γ u))) ∈ G ∧ q (Φ (pr (p (γ u)))) ∈ Ω''
      rw [hfix, hpar.left_inv _ (hΩ''Ω hx)]
      exact ⟨hpar.mem_A (hΩ''Ω hx), hpar.mem_G (hΩ''Ω hx), hx⟩
    · rintro ⟨hyM, hyG, hyΩ⟩
      obtain ⟨x, hx, hpx⟩ : Φ y ∈ p '' Ω := hpar.image_eq ▸ ⟨hyM, hyG⟩
      have hqx : q (Φ y) = x := by rw [← hpx, hpar.left_inv x hx]
      have hxΩ : x ∈ Ω'' := hqx ▸ hyΩ
      have hmem : x ∈ γ '' Ωγ := by
        rw [himg]
        exact ⟨hxΩ, by rw [hpx, hprΦ]⟩
      obtain ⟨u, hu, rfl⟩ := hmem
      exact ⟨u, hu, by change pr (p (γ u)) = y; rw [hpx, hprΦ]⟩
  left_inv u hu := by
    obtain ⟨hx, hfix⟩ : γ u ∈ {x | x ∈ Ω'' ∧ Φ (pr (p x)) = p x} := himg ▸ mem_image_of_mem γ hu
    change π (q (Φ (pr (p (γ u)))) - v) = u
    rw [hfix, hpar.left_inv _ (hΩ''Ω hx), hleft u hu]
  smooth_q ℓ := by
    have h1 : PX.IsScSmoothMap realPolyfold fun y => (ℓ.comp π) (q (Φ y)) :=
      (hpar.smooth_q (ℓ.comp π)).comp hΦ
    have h2 := h1.real_sub (isScSmoothMap_real_const ((ℓ.comp π) v))
    have heq : (fun y => ℓ (π (q (Φ y) - v))) =
        fun y => (ℓ.comp π) (q (Φ y)) - (ℓ.comp π) v := by
      funext y; simp
    rw [heq]; exact h2
  smooth_p f hf := by
    have h1 : ContDiffOn ℝ ∞ ((f ∘ pr) ∘ p) Ω := hpar.smooth_p (f ∘ pr) (hf.comp hpr)
    have hmaps : MapsTo γ Ωγ Ω := fun u hu =>
      hΩ''Ω (himg ▸ mem_image_of_mem γ hu : γ u ∈ {x | x ∈ Ω'' ∧ Φ (pr (p x)) = p x}).1
    exact h1.comp hγ hmaps

end Param

/-! ### Maps into `ℝᵏ` and the shift of the family -/

section Shift

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- A map into `ℝᵏ` with sc-smooth components is sc-smooth. -/
theorem isScSmoothMap_rn_of_components {k : ℕ} {f : X → Fin k → ℝ}
    (hf : ∀ j, PX.IsScSmoothMap realPolyfold fun x => f x j) :
    PX.IsScSmoothMap (rnPolyfold k) f := by
  classical
  refine MPolyfold.isScSmoothMap_of_local fun x => ?_
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source x
  refine ⟨φ, rnChart k 0, φ.source, hφ, isChart_rnChart 0, φ.isOpen_source, hx, subset_rfl,
    mapsTo_univ _ _, mapsTo_univ _ _, fun R hR => ?_⟩
  have hj : ∀ j, IsScSmooth (F := ScBanach.const ℝ) R.U (((fun x => f x j) ∘ φ.symm) ∘ R) :=
    fun j => ((hf j).real_chart_on hφ φ.isOpen_source subset_rfl).comp_isScSmooth R hR
  have hc : ∀ j : Fin k, IsScSmooth (F := rnSc k) R.U fun _ => (Pi.single j (1 : ℝ) : Fin k → ℝ) :=
    fun j => IsScSmooth.of_contDiffOn_finiteDimensional R.isScDomain contDiffOn_const
  have hsum : IsScSmooth (F := rnSc k) R.U fun u =>
      ∑ j, (((fun x => f x j) ∘ φ.symm) ∘ R) u • (Pi.single j (1 : ℝ) : Fin k → ℝ) :=
    IsScSmooth.finsetSum R.isScDomain _ fun j _ => (hj j).smul R.isScDomain (hc j)
  refine hsum.congr R.isScDomain fun u _ => ?_
  change ∑ j, f (φ.symm (R u)) j • (Pi.single j (1 : ℝ) : Fin k → ℝ) = f (φ.symm (R u)) - 0
  rw [sub_zero]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

variable {d k : ℕ}

/-- **The shift `Λ(λ, y) ∈ ℝᵏ` of the family**, `Λ(λ, y)_j = Σ_{g(i) = j} λᵢ aᵢ(y)`: the section
`f + Σ λᵢ aᵢ σ_{g(i)}` is `f + Σ_j Λ(λ, ·)_j σ_j`. -/
def famShift (a : Fin d → X → ℝ) (g : Fin d → Fin k) (lam : Fin d → ℝ) (y : X) : Fin k → ℝ :=
  ∑ i, (lam i * a i y) • (Pi.single (g i) (1 : ℝ) : Fin k → ℝ)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
lemma famShift_zero (a : Fin d → X → ℝ) (g : Fin d → Fin k) (y : X) :
    famShift a g (0 : Fin d → ℝ) y = 0 := by
  simp [famShift]

lemma isScSmoothMap_famShift {a : Fin d → X → ℝ}
    (ha : ∀ i, PX.IsScSmoothMap realPolyfold (a i)) (g : Fin d → Fin k) (lam : Fin d → ℝ) :
    PX.IsScSmoothMap (rnPolyfold k) (famShift a g lam) := by
  refine isScSmoothMap_rn_of_components fun j => ?_
  have h1 : (fun x => famShift a g lam x j) =
      fun x => ∑ i, (lam i * a i x) * (Pi.single (g i) (1 : ℝ) : Fin k → ℝ) j := by
    funext x; simp [famShift, Finset.sum_apply]
  rw [h1]
  exact isScSmoothMap_real_finsetSum _ fun i _ =>
    ((isScSmoothMap_real_const (lam i)).real_mul (ha i)).real_mul (isScSmoothMap_real_const _)

omit [T2Space X] [ParacompactSpace X] in
lemma continuous_famShift {a : Fin d → X → ℝ} (ha : ∀ i, Continuous (a i)) (g : Fin d → Fin k) :
    Continuous fun p : (Fin d → ℝ) × X => famShift a g p.1 p.2 :=
  continuous_finsetSum _ fun i _ =>
    ((((continuous_apply i).comp continuous_fst).mul ((ha i).comp continuous_snd))).smul
      continuous_const

end Shift

/-! ### The local statement -/

section Local

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {d k : ℕ} [ParacompactSpace ((Fin k → ℝ) × X)]

/-- **Generic Morse-type critical points on the slices of a parametrized family, locally**
(proof of 2021 Theorem 5.3.15, pp. 224–228): let `M ⊆ ℝᵏ × X` be smoothly parametrized by
`p : Ω → M ∩ G`, `Ω` open in a finite-dimensional space, `p(v₀) = (0, y₀)`; let `t` and
`a₁, …, a_d` be sc-smooth functions on `X` and `S_λ = {y | (Λ(λ, y), y) ∈ M}`,
`Λ(λ, y)_j = Σ_{g(i) = j} λᵢ aᵢ(y)`.  Suppose that `μ ∘ p` has a surjective derivative at `v₀`
(`μ` the projection to `ℝᵏ`), and that for every `c` with `d(t ∘ p)(v₀) = c ∘ d(μ ∘ p)(v₀)` the
forms `Σ δᵢ c_{g(i)} d(aᵢ ∘ p)(v₀)`, over the `δ` with `Λ(δ, y₀) = 0`, restrict onto the dual of
`ker d(μ ∘ p)(v₀)`.  Then there are `ε > 0` and an open `O ∋ y₀` such that for almost every `λ`
with `|λ| < ε` every point of `S_λ ∩ O` is a regular point or a Morse-type critical point of
`t|S_λ`. -/
theorem ae_isMorseOrRegularPoint_famSlice {M : Set ((Fin k → ℝ) × X)} {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] {Ω : Set N}
    {p : N → (Fin k → ℝ) × X} {q : (Fin k → ℝ) × X → N} {G : Set ((Fin k → ℝ) × X)}
    (hpar : ((rnPolyfold k).prod PX).IsSmoothParam M Ω p q G) (hΩ : IsOpen Ω) {t : X → ℝ}
    (ht : PX.IsScSmoothMap realPolyfold t) {a : Fin d → X → ℝ}
    (ha : ∀ i, PX.IsScSmoothMap realPolyfold (a i)) (g : Fin d → Fin k) {v₀ : N} (hv₀ : v₀ ∈ Ω)
    {y₀ : X} (hpv₀ : p v₀ = (0, y₀))
    (hsurj : Surjective (fderiv ℝ (fun v => (p v).1) v₀))
    (hSC : ∀ c : (Fin k → ℝ) →L[ℝ] ℝ,
      fderiv ℝ (fun v => t (p v).2) v₀ = c.comp (fderiv ℝ (fun v => (p v).1) v₀) →
      ∀ β : N →L[ℝ] ℝ, ∃ δ : Fin d → ℝ, famShift a g δ y₀ = 0 ∧
        ∀ κ, fderiv ℝ (fun v => (p v).1) v₀ κ = 0 →
          β κ = ∑ i, δ i * (c (Pi.single (g i) 1) * fderiv ℝ (fun v => a i (p v).2) v₀ κ)) :
    ∃ ε > 0, ∃ O : Set X, IsOpen O ∧ y₀ ∈ O ∧ ∀ᵐ lam : Fin d → ℝ, ‖lam‖ < ε → ∀ y ∈ O,
      (famShift a g lam y, y) ∈ M →
        PX.IsMorseOrRegularPoint {y | (famShift a g lam y, y) ∈ M} t y := by
  classical
  have hsnd : ((rnPolyfold k).prod PX).IsScSmoothMap PX Prod.snd :=
    MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX
  have hfst : ((rnPolyfold k).prod PX).IsScSmoothMap (rnPolyfold k) Prod.fst :=
    MPolyfold.isScSmoothMap_fst (rnPolyfold k) PX
  set T : N → ℝ := fun v => t (p v).2 with hTdef
  set μh : N → Fin k → ℝ := fun v => (p v).1 with hμdef
  set A : Fin d → N → ℝ := fun i v => a i (p v).2 with hAdef
  set Bf : Fin d → N → Fin k → ℝ := fun i v => A i v • (Pi.single (g i) (1 : ℝ) : Fin k → ℝ)
    with hBdef
  have hT : ContDiffOn ℝ ∞ T Ω := hpar.smooth_p (t ∘ Prod.snd) (ht.comp hsnd)
  have hμ : ContDiffOn ℝ ∞ μh Ω := contDiffOn_pi.2 fun j =>
    hpar.smooth_p (fun z => z.1 j)
      ((isScSmoothMap_rn_real_of_contDiff (contDiff_apply ℝ ℝ j)).comp hfst)
  have hA : ∀ i, ContDiffOn ℝ ∞ (A i) Ω := fun i =>
    hpar.smooth_p (a i ∘ Prod.snd) ((ha i).comp hsnd)
  have hB : ∀ i, ContDiffOn ℝ ∞ (Bf i) Ω := fun i => (hA i).smul contDiffOn_const
  have hcon : ∀ (lam : Fin d → ℝ) (v : N),
      famConstraint μh Bf lam v = (p v).1 - famShift a g lam (p v).2 := fun lam v => by
    simp only [famConstraint, famShift, hBdef, hAdef, hμdef, smul_smul]
  have hA1 : ∀ i, DifferentiableAt ℝ (A i) v₀ := fun i =>
    ((hA i).contDiffAt (hΩ.mem_nhds hv₀)).differentiableAt (by simp)
  have hy₀ : (p v₀).2 = y₀ := by rw [hpv₀]
  -- the classical statement
  obtain ⟨ε₁, hε₁, Ω', hΩ', hv₀Ω', hΩ'Ω, hae⟩ :=
    ae_isLagrangeNondegenerate_family hΩ hT hμ hB hv₀ hsurj (fun c _ hc β => by
      obtain ⟨δ, hδ0, hδ⟩ := hSC c hc β
      refine ⟨δ, ?_, fun κ hκ => ?_⟩
      · have := hcon δ v₀
        simp only [famConstraint] at this
        have h2 : ∑ i, δ i • Bf i v₀ = famShift a g δ (p v₀).2 := by
          simp only [famShift, hBdef, hAdef, smul_smul]
        rw [h2, hy₀, hδ0]
      · rw [hδ κ hκ]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h3 : fderiv ℝ (Bf i) v₀ κ =
            fderiv ℝ (A i) v₀ κ • (Pi.single (g i) (1 : ℝ) : Fin k → ℝ) := by
          rw [((hA1 i).hasFDerivAt.smul_const (Pi.single (g i) (1 : ℝ) : Fin k → ℝ)).fderiv]
          rfl
        rw [h3, map_smul, smul_eq_mul]
        ring)
  -- the neighbourhood of `y₀`
  have hac : ∀ i, Continuous (a i) := fun i => continuousOn_univ.1 (ha i).continuousOn
  have hΘ : Continuous fun r : (Fin d → ℝ) × X => ((famShift a g r.1 r.2, r.2) :
      (Fin k → ℝ) × X) := (continuous_famShift hac g).prodMk continuous_snd
  have hGo : IsOpen (G ∩ q ⁻¹' Ω') := hpar.isOpen_G.inter (hΩ'.preimage hpar.continuous_q)
  have hmem0 : ((famShift a g (0 : Fin d → ℝ) y₀, y₀) : (Fin k → ℝ) × X) ∈ G ∩ q ⁻¹' Ω' := by
    rw [famShift_zero, ← hpv₀]
    exact ⟨hpar.mem_G hv₀, by rw [mem_preimage, hpar.left_inv v₀ hv₀]; exact hv₀Ω'⟩
  have hNb : (fun r : (Fin d → ℝ) × X => ((famShift a g r.1 r.2, r.2) : (Fin k → ℝ) × X)) ⁻¹'
      (G ∩ q ⁻¹' Ω') ∈ 𝓝 ((0 : Fin d → ℝ), y₀) :=
    (hGo.preimage hΘ).mem_nhds hmem0
  obtain ⟨S₁, S₂, hS₁, h0S₁, hS₂, hyS₂, hsub⟩ := mem_nhds_prod_iff'.1 hNb
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.isOpen_iff.1 hS₁ 0 h0S₁
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, S₂, hS₂, hyS₂, ?_⟩
  filter_upwards [hae] with lam hlam hlε y hyO hyM
  obtain ⟨hzG, hzΩ'⟩ : ((famShift a g lam y, y) : (Fin k → ℝ) × X) ∈ G ∩ q ⁻¹' Ω' :=
    hsub (show ((lam, y) : (Fin d → ℝ) × X) ∈ S₁ ×ˢ S₂ from
      ⟨hball (mem_ball_zero_iff.2 (hlε.trans_le (min_le_right _ _))), hyO⟩)
  obtain ⟨v, hvΩ, hpv⟩ : ((famShift a g lam y, y) : (Fin k → ℝ) × X) ∈ p '' Ω :=
    hpar.image_eq ▸ ⟨hyM, hzG⟩
  have hqv : q (famShift a g lam y, y) = v := by rw [← hpv, hpar.left_inv v hvΩ]
  have hvΩ' : v ∈ Ω' := hqv ▸ hzΩ'
  set hf : N → Fin k → ℝ := famConstraint μh Bf lam with hfdef
  have hv0 : hf v = 0 := by rw [hfdef, hcon, hpv]; simp
  obtain ⟨hsv, hnd⟩ := hlam (hlε.trans_le (min_le_left _ _)) v hvΩ' hv0
  have hhf : ContDiffOn ℝ ∞ hf Ω :=
    hμ.sub (ContDiffOn.sum fun i _ => (hB i).const_smul (lam i))
  obtain ⟨K, Ωγ, γ, π, Ω'', hK, hΩγ, hΩ''o, hΩ''Ω', hvΩ'', h0γ, hγ0, hγc, himg, hleft, hrange⟩ :=
    exists_levelSet_param hΩ' (hhf.mono hΩ'Ω) hvΩ' hv0 hsv
  -- the parametrization of the slice
  set Φ : X → (Fin k → ℝ) × X := fun y' => (famShift a g lam y', y') with hΦdef
  have hΦ : PX.IsScSmoothMap ((rnPolyfold k).prod PX) Φ :=
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_famShift ha g lam) MPolyfold.isScSmoothMap_id
  have himg' : γ '' Ωγ = {x | x ∈ Ω'' ∧ Φ (Prod.snd (p x)) = p x} := by
    rw [himg]
    ext x
    refine and_congr_right fun _ => ?_
    rw [hfdef, hcon, sub_eq_zero]
    constructor
    · intro h; exact Prod.ext h.symm rfl
    · intro h; exact (congrArg Prod.fst h).symm
  have hsub' := MPolyfold.IsSmoothParam.of_levelSet (PX := PX) hpar hΦ hsnd (fun _ => rfl) π v
    hΩ''o (hΩ''Ω'.trans hΩ'Ω) hγc himg' hleft
  have hpt : (Prod.snd ∘ p ∘ γ) 0 = y := by
    change (p (γ 0)).2 = y
    rw [hγ0, hpv]
  rw [← hpt]
  refine MPolyfold.isMorseOrRegularPoint_of_param hsub' hΩγ h0γ ht fun hcrit => ?_
  have hTγ : t ∘ (Prod.snd ∘ p ∘ γ) = T ∘ γ := rfl
  rw [hTγ] at hcrit ⊢
  subst hγ0
  have hT2 : ContDiffAt ℝ 2 T (γ 0) := (hT.contDiffAt (hΩ.mem_nhds hvΩ)).of_le (by decide)
  have hh2 : ContDiffAt ℝ 2 hf (γ 0) := (hhf.contDiffAt (hΩ.mem_nhds hvΩ)).of_le (by decide)
  have hγ2 : ContDiffAt ℝ 2 γ 0 := (hγc.contDiffAt (hΩγ.mem_nhds h0γ)).of_le (by decide)
  have hγd : HasFDerivAt γ (fderiv ℝ γ 0) 0 := (hγ2.differentiableAt (by norm_num)).hasFDerivAt
  have hzero : ∀ᶠ u in 𝓝 (0 : K), hf (γ u) = 0 := by
    filter_upwards [hΩγ.mem_nhds h0γ] with u hu
    exact (himg ▸ mem_image_of_mem γ hu : γ u ∈ {x | x ∈ Ω'' ∧ hf x = 0}).2
  have hinj : Injective (fderiv ℝ γ 0) := by
    have h1 : HasFDerivAt (fun u => π (γ u - γ 0)) ((π : N →L[ℝ] K).comp (fderiv ℝ γ 0)) 0 :=
      π.hasFDerivAt.comp 0 (hγd.sub_const (γ 0))
    have h2 : (fun u => π (γ u - γ 0)) =ᶠ[𝓝 0] fun u => u := by
      filter_upwards [hΩγ.mem_nhds h0γ] with u hu using hleft u hu
    have h3 : (π : N →L[ℝ] K).comp (fderiv ℝ γ 0) = ContinuousLinearMap.id ℝ K :=
      (h1.congr_of_eventuallyEq h2.symm).unique (hasFDerivAt_id 0)
    intro x y hxy
    have := congrArg (fun L : K →L[ℝ] K => L x) h3
    have h4 := congrArg (fun L : K →L[ℝ] K => L y) h3
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h4
    rw [← this, ← h4, hxy]
  have hcomp : fderiv ℝ (T ∘ γ) 0 = (fderiv ℝ T (γ 0)).comp (fderiv ℝ γ 0) :=
    fderiv_comp 0 (hT2.differentiableAt (by norm_num)) hγd.differentiableAt
  obtain ⟨c, hc⟩ := exists_clm_comp_eq_of_ker_le (fderiv ℝ hf (γ 0)) (fderiv ℝ T (γ 0))
    fun κ hκ => by
      obtain ⟨b, hb⟩ := hrange 0 h0γ κ hκ
      have := congrArg (fun L : K →L[ℝ] ℝ => L b) (hcomp.symm.trans hcrit)
      simpa [hb] using this
  exact injective_hessian_comp_of_lagrange hT2 hh2 hγ2 hzero hinj (hrange 0 h0γ) hc (hnd c hc)

end Local

end Polyfold
