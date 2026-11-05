import Polyfold.Chapter3.GlobalIFTNearbyOntoGerm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Theorem 3.54 (1), the surjectivity of `f'(y)` at the nearby zeros: the curve of perturbed zeros
through a nearby zero (Lemma 4 and Proposition 7 of the argument).**

# The finite-dimensional reduction at a nearby zero and the curve of perturbed zeros

## The text, paraphrased

Nothing in the text (the repair of the gap of Finding 100, see `GlobalIFTNearbyOntoLemmas.lean`).

## What is formalized

In the normal form `ShiftedBasicData` (`g : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W` with `g¹ = (G₁, w − B)` a basic
germ on the index-raised structure) with an sc⁺-perturbation `e`, the contraction regions `R`
and the bounds `c` of `GlobalIFTNearbyOntoGerm.lean`, let `z = (a₀, w₀) ∈ U₁` be a zero of `g`
with `‖a₀‖ < ν_3`, `‖w₀‖₁ < ρ_0`, `a₀ ∈ C̃`, such that `Dg(z) : E₀ → F₀` has a kernel of
dimension `n − N` and contains an inward direction `v` (`a₀ + t(v₁ + β) ∈ C̃` for small `t ≥ 0`
and `β`).

* `ShiftedBasicData.curveMap`, `hasFDerivWithinAt_curveMap` (**Lemma 4 (i)**): the map
  `G̃(μ, a) = (g + μ ι e)(a, δ_μ(μ, a))` is `C¹` on the region `(−μ_3, μ_3) × (N(3) ∩ C̃)` with
  derivative `Dg(z) ∘ (α, Dδ(0, a₀)(dμ, α)) + dμ · ι e(z)` at `(0, a₀)` (the chain rule with
  Theorem 3.30 for the perturbed germ).
* `ShiftedBasicData.curveMap_snd` : the `W`-component of `G̃` vanishes identically (`δ_μ` is the
  fixed point of `B_μ`), so `H = (1 − P) G̃` carries the whole equation.
* `ShiftedBasicData.surjective_DH_and_ker_eq` (**Lemma 4 (ii)**): `ker Dg(z)` is the graph
  of `L = ι D_aδ(0, a₀)` over `ker D_aH(0, a₀)`, and `D_aH(0, a₀) : ℝⁿ → ℝᴺ` is onto — by the
  dimension count `dim ker D_aH(0, a₀) ≤ dim ker Dg(z) = n − N`, which replaces the block
  elimination with `(1 − D₂B(z))⁻¹` of the note (the latter would need the level-`1` surjectivity).
* `ShiftedBasicData.exists_perturbed_curve` (**Proposition 7**): a curve `u'(μ) = (a(μ), δ_μ(μ, a(μ)))`,
  `0 ≤ μ < μ₀`, of zeros of `g + μ ι e`, with `u'(0) = z`, `u'(μ) ∈ U₂ ∩ (C̃ ⊕ W)`, right
  differentiable at `0` as a map into `E₂`: `a(μ)` from `exists_curve_of_inward` applied to `H`
  with the inward kernel direction `v₁` tilted to `α₀ = a₁ + s v₁`, `D_aH(0, a₀) a₁ = −D_μH(0, a₀)`.

## What the text leaves implicit, and the choices made (the findings)

The level bookkeeping (Finding 186): `δ_μ` is `C¹` into `W₂` on `(−μ_3, μ_3) × (N(3) ∩ C̃)`
(Theorem 3.30 on the re-indexed germ and Proposition 1.16 on level `1`), so the curve is right
differentiable into `E₂ = ℝⁿ ⊕ W₂`; `g` and `e` are differentiated from level `1` to level `0`.
-/

open Set Filter Topology Function Module ContinuousLinearMap Metric Asymptotics

noncomputable section

namespace Polyfold

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [FiniteDimensional ℝ Q]

namespace ShiftedBasicData

variable (𝒟 : ShiftedBasicData Ct W Q)

/-- The derivative family of `g` on the germ `G₀`, at a point of `U₁`. -/
abbrev Dg' : (ScBanach.paramProd P W) 1 → P × W 0 →L[ℝ] Q × W 0 :=
  scDerivGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒟.G₀ 𝒟.g

lemma hasFDerivWithinAt_Dg' {z : (ScBanach.paramProd P W) 1} (hz : z ∈ 𝒟.G₀.U 1) :
    HasFDerivWithinAt (𝒟.g ∘ (ScBanach.paramProd P W).toBase 1)
      ((𝒟.Dg' z).comp ((ScBanach.paramProd P W).toBase 1)) (𝒟.G₀.U 1) z :=
  𝒟.hg1.hasFDerivWithinAt z hz

/-- `(g(ι x))_W = ι((g¹(x))_W) = ι(x_W − B(x))` for `x ∈ U₁`. -/
lemma snd_g_toBase {x : P × W 1} (hx : x ∈ 𝒟.G₀.U 1) :
    (𝒟.g ((ScBanach.paramProd P W).toBase 1 x)).2 = W.toBase 1 (x.2 - 𝒟.B x) := by
  have hx' : x ∈ 𝒟.G₁.U 0 := by rw [𝒟.G₁_U 0]; exact hx
  have h1 := congrArg Prod.snd ((𝒟.isScSmooth 0).toBase_levelMap hx)
  rw [← 𝒟.g₁_eq _ hx, ScBanach.paramProd_toBase, 𝒟.basic.snd_eq _ hx'] at h1
  exact h1.symm

/-- A zero `z ∈ U₁` of `g` is a fixed point of `B(a, ·)`: `B(z) = z_W`. -/
lemma B_eq_of_zero {z : P × W 1} (hz : z ∈ 𝒟.G₀.U 1)
    (hz0 : 𝒟.g ((ScBanach.paramProd P W).toBase 1 z) = 0) : 𝒟.B z = z.2 := by
  have h1 := 𝒟.snd_g_toBase hz
  rw [hz0] at h1
  have h2 : W.toBase 1 (z.2 - 𝒟.B z) = 0 := h1.symm
  rw [← map_zero (W.toBase 1)] at h2
  have := W.toBase_injective 1 h2
  exact (sub_eq_zero.1 this).symm

variable (hC : IsQuadrantLike (ScBanach.const P) Ct) (R : 𝒟.Radii) {e : P × W 0 → Q × W 1}
  (he : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift)
    𝒟.G₀ e)
  (c : ℕ → ℝ) (hc : ∀ m, 0 ≤ c m)
  (hce : ∀ m, ∀ a ∈ Ct, ‖a‖ < R.ν m → ∀ w w' : W (m + 1), ‖w‖ < R.ρ m → ‖w'‖ < R.ρ m →
    ‖levelB (W := W.shift) (perturbEW e) m (a, w)‖ ≤ c m ∧
    ‖levelB (W := W.shift) (perturbEW e) m (a, w) -
      levelB (W := W.shift) (perturbEW e) m (a, w')‖ ≤ c m * ‖w - w'‖)

include hC he hc hce

/-! ### The perturbed section along the solution germ -/

/-- The map `(μ, a) ↦ (a, δ_μ(μ, a)) ∈ E₁` along the solution germ of the perturbed contraction
germ. -/
def curveLift : ℝ × P → (ScBanach.paramProd P W) 1 :=
  fun p => (p.2, (𝒟.perturbContraction hC R he c hc hce).sol p)

/-- `G̃(μ, a) = (g + μ ι e)(a, δ_μ(μ, a))` on level `0`. -/
def curveMap : ℝ × P → Q × W 0 :=
  fun p => 𝒟.g ((ScBanach.paramProd P W).toBase 1 (𝒟.curveLift hC R he c hc hce p)) +
    p.1 • (ScBanach.paramProd Q W).toBase 1
      (e ((ScBanach.paramProd P W).toBase 1 (𝒟.curveLift hC R he c hc hce p)))

/-- The domain `(−μ_3, μ_3) × (N(3) ∩ C̃)` of the finite-dimensional reduction. -/
def curveDom : Set (ℝ × P) :=
  (𝒟.perturbContraction hC R he c hc hce).N 3 ∩ (univ ×ˢ Ct)

lemma curveDom_eq :
    𝒟.curveDom hC R he c hc hce =
      ((𝒟.perturbContraction hC R he c hc hce).germ (isQuadrantLike_perturb hC) 1).U 2 := rfl

lemma curveDom_subset (m : ℕ) (hm : m ≤ 3) :
    𝒟.curveDom hC R he c hc hce ⊆ (𝒟.perturbContraction hC R he c hc hce).N m ∩ (univ ×ˢ Ct) :=
  fun p hp => ⟨(𝒟.perturbContraction hC R he c hc hce).N_anti_le hm hp.1, hp.2⟩

lemma mem_curveDom_iff (p : ℝ × P) :
    p ∈ 𝒟.curveDom hC R he c hc hce ↔
      |p.1| < 𝒟.perturbMu R c 3 ∧ ‖p.2‖ < R.ν 3 ∧ p.2 ∈ Ct :=
  𝒟.mem_perturbContraction_N_iff hC R he c hc hce 3 p

lemma uniqueDiffOn_curveDom : UniqueDiffOn ℝ (𝒟.curveDom hC R he c hc hce) := fun _ hp =>
  ((𝒟.perturbContraction hC R he c hc hce).germ (isQuadrantLike_perturb hC) 1).uniqueDiffWithinAt
    (isQuadrantLike_perturb hC) 2 hp

/-- `(a, δ_μ(μ, a)) ∈ U₁` on the solution region. -/
lemma curveLift_mem {p : ℝ × P}
    (hp : p ∈ (𝒟.perturbContraction hC R he c hc hce).N 0 ∩ (univ ×ˢ Ct)) :
    𝒟.curveLift hC R he c hc hce p ∈ 𝒟.G₀.U 1 := by
  have := (𝒟.perturbContraction hC R he c hc hce).mem_G_fixLvl 0 hp
  rw [perturbContraction_G, mem_perturbGerm_U] at this
  rw [← 𝒟.G₁_U 0]
  exact this

/-- **The `W`-component of `G̃` vanishes**: `δ_μ` is the fixed point of `B_μ(a, ·)`. -/
theorem curveMap_snd {p : ℝ × P}
    (hp : p ∈ (𝒟.perturbContraction hC R he c hc hce).N 0 ∩ (univ ×ˢ Ct)) :
    (𝒟.curveMap hC R he c hc hce p).2 = 0 := by
  set 𝒞 := 𝒟.perturbContraction hC R he c hc hce with h𝒞
  have hmem := 𝒟.curveLift_mem hC R he c hc hce hp
  have hfix := 𝒞.sol_fixed hp
  rw [perturbContraction_B, perturbB_apply] at hfix
  change 𝒟.B (p.2, 𝒞.sol p) - p.1 • perturbEW e (p.2, 𝒞.sol p) = 𝒞.sol p at hfix
  simp only [curveMap, Prod.snd_add, Prod.smul_snd]
  rw [𝒟.snd_g_toBase hmem, ScBanach.paramProd_toBase]
  change W.toBase 1 (𝒞.sol p - 𝒟.B (p.2, 𝒞.sol p)) +
    p.1 • W.toBase 1 (perturbEW e (p.2, 𝒞.sol p)) = 0
  rw [← map_smul, ← map_add, ← map_zero (W.toBase 1)]
  congr 1
  have h3 : 𝒞.sol p - 𝒟.B (p.2, 𝒞.sol p) + p.1 • perturbEW e (p.2, 𝒞.sol p) =
      𝒞.sol p - (𝒟.B (p.2, 𝒞.sol p) - p.1 • perturbEW e (p.2, 𝒞.sol p)) := by abel
  rw [h3, hfix, sub_self]

/-- **`G̃` is `C¹` on the solution region** (Lemma 4 (i)): `δ_μ` is `C¹` into `W₁` by Theorem
3.30, `g` and `e` are `C¹` from level `1` to level `0`. -/
theorem contDiffOn_curveMap :
    ContDiffOn ℝ 1 (𝒟.curveMap hC R he c hc hce) (𝒟.curveDom hC R he c hc hce) := by
  set 𝒞 := 𝒟.perturbContraction hC R he c hc hce with h𝒞
  have hC₁ := isQuadrantLike_perturb hC
  have hCW := hC.paramProd W
  have hsc1 := 𝒟.perturbContraction_isSc1GermWith hC R he c hc hce
  have hsck : IsSckGerm 1 (𝒞.germ hC₁ 1) 𝒞.sol :=
    ⟨hsc1.isSc1Germ, hsc1.isSc1Germ.tangentMapGerm_isSc0⟩
  have hsol : ContDiffOn ℝ 1 𝒞.sol ((𝒞.germ hC₁ 1).U 1) := by
    have := hsck.contDiffOn_base hC₁
    refine this.congr fun p _ => ?_
    rw [Function.comp_apply, ScBanach.const_toBase]
  have hsol' : ContDiffOn ℝ 1 𝒞.sol (𝒟.curveDom hC R he c hc hce) :=
    hsol.mono (by exact 𝒟.curveDom_subset hC R he c hc hce 2 (by norm_num))
  have hlift : ContDiffOn ℝ 1 (𝒟.curveLift hC R he c hc hce) (𝒟.curveDom hC R he c hc hce) :=
    contDiffOn_snd.prodMk hsol'
  have hmaps : MapsTo (𝒟.curveLift hC R he c hc hce) (𝒟.curveDom hC R he c hc hce) (𝒟.G₀.U 1) :=
    fun p hp => 𝒟.curveLift_mem hC R he c hc hce (𝒟.curveDom_subset hC R he c hc hce 0 (by norm_num) hp)
  have hg : ContDiffOn ℝ 1 (𝒟.g ∘ (ScBanach.paramProd P W).toBase 1) (𝒟.G₀.U 1) :=
    (𝒟.isScSmooth 1).contDiffOn_base hCW
  have he' : ContDiffOn ℝ 1 (e ∘ (ScBanach.paramProd P W).toBase 1) (𝒟.G₀.U 1) :=
    (he 1).contDiffOn_base hCW
  have h1 := hg.comp hlift hmaps
  have h2 := ((ScBanach.paramProd Q W).toBase 1).contDiff.comp_contDiffOn (he'.comp hlift hmaps)
  have h3 := h1.add (contDiffOn_fst.smul h2)
  exact h3.congr fun p _ => rfl

/-! ### The derivative of `G̃` at a nearby zero (Lemma 4) -/

section Zero

variable {z : P × W 1} (hz : z ∈ 𝒟.G₀.U 1) (hzC : z.1 ∈ Ct) (hzν : ‖z.1‖ < R.ν 3)
  (hzρ : ‖z.2‖ < R.ρ 0) (hz0 : 𝒟.g ((ScBanach.paramProd P W).toBase 1 z) = 0)

/-- The derivative family of the perturbed contraction map. -/
abbrev perturbD : (ScBanach.paramProd (ℝ × P) W.shift) 1 →
    (ScBanach.paramProd (ℝ × P) W.shift) 0 →L[ℝ] W.shift 0 :=
  scDerivGerm (E := ScBanach.paramProd (ℝ × P) W.shift) (F := W.shift) 𝒟.perturbGerm
    (𝒟.perturbB e)

/-- The derivative `Dδ_μ(0, a₀) : ℝ × P → W₁` of the solution germ at `(0, a₀)`. -/
def solD : ℝ × P →L[ℝ] W 1 :=
  (𝒟.perturbContraction hC R he c hc hce).Aop (D := 𝒟.perturbD (e := e)) 0 ((0 : ℝ), z.1)

/-- The derivative of `G̃` at `(0, a₀)`:
`(dμ, α) ↦ Dg(z)(α, ι Dδ(0, a₀)(dμ, α)) + dμ · ι e(z)`. -/
def curveDeriv : ℝ × P →L[ℝ] Q × W 0 :=
  (𝒟.Dg' z).comp (((ScBanach.paramProd P W).toBase 1).comp
    ((ContinuousLinearMap.snd ℝ ℝ P).prod (𝒟.solD hC R he c hc hce (z := z)))) +
  (ContinuousLinearMap.fst ℝ ℝ P).smulRight
    ((ScBanach.paramProd Q W).toBase 1 (e ((ScBanach.paramProd P W).toBase 1 z)))

include hzC hzν

lemma zero_mem_curveDom : ((0 : ℝ), z.1) ∈ 𝒟.curveDom hC R he c hc hce := by
  rw [mem_curveDom_iff]
  exact ⟨by rw [abs_zero]; exact 𝒟.perturbMu_pos R c hc 3, hzν, hzC⟩

include hz hzρ hz0 in
/-- `δ_μ(0, a₀) = w₀`. -/
lemma sol_zero_eq : (𝒟.perturbContraction hC R he c hc hce).sol ((0 : ℝ), z.1) = z.2 :=
  𝒟.perturbContraction_sol_zero hC R he c hc hce hzC (hzν.trans_le (R.ν_anti_le (by norm_num)))
    hzρ (𝒟.B_eq_of_zero hz hz0)

include hz hzρ hz0 in
lemma curveLift_zero_eq : 𝒟.curveLift hC R he c hc hce ((0 : ℝ), z.1) = z :=
  Prod.ext rfl (𝒟.sol_zero_eq hC R he c hc hce hz hzC hzν hzρ hz0)

include hz hzρ hz0 in
/-- **The derivative of `G̃` at `(0, a₀)`** (the chain rule with Theorem 3.30). -/
theorem hasFDerivWithinAt_curveMap :
    HasFDerivWithinAt (𝒟.curveMap hC R he c hc hce) (𝒟.curveDeriv hC R he c hc hce (z := z))
      (𝒟.curveDom hC R he c hc hce) ((0 : ℝ), z.1) := by
  set 𝒞 := 𝒟.perturbContraction hC R he c hc hce with h𝒞
  have hC₁ := isQuadrantLike_perturb hC
  have hB : IsSc1GermWith 𝒞.G 𝒞.B (𝒟.perturbD (e := e)) :=
    ((𝒟.perturbB_isScSmoothGerm hC he).isSckGerm 1).1.isSc1GermWith_scDerivGerm
  have h0D := 𝒟.zero_mem_curveDom hC R he c hc hce hzC hzν
  have h0N2 : ((0 : ℝ), z.1) ∈ 𝒞.N 2 ∩ (univ ×ˢ Ct) :=
    𝒟.curveDom_subset hC R he c hc hce 2 (by norm_num) h0D
  -- the derivative of the solution germ
  have hsolA : HasFDerivWithinAt 𝒞.sol (𝒟.solD hC R he c hc hce (z := z))
      (𝒟.curveDom hC R he c hc hce) ((0 : ℝ), z.1) :=
    (𝒞.hasFDerivWithinAt_sol hC₁ hB h0N2).mono
      (𝒟.curveDom_subset hC R he c hc hce 2 (by norm_num))
  have hlift : HasFDerivWithinAt (𝒟.curveLift hC R he c hc hce)
      ((ContinuousLinearMap.snd ℝ ℝ P).prod (𝒟.solD hC R he c hc hce (z := z)))
      (𝒟.curveDom hC R he c hc hce) ((0 : ℝ), z.1) :=
    hasFDerivWithinAt_snd.prodMk hsolA
  have hmaps : MapsTo (𝒟.curveLift hC R he c hc hce) (𝒟.curveDom hC R he c hc hce)
      (𝒟.G₀.U 1) := fun p hp =>
    𝒟.curveLift_mem hC R he c hc hce (𝒟.curveDom_subset hC R he c hc hce 0 (by norm_num) hp)
  have hliftz := 𝒟.curveLift_zero_eq hC R he c hc hce hz hzC hzν hzρ hz0
  -- `g` and `e` at `z`
  have hgz : HasFDerivWithinAt (𝒟.g ∘ (ScBanach.paramProd P W).toBase 1)
      ((𝒟.Dg' z).comp ((ScBanach.paramProd P W).toBase 1)) (𝒟.G₀.U 1)
      (𝒟.curveLift hC R he c hc hce ((0 : ℝ), z.1)) := by
    rw [hliftz]; exact 𝒟.hasFDerivWithinAt_Dg' hz
  have hez : HasFDerivWithinAt (e ∘ (ScBanach.paramProd P W).toBase 1)
      ((scDerivGerm (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift) 𝒟.G₀ e z).comp
        ((ScBanach.paramProd P W).toBase 1)) (𝒟.G₀.U 1)
      (𝒟.curveLift hC R he c hc hce ((0 : ℝ), z.1)) := by
    rw [hliftz]; exact (he 1).1.isSc1GermWith_scDerivGerm.hasFDerivWithinAt z hz
  have h1 := hgz.comp ((0 : ℝ), z.1) hlift hmaps
  have h2 := ((ScBanach.paramProd Q W).toBase 1).hasFDerivAt.comp_hasFDerivWithinAt ((0 : ℝ), z.1)
    (hez.comp ((0 : ℝ), z.1) hlift hmaps)
  have h3 := hasFDerivWithinAt_fst.smul h2
  have h4 := h1.add h3
  refine h4.congr_fderiv ?_
  simp only [Function.comp_apply]
  rw [hliftz]
  ext v <;> simp [curveDeriv]

include hz hzρ hz0 in
/-- **The `W`-component of the derivative of `G̃` vanishes** (`G̃_W = 0` on the solution region). -/
theorem curveDeriv_snd (v : ℝ × P) : (𝒟.curveDeriv hC R he c hc hce (z := z) v).2 = 0 := by
  have h0D := 𝒟.zero_mem_curveDom hC R he c hc hce hzC hzν
  have hd := 𝒟.hasFDerivWithinAt_curveMap hC R he c hc hce hz hzC hzν hzρ hz0
  have h1 := (ContinuousLinearMap.snd ℝ Q (W 0)).hasFDerivAt.comp_hasFDerivWithinAt ((0 : ℝ), z.1) hd
  have h2 : HasFDerivWithinAt (fun p => (𝒟.curveMap hC R he c hc hce p).2) (0 : ℝ × P →L[ℝ] W 0)
      (𝒟.curveDom hC R he c hc hce) ((0 : ℝ), z.1) := by
    refine (hasFDerivWithinAt_const (0 : W 0) _ _).congr (fun p hp => ?_) ?_
    · exact 𝒟.curveMap_snd hC R he c hc hce (𝒟.curveDom_subset hC R he c hc hce 0 (by norm_num) hp)
    · exact 𝒟.curveMap_snd hC R he c hc hce (𝒟.curveDom_subset hC R he c hc hce 0 (by norm_num) h0D)
  have huniq := 𝒟.uniqueDiffOn_curveDom hC R he c hc hce _ h0D
  have heq := huniq.eq h1 h2
  have := congrArg (fun T : ℝ × P →L[ℝ] W 0 => T v) heq
  simpa using this

/-- The finite-dimensional derivative `M₀ = D_aH(0, a₀) : P → Q`. -/
def DH : P →L[ℝ] Q :=
  (ContinuousLinearMap.fst ℝ Q (W 0)).comp
    ((𝒟.curveDeriv hC R he c hc hce (z := z)).comp (ContinuousLinearMap.inr ℝ ℝ P))

/-- `L = ι D_aδ(0, a₀) : P → W₀`. -/
def solL : P →L[ℝ] W 0 :=
  (W.toBase 1).comp ((𝒟.solD hC R he c hc hce (z := z)).comp (ContinuousLinearMap.inr ℝ ℝ P))

omit hzC hzν in
lemma curveDeriv_inr (α : P) :
    𝒟.curveDeriv hC R he c hc hce (z := z) ((0 : ℝ), α) =
      𝒟.Dg' z (α, 𝒟.solL hC R he c hc hce (z := z) α) := by
  simp only [curveDeriv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_snd', zero_smul, add_zero]
  rw [ScBanach.paramProd_toBase]
  rfl

include hz hzρ hz0 in
/-- **`Dg(z)(α, Lα) = (M₀ α, 0)`.** -/
theorem Dg'_graph (α : P) :
    𝒟.Dg' z (α, 𝒟.solL hC R he c hc hce (z := z) α) = (𝒟.DH hC R he c hc hce (z := z) α, 0) := by
  rw [← curveDeriv_inr]
  refine Prod.ext rfl ?_
  exact 𝒟.curveDeriv_snd hC R he c hc hce hz hzC hzν hzρ hz0 _

include hz hzρ hz0 in
/-- The graph of `L` over `ker M₀` lies in `ker Dg(z)`. -/
theorem map_graph_le_ker :
    (LinearMap.ker (𝒟.DH hC R he c hc hce (z := z) : P →ₗ[ℝ] Q)).map
        (graphMap (𝒟.solL hC R he c hc hce (z := z))) ≤
      LinearMap.ker (𝒟.Dg' z : P × W 0 →ₗ[ℝ] Q × W 0) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_map_graphMap.1 hx
  rw [LinearMap.mem_ker] at hx1 ⊢
  have hxeq : x = (x.1, 𝒟.solL hC R he c hc hce (z := z) x.1) := Prod.ext rfl hx2
  have hx1' : 𝒟.DH hC R he c hc hce (z := z) x.1 = 0 := hx1
  change 𝒟.Dg' z x = 0
  rw [hxeq, 𝒟.Dg'_graph hC R he c hc hce hz hzC hzν hzρ hz0, hx1']
  rfl

variable (hfin : FiniteDimensional ℝ (LinearMap.ker (𝒟.Dg' z : P × W 0 →ₗ[ℝ] Q × W 0)))
  (hdim : (finrank ℝ (LinearMap.ker (𝒟.Dg' z : P × W 0 →ₗ[ℝ] Q × W 0)) : ℤ) =
    finrank ℝ P - finrank ℝ Q)

include hz hzρ hz0 hfin hdim in
/-- **`M₀ = D_aH(0, a₀)` is onto, and `ker Dg(z)` is the graph of `L` over `ker M₀`** (Lemma 4
(ii)): `dim ker M₀ ≤ dim ker Dg(z) = n − N`, so `rank M₀ ≥ N`. -/
theorem surjective_DH_and_ker_eq :
    Surjective (𝒟.DH hC R he c hc hce (z := z)) ∧
      LinearMap.ker (𝒟.Dg' z : P × W 0 →ₗ[ℝ] Q × W 0) =
        (LinearMap.ker (𝒟.DH hC R he c hc hce (z := z) : P →ₗ[ℝ] Q)).map
          (graphMap (𝒟.solL hC R he c hc hce (z := z))) := by
  classical
  haveI := hfin
  set M₀ := 𝒟.DH hC R he c hc hce (z := z) with hM₀
  set L := 𝒟.solL hC R he c hc hce (z := z) with hL
  set K := LinearMap.ker (𝒟.Dg' z : P × W 0 →ₗ[ℝ] Q × W 0) with hK
  set K₀ := LinearMap.ker (M₀ : P →ₗ[ℝ] Q) with hK₀
  have hsub : K₀.map (graphMap L) ≤ K := 𝒟.map_graph_le_ker hC R he c hc hce hz hzC hzν hzρ hz0
  have hrank : finrank ℝ (K₀.map (graphMap L)) = finrank ℝ K₀ :=
    ((Submodule.equivMapOfInjective (graphMap L) (graphMap_injective L) K₀).finrank_eq).symm
  have hle : finrank ℝ K₀ ≤ finrank ℝ K := by
    rw [← hrank]; exact Submodule.finrank_mono hsub
  have hrn := (M₀ : P →ₗ[ℝ] Q).finrank_range_add_finrank_ker
  have hrange : finrank ℝ (LinearMap.range (M₀ : P →ₗ[ℝ] Q)) ≤ finrank ℝ Q :=
    Submodule.finrank_le _
  have hQ : finrank ℝ (LinearMap.range (M₀ : P →ₗ[ℝ] Q)) = finrank ℝ Q := by
    have h1 : (finrank ℝ (LinearMap.range (M₀ : P →ₗ[ℝ] Q)) : ℤ) + finrank ℝ K₀ = finrank ℝ P := by
      exact_mod_cast hrn
    have h2 : (finrank ℝ K₀ : ℤ) ≤ finrank ℝ K := by exact_mod_cast hle
    omega
  have hsurj : Surjective M₀ := LinearMap.range_eq_top.1 (Submodule.eq_top_of_finrank_eq hQ)
  refine ⟨hsurj, ?_⟩
  symm
  refine Submodule.eq_of_le_of_finrank_eq hsub ?_
  rw [hrank]
  have h1 : (finrank ℝ (LinearMap.range (M₀ : P →ₗ[ℝ] Q)) : ℤ) + finrank ℝ K₀ = finrank ℝ P := by
    exact_mod_cast hrn
  rw [hQ] at h1
  have : (finrank ℝ K₀ : ℤ) = finrank ℝ K := by omega
  exact_mod_cast this

include hz hzρ hz0 hfin hdim in
/-- **Proposition 7: the curve of perturbed zeros through the nearby zero.**  Let `z = (a₀, w₀)`
be a zero of `g` on level `1` with `‖a₀‖ < ν_3`, `‖w₀‖₁ < ρ_0`, `a₀ ∈ C̃`, `dim ker Dg(z) = n − N`,
and `v ∈ ker Dg(z)` with `v₁` an inward direction at `a₀`.  Then there are `μ₀ > 0` and a curve
`u'(μ) = (a(μ), δ_μ(μ, a(μ)))`, `0 ≤ μ < μ₀`, with values in `U₂ ∩ (C̃ ⊕ W)`, `ι u'(0) = ι z`,
right differentiable at `0` as a map into `E₂`, and `(g + μ ι e)(ι u'(μ)) = 0`. -/
theorem exists_perturbed_curve {v : P × W 0}
    (hv : v ∈ LinearMap.ker (𝒟.Dg' z : P × W 0 →ₗ[ℝ] Q × W 0)) {η t₀ : ℝ} (hη : 0 < η)
    (ht₀ : 0 < t₀) (hin : ∀ β : P, ‖β‖ < η → ∀ t ∈ Icc (0 : ℝ) t₀, z.1 + t • (v.1 + β) ∈ Ct) :
    ∃ μ₀ > 0, ∃ cv : ℝ → (ScBanach.paramProd P W) 2, ∃ ξ : (ScBanach.paramProd P W) 2,
      (ScBanach.paramProd P W).toBase 2 (cv 0) = (ScBanach.paramProd P W).toBase 1 z ∧
      HasDerivWithinAt cv ξ (Ici 0) 0 ∧
      ∀ μ ∈ Ico (0 : ℝ) μ₀, cv μ ∈ 𝒟.G₀.U 2 ∧ (cv μ).1 ∈ Ct ∧
        𝒟.g ((ScBanach.paramProd P W).toBase 2 (cv μ)) +
          μ • (ScBanach.paramProd Q W).toBase 1
            (e ((ScBanach.paramProd P W).toBase 2 (cv μ))) = 0 := by
  classical
  set 𝒞 := 𝒟.perturbContraction hC R he c hc hce with h𝒞
  have hC₁ := isQuadrantLike_perturb hC
  set D := 𝒟.curveDom hC R he c hc hce with hDdef
  have h0D := 𝒟.zero_mem_curveDom hC R he c hc hce hzC hzν
  obtain ⟨hsurj, hker⟩ :=
    𝒟.surjective_DH_and_ker_eq hC R he c hc hce hz hzC hzν hzρ hz0 hfin hdim
  set M₀ := 𝒟.DH hC R he c hc hce (z := z) with hM₀
  set DG := 𝒟.curveDeriv hC R he c hc hce (z := z) with hDG
  set H : ℝ × P → Q := fun p => (𝒟.curveMap hC R he c hc hce p).1 with hHdef
  -- `H` is `C¹` with derivative `pr ∘ DG` at `(0, a₀)`
  have hH : ContDiffOn ℝ 1 H D :=
    contDiff_fst.comp_contDiffOn (𝒟.contDiffOn_curveMap hC R he c hc hce)
  have hHd : HasFDerivWithinAt H ((ContinuousLinearMap.fst ℝ Q (W 0)).comp DG) D
      ((0 : ℝ), z.1) :=
    (ContinuousLinearMap.fst ℝ Q (W 0)).hasFDerivAt.comp_hasFDerivWithinAt _
      (𝒟.hasFDerivWithinAt_curveMap hC R he c hc hce hz hzC hzν hzρ hz0)
  have hHfd : fderivWithin ℝ H D ((0 : ℝ), z.1) = (ContinuousLinearMap.fst ℝ Q (W 0)).comp DG :=
    hHd.fderivWithin (𝒟.uniqueDiffOn_curveDom hC R he c hc hce _ h0D)
  have hH0 : H (0, z.1) = 0 := by
    simp only [hHdef, curveMap, Prod.fst_add, Prod.smul_fst, zero_smul, add_zero]
    rw [𝒟.curveLift_zero_eq hC R he c hc hce hz hzC hzν hzρ hz0, hz0]
    rfl
  -- the kernel vector and the inward direction `α₀ = a₁ + s v₁`
  have hv1 : v.1 ∈ LinearMap.ker (M₀ : P →ₗ[ℝ] Q) := by
    rw [hker] at hv; exact (mem_map_graphMap.1 hv).1
  obtain ⟨a₁, ha₁⟩ := hsurj (-(DG ((1 : ℝ), 0)).1)
  obtain ⟨s, hs, hin'⟩ := inward_add_smul hη hin a₁
  set α₀ := a₁ + s • v.1 with hα₀def
  have hα₀ : fderivWithin ℝ H D ((0 : ℝ), z.1) (1, α₀) = 0 := by
    have h1 : ((1 : ℝ), α₀) = ((1 : ℝ), (0 : P)) + ((0 : ℝ), α₀) := by simp
    rw [hHfd, ContinuousLinearMap.comp_apply, h1, map_add, map_add]
    have h2 : (ContinuousLinearMap.fst ℝ Q (W 0)) (DG ((0 : ℝ), α₀)) = M₀ α₀ := rfl
    have h2' : (ContinuousLinearMap.fst ℝ Q (W 0)) (DG ((1 : ℝ), 0)) = (DG ((1 : ℝ), 0)).1 := rfl
    have h3 : M₀ v.1 = 0 := hv1
    rw [h2, h2', hα₀def, map_add, map_smul, ha₁, h3, smul_zero, add_zero, add_neg_cancel]
  have hCt : Convex ℝ Ct := by
    have := hC.convex 0; rwa [ScBanach.const_lvlSet] at this
  have hsurj' : Surjective ((fderivWithin ℝ H D ((0 : ℝ), z.1)).comp
      (ContinuousLinearMap.inr ℝ ℝ P)) := by
    rw [hHfd]; exact hsurj
  obtain ⟨μ₀, hμ₀, a, ha0, hader, hcurve⟩ := exists_curve_of_inward hCt (𝒞.N_open 3) hzC h0D.1 hH
    hH0 hsurj' hα₀ one_pos (by positivity) hin'
  -- the level-`1` solution `(μ, a) ↦ δ_{μ,1}(μ, a)` is differentiable at `(0, a₀)` within `D`
  have hsc1 := 𝒟.perturbContraction_isSc1GermWith hC R he c hc hce
  have hfix1 := hsc1.hasFDerivWithinAt_level hC₁ (m := 1) (x := ((0 : ℝ), z.1)) h0D
  set Dfix := (levelDeriv (𝒞.solDeriv (D := 𝒟.perturbD (e := e))) 1 ((0 : ℝ), z.1)).comp
    ((ScBanach.const (ℝ × P)).incl 1) with hDfix
  have hfix1' : HasFDerivWithinAt (fun p : ℝ × P => 𝒞.fixLvl 1 p) Dfix D ((0 : ℝ), z.1) := by
    refine hfix1.congr (fun p hp => ?_) ?_
    · exact (𝒞.levelMap_sol 1 (𝒟.curveDom_subset hC R he c hc hce 1 (by norm_num) hp)).symm
    · exact (𝒞.levelMap_sol 1 (𝒟.curveDom_subset hC R he c hc hce 1 (by norm_num) h0D)).symm
  have hγ : HasDerivWithinAt (fun μ : ℝ => ((μ, a μ) : ℝ × P)) ((1 : ℝ), α₀) (Ico 0 μ₀) 0 :=
    (hasDerivWithinAt_id 0 _).prodMk (hader.mono Ico_subset_Ici_self)
  have hγmaps : MapsTo (fun μ : ℝ => ((μ, a μ) : ℝ × P)) (Ico 0 μ₀) D := fun μ hμ =>
    (hcurve μ hμ).1
  have hfixc : HasDerivWithinAt (fun μ : ℝ => 𝒞.fixLvl 1 (μ, a μ)) (Dfix ((1 : ℝ), α₀))
      (Ici 0) 0 := by
    have h0' : HasFDerivWithinAt (fun p : ℝ × P => 𝒞.fixLvl 1 p) Dfix D
        ((fun μ : ℝ => ((μ, a μ) : ℝ × P)) 0) := by
      change HasFDerivWithinAt (fun p : ℝ × P => 𝒞.fixLvl 1 p) Dfix D ((0 : ℝ), a 0)
      rw [ha0]
      exact hfix1'
    exact (h0'.comp_hasDerivWithinAt (0 : ℝ) hγ hγmaps).mono_of_mem_nhdsWithin
      (Ico_mem_nhdsGE hμ₀)
  -- the curve `u'(μ) = (a(μ), δ_{μ,1}(μ, a(μ)))`
  set cv : ℝ → (ScBanach.paramProd P W) 2 := fun μ => (a μ, 𝒞.fixLvl 1 (μ, a μ)) with hcv
  refine ⟨μ₀, hμ₀, cv, (α₀, Dfix ((1 : ℝ), α₀)), ?_, hader.prodMk hfixc, fun μ hμ => ?_⟩
  · have h01 : ((0 : ℝ), z.1) ∈ 𝒞.N 1 ∩ (univ ×ˢ Ct) :=
      𝒟.curveDom_subset hC R he c hc hce 1 (by norm_num) h0D
    have hsh : W.toBase 2 (𝒞.fixLvl 1 ((0 : ℝ), z.1)) =
        W.toBase 1 (W.shift.toBase 1 (𝒞.fixLvl 1 ((0 : ℝ), z.1))) := W.shift_toBase 1 _
    simp only [hcv, ha0]
    rw [ScBanach.paramProd_toBase, ScBanach.paramProd_toBase, hsh, 𝒞.toBase_fixLvl 1 h01,
      𝒟.sol_zero_eq hC R he c hc hce hz hzC hzν hzρ hz0]
  · have hpD : ((μ, a μ) : ℝ × P) ∈ D := (hcurve μ hμ).1
    have hp1 : ((μ, a μ) : ℝ × P) ∈ 𝒞.N 1 ∩ (univ ×ˢ Ct) :=
      𝒟.curveDom_subset hC R he c hc hce 1 (by norm_num) hpD
    have hp0 : ((μ, a μ) : ℝ × P) ∈ 𝒞.N 0 ∩ (univ ×ˢ Ct) :=
      𝒟.curveDom_subset hC R he c hc hce 0 (by norm_num) hpD
    refine ⟨?_, hpD.2.2, ?_⟩
    · have := 𝒞.mem_G_fixLvl 1 hp1
      rw [perturbContraction_G, mem_perturbGerm_U] at this
      rw [← 𝒟.G₁_U 1]; exact this
    · have hsh : W.toBase 2 (𝒞.fixLvl 1 (μ, a μ)) =
          W.toBase 1 (W.shift.toBase 1 (𝒞.fixLvl 1 (μ, a μ))) := W.shift_toBase 1 _
      have hbase : (ScBanach.paramProd P W).toBase 2 (cv μ) =
          (ScBanach.paramProd P W).toBase 1 (𝒟.curveLift hC R he c hc hce (μ, a μ)) := by
        simp only [hcv, curveLift]
        rw [ScBanach.paramProd_toBase, ScBanach.paramProd_toBase, hsh, 𝒞.toBase_fixLvl 1 hp1]
      rw [hbase]
      have hcm : 𝒟.curveMap hC R he c hc hce (μ, a μ) = 0 :=
        Prod.ext (hcurve μ hμ).2 (𝒟.curveMap_snd hC R he c hc hce hp0)
      exact hcm

end Zero

end ShiftedBasicData

end Polyfold
