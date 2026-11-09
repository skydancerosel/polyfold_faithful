import Polyfold.Chapter6.SolutionOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, pp. 275–276:
**Theorem 6.6.18** (preprint Theorem 6.41, p. 229; 2017: Theorem 6.3), the two points of the
proof that `SolutionOrientation.lean` leaves open: the tangent orientation does not depend on the
chart (gap G.68), and the last paragraph, a perturbation `f + s` (gap G.69).

# The natural orientation of the solution set: charts and perturbations

## The text, paraphrased

(Theorem 6.6.18, proof) At `x ∈ S`, `T_xS = ker f'(x)`, and since `f'(x)` is onto, `T_xS` is
oriented by `o_x^f`.  If `f` is not generic, a small perturbation `s` supported near the zero set
gives `S_{f+s}` an orientation coming from `o^f`, since `det((f + s)'(x))` is oriented from
`DET(f, x)` for `x ∈ S_{f+s}`.

## What is formalized

* Linear algebra: `detEquivOfSurjective_conjDet` (for onto `S`, `S'` with `S' A = Γ S`,
  `det(S) ≅ λ(ker S)` commutes with `conjDet A Γ` and `λ(A|ker)`: the empty wedge of the cokernel
  goes to the empty wedge), `conjKerEquivOfMap` and `surjRay_conjDet` (the same on rays, after
  `ker S ≅ N ⊆ V`).
* **Gap G.68 (chart independence)**: `ChartPoint.linZero_conj` (`f'(x)` read in two chart points
  is conjugate by `A = D(τ ∘ r)(z)` and `Γ`, `scDeriv_principal_baseDeriv`);
  `ChartPoint.tangentKerEquiv`, the identification `ker f'(x) ≅ ker f'(x)` of the kernels read in
  `p` and in `p'` by the tangent map of the transition (`coe_tangentKerEquiv`: it is
  `v ↦ D(τ ∘ r)(z) v`); `ChartPoint.orTransfer_surjRay`; `ChartPoint.tangentOr_orTransfer`
  (the tangent orientation in `p'` of the transferred orientation is `λ(tangentKerEquiv)` of the
  one in `p`); and in the chart-free form, for `o ∈ Or_x^f`, `tangentOrAt_toChartOr`.
* **Gap G.69 (perturbations)**: `sectionAdd_assoc`; `ChartPoint.linSet_sectionAdd`:
  **`Lin(f + s, x) = Lin(f, x)` for every sc⁺-section `s`** (with `s' ↦ s + s'` and
  `s'' ↦ s'' − s`); hence `ChartPoint.orSectionAdd : Or_x^f ≃ Or_x^{f+s}` (`f + s` inherits the
  orientations of `f`, `orSectionAdd_apply`), through `LineOrientation.congrDetOn`.
  `ChartPoint.tangentOrOf`: for a section `g` with a zero at `x`, `g'(x)` onto and
  `g'(x) ∈ Lin(f, x)`, the orientation of `ker g'(x)` given by an orientation of `DET(f, x)`;
  `ChartPoint.pertTangentOr` (`g = f + s`), `tangentOr_orSectionAdd` (it is the tangent
  orientation of `f + s` for the inherited orientation), `tangentOrOf_orTransfer`,
  `pertTangentOr_orTransfer` and `pertTangentOrAt_toChartOr` (it does not depend on the chart
  either).  With Theorem 5.3.10 (2021; preprint Theorem 5.18, `theorem_5_18`), whose
  perturbations `s_λ` give `SolutionSetInGeneralPosition (f + s_λ)` and hence `(f + s_λ)'(x)`
  onto at every `x ∈ S_{f+s_λ}`, every `o ∈ Or_x^f` orients every `T_xS_{f+s_λ}` chart
  independently.
* `toChartOr_eq_orTransfer`: `toChartOr` into `c'` is `toChartOr` into `c` followed by
  `orTransfer`.

## What this makes unnecessary

* Gap G.68 ("the compatibility of the tangent orientations read in two charts at the same point
  is not formalized", `SolutionOrientation.lean`): closed by `tangentOrAt_toChartOr`.
* Gap G.69 ("the perturbation `s` when `f` is not generic, and the orientation of `S_{f+s}` from
  `o_f`"): closed at each point (`linSet_sectionAdd`, `orSectionAdd`, `tangentOr_orSectionAdd`,
  `pertTangentOrAt_toChartOr`).  **Not closed**: that the inherited orientations
  `y ↦ orSectionAdd(o_y)` form an orientation of `f + s` in the sense of Definition 6.6.16
  (`IsSectionOrientation`), which is what `theorem_6_41` needs to give their continuity along
  paths of zeros of `f + s`.  It needs push-forward data for `(f + s, S)` to be read as data for
  `(f, S + s̃)` (`IsStabKernels`, `IsPush`) through the identification `orSectionAdd`.

## Reading

As in `SolutionOrientation.lean`: `T_xS = ker f'(x)` is read in a chart as `ker Lin(z) ⊆ E₀`.  Two
readings in the chart points `p`, `p'` at `x` are identified by the tangent map `D(τ ∘ r)(z)` of
the transition (`transferT`), which is the identification of `T_xX` in the two charts.
-/

open Module TensorProduct Bundle Topology Set

noncomputable section

namespace Polyfold

universe u v

/-! ### Onto operators and conjugations -/

section SurjConj

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']

variable (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F') {S : E →L[ℝ] F} {S' : E' →L[ℝ] F'}

/-- **`det(S) ≅ λ(ker S)` commutes with conjugations** for onto `S`, `S'` with `S' A = Γ S`:
`det(S) → det(S') → λ(ker S')` is `det(S) → λ(ker S) → λ(ker S')`, `λ(A|ker)` (the cokernels are
`{0}`, and the empty wedge goes to the empty wedge). -/
theorem detEquivOfSurjective_conjDet (hS : Function.Surjective S)
    (hS' : Function.Surjective S') (h : ∀ v, S' (A v) = Γ (S v)) :
    (conjDet A Γ h).trans (detEquivOfSurjective hS') =
      (detEquivOfSurjective hS).trans (maxPowEquiv (conjKerEquiv A Γ h)) := by
  apply LinearEquiv.toLinearMap_injective
  refine TensorProduct.ext' fun w ξ => ?_
  change detEquivOfSurjective hS' (conjDet A Γ h (w ⊗ₜ ξ)) =
    maxPowEquiv (conjKerEquiv A Γ h) (detEquivOfSurjective hS (w ⊗ₜ ξ))
  rw [conjDet, TensorProduct.congr_tmul, detEquivOfSurjective_tmul, detEquivOfSurjective_tmul,
    LinearEquiv.map_smul]
  congr 1
  change ξ (maxPowEquiv (conjCokerEquiv A Γ h).symm (emptyWedge _ _)) = ξ (emptyWedge _ _)
  rw [emptyWedge, emptyWedge, maxPowEquiv_wedge]
  congr 1

variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V']
  [NormedSpace ℝ V']

/-- **The kernels of conjugate operators, read in `V` and `V'`**: for `N = j(ker S)`,
`N' = j'(ker S')`, `N ≅ ker S ≅ ker S' ≅ N'`, the middle map being `A` (`conjKerEquiv`). -/
def conjKerEquivOfMap (h : ∀ v, S' (A v) = Γ (S v)) (j : E →L[ℝ] V) (hj : Function.Injective j)
    {N : Submodule ℝ V} (hN : (LinearMap.ker (S : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N)
    (j' : E' →L[ℝ] V') (hj' : Function.Injective j') {N' : Submodule ℝ V'}
    (hN' : (LinearMap.ker (S' : E' →ₗ[ℝ] F')).map (j' : E' →ₗ[ℝ] V') = N') : N ≃ₗ[ℝ] N' :=
  (kerEquivOfMap S j hj hN).symm.trans ((conjKerEquiv A Γ h).trans (kerEquivOfMap S' j' hj' hN'))

/-- `conjKerEquivOfMap` is `j v ↦ j' (A v)`. -/
theorem coe_conjKerEquivOfMap (h : ∀ v, S' (A v) = Γ (S v)) (j : E →L[ℝ] V)
    (hj : Function.Injective j) {N : Submodule ℝ V}
    (hN : (LinearMap.ker (S : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N) (j' : E' →L[ℝ] V')
    (hj' : Function.Injective j') {N' : Submodule ℝ V'}
    (hN' : (LinearMap.ker (S' : E' →ₗ[ℝ] F')).map (j' : E' →ₗ[ℝ] V') = N')
    (v : LinearMap.ker (S : E →ₗ[ℝ] F)) :
    (conjKerEquivOfMap A Γ h j hj hN j' hj' hN' (kerEquivOfMap S j hj hN v) : V') = j' (A v) := by
  rw [conjKerEquivOfMap, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.trans_apply, coe_kerEquivOfMap, coe_conjKerEquiv_apply]

/-- **`surjRay` commutes with conjugations**: for onto `S`, `S'` with `S' A = Γ S`, the ray
`conjDet(r)` of `det(S')` read in `λ(N')` is `λ(N ≅ N')` of `r` read in `λ(N)`. -/
theorem surjRay_conjDet (hS : Function.Surjective S) (hS' : Function.Surjective S')
    (h : ∀ v, S' (A v) = Γ (S v)) (j : E →L[ℝ] V) (hj : Function.Injective j)
    {N : Submodule ℝ V} (hN : (LinearMap.ker (S : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N)
    (j' : E' →L[ℝ] V') (hj' : Function.Injective j') {N' : Submodule ℝ V'}
    (hN' : (LinearMap.ker (S' : E' →ₗ[ℝ] F')).map (j' : E' →ₗ[ℝ] V') = N')
    (r : Module.Ray ℝ (fredholmDet S)) :
    surjRay hS' j' hj' hN' (Module.Ray.map (conjDet A Γ h) r) =
      Module.Ray.map (maxPowEquiv (conjKerEquivOfMap A Γ h j hj hN j' hj' hN'))
        (surjRay hS j hj hN r) := by
  change Module.Ray.map (maxPowEquiv (kerEquivOfMap S' j' hj' hN'))
      (Module.Ray.map (detEquivOfSurjective hS') (Module.Ray.map (conjDet A Γ h) r)) =
    Module.Ray.map (maxPowEquiv (conjKerEquivOfMap A Γ h j hj hN j' hj' hN'))
      (Module.Ray.map (maxPowEquiv (kerEquivOfMap S j hj hN))
        (Module.Ray.map (detEquivOfSurjective hS) r))
  rw [ray_map_map (conjDet A Γ h) (detEquivOfSurjective hS'),
    ray_map_map ((conjDet A Γ h).trans (detEquivOfSurjective hS'))
      (maxPowEquiv (kerEquivOfMap S' j' hj' hN')),
    ray_map_map (detEquivOfSurjective hS) (maxPowEquiv (kerEquivOfMap S j hj hN)),
    ray_map_map ((detEquivOfSurjective hS).trans (maxPowEquiv (kerEquivOfMap S j hj hN)))
      (maxPowEquiv (conjKerEquivOfMap A Γ h j hj hN j' hj' hN'))]
  have hκ : (kerEquivOfMap S j hj hN).trans (conjKerEquivOfMap A Γ h j hj hN j' hj' hN') =
      (conjKerEquiv A Γ h).trans (kerEquivOfMap S' j' hj' hN') := LinearEquiv.ext fun v => by
    rw [LinearEquiv.trans_apply, conjKerEquivOfMap, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
  have key : ((conjDet A Γ h).trans (detEquivOfSurjective hS')).trans
      (maxPowEquiv (kerEquivOfMap S' j' hj' hN')) =
      ((detEquivOfSurjective hS).trans (maxPowEquiv (kerEquivOfMap S j hj hN))).trans
        (maxPowEquiv (conjKerEquivOfMap A Γ h j hj hN j' hj' hN')) := by
    rw [detEquivOfSurjective_conjDet A Γ hS hS' h, LinearEquiv.trans_assoc,
      LinearEquiv.trans_assoc, ← maxPowEquiv_trans, ← maxPowEquiv_trans, hκ]
  rw [key]

end SurjConj

/-! ### The orientations over equal sets of operators -/

section CongrDetOn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Orientations of `DET` over equal sets** `C = C'` of Fredholm operators are the same. -/
def LineOrientation.congrDetOn {C C' : Set (E →L[ℝ] F)} (h : C = C')
    (hC : ∀ T ∈ C, T.IsFredholm) (hC' : ∀ T ∈ C', T.IsFredholm) :
    LineOrientation (DetOn C hC) ≃ LineOrientation (DetOn C' hC') := by
  subst h
  exact Equiv.refl _

/-- `congrDetOn` does not change the values. -/
theorem LineOrientation.congrDetOn_apply {C C' : Set (E →L[ℝ] F)} (h : C = C')
    (hC : ∀ T ∈ C, T.IsFredholm) (hC' : ∀ T ∈ C', T.IsFredholm)
    (o : LineOrientation (DetOn C hC)) {L : E →L[ℝ] F} (hL : L ∈ C') :
    LineOrientation.congrDetOn h hC hC' o ⟨L, hL⟩ = o ⟨L, h ▸ hL⟩ := by
  subst h
  rfl

end CongrDetOn

/-! ### `(f + s) + s' = f + (s + s')` -/

section Assoc

variable {X : Type u} {Y : Type v} {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]

/-- **`(f + s) + s' = f + (s + s')`** for sections. -/
lemma sectionAdd_assoc {f s s' : X → Y} (hf : IsSection P f) (hs : IsSection P s)
    (hs' : IsSection P s') :
    sectionAdd P (sectionAdd P f s) s' = sectionAdd P f (sectionAdd P s s') := by
  funext x
  rw [sectionAdd_apply (hf.sectionAdd hs) hs', sectionAdd_apply hf (hs.sectionAdd hs')]
  congr 1
  have hA : (⟨sectionAdd P f s x, (hf.sectionAdd hs) x⟩ : P ⁻¹' {x}) =
      ⟨f x, hf x⟩ + ⟨s x, hs x⟩ := Subtype.ext (sectionAdd_apply hf hs x)
  have hB : (⟨sectionAdd P s s' x, (hs.sectionAdd hs') x⟩ : P ⁻¹' {x}) =
      ⟨s x, hs x⟩ + ⟨s' x, hs' x⟩ := Subtype.ext (sectionAdd_apply hs hs' x)
  rw [hA, hB, add_assoc]

end Assoc

/-! ### The tangent orientation in two chart points (gap G.68) and for `f + s` (gap G.69) -/

section Charts

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace ChartPoint

variable {x : X} (p p' : ChartPoint B x)

/-- **`g'(x)` read in two chart points is conjugate**: at a zero `x` of an sc-Fredholm `g`,
`g'(x)_{p'} ∘ A = Γ ∘ g'(x)_p` for `A = D(τ ∘ r)(z)` (`transferT`) and `Γ` (`transferK`)
(`scDeriv_principal_baseDeriv`). -/
theorem linZero_conj {g : X → Y} (hg : B.IsScFredholmSection g) (hx : IsZeroAt P g x)
    (v : ↥p.T) : p'.linZero hg hx (p.transferT p' v) = p.transferK p' (p.linZero hg hx v) := by
  apply Subtype.ext
  rw [coe_linZero, coe_transferK_apply, coe_linZero, linAt_apply, linAt_apply,
    coe_transferT_apply]
  exact p.scDeriv_principal_baseDeriv p' hg.isScSmooth hx v

/-- **`T_xS = ker g'(x)` read in `p` and in `p'`**: the kernels `ker Lin(z) ⊆ E₀` and
`ker Lin(z') ⊆ E₀'` are identified by `A = D(τ ∘ r)(z)` (`coe_tangentKerEquiv`), the tangent map
of the transition. -/
def tangentKerEquiv {g : X → Y} (hg : B.IsScFredholmSection g) (hx : IsZeroAt P g x) :
    p.c.linKer g p.z ≃ₗ[ℝ] p'.c.linKer g p'.z :=
  conjKerEquivOfMap (p.transferT p') (p.transferK p') (p.linZero_conj p' hg hx) p.T.subtypeL
    Subtype.val_injective (p.map_ker_linZero hg hx) p'.T.subtypeL Subtype.val_injective
    (p'.map_ker_linZero hg hx)

/-- `tangentKerEquiv` is `v ↦ D(τ ∘ r)(z) v`. -/
theorem coe_tangentKerEquiv {g : X → Y} (hg : B.IsScFredholmSection g) (hx : IsZeroAt P g x)
    (v : p.c.linKer g p.z) :
    (p.tangentKerEquiv p' hg hx v : p'.c.φ.model.E 0) = p.baseDeriv p' v := by
  obtain ⟨w, rfl⟩ := (kerEquivOfMap _ p.T.subtypeL Subtype.val_injective
    (p.map_ker_linZero hg hx)).surjective v
  exact (coe_conjKerEquivOfMap _ _ (p.linZero_conj p' hg hx) _ _ (p.map_ker_linZero hg hx) _ _
    (p'.map_ker_linZero hg hx) w).trans rfl

/-- **`orTransfer` read on onto operators**: for onto `L ∈ Lin_p(f, x)` and
`L' ∈ Lin_{p'}(f, x)` with `L' A = Γ L`, the transferred orientation at `L'` read in
`λ(ker L')` is `λ(A|ker)` of the orientation at `L` read in `λ(ker L)` (`orTransfer_apply`,
`surjRay_conjDet`). -/
theorem orTransfer_surjRay (hf : B.IsScFredholmSection f) (hxs : x ∈ PX.smoothSet)
    (o : p.Or f hf) {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) (hLs : Function.Surjective L)
    {L' : ↥p'.T →L[ℝ] ↥p'.K} (hL' : L' ∈ p'.linSet f) (hL's : Function.Surjective L')
    (hconj : ∀ v, L' (p.transferT p' v) = p.transferK p' (L v))
    {N : Submodule ℝ (p.c.φ.model.E 0)}
    (hN : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N)
    {N' : Submodule ℝ (p'.c.φ.model.E 0)}
    (hN' : (LinearMap.ker (L' : ↥p'.T →ₗ[ℝ] ↥p'.K)).map
      (p'.T.subtypeL : ↥p'.T →ₗ[ℝ] p'.c.φ.model.E 0) = N') :
    surjRay hL's p'.T.subtypeL Subtype.val_injective hN'
        (p'.orEquivRay hf hL' (p.orTransfer p' hf hxs o)) =
      Module.Ray.map (maxPowEquiv (conjKerEquivOfMap (p.transferT p') (p.transferK p') hconj
          p.T.subtypeL Subtype.val_injective hN p'.T.subtypeL Subtype.val_injective hN'))
        (surjRay hLs p.T.subtypeL Subtype.val_injective hN (p.orEquivRay hf hL o)) := by
  have heq : L' = (p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L ∘L
      (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T) :=
    ContinuousLinearMap.ext fun w => by
      have h := hconj (p'.transferT p w)
      rwa [p'.transferT_trans_apply p p' w, p'.transferT_self_apply w] at h
  subst heq
  exact (congrArg (surjRay hL's p'.T.subtypeL Subtype.val_injective hN')
    (p.orTransfer_apply p' hf hxs o hL)).trans
    (surjRay_conjDet _ _ hLs hL's _ _ _ hN _ _ hN' _)

/-- **The orientation of `ker g'(x)` given by an orientation of `DET(f, x)`**: for a section `g`
with a zero at `x`, `g'(x)` onto and `g'(x) ∈ Lin(f, x)`, `o ↦ o(g'(x))` read in
`λ(ker g'(x))` (`surjRay`).  For `g = f` it is `tangentOr` (`tangentOrOf_self`); for `g = f + s` it
is the text's "`det((f + s)'(x))` has an orientation coming from `DET(f, x)`" (`pertTangentOr`). -/
def tangentOrOf (hf : B.IsScFredholmSection f) {g : X → Y} (hg : B.IsScFredholmSection g)
    (hx : IsZeroAt P g x) (hgL : B.IsLinSurjAt g x) (hmem : p.linZero hg hx ∈ p.linSet f) :
    p.Or f hf ≃ Module.Ray ℝ (maxPow (p.c.linKer g p.z)) :=
  (p.orEquivRay hf hmem).trans (surjRay (p.linZero_surjective hg hx hgL) p.T.subtypeL
    Subtype.val_injective (p.map_ker_linZero hg hx))

/-- For `g = f`, `tangentOrOf` is the tangent orientation `tangentOr`. -/
theorem tangentOrOf_self (hf : B.IsScFredholmSection f) (hx : IsZeroAt P f x)
    (hL : B.IsLinSurjAt f x) :
    p.tangentOrOf hf hf hx hL (p.linZero_mem_linSet hf hx) = p.tangentOr hf hx hL :=
  rfl

/-- **`tangentOrOf` does not depend on the chart point**: read in `p'`, the orientation
transferred from `p` (`orTransfer`) gives `λ(A|ker)` of the one read in `p`, where
`A = D(τ ∘ r)(z)` (`tangentKerEquiv`). -/
theorem tangentOrOf_orTransfer (hf : B.IsScFredholmSection f) {g : X → Y}
    (hg : B.IsScFredholmSection g) (hx : IsZeroAt P g x) (hgL : B.IsLinSurjAt g x)
    (hmem : p.linZero hg hx ∈ p.linSet f) (hmem' : p'.linZero hg hx ∈ p'.linSet f)
    (hxs : x ∈ PX.smoothSet) (o : p.Or f hf) :
    p'.tangentOrOf hf hg hx hgL hmem' (p.orTransfer p' hf hxs o) =
      Module.Ray.map (maxPowEquiv (p.tangentKerEquiv p' hg hx))
        (p.tangentOrOf hf hg hx hgL hmem o) :=
  p.orTransfer_surjRay p' hf hxs o hmem (p.linZero_surjective hg hx hgL) hmem'
    (p'.linZero_surjective hg hx hgL) (p.linZero_conj p' hg hx) (p.map_ker_linZero hg hx)
    (p'.map_ker_linZero hg hx)

/-- **Gap G.68 in chart points**: the tangent orientation in `p'` of the orientation transferred
from `p` is `λ(A|ker)` of the tangent orientation in `p`, `A = D(τ ∘ r)(z)`. -/
theorem tangentOr_orTransfer (hf : B.IsScFredholmSection f) (hx : IsZeroAt P f x)
    (hL : B.IsLinSurjAt f x) (hxs : x ∈ PX.smoothSet) (o : p.Or f hf) :
    p'.tangentOr hf hx hL (p.orTransfer p' hf hxs o) =
      Module.Ray.map (maxPowEquiv (p.tangentKerEquiv p' hf hx)) (p.tangentOr hf hx hL o) :=
  p.tangentOrOf_orTransfer p' hf hf hx hL _ _ hxs o

/-- **Gap G.69: `Lin(f + s, x) = Lin(f, x)`** for an sc⁺-section `s` (2021 Definition 6.2.1;
preprint Definition 6.1): `s'` for `f + s` gives `s + s'` for `f` (`sectionAdd_assoc`,
`IsScPlusSection.add`), and `s''` for `f` gives `s'' − s` for `f + s`
(`sectionAdd_sectionAdd_sectionDiff`, `IsScPlusSection.smul_left`). -/
theorem linSet_sectionAdd (hf : IsSection P f) {s : X → Y} (hs : B.IsScPlusSection s) :
    p.linSet (sectionAdd P f s) = p.linSet f := by
  ext L
  constructor
  · rintro ⟨s', hs', hz, a, ha, hLa⟩
    refine ⟨sectionAdd P s s', hs.add hs', ?_, a, ha, ?_⟩
    · rwa [← sectionAdd_assoc hf hs.1 hs'.1]
    · rwa [← sectionAdd_assoc hf hs.1 hs'.1]
  · rintro ⟨s'', hs'', hz, a, ha, hLa⟩
    refine ⟨sectionDiff P s'' s, hs''.add (hs.smul_left (isScSmoothMap_real_const (-1))), ?_, a,
      ha, ?_⟩
    · rwa [sectionAdd_sectionAdd_sectionDiff hf hs.1 hs''.1]
    · rwa [sectionAdd_sectionAdd_sectionDiff hf hs.1 hs''.1]

/-- **`f + s` inherits the orientations of `f`**: `Or_x^f ≃ Or_x^{f+s}`, the orientations of
`DET` over the same set `Lin(f + s, x) = Lin(f, x)`. -/
def orSectionAdd (hf : B.IsScFredholmSection f) {s : X → Y} (hs : B.IsScPlusSection s) :
    p.Or f hf ≃ p.Or (sectionAdd P f s) (theorem_3_15 hf hs) :=
  LineOrientation.congrDetOn (p.linSet_sectionAdd hf.isScSmooth.1 hs).symm _ _

/-- `orSectionAdd` does not change the values. -/
theorem orSectionAdd_apply (hf : B.IsScFredholmSection f) {s : X → Y}
    (hs : B.IsScPlusSection s) (o : p.Or f hf) {L : ↥p.T →L[ℝ] ↥p.K}
    (hL : L ∈ p.linSet (sectionAdd P f s)) :
    p.orSectionAdd hf hs o ⟨L, hL⟩ = o ⟨L, p.linSet_sectionAdd hf.isScSmooth.1 hs ▸ hL⟩ :=
  LineOrientation.congrDetOn_apply _ _ _ o hL

/-- At a zero `x` of `f + s`, `(f + s)'(x) ∈ Lin(f, x)`. -/
theorem linZero_mem_linSet_of_sectionAdd (hf : B.IsScFredholmSection f) {s : X → Y}
    (hs : B.IsScPlusSection s) (hx : IsZeroAt P (sectionAdd P f s) x) :
    p.linZero (theorem_3_15 hf hs) hx ∈ p.linSet f :=
  p.linSet_sectionAdd hf.isScSmooth.1 hs ▸ p.linZero_mem_linSet (theorem_3_15 hf hs) hx

/-- **The orientation of `T_xS_{f+s}` coming from `DET(f, x)`** (the last paragraph of the proof
of Theorem 6.6.18): at a zero `x` of `f + s` with `(f + s)'(x)` onto, `o ↦ o((f + s)'(x))` read
in `λ(ker (f + s)'(x))`. -/
def pertTangentOr (hf : B.IsScFredholmSection f) {s : X → Y} (hs : B.IsScPlusSection s)
    (hx : IsZeroAt P (sectionAdd P f s) x) (hL : B.IsLinSurjAt (sectionAdd P f s) x) :
    p.Or f hf ≃ Module.Ray ℝ (maxPow (p.c.linKer (sectionAdd P f s) p.z)) :=
  p.tangentOrOf hf (theorem_3_15 hf hs) hx hL (p.linZero_mem_linSet_of_sectionAdd hf hs hx)

/-- **`pertTangentOr` is the tangent orientation of `f + s`** for the inherited orientation
`orSectionAdd o`. -/
theorem tangentOr_orSectionAdd (hf : B.IsScFredholmSection f) {s : X → Y}
    (hs : B.IsScPlusSection s) (hx : IsZeroAt P (sectionAdd P f s) x)
    (hL : B.IsLinSurjAt (sectionAdd P f s) x) (o : p.Or f hf) :
    p.tangentOr (theorem_3_15 hf hs) hx hL (p.orSectionAdd hf hs o) =
      p.pertTangentOr hf hs hx hL o :=
  congrArg (surjRay (p.linZero_surjective (theorem_3_15 hf hs) hx hL) p.T.subtypeL
    Subtype.val_injective (p.map_ker_linZero (theorem_3_15 hf hs) hx))
    (p.orSectionAdd_apply hf hs o (p.linZero_mem_linSet (theorem_3_15 hf hs) hx))

/-- **`pertTangentOr` does not depend on the chart point** (`tangentOrOf_orTransfer`). -/
theorem pertTangentOr_orTransfer (hf : B.IsScFredholmSection f) {s : X → Y}
    (hs : B.IsScPlusSection s) (hx : IsZeroAt P (sectionAdd P f s) x)
    (hL : B.IsLinSurjAt (sectionAdd P f s) x) (hxs : x ∈ PX.smoothSet) (o : p.Or f hf) :
    p'.pertTangentOr hf hs hx hL (p.orTransfer p' hf hxs o) =
      Module.Ray.map (maxPowEquiv (p.tangentKerEquiv p' (theorem_3_15 hf hs) hx))
        (p.pertTangentOr hf hs hx hL o) :=
  p.tangentOrOf_orTransfer p' hf _ hx hL _ _ hxs o

end ChartPoint

/-- `toChartOr` into `c'` is `toChartOr` into `c` followed by the transfer from `c` to `c'`
(`ChartPoint.orTransfer_trans`). -/
theorem toChartOr_eq_orTransfer (hf : B.IsScFredholmSection f) {x : X} (hs : x ∈ PX.smoothSet)
    (o : Orx f hf x hs) {c c' : StrongBundleChart PX P} (hc : B.IsChart c) (hc' : B.IsChart c')
    (hxc : x ∈ c.φ.source) (hxc' : x ∈ c'.φ.source) :
    toChartOr hf hs c' hc' hxc' o = (chartPtOf c hc hxc hs).orTransfer (chartPtOf c' hc' hxc' hs)
      hf hs (toChartOr hf hs c hc hxc o) := by
  rw [toChartOr, toChartOr, ← ChartPoint.orTransfer_trans _ (chartPtOf c hc hxc hs) _ hf hs]
  rfl

/-- **Gap G.68: the tangent orientation of `T_xS` does not depend on the chart.** For an
orientation `o ∈ Or_x^f` at a zero `x` with `f'(x)` onto and two charts `c`, `c'` at `x`, the
orientation `o` read in `c'` gives on `T_xS = ker f'(x)` the image under the tangent map
`D(τ ∘ r)(z)` of the transition (`tangentKerEquiv`) of the orientation read in `c`. -/
theorem tangentOrAt_toChartOr (hf : B.IsScFredholmSection f) {x : X} (hs : x ∈ PX.smoothSet)
    (hx0 : IsZeroAt P f x) (hL : B.IsLinSurjAt f x) (o : Orx f hf x hs)
    {c c' : StrongBundleChart PX P} (hc : B.IsChart c) (hc' : B.IsChart c')
    (hxc : x ∈ c.φ.source) (hxc' : x ∈ c'.φ.source) :
    (chartPtOf c' hc' hxc' hs).tangentOr hf hx0 hL (toChartOr hf hs c' hc' hxc' o) =
      Module.Ray.map (maxPowEquiv ((chartPtOf c hc hxc hs).tangentKerEquiv
          (chartPtOf c' hc' hxc' hs) hf hx0))
        ((chartPtOf c hc hxc hs).tangentOr hf hx0 hL (toChartOr hf hs c hc hxc o)) := by
  rw [toChartOr_eq_orTransfer hf hs o hc hc' hxc hxc']
  exact (chartPtOf c hc hxc hs).tangentOr_orTransfer _ hf hx0 hL hs _

/-- **Gap G.69: the orientation of `T_xS_{f+s}` coming from `o ∈ Or_x^f` does not depend on the
chart** either (`pertTangentOr_orTransfer`). -/
theorem pertTangentOrAt_toChartOr (hf : B.IsScFredholmSection f) {s : X → Y}
    (hsp : B.IsScPlusSection s) {x : X} (hs : x ∈ PX.smoothSet)
    (hx0 : IsZeroAt P (sectionAdd P f s) x) (hL : B.IsLinSurjAt (sectionAdd P f s) x)
    (o : Orx f hf x hs) {c c' : StrongBundleChart PX P} (hc : B.IsChart c) (hc' : B.IsChart c')
    (hxc : x ∈ c.φ.source) (hxc' : x ∈ c'.φ.source) :
    (chartPtOf c' hc' hxc' hs).pertTangentOr hf hsp hx0 hL (toChartOr hf hs c' hc' hxc' o) =
      Module.Ray.map (maxPowEquiv ((chartPtOf c hc hxc hs).tangentKerEquiv
          (chartPtOf c' hc' hxc' hs) (theorem_3_15 hf hsp) hx0))
        ((chartPtOf c hc hxc hs).pertTangentOr hf hsp hx0 hL (toChartOr hf hs c hc hxc o)) := by
  rw [toChartOr_eq_orTransfer hf hs o hc hc' hxc hxc']
  exact (chartPtOf c hc hxc hs).pertTangentOr_orTransfer _ hf hsp hx0 hL hs _

end Charts

end Polyfold
