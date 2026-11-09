import Polyfold.Chapter11.StrongBundleUpToEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.5, **Proposition 11.5.1** (p. 547; 2017: Proposition 11.6, p. 399):
conditions (1) and (2) of Definition 8.3.5 for the pull-back and push-forward of auxiliary norms.

# Auxiliary norms under generalized strong bundle isomorphisms: conditions (1) and (2)

## The text, paraphrased

(p. 547) For a generalized strong bundle isomorphism `[D] : W → W'` and an auxiliary norm `N'`
of `(P', μ')`, the pull-back `[D]^*N'` is an auxiliary norm of `(P, μ)`, and the push-forward
`[D]_*N` of an auxiliary norm `N` of `(P, μ)` is one of `(P', μ')`; they are mutually inverse and
depend only on `|[D]|`.  The text calls this a consequence of the definitions.

## What is formalized

`Chapter11/StrongBundleUpToEquivalence.lean` has the construction, condition (3) (invariance),
continuity, the inverses and the dependence on `|[D]|` (`GenSBMap.proposition_11_5_1`).  This
file adds conditions (1) and (2) of Definition 8.3.5:
* level-`1` fibre maps as linear isomorphisms: `SBLocalization.oneFiberMor` (`μ(σ, ·)` on
  `(W_{0,1})_{s(σ)} → (W_{0,1})_{t(σ)}`), `SBLocalization.oneFiberObj` (a strong bundle
  equivalence on `(W''_{0,1})_x → (W_{0,1})_{ϕ(x)}`); transfer of a complete norm along a linear
  isomorphism, `StrongBundle.IsCompleteFiberNorm.of_linearEquiv`;
* the level-`1` behaviour at the zero section: `tendsto_zeroOne_of_tendsto_obj` (a strong bundle
  equivalence is a local homeomorphism of `W[1]` near `0`, from Definition 10.4.1 (2)) and
  `tendsto_zeroOne_μ_obj` (continuity of `μ[1]` along a local inverse of the source map);
* `SDiagram.isCompleteFiberNorm_pullNorm` (condition (1)), `SDiagram.tendsto_zeroOne_pullNorm`
  (condition (2)), `SDiagram.isAuxNorm_pullNorm`, `SDiagram.isAuxNorm_pushNorm`;
* **Proposition 11.5.1** as stated: `GenSBMap.proposition_11_5_1_book`, no added hypothesis.

## Choices

* Condition (2) for `[D]^*N'`: for `h_k` with `P(h_k) → x` and `[D]^*N'(h_k) → 0`, the proof
  fixes `σ : ϕ(x'') → x`, a local inverse `τ` of the target map at `σ` and a local inverse of `ϕ`
  at `x''`, and lifts `h_k` to `e''_k` over `g(s(τ(P(h_k))))` (by choice, with a junk value off a
  neighbourhood); then condition (2) for `N'` gives `Ψ(e''_k) → 0`, hence `e''_k → 0` and
  `h_k = μ(τ(·), Φ(e''_k)) → 0`.
* `[D]_*N` is the pull-back along the reversed diagram, so its conditions follow from the above.
-/

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### Strong bundle maps over M-polyfolds: the zero section, fibres of `Y[1]` -/

section Generic

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]

namespace StrongBundle

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {f : X → X'} {Φ : Y → Y'}

/-- A strong bundle map sends the zero of `Y_x` to the zero of `Y'_{f(x)}`. -/
theorem IsStrongBundleMap.map_fiberZero (h : B.IsStrongBundleMap B' f Φ) (x : X) :
    Φ (fiberZero P x) = fiberZero P' (f x) :=
  congrArg Subtype.val ((h.fiberMap x).map_zero)

/-- At level `[1]`: `Φ[1](0_x) = 0_{f(x)}`. -/
theorem IsStrongBundleMap.oneRestrict_zeroOne (h : B.IsStrongBundleMap B' f Φ) (x : X) :
    oneRestrict B B' Φ h.mapsTo_oneSet (B.zeroOne x) = B'.zeroOne (f x) :=
  B'.oneVal_injective (h.map_fiberZero x)

/-- **Transfer of condition (1) of Definition 5.1.1 along a linear isomorphism of fibres**: if
`N(v) = N'(L v)` on `(Y_{0,1})_x` for a linear isomorphism `L : (Y_{0,1})_x → (Y'_{0,1})_{x'}`
and `N'` is a complete norm on `(Y'_{0,1})_{x'}`, then `N` is a complete norm on `(Y_{0,1})_x`. -/
theorem IsCompleteFiberNorm.of_linearEquiv {N : B.One → ℝ} {N' : B'.One → ℝ} {x : X} {x' : X'}
    (L : B.oneFiber x ≃ₗ[ℝ] B'.oneFiber x') (hL : ∀ v, N (B.toOne v) = N' (B'.toOne (L v)))
    (h : B'.IsCompleteFiberNorm N' x') : B.IsCompleteFiberNorm N x where
  eq_zero v hv := L.injective ((h.eq_zero _ (by rw [← hL]; exact hv)).trans L.map_zero.symm)
  smul t v := by rw [hL, hL, map_smul, h.smul]
  add_le v w := by rw [hL, hL, hL, map_add]; exact h.add_le _ _
  complete u hu := by
    obtain ⟨v', hv'⟩ := h.complete (fun k => L (u k)) fun ε hε => by
      obtain ⟨n, hn⟩ := hu ε hε
      exact ⟨n, fun m hm k hk => by rw [← map_sub, ← hL]; exact hn m hm k hk⟩
    refine ⟨L.symm v', hv'.congr fun k => ?_⟩
    rw [hL, map_sub, L.apply_symm_apply]

/-- A linear isomorphism of fibres `Y_a → Y'_b` which preserves and reflects `Y_{0,1}` restricts to
a linear isomorphism `(Y_{0,1})_a → (Y'_{0,1})_b`. -/
def oneFiberEquivOf {a : X} {b : X'} (e : P ⁻¹' {a} ≃ₗ[ℝ] P' ⁻¹' {b})
    (he : ∀ v, ((e v : P' ⁻¹' {b}) : Y') ∈ B'.oneSet ↔ (v : Y) ∈ B.oneSet) :
    B.oneFiber a ≃ₗ[ℝ] B'.oneFiber b :=
  LinearEquiv.ofSubmodules e (B.oneFiber a) (B'.oneFiber b) (by
    ext w
    refine ⟨?_, fun hw => ⟨e.symm w, ?_, e.apply_symm_apply w⟩⟩
    · rintro ⟨v, hv, rfl⟩
      exact (he v).2 hv
    · change ((e.symm w : P ⁻¹' {a}) : Y) ∈ B.oneSet
      rw [← he, e.apply_symm_apply]; exact hw)

@[simp] lemma oneFiberEquivOf_val {a : X} {b : X'} (e : P ⁻¹' {a} ≃ₗ[ℝ] P' ⁻¹' {b})
    (he : ∀ v, ((e v : P' ⁻¹' {b}) : Y') ∈ B'.oneSet ↔ (v : Y) ∈ B.oneSet) (v : B.oneFiber a) :
    (((oneFiberEquivOf e he v : B'.oneFiber b) : P' ⁻¹' {b}) : Y') = e v := rfl

variable (B) in
/-- `(Y_{0,1})_a = (Y_{0,1})_b` for `a = b`. -/
def oneFiberCast {a b : X} (h : a = b) : B.oneFiber a ≃ₗ[ℝ] B.oneFiber b := by
  subst h; exact LinearEquiv.refl ℝ _

@[simp] lemma oneFiberCast_val {a b : X} (h : a = b) (v : B.oneFiber a) :
    (((B.oneFiberCast h v : B.oneFiber b) : P ⁻¹' {b}) : Y) = ((v : P ⁻¹' {a}) : Y) := by
  subst h; rfl

/-- `0_x` as the image of `0 ∈ (Y_{0,1})_x`. -/
lemma toOne_zero (x : X) : B.toOne (0 : B.oneFiber x) = B.zeroOne x := rfl

end StrongBundle

end Generic

namespace SBLocalization

open EPLocalization StrongBundle

variable {A A' C : SEP.{u}}

/-! ### The fibres of `W[1]` under `μ` and under strong bundle equivalences -/

/-- `μ(σ, ·)` maps `W_{0,1}` into `W_{0,1}`. -/
theorem μ_mem_oneSet (A : SEP.{u}) (q : pullbackSpace A.P A.X.src)
    (h : (q : A.Mor × A.W).2 ∈ A.B.oneSet) : A.E.μ q ∈ A.B.oneSet :=
  A.E.isStrongBundleMap.mapsTo_oneSet ((A.B.mem_oneSet_pullback_iff A.X.isScSmoothMap_src q).2 h)

/-- **`μ(σ, ·) : (W_{0,1})_{s(σ)} → (W_{0,1})_{t(σ)}` is a linear isomorphism** (the restriction of
`fiberMorEquiv`; its inverse `μ(σ⁻¹, ·)` maps `W_{0,1}` into `W_{0,1}` as well). -/
def oneFiberMor (A : SEP.{u}) (σ : A.Mor) :
    A.B.oneFiber (A.X.src σ) ≃ₗ[ℝ] A.B.oneFiber (A.X.tgt σ) :=
  oneFiberEquivOf (A.E.fiberMorEquiv σ).toLinearEquiv fun v => by
    refine ⟨fun h => ?_, fun h => μ_mem_oneSet A _ h⟩
    have e := (A.E.fiberMorEquiv σ).symm_apply_apply v
    rw [← e]
    exact μ_mem_oneSet A _ h

@[simp] lemma oneFiberMor_symm_val (A : SEP.{u}) (σ : A.Mor) (v : A.B.oneFiber (A.X.tgt σ)) :
    ((((oneFiberMor A σ).symm v : A.B.oneFiber (A.X.src σ)) : A.P ⁻¹' {A.X.src σ}) : A.W) =
      A.E.μ ⟨(A.X.inv σ, ((v : A.P ⁻¹' {A.X.tgt σ}) : A.W)),
        (v : A.P ⁻¹' {A.X.tgt σ}).2.trans (A.X.src_inv σ).symm⟩ := rfl

variable {F : C ⟶ A}

/-- **A strong bundle equivalence reflects `W_{0,1}`**: if `Φ(v) ∈ W_{0,1}` then `v ∈ W''_{0,1}`
(from the level-`[1]` part of Definition 10.4.1 (2) and the injectivity of `Φ` on fibres). -/
theorem mem_oneSet_of_obj_mem (hF : SEP.equivalences F) {v : C.W}
    (h : (SEP.Hom.Φ F).obj v ∈ A.B.oneSet) : v ∈ C.B.oneSet := by
  obtain ⟨U, U', hx, hi⟩ := (sbe hF).isLocalStrongBundleIso_obj (C.P v)
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  set w' := A.B.oneMk _ h
  have hw' : w' ∈ (A.P ∘ A.B.oneVal) ⁻¹' U' := by
    change A.P ((SEP.Hom.Φ F).obj v) ∈ U'
    rw [(sbe hF).covers]; exact hg.mapsTo hx
  have h2 := hΨ₁.mapsTo_inv hw'
  have h3 : (SEP.Hom.Φ F).obj (C.B.oneVal (Ψ₁ w')) = (SEP.Hom.Φ F).obj v :=
    congrArg A.B.oneVal (hΨ₁.right_inv w' hw')
  have hP : C.P (C.B.oneVal (Ψ₁ w')) = C.P v := by
    have e := congrArg A.P h3
    rw [(sbe hF).covers, (sbe hF).covers] at e
    have e1 : g ((SEP.Hom.ϕ F).obj (C.P (C.B.oneVal (Ψ₁ w')))) = C.P (C.B.oneVal (Ψ₁ w')) :=
      hg.left_inv _ h2
    have e2 := hg.left_inv _ hx
    rw [e] at e1
    exact e1.symm.trans e2
  rw [← (sbe hF).eq_of_obj_eq hP h3]
  exact C.B.oneVal_mem _

/-- **The fibre map `Φ : (W''_{0,1})_{x''} → (W_{0,1})_{ϕ(x'')}` of a strong bundle equivalence is a
linear isomorphism.** -/
def oneFiberObj (hF : SEP.equivalences F) (x : C.Obj) :
    C.B.oneFiber x ≃ₗ[ℝ] A.B.oneFiber ((SEP.Hom.ϕ F).obj x) :=
  oneFiberEquivOf ((sbe hF).fiberEquiv x).toLinearEquiv fun _ =>
    ⟨mem_oneSet_of_obj_mem hF,
      fun h => (SEP.Hom.isStrongBundleFunctor F).isStrongBundleMap_obj.mapsTo_oneSet h⟩

@[simp] lemma oneFiberObj_val (hF : SEP.equivalences F) (x : C.Obj) (v : C.B.oneFiber x) :
    (((oneFiberObj hF x v : A.B.oneFiber ((SEP.Hom.ϕ F).obj x)) :
      A.P ⁻¹' {(SEP.Hom.ϕ F).obj x}) : A.W) =
      (SEP.Hom.Φ F).obj ((v : C.P ⁻¹' {x}) : C.W) := rfl

theorem obj_oneFiberObj_symm_val (hF : SEP.equivalences F) (x : C.Obj)
    (v : A.B.oneFiber ((SEP.Hom.ϕ F).obj x)) :
    (SEP.Hom.Φ F).obj ((((oneFiberObj hF x).symm v : C.B.oneFiber x) : C.P ⁻¹' {x}) : C.W) =
      ((v : A.P ⁻¹' {(SEP.Hom.ϕ F).obj x}) : A.W) := by
  rw [← oneFiberObj_val hF x, LinearEquiv.apply_symm_apply]

/-! ### Convergence to the zero section at level `[1]` -/

/-- `μ(σ, 0_{s(σ)}) = 0_{t(σ)}`. -/
theorem μ_fiberZero (A : SEP.{u}) (σ : A.Mor) (h : A.P (fiberZero A.P (A.X.src σ)) = A.X.src σ) :
    A.E.μ ⟨(σ, fiberZero A.P (A.X.src σ)), h⟩ = fiberZero A.P (A.X.tgt σ) :=
  congrArg Subtype.val ((A.E.fiberMor σ).map_zero)

/-- **A strong bundle equivalence is a local homeomorphism of `W[1]` near the zero section**: if
`P''(e_k) → x''` and `Φ(e_k) → 0_{ϕ(x'')}` in `W_{0,1}`, then `e_k → 0_{x''}` in `W''_{0,1}`
(from the level-`[1]` part of Definition 10.4.1 (2)). -/
theorem tendsto_zeroOne_of_tendsto_obj (hF : SEP.equivalences F) {e : ℕ → C.B.One} {x : C.Obj}
    (he : Tendsto (fun k => C.P (C.B.oneVal (e k))) atTop (𝓝 x))
    (hΦe : Tendsto (fun k => oneRestrict C.B A.B (SEP.Hom.Φ F).obj
      (SEP.Hom.isStrongBundleFunctor F).isStrongBundleMap_obj.mapsTo_oneSet (e k)) atTop
      (𝓝 (A.B.zeroOne ((SEP.Hom.ϕ F).obj x)))) :
    Tendsto e atTop (𝓝 (C.B.zeroOne x)) := by
  obtain ⟨U, U', hx, hi⟩ := (sbe hF).isLocalStrongBundleIso_obj x
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  have h0 : C.B.zeroOne x ∈ (C.P ∘ C.B.oneVal) ⁻¹' U := by
    change C.P (C.B.oneVal (C.B.zeroOne x)) ∈ U
    rw [C.B.proj_oneVal_zeroOne]; exact hx
  have hΦ0 := (SEP.Hom.isStrongBundleFunctor F).isStrongBundleMap_obj.oneRestrict_zeroOne x
  have hΨ0 : Ψ₁ (A.B.zeroOne ((SEP.Hom.ϕ F).obj x)) = C.B.zeroOne x := by
    rw [← hΦ0]; exact hΨ₁.left_inv _ h0
  have hmem : A.B.zeroOne ((SEP.Hom.ϕ F).obj x) ∈ (A.P ∘ A.B.oneVal) ⁻¹' U' := by
    rw [← hΦ0]; exact hΨ₁.mapsTo h0
  have hc : ContinuousAt Ψ₁ (A.B.zeroOne ((SEP.Hom.ϕ F).obj x)) :=
    hΨ₁.isScSmoothOn_inv.continuousOn.continuousAt (hΨ₁.isScSmoothOn_inv.isOpen.mem_nhds hmem)
  have h1 := hc.tendsto.comp hΦe
  rw [hΨ0] at h1
  refine h1.congr' ?_
  have hU : ∀ᶠ k in atTop, C.P (C.B.oneVal (e k)) ∈ U := he (hg.isOpen_source.mem_nhds hx)
  filter_upwards [hU] with k hk
  exact hΨ₁.left_inv _ hk

/-- **The transport `e'' ↦ μ(σ_k, Φ(e''))` near the zero section**: if `e_k → 0_{x''}` in
`W''_{0,1}`, `σ_k → σ` with `s(σ) = ϕ(x'')`, and `w_k = μ(σ_k, Φ(e_k))` eventually, then
`w_k → 0_{t(σ)}` in `W_{0,1}` (`μ[1]` is sc-smooth on the level `[1]` of the pull-back bundle,
`ρ` a local inverse of `s` at `σ`). -/
theorem tendsto_zeroOne_μ_obj (F : C ⟶ A) {σ : A.Mor} {x : C.Obj}
    (hσ : A.X.src σ = (SEP.Hom.ϕ F).obj x) {e : ℕ → C.B.One}
    (he : Tendsto e atTop (𝓝 (C.B.zeroOne x))) {σs : ℕ → A.Mor} (hσs : Tendsto σs atTop (𝓝 σ))
    {w : ℕ → A.B.One}
    (hw : ∀ᶠ k in atTop, ∃ h : A.P ((SEP.Hom.Φ F).obj (C.B.oneVal (e k))) = A.X.src (σs k),
      A.B.oneVal (w k) = A.E.μ ⟨(σs k, (SEP.Hom.Φ F).obj (C.B.oneVal (e k))), h⟩) :
    Tendsto w atTop (𝓝 (A.B.zeroOne (A.X.tgt σ))) := by
  classical
  obtain ⟨T, Vs, ρ, hσT, hρ⟩ := A.X.isLocalScDiffeo_src σ
  have hF := (SEP.Hom.isStrongBundleFunctor F).isStrongBundleMap_obj
  let ι : C.B.One → pullbackSpace A.P A.X.src := fun e =>
    if h : A.P ((SEP.Hom.Φ F).obj (C.B.oneVal e)) =
        A.X.src (ρ ((SEP.Hom.ϕ F).obj (C.P (C.B.oneVal e)))) then
      ⟨(ρ ((SEP.Hom.ϕ F).obj (C.P (C.B.oneVal e))), (SEP.Hom.Φ F).obj (C.B.oneVal e)), h⟩
    else ⟨(A.X.unit (A.P ((SEP.Hom.Φ F).obj (C.B.oneVal e))), (SEP.Hom.Φ F).obj (C.B.oneVal e)),
      (A.X.src_unit _).symm⟩
  have hι2 : ∀ e, (ι e : A.Mor × A.W).2 = (SEP.Hom.Φ F).obj (C.B.oneVal e) := fun e => by
    dsimp only [ι]; split_ifs <;> rfl
  have hιpos : ∀ e, A.P ((SEP.Hom.Φ F).obj (C.B.oneVal e)) =
      A.X.src (ρ ((SEP.Hom.ϕ F).obj (C.P (C.B.oneVal e)))) →
      (ι e : A.Mor × A.W) = (ρ ((SEP.Hom.ϕ F).obj (C.P (C.B.oneVal e))),
        (SEP.Hom.Φ F).obj (C.B.oneVal e)) := fun e h => by
    dsimp only [ι]; rw [dif_pos h]
  have hι1 : ∀ e, ι e ∈ (A.B.pullback A.X.isScSmoothMap_src).oneSet := fun e =>
    (A.B.mem_oneSet_pullback_iff A.X.isScSmoothMap_src _).2
      (by rw [hι2]; exact hF.mapsTo_oneSet (C.B.oneVal_mem e))
  let ι₁ : C.B.One → (A.B.pullback A.X.isScSmoothMap_src).One := fun e =>
    (A.B.pullback A.X.isScSmoothMap_src).oneMk (ι e) (hι1 e)
  set O : Set C.B.One := {e | (SEP.Hom.ϕ F).obj (C.P (C.B.oneVal e)) ∈ Vs} with hOdef
  have hcP : Continuous fun e : C.B.One => (SEP.Hom.ϕ F).obj (C.P (C.B.oneVal e)) :=
    (SEP.Hom.ϕ F).continuous_obj'.comp (C.B.continuous.comp C.B.continuous_oneVal)
  have hO : IsOpen O := hρ.isOpen_target.preimage hcP
  have hcond : ∀ e ∈ O, A.P ((SEP.Hom.Φ F).obj (C.B.oneVal e)) =
      A.X.src (ρ ((SEP.Hom.ϕ F).obj (C.P (C.B.oneVal e)))) := fun e he => by
    rw [hF.covers, hρ.right_inv _ he]
  have ha : C.B.toMPolyfold1.IsScSmoothOn A.X.PMor
      (pullbackProj A.P A.X.src ∘ (A.B.pullback A.X.isScSmoothMap_src).oneVal ∘ ι₁) O := by
    have hin : C.B.toMPolyfold1.IsScSmoothOn A.X.PObj
        ((SEP.Hom.ϕ F).obj ∘ (C.P ∘ C.B.oneVal)) O :=
      ((SEP.Hom.ϕ F).isScSmoothMap_obj.comp C.B.isScSmoothMap_proj1).mono hO (subset_univ _)
    refine (hρ.isScSmoothOn_inv.comp hin fun e he => he).congr fun e he => ?_
    change ρ ((SEP.Hom.ϕ F).obj (C.P (C.B.oneVal e))) = (ι e : A.Mor × A.W).1
    rw [hιpos e (hcond e he)]
  have hb : C.B.toMPolyfold1.IsScSmoothOn A.B.toMPolyfold1
      (A.B.pullbackProj'One A.X.isScSmoothMap_src ∘ ι₁) O := by
    refine (hF.isScSmoothMap_one.mono hO (subset_univ _)).congr fun e _ => ?_
    apply A.B.oneVal_injective
    change (SEP.Hom.Φ F).obj (C.B.oneVal e) = (ι e : A.Mor × A.W).2
    rw [hι2]
  have hι₁ := A.B.isScSmoothOn_to_pullback_one A.X.isScSmoothMap_src ha hb
  have hμ := MPolyfold.IsScSmoothOn.comp A.E.isStrongBundleMap.isScSmoothMap_one hι₁
    (mapsTo_univ _ _)
  have h0O : C.B.zeroOne x ∈ O := by
    change (SEP.Hom.ϕ F).obj (C.P (C.B.oneVal (C.B.zeroOne x))) ∈ Vs
    rw [C.B.proj_oneVal_zeroOne, ← hσ]; exact hρ.mapsTo hσT
  have hc := (hμ.continuousOn.continuousAt (hO.mem_nhds h0O)).tendsto.comp he
  have hρσ : ρ (A.X.src σ) = σ := hρ.left_inv σ hσT
  have hval0 : (oneRestrict _ A.B A.E.μ A.E.isStrongBundleMap.mapsTo_oneSet ∘ ι₁)
      (C.B.zeroOne x) = A.B.zeroOne (A.X.tgt σ) := by
    apply A.B.oneVal_injective
    change A.E.μ (ι (C.B.zeroOne x)) = fiberZero A.P (A.X.tgt σ)
    have hpair := hιpos _ (hcond _ h0O)
    rw [C.B.proj_oneVal_zeroOne, C.B.oneVal_zeroOne, hF.map_fiberZero, ← hσ, hρσ] at hpair
    rw [← μ_fiberZero A σ (proj_fiberZero A.P _)]
    exact A.E.μ_congr hpair
  rw [hval0] at hc
  refine hc.congr' ?_
  have hT : ∀ᶠ k in atTop, σs k ∈ T := hσs (hρ.isOpen_source.mem_nhds hσT)
  filter_upwards [hT, hw] with k hk ⟨h, hwk⟩
  apply A.B.oneVal_injective
  change A.E.μ (ι (e k)) = A.B.oneVal (w k)
  have hρk : ρ ((SEP.Hom.ϕ F).obj (C.P (C.B.oneVal (e k)))) = σs k := by
    rw [← hF.covers, h]; exact hρ.left_inv _ hk
  have hpair := hιpos (e k) (by rw [hρk]; exact h)
  rw [hwk]
  exact A.E.μ_congr (hpair.trans (by rw [hρk]))

/-! ### Condition (1) of Definition 8.3.5 for `[D]^*N'` -/

namespace SDiagram

variable (D : SDiagram A A')

/-- **Condition (1) of Definition 8.3.5 for `[D]^*N'`**: on `(W_{0,1})_x`, `[D]^*N'` is `N'`
composed with the linear isomorphism `Ψ ∘ Φ⁻¹ ∘ μ(σ⁻¹, ·) : (W_{0,1})_x → (W'_{0,1})_{ψ(x'')}`
for a morphism `σ : ϕ(x'') → x`, hence a complete norm. -/
theorem isCompleteFiberNorm_pullNorm (hΨ : SEP.equivalences D.Ψ) {N' : A'.B.One → ℝ}
    (hN'i : IsOneInvariant A' N') (hN' : ∀ x', A'.B.IsCompleteFiberNorm N' x') (x : A.Obj) :
    A.B.IsCompleteFiberNorm (D.pullNorm N') x := by
  obtain ⟨x'', σ, hs, ht⟩ := D.hΦ.isEquivalence_base.exists_iso x
  subst ht
  let L₁ : A.B.oneFiber (A.X.tgt σ) ≃ₗ[ℝ] D.B.B.oneFiber x'' :=
    ((oneFiberMor A σ).symm.trans (A.B.oneFiberCast hs)).trans
      (oneFiberObj D.isEquivalence_Φ x'').symm
  refine IsCompleteFiberNorm.of_linearEquiv (L₁.trans (oneFiberObj hΨ x'')) (fun v => ?_)
    (hN' _)
  rw [pullNorm_eq_Ψ hN'i (D.B.B.toOne (L₁ v))]
  · rfl
  · refine mk_eq_mk_of_π_eq ?_
    change A.E.toEpGroupoid.π ((SEP.Hom.Φ D.Φ).obj
      ((((oneFiberObj D.isEquivalence_Φ x'').symm
        (A.B.oneFiberCast hs ((oneFiberMor A σ).symm v)) : D.B.B.oneFiber x'') :
          D.B.P ⁻¹' {x''}) : D.B.W)) = _
    rw [obj_oneFiberObj_symm_val, oneFiberCast_val, oneFiberMor_symm_val, EpStrongBundle.π_μ]
    rfl

/-- **Condition (2) of Definition 8.3.5 for `[D]^*N'`**: if `P(w_k) → x` and `[D]^*N'(w_k) → 0`,
then `w_k → 0_x` in `W_{0,1}`.  With `σ : ϕ(x'') → x`, local inverses `τ` of `t` at `σ` and `g` of
`ϕ` at `x''`, `σ_k = τ(P(w_k))`, and `e''_k ∈ W''_{0,1}` over `g(s(σ_k))` with
`w_k = μ(σ_k, Φ(e''_k))`: then `N'(Ψ(e''_k)) = [D]^*N'(w_k) → 0`, so `Ψ(e''_k) → 0` by (2) for `N'`,
`e''_k → 0` (`tendsto_zeroOne_of_tendsto_obj`) and `w_k → 0_x` (`tendsto_zeroOne_μ_obj`). -/
theorem tendsto_zeroOne_pullNorm (hΨ : SEP.equivalences D.Ψ) {N' : A'.B.One → ℝ}
    (hN'i : IsOneInvariant A' N')
    (hN' : ∀ (w : ℕ → A'.B.One) (x : A'.Obj),
      Tendsto (fun k => A'.P (A'.B.oneVal (w k))) atTop (𝓝 x) →
      Tendsto (fun k => N' (w k)) atTop (𝓝 0) → Tendsto w atTop (𝓝 (A'.B.zeroOne x)))
    (w : ℕ → A.B.One) (x : A.Obj) (hx : Tendsto (fun k => A.P (A.B.oneVal (w k))) atTop (𝓝 x))
    (hN : Tendsto (fun k => D.pullNorm N' (w k)) atTop (𝓝 0)) :
    Tendsto w atTop (𝓝 (A.B.zeroOne x)) := by
  classical
  obtain ⟨x'', σ, hs, ht⟩ := D.hΦ.isEquivalence_base.exists_iso x
  subst ht
  obtain ⟨T, V, τ, hσT, hτ⟩ := A.X.isLocalScDiffeo_tgt σ
  obtain ⟨U₁, U₁', g, hx''U, hg⟩ := D.hΦ.isEquivalence_base.isLocalScDiffeo_obj x''
  set σs : ℕ → A.Mor := fun k => τ (A.P (A.B.oneVal (w k))) with hσsdef
  have hτσ : τ (A.X.tgt σ) = σ := hτ.left_inv σ hσT
  have htV : A.X.tgt σ ∈ V := hτ.mapsTo hσT
  have hσs : Tendsto σs atTop (𝓝 σ) := by
    have := (hτ.isScSmoothOn_inv.continuousOn.continuousAt
      (hτ.isOpen_target.mem_nhds htV)).tendsto.comp hx
    rwa [hτσ] at this
  have hsU : A.X.src σ ∈ U₁' := by rw [hs]; exact hg.mapsTo hx''U
  have hsσs : Tendsto (fun k => A.X.src (σs k)) atTop (𝓝 (A.X.src σ)) :=
    (A.X.continuous_src.tendsto σ).comp hσs
  set xs : ℕ → D.B.Obj := fun k => g (A.X.src (σs k)) with hxsdef
  have hgx : g (A.X.src σ) = x'' := by rw [hs]; exact hg.left_inv _ hx''U
  have hxs : Tendsto xs atTop (𝓝 x'') := by
    have := (hg.isScSmoothOn_inv.continuousOn.continuousAt
      (hg.isOpen_target.mem_nhds hsU)).tendsto.comp hsσs
    rwa [hgx] at this
  let good : ℕ → Prop := fun k => ∃ e : D.B.B.One, D.B.P (D.B.B.oneVal e) = xs k ∧
    ∃ h : A.P ((SEP.Hom.Φ D.Φ).obj (D.B.B.oneVal e)) = A.X.src (σs k),
      A.B.oneVal (w k) = A.E.μ ⟨(σs k, (SEP.Hom.Φ D.Φ).obj (D.B.B.oneVal e)), h⟩
  let e'' : ℕ → D.B.B.One := fun k => if h : good k then h.choose else D.B.B.zeroOne (xs k)
  have hgood : ∀ k, good k → D.B.P (D.B.B.oneVal (e'' k)) = xs k ∧
      ∃ h : A.P ((SEP.Hom.Φ D.Φ).obj (D.B.B.oneVal (e'' k))) = A.X.src (σs k),
        A.B.oneVal (w k) = A.E.μ ⟨(σs k, (SEP.Hom.Φ D.Φ).obj (D.B.B.oneVal (e'' k))), h⟩ :=
    fun k hk => by simp only [e'', dif_pos hk]; exact hk.choose_spec
  have hPe : ∀ k, D.B.P (D.B.B.oneVal (e'' k)) = xs k := fun k => by
    by_cases h : good k
    · exact (hgood k h).1
    · simp only [e'', dif_neg h]; exact D.B.B.proj_oneVal_zeroOne _
  have hev : ∀ᶠ k in atTop, good k := by
    have hV : ∀ᶠ k in atTop, A.P (A.B.oneVal (w k)) ∈ V := hx (hτ.isOpen_target.mem_nhds htV)
    have hU : ∀ᶠ k in atTop, A.X.src (σs k) ∈ U₁' := hsσs (hg.isOpen_target.mem_nhds hsU)
    filter_upwards [hV, hU] with k hk hk'
    have h2 : A.P (A.B.oneVal (w k)) = A.X.tgt (σs k) := (hτ.right_inv _ hk).symm
    have h1 : A.X.src (σs k) = (SEP.Hom.ϕ D.Φ).obj (xs k) := (hg.right_inv _ hk').symm
    let v : D.B.B.oneFiber (xs k) := (oneFiberObj D.isEquivalence_Φ (xs k)).symm
      (A.B.oneFiberCast h1 ((oneFiberMor A (σs k)).symm (A.B.oneFiberCast h2 (A.B.ofOne (w k)))))
    refine ⟨D.B.B.toOne v, D.B.B.proj_oneVal_toOne v, ?_⟩
    have hw2 : A.P (A.B.oneVal (w k)) = A.X.src (A.X.inv (σs k)) := h2.trans (A.X.src_inv _).symm
    have hΦv : (SEP.Hom.Φ D.Φ).obj (D.B.B.oneVal (D.B.B.toOne v)) =
        A.E.μ ⟨(A.X.inv (σs k), A.B.oneVal (w k)), hw2⟩ := by
      rw [D.B.B.oneVal_toOne, obj_oneFiberObj_symm_val, oneFiberCast_val, oneFiberMor_symm_val]
      exact A.E.μ_congr (Prod.ext rfl (A.B.oneFiberCast_val h2 (A.B.ofOne (w k))))
    have hP : A.P ((SEP.Hom.Φ D.Φ).obj (D.B.B.oneVal (D.B.B.toOne v))) = A.X.src (σs k) := by
      rw [hΦv, A.E.P_μ]; exact A.X.tgt_inv _
    refine ⟨hP, ?_⟩
    have hP' : A.P (A.E.μ ⟨(A.X.inv (σs k), A.B.oneVal (w k)), hw2⟩) = A.X.src (σs k) := by
      rw [← hΦv]; exact hP
    exact (A.E.μ_μ_inv (σs k) (A.B.oneVal (w k)) hw2 hP').symm.trans
      (A.E.μ_congr (Prod.ext rfl hΦv.symm))
  set Ψ₁ := oneRestrict D.B.B A'.B (SEP.Hom.Φ D.Ψ).obj
    (SEP.Hom.isStrongBundleFunctor D.Ψ).isStrongBundleMap_obj.mapsTo_oneSet with hΨ₁def
  have hPN : ∀ᶠ k in atTop, D.pullNorm N' (w k) = N' (Ψ₁ (e'' k)) := by
    filter_upwards [hev] with k hk
    obtain ⟨-, h, hwk⟩ := hgood k hk
    refine pullNorm_eq_Ψ hN'i (e'' k) (mk_eq_mk_of_π_eq ?_)
    change A.E.toEpGroupoid.π ((SEP.Hom.Φ D.Φ).obj (D.B.B.oneVal (e'' k))) =
      A.E.toEpGroupoid.π (A.B.oneVal (w k))
    rw [hwk, EpStrongBundle.π_μ]
  have hN'k : Tendsto (fun k => N' (Ψ₁ (e'' k))) atTop (𝓝 0) := hN.congr' hPN
  have hPΨ : Tendsto (fun k => A'.P (A'.B.oneVal (Ψ₁ (e'' k)))) atTop
      (𝓝 ((SEP.Hom.ϕ D.Ψ).obj x'')) := by
    have hfun : (fun k => A'.P (A'.B.oneVal (Ψ₁ (e'' k)))) =
        fun k => (SEP.Hom.ϕ D.Ψ).obj (xs k) := funext fun k => by
      change A'.P ((SEP.Hom.Φ D.Ψ).obj (D.B.B.oneVal (e'' k))) = _
      rw [(SEP.Hom.isStrongBundleFunctor D.Ψ).isStrongBundleMap_obj.covers, hPe]
    rw [hfun]
    exact ((SEP.Hom.ϕ D.Ψ).continuous_obj'.tendsto x'').comp hxs
  have hΨe := hN' _ _ hPΨ hN'k
  have hPe' : Tendsto (fun k => D.B.P (D.B.B.oneVal (e'' k))) atTop (𝓝 x'') := by
    simp only [hPe]; exact hxs
  have he0 := tendsto_zeroOne_of_tendsto_obj hΨ hPe' hΨe
  refine tendsto_zeroOne_μ_obj D.Φ hs he0 hσs ?_
  filter_upwards [hev] with k hk
  exact (hgood k hk).2

/-- **`[D]^*N'` is an auxiliary norm** (Definition 8.3.5) for a diagram with both legs strong bundle
equivalences. -/
theorem isAuxNorm_pullNorm (hΨ : SEP.equivalences D.Ψ) {N' : A'.B.One → ℝ}
    (hN' : A'.E.IsAuxNorm N') : A.E.IsAuxNorm (D.pullNorm N') :=
  ⟨⟨continuous_pullNorm hN'.isOneInvariant hN'.isAuxNorm.continuous,
    D.isCompleteFiberNorm_pullNorm hΨ hN'.isOneInvariant hN'.isAuxNorm.fiber,
    D.tendsto_zeroOne_pullNorm hΨ hN'.isOneInvariant hN'.isAuxNorm.tendsto_zeroOne⟩,
    isOneInvariant_iff.1 (isOneInvariant_pullNorm N')⟩

/-- **`[D]_*N` is an auxiliary norm**: the pull-back along the reversed diagram. -/
theorem isAuxNorm_pushNorm (hΨ : SEP.equivalences D.Ψ) {N : A.B.One → ℝ}
    (hN : A.E.IsAuxNorm N) : A'.E.IsAuxNorm (D.pushNorm hΨ N) :=
  (D.symm hΨ).isAuxNorm_pullNorm D.isEquivalence_Φ hN

end SDiagram

namespace GenSBMap

variable {f : GenSBMap A A'} (hf : f.IsGeneralizedIso)

theorem isAuxNorm_pullNorm {N' : A'.B.One → ℝ} (hN' : A'.E.IsAuxNorm N') :
    A.E.IsAuxNorm (pullNorm hf N') :=
  (rep hf).isAuxNorm_pullNorm (isEquivalence_rep_Ψ hf) hN'

theorem isAuxNorm_pushNorm {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N) :
    A'.E.IsAuxNorm (pushNorm hf N) :=
  (rep hf).isAuxNorm_pushNorm (isEquivalence_rep_Ψ hf) hN

/-- **2021 Proposition 11.5.1, p. 547 (2017: Proposition 11.6, p. 399)**, as stated: for a
generalized strong bundle isomorphism `[D] : W → W'`,
* the pull-back `[D]^*N'` of an auxiliary norm of `(P', μ')` is an auxiliary norm of `(P, μ)`, and
  the push-forward `[D]_*N` of one of `(P, μ)` is one of `(P', μ')` (all of Definition 8.3.5);
* `[D]^*[D]_*N = N` and `[D]_*[D]^*N' = N'`;
* both are computed by any representative `W ←Φ W'' →Ψ W'` with both legs strong bundle
  equivalences (`[D]^*N'(e) = N'(Ψ(e''))` for `Φ(e'') ≅ e`, `GenSBMap.proposition_11_5_1`);
* if `|[D]| = |[D']|`, then `[D]^*N' = [D']^*N'` and `[D]_*N = [D']_*N`. -/
theorem proposition_11_5_1_book :
    (∀ N', A'.E.IsAuxNorm N' → A.E.IsAuxNorm (pullNorm hf N')) ∧
    (∀ N, A.E.IsAuxNorm N → A'.E.IsAuxNorm (pushNorm hf N)) ∧
    (∀ N, A.E.IsAuxNorm N → pullNorm hf (pushNorm hf N) = N) ∧
    (∀ N', A'.E.IsAuxNorm N' → pushNorm hf (pullNorm hf N') = N') ∧
    (∀ (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ), D.cls = f →
      (∀ N', pullNorm hf N' = D.pullNorm N') ∧ ∀ N, pushNorm hf N = D.pushNorm hΨ N) ∧
    (∀ {g : GenSBMap A A'} (hg : g.IsGeneralizedIso), f.orbitMap = g.orbitMap →
      (∀ N', pullNorm hf N' = pullNorm hg N') ∧ ∀ N, pushNorm hf N = pushNorm hg N) := by
  obtain ⟨h1, h2, -, -, -, h6, h7, h8⟩ := proposition_11_5_1 hf
  exact ⟨fun _ hN' => isAuxNorm_pullNorm hf hN', fun _ hN => isAuxNorm_pushNorm hf hN,
    fun _ hN => h6 _ hN.isOneInvariant, fun _ hN' => h7 _ hN'.isOneInvariant,
    fun D hΨ hD => ⟨h1 D hD, h2 D hΨ hD⟩, fun hg hfg => h8 hg hfg⟩

end GenSBMap

end SBLocalization

end Polyfold
