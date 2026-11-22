import Polyfold.Chapter19.CoveringPullbackCoherence
import Polyfold.Chapter19.CoveringSquareTheorem
import Polyfold.Chapter11.StrongBundleCoveringPullback

/-!
# Strong ep-bundle covering models and uniformizers for `𝔈` (HWZ 2021 §19.8, pp. 941–954)

Witnesses for 2021 Definitions 19.8.8, 19.8.10, 19.8.13–19.8.15 and 19.8.19, pp. 942–954.

## What is formalized

* `StrongBundleOver.epBundle`: for a strong bundle uniformizer `(Ψ, Γ)` (Definition 19.6.1),
  `Q : W → O` is a strong bundle over the translation groupoid `G ⋉ O` (Definition 8.3.1) with
  `μ((g, o), w) = g ∗ w`.
* `PullbackUniformizer.coveringModel`: for a uniformizer `(Ψ, Ψ̂, Γ)` of a bundle covering
  pull-back diagram (Definition 19.8.1) and a finite-to-one covering `P`, the pull-back
  `Ŵ = τ*W → Ê` with `Ξ(ê, w) = w` is a strong ep-bundle covering model (**Definition 19.8.8**):
  `Ξ` is a proper strong bundle covering (Definition 8.5.9) covering `τ`.
* `PullbackUniformizer.toSquare`: with `Γ̂ = gammaHat` (19.55), `(Ψ, Ψ̂, Γ, Γ̂)` is a uniformizer
  for the bundle covering square `(P, μ_B ∘ P, μ_B)` of `(P, μ_B)` (**Definition 19.8.10**).
* `absSquareU β`: the uniformizer for `reflAbsSquare` (the reflection bundle pulled back along
  `absCovP`) at every `β`, and `absSquareU_nondegenerate`: over `β = 0`, the model has two sheets
  and the element `-1` of `G = ℤ/2` acts on `W` by `-1` on the fibre;
  `absSquareU_isProperSquare` (its model is a proper strong bundle covering square,
  Definition 19.8.19).
* `absSqFt` (**Definition 19.8.13**, `F̃(β) = {absSquareU β}`), `absSqFt_toPullback`
  (its underlying construction is `absFt`), `absSqTransition` (**Definition 19.8.14**),
  `absSqBasic` (**Definition 19.8.15**), `absSqBasic_definition_19_8_15`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

universe u

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

/-! ### The translation strong bundle of a strong bundle uniformizer -/

namespace StrongBundleOver

variable {B : GroupoidalCategory.{u}} {μ : B.BanFunctor} {Ψ : B.Uniformizer}
  (Γ : StrongBundleOver μ Ψ)

/-- `μ((g, o), w) = g ∗ w` on the pull-back `{((g, o), w) | Q(w) = o}`. -/
def epMu (q : pullbackSpace Γ.Q (actionEpGroupoid Ψ.smooth_smul).src) : Γ.W :=
  (q : (Ψ.G × Ψ.O) × Γ.W).1.1 • (q : (Ψ.G × Ψ.O) × Γ.W).2

theorem isStrongBundleMap_epMu :
    haveI := Γ.bundle.paracompactSpace_pullback (actionEpGroupoid Ψ.smooth_smul).PMor
      (actionEpGroupoid Ψ.smooth_smul).src
    (Γ.bundle.pullback (actionEpGroupoid Ψ.smooth_smul).isScSmoothMap_src).IsStrongBundleMap
      Γ.bundle (actionEpGroupoid Ψ.smooth_smul).tgt Γ.epMu := by
  have := Γ.bundle.paracompactSpace_pullback (actionEpGroupoid Ψ.smooth_smul).PMor
    (actionEpGroupoid Ψ.smooth_smul).src
  refine StrongBundle.isStrongBundleMap_of_locally_eqOn (fun q => ?_) fun x => ?_
  · obtain ⟨⟨⟨g, o⟩, w⟩, hq⟩ := q
    have hq' : Γ.Q w = o := hq
    change Γ.Q (g • w) = g • o
    rw [Γ.Q_smul, hq']
  · refine ⟨Prod.fst ⁻¹' {x.1}, (isOpen_discrete _).preimage continuous_fst, rfl, _, _,
      (Γ.isStrongBundleMap_smul x.1).comp (Γ.bundle.isStrongBundleMap_pullbackProj'
        (actionEpGroupoid Ψ.smooth_smul).isScSmoothMap_src), fun q hq => ?_⟩
    have hq' : (q : (Ψ.G × Ψ.O) × Γ.W).1.1 = x.1 := hq
    change (q : (Ψ.G × Ψ.O) × Γ.W).1.1 • _ = x.1 • _
    rw [hq']
    rfl

theorem isLocalScDiffeo_epMu :
    haveI := Γ.bundle.paracompactSpace_pullback (actionEpGroupoid Ψ.smooth_smul).PMor
      (actionEpGroupoid Ψ.smooth_smul).src
    (Γ.bundle.pullback
      (actionEpGroupoid Ψ.smooth_smul).isScSmoothMap_src).toMPolyfold0.IsLocalScDiffeo
      Γ.bundle.toMPolyfold0 Γ.epMu := by
  have := Γ.bundle.paracompactSpace_pullback (actionEpGroupoid Ψ.smooth_smul).PMor
    (actionEpGroupoid Ψ.smooth_smul).src
  have hπ := Γ.bundle.isLocalScDiffeo_pullbackProj'
    (actionEpGroupoid Ψ.smooth_smul).isScSmoothMap_src
    (actionEpGroupoid Ψ.smooth_smul).isLocalScDiffeo_src
  intro q
  set g := (q : (Ψ.G × Ψ.O) × Γ.W).1.1
  have hg : Γ.bundle.toMPolyfold0.IsLocalScDiffeo Γ.bundle.toMPolyfold0 (fun w => g • w) :=
    CoveringBasicConstruction.isLocalScDiffeo_of_isScDiffeoOn_univ (g := fun w => g⁻¹ • w)
      ⟨(Γ.isStrongBundleMap_smul g).isScSmoothMap, (Γ.isStrongBundleMap_smul g⁻¹).isScSmoothMap,
        mapsTo_univ _ _, mapsTo_univ _ _, fun w _ => inv_smul_smul g w,
        fun w _ => smul_inv_smul g w⟩
  have hN : IsOpen {q' : pullbackSpace Γ.Q (actionEpGroupoid Ψ.smooth_smul).src |
      (q' : (Ψ.G × Ψ.O) × Γ.W).1.1 = g} :=
    (isOpen_discrete {g}).preimage
      (continuous_fst.comp (continuous_fst.comp continuous_subtype_val))
  obtain ⟨U, V, σ, hqU, hUN, hd⟩ := (hg.comp hπ).exists_isScDiffeoOn_subset hN rfl
  refine ⟨U, V, σ, hqU, hd.congr fun q' hq' => ?_⟩
  have h' : (q' : (Ψ.G × Ψ.O) × Γ.W).1.1 = g := hUN hq'
  change g • _ = (q' : (Ψ.G × Ψ.O) × Γ.W).1.1 • _
  rw [h']
  rfl

/-- **`Q : W → O` as a strong bundle over `G ⋉ O`** (Definition 8.3.1): `μ((g, o), w) = g ∗ w`.
This is the structure `μ` of the strong ep-bundle `W` of Definition 19.8.8 for a strong bundle
uniformizer `(Ψ, Γ)` (Definition 19.6.1). -/
def epBundle : EpStrongBundle (actionEpGroupoid Ψ.smooth_smul) Γ.bundle where
  μ := Γ.epMu
  isStrongBundleMap := Γ.isStrongBundleMap_epMu
  surjective w := ⟨⟨((1, Γ.Q w), w), rfl⟩, one_smul _ w⟩
  isLocalScDiffeo := Γ.isLocalScDiffeo_epMu
  μ_unit w := one_smul _ w
  μ_comp ψ γ w _ _ := mul_smul ψ.1 γ.1 w

@[simp] theorem epBundle_μ (q : pullbackSpace Γ.Q (actionEpGroupoid Ψ.smooth_smul).src) :
    Γ.epBundle.μ q = (q : (Ψ.G × Ψ.O) × Γ.W).1.1 • (q : (Ψ.G × Ψ.O) × Γ.W).2 := rfl

end StrongBundleOver

/-! ### Definition 19.8.8: the pull-back `τ*W` -/

namespace PullbackUniformizer

variable {A B : GroupoidalCategory.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
  {μ : B.BanFunctor} {β : B.Obj} (x : PullbackUniformizer P μ β)

/-- For a finite-to-one covering `P`, `τ̂ : Ê → G ⋉ O` is a proper covering functor
(Definition 8.5.1): its fibres embed in those of `P` (`finite_fiber_τ`). -/
theorem isProperCovering_τ (hP : IsFiniteToOneCovering P) : x.Ψh.τ.IsProperCovering :=
  x.Ψh.model.isProperCovering (x.Ψh.finite_fiber_τ hP x.Ψh.model.pt)

/-- **`Ξ : τ*W → W`, `(ê, w) ↦ w`, is a proper strong bundle covering covering `τ̂`**
(Definition 8.5.9): it is a strong bundle map over `τ̂`, compatible with the structures `μ`,
surjective, and near every point the pull-back projection along the local sc-diffeomorphism
`τ̂`, a strong bundle isomorphism. -/
theorem isProperStrongBundleCovering2021_tauW (hP : IsFiniteToOneCovering P) :
    haveI := x.bun.bundle.paracompactSpace_pullback
      (actionEpGroupoid x.Ψh.Ψ.smooth_smul).PMor (actionEpGroupoid x.Ψh.Ψ.smooth_smul).src
    (x.bun.epBundle.pullbackAlong x.Ψh.τ).IsProperStrongBundleCovering2021 x.bun.epBundle x.Ψh.τ
      (pullbackProj' x.bun.Q x.Ψh.τ.obj) := by
  have := x.bun.bundle.paracompactSpace_pullback
    (actionEpGroupoid x.Ψh.Ψ.smooth_smul).PMor (actionEpGroupoid x.Ψh.Ψ.smooth_smul).src
  refine EpStrongBundle.isProperStrongBundleCovering2021_of
    (x.bun.epBundle.isMap_pullbackProj' x.Ψh.τ) (fun w => ?_) (x.isProperCovering_τ hP)
    fun y => ?_
  · obtain ⟨e, he⟩ := x.Ψh.model.surjective (x.bun.Q w)
    exact ⟨⟨(e, w), he.symm⟩, rfl⟩
  · obtain ⟨U, V, σ, hy, hd⟩ := x.Ψh.model.isLocalScDiffeo y
    exact ⟨U, V, hy, x.bun.bundle.isStrongBundleIsoOn_pullbackProj'
      x.Ψh.τ.isScSmoothMap_obj hd y⟩

/-- **2021 Definition 19.8.8, p. 943, for a uniformizer `(Ψ, Ψ̂, Γ)` of `(P, μ_B)`**: the strong
ep-bundle covering model with `W` the total space of `Γ` (`μ((g, o), w) = g ∗ w`),
`Ŵ = τ*W = {(ê, w) | τ̂(ê) = Q(w)}` over `Ê` (the pull-back strong bundle over the ep-groupoid
`Ê`, `μ̂(σ̂, (s σ̂, w)) = (t σ̂, τ(σ̂) ∗ w)`) and `Ξ(ê, w) = w`. -/
def coveringModel (hP : IsFiniteToOneCovering P) : StrongEpBundleCoveringModel x.Ψh.model where
  W := x.bun.W
  Q := x.bun.Q
  BW := x.bun.bundle
  μW := x.bun.epBundle
  Wh := x.TauW
  Qh := pullbackProj x.bun.Q x.Ψh.τ.obj
  BWh := x.bun.bundle.pullback x.Ψh.τ.isScSmoothMap_obj
  μWh := x.bun.epBundle.pullbackAlong x.Ψh.τ
  Ξ := pullbackProj' x.bun.Q x.Ψh.τ.obj
  isCovering := x.isProperStrongBundleCovering2021_tauW hP

/-! ### Definition 19.8.10: `Γ̂` -/

/-- `Â : Q̂⁻¹(ê) → (μ_B ∘ P)(Ψ̂(ê))`: the fibre of `τ*W` over `ê` is that of `W` over `τ̂(ê)`,
`A` maps it to `μ_B(Ψ(τ̂ ê)) = μ_B(P(Ψ̂ ê))`. -/
def fiberCLEh (e : x.Ψh.ObjE) :
    (pullbackProj x.bun.Q x.Ψh.τ.obj ⁻¹' {e}) ≃L[ℝ] (μ.pull P).P ⁻¹' {x.Ψh.hat.obj e} :=
  (pullbackFiberCLE e).trans ((x.bun.fiberCLE (x.Ψh.τ.obj e)).trans
    ((μ.fiberCast (x.Ψh.obj_comm e).symm).trans (μ.pullFiberCLE P (x.Ψh.hat.obj e)).symm))

theorem fiberCLEh_apply (e : x.Ψh.ObjE) (v : pullbackProj x.bun.Q x.Ψh.τ.obj ⁻¹' {e}) :
    (x.fiberCLEh e v : (μ.pull P).E) = x.gammaHat.obj v := by
  obtain ⟨⟨⟨e', w⟩, hw⟩, he⟩ := v
  obtain rfl : e' = e := he
  apply BanFunctor.pullPt_injective
  refine Prod.ext rfl ?_
  change ((μ.fiberCast _ (x.bun.fiberCLE _ _)) : μ.E) = x.bun.functor.obj w
  rw [BanFunctor.fiberCast_apply, x.bun.fiberCLE_apply]
  rfl

/-- **2021 Definition 19.8.10, p. 943, for a uniformizer `(Ψ, Ψ̂, Γ)` of `(P, μ_B)`**: with the
strong ep-bundle covering model `coveringModel` and `Γ̂ = gammaHat` (19.55),
`Γ̂(ê, w) = (Ψ̂(ê), Γ(w))`, `(Ψ, Ψ̂, Γ, Γ̂)` is a uniformizer for the bundle covering square
`(P, μ_B ∘ P, μ_B)` of `(P, μ_B)` (Definition 19.8.7, `BundleCoveringSquare.ofPull`). -/
def toSquare (hP : IsFiniteToOneCovering P) :
    SquareUniformizer (BundleCoveringSquare.ofPull P hP μ) β where
  Ψh := x.Ψh
  K := x.coveringModel hP
  Γ := x.bun.functor
  injective_Γ := x.bun.injective_obj
  full_Γ := x.bun.full
  faithful_Γ := x.bun.faithful
  P_obj := x.bun.P_obj
  mor_fst := x.bun.mor_fst
  fiberCLE := x.bun.fiberCLE
  fiberCLE_apply := x.bun.fiberCLE_apply
  Γh := x.gammaHat
  injective_Γh := x.injective_gammaHat
  full_Γh := x.full_gammaHat
  faithful_Γh := x.faithful_gammaHat
  PA_obj _ := rfl
  PA_mor _ := rfl
  fiberCLEh := x.fiberCLEh
  fiberCLEh_apply := x.fiberCLEh_apply
  comm_obj _ := rfl

@[simp] theorem toSquare_toPullbackUniformizer (hP : IsFiniteToOneCovering P) :
    (x.toSquare hP).toPullbackUniformizer = x := rfl

end PullbackUniformizer

/-! ### The reflection bundle pulled back along `absCovP` -/

open GCT.PolyfoldConstruction TrivialBundle Chapter19

/-- **2021 Definition 19.8.10, p. 943, for `reflAbsSquare`**: the uniformizer
`(Ψ, Ψ̂, Γ, Γ̂)` at `β` of the bundle covering square of `(absCovP, reflBan)` built from the member
`absPU β` of `F̃(β)` (Definition 19.8.2); its strong ep-bundle covering model (Definition 19.8.8)
is `τ*W_V → H ⋉ (ℤˣ × V)` over the sheet model. -/
def absSquareU (β : Fin 1 → ℝ) : SquareUniformizer reflAbsSquare β :=
  (absPU β).toSquare absCovP_isFiniteToOneCovering

theorem absSquareU_toPullbackUniformizer (β : Fin 1 → ℝ) :
    (absSquareU β).toPullbackUniformizer = absPU β := rfl

theorem absSquareU_zero : absSquareU 0 =
    (slicePU overlapSlice₀ 0 (mem_univ _) zero_fix).toSquare absCovP_isFiniteToOneCovering := by
  rw [absSquareU, absPU_zero]

/-- **The model over `β = 0` is non-degenerate**: `Ξ : Ŵ → W` is two-to-one (the two sheets
`{±1} × ℝ` of `Ê`), and `-1 ∈ G = ℤ/2` acts on `W` by `(v, a) ↦ (-v, -a)`, non-trivially on the
fibre over `0`. -/
theorem absSquareU_nondegenerate :
    ¬ Injective (absSquareU 0).K.Ξ ∧
      ∃ (g : (absSquareU 0).Ψh.Ψ.G) (w : (absSquareU 0).K.W), g • w ≠ w := by
  rw [absSquareU_zero]
  refine ⟨fun h => ?_, ⟨-1, Subgroup.mem_top _⟩,
    (show SliceW overlapSlice₀ from ⟨(⟨0, mem_univ _⟩, (0, fun _ => 1)), rfl⟩), fun h => ?_⟩
  · let w₀ : SliceW overlapSlice₀ := ⟨(⟨0, mem_univ _⟩, (0, 0)), rfl⟩
    have h1 := @h ⟨((1, ⟨0, mem_univ _⟩), w₀), rfl⟩ ⟨((-1, ⟨0, mem_univ _⟩), w₀), rfl⟩ rfl
    have h2 := congrArg (fun y : (slicePU overlapSlice₀ 0 (mem_univ _) zero_fix).TauW =>
      (y.1.1.1 : ℤˣ)) h1
    exact absurd h2 (by decide)
  · have h2 := congrArg (fun w : SliceW overlapSlice₀ => (w.1.2.2 : Fin 1 → ℝ) 0) h
    change ((-1 : ℤˣ) • (fun _ => (1 : ℝ) : Fin 1 → ℝ)) 0 = 1 at h2
    rw [units_smul_rn_neg_one] at h2
    norm_num at h2


/-- **2021 Definition 19.8.19, p. 954, for the model of `absSquareU 0`**: `Ξ : Ŵ → W` over
`τ̂ : Ê → O` is a proper strong bundle covering square; it is two-to-one
(`absSquareU_nondegenerate`). -/
theorem absSquareU_isProperSquare :
    IsProperStrongBundleCoveringSquare (absSquareU 0).K.BWh (absSquareU 0).K.BW
      (absSquareU 0).Ψh.τ.obj (absSquareU 0).K.Ξ :=
  (absSquareU 0).K.isProperSquare

/-! ### Definitions 19.8.13–19.8.15 for `reflAbsSquare` -/

/-- **2021 Definition 19.8.13, p. 948, for `reflAbsSquare`**: `F̃(β) = {absSquareU β}`. -/
def absSqFt : SquareUniformizerConstruction reflAbsSquare := ⟨fun β => {absSquareU β}⟩

/-- The underlying uniformizer construction of `absSqFt` is `absFt` (Definition 19.8.2). -/
theorem absSqFt_toPullback : absSqFt.toPullback = absFt := by
  change (⟨fun β => (fun x : SquareUniformizer reflAbsSquare β => x.toPullbackUniformizer) ''
    {absSquareU β}⟩ : PullbackUniformizerConstruction absCovP reflBan) = ⟨fun β => {absPU β}⟩
  congr 1
  funext β
  exact Set.image_singleton

/-- **2021 Definition 19.8.14, p. 948, for `reflAbsSquare`**: the compatible transition
construction of `absSqFt`, transported from `absFtTransition` (Definition 19.8.4, coherent). -/
def absSqTransition : absSqFt.CompatibleTransitionConstruction :=
  show absSqFt.toPullback.PullbackTransitionConstruction from
    absSqFt_toPullback.symm ▸ absFtTransition

/-- **2021 Definition 19.8.15, p. 948, for `reflAbsSquare`**: the basic construction
`(F̃, 𝓕)`. -/
def absSqBasic : SquareBasicConstruction reflAbsSquare := ⟨absSqFt, absSqTransition⟩

/-- The square basic construction `absSqBasic` satisfies the conclusions of Definition 19.8.15,
with the non-degenerate model of `absSquareU_nondegenerate` in `F̃(0)`. -/
theorem absSqBasic_definition_19_8_15 :
    (absSqBasic.toPullbackBasic.Ft = absSqBasic.Ft.toPullback ∧
      absSqBasic.Ft.toPullback.IsCoherent absSqBasic.T.𝓕) ∧ absSquareU 0 ∈ absSqBasic.Ft.F 0 :=
  ⟨definition_19_8_15 absSqBasic, rfl⟩

end GroupoidalCategory

end Polyfold
