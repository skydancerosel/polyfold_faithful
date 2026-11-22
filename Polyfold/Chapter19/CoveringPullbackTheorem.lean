import Polyfold.Chapter19.CoveringPullbackDiagram
import Polyfold.Chapter19.CoveringPolyfold
import Polyfold.Chapter19.StrongBundleTransport
import Polyfold.Chapter10.StrongBundleEquivalence

/-!
# Basic constructions for bundle covering pull-backs (HWZ 2021 §19.8, pp. 934–939)

2021 Definition 19.8.4 (transition construction for a uniformizer construction `F̃` of
`(P, μ_B)`), Definition 19.8.5 (basic construction for `(P, μ_B)`) and Theorem 19.8.6 (the
transition sets `M(Γ̂, Γ̂')`, the map `U : M(Γ̂, Γ̂') → p*M(Γ, Γ')` and `p̄`), pp. 934–939.

For uniformizers `(Ψ, Ψ̂, Γ)`, `(Ψ', Ψ̂', Γ')` in `F̃`:

* `M(Ψ, Ψ')` carries the natural M-polyfold structure of Theorem 19.5.1 (`basePolyfold`) and
  `M(Ψ̂, Ψ̂')` the structure of Proposition 19.7.26 (`hatPolyfold`), for which
  `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is a surjective local sc-diffeomorphism;
* `m : M(Γ, Γ') → M(Ψ, Ψ')` carries the strong bundle structure of §19.6 for which
  `H : M(Ψ, Ψ') ₛ×_Q W → M(Γ, Γ')`, `((e, φ, e'), w) ↦ (w, (φ, Γ(w)), Γ'⁻¹(μ_B(φ)(Γ(w))))`,
  is a strong bundle isomorphism (p. 901, (19.16));
* `U : M(Γ̂, Γ̂') → p*M(Γ, Γ')` (19.58), with `p*M(Γ, Γ')` the pull-back strong bundle of
  Proposition 2.6.8 (`StrongBundle.pullback`), is a bijection over `M(Ψ̂, Ψ̂')` (19.59), linear on
  the fibres, and `m̂` carries a unique strong bundle structure for which `U` is a strong bundle
  isomorphism;
* `p̄ : M(Γ̂, Γ̂') → M(Γ, Γ')` (19.60) is a surjective local strong bundle isomorphism covering
  `p`.

## What is formalized

* `PullbackTransitionConstruction`, `definition_19_8_4` (**Definition 19.8.4**), with
  `toCoveringBasicConstruction`; the note "(1) implies (3)" is part of `definition_19_8_4`.
* `PullbackBasicConstruction`, `definition_19_8_5` (**Definition 19.8.5**).
* `SrcPB`, `srcBundle`, `TgtPB`, `tgtBundle`, `altH`, `altHinv`, `altH'`, `altC`, `IsCoherent`:
  the fibred products (19.14), the maps `H`, `H'` of (19.16) and coherence (Definition 19.6.15)
  for the strong bundle uniformizers `(Ψ, Γ)` of `F̃`.
* `MG`, `mGmap`, `bundleG`: `m : M(Γ, Γ') → M(Ψ, Ψ')` with its strong bundle structure;
  `isStrongBundleIso_altH` (Theorem 19.6.13 for this structure).
* `MGHat`, `mHatMap`, `pbarMap`, `Umap`, `Uinv`: the transition set `M(Γ̂, Γ̂')`, the maps `m̂`
  (19.57), `p̄` (19.60) and `U` (19.58) with its inverse; `pullBundle` (`p*M(Γ, Γ')`, (19.53)),
  `bundleHat` (the strong bundle structure of `m̂`), `isStrongBundleIso_U`, `bundleHat_unique`,
  `mGmap_pbarMap`, `isStrongBundleMap_pbar`, `isLocalStrongBundleIso_pbar`, `surjective_pbar`.
* `theorem_19_8_6_hyp` (**Theorem 19.8.6**, (1)–(4) and the orbit space part of (5) for `|A|` and
  `|B|`) and `theorem_19_8_6_one_four` (the functor `Γ̂` and (1)–(4) for any transition
  construction `𝓕` of `F`).

## Readings

* Definition 19.8.4 (1): "defines a metrizable natural topology" is read as: every isomorphism
  class of `B` contains an object with a uniformizer (`HasClassUniformizers`, needed to define
  `T_{|B|}` in Definition 19.2.1) and `T_{|B|}` is metrizable.
* Definition 19.8.4 (2): we read the coherence of Definition 19.6.15 for the pairs `(Ψ, Γ)` of
  `F̃` (in the §19.6 formalization the structure (1) of Definition 19.6.1 is a function of the
  functor `Ψ̄`; here it is part of the member `(Ψ, Ψ̂, Γ)` of `F̃`): for all members the map
  `C = H'⁻¹ ∘ H : M(Ψ, Ψ') ₛ×_Q W → M(Ψ, Ψ') ₜ×_{Q'} W'` is a strong bundle isomorphism covering
  the identity.
* "`m : M(Γ, Γ') → M(Ψ, Ψ')` has a natural strong bundle structure" (Theorem 19.8.6 (1)) is read
  as the structure of Theorem 19.6.13: the one for which `H` is a strong bundle isomorphism over
  the natural M-polyfold `M(Ψ, Ψ')` (`bundleG`, transported from the pull-back `s*W`); the
  topology of `M(Γ, Γ')` is the one making `H` a homeomorphism, and the linear structure of the
  fibres is the one making `H` fibrewise linear.
* The linear structure of the fibres of `m̂` and the topology of `M(Γ̂, Γ̂')` are the ones making
  `U` fibrewise linear and a homeomorphism (the book: "`U` is a fiber-wise linear isomorphism");
  with them `p̄` is linear on the fibres (it is a strong bundle map), so the fibre of `m̂` over
  `(ê, φ̂, ê')` is linearly identified with `W_{τ(ê)}` through `p̄` and `H`.
* `P : A → B` is a finite-to-one covering functor (Definition 19.8.1): we pass it as
  `[Fact (IsFiniteToOneCovering P)]`; the M-polyfold `M(Ψ̂, Ψ̂')` (Proposition 19.7.26) is
  Hausdorff and paracompact under it.
* Theorem 19.8.6 (5), the orbit spaces of `E_B` and `P*E_B`: the natural topologies on these are
  those of basic constructions for `E_B` and `P*E_B`, which Definition 19.8.4 does not provide
  here; `theorem_19_8_6_hyp` states (5) for `|A|` and `|B|`, under `IsCompatible`, the added
  hypothesis of l. 44572 (hence the suffix).  The metrizability of `|E_B|` and `|E_A|` for the
  natural topologies of §19.8 is in `CoveringSquareTopology.lean` (`metrizableSpace_natTopEB`,
  `metrizableSpace_natTopEA`, Lemma 19.8.21).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace Polyfold

noncomputable section

universe u

open Set Function Topology TopologicalSpace

/-! ### Transferring the fibre structures along an equivalence over the base -/

section Transfer

variable {X : Type*} {Y : Type*} {Pr : Y → X} {Y' : Type*} {Pr' : Y' → X}

/-- **The fibre equivalence** `Pr'⁻¹(x) ≃ Pr⁻¹(x)` of an equivalence `e : Y' ≃ Y` over `X`. -/
def fiberEquivOver (e : Y' ≃ Y) (he : ∀ y, Pr (e y) = Pr' y) (x : X) :
    Pr' ⁻¹' {x} ≃ Pr ⁻¹' {x} where
  toFun v := ⟨e v, show Pr (e v) = x from (he v).trans v.2⟩
  invFun v := ⟨e.symm v, show Pr' (e.symm v) = x by
    rw [← he (e.symm v), e.apply_symm_apply]; exact v.2⟩
  left_inv v := Subtype.ext (e.symm_apply_apply _)
  right_inv v := Subtype.ext (e.apply_symm_apply _)

@[simp] theorem fiberEquivOver_apply (e : Y' ≃ Y) (he : ∀ y, Pr (e y) = Pr' y) (x : X)
    (v : Pr' ⁻¹' {x}) : (fiberEquivOver e he x v : Y) = e v := rfl

@[simp] theorem fiberEquivOver_symm_apply (e : Y' ≃ Y) (he : ∀ y, Pr (e y) = Pr' y) (x : X)
    (v : Pr ⁻¹' {x}) : ((fiberEquivOver e he x).symm v : Y') = e.symm v := rfl

end Transfer

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

variable {A B : GroupoidalCategory.{u}}

/-! ### Hausdorff and paracompact `M(Ψ̂, Ψ̂')` for a finite-to-one covering -/

namespace CoveringBasicConstruction

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}

instance instT2SpaceMHatFact [hP : Fact (IsFiniteToOneCovering P)]
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) : T2Space (Bh.MHat x y) :=
  Bh.t2Space_MHat hP.out x y

instance instParacompactSpaceMHatFact [hP : Fact (IsFiniteToOneCovering P)]
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) : ParacompactSpace (Bh.MHat x y) :=
  Bh.paracompactSpace_MHat hP.out x y

end CoveringBasicConstruction

namespace PullbackUniformizerConstruction

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} {μ : B.BanFunctor}
  (Ft : PullbackUniformizerConstruction P μ)

/-- **The covering basic construction `(F̂, 𝓕)`** for `P` of a transition construction `𝓕` of the
underlying `F` (Definition 19.8.4 (3)). -/
abbrev toCBC (𝓕 : Ft.toUniformizerConstruction.TransitionConstruction) :
    CoveringBasicConstruction P :=
  ⟨Ft.hatU, 𝓕⟩

section Pair

variable (𝓕 : Ft.toUniformizerConstruction.TransitionConstruction) (x y : Ft.Unif)

/-- `M(Ψ, Ψ')` with its natural topology. -/
abbrev MBase : Type u := (Ft.toCBC 𝓕).MB x.toHat y.toHat

/-- `M(Ψ, Ψ')` with its natural M-polyfold structure (Theorem 19.5.1). -/
abbrev basePoly : MPolyfold (Ft.MBase 𝓕 x y) := (Ft.toCBC 𝓕).basePolyfold x.toHat y.toHat

/-- The source map `s : M(Ψ, Ψ') → O`. -/
abbrev srcB (k : Ft.MBase 𝓕 x y) : x.x.Ψh.Ψ.O := (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).src

/-- The target map `t : M(Ψ, Ψ') → O'`. -/
abbrev tgtB (k : Ft.MBase 𝓕 x y) : y.x.Ψh.Ψ.O := (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).tgt

theorem isScSmoothMap_srcB : (Ft.basePoly 𝓕 x y).IsScSmoothMap x.x.Ψh.Ψ.P (Ft.srcB 𝓕 x y) :=
  ((Ft.toCBC 𝓕).isLocalScDiffeo_srcB' x.toHat y.toHat).isScSmoothMap

theorem isScSmoothMap_tgtB : (Ft.basePoly 𝓕 x y).IsScSmoothMap y.x.Ψh.Ψ.P (Ft.tgtB 𝓕 x y) :=
  ((Ft.toCBC 𝓕).toBasic.rep.isLocalScDiffeo_tgt x.toHat.toUnif y.toHat.toUnif).isScSmoothMap

/-- **2021 (19.14): the fibred product `M(Ψ, Ψ') ₛ×_Q W`**. -/
abbrev SrcPB : Set (Ft.MBase 𝓕 x y × x.x.bun.W) := pullbackSpace x.x.bun.Q (Ft.srcB 𝓕 x y)

/-- **2021 (19.14): the fibred product `M(Ψ, Ψ') ₜ×_{Q'} W'`**. -/
abbrev TgtPB : Set (Ft.MBase 𝓕 x y × y.x.bun.W) := pullbackSpace y.x.bun.Q (Ft.tgtB 𝓕 x y)

instance instParacompactSpaceSrcPB : ParacompactSpace (Ft.SrcPB 𝓕 x y) :=
  paracompactSpace_pullbackSpace (Ft.basePoly 𝓕 x y) x.x.bun.bundle

instance instParacompactSpaceTgtPB : ParacompactSpace (Ft.TgtPB 𝓕 x y) :=
  paracompactSpace_pullbackSpace (Ft.basePoly 𝓕 x y) y.x.bun.bundle

/-- **The strong bundle `M(Ψ, Ψ') ₛ×_Q W → M(Ψ, Ψ')`** (Proposition 2.6.8). -/
def srcBundle : StrongBundle (Ft.basePoly 𝓕 x y) (pullbackProj x.x.bun.Q (Ft.srcB 𝓕 x y)) :=
  x.x.bun.bundle.pullback (Ft.isScSmoothMap_srcB 𝓕 x y)

/-- **The strong bundle `M(Ψ, Ψ') ₜ×_{Q'} W' → M(Ψ, Ψ')`** (Proposition 2.6.8). -/
def tgtBundle : StrongBundle (Ft.basePoly 𝓕 x y) (pullbackProj y.x.bun.Q (Ft.tgtB 𝓕 x y)) :=
  y.x.bun.bundle.pullback (Ft.isScSmoothMap_tgtB 𝓕 x y)

/-- **2021 (19.16): `H((e, φ, e'), w) = (w, (φ, Γ(w)), Γ'⁻¹(μ_B(φ)(Γ(w))))`.** -/
def altH (z : Ft.SrcPB 𝓕 x y) : x.x.TransG y.x :=
  x.x.str.lift y.x.str (z : Ft.MBase 𝓕 x y × x.x.bun.W).1 (z : Ft.MBase 𝓕 x y × x.x.bun.W).2 z.2

/-- `H⁻¹(h) = (m(h), s(h))`. -/
def altHinv (h : x.x.TransG y.x) : Ft.SrcPB 𝓕 x y :=
  ⟨(x.x.mG y.x h, h.src), rfl⟩

/-- **2021 (19.16): `H'((e, φ, e'), w') = (Γ⁻¹(μ_B(φ⁻¹)(Γ'(w'))), (φ, …), w')`.** -/
def altH' (z : Ft.TgtPB 𝓕 x y) : x.x.TransG y.x :=
  (y.x.str.lift x.x.str ((z : Ft.MBase 𝓕 x y × y.x.bun.W).1 :
    x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).inv (z : Ft.MBase 𝓕 x y × y.x.bun.W).2 z.2).inv

/-- `H'⁻¹(h) = (m(h), t(h))`. -/
def altH'inv (h : x.x.TransG y.x) : Ft.TgtPB 𝓕 x y :=
  ⟨(x.x.mG y.x h, h.tgt), rfl⟩

theorem altHinv_altH (z : Ft.SrcPB 𝓕 x y) : Ft.altHinv 𝓕 x y (Ft.altH 𝓕 x y z) = z :=
  Subtype.ext (Prod.ext (x.x.str.proj_lift y.x.str _ _ _) rfl)

theorem altH_altHinv (h : x.x.TransG y.x) : Ft.altH 𝓕 x y (Ft.altHinv 𝓕 x y h) = h :=
  x.x.str.lift_proj y.x.str h

theorem altH'inv_altH' (z : Ft.TgtPB 𝓕 x y) : Ft.altH'inv 𝓕 x y (Ft.altH' 𝓕 x y z) = z :=
  Subtype.ext (Prod.ext ((congrArg TransitionSet.inv (y.x.str.proj_lift x.x.str _ _ _)).trans
    (TransitionSet.inv_inv _)) rfl)

theorem altH'_altH'inv (h : x.x.TransG y.x) : Ft.altH' 𝓕 x y (Ft.altH'inv 𝓕 x y h) = h := by
  have e : y.x.str.lift x.x.str (x.x.str.proj y.x.str h).inv h.tgt rfl = h.inv :=
    ((y.x.str.eq_lift_iff x.x.str (h := h.inv) rfl).2 ⟨rfl, rfl⟩).symm
  exact (congrArg TransitionSet.inv e).trans (TransitionSet.inv_inv _)

/-- **`C = H'⁻¹ ∘ H : M(Ψ, Ψ') ₛ×_Q W → M(Ψ, Ψ') ₜ×_{Q'} W'`** (Definition 19.6.15). -/
def altC (z : Ft.SrcPB 𝓕 x y) : Ft.TgtPB 𝓕 x y := Ft.altH'inv 𝓕 x y (Ft.altH 𝓕 x y z)

end Pair

/-- **2021 Definition 19.6.15, p. 902, for the pairs `(Ψ, Γ)` of `F̃`: coherence**: for all
members of `F̃` the map `C = H'⁻¹ ∘ H` is a strong bundle isomorphism covering the identity of
`M(Ψ, Ψ')`. -/
def IsCoherent (𝓕 : Ft.toUniformizerConstruction.TransitionConstruction) : Prop :=
  ∀ x y : Ft.Unif, ∃ h : (Ft.srcBundle 𝓕 x y).IsStrongBundleMap (Ft.tgtBundle 𝓕 x y) id
      (Ft.altC 𝓕 x y), (Ft.srcBundle 𝓕 x y).IsStrongBundleIsoOn (Ft.tgtBundle 𝓕 x y) h univ univ

/-! ### Definitions 19.8.4 and 19.8.5 -/

/-- **2021 Definition 19.8.4, p. 934 (transition construction for `F̃`)**: a transition
construction `𝓕` for the underlying `F` such that (1) `(F, 𝓕)` defines a metrizable natural
topology `T_{|B|}` and (2) the associated basic construction `(F̄, 𝓕)` for `P_B` is coherent.
((3), that `(F̂, 𝓕)` is a basic construction for `P`, holds by construction:
`toCoveringBasicConstruction`.) -/
structure PullbackTransitionConstruction : Type (u + 1) where
  /-- The transition construction `𝓕` for `F`. -/
  𝓕 : Ft.toUniformizerConstruction.TransitionConstruction
  /-- (1) Every isomorphism class of `B` contains an object with a uniformizer. -/
  hasClassUniformizers : (Ft.toCBC 𝓕).HasClassUniformizers
  /-- (1) `T_{|B|}` is metrizable. -/
  metrizable : @MetrizableSpace B.OrbitSpace
    ((Ft.toCBC 𝓕).toBasic.natTop hasClassUniformizers.toBasic)
  /-- (2) Coherence of `(F̄, 𝓕)`. -/
  isCoherent : Ft.IsCoherent 𝓕

variable {Ft}

/-- **(3) The underlying basic construction `(F̂, 𝓕)` for `P`** (Definition 19.7.11). -/
abbrev PullbackTransitionConstruction.toCoveringBasicConstruction
    (T : Ft.PullbackTransitionConstruction) : CoveringBasicConstruction P :=
  Ft.toCBC T.𝓕

/-- **2021 Definition 19.8.4, p. 934**, and the note "(1) implies (3)": the underlying covering
basic construction has uniformizer construction `F̂` and transition construction `𝓕`, its basic
construction for `B` is `(F, 𝓕)` and it has class uniformizers with metrizable `T_{|B|}`. -/
theorem definition_19_8_4 (T : Ft.PullbackTransitionConstruction) :
    T.toCoveringBasicConstruction.hatU = Ft.hatU ∧
      T.toCoveringBasicConstruction.toBasic = ⟨Ft.toUniformizerConstruction, T.𝓕⟩ ∧
      T.toCoveringBasicConstruction.HasClassUniformizers ∧ Ft.IsCoherent T.𝓕 :=
  ⟨rfl, rfl, T.hasClassUniformizers, T.isCoherent⟩

variable (P μ) in
/-- **2021 Definition 19.8.5, p. 937 (basic construction for `(P, μ_B)`)**: a uniformizer
construction `F̃` for `(P, μ_B)` with a transition construction for it. -/
structure PullbackBasicConstruction : Type (u + 1) where
  /-- The uniformizer construction `F̃`. -/
  Ft : PullbackUniformizerConstruction P μ
  /-- The transition construction. -/
  T : Ft.PullbackTransitionConstruction

/-- **2021 Definition 19.8.5, p. 937.** -/
theorem definition_19_8_5 (Bt : PullbackBasicConstruction P μ) :
    Bt.T.toCoveringBasicConstruction.hatU = Bt.Ft.hatU ∧ Bt.Ft.IsCoherent Bt.T.𝓕 :=
  ⟨rfl, Bt.T.isCoherent⟩

/-! ### The strong bundle `m : M(Γ, Γ') → M(Ψ, Ψ')` (Theorem 19.8.6 (1)) -/

section BundleG

variable (Ft) (𝓕 : Ft.toUniformizerConstruction.TransitionConstruction) (x y : Ft.Unif)

/-- **`M(Γ, Γ')`** (19.47), to be topologized by `H`. -/
def MG (_𝓕 : Ft.toUniformizerConstruction.TransitionConstruction) (x y : Ft.Unif) : Type u :=
  x.x.TransG y.x

/-- **`m : M(Γ, Γ') → M(Ψ, Ψ')`** (19.49), into the topological `M(Ψ, Ψ')`. -/
def mGmap (h : Ft.MG 𝓕 x y) : Ft.MBase 𝓕 x y := x.x.mG y.x h

/-- `H` as an equivalence `M(Ψ, Ψ') ₛ×_Q W ≃ M(Γ, Γ')`. -/
def altHEquiv : Ft.SrcPB 𝓕 x y ≃ Ft.MG 𝓕 x y where
  toFun := Ft.altH 𝓕 x y
  invFun := Ft.altHinv 𝓕 x y
  left_inv := Ft.altHinv_altH 𝓕 x y
  right_inv := Ft.altH_altHinv 𝓕 x y

/-- **The topology of `M(Γ, Γ')`**: the one making `H` a homeomorphism. -/
instance instTopologicalSpaceMG : TopologicalSpace (Ft.MG 𝓕 x y) :=
  TopologicalSpace.induced (Ft.altHinv 𝓕 x y) inferInstance

/-- **`H : M(Ψ, Ψ') ₛ×_Q W → M(Γ, Γ')` as a homeomorphism.** -/
def altHHomeo : Ft.SrcPB 𝓕 x y ≃ₜ Ft.MG 𝓕 x y where
  toEquiv := Ft.altHEquiv 𝓕 x y
  continuous_toFun := continuous_induced_rng.2 (by
    have : Ft.altHinv 𝓕 x y ∘ Ft.altH 𝓕 x y = id := funext (Ft.altHinv_altH 𝓕 x y)
    change Continuous (Ft.altHinv 𝓕 x y ∘ Ft.altH 𝓕 x y)
    rw [this]; exact continuous_id)
  continuous_invFun := continuous_induced_dom

instance instT2SpaceMG : T2Space (Ft.MG 𝓕 x y) := (Ft.altHHomeo 𝓕 x y).symm.isEmbedding.t2Space

instance instParacompactSpaceMG : ParacompactSpace (Ft.MG 𝓕 x y) :=
  (Ft.altHHomeo 𝓕 x y).symm.isClosedEmbedding.paracompactSpace

/-- The fibres of `m` are those of `M(Ψ, Ψ') ₛ×_Q W` (via `H⁻¹`). -/
def fiberGEquiv (k : Ft.MBase 𝓕 x y) :
    Ft.mGmap 𝓕 x y ⁻¹' {k} ≃ pullbackProj x.x.bun.Q (Ft.srcB 𝓕 x y) ⁻¹' {k} :=
  fiberEquivOver (Pr := pullbackProj x.x.bun.Q (Ft.srcB 𝓕 x y)) (Pr' := Ft.mGmap 𝓕 x y)
    (Ft.altHEquiv 𝓕 x y).symm (fun _ => rfl) k

instance instAddCommGroupFiberG (k : Ft.MBase 𝓕 x y) : AddCommGroup (Ft.mGmap 𝓕 x y ⁻¹' {k}) :=
  (Ft.fiberGEquiv 𝓕 x y k).addCommGroup

instance instModuleFiberG (k : Ft.MBase 𝓕 x y) : Module ℝ (Ft.mGmap 𝓕 x y ⁻¹' {k}) :=
  (Ft.fiberGEquiv 𝓕 x y k).module ℝ

/-- `H` on the fibres, a linear isomorphism. -/
def fiberGLin (k : Ft.MBase 𝓕 x y) :
    pullbackProj x.x.bun.Q (Ft.srcB 𝓕 x y) ⁻¹' {k} ≃ₗ[ℝ] Ft.mGmap 𝓕 x y ⁻¹' {k} :=
  (Equiv.linearEquiv ℝ (Ft.fiberGEquiv 𝓕 x y k)).symm

theorem fiberGLin_apply (k : Ft.MBase 𝓕 x y) (v : pullbackProj x.x.bun.Q (Ft.srcB 𝓕 x y) ⁻¹' {k}) :
    (Ft.fiberGLin 𝓕 x y k v : Ft.MG 𝓕 x y) = Ft.altHHomeo 𝓕 x y v := rfl

/-- **The natural strong bundle structure of `m : M(Γ, Γ') → M(Ψ, Ψ')`** (Theorem 19.8.6 (1),
Theorem 19.6.13): transported from `M(Ψ, Ψ') ₛ×_Q W` along `H`. -/
def bundleG : StrongBundle (Ft.basePoly 𝓕 x y) (Ft.mGmap 𝓕 x y) :=
  (Ft.srcBundle 𝓕 x y).transport (Ft.altHHomeo 𝓕 x y) (Ft.fiberGLin 𝓕 x y)
    (Ft.fiberGLin_apply 𝓕 x y)

/-- **`H` is a strong bundle isomorphism covering the identity of `M(Ψ, Ψ')`.** -/
theorem isStrongBundleIso_altH :
    (Ft.srcBundle 𝓕 x y).IsStrongBundleIso (Ft.bundleG 𝓕 x y) id (Ft.altHHomeo 𝓕 x y) id
      (Ft.altHHomeo 𝓕 x y).symm :=
  StrongBundle.isStrongBundleIso_transport _

end BundleG

/-! ### `M(Γ̂, Γ̂')`, `U` and `p̄` (Theorem 19.8.6 (3), (4)) -/

section Hat

variable (Ft) (𝓕 : Ft.toUniformizerConstruction.TransitionConstruction) (x y : Ft.Unif)
  [Fact (IsFiniteToOneCovering P)]

/-- `M(Ψ̂, Ψ̂')` with its topology (Proposition 19.7.13). -/
abbrev MHatB : Type u := (Ft.toCBC 𝓕).MHat x.toHat y.toHat

/-- **`M(Ψ̂, Ψ̂')` with its M-polyfold structure** (Proposition 19.7.26). -/
abbrev hatPoly : MPolyfold (Ft.MHatB 𝓕 x y) := (Ft.toCBC 𝓕).hatPolyfold Fact.out x.toHat y.toHat

/-- **`p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')`** (19.50). -/
abbrev pBmap : Ft.MHatB 𝓕 x y → Ft.MBase 𝓕 x y := (Ft.toCBC 𝓕).pB x.toHat y.toHat

theorem isLocalScDiffeo_pBmap :
    (Ft.hatPoly 𝓕 x y).IsLocalScDiffeo (Ft.basePoly 𝓕 x y) (Ft.pBmap 𝓕 x y) :=
  (Ft.toCBC 𝓕).isLocalScDiffeo_pB Fact.out x.toHat y.toHat

theorem surjective_pBmap : Surjective (Ft.pBmap 𝓕 x y) :=
  ((Ft.toCBC 𝓕).proposition_19_7_14 Fact.out x.toHat y.toHat).2

/-- **The pull-back `p*M(Γ, Γ')`** (19.53). -/
abbrev PB : Set (Ft.MHatB 𝓕 x y × Ft.MG 𝓕 x y) := pullbackSpace (Ft.mGmap 𝓕 x y) (Ft.pBmap 𝓕 x y)

instance instParacompactSpacePB : ParacompactSpace (Ft.PB 𝓕 x y) :=
  paracompactSpace_pullbackSpace (Ft.hatPoly 𝓕 x y) (Ft.bundleG 𝓕 x y)

/-- **The strong bundle `p*m : p*M(Γ, Γ') → M(Ψ̂, Ψ̂')`** (Definition 2.6.7, Proposition 2.6.8). -/
def pullBundle : StrongBundle (Ft.hatPoly 𝓕 x y) (pullbackProj (Ft.mGmap 𝓕 x y) (Ft.pBmap 𝓕 x y)) :=
  (Ft.bundleG 𝓕 x y).pullback (Ft.isLocalScDiffeo_pBmap 𝓕 x y).isScSmoothMap

/-- **The transition set `M(Γ̂, Γ̂')`** of the functors `Γ̂ : τ*W → P*E_B`,
`Γ̂' : τ'*W' → P*E_B`: the triples `((ê, w), (φ̂, Γ̂(ê, w)), (ê', w'))`. -/
def MGHat (_𝓕 : Ft.toUniformizerConstruction.TransitionConstruction) (x y : Ft.Unif) : Type u :=
  (μ.pull P).cat.toGroupoidStr.TransitionSet x.x.gammaHat.obj y.x.gammaHat.obj

variable {Ft 𝓕 x y}

/-- The underlying element of the transition set. -/
abbrev MGHat.toTrans (h : Ft.MGHat 𝓕 x y) :
    (μ.pull P).cat.toGroupoidStr.TransitionSet x.x.gammaHat.obj y.x.gammaHat.obj := h

variable (Ft 𝓕 x y)

/-- **`m̂ : M(Γ̂, Γ̂') → M(Ψ̂, Ψ̂')`** (19.57): `((ê, w), (φ̂, Γ(w)), (ê', w')) ↦ (ê, φ̂, ê')`. -/
def mHatMap (h : Ft.MGHat 𝓕 x y) : Ft.MHatB 𝓕 x y :=
  (⟨(h.toTrans.src : x.x.Ψh.ObjE × x.x.bun.W).1,
    ((h.toTrans.mor : (μ.pull P).cat.Mor) : A.Mor × (μ.pull P).E).1,
    (h.toTrans.tgt : y.x.Ψh.ObjE × y.x.bun.W).1,
    (h.toTrans.mor.2 : (μ.pull P).P _ = _).symm.trans (congrArg (μ.pull P).P h.toTrans.src_mor),
    (congrArg Prod.fst (BanFunctor.pull_act μ P h.toTrans.mor)).symm.trans
      (congrArg (fun e => (BanFunctor.pullPt e).1) h.toTrans.tgt_mor)⟩ :
    x.x.Ψh.Trans y.x.Ψh)

/-- **`p̄ : M(Γ̂, Γ̂') → M(Γ, Γ')`** (19.60):
`((ê, w), (φ̂, Γ(w)), (ê', w')) ↦ (w, (P(φ̂), A(w)), w')`. -/
def pbarMap (h : Ft.MGHat 𝓕 x y) : Ft.MG 𝓕 x y :=
  (⟨(h.toTrans.src : x.x.Ψh.ObjE × x.x.bun.W).2, μ.pullMorE P h.toTrans.mor,
    (h.toTrans.tgt : y.x.Ψh.ObjE × y.x.bun.W).2,
    congrArg (fun e => (BanFunctor.pullPt e).2) h.toTrans.src_mor,
    (μ.act_pullMorE P h.toTrans.mor).trans
      (congrArg (fun e => (BanFunctor.pullPt e).2) h.toTrans.tgt_mor)⟩ : x.x.TransG y.x)

/-- **`m ∘ p̄ = p ∘ m̂`** (Theorem 19.8.6 (4)). -/
theorem mGmap_pbarMap (h : Ft.MGHat 𝓕 x y) :
    Ft.mGmap 𝓕 x y (Ft.pbarMap 𝓕 x y h) = Ft.pBmap 𝓕 x y (Ft.mHatMap 𝓕 x y h) :=
  TransitionSet.ext h.toTrans.src.2 rfl h.toTrans.tgt.2

/-- **2021 (19.58): `U : M(Γ̂, Γ̂') → p*M(Γ, Γ')`**,
`U((ê, w), (φ̂, Γ(w)), (ê', w')) = ((ê, φ̂, ê'), (w, (P(φ̂), A(w)), w'))`. -/
def Umap (h : Ft.MGHat 𝓕 x y) : Ft.PB 𝓕 x y :=
  ⟨(Ft.mHatMap 𝓕 x y h, Ft.pbarMap 𝓕 x y h), Ft.mGmap_pbarMap 𝓕 x y h⟩

/-- **The inverse of `U`**:
`((ê, φ̂, ê'), (w, (P(φ̂), A(w)), w')) ↦ ((ê, w), (φ̂, Γ̂(ê, w)), (ê', w'))`. -/
def Uinv (z : Ft.PB 𝓕 x y) : Ft.MGHat 𝓕 x y :=
  let a : x.x.Ψh.Trans y.x.Ψh := (z : Ft.MHatB 𝓕 x y × Ft.MG 𝓕 x y).1
  let g : x.x.TransG y.x := (z : Ft.MHatB 𝓕 x y × Ft.MG 𝓕 x y).2
  have hs : x.x.bun.Q g.src = x.x.Ψh.τ.obj a.src := congrArg TransitionSet.src z.2
  have ht : y.x.bun.Q g.tgt = y.x.Ψh.τ.obj a.tgt := congrArg TransitionSet.tgt z.2
  have hm : ((g.mor : μ.cat.Mor) : B.Mor × μ.E).1 = P.mor a.mor := congrArg TransitionSet.mor z.2
  ⟨⟨(a.src, g.src), hs⟩, ⟨(a.mor, x.x.gammaHatObj ⟨(a.src, g.src), hs⟩), a.src_mor.symm⟩,
    ⟨(a.tgt, g.tgt), ht⟩, rfl,
    BanFunctor.pullPt_injective (by
      change BanFunctor.pullPt ((μ.pull P).act _) = _
      rw [BanFunctor.pull_act]
      exact Prod.ext a.tgt_mor
        ((μ.act_congr (Prod.ext hm.symm g.src_mor.symm)).trans g.tgt_mor))⟩

theorem Uinv_Umap (h : Ft.MGHat 𝓕 x y) : Ft.Uinv 𝓕 x y (Ft.Umap 𝓕 x y h) = h :=
  TransitionSet.ext rfl (Subtype.ext (Prod.ext rfl h.toTrans.src_mor.symm)) rfl

theorem Umap_Uinv (z : Ft.PB 𝓕 x y) : Ft.Umap 𝓕 x y (Ft.Uinv 𝓕 x y z) = z := by
  obtain ⟨⟨a, g⟩, hz⟩ := z
  have hm : ((g.mor : μ.cat.Mor) : B.Mor × μ.E).1 = P.mor (a : x.x.Ψh.Trans y.x.Ψh).mor :=
    congrArg TransitionSet.mor hz
  have hg : ((g.mor : μ.cat.Mor) : B.Mor × μ.E).2 = x.x.Γ.obj g.src := g.src_mor
  refine Subtype.ext (Prod.ext rfl ?_)
  exact TransitionSet.ext rfl (Subtype.ext (Prod.ext hm.symm hg.symm)) rfl

/-- `U` as an equivalence. -/
def Uequiv : Ft.MGHat 𝓕 x y ≃ Ft.PB 𝓕 x y where
  toFun := Ft.Umap 𝓕 x y
  invFun := Ft.Uinv 𝓕 x y
  left_inv := Ft.Uinv_Umap 𝓕 x y
  right_inv := Ft.Umap_Uinv 𝓕 x y

/-- **The topology of `M(Γ̂, Γ̂')`**: the one making `U` a homeomorphism. -/
instance instTopologicalSpaceMGHat : TopologicalSpace (Ft.MGHat 𝓕 x y) :=
  TopologicalSpace.induced (Ft.Umap 𝓕 x y) inferInstance

/-- **`U` as a homeomorphism.** -/
def Uhomeo : Ft.MGHat 𝓕 x y ≃ₜ Ft.PB 𝓕 x y where
  toEquiv := Ft.Uequiv 𝓕 x y
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 (by
    have : Ft.Umap 𝓕 x y ∘ Ft.Uinv 𝓕 x y = id := funext (Ft.Umap_Uinv 𝓕 x y)
    change Continuous (Ft.Umap 𝓕 x y ∘ Ft.Uinv 𝓕 x y)
    rw [this]; exact continuous_id)

instance instT2SpaceMGHat : T2Space (Ft.MGHat 𝓕 x y) := (Ft.Uhomeo 𝓕 x y).isEmbedding.t2Space

instance instParacompactSpaceMGHat : ParacompactSpace (Ft.MGHat 𝓕 x y) :=
  (Ft.Uhomeo 𝓕 x y).isClosedEmbedding.paracompactSpace

/-- The fibres of `m̂` are those of `p*m` (via `U`, (19.59)). -/
def fiberHatEquiv (a : Ft.MHatB 𝓕 x y) :
    Ft.mHatMap 𝓕 x y ⁻¹' {a} ≃ pullbackProj (Ft.mGmap 𝓕 x y) (Ft.pBmap 𝓕 x y) ⁻¹' {a} :=
  fiberEquivOver (Pr := pullbackProj (Ft.mGmap 𝓕 x y) (Ft.pBmap 𝓕 x y)) (Pr' := Ft.mHatMap 𝓕 x y)
    (Ft.Uequiv 𝓕 x y) (fun _ => rfl) a

instance instAddCommGroupFiberHat (a : Ft.MHatB 𝓕 x y) :
    AddCommGroup (Ft.mHatMap 𝓕 x y ⁻¹' {a}) :=
  (Ft.fiberHatEquiv 𝓕 x y a).addCommGroup

instance instModuleFiberHat (a : Ft.MHatB 𝓕 x y) : Module ℝ (Ft.mHatMap 𝓕 x y ⁻¹' {a}) :=
  (Ft.fiberHatEquiv 𝓕 x y a).module ℝ

/-- `U⁻¹` on the fibres, a linear isomorphism. -/
def fiberHatLin (a : Ft.MHatB 𝓕 x y) :
    pullbackProj (Ft.mGmap 𝓕 x y) (Ft.pBmap 𝓕 x y) ⁻¹' {a} ≃ₗ[ℝ] Ft.mHatMap 𝓕 x y ⁻¹' {a} :=
  (Equiv.linearEquiv ℝ (Ft.fiberHatEquiv 𝓕 x y a)).symm

theorem fiberHatLin_apply (a : Ft.MHatB 𝓕 x y)
    (v : pullbackProj (Ft.mGmap 𝓕 x y) (Ft.pBmap 𝓕 x y) ⁻¹' {a}) :
    (Ft.fiberHatLin 𝓕 x y a v : Ft.MGHat 𝓕 x y) = (Ft.Uhomeo 𝓕 x y).symm v := rfl

/-- **The strong bundle structure of `m̂ : M(Γ̂, Γ̂') → M(Ψ̂, Ψ̂')`** (Theorem 19.8.6 (3)):
transported from `p*M(Γ, Γ')` along `U⁻¹`. -/
def bundleHat : StrongBundle (Ft.hatPoly 𝓕 x y) (Ft.mHatMap 𝓕 x y) :=
  (Ft.pullBundle 𝓕 x y).transport (Ft.Uhomeo 𝓕 x y).symm (Ft.fiberHatLin 𝓕 x y)
    (Ft.fiberHatLin_apply 𝓕 x y)

/-- **`U` is a strong bundle isomorphism covering the identity of `M(Ψ̂, Ψ̂')`.** -/
theorem isStrongBundleIso_U :
    (Ft.bundleHat 𝓕 x y).IsStrongBundleIso (Ft.pullBundle 𝓕 x y) id (Ft.Umap 𝓕 x y) id
      (Ft.Uinv 𝓕 x y) :=
  (StrongBundle.isStrongBundleIso_transport (Ft.pullBundle 𝓕 x y)).symm

/-- **Uniqueness (Theorem 19.8.6 (3))**: any strong bundle structure on `m̂` for which `U` is a
strong bundle isomorphism agrees with `bundleHat`. -/
theorem bundleHat_unique (B' : StrongBundle (Ft.hatPoly 𝓕 x y) (Ft.mHatMap 𝓕 x y))
    (hB' : B'.IsStrongBundleIso (Ft.pullBundle 𝓕 x y) id (Ft.Umap 𝓕 x y) id (Ft.Uinv 𝓕 x y)) :
    B'.IsStrongBundleIso (Ft.bundleHat 𝓕 x y) id id id id :=
  StrongBundle.isStrongBundleIso_id_of_isStrongBundleIsoOn B' (Ft.bundleHat 𝓕 x y) hB'.toMap
    (Ft.isStrongBundleIso_U 𝓕 x y).toMap
    (fun _ => ⟨univ, univ, mem_univ _, hB'.isStrongBundleIsoOn_univ⟩)
    (fun _ => ⟨univ, univ, mem_univ _, (Ft.isStrongBundleIso_U 𝓕 x y).isStrongBundleIsoOn_univ⟩)

/-- **`p̄` is a strong bundle map covering `p`.** -/
theorem isStrongBundleMap_pbar :
    (Ft.bundleHat 𝓕 x y).IsStrongBundleMap (Ft.bundleG 𝓕 x y) (Ft.pBmap 𝓕 x y)
      (Ft.pbarMap 𝓕 x y) :=
  ((Ft.bundleG 𝓕 x y).isStrongBundleMap_pullbackProj'
    (Ft.isLocalScDiffeo_pBmap 𝓕 x y).isScSmoothMap).comp (Ft.isStrongBundleIso_U 𝓕 x y).toMap

/-- **`p̄` is a local strong bundle isomorphism** (Theorem 19.8.6 (4)). -/
theorem isLocalStrongBundleIso_pbar (a : Ft.MHatB 𝓕 x y) :
    ∃ (U₀ : Set (Ft.MHatB 𝓕 x y)) (U₀' : Set (Ft.MBase 𝓕 x y)), a ∈ U₀ ∧
      (Ft.bundleHat 𝓕 x y).IsStrongBundleIsoOn (Ft.bundleG 𝓕 x y) (Ft.isStrongBundleMap_pbar 𝓕 x y)
        U₀ U₀' := by
  obtain ⟨U, V, σ, ha, hd⟩ := Ft.isLocalScDiffeo_pBmap 𝓕 x y a
  have hi' := (Ft.bundleG 𝓕 x y).isStrongBundleIsoOn_pullbackProj'
    (Ft.isLocalScDiffeo_pBmap 𝓕 x y).isScSmoothMap hd a
  exact hi'.exists_comp (Ft.isStrongBundleIso_U 𝓕 x y).isStrongBundleIsoOn_univ (mem_univ a) ha

/-- **`p̄` is surjective** (Theorem 19.8.6 (4)). -/
theorem surjective_pbar : Surjective (Ft.pbarMap 𝓕 x y) := fun g => by
  obtain ⟨a, ha⟩ := Ft.surjective_pBmap 𝓕 x y (Ft.mGmap 𝓕 x y g)
  exact ⟨Ft.Uinv 𝓕 x y ⟨(a, g), ha.symm⟩,
    congrArg (fun z : Ft.PB 𝓕 x y => (z : Ft.MHatB 𝓕 x y × Ft.MG 𝓕 x y).2)
      (Ft.Umap_Uinv 𝓕 x y ⟨(a, g), ha.symm⟩)⟩

end Hat

/-! ### Theorem 19.8.6 -/

/-- **2021 Theorem 19.8.6, the functor `Γ̂` and (1)–(4)**, for any transition construction `𝓕`
of the underlying `F` (conditions (1), (2) of Definition 19.8.4 are not used here; they enter
(5) and §19.6). -/
theorem theorem_19_8_6_one_four [Fact (IsFiniteToOneCovering P)]
    (𝓕 : Ft.toUniformizerConstruction.TransitionConstruction) (x y : Ft.Unif) :
    (Injective x.x.gammaHat.obj ∧ x.x.gammaHat.toFunctor.Full ∧
      x.x.gammaHat.toFunctor.Faithful) ∧
    (Ft.srcBundle 𝓕 x y).IsStrongBundleIso (Ft.bundleG 𝓕 x y) id (Ft.altHHomeo 𝓕 x y) id
      (Ft.altHHomeo 𝓕 x y).symm ∧
    ((Ft.hatPoly 𝓕 x y).IsLocalScDiffeo (Ft.basePoly 𝓕 x y) (Ft.pBmap 𝓕 x y) ∧
      Surjective (Ft.pBmap 𝓕 x y)) ∧
    (Bijective (Ft.Umap 𝓕 x y) ∧
      (∀ h, pullbackProj (Ft.mGmap 𝓕 x y) (Ft.pBmap 𝓕 x y) (Ft.Umap 𝓕 x y h) =
        Ft.mHatMap 𝓕 x y h) ∧
      (Ft.bundleHat 𝓕 x y).IsStrongBundleIso (Ft.pullBundle 𝓕 x y) id (Ft.Umap 𝓕 x y) id
        (Ft.Uinv 𝓕 x y) ∧
      ∀ B' : StrongBundle (Ft.hatPoly 𝓕 x y) (Ft.mHatMap 𝓕 x y),
        B'.IsStrongBundleIso (Ft.pullBundle 𝓕 x y) id (Ft.Umap 𝓕 x y) id (Ft.Uinv 𝓕 x y) →
          B'.IsStrongBundleIso (Ft.bundleHat 𝓕 x y) id id id id) ∧
    ((∀ h, Ft.mGmap 𝓕 x y (Ft.pbarMap 𝓕 x y h) = Ft.pBmap 𝓕 x y (Ft.mHatMap 𝓕 x y h)) ∧
      Surjective (Ft.pbarMap 𝓕 x y) ∧
      ∃ hp : (Ft.bundleHat 𝓕 x y).IsStrongBundleMap (Ft.bundleG 𝓕 x y) (Ft.pBmap 𝓕 x y)
          (Ft.pbarMap 𝓕 x y),
        ∀ a, ∃ (U₀ : Set (Ft.MHatB 𝓕 x y)) (U₀' : Set (Ft.MBase 𝓕 x y)), a ∈ U₀ ∧
          (Ft.bundleHat 𝓕 x y).IsStrongBundleIsoOn (Ft.bundleG 𝓕 x y) hp U₀ U₀') :=
  ⟨⟨x.x.injective_gammaHat, x.x.full_gammaHat, x.x.faithful_gammaHat⟩,
    Ft.isStrongBundleIso_altH 𝓕 x y,
    ⟨Ft.isLocalScDiffeo_pBmap 𝓕 x y, Ft.surjective_pBmap 𝓕 x y⟩,
    ⟨(Ft.Uequiv 𝓕 x y).bijective, fun _ => rfl, Ft.isStrongBundleIso_U 𝓕 x y,
      Ft.bundleHat_unique 𝓕 x y⟩,
    ⟨Ft.mGmap_pbarMap 𝓕 x y, Ft.surjective_pbar 𝓕 x y, Ft.isStrongBundleMap_pbar 𝓕 x y,
      Ft.isLocalStrongBundleIso_pbar 𝓕 x y⟩⟩

/-- **2021 Theorem 19.8.6, p. 938**, for a basic construction `(F̃, 𝓕)` of `(P, μ_B)` (with
`P` finite-to-one, Definition 19.8.1, and under `IsCompatible`, the added hypothesis of
l. 44572, for the metrizability of `|A|`), and members `(Ψ, Ψ̂, Γ)`,
`(Ψ', Ψ̂', Γ')` of `F̃`:

* `Γ̂ : τ*W → P*E_B` is injective on objects and fully faithful (the diagram (19.61) is
  `gammaHat_comm`);
* (1) `m : M(Γ, Γ') → M(Ψ, Ψ')` carries the strong bundle structure over the natural M-polyfold
  `M(Ψ, Ψ')` for which `H` is a strong bundle isomorphism (and `M(Ψ̂, Ψ̂')` the structure
  `hatPolyfold`);
* (2) `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is a surjective local sc-diffeomorphism;
* (3) `U : M(Γ̂, Γ̂') → p*M(Γ, Γ')` is a bijection over `M(Ψ̂, Ψ̂')` (19.59), `m̂` carries a strong
  bundle structure turning `U` into a strong bundle isomorphism, and it is unique;
* (4) `m ∘ p̄ = p ∘ m̂`, and `p̄` is a surjective strong bundle map covering `p` which is a local
  strong bundle isomorphism near every point;
* (5) the natural topologies of `|B|` and `|A|` are metrizable. -/
theorem theorem_19_8_6_hyp [Fact (IsFiniteToOneCovering P)] (T : Ft.PullbackTransitionConstruction)
    (hC : T.toCoveringBasicConstruction.IsCompatible) (x y : Ft.Unif) :
    (Injective x.x.gammaHat.obj ∧ x.x.gammaHat.toFunctor.Full ∧
      x.x.gammaHat.toFunctor.Faithful) ∧
    (Ft.srcBundle T.𝓕 x y).IsStrongBundleIso (Ft.bundleG T.𝓕 x y) id (Ft.altHHomeo T.𝓕 x y) id
      (Ft.altHHomeo T.𝓕 x y).symm ∧
    ((Ft.hatPoly T.𝓕 x y).IsLocalScDiffeo (Ft.basePoly T.𝓕 x y) (Ft.pBmap T.𝓕 x y) ∧
      Surjective (Ft.pBmap T.𝓕 x y)) ∧
    (Bijective (Ft.Umap T.𝓕 x y) ∧
      (∀ h, pullbackProj (Ft.mGmap T.𝓕 x y) (Ft.pBmap T.𝓕 x y) (Ft.Umap T.𝓕 x y h) =
        Ft.mHatMap T.𝓕 x y h) ∧
      (Ft.bundleHat T.𝓕 x y).IsStrongBundleIso (Ft.pullBundle T.𝓕 x y) id (Ft.Umap T.𝓕 x y) id
        (Ft.Uinv T.𝓕 x y) ∧
      ∀ B' : StrongBundle (Ft.hatPoly T.𝓕 x y) (Ft.mHatMap T.𝓕 x y),
        B'.IsStrongBundleIso (Ft.pullBundle T.𝓕 x y) id (Ft.Umap T.𝓕 x y) id (Ft.Uinv T.𝓕 x y) →
          B'.IsStrongBundleIso (Ft.bundleHat T.𝓕 x y) id id id id) ∧
    ((∀ h, Ft.mGmap T.𝓕 x y (Ft.pbarMap T.𝓕 x y h) = Ft.pBmap T.𝓕 x y (Ft.mHatMap T.𝓕 x y h)) ∧
      Surjective (Ft.pbarMap T.𝓕 x y) ∧
      ∃ hp : (Ft.bundleHat T.𝓕 x y).IsStrongBundleMap (Ft.bundleG T.𝓕 x y) (Ft.pBmap T.𝓕 x y)
          (Ft.pbarMap T.𝓕 x y),
        ∀ a, ∃ (U₀ : Set (Ft.MHatB T.𝓕 x y)) (U₀' : Set (Ft.MBase T.𝓕 x y)), a ∈ U₀ ∧
          (Ft.bundleHat T.𝓕 x y).IsStrongBundleIsoOn (Ft.bundleG T.𝓕 x y) hp U₀ U₀') ∧
    (@MetrizableSpace _ (T.toCoveringBasicConstruction.toBasic.natTop
        T.hasClassUniformizers.toBasic) ∧
      @MetrizableSpace _ (T.toCoveringBasicConstruction.natTopA Fact.out hC
        T.hasClassUniformizers)) :=
  ⟨⟨x.x.injective_gammaHat, x.x.full_gammaHat, x.x.faithful_gammaHat⟩,
    Ft.isStrongBundleIso_altH T.𝓕 x y,
    ⟨Ft.isLocalScDiffeo_pBmap T.𝓕 x y, Ft.surjective_pBmap T.𝓕 x y⟩,
    ⟨(Ft.Uequiv T.𝓕 x y).bijective, fun _ => rfl, Ft.isStrongBundleIso_U T.𝓕 x y,
      Ft.bundleHat_unique T.𝓕 x y⟩,
    ⟨Ft.mGmap_pbarMap T.𝓕 x y, Ft.surjective_pbar T.𝓕 x y, Ft.isStrongBundleMap_pbar T.𝓕 x y,
      Ft.isLocalStrongBundleIso_pbar T.𝓕 x y⟩,
    T.metrizable,
    (T.toCoveringBasicConstruction.theorem_19_7_25_one_hyp Fact.out hC T.hasClassUniformizers
      T.metrizable).1⟩

end PullbackUniformizerConstruction

end GroupoidalCategory

end

end Polyfold
