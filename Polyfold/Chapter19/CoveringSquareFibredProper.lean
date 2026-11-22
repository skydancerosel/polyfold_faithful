import Polyfold.Chapter19.CoveringSquareMultiplication
import Polyfold.Chapter19.FibredProductCovering

/-!
# The fibred-product square of Theorem 19.8.22 is proper (HWZ 2021 §19.8, pp. 955–957)

2021 Theorem 19.8.22 (pp. 956–957), last sentence: the multiplication
`m : M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂') → M(Γ̂, Γ̂'')` is a strong bundle map *between proper strong
bundle covering squares* (diagram (19.100), p. 955; Definition 19.8.19, p. 954). The source
square is

```
M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂')  --p̂ ₛ×ₜ p̂-->  M(Γ', Γ'') ₛ×ₜ M(Γ, Γ')
          |                                   |
M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂')  --p ₛ×ₜ p-->   M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')
```

with the strong bundle structures of `mulBundleSq`, `mulBundleG` (the pull-backs of `m̂`, `m` by
`pr₂`, identified with the literal fibred products by `fpEquivSq`, `fpEquivG`).

## What is formalized

* `liftSrc_HFP`, `injOn_srcH_HFP`: `ŝ : M(Ψ̂', Ψ̂'') → Ê'` is bijective from each fibre `p⁻¹(k')`
  onto `τ̂'⁻¹(s(k'))` (Lemma 19.7.9), in the form used by `FibredProductCovering`.
* `surjective_pFP`, `isLocalScDiffeo_pFP`, `finite_pFP_fiber`, `bijOn_pFP_fiber`:
  `p ₛ×ₜ p` is a surjective local sc-diffeomorphism of the sub-M-polyfolds whose fibre over
  `(k', k)` is the fibre of `p` over `k`.
* **`isProperSquare_pbarFP`**: the square above is a proper strong bundle covering square
  (`isProperStrongBundleCoveringSquare_fibredProduct` applied to `isProperSquare_pbarSq`).
* **`theorem_19_8_22_mul_hyp`**: Theorem 19.8.22 for the multiplication (19.100), with both
  squares proper (it contains `isStrongBundleMap_mul_and_faces`).
* For a basic construction `Bs` (Definition 19.8.15):
  **`SquareBasicConstruction.theorem_19_8_22_inv_hyp`** (the inversion, coherence from `Bs`) and
  **`SquareBasicConstruction.theorem_19_8_22_hyp`**, the whole theorem (the complete form of
  Theorem 19.8.22).

## The hypotheses `hcoh` and `hC`

* `hcoh : Ft.toPullback.IsCoherent 𝓕` is condition (2) of Definition 19.8.4 (= Definition 19.8.14),
  a field of every basic construction `(F̃, 𝓕)` of Definition 19.8.15 (`Bs.T.isCoherent`): it is
  part of the printed hypothesis "a basic construction `(F̃, 𝓕)`" of Theorem 19.8.22, and the
  forms for `Bs` do not take it.
* `hC : (Ft.toPullback.toCBC 𝓕).IsCompatible` is the continuity of every top target map
  `t̂ : M(Ψ̂, Ψ̂') → Ê'`: an added hypothesis, the reading of l. 44572 (the opening of §19.7: the
  uniformizers "are sc-smoothly compatible"), used for Proposition 19.7.15 (2); hence the `_hyp`
  suffix.  We do not derive it from Definitions 19.8.13–19.8.15: coherence concerns the bottom
  strong bundles `M(Γ, Γ')` over `M(Ψ, Ψ')`, while `t̂` depends on the sheets of the `Ψ̂`, on
  which Definition 19.8.10 imposes nothing beyond Definition 19.7.4; for covering basic
  constructions `proposition_19_7_15_two_without_compatible` (`twistBasic`) shows that `t̂` need
  not be continuous without it.  The top fibred product `M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂')` is a
  sub-M-polyfold only once `t̂` is sc-smooth.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace Polyfold

noncomputable section

universe u

open Set Function Topology TopologicalSpace

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

variable {A B : GroupoidalCategory.{u}}

namespace SquareUniformizerConstruction

variable {S : BundleCoveringSquare A B} (Ft : SquareUniformizerConstruction S)
  (𝓕 : Ft.toPullback.toUniformizerConstruction.TransitionConstruction) (X Y Z : Ft.Unif)

/-! ### `ŝ` over `p` is fibrewise bijective (Lemma 19.7.9) -/

/-- **Lifting (Lemma 19.7.9)**: for `a ∈ M(Ψ̂, Ψ̂')` and `k' ∈ M(Ψ', Ψ'')` with
`s(k') = t(p(a))` there is `a' ∈ M(Ψ̂', Ψ̂'')` over `k'` with `ŝ(a') = t̂(a)`. -/
theorem liftSrc_HFP (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU)
    (k : Ft.toPullback.MBase 𝓕 Y.toPU Z.toPU)
    (hk : Ft.toPullback.srcB 𝓕 Y.toPU Z.toPU k =
      Ft.toPullback.tgtB 𝓕 X.toPU Y.toPU (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU a)) :
    ∃ a', Ft.toPullback.pBmap 𝓕 Y.toPU Z.toPU a' = k ∧ Ft.srcH 𝓕 Y Z a' = Ft.tgtH 𝓕 X Y a := by
  obtain ⟨a', ha', hs⟩ := ((Y.x.Ψh.lemma_19_7_9 Z.x.Ψh S.isFiniteToOneCovering).2 k).1.surjOn
    (show Ft.tgtH 𝓕 X Y a ∈ Y.x.Ψh.τ.obj ⁻¹' {(k : Y.x.Ψh.Ψ.Trans Z.x.Ψh.Ψ).src} from hk.symm)
  exact ⟨a', ha', hs⟩

/-- **Injectivity (Lemma 19.7.9)**: `ŝ` is injective on the fibres of `p`. -/
theorem injOn_srcH_HFP (a b : Ft.toPullback.MHatB 𝓕 Y.toPU Z.toPU)
    (hp : Ft.toPullback.pBmap 𝓕 Y.toPU Z.toPU a = Ft.toPullback.pBmap 𝓕 Y.toPU Z.toPU b)
    (hs : Ft.srcH 𝓕 Y Z a = Ft.srcH 𝓕 Y Z b) : a = b :=
  ((Y.x.Ψh.lemma_19_7_9 Z.x.Ψh S.isFiniteToOneCovering).2
    (Ft.toPullback.pBmap 𝓕 Y.toPU Z.toPU a)).1.injOn rfl hp.symm hs

/-! ### `p ₛ×ₜ p` -/

theorem continuous_pFP : Continuous (Ft.pFP 𝓕 X Y Z) :=
  MPolyfold.continuous_fibredProductMap
    (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 Y.toPU Z.toPU).continuous
    (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU).continuous (fun _ => rfl) fun _ => rfl

/-- **`p ₛ×ₜ p : M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂') → M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` is a local
sc-diffeomorphism** of the sub-M-polyfolds, under `IsCompatible`. -/
theorem isLocalScDiffeo_pFP (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.HFPpoly 𝓕 X Y Z hC).IsLocalScDiffeo (Ft.toPullback.BFPpoly 𝓕 X.toPU Y.toPU Z.toPU)
      (Ft.pFP 𝓕 X Y Z) :=
  MPolyfold.isLocalScDiffeo_fibredProductMap (Ft.isLocalScDiffeo_srcH 𝓕 Y Z)
    (Ft.isLocalScDiffeo_tgtH 𝓕 X Y hC).isScSmoothMap
    (Ft.toPullback.isLocalScDiffeo_srcBase 𝓕 Y.toPU Z.toPU)
    (Ft.toPullback.isScSmoothMap_tgtB 𝓕 X.toPU Y.toPU)
    (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU) (Ft.continuous_pFP 𝓕 X Y Z)
    fun _ => rfl

/-- **`p ₛ×ₜ p` is surjective.** -/
theorem surjective_pFP : Surjective (Ft.pFP 𝓕 X Y Z) :=
  MPolyfold.surjective_fibredProductMap (Ft.toPullback.surjective_pBmap 𝓕 X.toPU Y.toPU)
    (fun a k hk => Ft.liftSrc_HFP 𝓕 X Y Z a k hk) (fun _ => rfl) fun _ => rfl

/-- **The fibre of `p ₛ×ₜ p` over `(k', k)` is the fibre of `p` over `k`**: `pr₂` is a bijection
`(p ₛ×ₜ p)⁻¹(k', k) → p⁻¹(k)`. -/
theorem bijOn_pFP_fiber (k : Ft.toPullback.BFP 𝓕 X.toPU Y.toPU Z.toPU) :
    BijOn (Ft.pr₂H 𝓕 X Y Z) (Ft.pFP 𝓕 X Y Z ⁻¹' {k})
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU ⁻¹' {k.1.2}) := by
  refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_, fun a₂ ha₂ => ?_⟩
  · change Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU a.1.2 = k.1.2
    rw [← show Ft.pFP 𝓕 X Y Z a = k from ha]
    rfl
  · exact MPolyfold.fibredProductMap_eq_of_snd_eq (Θ := Ft.pFP 𝓕 X Y Z)
      (fun a b => Ft.injOn_srcH_HFP 𝓕 Y Z a b) (fun _ => rfl)
      ((show Ft.pFP 𝓕 X Y Z a = k from ha).trans hb.symm) hab
  · have hk : Ft.toPullback.srcB 𝓕 Y.toPU Z.toPU k.1.1 =
        Ft.toPullback.tgtB 𝓕 X.toPU Y.toPU k.1.2 := k.2
    obtain ⟨a₁, ha₁, hs⟩ := Ft.liftSrc_HFP 𝓕 X Y Z a₂ _
      (hk.trans (congrArg (Ft.toPullback.tgtB 𝓕 X.toPU Y.toPU) (show _ = _ from ha₂).symm))
    exact ⟨⟨(a₁, a₂), hs⟩, Subtype.ext (Prod.ext ha₁ ha₂), rfl⟩

/-- **The fibres of `p ₛ×ₜ p` have the cardinality of the fibres of `τ̂`**: `(p ₛ×ₜ p)⁻¹(k', k)`
has as many points as `τ̂⁻¹(s(k))` (`bijOn_pFP_fiber` and Lemma 19.7.9). -/
theorem ncard_pFP_fiber (k : Ft.toPullback.BFP 𝓕 X.toPU Y.toPU Z.toPU) :
    (Ft.pFP 𝓕 X Y Z ⁻¹' {k}).ncard =
      (X.x.Ψh.τ.obj ⁻¹' {(k.1.2 : X.x.Ψh.Ψ.Trans Y.x.Ψh.Ψ).src}).ncard := by
  have h1 := Ft.bijOn_pFP_fiber 𝓕 X Y Z k
  have h2 := ((X.x.Ψh.lemma_19_7_9 Y.x.Ψh S.isFiniteToOneCovering).2 k.1.2).1
  calc (Ft.pFP 𝓕 X Y Z ⁻¹' {k}).ncard = (Ft.pr₂H 𝓕 X Y Z '' (Ft.pFP 𝓕 X Y Z ⁻¹' {k})).ncard :=
        (h1.injOn.ncard_image).symm
    _ = (X.x.Ψh.transMap Y.x.Ψh ⁻¹' {(k.1.2 : X.x.Ψh.Ψ.Trans Y.x.Ψh.Ψ)}).ncard := by
        rw [h1.image_eq]; rfl
    _ = ((fun a : X.x.Ψh.Trans Y.x.Ψh => a.src) ''
          (X.x.Ψh.transMap Y.x.Ψh ⁻¹' {(k.1.2 : X.x.Ψh.Ψ.Trans Y.x.Ψh.Ψ)})).ncard :=
        (h2.injOn.ncard_image).symm
    _ = _ := congrArg Set.ncard h2.image_eq

/-- The fibres of `p ₛ×ₜ p` are finite. -/
theorem finite_pFP_fiber (k : Ft.toPullback.BFP 𝓕 X.toPU Y.toPU Z.toPU) :
    (Ft.pFP 𝓕 X Y Z ⁻¹' {k}).Finite :=
  MPolyfold.finite_fibredProductMap_fiber (fun a b => Ft.injOn_srcH_HFP 𝓕 Y Z a b)
    (fun _ => rfl) (fun _ => rfl) k
    ((X.x.Ψh.lemma_19_7_9 Y.x.Ψh S.isFiniteToOneCovering).2 _).2

/-! ### The proper strong bundle covering square over `p ₛ×ₜ p` -/

/-- **2021 Theorem 19.8.22, p. 957, the source square of the multiplication (19.100)**: under
`IsCompatible`, `p̂ ₛ×ₜ p̂ : M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂') → M(Γ', Γ'') ₛ×ₜ M(Γ, Γ')` over
`p ₛ×ₜ p : M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂') → M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` is a proper strong bundle
covering square (Definition 19.8.19), for the strong bundles `mulBundleSq`, `mulBundleG`. -/
theorem isProperSquare_pbarFP (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    IsProperStrongBundleCoveringSquare (Ft.mulBundleSq 𝓕 X Y Z hC)
      (Ft.toPullback.mulBundleG 𝓕 X.toPU Y.toPU Z.toPU) (Ft.pFP 𝓕 X Y Z) (Ft.pbarFP 𝓕 X Y Z) :=
  isProperStrongBundleCoveringSquare_fibredProduct (Ft.isLocalScDiffeo_srcH 𝓕 Y Z)
    (Ft.isLocalScDiffeo_tgtH 𝓕 X Y hC).isScSmoothMap
    (Ft.toPullback.isLocalScDiffeo_srcBase 𝓕 Y.toPU Z.toPU)
    (Ft.toPullback.isScSmoothMap_tgtB 𝓕 X.toPU Y.toPU) (Ft.isProperSquare_pbarSq 𝓕 X Y)
    (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 Y.toPU Z.toPU).continuous (fun _ => rfl)
    (fun _ => rfl) (fun a k hk => Ft.liftSrc_HFP 𝓕 X Y Z a k hk)
    fun a b => Ft.injOn_srcH_HFP 𝓕 Y Z a b

/-! ### Theorem 19.8.22 for the multiplication -/

/-- **2021 Theorem 19.8.22, p. 957, the multiplication (diagram (19.100))**, under `IsCompatible`
(an added hypothesis, the reading of l. 44572): with `M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂')` and
`M(Γ', Γ'') ₛ×ₜ M(Γ, Γ')` the pull-backs of `m̂`, `m` by `pr₂` (`fpEquivSq`, `fpEquivG`), the
multiplications are strong bundle maps covering `m̂` and `m`, `p̂ ₛ×ₜ p̂` is a strong bundle map
covering `p ₛ×ₜ p`, the faces of (19.100) commute, the multiplications are the composition
`(h', h) ↦ h' ∘ h`, and the multiplication is a map between proper strong bundle covering
squares: the square `p̂ ₛ×ₜ p̂` over `p ₛ×ₜ p` and the square `p̂ : M(Γ̂, Γ̂'') → M(Γ, Γ'')` are
proper. -/
theorem theorem_19_8_22_mul_hyp (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    ((Ft.mulBundleSq 𝓕 X Y Z hC).IsStrongBundleMap (Ft.bundleSq 𝓕 X Z) (Ft.mulH 𝓕 X Y Z)
      (Ft.mulSq 𝓕 X Y Z) ∧
    (Ft.toPullback.mulBundleG 𝓕 X.toPU Y.toPU Z.toPU).IsStrongBundleMap
      (Ft.toPullback.bundleG 𝓕 X.toPU Z.toPU) (Ft.toPullback.mulB 𝓕 X.toPU Y.toPU Z.toPU)
      (Ft.toPullback.mulG 𝓕 X.toPU Y.toPU Z.toPU) ∧
    (Ft.mulBundleSq 𝓕 X Y Z hC).IsStrongBundleMap
      (Ft.toPullback.mulBundleG 𝓕 X.toPU Y.toPU Z.toPU) (Ft.pFP 𝓕 X Y Z) (Ft.pbarFP 𝓕 X Y Z) ∧
    (∀ w, Ft.mSq 𝓕 X Z (Ft.mulSq 𝓕 X Y Z w) =
      Ft.mulH 𝓕 X Y Z (pullbackProj (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z) w)) ∧
    (∀ w, Ft.pbarSq 𝓕 X Z (Ft.mulSq 𝓕 X Y Z w) =
      Ft.toPullback.mulG 𝓕 X.toPU Y.toPU Z.toPU (Ft.pbarFP 𝓕 X Y Z w)) ∧
    (∀ w, Ft.toPullback.pBmap 𝓕 X.toPU Z.toPU (Ft.mulH 𝓕 X Y Z w) =
      Ft.toPullback.mulB 𝓕 X.toPU Y.toPU Z.toPU (Ft.pFP 𝓕 X Y Z w)) ∧
    (∀ q, Ft.mulSq 𝓕 X Y Z (Ft.toFPSq 𝓕 X Y Z q) = (TransitionSet.comp q.1.1.toTrans
      q.1.2.toTrans (TransitionSet.mor_composable_of_src_eq_tgt q.2) : Ft.MSq 𝓕 X Z)) ∧
    ∀ q, Ft.toPullback.mulG 𝓕 X.toPU Y.toPU Z.toPU (Ft.toPullback.toFPG 𝓕 X.toPU Y.toPU Z.toPU q) =
      (TransitionSet.comp (q.1.1 : Y.toPU.x.TransG Z.toPU.x) (q.1.2 : X.toPU.x.TransG Y.toPU.x)
        (TransitionSet.mor_composable_of_src_eq_tgt q.2) : X.toPU.x.TransG Z.toPU.x)) ∧
    IsProperStrongBundleCoveringSquare (Ft.mulBundleSq 𝓕 X Y Z hC)
      (Ft.toPullback.mulBundleG 𝓕 X.toPU Y.toPU Z.toPU) (Ft.pFP 𝓕 X Y Z) (Ft.pbarFP 𝓕 X Y Z) ∧
    IsProperStrongBundleCoveringSquare (Ft.bundleSq 𝓕 X Z) (Ft.toPullback.bundleG 𝓕 X.toPU Z.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Z.toPU) (Ft.pbarSq 𝓕 X Z) :=
  ⟨Ft.isStrongBundleMap_mul_and_faces 𝓕 X Y Z hC, Ft.isProperSquare_pbarFP 𝓕 X Y Z hC,
    Ft.isProperSquare_pbarSq 𝓕 X Z⟩

end SquareUniformizerConstruction

/-! ### Theorem 19.8.22 for a basic construction -/

namespace SquareBasicConstruction

variable {S : BundleCoveringSquare A B} (Bs : SquareBasicConstruction S)

/-- **2021 Theorem 19.8.22, p. 957, the inversion (diagram (19.98))**, for a basic construction
`(F̃, 𝓕)` (Definition 19.8.15, which contains the coherence of `𝓕`), under `IsCompatible` (an
added hypothesis, the reading of l. 44572): `ι : M(Γ̂, Γ̂') → M(Γ̂', Γ̂)` and
`ι : M(Γ, Γ') → M(Γ', Γ)` are strong bundle isomorphisms covering `ι̂` and `ι`, the faces of (19.98)
commute, and both squares are proper strong bundle covering squares. -/
theorem theorem_19_8_22_inv_hyp (X Y : Bs.Ft.Unif)
    (hC : (Bs.Ft.toPullback.toCBC Bs.T.𝓕).IsCompatible) :
    (Bs.Ft.bundleSq Bs.T.𝓕 X Y).IsStrongBundleIso (Bs.Ft.bundleSq Bs.T.𝓕 Y X)
      (Bs.Ft.invH Bs.T.𝓕 X Y) (Bs.Ft.invSq Bs.T.𝓕 X Y) (Bs.Ft.invH Bs.T.𝓕 Y X)
      (Bs.Ft.invSq Bs.T.𝓕 Y X) ∧
    (Bs.Ft.toPullback.bundleG Bs.T.𝓕 X.toPU Y.toPU).IsStrongBundleIso
      (Bs.Ft.toPullback.bundleG Bs.T.𝓕 Y.toPU X.toPU) (Bs.Ft.toPullback.invB Bs.T.𝓕 X.toPU Y.toPU)
      (Bs.Ft.toPullback.invG Bs.T.𝓕 X.toPU Y.toPU) (Bs.Ft.toPullback.invB Bs.T.𝓕 Y.toPU X.toPU)
      (Bs.Ft.toPullback.invG Bs.T.𝓕 Y.toPU X.toPU) ∧
    (∀ h, Bs.Ft.mSq Bs.T.𝓕 Y X (Bs.Ft.invSq Bs.T.𝓕 X Y h) =
      Bs.Ft.invH Bs.T.𝓕 X Y (Bs.Ft.mSq Bs.T.𝓕 X Y h)) ∧
    (∀ h, Bs.Ft.pbarSq Bs.T.𝓕 Y X (Bs.Ft.invSq Bs.T.𝓕 X Y h) =
      Bs.Ft.toPullback.invG Bs.T.𝓕 X.toPU Y.toPU (Bs.Ft.pbarSq Bs.T.𝓕 X Y h)) ∧
    (∀ a, Bs.Ft.toPullback.pBmap Bs.T.𝓕 Y.toPU X.toPU (Bs.Ft.invH Bs.T.𝓕 X Y a) =
      Bs.Ft.toPullback.invB Bs.T.𝓕 X.toPU Y.toPU (Bs.Ft.toPullback.pBmap Bs.T.𝓕 X.toPU Y.toPU a)) ∧
    IsProperStrongBundleCoveringSquare (Bs.Ft.bundleSq Bs.T.𝓕 X Y)
      (Bs.Ft.toPullback.bundleG Bs.T.𝓕 X.toPU Y.toPU)
      (Bs.Ft.toPullback.pBmap Bs.T.𝓕 X.toPU Y.toPU) (Bs.Ft.pbarSq Bs.T.𝓕 X Y) ∧
    IsProperStrongBundleCoveringSquare (Bs.Ft.bundleSq Bs.T.𝓕 Y X)
      (Bs.Ft.toPullback.bundleG Bs.T.𝓕 Y.toPU X.toPU)
      (Bs.Ft.toPullback.pBmap Bs.T.𝓕 Y.toPU X.toPU) (Bs.Ft.pbarSq Bs.T.𝓕 Y X) :=
  Bs.Ft.theorem_19_8_22_inv_hyp Bs.T.𝓕 X Y Bs.T.isCoherent hC

/-- **2021 Theorem 19.8.22 (Strong bundle covering), pp. 956–957**, for a basic construction
`(F̃, 𝓕)` of the bundle covering square (Definition 19.8.15: `𝓕` coherent, class uniformizers,
`T_{|B|}` metrizable), under `IsCompatible` (an added hypothesis, the reading of l. 44572): the
complete form of the theorem:

1. the orbit spaces `|A|`, `|E_B|`, `|E_A|` carry the natural metrizable topologies
   (`T̄_{|A|}` of Theorem 19.7.25, `T̄_B` of Definition 19.6.7 for `(F̄, 𝓕)`, `T̄_A` of
   Definition 19.8.20; `T_{|B|}` is metrizable by Definition 19.8.4 (1));
2. for members `Γ̂`, `Γ̂'` the square `p̂ : M(Γ̂, Γ̂') → M(Γ, Γ')` over `p` is a proper strong
   bundle covering square, and the source and target maps of `M(Γ̂, Γ̂')` and `M(Γ, Γ')` are
   local strong bundle isomorphisms;
3. the inversion `ι : M(Γ̂, Γ̂') → M(Γ̂', Γ̂)` is an isomorphism of proper strong bundle covering
   squares;
4. the unit `u : K → M(Γ̂, Γ̂)` is a strong bundle map between proper strong bundle covering
   squares;
5. the multiplication `M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂') → M(Γ̂, Γ̂'')` is a strong bundle map between
   proper strong bundle covering squares (`theorem_19_8_22_mul_hyp`). -/
theorem theorem_19_8_22_hyp (hC : (Bs.Ft.toPullback.toCBC Bs.T.𝓕).IsCompatible) :
    (@MetrizableSpace _ ((Bs.Ft.toPullback.toCBC Bs.T.𝓕).natTopA S.isFiniteToOneCovering hC
        Bs.T.hasClassUniformizers) ∧
      @MetrizableSpace _ (Bs.Ft.toPullback.natTopEB Bs.T.𝓕 Bs.T.isCoherent
        Bs.T.hasClassUniformizers) ∧
      @MetrizableSpace _ (Bs.Ft.natTopEA Bs.T.𝓕 Bs.T.isCoherent hC Bs.T.hasClassUniformizers) ∧
      ∀ X Y : Bs.Ft.Unif,
        IsProperStrongBundleCoveringSquare (Bs.Ft.bundleSq Bs.T.𝓕 X Y)
          (Bs.Ft.toPullback.bundleG Bs.T.𝓕 X.toPU Y.toPU)
          (Bs.Ft.toPullback.pBmap Bs.T.𝓕 X.toPU Y.toPU) (Bs.Ft.pbarSq Bs.T.𝓕 X Y) ∧
        (∀ a, ∃ (U : Set (Bs.Ft.toPullback.MHatB Bs.T.𝓕 X.toPU Y.toPU))
          (U' : Set X.x.Ψh.ObjE), a ∈ U ∧
          (Bs.Ft.bundleSq Bs.T.𝓕 X Y).IsStrongBundleIsoOn X.x.K.BWh
            (Bs.Ft.isStrongBundleMap_srcSq Bs.T.𝓕 X Y) U U') ∧
        (∀ a, ∃ (U : Set (Bs.Ft.toPullback.MHatB Bs.T.𝓕 X.toPU Y.toPU))
          (U' : Set Y.toPU.x.Ψh.ObjE), a ∈ U ∧
          (Bs.Ft.bundleSq Bs.T.𝓕 X Y).IsStrongBundleIsoOn Y.x.K.BWh
            (Bs.Ft.isStrongBundleMap_tgtSq Bs.T.𝓕 X Y Bs.T.isCoherent hC) U U') ∧
        (∀ k, ∃ (U : Set (Bs.Ft.toPullback.MBase Bs.T.𝓕 X.toPU Y.toPU))
          (U' : Set X.toPU.x.Ψh.Ψ.O), k ∈ U ∧
          (Bs.Ft.toPullback.bundleG Bs.T.𝓕 X.toPU Y.toPU).IsStrongBundleIsoOn X.x.K.BW
            (Bs.Ft.isStrongBundleMap_srcG Bs.T.𝓕 X Y) U U') ∧
        ∀ k, ∃ (U : Set (Bs.Ft.toPullback.MBase Bs.T.𝓕 X.toPU Y.toPU))
          (U' : Set Y.toPU.x.Ψh.Ψ.O), k ∈ U ∧
          (Bs.Ft.toPullback.bundleG Bs.T.𝓕 X.toPU Y.toPU).IsStrongBundleIsoOn
            Y.toPU.x.bun.bundle
            (Bs.Ft.toPullback.isStrongBundleMap_tgtGmap Bs.T.𝓕 X.toPU Y.toPU Bs.T.isCoherent)
            U U') ∧
    (∀ X Y : Bs.Ft.Unif,
      (Bs.Ft.bundleSq Bs.T.𝓕 X Y).IsStrongBundleIso (Bs.Ft.bundleSq Bs.T.𝓕 Y X)
        (Bs.Ft.invH Bs.T.𝓕 X Y) (Bs.Ft.invSq Bs.T.𝓕 X Y) (Bs.Ft.invH Bs.T.𝓕 Y X)
        (Bs.Ft.invSq Bs.T.𝓕 Y X) ∧
      (Bs.Ft.toPullback.bundleG Bs.T.𝓕 X.toPU Y.toPU).IsStrongBundleIso
        (Bs.Ft.toPullback.bundleG Bs.T.𝓕 Y.toPU X.toPU)
        (Bs.Ft.toPullback.invB Bs.T.𝓕 X.toPU Y.toPU) (Bs.Ft.toPullback.invG Bs.T.𝓕 X.toPU Y.toPU)
        (Bs.Ft.toPullback.invB Bs.T.𝓕 Y.toPU X.toPU) (Bs.Ft.toPullback.invG Bs.T.𝓕 Y.toPU X.toPU) ∧
      (∀ h, Bs.Ft.mSq Bs.T.𝓕 Y X (Bs.Ft.invSq Bs.T.𝓕 X Y h) =
        Bs.Ft.invH Bs.T.𝓕 X Y (Bs.Ft.mSq Bs.T.𝓕 X Y h)) ∧
      ∀ h, Bs.Ft.pbarSq Bs.T.𝓕 Y X (Bs.Ft.invSq Bs.T.𝓕 X Y h) =
        Bs.Ft.toPullback.invG Bs.T.𝓕 X.toPU Y.toPU (Bs.Ft.pbarSq Bs.T.𝓕 X Y h)) ∧
    (∀ X : Bs.Ft.Unif,
      X.x.K.BWh.IsStrongBundleMap (Bs.Ft.bundleSq Bs.T.𝓕 X X) (Bs.Ft.unitH Bs.T.𝓕 X)
        (Bs.Ft.unitSq Bs.T.𝓕 X) ∧
      X.toPU.x.bun.bundle.IsStrongBundleMap (Bs.Ft.toPullback.bundleG Bs.T.𝓕 X.toPU X.toPU)
        (Bs.Ft.toPullback.unitB Bs.T.𝓕 X.toPU) (Bs.Ft.toPullback.unitG Bs.T.𝓕 X.toPU) ∧
      (∀ w, Bs.Ft.mSq Bs.T.𝓕 X X (Bs.Ft.unitSq Bs.T.𝓕 X w) = Bs.Ft.unitH Bs.T.𝓕 X (X.x.K.Qh w)) ∧
      (∀ w, Bs.Ft.pbarSq Bs.T.𝓕 X X (Bs.Ft.unitSq Bs.T.𝓕 X w) =
        Bs.Ft.toPullback.unitG Bs.T.𝓕 X.toPU (X.x.K.Ξ w)) ∧
      IsProperStrongBundleCoveringSquare X.x.K.BWh X.x.K.BW X.x.Ψh.τ.obj X.x.K.Ξ) ∧
    ∀ X Y Z : Bs.Ft.Unif,
      (Bs.Ft.mulBundleSq Bs.T.𝓕 X Y Z hC).IsStrongBundleMap (Bs.Ft.bundleSq Bs.T.𝓕 X Z)
        (Bs.Ft.mulH Bs.T.𝓕 X Y Z) (Bs.Ft.mulSq Bs.T.𝓕 X Y Z) ∧
      (Bs.Ft.toPullback.mulBundleG Bs.T.𝓕 X.toPU Y.toPU Z.toPU).IsStrongBundleMap
        (Bs.Ft.toPullback.bundleG Bs.T.𝓕 X.toPU Z.toPU)
        (Bs.Ft.toPullback.mulB Bs.T.𝓕 X.toPU Y.toPU Z.toPU)
        (Bs.Ft.toPullback.mulG Bs.T.𝓕 X.toPU Y.toPU Z.toPU) ∧
      (∀ w, Bs.Ft.mSq Bs.T.𝓕 X Z (Bs.Ft.mulSq Bs.T.𝓕 X Y Z w) =
        Bs.Ft.mulH Bs.T.𝓕 X Y Z (pullbackProj (Bs.Ft.mSq Bs.T.𝓕 X Y) (Bs.Ft.pr₂H Bs.T.𝓕 X Y Z) w)) ∧
      (∀ w, Bs.Ft.pbarSq Bs.T.𝓕 X Z (Bs.Ft.mulSq Bs.T.𝓕 X Y Z w) =
        Bs.Ft.toPullback.mulG Bs.T.𝓕 X.toPU Y.toPU Z.toPU (Bs.Ft.pbarFP Bs.T.𝓕 X Y Z w)) ∧
      IsProperStrongBundleCoveringSquare (Bs.Ft.mulBundleSq Bs.T.𝓕 X Y Z hC)
        (Bs.Ft.toPullback.mulBundleG Bs.T.𝓕 X.toPU Y.toPU Z.toPU) (Bs.Ft.pFP Bs.T.𝓕 X Y Z)
        (Bs.Ft.pbarFP Bs.T.𝓕 X Y Z) := by
  refine ⟨Bs.Ft.theorem_19_8_22_topology_hyp Bs.T.𝓕 Bs.T.isCoherent hC Bs.T.hasClassUniformizers
    Bs.T.metrizable, fun X Y => ?_, fun X => ?_, fun X Y Z => ?_⟩
  · obtain ⟨h1, h2, h3, h4, -⟩ := Bs.theorem_19_8_22_inv_hyp X Y hC
    exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨h1, h2, h3, h4, -, h5, -⟩ := Bs.Ft.theorem_19_8_22_unit Bs.T.𝓕 X
    exact ⟨h1, h2, h3, h4, h5⟩
  · obtain ⟨⟨h1, h2, -, h3, h4, -⟩, h5, -⟩ := Bs.Ft.theorem_19_8_22_mul_hyp Bs.T.𝓕 X Y Z hC
    exact ⟨h1, h2, h3, h4, h5⟩

end SquareBasicConstruction

end GroupoidalCategory

end

end Polyfold
