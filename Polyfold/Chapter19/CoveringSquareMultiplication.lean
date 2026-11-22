import Polyfold.Chapter19.CoveringSquareTopology

/-!
# Inversion, unit and multiplication of the transition squares (HWZ 2021 §19.8, pp. 955–957)

2021 Theorem 19.8.22 (pp. 956–957), the last three sentences: the inversion
`ι : M(Γ̂, Γ̂') → M(Γ̂', Γ̂)` is an isomorphism between proper strong bundle covering squares, and
the unit map `u : K → M(Γ̂, Γ̂)` and the multiplication
`m : M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂') → M(Γ̂, Γ̂'')` are strong bundle maps between proper strong bundle
covering squares (the diagrams (19.98)–(19.100), p. 955).

## What is formalized

The bottom face (`PullbackUniformizerConstruction`, the strong bundles `M(Γ, Γ') → M(Ψ, Ψ')` of
Lemma 19.8.16 / Theorem 19.8.6):

* `isStrongBundleIso_invG`: `ι : M(Γ, Γ') → M(Γ', Γ)` is a strong bundle isomorphism covering
  `ι : M(Ψ, Ψ') → M(Ψ', Ψ)`, for coherent `𝓕` (`invG = H' ∘ A ∘ C ∘ H⁻¹`, `invG_eq`);
* `isStrongBundleMap_unitG`: `u : W → M(Γ, Γ)` covering `u : O → M(Ψ, Ψ)`;
* `mulBundleG`, `fpEquivG`, `isStrongBundleMap_mulG`, `mulG_toFPG`: the fibred product
  `M(Γ', Γ'') ₛ×ₜ M(Γ, Γ')` is the total space of a strong bundle over
  `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`, and the composition is a strong bundle map covering `m`.

The top face (`SquareUniformizerConstruction`, the strong bundles `M(Γ̂, Γ̂') → M(Ψ̂, Ψ̂')`):

* `isStrongBundleIso_invSq`: `ι : M(Γ̂, Γ̂') → M(Γ̂', Γ̂)` is a strong bundle isomorphism covering
  `ι̂`, with `mSq_invSq`, `pbarSq_invSq`, `pBmap_invH` the faces of (19.98);
* `isStrongBundleMap_unitSq`: `u : Ŵ → M(Γ̂, Γ̂)` covering `û : Ê → M(Ψ̂, Ψ̂)`, with
  `mSq_unitSq`, `pbarSq_unitSq`, `pBmap_unitH` the faces of (19.99);
* `HFPpoly`, `mulBundleSq`, `fpEquivSq`, `isStrongBundleMap_mulSq`, `mulSq_toFPSq`: the fibred
  product `M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂')` is the total space of a strong bundle over the
  sub-M-polyfold `M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂')`, the composition is a strong bundle map covering
  `m̂`,   `isStrongBundleMap_pbarFP` (`p̂ ₛ×ₜ p̂` over `p ₛ×ₜ p`), and `mSq_mulSq`, `pbarSq_mulSq`,
  `pBmap_mulH` the faces of (19.100);
* `theorem_19_8_22_inv_hyp`, `theorem_19_8_22_unit`, `isStrongBundleMap_mul_and_faces` collect
  these, together with the properness of the squares `K` and `M(Γ̂, Γ̂')` (`isProperSquare`,
  `isProperSquare_pbarSq`).

2021 Remark 19.6.2 (p. 892), the variant of Definition 19.6.1 over an ep-groupoid, is the form
in which Definition 19.8.10 (3) reads `Γ̂` (`SquareUniformizer`); its consequence
`Ψ̄(0_e) = (α, 0_{μ(e)})` is `SquareUniformizer.remark_19_6_2` for `Γ̂` and `Γ`.

## Readings

* We read the strong bundle structure on `M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂')` (and on
  `M(Γ', Γ'') ₛ×ₜ M(Γ, Γ')`), which the text uses in (19.100) without spelling it out, as the
  pull-back of `m̂ : M(Γ̂, Γ̂') → M(Ψ̂, Ψ̂')` by
  `pr₂ : M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂') → M(Ψ̂, Ψ̂')`, as for `m̄` in §17.8 and §19.6: a point
  `((a', a), h)` with `m̂(h) = a` determines the element `h'` over `a'` with `s(h') = t(h)`,
  and `fpEquivSq` identifies the total space with the fibred product.
* The top inversion and multiplication use the sc-smoothness of `ι̂`, `t̂` and `m̂`, proved under
  `IsCompatible` (Proposition 19.7.26), an added hypothesis, the reading of l. 44572; hence the
  `_hyp` suffix on `theorem_19_8_22_inv_hyp`. The inversion on `M(Γ, Γ')` uses the coherence of `𝓕`
  (Definition 19.8.14), as for `ι̂` in Theorem 19.6.13. The unit needs neither.

## In `CoveringSquareFibredProper.lean`

The square formed by `M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂') → M(Γ', Γ'') ₛ×ₜ M(Γ, Γ')` over
`p ₛ×ₜ p` is a proper strong bundle covering square (`isProperSquare_pbarFP`); the
multiplication with both squares proper is `theorem_19_8_22_mul_hyp`, and the whole theorem for a
basic construction is `SquareBasicConstruction.theorem_19_8_22_hyp`.
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

/-! ### The structure maps of `M(Γ, Γ')` (bottom face) -/

namespace PullbackUniformizerConstruction

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} {μ : B.BanFunctor}
  (Ft : PullbackUniformizerConstruction P μ)
  (𝓕 : Ft.toUniformizerConstruction.TransitionConstruction) (x y z : Ft.Unif)

/-- **`s : M(Γ, Γ') → W` is a strong bundle map covering `s : M(Ψ, Ψ') → O`** (`s = pr₂ ∘ H⁻¹`). -/
theorem isStrongBundleMap_srcGmap :
    (Ft.bundleG 𝓕 x y).IsStrongBundleMap x.x.bun.bundle (Ft.srcB 𝓕 x y) (Ft.srcGmap 𝓕 x y) :=
  (x.x.bun.bundle.isStrongBundleMap_pullbackProj' (Ft.isScSmoothMap_srcB 𝓕 x y)).comp
    (Ft.isStrongBundleIso_altH 𝓕 x y).invMap

/-! #### The inversion -/

/-- **The inversion `ι : M(Ψ, Ψ') → M(Ψ', Ψ)`** of the natural M-polyfolds (Corollary 19.5.2). -/
abbrev invB (k : Ft.MBase 𝓕 x y) : Ft.MBase 𝓕 y x :=
  (Ft.toCBC 𝓕).toBasic.rep.toTr (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).inv

theorem isScSmoothMap_invB :
    (Ft.basePoly 𝓕 x y).IsScSmoothMap (Ft.basePoly 𝓕 y x) (Ft.invB 𝓕 x y) :=
  ((Ft.toCBC 𝓕).isScDiffeoOn_invB x.toHat y.toHat).isScSmoothOn

/-- **The inversion `ι : M(Γ, Γ') → M(Γ', Γ)`**, `h ↦ h⁻¹`. -/
def invG (h : Ft.MG 𝓕 x y) : Ft.MG 𝓕 y x := (h : x.x.TransG y.x).inv

/-- `m ∘ ι = ι ∘ m` (the bottom face of (19.98)). -/
theorem mGmap_invG (h : Ft.MG 𝓕 x y) :
    Ft.mGmap 𝓕 y x (Ft.invG 𝓕 x y h) = Ft.invB 𝓕 x y (Ft.mGmap 𝓕 x y h) := rfl

theorem invG_invG (h : Ft.MG 𝓕 x y) : Ft.invG 𝓕 y x (Ft.invG 𝓕 x y h) = h :=
  TransitionSet.inv_inv (h : x.x.TransG y.x)

/-- **2021 (19.18) for the members of `F̃`: `A((e, φ, e'), w') = ((e', φ⁻¹, e), w')`**,
`A : M(Ψ, Ψ') ₜ×_{Q'} W' → M(Ψ', Ψ) ₛ×_{Q'} W'`. -/
def altA (z : Ft.TgtPB 𝓕 x y) : Ft.SrcPB 𝓕 y x :=
  ⟨(Ft.invB 𝓕 x y (z : Ft.MBase 𝓕 x y × y.x.bun.W).1, (z : Ft.MBase 𝓕 x y × y.x.bun.W).2), z.2⟩

/-- `A⁻¹`. -/
def altAinv (z : Ft.SrcPB 𝓕 y x) : Ft.TgtPB 𝓕 x y :=
  ⟨(Ft.invB 𝓕 y x (z : Ft.MBase 𝓕 y x × y.x.bun.W).1, (z : Ft.MBase 𝓕 y x × y.x.bun.W).2), z.2⟩

theorem altAinv_altA (z : Ft.TgtPB 𝓕 x y) : Ft.altAinv 𝓕 x y (Ft.altA 𝓕 x y z) = z :=
  Subtype.ext (Prod.ext (TransitionSet.inv_inv _) rfl)

theorem altA_altAinv (z : Ft.SrcPB 𝓕 y x) : Ft.altA 𝓕 x y (Ft.altAinv 𝓕 x y z) = z :=
  Subtype.ext (Prod.ext (TransitionSet.inv_inv _) rfl)

/-- **`A` is a strong bundle isomorphism covering `ι`** (p. 902). -/
theorem isStrongBundleIso_altA :
    (Ft.tgtBundle 𝓕 x y).IsStrongBundleIso (Ft.srcBundle 𝓕 y x) (Ft.invB 𝓕 x y) (Ft.altA 𝓕 x y)
      (Ft.invB 𝓕 y x) (Ft.altAinv 𝓕 x y) :=
  ⟨StrongBundle.isStrongBundleMap_pullbackPair y.x.bun.bundle (Ft.isScSmoothMap_srcB 𝓕 y x)
      (l := Ft.invB 𝓕 x y) (Ft.isScSmoothMap_invB 𝓕 x y)
      (y.x.bun.bundle.isStrongBundleMap_pullbackProj' (Ft.isScSmoothMap_tgtB 𝓕 x y)),
    StrongBundle.isStrongBundleMap_pullbackPair y.x.bun.bundle (Ft.isScSmoothMap_tgtB 𝓕 x y)
      (l := Ft.invB 𝓕 y x) (Ft.isScSmoothMap_invB 𝓕 y x)
      (y.x.bun.bundle.isStrongBundleMap_pullbackProj' (Ft.isScSmoothMap_srcB 𝓕 y x)),
    Ft.altAinv_altA 𝓕 x y, Ft.altA_altAinv 𝓕 x y⟩

/-- **`ι = H ∘ (A ∘ C) ∘ H⁻¹`** on `M(Γ, Γ')` (p. 904). -/
theorem invG_eq : Ft.invG 𝓕 x y = Ft.altHHomeo 𝓕 y x ∘
    (Ft.altA 𝓕 x y ∘ Ft.altC 𝓕 x y ∘ (Ft.altHHomeo 𝓕 x y).symm) :=
  funext fun h => y.x.str.eq_of_proj x.x.str
    (congrArg TransitionSet.tgt (Ft.altH_altHinv 𝓕 x y h).symm)
    ((congrArg (fun g : x.x.TransG y.x => (x.x.mG y.x g).inv) (Ft.altH_altHinv 𝓕 x y h).symm).trans
      (y.x.str.proj_lift x.x.str _ _ _).symm)

/-- `ι : M(Γ, Γ') → M(Γ', Γ)` is a strong bundle map covering `ι`, for coherent `𝓕`. -/
theorem isStrongBundleMap_invG (hcoh : Ft.IsCoherent 𝓕) :
    (Ft.bundleG 𝓕 x y).IsStrongBundleMap (Ft.bundleG 𝓕 y x) (Ft.invB 𝓕 x y) (Ft.invG 𝓕 x y) := by
  obtain ⟨hm, -⟩ := hcoh x y
  rw [Ft.invG_eq 𝓕 x y]
  exact (Ft.isStrongBundleIso_altH 𝓕 y x).toMap.comp
    (((Ft.isStrongBundleIso_altA 𝓕 x y).toMap.comp hm).comp
      (Ft.isStrongBundleIso_altH 𝓕 x y).invMap)

/-- **The inversion `ι : M(Γ, Γ') → M(Γ', Γ)` is a strong bundle isomorphism covering
`ι : M(Ψ, Ψ') → M(Ψ', Ψ)`** (Theorem 19.6.13 for the members of `F̃`), for coherent `𝓕`. -/
theorem isStrongBundleIso_invG (hcoh : Ft.IsCoherent 𝓕) :
    (Ft.bundleG 𝓕 x y).IsStrongBundleIso (Ft.bundleG 𝓕 y x) (Ft.invB 𝓕 x y) (Ft.invG 𝓕 x y)
      (Ft.invB 𝓕 y x) (Ft.invG 𝓕 y x) :=
  ⟨Ft.isStrongBundleMap_invG 𝓕 x y hcoh, Ft.isStrongBundleMap_invG 𝓕 y x hcoh,
    Ft.invG_invG 𝓕 x y, Ft.invG_invG 𝓕 y x⟩

/-! #### The unit -/

/-- **The unit `u : O → M(Ψ, Ψ)`** (Corollary 19.5.2). -/
abbrev unitB (o : x.x.Ψh.Ψ.O) : Ft.MBase 𝓕 x x :=
  (Ft.toCBC 𝓕).toBasic.rep.toTr (TransitionSet.unit o : x.x.Ψh.Ψ.Trans x.x.Ψh.Ψ)

theorem isScSmoothMap_unitB : x.x.Ψh.Ψ.P.IsScSmoothMap (Ft.basePoly 𝓕 x x) (Ft.unitB 𝓕 x) :=
  (Ft.toCBC 𝓕).toBasic.rep.isScSmoothMap_unit x.toHat.toUnif

/-- **The unit `u : W → M(Γ, Γ)`**, `w ↦ (w, 1_{Γ(w)}, w)`. -/
def unitG (w : x.x.bun.W) : Ft.MG 𝓕 x x := (TransitionSet.unit w : x.x.TransG x.x)

/-- `m ∘ u = u ∘ Q`. -/
theorem mGmap_unitG (w : x.x.bun.W) :
    Ft.mGmap 𝓕 x x (Ft.unitG 𝓕 x w) = Ft.unitB 𝓕 x (x.x.bun.Q w) :=
  x.x.str.proj_unit w

/-- **`u = H ∘ (u ∘ Q, Id)`** (p. 904). -/
theorem unitG_eq : Ft.unitG 𝓕 x = Ft.altHHomeo 𝓕 x x ∘ pullbackPair x.x.bun.Q (Ft.srcB 𝓕 x x)
    (Ft.unitB 𝓕 x ∘ x.x.bun.Q) id (fun _ => rfl) :=
  funext fun w => x.x.str.eq_of_proj x.x.str rfl
    ((x.x.str.proj_unit w).trans (x.x.str.proj_lift x.x.str _ _ _).symm)

/-- **The unit `u : W → M(Γ, Γ)` is a strong bundle map covering `u : O → M(Ψ, Ψ)`.** -/
theorem isStrongBundleMap_unitG :
    x.x.bun.bundle.IsStrongBundleMap (Ft.bundleG 𝓕 x x) (Ft.unitB 𝓕 x) (Ft.unitG 𝓕 x) := by
  rw [Ft.unitG_eq 𝓕 x]
  exact (Ft.isStrongBundleIso_altH 𝓕 x x).toMap.comp
    (StrongBundle.isStrongBundleMap_pullbackPair x.x.bun.bundle (Ft.isScSmoothMap_srcB 𝓕 x x)
      (Ft.isScSmoothMap_unitB 𝓕 x) (StrongBundle.IsStrongBundleMap.id _))

/-! #### The multiplication -/

/-- **The fibred product `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`.** -/
abbrev BFP : Set (Ft.MBase 𝓕 y z × Ft.MBase 𝓕 x y) :=
  MPolyfold.fibredProduct (Ft.srcB 𝓕 y z) (Ft.tgtB 𝓕 x y)

instance instParacompactSpaceProdMBase : ParacompactSpace (Ft.MBase 𝓕 y z × Ft.MBase 𝓕 x y) :=
  MPolyfold.paracompactSpace_prod (Ft.basePoly 𝓕 y z) (Ft.basePoly 𝓕 x y)

instance instParacompactSpaceBFP : ParacompactSpace (Ft.BFP 𝓕 x y z) :=
  ((Ft.basePoly 𝓕 y z).prod (Ft.basePoly 𝓕 x y)).paracompactSpace_subtype _

theorem isLocalScDiffeo_srcBase :
    (Ft.basePoly 𝓕 x y).IsLocalScDiffeo x.x.Ψh.Ψ.P (Ft.srcB 𝓕 x y) :=
  (Ft.toCBC 𝓕).isLocalScDiffeo_srcB' x.toHat y.toHat

theorem isSubMPolyfold_BFP :
    ((Ft.basePoly 𝓕 y z).prod (Ft.basePoly 𝓕 x y)).IsSubMPolyfold (Ft.BFP 𝓕 x y z) :=
  MPolyfold.isSubMPolyfold_fibredProduct (Ft.isLocalScDiffeo_srcBase 𝓕 y z)
    (Ft.isScSmoothMap_tgtB 𝓕 x y)

/-- The M-polyfold structure of `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` (Definition 17.1.8 (c)). -/
def BFPpoly : MPolyfold (Ft.BFP 𝓕 x y z) := MPolyfold.subPolyfold (Ft.isSubMPolyfold_BFP 𝓕 x y z)

/-- `pr₂ : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ')`. -/
abbrev pr₂B (w : Ft.BFP 𝓕 x y z) : Ft.MBase 𝓕 x y := w.1.2

/-- **The multiplication `m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')`.** -/
abbrev mulB (w : Ft.BFP 𝓕 x y z) : Ft.MBase 𝓕 x z :=
  (Ft.toCBC 𝓕).toBasic.rep.toTr (TransitionSet.mul w)

theorem isScSmoothMap_pr₂B :
    (Ft.BFPpoly 𝓕 x y z).IsScSmoothMap (Ft.basePoly 𝓕 x y) (Ft.pr₂B 𝓕 x y z) :=
  (MPolyfold.isScSmoothMap_snd _ _).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth (Ft.isSubMPolyfold_BFP 𝓕 x y z))

theorem isScSmoothMap_mulB :
    (Ft.BFPpoly 𝓕 x y z).IsScSmoothMap (Ft.basePoly 𝓕 x z) (Ft.mulB 𝓕 x y z) :=
  (Ft.toCBC 𝓕).toBasic.rep.isScSmoothMap_mul x.toHat.toUnif y.toHat.toUnif z.toHat.toUnif

instance instParacompactSpaceMulPB :
    ParacompactSpace (pullbackSpace (Ft.mGmap 𝓕 x y) (Ft.pr₂B 𝓕 x y z)) :=
  paracompactSpace_pullbackSpace (Ft.BFPpoly 𝓕 x y z) (Ft.bundleG 𝓕 x y)

/-- **The strong bundle over `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`** whose total space is
`M(Γ', Γ'') ₛ×ₜ M(Γ, Γ')` (`fpEquivG`): the pull-back of `m : M(Γ, Γ') → M(Ψ, Ψ')` by `pr₂`. -/
def mulBundleG : StrongBundle (Ft.BFPpoly 𝓕 x y z)
    (pullbackProj (Ft.mGmap 𝓕 x y) (Ft.pr₂B 𝓕 x y z)) :=
  (Ft.bundleG 𝓕 x y).pullback (Ft.isScSmoothMap_pr₂B 𝓕 x y z)

/-- The element of `M(Γ', Γ'')` over `k'` with source `t(h)`, for `((k', k), h)` with
`m(h) = k`. -/
def mulLiftG (w : pullbackSpace (Ft.mGmap 𝓕 x y) (Ft.pr₂B 𝓕 x y z)) : y.x.TransG z.x :=
  y.x.str.lift z.x.str
    (((w : Ft.BFP 𝓕 x y z × Ft.MG 𝓕 x y).1 : Ft.MBase 𝓕 y z × Ft.MBase 𝓕 x y).1 :
      y.x.Ψh.Ψ.Trans z.x.Ψh.Ψ)
    ((w : Ft.BFP 𝓕 x y z × Ft.MG 𝓕 x y).2 : x.x.TransG y.x).tgt
    ((congrArg (fun k : Ft.MBase 𝓕 x y => (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).tgt) w.2).trans
      (w : Ft.BFP 𝓕 x y z × Ft.MG 𝓕 x y).1.2.symm)

/-- **The multiplication `m : M(Γ', Γ'') ₛ×ₜ M(Γ, Γ') → M(Γ, Γ'')`** on the total space of
`mulBundleG`: `((k', k), h) ↦ h' ∘ h` with `h'` over `k'`, `s(h') = t(h)`. -/
def mulG (w : pullbackSpace (Ft.mGmap 𝓕 x y) (Ft.pr₂B 𝓕 x y z)) : Ft.MG 𝓕 x z :=
  (TransitionSet.comp (Ft.mulLiftG 𝓕 x y z w)
    ((w : Ft.BFP 𝓕 x y z × Ft.MG 𝓕 x y).2 : x.x.TransG y.x)
    (TransitionSet.mor_composable_of_src_eq_tgt rfl) : x.x.TransG z.x)

/-- **The multiplication `M(Γ', Γ'') ₛ×ₜ M(Γ, Γ') → M(Γ, Γ'')` is a strong bundle map covering
`m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')`** (`m̄ = H ∘ (m ∘ π, s ∘ pr₂)`, p. 904). -/
theorem isStrongBundleMap_mulG :
    (Ft.mulBundleG 𝓕 x y z).IsStrongBundleMap (Ft.bundleG 𝓕 x z) (Ft.mulB 𝓕 x y z)
      (Ft.mulG 𝓕 x y z) := by
  have hΘ := (Ft.isStrongBundleMap_srcGmap 𝓕 x y).comp
    ((Ft.bundleG 𝓕 x y).isStrongBundleMap_pullbackProj' (Ft.isScSmoothMap_pr₂B 𝓕 x y z))
  have hpair := StrongBundle.isStrongBundleMap_pullbackPair x.x.bun.bundle
    (Ft.isScSmoothMap_srcB 𝓕 x z) (l := Ft.mulB 𝓕 x y z) (Ft.isScSmoothMap_mulB 𝓕 x y z) hΘ
  have h := (Ft.isStrongBundleIso_altH 𝓕 x z).toMap.comp hpair
  have key : ∀ (a a' : y.x.Ψh.Ψ.Trans z.x.Ψh.Ψ) (b b' : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ) (ha : a = a')
      (hb : b = b') hab hab', TransitionSet.comp a b hab = TransitionSet.comp a' b' hab' := by
    intros; subst_vars; rfl
  have e : (⇑(Ft.altHHomeo 𝓕 x z) ∘ pullbackPair x.x.bun.Q (Ft.srcB 𝓕 x z)
      (Ft.mulB 𝓕 x y z ∘ pullbackProj (Ft.mGmap 𝓕 x y) (Ft.pr₂B 𝓕 x y z))
      (Ft.srcGmap 𝓕 x y ∘ pullbackProj' (Ft.mGmap 𝓕 x y) (Ft.pr₂B 𝓕 x y z)) hΘ.covers) =
      Ft.mulG 𝓕 x y z := by
    funext w
    exact x.x.str.eq_of_proj z.x.str rfl
      (((x.x.str.proj_lift z.x.str _ _ _).trans
        (key _ _ _ _ (y.x.str.proj_lift z.x.str _ _ _) w.2 _
          (TransitionSet.mor_composable_of_src_eq_tgt w.1.1.2)).symm).trans
        (x.x.str.proj_comp y.x.str z.x.str _ _ _).symm)
  rw [e] at h
  exact h

/-- **The literal fibred product `M(Γ', Γ'') ₛ×ₜ M(Γ, Γ')`**: pairs `(h', h)` with
`s(h') = t(h)`. -/
abbrev FPG : Type u :=
  {q : Ft.MG 𝓕 y z × Ft.MG 𝓕 x y // (q.1 : y.x.TransG z.x).src = (q.2 : x.x.TransG y.x).tgt}

/-- `(h', h) ↦ ((m(h'), m(h)), h)`. -/
def toFPG (q : Ft.FPG 𝓕 x y z) : pullbackSpace (Ft.mGmap 𝓕 x y) (Ft.pr₂B 𝓕 x y z) :=
  ⟨(⟨(Ft.mGmap 𝓕 y z q.1.1, Ft.mGmap 𝓕 x y q.1.2), congrArg y.x.bun.Q q.2⟩, q.1.2), rfl⟩

/-- `((k', k), h) ↦ (h', h)`. -/
def ofFPG (w : pullbackSpace (Ft.mGmap 𝓕 x y) (Ft.pr₂B 𝓕 x y z)) : Ft.FPG 𝓕 x y z :=
  ⟨(Ft.mulLiftG 𝓕 x y z w, (w : Ft.BFP 𝓕 x y z × Ft.MG 𝓕 x y).2), rfl⟩

theorem mulLiftG_toFPG (q : Ft.FPG 𝓕 x y z) : Ft.mulLiftG 𝓕 x y z (Ft.toFPG 𝓕 x y z q) = q.1.1 :=
  ((y.x.str.eq_lift_iff z.x.str _).2 ⟨q.2, rfl⟩).symm

theorem ofFPG_toFPG (q : Ft.FPG 𝓕 x y z) : Ft.ofFPG 𝓕 x y z (Ft.toFPG 𝓕 x y z q) = q :=
  Subtype.ext (Prod.ext (Ft.mulLiftG_toFPG 𝓕 x y z q) rfl)

theorem toFPG_ofFPG (w : pullbackSpace (Ft.mGmap 𝓕 x y) (Ft.pr₂B 𝓕 x y z)) :
    Ft.toFPG 𝓕 x y z (Ft.ofFPG 𝓕 x y z w) = w :=
  Subtype.ext (Prod.ext (Subtype.ext (Prod.ext (y.x.str.proj_lift z.x.str _ _ _) w.2)) rfl)

/-- **`M(Γ', Γ'') ₛ×ₜ M(Γ, Γ')` is the total space of `mulBundleG`.** -/
def fpEquivG : Ft.FPG 𝓕 x y z ≃ pullbackSpace (Ft.mGmap 𝓕 x y) (Ft.pr₂B 𝓕 x y z) where
  toFun := Ft.toFPG 𝓕 x y z
  invFun := Ft.ofFPG 𝓕 x y z
  left_inv := Ft.ofFPG_toFPG 𝓕 x y z
  right_inv := Ft.toFPG_ofFPG 𝓕 x y z

/-- **Under `fpEquivG`, `mulG` is the composition**: `mulG((m(h'), m(h)), h) = h' ∘ h`. -/
theorem mulG_toFPG (q : Ft.FPG 𝓕 x y z) :
    Ft.mulG 𝓕 x y z (Ft.toFPG 𝓕 x y z q) = (TransitionSet.comp (q.1.1 : y.x.TransG z.x)
      (q.1.2 : x.x.TransG y.x) (TransitionSet.mor_composable_of_src_eq_tgt q.2) :
        x.x.TransG z.x) := by
  have e := Ft.mulLiftG_toFPG 𝓕 x y z q
  exact TransitionSet.ext rfl (congrArg (fun g : y.x.TransG z.x =>
    μ.cat.toGroupoidStr.comp g.mor (q.1.2 : x.x.TransG y.x).mor) e)
    (congrArg (fun g : y.x.TransG z.x => g.tgt) e)

end PullbackUniformizerConstruction

/-! ### The structure maps of `M(Γ̂, Γ̂')` (top face) -/

namespace SquareUniformizerConstruction

variable {S : BundleCoveringSquare A B} (Ft : SquareUniformizerConstruction S)
  (𝓕 : Ft.toPullback.toUniformizerConstruction.TransitionConstruction) (X Y Z : Ft.Unif)

/-! #### The inversion -/

/-- The top inversion `ι̂ : M(Ψ̂, Ψ̂') → M(Ψ̂', Ψ̂)`. -/
abbrev invH (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) : Ft.toPullback.MHatB 𝓕 Y.toPU X.toPU :=
  (Ft.toPullback.toCBC 𝓕).invHat X.toPU.toHat Y.toPU.toHat a

theorem isScSmoothMap_invH (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.toPullback.hatPoly 𝓕 X.toPU Y.toPU).IsScSmoothMap (Ft.toPullback.hatPoly 𝓕 Y.toPU X.toPU)
      (Ft.invH 𝓕 X Y) :=
  (Ft.toPullback.toCBC 𝓕).isScSmoothMap_invHat S.isFiniteToOneCovering hC X.toPU.toHat
    Y.toPU.toHat

/-- `p ∘ ι̂ = ι ∘ p`. -/
theorem pBmap_invH (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) :
    Ft.toPullback.pBmap 𝓕 Y.toPU X.toPU (Ft.invH 𝓕 X Y a) =
      Ft.toPullback.invB 𝓕 X.toPU Y.toPU (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU a) :=
  X.x.Ψh.transMap_inv Y.x.Ψh _

/-- **The inversion `ι : M(Γ̂, Γ̂') → M(Γ̂', Γ̂)`**, `h ↦ h⁻¹`. -/
def invSq (h : Ft.MSq 𝓕 X Y) : Ft.MSq 𝓕 Y X := h.toTrans.inv

theorem invSq_invSq (h : Ft.MSq 𝓕 X Y) : Ft.invSq 𝓕 Y X (Ft.invSq 𝓕 X Y h) = h :=
  TransitionSet.inv_inv h.toTrans

/-- `m̂ ∘ ι = ι̂ ∘ m̂` (the left face of (19.98)). -/
theorem mSq_invSq (h : Ft.MSq 𝓕 X Y) :
    Ft.mSq 𝓕 Y X (Ft.invSq 𝓕 X Y h) = Ft.invH 𝓕 X Y (Ft.mSq 𝓕 X Y h) := rfl

/-- `p̂ ∘ ι = ι ∘ p̂` (the top face of (19.98)). -/
theorem pbarSq_invSq (h : Ft.MSq 𝓕 X Y) :
    Ft.pbarSq 𝓕 Y X (Ft.invSq 𝓕 X Y h) =
      Ft.toPullback.invG 𝓕 X.toPU Y.toPU (Ft.pbarSq 𝓕 X Y h) :=
  TransitionSet.ext rfl (GroupoidFunctor.mor_inv S.Phat _) rfl

/-- `ι̂ × ι : p*M(Γ, Γ') → p*M(Γ', Γ)`, `(a, g) ↦ (ι̂(a), ι(g))`. -/
def invPB : Ft.toPullback.PB 𝓕 X.toPU Y.toPU → Ft.toPullback.PB 𝓕 Y.toPU X.toPU :=
  pullbackPair (Ft.toPullback.mGmap 𝓕 Y.toPU X.toPU) (Ft.toPullback.pBmap 𝓕 Y.toPU X.toPU)
    (Ft.invH 𝓕 X Y ∘ pullbackProj (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU))
    (Ft.toPullback.invG 𝓕 X.toPU Y.toPU ∘ pullbackProj' (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU))
    fun z => (congrArg (Ft.toPullback.invB 𝓕 X.toPU Y.toPU) z.2).trans (Ft.pBmap_invH 𝓕 X Y _).symm

theorem USq_invSq (h : Ft.MSq 𝓕 X Y) :
    Ft.USq 𝓕 Y X (Ft.invSq 𝓕 X Y h) = Ft.invPB 𝓕 X Y (Ft.USq 𝓕 X Y h) :=
  Subtype.ext (Prod.ext (Ft.mSq_invSq 𝓕 X Y h) (Ft.pbarSq_invSq 𝓕 X Y h))

/-- **`ι = U⁻¹ ∘ (ι̂ × ι) ∘ U`** on `M(Γ̂, Γ̂')`. -/
theorem invSq_eq : Ft.invSq 𝓕 X Y = Ft.USqInv 𝓕 Y X ∘ Ft.invPB 𝓕 X Y ∘ Ft.USq 𝓕 X Y :=
  funext fun h => by
    rw [comp_apply, comp_apply, ← Ft.USq_invSq 𝓕 X Y h, Ft.USqInv_USq]

theorem isStrongBundleMap_invPB (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU).IsStrongBundleMap
      (Ft.toPullback.pullBundle 𝓕 Y.toPU X.toPU) (Ft.invH 𝓕 X Y) (Ft.invPB 𝓕 X Y) :=
  StrongBundle.isStrongBundleMap_pullbackPair (Ft.toPullback.bundleG 𝓕 Y.toPU X.toPU)
    (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 Y.toPU X.toPU).isScSmoothMap (l := Ft.invH 𝓕 X Y)
    (Ft.isScSmoothMap_invH 𝓕 X Y hC)
    (((Ft.toPullback.isStrongBundleMap_invG 𝓕 X.toPU Y.toPU hcoh).comp
      ((Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU).isStrongBundleMap_pullbackProj'
        (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU).isScSmoothMap)).congr_base
      (funext fun a => (Ft.pBmap_invH 𝓕 X Y a).symm))

/-- `ι : M(Γ̂, Γ̂') → M(Γ̂', Γ̂)` is a strong bundle map covering `ι̂` (Definition 19.8.17). -/
theorem isStrongBundleMap_invSq (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.bundleSq 𝓕 X Y).IsStrongBundleMap (Ft.bundleSq 𝓕 Y X) (Ft.invH 𝓕 X Y) (Ft.invSq 𝓕 X Y) := by
  rw [Ft.invSq_eq 𝓕 X Y]
  exact (Ft.isStrongBundleIso_USq 𝓕 Y X).invMap.comp
    ((Ft.isStrongBundleMap_invPB 𝓕 X Y hcoh hC).comp (Ft.isStrongBundleIso_USq 𝓕 X Y).toMap)

/-- **The inversion `ι : M(Γ̂, Γ̂') → M(Γ̂', Γ̂)` is a strong bundle isomorphism covering
`ι̂ : M(Ψ̂, Ψ̂') → M(Ψ̂', Ψ̂)`**, for coherent `𝓕` under `IsCompatible`. -/
theorem isStrongBundleIso_invSq (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.bundleSq 𝓕 X Y).IsStrongBundleIso (Ft.bundleSq 𝓕 Y X) (Ft.invH 𝓕 X Y) (Ft.invSq 𝓕 X Y)
      (Ft.invH 𝓕 Y X) (Ft.invSq 𝓕 Y X) :=
  ⟨Ft.isStrongBundleMap_invSq 𝓕 X Y hcoh hC, Ft.isStrongBundleMap_invSq 𝓕 Y X hcoh hC,
    Ft.invSq_invSq 𝓕 X Y, Ft.invSq_invSq 𝓕 Y X⟩

/-! #### The unit -/

/-- The top unit `û : Ê → M(Ψ̂, Ψ̂)`. -/
abbrev unitH (e : X.x.Ψh.ObjE) : Ft.toPullback.MHatB 𝓕 X.toPU X.toPU :=
  (Ft.toPullback.toCBC 𝓕).unitHat X.toPU.toHat e

theorem isScSmoothMap_unitH :
    X.x.Ψh.E.PObj.IsScSmoothMap (Ft.toPullback.hatPoly 𝓕 X.toPU X.toPU) (Ft.unitH 𝓕 X) :=
  (Ft.toPullback.toCBC 𝓕).isScSmoothMap_unitHat S.isFiniteToOneCovering X.toPU.toHat

/-- `p ∘ û = u ∘ τ̂`. -/
theorem pBmap_unitH (e : X.x.Ψh.ObjE) :
    Ft.toPullback.pBmap 𝓕 X.toPU X.toPU (Ft.unitH 𝓕 X e) =
      Ft.toPullback.unitB 𝓕 X.toPU (X.x.Ψh.τ.obj e) :=
  X.x.Ψh.transMap_unit e

/-- **The unit `u : Ŵ → M(Γ̂, Γ̂)`**, `ŵ ↦ (ŵ, 1_{Γ̂(ŵ)}, ŵ)`. -/
def unitSq (w : X.x.K.Wh) : Ft.MSq 𝓕 X X :=
  (TransitionSet.unit w : S.μA.cat.toGroupoidStr.TransitionSet X.x.Γh.obj X.x.Γh.obj)

/-- `m̂ ∘ u = û ∘ Q̂` (the left face of (19.99)). -/
theorem mSq_unitSq (w : X.x.K.Wh) :
    Ft.mSq 𝓕 X X (Ft.unitSq 𝓕 X w) = Ft.unitH 𝓕 X (X.x.K.Qh w) :=
  TransitionSet.ext rfl (congrArg A.toGroupoidStr.unit (X.x.PA_obj w)) rfl

/-- `p̂ ∘ u = u ∘ Ξ` (the top face of (19.99)). -/
theorem pbarSq_unitSq (w : X.x.K.Wh) :
    Ft.pbarSq 𝓕 X X (Ft.unitSq 𝓕 X w) = Ft.toPullback.unitG 𝓕 X.toPU (X.x.K.Ξ w) :=
  TransitionSet.ext rfl ((S.Phat.mor_unit _).trans
    (congrArg S.μB.cat.toGroupoidStr.unit (X.x.comm_obj w))) rfl

/-- `(û ∘ Q̂, u ∘ Ξ) : Ŵ → p*M(Γ, Γ)`. -/
def unitPB : X.x.K.Wh → Ft.toPullback.PB 𝓕 X.toPU X.toPU :=
  pullbackPair (Ft.toPullback.mGmap 𝓕 X.toPU X.toPU) (Ft.toPullback.pBmap 𝓕 X.toPU X.toPU)
    (Ft.unitH 𝓕 X ∘ X.x.K.Qh) (Ft.toPullback.unitG 𝓕 X.toPU ∘ X.x.K.Ξ)
    fun w => (Ft.toPullback.mGmap_unitG 𝓕 X.toPU _).trans
      ((congrArg (Ft.toPullback.unitB 𝓕 X.toPU) (X.x.K.Q_Ξ w)).trans (Ft.pBmap_unitH 𝓕 X _).symm)

theorem USq_unitSq (w : X.x.K.Wh) : Ft.USq 𝓕 X X (Ft.unitSq 𝓕 X w) = Ft.unitPB 𝓕 X w :=
  Subtype.ext (Prod.ext (Ft.mSq_unitSq 𝓕 X w) (Ft.pbarSq_unitSq 𝓕 X w))

/-- **`u = U⁻¹ ∘ (û ∘ Q̂, u ∘ Ξ)`** on `Ŵ`. -/
theorem unitSq_eq : Ft.unitSq 𝓕 X = Ft.USqInv 𝓕 X X ∘ Ft.unitPB 𝓕 X :=
  funext fun w => by rw [comp_apply, ← Ft.USq_unitSq 𝓕 X w, Ft.USqInv_USq]

theorem isStrongBundleMap_unitPB :
    X.x.K.BWh.IsStrongBundleMap (Ft.toPullback.pullBundle 𝓕 X.toPU X.toPU) (Ft.unitH 𝓕 X)
      (Ft.unitPB 𝓕 X) :=
  StrongBundle.isStrongBundleMap_pullbackPair (Ft.toPullback.bundleG 𝓕 X.toPU X.toPU)
    (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU X.toPU).isScSmoothMap (l := Ft.unitH 𝓕 X)
    (Ft.isScSmoothMap_unitH 𝓕 X)
    (((Ft.toPullback.isStrongBundleMap_unitG 𝓕 X.toPU).comp X.x.K.isStrongBundleMap_Ξ).congr_base
      (funext fun e => (Ft.pBmap_unitH 𝓕 X e).symm))

/-- **The unit `u : Ŵ → M(Γ̂, Γ̂)` is a strong bundle map covering `û : Ê → M(Ψ̂, Ψ̂)`.** -/
theorem isStrongBundleMap_unitSq :
    X.x.K.BWh.IsStrongBundleMap (Ft.bundleSq 𝓕 X X) (Ft.unitH 𝓕 X) (Ft.unitSq 𝓕 X) := by
  rw [Ft.unitSq_eq 𝓕 X]
  exact (Ft.isStrongBundleIso_USq 𝓕 X X).invMap.comp (Ft.isStrongBundleMap_unitPB 𝓕 X)

/-! #### The multiplication -/

instance instParacompactSpaceProdMHat :
    ParacompactSpace (Ft.toPullback.MHatB 𝓕 Y.toPU Z.toPU × Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) :=
  MPolyfold.paracompactSpace_prod (Ft.toPullback.hatPoly 𝓕 Y.toPU Z.toPU)
    (Ft.toPullback.hatPoly 𝓕 X.toPU Y.toPU)

/-- **The fibred product `M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂')`.** -/
abbrev HFP : Set (Ft.toPullback.MHatB 𝓕 Y.toPU Z.toPU × Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) :=
  MPolyfold.fibredProduct (Ft.srcH 𝓕 Y Z) (Ft.tgtH 𝓕 X Y)

instance instParacompactSpaceHFP : ParacompactSpace (Ft.HFP 𝓕 X Y Z) :=
  ((Ft.toPullback.hatPoly 𝓕 Y.toPU Z.toPU).prod
    (Ft.toPullback.hatPoly 𝓕 X.toPU Y.toPU)).paracompactSpace_subtype _

/-- The M-polyfold structure of `M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂')` (Definition 17.1.8 (c)): a
sub-M-polyfold of the product, `ŝ` being a local sc-diffeomorphism and, under `IsCompatible`,
`t̂` sc-smooth. -/
def HFPpoly (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) : MPolyfold (Ft.HFP 𝓕 X Y Z) :=
  MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct (Ft.isLocalScDiffeo_srcH 𝓕 Y Z)
    (Ft.isLocalScDiffeo_tgtH 𝓕 X Y hC).isScSmoothMap)

/-- `pr₂ : M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂') → M(Ψ̂, Ψ̂')`. -/
abbrev pr₂H (w : Ft.HFP 𝓕 X Y Z) : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU := w.1.2

/-- The top multiplication `m̂ : M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂') → M(Ψ̂, Ψ̂'')` of (19.32). -/
abbrev mulH (w : Ft.HFP 𝓕 X Y Z) : Ft.toPullback.MHatB 𝓕 X.toPU Z.toPU :=
  (Ft.toPullback.toCBC 𝓕).mulHat X.toPU.toHat Y.toPU.toHat Z.toPU.toHat w

theorem isScSmoothMap_pr₂H (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.HFPpoly 𝓕 X Y Z hC).IsScSmoothMap (Ft.toPullback.hatPoly 𝓕 X.toPU Y.toPU)
      (Ft.pr₂H 𝓕 X Y Z) :=
  (MPolyfold.isScSmoothMap_snd _ _).comp (MPolyfold.subPolyfold_inclusion_isScSmooth _)

theorem isScSmoothMap_mulH (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.HFPpoly 𝓕 X Y Z hC).IsScSmoothMap (Ft.toPullback.hatPoly 𝓕 X.toPU Z.toPU)
      (Ft.mulH 𝓕 X Y Z) :=
  (Ft.toPullback.toCBC 𝓕).isScSmoothMap_mulHat S.isFiniteToOneCovering hC X.toPU.toHat
    Y.toPU.toHat Z.toPU.toHat

/-- `p ₛ×ₜ p : M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂') → M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`. -/
def pFP (w : Ft.HFP 𝓕 X Y Z) : Ft.toPullback.BFP 𝓕 X.toPU Y.toPU Z.toPU :=
  ⟨(Ft.toPullback.pBmap 𝓕 Y.toPU Z.toPU w.1.1, Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU w.1.2),
    congrArg Y.toPU.x.Ψh.τ.obj w.2⟩

theorem isScSmoothMap_pFP (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.HFPpoly 𝓕 X Y Z hC).IsScSmoothMap (Ft.toPullback.BFPpoly 𝓕 X.toPU Y.toPU Z.toPU)
      (Ft.pFP 𝓕 X Y Z) :=
  MPolyfold.isScSmoothOn_subPolyfold_of_val _ (MPolyfold.IsScSmoothOn.prodMk
    ((Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 Y.toPU Z.toPU).isScSmoothMap.comp
      ((MPolyfold.isScSmoothMap_fst _ _).comp (MPolyfold.subPolyfold_inclusion_isScSmooth _)))
    ((Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU).isScSmoothMap.comp
      ((MPolyfold.isScSmoothMap_snd _ _).comp (MPolyfold.subPolyfold_inclusion_isScSmooth _))))

/-- The multiplication diagram (19.32): `p ∘ m̂ = m ∘ (p ₛ×ₜ p)`. -/
theorem pBmap_mulH (w : Ft.HFP 𝓕 X Y Z) :
    Ft.toPullback.pBmap 𝓕 X.toPU Z.toPU (Ft.mulH 𝓕 X Y Z w) =
      Ft.toPullback.mulB 𝓕 X.toPU Y.toPU Z.toPU (Ft.pFP 𝓕 X Y Z w) :=
  X.toPU.x.Ψh.transMap_comp Y.toPU.x.Ψh Z.toPU.x.Ψh _ _
    (TransitionSet.mor_composable_of_src_eq_tgt w.2)

instance instParacompactSpaceMulSq :
    ParacompactSpace (pullbackSpace (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z)) := by
  have := (Ft.toPullback.hatPoly 𝓕 Y.toPU Z.toPU).metrizableSpace
  have := (Ft.toPullback.hatPoly 𝓕 X.toPU Y.toPU).metrizableSpace
  have := (Ft.bundleSq 𝓕 X Y).toMPolyfold0.metrizableSpace
  exact paracompactSpace_of_metrizableSpace _

/-- **The strong bundle over `M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂')`** whose total space is
`M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂')` (`fpEquivSq`): the pull-back of `m̂ : M(Γ̂, Γ̂') → M(Ψ̂, Ψ̂')` by
`pr₂`. -/
def mulBundleSq (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    StrongBundle (Ft.HFPpoly 𝓕 X Y Z hC) (pullbackProj (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z)) :=
  (Ft.bundleSq 𝓕 X Y).pullback (Ft.isScSmoothMap_pr₂H 𝓕 X Y Z hC)

/-- `p̂ ₛ×ₜ p̂` on the total spaces: `((a', a), h) ↦ ((p(a'), p(a)), p̂(h))`. -/
def pbarFP : pullbackSpace (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z) →
    pullbackSpace (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pr₂B 𝓕 X.toPU Y.toPU Z.toPU) :=
  pullbackPair (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU) (Ft.toPullback.pr₂B 𝓕 X.toPU Y.toPU Z.toPU)
    (Ft.pFP 𝓕 X Y Z ∘ pullbackProj (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z))
    (Ft.pbarSq 𝓕 X Y ∘ pullbackProj' (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z))
    fun z => (Ft.mGmap_pbarSq 𝓕 X Y _).trans (congrArg (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) z.2)

/-- `p̂ ₛ×ₜ p̂` is a strong bundle map covering `p ₛ×ₜ p`. -/
theorem isStrongBundleMap_pbarFP (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.mulBundleSq 𝓕 X Y Z hC).IsStrongBundleMap
      (Ft.toPullback.mulBundleG 𝓕 X.toPU Y.toPU Z.toPU) (Ft.pFP 𝓕 X Y Z) (Ft.pbarFP 𝓕 X Y Z) :=
  StrongBundle.isStrongBundleMap_pullbackPair (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU)
    (Ft.toPullback.isScSmoothMap_pr₂B 𝓕 X.toPU Y.toPU Z.toPU) (l := Ft.pFP 𝓕 X Y Z)
    (Ft.isScSmoothMap_pFP 𝓕 X Y Z hC)
    ((Ft.isStrongBundleMap_pbarSq 𝓕 X Y).comp
      ((Ft.bundleSq 𝓕 X Y).isStrongBundleMap_pullbackProj' (Ft.isScSmoothMap_pr₂H 𝓕 X Y Z hC)))

/-- `(m̂ ∘ π, m ∘ (p̂ ₛ×ₜ p̂))` into `p*M(Γ, Γ'')`. -/
def mulPB : pullbackSpace (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z) →
    Ft.toPullback.PB 𝓕 X.toPU Z.toPU :=
  pullbackPair (Ft.toPullback.mGmap 𝓕 X.toPU Z.toPU) (Ft.toPullback.pBmap 𝓕 X.toPU Z.toPU)
    (Ft.mulH 𝓕 X Y Z ∘ pullbackProj (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z))
    (Ft.toPullback.mulG 𝓕 X.toPU Y.toPU Z.toPU ∘ Ft.pbarFP 𝓕 X Y Z)
    fun _ => ((Ft.toPullback.isStrongBundleMap_mulG 𝓕 X.toPU Y.toPU Z.toPU).covers _).trans
      (Ft.pBmap_mulH 𝓕 X Y Z _).symm

theorem isStrongBundleMap_mulPB (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.mulBundleSq 𝓕 X Y Z hC).IsStrongBundleMap (Ft.toPullback.pullBundle 𝓕 X.toPU Z.toPU)
      (Ft.mulH 𝓕 X Y Z) (Ft.mulPB 𝓕 X Y Z) :=
  StrongBundle.isStrongBundleMap_pullbackPair (Ft.toPullback.bundleG 𝓕 X.toPU Z.toPU)
    (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Z.toPU).isScSmoothMap (l := Ft.mulH 𝓕 X Y Z)
    (Ft.isScSmoothMap_mulH 𝓕 X Y Z hC)
    (((Ft.toPullback.isStrongBundleMap_mulG 𝓕 X.toPU Y.toPU Z.toPU).comp
      (Ft.isStrongBundleMap_pbarFP 𝓕 X Y Z hC)).congr_base
      (funext fun w => (Ft.pBmap_mulH 𝓕 X Y Z w).symm))

/-- **The multiplication `m : M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂') → M(Γ̂, Γ̂'')`** on the total space of
`mulBundleSq`: `U⁻¹ ∘ (m̂ ∘ π, m ∘ (p̂ ₛ×ₜ p̂))`; under `fpEquivSq` it is the composition
(`mulSq_toFPSq`). -/
def mulSq (w : pullbackSpace (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z)) : Ft.MSq 𝓕 X Z :=
  Ft.USqInv 𝓕 X Z (Ft.mulPB 𝓕 X Y Z w)

/-- **The multiplication `M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂') → M(Γ̂, Γ̂'')` is a strong bundle map
covering `m̂ : M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂') → M(Ψ̂, Ψ̂'')`**, under `IsCompatible`. -/
theorem isStrongBundleMap_mulSq (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.mulBundleSq 𝓕 X Y Z hC).IsStrongBundleMap (Ft.bundleSq 𝓕 X Z) (Ft.mulH 𝓕 X Y Z)
      (Ft.mulSq 𝓕 X Y Z) :=
  (Ft.isStrongBundleIso_USq 𝓕 X Z).invMap.comp (Ft.isStrongBundleMap_mulPB 𝓕 X Y Z hC)

/-- `m ∘ (p̂ ₛ×ₜ p̂) = p̂ ∘ m` (the top face of (19.100)). -/
theorem pbarSq_mulSq (w : pullbackSpace (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z)) :
    Ft.pbarSq 𝓕 X Z (Ft.mulSq 𝓕 X Y Z w) =
      Ft.toPullback.mulG 𝓕 X.toPU Y.toPU Z.toPU (Ft.pbarFP 𝓕 X Y Z w) := by
  have h := congrArg (fun z : Ft.toPullback.PB 𝓕 X.toPU Z.toPU => z.1.2)
    (Ft.USq_USqInv 𝓕 X Z (Ft.mulPB 𝓕 X Y Z w))
  exact h

/-- `m̂ ∘ m = m̂ ∘ (m̂ ₛ×ₜ m̂)` (the left face of (19.100)). -/
theorem mSq_mulSq (w : pullbackSpace (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z)) :
    Ft.mSq 𝓕 X Z (Ft.mulSq 𝓕 X Y Z w) =
      Ft.mulH 𝓕 X Y Z (pullbackProj (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z) w) := by
  have h := congrArg (fun z : Ft.toPullback.PB 𝓕 X.toPU Z.toPU => z.1.1)
    (Ft.USq_USqInv 𝓕 X Z (Ft.mulPB 𝓕 X Y Z w))
  exact h

/-! #### The fibred product `M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂')` -/

/-- **The fibred product `M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂')`** of (19.100): pairs `(h', h)` with
`s(h') = t(h)`. -/
abbrev FPSq : Type u :=
  {q : Ft.MSq 𝓕 Y Z × Ft.MSq 𝓕 X Y // q.1.toTrans.src = q.2.toTrans.tgt}

/-- `U⁻¹(z) = h` as soon as `z = U(h)` componentwise. -/
theorem USqInv_eq_of (z : Ft.toPullback.PB 𝓕 X.toPU Y.toPU) (h : Ft.MSq 𝓕 X Y)
    (h₁ : z.1.1 = Ft.mSq 𝓕 X Y h) (h₂ : z.1.2 = Ft.pbarSq 𝓕 X Y h) : Ft.USqInv 𝓕 X Y z = h := by
  rw [show z = Ft.USq 𝓕 X Y h from Subtype.ext (Prod.ext h₁ h₂), Ft.USqInv_USq]

/-- `(h', h) ↦ ((m̂(h'), m̂(h)), h)`. -/
def toFPSq (q : Ft.FPSq 𝓕 X Y Z) : pullbackSpace (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z) :=
  ⟨(⟨(Ft.mSq 𝓕 Y Z q.1.1, Ft.mSq 𝓕 X Y q.1.2), congrArg Y.x.K.Qh q.2⟩, q.1.2), rfl⟩

theorem mulLiftG_pbarFP_toFPSq (q : Ft.FPSq 𝓕 X Y Z) :
    Ft.toPullback.mulLiftG 𝓕 X.toPU Y.toPU Z.toPU (Ft.pbarFP 𝓕 X Y Z (Ft.toFPSq 𝓕 X Y Z q)) =
      Ft.pbarSq 𝓕 Y Z q.1.1 :=
  Y.toPU.x.str.eq_of_proj Z.toPU.x.str (congrArg Y.x.K.Ξ q.2).symm
    ((Y.toPU.x.str.proj_lift Z.toPU.x.str _ _ _).trans (Ft.mGmap_pbarSq 𝓕 Y Z q.1.1).symm)

/-- `((a', a), h) ↦ (h', h)` with `h'` the element over `a'` with `s(h') = t(h)`. -/
def ofFPSq (w : pullbackSpace (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z)) : Ft.FPSq 𝓕 X Y Z :=
  ⟨(Ft.USqInv 𝓕 Y Z ⟨(w.1.1.1.1, Ft.toPullback.mulLiftG 𝓕 X.toPU Y.toPU Z.toPU
      (Ft.pbarFP 𝓕 X Y Z w)), Y.toPU.x.str.proj_lift Z.toPU.x.str _ _ _⟩, w.1.2),
    Y.x.K.liftPt_eq _ ((congrArg (Ft.tgtH 𝓕 X Y) w.2).trans w.1.1.2.symm) rfl⟩

theorem ofFPSq_toFPSq (q : Ft.FPSq 𝓕 X Y Z) : Ft.ofFPSq 𝓕 X Y Z (Ft.toFPSq 𝓕 X Y Z q) = q :=
  Subtype.ext (Prod.ext (Ft.USqInv_eq_of 𝓕 Y Z _ q.1.1 rfl (Ft.mulLiftG_pbarFP_toFPSq 𝓕 X Y Z q))
    rfl)

theorem toFPSq_ofFPSq (w : pullbackSpace (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z)) :
    Ft.toFPSq 𝓕 X Y Z (Ft.ofFPSq 𝓕 X Y Z w) = w :=
  Subtype.ext (Prod.ext (Subtype.ext (Prod.ext
    (congrArg (fun z : Ft.toPullback.PB 𝓕 Y.toPU Z.toPU => z.1.1) (Ft.USq_USqInv 𝓕 Y Z _))
    w.2)) rfl)

/-- **`M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂')` is the total space of `mulBundleSq`.** -/
def fpEquivSq : Ft.FPSq 𝓕 X Y Z ≃ pullbackSpace (Ft.mSq 𝓕 X Y) (Ft.pr₂H 𝓕 X Y Z) where
  toFun := Ft.toFPSq 𝓕 X Y Z
  invFun := Ft.ofFPSq 𝓕 X Y Z
  left_inv := Ft.ofFPSq_toFPSq 𝓕 X Y Z
  right_inv := Ft.toFPSq_ofFPSq 𝓕 X Y Z

/-- **Under `fpEquivSq`, `mulSq` is the composition**: `mulSq((m̂(h'), m̂(h)), h) = h' ∘ h`. -/
theorem mulSq_toFPSq (q : Ft.FPSq 𝓕 X Y Z) :
    Ft.mulSq 𝓕 X Y Z (Ft.toFPSq 𝓕 X Y Z q) = (TransitionSet.comp q.1.1.toTrans q.1.2.toTrans
      (TransitionSet.mor_composable_of_src_eq_tgt q.2) : Ft.MSq 𝓕 X Z) := by
  have hl := Ft.mulLiftG_pbarFP_toFPSq 𝓕 X Y Z q
  exact Ft.USqInv_eq_of 𝓕 X Z _ _
    (TransitionSet.ext rfl (S.μA.cat_comp_fst (TransitionSet.mor_composable_of_src_eq_tgt q.2)).symm
      rfl)
    (TransitionSet.ext rfl
      ((congrArg (fun g : Y.toPU.x.TransG Z.toPU.x =>
          S.μB.cat.toGroupoidStr.comp g.mor (Ft.pbarSq 𝓕 X Y q.1.2).mor) hl).trans
        (S.Phat.mor_comp _ _ (TransitionSet.mor_composable_of_src_eq_tgt q.2)).symm)
      (congrArg (fun g : Y.toPU.x.TransG Z.toPU.x => g.tgt) hl))

/-! #### Theorem 19.8.22: the structure maps -/

/-- **2021 Theorem 19.8.22, p. 956, the inversion (diagram (19.98))**, for coherent `𝓕` under
`IsCompatible` (an added hypothesis, the reading of l. 44572): `ι : M(Γ̂, Γ̂') → M(Γ̂', Γ̂)` and
`ι : M(Γ, Γ') → M(Γ', Γ)` are strong bundle isomorphisms covering `ι̂` and `ι`, they commute with
the vertical maps `m̂` and the horizontal maps `p̂`, `p`, and both squares are proper strong bundle
covering squares. -/
theorem theorem_19_8_22_inv_hyp (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.bundleSq 𝓕 X Y).IsStrongBundleIso (Ft.bundleSq 𝓕 Y X) (Ft.invH 𝓕 X Y) (Ft.invSq 𝓕 X Y)
      (Ft.invH 𝓕 Y X) (Ft.invSq 𝓕 Y X) ∧
    (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU).IsStrongBundleIso
      (Ft.toPullback.bundleG 𝓕 Y.toPU X.toPU) (Ft.toPullback.invB 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.invG 𝓕 X.toPU Y.toPU) (Ft.toPullback.invB 𝓕 Y.toPU X.toPU)
      (Ft.toPullback.invG 𝓕 Y.toPU X.toPU) ∧
    (∀ h, Ft.mSq 𝓕 Y X (Ft.invSq 𝓕 X Y h) = Ft.invH 𝓕 X Y (Ft.mSq 𝓕 X Y h)) ∧
    (∀ h, Ft.pbarSq 𝓕 Y X (Ft.invSq 𝓕 X Y h) =
      Ft.toPullback.invG 𝓕 X.toPU Y.toPU (Ft.pbarSq 𝓕 X Y h)) ∧
    (∀ a, Ft.toPullback.pBmap 𝓕 Y.toPU X.toPU (Ft.invH 𝓕 X Y a) =
      Ft.toPullback.invB 𝓕 X.toPU Y.toPU (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU a)) ∧
    IsProperStrongBundleCoveringSquare (Ft.bundleSq 𝓕 X Y) (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) (Ft.pbarSq 𝓕 X Y) ∧
    IsProperStrongBundleCoveringSquare (Ft.bundleSq 𝓕 Y X) (Ft.toPullback.bundleG 𝓕 Y.toPU X.toPU)
      (Ft.toPullback.pBmap 𝓕 Y.toPU X.toPU) (Ft.pbarSq 𝓕 Y X) :=
  ⟨Ft.isStrongBundleIso_invSq 𝓕 X Y hcoh hC,
    Ft.toPullback.isStrongBundleIso_invG 𝓕 X.toPU Y.toPU hcoh, Ft.mSq_invSq 𝓕 X Y,
    Ft.pbarSq_invSq 𝓕 X Y, Ft.pBmap_invH 𝓕 X Y, Ft.isProperSquare_pbarSq 𝓕 X Y,
    Ft.isProperSquare_pbarSq 𝓕 Y X⟩

/-- **2021 Theorem 19.8.22, p. 956, the unit (diagram (19.99))**: `u : Ŵ → M(Γ̂, Γ̂)` and
`u : W → M(Γ, Γ)` are strong bundle maps covering `û` and `u`, they commute with the vertical maps
and the horizontal maps `Ξ`, `p̂`, `τ̂`, `p`, and both squares are proper strong bundle covering
squares. -/
theorem theorem_19_8_22_unit :
    X.x.K.BWh.IsStrongBundleMap (Ft.bundleSq 𝓕 X X) (Ft.unitH 𝓕 X) (Ft.unitSq 𝓕 X) ∧
    X.toPU.x.bun.bundle.IsStrongBundleMap (Ft.toPullback.bundleG 𝓕 X.toPU X.toPU)
      (Ft.toPullback.unitB 𝓕 X.toPU) (Ft.toPullback.unitG 𝓕 X.toPU) ∧
    (∀ w, Ft.mSq 𝓕 X X (Ft.unitSq 𝓕 X w) = Ft.unitH 𝓕 X (X.x.K.Qh w)) ∧
    (∀ w, Ft.pbarSq 𝓕 X X (Ft.unitSq 𝓕 X w) = Ft.toPullback.unitG 𝓕 X.toPU (X.x.K.Ξ w)) ∧
    (∀ e, Ft.toPullback.pBmap 𝓕 X.toPU X.toPU (Ft.unitH 𝓕 X e) =
      Ft.toPullback.unitB 𝓕 X.toPU (X.x.Ψh.τ.obj e)) ∧
    IsProperStrongBundleCoveringSquare X.x.K.BWh X.x.K.BW X.x.Ψh.τ.obj X.x.K.Ξ ∧
    IsProperStrongBundleCoveringSquare (Ft.bundleSq 𝓕 X X) (Ft.toPullback.bundleG 𝓕 X.toPU X.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU X.toPU) (Ft.pbarSq 𝓕 X X) :=
  ⟨Ft.isStrongBundleMap_unitSq 𝓕 X, Ft.toPullback.isStrongBundleMap_unitG 𝓕 X.toPU,
    Ft.mSq_unitSq 𝓕 X, Ft.pbarSq_unitSq 𝓕 X, Ft.pBmap_unitH 𝓕 X, X.x.K.isProperSquare,
    Ft.isProperSquare_pbarSq 𝓕 X X⟩

/-- **The multiplication maps of 2021 Theorem 19.8.22 (diagram (19.100)) and the faces**, under
`IsCompatible` (an added hypothesis, the reading of l. 44572), without the properness of the
squares (the full multiplication statement is `theorem_19_8_22_mul_hyp`,
`CoveringSquareFibredProper.lean`): with `M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂')` and `M(Γ', Γ'') ₛ×ₜ M(Γ, Γ')`
the pull-backs of `m̂`, `m` by `pr₂` (`fpEquivSq`, `fpEquivG`), the multiplications are strong
bundle maps covering `m̂` and `m`, `p̂ ₛ×ₜ p̂` is a strong bundle map covering `p ₛ×ₜ p`, the faces
of (19.100) commute, and the multiplications are the composition `(h', h) ↦ h' ∘ h`. -/
theorem isStrongBundleMap_mul_and_faces (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.mulBundleSq 𝓕 X Y Z hC).IsStrongBundleMap (Ft.bundleSq 𝓕 X Z) (Ft.mulH 𝓕 X Y Z)
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
        (TransitionSet.mor_composable_of_src_eq_tgt q.2) : X.toPU.x.TransG Z.toPU.x) :=
  ⟨Ft.isStrongBundleMap_mulSq 𝓕 X Y Z hC,
    Ft.toPullback.isStrongBundleMap_mulG 𝓕 X.toPU Y.toPU Z.toPU,
    Ft.isStrongBundleMap_pbarFP 𝓕 X Y Z hC, Ft.mSq_mulSq 𝓕 X Y Z, Ft.pbarSq_mulSq 𝓕 X Y Z,
    Ft.pBmap_mulH 𝓕 X Y Z, Ft.mulSq_toFPSq 𝓕 X Y Z,
    Ft.toPullback.mulG_toFPG 𝓕 X.toPU Y.toPU Z.toPU⟩

end SquareUniformizerConstruction

/-! ### Remark 19.6.2: the zero sections -/

namespace SquareUniformizer

variable {S : BundleCoveringSquare A B} {β : B.Obj} (x : SquareUniformizer S β)

/-- **2021 Remark 19.6.2, p. 892**, for the strong bundle uniformizers `Γ̂ : Ŵ → E_A` over the
ep-groupoid `Ê` and `Γ : W → E_B` of a member of `F̃` (Definition 19.8.10 (2), (3)): being a
topological linear isomorphism on the fibres, `Γ̂` maps `0_ê` to `(Ψ̂(ê), 0)` and `Γ` maps `0_o`
to `(Ψ(o), 0)`; in particular a distinguished point mapped to `α` has `Γ̂(0_ê) = (α, 0_{μ(α)})`. -/
theorem remark_19_6_2 :
    (∀ e, x.Γh.obj (fiberZero x.K.Qh e) = S.μA.zero (x.Ψh.hat.obj e)) ∧
      ∀ o, x.Γ.obj (fiberZero x.K.Q o) = S.μB.zero (x.Ψh.Ψ.obj o) :=
  ⟨fun e => by
    change x.Γh.obj ((0 : x.K.Qh ⁻¹' {e}) : x.K.Wh) = _
    rw [← x.fiberCLEh_apply e 0, map_zero]; rfl,
  fun o => by
    change x.Γ.obj ((0 : x.K.Q ⁻¹' {o}) : x.K.W) = _
    rw [← x.fiberCLE_apply o 0, map_zero]; rfl⟩

end SquareUniformizer

end GroupoidalCategory

end

end Polyfold
