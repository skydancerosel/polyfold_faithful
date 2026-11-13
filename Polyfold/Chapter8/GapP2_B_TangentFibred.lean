import Polyfold.Chapter8.TangentEp
import Polyfold.Chapter7.Discrete

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §8.1, p. 359
(2017 p. 258): the identification `T(𝐗 ₛ×ₜ 𝐗) = T𝐗 _{Ts}×_{Tt} T𝐗` before **Lemma 8.1.2**
(2017: Lemma 8.1), and the lemma as printed, `(ψ, k) ∘ (φ, h) = Tm(ψ, φ)(k, h)` (gap G.75).

# The tangent of the fibred product, and `m_{T𝐗} = Tm`

## The text, paraphrased

(p. 359) `𝐗 ₛ×ₜ 𝐗` is a sub-M-polyfold of `𝐗 × 𝐗`; its tangent is identified with the
sub-M-polyfold `T𝐗 _{Ts}×_{Tt} T𝐗` of `T𝐗 × T𝐗`, so that `((ψ, k), (φ, h))` belongs to it iff
`Ts(ψ)(k) = Tt(φ)(h)`.  (Lemma 8.1.2) With this identification the multiplication (8.5) of `T𝐗` is
`Tm`, the tangent of the multiplication `m : 𝐗 ₛ×ₜ 𝐗 → 𝐗`.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* `CompPairs X` (the set `𝐗 ₛ×ₜ 𝐗` as a type), `compPolyfold` (its M-polyfold structure, the
  sub-M-polyfold of Definition 7.1.3 (4)), the projections `compFst`, `compSnd` (sc-smooth;
  `compSnd` is a local sc-diffeomorphism, `isLocalScDiffeo_compSnd`) and the multiplication
  `compMul` (sc-smooth: this is condition (4)).
* `tangentCompPairs : T(𝐗 ₛ×ₜ 𝐗) → T𝐗 × T𝐗`, `v ↦ (Tπ₁ v, Tπ₂ v)`: the identification.
  `tangentCompPairs_injective`, `range_tangentCompPairs` (**its range is
  `{(k, h) | Ts k = Tt h}`**), and `tangentCompPairsEquiv`, the bijection onto the fibred product
  of the tangent ep-groupoid `T(X, 𝐗)`.
* **`isScDiffeoOn_tangentCompPairs`**: this bijection is an sc-diffeomorphism from the M-polyfold
  `T(𝐗 ₛ×ₜ 𝐗)` onto the sub-M-polyfold `T𝐗 _{Ts}×_{Tt} T𝐗` of `T𝐗 × T𝐗`.
* **`lemma_8_1_2_tangentMul`**: `Tm(v) = Tπ₁(v) ∘ Tπ₂(v)` (the composition (8.5), `tComp`), and
  **`lemma_8_1_2_book`**: for `Ts(k) = Tt(h)` there is exactly one `v ∈ T(𝐗 ₛ×ₜ 𝐗)` over `(k, h)`,
  and `k ∘ h = Tm(v)`, with base point `p(k) ∘ p(h)` and `Ts(k ∘ h) = Ts(h)`.

## The proof

`π₂ : 𝐗 ₛ×ₜ 𝐗 → 𝐗` is a local sc-diffeomorphism (`s` is one), so `Tπ₂` is bijective on the
fibres; a vector of `T(𝐗 ₛ×ₜ 𝐗)` is determined by its base point and `Tπ₂`.  `Tπ₁(v)` is the
vector over `π₁` with `Ts(Tπ₁ v) = Tt(Tπ₂ v)` (chain rule for `s ∘ π₁ = t ∘ π₂`).  `Tm(v)` lies
over `m` and `Ts(Tm v) = Ts(Tπ₂ v)` (chain rule for `s ∘ m = s ∘ π₂`), which characterizes the
composition (8.5).  The sc-diffeomorphism: the identification commutes with the local
sc-diffeomorphisms `Tπ₂` and `π₂` of `T𝐗 _{Ts}×_{Tt} T𝐗` (`isLocalScDiffeo_of_comp_eq`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v w

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-- A continuous map `Θ` over a common base, `b ∘ Θ = a` with `a`, `b` local sc-diffeomorphisms,
is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_of_comp_eq {a : X → Z} {b : Y → Z} {Θ : X → Y}
    (ha : P.IsLocalScDiffeo S a) (hb : Q.IsLocalScDiffeo S b) (hΘ : Continuous Θ)
    (hab : ∀ x, b (Θ x) = a x) : P.IsLocalScDiffeo Q Θ := by
  intro x
  obtain ⟨U, V, g, hxU, hd⟩ := ha x
  obtain ⟨U', V', g', hxU', hd'⟩ := hb (Θ x)
  have hOo : IsOpen (U ∩ Θ ⁻¹' U') :=
    hd.isScSmoothOn.isOpen.inter (hd'.isScSmoothOn.isOpen.preimage hΘ)
  have hVo : IsOpen (V ∩ g ⁻¹' (U ∩ Θ ⁻¹' U')) :=
    hd.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hd.isScSmoothOn_inv.isOpen hOo
  have hWo : IsOpen (U' ∩ b ⁻¹' (V ∩ g ⁻¹' (U ∩ Θ ⁻¹' U'))) :=
    hd'.isScSmoothOn.continuousOn.isOpen_inter_preimage hd'.isScSmoothOn.isOpen hVo
  refine ⟨U ∩ Θ ⁻¹' U', U' ∩ b ⁻¹' (V ∩ g ⁻¹' (U ∩ Θ ⁻¹' U')), g ∘ b, ⟨hxU, hxU'⟩, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · refine ((hd'.isScSmoothOn_inv.comp (hd.isScSmoothOn.mono hOo inter_subset_left)
      fun y hy => by rw [← hab y]; exact hd'.mapsTo hy.2).congr fun y hy => ?_)
    change g' (a y) = Θ y
    rw [← hab y, hd'.left_inv _ hy.2]
  · exact (hd.isScSmoothOn_inv.mono hVo inter_subset_left).comp
      (hd'.isScSmoothOn.mono hWo inter_subset_left) fun w hw => hw.2
  · intro y hy
    refine ⟨hy.2, ?_, ?_⟩
    · rw [hab]; exact hd.mapsTo hy.1
    · rw [mem_preimage, hab, hd.left_inv _ hy.1]; exact hy
  · exact fun w hw => hw.2.2
  · intro y hy
    change g (b (Θ y)) = y
    rw [hab, hd.left_inv _ hy.1]
  · intro w hw
    have hy : g (b w) ∈ U ∩ Θ ⁻¹' U' := hw.2.2
    have h1 : b (Θ (g (b w))) = b w := by rw [hab, hd.right_inv _ hw.2.1]
    have h2 := congrArg g' h1
    rwa [hd'.left_inv _ hy.2, hd'.left_inv _ hw.1] at h2

/-- A bijective local sc-diffeomorphism is an sc-diffeomorphism. -/
theorem IsLocalScDiffeo.isScDiffeoOn_of_bijective {f : X → Y} (hf : P.IsLocalScDiffeo Q f)
    (e : X ≃ Y) (he : ∀ x, e x = f x) : P.IsScDiffeoOn Q f e.symm univ univ := by
  refine ⟨hf.isScSmoothMap, ?_, mapsTo_univ _ _, mapsTo_univ _ _, fun x _ => ?_, fun y _ => ?_⟩
  · refine IsScSmoothOn.of_locally isOpen_univ fun y _ => ?_
    obtain ⟨U, V, g, hxU, hd⟩ := hf (e.symm y)
    have hyV : y ∈ V := by
      have := hd.mapsTo hxU
      rwa [← he, e.apply_symm_apply] at this
    refine ⟨V, hd.isScSmoothOn_inv.isOpen, hyV, subset_univ _, hd.isScSmoothOn_inv.congr
      fun z hz => ?_⟩
    apply e.injective
    rw [e.apply_symm_apply, he, hd.right_inv z hz]
  · rw [← he, e.symm_apply_apply]
  · rw [← he, e.apply_symm_apply]

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### The M-polyfold `𝐗 ₛ×ₜ 𝐗` -/

/-- The fibred product `𝐗 ₛ×ₜ 𝐗 = {(ψ, φ) | s(ψ) = t(φ)}`, as a type. -/
def CompPairs : Type u := ↥(MPolyfold.fibredProduct X.src X.tgt)

instance : TopologicalSpace X.CompPairs :=
  inferInstanceAs (TopologicalSpace ↥(MPolyfold.fibredProduct X.src X.tgt))

instance : T2Space X.CompPairs :=
  inferInstanceAs (T2Space ↥(MPolyfold.fibredProduct X.src X.tgt))

include X in
theorem paracompactSpace_morProd : ParacompactSpace (Mor × Mor) :=
  MPolyfold.paracompactSpace_prod X.PMor X.PMor

theorem paracompactSpace_fibredProduct :
    ParacompactSpace ↥(MPolyfold.fibredProduct X.src X.tgt) :=
  letI := X.paracompactSpace_morProd
  (X.PMor.prod X.PMor).paracompactSpace_subtype (MPolyfold.fibredProduct X.src X.tgt)

instance : ParacompactSpace X.CompPairs := X.paracompactSpace_fibredProduct

/-- The M-polyfold `𝐗 ₛ×ₜ 𝐗`, a sub-M-polyfold of `𝐗 × 𝐗` (the one of Definition 7.1.3 (4)). -/
def compPolyfold : MPolyfold X.CompPairs :=
  letI := X.paracompactSpace_morProd
  letI := X.paracompactSpace_fibredProduct
  MPolyfold.subPolyfold
    (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src X.isScSmoothMap_tgt)

/-- `π₁(ψ, φ) = ψ`. -/
def compFst (a : X.CompPairs) : Mor := a.1.1

/-- `π₂(ψ, φ) = φ`. -/
def compSnd (a : X.CompPairs) : Mor := a.1.2

/-- The multiplication `m(ψ, φ) = ψ ∘ φ` on `𝐗 ₛ×ₜ 𝐗`. -/
def compMul (a : X.CompPairs) : Mor := X.comp a.1.1 a.1.2

theorem src_compFst (a : X.CompPairs) : X.src (X.compFst a) = X.tgt (X.compSnd a) := a.2

theorem compPairs_ext {a b : X.CompPairs} (h1 : X.compFst a = X.compFst b)
    (h2 : X.compSnd a = X.compSnd b) : a = b := Subtype.ext (Prod.ext h1 h2)

/-- Definition 7.1.3 (4): `m` is sc-smooth on `𝐗 ₛ×ₜ 𝐗`. -/
theorem isScSmoothMap_compMul : X.compPolyfold.IsScSmoothMap X.PMor X.compMul :=
  X.isScSmoothComp

theorem isScSmoothMap_compFst : X.compPolyfold.IsScSmoothMap X.PMor X.compFst :=
  letI := X.paracompactSpace_morProd
  letI := X.paracompactSpace_fibredProduct
  (MPolyfold.isScSmoothMap_fst (P := X.PMor) (Q := X.PMor)).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth
      (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src X.isScSmoothMap_tgt))

/-- `π₂ : 𝐗 ₛ×ₜ 𝐗 → 𝐗` is a local sc-diffeomorphism (since `s` is one). -/
theorem isLocalScDiffeo_compSnd : X.compPolyfold.IsLocalScDiffeo X.PMor X.compSnd := by
  let _ := X.paracompactSpace_morProd
  let _ := X.paracompactSpace_fibredProduct
  intro a
  obtain ⟨W, V, σ, haW, hd⟩ := X.isLocalScDiffeo_src a.1.1
  refine ⟨_, _, _, ?_, MPolyfold.isScDiffeoOn_snd_fibredProduct
    (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src X.isScSmoothMap_tgt) hd
    X.isScSmoothMap_tgt a⟩
  refine ⟨haW, ?_⟩
  change X.tgt a.1.2 ∈ V
  rw [← show X.src a.1.1 = X.tgt a.1.2 from a.2]
  exact hd.mapsTo haW

theorem isScSmoothMap_compSnd : X.compPolyfold.IsScSmoothMap X.PMor X.compSnd :=
  X.isLocalScDiffeo_compSnd.isScSmoothMap

/-! ### The identification `T(𝐗 ₛ×ₜ 𝐗) = T𝐗 _{Ts}×_{Tt} T𝐗` -/

/-- `Tπ₁ : T(𝐗 ₛ×ₜ 𝐗) → T𝐗`. -/
def tCompFst : X.compPolyfold.TangentSpace → X.PMor.TangentSpace :=
  MPolyfold.tangentMap X.isScSmoothMap_compFst

/-- `Tπ₂ : T(𝐗 ₛ×ₜ 𝐗) → T𝐗`. -/
def tCompSnd : X.compPolyfold.TangentSpace → X.PMor.TangentSpace :=
  MPolyfold.tangentMap X.isScSmoothMap_compSnd

/-- `Tm : T(𝐗 ₛ×ₜ 𝐗) → T𝐗`, the tangent of the multiplication. -/
def tCompMul : X.compPolyfold.TangentSpace → X.PMor.TangentSpace :=
  MPolyfold.tangentMap X.isScSmoothMap_compMul

/-- The base point of a tangent vector of `𝐗 ₛ×ₜ 𝐗`. -/
def tCompBase (v : X.compPolyfold.TangentSpace) : X.CompPairs :=
  X.compPolyfold.levelVal 1 (X.compPolyfold.tangentProj v)

theorem tBase_tCompFst (v : X.compPolyfold.TangentSpace) :
    X.tBase (X.tCompFst v) = X.compFst (X.tCompBase v) :=
  MPolyfold.levelVal_tangentProj_tangentMap _ v

theorem tBase_tCompSnd (v : X.compPolyfold.TangentSpace) :
    X.tBase (X.tCompSnd v) = X.compSnd (X.tCompBase v) :=
  MPolyfold.levelVal_tangentProj_tangentMap _ v

theorem tBase_tCompMul (v : X.compPolyfold.TangentSpace) :
    X.tBase (X.tCompMul v) = X.compMul (X.tCompBase v) :=
  MPolyfold.levelVal_tangentProj_tangentMap _ v

/-- `Ts(Tπ₁ v) = Tt(Tπ₂ v)`: the chain rule for `s ∘ π₁ = t ∘ π₂`. -/
theorem tSrc_tCompFst (v : X.compPolyfold.TangentSpace) :
    X.tSrc (X.tCompFst v) = X.tTgt (X.tCompSnd v) :=
  MPolyfold.tangentMap_tangentMap_comm X.isScSmoothMap_src X.isScSmoothMap_compFst
    X.isScSmoothMap_tgt X.isScSmoothMap_compSnd (funext fun a => X.src_compFst a) v

/-- `Ts(Tm v) = Ts(Tπ₂ v)`: the chain rule for `s ∘ m = s ∘ π₂`. -/
theorem tSrc_tCompMul (v : X.compPolyfold.TangentSpace) :
    X.tSrc (X.tCompMul v) = X.tSrc (X.tCompSnd v) :=
  MPolyfold.tangentMap_tangentMap_comm X.isScSmoothMap_src X.isScSmoothMap_compMul
    X.isScSmoothMap_src X.isScSmoothMap_compSnd
    (funext fun a => X.src_comp _ _ (X.src_compFst a)) v

/-- A tangent vector of `𝐗 ₛ×ₜ 𝐗` is determined by its base point and `Tπ₂`. -/
theorem tangentCompPairs_ext {v w : X.compPolyfold.TangentSpace}
    (hb : X.tCompBase v = X.tCompBase w) (h2 : X.tCompSnd v = X.tCompSnd w) : v = w := by
  have hp : X.compPolyfold.tangentProj v = X.compPolyfold.tangentProj w := MPolyfold.level_ext hb
  exact X.isLocalScDiffeo_compSnd.injOn_tangentFiber (X.compPolyfold.tangentProj v) rfl hp.symm h2

/-- **The identification `T(𝐗 ₛ×ₜ 𝐗) → T𝐗 × T𝐗`** of 2021 p. 359: `v ↦ (Tπ₁ v, Tπ₂ v)`. -/
def tangentCompPairs (v : X.compPolyfold.TangentSpace) :
    X.PMor.TangentSpace × X.PMor.TangentSpace := (X.tCompFst v, X.tCompSnd v)

theorem tangentCompPairs_injective : Injective X.tangentCompPairs := fun v w h => by
  have h1 : X.tCompFst v = X.tCompFst w := congrArg Prod.fst h
  have h2 : X.tCompSnd v = X.tCompSnd w := congrArg Prod.snd h
  refine X.tangentCompPairs_ext (X.compPairs_ext ?_ ?_) h2
  · rw [← tBase_tCompFst, h1, tBase_tCompFst]
  · rw [← tBase_tCompSnd, h2, tBase_tCompSnd]

/-- A pair of composable morphisms on level `1` is a point of level `1` of `𝐗 ₛ×ₜ 𝐗`. -/
theorem mem_levelSet_compPolyfold {a : X.CompPairs} (m : ℕ) :
    a ∈ X.compPolyfold.levelSet m ↔ X.compSnd a ∈ X.PMor.levelSet m := by
  obtain ⟨W, V, σ, haW, hd⟩ := X.isLocalScDiffeo_compSnd a
  refine ⟨fun h => hd.isScSmoothOn.mapsTo_levelSet m ⟨haW, h⟩, fun h => ?_⟩
  have := hd.isScSmoothOn_inv.mapsTo_levelSet m ⟨hd.mapsTo haW, h⟩
  rwa [hd.left_inv a haW] at this

/-- **`T(𝐗 ₛ×ₜ 𝐗) = T𝐗 _{Ts}×_{Tt} T𝐗`** (2021 p. 359): every pair `(k, h)` with
`Ts(k) = Tt(h)` is `(Tπ₁ v, Tπ₂ v)` for a tangent vector `v` of `𝐗 ₛ×ₜ 𝐗`. -/
theorem exists_tangentCompPairs_eq {k h : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h) :
    ∃ v, X.tangentCompPairs v = (k, h) := by
  let a : X.CompPairs := ⟨(X.tBase k, X.tBase h), X.src_tBase_eq hkh⟩
  have ha : a ∈ X.compPolyfold.levelSet 1 :=
    (X.mem_levelSet_compPolyfold 1).2 (X.tBase_mem_levelSet h)
  obtain ⟨v, hv, hvh⟩ := X.isLocalScDiffeo_compSnd.tangentFiber_subset_image
    (X.compPolyfold.levelMk 1 a ha) (X.PMor.tangentProj h)
    (by rw [MPolyfold.levelVal_levelMk]; rfl) (show h ∈ X.PMor.tangentFiber _ from rfl)
  have hvb : X.tCompBase v = a := by
    rw [tCompBase, show X.compPolyfold.tangentProj v = _ from hv, MPolyfold.levelVal_levelMk]
  have hvh' : X.tCompSnd v = h := hvh
  refine ⟨v, Prod.ext (X.tangent_ext ?_ ?_) hvh'⟩
  · change X.tBase (X.tCompFst v) = X.tBase k
    rw [tBase_tCompFst, hvb]; rfl
  · change X.tSrc (X.tCompFst v) = X.tSrc k
    rw [tSrc_tCompFst, hvh', hkh]

/-- **The range of the identification is `T𝐗 _{Ts}×_{Tt} T𝐗`** (2021 p. 359). -/
theorem range_tangentCompPairs :
    range X.tangentCompPairs = MPolyfold.fibredProduct X.tSrc X.tTgt := by
  ext ⟨k, h⟩
  constructor
  · rintro ⟨v, hv⟩
    have h1 : X.tCompFst v = k := congrArg Prod.fst hv
    have h2 : X.tCompSnd v = h := congrArg Prod.snd hv
    change X.tSrc k = X.tTgt h
    rw [← h1, ← h2, tSrc_tCompFst]
  · exact fun hkh => X.exists_tangentCompPairs_eq hkh

/-! ### Lemma 8.1.2 as printed -/

/-- **2021 Lemma 8.1.2, p. 359 (2017: Lemma 8.1)**: `Tm(v) = Tπ₁(v) ∘ Tπ₂(v)`, the composition
(8.5) of `T𝐗`, for every tangent vector `v` of `𝐗 ₛ×ₜ 𝐗`: the multiplication of `T𝐗` is `Tm`
under the identification `tangentCompPairs`. -/
theorem lemma_8_1_2_tangentMul (v : X.compPolyfold.TangentSpace) :
    X.tCompMul v = X.tComp (X.tCompFst v) (X.tCompSnd v) :=
  (X.tComp_eq (X.tSrc_tCompFst v)
    (by rw [tBase_tCompMul, tBase_tCompFst, tBase_tCompSnd]; rfl) (X.tSrc_tCompMul v)).symm

/-- **2021 Lemma 8.1.2, p. 359 (2017: Lemma 8.1), as printed**: for `(ψ, k)`, `(φ, h)` in `T𝐗`
with `Ts(ψ)(k) = Tt(φ)(h)` there is exactly one tangent vector `v` of `𝐗 ₛ×ₜ 𝐗` identified with
`((ψ, k), (φ, h))`, and `(ψ, k) ∘ (φ, h) = Tm(v)`; it lies over `ψ ∘ φ` and
`Ts(ψ ∘ φ)(k ∘ h) = Ts(φ)(h)`. -/
theorem lemma_8_1_2_book {k h : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h) :
    (∃! v, X.tangentCompPairs v = (k, h)) ∧
      (∀ v, X.tangentCompPairs v = (k, h) → X.tComp k h = X.tCompMul v) ∧
      X.tBase (X.tComp k h) = X.comp (X.tBase k) (X.tBase h) ∧
      X.tSrc (X.tComp k h) = X.tSrc h := by
  refine ⟨?_, fun v hv => ?_, X.tBase_tComp hkh, X.tSrc_tComp hkh⟩
  · obtain ⟨v, hv⟩ := X.exists_tangentCompPairs_eq hkh
    exact ⟨v, hv, fun w hw => X.tangentCompPairs_injective (hw.trans hv.symm)⟩
  · have h1 : X.tCompFst v = k := congrArg Prod.fst hv
    have h2 : X.tCompSnd v = h := congrArg Prod.snd hv
    rw [lemma_8_1_2_tangentMul, h1, h2]

/-! ### The identification is an sc-diffeomorphism -/

/-- The identification, with values in the fibred product `T𝐗 _{Ts}×_{Tt} T𝐗` of the tangent
ep-groupoid `T(X, 𝐗)` (Theorem 8.1.1). -/
def tangentCompPairsInto (v : X.compPolyfold.TangentSpace) : X.tangentEpGroupoid.CompPairs :=
  ⟨X.tangentCompPairs v, X.tSrc_tCompFst v⟩

theorem compSnd_tangentCompPairsInto (v : X.compPolyfold.TangentSpace) :
    X.tangentEpGroupoid.compSnd (X.tangentCompPairsInto v) = X.tCompSnd v := rfl

theorem compFst_tangentCompPairsInto (v : X.compPolyfold.TangentSpace) :
    X.tangentEpGroupoid.compFst (X.tangentCompPairsInto v) = X.tCompFst v := rfl

theorem bijective_tangentCompPairsInto : Bijective X.tangentCompPairsInto := by
  refine ⟨fun v w h => X.tangentCompPairs_injective (congrArg Subtype.val h), fun b => ?_⟩
  obtain ⟨v, hv⟩ := X.exists_tangentCompPairs_eq (k := b.1.1) (h := b.1.2) b.2
  exact ⟨v, Subtype.ext hv⟩

/-- **The bijection `T(𝐗 ₛ×ₜ 𝐗) ≃ T𝐗 _{Ts}×_{Tt} T𝐗`** (2021 p. 359). -/
def tangentCompPairsEquiv : X.compPolyfold.TangentSpace ≃ X.tangentEpGroupoid.CompPairs :=
  Equiv.ofBijective X.tangentCompPairsInto X.bijective_tangentCompPairsInto

theorem continuous_tangentCompPairsInto : Continuous X.tangentCompPairsInto :=
  Continuous.subtype_mk ((MPolyfold.continuous_tangentMap _).prodMk
    (MPolyfold.continuous_tangentMap _)) _

/-- The identification is a local sc-diffeomorphism: it commutes with the local
sc-diffeomorphisms `Tπ₂` and `π₂`. -/
theorem isLocalScDiffeo_tangentCompPairsInto :
    X.compPolyfold.tangentPolyfold.IsLocalScDiffeo X.tangentEpGroupoid.compPolyfold
      X.tangentCompPairsInto :=
  MPolyfold.isLocalScDiffeo_of_comp_eq (X.isLocalScDiffeo_compSnd.tangentMap)
    X.tangentEpGroupoid.isLocalScDiffeo_compSnd X.continuous_tangentCompPairsInto fun _ => rfl

/-- **2021 p. 359 (2017 p. 258): `T(𝐗 ₛ×ₜ 𝐗) = T𝐗 _{Ts}×_{Tt} T𝐗` as M-polyfolds.**  The
identification `v ↦ (Tπ₁ v, Tπ₂ v)` is an sc-diffeomorphism from the tangent of the
sub-M-polyfold `𝐗 ₛ×ₜ 𝐗 ⊆ 𝐗 × 𝐗` onto the sub-M-polyfold `T𝐗 _{Ts}×_{Tt} T𝐗 ⊆ T𝐗 × T𝐗`. -/
theorem isScDiffeoOn_tangentCompPairs :
    X.compPolyfold.tangentPolyfold.IsScDiffeoOn X.tangentEpGroupoid.compPolyfold
      X.tangentCompPairsInto X.tangentCompPairsEquiv.symm univ univ :=
  X.isLocalScDiffeo_tangentCompPairsInto.isScDiffeoOn_of_bijective X.tangentCompPairsEquiv
    fun _ => rfl

/-- **`m_{T𝐗} = Tm`** (2021 Lemma 8.1.2 with the identification of p. 359): the multiplication
of the tangent ep-groupoid, on its fibred product `T𝐗 _{Ts}×_{Tt} T𝐗`, is `Tm` transported by
the identification. -/
theorem lemma_8_1_2_compMul (b : X.tangentEpGroupoid.CompPairs) :
    X.tangentEpGroupoid.compMul b = X.tCompMul (X.tangentCompPairsEquiv.symm b) := by
  obtain ⟨v, rfl⟩ := X.tangentCompPairsEquiv.surjective b
  rw [Equiv.symm_apply_apply, lemma_8_1_2_tangentMul]
  rfl

end EpGroupoid

end Polyfold
