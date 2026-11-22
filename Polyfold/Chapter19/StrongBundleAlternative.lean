import Polyfold.Chapter19.StrongBundleTopology
import Polyfold.Chapter19.PolyfoldStructure
import Polyfold.Chapter2.StrongBundlePullback

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.6 "A Strong Bundle Version", **"Alternative Approach"** (pp. 900–902): the fibred products
(19.14), the maps `H`, `H'` of (19.15)–(19.16), the map `C = H'⁻¹ ∘ H`, and
**Definition 19.6.15** (coherence).  Numbers and pages are the 2021 text's.

# The alternative approach: the maps `H`, `H'`, `C` and coherence

## The text, paraphrased

A uniformizer construction `F̄` for `P : E → S` induces `F` for `S`; given transition data `F`
for `F` (with the properness condition, so that every `M(Ψ, Ψ')` has its natural M-polyfold
structure, Theorem 19.5.1), the fibred products `M(Ψ, Ψ') ₛ×ₚ K` and `M(Ψ, Ψ') ₜ×ₚ' K'` (19.14)
are strong bundles over `M(Ψ, Ψ')` (pull-backs by `s` and `t`, Proposition 2.6.8).  The
bijections, linear on the fibres, (19.16)
`H((q, φ, q'), k) = (k, φ, Ψ̄'⁻¹(μ(φ, Ψ̄(k))))`,
`H'((q, φ, q'), k') = (Ψ̄⁻¹(μ(φ⁻¹, Ψ̄'(k'))), φ, k')`
cover `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`.  (Definition 19.6.15) `(F̄, F)` is **coherent** if for all
`Ψ̄ ∈ F̄(β)`, `Ψ̄' ∈ F̄(β')` the map `C = H'⁻¹ ∘ H : M(Ψ, Ψ') ₛ×ₚ K → M(Ψ, Ψ') ₜ×ₚ' K'` is a strong
bundle isomorphism (covering the identity).

## What is formalized (namespace `Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction`)

`Fb : StrongBundleUniformizerConstruction μ` (the text's `F̄`), `F : Fb.base.TransitionData`
(transition data for the underlying `F`), `Ψ Ψ' : Fb.Unif`.

* `SrcPB F Ψ Ψ'`, `TgtPB F Ψ Ψ'` (the fibred products (19.14)), `srcBundle`, `tgtBundle` (their
  strong bundle structures over `F.transPolyfold`, the pulled-back atlases of Proposition 2.6.8).
* `altH`, `altH'` ((19.16)), `proj_altH`, `proj_altH'` (they cover `p`), `src_altH`,
  `tgt_altH'`, `altH_bijective`, `altH'_bijective`.
* `altC` (`C = H'⁻¹ ∘ H`), `altH'_altC` (`H' ∘ C = H`), `altC_eq` (`C = H'⁻¹ ∘ H` as maps),
  `pullbackProj_altC` (`C` covers the identity), `altC_bijective`.
* `IsCoherent`, `definition_19_6_15` (**Definition 19.6.15**).
* `StrongBundleStr.eq_of_proj_tgt` (an element of `M(Ψ̄, Ψ̄')` is determined by its target and
  its image under `p`).

## What the text leaves implicit, and the choices made

* We read the fibred products (19.14) as the pull-backs `pullbackSpace` of Definition 2.6.7, the
  second one taken with the target map `t` (the text writes "the source map t").
* The M-polyfold structure of `M(Ψ, Ψ')` is `F.transPolyfold` (Theorem 19.5.1); in this
  formalization it is defined from the transition data alone, so the properness condition
  enters only through the metrizability of `T` and is not a hypothesis here.
* We read "`C` is a strong bundle isomorphism" as: `C` is a strong bundle map covering the
  identity of `M(Ψ, Ψ')` and a strong bundle isomorphism on all of `M(Ψ, Ψ')`
  (`IsStrongBundleIsoOn` over `univ`).
-/

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

universe u

variable {C : GroupoidalCategory.{u}}

open GroupoidStr (TransitionSet)

namespace StrongBundleStr

variable {μ : C.BanFunctor} {Ψe Ψe' : μ.cat.Uniformizer} (S : StrongBundleStr μ Ψe)
  (S' : StrongBundleStr μ Ψe')

/-- **An element of `M(Ψ̄, Ψ̄')` is determined by its target and its image under `p`.** -/
theorem eq_of_proj_tgt {h₁ h₂ : Ψe.Trans Ψe'} (ht : h₁.tgt = h₂.tgt)
    (hp : S.proj S' h₁ = S.proj S' h₂) : h₁ = h₂ := by
  have e : h₁.inv = h₂.inv := S'.eq_of_proj S ht (by
    rw [S.proj_inv S' h₁, S.proj_inv S' h₂, hp])
  rw [← TransitionSet.inv_inv h₁, e, TransitionSet.inv_inv]

end StrongBundleStr

namespace StrongBundleUniformizerConstruction

variable {μ : C.BanFunctor} {Fb : StrongBundleUniformizerConstruction μ}
  (F : Fb.base.TransitionData) (Ψ Ψ' : Fb.Unif)

/-- The source map `s : M(Ψ, Ψ') → O`. -/
abbrev trSrc : F.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') → (Fb.strU Ψ).O :=
  fun h => (h : (Fb.strU Ψ).toBase.Trans (Fb.strU Ψ').toBase).src

/-- The target map `t : M(Ψ, Ψ') → O'`. -/
abbrev trTgt : F.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') → (Fb.strU Ψ').O :=
  fun h => (h : (Fb.strU Ψ).toBase.Trans (Fb.strU Ψ').toBase).tgt

/-- **2021 (19.14), p. 901: the fibred product `M(Ψ, Ψ') ₛ×ₚ K`**, the pull-back of `p : K → O`
by `s`. -/
abbrev SrcPB : Set (F.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') × Ψ.1.O) :=
  pullbackSpace (Fb.strU Ψ).p (trSrc F Ψ Ψ')

/-- **2021 (19.14), p. 901: the fibred product `M(Ψ, Ψ') ₜ×ₚ' K'`**, the pull-back of
`p' : K' → O'` by `t`. -/
abbrev TgtPB : Set (F.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') × Ψ'.1.O) :=
  pullbackSpace (Fb.strU Ψ').p (trTgt F Ψ Ψ')

instance instParacompactSpaceSrcPB : ParacompactSpace (SrcPB F Ψ Ψ') :=
  paracompactSpace_pullbackSpace (F.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
    (Fb.strU Ψ).B

instance instParacompactSpaceTgtPB : ParacompactSpace (TgtPB F Ψ Ψ') :=
  paracompactSpace_pullbackSpace (F.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
    (Fb.strU Ψ').B

theorem isScSmoothMap_trSrc :
    (F.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ')).IsScSmoothMap (Fb.strU Ψ).PO
      (trSrc F Ψ Ψ') :=
  (F.isLocalScDiffeo_src (Fb.baseUnif Ψ) (Fb.baseUnif Ψ')).isScSmoothMap

theorem isScSmoothMap_trTgt :
    (F.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ')).IsScSmoothMap (Fb.strU Ψ').PO
      (trTgt F Ψ Ψ') :=
  (F.isLocalScDiffeo_tgt (Fb.baseUnif Ψ) (Fb.baseUnif Ψ')).isScSmoothMap

/-- **The strong bundle `π : M(Ψ, Ψ') ₛ×ₚ K → M(Ψ, Ψ')`** (p. 901; the pull-back structure of
Proposition 2.6.8). -/
def srcBundle :
    StrongBundle (F.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
      (pullbackProj (Fb.strU Ψ).p (trSrc F Ψ Ψ')) where
  continuous := continuous_pullbackProj _ _
  surjective z := by
    obtain ⟨y, hy⟩ := (Fb.strU Ψ).B.surjective (trSrc F Ψ Ψ' z)
    exact ⟨⟨(z, y), hy⟩, rfl⟩
  banachable z := by
    obtain ⟨Bsp, h1, h2, h3, ⟨e⟩⟩ := (Fb.strU Ψ).B.banachable (trSrc F Ψ Ψ' z)
    exact ⟨Bsp, h1, h2, h3, ⟨(pullbackFiberCLE z).trans e⟩⟩
  atlas := pullbackAtlas (Fb.strU Ψ).B (isScSmoothMap_trSrc F Ψ Ψ')

/-- **The strong bundle `π' : M(Ψ, Ψ') ₜ×ₚ' K' → M(Ψ, Ψ')`** (p. 901). -/
def tgtBundle :
    StrongBundle (F.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
      (pullbackProj (Fb.strU Ψ').p (trTgt F Ψ Ψ')) where
  continuous := continuous_pullbackProj _ _
  surjective z := by
    obtain ⟨y, hy⟩ := (Fb.strU Ψ').B.surjective (trTgt F Ψ Ψ' z)
    exact ⟨⟨(z, y), hy⟩, rfl⟩
  banachable z := by
    obtain ⟨Bsp, h1, h2, h3, ⟨e⟩⟩ := (Fb.strU Ψ').B.banachable (trTgt F Ψ Ψ' z)
    exact ⟨Bsp, h1, h2, h3, ⟨(pullbackFiberCLE z).trans e⟩⟩
  atlas := pullbackAtlas (Fb.strU Ψ').B (isScSmoothMap_trTgt F Ψ Ψ')

/-! ### The maps `H`, `H'` of (19.16) -/

/-- **2021 (19.16), p. 901: `H((q, φ, q'), k) = (k, φ, Ψ̄'⁻¹(μ(φ, Ψ̄(k))))`.** -/
def altH (x : SrcPB F Ψ Ψ') : Ψ.1.Trans Ψ'.1 :=
  (Fb.strU Ψ).lift (Fb.strU Ψ') x.1.1 x.1.2 x.2

/-- **2021 (19.16), p. 901: `H'((q, φ, q'), k') = (Ψ̄⁻¹(μ(φ⁻¹, Ψ̄'(k'))), φ, k')`.** -/
def altH' (x : TgtPB F Ψ Ψ') : Ψ.1.Trans Ψ'.1 :=
  ((Fb.strU Ψ').lift (Fb.strU Ψ)
    (x.1.1 : (Fb.strU Ψ).toBase.Trans (Fb.strU Ψ').toBase).inv x.1.2 x.2).inv

theorem src_altH (x : SrcPB F Ψ Ψ') : (altH F Ψ Ψ' x).src = x.1.2 := rfl

theorem tgt_altH' (x : TgtPB F Ψ Ψ') : (altH' F Ψ Ψ' x).tgt = x.1.2 := rfl

/-- **`H` covers `p`**: `p ∘ H = π` (diagram (19.15)). -/
theorem proj_altH (x : SrcPB F Ψ Ψ') :
    (Fb.strU Ψ).proj (Fb.strU Ψ') (altH F Ψ Ψ' x) = x.1.1 :=
  (Fb.strU Ψ).proj_lift (Fb.strU Ψ') _ _ _

/-- **`H'` covers `p`**: `p ∘ H' = π'` (diagram (19.15)). -/
theorem proj_altH' (x : TgtPB F Ψ Ψ') :
    (Fb.strU Ψ).proj (Fb.strU Ψ') (altH' F Ψ Ψ' x) = x.1.1 := by
  rw [altH', (Fb.strU Ψ').proj_inv (Fb.strU Ψ)]
  exact (congrArg TransitionSet.inv ((Fb.strU Ψ').proj_lift (Fb.strU Ψ) _ _ _)).trans
    (TransitionSet.inv_inv (x.1.1 : (Fb.strU Ψ).toBase.Trans (Fb.strU Ψ').toBase))

/-- **`H` is a bijection** (p. 901). -/
theorem altH_bijective : Bijective (altH F Ψ Ψ') := by
  refine ⟨fun x y hxy => ?_, fun h => ?_⟩
  · have h1 : x.1.1 = y.1.1 := by
      rw [← proj_altH F Ψ Ψ' x, ← proj_altH F Ψ Ψ' y, hxy]
    have h2 : x.1.2 = y.1.2 := by
      rw [← src_altH F Ψ Ψ' x, ← src_altH F Ψ Ψ' y, hxy]
    exact Subtype.ext (Prod.ext h1 h2)
  · refine ⟨⟨((Fb.strU Ψ).proj (Fb.strU Ψ') h, h.src), rfl⟩, ?_⟩
    exact (Fb.strU Ψ).lift_proj (Fb.strU Ψ') h

/-- **`H'` is a bijection** (p. 901). -/
theorem altH'_bijective : Bijective (altH' F Ψ Ψ') := by
  refine ⟨fun x y hxy => ?_, fun h => ?_⟩
  · have h1 : x.1.1 = y.1.1 := by
      rw [← proj_altH' F Ψ Ψ' x, ← proj_altH' F Ψ Ψ' y, hxy]
    have h2 : x.1.2 = y.1.2 := by
      rw [← tgt_altH' F Ψ Ψ' x, ← tgt_altH' F Ψ Ψ' y, hxy]
    exact Subtype.ext (Prod.ext h1 h2)
  · refine ⟨⟨((Fb.strU Ψ).proj (Fb.strU Ψ') h, h.tgt), rfl⟩, ?_⟩
    exact (Fb.strU Ψ).eq_of_proj_tgt (Fb.strU Ψ') rfl (proj_altH' F Ψ Ψ' _)

/-! ### The map `C = H'⁻¹ ∘ H` and Definition 19.6.15 -/

/-- **2021 p. 901: `C = H'⁻¹ ∘ H : M(Ψ, Ψ') ₛ×ₚ K → M(Ψ, Ψ') ₜ×ₚ' K'`**, explicitly
`C((q, φ, q'), k) = ((q, φ, q'), Ψ̄'⁻¹(μ(φ, Ψ̄(k))))`. -/
def altC (x : SrcPB F Ψ Ψ') : TgtPB F Ψ Ψ' :=
  ⟨(x.1.1, (altH F Ψ Ψ' x).tgt), (Fb.strU Ψ).p_lift_tgt (Fb.strU Ψ') _ _ _⟩

/-- `H' ∘ C = H`. -/
theorem altH'_altC (x : SrcPB F Ψ Ψ') : altH' F Ψ Ψ' (altC F Ψ Ψ' x) = altH F Ψ Ψ' x :=
  (Fb.strU Ψ).eq_of_proj_tgt (Fb.strU Ψ') rfl
    ((proj_altH' F Ψ Ψ' _).trans (proj_altH F Ψ Ψ' x).symm)

/-- **`C = H'⁻¹ ∘ H`.** -/
theorem altC_eq (x : SrcPB F Ψ Ψ') :
    altC F Ψ Ψ' x = (Equiv.ofBijective _ (altH'_bijective F Ψ Ψ')).symm (altH F Ψ Ψ' x) := by
  rw [Equiv.eq_symm_apply]
  exact altH'_altC F Ψ Ψ' x

/-- **`C` covers the identity of `M(Ψ, Ψ')`** (diagram (19.17)). -/
theorem pullbackProj_altC (x : SrcPB F Ψ Ψ') :
    pullbackProj (Fb.strU Ψ').p (trTgt F Ψ Ψ') (altC F Ψ Ψ' x) =
      pullbackProj (Fb.strU Ψ).p (trSrc F Ψ Ψ') x := rfl

/-- **`C` is a bijection.** -/
theorem altC_bijective : Bijective (altC F Ψ Ψ') := by
  have e : altC F Ψ Ψ' =
      (Equiv.ofBijective _ (altH'_bijective F Ψ Ψ')).symm ∘ altH F Ψ Ψ' :=
    funext (altC_eq F Ψ Ψ')
  rw [e]
  exact (Equiv.bijective _).comp (altH_bijective F Ψ Ψ')

/-- **2021 Definition 19.6.15, p. 902: coherence of `(F̄, F)`**: for all `Ψ̄, Ψ̄'` in `F̄`, the map
`C = H'⁻¹ ∘ H : M(Ψ, Ψ') ₛ×ₚ K → M(Ψ, Ψ') ₜ×ₚ' K'` is a strong bundle isomorphism covering the
identity of `M(Ψ, Ψ')`. -/
def IsCoherent : Prop :=
  ∀ Ψ Ψ' : Fb.Unif, ∃ h : (srcBundle F Ψ Ψ').IsStrongBundleMap (tgtBundle F Ψ Ψ') id
      (altC F Ψ Ψ'), (srcBundle F Ψ Ψ').IsStrongBundleIsoOn (tgtBundle F Ψ Ψ') h univ univ

/-- **2021 Definition 19.6.15, p. 902.** -/
theorem definition_19_6_15 :
    IsCoherent F ↔ ∀ Ψ Ψ' : Fb.Unif, ∃ h : (srcBundle F Ψ Ψ').IsStrongBundleMap
      (tgtBundle F Ψ Ψ') id (altC F Ψ Ψ'),
        (srcBundle F Ψ Ψ').IsStrongBundleIsoOn (tgtBundle F Ψ Ψ') h univ univ :=
  Iff.rfl

end StrongBundleUniformizerConstruction

end GroupoidalCategory

end Polyfold
