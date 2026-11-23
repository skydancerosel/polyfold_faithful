import Polyfold.Chapter15.RestrictedOrientationCanonSum

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702, **Theorem 15.4.1** and **Definition 15.4.2**, with Chapter 11's pull-back of
orientations (Theorem 11.3.5, Definition 11.3.6, p. 540), on the restriction `W|V → X|V` of a
strong bundle over an ep-groupoid to a saturated open set `V` (Proposition 7.1.22, p. 250).

# The canonical orientation restricted to a saturated open set is canonical

## The text, paraphrased

(p. 702) `Θ = Λ ∘ f` carries the canonical orientation `T̂_((f, o), Λ)`, computed in local
branching structures whose sheets are the solution sets `Mᵢ = {f = sᵢ}` of a local sc⁺-section
structure `(sᵢ, σᵢ)` of `Λ`, oriented by `o`.  All of the data are local, so they restrict to a
saturated open subset of the object space.

## What is formalized

For `V` open and saturated and the inclusion `ι : X|V → X` (`restrFun hV`, by definition
`A.baseEP.subFunctor hV`):

* `EpFunctor.isOrientation_pullSection_of_isLocalScDiffeo`: Theorem 11.3.5, pull-back, for a
  functor which is a local sc-diffeomorphism on objects (the proof of
  `EpFunctor.isOrientation_pullSection` with the independence of Theorem 9.2.1 on the source).
* `KernelBranching.restr`: a local branching structure `K'` of `Λ ∘ f` at `ι(x)` described by
  kernels gives one of `Λ|V ∘ f|V` at `x`: the sections `sᵢ|V`, the sheets `ι⁻¹(Mᵢ')` on the
  domain of a natural representation.
* **`IsCanonicalFor.restr`**: if `T̂` is canonical for `(Λ, o)` on `A`, then `ι^* T̂`
  (`(restrFun hV).pullSection T̂`) is canonical for `(Λ|V, o|V)` on `A.restr hV`, with the same
  dimension, for an orientation `o` made with local sc⁺-sections on a tame `X`.
* **`canonicalOrientation_restr`**: the canonical lift of `(f|V, o|V, Λ|V)` is the pull-back of
  the canonical lift of `(f, o, Λ)` at every smooth point, when the latter is canonical.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

/-! ### Theorem 11.3.5, pull-back, along a local sc-diffeomorphism -/

namespace EpFunctor

open EpGroupoid MPolyfold

variable {Obj Mor Obj' Mor' : Type u}
  [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {F : EpFunctor X Y}

/-- **Theorem 11.3.5, pull-back** (2021 p. 540), for a functor `F` which is a local
sc-diffeomorphism on objects: `F^* T̂_Θ'` is an orientation of `F^*Θ'`; an oriented branching
structure at `F(x)` is moved back by a local inverse of `F`. -/
theorem isOrientation_pullSection_of_isLocalScDiffeo
    (hd : X.PObj.IsLocalScDiffeo Y.PObj F.obj) {Θ' : Obj' → ℚ}
    {T' : Obj' → Y.PObj.OrTangent →₀ ℚ} (hT' : Y.IsOrientation Θ' T') :
    X.IsOrientation (F.pullbackTheta Θ') (F.pullSection T') := by
  have hS := isGrHatSection_pullSection hd hT'.isGrHatSection
  refine IsOrientation.mk' (X.hasIndependentTangentSums _) hS.mem hS.natural
    (fun x hx hxs => ?_) fun x hx => ?_
  · rw [pullSection_of_mem hx, hT'.eq_zero_of_not_mem ((hd.mem_smoothSet_iff x).2 hx)
      fun h => hxs (show 0 < F.pullbackTheta Θ' x by rw [pullbackTheta_apply]; exact h),
      Finsupp.mapDomain_zero]
  · have hFx : F.obj x ∈ supp Θ' := by
      have h : 0 < F.pullbackTheta Θ' x := hx
      rwa [pullbackTheta_apply] at h
    obtain ⟨B', hB'⟩ := hT'.locallyOriented _ hFx
    obtain ⟨U, V, g, hxU, hdF⟩ := hd x
    have hΘ : ∀ v ∈ V, F.pullbackTheta Θ' (g v) = Θ' v := fun v hv => by
      simp only [pullbackTheta_apply, hdF.right_inv v hv]
    refine ⟨B'.mapDiffeo hdF.symm (hdF.mapsTo hxU) (hdF.left_inv x hxU) hΘ, fun z hz hzs => ?_⟩
    rw [B'.orientedSum_mapDiffeo hdF.symm (hdF.mapsTo hxU) (hdF.left_inv x hxU) hΘ hz]
    obtain ⟨hzU, hFzU', -⟩ := hz
    have hFzs : F.obj z ∈ Y.PObj.smoothSet := (hd.mem_smoothSet_iff z).2 hzs
    rw [pullSection_of_mem hzs, hB' (F.obj z) hFzU' hFzs]
    exact mapDomain_map_congr (B'.orientedSum_mem _) fun β hβ =>
      fibreInv_eq_tangentMapOn hd hdF hzU hβ

end EpFunctor

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}} {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V) (hVo : IsOpen V)
  {f : A.Obj → A.W} (hF : A.E.IsScFredholmSectionFunctor f)

include hVo hF

/-! ### A structure described by kernels on a saturated open set -/

/-- `f|V(z) = Ψ(s'(ι z))` iff `f(ι z) = s'(ι z)`. -/
theorem eq_isoSec_iff_restr (a z : (A.restr hV).Obj) {s' : A.Obj → A.W}
    (hs' : A.P (s' (restrBase hV z)) = restrBase hV z) :
    restrSec hV f hF.1.1.1 z = isoSec (restrIso hV hVo a) s' z ↔
      f (restrBase hV z) = s' (restrBase hV z) := by
  set L := restrIso hV hVo a with hL
  have e2 : restrSec hV f hF.1.1.1 z = L.Ψ (f (restrBase hV z)) :=
    eqOn_restrSec hV hVo hF.1.1.1 a (mem_univ z)
  have hU' : restrBase hV z ∈ V := restrBase_mem hV z
  change restrSec hV f hF.1.1.1 z = L.Ψ (s' (restrBase hV z)) ↔ _
  rw [e2]
  constructor
  · intro h0
    have h1 := congrArg L.Φ h0
    rwa [L.zero.right_inv _ (show A.P (f (restrBase hV z)) ∈ V by
        rw [hF.1.1.1 (restrBase hV z)]; exact hU'),
      L.zero.right_inv _ (show A.P (s' (restrBase hV z)) ∈ V by rw [hs']; exact hU')] at h1
  · intro h0
    rw [h0]

variable {Λ : A.W → ℚ≥0} {x : (A.restr hV).Obj} (K' : KernelBranching A f Λ (restrBase hV x))
  {R : (A.restr hV).X.NaturalRep x} (hRU : R.U ⊆ isoSet (restrIso hV hVo x) K'.U)

include hRU

theorem mem_M_iff_restr (i : K'.ι) {z : (A.restr hV).Obj} (hzR : z ∈ R.U) :
    restrSec hV f hF.1.1.1 z = isoSec (restrIso hV hVo x) (K'.s i) z ↔
      restrBase hV z ∈ K'.M i := by
  have hϕU : restrBase hV z ∈ K'.U := (hRU hzR).2
  rw [eq_isoSec_iff_restr hV hVo hF x z ((K'.isScPlus i).1 _ (K'.U_subset hϕU)), K'.M_eq i]
  exact ⟨fun h0 => ⟨hϕU, h0⟩, fun h0 => h0.2⟩

/-- The sheet `{z ∈ R.U | f|V(z) = Ψ(sᵢ(ι z))}` is `ι⁻¹(Mᵢ') ∩ R.U`, written with the local
inverse of `ι`. -/
theorem sep_eq_image_restr (i : K'.ι) :
    {z ∈ R.U | restrSec hV f hF.1.1.1 z = isoSec (restrIso hV hVo x) (K'.s i) z} =
      (restrIso hV hVo x).g '' (K'.M i ∩ V) ∩ R.U := by
  set L := restrIso hV hVo x with hL
  ext z
  constructor
  · rintro ⟨hzR, hz⟩
    exact ⟨⟨restrBase hV z, ⟨(mem_M_iff_restr hV hVo hF K' hRU i hzR).1 hz, restrBase_mem hV z⟩,
      L.base.left_inv z (mem_univ z)⟩, hzR⟩
  · rintro ⟨⟨w, ⟨hwM, hwU'⟩, rfl⟩, hzR⟩
    refine ⟨hzR, (mem_M_iff_restr hV hVo hF K' hRU i hzR).2 ?_⟩
    have e : restrBase hV (L.g w) = w := L.base.right_inv w hwU'
    rw [e]
    exact hwM

omit hF hRU in
open Classical in
/-- The local sc⁺-section structure of `Λ|V` on `ι⁻¹(O(K') ∩ V)`. -/
theorem isLocalRepOn_restr :
    IsLocalRepOn (A.restr hV) (restrMult hV Λ) (isoSet (restrIso hV hVo x) (K'.O ∩ V))
      (fun j => isoSec (restrIso hV hVo x) (K'.sAll j)) K'.σAll :=
  isLocalRepOn_isoSec (restrIso hV hVo x) (fun _ _ => rfl) (K'.isOpen_O.inter hVo)
    inter_subset_right (K'.isLocalRep.mono (K'.isOpen_O.inter hVo) inter_subset_left)

/-- **`T_yMᵢ = ker (f|V − sᵢ|V)'(y)` and `(f|V − sᵢ|V)'(y)` onto, for the restricted sheets, in
every chart**: the chart `c` is carried to `W` through the inverse of the inclusion, where the
structure `K'` gives both properties. -/
theorem chartVec_image_restr (i : K'.ι) {y : (A.restr hV).Obj} (hyR : y ∈ R.U)
    (hy : restrSec hV f hF.1.1.1 y = isoSec (restrIso hV hVo x) (K'.s i) y)
    (c : StrongBundleChart (A.restr hV).X.PObj (A.restr hV).P) (hc : (A.restr hV).B.IsChart c)
    (hsub : c.φ.source ⊆ isoSet (restrIso hV hVo x) (K'.O ∩ V))
    (hyc : y ∈ c.φ.source) (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ y) :
    chartVec c.isChart '' (A.restr hV).X.PObj.submanifoldTangent
        {z ∈ R.U | restrSec hV f hF.1.1.1 z = isoSec (restrIso hV hVo x) (K'.s i) z} y =
      kerSet c (restrSec hV f hF.1.1.1) (isoSec (restrIso hV hVo x) (K'.s i)) z ∧
    ChartOnto c (subDeriv c (restrSec hV f hF.1.1.1)
      (isoSec (restrIso hV hVo x) (K'.s i)) z) z := by
  have hF₁ := isScFredholmSectionFunctor_restrSec hV hVo hF
  set L := restrIso hV hVo x with hL
  have hyU : y ∈ (univ : Set (A.restr hV).Obj) := mem_univ y
  have hϕM : restrBase hV y ∈ K'.M i := (mem_M_iff_restr hV hVo hF K' hRU i hyR).1 hy
  have hcU : c.φ.source ⊆ (univ : Set (A.restr hV).Obj) := fun w _ => mem_univ w
  set c'' := L.symm.transportChart c hcU with hc''def
  have hc'' : A.B.IsChart c'' := L.symm.isChart_transportChart c hcU hc
  have hgy : L.g (restrBase hV y) = y := L.base.left_inv y hyU
  have hϕU' : restrBase hV y ∈ V := restrBase_mem hV y
  have hyc'' : restrBase hV y ∈ c''.φ.source := ⟨hϕU', by
    change L.g (restrBase hV y) ∈ c.φ.source
    rw [hgy]; exact hyc⟩
  have hsub'' : c''.φ.source ⊆ K'.O := fun w hw => by
    have h1 := hsub hw.2
    have h2 : L.ϕ (L.g w) = w := L.base.right_inv w hw.1
    have h3 : L.ϕ (L.g w) ∈ K'.O := h1.2.1
    rwa [h2] at h3
  have hz'' : c''.φ.model.E.toBase 1 z = c''.φ (restrBase hV y) := by
    change c.φ.model.E.toBase 1 z = c.φ (L.g (restrBase hV y))
    rw [hgy]; exact hz
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U :=
    mem_U_of_mem_O c.isRetraction (by rw [c.r_image, hz]; exact c.φ.mapsTo_model y hyc)
  have hfL'' : EqOn f (L.symm.Ψ ∘ restrSec hV f hF.1.1.1 ∘ L.symm.ϕ) V :=
    L.eqOn_symm hF.1.1.1 (eqOn_restrSec hV hVo hF.1.1.1 x)
  have hsI := (isLocalRepOn_restr hV hVo K' (x := x)).2.1 (K'.idx i)
  have e1 : subDeriv c'' f (isoSec L.symm (isoSec L (K'.s i))) z =
      subDeriv c (restrSec hV f hF.1.1.1) (isoSec L (K'.s i)) z :=
    subDeriv_transportChart L.symm hcU hF₁.2.isScSmooth hfL'' hsI hc hsub hzU
  have h12 : EqOn (K'.s i) (isoSec L.symm (isoSec L (K'.s i))) c''.φ.source := fun w hw => by
    change K'.s i w = L.Φ (L.Ψ (K'.s i (L.ϕ (L.g w))))
    rw [L.base.right_inv w hw.1, L.zero.right_inv _ (show A.P (K'.s i w) ∈ V by
      rw [(K'.isScPlus i).1 w (hsub'' hw)]; exact hw.1)]
  have e2 : subDeriv c'' f (isoSec L.symm (isoSec L (K'.s i))) z = subDeriv c'' f (K'.s i) z :=
    subDeriv_congr_sec hc'' hF.2.isScSmooth (K'.isScPlus i) hsub'' h12 hzU
  have hD : subDeriv c'' f (K'.s i) z =
      subDeriv c (restrSec hV f hF.1.1.1) (isoSec L (K'.s i)) z := e2.symm.trans e1
  have hK1 := K'.tangent_eq i (restrBase hV y) hϕM c'' hc'' hsub'' hyc'' z hz''
  have hK2 := K'.onto i (restrBase hV y) hϕM c'' hc'' hsub'' hyc'' z hz''
  refine ⟨?_, ?_⟩
  · have hker : kerSet c'' f (K'.s i) z =
        kerSet c (restrSec hV f hF.1.1.1) (isoSec L (K'.s i)) z := by
      unfold kerSet; rw [hD]; rfl
    rw [← hker, ← hK1, sep_eq_image_restr hV hVo hF K' hRU i,
      submanifoldTangent_inter_isOpen R.isOpen_U hyR]
    have hA : A.X.PObj.IsSmoothSubmanifold (K'.M i ∩ V) :=
      (K'.isSmoothSubmanifold i).inter_isOpen L.isOpen_U'
    have ht := submanifoldTangent_image_of_isScDiffeoOn L.base.symm hA inter_subset_right
      ⟨hϕM, hϕU'⟩
    rw [hgy] at ht
    rw [ht, submanifoldTangent_inter_isOpen L.isOpen_U' hϕU', image_image]
    refine image_congr fun α hα => ?_
    have hα1 : A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = restrBase hV y := hα.1
    exact chartVec_tangentMapOn_of_isScDiffeoOn L.base.symm c.isChart (by
      rw [hα1]
      exact ⟨hϕU', by change L.g (restrBase hV y) ∈ c.φ.source; rw [hgy]; exact hyc⟩)
  · rw [← hD]; exact hK2

variable (hRP : (A.restr hV).X.HasPropernessProperty R.U)

open Classical in
/-- **A structure described by kernels restricted to a saturated open set**: from `K'` at
`ι(x)` and a natural representation `R` of `G_x` in `X|V` with the properness property on
`R.U ⊆ ι⁻¹(U(K'))`, the sheets `Mᵢ = {z ∈ R.U | f|V(z) = sᵢ|V(z)} = R.U ∩ ι⁻¹(Mᵢ')`, with the
weights and dimensions of `K'`. -/
def KernelBranching.restr :
    KernelBranching (A.restr hV) (restrSec hV f hF.1.1.1) (restrMult hV Λ) x where
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  ι := K'.ι
  M i := {z ∈ R.U | restrSec hV f hF.1.1.1 z = isoSec (restrIso hV hVo x) (K'.s i) z}
  subset_U _ := sep_subset _ _
  isSmoothSubmanifold i := by
    rw [sep_eq_image_restr hV hVo hF K' hRU i]
    exact (((K'.isSmoothSubmanifold i).inter_isOpen hVo).image_of_isScDiffeoOn
      (restrIso hV hVo x).base.symm inter_subset_right).inter_isOpen R.isOpen_U
  mem_M i := ⟨R.mem_U, (mem_M_iff_restr hV hVo hF K' hRU i R.mem_U).2 (K'.mem_M i)⟩
  isProperMap i := by
    rw [isProperMap_inclusion_iff]
    have hfc : Continuous (restrSec hV f hF.1.1.1) := continuousOn_univ.1
      (isScFredholmSectionFunctor_restrSec hV hVo hF).2.isScSmooth.2.continuousOn
    have hRO : R.U ⊆ isoSet (restrIso hV hVo x) (K'.O ∩ V) := fun z hz =>
      ⟨(hRU hz).1, K'.U_subset (hRU hz).2, restrBase_mem hV z⟩
    have hcs : ContinuousOn (isoSec (restrIso hV hVo x) (K'.s i)) R.U :=
      ((isLocalRepOn_restr hV hVo K' (x := x)).2.1 (K'.idx i)).continuousOn.mono hRO
    have h1 : Continuous fun p : R.U => restrSec hV f hF.1.1.1 p :=
      hfc.comp continuous_subtype_val
    have h2 : Continuous fun p : R.U => isoSec (restrIso hV hVo x) (K'.s i) p :=
      hcs.comp_continuous continuous_subtype_val fun p => p.2
    convert isClosed_eq h1 h2 using 1
    ext p
    simp
  σ := K'.σ
  σ_pos := K'.σ_pos
  eq_sum y hy := by
    have hϕU : restrBase hV y ∈ K'.U := (hRU hy).2
    change ((Λ (f (restrBase hV y)) : ℚ≥0) : ℚ) = _
    rw [K'.eq_sum (restrBase hV y) hϕU]
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨hy, (mem_M_iff_restr hV hVo hF K' hRU i hy).2 h1⟩ h2
    · exact absurd ((mem_M_iff_restr hV hVo hF K' hRU i hy).1 h2.2) h1
    · rfl
  rep := R
  U_eq := rfl
  hasPropernessProperty := hRP
  hasTameInducedStructure i := by
    rw [sep_eq_image_restr hV hVo hF K' hRU i]
    have hA : A.X.PObj.IsSmoothSubmanifold (K'.M i ∩ V) :=
      (K'.isSmoothSubmanifold i).inter_isOpen hVo
    exact MPolyfold.HasTameInducedStructure.inter_isOpen
      (hA.image_of_isScDiffeoOn (restrIso hV hVo x).base.symm inter_subset_right)
      (MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn hA
        (MPolyfold.HasTameInducedStructure.inter_isOpen (K'.isSmoothSubmanifold i)
          (K'.hasTameInducedStructure i) hVo)
        (restrIso hV hVo x).base.symm inter_subset_right) R.isOpen_U
  dim := K'.dim
  isSubmanifoldOfDim i := by
    rw [sep_eq_image_restr hV hVo hF K' hRU i]
    exact (((K'.isSubmanifoldOfDim i).inter_isOpen hVo).image_isScDiffeoOn
      (restrIso hV hVo x).base.symm inter_subset_right).inter_isOpen R.isOpen_U
  O := isoSet (restrIso hV hVo x) (K'.O ∩ V)
  isOpen_O := isOpen_isoSet _ (K'.isOpen_O.inter hVo)
  U_subset := fun z hz => ⟨(hRU hz).1, K'.U_subset (hRU hz).2, restrBase_mem hV z⟩
  k := K'.k
  sAll j := isoSec (restrIso hV hVo x) (K'.sAll j)
  σAll := K'.σAll
  isLocalRep := isLocalRepOn_restr hV hVo K'
  idx := K'.idx
  idx_injective := K'.idx_injective
  σ_eq := K'.σ_eq
  mem_range j z hz hfz := K'.mem_range j (restrBase hV z) (hRU hz).2
    ((eq_isoSec_iff_restr hV hVo hF x z
      ((K'.isLocalRep.2.1 j).1 _ (K'.U_subset (hRU hz).2))).1 hfz)
  M_eq _ := rfl
  smooth i y hy := ((restrIso hV hVo x).mem_smoothSet_iff (mem_univ y)).2
    (K'.smooth i _ ((mem_M_iff_restr hV hVo hF K' hRU i hy.1).1 hy.2))
  tangent_eq i y hy c hc hsub hyc z hz :=
    (chartVec_image_restr hV hVo hF K' hRU i hy.1 hy.2 c hc hsub hyc z hz).1
  onto i y hy c hc hsub hyc z hz :=
    (chartVec_image_restr hV hVo hF K' hRU i hy.1 hy.2 c hc hsub hyc z hz).2

omit hRU

/-! ### The restriction of a canonical orientation -/

variable (hsec : A.B.HasScPlusSectionsThrough)

include hsec

omit x K' R in
/-- **2021 Theorem 15.4.1 / Definition 15.4.2 on a saturated open set: the restriction of a
canonical orientation is canonical.**  Let `X` be tame, `f` with tame germ data and `o` an
orientation of `f` in the sense of Definition 6.6.16 made with local sc⁺-sections.  If `T̂` is the
canonical orientation of `Θ = Λ ∘ f` for `(f, o)`, then `ι^* T̂` (Definition 11.3.6) is the
canonical orientation of `Θ|V = Λ|V ∘ f|V` for `(f|V, o|V)`, with the same dimension: it is an
orientation of `Θ|V` (Theorem 11.3.5), and at every point `x` of the support the structure of
`T̂` at `ι(x)`, restricted to `V` (`KernelBranching.restr`), represents it. -/
theorem IsCanonicalFor.restr (hX : A.X.PObj.IsTame) (hft : A.B.IsScFredholmSectionTame f)
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy}
    (hoL : IsSectionOrientationLoc hX hft fun y hy => orxLocEquiv hft hsec y hy (o y hy))
    {n : ℕ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (hT : IsCanonicalFor Λ hF.2 hsec o n T) :
    IsCanonicalFor (restrMult hV Λ) (isScFredholmSectionFunctor_restrSec hV hVo hF).2
      (hasScPlusSectionsThrough_restr hV hVo hsec) (restrOr hV hVo hF hsec o) n
      ((restrFun hV).pullSection T) := by
  have hF₁ := isScFredholmSectionFunctor_restrSec hV hVo hF
  have hsec₁ := hasScPlusSectionsThrough_restr hV hVo hsec
  have hX₁ := isTame_restr_of_isTame hV hVo hX
  have hft₁ := isScFredholmSectionTame_restrSec hV hVo hF.1 hft
  have hoL₁ := isSectionOrientationLoc_restrOr hV hVo hF hsec hX hft o hoL
  refine ⟨?_, fun x hx => ?_⟩
  · exact EpFunctor.isOrientation_pullSection_of_isLocalScDiffeo
      (isLocalScDiffeo_restrFun hV hVo) hT.1
  · have hx' : restrBase hV x ∈ EpGroupoid.supp (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) := hx
    obtain ⟨K', hc', hn', hR'⟩ := hT.2 (restrBase hV x) hx'
    obtain ⟨Q, hxQ, hQP⟩ := (A.restr hV).X.exists_hasPropernessProperty x
    have hWo : IsOpen (Q ∩ isoSet (restrIso hV hVo x) K'.U) :=
      hQP.1.inter (isOpen_isoSet _ K'.isOpen_U)
    obtain ⟨R, hRW⟩ := (A.restr hV).X.theorem_7_1_13 x hWo ⟨hxQ, mem_univ x, K'.mem_U⟩
    have hRU : R.U ⊆ isoSet (restrIso hV hVo x) K'.U := fun z hz => (hRW hz).2
    have hRP : (A.restr hV).X.HasPropernessProperty R.U :=
      hQP.mono R.isOpen_U fun z hz => (hRW hz).1
    set K := KernelBranching.restr hV hVo hF K' hRU hRP with hK
    have hc : K.FramesContinuous hF₁.2 hsec₁ (restrOr hV hVo hF hsec o) :=
      KernelBranching.framesContinuous_loc hX₁ hft₁ hsec₁ (restrOr hV hVo hF hsec o) hoL₁ K
    refine ⟨K, hc, hn', K.represents_toOrientedTame hc hn' fun y hy hys => ?_⟩
    have hϕU : restrBase hV y ∈ K'.U := (hRU hy).2
    have hys' : restrBase hV y ∈ A.X.PObj.smoothSet := restrBase_mem_smoothSet hV hVo hys
    rw [EpFunctor.pullSection_of_mem hys]
    refine Eq.trans ?_
      (KernelBranching.canonSum_restrOr hV hVo hF hsec o K K' hy hϕU hys).symm
    have h1 : T (restrBase hV y) = K'.canonSum hF.2 hsec o (restrBase hV y) :=
      (hR' _ hϕU hys').trans (K'.orientedSum_toOrientedTame hc' hn' _)
    exact congrArg (fun w => Finsupp.mapDomain
      (OrTangent.map (fibreInv (restrFun hV).tangent.obj y)) w) h1

omit x K' R in
/-- **The canonical lift restricts**: if the canonical lift `T̂_((f, o), Λ)` is the canonical
orientation of `Λ ∘ f` (Theorem 15.4.1), then the canonical lift of `(f|V, o|V, Λ|V)` is its
pull-back under the inclusion `ι : X|V → X`, at every smooth point of `X|V`. -/
theorem canonicalOrientation_restr (hX : A.X.PObj.IsTame) (hft : A.B.IsScFredholmSectionTame f)
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy}
    (hoL : IsSectionOrientationLoc hX hft fun y hy => orxLocEquiv hft hsec y hy (o y hy))
    {n : ℕ} (hT : IsCanonicalFor Λ hF.2 hsec o n (canonicalOrientation Λ hF.2 hsec o))
    {y : (A.restr hV).Obj} (hys : y ∈ (A.restr hV).X.PObj.smoothSet) :
    canonicalOrientation (restrMult hV Λ) (isScFredholmSectionFunctor_restrSec hV hVo hF).2
        (hasScPlusSectionsThrough_restr hV hVo hsec) (restrOr hV hVo hF hsec o) y =
      (restrFun hV).pullSection (canonicalOrientation Λ hF.2 hsec o) y := by
  have hF₁ := isScFredholmSectionFunctor_restrSec hV hVo hF
  have hsec₁ := hasScPlusSectionsThrough_restr hV hVo hsec
  have hT₁ := IsCanonicalFor.restr hV hVo hF hsec hX hft hoL hT
  by_cases hy : y ∈ EpGroupoid.supp
      (fun z => ((restrMult hV Λ (restrSec hV f hF.1.1.1 z) : ℚ≥0) : ℚ))
  · obtain ⟨K, hc, hn, hR⟩ := hT₁.2 y hy
    rw [canonicalOrientation_eq (canonIndependent (restrMult hV Λ) hF₁.2 hsec₁ _) K K.mem_U hys,
      hR y K.mem_U hys, K.orientedSum_toOrientedTame]
  · rw [canonicalOrientation_eq_zero hy, hT₁.1.eq_zero_of_not_mem hys hy]

end SBLocalization

end Polyfold
