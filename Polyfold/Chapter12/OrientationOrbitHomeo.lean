import Polyfold.Chapter5.SmoothLevelContinuity
import Polyfold.Chapter12.OrientationEquivalenceContinuity
import Polyfold.Chapter6.OrientationBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597: **Theorem 12.5.7 (1)** (2017: Theorem 12.12 (1)), the homeomorphism
`|O_f| → |O_{f'}|`, and **Theorem 12.5.7 (2)** in the form of Definition 12.5.4.

# The orbit map of orientation bundles is a homeomorphism

Topologies: Part I's topology on `O_f` (`orTopology` of the transport `orLocalTransport`, the
topology of Theorem 6.6.17 and 12.5.3), the topology of Theorem 2.3.10 on `X_∞`, and the quotient
topologies on `|O_f|` and `|X_∞|`.

* `MPolyfold.IsScDiffeoOn.smoothFwd`, `smoothBwd`: the maps of `X_∞` and `X'_∞` of an
  sc-diffeomorphism `U → U'`, continuous on the smooth parts of `U`, `U'`
  (`IsScSmoothOn.continuousOn_smoothLevel`).
* `EpStrongBundle.isOpen_orSat`: the saturation of an open subset of `O_f` is open (by the last
  sentence of Theorem 12.5.3, `theorem_12_5_3_push_hyp`), so `O_f → |O_f|` is an open map
  (`isOpenMap_quotMk_or`); `EpGroupoid.isOpenMap_quotMk_smooth`: the same for `X_∞ → |X_∞|`.
* For one strong bundle equivalence `h` over `ϕ` and `f = Φ^* f'`:
  `continuous_smoothMap`, `isOpenMap_smoothMap` (`ϕ` is a local homeomorphism of the smooth
  levels), `continuous_orSpaceMap`, `isOpenMap_orSpaceMap` (`(a, o) ↦ (ϕ(a), orEqv⁻¹ o)` is
  continuous and open: near a point it is `y ↦ (ϕ(y), o'_{ϕ(y)})` on the set of a pulled-back
  continuous orientation), and `orbitOrHomeo`, `smoothOrbitHomeo`: **`|O_f| ≃ₜ |O_{f'}|` and
  `|X_∞| ≃ₜ |X'_∞|`**.
* `theorem_12_5_7_one_homeo_hyp`: **Theorem 12.5.7 (1)** for a representative `W ← V → W'`:
  homeomorphisms `|O_f| ≃ₜ |O_{f'}|` over `|X_∞| ≃ₜ |X'_∞|`, the maps of the diagram.
* `theorem_12_5_7_two_book_hyp`: **Theorem 12.5.7 (2)** as printed, with "orientation" in the
  sense of Definition 12.5.4 (continuous for Part I's topology and invariant), from
  `theorem_12_5_7_two_hyp` and Part I's `continuous_orSec_iff`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v'

/-! ### The maps of the smooth levels of an sc-diffeomorphism -/

section Loc

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}

namespace MPolyfold.IsScDiffeoOn

variable {ϕ : X → X'} {g : X' → X} {U : Set X} {U' : Set X'}
  (hd : PX.IsScDiffeoOn PX' ϕ g U U')

include hd in
theorem mem_smoothSet_fwd {x : X} (hx : x ∈ U) (hs : x ∈ PX.smoothSet) :
    ϕ x ∈ PX'.smoothSet :=
  mem_iInter.2 fun m => hd.isScSmoothOn.mapsTo_levelSet m ⟨hx, mem_iInter.1 hs m⟩

include hd in
theorem mem_smoothSet_bwd {y : X'} (hy : y ∈ U') (hs : y ∈ PX'.smoothSet) :
    g y ∈ PX.smoothSet :=
  mem_iInter.2 fun m => hd.isScSmoothOn_inv.mapsTo_levelSet m ⟨hy, mem_iInter.1 hs m⟩

open Classical in
/-- The map `U_∞ → U'_∞` of `ϕ` (extended by a constant `b₀` outside `U`). -/
def smoothFwd (b₀ : PX'.SmoothLevel) (y : PX.SmoothLevel) : PX'.SmoothLevel :=
  if hy : PX.smoothVal y ∈ U then
    PX'.smoothMk (ϕ (PX.smoothVal y)) (hd.mem_smoothSet_fwd hy (PX.smoothVal_mem y))
  else b₀

open Classical in
/-- The map `U'_∞ → U_∞` of `ϕ⁻¹` (extended by a constant `a₀` outside `U'`). -/
def smoothBwd (a₀ : PX.SmoothLevel) (y : PX'.SmoothLevel) : PX.SmoothLevel :=
  if hy : PX'.smoothVal y ∈ U' then
    PX.smoothMk (g (PX'.smoothVal y)) (hd.mem_smoothSet_bwd hy (PX'.smoothVal_mem y))
  else a₀

theorem smoothVal_smoothFwd (b₀ : PX'.SmoothLevel) {y : PX.SmoothLevel}
    (hy : PX.smoothVal y ∈ U) : PX'.smoothVal (hd.smoothFwd b₀ y) = ϕ (PX.smoothVal y) := by
  rw [smoothFwd, dif_pos hy]; rfl

theorem smoothVal_smoothBwd (a₀ : PX.SmoothLevel) {y : PX'.SmoothLevel}
    (hy : PX'.smoothVal y ∈ U') : PX.smoothVal (hd.smoothBwd a₀ y) = g (PX'.smoothVal y) := by
  rw [smoothBwd, dif_pos hy]; rfl

theorem continuousOn_smoothFwd (b₀ : PX'.SmoothLevel) :
    ContinuousOn (hd.smoothFwd b₀) (PX.smoothVal ⁻¹' U) :=
  hd.isScSmoothOn.continuousOn_smoothLevel fun _ hy => hd.smoothVal_smoothFwd b₀ hy

theorem continuousOn_smoothBwd (a₀ : PX.SmoothLevel) :
    ContinuousOn (hd.smoothBwd a₀) (PX'.smoothVal ⁻¹' U') :=
  hd.isScSmoothOn_inv.continuousOn_smoothLevel fun _ hy => hd.smoothVal_smoothBwd a₀ hy

/-- **`ϕ` maps open subsets of `U_∞` to open subsets of `X'_∞`** (its inverse is continuous on
`U'_∞`). -/
theorem isOpen_image_smoothFwd (b₀ : PX'.SmoothLevel) {M : Set PX.SmoothLevel} (hM : IsOpen M)
    (hMU : M ⊆ PX.smoothVal ⁻¹' U) : IsOpen (hd.smoothFwd b₀ '' M) := by
  rcases M.eq_empty_or_nonempty with rfl | ⟨a₀, -⟩
  · rw [image_empty]; exact isOpen_empty
  have he : hd.smoothFwd b₀ '' M = PX'.smoothVal ⁻¹' U' ∩ hd.smoothBwd a₀ ⁻¹' M := by
    ext y'
    constructor
    · rintro ⟨y, hyM, rfl⟩
      have hyU := hMU hyM
      have h1 : PX'.smoothVal (hd.smoothFwd b₀ y) ∈ U' := by
        rw [hd.smoothVal_smoothFwd b₀ hyU]; exact hd.mapsTo hyU
      refine ⟨h1, ?_⟩
      have h2 : hd.smoothBwd a₀ (hd.smoothFwd b₀ y) = y := by
        apply Subtype.ext
        change PX.smoothVal _ = PX.smoothVal y
        rw [hd.smoothVal_smoothBwd a₀ h1, hd.smoothVal_smoothFwd b₀ hyU, hd.left_inv _ hyU]
      rw [mem_preimage, h2]; exact hyM
    · rintro ⟨hy'U, hy'M⟩
      refine ⟨_, hy'M, ?_⟩
      have hU := hMU hy'M
      apply Subtype.ext
      change PX'.smoothVal _ = PX'.smoothVal y'
      rw [hd.smoothVal_smoothFwd b₀ hU, hd.smoothVal_smoothBwd a₀ hy'U, hd.right_inv _ hy'U]
  rw [he]
  exact (hd.continuousOn_smoothBwd a₀).isOpen_inter_preimage
    (hd.isScSmoothOn_inv.isOpen.preimage PX'.continuous_smoothVal) hM

end MPolyfold.IsScDiffeoOn

end Loc

/-! ### Open saturations in `O_f` and `X_∞` -/

section Sat

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpGroupoid

/-- **`X_∞ → |X_∞|` is an open map**: the saturation of an open subset of `X_∞` is open (near
`t(φ)`, `y ↦ s((t|sheet)⁻¹ y)` is continuous on the smooth level). -/
theorem isOpenMap_quotMk_smooth : IsOpenMap (Quot.mk X.SmoothRel) := by
  intro S hS
  refine isQuotientMap_quot_mk.isOpen_preimage.1 (isOpen_iff_mem_nhds.2 ?_)
  rintro y₀ ⟨x, hxS, hx⟩
  obtain ⟨φ, h1, h2⟩ := EpGroupoid.smoothRel_of_quot_eq hx
  have hy₀T : X.PObj.smoothVal y₀ ∈ (X.sheetAt φ).tgtSet := EpStrongBundle.mem_tgtSet h2
  set G := (EpStrongBundle.isScDiffeoOn_morBase (X := X) φ).smoothFwd y₀ with hG
  have hGc : ContinuousAt G y₀ :=
    ((EpStrongBundle.isScDiffeoOn_morBase (X := X) φ).continuousOn_smoothFwd y₀).continuousAt
      ((((X.sheetAt φ).isScDiffeoOn_tgt.isOpen_target).preimage
        X.PObj.continuous_smoothVal).mem_nhds hy₀T)
  have hGy₀ : G y₀ = x := by
    apply Subtype.ext
    change X.PObj.smoothVal _ = X.PObj.smoothVal x
    rw [(EpStrongBundle.isScDiffeoOn_morBase (X := X) φ).smoothVal_smoothFwd y₀ hy₀T]
    change X.src ((X.sheetAt φ).tgtInv _) = _
    rw [← h2, EpStrongBundle.tgtInv_tgt, h1]
  filter_upwards [hGc (hS.mem_nhds (hGy₀ ▸ hxS)),
    (((X.sheetAt φ).isScDiffeoOn_tgt.isOpen_target).preimage
      X.PObj.continuous_smoothVal).mem_nhds hy₀T] with y hyS hyT
  refine ⟨G y, hyS, Quot.sound ⟨(X.sheetAt φ).tgtInv (X.PObj.smoothVal y), ?_,
    (X.sheetAt φ).isScDiffeoOn_tgt.right_inv _ hyT⟩⟩
  rw [(EpStrongBundle.isScDiffeoOn_morBase (X := X) φ).smoothVal_smoothFwd y₀ hyT]; rfl

end EpGroupoid

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B)

variable {f : Obj → W} (hF : E.IsScFredholmSectionFunctor f) (hsec : B.HasScPlusSectionsThrough)

/-- The value of the carried section of `morIso φ` at `y'` is `(t|sheet)⁻¹(y')_*` of the value at
any point `z` equal to `ϕ(y')`. -/
theorem orMor_tgtInv_eq_pullOrx (φ : Mor) {y' : Obj} (hy' : y' ∈ (X.sheetAt φ).tgtSet) {z : Obj}
    (hz : X.src ((X.sheetAt φ).tgtInv y') = z) (hzs : z ∈ X.PObj.smoothSet)
    (hs' : y' ∈ X.PObj.smoothSet) (o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy) :
    E.orMor hF hsec ((X.sheetAt φ).tgtInv y') hz ((X.sheetAt φ).isScDiffeoOn_tgt.right_inv y' hy')
      hzs hs' (o z hzs) =
      (E.morIso φ).pullOrx hF.2 hF.2 (E.eqOn_morIso_of_functor hF φ) hsec hsec o y' hs' := by
  subst hz
  exact (E.pullOrx_morIso_eq_orMor hF hsec φ hy' hzs hs' o).symm

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
  (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (hfT : B.IsScFredholmSectionTame f)

/-- **The saturation of an open subset of `O_f` is open** (Part I's topology): near a point
`(y₀, φ_* ω)` with `(x, ω) ∈ S`, the continuous orientation through `(x, ω)` is carried by the
isomorphism of `φ` (Theorem 12.5.3, last sentence) to one through `(y₀, φ_* ω)`, whose points
`(y, σ'_* ô_z)` come from points `(z, ô_z) ∈ S`. -/
theorem isOpen_orSat {S : Set (OrSpace f hF.2)}
    (hS : IsOpen[orTopology (orLocalTransport hX hbump hfT hsec)] S) :
    IsOpen[orTopology (orLocalTransport hX hbump hfT hsec)]
      (Quot.mk (E.OrRel hF hsec) ⁻¹' (Quot.mk (E.OrRel hF hsec) '' S)) := by
  intro U'' o'' h''
  refine isOpen_iff_mem_nhds.2 fun y₀ ⟨hy₀U, p, hpS, hp⟩ => ?_
  obtain ⟨φ, hz, hy, hφ⟩ := E.orRel_of_quot_eq hF hsec hp
  obtain ⟨Û, ô, hô, -, hpô⟩ := exists_isContOrOn (orLocalTransport hX hbump hfT hsec) p
  obtain ⟨hC, hmem, hval⟩ := E.theorem_12_5_3_push_hyp hF hsec hX hbump hfT φ hz hy
    (X.PObj.smoothVal_mem _) (X.PObj.smoothVal_mem y₀) hô
  have hy₀C := hmem hpô.1
  have hy₀T : X.PObj.smoothVal y₀ ∈ (X.sheetAt φ).tgtSet := hy₀C.1
  have hy' : X.tgt φ = X.PObj.smoothVal y₀ := hy
  set C := (E.morIso φ).pullOrx hF.2 hF.2 (E.eqOn_morIso_of_functor hF φ) hsec hsec ô with hCdef
  have hCy₀ : C (X.PObj.smoothVal y₀) (X.PObj.smoothVal_mem y₀) =
      o'' (X.PObj.smoothVal y₀) (X.PObj.smoothVal_mem y₀) := by
    refine hval.trans ?_
    rw [← hpô.2]; exact hφ
  set G := (isScDiffeoOn_morBase (X := X) φ).smoothFwd y₀ with hG
  have hGc : ContinuousAt G y₀ :=
    ((isScDiffeoOn_morBase (X := X) φ).continuousOn_smoothFwd y₀).continuousAt
      ((((X.sheetAt φ).isScDiffeoOn_tgt.isOpen_target).preimage
        X.PObj.continuous_smoothVal).mem_nhds
      hy₀T)
  have hGy₀ : G y₀ = p.1 := by
    apply Subtype.ext
    change X.PObj.smoothVal _ = X.PObj.smoothVal p.1
    rw [hG, (isScDiffeoOn_morBase (X := X) φ).smoothVal_smoothFwd y₀ hy₀T]
    exact E.morIso_ϕ_eq hz hy'
  set M := {z : X.PObj.SmoothLevel | X.PObj.smoothVal z ∈ Û ∧ orSec ô z ∈ S} with hM
  have hMo : IsOpen M := hS Û ô hô
  have hpM : p.1 ∈ M := ⟨hpô.1, by rw [← eq_orSec_of_mem_orBasic hpô]; exact hpS⟩
  filter_upwards [hC.eventually_iff h'' hy₀C hy₀U, hGc (hMo.mem_nhds (hGy₀ ▸ hpM))]
    with y ⟨hyC, hyU, hiff⟩ hyM
  refine ⟨hyU, orSec ô (G y), hyM.2, Quot.sound ⟨(X.sheetAt φ).tgtInv (X.PObj.smoothVal y), ?_,
    (X.sheetAt φ).isScDiffeoOn_tgt.right_inv _ hyC.1, ?_⟩⟩
  · change _ = X.PObj.smoothVal (G y)
    rw [hG, (isScDiffeoOn_morBase (X := X) φ).smoothVal_smoothFwd y₀ hyC.1]; rfl
  · exact (E.orMor_tgtInv_eq_pullOrx hF hsec φ hyC.1 _ _ _ ô).trans (hiff.2 hCy₀)

/-- **`O_f → |O_f|` is an open map** (Part I's topology and the quotient topology). -/
theorem isOpenMap_quotMk_or :
    @IsOpenMap _ _ (orTopology (orLocalTransport hX hbump hfT hsec))
      (@instTopologicalSpaceQuot _ _ (orTopology (orLocalTransport hX hbump hfT hsec)))
      (Quot.mk (E.OrRel hF hsec)) := by
  let := orTopology (orLocalTransport hX hbump hfT hsec)
  exact fun S hS => isQuotientMap_quot_mk.isOpen_preimage.1 (E.isOpen_orSat hF hsec hX hbump hfT hS)

end EpStrongBundle

end Sat

/-! ### One strong bundle equivalence -/

section Equiv

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}

namespace EpStrongBundle.IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ)

/-- `ϕ : X_∞ → X'_∞` is continuous. -/
theorem continuous_smoothMap : Continuous h.smoothMap :=
  ϕ.isScSmoothMap_obj.continuous_smoothLevel fun _ => rfl

/-- `ϕ : X_∞ → X'_∞` is open (a local homeomorphism: on `U(a)_∞` it is `smoothFwd` of the local
strong bundle isomorphism at `a`). -/
theorem isOpenMap_smoothMap : IsOpenMap h.smoothMap := by
  intro M hM
  have he : h.smoothMap '' M = ⋃ a : X.PObj.SmoothLevel,
      (h.locIso (X.PObj.smoothVal a)).base.smoothFwd (h.smoothMap a) ''
        (M ∩ X.PObj.smoothVal ⁻¹' h.locSet (X.PObj.smoothVal a)) := by
    ext y'
    simp only [mem_image, mem_iUnion, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨y, hyM, rfl⟩
      refine ⟨y, y, ⟨hyM, h.mem_locSet _⟩, ?_⟩
      apply Subtype.ext
      change X'.PObj.smoothVal _ = X'.PObj.smoothVal (h.smoothMap y)
      rw [(h.locIso _).base.smoothVal_smoothFwd _ (h.mem_locSet _)]; rfl
    · rintro ⟨a, y, ⟨hyM, hyU⟩, rfl⟩
      refine ⟨y, hyM, ?_⟩
      apply Subtype.ext
      change X'.PObj.smoothVal (h.smoothMap y) = X'.PObj.smoothVal _
      rw [(h.locIso _).base.smoothVal_smoothFwd _ hyU]; rfl
  rw [he]
  exact isOpen_iUnion fun a => (h.locIso _).base.isOpen_image_smoothFwd _
    (hM.inter ((h.isOpen_locSet _).preimage X.PObj.continuous_smoothVal)) inter_subset_right

/-- **`|ϕ| : |X_∞| → |X'_∞|` is a homeomorphism.** -/
def smoothOrbitHomeo : Quot X.SmoothRel ≃ₜ Quot X'.SmoothRel :=
  (Equiv.ofBijective _ h.smoothOrbitMap_bijective).toHomeomorphOfContinuousOpen
    (continuous_quot_lift _ (continuous_quot_mk.comp h.continuous_smoothMap))
    (by
      intro S hS
      have he : h.smoothOrbitMap '' S = Quot.mk X'.SmoothRel ''
          (h.smoothMap '' (Quot.mk X.SmoothRel ⁻¹' S)) := by
        ext c
        constructor
        · rintro ⟨d, hdS, rfl⟩
          induction d using Quot.ind with
          | mk y => exact ⟨h.smoothMap y, ⟨y, hdS, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨y, hyS, rfl⟩, rfl⟩
          exact ⟨Quot.mk _ y, hyS, rfl⟩
      change IsOpen (h.smoothOrbitMap '' S)
      rw [he]
      exact EpGroupoid.isOpenMap_quotMk_smooth _ (h.isOpenMap_smoothMap _
        (hS.preimage continuous_quot_mk)))

theorem smoothOrbitHomeo_apply (c : Quot X.SmoothRel) :
    h.smoothOrbitHomeo c = h.smoothOrbitMap c := rfl

section Orbit

variable {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpb : f = h.pullback f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)

/-- On the points of a pulled-back orientation, `(a, o) ↦ (ϕ(a), orEqv⁻¹ o)` is
`y ↦ (ϕ(y), o'_{ϕ(y)})`. -/
theorem orSpaceMap_orSec_pullOr (o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs)
    (y : X.PObj.SmoothLevel) :
    h.orSpaceMap hF hF' hpb hsec hsec' (orSec (h.pullOr hF hF' hpb hsec hsec' o') y) =
      orSec o' (h.smoothMap y) :=
  Sigma.ext rfl (heq_of_eq (Equiv.symm_apply_apply _ _))

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj')]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin n → ℝ) × Obj' → Obj'))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj'))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P' (Prod.snd : (Fin n → ℝ) × Obj' → Obj'))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj') → (Fin n → ℝ) × Obj'))]
  (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (hfT : B.IsScFredholmSectionTame f)
  (hX' : X'.PObj.IsTame) (hbump' : X'.PObj.AdmitsBumpFunctions)
  (hfT' : B'.IsScFredholmSectionTame f')

/-- **`O_f → O_{f'}`, `(a, o) ↦ (ϕ(a), orEqv⁻¹ o)`, is continuous** (Part I's topologies). -/
theorem continuous_orSpaceMap :
    @Continuous _ _ (orTopology (orLocalTransport hX hbump hfT hsec))
      (orTopology (orLocalTransport hX' hbump' hfT' hsec'))
      (h.orSpaceMap hF hF' hpb hsec hsec') := by
  let := orTopology (orLocalTransport hX hbump hfT hsec)
  let := orTopology (orLocalTransport hX' hbump' hfT' hsec')
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨U', o', ho', -, hp'⟩ := exists_isContOrOn (orLocalTransport hX' hbump' hfT' hsec')
    (h.orSpaceMap hF hF' hpb hsec hsec' p)
  have hc := h.isContOrOn_pullOr_hyp hF hF' hpb hsec hsec' hX hbump hfT hX' hbump' hfT' ho'
  have hpB : p ∈ orBasic (ϕ.obj ⁻¹' U') (h.pullOr hF hF' hpb hsec hsec' o') :=
    ⟨hp'.1, (Equiv.symm_apply_eq _).1 hp'.2⟩
  have heq : EqOn (fun q => orSec o' (h.smoothMap q.1)) (h.orSpaceMap hF hF' hpb hsec hsec')
      (orBasic (ϕ.obj ⁻¹' U') (h.pullOr hF hF' hpb hsec hsec' o')) := fun q hq => by
    conv_rhs => rw [eq_orSec_of_mem_orBasic hq]
    exact (h.orSpaceMap_orSec_pullOr hF hF' hpb hsec hsec' o' q.1).symm
  have hcont : ContinuousOn (fun q : OrSpace f hF.2 => orSec o' (h.smoothMap q.1))
      (orBasic (ϕ.obj ⁻¹' U') (h.pullOr hF hF' hpb hsec hsec' o')) :=
    (continuousOn_orSec ho').comp
      (h.continuous_smoothMap.comp
        (continuous_orProj (orLocalTransport hX hbump hfT hsec))).continuousOn
      fun q hq => hq.1
  exact (hcont.congr heq.symm).continuousAt ((isOpen_orBasic hc).mem_nhds hpB)

/-- **`O_f → O_{f'}` is an open map** (Part I's topologies): the image of an open `S` meets the
set of every continuous orientation `o''` of `f'` in an open set, the image under `ϕ` of the open
set where `(y, (pullOr o'')_y) ∈ S`. -/
theorem isOpenMap_orSpaceMap :
    @IsOpenMap _ _ (orTopology (orLocalTransport hX hbump hfT hsec))
      (orTopology (orLocalTransport hX' hbump' hfT' hsec'))
      (h.orSpaceMap hF hF' hpb hsec hsec') := by
  let := orTopology (orLocalTransport hX hbump hfT hsec)
  let := orTopology (orLocalTransport hX' hbump' hfT' hsec')
  intro S hS U'' o'' h''
  refine isOpen_iff_mem_nhds.2 fun y₀ ⟨hy₀U, p, hpS, hp⟩ => ?_
  have h1 : h.smoothMap p.1 = y₀ := congrArg Sigma.fst hp
  subst h1
  have h2 : (h.orEqv hF hF' hpb hsec hsec' _ (X.PObj.smoothVal_mem p.1)).symm p.2 =
      o'' (X'.PObj.smoothVal (h.smoothMap p.1)) (X'.PObj.smoothVal_mem _) :=
    eq_of_heq (Sigma.mk.inj_iff.1 hp).2
  have hc := h.isContOrOn_pullOr_hyp hF hF' hpb hsec hsec' hX hbump hfT hX' hbump' hfT' h''
  set a := X.PObj.smoothVal p.1
  set M := {y : X.PObj.SmoothLevel | X.PObj.smoothVal y ∈ ϕ.obj ⁻¹' U'' ∧
      orSec (h.pullOr hF hF' hpb hsec hsec' o'') y ∈ S} ∩
    X.PObj.smoothVal ⁻¹' h.locSet a with hM
  have hMo : IsOpen M :=
    (hS _ _ hc).inter ((h.isOpen_locSet a).preimage X.PObj.continuous_smoothVal)
  have hpp : orSec (h.pullOr hF hF' hpb hsec hsec' o'') p.1 = p :=
    Sigma.ext rfl (heq_of_eq ((Equiv.symm_apply_eq _).1 h2).symm)
  have hpM : p.1 ∈ M := ⟨⟨hy₀U, by rw [hpp]; exact hpS⟩, h.mem_locSet a⟩
  have himg : IsOpen ((h.locIso a).base.smoothFwd (h.smoothMap p.1) '' M) :=
    (h.locIso a).base.isOpen_image_smoothFwd _ hMo fun y hy => hy.2
  have hfw : ∀ y ∈ M, (h.locIso a).base.smoothFwd (h.smoothMap p.1) y = h.smoothMap y := by
    intro y hy
    apply Subtype.ext
    change X'.PObj.smoothVal _ = X'.PObj.smoothVal (h.smoothMap y)
    rw [(h.locIso a).base.smoothVal_smoothFwd _ hy.2]; rfl
  refine mem_of_superset (himg.mem_nhds ⟨p.1, hpM, hfw _ hpM⟩) ?_
  rintro _ ⟨y, hyM, rfl⟩
  rw [hfw y hyM]
  exact ⟨hyM.1.1, _, hyM.1.2, h.orSpaceMap_orSec_pullOr hF hF' hpb hsec hsec' o'' y⟩

/-- **`|Φ|_* : |O_f| → |O_{f'}|` is a homeomorphism** (Theorem 12.5.7 (1) for one strong bundle
equivalence; Part I's topology on `O_f`, `O_{f'}` and the quotient topologies). -/
def orbitOrHomeo :
    @Homeomorph (Quot (E.OrRel hF hsec)) (Quot (E'.OrRel hF' hsec'))
      (@instTopologicalSpaceQuot _ _ (orTopology (orLocalTransport hX hbump hfT hsec)))
      (@instTopologicalSpaceQuot _ _ (orTopology (orLocalTransport hX' hbump' hfT' hsec'))) :=
  letI := orTopology (orLocalTransport hX hbump hfT hsec)
  letI := orTopology (orLocalTransport hX' hbump' hfT' hsec')
  (Equiv.ofBijective _ (h.orbitOrMap_bijective hF hF' hpb hsec hsec')).toHomeomorphOfContinuousOpen
    (continuous_quot_lift _ (continuous_quot_mk.comp
      (h.continuous_orSpaceMap hF hF' hpb hsec hsec' hX hbump hfT hX' hbump' hfT')))
    (by
      intro S hS
      have he : h.orbitOrMap hF hF' hpb hsec hsec' '' S = Quot.mk (E'.OrRel hF' hsec') ''
          (h.orSpaceMap hF hF' hpb hsec hsec' '' (Quot.mk (E.OrRel hF hsec) ⁻¹' S)) := by
        ext c
        constructor
        · rintro ⟨d, hdS, rfl⟩
          induction d using Quot.ind with
          | mk y => exact ⟨h.orSpaceMap hF hF' hpb hsec hsec' y, ⟨y, hdS, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨y, hyS, rfl⟩, rfl⟩
          exact ⟨Quot.mk _ y, hyS, rfl⟩
      change IsOpen (h.orbitOrMap hF hF' hpb hsec hsec' '' S)
      rw [he]
      exact E'.isOpenMap_quotMk_or hF' hsec' hX' hbump' hfT' _
        (h.isOpenMap_orSpaceMap hF hF' hpb hsec hsec' hX hbump hfT hX' hbump' hfT' _
          (hS.preimage continuous_quot_mk)))

theorem orbitOrHomeo_apply (c : Quot (E.OrRel hF hsec)) :
    h.orbitOrHomeo hF hF' hpb hsec hsec' hX hbump hfT hX' hbump' hfT' c =
      h.orbitOrMap hF hF' hpb hsec hsec' c := rfl

end Orbit

end EpStrongBundle.IsStrongBundleEquivalence

end Equiv

end Polyfold
