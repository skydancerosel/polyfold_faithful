import Polyfold.Chapter12.LocalOrientationEquivalenceComp
import Polyfold.Chapter12.OrientationOrbitHomeo

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597: **Theorem 12.5.7** for a representative `W ←Φ₁– V –Φ₂→ W'`, with the topology, for
the linearizations made with local sc⁺-sections.

# Theorem 12.5.7 with tame object spaces and tame germ data only

## The text, paraphrased

(Theorem 12.5.7) Let `P : W → X` and `P' : W' → X'` be strong bundles over tame ep-groupoids,
`f`, `f'` sc-Fredholm section functors and `𝔣 : W → W'` a generalized strong bundle isomorphism
with `𝔣_* f = f'`.  (1) `𝔣` induces a homeomorphism `|O_f| → |O_{f'}|` fitting into a commutative
square with `|σ|`, `|σ'|` and the homeomorphism `|X_∞| → |X'_∞|`.  (2) If `o` is an orientation
of `f` (Definition 12.5.4), there is a unique push-forward orientation `o'` of `f'`.

## What is formalized

For a representative `W ←Φ₁– V –Φ₂→ W'` (two strong bundle equivalences) and section functors
with `Φ₁^* f = f'' = Φ₂^* f'`; the orientation sets are the local ones (`OrxLoc`), the topology
of `O_f` is that of `theorem_12_5_3_loc`, and the hypotheses are: tame object M-polyfolds of
`X`, `X'`, `V` and tame germ data of `f`, `f'`, `f''`.  No sc-smooth bump functions and no
sc⁺-sections over the whole object space are assumed.

* `EpStrongBundle.isOpen_orSatLoc_of_isOpen`, `isOpenMap_quotMk_orLoc`: the saturation of an
  open subset of `O_f` is open; `O_f → |O_f|` is an open map.
* For one strong bundle equivalence: `isContOn_pullOrLoc` (the pull-back of a continuous family
  of orientations is continuous), `isContOn_pushOrLoc` (the push-forward of an invariant
  continuous family is continuous), `continuous_orSpaceMapLoc`, `isOpenMap_orSpaceMapLoc`,
  `orbitOrHomeoLoc : |O_f| ≃ₜ |O_{f'}|`.
* `theorem_12_5_7_one_loc`: **Theorem 12.5.7 (1)**: homeomorphisms `|O_f| ≃ₜ |O_{f'}|` and
  `|X_∞| ≃ₜ |X'_∞|` commuting with `|σ|`, `|σ'|` and with the maps of the diagram.
* `theorem_12_5_7_two_loc_cont`, `theorem_12_5_7_two_loc`: **Theorem 12.5.7 (2)**: an
  orientation `o` of `f` (Definition 12.5.4) has exactly one invariant family `o'` of
  orientations of `f'` corresponding to `o` over `V`, and `o'` is an orientation of `f'`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr StrongBundle.LocalIso

universe u

/-! ### The saturation of an open set of orientations -/

section Sat

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}
  (hX : X.PObj.IsTame) (hF : E.IsScFredholmSectionFunctor f)
  (hfT : B.IsScFredholmSectionTame f)

/-- **The saturation of an open subset of `O_f` is open**: near a point `(y₀, φ_* ω)` with
`(x, ω) ∈ S`, the continuous family of orientations through `(x, ω)` is carried by the
isomorphism of `φ` (Theorem 12.5.3, last sentence) to one through `(y₀, φ_* ω)`, whose points
`(y, τ_* ô_z)` come from points `(z, ô_z) ∈ S`. -/
theorem isOpen_orSatLoc_of_isOpen {S : Set (OrSpaceLoc hX hfT)}
    (hS : IsOpen[orTopologyLoc hX hfT] S) :
    IsOpen[orTopologyLoc hX hfT]
      (Quot.mk (E.OrRelLoc hX hF hfT) ⁻¹' (Quot.mk (E.OrRelLoc hX hF hfT) '' S)) := by
  intro U'' o'' h''
  refine isOpen_iff_mem_nhds.2 fun y₀ ⟨hy₀U, p, hpS, hp⟩ => ?_
  obtain ⟨φ, hz, hy, hφ⟩ := E.orRelLoc_of_quot_eq hX hF hfT hp
  obtain ⟨Û, ô, hô, -, hpô⟩ := (orLocalTransportLoc hX hfT).exists_isContOn p
  obtain ⟨V', o', hy₀V', hV'T, hcont', hval₀, hval⟩ := E.theorem_12_5_3_push_loc hX hF hfT φ hz
    hy (X.PObj.smoothVal_mem p.1) (X.PObj.smoothVal_mem y₀) hô hpô.1
  have hy₀T : X.PObj.smoothVal y₀ ∈ (X.sheetAt φ).tgtSet := hV'T hy₀V'
  have hy' : X.tgt φ = X.PObj.smoothVal y₀ := hy
  have hCy₀ : o' (X.PObj.smoothVal y₀) (X.PObj.smoothVal_mem y₀) =
      o'' (X.PObj.smoothVal y₀) (X.PObj.smoothVal_mem y₀) := by
    refine hval₀.trans ?_
    rw [← hpô.2]; exact hφ
  set G := (isScDiffeoOn_morBase (X := X) φ).smoothFwd y₀ with hG
  have hGc : ContinuousAt G y₀ :=
    ((isScDiffeoOn_morBase (X := X) φ).continuousOn_smoothFwd y₀).continuousAt
      ((((X.sheetAt φ).isScDiffeoOn_tgt.isOpen_target).preimage
        X.PObj.continuous_smoothVal).mem_nhds hy₀T)
  have hGy₀ : G y₀ = p.1 := by
    apply Subtype.ext
    change X.PObj.smoothVal _ = X.PObj.smoothVal p.1
    rw [hG, (isScDiffeoOn_morBase (X := X) φ).smoothVal_smoothFwd y₀ hy₀T]
    exact E.morIso_ϕ_eq hz hy'
  set M := {z : X.PObj.SmoothLevel | X.PObj.smoothVal z ∈ Û ∧
    (orLocalTransportLoc hX hfT).sec ô z ∈ S} with hM
  have hMo : IsOpen M := hS Û ô hô
  have hpM : p.1 ∈ M :=
    ⟨hpô.1, by rw [← LocalTransport.eq_sec_of_mem_basic hpô]; exact hpS⟩
  filter_upwards [hcont'.eventually_iff h'' hy₀V' hy₀U, hGc (hMo.mem_nhds (hGy₀ ▸ hpM))]
    with y ⟨hyV', hyU, hiff⟩ hyM
  have hyT : X.PObj.smoothVal y ∈ (X.sheetAt φ).tgtSet := hV'T hyV'
  have hτ : (X.sheetAt φ).tgtInv (X.PObj.smoothVal y) ∈ (X.sheetAt φ).carrier :=
    (X.sheetAt φ).isScDiffeoOn_tgt.mapsTo_inv hyT
  have hτt : X.tgt ((X.sheetAt φ).tgtInv (X.PObj.smoothVal y)) = X.PObj.smoothVal y :=
    (X.sheetAt φ).isScDiffeoOn_tgt.right_inv _ hyT
  have hsrc : X.src ((X.sheetAt φ).tgtInv (X.PObj.smoothVal y)) = X.PObj.smoothVal (G y) := by
    rw [hG, (isScDiffeoOn_morBase (X := X) φ).smoothVal_smoothFwd y₀ hyT]; rfl
  refine ⟨hyU, (orLocalTransportLoc hX hfT).sec ô (G y), hyM.2,
    Quot.sound ⟨(X.sheetAt φ).tgtInv (X.PObj.smoothVal y), hsrc, hτt, ?_⟩⟩
  exact ((hval _ hτ hsrc hτt (X.PObj.smoothVal_mem (G y)) (X.PObj.smoothVal_mem y)
    hyV').2).symm.trans (hiff.2 hCy₀)

/-- **`O_f → |O_f|` is an open map** (the topology of Theorem 12.5.3 and the quotient
topology). -/
theorem isOpenMap_quotMk_orLoc :
    @IsOpenMap _ _ (orTopologyLoc hX hfT)
      (@instTopologicalSpaceQuot _ _ (orTopologyLoc hX hfT))
      (Quot.mk (E.OrRelLoc hX hF hfT)) := by
  let := orTopologyLoc hX hfT
  exact fun S hS => isQuotientMap_quot_mk.isOpen_preimage.1
    (E.isOpen_orSatLoc_of_isOpen hX hF hfT hS)

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
  {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpb : f = h.pullback f')
  (hX : X.PObj.IsTame) (hX' : X'.PObj.IsTame) (hfT : B.IsScFredholmSectionTame f)
  (hfT' : B'.IsScFredholmSectionTame f')

/-- On `U(a)` the pull-back `pullOrLoc o'` is the family carried by the local strong bundle
isomorphism of `Φ` at `a`. -/
theorem pullOrLoc_eq_pullLoc (a : Obj) (o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), OrxLoc hfT' x hs)
    {b : Obj} (hb : b ∈ h.locSet a) (hs : b ∈ X.PObj.smoothSet) :
    h.pullOrLoc hpb hfT hfT' o' b hs =
      (h.locIso a).pullLoc hfT hfT' (h.eqOn_loc hpb hfT'.isScSmooth.1 a) o' b hs :=
  (DFunLike.congr_fun (h.orEqvLoc_eq_orLoc hpb hfT hfT' a hb hs) _).trans
    ((h.locIso a).pullLoc_of_mem hfT hfT' (h.eqOn_loc hpb hfT'.isScSmooth.1 a) o' hb hs
      (h.smooth_obj hs)).symm

/-- **The pull-back of a continuous family of orientations is continuous** (Theorem 12.5.7, the
pull-back half of (2) for one equivalence): if `o'` is a continuous family of orientations of
`f'` over an open `V'`, then `pullOrLoc o'` is one of `f` over `ϕ⁻¹(V')`. -/
theorem isContOn_pullOrLoc {V' : Set Obj'}
    {o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), OrxLoc hfT' x hs}
    (ho' : (orLocalTransportLoc hX' hfT').IsContOn V' o') :
    (orLocalTransportLoc hX hfT).IsContOn (ϕ.obj ⁻¹' V') (h.pullOrLoc hpb hfT hfT' o') := by
  refine LocalTransport.isContOn_of_local
    (ho'.1.preimage (continuousOn_univ.1 ϕ.isScSmoothMap_obj.continuousOn)) fun a ha _ => ?_
  exact ⟨h.locSet a ∩ (h.locIso a).ϕ ⁻¹' V', ⟨h.mem_locSet a, ha⟩,
    ((h.locIso a).isContOn_pullLoc hX hX' hfT hfT' (h.eqOn_loc hpb hfT'.isScSmooth.1 a) ho').congr
      fun y hy hys => (h.pullOrLoc_eq_pullLoc hpb hfT hfT' a o' hy.1 hys).symm⟩

/-- **The push-forward of an invariant continuous family of orientations is continuous**
(Theorem 12.5.7, the push-forward half of (2), for one equivalence): if `o` is an invariant
continuous family of orientations of `f` over all of `X`, then `pushOrLoc o` is one of `f'`
over all of `X'`. -/
theorem isContOn_pushOrLoc {o : ∀ x (hs : x ∈ X.PObj.smoothSet), OrxLoc hfT x hs}
    (ho : E.IsOrInvariantLoc hF hfT o) (hoc : (orLocalTransportLoc hX hfT).IsContOn univ o) :
    (orLocalTransportLoc hX' hfT').IsContOn univ (h.pushOrLoc hF' hpb hfT hfT' o) := by
  set o' := h.pushOrLoc hF' hpb hfT hfT' o with ho'
  have hinv' := h.isOrInvariantLoc_pushOrLoc hF hF' hpb hfT hfT' ho
  -- near `ϕ(a)`
  have hnear : ∀ a, (orLocalTransportLoc hX' hfT').IsContOn (h.locSet' a ∩ univ) o' :=
    fun a => (h.locIso a).isContOn_of_pullLoc hX hX' hfT hfT'
      (h.eqOn_loc hpb hfT'.isScSmooth.1 a) isOpen_univ
      ((hoc.mono ((h.locIso a).base.isScSmoothOn.continuousOn.isOpen_inter_preimage
        (h.isOpen_locSet a) isOpen_univ) (subset_univ _)).congr fun y hy hys =>
          (h.pushOrLoc_obj hF hF' hpb hfT hfT' ho hys).symm.trans
            (h.pullOrLoc_eq_pullLoc hpb hfT hfT' a o' hy.1 hys))
  refine LocalTransport.isContOn_of_local isOpen_univ fun x' _ hs' => ?_
  obtain ⟨a, ha, ψ, h1, h2⟩ := h.exists_smooth_iso hs'
  obtain ⟨V', o'', hx'V', hV'T, hcont, -, hval⟩ := E'.theorem_12_5_3_push_loc hX' hF' hfT' ψ h1
    h2 (h.smooth_obj ha) hs' (hnear a) ⟨h.obj_mem_locSet' a, mem_univ _⟩
  refine ⟨V', hx'V', hcont.congr fun y' hy' hys' => ?_⟩
  have hyT : y' ∈ (X'.sheetAt ψ).tgtSet := hV'T hy'
  have hτ : (X'.sheetAt ψ).tgtInv y' ∈ (X'.sheetAt ψ).carrier :=
    (X'.sheetAt ψ).isScDiffeoOn_tgt.mapsTo_inv hyT
  have hτt : X'.tgt ((X'.sheetAt ψ).tgtInv y') = y' :=
    (X'.sheetAt ψ).isScDiffeoOn_tgt.right_inv _ hyT
  have hys : X'.src ((X'.sheetAt ψ).tgtInv y') ∈ X'.PObj.smoothSet :=
    (X'.mem_smoothSet_src_iff _).2 ((X'.mem_smoothSet_tgt_iff _).1 (hτt.symm ▸ hys'))
  exact ((hval _ hτ rfl hτt hys hys' hy').2).trans (hinv' _ rfl hτt hys hys')

/-- On the points of a pulled-back family, `(a, o) ↦ (ϕ(a), orEqvLoc⁻¹ o)` is
`y ↦ (ϕ(y), o'_{ϕ(y)})`. -/
theorem orSpaceMapLoc_sec_pullOrLoc
    (o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), OrxLoc hfT' x hs) (y : X.PObj.SmoothLevel) :
    h.orSpaceMapLoc hpb hX hX' hfT hfT'
        ((orLocalTransportLoc hX hfT).sec (h.pullOrLoc hpb hfT hfT' o') y) =
      (orLocalTransportLoc hX' hfT').sec o' (h.smoothMap y) :=
  Sigma.ext rfl (heq_of_eq (Equiv.symm_apply_apply _ _))

/-- **`O_f → O_{f'}`, `(a, o) ↦ (ϕ(a), orEqvLoc⁻¹ o)`, is continuous** (the topologies of
Theorem 12.5.3). -/
theorem continuous_orSpaceMapLoc :
    @Continuous _ _ (orTopologyLoc hX hfT) (orTopologyLoc hX' hfT')
      (h.orSpaceMapLoc hpb hX hX' hfT hfT') := by
  let := orTopologyLoc hX hfT
  let := orTopologyLoc hX' hfT'
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨U', o', ho', -, hp'⟩ := (orLocalTransportLoc hX' hfT').exists_isContOn
    (h.orSpaceMapLoc hpb hX hX' hfT hfT' p)
  have hc := h.isContOn_pullOrLoc hpb hX hX' hfT hfT' ho'
  have hpB : p ∈ (orLocalTransportLoc hX hfT).basic (ϕ.obj ⁻¹' U')
      (h.pullOrLoc hpb hfT hfT' o') := ⟨hp'.1, (Equiv.symm_apply_eq _).1 hp'.2⟩
  have heq : EqOn (fun q => (orLocalTransportLoc hX' hfT').sec o' (h.smoothMap q.1))
      (h.orSpaceMapLoc hpb hX hX' hfT hfT')
      ((orLocalTransportLoc hX hfT).basic (ϕ.obj ⁻¹' U') (h.pullOrLoc hpb hfT hfT' o')) :=
    fun q hq => by
      conv_rhs => rw [LocalTransport.eq_sec_of_mem_basic hq]
      exact (h.orSpaceMapLoc_sec_pullOrLoc hpb hX hX' hfT hfT' o' q.1).symm
  have hcont : ContinuousOn
      (fun q : OrSpaceLoc hX hfT => (orLocalTransportLoc hX' hfT').sec o' (h.smoothMap q.1))
      ((orLocalTransportLoc hX hfT).basic (ϕ.obj ⁻¹' U') (h.pullOrLoc hpb hfT hfT' o')) :=
    (LocalTransport.continuousOn_sec ho').comp
      (h.continuous_smoothMap.comp
        (orLocalTransportLoc hX hfT).continuous_proj).continuousOn fun q hq => hq.1
  exact (hcont.congr heq.symm).continuousAt ((LocalTransport.isOpen_basic hc).mem_nhds hpB)

/-- **`O_f → O_{f'}` is an open map** (the topologies of Theorem 12.5.3): the image of an open
`S` meets the set of every continuous family `o''` of orientations of `f'` in an open set, the
image under `ϕ` of the open set where `(y, (pullOrLoc o'')_y) ∈ S`. -/
theorem isOpenMap_orSpaceMapLoc :
    @IsOpenMap _ _ (orTopologyLoc hX hfT) (orTopologyLoc hX' hfT')
      (h.orSpaceMapLoc hpb hX hX' hfT hfT') := by
  let := orTopologyLoc hX hfT
  let := orTopologyLoc hX' hfT'
  intro S hS U'' o'' h''
  refine isOpen_iff_mem_nhds.2 fun y₀ ⟨hy₀U, p, hpS, hp⟩ => ?_
  have h1 : h.smoothMap p.1 = y₀ := congrArg Sigma.fst hp
  subst h1
  have h2 : (h.orEqvLoc hpb hfT hfT' _ (X.PObj.smoothVal_mem p.1)).symm p.2 =
      o'' (X'.PObj.smoothVal (h.smoothMap p.1)) (X'.PObj.smoothVal_mem _) :=
    eq_of_heq (Sigma.mk.inj_iff.1 hp).2
  have hc := h.isContOn_pullOrLoc hpb hX hX' hfT hfT' h''
  set a := X.PObj.smoothVal p.1
  set M := {y : X.PObj.SmoothLevel | X.PObj.smoothVal y ∈ ϕ.obj ⁻¹' U'' ∧
      (orLocalTransportLoc hX hfT).sec (h.pullOrLoc hpb hfT hfT' o'') y ∈ S} ∩
    X.PObj.smoothVal ⁻¹' h.locSet a with hM
  have hMo : IsOpen M :=
    (hS _ _ hc).inter ((h.isOpen_locSet a).preimage X.PObj.continuous_smoothVal)
  have hpp : (orLocalTransportLoc hX hfT).sec (h.pullOrLoc hpb hfT hfT' o'') p.1 = p :=
    Sigma.ext rfl (heq_of_eq ((Equiv.symm_apply_eq _).1 h2).symm)
  have hpM : p.1 ∈ M := ⟨⟨hy₀U, by rw [hpp]; exact hpS⟩, h.mem_locSet a⟩
  have himg : IsOpen ((h.locIso a).base.smoothFwd (h.smoothMap p.1) '' M) :=
    (h.locIso a).base.isOpen_image_smoothFwd _ hMo fun y hy => hy.2
  have hfw : ∀ y ∈ M, (h.locIso a).base.smoothFwd (h.smoothMap p.1) y = h.smoothMap y := by
    intro y hy
    apply Subtype.ext
    change X'.PObj.smoothVal _ = X'.PObj.smoothVal (h.smoothMap y)
    rw [(h.locIso a).base.smoothVal_smoothFwd _ hy.2]; rfl
  refine Filter.mem_of_superset (himg.mem_nhds ⟨p.1, hpM, hfw _ hpM⟩) ?_
  rintro _ ⟨y, hyM, rfl⟩
  rw [hfw y hyM]
  exact ⟨hyM.1.1, _, hyM.1.2, h.orSpaceMapLoc_sec_pullOrLoc hpb hX hX' hfT hfT' o'' y⟩

/-- **`|Φ|_* : |O_f| → |O_{f'}|` is a homeomorphism** (Theorem 12.5.7 (1) for one strong bundle
equivalence; the topologies of Theorem 12.5.3 on `O_f`, `O_{f'}` and the quotient
topologies). -/
def orbitOrHomeoLoc :
    @Homeomorph (Quot (E.OrRelLoc hX hF hfT)) (Quot (E'.OrRelLoc hX' hF' hfT'))
      (@instTopologicalSpaceQuot _ _ (orTopologyLoc hX hfT))
      (@instTopologicalSpaceQuot _ _ (orTopologyLoc hX' hfT')) :=
  letI := orTopologyLoc hX hfT
  letI := orTopologyLoc hX' hfT'
  (Equiv.ofBijective _
    (h.orbitOrMapLoc_bijective hF hF' hpb hX hX' hfT hfT')).toHomeomorphOfContinuousOpen
    (continuous_quot_lift _ (continuous_quot_mk.comp
      (h.continuous_orSpaceMapLoc hpb hX hX' hfT hfT')))
    (by
      intro S hS
      have he : h.orbitOrMapLoc hF hF' hpb hX hX' hfT hfT' '' S =
          Quot.mk (E'.OrRelLoc hX' hF' hfT') '' (h.orSpaceMapLoc hpb hX hX' hfT hfT' ''
            (Quot.mk (E.OrRelLoc hX hF hfT) ⁻¹' S)) := by
        ext c
        constructor
        · rintro ⟨d, hdS, rfl⟩
          induction d using Quot.ind with
          | mk y => exact ⟨h.orSpaceMapLoc hpb hX hX' hfT hfT' y, ⟨y, hdS, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨y, hyS, rfl⟩, rfl⟩
          exact ⟨Quot.mk _ y, hyS, rfl⟩
      change IsOpen (h.orbitOrMapLoc hF hF' hpb hX hX' hfT hfT' '' S)
      rw [he]
      exact E'.isOpenMap_quotMk_orLoc hX' hF' hfT' _
        (h.isOpenMap_orSpaceMapLoc hpb hX hX' hfT hfT' _ (hS.preimage continuous_quot_mk)))

theorem orbitOrHomeoLoc_apply (c : Quot (E.OrRelLoc hX hF hfT)) :
    h.orbitOrHomeoLoc hF hF' hpb hX hX' hfT hfT' c =
      h.orbitOrMapLoc hF hF' hpb hX hX' hfT hfT' c := rfl

end EpStrongBundle.IsStrongBundleEquivalence

end Equiv

/-! ### Theorem 12.5.7 for a representative `W ← V → W'` -/

section Diagram

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
  {Obj'' Mor'' : Type u} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor''] {X'' : EpGroupoid Obj'' Mor''}
  {W'' : Type u} [TopologicalSpace W''] [T2Space W''] [ParacompactSpace W''] {P'' : W'' → Obj''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
  {B'' : StrongBundle X''.PObj P''} [ParacompactSpace (pullbackSpace P'' X''.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {E'' : EpStrongBundle X'' B''}
  {ϕ₁ : EpFunctor X'' X} {Φ₁ : EpFunctor E''.toEpGroupoid E.toEpGroupoid}
  {ϕ₂ : EpFunctor X'' X'} {Φ₂ : EpFunctor E''.toEpGroupoid E'.toEpGroupoid}
  (h₁ : E''.IsStrongBundleEquivalence E ϕ₁ Φ₁) (h₂ : E''.IsStrongBundleEquivalence E' ϕ₂ Φ₂)
  {f : Obj → W} {f' : Obj' → W'} {f'' : Obj'' → W''} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hF'' : E''.IsScFredholmSectionFunctor f'')
  (hpb₁ : f'' = h₁.pullback f) (hpb₂ : f'' = h₂.pullback f')
  (hX : X.PObj.IsTame) (hX' : X'.PObj.IsTame) (hX'' : X''.PObj.IsTame)
  (hfT : B.IsScFredholmSectionTame f) (hfT' : B'.IsScFredholmSectionTame f')
  (hfT'' : B''.IsScFredholmSectionTame f'')

/-- **Theorem 12.5.7 (1)**, p. 595, with the topology, for the local orientation sets and a
representative `W ←Φ₁– V –Φ₂→ W'`: there are homeomorphisms `|O_f| ≃ₜ |O_{f'}|` and
`|X_∞| ≃ₜ |X'_∞|` with `|σ'| ∘ F = G ∘ |σ|`; they are the maps of the diagram,
`F ∘ |Φ₁|_* = |Φ₂|_*` and `G ∘ |ϕ₁| = |ϕ₂|`.  The topology of `O_f` is that of Theorem 12.5.3,
those of `|O_f|`, `|X_∞|` the quotient topologies.  Hypotheses: tame object M-polyfolds and
tame germ data for `W`, `W'` and `V`. -/
theorem theorem_12_5_7_one_loc :
    letI : TopologicalSpace (OrSpaceLoc hX hfT) := orTopologyLoc hX hfT
    letI : TopologicalSpace (OrSpaceLoc hX' hfT') := orTopologyLoc hX' hfT'
    ∃ (F : Quot (E.OrRelLoc hX hF hfT) ≃ₜ Quot (E'.OrRelLoc hX' hF' hfT'))
      (G : Quot X.SmoothRel ≃ₜ Quot X'.SmoothRel),
      (∀ c, E'.orbitProjLoc hX' hF' hfT' (F c) = G (E.orbitProjLoc hX hF hfT c)) ∧
      (∀ c, F (h₁.orbitOrMapLoc hF'' hF hpb₁ hX'' hX hfT'' hfT c) =
        h₂.orbitOrMapLoc hF'' hF' hpb₂ hX'' hX' hfT'' hfT' c) ∧
      ∀ v, G (h₁.smoothOrbitMap v) = h₂.smoothOrbitMap v := by
  let := orTopologyLoc hX hfT
  let := orTopologyLoc hX' hfT'
  let := orTopologyLoc hX'' hfT''
  set F₁ := h₁.orbitOrHomeoLoc hF'' hF hpb₁ hX'' hX hfT'' hfT
  set F₂ := h₂.orbitOrHomeoLoc hF'' hF' hpb₂ hX'' hX' hfT'' hfT'
  set G₁ := h₁.smoothOrbitHomeo
  set G₂ := h₂.smoothOrbitHomeo
  refine ⟨F₁.symm.trans F₂, G₁.symm.trans G₂, fun c => ?_, fun c => ?_, fun v => ?_⟩
  · obtain ⟨d, rfl⟩ := F₁.surjective c
    rw [Homeomorph.trans_apply, Homeomorph.symm_apply_apply, Homeomorph.trans_apply]
    change E'.orbitProjLoc hX' hF' hfT' (h₂.orbitOrMapLoc hF'' hF' hpb₂ hX'' hX' hfT'' hfT' d) =
      G₂ (G₁.symm (E.orbitProjLoc hX hF hfT
        (h₁.orbitOrMapLoc hF'' hF hpb₁ hX'' hX hfT'' hfT d)))
    rw [h₂.orbitProjLoc_orbitOrMapLoc, h₁.orbitProjLoc_orbitOrMapLoc]
    change _ = G₂ (G₁.symm (G₁ _))
    rw [Homeomorph.symm_apply_apply]
    rfl
  · change F₂ (F₁.symm (F₁ c)) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  · change G₂ (G₁.symm (G₁ v)) = _
    rw [Homeomorph.symm_apply_apply]
    rfl

include hF'' hX'' in
/-- **Theorem 12.5.7 (2)**, p. 595, with the continuity read along paths, for the local
orientation sets and a representative `W ←Φ₁– V –Φ₂→ W'`: an invariant family `o` of
orientations of `f` which is continuous over all of `X` has exactly one invariant family `o'`
of orientations of `f'` corresponding to `o` over `V`, and `o'` is continuous over all of
`X'`. -/
theorem theorem_12_5_7_two_loc_cont {o : ∀ a (hs : a ∈ X.PObj.smoothSet), OrxLoc hfT a hs}
    (ho : E.IsOrInvariantLoc hF hfT o)
    (hoc : (orLocalTransportLoc hX hfT).IsContOn univ o) :
    ∃! o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), OrxLoc hfT' x hs,
      E'.IsOrInvariantLoc hF' hfT' o' ∧ (∀ v (hv : v ∈ X''.PObj.smoothSet),
        h₂.orEqvLoc hpb₂ hfT'' hfT' v hv (o' (ϕ₂.obj v) (h₂.smooth_obj hv)) =
          h₁.orEqvLoc hpb₁ hfT'' hfT v hv (o (ϕ₁.obj v) (h₁.smooth_obj hv))) ∧
        (orLocalTransportLoc hX' hfT').IsContOn univ o' := by
  have ho'' := h₁.isOrInvariantLoc_pullOrLoc hF'' hF hpb₁ hfT'' hfT ho
  have hc'' : (orLocalTransportLoc hX'' hfT'').IsContOn univ
      (h₁.pullOrLoc hpb₁ hfT'' hfT o) := by
    have := h₁.isContOn_pullOrLoc hpb₁ hX'' hX hfT'' hfT hoc
    rwa [preimage_univ] at this
  refine ⟨h₂.pushOrLoc hF' hpb₂ hfT'' hfT' (h₁.pullOrLoc hpb₁ hfT'' hfT o),
    ⟨h₂.isOrInvariantLoc_pushOrLoc hF'' hF' hpb₂ hfT'' hfT' ho'', fun v hv =>
      h₂.pushOrLoc_obj hF'' hF' hpb₂ hfT'' hfT' ho'' hv,
      h₂.isContOn_pushOrLoc hF'' hF' hpb₂ hX'' hX' hfT'' hfT' ho'' hc''⟩,
    fun o' ⟨ho', hoo, _⟩ => ?_⟩
  exact h₂.pushOrLoc_unique hF'' hF' hpb₂ hfT'' hfT' ho'' ho' hoo

include hF'' hX'' in
/-- **Theorem 12.5.7 (2)**, p. 595, as printed, for the local orientation sets and a
representative `W ←Φ₁– V –Φ₂→ W'`: if `o` is an orientation of `f` (Definition 12.5.4:
`x ↦ (x, o_x)` continuous for the topology of `O_f`, and invariant under morphisms), there is
exactly one family `o'` which is an orientation of `f'` (Definition 12.5.4) and corresponds to
`o` over `V` (`orEqvLoc₂ o'_{ϕ₂ v} = orEqvLoc₁ o_{ϕ₁ v}`).  Hypotheses: tame object
M-polyfolds and tame germ data for `W`, `W'` and `V`. -/
theorem theorem_12_5_7_two_loc {o : ∀ a (hs : a ∈ X.PObj.smoothSet), OrxLoc hfT a hs}
    (ho : E.definition_12_5_4_loc hX hF hfT o) :
    ∃! o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), OrxLoc hfT' x hs,
      E'.definition_12_5_4_loc hX' hF' hfT' o' ∧
        ∀ v (hv : v ∈ X''.PObj.smoothSet),
          h₂.orEqvLoc hpb₂ hfT'' hfT' v hv (o' (ϕ₂.obj v) (h₂.smooth_obj hv)) =
            h₁.orEqvLoc hpb₁ hfT'' hfT v hv (o (ϕ₁.obj v) (h₁.smooth_obj hv)) := by
  have hoc := ((E.definition_12_5_4_loc_iff hX hF hfT o).1 ho).1
  obtain ⟨o', ⟨hinv, hcorr, hc'⟩, huniq⟩ := theorem_12_5_7_two_loc_cont h₁ h₂ hF hF' hF'' hpb₁
    hpb₂ hX hX' hX'' hfT hfT' hfT'' ho.2 hoc
  refine ⟨o', ⟨(E'.definition_12_5_4_loc_iff hX' hF' hfT' o').2 ⟨hc', hinv⟩, hcorr⟩,
    fun o'' ⟨ho'', hcorr''⟩ => huniq o'' ⟨ho''.2, hcorr'',
      ((E'.definition_12_5_4_loc_iff hX' hF' hfT' o'').1 ho'').1⟩⟩

end Diagram

end Polyfold
