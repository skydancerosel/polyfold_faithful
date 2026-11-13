import Polyfold.Chapter12.OrientationBundleEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597: the chart-level part of **Theorem 12.5.7** (2017: Theorem 12.12): linearizations
and their determinant orientations carried along a local strong bundle isomorphism between two
*different* strong bundles.

# Chart points carried along a local strong bundle isomorphism `Y|U → Y'|U'`

`ChartPull` carries chart points along a local isomorphism `L : Y|U → Y|U'` of one strong
bundle (the action of a morphism).  The proof of Theorem 12.5.7 compares orientations along the
strong bundle equivalences `Φ : V → W` of a representative of a generalized strong bundle
isomorphism, which are local isomorphisms between different bundles.  This file repeats the
constructions in that generality.

* `LocalIso.mpullPt L p`: for a chart point `p` of `Y'` at `x = ϕ(a)` whose chart lies in `U'`,
  the chart point of `Y` at `a` of the transported chart (`LocalIso.transportChart`); same model,
  same retraction, same level-`1` point.  For `Y' = Y` it is `pullPt` (`mpullPt_eq_pullPt`).
* `linSet_mpullPt`: **if `f = Ψ ∘ f' ∘ ϕ` on `U`, then `Lin(f, a)` read in `mpullPt L p` is
  `Lin(f', x)` read in `p`.**
* `transferT_mpullPt`, `transferK_mpullPt`: the identifications between two carried chart points
  are those between the original ones.
* `GermAgree₄`, `transferT_mpullPt₄`, `transferK_mpullPt₄`: if two composites `L ∘ L₂` and
  `M ∘ M₂` of local isomorphisms (through possibly different intermediate bundles) agree near
  `b`, the identification between the two chart points at `b` they produce is the identity.
* Orientations: `morPull` (an orientation of `DET(f', x)` read in `p` is one of `DET(f, a)` read
  in `mpullPt L p`), `mmorT`/`mmorK` (the maps `T_xX' → T_aX` and `Y'_x → Y_a` read in chart
  points), `morVia` (the orientation map), `morVia_apply` (it is the conjugation by
  `mmorT`, `mmorK`), `mmorT_eq`/`morVia_eq` (independent of the intermediate chart point).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Module

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v' u₁ v₁ u₂ v₂

/-- The difference of two sc-operators is an sc-operator. -/
private theorem isScOperator_sub' {E F : ScBanach} {S T : E 0 →L[ℝ] F 0} (hS : IsScOperator S)
    (hT : IsScOperator T) : IsScOperator (S - T) := fun m => by
  obtain ⟨Sm, hSm⟩ := hS m
  obtain ⟨Tm, hTm⟩ := hT m
  exact ⟨Sm - Tm, fun x => by simp [hSm, hTm]⟩

section Mixed

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U : Set X} {U' : Set X'} (L : LocalIso B B' U U')

/-- **The chart point at `a` carried from a chart point `p` of `Y'` at `x = ϕ(a)`**: the chart
point of the transported chart `Ψ' ∘ Φ` (`transportChart`) with the level-`1` point of `p`. -/
def mpullPt {x : X'} {a : X} (p : ChartPoint B' x) (hsub : p.c.φ.source ⊆ U') (ha : a ∈ U)
    (hϕ : L.ϕ a = x) : ChartPoint B a where
  c := L.transportChart p.c hsub
  isChart := L.isChart_transportChart p.c hsub p.isChart
  mem_source := ⟨ha, by rw [Set.mem_preimage, hϕ]; exact p.mem_source⟩
  z := p.z
  toBase_z := by
    change p.c.φ.model.E.toBase 1 p.z = p.c.φ (L.ϕ a)
    rw [hϕ]; exact p.toBase_z

variable {x : X'} {a : X} (p : ChartPoint B' x) (hsub : p.c.φ.source ⊆ U') (ha : a ∈ U)
  (hϕ : L.ϕ a = x)

@[simp] lemma mpullPt_c : (L.mpullPt p hsub ha hϕ).c = L.transportChart p.c hsub := rfl

@[simp] lemma mpullPt_z : (L.mpullPt p hsub ha hϕ).z = p.z := rfl

lemma mpullPt_source : (L.mpullPt p hsub ha hϕ).c.φ.source = U ∩ L.ϕ ⁻¹' p.c.φ.source := rfl

/-! ### `Lin(f', x)` is carried to `Lin(f, a)` -/

variable {L p hsub ha hϕ}

/-- **The linearizations at `x` and at `a` differ by an sc⁺-operator** (mixed form of
`LocalIso.exists_isScPlusOp_pullPt`): for sc⁺-sections `s₀` of `Y'`, `s` of `Y` with
`(f' + s₀)(x) = 0` and `(f + s)(a) = 0`, the linearization of `f + s` read in the carried chart
point is that of `f' + s₀` in `p` plus an sc⁺-operator. -/
theorem exists_isScPlusOp_mpullPt (hf : B.IsScFredholmSection f)
    (hf' : B'.IsScFredholmSection f') (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (ha : a ∈ U)
    (hϕ : L.ϕ a = x) (hxs : x ∈ PX'.smoothSet) {s : X → Y} {s₀ : X' → Y'}
    (hs : B.IsScPlusSection s) (hs₀ : B'.IsScPlusSection s₀)
    (hz : IsZeroAt P (sectionAdd P f s) a) (hz₀ : IsZeroAt P' (sectionAdd P' f' s₀) x) :
    ∃ b : ↥p.T →L[ℝ] ↥p.K, p.IsScPlusOp b ∧ ∀ v,
      linAt p.c.U p.c.R ((L.transportChart p.c hsub).principal (sectionAdd P f s)) p.z v =
        linAt p.c.U p.c.R (p.c.principal (sectionAdd P' f' s₀)) p.z v + (b v : p.c.F 0) := by
  set q := L.mpullPt p hsub ha hϕ with hq
  have hfs := hf.isScSmooth
  have hfs' := hf'.isScSmooth
  have hfsec : IsSection P f := hfs.1
  have hfsec' : IsSection P' f' := hfs'.1
  have hg := hfs.sectionAdd hs
  have hg₀ := hfs'.sectionAdd hs₀
  have hk : IsSc1 p.c.U (p.c.principal f' ∘ r p.c.R) := hfs'.isSc1_principal_comp_r p.isChart
  have hg' : IsSc1 p.c.U ((L.transportChart p.c hsub).principal (sectionAdd P f s) ∘ r p.c.R) :=
    hg.isSc1_principal_comp_r q.isChart
  have hg₀' : IsSc1 p.c.U (p.c.principal (sectionAdd P' f' s₀) ∘ r p.c.R) :=
    hg₀.isSc1_principal_comp_r p.isChart
  have hl₁ : IsScSmooth (F := p.c.F.shift) p.c.U
      ((L.transportChart p.c hsub).principalLift s ∘ r p.c.R) :=
    (((hs.isScSmoothRetractMap_one q.isChart).comp_isScSmooth
      (q.c.isRetraction.baseRetraction q.c.relOpen) q.c.base_retract).snd
      q.c.relOpen.isScDomain).congr q.c.relOpen.isScDomain fun _ _ => rfl
  have hl₀ : IsScSmooth (F := p.c.F.shift) p.c.U (p.c.principalLift s₀ ∘ r p.c.R) :=
    (((hs₀.isScSmoothRetractMap_one p.isChart).comp_isScSmooth
      (p.c.isRetraction.baseRetraction p.c.relOpen) p.c.base_retract).snd
      p.c.relOpen.isScDomain).congr p.c.relOpen.isScDomain fun _ _ => rfl
  have hO : ∀ u ∈ p.c.U, r p.c.R u ∈ p.c.φ.model.O := fun u hu => p.c.r_mem_O hu
  have hO' : ∀ u ∈ p.c.U, r p.c.R u ∈ (L.transportChart p.c hsub).φ.model.O := fun u hu => by
    rw [L.transportChart_model_O]; exact p.c.r_mem_O hu
  have hkey : ∀ w ∈ (L.transportChart p.c hsub).φ.model.O,
      (L.transportChart p.c hsub).principal (sectionAdd P f s) w =
        (L.transportChart p.c hsub).principal f w +
          (L.transportChart p.c hsub).F.toBase 1 ((L.transportChart p.c hsub).principalLift s w) :=
      fun w hw => by
    rw [(L.transportChart p.c hsub).principal_sectionAdd hfsec hs.1 hw,
      hs.toBase_principalLift (L.isChart_transportChart p.c hsub p.isChart) hw]
  have hpf : ∀ w ∈ p.c.φ.model.O,
      (L.transportChart p.c hsub).principal f w = p.c.principal f' w :=
    fun w hw => L.principal_transportChart p.c hsub hfL hfsec' hw
  have e₁ := scDeriv_add_toBase_one_apply p.c.relOpen hk hg' hl₁.isSc1 (fun u hu =>
      (hkey (r p.c.R u) (hO' u hu)).trans
        (congrArg (· + p.c.F.toBase 1 ((L.transportChart p.c hsub).principalLift s (r p.c.R u)))
          (hpf (r p.c.R u) (hO u hu)))) p.mem_U
  have e₀ := scDeriv_add_toBase_one_apply p.c.relOpen hk hg₀' hl₀.isSc1 (fun u hu => by
      simp only [Function.comp_apply]
      rw [p.c.principal_sectionAdd hfsec' hs₀.1 (hO u hu),
        hs₀.toBase_principalLift p.isChart (hO u hu)]) p.mem_U
  set D := scDeriv (F := p.c.F.shift) p.c.U ((L.transportChart p.c hsub).principalLift s ∘ r p.c.R)
      p.z - scDeriv (F := p.c.F.shift) p.c.U (p.c.principalLift s₀ ∘ r p.c.R) p.z with hDdef
  have hD : IsScOperator (E := p.c.φ.model.E) (F := p.c.F.shift) D :=
    isScOperator_sub' (hl₁.isSc1.isSc1With_scDeriv.scOperator_deriv p.mem_U
      (p.z_mem_smoothLvl hxs))
      (hl₀.isSc1.isSc1With_scDeriv.scOperator_deriv p.mem_U (p.z_mem_smoothLvl hxs))
  have hsum : ∀ v, p.c.F.toBase 1 (D v) +
      scDeriv p.c.U (p.c.principal (sectionAdd P' f' s₀) ∘ r p.c.R) p.z v =
        scDeriv p.c.U ((L.transportChart p.c hsub).principal (sectionAdd P f s) ∘ r p.c.R) p.z v :=
    fun v => (show p.c.F.toBase 1 (D v) +
        scDeriv p.c.U (p.c.principal (sectionAdd P' f' s₀) ∘ r p.c.R) p.z v =
          scDeriv p.c.U (p.c.principal f' ∘ r p.c.R) p.z v + p.c.F.toBase 1
            (scDeriv (F := p.c.F.shift) p.c.U ((L.transportChart p.c hsub).principalLift s ∘
              r p.c.R) p.z v) by
      rw [e₀ v, hDdef, sub_apply, map_sub]; abel).trans (e₁ v).symm
  have hDK : ∀ v, p.c.F.toBase 1 (D v) ∈ p.K := fun v => by
    have hm := sub_mem (q.scDeriv_mem_K hg hz v) (p.scDeriv_mem_K hg₀ hz₀ v)
    rw [eq_sub_of_add_eq (hsum v)]
    exact hm
  let b : ↥p.T →L[ℝ] ↥p.K :=
    (((p.c.F.toBase 1).comp D).comp p.T.subtypeL).codRestrict p.K fun v => hDK v
  refine ⟨b, p.isScPlusOp_of_shift (p.isScSubspace_T hxs) (p.isScSubspace_K hxs) hD
    (fun v _ => hDK v) (fun v => rfl), fun v => ?_⟩
  exact (hsum v).symm.trans (add_comm _ _)

/-- **`Lin(f, a)` read in the carried chart point is `Lin(f', x)` read in `p`**, for
`f = Ψ ∘ f' ∘ ϕ` on `U` and sc⁺-sections through the smooth fibre points of both bundles. -/
theorem linSet_mpullPt (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) (has : a ∈ PX.smoothSet)
    (hxs : x ∈ PX'.smoothSet) :
    (L.mpullPt p hsub ha hϕ).linSet f = p.linSet f' := by
  obtain ⟨-, s₀, hs₀, hz₀, -⟩ := p.linSet_nonempty hf' hxs hsec'
  obtain ⟨-, s₁, hs₁, hz₁, -⟩ := (L.mpullPt p hsub ha hϕ).linSet_nonempty hf has hsec
  ext (T : ↥p.T →L[ℝ] ↥p.K)
  constructor
  · rintro ⟨s, hs, hz, a', ha', hT⟩
    let a'' : ↥p.T →L[ℝ] ↥p.K := a'
    have ha'' : p.IsScPlusOp a'' := ha'
    have h1 : ∀ v, (T v : p.c.F 0) = linAt p.c.U p.c.R ((L.transportChart p.c hsub).principal
      (sectionAdd P f s)) p.z v + (a'' v : p.c.F 0) := hT
    obtain ⟨b, hb, hbv⟩ := exists_isScPlusOp_mpullPt hf hf' hfL ha hϕ hxs hs hs₀ hz hz₀
    refine (p.mem_linSet_iff hf' hs₀ hz₀ T).2 ⟨b + a'', hb.add ha'', fun v => ?_⟩
    rw [h1 v, hbv v, add_apply, Submodule.coe_add]
    abel
  · intro hT
    obtain ⟨a', ha', hTa⟩ := (p.mem_linSet_iff hf' hs₀ hz₀ T).1 hT
    obtain ⟨b, hb, hbv⟩ := exists_isScPlusOp_mpullPt hf hf' hfL ha hϕ hxs hs₁ hs₀ hz₁ hz₀
    let a'' : ↥p.T →L[ℝ] ↥p.K := a' + (-1 : ℝ) • b
    have ha'' : p.IsScPlusOp a'' := ha'.add (hb.smul (-1))
    have key : ∀ v, (T v : p.c.F 0) = linAt p.c.U p.c.R ((L.transportChart p.c hsub).principal
        (sectionAdd P f s₁)) p.z v + (a'' v : p.c.F 0) := fun v => by
      rw [hTa v, hbv v]
      simp only [a'', add_apply, smul_apply, Submodule.coe_add, Submodule.coe_smul]
      module
    exact ⟨s₁, hs₁, hz₁, a'', ha'', key⟩

/-! ### The identifications between carried chart points -/

section Transfer

/-- The base derivatives between two carried chart points are those between the original ones. -/
theorem baseDeriv_mpullPt (L : LocalIso B B' U U') {p q : ChartPoint B' x}
    (hp : p.c.φ.source ⊆ U') (hq : q.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (v : p.c.φ.model.E 0) :
    (L.mpullPt p hp ha hϕ).baseDeriv (L.mpullPt q hq ha hϕ) v = p.baseDeriv q v := by
  set p' := L.mpullPt p hp ha hϕ with hp'
  set q' := L.mpullPt q hq ha hϕ with hq'
  set R₁₃ := (p.baseRet q).restrict (p'.isOpen_overlapW q') with hR₁₃
  have hV₁ : R₁₃.U ⊆ (p.baseRet q).U := inter_subset_left
  have hV₃ : R₁₃.U ⊆ (p'.baseRet q').U := fun u hu => ⟨(p.baseRet_U_subset q) hu.1, hu.2⟩
  have hzV : p.z ∈ p.c.φ.model.E.lvlSet R₁₃.U 1 := ⟨p.z_mem_baseRet q, (p'.z_mem_baseRet q').2⟩
  have heq : EqOn (p'.c.φ.transition q'.c.φ ∘ p'.baseRet q')
      (p.c.φ.transition q.c.φ ∘ p.baseRet q) R₁₃.U := by
    intro u hu
    obtain ⟨y, hy, hy', hyu⟩ := p'.exists_eq_of_mem_baseRet q' (hV₃ hu)
    have hyu' : r p.c.R u = p.c.φ (L.ϕ y) := hyu
    change q.c.φ (L.ϕ (L.g (p.c.φ.symm (r p.c.R u)))) = q.c.φ (p.c.φ.symm (r p.c.R u))
    rw [hyu', p.c.φ.symm_apply_apply hy.2, L.base.left_inv y hy.1]
  exact congrArg (fun T : p.c.φ.model.E 0 →L[ℝ] q.c.φ.model.E 0 => T v)
    (scDeriv_eq_of_eqOn_relOpen R₁₃.relOpen (p'.isSc1_transition q') (p.isSc1_transition q) hV₃
      hV₁ heq hzV)

/-- The fibre transitions between two carried chart points are those between the original
ones. -/
theorem fiberMap_mpullPt (L : LocalIso B B' U U') {p q : ChartPoint B' x}
    (hp : p.c.φ.source ⊆ U') (hq : q.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (k : p.c.F 0) :
    (L.mpullPt p hp ha hϕ).fiberMap (L.mpullPt q hq ha hϕ) k = p.fiberMap q k := by
  set w : p.c.φ.model.E 0 × p.c.F 0 :=
    (p.c.φ.model.E.toBase 1 p.z, ρ p.c.R (p.c.φ.model.E.toBase 1 p.z) k) with hw
  have hwK : w ∈ p.c.toPartialEquiv.target := by
    rw [p.c.target_eq]; exact p.c.mem_K_ρ p.toBase_z_mem_O k
  have hsrc := p.c.toPartialEquiv.map_target hwK
  have hU' : P' (p.c.toPartialEquiv.symm w) ∈ U' := by
    rw [p.c.source_eq] at hsrc; exact hp hsrc
  change (q.c (L.Φ (L.Ψ (p.c.toPartialEquiv.symm w)))).2 = (q.c (p.c.toPartialEquiv.symm w)).2
  rw [L.zero.right_inv _ hU']

/-- `T_aX` read in two carried chart points: the identification of the original ones. -/
theorem transferT_mpullPt (L : LocalIso B B' U U') {p q : ChartPoint B' x}
    (hp : p.c.φ.source ⊆ U') (hq : q.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (v : ↥p.T) :
    (Subtype.val ((L.mpullPt p hp ha hϕ).transferT (L.mpullPt q hq ha hϕ) v) :
      q.c.φ.model.E 0) = p.transferT q v :=
  baseDeriv_mpullPt L hp hq ha hϕ v

/-- `Y_a` read in two carried chart points: the identification of the original ones. -/
theorem transferK_mpullPt (L : LocalIso B B' U U') {p q : ChartPoint B' x}
    (hp : p.c.φ.source ⊆ U') (hq : q.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (k : ↥p.K) :
    (Subtype.val ((L.mpullPt p hp ha hϕ).transferK (L.mpullPt q hq ha hϕ) k) : q.c.F 0) =
      p.transferK q k :=
  fiberMap_mpullPt L hp hq ha hϕ k

end Transfer

end StrongBundle.LocalIso

end Mixed

/-! ### Two composite carried chart points that agree near the point -/

section Compose

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {X₁ : Type u₁} [TopologicalSpace X₁] [T2Space X₁] [ParacompactSpace X₁] {PX₁ : MPolyfold X₁}
  {Y₁ : Type v₁} [TopologicalSpace Y₁] [T2Space Y₁] [ParacompactSpace Y₁] {P₁ : Y₁ → X₁}
  [∀ x, AddCommGroup (P₁ ⁻¹' {x})] [∀ x, Module ℝ (P₁ ⁻¹' {x})] {B₁ : StrongBundle PX₁ P₁}
  {X₂ : Type u₂} [TopologicalSpace X₂] [T2Space X₂] [ParacompactSpace X₂] {PX₂ : MPolyfold X₂}
  {Y₂ : Type v₂} [TopologicalSpace Y₂] [T2Space Y₂] [ParacompactSpace Y₂] {P₂ : Y₂ → X₂}
  [∀ x, AddCommGroup (P₂ ⁻¹' {x})] [∀ x, Module ℝ (P₂ ⁻¹' {x})] {B₂ : StrongBundle PX₂ P₂}
  {U₁ : Set X₁} {U₁' : Set X'} {U₂ : Set X} {U₂' : Set X₁}
  {V₁ : Set X₂} {V₁' : Set X'} {V₂ : Set X} {V₂' : Set X₂}

namespace StrongBundle.LocalIso

/-- **Germ agreement of two composites** `L ∘ L₂ : Y|_{U₂} → Y₁ → Y'` and
`M ∘ M₂ : Y|_{V₂} → Y₂ → Y'` near `b`: on an open `N ∋ b` the base maps and the bundle maps
agree. -/
structure GermAgree₄ (L : LocalIso B₁ B' U₁ U₁') (L₂ : LocalIso B B₁ U₂ U₂')
    (M : LocalIso B₂ B' V₁ V₁') (M₂ : LocalIso B B₂ V₂ V₂') (b : X) : Prop where
  exists_nhds : ∃ N : Set X, IsOpen N ∧ b ∈ N ∧ N ⊆ U₂ ∧ N ⊆ V₂ ∧
    (∀ y ∈ N, L.ϕ (L₂.ϕ y) = M.ϕ (M₂.ϕ y)) ∧ ∀ w, P w ∈ N → L.Φ (L₂.Φ w) = M.Φ (M₂.Φ w)

variable {L : LocalIso B₁ B' U₁ U₁'} {L₂ : LocalIso B B₁ U₂ U₂'} {M : LocalIso B₂ B' V₁ V₁'}
  {M₂ : LocalIso B B₂ V₂ V₂'} {x : X'} {x₁ : X₁} {x₂ : X₂} {b : X}

/-- **Two composite carried chart points with the same germ**: the base derivative between them
is `Dr(z)`, as from a chart point to itself. -/
theorem baseDeriv_mpullPt₄ (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hx₁ : x₁ ∈ U₁)
    (hϕ₁ : L.ϕ x₁ = x) (h₂ : (L.mpullPt p h₁ hx₁ hϕ₁).c.φ.source ⊆ U₂') (hb : b ∈ U₂)
    (hϕ₂ : L₂.ϕ b = x₁) (k₁ : p.c.φ.source ⊆ V₁') (hx₂ : x₂ ∈ V₁) (hψ₁ : M.ϕ x₂ = x)
    (k₂ : (M.mpullPt p k₁ hx₂ hψ₁).c.φ.source ⊆ V₂') (hb' : b ∈ V₂) (hψ₂ : M₂.ϕ b = x₂)
    (hG : GermAgree₄ L L₂ M M₂ b) (v : p.c.φ.model.E 0) :
    (M₂.mpullPt (M.mpullPt p k₁ hx₂ hψ₁) k₂ hb' hψ₂).baseDeriv
      (L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂) v = p.baseDeriv p v := by
  obtain ⟨N, hNo, hbN, -, -, hNϕ, -⟩ := hG.exists_nhds
  set a₃ := M₂.mpullPt (M.mpullPt p k₁ hx₂ hψ₁) k₂ hb' hψ₂ with ha₃
  set a₁₂ := L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂ with ha₁₂
  obtain ⟨G, hGo, hG⟩ := a₃.c.φ.exists_isOpen_image_eq (s := N ∩ a₃.c.φ.source)
    inter_subset_right (hNo.inter a₃.c.φ.isOpen_source)
  set R' := (a₃.baseRet a₁₂).restrict hGo with hR'
  have hV₁ : R'.U ⊆ (a₃.baseRet a₁₂).U := inter_subset_left
  have hV₂ : R'.U ⊆ p.c.U := fun u hu => (a₃.baseRet_U_subset a₁₂) hu.1
  have hzG : r p.c.R (p.c.φ.model.E.toBase 1 p.z) ∈ G := by
    rw [p.r_toBase_z]
    have : a₃.c.φ b ∈ a₃.c.φ '' (N ∩ a₃.c.φ.source) := ⟨b, ⟨hbN, a₃.mem_source⟩, rfl⟩
    rw [hG] at this
    have h' : a₃.c.φ b = p.c.φ.model.E.toBase 1 p.z := a₃.toBase_z.symm
    rw [h'] at this
    exact this.2
  have hzV : p.z ∈ p.c.φ.model.E.lvlSet R'.U 1 := ⟨a₃.z_mem_baseRet a₁₂, hzG⟩
  have hr1 : IsSc1 p.c.U (r p.c.R) := (r_isScSmooth p.c.relOpen p.c.isRetraction).isSc1
  have hOO : a₃.c.φ.model.O = p.c.φ.model.O :=
    (M₂.transportChart_model_O _ k₂).trans (M.transportChart_model_O p.c k₁)
  have heq : EqOn (a₃.c.φ.transition a₁₂.c.φ ∘ a₃.baseRet a₁₂) (r p.c.R) R'.U := by
    intro u hu
    obtain ⟨y, hy, hy', hyu⟩ := a₃.exists_eq_of_mem_baseRet a₁₂ (hV₁ hu)
    have hrG : r p.c.R u ∈ a₃.c.φ.model.O ∩ G := ⟨hOO ▸ p.c.r_mem_O (hV₂ hu), hu.2⟩
    rw [← hG] at hrG
    obtain ⟨y₂, ⟨hy₂N, hy₂s⟩, hy₂u⟩ := hrG
    have hyy : y₂ = y := by
      have e : a₃.c.φ y₂ = a₃.c.φ y := hy₂u.trans hyu
      rw [← a₃.c.φ.symm_apply_apply hy₂s, ← a₃.c.φ.symm_apply_apply hy, e]
    subst hyy
    have hyu' : r p.c.R u = p.c.φ (M.ϕ (M₂.ϕ y₂)) := hyu
    change p.c.φ (L.ϕ (L₂.ϕ (M₂.g (M.g (p.c.φ.symm (r p.c.R u)))))) = r p.c.R u
    rw [hyu', p.c.φ.symm_apply_apply hy.2.2, M.base.left_inv _ hy.2.1,
      M₂.base.left_inv y₂ hy.1, hNϕ y₂ hy₂N]
  have := scDeriv_eq_of_eqOn_relOpen R'.relOpen (a₃.isSc1_transition a₁₂) hr1 hV₁ hV₂ heq hzV
  rw [p.baseDeriv_self]
  exact congrArg (fun T : p.c.φ.model.E 0 →L[ℝ] p.c.φ.model.E 0 => T v) this

/-- **Two composite carried chart points with the same germ**: the fibre transition between
them is the identity on `K_z`. -/
theorem fiberMap_mpullPt₄ (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hx₁ : x₁ ∈ U₁)
    (hϕ₁ : L.ϕ x₁ = x) (h₂ : (L.mpullPt p h₁ hx₁ hϕ₁).c.φ.source ⊆ U₂') (hb : b ∈ U₂)
    (hϕ₂ : L₂.ϕ b = x₁) (k₁ : p.c.φ.source ⊆ V₁') (hx₂ : x₂ ∈ V₁) (hψ₁ : M.ϕ x₂ = x)
    (k₂ : (M.mpullPt p k₁ hx₂ hψ₁).c.φ.source ⊆ V₂') (hb' : b ∈ V₂) (hψ₂ : M₂.ϕ b = x₂)
    (hG : GermAgree₄ L L₂ M M₂ b) (k : p.c.F 0) :
    (M₂.mpullPt (M.mpullPt p k₁ hx₂ hψ₁) k₂ hb' hψ₂).fiberMap
      (L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂) k = p.fiberMap p k := by
  obtain ⟨N, -, hbN, -, -, -, hNΦ⟩ := hG.exists_nhds
  set w : p.c.φ.model.E 0 × p.c.F 0 :=
    (p.c.φ.model.E.toBase 1 p.z, ρ p.c.R (p.c.φ.model.E.toBase 1 p.z) k) with hw
  have hwK : w ∈ p.c.toPartialEquiv.target := by
    rw [p.c.target_eq]; exact p.c.mem_K_ρ p.toBase_z_mem_O k
  have hsrc := p.c.toPartialEquiv.map_target hwK
  have hPx : P' (p.c.toPartialEquiv.symm w) = x := by
    have h1 := p.c.covers _ hsrc
    rw [p.c.toPartialEquiv.right_inv hwK] at h1
    have h2 : p.c.φ.model.E.toBase 1 p.z = p.c.φ (P' (p.c.toPartialEquiv.symm w)) := h1
    rw [p.c.source_eq] at hsrc
    rw [p.toBase_z] at h2
    rw [← p.c.φ.symm_apply_apply hsrc, ← h2, p.c.φ.symm_apply_apply p.mem_source]
  have hV₁' : P' (p.c.toPartialEquiv.symm w) ∈ V₁' := by rw [hPx]; exact k₁ p.mem_source
  have hP₂ : P₂ (M.Ψ (p.c.toPartialEquiv.symm w)) = x₂ := by
    rw [M.covers_inv _ hV₁', hPx, ← hψ₁, M.base.left_inv _ hx₂]
  have hV₂' : P₂ (M.Ψ (p.c.toPartialEquiv.symm w)) ∈ V₂' := by
    rw [hP₂]; exact k₂ (M.mpullPt p k₁ hx₂ hψ₁).mem_source
  have hPb : P (M₂.Ψ (M.Ψ (p.c.toPartialEquiv.symm w))) ∈ N := by
    rw [M₂.covers_inv _ hV₂', hP₂, ← hψ₂, M₂.base.left_inv _ hb']; exact hbN
  change (p.c (L.Φ (L₂.Φ (M₂.Ψ (M.Ψ (p.c.toPartialEquiv.symm w)))))).2 =
    (p.c (p.c.toPartialEquiv.symm w)).2
  rw [hNΦ _ hPb, M₂.zero.right_inv _ hV₂', M.zero.right_inv _ hV₁']

/-- The identification of `T_bX` between the two composite carried chart points is the
identity. -/
theorem transferT_mpullPt₄ (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hx₁ : x₁ ∈ U₁)
    (hϕ₁ : L.ϕ x₁ = x) (h₂ : (L.mpullPt p h₁ hx₁ hϕ₁).c.φ.source ⊆ U₂') (hb : b ∈ U₂)
    (hϕ₂ : L₂.ϕ b = x₁) (k₁ : p.c.φ.source ⊆ V₁') (hx₂ : x₂ ∈ V₁) (hψ₁ : M.ϕ x₂ = x)
    (k₂ : (M.mpullPt p k₁ hx₂ hψ₁).c.φ.source ⊆ V₂') (hb' : b ∈ V₂) (hψ₂ : M₂.ϕ b = x₂)
    (hG : GermAgree₄ L L₂ M M₂ b) (v : ↥p.T) :
    (Subtype.val ((M₂.mpullPt (M.mpullPt p k₁ hx₂ hψ₁) k₂ hb' hψ₂).transferT
      (L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂) v) : p.c.φ.model.E 0) = v :=
  (baseDeriv_mpullPt₄ p h₁ hx₁ hϕ₁ h₂ hb hϕ₂ k₁ hx₂ hψ₁ k₂ hb' hψ₂ hG v).trans
    (congrArg Subtype.val (p.transferT_self_apply v))

/-- The identification of `Y_b` between the two composite carried chart points is the
identity. -/
theorem transferK_mpullPt₄ (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hx₁ : x₁ ∈ U₁)
    (hϕ₁ : L.ϕ x₁ = x) (h₂ : (L.mpullPt p h₁ hx₁ hϕ₁).c.φ.source ⊆ U₂') (hb : b ∈ U₂)
    (hϕ₂ : L₂.ϕ b = x₁) (k₁ : p.c.φ.source ⊆ V₁') (hx₂ : x₂ ∈ V₁) (hψ₁ : M.ϕ x₂ = x)
    (k₂ : (M.mpullPt p k₁ hx₂ hψ₁).c.φ.source ⊆ V₂') (hb' : b ∈ V₂) (hψ₂ : M₂.ϕ b = x₂)
    (hG : GermAgree₄ L L₂ M M₂ b) (k : ↥p.K) :
    (Subtype.val ((M₂.mpullPt (M.mpullPt p k₁ hx₂ hψ₁) k₂ hb' hψ₂).transferK
      (L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂) k) : p.c.F 0) = k :=
  (fiberMap_mpullPt₄ p h₁ hx₁ hϕ₁ h₂ hb hϕ₂ k₁ hx₂ hψ₁ k₂ hb' hψ₂ hG k).trans
    (congrArg Subtype.val (p.transferK_self_apply k))

end StrongBundle.LocalIso

end Compose

/-! ### Carrying orientations along a local isomorphism between two bundles -/

section OrVia

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'} {U : Set X} {U' : Set X'} (L : StrongBundle.LocalIso B B' U U')
  {x : X'} {a : X}

namespace StrongBundle.LocalIso

/-- The identity of `T_zO` from a chart point to its carried chart point. -/
abbrev mcastT (p : ChartPoint B' x) (hp : p.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x) :
    ↥p.T ≃L[ℝ] ↥(L.mpullPt p hp ha hϕ).T :=
  ContinuousLinearEquiv.refl ℝ ↥p.T

/-- The identity of `K_z` from a chart point to its carried chart point. -/
abbrev mcastK (p : ChartPoint B' x) (hp : p.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x) :
    ↥p.K ≃L[ℝ] ↥(L.mpullPt p hp ha hϕ).K :=
  ContinuousLinearEquiv.refl ℝ ↥p.K

variable {L} in
theorem mcastT_mem {p : ChartPoint B' x} {hp : p.c.φ.source ⊆ U'} {ha : a ∈ U} {hϕ : L.ϕ a = x}
    (hlin : (L.mpullPt p hp ha hϕ).linSet f = p.linSet f') :
    ∀ S ∈ (L.mpullPt p hp ha hϕ).linSet f, (((L.mcastK p hp ha hϕ).symm :
      ↥(L.mpullPt p hp ha hϕ).K →L[ℝ] ↥p.K) ∘L S ∘L (L.mcastT p hp ha hϕ : ↥p.T →L[ℝ] _)) ∈
        p.linSet f' := fun S hS => by
  rw [← hlin]; exact hS

variable {L} in
theorem mcastT_mem_symm {p : ChartPoint B' x} {hp : p.c.φ.source ⊆ U'} {ha : a ∈ U}
    {hϕ : L.ϕ a = x} (hlin : (L.mpullPt p hp ha hϕ).linSet f = p.linSet f') :
    ∀ S ∈ p.linSet f', ((((L.mcastK p hp ha hϕ).symm.symm : ↥p.K →L[ℝ]
      ↥(L.mpullPt p hp ha hϕ).K)) ∘L S ∘L ((L.mcastT p hp ha hϕ).symm :
        ↥(L.mpullPt p hp ha hϕ).T →L[ℝ] ↥p.T)) ∈ (L.mpullPt p hp ha hϕ).linSet f :=
  fun S hS => by rw [hlin]; exact hS

/-- **An orientation of `DET(f', x)` read in `p` is one of `DET(f, a)` read in the carried chart
point**: the two sets `Lin` coincide (`linSet_mpullPt`). -/
def morPull (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (p : ChartPoint B' x) (hp : p.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (hlin : (L.mpullPt p hp ha hϕ).linSet f = p.linSet f') :
    p.Or f' hf' ≃ (L.mpullPt p hp ha hϕ).Or f hf where
  toFun o := o.conj (hC' := (L.mpullPt p hp ha hϕ).isFredholm_of_mem_linSet hf)
    (L.mcastT p hp ha hϕ) (L.mcastK p hp ha hϕ) (mcastT_mem hlin)
  invFun o := o.conj (hC' := p.isFredholm_of_mem_linSet hf')
    (L.mcastT p hp ha hϕ).symm (L.mcastK p hp ha hϕ).symm (mcastT_mem_symm hlin)
  left_inv o := (LineOrientation.conj_trans
    (hC' := (L.mpullPt p hp ha hϕ).isFredholm_of_mem_linSet hf)
    (hC'' := p.isFredholm_of_mem_linSet hf') _ _ _ _ (mcastT_mem hlin) (mcastT_mem_symm hlin)
    (conj_mem_trans _ _ _ _ (mcastT_mem hlin) (mcastT_mem_symm hlin)) o).trans
    ((LineOrientation.conj_congr (hC' := p.isFredholm_of_mem_linSet hf')
      (A₂ := ContinuousLinearEquiv.refl ℝ ↥p.T) (Γ₂ := ContinuousLinearEquiv.refl ℝ ↥p.K)
      (fun _ => rfl) (fun _ => rfl) _ (conj_mem_refl _) o).trans (LineOrientation.conj_refl _ o))
  right_inv o := (LineOrientation.conj_trans (hC' := p.isFredholm_of_mem_linSet hf')
    (hC'' := (L.mpullPt p hp ha hϕ).isFredholm_of_mem_linSet hf) _ _ _ _ (mcastT_mem_symm hlin)
    (mcastT_mem hlin) (conj_mem_trans _ _ _ _ (mcastT_mem_symm hlin) (mcastT_mem hlin)) o).trans
    ((LineOrientation.conj_congr (hC' := (L.mpullPt p hp ha hϕ).isFredholm_of_mem_linSet hf)
      (A₂ := ContinuousLinearEquiv.refl ℝ ↥(L.mpullPt p hp ha hϕ).T)
      (Γ₂ := ContinuousLinearEquiv.refl ℝ ↥(L.mpullPt p hp ha hϕ).K)
      (fun _ => rfl) (fun _ => rfl) _ (conj_mem_refl _) o).trans (LineOrientation.conj_refl _ o))

/-- **The map `T_xX' → T_aX` of `L⁻¹` read in chart points** `q'` at `x` and `q` at `a`, through
a chart point `p` at `x` inside `U'`: `D(τ ∘ r)` from `q'` to `p`, the identity to the carried
chart point, and `D(τ ∘ r)` from it to `q`. -/
def mmorT (q' : ChartPoint B' x) (q : ChartPoint B a) (p : ChartPoint B' x)
    (hp : p.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x) : ↥q'.T ≃L[ℝ] ↥q.T :=
  ((q'.transferT p).trans (L.mcastT p hp ha hϕ)).trans ((L.mpullPt p hp ha hϕ).transferT q)

/-- **The map `Y'_x → Y_a`** read in chart points, as `mmorT`. -/
def mmorK (q' : ChartPoint B' x) (q : ChartPoint B a) (p : ChartPoint B' x)
    (hp : p.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x) : ↥q'.K ≃L[ℝ] ↥q.K :=
  ((q'.transferK p).trans (L.mcastK p hp ha hϕ)).trans ((L.mpullPt p hp ha hϕ).transferK q)

theorem mmorT_apply (q' : ChartPoint B' x) (q : ChartPoint B a) (p : ChartPoint B' x)
    (hp : p.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x) (v : ↥q'.T) :
    L.mmorT q' q p hp ha hϕ v = (L.mpullPt p hp ha hϕ).transferT q (q'.transferT p v) := rfl

theorem mmorK_apply (q' : ChartPoint B' x) (q : ChartPoint B a) (p : ChartPoint B' x)
    (hp : p.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x) (k : ↥q'.K) :
    L.mmorK q' q p hp ha hϕ k = (L.mpullPt p hp ha hϕ).transferK q (q'.transferK p k) := rfl

variable {L} in
/-- The hypothesis of `LineOrientation.conj` for `mmorT`, `mmorK`. -/
theorem mmorT_mem (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    {q' : ChartPoint B' x} {q : ChartPoint B a} {p : ChartPoint B' x}
    {hp : p.c.φ.source ⊆ U'} {ha : a ∈ U} {hϕ : L.ϕ a = x}
    (hlin : (L.mpullPt p hp ha hϕ).linSet f = p.linSet f') (hxs : x ∈ PX'.smoothSet)
    (has : a ∈ PX.smoothSet) :
    ∀ S ∈ q.linSet f, (((L.mmorK q' q p hp ha hϕ).symm : ↥q.K →L[ℝ] ↥q'.K) ∘L S ∘L
      (L.mmorT q' q p hp ha hϕ : ↥q'.T →L[ℝ] ↥q.T)) ∈ q'.linSet f' :=
  conj_mem_trans _ _ _ _ (conj_mem_trans _ _ _ _ (q'.transfer_mem_linSet p hf' hxs)
    (mcastT_mem hlin)) ((L.mpullPt p hp ha hϕ).transfer_mem_linSet q hf has)

/-- **The orientation map of `L⁻¹` read in chart points**: `orTransfer` from `q'` to `p`,
`morPull`, and `orTransfer` from the carried chart point to `q`. -/
def morVia (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (q' : ChartPoint B' x) (q : ChartPoint B a) (p : ChartPoint B' x)
    (hp : p.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (hlin : (L.mpullPt p hp ha hϕ).linSet f = p.linSet f') (hxs : x ∈ PX'.smoothSet)
    (has : a ∈ PX.smoothSet) : q'.Or f' hf' ≃ q.Or f hf :=
  (q'.orTransfer p hf' hxs).trans ((L.morPull hf hf' p hp ha hϕ hlin).trans
    ((L.mpullPt p hp ha hϕ).orTransfer q hf has))

/-- **`morVia` is the conjugation by `mmorT` and `mmorK`.** -/
theorem morVia_apply (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (q' : ChartPoint B' x) (q : ChartPoint B a) (p : ChartPoint B' x)
    (hp : p.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (hlin : (L.mpullPt p hp ha hϕ).linSet f = p.linSet f') (hxs : x ∈ PX'.smoothSet)
    (has : a ∈ PX.smoothSet) (o : q'.Or f' hf') :
    L.morVia hf hf' q' q p hp ha hϕ hlin hxs has o =
      o.conj (hC' := q.isFredholm_of_mem_linSet hf) (L.mmorT q' q p hp ha hϕ)
        (L.mmorK q' q p hp ha hϕ) (mmorT_mem hf hf' hlin hxs has) := by
  have e1 := LineOrientation.conj_trans (hC' := p.isFredholm_of_mem_linSet hf')
    (hC'' := (L.mpullPt p hp ha hϕ).isFredholm_of_mem_linSet hf) _ _ _ _
    (q'.transfer_mem_linSet p hf' hxs) (mcastT_mem hlin)
    (conj_mem_trans _ _ _ _ (q'.transfer_mem_linSet p hf' hxs) (mcastT_mem hlin)) o
  have e2 := LineOrientation.conj_trans
    (hC' := (L.mpullPt p hp ha hϕ).isFredholm_of_mem_linSet hf)
    (hC'' := q.isFredholm_of_mem_linSet hf) _ _ _ _
    (conj_mem_trans _ _ _ _ (q'.transfer_mem_linSet p hf' hxs) (mcastT_mem hlin))
    ((L.mpullPt p hp ha hϕ).transfer_mem_linSet q hf has) (mmorT_mem hf hf' hlin hxs has) o
  exact (congrArg (fun o' => LineOrientation.conj (hC' := q.isFredholm_of_mem_linSet hf) _ _
    ((L.mpullPt p hp ha hϕ).transfer_mem_linSet q hf has) o') e1).trans e2

/-- **`mmorT` does not depend on the intermediate chart point.** -/
theorem mmorT_eq (q' : ChartPoint B' x) (q : ChartPoint B a) {p p₂ : ChartPoint B' x}
    (hp : p.c.φ.source ⊆ U') (hp₂ : p₂.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (v : ↥q'.T) : L.mmorT q' q p hp ha hϕ v = L.mmorT q' q p₂ hp₂ ha hϕ v := by
  rw [mmorT_apply, mmorT_apply, ← q'.transferT_trans_apply p p₂ v]
  set w : ↥(L.mpullPt p hp ha hϕ).T := q'.transferT p v
  have h1 := ((L.mpullPt p hp ha hϕ).transferT_trans_apply (L.mpullPt p₂ hp₂ ha hϕ) q w).symm
  have h2 : (L.mpullPt p hp ha hϕ).transferT (L.mpullPt p₂ hp₂ ha hϕ) w =
      (p.transferT p₂ w : ↥(L.mpullPt p₂ hp₂ ha hϕ).T) :=
    Subtype.ext (transferT_mpullPt L hp hp₂ ha hϕ w)
  exact h1.trans (congrArg ((L.mpullPt p₂ hp₂ ha hϕ).transferT q) h2)

/-- **`mmorK` does not depend on the intermediate chart point.** -/
theorem mmorK_eq (q' : ChartPoint B' x) (q : ChartPoint B a) {p p₂ : ChartPoint B' x}
    (hp : p.c.φ.source ⊆ U') (hp₂ : p₂.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (k : ↥q'.K) : L.mmorK q' q p hp ha hϕ k = L.mmorK q' q p₂ hp₂ ha hϕ k := by
  rw [mmorK_apply, mmorK_apply, ← q'.transferK_trans_apply p p₂ k]
  set w : ↥(L.mpullPt p hp ha hϕ).K := q'.transferK p k
  have h1 := ((L.mpullPt p hp ha hϕ).transferK_trans_apply (L.mpullPt p₂ hp₂ ha hϕ) q w).symm
  have h2 : (L.mpullPt p hp ha hϕ).transferK (L.mpullPt p₂ hp₂ ha hϕ) w =
      (p.transferK p₂ w : ↥(L.mpullPt p₂ hp₂ ha hϕ).K) :=
    Subtype.ext (transferK_mpullPt L hp hp₂ ha hϕ w)
  exact h1.trans (congrArg ((L.mpullPt p₂ hp₂ ha hϕ).transferK q) h2)

/-- **`morVia` does not depend on the intermediate chart point.** -/
theorem morVia_eq (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (q' : ChartPoint B' x) (q : ChartPoint B a) {p p₂ : ChartPoint B' x}
    (hp : p.c.φ.source ⊆ U') (hp₂ : p₂.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (hlp : (L.mpullPt p hp ha hϕ).linSet f = p.linSet f')
    (hlp₂ : (L.mpullPt p₂ hp₂ ha hϕ).linSet f = p₂.linSet f') (hxs : x ∈ PX'.smoothSet)
    (has : a ∈ PX.smoothSet) :
    L.morVia hf hf' q' q p hp ha hϕ hlp hxs has = L.morVia hf hf' q' q p₂ hp₂ ha hϕ hlp₂ hxs has :=
  Equiv.ext fun o => by
    rw [morVia_apply, morVia_apply]
    exact LineOrientation.conj_congr (L.mmorT_eq q' q hp hp₂ ha hϕ) (L.mmorK_eq q' q hp hp₂ ha hϕ)
      _ _ o

end StrongBundle.LocalIso

end OrVia

/-- For one bundle, the mixed carried chart point is `pullPt`. -/
theorem StrongBundle.LocalIso.mpullPt_eq_pullPt {X : Type u} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]
    [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P} {U U' : Set X} (L : LocalIso B B U U')
    {x a : X} (p : ChartPoint B x) (hsub : p.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x) :
    L.mpullPt p hsub ha hϕ = L.pullPt p hsub ha hϕ := rfl

end Polyfold
