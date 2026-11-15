import Polyfold.Chapter12.LocalOrientationComparison
import Polyfold.Chapter12.LocalOrientationOrbit

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5:
Lemma 12.5.1 and the action `φ_*` on orientations (pp. 592–593), Definition 12.5.2,
Theorem 12.5.3, Definition 12.5.4 (p. 594) and the orbit space `|O_f|` of Proposition 12.5.6
(p. 595).

# The orientation bundle over an ep-groupoid: local and global sc⁺-sections

## The text, paraphrased

For a strong bundle over an ep-groupoid and an sc-Fredholm section functor `f`, a morphism
`φ : x → x'` between smooth objects acts on `Lin(f, x)` and on the orientations of `DET(f, x)`;
`O_f` is the orientation space with this action, an orientation of `f` is a continuous section
of `σ : O_f → X_∞` invariant under the morphisms, and `|O_f| → |X_∞|` is the map of orbit
spaces.  The linearizations are those of `f − s` for sc⁺-sections `s` defined near a point; with
sc-smooth bump functions they can be taken to be defined on the whole object space.

## What is formalized

The objects of `OrientationBundleEp.lean` and `OrientationOrbit.lean` (made with sc⁺-sections
over the whole object space: `orMor`, `OrRel`, `definition_12_5_4`, `orbitProj`) and those of
`LocalOrientationMorphisms.lean`, `LocalOrientationBundleEp.lean`, `LocalOrientationOrbit.lean`
(made with sc⁺-sections over open subsets of chart domains: `orMorLoc`, `OrRelLoc`,
`definition_12_5_4_loc`, `orbitProjLoc`) agree under `orxLocEquiv` when the object M-polyfold
admits sc-smooth bump functions:

* `orMor_eq_orxViaAt`: `φ_*` is the orientation map of the local isomorphism of `φ`.
* `restrictIso_morIsoDom_germ`, `toGlobal_orMorDom`, `orxLocEquiv_orMor`: **`orxLocEquiv`
  commutes with the action of the morphisms**, `orxLocEquiv (φ_* o) = φ_* (orxLocEquiv o)`.
* `orRel_iff_orRelLoc`: the relations on the orientation spaces correspond under
  `orSpaceLocHomeomorph`.
* `definition_12_5_4_iff_loc`: `o` is an orientation of `f` (Definition 12.5.4) iff its image
  is an orientation in the sense of `definition_12_5_4_loc`.
* `orbitLocHomeomorph`: **the homeomorphism of the orbit spaces `|O_f|`**, with
  `orbitProjLoc_orbitLocHomeomorph` (it commutes with the maps to `|X_∞|`).
* `isTwoToOne_iff_loc`: `|σ|` is `(2 : 1)` for one description iff it is for the other.
* `exists_orxLoc_equiv_orMor`: the summary without instance arguments.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

section Mor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}
  (hF : E.IsScFredholmSectionFunctor f) (hfT : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)

/-! ### The action of the morphisms -/

/-- **`φ_*` on orientations is the orientation map of the local isomorphism of `φ`.** -/
theorem orMor_eq_orxViaAt (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    E.orMor hF hsec σ hx hx' hs hs' =
      (E.morIso σ).orxViaAt hF.2 hF.2 (E.eqOn_morIso_of_functor hF σ) hsec hsec
        (mem_tgtSet hx') hs' (E.morIso_ϕ_eq hx hx') := by
  have hϕ : (E.morIso σ).ϕ x' = x := E.morIso_ϕ_eq hx hx'
  subst hϕ
  rw [StrongBundle.LocalIso.orxViaAt_eq_morVia _ _ _ _ _ _ _ _ _
    (restrPt B _ (isOpen_srcSet σ) (mem_srcSet hx) hs) (restrPt_sub _ _ _ _)]
  rfl

/-- **The isomorphism of a morphism and the inclusions of two domains**: near the target `x'`
of `σ : x → x'`, the inclusion `P|D' → P` followed by the isomorphism of `σ` is the isomorphism
of `σ` read in the domains `D ∋ x`, `D' ∋ x'` followed by the inclusion `P|D → P`. -/
theorem restrictIso_morIsoDom_germ (σ : Mor) {x x' : Obj} (hx : X.src σ = x)
    (hx' : X.tgt σ = x') {D D' : B.Dom} (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) :
    StrongBundle.LocalIso.GermAgree₄ (E.morIso σ) (B.restrictIso D'.isOpen)
      (B.restrictIso D.isOpen) (E.morIsoDom σ D D') (⟨x', hxD'⟩ : D'.carrier) := by
  refine ⟨⟨E.morIsoDomSet σ D D', (E.morIsoDom σ D D').isOpen_U,
    E.mem_morIsoDomSet σ hx hx' hxD hxD', fun _ _ => mem_univ _, subset_rfl, fun y hy => ?_,
    fun q hq => ?_⟩⟩
  · rw [E.morIsoDom_ϕ_of_mem hy]; rfl
  · have hPq : P q.1.2 = q.1.1.1 := StrongBundle.pullbackSpace_subtypeVal_proj q
    have h1 : P ((E.morIso σ).Φ q.1.2) ∈ D.carrier := by
      rw [(E.morIso σ).covers _ (by rw [hPq]; exact hq.1), hPq]; exact hq.2
    change (E.morIso σ).Φ q.1.2 = (B.restrictIsoInv D.carrier ((E.morIso σ).Φ q.1.2)).1.2
    rw [B.restrictIsoInv_of_mem h1]

/-- **`φ_*` read in two domains**: for `σ : x → x'` and domains `D ∋ x`, `D' ∋ x'`, the action
`σ_*` on `Or^f` followed by `Or_{x'}^f ≃ Or_{x'}^{f|D'}` is `Or_x^f ≃ Or_x^{f|D}` followed by
`σ_*` read in `D`, `D'`. -/
theorem toGlobal_orMorDom (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) :
    (E.orMor hF hsec σ hx hx' hs hs').trans (D'.toGlobal hfT hsec x' hxD' hs') =
      (D.toGlobal hfT hsec x hxD hs).trans (E.orMorDom hF hfT σ hx hx' D D' hxD hxD' hs hs') := by
  rw [E.orMor_eq_orxViaAt hF hsec σ hx hx' hs hs']
  exact StrongBundle.LocalIso.orxViaAt_square (L := E.morIso σ)
    (L₂ := B.restrictIso D'.isOpen) (M := B.restrictIso D.isOpen) (M₂ := E.morIsoDom σ D D')
    (D'.isFredholm hfT).toIsScFredholmSection hF.2 (D.isFredholm hfT).toIsScFredholmSection
    hF.2 (E.eqOn_morIso_of_functor hF σ)
    (B.restrictSection_eqOn_restrictIso D'.isOpen hfT.isScSmooth.1)
    (B.restrictSection_eqOn_restrictIso D.isOpen hfT.isScSmooth.1)
    (E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 σ D D') D'.hasSections hsec D.hasSections hsec
    (b := ⟨x', hxD'⟩) (mem_univ _) (E.mem_morIsoDomSet σ hx hx' hxD hxD')
    (StrongBundle.Dom.mem_smoothSet hxD' hs') rfl (E.morIsoDom_ϕ_mk σ hx hx' hxD hxD')
    (mem_tgtSet hx') (mem_univ _) (E.morIso_ϕ_eq hx hx') rfl
    (E.restrictIso_morIsoDom_germ σ hx hx' hxD hxD')

/-- **`orxLocEquiv` commutes with the action of the morphisms**: for a morphism `σ : x → x'`
between smooth objects, `σ_*` on `Or^f` (made with sc⁺-sections over the whole object space)
followed by `orxLocEquiv` at `x'` is `orxLocEquiv` at `x` followed by `σ_*` on the local
orientation sets. -/
theorem orxLocEquiv_orMor (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    (E.orMor hF hsec σ hx hx' hs hs').trans (orxLocEquiv hfT hsec x' hs') =
      (orxLocEquiv hfT hsec x hs).trans (E.orMorLoc hF hfT σ hx hx' hs hs') :=
  E.toGlobal_orMorDom hF hfT hsec σ hx hx' (B.domAt x) (B.domAt x') (B.mem_domAt x)
    (B.mem_domAt x') hs hs'

theorem orxLocEquiv_orMor_apply (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (o : Orx f hF.2 x hs) :
    orxLocEquiv hfT hsec x' hs' (E.orMor hF hsec σ hx hx' hs hs' o) =
      E.orMorLoc hF hfT σ hx hx' hs hs' (orxLocEquiv hfT hsec x hs o) :=
  DFunLike.congr_fun (E.orxLocEquiv_orMor hF hfT hsec σ hx hx' hs hs') o

/-! ### The orientation spaces, the orientations and the orbit spaces -/

section Space

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]

variable (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions)

/-- **The relations given by the morphisms correspond** under the homeomorphism of the
orientation spaces. -/
theorem orRel_iff_orRelLoc (p q : OrSpace f hF.2) :
    E.OrRel hF hsec p q ↔
      E.OrRelLoc hX hF hfT (orSpaceLocHomeomorph hX hbump hfT hsec p)
        (orSpaceLocHomeomorph hX hbump hfT hsec q) := by
  refine ⟨fun ⟨φ, hx, hx', h⟩ => ⟨φ, hx, hx', ?_⟩, fun ⟨φ, hx, hx', h⟩ => ⟨φ, hx, hx', ?_⟩⟩
  · exact (E.orxLocEquiv_orMor_apply hF hfT hsec φ hx hx' _ _ p.2).symm.trans
      (congrArg (orxLocEquiv hfT hsec _ (X.PObj.smoothVal_mem q.1)) h)
  · exact (orxLocEquiv hfT hsec _ (X.PObj.smoothVal_mem q.1)).injective
      ((E.orxLocEquiv_orMor_apply hF hfT hsec φ hx hx' _ _ p.2).trans h)

/-- **The orientations of `f` correspond** (Definition 12.5.4): `o` is an orientation of `f`
for the orientation space made with sc⁺-sections over the whole object space iff its image
under `orxLocEquiv` is an orientation for the local orientation sets. -/
theorem definition_12_5_4_iff_loc (o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs) :
    E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hfT hsec)) o ↔
      E.definition_12_5_4_loc hX hF hfT fun x hs => orxLocEquiv hfT hsec x hs (o x hs) := by
  have hc : @Continuous _ _ _ (orTopology (orLocalTransport hX hbump hfT hsec)) (orSec o) ↔
      @Continuous _ _ _ (orTopologyLoc hX hfT) ((orLocalTransportLoc hX hfT).sec
        fun x hs => orxLocEquiv hfT hsec x hs (o x hs)) := by
    let _ := orTopology (orLocalTransport hX hbump hfT hsec)
    let _ := orTopologyLoc hX hfT
    exact ((orSpaceLocHomeomorph hX hbump hfT hsec).comp_continuous_iff (f := orSec o)).symm
  refine and_congr hc ⟨fun h φ x x' hx hx' hs hs' => ?_, fun h φ x x' hx hx' hs hs' => ?_⟩
  · exact (E.orxLocEquiv_orMor_apply hF hfT hsec φ hx hx' hs hs' (o x hs)).symm.trans
      (congrArg (orxLocEquiv hfT hsec x' hs') (h φ hx hx' hs hs'))
  · exact (orxLocEquiv hfT hsec x' hs').injective
      ((E.orxLocEquiv_orMor_apply hF hfT hsec φ hx hx' hs hs' (o x hs)).trans
        (h φ hx hx' hs hs'))

/-- **The homeomorphism of the orbit spaces `|O_f|`**: the orbit space of the orientation
space made with sc⁺-sections over the whole object space and the orbit space of the
orientation space of the local orientation sets, with the quotient topologies. -/
def orbitLocHomeomorph :
    @Homeomorph (Quot (E.OrRel hF hsec)) (Quot (E.OrRelLoc hX hF hfT))
      (@instTopologicalSpaceQuot _ _ (orTopology (orLocalTransport hX hbump hfT hsec)))
      (@instTopologicalSpaceQuot _ _ (orTopologyLoc hX hfT)) :=
  letI := orTopology (orLocalTransport hX hbump hfT hsec)
  letI := orTopologyLoc hX hfT
  { toEquiv := Quot.congr (orSpaceLocHomeomorph hX hbump hfT hsec).toEquiv
      (E.orRel_iff_orRelLoc hF hfT hsec hX hbump)
    continuous_toFun := continuous_quot_lift _
      (continuous_quot_mk.comp (orSpaceLocHomeomorph hX hbump hfT hsec).continuous)
    continuous_invFun := continuous_quot_lift _
      (continuous_quot_mk.comp (orSpaceLocHomeomorph hX hbump hfT hsec).symm.continuous) }

theorem orbitLocHomeomorph_mk (p : OrSpace f hF.2) :
    E.orbitLocHomeomorph hF hfT hsec hX hbump (Quot.mk _ p) =
      Quot.mk _ (orSpaceLocHomeomorph hX hbump hfT hsec p) := rfl

/-- The homeomorphism of the orbit spaces commutes with the maps `|σ|` to `|X_∞|`. -/
theorem orbitProjLoc_orbitLocHomeomorph (c : Quot (E.OrRel hF hsec)) :
    E.orbitProjLoc hX hF hfT (E.orbitLocHomeomorph hF hfT hsec hX hbump c) =
      E.orbitProj hF hsec c := by
  induction c using Quot.ind with
  | mk p => rfl

include hbump in
/-- **`|σ|` is `(2 : 1)` for one description iff it is for the other.** -/
theorem isTwoToOne_iff_loc : E.IsTwoToOne hF hsec ↔ E.IsTwoToOneLoc hX hF hfT := by
  let F : Quot (E.OrRel hF hsec) ≃ Quot (E.OrRelLoc hX hF hfT) :=
    Quot.congr (LocalTransport.Intertwines.totalEquiv (orLocalTransport hX hbump hfT hsec)
      (orLocalTransportLoc hX hfT) fun x hs => orxLocEquiv hfT hsec x hs)
      (E.orRel_iff_orRelLoc hF hfT hsec hX hbump)
  have hp : ∀ d, E.orbitProjLoc hX hF hfT (F d) = E.orbitProj hF hsec d := fun d =>
    Quot.inductionOn d fun _ => rfl
  have hp' : ∀ d', E.orbitProj hF hsec (F.symm d') = E.orbitProjLoc hX hF hfT d' := fun d' => by
    rw [← hp, F.apply_symm_apply]
  constructor
  · intro h c
    obtain ⟨d₁, d₂, hne, h₁, h₂, hall⟩ := h c
    refine ⟨F d₁, F d₂, fun e => hne (F.injective e), (hp d₁).trans h₁, (hp d₂).trans h₂,
      fun d hd => ?_⟩
    rcases hall (F.symm d) ((hp' d).trans hd) with e | e
    · exact Or.inl ((F.symm_apply_eq).1 e)
    · exact Or.inr ((F.symm_apply_eq).1 e)
  · intro h c
    obtain ⟨d₁, d₂, hne, h₁, h₂, hall⟩ := h c
    refine ⟨F.symm d₁, F.symm d₂, fun e => hne (F.symm.injective e), (hp' d₁).trans h₁,
      (hp' d₂).trans h₂, fun d hd => ?_⟩
    rcases hall (F d) ((hp d).trans hd) with e | e
    · exact Or.inl ((F.eq_symm_apply).2 e)
    · exact Or.inr ((F.eq_symm_apply).2 e)

end Space

/-- **§12.5 with local and with global sc⁺-sections is the same theory**, for a tame object
M-polyfold with sc-smooth bump functions and an sc-Fredholm section functor with tame germ
data, without instance arguments: there are bijections `ρ_x : Or_x^f ≃ OrxLoc` which commute
with the action of the morphisms and under which the orientations of `f` (Definition 12.5.4)
correspond. -/
theorem exists_orxLoc_equiv_orMor (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) :
    haveI := paracompactSpace_rn_prod X.PObj
    haveI := paracompactSpace_rn_pullback B
    haveI := paracompactSpace_rn_rn_prod X.PObj
    haveI := paracompactSpace_rn_rn_pullback B
    ∃ ρ : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs ≃ OrxLoc hfT x hs,
      (∀ (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
        (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (o : Orx f hF.2 x hs),
        ρ x' hs' (E.orMor hF hbump.hasScPlusSectionsThrough σ hx hx' hs hs' o) =
          E.orMorLoc hF hfT σ hx hx' hs hs' (ρ x hs o)) ∧
      ∀ o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs,
        E.definition_12_5_4 hF hbump.hasScPlusSectionsThrough
            (orTopology (orLocalTransport hX hbump hfT hbump.hasScPlusSectionsThrough)) o ↔
          E.definition_12_5_4_loc hX hF hfT fun x hs => ρ x hs (o x hs) := by
  have := paracompactSpace_rn_prod X.PObj
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod X.PObj
  have := paracompactSpace_rn_rn_pullback B
  exact ⟨fun x hs => orxLocEquiv hfT hbump.hasScPlusSectionsThrough x hs,
    fun σ _ _ hx hx' hs hs' o => E.orxLocEquiv_orMor_apply hF hfT _ σ hx hx' hs hs' o,
    fun o => E.definition_12_5_4_iff_loc hF hfT _ hX hbump o⟩

end EpStrongBundle

end Mor

end Polyfold
