import Polyfold.Chapter12.LocalOrientationComparisonEp
import Polyfold.Chapter12.LocalOrientationFunctor
import Polyfold.Chapter6.OrientationBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5:
Theorem 12.5.3 (p. 594) and Proposition 12.5.6 (p. 595), in the two descriptions of `O_f`.

# Theorem 12.5.3 and Proposition 12.5.6: local and global sc⁺-sections

## The text, paraphrased

(Theorem 12.5.3) `O_f` carries exactly one topology with the properties of Theorem 6.6.17, and
the morphisms act on it.  (Proposition 12.5.6) `f` is orientable iff `|σ| : |O_f| → |X_∞|` is
`(2 : 1)` and has a continuous global section.

## What is formalized

The sets `Lin(f, x)` can be made with sc⁺-sections over the whole object space (Part I's
objects, with sc-smooth bump functions: `Orx`, `orTopology`, `orMor`, `OrRel`) or with
sc⁺-sections over open subsets of chart domains (`OrxLoc`, `orTopologyLoc`, `orMorLoc`,
`OrRelLoc`, which need a tame base and tame germ data only).  Where bump functions exist, the
two statements of each result are equivalent, statement by statement:

* `isOrientationTopology_iff_loc`: a topology `t` on `O_f` has the properties of
  Theorem 6.6.17 iff its image under the bijection `(x, o) ↦ (x, orxLocEquiv o)` has them for
  the local orientation sets.  So the topologies of Theorem 12.5.3 correspond
  (`theorem_12_5_3_iff_loc`, together with the morphism actions, `orxLocEquiv_orMor`).
* `isSectionOrientation_iff_loc`: `y ↦ o_y` is an orientation of `f` in the sense of
  Definition 6.6.16 iff its image under `orxLocEquiv` is one for the local orientation sets.
* `orientable_iff_loc`: `f` has an orientation (Definition 12.5.4) in one description iff in
  the other.
* `orbitSection_iff_loc`: `|σ|` is `(2 : 1)` with a continuous global section in one
  description iff in the other (`orbitLocHomeomorph`, `isTwoToOne_iff_loc`).
* `proposition_12_5_6_of_loc`: Proposition 12.5.6 for Part I's objects as one equivalence,
  derived from `proposition_12_5_6_loc`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v

section Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
  (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)

/-- The bijection `(x, o) ↦ (x, orxLocEquiv o)` of the orientation spaces. -/
def orSpaceLocEquiv : OrSpace f hf.toIsScFredholmSection ≃ OrSpaceLoc hX hf :=
  @Homeomorph.toEquiv _ _ (orTopology (orLocalTransport hX hbump hf hsec)) (orTopologyLoc hX hf)
    (orSpaceLocHomeomorph hX hbump hf hsec)

theorem coinduced_orSpaceLocEquiv :
    (orTopology (orLocalTransport hX hbump hf hsec)).coinduced
      (orSpaceLocEquiv hX hbump hf hsec) = orTopologyLoc hX hf :=
  @Homeomorph.coinduced_eq _ _ (orTopology _) (orTopologyLoc hX hf)
    (orSpaceLocHomeomorph hX hbump hf hsec)

theorem induced_orSpaceLocEquiv :
    (orTopologyLoc hX hf).induced (orSpaceLocEquiv hX hbump hf hsec) =
      orTopology (orLocalTransport hX hbump hf hsec) :=
  @Homeomorph.induced_eq _ _ (orTopology _) (orTopologyLoc hX hf)
    (orSpaceLocHomeomorph hX hbump hf hsec)

omit [T2Space X] [ParacompactSpace X] [T2Space Y] [ParacompactSpace Y] in
theorem induced_coinduced_equiv {α β : Type*} (e : α ≃ β) (t : TopologicalSpace α) :
    (t.coinduced e).induced e = t := by
  rw [← e.coinduced_symm, coinduced_compose]
  simp only [Equiv.symm_comp_self]
  exact coinduced_id

/-- **The topologies of Theorem 6.6.17 correspond**: a topology `t` on `O_f` (sc⁺-sections
over the whole space) has the properties of Theorem 6.6.17 iff its image under
`(x, o) ↦ (x, orxLocEquiv o)` has them for the local orientation sets. -/
theorem isOrientationTopology_iff_loc (hC : PX.HasConnectedSmoothNbhds)
    (t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection)) :
    IsOrientationTopology f hf.toIsScFredholmSection t ↔
      (orLocalTransportLoc hX hf).IsOrientationTopology
        (t.coinduced (orSpaceLocEquiv hX hbump hf hsec)) := by
  obtain ⟨t₀, ht₀, -⟩ := theorem_6_6_17_hyp hX hbump hf hsec hC
  have e₀ : t₀ = orTopology (orLocalTransport hX hbump hf hsec) :=
    eq_orTopology_of hX hbump hf hsec ht₀.isLocalHomeomorph ht₀.propagation
  constructor
  · intro ht
    rw [eq_orTopology_of hX hbump hf hsec ht.isLocalHomeomorph ht.propagation,
      coinduced_orSpaceLocEquiv]
    exact isOrientationTopology_orTopologyLoc hX hf
  · intro ht
    obtain ⟨t₁, -, huniq'⟩ := theorem_6_6_17_loc hX hf
    have e₁ : t.coinduced (orSpaceLocEquiv hX hbump hf hsec) = orTopologyLoc hX hf :=
      (huniq' _ ht).trans (huniq' _ (isOrientationTopology_orTopologyLoc hX hf)).symm
    have et : t = orTopology (orLocalTransport hX hbump hf hsec) := by
      rw [← induced_coinduced_equiv (orSpaceLocEquiv hX hbump hf hsec) t, e₁,
        induced_orSpaceLocEquiv]
    rw [et, ← e₀]
    exact ht₀

include hbump in
/-- **Definition 6.6.16 in the two descriptions**: `y ↦ o_y` is an orientation of `f`
(sc⁺-sections over the whole space) iff `y ↦ orxLocEquiv o_y` is an orientation for the local
orientation sets. -/
theorem isSectionOrientation_iff_loc
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy) :
    IsSectionOrientation f hf.toIsScFredholmSection o ↔
      IsSectionOrientationLoc hX hf fun y hy => orxLocEquiv hf hsec y hy (o y hy) := by
  rw [isSectionOrientation_iff_continuous hX hbump hf hsec,
    continuous_orSec_iff _ (isTwoPointed_of_hasScPlusSectionsThrough hf hsec),
    isContOrOn_iff_isContOn_orxLocEquiv hX hbump hf hsec,
    isSectionOrientationLoc_iff_isContOn_univ]

end Topology

section Mor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}
  (hF : E.IsScFredholmSectionFunctor f) (hfT : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
  (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions)

/-- **Theorem 12.5.3 in the two descriptions**, for a tame object M-polyfold with sc-smooth
bump functions and a section functor with tame germ data: a topology on `O_f` has the
properties of Theorem 6.6.17 iff its image on the orientation space of the local orientation
sets has them, the bijection lies over the identity of `X_∞`, and it commutes with the action
`φ_*` of every morphism between smooth objects. -/
theorem theorem_12_5_3_iff_loc :
    (∀ t : TopologicalSpace (OrSpace f hF.2),
      IsOrientationTopology f hF.2 t ↔ (orLocalTransportLoc hX hfT).IsOrientationTopology
        (t.coinduced (orSpaceLocEquiv hX hbump hfT hsec))) ∧
    (∀ p, (orLocalTransportLoc hX hfT).proj (orSpaceLocEquiv hX hbump hfT hsec p) =
      orProj f hF.2 p) ∧
    ∀ (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
      (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (o : Orx f hF.2 x hs),
      orxLocEquiv hfT hsec x' hs' (E.orMor hF hsec σ hx hx' hs hs' o) =
        E.orMorLoc hF hfT σ hx hx' hs hs' (orxLocEquiv hfT hsec x hs o) :=
  ⟨isOrientationTopology_iff_loc hX hbump hfT hsec X.PObj.hasConnectedSmoothNbhds,
    fun _ => rfl, fun σ _ _ hx hx' hs hs' o =>
      E.orxLocEquiv_orMor_apply hF hfT hsec σ hx hx' hs hs' o⟩

/-- **Orientability in the two descriptions** (Definition 12.5.4): `f` has an orientation for
`O_f` made with sc⁺-sections over the whole object space iff it has one for the local
orientation sets. -/
theorem orientable_iff_loc :
    (∃ o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs,
        E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hfT hsec)) o) ↔
      ∃ o : ∀ x (hs : x ∈ X.PObj.smoothSet), OrxLoc hfT x hs,
        E.definition_12_5_4_loc hX hF hfT o := by
  constructor
  · rintro ⟨o, ho⟩
    exact ⟨_, (E.definition_12_5_4_iff_loc hF hfT hsec hX hbump o).1 ho⟩
  · rintro ⟨o, ho⟩
    refine ⟨fun x hs => (orxLocEquiv hfT hsec x hs).symm (o x hs),
      (E.definition_12_5_4_iff_loc hF hfT hsec hX hbump _).2 ?_⟩
    simpa only [Equiv.apply_symm_apply] using ho

include hbump in
/-- **The right side of Proposition 12.5.6 in the two descriptions**: `|σ|` is `(2 : 1)` and
has a continuous global section for one description of `|O_f|` iff for the other. -/
theorem orbitSection_iff_loc :
    (E.IsTwoToOne hF hsec ∧ ∃ s : Quot X.SmoothRel → Quot (E.OrRel hF hsec),
        @Continuous _ _ _ (@instTopologicalSpaceQuot _ _
          (orTopology (orLocalTransport hX hbump hfT hsec))) s ∧
        ∀ c, E.orbitProj hF hsec (s c) = c) ↔
      E.IsTwoToOneLoc hX hF hfT ∧ ∃ s : Quot X.SmoothRel → Quot (E.OrRelLoc hX hF hfT),
        @Continuous _ _ _ (@instTopologicalSpaceQuot _ _ (orTopologyLoc hX hfT)) s ∧
        ∀ c, E.orbitProjLoc hX hF hfT (s c) = c := by
  let := orTopology (orLocalTransport hX hbump hfT hsec)
  let := orTopologyLoc hX hfT
  set G := E.orbitLocHomeomorph hF hfT hsec hX hbump
  refine and_congr (E.isTwoToOne_iff_loc hF hfT hsec hX hbump) ⟨?_, ?_⟩
  · rintro ⟨s, hsc, hs⟩
    exact ⟨G ∘ s, G.continuous.comp hsc, fun c =>
      (E.orbitProjLoc_orbitLocHomeomorph hF hfT hsec hX hbump (s c)).trans (hs c)⟩
  · rintro ⟨s, hsc, hs⟩
    refine ⟨G.symm ∘ s, G.symm.continuous.comp hsc, fun c => ?_⟩
    have h := E.orbitProjLoc_orbitLocHomeomorph hF hfT hsec hX hbump (G.symm (s c))
    rw [G.apply_symm_apply] at h
    exact h.symm.trans (hs c)

/-- **Proposition 12.5.6**, p. 595, for `O_f` made with sc⁺-sections over the whole object
space, as one equivalence, for a tame object M-polyfold with sc-smooth bump functions and a
section functor with tame germ data: `f` is orientable (Definition 12.5.4) iff
`|σ| : |O_f| → |X_∞|` is `(2 : 1)` and has a continuous global section.  Derived from the
statement for the local orientation sets (`proposition_12_5_6_loc`). -/
theorem proposition_12_5_6_of_loc :
    (∃ o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs,
        E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hfT hsec)) o) ↔
      E.IsTwoToOne hF hsec ∧ ∃ s : Quot X.SmoothRel → Quot (E.OrRel hF hsec),
        @Continuous _ _ _ (@instTopologicalSpaceQuot _ _
          (orTopology (orLocalTransport hX hbump hfT hsec))) s ∧
        ∀ c, E.orbitProj hF hsec (s c) = c :=
  (E.orientable_iff_loc hF hfT hsec hX hbump).trans
    ((E.proposition_12_5_6_loc hX hF hfT).trans
      (E.orbitSection_iff_loc hF hfT hsec hX hbump).symm)

end EpStrongBundle

end Mor

end Polyfold
