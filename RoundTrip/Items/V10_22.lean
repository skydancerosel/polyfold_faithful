import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_22

/-! Round trip for V10_22 (2021 Definition 10.4.1 = 2017 Definition 10.10, strong bundle
equivalences).

The item lists the definitions `IsStrongBundleEquivalence`, `OneOrbitSpace`, `oneOrbitMap`,
`IsStrongBundleEquivalence.fiberEquiv` (vocabulary) and ten theorems; `A` is the conjunction of
their types, universes at `0` (the two example theorems have no universe parameter):
`IsStrongBundleFunctor.comp`, `covers`, `eq_of_obj_eq`, `isLocalScDiffeo_obj`,
`isLocalScDiffeo_one`, `isStrongBundleEquivalence_id`, `IsStrongBundleEquivalence.comp`,
`isStrongBundleEquivalence_of_inverse`, and the witnesses `isStrongBundleEquivalence_pullbackProj'`,
`trivialNeg_obj_ne_id`.

`B` says that the project's `IsStrongBundleEquivalence E E' ϕ Φ` is the blind `IsSBEquivB`, which
spells (1) for `i = 1` out as: `Φ` maps `W_{0,1}` into `W'_{0,1}`, is a local sc-diffeomorphism
`W[1] → W'[1]`, faithful and full on `W[1]`, and induces a homeomorphism `|W[1]| → |W'[1]|`.
The project keeps only the homeomorphism (and derives the local sc-diffeomorphism property from
(2), `isLocalScDiffeo_one`).

* `A_to_B`: the iff.  `→`: the local sc-diffeomorphism property of `Φ[1]` is `A`'s
  `isLocalScDiffeo_one`; faithfulness and fullness on `W[1]` are those of `Φ : W[0] → W'[0]`
  (`IsEquivalence.mor_injective`, `exists_mor_eq`); the homeomorphism is `|Φ|` itself (the blind
  `Quot (IsoOneB E)` is the project's `OneOrbitSpace` by `rfl`).  `←`: `e = |Φ|` on classes.
* `B_to_A`: `covers`, `eq_of_obj_eq`, `isLocalScDiffeo_obj`, `isLocalScDiffeo_one` are read off
  `IsSBEquivB` (through `B`, `→`).  The other conjuncts are not about the definition's content
  (composition of strong bundle functors, the identity and composites and inverse pairs being
  equivalences, and the two witnesses): they are re-proved outright below (the project's proofs,
  from non-item lemmas). -/

set_option maxSynthPendingDepth 3

namespace RoundTrip.V10_22
open Polyfold Set Function

/-! The project's statement (universes at `0`). -/
def A1 : Prop := type_of% @Polyfold.EpStrongBundle.IsStrongBundleFunctor.comp.{0}
def A2 : Prop := type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.covers.{0}
def A3 : Prop := type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.eq_of_obj_eq.{0}
def A4 : Prop := type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isLocalScDiffeo_obj.{0}
def A5 : Prop := type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isLocalScDiffeo_one.{0}
def A6 : Prop := type_of% @Polyfold.EpStrongBundle.isStrongBundleEquivalence_id.{0}
def A7 : Prop := type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.comp.{0}
def A8 : Prop := type_of% @Polyfold.EpStrongBundle.isStrongBundleEquivalence_of_inverse.{0}
def A9 : Prop :=
  type_of% @Polyfold.StrongBundleEquivalenceExamples.isStrongBundleEquivalence_pullbackProj'
def A10 : Prop := type_of% @Polyfold.StrongBundleEquivalenceExamples.trivialNeg_obj_ne_id

/-- The project's statement. -/
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6 ∧ A7 ∧ A8 ∧ A9 ∧ A10

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.IsStrongBundleFunctor.comp.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.covers.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.eq_of_obj_eq.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isLocalScDiffeo_obj.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isLocalScDiffeo_one.{0},
    @Polyfold.EpStrongBundle.isStrongBundleEquivalence_id.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.comp.{0},
    @Polyfold.EpStrongBundle.isStrongBundleEquivalence_of_inverse.{0},
    @Polyfold.StrongBundleEquivalenceExamples.isStrongBundleEquivalence_pullbackProj',
    @Polyfold.StrongBundleEquivalenceExamples.trivialNeg_obj_ne_id⟩

section Setting
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {ϕ : EpFunctor X X'}
  {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}

/-- `→` of the iff, with the local sc-diffeomorphism property of `Φ[1]` as a hypothesis (`A`'s
`isLocalScDiffeo_one` in `A_to_B`). -/
theorem toB (h : E.IsStrongBundleEquivalence E' ϕ Φ)
    (hone : B.toMPolyfold1.IsLocalScDiffeo B'.toMPolyfold1 (StrongBundle.oneRestrict B B' Φ.obj
      h.isStrongBundleFunctor.isStrongBundleMap_obj.mapsTo_oneSet)) :
    IsSBEquivB E E' ϕ Φ := by
  refine ⟨h.isStrongBundleFunctor, h.isEquivalence_base, h.isEquivalence,
    ⟨h.isStrongBundleFunctor.isStrongBundleMap_obj.mapsTo_oneSet, hone, ?_, ?_, ?_⟩,
    h.isLocalStrongBundleIso_obj, h.isLocalStrongBundleIso_mor⟩
  · intro m m' _ hs ht he
    exact h.isEquivalence.mor_injective hs ht he
  · intro w₁ w₂ _ _ m' hs ht
    exact h.isEquivalence.exists_mor_eq hs ht
  · exact ⟨h.isHomeomorph_oneOrbitMap.homeomorph, fun a => rfl⟩

/-- `←` of the iff. -/
theorem ofB (h : IsSBEquivB E E' ϕ Φ) : E.IsStrongBundleEquivalence E' ϕ Φ := by
  obtain ⟨hF, hϕ, hΦ, ⟨hmap, -, -, -, e, he⟩, hobj, hmor⟩ := h
  refine ⟨hF, hϕ, hΦ, ?_, hobj, hmor⟩
  have : E.oneOrbitMap E' Φ hF.isStrongBundleMap_obj.mapsTo_oneSet = e := by
    funext q
    induction q using Quot.ind with
    | mk a => exact (he a).symm
  rw [this]
  exact e.isHomeomorph

end Setting

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, -, hone, -⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
    E E' ϕ Φ
  exact ⟨fun h => toB h (hone h), ofB⟩

/-! ### Conjuncts not about the content of the definition, re-proved outright -/

section Outright
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {Obj'' Mor'' : Type} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor''] {X'' : EpGroupoid Obj'' Mor''}
  {W'' : Type} [TopologicalSpace W''] [T2Space W''] [ParacompactSpace W''] {P'' : W'' → Obj''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
  {B'' : StrongBundle X''.PObj P''} [ParacompactSpace (pullbackSpace P'' X''.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {E'' : EpStrongBundle X'' B''}

theorem sbFunctor_comp {ϕ : EpFunctor X X'} {ψ : EpFunctor X' X''}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} {Ψ : EpFunctor E'.toEpGroupoid E''.toEpGroupoid}
    (h₂ : E'.IsStrongBundleFunctor E'' ψ Ψ) (h₁ : E.IsStrongBundleFunctor E' ϕ Φ) :
    E.IsStrongBundleFunctor E'' (ψ.comp ϕ) (Ψ.comp Φ) :=
  ⟨h₂.isStrongBundleMap_obj.comp h₁.isStrongBundleMap_obj,
    h₂.isStrongBundleMap_mor.comp h₁.isStrongBundleMap_mor⟩

theorem sbEquiv_id (E : EpStrongBundle X B) :
    E.IsStrongBundleEquivalence E (EpFunctor.id X) (EpFunctor.id E.toEpGroupoid) where
  isStrongBundleFunctor := E.isStrongBundleFunctor_id
  isEquivalence_base := EpFunctor.IsEquivalence.id X
  isEquivalence := EpFunctor.IsEquivalence.id E.toEpGroupoid
  isHomeomorph_oneOrbitMap := by rw [EpStrongBundle.oneOrbitMap_id]; exact IsHomeomorph.id
  isLocalStrongBundleIso_obj x := ⟨univ, univ, mem_univ x, B.isStrongBundleIsoOn_id isOpen_univ⟩
  isLocalStrongBundleIso_mor φ := ⟨univ, univ, mem_univ φ,
    (B.pullback X.isScSmoothMap_src).isStrongBundleIsoOn_id isOpen_univ⟩

theorem sbEquiv_comp {ϕ : EpFunctor X X'} {ψ : EpFunctor X' X''}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} {Ψ : EpFunctor E'.toEpGroupoid E''.toEpGroupoid}
    (h₂ : E'.IsStrongBundleEquivalence E'' ψ Ψ) (h₁ : E.IsStrongBundleEquivalence E' ϕ Φ) :
    E.IsStrongBundleEquivalence E'' (ψ.comp ϕ) (Ψ.comp Φ) where
  isStrongBundleFunctor := sbFunctor_comp h₂.isStrongBundleFunctor h₁.isStrongBundleFunctor
  isEquivalence_base := h₂.isEquivalence_base.comp h₁.isEquivalence_base
  isEquivalence := h₂.isEquivalence.comp h₁.isEquivalence
  isHomeomorph_oneOrbitMap := by
    rw [EpStrongBundle.oneOrbitMap_comp h₁.isStrongBundleFunctor.isStrongBundleMap_obj.mapsTo_oneSet
      h₂.isStrongBundleFunctor.isStrongBundleMap_obj.mapsTo_oneSet]
    exact h₂.isHomeomorph_oneOrbitMap.comp h₁.isHomeomorph_oneOrbitMap
  isLocalStrongBundleIso_obj x := by
    obtain ⟨U, U', hx, hi⟩ := h₁.isLocalStrongBundleIso_obj x
    obtain ⟨V', V'', hy, hi'⟩ := h₂.isLocalStrongBundleIso_obj (ϕ.obj x)
    exact hi'.exists_comp hi hx hy
  isLocalStrongBundleIso_mor φ := by
    obtain ⟨U, U', hx, hi⟩ := h₁.isLocalStrongBundleIso_mor φ
    obtain ⟨V', V'', hy, hi'⟩ := h₂.isLocalStrongBundleIso_mor (ϕ.mor φ)
    exact hi'.exists_comp hi hx hy

open EpStrongBundle in
theorem sbEquiv_of_inverse {ϕ : EpFunctor X X'} {ψ : EpFunctor X' X}
    {Φ : W → W'} {Ψ : W' → W} (hΦ : E.IsMap E' ϕ Φ) (hΨ : E'.IsMap E ψ Ψ)
    (hϕψ : ∀ x, ψ.obj (ϕ.obj x) = x) (hψϕ : ∀ x', ϕ.obj (ψ.obj x') = x')
    (hϕψm : ∀ φ, ψ.mor (ϕ.mor φ) = φ) (hψϕm : ∀ φ', ϕ.mor (ψ.mor φ') = φ')
    (hΦΨ : ∀ w, Ψ (Φ w) = w) (hΨΦ : ∀ w', Φ (Ψ w') = w') :
    E.IsStrongBundleEquivalence E' ϕ hΦ.liftFunctor := by
  have hm₁ : ∀ q, liftMor ψ hΨ.isStrongBundleMap.covers (liftMor ϕ hΦ.isStrongBundleMap.covers q) =
      q := fun q => Subtype.ext (Prod.ext (hϕψm _) (hΦΨ _))
  have hm₂ : ∀ q', liftMor ϕ hΦ.isStrongBundleMap.covers
      (liftMor ψ hΨ.isStrongBundleMap.covers q') = q' := fun q' =>
    Subtype.ext (Prod.ext (hψϕm _) (hΨΦ _))
  have hS₁ := hΦ.isStrongBundleFunctor_liftFunctor
  have hS₂ := hΨ.isStrongBundleFunctor_liftFunctor
  have hc : ∀ {Y₁ Y₂ : Type} [TopologicalSpace Y₁] [TopologicalSpace Y₂] (g : Y₁ → Y₂),
      ContinuousOn g univ → Continuous g := fun g hg => continuousOn_univ.1 hg
  refine ⟨hS₁, EpFunctor.isEquivalence_of_inverse (G := ψ) hϕψ hψϕ hϕψm hψϕm,
    EpFunctor.isEquivalence_of_inverse (G := hΨ.liftFunctor) hΦΨ hΨΦ hm₁ hm₂, ?_,
    fun x => ⟨univ, univ, mem_univ x, StrongBundle.isStrongBundleIsoOn_univ_of_inverse
      hΦ.isStrongBundleMap hΨ.isStrongBundleMap ϕ.isScSmoothMap_obj ψ.isScSmoothMap_obj hϕψ hψϕ
      hΦΨ hΨΦ⟩,
    fun φ => ⟨univ, univ, mem_univ φ, StrongBundle.isStrongBundleIsoOn_univ_of_inverse
      hS₁.isStrongBundleMap_mor hS₂.isStrongBundleMap_mor ϕ.isScSmoothMap_mor ψ.isScSmoothMap_mor
      hϕψm hψϕm hm₁ hm₂⟩⟩
  have hl : ∀ a, E'.oneOrbitMap E hΨ.liftFunctor hS₂.isStrongBundleMap_obj.mapsTo_oneSet
      (E.oneOrbitMap E' hΦ.liftFunctor hS₁.isStrongBundleMap_obj.mapsTo_oneSet a) = a := fun a =>
    Quotient.inductionOn a fun w => congrArg (Quotient.mk _)
      (B.oneVal_injective (by
        rw [StrongBundle.oneVal_oneRestrict, StrongBundle.oneVal_oneRestrict]; exact hΦΨ _))
  have hr : ∀ a, E.oneOrbitMap E' hΦ.liftFunctor hS₁.isStrongBundleMap_obj.mapsTo_oneSet
      (E'.oneOrbitMap E hΨ.liftFunctor hS₂.isStrongBundleMap_obj.mapsTo_oneSet a) = a := fun a =>
    Quotient.inductionOn a fun w => congrArg (Quotient.mk _)
      (B'.oneVal_injective (by
        rw [StrongBundle.oneVal_oneRestrict, StrongBundle.oneVal_oneRestrict]; exact hΨΦ _))
  exact (Homeomorph.mk ⟨_, _, hl, hr⟩
    (continuous_oneOrbitMap (hc _ hS₁.isStrongBundleMap_obj.isScSmoothMap_one.continuousOn))
    (continuous_oneOrbitMap
      (hc _ hS₂.isStrongBundleMap_obj.isScSmoothMap_one.continuousOn))).isHomeomorph

end Outright

section Witness
open StrongBundleEquivalenceExamples TrivialBundle
variable (n k : ℕ)

theorem pullbackProj'_equiv :
    (negEpBundle n k).IsStrongBundleEquivalence (epBundle n k) (trivialNeg n)
      (isMap_pullbackProj' n k).liftFunctor :=
  sbEquiv_of_inverse (isMap_pullbackProj' n k)
    (isMap_negInv n k) (fun x => neg_neg x) (fun x => neg_neg x) (fun x => neg_neg x)
    (fun x => neg_neg x)
    (fun q => Subtype.ext (Prod.ext (by
      have hq : (q : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin k → ℝ))).2.1 =
          -(q : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin k → ℝ))).1 := q.2
      change -(q : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin k → ℝ))).2.1 = _
      rw [hq, neg_neg]) rfl))
    fun _ => rfl

theorem trivialNeg_ne_id [NeZero n] : (trivialNeg n).obj ≠ id := fun h => by
  have h1 := congrFun h (fun _ => 1)
  have h2 := congrFun h1 0
  change -(1 : ℝ) = 1 at h2
  norm_num at h2

end Witness

theorem B_to_A : B → A := by
  intro hB
  have conv : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
      {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
      [ParacompactSpace (pullbackSpace P X.src)]
      {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
      [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
      {W' : Type} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
      [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
      {B' : StrongBundle X'.PObj P'} [ParacompactSpace (pullbackSpace P' X'.src)]
      {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {ϕ : EpFunctor X X'}
      {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid},
      E.IsStrongBundleEquivalence E' ϕ Φ → IsSBEquivB E E' ϕ Φ :=
    fun {Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
      E E' ϕ Φ} h => (hB Obj Mor X W P B Obj' Mor' X' W' P' B' E E' ϕ Φ).1 h
  refine ⟨@sbFunctor_comp, ?_, ?_, ?_, ?_, @sbEquiv_id, @sbEquiv_comp, @sbEquiv_of_inverse,
    pullbackProj'_equiv, trivialNeg_ne_id⟩
  · -- `covers`
    intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
      E E' ϕ Φ h w
    obtain ⟨hF, -⟩ := conv h
    exact hF.isStrongBundleMap_obj.covers w
  · -- `eq_of_obj_eq`
    intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
      E E' ϕ Φ h w w₁ hP he
    obtain ⟨hF, -, -, -, hobj, -⟩ := conv h
    obtain ⟨U, U', hx, hi⟩ := hobj (P w₁)
    have := (hi.fiberEquiv hx).injective (a₁ := ⟨w, hP⟩) (a₂ := ⟨w₁, rfl⟩) (Subtype.ext he)
    exact congrArg Subtype.val this
  · -- `isLocalScDiffeo_obj`
    intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
      E E' ϕ Φ h
    obtain ⟨-, -, hΦ, -⟩ := conv h
    exact hΦ.isLocalScDiffeo_obj
  · -- `isLocalScDiffeo_one`
    intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
      E E' ϕ Φ h
    obtain ⟨-, -, -, ⟨hmap, hone, -⟩, -⟩ := conv h
    exact hone

#rt_check RoundTrip.V10_22.A_to_B [Polyfold.EpStrongBundle.IsStrongBundleFunctor.comp,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.covers,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.eq_of_obj_eq,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isLocalScDiffeo_obj,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isLocalScDiffeo_one,
  Polyfold.EpStrongBundle.isStrongBundleEquivalence_id,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.comp,
  Polyfold.EpStrongBundle.isStrongBundleEquivalence_of_inverse,
  Polyfold.StrongBundleEquivalenceExamples.isStrongBundleEquivalence_pullbackProj',
  Polyfold.StrongBundleEquivalenceExamples.trivialNeg_obj_ne_id]
#rt_check RoundTrip.V10_22.B_to_A [Polyfold.EpStrongBundle.IsStrongBundleFunctor.comp,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.covers,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.eq_of_obj_eq,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isLocalScDiffeo_obj,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isLocalScDiffeo_one,
  Polyfold.EpStrongBundle.isStrongBundleEquivalence_id,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.comp,
  Polyfold.EpStrongBundle.isStrongBundleEquivalence_of_inverse,
  Polyfold.StrongBundleEquivalenceExamples.isStrongBundleEquivalence_pullbackProj',
  Polyfold.StrongBundleEquivalenceExamples.trivialNeg_obj_ne_id]
#rt_overlap RoundTrip.V10_22.B_to_A [Polyfold.EpStrongBundle.IsStrongBundleFunctor.comp,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.covers,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.eq_of_obj_eq,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isLocalScDiffeo_obj,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isLocalScDiffeo_one,
  Polyfold.EpStrongBundle.isStrongBundleEquivalence_id,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.comp,
  Polyfold.EpStrongBundle.isStrongBundleEquivalence_of_inverse,
  Polyfold.StrongBundleEquivalenceExamples.isStrongBundleEquivalence_pullbackProj',
  Polyfold.StrongBundleEquivalenceExamples.trivialNeg_obj_ne_id]

end RoundTrip.V10_22
