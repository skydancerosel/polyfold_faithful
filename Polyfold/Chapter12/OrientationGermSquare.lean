import Polyfold.Chapter12.OrientationEquivalenceComp
import Polyfold.Chapter12.OrientationGerm
import Polyfold.Chapter12.OrientationLocalCommute

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 592–597: Lemma 12.5.1 (3) and the proof of Theorem 12.5.7 (2017: Lemma 12.9,
Theorem 12.12).

# Functoriality of the orientation maps of local strong bundle isomorphisms

## The text, paraphrased

A local sc-diffeomorphism of the bases covered by a local strong bundle isomorphism has
"canonical lifts to maps between the bundle fibers"; with the tangent maps they carry the
linearizations of an sc-Fredholm section at a smooth point to those of the corresponding section
at the image point, hence orientations of `DET(f', ϕ(a))` to orientations of `DET(f, a)`.  The
proofs of Lemma 12.5.1 (3) and of Theorem 12.5.7 use that this assignment is compatible with
composition: the map of a composite is the composite of the maps, the map of the identity is the
identity, and the map depends only on the germ at the point.

## What is formalized

For a local strong bundle isomorphism `L : Y|U → Y'|U'` (`StrongBundle.LocalIso`), sections with
`f = Ψ ∘ f' ∘ ϕ` on `U` and a smooth `a ∈ U`, `LocalIso.orxVia` is the bijection
`Or^{f'}_{ϕ(a)} ≃ Or^f_a` read in the chosen chart points.

* `orxPt B x hs`: the chosen chart point at a smooth `x` (the one `Orx` is read in).
* `orxTAt`, `orxKAt`, `orxViaAt`: the maps `T_xX' → T_aX`, `Y'_x → Y_a` and `Or^{f'}_x ≃ Or^f_a`
  for a point `x` given with an equation `ϕ(a) = x`; `orxT`, `orxK` are the case of the equation
  `rfl`, and `orxViaAt_rfl` identifies `orxViaAt` with `orxVia` in that case.
* `orxViaAt_apply`, `orxVia_apply`: the orientation map is the conjugation by `orxTAt`, `orxKAt`
  (`orxTAt_mem`: the conjugate of a member of `Lin(f, a)` is a member of `Lin(f', x)`);
  `orxTAt_eq_mmorT`, `orxKAt_eq_mmorK`, `orxViaAt_eq_morVia`: any intermediate chart point inside
  `U'` gives them.
* **Squares** (`mmorT_square`, `orxTAt_square`, `orxKAt_square`, `orxViaAt_square`): if two
  composites `L ∘ L₂` and `M ∘ M₂` through two intermediate bundles have the same germ at `b`
  (`GermAgree₄`), the composites of the two orientation maps coincide.
* **Triangles** (`orxTAt_triangle`, `orxKAt_triangle`, `orxViaAt_triangle`): if `L ∘ L₂ = M`
  near `b`, the orientation map of `M` is the composite of those of `L` and `L₂`.
* **Identity** (`orxTAt_of_germ_id`, `orxKAt_of_germ_id`, `orxViaAt_of_germ_id`,
  `orxViaAt_refl`): a local isomorphism of one bundle with the germ of the identity at `b` acts
  as the identity.
* **Germ** (`orxTAt_germ`, `orxKAt_germ`, `orxViaAt_germ`): two local isomorphisms with the same
  germ at `b` (`GermEq`) have the same orientation map at `b`.
* **Inverse** (`orxViaAt_symm`): the orientation map of `L⁻¹` is the inverse of that of `L`
  (`eqOn_symm`: the relation between the sections for `L⁻¹`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v' u₁ v₁ u₂ v₂

/-! ### Chosen chart points -/

section Point

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

variable (B) in
/-- The chosen chart point at a smooth `x` (the one `Orx` is read in). -/
abbrev orxPt (x : X) (hs : x ∈ PX.smoothSet) : ChartPoint B x :=
  chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hs

variable (B) in
/-- Every open neighbourhood of a smooth point contains the base domain of a chart point. -/
theorem exists_chartPoint_source_subset {x : X} (hs : x ∈ PX.smoothSet) {W : Set X}
    (hW : IsOpen W) (hx : x ∈ W) : ∃ p : ChartPoint B x, p.c.φ.source ⊆ W :=
  ⟨chartPtOf ((orChart B x).restrictInter hW) ((isChart_orChart x).restrictInter hW)
    ⟨mem_orChart x, hx⟩ hs, fun _ hy => hy.2⟩

end Point

/-! ### The chart-level maps of `orxVia` -/

section Two

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U : Set X} {U' : Set X'} (L : LocalIso B B' U U') {a : X} {x : X'}

/-- A point `x = ϕ(a)` with `a ∈ U` lies in `U'`. -/
theorem mem_of_ϕ_eq (ha : a ∈ U) (hϕ : L.ϕ a = x) : x ∈ U' := hϕ ▸ L.base.mapsTo ha

/-- A point `x = ϕ(a)` with `a ∈ U` smooth is smooth. -/
theorem mem_smoothSet_of_ϕ_eq (ha : a ∈ U) (has : a ∈ PX.smoothSet) (hϕ : L.ϕ a = x) :
    x ∈ PX'.smoothSet := hϕ ▸ (L.mem_smoothSet_iff ha).1 has

/-- **The map `T_xX' → T_aX` of `L⁻¹` in the chosen chart points**, for `x = ϕ(a)`: `mmorT`
through `innerPt`. -/
def orxTAt (ha : a ∈ U) (has : a ∈ PX.smoothSet) (hϕ : L.ϕ a = x) :
    ↥(orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)).T ≃L[ℝ] ↥(orxPt B a has).T :=
  L.mmorT _ _ (L.innerPt x (L.mem_of_ϕ_eq ha hϕ) (L.mem_smoothSet_of_ϕ_eq ha has hϕ))
    (L.innerPt_sub _ _ _) ha hϕ

/-- **The map `Y'_x → Y_a` of `L⁻¹` in the chosen chart points**, for `x = ϕ(a)`: `mmorK`
through `innerPt`. -/
def orxKAt (ha : a ∈ U) (has : a ∈ PX.smoothSet) (hϕ : L.ϕ a = x) :
    ↥(orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)).K ≃L[ℝ] ↥(orxPt B a has).K :=
  L.mmorK _ _ (L.innerPt x (L.mem_of_ϕ_eq ha hϕ) (L.mem_smoothSet_of_ϕ_eq ha has hϕ))
    (L.innerPt_sub _ _ _) ha hϕ

/-- **The map `T_{ϕ(a)}X' → T_aX` of `L⁻¹` in the chosen chart points** (those of `orxVia`). -/
def orxT (ha : a ∈ U) (has : a ∈ PX.smoothSet) :
    ↥(orxPt B' (L.ϕ a) ((L.mem_smoothSet_iff ha).1 has)).T ≃L[ℝ] ↥(orxPt B a has).T :=
  L.orxTAt ha has rfl

/-- **The map `Y'_{ϕ(a)} → Y_a` of `L⁻¹` in the chosen chart points** (those of `orxVia`). -/
def orxK (ha : a ∈ U) (has : a ∈ PX.smoothSet) :
    ↥(orxPt B' (L.ϕ a) ((L.mem_smoothSet_iff ha).1 has)).K ≃L[ℝ] ↥(orxPt B a has).K :=
  L.orxKAt ha has rfl

theorem orxTAt_rfl (ha : a ∈ U) (has : a ∈ PX.smoothSet) :
    L.orxTAt ha has rfl = L.orxT ha has := rfl

theorem orxKAt_rfl (ha : a ∈ U) (has : a ∈ PX.smoothSet) :
    L.orxKAt ha has rfl = L.orxK ha has := rfl

/-- **`orxTAt` through any chart point inside `U'`** (`mmorT_eq`). -/
theorem orxTAt_eq_mmorT (ha : a ∈ U) (has : a ∈ PX.smoothSet) (hϕ : L.ϕ a = x)
    (p : ChartPoint B' x) (hp : p.c.φ.source ⊆ U')
    (v : ↥(orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)).T) :
    L.orxTAt ha has hϕ v = L.mmorT (orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ))
      (orxPt B a has) p hp ha hϕ v :=
  L.mmorT_eq _ _ _ hp ha hϕ v

/-- **`orxKAt` through any chart point inside `U'`** (`mmorK_eq`). -/
theorem orxKAt_eq_mmorK (ha : a ∈ U) (has : a ∈ PX.smoothSet) (hϕ : L.ϕ a = x)
    (p : ChartPoint B' x) (hp : p.c.φ.source ⊆ U')
    (k : ↥(orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)).K) :
    L.orxKAt ha has hϕ k = L.mmorK (orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ))
      (orxPt B a has) p hp ha hϕ k :=
  L.mmorK_eq _ _ _ hp ha hϕ k

/-- **`orxT` through any chart point inside `U'`.** -/
theorem orxT_eq_mmorT (ha : a ∈ U) (has : a ∈ PX.smoothSet) (p : ChartPoint B' (L.ϕ a))
    (hp : p.c.φ.source ⊆ U') (v : ↥(orxPt B' (L.ϕ a) ((L.mem_smoothSet_iff ha).1 has)).T) :
    L.orxT ha has v = L.mmorT (orxPt B' (L.ϕ a) ((L.mem_smoothSet_iff ha).1 has))
      (orxPt B a has) p hp ha rfl v :=
  L.orxTAt_eq_mmorT ha has rfl p hp v

/-- **`orxK` through any chart point inside `U'`.** -/
theorem orxK_eq_mmorK (ha : a ∈ U) (has : a ∈ PX.smoothSet) (p : ChartPoint B' (L.ϕ a))
    (hp : p.c.φ.source ⊆ U') (k : ↥(orxPt B' (L.ϕ a) ((L.mem_smoothSet_iff ha).1 has)).K) :
    L.orxK ha has k = L.mmorK (orxPt B' (L.ϕ a) ((L.mem_smoothSet_iff ha).1 has))
      (orxPt B a has) p hp ha rfl k :=
  L.orxKAt_eq_mmorK ha has rfl p hp k

/-- **The hypothesis of `LineOrientation.conj` for `orxTAt`, `orxKAt`**: the conjugate of a member
of `Lin(f, a)` is a member of `Lin(f', x)`. -/
theorem orxTAt_mem (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) (ha : a ∈ U) (has : a ∈ PX.smoothSet)
    (hϕ : L.ϕ a = x) :
    ∀ S ∈ (orxPt B a has).linSet f, (((L.orxKAt ha has hϕ).symm : ↥(orxPt B a has).K →L[ℝ]
      ↥(orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)).K) ∘L S ∘L
        (L.orxTAt ha has hϕ : ↥(orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)).T →L[ℝ]
          ↥(orxPt B a has).T)) ∈ (orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)).linSet f' :=
  mmorT_mem hf hf' (linSet_mpullPt hf hf' hfL hsec hsec' has
    (L.mem_smoothSet_of_ϕ_eq ha has hϕ)) (L.mem_smoothSet_of_ϕ_eq ha has hϕ) has

/-- **The hypothesis of `LineOrientation.conj` for `orxT`, `orxK`.** -/
theorem orxT_mem (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) (ha : a ∈ U) (has : a ∈ PX.smoothSet) :
    ∀ S ∈ (orxPt B a has).linSet f, (((L.orxK ha has).symm : ↥(orxPt B a has).K →L[ℝ]
      ↥(orxPt B' (L.ϕ a) ((L.mem_smoothSet_iff ha).1 has)).K) ∘L S ∘L
        (L.orxT ha has : ↥(orxPt B' (L.ϕ a) ((L.mem_smoothSet_iff ha).1 has)).T →L[ℝ]
          ↥(orxPt B a has).T)) ∈
      (orxPt B' (L.ϕ a) ((L.mem_smoothSet_iff ha).1 has)).linSet f' :=
  L.orxTAt_mem hf hf' hfL hsec hsec' ha has rfl

/-- **`L⁻¹` on orientations in the chosen charts, at a point `x = ϕ(a)`**:
`Or^{f'}_x ≃ Or^f_a` for a smooth `a ∈ U`. -/
def orxViaAt (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) (ha : a ∈ U) (has : a ∈ PX.smoothSet)
    (hϕ : L.ϕ a = x) :
    Orx f' hf' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ) ≃ Orx f hf a has :=
  L.morVia hf hf' _ _ (L.innerPt x (L.mem_of_ϕ_eq ha hϕ) (L.mem_smoothSet_of_ϕ_eq ha has hϕ))
    (L.innerPt_sub _ _ _) ha hϕ (linSet_mpullPt hf hf' hfL hsec hsec' has
      (L.mem_smoothSet_of_ϕ_eq ha has hϕ)) (L.mem_smoothSet_of_ϕ_eq ha has hϕ) has

/-- For the equation `rfl`, `orxViaAt` is `orxVia`. -/
theorem orxViaAt_rfl (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) (ha : a ∈ U) (has : a ∈ PX.smoothSet) :
    L.orxViaAt hf hf' hfL hsec hsec' ha has rfl = L.orxVia hf hf' hfL hsec hsec' ha has := rfl

/-- **`orxViaAt` through any chart point inside `U'`** (`morVia_eq`). -/
theorem orxViaAt_eq_morVia (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) (ha : a ∈ U) (has : a ∈ PX.smoothSet)
    (hϕ : L.ϕ a = x) (p : ChartPoint B' x) (hp : p.c.φ.source ⊆ U') :
    L.orxViaAt hf hf' hfL hsec hsec' ha has hϕ =
      L.morVia hf hf' _ _ p hp ha hϕ (linSet_mpullPt hf hf' hfL hsec hsec' has
        (L.mem_smoothSet_of_ϕ_eq ha has hϕ)) (L.mem_smoothSet_of_ϕ_eq ha has hϕ) has :=
  L.morVia_eq hf hf' _ _ _ hp ha hϕ _ _ _ has

/-- **`orxViaAt` is the conjugation by `orxTAt` and `orxKAt`.** -/
theorem orxViaAt_apply (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) (ha : a ∈ U) (has : a ∈ PX.smoothSet)
    (hϕ : L.ϕ a = x) (o : Orx f' hf' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)) :
    L.orxViaAt hf hf' hfL hsec hsec' ha has hϕ o =
      o.conj (hC' := (orxPt B a has).isFredholm_of_mem_linSet hf) (L.orxTAt ha has hϕ)
        (L.orxKAt ha has hϕ) (L.orxTAt_mem hf hf' hfL hsec hsec' ha has hϕ) :=
  L.morVia_apply hf hf' _ _ _ _ ha hϕ _ _ has o

/-- **`orxVia` is the conjugation by `orxT` and `orxK`.** -/
theorem orxVia_apply (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) (ha : a ∈ U) (has : a ∈ PX.smoothSet)
    (o : Orx f' hf' (L.ϕ a) ((L.mem_smoothSet_iff ha).1 has)) :
    L.orxVia hf hf' hfL hsec hsec' ha has o =
      o.conj (hC' := (orxPt B a has).isFredholm_of_mem_linSet hf) (L.orxT ha has)
        (L.orxK ha has) (L.orxT_mem hf hf' hfL hsec hsec' ha has) :=
  L.orxViaAt_apply hf hf' hfL hsec hsec' ha has rfl o

/-- **The relation between the sections for `L⁻¹`**: if `f = Ψ ∘ f' ∘ ϕ` on `U`, then
`f' = Φ ∘ f ∘ g` on `U'`. -/
theorem eqOn_symm (hf' : IsSection P' f') (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) :
    EqOn f' (L.symm.Ψ ∘ f ∘ L.symm.ϕ) U' := fun y hy => by
  change f' y = L.Φ (f (L.g y))
  rw [hfL (L.base.mapsTo_inv hy)]
  change f' y = L.Φ (L.Ψ (f' (L.ϕ (L.g y))))
  rw [L.base.right_inv y hy, L.zero.right_inv _ (by rw [mem_preimage, hf' y]; exact hy)]

/-! ### Dependence on the germ only -/

variable {L}
variable {U₃ : Set X} {U₃' : Set X'} {L₃ : LocalIso B B' U₃ U₃'}

/-- **`orxTAt` depends only on the germ.** -/
theorem orxTAt_germ (ha : a ∈ U) (ha₃ : a ∈ U₃) (has : a ∈ PX.smoothSet) (hϕ : L.ϕ a = x)
    (hϕ₃ : L₃.ϕ a = x) (hG : GermEq L L₃ a)
    (v : ↥(orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)).T) :
    L.orxTAt ha has hϕ v = L₃.orxTAt ha₃ has hϕ₃ v := by
  obtain ⟨p, hp⟩ := exists_chartPoint_source_subset B' (L.mem_smoothSet_of_ϕ_eq ha has hϕ)
    (L.isOpen_U'.inter L₃.isOpen_U') ⟨L.mem_of_ϕ_eq ha hϕ, L₃.mem_of_ϕ_eq ha₃ hϕ₃⟩
  have h₁ : p.c.φ.source ⊆ U' := fun y hy => (hp hy).1
  have h₃ : p.c.φ.source ⊆ U₃' := fun y hy => (hp hy).2
  exact (L.orxTAt_eq_mmorT ha has hϕ p h₁ v).trans ((mmorT_germ _ _ p h₁ ha hϕ h₃ ha₃ hϕ₃ hG
    v).trans (L₃.orxTAt_eq_mmorT ha₃ has hϕ₃ p h₃ v).symm)

/-- **`orxKAt` depends only on the germ.** -/
theorem orxKAt_germ (ha : a ∈ U) (ha₃ : a ∈ U₃) (has : a ∈ PX.smoothSet) (hϕ : L.ϕ a = x)
    (hϕ₃ : L₃.ϕ a = x) (hG : GermEq L L₃ a)
    (k : ↥(orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)).K) :
    L.orxKAt ha has hϕ k = L₃.orxKAt ha₃ has hϕ₃ k := by
  obtain ⟨p, hp⟩ := exists_chartPoint_source_subset B' (L.mem_smoothSet_of_ϕ_eq ha has hϕ)
    (L.isOpen_U'.inter L₃.isOpen_U') ⟨L.mem_of_ϕ_eq ha hϕ, L₃.mem_of_ϕ_eq ha₃ hϕ₃⟩
  have h₁ : p.c.φ.source ⊆ U' := fun y hy => (hp hy).1
  have h₃ : p.c.φ.source ⊆ U₃' := fun y hy => (hp hy).2
  exact (L.orxKAt_eq_mmorK ha has hϕ p h₁ k).trans ((mmorK_germ _ _ p h₁ ha hϕ h₃ ha₃ hϕ₃ hG
    k).trans (L₃.orxKAt_eq_mmorK ha₃ has hϕ₃ p h₃ k).symm)

/-- **The orientation map depends only on the germ**: two local isomorphisms with the same germ
at `a` have the same `orxViaAt` at `a`. -/
theorem orxViaAt_germ (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hfL₃ : EqOn f (L₃.Ψ ∘ f' ∘ L₃.ϕ) U₃)
    (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough) (ha : a ∈ U)
    (ha₃ : a ∈ U₃) (has : a ∈ PX.smoothSet) (hϕ : L.ϕ a = x) (hϕ₃ : L₃.ϕ a = x)
    (hG : GermEq L L₃ a) :
    L.orxViaAt hf hf' hfL hsec hsec' ha has hϕ =
      L₃.orxViaAt hf hf' hfL₃ hsec hsec' ha₃ has hϕ₃ := by
  obtain ⟨p, hp⟩ := exists_chartPoint_source_subset B' (L.mem_smoothSet_of_ϕ_eq ha has hϕ)
    (L.isOpen_U'.inter L₃.isOpen_U') ⟨L.mem_of_ϕ_eq ha hϕ, L₃.mem_of_ϕ_eq ha₃ hϕ₃⟩
  have h₁ : p.c.φ.source ⊆ U' := fun y hy => (hp hy).1
  have h₃ : p.c.φ.source ⊆ U₃' := fun y hy => (hp hy).2
  exact (L.orxViaAt_eq_morVia hf hf' hfL hsec hsec' ha has hϕ p h₁).trans
    ((morVia_germ hf hf' _ _ p h₁ ha hϕ h₃ ha₃ hϕ₃ hG _ _ _ has).trans
      (L₃.orxViaAt_eq_morVia hf hf' hfL₃ hsec hsec' ha₃ has hϕ₃ p h₃).symm)

end StrongBundle.LocalIso

end Two

/-! ### Composites: squares and triangles -/

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
  {V₁ : Set X₂} {V₁' : Set X'} {V₂ : Set X} {V₂' : Set X₂} {V : Set X} {V' : Set X'}
  {f : X → Y} {f₁ : X₁ → Y₁} {f₂ : X₂ → Y₂} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {L : LocalIso B₁ B' U₁ U₁'} {L₂ : LocalIso B B₁ U₂ U₂'} {M : LocalIso B₂ B' V₁ V₁'}
  {M₂ : LocalIso B B₂ V₂ V₂'} {N : LocalIso B B' V V'} {x : X'} {x₁ : X₁} {x₂ : X₂} {b : X}

/-- The open subset of `U₁'` on which `L⁻¹` takes values in the target `U₂'` of `L₂`: chart
points of `Y'` inside it can be carried along `L` and then along `L₂`. -/
def twoStepSet (L : LocalIso B₁ B' U₁ U₁') (_L₂ : LocalIso B B₁ U₂ U₂') : Set X' :=
  U₁' ∩ L.g ⁻¹' U₂'

theorem isOpen_twoStepSet (L : LocalIso B₁ B' U₁ U₁') (L₂ : LocalIso B B₁ U₂ U₂') :
    IsOpen (twoStepSet L L₂) :=
  L.base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage L.isOpen_U' L₂.isOpen_U'

theorem mem_twoStepSet (hx₁ : x₁ ∈ U₁) (hϕ₁ : L.ϕ x₁ = x) (hb : b ∈ U₂) (hϕ₂ : L₂.ϕ b = x₁) :
    x ∈ twoStepSet L L₂ := by
  refine ⟨L.mem_of_ϕ_eq hx₁ hϕ₁, ?_⟩
  rw [mem_preimage, ← hϕ₁, L.base.left_inv _ hx₁]
  exact L₂.mem_of_ϕ_eq hb hϕ₂

/-- A chart point inside `twoStepSet`, carried along `L`, lies in the target of `L₂`. -/
theorem mpullPt_source_subset_of_twoStepSet (p : ChartPoint B' x)
    (hp : p.c.φ.source ⊆ twoStepSet L L₂) (hx₁ : x₁ ∈ U₁) (hϕ₁ : L.ϕ x₁ = x) :
    (L.mpullPt p (fun _ hy => (hp hy).1) hx₁ hϕ₁).c.φ.source ⊆ U₂' := by
  rintro y ⟨hyU, hyp⟩
  have := (hp hyp).2
  rwa [mem_preimage, L.base.left_inv y hyU] at this

/-- **Two steps through a common chart point** (base part): `mmorT` of `L₂` after `mmorT` of `L`
is the identification of the two-step carried chart point with the chart point at `b`. -/
theorem mmorT_mmorT (q' : ChartPoint B' x) (q₁ : ChartPoint B₁ x₁) (q : ChartPoint B b)
    (p₁ : ChartPoint B' x) (hp₁ : p₁.c.φ.source ⊆ U₁') (p₂ : ChartPoint B₁ x₁)
    (hp₂ : p₂.c.φ.source ⊆ U₂') (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hx₁ : x₁ ∈ U₁)
    (hϕ₁ : L.ϕ x₁ = x) (h₂ : (L.mpullPt p h₁ hx₁ hϕ₁).c.φ.source ⊆ U₂') (hb : b ∈ U₂)
    (hϕ₂ : L₂.ϕ b = x₁) (v : ↥q'.T) :
    L₂.mmorT q₁ q p₂ hp₂ hb hϕ₂ (L.mmorT q' q₁ p₁ hp₁ hx₁ hϕ₁ v) =
      (L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂).transferT q (q'.transferT p v) := by
  rw [L.mmorT_eq q' q₁ hp₁ h₁ hx₁ hϕ₁ v, L₂.mmorT_eq q₁ q hp₂ h₂ hb hϕ₂, mmorT_apply, mmorT_apply]
  set t : ↥(L.mpullPt p h₁ hx₁ hϕ₁).T := q'.transferT p v
  exact congrArg ((L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂).transferT q)
    (((L.mpullPt p h₁ hx₁ hϕ₁).transferT_trans_apply q₁ (L.mpullPt p h₁ hx₁ hϕ₁) t).trans
      ((L.mpullPt p h₁ hx₁ hϕ₁).transferT_self_apply t))

/-- **Two steps through a common chart point** (fibre part). -/
theorem mmorK_mmorK (q' : ChartPoint B' x) (q₁ : ChartPoint B₁ x₁) (q : ChartPoint B b)
    (p₁ : ChartPoint B' x) (hp₁ : p₁.c.φ.source ⊆ U₁') (p₂ : ChartPoint B₁ x₁)
    (hp₂ : p₂.c.φ.source ⊆ U₂') (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hx₁ : x₁ ∈ U₁)
    (hϕ₁ : L.ϕ x₁ = x) (h₂ : (L.mpullPt p h₁ hx₁ hϕ₁).c.φ.source ⊆ U₂') (hb : b ∈ U₂)
    (hϕ₂ : L₂.ϕ b = x₁) (k : ↥q'.K) :
    L₂.mmorK q₁ q p₂ hp₂ hb hϕ₂ (L.mmorK q' q₁ p₁ hp₁ hx₁ hϕ₁ k) =
      (L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂).transferK q (q'.transferK p k) := by
  rw [L.mmorK_eq q' q₁ hp₁ h₁ hx₁ hϕ₁ k, L₂.mmorK_eq q₁ q hp₂ h₂ hb hϕ₂, mmorK_apply, mmorK_apply]
  set t : ↥(L.mpullPt p h₁ hx₁ hϕ₁).K := q'.transferK p k
  exact congrArg ((L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂).transferK q)
    (((L.mpullPt p h₁ hx₁ hϕ₁).transferK_trans_apply q₁ (L.mpullPt p h₁ hx₁ hϕ₁) t).trans
      ((L.mpullPt p h₁ hx₁ hϕ₁).transferK_self_apply t))

/-- **The square of the base parts, in arbitrary chart points**: if `L ∘ L₂` and `M ∘ M₂` have
the same germ at `b`, then `mmorT` of `L₂` after that of `L` is `mmorT` of `M₂` after that of
`M`. -/
theorem mmorT_square (q' : ChartPoint B' x) (q₁ : ChartPoint B₁ x₁) (q₂ : ChartPoint B₂ x₂)
    (q : ChartPoint B b) (p₁ : ChartPoint B' x) (hp₁ : p₁.c.φ.source ⊆ U₁')
    (p₂ : ChartPoint B₁ x₁) (hp₂ : p₂.c.φ.source ⊆ U₂') (p₃ : ChartPoint B' x)
    (hp₃ : p₃.c.φ.source ⊆ V₁') (p₄ : ChartPoint B₂ x₂) (hp₄ : p₄.c.φ.source ⊆ V₂')
    (hx₁ : x₁ ∈ U₁) (hϕ₁ : L.ϕ x₁ = x) (hb : b ∈ U₂) (hϕ₂ : L₂.ϕ b = x₁) (hx₂ : x₂ ∈ V₁)
    (hψ₁ : M.ϕ x₂ = x) (hb' : b ∈ V₂) (hψ₂ : M₂.ϕ b = x₂) (hxs : x ∈ PX'.smoothSet)
    (hG : GermAgree₄ L L₂ M M₂ b) (v : ↥q'.T) :
    L₂.mmorT q₁ q p₂ hp₂ hb hϕ₂ (L.mmorT q' q₁ p₁ hp₁ hx₁ hϕ₁ v) =
      M₂.mmorT q₂ q p₄ hp₄ hb' hψ₂ (M.mmorT q' q₂ p₃ hp₃ hx₂ hψ₁ v) := by
  obtain ⟨p, hp⟩ := exists_chartPoint_source_subset B' hxs
    ((isOpen_twoStepSet L L₂).inter (isOpen_twoStepSet M M₂))
    ⟨mem_twoStepSet hx₁ hϕ₁ hb hϕ₂, mem_twoStepSet hx₂ hψ₁ hb' hψ₂⟩
  have hpL : p.c.φ.source ⊆ twoStepSet L L₂ := fun y hy => (hp hy).1
  have hpM : p.c.φ.source ⊆ twoStepSet M M₂ := fun y hy => (hp hy).2
  have h₁ : p.c.φ.source ⊆ U₁' := fun y hy => (hpL hy).1
  have k₁ : p.c.φ.source ⊆ V₁' := fun y hy => (hpM hy).1
  have h₂ := mpullPt_source_subset_of_twoStepSet p hpL hx₁ hϕ₁
  have k₂ := mpullPt_source_subset_of_twoStepSet p hpM hx₂ hψ₁
  rw [mmorT_mmorT q' q₁ q p₁ hp₁ p₂ hp₂ p h₁ hx₁ hϕ₁ h₂ hb hϕ₂ v,
    mmorT_mmorT q' q₂ q p₃ hp₃ p₄ hp₄ p k₁ hx₂ hψ₁ k₂ hb' hψ₂ v]
  set A := L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂ with hA
  set C := M₂.mpullPt (M.mpullPt p k₁ hx₂ hψ₁) k₂ hb' hψ₂ with hC
  set t : ↥C.T := q'.transferT p v
  have h4 := transferT_mpullPt₄ p h₁ hx₁ hϕ₁ h₂ hb hϕ₂ k₁ hx₂ hψ₁ k₂ hb' hψ₂ hG t
  exact (congrArg (A.transferT q) (Subtype.ext h4).symm).trans
    (ChartPoint.transferT_trans_apply C A q t)

/-- **The square of the fibre parts, in arbitrary chart points.** -/
theorem mmorK_square (q' : ChartPoint B' x) (q₁ : ChartPoint B₁ x₁) (q₂ : ChartPoint B₂ x₂)
    (q : ChartPoint B b) (p₁ : ChartPoint B' x) (hp₁ : p₁.c.φ.source ⊆ U₁')
    (p₂ : ChartPoint B₁ x₁) (hp₂ : p₂.c.φ.source ⊆ U₂') (p₃ : ChartPoint B' x)
    (hp₃ : p₃.c.φ.source ⊆ V₁') (p₄ : ChartPoint B₂ x₂) (hp₄ : p₄.c.φ.source ⊆ V₂')
    (hx₁ : x₁ ∈ U₁) (hϕ₁ : L.ϕ x₁ = x) (hb : b ∈ U₂) (hϕ₂ : L₂.ϕ b = x₁) (hx₂ : x₂ ∈ V₁)
    (hψ₁ : M.ϕ x₂ = x) (hb' : b ∈ V₂) (hψ₂ : M₂.ϕ b = x₂) (hxs : x ∈ PX'.smoothSet)
    (hG : GermAgree₄ L L₂ M M₂ b) (k : ↥q'.K) :
    L₂.mmorK q₁ q p₂ hp₂ hb hϕ₂ (L.mmorK q' q₁ p₁ hp₁ hx₁ hϕ₁ k) =
      M₂.mmorK q₂ q p₄ hp₄ hb' hψ₂ (M.mmorK q' q₂ p₃ hp₃ hx₂ hψ₁ k) := by
  obtain ⟨p, hp⟩ := exists_chartPoint_source_subset B' hxs
    ((isOpen_twoStepSet L L₂).inter (isOpen_twoStepSet M M₂))
    ⟨mem_twoStepSet hx₁ hϕ₁ hb hϕ₂, mem_twoStepSet hx₂ hψ₁ hb' hψ₂⟩
  have hpL : p.c.φ.source ⊆ twoStepSet L L₂ := fun y hy => (hp hy).1
  have hpM : p.c.φ.source ⊆ twoStepSet M M₂ := fun y hy => (hp hy).2
  have h₁ : p.c.φ.source ⊆ U₁' := fun y hy => (hpL hy).1
  have k₁ : p.c.φ.source ⊆ V₁' := fun y hy => (hpM hy).1
  have h₂ := mpullPt_source_subset_of_twoStepSet p hpL hx₁ hϕ₁
  have k₂ := mpullPt_source_subset_of_twoStepSet p hpM hx₂ hψ₁
  rw [mmorK_mmorK q' q₁ q p₁ hp₁ p₂ hp₂ p h₁ hx₁ hϕ₁ h₂ hb hϕ₂ k,
    mmorK_mmorK q' q₂ q p₃ hp₃ p₄ hp₄ p k₁ hx₂ hψ₁ k₂ hb' hψ₂ k]
  set A := L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂ with hA
  set C := M₂.mpullPt (M.mpullPt p k₁ hx₂ hψ₁) k₂ hb' hψ₂ with hC
  set t : ↥C.K := q'.transferK p k
  have h4 := transferK_mpullPt₄ p h₁ hx₁ hϕ₁ h₂ hb hϕ₂ k₁ hx₂ hψ₁ k₂ hb' hψ₂ hG t
  exact (congrArg (A.transferK q) (Subtype.ext h4).symm).trans
    (ChartPoint.transferK_trans_apply C A q t)

/-- **The triangle of the base parts, in arbitrary chart points**: if `L ∘ L₂ = N` near `b`, then
`mmorT` of `L₂` after that of `L` is `mmorT` of `N`. -/
theorem mmorT_triangle (q' : ChartPoint B' x) (q₁ : ChartPoint B₁ x₁) (q : ChartPoint B b)
    (p₁ : ChartPoint B' x) (hp₁ : p₁.c.φ.source ⊆ U₁') (p₂ : ChartPoint B₁ x₁)
    (hp₂ : p₂.c.φ.source ⊆ U₂') (p₃ : ChartPoint B' x) (hp₃ : p₃.c.φ.source ⊆ V')
    (hx₁ : x₁ ∈ U₁) (hϕ₁ : L.ϕ x₁ = x) (hb : b ∈ U₂) (hϕ₂ : L₂.ϕ b = x₁) (hb' : b ∈ V)
    (hψ : N.ϕ b = x) (hxs : x ∈ PX'.smoothSet)
    (hG : ∃ W : Set X, IsOpen W ∧ b ∈ W ∧ (∀ y ∈ W, L.ϕ (L₂.ϕ y) = N.ϕ y) ∧
      ∀ w, P w ∈ W → L.Φ (L₂.Φ w) = N.Φ w) (v : ↥q'.T) :
    L₂.mmorT q₁ q p₂ hp₂ hb hϕ₂ (L.mmorT q' q₁ p₁ hp₁ hx₁ hϕ₁ v) =
      N.mmorT q' q p₃ hp₃ hb' hψ v := by
  obtain ⟨p, hp⟩ := exists_chartPoint_source_subset B' hxs
    ((isOpen_twoStepSet L L₂).inter N.isOpen_U')
    ⟨mem_twoStepSet hx₁ hϕ₁ hb hϕ₂, N.mem_of_ϕ_eq hb' hψ⟩
  have hpL : p.c.φ.source ⊆ twoStepSet L L₂ := fun y hy => (hp hy).1
  have h₁ : p.c.φ.source ⊆ U₁' := fun y hy => (hpL hy).1
  have k₁ : p.c.φ.source ⊆ V' := fun y hy => (hp hy).2
  have h₂ := mpullPt_source_subset_of_twoStepSet p hpL hx₁ hϕ₁
  rw [mmorT_mmorT q' q₁ q p₁ hp₁ p₂ hp₂ p h₁ hx₁ hϕ₁ h₂ hb hϕ₂ v,
    N.mmorT_eq q' q hp₃ k₁ hb' hψ v, mmorT_apply]
  set A := L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂ with hA
  set C := N.mpullPt p k₁ hb' hψ with hC
  set t : ↥C.T := q'.transferT p v
  have h4 := transferT_mpullPt₃ p h₁ hx₁ hϕ₁ h₂ hb hϕ₂ k₁ hb' hψ hG t
  exact (congrArg (A.transferT q) (Subtype.ext h4).symm).trans
    (ChartPoint.transferT_trans_apply C A q t)

/-- **The triangle of the fibre parts, in arbitrary chart points.** -/
theorem mmorK_triangle (q' : ChartPoint B' x) (q₁ : ChartPoint B₁ x₁) (q : ChartPoint B b)
    (p₁ : ChartPoint B' x) (hp₁ : p₁.c.φ.source ⊆ U₁') (p₂ : ChartPoint B₁ x₁)
    (hp₂ : p₂.c.φ.source ⊆ U₂') (p₃ : ChartPoint B' x) (hp₃ : p₃.c.φ.source ⊆ V')
    (hx₁ : x₁ ∈ U₁) (hϕ₁ : L.ϕ x₁ = x) (hb : b ∈ U₂) (hϕ₂ : L₂.ϕ b = x₁) (hb' : b ∈ V)
    (hψ : N.ϕ b = x) (hxs : x ∈ PX'.smoothSet)
    (hG : ∃ W : Set X, IsOpen W ∧ b ∈ W ∧ (∀ y ∈ W, L.ϕ (L₂.ϕ y) = N.ϕ y) ∧
      ∀ w, P w ∈ W → L.Φ (L₂.Φ w) = N.Φ w) (k : ↥q'.K) :
    L₂.mmorK q₁ q p₂ hp₂ hb hϕ₂ (L.mmorK q' q₁ p₁ hp₁ hx₁ hϕ₁ k) =
      N.mmorK q' q p₃ hp₃ hb' hψ k := by
  obtain ⟨p, hp⟩ := exists_chartPoint_source_subset B' hxs
    ((isOpen_twoStepSet L L₂).inter N.isOpen_U')
    ⟨mem_twoStepSet hx₁ hϕ₁ hb hϕ₂, N.mem_of_ϕ_eq hb' hψ⟩
  have hpL : p.c.φ.source ⊆ twoStepSet L L₂ := fun y hy => (hp hy).1
  have h₁ : p.c.φ.source ⊆ U₁' := fun y hy => (hpL hy).1
  have k₁ : p.c.φ.source ⊆ V' := fun y hy => (hp hy).2
  have h₂ := mpullPt_source_subset_of_twoStepSet p hpL hx₁ hϕ₁
  rw [mmorK_mmorK q' q₁ q p₁ hp₁ p₂ hp₂ p h₁ hx₁ hϕ₁ h₂ hb hϕ₂ k,
    N.mmorK_eq q' q hp₃ k₁ hb' hψ k, mmorK_apply]
  set A := L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂ with hA
  set C := N.mpullPt p k₁ hb' hψ with hC
  set t : ↥C.K := q'.transferK p k
  have h4 := transferK_mpullPt₃ p h₁ hx₁ hϕ₁ h₂ hb hϕ₂ k₁ hb' hψ hG t
  exact (congrArg (A.transferK q) (Subtype.ext h4).symm).trans
    (ChartPoint.transferK_trans_apply C A q t)

/-! ### The chosen chart points -/

/-- **The square of the maps `T_xX' → T_bX`**: for `L ∘ L₂` and `M ∘ M₂` with the same germ at
`b`, `orxTAt` of `L₂` after that of `L` is `orxTAt` of `M₂` after that of `M`. -/
theorem orxTAt_square (hb : b ∈ U₂) (hb' : b ∈ V₂) (hbs : b ∈ PX.smoothSet)
    (hx₁ : L₂.ϕ b = x₁) (hx₂ : M₂.ϕ b = x₂) (hU : x₁ ∈ U₁) (hV : x₂ ∈ V₁) (hx : L.ϕ x₁ = x)
    (hx' : M.ϕ x₂ = x) (hG : GermAgree₄ L L₂ M M₂ b)
    (v : ↥(orxPt B' x (L.mem_smoothSet_of_ϕ_eq hU
      (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx)).T) :
    L₂.orxTAt hb hbs hx₁ (L.orxTAt hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx v) =
      M₂.orxTAt hb' hbs hx₂ (M.orxTAt hV (M₂.mem_smoothSet_of_ϕ_eq hb' hbs hx₂) hx' v) :=
  mmorT_square _ _ _ _ _ _ _ _ _ _ _ _ hU hx hb hx₁ hV hx' hb' hx₂
    (L.mem_smoothSet_of_ϕ_eq hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx) hG v

/-- **The square of the maps `Y'_x → Y_b`.** -/
theorem orxKAt_square (hb : b ∈ U₂) (hb' : b ∈ V₂) (hbs : b ∈ PX.smoothSet)
    (hx₁ : L₂.ϕ b = x₁) (hx₂ : M₂.ϕ b = x₂) (hU : x₁ ∈ U₁) (hV : x₂ ∈ V₁) (hx : L.ϕ x₁ = x)
    (hx' : M.ϕ x₂ = x) (hG : GermAgree₄ L L₂ M M₂ b)
    (k : ↥(orxPt B' x (L.mem_smoothSet_of_ϕ_eq hU
      (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx)).K) :
    L₂.orxKAt hb hbs hx₁ (L.orxKAt hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx k) =
      M₂.orxKAt hb' hbs hx₂ (M.orxKAt hV (M₂.mem_smoothSet_of_ϕ_eq hb' hbs hx₂) hx' k) :=
  mmorK_square _ _ _ _ _ _ _ _ _ _ _ _ hU hx hb hx₁ hV hx' hb' hx₂
    (L.mem_smoothSet_of_ϕ_eq hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx) hG k

/-- **The triangle of the maps `T_xX' → T_bX`**: for `L ∘ L₂ = N` near `b`, `orxTAt` of `L₂`
after that of `L` is `orxTAt` of `N`. -/
theorem orxTAt_triangle (hb : b ∈ U₂) (hb' : b ∈ V) (hbs : b ∈ PX.smoothSet)
    (hx₁ : L₂.ϕ b = x₁) (hU : x₁ ∈ U₁) (hx : L.ϕ x₁ = x) (hx' : N.ϕ b = x)
    (hG : ∃ W : Set X, IsOpen W ∧ b ∈ W ∧ (∀ y ∈ W, L.ϕ (L₂.ϕ y) = N.ϕ y) ∧
      ∀ w, P w ∈ W → L.Φ (L₂.Φ w) = N.Φ w)
    (v : ↥(orxPt B' x (N.mem_smoothSet_of_ϕ_eq hb' hbs hx')).T) :
    L₂.orxTAt hb hbs hx₁ (L.orxTAt hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx v) =
      N.orxTAt hb' hbs hx' v :=
  mmorT_triangle _ _ _ _ _ _ _ _ _ hU hx hb hx₁ hb' hx'
    (N.mem_smoothSet_of_ϕ_eq hb' hbs hx') hG v

/-- **The triangle of the maps `Y'_x → Y_b`.** -/
theorem orxKAt_triangle (hb : b ∈ U₂) (hb' : b ∈ V) (hbs : b ∈ PX.smoothSet)
    (hx₁ : L₂.ϕ b = x₁) (hU : x₁ ∈ U₁) (hx : L.ϕ x₁ = x) (hx' : N.ϕ b = x)
    (hG : ∃ W : Set X, IsOpen W ∧ b ∈ W ∧ (∀ y ∈ W, L.ϕ (L₂.ϕ y) = N.ϕ y) ∧
      ∀ w, P w ∈ W → L.Φ (L₂.Φ w) = N.Φ w)
    (k : ↥(orxPt B' x (N.mem_smoothSet_of_ϕ_eq hb' hbs hx')).K) :
    L₂.orxKAt hb hbs hx₁ (L.orxKAt hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx k) =
      N.orxKAt hb' hbs hx' k :=
  mmorK_triangle _ _ _ _ _ _ _ _ _ hU hx hb hx₁ hb' hx'
    (N.mem_smoothSet_of_ϕ_eq hb' hbs hx') hG k

/-! ### Orientations -/

/-- **Two orientation maps in a row are the conjugation by the composites** of the maps
`orxTAt` and of the maps `orxKAt`. -/
theorem orxViaAt_trans_apply (hf : B.IsScFredholmSection f) (hf₁ : B₁.IsScFredholmSection f₁)
    (hf' : B'.IsScFredholmSection f') (hfL : EqOn f₁ (L.Ψ ∘ f' ∘ L.ϕ) U₁)
    (hfL₂ : EqOn f (L₂.Ψ ∘ f₁ ∘ L₂.ϕ) U₂) (hsec : B.HasScPlusSectionsThrough)
    (hsec₁ : B₁.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough) (hb : b ∈ U₂)
    (hbs : b ∈ PX.smoothSet) (hx₁ : L₂.ϕ b = x₁) (hU : x₁ ∈ U₁) (hx : L.ϕ x₁ = x)
    (o : Orx f' hf' x (L.mem_smoothSet_of_ϕ_eq hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx)) :
    ((L.orxViaAt hf₁ hf' hfL hsec₁ hsec' hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx).trans
      (L₂.orxViaAt hf hf₁ hfL₂ hsec hsec₁ hb hbs hx₁)) o =
      o.conj (hC' := (orxPt B b hbs).isFredholm_of_mem_linSet hf)
        ((L.orxTAt hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx).trans (L₂.orxTAt hb hbs hx₁))
        ((L.orxKAt hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx).trans (L₂.orxKAt hb hbs hx₁))
        (conj_mem_trans _ _ _ _
          (L.orxTAt_mem hf₁ hf' hfL hsec₁ hsec' hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx)
          (L₂.orxTAt_mem hf hf₁ hfL₂ hsec hsec₁ hb hbs hx₁)) := by
  have m1 := L.orxTAt_mem hf₁ hf' hfL hsec₁ hsec' hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx
  have m2 := L₂.orxTAt_mem hf hf₁ hfL₂ hsec hsec₁ hb hbs hx₁
  have e1 := L.orxViaAt_apply hf₁ hf' hfL hsec₁ hsec' hU
    (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx o
  have e2 := L₂.orxViaAt_apply hf hf₁ hfL₂ hsec hsec₁ hb hbs hx₁
    (L.orxViaAt hf₁ hf' hfL hsec₁ hsec' hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx o)
  refine (Equiv.trans_apply _ _ o).trans (e2.trans ?_)
  rw [e1]
  exact LineOrientation.conj_trans
    (hC' := (orxPt B₁ x₁ (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁)).isFredholm_of_mem_linSet hf₁)
    (hC'' := (orxPt B b hbs).isFredholm_of_mem_linSet hf) _ _ _ _ m1 m2
    (conj_mem_trans _ _ _ _ m1 m2) o

/-- **The square of the orientation maps** (functoriality of `orxVia`): if `L ∘ L₂` and
`M ∘ M₂` have the same germ at `b`, then the orientation map of `L₂` after that of `L` is the
orientation map of `M₂` after that of `M`, as bijections `Or^{f'}_x ≃ Or^f_b`. -/
theorem orxViaAt_square (hf : B.IsScFredholmSection f) (hf₁ : B₁.IsScFredholmSection f₁)
    (hf₂ : B₂.IsScFredholmSection f₂) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f₁ (L.Ψ ∘ f' ∘ L.ϕ) U₁) (hfL₂ : EqOn f (L₂.Ψ ∘ f₁ ∘ L₂.ϕ) U₂)
    (hfM : EqOn f₂ (M.Ψ ∘ f' ∘ M.ϕ) V₁) (hfM₂ : EqOn f (M₂.Ψ ∘ f₂ ∘ M₂.ϕ) V₂)
    (hsec : B.HasScPlusSectionsThrough) (hsec₁ : B₁.HasScPlusSectionsThrough)
    (hsec₂ : B₂.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough) (hb : b ∈ U₂)
    (hb' : b ∈ V₂) (hbs : b ∈ PX.smoothSet) (hx₁ : L₂.ϕ b = x₁) (hx₂ : M₂.ϕ b = x₂)
    (hU : x₁ ∈ U₁) (hV : x₂ ∈ V₁) (hx : L.ϕ x₁ = x) (hx' : M.ϕ x₂ = x)
    (hG : GermAgree₄ L L₂ M M₂ b) :
    (L.orxViaAt hf₁ hf' hfL hsec₁ hsec' hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx).trans
      (L₂.orxViaAt hf hf₁ hfL₂ hsec hsec₁ hb hbs hx₁) =
    (M.orxViaAt hf₂ hf' hfM hsec₂ hsec' hV (M₂.mem_smoothSet_of_ϕ_eq hb' hbs hx₂) hx').trans
      (M₂.orxViaAt hf hf₂ hfM₂ hsec hsec₂ hb' hbs hx₂) :=
  Equiv.ext fun o =>
    (orxViaAt_trans_apply hf hf₁ hf' hfL hfL₂ hsec hsec₁ hsec' hb hbs hx₁ hU hx o).trans
      ((LineOrientation.conj_congr
        (orxTAt_square hb hb' hbs hx₁ hx₂ hU hV hx hx' hG)
        (orxKAt_square hb hb' hbs hx₁ hx₂ hU hV hx hx' hG) _ _ o).trans
        (orxViaAt_trans_apply hf hf₂ hf' hfM hfM₂ hsec hsec₂ hsec' hb' hbs hx₂ hV hx' o).symm)

/-- **The triangle of the orientation maps**: if `L ∘ L₂ = N` near `b`, the orientation map of
`N` is that of `L₂` after that of `L`. -/
theorem orxViaAt_triangle (hf : B.IsScFredholmSection f) (hf₁ : B₁.IsScFredholmSection f₁)
    (hf' : B'.IsScFredholmSection f') (hfL : EqOn f₁ (L.Ψ ∘ f' ∘ L.ϕ) U₁)
    (hfL₂ : EqOn f (L₂.Ψ ∘ f₁ ∘ L₂.ϕ) U₂) (hfN : EqOn f (N.Ψ ∘ f' ∘ N.ϕ) V)
    (hsec : B.HasScPlusSectionsThrough) (hsec₁ : B₁.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) (hb : b ∈ U₂) (hb' : b ∈ V)
    (hbs : b ∈ PX.smoothSet) (hx₁ : L₂.ϕ b = x₁) (hU : x₁ ∈ U₁) (hx : L.ϕ x₁ = x)
    (hx' : N.ϕ b = x)
    (hG : ∃ W : Set X, IsOpen W ∧ b ∈ W ∧ (∀ y ∈ W, L.ϕ (L₂.ϕ y) = N.ϕ y) ∧
      ∀ w, P w ∈ W → L.Φ (L₂.Φ w) = N.Φ w) :
    (L.orxViaAt hf₁ hf' hfL hsec₁ hsec' hU (L₂.mem_smoothSet_of_ϕ_eq hb hbs hx₁) hx).trans
      (L₂.orxViaAt hf hf₁ hfL₂ hsec hsec₁ hb hbs hx₁) =
    N.orxViaAt hf hf' hfN hsec hsec' hb' hbs hx' :=
  Equiv.ext fun o =>
    (orxViaAt_trans_apply hf hf₁ hf' hfL hfL₂ hsec hsec₁ hsec' hb hbs hx₁ hU hx o).trans
      ((LineOrientation.conj_congr
        (orxTAt_triangle hb hb' hbs hx₁ hU hx hx' hG)
        (orxKAt_triangle hb hb' hbs hx₁ hU hx hx' hG) _ _ o).trans
        (N.orxViaAt_apply hf hf' hfN hsec hsec' hb' hbs hx' o).symm)

end StrongBundle.LocalIso

end Compose

/-! ### The identity and the inverse -/

section Identity

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U U' : Set X} (L : LocalIso B B U U') {b : X}

/-- A local isomorphism with the germ of the identity at `b` is idempotent near `b`. -/
theorem germ_comp_self_of_germ_id
    (hG : ∃ W : Set X, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ (∀ y ∈ W, L.ϕ y = y) ∧
      ∀ w, P w ∈ W → L.Φ w = w) :
    ∃ W : Set X, IsOpen W ∧ b ∈ W ∧ (∀ y ∈ W, L.ϕ (L.ϕ y) = L.ϕ y) ∧
      ∀ w, P w ∈ W → L.Φ (L.Φ w) = L.Φ w := by
  obtain ⟨W, hWo, hbW, -, hϕ, hΦ⟩ := hG
  exact ⟨W, hWo, hbW, fun y hy => congrArg L.ϕ (hϕ y hy), fun w hw => congrArg L.Φ (hΦ w hw)⟩

/-- **The identity on `T_bX`**: a local isomorphism with the germ of the identity at `b` has
`orxTAt = id` at `b`. -/
theorem orxTAt_of_germ_id (hb : b ∈ U) (hbs : b ∈ PX.smoothSet) (hϕ : L.ϕ b = b)
    (hG : ∃ W : Set X, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ (∀ y ∈ W, L.ϕ y = y) ∧
      ∀ w, P w ∈ W → L.Φ w = w) (v : ↥(orxPt B b hbs).T) : L.orxTAt hb hbs hϕ v = v :=
  (L.orxTAt hb hbs hϕ).injective
    (orxTAt_triangle (L := L) (L₂ := L) (N := L) hb hb hbs hϕ hb hϕ hϕ
      (L.germ_comp_self_of_germ_id hG) v)

/-- **The identity on `Y_b`**: a local isomorphism with the germ of the identity at `b` has
`orxKAt = id` at `b`. -/
theorem orxKAt_of_germ_id (hb : b ∈ U) (hbs : b ∈ PX.smoothSet) (hϕ : L.ϕ b = b)
    (hG : ∃ W : Set X, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ (∀ y ∈ W, L.ϕ y = y) ∧
      ∀ w, P w ∈ W → L.Φ w = w) (k : ↥(orxPt B b hbs).K) : L.orxKAt hb hbs hϕ k = k :=
  (L.orxKAt hb hbs hϕ).injective
    (orxKAt_triangle (L := L) (L₂ := L) (N := L) hb hb hbs hϕ hb hϕ hϕ
      (L.germ_comp_self_of_germ_id hG) k)

/-- **The orientation map of the identity is the identity**: a local isomorphism of one bundle
with the germ of the identity at `b` acts trivially on `Or^f_b`. -/
theorem orxViaAt_of_germ_id {f : X → Y} (hf : B.IsScFredholmSection f)
    (hfL : EqOn f (L.Ψ ∘ f ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough) (hb : b ∈ U)
    (hbs : b ∈ PX.smoothSet) (hϕ : L.ϕ b = b)
    (hG : ∃ W : Set X, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ (∀ y ∈ W, L.ϕ y = y) ∧
      ∀ w, P w ∈ W → L.Φ w = w) :
    L.orxViaAt hf hf hfL hsec hsec hb hbs hϕ = Equiv.refl _ :=
  Equiv.ext fun o => (L.orxViaAt_apply hf hf hfL hsec hsec hb hbs hϕ o).trans
    ((LineOrientation.conj_congr (hC' := (orxPt B b hbs).isFredholm_of_mem_linSet hf)
      (A₂ := ContinuousLinearEquiv.refl ℝ ↥(orxPt B b hbs).T)
      (Γ₂ := ContinuousLinearEquiv.refl ℝ ↥(orxPt B b hbs).K)
      (L.orxTAt_of_germ_id hb hbs hϕ hG) (L.orxKAt_of_germ_id hb hbs hϕ hG) _
      (conj_mem_refl _) o).trans (LineOrientation.conj_refl _ o))

/-- The relation between the sections for the identity. -/
theorem eqOn_refl (f : X → Y) :
    EqOn f ((LocalIso.refl B).Ψ ∘ f ∘ (LocalIso.refl B).ϕ) univ := fun _ _ => rfl

/-- **The orientation map of `LocalIso.refl` is the identity.** -/
theorem orxViaAt_refl {f : X → Y} (hf : B.IsScFredholmSection f)
    (hsec : B.HasScPlusSectionsThrough) (hbs : b ∈ PX.smoothSet) :
    (LocalIso.refl B).orxViaAt hf hf (eqOn_refl f) hsec hsec (mem_univ b) hbs rfl =
      Equiv.refl _ :=
  (LocalIso.refl B).orxViaAt_of_germ_id hf (eqOn_refl f) hsec (mem_univ b) hbs rfl
    ⟨univ, isOpen_univ, mem_univ b, subset_rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end StrongBundle.LocalIso

namespace StrongBundle.LocalIso

variable {U : Set X} {U' : Set X'} (L : LocalIso B B' U U') {a : X} {x : X'}

/-- **The orientation map of the inverse is the inverse of the orientation map**: for
`ϕ(a) = x` and `g(x) = a`, `orxViaAt` of `L⁻¹` at `x` is the inverse of `orxViaAt` of `L` at
`a`. -/
theorem orxViaAt_symm (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hfL' : EqOn f' (L.symm.Ψ ∘ f ∘ L.symm.ϕ) U')
    (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough) (ha : a ∈ U)
    (has : a ∈ PX.smoothSet) (hϕ : L.ϕ a = x) (hg : L.symm.ϕ x = a) :
    L.symm.orxViaAt hf' hf hfL' hsec' hsec (L.mem_of_ϕ_eq ha hϕ)
      (L.mem_smoothSet_of_ϕ_eq ha has hϕ) hg =
      (L.orxViaAt hf hf' hfL hsec hsec' ha has hϕ).symm := by
  have hG : ∃ W : Set X, IsOpen W ∧ a ∈ W ∧ (∀ y ∈ W, L.symm.ϕ (L.ϕ y) = (LocalIso.refl B).ϕ y) ∧
      ∀ w, P w ∈ W → L.symm.Φ (L.Φ w) = (LocalIso.refl B).Φ w :=
    ⟨U, L.isOpen_U, ha, fun y hy => L.base.left_inv y hy, fun w hw => L.zero.left_inv w hw⟩
  have h := (orxViaAt_triangle (L := L.symm) (L₂ := L) (N := LocalIso.refl B) hf hf' hf hfL' hfL
    (eqOn_refl f) hsec hsec' hsec ha (mem_univ a) has hϕ (L.mem_of_ϕ_eq ha hϕ) hg rfl hG).trans
      (orxViaAt_refl hf hsec has)
  refine Equiv.ext fun o => ?_
  have h' := congrFun (congrArg DFunLike.coe h) o
  exact (Equiv.eq_symm_apply (L.orxViaAt hf hf' hfL hsec hsec' ha has hϕ)).2 h'

end StrongBundle.LocalIso

end Identity

end Polyfold
