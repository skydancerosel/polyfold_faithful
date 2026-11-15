import Polyfold.Chapter12.LocalOrientationSpace

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 592–597: the maps of orientations induced by local strong bundle isomorphisms (the proofs of
Lemma 12.5.1, Theorem 12.5.3 and Theorem 12.5.7), for the linearizations made with local
sc⁺-sections.

# Local strong bundle isomorphisms and the local orientation sets

## The text, paraphrased

A local strong bundle isomorphism `Φ : W|U → W'|U'` covering a local sc-diffeomorphism `ϕ`
carries a local sc⁺-section `s'` near `ϕ(a)` to the local sc⁺-section `Φ^* s'` near `a`, and
`(f − Φ^* s')'(a) = Φ⁻¹ ∘ (f' − s')'(ϕ(a)) ∘ Tϕ(a)` when `f = Φ^* f'`.  Hence it maps
`Lin(f', ϕ(a))` onto `Lin(f, a)` and induces a bijection between the orientations of
`DET(f', ϕ(a))` and of `DET(f, a)`.  The maps induced by morphisms (Lemma 12.5.1), by strong
bundle equivalences and by the diagrams relating two representatives of a generalized strong
bundle isomorphism (proof of Theorem 12.5.7, "canonical lifts to maps between the bundle
fibers") are of this kind, and they are compatible with the propagation of orientations along
sc-smooth paths (last sentence of Theorem 12.5.3).

## What is formalized

For strong bundles `B`, `B'` over tame M-polyfolds, sections `f`, `f'` with tame germ data and
a local strong bundle isomorphism `L : LocalIso B B' U U'` with `f = Ψ ∘ f' ∘ ϕ` on `U`.  The
orientation sets are the local ones, `OrxLoc` (linearizations made with the sc⁺-sections over a
domain); no sc⁺-sections over the whole base and no sc-smooth bump functions are assumed.

* `LocalIso.domIso D D'`: `L` read as a local strong bundle isomorphism `P|D → P'|D'` for
  domains `D` of `B` and `D'` of `B'`; `sec_eqOn_domIso`.
* `germAgree₄_domIso`, `germAgree₄_domIso_iso`: squares of local isomorphisms which commute as
  germs keep doing so when read in domains.
* `LocalIso.orDom`, `LocalIso.orLoc`: **the map `Or_{ϕ(a)}^{f'} ≃ Or_a^f`**, read in two domains
  and on the local orientation sets; `orDom_compare`, `orDom_toLoc` (independence of the
  domains).
* `orLoc_square`, `orLoc_triangle`, `orLoc_germ`, `orLoc_refl`, `orLoc_of_germ_id`,
  `orLoc_symm`: functoriality for germs of local isomorphisms.
* `orLoc_comm`: **the maps commute with the propagation along sc-smooth paths in `U`**.
* `pullLoc`, `isContOn_pullLoc`, `isContOn_of_pullLoc`: a family of orientations of `f'` is
  continuous over `U' ∩ V'` iff the family carried by `L` is continuous over `U ∩ ϕ⁻¹(V')`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v u' v' u₁ v₁ u₂ v₂

section Two

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U : Set X} {U' : Set X'} (L : LocalIso B B' U U')

/-! ### A local isomorphism read in two domains -/

/-- The part of the domain `D` on which `L` is defined with values in the domain `D'`. -/
def domSet (D : B.Dom) (D' : B'.Dom) : Set D.carrier :=
  {w | w.1 ∈ U ∧ L.ϕ w.1 ∈ D'.carrier}

/-- The image of `domSet` in the domain `D'`. -/
def domTarget (D : B.Dom) (D' : B'.Dom) : Set D'.carrier :=
  {v | v.1 ∈ U' ∧ L.g v.1 ∈ D.carrier}

/-- **A local strong bundle isomorphism read in two domains**: for a domain `D` of `B` and a
domain `D'` of `B'`, the composite of the inclusion `P|D → P`, of `L` and of the inverse of the
inclusion `P'|D' → P'`, a local strong bundle isomorphism `P|D → P'|D'`. -/
def domIso (D : B.Dom) (D' : B'.Dom) :
    LocalIso D.bundle D'.bundle (L.domSet D D') (L.domTarget D D') :=
  (((B.restrictIso D.isOpen).trans L).trans (B'.restrictIso D'.isOpen).symm).ofEq
    (Set.ext fun _ => ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨mem_univ _, h.1⟩, h.2⟩⟩)
    (Set.ext fun _ => ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩)

variable {L}

theorem domIso_ϕ_of_mem {D : B.Dom} {D' : B'.Dom} {w : D.carrier} (hw : w ∈ L.domSet D D') :
    (L.domIso D D').ϕ w = ⟨L.ϕ w.1, hw.2⟩ :=
  MPolyfold.openRetraction_of_mem hw.2

variable (L)

theorem domIso_Φ_apply (D : B.Dom) (D' : B'.Dom)
    (q : pullbackSpace P (Subtype.val : D.carrier → X)) :
    (L.domIso D D').Φ q = B'.restrictIsoInv D'.carrier (L.Φ q.1.2) := rfl

theorem domIso_Ψ_apply (D : B.Dom) (D' : B'.Dom)
    (q : pullbackSpace P' (Subtype.val : D'.carrier → X')) :
    (L.domIso D D').Ψ q = B.restrictIsoInv D.carrier (L.Ψ q.1.2) := rfl

/-- A point `a ∈ U ∩ D` with `ϕ(a) ∈ D'` lies in the domain of `domIso D D'`. -/
theorem mem_domSet {D : B.Dom} {D' : B'.Dom} {a : X} {x : X'} (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (haD : a ∈ D.carrier) (hxD : x ∈ D'.carrier) : (⟨a, haD⟩ : D.carrier) ∈ L.domSet D D' :=
  ⟨ha, by change L.ϕ a ∈ D'.carrier; rw [hϕ]; exact hxD⟩

theorem domIso_ϕ_mk {D : B.Dom} {D' : B'.Dom} {a : X} {x : X'} (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (haD : a ∈ D.carrier) (hxD : x ∈ D'.carrier) :
    (L.domIso D D').ϕ ⟨a, haD⟩ = ⟨x, hxD⟩ :=
  (domIso_ϕ_of_mem (L.mem_domSet ha hϕ haD hxD)).trans (Subtype.ext hϕ)

/-- **The restrictions of corresponding sections to two domains correspond**: if
`f = Ψ ∘ f' ∘ ϕ` on `U`, then `f|D = Ψ ∘ f'|D' ∘ ϕ` on the domain of `domIso D D'`. -/
theorem sec_eqOn_domIso (hfs : IsSection P f) (hfs' : IsSection P' f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (D : B.Dom) (D' : B'.Dom) :
    EqOn (D.sec f hfs) ((L.domIso D D').Ψ ∘ D'.sec f' hfs' ∘ (L.domIso D D').ϕ)
      (L.domSet D D') := by
  intro w hw
  have h1 : f w.1 = L.Ψ (f' (L.ϕ w.1)) := hfL hw.1
  have h2 := B.restrictSection_eqOn_restrictIso D.isOpen hfs (mem_univ w)
  change D.sec f hfs w = B.restrictIsoInv D.carrier
    (L.Ψ ((D'.sec f' hfs' ((L.domIso D D').ϕ w)).1.2))
  rw [domIso_ϕ_of_mem hw]
  change D.sec f hfs w = B.restrictIsoInv D.carrier (L.Ψ (f' (L.ϕ w.1)))
  rw [← h1]
  exact h2

/-- **Change of the domains**: for domains `D₁, D₂ ∋ a` and `D₁', D₂' ∋ ϕ(a)`, `L` read in
`D₁`, `D₁'` followed by the identification of `D₁'` with `D₂'` is, near `a`, the identification
of `D₁` with `D₂` followed by `L` read in `D₂`, `D₂'`. -/
theorem germAgree₄_domIso_iso {a : X} {x : X'} (ha : a ∈ U) (hϕ : L.ϕ a = x) {D₁ D₂ : B.Dom}
    {D₁' D₂' : B'.Dom} (ha₁ : a ∈ D₁.carrier) (ha₂ : a ∈ D₂.carrier) (hx₁ : x ∈ D₁'.carrier)
    (hx₂ : x ∈ D₂'.carrier) :
    GermAgree₄ (D₁'.iso D₂') (L.domIso D₁ D₁') (L.domIso D₂ D₂') (D₁.iso D₂)
      (⟨a, ha₁⟩ : D₁.carrier) := by
  have hO := (L.domIso D₁ D₁').base.isScSmoothOn.continuousOn.isOpen_inter_preimage
    (L.domIso D₁ D₁').isOpen_U (D₁'.iso D₂').isOpen_U
  refine ⟨⟨{w : D₁.carrier | w.1 ∈ D₂.carrier} ∩ (L.domSet D₁ D₁' ∩
      (L.domIso D₁ D₁').ϕ ⁻¹' {v : D₁'.carrier | v.1 ∈ D₂'.carrier}),
    (D₂.isOpen.preimage continuous_subtype_val).inter hO,
    ⟨ha₂, L.mem_domSet ha hϕ ha₁ hx₁, ?_⟩, fun w hw => hw.2.1, fun w hw => hw.1,
    fun w hw => ?_, fun q hq => ?_⟩⟩
  · rw [mem_preimage, L.domIso_ϕ_mk ha hϕ ha₁ hx₁]; exact hx₂
  · have h1 := domIso_ϕ_of_mem hw.2.1
    have h2 : L.ϕ w.1 ∈ D₂'.carrier := by
      have := hw.2.2; rw [mem_preimage, h1] at this; exact this
    have h3 : (⟨w.1, hw.1⟩ : D₂.carrier) ∈ L.domSet D₂ D₂' := ⟨hw.2.1.1, h2⟩
    rw [h1, D₁'.iso_ϕ_of_mem D₂' h2, D₁.iso_ϕ_of_mem D₂ hw.1, domIso_ϕ_of_mem h3]
  · have hPq : P q.1.2 = q.1.1.1 := StrongBundle.pullbackSpace_subtypeVal_proj q
    have h1 : P' (L.Φ q.1.2) ∈ D₁'.carrier := by
      rw [L.covers _ (by rw [hPq]; exact hq.2.1.1), hPq]; exact hq.2.1.2
    have h2 : P q.1.2 ∈ D₂.carrier := by rw [hPq]; exact hq.1
    change B'.restrictIsoInv D₂'.carrier ((L.domIso D₁ D₁').Φ q).1.2 =
      (L.domIso D₂ D₂').Φ (B.restrictIsoInv D₂.carrier q.1.2)
    rw [L.domIso_Φ_apply, L.domIso_Φ_apply, B'.restrictIsoInv_snd h1,
      B.restrictIsoInv_snd h2]

/-! ### The maps of orientations -/

/-- **The map of orientations of a local strong bundle isomorphism, read in two domains**:
`Or_{ϕ(a)}^{f'|D'} ≃ Or_a^{f|D}` for `a ∈ U ∩ D` smooth with `ϕ(a) ∈ D'`. -/
def orDom (hf : B.IsScFredholmSectionTame f) (hf' : B'.IsScFredholmSectionTame f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (D : B.Dom) (D' : B'.Dom) {a : X} {x : X'} (ha : a ∈ U)
    (hϕ : L.ϕ a = x) (haD : a ∈ D.carrier) (hxD : x ∈ D'.carrier) (has : a ∈ PX.smoothSet)
    (hxs : x ∈ PX'.smoothSet) : D'.Or hf' x hxD hxs ≃ D.Or hf a haD has :=
  (L.domIso D D').orxViaAt (D.isFredholm hf).toIsScFredholmSection
    (D'.isFredholm hf').toIsScFredholmSection
    (L.sec_eqOn_domIso hf.isScSmooth.1 hf'.isScSmooth.1 hfL D D') D.hasSections D'.hasSections
    (a := ⟨a, haD⟩) (L.mem_domSet ha hϕ haD hxD) (StrongBundle.Dom.mem_smoothSet haD has)
    (L.domIso_ϕ_mk ha hϕ haD hxD)

/-- **The map of orientations does not depend on the domains**: the comparison maps of the
domains intertwine the maps read in `D₁`, `D₁'` and in `D₂`, `D₂'`. -/
theorem orDom_compare (hf : B.IsScFredholmSectionTame f) (hf' : B'.IsScFredholmSectionTame f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (D₁ D₂ : B.Dom) (D₁' D₂' : B'.Dom) {a : X} {x : X'}
    (ha : a ∈ U) (hϕ : L.ϕ a = x) (ha₁ : a ∈ D₁.carrier) (ha₂ : a ∈ D₂.carrier)
    (hx₁ : x ∈ D₁'.carrier) (hx₂ : x ∈ D₂'.carrier) (has : a ∈ PX.smoothSet)
    (hxs : x ∈ PX'.smoothSet) :
    (D₁'.compare D₂' hf' x hx₁ hx₂ hxs).trans (L.orDom hf hf' hfL D₁ D₁' ha hϕ ha₁ hx₁ has hxs) =
      (L.orDom hf hf' hfL D₂ D₂' ha hϕ ha₂ hx₂ has hxs).trans
        (D₁.compare D₂ hf a ha₁ ha₂ has) :=
  orxViaAt_square (L := D₁'.iso D₂') (L₂ := L.domIso D₁ D₁') (M := L.domIso D₂ D₂')
    (M₂ := D₁.iso D₂) (D₁.isFredholm hf).toIsScFredholmSection
    (D₁'.isFredholm hf').toIsScFredholmSection (D₂.isFredholm hf).toIsScFredholmSection
    (D₂'.isFredholm hf').toIsScFredholmSection (D₁'.sec_eqOn_iso D₂' hf'.isScSmooth.1)
    (L.sec_eqOn_domIso hf.isScSmooth.1 hf'.isScSmooth.1 hfL D₁ D₁')
    (L.sec_eqOn_domIso hf.isScSmooth.1 hf'.isScSmooth.1 hfL D₂ D₂')
    (D₁.sec_eqOn_iso D₂ hf.isScSmooth.1) D₁.hasSections D₁'.hasSections D₂.hasSections
    D₂'.hasSections (L.mem_domSet ha hϕ ha₁ hx₁) ha₂ (StrongBundle.Dom.mem_smoothSet ha₁ has)
    (L.domIso_ϕ_mk ha hϕ ha₁ hx₁) (D₁.iso_ϕ_mk D₂ ha₁ ha₂) hx₂
    (L.mem_domSet ha hϕ ha₂ hx₂) (D₁'.iso_ϕ_mk D₂' hx₁ hx₂) (L.domIso_ϕ_mk ha hϕ ha₂ hx₂)
    (L.germAgree₄_domIso_iso ha hϕ ha₁ ha₂ hx₁ hx₂)

/-- **The map `Or_{ϕ(a)}^{f'} ≃ Or_a^f` of a local strong bundle isomorphism** on the local
orientation sets, for `a ∈ U` smooth: the map read in the chosen domains at `a` and `ϕ(a)`. -/
def orLoc (hf : B.IsScFredholmSectionTame f) (hf' : B'.IsScFredholmSectionTame f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) {a : X} {x : X'} (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (has : a ∈ PX.smoothSet) (hxs : x ∈ PX'.smoothSet) : OrxLoc hf' x hxs ≃ OrxLoc hf a has :=
  L.orDom hf hf' hfL (B.domAt a) (B'.domAt x) ha hϕ (B.mem_domAt a) (B'.mem_domAt x) has hxs

/-- **The map of orientations read in two domains**: the identifications of the local
orientation sets with the orientation sets of the domains intertwine `orDom` and `orLoc`. -/
theorem orDom_toLoc (hf : B.IsScFredholmSectionTame f) (hf' : B'.IsScFredholmSectionTame f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (D : B.Dom) (D' : B'.Dom) {a : X} {x : X'} (ha : a ∈ U)
    (hϕ : L.ϕ a = x) (haD : a ∈ D.carrier) (hxD : x ∈ D'.carrier) (has : a ∈ PX.smoothSet)
    (hxs : x ∈ PX'.smoothSet) :
    (D'.toLoc hf' x hxD hxs).trans (L.orDom hf hf' hfL D D' ha hϕ haD hxD has hxs) =
      (L.orLoc hf hf' hfL ha hϕ has hxs).trans (D.toLoc hf a haD has) :=
  L.orDom_compare hf hf' hfL D (B.domAt a) D' (B'.domAt x) ha hϕ haD (B.mem_domAt a) hxD
    (B'.mem_domAt x) has hxs

end StrongBundle.LocalIso

end Two

/-! ### The identity -/

section Identity

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace StrongBundle.LocalIso

/-- **The map of orientations of the identity is the identity.** -/
theorem orLoc_refl (hf : B.IsScFredholmSectionTame f) {b : X} (hbs : b ∈ PX.smoothSet) :
    (LocalIso.refl B).orLoc hf hf (eqOn_refl f) (mem_univ b) rfl hbs hbs = Equiv.refl _ :=
  ((LocalIso.refl B).domIso (B.domAt b) (B.domAt b)).orxViaAt_of_germ_id
    ((B.domAt b).isFredholm hf).toIsScFredholmSection
    ((LocalIso.refl B).sec_eqOn_domIso hf.isScSmooth.1 hf.isScSmooth.1 (eqOn_refl f) _ _)
    (B.domAt b).hasSections (b := ⟨b, B.mem_domAt b⟩)
    ((LocalIso.refl B).mem_domSet (mem_univ b) rfl (B.mem_domAt b) (B.mem_domAt b))
    (StrongBundle.Dom.mem_smoothSet (B.mem_domAt b) hbs)
    ((LocalIso.refl B).domIso_ϕ_mk (mem_univ b) rfl (B.mem_domAt b) (B.mem_domAt b))
    ⟨univ, isOpen_univ, mem_univ _, fun w _ => ⟨mem_univ _, w.2⟩,
      fun w _ => (domIso_ϕ_of_mem (L := LocalIso.refl B) (D := B.domAt b) (D' := B.domAt b)
        (w := w) ⟨mem_univ _, w.2⟩).trans (Subtype.ext rfl),
      fun q _ => B.restrictIsoInv_snd_self q⟩

end StrongBundle.LocalIso

end Identity

/-! ### Squares of local isomorphisms -/

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

/-- **A square of local isomorphisms which commutes as germs at `b` commutes as germs when read
in domains** around `b`, `L₂(b)`, `M₂(b)` and `L(L₂(b))`. -/
theorem germAgree₄_domIso (hG : GermAgree₄ L L₂ M M₂ b) (D : B.Dom) (D₁ : B₁.Dom) (D₂ : B₂.Dom)
    (D' : B'.Dom) (hbD : b ∈ D.carrier) (hb : b ∈ U₂) (hb' : b ∈ V₂) (hx₁ : L₂.ϕ b = x₁)
    (hx₂ : M₂.ϕ b = x₂) (hU : x₁ ∈ U₁) (hV : x₂ ∈ V₁) (hx : L.ϕ x₁ = x)
    (h₁ : x₁ ∈ D₁.carrier) (h₂ : x₂ ∈ D₂.carrier) (h' : x ∈ D'.carrier) :
    GermAgree₄ (L.domIso D₁ D') (L₂.domIso D D₁) (M.domIso D₂ D') (M₂.domIso D D₂)
      (⟨b, hbD⟩ : D.carrier) := by
  subst hx₁ hx₂ hx
  obtain ⟨N, hNo, hbN, -, -, hϕ, hΦ⟩ := hG.exists_nhds
  have hO₁ : IsOpen (U₁ ∩ L.ϕ ⁻¹' D'.carrier) :=
    L.base.isScSmoothOn.continuousOn.isOpen_inter_preimage L.isOpen_U D'.isOpen
  have hA : IsOpen (U₂ ∩ L₂.ϕ ⁻¹' (D₁.carrier ∩ (U₁ ∩ L.ϕ ⁻¹' D'.carrier))) :=
    L₂.base.isScSmoothOn.continuousOn.isOpen_inter_preimage L₂.isOpen_U (D₁.isOpen.inter hO₁)
  have hB : IsOpen (V₂ ∩ M₂.ϕ ⁻¹' (D₂.carrier ∩ V₁)) :=
    M₂.base.isScSmoothOn.continuousOn.isOpen_inter_preimage M₂.isOpen_U
      (D₂.isOpen.inter M.isOpen_U)
  refine ⟨⟨Subtype.val ⁻¹' (N ∩ ((U₂ ∩ L₂.ϕ ⁻¹' (D₁.carrier ∩ (U₁ ∩ L.ϕ ⁻¹' D'.carrier))) ∩
      (V₂ ∩ M₂.ϕ ⁻¹' (D₂.carrier ∩ V₁)))),
    (hNo.inter (hA.inter hB)).preimage continuous_subtype_val,
    ⟨hbN, ⟨hb, h₁, hU, h'⟩, hb', h₂, hV⟩, fun w hw => ⟨hw.2.1.1, hw.2.1.2.1⟩,
    fun w hw => ⟨hw.2.2.1, hw.2.2.2.1⟩, fun w hw => ?_, fun q hq => ?_⟩⟩
  · have e := hϕ w.1 hw.1
    have m1 : w ∈ L₂.domSet D D₁ := ⟨hw.2.1.1, hw.2.1.2.1⟩
    have m2 : (⟨L₂.ϕ w.1, hw.2.1.2.1⟩ : D₁.carrier) ∈ L.domSet D₁ D' :=
      ⟨hw.2.1.2.2.1, hw.2.1.2.2.2⟩
    have m3 : w ∈ M₂.domSet D D₂ := ⟨hw.2.2.1, hw.2.2.2.1⟩
    have m4 : (⟨M₂.ϕ w.1, hw.2.2.2.1⟩ : D₂.carrier) ∈ M.domSet D₂ D' :=
      ⟨hw.2.2.2.2, by change M.ϕ (M₂.ϕ w.1) ∈ D'.carrier; rw [← e]; exact hw.2.1.2.2.2⟩
    rw [domIso_ϕ_of_mem m1, domIso_ϕ_of_mem m2, domIso_ϕ_of_mem m3, domIso_ϕ_of_mem m4]
    exact Subtype.ext e
  · have hPq : P q.1.2 = q.1.1.1 := StrongBundle.pullbackSpace_subtypeVal_proj q
    have k1 : P₁ (L₂.Φ q.1.2) ∈ D₁.carrier := by
      rw [L₂.covers _ (by rw [hPq]; exact hq.2.1.1), hPq]; exact hq.2.1.2.1
    have k2 : P₂ (M₂.Φ q.1.2) ∈ D₂.carrier := by
      rw [M₂.covers _ (by rw [hPq]; exact hq.2.2.1), hPq]; exact hq.2.2.2.1
    rw [domIso_Φ_apply, domIso_Φ_apply, domIso_Φ_apply, domIso_Φ_apply,
      B₁.restrictIsoInv_snd k1, B₂.restrictIsoInv_snd k2]
    exact congrArg _ (hΦ q.1.2 (by rw [hPq]; exact hq.1))

/-- **The maps of orientations of a square of local isomorphisms which commutes as germs
commute**: if `L ∘ L₂` and `M ∘ M₂` have the same germ at `b`, then
`Or^{f'} → Or^{f₁} → Or^f` and `Or^{f'} → Or^{f₂} → Or^f` agree at `b`. -/
theorem orLoc_square (hf : B.IsScFredholmSectionTame f) (hf₁ : B₁.IsScFredholmSectionTame f₁)
    (hf₂ : B₂.IsScFredholmSectionTame f₂) (hf' : B'.IsScFredholmSectionTame f')
    (hfL : EqOn f₁ (L.Ψ ∘ f' ∘ L.ϕ) U₁) (hfL₂ : EqOn f (L₂.Ψ ∘ f₁ ∘ L₂.ϕ) U₂)
    (hfM : EqOn f₂ (M.Ψ ∘ f' ∘ M.ϕ) V₁) (hfM₂ : EqOn f (M₂.Ψ ∘ f₂ ∘ M₂.ϕ) V₂) (hb : b ∈ U₂)
    (hb' : b ∈ V₂) (hx₁ : L₂.ϕ b = x₁) (hx₂ : M₂.ϕ b = x₂) (hU : x₁ ∈ U₁) (hV : x₂ ∈ V₁)
    (hx : L.ϕ x₁ = x) (hx' : M.ϕ x₂ = x) (hbs : b ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX₁.smoothSet)
    (hs₂ : x₂ ∈ PX₂.smoothSet) (hxs : x ∈ PX'.smoothSet) (hG : GermAgree₄ L L₂ M M₂ b) :
    (L.orLoc hf₁ hf' hfL hU hx hs₁ hxs).trans (L₂.orLoc hf hf₁ hfL₂ hb hx₁ hbs hs₁) =
      (M.orLoc hf₂ hf' hfM hV hx' hs₂ hxs).trans (M₂.orLoc hf hf₂ hfM₂ hb' hx₂ hbs hs₂) :=
  orxViaAt_square (L := L.domIso (B₁.domAt x₁) (B'.domAt x))
    (L₂ := L₂.domIso (B.domAt b) (B₁.domAt x₁)) (M := M.domIso (B₂.domAt x₂) (B'.domAt x))
    (M₂ := M₂.domIso (B.domAt b) (B₂.domAt x₂))
    ((B.domAt b).isFredholm hf).toIsScFredholmSection
    ((B₁.domAt x₁).isFredholm hf₁).toIsScFredholmSection
    ((B₂.domAt x₂).isFredholm hf₂).toIsScFredholmSection
    ((B'.domAt x).isFredholm hf').toIsScFredholmSection
    (L.sec_eqOn_domIso hf₁.isScSmooth.1 hf'.isScSmooth.1 hfL _ _)
    (L₂.sec_eqOn_domIso hf.isScSmooth.1 hf₁.isScSmooth.1 hfL₂ _ _)
    (M.sec_eqOn_domIso hf₂.isScSmooth.1 hf'.isScSmooth.1 hfM _ _)
    (M₂.sec_eqOn_domIso hf.isScSmooth.1 hf₂.isScSmooth.1 hfM₂ _ _)
    (B.domAt b).hasSections (B₁.domAt x₁).hasSections (B₂.domAt x₂).hasSections
    (B'.domAt x).hasSections (L₂.mem_domSet hb hx₁ (B.mem_domAt b) (B₁.mem_domAt x₁))
    (M₂.mem_domSet hb' hx₂ (B.mem_domAt b) (B₂.mem_domAt x₂))
    (StrongBundle.Dom.mem_smoothSet (B.mem_domAt b) hbs)
    (L₂.domIso_ϕ_mk hb hx₁ (B.mem_domAt b) (B₁.mem_domAt x₁))
    (M₂.domIso_ϕ_mk hb' hx₂ (B.mem_domAt b) (B₂.mem_domAt x₂))
    (L.mem_domSet hU hx (B₁.mem_domAt x₁) (B'.mem_domAt x))
    (M.mem_domSet hV hx' (B₂.mem_domAt x₂) (B'.mem_domAt x))
    (L.domIso_ϕ_mk hU hx (B₁.mem_domAt x₁) (B'.mem_domAt x))
    (M.domIso_ϕ_mk hV hx' (B₂.mem_domAt x₂) (B'.mem_domAt x))
    (germAgree₄_domIso hG _ _ _ _ (B.mem_domAt b) hb hb' hx₁ hx₂ hU hV hx (B₁.mem_domAt x₁)
      (B₂.mem_domAt x₂) (B'.mem_domAt x))

/-- **The maps of orientations of a commuting triangle compose**: if `L ∘ L₂` and `N` have the
same germ at `b`, then `Or^{f'} → Or^{f₁} → Or^f` is the map of `N` at `b`. -/
theorem orLoc_triangle (hf : B.IsScFredholmSectionTame f) (hf₁ : B₁.IsScFredholmSectionTame f₁)
    (hf' : B'.IsScFredholmSectionTame f') (hfL : EqOn f₁ (L.Ψ ∘ f' ∘ L.ϕ) U₁)
    (hfL₂ : EqOn f (L₂.Ψ ∘ f₁ ∘ L₂.ϕ) U₂) (hfN : EqOn f (N.Ψ ∘ f' ∘ N.ϕ) V) (hb : b ∈ U₂)
    (hb' : b ∈ V) (hx₁ : L₂.ϕ b = x₁) (hU : x₁ ∈ U₁) (hx : L.ϕ x₁ = x) (hx' : N.ϕ b = x)
    (hbs : b ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX₁.smoothSet) (hxs : x ∈ PX'.smoothSet)
    (hG : ∃ W : Set X, IsOpen W ∧ b ∈ W ∧ (∀ y ∈ W, L.ϕ (L₂.ϕ y) = N.ϕ y) ∧
      ∀ w, P w ∈ W → L.Φ (L₂.Φ w) = N.Φ w) :
    (L.orLoc hf₁ hf' hfL hU hx hs₁ hxs).trans (L₂.orLoc hf hf₁ hfL₂ hb hx₁ hbs hs₁) =
      N.orLoc hf hf' hfN hb' hx' hbs hxs := by
  obtain ⟨W, hWo, hbW, hϕ, hΦ⟩ := hG
  have hG₄ : GermAgree₄ L L₂ N (LocalIso.refl B) b :=
    ⟨⟨W ∩ (U₂ ∩ V), hWo.inter (L₂.isOpen_U.inter N.isOpen_U), ⟨hbW, hb, hb'⟩,
      fun _ hy => hy.2.1, fun _ _ => mem_univ _, fun y hy => hϕ y hy.1,
      fun w hw => hΦ w hw.1⟩⟩
  have h := orLoc_square hf hf₁ hf hf' hfL hfL₂ hfN (eqOn_refl f) hb (mem_univ b) hx₁ rfl hU
    hb' hx hx' hbs hs₁ hbs hxs hG₄
  exact h.trans ((congrArg (Equiv.trans _) (orLoc_refl hf hbs)).trans (Equiv.trans_refl _))

end StrongBundle.LocalIso

end Compose

/-! ### Germs, inverses -/

section Germ

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U U₃ : Set X} {U' U₃' : Set X'} (L : LocalIso B B' U U') {L₃ : LocalIso B B' U₃ U₃'}

variable {L} in
/-- **Local isomorphisms with the same germ at `a` induce the same map of orientations at
`a`.** -/
theorem orLoc_germ (hf : B.IsScFredholmSectionTame f) (hf' : B'.IsScFredholmSectionTame f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hfL₃ : EqOn f (L₃.Ψ ∘ f' ∘ L₃.ϕ) U₃) {a : X} {x : X'}
    (ha : a ∈ U) (ha₃ : a ∈ U₃) (hϕ : L.ϕ a = x) (hϕ₃ : L₃.ϕ a = x) (has : a ∈ PX.smoothSet)
    (hxs : x ∈ PX'.smoothSet) (hG : GermEq L L₃ a) :
    L.orLoc hf hf' hfL ha hϕ has hxs = L₃.orLoc hf hf' hfL₃ ha₃ hϕ₃ has hxs := by
  obtain ⟨W, hWo, haW, hW, hW₃, hWϕ, hWΦ⟩ := hG.exists_nhds
  have hG₄ : GermAgree₄ L (LocalIso.refl B) L₃ (LocalIso.refl B) a :=
    ⟨⟨W, hWo, haW, fun _ _ => mem_univ _, fun _ _ => mem_univ _, hWϕ, hWΦ⟩⟩
  have h := orLoc_square hf hf hf hf' hfL (eqOn_refl f) hfL₃ (eqOn_refl f) (mem_univ a)
    (mem_univ a) rfl rfl ha ha₃ hϕ hϕ₃ has has has hxs hG₄
  rw [orLoc_refl hf has] at h
  exact Equiv.ext fun o => DFunLike.congr_fun h o

/-- **The map of orientations of the inverse is the inverse.** -/
theorem orLoc_symm (hf : B.IsScFredholmSectionTame f) (hf' : B'.IsScFredholmSectionTame f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hfL' : EqOn f' (L.symm.Ψ ∘ f ∘ L.symm.ϕ) U') {a : X}
    {x : X'} (ha : a ∈ U) (hx : x ∈ U') (hϕ : L.ϕ a = x) (hg : L.symm.ϕ x = a)
    (has : a ∈ PX.smoothSet) (hxs : x ∈ PX'.smoothSet) :
    L.symm.orLoc hf' hf hfL' hx hg hxs has = (L.orLoc hf hf' hfL ha hϕ has hxs).symm := by
  have hG₄ : GermAgree₄ L.symm L (LocalIso.refl B) (LocalIso.refl B) a :=
    ⟨⟨U, L.isOpen_U, ha, subset_rfl, fun _ _ => mem_univ _,
      fun y hy => L.base.left_inv y hy, fun w hw => L.zero.left_inv w hw⟩⟩
  have h := orLoc_square hf hf' hf hf hfL' hfL (eqOn_refl f) (eqOn_refl f) ha (mem_univ a) hϕ
    rfl hx (mem_univ a) hg rfl has hxs has has hG₄
  refine Equiv.ext fun o => ?_
  have h' : L.orLoc hf hf' hfL ha hϕ has hxs (L.symm.orLoc hf' hf hfL' hx hg hxs has o) =
      (LocalIso.refl B).orLoc hf hf (eqOn_refl f) (mem_univ a) rfl has has
        ((LocalIso.refl B).orLoc hf hf (eqOn_refl f) (mem_univ a) rfl has has o) :=
    DFunLike.congr_fun h o
  have er : ∀ o' : OrxLoc hf a has,
      (LocalIso.refl B).orLoc hf hf (eqOn_refl f) (mem_univ a) rfl has has o' = o' :=
    fun o' => DFunLike.congr_fun (orLoc_refl hf has) o'
  exact (Equiv.eq_symm_apply _).2 (h'.trans ((congrArg _ (er o)).trans (er o)))

end StrongBundle.LocalIso

end Germ

section GermId

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **A local isomorphism with the germ of the identity at `b` induces the identity** on the
orientations at `b`. -/
theorem StrongBundle.LocalIso.orLoc_of_germ_id {U U' : Set X} (L : LocalIso B B U U')
    (hf : B.IsScFredholmSectionTame f) (hfL : EqOn f (L.Ψ ∘ f ∘ L.ϕ) U) {b : X} (hb : b ∈ U)
    (hϕ : L.ϕ b = b) (hbs : b ∈ PX.smoothSet)
    (hG : ∃ W : Set X, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ (∀ y ∈ W, L.ϕ y = y) ∧
      ∀ w, P w ∈ W → L.Φ w = w) :
    L.orLoc hf hf hfL hb hϕ hbs hbs = Equiv.refl _ := by
  obtain ⟨W, hWo, hbW, hWU, hWϕ, hWΦ⟩ := hG
  exact (orLoc_germ hf hf hfL (eqOn_refl f) hb (mem_univ b) hϕ rfl hbs hbs
    ⟨⟨W, hWo, hbW, hWU, fun _ _ => mem_univ _, hWϕ, hWΦ⟩⟩).trans (orLoc_refl hf hbs)

end GermId

end Polyfold
