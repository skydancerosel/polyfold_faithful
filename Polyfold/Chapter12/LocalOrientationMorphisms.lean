import Polyfold.Chapter12.LocalOrientationDomains
import Polyfold.Chapter12.OrientationMorphismContinuity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
Lemma 12.5.1 and the definition of `φ_*` on orientations (pp. 592–593).

# The action of morphisms on `Lin(f, x)` and on orientations, with local sc⁺-sections

## The text, paraphrased

`(P : W → X, μ)` is a strong bundle over an ep-groupoid and `f` an sc-Fredholm section functor.
For a smooth object `x` the set `Lin(f, x)` consists of the linearizations `(f − s)'(x)` for the
local sc⁺-sections `s` with `s(x) = f(x)`.  A morphism `φ : x → x'` between smooth objects acts by
`φ_* S = μ(φ, S ∘ (Tφ)⁻¹)`.  Lemma 12.5.1: (1) `φ_* S ∈ Lin(f, x')`; (2) `φ_*` is a bijection
`Lin(f, x) → Lin(f, x')`; (3) `(1_x)_* = Id` and `(ψ ∘ φ)_* = ψ_* ∘ φ_*`.  In the proof `φ` is
extended to a local sc-diffeomorphism covered by a local strong bundle isomorphism `Φ̂`, and a
local sc⁺-section `s₀` near `x` with `s₀(x) = f(x)` is carried to the local sc⁺-section
`s₁ = Φ̂_* s₀` near `x'`, with `μ(φ, (f − s₀)'(x) ∘ Tφ⁻¹) = (f − s₁)'(x')`.  The induced map of the
orientations of `DET(f, x)` and `DET(f, x')` is again denoted by `φ_*`.

## What is formalized

The sets `Lin(f, x)` and `Or_x^f` are those of `LocalOrientationDomains.lean`: they are made
with the sc⁺-sections over a *domain* (an open subset of the base domain of a chart), and
`OrxLoc` is read in the chosen domain `B.domAt x`.  No sc⁺-sections over all of the object space
and no sc-smooth bump functions are assumed.

* `morIsoDom σ D D'`: the local strong bundle isomorphism `P|D' → P|D` of a morphism `σ` for
  domains `D` (at the source) and `D'` (at the target): `E.morIso σ` read through the inclusions
  of the domains; `sec_eqOn_morIsoDom`: `f|D' = Ψ ∘ f|D ∘ ϕ` for a section functor `f`.
* Germs: `morIsoDom_comp_germ` (composition of morphisms), `germAgree₄_morIsoDom` (change of the
  domains), `germEq_morIsoDom_sheet` (two morphisms of one sheet).
* `Dom.linPt`, `linPtLoc`: the chart points in which `Lin(f|D, x)` and `Lin(f, x)` are read.
* `morTDom`, `morKDom`, `orMorDom`: the maps `Tσ`, `μ(σ, ·)` and `σ_*` on orientations read in
  two domains, with composition, units, inverses, and the compatibility of `orMorDom` with the
  comparison maps of domains (`orMorDom_compare`, `orMorDom_toLoc`).
* `morTLoc`, `morKLoc`, `linMorLoc`: `Tφ`, `μ(φ, ·)` and `φ_*` in the chosen domains;
  `lemma_12_5_1_one_loc`, `lemma_12_5_1_two_loc`, `lemma_12_5_1_three_unit_loc`,
  `lemma_12_5_1_three_comp_loc`: **Lemma 12.5.1 (1)–(3)**.
* `orMorLoc`: **`φ_* : Or_x^f → Or_{x'}^f`** on the local orientation sets, with `orMorLoc_apply`
  (it is the conjugation by `Tφ` and `μ(φ, ·)`), `orMorLoc_comp`, `orMorLoc_unit`,
  `orMorLoc_inv`, `orMorLoc_congr`.
* `orMorLoc_eq_orxViaAt_sheet`: for a morphism `τ : y → y'` in the sheet of `σ : x → x'` with
  `y`, `y'` in the chosen domains at `x`, `x'`, the map `τ_*` is the orientation map at `y'` of
  the local isomorphism of `σ`, read through the comparison maps of the domains.
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

/-- **The chart point in which `Lin(f|D, x)` and `Or_x^{f|D}` are read**, for a smooth point `x`
of a domain `D`: the chosen chart point of the restriction `P|D` at `x`. -/
abbrev StrongBundle.Dom.linPt (D : B.Dom) {x : Obj} (hxD : x ∈ D.carrier)
    (hs : x ∈ X.PObj.smoothSet) : ChartPoint D.bundle ⟨x, hxD⟩ :=
  orxPt D.bundle ⟨x, hxD⟩ (StrongBundle.Dom.mem_smoothSet hxD hs)

variable (B) in
/-- **The chart point in which `Lin(f, x)` and the local orientation set `Or_x^f` are read**: the
chosen chart point at `x` of the restriction of the bundle to the chosen domain at `x`. -/
abbrev linPtLoc (x : Obj) (hs : x ∈ X.PObj.smoothSet) :
    ChartPoint (B.domAt x).bundle ⟨x, B.mem_domAt x⟩ :=
  (B.domAt x).linPt (B.mem_domAt x) hs

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}

/-! ### The local isomorphism of a morphism between two domains -/

/-- The part of the domain `D'` on which the isomorphism of `σ` is defined with values in the
domain `D`. -/
def morIsoDomSet (σ : Mor) (D D' : B.Dom) : Set D'.carrier :=
  {w | w.1 ∈ (X.sheetAt σ).tgtSet ∧ (E.morIso σ).ϕ w.1 ∈ D.carrier}

/-- The image of `morIsoDomSet` in the domain `D`. -/
def morIsoDomTarget (σ : Mor) (D D' : B.Dom) : Set D.carrier :=
  {v | v.1 ∈ (X.sheetAt σ).srcSet ∧ (E.morIso σ).g v.1 ∈ D'.carrier}

/-- **The local strong bundle isomorphism of a morphism `σ` between two domains**: for a domain
`D` (at the source of `σ`) and a domain `D'` (at the target), the isomorphism `E.morIso σ` read
as a local strong bundle isomorphism `P|D' → P|D`, the composite of the inclusion `P|D' → P`,
of `E.morIso σ` and of the inverse of the inclusion `P|D → P`. -/
def morIsoDom (σ : Mor) (D D' : B.Dom) :
    StrongBundle.LocalIso D'.bundle D.bundle (E.morIsoDomSet σ D D')
      (E.morIsoDomTarget σ D D') :=
  (((B.restrictIso D'.isOpen).trans (E.morIso σ)).trans (B.restrictIso D.isOpen).symm).ofEq
    (Set.ext fun _ => ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨mem_univ _, h.1⟩, h.2⟩⟩)
    (Set.ext fun _ => ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩)

theorem morIsoDom_ϕ_of_mem {σ : Mor} {D D' : B.Dom} {w : D'.carrier}
    (hw : w ∈ E.morIsoDomSet σ D D') :
    (E.morIsoDom σ D D').ϕ w = ⟨(E.morIso σ).ϕ w.1, hw.2⟩ :=
  MPolyfold.openRetraction_of_mem hw.2

theorem morIsoDom_Φ_apply (σ : Mor) (D D' : B.Dom)
    (q : pullbackSpace P (Subtype.val : D'.carrier → Obj)) :
    (E.morIsoDom σ D D').Φ q = B.restrictIsoInv D.carrier ((E.morIso σ).Φ q.1.2) := rfl

theorem morIsoDom_Ψ_apply (σ : Mor) (D D' : B.Dom)
    (q : pullbackSpace P (Subtype.val : D.carrier → Obj)) :
    (E.morIsoDom σ D D').Ψ q = B.restrictIsoInv D'.carrier ((E.morIso σ).Ψ q.1.2) := rfl

/-- The target of a morphism `σ : x → x'` with `x ∈ D`, `x' ∈ D'` lies in the domain of
`morIsoDom σ D D'`. -/
theorem mem_morIsoDomSet (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    {D D' : B.Dom} (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) :
    (⟨x', hxD'⟩ : D'.carrier) ∈ E.morIsoDomSet σ D D' :=
  ⟨mem_tgtSet hx', by
    change (E.morIso σ).ϕ x' ∈ D.carrier
    rw [E.morIso_ϕ_eq hx hx']; exact hxD⟩

/-- The base map of `morIsoDom σ D D'` sends the target of `σ` to its source. -/
theorem morIsoDom_ϕ_mk (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    {D D' : B.Dom} (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) :
    (E.morIsoDom σ D D').ϕ ⟨x', hxD'⟩ = ⟨x, hxD⟩ :=
  (E.morIsoDom_ϕ_of_mem (E.mem_morIsoDomSet σ hx hx' hxD hxD')).trans
    (Subtype.ext (E.morIso_ϕ_eq hx hx'))

/-- **The restrictions of a section functor to two domains correspond under the isomorphism of
a morphism**: `f|D' = Ψ ∘ f|D ∘ ϕ` on the domain of `morIsoDom σ D D'`. -/
theorem sec_eqOn_morIsoDom (hF : E.IsScFredholmSectionFunctor f) (hfs : IsSection P f) (σ : Mor)
    (D D' : B.Dom) :
    EqOn (D'.sec f hfs) ((E.morIsoDom σ D D').Ψ ∘ D.sec f hfs ∘ (E.morIsoDom σ D D').ϕ)
      (E.morIsoDomSet σ D D') := by
  intro w hw
  have h1 : f w.1 = (E.morIso σ).Ψ (f ((E.morIso σ).ϕ w.1)) :=
    E.eqOn_morIso_of_functor hF σ hw.1
  have h2 := B.restrictSection_eqOn_restrictIso D'.isOpen hfs (mem_univ w)
  change D'.sec f hfs w = B.restrictIsoInv D'.carrier
    ((E.morIso σ).Ψ ((D.sec f hfs ((E.morIsoDom σ D D').ϕ w)).1.2))
  rw [E.morIsoDom_ϕ_of_mem hw]
  change D'.sec f hfs w = B.restrictIsoInv D'.carrier
    ((E.morIso σ).Ψ (f ((E.morIso σ).ϕ w.1)))
  rw [← h1]
  exact h2

/-! ### Germs of the local isomorphisms -/

/-- **The isomorphism of a composite is the composite of the isomorphisms**, near the target of
`ψ`: for `φ : x → y`, `ψ : y → z` and domains `D ∋ x`, `D' ∋ y`, `D'' ∋ z`, the composite of
`morIsoDom ψ D' D''` and `morIsoDom φ D D'` is `morIsoDom (ψ ∘ φ) D D''` near `z`. -/
theorem morIsoDom_comp_germ {φ ψ : Mor} {x y z : Obj} (hφx : X.src φ = x) (hφy : X.tgt φ = y)
    (hψy : X.src ψ = y) (hψz : X.tgt ψ = z) {D D' D'' : B.Dom} (hxD : x ∈ D.carrier)
    (hyD : y ∈ D'.carrier) (hzD : z ∈ D''.carrier) :
    ∃ N : Set D''.carrier, IsOpen N ∧ (⟨z, hzD⟩ : D''.carrier) ∈ N ∧
      (∀ w ∈ N, (E.morIsoDom φ D D').ϕ ((E.morIsoDom ψ D' D'').ϕ w) =
        (E.morIsoDom (X.comp ψ φ) D D'').ϕ w) ∧
      ∀ q, pullbackProj P (Subtype.val : D''.carrier → Obj) q ∈ N →
        (E.morIsoDom φ D D').Φ ((E.morIsoDom ψ D' D'').Φ q) =
          (E.morIsoDom (X.comp ψ φ) D D'').Φ q := by
  have hG : StrongBundle.LocalIso.GermAgree (E.morIso φ) (E.morIso ψ)
      (E.morIso (X.comp ψ φ)) z := hψz ▸ E.germAgree_morIso_comp (hψy.trans hφy.symm)
  obtain ⟨N, hNo, hzN, -, -, hϕ, hΦ⟩ := hG.exists_nhds
  have hO := (E.morIsoDom ψ D' D'').base.isScSmoothOn.continuousOn.isOpen_inter_preimage
    (E.morIsoDom ψ D' D'').isOpen_U (E.morIsoDom φ D D').isOpen_U
  refine ⟨(Subtype.val ⁻¹' N ∩ E.morIsoDomSet (X.comp ψ φ) D D'') ∩
      (E.morIsoDomSet ψ D' D'' ∩ (E.morIsoDom ψ D' D'').ϕ ⁻¹' E.morIsoDomSet φ D D'),
    ((hNo.preimage continuous_subtype_val).inter (E.morIsoDom _ D D'').isOpen_U).inter hO,
    ⟨⟨hzN, E.mem_morIsoDomSet _ (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hxD hzD⟩,
      E.mem_morIsoDomSet ψ hψy hψz hyD hzD, ?_⟩, fun w hw => ?_, fun q hq => ?_⟩
  · rw [mem_preimage, E.morIsoDom_ϕ_mk ψ hψy hψz hyD hzD]
    exact E.mem_morIsoDomSet φ hφx hφy hxD hyD
  · have h1 := E.morIsoDom_ϕ_of_mem hw.2.1
    have h2 : (⟨(E.morIso ψ).ϕ w.1, hw.2.1.2⟩ : D'.carrier) ∈ E.morIsoDomSet φ D D' :=
      h1 ▸ hw.2.2
    rw [h1, E.morIsoDom_ϕ_of_mem h2, E.morIsoDom_ϕ_of_mem hw.1.2]
    exact Subtype.ext (hϕ w.1 hw.1.1)
  · have hPq : P q.1.2 = q.1.1.1 := StrongBundle.pullbackSpace_subtypeVal_proj q
    have hψq : P ((E.morIso ψ).Φ q.1.2) ∈ D'.carrier := by
      rw [(E.morIso ψ).covers _ (by rw [hPq]; exact hq.2.1.1), hPq]; exact hq.2.1.2
    rw [E.morIsoDom_Φ_apply, E.morIsoDom_Φ_apply, E.morIsoDom_Φ_apply,
      B.restrictIsoInv_snd hψq]
    exact congrArg _ (hΦ q.1.2 (by rw [hPq]; exact hq.1.1))

/-- **Change of the domains**: for a morphism `σ : x → x'`, domains `D₁, D₂ ∋ x` and
`D₁', D₂' ∋ x'`, the isomorphism of `σ` read in `D₁`, `D₁'` followed by the identification of
`D₁` with `D₂` is, near `x'`, the identification of `D₁'` with `D₂'` followed by the isomorphism
of `σ` read in `D₂`, `D₂'`. -/
theorem germAgree₄_morIsoDom (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    {D₁ D₂ D₁' D₂' : B.Dom} (hx₁ : x ∈ D₁.carrier) (hx₂ : x ∈ D₂.carrier)
    (hx₁' : x' ∈ D₁'.carrier) (hx₂' : x' ∈ D₂'.carrier) :
    StrongBundle.LocalIso.GermAgree₄ (D₁.iso D₂) (E.morIsoDom σ D₁ D₁')
      (E.morIsoDom σ D₂ D₂') (D₁'.iso D₂') (⟨x', hx₁'⟩ : D₁'.carrier) := by
  have hO := (E.morIsoDom σ D₁ D₁').base.isScSmoothOn.continuousOn.isOpen_inter_preimage
    (E.morIsoDom σ D₁ D₁').isOpen_U (D₁.iso D₂).isOpen_U
  refine ⟨⟨{w : D₁'.carrier | w.1 ∈ D₂'.carrier} ∩ (E.morIsoDomSet σ D₁ D₁' ∩
      (E.morIsoDom σ D₁ D₁').ϕ ⁻¹' {v : D₁.carrier | v.1 ∈ D₂.carrier}),
    (D₂'.isOpen.preimage continuous_subtype_val).inter hO,
    ⟨hx₂', E.mem_morIsoDomSet σ hx hx' hx₁ hx₁', ?_⟩, fun w hw => hw.2.1, fun w hw => hw.1,
    fun w hw => ?_, fun q hq => ?_⟩⟩
  · rw [mem_preimage, E.morIsoDom_ϕ_mk σ hx hx' hx₁ hx₁']; exact hx₂
  · have h1 := E.morIsoDom_ϕ_of_mem hw.2.1
    have h2 : (E.morIso σ).ϕ w.1 ∈ D₂.carrier := by
      have := hw.2.2; rw [mem_preimage, h1] at this; exact this
    have h3 : (⟨w.1, hw.1⟩ : D₂'.carrier) ∈ E.morIsoDomSet σ D₂ D₂' := ⟨hw.2.1.1, h2⟩
    rw [h1, D₁.iso_ϕ_of_mem D₂ h2, D₁'.iso_ϕ_of_mem D₂' hw.1, E.morIsoDom_ϕ_of_mem h3]
  · have hPq : P q.1.2 = q.1.1.1 := StrongBundle.pullbackSpace_subtypeVal_proj q
    have h1 : P ((E.morIso σ).Φ q.1.2) ∈ D₁.carrier := by
      rw [(E.morIso σ).covers _ (by rw [hPq]; exact hq.2.1.1), hPq]; exact hq.2.1.2
    have h2 : P q.1.2 ∈ D₂'.carrier := by rw [hPq]; exact hq.1
    change B.restrictIsoInv D₂.carrier ((E.morIsoDom σ D₁ D₁').Φ q).1.2 =
      (E.morIsoDom σ D₂ D₂').Φ (B.restrictIsoInv D₂'.carrier q.1.2)
    rw [E.morIsoDom_Φ_apply, E.morIsoDom_Φ_apply, B.restrictIsoInv_snd h1,
      B.restrictIsoInv_snd h2]

/-- **Two morphisms of one sheet**: for a morphism `τ : y → y'` in the sheet of `σ` and domains
`D ∋ y`, `D' ∋ y'`, the isomorphisms of `σ` and of `τ` read in `D`, `D'` have the same germ at
`y'`. -/
theorem germEq_morIsoDom_sheet (σ : Mor) {τ : Mor} (hτ : τ ∈ (X.sheetAt σ).carrier)
    {y y' : Obj} (hy : X.src τ = y) (hy' : X.tgt τ = y') {D D' : B.Dom} (hyD : y ∈ D.carrier)
    (hyD' : y' ∈ D'.carrier) :
    StrongBundle.LocalIso.GermEq (E.morIsoDom σ D D') (E.morIsoDom τ D D')
      (⟨y', hyD'⟩ : D'.carrier) := by
  have hmem : y' ∈ (X.sheetAt σ).tgtSet := hy' ▸ (X.sheetAt σ).isScDiffeoOn_tgt.mapsTo hτ
  have hτe : (X.sheetAt σ).tgtInv y' = τ :=
    hy' ▸ (X.sheetAt σ).isScDiffeoOn_tgt.left_inv τ hτ
  have hG : StrongBundle.LocalIso.GermEq (E.morIso σ) (E.morIso τ) y' :=
    hτe ▸ E.germEq_morIso_sheet σ hmem
  obtain ⟨N, hNo, hyN, -, -, hϕ, hΦ⟩ := hG.exists_nhds
  have hσy : (E.morIso σ).ϕ y' = y := (hϕ y' hyN).trans (E.morIso_ϕ_eq hy hy')
  refine ⟨⟨(Subtype.val ⁻¹' N ∩ E.morIsoDomSet σ D D') ∩ E.morIsoDomSet τ D D',
    ((hNo.preimage continuous_subtype_val).inter (E.morIsoDom σ D D').isOpen_U).inter
      (E.morIsoDom τ D D').isOpen_U,
    ⟨⟨hyN, hmem, ?_⟩, E.mem_morIsoDomSet τ hy hy' hyD hyD'⟩, fun w hw => hw.1.2,
    fun w hw => hw.2, fun w hw => ?_, fun q hq => ?_⟩⟩
  · change (E.morIso σ).ϕ y' ∈ D.carrier
    rw [hσy]; exact hyD
  · rw [E.morIsoDom_ϕ_of_mem hw.1.2, E.morIsoDom_ϕ_of_mem hw.2]
    exact Subtype.ext (hϕ w.1 hw.1.1)
  · rw [E.morIsoDom_Φ_apply, E.morIsoDom_Φ_apply]
    exact congrArg _ (hΦ q.1.2 (by
      rw [StrongBundle.pullbackSpace_subtypeVal_proj q]; exact hq.1.1))

/-! ### `Tσ` and `μ(σ, ·)` read in two domains -/

/-- **`Tσ : T_xX → T_{x'}X`** for a morphism `σ : x → x'` between smooth objects, read in the
chosen chart points of the restrictions of the bundle to domains `D ∋ x` and `D' ∋ x'`. -/
def morTDom (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x') (D D' : B.Dom)
    (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) :
    ↥(D.linPt hxD hs).T ≃L[ℝ] ↥(D'.linPt hxD' hs').T :=
  (E.morIsoDom σ D D').orxTAt (E.mem_morIsoDomSet σ hx hx' hxD hxD')
    (StrongBundle.Dom.mem_smoothSet hxD' hs') (E.morIsoDom_ϕ_mk σ hx hx' hxD hxD')

/-- **`μ(σ, ·) : W_x → W_{x'}`** for a morphism `σ : x → x'` between smooth objects, read in the
chosen chart points of the restrictions of the bundle to domains `D ∋ x` and `D' ∋ x'`. -/
def morKDom (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x') (D D' : B.Dom)
    (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) :
    ↥(D.linPt hxD hs).K ≃L[ℝ] ↥(D'.linPt hxD' hs').K :=
  (E.morIsoDom σ D D').orxKAt (E.mem_morIsoDomSet σ hx hx' hxD hxD')
    (StrongBundle.Dom.mem_smoothSet hxD' hs') (E.morIsoDom_ϕ_mk σ hx hx' hxD hxD')

theorem morTDom_congr {σ σ' : Mor} (h : σ = σ') {x x' : Obj} (hx : X.src σ = x)
    (hx' : X.tgt σ = x') (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier)
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (v) :
    E.morTDom σ hx hx' D D' hxD hxD' hs hs' v =
      E.morTDom σ' (h ▸ hx) (h ▸ hx') D D' hxD hxD' hs hs' v := by
  subst h; rfl

theorem morKDom_congr {σ σ' : Mor} (h : σ = σ') {x x' : Obj} (hx : X.src σ = x)
    (hx' : X.tgt σ = x') (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier)
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (k) :
    E.morKDom σ hx hx' D D' hxD hxD' hs hs' k =
      E.morKDom σ' (h ▸ hx) (h ▸ hx') D D' hxD hxD' hs hs' k := by
  subst h; rfl

section Comp

variable {φ ψ : Mor} {x y z : Obj} (hφx : X.src φ = x) (hφy : X.tgt φ = y) (hψy : X.src ψ = y)
  (hψz : X.tgt ψ = z) (D D' D'' : B.Dom) (hxD : x ∈ D.carrier) (hyD : y ∈ D'.carrier)
  (hzD : z ∈ D''.carrier)

/-- **`T(ψ ∘ φ) = Tψ ∘ Tφ`** read in three domains. -/
theorem morTDom_comp (hs : x ∈ X.PObj.smoothSet) (hs' : y ∈ X.PObj.smoothSet)
    (hs'' : z ∈ X.PObj.smoothSet)
    (v : ↥(D.linPt hxD hs).T) :
    E.morTDom ψ hψy hψz D' D'' hyD hzD hs' hs'' (E.morTDom φ hφx hφy D D' hxD hyD hs hs' v) =
      E.morTDom (X.comp ψ φ) (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) D D'' hxD hzD
        hs hs'' v :=
  StrongBundle.LocalIso.orxTAt_triangle (L := E.morIsoDom φ D D') (L₂ := E.morIsoDom ψ D' D'')
    (N := E.morIsoDom (X.comp ψ φ) D D'') (E.mem_morIsoDomSet ψ hψy hψz hyD hzD)
    (E.mem_morIsoDomSet _ (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hxD hzD)
    (StrongBundle.Dom.mem_smoothSet hzD hs'') (E.morIsoDom_ϕ_mk ψ hψy hψz hyD hzD)
    (E.mem_morIsoDomSet φ hφx hφy hxD hyD) (E.morIsoDom_ϕ_mk φ hφx hφy hxD hyD)
    (E.morIsoDom_ϕ_mk _ (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hxD hzD)
    (E.morIsoDom_comp_germ hφx hφy hψy hψz hxD hyD hzD) v

/-- **`μ(ψ ∘ φ, ·) = μ(ψ, ·) ∘ μ(φ, ·)`** read in three domains. -/
theorem morKDom_comp (hs : x ∈ X.PObj.smoothSet) (hs' : y ∈ X.PObj.smoothSet)
    (hs'' : z ∈ X.PObj.smoothSet)
    (k : ↥(D.linPt hxD hs).K) :
    E.morKDom ψ hψy hψz D' D'' hyD hzD hs' hs'' (E.morKDom φ hφx hφy D D' hxD hyD hs hs' k) =
      E.morKDom (X.comp ψ φ) (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) D D'' hxD hzD
        hs hs'' k :=
  StrongBundle.LocalIso.orxKAt_triangle (L := E.morIsoDom φ D D') (L₂ := E.morIsoDom ψ D' D'')
    (N := E.morIsoDom (X.comp ψ φ) D D'') (E.mem_morIsoDomSet ψ hψy hψz hyD hzD)
    (E.mem_morIsoDomSet _ (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hxD hzD)
    (StrongBundle.Dom.mem_smoothSet hzD hs'') (E.morIsoDom_ϕ_mk ψ hψy hψz hyD hzD)
    (E.mem_morIsoDomSet φ hφx hφy hxD hyD) (E.morIsoDom_ϕ_mk φ hφx hφy hxD hyD)
    (E.morIsoDom_ϕ_mk _ (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hxD hzD)
    (E.morIsoDom_comp_germ hφx hφy hψy hψz hxD hyD hzD) k

end Comp

/-- **`T(1_x) = Id`** read in a domain. -/
theorem morTDom_unit {σ : Mor} {x : Obj} (h : σ = X.unit x) (hx : X.src σ = x)
    (hx' : X.tgt σ = x) (D : B.Dom) (hxD : x ∈ D.carrier) (hs : x ∈ X.PObj.smoothSet)
    (v : ↥(D.linPt hxD hs).T) :
    E.morTDom σ hx hx' D D hxD hxD hs hs v = v := by
  subst h
  have key := E.morTDom_comp hx hx' hx hx' D D D hxD hxD hxD hs hs hs v
  rw [E.morTDom_congr (comp_unit_unit x)] at key
  exact (E.morTDom (X.unit x) hx hx' D D hxD hxD hs hs).injective key

/-- **`μ(1_x, ·) = Id`** read in a domain. -/
theorem morKDom_unit {σ : Mor} {x : Obj} (h : σ = X.unit x) (hx : X.src σ = x)
    (hx' : X.tgt σ = x) (D : B.Dom) (hxD : x ∈ D.carrier) (hs : x ∈ X.PObj.smoothSet)
    (k : ↥(D.linPt hxD hs).K) :
    E.morKDom σ hx hx' D D hxD hxD hs hs k = k := by
  subst h
  have key := E.morKDom_comp hx hx' hx hx' D D D hxD hxD hxD hs hs hs k
  rw [E.morKDom_congr (comp_unit_unit x)] at key
  exact (E.morKDom (X.unit x) hx hx' D D hxD hxD hs hs).injective key

/-- **`T(φ⁻¹) ∘ Tφ = Id`** read in two domains. -/
theorem morTDom_inv {φ : Mor} {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet)
    (v : ↥(D.linPt hxD hs).T) :
    E.morTDom (X.inv φ) ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) D' D hxD' hxD hs' hs
      (E.morTDom φ hx hx' D D' hxD hxD' hs hs' v) = v :=
  (E.morTDom_comp hx hx' ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) D D' D hxD hxD' hxD
    hs hs' hs v).trans
    (E.morTDom_unit ((X.inv_comp φ).trans (congrArg X.unit hx)) _ _ D hxD hs v)

/-- **`μ(φ⁻¹, ·) ∘ μ(φ, ·) = Id`** read in two domains. -/
theorem morKDom_inv {φ : Mor} {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet)
    (k : ↥(D.linPt hxD hs).K) :
    E.morKDom (X.inv φ) ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) D' D hxD' hxD hs' hs
      (E.morKDom φ hx hx' D D' hxD hxD' hs hs' k) = k :=
  (E.morKDom_comp hx hx' ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) D D' D hxD hxD' hxD
    hs hs' hs k).trans
    (E.morKDom_unit ((X.inv_comp φ).trans (congrArg X.unit hx)) _ _ D hxD hs k)

theorem morTDom_inv_eq_symm {φ : Mor} {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet)
    (v : ↥(D'.linPt hxD' hs').T) :
    E.morTDom (X.inv φ) ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) D' D hxD' hxD hs' hs
      v = (E.morTDom φ hx hx' D D' hxD hxD' hs hs').symm v := by
  conv_lhs => rw [← (E.morTDom φ hx hx' D D' hxD hxD' hs hs').apply_symm_apply v]
  exact E.morTDom_inv hx hx' D D' hxD hxD' hs hs' _

theorem morKDom_inv_eq_symm {φ : Mor} {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet)
    (k : ↥(D'.linPt hxD' hs').K) :
    E.morKDom (X.inv φ) ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) D' D hxD' hxD hs' hs
      k = (E.morKDom φ hx hx' D D' hxD hxD' hs hs').symm k := by
  conv_lhs => rw [← (E.morKDom φ hx hx' D D' hxD hxD' hs hs').apply_symm_apply k]
  exact E.morKDom_inv hx hx' D D' hxD hxD' hs hs' _

/-! ### The action on `Lin(f|D, x)` and on orientations, read in two domains -/

section Action

variable (hF : E.IsScFredholmSectionFunctor f) (hfT : B.IsScFredholmSectionTame f)

include hF hfT in
/-- The conjugate `μ(σ, ·)⁻¹ ∘ S' ∘ Tσ` of a member of `Lin(f|D', x')` is a member of
`Lin(f|D, x)`. -/
theorem morTDom_mem (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) :
    ∀ S' ∈ (D'.linPt hxD' hs').linSet (D'.sec f hfT.isScSmooth.1),
      ((E.morKDom σ hx hx' D D' hxD hxD' hs hs').symm.toContinuousLinearMap ∘L S' ∘L
        (E.morTDom σ hx hx' D D' hxD hxD' hs hs').toContinuousLinearMap) ∈
          (D.linPt hxD hs).linSet (D.sec f hfT.isScSmooth.1) :=
  (E.morIsoDom σ D D').orxTAt_mem (D'.isFredholm hfT).toIsScFredholmSection
    (D.isFredholm hfT).toIsScFredholmSection (E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 σ D D')
    D'.hasSections D.hasSections (E.mem_morIsoDomSet σ hx hx' hxD hxD')
    (StrongBundle.Dom.mem_smoothSet hxD' hs') (E.morIsoDom_ϕ_mk σ hx hx' hxD hxD')

/-- **`σ_* S = μ(σ, ·) ∘ S ∘ (Tσ)⁻¹`**, read in two domains `D ∋ x`, `D' ∋ x'`. -/
def linMorDom (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x') (D D' : B.Dom)
    (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) (S : ↥(D.linPt hxD hs).T →L[ℝ] ↥(D.linPt hxD hs).K) :
    ↥(D'.linPt hxD' hs').T →L[ℝ] ↥(D'.linPt hxD' hs').K :=
  (E.morKDom σ hx hx' D D' hxD hxD' hs hs').toContinuousLinearMap ∘L S ∘L
    (E.morTDom σ hx hx' D D' hxD hxD' hs hs').symm.toContinuousLinearMap

theorem linMorDom_apply (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) (S : ↥(D.linPt hxD hs).T →L[ℝ] ↥(D.linPt hxD hs).K)
    (v : ↥(D'.linPt hxD' hs').T) :
    E.linMorDom σ hx hx' D D' hxD hxD' hs hs' S v =
      E.morKDom σ hx hx' D D' hxD hxD' hs hs'
        (S ((E.morTDom σ hx hx' D D' hxD hxD' hs hs').symm v)) := rfl

include hF hfT in
/-- **`σ_*` maps `Lin(f|D, x)` into `Lin(f|D', x')`.** -/
theorem linMorDom_mem (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) {S : ↥(D.linPt hxD hs).T →L[ℝ] ↥(D.linPt hxD hs).K}
    (hS : S ∈ (D.linPt hxD hs).linSet (D.sec f hfT.isScSmooth.1)) :
    E.linMorDom σ hx hx' D D' hxD hxD' hs hs' S ∈
      (D'.linPt hxD' hs').linSet (D'.sec f hfT.isScSmooth.1) := by
  have h := E.morTDom_mem hF hfT (X.inv σ) ((X.src_inv σ).trans hx') ((X.tgt_inv σ).trans hx)
    D' D hxD' hxD hs' hs S hS
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  change E.morKDom σ hx hx' D D' hxD hxD' hs hs'
      (S ((E.morTDom σ hx hx' D D' hxD hxD' hs hs').symm v)) =
    (E.morKDom (X.inv σ) ((X.src_inv σ).trans hx') ((X.tgt_inv σ).trans hx) D' D hxD' hxD
      hs' hs).symm (S (E.morTDom (X.inv σ) ((X.src_inv σ).trans hx') ((X.tgt_inv σ).trans hx)
        D' D hxD' hxD hs' hs v))
  rw [E.morTDom_inv_eq_symm hx hx' D D' hxD hxD' hs hs', ContinuousLinearEquiv.eq_symm_apply,
    E.morKDom_inv_eq_symm hx hx' D D' hxD hxD' hs hs', ContinuousLinearEquiv.symm_apply_apply]

/-- `σ_*` is injective (it is the conjugation by two isomorphisms). -/
theorem linMorDom_injective (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) :
    Function.Injective (E.linMorDom σ hx hx' D D' hxD hxD' hs hs') := fun S₁ S₂ h =>
  ContinuousLinearMap.ext fun v => by
    have h1 := DFunLike.congr_fun h (E.morTDom σ hx hx' D D' hxD hxD' hs hs' v)
    rw [linMorDom_apply, linMorDom_apply, ContinuousLinearEquiv.symm_apply_apply] at h1
    exact (E.morKDom σ hx hx' D D' hxD hxD' hs hs').injective h1

include hF hfT in
/-- **`σ_* : Lin(f|D, x) → Lin(f|D', x')` is a bijection.** -/
theorem bijOn_linMorDom (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) :
    Set.BijOn (E.linMorDom σ hx hx' D D' hxD hxD' hs hs')
      ((D.linPt hxD hs).linSet (D.sec f hfT.isScSmooth.1))
      ((D'.linPt hxD' hs').linSet (D'.sec f hfT.isScSmooth.1)) := by
  refine ⟨fun S hS => E.linMorDom_mem hF hfT σ hx hx' D D' hxD hxD' hs hs' hS,
    (E.linMorDom_injective σ hx hx' D D' hxD hxD' hs hs').injOn, fun S' hS' => ?_⟩
  refine ⟨_, E.morTDom_mem hF hfT σ hx hx' D D' hxD hxD' hs hs' S' hS',
    ContinuousLinearMap.ext fun v => ?_⟩
  change E.morKDom σ hx hx' D D' hxD hxD' hs hs'
    ((E.morKDom σ hx hx' D D' hxD hxD' hs hs').symm
      (S' (E.morTDom σ hx hx' D D' hxD hxD' hs hs'
        ((E.morTDom σ hx hx' D D' hxD hxD' hs hs').symm v)))) = S' v
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- **`σ_* : Or_x^{f|D} → Or_{x'}^{f|D'}`** for a morphism `σ : x → x'` between smooth objects
and domains `D ∋ x`, `D' ∋ x'`: the orientation map of the local isomorphism of `σ` read in the
two domains. -/
def orMorDom (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x') (D D' : B.Dom)
    (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) : D.Or hfT x hxD hs ≃ D'.Or hfT x' hxD' hs' :=
  (E.morIsoDom σ D D').orxViaAt (D'.isFredholm hfT).toIsScFredholmSection
    (D.isFredholm hfT).toIsScFredholmSection (E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 σ D D')
    D'.hasSections D.hasSections (E.mem_morIsoDomSet σ hx hx' hxD hxD')
    (StrongBundle.Dom.mem_smoothSet hxD' hs') (E.morIsoDom_ϕ_mk σ hx hx' hxD hxD')

/-- **`σ_*` on orientations is the conjugation by `Tσ` and `μ(σ, ·)`.** -/
theorem orMorDom_apply (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) (o : D.Or hfT x hxD hs) :
    E.orMorDom hF hfT σ hx hx' D D' hxD hxD' hs hs' o =
      o.conj (hC' := (D'.linPt hxD' hs').isFredholm_of_mem_linSet
          (D'.isFredholm hfT).toIsScFredholmSection)
        (E.morTDom σ hx hx' D D' hxD hxD' hs hs') (E.morKDom σ hx hx' D D' hxD hxD' hs hs')
        (E.morTDom_mem hF hfT σ hx hx' D D' hxD hxD' hs hs') :=
  (E.morIsoDom σ D D').orxViaAt_apply (D'.isFredholm hfT).toIsScFredholmSection
    (D.isFredholm hfT).toIsScFredholmSection (E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 σ D D')
    D'.hasSections D.hasSections (E.mem_morIsoDomSet σ hx hx' hxD hxD')
    (StrongBundle.Dom.mem_smoothSet hxD' hs') (E.morIsoDom_ϕ_mk σ hx hx' hxD hxD') o

theorem orMorDom_congr {σ σ' : Mor} (h : σ = σ') {x x' : Obj} (hx : X.src σ = x)
    (hx' : X.tgt σ = x') (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier)
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    E.orMorDom hF hfT σ hx hx' D D' hxD hxD' hs hs' =
      E.orMorDom hF hfT σ' (h ▸ hx) (h ▸ hx') D D' hxD hxD' hs hs' := by
  subst h; rfl

/-- **`(ψ ∘ φ)_* = ψ_* ∘ φ_*` on orientations**, read in three domains. -/
theorem orMorDom_comp {φ ψ : Mor} {x y z : Obj} (hφx : X.src φ = x) (hφy : X.tgt φ = y)
    (hψy : X.src ψ = y) (hψz : X.tgt ψ = z) (D D' D'' : B.Dom) (hxD : x ∈ D.carrier)
    (hyD : y ∈ D'.carrier) (hzD : z ∈ D''.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : y ∈ X.PObj.smoothSet) (hs'' : z ∈ X.PObj.smoothSet) :
    (E.orMorDom hF hfT φ hφx hφy D D' hxD hyD hs hs').trans
        (E.orMorDom hF hfT ψ hψy hψz D' D'' hyD hzD hs' hs'') =
      E.orMorDom hF hfT (X.comp ψ φ) (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) D D''
        hxD hzD hs hs'' :=
  StrongBundle.LocalIso.orxViaAt_triangle (L := E.morIsoDom φ D D')
    (L₂ := E.morIsoDom ψ D' D'') (N := E.morIsoDom (X.comp ψ φ) D D'')
    (D''.isFredholm hfT).toIsScFredholmSection (D'.isFredholm hfT).toIsScFredholmSection
    (D.isFredholm hfT).toIsScFredholmSection (E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 φ D D')
    (E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 ψ D' D'')
    (E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 (X.comp ψ φ) D D'') D''.hasSections
    D'.hasSections D.hasSections (E.mem_morIsoDomSet ψ hψy hψz hyD hzD)
    (E.mem_morIsoDomSet _ (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hxD hzD)
    (StrongBundle.Dom.mem_smoothSet hzD hs'') (E.morIsoDom_ϕ_mk ψ hψy hψz hyD hzD)
    (E.mem_morIsoDomSet φ hφx hφy hxD hyD) (E.morIsoDom_ϕ_mk φ hφx hφy hxD hyD)
    (E.morIsoDom_ϕ_mk _ (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hxD hzD)
    (E.morIsoDom_comp_germ hφx hφy hψy hψz hxD hyD hzD)

/-- **`(1_x)_* = Id` on orientations**, read in a domain. -/
theorem orMorDom_unit {σ : Mor} {x : Obj} (h : σ = X.unit x) (hx : X.src σ = x)
    (hx' : X.tgt σ = x) (D : B.Dom) (hxD : x ∈ D.carrier) (hs : x ∈ X.PObj.smoothSet) :
    E.orMorDom hF hfT σ hx hx' D D hxD hxD hs hs = Equiv.refl _ := by
  subst h
  have key := (E.orMorDom_comp hF hfT hx hx' hx hx' D D D hxD hxD hxD hs hs hs).trans
    (E.orMorDom_congr hF hfT (comp_unit_unit x) _ _ D D hxD hxD hs hs)
  refine Equiv.ext fun o => ?_
  exact (E.orMorDom hF hfT (X.unit x) hx hx' D D hxD hxD hs hs).injective
    (DFunLike.congr_fun key o)

/-- **`(φ⁻¹)_* = (φ_*)⁻¹` on orientations**, read in two domains. -/
theorem orMorDom_inv {φ : Mor} {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) :
    E.orMorDom hF hfT (X.inv φ) ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) D' D hxD'
        hxD hs' hs = (E.orMorDom hF hfT φ hx hx' D D' hxD hxD' hs hs').symm := by
  have h := (E.orMorDom_comp hF hfT hx hx' ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx)
    D D' D hxD hxD' hxD hs hs' hs).trans
    (E.orMorDom_unit hF hfT ((X.inv_comp φ).trans (congrArg X.unit hx)) _ _ D hxD hs)
  refine Equiv.ext fun o' => ?_
  have h1 := DFunLike.congr_fun h ((E.orMorDom hF hfT φ hx hx' D D' hxD hxD' hs hs').symm o')
  rw [Equiv.trans_apply, Equiv.apply_symm_apply] at h1
  exact h1

/-- **`σ_*` commutes with the comparison maps of domains**: for a morphism `σ : x → x'`, domains
`D₁, D₂ ∋ x` and `D₁', D₂' ∋ x'`, the comparison map `Or_x^{f|D₂} → Or_x^{f|D₁}` followed by
`σ_*` read in `D₁`, `D₁'` is `σ_*` read in `D₂`, `D₂'` followed by the comparison map
`Or_{x'}^{f|D₂'} → Or_{x'}^{f|D₁'}`. -/
theorem orMorDom_compare (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (D₁ D₂ D₁' D₂' : B.Dom) (hx₁ : x ∈ D₁.carrier) (hx₂ : x ∈ D₂.carrier)
    (hx₁' : x' ∈ D₁'.carrier) (hx₂' : x' ∈ D₂'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) :
    (D₁.compare D₂ hfT x hx₁ hx₂ hs).trans
        (E.orMorDom hF hfT σ hx hx' D₁ D₁' hx₁ hx₁' hs hs') =
      (E.orMorDom hF hfT σ hx hx' D₂ D₂' hx₂ hx₂' hs hs').trans
        (D₁'.compare D₂' hfT x' hx₁' hx₂' hs') :=
  StrongBundle.LocalIso.orxViaAt_square (L := D₁.iso D₂) (L₂ := E.morIsoDom σ D₁ D₁')
    (M := E.morIsoDom σ D₂ D₂') (M₂ := D₁'.iso D₂')
    (D₁'.isFredholm hfT).toIsScFredholmSection (D₁.isFredholm hfT).toIsScFredholmSection
    (D₂'.isFredholm hfT).toIsScFredholmSection (D₂.isFredholm hfT).toIsScFredholmSection
    (D₁.sec_eqOn_iso D₂ hfT.isScSmooth.1) (E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 σ D₁ D₁')
    (E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 σ D₂ D₂') (D₁'.sec_eqOn_iso D₂' hfT.isScSmooth.1)
    D₁'.hasSections D₁.hasSections D₂'.hasSections D₂.hasSections
    (E.mem_morIsoDomSet σ hx hx' hx₁ hx₁') hx₂' (StrongBundle.Dom.mem_smoothSet hx₁' hs')
    (E.morIsoDom_ϕ_mk σ hx hx' hx₁ hx₁') (D₁'.iso_ϕ_mk D₂' hx₁' hx₂') hx₂
    (E.mem_morIsoDomSet σ hx hx' hx₂ hx₂') (D₁.iso_ϕ_mk D₂ hx₁ hx₂)
    (E.morIsoDom_ϕ_mk σ hx hx' hx₂ hx₂') (E.germAgree₄_morIsoDom σ hx hx' hx₁ hx₂ hx₁' hx₂')

/-- **The orientation map of the isomorphism of `σ` at the target of a morphism `τ` of the sheet
of `σ` is `τ_*`**: for `τ : y → y'` in the sheet of `σ` and domains `D ∋ y`, `D' ∋ y'`. -/
theorem orxViaAt_morIsoDom_sheet (σ : Mor) {τ : Mor} (hτ : τ ∈ (X.sheetAt σ).carrier)
    {y y' : Obj} (hy : X.src τ = y) (hy' : X.tgt τ = y') (D D' : B.Dom) (hyD : y ∈ D.carrier)
    (hyD' : y' ∈ D'.carrier) (hs : y ∈ X.PObj.smoothSet) (hs' : y' ∈ X.PObj.smoothSet)
    (hmem : (⟨y', hyD'⟩ : D'.carrier) ∈ E.morIsoDomSet σ D D')
    (hϕ : (E.morIsoDom σ D D').ϕ ⟨y', hyD'⟩ = ⟨y, hyD⟩) :
    (E.morIsoDom σ D D').orxViaAt (D'.isFredholm hfT).toIsScFredholmSection
        (D.isFredholm hfT).toIsScFredholmSection
        (E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 σ D D') D'.hasSections D.hasSections hmem
        (StrongBundle.Dom.mem_smoothSet hyD' hs') hϕ =
      E.orMorDom hF hfT τ hy hy' D D' hyD hyD' hs hs' :=
  StrongBundle.LocalIso.orxViaAt_germ _ _ _ _ _ _ _ _ _ _ _
    (E.germEq_morIsoDom_sheet σ hτ hy hy' hyD hyD')

end Action

/-! ### Lemma 12.5.1 for the linearizations made with local sc⁺-sections -/

/-- **`Tφ : T_xX → T_{x'}X`** for a morphism `σ : x → x'` between smooth objects, read in the
chart points of the chosen domains at `x` and `x'`. -/
def morTLoc (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    ↥(linPtLoc B x hs).T ≃L[ℝ] ↥(linPtLoc B x' hs').T :=
  E.morTDom σ hx hx' (B.domAt x) (B.domAt x') (B.mem_domAt x) (B.mem_domAt x') hs hs'

/-- **`μ(σ, ·) : W_x → W_{x'}`** for a morphism `σ : x → x'` between smooth objects, read in the
chart points of the chosen domains at `x` and `x'`. -/
def morKLoc (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    ↥(linPtLoc B x hs).K ≃L[ℝ] ↥(linPtLoc B x' hs').K :=
  E.morKDom σ hx hx' (B.domAt x) (B.domAt x') (B.mem_domAt x) (B.mem_domAt x') hs hs'

/-- **`φ_* S = μ(φ, ·) ∘ S ∘ (Tφ)⁻¹`** (p. 592), read in the chart points of the chosen domains. -/
def linMorLoc (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet)
    (S : ↥(linPtLoc B x hs).T →L[ℝ] ↥(linPtLoc B x hs).K) :
    ↥(linPtLoc B x' hs').T →L[ℝ] ↥(linPtLoc B x' hs').K :=
  E.linMorDom σ hx hx' (B.domAt x) (B.domAt x') (B.mem_domAt x) (B.mem_domAt x') hs hs' S

theorem linMorLoc_apply (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet)
    (S : ↥(linPtLoc B x hs).T →L[ℝ] ↥(linPtLoc B x hs).K) (v : ↥(linPtLoc B x' hs').T) :
    E.linMorLoc σ hx hx' hs hs' S v =
      E.morKLoc σ hx hx' hs hs' (S ((E.morTLoc σ hx hx' hs hs').symm v)) := rfl

/-- **`T(ψ ∘ φ) = Tψ ∘ Tφ`** in the chart points of the chosen domains. -/
theorem morTLoc_comp {φ ψ : Mor} {x y z : Obj} (hφx : X.src φ = x) (hφy : X.tgt φ = y)
    (hψy : X.src ψ = y) (hψz : X.tgt ψ = z) (hs : x ∈ X.PObj.smoothSet)
    (hs' : y ∈ X.PObj.smoothSet) (hs'' : z ∈ X.PObj.smoothSet) (v : ↥(linPtLoc B x hs).T) :
    E.morTLoc ψ hψy hψz hs' hs'' (E.morTLoc φ hφx hφy hs hs' v) =
      E.morTLoc (X.comp ψ φ) (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hs hs'' v :=
  E.morTDom_comp hφx hφy hψy hψz _ _ _ _ _ _ hs hs' hs'' v

/-- **`μ(ψ ∘ φ, ·) = μ(ψ, ·) ∘ μ(φ, ·)`** in the chart points of the chosen domains. -/
theorem morKLoc_comp {φ ψ : Mor} {x y z : Obj} (hφx : X.src φ = x) (hφy : X.tgt φ = y)
    (hψy : X.src ψ = y) (hψz : X.tgt ψ = z) (hs : x ∈ X.PObj.smoothSet)
    (hs' : y ∈ X.PObj.smoothSet) (hs'' : z ∈ X.PObj.smoothSet) (k : ↥(linPtLoc B x hs).K) :
    E.morKLoc ψ hψy hψz hs' hs'' (E.morKLoc φ hφx hφy hs hs' k) =
      E.morKLoc (X.comp ψ φ) (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hs hs'' k :=
  E.morKDom_comp hφx hφy hψy hψz _ _ _ _ _ _ hs hs' hs'' k

/-- **`T(1_x) = Id`** in the chart point of the chosen domain. -/
theorem morTLoc_unit {σ : Mor} {x : Obj} (h : σ = X.unit x) (hx : X.src σ = x)
    (hx' : X.tgt σ = x) (hs : x ∈ X.PObj.smoothSet) (v : ↥(linPtLoc B x hs).T) :
    E.morTLoc σ hx hx' hs hs v = v :=
  E.morTDom_unit h hx hx' _ _ hs v

/-- **`μ(1_x, ·) = Id`** in the chart point of the chosen domain. -/
theorem morKLoc_unit {σ : Mor} {x : Obj} (h : σ = X.unit x) (hx : X.src σ = x)
    (hx' : X.tgt σ = x) (hs : x ∈ X.PObj.smoothSet) (k : ↥(linPtLoc B x hs).K) :
    E.morKLoc σ hx hx' hs hs k = k :=
  E.morKDom_unit h hx hx' _ _ hs k

section Action

variable (hF : E.IsScFredholmSectionFunctor f) (hfT : B.IsScFredholmSectionTame f)

include hF hfT in
/-- **Lemma 12.5.1 (1)**, p. 592, for the linearizations made with local sc⁺-sections: for a
morphism `φ : x → x'` between smooth objects and `S ∈ Lin(f, x)`, `φ_* S ∈ Lin(f, x')`.  Here
`f` is an sc-Fredholm section functor with tame germ data, and `Lin(f, x)` consists of the
linearizations `(f − s)'(x)` for the sc⁺-sections `s` over the chosen domain at `x` with
`s(x) = f(x)`. -/
theorem lemma_12_5_1_one_loc (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet)
    {S : ↥(linPtLoc B x hs).T →L[ℝ] ↥(linPtLoc B x hs).K}
    (hS : S ∈ (linPtLoc B x hs).linSet ((B.domAt x).sec f hfT.isScSmooth.1)) :
    E.linMorLoc σ hx hx' hs hs' S ∈
      (linPtLoc B x' hs').linSet ((B.domAt x').sec f hfT.isScSmooth.1) :=
  E.linMorDom_mem hF hfT σ hx hx' _ _ _ _ hs hs' hS

include hF hfT in
/-- **Lemma 12.5.1 (2)**, p. 592, for the linearizations made with local sc⁺-sections:
`φ_* : Lin(f, x) → Lin(f, x')` is a bijection. -/
theorem lemma_12_5_1_two_loc (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    Set.BijOn (E.linMorLoc σ hx hx' hs hs')
      ((linPtLoc B x hs).linSet ((B.domAt x).sec f hfT.isScSmooth.1))
      ((linPtLoc B x' hs').linSet ((B.domAt x').sec f hfT.isScSmooth.1)) :=
  E.bijOn_linMorDom hF hfT σ hx hx' _ _ _ _ hs hs'

/-- **Lemma 12.5.1 (3), units**, p. 592, for the linearizations made with local sc⁺-sections:
`(1_x)_* = Id_{Lin(f, x)}`. -/
theorem lemma_12_5_1_three_unit_loc (x : Obj) (hs : x ∈ X.PObj.smoothSet)
    (S : ↥(linPtLoc B x hs).T →L[ℝ] ↥(linPtLoc B x hs).K) :
    E.linMorLoc (X.unit x) (X.src_unit x) (X.tgt_unit x) hs hs S = S :=
  ContinuousLinearMap.ext fun v => by
    rw [linMorLoc_apply, E.morKLoc_unit rfl]
    congr 1
    rw [ContinuousLinearEquiv.symm_apply_eq, E.morTLoc_unit rfl]

/-- **Lemma 12.5.1 (3), composition**, p. 592, for the linearizations made with local
sc⁺-sections: `(ψ ∘ φ)_* = ψ_* ∘ φ_*` for `s(ψ) = t(φ)`. -/
theorem lemma_12_5_1_three_comp_loc {φ ψ : Mor} {x y z : Obj} (hφx : X.src φ = x)
    (hφy : X.tgt φ = y) (hψy : X.src ψ = y) (hψz : X.tgt ψ = z) (hs : x ∈ X.PObj.smoothSet)
    (hs' : y ∈ X.PObj.smoothSet) (hs'' : z ∈ X.PObj.smoothSet)
    (S : ↥(linPtLoc B x hs).T →L[ℝ] ↥(linPtLoc B x hs).K) :
    E.linMorLoc (X.comp ψ φ) (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hs hs'' S =
      E.linMorLoc ψ hψy hψz hs' hs'' (E.linMorLoc φ hφx hφy hs hs' S) :=
  ContinuousLinearMap.ext fun v => by
    rw [linMorLoc_apply, linMorLoc_apply, linMorLoc_apply,
      E.morKLoc_comp hφx hφy hψy hψz hs hs' hs'']
    congr 2
    rw [ContinuousLinearEquiv.symm_apply_eq, ← E.morTLoc_comp hφx hφy hψy hψz hs hs' hs'',
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

/-! ### The action on the local orientation sets -/

/-- **`φ_* : Or_x^f → Or_{x'}^f`** (p. 593) on the local orientation sets, for a morphism
`σ : x → x'` between smooth objects: an orientation `o` of `DET(f, x)` goes to
`φ_* S ↦ φ_* (o(S))`.  It is the orientation map of the local strong bundle isomorphism of `σ`
read in the chosen domains at `x` and `x'`, the conjugation by `Tφ` and `μ(φ, ·)`
(`orMorLoc_apply`). -/
def orMorLoc (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    OrxLoc hfT x hs ≃ OrxLoc hfT x' hs' :=
  E.orMorDom hF hfT σ hx hx' (B.domAt x) (B.domAt x') (B.mem_domAt x) (B.mem_domAt x') hs hs'

/-- **`φ_*` is the conjugation by `Tφ` and `μ(φ, ·)`**: `(φ_* o)(φ_* S) = conjDet (o(S))`. -/
theorem orMorLoc_apply (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (o : OrxLoc hfT x hs) :
    E.orMorLoc hF hfT σ hx hx' hs hs' o =
      o.conj (hC' := (linPtLoc B x' hs').isFredholm_of_mem_linSet
          ((B.domAt x').isFredholm hfT).toIsScFredholmSection)
        (E.morTLoc σ hx hx' hs hs') (E.morKLoc σ hx hx' hs hs')
        (E.morTDom_mem hF hfT σ hx hx' (B.domAt x) (B.domAt x') (B.mem_domAt x)
          (B.mem_domAt x') hs hs') :=
  E.orMorDom_apply hF hfT σ hx hx' _ _ _ _ hs hs' o

theorem orMorLoc_congr {σ σ' : Mor} (h : σ = σ') {x x' : Obj} (hx : X.src σ = x)
    (hx' : X.tgt σ = x') (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    E.orMorLoc hF hfT σ hx hx' hs hs' = E.orMorLoc hF hfT σ' (h ▸ hx) (h ▸ hx') hs hs' := by
  subst h; rfl

/-- **`(ψ ∘ φ)_* = ψ_* ∘ φ_*` on the local orientation sets.** -/
theorem orMorLoc_comp {φ ψ : Mor} {x y z : Obj} (hφx : X.src φ = x) (hφy : X.tgt φ = y)
    (hψy : X.src ψ = y) (hψz : X.tgt ψ = z) (hs : x ∈ X.PObj.smoothSet)
    (hs' : y ∈ X.PObj.smoothSet) (hs'' : z ∈ X.PObj.smoothSet) :
    (E.orMorLoc hF hfT φ hφx hφy hs hs').trans (E.orMorLoc hF hfT ψ hψy hψz hs' hs'') =
      E.orMorLoc hF hfT (X.comp ψ φ) (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hs
        hs'' :=
  E.orMorDom_comp hF hfT hφx hφy hψy hψz _ _ _ _ _ _ hs hs' hs''

/-- **`(1_x)_* = Id` on the local orientation sets.** -/
theorem orMorLoc_unit {σ : Mor} {x : Obj} (h : σ = X.unit x) (hx : X.src σ = x)
    (hx' : X.tgt σ = x) (hs : x ∈ X.PObj.smoothSet) :
    E.orMorLoc hF hfT σ hx hx' hs hs = Equiv.refl _ :=
  E.orMorDom_unit hF hfT h hx hx' _ _ hs

/-- **`(φ⁻¹)_* = (φ_*)⁻¹` on the local orientation sets.** -/
theorem orMorLoc_inv {φ : Mor} {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    E.orMorLoc hF hfT (X.inv φ) ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) hs' hs =
      (E.orMorLoc hF hfT φ hx hx' hs hs').symm :=
  E.orMorDom_inv hF hfT hx hx' _ _ _ _ hs hs'

/-- **`φ_*` read in two domains**: for a morphism `σ : x → x'` and domains `D ∋ x`, `D' ∋ x'`,
the identification `Or_x^f ≃ Or_x^{f|D}` followed by `σ_*` read in `D`, `D'` is `σ_*` on the
local orientation sets followed by the identification `Or_{x'}^f ≃ Or_{x'}^{f|D'}`. -/
theorem orMorDom_toLoc (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (D D' : B.Dom) (hxD : x ∈ D.carrier) (hxD' : x' ∈ D'.carrier) (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) :
    (D.toLoc hfT x hxD hs).trans (E.orMorDom hF hfT σ hx hx' D D' hxD hxD' hs hs') =
      (E.orMorLoc hF hfT σ hx hx' hs hs').trans (D'.toLoc hfT x' hxD' hs') :=
  E.orMorDom_compare hF hfT σ hx hx' D (B.domAt x) D' (B.domAt x') hxD (B.mem_domAt x) hxD'
    (B.mem_domAt x') hs hs'

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- The target of a morphism of a sheet lies in the target of the sheet. -/
theorem tgt_mem_tgtSet_of_mem_sheet (σ : Mor) {τ : Mor} (hτ : τ ∈ (X.sheetAt σ).carrier)
    {y' : Obj} (hy' : X.tgt τ = y') : y' ∈ (X.sheetAt σ).tgtSet :=
  hy' ▸ (X.sheetAt σ).isScDiffeoOn_tgt.mapsTo hτ

/-- The base map of the isomorphism of `σ` sends the target of a morphism `τ` of the sheet of
`σ` to the source of `τ`. -/
theorem morIso_ϕ_of_mem_sheet (σ : Mor) {τ : Mor} (hτ : τ ∈ (X.sheetAt σ).carrier) {y y' : Obj}
    (hy : X.src τ = y) (hy' : X.tgt τ = y') : (E.morIso σ).ϕ y' = y := by
  subst hy hy'
  change X.src ((X.sheetAt σ).tgtInv (X.tgt τ)) = X.src τ
  rw [(X.sheetAt σ).isScDiffeoOn_tgt.left_inv τ hτ]

/-- For a morphism `τ : y → y'` of the sheet of `σ` and domains `D ∋ y`, `D' ∋ y'`, the point
`y'` lies in the domain of `morIsoDom σ D D'`. -/
theorem mem_morIsoDomSet_of_mem_sheet (σ : Mor) {τ : Mor} (hτ : τ ∈ (X.sheetAt σ).carrier)
    {y y' : Obj} (hy : X.src τ = y) (hy' : X.tgt τ = y') {D D' : B.Dom} (hyD : y ∈ D.carrier)
    (hyD' : y' ∈ D'.carrier) : (⟨y', hyD'⟩ : D'.carrier) ∈ E.morIsoDomSet σ D D' :=
  ⟨tgt_mem_tgtSet_of_mem_sheet σ hτ hy', by
    change (E.morIso σ).ϕ y' ∈ D.carrier
    rw [E.morIso_ϕ_of_mem_sheet σ hτ hy hy']; exact hyD⟩

/-- For a morphism `τ : y → y'` of the sheet of `σ`, the base map of `morIsoDom σ D D'` sends
`y'` to `y`. -/
theorem morIsoDom_ϕ_mk_of_mem_sheet (σ : Mor) {τ : Mor} (hτ : τ ∈ (X.sheetAt σ).carrier)
    {y y' : Obj} (hy : X.src τ = y) (hy' : X.tgt τ = y') {D D' : B.Dom} (hyD : y ∈ D.carrier)
    (hyD' : y' ∈ D'.carrier) : (E.morIsoDom σ D D').ϕ ⟨y', hyD'⟩ = ⟨y, hyD⟩ :=
  (E.morIsoDom_ϕ_of_mem (E.mem_morIsoDomSet_of_mem_sheet σ hτ hy hy' hyD hyD')).trans
    (Subtype.ext (E.morIso_ϕ_of_mem_sheet σ hτ hy hy'))

/-- **The push-forward by the morphisms of a sheet is the orientation map of one local
isomorphism**: for a morphism `τ : y → y'` in the sheet of `σ` and domains `D ∋ y`, `D' ∋ y'`
(for instance the chosen domains at the source and the target of `σ`), the map
`τ_* : Or_y^f → Or_{y'}^f` is the orientation map at `y'` of the local isomorphism of `σ` read
in `D`, `D'`, conjugated by the identifications `Or_y^f ≃ Or_y^{f|D}` and
`Or_{y'}^f ≃ Or_{y'}^{f|D'}`. -/
theorem orMorLoc_eq_orxViaAt_sheet (σ : Mor) {τ : Mor} (hτ : τ ∈ (X.sheetAt σ).carrier)
    {y y' : Obj} (hy : X.src τ = y) (hy' : X.tgt τ = y') (D D' : B.Dom) (hyD : y ∈ D.carrier)
    (hyD' : y' ∈ D'.carrier) (hs : y ∈ X.PObj.smoothSet) (hs' : y' ∈ X.PObj.smoothSet) :
    (D.toLoc hfT y hyD hs).trans
        (((E.morIsoDom σ D D').orxViaAt (D'.isFredholm hfT).toIsScFredholmSection
          (D.isFredholm hfT).toIsScFredholmSection
          (E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 σ D D') D'.hasSections D.hasSections
          (E.mem_morIsoDomSet_of_mem_sheet σ hτ hy hy' hyD hyD')
          (StrongBundle.Dom.mem_smoothSet hyD' hs')
          (E.morIsoDom_ϕ_mk_of_mem_sheet σ hτ hy hy' hyD hyD')).trans
          (D'.toLoc hfT y' hyD' hs').symm) =
      E.orMorLoc hF hfT τ hy hy' hs hs' := by
  rw [E.orxViaAt_morIsoDom_sheet hF hfT σ hτ hy hy' D D' hyD hyD' hs hs']
  have h := E.orMorDom_toLoc hF hfT τ hy hy' D D' hyD hyD' hs hs'
  refine Equiv.ext fun o => ?_
  exact (Equiv.symm_apply_eq (D'.toLoc hfT y' hyD' hs')).2 (DFunLike.congr_fun h o)

end Action

end EpStrongBundle

end Mor

end Polyfold
