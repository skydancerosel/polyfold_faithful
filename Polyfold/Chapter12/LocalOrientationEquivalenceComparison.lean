import Polyfold.Chapter12.LocalOrientationEquivalenceHomeo
import Polyfold.Chapter12.LocalOrientationComparisonEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7**: the maps of orientations of local strong bundle isomorphisms
and of strong bundle equivalences on the local orientation sets agree with those on the
orientation sets made with sc⁺-sections over the whole base, where the latter exist.

## The text, paraphrased

The linearizations `(f − s)'(x)` are taken for sc⁺-sections `s` with `s(x) = f(x)`; such
sections are found in a strong bundle chart around `x` (p. 239), and with sc-smooth bump
functions they extend to the whole base.

## What is formalized

With sc⁺-sections through all smooth fibre points over the whole base (`hsec`, a consequence of
sc-smooth bump functions) both descriptions of the orientation sets exist: `Orx` (sc⁺-sections
over the whole base) and `OrxLoc` (sc⁺-sections over open subsets of chart domains), identified
by `orxLocEquiv`.

* `StrongBundle.LocalIso.restrictIso_domIso_germ`, `toGlobal_orDom`,
  **`orxLocEquiv_orxViaAt`**: for a local strong bundle isomorphism `L` with `f = Ψ ∘ f' ∘ ϕ`,
  `orxLocEquiv` intertwines `L.orxViaAt` and `L.orLoc`.
* `IsStrongBundleEquivalence.orxLocEquiv_orEqv`: for a strong bundle equivalence, `orxLocEquiv`
  intertwines `orEqv` and `orEqvLoc`; `orxLocEquiv_pullOr`: pull-backs of families correspond.
* `orSpaceMapLoc_orSpaceLocHomeomorph`, **`orbitOrMapLoc_orbitLocHomeomorph`**: with sc-smooth
  bump functions, the homeomorphisms `O_f ≅ O_f^{loc}` and `|O_f| ≅ |O_f^{loc}|` intertwine the
  maps of Theorem 12.5.7 (1) in the two descriptions.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v'

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

/-- **A local isomorphism and the inclusions of two domains**: near a point `a ∈ U ∩ D` with
`ϕ(a) ∈ D'`, the inclusion `P|D → P` followed by `L` is `L` read in `D`, `D'` followed by the
inclusion `P'|D' → P'`. -/
theorem restrictIso_domIso_germ {D : B.Dom} {D' : B'.Dom} {a : X} {x : X'} (ha : a ∈ U)
    (hϕ : L.ϕ a = x) (haD : a ∈ D.carrier) (hxD : x ∈ D'.carrier) :
    GermAgree₄ L (B.restrictIso D.isOpen) (B'.restrictIso D'.isOpen) (L.domIso D D')
      (⟨a, haD⟩ : D.carrier) := by
  refine ⟨⟨L.domSet D D', (L.domIso D D').isOpen_U, L.mem_domSet ha hϕ haD hxD,
    fun _ _ => mem_univ _, subset_rfl, fun y hy => ?_, fun q hq => ?_⟩⟩
  · rw [domIso_ϕ_of_mem hy]; rfl
  · have hPq : P q.1.2 = q.1.1.1 := StrongBundle.pullbackSpace_subtypeVal_proj q
    have h1 : P' (L.Φ q.1.2) ∈ D'.carrier := by
      rw [L.covers _ (by rw [hPq]; exact hq.1), hPq]; exact hq.2
    change L.Φ q.1.2 = (B'.restrictIsoInv D'.carrier (L.Φ q.1.2)).1.2
    rw [B'.restrictIsoInv_of_mem h1]

variable (hf : B.IsScFredholmSectionTame f) (hf' : B'.IsScFredholmSectionTame f')
  (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
  (hsec' : B'.HasScPlusSectionsThrough)

/-- **The map of orientations read in two domains and on the whole base**: the identifications
`Or^f ≃ Or^{f|D}`, `Or^{f'} ≃ Or^{f'|D'}` intertwine `L.orxViaAt` and `L.orDom`. -/
theorem toGlobal_orDom (D : B.Dom) (D' : B'.Dom) {a : X} {x : X'} (ha : a ∈ U)
    (hϕ : L.ϕ a = x) (haD : a ∈ D.carrier) (hxD : x ∈ D'.carrier) (has : a ∈ PX.smoothSet)
    (hxs : x ∈ PX'.smoothSet) :
    (L.orxViaAt hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' ha has
        hϕ).trans (D.toGlobal hf hsec a haD has) =
      (D'.toGlobal hf' hsec' x hxD hxs).trans
        (L.orDom hf hf' hfL D D' ha hϕ haD hxD has hxs) :=
  orxViaAt_square (L := L) (L₂ := B.restrictIso D.isOpen) (M := B'.restrictIso D'.isOpen)
    (M₂ := L.domIso D D') (D.isFredholm hf).toIsScFredholmSection hf.toIsScFredholmSection
    (D'.isFredholm hf').toIsScFredholmSection hf'.toIsScFredholmSection hfL
    (B.restrictSection_eqOn_restrictIso D.isOpen hf.isScSmooth.1)
    (B'.restrictSection_eqOn_restrictIso D'.isOpen hf'.isScSmooth.1)
    (L.sec_eqOn_domIso hf.isScSmooth.1 hf'.isScSmooth.1 hfL D D') D.hasSections hsec
    D'.hasSections hsec' (b := ⟨a, haD⟩) (mem_univ _) (L.mem_domSet ha hϕ haD hxD)
    (StrongBundle.Dom.mem_smoothSet haD has) rfl (L.domIso_ϕ_mk ha hϕ haD hxD) ha (mem_univ _)
    hϕ rfl (L.restrictIso_domIso_germ ha hϕ haD hxD)

/-- **`orxLocEquiv` intertwines the maps of orientations of a local strong bundle
isomorphism**: `Or^{f'}_{ϕ(a)} → Or^f_a` made with sc⁺-sections over the whole bases, followed
by `orxLocEquiv` at `a`, is `orxLocEquiv` at `ϕ(a)` followed by the map `L.orLoc` on the local
orientation sets. -/
theorem orxLocEquiv_orxViaAt {a : X} {x : X'} (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (has : a ∈ PX.smoothSet) (hxs : x ∈ PX'.smoothSet) :
    (L.orxViaAt hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' ha has
        hϕ).trans (orxLocEquiv hf hsec a has) =
      (orxLocEquiv hf' hsec' x hxs).trans (L.orLoc hf hf' hfL ha hϕ has hxs) :=
  L.toGlobal_orDom hf hf' hfL hsec hsec' (B.domAt a) (B'.domAt x) ha hϕ (B.mem_domAt a)
    (B'.mem_domAt x) has hxs

end StrongBundle.LocalIso

end Two

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
  (hfT : B.IsScFredholmSectionTame f) (hfT' : B'.IsScFredholmSectionTame f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)

/-- **`orxLocEquiv` intertwines the identifications of orientations of a strong bundle
equivalence**: `orEqv a` (sc⁺-sections over the whole object spaces) followed by `orxLocEquiv`
at `a` is `orxLocEquiv` at `ϕ(a)` followed by `orEqvLoc a`. -/
theorem orxLocEquiv_orEqv (a : Obj) (hs : a ∈ X.PObj.smoothSet) :
    (h.orEqv hF hF' hpb hsec hsec' a hs).trans (orxLocEquiv hfT hsec a hs) =
      (orxLocEquiv hfT' hsec' (ϕ.obj a) (h.smooth_obj hs)).trans
        (h.orEqvLoc hpb hfT hfT' a hs) := by
  rw [h.orEqv_eq_orxVia hF hF' hpb hsec hsec' (h.mem_locSet a) hs]
  exact (h.locIso a).orxLocEquiv_orxViaAt hfT hfT' (h.eqOn_loc hpb hfT'.isScSmooth.1 a) hsec
    hsec' (h.mem_locSet a) rfl hs (h.smooth_obj hs)

theorem orxLocEquiv_orEqv_apply (a : Obj) (hs : a ∈ X.PObj.smoothSet)
    (o : Orx f' hF'.2 (ϕ.obj a) (h.smooth_obj hs)) :
    orxLocEquiv hfT hsec a hs (h.orEqv hF hF' hpb hsec hsec' a hs o) =
      h.orEqvLoc hpb hfT hfT' a hs (orxLocEquiv hfT' hsec' (ϕ.obj a) (h.smooth_obj hs) o) :=
  DFunLike.congr_fun (h.orxLocEquiv_orEqv hF hF' hpb hfT hfT' hsec hsec' a hs) o

/-- **Pull-backs of families of orientations correspond**: the image under `orxLocEquiv` of
the pull-back `pullOr o'` is the pull-back `pullOrLoc` of the image of `o'`. -/
theorem orxLocEquiv_pullOr (o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs) (a : Obj)
    (hs : a ∈ X.PObj.smoothSet) :
    orxLocEquiv hfT hsec a hs (h.pullOr hF hF' hpb hsec hsec' o' a hs) =
      h.pullOrLoc hpb hfT hfT' (fun x hx => orxLocEquiv hfT' hsec' x hx (o' x hx)) a hs :=
  h.orxLocEquiv_orEqv_apply hF hF' hpb hfT hfT' hsec hsec' a hs _

section Space

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj')]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin n → ℝ) × Obj' → Obj'))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj'))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P' (Prod.snd : (Fin n → ℝ) × Obj' → Obj'))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj') → (Fin n → ℝ) × Obj'))]

variable (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (hX' : X'.PObj.IsTame)
  (hbump' : X'.PObj.AdmitsBumpFunctions)

/-- **The maps `O_f → O_{f'}` of a strong bundle equivalence correspond** under the
homeomorphisms of the orientation spaces. -/
theorem orSpaceMapLoc_orSpaceLocHomeomorph (p : OrSpace f hF.2) :
    h.orSpaceMapLoc hpb hX hX' hfT hfT' (orSpaceLocHomeomorph hX hbump hfT hsec p) =
      orSpaceLocHomeomorph hX' hbump' hfT' hsec' (h.orSpaceMap hF hF' hpb hsec hsec' p) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  change (h.orEqvLoc hpb hfT hfT' _ (X.PObj.smoothVal_mem p.1)).symm
      (orxLocEquiv hfT hsec _ (X.PObj.smoothVal_mem p.1) p.2) =
    orxLocEquiv hfT' hsec' _ (h.smooth_obj (X.PObj.smoothVal_mem p.1))
      ((h.orEqv hF hF' hpb hsec hsec' _ (X.PObj.smoothVal_mem p.1)).symm p.2)
  rw [Equiv.symm_apply_eq, ← h.orxLocEquiv_orEqv_apply hF hF' hpb hfT hfT' hsec hsec',
    Equiv.apply_symm_apply]

/-- **The maps `|O_f| → |O_{f'}|` of Theorem 12.5.7 (1) for one strong bundle equivalence
correspond** under the homeomorphisms of the orbit spaces of the orientation spaces. -/
theorem orbitOrMapLoc_orbitLocHomeomorph (c : Quot (E.OrRel hF hsec)) :
    h.orbitOrMapLoc hF hF' hpb hX hX' hfT hfT' (E.orbitLocHomeomorph hF hfT hsec hX hbump c) =
      E'.orbitLocHomeomorph hF' hfT' hsec' hX' hbump'
        (h.orbitOrMap hF hF' hpb hsec hsec' c) := by
  induction c using Quot.ind with
  | mk p =>
    exact congrArg (Quot.mk _)
      (h.orSpaceMapLoc_orSpaceLocHomeomorph hF hF' hpb hfT hfT' hsec hsec' hX hbump hX' hbump' p)

end Space

end EpStrongBundle.IsStrongBundleEquivalence

end Equiv

end Polyfold
