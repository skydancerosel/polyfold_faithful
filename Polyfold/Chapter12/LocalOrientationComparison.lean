import Polyfold.Chapter12.ChartBumpTransportCommute
import Polyfold.Chapter12.LocalOrientationSpace
import Polyfold.Chapter6.TransportSpaceEquiv

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6:
Definition 6.2.1 (p. 239), Theorem 6.6.11 (p. 272), Theorem 6.6.13 (pp. 273–274) and
Theorem 6.6.17 (pp. 274–275).

# The orientation space made with local sc⁺-sections is the one made with global ones

## The text, paraphrased

`Lin(f, x)` is the set of the linearizations `(f − s)'(x)` for the sc⁺-sections `s` with
`s(x) = f(x)`; such `s` exist near `x` ("we take a strong bundle chart around `x`", p. 239),
and if `X` admits sc-smooth bump functions they can be taken to be defined on all of `X`.  The
orientations of `DET(f, x)` are the orientations of the determinants of the members of
`Lin(f, x)` related by the canonical maps; they are propagated along sc-smooth paths
(Theorem 6.6.11, Theorem 6.6.13), and the orientation space `O_f` has the topology of
Theorem 6.6.17.

## What is formalized

`Orx f hf x` is made with the sc⁺-sections of the bundle over all of `X`, with the transport
`orLocalTransport` (which uses sc-smooth bump functions) and the orientation space `OrSpace`.
`OrxLoc hf x` is made with the sc⁺-sections over an open subset of a chart domain, with the
transport `orLocalTransportLoc` and the orientation space `OrSpaceLoc` (no bump functions).
When `X` admits sc-smooth bump functions the two agree:

* `Dom.toGlobal`: `Or_x^f ≃ Or_x^{f|W}` for a domain `W ∋ x`, the orientation map of the
  inclusion `P|W → P`; `Dom.toGlobal_compare`: compatibility with the comparison maps of two
  domains.
* `orxLocEquiv`: **`Or_x^f ≃ OrxLoc`**, with `orxLocEquiv_toLoc`.
* `Dom.toGlobal_transport`: for sc-smooth paths in a domain `W`, `toGlobal` carries the
  transport of `f` to the transport of `f|W`; `Dom.transportLoc_eq_conj`.
* `intertwines_orxLocEquiv`: **`orxLocEquiv` commutes with the transports** along all sc-smooth
  paths (`orxLocEquiv_transport`).
* `isContOrOn_iff_isContOn_orxLocEquiv`: the continuous orientations over an open set
  correspond.
* `orSpaceLocHomeomorph`: **the homeomorphism `O_f ≃ₜ OrSpaceLoc`** over the identity of `X_∞`
  (`proj_orSpaceLocHomeomorph`), carrying the section of `o` to the section of its image
  (`orSpaceLocHomeomorph_orSec`).
* `exists_orSpaceLoc_homeomorph`: the same without instance arguments and with the sc⁺-sections
  through all smooth fibre points obtained from the bump functions.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- Conjugation by a composite: if `a = r ∘ b` and `b₀ ∘ T = S ∘ b₁` then
`a₀ ∘ T ∘ a₁⁻¹ = r₀⁻¹ ∘ S ∘ r₁` (composition from left to right). -/
private theorem conj_eq_of_comm {α α' β β' γ γ' : Sort*} {a₀ : α ≃ β} {a₁ : α' ≃ β'}
    {r₀ : γ ≃ α} {r₁ : γ' ≃ α'} {b₀ : γ ≃ β} {b₁ : γ' ≃ β'} {T : β ≃ β'} {S : γ ≃ γ'}
    (h₀ : r₀.trans a₀ = b₀) (h₁ : r₁.trans a₁ = b₁) (hc : b₀.trans T = S.trans b₁) :
    a₀.trans (T.trans a₁.symm) = r₀.symm.trans (S.trans r₁) := by
  subst h₀ h₁
  ext x
  have h := DFunLike.congr_fun hc (r₀.symm x)
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at h ⊢
  rw [h, Equiv.symm_apply_apply]

namespace StrongBundle.Dom

variable (D D' : B.Dom)

/-! ### The orientation map of the inclusion of a domain -/

/-- **`Or_x^f ≃ Or_x^{f|W}`** for a smooth point `x` of a domain `W`: the orientation map of the
inclusion `P|W → P`.  The linearizations of `f` are made with the sc⁺-sections of `P` over all
of the base, those of `f|W` with the sc⁺-sections over `W`. -/
def toGlobal (hf : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough) (x : X)
    (hx : x ∈ D.carrier) (hs : x ∈ PX.smoothSet) :
    Orx f hf.toIsScFredholmSection x hs ≃ D.Or hf x hx hs :=
  (B.restrictIso D.isOpen).orxViaAt (D.isFredholm hf).toIsScFredholmSection
    hf.toIsScFredholmSection (B.restrictSection_eqOn_restrictIso D.isOpen hf.isScSmooth.1)
    D.hasSections hsec (a := ⟨x, hx⟩) (mem_univ _) (mem_smoothSet hx hs) rfl

/-- The inclusion `P|W' → P` after the identification of `P|W` with `P|W'` is the inclusion
`P|W → P`, near every point of `W ∩ W'`. -/
theorem restrictIso_iso_germ {x : X} (hx : x ∈ D.carrier) (hx' : x ∈ D'.carrier) :
    ∃ N : Set D.carrier, IsOpen N ∧ (⟨x, hx⟩ : D.carrier) ∈ N ∧
      (∀ y ∈ N, (B.restrictIso D'.isOpen).ϕ ((D.iso D').ϕ y) = (B.restrictIso D.isOpen).ϕ y) ∧
      ∀ w, pullbackProj P (Subtype.val : D.carrier → X) w ∈ N →
        (B.restrictIso D'.isOpen).Φ ((D.iso D').Φ w) = (B.restrictIso D.isOpen).Φ w := by
  refine ⟨{w : D.carrier | w.1 ∈ D'.carrier}, D'.isOpen.preimage continuous_subtype_val, hx',
    fun y hy => ?_, fun w hw => ?_⟩
  · rw [D.iso_ϕ_of_mem D' hy]; rfl
  · have h1 : P w.1.2 ∈ D'.carrier := by
      rw [StrongBundle.pullbackSpace_subtypeVal_proj w]; exact hw
    change (B.restrictIsoInv D'.carrier w.1.2).1.2 = w.1.2
    rw [B.restrictIsoInv_of_mem h1]

/-- **The maps `Or_x^f ≃ Or_x^{f|W}` are compatible with the comparison maps of domains.** -/
theorem toGlobal_compare (hf : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough)
    (x : X) (hx : x ∈ D.carrier) (hx' : x ∈ D'.carrier) (hs : x ∈ PX.smoothSet) :
    (D'.toGlobal hf hsec x hx' hs).trans (D.compare D' hf x hx hx' hs) =
      D.toGlobal hf hsec x hx hs :=
  StrongBundle.LocalIso.orxViaAt_triangle (L := B.restrictIso D'.isOpen) (L₂ := D.iso D')
    (N := B.restrictIso D.isOpen) (D.isFredholm hf).toIsScFredholmSection
    (D'.isFredholm hf).toIsScFredholmSection hf.toIsScFredholmSection
    (B.restrictSection_eqOn_restrictIso D'.isOpen hf.isScSmooth.1)
    (D.sec_eqOn_iso D' hf.isScSmooth.1)
    (B.restrictSection_eqOn_restrictIso D.isOpen hf.isScSmooth.1) D.hasSections D'.hasSections
    hsec (b := ⟨x, hx⟩) hx' (mem_univ _) (mem_smoothSet hx hs) (D.iso_ϕ_mk D' hx hx')
    (x₁ := ⟨x, hx'⟩) (mem_univ _) rfl rfl (D.restrictIso_iso_germ D' hx hx')

end StrongBundle.Dom

/-! ### The comparison of the orientation sets -/

/-- **`Or_x^f ≃ OrxLoc`**: the orientations of `DET(f, x)` made with the sc⁺-sections over all
of the base and those made with the sc⁺-sections over the chosen domain at `x` correspond
under the orientation map of the inclusion of the domain. -/
def orxLocEquiv (hf : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough) (x : X)
    (hs : x ∈ PX.smoothSet) : Orx f hf.toIsScFredholmSection x hs ≃ OrxLoc hf x hs :=
  (B.domAt x).toGlobal hf hsec x (B.mem_domAt x) hs

/-- `Or_x^f ≃ OrxLoc ≃ Or_x^{f|W}` is the orientation map of the inclusion of `W`. -/
theorem orxLocEquiv_toLoc (hf : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough)
    (D : B.Dom) (x : X) (hx : x ∈ D.carrier) (hs : x ∈ PX.smoothSet) :
    (orxLocEquiv hf hsec x hs).trans (D.toLoc hf x hx hs) = D.toGlobal hf hsec x hx hs :=
  D.toGlobal_compare (B.domAt x) hf hsec x hx (B.mem_domAt x) hs

/-! ### The transports -/

section Transport

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

variable (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)

namespace StrongBundle.Dom

variable (D : B.Dom)

/-- **The inclusion of a domain carries the transport of `f` to the transport of `f|W`**: for an
sc-smooth path `γ` from `x₀` to `x₁` with all values in a domain `W`, the map
`Or_{x₀}^f ≃ Or_{x₀}^{f|W}` followed by the transport of `f|W` along `γ` is the transport of
`f` along `γ` followed by `Or_{x₁}^f ≃ Or_{x₁}^{f|W}`. -/
theorem toGlobal_transport {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    (D.toGlobal hf hsec x₀ (h₀ ▸ hγD _) hs₀).trans
      ((D.transport hX hf).transport (D.liftPath γ hγD) (D.isScSmoothMap_liftPath hγ hγD)
        (x₀ := ⟨x₀, h₀ ▸ hγD _⟩) (x₁ := ⟨x₁, h₁ ▸ hγD _⟩) (Subtype.ext h₀) (Subtype.ext h₁)
        (mem_smoothSet _ hs₀) (mem_smoothSet _ hs₁)) =
    ((orLocalTransport hX hbump hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁).trans
      (D.toGlobal hf hsec x₁ (h₁ ▸ hγD _) hs₁) :=
  (B.restrictIso D.isOpen).orxVia_comm_chart_bump (D.isTame hX) D.exists_chart_univ
    (D.isFredholm hf) D.hasSections hX hbump D.exists_chart hf hsec
    (B.restrictSection_eqOn_restrictIso D.isOpen hf.isScSmooth.1)
    (D.isScSmoothMap_liftPath hγ hγD) (x₀ := ⟨x₀, h₀ ▸ hγD _⟩) (x₁ := ⟨x₁, h₁ ▸ hγD _⟩)
    (Subtype.ext h₀) (Subtype.ext h₁) (mem_smoothSet _ hs₀) (mem_smoothSet _ hs₁)

/-- **The propagation in a domain is the transport of `f`**, read through `orxLocEquiv`. -/
theorem transportLoc_eq_conj {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    D.transportLoc hX hf γ hγ hγD h₀ h₁ hs₀ hs₁ =
      (orxLocEquiv hf hsec x₀ hs₀).symm.trans
        (((orLocalTransport hX hbump hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁).trans
          (orxLocEquiv hf hsec x₁ hs₁)) :=
  conj_eq_of_comm (orxLocEquiv_toLoc hf hsec D x₀ (h₀ ▸ hγD _) hs₀)
    (orxLocEquiv_toLoc hf hsec D x₁ (h₁ ▸ hγD _) hs₁)
    (D.toGlobal_transport hX hbump hf hsec hγ hγD h₀ h₁ hs₀ hs₁)

end StrongBundle.Dom

/-- **`orxLocEquiv` commutes with the transports**: the transport of the local orientation sets
along an sc-smooth path is the transport of Theorem 6.6.13 made with sc-smooth bump functions,
read through `orxLocEquiv`. -/
theorem orxLocEquiv_transport {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) :
    (orxLocEquiv hf hsec x₀ hs₀).symm.trans
        (((orLocalTransport hX hbump hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁).trans
          (orxLocEquiv hf hsec x₁ hs₁)) =
      (orLocalTransportLoc hX hf).transport γ hγ h₀ h₁ hs₀ hs₁ := by
  refine (orLocalTransportLoc hX hf).transport_unique
    (fun γ hγ {x₀ x₁} h₀ h₁ hs₀ hs₁ => (orxLocEquiv hf hsec x₀ hs₀).symm.trans
      (((orLocalTransport hX hbump hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁).trans
        (orxLocEquiv hf hsec x₁ hs₁))) ?_ ?_ ?_ hγ h₀ h₁ hs₀ hs₁
  · intro γ₀ γ₁ Φ hΦ hγ₀ hγ₁ x₀ x₁ h₀ h₁ hs₀ hs₁
    exact congrArg (fun T => (orxLocEquiv hf hsec x₀ hs₀).symm.trans
        (T.trans (orxLocEquiv hf hsec x₁ hs₁)))
      ((orLocalTransport hX hbump hf hsec).transport_eq_of_isScHomotopyRel hΦ hγ₀ hγ₁ h₀ h₁
        hs₀ hs₁)
  · intro γ₁ γ₂ hγ₁ hγ₂ x₀ x₁ x₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
    have e := (orLocalTransport hX hbump hf hsec).transport_concatPath hγ₁ hγ₂ h₁₀ h₁₁ h₂₀ h₂₁
      hs₀ hs₁ hs₂
    refine Equiv.ext fun a => ?_
    have e' := DFunLike.congr_fun e ((orxLocEquiv hf hsec x₀ hs₀).symm a)
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at e' ⊢
    exact congrArg _ e'
  · intro U hU γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁
    have hγD : ∀ q, smoothTransPath_or γ q ∈ hU.2.choose.carrier := fun q =>
      hU.2.choose_spec.1 (smoothTransPath_or_mem hγU q)
    have h₀' : smoothTransPath_or γ (pt1 0) = x₀ :=
      (congrArg (fun t => γ (pt1 t)) Real.smoothTransition.zero).trans h₀
    have h₁' : smoothTransPath_or γ (pt1 1) = x₁ :=
      (congrArg (fun t => γ (pt1 t)) Real.smoothTransition.one).trans h₁
    have er := (orLocalTransport hX hbump hf hsec).transport_reparam hγ
      Real.smoothTransition.contDiff Real.smoothTransition.zero Real.smoothTransition.one h₀ h₁
      hs₀ hs₁
    rw [orLocalTransportLoc_push_eq hX hf hU hU.2.choose hγ hγU hγD h₀ h₁ hs₀ hs₁,
      hU.2.choose.transportLoc_eq_conj hX hbump hf hsec (isScSmoothMap_smoothTransPath_or hγ)
        hγD h₀' h₁' hs₀ hs₁]
    exact congrArg (fun T => (orxLocEquiv hf hsec x₀ hs₀).symm.trans
        (T.trans (orxLocEquiv hf hsec x₁ hs₁))) er.symm

/-- **`orxLocEquiv` commutes with the transports** (`LocalTransport.Intertwines`). -/
theorem intertwines_orxLocEquiv :
    (orLocalTransport hX hbump hf hsec).Intertwines (orLocalTransportLoc hX hf)
      fun x hs => orxLocEquiv hf hsec x hs := by
  intro γ hγ x₀ x₁ h₀ h₁ hs₀ hs₁ a
  have e := DFunLike.congr_fun (orxLocEquiv_transport hX hbump hf hsec hγ h₀ h₁ hs₀ hs₁)
    (orxLocEquiv hf hsec x₀ hs₀ a)
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at e
  exact e

/-- **The continuous orientations correspond**: a family `o_y ∈ Or_y^f` is a continuous
orientation over an open set `U` (for the transport made with bump functions) iff its image in
the local orientation sets is carried along by their transport over `U`. -/
theorem isContOrOn_iff_isContOn_orxLocEquiv (U : Set X)
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy) :
    IsContOrOn (orLocalTransport hX hbump hf hsec) U o ↔
      (orLocalTransportLoc hX hf).IsContOn U fun y hy => orxLocEquiv hf hsec y hy (o y hy) :=
  (intertwines_orxLocEquiv hX hbump hf hsec).isContOn_iff U o

/-- **The homeomorphism of the orientation spaces**: `(x, o) ↦ (x, orxLocEquiv o)` is a
homeomorphism from `O_f` with the topology of Theorem 6.6.17 made with sc-smooth bump
functions onto the orientation space of the local orientation sets. -/
def orSpaceLocHomeomorph :
    @Homeomorph (OrSpace f hf.toIsScFredholmSection) (OrSpaceLoc hX hf)
      (orTopology (orLocalTransport hX hbump hf hsec)) (orTopologyLoc hX hf) :=
  (intertwines_orxLocEquiv hX hbump hf hsec).totalHomeomorph

theorem orSpaceLocHomeomorph_apply (p : OrSpace f hf.toIsScFredholmSection) :
    orSpaceLocHomeomorph hX hbump hf hsec p = ⟨p.1, orxLocEquiv hf hsec _ _ p.2⟩ := rfl

/-- The homeomorphism of the orientation spaces commutes with the projections to `X_∞`. -/
theorem proj_orSpaceLocHomeomorph (p : OrSpace f hf.toIsScFredholmSection) :
    (orLocalTransportLoc hX hf).proj (orSpaceLocHomeomorph hX hbump hf hsec p) =
      orProj f hf.toIsScFredholmSection p := rfl

/-- The homeomorphism of the orientation spaces carries the section of `o` to the section of
the image of `o`. -/
theorem orSpaceLocHomeomorph_orSec
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy)
    (y : PX.SmoothLevel) :
    orSpaceLocHomeomorph hX hbump hf hsec (orSec o y) =
      (orLocalTransportLoc hX hf).sec (fun y hy => orxLocEquiv hf hsec y hy (o y hy)) y := rfl

end Transport

/-- **The orientation space made with local sc⁺-sections is the orientation space of
Theorem 6.6.17**, for a tame M-polyfold with sc-smooth bump functions and a section with tame
germ data: there is a homeomorphism `O_f ≃ₜ OrSpaceLoc` over the identity of `X_∞` which is a
bijection `Or_x^f ≃ OrxLoc` on every fibre and under which the continuous orientations over
open sets correspond. -/
theorem exists_orSpaceLoc_homeomorph (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) :
    haveI := paracompactSpace_rn_prod PX
    haveI := paracompactSpace_rn_pullback B
    haveI := paracompactSpace_rn_rn_prod PX
    haveI := paracompactSpace_rn_rn_pullback B
    ∃ (ρ : ∀ x (hs : x ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection x hs ≃ OrxLoc hf x hs)
      (F : @Homeomorph (OrSpace f hf.toIsScFredholmSection) (OrSpaceLoc hX hf)
        (orTopology (orLocalTransport hX hbump hf
          (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump)))
        (orTopologyLoc hX hf)),
      (∀ p, F p = ⟨p.1, ρ _ _ p.2⟩) ∧
      ∀ (U : Set X) (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy),
        IsContOrOn (orLocalTransport hX hbump hf
          (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump)) U o ↔
        (orLocalTransportLoc hX hf).IsContOn U fun y hy => ρ y hy (o y hy) := by
  have := paracompactSpace_rn_prod PX
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod PX
  have := paracompactSpace_rn_rn_pullback B
  exact ⟨fun x hs => orxLocEquiv hf _ x hs, orSpaceLocHomeomorph hX hbump hf _, fun _ => rfl,
    fun U o => isContOrOn_iff_isContOn_orxLocEquiv hX hbump hf _ U o⟩

end Polyfold
