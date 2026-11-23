import Polyfold.Chapter16.OrientationRepLocalNoBumpsCover
import Polyfold.Chapter12.LocalOrientationComparison
import Polyfold.Chapter12.LocalOrientationFunctor
import Polyfold.Chapter16.PolyfoldFredholmSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
**Theorem 6.6.13** (pp. 273–274), **Definition 6.6.16** (p. 274), **Theorem 6.6.17**
(pp. 274–275); Chapter 12, **Definition 12.5.4** (p. 594); Chapter 16, **Definition 16.6.5**
(p. 739).

# An orientation of Definition 16.6.5 is an orientation made with local sc⁺-sections

## The text, paraphrased

Theorem 6.6.17: the orientation space `O_f` has exactly one topology which is Hausdorff and for
which (1) the projection to `X_∞` is a local homeomorphism, (2) there are two continuous sections
near every point, (3) along an sc-smooth path a continuous section of the pull-back is locally
the propagation of Theorem 6.6.11.  Definition 12.5.4 / 16.6.5: an orientation is a continuous
section of `O_f` which is invariant under the morphisms.

## What is formalized

No sc-smooth bump functions are used.

* `exists_isPropagationNbhd_of_isPropagationContinuous_dom`: a topology on `O_f` with property (3)
  gives, around every smooth point, an open set with the local propagation property
  (`IsPropagationNbhd`): property (3) for the constant path at the point names such a set.
  The push-forwards in these sets are made with sc⁺-sections of the pull-back bundle over
  `ℝ × X`, which are part of the local propagation property.
* `StrongBundle.Dom.toGlobal_transport_cover`, `StrongBundle.Dom.transportLoc_eq_conj_cover`,
  `orxLocEquiv_transport_cover`, `intertwines_orxLocEquiv_cover`: when the smooth points are
  covered by such sets, `orxLocEquiv : Or_x^f ≃ OrxLoc` carries the transport made from the
  covering (`orLocalTransportOfCover`) to the transport of the local orientation sets.
* `isSectionOrientationLoc_of_continuous_orSec`: for a topology on `O_f` with properties (1) and
  (3), a section `o` with `y ↦ (y, o_y)` continuous is, read through `orxLocEquiv`, an
  orientation in the sense of Definition 6.6.16 for the local orientation sets.
* `StrongPolyfoldBundle.OrientationRep.isSectionOrientationLoc`: the orientation of
  Definition 16.6.5.
* `StrongPolyfoldBundle.OrientationRep.isOrInvariant`: its invariance under the morphisms.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- Conjugation by a composite: if `a = r ∘ b` and `b₀ ∘ T = S ∘ b₁` then
`a₀ ∘ T ∘ a₁⁻¹ = r₀⁻¹ ∘ S ∘ r₁` (composition from left to right). -/
private theorem conj_eq_of_comm' {α α' β β' γ γ' : Sort*} {a₀ : α ≃ β} {a₁ : α' ≃ β'}
    {r₀ : γ ≃ α} {r₁ : γ' ≃ α'} {b₀ : γ ≃ β} {b₁ : γ' ≃ β'} {T : β ≃ β'} {S : γ ≃ γ'}
    (h₀ : r₀.trans a₀ = b₀) (h₁ : r₁.trans a₁ = b₁) (hc : b₀.trans T = S.trans b₁) :
    a₀.trans (T.trans a₁.symm) = r₀.symm.trans (S.trans r₁) := by
  subst h₀ h₁
  ext x
  have h := DFunLike.congr_fun hc (r₀.symm x)
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at h ⊢
  rw [h, Equiv.symm_apply_apply]

section Transport

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **Property (3) names propagation neighbourhoods**: if a topology on `O_f` has property (3)
of Theorem 6.6.17, every smooth point lies in an open set with the local propagation property
in some chart (property (3) for the constant path at the point). -/
theorem exists_isPropagationNbhd_of_isPropagationContinuous_dom (hf : B.IsScFredholmSection f)
    (hsec : B.HasScPlusSectionsThrough) {t : TopologicalSpace (OrSpace f hf)}
    (h3 : IsPropagationContinuous f hf t) (x : X) (hx : x ∈ PX.smoothSet) :
    ∃ U, IsPropagationNbhd f hf U ∧ x ∈ U := by
  let := t
  obtain ⟨a, -, -, -⟩ := exists_two_orx hf hx hsec
  let α : unitInterval → OrPullback f hf (fun _ : Fin 1 → ℝ => x) := fun s =>
    ⟨(s, ⟨PX.smoothMk x hx, a⟩), rfl⟩
  have hα : Continuous α := (continuous_id.prodMk continuous_const).subtype_mk _
  obtain ⟨_, U, hU, hseg, -⟩ :=
    (h3 _ (isScSmoothMap_const_of_mem_smoothSet hx) α hα (fun _ => rfl) 0).exists
  exact ⟨U, hU, hseg 0 ⟨le_rfl, zero_le_one⟩⟩

variable (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)
  (hcov : ∀ x ∈ PX.smoothSet, ∃ U, IsPropagationNbhd f hf.toIsScFredholmSection U ∧ x ∈ U)

namespace StrongBundle.Dom

variable (D : B.Dom)

/-- **The inclusion of a domain carries the transport of `f` to the transport of `f|W`**, for
the transport of `f` made from a covering by propagation neighbourhoods: for an sc-smooth path
`γ` from `x₀` to `x₁` with all values in a domain `W`, the map `Or_{x₀}^f ≃ Or_{x₀}^{f|W}`
followed by the transport of `f|W` along `γ` is the transport of `f` along `γ` followed by
`Or_{x₁}^f ≃ Or_{x₁}^{f|W}`. -/
theorem toGlobal_transport_cover {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    (D.toGlobal hf hsec x₀ (h₀ ▸ hγD _) hs₀).trans
      ((D.transport hX hf).transport (D.liftPath γ hγD) (D.isScSmoothMap_liftPath hγ hγD)
        (x₀ := ⟨x₀, h₀ ▸ hγD _⟩) (x₁ := ⟨x₁, h₁ ▸ hγD _⟩) (Subtype.ext h₀) (Subtype.ext h₁)
        (mem_smoothSet _ hs₀) (mem_smoothSet _ hs₁)) =
    ((orLocalTransportOfCover hf.toIsScFredholmSection hsec hcov).transport γ hγ h₀ h₁ hs₀
      hs₁).trans (D.toGlobal hf hsec x₁ (h₁ ▸ hγD _) hs₁) :=
  (B.restrictIso D.isOpen).orxVia_comm_chart_cover (D.isTame hX) D.exists_chart_univ
    (D.isFredholm hf) D.hasSections D.exists_chart hf.toIsScFredholmSection hsec hcov
    (B.restrictSection_eqOn_restrictIso D.isOpen hf.isScSmooth.1)
    (D.isScSmoothMap_liftPath hγ hγD) (x₀ := ⟨x₀, h₀ ▸ hγD _⟩) (x₁ := ⟨x₁, h₁ ▸ hγD _⟩)
    (Subtype.ext h₀) (Subtype.ext h₁) (mem_smoothSet _ hs₀) (mem_smoothSet _ hs₁)

/-- **The propagation in a domain is the transport of `f` made from the covering**, read
through `orxLocEquiv`. -/
theorem transportLoc_eq_conj_cover {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    D.transportLoc hX hf γ hγ hγD h₀ h₁ hs₀ hs₁ =
      (orxLocEquiv hf hsec x₀ hs₀).symm.trans
        (((orLocalTransportOfCover hf.toIsScFredholmSection hsec hcov).transport γ hγ h₀ h₁
          hs₀ hs₁).trans (orxLocEquiv hf hsec x₁ hs₁)) :=
  conj_eq_of_comm' (orxLocEquiv_toLoc hf hsec D x₀ (h₀ ▸ hγD _) hs₀)
    (orxLocEquiv_toLoc hf hsec D x₁ (h₁ ▸ hγD _) hs₁)
    (D.toGlobal_transport_cover hX hf hsec hcov hγ hγD h₀ h₁ hs₀ hs₁)

end StrongBundle.Dom

/-- **`orxLocEquiv` commutes with the transports**: the transport of the local orientation sets
along an sc-smooth path is the transport made from a covering by propagation neighbourhoods,
read through `orxLocEquiv`. -/
theorem orxLocEquiv_transport_cover {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) :
    (orxLocEquiv hf hsec x₀ hs₀).symm.trans
        (((orLocalTransportOfCover hf.toIsScFredholmSection hsec hcov).transport γ hγ h₀ h₁
          hs₀ hs₁).trans (orxLocEquiv hf hsec x₁ hs₁)) =
      (orLocalTransportLoc hX hf).transport γ hγ h₀ h₁ hs₀ hs₁ := by
  refine (orLocalTransportLoc hX hf).transport_unique
    (fun γ hγ {x₀ x₁} h₀ h₁ hs₀ hs₁ => (orxLocEquiv hf hsec x₀ hs₀).symm.trans
      (((orLocalTransportOfCover hf.toIsScFredholmSection hsec hcov).transport γ hγ h₀ h₁ hs₀
        hs₁).trans (orxLocEquiv hf hsec x₁ hs₁))) ?_ ?_ ?_ hγ h₀ h₁ hs₀ hs₁
  · intro γ₀ γ₁ Φ hΦ hγ₀ hγ₁ x₀ x₁ h₀ h₁ hs₀ hs₁
    exact congrArg (fun T => (orxLocEquiv hf hsec x₀ hs₀).symm.trans
        (T.trans (orxLocEquiv hf hsec x₁ hs₁)))
      ((orLocalTransportOfCover hf.toIsScFredholmSection hsec
        hcov).transport_eq_of_isScHomotopyRel hΦ hγ₀ hγ₁ h₀ h₁ hs₀ hs₁)
  · intro γ₁ γ₂ hγ₁ hγ₂ x₀ x₁ x₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
    have e := (orLocalTransportOfCover hf.toIsScFredholmSection hsec hcov).transport_concatPath
      hγ₁ hγ₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
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
    have er := (orLocalTransportOfCover hf.toIsScFredholmSection hsec hcov).transport_reparam hγ
      Real.smoothTransition.contDiff Real.smoothTransition.zero Real.smoothTransition.one h₀ h₁
      hs₀ hs₁
    rw [orLocalTransportLoc_push_eq hX hf hU hU.2.choose hγ hγU hγD h₀ h₁ hs₀ hs₁,
      hU.2.choose.transportLoc_eq_conj_cover hX hf hsec hcov
        (isScSmoothMap_smoothTransPath_or hγ) hγD h₀' h₁' hs₀ hs₁]
    exact congrArg (fun T => (orxLocEquiv hf hsec x₀ hs₀).symm.trans
        (T.trans (orxLocEquiv hf hsec x₁ hs₁))) er.symm

/-- **`orxLocEquiv` commutes with the transports** (`LocalTransport.Intertwines`), for the
transport made from a covering by propagation neighbourhoods. -/
theorem intertwines_orxLocEquiv_cover :
    (orLocalTransportOfCover hf.toIsScFredholmSection hsec hcov).Intertwines
      (orLocalTransportLoc hX hf) fun x hs => orxLocEquiv hf hsec x hs := by
  intro γ hγ x₀ x₁ h₀ h₁ hs₀ hs₁ a
  have e := DFunLike.congr_fun (orxLocEquiv_transport_cover hX hf hsec hcov hγ h₀ h₁ hs₀ hs₁)
    (orxLocEquiv hf hsec x₀ hs₀ a)
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at e
  exact e

omit hcov in
/-- **A continuous section of `O_f` is an orientation made with local sc⁺-sections**
(Definition 6.6.16, Theorem 6.6.17), without sc-smooth bump functions: for a topology `t` on
`O_f` with properties (1) and (3) of Theorem 6.6.17 and a family `o_y ∈ Or_y^f` with
`y ↦ (y, o_y)` continuous for `t`, the family read through `orxLocEquiv` is carried along by the
propagation of the local orientation sets.  Property (3) names the propagation neighbourhoods
(`exists_isPropagationNbhd_of_isPropagationContinuous_dom`); `t` is the topology of the transport
made from them (`LocalTransport.eq_topology_of`), so that `o` is carried along by this transport
(`LocalTransport.isContOn_univ_of_continuous_sec`), which `orxLocEquiv` carries to the transport
of the local orientation sets (`intertwines_orxLocEquiv_cover`). -/
theorem isSectionOrientationLoc_of_continuous_orSec
    {t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection)}
    (h1 : @IsLocalHomeomorph _ _ t _ (orProj f hf.toIsScFredholmSection))
    (h3 : IsPropagationContinuous f hf.toIsScFredholmSection t)
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy)
    (hc : @Continuous _ _ _ t (orSec o)) :
    IsSectionOrientationLoc hX hf fun y hy => orxLocEquiv hf hsec y hy (o y hy) := by
  have hcov := exists_isPropagationNbhd_of_isPropagationContinuous_dom hf.toIsScFredholmSection hsec
    h3
  have ht : t = (orLocalTransportOfCover hf.toIsScFredholmSection hsec hcov).topology :=
    LocalTransport.eq_topology_of (L := orLocalTransportOfCover hf.toIsScFredholmSection hsec
      hcov) h1 h3
  subst ht
  have hcont : (orLocalTransportOfCover hf.toIsScFredholmSection hsec hcov).IsContOn univ o :=
    LocalTransport.isContOn_univ_of_continuous_sec
      (fun _ hy => exists_two_orx hf.toIsScFredholmSection hy hsec) hc
  exact (isSectionOrientationLoc_iff_isContOn_univ hX hf _).2
    (((intertwines_orxLocEquiv_cover hX hf hsec hcov).isContOn_iff univ o).1 hcont)

end Transport

end Polyfold

namespace Polyfold.StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization SEP

universe u

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **An orientation in the sense of Definition 16.6.5 is an orientation made with local
sc⁺-sections** (2021 pp. 274–275, 739), for a tame object M-polyfold and tame germ data of `F`,
without sc-smooth bump functions: the family `o`, read through `orxLocEquiv`, is an orientation
of `F` in the sense of Definition 6.6.16 for the local orientation sets. -/
theorem OrientationRep.isSectionOrientationLoc {s : FredholmSection c} (o : OrientationRep s)
    (hX : o.a.S.A.X.PObj.IsTame) (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F) :
    IsSectionOrientationLoc hX hft fun y hy => orxLocEquiv hft o.hsec y hy (o.o y hy) := by
  have := paracompactSpace_rn_prod o.a.S.A.X.PObj
  have := paracompactSpace_rn_pullback o.a.S.A.B
  exact isSectionOrientationLoc_of_continuous_orSec hX hft o.hsec
    o.isOrientationTopology.isLocalHomeomorph o.isOrientationTopology.propagation o.o
    o.isOrientation.1

/-- **The orientation of Definition 16.6.5 is invariant under the morphisms**: the second clause
of Definition 12.5.4. -/
theorem OrientationRep.isOrInvariant {s : FredholmSection c} (o : OrientationRep s) :
    o.a.S.A.E.IsOrInvariant o.hF o.hsec o.o :=
  o.isOrientation.2

end Polyfold.StrongPolyfoldBundle
