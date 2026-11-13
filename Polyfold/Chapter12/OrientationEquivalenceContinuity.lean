import Polyfold.Chapter12.OrientationGerm
import Polyfold.Chapter12.OrientationNaturality

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597: **Theorem 12.5.7 (2)** (2017: Theorem 12.12 (2)), the continuity of the
push-forward of an orientation, for one strong bundle equivalence.

# Strong bundle equivalences keep orientations continuous

* `LocalIso.isContOrOn_of_pullOrx`: the converse of `isContOrOn_pullOrx` — if the section carried
  by a local strong bundle isomorphism `L` from `o'` is a continuous orientation over
  `U ∩ ϕ⁻¹(V')`, then `o'` is one over `U' ∩ V'` (paths in `U'` are carried back by `ϕ⁻¹`, and
  `orxVia_comm`).
* `IsStrongBundleEquivalence.isContOrOn_pullOr_hyp`: the pull-back `pullOr o'` of a continuous
  orientation `o'` over `V'` is one over `ϕ⁻¹(V')` (`orEqv_eq_orxVia`, `isContOrOn_pullOrx`, and
  the locality lemma `isContOrOn_of_local_or`).
* `IsStrongBundleEquivalence.isContOrOn_pushOr_hyp`: the push-forward `pushOr o` of an invariant
  continuous orientation `o` (over all of `X`) is a continuous orientation over all of `X'`: near
  `ϕ(a)` by `isContOrOn_of_pullOrx`, near any `x'` by a morphism `ψ : ϕ(a) → x'` and the last
  sentence of Theorem 12.5.3 (`theorem_12_5_3_push_hyp`, `pullOrx_morIso_eq_orMor`).
* `theorem_12_5_7_two_hyp`: **Theorem 12.5.7 (2) with continuity** for a representative
  `W ← V → W'`: the unique invariant push-forward `o'` of an invariant continuous orientation `o`
  is continuous; `theorem_12_5_7_two_cont`: the same without instance arguments.

"Continuous" is Part I's `IsContOrOn` over an open set; its relation to the continuity of
`x ↦ (x, o_x)` for Part I's topology is `continuousOn_orSec`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v'

section Back

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U : Set X} {U' : Set X'} (L : LocalIso B B' U U')

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X')]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin n → ℝ) × X' → X'))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X'))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P' (Prod.snd : (Fin n → ℝ) × X' → X'))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X') → (Fin n → ℝ) × X'))]

variable (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough) (hX' : PX'.IsTame) (hbump' : PX'.AdmitsBumpFunctions)
  (hf' : B'.IsScFredholmSectionTame f') (hsec' : B'.HasScPlusSectionsThrough)
  (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U)

/-- **A section is continuous where the section it carries is** (the converse of
`isContOrOn_pullOrx`): if `a ↦ orxVia (o'_{ϕ(a)})` is a continuous orientation of `f` over
`U ∩ ϕ⁻¹(V')`, then `o'` is a continuous orientation of `f'` over `U' ∩ V'`. -/
theorem isContOrOn_of_pullOrx {V' : Set X'} (hV' : IsOpen V')
    {o' : ∀ y (hy : y ∈ PX'.smoothSet), Orx f' hf'.toIsScFredholmSection y hy}
    (h : IsContOrOn (orLocalTransport hX hbump hf hsec) (U ∩ L.ϕ ⁻¹' V')
      (L.pullOrx hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' o')) :
    IsContOrOn (orLocalTransport hX' hbump' hf' hsec') (U' ∩ V') o' := by
  refine ⟨L.isOpen_U'.inter hV', ?_⟩
  intro γ' hγ' hγ'V x₀' x₁' h₀' h₁' hs₀' hs₁'
  have hx₀' : x₀' ∈ U' := h₀' ▸ (hγ'V 0 (left_mem_Icc.2 zero_le_one)).1
  have hx₁' : x₁' ∈ U' := h₁' ▸ (hγ'V 1 (right_mem_Icc.2 zero_le_one)).1
  obtain ⟨x₀, hx₀, rfl⟩ : ∃ x₀ ∈ U, L.ϕ x₀ = x₀' :=
    ⟨L.g x₀', L.base.mapsTo_inv hx₀', L.base.right_inv _ hx₀'⟩
  obtain ⟨x₁, hx₁, rfl⟩ : ∃ x₁ ∈ U, L.ϕ x₁ = x₁' :=
    ⟨L.g x₁', L.base.mapsTo_inv hx₁', L.base.right_inv _ hx₁'⟩
  have hs₀ : x₀ ∈ PX.smoothSet := (L.mem_smoothSet_iff hx₀).2 hs₀'
  have hs₁ : x₁ ∈ PX.smoothSet := (L.mem_smoothSet_iff hx₁).2 hs₁'
  have hγ'' := isScSmoothMap_smoothTransPath_or hγ'
  have hγ''U : ∀ q, smoothTransPath_or γ' q ∈ U' ∩ V' := smoothTransPath_or_mem hγ'V
  set γ : (Fin 1 → ℝ) → X := fun q => L.g (smoothTransPath_or γ' q) with hγdef
  have hγ : (rnPolyfold 1).IsScSmoothMap PX γ :=
    L.base.isScSmoothOn_inv.comp hγ'' fun q _ => (hγ''U q).1
  have hγU : ∀ q, γ q ∈ U := fun q => L.base.mapsTo_inv (hγ''U q).1
  have hϕγ : ∀ q, L.ϕ (γ q) = smoothTransPath_or γ' q := fun q =>
    L.base.right_inv _ (hγ''U q).1
  have h₀'' : smoothTransPath_or γ' (pt1 0) = L.ϕ x₀ :=
    (congrArg (fun t => γ' (pt1 t)) Real.smoothTransition.zero).trans h₀'
  have h₁'' : smoothTransPath_or γ' (pt1 1) = L.ϕ x₁ :=
    (congrArg (fun t => γ' (pt1 t)) Real.smoothTransition.one).trans h₁'
  have h₀ : γ (pt1 0) = x₀ := by
    change L.g (smoothTransPath_or γ' (pt1 0)) = x₀
    rw [h₀'', L.base.left_inv _ hx₀]
  have h₁ : γ (pt1 1) = x₁ := by
    change L.g (smoothTransPath_or γ' (pt1 1)) = x₁
    rw [h₁'', L.base.left_inv _ hx₁]
  have e1 := (orLocalTransport hX' hbump' hf' hsec').transport_reparam hγ'
    Real.smoothTransition.contDiff Real.smoothTransition.zero Real.smoothTransition.one h₀' h₁'
    hs₀' hs₁'
  have e2 := (orLocalTransport hX' hbump' hf' hsec').transport_congr
    (γ := fun s => γ' (pt1 (Real.smoothTransition (s 0)))) (γ' := fun q => L.ϕ (γ q))
    (fun t _ => (hϕγ (pt1 t)).symm) (isScSmoothMap_reparam hγ' Real.smoothTransition.contDiff)
    (L.isScSmoothMap_comp_or hγ hγU) h₀'' h₁'' (congrArg L.ϕ h₀) (congrArg L.ϕ h₁) hs₀' hs₁'
  rw [← e1, e2]
  have hc := DFunLike.congr_fun (L.orxVia_comm hX hbump hf hsec hX' hbump' hf' hsec' hfL hγ hγU
    h₀ h₁ hx₀ hx₁ hs₀ hs₁) (o' (L.ϕ x₀) hs₀')
  simp only [Equiv.trans_apply] at hc
  have hcont := h.2 γ hγ (fun t _ => ⟨hγU _, by rw [mem_preimage, hϕγ]; exact (hγ''U _).2⟩)
    h₀ h₁ hs₀ hs₁
  rw [pullOrx, pullOrx, dif_pos hx₀, dif_pos hx₁] at hcont
  exact (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' hx₁
    hs₁).injective (hc.symm.trans hcont)

end StrongBundle.LocalIso

end Back

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
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)
  (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (hfT : B.IsScFredholmSectionTame f)
  (hX' : X'.PObj.IsTame) (hbump' : X'.PObj.AdmitsBumpFunctions)
  (hfT' : B'.IsScFredholmSectionTame f')

/-- `pullOr o'` is, on `U(a)`, the section carried by the local isomorphism at `a`. -/
theorem pullOr_eq_pullOrx (a : Obj) (o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs)
    {y : Obj} (hy : y ∈ h.locSet a) (hys : y ∈ X.PObj.smoothSet) :
    (h.locIso a).pullOrx hF.2 hF'.2 (h.eqOn_loc hpb hF'.2.isScSmooth.1 a) hsec hsec' o' y hys =
      h.pullOr hF hF' hpb hsec hsec' o' y hys := by
  rw [StrongBundle.LocalIso.pullOrx, dif_pos hy, ← h.orEqv_eq_orxVia hF hF' hpb hsec hsec' hy]
  rfl

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj')]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin n → ℝ) × Obj' → Obj'))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj'))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P' (Prod.snd : (Fin n → ℝ) × Obj' → Obj'))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj') → (Fin n → ℝ) × Obj'))]

/-- **The pull-back of a continuous orientation is continuous** (Theorem 12.5.7, p. 595, the
pull-back half of (2), for one equivalence; Part I's hypotheses): if `o'` is a continuous
orientation of `f'` over an open `V'`, then `pullOr o'` is one of `f` over `ϕ⁻¹(V')`. -/
theorem isContOrOn_pullOr_hyp {V' : Set Obj'}
    {o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs}
    (ho' : IsContOrOn (orLocalTransport hX' hbump' hfT' hsec') V' o') :
    IsContOrOn (orLocalTransport hX hbump hfT hsec) (ϕ.obj ⁻¹' V')
      (h.pullOr hF hF' hpb hsec hsec' o') := by
  have hloc : ∀ b, IsContOrOn (orLocalTransport hX hbump hfT hsec) (h.locSet b ∩ ϕ.obj ⁻¹' V')
      (h.pullOr hF hF' hpb hsec hsec' o') := fun b =>
    ((h.locIso b).isContOrOn_pullOrx hX hbump hfT hsec hX' hbump' hfT' hsec'
      (h.eqOn_loc hpb hF'.2.isScSmooth.1 b) ho').congr_or fun y hy hys =>
        h.pullOr_eq_pullOrx hF hF' hpb hsec hsec' b o' hy.1 hys
  have hopen : IsOpen (ϕ.obj ⁻¹' V') := by
    refine isOpen_iff_forall_mem_open.2 fun b hb => ?_
    exact ⟨h.locSet b ∩ ϕ.obj ⁻¹' V', fun y hy => hy.2, (hloc b).1, ⟨h.mem_locSet b, hb⟩⟩
  refine isContOrOn_of_local_or hopen ?_
  intro b hb _
  exact ⟨h.locSet b ∩ ϕ.obj ⁻¹' V', ⟨h.mem_locSet b, hb⟩, hloc b⟩

/-- **The push-forward of an invariant continuous orientation is continuous** (Theorem 12.5.7,
p. 595, the push-forward half of (2), for one equivalence; Part I's hypotheses): if `o` is an
invariant continuous orientation of `f` over all of `X`, then `pushOr o` is an invariant
continuous orientation of `f'` over all of `X'`. -/
theorem isContOrOn_pushOr_hyp {o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs}
    (ho : E.IsOrInvariant hF hsec o)
    (hoc : IsContOrOn (orLocalTransport hX hbump hfT hsec) univ o) :
    IsContOrOn (orLocalTransport hX' hbump' hfT' hsec') univ
      (h.pushOr hF hF' hpb hsec hsec' o) := by
  set o' := h.pushOr hF hF' hpb hsec hsec' o
  have hinv' := h.isOrInvariant_pushOr hF hF' hpb hsec hsec' ho
  -- near `ϕ(a)`
  have hnear : ∀ a, IsContOrOn (orLocalTransport hX' hbump' hfT' hsec') (h.locSet' a ∩ univ) o' :=
    fun a => (h.locIso a).isContOrOn_of_pullOrx hX hbump hfT hsec hX' hbump' hfT' hsec'
      (h.eqOn_loc hpb hF'.2.isScSmooth.1 a) isOpen_univ
      ((hoc.mono_or ((h.isOpen_locSet a).inter isOpen_univ) (subset_univ _)).congr_or
        fun y hy hys => by
          rw [h.pullOr_eq_pullOrx hF hF' hpb hsec hsec' a o' hy.1 hys]
          exact (h.pushOr_obj hF hF' hpb hsec hsec' ho hys).symm)
  refine isContOrOn_of_local_or isOpen_univ fun x' _ hs' => ?_
  obtain ⟨a, ha, ψ, h1, h2⟩ := h.exists_smooth_iso hs'
  obtain ⟨hC, hmem, -⟩ := E'.theorem_12_5_3_push_hyp hF' hsec' hX' hbump' hfT' ψ h1 h2
    (h.smooth_obj ha) hs' (hnear a)
  refine ⟨_, hmem ⟨h.obj_mem_locSet' a, mem_univ _⟩, hC.congr_or fun y' hy' hys' => ?_⟩
  have hϕs : (E'.morIso ψ).ϕ y' ∈ X'.PObj.smoothSet :=
    ((E'.morIso ψ).mem_smoothSet_iff hy'.1).1 hys'
  rw [E'.pullOrx_morIso_eq_orMor hF' hsec' ψ hy'.1 hϕs hys' o']
  exact hinv' _ _ _ _ _

end EpStrongBundle.IsStrongBundleEquivalence

end Equiv

section Diagram

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
  {Obj'' Mor'' : Type u} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor''] {X'' : EpGroupoid Obj'' Mor''}
  {W'' : Type u} [TopologicalSpace W''] [T2Space W''] [ParacompactSpace W''] {P'' : W'' → Obj''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
  {B'' : StrongBundle X''.PObj P''} [ParacompactSpace (pullbackSpace P'' X''.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {E'' : EpStrongBundle X'' B''}
  {ϕ₁ : EpFunctor X'' X} {Φ₁ : EpFunctor E''.toEpGroupoid E.toEpGroupoid}
  {ϕ₂ : EpFunctor X'' X'} {Φ₂ : EpFunctor E''.toEpGroupoid E'.toEpGroupoid}
  (h₁ : E''.IsStrongBundleEquivalence E ϕ₁ Φ₁) (h₂ : E''.IsStrongBundleEquivalence E' ϕ₂ Φ₂)
  {f : Obj → W} {f' : Obj' → W'} {f'' : Obj'' → W''} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hF'' : E''.IsScFredholmSectionFunctor f'')
  (hpb₁ : f'' = h₁.pullback f) (hpb₂ : f'' = h₂.pullback f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)
  (hsec'' : B''.HasScPlusSectionsThrough)
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
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
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj'')]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P'' (Prod.snd : (Fin n → ℝ) × Obj'' → Obj''))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj''))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P'' (Prod.snd : (Fin n → ℝ) × Obj'' → Obj''))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj'') → (Fin n → ℝ) × Obj''))]
  (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (hfT : B.IsScFredholmSectionTame f)
  (hX' : X'.PObj.IsTame) (hbump' : X'.PObj.AdmitsBumpFunctions)
  (hfT' : B'.IsScFredholmSectionTame f') (hX'' : X''.PObj.IsTame)
  (hbump'' : X''.PObj.AdmitsBumpFunctions) (hfT'' : B''.IsScFredholmSectionTame f'')

include hX'' hbump'' hfT'' in
/-- **Theorem 12.5.7 (2)**, p. 595 (2017: Theorem 12.12 (2)), with continuity and Part I's
hypotheses, for a representative `W ←Φ₁– V –Φ₂→ W'`: an invariant orientation `o` of `f` which is
a continuous orientation over all of `X` (Part I's `IsContOrOn`) has exactly one invariant
section `o'` of `σ'` corresponding to `o` over `V`, and `o'` is a continuous orientation over all
of `X'`. -/
theorem theorem_12_5_7_two_hyp {o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs}
    (ho : E.IsOrInvariant hF hsec o)
    (hoc : IsContOrOn (orLocalTransport hX hbump hfT hsec) univ o) :
    ∃! o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs,
      E'.IsOrInvariant hF' hsec' o' ∧ (∀ v (hv : v ∈ X''.PObj.smoothSet),
        h₂.orEqv hF'' hF' hpb₂ hsec'' hsec' v hv (o' (ϕ₂.obj v) (h₂.smooth_obj hv)) =
          h₁.orEqv hF'' hF hpb₁ hsec'' hsec v hv (o (ϕ₁.obj v) (h₁.smooth_obj hv))) ∧
        IsContOrOn (orLocalTransport hX' hbump' hfT' hsec') univ o' := by
  have ho'' := h₁.isOrInvariant_pullOr hF'' hF hpb₁ hsec'' hsec ho
  have hc'' : IsContOrOn (orLocalTransport hX'' hbump'' hfT'' hsec'') univ
      (h₁.pullOr hF'' hF hpb₁ hsec'' hsec o) := by
    have := h₁.isContOrOn_pullOr_hyp hF'' hF hpb₁ hsec'' hsec hX'' hbump'' hfT'' hX hbump hfT hoc
    rwa [preimage_univ] at this
  refine ⟨h₂.pushOr hF'' hF' hpb₂ hsec'' hsec' (h₁.pullOr hF'' hF hpb₁ hsec'' hsec o),
    ⟨h₂.isOrInvariant_pushOr hF'' hF' hpb₂ hsec'' hsec' ho'', fun v hv =>
      h₂.pushOr_obj hF'' hF' hpb₂ hsec'' hsec' ho'' hv,
      h₂.isContOrOn_pushOr_hyp hF'' hF' hpb₂ hsec'' hsec' hX'' hbump'' hfT'' hX' hbump' hfT'
        ho'' hc''⟩, fun o' ⟨ho', hoo, _⟩ => ?_⟩
  exact h₂.pushOr_unique hF'' hF' hpb₂ hsec'' hsec' ho'' ho' hoo

end Diagram

section DiagramWitness


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
  {Obj'' Mor'' : Type u} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor''] {X'' : EpGroupoid Obj'' Mor''}
  {W'' : Type u} [TopologicalSpace W''] [T2Space W''] [ParacompactSpace W''] {P'' : W'' → Obj''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
  {B'' : StrongBundle X''.PObj P''} [ParacompactSpace (pullbackSpace P'' X''.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {E'' : EpStrongBundle X'' B''}
  {ϕ₁ : EpFunctor X'' X} {Φ₁ : EpFunctor E''.toEpGroupoid E.toEpGroupoid}
  {ϕ₂ : EpFunctor X'' X'} {Φ₂ : EpFunctor E''.toEpGroupoid E'.toEpGroupoid}
  (h₁ : E''.IsStrongBundleEquivalence E ϕ₁ Φ₁) (h₂ : E''.IsStrongBundleEquivalence E' ϕ₂ Φ₂)
  {f : Obj → W} {f' : Obj' → W'} {f'' : Obj'' → W''} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hF'' : E''.IsScFredholmSectionFunctor f'')
  (hpb₁ : f'' = h₁.pullback f) (hpb₂ : f'' = h₂.pullback f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)
  (hsec'' : B''.HasScPlusSectionsThrough)
  (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (hfT : B.IsScFredholmSectionTame f)
  (hX' : X'.PObj.IsTame) (hbump' : X'.PObj.AdmitsBumpFunctions)
  (hfT' : B'.IsScFredholmSectionTame f') (hX'' : X''.PObj.IsTame)
  (hbump'' : X''.PObj.AdmitsBumpFunctions) (hfT'' : B''.IsScFredholmSectionTame f'')

include hX'' hbump'' hfT'' in
/-- **Theorem 12.5.7 (2)**, p. 595 (2017: Theorem 12.12 (2)), with continuity, Part I's hypotheses
and no instance arguments (they hold for the metrizable spaces of the text:
`paracompactSpace_rn_prod`, `paracompactSpace_rn_pullback`, `paracompactSpace_rn_rn_prod`,
`paracompactSpace_rn_rn_pullback`); as `theorem_12_5_7_two_hyp`. -/
theorem theorem_12_5_7_two_cont {o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs}
    (ho : E.IsOrInvariant hF hsec o) :
    haveI := paracompactSpace_rn_prod X.PObj
    haveI := paracompactSpace_rn_pullback B
    haveI := paracompactSpace_rn_rn_prod X.PObj
    haveI := paracompactSpace_rn_rn_pullback B
    haveI := paracompactSpace_rn_prod X'.PObj
    haveI := paracompactSpace_rn_pullback B'
    haveI := paracompactSpace_rn_rn_prod X'.PObj
    haveI := paracompactSpace_rn_rn_pullback B'
    IsContOrOn (orLocalTransport hX hbump hfT hsec) univ o →
    ∃! o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs,
      E'.IsOrInvariant hF' hsec' o' ∧ (∀ v (hv : v ∈ X''.PObj.smoothSet),
        h₂.orEqv hF'' hF' hpb₂ hsec'' hsec' v hv (o' (ϕ₂.obj v) (h₂.smooth_obj hv)) =
          h₁.orEqv hF'' hF hpb₁ hsec'' hsec v hv (o (ϕ₁.obj v) (h₁.smooth_obj hv))) ∧
        IsContOrOn (orLocalTransport hX' hbump' hfT' hsec') univ o' := by
  have := paracompactSpace_rn_prod X.PObj
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod X.PObj
  have := paracompactSpace_rn_rn_pullback B
  have := paracompactSpace_rn_prod X'.PObj
  have := paracompactSpace_rn_pullback B'
  have := paracompactSpace_rn_rn_prod X'.PObj
  have := paracompactSpace_rn_rn_pullback B'
  have := paracompactSpace_rn_prod X''.PObj
  have := paracompactSpace_rn_pullback B''
  have := paracompactSpace_rn_rn_prod X''.PObj
  have := paracompactSpace_rn_rn_pullback B''
  exact theorem_12_5_7_two_hyp h₁ h₂ hF hF' hF'' hpb₁ hpb₂ hsec hsec' hsec'' hX hbump hfT hX'
    hbump' hfT' hX'' hbump'' hfT'' ho

end DiagramWitness

end Polyfold
