import Polyfold.Chapter2.LevelPolyfold
import Polyfold.Chapter2.FibredProduct

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.1, the proof
of **Proposition 9.1.9 (1)** (p. 406; 2017: Proposition 9.1, pp. 295–296): "we can use them to
construct ordinary M⁺-polyfold charts for the metrizable space `Z`, which … are smoothly
compatible".

# Descending an M-polyfold structure along a local homeomorphism

## The text, paraphrased

(Proof of Proposition 9.1.9 (1)) The maps `Ψ_x : M_x → Z` are injective and open onto open
subsets; if `Ψ_x(w) = Ψ_{x'}(w')`, then `Ψ_{x'}⁻¹ ∘ Ψ_x` is near `w` the restriction of an
sc-diffeomorphism `t ∘ (s|U(φ))⁻¹`, so the charts of the `M_x` pushed forward by the `Ψ_x` are
sc-smoothly compatible and define a smooth structure on `Z`.

## What is formalized

A general form, for an M-polyfold `A` and a map `p : A → Z` to a Hausdorff paracompact space:

* `MPolyfold.IsDescentMap PA p`: `p` is continuous, open, surjective, locally injective, and
  whenever `p a = p b` there is an sc-smooth `f` near `a` with `f a = b` and `p ∘ f = p` (the
  text's `t ∘ (s|U(φ))⁻¹`).
* `MPolyfold.descChart`: for a chart `φ` of `A` and an open `V ⊆ dom φ` on which `p` is injective,
  the chart `φ ∘ (p|V)⁻¹` of `Z` with domain `p(V)`.
* `MPolyfold.descChart_compatible`, `MPolyfold.descAtlas`, **`MPolyfold.descend`** (the
  M-polyfold structure on `Z`), and **`MPolyfold.isLocalScDiffeo_descend`**: `p : A → Z` is a
  local sc-diffeomorphism for it.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v

namespace MPolyfold

variable {A : Type u} [TopologicalSpace A] [T2Space A] [ParacompactSpace A] (PA : MPolyfold A)
  {Z : Type v} [TopologicalSpace Z] (p : A → Z)

/-- **The hypotheses of the descent** (the situation of the proof of Proposition 9.1.9 (1)). -/
structure IsDescentMap : Prop where
  continuous : Continuous p
  isOpenMap : IsOpenMap p
  surjective : Surjective p
  locInj : ∀ a, ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ InjOn p V
  trans : ∀ a b, p a = p b → ∃ (N : Set A) (f : A → A), IsOpen N ∧ a ∈ N ∧
    PA.IsScSmoothOn PA f N ∧ f a = b ∧ ∀ y ∈ N, p (f y) = p y

variable {PA p}

section Chart

variable [Nonempty A] {φ : MChart A} {V : Set A}

/-- `(p|V)⁻¹ : p(V) → V`. -/
abbrev descInv (p : A → Z) (V : Set A) : Z → A := Function.invFunOn p V

omit [TopologicalSpace A] [T2Space A] [ParacompactSpace A] [TopologicalSpace Z] in
theorem descInv_apply {V : Set A} (hinj : InjOn p V) {a : A} (ha : a ∈ V) :
    descInv p V (p a) = a :=
  hinj.leftInvOn_invFunOn ha

omit [TopologicalSpace A] [T2Space A] [ParacompactSpace A] [TopologicalSpace Z] in
theorem descInv_mem {V : Set A} {z : Z} (hz : z ∈ p '' V) : descInv p V z ∈ V :=
  Function.invFunOn_mem hz

omit [TopologicalSpace A] [T2Space A] [ParacompactSpace A] [TopologicalSpace Z] in
theorem p_descInv {V : Set A} {z : Z} (hz : z ∈ p '' V) : p (descInv p V z) = z :=
  Function.invFunOn_eq hz

omit [T2Space A] [ParacompactSpace A] in
theorem continuousOn_descInv (hp : IsOpenMap p) (hVo : IsOpen V) (hinj : InjOn p V) :
    ContinuousOn (descInv p V) (p '' V) := by
  refine (continuousOn_open_iff (hp V hVo)).2 fun W hW => ?_
  have : p '' V ∩ descInv p V ⁻¹' W = p '' (V ∩ W) := by
    ext z
    constructor
    · rintro ⟨hz, hzW⟩
      exact ⟨descInv p V z, ⟨descInv_mem hz, hzW⟩, p_descInv hz⟩
    · rintro ⟨a, ⟨haV, haW⟩, rfl⟩
      exact ⟨mem_image_of_mem _ haV, by rw [mem_preimage, descInv_apply hinj haV]; exact haW⟩
  rw [this]
  exact hp _ (hVo.inter hW)

variable (p) in
/-- **The descended chart** `φ ∘ (p|V)⁻¹ : p(V) → φ(V)`. -/
def descChart (hp : IsOpenMap p) (hpc : Continuous p) (φ : MChart A) {V : Set A}
    (hV : V ⊆ φ.source) (hVo : IsOpen V) (hinj : InjOn p V) : MChart Z where
  model := ⟨φ.model.E, φ.model.C, φ '' V, φ.isScRetract_image hV hVo⟩
  toPartialEquiv :=
    { toFun := φ ∘ descInv p V
      invFun := p ∘ φ.symm
      source := p '' V
      target := φ '' V
      map_source' := fun z hz => ⟨_, descInv_mem hz, rfl⟩
      map_target' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a, ha, by simp only [Function.comp_apply, φ.symm_apply_apply (hV ha)]⟩
      left_inv' := fun z hz => by
        simp only [Function.comp_apply, φ.symm_apply_apply (hV (descInv_mem hz)), p_descInv hz]
      right_inv' := by
        rintro _ ⟨a, ha, rfl⟩
        simp only [Function.comp_apply, φ.symm_apply_apply (hV ha), descInv_apply hinj ha] }
  isOpen_source := hp V hVo
  target_eq := rfl
  continuousOn_toFun :=
    φ.continuousOn_toFun.comp (continuousOn_descInv hp hVo hinj) fun _ hz => hV (descInv_mem hz)
  continuousOn_invFun :=
    hpc.comp_continuousOn (φ.continuousOn_invFun.mono (φ.image_subset_model hV))

variable (hp : IsOpenMap p) (hpc : Continuous p) (hV : V ⊆ φ.source) (hVo : IsOpen V)
  (hinj : InjOn p V)

omit [T2Space A] [ParacompactSpace A] in
theorem descChart_source : (descChart p hp hpc φ hV hVo hinj).source = p '' V := rfl

omit [T2Space A] [ParacompactSpace A] in
theorem descChart_apply (z : Z) : descChart p hp hpc φ hV hVo hinj z = φ (descInv p V z) := rfl

omit [T2Space A] [ParacompactSpace A] in
theorem descChart_apply_p {a : A} (ha : a ∈ V) : descChart p hp hpc φ hV hVo hinj (p a) = φ a := by
  rw [descChart_apply, descInv_apply hinj ha]

omit [T2Space A] [ParacompactSpace A] in
theorem descChart_symm_apply (w : φ.model.E 0) :
    (descChart p hp hpc φ hV hVo hinj).symm w = p (φ.symm w) := rfl

omit [T2Space A] [ParacompactSpace A] in
theorem descChart_model_O : (descChart p hp hpc φ hV hVo hinj).model.O = φ '' V := rfl

end Chart

/-! ### Compatibility -/

section Compat

variable [Nonempty A] (hd : PA.IsDescentMap p)
include hd

/-- **The descended charts are compatible** (the text: "`f(v) = Ψ_{x'}⁻¹ ∘ Ψ_x(v)`, which implies
that `Ψ_x` and `Ψ_{x'}` are sc-smoothly compatible"): near `φ₁(a)` the transition
`φ₂ ∘ (p|V₂)⁻¹ ∘ p ∘ φ₁⁻¹` is `φ₂ ∘ f ∘ φ₁⁻¹`, `f` the sc-smooth map of `IsDescentMap.trans`. -/
theorem descChart_transition_smooth {φ₁ φ₂ : MChart A} (hφ₁ : PA.IsChart φ₁)
    (hφ₂ : PA.IsChart φ₂) {V₁ V₂ : Set A} (hV₁ : V₁ ⊆ φ₁.source) (hV₁o : IsOpen V₁)
    (hinj₁ : InjOn p V₁) (hV₂ : V₂ ⊆ φ₂.source) (hV₂o : IsOpen V₂) (hinj₂ : InjOn p V₂) :
    let χ₁ := descChart p hd.isOpenMap hd.continuous φ₁ hV₁ hV₁o hinj₁
    let χ₂ := descChart p hd.isOpenMap hd.continuous φ₂ hV₂ hV₂o hinj₂
    IsScSmoothRetractMap χ₁.model.E χ₁.model.C (χ₁.overlap χ₂) χ₂.model.E χ₂.model.C
      (χ₂.overlap χ₁) (χ₁.transition χ₂) := by
  intro χ₁ χ₂
  refine IsScSmoothRetractMap.of_locally (χ₁.transition_mapsTo χ₂) ?_
  rintro _ ⟨z, ⟨hz₁, hz₂⟩, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hz₁
  obtain ⟨b, hb, hab⟩ := hz₂
  obtain ⟨N, f, hNo, haN, hf, hfa, hpf⟩ := hd.trans a b hab.symm
  -- the open piece `N' = N ∩ V₁ ∩ f⁻¹(V₂)`
  set N' := N ∩ V₁ ∩ f ⁻¹' V₂ with hN'def
  have hN'o : IsOpen N' := (hf.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    (hNo.inter hV₁o) hV₂o
  have haN' : a ∈ N' := ⟨⟨haN, ha⟩, by rw [mem_preimage, hfa]; exact hb⟩
  obtain ⟨W, hWo, hW⟩ := φ₁.exists_isOpen_image_eq (fun y hy => hV₁ hy.1.2) hN'o
  refine ⟨W, hWo, ?_, ?_⟩
  · have : φ₁ a ∈ φ₁ '' N' := mem_image_of_mem _ haN'
    rw [hW] at this
    change descChart p _ _ φ₁ hV₁ hV₁o hinj₁ (p a) ∈ W
    rw [descChart_apply_p _ _ _ _ hinj₁ ha]; exact this.2
  -- on `χ₁.overlap χ₂ ∩ W = φ₁(N')` the transition is `φ₂ ∘ f ∘ φ₁⁻¹`
  have hset : χ₁.overlap χ₂ ∩ W = φ₁ '' N' := by
    apply Subset.antisymm
    · rintro w ⟨hw, hwW⟩
      rw [hW]
      exact ⟨φ₁.image_subset_model hV₁ (χ₁.overlap_subset χ₂ hw), hwW⟩
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨⟨p y, ⟨⟨y, hy.1.2, rfl⟩, ⟨f y, hy.2, hpf y hy.1.1⟩⟩,
        descChart_apply_p _ _ _ _ hinj₁ hy.1.2⟩, ?_⟩
      have : φ₁ y ∈ φ₁ '' N' := mem_image_of_mem _ hy
      rw [hW] at this; exact this.2
  rw [hset]
  have hsm := hf.smooth φ₁ φ₂ hφ₁ hφ₂ N' hN'o (fun y hy => ⟨hy.1.1, hV₁ hy.1.2⟩)
    fun y hy => hV₂ hy.2
  refine (hsm.mono_target ?_).congr ?_
  · rintro _ ⟨y, hy, rfl⟩
    change φ₂ (f (φ₁.symm (φ₁ y))) ∈ χ₂.overlap χ₁
    rw [φ₁.symm_apply_apply (hV₁ hy.1.2)]
    refine ⟨p (f y), ⟨⟨f y, hy.2, rfl⟩, ⟨y, hy.1.2, (hpf y hy.1.1).symm⟩⟩, ?_⟩
    exact descChart_apply_p _ _ _ _ hinj₂ hy.2
  · rintro _ ⟨y, hy, rfl⟩
    change φ₂ (f (φ₁.symm (φ₁ y))) = χ₂ (χ₁.symm (φ₁ y))
    rw [φ₁.symm_apply_apply (hV₁ hy.1.2), descChart_symm_apply, φ₁.symm_apply_apply (hV₁ hy.1.2),
      ← hpf y hy.1.1, descChart_apply_p _ _ _ _ hinj₂ hy.2]

theorem descChart_compatible {φ₁ φ₂ : MChart A} (hφ₁ : PA.IsChart φ₁)
    (hφ₂ : PA.IsChart φ₂) {V₁ V₂ : Set A} (hV₁ : V₁ ⊆ φ₁.source) (hV₁o : IsOpen V₁)
    (hinj₁ : InjOn p V₁) (hV₂ : V₂ ⊆ φ₂.source) (hV₂o : IsOpen V₂) (hinj₂ : InjOn p V₂) :
    (descChart p hd.isOpenMap hd.continuous φ₁ hV₁ hV₁o hinj₁).Compatible
      (descChart p hd.isOpenMap hd.continuous φ₂ hV₂ hV₂o hinj₂) :=
  ⟨descChart_transition_smooth hd hφ₁ hφ₂ hV₁ hV₁o hinj₁ hV₂ hV₂o hinj₂,
    descChart_transition_smooth hd hφ₂ hφ₁ hV₂ hV₂o hinj₂ hV₁ hV₁o hinj₁⟩

end Compat

/-! ### The descended M-polyfold -/

section Descend

variable (hd : PA.IsDescentMap p)

/-- The set of descended charts. -/
def descCharts : Set (MChart Z) :=
  {χ | ∃ (_ : Nonempty A) (φ : MChart A) (_ : PA.IsChart φ) (V : Set A) (hV : V ⊆ φ.source)
    (hVo : IsOpen V) (hinj : InjOn p V), χ = descChart p hd.isOpenMap hd.continuous φ hV hVo hinj}

/-- **The atlas of descended charts.** -/
def descAtlas : MAtlas Z where
  charts := descCharts hd
  compatible := by
    rintro _ ⟨_, φ₁, hφ₁, V₁, hV₁, hV₁o, hinj₁, rfl⟩ _ ⟨_, φ₂, hφ₂, V₂, hV₂, hV₂o, hinj₂, rfl⟩
    exact descChart_compatible hd hφ₁ hφ₂ hV₁ hV₁o hinj₁ hV₂ hV₂o hinj₂
  cover z := by
    obtain ⟨a, rfl⟩ := hd.surjective z
    have : Nonempty A := ⟨a⟩
    obtain ⟨V, hVo, haV, hinj⟩ := hd.locInj a
    obtain ⟨φ, hφ, haφ⟩ := PA.exists_isChart_mem_source a
    refine ⟨descChart p hd.isOpenMap hd.continuous φ (inter_subset_right (s := V))
      (hVo.inter φ.isOpen_source) (hinj.mono inter_subset_left),
      ⟨this, φ, hφ, _, _, _, _, rfl⟩, ⟨a, ⟨haV, haφ⟩, rfl⟩⟩

variable [T2Space Z] [ParacompactSpace Z]

/-- **The M-polyfold structure on `Z` descended from `A` along `p`** (the text's "ordinary
M⁺-polyfold charts for the metrizable space `Z`"). -/
def descend : MPolyfold Z := ⟨descAtlas hd⟩

theorem isChart_descChart [Nonempty A] {φ : MChart A} (hφ : PA.IsChart φ) {V : Set A}
    (hV : V ⊆ φ.source) (hVo : IsOpen V) (hinj : InjOn p V) :
    (descend hd).IsChart (descChart p hd.isOpenMap hd.continuous φ hV hVo hinj) :=
  (descend hd).isChart_of_mem ⟨inferInstance, φ, hφ, V, hV, hVo, hinj, rfl⟩

/-- **`p : A → Z` is a local sc-diffeomorphism** for the descended structure: on `V` (with `p|V`
injective) it reads the identity in the charts `φ` and `φ ∘ (p|V)⁻¹`. -/
theorem isLocalScDiffeo_descend : PA.IsLocalScDiffeo (descend hd) p := by
  intro a
  have : Nonempty A := ⟨a⟩
  obtain ⟨V, hVo, haV, hinj⟩ := hd.locInj a
  obtain ⟨φ, hφ, haφ⟩ := PA.exists_isChart_mem_source a
  set V' := V ∩ φ.source with hV'
  have hV'o : IsOpen V' := hVo.inter φ.isOpen_source
  have hinj' : InjOn p V' := hinj.mono inter_subset_left
  have hV'φ : V' ⊆ φ.source := inter_subset_right
  set χ := descChart p hd.isOpenMap hd.continuous φ hV'φ hV'o hinj'
  have hχ := isChart_descChart hd hφ hV'φ hV'o hinj'
  refine ⟨V', p '' V', descInv p V', ⟨haV, haφ⟩, ⟨?_, ?_, fun y hy => mem_image_of_mem _ hy,
    fun z hz => descInv_mem hz, fun y hy => descInv_apply hinj' hy, fun z hz => p_descInv hz⟩⟩
  · refine IsScSmoothOn.of_exists_charts hV'o hd.continuous.continuousOn fun y hy => ?_
    refine ⟨φ, χ, V', hφ, hχ, hV'o, hy, fun w hw => ⟨hw, hV'φ hw⟩,
      fun w hw => mem_image_of_mem _ hw, ?_⟩
    change IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V') φ.model.E φ.model.C (φ '' V') _
    refine (isScSmoothRetractMap_id (φ '' V')).congr ?_
    rintro _ ⟨w, hw, rfl⟩
    change φ w = χ (p (φ.symm (φ w)))
    rw [φ.symm_apply_apply (hV'φ hw), descChart_apply_p _ _ _ _ hinj' hw]
  · refine IsScSmoothOn.of_exists_charts (hd.isOpenMap _ hV'o)
      (continuousOn_descInv hd.isOpenMap hV'o hinj') fun z hz => ?_
    refine ⟨χ, φ, p '' V', hχ, hφ, hd.isOpenMap _ hV'o, hz, fun w hw => ⟨hw, hw⟩,
      fun w hw => hV'φ (descInv_mem hw), ?_⟩
    have himg : χ '' (p '' V') = χ.model.O := χ.image_source
    rw [himg]
    change IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V') φ.model.E φ.model.C φ.model.O _
    refine ((isScSmoothRetractMap_id (φ '' V')).mono_target
      (φ.image_subset_model hV'φ)).congr ?_
    rintro _ ⟨w, hw, rfl⟩
    change φ w = φ (descInv p V' (p (φ.symm (φ w))))
    rw [φ.symm_apply_apply (hV'φ hw), descInv_apply hinj' hw]

end Descend

end MPolyfold

end Polyfold
