import Polyfold.Chapter14.BoundaryPull
import Polyfold.Chapter13.Commensurable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.5, p. 672:
**Lemma 14.5.2** (the decomposition `Λ̃ = ⊕_a Λ̃_a` over `∂X`) and **Remark 14.5.3** (`Λ_a` is
determined by its sections at `a`) (2017: Lemma 14.11, Remark 14.7).

# Commensurable sums of structured sc⁺-multisections over the boundary

## The text, paraphrased

(p. 672) With `β_a : X → [0, 1]` sc-smooth functors as in Lemma 14.5.1 (supported in
`π⁻¹(π(V̂_a))`, locally finite, `∑_a β_a = 1` on `∂X`), and a structured `Λ̃ = (Λ, 𝒰⁰, S⁰, τ⁰)`
over `∂X`, put `Λ_a = (β_a|∂X) ⊙ Λ`, structured by the same `(𝒰⁰, I, τ⁰)` and the sections
`s^{a,x}_i = β_a · s^{0x}_i`.  (Lemma 14.5.2) `Λ̃` is the commensurable locally finite sum of
the `Λ̃_a = (Λ_a, 𝒰⁰, S^a, τ⁰)` (Definition 13.4.5 over `∂X`).  (Remark 14.5.3) `Λ_a` is
completely determined by the sections `(β_a · s^{0a}_i)` on `U⁰(a)`, even by their restriction
to `V_a`, given `τ⁰`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* Sections satisfying (1) of Definition 14.1.3 (`IsFaceScPlusSectionOn`) are closed under
  multiplication by sc-smooth functions (`IsFaceScPlusSectionOn.sectionSmul`), sums
  (`sectionAdd`, `isFaceScPlusSectionOn_sectionSum`), and the condition is local
  (`isFaceScPlusSectionOn_of_locally`).
* `BoundaryCommData A`: a common choice `c = (𝒰, I, τ)` of the data of Definition 14.1.7 that do
  not involve sections (the boundary form of Definition 13.4.5 (1)); `BoundaryCommData.Over c Λ`:
  sections over `c` for `Λ`; `Over.toTuple`: the structured tuple `(Λ, 𝒰, S, τ)` over `∂X`;
  `BoundaryCommData.ofTuple`, `Over.ofTuple`: every structured tuple over `∂X` is of this form.
* `BoundaryCommData.Over.lfSum`: **the commensurable sum of a locally finite family over `∂X`**,
  with the sections `sˣᵢ = ∑ᶠⱼ s^{j,x}ᵢ` (`definition_13_4_5_boundary`).
* `BoundaryCommData.smulOver`: the data `(β·s^{0x}_i)` over the data of a tuple, for
  `β ⊙ Λ` (Lemma 13.2.11 over `∂X`).
* **`lemma_14_5_2`**: for a locally finite family `(β_a)` of sc-smooth functors with
  `∑ᶠ_a β_a = 1` on `∂X`, the commensurable sum of the `Λ̃_a` has the sections of `Λ̃`, the
  functor `Λ` over `∂X`, and is equivalent to `Λ̃` (Definition 14.1.7).
* **`remark_14_5_3`**: data over `c` are determined by their sections at one point `a` on a set
  `V ⊆ U(a)` and their vanishing off `π⁻¹(π(V))` (`Over.s_eq_of_eqOn`); in particular
  `Λ_a` is determined by `(β_a · s^{0a}_i)|V` when `supp β_a ⊆ π⁻¹(π(V))`.

## Readings

* "Locally finite" for a family over `∂X` (`IsLocallyFiniteBoundaryFamily`) is Definition
  13.2.12 read over `∂X`: every point of `∂X` has an open neighbourhood over whose boundary
  points only finitely many `Λⱼ` charge a non-zero point.  The `β_a` of Lemma 14.5.1 (2) are
  locally finite in the sense that only finitely many are non-zero near each point.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### Condition (1) of Definition 14.1.3 under products, sums and localization -/

section FaceAlgebra

/-- `t(φ) ∈ ∂X` iff `s(φ) ∈ ∂X` (morphisms preserve the degeneracy index). -/
theorem tgt_mem_boundary_iff_src (φ : A.Mor) :
    A.X.tgt φ ∈ A.X.PObj.boundary ↔ A.X.src φ ∈ A.X.PObj.boundary := by
  change 1 ≤ A.X.PObj.degIndex (A.X.tgt φ) ↔ 1 ≤ A.X.PObj.degIndex (A.X.src φ)
  rw [← A.X.degIndex_tgt, A.X.degIndex_src]

/-- The value of `f·s` in the chart of a strong bundle chart. -/
theorem chart_sectionSmul_snd {s : A.Obj → A.W} (hs : IsSection A.P s) {f : A.Obj → ℝ}
    (c : StrongBundleChart A.X.PObj A.P) {y : A.Obj} (hy : y ∈ c.φ.source) :
    (c (Polyfold.sectionSmul A.P f s y)).2 = f y • (c (s y)).2 := by
  rw [sectionSmul_apply hs]
  exact (c.fiber_linear y hy).map_smul (f y) ⟨s y, hs y⟩

/-- The value of `s₁ + s₂` in the chart of a strong bundle chart. -/
theorem chart_sectionAdd_snd {s₁ s₂ : A.Obj → A.W} (hs₁ : IsSection A.P s₁)
    (hs₂ : IsSection A.P s₂) (c : StrongBundleChart A.X.PObj A.P) {y : A.Obj}
    (hy : y ∈ c.φ.source) :
    (c (Polyfold.sectionAdd A.P s₁ s₂ y)).2 = (c (s₁ y)).2 + (c (s₂ y)).2 := by
  rw [sectionAdd_apply hs₁ hs₂]; exact c.snd_add hy _ _

/-- A section `s` with `s(y) ∈ W_{0,1}` has its fibre component in `F₁` in every compatible
chart around `y`. -/
theorem mem_range_of_mem_oneSet {s : A.Obj → A.W} (hs : IsSection A.P s)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) {y : A.Obj} (hy : y ∈ c.φ.source)
    (h1 : s y ∈ A.B.oneSet) : (c (s y)).2 ∈ range (c.F.toBase 1) := by
  refine (mem_oneSet_iff_of_isChart hc ?_).1 h1
  rw [c.source_eq, mem_preimage, hs y]; exact hy

/-- `W_{0,1}` is closed under multiplication by scalars (read in a chart of the atlas). -/
theorem smul_mem_oneSet {s : A.Obj → A.W} (hs : IsSection A.P s) {f : A.Obj → ℝ} {y : A.Obj}
    (h1 : s y ∈ A.B.oneSet) : Polyfold.sectionSmul A.P f s y ∈ A.B.oneSet := by
  obtain ⟨c, hc, hyc⟩ := exists_chart_mem_source A y
  have hsrc : Polyfold.sectionSmul A.P f s y ∈ c.toPartialEquiv.source := by
    rw [c.source_eq, mem_preimage, hs.sectionSmul]; exact hyc
  refine (A.B.mem_oneSet_iff hc hsrc).2 ?_
  rw [chart_sectionSmul_snd hs c hyc]
  obtain ⟨a, ha⟩ := mem_range_of_mem_oneSet hs (A.B.isChart_of_mem hc) hyc h1
  exact ⟨f y • a, by rw [map_smul, ha]⟩

/-- `W_{0,1}` is closed under fibrewise sums. -/
theorem add_mem_oneSet {s₁ s₂ : A.Obj → A.W} (hs₁ : IsSection A.P s₁) (hs₂ : IsSection A.P s₂)
    {y : A.Obj} (h₁ : s₁ y ∈ A.B.oneSet) (h₂ : s₂ y ∈ A.B.oneSet) :
    Polyfold.sectionAdd A.P s₁ s₂ y ∈ A.B.oneSet := by
  obtain ⟨c, hc, hyc⟩ := exists_chart_mem_source A y
  have hsrc : Polyfold.sectionAdd A.P s₁ s₂ y ∈ c.toPartialEquiv.source := by
    rw [c.source_eq, mem_preimage, hs₁.sectionAdd hs₂]; exact hyc
  refine (A.B.mem_oneSet_iff hc hsrc).2 ?_
  rw [chart_sectionAdd_snd hs₁ hs₂ c hyc]
  obtain ⟨a, ha⟩ := mem_range_of_mem_oneSet hs₁ (A.B.isChart_of_mem hc) hyc h₁
  obtain ⟨b, hb⟩ := mem_range_of_mem_oneSet hs₂ (A.B.isChart_of_mem hc) hyc h₂
  exact ⟨a + b, by rw [map_add, ha, hb]⟩

/-- The open set of the model of a chart over an open set `O` of `X`: an open `N'` of the
model with `N' ∩ O_c = φ(O ∩ dom φ)`-preimage, containing `φ(x)` for `x ∈ O ∩ dom φ`. -/
theorem exists_model_open (c : StrongBundleChart A.X.PObj A.P) {O : Set A.Obj} (hO : IsOpen O)
    {x : A.Obj} (hxO : x ∈ O) (hx : x ∈ c.φ.source) :
    ∃ N' : Set (c.φ.model.E 0), IsOpen N' ∧ c.φ x ∈ N' ∧
      ∀ z ∈ c.φ.model.O ∩ N', c.φ.symm z ∈ O := by
  obtain ⟨N', hN', hN'eq⟩ := continuousOn_iff'.1 c.φ.continuousOn_invFun O hO
  refine ⟨N', hN', ?_, fun z hz => ?_⟩
  · have : c.φ x ∈ c.φ.symm ⁻¹' O ∩ c.φ.model.O :=
      ⟨by rw [mem_preimage, c.φ.symm_apply_apply hx]; exact hxO, c.φ.mapsTo_model x hx⟩
    rw [hN'eq] at this; exact this.1
  · have : z ∈ N' ∩ c.φ.model.O := ⟨hz.2, hz.1⟩
    rw [← hN'eq] at this; exact this.1

variable {U O : Set A.Obj}

/-- **Products with sc-smooth functions** preserve (1) of Definition 14.1.3: for `U` open in
`∂X` (`U ⊆ O`, `O ∩ ∂X ⊆ U`, `O` open), a global section `s` sc⁺ on every local face at the
points of `U`, and `f : X → ℝ` sc-smooth, `f·s` is sc⁺ on every local face at the points of `U`
(in a tame chart, `(f·s)^ = (f ∘ φ⁻¹)·ŝ` on the face germ, and the product rule). -/
theorem IsFaceScPlusSectionOn.sectionSmul (hO : IsOpen O) (hUO : U ⊆ O)
    (hOU : O ∩ A.X.PObj.boundary ⊆ U) {s : A.Obj → A.W} (hs : IsSection A.P s)
    (h : IsFaceScPlusSectionOn A s U) {f : A.Obj → ℝ}
    (hf : A.X.PObj.IsScSmoothMap realPolyfold f) :
    IsFaceScPlusSectionOn A (Polyfold.sectionSmul A.P f s) U := by
  refine ⟨fun x hx => ⟨hs.sectionSmul x, smul_mem_oneSet hs (h.1 x hx).2⟩,
    fun c hc n W T hT x hx i hi => ?_⟩
  obtain ⟨V, hV, hxV, hret, hsec⟩ := h.2 c hc n W T hT x hx i hi
  set L := localRepOne c s
  set G : c.φ.model.E 0 → (c.φ.model.E.prod c.F.shift) 0 :=
    fun z => ((L z).1, f (c.φ.symm z) • (L z).2) with hG
  -- `G` is an sc⁺-section on the face germ
  have hQO : c.φ.model.O ∩ V ∩ coordHyper T i ⊆ c.φ.model.O := fun z hz => hz.1.1
  have hf1 := (hf.real_chart c.isChart).mono_source c.φ.model.isScRetract hQO
  have hGsec : IsScPlusSection c.φ.model.C (c.φ.model.O ∩ V ∩ coordHyper T i) c.K G := by
    refine ⟨fun z hz => hsec.fst_eq z hz, ⟨fun z hz => ?_, fun R hR => ?_⟩⟩
    · exact c.smul_mem_strongShiftOne (hsec.isScSmooth.mapsTo hz) _
    · have hUR := R.isScDomain
      have h1 := hsec.isScSmooth.comp_isScSmooth R hR
      have h2 := (hf1.comp_isScSmooth R hR).smul hUR (h1.snd hUR)
      exact ((h1.fst hUR).scPair hUR h2).congr hUR fun _ _ => rfl
  have hface : IsScPlusOnFaceNear T c.φ.model.C c.φ.model.O c.K G (c.φ x) i :=
    ⟨V, hV, hxV, hret, hGsec⟩
  -- on the face points over `O`, `G` is the representative of `f·s`
  obtain ⟨N', hN', hxN', hN'O⟩ := exists_model_open c hO (hUO hx.1) hx.2
  refine IsScPlusOnFaceNear.congr_open hface hN' hxN' fun z hz => ?_
  have hzO : z ∈ c.φ.model.O := hz.1.1
  have hzs : c.φ.symm z ∈ c.φ.source := c.φ.symm_mapsTo hzO
  have hzU : c.φ.symm z ∈ U :=
    hOU ⟨hN'O z ⟨hzO, hz.1.2⟩, symm_mem_boundary c hc hT hzO hz.2⟩
  have hr := mem_range_of_mem_oneSet hs hc.isChart hzs (h.1 _ hzU).2
  refine Prod.ext ?_ (c.F.toBase_injective 1 ?_)
  · change (L z).1 = (c (Polyfold.sectionSmul A.P f s (c.φ.symm z))).1
    rw [localRepOne_fst hs hzO, c.fst_apply (by rw [hs.sectionSmul]; exact hzs),
      hs.sectionSmul, c.φ.apply_symm_apply hzO]
  · change c.F.toBase 1 (f (c.φ.symm z) • (L z).2) =
      c.F.toBase 1 (Function.invFun (c.F.toBase 1)
        (c (Polyfold.sectionSmul A.P f s (c.φ.symm z))).2)
    rw [map_smul, toBase_localRepOne_snd_of_mem c hr, chart_sectionSmul_snd hs c hzs]
    obtain ⟨a, ha⟩ := hr
    exact (Function.invFun_eq ⟨f (c.φ.symm z) • a, by rw [map_smul, ha]⟩).symm

/-- **Sums** preserve (1) of Definition 14.1.3 (for `U` open in `∂X`). -/
theorem IsFaceScPlusSectionOn.sectionAdd (hO : IsOpen O) (hUO : U ⊆ O)
    (hOU : O ∩ A.X.PObj.boundary ⊆ U) {s₁ s₂ : A.Obj → A.W} (hs₁ : IsSection A.P s₁)
    (hs₂ : IsSection A.P s₂) (h₁ : IsFaceScPlusSectionOn A s₁ U)
    (h₂ : IsFaceScPlusSectionOn A s₂ U) :
    IsFaceScPlusSectionOn A (Polyfold.sectionAdd A.P s₁ s₂) U := by
  refine ⟨fun x hx => ⟨hs₁.sectionAdd hs₂ x, add_mem_oneSet hs₁ hs₂ (h₁.1 x hx).2
    (h₂.1 x hx).2⟩, fun c hc n W T hT x hx i hi => ?_⟩
  obtain ⟨V₁, hV₁, hxV₁, hret₁, hsec₁⟩ := h₁.2 c hc n W T hT x hx i hi
  obtain ⟨V₂, hV₂, hxV₂, hret₂, hsec₂⟩ := h₂.2 c hc n W T hT x hx i hi
  set L₁ := localRepOne c s₁
  set L₂ := localRepOne c s₂
  set G : c.φ.model.E 0 → (c.φ.model.E.prod c.F.shift) 0 :=
    fun z => ((L₁ z).1, (L₁ z).2 + (L₂ z).2) with hG
  set Q := c.φ.model.O ∩ (V₁ ∩ V₂) ∩ coordHyper T i
  have hQ₁ : Q = (c.φ.model.O ∩ V₁ ∩ coordHyper T i) ∩ V₂ := by
    ext z; simp only [Q, mem_inter_iff]; tauto
  have hQ₂ : Q = (c.φ.model.O ∩ V₂ ∩ coordHyper T i) ∩ V₁ := by
    ext z; simp only [Q, mem_inter_iff]; tauto
  have hret : IsScRetract c.φ.model.E c.φ.model.C Q := by
    rw [hQ₁]; exact proposition_2_3_1_one hret₁ hV₂
  have hm₁ : IsScSmoothRetractMap c.φ.model.E c.φ.model.C Q (c.φ.model.E.prod c.F.shift)
      (c.φ.model.C ×ˢ univ) (strongShiftOne c.K) L₁ :=
    hsec₁.isScSmooth.mono_source hret₁ (by rw [hQ₁]; exact inter_subset_left)
  have hm₂ : IsScSmoothRetractMap c.φ.model.E c.φ.model.C Q (c.φ.model.E.prod c.F.shift)
      (c.φ.model.C ×ˢ univ) (strongShiftOne c.K) L₂ :=
    hsec₂.isScSmooth.mono_source hret₂ (by rw [hQ₂]; exact inter_subset_left)
  have hGsec : IsScPlusSection c.φ.model.C Q c.K G := by
    refine ⟨fun z hz => hsec₁.fst_eq z (by rw [hQ₁] at hz; exact hz.1), ⟨fun z hz => ?_,
      fun R hR => ?_⟩⟩
    · have hz₁ : z ∈ c.φ.model.O ∩ V₁ ∩ coordHyper T i := by rw [hQ₁] at hz; exact hz.1
      have hz₂ : z ∈ c.φ.model.O ∩ V₂ ∩ coordHyper T i := by rw [hQ₂] at hz; exact hz.1
      have ha := hm₁.mapsTo hz
      have hb := hm₂.mapsTo hz
      have e1 : L₁ z = (z, (L₁ z).2) := Prod.ext (hsec₁.fst_eq z hz₁) rfl
      have e2 : L₂ z = (z, (L₂ z).2) := Prod.ext (hsec₂.fst_eq z hz₂) rfl
      rw [e1] at ha; rw [e2] at hb
      change ((L₁ z).1, (L₁ z).2 + (L₂ z).2) ∈ strongShiftOne c.K
      rw [hsec₁.fst_eq z hz₁]
      exact c.add_mem_strongShiftOne ha hb
    · have hUR := R.isScDomain
      have g₁ := hm₁.comp_isScSmooth R hR
      have g₂ := hm₂.comp_isScSmooth R hR
      exact ((g₁.fst hUR).scPair hUR ((g₁.snd hUR).add hUR (g₂.snd hUR))).congr hUR
        fun _ _ => rfl
  have hface : IsScPlusOnFaceNear T c.φ.model.C c.φ.model.O c.K G (c.φ x) i :=
    ⟨V₁ ∩ V₂, hV₁.inter hV₂, ⟨hxV₁, hxV₂⟩, hret, hGsec⟩
  obtain ⟨N', hN', hxN', hN'O⟩ := exists_model_open c hO (hUO hx.1) hx.2
  refine IsScPlusOnFaceNear.congr_open hface hN' hxN' fun z hz => ?_
  have hzO : z ∈ c.φ.model.O := hz.1.1
  have hzs : c.φ.symm z ∈ c.φ.source := c.φ.symm_mapsTo hzO
  have hzU : c.φ.symm z ∈ U :=
    hOU ⟨hN'O z ⟨hzO, hz.1.2⟩, symm_mem_boundary c hc hT hzO hz.2⟩
  have hr₁ := mem_range_of_mem_oneSet hs₁ hc.isChart hzs (h₁.1 _ hzU).2
  have hr₂ := mem_range_of_mem_oneSet hs₂ hc.isChart hzs (h₂.1 _ hzU).2
  refine Prod.ext ?_ (c.F.toBase_injective 1 ?_)
  · change (L₁ z).1 = (c (Polyfold.sectionAdd A.P s₁ s₂ (c.φ.symm z))).1
    rw [localRepOne_fst hs₁ hzO, c.fst_apply (by rw [hs₁.sectionAdd hs₂]; exact hzs),
      hs₁.sectionAdd hs₂, c.φ.apply_symm_apply hzO]
  · change c.F.toBase 1 ((L₁ z).2 + (L₂ z).2) =
      c.F.toBase 1 (Function.invFun (c.F.toBase 1)
        (c (Polyfold.sectionAdd A.P s₁ s₂ (c.φ.symm z))).2)
    rw [map_add, toBase_localRepOne_snd_of_mem c hr₁, toBase_localRepOne_snd_of_mem c hr₂,
      chart_sectionAdd_snd hs₁ hs₂ c hzs]
    obtain ⟨a, ha⟩ := hr₁
    obtain ⟨b, hb⟩ := hr₂
    exact (Function.invFun_eq ⟨a + b, by rw [map_add, ha, hb]⟩).symm

/-- **Finite sums** preserve (1) of Definition 14.1.3 (for `U` open in `∂X`). -/
theorem isFaceScPlusSectionOn_sectionSum (hO : IsOpen O) (hUO : U ⊆ O)
    (hOU : O ∩ A.X.PObj.boundary ⊆ U) (hUb : U ⊆ A.X.PObj.boundary) {ι : Type*}
    (I : Finset ι) {s : ι → A.Obj → A.W} (hs : ∀ i, IsSection A.P (s i))
    (h : ∀ i, IsFaceScPlusSectionOn A (s i) U) :
    IsFaceScPlusSectionOn A (sectionSum A.P I s) U := by
  induction I using Finset.induction_on with
  | empty =>
    have : sectionSum A.P (∅ : Finset ι) s = fiberZero A.P := funext fun x => by
      rw [sectionSum_apply hs, Finset.sum_empty]; rfl
    rw [this]; exact isFaceScPlusSectionOn_fiberZero hUb
  | insert a I ha ih =>
    have hI : IsSection A.P (sectionSum A.P I s) := fun x => by
      rw [sectionSum_apply hs]
      exact ((∑ i ∈ I, (⟨s i x, hs i x⟩ : A.P ⁻¹' {x})) : A.P ⁻¹' {x}).2
    have hfib : ∀ x, (⟨sectionSum A.P I s x, hI x⟩ : A.P ⁻¹' {x}) =
        ∑ i ∈ I, (⟨s i x, hs i x⟩ : A.P ⁻¹' {x}) :=
      fun x => Subtype.ext (sectionSum_apply (I := I) hs x)
    have : sectionSum A.P (insert a I) s = Polyfold.sectionAdd A.P (s a) (sectionSum A.P I s) :=
      funext fun x => by
        rw [sectionAdd_apply (hs a) hI, sectionSum_apply (I := insert a I) hs,
          Finset.sum_insert ha, hfib]
    rw [this]; exact (h a).sectionAdd hO hUO hOU (hs a) hI ih

/-- **(1) of Definition 14.1.3 is local**: if near every `y ∈ U ⊆ ∂X` the section `s` agrees on
the boundary points of an open `N ∋ y` with a section `σ` satisfying (1) at `y`, then `s`
satisfies (1) on `U`. -/
theorem isFaceScPlusSectionOn_of_locally {s : A.Obj → A.W} (hUb : U ⊆ A.X.PObj.boundary)
    (h : ∀ y ∈ U, ∃ σ : A.Obj → A.W, ∃ N : Set A.Obj, IsOpen N ∧ y ∈ N ∧
      IsFaceScPlusSectionOn A σ {y} ∧ EqOn σ s (N ∩ A.X.PObj.boundary)) :
    IsFaceScPlusSectionOn A s U := by
  have hy : ∀ y ∈ U, IsFaceScPlusSectionOn A s {y} := fun y hyU => by
    obtain ⟨σ, N, hN, hyN, hσ, heq⟩ := h y hyU
    exact hσ.congr_of_eqOn_boundary hN (singleton_subset_iff.2 hyN) (singleton_subset_iff.2 (hUb hyU)) heq
  exact ⟨fun x hx => (hy x hx).1 x rfl,
    fun c hc n W T hT x hx i hi => (hy x hx.1).2 c hc n W T hT x ⟨rfl, hx.2⟩ i hi⟩

/-- A section satisfying (1) on `U` may be replaced by the global section equal to it on `U` and
zero elsewhere. -/
theorem IsFaceScPlusSectionOn.extendZero (hO : IsOpen O) (hUO : U ⊆ O)
    (hOU : O ∩ A.X.PObj.boundary ⊆ U) (hUb : U ⊆ A.X.PObj.boundary) {s : A.Obj → A.W}
    (h : IsFaceScPlusSectionOn A s U) :
    IsFaceScPlusSectionOn A (SBLocalization.extendZero U s) U :=
  h.congr_of_eqOn_boundary hO hUO hUb fun _ hy => extendZero_eqOn (fun z hz => (h.1 z hz).1) (hOU hy)

end FaceAlgebra

/-! ### Common data over the boundary (Definition 13.4.5 (1) for Definition 14.1.7) -/

/-- **A choice `c` of common data over `∂X`**: a good system `𝒰` for `∂X` (Definition 14.1.5),
non-empty index types `I_x` with `G_x`-actions, and maps `τ_{x,x'}` with the conditions (2),
(2)(a)–(c) of Definition 14.1.7, which do not involve sections. -/
structure BoundaryCommData (A : SEP.{u}) where
  /-- The good system `𝒰` for `∂X`. -/
  𝒰 : A.X.BoundaryGoodSystem
  /-- The index sets `I_x`. -/
  I : A.X.PObj.boundary → Type u
  [fintype : ∀ x, Fintype (I x)]
  [mulAction : ∀ x : A.X.PObj.boundary, MulAction (A.X.Isotropy x) (I x)]
  [nonempty : ∀ x, Nonempty (I x)]
  /-- The maps `τ_{x,x'}`. -/
  τ : ∀ x x' : A.X.PObj.boundary, A.Mor → IndexCorr (I x) (I x')
  locallyConstant : ∀ x x', ∀ φ ∈ 𝒰.mor x x', ∀ᶠ ψ in 𝓝[𝒰.mor x x'] φ, τ x x' ψ = τ x x' φ
  finite : ∀ x x', (τ x x' '' 𝒰.mor x x').Finite
  swap : ∀ x x', ∀ φ ∈ 𝒰.mor x x', τ x' x (A.X.inv φ) = (τ x x' φ).swap
  diag : ∀ (x : A.X.PObj.boundary) (g : A.X.Isotropy x), ∀ z ∈ 𝒰.U x,
    τ x x ((𝒰.nbhd x).rep.Γ g z) = IndexCorr.ofPerm (α := I x) g
  biact : ∀ x x', ∀ φ ∈ 𝒰.mor x x', ∀ (g' : A.X.Isotropy x') (g : A.X.Isotropy x),
    τ x x' (EpGroupoid.biact (𝒰.nbhd x) (𝒰.nbhd x') g' φ g) = IndexCorr.biact g' (τ x x' φ) g

attribute [instance] BoundaryCommData.fintype BoundaryCommData.mulAction
  BoundaryCommData.nonempty

namespace BoundaryCommData

variable (c : BoundaryCommData A)

/-- The identity (4) of Definition 14.1.7 along `φ`: `s^{x'}_j(t(φ)) = μ(φ, sˣᵢ(s(φ)))`. -/
def Compat (s : ∀ x, c.I x → A.Obj → A.W) {x x' : A.X.PObj.boundary} (φ : A.Mor) (i : c.I x)
    (j : c.I x') : Prop :=
  s x' j (A.X.tgt φ) = fibAct φ (s x i (A.X.src φ))

/-- **Sections over `c`**: sections `(sˣᵢ)_{i ∈ I_x}` on every `U(x)` with (1) and (2) of
Definition 14.1.3 for which `τ` satisfies (4) of Definition 14.1.7. -/
structure Sections where
  /-- The sections `sˣᵢ`. -/
  s : ∀ x, c.I x → A.Obj → A.W
  isFaceScPlus : ∀ x i, IsFaceScPlusSectionOn A (s x i) (c.𝒰.U x)
  equivariant : ∀ (x : A.X.PObj.boundary) (g : A.X.Isotropy x) (i : c.I x), ∀ y ∈ c.𝒰.U x,
    s x (g • i) ((c.𝒰.nbhd x).rep.Φ g y) = fibAct ((c.𝒰.nbhd x).rep.Γ g y) (s x i y)
  compat : ∀ x x', ∀ φ ∈ c.𝒰.mor x x', (c.τ x x' φ).Sat fun i j => c.Compat s φ i j

/-- `|I_x|⁻¹·#{i ∈ I_x | sˣᵢ(P(w)) = w}`. -/
def countAt (s : ∀ x, c.I x → A.Obj → A.W) (x : A.X.PObj.boundary) (w : A.W) : ℚ≥0 :=
  (Fintype.card (c.I x) : ℚ≥0)⁻¹ * ((Finset.univ.filter fun i => s x i (A.P w) = w).card : ℚ≥0)

/-- **The functor of the counting formula over `∂X`**: `Λ(w) = |I_x|⁻¹·#{i | sˣᵢ(P(w)) = w}` at
`x = P(w) ∈ ∂X` (and `0` off `W|∂X`, where nothing is asked). -/
def sumMult (s : ∀ x, c.I x → A.Obj → A.W) (w : A.W) : ℚ≥0 :=
  if h : A.P w ∈ A.X.PObj.boundary then c.countAt s ⟨A.P w, h⟩ w else 0

/-- **Sections over `c` for `Λ`**: the counting formula (3) of Definition 14.1.3 holds on every
`U(x)`; these are the data of a structured `(Λ, 𝒰, S, τ)` over `∂X` with the common `c`. -/
structure Over (Λ : A.W → ℚ≥0) extends c.Sections where
  rep : ∀ x w, A.P w ∈ c.𝒰.U x → Λ w = c.countAt s x w

variable {c}

namespace Sections

variable (S : c.Sections)

theorem P_s {x : A.X.PObj.boundary} (i : c.I x) {y : A.Obj} (hy : y ∈ c.𝒰.U x) :
    A.P (S.s x i y) = y :=
  ((S.isFaceScPlus x i).1 y hy).1

/-- **Count transport** along `φ ∈ 𝒰(x, x')`: `countAt x v = countAt x' (μ(φ, v))`. -/
theorem countAt_fibAct {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ c.𝒰.mor x x')
    {v : A.W} (hv : A.P v = A.X.src φ) :
    c.countAt S.s x v = c.countAt S.s x' (fibAct φ v) := by
  unfold countAt
  rw [P_fibAct hv, hv]
  refine IndexCorr.count_eq_of_sat (s := fun i => S.s x i (A.X.src φ))
    (s' := fun j => S.s x' j (A.X.tgt φ)) (f := fibAct φ) (T := {w | A.P w = A.X.src φ})
    (fun a ha b hb e => ?_) (fun i => S.P_s i hφ.1) (S.compat x x' φ hφ) hv
  rw [fibAct_of ha, fibAct_of hb] at e
  exact EpStrongBundle.μ_injective_snd A.E ha hb e

/-- **The count does not depend on `x`**: `countAt x w = sumMult w` for `P(w) ∈ U(x)`. -/
theorem countAt_eq {x : A.X.PObj.boundary} {w : A.W} (hw : A.P w ∈ c.𝒰.U x) :
    c.countAt S.s x w = c.sumMult S.s w := by
  have hb : A.P w ∈ A.X.PObj.boundary := c.𝒰.U_subset_boundary x hw
  have hmor : A.X.unit (A.P w) ∈ c.𝒰.mor x ⟨A.P w, hb⟩ :=
    ⟨by rw [A.X.src_unit]; exact hw, by rw [A.X.tgt_unit]; exact c.𝒰.mem_U _⟩
  have h := S.countAt_fibAct hmor (v := w) (A.X.src_unit _).symm
  rw [fibAct_unit rfl] at h
  rw [h, sumMult, dif_pos hb]

/-- The symmetric structure on `U(x)` (Definition 14.1.3) of the counting functor. -/
def sym (x : A.X.PObj.boundary) : BoundarySymmetricStructure A (c.sumMult S.s) (c.𝒰.nbhd x) where
  I := c.I x
  s := S.s x
  isFaceScPlus := S.isFaceScPlus x
  equivariant := S.equivariant x
  rep _ hw := (S.countAt_eq hw).symm

/-- The counting functor is a functor on `W|∂X`. -/
theorem isBoundaryWFunctor_sumMult : IsBoundaryWFunctor A (c.sumMult S.s) := by
  rintro ⟨⟨φ, w⟩, hq⟩ hφ
  have hq' : A.P w = A.X.src φ := hq
  have htb : A.X.tgt φ ∈ A.X.PObj.boundary := (tgt_mem_boundary_iff_src φ).2 hφ
  have hmor : φ ∈ c.𝒰.mor ⟨A.X.src φ, hφ⟩ ⟨A.X.tgt φ, htb⟩ := ⟨c.𝒰.mem_U _, c.𝒰.mem_U _⟩
  have h := S.countAt_fibAct hmor hq'
  rw [fibAct_of hq'] at h
  have h₁ : A.P w ∈ c.𝒰.U ⟨A.X.src φ, hφ⟩ := by rw [hq']; exact c.𝒰.mem_U _
  have h₂ : A.P (A.E.μ ⟨(φ, w), hq⟩) ∈ c.𝒰.U ⟨A.X.tgt φ, htb⟩ := by
    rw [A.E.P_μ]; exact c.𝒰.mem_U _
  change c.sumMult S.s (A.E.μ ⟨(φ, w), hq⟩) = c.sumMult S.s w
  rw [← S.countAt_eq h₁, ← S.countAt_eq h₂, h]

/-- **The counting functor is an sc⁺-multisection over `∂X`** (Definition 14.1.3). -/
theorem isBoundaryScPlusMultisection_sumMult :
    IsBoundaryScPlusMultisection A (c.sumMult S.s) :=
  ⟨S.isBoundaryWFunctor_sumMult, fun x hx =>
    ⟨c.𝒰.nbhd ⟨x, hx⟩, c.𝒰.isGood _, ⟨S.sym ⟨x, hx⟩⟩⟩⟩

/-- The sections over `c` are sections over `c` for the functor they define. -/
def toOver : c.Over (c.sumMult S.s) :=
  { S with rep := fun _ _ hw => (S.countAt_eq hw).symm }

end Sections

namespace Over

variable {Λ : A.W → ℚ≥0} (o : c.Over Λ)

/-- **Over `∂X` a functor with sections over `c` is the counting functor.** -/
theorem eq_sumMult {w : A.W} (hw : A.P w ∈ A.X.PObj.boundary) : Λ w = c.sumMult o.s w := by
  rw [o.rep ⟨A.P w, hw⟩ w (c.𝒰.mem_U _), o.toSections.countAt_eq (c.𝒰.mem_U _)]

/-- The symmetric structure on `U(x)` (Definition 14.1.3). -/
def sym (x : A.X.PObj.boundary) : BoundarySymmetricStructure A Λ (c.𝒰.nbhd x) where
  I := c.I x
  s := o.s x
  isFaceScPlus := o.isFaceScPlus x
  equivariant := o.equivariant x
  rep := o.rep x

include o in
theorem isBoundaryScPlusMultisection : IsBoundaryScPlusMultisection A Λ := by
  refine ⟨fun q hq => ?_, fun x hx => ⟨c.𝒰.nbhd ⟨x, hx⟩, c.𝒰.isGood _, ⟨?_⟩⟩⟩
  · obtain ⟨⟨φ, w⟩, hq'⟩ := q
    have hP : A.P w = A.X.src φ := hq'
    have hwb : A.P w ∈ A.X.PObj.boundary := by rw [hP]; exact hq
    have hμb : A.P (A.E.μ ⟨(φ, w), hq'⟩) ∈ A.X.PObj.boundary := by
      rw [A.E.P_μ]; exact (tgt_mem_boundary_iff_src φ).2 hq
    change Λ (A.E.μ ⟨(φ, w), hq'⟩) = Λ w
    rw [o.eq_sumMult hμb, o.eq_sumMult hwb]
    exact o.toSections.isBoundaryWFunctor_sumMult ⟨(φ, w), hq'⟩ hq
  · exact o.sym ⟨x, hx⟩

/-- The decoration `(𝒰, S)` (Definition 14.1.7 (1), (3)). -/
def toDecoration : BoundaryDecoration A Λ := ⟨c.𝒰, o.sym⟩

/-- The correspondences `τ` of `c` structure the decoration (Definition 14.1.7 (2), (4)). -/
def tau : o.toDecoration.Tau where
  τ := c.τ
  locallyConstant := c.locallyConstant
  finite := c.finite
  swap := c.swap
  diag := c.diag
  biact := c.biact
  compat := o.compat

/-- **The structured tuple `(Λ, 𝒰, S, τ)` over `∂X`** of sections over `c`. -/
def toTuple : BoundaryStructuredTuple A :=
  ⟨Λ, o.isBoundaryScPlusMultisection, o.toDecoration, o.tau⟩

@[simp] theorem toTuple_Λ : o.toTuple.Λ = Λ := rfl

/-- The class `[Λ, 𝒰, S, τ]` (Definition 14.1.7). -/
def toStructured : BoundaryStructuredMultisection A := Quotient.mk _ o.toTuple

/-- A section over `c` vanishes at a point over which `Λ` charges no non-zero point
(`sᵢ(y)` has weight `≥ |I_x|⁻¹ > 0`). -/
theorem s_eq_fiberZero {x : A.X.PObj.boundary} {y : A.Obj} (hy : y ∈ c.𝒰.U x)
    (h0 : ∀ w, A.P w = y → w ≠ fiberZero A.P y → Λ w = 0) (i : c.I x) :
    o.s x i y = fiberZero A.P y := by
  by_contra hne
  have hP := o.toSections.P_s i hy
  have e := o.rep x (o.s x i y) (by rw [hP]; exact hy)
  rw [h0 _ hP hne] at e
  have hmem : i ∈ Finset.univ.filter fun j => o.s x j (A.P (o.s x i y)) = o.s x i y := by
    simp [hP]
  have hcard : 0 < ((Finset.univ.filter fun j => o.s x j (A.P (o.s x i y)) = o.s x i y).card :
      ℚ≥0) := Nat.cast_pos.2 (Finset.card_pos.2 ⟨i, hmem⟩)
  have hI : (0 : ℚ≥0) < (Fintype.card (c.I x) : ℚ≥0)⁻¹ :=
    inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  exact (mul_pos hI hcard).ne' (e.symm.trans rfl)

end Over

/-! ### Every structured tuple over `∂X` is a tuple over its own data -/

/-- The common data of a structured tuple `(Λ, 𝒰, S, τ)` over `∂X`. -/
def ofTuple (T : BoundaryStructuredTuple A) : BoundaryCommData A where
  𝒰 := T.dec.𝒰
  I x := (T.dec.S x).I
  τ := T.tau.τ
  locallyConstant := T.tau.locallyConstant
  finite := T.tau.finite
  swap := T.tau.swap
  diag := T.tau.diag
  biact := T.tau.biact

/-- The sections of a structured tuple over `∂X` over its own data. -/
def Over.ofTuple (T : BoundaryStructuredTuple A) : (ofTuple T).Over T.Λ where
  s x := (T.dec.S x).s
  isFaceScPlus x := (T.dec.S x).isFaceScPlus
  equivariant x := (T.dec.S x).equivariant
  compat := T.tau.compat
  rep x := (T.dec.S x).rep

theorem Over.ofTuple_toTuple (T : BoundaryStructuredTuple A) : (Over.ofTuple T).toTuple = T :=
  rfl

/-! ### The commensurable sum of a locally finite family over `∂X` -/

/-- **A locally finite family over `∂X`** (Definition 13.2.12 read over `∂X`): every point of
`∂X` has an open neighbourhood `O` over whose boundary points only finitely many `Λⱼ` charge a
non-zero point. -/
def IsLocallyFiniteBoundaryFamily {J : Type*} (Λ : J → A.W → ℚ≥0) : Prop :=
  ∀ y ∈ A.X.PObj.boundary, ∃ O : Set A.Obj, IsOpen O ∧ y ∈ O ∧
    {j | ∃ w, A.P w ∈ O ∩ A.X.PObj.boundary ∧ w ≠ fiberZero A.P (A.P w) ∧ 0 < Λ j w}.Finite

variable {J : Type*} {Λ : J → A.W → ℚ≥0}

/-- **Local finiteness of the sections**: near every point of `∂X` only finitely many families of
sections are non-zero. -/
theorem exists_finite_support (o : ∀ j, c.Over (Λ j)) (hlf : IsLocallyFiniteBoundaryFamily Λ)
    {y₀ : A.Obj} (hy₀ : y₀ ∈ A.X.PObj.boundary) :
    ∃ O : Set A.Obj, IsOpen O ∧ y₀ ∈ O ∧ ∃ F : Finset J, ∀ j ∉ F, ∀ x (i : c.I x),
      ∀ y ∈ O, extendZero (c.𝒰.U x) ((o j).s x i) y = fiberZero A.P y := by
  obtain ⟨O, hO, hy₀O, hfin⟩ := hlf y₀ hy₀
  refine ⟨O, hO, hy₀O, hfin.toFinset, fun j hj x i y hy => ?_⟩
  by_cases hyx : y ∈ c.𝒰.U x
  · rw [← extendZero_eqOn (fun z hz => (o j).toSections.P_s i hz) hyx]
    refine (o j).s_eq_fiberZero hyx (fun w hw hw0 => ?_) i
    by_contra hpos
    exact hj (hfin.mem_toFinset.2 ⟨w, ⟨by rw [hw]; exact hy, by
      rw [hw]; exact c.𝒰.U_subset_boundary x hyx⟩, hw ▸ hw0, pos_iff_ne_zero.2 hpos⟩)
  · unfold extendZero
    rw [if_neg fun h => hyx h.1]

/-- The fibre value `∑ᶠⱼ s^{j,x}ᵢ(y)` (the summands extended by `0` off `U(x)`). -/
def sumFib (o : ∀ j, c.Over (Λ j)) (x : A.X.PObj.boundary) (i : c.I x) (y : A.Obj) :
    A.P ⁻¹' {y} :=
  ∑ᶠ j, (⟨extendZero (c.𝒰.U x) ((o j).s x i) y, isSection_extendZero _ _ y⟩ : A.P ⁻¹' {y})

/-- **The sections `sˣᵢ = ∑ᶠⱼ s^{j,x}ᵢ`** of the commensurable sum over `∂X`. -/
def sumSec (o : ∀ j, c.Over (Λ j)) (x : A.X.PObj.boundary) (i : c.I x) (y : A.Obj) : A.W :=
  (sumFib o x i y : A.W)

theorem support_subset (o : ∀ j, c.Over (Λ j)) {O : Set A.Obj} {F : Finset J}
    (hF : ∀ j ∉ F, ∀ x (i : c.I x), ∀ y ∈ O,
      extendZero (c.𝒰.U x) ((o j).s x i) y = fiberZero A.P y)
    {x : A.X.PObj.boundary} (i : c.I x) {y : A.Obj} (hy : y ∈ O) :
    (support fun j => (⟨extendZero (c.𝒰.U x) ((o j).s x i) y, isSection_extendZero _ _ y⟩ :
      A.P ⁻¹' {y})) ⊆ F := by
  intro j hj
  by_contra hjF
  exact hj (Subtype.ext (hF j hjF x i y hy))

theorem sumSec_eq_sectionSum (o : ∀ j, c.Over (Λ j)) {O : Set A.Obj} {F : Finset J}
    (hF : ∀ j ∉ F, ∀ x (i : c.I x), ∀ y ∈ O,
      extendZero (c.𝒰.U x) ((o j).s x i) y = fiberZero A.P y)
    {x : A.X.PObj.boundary} (i : c.I x) {y : A.Obj} (hy : y ∈ O) :
    sumSec o x i y = sectionSum A.P F (fun j => extendZero (c.𝒰.U x) ((o j).s x i)) y := by
  rw [sectionSum_apply fun j => isSection_extendZero _ _, sumSec, sumFib,
    finsum_eq_sum_of_support_subset _ (support_subset o hF i hy)]

/-- **The sections of the commensurable sum are sections over `c`.** -/
def lfSections (o : ∀ j, c.Over (Λ j)) (hlf : IsLocallyFiniteBoundaryFamily Λ) : c.Sections where
  s := sumSec o
  isFaceScPlus x i := by
    have hUb := c.𝒰.U_subset_boundary x
    refine isFaceScPlusSectionOn_of_locally hUb fun y hy => ?_
    obtain ⟨O, hO, hyO, F, hF⟩ := exists_finite_support o hlf (hUb hy)
    have hsum : IsFaceScPlusSectionOn A
        (sectionSum A.P F fun j => extendZero (c.𝒰.U x) ((o j).s x i)) (c.𝒰.U x) :=
      isFaceScPlusSectionOn_sectionSum (c.𝒰.nbhd x).isOpen_U inter_subset_left subset_rfl hUb F
        (fun j => isSection_extendZero _ _) fun j =>
          ((o j).isFaceScPlus x i).extendZero (c.𝒰.nbhd x).isOpen_U inter_subset_left subset_rfl
            hUb
    exact ⟨_, O, hO, hyO, hsum.mono (singleton_subset_iff.2 hy),
      fun z hz => (sumSec_eq_sectionSum o hF i hz.1).symm⟩
  equivariant x g i y hy := by
    obtain ⟨O, -, hyO, F, hF⟩ := exists_finite_support o hlf (c.𝒰.U_subset_boundary x hy)
    have hgy : (c.𝒰.nbhd x).rep.Φ g y ∈ c.𝒰.U x := NatNbhd.mapsTo_Φ_bdry _ g hy
    refine (fibAct_finsum ((c.𝒰.nbhd x).src_Γ g hy.1) ((c.𝒰.nbhd x).tgt_Γ g hy.1)
      (F.finite_toSet.subset (support_subset o hF i hyO)) fun j => ?_).symm
    change extendZero _ _ _ = fibAct _ (extendZero _ _ _)
    rw [← extendZero_eqOn (fun z hz => (o j).toSections.P_s _ hz) hgy,
      ← extendZero_eqOn (fun z hz => (o j).toSections.P_s _ hz) hy]
    exact (o j).equivariant x g i y hy
  compat x x' φ hφ := by
    refine IndexCorr.sat_mono (fun i i' H => ?_)
      (IndexCorr.sat_iInter fun j => (o j).compat x x' φ hφ)
    obtain ⟨O, -, hyO, F, hF⟩ := exists_finite_support o hlf (c.𝒰.U_subset_boundary x hφ.1)
    refine (fibAct_finsum rfl rfl (F.finite_toSet.subset (support_subset o hF i hyO))
      fun j => ?_).symm
    change extendZero _ _ _ = fibAct _ (extendZero _ _ _)
    rw [← extendZero_eqOn (fun z hz => (o j).toSections.P_s _ hz) hφ.2,
      ← extendZero_eqOn (fun z hz => (o j).toSections.P_s _ hz) hφ.1]
    exact H j

/-- **The commensurable sum `⊕^c_{j ∈ J} Λⱼ` over `∂X`** of a locally finite family over `c`:
the counting functor of the sections `sˣᵢ = ∑ᶠⱼ s^{j,x}ᵢ`. -/
def lfSum (o : ∀ j, c.Over (Λ j)) (hlf : IsLocallyFiniteBoundaryFamily Λ) : A.W → ℚ≥0 :=
  c.sumMult (lfSections o hlf).s

/-- The data `(𝒰, S, τ)` of the commensurable sum. -/
def Over.lfSum (o : ∀ j, c.Over (Λ j)) (hlf : IsLocallyFiniteBoundaryFamily Λ) :
    c.Over (BoundaryCommData.lfSum o hlf) :=
  (lfSections o hlf).toOver

/-- **Definition 13.4.5 over `∂X`, the locally finite commensurable sum**: for a locally finite
family `(Λⱼ)` with structures `[Λⱼ, 𝒰, Sⱼ, τ]` over `∂X` over a common `c`, `Λ = ⊕^c_j Λⱼ` is an
sc⁺-multisection over `∂X`, structured by `(𝒰, S, τ)` with `sˣᵢ = ∑ᶠⱼ s^{j,x}ᵢ` on `U(x)` and
`Λ(w) = |I_x|⁻¹·#{i | sˣᵢ(P(w)) = w}` for `P(w) ∈ U(x)`. -/
theorem definition_13_4_5_boundary (o : ∀ j, c.Over (Λ j))
    (hlf : IsLocallyFiniteBoundaryFamily Λ) :
    IsBoundaryScPlusMultisection A (lfSum o hlf) ∧
      (∀ x (i : c.I x) y (hy : y ∈ c.𝒰.U x), (Over.lfSum o hlf).s x i y =
        ((∑ᶠ j, (⟨(o j).s x i y, (o j).toSections.P_s i hy⟩ : A.P ⁻¹' {y}) :
          A.P ⁻¹' {y}) : A.W)) ∧
      ∀ x w, A.P w ∈ c.𝒰.U x → lfSum o hlf w =
        (Fintype.card (c.I x) : ℚ≥0)⁻¹ *
          ((Finset.univ.filter fun i => (Over.lfSum o hlf).s x i (A.P w) = w).card : ℚ≥0) := by
  refine ⟨(Over.lfSum o hlf).isBoundaryScPlusMultisection, fun x i y hy => ?_,
    fun x w hw => (Over.lfSum o hlf).rep x w hw⟩
  change ((∑ᶠ j, _ : A.P ⁻¹' {y}) : A.W) = _
  congr 1
  exact finsum_congr fun j => Subtype.ext
    (extendZero_eqOn (fun z hz => (o j).toSections.P_s i hz) hy).symm

/-! ### The data `(β·s^{0x}_i)` (Lemma 13.2.11 over `∂X`) -/

/-- **`β ⊙ Λ` over the data of a structured tuple over `∂X`**: the sections `β·sˣᵢ` with the same
`(𝒰, I, τ)` (the structured `Λ_a` of p. 672 for `β = β_a`). -/
def smulOver (T : BoundaryStructuredTuple A) {β : A.Obj → ℝ}
    (hβ : ∀ φ : A.Mor, β (A.X.tgt φ) = β (A.X.src φ))
    (hβs : A.X.PObj.IsScSmoothMap realPolyfold β) :
    (ofTuple T).Over (multisectionSmulFun β T.Λ) where
  s x i := SymmetricStructureOn.smulSection (T.dec.𝒰.U x) β ((T.dec.S x).s i)
  isFaceScPlus x i := by
    have hUb := T.dec.𝒰.U_subset_boundary x
    exact (((T.dec.S x).isFaceScPlus i).extendZero (T.dec.𝒰.nbhd x).isOpen_U inter_subset_left
      subset_rfl hUb).sectionSmul (T.dec.𝒰.nbhd x).isOpen_U inter_subset_left subset_rfl
        (isSection_extendZero _ _) hβs
  equivariant x g i y hy := by
    set N := T.dec.𝒰.nbhd x
    have hgy : N.rep.Φ g y ∈ N.bdry := NatNbhd.mapsTo_Φ_bdry N g hy
    refine (fibAct_sectionSmul (isSection_extendZero _ _) (isSection_extendZero _ _)
      (N.src_Γ g hy.1) (N.tgt_Γ g hy.1) ?_ ?_).symm
    · rw [← N.tgt_Γ g hy.1, hβ, N.src_Γ g hy.1]
    · exact ((extendZero_eqOn (s := (T.dec.S x).s (g • (i : (T.dec.S x).I)))
        (fun z hz => (T.dec.S x).P_s _ hz) hgy).symm.trans
          ((T.dec.S x).equivariant g i y hy)).trans
        (congrArg (fibAct (N.rep.Γ g y))
          (extendZero_eqOn (s := (T.dec.S x).s i) (fun z hz => (T.dec.S x).P_s _ hz) hy))
  compat x x' φ hφ := by
    refine IndexCorr.sat_mono (fun i j H => ?_) (T.tau.compat x x' φ hφ)
    refine (fibAct_sectionSmul (isSection_extendZero _ _) (isSection_extendZero _ _) rfl rfl
      (hβ φ) ?_).symm
    exact ((extendZero_eqOn (s := (T.dec.S x').s j) (fun z hz => (T.dec.S x').P_s _ hz)
      hφ.2).symm.trans H).trans (congrArg (fibAct φ)
        (extendZero_eqOn (s := (T.dec.S x).s i) (fun z hz => (T.dec.S x).P_s _ hz) hφ.1))
  rep x := by
    have hs : ∀ i, ∀ y ∈ T.dec.𝒰.U x,
        A.P (SymmetricStructureOn.smulSection (T.dec.𝒰.U x) β ((T.dec.S x).s i) y) = y :=
      fun i y _ => (isSection_extendZero _ _).sectionSmul y
    refine SymmetricStructureOn.rep_of_apply_fib hs fun y hy u => ?_
    have hP : A.P (u : A.W) = y := u.2
    have hsum : ∑ _i : (T.dec.S x).I, (Fintype.card (T.dec.S x).I : ℚ≥0)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    have hfib : ∀ v : A.P ⁻¹' {y}, T.Λ v = ∑ i, if v = (⟨(T.dec.S x).s i y,
        (T.dec.S x).P_s i hy⟩ : A.P ⁻¹' {y}) then (Fintype.card (T.dec.S x).I : ℚ≥0)⁻¹
        else 0 := fun v => by
      have hPv : A.P (v : A.W) = y := v.2
      rw [(T.dec.S x).rep v (by rw [hPv]; exact hy)]
      exact count_eq_sum (T.dec.S x).s (fun i => (T.dec.S x).P_s i hy) v
    change multisectionSmul (β (A.P (u : A.W))) T.Λ u = _
    rw [multisectionSmul_fib, hP, smulAt_eq_sum _ _ hsum hfib]
    refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
    constructor
    · intro e; rw [e]
      exact Subtype.ext (SymmetricStructureOn.smulSection_apply hy _).symm
    · intro e; rw [e]
      exact Subtype.ext (SymmetricStructureOn.smulSection_apply hy _)

theorem smulOver_s_apply (T : BoundaryStructuredTuple A) {β : A.Obj → ℝ}
    (hβ : ∀ φ : A.Mor, β (A.X.tgt φ) = β (A.X.src φ))
    (hβs : A.X.PObj.IsScSmoothMap realPolyfold β) {x : A.X.PObj.boundary}
    (i : (ofTuple T).I x) {y : A.Obj} (hy : y ∈ T.dec.𝒰.U x) :
    (smulOver T hβ hβs).s x i y =
      ((β y • (⟨(T.dec.S x).s i y, (T.dec.S x).P_s i hy⟩ : A.P ⁻¹' {y}) : A.P ⁻¹' {y}) : A.W) :=
  SymmetricStructureOn.smulSection_apply hy _

/-! ### Lemma 14.5.2 -/

/-- `β ⊙ Λ` is trivial where `β = 0`. -/
theorem multisectionSmulFun_eq_zero_of {β : A.Obj → ℝ} {Λ' : A.W → ℚ≥0} {w : A.W}
    (h : β (A.P w) = 0) (hw : w ≠ fiberZero A.P (A.P w)) : multisectionSmulFun β Λ' w = 0 := by
  unfold multisectionSmulFun
  rw [h, multisectionSmul_zero]
  unfold zeroMultisection
  rw [if_neg hw]

/-- **2021 Lemma 14.5.2, p. 672 (2017: Lemma 14.11)**: let `Λ̃ = (Λ, 𝒰⁰, S⁰, τ⁰)` be a structured
sc⁺-multisection over `∂X` and `(β_a)_{a ∈ ι}` sc-smooth functors `X → ℝ` (as in Lemma 14.5.1),
locally finite (near every point only finitely many are non-zero, Lemma 14.5.1 (2)) with
`∑ᶠ_a β_a = 1` on `∂X` (Lemma 14.5.1 (3)).  The structured `Λ̃_a = (β_a ⊙ Λ, 𝒰⁰, S^a, τ⁰)` with
the sections `s^{a,x}_i = β_a · s^{0x}_i` (`smulOver`) form a locally finite family over the
common data of `Λ̃`, and their commensurable sum `⊕_a Λ̃_a` is `Λ̃`: it has the sections
`s^{0x}_i` on every `U⁰(x)`, the functor `Λ` over `∂X`, and the same class as `Λ̃`
(Definition 14.1.7). -/
theorem lemma_14_5_2 (T : BoundaryStructuredTuple A) {ι : Type*} (β : ι → A.Obj → ℝ)
    (hβ : ∀ a (φ : A.Mor), β a (A.X.tgt φ) = β a (A.X.src φ))
    (hβs : ∀ a, A.X.PObj.IsScSmoothMap realPolyfold (β a))
    (hlf : ∀ y, ∃ O : Set A.Obj, IsOpen O ∧ y ∈ O ∧ {a | ∃ z ∈ O, β a z ≠ 0}.Finite)
    (hsum : ∀ y ∈ A.X.PObj.boundary, ∑ᶠ a, β a y = 1) :
    ∃ hlfΛ : IsLocallyFiniteBoundaryFamily fun a => multisectionSmulFun (β a) T.Λ,
      (∀ x (i : (ofTuple T).I x), ∀ y ∈ T.dec.𝒰.U x,
        (Over.lfSum (fun a => smulOver T (hβ a) (hβs a)) hlfΛ).s x i y = (T.dec.S x).s i y) ∧
      (∀ w, A.P w ∈ A.X.PObj.boundary →
        lfSum (fun a => smulOver T (hβ a) (hβs a)) hlfΛ w = T.Λ w) ∧
      BoundaryStructuredTuple.Equiv
        (Over.lfSum (fun a => smulOver T (hβ a) (hβs a)) hlfΛ).toTuple T := by
  -- local finiteness of the family `β_a ⊙ Λ`
  have hlfΛ : IsLocallyFiniteBoundaryFamily fun a => multisectionSmulFun (β a) T.Λ := by
    intro y _
    obtain ⟨O, hO, hyO, hfin⟩ := hlf y
    refine ⟨O, hO, hyO, hfin.subset fun a ⟨w, hw, hw0, hpos⟩ => ?_⟩
    by_contra hne
    have h0 : β a (A.P w) = 0 := by
      by_contra h0
      exact hne ⟨A.P w, hw.1, h0⟩
    have e : multisectionSmulFun (β a) T.Λ w = 0 := multisectionSmulFun_eq_zero_of h0 hw0
    simp only [e] at hpos
    exact lt_irrefl _ hpos
  set o := fun a => smulOver T (hβ a) (hβs a) with ho
  -- the sections of the sum are the original ones (`∑ᶠ_a β_a = 1` on `∂X`)
  have hsec : ∀ x (i : (ofTuple T).I x), ∀ y ∈ T.dec.𝒰.U x,
      (Over.lfSum o hlfΛ).s x i y = (T.dec.S x).s i y := fun x i y hy => by
    rw [(definition_13_4_5_boundary o hlfΛ).2.1 x i y hy]
    have hP : A.P ((T.dec.S x).s i y) = y := (T.dec.S x).P_s i hy
    have e : ∀ a, (⟨(o a).s x i y, (o a).toSections.P_s i hy⟩ : A.P ⁻¹' {y}) =
        β a y • (⟨(T.dec.S x).s i y, hP⟩ : A.P ⁻¹' {y}) := fun a =>
      Subtype.ext (smulOver_s_apply T (hβ a) (hβs a) i hy)
    obtain ⟨O, -, hyO, hfin⟩ := hlf y
    have hfs : (support fun a => β a y).Finite :=
      hfin.subset fun a ha => ⟨y, hyO, ha⟩
    rw [finsum_congr e, ← finsum_smul' hfs, hsum y (T.dec.𝒰.U_subset_boundary x hy), one_smul]
  -- the functors agree over `∂X`
  have hmult : ∀ w, A.P w ∈ A.X.PObj.boundary → lfSum o hlfΛ w = T.Λ w := fun w hw => by
    have hwU : A.P w ∈ T.dec.𝒰.U ⟨A.P w, hw⟩ := T.dec.𝒰.mem_U _
    rw [(Over.lfSum o hlfΛ).rep ⟨A.P w, hw⟩ w hwU, (Over.ofTuple T).rep ⟨A.P w, hw⟩ w hwU]
    unfold countAt
    congr 3
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hsec _ i _ hwU]
    rfl
  refine ⟨hlfΛ, hsec, hmult, hmult, fun x => (T.dec.𝒰.nbhd x).U,
    fun x => (T.dec.𝒰.nbhd x).isOpen_U, fun x => (T.dec.𝒰.nbhd x).mem_U,
    fun _ _ hy => ⟨hy, hy⟩, fun _ => rfl, fun _ _ _ _ => (IndexCorr.map_cast_rfl _).symm⟩

/-! ### Remark 14.5.3 -/

/-- **Data over `c` are determined by their sections at one point**: if two families of
sections over `c` agree at `a ∈ ∂X` on `V ⊆ U(a)` and both vanish at the points of the `U(x)`
outside the saturation `π⁻¹(π(V))`, they agree on every `U(x)` (along a morphism `φ : z → y`
with `z ∈ V`, (4) gives `s^x_{b(k)}(y) = μ(φ, s^a_{a(k)}(z))` for a representative of
`τ_{a,x}(φ)`, and `b` is onto). -/
theorem Over.s_eq_of_eqOn {Λ₁ Λ₂ : A.W → ℚ≥0} (o₁ : c.Over Λ₁) (o₂ : c.Over Λ₂)
    (a : A.X.PObj.boundary) {V : Set A.Obj} (hV : V ⊆ c.𝒰.U a)
    (heq : ∀ i, ∀ z ∈ V, o₁.s a i z = o₂.s a i z)
    (hz : ∀ x (i : c.I x), ∀ y ∈ c.𝒰.U x, A.X.π y ∉ A.X.π '' V →
      o₁.s x i y = fiberZero A.P y ∧ o₂.s x i y = fiberZero A.P y)
    (x : A.X.PObj.boundary) (j : c.I x) {y : A.Obj} (hy : y ∈ c.𝒰.U x) :
    o₁.s x j y = o₂.s x j y := by
  by_cases hπ : A.X.π y ∈ A.X.π '' V
  · obtain ⟨z, hzV, hzy⟩ := hπ
    obtain ⟨φ, hφs, hφt⟩ := (A.X.π_eq_π_iff).1 hzy
    have hφ : φ ∈ c.𝒰.mor a x := ⟨by rw [hφs]; exact hV hzV, by rw [hφt]; exact hy⟩
    have h₁ := o₁.compat a x φ hφ
    have h₂ := o₂.compat a x φ hφ
    revert h₁ h₂
    refine IndexCorr.ind (fun d h₁ h₂ => ?_) (c.τ a x φ)
    obtain ⟨k, hk⟩ := d.surjective_b j
    have e₁ : o₁.s x (d.b k) (A.X.tgt φ) = fibAct φ (o₁.s a (d.a k) (A.X.src φ)) := h₁ k
    have e₂ : o₂.s x (d.b k) (A.X.tgt φ) = fibAct φ (o₂.s a (d.a k) (A.X.src φ)) := h₂ k
    rw [hk, hφt, hφs] at e₁ e₂
    rw [e₁, e₂, heq _ z hzV]
  · rw [(hz x j y hy hπ).1, (hz x j y hy hπ).2]

/-- **2021 Remark 14.5.3, p. 672 (2017: Remark 14.7)**: `Λ_a = β_a ⊙ Λ` is completely determined
by the sections `(β_a · s^{0a}_i)` at `a` on a set `V ⊆ U⁰(a)` (the text: on `U⁰(a)`, even on
`V_a`) together with `τ⁰`, when `β_a` vanishes off the saturation `π⁻¹(π(V))` (Lemma 14.5.1 (1)
with `V = V̂_a ∩ U⁰(a)`): every structure `[Λ', 𝒰⁰, S', τ⁰]` over the same data whose sections
at `a` agree with them on `V` and vanish off `π⁻¹(π(V))` has the sections of `Λ̃_a` everywhere
and `Λ' = Λ_a` over `∂X`. -/
theorem remark_14_5_3 (T : BoundaryStructuredTuple A) {β : A.Obj → ℝ}
    (hβ : ∀ φ : A.Mor, β (A.X.tgt φ) = β (A.X.src φ))
    (hβs : A.X.PObj.IsScSmoothMap realPolyfold β) (a : A.X.PObj.boundary) {V : Set A.Obj}
    (hV : V ⊆ T.dec.𝒰.U a) (hsupp : ∀ y, β y ≠ 0 → A.X.π y ∈ A.X.π '' V)
    {Λ' : A.W → ℚ≥0} (o' : (ofTuple T).Over Λ')
    (heq : ∀ i, ∀ z ∈ V, o'.s a i z = (smulOver T hβ hβs).s a i z)
    (hz : ∀ x (i : (ofTuple T).I x), ∀ y ∈ T.dec.𝒰.U x, A.X.π y ∉ A.X.π '' V →
      o'.s x i y = fiberZero A.P y) :
    (∀ x (i : (ofTuple T).I x), ∀ y ∈ T.dec.𝒰.U x, o'.s x i y = (smulOver T hβ hβs).s x i y) ∧
      ∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = multisectionSmulFun β T.Λ w := by
  have hzero : ∀ x (i : (ofTuple T).I x), ∀ y ∈ T.dec.𝒰.U x, A.X.π y ∉ A.X.π '' V →
      (smulOver T hβ hβs).s x i y = fiberZero A.P y := fun x i y hy hπ => by
    have h0 : β y = 0 := by
      by_contra h0
      exact hπ (hsupp y h0)
    rw [smulOver_s_apply T hβ hβs i hy, h0, zero_smul]
    rfl
  have hall := Over.s_eq_of_eqOn o' (smulOver T hβ hβs) a hV heq
    (fun x i y hy hπ => ⟨hz x i y hy hπ, hzero x i y hy hπ⟩)
  refine ⟨fun x i y hy => hall x i hy, fun w hw => ?_⟩
  have hwU : A.P w ∈ T.dec.𝒰.U ⟨A.P w, hw⟩ := T.dec.𝒰.mem_U _
  rw [o'.rep ⟨A.P w, hw⟩ w hwU, (smulOver T hβ hβs).rep ⟨A.P w, hw⟩ w hwU]
  unfold countAt
  congr 3
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hall _ i hwU]

end BoundaryCommData


end SBLocalization

end Polyfold
