import Polyfold.Chapter11.MultisectionLocalStructure2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.2 (pp. 607–612): the local sections of Definition 13.2.1 under sums and scalar multiples.

# Local sc⁺-sections form a module over the sc-smooth functions

The sums `Λ' ⊕ Λ''` (Definition 13.2.9 (3): `s_{(i,i')} = s_i + s'_{i'}`), the scalar multiples
`aΛ` (Definition 13.2.10: `a·s_i`), the products `β ⊙ Λ` (Lemma 13.2.11) and the locally finite
sums (before Lemma 13.2.13: `∑_j s^j_{i_j}`) all use that the local sc⁺-sections on an open set
`U` (`IsScPlusSectionOn`, the sections of Definition 13.2.1) are closed under fibrewise sums and
under multiplication by sc-smooth functions.  Part I proves this for global sc⁺-sections
(`StrongBundle.IsScPlusSection.add`, `smul_left`); here is the version on an open set, read in
the charts `Φ[1]` of `W[1]` exactly as in the proof of `StrongBundle.isScPlusSection_iff`.

## Main statements (namespace `Polyfold.SBLocalization`)

* `IsScPlusSectionOn.isScSmoothRetractMap_localRepOne`, `isScPlusSectionOn_of_localRepOne`: an
  sc⁺-section on `U` is the same as a section on `U` whose chart representatives
  `z ↦ Φ(s(φ⁻¹ z))[1]` are sc-smooth on `φ(U ∩ dom φ)`.
* `IsScPlusSectionOn.sectionAdd`, `IsScPlusSectionOn.sectionSmul`, `isScPlusSectionOn_sectionSum`.
* `IsScPlusSectionOn.normalize`, `IsLocalRepOn.normalize`: the local sections of a local
  representation may be taken to be global sections of `P` (values off `U` do not matter).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle

variable {A : SEP.{u}}

theorem localRepOne_eq_liftOne (c : StrongBundleChart A.X.PObj A.P) (s : A.Obj → A.W)
    (z : c.φ.model.E 0) : localRepOne c s z = c.liftOne (s (c.φ.symm z)) := rfl

/-- An sc⁺-section on `U` read in a strong bundle chart `Φ` of the atlas: its representative
`z ↦ Φ(s(φ⁻¹ z))[1]` is sc-smooth on `φ(U ∩ dom φ)`. -/
theorem IsScPlusSectionOn.isScSmoothRetractMap_localRepOne {s : A.Obj → A.W} {U : Set A.Obj}
    (h : IsScPlusSectionOn A s U) (hU : IsOpen U) {c : StrongBundleChart A.X.PObj A.P}
    (hc : c ∈ A.B.atlas.charts) (x : A.Obj) :
    IsScSmoothRetractMap c.φ.model.E c.φ.model.C (c.φ '' (U ∩ c.φ.source))
      (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c.K)
      (localRepOne c s) := by
  obtain ⟨hsec, G, hG, hGs⟩ := h
  have h1 := hGs.smooth c.φ (oneChart hc (G x)) c.isChart (A.B.isChart_oneChart hc (G x))
    (U ∩ c.φ.source) (hU.inter c.φ.isOpen_source) subset_rfl fun y hy => by
      change A.B.oneVal (G y) ∈ c.toPartialEquiv.source
      rw [hG y hy.1, c.source_eq, mem_preimage, hsec y hy.1]; exact hy.2
  refine h1.congr ?_
  rintro _ ⟨y, hy, rfl⟩
  change c.liftOne (A.B.oneVal (G (c.φ.symm (c.φ y)))) = localRepOne c s (c.φ y)
  rw [localRepOne_eq_liftOne, c.φ.symm_apply_apply hy.2, hG y hy.1]

/-- The values of an sc⁺-section on `U` lie in `W_{0,1}`. -/
theorem IsScPlusSectionOn.mem_oneSet {s : A.Obj → A.W} {U : Set A.Obj}
    (h : IsScPlusSectionOn A s U) {y : A.Obj} (hy : y ∈ U) : s y ∈ A.B.oneSet := by
  obtain ⟨-, G, hG, -⟩ := h
  rw [← hG y hy]; exact A.B.oneVal_mem (G y)

/-- A chart of the atlas of `W` whose base domain contains a given point. -/
theorem exists_chart_mem_source (A : SEP.{u}) (x : A.Obj) :
    ∃ c ∈ A.B.atlas.charts, x ∈ c.φ.source := by
  obtain ⟨c, hc, hxc⟩ := A.B.atlas.cover (fiberZero A.P x)
  refine ⟨c, hc, ?_⟩
  rw [c.source_eq, mem_preimage, proj_fiberZero A.P x] at hxc; exact hxc

/-- **The converse**: a section on the open set `U` whose representatives in charts of the atlas
around every point of `U` take values in `F₁` and are sc-smooth on `φ(U ∩ dom φ)` is an
sc⁺-section on `U`. -/
theorem isScPlusSectionOn_of_localRepOne {s : A.Obj → A.W} {U : Set A.Obj} (hU : IsOpen U)
    (hsec : ∀ y ∈ U, A.P (s y) = y)
    (hloc : ∀ x ∈ U, ∃ c ∈ A.B.atlas.charts, x ∈ c.φ.source ∧
      (∀ y ∈ U ∩ c.φ.source, (c (s y)).2 ∈ range (c.F.toBase 1)) ∧
      IsScSmoothRetractMap c.φ.model.E c.φ.model.C (c.φ '' (U ∩ c.φ.source))
        (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c.K)
        (localRepOne c s)) :
    IsScPlusSectionOn A s U := by
  classical
  have hsrc : ∀ {c : StrongBundleChart A.X.PObj A.P}, ∀ y ∈ U, y ∈ c.φ.source →
      s y ∈ c.toPartialEquiv.source := fun {c} y hy hyc => by
    rw [c.source_eq, mem_preimage, hsec y hy]; exact hyc
  have hmem : ∀ y ∈ U, s y ∈ A.B.oneSet := fun y hy => by
    obtain ⟨c, hc, hyc, hr, -⟩ := hloc y hy
    exact (A.B.mem_oneSet_iff hc (hsrc y hy hyc)).2 (hr y ⟨hy, hyc⟩)
  have h0 : ∀ y, fiberZero A.P y ∈ A.B.oneSet := fun y =>
    (StrongBundle.isScPlusSection_fiberZero (B := A.B)).mem_oneSet y
  set G : A.Obj → A.B.One := fun y =>
    if hy : s y ∈ A.B.oneSet then A.B.oneMk (s y) hy else A.B.oneMk _ (h0 y) with hGdef
  have hG : ∀ y ∈ U, A.B.oneVal (G y) = s y := fun y hy => by
    simp only [hGdef, dif_pos (hmem y hy), oneVal_oneMk]
  -- in the chart `Φ[1]`, `G = (Φ[1])⁻¹ ∘ (representative) ∘ φ` on `U ∩ dom φ`
  have hloc' : ∀ x ∈ U, ∃ c ∈ A.B.atlas.charts, ∃ hc : c ∈ A.B.atlas.charts, x ∈ c.φ.source ∧
      EqOn G ((oneChart hc (G x)).symm ∘ localRepOne c s ∘ c.φ) (U ∩ c.φ.source) ∧
      IsScSmoothRetractMap c.φ.model.E c.φ.model.C (c.φ '' (U ∩ c.φ.source))
        (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c.K)
        (localRepOne c s) := fun x hx => by
    obtain ⟨c, hc, hxc, -, hrep⟩ := hloc x hx
    refine ⟨c, hc, hc, hxc, fun y hy => ?_, hrep⟩
    have hy1 : G y ∈ (oneChart hc (G x)).source := by
      change A.B.oneVal (G y) ∈ c.toPartialEquiv.source
      rw [hG y hy.1]; exact hsrc y hy.1 hy.2
    change G y = (oneChart hc (G x)).symm (localRepOne c s (c.φ y))
    have : localRepOne c s (c.φ y) = oneChart hc (G x) (G y) := by
      rw [localRepOne_eq_liftOne, c.φ.symm_apply_apply hy.2, oneChart_apply, hG y hy.1]
    rw [this, (oneChart hc (G x)).symm_apply_apply hy1]
  have hcont : ContinuousOn G U := fun x hx => by
    obtain ⟨c, -, hc, hxc, heq, hrep⟩ := hloc' x hx
    have hV : IsOpen (U ∩ c.φ.source) := hU.inter c.φ.isOpen_source
    have hret := c.φ.isScRetract_image inter_subset_right hV
    have h3 : ContinuousOn ((oneChart hc (G x)).symm ∘ localRepOne c s ∘ c.φ) (U ∩ c.φ.source) :=
      ((oneChart hc (G x)).continuousOn_invFun.comp (hrep.continuousOn hret)
        fun z hz => hrep.mapsTo hz).comp (c.φ.continuousOn_toFun.mono inter_subset_right)
          fun y hy => mem_image_of_mem _ hy
    exact ((h3.congr heq).continuousAt (hV.mem_nhds ⟨hx, hxc⟩)).continuousWithinAt
  refine ⟨hsec, G, hG, MPolyfold.IsScSmoothOn.of_exists_charts hU hcont fun x hx => ?_⟩
  obtain ⟨c, -, hc, hxc, heq, hrep⟩ := hloc' x hx
  refine ⟨c.φ, oneChart hc (G x), U ∩ c.φ.source, c.isChart, A.B.isChart_oneChart hc (G x),
    hU.inter c.φ.isOpen_source, ⟨hx, hxc⟩, subset_rfl, fun y hy => ?_, hrep.congr ?_⟩
  · change A.B.oneVal (G y) ∈ c.toPartialEquiv.source
    rw [hG y hy.1]; exact hsrc y hy.1 hy.2
  · rintro _ ⟨y, hy, rfl⟩
    change localRepOne c s (c.φ y) = oneChart hc (G x) (G (c.φ.symm (c.φ y)))
    rw [c.φ.symm_apply_apply hy.2, oneChart_apply, hG y hy.1, localRepOne_eq_liftOne,
      c.φ.symm_apply_apply hy.2]


/-! ### Sums and products with functions -/

theorem toBase_localRepOne_snd_of_mem (c : StrongBundleChart A.X.PObj A.P) {s : A.Obj → A.W}
    {z : c.φ.model.E 0} (h : (c (s (c.φ.symm z))).2 ∈ range (c.F.toBase 1)) :
    c.F.toBase 1 (localRepOne c s z).2 = (c (s (c.φ.symm z))).2 :=
  Function.invFun_eq h

theorem IsScPlusSectionOn.mem_range {s : A.Obj → A.W} {U : Set A.Obj}
    (h : IsScPlusSectionOn A s U) {c : StrongBundleChart A.X.PObj A.P}
    (hc : c ∈ A.B.atlas.charts) {y : A.Obj} (hy : y ∈ U ∩ c.φ.source) :
    (c (s y)).2 ∈ range (c.F.toBase 1) := by
  refine (A.B.mem_oneSet_iff hc ?_).1 (h.mem_oneSet hy.1)
  rw [c.source_eq, mem_preimage, h.1 y hy.1]; exact hy.2

/-- **The sum of two sc⁺-sections on `U` is an sc⁺-section on `U`** (the local form of Part I's
`StrongBundle.IsScPlusSection.add`; used in Definition 13.2.9 (3)). -/
theorem IsScPlusSectionOn.sectionAdd {s₁ s₂ : A.Obj → A.W} {U : Set A.Obj} (hU : IsOpen U)
    (h₁ : IsScPlusSectionOn A s₁ U) (h₂ : IsScPlusSectionOn A s₂ U)
    (hs₁ : IsSection A.P s₁) (hs₂ : IsSection A.P s₂) :
    IsScPlusSectionOn A (Polyfold.sectionAdd A.P s₁ s₂) U := by
  have hval : ∀ (c : StrongBundleChart A.X.PObj A.P) {y : A.Obj}, y ∈ c.φ.source →
      (c (Polyfold.sectionAdd A.P s₁ s₂ y)).2 = (c (s₁ y)).2 + (c (s₂ y)).2 := fun c y hy => by
    rw [sectionAdd_apply hs₁ hs₂]; exact c.snd_add hy _ _
  refine isScPlusSectionOn_of_localRepOne hU (fun y _ => hs₁.sectionAdd hs₂ y) fun x hx => ?_
  obtain ⟨c, hc, hxc⟩ := exists_chart_mem_source A x
  refine ⟨c, hc, hxc, fun y hy => ?_, ?_⟩
  · rw [hval c hy.2]
    obtain ⟨a, ha⟩ := h₁.mem_range hc hy
    obtain ⟨b, hb⟩ := h₂.mem_range hc hy
    exact ⟨a + b, by rw [map_add, ha, hb]⟩
  have hL₁ := h₁.isScSmoothRetractMap_localRepOne hU hc x
  have hL₂ := h₂.isScSmoothRetractMap_localRepOne hU hc x
  have hrep : EqOn (fun z => ((localRepOne c s₁ z).1,
      (localRepOne c s₁ z).2 + (localRepOne c s₂ z).2))
      (localRepOne c (Polyfold.sectionAdd A.P s₁ s₂)) (c.φ '' (U ∩ c.φ.source)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hz : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model y hy.2
    have hzs : c.φ.symm (c.φ y) = y := c.φ.symm_apply_apply hy.2
    have hy' : c.φ.symm (c.φ y) ∈ U ∩ c.φ.source := by rw [hzs]; exact hy
    refine Prod.ext ?_ (c.F.toBase_injective 1 ?_)
    · change (localRepOne c s₁ (c.φ y)).1 =
        (c (Polyfold.sectionAdd A.P s₁ s₂ (c.φ.symm (c.φ y)))).1
      rw [localRepOne_fst hs₁ hz, c.fst_apply (by rw [hs₁.sectionAdd hs₂]; exact hy'.2),
        hs₁.sectionAdd hs₂, hzs]
    · change c.F.toBase 1 ((localRepOne c s₁ (c.φ y)).2 + (localRepOne c s₂ (c.φ y)).2) =
        c.F.toBase 1 (Function.invFun (c.F.toBase 1)
          (c (Polyfold.sectionAdd A.P s₁ s₂ (c.φ.symm (c.φ y)))).2)
      rw [map_add, toBase_localRepOne_snd_of_mem c (h₁.mem_range hc hy'),
        toBase_localRepOne_snd_of_mem c (h₂.mem_range hc hy'), hval c hy'.2]
      obtain ⟨a, ha⟩ := h₁.mem_range hc hy'
      obtain ⟨b, hb⟩ := h₂.mem_range hc hy'
      exact (Function.invFun_eq ⟨a + b, by rw [map_add, ha, hb]⟩).symm
  refine IsScSmoothRetractMap.congr ⟨fun z hz => ?_, fun R hR => ?_⟩ hrep
  · obtain ⟨y, hy, rfl⟩ := hz
    have hz' : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model y hy.2
    have ha := hL₁.mapsTo (mem_image_of_mem c.φ hy)
    have hb := hL₂.mapsTo (mem_image_of_mem c.φ hy)
    have e1 : localRepOne c s₁ (c.φ y) = (c.φ y, (localRepOne c s₁ (c.φ y)).2) :=
      Prod.ext (localRepOne_fst hs₁ hz') rfl
    have e2 : localRepOne c s₂ (c.φ y) = (c.φ y, (localRepOne c s₂ (c.φ y)).2) :=
      Prod.ext (localRepOne_fst hs₂ hz') rfl
    rw [e1] at ha; rw [e2] at hb
    change ((localRepOne c s₁ (c.φ y)).1,
      (localRepOne c s₁ (c.φ y)).2 + (localRepOne c s₂ (c.φ y)).2) ∈ strongShiftOne c.K
    rw [localRepOne_fst hs₁ hz']
    exact c.add_mem_strongShiftOne ha hb
  · have hUR := R.isScDomain
    have g₁ := hL₁.comp_isScSmooth R hR
    have g₂ := hL₂.comp_isScSmooth R hR
    exact ((g₁.fst hUR).scPair hUR ((g₁.snd hUR).add hUR (g₂.snd hUR))).congr hUR
      fun _ _ => rfl

/-- **The product of an sc-smooth function and an sc⁺-section on `U` is an sc⁺-section on `U`**
(the local form of Part I's `StrongBundle.IsScPlusSection.smul_left`; used in Definition 13.2.10
and Lemma 13.2.11). -/
theorem IsScPlusSectionOn.sectionSmul {s : A.Obj → A.W} {U : Set A.Obj} (hU : IsOpen U)
    (h : IsScPlusSectionOn A s U) (hs : IsSection A.P s) {f : A.Obj → ℝ}
    (hf : A.X.PObj.IsScSmoothMap realPolyfold f) :
    IsScPlusSectionOn A (Polyfold.sectionSmul A.P f s) U := by
  have hval : ∀ (c : StrongBundleChart A.X.PObj A.P) {y : A.Obj}, y ∈ c.φ.source →
      (c (Polyfold.sectionSmul A.P f s y)).2 = f y • (c (s y)).2 := fun c y hy => by
    rw [sectionSmul_apply hs]
    exact (c.fiber_linear y hy).map_smul (f y) ⟨s y, hs y⟩
  refine isScPlusSectionOn_of_localRepOne hU (fun y _ => hs.sectionSmul y) fun x hx => ?_
  obtain ⟨c, hc, hxc⟩ := exists_chart_mem_source A x
  refine ⟨c, hc, hxc, fun y hy => ?_, ?_⟩
  · rw [hval c hy.2]
    obtain ⟨a, ha⟩ := h.mem_range hc hy
    exact ⟨f y • a, by rw [map_smul, ha]⟩
  have hL := h.isScSmoothRetractMap_localRepOne hU hc x
  have hrep : EqOn (fun z => ((localRepOne c s z).1, f (c.φ.symm z) • (localRepOne c s z).2))
      (localRepOne c (Polyfold.sectionSmul A.P f s)) (c.φ '' (U ∩ c.φ.source)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hz : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model y hy.2
    have hzs : c.φ.symm (c.φ y) = y := c.φ.symm_apply_apply hy.2
    have hy' : c.φ.symm (c.φ y) ∈ U ∩ c.φ.source := by rw [hzs]; exact hy
    refine Prod.ext ?_ (c.F.toBase_injective 1 ?_)
    · change (localRepOne c s (c.φ y)).1 =
        (c (Polyfold.sectionSmul A.P f s (c.φ.symm (c.φ y)))).1
      rw [localRepOne_fst hs hz, c.fst_apply (by rw [hs.sectionSmul]; exact hy'.2),
        hs.sectionSmul, hzs]
    · change c.F.toBase 1 (f (c.φ.symm (c.φ y)) • (localRepOne c s (c.φ y)).2) =
        c.F.toBase 1 (Function.invFun (c.F.toBase 1)
          (c (Polyfold.sectionSmul A.P f s (c.φ.symm (c.φ y)))).2)
      rw [map_smul, toBase_localRepOne_snd_of_mem c (h.mem_range hc hy'), hval c hy'.2]
      obtain ⟨a, ha⟩ := h.mem_range hc hy'
      exact (Function.invFun_eq ⟨f (c.φ.symm (c.φ y)) • a, by rw [map_smul, ha]⟩).symm
  have hf1 := (hf.real_chart c.isChart).mono_source c.φ.model.isScRetract
    (c.φ.image_subset_model (s := U ∩ c.φ.source) inter_subset_right)
  refine IsScSmoothRetractMap.congr ⟨fun z hz => ?_, fun R hR => ?_⟩ hrep
  · exact c.smul_mem_strongShiftOne (hL.mapsTo hz) _
  · have hUR := R.isScDomain
    have h1 := hL.comp_isScSmooth R hR
    have h2 := (hf1.comp_isScSmooth R hR).smul hUR (h1.snd hUR)
    exact ((h1.fst hUR).scPair hUR h2).congr hUR fun _ _ => rfl

/-- Constant multiples of sc⁺-sections on `U`. -/
theorem IsScPlusSectionOn.sectionSmul_const {s : A.Obj → A.W} {U : Set A.Obj} (hU : IsOpen U)
    (h : IsScPlusSectionOn A s U) (hs : IsSection A.P s) (a : ℝ) :
    IsScPlusSectionOn A (Polyfold.sectionSmul A.P (fun _ => a) s) U :=
  h.sectionSmul hU hs (isScSmoothMap_real_const a)

/-- The zero section is an sc⁺-section on every open set. -/
theorem isScPlusSectionOn_fiberZero {U : Set A.Obj} (hU : IsOpen U) :
    IsScPlusSectionOn A (fiberZero A.P) U :=
  IsScPlusSectionOn.of_isScPlusSection StrongBundle.isScPlusSection_fiberZero hU

theorem IsScPlusSectionOn.congr {s s' : A.Obj → A.W} {U : Set A.Obj}
    (h : IsScPlusSectionOn A s U) (hss' : EqOn s s' U) : IsScPlusSectionOn A s' U := by
  obtain ⟨hsec, G, hG, hGs⟩ := h
  exact ⟨fun y hy => hss' hy ▸ hsec y hy, G, fun y hy => (hG y hy).trans (hss' hy), hGs⟩

/-- **Finite sums of sc⁺-sections on `U`** (the sections `∑_j s^j_{i_j}` before Lemma 13.2.13). -/
theorem isScPlusSectionOn_sectionSum {ι : Type*} (I : Finset ι) {s : ι → A.Obj → A.W}
    {U : Set A.Obj} (hU : IsOpen U) (h : ∀ i, IsScPlusSectionOn A (s i) U)
    (hs : ∀ i, IsSection A.P (s i)) : IsScPlusSectionOn A (sectionSum A.P I s) U := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have : sectionSum A.P (∅ : Finset ι) s = fiberZero A.P := funext fun x => by
      rw [sectionSum_apply hs, Finset.sum_empty]; rfl
    rw [this]; exact isScPlusSectionOn_fiberZero hU
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
    rw [this]; exact (h a).sectionAdd hU ih (hs a) hI

/-! ### Normalized local sections -/

open scoped Classical in
/-- The section `s` on `U`, extended by the zero section off `U`. -/
def extendZero (U : Set A.Obj) (s : A.Obj → A.W) : A.Obj → A.W :=
  fun y => if y ∈ U ∧ A.P (s y) = y then s y else fiberZero A.P y

theorem isSection_extendZero (U : Set A.Obj) (s : A.Obj → A.W) :
    IsSection A.P (extendZero U s) := fun y => by
  unfold extendZero
  split_ifs with h
  · exact h.2
  · exact proj_fiberZero A.P y

theorem extendZero_eqOn {U : Set A.Obj} {s : A.Obj → A.W} (hs : ∀ y ∈ U, A.P (s y) = y) :
    EqOn s (extendZero U s) U := fun y hy => by
  unfold extendZero; rw [if_pos ⟨hy, hs y hy⟩]

/-- An sc⁺-section on `U` may be replaced by a global section of `P` equal to it on `U`. -/
theorem IsScPlusSectionOn.extendZero {s : A.Obj → A.W} {U : Set A.Obj}
    (h : IsScPlusSectionOn A s U) : IsScPlusSectionOn A (SBLocalization.extendZero U s) U :=
  h.congr (extendZero_eqOn h.1)

/-- **Normalized local representations**: the local sections of a local representation on `O`
may be taken to be global sections of `P` (only their values on `O` enter). -/
theorem IsLocalRepOn.extendZero {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ) :
    IsLocalRepOn A Λ O (fun i => SBLocalization.extendZero O (s i)) σ := by
  classical
  refine ⟨h.1, fun i => (h.2.1 i).extendZero, h.2.2.1, fun w hw => ?_⟩
  rw [h.2.2.2 w hw]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [extendZero_eqOn (h.2.1 i).1 hw]

end SBLocalization

end Polyfold
