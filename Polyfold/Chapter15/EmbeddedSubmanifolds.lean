import Polyfold.Chapter11.GraphChartsDiffeo
import Polyfold.Chapter11.BranchedEquivalenceTangent
import Polyfold.Chapter9.TangentSlicesBasic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definition 4.2.1 (p. 135),
Remark 4.2.2, §9.2 (p. 409) and the proof of Corollary 15.4.4 (p. 703).

# Submanifolds under sc-smooth maps with an sc-smooth left inverse

## The text, paraphrased

In the proof of Corollary 15.4.4 the solution sheets `M` of `X` are identified with the faces
`{i} × M` of the sheets of the cylinder `[0, 1] × X` through `x ↦ (i, x)`; the projection
`[0, 1] × X → X` is a left inverse of this map.

## What is formalized

For sc-smooth maps `f : X → Y`, `g : Y → X` of M-polyfolds with `g ∘ f = id`:

* `MPolyfold.IsSmoothSubmanifold.image_of_leftInverse`: the image `f(A)` of a smooth
  finite-dimensional submanifold `A ⊆ X` is one of `Y` (the sc⁺-retraction `f ∘ s ∘ g`).
* `MPolyfold.submanifoldTangent_image_of_leftInverse`: `T_{f(a)} f(A) = Tf(T_aA)`.
* `MPolyfold.tangentMap_tangentMap_of_leftInverse`,
  `MPolyfold.injective_tangentMap_of_leftInverse`: `Tg ∘ Tf = id`.
* `MPolyfold.chartVec_tangentMap_of_scOperator`, `MPolyfold.chartVec_tangentMap_of_const`: the
  chart vectors of `Tf(α)` when `f` is an sc-operator in charts, or constant.

For the slice inclusion `ι(x) = (q, x)` into a product `T × X` of M-polyfolds:

* `MPolyfold.chartVec_tangentMap_prodMk`, `MPolyfold.chartTangent_image_prodMk`: in a product
  chart, `Tι(α)` has the chart vector `(0, h)`, and `T_{(q, a)}({q} × A) = {0} × T_aA`.
* `MPolyfold.IsSubmanifoldOfDim.image_prodMk`: `{q} × A` has the dimension of `A`.
* `MPolyfold.GraphChart.prodMk`: the graph chart of `{q} × N` from one of `N`, with the same
  coordinates and the frame `Tι ∘ c.tvec` (`prodMk_coord_image`, `prodMk_tvec`).
* `MPolyfold.SubmanifoldOrientation.prodMk`: the pushed-forward orientation of `{q} × M`
  (`prodMk_frames_iff`).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u v

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {f : X → Y} {g : Y → X}

/-- `Tg ∘ Tf = id` for sc-smooth maps with `g ∘ f = id`. -/
theorem tangentMap_tangentMap_of_leftInverse (hf : P.IsScSmoothMap Q f) (hg : Q.IsScSmoothMap P g)
    (hgf : ∀ x, g (f x) = x) (α : P.TangentSpace) : tangentMap hg (tangentMap hf α) = α := by
  have h1 := congrFun (tangentMap_comp hg hf) α
  have h2 : tangentMap (hg.comp hf) α = tangentMap (P := P) isScSmoothMap_id α :=
    tangentMap_eqOn_of_eqOn _ _ isOpen_univ (fun x _ => hgf x) (mem_univ _)
  rw [tangentMap_id] at h2
  exact h1.symm.trans h2

theorem injective_tangentMap_of_leftInverse (hf : P.IsScSmoothMap Q f) (hg : Q.IsScSmoothMap P g)
    (hgf : ∀ x, g (f x) = x) : Injective (tangentMap hf) :=
  LeftInverse.injective (tangentMap_tangentMap_of_leftInverse hf hg hgf)

/-- **The image of a smooth finite-dimensional submanifold under an sc-smooth map with an
sc-smooth left inverse** is a smooth finite-dimensional submanifold (Definition 4.2.1): if `s` is
an sc⁺-retraction onto `A ∩ W`, then `f ∘ s ∘ g` is one onto `f(A) ∩ g⁻¹(W)`. -/
theorem IsSmoothSubmanifold.image_of_leftInverse (hf : P.IsScSmoothMap Q f)
    (hg : Q.IsScSmoothMap P g) (hgf : ∀ x, g (f x) = x) {A : Set X}
    (hA : P.IsSmoothSubmanifold A) : Q.IsSmoothSubmanifold (f '' A) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨W, hW, haW, s, hs, himg⟩ := hA a ha
  have hW'o : IsOpen (univ ∩ g ⁻¹' W) := hg.continuousOn.isOpen_inter_preimage isOpen_univ hW
  have hgW' : MapsTo g (univ ∩ g ⁻¹' W) W := fun y hy => hy.2
  have hmapsW' : MapsTo (f ∘ s ∘ g) (univ ∩ g ⁻¹' W) (univ ∩ g ⁻¹' W) := fun y hy =>
    ⟨mem_univ _, by change g (f (s (g y))) ∈ W; rw [hgf]; exact hs.mapsTo hy.2⟩
  obtain ⟨w₀, hw₀, hw₀a⟩ : a ∈ s '' W := himg ▸ ⟨ha, haW⟩
  have ha1 : a ∈ P.levelSet 1 := hw₀a ▸ hs.mem_levelSet w₀ hw₀
  have hg_sm : Q.IsScSmoothOn P g (univ ∩ g ⁻¹' W) := hg.mono hW'o (subset_univ _)
  have hfU : P.IsScSmoothOn Q f univ := hf
  refine ⟨univ ∩ g ⁻¹' W, hW'o, ⟨mem_univ _, by rw [mem_preimage, hgf]; exact haW⟩,
    f ∘ s ∘ g, ⟨?_, hmapsW', fun y hy => ?_, fun y hy => ?_, fun y₀ => ?_⟩, ?_⟩
  · exact hfU.comp (hs.isScSmoothOn.comp hg_sm hgW') fun y _ => mem_univ _
  · simp only [Function.comp_apply]
    rw [hgf, hs.idem _ (hgW' hy)]
  · exact hfU.mapsTo_levelSet 1 ⟨mem_univ _, hs.mem_levelSet _ (hgW' hy)⟩
  · let x₀ : P.Level 1 := P.levelMk 1 a ha1
    let F₁ : P.Level 1 → Q.Level 1 := fun x => Q.toLevelOne y₀ (f (P.levelVal 1 x))
    have hF₁ : P.shift.IsScSmoothOn Q.shift F₁ {x | P.levelVal 1 x ∈ univ} :=
      hfU.levelOne fun x hx =>
        levelVal_toLevelOne y₀ (hfU.mapsTo_levelSet 1 ⟨hx, levelVal_mem x⟩)
    have hin : Q.IsScSmoothOn P.shift (P.toLevelOne x₀ ∘ s ∘ g) (univ ∩ g ⁻¹' W) :=
      (hs.isScSmoothOn_one x₀).comp hg_sm hgW'
    refine (hF₁.comp hin fun y _ => mem_univ _).congr fun y hy => ?_
    simp only [Function.comp_apply, F₁]
    rw [levelVal_toLevelOne x₀ (hs.mem_levelSet _ (hgW' hy))]
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : s (g y) ∈ s '' W := ⟨g y, hgW' hy, rfl⟩
      rw [himg] at h1
      exact ⟨⟨s (g y), h1.1, rfl⟩, hmapsW' hy⟩
    · rintro ⟨⟨a', ha', rfl⟩, hz⟩
      have ha'W : a' ∈ W := by
        have h2 := hz.2
        rwa [mem_preimage, hgf] at h2
      obtain ⟨w, hw, hwa⟩ : a' ∈ s '' W := himg ▸ ⟨ha', ha'W⟩
      refine ⟨f a', hz, ?_⟩
      simp only [Function.comp_apply]
      rw [hgf, ← hwa, hs.idem w hw]

/-- **`T_{f(a)} f(A) = Tf(T_aA)`** for an sc-smooth map `f` with an sc-smooth left inverse `g`
and a smooth finite-dimensional submanifold `A`: `Tf` maps the fixed vectors of `Ts` to those of
`T(f ∘ s ∘ g)`, and `Tg` maps them back. -/
theorem submanifoldTangent_image_of_leftInverse (hf : P.IsScSmoothMap Q f)
    (hg : Q.IsScSmoothMap P g) (hgf : ∀ x, g (f x) = x) {A : Set X}
    (hA : P.IsSmoothSubmanifold A) {a : X} (ha : a ∈ A) :
    Q.submanifoldTangent (f '' A) (f a) = tangentMap hf '' P.submanifoldTangent A a := by
  have hfA := hA.image_of_leftInverse hf hg hgf
  have hfU : P.IsScSmoothOn Q f univ := hf
  have hgU : Q.IsScSmoothOn P g univ := hg
  have efT : tangentMapOn hfU = tangentMap hf := tangentMapOn_univ hf
  have egT : tangentMapOn hgU = tangentMap hg := tangentMapOn_univ hg
  refine Subset.antisymm (fun β hβ => ?_) ?_
  · obtain ⟨hβa, d', hy', hfix'⟩ := hβ
    set d := hA.data ha
    have had : a ∈ d.V := hA.mem_data_V ha
    have hs' := d'.isScPlusRetractionOn.isScSmoothOn
    have hs'a : d'.s (f a) = f a := d'.apply_eq_self ⟨⟨a, ha, rfl⟩, hy'⟩
    set W := d'.V ∩ d'.s ⁻¹' (univ ∩ g ⁻¹' d.V)
    have hW : IsOpen W := hs'.continuousOn.isOpen_inter_preimage d'.isOpen
      (hgU.continuousOn.isOpen_inter_preimage isOpen_univ d.isOpen)
    have haW : f a ∈ W := ⟨hy', by
      change d'.s (f a) ∈ univ ∩ g ⁻¹' d.V
      rw [hs'a]; exact ⟨mem_univ _, by rw [mem_preimage, hgf]; exact had⟩⟩
    have hβW : β ∈ Q.tangentPreimage W := by change _ ∈ W; rw [hβa]; exact haW
    have hmem : ∀ w ∈ W, ∃ a' ∈ A, d'.s w = f a' := fun w hw => by
      have h2 : d'.s w ∈ d'.s '' d'.V := ⟨w, hw.1, rfl⟩
      rw [d'.image] at h2
      obtain ⟨a', ha', h3⟩ := h2.1
      exact ⟨a', ha', h3.symm⟩
    have hgs : Q.IsScSmoothOn P (g ∘ d'.s) W :=
      hgU.comp (hs'.mono hW fun _ hw => hw.1) fun _ _ => mem_univ _
    have h1 : tangentMapOn hgU (d'.tmap β) = tangentMapOn hgs β :=
      tangentMapOn_tangentMapOn_eq_of_eqOn hs' hgU hgs hW (fun _ hw => hw.1) subset_rfl
        (fun _ _ => mem_univ _) (fun _ _ => rfl) hβW
    rw [hfix'] at h1
    have heq : EqOn (d.s ∘ (g ∘ d'.s)) (g ∘ d'.s) W := fun w hw => by
      obtain ⟨a', ha', h3⟩ := hmem w hw
      have h4 : g (d'.s w) ∈ d.V := hw.2.2
      simp only [Function.comp_apply]
      rw [h3, hgf] at h4 ⊢
      exact d.apply_eq_self ⟨ha', h4⟩
    have h3 := tangentMapOn_tangentMapOn_eq_of_eqOn hgs d.isScPlusRetractionOn.isScSmoothOn hgs
      hW subset_rfl subset_rfl (fun w hw => hw.2.2) heq hβW
    have heq' : EqOn (f ∘ (g ∘ d'.s)) d'.s W := fun w hw => by
      obtain ⟨a', ha', h3⟩ := hmem w hw
      simp only [Function.comp_apply]
      rw [h3, hgf]
    have h5 := tangentMapOn_tangentMapOn_eq_of_eqOn hgs hfU hs' hW subset_rfl
      (fun _ hw => hw.1) (fun _ _ => mem_univ _) heq' hβW
    have h6 : tangentMapOn hs' β = β := hfix'
    rw [← h1, h6, efT, egT] at h5
    refine ⟨tangentMap hg β, ⟨?_, d, had, ?_⟩, h5⟩
    · rw [levelVal_tangentProj_tangentMap, hβa, hgf]
    · change tangentMapOn _ (tangentMap hg β) = tangentMap hg β
      rw [← egT, h1]
      exact h3
  · rintro _ ⟨α, hα, rfl⟩
    obtain ⟨hαa, d, hy, hfix⟩ := hα
    set d' := hfA.data ⟨a, ha, rfl⟩
    have hfa' : f a ∈ d'.V := hfA.mem_data_V ⟨a, ha, rfl⟩
    have hs := d.isScPlusRetractionOn.isScSmoothOn
    have hsa : d.s a = a := d.apply_eq_self ⟨ha, hy⟩
    set W := d.V ∩ d.s ⁻¹' (univ ∩ f ⁻¹' d'.V)
    have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage d.isOpen
      (hfU.continuousOn.isOpen_inter_preimage isOpen_univ d'.isOpen)
    have haW : a ∈ W := ⟨hy, by
      change d.s a ∈ univ ∩ f ⁻¹' d'.V; rw [hsa]; exact ⟨mem_univ _, hfa'⟩⟩
    have hαW : α ∈ P.tangentPreimage W := by change _ ∈ W; rw [hαa]; exact haW
    have hfs : P.IsScSmoothOn Q (f ∘ d.s) W :=
      hfU.comp (hs.mono hW fun _ hw => hw.1) fun _ _ => mem_univ _
    have h1 : tangentMapOn hfU (d.tmap α) = tangentMapOn hfs α :=
      tangentMapOn_tangentMapOn_eq_of_eqOn hs hfU hfs hW (fun _ hw => hw.1) subset_rfl
        (fun _ _ => mem_univ _) (fun _ _ => rfl) hαW
    rw [hfix] at h1
    have heq : EqOn (d'.s ∘ (f ∘ d.s)) (f ∘ d.s) W := fun w hw => by
      have h2 : d.s w ∈ d.s '' d.V := ⟨w, hw.1, rfl⟩
      rw [d.image] at h2
      exact d'.apply_eq_self ⟨⟨d.s w, h2.1, rfl⟩, hw.2.2⟩
    have h3 := tangentMapOn_tangentMapOn_eq_of_eqOn hfs d'.isScPlusRetractionOn.isScSmoothOn hfs
      hW subset_rfl subset_rfl (fun w hw => hw.2.2) heq hαW
    refine ⟨?_, d', hfa', ?_⟩
    · rw [levelVal_tangentProj_tangentMap, hαa]
    · change tangentMapOn _ (tangentMap hf α) = tangentMap hf α
      rw [← efT, h1]
      exact h3

/-! ### Chart vectors of tangent maps -/

/-- If `f` is, in the charts `φ` and `ψ`, the restriction of an sc-operator `L`, then the chart
vector of `Tf(α)` is `L` of the chart vector of `α`. -/
theorem chartVec_tangentMap_of_scOperator (hf : P.IsScSmoothMap Q f) {φ : MChart X}
    (hφ : P.IsChart φ) {ψ : MChart Y} (hψ : Q.IsChart ψ) (L : ScOperator φ.model.E ψ.model.E)
    (hL : ∀ x ∈ φ.source, f x ∈ ψ.source ∧ ψ (f x) = L 0 (φ x)) {α : P.TangentSpace}
    (hα : P.levelVal 1 (P.tangentProj α) ∈ φ.source) :
    chartVec hψ (tangentMap hf α) = L 0 (chartVec hφ α) := by
  have hfU : P.IsScSmoothOn Q f univ := hf
  have hdom : TangentPre.fdomOn univ φ f ψ = φ.source := by
    ext x
    simp only [TangentPre.fdomOn, mem_inter_iff, mem_univ, true_and, mem_preimage]
    exact ⟨fun h => h.1, fun h => ⟨h, (hL x h).1⟩⟩
  have hαW : α ∈ P.tangentPreimage (TangentPre.fdomOn univ φ f ψ) := by rw [hdom]; exact hα
  have h1 := tangentChartMap_tangentMapOn hfU hφ hψ hαW
  rw [tangentMapOn_univ hf] at h1
  have hO : IsScRetract φ.model.E φ.model.C (φ '' TangentPre.fdomOn univ φ f ψ) :=
    φ.isScRetract_image (TangentPre.fdomOn_subset univ φ f ψ) (TangentPre.isOpen_fdomOn hfU φ ψ)
  have hsm := TangentPre.isScSmoothRetractMap_coordOn hfU hφ hψ subset_rfl
    (TangentPre.isOpen_fdomOn hfU φ ψ)
  have heq : EqOn (ψ ∘ f ∘ φ.symm) (L 0) (φ '' TangentPre.fdomOn univ φ f ψ) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxφ := TangentPre.fdomOn_subset univ φ f ψ hx
    simp only [Function.comp_apply]
    rw [φ.symm_apply_apply hxφ]
    exact (hL x hxφ).2
  have hαφ : α ∈ tangentChartSet φ := hα
  have hmem : tangentChartMap hφ α ∈ retractTangent φ.model.E φ.model.C
      (φ '' TangentPre.fdomOn univ φ f ψ) := by
    refine (TangentPre.mem_retractTangent_image_iff (TangentPre.fdomOn_subset univ φ f ψ)
      (TangentPre.isOpen_fdomOn hfU φ ψ) ?_).2 (tangentChartMap_mem hφ hαφ)
    rw [tangentChartMap_fst hφ hαφ, P.toBase_levelLift hφ hαφ (levelVal_mem _)]
    exact ⟨_, hαW, rfl⟩
  unfold chartVec
  rw [h1, retractTangentMap_congr hsm hO heq hmem,
    retractTangentMap_scOperator L hO (O' := univ) (mapsTo_univ _ _) hmem]

/-- The tangent map of a constant map has chart vectors `0`. -/
theorem chartVec_tangentMap_of_const (hf : P.IsScSmoothMap Q f) {z : Y} (hfz : ∀ x, f x = z)
    {φ : MChart X} (hφ : P.IsChart φ) {ψ : MChart Y} (hψ : Q.IsChart ψ) (hz : z ∈ ψ.source)
    {α : P.TangentSpace} (hα : P.levelVal 1 (P.tangentProj α) ∈ φ.source) :
    chartVec hψ (tangentMap hf α) = 0 := by
  have hfU : P.IsScSmoothOn Q f univ := hf
  have hdom : TangentPre.fdomOn univ φ f ψ = φ.source := by
    ext x
    simp only [TangentPre.fdomOn, mem_inter_iff, mem_univ, true_and, mem_preimage]
    exact ⟨fun h => h.1, fun h => ⟨h, by rw [hfz]; exact hz⟩⟩
  have hαW : α ∈ P.tangentPreimage (TangentPre.fdomOn univ φ f ψ) := by rw [hdom]; exact hα
  have h1 := tangentChartMap_tangentMapOn hfU hφ hψ hαW
  rw [tangentMapOn_univ hf] at h1
  have hO : IsScRetract φ.model.E φ.model.C (φ '' TangentPre.fdomOn univ φ f ψ) :=
    φ.isScRetract_image (TangentPre.fdomOn_subset univ φ f ψ) (TangentPre.isOpen_fdomOn hfU φ ψ)
  have hsm := TangentPre.isScSmoothRetractMap_coordOn hfU hφ hψ subset_rfl
    (TangentPre.isOpen_fdomOn hfU φ ψ)
  have hαφ : α ∈ tangentChartSet φ := hα
  have hmem : tangentChartMap hφ α ∈ retractTangent φ.model.E φ.model.C
      (φ '' TangentPre.fdomOn univ φ f ψ) := by
    refine (TangentPre.mem_retractTangent_image_iff (TangentPre.fdomOn_subset univ φ f ψ)
      (TangentPre.isOpen_fdomOn hfU φ ψ) ?_).2 (tangentChartMap_mem hφ hαφ)
    rw [tangentChartMap_fst hφ hαφ, P.toBase_levelLift hφ hαφ (levelVal_mem _)]
    exact ⟨_, hαW, rfl⟩
  obtain ⟨R, hR⟩ := hO
  have hp1 : (tangentChartMap hφ α).1 ∈ φ.model.E.lvlSet R.U 1 := by
    have h := hmem
    rw [← hR, retractTangent_eq] at h
    exact R.tangent_subset h
  unfold chartVec
  rw [h1, retractTangentMap_eqOn hsm R hR hmem]
  change scDeriv R.U ((ψ ∘ f ∘ φ.symm) ∘ R) (tangentChartMap hφ α).1 (tangentChartMap hφ α).2 = 0
  rw [scDeriv_eq_zero_of_eqOn_const (hsm.comp_isScSmooth R hR).isSc1 R.isScDomain (q := ψ z)
    (fun u _ => by simp only [Function.comp_apply, hfz]) hp1]
  rfl

/-! ### The slice `{q} × A` of a product -/

section Slice

variable {T : Type v} [TopologicalSpace T] [T2Space T] [ParacompactSpace T] {P₀ : MPolyfold T}
  [ParacompactSpace (T × X)] {q : T}

/-- **The chart vector of `Tι(α)`, `ι(x) = (q, x)`, in a product chart** is `(0, h)` for the
chart vector `h` of `α`. -/
theorem chartVec_tangentMap_prodMk (hι : P.IsScSmoothMap (P₀.prod P) fun x => (q, x))
    {χ : MChart T} (hχ : P₀.IsChart χ) (hq : q ∈ χ.source) {φ : MChart X} (hφ : P.IsChart φ)
    {α : P.TangentSpace} (hα : P.levelVal 1 (P.tangentProj α) ∈ φ.source) :
    chartVec (hχ.prod hφ) (tangentMap hι α) = ((0 : χ.model.E 0), chartVec hφ α) := by
  have hbase : (P₀.prod P).levelVal 1 ((P₀.prod P).tangentProj (tangentMap hι α)) ∈
      (χ.prod φ).source := by
    rw [levelVal_tangentProj_tangentMap]
    exact ⟨hq, hα⟩
  have h1 := chartVec_tangentMap_of_scOperator (isScSmoothMap_fst P₀ P)
    (hχ.prod hφ) hχ (χ.model.E.prodFstOp φ.model.E) (fun x hx => ⟨hx.1, rfl⟩) hbase
  have h2 := chartVec_tangentMap_of_scOperator (isScSmoothMap_snd P₀ P)
    (hχ.prod hφ) hφ (χ.model.E.prodSndOp φ.model.E) (fun x hx => ⟨hx.2, rfl⟩) hbase
  rw [tangentMap_tangentMap_of_leftInverse hι (isScSmoothMap_snd P₀ P) (fun _ => rfl)] at h2
  have h3 : tangentMap (isScSmoothMap_fst P₀ P) (tangentMap hι α) =
      tangentMap ((isScSmoothMap_fst P₀ P).comp hι) α :=
    (congrFun (tangentMap_comp _ hι) α).symm
  rw [h3, chartVec_tangentMap_of_const _ (fun _ => rfl) hφ hχ hq hα] at h1
  exact Prod.ext h1.symm h2.symm

variable (hι : P.IsScSmoothMap (P₀.prod P) fun x => (q, x))
include hι

/-- `{q} × A` is a smooth finite-dimensional submanifold of the product. -/
theorem IsSmoothSubmanifold.image_prodMk {A : Set X} (hA : P.IsSmoothSubmanifold A) :
    (P₀.prod P).IsSmoothSubmanifold ((fun x => (q, x)) '' A) :=
  hA.image_of_leftInverse hι (isScSmoothMap_snd P₀ P) fun _ => rfl

/-- `T_{(q, a)}({q} × A) = Tι(T_aA)`. -/
theorem submanifoldTangent_image_prodMk {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : X}
    (ha : a ∈ A) :
    (P₀.prod P).submanifoldTangent ((fun x => (q, x)) '' A) (q, a) =
      tangentMap hι '' P.submanifoldTangent A a :=
  submanifoldTangent_image_of_leftInverse hι (isScSmoothMap_snd P₀ P) (fun _ => rfl) hA ha

/-- **`T_{(q, a)}({q} × A)` in a product chart** is `{0} × T_aA`. -/
theorem chartTangent_image_prodMk {χ : MChart T} (hχ : P₀.IsChart χ) (hq : q ∈ χ.source)
    {φ : MChart X} (hφ : P.IsChart φ) {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : X}
    (ha : a ∈ A) (haφ : a ∈ φ.source) :
    (P₀.prod P).chartTangent (hχ.prod hφ) ((fun x => (q, x)) '' A) (q, a) =
      (fun v => ((0 : χ.model.E 0), v)) '' P.chartTangent hφ A a := by
  unfold chartTangent
  rw [submanifoldTangent_image_prodMk hι hA ha, image_image, image_image]
  refine image_congr fun α hα => ?_
  exact chartVec_tangentMap_prodMk hι hχ hq hφ
    (by rw [levelVal_tangentProj_of_mem hα]; exact haφ)

/-- **`{q} × A` has the dimension of `A`.** -/
theorem IsSubmanifoldOfDim.image_prodMk {A : Set X} {n : ℕ}
    (hA : P.IsSubmanifoldOfDim A n) :
    (P₀.prod P).IsSubmanifoldOfDim ((fun x => (q, x)) '' A) n := by
  have hA' := hA.1.image_prodMk hι
  refine ⟨hA', ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨k, hk⟩ := hA'.exists_hasDimAt (a := (q, a)) ⟨a, ha, rfl⟩
  obtain ⟨χ, hχ, hqχ⟩ := P₀.exists_isChart_mem_source q
  obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a
  obtain ⟨NA, hNA, -⟩ := exists_submodule_chartTangent hφ hA.1 ha haφ
  obtain ⟨NB, hNB, -⟩ := exists_submodule_chartTangent (hχ.prod hφ) hA' (y := (q, a))
    ⟨a, ha, rfl⟩ ⟨hqχ, haφ⟩
  have hra := finrank_chartTangent hφ (hA.2 a ha) hA.1 haφ hNA
  have hrb := finrank_chartTangent (hχ.prod hφ) hk hA' (y := (q, a)) ⟨hqχ, haφ⟩ hNB
  have hmap : NB = NA.map (LinearMap.inr ℝ (χ.model.E 0) (φ.model.E 0)) := by
    refine SetLike.coe_injective ?_
    rw [hNB, chartTangent_image_prodMk hι hχ hqχ hφ hA.1 ha haφ, ← hNA]
    rfl
  have hfr : Module.finrank ℝ NB = Module.finrank ℝ NA := by
    rw [hmap]
    exact (Submodule.equivMapOfInjective _ LinearMap.inr_injective NA).finrank_eq.symm
  have hkn : k = n := by rw [← hrb, hfr, hra]
  exact hkn ▸ hk

/-! ### Graph charts and orientations of `{q} × N` -/

/-- **The graph chart of `{q} × N` in a product chart**, from a graph chart `c` of `N`: the same
coordinates, the parametrization `u ↦ (q, c.q u)` and the derivative `(0, c.L)`. -/
def GraphChart.prodMk {n : ℕ} {N : Set X} (c : P.GraphChart n N)
    (hN : P.IsSmoothSubmanifold N) {χ : MChart T} (hχ : P₀.IsChart χ) (hq : q ∈ χ.source) :
    (P₀.prod P).GraphChart n ((fun x => (q, x)) '' N) where
  φ := χ.prod c.φ
  isChart := hχ.prod c.isChart
  subset_source := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hq, c.subset_source hy⟩
  p := c.p.comp (ContinuousLinearMap.snd ℝ (χ.model.E 0) (c.φ.model.E 0))
  q := fun u => (q, c.q u)
  q_coord := by
    rintro _ ⟨y, hy, rfl⟩
    change (q, c.q (c.p (c.φ y))) = (q, y)
    rw [c.q_coord y hy]
  L := fun z => (ContinuousLinearMap.inr ℝ (χ.model.E 0) (c.φ.model.E 0)).comp (c.L z.2)
  measurableSet_dom := by
    have h : (fun z : T × X => c.p (c.φ z.2)) '' ((fun x => (q, x)) '' N) =
        (fun y => c.p (c.φ y)) '' N := by rw [image_image]
    exact h ▸ c.measurableSet_dom
  p_L := by
    rintro _ ⟨y, hy, rfl⟩ v
    exact c.p_L y hy v
  range_L := by
    rintro _ ⟨y, hy, rfl⟩
    rw [chartTangent_image_prodMk hι hχ hq c.isChart hN hy (c.subset_source hy),
      ← c.range_L y hy, ← range_comp]
    rfl
  hasFDerivWithinAt := by
    rintro _ ⟨y, hy, rfl⟩
    have hset : (fun z : T × X => c.p (c.φ z.2)) '' ((fun x => (q, x)) '' N) =
        (fun y => c.p (c.φ y)) '' N := by rw [image_image]
    have key := (hasFDerivWithinAt_const (χ q) (c.p (c.φ y))
      ((fun y => c.p (c.φ y)) '' N)).prodMk (c.hasFDerivWithinAt y hy)
    change HasFDerivWithinAt (fun u => (χ q, c.φ (c.q u)))
      ((ContinuousLinearMap.inr ℝ (χ.model.E 0) (c.φ.model.E 0)).comp (c.L y))
      ((fun z : T × X => c.p (c.φ z.2)) '' ((fun x => (q, x)) '' N)) (c.p (c.φ y))
    have hL : (ContinuousLinearMap.inr ℝ (χ.model.E 0) (c.φ.model.E 0)).comp (c.L y) =
        (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] χ.model.E 0).prod (c.L y) :=
      ContinuousLinearMap.ext fun v => Prod.ext rfl rfl
    rw [hset, hL]
    exact key
  continuousOn_L := by
    have h1 : ContinuousOn (fun z : T × X => c.L z.2) ((fun x => (q, x)) '' N) :=
      c.continuousOn_L.comp continuous_snd.continuousOn (by
        rintro _ ⟨y, hy, rfl⟩; exact hy)
    exact ((ContinuousLinearMap.compL ℝ _ _ _
      (ContinuousLinearMap.inr ℝ (χ.model.E 0) (c.φ.model.E 0))).continuous).comp_continuousOn h1

section GraphChartProdMk

variable {n : ℕ} {N : Set X} (c : P.GraphChart n N) (hN : P.IsSmoothSubmanifold N)
  {χ : MChart T} (hχ : P₀.IsChart χ) (hq : q ∈ χ.source)

/-- The coordinate of `(q, y)` in the graph chart of `{q} × N` is the coordinate of `y`. -/
theorem GraphChart.prodMk_coord (y : X) : (c.prodMk hι hN hχ hq).coord (q, y) = c.coord y := rfl

theorem GraphChart.prodMk_coord_image (A : Set X) :
    (c.prodMk hι hN hχ hq).coord '' ((fun x => (q, x)) '' A) = c.coord '' A := by
  rw [image_image]; rfl

theorem GraphChart.prodMk_dom : (c.prodMk hι hN hχ hq).dom = c.dom :=
  GraphChart.prodMk_coord_image hι c hN hχ hq N

theorem GraphChart.prodMk_q (u : EuclideanSpace ℝ (Fin n)) :
    (c.prodMk hι hN hχ hq).q u = (q, c.q u) := rfl

/-- The frame of the graph chart of `{q} × N` at `(q, y)` is `Tι` of the frame at `y`. -/
theorem GraphChart.prodMk_tvec {y : X} (hy : y ∈ N) (i : Fin n) :
    (c.prodMk hι hN hχ hq).tvec (q, y) i = tangentMap hι (c.tvec y i) := by
  have hfy : (q, y) ∈ (fun x => (q, x)) '' N := ⟨y, hy, rfl⟩
  have hα : P.levelVal 1 (P.tangentProj (c.tvec y i)) = y :=
    levelVal_tangentProj_of_mem (c.tvec_mem hy i)
  refine chartVec_injOn (c.prodMk hι hN hχ hq).isChart
    ((c.prodMk hι hN hχ hq).subset_source hfy)
    (levelVal_tangentProj_of_mem ((c.prodMk hι hN hχ hq).tvec_mem hfy i)) ?_ ?_
  · change (P₀.prod P).levelVal 1 ((P₀.prod P).tangentProj (tangentMap hι (c.tvec y i))) = (q, y)
    rw [levelVal_tangentProj_tangentMap, hα]
  · rw [(c.prodMk hι hN hχ hq).chartVec_tvec hfy]
    refine Eq.trans ?_ (chartVec_tangentMap_prodMk hι hχ hq c.isChart
      (by rw [hα]; exact c.subset_source hy)).symm
    rw [c.chartVec_tvec hy]
    rfl

end GraphChartProdMk

/-- **The orientation of `{q} × M` pushed forward from `M`**: the positive frames of
`T_{(q, y)}({q} × M)` are the images `Tι ∘ v` of the positive frames of `T_yM`. -/
def SubmanifoldOrientation.prodMk {M : Set X} {n : ℕ} (o : P.SubmanifoldOrientation M n)
    (hM : P.IsSmoothSubmanifold M) :
    (P₀.prod P).SubmanifoldOrientation ((fun x => (q, x)) '' M) n where
  frames z := (fun v => tangentMap hι ∘ v) '' o.frames z.2
  isOrientedAt := by
    rintro _ ⟨y, hy, rfl⟩
    rw [submanifoldTangent_image_prodMk hι hM hy]
    have h := o.isOrientedAt y hy
    have hL := h.1
    obtain ⟨χ, hχ, hqχ⟩ := P₀.exists_isChart_mem_source q
    obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
    obtain ⟨N, hN, hfin, hrank, ω, hO⟩ := h.isChartOrientation hφ hyφ
    have hcv : ∀ α ∈ P.submanifoldTangent M y, chartVec (hχ.prod hφ) (tangentMap hι α) =
        ((0 : χ.model.E 0), chartVec hφ α) := fun α hα =>
      chartVec_tangentMap_prodMk hι hχ hqχ hφ (by rw [hL α hα]; exact hyφ)
    let j : φ.model.E 0 →ₗ[ℝ] (χ.prod φ).model.E 0 := LinearMap.inr ℝ (χ.model.E 0) (φ.model.E 0)
    let e : N ≃ₗ[ℝ] N.map j := Submodule.equivMapOfInjective j LinearMap.inr_injective N
    have he : ∀ v : N, ((e v : N.map j) : (χ.prod φ).model.E 0) =
        ((0 : χ.model.E 0), (v : φ.model.E 0)) := fun _ => rfl
    refine ⟨?_, χ.prod φ, hχ.prod hφ, ⟨hqχ, hyφ⟩, N.map j, ?_, e.finiteDimensional,
      e.finrank_eq.symm.trans hrank, Orientation.map (Fin n) e ω, ?_⟩
    · rintro _ ⟨α, hα, rfl⟩
      rw [levelVal_tangentProj_tangentMap, hL α hα]
    · refine (Submodule.map_coe j N).trans ?_
      rw [hN, image_image, image_image]
      exact image_congr fun α hα => (hcv α hα).symm
    · change (fun v => tangentMap hι ∘ v) '' o.frames y = _
      have hO' : o.frames y = chartFrames hφ (P.submanifoldTangent M y) N ω := hO
      rw [hO']
      ext w
      constructor
      · rintro ⟨v, ⟨hv, b, hb, hbo⟩, rfl⟩
        refine ⟨fun i => mem_image_of_mem _ (hv i), b.map e, fun i => ?_, ?_⟩
        · refine (congrArg Subtype.val (Module.Basis.map_apply b e i)).trans ((he (b i)).trans ?_)
          rw [hb i]
          exact (hcv _ (hv i)).symm
        · exact (Module.Basis.orientation_map b e).trans (congrArg _ hbo)
      · rintro ⟨hw, b, hb, hbo⟩
        choose u hu hfu using hw
        refine ⟨u, ⟨hu, b.map e.symm, fun i => ?_, ?_⟩, funext hfu⟩
        · have h1 : ((e (e.symm (b i)) : N.map j) : (χ.prod φ).model.E 0) =
              ((0 : χ.model.E 0), chartVec hφ (u i)) :=
            (congrArg Subtype.val (e.apply_symm_apply (b i))).trans ((hb i).trans
              ((congrArg (chartVec (hχ.prod hφ)) (hfu i).symm).trans (hcv _ (hu i))))
          exact (congrArg Subtype.val (Module.Basis.map_apply b e.symm i)).trans
            (congrArg Prod.snd ((he (e.symm (b i))).symm.trans h1))
        · refine (Module.Basis.orientation_map b e.symm).trans
            ((congrArg (Orientation.map (Fin n) e.symm) hbo).trans ?_)
          rw [← Orientation.map_symm]
          exact (Orientation.map (Fin n) e).symm_apply_apply ω
  continuous hn := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨φ, hφ, V, hV, hyV, hVφ, e, he, hc⟩ := o.continuous hn y hy
    obtain ⟨χ, hχ, hqχ⟩ := P₀.exists_isChart_mem_source q
    refine ⟨χ.prod φ, hχ.prod hφ, χ.source ×ˢ V, χ.isOpen_source.prod hV, ⟨hqχ, hyV⟩,
      prod_mono subset_rfl hVφ, fun w i => tangentMap hι (e w.2 i), ?_, ?_⟩
    · rintro _ ⟨⟨u, hu, rfl⟩, hV'⟩
      exact ⟨e u, he u ⟨hu, hV'.2⟩, rfl⟩
    · have hmaps : MapsTo (Prod.snd : T × X → X)
          ((fun x => (q, x)) '' M ∩ χ.source ×ˢ V) (M ∩ V) := by
        rintro _ ⟨⟨u, hu, rfl⟩, hV'⟩
        exact ⟨hu, hV'.2⟩
      have hc1 : ContinuousOn (fun w : T × X => fun i => chartVec hφ (e w.2 i))
          ((fun x => (q, x)) '' M ∩ χ.source ×ˢ V) :=
        hc.comp continuous_snd.continuousOn hmaps
      have hc2 : Continuous (fun g : Fin n → φ.model.E 0 => fun i =>
          ((0 : χ.model.E 0), g i)) :=
        continuous_pi fun i => continuous_const.prodMk (continuous_apply i)
      refine (hc2.comp_continuousOn hc1).congr fun w hw => ?_
      obtain ⟨⟨u, hu, rfl⟩, hV'⟩ := hw
      funext i
      exact chartVec_tangentMap_prodMk hι hχ hqχ hφ (by
        rw [((o.isOrientedAt u hu).mem_carrier (he u ⟨hu, hV'.2⟩) i).1]; exact hVφ hV'.2)

@[simp] theorem SubmanifoldOrientation.prodMk_frames {M : Set X} {n : ℕ}
    (o : P.SubmanifoldOrientation M n) (hM : P.IsSmoothSubmanifold M) (z : T × X) :
    (o.prodMk hι hM).frames z = (fun v => tangentMap hι ∘ v) '' o.frames z.2 := rfl

/-- A frame is positive for `o` iff its image under `Tι` is positive for the pushed-forward
orientation of `{q} × M`. -/
theorem SubmanifoldOrientation.prodMk_frames_iff {M : Set X} {n : ℕ}
    (o : P.SubmanifoldOrientation M n) (hM : P.IsSmoothSubmanifold M) (y : X)
    (α : Fin n → P.TangentSpace) :
    (fun i => tangentMap hι (α i)) ∈ (o.prodMk hι hM).frames (q, y) ↔ α ∈ o.frames y := by
  constructor
  · rintro ⟨v, hv, hve⟩
    have : v = α := funext fun i =>
      injective_tangentMap_of_leftInverse hι (isScSmoothMap_snd P₀ P) (fun _ => rfl)
        (congrFun hve i)
    exact this ▸ hv
  · exact fun h => ⟨α, h, rfl⟩

end Slice

end MPolyfold

end Polyfold
