import Polyfold.Chapter3.UntamedBundle
import Polyfold.Chapter3.NonVacuity
import Polyfold.Chapter3.GermVsChart
import Polyfold.Chapter3.RestrictOpenGerms
import Polyfold.Chapter3.TameGermTransfer
import Polyfold.Chapter4.Recentre
import Polyfold.Chapter4.LocalStrongBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §3.1 and §3.6:
**Definitions 3.1.16 = 3.6.4** (sc-Fredholm section, pp. 97, 135) and **Definition 2.6.4** (strong
bundle charts, p. 67), for the untamed example of `UntamedBundle.lean`.  Gap G.79.

# The untamed example: germ data at the points `t ≠ 0`, and the section is sc-Fredholm

## The text, paraphrased

(Definition 3.6.4, p. 135) An sc-smooth section `f` of a strong bundle is an sc-Fredholm section
if it is regularizing and `(f, x)` is an sc-Fredholm germ (Definition 3.6.3: germ data in a strong
bundle chart around `x`) at every smooth point `x`.

## What is formalized

For the strong bundle `K → O` and the section `sec` of `UntamedBundle.lean`
(`O ≅ ℝ ∋ t`, fibre `0` for `t ≤ 0`, the line `ran π_t` for `0 < t < 1`):

* `Frame k J`: a frame of `K` over an open `J ⊆ (−∞, 1)`: sc-smooth maps
  `(t, s) ↦ fr_t(s) ∈ ran π_t` (`s ∈ ℝᵏ`, also into `X¹`) and `(t, h) ↦ co_t(h) ∈ ℝᵏ`, inverse to
  each other on `ran π_t`, in which the section is a constant `cst ∈ ℝᵏ`.
* `Frame.chart`: the strong bundle chart `Φ(((0, t), 0), (0, h)) = (t, co_t(h))` over the chart
  `t` of `O` restricted to `J`, onto `J ◁ ℝᵏ` with the identity retraction (a tame chart);
  `Frame.compatible_chart0`: **it is compatible with the chart `chart0` of the bundle** (the four
  transition maps on `[0]` and `[1]` and the two filtration conditions of Definition 2.6.4);
  `Frame.isChart_chart`.
* `Frame.isScFredholmGermInterior_sec`: at every `t₀ ∈ J` the germ of `sec` has germ data in the
  chart re-centred at `t₀` (filling: the constant principal part, `R = id`; sc⁺-germ: the same
  constant; the zero map is a basic germ), in a chart centred at an interior point of its
  quadrant, so tame germ data (`IsScFredholmGermInterior`).
* `frame0` (over `t < 0`, `k = 0`) and `frame1` (over `0 < t < 1`, `k = 1`: `fr_t(s) = s π_t v`,
  `co_t(h) = ν(h)/ν(π_t v)`).
* `isScFredholmSection2021_sec`: **`sec` is an sc-Fredholm section in the sense of 2021
  Definitions 3.1.16 = 3.6.4**; `isScFredholmGermTame_sec_of_ne`: at every point other than `x₀`
  the germ data can be taken in a tame chart.

## Choices

* The charts over `J` are built first with base chart `t` (not centred) and then re-centred with
  `StrongBundleChart.recentre`.
* In the frame over `0 < t < 1` the coordinate is normalised by the section (`co_t(π_t v) = 1`), so
  that the principal part is constant and no classical smoothness of `t ↦ ν(π_t v)` is needed;
  the division by `ν(π_t v) ≠ 0` is an sc-smooth operation (`isScSmooth_inv`).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace UntamedCorner

open ScOneExample Jump StrongRetr

/-! ### Frames of `K` over an open set of parameters -/

/-- **A frame of `K → O` over the open set `J ⊆ (−∞, 1)` of parameters `t`**: `fr_t : ℝᵏ → ran π_t`
and `co_t : X → ℝᵏ`, inverse to each other on `ran π_t`, sc-smooth in `(t, ·)` (`fr` also into
`X¹`), such that the section `t ↦ π_t v` has the constant coordinates `cst`. -/
structure Frame (k : ℕ) (J : Set ℝ) where
  /-- The coordinates `co_t(h) ∈ ℝᵏ`. -/
  co : ℝ → X 0 → (Fin k → ℝ)
  /-- The frame `fr_t(s) ∈ ran π_t`. -/
  fr : ℝ → (Fin k → ℝ) → X 0
  /-- The frame on level `1`. -/
  fr1 : ℝ → (Fin k → ℝ) → X 1
  /-- The coordinates of the section. -/
  cst : Fin k → ℝ
  isOpen : IsOpen J
  lt_one : ∀ t ∈ J, t < 1
  toBase_fr1 : ∀ t s, X.toBase 1 (fr1 t s) = fr t s
  proj_fr : ∀ t ∈ J, ∀ s, proj t (fr t s) = fr t s
  co_fr : ∀ t ∈ J, ∀ s, co t (fr t s) = s
  fr_co : ∀ t ∈ J, ∀ h, proj t h = h → fr t (co t h) = h
  co_linear : ∀ t ∈ J, IsLinearMap ℝ (co t)
  co_v : ∀ t ∈ J, co t (proj t v) = cst
  smooth_co : IsScSmooth (E := (ScBanach.const ℝ).prod X) (F := rnSc k) {p | p.1 ∈ J}
    (fun p => co p.1 p.2)
  smooth_fr : IsScSmooth (E := (ScBanach.const ℝ).prod (rnSc k)) (F := X) univ
    (fun p => fr p.1 p.2)
  smooth_fr1 : IsScSmooth (E := (ScBanach.const ℝ).prod (rnSc k)) (F := X.shift) univ
    (fun p => fr1 p.1 p.2)

/-- The domain `{t ∈ J}` of `ℝ¹`. -/
def UJ (J : Set ℝ) : Set (Fin 1 → ℝ) := {p | p 0 ∈ J}

namespace Frame

variable {k : ℕ} {J : Set ℝ} (Fr : Frame k J)

include Fr in
lemma isOpen_UJ : IsOpen (UJ J) := Fr.isOpen.preimage (continuous_apply 0)

include Fr in
lemma relOpen_UJ : IsRelOpenInQuadrant (rnSc 1) univ (UJ J) :=
  ⟨(rn_relOpen_univ 1).isPartialQuadrant, UJ J, Fr.isOpen_UJ, (inter_univ _).symm⟩

/-- The chart `t` of `O`, restricted to `{t ∈ J}`. -/
def baseChart : MChart Ob :=
  chartT.restrict (s := tco ⁻¹' J) (subset_univ _) (Fr.isOpen.preimage continuous_tco)

lemma isChart_baseChart : polyO.IsChart Fr.baseChart :=
  MPolyfold.IsChart.restrict polyO isChart_chartT (subset_univ _)
    (Fr.isOpen.preimage continuous_tco)

lemma baseChart_O : Fr.baseChart.model.O = UJ J := by
  change chartT '' (tco ⁻¹' J) = UJ J
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hp
    exact ⟨ptO (p 0) (Fr.lt_one _ hp), hp, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩

/-- The chart map `Φ(((0, t), 0), (0, h)) = (t, co_t(h))`. -/
def fwd (y : Kt) : (Fin 1 → ℝ) × (Fin k → ℝ) :=
  (fun _ => tco (kproj y), Fr.co (tco (kproj y)) (y : E 0 × F 0).2.2)

/-- The inverse `(t, s) ↦ (((0, t), 0), (0, fr_t(s)))`, as a map into `E₀ × F₀`. -/
def bwd (q : (Fin 1 → ℝ) × (Fin k → ℝ)) : E 0 × F 0 :=
  (((0, q.1 0), 0), (0, Fr.fr (q.1 0) q.2))

lemma bwd_mem_K {q : (Fin 1 → ℝ) × (Fin k → ℝ)} (hq : q.1 0 ∈ J) :
    Fr.bwd q ∈ R '' (U ×ˢ (univ : Set (F 0))) :=
  mem_K.2 ⟨mem_O.2 ⟨rfl, Fr.lt_one _ hq, rfl⟩, rfl, Fr.proj_fr _ hq _⟩

lemma bwd_fwd {y : Kt} (hy : tco (kproj y) ∈ J) : Fr.bwd (Fr.fwd y) = (y : E 0 × F 0) := by
  obtain ⟨h1, h2, h3⟩ := mem_K.1 y.2
  obtain ⟨ha, -, hw⟩ := mem_O.1 h1
  refine Prod.ext (Prod.ext (Prod.ext ha.symm rfl) hw.symm) (Prod.ext h2.symm ?_)
  exact Fr.fr_co _ hy _ h3

lemma fwd_bwd {q : (Fin 1 → ℝ) × (Fin k → ℝ)} (hq : q.1 0 ∈ J) (y : Kt)
    (hy : (y : E 0 × F 0) = Fr.bwd q) : Fr.fwd y = q := by
  have ht : tco (kproj y) = q.1 0 := by
    change (y : E 0 × F 0).1.1.2 = _
    rw [hy]; rfl
  refine Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; exact ht) ?_
  change Fr.co (tco (kproj y)) (y : E 0 × F 0).2.2 = q.2
  rw [ht, hy]
  exact Fr.co_fr _ hq _

open scoped Classical in
/-- The bundle chart over `J` as a partial equivalence. -/
def chartPE : PartialEquiv Kt ((Fin 1 → ℝ) × (Fin k → ℝ)) where
  toFun := Fr.fwd
  invFun q := if h : q.1 0 ∈ J then ⟨Fr.bwd q, Fr.bwd_mem_K h⟩ else ⟨0, zero_mem_K⟩
  source := kproj ⁻¹' (tco ⁻¹' J)
  target := UJ J ×ˢ univ
  map_source' y hy := ⟨hy, mem_univ _⟩
  map_target' q hq := by
    have h : q.1 0 ∈ J := hq.1
    dsimp only
    rw [dif_pos h]
    exact h
  left_inv' y hy := by
    have h : (Fr.fwd y).1 0 ∈ J := hy
    dsimp only
    rw [dif_pos h]
    exact Subtype.ext (Fr.bwd_fwd hy)
  right_inv' q hq := by
    have h : q.1 0 ∈ J := hq.1
    dsimp only
    rw [dif_pos h]
    exact Fr.fwd_bwd h _ rfl

lemma continuous_fr : Continuous fun p : ℝ × (Fin k → ℝ) => Fr.fr p.1 p.2 :=
  continuousOn_univ.1 Fr.smooth_fr.isSc1.isSc0.continuousOn_base

lemma continuous_bwd : Continuous Fr.bwd := by
  have h1 : Continuous fun q : (Fin 1 → ℝ) × (Fin k → ℝ) => q.1 0 :=
    (continuous_apply 0).comp continuous_fst
  have h2 : Continuous fun q : (Fin 1 → ℝ) × (Fin k → ℝ) => ((q.1 0, q.2) : ℝ × (Fin k → ℝ)) :=
    h1.prodMk continuous_snd
  have h3 : Continuous fun q : (Fin 1 → ℝ) × (Fin k → ℝ) => Fr.fr (q.1 0) q.2 :=
    Fr.continuous_fr.comp h2
  exact ((continuous_const.prodMk h1).prodMk continuous_const).prodMk
    (continuous_const.prodMk h3)

lemma continuousOn_fwd : ContinuousOn Fr.fwd (kproj ⁻¹' (tco ⁻¹' J)) := by
  have hco : ContinuousOn (fun p : ℝ × X 0 => Fr.co p.1 p.2) {p | p.1 ∈ J} :=
    Fr.smooth_co.isSc1.isSc0.continuousOn_base
  have hm : Continuous fun y : Kt => ((tco (kproj y), (y : E 0 × F 0).2.2) : ℝ × X 0) :=
    (continuous_tco.comp bundle.continuous).prodMk
      (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))
  refine ContinuousOn.prodMk ?_ (hco.comp hm.continuousOn fun y hy => hy)
  exact (continuous_pi fun _ => continuous_tco.comp bundle.continuous).continuousOn

/-- **The strong bundle chart of `K → O` over `{t ∈ J}`**, onto `J ◁ ℝᵏ` with the identity strong
bundle retraction (a tame chart). -/
def chart : StrongBundleChart polyO kproj where
  φ := Fr.baseChart
  isChart := Fr.isChart_baseChart
  F := rnSc k
  U := UJ J
  R := id
  relOpen := Fr.relOpen_UJ
  isRetraction := isStrongBundleRetraction_id_of_relOpen Fr.relOpen_UJ
  base_retract := by
    change (fun u => u) '' UJ J = Fr.baseChart.model.O
    rw [Fr.baseChart_O]; exact image_id' _
  toPartialEquiv := Fr.chartPE
  source_eq := rfl
  target_eq := (image_id _).symm
  continuousOn_toFun := Fr.continuousOn_fwd
  continuousOn_invFun := by
    classical
    change ContinuousOn (fun q : (Fin 1 → ℝ) × (Fin k → ℝ) =>
      if h : q.1 0 ∈ J then (⟨Fr.bwd q, Fr.bwd_mem_K h⟩ : Kt) else ⟨0, zero_mem_K⟩)
      (UJ J ×ˢ univ)
    rw [continuousOn_iff_continuous_domRestrict]
    have e : (UJ J ×ˢ (univ : Set (Fin k → ℝ))).domRestrict
        (fun q : (Fin 1 → ℝ) × (Fin k → ℝ) =>
          if h : q.1 0 ∈ J then (⟨Fr.bwd q, Fr.bwd_mem_K h⟩ : Kt) else ⟨0, zero_mem_K⟩) =
        fun q => ⟨Fr.bwd q.1, Fr.bwd_mem_K q.2.1⟩ := by
      funext q
      change (if h : (q : (Fin 1 → ℝ) × (Fin k → ℝ)).1 0 ∈ J then
        (⟨Fr.bwd q, Fr.bwd_mem_K h⟩ : Kt) else ⟨0, zero_mem_K⟩) = _
      rw [dif_pos (show (q : (Fin 1 → ℝ) × (Fin k → ℝ)).1 0 ∈ J from q.2.1)]
    rw [e]
    exact (Fr.continuous_bwd.comp continuous_subtype_val).subtype_mk _
  covers _ _ := rfl
  fiber_linear x hx := by
    have hJx : tco x ∈ J := hx
    have hk : ∀ v : kproj ⁻¹' {x}, kproj (v : Kt) = x := fun v => v.2
    constructor
    · intro v w
      change Fr.co (tco (kproj ((v + w : kproj ⁻¹' {x}) : Kt)))
          (((v + w : kproj ⁻¹' {x}) : Kt) : E 0 × F 0).2.2 =
        Fr.co (tco (kproj (v : Kt))) ((v : Kt) : E 0 × F 0).2.2 +
          Fr.co (tco (kproj (w : Kt))) ((w : Kt) : E 0 × F 0).2.2
      rw [hk, hk, hk]
      have h2 : (((v + w : kproj ⁻¹' {x}) : Kt) : E 0 × F 0).2.2 =
          ((v : Kt) : E 0 × F 0).2.2 + ((w : Kt) : E 0 × F 0).2.2 :=
        congrArg Prod.snd ((isLinearMap_fibEquiv x).map_add v w)
      rw [h2]
      exact (Fr.co_linear _ hJx).map_add _ _
    · intro a v
      change Fr.co (tco (kproj ((a • v : kproj ⁻¹' {x}) : Kt)))
          (((a • v : kproj ⁻¹' {x}) : Kt) : E 0 × F 0).2.2 =
        a • Fr.co (tco (kproj (v : Kt))) ((v : Kt) : E 0 × F 0).2.2
      rw [hk, hk]
      have h2 : (((a • v : kproj ⁻¹' {x}) : Kt) : E 0 × F 0).2.2 =
          a • ((v : Kt) : E 0 × F 0).2.2 :=
        congrArg Prod.snd ((isLinearMap_fibEquiv x).map_smul a v)
      rw [h2]
      exact (Fr.co_linear _ hJx).map_smul _ _

/-! ### Compatibility with the chart `chart0` of the bundle -/

lemma overlap0 :
    chart0.overlap Fr.chart = {p | p ∈ R '' (U ×ˢ (univ : Set (F 0))) ∧ p.1.1.2 ∈ J} := by
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy.2⟩
  · rintro ⟨hp, hpJ⟩
    exact ⟨⟨p, hp⟩, ⟨mem_univ _, hpJ⟩, rfl⟩

lemma overlapJ : Fr.chart.overlap chart0 = UJ J ×ˢ univ := by
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy.1, mem_univ _⟩
  · intro hq
    exact ⟨⟨Fr.bwd q, Fr.bwd_mem_K hq.1⟩, ⟨hq.1, mem_univ _⟩, Fr.fwd_bwd hq.1 _ rfl⟩

/-- The transition map `chart0 → chart`, extended to `E₀ × F₀`:
`(((a, t), w), (x, h)) ↦ (t, co_t(h))`. -/
def A0 (p : E 0 × F 0) : (Fin 1 → ℝ) × (Fin k → ℝ) := (fun _ => p.1.1.2, Fr.co p.1.1.2 p.2.2)

lemma transition0 {p : E 0 × F 0} (hp : p ∈ chart0.overlap Fr.chart) :
    chart0.transition Fr.chart p = Fr.A0 p := by
  obtain ⟨y, hy, rfl⟩ := hp
  change Fr.chart (chart0.toPartialEquiv.symm (chart0 y)) = _
  rw [chart0.toPartialEquiv.left_inv hy.1]; rfl

lemma transitionJ {q : (Fin 1 → ℝ) × (Fin k → ℝ)} (hq : q ∈ Fr.chart.overlap chart0) :
    Fr.chart.transition chart0 q = Fr.bwd q := by
  obtain ⟨y, hy, rfl⟩ := hq
  change chart0 (Fr.chart.toPartialEquiv.symm (Fr.chart y)) = _
  rw [Fr.chart.toPartialEquiv.left_inv hy.1]
  exact (Fr.bwd_fwd hy.1).symm

/-- `(((a, t), w), (x, h)) ↦ t` as an sc-operator `E ⊕ F → ℝ¹`. -/
def tauF : ScOperator (E.prod F) (rnSc 1) where
  lvl m := (tauOp m).comp (ContinuousLinearMap.fst ℝ (E m) (F m))
  incl_comm m x := tauOp.incl_comm m x.1

/-- `(t, s) ↦ ((0, t), 0)` as an sc-operator `ℝ¹ ⊕ ℝᵏ → E`. -/
def sigF (k : ℕ) : ScOperator ((rnSc 1).prod (rnSc k)) E where
  lvl m := (sigmaOp m).comp (ContinuousLinearMap.fst ℝ ((rnSc 1) m) ((rnSc k) m))
  incl_comm m x := sigmaOp.incl_comm m x.1

/-- `(t, s) ↦ (t, s)` as an sc-operator `ℝ¹ ⊕ ℝᵏ → ℝ ⊕ ℝᵏ`. -/
def tsOp (k : ℕ) : ScOperator ((rnSc 1).prod (rnSc k)) ((ScBanach.const ℝ).prod (rnSc k)) where
  lvl _ := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
      (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (Fin k → ℝ))).prod
    (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) (Fin k → ℝ))
  incl_comm _ _ := rfl

include Fr in
lemma isScDomain_J : IsScDomain ((ScBanach.const ℝ).prod X) {p | p.1 ∈ J} := by
  have h := (isScDomain_univ ((ScBanach.const ℝ).prod X)).inter_isOpen
    (W := {p | p.1 ∈ J}) (Fr.isOpen.preimage continuous_fst)
  rwa [univ_inter] at h

include Fr in
lemma isScDomain_D0 : IsScDomain (E.prod F) {p | p.1.1.2 ∈ J} := by
  have h := (isScDomain_univ (E.prod F)).inter_isOpen (W := {p | p.1.1.2 ∈ J})
    (Fr.isOpen.preimage (continuous_snd.comp (continuous_fst.comp continuous_fst)))
  rwa [univ_inter] at h

include Fr in
lemma isScDomain_D1 : IsScDomain (E.prod F.shift) {p | p.1.1.2 ∈ J} := by
  have h := (isScDomain_univ (E.prod F.shift)).inter_isOpen (W := {p | p.1.1.2 ∈ J})
    (Fr.isOpen.preimage (continuous_snd.comp (continuous_fst.comp continuous_fst)))
  rwa [univ_inter] at h

theorem isScSmooth_A0 :
    IsScSmooth (E := E.prod F) (F := (rnSc 1).prod (rnSc k)) {p | p.1.1.2 ∈ J} Fr.A0 := by
  have hD := Fr.isScDomain_D0
  have h1 := tauF.isScSmooth hD
  have h2 : IsScSmooth (E := E.prod F) (F := rnSc k) {p | p.1.1.2 ∈ J}
      ((fun p : ((ScBanach.const ℝ).prod X) 0 => Fr.co p.1 p.2) ∘ tfOp X 0) :=
    IsScSmooth.comp hD Fr.isScDomain_J Fr.smooth_co ((tfOp X).isScSmooth hD) fun p hp => hp
  exact (h1.scPair hD h2).congr hD fun p _ => rfl

theorem isScSmooth_bwd :
    IsScSmooth (E := (rnSc 1).prod (rnSc k)) (F := E.prod F) univ Fr.bwd := by
  have hU := isScDomain_univ ((rnSc 1).prod (rnSc k))
  have h1 := (sigF k).isScSmooth hU
  have h2 := (ScOperator.zeroOp ((rnSc 1).prod (rnSc k)) (ScBanach.const ℝ)).isScSmooth hU
  have h3 := IsScSmooth.comp hU (isScDomain_univ _) Fr.smooth_fr ((tsOp k).isScSmooth hU)
    (mapsTo_univ _ _)
  exact (h1.scPair hU (h2.scPair hU h3)).congr hU fun q _ => rfl

/-- The inverse chart map with the fibre component on level `1`. -/
def bwd1 (q : (Fin 1 → ℝ) × (Fin k → ℝ)) : E 0 × F 1 :=
  (((0, q.1 0), 0), (0, Fr.fr1 (q.1 0) q.2))

theorem isScSmooth_bwd1 :
    IsScSmooth (E := (rnSc 1).prod (rnSc k)) (F := E.prod F.shift) univ Fr.bwd1 := by
  have hU := isScDomain_univ ((rnSc 1).prod (rnSc k))
  have h1 := (sigF k).isScSmooth hU
  have h2 := (ScOperator.zeroOp ((rnSc 1).prod (rnSc k)) (ScBanach.const ℝ)).isScSmooth hU
  have h3 := IsScSmooth.comp hU (isScDomain_univ _) Fr.smooth_fr1 ((tsOp k).isScSmooth hU)
    (mapsTo_univ _ _)
  exact (h1.scPair hU (h2.scPair hU h3)).congr hU fun q _ => rfl

lemma toBase_bwd1 (q : (Fin 1 → ℝ) × (Fin k → ℝ)) :
    F.toBase 1 (Fr.bwd1 q).2 = (Fr.bwd q).2 := by
  rw [F_toBase]
  exact Prod.ext rfl (Fr.toBase_fr1 _ _)

lemma invFun_bwd (q : (Fin 1 → ℝ) × (Fin k → ℝ)) :
    invFun (F.toBase 1) (Fr.bwd q).2 = (Fr.bwd1 q).2 := by
  rw [← Fr.toBase_bwd1 q, leftInverse_invFun (F.toBase_injective 1)]

lemma A0_mem_overlapJ {p : E 0 × F 0} (hp : p.1.1.2 ∈ J) :
    Fr.A0 p ∈ Fr.chart.overlap chart0 := by
  rw [Fr.overlapJ]; exact ⟨hp, mem_univ _⟩

lemma bwd_mem_overlap0 {q : (Fin 1 → ℝ) × (Fin k → ℝ)} (hq : q.1 0 ∈ J) :
    Fr.bwd q ∈ chart0.overlap Fr.chart := by
  rw [Fr.overlap0]; exact ⟨Fr.bwd_mem_K hq, hq⟩

lemma mem_J_of_overlap0 {p : E 0 × F 0} (hp : p ∈ chart0.overlap Fr.chart) : p.1.1.2 ∈ J := by
  rw [Fr.overlap0] at hp; exact hp.2

lemma mem_J_of_overlapJ {q : (Fin 1 → ℝ) × (Fin k → ℝ)} (hq : q ∈ Fr.chart.overlap chart0) :
    q.1 0 ∈ J := by
  rw [Fr.overlapJ] at hq; exact hq.1

lemma invFun_toBase_rn (x : Fin k → ℝ) : invFun ((rnSc k).toBase 1) x = x := by
  have h := leftInverse_invFun ((rnSc k).toBase_injective 1) x
  rwa [ScBanach.const_toBase] at h

/-- The transition `chart0 → chart` on `[1]`. -/
lemma shiftFiber_transition0 {p : E 0 × F 1}
    (hp : (p.1, F.toBase 1 p.2) ∈ chart0.overlap Fr.chart) :
    shiftFiber (chart0.transition Fr.chart) p = Fr.A0 (p.1, F.toBase 1 p.2) := by
  have h := Fr.transition0 hp
  refine Prod.ext ?_ ?_
  · change (chart0.transition Fr.chart (p.1, F.toBase 1 p.2)).1 =
      (Fr.A0 (p.1, F.toBase 1 p.2)).1
    exact congrArg Prod.fst h
  · exact (congrArg (fun z : (Fin 1 → ℝ) × (Fin k → ℝ) =>
      invFun ((rnSc k).toBase 1) z.2) h).trans (invFun_toBase_rn _)

/-- The transition `chart → chart0` on `[1]`. -/
lemma shiftFiber_transitionJ {q : (Fin 1 → ℝ) × (Fin k → ℝ)}
    (hq : q ∈ Fr.chart.overlap chart0) :
    shiftFiber (Fr.chart.transition chart0) q = Fr.bwd1 q := by
  have hq2 : ((q.1, (rnSc k).toBase 1 q.2) : (Fin 1 → ℝ) × (Fin k → ℝ)) = q :=
    Prod.ext rfl (ScBanach.const_toBase _ 1 _)
  have h := Fr.transitionJ hq
  have e1 : shiftFiber (Fr.chart.transition chart0) q =
      ((Fr.chart.transition chart0 q).1, invFun (F.toBase 1) (Fr.chart.transition chart0 q).2) :=
    congrArg (fun z : (Fin 1 → ℝ) × (Fin k → ℝ) => ((Fr.chart.transition chart0 z).1,
      invFun (F.toBase 1) (Fr.chart.transition chart0 z).2)) hq2
  have e2 : (((Fr.chart.transition chart0 q).1,
      invFun (F.toBase 1) (Fr.chart.transition chart0 q).2) : E 0 × F 1) =
      ((Fr.bwd q).1, invFun (F.toBase 1) (Fr.bwd q).2) :=
    congrArg (fun z : E 0 × F 0 => ((z.1, invFun (F.toBase 1) z.2) : E 0 × F 1)) h
  exact e1.trans (e2.trans (Prod.ext rfl (Fr.invFun_bwd q)))

lemma mem_overlapJ_of_shift {q : (Fin 1 → ℝ) × (Fin k → ℝ)}
    (hq : q ∈ strongShiftOne (Fr.chart.overlap chart0)) : q ∈ Fr.chart.overlap chart0 := by
  have hq' : ((q.1, (rnSc k).toBase 1 q.2) : (Fin 1 → ℝ) × (Fin k → ℝ)) ∈
      Fr.chart.overlap chart0 := hq
  have hJ : q.1 0 ∈ J := Fr.mem_J_of_overlapJ hq'
  rw [Fr.overlapJ]; exact ⟨hJ, mem_univ _⟩

/-- **The chart over `J` is compatible with the chart `chart0` of the bundle** (2021 Definition
2.6.4): the transition maps `(((0, t), 0), (0, h)) ↦ (t, co_t(h))` and
`(t, s) ↦ (((0, t), 0), (0, fr_t(s)))` are sc-smooth on `[0]` and on `[1]`. -/
theorem compatible_chart0 : chart0.Compatible Fr.chart := by
  refine ⟨⟨fun p hp => ?_, fun Rr hRr => ?_⟩, ⟨fun q hq => ?_, fun Rr hRr => ?_⟩,
    ⟨fun p hp => ?_, fun Rr hRr => ?_⟩, ⟨fun q hq => ?_, fun Rr hRr => ?_⟩,
    fun x _ _ => ?_, fun x hx _ => ?_⟩
  · rw [Fr.transition0 hp]
    exact Fr.A0_mem_overlapJ (Fr.mem_J_of_overlap0 hp)
  · have hmem : ∀ u ∈ Rr.U, Rr u ∈ chart0.overlap Fr.chart := fun u hu =>
      hRr ▸ Rr.apply_mem_retract hu
    exact (IsScSmooth.comp Rr.isScDomain Fr.isScDomain_D0 Fr.isScSmooth_A0 Rr.isScSmooth
      fun u hu => Fr.mem_J_of_overlap0 (hmem u hu)).congr Rr.isScDomain
      fun u hu => (Fr.transition0 (hmem u hu)).symm
  · rw [Fr.transitionJ hq]
    exact Fr.bwd_mem_overlap0 (Fr.mem_J_of_overlapJ hq)
  · have hmem : ∀ u ∈ Rr.U, Rr u ∈ Fr.chart.overlap chart0 := fun u hu =>
      hRr ▸ Rr.apply_mem_retract hu
    exact (IsScSmooth.comp Rr.isScDomain (isScDomain_univ _) Fr.isScSmooth_bwd Rr.isScSmooth
      (mapsTo_univ _ _)).congr Rr.isScDomain fun u hu => (Fr.transitionJ (hmem u hu)).symm
  · have hp' : (p.1, F.toBase 1 p.2) ∈ chart0.overlap Fr.chart := hp
    refine Set.mem_of_eq_of_mem (Fr.shiftFiber_transition0 hp') ?_
    exact Fr.A0_mem_overlapJ (Fr.mem_J_of_overlap0 hp')
  · have hmem : ∀ u ∈ Rr.U, ((Rr u).1, F.toBase 1 (Rr u).2) ∈ chart0.overlap Fr.chart :=
      fun u hu => by
        have h1 : Rr u ∈ strongShiftOne (chart0.overlap Fr.chart) :=
          hRr ▸ Rr.apply_mem_retract hu
        exact h1
    have hDS := Fr.isScDomain_D1
    have hA : IsScSmooth (E := E.prod F.shift) (F := (rnSc 1).prod (rnSc k))
        {p | p.1.1.2 ∈ J} (Fr.A0 ∘ E.prodShiftInclOp F 0) :=
      IsScSmooth.comp hDS Fr.isScDomain_D0 Fr.isScSmooth_A0
        ((E.prodShiftInclOp F).isScSmooth hDS) fun p hp => hp
    exact (IsScSmooth.comp Rr.isScDomain hDS hA Rr.isScSmooth
      fun u hu => by
        have h1 := Fr.mem_J_of_overlap0 (hmem u hu)
        exact h1).congr Rr.isScDomain
      fun u hu => (Fr.shiftFiber_transition0 (hmem u hu)).symm
  · have hqJ := Fr.mem_overlapJ_of_shift hq
    refine Set.mem_of_eq_of_mem (Fr.shiftFiber_transitionJ hqJ) ?_
    have e2 : ((Fr.bwd1 q).1, F.toBase 1 (Fr.bwd1 q).2) = Fr.bwd q :=
      Prod.ext rfl (Fr.toBase_bwd1 q)
    change ((Fr.bwd1 q).1, F.toBase 1 (Fr.bwd1 q).2) ∈ chart0.overlap Fr.chart
    exact Set.mem_of_eq_of_mem e2 (Fr.bwd_mem_overlap0 (Fr.mem_J_of_overlapJ hqJ))
  · have hmem : ∀ u ∈ Rr.U, Rr u ∈ Fr.chart.overlap chart0 := fun u hu => by
      have h1 : Rr u ∈ strongShiftOne (Fr.chart.overlap chart0) :=
        hRr ▸ Rr.apply_mem_retract hu
      exact Fr.mem_overlapJ_of_shift h1
    exact (IsScSmooth.comp Rr.isScDomain (isScDomain_univ _) Fr.isScSmooth_bwd1 Rr.isScSmooth
      (mapsTo_univ _ _)).congr Rr.isScDomain
      fun u hu => (Fr.shiftFiber_transitionJ (hmem u hu)).symm
  · exact ⟨_, ScBanach.const_toBase _ 1 _⟩
  · rw [Fr.transitionJ hx]
    exact ⟨(Fr.bwd1 x).2, Fr.toBase_bwd1 x⟩

/-- The chart over `J` is a strong bundle chart of `bundle`. -/
theorem isChart_chart : bundle.IsChart Fr.chart := fun c hc => by
  rw [mem_singleton_iff.1 hc]
  exact Fr.compatible_chart0.symm

/-! ### Germ data at the points of `J` -/

/-- In the frame the section is the constant `cst`. -/
lemma fwd_sec {x : Ob} (hx : tco x ∈ J) : (Fr.fwd (sec x)).2 = Fr.cst := by
  obtain ⟨-, -, hw⟩ := mem_O.1 x.2
  change Fr.co (tco x) ((x : E 0).2 + proj (x : E 0).1.2 v) = Fr.cst
  rw [hw, zero_add]
  exact Fr.co_v _ hx

/-- **Germ data of `sec` at the points over `J`** (2021 Definition 3.6.3): in the chart over `J`
re-centred at `t₀` (identity retraction, quadrant `ℝ¹`), the principal part of `sec` is the
constant `cst`; it fills itself, the sc⁺-germ is the same constant, and the zero map is a basic
germ.  The chart is centred at an interior point of its quadrant, so these are tame germ data
(`IsScFredholmGermInterior`). -/
theorem isScFredholmGermInterior_sec {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    bundle.IsScFredholmGermInterior sec (ptO t₀ (Fr.lt_one _ ht₀)) := by
  obtain ⟨n, W, T, hT⟩ := (rn_relOpen_univ 1).isPartialQuadrant
  have he : (fun _ => t₀ : Fin 1 → ℝ) ∈ (rnSc 1).smooth :=
    (rnSc 1).mem_smooth_iff.2 fun m => ⟨fun _ => t₀, ScBanach.const_toBase _ m _⟩
  have hT' : Fr.chart.φ.model.C = T 0 ⁻¹' quadrant n W 0 := hT
  have hall : ∀ w : Fin 1 → ℝ, T 0 w ∈ quadrant n W 0 := fun w => by
    have h : w ∈ (univ : Set ((rnSc 1) 0)) := mem_univ w
    rw [hT] at h
    exact h
  set c := Fr.chart.recentre (T := T) hT' (fun _ => t₀) he with hc_def
  have hc : bundle.IsChart c := Fr.isChart_chart.recentre T hT' _ he
  have hCu : c.φ.model.C = univ := eq_univ_of_forall fun w i _ => hall w i
  have hxφ : Fr.chart.φ (ptO t₀ (Fr.lt_one _ ht₀)) = (fun _ => t₀) := rfl
  have hxs : ptO t₀ (Fr.lt_one _ ht₀) ∈ Fr.chart.φ.source := ht₀
  have hxV : ptO t₀ (Fr.lt_one _ ht₀) ∈ c.φ.source :=
    Fr.chart.φ.mem_recentre_source T hT' _ he hxs hxφ
  have hφ0 : c.φ (ptO t₀ (Fr.lt_one _ ht₀)) = 0 :=
    Fr.chart.φ.recentre_apply_self T hT' _ he hxφ
  have hG : (fun _ => t₀ : Fin 1 → ℝ) ∈ recentreNbhd T (fun _ => t₀) :=
    mem_recentreNbhd hT (mem_univ _)
  have h0 : (0 : c.φ.model.E 0) ∈ c.U := by
    have e0 : (0 : Fin 1 → ℝ) + (fun _ => t₀) = fun _ => t₀ := zero_add _
    have hU : (fun _ => t₀ : Fin 1 → ℝ) ∈ UJ J := ht₀
    exact ⟨⟨Set.mem_of_eq_of_mem e0 hU, Set.mem_of_eq_of_mem e0 hG⟩,
      Set.mem_of_eq_of_mem e0 hG⟩
  have hRid : ∀ p, c.R p = p := fun p => subFst_addFst _ p
  have hcst : Fr.cst ∈ (rnSc k).smooth :=
    (rnSc k).mem_smooth_iff.2 fun m => ⟨Fr.cst, ScBanach.const_toBase _ m _⟩
  have hsm : IsScSmooth (E := c.φ.model.E) (F := c.F) c.U (fun _ => Fr.cst) :=
    isScSmooth_const c.relOpen.isScDomain hcst
  have hsm1 : IsScSmooth (E := c.φ.model.E) (F := c.F.shift) c.U (fun _ => Fr.cst) :=
    isScSmooth_const (H := rnSc k) c.relOpen.isScDomain hcst
  have hfill0 := isFilling2021_of_R_eq_self c.relOpen c.isRetraction hRid h0 hsm
  have hprin : ∀ z ∈ c.φ.model.O, c.principal sec z = Fr.cst := fun z hz => by
    have hs : c.φ.symm z ∈ c.φ.source := c.φ.symm_mapsTo hz
    have hs' : c.φ.symm z ∈ Fr.chart.φ.source := Fr.chart.φ.recentreSource_subset T _ hs
    exact Fr.fwd_sec hs'
  have hfill : IsFilling2021 c.relOpen c.isRetraction h0 (c.principal sec) (fun _ => Fr.cst) :=
    ⟨hfill0.r_zero, Eventually.of_forall fun z hz => hprin z (c.r_image ▸ hz),
      hfill0.mem_of_fixed, hfill0.germ⟩
  have hplus : IsScPlusGerm (F := c.F) c.φ.model.C c.U (fun _ => Fr.cst) :=
    ⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0, fun _ hu => hu,
      hsm1.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen h0⟩
  have hopen : IsOpen c.U := by
    obtain ⟨O, hO, hUO⟩ := c.relOpen.relOpen
    have : c.U = O := by rw [hUO, hCu, inter_univ]
    rw [this]; exact hO
  have hrel : IsRelOpenInQuadrant (rnSc 1) univ c.U :=
    ⟨(rn_relOpen_univ 1).isPartialQuadrant, c.U, hopen, (inter_univ _).symm⟩
  have hconj0 : IsConjugateToBasicGerm (E := rnSc 1) (F := rnSc k) univ
      (fun _ => (0 : Fin k → ℝ)) :=
    TrivialBundle.isConjugateToBasicGerm_of_contDiff contDiff_const rfl
  have hconj : IsConjugateToBasicGerm (E := rnSc 1) (F := rnSc k) c.U
      (fun _ => Fr.cst - (rnSc k).toBase 1 Fr.cst) :=
    (hconj0.of_subset (rn_relOpen_univ 1) (mem_univ _) hrel (subset_univ _) h0).congr
      fun u _ => by
        change (0 : Fin k → ℝ) = Fr.cst - (rnSc k).toBase 1 Fr.cst
        rw [ScBanach.const_toBase, sub_self]
  refine ⟨by rw [smoothSet_polyO]; exact mem_univ _, c, hc, hxV, hφ0, h0, fun _ => Fr.cst,
    fun _ => Fr.cst, hfill, hplus, ScBanach.const_toBase _ 1 _, hconj, ?_⟩
  rw [hCu, interior_univ]; exact mem_univ _

end Frame

/-! ### The frame over `t < 0` -/

lemma isScDomain_fst {J : Set ℝ} (hJ : IsOpen J) :
    IsScDomain ((ScBanach.const ℝ).prod X) {p | p.1 ∈ J} := by
  have h := (isScDomain_univ ((ScBanach.const ℝ).prod X)).inter_isOpen
    (W := {p | p.1 ∈ J}) (hJ.preimage continuous_fst)
  rwa [univ_inter] at h

/-- **The frame over `t < 0`**, where the fibre of `K` is `0` (`k = 0`). -/
def frame0 : Frame 0 (Iio (0 : ℝ)) where
  co _ _ := 0
  fr _ _ := 0
  fr1 _ _ := 0
  cst := 0
  isOpen := isOpen_Iio
  lt_one _ ht := lt_trans ht zero_lt_one
  toBase_fr1 _ _ := map_zero _
  proj_fr _ _ _ := map_zero _
  co_fr _ _ _ := Subsingleton.elim _ _
  fr_co t ht h hh := by rw [← hh]; exact (proj_of_nonpos (le_of_lt ht) h).symm
  co_linear _ _ := ⟨fun _ _ => (add_zero _).symm, fun _ _ => (smul_zero _).symm⟩
  co_v _ _ := rfl
  smooth_co := isScSmooth_const (isScDomain_fst isOpen_Iio) (Submodule.zero_mem _)
  smooth_fr := isScSmooth_const (isScDomain_univ _) (Submodule.zero_mem _)
  smooth_fr1 := isScSmooth_const (isScDomain_univ _) (Submodule.zero_mem _)

/-! ### The frame over `0 < t < 1` -/

/-- `q(t) = ν(π_t v)`, non-zero for `0 < t < 1`. -/
def qf (t : ℝ) : ℝ := nu (proj t v)

lemma qf_ne_zero {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : qf t ≠ 0 := fun h =>
  proj_ne_zero ht.1 ht.2 v_pos
    (eq_zero_of_proj_eq ht.2 (fun i => nu_unitVec_pos (pos i)) (proj_proj ht.2 v) h)

/-- `ν` as an sc-operator `X → ℝ`. -/
def nuX : ScOperator X (ScBanach.const ℝ) where
  lvl m := nu.comp (X.toBase m)
  incl_comm _ _ := rfl

/-- `x ↦ (x)` as an sc-operator `ℝ → ℝ¹`. -/
def piOp : ScOperator (ScBanach.const ℝ) (rnSc 1) where
  lvl _ := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ
  incl_comm _ _ := rfl

/-- `(t, s) ↦ s₀` as an sc-operator `ℝ ⊕ ℝ¹ → ℝ`. -/
def coordOp : ScOperator ((ScBanach.const ℝ).prod (rnSc 1)) (ScBanach.const ℝ) where
  lvl _ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
    (ContinuousLinearMap.snd ℝ ℝ (Fin 1 → ℝ))
  incl_comm _ _ := rfl

/-- `t ↦ ν(π_t v)` is sc-smooth. -/
theorem isScSmooth_qf :
    IsScSmooth (E := ScBanach.const ℝ) (F := ScBanach.const ℝ) univ qf := by
  have hU := isScDomain_univ (ScBanach.const ℝ)
  have hpair : IsScSmooth (E := ScBanach.const ℝ) (F := (ScBanach.const ℝ).prod X) univ
      (scPair id fun _ => v) :=
    (isScSmooth_id hU).scPair hU (isScSmooth_const hU v_mem_smooth)
  have h1 := IsScSmooth.comp hU (isScDomain_univ _) family.isScSmooth_map hpair (mapsTo_univ _ _)
  exact (IsScSmooth.comp hU (isScDomain_univ _) (nuX.isScSmooth (isScDomain_univ _)) h1
    (mapsTo_univ _ _)).congr hU fun t _ => rfl

/-- Inversion is sc-smooth on `ℝ ∖ 0`. -/
theorem isScSmooth_inv :
    IsScSmooth (E := ScBanach.const ℝ) (F := ScBanach.const ℝ) ({0}ᶜ : Set ℝ)
      (fun x : ℝ => x⁻¹) :=
  isScSmooth_of_bijective_toBase (bijective_toBase_const ℝ) (bijective_toBase_const ℝ)
    (GermVsChart.isScDomain_const_of_isOpen isOpen_compl_singleton) (contDiffOn_inv ℝ)

theorem isScSmooth_co_one :
    IsScSmooth (E := (ScBanach.const ℝ).prod X) (F := rnSc 1) {p | p.1 ∈ Ioo (0 : ℝ) 1}
      (fun p => (fun _ => nu p.2 * (qf p.1)⁻¹ : Fin 1 → ℝ)) := by
  have hD := isScDomain_fst (isOpen_Ioo (a := (0 : ℝ)) (b := 1))
  have hfst := ((ScBanach.const ℝ).prodFstOp X).isScSmooth hD
  have hq : IsScSmooth (E := (ScBanach.const ℝ).prod X) (F := ScBanach.const ℝ)
      {p | p.1 ∈ Ioo (0 : ℝ) 1} (qf ∘ (ScBanach.const ℝ).prodFstOp X 0) :=
    IsScSmooth.comp hD (isScDomain_univ _) isScSmooth_qf hfst (mapsTo_univ _ _)
  have hinv : IsScSmooth (E := (ScBanach.const ℝ).prod X) (F := ScBanach.const ℝ)
      {p | p.1 ∈ Ioo (0 : ℝ) 1}
      ((fun x : ℝ => x⁻¹) ∘ (qf ∘ (ScBanach.const ℝ).prodFstOp X 0)) :=
    IsScSmooth.comp hD (GermVsChart.isScDomain_const_of_isOpen isOpen_compl_singleton)
      isScSmooth_inv hq fun p hp => qf_ne_zero hp
  have hν : IsScSmooth (E := (ScBanach.const ℝ).prod X) (F := ScBanach.const ℝ)
      {p | p.1 ∈ Ioo (0 : ℝ) 1} (nuX 0 ∘ (ScBanach.const ℝ).prodSndOp X 0) :=
    IsScSmooth.comp hD (isScDomain_univ _) (nuX.isScSmooth (isScDomain_univ _))
      (((ScBanach.const ℝ).prodSndOp X).isScSmooth hD) (mapsTo_univ _ _)
  have hprod := IsScSmooth.smul hD hν hinv
  exact (IsScSmooth.comp hD (isScDomain_univ _) (piOp.isScSmooth (isScDomain_univ _)) hprod
    (mapsTo_univ _ _)).congr hD fun p _ => rfl

theorem isScSmooth_fr_one :
    IsScSmooth (E := (ScBanach.const ℝ).prod (rnSc 1)) (F := X) univ
      (fun p => proj p.1 (p.2 0 • v)) := by
  have hU := isScDomain_univ ((ScBanach.const ℝ).prod (rnSc 1))
  have h1 := ((ScBanach.const ℝ).prodFstOp (rnSc 1)).isScSmooth hU
  have h3 : IsScSmooth (E := (ScBanach.const ℝ).prod (rnSc 1)) (F := X) univ
      (fun p => coordOp 0 p • v) :=
    IsScSmooth.smul hU (coordOp.isScSmooth hU) (isScSmooth_const hU v_mem_smooth)
  exact (IsScSmooth.comp hU (isScDomain_univ _) family.isScSmooth_map (h1.scPair hU h3)
    (mapsTo_univ _ _)).congr hU fun p _ => rfl

lemma vlvl_one_mem_smooth : vlvl 1 ∈ X.shift.smooth :=
  X.shift.mem_smooth_iff.2 fun m => ⟨vlvl (m + 1), X.toBase_injective 1 (by
    rw [← X.shift_toBase, X_toBase_vlvl, X_toBase_vlvl])⟩

theorem isScSmooth_fr1_one :
    IsScSmooth (E := (ScBanach.const ℝ).prod (rnSc 1)) (F := X.shift) univ
      (fun p => family.A 1 p.1 (p.2 0 • vlvl 1)) := by
  have hU := isScDomain_univ ((ScBanach.const ℝ).prod (rnSc 1))
  have h1 := ((ScBanach.const ℝ).prodFstOp (rnSc 1)).isScSmooth hU
  have h3 : IsScSmooth (E := (ScBanach.const ℝ).prod (rnSc 1)) (F := X.shift) univ
      (fun p => coordOp 0 p • vlvl 1) :=
    IsScSmooth.smul hU (coordOp.isScSmooth hU) (isScSmooth_const hU vlvl_one_mem_smooth)
  exact (IsScSmooth.comp hU (isScDomain_univ _) family.isScSmooth_shift_map (h1.scPair hU h3)
    (mapsTo_univ _ _)).congr hU fun p _ => rfl

/-- **The frame over `0 < t < 1`**, where the fibre of `K` is the line `ran π_t` (`k = 1`):
`fr_t(s) = s π_t v`, `co_t(h) = ν(h)/ν(π_t v)`; the section `π_t v` has the coordinate `1`. -/
def frame1 : Frame 1 (Ioo (0 : ℝ) 1) where
  co t h := fun _ => nu h * (qf t)⁻¹
  fr t s := proj t (s 0 • v)
  fr1 t s := family.A 1 t (s 0 • vlvl 1)
  cst := fun _ => 1
  isOpen := isOpen_Ioo
  lt_one _ ht := ht.2
  toBase_fr1 t s := by
    rw [family.toBase_A, map_smul, X_toBase_vlvl]; rfl
  proj_fr _ ht _ := proj_proj ht.2 _
  co_fr t ht s := funext fun i => by
    rw [Subsingleton.elim i 0]
    rw [map_smul, map_smul, smul_eq_mul]
    exact mul_inv_cancel_right₀ (qf_ne_zero ht) _
  fr_co t ht h hh := by
    change proj t ((nu h * (qf t)⁻¹) • v) = h
    rw [map_smul]
    have hy : proj t (h - (nu h * (qf t)⁻¹) • proj t v) = h - (nu h * (qf t)⁻¹) • proj t v := by
      rw [map_sub, map_smul, proj_proj ht.2, hh]
    have hν : nu (h - (nu h * (qf t)⁻¹) • proj t v) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul]
      change nu h - nu h * (qf t)⁻¹ * qf t = 0
      rw [inv_mul_cancel_right₀ (qf_ne_zero ht), sub_self]
    exact (sub_eq_zero.1
      (eq_zero_of_proj_eq ht.2 (fun i => nu_unitVec_pos (pos i)) hy hν)).symm
  co_linear t _ :=
    ⟨fun a b => funext fun _ => by
        change nu (a + b) * (qf t)⁻¹ = nu a * (qf t)⁻¹ + nu b * (qf t)⁻¹
        rw [map_add, add_mul],
      fun c a => funext fun _ => by
        change nu (c • a) * (qf t)⁻¹ = c * (nu a * (qf t)⁻¹)
        rw [map_smul, smul_eq_mul, mul_assoc]⟩
  co_v _ ht := funext fun _ => mul_inv_cancel₀ (qf_ne_zero ht)
  smooth_co := isScSmooth_co_one
  smooth_fr := isScSmooth_fr_one
  smooth_fr1 := isScSmooth_fr1_one

/-! ### The section is sc-Fredholm -/

/-- **Germ data of `sec` at every point other than `x₀`**, in a chart centred at an interior point
of its quadrant. -/
theorem isScFredholmGermInterior_sec_of_ne {x : Ob} (hx : x ≠ x0) :
    bundle.IsScFredholmGermInterior sec x := by
  have h1 : tco x < 1 := (mem_O.1 x.2).2.1
  have hne : tco x ≠ 0 := fun h => hx (tco_injective h)
  rcases lt_or_gt_of_ne hne with h | h
  · have e : ptO (tco x) (frame0.lt_one _ h) = x := tco_injective rfl
    exact e ▸ frame0.isScFredholmGermInterior_sec (t₀ := tco x) h
  · have e : ptO (tco x) (frame1.lt_one _ ⟨h, h1⟩) = x := tco_injective rfl
    exact e ▸ frame1.isScFredholmGermInterior_sec (t₀ := tco x) ⟨h, h1⟩

/-- **At every point other than `x₀` the germ of `sec` has tame germ data** (the 2017 and preprint
form of Definition 3.6.3). -/
theorem isScFredholmGermTame_sec_of_ne {x : Ob} (hx : x ≠ x0) :
    bundle.IsScFredholmGermTame sec x :=
  (isScFredholmGermInterior_sec_of_ne hx).isScFredholmGermTame

/-- **`sec` is an sc-Fredholm section in the sense of 2021 Definitions 3.1.16 = 3.6.4**:
sc-smooth, regularizing (every point of `O` is smooth), and an sc-Fredholm germ (2021 Definition
3.6.3) at every point: at `x₀` with the germ data of `UntamedBundle.lean` in the chart
`chart0`, at the other points in the charts of the two frames. -/
theorem isScFredholmSection2021_sec : bundle.IsScFredholmSection2021 sec where
  isScSmooth := isScSmoothSection_sec
  regularizing m x _ _ := by rw [levelSet_polyO]; exact mem_univ x
  germ x _ := by
    by_cases hx : x = x0
    · rw [hx]; exact isScFredholmGerm2021_sec_zero
    · exact (isScFredholmGermInterior_sec_of_ne hx).isScFredholmGerm2021

end UntamedCorner

end Polyfold
