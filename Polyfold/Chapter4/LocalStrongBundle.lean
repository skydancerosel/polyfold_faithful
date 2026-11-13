import Polyfold.Chapter4.RemarkFourThreeFamily
import Polyfold.Chapter4.Recentre
import Polyfold.Chapter3.NonVacuityCorner
import Polyfold.Chapter3.Book2021Germs

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.1, the local
strong bundle `π : U ◁ Y → U` of the proof of **Proposition 4.1.9** (p. 179), on which
**Lemma 4.1.11** (p. 179) is stated.

# The local strong bundle `U ◁ F → U` as a strong bundle

## The text

In the proof of Proposition 4.1.9 the text considers "the local strong bundle `π : U ◁ Y → U`"
over a relatively open subset `U` of a partial quadrant `C ⊆ E`, and sections
`f(u) = (u, f(u))` of it.  Lemma 4.1.11 says such a section is sc-Fredholm (Definition 3.1.16,
which is stated for strong bundles over M-polyfolds).

## What is formalized

* `LocalBundle.bundle hU F u₀`: for `U` relatively open in the partial quadrant `C ⊆ E` and an
  sc-Banach space `F`, the strong bundle `U × F₀ → U` over the M-polyfold `U` (the retract
  `(U, C, E)` with its one chart, `retractPolyfold`), with the one strong bundle chart
  `(x, h) ↦ (x, h)` onto `U ◁ F` (identity strong bundle retraction).  The point `u₀ ∈ U` is the
  junk value of the inverse chart off `U`.
* `LocalBundle.sec k`: the section `x ↦ (x, k(x))` of a map `k : E₀ → F₀`;
  `isScSmoothSection_sec` (sc-smooth if `k` is sc-smooth on `U`), `mem_doubleLevel_iff`,
  `mem_levelSet_iff`, `mem_smoothSet_iff`.
* Re-centring at a smooth `e ∈ U`: `centred hT e he` is `StrongBundleChart.recentre` of the
  chart, a chart of the bundle (`isChart_centred`); in it the principal part of `sec k` is
  `v ↦ k(v + e)` on the domain (`principal_centred`), and the strong bundle retraction is the
  identity (`centred_R_apply`), so every sc-smooth map fills itself
  (`isFilling2021_of_R_eq_self`).

## Choices

* The text's `U ◁ Y` is the product `U × Y`; as a type it is `U × F₀` with the fibre structure of
  `F₀` transported to `π⁻¹(x)`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### A strong bundle retraction which is the identity fills every sc-smooth map -/

section Fill

variable {E F : ScBanach} {C U : Set (E 0)}

/-- **A strong bundle retraction which is pointwise the identity**: every sc-smooth `g` is a filling
of itself (2021 Definition 3.1.4), as for `R = id` (`isFilling2017_id`). -/
theorem isFilling2021_of_R_eq_self (hU : IsRelOpenInQuadrant E C U)
    {R : E 0 × F 0 → E 0 × F 0} (hR : IsStrongBundleRetraction U R) (hRid : ∀ p, R p = p)
    (h0 : (0 : E 0) ∈ U) {g : E 0 → F 0} (hg : IsScSmooth U g) : IsFilling2021 hU hR h0 g g := by
  have hid : R = id := funext hRid
  subst hid
  exact (isFilling2017_id hU h0 hg).isFilling2021

end Fill

namespace LocalBundle

variable {E F : ScBanach} {C U : Set (E 0)}

/-- The projection `U × F₀ → U`. -/
def proj : U × F 0 → U := Prod.fst

@[simp] lemma proj_apply (y : U × F 0) : proj y = y.1 := rfl

/-- The fibre `π⁻¹(x) ≃ F₀`. -/
def fibEquiv (x : U) : (proj (F := F) ⁻¹' {x}) ≃ F 0 where
  toFun y := y.1.2
  invFun v := ⟨(x, v), rfl⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    simp only [mem_preimage, proj_apply, mem_singleton_iff] at h
    subst h; rfl
  right_inv _ := rfl

instance (x : U) : AddCommGroup (proj (F := F) ⁻¹' {x}) := (fibEquiv x).addCommGroup

instance (x : U) : Module ℝ (proj (F := F) ⁻¹' {x}) := (fibEquiv x).module ℝ

lemma isLinearMap_fibEquiv (x : U) : IsLinearMap ℝ (fibEquiv (F := F) x) :=
  ((fibEquiv x).linearEquiv ℝ).toLinearMap.isLinear

variable (hU : IsRelOpenInQuadrant E C U) (u₀ : U)

/-- The M-polyfold `U` (the retract `(U, C, E)` with its one chart). -/
abbrev basePolyfold : MPolyfold U := retractPolyfold hU.isScRetract u₀

/-- The one chart of the base. -/
abbrev baseChart : MChart U := retractChart hU.isScRetract u₀

open scoped Classical in
/-- The bundle chart `(x, h) ↦ (x, h)` onto `U × F₀`. -/
def chartPE : PartialEquiv (U × F 0) (E 0 × F 0) where
  toFun y := ((y.1 : E 0), y.2)
  invFun p := (if h : p.1 ∈ U then ⟨p.1, h⟩ else u₀, p.2)
  source := univ
  target := U ×ˢ univ
  map_source' y _ := ⟨y.1.2, mem_univ _⟩
  map_target' _ _ := mem_univ _
  left_inv' y _ := by simp [y.1.2]
  right_inv' p hp := by simp [hp.1]

/-- **The strong bundle chart of `U ◁ F`**: over the chart `U → U` of the base, the identity strong
bundle retraction on `U ◁ F` and `Φ(x, h) = (x, h)`. -/
def chart : StrongBundleChart (basePolyfold hU u₀) (proj (F := F)) where
  φ := baseChart hU u₀
  isChart := isChart_retractChart hU.isScRetract u₀
  F := F
  U := U
  R := id
  relOpen := hU
  isRetraction := isStrongBundleRetraction_id_of_relOpen hU
  base_retract := by
    change (fun u => u) '' U = U
    exact image_id' U
  toPartialEquiv := chartPE u₀
  source_eq := preimage_univ.symm
  target_eq := (image_id _).symm
  continuousOn_toFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
  continuousOn_invFun := by
    classical
    refine ContinuousOn.prodMk ?_ continuous_snd.continuousOn
    rw [continuousOn_iff_continuous_domRestrict]
    have e : (U ×ˢ (univ : Set (F 0))).domRestrict
        (fun p : E 0 × F 0 => if h : p.1 ∈ U then (⟨p.1, h⟩ : U) else u₀) =
        fun q => ⟨q.1.1, q.2.1⟩ := by
      funext q
      change (if h : (q : E 0 × F 0).1 ∈ U then (⟨(q : E 0 × F 0).1, h⟩ : U) else u₀) = _
      rw [dif_pos q.2.1]
    change Continuous ((U ×ˢ (univ : Set (F 0))).domRestrict
      (fun p : E 0 × F 0 => if h : p.1 ∈ U then (⟨p.1, h⟩ : U) else u₀))
    rw [e]
    exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
  covers _ _ := rfl
  fiber_linear x _ := isLinearMap_fibEquiv x

lemma chart_apply (y : U × F 0) : chart (F := F) hU u₀ y = ((y.1 : E 0), y.2) := rfl

lemma chart_source : (chart (F := F) hU u₀).toPartialEquiv.source = univ := rfl

lemma chart_U : (chart (F := F) hU u₀).U = U := rfl

lemma chart_R : (chart (F := F) hU u₀).R = id := rfl

variable (F) in
/-- **The local strong bundle `U ◁ F → U`** (the text's `π : U ◁ Y → U`), with its one chart. -/
def bundle : StrongBundle (basePolyfold hU u₀) (proj (F := F)) where
  continuous := continuous_fst
  surjective x := ⟨(x, 0), rfl⟩
  banachable x := ⟨F 0, inferInstance, inferInstance, inferInstance,
    ⟨{ toLinearEquiv := (fibEquiv x).linearEquiv ℝ
       continuous_toFun := continuous_snd.comp continuous_subtype_val
       continuous_invFun :=
        (continuous_const.prodMk continuous_id).subtype_mk fun _ => rfl }⟩⟩
  atlas :=
    { charts := {chart hU u₀}
      compatible := by
        rintro c hc c' hc'
        rw [mem_singleton_iff.1 hc, mem_singleton_iff.1 hc']
        exact StrongBundleChart.compatible_self _
      cover := fun _ => ⟨chart hU u₀, mem_singleton _, mem_univ _⟩ }

lemma isChart_chart : (bundle F hU u₀).IsChart (chart hU u₀) :=
  StrongBundle.isChart_of_mem (B := bundle F hU u₀) (mem_singleton _)

/-! ### Levels -/

lemma mem_levelSet_iff {m : ℕ} {x : U} :
    x ∈ (basePolyfold hU u₀).levelSet m ↔ (x : E 0) ∈ range (E.toBase m) :=
  (basePolyfold hU u₀).mem_levelSet_iff (isChart_retractChart hU.isScRetract u₀) (mem_univ x)

lemma mem_smoothSet_iff {x : U} :
    x ∈ (basePolyfold hU u₀).smoothSet ↔ (x : E 0) ∈ E.smooth :=
  MPolyfold.mem_smoothSet_iff (isChart_retractChart hU.isScRetract u₀) (mem_univ x)

lemma mem_doubleLevel_iff {m k : ℕ} {y : U × F 0} :
    y ∈ (bundle F hU u₀).doubleLevel m k ↔
      (y.1 : E 0) ∈ range (E.toBase m) ∧ y.2 ∈ range (F.toBase k) := by
  constructor
  · intro h
    exact h (chart hU u₀) (mem_singleton _) (mem_univ _)
  · rintro h c hc -
    rw [mem_singleton_iff.1 hc]
    exact h

/-! ### The section `x ↦ (x, k(x))` -/

/-- The section `x ↦ (x, k(x))` of `U ◁ F → U` with principal part `k`. -/
def sec (k : E 0 → F 0) (x : U) : U × F 0 := (x, k x)

lemma isSection_sec (k : E 0 → F 0) : IsSection (proj (U := U) (F := F)) (sec k) := fun _ => rfl

/-- **The section with an sc-smooth principal part is sc-smooth** (Definition 2.6.6). -/
theorem isScSmoothSection_sec {k : E 0 → F 0} (hk : IsScSmooth U k) :
    (bundle F hU u₀).IsScSmoothSection (sec k) := by
  classical
  refine ⟨isSection_sec k, MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ ?_ fun x _ => ?_⟩
  · have hc : Continuous fun x : U => k x :=
      continuousOn_iff_continuous_domRestrict.1 hk.isSc1.isSc0.continuousOn_base
    exact (continuous_id.prodMk hc).continuousOn
  refine ⟨baseChart hU u₀, (chart hU u₀).toMChart (bundle F hU u₀).continuous, univ,
    isChart_retractChart hU.isScRetract u₀,
    (bundle F hU u₀).isChart_toMChart (mem_singleton _), isOpen_univ, mem_univ x,
    fun _ _ => ⟨mem_univ _, mem_univ _⟩, fun _ _ => mem_univ _, ?_⟩
  have himg : (baseChart hU u₀) '' univ = U := by
    ext v
    constructor
    · rintro ⟨y, -, rfl⟩; exact y.2
    · intro hv; exact ⟨⟨v, hv⟩, mem_univ _, rfl⟩
  rw [himg]
  have heq : ∀ v ∈ U, ((chart (F := F) hU u₀).toMChart (bundle F hU u₀).continuous ∘ sec k ∘
      (baseChart hU u₀).symm) v = (v, k v) := by
    intro v hv
    have h1 : ((baseChart hU u₀).toPartialEquiv.symm v : E 0) = v :=
      (baseChart hU u₀).toPartialEquiv.right_inv hv
    change (((baseChart hU u₀).toPartialEquiv.symm v : E 0),
      k ((baseChart hU u₀).toPartialEquiv.symm v : E 0)) = (v, k v)
    rw [h1]
  refine (isScSmoothRetractMap_iff_exists hU.isScRetract).2
    ⟨fun v hv => ?_, ScRetraction.id hU, image_id U, ?_⟩
  · rw [heq v hv]
    exact ⟨(v, k v), ⟨hv, mem_univ _⟩, rfl⟩
  · exact (IsScSmooth.scPair hU.isScDomain (isScSmooth_id hU.isScDomain) hk).congr
      hU.isScDomain fun v hv => (heq v hv).symm

/-! ### Re-centring at a smooth point -/

variable {n : ℕ} {W : ScBanach} {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}
  (hT : C = T 0 ⁻¹' quadrant n W 0) {e : E 0} (he : e ∈ E.smooth)

/-- **The strong bundle chart centred at the smooth point `e ∈ U`** (`StrongBundleChart.recentre`
of the chart, in the partial quadrant `C_e`). -/
abbrev centred : StrongBundleChart (basePolyfold hU u₀) (proj (F := F)) :=
  (chart hU u₀).recentre T hT e he

lemma isChart_centred : (bundle F hU u₀).IsChart (centred hU u₀ hT he) :=
  (isChart_chart hU u₀).recentre T hT e he

lemma centred_F : (centred (F := F) hU u₀ hT he).F = F := rfl

lemma centred_model_E : (centred (F := F) hU u₀ hT he).φ.model.E = E := rfl

lemma centred_R_apply (p : E 0 × F 0) : (centred (F := F) hU u₀ hT he).R p = p :=
  subFst_addFst e p

lemma add_mem_of_mem_centred_U {v : E 0} (hv : v ∈ (centred (F := F) hU u₀ hT he).U) :
    v + e ∈ U := hv.1.1

lemma mem_centred_source {x : U} (hx : (x : E 0) = e) :
    x ∈ (centred (F := F) hU u₀ hT he).φ.source :=
  (baseChart hU u₀).mem_recentre_source T hT e he (mem_univ x) hx

lemma centred_apply_self {x : U} (hx : (x : E 0) = e) :
    (centred (F := F) hU u₀ hT he).φ x = 0 :=
  (baseChart hU u₀).recentre_apply_self T hT e he hx

lemma zero_mem_centred_U (heU : e ∈ U) : (0 : E 0) ∈ (centred (F := F) hU u₀ hT he).U := by
  have heC : e ∈ C := by
    obtain ⟨O, -, hO⟩ := hU.relOpen
    rw [hO] at heU; exact heU.2
  have hG := mem_recentreNbhd hT heC
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change 0 + e ∈ U; rw [zero_add]; exact heU
  · change id (0 + e) ∈ recentreNbhd T e; rw [zero_add]; exact hG
  · change 0 + e ∈ recentreNbhd T e; rw [zero_add]; exact hG

/-- **The principal part of `sec k` in the centred chart** is `v ↦ k(v + e)` on its domain. -/
lemma principal_centred (k : E 0 → F 0) {v : E 0}
    (hv : v ∈ (centred (F := F) hU u₀ hT he).U) :
    (centred (F := F) hU u₀ hT he).principal (sec k) v = k (v + e) := by
  have hve := add_mem_of_mem_centred_U hU u₀ hT he hv
  have h1 : ((baseChart hU u₀).toPartialEquiv.symm (v + e) : E 0) = v + e :=
    (baseChart hU u₀).toPartialEquiv.right_inv hve
  change k ((baseChart hU u₀).toPartialEquiv.symm (v + e) : E 0) = k (v + e)
  rw [h1]

end LocalBundle

end Polyfold
