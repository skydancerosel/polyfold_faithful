import Polyfold.Chapter19.Metrizability
import Polyfold.Chapter19.BasicConstructionExamples
import Polyfold.Chapter7.PropertyFiveResearch
import Polyfold.Chapter5.OrientableNbhd

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.4 "Metrizability Criteria" (pp. 879–885): witnesses for the hypotheses of `Metrizability`,
and the basic constructions for `proposition_19_4_2_v3_without_limit` and `not_lemma_19_4_3`.
Numbers and pages are the 2021 text's.

# Metrizability criteria: witnesses and examples

## The constructions

* `reflectionBasic` (`ℤ/2 ⋉ ℝ`, `BasicConstructionExamples`): `|Ψ₀|` is onto, so `T` is
  metrizable and the properness condition holds.
* `gluedBasic` (Remark 19.2.3): the domains are `ℝ`, so (v3) as printed holds; (v2) does not hold at
  `Ψ_+` and `o = 0`, since `|(0, −1)|` lies in the closure of `|Ψ_+(U)|` for every `U ∋ 0` but
  not in `|Ψ_+(ℝ)|`.
* `expBasic`: on the trivial groupoid `{1} ⋉ ℝ`, `F(x) = {Ψ₀}` for `x ≤ 0` and `{Ψ₀, Ψ_e}` for
  `x > 0`, with `Ψ₀ = id` and `Ψ_e(t) = eᵗ` (both with the trivial group).  An element of
  `M(Ψ_a, Ψ_b)` is determined by its source; the transition data is keyed by the constant key.
  `|Ψ₀|` is onto, so `T` is metrizable and properness holds.  No element of `M(Ψ₀, Ψ_e)` has
  source `0`, but every neighbourhood of `0` contains sources of elements.

## What is formalized

* `reflectionBasic_hB`, `reflectionBasic_metrizableSpace`, `reflectionBasic_propernessV2`,
  `reflectionBasic_t2Space` (witnesses for the hypotheses of 19.4.2–19.4.8).
* `exists_pos_mem_of_isOpen`; `gluedBasic_hB`, `gluedBasic_propernessV3`,
  `gluedBasic_not_propernessV2`, `gluedBasic_not_propernessV1` and
  **`proposition_19_4_2_v3_without_limit`** ((v3) without the limit in the fibre does not imply
  (v1), (v2); we read (v3) with the limit `q` satisfying `|Ψ(q)| = z`, `proposition_19_4_2`).
* `lineMap`, `lineInv`, `lineUnif`, `expU`, `expData`, `expBasic`, `expBasic_hB`,
  `expBasic_metrizableSpace`, `expBasic_propernessV2`, `expBasic_exists_trans` (the witness for
  the hypothesis of `lemma_19_4_3_hyp`, between two different uniformizers),
  `expBasic_not_lemma_19_4_3` and **`not_lemma_19_4_3`** (the form at sources is
  `lemma_19_4_3_hyp`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace Filter

open scoped ContDiff

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

open EpGroupoid.Examples

/-- An open set of `ℝ` containing `0` contains a positive number. -/
theorem exists_pos_mem_of_isOpen {W : Set (Fin 1 → ℝ)} (hW : IsOpen W)
    (h0 : (0 : Fin 1 → ℝ) ∈ W) : ∃ t ∈ W, 0 < t 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW 0 h0
  refine ⟨fun _ => r / 2, hball ?_, half_pos hr⟩
  rw [Metric.mem_ball, dist_zero_right, pi_norm_const, Real.norm_eq_abs,
    abs_of_pos (half_pos hr)]
  exact half_lt_self hr

/-! ### `reflectionBasic`: the witness -/

section Reflection

theorem reflectionBasic_hB : reflectionBasic.U.HasClassUniformizers :=
  (translationBasic_hasUniformizers _).hasClassUniformizers

/-- The natural topology of `reflectionBasic` is metrizable (`|Ψ₀|` is onto). -/
theorem reflectionBasic_metrizableSpace :
    @MetrizableSpace _ (reflectionBasic.natTop reflectionBasic_hB) :=
  reflectionBasic.metrizableSpace_natTop_of_surjective reflectionBasic_hB (α := 0)
    (Ψ := tautUniformizer (rnPolyfold 1) isScSmoothMap_units_smul) rfl fun z => by
      obtain ⟨x, rfl⟩ :=
        (GroupoidalCategory.translation ℤˣ (Fin 1 → ℝ)).toGroupoidStr.surjective_π z
      exact ⟨x, rfl⟩

/-- **The witness for the properness condition**: `reflectionBasic` satisfies (v2). -/
theorem reflectionBasic_propernessV2 : reflectionBasic.PropernessV2 reflectionBasic_hB :=
  ((reflectionBasic.proposition_19_4_7 reflectionBasic_hB).1 reflectionBasic_metrizableSpace).1

/-- The natural topology of `reflectionBasic` is Hausdorff (the witness for
`proposition_19_4_2_three_two_hyp`). -/
theorem reflectionBasic_t2Space : @T2Space _ (reflectionBasic.natTop reflectionBasic_hB) :=
  (reflectionBasic.proposition_19_4_5 reflectionBasic_hB reflectionBasic_propernessV2).1

end Reflection

/-! ### `gluedBasic`: (v3) does not imply (v2) -/

section Glued

theorem gluedBasic_hB : gluedBasic.U.HasClassUniformizers :=
  gluedBasic_hasUniformizers.hasClassUniformizers

/-- (v3) as printed holds for `gluedBasic` (the domains are `ℝ`). -/
theorem gluedBasic_propernessV3 : gluedBasic.PropernessV3 gluedBasic_hB :=
  gluedBasic.propernessV3_of_locallyCompactSpace gluedBasic_hB fun Ψ => by
    obtain ⟨Ψ₁, α, hΨ₁⟩ := Ψ
    have h := gluedU_mem hΨ₁
    subst h
    exact inferInstanceAs (LocallyCompactSpace (Fin 1 → ℝ))

/-- (v2) does not hold for `gluedBasic` at `Ψ_+` and `o = 0`: `|(0, −1)|` lies in the closure of
`|Ψ_+(U)|` for every open `U ∋ 0`, but not in `|Ψ_+(ℝ)|`. -/
theorem gluedBasic_not_propernessV2 : ¬ gluedBasic.PropernessV2 gluedBasic_hB := by
  intro hv
  let _inst := gluedBasic.natTop gluedBasic_hB
  obtain ⟨U, hU, h0, hcl⟩ := hv ⟨gluedUnif 1, ((0 : Fin 1 → ℝ), 1), rfl⟩ (0 : Fin 1 → ℝ)
  have hU' : IsOpen (U : Set (Fin 1 → ℝ)) := hU
  have hmem : gluedLines.π ((0 : Fin 1 → ℝ), -1) ∈
      closure ((fun q => gluedLines.π ((gluedUnif 1).obj q)) '' U) := by
    rw [mem_closure_iff]
    intro W hW hzW
    obtain ⟨V, hV, h0V, hsV⟩ := gluedBasic_natOpen hW hzW
    obtain ⟨t, ht, htp⟩ := exists_pos_mem_of_isOpen (hU'.inter hV) ⟨h0, h0V⟩
    refine ⟨gluedLines.π (t, 1), ?_, t, ht.1, rfl⟩
    rw [← gluedLines_π_eq_iff.2 ⟨rfl, Or.inr htp⟩]
    exact hsV t ht.2
  obtain ⟨q, hq⟩ := hcl hmem
  change gluedLines.π (q, 1) = gluedLines.π ((0 : Fin 1 → ℝ), -1) at hq
  obtain ⟨rfl, h | h⟩ := gluedLines_π_eq_iff.1 hq
  · exact absurd h (by decide)
  · exact lt_irrefl _ h

/-- (v1) does not hold for `gluedBasic` (by `proposition_19_4_2_one_iff_two`). -/
theorem gluedBasic_not_propernessV1 : ¬ gluedBasic.PropernessV1 := fun h =>
  gluedBasic_not_propernessV2 ((gluedBasic.proposition_19_4_2_one_iff_two gluedBasic_hB).1 h)

/-- **2021 Proposition 19.4.2, p. 880, with (v3) read without a limit in the fibre**: for
`gluedBasic` (Remark 19.2.3), (v3) in that form holds but (v1) and (v2) do not.  We read (v3) with
the limit `q` satisfying `|Ψ(q)| = z`, which the proof of (3) ⇒ (1) uses; then the three
conditions are equivalent (`proposition_19_4_2`), and (v3) in the form above implies (v2) when `T`
is Hausdorff (`proposition_19_4_2_three_two_hyp`). -/
theorem proposition_19_4_2_v3_without_limit :
    ¬ ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (hB : B.U.HasClassUniformizers),
      (B.PropernessV1 ↔ B.PropernessV2 hB) ∧ (B.PropernessV2 hB ↔ B.PropernessV3 hB) := fun h =>
  gluedBasic_not_propernessV2 ((h _ gluedBasic gluedBasic_hB).2.2 gluedBasic_propernessV3)

end Glued

/-! ### `expBasic`: Lemma 19.4.3 at a limit of sources -/

section Exp

open GroupoidStr (TransitionSet)

/-- The groupoidal category `{1} ⋉ ℝ` (only units). -/
abbrev lineCat : GroupoidalCategory.{0} :=
  GroupoidalCategory.translation (⊥ : Subgroup ℤˣ) (Fin 1 → ℝ)

/-- `lineMap false = id` and `lineMap true = (t ↦ eᵗ)`. -/
def lineMap : Bool → (Fin 1 → ℝ) → Fin 1 → ℝ
  | false => id
  | true => fun y _ => Real.exp (y 0)

/-- The inverses on the ranges: `lineInv false = id` and `lineInv true = log`. -/
def lineInv : Bool → (Fin 1 → ℝ) → Fin 1 → ℝ
  | false => id
  | true => fun x _ => Real.log (x 0)

theorem fin1_ext {x y : Fin 1 → ℝ} (h : x 0 = y 0) : x = y :=
  funext fun i => by rw [Subsingleton.elim i 0]; exact h

theorem lineInv_lineMap (b : Bool) (y : Fin 1 → ℝ) : lineInv b (lineMap b y) = y := by
  cases b
  · rfl
  · exact fin1_ext (Real.log_exp (y 0))

theorem lineMap_injective (b : Bool) : Injective (lineMap b) :=
  (leftInverse_iff_comp.2 (funext (lineInv_lineMap b))).injective

theorem mem_range_lineMap (b : Bool) (x : Fin 1 → ℝ) :
    x ∈ range (lineMap b) ↔ (b = true → 0 < x 0) := by
  cases b
  · exact ⟨fun _ h => absurd h (by decide), fun _ => ⟨x, rfl⟩⟩
  · refine ⟨?_, fun h => ⟨lineInv true x, fin1_ext (Real.exp_log (h rfl))⟩⟩
    rintro ⟨y, rfl⟩ -
    exact Real.exp_pos _

theorem lineMap_lineInv (b : Bool) {x : Fin 1 → ℝ} (hx : x ∈ range (lineMap b)) :
    lineMap b (lineInv b x) = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [lineInv_lineMap]

theorem isOpen_range_lineMap (b : Bool) : IsOpen (range (lineMap b)) := by
  cases b
  · rw [eq_univ_of_forall fun x => ((mem_range_lineMap false x).2 fun h => absurd h (by decide))]
    exact isOpen_univ
  · have he : range (lineMap true) = {x | 0 < x 0} :=
      ext fun x => (mem_range_lineMap true x).trans ⟨fun h => h rfl, fun h _ => h⟩
    rw [he]
    exact isOpen_lt continuous_const (continuous_apply 0)

theorem contDiff_lineMap (b : Bool) : ContDiff ℝ ∞ (lineMap b) := by
  cases b
  · exact contDiff_id
  · exact contDiff_pi.2 fun _ => Real.contDiff_exp.comp (contDiff_apply ℝ ℝ 0)

theorem contDiffOn_lineInv (b : Bool) : ContDiffOn ℝ ∞ (lineInv b) (range (lineMap b)) := by
  cases b
  · exact contDiffOn_id
  · refine contDiffOn_pi.2 fun _ => Real.contDiffOn_log.comp (contDiff_apply ℝ ℝ 0).contDiffOn
      fun x hx => ?_
    exact ne_of_gt ((mem_range_lineMap true x).1 hx rfl)

theorem lineMap_isScSmoothOn (a b : Bool) :
    (rnPolyfold 1).IsScSmoothOn (rnPolyfold 1) (lineInv b ∘ lineMap a)
      (lineMap a ⁻¹' range (lineMap b)) :=
  isScSmoothOn_rn_rn_of_contDiffOn
    ((isOpen_range_lineMap b).preimage (contDiff_lineMap a).continuous)
    ((contDiffOn_lineInv b).comp (contDiff_lineMap a).contDiffOn fun _ hq => hq)

/-- `lineInv b ∘ lineMap a` is an sc-diffeomorphism from `lineMap a⁻¹(range (lineMap b))` onto
`lineMap b⁻¹(range (lineMap a))`. -/
theorem lineMap_isScDiffeoOn (a b : Bool) :
    (rnPolyfold 1).IsScDiffeoOn (rnPolyfold 1) (lineInv b ∘ lineMap a) (lineInv a ∘ lineMap b)
      (lineMap a ⁻¹' range (lineMap b)) (lineMap b ⁻¹' range (lineMap a)) where
  isScSmoothOn := lineMap_isScSmoothOn a b
  isScSmoothOn_inv := lineMap_isScSmoothOn b a
  mapsTo q hq := by
    change lineMap b (lineInv b (lineMap a q)) ∈ range (lineMap a)
    rw [lineMap_lineInv b hq]
    exact mem_range_self q
  mapsTo_inv q hq := by
    change lineMap a (lineInv a (lineMap b q)) ∈ range (lineMap b)
    rw [lineMap_lineInv a hq]
    exact mem_range_self q
  left_inv q hq := by
    change lineInv a (lineMap b (lineInv b (lineMap a q))) = q
    rw [lineMap_lineInv b hq, lineInv_lineMap]
  right_inv q hq := by
    change lineInv b (lineMap a (lineInv a (lineMap b q))) = q
    rw [lineMap_lineInv a hq, lineInv_lineMap]

/-- **The uniformizer `lineMap b : ℝ → ℝ`** of `{1} ⋉ ℝ`, with the trivial group. -/
def lineUnif (b : Bool) : lineCat.Uniformizer where
  O := Fin 1 → ℝ
  P := rnPolyfold 1
  G := (⊥ : Subgroup ℤˣ)
  smooth_smul g := isScSmoothMap_units_smul (g : ℤˣ)
  functor :=
    { obj := lineMap b
      mor := fun p => (p.1, lineMap b p.2)
      src_mor := fun _ => rfl
      tgt_mor := fun p => by
        change p.1 • lineMap b p.2 = lineMap b (p.1 • p.2)
        rw [gluedUnif_smul_eq, gluedUnif_smul_eq]
      mor_comp := fun _ _ _ => rfl
      mor_unit := fun _ => rfl }
  injective_obj := lineMap_injective b
  full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => by
    have hs' : ψ.2 = lineMap b x := hs
    have ht' : ψ.2 = lineMap b x' := by
      rw [← gluedUnif_smul_eq ψ.1 ψ.2]
      exact ht
    refine ⟨(ψ.1, x), rfl, ?_, Prod.ext rfl hs'.symm⟩
    change ψ.1 • x = x'
    rw [gluedUnif_smul_eq]
    exact lineMap_injective b (hs'.symm.trans ht')
  faithful := (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ _ =>
    Prod.ext (Subtype.ext ((Subgroup.mem_bot.1 φ.1.2).trans (Subgroup.mem_bot.1 φ'.1.2).symm)) hs

/-- An element `(q, φ, q')` of `M(lineMap a, lineMap b)` has `lineMap a q = lineMap b q'`. -/
theorem lineUnif_trans_eq {a b : Bool} (h : (lineUnif a).Trans (lineUnif b)) :
    lineMap a h.src = lineMap b h.tgt := by
  have hs : h.mor.2 = lineMap a h.src := h.src_mor
  have ht : h.mor.1 • h.mor.2 = lineMap b h.tgt := h.tgt_mor
  rw [gluedUnif_smul_eq] at ht
  exact hs.symm.trans ht

/-- Elements of `M(lineMap a, lineMap b)` are determined by their source. -/
theorem lineUnif_trans_ext {a b : Bool} (h₁ h₂ : (lineUnif a).Trans (lineUnif b))
    (hs : h₁.src = h₂.src) : h₁ = h₂ := by
  have a₁ : h₁.mor.2 = lineMap a h₁.src := h₁.src_mor
  have a₂ : h₂.mor.2 = lineMap a h₂.src := h₂.src_mor
  have hm : h₁.mor = h₂.mor := Prod.ext
    (Subtype.ext ((Subgroup.mem_bot.1 h₁.mor.1.2).trans (Subgroup.mem_bot.1 h₂.mor.1.2).symm))
    (by rw [a₁, a₂, hs])
  refine TransitionSet.ext hs hm (lineMap_injective b ?_)
  rw [← lineUnif_trans_eq, ← lineUnif_trans_eq, hs]

/-- `M(lineMap a, lineMap b)` has an element over `q` iff `lineMap a q ∈ range (lineMap b)`. -/
theorem lineUnif_exists_iff {a b : Bool} (q : Fin 1 → ℝ) :
    (∃ h : (lineUnif a).Trans (lineUnif b), h.src = q) ↔ lineMap a q ∈ range (lineMap b) := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h.tgt, (lineUnif_trans_eq h).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨⟨q, (1, lineMap a q), y, rfl, (one_smul _ _).trans hy.symm⟩, rfl⟩

/-- **The uniformizer construction `expU`**: `F(x) = {lineMap false}` for `x ≤ 0` and
`F(x) = {lineMap false, lineMap true}` for `x > 0`. -/
def expU : lineCat.UniformizerConstruction where
  F x := {Ψ | Ψ = lineUnif false ∨ (Ψ = lineUnif true ∧ 0 < x 0)}
  isAt x Ψ hΨ := by
    rcases hΨ with rfl | ⟨rfl, hx⟩
    · exact ⟨x, rfl⟩
    · exact ⟨lineInv true x, lineMap_lineInv true ((mem_range_lineMap true x).2 fun _ => hx)⟩

theorem expU_unif (Ψ : expU.Unif) : ∃ b, Ψ.1 = lineUnif b := by
  obtain ⟨_, _, h | ⟨h, -⟩⟩ := Ψ
  exacts [⟨false, h⟩, ⟨true, h⟩]

/-- The domain `D(h)`: the `q` over which `M(Ψ, Ψ')` has an element. -/
def expDom (Ψ Ψ' : expU.Unif) (_h : Ψ.1.Trans Ψ'.1) : Set Ψ.1.O :=
  {q | ∃ h' : Ψ.1.Trans Ψ'.1, h'.src = q}

theorem expDom_eq {a b : Bool} (h₁ : ∃ α, lineUnif a ∈ expU.F α)
    (h₂ : ∃ α, lineUnif b ∈ expU.F α) (h : (lineUnif a).Trans (lineUnif b)) :
    expDom ⟨_, h₁⟩ ⟨_, h₂⟩ h = lineMap a ⁻¹' range (lineMap b) :=
  ext fun q => lineUnif_exists_iff q

theorem isOpen_expDom (Ψ Ψ' : expU.Unif) (h : Ψ.1.Trans Ψ'.1) : IsOpen (expDom Ψ Ψ' h) := by
  obtain ⟨Ψ₁, hΨ₁⟩ := Ψ
  obtain ⟨Ψ₂, hΨ₂⟩ := Ψ'
  obtain ⟨a, rfl⟩ := expU_unif ⟨Ψ₁, hΨ₁⟩
  obtain ⟨b, rfl⟩ := expU_unif ⟨Ψ₂, hΨ₂⟩
  rw [expDom_eq]
  exact (isOpen_range_lineMap b).preimage (contDiff_lineMap a).continuous

/-- **The transition data of `expU`**: `F_h(q)` is the element of `M(Ψ, Ψ')` over `q` (keyed by
the constant key). -/
def expData : expU.TransitionData :=
  UniformizerConstruction.TransitionData.ofKey (U := expU) (fun _ : lineCat.Mor => ()) expDom
    (fun Ψ Ψ' => by
      obtain ⟨Ψ₁, hΨ₁⟩ := Ψ
      obtain ⟨Ψ₂, hΨ₂⟩ := Ψ'
      obtain ⟨a, rfl⟩ := expU_unif ⟨Ψ₁, hΨ₁⟩
      obtain ⟨b, rfl⟩ := expU_unif ⟨Ψ₂, hΨ₂⟩
      exact fun h₁ h₂ hs _ => lineUnif_trans_ext h₁ h₂ hs)
    (fun _ _ _ _ => ⟨fun ⟨h', hs⟩ => ⟨h', hs, rfl⟩, fun ⟨h', hs, _⟩ => ⟨h', hs⟩⟩)
    isOpen_expDom
    (fun Ψ Ψ' h => by
      obtain ⟨Ψ₁, hΨ₁⟩ := Ψ
      obtain ⟨Ψ₂, hΨ₂⟩ := Ψ'
      obtain ⟨a, rfl⟩ := expU_unif ⟨Ψ₁, hΨ₁⟩
      obtain ⟨b, rfl⟩ := expU_unif ⟨Ψ₂, hΨ₂⟩
      rw [expDom_eq]
      refine ⟨lineInv b ∘ lineMap a, lineInv a ∘ lineMap b, lineMap b ⁻¹' range (lineMap a),
        lineMap_isScDiffeoOn a b, fun h' _ => ?_⟩
      change lineInv b (lineMap a h'.src) = h'.tgt
      rw [lineUnif_trans_eq h']
      exact lineInv_lineMap b h'.tgt)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

/-- **The basic construction `expBasic`** of `{1} ⋉ ℝ`. -/
def expBasic : lineCat.BasicConstruction := ⟨expU, ⟦expData⟧⟩

theorem expBasic_hB : expBasic.U.HasClassUniformizers :=
  UniformizerConstruction.HasUniformizers.hasClassUniformizers fun _ =>
    ⟨lineUnif false, Or.inl rfl⟩

/-- The natural topology of `expBasic` is metrizable (`|lineMap false|` is onto). -/
theorem expBasic_metrizableSpace : @MetrizableSpace _ (expBasic.natTop expBasic_hB) :=
  expBasic.metrizableSpace_natTop_of_surjective expBasic_hB (α := 0) (Ψ := lineUnif false)
    (Or.inl rfl) fun z => by
      obtain ⟨x, rfl⟩ := lineCat.toGroupoidStr.surjective_π z
      exact ⟨x, rfl⟩

/-- `expBasic` satisfies the properness condition. -/
theorem expBasic_propernessV2 : expBasic.PropernessV2 expBasic_hB :=
  ((expBasic.proposition_19_4_7 expBasic_hB).1 expBasic_metrizableSpace).1

/-- `lineMap false` as an element of `F`. -/
abbrev expΨ₀ : expBasic.U.Unif := ⟨lineUnif false, 0, Or.inl rfl⟩

/-- `lineMap true` as an element of `F`. -/
abbrev expΨₑ : expBasic.U.Unif := ⟨lineUnif true, fun _ => 1, Or.inr ⟨rfl, one_pos⟩⟩

/-- **The witness for `lemma_19_4_3_hyp`**: `M(Ψ₀, Ψ_e)` (two different uniformizers) has an
element with source `1`. -/
theorem expBasic_exists_trans :
    ∃ h : expBasic.M expΨ₀ expΨₑ, (h : (lineUnif false).Trans (lineUnif true)).src = fun _ => 1 :=
  (lineUnif_exists_iff _).2 ((mem_range_lineMap true _).2 fun _ => one_pos)

/-- For `expBasic`, `Ψ₀`, `Ψ_e` and `o = 0` the conclusion of Lemma 19.4.3 does not hold: no element of
`M(Ψ₀, Ψ_e)` has source `0`, but every neighbourhood of `0` contains the source of one. -/
theorem expBasic_not_lemma_19_4_3 :
    ¬ ∃ (H : Set (expBasic.M expΨ₀ expΨₑ)) (Uo : Set (Fin 1 → ℝ))
        (Uh : expBasic.M expΨ₀ expΨₑ → Set (expBasic.M expΨ₀ expΨₑ)),
      H.Finite ∧ IsOpen Uo ∧ (0 : Fin 1 → ℝ) ∈ Uo ∧
      (∀ h ∈ H, IsOpen (Uh h) ∧ h ∈ Uh h ∧
        IsOpenEmbedding ((Uh h).domRestrict fun a : expBasic.M expΨ₀ expΨₑ =>
          (a : (lineUnif false).Trans (lineUnif true)).src) ∧
        (fun a : expBasic.M expΨ₀ expΨₑ => (a : (lineUnif false).Trans (lineUnif true)).src) ''
          Uh h = Uo) ∧
      ∀ h : expBasic.M expΨ₀ expΨₑ, (h : (lineUnif false).Trans (lineUnif true)).src ∈ Uo →
        ∃ h' ∈ H, h ∈ Uh h' := by
  rintro ⟨H, Uo, Uh, -, hUo, h0, hH, hcov⟩
  obtain ⟨t, ht, htp⟩ := exists_pos_mem_of_isOpen hUo h0
  obtain ⟨h, hs⟩ := (lineUnif_exists_iff (a := false) (b := true) t).2
    ((mem_range_lineMap true t).2 fun _ => htp)
  obtain ⟨h', hh', -⟩ := hcov h (hs ▸ ht)
  rw [← (hH h' hh').2.2.2] at h0
  obtain ⟨m, -, hm⟩ := h0
  have h0r := (lineUnif_exists_iff (a := false) (b := true) 0).1 ⟨m, hm⟩
  exact lt_irrefl _ ((mem_range_lineMap true 0).1 h0r rfl)

/-- **2021 Lemma 19.4.3, p. 881, does not hold as we read it** when `o` is not the source of an
element of `M(Ψ, Ψ')`: for `expBasic`, which satisfies the properness condition, `Ψ₀`, `Ψ_e` and
`o = 0` there are no `h_i`, `U(o)`, `U(h_i)` with (1) and (2).  With `o` the source of an element
the statement holds (`lemma_19_4_3_hyp`). -/
theorem not_lemma_19_4_3 :
    ¬ ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (hB : B.U.HasClassUniformizers),
      B.PropernessV2 hB → ∀ (Ψ Ψ' : B.U.Unif) (o : Ψ.1.O),
      ∃ (H : Set (B.M Ψ Ψ')) (Uo : Set Ψ.1.O) (Uh : B.M Ψ Ψ' → Set (B.M Ψ Ψ')),
        H.Finite ∧ IsOpen Uo ∧ o ∈ Uo ∧
        (∀ h ∈ H, IsOpen (Uh h) ∧ h ∈ Uh h ∧
          IsOpenEmbedding ((Uh h).domRestrict fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) ∧
          (fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) '' Uh h = Uo) ∧
        ∀ h : B.M Ψ Ψ', (h : Ψ.1.Trans Ψ'.1).src ∈ Uo → ∃ h' ∈ H, h ∈ Uh h' := fun h =>
  expBasic_not_lemma_19_4_3
    (h _ expBasic expBasic_hB expBasic_propernessV2 expΨ₀ expΨₑ (0 : Fin 1 → ℝ))

end Exp

end GroupoidalCategory

end Polyfold
