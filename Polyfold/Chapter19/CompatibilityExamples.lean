import Polyfold.Chapter19.CoveringLocalExamples
import Polyfold.Chapter19.CoveringPullbackCoherence

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19:
**Definition 19.7.11** (p. 910), **Definition 19.7.16** and **Lemma 19.7.17** (p. 916),
**Proposition 19.7.15 (2)** (p. 915) and the note after **Definition 19.8.4** (p. 934, "(1) implies
(3)").  Numbers and pages are the 2021 text's.

# Examples on the compatibility of the members of `F̂`

Definition 19.7.11 asks no compatibility between the proper covering uniformizers of `F̂`; we
read Proposition 19.7.15 (2), Lemma 19.7.17 and their consequences under `IsCompatible` (every top
target map `t̂ : M(Ψ̂, Ψ̂') → E'` is continuous).  `twistBasic` (`CoveringLocalExamples.lean`, with
`F̂(0) = {absCU 0, twistCU}`, `twistCU` twisted by `σ(x) = −1` for `|x| > 1`) is not compatible
(`not_isCompatible_twistBasic`).  This file determines what of Lemma 19.7.17 and of the note
after Definition 19.8.4 holds without the compatibility.

## Lemma 19.7.17 for `twistBasic`

* **(1) holds**: `twistBasic_natOpenA_iff` — `T_{|A|}` of `twistBasic` equals `T_{|A|}` of
  `absBasic`; the twisted member is used only at points over `|0|`, where it agrees with
  `absCU 0` near `τ̂⁻¹(0)`.  So `T_{|A|}` is a metrizable topology, the orbit-space topology of
  `|A| ≅ ℝ` (`lemma_19_7_17_one_twistBasic`, with `absInv : |A| → ℝ`, `|(i, x)| ↦ i x`,
  injective).
* **(2) does not hold**: `lemma_19_7_17_two_without_compatible` — for `Ψ̂ = twistCU` and
  `V = {1} × (1/2, 3/2)` the set `|Ψ̂(V)|` (invariant in `(1/2, 1] ∪ (−3/2, −1)`) is not in
  `T_{|A|}`.

## Lemma 19.7.17 (1) without the compatibility

* `twoBasic`: the members of `absBasic` and, at `β = 2`, a second member `twoCU` over the slice
  `{1} ⋉ (0, ∞)` twisted by `σ₂(x) = −1` for `x > 2` (`twistSliceCU`, a twisted sheet model for
  any slice).  `lemma_19_7_17_one_without_compatible`: `W₁ = absInv⁻¹((3/2, 2] ∪ (−5/2, −2))`
  and `W₂ = absInv⁻¹((3/2, 5/2))` are in `T_{|A|}` (`W₁` through `twoCU` at `|(1, 2)|`), and
  `W₁ ∩ W₂ = absInv⁻¹((3/2, 2])` is not: at `|(1, 2)|` the members `absCU (±2)` reach invariants
  `2 + t`, and `twoCU` reaches `−(2 + t)`.  So `T_{|A|}` is not a topology
  (`twoBasic_no_topology`) and `twoBasic` is not compatible.  Lemma 19.7.17 (1) needs the
  compatibility.

## The note after Definition 19.8.4

* As printed (Definition 19.7.11 without compatibility) "(1) implies (3)" holds:
  `definition_19_8_4_one_implies_three` (`(F̂, 𝓕)` is a basic construction for `P` with
  underlying `(F, 𝓕)`, and `F(α) ≠ ∅` on every class gives `F̂(β) ≠ ∅` on every class).
* With the compatibility read into Definition 19.7.11 it does not follow from (1):
  `twistFt` (`F̃(0) = {absPU 0, twistPU}`, `twistPU = (Ψ, twistCU, Γ)` with the strong bundle
  uniformizer `Γ` of `absPU 0`, Definitions 19.8.1, 19.8.2) has a transition construction
  `twistFt𝓕` with (1) (`definition_19_8_4_one_without_compatible`), and even with (1)–(3)
  (`twistFtTransition`, coherence `twistFt_isCoherent` transferred from `absFt_isCoherent` by
  `cohPair_congr`), whose `(F̂, 𝓕) = twistBasic` is not compatible
  (`definition_19_8_4_without_compatible`).  So `IsCompatible` in Theorem 19.8.6 (5), Lemma
  19.8.21 and Theorem 19.8.22 is a hypothesis beyond Definitions 19.8.4 and 19.8.5.
-/

open Set Function Topology TopologicalSpace Filter

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples GCT.PolyfoldConstruction Chapter19

section Invariant

/-- `(i, x) ↦ i x`. -/
def absInvPt (a : ℤˣ × (Fin 1 → ℝ)) : ℝ := ((a.1 : ℤ) : ℝ) * a.2 0

theorem units_smul_rn_apply_zero (k : ℤˣ) (x : Fin 1 → ℝ) : (k • x) 0 = ((k : ℤ) : ℝ) * x 0 := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp
  · rw [units_smul_rn_neg_one]
    simp

theorem absInvPt_smul (k : ℤˣ) (a : ℤˣ × (Fin 1 → ℝ)) : absInvPt (k • a) = absInvPt a := by
  obtain ⟨i, x⟩ := a
  change (((k * i : ℤˣ) : ℤ) : ℝ) * (k • x) 0 = ((i : ℤ) : ℝ) * x 0
  rw [units_smul_rn_apply_zero, Units.val_mul, Int.cast_mul]
  have hk : ((k : ℤ) : ℝ) * ((k : ℤ) : ℝ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  calc ((k : ℤ) : ℝ) * ((i : ℤ) : ℝ) * (((k : ℤ) : ℝ) * x 0)
      = (((k : ℤ) : ℝ) * ((k : ℤ) : ℝ)) * (((i : ℤ) : ℝ) * x 0) := by ring
    _ = _ := by rw [hk, one_mul]

/-- **The invariant `|A| → ℝ`**, `|(i, x)| ↦ i x`. -/
def absInv : absCatA.OrbitSpace → ℝ :=
  Quotient.lift absInvPt fun a b h => by
    obtain ⟨φ, hs, ht⟩ := (GroupoidalCategory.π_eq_π_iff absCatA).1 (Quotient.sound h)
    have hs' : φ.2 = a := hs
    have ht' : φ.1 • φ.2 = b := ht
    rw [← ht', hs', absInvPt_smul]

@[simp] theorem absInv_π (a : ℤˣ × (Fin 1 → ℝ)) : absInv (absCatA.π a) = absInvPt a := rfl

theorem units_cast_mul_self (i : ℤˣ) : ((i : ℤ) : ℝ) * ((i : ℤ) : ℝ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

/-- `absInv` is injective: `|A| ≅ ℝ`. -/
theorem absInv_injective : Injective absInv := by
  intro z w h
  induction z using Quotient.inductionOn with
  | h a =>
  induction w using Quotient.inductionOn with
  | h b =>
  obtain ⟨i, x⟩ := a
  obtain ⟨j, y⟩ := b
  change ((i : ℤ) : ℝ) * x 0 = ((j : ℤ) : ℝ) * y 0 at h
  refine (GroupoidalCategory.π_eq_π_iff absCatA).2 ⟨(j * i, (i, x)), rfl, ?_⟩
  change (j * i) • (i, x) = (j, y)
  refine Prod.ext ?_ ?_
  · change j * i * i = j
    rw [mul_assoc, Int.units_mul_self, mul_one]
  · funext t
    change ((j * i) • x) t = y t
    rw [Fin.eq_zero t, units_smul_rn_apply_zero, Units.val_mul, Int.cast_mul, mul_assoc, h,
      ← mul_assoc,
      units_cast_mul_self, one_mul]

theorem continuous_absInvPt : Continuous absInvPt :=
  ((continuous_of_discreteTopology (f := fun i : ℤˣ => ((i : ℤ) : ℝ))).comp continuous_fst).mul
    ((continuous_apply 0).comp continuous_snd)

/-- Preimages of open sets under `absInv` are open in `T_{|A|}` of `absBasic`. -/
theorem natOpenA_abs_preimage {S : Set ℝ} (hS : IsOpen S) : absBasic.NatOpenA (absInv ⁻¹' S) :=
  (natOpenA_abs_iff _).2 (hS.preimage continuous_absInvPt)

end Invariant

/-! ### Comparison of `T_{|A|}` for different `F̂` -/

namespace CoveringBasicConstruction

variable {A B : GroupoidalCategory.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}

/-- `T_{|A|}` grows with `F̂`. -/
theorem natOpenA_mono {Bh Bh' : CoveringBasicConstruction P}
    (h : ∀ β, Bh.hatU.F β ⊆ Bh'.hatU.F β) {W : Set A.OrbitSpace} (hW : Bh.NatOpenA W) :
    Bh'.NatOpenA W := by
  intro z hz
  obtain ⟨β, hβ, Ψh, hΨh, rest⟩ := hW z hz
  exact ⟨β, hβ, Ψh, h β hΨh, rest⟩

end CoveringBasicConstruction

/-! ### `twistBasic`: Lemma 19.7.17 (1) holds, (2) does not -/

section TwistBasic

theorem absHatU_subset_twistHatU (β : Fin 1 → ℝ) :
    absBasic.hatU.F β ⊆ twistBasic.hatU.F β := fun _ h => Or.inl (mem_singleton_iff.1 h)

/-- **`T_{|A|}` of `twistBasic` is `T_{|A|}` of `absBasic`**: the twisted member of `F̂(0)` is only
used at points over `|0|`, and near `τ̂⁻¹(0)` it agrees with `absCU 0`. -/
theorem twistBasic_natOpenA_iff (W : Set absCatA.OrbitSpace) :
    twistBasic.NatOpenA W ↔ absBasic.NatOpenA W := by
  refine ⟨fun hW z hz => ?_, CoveringBasicConstruction.natOpenA_mono absHatU_subset_twistHatU⟩
  obtain ⟨β, hβ, Ψh, hΨh, e, he, V, hV, heV, hsub⟩ := hW z hz
  rcases hΨh with rfl | ⟨h0, hΨ⟩
  · exact ⟨β, hβ, absCU β, mem_singleton _, e, he, V, hV, heV, hsub⟩
  · subst h0
    have hΨ' : Ψh = twistCU := hΨ
    subst hΨ'
    -- `e` lies over `0`
    have he0 : (e.2 : overlapSlice₀.V).1 = 0 := by
      have h1 : absCatB.π 0 = absCatB.π (e.2 : overlapSlice₀.V).1 := by
        rw [hβ, ← he]
        rfl
      obtain ⟨φ, hs, ht⟩ := (GroupoidalCategory.π_eq_π_iff absCatB).1 h1
      have hs' : φ.2 = 0 := hs
      have ht' : φ.1 • φ.2 = (e.2 : overlapSlice₀.V).1 := ht
      rw [← ht', hs', units_smul_zero_rn]
    have hcV : Continuous fun d : ℤˣ × overlapSlice₀.V => |(d.2 : overlapSlice₀.V).1 0| :=
      continuous_abs.comp ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_snd))
    set V' : Set twistCU.ObjE :=
      V ∩ (fun d : ℤˣ × overlapSlice₀.V => |(d.2 : overlapSlice₀.V).1 0|) ⁻¹' Iio 1
    have hV' : IsOpen V' := hV.inter (isOpen_Iio.preimage hcV)
    have hsign : ∀ d ∈ V', twistSign (d.2 : overlapSlice₀.V).1 = 1 := fun d hd => by
      simp only [twistSign, not_lt.2 (show |(d.2 : overlapSlice₀.V).1 0| < 1 from hd.2).le,
        if_false]
    have heV' : e ∈ V' := ⟨heV, show |(e.2 : overlapSlice₀.V).1 0| < 1 by
      rw [he0]; norm_num⟩
    have hobj : ∀ d ∈ V', twistCU.hat.obj d =
        (sliceCU overlapSlice₀ 0 (mem_univ _) zero_fix).hat.obj d := fun d hd => by
      change (twistSign (d.2 : overlapSlice₀.V).1 * d.1, (d.2 : overlapSlice₀.V).1) =
        (d.1, (d.2 : overlapSlice₀.V).1)
      rw [hsign d hd, one_mul]
    refine ⟨0, hβ, sliceCU overlapSlice₀ 0 (mem_univ _) zero_fix, by
      rw [mem_absBasic_iff, absCU_zero], e, by rw [← hobj e heV']; exact he, V', hV', heV', ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    refine hsub ⟨d, hd.1, ?_⟩
    change absCatA.π (twistCU.hat.obj d) =
      absCatA.π ((sliceCU overlapSlice₀ 0 (mem_univ _) zero_fix).hat.obj d)
    rw [hobj d hd]

/-- **`T_{|A|}` of `twistBasic` as a topology** (Definition 19.7.16), through
`twistBasic_natOpenA_iff` and Lemma 19.7.17 (1) for `absBasic`. -/
abbrev twistTopA : TopologicalSpace absCatA.OrbitSpace where
  IsOpen := twistBasic.NatOpenA
  isOpen_univ := (twistBasic_natOpenA_iff _).2 (absBasic.natOpenA_univ
    absCovP_isFiniteToOneCovering absBasic_hasClassUniformizers)
  isOpen_inter _ _ h₁ h₂ := (twistBasic_natOpenA_iff _).2 (absBasic.natOpenA_inter
    absCovP_isFiniteToOneCovering absBasic_isCompatible ((twistBasic_natOpenA_iff _).1 h₁)
    ((twistBasic_natOpenA_iff _).1 h₂))
  isOpen_sUnion _ := twistBasic.natOpenA_sUnion

theorem twistTopA_eq : twistTopA = absTopA :=
  TopologicalSpace.ext (funext fun W => propext ((twistBasic_natOpenA_iff W).trans
    (isOpen_absTopA_iff W).symm))

theorem metrizableSpace_absTopA : @MetrizableSpace _ absTopA := by
  have h := theorem_19_7_25_absBasic.2.2.1
  rw [absBasic_natTopA_eq] at h
  exact h

/-- **2021 Lemma 19.7.17 (1), p. 916, for `twistBasic`**: although `twistBasic` is not compatible
(`not_isCompatible_twistBasic`), `T_{|A|}` (Definition 19.7.16) is a topology, closed under finite
intersections, and metrizable: it is the orbit-space topology `absTopA` of `|A| ≅ ℝ`. -/
theorem lemma_19_7_17_one_twistBasic :
    ¬ twistBasic.IsCompatible ∧ twistBasic.HasClassUniformizers ∧
      (∀ W₁ W₂, twistBasic.NatOpenA W₁ → twistBasic.NatOpenA W₂ →
        twistBasic.NatOpenA (W₁ ∩ W₂)) ∧
      (∀ W, twistBasic.NatOpenA W ↔ IsOpen[absTopA] W) ∧ @MetrizableSpace _ twistTopA :=
  ⟨not_isCompatible_twistBasic, twistBasic_hasClassUniformizers,
    fun _ _ h₁ h₂ => twistTopA.isOpen_inter _ _ h₁ h₂,
    fun W => (twistBasic_natOpenA_iff W).trans (isOpen_absTopA_iff W).symm,
    twistTopA_eq ▸ metrizableSpace_absTopA⟩

/-- The open set `{1} × (1/2, 3/2)` of the sheets of `twistCU`. -/
def twistV : Set twistY.Ψh.ObjE :=
  {d | d.1 = 1 ∧ 1 / 2 < (d.2 : overlapSlice₀.V).1 0 ∧ (d.2 : overlapSlice₀.V).1 0 < 3 / 2}

theorem isOpen_twistV : IsOpen twistV := by
  have hc : Continuous fun d : twistY.Ψh.ObjE => (d.2 : overlapSlice₀.V).1 0 :=
    (continuous_apply 0).comp (continuous_subtype_val.comp continuous_snd)
  exact ((isOpen_discrete {(1 : ℤˣ)}).preimage continuous_fst).inter
    ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))

/-- `absInv (|Ψ̂(d)|) = σ(x) x` on `twistV`. -/
theorem absInv_twist_image {z : absCatA.OrbitSpace}
    (hz : z ∈ (fun d => absCatA.π (twistY.Ψh.hat.obj d)) '' twistV) :
    absInv z ∈ Ioc (1 / 2) 1 ∪ Ioo (-(3 / 2)) (-1) := by
  obtain ⟨d, ⟨h1, h2, h3⟩, rfl⟩ := hz
  change absInvPt (twistSign (d.2 : overlapSlice₀.V).1 * d.1, (d.2 : overlapSlice₀.V).1) ∈ _
  simp only [absInvPt, h1, mul_one, twistSign]
  split_ifs with h
  · right
    rw [abs_of_pos (by linarith)] at h
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
    constructor <;> linarith
  · left
    rw [abs_of_pos (by linarith), not_lt] at h
    simp only [Units.val_one, Int.cast_one, one_mul]
    exact ⟨h2, h⟩

/-- **2021 Lemma 19.7.17 (2), p. 916, needs the compatibility**: for `twistBasic` (Definition
19.7.11, with `F̂(0) = {absCU 0, twistCU}`), the image `|Ψ̂(V)|` of the open set
`V = {1} × (1/2, 3/2)` under the member `Ψ̂ = twistCU` of `F̂(0)` does not belong to `T_{|A|}`
(its image in `|A| ≅ ℝ` is `(1/2, 1] ∪ (−3/2, −1)`). -/
theorem lemma_19_7_17_two_without_compatible :
    IsFiniteToOneCovering absCovP ∧ twistBasic.HasClassUniformizers ∧ ¬ twistBasic.IsCompatible ∧
      ¬ ∀ (x : twistBasic.hatU.Unif) (V : Set x.Ψh.ObjE), IsOpen V →
        twistBasic.NatOpenA ((fun d => absCatA.π (x.Ψh.hat.obj d)) '' V) := by
  refine ⟨absCovP_isFiniteToOneCovering, twistBasic_hasClassUniformizers,
    not_isCompatible_twistBasic, fun h => ?_⟩
  have hW := (natOpenA_abs_iff _).1 ((twistBasic_natOpenA_iff _).1 (h twistY twistV isOpen_twistV))
  set W := (fun d => absCatA.π (twistY.Ψh.hat.obj d)) '' twistV
  have hc : Continuous fun t : ℝ => ((1 : ℤˣ), (fun _ => t : Fin 1 → ℝ)) :=
    continuous_const.prodMk (continuous_pi fun _ => continuous_id)
  have hO := hW.preimage hc
  have h1 : (1 : ℝ) ∈
      (fun t : ℝ => ((1 : ℤˣ), (fun _ => t : Fin 1 → ℝ))) ⁻¹' (absCatA.π ⁻¹' W) := by
    refine ⟨((1 : ℤˣ), ⟨fun _ => 1, mem_univ _⟩), ⟨rfl, by norm_num, by norm_num⟩, ?_⟩
    change absCatA.π (twistSign (fun _ => (1 : ℝ)) * 1, fun _ => (1 : ℝ)) = _
    have : twistSign (fun _ => (1 : ℝ)) = 1 := by simp [twistSign]
    rw [this, one_mul]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO 1 h1
  set t := 1 + min (ε / 2) (1 / 4)
  have ht1 : 1 < t := by
    have : 0 < min (ε / 2) (1 / 4) := lt_min (by linarith) (by norm_num)
    linarith
  have ht2 : t ≤ 5 / 4 := by
    have : min (ε / 2) (1 / 4) ≤ 1 / 4 := min_le_right _ _
    linarith
  have htb : t ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
    have : min (ε / 2) (1 / 4) ≤ ε / 2 := min_le_left _ _
    linarith
  have hmem := absInv_twist_image (hball htb)
  change absInvPt ((1 : ℤˣ), (fun _ => t : Fin 1 → ℝ)) ∈ _ at hmem
  simp only [absInvPt, Units.val_one, Int.cast_one, one_mul] at hmem
  rcases hmem with ⟨-, h2⟩ | ⟨-, h2⟩ <;> linarith

end TwistBasic


/-! ### A twisted member at `β = 2`: Lemma 19.7.17 (1) does not hold -/

section TwistTwo

/-- **A twisted proper covering uniformizer of a slice** (Definitions 19.7.3, 19.7.4): the sheet
model of `sliceCU D β` with `Ψ̂(i, v) = (σ(v) i, v)` for a `σ : ℝ → ℤ/2` invariant under the
group `H` of the slice. -/
def twistSliceCU (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) (β : Fin 1 → ℝ) (hβ : β ∈ D.V)
    (hfix : ∀ h ∈ D.H, h • β = β) (σ : (Fin 1 → ℝ) → ℤˣ)
    (hσ : ∀ h ∈ D.H, ∀ v, σ (h • v) = σ v) : CoveringUniformizer absCovP β where
  Ψ := absSliceUnif D
  ObjE := ℤˣ × (absSliceUnif D).O
  MorE := (absSliceUnif D).G × (ℤˣ × (absSliceUnif D).O)
  E := sheetEp (absSliceUnif D).smooth_smul ℤˣ
  τ := sheetFunctor (absSliceUnif D).smooth_smul ℤˣ
  model := (sliceCU D β hβ hfix).model
  hat :=
    { obj := fun p => (σ (p.2 : D.V).1 * p.1, (p.2 : D.V).1)
      mor := fun φ => ((φ.1 : D.H).1, (σ (φ.2.2 : D.V).1 * φ.2.1, (φ.2.2 : D.V).1))
      src_mor := fun _ => rfl
      tgt_mor := fun φ => by
        obtain ⟨⟨k, hk⟩, i, v⟩ := φ
        refine Prod.ext ?_ rfl
        change k * (σ v.1 * i) = σ (k • v.1) * (k * i)
        rw [hσ k hk, mul_left_comm]
      mor_comp := fun _ _ _ => rfl
      mor_unit := fun _ => rfl }
  obj_pt := rfl
  injective_hat p q h := by
    have h2 : (p.2 : D.V).1 = (q.2 : D.V).1 := congrArg (fun r => r.2) h
    have h1 : σ (p.2 : D.V).1 * p.1 = σ (q.2 : D.V).1 * q.1 := congrArg (fun r => r.1) h
    rw [h2] at h1
    exact Prod.ext (mul_left_cancel h1) (Subtype.ext h2)
  full_hat := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => by
    have hs' : ψ.2 = (σ (x.2 : D.V).1 * x.1, (x.2 : D.V).1) := hs
    have ht' : ψ.1 • ψ.2 = (σ (x'.2 : D.V).1 * x'.1, (x'.2 : D.V).1) := ht
    rw [hs'] at ht'
    have h1 : ψ.1 * (σ (x.2 : D.V).1 * x.1) = σ (x'.2 : D.V).1 * x'.1 := congrArg Prod.fst ht'
    have h2 : ψ.1 • (x.2 : D.V).1 = (x'.2 : D.V).1 := congrArg Prod.snd ht'
    have hk : ψ.1 ∈ D.H := D.mem_of_smul_mem ψ.1 _ (x.2 : D.V).2 (h2 ▸ (x'.2 : D.V).2)
    rw [← h2, hσ _ hk, mul_left_comm] at h1
    exact ⟨((⟨ψ.1, hk⟩ : D.H), x), rfl, Prod.ext (mul_left_cancel h1) (Subtype.ext h2),
      Prod.ext rfl hs'.symm⟩
  faithful_hat := (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ he =>
    Prod.ext (Subtype.ext (congrArg Prod.fst he)) hs
  obj_comm _ := rfl
  mor_comm _ := rfl
  cartesian_obj o a h := by
    refine ⟨(σ (o : D.V).1 * a.1, o), rfl, Prod.ext ?_ h.symm⟩
    change σ (o : D.V).1 * (σ (o : D.V).1 * a.1) = a.1
    rw [← mul_assoc, Int.units_mul_self, one_mul]
  cartesian_mor φ p h := by
    have h1 : φ.1 = (p.1 : D.H).1 := congrArg Prod.fst h
    have h2 : φ.2.2 = (p.2 : D.V).1 := congrArg Prod.snd h
    refine ⟨(p.1, (σ (p.2 : D.V).1 * φ.2.1, p.2)), rfl, Prod.ext h1.symm (Prod.ext ?_ h2.symm)⟩
    change σ (p.2 : D.V).1 * (σ (p.2 : D.V).1 * φ.2.1) = φ.2.1
    rw [← mul_assoc, Int.units_mul_self, one_mul]

/-- The point `2 ∈ ℝ`. -/
abbrev twoPt : Fin 1 → ℝ := fun _ => 2

theorem twoPt_mem : twoPt ∈ posSlice.V := show (0 : ℝ) < 2 by norm_num

/-- **The twist at `2`**: `σ₂(x) = −1` for `x > 2`, `σ₂(x) = 1` otherwise. -/
def twistSignTwo (x : Fin 1 → ℝ) : ℤˣ := if 2 < x 0 then -1 else 1

theorem twistSignTwo_twoPt : twistSignTwo twoPt = 1 := by simp [twistSignTwo]

/-- **The twisted member at `β = 2`**: the sheet model over the slice `{1} ⋉ (0, ∞)` with
`Ψ̂(i, x) = (σ₂(x) i, x)`. -/
def twoCU : CoveringUniformizer absCovP twoPt :=
  twistSliceCU posSlice twoPt twoPt_mem (bot_fix _ rfl _) twistSignTwo fun h hh v => by
    rw [Subgroup.mem_bot.1 hh, one_smul]

/-- **`F̂` with a twisted member at `2`**: `F̂(β) = {absCU β}` for `β ≠ 2` and
`F̂(2) = {absCU 2, twoCU}` (Definition 19.7.7). -/
def twoHatU : CoveringUniformizerConstruction absCovP :=
  ⟨fun β => {Ψh | Ψh = absCU β ∨ ∃ h : twoPt = β, Ψh = h ▸ twoCU}⟩

theorem twoHatU_slice (Ψ : twoHatU.toUniformizerConstruction.Unif) :
    ∃ D : TranslationSlice ℤˣ (Fin 1 → ℝ), Ψ.1 = sliceUniformizer isScSmoothMap_units_smul D := by
  obtain ⟨Ψ₁, β, Ψh, hmem, hΨ⟩ := Ψ
  rcases hmem with rfl | ⟨rfl, rfl⟩
  · obtain ⟨D, hβ, hfix, h⟩ := absCU_eq β
    refine ⟨D, ?_⟩
    change Ψ₁ = _
    rw [← hΨ, h]
    rfl
  · refine ⟨posSlice, ?_⟩
    change Ψ₁ = _
    rw [← hΨ]
    rfl

/-- **The basic construction with the twisted member at `2`** (Definition 19.7.11): `twoHatU`
with the keyed transitions of `B`. -/
def twoBasic : CoveringBasicConstruction absCovP :=
  ⟨twoHatU, ⟦sliceData isScSmoothMap_units_smul twoHatU_slice⟧⟩

theorem twoBasic_hasClassUniformizers : twoBasic.HasClassUniformizers := fun z =>
  Quotient.inductionOn z fun β => ⟨β, rfl, absCU β, Or.inl rfl⟩

theorem absHatU_subset_twoHatU (β : Fin 1 → ℝ) : absBasic.hatU.F β ⊆ twoBasic.hatU.F β :=
  fun _ h => Or.inl (mem_singleton_iff.1 h)

/-- `|(1, 2)|`. -/
abbrev twoOrbit : absCatA.OrbitSpace := absCatA.π ((1 : ℤˣ), twoPt)

theorem absInv_twoOrbit : absInv twoOrbit = 2 := by
  change ((1 : ℤˣ) : ℤ) * (2 : ℝ) = 2
  norm_num

theorem eq_twoOrbit {z : absCatA.OrbitSpace} (hz : absInv z = 2) : z = twoOrbit :=
  absInv_injective (hz.trans absInv_twoOrbit.symm)

/-- The open set `{1} × (3/2, 5/2)` of the sheets of `twoCU`. -/
def twoV : Set twoCU.ObjE :=
  {d | d.1 = 1 ∧ 3 / 2 < (d.2 : posSlice.V).1 0 ∧ (d.2 : posSlice.V).1 0 < 5 / 2}

theorem isOpen_twoV : IsOpen twoV := by
  have hc : Continuous fun d : ℤˣ × posSlice.V => (d.2 : posSlice.V).1 0 :=
    (continuous_apply 0).comp (continuous_subtype_val.comp continuous_snd)
  exact ((isOpen_discrete {(1 : ℤˣ)}).preimage continuous_fst).inter
    ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))

/-- `W₁ = |A|`-points with invariant in `(3/2, 2] ∪ (−5/2, −2)`. -/
def twoW₁ : Set absCatA.OrbitSpace := absInv ⁻¹' (Ioc (3 / 2) 2 ∪ Ioo (-(5 / 2)) (-2))

/-- `W₂ = |A|`-points with invariant in `(3/2, 5/2)`. -/
def twoW₂ : Set absCatA.OrbitSpace := absInv ⁻¹' Ioo (3 / 2) (5 / 2)

theorem natOpenA_twoW₂ : twoBasic.NatOpenA twoW₂ :=
  CoveringBasicConstruction.natOpenA_mono absHatU_subset_twoHatU
    (natOpenA_abs_preimage isOpen_Ioo)

/-- `W₁ ∈ T_{|A|}`: at `|(1, 2)|` through the twisted member `twoCU` and `V = {1} × (3/2, 5/2)`,
elsewhere through the members `absCU β`. -/
theorem natOpenA_twoW₁ : twoBasic.NatOpenA twoW₁ := by
  intro z hz
  by_cases h2 : absInv z = 2
  · rw [eq_twoOrbit h2]
    refine ⟨twoPt, rfl, twoCU, Or.inr ⟨rfl, rfl⟩, ((1 : ℤˣ), ⟨twoPt, twoPt_mem⟩), ?_, twoV,
      isOpen_twoV, ⟨rfl, by norm_num, by norm_num⟩, ?_⟩
    · change absCatA.π (twistSignTwo twoPt * 1, twoPt) = _
      rw [twistSignTwo_twoPt, one_mul]
    · rintro _ ⟨d, ⟨h1, h3, h5⟩, rfl⟩
      change absInvPt (twistSignTwo (d.2 : posSlice.V).1 * d.1, (d.2 : posSlice.V).1) ∈
        Ioc (3 / 2 : ℝ) 2 ∪ Ioo (-(5 / 2)) (-2)
      simp only [absInvPt, h1, mul_one, twistSignTwo]
      split_ifs with h
      · right
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
        constructor <;> linarith
      · left
        simp only [Units.val_one, Int.cast_one, one_mul]
        exact ⟨h3, not_lt.1 h⟩
  · have hS : IsOpen (Ioo (3 / 2 : ℝ) 2 ∪ Ioo (-(5 / 2)) (-2)) := isOpen_Ioo.union isOpen_Ioo
    have hz0 : z ∈ absInv ⁻¹' (Ioo (3 / 2 : ℝ) 2 ∪ Ioo (-(5 / 2)) (-2)) := by
      rcases hz with ⟨h3, h4⟩ | h4
      · exact Or.inl ⟨h3, lt_of_le_of_ne h4 h2⟩
      · exact Or.inr h4
    obtain ⟨β, hβ, Ψh, hΨh, e, he, V, hV, heV, hsub⟩ := natOpenA_abs_preimage hS z hz0
    refine ⟨β, hβ, Ψh, absHatU_subset_twoHatU β hΨh, e, he, V, hV, heV, fun w hw => ?_⟩
    rcases hsub hw with ⟨h3, h4⟩ | h4
    · exact Or.inl ⟨h3, h4.le⟩
    · exact Or.inr h4

/-- Points of `W₁ ∩ W₂` have invariant in `(3/2, 2]`. -/
theorem absInv_mem_of_mem_inter {z : absCatA.OrbitSpace} (hz : z ∈ twoW₁ ∩ twoW₂) :
    absInv z ∈ Ioc (3 / 2 : ℝ) 2 := by
  rcases hz with ⟨h | h, h'⟩
  · exact h
  · exfalso
    have := h.2
    have := h'.1
    linarith

/-- A small step `t > 0` along a line through `p` staying in an open set. -/
theorem exists_pos_mem_line {U : Set (ℤˣ × (Fin 1 → ℝ))} (hU : IsOpen U) (i : ℤˣ)
    (x₀ c : ℝ) (h0 : (i, (fun _ => x₀ : Fin 1 → ℝ)) ∈ U) :
    ∃ t : ℝ, 0 < t ∧ (i, (fun _ => x₀ + c * t : Fin 1 → ℝ)) ∈ U := by
  have hc : Continuous fun t : ℝ => (i, (fun _ => x₀ + c * t : Fin 1 → ℝ)) :=
    continuous_const.prodMk (continuous_pi fun _ => continuous_const.add
      (continuous_const.mul continuous_id))
  have hO := hU.preimage hc
  have h0' : (0 : ℝ) ∈ (fun t : ℝ => (i, (fun _ => x₀ + c * t : Fin 1 → ℝ))) ⁻¹' U := by
    simp only [mem_preimage, mul_zero, add_zero]
    exact h0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO 0 h0'
  refine ⟨ε / 2, by linarith, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
  linarith

theorem fin_one_const_apply_zero (v : Fin 1 → ℝ) : (fun _ => v 0 : Fin 1 → ℝ) = v := by
  funext t
  rw [Fin.eq_zero t]

/-- **`W₁ ∩ W₂ ∉ T_{|A|}`**: at `|(1, 2)|` every member of `F̂` maps every open neighbourhood of a
lift onto points outside `W₁ ∩ W₂`: for `absCU β` the invariant `2 + t`, for `twoCU` the
invariant `−(2 + t)`. -/
theorem twoBasic_inter_not_natOpenA : ¬ twoBasic.NatOpenA (twoW₁ ∩ twoW₂) := by
  intro h
  have hz : twoOrbit ∈ twoW₁ ∩ twoW₂ := by
    refine ⟨?_, ?_⟩
    · change absInv twoOrbit ∈ Ioc (3 / 2 : ℝ) 2 ∪ Ioo (-(5 / 2)) (-2)
      rw [absInv_twoOrbit]
      exact Or.inl ⟨by norm_num, le_rfl⟩
    · change absInv twoOrbit ∈ Ioo (3 / 2 : ℝ) (5 / 2)
      rw [absInv_twoOrbit]
      exact ⟨by norm_num, by norm_num⟩
  obtain ⟨β, -, Ψh, hΨh, e, he, V, hV, heV, hsub⟩ := h _ hz
  rcases hΨh with hΨh | ⟨h0, hΨ⟩
  · obtain ⟨D, hβD, hfix, hD⟩ := absCU_eq β
    have hΨ' := hΨh.trans hD
    subst hΨ'
    -- `Ψ̂(i, v) = (i, v)` and `i v = 2`
    have he2 : ((e.1 : ℤ) : ℝ) * (e.2 : D.V).1 0 = 2 := by
      have := congrArg absInv he
      rwa [absInv_twoOrbit] at this
    have hU := isOpenMap_sliceHat D V hV
    obtain ⟨t, ht, ⟨d, hdV, hd⟩⟩ := exists_pos_mem_line hU e.1 ((e.2 : D.V).1 0)
      ((e.1 : ℤ) : ℝ) ⟨e, heV, by rw [fin_one_const_apply_zero]⟩
    have hmem := absInv_mem_of_mem_inter (hsub ⟨d, hdV, rfl⟩)
    change absInvPt (d.1, (d.2 : D.V).1) ∈ _ at hmem
    rw [show (d.1, (d.2 : D.V).1) = _ from hd] at hmem
    simp only [absInvPt] at hmem
    have : ((e.1 : ℤ) : ℝ) * ((e.2 : D.V).1 0 + ((e.1 : ℤ) : ℝ) * t) = 2 + t := by
      rw [mul_add, he2, ← mul_assoc, units_cast_mul_self, one_mul]
    rw [this] at hmem
    linarith [hmem.2]
  · subst h0
    have hΨ' : Ψh = twoCU := hΨ
    subst hΨ'
    have hpos : 0 < (e.2 : posSlice.V).1 0 := (e.2 : posSlice.V).2
    have he2 : (((twistSignTwo (e.2 : posSlice.V).1 * e.1 : ℤˣ) : ℤ) : ℝ) *
        (e.2 : posSlice.V).1 0 = 2 := by
      have := congrArg absInv he
      rwa [absInv_twoOrbit] at this
    -- so `e = (1, 2)`
    have hx : (e.2 : posSlice.V).1 0 = 2 ∧ e.1 = 1 := by
      by_cases hv : 2 < (e.2 : posSlice.V).1 0
      · exfalso
        have hs : twistSignTwo (e.2 : posSlice.V).1 = -1 := if_pos hv
        rw [hs] at he2
        rcases Int.units_eq_one_or e.1 with h1 | h1 <;> rw [h1] at he2
        · simp only [mul_one, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
            neg_one_mul] at he2
          linarith
        · simp only [mul_neg, mul_one, neg_neg, Units.val_one, Int.cast_one, one_mul] at he2
          linarith
      · have hs : twistSignTwo (e.2 : posSlice.V).1 = 1 := if_neg hv
        rw [hs, one_mul] at he2
        rcases Int.units_eq_one_or e.1 with h1 | h1 <;> rw [h1] at he2
        · simp only [Units.val_one, Int.cast_one, one_mul] at he2
          exact ⟨he2, h1⟩
        · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
            neg_one_mul] at he2
          linarith
    have hU := isOpenMap_sliceHat posSlice V hV
    obtain ⟨t, ht, ⟨d, hdV, hd⟩⟩ := exists_pos_mem_line hU e.1 ((e.2 : posSlice.V).1 0) 1
      ⟨e, heV, by rw [fin_one_const_apply_zero]⟩
    have hmem := absInv_mem_of_mem_inter (hsub ⟨d, hdV, rfl⟩)
    change absInvPt (twistSignTwo (d.2 : posSlice.V).1 * d.1, (d.2 : posSlice.V).1) ∈ _ at hmem
    have hd1 : d.1 = 1 := (congrArg Prod.fst hd).trans hx.2
    have hd2 : (d.2 : posSlice.V).1 0 = 2 + t := by
      have h' := congrFun (congrArg Prod.snd hd) 0
      simp only at h'
      rw [h', hx.1, one_mul]
    have hs : twistSignTwo (d.2 : posSlice.V).1 = -1 := by
      simp only [twistSignTwo, hd2]
      rw [if_pos (by linarith)]
    simp only [absInvPt, hs, hd1, hd2, mul_one, Units.val_neg, Units.val_one, Int.cast_neg,
      Int.cast_one] at hmem
    linarith [hmem.1]

/-- **2021 Lemma 19.7.17 (1), p. 916, needs the compatibility**: for the basic construction
`twoBasic` for the finite-to-one covering functor `P : ℤ/2 ⋉ (ℤˣ × ℝ) → ℤ/2 ⋉ ℝ` (Definition
19.7.11; `F̂(2) = {absCU 2, twoCU}` with `twoCU` twisted by `σ₂`, the other members those of
`absBasic`), the collection `T_{|A|}` of Definition 19.7.16 is not closed under intersections:
`W₁ ∩ W₂ ∉ T_{|A|}` for `W₁, W₂ ∈ T_{|A|}`.  Hence `T_{|A|}` is not a topology, and `twoBasic` is
not compatible. -/
theorem lemma_19_7_17_one_without_compatible :
    IsFiniteToOneCovering absCovP ∧ twoBasic.HasClassUniformizers ∧ ¬ twoBasic.IsCompatible ∧
      ∃ W₁ W₂ : Set absCatA.OrbitSpace, twoBasic.NatOpenA W₁ ∧ twoBasic.NatOpenA W₂ ∧
        ¬ twoBasic.NatOpenA (W₁ ∩ W₂) :=
  ⟨absCovP_isFiniteToOneCovering, twoBasic_hasClassUniformizers, fun hC =>
    twoBasic_inter_not_natOpenA (twoBasic.natOpenA_inter absCovP_isFiniteToOneCovering hC
      natOpenA_twoW₁ natOpenA_twoW₂),
    twoW₁, twoW₂, natOpenA_twoW₁, natOpenA_twoW₂, twoBasic_inter_not_natOpenA⟩

/-- No topology on `|A|` has the `T_{|A|}`-sets of `twoBasic` as its open sets. -/
theorem twoBasic_no_topology :
    ¬ ∃ T : TopologicalSpace absCatA.OrbitSpace, ∀ W, IsOpen[T] W ↔ twoBasic.NatOpenA W := by
  rintro ⟨T, hT⟩
  exact twoBasic_inter_not_natOpenA
    ((hT _).1 (((hT _).2 natOpenA_twoW₁).inter ((hT _).2 natOpenA_twoW₂)))

end TwistTwo


/-! ### Definition 19.8.4: "(1) implies (3)" -/

section Remark1984

theorem uniformizerConstruction_ext_F {C : GroupoidalCategory.{u}}
    {U U' : C.UniformizerConstruction} (h : U.F = U'.F) : U = U' := by
  cases U
  cases U'
  simp only at h
  subst h
  rfl

/-- `F` of `twistBasic` is `F` of `absBasic`: the twisted member has the same `Ψ` as `absCU 0`. -/
theorem twistHatU_toUniformizerConstruction :
    twistHatU.toUniformizerConstruction = absHatU.toUniformizerConstruction := by
  refine uniformizerConstruction_ext_F (funext fun α => Set.ext fun Ψ => ⟨?_, ?_⟩)
  · rintro ⟨Ψh, hΨh, rfl⟩
    rcases hΨh with rfl | ⟨h0, hΨ⟩
    · exact ⟨absCU α, mem_singleton _, rfl⟩
    · subst h0
      have hΨ' : Ψh = twistCU := hΨ
      subst hΨ'
      exact ⟨absCU 0, mem_singleton _, by rw [absCU_zero]; rfl⟩
  · rintro ⟨Ψh, hΨh, rfl⟩
    exact ⟨Ψh, Or.inl (mem_singleton_iff.1 hΨh), rfl⟩

/-- **`T_{|B|}` of `twistBasic` is `T_{|B|}` of `absBasic`**, the orbit-space topology of
`|B| ≅ [0, ∞)`; it is metrizable. -/
theorem twistBasic_natTop_eq :
    twistBasic.toBasic.natTop twistBasic_hasClassUniformizers.toBasic =
      absBasic.toBasic.natTop absBasic_hasClassUniformizers.toBasic := by
  refine TopologicalSpace.ext (funext fun W => propext ?_)
  change twistHatU.toUniformizerConstruction.NatOpen W ↔
    absHatU.toUniformizerConstruction.NatOpen W
  rw [twistHatU_toUniformizerConstruction]

theorem twistBasic_metrizable :
    @MetrizableSpace _ (twistBasic.toBasic.natTop twistBasic_hasClassUniformizers.toBasic) :=
  twistBasic_natTop_eq ▸ not_theorem_19_7_25_four_b.1

/-- **The twisted uniformizer for the bundle covering pull-back** (Definition 19.8.1):
`(Ψ, Ψ̂, Γ)` with `(Ψ, Ψ̂) = twistCU` and the strong bundle uniformizer `Γ` of `absPU 0`. -/
def twistPU : PullbackUniformizer absCovP reflBan 0 := ⟨twistCU, sliceBun overlapSlice₀⟩

/-- **`F̃` with the twisted member** (Definition 19.8.2): `F̃(β) = {absPU β}` for `β ≠ 0` and
`F̃(0) = {absPU 0, twistPU}`. -/
def twistFt : PullbackUniformizerConstruction absCovP reflBan :=
  ⟨fun β => {x | x = absPU β ∨ ∃ h : (0 : Fin 1 → ℝ) = β, x = h ▸ twistPU}⟩

/-- The induced `F̂` is `twistHatU`. -/
theorem twistFt_hatU : twistFt.hatU = twistHatU := by
  unfold PullbackUniformizerConstruction.hatU twistHatU
  congr 1
  funext β
  refine Set.ext fun Ψh => ⟨?_, ?_⟩
  · rintro ⟨x, hx | ⟨h0, hx⟩, rfl⟩
    · exact Or.inl (by rw [hx]; exact absPU_Ψh β)
    · subst h0
      have hx' : x = twistPU := hx
      subst hx'
      exact Or.inr ⟨rfl, rfl⟩
  · rintro (h | ⟨h0, h⟩)
    · exact ⟨absPU β, Or.inl rfl, (absPU_Ψh β).trans h.symm⟩
    · subst h0
      have h' : Ψh = twistCU := h
      subst h'
      exact ⟨twistPU, Or.inr ⟨rfl, rfl⟩, rfl⟩

theorem twistFt_slice (Ψ : twistFt.toUniformizerConstruction.Unif) :
    ∃ D : TranslationSlice ℤˣ (Fin 1 → ℝ), Ψ.1 = sliceUniformizer isScSmoothMap_units_smul D := by
  obtain ⟨Ψ₁, β, Ψh, hmem, hΨ⟩ := Ψ
  have hmem' : Ψh ∈ twistHatU.F β := twistFt_hatU ▸ hmem
  exact twistHatU_slice ⟨Ψ₁, β, Ψh, hmem', hΨ⟩

/-- **The keyed transition construction for `twistFt`**. -/
def twistFt𝓕 : twistFt.toUniformizerConstruction.TransitionConstruction :=
  ⟦sliceData isScSmoothMap_units_smul twistFt_slice⟧

/-- **`(F̂, 𝓕)` is `twistBasic`** (Definition 19.8.4 (3) as printed). -/
theorem twistFt_toCBC : twistFt.toCBC twistFt𝓕 = twistBasic :=
  toCBC_sliceData_eq _ _ twistFt_hatU _ _

/-- **2021 Definition 19.8.4, p. 934, the note "(1) implies (3)", as printed**: for every
uniformizer construction `F̃` for `(P, μ_B)` and every transition construction `𝓕` for the
underlying `F`, `(F̂, 𝓕)` is a basic construction for `P` in the sense of Definition 19.7.11
(with uniformizer construction `F̂` and underlying basic construction `(F, 𝓕)` for `B`), and the
part of (1) that `T_{|B|}` needs, `F(α) ≠ ∅` on every class, gives `F̂(β) ≠ ∅` on every class. -/
theorem definition_19_8_4_one_implies_three {A B : GroupoidalCategory.{u}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} {μ : B.BanFunctor}
    (Ft : PullbackUniformizerConstruction P μ)
    (𝓕 : Ft.toUniformizerConstruction.TransitionConstruction) :
    (Ft.toCBC 𝓕).hatU = Ft.hatU ∧ (Ft.toCBC 𝓕).toBasic = ⟨Ft.toUniformizerConstruction, 𝓕⟩ ∧
      (Ft.toUniformizerConstruction.HasClassUniformizers → (Ft.toCBC 𝓕).HasClassUniformizers) := by
  refine ⟨rfl, rfl, fun h z => ?_⟩
  obtain ⟨β, hβ, Ψ, Ψh, hΨh, -⟩ := h z
  exact ⟨β, hβ, Ψh, hΨh⟩

/-- **2021 Definition 19.8.4, p. 934: with compatibility read into Definition 19.7.11, (1) does not
give (3)**.  For the uniformizer construction `twistFt` for `(absCovP, reflBan)` (Definitions
19.8.1, 19.8.2; `F̃(0) = {absPU 0, twistPU}`), the keyed transition construction `𝓕` satisfies
Definition 19.8.4 (1) (class uniformizers and a metrizable `T_{|B|}`), `(F̂, 𝓕)` is the basic
construction `twistBasic` for `P` of Definition 19.7.11 as printed, and it is not compatible
(`IsCompatible`, the added hypothesis of l. 44572 used in Lemma 19.7.17, Corollary 19.7.20,
Theorem 19.8.6 (5) and §19.8's `T_{|E_A|}`).  So the note "(1) implies (3)" holds for Definition
19.7.11 as printed (`definition_19_8_4_one_implies_three`) and needs the compatibility as an
assumption when Definition 19.7.11 is read with it. -/
theorem definition_19_8_4_one_without_compatible :
    ∃ 𝓕 : twistFt.toUniformizerConstruction.TransitionConstruction,
      twistFt.toCBC 𝓕 = twistBasic ∧
      ∃ hB : (twistFt.toCBC 𝓕).HasClassUniformizers,
        @MetrizableSpace _ ((twistFt.toCBC 𝓕).toBasic.natTop hB.toBasic) ∧
          ¬ (twistFt.toCBC 𝓕).IsCompatible := by
  refine ⟨twistFt𝓕, twistFt_toCBC, ?_⟩
  rw [twistFt_toCBC]
  exact ⟨twistBasic_hasClassUniformizers, twistBasic_metrizable, not_isCompatible_twistBasic⟩


/-! #### Coherence (Definition 19.8.4 (2)) for `twistFt` -/

section CoherenceData

variable {C : GroupoidalCategory.{u}} {μ : C.BanFunctor} (Bc : C.BasicConstruction)
  (Ψ Ψ' : Bc.U.Unif) (b : StrongBundleOver μ Ψ.1) (b' : StrongBundleOver μ Ψ'.1)

/-- `s : M(Ψ, Ψ') → O`. -/
abbrev cohSrc (k : Bc.M Ψ Ψ') : Ψ.1.O := (k : Ψ.1.Trans Ψ'.1).src

/-- `t : M(Ψ, Ψ') → O'`. -/
abbrev cohTgt (k : Bc.M Ψ Ψ') : Ψ'.1.O := (k : Ψ.1.Trans Ψ'.1).tgt

instance instParacompactSpaceCohSrc : ParacompactSpace (pullbackSpace b.Q (cohSrc Bc Ψ Ψ')) :=
  paracompactSpace_pullbackSpace (Bc.transPolyfold Ψ Ψ') b.bundle

instance instParacompactSpaceCohTgt : ParacompactSpace (pullbackSpace b'.Q (cohTgt Bc Ψ Ψ')) :=
  paracompactSpace_pullbackSpace (Bc.transPolyfold Ψ Ψ') b'.bundle

/-- `M(Ψ, Ψ') ₛ×_Q W → M(Ψ, Ψ')` for a basic construction `Bc` and bundle data `b` over `Ψ`. -/
def cohSrcBundle :
    StrongBundle (Bc.transPolyfold Ψ Ψ') (pullbackProj b.Q (cohSrc Bc Ψ Ψ')) :=
  b.bundle.pullback (Bc.rep.isLocalScDiffeo_src Ψ Ψ').isScSmoothMap

/-- `M(Ψ, Ψ') ₜ×_{Q'} W' → M(Ψ, Ψ')`. -/
def cohTgtBundle :
    StrongBundle (Bc.transPolyfold Ψ Ψ') (pullbackProj b'.Q (cohTgt Bc Ψ Ψ')) :=
  b'.bundle.pullback (Bc.rep.isLocalScDiffeo_tgt Ψ Ψ').isScSmoothMap

/-- `C = H'⁻¹ ∘ H`. -/
def cohAltC (z : pullbackSpace b.Q (cohSrc Bc Ψ Ψ')) : pullbackSpace b'.Q (cohTgt Bc Ψ Ψ') :=
  ⟨(b.toStr.proj b'.toStr (b.toStr.lift b'.toStr (z : Bc.M Ψ Ψ' × b.W).1
      (z : Bc.M Ψ Ψ' × b.W).2 z.2),
    (b.toStr.lift b'.toStr (z : Bc.M Ψ Ψ' × b.W).1 (z : Bc.M Ψ Ψ' × b.W).2 z.2).tgt), rfl⟩

/-- **Coherence of one pair** (Definition 19.6.15), in terms of `Bc`, `Ψ`, `Ψ'` and the bundle
data only. -/
def CohPair : Prop :=
  ∃ h : (cohSrcBundle Bc Ψ Ψ' b).IsStrongBundleMap (cohTgtBundle Bc Ψ Ψ' b') id
      (cohAltC Bc Ψ Ψ' b b'),
    (cohSrcBundle Bc Ψ Ψ' b).IsStrongBundleIsoOn (cohTgtBundle Bc Ψ Ψ' b') h univ univ

end CoherenceData

theorem isCoherent_iff_cohPair {A B : GroupoidalCategory.{u}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} {μ : B.BanFunctor}
    (Ft : PullbackUniformizerConstruction P μ)
    (𝓕 : Ft.toUniformizerConstruction.TransitionConstruction) :
    Ft.IsCoherent 𝓕 ↔ ∀ x y : Ft.Unif,
      CohPair (Ft.toCBC 𝓕).toBasic x.toHat.toUnif y.toHat.toUnif x.x.bun y.x.bun :=
  Iff.rfl


/-- `CohPair` depends on the basic construction, the uniformizers `Ψ`, `Ψ'` and the bundle data
only. -/
theorem cohPair_congr {C : GroupoidalCategory.{u}} {μ : C.BanFunctor}
    {Bc₁ Bc₂ : C.BasicConstruction} (hBc : Bc₁ = Bc₂) {Ψ₁ Ψ₁' : Bc₁.U.Unif}
    {Ψ₂ Ψ₂' : Bc₂.U.Unif} (hΨ : Ψ₁.1 = Ψ₂.1) (hΨ' : Ψ₁'.1 = Ψ₂'.1)
    {b₁ : StrongBundleOver μ Ψ₁.1} {b₁' : StrongBundleOver μ Ψ₁'.1}
    {b₂ : StrongBundleOver μ Ψ₂.1} {b₂' : StrongBundleOver μ Ψ₂'.1}
    (hb : HEq b₁ b₂) (hb' : HEq b₁' b₂') (h : CohPair Bc₂ Ψ₂ Ψ₂' b₂ b₂') :
    CohPair Bc₁ Ψ₁ Ψ₁' b₁ b₁' := by
  subst hBc
  obtain ⟨v₁, p₁⟩ := Ψ₁
  obtain ⟨v₂, p₂⟩ := Ψ₂
  obtain ⟨v₁', p₁'⟩ := Ψ₁'
  obtain ⟨v₂', p₂'⟩ := Ψ₂'
  dsimp only at hΨ hΨ'
  subst hΨ hΨ'
  obtain rfl := eq_of_heq hb
  obtain rfl := eq_of_heq hb'
  exact h

/-- Every member of `twistFt` has the `Ψ` and the strong bundle uniformizer of `absPU β`. -/
theorem twistFt_member_data (X : twistFt.Unif) :
    X.x.Ψh.Ψ = (absPU X.β).Ψh.Ψ ∧ HEq X.x.bun (absPU X.β).bun := by
  obtain ⟨β, x, hx | ⟨h0, hx⟩⟩ := X
  · subst hx
    exact ⟨rfl, HEq.rfl⟩
  · subst h0
    have hx' : x = twistPU := hx
    subst hx'
    refine ⟨?_, ?_⟩
    · change twistCU.Ψ = (absPU 0).Ψh.Ψ
      rw [absPU_Ψh, absCU_zero]
      rfl
    · change HEq (sliceBun overlapSlice₀) (absPU 0).bun
      rw [absPU_zero]
      rfl

theorem basicConstruction_sliceData_eq (U₁ U₂ : absCatB.UniformizerConstruction) (h : U₁ = U₂)
    (h₁ : ∀ Ψ : U₁.Unif,
      ∃ D : TranslationSlice ℤˣ (Fin 1 → ℝ), Ψ.1 = sliceUniformizer isScSmoothMap_units_smul D)
    (h₂ : ∀ Ψ : U₂.Unif,
      ∃ D : TranslationSlice ℤˣ (Fin 1 → ℝ), Ψ.1 = sliceUniformizer isScSmoothMap_units_smul D) :
    (⟨U₁, ⟦sliceData isScSmoothMap_units_smul h₁⟧⟩ : absCatB.BasicConstruction) =
      ⟨U₂, ⟦sliceData isScSmoothMap_units_smul h₂⟧⟩ := by
  subst h
  rfl

/-- The basic constructions `(F, 𝓕)` for `B` of `twistFt` and `absFt` coincide. -/
theorem twistFt_toBasic_eq :
    (twistFt.toCBC twistFt𝓕).toBasic = (absFt.toCBC absFt𝓕).toBasic := by
  rw [twistFt_toCBC, absFt_toCBC]
  exact basicConstruction_sliceData_eq _ _ twistHatU_toUniformizerConstruction _ _

/-- **2021 Definition 19.8.4 (2) for `twistFt`**: coherence, transferred from `absFt`
(`absFt_isCoherent`), since coherence involves only `(F, 𝓕)` and the pairs `(Ψ, Γ)`, and
`twistPU` has the pair `(Ψ, Γ)` of `absPU 0`. -/
theorem twistFt_isCoherent : twistFt.IsCoherent twistFt𝓕 := by
  have H := (isCoherent_iff_cohPair absFt absFt𝓕).1 absFt_isCoherent
  refine (isCoherent_iff_cohPair twistFt twistFt𝓕).2 fun X Y => ?_
  exact cohPair_congr twistFt_toBasic_eq (twistFt_member_data X).1 (twistFt_member_data Y).1
    (twistFt_member_data X).2 (twistFt_member_data Y).2
    (H ⟨X.β, absPU X.β, mem_singleton _⟩ ⟨Y.β, absPU Y.β, mem_singleton _⟩)

theorem twistBasic_conditions (X : CoveringBasicConstruction absCovP) (hX : X = twistBasic) :
    ∃ hB : X.HasClassUniformizers,
      @MetrizableSpace _ (X.toBasic.natTop hB.toBasic) ∧ ¬ X.IsCompatible := by
  subst hX
  exact ⟨twistBasic_hasClassUniformizers, twistBasic_metrizable, not_isCompatible_twistBasic⟩

/-- **2021 Definition 19.8.4 for `twistFt`**: the keyed transition construction, with class
uniformizers, a metrizable `T_{|B|}` and coherence. -/
def twistFtTransition : twistFt.PullbackTransitionConstruction where
  𝓕 := twistFt𝓕
  hasClassUniformizers := twistFt_toCBC ▸ twistBasic_hasClassUniformizers
  metrizable := by
    obtain ⟨_, hm, -⟩ := twistBasic_conditions (twistFt.toCBC twistFt𝓕) twistFt_toCBC
    exact hm
  isCoherent := twistFt_isCoherent

/-- **2021 Definition 19.8.5 for `(absCovP, reflBan)` with the twisted member**. -/
def twistFtBasic : PullbackUniformizerConstruction.PullbackBasicConstruction absCovP reflBan :=
  ⟨twistFt, twistFtTransition⟩

/-- **2021 Definition 19.8.4, p. 934, as printed, does not give the compatibility**: `twistFt` has
a transition construction in the sense of Definition 19.8.4 ((1) class uniformizers and a
metrizable `T_{|B|}`, (2) coherence, (3) `(F̂, 𝓕)` a basic construction for `P` as in Definition
19.7.11 as printed), and its basic construction `(F̂, 𝓕) = twistBasic` for `P` is not compatible.
So the hypothesis `IsCompatible` of the §19.8 results (Theorem 19.8.6 (5), Lemma 19.8.21,
Theorem 19.8.22) is not a consequence of Definitions 19.8.4 and 19.8.5. -/
theorem definition_19_8_4_without_compatible :
    twistFtTransition.toCoveringBasicConstruction = twistBasic ∧
      ¬ twistFtTransition.toCoveringBasicConstruction.IsCompatible :=
  ⟨twistFt_toCBC, by
    have h := not_isCompatible_twistBasic
    rw [← twistFt_toCBC] at h
    exact h⟩

end Remark1984

end GroupoidalCategory

end Polyfold
