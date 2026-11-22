import Polyfold.Chapter19.CoveringPullbackTheorem
import Polyfold.Chapter19.CoveringSquare
import Polyfold.Chapter19.StrongBundleExamples
import Polyfold.Chapter19.CoveringCounterexamples

/-!
# The reflection bundle pulled back along `absBasic` (HWZ 2021 §19.8, pp. 930–941)

Non-degenerate witnesses for 2021 Definitions 19.8.1, 19.8.2, 19.8.7, the transition
construction of Definition 19.8.4 without coherence, and Theorem 19.8.6 (the functor `Γ̂` and
(1)–(4)), pp. 930–941.

`μ_B` is the reflection bundle `reflBan` over `B = ℤ/2 ⋉ ℝ` (`μ(x) = {x} × ℝ`,
`μ(g, x)(x, v) = (g x, g v)`) and `P = absCovP : ℤ/2 ⋉ (ℤˣ × ℝ) → ℤ/2 ⋉ ℝ`, `(i, x) ↦ x`, the
finite-to-one covering functor of `absBasic`.  Over a slice `H ⋉ V` of `B` the strong bundle
uniformizer is the trivial bundle `W_V = V ×_ℝ (ℝ × ℝ) → V` (the pull-back of
`TrivialBundle.bundle 1 1` along `V ⊆ ℝ`) with `h ∗ (v, a) = (h v, h a)` and `Γ(v, a) = a`.

## What is formalized

* `SliceW`, `sliceBun` (a `StrongBundleOver reflBan` the slice uniformizer `absSliceUnif D`),
  `slicePU` (a member of Definition 19.8.1 over `sliceCU`), `absPU` (over `absCU β`),
  `absPU_Ψh`, `absFt` (**Definition 19.8.2**, `F̃(β) = {absPU β}`), `absFt_hatU` (`F̂ = absHatU`).
* `sliceBun_smul_neg`: on `V = ℝ` the element `-1` of `H = ℤ/2` acts on the fibre by `-1`
  (the fibre action is non-trivial).
* `exists_absFt_transition`: a transition construction `𝓕` for `F` with
  `(F̂, 𝓕) = absBasic`, so it has class uniformizers, a metrizable `T_{|B|}` (Definition 19.8.4
  (1)) and is compatible (`IsCompatible`), and
  `absFt_theorem_19_8_6`: the conclusions of `theorem_19_8_6_one_four` for it.
* `reflAbsSquare` (**Definition 19.8.7** for `(absCovP, reflBan)`), `reflAbsSquare_μA` and
  `reflAbsSquare_act_neg` (`μ_A = μ_B ∘ P` maps the fibre over `(1, 0)` to the one over
  `(-1, 0)` by `-1`).

The coherence (2) of Definition 19.8.4 for `absFt` is not part of this file.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples GCT.PolyfoldConstruction TrivialBundle Chapter19

/-! ### The trivial bundle over a slice -/

/-- **The total space `W_V = {(v, a) ∈ V × (ℝ × ℝ) | a₁ = v}`** over a slice `V`: the pull-back
of `ℝ × ℝ → ℝ` along `Ψ : V → ℝ`. -/
abbrev SliceW (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) : Type :=
  pullbackSpace (proj 1 1) (absSliceUnif D).obj

instance SliceW.paracompactSpace (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) :
    ParacompactSpace (SliceW D) :=
  paracompactSpace_pullbackSpace (absSliceUnif D).P (bundle 1 1)

/-- The group element `h ∈ H ⊆ ℤˣ`. -/
abbrev sliceElt {D : TranslationSlice ℤˣ (Fin 1 → ℝ)} (h : (absSliceUnif D).G) : ℤˣ :=
  (h : D.H).1

/-- `h ∗ (v, a) = (h v, h a)`. -/
def SliceW.smul {D : TranslationSlice ℤˣ (Fin 1 → ℝ)} (h : (absSliceUnif D).G) (w : SliceW D) :
    SliceW D :=
  ⟨(h • w.1.1, sliceElt h • w.1.2), (congrArg (fun x => sliceElt h • x) w.2 : _)⟩

instance SliceW.instMulAction (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) :
    MulAction (absSliceUnif D).G (SliceW D) where
  smul := SliceW.smul
  one_smul _ := Subtype.ext (Prod.ext (one_smul _ _) (one_smul ℤˣ _))
  mul_smul h h' _ := Subtype.ext (Prod.ext (mul_smul _ _ _) (mul_smul (sliceElt h) (sliceElt h') _))

theorem SliceW.smul_val {D : TranslationSlice ℤˣ (Fin 1 → ℝ)} (h : (absSliceUnif D).G)
    (w : SliceW D) :
    ((h • w : SliceW D) : (absSliceUnif D).O × ((Fin 1 → ℝ) × (Fin 1 → ℝ))) =
      (h • w.1.1, sliceElt h • w.1.2) := rfl

theorem isScSmoothMap_sliceObj (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) :
    (absSliceUnif D).P.IsScSmoothMap (rnPolyfold 1) (absSliceUnif D).obj :=
  MPolyfold.isScSmoothMap_subtypeVal D.isOpen

/-- The strong bundle `W_V → V`, the pull-back of `ℝ × ℝ → ℝ` along `V ⊆ ℝ`. -/
abbrev sliceBundle (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) :
    StrongBundle (absSliceUnif D).P (pullbackProj (proj 1 1) (absSliceUnif D).obj) :=
  (bundle 1 1).pullback (isScSmoothMap_sliceObj D)

theorem isStrongBundleMap_sliceW_smul (D : TranslationSlice ℤˣ (Fin 1 → ℝ))
    (g : (absSliceUnif D).G) :
    (sliceBundle D).IsStrongBundleMap (sliceBundle D) (fun y => g • y)
      (fun w : SliceW D => g • w) := by
  have hf := isScSmoothMap_sliceObj D
  have h1 := (bundle 1 1).isStrongBundleMap_pullbackProj' hf
  have h2 := (reflHmap (sliceElt g)).comp h1
  exact (bundle 1 1).isStrongBundleMap_pullbackPair hf ((absSliceUnif D).smooth_smul g) h2

/-- **The functor `Γ : H ⋉ W_V → E_μ`**, `(v, a) ↦ a`, `(h, (v, a)) ↦ ((h, a₁), a)`. -/
def sliceBunFunctor (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) :
    GroupoidFunctor (GroupoidStr.translation (absSliceUnif D).G (SliceW D))
      reflBan.cat.toGroupoidStr where
  obj w := w.1.2
  mor q := ⟨((sliceElt q.1, q.2.1.2.1), q.2.1.2), rfl⟩
  src_mor _ := rfl
  tgt_mor q := reflBan_act_mk (sliceElt q.1) q.2.1.2
  mor_comp φ ψ h := by
    have hc : ((⟨((sliceElt φ.1, φ.2.1.2.1), φ.2.1.2), rfl⟩ : reflBan.cat.Mor) :
        ReflCat.Mor × reflBan.E).2 = reflBan.act ⟨((sliceElt ψ.1, ψ.2.1.2.1), ψ.2.1.2), rfl⟩ :=
      (congrArg (fun w : SliceW D => w.1.2) h).trans (reflBan_act_mk (sliceElt ψ.1) ψ.2.1.2).symm
    exact Subtype.ext (BanFunctor.morComp_val hc).symm
  mor_unit _ := rfl

/-- **The strong bundle uniformizer over a slice**: `W_V → V` with `Γ(v, a) = a`. -/
def sliceBun (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) :
    StrongBundleOver reflBan (absSliceUnif D) where
  W := SliceW D
  Q := pullbackProj (proj 1 1) (absSliceUnif D).obj
  bundle := sliceBundle D
  Q_smul _ _ := rfl
  isStrongBundleMap_smul := isStrongBundleMap_sliceW_smul D
  functor := sliceBunFunctor D
  injective_obj w w' h := Subtype.ext (Prod.ext
    (Subtype.ext (w.2.symm.trans ((congrArg (proj 1 1) h).trans w'.2))) h)
  full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => by
    obtain ⟨⟨⟨g, y⟩, e⟩, hψ⟩ := ψ
    have he : e = x.1.2 := hs
    subst he
    have hy : x.1.2.1 = y := hψ
    subst hy
    have ht' : g • x.1.2 = x'.1.2 := (reflBan_act_mk g x.1.2).symm.trans ht
    have a : x.1.2.1 = (x.1.1 : D.V).1 := x.2
    have b : x'.1.2.1 = (x'.1.1 : D.V).1 := x'.2
    have hv : g • (x.1.1 : D.V).1 = (x'.1.1 : D.V).1 := by
      rw [← a, ← b, ← ht']
      rfl
    have hk : g ∈ D.H := D.mem_of_smul_mem g _ (x.1.1 : D.V).2 (hv ▸ (x'.1.1 : D.V).2)
    exact ⟨((⟨g, hk⟩ : D.H), x), rfl,
      Subtype.ext (Prod.ext (Subtype.ext (p := (· ∈ D.V)) hv) ht'), rfl⟩
  faithful := (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ he =>
    Prod.ext (Subtype.ext (p := (· ∈ D.H)) (congrArg
      (fun q : reflBan.cat.Mor => (q : ReflCat.Mor × reflBan.E).1.1) he)) hs
  P_obj w := w.2
  mor_fst _ w := Prod.ext rfl w.2
  fiberCLE o := pullbackFiberCLE o
  fiberCLE_apply _ _ := rfl

/-- **The fibre action is non-trivial**: on `V = ℝ`, `-1 ∈ ℤ/2` maps `(0, (0, v))` to
`(0, (0, -v))`. -/
theorem sliceBun_smul_neg (v : Fin 1 → ℝ) :
    (sliceBun overlapSlice₀).functor.obj
        ((show (absSliceUnif overlapSlice₀).G from ⟨-1, Subgroup.mem_top _⟩) •
          (show SliceW overlapSlice₀ from ⟨(⟨0, mem_univ _⟩, (0, v)), rfl⟩)) =
      (0, -v) := by
  change ((-1 : ℤˣ) • ((0 : Fin 1 → ℝ), v)) = (0, -v)
  rw [Prod.smul_mk, units_smul_rn_neg_one, units_smul_rn_neg_one, neg_zero]

/-! ### Definitions 19.8.1 and 19.8.2 -/

/-- **2021 Definition 19.8.1, p. 930, over a slice**: the proper covering uniformizer
`sliceCU D β` with the strong bundle uniformizer `sliceBun D`. -/
def slicePU (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) (β : Fin 1 → ℝ) (hβ : β ∈ D.V)
    (hfix : ∀ h ∈ D.H, h • β = β) : PullbackUniformizer absCovP reflBan β :=
  ⟨sliceCU D β hβ hfix, sliceBun D⟩

open Classical in
/-- **The member of `F̃(β)`** (Definition 19.8.1): over `absCU β`. -/
def absPU (β : Fin 1 → ℝ) : PullbackUniformizer absCovP reflBan β :=
  if h0 : β = 0 then h0 ▸ slicePU overlapSlice₀ 0 (mem_univ _) zero_fix
  else if hp : 0 < β 0 then slicePU posSlice β hp (bot_fix _ rfl β)
  else slicePU negSlice β (lt_of_le_of_ne (not_lt.1 hp) fun h => h0 (fin_one_ext h))
    (bot_fix _ rfl β)

theorem absPU_Ψh (β : Fin 1 → ℝ) : (absPU β).Ψh = absCU β := by
  unfold absPU absCU
  split_ifs with h0 hp
  · subst h0
    rfl
  · rfl
  · rfl

/-- **2021 Definition 19.8.2, p. 932**: the uniformizer construction `F̃(β) = {absPU β}` for
`(absCovP, reflBan)`. -/
def absFt : PullbackUniformizerConstruction absCovP reflBan := ⟨fun β => {absPU β}⟩

/-- The induced `F̂` is `absHatU`. -/
theorem absFt_hatU : absFt.hatU = absHatU := by
  unfold PullbackUniformizerConstruction.hatU absHatU absFt
  congr 1
  funext β
  rw [image_singleton, absPU_Ψh]

theorem nonempty_absFt_unif : Nonempty absFt.Unif := ⟨⟨0, absPU 0, mem_singleton _⟩⟩

theorem exists_transition_of_eq (U : CoveringUniformizerConstruction absCovP)
    (hU : U = absHatU) :
    ∃ 𝓕 : U.toUniformizerConstruction.TransitionConstruction,
      (⟨U, 𝓕⟩ : CoveringBasicConstruction absCovP) = absBasic := by
  subst hU
  exact ⟨absBasic.𝓕, rfl⟩

instance fact_absCovP_isFiniteToOneCovering : Fact (IsFiniteToOneCovering absCovP) :=
  ⟨absCovP_isFiniteToOneCovering⟩

theorem absBasic_conditions (X : CoveringBasicConstruction absCovP) (hX : X = absBasic) :
    ∃ hB : X.HasClassUniformizers,
      @MetrizableSpace _ (X.toBasic.natTop hB.toBasic) ∧ X.IsCompatible := by
  subst hX
  exact ⟨absBasic_hasClassUniformizers, not_theorem_19_7_25_four_b.1, absBasic_isCompatible⟩

/-- **A transition construction for `absFt`** (Definition 19.8.4 (1) and (3)): `(F̂, 𝓕)` is
`absBasic`, so it has class uniformizers, a metrizable `T_{|B|}`, and is compatible. -/
theorem exists_absFt_transition :
    ∃ 𝓕 : absFt.toUniformizerConstruction.TransitionConstruction,
      absFt.toCBC 𝓕 = absBasic ∧ ∃ hB : (absFt.toCBC 𝓕).HasClassUniformizers,
        @MetrizableSpace _ ((absFt.toCBC 𝓕).toBasic.natTop hB.toBasic) ∧
          (absFt.toCBC 𝓕).IsCompatible := by
  obtain ⟨𝓕, h⟩ := exists_transition_of_eq absFt.hatU absFt_hatU
  exact ⟨𝓕, h, absBasic_conditions _ h⟩

/-- **2021 Theorem 19.8.6, the functor `Γ̂` and (1)–(4), for `absFt`**: a sample of the
conclusions of `theorem_19_8_6_one_four` for the transition construction of
`exists_absFt_transition`. -/
theorem absFt_theorem_19_8_6 :
    ∃ 𝓕 : absFt.toUniformizerConstruction.TransitionConstruction,
      absFt.toCBC 𝓕 = absBasic ∧ ∀ x y : absFt.Unif,
        Injective x.x.gammaHat.obj ∧ Surjective (absFt.pBmap 𝓕 x y) ∧
          Bijective (absFt.Umap 𝓕 x y) ∧ Surjective (absFt.pbarMap 𝓕 x y) := by
  obtain ⟨𝓕, h, -⟩ := exists_absFt_transition
  refine ⟨𝓕, h, fun x y => ?_⟩
  obtain ⟨h0, -, h2, h3, h4⟩ := absFt.theorem_19_8_6_one_four 𝓕 x y
  exact ⟨h0.1, h2.2, h3.1, h4.2.1⟩

/-! ### Definition 19.8.7 -/

/-- **2021 Definition 19.8.7, p. 941, for `(absCovP, reflBan)`**: the bundle covering square of
the pull-back `μ_A = μ_B ∘ P`. -/
def reflAbsSquare : BundleCoveringSquare absCatA absCatB :=
  BundleCoveringSquare.ofPull absCovP absCovP_isFiniteToOneCovering reflBan

theorem reflAbsSquare_μA : reflAbsSquare.μA = reflBan.pull absCovP := rfl

/-- **`μ_A` acts non-trivially**: `μ_A(-1, (1, 0))((1, 0), (0, v)) = ((-1, 0), (0, -v))`. -/
theorem reflAbsSquare_act_neg (v : Fin 1 → ℝ) :
    BanFunctor.pullPt ((reflBan.pull absCovP).act
        ⟨(((-1 : ℤˣ), ((1 : ℤˣ), 0)),
          BanFunctor.pullMk (μ := reflBan) (P := absCovP) ((1 : ℤˣ), 0) (0, v) rfl), rfl⟩) =
      (((-1 : ℤˣ), 0), (0, -v)) := by
  refine (BanFunctor.pull_act (μ := reflBan) (P := absCovP) _).trans ?_
  change (((-1 : ℤˣ) * 1, (-1 : ℤˣ) • (0 : Fin 1 → ℝ)),
    reflBan.act ⟨(((-1 : ℤˣ), (0 : Fin 1 → ℝ)), ((0 : Fin 1 → ℝ), v)), rfl⟩) = _
  rw [reflBan_act]
  change (((-1 : ℤˣ) * 1, (-1 : ℤˣ) • (0 : Fin 1 → ℝ)), (-1 : ℤˣ) • ((0 : Fin 1 → ℝ), v)) = _
  rw [Prod.smul_mk, units_smul_rn_neg_one, units_smul_rn_neg_one, neg_zero, mul_one]

end GroupoidalCategory

end Polyfold
