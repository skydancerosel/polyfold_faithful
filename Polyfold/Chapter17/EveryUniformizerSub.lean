import Polyfold.Chapter17.EveryUniformizerGauge

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
**Proposition 17.3.6, 2021 p. 786**: `M(Ψ_A, Ψ'_A) = s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')` for every pair of
uniformizers.

# The identification `M(Ψ_A, Ψ'_A) = s⁻¹(A_Ψ)` for every pair

## The text, paraphrased

A subpolyfold `A` inherits the polyfold structure `(F_A, M)`: `F_A(α) = {Ψ_A | Ψ ∈ F(α)}`, and
`M(Ψ_A, Ψ'_A)` is `s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')` with its structure as a sub-M-polyfold (Lemma 17.3.5),
through `(o, φ, o') ↦ (o, φ, o')`.

## What is formalized

The project's `subConstruction` defines `M(L, L')` through one chosen `Ψ` with `Ψ_A = L`
(`subData`), and `proposition_17_3_6` gives the identification for that choice.  Here: the
identification cannot hold for every pair `Ψ, Ψ'` with a single structure on `A`.

* `gaugeSub c`: the polyfold structure `gaugeConstruction` on `ℤ/3 ⋉ ℝ` (trivial action) with
  `D = A = (0, ∞)`, so that `Ψ_false` and `Ψ_true` differ off `A` and have the same restriction
  (`restrict_false_eq_true`); `A` is a subpolyfold (`isSubpolyfold_gaugeSub`).
* `continuous_of_isHomeomorph_restrictTransEquiv`: if for some polyfold structure `S_A` on `A`
  the identifications of `M_{S_A}(Ψ_A, Ψ_A)` with `s⁻¹(A) ⊆ M(Ψ_false, Ψ_false)` and of
  `M_{S_A}(Ψ_A, Ψ'_A)` with `s⁻¹(A) ⊆ M(Ψ_false, Ψ_true)` are homeomorphisms, the gauge `c` is
  continuous on `A`.
* **`proposition_17_3_6_not_every_pair`**: with `c = 1` on `(0, 1]` and `c = g` on `(1, ∞)`, no
  polyfold structure on `A` makes both identifications homeomorphisms.

## Readings

* The text identifies `M(Ψ_A, Ψ'_A)` with `s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')`, which presupposes that this
  sub-M-polyfold depends only on `Ψ_A, Ψ'_A`.  As we read Definition 17.1.8, two uniformizers that
  agree on `A_Ψ` may carry transition structures that differ over `A`; the statement holds for one
  representative per restriction (`proposition_17_3_6`), not for every pair.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold.GCT.PolyfoldConstruction.EveryUniformizer

/-- `A = (0, ∞) ⊆ ℝ`. -/
def posSet : Set (Fin 1 → ℝ) := {x | 0 < x 0}

theorem isOpen_posSet : IsOpen posSet := isOpen_lt continuous_const (continuous_apply 0)

open scoped Classical in
/-- The gauge `1` on `(-∞, 1]`, `g` on `(1, ∞)`. -/
def stepGauge (x : Fin 1 → ℝ) : Z3 := if x 0 ≤ 1 then 1 else gen

/-- The gauge structure on `ℤ/3 ⋉ ℝ` with `D = A = (0, ∞)`. -/
abbrev gaugeSub (c : (Fin 1 → ℝ) → Z3) : (C (rnPolyfold 1)).PolyfoldConstruction :=
  gaugeConstruction (rnPolyfold 1) posSet c

variable (c : (Fin 1 → ℝ) → Z3)

theorem isSaturated_posSet : (C (rnPolyfold 1)).toGroupoidStr.IsSaturated posSet :=
  (C (rnPolyfold 1)).toGroupoidStr.isSaturated_iff.2 fun _ h => h

theorem isSubMPolyfold_posSet : (rnPolyfold 1).IsSubMPolyfold posSet :=
  fun _ ha => ⟨posSet, isOpen_posSet, ha, id, mapsTo_id _,
    MPolyfold.isScSmoothMap_id.mono isOpen_posSet (subset_univ _), fun _ _ => rfl,
    by rw [image_id, inter_self]⟩

/-- `A = (0, ∞)` is a subpolyfold (Definition 17.3.1). -/
theorem isSubpolyfold_gaugeSub : (gaugeSub c).IsSubpolyfold posSet := by
  refine ⟨isSaturated_posSet, ?_⟩
  rintro α - L ⟨b, rfl⟩
  exact isSubMPolyfold_posSet

/-- The restrictions agree: `Ψ_false` and `Ψ_true` coincide on `A`. -/
theorem restrict_false_eq_true (x : Fin 1 → ℝ) :
    LocalUniformizer.restrict isSaturated_posSet
        (Ψ := (unifAt (rnPolyfold 1) posSet c false x).1) isSubMPolyfold_posSet =
      LocalUniformizer.restrict isSaturated_posSet
        (Ψ := (unifAt (rnPolyfold 1) posSet c true x).1) isSubMPolyfold_posSet := by
  have hF : (unifAt (rnPolyfold 1) posSet c false x).1.restrictFunctor isSaturated_posSet =
      (unifAt (rnPolyfold 1) posSet c true x).1.restrictFunctor isSaturated_posSet := by
    refine GroupoidFunctor.ext rfl (funext fun p => Subtype.ext ?_)
    change (tw posSet false p.2.1 p.1, p.2.1) = (tw posSet true p.2.1 p.1, p.2.1)
    rw [tw_of_mem posSet true (show p.2.1 ∈ posSet from p.2.2), tw_false]
  unfold LocalUniformizer.restrict
  congr 1
  congr 1

/-- **The key step**: if, for a polyfold structure `S_A` on `A`, the identifications
`M_{S_A}(Ψ_A, Ψ_A) → s⁻¹(A) ⊆ M(Ψ_false, Ψ_false)` and
`M_{S_A}(Ψ_A, Ψ'_A) → s⁻¹(A) ⊆ M(Ψ_false, Ψ_true)` are homeomorphisms, then `c` is continuous
on `A`. -/
theorem continuous_of_isHomeomorph_restrictTransEquiv (x : Fin 1 → ℝ)
    (SA : ((C (rnPolyfold 1)).sub posSet).PolyfoldConstruction)
    (h : ∃ α, LocalUniformizer.restrict isSaturated_posSet
      (Ψ := (unifAt (rnPolyfold 1) posSet c false x).1) isSubMPolyfold_posSet ∈ SA.F α)
    (h' : ∃ α, LocalUniformizer.restrict isSaturated_posSet
      (Ψ := (unifAt (rnPolyfold 1) posSet c true x).1) isSubMPolyfold_posSet ∈ SA.F α)
    (H₀ : @IsHomeomorph _ _ (SA.topM ⟨_, h⟩ ⟨_, h⟩) _
      ((gaugeSub c).restrictTransEquiv isSaturated_posSet (unifAt (rnPolyfold 1) posSet c false x)
        (unifAt (rnPolyfold 1) posSet c false x) isSubMPolyfold_posSet isSubMPolyfold_posSet))
    (H₁ : @IsHomeomorph _ _ (SA.topM ⟨_, h⟩ ⟨_, h'⟩) _
      ((gaugeSub c).restrictTransEquiv isSaturated_posSet (unifAt (rnPolyfold 1) posSet c false x)
        (unifAt (rnPolyfold 1) posSet c true x) isSubMPolyfold_posSet isSubMPolyfold_posSet)) :
    Continuous fun q : posSet => (c q.1)⁻¹ := by
  obtain ⟨f, hf, hfm⟩ := exists_continuous_cast SA _ _ _ h h h' (restrict_false_eq_true c x)
  let S := gaugeSub c
  let Ψ₀ := unifAt (rnPolyfold 1) posSet c false x
  let Ψ₁ := unifAt (rnPolyfold 1) posSet c true x
  -- the unit map on `A`
  let u : posSet → S.restrictTransSet (A := posSet) Ψ₀ Ψ₀ :=
    fun q => ⟨S.toTr (GroupoidStr.TransitionSet.unit q.1), q.2⟩
  have hu : Continuous u :=
    (continuousOn_univ.1 (S.isScSmoothMap_trUnit Ψ₀).continuousOn).comp
      continuous_subtype_val |>.subtype_mk _
  let _ := SA.topM ⟨_, h⟩ ⟨_, h⟩
  let _ := SA.topM ⟨_, h⟩ ⟨_, h'⟩
  let e₀ := H₀.homeomorph _
  have hρ : @Continuous (S.Tr Ψ₀ Ψ₁) (Z3 × (Fin 1 → ℝ)) _ _
      (gRho (rnPolyfold 1) posSet c (unif (rnPolyfold 1) posSet false)
        (unif (rnPolyfold 1) posSet true)) :=
    continuous_gRho _ _ c _ _
  have hcomp : Continuous fun q : posSet =>
      (gRho (rnPolyfold 1) posSet c (unif (rnPolyfold 1) posSet false)
        (unif (rnPolyfold 1) posSet true)
        (S.restrictTransEquiv isSaturated_posSet Ψ₀ Ψ₁ isSubMPolyfold_posSet
          isSubMPolyfold_posSet (f (e₀.symm (u q)))).1).1 :=
    continuous_fst.comp (hρ.comp (continuous_subtype_val.comp (H₁.continuous.comp
      (hf.comp (e₀.symm.continuous.comp hu)))))
  refine hcomp.congr fun q => ?_
  have hmor : (S.restrictTransEquiv isSaturated_posSet Ψ₀ Ψ₁ isSubMPolyfold_posSet
      isSubMPolyfold_posSet (f (e₀.symm (u q)))).1.mor = (1, q.1) := by
    have h2 : S.restrictTransEquiv isSaturated_posSet Ψ₀ Ψ₀ isSubMPolyfold_posSet
        isSubMPolyfold_posSet (e₀.symm (u q)) = u q := e₀.apply_symm_apply _
    calc (f (e₀.symm (u q))).mor.1 = (e₀.symm (u q)).mor.1 := by rw [hfm]
      _ = (S.restrictTransEquiv isSaturated_posSet Ψ₀ Ψ₀ isSubMPolyfold_posSet
            isSubMPolyfold_posSet (e₀.symm (u q))).1.mor := rfl
      _ = (u q).1.mor := by rw [h2]
      _ = (1, q.1) := rfl
  refine (congrArg Prod.fst (gRho_false_true _ posSet c (x₁ := 0) (lt_irrefl (0 : ℝ)) _)).trans ?_
  change (S.restrictTransEquiv isSaturated_posSet Ψ₀ Ψ₁ isSubMPolyfold_posSet
      isSubMPolyfold_posSet (f (e₀.symm (u q)))).1.mor.1 *
    (c (S.restrictTransEquiv isSaturated_posSet Ψ₀ Ψ₁ isSubMPolyfold_posSet
      isSubMPolyfold_posSet (f (e₀.symm (u q)))).1.mor.2)⁻¹ = _
  rw [hmor, one_mul]

/-- `stepGauge` is not continuous on `A = (0, ∞)`. -/
theorem not_continuous_stepGauge : ¬ Continuous fun q : posSet => (stepGauge q.1)⁻¹ := by
  intro hcont
  let ι : Ioi (0 : ℝ) → posSet := fun t => ⟨fun _ => t.1, t.2⟩
  have hι : Continuous ι :=
    (continuous_pi fun _ => continuous_subtype_val).subtype_mk _
  have hF : ContinuousOn (fun t : ℝ => (stepGauge fun _ => t)⁻¹) (Ioi 0) :=
    continuousOn_iff_continuous_domRestrict.2 (hcont.comp hι)
  have := isPreconnected_Ioi.constant hF (x := 1 / 2) (y := 2) (by norm_num) (by norm_num)
  simp only [stepGauge] at this
  rw [if_pos (by norm_num), if_neg (by norm_num)] at this
  exact gen_inv_ne_one (by rw [← this]; rfl)

end Polyfold.GCT.PolyfoldConstruction.EveryUniformizer

namespace Polyfold.GCT.PolyfoldConstruction

open EveryUniformizer

/-- **Proposition 17.3.6, 2021 p. 786, for every pair of uniformizers, does not hold as we read
it**: there are a GCT `C` with a polyfold structure `S` (`F(α) ≠ ∅` for every `α`), a
subpolyfold `A`, and uniformizers `Ψ ≠ Ψ'` in `F(α)` for an `α ∈ A`, with the same restriction `Ψ_A = Ψ'_A`, such that
for no polyfold structure `S_A` on `A` with `Ψ_A ∈ F_{S_A}` both identifications
`M_{S_A}(Ψ_A, Ψ_A) → s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ)` and `M_{S_A}(Ψ_A, Ψ'_A) → s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')` are
homeomorphisms.  (`C = ℤ/3 ⋉ ℝ`, trivial action, `A = (0, ∞)`; `Ψ, Ψ'` differ off `A`; the
transition structures are `gaugeConstruction` with `stepGauge`.)  For the representative chosen
by `subData` the identification holds (`proposition_17_3_6`). -/
theorem proposition_17_3_6_not_every_pair :
    ∃ (C : GCT.{0}) (S : C.PolyfoldConstruction) (A : Set C.Obj)
      (hA : C.toGroupoidStr.IsSaturated A) (Ψ Ψ' : S.Unif)
      (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A)),
      S.HasUniformizers ∧ S.IsSubpolyfold A ∧ (∃ α ∈ A, Ψ.1 ∈ S.F α ∧ Ψ'.1 ∈ S.F α) ∧ Ψ ≠ Ψ' ∧
      LocalUniformizer.restrict hA p = LocalUniformizer.restrict hA p' ∧
      ∀ (SA : (C.sub A).PolyfoldConstruction)
        (h : ∃ α, LocalUniformizer.restrict hA p ∈ SA.F α)
        (h' : ∃ α, LocalUniformizer.restrict hA p' ∈ SA.F α),
        ¬ (@IsHomeomorph _ _ (SA.topM ⟨_, h⟩ ⟨_, h⟩) _ (S.restrictTransEquiv hA Ψ Ψ p p) ∧
          @IsHomeomorph _ _ (SA.topM ⟨_, h⟩ ⟨_, h'⟩) _ (S.restrictTransEquiv hA Ψ Ψ' p p')) := by
  refine ⟨_, gaugeSub stepGauge, posSet, isSaturated_posSet,
    unifAt (rnPolyfold 1) posSet stepGauge false 0, unifAt (rnPolyfold 1) posSet stepGauge true 0,
    isSubMPolyfold_posSet, isSubMPolyfold_posSet, gaugeConstruction_hasUniformizers _ _ _,
    isSubpolyfold_gaugeSub stepGauge,
    ⟨fun _ => 1, show (0 : ℝ) < 1 from one_pos, ⟨false, rfl⟩, ⟨true, rfl⟩⟩, fun he => ?_, restrict_false_eq_true stepGauge 0,
    fun SA h h' ⟨H₀, H₁⟩ => ?_⟩
  · exact unif_false_ne_true (rnPolyfold 1) posSet (x₁ := 0) (lt_irrefl (0 : ℝ))
      (congrArg Subtype.val he)
  · exact not_continuous_stepGauge
      (continuous_of_isHomeomorph_restrictTransEquiv stepGauge 0 SA h h' H₀ H₁)

end Polyfold.GCT.PolyfoldConstruction
