import Polyfold.Chapter6.UntamedOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6:
**Theorem 6.6.13** (pp. 273–274), read with the 2021 sc-Fredholm notion of
**Definitions 3.1.16 = 3.6.4** (pp. 96, 135), whose germ data need not sit in a tame chart.

# Theorem 6.6.13 with the 2021 (untamed) sc-Fredholm notion: the functor is not unique

## The text, paraphrased

(Theorem 6.6.13) For an sc-Fredholm section `f` of a strong bundle over a tame M-polyfold there is
a uniquely determined functor `Γ_f : P_X → Or_f`, `x ↦ Or_x^f`, with property (∗): for a smooth
point `x`, a neighbourhood `U(x)` in which the orientations are propagated (Theorem 6.6.11) and an
sc-smooth path `φ` in `U(x)`, `Γ_f([φ])` is the local propagation `φ_*`.

## What is formalized

In general, for an sc-Fredholm section `f` (germ data in any compatible chart) of a strong bundle
with sc⁺-sections through every smooth fibre point, and a set `A` of points of `X`:

* `equiv_conj_eq_of_two`: a bijection between two sets with two elements commutes with the
  exchanges of the two elements.
* `orSwap`: the exchange of the two elements of `Or_x^f`; `orFlip A`: `orSwap` at the points of
  `A`, the identity elsewhere; `orFlipConj A G`: the family `G` on the morphisms of `P_X`
  conjugated by `orFlip A`, `[φ] ↦ orFlip_y ∘ G([φ]) ∘ orFlip_x⁻¹`.
* `IsOrientationFunctor f hf G`: the three properties of the family `Γ_f` in `theorem_6_6_13`
  (identities to identities, compositions to composites, property (∗) = `IsStarProperty`).
* `IsOrientationFunctor.orFlipConj`: **if no sc-smooth path in an open set with the local
  propagation property joins `A` and its complement, then `orFlipConj A G` is again a functor
  with property (∗)**; `orFlipConj_ne`: it is different from `G` as soon as some morphism of
  `P_X` goes from the complement of `A` to `A`.

For the untamed example `(bundle, sec)` of `Chapter3/UntamedBundle.lean` (base `O ≅ ℝ` with the
parameter `t`, the point `x₀` is `t = 0`), with `A = {t > 0}`:

* `pos_iff_of_hasLocalPropagation_sec`: an sc-smooth path in an open set with the local
  propagation property does not meet `x₀` (`not_hasLocalPropagation_sec`), so its two ends are on
  the same side of `x₀`: **property (∗) says nothing on the paths through `x₀`**.
* `crossingHom`: the class of the path `scPathO (1/2)`, a morphism of `P_O` from `t = −1/2` to
  `t = 1/2`.
* `exists_ne_orientation_functor_sec`: **for every functor `G` with property (∗) there is a
  second one, different from `G`** (`G` followed by the exchange of the two orientations at the
  points with `t > 0`).
* `not_existsUnique_orientation_functor_sec`: the conclusion of `theorem_6_6_13` does not hold for
  `(bundle, sec)`; `not_unique_orientation_functor_sec`: if a functor with property (∗) exists,
  then two functors with property (∗) need not agree.
* `theorem_6_6_13_untamed_not`: **the statement of `theorem_6_6_13` with
  `IsScFredholmSection2021` (2021 Definitions 3.1.16 = 3.6.4) in place of
  `IsScFredholmSectionTame` does not hold as we read it.**

## What this says about the text

The example meets the printed hypotheses (`untamed_example_hypotheses`).  No open set containing
`x₀` has the local propagation property, since the index is `1` for `t ≤ 0` and `0` for `t > 0`
(`isIndexAt_sec_iff`); hence property (∗) does not relate the orientations on the two sides of
`x₀`, and "exactly one functor with (∗)" does not hold as we read it: there is none or there are
at least two.  What is proved is the form `¬ ∃!` and the implication "one functor with (∗) gives a
second one".  The existence of a functor with (∗) for the example is not contradicted and is not
proved here: presumably it holds (propagation on each side of `x₀`, any bijection across `x₀`;
`O ≅ ℝ` is simply connected), so that it is presumably the uniqueness which is lost; a proof
needs the local propagation near the points `x ≠ x₀` of the example, where the germ data are in
tame charts (`isScFredholmGermTame_sec_of_ne`), and Theorem 6.6.11 is formalized for sections with
tame germ data at every smooth point.  With germ data in tame charts the statement is
`theorem_6_6_13`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-- **A bijection between two sets with two elements commutes with the exchanges**: for `s`, `t`
without fixed points, `t ∘ e ∘ s⁻¹ = e`. -/
theorem equiv_conj_eq_of_two {α β : Sort*} {b₁ b₂ : β} (hb : ∀ b, b = b₁ ∨ b = b₂) {s : α ≃ α}
    {t : β ≃ β} (hs : ∀ a, s a ≠ a) (ht : ∀ b, t b ≠ b) (e : α ≃ β) :
    s.symm.trans (e.trans t) = e :=
  Equiv.ext fun a => eq_of_ne_of_ne_of_two hb (ht (e (s.symm a)))
    (e.injective.ne fun h => hs a ((Equiv.eq_symm_apply s).1 h))

section General

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### The exchange of the two orientations -/

open Classical in
/-- **The exchange of the two elements of `Or_x^f`** (`exists_two_orx`). -/
def orSwap (hf : B.IsScFredholmSection f) (hsec : B.HasScPlusSectionsThrough) (x : X)
    (hs : x ∈ PX.smoothSet) : Orx f hf x hs ≃ Orx f hf x hs :=
  Equiv.swap (exists_two_orx hf hs hsec).choose (exists_two_orx hf hs hsec).choose_spec.choose

/-- The exchange has no fixed point. -/
theorem orSwap_ne (hf : B.IsScFredholmSection f) (hsec : B.HasScPlusSectionsThrough) (x : X)
    (hs : x ∈ PX.smoothSet) (o : Orx f hf x hs) : orSwap hf hsec x hs o ≠ o := by
  classical
  obtain ⟨hne, hall⟩ := (exists_two_orx hf hs hsec).choose_spec.choose_spec
  unfold orSwap
  rcases hall o with h | h
  · rw [h, Equiv.swap_apply_left]
    exact hne.symm
  · rw [h, Equiv.swap_apply_right]
    exact hne

open Classical in
/-- **The exchange of the orientations over a set `A`**: `orSwap` at the points of `A`, the
identity at the other points. -/
def orFlip (hf : B.IsScFredholmSection f) (hsec : B.HasScPlusSectionsThrough) (A : Set X) (x : X)
    (hs : x ∈ PX.smoothSet) : Orx f hf x hs ≃ Orx f hf x hs :=
  if x ∈ A then orSwap hf hsec x hs else Equiv.refl _

/-- At the points of `A`, `orFlip` is the exchange. -/
theorem orFlip_of_mem (hf : B.IsScFredholmSection f) (hsec : B.HasScPlusSectionsThrough)
    {A : Set X} {x : X} (hx : x ∈ A) (hs : x ∈ PX.smoothSet) :
    orFlip hf hsec A x hs = orSwap hf hsec x hs := by
  unfold orFlip
  exact if_pos hx

/-- At the points outside `A`, `orFlip` is the identity. -/
theorem orFlip_of_not_mem (hf : B.IsScFredholmSection f) (hsec : B.HasScPlusSectionsThrough)
    {A : Set X} {x : X} (hx : x ∉ A) (hs : x ∈ PX.smoothSet) :
    orFlip hf hsec A x hs = Equiv.refl _ := by
  unfold orFlip
  exact if_neg hx

/-- **A family of maps on the morphisms of `P_X` conjugated by the exchange over `A`**:
`[φ] ↦ orFlip_y ∘ G([φ]) ∘ orFlip_x⁻¹` for `[φ] : x ⟶ y`. -/
def orFlipConj (hf : B.IsScFredholmSection f) (hsec : B.HasScPlusSectionsThrough) (A : Set X)
    (G : ∀ x y : PathCat PX, (x ⟶ y) → (Orx f hf x.pt x.smooth ≃ Orx f hf y.pt y.smooth))
    (x y : PathCat PX) (a : x ⟶ y) : Orx f hf x.pt x.smooth ≃ Orx f hf y.pt y.smooth :=
  (orFlip hf hsec A x.pt x.smooth).symm.trans ((G x y a).trans (orFlip hf hsec A y.pt y.smooth))

/-- **The conjugated family differs from `G`** as soon as a morphism of `P_X` goes from the
complement of `A` to `A`. -/
theorem orFlipConj_ne (hf : B.IsScFredholmSection f) (hsec : B.HasScPlusSectionsThrough)
    {A : Set X}
    (G : ∀ x y : PathCat PX, (x ⟶ y) → (Orx f hf x.pt x.smooth ≃ Orx f hf y.pt y.smooth))
    {x y : PathCat PX} (a : x ⟶ y) (hx : x.pt ∉ A) (hy : y.pt ∈ A) :
    orFlipConj hf hsec A G ≠ G := by
  intro h
  have e : (orFlip hf hsec A x.pt x.smooth).symm.trans
      ((G x y a).trans (orFlip hf hsec A y.pt y.smooth)) = G x y a :=
    congrFun (congrFun (congrFun h x) y) a
  rw [orFlip_of_not_mem hf hsec hx, orFlip_of_mem hf hsec hy] at e
  obtain ⟨o, -⟩ := exists_two_orx hf x.smooth hsec
  exact orSwap_ne hf hsec y.pt y.smooth (G x y a o) (Equiv.congr_fun e o)

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-! ### Functors with property (∗) -/

variable (f) in
/-- **The properties of the family `Γ_f` in Theorem 6.6.13** (the conditions of
`theorem_6_6_13`), for a family `G` of maps `Or_x^f ≃ Or_y^f` on the morphisms `x ⟶ y` of `P_X`:
identities go to identities, compositions to composites, and `G` has property (∗)
(`IsStarProperty`). -/
def IsOrientationFunctor (hf : B.IsScFredholmSection f)
    (G : ∀ x y : PathCat PX, (x ⟶ y) → (Orx f hf x.pt x.smooth ≃ Orx f hf y.pt y.smooth)) :
    Prop :=
  (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
  (∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z), G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
  IsStarProperty f hf G

/-- **A functor with property (∗), conjugated by the exchange of the orientations over `A`, is a
functor with property (∗)**, if no sc-smooth path in an open set with the local propagation
property joins `A` and its complement: property (∗) is asked on such paths only, and there the
conjugated family is `G` (`equiv_conj_eq_of_two`). -/
theorem IsOrientationFunctor.orFlipConj {hf : B.IsScFredholmSection f}
    (hsec : B.HasScPlusSectionsThrough) {A : Set X}
    {G : ∀ x y : PathCat PX, (x ⟶ y) → (Orx f hf x.pt x.smooth ≃ Orx f hf y.pt y.smooth)}
    (hG : IsOrientationFunctor f hf G)
    (hA : ∀ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U : Set X), IsOpen U →
      HasLocalPropagation f hf c hc U → ∀ γ : (Fin 1 → ℝ) → X,
      (rnPolyfold 1).IsScSmoothMap PX γ → (∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U) →
      (γ (pt1 0) ∈ A ↔ γ (pt1 1) ∈ A)) :
    IsOrientationFunctor f hf (Polyfold.orFlipConj hf hsec A G) := by
  refine ⟨fun x => ?_, fun x y z a b => ?_, fun c hc U hUo hU x y φ hφ hx hy e he => ?_⟩
  · change (orFlip hf hsec A x.pt x.smooth).symm.trans
      ((G x x (𝟙 x)).trans (orFlip hf hsec A x.pt x.smooth)) = Equiv.refl _
    rw [hG.1 x, Equiv.refl_trans, Equiv.symm_trans_self]
  · change (orFlip hf hsec A x.pt x.smooth).symm.trans
      ((G x z (a ≫ b)).trans (orFlip hf hsec A z.pt z.smooth)) =
      ((orFlip hf hsec A x.pt x.smooth).symm.trans
        ((G x y a).trans (orFlip hf hsec A y.pt y.smooth))).trans
      ((orFlip hf hsec A y.pt y.smooth).symm.trans
        ((G y z b).trans (orFlip hf hsec A z.pt z.smooth)))
    rw [hG.2.1 x y z a b]
    refine Equiv.ext fun o => ?_
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  · have key : ∀ R : Orx f hf x.pt x.smooth ≃ Orx f hf y.pt y.smooth,
        (orFlip hf hsec A x.pt x.smooth).symm.trans
          (R.trans (orFlip hf hsec A y.pt y.smooth)) = R := by
      intro R
      have hiff : x.pt ∈ A ↔ y.pt ∈ A := by
        have h := hA c hc U hUo hU φ.toFun φ.isScSmoothMap hφ
        rwa [φ.source, φ.target] at h
      by_cases hxA : x.pt ∈ A
      · obtain ⟨o₁, o₂, -, hall⟩ := exists_two_orx hf y.smooth hsec
        rw [orFlip_of_mem hf hsec hxA, orFlip_of_mem hf hsec (hiff.1 hxA)]
        exact equiv_conj_eq_of_two hall (orSwap_ne hf hsec x.pt x.smooth)
          (orSwap_ne hf hsec y.pt y.smooth) R
      · rw [orFlip_of_not_mem hf hsec hxA, orFlip_of_not_mem hf hsec (fun h => hxA (hiff.2 h))]
        rfl
    exact (key _).trans (hG.2.2 c hc U hUo hU x y φ hφ hx hy e he)

end General

/-! ### The untamed example -/

namespace UntamedCorner

/-- **An sc-smooth path in an open set with the local propagation property stays on one side of
`x₀`**: such a set does not contain `x₀` (`not_hasLocalPropagation_sec`), and `t` is continuous
along the path. -/
theorem pos_iff_of_hasLocalPropagation_sec (c : StrongBundleChart polyO kproj)
    (hc : bundle.IsChart c) {U : Set Ob} (hUo : IsOpen U)
    (hU : haveI := paracompactSpace_rn_prod polyO
      haveI := paracompactSpace_rn_pullback bundle
      HasLocalPropagation sec isScFredholmSection_sec c hc U)
    {γ : (Fin 1 → ℝ) → Ob} (hγs : (rnPolyfold 1).IsScSmoothMap polyO γ)
    (hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U) :
    0 < tco (γ (pt1 0)) ↔ 0 < tco (γ (pt1 1)) := by
  have h0 : x0 ∉ U := fun h0 => not_hasLocalPropagation_sec c hc hUo h0 hU
  have hcont : Continuous fun s : ℝ => tco (γ (pt1 s)) :=
    continuous_tco.comp ((continuousOn_univ.1 hγs.continuousOn).comp continuous_pt1)
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, tco (γ (pt1 s)) ≠ 0 := fun s hs h =>
    h0 (tco_injective (a₁ := γ (pt1 s)) (a₂ := x0) h ▸ hγ _ (pt1_mem_Icc hs))
  have e0 := hne 0 (left_mem_Icc.2 zero_le_one)
  have e1 := hne 1 (right_mem_Icc.2 zero_le_one)
  constructor
  · intro h
    by_contra h1
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont.continuousOn
      (show (0 : ℝ) ∈ Icc (tco (γ (pt1 1))) (tco (γ (pt1 0))) from ⟨not_lt.1 h1, h.le⟩)
    exact hne s hs hs0
  · intro h
    by_contra h1
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc (zero_le_one' ℝ) hcont.continuousOn
      (show (0 : ℝ) ∈ Icc (tco (γ (pt1 0))) (tco (γ (pt1 1))) from ⟨not_lt.1 h1, h.le⟩)
    exact hne s hs hs0

/-- The start `t = −1/2` of the path `scPathO (1/2)`, an object of `P_O`. -/
def crossingSource : PathCat polyO := ⟨scPathO (1 / 2) (pt1 0), mem_smoothSet_polyO _⟩

/-- The end `t = 1/2` of the path `scPathO (1/2)`, an object of `P_O`. -/
def crossingTarget : PathCat polyO := ⟨scPathO (1 / 2) (pt1 1), mem_smoothSet_polyO _⟩

/-- **A morphism of `P_O` across `x₀`**: the class of the path `scPathO (1/2)` from `t = −1/2`
to `t = 1/2`. -/
def crossingHom : crossingSource ⟶ crossingTarget :=
  PathCat.homMk ⟨scPathO (1 / 2), isScSmoothMap_scPathO (by norm_num) (by norm_num), rfl, rfl⟩

/-- The start of the path `scPathO (1/2)` is `t = −1/2`. -/
lemma tco_crossingSource : tco crossingSource.pt = -(1 / 2) := by
  change tco (scPathO (1 / 2) (pt1 0)) = _
  rw [tco_scPathO (by norm_num) (by norm_num), pt1_apply, Real.smoothTransition.zero]
  norm_num

/-- The end of the path `scPathO (1/2)` is `t = 1/2`. -/
lemma tco_crossingTarget : tco crossingTarget.pt = 1 / 2 := by
  change tco (scPathO (1 / 2) (pt1 1)) = _
  rw [tco_scPathO (by norm_num) (by norm_num), pt1_apply, Real.smoothTransition.one]
  norm_num

/-- **A functor with property (∗) for `(bundle, sec)` is never the only one**: for every family
`G` on the morphisms of `P_O` which is a functor and has property (∗) there is a second such
family `G' ≠ G`, namely `G` conjugated by the exchange of the two orientations at the points with
`t > 0` (`orFlipConj`).  Property (∗) holds for `G'` since no path on which (∗) is asked passes
through `x₀` (`pos_iff_of_hasLocalPropagation_sec`), and `G'([φ]) ≠ G([φ])` for the class of the
path `scPathO (1/2)` (`crossingHom`). -/
theorem exists_ne_orientation_functor_sec :
    haveI := paracompactSpace_rn_prod polyO
    haveI := paracompactSpace_rn_pullback bundle
    ∀ G : ∀ x y : PathCat polyO, (x ⟶ y) →
        (Orx sec isScFredholmSection_sec x.pt x.smooth ≃
          Orx sec isScFredholmSection_sec y.pt y.smooth),
      IsOrientationFunctor sec isScFredholmSection_sec G →
      ∃ G', G' ≠ G ∧ IsOrientationFunctor sec isScFredholmSection_sec G' := by
  have := paracompactSpace_rn_prod polyO
  have := paracompactSpace_rn_pullback bundle
  intro G hG
  refine ⟨orFlipConj isScFredholmSection_sec hasScPlusSectionsThrough_bundle
      {x : Ob | 0 < tco x} G,
    orFlipConj_ne isScFredholmSection_sec hasScPlusSectionsThrough_bundle G crossingHom ?_ ?_,
    hG.orFlipConj hasScPlusSectionsThrough_bundle fun c hc U hUo hU γ hγs hγ =>
      pos_iff_of_hasLocalPropagation_sec c hc hUo hU hγs hγ⟩
  · change ¬ 0 < tco crossingSource.pt
    rw [tco_crossingSource]
    norm_num
  · change 0 < tco crossingTarget.pt
    rw [tco_crossingTarget]
    norm_num

/-- **The conclusion of `theorem_6_6_13` (2021 Theorem 6.6.13) does not hold for
`(bundle, sec)`**: there is not exactly one functor `P_O → Or_sec` with property (∗); every such
functor has a second one beside it (`exists_ne_orientation_functor_sec`). -/
theorem not_existsUnique_orientation_functor_sec :
    haveI := paracompactSpace_rn_prod polyO
    haveI := paracompactSpace_rn_pullback bundle
    ¬ ∃! G : ∀ x y : PathCat polyO, (x ⟶ y) →
        (Orx sec isScFredholmSection_sec x.pt x.smooth ≃
          Orx sec isScFredholmSection_sec y.pt y.smooth),
      (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
      (∀ (x y z : PathCat polyO) (a : x ⟶ y) (b : y ⟶ z),
        G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
      IsStarProperty sec isScFredholmSection_sec G := by
  have := paracompactSpace_rn_prod polyO
  have := paracompactSpace_rn_pullback bundle
  rintro ⟨G, hG, huniq⟩
  obtain ⟨G', hne, hG'⟩ := exists_ne_orientation_functor_sec G hG
  exact hne (huniq G' hG')

/-- **The uniqueness in 2021 Theorem 6.6.13 for `(bundle, sec)`**: if there is a functor
`P_O → Or_sec` with property (∗), then two functors with property (∗) need not agree. -/
theorem not_unique_orientation_functor_sec :
    haveI := paracompactSpace_rn_prod polyO
    haveI := paracompactSpace_rn_pullback bundle
    (∃ G, IsOrientationFunctor sec isScFredholmSection_sec G) →
    ¬ ∀ G G', IsOrientationFunctor sec isScFredholmSection_sec G →
      IsOrientationFunctor sec isScFredholmSection_sec G' → G = G' := by
  have := paracompactSpace_rn_prod polyO
  have := paracompactSpace_rn_pullback bundle
  rintro ⟨G, hG⟩ h
  obtain ⟨G', hne, hG'⟩ := exists_ne_orientation_functor_sec G hG
  exact hne (h G' G hG' hG)

/-- **2021 Theorem 6.6.13, pp. 273–274, read with the 2021 sc-Fredholm notion, does not hold as we
read it**: the statement of `theorem_6_6_13` with `IsScFredholmSection2021` (Definitions
3.1.16 = 3.6.4, no tameness of the chart of the germ data) in place of `IsScFredholmSectionTame`,
for a tame strong bundle (`IsTameBundle`) over an M-polyfold with bump functions.  The
counterexample is `(bundle, sec)`: property (∗) does not relate the orientations on the two sides
of `x₀`, and beside every functor with (∗) there is a second one
(`exists_ne_orientation_functor_sec`).  The existence of a functor with (∗) is not contradicted.
With germ data in tame charts the statement is `theorem_6_6_13`. -/
theorem theorem_6_6_13_untamed_not :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      (Y : Type) [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
      (f : X → Y), B.IsTameBundle → PX.AdmitsBumpFunctions →
      ∀ hf : B.IsScFredholmSection2021 f,
      haveI := paracompactSpace_rn_prod PX
      haveI := paracompactSpace_rn_pullback B
      ∃! G : ∀ x y : PathCat PX, (x ⟶ y) →
          (Orx f (StrongBundle.isScFredholmSection2021_iff.1 hf) x.pt x.smooth ≃
            Orx f (StrongBundle.isScFredholmSection2021_iff.1 hf) y.pt y.smooth),
        (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
        (∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
          G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
        IsStarProperty f (StrongBundle.isScFredholmSection2021_iff.1 hf) G := fun h =>
  not_existsUnique_orientation_functor_sec (h Ob polyO Kt kproj bundle sec isTameBundle_bundle
    admitsBumpFunctions_polyO isScFredholmSection2021_sec)

end UntamedCorner

end Polyfold
