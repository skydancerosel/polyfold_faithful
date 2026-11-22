import Polyfold.Chapter19.NaturalTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.1–§19.2 (pp. 864–872): witnesses for **Definitions 19.1.3, 19.1.5–19.1.7** and
**Theorem 19.2.2**, the example `theorem_19_2_2_empty_family` (why `F(α) ≠ ∅` is needed), and
**Remark 19.2.3**.  Numbers and pages are the 2021 text's.

# Basic constructions: witnesses and Remark 19.2.3

## The constructions

* **Keyed transition data** (`TransitionData.ofKey`).  Suppose a map `κ : mor(S) → K` and sets
  `D(h) ⊂ O` are given such that an element of `M(Ψ, Ψ')` is determined by its source and the
  key of its morphism, `D(h)` is the open set of the `q` over which `M(Ψ, Ψ')` has an element with
  the key of `h`, `κ` is compatible with `u`, `ι`, `m` and `Ψ(g, ·)`, and `q ↦ t(h_q)` is an
  sc-diffeomorphism on `D(h)`.  Then `F_h(q)`, the element over `q` with the key of `h`,
  satisfies (A)–(F).
* **Translation groupoids** (`translationBasic`): for `C = G ⋉ O`, `F(x) = {Ψ₀}` with `Ψ₀` the
  tautological uniformizer (the identity), key `κ(g, x) = g`, `D(h) = O`, so
  `F_h(q) = (q, g, g ∗ q)` for `h = (o, g, g ∗ o)`.  Every `F(x)` is non-empty.  Instances:
  `reflectionBasic` on `ℤ/2 ⋉ ℝ` (reflection; a non-trivial action, centred at `0`) and `z3Basic`
  on `ℤ/3 ⋉ ℝ` (trivial action; centred at every object, so `IsCentred`).
* **The empty construction** (`emptyBasic`): `F ≡ ∅` on `ℤ/2 ⋉ ℝ`; the Properties (19.3) hold
  vacuously.
* **Remark 19.2.3** (`gluedLines`, `gluedBasic`): objects `ℝ × {±1}`; besides the units, one
  morphism `(x, a) → (x, −a)` for every `x > 0`.  `F((x, a)) = {Ψ_a}`, `Ψ_a(t) = (t, a)` with the
  trivial group; key `κ(x, a, k) = k`, `D(h) = ℝ` for `k = 1` and `(0, ∞)` for `k = −1`.

## What is formalized

* `keyMap`, `keyMap_spec`, `keyMap_eq`, `TransitionData.ofKey`.
* `tautUniformizer`, `translationUnif`, `taut_trans_ext`, `translationData`, `translationBasic`,
  `translationBasic_hasUniformizers`; `reflectionBasic` with `reflectionBasic_witness` (every
  `F(x) ≠ ∅`, the action is non-trivial, the uniformizer is centred at `0`) and
  `reflectionBasic_theorem_19_2_2`; `z3Basic` with `z3Basic_isCentred`.
* `emptyUnif`, `emptyData`, `emptyBasic`, `emptyBasic_natOpen_iff` (`T = {∅}`) and
  **`theorem_19_2_2_empty_family`**: for `emptyBasic` (`F ≡ ∅`) the collection `T` is not the
  collection of open sets of a topology, since `|S| ∉ T`; this is why we read `F(α) ≠ ∅`, the
  standing reading of §17.1, throughout.
* **Remark 19.2.3**: `GluedMor`, `gluedStr`, `gluedLines`, `gluedLines_π_eq_iff`,
  `gluedLines_π_ne` (`|(0, −1)| ≠ |(0, 1)|`), `gluedUnif` (`Ψ_a`), `gluedU`, `gluedData`,
  `gluedBasic`, `gluedBasic_hasUniformizers`, `gluedBasic_isCentred`, `gluedBasic_natOpen`, and
  `remark_19_2_3` (`T` is not Hausdorff).

## Readings

* Remark 19.2.3 says that the transition sets "have natural smooth structures"; the topology of
  `M(Ψ_ε, Ψ_δ)` belongs to §19.3 and the smooth structures to §19.5, so we formalize the claim
  about `T` and the basic construction it rests on.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)

/-! ### Keyed transition data -/

section Key

variable {C : GroupoidalCategory.{u}} {K : Type*} (κ : C.Mor → K)

open Classical in
/-- The element of `M(Ψ, Ψ')` over `q` whose morphism has the key of `h` (and `h` if there is
none). -/
def keyMap {Ψ Ψ' : C.Uniformizer} (h : Ψ.Trans Ψ') (q : Ψ.O) : Ψ.Trans Ψ' :=
  if hq : ∃ h' : Ψ.Trans Ψ', h'.src = q ∧ κ h'.mor = κ h.mor then hq.choose else h

theorem keyMap_spec {Ψ Ψ' : C.Uniformizer} {h : Ψ.Trans Ψ'} {q : Ψ.O}
    (hq : ∃ h' : Ψ.Trans Ψ', h'.src = q ∧ κ h'.mor = κ h.mor) :
    (keyMap κ h q).src = q ∧ κ (keyMap κ h q).mor = κ h.mor := by
  rw [keyMap, dif_pos hq]
  exact hq.choose_spec

theorem keyMap_eq {Ψ Ψ' : C.Uniformizer}
    (hinj : ∀ h₁ h₂ : Ψ.Trans Ψ', h₁.src = h₂.src → κ h₁.mor = κ h₂.mor → h₁ = h₂)
    {h : Ψ.Trans Ψ'} {q : Ψ.O} (h' : Ψ.Trans Ψ') (hs : h'.src = q) (hk : κ h'.mor = κ h.mor) :
    keyMap κ h q = h' := by
  obtain ⟨h1, h2⟩ := keyMap_spec κ ⟨h', hs, hk⟩
  exact hinj _ _ (h1.trans hs.symm) (h2.trans hk.symm)

namespace UniformizerConstruction.TransitionData

variable {U : C.UniformizerConstruction} (D : ∀ Ψ Ψ' : U.Unif, Ψ.1.Trans Ψ'.1 → Set Ψ.1.O)

/-- **Keyed transition data**: `F_h(q)` is the element of `M(Ψ, Ψ')` over `q` with the key of `h`,
defined on the open set `D(h)` of the `q` over which there is one.  The hypotheses: an element
is determined by its source and key (`hinj`), the key is compatible with `u`, `ι`, `m` and
`Ψ(g, ·)`, and `q ↦ t(F_h(q))` is an sc-diffeomorphism on `D(h)`. -/
def ofKey
    (hinj : ∀ (Ψ Ψ' : U.Unif) (h₁ h₂ : Ψ.1.Trans Ψ'.1), h₁.src = h₂.src →
      κ h₁.mor = κ h₂.mor → h₁ = h₂)
    (hD : ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) (q : Ψ.1.O),
      q ∈ D Ψ Ψ' h ↔ ∃ h' : Ψ.1.Trans Ψ'.1, h'.src = q ∧ κ h'.mor = κ h.mor)
    (hDo : ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1), IsOpen (D Ψ Ψ' h))
    (hdiffeo : ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1), ∃ (f : Ψ.1.O → Ψ'.1.O)
      (g : Ψ'.1.O → Ψ.1.O) (V : Set Ψ'.1.O), Ψ.1.P.IsScDiffeoOn Ψ'.1.P f g (D Ψ Ψ' h) V ∧
        ∀ h' : Ψ.1.Trans Ψ'.1, κ h'.mor = κ h.mor → f h'.src = h'.tgt)
    (hunit : ∀ x y, κ (C.toGroupoidStr.unit x) = κ (C.toGroupoidStr.unit y))
    (hinv : ∀ φ ψ, κ φ = κ ψ → κ (C.toGroupoidStr.inv φ) = κ (C.toGroupoidStr.inv ψ))
    (hcomp : ∀ φ φ' ψ ψ', C.toGroupoidStr.src φ = C.toGroupoidStr.tgt ψ →
      C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt ψ' → κ φ = κ φ' → κ ψ = κ ψ' →
        κ (C.toGroupoidStr.comp φ ψ) = κ (C.toGroupoidStr.comp φ' ψ'))
    (hhat : ∀ (Ψ : U.Unif) (g : Ψ.1.G) (q q' : Ψ.1.O), κ (Ψ.1.mor (g, q)) = κ (Ψ.1.mor (g, q'))) :
    U.TransitionData where
  dom := D
  map _ _ h q := keyMap κ h q
  isOpen_dom := hDo
  mem_dom Ψ Ψ' h := (hD Ψ Ψ' h _).2 ⟨h, rfl, rfl⟩
  map_src Ψ Ψ' h := keyMap_eq κ (hinj Ψ Ψ') h rfl rfl
  src_map Ψ Ψ' h q hq := (keyMap_spec κ ((hD Ψ Ψ' h q).1 hq)).1
  diffeo Ψ Ψ' h := by
    obtain ⟨f, g, V, hfg, hf⟩ := hdiffeo Ψ Ψ' h
    have heq : EqOn f (fun q => (keyMap κ h q).tgt) (D Ψ Ψ' h) := fun q hq => by
      obtain ⟨hs, hk⟩ := keyMap_spec κ ((hD Ψ Ψ' h q).1 hq)
      change f q = (keyMap κ h q).tgt
      rw [← hf _ hk, hs]
    have h' := hfg.congr_left heq
    refine ⟨g, ?_⟩
    rw [h'.image_eq]
    exact h'
  map_hat Ψ p q _ := keyMap_eq κ (hinj Ψ Ψ) (Ψ.1.hat (p.1, q)) rfl (hhat Ψ p.1 q p.2)
  stability Ψ Ψ' h q hq p hp := by
    have hk := (keyMap_spec κ ((hD Ψ Ψ' h q).1 hq)).2
    obtain ⟨hs', hk'⟩ := keyMap_spec κ ((hD Ψ Ψ' h p).1 hp.2)
    exact keyMap_eq κ (hinj Ψ Ψ') _ hs' (hk'.trans hk.symm)
  identity Ψ o q _ := keyMap_eq κ (hinj Ψ Ψ) _ rfl (hunit _ _)
  inversion Ψ Ψ' h q hq _ :=
    keyMap_eq κ (hinj Ψ' Ψ) _ rfl (hinv _ _ (keyMap_spec κ ((hD Ψ Ψ' h q).1 hq)).2)
  multiplication Ψ Ψ' Ψ'' h h' hh q hq hq' _ := by
    obtain ⟨hs, hk⟩ := keyMap_spec κ ((hD Ψ Ψ' h q).1 hq)
    obtain ⟨hs', hk'⟩ := keyMap_spec κ ((hD Ψ' Ψ'' h' _).1 hq')
    refine (keyMap_eq κ (hinj Ψ Ψ'') _ hs (hcomp _ _ _ _ ?_ ?_ hk' hk)).symm
    · exact TransitionSet.mor_composable_of_src_eq_tgt hs'
    · exact TransitionSet.mor_composable_of_src_eq_tgt hh
  hausdorff Ψ Ψ' h₁ h₂ hne hs := by
    by_cases hk : κ h₁.mor = κ h₂.mor
    · exact absurd (hinj Ψ Ψ' h₁ h₂ hs hk) hne
    have m₁ := (hD Ψ Ψ' h₁ _).2 ⟨h₁, rfl, rfl⟩
    have m₂ : h₁.src ∈ D Ψ Ψ' h₂ := hs ▸ (hD Ψ Ψ' h₂ _).2 ⟨h₂, rfl, rfl⟩
    refine ⟨D Ψ Ψ' h₁ ∩ D Ψ Ψ' h₂, (hDo Ψ Ψ' h₁).inter (hDo Ψ Ψ' h₂), ⟨m₁, m₂⟩, subset_rfl, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨q, hq, rfl⟩ ⟨q', hq', he⟩
    have he' : keyMap κ h₂ q' = keyMap κ h₁ q := he
    apply hk
    rw [← (keyMap_spec κ ((hD Ψ Ψ' h₁ q).1 hq.1)).2,
      ← (keyMap_spec κ ((hD Ψ Ψ' h₂ q').1 hq'.2)).2, he']

end UniformizerConstruction.TransitionData

end Key

/-! ### Translation groupoids -/

section Translation

variable {G O : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O] {P : MPolyfold O}

variable (P) in
/-- The tautological uniformizer of `G ⋉ O` (the identity functor). -/
abbrev tautUniformizer (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y) :
    (GroupoidalCategory.translation G O).Uniformizer :=
  (GCT.LocalUniformizer.tautological P hP).toUniformizer

variable (P) in
/-- The uniformizer construction `F(x) = {Ψ₀}` of `G ⋉ O`. -/
abbrev translationUnif (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y) :
    (GroupoidalCategory.translation G O).UniformizerConstruction where
  F _ := {tautUniformizer P hP}
  isAt x Ψ hΨ := by
    rw [mem_singleton_iff] at hΨ
    subst hΨ
    exact ⟨x, rfl⟩

theorem translationUnif_eq (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y)
    (Ψ : (translationUnif P hP).Unif) : Ψ.1 = tautUniformizer P hP := by
  obtain ⟨_, _, h⟩ := Ψ
  exact h

/-- Elements of `M(Ψ₀, Ψ₀)` are determined by source and group element. -/
theorem taut_trans_ext (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y)
    (h₁ h₂ : (tautUniformizer P hP).Trans (tautUniformizer P hP)) (hs : h₁.src = h₂.src)
    (hk : h₁.mor.1 = h₂.mor.1) : h₁ = h₂ := by
  have a₁ : h₁.mor.2 = h₁.src := h₁.src_mor
  have a₂ : h₂.mor.2 = h₂.src := h₂.src_mor
  have hm : h₁.mor = h₂.mor := Prod.ext hk (by rw [a₁, a₂, hs])
  have b₁ : h₁.mor.1 • h₁.mor.2 = h₁.tgt := h₁.tgt_mor
  have b₂ : h₂.mor.1 • h₂.mor.2 = h₂.tgt := h₂.tgt_mor
  exact TransitionSet.ext hs hm (by rw [← b₁, ← b₂, hm])

variable (P) in
/-- **The basic construction of a translation groupoid** `G ⋉ O`: `F(x) = {Ψ₀}` and
`F_h(q) = (q, g, g ∗ q)` for `h = (o, g, g ∗ o)` (keyed by `κ(g, x) = g`, `D(h) = O`). -/
def translationData (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y) :
    (translationUnif P hP).TransitionData :=
  UniformizerConstruction.TransitionData.ofKey (U := translationUnif P hP)
    (Prod.fst : G × O → G) (fun _ _ _ => univ)
    (fun Ψ Ψ' => by
      obtain ⟨Ψ₁, -, h₁⟩ := Ψ; obtain ⟨Ψ₂, -, h₂⟩ := Ψ'
      rw [mem_singleton_iff] at h₁ h₂; subst h₁ h₂
      exact taut_trans_ext hP)
    (fun Ψ Ψ' => by
      obtain ⟨Ψ₁, -, h₁⟩ := Ψ; obtain ⟨Ψ₂, -, h₂⟩ := Ψ'
      rw [mem_singleton_iff] at h₁ h₂; subst h₁ h₂
      intro h q
      exact ⟨fun _ => ⟨(tautUniformizer P hP).hat (h.mor.1, q), rfl, rfl⟩, fun _ => mem_univ _⟩)
    (fun _ _ _ => isOpen_univ)
    (fun Ψ Ψ' => by
      obtain ⟨Ψ₁, -, h₁⟩ := Ψ; obtain ⟨Ψ₂, -, h₂⟩ := Ψ'
      rw [mem_singleton_iff] at h₁ h₂; subst h₁ h₂
      intro h
      refine ⟨fun q => h.mor.1 • q, fun q => h.mor.1⁻¹ • q, univ,
        ⟨hP _, hP _, mapsTo_univ _ _, mapsTo_univ _ _, fun x _ => inv_smul_smul _ x,
          fun y _ => smul_inv_smul _ y⟩, fun h' hk => ?_⟩
      have a : h'.mor.2 = h'.src := h'.src_mor
      have b : h'.mor.1 • h'.mor.2 = h'.tgt := h'.tgt_mor
      change h.mor.1 • h'.src = h'.tgt
      rw [← hk, ← a, b])
    (fun _ _ => rfl)
    (fun _ _ h => congrArg (·⁻¹) h)
    (fun _ _ _ _ _ _ h₁ h₂ => congrArg₂ (· * ·) h₁ h₂)
    (fun Ψ => by
      obtain ⟨Ψ₁, -, h₁⟩ := Ψ
      rw [mem_singleton_iff] at h₁; subst h₁
      intro _ _ _; rfl)

variable (P) in
/-- **The basic construction of a translation groupoid** `G ⋉ O` (Definition 19.1.7). -/
def translationBasic (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y) :
    (GroupoidalCategory.translation G O).BasicConstruction :=
  ⟨translationUnif P hP, ⟦translationData P hP⟧⟩

theorem translationBasic_hasUniformizers (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y) :
    (translationBasic P hP).U.HasUniformizers := fun _ => ⟨_, rfl⟩

end Translation

/-! ### `ℤ/2 ⋉ ℝ` and `ℤ/3 ⋉ ℝ` -/

section Witnesses

open EpGroupoid.Examples

/-- **The basic construction of `ℤ/2 ⋉ ℝ`** (`ℤ/2 = ℤˣ` acting by reflection). -/
abbrev reflectionBasic : (GroupoidalCategory.translation ℤˣ (Fin 1 → ℝ)).BasicConstruction :=
  translationBasic (rnPolyfold 1) isScSmoothMap_units_smul

/-- **The non-degenerate witness for Theorem 19.2.2**: in `reflectionBasic` every `F(x)` is
non-empty, `G = ℤ/2` acts non-trivially on `O = ℝ`, and the uniformizer is centred at `0`. -/
theorem reflectionBasic_witness :
    reflectionBasic.U.HasUniformizers ∧
      (∀ x, ∀ Ψ ∈ reflectionBasic.U.F x, ∃ (g : Ψ.G) (q : Ψ.O), g • q ≠ q) ∧
      (tautUniformizer (rnPolyfold 1) isScSmoothMap_units_smul).IsCentredAt
        (0 : Fin 1 → ℝ) := by
  refine ⟨translationBasic_hasUniformizers _, fun x Ψ hΨ => ?_,
    GCT.LocalUniformizer.reflection_isCentredAt.1⟩
  rw [show Ψ = _ from hΨ]
  exact GCT.LocalUniformizer.reflection_isCentredAt.2

/-- **Theorem 19.2.2** for `reflectionBasic`: `T` is a first countable topology for which
`|Ψ₀| : G\O → |S|` is an open embedding. -/
theorem reflectionBasic_theorem_19_2_2 :
    let hB := (translationBasic_hasUniformizers _).hasClassUniformizers
    @FirstCountableTopology _ (reflectionBasic.natTop hB) ∧
      @IsOpenEmbedding _ _ _ (reflectionBasic.natTop hB)
        (tautUniformizer (rnPolyfold 1) isScSmoothMap_units_smul).functor.orbitMap :=
  ⟨reflectionBasic.theorem_19_2_2_four _,
    (reflectionBasic.theorem_19_2_2_three _ (α := 0) rfl).1⟩

/-- **The basic construction of `ℤ/3 ⋉ ℝ`** (trivial action). -/
abbrev z3Basic :
    (GroupoidalCategory.translation (Multiplicative (ZMod 3)) (Fin 1 → ℝ)).BasicConstruction :=
  translationBasic (rnPolyfold 1) isScSmoothMap_z3_smul

/-- In `z3Basic` every `F(x)` is non-empty and every uniformizer of `F(x)` is centred at `x` with
`G = ℤ/3`. -/
theorem z3Basic_isCentred : z3Basic.U.HasUniformizers ∧ z3Basic.U.IsCentred ∧
    Nat.card (tautUniformizer (rnPolyfold 1) isScSmoothMap_z3_smul).G = 3 := by
  refine ⟨translationBasic_hasUniformizers _, fun x Ψ hΨ => ?_, ?_⟩
  · rw [show Ψ = _ from hΨ]
    exact ⟨x, rfl, fun _ => rfl⟩
  · change Nat.card (Multiplicative (ZMod 3)) = 3
    rw [Nat.card_eq_fintype_card]
    rfl

end Witnesses

/-! ### The empty construction and Theorem 19.2.2 (1) -/

section Empty

/-- The uniformizer construction `F ≡ ∅` on `ℤ/2 ⋉ ℝ`. -/
abbrev emptyUnif : (GroupoidalCategory.translation ℤˣ (Fin 1 → ℝ)).UniformizerConstruction where
  F _ := ∅
  isAt _ _ h := absurd h (notMem_empty _)

theorem emptyUnif_elim (Ψ : emptyUnif.Unif) : False := by
  obtain ⟨_, _, h⟩ := Ψ
  exact h

/-- Transition data for `F ≡ ∅` (there are no uniformizers). -/
def emptyData : emptyUnif.TransitionData where
  dom Ψ := (emptyUnif_elim Ψ).elim
  map Ψ := (emptyUnif_elim Ψ).elim
  isOpen_dom Ψ := (emptyUnif_elim Ψ).elim
  mem_dom Ψ := (emptyUnif_elim Ψ).elim
  map_src Ψ := (emptyUnif_elim Ψ).elim
  src_map Ψ := (emptyUnif_elim Ψ).elim
  diffeo Ψ := (emptyUnif_elim Ψ).elim
  map_hat Ψ := (emptyUnif_elim Ψ).elim
  stability Ψ := (emptyUnif_elim Ψ).elim
  identity Ψ := (emptyUnif_elim Ψ).elim
  inversion Ψ := (emptyUnif_elim Ψ).elim
  multiplication Ψ := (emptyUnif_elim Ψ).elim
  hausdorff Ψ := (emptyUnif_elim Ψ).elim

/-- **The basic construction `F ≡ ∅`** on `ℤ/2 ⋉ ℝ` (Definition 19.1.7 holds). -/
def emptyBasic : (GroupoidalCategory.translation ℤˣ (Fin 1 → ℝ)).BasicConstruction :=
  ⟨emptyUnif, ⟦emptyData⟧⟩

/-- For `F ≡ ∅`, `T = {∅}`. -/
theorem emptyBasic_natOpen_iff
    (W : Set (GroupoidalCategory.translation ℤˣ (Fin 1 → ℝ)).OrbitSpace) :
    emptyBasic.U.NatOpen W ↔ W = ∅ := by
  refine ⟨fun h => eq_empty_iff_forall_notMem.2 fun z hz => ?_,
    fun h => h ▸ emptyBasic.U.natOpen_empty⟩
  obtain ⟨_, _, Ψ, hΨ, -⟩ := h z hz
  exact hΨ

/-- **2021 Theorem 19.2.2 (1), p. 869, for an empty uniformizer construction**: "`T` is a topology
on `|S|`" does not hold for the basic construction `F ≡ ∅` on `ℤ/2 ⋉ ℝ`, as `|S| ∉ T = {∅}`.  This shows
why `F(α) ≠ ∅`, the standing reading of §17.1, is needed; under it (every isomorphism class meets
a uniformizer) the statement is `BasicConstruction.theorem_19_2_2_one`. -/
theorem theorem_19_2_2_empty_family :
    ¬ ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction),
      ∃ τ : TopologicalSpace C.OrbitSpace, ∀ W, IsOpen[τ] W ↔ B.U.NatOpen W := by
  intro h
  obtain ⟨τ, hτ⟩ := h _ emptyBasic
  have hu := (hτ univ).1 (@isOpen_univ _ τ)
  rw [emptyBasic_natOpen_iff] at hu
  exact eq_empty_iff_forall_notMem.1 hu
    ((GroupoidalCategory.translation ℤˣ (Fin 1 → ℝ)).π 0) (mem_univ _)

end Empty

/-! ### Remark 19.2.3: a basic construction whose `T` is not Hausdorff -/

section Glued

open EpGroupoid.Examples

/-- A morphism of `gluedLines`: `(x, a, k) : (x, a) → (x, k a)`, with `k = 1` or `x > 0`. -/
@[ext]
structure GluedMor : Type where
  /-- The point `x`. -/
  x : Fin 1 → ℝ
  /-- The sheet `a` of the source. -/
  a : ℤˣ
  /-- `k = 1` (the unit) or `k = −1` (a change of sheet). -/
  k : ℤˣ
  valid : k = 1 ∨ 0 < x 0

theorem GluedMor.k_eq_one (m : GluedMor) (h : ¬ 0 < m.x 0) : m.k = 1 := m.valid.resolve_right h

/-- The groupoid of Remark 19.2.3 on `ℝ × {±1}`. -/
def gluedStr : GroupoidStr ((Fin 1 → ℝ) × ℤˣ) GluedMor where
  src m := (m.x, m.a)
  tgt m := (m.x, m.k * m.a)
  comp φ ψ := ⟨ψ.x, ψ.a, if 0 < ψ.x 0 then φ.k * ψ.k else 1, by
    split_ifs with h
    · exact Or.inr h
    · exact Or.inl rfl⟩
  unit y := ⟨y.1, y.2, 1, Or.inl rfl⟩
  inv φ := ⟨φ.x, φ.k * φ.a, φ.k⁻¹, φ.valid.imp (fun h => by rw [h, inv_one]) id⟩
  src_comp _ _ _ := rfl
  tgt_comp φ ψ h := by
    have hx : φ.x = ψ.x := congrArg Prod.fst h
    have ha : φ.a = ψ.k * ψ.a := congrArg Prod.snd h
    change (ψ.x, (if 0 < ψ.x 0 then φ.k * ψ.k else 1) * ψ.a) = (φ.x, φ.k * φ.a)
    rw [hx, ha]
    split_ifs with hp
    · rw [mul_assoc]
    · rw [ψ.k_eq_one hp, φ.k_eq_one (by rwa [hx])]
      simp only [one_mul]
  comp_assoc φ ψ χ _ h₂ := by
    have hx : ψ.x = χ.x := congrArg Prod.fst h₂
    refine GluedMor.ext rfl rfl ?_
    change (if 0 < χ.x 0 then (if 0 < ψ.x 0 then φ.k * ψ.k else 1) * χ.k else 1) =
      if 0 < χ.x 0 then φ.k * (if 0 < χ.x 0 then ψ.k * χ.k else 1) else 1
    rw [hx]
    split_ifs
    · rw [mul_assoc]
    · rfl
  src_unit _ := rfl
  tgt_unit y := Prod.ext rfl (one_mul y.2)
  comp_unit φ := by
    refine GluedMor.ext rfl rfl ?_
    change (if 0 < φ.x 0 then φ.k * 1 else 1) = φ.k
    split_ifs with hp
    · rw [mul_one]
    · rw [φ.k_eq_one hp]
  unit_comp φ := by
    refine GluedMor.ext rfl rfl ?_
    change (if 0 < φ.x 0 then 1 * φ.k else 1) = φ.k
    split_ifs with hp
    · rw [one_mul]
    · rw [φ.k_eq_one hp]
  src_inv _ := rfl
  tgt_inv φ := Prod.ext rfl (inv_mul_cancel_left φ.k φ.a)
  comp_inv φ := by
    refine GluedMor.ext rfl rfl ?_
    change (if 0 < φ.x 0 then φ.k * φ.k⁻¹ else 1) = 1
    split_ifs
    · rw [mul_inv_cancel]
    · rfl
  inv_comp φ := by
    refine GluedMor.ext rfl rfl ?_
    change (if 0 < φ.x 0 then φ.k⁻¹ * φ.k else 1) = 1
    split_ifs
    · rw [inv_mul_cancel]
    · rfl

theorem gluedStr_k_comp {φ ψ : GluedMor} (h : gluedStr.src φ = gluedStr.tgt ψ) :
    (gluedStr.comp φ ψ).k = φ.k * ψ.k := by
  have hx : φ.x = ψ.x := congrArg Prod.fst h
  change (if 0 < ψ.x 0 then φ.k * ψ.k else 1) = φ.k * ψ.k
  split_ifs with hp
  · rfl
  · rw [ψ.k_eq_one hp, φ.k_eq_one (by rwa [hx]), one_mul]

/-- **The category of Remark 19.2.3**: objects `ℝ × {±1}`; `mor((x, a), (y, b))` is `{1}` for
`(x, a) = (y, b)`, `{φ_{(x,a),(x,b)}}` for `a b = −1` and `x > 0`, and empty otherwise. -/
abbrev gluedLines : GroupoidalCategory.{0} where
  Obj := (Fin 1 → ℝ) × ℤˣ
  Mor := GluedMor
  toGroupoidStr := gluedStr
  finite_mor α β := Set.Subsingleton.finite fun φ hφ ψ hψ => by
    have hs : (φ.x, φ.a) = (ψ.x, ψ.a) := hφ.1.trans hψ.1.symm
    have ht : (φ.x, φ.k * φ.a) = (ψ.x, ψ.k * ψ.a) := hφ.2.trans hψ.2.symm
    have hx : φ.x = ψ.x := congrArg Prod.fst hs
    have ha : φ.a = ψ.a := congrArg Prod.snd hs
    have hk : φ.k * φ.a = ψ.k * ψ.a := congrArg Prod.snd ht
    rw [ha] at hk
    exact GluedMor.ext hx ha (mul_right_cancel hk)

/-- `|(x, a)| = |(y, b)|` iff `x = y` and (`a = b` or `x > 0`). -/
theorem gluedLines_π_eq_iff {x y : Fin 1 → ℝ} {a b : ℤˣ} :
    gluedLines.π (x, a) = gluedLines.π (y, b) ↔ x = y ∧ (a = b ∨ 0 < x 0) := by
  rw [π_eq_π_iff]
  constructor
  · rintro ⟨φ, hs, ht⟩
    have hx : φ.x = x := congrArg Prod.fst hs
    have ha : φ.a = a := congrArg Prod.snd hs
    have hy : φ.x = y := congrArg Prod.fst ht
    have hb : φ.k * φ.a = b := congrArg Prod.snd ht
    refine ⟨hx.symm.trans hy, φ.valid.imp (fun hk => ?_) (fun h => hx ▸ h)⟩
    rw [← hb, ← ha, hk, one_mul]
  · rintro ⟨rfl, h | h⟩
    · subst h
      exact gluedLines.toGroupoidStr.isomorphic_refl _
    · exact ⟨⟨x, a, b * a⁻¹, Or.inr h⟩, rfl, Prod.ext rfl (inv_mul_cancel_right b a)⟩

/-- `|(0, −1)| ≠ |(0, 1)|`. -/
theorem gluedLines_π_ne : gluedLines.π (0, -1) ≠ gluedLines.π (0, 1) := by
  rw [Ne, gluedLines_π_eq_iff]
  rintro ⟨-, h | h⟩
  · exact absurd h (by decide)
  · exact lt_irrefl _ h

/-- The trivial group `{1} ⊂ ℤˣ` acts trivially. -/
theorem gluedUnif_smul_eq (g : (⊥ : Subgroup ℤˣ)) (t : Fin 1 → ℝ) : g • t = t := by
  change (g : ℤˣ) • t = t
  rw [Subgroup.mem_bot.1 g.2, one_smul]

/-- **The uniformizer `Ψ_b(t) = (t, b)`** of Remark 19.2.3, with the trivial group. -/
def gluedUnif (b : ℤˣ) : gluedLines.Uniformizer where
  O := Fin 1 → ℝ
  P := rnPolyfold 1
  G := (⊥ : Subgroup ℤˣ)
  smooth_smul g := isScSmoothMap_units_smul (g : ℤˣ)
  functor :=
    { obj := fun t => (t, b)
      mor := fun p => ⟨p.2, b, 1, Or.inl rfl⟩
      src_mor := fun _ => rfl
      tgt_mor := fun p => Prod.ext (gluedUnif_smul_eq p.1 p.2).symm (one_mul b)
      mor_comp := fun φ ψ _ => by
        refine GluedMor.ext rfl rfl ?_
        change (1 : ℤˣ) = if 0 < ψ.2 0 then 1 * 1 else 1
        split_ifs <;> rfl
      mor_unit := fun _ => rfl }
  injective_obj _ _ h := congrArg Prod.fst h
  full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => by
    have hx : ψ.x = x := congrArg Prod.fst hs
    have ha : ψ.a = b := congrArg Prod.snd hs
    have hx' : ψ.x = x' := congrArg Prod.fst ht
    have hk : ψ.k * ψ.a = b := congrArg Prod.snd ht
    rw [ha] at hk
    have hk1 : ψ.k = 1 := mul_eq_right.1 hk
    refine ⟨(1, x), rfl, (one_smul _ x).trans (hx.symm.trans hx'), ?_⟩
    exact GluedMor.ext hx.symm ha.symm hk1.symm
  faithful := (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ _ =>
    Prod.ext (Subtype.ext ((Subgroup.mem_bot.1 φ.1.2).trans (Subgroup.mem_bot.1 φ'.1.2).symm)) hs

/-- **The uniformizer construction of Remark 19.2.3**: `F((x, a)) = {Ψ_a}`. -/
def gluedU : gluedLines.UniformizerConstruction where
  F α := {gluedUnif α.2}
  isAt α Ψ hΨ := by
    rw [mem_singleton_iff] at hΨ
    subst hΨ
    exact ⟨α.1, rfl⟩

theorem gluedU_mem {α : gluedLines.Obj} {Ψ : gluedLines.Uniformizer} (h : Ψ ∈ gluedU.F α) :
    Ψ = gluedUnif α.2 := h

theorem gluedU_unif (Ψ : gluedU.Unif) : ∃ a, Ψ.1 = gluedUnif a := by
  obtain ⟨_, α, h⟩ := Ψ
  exact ⟨α.2, h⟩

/-- Over `q`, `M(Ψ_a, Ψ_b)` has an element with key `k` iff `k a = b` and (`k = 1` or `q > 0`). -/
theorem glued_exists_iff (a b : ℤˣ) (q : Fin 1 → ℝ) (k : ℤˣ) :
    (∃ h' : (gluedUnif a).Trans (gluedUnif b), h'.src = q ∧ h'.mor.k = k) ↔
      k * a = b ∧ (k = 1 ∨ 0 < q 0) := by
  constructor
  · rintro ⟨h', rfl, rfl⟩
    have hx : h'.mor.x = h'.src := congrArg Prod.fst h'.src_mor
    have ha : h'.mor.a = a := congrArg Prod.snd h'.src_mor
    have hb : h'.mor.k * h'.mor.a = b := congrArg Prod.snd h'.tgt_mor
    rw [ha] at hb
    refine ⟨hb, ?_⟩
    rw [← hx]
    exact h'.mor.valid
  · rintro ⟨hb, hv⟩
    exact ⟨⟨q, ⟨q, a, k, hv⟩, q, rfl, Prod.ext rfl hb⟩, rfl, rfl⟩

theorem glued_trans_ext {a b : ℤˣ} (h₁ h₂ : (gluedUnif a).Trans (gluedUnif b))
    (hs : h₁.src = h₂.src) (hk : h₁.mor.k = h₂.mor.k) : h₁ = h₂ := by
  have x₁ : h₁.mor.x = h₁.src := congrArg Prod.fst h₁.src_mor
  have x₂ : h₂.mor.x = h₂.src := congrArg Prod.fst h₂.src_mor
  have a₁ : h₁.mor.a = a := congrArg Prod.snd h₁.src_mor
  have a₂ : h₂.mor.a = a := congrArg Prod.snd h₂.src_mor
  have t₁ : h₁.mor.x = h₁.tgt := congrArg Prod.fst h₁.tgt_mor
  have t₂ : h₂.mor.x = h₂.tgt := congrArg Prod.fst h₂.tgt_mor
  have hm : h₁.mor = h₂.mor := GluedMor.ext (by rw [x₁, x₂, hs]) (a₁.trans a₂.symm) hk
  exact TransitionSet.ext hs hm (by rw [← t₁, ← t₂, hm])

/-- The domain `D(h)` of the keyed transition data of Remark 19.2.3. -/
def gluedDom (Ψ Ψ' : gluedU.Unif) (h : Ψ.1.Trans Ψ'.1) : Set Ψ.1.O :=
  {q | ∃ h' : Ψ.1.Trans Ψ'.1, h'.src = q ∧ h'.mor.k = h.mor.k}

theorem isOpen_gluedDom (Ψ Ψ' : gluedU.Unif) (h : Ψ.1.Trans Ψ'.1) :
    IsOpen (gluedDom Ψ Ψ' h) := by
  obtain ⟨Ψ₁, hΨ₁⟩ := Ψ
  obtain ⟨Ψ₂, hΨ₂⟩ := Ψ'
  obtain ⟨a, rfl⟩ := gluedU_unif ⟨Ψ₁, hΨ₁⟩
  obtain ⟨b, rfl⟩ := gluedU_unif ⟨Ψ₂, hΨ₂⟩
  have hb := ((glued_exists_iff a b h.src h.mor.k).1 ⟨h, rfl, rfl⟩).1
  have he : gluedDom ⟨_, hΨ₁⟩ ⟨_, hΨ₂⟩ h =
      {_q : Fin 1 → ℝ | h.mor.k = 1} ∪ {q : Fin 1 → ℝ | 0 < q 0} := by
    ext q
    exact (glued_exists_iff a b q h.mor.k).trans ⟨fun h' => h'.2, fun h' => ⟨hb, h'⟩⟩
  rw [he]
  exact isOpen_const.union (isOpen_lt continuous_const (continuous_apply 0))

/-- **The transition data of Remark 19.2.3**: `F_h(q) = (q, φ_{(q,a),(q,b)}, q)`, defined for all
`q` if `a = b` and for `q > 0` if `a ≠ b`. -/
def gluedData : gluedU.TransitionData :=
  UniformizerConstruction.TransitionData.ofKey (U := gluedU) GluedMor.k gluedDom
    (fun Ψ Ψ' => by
      obtain ⟨Ψ₁, hΨ₁⟩ := Ψ
      obtain ⟨Ψ₂, hΨ₂⟩ := Ψ'
      obtain ⟨a, rfl⟩ := gluedU_unif ⟨Ψ₁, hΨ₁⟩
      obtain ⟨b, rfl⟩ := gluedU_unif ⟨Ψ₂, hΨ₂⟩
      exact glued_trans_ext)
    (fun _ _ _ _ => Iff.rfl) isOpen_gluedDom
    (fun Ψ Ψ' h => by
      obtain ⟨Ψ₁, hΨ₁⟩ := Ψ
      obtain ⟨Ψ₂, hΨ₂⟩ := Ψ'
      obtain ⟨a, rfl⟩ := gluedU_unif ⟨Ψ₁, hΨ₁⟩
      obtain ⟨b, rfl⟩ := gluedU_unif ⟨Ψ₂, hΨ₂⟩
      refine ⟨id, id, _, MPolyfold.isScDiffeoOn_id (isOpen_gluedDom ⟨_, hΨ₁⟩ ⟨_, hΨ₂⟩ h),
        fun h' _ => ?_⟩
      have x₁ : h'.mor.x = h'.src := congrArg Prod.fst h'.src_mor
      have t₁ : h'.mor.x = h'.tgt := congrArg Prod.fst h'.tgt_mor
      exact x₁.symm.trans t₁)
    (fun _ _ => rfl) (fun _ _ h => congrArg (·⁻¹) h)
    (fun _ _ _ _ h₁ h₂ e₁ e₂ => by rw [gluedStr_k_comp h₁, gluedStr_k_comp h₂, e₁, e₂])
    (fun Ψ g q q' => by
      obtain ⟨Ψ₁, hΨ₁⟩ := Ψ
      obtain ⟨a, rfl⟩ := gluedU_unif ⟨Ψ₁, hΨ₁⟩
      rfl)

/-- **The basic construction of Remark 19.2.3**. -/
def gluedBasic : gluedLines.BasicConstruction := ⟨gluedU, ⟦gluedData⟧⟩

theorem gluedBasic_hasUniformizers : gluedBasic.U.HasUniformizers := fun _ => ⟨_, rfl⟩

/-- Every `Ψ_a ∈ F((x, a))` is centred at `(x, a)` (the isotropy groups are trivial). -/
theorem gluedBasic_isCentred : gluedBasic.U.IsCentred := fun α Ψ hΨ => by
  rw [gluedU_mem hΨ]
  exact ⟨α.1, rfl, fun g => gluedUnif_smul_eq g α.1⟩

theorem gluedBasic_natOpen {W : Set gluedLines.OrbitSpace} (hW : gluedBasic.U.NatOpen W)
    {ε : ℤˣ} (hz : gluedLines.π (0, ε) ∈ W) :
    ∃ V : Set (Fin 1 → ℝ), IsOpen V ∧ (0 : Fin 1 → ℝ) ∈ V ∧ ∀ t ∈ V, gluedLines.π (t, ε) ∈ W := by
  obtain ⟨⟨x, a⟩, hα, Ψ, hΨ, o, ho, V, hV, hoV, hsub⟩ := hW _ hz
  have hΨ' := gluedU_mem hΨ
  subst hΨ'
  obtain ⟨hx, ha⟩ := gluedLines_π_eq_iff.1 hα
  subst hx
  have ha' : a = ε := ha.resolve_right (lt_irrefl _)
  subst ha'
  have ho' : o = (0 : Fin 1 → ℝ) := congrArg Prod.fst ho
  subst ho'
  exact ⟨V, hV, hoV, fun t ht => hsub ⟨t, ht, rfl⟩⟩

/-- **2021 Remark 19.2.3, p. 870**: the natural topology `T` of the basic construction
`gluedBasic` on `ℝ × {±1}` is not Hausdorff: `|(0, −1)| ≠ |(0, 1)|` have no disjoint
neighbourhoods. -/
theorem remark_19_2_3 :
    ¬ @T2Space _ (gluedBasic.natTop gluedBasic_hasUniformizers.hasClassUniformizers) := by
  intro hT
  let _inst := gluedBasic.natTop gluedBasic_hasUniformizers.hasClassUniformizers
  obtain ⟨W₁, W₂, h₁, h₂, hz₁, hz₂, hd⟩ := t2_separation gluedLines_π_ne
  obtain ⟨V₁, hV₁, h0₁, hs₁⟩ := gluedBasic_natOpen h₁ hz₁
  obtain ⟨V₂, hV₂, h0₂, hs₂⟩ := gluedBasic_natOpen h₂ hz₂
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hV₁.inter hV₂) 0 ⟨h0₁, h0₂⟩
  have ht : (fun _ => r / 2 : Fin 1 → ℝ) ∈ V₁ ∩ V₂ := hball (by
    rw [Metric.mem_ball, dist_zero_right, pi_norm_const, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    exact half_lt_self hr)
  have he : gluedLines.π ((fun _ => r / 2 : Fin 1 → ℝ), -1) =
      gluedLines.π ((fun _ => r / 2 : Fin 1 → ℝ), 1) :=
    gluedLines_π_eq_iff.2 ⟨rfl, Or.inr (half_pos hr)⟩
  exact Set.disjoint_left.1 hd (hs₁ _ ht.1) (he ▸ hs₂ _ ht.2)

end Glued

end GroupoidalCategory

end Polyfold
