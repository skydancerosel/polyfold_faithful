import Polyfold.Chapter10.LocalizationLRCounterexample
import Polyfold.Chapter11.EpEquivalenceGeometryFaces
import Polyfold.Chapter7.SmoothRegularAssembly

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.1 (pp. 705–714; 2017: §16.1, pp. 539–548): **Definitions 16.1.1, 16.1.2, 16.1.3, Lemma 16.1.13,
Definitions 16.1.14, 16.1.17, Lemma 16.1.19, Definition 16.1.20**, and the uniqueness claim
after Definition 16.1.2 for an effective target.  Numbers and pages are the 2021 text's.

# Polyfold structures

## The text, paraphrased

(Definition 16.1.1, p. 705) A polyfold structure on a topological space `Z` is a pair `(X, β)`:
an ep-groupoid `X` with paracompact orbit space `|X|` satisfying (ZHOU) (Definition 7.4.5), and a
homeomorphism `β : |X| → Z`.  (Definition 16.1.2, p. 707) `(X, α)` and `(Y, β)` are equivalent if
a generalized isomorphism `f : X → Y` has `α = β ∘ |f|`; the text adds that `f` is unique by
(ZHOU).  (Definition 16.1.3) A polyfold is `Z` with an equivalence class `c` of polyfold
structures.  (p. 712) `d_{(X,β)}(z) = d_X(x)` for `β(|x|) = z`; (Lemma 16.1.13) equivalent
structures give the same function; (Definition 16.1.14) hence `d_Z`.  (Definition 16.1.17)
`∂Z = {z | d_Z(z) ≥ 1}`.  (Lemma 16.1.19) For equivalent structures, `X` tame implies `Y` tame;
(Definition 16.1.20) a polyfold is tame if one (then every) structure of `c` is tame.

## What is formalized (namespace `Polyfold.PolyfoldStructure`)

* `PolyfoldStructure Z` (**Definition 16.1.1**), with `toOrbitChart` (the pair of Remark 10.3.18).
* `PolyfoldStructure.Equiv` (**Definition 16.1.2**), an equivalence relation
  (`equiv_iff_rel`, `Equiv.refl/symm/trans`, `setoid`); `orbitMap_eq_of_equiv` (`|f| = β⁻¹ ∘ α`).
* `PolyfoldClass Z` (**Definition 16.1.3**), the quotient.
* `degIndex`, `degIndex_eq` (the definition on p. 712, independent of `x`), `lemma_16_1_13`;
  `PolyfoldClass.degIndex` and `definition_16_1_14` (**Definition 16.1.14**).
* `PolyfoldClass.boundary` (**Definition 16.1.17**).
* `lemma_16_1_19` (**Lemma 16.1.19**, as an `↔`), `PolyfoldClass.IsTame` and
  `definition_16_1_20` (**Definition 16.1.20**: one structure tame iff every structure tame).
* `uniqueness_16_1_2_of_isEffective` and `remark_16_1_7_of_isEffective`: the uniqueness after
  Definition 16.1.2 and in Remark 16.1.7 holds when the target ep-groupoid is effective.  Without
  effectiveness it does not hold as we read it (`ZhouUniquenessCheck.lean`).

## Readings

* `Z` lives in the universe of the object and morphism sets of `X` (as `OrbitChart`).
* "Unique as a consequence of (ZHOU)" rests on Theorem 10.3.19 (`not_theorem_10_3_19`).  The
  trivial `ℤ/3`-action on `ℝ` satisfies (ZHOU) (`Examples.isZhou_trivialZ3`), so the uniqueness
  claim does not hold as we read it; see `ZhouUniquenessCheck.lean`.  (ZHOU) gives (LR)
  (`proposition_7_4_22_of_isZhou`), so Theorem 10.3.19 for an effective target applies.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization

/-- **2021 Definition 16.1.1, p. 705 (2017: Definition 16.1)**: a **polyfold structure** on the
topological space `Z`: an ep-groupoid `X` with (1) paracompact orbit space, (2) the Zhou condition
(Definition 7.4.5), and (3) a homeomorphism `β : |X| → Z`. -/
structure PolyfoldStructure (Z : Type u) [TopologicalSpace Z] : Type (u + 1) where
  /-- The ep-groupoid. -/
  X : EP.{u}
  /-- (1) `|X|` is paracompact. -/
  paracompact : X.X.HasParacompactOrbitSpace
  /-- (2) `X` satisfies (ZHOU). -/
  isZhou : X.X.IsZhou
  /-- (3) The homeomorphism `β : |X| → Z`. -/
  β : X.X.OrbitSpace ≃ₜ Z

namespace PolyfoldStructure

variable {Z : Type u} [TopologicalSpace Z]

/-- The underlying pair `(X, β)` of Remark 10.3.18. -/
def toOrbitChart (p : PolyfoldStructure Z) : OrbitChart Z := ⟨p.X, p.β⟩

/-- `X` has (LR) (Proposition 7.4.22 from (ZHOU)). -/
theorem isLR (p : PolyfoldStructure Z) : p.X.X.IsLR :=
  p.X.X.proposition_7_4_22_of_isZhou p.isZhou

/-- **2021 Definition 16.1.2, p. 707 (2017: Definition 16.2)**: `(X, α)` and `(Y, β)` are
**equivalent** if some generalized isomorphism `f : X → Y` has `α = β ∘ |f|`. -/
def Equiv (p q : PolyfoldStructure Z) : Prop :=
  ∃ f : EPLoc.of p.X ⟶ EPLoc.of q.X, EPLoc.IsGeneralizedIso f ∧
    ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap f

theorem equiv_iff_rel {p q : PolyfoldStructure Z} :
    Equiv p q ↔ OrbitChart.Rel p.toOrbitChart q.toOrbitChart :=
  exists_congr fun _ => and_congr_right fun _ => eq_comm

theorem Equiv.refl (p : PolyfoldStructure Z) : Equiv p p :=
  equiv_iff_rel.2 (OrbitChart.Rel.refl _)

theorem Equiv.symm {p q : PolyfoldStructure Z} (h : Equiv p q) : Equiv q p :=
  equiv_iff_rel.2 (equiv_iff_rel.1 h).symm

theorem Equiv.trans {p q r : PolyfoldStructure Z} (h : Equiv p q) (h' : Equiv q r) :
    Equiv p r :=
  equiv_iff_rel.2 ((equiv_iff_rel.1 h).trans (equiv_iff_rel.1 h'))

/-- **Definition 16.1.2**: equivalence of polyfold structures is an equivalence relation. -/
instance setoid (Z : Type u) [TopologicalSpace Z] : Setoid (PolyfoldStructure Z) where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

theorem equiv_iff {p q : PolyfoldStructure Z} : p ≈ q ↔ Equiv p q := Iff.rfl

/-- The orbit map of an `f` as in Definition 16.1.2 is `β⁻¹ ∘ α` (2021 p. 708). -/
theorem orbitMap_eq_of_equiv {p q : PolyfoldStructure Z} {f : EPLoc.of p.X ⟶ EPLoc.of q.X}
    (h : ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap f) : EPLoc.orbitMap f = ⇑q.β.symm ∘ ⇑p.β := by
  rw [h, ← Function.comp_assoc, q.β.symm_comp_self, Function.id_comp]

/-- **The uniqueness after 2021 Definition 16.1.2 (p. 707; 2017: Definition 16.2), for an
effective target**: if `Y` is effective, at most one generalized isomorphism `f : X → Y` has
`α = β ∘ |f|` (Theorem 10.3.19 for an effective target; (ZHOU) gives (LR)).  Without
effectiveness it does not hold as we read it: `not_uniqueness_16_1_2`. -/
theorem uniqueness_16_1_2_of_isEffective {p q : PolyfoldStructure Z} (hq : q.X.X.IsEffective)
    {f f' : EPLoc.of p.X ⟶ EPLoc.of q.X} (hf : EPLoc.IsGeneralizedIso f)
    (hf' : EPLoc.IsGeneralizedIso f') (h : ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap f)
    (h' : ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap f') : f = f' :=
  EPLoc.theorem_10_3_19_of_isEffective hq (Or.inl p.isLR) hf hf'
    ((orbitMap_eq_of_equiv h).trans (orbitMap_eq_of_equiv h').symm)

/-- **2021 Remark 16.1.7, p. 711 (2017: Remark 16.1), for an effective target**: for a
homeomorphism `h : Z → W` and polyfold structures `(X, α)` on `Z`, `(Y, β)` on `W` with `Y`
effective, at most one generalized isomorphism `f : X → Y` has `h ∘ α = β ∘ |f|`.  Without
effectiveness it does not hold as we read it: `not_remark_16_1_7`. -/
theorem remark_16_1_7_of_isEffective {W : Type u} [TopologicalSpace W] (k : Z ≃ₜ W)
    {p : PolyfoldStructure Z} {q : PolyfoldStructure W} (hq : q.X.X.IsEffective)
    {f f' : EPLoc.of p.X ⟶ EPLoc.of q.X} (hf : EPLoc.IsGeneralizedIso f)
    (hf' : EPLoc.IsGeneralizedIso f') (h : ⇑k ∘ ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap f)
    (h' : ⇑k ∘ ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap f') : f = f' := by
  refine EPLoc.theorem_10_3_19_of_isEffective hq (Or.inl p.isLR) hf hf' ?_
  have e : ∀ g : EPLoc.of p.X ⟶ EPLoc.of q.X, ⇑k ∘ ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap g →
      EPLoc.orbitMap g = ⇑q.β.symm ∘ ⇑k ∘ ⇑p.β := fun g hg => by
    rw [hg, ← Function.comp_assoc, q.β.symm_comp_self, Function.id_comp]
  rw [e f h, e f' h']

/-! ### The degeneracy index (p. 712, Lemma 16.1.13) -/

/-- The degeneracy index `d_{(X,β)} : Z → ℕ`, `d_{(X,β)}(z) = d_X(x)` for `β(|x|) = z`
(2021 p. 712), i.e. `d_{|X|} ∘ β⁻¹`. -/
def degIndex (p : PolyfoldStructure Z) (z : Z) : ℕ := p.X.X.degIndexOrbit (p.β.symm z)

/-- `d_{(X,β)}(z) = d_X(x)` for every `x` with `β(|x|) = z` (the choice of `x` does not matter). -/
theorem degIndex_eq (p : PolyfoldStructure Z) {x : p.X.Obj} {z : Z} (h : p.β (p.X.X.π x) = z) :
    p.degIndex z = p.X.X.PObj.degIndex x := by
  rw [degIndex, ← h, Homeomorph.symm_apply_apply, EpGroupoid.degIndexOrbit_π]

/-- **2021 Lemma 16.1.13, p. 712 (2017: Lemma 16.1)**: equivalent polyfold structures have the
same degeneracy index. -/
theorem lemma_16_1_13 {p q : PolyfoldStructure Z} (h : Equiv p q) : p.degIndex = q.degIndex := by
  obtain ⟨f, hf, hβ⟩ := h
  funext z
  have e : q.β.symm z = EPLoc.orbitMap f (p.β.symm z) := by
    rw [orbitMap_eq_of_equiv hβ, Function.comp_apply, Homeomorph.apply_symm_apply]
  rw [degIndex, degIndex, e, EPLoc.degIndexOrbit_orbitMap hf]

/-! ### Tameness (Lemma 16.1.19) -/

/-- **2021 Lemma 16.1.19, p. 714 (2017: Lemma 16.2)**: for equivalent polyfold structures
`(X, α)`, `(Y, β)`, `X` is tame iff `Y` is (the text: if `X` is tame, so is `Y`). -/
theorem lemma_16_1_19 {p q : PolyfoldStructure Z} (h : Equiv p q) :
    p.X.X.IsTame ↔ q.X.X.IsTame := by
  obtain ⟨f, hf, -⟩ := h
  exact EPLoc.iff_of_isGeneralizedIso (fun A => A.X.IsTame) (fun _ hF => hF.isTame_iff) hf

end PolyfoldStructure

/-! ### Definition 16.1.3: polyfolds -/

/-- **2021 Definition 16.1.3, p. 707 (2017: Definition 16.3)**: a **polyfold** `(Z, c)`: an
equivalence class `c` of polyfold structures on the topological space `Z`. -/
abbrev PolyfoldClass (Z : Type u) [TopologicalSpace Z] : Type (u + 1) :=
  Quotient (PolyfoldStructure.setoid Z)

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z]

/-- **2021 Definition 16.1.14, p. 712 (2017: Definition 16.9)**: the degeneracy index
`d_Z : Z → ℕ` of a polyfold (well defined by Lemma 16.1.13). -/
def degIndex (c : PolyfoldClass Z) : Z → ℕ :=
  Quotient.lift PolyfoldStructure.degIndex (fun _ _ h => PolyfoldStructure.lemma_16_1_13 h) c

@[simp] theorem degIndex_mk (p : PolyfoldStructure Z) : degIndex ⟦p⟧ = p.degIndex := rfl

/-- **2021 Definition 16.1.14**: `d_Z(z) = d_X(x)` for every structure `(X, β) ∈ c` and every `x`
with `β(|x|) = z`. -/
theorem definition_16_1_14 (c : PolyfoldClass Z) (p : PolyfoldStructure Z) (hp : ⟦p⟧ = c)
    {x : p.X.Obj} {z : Z} (h : p.β (p.X.X.π x) = z) : c.degIndex z = p.X.X.PObj.degIndex x := by
  rw [← hp, degIndex_mk, p.degIndex_eq h]

/-- **2021 Definition 16.1.17, p. 713 (2017: Definition 16.11)**: the boundary
`∂Z = {z | d_Z(z) ≥ 1}`. -/
def boundary (c : PolyfoldClass Z) : Set Z := {z | 1 ≤ c.degIndex z}

theorem mem_boundary_iff (c : PolyfoldClass Z) (p : PolyfoldStructure Z) (hp : ⟦p⟧ = c)
    {x : p.X.Obj} {z : Z} (h : p.β (p.X.X.π x) = z) :
    z ∈ c.boundary ↔ 1 ≤ p.X.X.PObj.degIndex x := by
  change 1 ≤ c.degIndex z ↔ _
  rw [c.definition_16_1_14 p hp h]

/-- **2021 Definition 16.1.20, p. 714 (2017: Definition 16.12)**: the polyfold `(Z, c)` is
**tame** if some structure `(X, β) ∈ c` has `X` tame. -/
def IsTame (c : PolyfoldClass Z) : Prop := ∃ p : PolyfoldStructure Z, ⟦p⟧ = c ∧ p.X.X.IsTame

/-- **Definition 16.1.20**, "(and then all)": `(Z, c)` is tame iff every `(X, β) ∈ c` has `X`
tame (Lemma 16.1.19). -/
theorem definition_16_1_20 (c : PolyfoldClass Z) :
    c.IsTame ↔ ∀ p : PolyfoldStructure Z, ⟦p⟧ = c → p.X.X.IsTame := by
  refine ⟨fun ⟨p, hp, hX⟩ q hq => ?_, fun h => ?_⟩
  · exact (PolyfoldStructure.lemma_16_1_19 (Quotient.exact (hp.trans hq.symm))).1 hX
  · obtain ⟨p, rfl⟩ := Quotient.exists_rep c
    exact ⟨p, rfl, h p rfl⟩

end PolyfoldClass

end Polyfold
