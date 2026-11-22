import Polyfold.Chapter17.ProperCoveringModel
import Polyfold.Chapter17.GroupoidalCategory

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8:
**Definition 17.8.1** (p. 828, proper covering functor of GCTs).  Numbers and pages are the 2021
text's.

# Proper covering functors of GCTs

## The text, paraphrased

(Definition 17.8.1) A functor `P : A → B` between GCTs is a proper covering functor of GCTs if
(1) `|P| : |A| → |B|` is continuous and surjective; (2) `P` is finite-to-one and surjective on
objects; (3) for every `z ∈ |B|` and `{y₁, …, y_k} = |P|⁻¹(z)` there are an open neighbourhood
`U(z)` and mutually disjoint open neighbourhoods `U(yᵢ)` with `|P|⁻¹(U(z)) = ⊔ U(yᵢ)`; (4) the
map `𝐀 → 𝐁 ₛ×_P A`, `φ ↦ (P(φ), s(φ))`, is a bijection.

## What is formalized

* **`GroupoidFunctor.IsProperCoveringGCT`** (Definition 17.8.1), with `fibredMor` (the map of (4)).
* `sheetOrbit` (`|(s, o)| ↦ s` for `G` acting trivially on `S`), `continuous_sheetOrbit`.
* **`isProperCoveringGCT_sheet`**: the sheet functor `G ⋉ (S × O) → G ⋉ O` (`sheetFunctor`) of a
  finite nonempty `S` with trivial `G`-action is a proper covering functor of GCTs.
* Witness: `isProperCoveringGCT_reflectionSheets`, two copies of `ℤˣ ⋉ ℝ` (`±1` acting) over
  `ℤˣ ⋉ ℝ`, with `|P|⁻¹(|1|)` of two points (`ncard_orbitFiber_reflectionSheets`).

## Readings

* **Finiteness in (3).**  `{y₁, …, y_k} = |P|⁻¹(z)` is a finite set; we include
  `(|P|⁻¹(z)).Finite` in (3).
* **(4)** is the map into Part I's fibred product `{(ψ, x) | s(ψ) = P(x)}`.
* "Mutually disjoint" is pairwise disjointness of `y ↦ U(y)` on `|P|⁻¹(z)`; `U(y)` need not be
  connected, and nothing asks `|P| : U(yᵢ) → U(z)` to be a homeomorphism (the text notes this holds
  "in all interesting cases").
-/

open Set Function Topology

noncomputable section

universe u

namespace Polyfold

/-! ### Definition 17.8.1 -/

namespace GroupoidFunctor

variable {A B : GCT.{u}}

/-- The map `𝐀 → 𝐁 ₛ×_P A`, `φ ↦ (P(φ), s(φ))`, of Definition 17.8.1 (4). -/
def fibredMor (F : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr) (φ : A.Mor) :
    {p : B.Mor × A.Obj // B.toGroupoidStr.src p.1 = F.obj p.2} :=
  ⟨(F.mor φ, A.toGroupoidStr.src φ), F.src_mor φ⟩

/-- **Definition 17.8.1 (proper covering functor of GCTs)**, p. 828: (1) `|P|` is continuous and
surjective; (2) `P` is finite-to-one and surjective on objects; (3) every `z ∈ |B|` has an open
neighbourhood `U(z)` with `|P|⁻¹(U(z))` the disjoint union of open neighbourhoods `U(y)` of the
finitely many `y ∈ |P|⁻¹(z)`; (4) `φ ↦ (P(φ), s(φ))` is a bijection `𝐀 → 𝐁 ₛ×_P A`. -/
structure IsProperCoveringGCT (F : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr) : Prop where
  continuous_orbitMap : Continuous F.orbitMap
  surjective_orbitMap : Surjective F.orbitMap
  finite_fiber : ∀ β : B.Obj, (F.obj ⁻¹' {β}).Finite
  surjective_obj : Surjective F.obj
  evenlyCovered : ∀ z : B.OrbitSpace, (F.orbitMap ⁻¹' {z}).Finite ∧
    ∃ (Uz : Set B.OrbitSpace) (V : A.OrbitSpace → Set A.OrbitSpace), IsOpen Uz ∧ z ∈ Uz ∧
      (∀ y ∈ F.orbitMap ⁻¹' {z}, IsOpen (V y) ∧ y ∈ V y) ∧
      (F.orbitMap ⁻¹' {z}).PairwiseDisjoint V ∧
      F.orbitMap ⁻¹' Uz = ⋃ y ∈ F.orbitMap ⁻¹' {z}, V y
  bijective_fibredMor : Bijective F.fibredMor

end GroupoidFunctor

/-! ### The sheet functor with trivial action on the sheets -/

section Sheet

open EpGroupoid EpGroupoid.Examples

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {P : MPolyfold O} (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y)
  (S : Type u) [TopologicalSpace S] [DiscreteTopology S] [MulAction G S]
  [ParacompactSpace (S × O)]

/-- The GCT `G ⋉ (S × O)`. -/
abbrev sheetGCT : GCT.{u} := GCT.translation G (S × O) (isScSmoothMap_sheet_smul' hP S)

/-- The sheet functor `G ⋉ (S × O) → G ⋉ O`, `(s, o) ↦ o`, as a functor of GCTs. -/
abbrev sheetGCTFunctor :
    GroupoidFunctor (sheetGCT hP S).toGroupoidStr (GCT.translation G O hP).toGroupoidStr :=
  (sheetFunctor hP S).toGroupoidFunctor

variable {S}

/-- `|(s, o)| ↦ s`, for `G` acting trivially on `S`. -/
def sheetOrbit (htriv : ∀ (g : G) (s : S), g • s = s) : (sheetGCT hP S).OrbitSpace → S :=
  Quotient.lift (fun p : S × O => p.1) fun _ _ ⟨φ, ha, hb⟩ => by
    rw [← ha, ← hb]
    exact (htriv φ.1 φ.2.1).symm

theorem continuous_sheetOrbit (htriv : ∀ (g : G) (s : S), g • s = s) :
    Continuous (sheetOrbit hP htriv) :=
  continuous_fst.quotient_lift _

theorem sheetOrbit_π (htriv : ∀ (g : G) (s : S), g • s = s) (p : S × O) :
    sheetOrbit hP htriv ((sheetGCT hP S).π p) = p.1 := rfl

/-- Over `|x|`, the orbit `|(s, o)|` is `|(s, x)|`. -/
theorem π_eq_of_orbitMap (htriv : ∀ (g : G) (s : S), g • s = s) {p : S × O} {x : O}
    (h : (sheetGCTFunctor hP S).orbitMap ((sheetGCT hP S).π p) = (GCT.translation G O hP).π x) :
    (sheetGCT hP S).π p = (sheetGCT hP S).π (p.1, x) := by
  obtain ⟨⟨g, o⟩, hs, ht⟩ := (GCT.translation G O hP).π_eq_π_iff.1 h
  change o = p.2 at hs
  change g • o = x at ht
  subst hs ht
  refine (sheetGCT hP S).π_eq_π_iff.2 ⟨(g, p), rfl, ?_⟩
  change (g • p.1, g • p.2) = (p.1, g • p.2)
  rw [htriv]

/-- **The sheet functor of a finite nonempty `S` with trivial `G`-action is a proper covering
functor of GCTs** (Definition 17.8.1). -/
theorem isProperCoveringGCT_sheet [Finite S] [Nonempty S] (htriv : ∀ (g : G) (s : S), g • s = s) :
    (sheetGCTFunctor hP S).IsProperCoveringGCT where
  continuous_orbitMap := (continuous_quot_mk.comp continuous_snd).quotient_lift _
  surjective_orbitMap z := by
    obtain ⟨x, rfl⟩ : ∃ x, (GCT.translation G O hP).π x = z := Quotient.exists_rep z
    exact ⟨(sheetGCT hP S).π (Classical.arbitrary S, x), rfl⟩
  finite_fiber x := (finite_range fun s : S => (s, x)).subset fun p hp =>
    ⟨p.1, Prod.ext rfl (show x = p.2 from (hp : p.2 = x).symm)⟩
  surjective_obj x := ⟨(Classical.arbitrary S, x), rfl⟩
  evenlyCovered z := by
    obtain ⟨x, rfl⟩ : ∃ x, (GCT.translation G O hP).π x = z := Quotient.exists_rep z
    have hfib : ∀ y ∈ (sheetGCTFunctor hP S).orbitMap ⁻¹' {(GCT.translation G O hP).π x},
        y = (sheetGCT hP S).π (sheetOrbit hP htriv y, x) := by
      intro y hy
      obtain ⟨p, rfl⟩ : ∃ p, (sheetGCT hP S).π p = y := Quotient.exists_rep y
      exact π_eq_of_orbitMap hP htriv hy
    refine ⟨(finite_range fun s : S => (sheetGCT hP S).π (s, x)).subset fun y hy =>
      ⟨_, (hfib y hy).symm⟩, univ, fun y => sheetOrbit hP htriv ⁻¹' {sheetOrbit hP htriv y},
      isOpen_univ, mem_univ _, fun y _ => ⟨(isOpen_discrete _).preimage
        (continuous_sheetOrbit hP htriv), rfl⟩, fun y hy y' hy' hne => ?_, ?_⟩
    · refine Set.disjoint_left.2 fun w hw hw' => hne ?_
      rw [hfib y hy, hfib y' hy', ← (hw : _ = _), ← (hw' : _ = _)]
    · rw [preimage_univ]
      refine (eq_univ_of_forall fun w => ?_).symm
      obtain ⟨p, rfl⟩ : ∃ p, (sheetGCT hP S).π p = w := Quotient.exists_rep w
      simp only [mem_iUnion, exists_prop]
      exact ⟨(sheetGCT hP S).π (p.1, x), rfl, rfl⟩
  bijective_fibredMor := by
    refine ⟨fun φ ψ h => ?_, fun q => ⟨(q.1.1.1, q.1.2), Subtype.ext ?_⟩⟩
    · have h1 := congrArg (fun q => q.1.1.1) h
      have h2 := congrArg (fun q => q.1.2) h
      exact Prod.ext h1 h2
    · obtain ⟨⟨⟨g, o⟩, p⟩, hq⟩ := q
      change o = p.2 at hq
      subst hq
      rfl

end Sheet

/-! ### Witness: two copies of `ℤˣ ⋉ ℝ` over `ℤˣ ⋉ ℝ` -/

section Witness

open EpGroupoid.Examples

/-- `ℤˣ` acting trivially on the two sheets `Bool`. -/
local instance instMulActionUnitsBool : MulAction ℤˣ Bool where
  smul _ b := b
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- **Two copies of `ℤˣ ⋉ ℝ` over `ℤˣ ⋉ ℝ` form a proper covering functor of GCTs**; `-1 ∈ ℤˣ`
acts nontrivially on `ℝ`. -/
theorem isProperCoveringGCT_reflectionSheets :
    (sheetGCTFunctor isScSmoothMap_units_smul Bool).IsProperCoveringGCT :=
  isProperCoveringGCT_sheet isScSmoothMap_units_smul fun _ _ => rfl

/-- The fibre `|P|⁻¹(|1|)` has two points: the covering has two sheets. -/
theorem ncard_orbitFiber_reflectionSheets :
    ((sheetGCTFunctor isScSmoothMap_units_smul Bool).orbitMap ⁻¹'
      {(GCT.translation ℤˣ (Fin 1 → ℝ) isScSmoothMap_units_smul).π (fun _ => 1)}).ncard = 2 := by
  set x : Fin 1 → ℝ := fun _ => 1
  set C := sheetGCT isScSmoothMap_units_smul Bool
  have hne : C.π (true, x) ≠ C.π (false, x) := fun h => by
    have := congrArg (sheetOrbit isScSmoothMap_units_smul (fun (_ : ℤˣ) (_ : Bool) => rfl)) h
    exact Bool.noConfusion this
  have hfib : (sheetGCTFunctor isScSmoothMap_units_smul Bool).orbitMap ⁻¹'
      {(GCT.translation ℤˣ (Fin 1 → ℝ) isScSmoothMap_units_smul).π x} =
      {C.π (true, x), C.π (false, x)} := by
    ext y
    refine ⟨fun hy => ?_, ?_⟩
    · obtain ⟨p, rfl⟩ : ∃ p, C.π p = y := Quotient.exists_rep y
      rw [π_eq_of_orbitMap isScSmoothMap_units_smul (fun _ _ => rfl) hy]
      cases p.1
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rintro (rfl | rfl) <;> rfl
  rw [hfib, ncard_pair hne]

end Witness

end Polyfold
