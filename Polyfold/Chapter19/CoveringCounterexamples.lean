import Polyfold.Chapter19.CoveringOrbitTopology
import Polyfold.Chapter19.BasicConstructionExamples
import Polyfold.Chapter19.ProperCoveringModelExample
import Polyfold.Chapter17.OverlappingUniformizers

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19, §19.7
"Covering Constructions": **Proposition 19.7.18** (p. 919), **Corollary 19.7.20 (3)** (p. 922) and
**Theorem 19.7.25 (4b)** (p. 926) do not hold as we read them.  Numbers and pages are the 2021
text's.

# The absolute-value covering construction

## The example

`B = ℤ/2 ⋉ ℝ` (`ℤ/2 = ℤˣ` acting by reflection) and `A = ℤ/2 ⋉ (ℤˣ × ℝ)`,
`k (i, x) = (k i, k x)`, with `P : A → B`, `(i, x) ↦ x` (`absCovP`), a finite-to-one covering
functor (Definition 19.7.1).  The proper covering uniformizer construction `F̂` has one member in
every `F̂(β)` (`absCU β`), all built from Definition 17.8.4 sheet models
(`sheetModel`, Chapter 17):

* at `β = 0` the global model `ℤ/2 ⋉ (ℤˣ × ℝ) → ℤ/2 ⋉ ℝ` (the model `absP_properCoveringModel` of
  Chapter 19's example, on the slice `ℝ` with group `ℤ/2`), `ō = 0`;
* at `β > 0` (resp. `β < 0`) the model `{1} ⋉ (ℤˣ × (0, ∞)) → {1} ⋉ (0, ∞)` (resp. `(−∞, 0)`),
  `ō = β`.

The transition construction is keyed by the group element (`sliceData`, for every uniformizer
construction of a translation groupoid made of slices), so `(F̂, 𝓕)` is a basic construction for
`P` (Definition 19.7.11, `absBasic`).  It satisfies `HasClassUniformizers` and the compatibility
`IsCompatible` (`absBasic_isCompatible`), so the readings of Chapter 19's
`CoveringOrbitTopology.lean` apply and `natTopA` is defined (`absBasic_natTopA_eq`).  The natural
topologies are the orbit-space topologies: `T_{|A|}` is that of `|A| ≅ ℝ` (`isOpen_absTopA_iff`),
`T_{|B|}` that of `|B| ≅ [0, ∞)` (`absNatTopB_eq`), and `|P|` is `t ↦ |t|`.

## Statements

* `not_proposition_19_7_18`: `T_{|A|}` is a topology, and `|P| : (|A|, T_{|A|}) → (|B|, T_{|B|})`
  is not a local homeomorphism (`not_proposition_19_7_18_natTopA`: the same for `natTopA`);
  `not_proposition_19_7_18_of_continuous`: this holds for every topology on `|A|` making
  `e ↦ |Ψ̂(e)|` continuous for `Ψ̂ ∈ F̂(0)` (Lemma 19.7.17 (2)) and every topology on `|B|`.
* `not_corollary_19_7_20_three`: for `Ψ̂ ∈ F̂(0)`, every `a ∈ τ̂⁻¹(ō)` and every open `V ∋ a` of
  `E`, `|P|` is not injective on `|Ψ̂(V)|`, so not a homeomorphism `W(z̄₁) → W(z)` for any choice in
  Corollary 19.7.20.
* `not_theorem_19_7_25_four_b`: `T_{|B|}` is metrizable, `|P|⁻¹(|0|) = {|(1, 0)|}`, and `|P|` is
  not injective on any `T_{|A|}`-open neighbourhood of `|(1, 0)|`.

The point at issue is the fixed point `0` of `ℤ/2`: the isotropy `Aut(1, 0) = 1` of `A` does not map
onto `Aut(0) = ℤ/2`; the criterion `isLocalHomeomorphOn_orbitMap_of_isotropy_surjective`
(Chapter 19) and the parts `proposition_19_7_18_hyp` hold.
-/

open Set Function Topology TopologicalSpace Filter

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples GCT.PolyfoldConstruction

/-! ### Keyed transition data for slices of a translation groupoid -/

section SliceData

variable {K X : Type u} [Group K] [Finite K] [TopologicalSpace K] [DiscreteTopology K]
  [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [MulAction K X] {P : MPolyfold X}
  (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y)

/-- The uniformizer `H ⋉ V → K ⋉ X` of a slice, as a uniformizer of the translation groupoid. -/
abbrev sliceUniformizer (D : TranslationSlice K X) : (GroupoidalCategory.translation K
    X).Uniformizer :=
  (D.unif P hP).toUniformizer

/-- An element of `M(Ψ_D, Ψ_D')` is determined by its source and its group element. -/
theorem slice_trans_ext {D D' : TranslationSlice K X}
    (h₁ h₂ : (sliceUniformizer hP D).Trans (sliceUniformizer hP D')) (hs : h₁.src = h₂.src)
    (hk : h₁.mor.1 = h₂.mor.1) : h₁ = h₂ := by
  have a₁ : h₁.mor.2 = h₁.src.1 := h₁.src_mor
  have a₂ : h₂.mor.2 = h₂.src.1 := h₂.src_mor
  have hm : h₁.mor = h₂.mor := Prod.ext hk (by rw [a₁, a₂, hs])
  have b₁ : h₁.mor.1 • h₁.mor.2 = h₁.tgt.1 := h₁.tgt_mor
  have b₂ : h₂.mor.1 • h₂.mor.2 = h₂.tgt.1 := h₂.tgt_mor
  exact TransitionSet.ext hs hm (Subtype.ext (by rw [← b₁, ← b₂, hm]))

/-- The domain of the keyed transition: the `q` over which `M(Ψ, Ψ')` has an element with the
group element of `h`. -/
def keyDom {Ψ Ψ' : (GroupoidalCategory.translation K X).Uniformizer} (h : Ψ.Trans Ψ') : Set Ψ.O :=
  {q | ∃ h' : Ψ.Trans Ψ', h'.src = q ∧ h'.mor.1 = h.mor.1}

omit [Finite K] [TopologicalSpace K] [DiscreteTopology K] in
include hP in
theorem continuous_smul_of (k : K) : Continuous fun y : X => k • y :=
  continuousOn_univ.1 (hP k).continuousOn

theorem keyDom_slice {D D' : TranslationSlice K X}
    (h : (sliceUniformizer hP D).Trans (sliceUniformizer hP D')) :
    keyDom h = {q : D.V | h.mor.1 • q.1 ∈ D'.V} := by
  ext q
  constructor
  · rintro ⟨h', hs, hk⟩
    have a : h'.mor.2 = h'.src.1 := h'.src_mor
    have b : h'.mor.1 • h'.mor.2 = h'.tgt.1 := h'.tgt_mor
    change h.mor.1 • q.1 ∈ D'.V
    rw [← hk, ← hs, ← a, b]
    exact h'.tgt.2
  · intro hq
    exact ⟨⟨q, (h.mor.1, q.1), ⟨_, hq⟩, rfl, rfl⟩, rfl, rfl⟩

theorem isOpen_keyDom_slice {D D' : TranslationSlice K X}
    (h : (sliceUniformizer hP D).Trans (sliceUniformizer hP D')) : IsOpen (keyDom h) := by
  rw [keyDom_slice]
  exact D'.isOpen.preimage ((continuous_smul_of hP _).comp continuous_subtype_val)

open Classical in
/-- The transition map `q ↦ k ∗ q` between slices, `D(k) → D'`. -/
def sliceMap (D D' : TranslationSlice K X) (k : K) (q : D.V) : D'.V :=
  if hq : k • q.1 ∈ D'.V then ⟨_, hq⟩ else Classical.arbitrary D'.V

theorem sliceMap_val {D D' : TranslationSlice K X} {k : K} {q : D.V} (hq : k • q.1 ∈ D'.V) :
    (sliceMap D D' k q).1 = k • q.1 := by
  rw [sliceMap, dif_pos hq]

theorem slice_diffeo {D D' : TranslationSlice K X}
    (h : (sliceUniformizer hP D).Trans (sliceUniformizer hP D')) :
    ∃ (f : D.V → D'.V) (g : D'.V → D.V) (V : Set D'.V),
      (sliceUniformizer hP D).P.IsScDiffeoOn (sliceUniformizer hP D').P f g (keyDom h) V ∧
        ∀ h' : (sliceUniformizer hP D).Trans (sliceUniformizer hP D'), h'.mor.1 = h.mor.1 →
          f h'.src = h'.tgt := by
  have := D.paracompactSpace P
  have := D'.paracompactSpace P
  set k := h.mor.1
  have hsm : ∀ (E E' : TranslationSlice K X) (k : K), have := E.paracompactSpace P
      have := E'.paracompactSpace P
      (P.restrictOpen E.isOpen).IsScSmoothOn (P.restrictOpen E'.isOpen) (sliceMap E E' k)
        {q : E.V | k • q.1 ∈ E'.V} := by
    intro E E' k
    have := E.paracompactSpace P
    have := E'.paracompactSpace P
    have ho : IsOpen {q : E.V | k • q.1 ∈ E'.V} :=
      E'.isOpen.preimage ((continuous_smul_of hP _).comp continuous_subtype_val)
    refine (MPolyfold.isScSmoothOn_restrictOpen_iff E'.isOpen).2 ?_
    refine (MPolyfold.IsScSmoothOn.mono ((hP k).comp
      (MPolyfold.isScSmoothMap_subtypeVal E.isOpen)) ho (subset_univ _)).congr fun q hq => ?_
    exact (sliceMap_val hq).symm
  refine ⟨sliceMap D D' k, sliceMap D' D k⁻¹, {q' : D'.V | k⁻¹ • q'.1 ∈ D.V}, ?_, ?_⟩
  · rw [keyDom_slice]
    refine ⟨hsm D D' k, hsm D' D k⁻¹, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · change k⁻¹ • (sliceMap D D' k q).1 ∈ D.V
      rw [sliceMap_val hq, inv_smul_smul]
      exact q.2
    · change k • (sliceMap D' D k⁻¹ q).1 ∈ D'.V
      rw [sliceMap_val hq, smul_inv_smul]
      exact q.2
    · refine Subtype.ext ?_
      have h1 : k⁻¹ • (sliceMap D D' k q).1 ∈ D.V := by
        rw [sliceMap_val hq, inv_smul_smul]; exact q.2
      rw [sliceMap_val h1, sliceMap_val hq, inv_smul_smul]
    · refine Subtype.ext ?_
      have h1 : k • (sliceMap D' D k⁻¹ q).1 ∈ D'.V := by
        rw [sliceMap_val hq, smul_inv_smul]; exact q.2
      rw [sliceMap_val h1, sliceMap_val hq, smul_inv_smul]
  · intro h' hk
    have a : h'.mor.2 = h'.src.1 := h'.src_mor
    have b : h'.mor.1 • h'.mor.2 = h'.tgt.1 := h'.tgt_mor
    have hm : k • h'.src.1 = h'.tgt.1 := by rw [← hk, ← a, b]
    have hmem : k • h'.src.1 ∈ D'.V := hm ▸ h'.tgt.2
    exact Subtype.ext ((sliceMap_val hmem).trans hm)

variable {U : (GroupoidalCategory.translation K X).UniformizerConstruction}

/-- **Keyed transition data for a uniformizer construction made of slices** of `K ⋉ X`:
`F_h(q) = (q, k, k ∗ q)` for `h = (o, k, k ∗ o)` on `D(h) = {q | k ∗ q ∈ V'}`. -/
def sliceData (hU : ∀ Ψ : U.Unif, ∃ D : TranslationSlice K X, Ψ.1 = sliceUniformizer hP D) :
    U.TransitionData :=
  UniformizerConstruction.TransitionData.ofKey (U := U) (Prod.fst : K × X → K)
    (fun _ _ h => keyDom h)
    (fun Ψ Ψ' => by
      obtain ⟨Ψ₁, h₁⟩ := Ψ; obtain ⟨Ψ₂, h₂⟩ := Ψ'
      obtain ⟨D, rfl⟩ := hU ⟨Ψ₁, h₁⟩; obtain ⟨D', rfl⟩ := hU ⟨Ψ₂, h₂⟩
      exact slice_trans_ext hP)
    (fun _ _ _ _ => Iff.rfl)
    (fun Ψ Ψ' => by
      obtain ⟨Ψ₁, h₁⟩ := Ψ; obtain ⟨Ψ₂, h₂⟩ := Ψ'
      obtain ⟨D, rfl⟩ := hU ⟨Ψ₁, h₁⟩; obtain ⟨D', rfl⟩ := hU ⟨Ψ₂, h₂⟩
      exact isOpen_keyDom_slice hP)
    (fun Ψ Ψ' => by
      obtain ⟨Ψ₁, h₁⟩ := Ψ; obtain ⟨Ψ₂, h₂⟩ := Ψ'
      obtain ⟨D, rfl⟩ := hU ⟨Ψ₁, h₁⟩; obtain ⟨D', rfl⟩ := hU ⟨Ψ₂, h₂⟩
      exact slice_diffeo hP)
    (fun _ _ => rfl)
    (fun _ _ h => congrArg (·⁻¹) h)
    (fun _ _ _ _ _ _ h₁ h₂ => congrArg₂ (· * ·) h₁ h₂)
    (fun Ψ => by
      obtain ⟨Ψ₁, h₁⟩ := Ψ
      obtain ⟨D, rfl⟩ := hU ⟨Ψ₁, h₁⟩
      intro _ _ _; rfl)

/-- In `T^F_{Ψ,Ψ'}` for the keyed data, the elements with a given group element form an open set
(so `h ↦ k(h)` is locally constant). -/
theorem sliceData_isOpenTr_key
    (hU : ∀ Ψ : U.Unif, ∃ D : TranslationSlice K X, Ψ.1 = sliceUniformizer hP D)
    (Ψ Ψ' : U.Unif) (k : K) :
    (sliceData hP hU).IsOpenTr Ψ Ψ' {h | h.mor.1 = k} := by
  intro h hh
  refine ⟨keyDom h, (sliceData hP hU).isOpen_dom Ψ Ψ' h, ⟨h, rfl, rfl⟩, subset_rfl, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  have hq' : ∃ h' : Ψ.1.Trans Ψ'.1, h'.src = q ∧ h'.mor.1 = h.mor.1 := hq
  exact (keyMap_spec (C := GroupoidalCategory.translation K X) (Prod.fst : K × X → K)
    hq').2.trans hh

end SliceData

/-! ### Neighbourhoods in translation groupoids -/

/-- If `|S| ⊂ W` for an open `S ⊂ X` and `|y| = |a|` with `y ∈ S`, then `a` has an open
neighbourhood in `π⁻¹(W)` (a translate of `S`). -/
theorem exists_open_of_π_eq {K X : Type u} [Group K] [Finite K] [MulAction K X]
    [TopologicalSpace X] (hc : ∀ k : K, Continuous fun y : X => k • y) {S : Set X}
    (hS : IsOpen S) {W : Set (GroupoidalCategory.translation K X).OrbitSpace}
    (hSW : ∀ y ∈ S, (GroupoidalCategory.translation K X).π y ∈ W) {y a : X} (hy : y ∈ S)
    (hya : (GroupoidalCategory.translation K X).π y = (GroupoidalCategory.translation K X).π a) :
    ∃ N ⊆ (GroupoidalCategory.translation K X).π ⁻¹' W, IsOpen N ∧ a ∈ N := by
  obtain ⟨φ, hφs, hφt⟩ := (GroupoidalCategory.π_eq_π_iff _).1 hya
  have hs : φ.2 = y := hφs
  have ht : φ.1 • φ.2 = a := hφt
  refine ⟨(fun b => φ.1⁻¹ • b) ⁻¹' S, fun b hb => ?_, hS.preimage (hc _), ?_⟩
  · have h1 := hSW _ hb
    have h2 : (GroupoidalCategory.translation K X).π b =
        (GroupoidalCategory.translation K X).π (φ.1⁻¹ • b) :=
      (GroupoidalCategory.π_eq_π_iff _).2 ⟨(φ.1⁻¹, b), rfl, rfl⟩
    change (GroupoidalCategory.translation K X).π b ∈ W
    rw [h2]
    exact h1
  · change φ.1⁻¹ • a ∈ S
    rw [← ht, inv_smul_smul, hs]
    exact hy

/-! ### The example -/

section Example

open Chapter19

/-- **`A = ℤ/2 ⋉ (ℤˣ × ℝ)`**, `k (i, x) = (k i, k x)` (the groupoid of Chapter 19's `absA`). -/
abbrev absCatA : GroupoidalCategory.{0} := GroupoidalCategory.translation ℤˣ (ℤˣ × (Fin 1 → ℝ))

/-- **`B = ℤ/2 ⋉ ℝ`** by the reflection (the groupoid of `absB`). -/
abbrev absCatB : GroupoidalCategory.{0} := GroupoidalCategory.translation ℤˣ (Fin 1 → ℝ)

/-- **`P : A → B`**, `(i, x) ↦ x`, `(k, (i, x)) ↦ (k, x)` (the functor of `absP`). -/
def absCovP : GroupoidFunctor absCatA.toGroupoidStr absCatB.toGroupoidStr where
  obj := Prod.snd
  mor φ := (φ.1, φ.2.2)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl

/-- **`P` is a finite-to-one covering functor** (Definition 19.7.1): `P⁻¹(x) = ℤˣ × {x}`, and a
morphism `(k, x)` with `x = P(i, x)` lifts uniquely to `(k, (i, x))`. -/
theorem absCovP_isFiniteToOneCovering : IsFiniteToOneCovering absCovP where
  surjective x := ⟨(1, x), rfl⟩
  finite_fiber x := (Set.finite_univ.prod (Set.finite_singleton x)).subset fun _ ha =>
    ⟨mem_univ _, ha⟩
  bijective := by
    refine ⟨fun φ φ' h => ?_, fun q => ⟨(q.1.1.1, q.1.2), Subtype.ext
      (Prod.ext (Prod.ext rfl q.2.symm) rfl)⟩⟩
    have h' := congrArg Subtype.val h
    have h1 : φ.1 = φ'.1 := congrArg (fun p => p.1.1) h'
    have h2 : φ.2 = φ'.2 := congrArg (fun p => p.2) h'
    exact Prod.ext h1 h2

/-- The uniformizer `H ⋉ V → B` of a slice of `B`. -/
abbrev absSliceUnif (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) : absCatB.Uniformizer :=
  sliceUniformizer isScSmoothMap_units_smul D

instance absSliceUnif_mulAction (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) :
    MulAction (absSliceUnif D).G ℤˣ :=
  inferInstanceAs (MulAction D.H ℤˣ)

theorem absSliceUnif_metrizable (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) :
    MetrizableSpace (absSliceUnif D).O :=
  (absSliceUnif D).P.metrizableSpace

instance absSliceUnif_paracompact_obj (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) :
    ParacompactSpace (ℤˣ × (absSliceUnif D).O) := by
  have := absSliceUnif_metrizable D
  exact paracompactSpace_of_metrizableSpace _

instance absSliceUnif_paracompact_mor (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) :
    ParacompactSpace ((absSliceUnif D).G × (ℤˣ × (absSliceUnif D).O)) := by
  have := absSliceUnif_metrizable D
  exact paracompactSpace_of_metrizableSpace _

/-- **The proper covering uniformizer of a slice** (Definitions 19.7.3, 19.7.4): the sheet model
`τ̂ : H ⋉ (ℤˣ × V) → H ⋉ V` (Definition 17.8.4, `sheetModel`, `ō = β`) and
`Ψ̂ : H ⋉ (ℤˣ × V) → A`, `(i, v) ↦ (i, v)`, over the uniformizer `Ψ : H ⋉ V → B` of the slice. -/
def sliceCU (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) (β : Fin 1 → ℝ) (hβ : β ∈ D.V)
    (hfix : ∀ h ∈ D.H, h • β = β) : CoveringUniformizer absCovP β where
  Ψ := absSliceUnif D
  ObjE := ℤˣ × (absSliceUnif D).O
  MorE := (absSliceUnif D).G × (ℤˣ × (absSliceUnif D).O)
  E := sheetEp (absSliceUnif D).smooth_smul ℤˣ
  τ := sheetFunctor (absSliceUnif D).smooth_smul ℤˣ
  model := sheetModel (absSliceUnif D).smooth_smul ℤˣ (⟨β, hβ⟩ : D.V)
    fun g => Subtype.ext (hfix (g : D.H).1 (g : D.H).2)
  hat :=
    { obj := fun p => (p.1, (p.2 : D.V).1)
      mor := fun φ => ((φ.1 : D.H).1, (φ.2.1, (φ.2.2 : D.V).1))
      src_mor := fun _ => rfl
      tgt_mor := fun _ => rfl
      mor_comp := fun _ _ _ => rfl
      mor_unit := fun _ => rfl }
  obj_pt := rfl
  injective_hat p q h := by
    have h1 : p.1 = q.1 := congrArg (fun r => r.1) h
    have h2 : (p.2 : D.V).1 = (q.2 : D.V).1 := congrArg (fun r => r.2) h
    exact Prod.ext h1 (Subtype.ext h2)
  full_hat := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => by
    have hs' : ψ.2 = (x.1, (x.2 : D.V).1) := hs
    have ht' : ψ.1 • ψ.2 = (x'.1, (x'.2 : D.V).1) := ht
    rw [hs'] at ht'
    have h1 : ψ.1 * x.1 = x'.1 := congrArg Prod.fst ht'
    have h2 : ψ.1 • (x.2 : D.V).1 = (x'.2 : D.V).1 := congrArg Prod.snd ht'
    have hk : ψ.1 ∈ D.H := D.mem_of_smul_mem ψ.1 _ (x.2 : D.V).2 (h2 ▸ (x'.2 : D.V).2)
    refine ⟨((⟨ψ.1, hk⟩ : D.H), x), rfl, Prod.ext h1 (Subtype.ext h2), Prod.ext rfl hs'.symm⟩
  faithful_hat := (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ he =>
    Prod.ext (Subtype.ext (congrArg Prod.fst he)) hs
  obj_comm _ := rfl
  mor_comm _ := rfl
  cartesian_obj o a h := ⟨(a.1, o), rfl, Prod.ext rfl h.symm⟩
  cartesian_mor φ p h := by
    have h1 : φ.1 = (p.1 : D.H).1 := congrArg Prod.fst h
    have h2 : φ.2.2 = (p.2 : D.V).1 := congrArg Prod.snd h
    exact ⟨(p.1, (φ.2.1, p.2)), rfl, Prod.ext h1.symm (Prod.ext rfl h2.symm)⟩

theorem sliceCU_hat_obj (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) (β : Fin 1 → ℝ) (hβ : β ∈ D.V)
    (hfix : ∀ h ∈ D.H, h • β = β) (e : (sliceCU D β hβ hfix).ObjE) :
    (sliceCU D β hβ hfix).hat.obj e = (e.1, (e.2 : D.V).1) := rfl

/-- The slice `(0, ∞)` with the trivial group. -/
def posSlice : TranslationSlice ℤˣ (Fin 1 → ℝ) where
  V := {x | 0 < x 0}
  isOpen := isOpen_lt continuous_const (continuous_apply 0)
  nonempty := ⟨fun _ => 1, by norm_num⟩
  H := ⊥
  smul_mem h hh v hv := by
    rw [Subgroup.mem_bot.1 hh, one_smul]
    exact hv
  mem_of_smul_mem k v hv hkv := by
    rcases Int.units_eq_one_or k with rfl | rfl
    · exact Subgroup.one_mem _
    · exfalso
      have h1 : 0 < ((-1 : ℤˣ) • v) 0 := hkv
      rw [units_smul_rn_neg_one, Pi.neg_apply] at h1
      have h2 : 0 < v 0 := hv
      linarith

/-- The slice `(−∞, 0)` with the trivial group. -/
def negSlice : TranslationSlice ℤˣ (Fin 1 → ℝ) where
  V := {x | x 0 < 0}
  isOpen := isOpen_lt (continuous_apply 0) continuous_const
  nonempty := ⟨fun _ => -1, by norm_num⟩
  H := ⊥
  smul_mem h hh v hv := by
    rw [Subgroup.mem_bot.1 hh, one_smul]
    exact hv
  mem_of_smul_mem k v hv hkv := by
    rcases Int.units_eq_one_or k with rfl | rfl
    · exact Subgroup.one_mem _
    · exfalso
      have h1 : ((-1 : ℤˣ) • v) 0 < 0 := hkv
      rw [units_smul_rn_neg_one, Pi.neg_apply] at h1
      have h2 : v 0 < 0 := hv
      linarith

theorem zero_fix : ∀ h ∈ overlapSlice₀.H, h • (0 : Fin 1 → ℝ) = 0 := fun h _ => units_smul_zero_rn h

theorem bot_fix (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) (hD : D.H = ⊥) (β : Fin 1 → ℝ) :
    ∀ h ∈ D.H, h • β = β := fun h hh => by
  rw [hD, Subgroup.mem_bot] at hh
  rw [hh, one_smul]

open Classical in
/-- **The member of `F̂(β)`**: the global sheet model over `ℤ/2 ⋉ ℝ` at `β = 0`, the sheet model
over `{1} ⋉ (0, ∞)` or `{1} ⋉ (−∞, 0)` at `β > 0` or `β < 0`. -/
def absCU (β : Fin 1 → ℝ) : CoveringUniformizer absCovP β :=
  if h0 : β = 0 then h0 ▸ sliceCU overlapSlice₀ 0 (mem_univ _) zero_fix
  else if hp : 0 < β 0 then sliceCU posSlice β hp (bot_fix _ rfl β)
  else sliceCU negSlice β (lt_of_le_of_ne (not_lt.1 hp) fun h => h0 (fin_one_ext h))
    (bot_fix _ rfl β)

theorem absCU_zero : absCU 0 = sliceCU overlapSlice₀ 0 (mem_univ _) zero_fix := by
  rw [absCU, dif_pos rfl]

theorem absCU_eq (β : Fin 1 → ℝ) :
    ∃ (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) (hβ : β ∈ D.V) (hfix : ∀ h ∈ D.H, h • β = β),
      absCU β = sliceCU D β hβ hfix := by
  by_cases h0 : β = 0
  · subst h0
    exact ⟨_, _, _, absCU_zero⟩
  · unfold absCU
    rw [dif_neg h0]
    by_cases hp : 0 < β 0
    · rw [dif_pos hp]
      exact ⟨_, _, _, rfl⟩
    · rw [dif_neg hp]
      exact ⟨_, _, _, rfl⟩

/-- **The proper covering uniformizer construction** `F̂(β) = {absCU β}` (Definition 19.7.7). -/
def absHatU : CoveringUniformizerConstruction absCovP := ⟨fun β => {absCU β}⟩

theorem absHatU_slice (Ψ : absHatU.toUniformizerConstruction.Unif) :
    ∃ D : TranslationSlice ℤˣ (Fin 1 → ℝ), Ψ.1 = sliceUniformizer isScSmoothMap_units_smul D := by
  obtain ⟨Ψ₁, β, Ψh, hmem, hΨ⟩ := Ψ
  obtain ⟨D, hβ, hfix, h⟩ := absCU_eq β
  refine ⟨D, ?_⟩
  change Ψ₁ = _
  rw [← hΨ, mem_singleton_iff.1 hmem, h]
  rfl

/-- **The basic construction for `P`** (Definition 19.7.11): `F̂` with the keyed transitions. -/
def absBasic : CoveringBasicConstruction absCovP :=
  ⟨absHatU, ⟦sliceData isScSmoothMap_units_smul absHatU_slice⟧⟩

theorem absBasic_hasClassUniformizers : absBasic.HasClassUniformizers := fun z =>
  Quotient.inductionOn z fun β => ⟨β, rfl, absCU β, mem_singleton _⟩

theorem mem_absBasic_iff {β : Fin 1 → ℝ} {Ψh : CoveringUniformizer absCovP β} :
    Ψh ∈ absBasic.hatU.F β ↔ Ψh = absCU β := mem_singleton_iff

/-- `h ↦ k(h)` is continuous on `M(Ψ, Ψ')` with its natural topology `T_{Ψ,Ψ'}`. -/
theorem continuous_absM_key (Ψ Ψ' : absBasic.toBasic.U.Unif) :
    Continuous fun h : absBasic.toBasic.M Ψ Ψ' => (h : Ψ.1.Trans Ψ'.1).mor.1 :=
  continuous_discrete_rng.2 fun k =>
    (absBasic.toBasic.isOpen_M_iff (F := sliceData isScSmoothMap_units_smul absHatU_slice) rfl).2
      (sliceData_isOpenTr_key isScSmoothMap_units_smul absHatU_slice Ψ Ψ' k)

/-- **The compatibility hypothesis holds for `absBasic`** (the non-degenerate witness for
`IsCompatible`): `t̂(h) = (k(p h) · i(s(h)), t(p h))` is continuous. -/
theorem absBasic_isCompatible : absBasic.IsCompatible := by
  rintro ⟨β, Ψh, mem⟩ ⟨β', Ψh', mem'⟩
  obtain ⟨D, hβ, hfix, h⟩ := absCU_eq β
  obtain ⟨D', hβ', hfix', h'⟩ := absCU_eq β'
  have hΨ : Ψh = sliceCU D β hβ hfix := (mem_absBasic_iff.1 mem).trans h
  have hΨ' : Ψh' = sliceCU D' β' hβ' hfix' := (mem_absBasic_iff.1 mem').trans h'
  subst hΨ hΨ'
  set x : absBasic.hatU.Unif := ⟨β, _, mem⟩
  set y : absBasic.hatU.Unif := ⟨β', _, mem'⟩
  have hP := absCovP_isFiniteToOneCovering
  have heq : absBasic.tgtHat x y = fun a =>
      (((absBasic.pB x y a : x.Ψh.Ψ.Trans y.Ψh.Ψ).mor.1 * (absBasic.srcHat x y a).1 : ℤˣ),
        ((absBasic.pB x y a : x.Ψh.Ψ.Trans y.Ψh.Ψ).tgt : D'.V)) := by
    funext a
    have hs : (a : x.Ψh.Trans y.Ψh).mor.2 = ((a : x.Ψh.Trans y.Ψh).src.1,
        ((a : x.Ψh.Trans y.Ψh).src.2 : D.V).1) := (a : x.Ψh.Trans y.Ψh).src_mor
    have ht : (a : x.Ψh.Trans y.Ψh).mor.1 • (a : x.Ψh.Trans y.Ψh).mor.2 =
        ((a : x.Ψh.Trans y.Ψh).tgt.1, ((a : x.Ψh.Trans y.Ψh).tgt.2 : D'.V).1) :=
      (a : x.Ψh.Trans y.Ψh).tgt_mor
    rw [hs] at ht
    exact Prod.ext (congrArg Prod.fst ht).symm rfl
  rw [heq]
  have hk : Continuous fun a => (absBasic.pB x y a : x.Ψh.Ψ.Trans y.Ψh.Ψ).mor.1 :=
    (continuous_absM_key x.toUnif y.toUnif).comp (absBasic.continuous_pB hP x y)
  have hs : Continuous fun a => (absBasic.srcHat x y a).1 :=
    continuous_fst.comp (absBasic.isLocalHomeomorph_srcHat hP x y).continuous
  refine Continuous.prodMk ?_ ((absBasic.isLocalHomeomorph_tgtB x y).continuous.comp
    (absBasic.continuous_pB hP x y))
  exact (continuous_of_discreteTopology (f := fun p : ℤˣ × ℤˣ => p.1 * p.2)).comp (hk.prodMk hs)

/-! #### The natural topologies are the orbit-space topologies -/

theorem continuous_sliceHat (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) :
    Continuous fun e : ℤˣ × D.V => (e.1, e.2.1) :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

theorem isOpenMap_sliceHat (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) :
    IsOpenMap fun e : ℤˣ × D.V => (e.1, e.2.1) :=
  IsOpenMap.prodMap IsOpenMap.id D.isOpen.isOpenMap_subtype_val

/-- **`T_{|A|}` is the orbit-space topology**: `W ∈ T_{|A|}` iff `π⁻¹(W)` is open in `ℤˣ × ℝ`. -/
theorem natOpenA_abs_iff (W : Set absCatA.OrbitSpace) :
    absBasic.NatOpenA W ↔ IsOpen (absCatA.π ⁻¹' W) := by
  constructor
  · intro hW
    refine isOpen_iff_forall_mem_open.2 fun a ha => ?_
    obtain ⟨β, -, Ψh, hΨh, e, he, V, hV, heV, hsub⟩ := hW _ ha
    obtain ⟨D, hβ, hfix, h⟩ := absCU_eq β
    rw [mem_absBasic_iff, h] at hΨh
    subst hΨh
    obtain ⟨N, hN, hNo, haN⟩ := exists_open_of_π_eq (K := ℤˣ)
      (continuous_smul_of isScSmoothMap_cover_smul)
      (isOpenMap_sliceHat D V hV) (W := W) (fun _ ⟨d, hd, hdy⟩ => hdy ▸ hsub ⟨d, hd, rfl⟩)
      ⟨e, heV, rfl⟩ he
    exact ⟨N, hN, hNo, haN⟩
  · intro hW z hz
    induction z using Quotient.inductionOn with
    | h a =>
    obtain ⟨D, hβ, hfix, h⟩ := absCU_eq a.2
    refine ⟨a.2, rfl, sliceCU D a.2 hβ hfix, by rw [mem_absBasic_iff, h], (a.1, ⟨a.2, hβ⟩), rfl,
      _, hW.preimage (continuous_sliceHat D), hz, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact hd

/-- **`T_{|B|}` is the orbit-space topology**: `W ∈ T_{|B|}` iff `π⁻¹(W)` is open in `ℝ`. -/
theorem natOpenB_abs_iff (W : Set absCatB.OrbitSpace) :
    absBasic.toBasic.U.NatOpen W ↔ IsOpen (absCatB.π ⁻¹' W) := by
  constructor
  · intro hW
    refine isOpen_iff_forall_mem_open.2 fun a ha => ?_
    obtain ⟨α, hα, Ψ, ⟨Ψh, hΨh, hΨ⟩, o, ho, V, hV, hoV, hsub⟩ := hW _ ha
    obtain ⟨D, hβ, hfix, h⟩ := absCU_eq α
    rw [mem_absBasic_iff.1 hΨh, h] at hΨ
    subst hΨ
    obtain ⟨N, hN, hNo, haN⟩ := exists_open_of_π_eq (K := ℤˣ)
      (continuous_smul_of isScSmoothMap_units_smul)
      (D.isOpen.isOpenMap_subtype_val V hV) (W := W)
      (fun _ ⟨d, hd, hdy⟩ => hdy ▸ hsub ⟨d, hd, rfl⟩) ⟨o, hoV, rfl⟩
      ((congrArg absCatB.π ho).trans hα)
    exact ⟨N, hN, hNo, haN⟩
  · intro hW z hz
    induction z using Quotient.inductionOn with
    | h x =>
    obtain ⟨D, hβ, hfix, h⟩ := absCU_eq x
    refine ⟨x, rfl, absSliceUnif D, ⟨absCU x, mem_singleton _, by rw [h]; rfl⟩, ⟨x, hβ⟩, rfl,
      Subtype.val ⁻¹' (absCatB.π ⁻¹' W), hW.preimage continuous_subtype_val, hz, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact hd

/-- `T_{|A|}` as a topology: the orbit-space topology of `absA` (`|A| ≅ ℝ`). -/
abbrev absTopA : TopologicalSpace absCatA.OrbitSpace := (inferInstance : TopologicalSpace
    absA.OrbitSpace)

theorem isOpen_absTopA_iff (W : Set absCatA.OrbitSpace) :
    IsOpen[absTopA] W ↔ absBasic.NatOpenA W :=
  (natOpenA_abs_iff W).symm

/-- **`T_{|B|}` is the orbit-space topology of `absB`** (`|B| ≅ [0, ∞)`). -/
theorem absNatTopB_eq :
    absBasic.toBasic.natTop absBasic_hasClassUniformizers.toBasic =
      (inferInstance : TopologicalSpace absB.OrbitSpace) :=
  TopologicalSpace.ext (funext fun W => propext (natOpenB_abs_iff W))

theorem absCovP_orbitMap_eq : absCovP.orbitMap = absP.orbitMap := rfl

/-- In `absBasic` the topology `natTopA` of Lemma 19.7.17 (under `IsCompatible`, which holds) is the
orbit-space topology `absTopA`. -/
theorem absBasic_natTopA_eq :
    absBasic.natTopA absCovP_isFiniteToOneCovering absBasic_isCompatible
      absBasic_hasClassUniformizers = absTopA :=
  TopologicalSpace.ext (funext fun W => propext (isOpen_absTopA_iff W).symm)

/-! #### `|P|` is not locally injective at `|(1, 0)|` -/

/-- For any topology on `|A|` making `t ↦ |(1, t)|` continuous, `|P|` is not injective on any
open neighbourhood of `|(1, 0)|`. -/
theorem not_injOn_of_continuous (T : TopologicalSpace absCatA.OrbitSpace)
    (hc : Continuous[_, T] fun t : ℝ => absCatA.π (1, fun _ => t)) {N : Set absCatA.OrbitSpace}
    (hN : IsOpen[T] N) (h0 : absCatA.π (1, 0) ∈ N) : ¬ InjOn absCovP.orbitMap N := by
  intro hinj
  set c : ℝ → absCatA.OrbitSpace := fun t => absCatA.π (1, fun _ => t)
  have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ N :=
    (@Continuous.continuousAt _ _ _ T _ _ hc).preimage_mem_nhds (@IsOpen.mem_nhds _ T _ _ hN h0)
  have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), c (-t) ∈ N := by
    have : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact this.eventually h1
  obtain ⟨t, ⟨ht1, ht2⟩, ht0⟩ :=
    ((h1.and h2).filter_mono nhdsWithin_le_nhds |>.and self_mem_nhdsWithin).exists
      (f := 𝓝[≠] (0 : ℝ))
  exact Chapter19.absA_π_ne 1 ht0 (hinj ht1 ht2 (Chapter19.absP_orbitMap_neg 1 t))

theorem continuous_absTopA_line : Continuous[_, absTopA] fun t : ℝ => absCatA.π (1, fun _ => t) :=
  absA.continuous_π.comp (continuous_const.prodMk (continuous_pi fun _ => continuous_id))

/-! #### Proposition 19.7.18, Corollary 19.7.20 (3), Theorem 19.7.25 (4b) -/

/-- **2021 Proposition 19.7.18, p. 919, does not hold as we read it**: for the finite-to-one
covering functor `P : ℤ/2 ⋉ (ℤˣ × ℝ) → ℤ/2 ⋉ ℝ` and the basic construction `absBasic` (sheet
models: global at `0`, slices elsewhere), `T_{|A|}` is a topology but
`|P| : (|A|, T_{|A|}) → (|B|, T_{|B|})` is not a local homeomorphism (it is `t ↦ |t|` on
`ℝ → [0, ∞)`). -/
theorem not_proposition_19_7_18 :
    IsFiniteToOneCovering absCovP ∧ absBasic.HasClassUniformizers ∧
      ∃ tA : TopologicalSpace absCatA.OrbitSpace, (∀ W, IsOpen[tA] W ↔ absBasic.NatOpenA W) ∧
        ¬ @IsLocalHomeomorph _ _ tA
          (absBasic.toBasic.natTop absBasic_hasClassUniformizers.toBasic) absCovP.orbitMap := by
  refine ⟨absCovP_isFiniteToOneCovering, absBasic_hasClassUniformizers, absTopA,
    isOpen_absTopA_iff, ?_⟩
  rw [absNatTopB_eq]
  exact Chapter19.absCovering_orbitMap_not_isLocalHomeomorph

/-- Proposition 19.7.18 for `absBasic` in the setting of `proposition_19_7_18_hyp` (where
`IsCompatible` and `HasClassUniformizers` hold): `|P| : (|A|, natTopA) → (|B|, T_{|B|})` is not a
local homeomorphism. -/
theorem not_proposition_19_7_18_natTopA :
    ¬ @IsLocalHomeomorph _ _ (absBasic.natTopA absCovP_isFiniteToOneCovering absBasic_isCompatible
        absBasic_hasClassUniformizers)
      (absBasic.toBasic.natTop absBasic_hasClassUniformizers.toBasic) absCovP.orbitMap := by
  rw [absBasic_natTopA_eq, absNatTopB_eq]
  exact Chapter19.absCovering_orbitMap_not_isLocalHomeomorph

/-- **Proposition 19.7.18 does not hold for any reading of `T_{|A|}`** that satisfies Lemma 19.7.17 (2):
for every topology on `|A|` making `e ↦ |Ψ̂(e)|` continuous for the member `Ψ̂` of `F̂(0)`, and
every topology on `|B|`, `|P|` is not a local homeomorphism. -/
theorem not_proposition_19_7_18_of_continuous (tA : TopologicalSpace absCatA.OrbitSpace)
    (tB : TopologicalSpace absCatB.OrbitSpace) :
    ∀ Ψh ∈ absBasic.hatU.F 0,
      Continuous[_, tA] (fun e : Ψh.ObjE => absCatA.π (Ψh.hat.obj e)) →
        ¬ @IsLocalHomeomorph _ _ tA tB absCovP.orbitMap := by
  intro Ψh hΨh hc hloc
  rw [mem_absBasic_iff, absCU_zero] at hΨh
  subst hΨh
  obtain ⟨e, he, hfe⟩ := hloc (absCatA.π (1, 0))
  have hline : Continuous[_, tA] fun t : ℝ => absCatA.π (1, fun _ => t) := by
    have hl : Continuous fun t : ℝ =>
        ((1 : ℤˣ), (⟨fun _ => t, mem_univ _⟩ : overlapSlice₀.V)) :=
      continuous_const.prodMk ((continuous_pi fun _ => continuous_id).subtype_mk _)
    have h := @Continuous.comp _ _ _ _ _ tA _ _ hc hl
    exact h
  refine not_injOn_of_continuous tA hline e.open_source he ?_
  rw [hfe]
  exact e.injOn

/-- **2021 Corollary 19.7.20 (3), p. 922, does not hold as we read it**: in `absBasic`, for
`z = |0|` (with `|P|⁻¹(z) = {|(1, 0)|}`), the member `Ψ̂` of `F̂(0)`, every `a ∈ τ̂⁻¹(ō)` and every
open `V ∋ a` of `E` (in particular every `V(a)` of the corollary), `|P|` is not injective on
`W(z̄₁) = |Ψ̂(V)|`, so `|P| : W(z̄₁) → W(z)` is not a homeomorphism. -/
theorem not_corollary_19_7_20_three :
    (∃ Ψh ∈ absBasic.hatU.F 0, Ψh.model.fiber.Nonempty) ∧
      ∀ Ψh ∈ absBasic.hatU.F 0, ∀ a ∈ Ψh.model.fiber, ∀ V : Set Ψh.ObjE, IsOpen V → a ∈ V →
        ¬ InjOn absCovP.orbitMap ((fun e => absCatA.π (Ψh.hat.obj e)) '' V) := by
  refine ⟨⟨absCU 0, mem_singleton _, (absCU 0).model.surjective _⟩, ?_⟩
  intro Ψh hΨh a ha V hV haV
  rw [mem_absBasic_iff, absCU_zero] at hΨh
  subst hΨh
  have ha' : (a.2 : overlapSlice₀.V).1 = 0 := congrArg Subtype.val ha
  refine not_injOn_of_continuous absTopA continuous_absTopA_line ?_ ?_
  · have : (fun e => absCatA.π ((sliceCU overlapSlice₀ 0 (mem_univ _) zero_fix).hat.obj e)) '' V =
        absA.π '' ((fun e : ℤˣ × overlapSlice₀.V => (e.1, e.2.1)) '' V) := by
      exact (image_image absA.π (fun e : ℤˣ × overlapSlice₀.V => (e.1, e.2.1)) V).symm
    rw [this]
    exact absA.proposition_7_1_8 _ (isOpenMap_sliceHat overlapSlice₀ V hV)
  · refine ⟨a, haV, ?_⟩
    change absCatA.π (a.1, (a.2 : overlapSlice₀.V).1) = absCatA.π (1, 0)
    rw [ha']
    refine (GroupoidalCategory.π_eq_π_iff _).2 ⟨(a.1⁻¹, (a.1, 0)), rfl, ?_⟩
    change (a.1⁻¹ * a.1, a.1⁻¹ • (0 : Fin 1 → ℝ)) = (1, 0)
    rw [inv_mul_cancel, units_smul_zero_rn]

/-- **2021 Theorem 19.7.25 (4b), p. 926, does not hold as we read it**: in `absBasic` the natural
topology `T_{|B|}` is metrizable (the hypothesis of the theorem), `|P|⁻¹(|0|) = {|(1, 0)|}`, and
`|P|` is not injective on any `T_{|A|}`-open neighbourhood `U(z̄₁)` of `|(1, 0)|`, so
`|P| : U(z̄₁) → U(z)` is not a homeomorphism. -/
theorem not_theorem_19_7_25_four_b :
    @MetrizableSpace _ (absBasic.toBasic.natTop absBasic_hasClassUniformizers.toBasic) ∧
      absCovP.orbitMap ⁻¹' {absCatB.π 0} = {absCatA.π (1, 0)} ∧
      absBasic.NatOpenA univ ∧
      ∀ N, absBasic.NatOpenA N → absCatA.π (1, 0) ∈ N → ¬ InjOn absCovP.orbitMap N := by
  refine ⟨?_, ?_, (natOpenA_abs_iff univ).2 isOpen_univ, fun N hN h0 =>
    not_injOn_of_continuous absTopA continuous_absTopA_line ((isOpen_absTopA_iff N).2 hN) h0⟩
  · rw [absNatTopB_eq]
    exact Chapter19.absBOrbitHomeomorph.isEmbedding.metrizableSpace
  · ext z
    constructor
    · intro hz
      have h1 := Chapter19.absBOrbitHomeomorph_orbitMap z
      rw [show absP.orbitMap z = absB.π 0 from hz, Chapter19.absBOrbitHomeomorph_π] at h1
      have h2 : Chapter19.absAOrbitHomeomorph z = 0 := by
        have : |Chapter19.absAOrbitHomeomorph z| = 0 := by rw [← h1]; simp
        exact abs_eq_zero.1 this
      have h3 := Chapter19.absAOrbitHomeomorph.symm_apply_apply z
      rw [h2] at h3
      exact h3.symm
    · rintro rfl
      rfl

end Example

end GroupoidalCategory

end Polyfold
