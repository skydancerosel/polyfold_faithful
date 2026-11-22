import Polyfold.Chapter19.CoveringConstruction
import Polyfold.Chapter19.Metrizability

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19, §19.7
"Covering Constructions", pp. 910–915: the Topological Properties of Structural Maps (19.25),
**Lemma 19.7.12**, **Proposition 19.7.13**, **Proposition 19.7.14**, the structural diagrams
(19.30)–(19.32) and **Proposition 19.7.15**.  Numbers and pages are the 2021 text's.

# Topologies on `M(Ψ̂, Ψ̂')`

## The text, paraphrased

For a basic construction `(F̂, 𝓕)` for `P` the transition sets `M(Ψ, Ψ')` carry the natural
topologies of Theorem 19.3.3 (19.25).  (Lemma 19.7.12) `M(Ψ, Ψ') ₛ×_τ̂ E` is locally metrizable,
regular and Hausdorff.  (Proposition 19.7.13) `M(Ψ̂, Ψ̂')` has a unique topology for which the
bijection (19.26) `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E` is a homeomorphism; it is regular, Hausdorff,
locally metrizable, and metrizable under the properness condition.  (Proposition 19.7.14)
`p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is a surjective local homeomorphism.  (Proposition 19.7.15) (1) `p` is a
surjective local homeomorphism and (19.29) a homeomorphism; (2) the source and target maps of
(19.30) are local homeomorphisms ("the bottom `s` and `t` are local homeomorphisms, `τ̂`, `τ̂'`
and `p` are local homeomorphisms; consequently the top source and target maps are"); (3) the
inversions of (19.31) are homeomorphisms and the units continuous; (4) the multiplications of
(19.32) are local homeomorphisms.

## What is formalized

* Point-set lemmas: `Chapter19.isLocalHomeomorph_fibredFst`, `Chapter19.isLocalHomeomorph_fibredSnd`
  (projections of a fibred product along a local homeomorphism).
* `CoveringBasicConstruction.MB x y` (`M(Ψ, Ψ')` with `T_{Ψ,Ψ'}`), `Fib x y`
  (`M(Ψ, Ψ') ₛ×_τ̂ E` with the subspace topology), **Lemma 19.7.12** (`lemma_19_7_12`, and
  `metrizableSpace_fib`: the space is even metrizable).
* `MHat x y` (`M(Ψ̂, Ψ̂')` with the topology induced by (19.26), `toFib`), **Proposition 19.7.13**
  (`proposition_19_7_13`: `fibHomeomorph`, uniqueness of the topology, regular, Hausdorff,
  metrizable), **Proposition 19.7.14** (`proposition_19_7_14`).
* **Proposition 19.7.15**: (1) `proposition_19_7_15_one`; (2) `isLocalHomeomorph_srcHat` (the
  top source map); (3) `continuous_unitHat`; and, under `IsCompatible` (the top target maps are
  continuous), the target maps `isLocalHomeomorph_tgtHat`, the inversion `invHatHomeomorph`, the
  multiplication `isLocalHomeomorph_mulHat`, collected in `proposition_19_7_15_hyp`.

## Readings

* "The top target map is a local homeomorphism" (19.7.15 (2)): the printed argument gives
  `τ̂' ∘ t̂ = t ∘ p`, a local homeomorphism, but does not give the continuity of `t̂`, which can
  jump
  between the sheets of `τ̂'`.  We read Proposition 19.7.15 (2)–(4) under the hypothesis
  `IsCompatible` (every top target map `t̂ : M(Ψ̂, Ψ̂') → E'` is continuous).  Definition 19.7.11
  asks for no relation between the members of `F̂(β)`: two members with the same `Ψ` may differ
  by a permutation of the sheets of `τ̂` that is not locally constant, and then `t̂` is not
  continuous; so we presume that such a compatibility is intended.  A non-degenerate witness:
  `absBasic_isCompatible` (`CoveringCounterexamples.lean`, `ℤ/2` acting non-trivially).
  The source map, `p` and the unit maps need no hypothesis.
* The properness condition of Propositions 19.7.13 and 19.7.15 is not needed for metrizability:
  `M(Ψ, Ψ')` is metrizable without it (`BasicConstruction.metrizableSpace_M`, Proposition 19.4.4),
  hence so are `M(Ψ, Ψ') ₛ×_τ̂ E ⊂ M(Ψ, Ψ') × E` and `M(Ψ̂, Ψ̂')`.
* "Uniquely characterized" (19.7.13): any topology on `M(Ψ̂, Ψ̂')` for which (19.26) is a
  homeomorphism is the induced one.
-/

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace Chapter19

/-! ### Fibred products along local homeomorphisms -/

section FibredProduct

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- **The first projection of a fibred product along a local homeomorphism**: for `s : X → Z`
continuous and `τ : Y → Z` a local homeomorphism, `{(x, y) | s x = τ y} → X` is a local
homeomorphism. -/
theorem isLocalHomeomorph_fibredFst {s : X → Z} {τ : Y → Z} (hs : Continuous s)
    (hτ : IsLocalHomeomorph τ) :
    IsLocalHomeomorph fun p : {p : X × Y // s p.1 = τ p.2} => p.1.1 := by
  classical
  refine IsLocalHomeomorph.mk _ fun p => ?_
  obtain ⟨e, hpe, he⟩ := hτ p.1.2
  have hτe : ∀ y, τ y = e y := fun y => congrFun he y
  have hmem : ∀ x, s x ∈ e.target → s x = τ (e.symm (s x)) := fun x hx => by
    rw [hτe, e.right_inv hx]
  let inv : X → {p : X × Y // s p.1 = τ p.2} := fun x =>
    if hx : s x ∈ e.target then ⟨(x, e.symm (s x)), hmem x hx⟩ else p
  have hinv : ∀ x (hx : s x ∈ e.target), inv x = ⟨(x, e.symm (s x)), hmem x hx⟩ :=
    fun x hx => dif_pos hx
  have hsrc : ∀ q : {p : X × Y // s p.1 = τ p.2}, q.1.2 ∈ e.source → s q.1.1 ∈ e.target :=
    fun q hq => by rw [q.2, hτe]; exact e.map_source hq
  refine ⟨{ toFun := fun q => q.1.1
            invFun := inv
            source := {q | q.1.2 ∈ e.source}
            target := s ⁻¹' e.target
            map_source' := fun q hq => hsrc q hq
            map_target' := fun x hx => by
              change (inv x).1.2 ∈ e.source
              rw [hinv x hx]
              exact e.map_target hx
            left_inv' := fun q hq => by
              change inv q.1.1 = q
              rw [hinv _ (hsrc q hq)]
              refine Subtype.ext (Prod.ext rfl ?_)
              change e.symm (s q.1.1) = q.1.2
              rw [q.2, hτe, e.left_inv hq]
            right_inv' := fun x hx => by
              rw [hinv x hx]
            open_source := e.open_source.preimage (continuous_snd.comp continuous_subtype_val)
            open_target := e.open_target.preimage hs
            continuousOn_toFun := (continuous_fst.comp continuous_subtype_val).continuousOn
            continuousOn_invFun := by
              rw [continuousOn_iff_continuous_domRestrict]
              exact Continuous.congr (Continuous.subtype_mk (continuous_subtype_val.prodMk
                (e.continuousOn_symm.comp_continuous (hs.comp continuous_subtype_val)
                  fun x => x.2)) fun x => hmem x.1 x.2) fun x => (hinv x.1 x.2).symm },
    hpe, fun _ _ => rfl⟩

/-- **The second projection of a fibred product along a local homeomorphism**: for `s : X → Z` a
local homeomorphism and `τ : Y → Z` continuous, `{(x, y) | s x = τ y} → Y` is a local
homeomorphism. -/
theorem isLocalHomeomorph_fibredSnd {s : X → Z} {τ : Y → Z} (hs : IsLocalHomeomorph s)
    (hτ : Continuous τ) :
    IsLocalHomeomorph fun p : {p : X × Y // s p.1 = τ p.2} => p.1.2 := by
  let e : {p : X × Y // s p.1 = τ p.2} ≃ₜ {p : Y × X // τ p.1 = s p.2} :=
    { toFun := fun p => ⟨p.1.swap, p.2.symm⟩
      invFun := fun p => ⟨p.1.swap, p.2.symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _ }
  exact (isLocalHomeomorph_fibredFst hτ hs).comp e.isLocalHomeomorph

end FibredProduct

end Chapter19

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

variable {A B : GroupoidalCategory.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}

namespace CoveringBasicConstruction

variable (Bh : CoveringBasicConstruction P)

/-- `M(Ψ, Ψ')` with its natural topology `T_{Ψ,Ψ'}` (19.25), for `Ψ̂ ∈ F̂(β)`, `Ψ̂' ∈ F̂(β')`. -/
abbrev MB (x y : Bh.hatU.Unif) : Type u := Bh.toBasic.M x.toUnif y.toUnif

/-- **`M(Ψ, Ψ') ₛ×_τ̂ E`** (Lemma 19.7.12) with the subspace topology of `M(Ψ, Ψ') × E`. -/
abbrev Fib (x y : Bh.hatU.Unif) : Type u :=
  {p : Bh.MB x y × x.Ψh.ObjE // (p.1 : x.Ψh.Ψ.Trans y.Ψh.Ψ).src = x.Ψh.τ.obj p.2}

/-- `M(Ψ̂, Ψ̂')`, to be topologized by (19.26). -/
def MHat (x y : Bh.hatU.Unif) : Type u := x.Ψh.Trans y.Ψh

variable {Bh}

/-- An element of `M(Ψ̂, Ψ̂')` in `Bh.MHat x y`. -/
abbrev toMHat {x y : Bh.hatU.Unif} (a : x.Ψh.Trans y.Ψh) : Bh.MHat x y := a

variable (Bh)

/-- `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` into the topological `M(Ψ, Ψ')`. -/
def pB (x y : Bh.hatU.Unif) (a : Bh.MHat x y) : Bh.MB x y :=
  x.Ψh.transMap y.Ψh (a : x.Ψh.Trans y.Ψh)

/-- **The map (19.26)** `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`, `(e, φ̂, e') ↦ (p(e, φ̂, e'), e)`. -/
def toFib (x y : Bh.hatU.Unif) (a : Bh.MHat x y) : Bh.Fib x y :=
  ⟨(Bh.pB x y a, (a : x.Ψh.Trans y.Ψh).src), rfl⟩

/-- **The topology of `M(Ψ̂, Ψ̂')` (Proposition 19.7.13)**: induced by (19.26). -/
instance topologicalSpaceMHat (x y : Bh.hatU.Unif) : TopologicalSpace (Bh.MHat x y) :=
  TopologicalSpace.induced (Bh.toFib x y) inferInstance

theorem continuous_toFib (x y : Bh.hatU.Unif) : Continuous (Bh.toFib x y) :=
  continuous_induced_dom

/-! ### Lemma 19.7.12 -/

/-- `M(Ψ, Ψ') ₛ×_τ̂ E` is metrizable (a subspace of the metrizable `M(Ψ, Ψ') × E`). -/
instance metrizableSpace_fib (x y : Bh.hatU.Unif) : MetrizableSpace (Bh.Fib x y) := by
  have h1 := Bh.toBasic.metrizableSpace_M x.toUnif y.toUnif
  have h2 := x.Ψh.E.PObj.metrizableSpace
  have : MetrizableSpace (Bh.MB x y × x.Ψh.ObjE) := inferInstance
  exact IsEmbedding.subtypeVal.metrizableSpace

/-- **2021 Lemma 19.7.12, p. 911**: `M(Ψ, Ψ') ₛ×_τ̂ E` is locally metrizable, regular and
Hausdorff. -/
theorem lemma_19_7_12 (x y : Bh.hatU.Unif) :
    (∀ z : Bh.Fib x y, ∃ W : Set (Bh.Fib x y), IsOpen W ∧ z ∈ W ∧ MetrizableSpace W) ∧
      RegularSpace (Bh.Fib x y) ∧ T2Space (Bh.Fib x y) :=
  ⟨fun _ => ⟨univ, isOpen_univ, mem_univ _, inferInstance⟩, inferInstance, inferInstance⟩

/-! ### Propositions 19.7.13 and 19.7.14 -/

/-- **(19.26)–(19.29) as a homeomorphism** `M(Ψ̂, Ψ̂') ≃ₜ M(Ψ, Ψ') ₛ×_τ̂ E` (Lemma 19.7.10). -/
def fibHomeomorph (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) : Bh.MHat x y ≃ₜ Bh.Fib x y
    where
  toFun := Bh.toFib x y
  invFun q := CoveringUniformizer.liftTrans hP (q.1.1 : x.Ψh.Ψ.Trans y.Ψh.Ψ) q.1.2 q.2
  left_inv a := (CoveringUniformizer.eq_liftTrans hP (a : x.Ψh.Trans y.Ψh)).symm
  right_inv q := Subtype.ext (Prod.ext (CoveringUniformizer.transMap_liftTrans hP _ _ _) rfl)
  continuous_toFun := Bh.continuous_toFib x y
  continuous_invFun := by
    refine continuous_induced_rng.2 ?_
    have : Bh.toFib x y ∘ (fun q : Bh.Fib x y =>
        toMHat (CoveringUniformizer.liftTrans hP (q.1.1 : x.Ψh.Ψ.Trans y.Ψh.Ψ) q.1.2 q.2)) =
        id :=
      funext fun q => Subtype.ext (Prod.ext (CoveringUniformizer.transMap_liftTrans hP _ _ _) rfl)
    rw [this]
    exact continuous_id

@[simp] theorem fibHomeomorph_apply (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) (a :
    Bh.MHat x y) :
    Bh.fibHomeomorph hP x y a = Bh.toFib x y a := rfl

/-- `M(Ψ̂, Ψ̂')` is metrizable (homeomorphic to `M(Ψ, Ψ') ₛ×_τ̂ E`). -/
theorem metrizableSpace_MHat (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) :
    MetrizableSpace (Bh.MHat x y) :=
  (Bh.fibHomeomorph hP x y).isEmbedding.metrizableSpace

/-- **2021 Proposition 19.7.13, p. 913**: `M(Ψ̂, Ψ̂')` has a topology for which the canonical map
(19.26) is a homeomorphism, and it is the only such topology; it is regular, Hausdorff and
locally metrizable, and metrizable (with or without the properness condition, see the module
docstring). -/
theorem proposition_19_7_13 (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) :
    (∃ e : Bh.MHat x y ≃ₜ Bh.Fib x y, ∀ a, e a = Bh.toFib x y a) ∧
      (∀ t : TopologicalSpace (Bh.MHat x y), @IsHomeomorph _ _ t _ (Bh.toFib x y) →
        t = Bh.topologicalSpaceMHat x y) ∧
      RegularSpace (Bh.MHat x y) ∧ T2Space (Bh.MHat x y) ∧
      (∀ a : Bh.MHat x y, ∃ W : Set (Bh.MHat x y), IsOpen W ∧ a ∈ W ∧ MetrizableSpace W) ∧
      MetrizableSpace (Bh.MHat x y) := by
  have := Bh.metrizableSpace_MHat hP x y
  refine ⟨⟨Bh.fibHomeomorph hP x y, fun _ => rfl⟩, fun t ht => ?_, inferInstance, inferInstance,
    fun _ => ⟨univ, isOpen_univ, mem_univ _, inferInstance⟩, inferInstance⟩
  exact (@IsHomeomorph.isInducing _ _ t _ _ ht).eq_induced

/-- `τ̂ : E → O` is a local homeomorphism (Definition 17.8.4 (1)). -/
theorem isLocalHomeomorph_τ (x : Bh.hatU.Unif) : IsLocalHomeomorph x.Ψh.τ.obj :=
  x.Ψh.model.isLocalScDiffeo.isLocalHomeomorph

/-- `τ̂ : E → O` is surjective (Definition 17.8.4 (1)). -/
theorem surjective_τ (x : Bh.hatU.Unif) : Surjective x.Ψh.τ.obj := x.Ψh.model.surjective

/-- The source map of `M(Ψ, Ψ')` is a local homeomorphism (Proposition 19.3.5). -/
theorem isLocalHomeomorph_srcB (x y : Bh.hatU.Unif) :
    IsLocalHomeomorph fun a : Bh.MB x y => (a : x.Ψh.Ψ.Trans y.Ψh.Ψ).src :=
  Bh.toBasic.rep.isLocalHomeomorph_src x.toUnif y.toUnif

/-- The target map of `M(Ψ, Ψ')` is a local homeomorphism (Proposition 19.3.5). -/
theorem isLocalHomeomorph_tgtB (x y : Bh.hatU.Unif) :
    IsLocalHomeomorph fun a : Bh.MB x y => (a : x.Ψh.Ψ.Trans y.Ψh.Ψ).tgt :=
  Bh.toBasic.rep.isLocalHomeomorph_tgt x.toUnif y.toUnif

/-- **2021 Proposition 19.7.14, p. 914**: `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is a surjective local
homeomorphism (between metrizable spaces). -/
theorem proposition_19_7_14 (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) :
    IsLocalHomeomorph (Bh.pB x y) ∧ Surjective (Bh.pB x y) := by
  refine ⟨?_, (x.Ψh.lemma_19_7_9 y.Ψh hP).1⟩
  have h1 := Chapter19.isLocalHomeomorph_fibredFst (Bh.isLocalHomeomorph_srcB x y).continuous
    (Bh.isLocalHomeomorph_τ x)
  exact h1.comp (Bh.fibHomeomorph hP x y).isLocalHomeomorph

/-! ### Proposition 19.7.15 -/

/-- **2021 Proposition 19.7.15 (1), p. 915**: `p` is a surjective local homeomorphism and
`(e, φ̂, e') ↦ (p(e, φ̂, e'), e)` is a homeomorphism `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`. -/
theorem proposition_19_7_15_one (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) :
    IsLocalHomeomorph (Bh.pB x y) ∧ Surjective (Bh.pB x y) ∧
      ∃ e : Bh.MHat x y ≃ₜ Bh.Fib x y, ∀ a, e a = Bh.toFib x y a :=
  ⟨(Bh.proposition_19_7_14 hP x y).1, (Bh.proposition_19_7_14 hP x y).2,
    Bh.fibHomeomorph hP x y, fun _ => rfl⟩

/-- The top source map `ŝ : M(Ψ̂, Ψ̂') → E` of (19.30). -/
def srcHat (x y : Bh.hatU.Unif) (a : Bh.MHat x y) : x.Ψh.ObjE := (a : x.Ψh.Trans y.Ψh).src

/-- The top target map `t̂ : M(Ψ̂, Ψ̂') → E'` of (19.30). -/
def tgtHat (x y : Bh.hatU.Unif) (a : Bh.MHat x y) : y.Ψh.ObjE := (a : x.Ψh.Trans y.Ψh).tgt

/-- **2021 Proposition 19.7.15 (2), p. 915, the source map**: `ŝ : M(Ψ̂, Ψ̂') → E` is a local
homeomorphism. -/
theorem isLocalHomeomorph_srcHat (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) :
    IsLocalHomeomorph (Bh.srcHat x y) := by
  have h1 := Chapter19.isLocalHomeomorph_fibredSnd (Bh.isLocalHomeomorph_srcB x y)
    (Bh.isLocalHomeomorph_τ x).continuous
  exact h1.comp (Bh.fibHomeomorph hP x y).isLocalHomeomorph

theorem continuous_pB (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) : Continuous (Bh.pB x y)
    :=
  (Bh.proposition_19_7_14 hP x y).1.continuous

/-- The diagram (19.30): `τ̂' ∘ t̂ = t ∘ p`. -/
theorem τ_tgtHat (x y : Bh.hatU.Unif) (a : Bh.MHat x y) :
    y.Ψh.τ.obj (Bh.tgtHat x y a) = (Bh.pB x y a : x.Ψh.Ψ.Trans y.Ψh.Ψ).tgt := rfl

/-- The diagram (19.30): `τ̂ ∘ ŝ = s ∘ p`. -/
theorem τ_srcHat (x y : Bh.hatU.Unif) (a : Bh.MHat x y) :
    x.Ψh.τ.obj (Bh.srcHat x y a) = (Bh.pB x y a : x.Ψh.Ψ.Trans y.Ψh.Ψ).src := rfl

/-- **The compatibility hypothesis**: every top target map `t̂ : M(Ψ̂, Ψ̂') → E'` is continuous.
An added hypothesis (hence the `_hyp` suffix of the statements that use it), the reading of
l. 44572, the opening of §19.7, where the uniformizers "are sc-smoothly compatible"; no definition
of §19.7 states it, and Proposition 19.7.15 (2) asserts its consequence that `t̂` is a local
homeomorphism.  Without it 19.7.15 (2) does not hold as we read it
(`proposition_19_7_15_two_without_compatible`). -/
def IsCompatible : Prop := ∀ x y : Bh.hatU.Unif, Continuous (Bh.tgtHat x y)

/-- **2021 Proposition 19.7.15 (2), p. 915, the target map**, under `IsCompatible`: `t̂` is a
local homeomorphism (`τ̂' ∘ t̂ = t ∘ p` is one and `τ̂'` is one). -/
theorem isLocalHomeomorph_tgtHat (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible) (x y :
    Bh.hatU.Unif) :
    IsLocalHomeomorph (Bh.tgtHat x y) := by
  have h0 := (Bh.isLocalHomeomorph_tgtB x y).comp (Bh.proposition_19_7_14 hP x y).1
  have h : IsLocalHomeomorph (y.Ψh.τ.obj ∘ Bh.tgtHat x y) := h0
  exact h.of_comp (Bh.isLocalHomeomorph_τ y) (hC x y)

/-- The top unit map `û : E → M(Ψ̂, Ψ̂)`. -/
def unitHat (x : Bh.hatU.Unif) (e : x.Ψh.ObjE) : Bh.MHat x x :=
  toMHat (TransitionSet.unit e : x.Ψh.Trans x.Ψh)

/-- **2021 Proposition 19.7.15 (3), p. 915, the unit map**: `û : E → M(Ψ̂, Ψ̂)` is continuous. -/
theorem continuous_unitHat (x : Bh.hatU.Unif) : Continuous (Bh.unitHat x) := by
  refine continuous_induced_rng.2 (Continuous.subtype_mk (Continuous.prodMk ?_ continuous_id) _)
  have h : (fun e => Bh.pB x x (Bh.unitHat x e)) =
      (fun o => Bh.toBasic.rep.toTr (TransitionSet.unit o : x.Ψh.Ψ.Trans x.Ψh.Ψ)) ∘ x.Ψh.τ.obj :=
    funext fun e => x.Ψh.transMap_unit e
  change Continuous fun e => Bh.pB x x (Bh.unitHat x e)
  rw [h]
  exact (Bh.toBasic.rep.continuous_unit x.toUnif).comp (Bh.isLocalHomeomorph_τ x).continuous

/-- The top inversion map `ι̂ : M(Ψ̂, Ψ̂') → M(Ψ̂', Ψ̂)`. -/
def invHat (x y : Bh.hatU.Unif) (a : Bh.MHat x y) : Bh.MHat y x :=
  toMHat (a : x.Ψh.Trans y.Ψh).inv

theorem continuous_invHat (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible) (x y :
    Bh.hatU.Unif) :
    Continuous (Bh.invHat x y) := by
  refine continuous_induced_rng.2 (Continuous.subtype_mk (Continuous.prodMk ?_ (hC x y)) _)
  have h : (fun a => Bh.pB y x (Bh.invHat x y a)) =
      (Bh.toBasic.rep.invHomeomorph x.toUnif y.toUnif) ∘ Bh.pB x y :=
    funext fun a => x.Ψh.transMap_inv y.Ψh (a : x.Ψh.Trans y.Ψh)
  change Continuous fun a => Bh.pB y x (Bh.invHat x y a)
  rw [h]
  exact (Bh.toBasic.rep.invHomeomorph x.toUnif y.toUnif).continuous.comp (Bh.continuous_pB hP x y)

/-- **2021 Proposition 19.7.15 (3), p. 915, the inversion map**, under `IsCompatible`: `ι̂` is a
homeomorphism `M(Ψ̂, Ψ̂') → M(Ψ̂', Ψ̂)`. -/
def invHatHomeomorph (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible) (x y : Bh.hatU.Unif) :
    Bh.MHat x y ≃ₜ Bh.MHat y x where
  toFun := Bh.invHat x y
  invFun := Bh.invHat y x
  left_inv a := TransitionSet.inv_inv (a : x.Ψh.Trans y.Ψh)
  right_inv a := TransitionSet.inv_inv (a : y.Ψh.Trans x.Ψh)
  continuous_toFun := Bh.continuous_invHat hP hC x y
  continuous_invFun := Bh.continuous_invHat hP hC y x

/-- `M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂')` (the source of (19.32)). -/
abbrev FibProdHat (x y z : Bh.hatU.Unif) : Type u :=
  {q : Bh.MHat y z × Bh.MHat x y // Bh.srcHat y z q.1 = Bh.tgtHat x y q.2}

/-- The top multiplication `m̂ : M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂') → M(Ψ̂, Ψ̂'')` of (19.32). -/
def mulHat (x y z : Bh.hatU.Unif) (q : Bh.FibProdHat x y z) : Bh.MHat x z :=
  toMHat (TransitionSet.comp (q.1.1 : y.Ψh.Trans z.Ψh) (q.1.2 : x.Ψh.Trans y.Ψh)
    (TransitionSet.mor_composable_of_src_eq_tgt q.2))

theorem srcHat_mulHat (x y z : Bh.hatU.Unif) (q : Bh.FibProdHat x y z) :
    Bh.srcHat x z (Bh.mulHat x y z q) = Bh.srcHat x y q.1.2 := rfl

theorem continuous_mulHat (hP : IsFiniteToOneCovering P) (x y z : Bh.hatU.Unif) : Continuous
    (Bh.mulHat x y z) := by
  refine continuous_induced_rng.2 (Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _)
  · have h : (fun q => Bh.pB x z (Bh.mulHat x y z q)) = Bh.toBasic.rep.mulMap x.toUnif y.toUnif
        z.toUnif ∘ fun q => ⟨(Bh.pB y z q.1.1, Bh.pB x y q.1.2), congrArg y.Ψh.τ.obj q.2⟩ :=
      funext fun q => x.Ψh.transMap_comp y.Ψh z.Ψh _ _
        (TransitionSet.mor_composable_of_src_eq_tgt q.2)
    change Continuous fun q => Bh.pB x z (Bh.mulHat x y z q)
    rw [h]
    refine (Bh.toBasic.rep.continuous_mulMap).comp (Continuous.subtype_mk ?_ _)
    exact ((Bh.continuous_pB hP y z).comp (continuous_fst.comp continuous_subtype_val)).prodMk
      ((Bh.continuous_pB hP x y).comp (continuous_snd.comp continuous_subtype_val))
  · exact (Bh.isLocalHomeomorph_srcHat hP x y).continuous.comp
      (continuous_snd.comp continuous_subtype_val)

/-- **2021 Proposition 19.7.15 (4), p. 915**, under `IsCompatible`: the top multiplication
`m̂` is a local homeomorphism (`ŝ ∘ m̂ = ŝ ∘ pr₂` and `pr₂` is a local homeomorphism, the
fibred product being taken along the local homeomorphism `ŝ` and the continuous `t̂`). -/
theorem isLocalHomeomorph_mulHat (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (x y z : Bh.hatU.Unif) :
    IsLocalHomeomorph (Bh.mulHat x y z) := by
  have h2 : IsLocalHomeomorph fun q : Bh.FibProdHat x y z => q.1.2 :=
    Chapter19.isLocalHomeomorph_fibredSnd (Bh.isLocalHomeomorph_srcHat hP y z) (hC x y)
  have h : IsLocalHomeomorph (Bh.srcHat x z ∘ Bh.mulHat x y z) :=
    (Bh.isLocalHomeomorph_srcHat hP x y).comp h2
  exact h.of_comp (Bh.isLocalHomeomorph_srcHat hP x z) (Bh.continuous_mulHat hP x y z)

/-- **2021 Proposition 19.7.15, p. 915**, under `IsCompatible` for (2)–(4): (1) `p` is a
surjective local homeomorphism and (19.29) a homeomorphism; (2) the top source and target maps
are local homeomorphisms; (3) the top inversion is a homeomorphism and the top unit continuous;
(4) the top multiplication is a local homeomorphism; all spaces are metrizable. -/
theorem proposition_19_7_15_hyp (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (x y z : Bh.hatU.Unif) :
    (IsLocalHomeomorph (Bh.pB x y) ∧ Surjective (Bh.pB x y) ∧
      ∃ e : Bh.MHat x y ≃ₜ Bh.Fib x y, ∀ a, e a = Bh.toFib x y a) ∧
    (IsLocalHomeomorph (Bh.srcHat x y) ∧ IsLocalHomeomorph (Bh.tgtHat x y)) ∧
    ((∃ e : Bh.MHat x y ≃ₜ Bh.MHat y x, ∀ a, e a = Bh.invHat x y a) ∧
      Continuous (Bh.unitHat x)) ∧
    IsLocalHomeomorph (Bh.mulHat x y z) ∧
    MetrizableSpace (Bh.MHat x y) ∧ MetrizableSpace (Bh.MB x y) :=
  ⟨Bh.proposition_19_7_15_one hP x y,
    ⟨Bh.isLocalHomeomorph_srcHat hP x y, Bh.isLocalHomeomorph_tgtHat hP hC x y⟩,
    ⟨⟨Bh.invHatHomeomorph hP hC x y, fun _ => rfl⟩, Bh.continuous_unitHat x⟩,
    Bh.isLocalHomeomorph_mulHat hP hC x y z, Bh.metrizableSpace_MHat hP x y,
    Bh.toBasic.metrizableSpace_M x.toUnif y.toUnif⟩

end CoveringBasicConstruction

end GroupoidalCategory

end Polyfold
