import Polyfold.Chapter19.CoveringMetrizability
import Polyfold.Chapter19.PolyfoldStructureGCT
import Polyfold.Chapter17.ProperCoveringPolyfold
import Polyfold.Chapter8.TangentPairs

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19, §19.7
"Covering Constructions", pp. 926–930, "Sc-Smoothness Properties": **Proposition 19.7.26**
(pp. 926–927), **Definition 19.7.27** (p. 928, the structural diagrams), **Theorem 19.7.28**
(pp. 928–929, polyfold results for `P`) and **Theorem 19.7.29** (pp. 929–930, `P` is
sc-smooth).  Numbers and pages are the 2021 text's.

# Covering constructions: the sc-smooth structure

## The text, paraphrased

(p. 926) If `T_{|B|}` is metrizable, `(F, 𝓕)` gives a polyfold construction `(F, M)` for the GCT
`B` (Theorem 19.5.3); the `M(Ψ̂, Ψ̂')` are metrizable (Proposition 19.7.13) and
`p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is a surjective local homeomorphism (Proposition 19.7.15), so its
domain carries a unique M-polyfold structure for which `p` is a surjective local
sc-diffeomorphism.  (Proposition 19.7.26) Every `M(Ψ, Ψ')` has its natural M-polyfold structure
(Theorem 19.5.3) and every `M(Ψ̂, Ψ̂')` an M-polyfold structure characterized by `p` being a
(surjective) local sc-diffeomorphism; then `⟨p, s⟩ : M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_p E`,
`(e, φ̂, e') ↦ (p(e, φ̂, e'), e)`, is an sc-diffeomorphism; if `(F, 𝓕)` is tame, all
`M(Ψ, Ψ')` and `M(Ψ̂, Ψ̂')` are tame.  *Proof*: `⟨p, s⟩` is a homeomorphism (Proposition 19.7.15),
sc-smooth, and a local sc-diffeomorphism since `p` is; tameness passes through the local
sc-diffeomorphisms `τ̂` and `p`.  (p. 928) From the diagrams (19.30)–(19.32): the top source and
target maps are local sc-diffeomorphisms, the top inversion an sc-diffeomorphism, the top
multiplication a local sc-diffeomorphism.  (Definition 19.7.27) The diagrams (19.30)–(19.32) are
the structural commutative diagrams.  (Theorem 19.7.28) (1) All `M(Ψ̂, Ψ̂')`, `M(Ψ, Ψ')` have
natural M-polyfold structures with `p` a surjective local sc-diffeomorphism and the structural
diagrams with the expected sc-smoothness; (2) `A` and `B` are GCTs and `P` is a proper covering
functor (Definition 17.8.1); (3) `F̂` is a functor of proper covering uniformizers, and the
upgraded transition construction is a proper polyfold covering structure `(F̂, M)` (Definition
17.8.13).  (Theorem 19.7.29) `A` and `B` have natural polyfold structures; (1) the local
representative of `P` with respect to `Ψ̂` is `τ̂`; (2) the diagram (19.40) commutes, `⟨P, s⟩`
maps the image of `Γ̂` onto that of `Γ ₛ×_τ̂ Ψ̂`, which is injective, so
`⟨p, s⟩ = (Γ ₛ×_τ̂ Ψ̂)⁻¹ ∘ ⟨P, s⟩ ∘ Γ̂` is sc-smooth.

## What is formalized (namespace `Polyfold.GroupoidalCategory.CoveringBasicConstruction`)

* `basePolyfold x y` (`M(Ψ, Ψ')`, Theorem 19.5.1), `fibSet`, `fibPolyfold` (Part I's
  fibred-product sub-M-polyfold `M(Ψ, Ψ') ₛ×_τ̂ E`, `MPolyfold.isSubMPolyfold_fibredProduct'`),
  `isLocalScDiffeo_fibFst`; `t2Space_MHat`, `paracompactSpace_MHat`; **`hatPolyfold hP x y`**,
  the M-polyfold structure of `M(Ψ̂, Ψ̂')` (transported along the homeomorphism (19.26),
  `MPolyfold.transport`, which is Chapter 9's descent along a homeomorphism).
* `isScDiffeoOn_toFibSet` (`⟨p, s⟩` is an sc-diffeomorphism), `isLocalScDiffeo_pB`,
  `isScDiffeoOn_id_of_isLocalScDiffeo_pB` (uniqueness), `isLocalScDiffeo_srcHat`,
  `isLocalScDiffeo_tgtHat`, `isScSmoothMap_unitHat`, `isScDiffeoOn_invB`, `isScDiffeoOn_invHat`,
  `isScSmoothMap_invHat`, `isLocalScDiffeo_mulHat`, `isScSmoothMap_mulHat`; tameness
  `isTame_E`, `isTame_basePolyfold`, `isTame_hatPolyfold`.
* **`proposition_19_7_26`**, **`definition_19_7_27`** (the four structural diagrams commute),
  **`theorem_19_7_28_one_hyp`**.
* `gctA`, `gctB` (reducible forms of Theorem 19.7.25 (2)'s `toGCTA`, `toGCTB`);
  `toProperCoveringUniformizer` (a member of `F̂(β)` is a proper covering uniformizer of
  Definition 17.8.10) and the converse `ofProperCoveringUniformizer`;
  `toProperCoveringConstruction` (Definition 17.8.12), `mem_toProperCoveringConstruction_iff`,
  `unifOf`, `polyfoldB` (Theorem 19.5.3 (2)), `polyfoldB_F`;
  **`toProperPolyfoldCoveringStructure`** (Definition 17.8.13) and
  `toProperPolyfoldCoveringFunctor`; **`theorem_19_7_28_two_hyp`**, **`theorem_19_7_28_three_hyp`**.
* `fibredMorP` (`⟨P, s⟩`), `gammaHat` (`Γ̂`), `gammaFib` (`Γ ₛ×_τ̂ Ψ̂`), **`theorem_19_7_29_hyp`**.
* Witnesses in `CoveringPolyfoldExamples.lean` (`absBasic`: two sheets of `ℤ/2 ⋉ ℝ` over
  `ℤ/2 ⋉ ℝ`, `-1` acting by the reflection).

## Readings

* **`M(Ψ, Ψ') ₛ×_p E`** in Proposition 19.7.26 is read as `M(Ψ, Ψ') ₛ×_τ̂ E` (as in Lemma
  19.7.10 and Theorem 19.7.29), with Part I's sub-M-polyfold structure of `M(Ψ, Ψ') × E` (`s` is a
  local sc-diffeomorphism, `τ̂` one on objects).
* **"Characterized by"** (19.7.26): any M-polyfold structure on the topological space
  `M(Ψ̂, Ψ̂')` for which `p` is a local sc-diffeomorphism agrees with `hatPolyfold` (the identity
  is an sc-diffeomorphism), as for Theorem 19.5.1.
* **The metrizability of `|B|`** in Proposition 19.7.26 and Theorem 19.7.28 (1) is kept as
  printed but not used (`M(Ψ, Ψ')` is metrizable for every basic construction, Proposition
  19.4.4); it is used in Theorem 19.7.28 (2), (3) and Theorem 19.7.29 (the GCTs).
* **"`(F, 𝓕)` is tame"**: the domains `O` of the uniformizers of `F` are tame, as in Theorem
  19.5.3 (2).
* **Top target maps.**  The statements involving `t̂` (and so `ι̂`, `m̂`, the proper polyfold
  covering structure and Theorem 19.7.29) are under `IsCompatible`, an added hypothesis, the
  reading of l. 44572 (`CoveringTopology.lean`; without it `t̂` need not be continuous,
  `proposition_19_7_15_two_without_compatible`); hence the `_hyp` suffixes.  `F̂(β) ≠ ∅` on every
  class (`HasClassUniformizers`) is the standing reading of §17.1, as in Theorem 19.2.2.
* **Theorem 19.7.28 (3)**: the proper covering uniformizers of Definition 17.8.10 for the GCTs of
  Theorem 19.7.25 (2) are exactly the members of `F̂` read through
  `toProperCoveringUniformizer`; Definition 17.8.10 (1), (3) follow from the cartesian property
  (Definition 19.7.4) and (4) from Theorem 19.2.2 (3), Lemma 19.7.17 (2) and (19.34).
  Conversely (`ofProperCoveringUniformizer`), a uniformizer of Definition 17.8.10 satisfies
  Definition 19.7.4 for a finite-to-one covering functor, and the two passages are inverse on
  the data.
* **"`A` has a natural polyfold structure"** (19.7.29): `A` has no translation-groupoid
  uniformizers (Remark 17.8.11); we read it, as Definition 17.8.13 does ("`A` becomes a
  polyfold"), as the M-polyfolds `M(Ψ̂, Ψ̂')` with (a)–(c) of Definition 17.1.8 over the object
  M-polyfolds of the `E` (the proper polyfold covering structure), together with the open
  embeddings `|Ψ̂|` whose images cover `|A|`.  For `B` it is Theorem 19.5.3 (2) (the form of
  Definition 17.1.8).
* **"The local representative of `P` with respect to `Ψ̂` is `τ̂`"**: `P ∘ Ψ̂ = Ψ ∘ τ̂` on objects
  and morphisms, with `τ̂` an sc-smooth functor which is a proper covering functor (Definition
  8.5.1; its fibres are finite by Definition 19.7.1).
* **`⟨p, s⟩ = (Γ ₛ×_τ̂ Ψ̂)⁻¹ ∘ ⟨P, s⟩ ∘ Γ̂`** (19.40) is stated as: for `q ∈ M(Ψ, Ψ') ₛ×_τ̂ E`,
  `(Γ ₛ×_τ̂ Ψ̂)(q) = ⟨P, s⟩(Γ̂(a))` if and only if `q = ⟨p, s⟩(a)`.
* **Definition 19.7.27** names the diagrams (19.30)–(19.32); `definition_19_7_27` records that
  they commute (proved in `CoveringConstruction.lean`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

variable {A B : GroupoidalCategory.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}

namespace CoveringBasicConstruction

variable (Bh : CoveringBasicConstruction P)

/-- The M-polyfold `M(Ψ, Ψ')` (Theorem 19.5.1) for `Ψ̂ ∈ F̂(β)`, `Ψ̂' ∈ F̂(β')`. -/
abbrev basePolyfold (x y : Bh.hatU.Unif) : MPolyfold (Bh.MB x y) :=
  Bh.toBasic.transPolyfold x.toUnif y.toUnif

theorem isLocalScDiffeo_srcB' (x y : Bh.hatU.Unif) :
    (Bh.basePolyfold x y).IsLocalScDiffeo x.toUnif.1.P
      fun a : Bh.MB x y => (a : x.toUnif.1.Trans y.toUnif.1).src :=
  Bh.toBasic.rep.isLocalScDiffeo_src x.toUnif y.toUnif

instance paracompactSpace_MB_prod (x y : Bh.hatU.Unif) :
    ParacompactSpace (Bh.MB x y × x.Ψh.ObjE) :=
  MPolyfold.paracompactSpace_prod (Bh.basePolyfold x y) x.Ψh.E.PObj

/-- The set `M(Ψ, Ψ') ₛ×_τ̂ E ⊂ M(Ψ, Ψ') × E`. -/
abbrev fibSet (x y : Bh.hatU.Unif) : Set (Bh.MB x y × x.Ψh.ObjE) :=
  MPolyfold.fibredProduct (fun a : Bh.MB x y => (a : x.toUnif.1.Trans y.toUnif.1).src) x.Ψh.τ.obj

instance paracompactSpace_fibSet (x y : Bh.hatU.Unif) : ParacompactSpace (Bh.fibSet x y) :=
  ((Bh.basePolyfold x y).prod x.Ψh.E.PObj).paracompactSpace_subtype _

theorem isSubMPolyfold_fibSet (x y : Bh.hatU.Unif) :
    ((Bh.basePolyfold x y).prod x.Ψh.E.PObj).IsSubMPolyfold (Bh.fibSet x y) :=
  MPolyfold.isSubMPolyfold_fibredProduct' (S := x.toUnif.1.P)
    (f := fun a : Bh.MB x y => (a : x.toUnif.1.Trans y.toUnif.1).src)
    (Bh.isLocalScDiffeo_srcB' x y).isScSmoothMap x.Ψh.model.isLocalScDiffeo

/-- **The sub-M-polyfold `M(Ψ, Ψ') ₛ×_τ̂ E`** of `M(Ψ, Ψ') × E` (Part I's fibred product). -/
def fibPolyfold (x y : Bh.hatU.Unif) : MPolyfold (Bh.fibSet x y) :=
  MPolyfold.subPolyfold (Bh.isSubMPolyfold_fibSet x y)

theorem isLocalScDiffeo_fibFst (x y : Bh.hatU.Unif) :
    (Bh.fibPolyfold x y).IsLocalScDiffeo (Bh.basePolyfold x y)
      fun q : Bh.fibSet x y => (q : Bh.MB x y × x.Ψh.ObjE).1 := by
  exact MPolyfold.isLocalScDiffeo_fstOfFibredProduct (S := x.toUnif.1.P)
    (f := fun a : Bh.MB x y => (a : x.toUnif.1.Trans y.toUnif.1).src)
    (Bh.isLocalScDiffeo_srcB' x y).isScSmoothMap x.Ψh.model.isLocalScDiffeo

/-- `M(Ψ̂, Ψ̂')` is Hausdorff. -/
theorem t2Space_MHat (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) :
    T2Space (Bh.MHat x y) := by
  have := Bh.metrizableSpace_MHat hP x y
  infer_instance

/-- `M(Ψ̂, Ψ̂')` is paracompact. -/
theorem paracompactSpace_MHat (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) :
    ParacompactSpace (Bh.MHat x y) := by
  have := Bh.metrizableSpace_MHat hP x y
  exact paracompactSpace_of_metrizableSpace _

/-- (19.26) as a homeomorphism onto the set `fibSet`. -/
def fibSetHomeomorph (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) :
    Bh.MHat x y ≃ₜ Bh.fibSet x y :=
  Bh.fibHomeomorph hP x y

/-- `⟨p, s⟩ : M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`, `(e, φ̂, e') ↦ (p(e, φ̂, e'), e)`. -/
abbrev toFibSet (x y : Bh.hatU.Unif) (a : Bh.MHat x y) : Bh.fibSet x y := Bh.toFib x y a

/-- **The M-polyfold structure of `M(Ψ̂, Ψ̂')`** (Proposition 19.7.26): transported from the
sub-M-polyfold `M(Ψ, Ψ') ₛ×_τ̂ E` along the homeomorphism (19.26). -/
def hatPolyfold (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    MPolyfold (Bh.MHat x y) :=
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  (Bh.fibPolyfold x y).transport (Bh.fibSetHomeomorph hP x y).symm

/-- The inversion `ι : M(Ψ, Ψ') → M(Ψ', Ψ)` is an sc-diffeomorphism (Corollary 19.5.2). -/
theorem isScDiffeoOn_invB (x y : Bh.hatU.Unif) :
    (Bh.basePolyfold x y).IsScDiffeoOn (Bh.basePolyfold y x)
      (fun a : Bh.MB x y => Bh.toBasic.rep.toTr (a : x.toUnif.1.Trans y.toUnif.1).inv)
      (fun a : Bh.MB y x => Bh.toBasic.rep.toTr (a : y.toUnif.1.Trans x.toUnif.1).inv)
      univ univ :=
  ⟨Bh.toBasic.rep.isScSmoothMap_inv x.toUnif y.toUnif,
    Bh.toBasic.rep.isScSmoothMap_inv y.toUnif x.toUnif, mapsTo_univ _ _, mapsTo_univ _ _,
    fun _ _ => TransitionSet.inv_inv _, fun _ _ => TransitionSet.inv_inv _⟩

theorem isLocalScDiffeo_of_isScDiffeoOn_univ {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {PX : MPolyfold X} {PY : MPolyfold Y} {f : X → Y} {g : Y → X}
    (h : PX.IsScDiffeoOn PY f g univ univ) : PX.IsLocalScDiffeo PY f :=
  fun a => ⟨univ, univ, g, mem_univ a, h⟩

section Smooth

variable (hP : IsFiniteToOneCovering P)

/-- **Proposition 19.7.26, `⟨p, s⟩` is an sc-diffeomorphism** `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`. -/
theorem isScDiffeoOn_toFibSet (x y : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    (Bh.hatPolyfold hP x y).IsScDiffeoOn (Bh.fibPolyfold x y) (Bh.toFibSet x y)
      (Bh.fibSetHomeomorph hP x y).symm univ univ := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  exact (MPolyfold.isScDiffeoOn_transport (Bh.fibPolyfold x y)
    (Bh.fibSetHomeomorph hP x y).symm).symm

/-- **Proposition 19.7.26, `p` is a local sc-diffeomorphism** `M(Ψ̂, Ψ̂') → M(Ψ, Ψ')`. -/
theorem isLocalScDiffeo_pB (x y : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    (Bh.hatPolyfold hP x y).IsLocalScDiffeo (Bh.basePolyfold x y) (Bh.pB x y) := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  exact (Bh.isLocalScDiffeo_fibFst x y).comp
    (isLocalScDiffeo_of_isScDiffeoOn_univ (Bh.isScDiffeoOn_toFibSet hP x y))

/-- **Proposition 19.7.26, "characterized by"**: every M-polyfold structure `Q` on the
topological space `M(Ψ̂, Ψ̂')` for which `p` is a local sc-diffeomorphism agrees with
`hatPolyfold`: the identity is an sc-diffeomorphism. -/
theorem isScDiffeoOn_id_of_isLocalScDiffeo_pB (x y : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    ∀ Q : MPolyfold (Bh.MHat x y), Q.IsLocalScDiffeo (Bh.basePolyfold x y) (Bh.pB x y) →
      Q.IsScDiffeoOn (Bh.hatPolyfold hP x y) id id univ univ := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  intro Q hQ
  exact (MPolyfold.isLocalScDiffeo_of_comp_eq hQ (Bh.isLocalScDiffeo_pB hP x y) continuous_id
    fun _ => rfl).isScDiffeoOn_of_bijective (Equiv.refl _) fun _ => rfl

/-- **The top source map `ŝ : M(Ψ̂, Ψ̂') → E` is a local sc-diffeomorphism** (diagram (19.30):
`τ̂ ∘ ŝ = s ∘ p`). -/
theorem isLocalScDiffeo_srcHat (x y : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    (Bh.hatPolyfold hP x y).IsLocalScDiffeo x.Ψh.E.PObj (Bh.srcHat x y) := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  exact MPolyfold.isLocalScDiffeo_of_comp_eq ((Bh.isLocalScDiffeo_srcB' x y).comp
    (Bh.isLocalScDiffeo_pB hP x y)) (S := x.toUnif.1.P) x.Ψh.model.isLocalScDiffeo
    (Bh.isLocalHomeomorph_srcHat hP x y).continuous fun _ => rfl

variable (hC : Bh.IsCompatible)
include hC

/-- **The top target map `t̂ : M(Ψ̂, Ψ̂') → E'` is a local sc-diffeomorphism**, under
`IsCompatible` (diagram (19.30): `τ̂' ∘ t̂ = t ∘ p`). -/
theorem isLocalScDiffeo_tgtHat (x y : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    (Bh.hatPolyfold hP x y).IsLocalScDiffeo y.Ψh.E.PObj (Bh.tgtHat x y) := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  exact MPolyfold.isLocalScDiffeo_of_comp_eq ((Bh.toBasic.rep.isLocalScDiffeo_tgt x.toUnif
    y.toUnif).comp (Bh.isLocalScDiffeo_pB hP x y)) (S := y.toUnif.1.P)
    y.Ψh.model.isLocalScDiffeo (hC x y) fun _ => rfl

omit hC in
/-- **The top unit map `û : E → M(Ψ̂, Ψ̂)` is sc-smooth** (diagram (19.31): `p ∘ û = u ∘ τ̂`). -/
theorem isScSmoothMap_unitHat (x : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    x.Ψh.E.PObj.IsScSmoothMap (Bh.hatPolyfold hP x x) (Bh.unitHat x) := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  refine MPolyfold.isScSmoothMap_of_isLocalScDiffeo_comp (Bh.isLocalScDiffeo_pB hP x x)
    (Bh.continuous_unitHat x) ?_
  have h : Bh.pB x x ∘ Bh.unitHat x =
      (fun o => Bh.toBasic.rep.toTr (TransitionSet.unit o : x.toUnif.1.Trans x.toUnif.1)) ∘
        x.Ψh.τ.obj :=
    funext fun e => x.Ψh.transMap_unit e
  rw [h]
  exact (Bh.toBasic.rep.isScSmoothMap_unit x.toUnif).comp x.Ψh.τ.isScSmoothMap_obj

/-- **The top inversion `ι̂ : M(Ψ̂, Ψ̂') → M(Ψ̂', Ψ̂)` is an sc-diffeomorphism**, under
`IsCompatible` (diagram (19.31): `p ∘ ι̂ = ι ∘ p`). -/
theorem isScDiffeoOn_invHat (x y : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    (Bh.hatPolyfold hP x y).IsScDiffeoOn (Bh.hatPolyfold hP y x) (Bh.invHat x y) (Bh.invHat y x)
      univ univ := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  have hl := MPolyfold.isLocalScDiffeo_of_comp_eq
    ((isLocalScDiffeo_of_isScDiffeoOn_univ (Bh.isScDiffeoOn_invB x y)).comp
      (Bh.isLocalScDiffeo_pB hP x y)) (Bh.isLocalScDiffeo_pB hP y x)
    (Bh.continuous_invHat hP hC x y) fun a => x.Ψh.transMap_inv y.Ψh (a : x.Ψh.Trans y.Ψh)
  exact hl.isScDiffeoOn_of_bijective
    ⟨Bh.invHat x y, Bh.invHat y x, fun a => TransitionSet.inv_inv (a : x.Ψh.Trans y.Ψh),
      fun a => TransitionSet.inv_inv (a : y.Ψh.Trans x.Ψh)⟩ fun _ => rfl

/-- The top inversion is sc-smooth. -/
theorem isScSmoothMap_invHat (x y : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    (Bh.hatPolyfold hP x y).IsScSmoothMap (Bh.hatPolyfold hP y x) (Bh.invHat x y) := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  exact (Bh.isScDiffeoOn_invHat hP hC x y).isScSmoothOn

/-- **The top multiplication `m̂ : M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂') → M(Ψ̂, Ψ̂'')` is a local
sc-diffeomorphism** on the fibred-product sub-M-polyfold, under `IsCompatible` (diagram (19.32);
`ŝ ∘ m̂ = ŝ ∘ pr₂`). -/
theorem isLocalScDiffeo_mulHat (x y z : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    letI := MPolyfold.paracompactSpace_prod (Bh.hatPolyfold hP y z) (Bh.hatPolyfold hP x y)
    letI := ((Bh.hatPolyfold hP y z).prod (Bh.hatPolyfold hP x y)).paracompactSpace_subtype
      (MPolyfold.fibredProduct (Bh.srcHat y z) (Bh.tgtHat x y))
    (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct
      (Bh.isLocalScDiffeo_srcHat hP y z)
      (Bh.isLocalScDiffeo_tgtHat hP hC x y).isScSmoothMap)).IsLocalScDiffeo
      (Bh.hatPolyfold hP x z) (Bh.mulHat x y z) := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  let := MPolyfold.paracompactSpace_prod (Bh.hatPolyfold hP y z) (Bh.hatPolyfold hP x y)
  let := ((Bh.hatPolyfold hP y z).prod (Bh.hatPolyfold hP x y)).paracompactSpace_subtype
    (MPolyfold.fibredProduct (Bh.srcHat y z) (Bh.tgtHat x y))
  have h2 := MPolyfold.isLocalScDiffeo_sndOfFibredProduct (Bh.isLocalScDiffeo_srcHat hP y z)
    (Bh.isLocalScDiffeo_tgtHat hP hC x y).isScSmoothMap
  exact MPolyfold.isLocalScDiffeo_of_comp_eq ((Bh.isLocalScDiffeo_srcHat hP x y).comp h2)
    (Bh.isLocalScDiffeo_srcHat hP x z) (Bh.continuous_mulHat hP x y z) fun _ => rfl

/-- **The top multiplication is sc-smooth** in Chapter 17's form (Definition 17.1.8 (c)). -/
theorem isScSmoothMap_mulHat (x y z : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    MPolyfold.IsScSmoothOnFibredProduct (Bh.hatPolyfold hP y z) (Bh.hatPolyfold hP x y)
      (Bh.hatPolyfold hP x z) (Bh.isLocalScDiffeo_srcHat hP y z)
      (Bh.isLocalScDiffeo_tgtHat hP hC x y).isScSmoothMap (Bh.mulHat x y z) := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  let := MPolyfold.paracompactSpace_prod (Bh.hatPolyfold hP y z) (Bh.hatPolyfold hP x y)
  let := ((Bh.hatPolyfold hP y z).prod (Bh.hatPolyfold hP x y)).paracompactSpace_subtype
    (MPolyfold.fibredProduct (Bh.srcHat y z) (Bh.tgtHat x y))
  exact (Bh.isLocalScDiffeo_mulHat hP hC x y z).isScSmoothMap

omit hP hC in
/-- `E` is tame if `O` is (`τ̂` is a local sc-diffeomorphism on objects). -/
theorem isTame_E (x : Bh.hatU.Unif) (hO : x.toUnif.1.P.IsTame) : x.Ψh.E.PObj.IsTame :=
  x.Ψh.model.isLocalScDiffeo.isTame hO

omit hP hC in
/-- `M(Ψ, Ψ')` is tame if `O` is (Theorem 19.5.1, `s` a local sc-diffeomorphism). -/
theorem isTame_basePolyfold (x y : Bh.hatU.Unif) (hO : x.toUnif.1.P.IsTame) :
    (Bh.basePolyfold x y).IsTame :=
  Bh.toBasic.rep.isTame_transPolyfold _ _ hO

omit hC in
/-- `M(Ψ̂, Ψ̂')` is tame if `O` is (`p` a local sc-diffeomorphism). -/
theorem isTame_hatPolyfold (x y : Bh.hatU.Unif) (hO : x.toUnif.1.P.IsTame) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    (Bh.hatPolyfold hP x y).IsTame := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  exact (Bh.isLocalScDiffeo_pB hP x y).isTame (Bh.isTame_basePolyfold x y hO)

omit hC in
/-- **2021 Proposition 19.7.26, pp. 926–927**: for a finite-to-one covering functor `P` and a
basic construction `(F̂, 𝓕)` for `P` with `|B|` metrizable, (i) every `M(Ψ, Ψ')` has its natural
M-polyfold structure (Theorems 19.5.1, 19.5.3: `s`, `t` local sc-diffeomorphisms); (ii) every
`M(Ψ̂, Ψ̂')` has an M-polyfold structure (`hatPolyfold`) for which `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is a
surjective local sc-diffeomorphism, (iii) characterized by this: for any other such structure
the identity is an sc-diffeomorphism; (iv) `⟨p, s⟩ : M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E` is an
sc-diffeomorphism onto Part I's fibred-product sub-M-polyfold; (v) if `(F, 𝓕)` is tame (the
domains `O` are tame), `E`, `M(Ψ, Ψ')` and `M(Ψ̂, Ψ̂')` are tame.  (The metrizability of `|B|` is
not used, as for Theorem 19.5.1.) -/
theorem proposition_19_7_26 (hU : Bh.HasClassUniformizers)
    (_hm : @MetrizableSpace B.OrbitSpace (Bh.toBasic.natTop hU.toBasic)) (x y : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    ((Bh.basePolyfold x y).IsLocalScDiffeo x.toUnif.1.P
        (fun a : Bh.MB x y => (a : x.toUnif.1.Trans y.toUnif.1).src) ∧
      (Bh.basePolyfold x y).IsLocalScDiffeo y.toUnif.1.P
        (fun a : Bh.MB x y => (a : x.toUnif.1.Trans y.toUnif.1).tgt)) ∧
    ((Bh.hatPolyfold hP x y).IsLocalScDiffeo (Bh.basePolyfold x y) (Bh.pB x y) ∧
      Surjective (Bh.pB x y)) ∧
    (∀ Q : MPolyfold (Bh.MHat x y), Q.IsLocalScDiffeo (Bh.basePolyfold x y) (Bh.pB x y) →
      Q.IsScDiffeoOn (Bh.hatPolyfold hP x y) id id univ univ) ∧
    (Bh.hatPolyfold hP x y).IsScDiffeoOn (Bh.fibPolyfold x y) (Bh.toFibSet x y)
      (Bh.fibSetHomeomorph hP x y).symm univ univ ∧
    ((∀ Ψ : Bh.toBasic.U.Unif, Ψ.1.P.IsTame) →
      x.Ψh.E.PObj.IsTame ∧ (Bh.basePolyfold x y).IsTame ∧ (Bh.hatPolyfold hP x y).IsTame) := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  exact ⟨⟨Bh.toBasic.rep.isLocalScDiffeo_src x.toUnif y.toUnif,
      Bh.toBasic.rep.isLocalScDiffeo_tgt x.toUnif y.toUnif⟩,
    ⟨Bh.isLocalScDiffeo_pB hP x y, (Bh.proposition_19_7_14 hP x y).2⟩,
    Bh.isScDiffeoOn_id_of_isLocalScDiffeo_pB hP x y, Bh.isScDiffeoOn_toFibSet hP x y,
    fun ht => ⟨Bh.isTame_E x (ht x.toUnif), Bh.isTame_basePolyfold x y (ht x.toUnif),
      Bh.isTame_hatPolyfold hP x y (ht x.toUnif)⟩⟩

omit hP hC in
/-- **2021 Definition 19.7.27, p. 928 (the structural commutative diagrams)**: the diagrams
(19.30) (source and target), (19.31) (inversion and unit) and (19.32) (multiplication) commute:
`s ∘ p = τ̂ ∘ ŝ`, `t ∘ p = τ̂' ∘ t̂`, `p ∘ ι̂ = ι ∘ p`, `p ∘ û = u ∘ τ̂`,
`p ∘ m̂ = m ∘ (p ₛ×ₜ p)`. -/
theorem definition_19_7_27 (x y z : Bh.hatU.Unif) :
    (∀ a : x.Ψh.Trans y.Ψh, (x.Ψh.transMap y.Ψh a).src = x.Ψh.τ.obj a.src ∧
      (x.Ψh.transMap y.Ψh a).tgt = y.Ψh.τ.obj a.tgt) ∧
    (∀ a : x.Ψh.Trans y.Ψh, y.Ψh.transMap x.Ψh a.inv = (x.Ψh.transMap y.Ψh a).inv) ∧
    (∀ e : x.Ψh.ObjE,
      x.Ψh.transMap x.Ψh (TransitionSet.unit e) = TransitionSet.unit (x.Ψh.τ.obj e)) ∧
    ∀ (b : y.Ψh.Trans z.Ψh) (a : x.Ψh.Trans y.Ψh)
      (h : A.toGroupoidStr.src b.mor = A.toGroupoidStr.tgt a.mor),
      ∃ h' : B.toGroupoidStr.src (y.Ψh.transMap z.Ψh b).mor =
          B.toGroupoidStr.tgt (x.Ψh.transMap y.Ψh a).mor,
        x.Ψh.transMap z.Ψh (TransitionSet.comp b a h) =
          TransitionSet.comp (y.Ψh.transMap z.Ψh b) (x.Ψh.transMap y.Ψh a) h' :=
  ⟨x.Ψh.transMap_src_tgt y.Ψh, x.Ψh.transMap_inv y.Ψh, x.Ψh.transMap_unit,
    fun b a h => ⟨_, x.Ψh.transMap_comp y.Ψh z.Ψh b a h⟩⟩

/-- **2021 Theorem 19.7.28 (1), p. 928**, under `IsCompatible` (an added hypothesis, the reading of
l. 44572): all `M(Ψ̂, Ψ̂')` and `M(Ψ, Ψ')` have natural M-polyfold structures for which `p` is a
surjective local sc-diffeomorphism, and the structural diagrams (19.30)–(19.32) (Definition
19.7.27) have the expected sc-smoothness properties: bottom and top source and target maps are
local sc-diffeomorphisms, the inversions are sc-diffeomorphisms, the units are sc-smooth, the
bottom multiplication is sc-smooth and the top multiplication a local sc-diffeomorphism. -/
theorem theorem_19_7_28_one_hyp (hU : Bh.HasClassUniformizers)
    (_hm : @MetrizableSpace B.OrbitSpace (Bh.toBasic.natTop hU.toBasic)) (x y z : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    ((Bh.hatPolyfold hP x y).IsLocalScDiffeo (Bh.basePolyfold x y) (Bh.pB x y) ∧
      Surjective (Bh.pB x y)) ∧
    ((Bh.basePolyfold x y).IsLocalScDiffeo x.toUnif.1.P
        (fun a : Bh.MB x y => (a : x.toUnif.1.Trans y.toUnif.1).src) ∧
      (Bh.basePolyfold x y).IsLocalScDiffeo y.toUnif.1.P
        (fun a : Bh.MB x y => (a : x.toUnif.1.Trans y.toUnif.1).tgt) ∧
      (Bh.hatPolyfold hP x y).IsLocalScDiffeo x.Ψh.E.PObj (Bh.srcHat x y) ∧
      (Bh.hatPolyfold hP x y).IsLocalScDiffeo y.Ψh.E.PObj (Bh.tgtHat x y)) ∧
    ((Bh.basePolyfold x y).IsScDiffeoOn (Bh.basePolyfold y x)
        (fun a : Bh.MB x y => Bh.toBasic.rep.toTr (a : x.toUnif.1.Trans y.toUnif.1).inv)
        (fun a : Bh.MB y x => Bh.toBasic.rep.toTr (a : y.toUnif.1.Trans x.toUnif.1).inv)
        univ univ ∧
      (Bh.hatPolyfold hP x y).IsScDiffeoOn (Bh.hatPolyfold hP y x) (Bh.invHat x y)
        (Bh.invHat y x) univ univ) ∧
    (x.toUnif.1.P.IsScSmoothMap (Bh.basePolyfold x x)
        (fun o => Bh.toBasic.rep.toTr (TransitionSet.unit o : x.toUnif.1.Trans x.toUnif.1)) ∧
      x.Ψh.E.PObj.IsScSmoothMap (Bh.hatPolyfold hP x x) (Bh.unitHat x)) ∧
    (MPolyfold.IsScSmoothOnFibredProduct (Bh.basePolyfold y z) (Bh.basePolyfold x y)
        (Bh.basePolyfold x z) (Bh.toBasic.rep.isLocalScDiffeo_src y.toUnif z.toUnif)
        (Bh.toBasic.rep.isLocalScDiffeo_tgt x.toUnif y.toUnif).isScSmoothMap
        (fun p => (Bh.toBasic.rep.toTr (GroupoidStr.TransitionSet.mul p) : Bh.MB x z)) ∧
      MPolyfold.IsScSmoothOnFibredProduct (Bh.hatPolyfold hP y z) (Bh.hatPolyfold hP x y)
        (Bh.hatPolyfold hP x z) (Bh.isLocalScDiffeo_srcHat hP y z)
        (Bh.isLocalScDiffeo_tgtHat hP hC x y).isScSmoothMap (Bh.mulHat x y z) ∧
      letI := MPolyfold.paracompactSpace_prod (Bh.hatPolyfold hP y z) (Bh.hatPolyfold hP x y)
      letI := ((Bh.hatPolyfold hP y z).prod (Bh.hatPolyfold hP x y)).paracompactSpace_subtype
        (MPolyfold.fibredProduct (Bh.srcHat y z) (Bh.tgtHat x y))
      (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct
        (Bh.isLocalScDiffeo_srcHat hP y z)
        (Bh.isLocalScDiffeo_tgtHat hP hC x y).isScSmoothMap)).IsLocalScDiffeo
        (Bh.hatPolyfold hP x z) (Bh.mulHat x y z)) := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  exact ⟨⟨Bh.isLocalScDiffeo_pB hP x y, (Bh.proposition_19_7_14 hP x y).2⟩,
    ⟨Bh.toBasic.rep.isLocalScDiffeo_src x.toUnif y.toUnif,
      Bh.toBasic.rep.isLocalScDiffeo_tgt x.toUnif y.toUnif, Bh.isLocalScDiffeo_srcHat hP x y,
      Bh.isLocalScDiffeo_tgtHat hP hC x y⟩,
    ⟨Bh.isScDiffeoOn_invB x y, Bh.isScDiffeoOn_invHat hP hC x y⟩,
    ⟨Bh.toBasic.rep.isScSmoothMap_unit x.toUnif, Bh.isScSmoothMap_unitHat hP x⟩,
    Bh.toBasic.rep.isScSmoothMap_mul x.toUnif y.toUnif z.toUnif,
    Bh.isScSmoothMap_mulHat hP hC x y z, Bh.isLocalScDiffeo_mulHat hP hC x y z⟩

end Smooth

/-! ### Theorem 19.7.28 (2), (3): the GCTs and the proper polyfold covering structure -/

section GCT

variable (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible) (hU : Bh.HasClassUniformizers)
  (hm : @MetrizableSpace B.OrbitSpace (Bh.toBasic.natTop hU.toBasic))

/-- **The GCT `A`** of Theorem 19.7.25 (2) (`toGCTA`), as a reducible definition. -/
abbrev gctA : GCT.{u} where
  toGroupoidalCategory := A
  top := Bh.natTopA hP hC hU
  metrizable := (Bh.theorem_19_7_25_one_hyp hP hC hU hm).1

/-- **The GCT `B`** of Theorem 19.7.25 (2) (`toGCTB`), as a reducible definition. -/
abbrev gctB : GCT.{u} where
  toGroupoidalCategory := B
  top := Bh.toBasic.natTop hU.toBasic
  metrizable := hm

theorem gctA_eq : Bh.gctA hP hC hU hm = Bh.toGCTA hP hC hU hm := rfl

theorem gctB_eq : Bh.gctB hU hm = Bh.toGCTB hU hm := rfl

/-- **Theorem 19.7.28 (3), `F̂(β)` as proper covering uniformizers (Definition 17.8.10)** of the
proper covering functor `P` of the GCTs of Theorem 19.7.25 (2).  Definition 17.8.10 (1) and (3)
follow from the cartesian property (Definition 19.7.4); (4) is Theorem 19.2.2 (3) for `|Ψ|`,
Lemma 19.7.17 (2) for `|Ψ̂|` and (19.34). -/
def toProperCoveringUniformizer {β : B.Obj} (Ψh : CoveringUniformizer P β)
    (hmem : Ψh ∈ Bh.hatU.F β) :
    @ProperCoveringUniformizer (Bh.gctA hP hC hU hm) (Bh.gctB hU hm) P β where
  Ψ := Ψh.Ψ
  ObjE := Ψh.ObjE
  MorE := Ψh.MorE
  E := Ψh.E
  τ := Ψh.τ
  model := Ψh.model
  hat := Ψh.hat
  obj_pt := Ψh.obj_pt
  bijOn_fiber := by
    refine ⟨fun e he => ?_, Ψh.injective_hat.injOn, fun a ha => ?_⟩
    · change P.obj (Ψh.hat.obj e) = β
      rw [Ψh.obj_comm, show Ψh.τ.obj e = Ψh.model.pt from he, Ψh.obj_pt]
    · have ha' : P.obj a = Ψh.Ψ.obj Ψh.model.pt := by rw [Ψh.obj_pt]; exact ha
      obtain ⟨e, he, rfl⟩ := Ψh.cartesian_obj _ a ha'
      exact ⟨e, he, rfl⟩
  injective_hat := Ψh.injective_hat
  full_hat := Ψh.full_hat
  faithful_hat := Ψh.faithful_hat
  obj_comm := Ψh.obj_comm
  mor_comm := Ψh.mor_comm
  preimage_range := by
    ext a
    constructor
    · rintro ⟨o, ho⟩
      obtain ⟨e, -, he⟩ := Ψh.cartesian_obj o a ho.symm
      exact ⟨e, he⟩
    · rintro ⟨e, rfl⟩
      exact ⟨Ψh.τ.obj e, (Ψh.obj_comm e).symm⟩
  orbit_homeomorph := by
    let _ := Bh.toBasic.natTop hU.toBasic
    let _ := Bh.natTopA hP hC hU
    let x : Bh.hatU.Unif := ⟨β, Ψh, hmem⟩
    have h1 := Bh.toBasic.theorem_19_2_2_three hU.toBasic
      (show Ψh.Ψ ∈ Bh.toBasic.U.F β from ⟨Ψh, hmem, rfl⟩)
    have h2 := Bh.lemma_19_7_17_two_hyp hP hC hU x
    refine ⟨range Ψh.Ψ.functor.orbitMap, h1.1.isOpen_range, h1.2, h1.1.isEmbedding, rfl,
      h2.isEmbedding, ?_⟩
    have e1 : range Ψh.Ψ.functor.orbitMap = range fun o => B.π (Ψh.Ψ.obj o) := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        induction w using Quotient.inductionOn with
        | h o => exact ⟨o, rfl⟩
      · rintro ⟨o, rfl⟩
        exact ⟨GroupoidStr.π _ o, rfl⟩
    have e2 : range Ψh.hat.orbitMap = range fun e => A.π (Ψh.hat.obj e) := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        induction w using Quotient.inductionOn with
        | h e => exact ⟨e, rfl⟩
      · rintro ⟨e, rfl⟩
        exact ⟨GroupoidStr.π _ e, rfl⟩
    change range Ψh.hat.orbitMap = P.orbitMap ⁻¹' range Ψh.Ψ.functor.orbitMap
    rw [e1, e2, preimage_range_orbitMap hP Ψh]

/-- **A proper covering uniformizer of Definition 17.8.10 as one of Definition 19.7.3**: the
cartesian property (Definition 19.7.4) follows from Definition 17.8.10 (3), the injectivity of
`Ψ` and Definition 19.7.1 (2) (a morphism of `A` is determined by its image and its source). -/
def ofProperCoveringUniformizer {β : B.Obj}
    (V : @ProperCoveringUniformizer (Bh.gctA hP hC hU hm) (Bh.gctB hU hm) P β) :
    CoveringUniformizer P β where
  Ψ := V.Ψ
  ObjE := V.ObjE
  MorE := V.MorE
  E := V.E
  τ := V.τ
  model := V.model
  hat := V.hat
  obj_pt := V.obj_pt
  injective_hat := V.injective_hat
  full_hat := V.full_hat
  faithful_hat := V.faithful_hat
  obj_comm := V.obj_comm
  mor_comm := V.mor_comm
  cartesian_obj o a h := by
    obtain ⟨e, he⟩ : a ∈ range V.hat.obj := V.preimage_range ▸ ⟨o, h.symm⟩
    refine ⟨e, V.Ψ.injective_obj ?_, he⟩
    change V.Ψ.obj (V.τ.obj e) = V.Ψ.obj o
    rw [← V.obj_comm, he, h]
  cartesian_mor φ q h := by
    have hs : P.obj (A.toGroupoidStr.src φ) = V.Ψ.obj q.2 := by
      rw [← P.src_mor, h]
      exact V.Ψ.functor.src_mor q
    obtain ⟨e, he⟩ : A.toGroupoidStr.src φ ∈ range V.hat.obj :=
      V.preimage_range ▸ ⟨q.2, hs.symm⟩
    have hτ : V.τ.obj e = q.2 := V.Ψ.injective_obj (by
      change V.Ψ.obj (V.τ.obj e) = V.Ψ.obj q.2
      rw [← V.obj_comm, he, hs])
    have hm' : V.τ.mor (V.model.liftMor q.1 e) = q := by
      rw [V.model.mor_eq, V.model.groupIndex_liftMor, V.model.src_liftMor, hτ]
    refine ⟨V.model.liftMor q.1 e, hm', hP.mor_ext ?_ ?_⟩
    · rw [V.mor_comm, hm', h]
    · rw [V.hat.src_mor, V.model.src_liftMor, he]

/-- `Ψ̂ ↦ Ψ̂` is the identity on the data (structure eta). -/
theorem ofProperCoveringUniformizer_to {β : B.Obj} (Ψh : CoveringUniformizer P β)
    (hmem : Ψh ∈ Bh.hatU.F β) :
    Bh.ofProperCoveringUniformizer hP hC hU hm (Bh.toProperCoveringUniformizer hP hC hU hm Ψh hmem)
      = Ψh := rfl

theorem toProperCoveringUniformizer_of {β : B.Obj}
    (V : @ProperCoveringUniformizer (Bh.gctA hP hC hU hm) (Bh.gctB hU hm) P β)
    (hmem : Bh.ofProperCoveringUniformizer hP hC hU hm V ∈ Bh.hatU.F β) :
    Bh.toProperCoveringUniformizer hP hC hU hm (Bh.ofProperCoveringUniformizer hP hC hU hm V) hmem
      = V := rfl

/-- **Theorem 19.7.28 (3): `F̂` as a proper covering uniformizer construction** (Definition
17.8.12) of `P : A → B` viewed as a proper covering functor of GCTs. -/
def toProperCoveringConstruction :
    @ProperCoveringUniformizerConstruction (Bh.gctA hP hC hU hm) (Bh.gctB hU hm) P where
  F β := {V | Bh.ofProperCoveringUniformizer hP hC hU hm V ∈ Bh.hatU.F β}

/-- The members of `toProperCoveringConstruction` are exactly the `Ψ̂ ∈ F̂(β)`. -/
theorem mem_toProperCoveringConstruction_iff {β : B.Obj}
    (V : @ProperCoveringUniformizer (Bh.gctA hP hC hU hm) (Bh.gctB hU hm) P β) :
    V ∈ (Bh.toProperCoveringConstruction hP hC hU hm).F β ↔
      ∃ (Ψh : CoveringUniformizer P β) (hmem : Ψh ∈ Bh.hatU.F β),
        V = Bh.toProperCoveringUniformizer hP hC hU hm Ψh hmem :=
  ⟨fun h => ⟨_, h, rfl⟩, by rintro ⟨Ψh, hmem, rfl⟩; exact hmem⟩

/-- The uniformizer `Ψ̂ ∈ F̂(β)` of a member of `toProperCoveringConstruction`. -/
def unifOf (U : (Bh.toProperCoveringConstruction hP hC hU hm).Unif) : Bh.hatU.Unif :=
  ⟨U.1.1, Bh.ofProperCoveringUniformizer hP hC hU hm U.unif, U.2⟩

/-- **The polyfold structure of `B`** (Theorem 19.5.3 (2)) on the GCT `B` of Theorem 19.7.25 (2). -/
abbrev polyfoldB : (Bh.gctB hU hm).PolyfoldConstruction :=
  Bh.toBasic.toPolyfoldConstruction hm

theorem polyfoldB_F (β : B.Obj) :
    (Bh.polyfoldB hU hm).F β =
      (Bh.toProperCoveringConstruction hP hC hU hm).toUniformizerConstruction.F β := by
  ext L
  constructor
  · rintro ⟨Ψh, hmem, hL⟩
    refine ⟨Bh.toProperCoveringUniformizer hP hC hU hm Ψh hmem, hmem, ?_⟩
    obtain ⟨L₀, hL₀⟩ := L
    subst hL
    rfl
  · rintro ⟨V, hV, rfl⟩
    exact ⟨_, hV, rfl⟩

/-- **Theorem 19.7.28 (3): the proper polyfold covering structure `(F̂, M)`** (Definition
17.8.13) for `P : A → B` viewed as a proper covering functor of GCTs (Theorem 19.7.25 (3)):
`F̂` (`toProperCoveringConstruction`), the polyfold structure of `B` of Theorem 19.5.3 (2), and
the M-polyfolds `M(Ψ̂, Ψ̂')` of Proposition 19.7.26, with the structure maps of Theorem
19.7.28 (1). -/
def toProperPolyfoldCoveringStructure :
    @ProperPolyfoldCoveringStructure (Bh.gctA hP hC hU hm) (Bh.gctB hU hm) P where
  toC := Bh.toProperCoveringConstruction hP hC hU hm
  SB := Bh.polyfoldB hU hm
  SB_F := Bh.polyfoldB_F hP hC hU hm
  topH U U' := Bh.topologicalSpaceMHat (Bh.unifOf hP hC hU hm U) (Bh.unifOf hP hC hU hm U')
  t2H U U' := Bh.t2Space_MHat hP (Bh.unifOf hP hC hU hm U) (Bh.unifOf hP hC hU hm U')
  paraH U U' := Bh.paracompactSpace_MHat hP (Bh.unifOf hP hC hU hm U) (Bh.unifOf hP hC hU hm U')
  MH U U' := Bh.hatPolyfold hP (Bh.unifOf hP hC hU hm U) (Bh.unifOf hP hC hU hm U')
  isLocalScDiffeo_src U U' :=
    Bh.isLocalScDiffeo_srcHat hP (Bh.unifOf hP hC hU hm U) (Bh.unifOf hP hC hU hm U')
  isLocalScDiffeo_tgt U U' :=
    Bh.isLocalScDiffeo_tgtHat hP hC (Bh.unifOf hP hC hU hm U) (Bh.unifOf hP hC hU hm U')
  isScSmoothMap_unit U := Bh.isScSmoothMap_unitHat hP (Bh.unifOf hP hC hU hm U)
  isScSmoothMap_inv U U' :=
    Bh.isScSmoothMap_invHat hP hC (Bh.unifOf hP hC hU hm U) (Bh.unifOf hP hC hU hm U')
  isScSmoothMap_mul U U' U'' :=
    Bh.isScSmoothMap_mulHat hP hC (Bh.unifOf hP hC hU hm U) (Bh.unifOf hP hC hU hm U')
      (Bh.unifOf hP hC hU hm U'')
  isLocalScDiffeo_p U U' :=
    Bh.isLocalScDiffeo_pB hP (Bh.unifOf hP hC hU hm U) (Bh.unifOf hP hC hU hm U')

/-- **Theorem 19.7.28 (3): `P` is a proper polyfold covering functor** (Definition 17.8.13). -/
def toProperPolyfoldCoveringFunctor :
    ProperPolyfoldCoveringFunctor (Bh.gctA hP hC hU hm) (Bh.gctB hU hm) where
  P := P
  isProperCovering := Bh.theorem_19_7_25_three_hyp hP hC hU hm
  S := Bh.toProperPolyfoldCoveringStructure hP hC hU hm

/-- **2021 Theorem 19.7.28 (2), p. 928**, under `IsCompatible`: `A` and `B` with their natural
topologies (metrizable) are GCTs and `P` is a proper covering functor of GCTs (Definition
17.8.1); this is Theorem 19.7.25 (2), (3). -/
theorem theorem_19_7_28_two_hyp :
    (Bh.gctA hP hC hU hm).toGroupoidalCategory = A ∧
      (Bh.gctA hP hC hU hm).top = Bh.natTopA hP hC hU ∧
      (Bh.gctB hU hm).toGroupoidalCategory = B ∧
      (Bh.gctB hU hm).top = Bh.toBasic.natTop hU.toBasic ∧
      @MetrizableSpace _ (Bh.natTopA hP hC hU) ∧ @MetrizableSpace _ (Bh.toBasic.natTop hU.toBasic) ∧
      @GroupoidFunctor.IsProperCoveringGCT (Bh.gctA hP hC hU hm) (Bh.gctB hU hm) P :=
  ⟨rfl, rfl, rfl, rfl, (Bh.theorem_19_7_25_one_hyp hP hC hU hm).1, hm,
    Bh.theorem_19_7_25_three_hyp hP hC hU hm⟩

/-- **2021 Theorem 19.7.28 (3), pp. 928–929**, under `IsCompatible`: `F̂` is a functor assigning to
`β` a set of proper covering uniformizers at `β` (Definition 17.8.10), exactly the `Ψ̂ ∈ F̂(β)`;
the transition construction is upgraded to M-polyfold structures on the `M(Ψ, Ψ')` (Theorem
19.5.3 (2)) and the `M(Ψ̂, Ψ̂')` (Proposition 19.7.26) for which `p` is a surjective local
sc-diffeomorphism fitting into the structural diagrams: a proper polyfold covering structure
`(F̂, M)` (Definition 17.8.13, `toProperPolyfoldCoveringStructure`), and `P` is a proper
polyfold covering functor. -/
theorem theorem_19_7_28_three_hyp :
    (∀ (β : B.Obj) (V : @ProperCoveringUniformizer (Bh.gctA hP hC hU hm) (Bh.gctB hU hm) P β),
      V ∈ (Bh.toProperPolyfoldCoveringStructure hP hC hU hm).toC.F β ↔
        ∃ (Ψh : CoveringUniformizer P β) (hmem : Ψh ∈ Bh.hatU.F β),
          V = Bh.toProperCoveringUniformizer hP hC hU hm Ψh hmem) ∧
    (Bh.toProperPolyfoldCoveringStructure hP hC hU hm).SB = Bh.toBasic.toPolyfoldConstruction hm ∧
    (∀ U U' : (Bh.toProperPolyfoldCoveringStructure hP hC hU hm).toC.Unif,
      (Bh.toProperPolyfoldCoveringStructure hP hC hU hm).MH U U' =
        Bh.hatPolyfold hP (Bh.unifOf hP hC hU hm U) (Bh.unifOf hP hC hU hm U') ∧
      Surjective fun a => (ProperCoveringUniformizer.transMap U.unif U'.unif a :
        (Bh.toProperPolyfoldCoveringStructure hP hC hU hm).BaseTr U U')) ∧
    (Bh.toProperPolyfoldCoveringFunctor hP hC hU hm).P = P :=
  ⟨fun _ V => Bh.mem_toProperCoveringConstruction_iff hP hC hU hm V, rfl,
    fun U U' => ⟨rfl, (Bh.proposition_19_7_14 hP (Bh.unifOf hP hC hU hm U)
      (Bh.unifOf hP hC hU hm U')).2⟩, rfl⟩

/-! ### Theorem 19.7.29 -/

/-- `⟨P, s⟩ : 𝐀 → 𝐁 ₛ×_P A`, `φ̂ ↦ (P(φ̂), s(φ̂))` (Definition 19.7.1 (2)). -/
def fibredMorP (φ : A.Mor) : {q : B.Mor × A.Obj // B.toGroupoidStr.src q.1 = P.obj q.2} :=
  ⟨(P.mor φ, A.toGroupoidStr.src φ), P.src_mor φ⟩

/-- `Γ̂ : M(Ψ̂, Ψ̂') → 𝐀`, `(e, φ̂, e') ↦ φ̂` (19.40). -/
def gammaHat (x y : Bh.hatU.Unif) (a : Bh.MHat x y) : A.Mor := (a : x.Ψh.Trans y.Ψh).mor

/-- `Γ ₛ×_τ̂ Ψ̂ : M(Ψ, Ψ') ₛ×_τ̂ E → 𝐁 ₛ×_P A`, `((o, φ, o'), e) ↦ (φ, Ψ̂(e))` (19.40). -/
def gammaFib (x y : Bh.hatU.Unif) (q : Bh.fibSet x y) :
    {q : B.Mor × A.Obj // B.toGroupoidStr.src q.1 = P.obj q.2} :=
  ⟨((q.1.1 : x.Ψh.Ψ.Trans y.Ψh.Ψ).mor, x.Ψh.hat.obj q.1.2), by
    rw [(q.1.1 : x.Ψh.Ψ.Trans y.Ψh.Ψ).src_mor, x.Ψh.obj_comm]
    exact congrArg x.Ψh.Ψ.obj q.2⟩

/-- **2021 Theorem 19.7.29, pp. 929–930**, under `IsCompatible`: `A` and `B` have natural
polyfold structures (for `B` Theorem 19.5.3 (2), whose footprints cover `|B|`; for `A` the
M-polyfolds `M(Ψ̂, Ψ̂')` of the proper polyfold covering structure of Theorem 19.7.28 (3), the
`|Ψ̂|` being open embeddings whose images cover `|A|`), and for `Ψ̂ ∈ F̂(β)`, `Ψ̂' ∈ F̂(β')`:
(1) the local representative of `P` with respect to `Ψ̂` is `τ̂` (`P ∘ Ψ̂ = Ψ ∘ τ̂` on objects and
morphisms, `τ̂` an sc-smooth functor which is a proper covering functor, Definition 8.5.1);
(2) the diagram (19.40) commutes, `⟨P, s⟩` maps the image of `Γ̂` onto the image of
`Γ ₛ×_τ̂ Ψ̂`, `Γ ₛ×_τ̂ Ψ̂` is injective, so that `⟨p, s⟩ = (Γ ₛ×_τ̂ Ψ̂)⁻¹ ∘ ⟨P, s⟩ ∘ Γ̂`, which is
sc-smooth. -/
theorem theorem_19_7_29_hyp (x y : Bh.hatU.Unif) :
    haveI := Bh.t2Space_MHat hP
    haveI := Bh.paracompactSpace_MHat hP
    ((Bh.toBasic.toPolyfoldConstruction hm).HasCoveringUniformizers ∧
      (∀ z : Bh.hatU.Unif, @IsOpenEmbedding _ _ _ (Bh.natTopA hP hC hU) z.Ψh.hat.orbitMap) ∧
      (⋃ z : Bh.hatU.Unif, range z.Ψh.hat.orbitMap) = univ ∧
      Nonempty (ProperPolyfoldCoveringFunctor (Bh.gctA hP hC hU hm) (Bh.gctB hU hm))) ∧
    ((∀ e, P.obj (x.Ψh.hat.obj e) = x.Ψh.Ψ.obj (x.Ψh.τ.obj e)) ∧
      (∀ φ, P.mor (x.Ψh.hat.mor φ) = x.Ψh.Ψ.mor (x.Ψh.τ.mor φ)) ∧
      x.Ψh.τ.IsProperCovering ∧ x.Ψh.E.PMor.IsScSmoothMap (actionEpGroupoid x.Ψh.Ψ.smooth_smul).PMor
        x.Ψh.τ.mor) ∧
    ((∀ a : Bh.MHat x y, Bh.gammaFib x y (Bh.toFibSet x y a) = fibredMorP (Bh.gammaHat x y a)) ∧
      fibredMorP '' range (Bh.gammaHat x y) = range (Bh.gammaFib x y) ∧
      Injective (Bh.gammaFib x y) ∧
      (∀ (a : Bh.MHat x y) (q : Bh.fibSet x y),
        Bh.gammaFib x y q = fibredMorP (Bh.gammaHat x y a) ↔ q = Bh.toFibSet x y a) ∧
      (Bh.hatPolyfold hP x y).IsScSmoothMap (Bh.fibPolyfold x y) (Bh.toFibSet x y)) := by
  have := Bh.t2Space_MHat hP
  have := Bh.paracompactSpace_MHat hP
  have hcomm : ∀ a : Bh.MHat x y,
      Bh.gammaFib x y (Bh.toFibSet x y a) = fibredMorP (Bh.gammaHat x y a) := fun a =>
    Subtype.ext (Prod.ext rfl (a : x.Ψh.Trans y.Ψh).src_mor.symm)
  have hinj : Injective (Bh.gammaFib x y) := by
    rintro ⟨⟨h, e⟩, hq⟩ ⟨⟨h', e'⟩, hq'⟩ hhe
    have hm' : (h : x.Ψh.Ψ.Trans y.Ψh.Ψ).mor = (h' : x.Ψh.Ψ.Trans y.Ψh.Ψ).mor :=
      congrArg (fun r => r.1.1) hhe
    have he : e = e' := x.Ψh.injective_hat (congrArg (fun r => r.1.2) hhe)
    subst he
    have hs : (h : x.Ψh.Ψ.Trans y.Ψh.Ψ).src = (h' : x.Ψh.Ψ.Trans y.Ψh.Ψ).src := hq.trans hq'.symm
    have ht : (h : x.Ψh.Ψ.Trans y.Ψh.Ψ).tgt = (h' : x.Ψh.Ψ.Trans y.Ψh.Ψ).tgt :=
      y.Ψh.Ψ.injective_obj ((h : x.Ψh.Ψ.Trans y.Ψh.Ψ).tgt_mor.symm.trans
        ((congrArg B.toGroupoidStr.tgt hm').trans (h' : x.Ψh.Ψ.Trans y.Ψh.Ψ).tgt_mor))
    have : h = h' := TransitionSet.ext hs hm' ht
    subst this
    rfl
  refine ⟨⟨BasicConstruction.hasCoveringUniformizers_toPolyfoldConstruction hm,
    fun z => Bh.lemma_19_7_17_two_hyp hP hC hU z, ?_,
    ⟨Bh.toProperPolyfoldCoveringFunctor hP hC hU hm⟩⟩,
    ⟨x.Ψh.obj_comm, x.Ψh.mor_comm,
      x.Ψh.model.isProperCovering (x.Ψh.finite_fiber_τ hP x.Ψh.model.pt),
      x.Ψh.τ.isScSmoothMap_mor⟩,
    hcomm, ?_, hinj, fun a q => ⟨fun h => hinj (h.trans (hcomm a).symm), fun h => h ▸ hcomm a⟩,
    (Bh.isScDiffeoOn_toFibSet hP x y).isScSmoothOn⟩
  · refine eq_univ_of_forall fun w => mem_iUnion.2 ?_
    obtain ⟨β, hβ, Ψh, hmem⟩ := hU (P.orbitMap w)
    obtain ⟨e, he⟩ := exists_hat_of_orbitMap_eq_pt hP Ψh hβ
    exact ⟨⟨β, Ψh, hmem⟩, GroupoidStr.π _ e, he⟩
  · ext r
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨Bh.toFibSet x y a, hcomm a⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨a, ha⟩ := (Bh.fibSetHomeomorph hP x y).surjective q
      refine ⟨Bh.gammaHat x y a, ⟨a, rfl⟩, ?_⟩
      rw [← hcomm a]
      exact congrArg (Bh.gammaFib x y) ha

end GCT

end CoveringBasicConstruction

end GroupoidalCategory

end Polyfold
