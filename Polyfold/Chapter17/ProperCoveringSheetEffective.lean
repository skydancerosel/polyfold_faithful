import Polyfold.Chapter17.ProperCoveringSheetCounterexample
import Polyfold.Chapter8.ProperCoveringFibredMap

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8:
**Remark 17.8.11**, second part (p. 835), for a proper covering uniformizer (**Definition
17.8.10**, pp. 834–835) whose model (**Definition 17.8.4**, p. 831) has a disconnected `O`, with
effective groupoids (**Definition 7.2.1**).  Numbers and pages are the 2021 text's.

# The sheets of a proper covering uniformizer need a connected model, also for effective `B`

## The text, paraphrased

(Remark 17.8.11) `Ψ : G ⋉ O_β → B` is a uniformizer, `Ψ̂ : E → A` is not; however the
restrictions of `Ψ̂` to `G_α ⋉ O_α` for `α ∈ P⁻¹(β)` are uniformizers.

## What is formalized

* `isEffective_sheetEp_units`: for every discrete `ℤ/2`-set `S`, the translation ep-groupoid
  `ℤ/2 ⋉ (S × ℝ)` (diagonal action, the reflection `x ↦ −x` on `ℝ`) is effective.
* The example (namespace `TwistedLine`), with `Pt = {base, other}` and `Sheet = {a, b}` from
  `TwistedSheet`:
  * `O = Pt × ℝ`, two copies of `ℝ`, with `ℤ/2` acting by `(c, x) ↦ (c, −x)`; `ō = (base, 0)`.
  * `E = ℤ/2 ⋉ ((Sheet × Pt) × ℝ)`, where `−1` sends `((s, base), x)` to `((s, base), −x)` and
    `((s, other), x)` to `((s', other), −x)`, `s'` the other sheet; `τ̂((s, c), x) = (c, x)`.
  * `model`: Definition 17.8.4, with `U((s, base), 0) = {s} × Pt × ℝ`, `τ̂⁻¹(ō)` of two points
    (`ncard_fiber`) and `O` not connected (`not_connected_model`).
  * `isProperCoveringGCT_P`: Definition 17.8.1 for `P = τ̂ : A → B`, `A = E`, `B = ℤ/2 ⋉ O`.
  * `unif`: Definition 17.8.10, with `Ψ = 1` and `Ψ̂ = 1`.
  * `isEffective_BEp`, `isEffective_E`: `B` (the ep-groupoid `G ⋉ O` of `Ψ`) and `E` are effective;
    `nondegenerate`: `(−1, y₀)` is a non-unit automorphism of `y₀ = ((a, base), 0)` over a
    non-unit automorphism of `ō`.
* `TwistedLine.not_exists_uniformizer`: the full subcategory on `Ψ̂(U(y₀))` is not the image of
  any uniformizer of `A` (`GroupoidalCategory.not_exists_uniformizer_range`): `y₀` has the
  automorphism `(−1, y₀)`, while the only morphism from `((a, other), 0)` into `U(y₀)` is its unit.
* **`remark_17_8_11_two_disconnected_effective`**: without the connectedness of the model (the
  standing reading), the second part of Remark 17.8.11 does not hold as we read it, even when
  `G ⋉ O_β` and `E` are effective, and even with "uniformizer" in the weakest sense (any
  `Φ : G ⋉ O → A` of Definition 17.1.1 with the right image, not necessarily centred or local).

## Readings

* `O_α` is the sheet `U(y)` of the point `y ∈ τ̂⁻¹(ō)` over `α = Ψ̂(y)`, as in
  `ProperCoveringSheetUniformizer.lean` and `ProperCoveringSheetCounterexample.lean`; a uniformizer
  "restricting `Ψ̂`" has image `Ψ̂(U(y))`.
* Connectedness of the model is the standing reading of the remark: its notation `O_α`,
  `G_α ⋉ O_α` is that of the construction (17.93)–(17.98), with which a Definition 17.8.4 model is
  identified on pp. 832–834 under "Suppose further that `O` is connected".  With it
  (`hO_conn`, available by Proposition 17.8.6) the statement holds: `remark_17_8_11_two`.  The
  present file records that the condition is not a consequence of effectiveness:
  `TwistedSheet` has a trivial action on a discrete `O`, here the action of `G` on `O` and the
  groupoids `B`, `E` are effective and `O` is 1-dimensional.
* "Effective" is Definition 7.2.1 for the ep-groupoids `G ⋉ O_β` and `E`.  For `B` itself (a GCT,
  Definition 17.1.1) effectiveness is not defined; in the example `B = G ⋉ O` as a GCT, so
  `G ⋉ O_β` effective is `B` effective.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

open EpGroupoid EpGroupoid.Examples

/-! ### Effectiveness of the reflection on sheets -/

/-- **`ℤ/2 ⋉ (S × ℝ)` is effective** (Definition 7.2.1) for every discrete `ℤ/2`-set `S`, with
`ℤ/2` acting on `ℝ` by the reflection. -/
theorem isEffective_sheetEp_units (S : Type) [TopologicalSpace S] [DiscreteTopology S]
    [MulAction ℤˣ S] [ParacompactSpace (S × (Fin 1 → ℝ))] :
    (sheetEp isScSmoothMap_units_smul S).IsEffective := by
  intro x g hg W hW hgW
  have h2 : g.val.2 = x := g.src_val
  have ht : g.val.1 • g.val.2 = x := g.tgt_val
  have h1 : g.val.1 = -1 := (Int.units_eq_one_or _).resolve_left fun h =>
    hg (GroupoidStr.Isotropy.ext (Prod.ext h h2))
  rw [h1, h2] at ht
  have hx1 : ((-1 : ℤˣ) • x.1) = x.1 := congrArg Prod.fst ht
  have hx2 : x.2 = 0 := by
    have h := congrArg Prod.snd ht
    change (-1 : ℤˣ) • x.2 = x.2 at h
    rw [units_smul_rn_neg_one] at h
    exact neg_eq_self.1 h
  have hS : IsOpen {v : Fin 1 → ℝ | ((-1 : ℤˣ), (x.1, v)) ∈ W} :=
    hW.preimage (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hg0 : g.val = ((-1 : ℤˣ), (x.1, (0 : Fin 1 → ℝ))) :=
    Prod.ext h1 (h2.trans (Prod.ext rfl hx2))
  have h0S : (0 : Fin 1 → ℝ) ∈ {v : Fin 1 → ℝ | ((-1 : ℤˣ), (x.1, v)) ∈ W} := by
    change ((-1 : ℤˣ), (x.1, (0 : Fin 1 → ℝ))) ∈ W
    rw [← hg0]
    exact hgW
  have hN : {v : Fin 1 → ℝ | ((-1 : ℤˣ), (x.1, v)) ∈ W} ∈ 𝓝[≠] (0 : Fin 1 → ℝ) :=
    mem_nhdsWithin_of_mem_nhds (hS.mem_nhds h0S)
  obtain ⟨v, hvW, hv0⟩ := Filter.nonempty_of_mem (Filter.inter_mem hN self_mem_nhdsWithin)
  refine ⟨((-1 : ℤˣ), (x.1, v)), hvW, ?_⟩
  change (x.1, v) ≠ (-1 : ℤˣ) • (x.1, v)
  intro h
  have h' := congrArg Prod.snd h
  change v = (-1 : ℤˣ) • v at h'
  rw [units_smul_rn_neg_one] at h'
  exact hv0 (self_eq_neg.1 h')

namespace TwistedLine

open TwistedSheet (Pt Sheet twistSmul)

/-- The diagonal action on `O = Pt × ℝ` (trivial on `Pt`, the reflection on `ℝ`) is sc-smooth. -/
theorem isScSmoothMap_smulB (k : ℤˣ) :
    ((discretePolyfold Pt).prod (rnPolyfold 1)).IsScSmoothMap
      ((discretePolyfold Pt).prod (rnPolyfold 1)) fun o : Pt × (Fin 1 → ℝ) => k • o :=
  isScSmoothMap_sheet_smul' isScSmoothMap_units_smul Pt k

/-- The diagonal action on `(Sheet × Pt) × ℝ` (the twisted action of `TwistedSheet` on
`Sheet × Pt`, the reflection on `ℝ`) is sc-smooth. -/
theorem isScSmoothMap_smulE (k : ℤˣ) :
    ((discretePolyfold (Sheet × Pt)).prod (rnPolyfold 1)).IsScSmoothMap
      ((discretePolyfold (Sheet × Pt)).prod (rnPolyfold 1))
      fun e : (Sheet × Pt) × (Fin 1 → ℝ) => k • e :=
  isScSmoothMap_sheet_smul' isScSmoothMap_units_smul (Sheet × Pt) k

/-- `G ⋉ O = ℤ/2 ⋉ (Pt × ℝ)`, two copies of `ℤ/2 ⋉ ℝ` (the reflection). -/
abbrev BEp : EpGroupoid (Pt × (Fin 1 → ℝ)) (ℤˣ × (Pt × (Fin 1 → ℝ))) :=
  actionEpGroupoid isScSmoothMap_smulB

/-- `E = ℤ/2 ⋉ ((Sheet × Pt) × ℝ)`: over `base` the sheets are kept, over `other` they are
exchanged. -/
abbrev E : EpGroupoid ((Sheet × Pt) × (Fin 1 → ℝ)) (ℤˣ × ((Sheet × Pt) × (Fin 1 → ℝ))) :=
  actionEpGroupoid isScSmoothMap_smulE

/-- The object map `((s, c), x) ↦ (c, x)`. -/
def τobj (e : (Sheet × Pt) × (Fin 1 → ℝ)) : Pt × (Fin 1 → ℝ) := (e.1.2, e.2)

/-- `τ̂ : E → O` on objects is sc-smooth. -/
theorem isScSmoothMap_τobj :
    E.PObj.IsScSmoothMap BEp.PObj τobj :=
  isScSmoothMap_prod_discrete_iff.2 fun q =>
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete q.2) MPolyfold.isScSmoothMap_id

/-- `τ̂ : E → G ⋉ O`, `((s, c), x) ↦ (c, x)`, `(k, e) ↦ (k, τ̂(e))`. -/
def τ : EpFunctor E BEp where
  obj := τobj
  mor φ := (φ.1, τobj φ.2)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := isScSmoothMap_τobj
  isScSmoothMap_mor := MPolyfold.IsScSmoothOn.prodMk (MPolyfold.isScSmoothMap_fst _ _)
    (isScSmoothMap_τobj.comp (MPolyfold.isScSmoothMap_snd _ _))

/-- The sheet section `(c, x) ↦ ((s, c), x)`. -/
def σs (s : Sheet) (o : Pt × (Fin 1 → ℝ)) : (Sheet × Pt) × (Fin 1 → ℝ) := ((s, o.1), o.2)

/-- The sheet section is sc-smooth. -/
theorem isScSmoothMap_σs (s : Sheet) : BEp.PObj.IsScSmoothMap E.PObj (σs s) :=
  isScSmoothMap_prod_discrete_iff.2 fun c =>
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete (s, c)) MPolyfold.isScSmoothMap_id

/-- The sheet `U_s = {((s, c), x)}`. -/
def sheetSet (s : Sheet) : Set ((Sheet × Pt) × (Fin 1 → ℝ)) := {e | e.1.1 = s}

/-- The sheet `U_s` is open. -/
theorem isOpen_sheetSet (s : Sheet) : IsOpen (sheetSet s) :=
  (isOpen_discrete {q : Sheet × Pt | q.1 = s}).preimage continuous_fst

/-- `τ̂ : U_s → O` is an sc-diffeomorphism with inverse `σs s`. -/
theorem isScDiffeoOn_sheet (s : Sheet) :
    E.PObj.IsScDiffeoOn BEp.PObj τobj (σs s) (sheetSet s) univ where
  isScSmoothOn := isScSmoothMap_τobj.mono (isOpen_sheetSet s) (subset_univ _)
  isScSmoothOn_inv := isScSmoothMap_σs s
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := fun _ _ => rfl
  left_inv := fun e he => by
    obtain ⟨⟨s', c⟩, x⟩ := e
    change s' = s at he
    subst he
    rfl
  right_inv := fun _ _ => rfl

/-- Definition 17.8.4 (3): `ψ ↦ (τ̂(ψ), s(ψ))` is bijective onto `(G ⋉ O) ₛ×_τ̂ E`. -/
theorem bijective_fibredMap : Bijective τ.fibredMap := by
  refine ⟨fun φ ψ h => ?_, fun q => ⟨(q.1.1.1, q.1.2), Subtype.ext ?_⟩⟩
  · have h1 := congrArg (fun q => q.1.1.1) h
    have h2 := congrArg (fun q => q.1.2) h
    exact Prod.ext h1 h2
  · obtain ⟨⟨⟨g, o⟩, p⟩, hq⟩ := q
    change o = τobj p at hq
    subst hq
    rfl

/-- The point `ō = (base, 0)`. -/
abbrev pt₀ : Pt × (Fin 1 → ℝ) := (.base, 0)

/-- `τ̂(y) = ō` if and only if `y = ((s, base), 0)`. -/
theorem mem_fiber_iff' (y : (Sheet × Pt) × (Fin 1 → ℝ)) :
    y ∈ τ.obj ⁻¹' {pt₀} ↔ y.1.2 = .base ∧ y.2 = 0 := by
  change τobj y = pt₀ ↔ _
  exact Prod.ext_iff

/-- **A proper covering model with a disconnected `O` and effective groupoids** (Definition
17.8.4, p. 831): `τ̂ : E → ℤ/2 ⋉ (Pt × ℝ)`, `ō = (base, 0)`, `U((s, base), 0) = {s} × Pt × ℝ`,
`σ_{((s, base), 0)}(c, x) = ((s, c), x)`. -/
def model : ProperCoveringModel τ where
  pt := pt₀
  smul_pt k := Prod.ext rfl (smul_zero k)
  surjective o := ⟨σs .a o, rfl⟩
  isLocalScDiffeo e := ⟨sheetSet e.1.1, univ, σs e.1.1, rfl, isScDiffeoOn_sheet e.1.1⟩
  U y := sheetSet y.1.1
  σ y := σs y.1.1
  mem_U _ _ := rfl
  pairwiseDisjoint_U := by
    intro y hy z hz hyz
    refine Set.disjoint_left.2 fun p hp hp' => hyz ?_
    rw [mem_fiber_iff'] at hy hz
    exact Prod.ext (Prod.ext ((hp : p.1.1 = y.1.1).symm.trans hp') (hy.1.trans hz.1.symm))
      (hy.2.trans hz.2.symm)
  iUnion_U := by
    refine eq_univ_of_forall fun p => ?_
    simp only [mem_iUnion, exists_prop]
    exact ⟨((p.1.1, .base), 0), (mem_fiber_iff' _).2 ⟨rfl, rfl⟩, rfl⟩
  isScDiffeoOn_U y _ := isScDiffeoOn_sheet y.1.1
  isScDiffeo_fibredMap := τ.isScDiffeo_fibredMap_of_bijective bijective_fibredMap

/-! ### The GCTs and Definition 17.8.1 -/

/-- The GCT `A = E`. -/
abbrev A : GCT.{0} := GCT.translation ℤˣ ((Sheet × Pt) × (Fin 1 → ℝ)) isScSmoothMap_smulE

/-- The GCT `B = ℤ/2 ⋉ (Pt × ℝ)`. -/
abbrev B : GCT.{0} := GCT.translation ℤˣ (Pt × (Fin 1 → ℝ)) isScSmoothMap_smulB

/-- `P = τ̂ : A → B` as a functor of GCTs. -/
abbrev P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr := τ.toGroupoidFunctor

/-- `−1 ∗ ((s, c), x) = (−1 ∗ (s, c), −x)`. -/
theorem smul_neg_one (e : (Sheet × Pt) × (Fin 1 → ℝ)) :
    (-1 : ℤˣ) • e = (twistSmul (-1) e.1, -e.2) := by
  change ((-1 : ℤˣ) • e.1, (-1 : ℤˣ) • e.2) = _
  rw [units_smul_rn_neg_one]
  rfl

/-- The lift to `|A|` of a function invariant under `−1`. -/
def liftA {X : Type} (f : (Sheet × Pt) × (Fin 1 → ℝ) → X)
    (hf : ∀ e, f ((-1 : ℤˣ) • e) = f e) : A.OrbitSpace → X :=
  Quotient.lift f fun _ _ ⟨φ, ha, hb⟩ => by
    rw [← ha, ← hb]
    change f φ.2 = f (φ.1 • φ.2)
    rcases Int.units_eq_one_or φ.1 with h | h <;> rw [h]
    · rw [one_smul]
    · exact (hf _).symm

/-- The lift of a continuous invariant function is continuous. -/
theorem continuous_liftA {X : Type} [TopologicalSpace X] {f : (Sheet × Pt) × (Fin 1 → ℝ) → X}
    (hf : ∀ e, f ((-1 : ℤˣ) • e) = f e) (hc : Continuous f) : Continuous (liftA f hf) :=
  hc.quotient_lift _

/-- The lift to `|B|` of a function invariant under `−1`. -/
def liftB {X : Type} (f : Pt × (Fin 1 → ℝ) → X) (hf : ∀ o, f ((-1 : ℤˣ) • o) = f o) :
    B.OrbitSpace → X :=
  Quotient.lift f fun _ _ ⟨φ, ha, hb⟩ => by
    rw [← ha, ← hb]
    change f φ.2 = f (φ.1 • φ.2)
    rcases Int.units_eq_one_or φ.1 with h | h <;> rw [h]
    · rw [one_smul]
    · exact (hf _).symm

/-- The lift of a continuous invariant function is continuous. -/
theorem continuous_liftB {X : Type} [TopologicalSpace X] {f : Pt × (Fin 1 → ℝ) → X}
    (hf : ∀ o, f ((-1 : ℤˣ) • o) = f o) (hc : Continuous f) : Continuous (liftB f hf) :=
  hc.quotient_lift _

/-- `|((s, c), x)| ↦ c`. -/
def ptA : A.OrbitSpace → Pt := liftA (fun e => e.1.2) fun _ => rfl

/-- `|((s, base), x)| ↦ s`, `|((s, other), x)| ↦ a`. -/
def sheetA : A.OrbitSpace → Sheet :=
  liftA (fun e => if e.1.2 = .base then e.1.1 else .a) fun e => by
    obtain ⟨⟨s, c⟩, x⟩ := e
    rw [smul_neg_one]
    cases c <;> simp [twistSmul]

/-- `|((a, other), x)| ↦ x`, `|((b, other), x)| ↦ −x`, `|((s, base), x)| ↦ 0`. -/
def heightA : A.OrbitSpace → ℝ :=
  liftA (fun e => if e.1.2 = .other then (if e.1.1 = .a then e.2 0 else -(e.2 0)) else 0)
    fun e => by
      obtain ⟨⟨s, c⟩, x⟩ := e
      rw [smul_neg_one]
      cases c <;> cases s <;> simp [twistSmul, TwistedSheet.Sheet.swap]

/-- `|(c, x)| ↦ c`. -/
def ptB : B.OrbitSpace → Pt := liftB (fun o => o.1) fun _ => rfl

/-- `|(c, x)| ↦ |x|`. -/
def absB : B.OrbitSpace → ℝ := liftB (fun o => |o.2 0|) fun o => by
  change |((-1 : ℤˣ) • o.2) 0| = _
  rw [units_smul_rn_neg_one]
  simp

/-- `ptA` is continuous. -/
theorem continuous_ptA : Continuous ptA := continuous_liftA _ (continuous_snd.comp continuous_fst)

/-- `sheetA` is continuous. -/
theorem continuous_sheetA : Continuous sheetA :=
  continuous_liftA _ ((continuous_of_discreteTopology
    (f := fun q : Sheet × Pt => if q.2 = .base then q.1 else .a)).comp continuous_fst)

/-- `heightA` is continuous. -/
theorem continuous_heightA : Continuous heightA :=
  continuous_liftA _ (continuous_prod_of_discrete_left.2 fun q => by
    obtain ⟨s, c⟩ := q
    cases s <;> cases c <;> simp only [reduceCtorEq, ↓reduceIte] <;> fun_prop)

/-- `ptB` is continuous. -/
theorem continuous_ptB : Continuous ptB := continuous_liftB _ continuous_fst

/-- `absB` is continuous. -/
theorem continuous_absB : Continuous absB :=
  continuous_liftB _ ((continuous_apply 0).comp continuous_snd).abs

/-- `ptA |((s, c), x)| = c`. -/
@[simp] theorem ptA_π (e : (Sheet × Pt) × (Fin 1 → ℝ)) : ptA (A.π e) = e.1.2 := rfl

/-- `sheetA |((s, base), x)| = s`. -/
@[simp] theorem sheetA_π_base (s : Sheet) (x : Fin 1 → ℝ) : sheetA (A.π ((s, .base), x)) = s := rfl

/-- `heightA |((a, other), x)| = x`. -/
@[simp] theorem heightA_π_a (x : Fin 1 → ℝ) : heightA (A.π ((.a, .other), x)) = x 0 := rfl

/-- `heightA |((b, other), x)| = −x`. -/
@[simp] theorem heightA_π_b (x : Fin 1 → ℝ) : heightA (A.π ((.b, .other), x)) = -x 0 := rfl

/-- `|P|(|e|) = |τ̂(e)|`. -/
theorem orbitMap_π (e : (Sheet × Pt) × (Fin 1 → ℝ)) : P.orbitMap (A.π e) = B.π (τobj e) := rfl

/-- `ptB ∘ |P| = ptA`. -/
theorem ptB_orbitMap (w : A.OrbitSpace) : ptB (P.orbitMap w) = ptA w :=
  Quotient.inductionOn w fun _ => rfl

/-- Over `other`, `absB ∘ |P| = |heightA|`. -/
theorem absB_orbitMap {w : A.OrbitSpace} (hw : ptA w = .other) :
    absB (P.orbitMap w) = |heightA w| := by
  induction w using Quotient.inductionOn with
  | h e =>
    obtain ⟨⟨s, c⟩, x⟩ := e
    change c = .other at hw
    subst hw
    cases s
    · rfl
    · change |x 0| = |-(x 0)|
      rw [abs_neg]

/-- Every orbit over `|(c, x)|` is `|((s, c), x)|` for some sheet `s`. -/
theorem exists_eq_of_orbitMap {y : A.OrbitSpace} {c : Pt} {x : Fin 1 → ℝ}
    (hy : P.orbitMap y = B.π (c, x)) : ∃ s : Sheet, y = A.π ((s, c), x) := by
  induction y using Quotient.inductionOn with
  | h e =>
    obtain ⟨⟨k, o⟩, hs, ht⟩ := (B.π_eq_π_iff).1 hy
    change o = τobj e at hs
    change k • o = (c, x) at ht
    subst hs
    refine ⟨(k • e).1.1, (A.π_eq_π_iff).2 ⟨(k, e), rfl, ?_⟩⟩
    change k • e = (((k • e).1.1, c), x)
    have h1 : (k • e).1.2 = c := congrArg Prod.fst ht
    have h2 : (k • e).2 = x := congrArg Prod.snd ht
    rw [← h1, ← h2]

/-- `|((b, other), x)| = |((a, other), −x)|`. -/
theorem π_b_other (x : Fin 1 → ℝ) : A.π ((.b, .other), x) = A.π ((.a, .other), -x) :=
  (A.π_eq_π_iff).2 ⟨((-1 : ℤˣ), ((.b, .other), x)), rfl, by
    change (-1 : ℤˣ) • (((Sheet.b, Pt.other), x) : (Sheet × Pt) × (Fin 1 → ℝ)) = _
    rw [smul_neg_one]
    rfl⟩

/-- `τ̂` is continuous on objects. -/
theorem continuous_τobj : Continuous τobj :=
  (continuous_snd.comp continuous_fst).prodMk continuous_snd

/-- **`P = τ̂` is a proper covering functor of GCTs** (Definition 17.8.1, p. 828).  Over
`|(base, x)|` the two orbits `|((a, base), x)|`, `|((b, base), x)|` lie in the disjoint open sets
`{sheetA = a}`, `{sheetA = b}`; over `|(other, 0)|` there is one orbit; over `|(other, x)|`,
`x ≠ 0`, the two orbits `|((a, other), x)|`, `|((b, other), x)|` lie in the disjoint open sets
`{heightA · x > 0}`, `{heightA · x < 0}` over `{c = other, x ≠ 0}`. -/
theorem isProperCoveringGCT_P : P.IsProperCoveringGCT where
  continuous_orbitMap := (continuous_quot_mk.comp continuous_τobj).quotient_lift _
  surjective_orbitMap z := by
    obtain ⟨o, rfl⟩ : ∃ o, B.π o = z := Quotient.exists_rep z
    exact ⟨A.π (σs .a o), rfl⟩
  finite_fiber β := (finite_range fun s : Sheet => σs s β).subset fun e he => by
    change τobj e = β at he
    subst he
    exact ⟨e.1.1, rfl⟩
  surjective_obj o := ⟨σs .a o, rfl⟩
  evenlyCovered z := by
    obtain ⟨⟨c, x⟩, rfl⟩ : ∃ o, B.π o = z := Quotient.exists_rep z
    have hfib : ∀ y ∈ P.orbitMap ⁻¹' {B.π (c, x)}, ∃ s : Sheet, y = A.π ((s, c), x) :=
      fun y hy => exists_eq_of_orbitMap hy
    have hmem : ∀ s : Sheet, A.π ((s, c), x) ∈ P.orbitMap ⁻¹' {B.π (c, x)} := fun _ => rfl
    have hfin : (P.orbitMap ⁻¹' {B.π (c, x)}).Finite :=
      (finite_range fun s : Sheet => A.π ((s, c), x)).subset fun y hy => by
        obtain ⟨s, rfl⟩ := hfib y hy
        exact ⟨s, rfl⟩
    refine ⟨hfin, ?_⟩
    cases c with
    | base =>
      refine ⟨ptB ⁻¹' {Pt.base}, fun y => ptA ⁻¹' {Pt.base} ∩ sheetA ⁻¹' {sheetA y},
        (isOpen_discrete _).preimage continuous_ptB, (rfl : ptB (B.π (Pt.base, x)) = Pt.base),
        fun y hy => ?_, ?_, ?_⟩
      · obtain ⟨s, rfl⟩ := hfib y hy
        exact ⟨((isOpen_discrete _).preimage continuous_ptA).inter
          ((isOpen_discrete _).preimage continuous_sheetA), rfl, rfl⟩
      · intro y₁ h₁ y₂ h₂ hne
        obtain ⟨s₁, rfl⟩ := hfib y₁ h₁
        obtain ⟨s₂, rfl⟩ := hfib y₂ h₂
        refine Set.disjoint_left.2 fun w hw₁ hw₂ => hne ?_
        have h : s₁ = s₂ := (hw₁.2 : sheetA w = s₁).symm.trans hw₂.2
        rw [h]
      · ext w
        constructor
        · intro hw
          have hw' : ptA w = Pt.base := (ptB_orbitMap w).symm.trans hw
          exact mem_iUnion₂.2 ⟨A.π ((sheetA w, Pt.base), x), hmem _, hw', rfl⟩
        · intro hw
          obtain ⟨y, -, hw', -⟩ := mem_iUnion₂.1 hw
          exact (ptB_orbitMap w).trans hw'
    | other =>
      by_cases hx : x 0 = 0
      · have hx0 : x = 0 := funext fun i => by
          rw [Subsingleton.elim i 0]
          exact hx
        subst hx0
        refine ⟨ptB ⁻¹' {Pt.other}, fun _ => ptA ⁻¹' {Pt.other},
          (isOpen_discrete _).preimage continuous_ptB, (rfl : ptB (B.π (Pt.other, 0)) = Pt.other),
          fun y hy => ?_, ?_, ?_⟩
        · obtain ⟨s, rfl⟩ := hfib y hy
          exact ⟨(isOpen_discrete _).preimage continuous_ptA, rfl⟩
        · refine Set.Subsingleton.pairwise (fun y₁ h₁ y₂ h₂ => ?_) _
          obtain ⟨s₁, rfl⟩ := hfib y₁ h₁
          obtain ⟨s₂, rfl⟩ := hfib y₂ h₂
          have hb : A.π ((Sheet.b, Pt.other), (0 : Fin 1 → ℝ)) =
              A.π ((Sheet.a, Pt.other), (0 : Fin 1 → ℝ)) := by
            rw [π_b_other, neg_zero]
          cases s₁ <;> cases s₂
          · rfl
          · exact hb.symm
          · exact hb
          · rfl
        · ext w
          constructor
          · intro hw
            exact mem_iUnion₂.2 ⟨_, hmem .a, (ptB_orbitMap w).symm.trans hw⟩
          · intro hw
            obtain ⟨y, -, hw'⟩ := mem_iUnion₂.1 hw
            exact (ptB_orbitMap w).trans hw'
      · refine ⟨ptB ⁻¹' {Pt.other} ∩ absB ⁻¹' {t | t ≠ 0},
          fun y => ptA ⁻¹' {Pt.other} ∩ {w | 0 < heightA w * heightA y},
          ((isOpen_discrete _).preimage continuous_ptB).inter
            (isOpen_ne.preimage continuous_absB),
          ⟨(rfl : ptB (B.π (Pt.other, x)) = Pt.other), abs_ne_zero.2 hx⟩,
          fun y hy => ?_, ?_, ?_⟩
        · obtain ⟨s, rfl⟩ := hfib y hy
          refine ⟨((isOpen_discrete _).preimage continuous_ptA).inter
            (isOpen_lt continuous_const (continuous_heightA.mul continuous_const)), rfl, ?_⟩
          cases s
          · exact (show 0 < x 0 * x 0 from mul_self_pos.2 hx)
          · exact (show 0 < -x 0 * -x 0 by rw [neg_mul_neg]; exact mul_self_pos.2 hx)
        · intro y₁ h₁ y₂ h₂ hne
          obtain ⟨s₁, rfl⟩ := hfib y₁ h₁
          obtain ⟨s₂, rfl⟩ := hfib y₂ h₂
          refine Set.disjoint_left.2 fun w hw₁ hw₂ => hne ?_
          have h₁' : 0 < heightA w * heightA (A.π ((s₁, Pt.other), x)) := hw₁.2
          have h₂' : 0 < heightA w * heightA (A.π ((s₂, Pt.other), x)) := hw₂.2
          cases s₁ <;> cases s₂
          · rfl
          · change 0 < heightA w * x 0 at h₁'
            change 0 < heightA w * -x 0 at h₂'
            rw [mul_neg] at h₂'
            linarith
          · change 0 < heightA w * -x 0 at h₁'
            change 0 < heightA w * x 0 at h₂'
            rw [mul_neg] at h₁'
            linarith
          · rfl
        · ext w
          constructor
          · rintro ⟨hw, hw'⟩
            have hw₀ : ptA w = Pt.other := (ptB_orbitMap w).symm.trans hw
            have hw₁ : heightA w ≠ 0 := by
              have h : absB (P.orbitMap w) ≠ 0 := hw'
              rwa [absB_orbitMap hw₀, abs_ne_zero] at h
            by_cases hpos : 0 < heightA w * x 0
            · exact mem_iUnion₂.2 ⟨A.π ((Sheet.a, Pt.other), x), hmem _, hw₀, hpos⟩
            · refine mem_iUnion₂.2 ⟨A.π ((Sheet.b, Pt.other), x), hmem _, hw₀, ?_⟩
              have hne : heightA w * x 0 ≠ 0 := mul_ne_zero hw₁ hx
              change 0 < heightA w * -x 0
              rw [mul_neg, neg_pos]
              exact lt_of_le_of_ne (not_lt.1 hpos) hne
          · intro hw
            obtain ⟨y, -, hw₀, hpos⟩ := mem_iUnion₂.1 hw
            have hw₀' : ptA w = Pt.other := hw₀
            refine ⟨(ptB_orbitMap w).trans hw₀', ?_⟩
            change absB (P.orbitMap w) ≠ 0
            rw [absB_orbitMap hw₀']
            refine abs_ne_zero.2 fun h0 => ?_
            have hpos' : 0 < heightA w * heightA y := hpos
            rw [h0, zero_mul] at hpos'
            exact lt_irrefl _ hpos'
  bijective_fibredMor := by
    refine ⟨fun φ ψ h => ?_, fun q => ⟨(q.1.1.1, q.1.2), Subtype.ext ?_⟩⟩
    · have h1 := congrArg (fun q => q.1.1.1) h
      have h2 := congrArg (fun q => q.1.2) h
      exact Prod.ext h1 h2
    · obtain ⟨⟨⟨g, o⟩, p⟩, hq⟩ := q
      change o = τobj p at hq
      subst hq
      rfl

/-! ### Definition 17.8.10 -/

/-- **The proper covering uniformizer** (Definition 17.8.10, pp. 834–835) of `P` at `ō = (base, 0)`:
`Ψ = 1`, `Ψ̂ = 1`, with the model `τ̂`. -/
def unif : ProperCoveringUniformizer P pt₀ where
  Ψ := (GCT.LocalUniformizer.tautological ((discretePolyfold Pt).prod (rnPolyfold 1))
    isScSmoothMap_smulB).toUniformizer
  ObjE := (Sheet × Pt) × (Fin 1 → ℝ)
  MorE := ℤˣ × ((Sheet × Pt) × (Fin 1 → ℝ))
  E := E
  τ := τ
  model := model
  hat := GroupoidFunctor.id _
  obj_pt := rfl
  bijOn_fiber := bijOn_id _
  injective_hat := injective_id
  full_hat := (GroupoidFunctor.full_iff _).2 fun _ _ ψ hs ht => ⟨ψ, hs, ht, rfl⟩
  faithful_hat := (GroupoidFunctor.faithful_iff _).2 fun _ _ _ _ h => h
  obj_comm _ := rfl
  mor_comm _ := rfl
  preimage_range := by
    have h1 : range (GCT.LocalUniformizer.tautological ((discretePolyfold Pt).prod (rnPolyfold 1))
        isScSmoothMap_smulB).toUniformizer.obj = univ := range_id
    rw [h1, preimage_univ]
    exact range_id.symm
  orbit_homeomorph := by
    refine ⟨univ, isOpen_univ, mem_univ _, ?_, eq_univ_of_forall fun z => ?_, ?_, ?_⟩
    · change IsEmbedding
        (GroupoidFunctor.id (GroupoidStr.translation ℤˣ (Pt × (Fin 1 → ℝ)))).orbitMap
      rw [GCT.LocalUniformizer.orbitMap_id_eq]
      exact IsEmbedding.id
    · change z ∈ range (GroupoidFunctor.id (GroupoidStr.translation ℤˣ (Pt × (Fin 1 → ℝ)))).orbitMap
      rw [GCT.LocalUniformizer.orbitMap_id_eq]
      exact ⟨z, rfl⟩
    · change IsEmbedding (GroupoidFunctor.id
        (GroupoidStr.translation ℤˣ ((Sheet × Pt) × (Fin 1 → ℝ)))).orbitMap
      rw [GCT.LocalUniformizer.orbitMap_id_eq]
      exact IsEmbedding.id
    · rw [preimage_univ]
      change range (GroupoidFunctor.id
        (GroupoidStr.translation ℤˣ ((Sheet × Pt) × (Fin 1 → ℝ)))).orbitMap = univ
      rw [GCT.LocalUniformizer.orbitMap_id_eq]
      exact range_id

/-! ### The example is non-degenerate -/

/-- `O = Pt × ℝ` is not connected. -/
theorem not_connected_model : ¬ model.Connected := fun h => by
  have : ConnectedSpace (Pt × (Fin 1 → ℝ)) := h
  have := (isPreconnected_univ.image Prod.fst continuous_fst.continuousOn).subsingleton
    ⟨((Pt.base, 0) : Pt × (Fin 1 → ℝ)), mem_univ _, rfl⟩
    ⟨((Pt.other, 0) : Pt × (Fin 1 → ℝ)), mem_univ _, rfl⟩
  exact Pt.noConfusion this

/-- **`G ⋉ O = ℤ/2 ⋉ (Pt × ℝ)` is effective** (Definition 7.2.1): `B` and the ep-groupoid of the
uniformizer `Ψ` are effective. -/
theorem isEffective_BEp : BEp.IsEffective := isEffective_sheetEp_units Pt

/-- **`E = ℤ/2 ⋉ ((Sheet × Pt) × ℝ)` is effective** (Definition 7.2.1). -/
theorem isEffective_E : E.IsEffective := isEffective_sheetEp_units (Sheet × Pt)

/-- The distinguished point `y₀ = ((a, base), 0)`. -/
abbrev y₀ : (Sheet × Pt) × (Fin 1 → ℝ) := ((.a, .base), 0)

/-- `y₀ ∈ τ̂⁻¹(ō)`. -/
theorem y₀_mem_fiber : y₀ ∈ unif.model.fiber := rfl

/-- The fibre `τ̂⁻¹(ō)` is `{((a, base), 0), ((b, base), 0)}`. -/
theorem fiber_eq : τ.obj ⁻¹' {pt₀} =
    {((Sheet.a, Pt.base), 0), ((Sheet.b, Pt.base), 0)} := by
  ext ⟨⟨s, c⟩, x⟩
  simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
  change (c, x) = pt₀ ↔ _
  cases s <;> cases c <;> simp

/-- The fibre `τ̂⁻¹(ō)` has two points, `((a, base), 0)` and `((b, base), 0)`. -/
theorem ncard_fiber : unif.model.fiber.ncard = 2 := by
  change (τ.obj ⁻¹' {pt₀}).ncard = 2
  rw [fiber_eq]
  exact Set.ncard_pair fun h => Sheet.noConfusion (congrArg (fun e => e.1.1) h)

/-- `(−1, y₀)` is a non-unit automorphism of `y₀` in `E`, and `τ̂(−1, y₀) = (−1, ō)` is a non-unit
automorphism of `ō` in `G ⋉ O`, acting on `O` by the reflection `(c, x) ↦ (c, −x)`. -/
theorem nondegenerate :
    E.src ((-1 : ℤˣ), y₀) = y₀ ∧ E.tgt ((-1 : ℤˣ), y₀) = y₀ ∧
      ((-1 : ℤˣ), y₀) ≠ E.unit y₀ ∧ τ.mor ((-1 : ℤˣ), y₀) ≠ BEp.unit pt₀ ∧
      ∀ o : Pt × (Fin 1 → ℝ), (-1 : ℤˣ) • o = (o.1, -o.2) := by
  refine ⟨rfl, ?_, fun h => absurd (congrArg Prod.fst h) (by decide),
    fun h => absurd (congrArg Prod.fst h) (by decide), fun o => ?_⟩
  · change (-1 : ℤˣ) • y₀ = y₀
    rw [smul_neg_one, neg_zero]
    rfl
  · change ((-1 : ℤˣ) • o.1, (-1 : ℤˣ) • o.2) = _
    rw [units_smul_rn_neg_one]
    rfl

/-! ### The sheet `U(y₀)` is not the image of a uniformizer -/

/-- **No uniformizer of `A` has image `Ψ̂(U(y₀))`**: `y₀ = ((a, base), 0)` has the automorphism
`(−1, y₀)`, while the only morphism from `((a, other), 0)` into `U(y₀) = {a} × Pt × ℝ` is its
unit (`−1` sends `((a, other), 0)` to `((b, other), 0)`). -/
theorem not_exists_uniformizer :
    ¬ ∃ Φ : A.toGroupoidalCategory.Uniformizer,
      range Φ.functor.obj = unif.hat.obj '' unif.model.U y₀ := by
  refine GroupoidalCategory.not_exists_uniformizer_range (C := A.toGroupoidalCategory)
    (y := y₀) (z := ((.a, .other), 0)) ⟨y₀, rfl, rfl⟩ ⟨((.a, .other), 0), rfl, rfl⟩
    (ψ := ((-1 : ℤˣ), y₀)) rfl nondegenerate.2.1 nondegenerate.2.2.1 ?_
  rintro ⟨k, q⟩ hs ht
  change q = ((.a, .other), 0) at hs
  subst hs
  obtain ⟨_, h1, h2⟩ := ht
  change _ = k • (((Sheet.a, Pt.other), 0) : (Sheet × Pt) × (Fin 1 → ℝ)) at h2
  rcases Int.units_eq_one_or k with rfl | rfl
  · rfl
  · exfalso
    rw [smul_neg_one] at h2
    have h3 := congrArg (fun e => e.1.1) h2
    have h1' : (unif.hat.obj _).1.1 = Sheet.a := h1
    change _ = (twistSmul (-1) (Sheet.a, Pt.other)).1 at h3
    rw [h1'] at h3
    have h4 : (twistSmul (-1) (Sheet.a, Pt.other)).1 = Sheet.b := by
      simp [twistSmul, TwistedSheet.Sheet.swap]
    exact Sheet.noConfusion (h3.trans h4)

end TwistedLine

open TwistedLine in
/-- **2021 Remark 17.8.11, second part (p. 835), without the connectedness of the model, for
effective groupoids.**  For the proper covering uniformizer `TwistedLine.unif` (two copies of `ℝ`
with the reflection, the two sheets exchanged over the second copy), with `O` disconnected and both
`G ⋉ O` and `E` effective, no uniformizer of `A` has image `Ψ̂(U(y))` for the point `y` over
`α = ((a, base), 0)`.  With the connectedness of the model (the standing reading, `hO_conn`) the
statement holds: `remark_17_8_11_two`. -/
theorem remark_17_8_11_two_disconnected_effective :
    ¬ ∀ (A B : GCT.{0}) (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr) (β : B.Obj)
      (U : ProperCoveringUniformizer P β), P.IsProperCoveringGCT →
        (actionEpGroupoid U.Ψ.smooth_smul).IsEffective → U.E.IsEffective →
        ∀ α : A.Obj, P.obj α = β →
        ∃ y ∈ U.model.fiber, U.hat.obj y = α ∧
          ∃ Φ : A.toGroupoidalCategory.Uniformizer,
            range Φ.functor.obj = U.hat.obj '' U.model.U y := by
  intro h
  obtain ⟨y, -, hyα, Φ, hΦ⟩ := h TwistedLine.A TwistedLine.B TwistedLine.P pt₀ unif
    isProperCoveringGCT_P isEffective_BEp isEffective_E y₀ rfl
  have hy : y = y₀ := hyα
  subst hy
  exact not_exists_uniformizer ⟨Φ, hΦ⟩

end Polyfold
