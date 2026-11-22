import Polyfold.Chapter17.ProperCoveringSheetUniformizer

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8:
**Remark 17.8.11**, second part (p. 835), for a proper covering uniformizer (**Definition
17.8.10**, p. 834) whose model (**Definition 17.8.4**, p. 831) has a disconnected `O`.  Numbers and
pages are the 2021 text's.

# The sheets of a proper covering uniformizer need a connected model

## The text, paraphrased

(Remark 17.8.11) `Ψ : G ⋉ O_β → B` is a uniformizer, `Ψ̂ : E → A` is not; however the
restrictions of `Ψ̂` to `G_α ⋉ O_α` for `α ∈ P⁻¹(β)` are uniformizers.

## What is formalized

* `GroupoidalCategory.not_exists_uniformizer_range`: a set `R` of objects is not the image of any
  uniformizer if it contains an object `y` with a non-unit automorphism and an object `z` whose
  only morphism into `R` is its unit.
* The example (namespace `TwistedSheet`): `O = {ō, p}` (discrete), `ℤ/2` acting trivially on `O`,
  `E = ℤ/2 ⋉ (S × O)` with two sheets `S = {a, b}`, `−1` fixing `(s, ō)` and exchanging `(a, p)`,
  `(b, p)`; `τ̂ = pr₂`.  `model` is a proper covering model (Definition 17.8.4) with
  `U(s, ō) = {s} × O` and `O` not connected (`not_connected_model`); `isProperCoveringGCT_P`
  (Definition 17.8.1) and `unif` (Definition 17.8.10, `Ψ = 1`, `Ψ̂ = 1`); the fibre `τ̂⁻¹(ō)` has
  two points (`ncard_fiber`).
* `TwistedSheet.not_exists_uniformizer`: the full subcategory on `Ψ̂(U(a, ō))` is not the image
  of any uniformizer of `A`: `(a, ō)` has the automorphism `(−1, (a, ō))`, while the only morphism
  from `(a, p)` into `U(a, ō)` is its unit.
* **`remark_17_8_11_two_disconnected`**: why the connectedness of the model is the standing
  reading of the remark: without it the second part of Remark 17.8.11 does not hold as we read
  it, even with "uniformizer" in the weakest sense (any `Φ : G ⋉ O → A` of Definition 17.1.1
  with the right image, not necessarily centred or local).

## Readings

* `O_α` is the sheet `U(y)` of the distinguished point `y ∈ τ̂⁻¹(ō)` over `α = Ψ̂(y)`, as in
  `ProperCoveringSheetUniformizer.lean`; a uniformizer "restricting `Ψ̂`" has image
  `Ψ̂(U(y))`.  The connectedness of the model (`hO_conn`, Definition 17.8.4's "connected",
  available by Proposition 17.8.6) is the tacit setting of the remark (pp. 832–834: "Suppose
  further that `O` is connected"); with it the statement holds: `remark_17_8_11_two`.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

/-! ### A full subcategory that is not the image of a uniformizer -/

namespace GroupoidalCategory

variable {C : GroupoidalCategory.{u}}

/-- **No uniformizer has image `R`** if `R` contains an object `y` with a non-unit automorphism
`ψ` and an object `z` whose only morphism into `R` is its unit: a uniformizer `Φ` with image `R`
would give `g ≠ 1` in its group (over `ψ`, by fullness), and `(g, o_z)` would be a morphism of
`G ⋉ O` from `o_z` with `Φ(g, o_z) = 1_z`, against faithfulness. -/
theorem not_exists_uniformizer_range {R : Set C.Obj} {y z : C.Obj} (hy : y ∈ R) (hz : z ∈ R)
    {ψ : C.Mor} (hψs : C.toGroupoidStr.src ψ = y) (hψt : C.toGroupoidStr.tgt ψ = y)
    (hψ : ψ ≠ C.toGroupoidStr.unit y)
    (hzR : ∀ χ, C.toGroupoidStr.src χ = z → C.toGroupoidStr.tgt χ ∈ R →
      χ = C.toGroupoidStr.unit z) :
    ¬ ∃ Φ : C.Uniformizer, range Φ.functor.obj = R := by
  rintro ⟨Φ, hΦ⟩
  obtain ⟨o₁, ho₁⟩ : y ∈ range Φ.functor.obj := hΦ ▸ hy
  obtain ⟨o₂, ho₂⟩ : z ∈ range Φ.functor.obj := hΦ ▸ hz
  obtain ⟨p, hps, hpt, hpψ⟩ := (GroupoidFunctor.full_iff _).1 Φ.full o₁ o₁ ψ
    (hψs.trans ho₁.symm) (hψt.trans ho₁.symm)
  have hg : p.1 ≠ 1 := by
    intro h1
    have hp : p = (GroupoidStr.translation Φ.G Φ.O).unit o₁ :=
      Prod.ext h1 (show p.2 = o₁ from hps)
    apply hψ
    rw [← hpψ, hp, Φ.functor.mor_unit, ho₁]
  set χ := Φ.functor.mor (p.1, o₂) with hχ
  have hχs : C.toGroupoidStr.src χ = z := (Φ.functor.src_mor _).trans ho₂
  have hχt : C.toGroupoidStr.tgt χ = Φ.functor.obj (p.1 • o₂) := Φ.functor.tgt_mor _
  have hχu := hzR χ hχs (hΦ ▸ hχt ▸ mem_range_self _)
  have hobj : Φ.functor.obj (p.1 • o₂) = Φ.functor.obj o₂ := by
    rw [← hχt, hχu, C.toGroupoidStr.tgt_unit, ho₂]
  have heq := (GroupoidFunctor.faithful_iff _).1 Φ.faithful (p.1, o₂)
    ((GroupoidStr.translation Φ.G Φ.O).unit o₂) rfl
    (Φ.injective_obj (hobj.trans (congrArg _ ((GroupoidStr.translation Φ.G Φ.O).tgt_unit o₂).symm)))
    (by rw [Φ.functor.mor_unit, ho₂]; exact hχu)
  exact hg (congrArg Prod.fst heq)

end GroupoidalCategory

/-! ### The example -/

namespace TwistedSheet

open EpGroupoid EpGroupoid.Examples

/-- The two points `ō = base` and `p = other` of `O`. -/
inductive Pt : Type
  | base
  | other
  deriving DecidableEq

/-- The two sheets `a`, `b`. -/
inductive Sheet : Type
  | a
  | b
  deriving DecidableEq

/-- Exchange the two sheets. -/
def Sheet.swap : Sheet → Sheet
  | .a => .b
  | .b => .a

@[simp] theorem Sheet.swap_swap (s : Sheet) : s.swap.swap = s := by cases s <;> rfl

instance : Finite Pt :=
  Finite.of_surjective (fun b : Bool => if b then Pt.other else Pt.base) fun x => by
    cases x
    exacts [⟨false, rfl⟩, ⟨true, rfl⟩]

instance : Finite Sheet :=
  Finite.of_surjective (fun b : Bool => if b then Sheet.b else Sheet.a) fun x => by
    cases x
    exacts [⟨false, rfl⟩, ⟨true, rfl⟩]

instance : TopologicalSpace Pt := ⊥
instance : DiscreteTopology Pt := ⟨rfl⟩
instance : TopologicalSpace Sheet := ⊥
instance : DiscreteTopology Sheet := ⟨rfl⟩

/-- `ℤˣ` acting trivially on `O`. -/
instance : MulAction ℤˣ Pt where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smul_pt (k : ℤˣ) (x : Pt) : k • x = x := rfl

/-- `k ∗ (s, ō) = (s, ō)`, and `−1` exchanges `(a, p)` and `(b, p)`. -/
def twistSmul (k : ℤˣ) (q : Sheet × Pt) : Sheet × Pt :=
  (if q.2 = .other ∧ k = -1 then q.1.swap else q.1, q.2)

theorem twistSmul_one (q : Sheet × Pt) : twistSmul 1 q = q := by
  obtain ⟨s, o⟩ := q
  simp [twistSmul]

theorem twistSmul_mul (k k' : ℤˣ) (q : Sheet × Pt) :
    twistSmul (k * k') q = twistSmul k (twistSmul k' q) := by
  obtain ⟨s, o⟩ := q
  rcases Int.units_eq_one_or k with rfl | rfl <;> rcases Int.units_eq_one_or k' with rfl | rfl <;>
    cases o <;> simp [twistSmul]

/-- The twisted action on `S × O`. -/
instance : MulAction ℤˣ (Sheet × Pt) where
  smul := twistSmul
  one_smul := twistSmul_one
  mul_smul := twistSmul_mul

theorem smul_def (k : ℤˣ) (q : Sheet × Pt) : k • q = twistSmul k q := rfl

/-- `O` as a discrete M-polyfold. -/
abbrev PB : MPolyfold Pt := discretePolyfold Pt

/-- `S × O` as a discrete M-polyfold. -/
abbrev PE : MPolyfold (Sheet × Pt) := (discretePolyfold Sheet).prod PB

theorem isScSmoothMap_smulB (k : ℤˣ) : PB.IsScSmoothMap PB fun o : Pt => k • o :=
  isScSmoothMap_discrete_of_continuous continuous_of_discreteTopology

theorem isScSmoothMap_smulE (k : ℤˣ) : PE.IsScSmoothMap PE fun p : Sheet × Pt => k • p :=
  isScSmoothMap_prod_discrete_iff.2 fun _ => MPolyfold.IsScSmoothOn.prodMk
    (isScSmoothMap_discrete_of_continuous continuous_of_discreteTopology)
    (isScSmoothMap_discrete_of_continuous continuous_of_discreteTopology)

/-- `E = ℤ/2 ⋉ (S × O)`. -/
abbrev E : EpGroupoid (Sheet × Pt) (ℤˣ × (Sheet × Pt)) := actionEpGroupoid isScSmoothMap_smulE

/-- `τ̂ : E → ℤ/2 ⋉ O`, `(s, o) ↦ o`. -/
def τ : EpFunctor E (actionEpGroupoid isScSmoothMap_smulB) where
  obj := Prod.snd
  mor φ := (φ.1, φ.2.2)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_snd _ _
  isScSmoothMap_mor := MPolyfold.IsScSmoothOn.prodMk (MPolyfold.isScSmoothMap_fst _ _)
    ((MPolyfold.isScSmoothMap_snd _ _).comp (MPolyfold.isScSmoothMap_snd _ _))

theorem isScDiffeoOn_τ_fibredMap
    [ParacompactSpace ((ℤˣ × Pt) × (Sheet × Pt))]
    [ParacompactSpace (MPolyfold.fibredProduct (actionEpGroupoid isScSmoothMap_smulB).src τ.obj)] :
    E.PMor.IsScDiffeoOn (MPolyfold.subPolyfold
      (MPolyfold.isSubMPolyfold_fibredProduct
        (actionEpGroupoid isScSmoothMap_smulB).isLocalScDiffeo_src τ.isScSmoothMap_obj)) τ.fibredMap
      (fun q => ((q : (ℤˣ × Pt) × (Sheet × Pt)).1.1, (q : (ℤˣ × Pt) × (Sheet × Pt)).2))
      univ univ where
  isScSmoothOn := MPolyfold.isScSmoothOn_subPolyfold_of_val _
    (MPolyfold.IsScSmoothOn.prodMk τ.isScSmoothMap_mor E.isScSmoothMap_src)
  isScSmoothOn_inv :=
    MPolyfold.IsScSmoothMap.comp
      (g := fun r : (ℤˣ × Pt) × (Sheet × Pt) => (r.1.1, r.2))
      (MPolyfold.IsScSmoothOn.prodMk
        ((MPolyfold.isScSmoothMap_fst (discretePolyfold ℤˣ) PB).comp
          (MPolyfold.isScSmoothMap_fst (actionEpGroupoid isScSmoothMap_smulB).PMor E.PObj))
        (MPolyfold.isScSmoothMap_snd (actionEpGroupoid isScSmoothMap_smulB).PMor E.PObj))
      (MPolyfold.subPolyfold_inclusion_isScSmooth _)
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv _ _ := rfl
  right_inv q _ := Subtype.ext (Prod.ext (Prod.ext rfl q.2.symm) rfl)

/-- **A proper covering model with a disconnected `O`** (Definition 17.8.4, p. 831):
`τ̂ : ℤ/2 ⋉ (S × O) → ℤ/2 ⋉ O`, `ō = base`, `U(s, ō) = {s} × O`, `σ_{(s, ō)}(o) = (s, o)`. -/
def model : ProperCoveringModel τ where
  pt := .base
  smul_pt _ := rfl
  surjective x := ⟨(.a, x), rfl⟩
  isLocalScDiffeo p :=
    ⟨{p.1} ×ˢ univ, univ, fun y => (p.1, y), ⟨rfl, mem_univ _⟩, isScDiffeoOn_snd_sheet p.1⟩
  U y := {y.1} ×ˢ univ
  σ y o := (y.1, o)
  mem_U _ _ := ⟨rfl, mem_univ _⟩
  pairwiseDisjoint_U := by
    intro y hy z hz hyz
    refine Set.disjoint_left.2 fun p hp hp' => hyz (Prod.ext ?_ ?_)
    · exact (hp.1 : p.1 = y.1).symm.trans hp'.1
    · exact (hy : y.2 = .base).trans (hz : z.2 = .base).symm
  iUnion_U := by
    refine eq_univ_of_forall fun p => ?_
    simp only [mem_iUnion, exists_prop]
    exact ⟨(p.1, .base), rfl, ⟨rfl, mem_univ _⟩⟩
  isScDiffeoOn_U y _ := isScDiffeoOn_snd_sheet y.1
  isScDiffeo_fibredMap := by
    have := MPolyfold.paracompactSpace_prod (actionEpGroupoid isScSmoothMap_smulB).PMor E.PObj
    have := ((actionEpGroupoid isScSmoothMap_smulB).PMor.prod E.PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct (actionEpGroupoid isScSmoothMap_smulB).src τ.obj)
    exact ⟨_, isScDiffeoOn_τ_fibredMap⟩

/-- `O` is not connected. -/
theorem not_connected_model : ¬ model.Connected := fun h => by
  have : ConnectedSpace Pt := h
  have := (isPreconnected_univ (α := Pt)).subsingleton (mem_univ .base) (mem_univ .other)
  exact Pt.noConfusion this

/-- The GCT `A = ℤ/2 ⋉ (S × O)`. -/
abbrev A : GCT.{0} := GCT.translation ℤˣ (Sheet × Pt) isScSmoothMap_smulE

/-- The GCT `B = ℤ/2 ⋉ O`. -/
abbrev B : GCT.{0} := GCT.translation ℤˣ Pt isScSmoothMap_smulB

/-- `P = τ̂ : A → B` as a functor of GCTs. -/
abbrev P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr := τ.toGroupoidFunctor

theorem isOpen_orbitSpace_A (V : Set A.OrbitSpace) : IsOpen V :=
  isOpen_coinduced.2 (isOpen_discrete _)

theorem isOpen_orbitSpace_B (V : Set B.OrbitSpace) : IsOpen V :=
  isOpen_coinduced.2 (isOpen_discrete _)

/-- **`P` is a proper covering functor of GCTs** (Definition 17.8.1, p. 828). -/
theorem isProperCoveringGCT_P : P.IsProperCoveringGCT where
  continuous_orbitMap := (continuous_quot_mk.comp continuous_snd).quotient_lift _
  surjective_orbitMap z := by
    obtain ⟨x, rfl⟩ : ∃ x, B.π x = z := Quotient.exists_rep z
    exact ⟨A.π (.a, x), rfl⟩
  finite_fiber _ := Set.toFinite _
  surjective_obj x := ⟨(.a, x), rfl⟩
  evenlyCovered z := by
    refine ⟨Set.toFinite _, {z}, fun y => {y}, isOpen_orbitSpace_B _, rfl,
      fun y _ => ⟨isOpen_orbitSpace_A _, rfl⟩, fun y _ y' _ hne => ?_, ?_⟩
    · exact Set.disjoint_singleton.2 hne
    · ext w
      simp
  bijective_fibredMor := by
    refine ⟨fun φ ψ h => ?_, fun q => ⟨(q.1.1.1, q.1.2), Subtype.ext ?_⟩⟩
    · have h1 := congrArg (fun q => q.1.1.1) h
      have h2 := congrArg (fun q => q.1.2) h
      exact Prod.ext h1 h2
    · obtain ⟨⟨⟨g, o⟩, p⟩, hq⟩ := q
      change o = p.2 at hq
      subst hq
      rfl

/-- **The proper covering uniformizer** (Definition 17.8.10, p. 834) of `P` at `ō`: `Ψ = 1`,
`Ψ̂ = 1`, with the model `τ̂`. -/
def unif : ProperCoveringUniformizer P Pt.base where
  Ψ := (GCT.LocalUniformizer.tautological PB isScSmoothMap_smulB).toUniformizer
  ObjE := Sheet × Pt
  MorE := ℤˣ × (Sheet × Pt)
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
    have h1 : range (GCT.LocalUniformizer.tautological PB isScSmoothMap_smulB).toUniformizer.obj =
        univ := range_id
    rw [h1, preimage_univ]
    exact range_id.symm
  orbit_homeomorph := by
    refine ⟨univ, isOpen_univ, mem_univ _, ?_, eq_univ_of_forall fun z => ?_, ?_, ?_⟩
    · change IsEmbedding (GroupoidFunctor.id (GroupoidStr.translation ℤˣ Pt)).orbitMap
      rw [GCT.LocalUniformizer.orbitMap_id_eq]
      exact IsEmbedding.id
    · change z ∈ range (GroupoidFunctor.id (GroupoidStr.translation ℤˣ Pt)).orbitMap
      rw [GCT.LocalUniformizer.orbitMap_id_eq]
      exact ⟨z, rfl⟩
    · change IsEmbedding (GroupoidFunctor.id (GroupoidStr.translation ℤˣ (Sheet × Pt))).orbitMap
      rw [GCT.LocalUniformizer.orbitMap_id_eq]
      exact IsEmbedding.id
    · rw [preimage_univ]
      change range (GroupoidFunctor.id (GroupoidStr.translation ℤˣ (Sheet × Pt))).orbitMap = univ
      rw [GCT.LocalUniformizer.orbitMap_id_eq]
      exact range_id

/-- The distinguished point `y₀ = (a, ō)`. -/
abbrev y₀ : Sheet × Pt := (.a, .base)

theorem y₀_mem_fiber : y₀ ∈ unif.model.fiber := rfl

/-- **No uniformizer of `A` has image `Ψ̂(U(y₀))`**: `y₀ = (a, ō)` has the automorphism
`(−1, y₀)`, while the only morphism from `(a, p)` into `U(y₀) = {a} × O` is its unit (`−1` sends
`(a, p)` to `(b, p)`). -/
theorem not_exists_uniformizer :
    ¬ ∃ Φ : A.toGroupoidalCategory.Uniformizer,
      range Φ.functor.obj = unif.hat.obj '' unif.model.U y₀ := by
  refine GroupoidalCategory.not_exists_uniformizer_range (C := A.toGroupoidalCategory)
    (y := y₀) (z := (.a, .other)) ⟨y₀, ⟨rfl, mem_univ _⟩, rfl⟩
    ⟨(.a, .other), ⟨rfl, mem_univ _⟩, rfl⟩ (ψ := ((-1 : ℤˣ), y₀)) rfl ?_ ?_ ?_
  · change twistSmul (-1) y₀ = y₀
    simp [twistSmul]
  · intro h
    have := congrArg Prod.fst h
    exact absurd this (by decide)
  · rintro ⟨k, q⟩ hs ht
    change q = (.a, .other) at hs
    subst hs
    obtain ⟨_, ⟨h1, -⟩, h2⟩ := ht
    change _ = twistSmul k (.a, .other) at h2
    rcases Int.units_eq_one_or k with rfl | rfl
    · rfl
    · exfalso
      have h4 : twistSmul (-1) (Sheet.a, Pt.other) = (Sheet.b, Pt.other) := by
        simp [twistSmul, Sheet.swap]
      rw [h4] at h2
      have h3 := congrArg Prod.fst h2
      have h1' : (unif.hat.obj _).1 = Sheet.a := h1
      rw [h1'] at h3
      exact Sheet.noConfusion h3

/-- The fibre `τ̂⁻¹(ō)` has two points, `(a, ō)` and `(b, ō)`. -/
theorem ncard_fiber : unif.model.fiber.ncard = 2 := by
  have h : (unif.model.fiber : Set (Sheet × Pt)) =
      ({(Sheet.a, Pt.base), (Sheet.b, Pt.base)} : Set (Sheet × Pt)) := by
    ext ⟨s, o⟩
    change o = Pt.base ↔ (s, o) ∈ ({(Sheet.a, Pt.base), (Sheet.b, Pt.base)} : Set (Sheet × Pt))
    cases s <;> cases o <;> simp
  rw [h]
  exact Set.ncard_pair fun h => Sheet.noConfusion (congrArg Prod.fst h)

end TwistedSheet

open TwistedSheet in
/-- **2021 Remark 17.8.11, second part (p. 835), for a disconnected model** (why the
connectedness `hO_conn` of `remark_17_8_11_two`, the tacit setting of pp. 832–834, is needed):
for the proper covering
uniformizer `TwistedSheet.unif`, with `O` disconnected, no uniformizer of `A` has image
`Ψ̂(U(y))` for the point `y` over `α = (a, ō)`. -/
theorem remark_17_8_11_two_disconnected :
    ¬ ∀ (A B : GCT.{0}) (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr) (β : B.Obj)
      (U : ProperCoveringUniformizer P β), P.IsProperCoveringGCT → ∀ α : A.Obj, P.obj α = β →
        ∃ y ∈ U.model.fiber, U.hat.obj y = α ∧
          ∃ Φ : A.toGroupoidalCategory.Uniformizer,
            range Φ.functor.obj = U.hat.obj '' U.model.U y := by
  intro h
  obtain ⟨y, -, hyα, Φ, hΦ⟩ := h TwistedSheet.A TwistedSheet.B TwistedSheet.P Pt.base unif
    isProperCoveringGCT_P y₀ rfl
  have hy : y = y₀ := hyα
  subst hy
  exact not_exists_uniformizer ⟨Φ, hΦ⟩

end Polyfold
