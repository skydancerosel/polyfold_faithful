import Polyfold.Chapter7.Effective
import Polyfold.Chapter7.OrbitTopology
import Polyfold.Chapter7.ProperSubsets

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 7: **witnesses and counterexamples** for the definitions and hypotheses of the chapter
(PLAN II.5, II.6 item 1, wave W5): the translation groupoid `K ⋉ U` of a finite group (p. 232),
**Definition 7.1.3 (2017: 7.3)** (3) (pp. 226–227), the remark after **Definition 7.1.7 (2017: 7.7)** (pp. 228–229),
**Definition 7.2.1 (2017: 7.11)** and "examples show that the regular set can be empty" (p. 239),
**Definition 7.2.7 (2017: 7.12)** (`T_x`, p. 241), **Definitions 7.5.1 (2017: 7.15)** and **7.17** (pp. 249, 251).
There is no 2014 preprint of Part II; numbers and pages are the 2017 text's.

# Non-vacuity: witnesses and counterexamples

## The text, paraphrased

(Definition 7.1.3 (2017: 7.3) (3)) Every object `x` has an open neighbourhood `V(x)` with `t : s⁻¹(cl V(x)) → X`
proper.  (p. 232) For a finite group `G` acting on `U` by sc-diffeomorphisms the translation
groupoid `G ⋉ U` has objects `U`, morphisms `G × U`, `s(g, y) = y`, `t(g, y) = g ∗ y`.
(Definition 7.1.7 (2017: 7.7)) `EP`: functors sc-smooth on objects and on morphisms; "actually, it is sufficient
to require that the functor `f` is sc-smooth between the object spaces", by
`f(γ) = (s|U(ψ))⁻¹(f(s(γ)))` on a neighbourhood `U(φ)` with `f(U(φ)) ⊂ U(ψ)`.  (Definition 7.2.1 (2017: 7.11))
`X` is effective if for every `x`, `g ∈ G_x ∖ {1_x}` and open `𝐔(g)` there is `ψ ∈ 𝐔(g)` with
`s(ψ) ≠ t(ψ)`; `x` is regular if `G_x = {1_x}`; (p. 239) "examples show that the regular set can
be empty".  (Definition 7.2.7 (2017: 7.12)) `T_x ⊆ G_x`, the elements acting trivially near `x`.
(Definition 7.5.8 (2017: 7.17)) `Q ⊆ X` is proper if `t : s⁻¹(Q) → X` is proper.

## What is formalized (namespace `Polyfold.EpGroupoid.Examples`)

* **The translation groupoid `K ⋉ U`** of a finite discrete group `K` acting on an M-polyfold
  `P : MPolyfold U` by sc-smooth maps (`hP : ∀ k, P.IsScSmoothMap P (k • ·)`):
  `actionEpGroupoid hP : EpGroupoid U (K × U)`, morphisms `actionMorPolyfold K P`
  (`discretePolyfold K` times `P`), with `action_isLocalScDiffeo_src`,
  `action_isLocalScDiffeo_tgt`, `action_isScSmoothCompSheet`, `action_isProperMap_tgt` and
  `actionShear` (`(k, y) ↦ (k, k y)`); the structure maps `actionEpGroupoid_src`, `_tgt`,
  `_comp`, `_unit`, `_inv`.  Its **isotropy** `isotropyEquivStabilizer : G_x ≃* K_x`,
  `isRegular_action_iff`, `regularSet_action`; its **orbit space** `action_isomorphic_iff`,
  `action_π_eq_π_iff`, `actionOrbitHomeomorph : |K ⋉ U| ≃ₜ U/K`; **properness**
  `isProperSubset_action` (every closed set is proper), `isProperSubset_action_iff` (proper ⟺
  closed), `hasPropernessProperty_action` (every open set); `hasParacompactOrbitSpace_action`
  (for second countable `U`).
* **`ℤ/2 ⋉ ℝ` by reflection** (`ℤ/2 = ℤˣ = {±1}`, `rnPolyfold 1`): `isScSmoothMap_units_smul`,
  `reflectionEpGroupoid`, `isEffective_reflection`, `reflectionIsotropyNegOne` (`(−1, 0) ≠ 1`),
  `isEffective_reflection_nonvacuous`, `regularSet_reflection` (`X_reg = ℝ ∖ {0}`),
  `reflectionIsotropyZeroEquiv` (`G_0 ≅ ℤ/2`), `trivialSubgroup_reflection` (`T_x = 1`),
  `isTame_reflection`, `hasParacompactOrbitSpace_reflection`.
* **The trivial action of `ℤ/3` on `ℝ`** (`Multiplicative (ZMod 3)`, the scoped instance
  `instMulActionZ3`): `trivialZ3EpGroupoid`, `trivialZ3IsotropyEquiv` (`G_x ≅ ℤ/3`),
  `trivialSubgroup_trivialZ3` (`T_x = G_x`), `trivialZ3TrivialSubgroupEquiv` (`T_x ≅ ℤ/3`),
  `not_isEffective_trivialZ3`, `regularSet_trivialZ3` (`X_reg = ∅`).
* **The remark after Definition 7.1.7 (2017: 7.7)** (PLAN II.6, 1): `remarkFunctor` on `trivialZ3EpGroupoid`
  (the identity on objects, `(g, y) ↦ (g, y)` for `y ≤ 0`, `(g², y)` for `y > 0`), a
  `GroupoidFunctor`; `isScSmoothMap_remarkFunctor_obj`, `not_continuous_remarkFunctor_mor`,
  `not_isScSmoothMap_remarkFunctor_mor`, `not_exists_epFunctor_remarkFunctor`, and the summary
  `remark_definition_7_1_7_counterexample`.
* **Definition 7.1.3 (2017: 7.3) (3), the universal reading** (PLAN II.5, 4): the pair groupoid of `ℤ`,
  `pairGroupoidStr`, `pairEpGroupoid` (`ℤ` and `ℤ × ℤ` discrete M-polyfolds, `V(x) = {x}`:
  `pair_isProperMap`); `pair_not_isProperMap_univ`, `pair_exists_not_isProperMap`,
  `pair_not_forall_isProperMap`.

## Witnesses and the hypotheses they make non-vacuous

* `K ⋉ U`, any finite `K`: Definition 7.1.3 (2017: 7.3) with isotropy groups `K_x` of any finite group
  (`actionEpGroupoid`, `isotropyEquivStabilizer`); Definition 7.5.8 (2017: 7.17) with proper subsets beyond the
  compact ones, all closed sets (`isProperSubset_action_iff`); for second countable `U`,
  Definition 7.5.1 (2017: 7.15) (5) (`hasParacompactOrbitSpace_action`).
* `ℤ/2 ⋉ ℝ`: Definition 7.2.1 (2017: 7.11), effective with `G_0 ≠ 1`, not vacuously
  (`isEffective_reflection_nonvacuous`); Lemma 7.2.2 (2017: 7.2) and Proposition 7.2.4 (2017: 7.8) with `X_reg` open, dense
  and `≠ X` (`regularSet_reflection`); Definitions 7.1.6 and 7.5.1 (2017: 7.6 and 7.15) (`isTame_reflection`,
  `hasParacompactOrbitSpace_reflection`); Definition 7.2.7 (2017: 7.12) with `T_x = 1 ≠ G_0`
  (`trivialSubgroup_reflection`, `reflectionIsotropyZeroEquiv`).
* `ℤ/3 × ℝ ⇉ ℝ` (trivial action): Definition 7.2.7 (2017: 7.12) with `T_x = G_x ≠ 1`
  (`trivialSubgroup_trivialZ3`); "the regular set can be empty" (`regularSet_trivialZ3`); a
  non-effective ep-groupoid (`not_isEffective_trivialZ3`).
* `remarkFunctor` on `ℤ/3 × ℝ ⇉ ℝ`: Definition 7.1.7 (2017: 7.7), sc-smoothness on morphisms is not implied
  by sc-smoothness on objects (`remark_definition_7_1_7_counterexample`).
* The pair groupoid of `ℤ`: Definition 7.1.3 (2017: 7.3) (3) must be existential in `V(x)`
  (`pair_not_forall_isProperMap`).

The vacuous case of Definition 7.2.1 (2017: 7.11) (trivial isotropy) is `EpGroupoid.isEffective_trivial`
(`EpGroupoid.lean`); Definitions 7.1.18, 7.1.21, 7.5.5 (2017: 7.8, 7.10, 7.16) and Theorem 7.1.13 (2017: 7.1)'s data are witnessed there by
the trivial ep-groupoid.

## Reading

* **`K ⋉ U`.**  "A finite group acting by sc-diffeomorphisms" is read as `[Finite K]` with the
  discrete topology and every `k • ·` sc-smooth; the inverse `k⁻¹ • ·` is then sc-smooth too, so
  each `k • ·` is an sc-diffeomorphism.  `K × U` is `discretePolyfold K` times `P`
  (`MPolyfold.prod`), "the finite disjoint union of copies of `U`" (p. 232).  The construction is
  `NaturalAction.lean`'s `translationEpGroupoid` with the data of a natural representation
  replaced by the hypothesis `hP`; condition (4) is checked in the sheet form.  The isotropy
  group is the stabilizer `K_x` and the orbit space is `U/K` with its quotient topology.
* **"Every subset is proper"** is read as "every closed subset is proper": a proper subset is
  closed (Proposition 7.5.9 (2017: 7.13)), and for finite `K` every closed subset is proper
  (`isProperSubset_action_iff`).
* **Effective, non-vacuously.**  In `ℤ/2 ⋉ ℝ`, `G_0 = ℤ/2` and every neighbourhood of `(−1, 0)`
  contains `(−1, y)`, `y ≠ 0`, with `s = y ≠ −y = t`; `G_x = 1` for `x ≠ 0`.  So `X_reg = ℝ ∖ {0}`,
  open and dense as Proposition 7.2.4 (2017: 7.8) says, and not all of `ℝ`.  `|X| = ℝ/±1` is paracompact
  (second countable, so metrizable by Corollary 7.3.6 (2017: 7.1)).
* **The regular set can be empty** (p. 239): in `ℤ/3 × ℝ ⇉ ℝ` with the trivial action every
  object has `G_x = T_x ≅ ℤ/3`; the ep-groupoid is not effective, consistently with
  Proposition 7.2.4 (2017: 7.8).
* **The remark after Definition 7.1.7 (2017: 7.7)** does not hold as we read it (PLAN II.6, 1): the functor
  `remarkFunctor` is a functor (composable morphisms have the same `y`, and `g ↦ g²` is an
  automorphism of `ℤ/3`), it is sc-smooth (the identity) on the object spaces, but it is not
  continuous on the morphism spaces (`y ↦ (f(g, y)).1` jumps from `g` to `g² ≠ g` at `0` while `ℝ`
  is connected), hence not sc-smooth there and not a morphism of `EP`.  The text's choice of
  `U(φ)` with `f(U(φ)) ⊂ U(ψ)` uses continuity on morphisms; with continuity added the remark
  holds (`EpGroupoid.isScSmoothMap_mor_of_continuous`, `EpFunctor.ofContinuous`, `Basic.lean`).
* **Definition 7.1.3 (2017: 7.3) (3)** is existential in `V(x)` (PLAN P3): in the pair groupoid of `ℤ`, the
  choice `V(x) = {x}` works (`t : ℤ × {x} → ℤ` is a bijection of discrete spaces), but for the
  neighbourhood `V = ℤ` of any `x`, `t : ℤ × ℤ → ℤ` has the infinite fibre `{0} × ℤ` over `0` and is
  not proper.  So the reading "for every neighbourhood `V` of `x`" would exclude this
  ep-groupoid; the existential reading of the text is the one formalized.
* No possible misprint was found in the passages used here.
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

namespace EpGroupoid

namespace Examples

universe u

/-- A map into a discrete M-polyfold, continuous on an open set, is sc-smooth there. -/
private theorem isScSmoothOn_discreteOn {G : Type*} [TopologicalSpace G] [DiscreteTopology G]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {PY : MPolyfold Y}
    {f : Y → G} {W : Set Y} (hW : IsOpen W) (hf : ContinuousOn f W) :
    PY.IsScSmoothOn (discretePolyfold G) f W := by
  refine MPolyfold.IsScSmoothOn.of_locally hW fun y hy => ⟨W ∩ f ⁻¹' {f y},
    hf.isOpen_inter_preimage hW (isOpen_discrete _), ⟨hy, rfl⟩, inter_subset_left, ?_⟩
  exact ((isScSmoothMap_const_discrete (f y)).mono
    (hf.isOpen_inter_preimage hW (isOpen_discrete _)) (subset_univ _)).congr
    fun z hz => hz.2.symm

/-! ### The translation groupoid `K ⋉ U` of a finite group acting by sc-diffeomorphisms -/

section Action

variable (K : Type u) [Group K] [Finite K] [TopologicalSpace K] [DiscreteTopology K]
  {U : Type u} [TopologicalSpace U] [T2Space U] [ParacompactSpace U] [MulAction K U]
  (P : MPolyfold U)

/-- **The M-polyfold `K × U`**: `#K` copies of `U` (`discretePolyfold K` times `P`). -/
def actionMorPolyfold : MPolyfold (K × U) := (discretePolyfold K).prod P

variable {K P}

omit [Finite K] [TopologicalSpace K] [DiscreteTopology K] in
theorem action_continuous_smul (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y) (k : K) :
    Continuous fun y : U => k • y :=
  continuousOn_univ.1 (hP k).continuousOn

omit [Finite K] in
theorem action_continuous_smul_prod (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y) :
    Continuous fun p : K × U => p.1 • p.2 :=
  continuous_prod_of_discrete_left.2 fun k => action_continuous_smul hP k

/-- `(k, y) ↦ (k, k y)`, a homeomorphism of `K × U`. -/
def actionShear (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y) : K × U ≃ₜ K × U where
  toFun p := (p.1, p.1 • p.2)
  invFun p := (p.1, p.1⁻¹ • p.2)
  left_inv p := Prod.ext rfl (inv_smul_smul p.1 p.2)
  right_inv p := Prod.ext rfl (smul_inv_smul p.1 p.2)
  continuous_toFun := continuous_fst.prodMk (action_continuous_smul_prod hP)
  continuous_invFun := continuous_fst.prodMk
    (continuous_prod_of_discrete_left.2 fun k => action_continuous_smul hP k⁻¹)

/-- `s(k, y) = y` is a local sc-diffeomorphism `K × U → U`. -/
theorem action_isLocalScDiffeo_src :
    (actionMorPolyfold K P).IsLocalScDiffeo P (GroupoidStr.translation K U).src := fun p =>
  ⟨{p.1} ×ˢ univ, univ, fun y => (p.1, y), ⟨rfl, mem_univ _⟩, isScDiffeoOn_snd_sheet p.1⟩

/-- `t(k, y) = k y` is a local sc-diffeomorphism `K × U → U`. -/
theorem action_isLocalScDiffeo_tgt (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y) :
    (actionMorPolyfold K P).IsLocalScDiffeo P (GroupoidStr.translation K U).tgt := fun p => by
  refine ⟨{p.1} ×ˢ univ, univ, fun z => (p.1, p.1⁻¹ • z), ⟨rfl, mem_univ _⟩, ?_⟩
  exact
    { isScSmoothOn := (MPolyfold.IsScSmoothOn.comp (hP p.1)
        ((MPolyfold.isScSmoothMap_snd _ _).mono (isOpen_sheet p.1) (subset_univ _))
        (mapsTo_univ _ _)).congr fun q hq => by
          change p.1 • q.2 = q.1 • q.2
          rw [show q.1 = p.1 from hq.1]
      isScSmoothOn_inv := (isScSmoothMap_sheet p.1).comp (hP p.1⁻¹)
      mapsTo := mapsTo_univ _ _
      mapsTo_inv := fun _ _ => ⟨rfl, mem_univ _⟩
      left_inv := fun q hq => Prod.ext (show p.1 = q.1 from (hq.1 : q.1 = p.1).symm) (by
        change p.1⁻¹ • q.1 • q.2 = q.2
        rw [show q.1 = p.1 from hq.1, inv_smul_smul])
      right_inv := fun z _ => smul_inv_smul p.1 z }

/-- Condition (4) for `K ⋉ U`, in the sheet form: `ψ ↦ σ(t ψ) ∘ ψ = (k(ψ) ψ₁, ψ₂)` with a
locally constant `k`. -/
theorem action_isScSmoothCompSheet (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y) :
    IsScSmoothCompSheet P (actionMorPolyfold K P) (GroupoidStr.translation K U).src
      (GroupoidStr.translation K U).tgt (GroupoidStr.translation K U).comp := by
  intro σ W V hd
  have hc := action_continuous_smul_prod hP
  have hTo : IsOpen ((fun p : K × U => p.1 • p.2) ⁻¹' V) :=
    hd.isScSmoothOn_inv.isOpen.preimage hc
  have h1 : ContinuousOn (fun ψ : K × U => σ (ψ.1 • ψ.2))
      ((fun p : K × U => p.1 • p.2) ⁻¹' V) :=
    hd.isScSmoothOn_inv.continuousOn.comp hc.continuousOn fun _ hψ => hψ
  have h2 : ContinuousOn (fun ψ : K × U => (σ (ψ.1 • ψ.2)).1 * ψ.1)
      ((fun p : K × U => p.1 • p.2) ⁻¹' V) :=
    (continuous_of_discreteTopology (f := fun a : K × K => a.1 * a.2)).comp_continuousOn
      ((continuous_fst.comp_continuousOn h1).prodMk continuous_fst.continuousOn)
  exact MPolyfold.IsScSmoothOn.prodMk (isScSmoothOn_discreteOn hTo h2)
    ((MPolyfold.isScSmoothMap_snd _ _).mono hTo (subset_univ _))

/-- `t : K × U → U` is proper: `t = π₂ ∘ (k, y) ↦ (k, k y)` with `K` finite. -/
theorem action_isProperMap_tgt (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y) :
    IsProperMap (GroupoidStr.translation K U).tgt :=
  isProperMap_snd_of_compactSpace.comp (actionShear hP).isProperMap

/-- **The translation groupoid `K ⋉ U` is an ep-groupoid** (p. 232) for a finite group `K` acting
on the M-polyfold `U` by sc-diffeomorphisms: objects `U`, morphisms the M-polyfold `K × U`. -/
def actionEpGroupoid (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y) :
    EpGroupoid U (K × U) where
  toGroupoidStr := GroupoidStr.translation K U
  PObj := P
  PMor := actionMorPolyfold K P
  isLocalScDiffeo_src := action_isLocalScDiffeo_src
  isLocalScDiffeo_tgt := action_isLocalScDiffeo_tgt hP
  isScSmoothMap_unit := isScSmoothMap_sheet 1
  isScSmoothMap_inv := isScSmoothMap_prod_discrete_iff.2 fun k =>
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete k⁻¹) (hP k)
  exists_isProperMap _ := ⟨univ, isOpen_univ, mem_univ _,
    (action_isProperMap_tgt hP).restrict (isClosed_closure.preimage continuous_snd)⟩
  isScSmoothComp := (isScSmoothComp_iff_sheet _ _).2 (action_isScSmoothCompSheet hP)

variable (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y)

@[simp] theorem actionEpGroupoid_src (p : K × U) : (actionEpGroupoid hP).src p = p.2 := rfl

@[simp] theorem actionEpGroupoid_tgt (p : K × U) : (actionEpGroupoid hP).tgt p = p.1 • p.2 :=
  rfl

@[simp] theorem actionEpGroupoid_comp (p q : K × U) :
    (actionEpGroupoid hP).comp p q = (p.1 * q.1, q.2) := rfl

@[simp] theorem actionEpGroupoid_unit (y : U) : (actionEpGroupoid hP).unit y = (1, y) := rfl

@[simp] theorem actionEpGroupoid_inv (p : K × U) :
    (actionEpGroupoid hP).inv p = (p.1⁻¹, p.1 • p.2) := rfl

theorem actionEpGroupoid_toGroupoidStr :
    (actionEpGroupoid hP).toGroupoidStr = GroupoidStr.translation K U := rfl

/-! #### The isotropy groups -/

/-- **The isotropy group of `K ⋉ U` is the stabilizer**: `G_x ≅ K_x`, `(k, x) ↦ k`. -/
def isotropyEquivStabilizer (x : U) :
    (actionEpGroupoid hP).Isotropy x ≃* MulAction.stabilizer K x where
  toFun g := ⟨g.val.1, by
    rw [MulAction.mem_stabilizer_iff]
    have h1 : g.val.1 • g.val.2 = x := g.tgt_val
    have h2 : g.val.2 = x := g.src_val
    rw [h2] at h1
    exact h1⟩
  invFun k := ⟨(k.1, x), rfl, MulAction.mem_stabilizer_iff.1 k.2⟩
  left_inv g := GroupoidStr.Isotropy.ext (Prod.ext rfl g.src_val.symm)
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem isotropyEquivStabilizer_apply (x : U) (g : (actionEpGroupoid hP).Isotropy x) :
    (isotropyEquivStabilizer hP x g : K) = g.val.1 := rfl

/-- An object of `K ⋉ U` is regular iff its stabilizer is trivial. -/
theorem isRegular_action_iff {x : U} :
    (actionEpGroupoid hP).IsRegular x ↔ ∀ k : K, k • x = x → k = 1 := by
  constructor
  · intro h k hk
    exact congrArg (fun g : (actionEpGroupoid hP).Isotropy x => g.val.1) (h ⟨(k, x), rfl, hk⟩)
  · intro h g
    exact GroupoidStr.Isotropy.ext (Prod.ext
      (h _ (MulAction.mem_stabilizer_iff.1 (isotropyEquivStabilizer hP x g).2)) g.src_val)

/-- The regular part of `K ⋉ U`: the points with trivial stabilizer. -/
theorem regularSet_action :
    (actionEpGroupoid hP).regularSet = {x | ∀ k : K, k • x = x → k = 1} :=
  Set.ext fun _ => isRegular_action_iff hP

/-! #### The orbit space -/

theorem action_isomorphic_iff {x y : U} :
    (actionEpGroupoid hP).Isomorphic x y ↔ ∃ k : K, k • x = y :=
  ⟨fun ⟨φ, hx, hy⟩ => ⟨φ.1, by rw [← hx]; exact hy⟩, fun ⟨k, hk⟩ => ⟨(k, x), rfl, hk⟩⟩

theorem action_π_eq_π_iff {x y : U} :
    (actionEpGroupoid hP).π x = (actionEpGroupoid hP).π y ↔ ∃ k : K, k • x = y :=
  (actionEpGroupoid hP).π_eq_π_iff.trans (action_isomorphic_iff hP)

/-- **The orbit space of `K ⋉ U` is `U/K`** with its quotient topology. -/
def actionOrbitHomeomorph :
    (actionEpGroupoid hP).OrbitSpace ≃ₜ MulAction.orbitRel.Quotient K U where
  toFun := Quotient.lift (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient K U))
    fun x y h => by
      obtain ⟨k, hk⟩ := (action_isomorphic_iff hP).1 h
      exact Quotient.sound (MulAction.orbitRel_apply.2
        (MulAction.mem_orbit_iff.2 ⟨k⁻¹, by rw [← hk, inv_smul_smul]⟩))
  invFun := Quotient.lift (actionEpGroupoid hP).π fun x y h => by
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact (action_π_eq_π_iff hP).2 ⟨k⁻¹, by rw [← hk, inv_smul_smul]⟩
  left_inv z := Quotient.inductionOn z fun _ => rfl
  right_inv z := Quotient.inductionOn z fun _ => rfl
  continuous_toFun := continuous_quot_mk.quotient_lift _
  continuous_invFun := continuous_quot_mk.quotient_lift _

/-! #### Properness -/

/-- **Every closed subset of `K ⋉ U` is proper** (Definition 7.5.8 (2017: 7.17)). -/
theorem isProperSubset_action {Q : Set U} (hQ : IsClosed Q) :
    (actionEpGroupoid hP).IsProperSubset Q :=
  (action_isProperMap_tgt hP).restrict (hQ.preimage continuous_snd)

/-- In `K ⋉ U` a subset is proper iff it is closed (Proposition 7.5.9 (2017: 7.13) for one direction). -/
theorem isProperSubset_action_iff {Q : Set U} :
    (actionEpGroupoid hP).IsProperSubset Q ↔ IsClosed Q :=
  ⟨(actionEpGroupoid hP).proposition_7_5_9, isProperSubset_action hP⟩

/-- **Every open subset of `K ⋉ U` has the properness property** (Definition 7.5.8 (2017: 7.17)). -/
theorem hasPropernessProperty_action {V : Set U} (hV : IsOpen V) :
    (actionEpGroupoid hP).HasPropernessProperty V :=
  ⟨hV, isProperSubset_action hP isClosed_closure⟩

/-- **`|K ⋉ U|` is paracompact** for second countable `U` (Definition 7.5.1 (2017: 7.15)): `U/K` is second
countable, hence metrizable (Corollary 7.3.6 (2017: 7.1)). -/
theorem hasParacompactOrbitSpace_action [SecondCountableTopology U] :
    (actionEpGroupoid hP).HasParacompactOrbitSpace := by
  have : ContinuousConstSMul K U := ⟨action_continuous_smul hP⟩
  have : SecondCountableTopology (MulAction.orbitRel.Quotient K U) :=
    ContinuousConstSMul.secondCountableTopology
  have : SecondCountableTopology (actionEpGroupoid hP).OrbitSpace :=
    (actionOrbitHomeomorph hP).secondCountableTopology
  have := (actionEpGroupoid hP).corollary_7_3_6
  exact paracompactSpace_of_metrizableSpace _

end Action

/-! ### `ℤ/2 ⋉ ℝ` by reflection -/

section Reflection

theorem units_smul_rn_neg_one (y : Fin 1 → ℝ) : (-1 : ℤˣ) • y = -y := by
  rw [Units.neg_smul, one_smul]

/-- `ℤ/2 = ℤˣ = {±1}` acts on `ℝ` by sc-smooth maps (`y ↦ ±y`). -/
theorem isScSmoothMap_units_smul (k : ℤˣ) :
    (rnPolyfold 1).IsScSmoothMap (rnPolyfold 1) fun y : Fin 1 → ℝ => k • y := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp only [one_smul]
    exact MPolyfold.isScSmoothMap_id
  · simp only [units_smul_rn_neg_one]
    exact (isLocalScDiffeo_rn_neg 1).isScSmoothMap

/-- **`ℤ/2 ⋉ ℝ`**: `ℤ/2 = ℤˣ = {±1}` acting on `ℝ` (`rnPolyfold 1`) by the reflection. -/
def reflectionEpGroupoid : EpGroupoid (Fin 1 → ℝ) (ℤˣ × (Fin 1 → ℝ)) :=
  actionEpGroupoid isScSmoothMap_units_smul

/-- **`ℤ/2 ⋉ ℝ` is effective** (Definition 7.2.1 (2017: 7.11)), not vacuously: `G_0 = ℤ/2`
(`reflectionIsotropyZeroEquiv`) and every neighbourhood of `(−1, 0)` contains `(−1, y)`, `y ≠ 0`,
with `s = y ≠ −y = t`. -/
theorem isEffective_reflection : reflectionEpGroupoid.IsEffective := by
  intro x g hg W hW hgW
  have h2 : g.val.2 = x := g.src_val
  have ht : g.val.1 • g.val.2 = x := g.tgt_val
  have h1 : g.val.1 = -1 := (Int.units_eq_one_or _).resolve_left fun h =>
    hg (GroupoidStr.Isotropy.ext (Prod.ext h h2))
  have hx : x = 0 := by
    rw [h1, h2, units_smul_rn_neg_one] at ht
    exact neg_eq_self.1 ht
  have hS : IsOpen {y : Fin 1 → ℝ | ((-1 : ℤˣ), y) ∈ W} :=
    hW.preimage (continuous_const.prodMk continuous_id)
  have hg0 : g.val = ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) := Prod.ext h1 (h2.trans hx)
  have h0S : (0 : Fin 1 → ℝ) ∈ {y : Fin 1 → ℝ | ((-1 : ℤˣ), y) ∈ W} := by
    change ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) ∈ W
    rw [← hg0]
    exact hgW
  have hN : {y : Fin 1 → ℝ | ((-1 : ℤˣ), y) ∈ W} ∈ 𝓝[≠] (0 : Fin 1 → ℝ) :=
    mem_nhdsWithin_of_mem_nhds (hS.mem_nhds h0S)
  obtain ⟨y, hyW, hy0⟩ := Filter.nonempty_of_mem (inter_mem hN self_mem_nhdsWithin)
  refine ⟨((-1 : ℤˣ), y), hyW, ?_⟩
  change y ≠ (-1 : ℤˣ) • y
  rw [units_smul_rn_neg_one]
  exact fun h => hy0 (self_eq_neg.1 h)

/-- The non-trivial element `(−1, 0)` of `G_0`. -/
def reflectionIsotropyNegOne : reflectionEpGroupoid.Isotropy 0 :=
  ⟨((-1 : ℤˣ), 0), rfl, smul_zero _⟩

theorem reflectionIsotropyNegOne_ne_one : reflectionIsotropyNegOne ≠ 1 := fun h =>
  absurd (congrArg (fun g : reflectionEpGroupoid.Isotropy 0 => g.val.1) h : (-1 : ℤˣ) = 1)
    (by decide)

/-- **Definition 7.2.1 (2017: 7.11) is satisfied non-vacuously**: `ℤ/2 ⋉ ℝ` is effective and has an object with
non-trivial isotropy. -/
theorem isEffective_reflection_nonvacuous : reflectionEpGroupoid.IsEffective ∧
    ∃ (x : Fin 1 → ℝ) (g : reflectionEpGroupoid.Isotropy x), g ≠ 1 :=
  ⟨isEffective_reflection, 0, reflectionIsotropyNegOne, reflectionIsotropyNegOne_ne_one⟩

/-- **The regular part of `ℤ/2 ⋉ ℝ` is `ℝ ∖ {0}`**: open, dense, not all of `ℝ`. -/
theorem regularSet_reflection : reflectionEpGroupoid.regularSet = {x | x ≠ 0} := by
  rw [reflectionEpGroupoid, regularSet_action]
  ext x
  change (∀ k : ℤˣ, k • x = x → k = 1) ↔ x ≠ 0
  refine ⟨fun h hx => absurd (h (-1) (by rw [hx, smul_zero])) (by decide), fun hx k hk => ?_⟩
  rcases Int.units_eq_one_or k with rfl | rfl
  · rfl
  · rw [units_smul_rn_neg_one] at hk
    exact absurd (neg_eq_self.1 hk) hx

/-- `G_0 ≅ ℤ/2` in `ℤ/2 ⋉ ℝ`. -/
def reflectionIsotropyZeroEquiv : reflectionEpGroupoid.Isotropy 0 ≃* ℤˣ :=
  (isotropyEquivStabilizer isScSmoothMap_units_smul 0).trans
    ((MulEquiv.subgroupCongr (eq_top_iff.2 fun k _ =>
      MulAction.mem_stabilizer_iff.2 (smul_zero k))).trans Subgroup.topEquiv)

/-- In `ℤ/2 ⋉ ℝ` every `T_x` is trivial (while `G_0 = ℤ/2`). -/
theorem trivialSubgroup_reflection (x : Fin 1 → ℝ) : reflectionEpGroupoid.trivialSubgroup x = ⊥ :=
  reflectionEpGroupoid.isEffective_iff_trivialSubgroup_eq_bot.1 isEffective_reflection x

/-- `ℤ/2 ⋉ ℝ` is tame (Definition 7.1.6 (2017: 7.6)). -/
theorem isTame_reflection : reflectionEpGroupoid.IsTame := rnPolyfold_isTame

/-- `|ℤ/2 ⋉ ℝ| = ℝ/±1` is paracompact (Definition 7.5.1 (2017: 7.15)). -/
theorem hasParacompactOrbitSpace_reflection : reflectionEpGroupoid.HasParacompactOrbitSpace :=
  hasParacompactOrbitSpace_action isScSmoothMap_units_smul

end Reflection

/-! ### The trivial action of `ℤ/3` on `ℝ` -/

section TrivialZ3

/-- The trivial action of `ℤ/3 = Multiplicative (ZMod 3)` on `ℝ`. -/
scoped instance instMulActionZ3 : MulAction (Multiplicative (ZMod 3)) (Fin 1 → ℝ) where
  smul _ y := y
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem z3_smul_eq (k : Multiplicative (ZMod 3)) (y : Fin 1 → ℝ) : k • y = y := rfl

theorem isScSmoothMap_z3_smul (k : Multiplicative (ZMod 3)) :
    (rnPolyfold 1).IsScSmoothMap (rnPolyfold 1) fun y : Fin 1 → ℝ => k • y :=
  MPolyfold.isScSmoothMap_id

/-- **`ℤ/3 × ℝ ⇉ ℝ`**: the translation groupoid of the trivial action of `ℤ/3` on `ℝ`
(`s = t = π₂`). -/
def trivialZ3EpGroupoid : EpGroupoid (Fin 1 → ℝ) (Multiplicative (ZMod 3) × (Fin 1 → ℝ)) :=
  actionEpGroupoid isScSmoothMap_z3_smul

/-- `G_x ≅ ℤ/3` for every `x`. -/
def trivialZ3IsotropyEquiv (x : Fin 1 → ℝ) :
    trivialZ3EpGroupoid.Isotropy x ≃* Multiplicative (ZMod 3) where
  toFun g := g.val.1
  invFun k := ⟨(k, x), rfl, rfl⟩
  left_inv g := GroupoidStr.Isotropy.ext (Prod.ext rfl g.src_val.symm)
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- **`T_x = G_x`**: every element acts trivially (`s = t` everywhere). -/
theorem trivialSubgroup_trivialZ3 (x : Fin 1 → ℝ) : trivialZ3EpGroupoid.trivialSubgroup x = ⊤ :=
  eq_top_iff.2 fun _ _ => trivialZ3EpGroupoid.mem_trivialSet_iff_eventually.2
    (Eventually.of_forall fun _ => rfl)

/-- `T_x ≅ ℤ/3` for every `x`. -/
def trivialZ3TrivialSubgroupEquiv (x : Fin 1 → ℝ) :
    trivialZ3EpGroupoid.trivialSubgroup x ≃* Multiplicative (ZMod 3) :=
  ((MulEquiv.subgroupCongr (trivialSubgroup_trivialZ3 x)).trans Subgroup.topEquiv).trans
    (trivialZ3IsotropyEquiv x)

/-- `ℤ/3 × ℝ ⇉ ℝ` is **not effective**. -/
theorem not_isEffective_trivialZ3 : ¬ trivialZ3EpGroupoid.IsEffective := by
  intro h
  obtain ⟨ψ, -, hψ⟩ := h 0 ⟨(Multiplicative.ofAdd 1, 0), rfl, rfl⟩ (fun h1 => absurd
    (congrArg (fun g : trivialZ3EpGroupoid.Isotropy 0 => g.val.1) h1 :
      Multiplicative.ofAdd (1 : ZMod 3) = 1) (by decide)) univ isOpen_univ (mem_univ _)
  exact hψ rfl

/-- **The regular set can be empty** (p. 239): `X_reg = ∅` for `ℤ/3 × ℝ ⇉ ℝ`. -/
theorem regularSet_trivialZ3 : trivialZ3EpGroupoid.regularSet = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  have h := (isRegular_action_iff isScSmoothMap_z3_smul).1 hx (Multiplicative.ofAdd 1) rfl
  exact absurd h (by decide)

end TrivialZ3

/-! ### The remark after Definition 7.1.7 (2017: 7.7) -/

section Remark

/-- **The functor of PLAN II.6, 1** on `ℤ/3 × ℝ ⇉ ℝ`: the identity on objects, `(g, y) ↦ (g, y)`
for `y ≤ 0` and `(g², y)` for `y > 0`. -/
def remarkFunctor :
    GroupoidFunctor trivialZ3EpGroupoid.toGroupoidStr trivialZ3EpGroupoid.toGroupoidStr where
  obj y := y
  mor φ := if 0 < φ.2 0 then (φ.1 ^ 2, φ.2) else φ
  src_mor φ := by split_ifs <;> rfl
  tgt_mor φ := by split_ifs <;> rfl
  mor_comp φ ψ h := by
    have h' : φ.2 = ψ.2 := h
    change (if 0 < ψ.2 0 then ((φ.1 * ψ.1) ^ 2, ψ.2) else (φ.1 * ψ.1, ψ.2)) =
      ((if 0 < φ.2 0 then (φ.1 ^ 2, φ.2) else φ).1 * (if 0 < ψ.2 0 then (ψ.1 ^ 2, ψ.2) else ψ).1,
        (if 0 < ψ.2 0 then (ψ.1 ^ 2, ψ.2) else ψ).2)
    rw [h']
    split_ifs
    · exact Prod.ext (mul_pow _ _ _) rfl
    · rfl
  mor_unit x := by
    change (if 0 < x 0 then ((1 : Multiplicative (ZMod 3)) ^ 2, x) else (1, x)) = (1, x)
    split_ifs
    · rw [one_pow]
    · rfl

theorem remarkFunctor_obj (y : Fin 1 → ℝ) : remarkFunctor.obj y = y := rfl

theorem remarkFunctor_mor (φ : Multiplicative (ZMod 3) × (Fin 1 → ℝ)) :
    remarkFunctor.mor φ = if 0 < φ.2 0 then (φ.1 ^ 2, φ.2) else φ := rfl

/-- The functor is sc-smooth on the object spaces (the identity). -/
theorem isScSmoothMap_remarkFunctor_obj :
    trivialZ3EpGroupoid.PObj.IsScSmoothMap trivialZ3EpGroupoid.PObj remarkFunctor.obj :=
  MPolyfold.isScSmoothMap_id

/-- The functor is **not continuous on the morphism spaces**: `y ↦ (f(g, y)).1` is `g` at `0` and
`g² ≠ g` at `1`, while `ℝ` is connected and `ℤ/3` discrete. -/
theorem not_continuous_remarkFunctor_mor : ¬ Continuous remarkFunctor.mor := by
  intro h
  have hc : Continuous fun y : Fin 1 → ℝ => (remarkFunctor.mor (Multiplicative.ofAdd 1, y)).1 :=
    continuous_fst.comp (h.comp (continuous_const.prodMk continuous_id))
  have h01 := PreconnectedSpace.constant inferInstance hc (x := 0) (y := fun _ => 1)
  simp only [remarkFunctor_mor, Pi.zero_apply, lt_self_iff_false, zero_lt_one,
    ↓reduceIte] at h01
  exact absurd h01 (by decide)

/-- The functor is not sc-smooth on the morphism spaces. -/
theorem not_isScSmoothMap_remarkFunctor_mor :
    ¬ trivialZ3EpGroupoid.PMor.IsScSmoothMap trivialZ3EpGroupoid.PMor remarkFunctor.mor :=
  fun h => not_continuous_remarkFunctor_mor (continuousOn_univ.1 h.continuousOn)

/-- The functor is not a morphism of `EP`. -/
theorem not_exists_epFunctor_remarkFunctor :
    ¬ ∃ F : EpFunctor trivialZ3EpGroupoid trivialZ3EpGroupoid,
      F.toGroupoidFunctor = remarkFunctor := by
  rintro ⟨F, hF⟩
  have h := F.continuous_mor
  rw [show F.mor = remarkFunctor.mor from congrArg GroupoidFunctor.mor hF] at h
  exact not_continuous_remarkFunctor_mor h

/-- **The remark after Definition 7.1.7 (2017: 7.7) does not hold as we read it**: a functor between
ep-groupoids that is sc-smooth on the object spaces need not be continuous, nor sc-smooth, on the
morphism spaces, and need not be a morphism of `EP`.  (With continuity on morphisms it holds:
`EpFunctor.ofContinuous`.) -/
theorem remark_definition_7_1_7_counterexample :
    ∃ F : GroupoidFunctor trivialZ3EpGroupoid.toGroupoidStr trivialZ3EpGroupoid.toGroupoidStr,
      trivialZ3EpGroupoid.PObj.IsScSmoothMap trivialZ3EpGroupoid.PObj F.obj ∧
      ¬ Continuous F.mor ∧
      ¬ trivialZ3EpGroupoid.PMor.IsScSmoothMap trivialZ3EpGroupoid.PMor F.mor ∧
      ¬ ∃ E : EpFunctor trivialZ3EpGroupoid trivialZ3EpGroupoid, E.toGroupoidFunctor = F :=
  ⟨remarkFunctor, isScSmoothMap_remarkFunctor_obj, not_continuous_remarkFunctor_mor,
    not_isScSmoothMap_remarkFunctor_mor, not_exists_epFunctor_remarkFunctor⟩

end Remark

/-! ### Definition 7.1.3 (2017: 7.3) (3): the pair groupoid of `ℤ` -/

section Pair

/-- **The pair groupoid of `ℤ`**: objects `ℤ`, one morphism `(b, a) : a → b` for every pair,
`(c, b) ∘ (b, a) = (c, a)`. -/
def pairGroupoidStr : GroupoidStr ℤ (ℤ × ℤ) where
  src p := p.2
  tgt p := p.1
  comp p q := (p.1, q.2)
  unit x := (x, x)
  inv p := (p.2, p.1)
  src_comp _ _ _ := rfl
  tgt_comp _ _ _ := rfl
  comp_assoc _ _ _ _ _ := rfl
  src_unit _ := rfl
  tgt_unit _ := rfl
  comp_unit _ := rfl
  unit_comp _ := rfl
  src_inv _ := rfl
  tgt_inv _ := rfl
  comp_inv _ := rfl
  inv_comp _ := rfl

/-- Every map between discrete M-polyfolds is a local sc-diffeomorphism (sheets `{p} → {f p}`). -/
private theorem isLocalScDiffeo_of_discrete {A B : Type*} [TopologicalSpace A]
    [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] (f : A → B) :
    (discretePolyfold A).IsLocalScDiffeo (discretePolyfold B) f := fun p =>
  ⟨{p}, {f p}, fun _ => p, rfl,
    { isScSmoothOn := (isScSmoothMap_discrete_of_continuous continuous_of_discreteTopology).mono
        (isOpen_discrete _) (subset_univ _)
      isScSmoothOn_inv := (isScSmoothMap_const_discrete p).mono (isOpen_discrete _)
        (subset_univ _)
      mapsTo := fun q hq => by rw [mem_singleton_iff.1 hq]; exact mem_singleton _
      mapsTo_inv := fun _ _ => mem_singleton p
      left_inv := fun _ hq => (mem_singleton_iff.1 hq).symm
      right_inv := fun _ hb => (mem_singleton_iff.1 hb).symm }⟩

/-- `t : s⁻¹({x}) = ℤ × {x} → ℤ` is proper (a bijection of discrete spaces). -/
theorem pair_isProperMap (x : ℤ) :
    IsProperMap ((pairGroupoidStr.src ⁻¹' closure {x}).domRestrict pairGroupoidStr.tgt) := by
  refine (IsClosedEmbedding.of_continuous_injective_isClosedMap continuous_of_discreteTopology
    ?_ fun _ _ => isClosed_discrete _).isProperMap
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have ha' : a.2 = x := by simpa [closure_discrete, pairGroupoidStr] using ha
  have hb' : b.2 = x := by simpa [closure_discrete, pairGroupoidStr] using hb
  exact Subtype.ext (Prod.ext hab (ha'.trans hb'.symm))

/-- **The pair groupoid of `ℤ` is an ep-groupoid**, with `ℤ` and `ℤ × ℤ` discrete M-polyfolds and
`V(x) = {x}` in Definition 7.1.3 (2017: 7.3) (3). -/
def pairEpGroupoid : EpGroupoid ℤ (ℤ × ℤ) where
  toGroupoidStr := pairGroupoidStr
  PObj := discretePolyfold ℤ
  PMor := discretePolyfold (ℤ × ℤ)
  isLocalScDiffeo_src := isLocalScDiffeo_of_discrete _
  isLocalScDiffeo_tgt := isLocalScDiffeo_of_discrete _
  isScSmoothMap_unit := isScSmoothMap_discrete_of_continuous continuous_of_discreteTopology
  isScSmoothMap_inv := isScSmoothMap_discrete_of_continuous continuous_of_discreteTopology
  exists_isProperMap x := ⟨{x}, isOpen_discrete _, rfl, pair_isProperMap x⟩
  isScSmoothComp := by
    let _ := MPolyfold.paracompactSpace_prod (discretePolyfold (ℤ × ℤ))
      (discretePolyfold (ℤ × ℤ))
    let _ := ((discretePolyfold (ℤ × ℤ)).prod (discretePolyfold (ℤ × ℤ))).paracompactSpace_subtype
      (MPolyfold.fibredProduct pairGroupoidStr.src pairGroupoidStr.tgt)
    exact isScSmoothMap_discrete_of_continuous continuous_of_discreteTopology

/-- For the neighbourhood `V = ℤ`, `t : s⁻¹(cl V) = ℤ × ℤ → ℤ` is **not proper**: its fibre over
`0` is `{0} × ℤ`. -/
theorem pair_not_isProperMap_univ :
    ¬ IsProperMap ((pairEpGroupoid.src ⁻¹' closure univ).domRestrict pairEpGroupoid.tgt) := by
  intro hp
  have hfin := (hp.isCompact_preimage (isCompact_singleton (x := (0 : ℤ)))).finite_of_discrete
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℤ => (⟨(0, n), by simp⟩ : ↥(pairEpGroupoid.src ⁻¹' closure univ)))
    (fun m n hmn => ?_) (fun _ => rfl) hfin
  exact congrArg (fun p : ↥(pairEpGroupoid.src ⁻¹' closure univ) => p.1.2) hmn

/-- Every object of the pair groupoid of `ℤ` has an open neighbourhood `V` for which
`t : s⁻¹(cl V) → ℤ` is not proper. -/
theorem pair_exists_not_isProperMap (x : ℤ) : ∃ V : Set ℤ, IsOpen V ∧ x ∈ V ∧
    ¬ IsProperMap ((pairEpGroupoid.src ⁻¹' closure V).domRestrict pairEpGroupoid.tgt) :=
  ⟨univ, isOpen_univ, mem_univ x, pair_not_isProperMap_univ⟩

/-- **The universal reading of Definition 7.1.3 (2017: 7.3) (3) fails** for the pair groupoid of `ℤ`, an
ep-groupoid (`pairEpGroupoid`): "for every open neighbourhood `V` of `x`, `t : s⁻¹(cl V) → X` is
proper" does not hold. -/
theorem pair_not_forall_isProperMap :
    ¬ ∀ x : ℤ, ∀ V : Set ℤ, IsOpen V → x ∈ V →
      IsProperMap ((pairEpGroupoid.src ⁻¹' closure V).domRestrict pairEpGroupoid.tgt) :=
  fun h => pair_not_isProperMap_univ (h 0 univ isOpen_univ (mem_univ 0))

end Pair

end Examples

end EpGroupoid

end Polyfold
