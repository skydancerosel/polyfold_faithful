import Polyfold.Chapter17.VectorBundleGCT
import Polyfold.Chapter17.PolyfoldConstruction
import Polyfold.Chapter10.StrongBundleWeakFibredProductPullback

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.7 "Strong Bundle Structures", pp. 825–828: **Definition 17.7.2** (strong bundle
uniformizer), **Definition 17.7.3** (compatible strong bundle uniformizer construction), the
transition sets `M(Ψ̄, Ψ̄')` and their natural maps to `M(Ψ, Ψ')`, and **Definition 17.7.4**
(strong polyfold bundle construction) with the structural maps listed after it.  Numbers and
pages are the 2021 text's.

# Strong bundle structures

## The text, paraphrased

(Definition 17.7.2) For a vector bundle GCT `P : E → C`, a strong bundle uniformizer at `α` is a
functor `Ψ̄ : G ⋉ K → E` covering a local uniformizer `Ψ ∈ F(α)`, where (1) `G ⋉ K` is the
translation groupoid of a strong bundle `p : K → O` with an action of `G` by strong bundle
isomorphisms, (2) `Ψ̄` is fully faithful and for every `q ∈ O` the map `K_q → P⁻¹(Ψ(q))`,
`k ↦ Ψ̄(k)`, is a Banach space isomorphism, (3) `|Ψ̄| : |K| → |E|` is a homeomorphism onto an open
set `|P|⁻¹(U)`, covering `|Ψ| : |O| → U`.

(Definition 17.7.3) A compatible strong bundle uniformizer construction associates to every `α`
a set `F̄(α)` of strong bundle uniformizers such that `(α, 0)` is in the image and the underlying
`Ψ` belongs to `F(α)`.

(p. 826) The transition set `M(Ψ̄, Ψ̄')` is the weak fibred product of `Ψ̄` and `Ψ̄'`: the
`(k, (φ, Ψ̄(k)), k')` with `φ : Ψ(p(k)) → Ψ'(p'(k'))` and `Ψ̄'(k') = μ(φ)(Ψ̄(k))`; it maps to
`M(Ψ, Ψ')` by `(k, (φ, Ψ̄(k)), k') ↦ (p(k), φ, p'(k'))`, the fibres are Banach spaces, and the
structural maps are fibrewise linear.

(Definition 17.7.4) A strong polyfold bundle construction is such an `F̄` together with a strong
bundle structure on every `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` over the M-polyfold `M(Ψ, Ψ')` of the polyfold
structure, such that (p. 827) `s̄` and `t̄` are sc-smooth strong bundle maps covering `s` and `t`
which are local strong bundle isomorphisms, the inversion `ῑ` is an sc-smooth strong bundle
isomorphism covering `ι`, the unit `ū` and the multiplication `m̄` are sc-smooth strong bundle
maps covering `u` and `m`.

## What is formalized (namespace `Polyfold.GCT.VectorBundle`)

* `StrongBundleUniformizerData`: the data of Definition 17.7.2 (1), (2): a local uniformizer
  `base` (`Ψ`), a strong bundle `B : p : K → O` with a `G`-action by strong bundle maps covering
  the action on `O`, and the fibre isomorphisms `fiber q : K_q ≃L μ(Ψ(q))`; the functor `Ψ̄`
  (`functor`, objects `obj k = (Ψ(p k), fiber (p k) k)`) is a functor `G ⋉ K → E` covering `Ψ`
  because of `obj_smul`.  `obj_injective`, `full`, `faithful`: Definition 17.7.2 (2).
* `StrongBundleUniformizer` (**Definition 17.7.2**): (3) `isOpenEmbedding_orbitMap`,
  `range_orbitMap`.  `exists_obj_eq_zero`: `(α, 0)` is in the image (Definition 17.7.3).
* `StrongBundleUniformizerConstruction` (**Definition 17.7.3**).
* `Trans Ψ̄ Ψ̄'` (the transition set `M(Ψ̄, Ψ̄')`), `transBase` (the natural map to `M(Ψ, Ψ')`),
  `transAct a k` (the element `k'` of `(k, (φ, Ψ̄(k)), k')` for `a = (p(k), φ, q')`),
  `transEquiv : M(Ψ̄, Ψ̄') ≃ s*K` (the pull-back of `K` along `s : M(Ψ, Ψ') → O`),
  `transBase_transEquiv_symm`, `transAct_unit`, `transAct_comp`, `transAct_inv` (the algebra of
  the structural maps).
* `StrongPolyfoldBundleConstruction` (**Definition 17.7.4**), with `isLocalStrongBundleIso_src`
  (`s̄`), `isStrongBundleMap_inv` and `transInv_transInv` (`ῑ`), `isStrongBundleMap_unit` (`ū`).

## Readings

* (Definition 17.7.2 (2)) We read "`Ψ̄` covers `Ψ`" as `P ∘ Ψ̄ = Ψ ∘ p` on objects and morphisms.
  A functor covering `Ψ` is then the same as the fibre maps `K_q → P⁻¹(Ψ(q))`, so the structure
  carries the fibre maps `fiber q` (Banach space isomorphisms, as (2) requires) and the functor
  is built from them; full faithfulness and injectivity on objects are then consequences
  (`full`, `faithful`, `obj_injective`).  `P⁻¹(Ψ(α))` in (2) is read as `P⁻¹(Ψ(q))`.
* (Definition 17.7.2 (1)) "an action by strong bundle isomorphisms" is read as: `p(g ∗ k) = g ∗ p(k)`
  and every `k ↦ g ∗ k` is a strong bundle map covering `q ↦ g ∗ q` (its inverse `g⁻¹ ∗ ·` is one as
  well, so these are strong bundle isomorphisms).
* (Definition 17.7.3) `Ψ̄ : G ⋉ K → C` is read as `Ψ̄ : G ⋉ K → E`, as in Definition 17.7.2 and
  Definition 17.7.4.  "`(α, 0)` is in the image" holds for every strong bundle uniformizer whose
  base is at `α` (`exists_obj_eq_zero`).
* (Definition 17.7.4) The strong bundle structure on `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` is read as the
  pull-back `s*K` of `p : K → O` along `s : M(Ψ, Ψ') → O`, transported along the natural bijection
  `transEquiv : M(Ψ̄, Ψ̄') ≃ s*K`, `(k, (φ, Ψ̄ k), k') ↦ ((p k, φ, p' k'), k)`.  The text requires
  `s̄` to be a strong bundle map covering `s` which is fibrewise a Banach space isomorphism
  (`K_q ≅ P⁻¹(Ψ(q)) ≅` the fibre of `M(Ψ̄, Ψ̄')`), and for such a structure `s̄` identifies it with
  `s*K`; the pull-back is the canonical representative.  In this form `s̄` is the projection
  `s*K → K`, a local strong bundle isomorphism since `s` is a local sc-diffeomorphism
  (`isLocalStrongBundleIso_src`), and `t̄` is the map `T(a, k) = transAct a k`; the data of
  Definition 17.7.4 are the conditions that `T` is a strong bundle map covering `t`
  (`isStrongBundleMap_trans`) and a local strong bundle isomorphism
  (`isLocalStrongBundleIso_trans`).  The inversion `ῑ(a, k) = (a⁻¹, T(a, k))` and the unit
  `ū(k) = (1_{p k}, k)` are then strong bundle maps covering `ι` and `u`
  (`isStrongBundleMap_inv`, `isStrongBundleMap_unit`), `ῑ ∘ ῑ = 1` (`transInv_transInv`), and the
  multiplication `m̄((b, k'), (a, k)) = (b ∘ a, k)` satisfies `T(b ∘ a, k) = T(b, T(a, k))`
  (`transAct_comp`).
* The universes: `O`, `K`, `G` and the Banach spaces `μ(α)` all live in the universe of `C`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace GCT

namespace VectorBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor

variable {C : GCT.{u}} (V : C.VectorBundle)

/-- **The data of 2021 Definition 17.7.2 (1), (2), p. 826**: a local uniformizer `Ψ = base`, a
strong bundle `p : K → O` over its M-polyfold `O` with an action of `G` by strong bundle maps
covering the action on `O`, and the fibre isomorphisms `K_q ≃L μ(Ψ(q))` such that the induced
object map `k ↦ (Ψ(p k), fiber (p k) k)` is `G`-equivariant (`obj_smul`), which makes it a functor
`Ψ̄ : G ⋉ K → E` covering `Ψ` (`functor`). -/
structure StrongBundleUniformizerData : Type (u + 1) where
  /-- The underlying local uniformizer `Ψ : G ⋉ O → C`. -/
  base : C.LocalUniformizer
  /-- The total space `K`. -/
  K : Type u
  [topK : TopologicalSpace K]
  [t2K : T2Space K]
  [paraK : ParacompactSpace K]
  /-- The projection `p : K → O`. -/
  p : K → base.O
  [addK : ∀ q, AddCommGroup (p ⁻¹' {q})]
  [modK : ∀ q, Module ℝ (p ⁻¹' {q})]
  /-- (1) The strong bundle structure of `p : K → O`. -/
  B : StrongBundle base.P p
  [actK : MulAction base.G K]
  /-- (1) The action covers the action on `O`. -/
  p_smul : ∀ (g : base.G) (k : K), p (g • k) = g • p k
  /-- (1) `G` acts by strong bundle maps. -/
  isStrongBundleMap_smul : ∀ g : base.G, B.IsStrongBundleMap B (fun q => g • q) fun k => g • k
  /-- (2) The fibre maps `K_q → P⁻¹(Ψ(q)) = μ(Ψ(q))`, Banach space isomorphisms. -/
  fiber : ∀ q : base.O, (p ⁻¹' {q}) ≃L[ℝ] V.V (base.obj q)
  /-- `Ψ̄(g ∗ k) = μ(Ψ(g, p k))(Ψ̄(k))`: the object map is that of a functor `G ⋉ K → E`. -/
  obj_smul : ∀ (g : base.G) (k : K),
    V.act (base.mor (g, p k)) (V.objMk (base.obj (p k)) (fiber (p k) ⟨k, rfl⟩))
      (base.functor.src_mor (g, p k)).symm =
    V.objMk (base.obj (p (g • k))) (fiber (p (g • k)) ⟨g • k, rfl⟩)

attribute [instance] StrongBundleUniformizerData.topK StrongBundleUniformizerData.t2K
  StrongBundleUniformizerData.paraK StrongBundleUniformizerData.addK
  StrongBundleUniformizerData.modK StrongBundleUniformizerData.actK

namespace StrongBundleUniformizerData

variable {V} (Ψ : V.StrongBundleUniformizerData)

/-- `Ψ̄(k) = (Ψ(p k), fiber (p k) k) ∈ P⁻¹(Ψ(p k))`. -/
def obj (k : Ψ.K) : V.EObj := V.objMk (Ψ.base.obj (Ψ.p k)) (Ψ.fiber (Ψ.p k) ⟨k, rfl⟩)

theorem base_obj (k : Ψ.K) : V.base (Ψ.obj k) = Ψ.base.obj (Ψ.p k) := rfl

theorem obj_of_eq {k : Ψ.K} {q : Ψ.base.O} (hk : Ψ.p k = q) :
    Ψ.obj k = V.objMk (Ψ.base.obj q) (Ψ.fiber q ⟨k, hk⟩) := by
  subst hk; rfl

/-- The morphism `Ψ̄(g, k) = (Ψ(g, p k), Ψ̄(k))`. -/
def mor (x : Ψ.base.G × Ψ.K) : V.EMor :=
  ⟨(Ψ.base.mor (x.1, Ψ.p x.2), Ψ.obj x.2), (Ψ.base.functor.src_mor (x.1, Ψ.p x.2)).symm⟩

theorem obj_smul' (g : Ψ.base.G) (k : Ψ.K) :
    V.act (Ψ.base.mor (g, Ψ.p k)) (Ψ.obj k) (Ψ.base.functor.src_mor (g, Ψ.p k)).symm =
      Ψ.obj (g • k) := Ψ.obj_smul g k

/-- **The functor `Ψ̄ : G ⋉ K → E`** of Definition 17.7.2. -/
def functor : GroupoidFunctor (GroupoidStr.translation Ψ.base.G Ψ.K) V.groupoid where
  obj := Ψ.obj
  mor := Ψ.mor
  src_mor _ := rfl
  tgt_mor x := Ψ.obj_smul' x.1 x.2
  mor_comp x y h := by
    have hy : (x.2 : Ψ.K) = y.1 • y.2 := h
    have hc : V.groupoid.src (Ψ.mor x) = V.groupoid.tgt (Ψ.mor y) := by
      change Ψ.obj x.2 = V.act (Ψ.mor y).φ (Ψ.mor y).e (Ψ.mor y).2
      rw [hy]; exact (Ψ.obj_smul' y.1 y.2).symm
    obtain ⟨h1, h2⟩ := groupoid_comp_of hc
    refine EMor.ext ?_ ?_
    · rw [h1]
      change Ψ.base.mor (x.1 * y.1, Ψ.p y.2) = _
      have hb := Ψ.base.functor.mor_comp (x.1, Ψ.p x.2) (y.1, Ψ.p y.2)
        (by change Ψ.p x.2 = y.1 • Ψ.p y.2; rw [hy, Ψ.p_smul])
      exact hb
    · rw [h2]; rfl
  mor_unit k := EMor.ext (Ψ.base.functor.mor_unit (Ψ.p k)) rfl

@[simp] theorem functor_obj (k : Ψ.K) : Ψ.functor.obj k = Ψ.obj k := rfl

@[simp] theorem functor_mor (x : Ψ.base.G × Ψ.K) : Ψ.functor.mor x = Ψ.mor x := rfl

/-- `P ∘ Ψ̄ = Ψ ∘ p` on objects. -/
theorem proj_obj_functor (k : Ψ.K) : V.proj.obj (Ψ.obj k) = Ψ.base.obj (Ψ.p k) := rfl

/-- `P ∘ Ψ̄ = Ψ ∘ p` on morphisms. -/
theorem proj_mor_functor (x : Ψ.base.G × Ψ.K) :
    V.proj.mor (Ψ.mor x) = Ψ.base.mor (x.1, Ψ.p x.2) := rfl

/-- **Definition 17.7.2 (2)**: `Ψ̄` is injective on objects. -/
theorem obj_injective : Injective Ψ.obj := by
  intro k k' h
  have hq : Ψ.p k = Ψ.p k' := Ψ.base.injective_obj (congrArg Sigma.fst h)
  rw [Ψ.obj_of_eq hq, Ψ.obj_of_eq (rfl : Ψ.p k' = Ψ.p k')] at h
  have := (Ψ.fiber (Ψ.p k')).injective ((objMk_eq_iff).1 h)
  exact congrArg Subtype.val this

/-- **The lift** `k ∈ K_q` with `Ψ̄(k) = e`, for `e ∈ P⁻¹(Ψ(q))`. -/
def lift (q : Ψ.base.O) (e : V.EObj) (he : V.base e = Ψ.base.obj q) : Ψ.K :=
  ((Ψ.fiber q).symm (cast (congrArg V.V he) e.2)).1

theorem p_lift (q : Ψ.base.O) (e : V.EObj) (he : V.base e = Ψ.base.obj q) :
    Ψ.p (Ψ.lift q e he) = q := ((Ψ.fiber q).symm (cast (congrArg V.V he) e.2)).2

theorem obj_lift (q : Ψ.base.O) (e : V.EObj) (he : V.base e = Ψ.base.obj q) :
    Ψ.obj (Ψ.lift q e he) = e := by
  rw [Ψ.obj_of_eq (Ψ.p_lift q e he)]
  have : (⟨Ψ.lift q e he, Ψ.p_lift q e he⟩ : Ψ.p ⁻¹' {q}) =
      (Ψ.fiber q).symm (cast (congrArg V.V he) e.2) := rfl
  rw [this, ContinuousLinearEquiv.apply_symm_apply]
  obtain ⟨β, v⟩ := e
  change β = Ψ.base.obj q at he
  subst he; rfl

theorem lift_obj (k : Ψ.K) : Ψ.lift (Ψ.p k) (Ψ.obj k) rfl = k :=
  Ψ.obj_injective (Ψ.obj_lift _ _ _)

theorem lift_eq_iff {q : Ψ.base.O} {e : V.EObj} (he : V.base e = Ψ.base.obj q) (k : Ψ.K) :
    Ψ.lift q e he = k ↔ Ψ.obj k = e :=
  ⟨fun h => h ▸ Ψ.obj_lift q e he, fun h => Ψ.obj_injective ((Ψ.obj_lift q e he).trans h.symm)⟩

/-- **Definition 17.7.2 (2)**: `Ψ̄` is faithful. -/
theorem faithful : Ψ.functor.toFunctor.Faithful := by
  refine (GroupoidFunctor.faithful_iff _).2 fun x y hs _ hm => ?_
  have hs' : x.2 = y.2 := hs
  have hb : Ψ.base.mor (x.1, Ψ.p x.2) = Ψ.base.mor (y.1, Ψ.p y.2) := congrArg EMor.φ hm
  have := Ψ.base.toUniformizer.mor_injective hb
  exact Prod.ext (Prod.mk.inj this).1 hs'

/-- **Definition 17.7.2 (2)**: `Ψ̄` is full. -/
theorem full : Ψ.functor.toFunctor.Full := by
  refine (GroupoidFunctor.full_iff _).2 fun k k' a hs ht => ?_
  have hs' : a.e = Ψ.obj k := hs
  have hφs : C.toGroupoidStr.src a.φ = Ψ.base.obj (Ψ.p k) :=
    a.2.symm.trans (congrArg V.base hs')
  have hφt : C.toGroupoidStr.tgt a.φ = Ψ.base.obj (Ψ.p k') := by
    have := congrArg V.base ht; exact this
  obtain ⟨g, hg, hm⟩ := Ψ.base.toUniformizer.exists_smul_eq_mor hφs hφt
  refine ⟨(g, k), rfl, ?_, EMor.ext hm hs'.symm⟩
  apply Ψ.obj_injective
  change Ψ.obj (g • k) = Ψ.obj k'
  refine (Ψ.obj_smul' g k).symm.trans ((act_congr hm hs'.symm _ a.2).trans ?_)
  exact ht

end StrongBundleUniformizerData

/-- **2021 Definition 17.7.2, p. 826 (strong bundle uniformizer)**: the data
`StrongBundleUniformizerData` ((1), (2)) such that (3) `|Ψ̄| : |K| → |E|` is a homeomorphism onto
an open subset of the form `|P|⁻¹(U)`, `U` the footprint of `Ψ`. -/
structure StrongBundleUniformizer : Type (u + 1) extends V.StrongBundleUniformizerData where
  /-- (3) `|Ψ̄|` is a homeomorphism onto an open subset. -/
  isOpenEmbedding_orbitMap : IsOpenEmbedding toStrongBundleUniformizerData.functor.orbitMap
  /-- (3) Its image is `|P|⁻¹(U)`, `U = |Ψ|(|O|)`. -/
  range_orbitMap : range toStrongBundleUniformizerData.functor.orbitMap =
    V.proj.orbitMap ⁻¹' base.footprint

namespace StrongBundleUniformizer

variable {V} (Ψ : V.StrongBundleUniformizer)

/-- The footprint `|P|⁻¹(U)` of `Ψ̄` (p. 826). -/
def footprint : Set V.groupoid.OrbitSpace := range Ψ.functor.orbitMap

theorem footprint_eq : Ψ.footprint = V.proj.orbitMap ⁻¹' Ψ.base.footprint := Ψ.range_orbitMap

/-- **Definition 17.7.3, "(α, 0) is in the image"**: for a strong bundle uniformizer at `α`
(its base is at `α`), the zero `(α, 0)` of `P⁻¹(α)` is `Ψ̄(k)` for some `k`. -/
theorem exists_obj_eq_zero {α : C.Obj} (hα : Ψ.base.IsAt α) :
    ∃ k, Ψ.obj k = V.objMk α 0 := by
  obtain ⟨q, rfl⟩ := hα
  refine ⟨((Ψ.fiber q).symm 0).1, ?_⟩
  rw [Ψ.obj_of_eq ((Ψ.fiber q).symm 0).2]
  change V.objMk _ (Ψ.fiber q ((Ψ.fiber q).symm 0)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

end StrongBundleUniformizer

/-! ### Transition sets of strong bundle uniformizers (p. 826) -/

namespace StrongBundleUniformizerData

variable {V} (Ψ Ψ' : V.StrongBundleUniformizerData)

/-- **The transition set `M(Ψ̄, Ψ̄')`** (p. 826): the weak fibred product of `Ψ̄` and `Ψ̄'`, the
`(k, (φ, Ψ̄(k)), k')` with `Ψ̄'(k') = μ(φ)(Ψ̄(k))`. -/
abbrev Trans : Type u := V.groupoid.TransitionSet Ψ.obj Ψ'.obj

variable {Ψ Ψ'}

/-- **The natural map `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`** (p. 826),
`(k, (φ, Ψ̄(k)), k') ↦ (p(k), φ, p'(k'))`. -/
def transBase (a : Ψ.Trans Ψ') : Ψ.base.Trans Ψ'.base where
  src := Ψ.p a.src
  mor := a.mor.φ
  tgt := Ψ'.p a.tgt
  src_mor := by
    rw [← a.mor.2]
    exact congrArg V.base a.src_mor
  tgt_mor := congrArg V.base a.tgt_mor

/-- **The fibre element `k'`** of `(k, (φ, Ψ̄(k)), k')` over `a = (q, φ, q')` with `p(k) = q`: the
lift of `μ(φ)(Ψ̄(k))` to `K'_{q'}`.  This is `t̄` in the pull-back form of `M(Ψ̄, Ψ̄')`. -/
def transAct (a : Ψ.base.Trans Ψ'.base) (k : Ψ.K) (hk : Ψ.p k = a.src) : Ψ'.K :=
  Ψ'.lift a.tgt (V.act a.mor (Ψ.obj k) ((congrArg Ψ.base.obj hk).trans a.src_mor.symm))
    a.tgt_mor

theorem p_transAct (a : Ψ.base.Trans Ψ'.base) (k : Ψ.K) (hk : Ψ.p k = a.src) :
    Ψ'.p (transAct a k hk) = a.tgt := Ψ'.p_lift _ _ _

theorem obj_transAct (a : Ψ.base.Trans Ψ'.base) (k : Ψ.K) (hk : Ψ.p k = a.src) :
    Ψ'.obj (transAct a k hk) =
      V.act a.mor (Ψ.obj k) ((congrArg Ψ.base.obj hk).trans a.src_mor.symm) :=
  Ψ'.obj_lift _ _ _

/-- The pair `((q, φ, q'), k)` as an element of `M(Ψ̄, Ψ̄')`. -/
def transMk (a : Ψ.base.Trans Ψ'.base) (k : Ψ.K) (hk : Ψ.p k = a.src) : Ψ.Trans Ψ' where
  src := k
  mor := ⟨(a.mor, Ψ.obj k), (congrArg Ψ.base.obj hk).trans a.src_mor.symm⟩
  tgt := transAct a k hk
  src_mor := rfl
  tgt_mor := (obj_transAct a k hk).symm

@[simp] theorem transBase_transMk (a : Ψ.base.Trans Ψ'.base) (k : Ψ.K) (hk : Ψ.p k = a.src) :
    transBase (transMk a k hk) = a :=
  GroupoidStr.TransitionSet.ext hk rfl (p_transAct a k hk)

theorem transMk_transBase (b : Ψ.Trans Ψ') : transMk (transBase b) b.src rfl = b := by
  have he : b.mor.e = Ψ.obj b.src := b.src_mor
  refine GroupoidStr.TransitionSet.ext rfl (EMor.ext rfl he.symm) ?_
  apply Ψ'.obj_injective
  exact (obj_transAct (transBase b) b.src rfl).trans ((act_congr rfl he.symm _ b.mor.2).trans b.tgt_mor)

/-- **`M(Ψ̄, Ψ̄')` is the pull-back `s*K`** of `p : K → O` along `s : M(Ψ, Ψ') → O`:
`(k, (φ, Ψ̄ k), k') ↦ ((p k, φ, p' k'), k)`. -/
def transEquiv : Ψ.Trans Ψ' ≃
    pullbackSpace Ψ.p (fun a : Ψ.base.Trans Ψ'.base => a.src) where
  toFun b := ⟨(transBase b, b.src), rfl⟩
  invFun x := transMk x.1.1 x.1.2 x.2
  left_inv b := transMk_transBase b
  right_inv x := by
    obtain ⟨⟨a, k⟩, hk⟩ := x
    exact Subtype.ext (Prod.ext (transBase_transMk a k hk) rfl)

/-- The natural map `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` is the pull-back projection under `transEquiv`. -/
theorem transBase_eq (b : Ψ.Trans Ψ') : transBase b = (transEquiv b).1.1 := rfl

/-- `s̄ = pr₂ ∘ transEquiv`. -/
theorem src_eq (b : Ψ.Trans Ψ') : b.src = (transEquiv b).1.2 := rfl

/-- `t̄ = T ∘ transEquiv`. -/
theorem tgt_eq (b : Ψ.Trans Ψ') :
    b.tgt = transAct (transEquiv b).1.1 (transEquiv b).1.2 (transEquiv b).2 :=
  (congrArg GroupoidStr.TransitionSet.tgt (transMk_transBase b)).symm

/-- **The unit map**: `T(1_q, k) = k`. -/
theorem transAct_unit (k : Ψ.K) :
    transAct (Ψ := Ψ) (Ψ' := Ψ) (GroupoidStr.TransitionSet.unit (Ψ.p k)) k rfl = k := by
  apply Ψ.obj_injective
  refine (obj_transAct (Ψ := Ψ) (Ψ' := Ψ) (GroupoidStr.TransitionSet.unit (Ψ.p k)) k rfl).trans ?_
  exact act_unit' _ _

/-- **The multiplication map**: `T(b ∘ a, k) = T(b, T(a, k))`. -/
theorem transAct_comp {Ψ'' : V.StrongBundleUniformizerData} (b : Ψ'.base.Trans Ψ''.base)
    (a : Ψ.base.Trans Ψ'.base) (hba : b.src = a.tgt) (k : Ψ.K) (hk : Ψ.p k = a.src) :
    transAct (GroupoidStr.TransitionSet.comp b a
        (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt hba)) k hk =
      transAct b (transAct a k hk) ((p_transAct a k hk).trans hba.symm) := by
  apply Ψ''.obj_injective
  have hc := GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt (a := b) (b := a) hba
  refine (obj_transAct (GroupoidStr.TransitionSet.comp b a hc) k hk).trans ?_
  refine (act_comp' b.mor a.mor hc _ _).trans ?_
  refine Eq.trans ?_ (obj_transAct _ _ _).symm
  exact act_congr rfl (obj_transAct a k hk).symm _ _

/-- **The inversion map**: `T(a⁻¹, T(a, k)) = k`. -/
theorem transAct_inv (a : Ψ.base.Trans Ψ'.base) (k : Ψ.K) (hk : Ψ.p k = a.src) :
    transAct (GroupoidStr.TransitionSet.inv a) (transAct a k hk) (p_transAct a k hk) = k := by
  apply Ψ.obj_injective
  refine (obj_transAct (GroupoidStr.TransitionSet.inv a) (transAct a k hk)
    (p_transAct a k hk)).trans ?_
  exact (act_congr rfl (obj_transAct a k hk) _ (C.toGroupoidStr.src_inv _).symm).trans
    (act_inv_act _ _ _)

end StrongBundleUniformizerData

/-! ### Definitions 17.7.3 and 17.7.4 -/

variable (S : C.PolyfoldConstruction)

/-- **2021 Definition 17.7.3, p. 826 (compatible strong bundle uniformizer construction)**: a set
`F̄(α)` of strong bundle uniformizers for every object `α` whose underlying local uniformizers
belong to `F(α)`.  `(α, 0)` is then in the image (`exists_zero_mem`). -/
structure StrongBundleUniformizerConstruction : Type (u + 1) where
  /-- `F̄ : C⁻ → SET`. -/
  F : C.Obj → Set V.StrongBundleUniformizer
  /-- The underlying `Ψ` belongs to `F(α)`. -/
  base_mem : ∀ α, ∀ Ψ ∈ F α, Ψ.base ∈ S.F α

namespace StrongBundleUniformizerConstruction

variable {V S} (U : V.StrongBundleUniformizerConstruction S)

/-- The strong bundle uniformizers of `F̄`. -/
abbrev Unif : Type (u + 1) := {Ψ : V.StrongBundleUniformizer // ∃ α, Ψ ∈ U.F α}

/-- The underlying uniformizer of `S`. -/
abbrev baseUnif (Ψ : U.Unif) : S.Unif :=
  ⟨Ψ.1.base, Ψ.2.elim fun α h => ⟨α, U.base_mem α _ h⟩⟩

@[simp] theorem baseUnif_val (Ψ : U.Unif) : (U.baseUnif Ψ).1 = Ψ.1.base := rfl

/-- **Definition 17.7.3**: `(α, 0)` is in the image of every `Ψ̄ ∈ F̄(α)`. -/
theorem exists_zero_mem {α : C.Obj} {Ψ : V.StrongBundleUniformizer} (hΨ : Ψ ∈ U.F α) :
    ∃ k, Ψ.obj k = V.objMk α 0 :=
  Ψ.exists_obj_eq_zero (S.isAt α _ (U.base_mem α Ψ hΨ))

/-- The pull-back `s*K` of `p : K → O` along `s : M(Ψ, Ψ') → O`, the total space of the strong
bundle `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` (`transEquiv`). -/
abbrev TransSpace (Ψ Ψ' : U.Unif) : Type u :=
  pullbackSpace Ψ.1.p fun a : S.Tr (U.baseUnif Ψ) (U.baseUnif Ψ') => a.src

instance (Ψ Ψ' : U.Unif) : ParacompactSpace (U.TransSpace Ψ Ψ') :=
  Ψ.1.B.paracompactSpace_pullback (S.transPolyfold (U.baseUnif Ψ) (U.baseUnif Ψ')) _

theorem isScSmoothMap_trSrc (Ψ Ψ' : U.Unif) :
    (S.transPolyfold (U.baseUnif Ψ) (U.baseUnif Ψ')).IsScSmoothMap Ψ.1.base.P
      fun a : S.Tr (U.baseUnif Ψ) (U.baseUnif Ψ') => a.src :=
  (S.isLocalScDiffeo_trSrc _ _).isScSmoothMap

/-- **The strong bundle `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`**: the pull-back `s*K` (reading of Definition
17.7.4). -/
def transBundle (Ψ Ψ' : U.Unif) :
    StrongBundle (S.transPolyfold (U.baseUnif Ψ) (U.baseUnif Ψ'))
      (pullbackProj Ψ.1.p fun a : S.Tr (U.baseUnif Ψ) (U.baseUnif Ψ') => a.src) :=
  Ψ.1.B.pullback (U.isScSmoothMap_trSrc Ψ Ψ')

/-- **`t̄ : M(Ψ̄, Ψ̄') → K'`** in the pull-back form: `T(a, k) = transAct a k`. -/
def transT (Ψ Ψ' : U.Unif) (x : U.TransSpace Ψ Ψ') : Ψ'.1.K :=
  StrongBundleUniformizerData.transAct x.1.1 x.1.2 x.2

/-- **`s̄ : M(Ψ̄, Ψ̄') → K`** is a strong bundle map covering `s` and a local strong bundle
isomorphism (since `s` is a local sc-diffeomorphism). -/
theorem isLocalStrongBundleIso_src (Ψ Ψ' : U.Unif) (a : S.Tr (U.baseUnif Ψ) (U.baseUnif Ψ')) :
    ∃ (W : Set (S.Tr (U.baseUnif Ψ) (U.baseUnif Ψ'))) (W' : Set Ψ.1.base.O), a ∈ W ∧
      (U.transBundle Ψ Ψ').IsStrongBundleIsoOn Ψ.1.B
        (Ψ.1.B.isStrongBundleMap_pullbackProj' (U.isScSmoothMap_trSrc Ψ Ψ')) W W' := by
  obtain ⟨W, W', σ, ha, hd⟩ := S.isLocalScDiffeo_trSrc (U.baseUnif Ψ) (U.baseUnif Ψ') a
  exact ⟨W, W', ha, Ψ.1.B.isStrongBundleIsoOn_pullbackProj' (U.isScSmoothMap_trSrc Ψ Ψ') hd a⟩

end StrongBundleUniformizerConstruction

open StrongBundleUniformizerConstruction in
/-- **2021 Definition 17.7.4, p. 827 (strong polyfold bundle construction)**: a compatible strong
bundle uniformizer construction `F̄` together with the strong bundle structures on the transition
sets `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` over the M-polyfolds `M(Ψ, Ψ')` of `S`, read as the pull-backs `s*K`
(`transBundle`, see the module docstring), such that `t̄ = T` is an sc-smooth strong bundle map
covering `t` and a local strong bundle isomorphism.  `s̄` (`isLocalStrongBundleIso_src`), `ῑ`
(`isStrongBundleMap_inv`) and `ū` (`isStrongBundleMap_unit`) are then as listed on p. 827. -/
structure StrongPolyfoldBundleConstruction : Type (u + 1)
    extends V.StrongBundleUniformizerConstruction S where
  /-- `t̄ : M(Ψ̄, Ψ̄') → K'` is a strong bundle map covering `t`. -/
  isStrongBundleMap_trans : ∀ Ψ Ψ' : toStrongBundleUniformizerConstruction.Unif,
    (toStrongBundleUniformizerConstruction.transBundle Ψ Ψ').IsStrongBundleMap Ψ'.1.B
      (fun a => a.tgt) (toStrongBundleUniformizerConstruction.transT Ψ Ψ')
  /-- `t̄` is a local strong bundle isomorphism. -/
  isLocalStrongBundleIso_trans : ∀ Ψ Ψ' : toStrongBundleUniformizerConstruction.Unif,
    ∀ a : S.Tr (toStrongBundleUniformizerConstruction.baseUnif Ψ)
      (toStrongBundleUniformizerConstruction.baseUnif Ψ'),
    ∃ (W : Set (S.Tr (toStrongBundleUniformizerConstruction.baseUnif Ψ)
      (toStrongBundleUniformizerConstruction.baseUnif Ψ'))) (W' : Set Ψ'.1.base.O), a ∈ W ∧
      (toStrongBundleUniformizerConstruction.transBundle Ψ Ψ').IsStrongBundleIsoOn Ψ'.1.B
        (isStrongBundleMap_trans Ψ Ψ') W W'

namespace StrongPolyfoldBundleConstruction

open StrongBundleUniformizerConstruction StrongBundleUniformizerData

variable {V S} (Q : V.StrongPolyfoldBundleConstruction S)

/-- The strong bundle uniformizers of `F̄`. -/
abbrev Unif : Type (u + 1) := Q.toStrongBundleUniformizerConstruction.Unif

/-- **The inversion `ῑ : M(Ψ̄, Ψ̄') → M(Ψ̄', Ψ̄)`** in the pull-back form:
`(a, k) ↦ (a⁻¹, T(a, k))`. -/
def transInv (Ψ Ψ' : Q.Unif) (x : Q.TransSpace Ψ Ψ') : Q.TransSpace Ψ' Ψ :=
  ⟨(S.toTr (GroupoidStr.TransitionSet.inv x.1.1), Q.transT Ψ Ψ' x), p_transAct x.1.1 x.1.2 x.2⟩

/-- **`ῑ ∘ ῑ = 1`**; in particular `ῑ` is bijective with inverse `ῑ`. -/
theorem transInv_transInv (Ψ Ψ' : Q.Unif) (x : Q.TransSpace Ψ Ψ') :
    Q.transInv Ψ' Ψ (Q.transInv Ψ Ψ' x) = x := by
  obtain ⟨⟨a, k⟩, hk⟩ := x
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change GroupoidStr.TransitionSet.inv (GroupoidStr.TransitionSet.inv a) = a
    exact GroupoidStr.TransitionSet.inv_inv a
  · change transAct (GroupoidStr.TransitionSet.inv a) (transAct a k hk) (p_transAct a k hk) = k
    exact transAct_inv a k hk

/-- **`ῑ` is an sc-smooth strong bundle map covering `ι`** (p. 827). -/
theorem isStrongBundleMap_inv (Ψ Ψ' : Q.Unif) :
    (Q.transBundle Ψ Ψ').IsStrongBundleMap (Q.transBundle Ψ' Ψ)
      (fun a => S.toTr (GroupoidStr.TransitionSet.inv a)) (Q.transInv Ψ Ψ') := by
  have := Ψ'.1.B.isStrongBundleMap_pullbackPair (Q.isScSmoothMap_trSrc Ψ' Ψ)
    (S.isScSmoothMap_trInv (Q.baseUnif Ψ) (Q.baseUnif Ψ')) (Q.isStrongBundleMap_trans Ψ Ψ')
  exact this

/-- **`ū : K → M(Ψ̄, Ψ̄)`**, `k ↦ (1_{p k}, k)`, in the pull-back form. -/
def transUnit (Ψ : Q.Unif) (k : Ψ.1.K) : Q.TransSpace Ψ Ψ :=
  ⟨(S.toTr (GroupoidStr.TransitionSet.unit (Ψ.1.p k)), k), rfl⟩

/-- `T ∘ ū = 1`. -/
theorem transT_transUnit (Ψ : Q.Unif) (k : Ψ.1.K) : Q.transT Ψ Ψ (Q.transUnit Ψ k) = k :=
  transAct_unit k

/-- **`ū` is an sc-smooth strong bundle map covering `u`** (p. 827). -/
theorem isStrongBundleMap_unit (Ψ : Q.Unif) :
    Ψ.1.B.IsStrongBundleMap (Q.transBundle Ψ Ψ)
      (fun q => S.toTr (GroupoidStr.TransitionSet.unit q)) (Q.transUnit Ψ) :=
  Ψ.1.B.isStrongBundleMap_pullbackPair (Q.isScSmoothMap_trSrc Ψ Ψ)
    (S.isScSmoothMap_trUnit (Q.baseUnif Ψ)) (StrongBundle.IsStrongBundleMap.id Ψ.1.B)

end StrongPolyfoldBundleConstruction

end VectorBundle

end GCT

end Polyfold
