import Polyfold.Chapter19.Metrizability
import Polyfold.Chapter8.EpStrongBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.6 "A Strong Bundle Version" (pp. 890–894): the functor `μ : S → Ban` and the category
`E = E_μ` with `P : E → S` (pp. 890–891), **Definition 19.6.1** (strong bundle uniformizer),
**Definition 19.6.3** (strong bundle uniformizer construction), the transition sets
`M(Ψ̄, Ψ̄')`, the map `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` and the structure maps over those of
`M(Ψ, Ψ')` (pp. 892–894).  Numbers and pages are the 2021 text's.

# Strong bundle uniformizers

## The text, paraphrased

(pp. 890–891) `S` and `E` are groupoidal categories, `P : E → S`, the fibres `P⁻¹(α)` are Banach
(perhaps Banachable) spaces and every `φ : α → α'` has a topological linear lift
`φ̂ : P⁻¹(α) → P⁻¹(α')` with `1̂_α = Id` and `(φ' ∘ φ)^ = φ̂' ∘ φ̂`; a morphism of `E` is a pair
`(φ, e)` with `s(φ) = P(e)`, `s(φ, e) = e`, `t(φ, e) = φ̂(e)`.  This is the same as a functor
`μ : S → Ban` (`μ(α) = P⁻¹(α)`, `μ(φ) = φ̂`), from which `E_μ` is rebuilt: objects `(α, e)`,
`e ∈ μ(α)`, morphisms `(φ, e) : e → μ(φ)(e)`.
(Definition 19.6.1) A strong bundle uniformizer at `α` is a functor `Ψ̄ : G ⋉ K → E` with
(1) `p : K → O` a strong bundle over an M-polyfold, `G` acting by strong bundle isomorphisms,
`Ψ̄` a topological linear isomorphism between fibres, and a uniformizer `Ψ : G ⋉ O → S` at `α`
with `P ∘ Ψ̄ = Ψ ∘ (Id ⋉ p)` ("`Ψ` is completely determined by `Ψ̄`"); (2) `Ψ̄` injective on
objects and fully faithful; (3) a `0_ō ∈ K_ō` with `Ψ(ō) = α`, `Ψ̄(0_ō) = (α, 0_{μ(α)})`.
(Definition 19.6.3) A strong bundle uniformizer construction `F̄ : S⁻ → SET` gives a set `F̄(α)`
of strong bundle uniformizers at `α`; it has an underlying uniformizer construction `F`.
(pp. 892–894) `M(Ψ̄, Ψ̄')` consists of the `(a, φ, a')` with `Ψ̄(a) = (s(φ), e)`,
`Ψ̄'(a') = (t(φ), φ̂(e))`; `p(a, φ, a') = (p(a), φ, p'(a'))`; the elements over
`(o, φ, o')` are the `(a, φ, Ψ̄'⁻¹ ∘ φ̂ ∘ Ψ̄(a))`, `a ∈ p⁻¹(o)`; `s`, `t`, `u`, `ι`, `m` cover
those of `M(Ψ, Ψ')`.

## What is formalized (namespace `Polyfold.GroupoidalCategory`)

* `BanFunctor C` (**`μ : S → Ban`**, pp. 890–891), presented by the text's own data: the total
  space `E` with `P : E → S`, the fibres `P⁻¹(α)` (Banachable topological vector spaces) and the
  lifts `lift φ = φ̂ : P⁻¹(s φ) →L P⁻¹(t φ)`, with `lift_unit` (1) and `lift_comp` (2).
  `BanFunctor.act` (`(φ, e) ↦ φ̂(e)`), `liftEquiv` (`φ̂` is a topological linear isomorphism).
* `BanFunctor.cat` (**the groupoidal category `E_μ`**): objects `E`, morphisms the pairs
  `(φ, e)` with `s(φ) = P(e)`; `BanFunctor.proj` (**the functor `P : E → S`**), `orbitProj`
  (`|P|`), the zero objects `zero α = (α, 0)` and `zeroOrbit : |S| → |E|` (`|P| ∘ zeroOrbit = id`).
* `StrongBundleStr μ Ψ̄` (**Definition 19.6.1 (1)**, the structure of a strong bundle
  uniformizer on a functor `Ψ̄ : G ⋉ K → E`, i.e. on a uniformizer of `E_μ`): the M-polyfold
  `O` with the `G`-action, the uniformizer `Ψ = toBase : G ⋉ O → S` (injective, fully faithful),
  the strong bundle `p : K → O` with `K[0]` the M-polyfold of `K`, `G` acting by strong bundle
  maps covering the action on `O`, the commutative diagram (`P_obj`, `mor_fst`), and the fibre
  isomorphisms `fiberCLE o : K_o ≅ μ(Ψ(o))`.  `toBase_obj_eq`, `toBase_mor_eq` ("`Ψ` is
  completely determined by `Ψ̄`").
* `StrongBundleUniformizer μ α` (**Definition 19.6.1**); `definition_19_6_1_two` ((2): `Ψ̄`
  injective on objects and fully faithful), `definition_19_6_1_three` ((3), a consequence of
  "`Ψ` at `α`" and the fibre linearity).
* `StrongBundleUniformizerConstruction μ` (**Definition 19.6.3**), `Unif`, `strU`, the
  underlying uniformizer construction `base` (`F`), `baseUnif`, and `toE`, the uniformizer
  construction of `E_μ` formed by the functors `Ψ̄` (with `toEUnif`, `ofE`).
* The transition sets: `M(Ψ̄, Ψ̄')` is `Ψ̄.Trans Ψ̄'` (the transition set of the functors into
  `E_μ`); `StrongBundleStr.proj` (**`p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`**),
  `StrongBundleStr.lift k a` (**`(a, φ, Ψ̄'⁻¹ ∘ φ̂ ∘ Ψ̄(a))`** over `k = (o, φ, o')`, `p(a) = o`),
  `proj_lift`, `lift_proj`, `eq_of_proj` (an element is determined by `s` and `p`), and the
  compatibility of `p` with `s`, `t`, `u`, `ι`, `m` and `Ψ̂` (`proj_unit`, `proj_inv`,
  `proj_comp`, `proj_hat`, `src_proj`, `tgt_proj`).

## Readings

* `μ : S → Ban`: Banachable topological vector spaces (the text's footnote; this includes Banach
  spaces and is Part I's convention for the fibres of strong bundles).  The functor is given by
  the total space of the text's first description (p. 890), which the text identifies with
  `E_μ` ("there is no difference", p. 891): `E_μ` has the elements of `E` as objects.
* A strong bundle uniformizer "is a functor `Ψ̄ : G ⋉ K → E`" with the properties (1)–(3).  We
  formalize the functor as a uniformizer of the groupoidal category `E_μ` (translation groupoid
  of the M-polyfold `K = K[0]`, injective on objects, fully faithful: this is (2)) and the
  properties (1) as the structure `StrongBundleStr`.  A strong bundle uniformizer construction
  is a set `F̄(α)` of such functors together with their structures (1) (`str`), so that the
  structure (1) is a function of the functor; distinct members of `F̄` are distinct functors.
* (3) is not an extra condition: "`Ψ` a uniformizer at `α`" gives `ō` with `Ψ(ō) = α`, and the
  zero of `K_ō` is mapped to `(α, 0)` by linearity (`definition_19_6_1_three`).
* "`G` acts by strong bundle isomorphisms": every `g ∗ ·` is a strong bundle map covering
  `g ∗ ·` (its inverse `g⁻¹ ∗ ·` is one as well).
* The elements of `M(Ψ̄, Ψ̄')` are the tuples `(a, (φ, e), a')` of the transition set of the
  functors into `E_μ`; `e = Ψ̄(a)` is determined by `a` (the text writes `(a, φ, a')`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

variable (C : GroupoidalCategory.{u})

/-! ### The functor `μ : S → Ban` and the category `E_μ` -/

/-- **2021 §19.6, pp. 890–891: a functor `μ : S → Ban`** into the category of Banachable
topological vector spaces and topological linear isomorphisms, given by the total space `E` of
the fibres `μ(α) = P⁻¹(α)` and the lifts `μ(φ) = φ̂ : P⁻¹(s φ) → P⁻¹(t φ)`, with
(1) `1̂_α = Id` and (2) `(φ' ∘ φ)^ = φ̂' ∘ φ̂`. -/
structure BanFunctor : Type (u + 1) where
  /-- The total space `E` of the fibres `μ(α) = P⁻¹(α)`. -/
  E : Type u
  /-- The projection `P : E → S` on objects. -/
  P : E → C.Obj
  [addFib : ∀ α, AddCommGroup (P ⁻¹' {α})]
  [modFib : ∀ α, Module ℝ (P ⁻¹' {α})]
  [topFib : ∀ α, TopologicalSpace (P ⁻¹' {α})]
  /-- The fibres are Banachable. -/
  banachable : ∀ α, IsBanachable (P ⁻¹' {α})
  /-- The lift `φ̂ = μ(φ) : P⁻¹(s φ) → P⁻¹(t φ)`, a bounded linear operator. -/
  lift : ∀ φ : C.Mor, P ⁻¹' {C.toGroupoidStr.src φ} →L[ℝ] P ⁻¹' {C.toGroupoidStr.tgt φ}
  /-- (1) `1̂_α = Id`. -/
  lift_unit : ∀ (e : E) (h : P e = C.toGroupoidStr.src (C.toGroupoidStr.unit (P e))),
    (lift (C.toGroupoidStr.unit (P e)) ⟨e, h⟩ : E) = e
  /-- (2) `(φ' ∘ φ)^ = φ̂' ∘ φ̂` for `s(φ') = t(φ)`. -/
  lift_comp : ∀ (φ' φ : C.Mor) (hc : C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ) (e : E)
    (h : P e = C.toGroupoidStr.src φ),
    (lift (C.toGroupoidStr.comp φ' φ)
        ⟨e, h.trans (C.toGroupoidStr.src_comp φ' φ hc).symm⟩ : E) =
      lift φ' ⟨lift φ ⟨e, h⟩,
        (show P (lift φ ⟨e, h⟩ : E) = C.toGroupoidStr.tgt φ from (lift φ ⟨e, h⟩).2).trans hc.symm⟩

namespace BanFunctor

attribute [instance] addFib modFib topFib

variable {C} (μ : C.BanFunctor)

theorem P_lift (φ : C.Mor) (v : μ.P ⁻¹' {C.toGroupoidStr.src φ}) :
    μ.P (μ.lift φ v : μ.E) = C.toGroupoidStr.tgt φ := (μ.lift φ v).2

/-- `(φ, e) ↦ φ̂(e)` for `s(φ) = P(e)`. -/
def act (q : pullbackSpace μ.P C.toGroupoidStr.src) : μ.E :=
  μ.lift (q : C.Mor × μ.E).1 ⟨(q : C.Mor × μ.E).2, q.2⟩

theorem P_act (q : pullbackSpace μ.P C.toGroupoidStr.src) :
    μ.P (μ.act q) = C.toGroupoidStr.tgt (q : C.Mor × μ.E).1 := μ.P_lift _ _

theorem act_congr {q q' : pullbackSpace μ.P C.toGroupoidStr.src}
    (h : (q : C.Mor × μ.E) = q') : μ.act q = μ.act q' := congrArg μ.act (Subtype.ext h)

/-- The pair `(1_{P(e)}, e)`. -/
def unitPair (e : μ.E) : pullbackSpace μ.P C.toGroupoidStr.src :=
  ⟨(C.toGroupoidStr.unit (μ.P e), e), (C.toGroupoidStr.src_unit (μ.P e)).symm⟩

theorem act_unitPair (e : μ.E) : μ.act (μ.unitPair e) = e := μ.lift_unit e _

theorem act_comp (ψ γ : C.Mor) (e : μ.E) (h₁ : μ.P e = C.toGroupoidStr.src γ)
    (h₂ : C.toGroupoidStr.src ψ = C.toGroupoidStr.tgt γ) :
    μ.act ⟨(C.toGroupoidStr.comp ψ γ, e), h₁.trans (C.toGroupoidStr.src_comp ψ γ h₂).symm⟩ =
      μ.act ⟨(ψ, μ.act ⟨(γ, e), h₁⟩), (μ.P_act _).trans h₂.symm⟩ :=
  μ.lift_comp ψ γ h₂ e h₁

theorem act_inv_act (q : pullbackSpace μ.P C.toGroupoidStr.src)
    (h : μ.P (μ.act q) = C.toGroupoidStr.src (C.toGroupoidStr.inv (q : C.Mor × μ.E).1)) :
    μ.act ⟨(C.toGroupoidStr.inv (q : C.Mor × μ.E).1, μ.act q), h⟩ = (q : C.Mor × μ.E).2 := by
  obtain ⟨⟨ψ, w⟩, hq⟩ := q
  have hq' : μ.P w = C.toGroupoidStr.src ψ := hq
  rw [← μ.act_comp (C.toGroupoidStr.inv ψ) ψ w hq' (C.toGroupoidStr.src_inv ψ)]
  refine (μ.act_congr ?_).trans (μ.act_unitPair w)
  change (C.toGroupoidStr.comp (C.toGroupoidStr.inv ψ) ψ, w) = (C.toGroupoidStr.unit (μ.P w), w)
  rw [C.toGroupoidStr.inv_comp, hq']

/-- The identification `μ(α) = μ(β)` for `α = β`. -/
def fiberCast {α β : C.Obj} (h : α = β) : μ.P ⁻¹' {α} ≃L[ℝ] μ.P ⁻¹' {β} := by
  subst h; exact ContinuousLinearEquiv.refl ℝ _

@[simp] theorem fiberCast_apply {α β : C.Obj} (h : α = β) (v : μ.P ⁻¹' {α}) :
    (μ.fiberCast h v : μ.E) = v := by
  subst h; rfl

theorem fiberCast_eq {α β : C.Obj} (h : α = β) (v : μ.P ⁻¹' {α}) :
    μ.fiberCast h v = ⟨v, (show μ.P v = α from v.2).trans h⟩ :=
  Subtype.ext (μ.fiberCast_apply h v)

/-- `(φ⁻¹)^`, as a map `μ(t φ) → μ(s φ)`. -/
def liftInv (φ : C.Mor) : μ.P ⁻¹' {C.toGroupoidStr.tgt φ} →L[ℝ] μ.P ⁻¹' {C.toGroupoidStr.src φ} :=
  ((μ.fiberCast (C.toGroupoidStr.tgt_inv φ) : _ →L[ℝ] _).comp (μ.lift (C.toGroupoidStr.inv φ))).comp
    (μ.fiberCast (C.toGroupoidStr.src_inv φ).symm : _ →L[ℝ] _)

theorem liftInv_apply (φ : C.Mor) (v : μ.P ⁻¹' {C.toGroupoidStr.tgt φ}) :
    (μ.liftInv φ v : μ.E) = μ.act ⟨(C.toGroupoidStr.inv φ, v),
      (show μ.P v = _ from v.2).trans (C.toGroupoidStr.src_inv φ).symm⟩ := by
  simp only [liftInv, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, fiberCast_eq]
  rfl

/-- **`φ̂` is a topological linear isomorphism** `μ(s φ) ≅ μ(t φ)`, with inverse `(φ⁻¹)^`
(by (1), (2)). -/
def liftEquiv (φ : C.Mor) :
    μ.P ⁻¹' {C.toGroupoidStr.src φ} ≃L[ℝ] μ.P ⁻¹' {C.toGroupoidStr.tgt φ} :=
  ContinuousLinearEquiv.equivOfInverse (μ.lift φ) (μ.liftInv φ)
    (fun v => Subtype.ext ((μ.liftInv_apply φ _).trans (μ.act_inv_act ⟨(φ, v), v.2⟩ _)))
    (fun v => by
      apply Subtype.ext
      have hv : μ.P (v : μ.E) = C.toGroupoidStr.src (C.toGroupoidStr.inv φ) :=
        (show μ.P v = _ from v.2).trans (C.toGroupoidStr.src_inv φ).symm
      let q : pullbackSpace μ.P C.toGroupoidStr.src := ⟨(C.toGroupoidStr.inv φ, v), hv⟩
      have h2 : μ.P (μ.act q) =
          C.toGroupoidStr.src (C.toGroupoidStr.inv (q : C.Mor × μ.E).1) :=
        (μ.P_act q).trans (C.toGroupoidStr.src_inv _).symm
      have h3 := μ.act_inv_act q h2
      have h4 : μ.liftInv φ v = ⟨μ.act q, (μ.P_act q).trans (C.toGroupoidStr.tgt_inv φ)⟩ :=
        Subtype.ext (μ.liftInv_apply φ v)
      change μ.act ⟨(φ, (μ.liftInv φ v : μ.E)), (μ.liftInv φ v).2⟩ = _
      rw [h4]
      refine (μ.act_congr ?_).trans h3
      exact Prod.ext (C.toGroupoidStr.inv_inv φ).symm rfl)

@[simp] theorem liftEquiv_apply (φ : C.Mor) (v : μ.P ⁻¹' {C.toGroupoidStr.src φ}) :
    μ.liftEquiv φ v = μ.lift φ v := rfl

/-! #### The groupoidal category `E_μ` -/

/-- The inverse `(φ, e)⁻¹ = (φ⁻¹, φ̂(e))`. -/
def morInv (q : pullbackSpace μ.P C.toGroupoidStr.src) : pullbackSpace μ.P C.toGroupoidStr.src :=
  ⟨(C.toGroupoidStr.inv (q : C.Mor × μ.E).1, μ.act q),
    (μ.P_act q).trans (C.toGroupoidStr.src_inv _).symm⟩

open scoped Classical in
/-- The composite `(φ', φ̂(e)) ∘ (φ, e) = (φ' ∘ φ, e)` (the junk value `(φ, e)` off composable
pairs). -/
def morComp (q' q : pullbackSpace μ.P C.toGroupoidStr.src) :
    pullbackSpace μ.P C.toGroupoidStr.src :=
  if h : μ.P (q : C.Mor × μ.E).2 =
      C.toGroupoidStr.src (C.toGroupoidStr.comp (q' : C.Mor × μ.E).1 (q : C.Mor × μ.E).1) then
    ⟨(C.toGroupoidStr.comp (q' : C.Mor × μ.E).1 (q : C.Mor × μ.E).1, (q : C.Mor × μ.E).2), h⟩
  else q

variable {μ}

theorem src_eq_tgt_of_eq_act {q' q : pullbackSpace μ.P C.toGroupoidStr.src}
    (h : (q' : C.Mor × μ.E).2 = μ.act q) :
    C.toGroupoidStr.src (q' : C.Mor × μ.E).1 = C.toGroupoidStr.tgt (q : C.Mor × μ.E).1 := by
  rw [← (q'.2 : μ.P (q' : C.Mor × μ.E).2 = _), h, μ.P_act]

theorem morComp_val {q' q : pullbackSpace μ.P C.toGroupoidStr.src}
    (h : (q' : C.Mor × μ.E).2 = μ.act q) :
    (μ.morComp q' q : C.Mor × μ.E) =
      (C.toGroupoidStr.comp (q' : C.Mor × μ.E).1 (q : C.Mor × μ.E).1, (q : C.Mor × μ.E).2) := by
  have hc : μ.P (q : C.Mor × μ.E).2 =
      C.toGroupoidStr.src (C.toGroupoidStr.comp (q' : C.Mor × μ.E).1 (q : C.Mor × μ.E).1) :=
    (q.2 : μ.P (q : C.Mor × μ.E).2 = _).trans
      (C.toGroupoidStr.src_comp _ _ (src_eq_tgt_of_eq_act h)).symm
  unfold morComp; rw [dif_pos hc]

theorem act_morComp {q' q : pullbackSpace μ.P C.toGroupoidStr.src}
    (h : (q' : C.Mor × μ.E).2 = μ.act q) : μ.act (μ.morComp q' q) = μ.act q' := by
  obtain ⟨⟨γ, w⟩, hq⟩ := q
  obtain ⟨⟨ψ, w'⟩, hq'⟩ := q'
  have h' : w' = μ.act ⟨(γ, w), hq⟩ := h
  subst h'
  have hq₁ : μ.P w = C.toGroupoidStr.src γ := hq
  calc μ.act (μ.morComp _ _) = μ.act ⟨(C.toGroupoidStr.comp ψ γ, w),
        hq₁.trans (C.toGroupoidStr.src_comp ψ γ (src_eq_tgt_of_eq_act h)).symm⟩ :=
        μ.act_congr (morComp_val h)
    _ = _ := μ.act_comp ψ γ w hq₁ (src_eq_tgt_of_eq_act h)

theorem act_morInv (q : pullbackSpace μ.P C.toGroupoidStr.src) :
    μ.act (μ.morInv q) = (q : C.Mor × μ.E).2 := μ.act_inv_act q _

variable (μ)

/-- The groupoid structure of `E_μ`: `s(φ, e) = e`, `t(φ, e) = φ̂(e)`, `1_e = (1_{P(e)}, e)`. -/
def groupoidStr : GroupoidStr μ.E (pullbackSpace μ.P C.toGroupoidStr.src) where
  src := pullbackProj' μ.P C.toGroupoidStr.src
  tgt := μ.act
  comp := μ.morComp
  unit := μ.unitPair
  inv := μ.morInv
  src_comp φ ψ h := by
    change (μ.morComp φ ψ : C.Mor × μ.E).2 = (ψ : C.Mor × μ.E).2
    rw [morComp_val h]
  tgt_comp φ ψ h := act_morComp h
  comp_assoc φ ψ χ h₁ h₂ := by
    have h₁' : (φ : C.Mor × μ.E).2 = μ.act ψ := h₁
    have h₂' : (ψ : C.Mor × μ.E).2 = μ.act χ := h₂
    have h₃ : (μ.morComp φ ψ : C.Mor × μ.E).2 = μ.act χ := by rw [morComp_val h₁']; exact h₂'
    have h₄ : (φ : C.Mor × μ.E).2 = μ.act (μ.morComp ψ χ) := by
      rw [act_morComp h₂']; exact h₁'
    apply Subtype.ext
    rw [morComp_val h₃, morComp_val h₁', morComp_val h₄, morComp_val h₂',
      C.toGroupoidStr.comp_assoc _ _ _ (src_eq_tgt_of_eq_act h₁') (src_eq_tgt_of_eq_act h₂')]
  src_unit _ := rfl
  tgt_unit w := μ.act_unitPair w
  comp_unit φ := by
    have h0 : (φ : C.Mor × μ.E).2 = μ.act (μ.unitPair (pullbackProj' μ.P _ φ)) :=
      (μ.act_unitPair _).symm
    apply Subtype.ext
    rw [morComp_val h0]
    change (C.toGroupoidStr.comp (φ : C.Mor × μ.E).1
      (C.toGroupoidStr.unit (μ.P (φ : C.Mor × μ.E).2)), (φ : C.Mor × μ.E).2) = φ
    rw [C.toGroupoidStr.comp_unit_of_eq (φ.2 : μ.P (φ : C.Mor × μ.E).2 = _).symm]
  unit_comp φ := by
    apply Subtype.ext
    rw [morComp_val (q' := μ.unitPair (μ.act φ)) (q := φ) rfl]
    change (C.toGroupoidStr.comp (C.toGroupoidStr.unit (μ.P (μ.act φ))) (φ : C.Mor × μ.E).1,
      (φ : C.Mor × μ.E).2) = φ
    rw [C.toGroupoidStr.unit_comp_of_eq (μ.P_act φ).symm]
  src_inv _ := rfl
  tgt_inv φ := act_morInv φ
  comp_inv φ := by
    apply Subtype.ext
    rw [morComp_val (act_morInv φ).symm]
    change (C.toGroupoidStr.comp (φ : C.Mor × μ.E).1 (C.toGroupoidStr.inv (φ : C.Mor × μ.E).1),
      μ.act φ) = (C.toGroupoidStr.unit (μ.P (μ.act φ)), μ.act φ)
    rw [C.toGroupoidStr.comp_inv, μ.P_act]
  inv_comp φ := by
    apply Subtype.ext
    rw [morComp_val (q' := μ.morInv φ) (q := φ) rfl]
    · change (C.toGroupoidStr.comp (C.toGroupoidStr.inv (φ : C.Mor × μ.E).1) (φ : C.Mor × μ.E).1,
        (φ : C.Mor × μ.E).2) = (C.toGroupoidStr.unit (μ.P (φ : C.Mor × μ.E).2),
          (φ : C.Mor × μ.E).2)
      rw [C.toGroupoidStr.inv_comp, (φ.2 : μ.P (φ : C.Mor × μ.E).2 = _)]

/-- **2021 §19.6, p. 891: the groupoidal category `E_μ`**: objects the elements `e` of the
fibres `μ(α)` (the pairs `(α, e)`, `α = P(e)`), morphisms the pairs `(φ, e)` with `s(φ) = P(e)`,
`(φ, e) : e → φ̂(e)`.  Between two objects there are finitely many morphisms. -/
abbrev cat : GroupoidalCategory.{u} where
  Obj := μ.E
  Mor := pullbackSpace μ.P C.toGroupoidStr.src
  toGroupoidStr := μ.groupoidStr
  finite_mor e e' := by
    refine Set.Finite.of_finite_image (f := fun q : pullbackSpace μ.P C.toGroupoidStr.src =>
      (q : C.Mor × μ.E).1) ((C.finite_mor (μ.P e) (μ.P e')).subset ?_) ?_
    · rintro _ ⟨q, ⟨hs, ht⟩, rfl⟩
      have hs' : (q : C.Mor × μ.E).2 = e := hs
      have ht' : μ.act q = e' := ht
      refine ⟨?_, ?_⟩
      · change C.toGroupoidStr.src (q : C.Mor × μ.E).1 = μ.P e
        rw [← hs']; exact (q.2 : μ.P _ = _).symm
      · change C.toGroupoidStr.tgt (q : C.Mor × μ.E).1 = μ.P e'
        rw [← ht', μ.P_act]
    · intro q hq q' hq' h
      have hs : (q : C.Mor × μ.E).2 = e := hq.1
      have hs' : (q' : C.Mor × μ.E).2 = e := hq'.1
      exact Subtype.ext (Prod.ext h (hs.trans hs'.symm))

@[simp] theorem cat_src (q : μ.cat.Mor) :
    μ.cat.toGroupoidStr.src q = (q : C.Mor × μ.E).2 := rfl
@[simp] theorem cat_tgt (q : μ.cat.Mor) : μ.cat.toGroupoidStr.tgt q = μ.act q := rfl
@[simp] theorem cat_unit (e : μ.cat.Obj) : μ.cat.toGroupoidStr.unit e = μ.unitPair e := rfl
@[simp] theorem cat_inv (q : μ.cat.Mor) : μ.cat.toGroupoidStr.inv q = μ.morInv q := rfl
@[simp] theorem cat_comp (q' q : μ.cat.Mor) : μ.cat.toGroupoidStr.comp q' q = μ.morComp q' q :=
  rfl

theorem cat_comp_fst {q' q : μ.cat.Mor}
    (h : μ.cat.toGroupoidStr.src q' = μ.cat.toGroupoidStr.tgt q) :
    ((μ.cat.toGroupoidStr.comp q' q : μ.cat.Mor) : C.Mor × μ.E).1 =
      C.toGroupoidStr.comp (q' : C.Mor × μ.E).1 (q : C.Mor × μ.E).1 :=
  congrArg Prod.fst (morComp_val h)

/-- **The functor `P : E → S`**: `e ↦ P(e)`, `(φ, e) ↦ φ`. -/
def proj : GroupoidFunctor μ.cat.toGroupoidStr C.toGroupoidStr where
  obj := μ.P
  mor q := (q : C.Mor × μ.E).1
  src_mor q := (q.2 : μ.P (q : C.Mor × μ.E).2 = _).symm
  tgt_mor q := (μ.P_act q).symm
  mor_comp _ _ h := μ.cat_comp_fst h
  mor_unit _ := rfl

/-- `|P| : |E| → |S|`. -/
abbrev orbitProj : μ.cat.OrbitSpace → C.OrbitSpace := μ.proj.orbitMap

theorem orbitProj_π (e : μ.E) : μ.orbitProj (μ.cat.π e) = C.π (μ.P e) := rfl

/-- `e ≅ φ̂(e)` in `E_μ`. -/
theorem π_act (q : pullbackSpace μ.P C.toGroupoidStr.src) :
    μ.cat.π (μ.act q) = μ.cat.π (q : C.Mor × μ.E).2 :=
  ((μ.cat.π_eq_π_iff).2 ⟨q, rfl, rfl⟩).symm

/-- **Moving an object into a fibre**: if `|P(e)| = |α|` there is `e'` in the fibre over `α`
with `|e'| = |e|`. -/
theorem exists_mem_fiber_of_π_eq {e : μ.E} {α : C.Obj} (h : C.π (μ.P e) = C.π α) :
    ∃ e' : μ.E, μ.P e' = α ∧ μ.cat.π e' = μ.cat.π e := by
  obtain ⟨φ, hs, ht⟩ := (C.π_eq_π_iff).1 h
  exact ⟨μ.act ⟨(φ, e), hs.symm⟩, (μ.P_act _).trans ht, μ.π_act _⟩

/-! #### The zero section -/

/-- The zero `(α, 0_{μ(α)})` of the fibre over `α`. -/
def zero (α : C.Obj) : μ.E := ((0 : μ.P ⁻¹' {α}) : μ.E)

theorem P_zero (α : C.Obj) : μ.P (μ.zero α) = α := (0 : μ.P ⁻¹' {α}).2

theorem act_zero (φ : C.Mor) :
    μ.act ⟨(φ, μ.zero (C.toGroupoidStr.src φ)), μ.P_zero _⟩ = μ.zero (C.toGroupoidStr.tgt φ) :=
  congrArg Subtype.val (map_zero (μ.lift φ))

theorem π_zero_eq {α β : C.Obj} (h : C.π α = C.π β) : μ.cat.π (μ.zero α) = μ.cat.π (μ.zero β) := by
  obtain ⟨φ, rfl, rfl⟩ := (C.π_eq_π_iff).1 h
  rw [← μ.act_zero φ, μ.π_act]

/-- **The zero section `|S| → |E|`**, `|α| ↦ |(α, 0)|`. -/
def zeroOrbit : C.OrbitSpace → μ.cat.OrbitSpace :=
  Quotient.lift (fun α => μ.cat.π (μ.zero α)) fun _ _ h => μ.π_zero_eq (Quotient.sound h)

@[simp] theorem zeroOrbit_π (α : C.Obj) : μ.zeroOrbit (C.π α) = μ.cat.π (μ.zero α) := rfl

/-- `|P| ∘ |0| = Id`. -/
theorem orbitProj_zeroOrbit (z : C.OrbitSpace) : μ.orbitProj (μ.zeroOrbit z) = z := by
  induction z using Quotient.inductionOn with
  | h α => exact congrArg C.π (μ.P_zero α)

end BanFunctor

/-! ### Definition 19.6.1: strong bundle uniformizers -/

variable {C}

/-- **2021 Definition 19.6.1 (1), p. 891**: the structure of a **strong bundle uniformizer** on a
functor `Ψ̄ : G ⋉ K → E_μ` (a uniformizer of `E_μ`, i.e. injective on objects and fully faithful,
(2)): an M-polyfold `O` with an action of `G` by sc-smooth maps, a uniformizer `Ψ : G ⋉ O → S`
(injective on objects, fully faithful), a strong bundle `p : K → O` whose M-polyfold `K[0]` is
the M-polyfold `K` of `Ψ̄`, on which `G` acts by strong bundle maps covering its action on `O`,
such that `P ∘ Ψ̄ = Ψ ∘ (Id ⋉ p)` and `Ψ̄ : K_o → μ(Ψ(o))` is a topological linear isomorphism. -/
structure StrongBundleStr (μ : C.BanFunctor) (Ψe : μ.cat.Uniformizer) : Type (u + 1) where
  /-- The base M-polyfold `O`. -/
  O : Type u
  [topO : TopologicalSpace O]
  [t2O : T2Space O]
  [paraO : ParacompactSpace O]
  /-- The M-polyfold structure of `O`. -/
  PO : MPolyfold O
  [actO : MulAction Ψe.G O]
  smooth_smul : ∀ g : Ψe.G, PO.IsScSmoothMap PO fun y => g • y
  /-- The underlying uniformizer `Ψ : G ⋉ O → S`. -/
  functor : GroupoidFunctor (GroupoidStr.translation Ψe.G O) C.toGroupoidStr
  injective_obj : Injective functor.obj
  full : functor.toFunctor.Full
  faithful : functor.toFunctor.Faithful
  /-- The strong bundle projection `p : K → O`. -/
  p : Ψe.O → O
  [addK : ∀ o, AddCommGroup (p ⁻¹' {o})]
  [modK : ∀ o, Module ℝ (p ⁻¹' {o})]
  /-- The strong bundle structure of `p : K → O`. -/
  B : StrongBundle PO p
  /-- `K[0]` is the M-polyfold `K` of `Ψ̄`. -/
  toMPolyfold0_eq : B.toMPolyfold0 = Ψe.P
  p_smul : ∀ (g : Ψe.G) (a : Ψe.O), p (g • a) = g • p a
  /-- `G` acts by strong bundle maps covering its action on `O`. -/
  isStrongBundleMap_smul : ∀ g : Ψe.G, B.IsStrongBundleMap B (fun y => g • y) (fun a => g • a)
  /-- `P ∘ Ψ̄ = Ψ ∘ p` on objects. -/
  P_obj : ∀ a, μ.P (Ψe.obj a) = functor.obj (p a)
  /-- `P ∘ Ψ̄ = Ψ ∘ (Id ⋉ p)` on morphisms. -/
  mor_fst : ∀ (g : Ψe.G) (a : Ψe.O), ((Ψe.mor (g, a) : μ.cat.Mor) : C.Mor × μ.E).1 =
    functor.mor (g, p a)
  /-- The fibre isomorphisms `Ψ̄ : K_o → μ(Ψ(o))`. -/
  fiberCLE : ∀ o, p ⁻¹' {o} ≃L[ℝ] μ.P ⁻¹' {functor.obj o}
  fiberCLE_apply : ∀ o (v : p ⁻¹' {o}), (fiberCLE o v : μ.E) = Ψe.obj v

namespace StrongBundleStr

attribute [instance] topO t2O paraO actO addK modK

variable {μ : C.BanFunctor} {Ψe : μ.cat.Uniformizer} (S : StrongBundleStr μ Ψe)

/-- **The underlying uniformizer** `Ψ : G ⋉ O → S` (Definition 19.6.1 (1)). -/
abbrev toBase : C.Uniformizer where
  O := S.O
  P := S.PO
  G := Ψe.G
  smooth_smul := S.smooth_smul
  functor := S.functor
  injective_obj := S.injective_obj
  full := S.full
  faithful := S.faithful

@[simp] theorem toBase_obj (o : S.O) : S.toBase.obj o = S.functor.obj o := rfl

theorem continuous_p : Continuous S.p := S.B.continuous

theorem obj_eq_fiberCLE (a : Ψe.O) : Ψe.obj a = (S.fiberCLE (S.p a) ⟨a, rfl⟩ : μ.E) :=
  (S.fiberCLE_apply (S.p a) ⟨a, rfl⟩).symm

/-- `Ψ̄(a)` lies in the fibre over `Ψ(p(a))`. -/
theorem P_obj' (a : Ψe.O) : μ.P (Ψe.obj a) = S.toBase.obj (S.p a) := S.P_obj a

/-- `Ψ̄(g, a) = (Ψ(g, p(a)), Ψ̄(a))`. -/
theorem mor_eq (g : Ψe.G) (a : Ψe.O) :
    ((Ψe.mor (g, a) : μ.cat.Mor) : C.Mor × μ.E) = (S.toBase.mor (g, S.p a), Ψe.obj a) :=
  Prod.ext (S.mor_fst g a) (Ψe.src_mor (g, a))

/-- **The functoriality of `Ψ̄`**: `Ψ̄(g ∗ a) = Ψ(g, p(a))^(Ψ̄(a))`. -/
theorem obj_smul (g : Ψe.G) (a : Ψe.O) :
    Ψe.obj (g • a) = μ.act ⟨(S.toBase.mor (g, S.p a), Ψe.obj a),
      (S.P_obj a).trans (S.toBase.src_mor (g, S.p a)).symm⟩ :=
  (Ψe.tgt_mor (g, a)).symm.trans (μ.act_congr (S.mor_eq g a))

/-- **"`Ψ` is completely determined by `Ψ̄`"** (Definition 19.6.1 (1)), on objects:
`Ψ(o) = P(Ψ̄(0_o))`. -/
theorem toBase_obj_eq (o : S.O) : S.toBase.obj o = μ.P (Ψe.obj (fiberZero S.p o)) := by
  rw [S.P_obj']; exact congrArg _ (isSection_fiberZero (P := S.p) o).symm

/-- **"`Ψ` is completely determined by `Ψ̄`"**, on morphisms: `Ψ(g, o)` is the morphism of `S`
underlying `Ψ̄(g, 0_o)`. -/
theorem toBase_mor_eq (g : Ψe.G) (o : S.O) :
    S.toBase.mor (g, o) = ((Ψe.mor (g, fiberZero S.p o) : μ.cat.Mor) : C.Mor × μ.E).1 := by
  rw [S.mor_fst]; exact congrArg (fun x => S.functor.mor (g, x)) (isSection_fiberZero o).symm

/-- `Ψ̄(0_o) = (Ψ(o), 0)`. -/
theorem obj_fiberZero (o : S.O) : Ψe.obj (fiberZero S.p o) = μ.zero (S.toBase.obj o) := by
  change Ψe.obj ((0 : S.p ⁻¹' {o}) : Ψe.O) = _
  rw [← S.fiberCLE_apply o 0, map_zero]; rfl

end StrongBundleStr

/-- **2021 Definition 19.6.1, p. 891**: a **strong bundle uniformizer at `α`**: a functor
`Ψ̄ : G ⋉ K → E_μ`, injective on objects and fully faithful ((2), a uniformizer of `E_μ`), with
the structure (1) of `StrongBundleStr`, whose underlying uniformizer `Ψ` is at `α`. -/
structure StrongBundleUniformizer (μ : C.BanFunctor) (α : C.Obj) : Type (u + 1) where
  /-- The functor `Ψ̄ : G ⋉ K → E`. -/
  toUniformizer : μ.cat.Uniformizer
  /-- The structure (1). -/
  str : StrongBundleStr μ toUniformizer
  /-- `Ψ` is a uniformizer at `α`. -/
  isAt : str.toBase.IsAt α

namespace StrongBundleUniformizer

variable {μ : C.BanFunctor} {α : C.Obj} (Ψ : StrongBundleUniformizer μ α)

/-- **2021 Definition 19.6.1 (2), p. 892**: `Ψ̄` is injective on objects and fully faithful
(these are the fields of a uniformizer of `E_μ`), and so is `Ψ`. -/
theorem definition_19_6_1_two :
    Injective Ψ.toUniformizer.obj ∧ Ψ.toUniformizer.functor.toFunctor.Full ∧
      Ψ.toUniformizer.functor.toFunctor.Faithful ∧ Injective Ψ.str.toBase.obj ∧
        Ψ.str.toBase.functor.toFunctor.Full ∧ Ψ.str.toBase.functor.toFunctor.Faithful :=
  ⟨Ψ.toUniformizer.injective_obj, Ψ.toUniformizer.full, Ψ.toUniformizer.faithful,
    Ψ.str.injective_obj, Ψ.str.full, Ψ.str.faithful⟩

/-- **2021 Definition 19.6.1 (3), p. 892**: there is `0_ō ∈ K_ō` with `Ψ(ō) = α` and
`Ψ̄(0_ō) = (α, 0_{μ(α)})` (from "`Ψ` at `α`" and the linearity of `Ψ̄` on the fibres). -/
theorem definition_19_6_1_three :
    ∃ o : Ψ.str.O, Ψ.str.toBase.obj o = α ∧
      Ψ.toUniformizer.obj (fiberZero Ψ.str.p o) = μ.zero α := by
  obtain ⟨o, ho⟩ := Ψ.isAt
  exact ⟨o, ho, (Ψ.str.obj_fiberZero o).trans (congrArg μ.zero ho)⟩

end StrongBundleUniformizer

/-! ### Definition 19.6.3: strong bundle uniformizer constructions -/

/-- **2021 Definition 19.6.3, p. 892**: a **strong bundle uniformizer construction**
`F̄ : S⁻ → SET`: for every object `α` a set `F̄(α)` of strong bundle uniformizers at `α`, i.e. of
functors `Ψ̄ : G ⋉ K → E_μ` with their structures (1) (`str`, a function of the functor). -/
structure StrongBundleUniformizerConstruction (μ : C.BanFunctor) : Type (u + 1) where
  /-- The sets `F̄(α)` of functors `Ψ̄`. -/
  F : C.Obj → Set μ.cat.Uniformizer
  /-- The structure (1) of a member of `F̄`. -/
  str : ∀ Ψe : μ.cat.Uniformizer, (∃ α, Ψe ∈ F α) → StrongBundleStr μ Ψe
  /-- The members of `F̄(α)` are at `α`. -/
  isAt : ∀ α Ψe (h : Ψe ∈ F α), (str Ψe ⟨α, h⟩).toBase.IsAt α

namespace StrongBundleUniformizerConstruction

variable {μ : C.BanFunctor} (Fb : StrongBundleUniformizerConstruction μ)

/-- The strong bundle uniformizers occurring in `F̄`. -/
abbrev Unif : Type (u + 1) := {Ψe : μ.cat.Uniformizer // ∃ α, Ψe ∈ Fb.F α}

/-- The structure (1) of a member of `F̄`. -/
abbrev strU (Ψ : Fb.Unif) : StrongBundleStr μ Ψ.1 := Fb.str Ψ.1 Ψ.2

/-- A member of `F̄(α)` as a strong bundle uniformizer at `α` (Definition 19.6.1). -/
def toStrongBundleUniformizer {α : C.Obj} {Ψe : μ.cat.Uniformizer} (h : Ψe ∈ Fb.F α) :
    StrongBundleUniformizer μ α :=
  ⟨Ψe, Fb.str Ψe ⟨α, h⟩, Fb.isAt α Ψe h⟩

/-- **The underlying uniformizer construction `F`** (p. 892): `F(α) = {Ψ | Ψ̄ ∈ F̄(α)}`. -/
def base : C.UniformizerConstruction where
  F α := {Ψ | ∃ (Ψe : μ.cat.Uniformizer) (h : Ψe ∈ Fb.F α), (Fb.str Ψe ⟨α, h⟩).toBase = Ψ}
  isAt α Ψ := by
    rintro ⟨Ψe, h, rfl⟩
    exact Fb.isAt α Ψe h

/-- The underlying uniformizer `Ψ` of a member `Ψ̄` of `F̄`, as a member of `F`. -/
abbrev baseUnif (Ψ : Fb.Unif) : Fb.base.Unif :=
  ⟨(Fb.strU Ψ).toBase, by obtain ⟨α, h⟩ := Ψ.2; exact ⟨α, Ψ.1, h, rfl⟩⟩

@[simp] theorem baseUnif_val (Ψ : Fb.Unif) : (Fb.baseUnif Ψ).1 = (Fb.strU Ψ).toBase := rfl

/-- **The uniformizer construction of `E_μ` formed by the functors `Ψ̄`**: `Ψ̄` belongs to the
set of an object `e` if `Ψ̄ ∈ F̄(α)` for an `α` isomorphic to `P(e)` and `Ψ̄` is at `e`. -/
def toE : μ.cat.UniformizerConstruction where
  F e := {Ψe | ∃ α, Ψe ∈ Fb.F α ∧ C.π α = C.π (μ.P e) ∧ Ψe.IsAt e}
  isAt _ _ h := h.choose_spec.2.2

/-- A member of `toE` as a member of `F̄`. -/
abbrev ofE (Ψ : Fb.toE.Unif) : Fb.Unif :=
  ⟨Ψ.1, by obtain ⟨_, α, h, -⟩ := Ψ.2; exact ⟨α, h⟩⟩

@[simp] theorem ofE_val (Ψ : Fb.toE.Unif) : (Fb.ofE Ψ).1 = Ψ.1 := rfl

/-- For `Ψ̄ ∈ F̄(α)`, `Ψ̄` belongs to the set of the object `Ψ̄(0_ō)` of `toE`, `Ψ(ō) = α`. -/
theorem mem_toE {α : C.Obj} {Ψe : μ.cat.Uniformizer} (h : Ψe ∈ Fb.F α) {o : (Fb.str Ψe ⟨α, h⟩).O}
    (ho : (Fb.str Ψe ⟨α, h⟩).toBase.obj o = α) :
    Ψe ∈ Fb.toE.F (Ψe.obj (fiberZero (Fb.str Ψe ⟨α, h⟩).p o)) := by
  refine ⟨α, h, ?_, _, rfl⟩
  rw [(Fb.str Ψe ⟨α, h⟩).P_obj', isSection_fiberZero (P := (Fb.str Ψe ⟨α, h⟩).p) o, ho]

/-- A member of `F̄` as a member of `toE`. -/
abbrev toEUnif (Ψ : Fb.Unif) : Fb.toE.Unif :=
  ⟨Ψ.1, by
    obtain ⟨α, h⟩ := Ψ.2
    obtain ⟨o, ho⟩ := Fb.isAt α Ψ.1 h
    exact ⟨_, Fb.mem_toE h ho⟩⟩

@[simp] theorem toEUnif_val (Ψ : Fb.Unif) : (Fb.toEUnif Ψ).1 = Ψ.1 := rfl

@[simp] theorem ofE_toEUnif (Ψ : Fb.Unif) : Fb.ofE (Fb.toEUnif Ψ) = Ψ := rfl

@[simp] theorem toEUnif_ofE (Ψ : Fb.toE.Unif) : Fb.toEUnif (Fb.ofE Ψ) = Ψ := rfl

/-- **Every isomorphism class of `E` meets `toE` iff every class of `S` meets `F`.** -/
theorem hasClassUniformizers_toE_iff :
    Fb.toE.HasClassUniformizers ↔ Fb.base.HasClassUniformizers := by
  constructor
  · intro h z
    obtain ⟨e, he, Ψe, α, hα, hαe, -⟩ := h (μ.zeroOrbit z)
    refine ⟨α, ?_, _, Ψe, hα, rfl⟩
    rw [hαe, ← μ.orbitProj_π, he, μ.orbitProj_zeroOrbit]
  · intro h z
    induction z using Quotient.inductionOn with
    | h e =>
      obtain ⟨α, hα, _, ⟨Ψe, hΨe, rfl⟩⟩ := h (C.π (μ.P e))
      obtain ⟨e', he', he'e⟩ := μ.exists_mem_fiber_of_π_eq hα.symm
      obtain ⟨o, ho⟩ := Fb.isAt α Ψe hΨe
      revert o
      generalize Fb.str Ψe ⟨α, hΨe⟩ = S
      intro o ho
      let v : S.p ⁻¹' {o} := (S.fiberCLE o).symm ⟨e', he'.trans ho.symm⟩
      have hv : Ψe.obj v = e' := by
        rw [← S.fiberCLE_apply o v, ContinuousLinearEquiv.apply_symm_apply]
      refine ⟨Ψe.obj v, ?_, Ψe, α, hΨe, ?_, v, rfl⟩
      · rw [hv, he'e]; rfl
      · rw [hv, he']

end StrongBundleUniformizerConstruction

/-! ### The transition sets `M(Ψ̄, Ψ̄')` and `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` -/

namespace StrongBundleStr

open GroupoidStr (TransitionSet)

variable {μ : C.BanFunctor} {Ψe Ψe' Ψe'' : μ.cat.Uniformizer} (S : StrongBundleStr μ Ψe)
  (S' : StrongBundleStr μ Ψe') (S'' : StrongBundleStr μ Ψe'')

/-- `e = Ψ̄(a)` in `h̄ = (a, (φ, e), a') ∈ M(Ψ̄, Ψ̄')`. -/
theorem trans_mor_snd (h : Ψe.Trans Ψe') :
    ((h.mor : μ.cat.Mor) : C.Mor × μ.E).2 = Ψe.obj h.src := h.src_mor

/-- `φ̂(e) = Ψ̄'(a')` in `h̄ = (a, (φ, e), a') ∈ M(Ψ̄, Ψ̄')`. -/
theorem trans_act_mor (h : Ψe.Trans Ψe') : μ.act h.mor = Ψe'.obj h.tgt := h.tgt_mor

/-- **2021 p. 892: the map `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`**, `p(a, φ, a') = (p(a), φ, p'(a'))`. -/
def proj (h : Ψe.Trans Ψe') : S.toBase.Trans S'.toBase where
  src := S.p h.src
  mor := ((h.mor : μ.cat.Mor) : C.Mor × μ.E).1
  tgt := S'.p h.tgt
  src_mor := by
    rw [← (h.mor.2 : μ.P ((h.mor : μ.cat.Mor) : C.Mor × μ.E).2 = _), trans_mor_snd, S.P_obj']
  tgt_mor := by rw [← μ.P_act, trans_act_mor, S'.P_obj']

@[simp] theorem proj_src (h : Ψe.Trans Ψe') : (S.proj S' h).src = S.p h.src := rfl
@[simp] theorem proj_tgt (h : Ψe.Trans Ψe') : (S.proj S' h).tgt = S'.p h.tgt := rfl
@[simp] theorem proj_mor (h : Ψe.Trans Ψe') :
    (S.proj S' h).mor = ((h.mor : μ.cat.Mor) : C.Mor × μ.E).1 := rfl

/-- The point `Ψ̄'⁻¹(φ̂(Ψ̄(a)))` of `K'` over `t(k)`, for `k = (o, φ, o')`, `p(a) = o`. -/
def liftTgt (k : S.toBase.Trans S'.toBase) (a : Ψe.O) (ha : S.p a = k.src) : S'.p ⁻¹' {k.tgt} :=
  (S'.fiberCLE k.tgt).symm ⟨μ.act ⟨(k.mor, Ψe.obj a),
    (S.P_obj' a).trans ((congrArg S.toBase.obj ha).trans k.src_mor.symm)⟩,
    (μ.P_act _).trans k.tgt_mor⟩

/-- **2021 p. 893: the elements of `M(Ψ̄, Ψ̄')` over `k = (o, φ, o')`**: for `a ∈ p⁻¹(o)`,
`(a, φ, Ψ̄'⁻¹ ∘ φ̂ ∘ Ψ̄(a))`.  (This is also the map `H` of (19.16).) -/
def lift (k : S.toBase.Trans S'.toBase) (a : Ψe.O) (ha : S.p a = k.src) : Ψe.Trans Ψe' where
  src := a
  mor := ⟨(k.mor, Ψe.obj a),
    (S.P_obj' a).trans ((congrArg S.toBase.obj ha).trans k.src_mor.symm)⟩
  tgt := (S.liftTgt S' k a ha : Ψe'.O)
  src_mor := rfl
  tgt_mor := by
    change μ.act _ = Ψe'.obj (S.liftTgt S' k a ha : Ψe'.O)
    rw [← S'.fiberCLE_apply k.tgt (S.liftTgt S' k a ha)]
    unfold liftTgt
    rw [ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem lift_src (k : S.toBase.Trans S'.toBase) (a : Ψe.O) (ha : S.p a = k.src) :
    (S.lift S' k a ha).src = a := rfl

theorem p_lift_tgt (k : S.toBase.Trans S'.toBase) (a : Ψe.O) (ha : S.p a = k.src) :
    S'.p (S.lift S' k a ha).tgt = k.tgt := (S.liftTgt S' k a ha).2

@[simp] theorem proj_lift (k : S.toBase.Trans S'.toBase) (a : Ψe.O) (ha : S.p a = k.src) :
    S.proj S' (S.lift S' k a ha) = k :=
  TransitionSet.ext ha rfl (S.p_lift_tgt S' k a ha)

/-- `Ψ̄'(t(lift k a)) = φ̂(Ψ̄(a))`. -/
theorem obj_lift_tgt (k : S.toBase.Trans S'.toBase) (a : Ψe.O) (ha : S.p a = k.src) :
    Ψe'.obj (S.lift S' k a ha).tgt = μ.act ⟨(k.mor, Ψe.obj a),
      (S.P_obj' a).trans ((congrArg S.toBase.obj ha).trans k.src_mor.symm)⟩ :=
  (S.lift S' k a ha).tgt_mor.symm

/-- **An element of `M(Ψ̄, Ψ̄')` is determined by its source and its image under `p`.** -/
theorem eq_of_proj {h₁ h₂ : Ψe.Trans Ψe'} (hs : h₁.src = h₂.src)
    (hp : S.proj S' h₁ = S.proj S' h₂) : h₁ = h₂ := by
  have hm : h₁.mor = h₂.mor := Subtype.ext (Prod.ext (congrArg TransitionSet.mor hp)
    (by rw [trans_mor_snd, trans_mor_snd, hs]))
  refine TransitionSet.ext hs hm (Ψe'.injective_obj ?_)
  have e1 := trans_act_mor h₁
  have e2 := trans_act_mor h₂
  rw [hm] at e1
  exact e1.symm.trans e2

theorem lift_proj (h : Ψe.Trans Ψe') : S.lift S' (S.proj S' h) h.src rfl = h :=
  S.eq_of_proj S' rfl (S.proj_lift S' _ _ _)

theorem lift_congr {k k' : S.toBase.Trans S'.toBase} (hk : k = k') {a a' : Ψe.O} (haa : a = a')
    (ha : S.p a = k.src) (ha' : S.p a' = k'.src) : S.lift S' k a ha = S.lift S' k' a' ha' := by
  subst hk haa; rfl

theorem eq_lift_iff {h : Ψe.Trans Ψe'} {k : S.toBase.Trans S'.toBase} {a : Ψe.O}
    (ha : S.p a = k.src) : h = S.lift S' k a ha ↔ h.src = a ∧ S.proj S' h = k :=
  ⟨fun e => e ▸ ⟨rfl, S.proj_lift S' k a ha⟩, fun ⟨e₁, e₂⟩ =>
    S.eq_of_proj S' e₁ (e₂.trans (S.proj_lift S' k a ha).symm)⟩

/-- **The source map covers `s`** (p. 893): `s ∘ p = p ∘ s`. -/
theorem src_proj (h : Ψe.Trans Ψe') : (S.proj S' h).src = S.p h.src := rfl

/-- **The target map covers `t`** (p. 893): `t ∘ p = p' ∘ t`. -/
theorem tgt_proj (h : Ψe.Trans Ψe') : (S.proj S' h).tgt = S'.p h.tgt := rfl

/-- **The unit map covers `u`** (p. 893): `p(u(a)) = u(p(a))`. -/
theorem proj_unit (a : Ψe.O) :
    S.proj S (TransitionSet.unit a) = TransitionSet.unit (S.p a) :=
  TransitionSet.ext rfl (congrArg C.toGroupoidStr.unit (S.P_obj' a)) rfl

/-- **The inversion map covers `ι`** (p. 893): `p(ι(h̄)) = ι(p(h̄))`. -/
theorem proj_inv (h : Ψe.Trans Ψe') : S'.proj S h.inv = (S.proj S' h).inv := rfl

/-- Composable elements of `M(Ψ̄', Ψ̄'') × M(Ψ̄, Ψ̄')` have composable images under `p`. -/
theorem proj_composable (h' : Ψe'.Trans Ψe'') (h : Ψe.Trans Ψe')
    (hc : μ.cat.toGroupoidStr.src h'.mor = μ.cat.toGroupoidStr.tgt h.mor) :
    C.toGroupoidStr.src (S'.proj S'' h').mor = C.toGroupoidStr.tgt (S.proj S' h).mor :=
  (μ.proj.src_mor h'.mor).trans ((congrArg μ.P hc).trans (μ.proj.tgt_mor h.mor).symm)

/-- **The multiplication covers `m`** (p. 894): `p(m(h̄', h̄)) = m(p(h̄'), p(h̄))`. -/
theorem proj_comp (h' : Ψe'.Trans Ψe'') (h : Ψe.Trans Ψe')
    (hc : μ.cat.toGroupoidStr.src h'.mor = μ.cat.toGroupoidStr.tgt h.mor) :
    S.proj S'' (TransitionSet.comp h' h hc) =
      TransitionSet.comp (S'.proj S'' h') (S.proj S' h) (S.proj_composable S' S'' h' h hc) :=
  TransitionSet.ext rfl (μ.cat_comp_fst hc) rfl

/-- **`p ∘ Ψ̂ = Ψ̂ ∘ (Id × p)`**: `p(a, Ψ̄(g, a), g ∗ a) = (p(a), Ψ(g, p(a)), g ∗ p(a))`. -/
theorem proj_hat (g : Ψe.G) (a : Ψe.O) :
    S.proj S (Ψe.hat (g, a)) = S.toBase.hat (g, S.p a) :=
  TransitionSet.ext rfl (S.mor_fst g a) (S.p_smul g a)

/-- The fibre of `p` over `k = (o, φ, o')` is in bijection with `K_o`: `a ↦ lift k a`. -/
def projFiberEquiv (k : S.toBase.Trans S'.toBase) :
    S.p ⁻¹' {k.src} ≃ {h : Ψe.Trans Ψe' // S.proj S' h = k} where
  toFun a := ⟨S.lift S' k a a.2, S.proj_lift S' _ _ _⟩
  invFun h := ⟨h.1.src, show S.p h.1.src = k.src from congrArg TransitionSet.src h.2⟩
  left_inv _ := rfl
  right_inv h := Subtype.ext ((S.eq_lift_iff S' _).2 ⟨rfl, h.2⟩).symm

end StrongBundleStr

end GroupoidalCategory

end Polyfold
