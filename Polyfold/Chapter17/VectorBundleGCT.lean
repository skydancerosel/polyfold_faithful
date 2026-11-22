import Polyfold.Chapter17.GroupoidalCategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.7 "Strong Bundle Structures", pp. 824–825: the category `E_μ` of a functor `μ : C → Ban`, the
projection `P : E → C`, and **Definition 17.7.1** (vector bundle GCT).  Numbers and pages are the
2021 text's.

# Vector bundle GCTs

## The text, paraphrased

(p. 824) For a GCT `C` with a polyfold structure and a functor `μ : C → Ban` (Banach spaces and
topological linear isomorphisms), `φ̂ := μ(φ)`, the category `E = E_μ` has the objects `(α, e)`,
`e ∈ μ(α)`, and the morphisms `(φ, e) : (s(φ), e) → (t(φ), φ̂(e))`, `e ∈ μ(s(φ))`.  The projection
`P : E → C`, `P(α, e) = α`, `P(φ, e) = φ`, is a functor; `P⁻¹(α)` and `P⁻¹(φ)` are Banach spaces
with `(α, e) + λ(α, e') = (α, e + λe')`.

(Definition 17.7.1) A vector bundle GCT over `C` is a functor `μ : C → Ban` with a metrizable
topology `T` on `|E_μ|` such that (1) for every object `α` the natural map `P⁻¹(α) → |E|` is
continuous, and (2) `|P| : |E| → |C|` is surjective, continuous and open.

## What is formalized (namespace `Polyfold.GroupoidalCategory`, `Polyfold.GCT`)

* `BanachFunctor C`: a functor `μ : C → Ban`, the Banach spaces `V α` and the topological linear
  isomorphisms `map φ : V (s φ) ≃L V (t φ)` with the functor laws, stated through
  `BanachFunctor.act φ (α, e) = (t φ, φ̂ e)` (`act_unit`, `act_comp`).
* `BanachFunctor.EObj` (objects `(α, e)`), `BanachFunctor.EMor` (morphisms `(φ, e)`, `e` over `s(φ)`),
  the groupoid `BanachFunctor.groupoid : GroupoidStr EObj EMor` (all morphisms invertible,
  `(φ, e)⁻¹ = (φ⁻¹, φ̂ e)`), `finite_mor` (finite morphism sets, so `E_μ` is a groupoidal category
  `BanachFunctor.toGroupoidalCategory`), and the projection functor `BanachFunctor.proj : E → C`.
* The fibres: `fiberEquiv α : P⁻¹(α) ≃ V α` and `morFiberEquiv φ : P⁻¹(φ) ≃ V (s φ)`, which carry
  the vector space operations of p. 825.
* `GCT.VectorBundle C` (**Definition 17.7.1**): a `BanachFunctor` with a metrizable topology on
  `|E_μ|`, (1) `continuous_fiber`, (2) `surjective_orbitProj`, `continuous_orbitProj`,
  `isOpenMap_orbitProj`.

## Readings

* `Ban` is read as Banach spaces over `ℝ` and topological linear isomorphisms (`≃L[ℝ]`).
* The objects of `E_μ` form the type synonym `EObj` of `Σ α, V α`; no topology is put on it, so
  that the only topology in sight is the topology `T` of `|E|` given in Definition 17.7.1.  A
  morphism `(φ, e)` is a pair with `e ∈ μ(s φ)`, written as a pair `(φ, (α, v))` with `α = s φ`.
* The composition of non-composable pairs is the second argument, as for the other groupoids of
  the formalization (`GroupoidStr`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

/-- `(t φ, μ(φ)(e))` for `e = (α, v)` with `α = s φ`: the target of the morphism `(φ, e)` of
`E_μ` (p. 824), for any family of maps `m φ : V (s φ) → V (t φ)`. -/
def sigmaAct {Obj Mor : Type u} {V : Obj → Type u} (src tgt : Mor → Obj)
    (m : ∀ φ, V (src φ) → V (tgt φ)) (φ : Mor) (e : Σ a, V a) (h : e.1 = src φ) : Σ a, V a :=
  ⟨tgt φ, m φ (cast (congrArg V h) e.2)⟩

/-- **A functor `μ : C → Ban`** (2021 p. 824): Banach spaces `μ(α) = V α` and topological linear
isomorphisms `φ̂ = μ(φ) : V (s φ) → V (t φ)` with `μ(1_α) = 1` and `μ(φ ∘ ψ) = μ(φ) ∘ μ(ψ)`,
stated on the pairs `(α, e)` (`sigmaAct`). -/
structure BanachFunctor (C : GroupoidalCategory.{u}) : Type (u + 1) where
  /-- The Banach space `μ(α)`. -/
  V : C.Obj → Type u
  [normed : ∀ α, NormedAddCommGroup (V α)]
  [space : ∀ α, NormedSpace ℝ (V α)]
  [complete : ∀ α, CompleteSpace (V α)]
  /-- `φ̂ = μ(φ) : μ(s φ) → μ(t φ)`, a topological linear isomorphism. -/
  map : ∀ φ : C.Mor, V (C.toGroupoidStr.src φ) ≃L[ℝ] V (C.toGroupoidStr.tgt φ)
  /-- `μ(1_α) = 1`. -/
  act_unit : ∀ (e : Σ a, V a) (h : e.1 = C.toGroupoidStr.src (C.toGroupoidStr.unit e.1)),
    sigmaAct C.toGroupoidStr.src C.toGroupoidStr.tgt (fun φ => map φ)
      (C.toGroupoidStr.unit e.1) e h = e
  /-- `μ(φ ∘ ψ) = μ(φ) ∘ μ(ψ)`. -/
  act_comp : ∀ (φ ψ : C.Mor) (hφψ : C.toGroupoidStr.src φ = C.toGroupoidStr.tgt ψ)
    (e : Σ a, V a) (h : e.1 = C.toGroupoidStr.src ψ),
    sigmaAct C.toGroupoidStr.src C.toGroupoidStr.tgt (fun φ => map φ)
        (C.toGroupoidStr.comp φ ψ) e (h.trans (C.toGroupoidStr.src_comp φ ψ hφψ).symm) =
      sigmaAct C.toGroupoidStr.src C.toGroupoidStr.tgt (fun φ => map φ) φ
        (sigmaAct C.toGroupoidStr.src C.toGroupoidStr.tgt (fun φ => map φ) ψ e h) hφψ.symm

attribute [instance] BanachFunctor.normed BanachFunctor.space BanachFunctor.complete

namespace BanachFunctor

variable {C : GroupoidalCategory.{u}} (μ : BanachFunctor C)


/-- The objects `(α, e)`, `e ∈ μ(α)`, of `E_μ` (a type synonym of `Σ α, μ(α)` without topology). -/
def EObj : Type u := Σ α, μ.V α

/-- The object `(α, e)`. -/
abbrev objMk (α : C.Obj) (v : μ.V α) : μ.EObj := ⟨α, v⟩

/-- `P(α, e) = α`. -/
abbrev base (e : μ.EObj) : C.Obj := Sigma.fst e

/-- The morphisms `(φ, e)`, `e ∈ μ(s φ)`, of `E_μ`. -/
abbrev EMor : Type u := {p : C.Mor × μ.EObj // μ.base p.2 = C.toGroupoidStr.src p.1}

variable {μ}

/-- The underlying morphism `φ` of `(φ, e)`. -/
abbrev EMor.φ (a : μ.EMor) : C.Mor := a.1.1

/-- The source `(s φ, e)` of `(φ, e)`. -/
abbrev EMor.e (a : μ.EMor) : μ.EObj := a.1.2

theorem EMor.base_e (a : μ.EMor) : μ.base a.e = C.toGroupoidStr.src a.φ := a.2

@[ext] theorem EMor.ext {a b : μ.EMor} (h₁ : a.φ = b.φ) (h₂ : a.e = b.e) : a = b :=
  Subtype.ext (Prod.ext h₁ h₂)

variable (μ)

/-- `(t φ, φ̂(e))` (p. 824). -/
def act (φ : C.Mor) (e : μ.EObj) (h : μ.base e = C.toGroupoidStr.src φ) : μ.EObj :=
  sigmaAct C.toGroupoidStr.src C.toGroupoidStr.tgt (fun φ => μ.map φ) φ e h

variable {μ}

@[simp] theorem base_act (φ : C.Mor) (e : μ.EObj) (h : μ.base e = C.toGroupoidStr.src φ) :
    μ.base (μ.act φ e h) = C.toGroupoidStr.tgt φ := rfl

theorem act_congr {φ φ' : C.Mor} {e e' : μ.EObj} (hφ : φ = φ') (he : e = e')
    (h : μ.base e = C.toGroupoidStr.src φ) (h' : μ.base e' = C.toGroupoidStr.src φ') : μ.act φ e h = μ.act φ' e' h' := by
  subst hφ he; rfl

theorem act_unit' {α : C.Obj} (e : μ.EObj) (h : μ.base e = C.toGroupoidStr.src (C.toGroupoidStr.unit α)) :
    μ.act (C.toGroupoidStr.unit α) e h = e := by
  have hα : μ.base e = α := h.trans (C.toGroupoidStr.src_unit α)
  calc μ.act (C.toGroupoidStr.unit α) e h
      = μ.act (C.toGroupoidStr.unit e.1) e (C.toGroupoidStr.src_unit _).symm :=
        act_congr (by rw [show e.1 = α from hα]) rfl _ _
    _ = e := μ.act_unit e _

theorem act_comp' (φ ψ : C.Mor) (hφψ : C.toGroupoidStr.src φ = C.toGroupoidStr.tgt ψ) (e : μ.EObj)
    (h : μ.base e = C.toGroupoidStr.src (C.toGroupoidStr.comp φ ψ)) :
    μ.act (C.toGroupoidStr.comp φ ψ) e h =
      μ.act φ (μ.act ψ e (h.trans (C.toGroupoidStr.src_comp φ ψ hφψ))) hφψ.symm :=
  μ.act_comp φ ψ hφψ e (h.trans (C.toGroupoidStr.src_comp φ ψ hφψ))

/-- `φ⁻¹` undoes `φ`: `μ(φ⁻¹)(μ(φ) e) = e`. -/
theorem act_inv_act (φ : C.Mor) (e : μ.EObj) (h : μ.base e = C.toGroupoidStr.src φ) :
    μ.act (C.toGroupoidStr.inv φ) (μ.act φ e h) (C.toGroupoidStr.src_inv φ).symm = e := by
  have h1 : μ.base e = C.toGroupoidStr.src (C.toGroupoidStr.comp (C.toGroupoidStr.inv φ) φ) := by
    rw [C.toGroupoidStr.src_comp _ _ (C.toGroupoidStr.src_inv φ)]; exact h
  have := act_comp' (C.toGroupoidStr.inv φ) φ (C.toGroupoidStr.src_inv φ) e h1
  rw [← this]
  have h2 : C.toGroupoidStr.comp (C.toGroupoidStr.inv φ) φ = C.toGroupoidStr.unit (C.toGroupoidStr.src φ) := C.toGroupoidStr.inv_comp φ
  rw [act_congr h2 rfl h1 (by rw [← h2]; exact h1)]
  exact act_unit' e _

/-- `φ` undoes `φ⁻¹`. -/
theorem act_act_inv (φ : C.Mor) (e : μ.EObj) (h : μ.base e = C.toGroupoidStr.src (C.toGroupoidStr.inv φ)) :
    μ.act φ (μ.act (C.toGroupoidStr.inv φ) e h) ((C.toGroupoidStr.tgt_inv φ)) = e := by
  have h1 : μ.base e = C.toGroupoidStr.src (C.toGroupoidStr.comp φ (C.toGroupoidStr.inv φ)) := by
    rw [C.toGroupoidStr.src_comp _ _ (C.toGroupoidStr.tgt_inv φ).symm]; exact h
  have := act_comp' φ (C.toGroupoidStr.inv φ) (C.toGroupoidStr.tgt_inv φ).symm e h1
  rw [← this]
  have h2 : C.toGroupoidStr.comp φ (C.toGroupoidStr.inv φ) = C.toGroupoidStr.unit (C.toGroupoidStr.tgt φ) := C.toGroupoidStr.comp_inv φ
  rw [act_congr h2 rfl h1 (by rw [← h2]; exact h1)]
  exact act_unit' e _

/-- Two objects over the same `α` with equal values are equal. -/
theorem objMk_eq_iff {α : C.Obj} {v w : μ.V α} : μ.objMk α v = μ.objMk α w ↔ v = w := by
  constructor
  · intro h; exact eq_of_heq (Sigma.mk.inj h).2
  · rintro rfl; rfl

/-- The value `μ(φ)(e)` of `act` for `e = (s φ, v)`. -/
theorem act_objMk (φ : C.Mor) (v : μ.V (C.toGroupoidStr.src φ)) :
    μ.act φ (μ.objMk (C.toGroupoidStr.src φ) v) rfl = μ.objMk (C.toGroupoidStr.tgt φ) (μ.map φ v) := rfl

/-- `μ(φ)` is injective on objects over `s φ`. -/
theorem act_injective {φ : C.Mor} {e e' : μ.EObj} (h : μ.base e = C.toGroupoidStr.src φ)
    (h' : μ.base e' = C.toGroupoidStr.src φ) (he : μ.act φ e h = μ.act φ e' h') : e = e' := by
  rw [← act_inv_act φ e h, ← act_inv_act φ e' h']
  exact act_congr rfl he _ _

/-- `(φ, e') ∘ (ψ, e) = (φ ∘ ψ, e)` for a composable pair (`e' = ψ̂ e`). -/
def compMor (a b : μ.EMor) (h : a.e = μ.act b.φ b.e b.2) : μ.EMor :=
  ⟨(C.toGroupoidStr.comp a.φ b.φ, b.e), b.2.trans (C.toGroupoidStr.src_comp _ _
    (a.2.symm.trans ((congrArg μ.base h).trans (base_act _ _ _)))).symm⟩

theorem composable_of {a b : μ.EMor} (h : a.e = μ.act b.φ b.e b.2) :
    C.toGroupoidStr.src a.φ = C.toGroupoidStr.tgt b.φ :=
  a.2.symm.trans ((congrArg μ.base h).trans (base_act _ _ _))

@[simp] theorem compMor_φ (a b : μ.EMor) (h : a.e = μ.act b.φ b.e b.2) :
    (compMor a b h).φ = C.toGroupoidStr.comp a.φ b.φ := rfl

@[simp] theorem compMor_e (a b : μ.EMor) (h : a.e = μ.act b.φ b.e b.2) :
    (compMor a b h).e = b.e := rfl

variable (μ)

open scoped Classical in
/-- The composition of `E_μ`, with the junk value `b` off composable pairs. -/
def compE (a b : μ.EMor) : μ.EMor :=
  if h : a.e = μ.act b.φ b.e b.2 then compMor a b h else b

/-- `1_{(α, e)} = (1_α, e)`. -/
def unitE (e : μ.EObj) : μ.EMor := ⟨(C.toGroupoidStr.unit e.1, e), (C.toGroupoidStr.src_unit _).symm⟩

/-- `(φ, e)⁻¹ = (φ⁻¹, φ̂ e)`. -/
def invE (a : μ.EMor) : μ.EMor :=
  ⟨(C.toGroupoidStr.inv a.φ, μ.act a.φ a.e a.2), (C.toGroupoidStr.src_inv _).symm⟩

variable {μ} in
theorem compE_of {a b : μ.EMor} (h : a.e = μ.act b.φ b.e b.2) :
    μ.compE a b = compMor a b h := by
  classical
  unfold compE; exact dif_pos h

/-- **The category `E_μ`** (2021 p. 824): objects `(α, e)`, morphisms
`(φ, e) : (s φ, e) → (t φ, φ̂ e)`, composition `(φ, e') ∘ (ψ, e) = (φ ∘ ψ, e)` for
`e' = ψ̂ e`, `1_{(α, e)} = (1_α, e)`, `(φ, e)⁻¹ = (φ⁻¹, φ̂ e)`.  All morphisms are
invertible. -/
def groupoid : GroupoidStr μ.EObj μ.EMor where
  src a := a.e
  tgt a := μ.act a.φ a.e a.2
  comp := μ.compE
  unit := μ.unitE
  inv := μ.invE
  src_comp a b h := by rw [compE_of h]; rfl
  tgt_comp a b h := by
    rw [compE_of h]
    exact (act_comp' _ _ (composable_of h) _ _).trans (act_congr rfl h.symm _ _)
  comp_assoc a b c h₁ h₂ := by
    have hab := composable_of h₁
    have hbc := composable_of h₂
    have h₄ : a.e = μ.act (compMor b c h₂).φ (compMor b c h₂).e (compMor b c h₂).2 := by
      refine h₁.trans ?_
      exact (act_congr rfl h₂ _ _).trans (act_comp' _ _ hbc _ _).symm
    have h₅ : (compMor a b h₁).e = μ.act c.φ c.e c.2 := h₂
    rw [compE_of h₁, compE_of h₂, compE_of h₅, compE_of h₄]
    exact EMor.ext (C.toGroupoidStr.comp_assoc _ _ _ hab hbc) rfl
  src_unit _ := rfl
  tgt_unit e := act_unit' e _
  comp_unit a := by
    have h : a.e = μ.act (μ.unitE a.e).φ (μ.unitE a.e).e (μ.unitE a.e).2 := (act_unit' _ _).symm
    rw [compE_of h]
    exact EMor.ext (C.toGroupoidStr.comp_unit_of_eq a.2.symm) rfl
  unit_comp a := by
    have h : (μ.unitE (μ.act a.φ a.e a.2)).e = μ.act a.φ a.e a.2 := rfl
    rw [compE_of h]
    exact EMor.ext (C.toGroupoidStr.unit_comp_of_eq rfl) rfl
  src_inv _ := rfl
  tgt_inv a := act_inv_act a.φ a.e a.2
  comp_inv a := by
    have h : a.e = μ.act (μ.invE a).φ (μ.invE a).e (μ.invE a).2 := (act_inv_act a.φ a.e a.2).symm
    rw [compE_of h]
    exact EMor.ext (C.toGroupoidStr.comp_inv a.φ) rfl
  inv_comp a := by
    have h : (μ.invE a).e = μ.act a.φ a.e a.2 := rfl
    rw [compE_of h]
    exact EMor.ext ((C.toGroupoidStr.inv_comp a.φ).trans (congrArg C.toGroupoidStr.unit a.2.symm)) rfl

variable {μ}

@[simp] theorem groupoid_src (a : μ.EMor) : μ.groupoid.src a = a.e := rfl

@[simp] theorem groupoid_tgt (a : μ.EMor) : μ.groupoid.tgt a = μ.act a.φ a.e a.2 := rfl

@[simp] theorem groupoid_unit (e : μ.EObj) :
    (μ.groupoid.unit e).φ = C.toGroupoidStr.unit e.1 ∧ (μ.groupoid.unit e).e = e := ⟨rfl, rfl⟩

theorem groupoid_comp_of {a b : μ.EMor} (h : μ.groupoid.src a = μ.groupoid.tgt b) :
    (μ.groupoid.comp a b).φ = C.toGroupoidStr.comp a.φ b.φ ∧ (μ.groupoid.comp a b).e = b.e := by
  have h' : a.e = μ.act b.φ b.e b.2 := h
  change (μ.compE a b).φ = _ ∧ (μ.compE a b).e = _
  rw [compE_of h']
  exact ⟨rfl, rfl⟩

/-- A morphism of `E_μ` is determined by `φ` and its source. -/
theorem eMor_eq_of {a b : μ.EMor} (h₁ : a.φ = b.φ) (h₂ : μ.groupoid.src a = μ.groupoid.src b) :
    a = b := EMor.ext h₁ h₂

/-- **`E_μ` has finite morphism sets** (it is a groupoidal category, Definition 17.1.1): a
morphism `e → e'` is determined by its underlying morphism `P(e) → P(e')` of `C`. -/
theorem finite_mor (e e' : μ.EObj) : (μ.groupoid.mor e e').Finite := by
  refine Set.Finite.of_finite_image (f := fun a : μ.EMor => a.φ) ?_ ?_
  · refine (C.finite_mor e.1 e'.1).subset ?_
    rintro _ ⟨a, ⟨ha, ha'⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · change C.toGroupoidStr.src a.φ = e.1
      rw [← a.2]; exact congrArg μ.base ha
    · change C.toGroupoidStr.tgt a.φ = e'.1
      exact congrArg μ.base ha'
  · intro a ha b hb hab
    exact eMor_eq_of hab (ha.1.trans hb.1.symm)

variable (μ)

/-- `E_μ` as a groupoidal category (Definition 17.1.1 (1)–(3)). -/
def toGroupoidalCategory : GroupoidalCategory.{u} :=
  ⟨μ.EObj, μ.EMor, μ.groupoid, μ.finite_mor⟩

/-- **The projection functor `P : E → C`**, `P(α, e) = α`, `P(φ, e) = φ` (p. 824). -/
def proj : GroupoidFunctor μ.groupoid C.toGroupoidStr where
  obj := μ.base
  mor a := a.φ
  src_mor a := a.2.symm
  tgt_mor _ := rfl
  mor_comp _ _ h := (groupoid_comp_of h).1
  mor_unit _ := rfl

@[simp] theorem proj_obj (e : μ.EObj) : μ.proj.obj e = e.1 := rfl

@[simp] theorem proj_mor (a : μ.EMor) : μ.proj.mor a = a.φ := rfl

/-- **The fibre `P⁻¹(α)` is the Banach space `μ(α)`** (p. 825): `(α, e) ↦ e`; the vector space
operations `(α, e) + λ(α, e') = (α, e + λ e')` are those transported along it. -/
def fiberEquiv (α : C.Obj) : (μ.base ⁻¹' {α}) ≃ μ.V α where
  toFun e := cast (congrArg μ.V e.2) e.1.2
  invFun v := ⟨μ.objMk α v, rfl⟩
  left_inv e := by
    obtain ⟨⟨β, v⟩, h⟩ := e
    change β = α at h
    subst h; rfl
  right_inv _ := rfl

/-- **The fibre `P⁻¹(φ)` over a morphism is the Banach space `μ(s φ)`** (p. 825):
`(φ, e) ↦ e`. -/
def morFiberEquiv (φ : C.Mor) : ({a : μ.EMor | a.φ = φ}) ≃ μ.V (C.toGroupoidStr.src φ) where
  toFun a := cast (congrArg μ.V (a.1.2.trans (congrArg C.toGroupoidStr.src a.2))) a.1.e.2
  invFun v := ⟨⟨(φ, μ.objMk (C.toGroupoidStr.src φ) v), rfl⟩, rfl⟩
  left_inv a := by
    obtain ⟨⟨⟨ψ, ⟨β, v⟩⟩, h⟩, hψ⟩ := a
    change ψ = φ at hψ
    subst hψ
    change β = C.toGroupoidStr.src ψ at h
    subst h; rfl
  right_inv _ := rfl

end BanachFunctor

end GroupoidalCategory

namespace GCT

open GroupoidalCategory

/-- **2021 Definition 17.7.1, p. 825 (vector bundle GCT)**: a functor `μ : C → Ban` and a
metrizable topology `T` on `|E_μ|` such that (1) for every object `α` the natural map
`P⁻¹(α) = μ(α) → |E|` is continuous, (2) `|P| : |E| → |C|` is surjective, continuous and open. -/
structure VectorBundle (C : GCT.{u}) : Type (u + 1) extends BanachFunctor C.toGroupoidalCategory where
  /-- The topology `T` on `|E_μ|`. -/
  [topE : TopologicalSpace toBanachFunctor.groupoid.OrbitSpace]
  /-- `T` is metrizable. -/
  [metrizableE : MetrizableSpace toBanachFunctor.groupoid.OrbitSpace]
  /-- (1) `P⁻¹(α) → |E|` is continuous. -/
  continuous_fiber : ∀ α : C.Obj,
    Continuous fun v : V α => toBanachFunctor.groupoid.π (toBanachFunctor.objMk α v)
  /-- (2) `|P|` is surjective. -/
  surjective_orbitProj : Surjective toBanachFunctor.proj.orbitMap
  /-- (2) `|P|` is continuous. -/
  continuous_orbitProj : Continuous toBanachFunctor.proj.orbitMap
  /-- (2) `|P|` is open. -/
  isOpenMap_orbitProj : IsOpenMap toBanachFunctor.proj.orbitMap

attribute [instance] VectorBundle.topE VectorBundle.metrizableE

end GCT

end Polyfold
