import Polyfold.Chapter19.CoveringConstruction
import Polyfold.Chapter19.StrongBundleUniformizer

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.8 "Covering Constructions for Strong Bundles", "Constructions for Pull-back Diagrams"
(pp. 930–934): the pull-back diagram (19.43), **Definition 19.8.1** (uniformizer for a bundle
covering pull-back), **Definition 19.8.2** (uniformizer construction `F̃`) with the induced
constructions `F`, `F̄`, `F̂`, the transition sets (19.47) with the maps `p` and `m`, and
**Lemma 19.8.3** (the identities (19.48)); the category `P*E_B` and the pull-back `τ*W` (p. 936)
with the functor `Γ̂ : τ*W → P*E_B` of (19.55).  Numbers and pages are the 2021 text's.

# Uniformizers for bundle covering pull-backs

## The text, paraphrased

(19.41)–(19.43) A finite-to-one covering functor `P : A → B` and a functor `μ_B : B → Ban` give
the category `E_B` (objects `(β, e)`, `e ∈ μ_B(β)`, morphisms `(φ, e) : (s φ, e) → (t φ, μ_B(φ) e)`)
with the forgetful functor `P_B : E_B → B`: the pull-back diagram `(P, μ_B)`.
(19.44)–(19.46) The models are a strong bundle `Q : W → E` over `E = G ⋉ O` and a proper covering
model `τ : Ê → E`; a triple `(Ψ, Ψ̂, Γ)` with `(Ψ, Ψ̂)` a uniformizer for `P` and `(Ψ, Γ)` a
uniformizer for `P_B` making (19.45) commute; then `Γ(w) = (Ψ(Q w), A(w))`.
(Definition 19.8.1) Such a triple is a uniformizer for `(P, μ_B)` at `β`: `(Ψ, Ψ̂)` as in
Definition 19.7.3, `(Ψ, Γ)` as in Definition 19.6.1.
(Definition 19.8.2) A uniformizer construction `F̃` assigns to `β` a set `F̃(β)` of such
triples; it induces (1) `F` for `B`, (2) `F̄` for `P_B` inducing `F`, (3) `F̂` for `P` inducing `F`.
(19.47) For two triples, `p(ê, φ̂, ê') = (τ(ê), P(φ̂), τ'(ê'))` and
`m(w, (φ, A(w)), w') = (Q(w), φ, Q'(w'))`.  (Lemma 19.8.3) For `(w, (φ, A(w)), w') ∈ M(Γ, Γ')`:
`s(φ) = Ψ(e)`, `t(φ) = Ψ'(e')`, `Q(w) = e`, `Q'(w') = e'`, `A'(w') = μ_B(φ)(A(w))`.
(p. 936) `τ*W` has objects `(ê, w)` with `τ(ê) = Q(w)` and morphisms `(σ̂, w)` with
`τ(s(σ̂)) = Q(w)`, `s(σ̂, w) = (s(σ̂), w)`, `t(σ̂, w) = (t(σ̂), μ_W(τ(σ̂))(w))`.
`P*E_B` has objects
`(α, (β, v))` with `β = P(α)` and morphisms `(φ̂, (β, v))` with `β = P(s(φ̂))`,
`t(φ̂, (β, v)) = (t(φ̂), (P(t(φ̂)), μ_B(P(φ̂))(v)))`.  (19.55) `Γ̂(ê, w) = (Ψ̂(ê), Γ(w))`,
`Γ̂(σ̂, w) = (Ψ̂(σ̂), Γ(w))`.

## What is formalized (namespace `Polyfold.GroupoidalCategory`)

* `BanFunctor.pull μ P` (**`μ_B ∘ P`, the functor whose category is `P*E_B`**): the total space
  `{(α, v) | P(α) = P_B(v)}` with the fibres `μ_B(P(α))` and the lifts `μ_B(P(φ̂))`;
  `BanFunctor.pullFiberCLE` (the fibre over `α` is `μ_B(P(α))`), `pull_act` (the action).
* `StrongBundleOver μ Ψ` (**the data `Γ` of a strong bundle uniformizer `(Ψ, Γ)` with given
  underlying uniformizer `Ψ`**, Definition 19.6.1 (1) with `O`, `G` and `Ψ` those of `Ψ`),
  `StrongBundleOver.toUniformizer` (`Γ`), `toStr` (Definition 19.6.1 (1)), `toStr_toBase`
  (`Ψ` is the underlying uniformizer, by definition), `amap` (`A : Q⁻¹(e) → μ_B(Ψ(e))`),
  `obj_eq` ((19.46)).
* `PullbackUniformizer P μ β` (**Definition 19.8.1**), `toStrongBundleUniformizer`,
  `definition_19_8_1` (the diagram (19.45) commutes and (19.46)).
* `PullbackUniformizerConstruction P μ` (**Definition 19.8.2**), `.Unif`, the induced
  `hatU` (`F̂`, (3)), `toUniformizerConstruction` (`F`, (1)), `barF` (`F̄`, (2)),
  `definition_19_8_2` (`F̂` and `F̄` both induce `F`).
* The transition sets (19.47): `PullbackUniformizer.TransG` (`M(Γ, Γ')`), `mG` (`m`), `pHat`
  (`p`), `lemma_19_8_3` (**Lemma 19.8.3**).
* `PullbackUniformizer.tauW` (the groupoid `τ*W`), `tauWProj` (`τ̂ : τ*W → W` on objects),
  `gammaHat` (**the functor `Γ̂ : τ*W → P*E_B` of (19.55)**), `injective_gammaHat`,
  `full_gammaHat`, `faithful_gammaHat` (Theorem 19.8.6: `Γ̂` is fully faithful and injective on
  objects), `gammaHat_comm` (the diagram (19.61) on objects and morphisms).

## Readings

* `μ_B : B → Ban` is Chapter 19's `BanFunctor` (§19.6): Banachable fibres, the text's footnote.
  `E_B` is `μ_B.cat`, `P_B` is `μ_B.proj`.
* Definition 19.8.1 asks `(Ψ, Γ)` to be a strong bundle uniformizer with **the same** `Ψ` as
  `(Ψ, Ψ̂)` (the diagram (19.45) has one `Ψ`).  We formalize the strong bundle part as
  `StrongBundleOver μ Ψ`: Definition 19.6.1 (1) with the base `O`, the group `G` and the functor
  `Ψ` taken from `Ψ`; `toStr` turns it into the structure `StrongBundleStr` of §19.6 whose
  underlying uniformizer is `Ψ` itself (`toStr_toBase`, by definition).
* Definition 19.8.2: `F̃ : B → SET` is read on objects (as Definitions 19.1.3, 19.7.7).  The
  induced `F̄` is the set of strong bundle uniformizers `(Ψ, Γ)` at `β` (Definition 19.6.1) given by
  the members of `F̃(β)`, each with its structure; it induces `F` (`definition_19_8_2`).
* (19.47): `M(Γ, Γ')` is the transition set of the functors `Γ`, `Γ'` into `E_B`; its elements
  `(w, (φ, e), w')` have `e = Γ(w) = (Ψ(Q w), A(w))`.  `m` is §19.6's `p` (`StrongBundleStr.proj`),
  `p` is §19.7's `p` (`CoveringUniformizer.transMap`).
* p. 936: `τ*W` is a groupoid (the objects and morphisms of the text); the action
  `μ_W(τ(σ̂))` of a morphism `τ(σ̂) = (g, o)` of `G ⋉ O` on `W` is `w ↦ g ∗ w`.  `P*E_B` is the
  category `(μ_B ∘ P).cat` of `BanFunctor.pull`: its objects `(α, v)` carry `β = P(α)` implicitly.
-/

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

variable {A B : GroupoidalCategory.{u}}

/-! ### The functor `μ_B ∘ P` and the category `P*E_B` -/

namespace BanFunctor

variable (μ : B.BanFunctor) (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr)

/-- The topology of the fibre `{(α, v)} ≅ μ_B(P(α))` of `μ_B ∘ P`. -/
@[instance_reducible] def pullTop (α : A.Obj) : TopologicalSpace (pullbackProj μ.P P.obj ⁻¹' {α}) :=
  TopologicalSpace.induced (pullbackFiberEquiv μ.P P.obj α) inferInstance

section PullTop

attribute [local instance] pullTop

/-- The fibre of `μ_B ∘ P` over `α` is `μ_B(P(α))`. -/
def pullCLE (α : A.Obj) : (pullbackProj μ.P P.obj ⁻¹' {α}) ≃L[ℝ] μ.P ⁻¹' {P.obj α} where
  toFun := pullbackFiberEquiv μ.P P.obj α
  invFun := (pullbackFiberEquiv μ.P P.obj α).symm
  map_add' := pullbackFiberEquiv_add μ.P P.obj α
  map_smul' := pullbackFiberEquiv_smul μ.P P.obj α
  left_inv := (pullbackFiberEquiv μ.P P.obj α).left_inv
  right_inv := (pullbackFiberEquiv μ.P P.obj α).right_inv
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 (by
    change Continuous ((pullbackFiberEquiv μ.P P.obj α) ∘ (pullbackFiberEquiv μ.P P.obj α).symm)
    rw [Equiv.self_comp_symm]; exact continuous_id)

/-- The lift `μ_B(P(φ̂)) : μ_B(P(s φ̂)) → μ_B(P(t φ̂))`. -/
def pullLift (φ : A.Mor) : (pullbackProj μ.P P.obj ⁻¹' {A.toGroupoidStr.src φ}) →L[ℝ]
    (pullbackProj μ.P P.obj ⁻¹' {A.toGroupoidStr.tgt φ}) :=
  ((μ.pullCLE P (A.toGroupoidStr.tgt φ)).symm.toContinuousLinearMap.comp
    ((μ.fiberCast (P.tgt_mor φ)).toContinuousLinearMap.comp ((μ.lift (P.mor φ)).comp
      (μ.fiberCast (P.src_mor φ).symm).toContinuousLinearMap))).comp
    (μ.pullCLE P (A.toGroupoidStr.src φ)).toContinuousLinearMap

theorem pullLift_val (φ : A.Mor) (v : pullbackProj μ.P P.obj ⁻¹' {A.toGroupoidStr.src φ}) :
    ((μ.pullLift P φ v : pullbackSpace μ.P P.obj) : A.Obj × μ.E) =
      (A.toGroupoidStr.tgt φ, μ.act ⟨(P.mor φ, ((v : pullbackSpace μ.P P.obj) : A.Obj × μ.E).2),
        (v.1.2.trans (congrArg P.obj v.2)).trans (P.src_mor φ).symm⟩) := by
  simp only [pullLift, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, fiberCast_eq]
  rfl

end PullTop

/-- **The functor `μ_B ∘ P : A → Ban`** (p. 936), whose category is `P*E_B`: the fibre over `α`
is `μ_B(P(α))` (the pairs `(α, v)`), the lift of `φ̂` is `μ_B(P(φ̂))`. -/
def pull : A.BanFunctor where
  E := pullbackSpace μ.P P.obj
  P := pullbackProj μ.P P.obj
  topFib := μ.pullTop P
  banachable α := by
    let _ := μ.pullTop P α
    obtain ⟨Bsp, h1, h2, h3, ⟨e⟩⟩ := μ.banachable (P.obj α)
    exact ⟨Bsp, h1, h2, h3, ⟨(μ.pullCLE P α).trans e⟩⟩
  lift := μ.pullLift P
  lift_unit e h := by
    apply Subtype.ext
    rw [pullLift_val]
    refine Prod.ext (A.toGroupoidStr.tgt_unit _) ?_
    change μ.act _ = (e : A.Obj × μ.E).2
    refine (μ.act_congr ?_).trans (μ.act_unitPair _)
    refine Prod.ext ?_ rfl
    change P.mor (A.toGroupoidStr.unit (pullbackProj μ.P P.obj e)) =
      B.toGroupoidStr.unit (μ.P (e : A.Obj × μ.E).2)
    rw [P.mor_unit]
    exact congrArg _ e.2.symm
  lift_comp φ' φ hc e h := by
    apply Subtype.ext
    rw [pullLift_val, pullLift_val]
    refine Prod.ext (A.toGroupoidStr.tgt_comp _ _ hc) ?_
    change μ.act _ = μ.act _
    have h₁ : μ.P (e : A.Obj × μ.E).2 = B.toGroupoidStr.src (P.mor φ) :=
      (e.2.trans (congrArg P.obj h)).trans (P.src_mor φ).symm
    have h₂ : B.toGroupoidStr.src (P.mor φ') = B.toGroupoidStr.tgt (P.mor φ) := by
      rw [P.src_mor, P.tgt_mor, hc]
    refine Eq.trans ?_ (Eq.trans (μ.act_comp (P.mor φ') (P.mor φ) _ h₁ h₂) ?_)
    · exact μ.act_congr (Prod.ext (P.mor_comp φ' φ hc) rfl)
    · exact μ.act_congr (Prod.ext rfl (congrArg Prod.snd (μ.pullLift_val P φ ⟨e, h⟩)).symm)

variable {μ P}

/-- An object `(α, v)` of `P*E_B` as a pair. -/
def pullPt (e : (μ.pull P).E) : A.Obj × μ.E := Subtype.val (p := (· ∈ pullbackSpace μ.P P.obj)) e

theorem pullPt_prop (e : (μ.pull P).E) : μ.P (pullPt e).2 = P.obj (pullPt e).1 :=
  Subtype.prop (p := (· ∈ pullbackSpace μ.P P.obj)) e

theorem pullPt_injective : Injective (pullPt (μ := μ) (P := P)) :=
  Subtype.val_injective (p := (· ∈ pullbackSpace μ.P P.obj))

/-- The object `(α, v)` of `P*E_B` for `P(α) = P_B(v)`. -/
def pullMk (α : A.Obj) (v : μ.E) (h : μ.P v = P.obj α) : (μ.pull P).E := ⟨(α, v), h⟩

@[simp] theorem pullPt_mk (α : A.Obj) (v : μ.E) (h : μ.P v = P.obj α) :
    pullPt (pullMk (μ := μ) (P := P) α v h) = (α, v) := rfl

@[simp] theorem pull_P_apply (e : (μ.pull P).E) : (μ.pull P).P e = (pullPt e).1 := rfl

variable (μ P)

/-- **The action of `μ_B ∘ P`**: `(φ̂, (α, v)) ↦ (t(φ̂), μ_B(P(φ̂))(v))`. -/
theorem pull_act (q : pullbackSpace (μ.pull P).P A.toGroupoidStr.src) :
    pullPt ((μ.pull P).act q) =
      (A.toGroupoidStr.tgt (q : A.Mor × (μ.pull P).E).1,
        μ.act ⟨(P.mor (q : A.Mor × (μ.pull P).E).1, (pullPt (q : A.Mor × (μ.pull P).E).2).2),
          (pullPt_prop _).trans ((congrArg P.obj q.2).trans (P.src_mor _).symm)⟩) :=
  μ.pullLift_val P _ _

/-- **The fibre of `μ_B ∘ P` over `α` is `μ_B(P(α))`.** -/
def pullFiberCLE (α : A.Obj) : (μ.pull P).P ⁻¹' {α} ≃L[ℝ] μ.P ⁻¹' {P.obj α} := μ.pullCLE P α

/-- A morphism `(φ̂, (α, v))` of `P*E_B` as the morphism `(P(φ̂), v)` of `E_B`. -/
def pullMorE (q : (μ.pull P).cat.Mor) : μ.cat.Mor :=
  ⟨(P.mor (q : A.Mor × (μ.pull P).E).1, (pullPt (q : A.Mor × (μ.pull P).E).2).2),
    (pullPt_prop _).trans ((congrArg P.obj q.2).trans (P.src_mor _).symm)⟩

theorem act_pullMorE (q : (μ.pull P).cat.Mor) :
    μ.act (μ.pullMorE P q) = (pullPt ((μ.pull P).act q)).2 := by
  rw [pull_act]; rfl

/-- **The forgetful functor `P*E_B → E_B`**, `(α, v) ↦ v`, `(φ̂, (α, v)) ↦ (P(φ̂), v)`. -/
def pullToE : GroupoidFunctor (μ.pull P).cat.toGroupoidStr μ.cat.toGroupoidStr where
  obj e := (pullPt e).2
  mor := μ.pullMorE P
  src_mor _ := rfl
  tgt_mor q := μ.act_pullMorE P q
  mor_comp φ ψ h := by
    have h2 : ((μ.pullMorE P φ : μ.cat.Mor) : B.Mor × μ.E).2 = μ.act (μ.pullMorE P ψ) := by
      rw [act_pullMorE]
      exact congrArg (fun e : (μ.pull P).E => (pullPt e).2) h
    apply Subtype.ext
    change (P.mor (((μ.pull P).morComp φ ψ : A.Mor × (μ.pull P).E).1),
        (pullPt (((μ.pull P).morComp φ ψ : A.Mor × (μ.pull P).E).2)).2) =
          (μ.morComp _ _ : B.Mor × μ.E)
    rw [(μ.pull P).morComp_val h, μ.morComp_val h2]
    exact Prod.ext (P.mor_comp _ _ (src_eq_tgt_of_eq_act (μ := μ.pull P) h)) rfl
  mor_unit e := by
    apply Subtype.ext
    exact Prod.ext ((P.mor_unit _).trans (congrArg _ (pullPt_prop e).symm)) rfl

end BanFunctor

/-! ### Groupoid actions and their action groupoids -/

/-- A (left) action of a groupoid `X` on a type `Y` over an anchor `π : Y → Obj`: `σ` acts on the
`y` with `π(y) = s(σ)`, `π(σ ∗ y) = t(σ)`, units act trivially and `(σ' ∘ σ) ∗ y = σ' ∗ (σ ∗ y)`.
(The pull-back `τ*W` of p. 936 is the action groupoid of such an action of `Ê`.) -/
structure GroupoidAction {Obj Mor : Type u} (X : GroupoidStr Obj Mor) (Y : Type u) where
  /-- The anchor `π : Y → Obj`. -/
  anchor : Y → Obj
  /-- The action `(σ, y) ↦ σ ∗ y` for `π(y) = s(σ)`. -/
  act : pullbackSpace anchor X.src → Y
  anchor_act : ∀ q, anchor (act q) = X.tgt (q : Mor × Y).1
  act_unit : ∀ y, act ⟨(X.unit (anchor y), y), (X.src_unit _).symm⟩ = y
  act_comp : ∀ (ψ γ : Mor) (y : Y) (h₁ : anchor y = X.src γ) (h₂ : X.src ψ = X.tgt γ),
    act ⟨(X.comp ψ γ, y), h₁.trans (X.src_comp ψ γ h₂).symm⟩ =
      act ⟨(ψ, act ⟨(γ, y), h₁⟩), (anchor_act _).trans h₂.symm⟩

namespace GroupoidAction

variable {Obj Mor : Type u} {X : GroupoidStr Obj Mor} {Y : Type u} (a : GroupoidAction X Y)

theorem act_congr {q q' : pullbackSpace a.anchor X.src} (h : (q : Mor × Y) = q') :
    a.act q = a.act q' := congrArg a.act (Subtype.ext h)

/-- The inverse `(σ, y)⁻¹ = (σ⁻¹, σ ∗ y)`. -/
def morInv (q : pullbackSpace a.anchor X.src) : pullbackSpace a.anchor X.src :=
  ⟨(X.inv (q : Mor × Y).1, a.act q), (a.anchor_act q).trans (X.src_inv _).symm⟩

open scoped Classical in
/-- The composite `(σ', σ ∗ y) ∘ (σ, y) = (σ' ∘ σ, y)` (junk off composable pairs). -/
def morComp (q' q : pullbackSpace a.anchor X.src) : pullbackSpace a.anchor X.src :=
  if h : a.anchor (q : Mor × Y).2 = X.src (X.comp (q' : Mor × Y).1 (q : Mor × Y).1) then
    ⟨(X.comp (q' : Mor × Y).1 (q : Mor × Y).1, (q : Mor × Y).2), h⟩
  else q

variable {a}

theorem src_eq_tgt_of_eq_act {q' q : pullbackSpace a.anchor X.src}
    (h : (q' : Mor × Y).2 = a.act q) : X.src (q' : Mor × Y).1 = X.tgt (q : Mor × Y).1 := by
  rw [← (q'.2 : a.anchor (q' : Mor × Y).2 = _), h, a.anchor_act]

theorem morComp_val {q' q : pullbackSpace a.anchor X.src} (h : (q' : Mor × Y).2 = a.act q) :
    (a.morComp q' q : Mor × Y) = (X.comp (q' : Mor × Y).1 (q : Mor × Y).1, (q : Mor × Y).2) := by
  have hc : a.anchor (q : Mor × Y).2 = X.src (X.comp (q' : Mor × Y).1 (q : Mor × Y).1) :=
    (q.2 : a.anchor (q : Mor × Y).2 = _).trans (X.src_comp _ _ (src_eq_tgt_of_eq_act h)).symm
  unfold morComp; rw [dif_pos hc]

theorem act_morComp {q' q : pullbackSpace a.anchor X.src} (h : (q' : Mor × Y).2 = a.act q) :
    a.act (a.morComp q' q) = a.act q' := by
  obtain ⟨⟨γ, w⟩, hq⟩ := q
  obtain ⟨⟨ψ, w'⟩, hq'⟩ := q'
  have h' : w' = a.act ⟨(γ, w), hq⟩ := h
  subst h'
  have hq₁ : a.anchor w = X.src γ := hq
  calc a.act (a.morComp _ _) = a.act ⟨(X.comp ψ γ, w),
        hq₁.trans (X.src_comp ψ γ (src_eq_tgt_of_eq_act h)).symm⟩ := a.act_congr (morComp_val h)
    _ = _ := a.act_comp ψ γ w hq₁ (src_eq_tgt_of_eq_act h)

theorem act_morInv (q : pullbackSpace a.anchor X.src) : a.act (a.morInv q) = (q : Mor × Y).2 := by
  obtain ⟨⟨ψ, w⟩, hq⟩ := q
  have hq' : a.anchor w = X.src ψ := hq
  have h2 : X.src (X.inv ψ) = X.tgt ψ := X.src_inv ψ
  change a.act ⟨(X.inv ψ, a.act ⟨(ψ, w), hq⟩), _⟩ = w
  rw [← a.act_comp (X.inv ψ) ψ w hq' h2]
  refine (a.act_congr ?_).trans (a.act_unit w)
  change (X.comp (X.inv ψ) ψ, w) = (X.unit (a.anchor w), w)
  rw [X.inv_comp, hq']

variable (a)

/-- **The action groupoid** of the action: objects `Y`, morphisms the pairs `(σ, y)` with
`π(y) = s(σ)`, `s(σ, y) = y`, `t(σ, y) = σ ∗ y`. -/
def groupoid : GroupoidStr Y (pullbackSpace a.anchor X.src) where
  src := pullbackProj' a.anchor X.src
  tgt := a.act
  comp := a.morComp
  unit y := ⟨(X.unit (a.anchor y), y), (X.src_unit _).symm⟩
  inv := a.morInv
  src_comp φ ψ h := by
    change (a.morComp φ ψ : Mor × Y).2 = (ψ : Mor × Y).2
    rw [morComp_val h]
  tgt_comp φ ψ h := act_morComp h
  comp_assoc φ ψ χ h₁ h₂ := by
    have h₁' : (φ : Mor × Y).2 = a.act ψ := h₁
    have h₂' : (ψ : Mor × Y).2 = a.act χ := h₂
    have h₃ : (a.morComp φ ψ : Mor × Y).2 = a.act χ := by rw [morComp_val h₁']; exact h₂'
    have h₄ : (φ : Mor × Y).2 = a.act (a.morComp ψ χ) := by rw [act_morComp h₂']; exact h₁'
    apply Subtype.ext
    rw [morComp_val h₃, morComp_val h₁', morComp_val h₄, morComp_val h₂',
      X.comp_assoc _ _ _ (src_eq_tgt_of_eq_act h₁') (src_eq_tgt_of_eq_act h₂')]
  src_unit _ := rfl
  tgt_unit w := a.act_unit w
  comp_unit φ := by
    have h0 : (φ : Mor × Y).2 = a.act ⟨(X.unit (a.anchor (φ : Mor × Y).2), (φ : Mor × Y).2),
        (X.src_unit _).symm⟩ := (a.act_unit _).symm
    apply Subtype.ext
    change (a.morComp φ ⟨(X.unit (a.anchor (φ : Mor × Y).2), (φ : Mor × Y).2),
      (X.src_unit _).symm⟩ : Mor × Y) = φ
    rw [morComp_val h0]
    change (X.comp (φ : Mor × Y).1 (X.unit (a.anchor (φ : Mor × Y).2)), (φ : Mor × Y).2) = φ
    rw [X.comp_unit_of_eq (φ.2 : a.anchor (φ : Mor × Y).2 = _).symm]
  unit_comp φ := by
    apply Subtype.ext
    rw [morComp_val (q' := ⟨(X.unit (a.anchor (a.act φ)), a.act φ), (X.src_unit _).symm⟩) (q := φ)
      rfl]
    change (X.comp (X.unit (a.anchor (a.act φ))) (φ : Mor × Y).1, (φ : Mor × Y).2) = φ
    rw [X.unit_comp_of_eq (a.anchor_act φ).symm]
  src_inv _ := rfl
  tgt_inv φ := act_morInv φ
  comp_inv φ := by
    apply Subtype.ext
    rw [morComp_val (act_morInv φ).symm]
    change (X.comp (φ : Mor × Y).1 (X.inv (φ : Mor × Y).1), a.act φ) =
      (X.unit (a.anchor (a.act φ)), a.act φ)
    rw [X.comp_inv, a.anchor_act]
  inv_comp φ := by
    apply Subtype.ext
    rw [morComp_val (q' := a.morInv φ) (q := φ) rfl]
    change (X.comp (X.inv (φ : Mor × Y).1) (φ : Mor × Y).1, (φ : Mor × Y).2) =
      (X.unit (a.anchor (φ : Mor × Y).2), (φ : Mor × Y).2)
    rw [X.inv_comp, (φ.2 : a.anchor (φ : Mor × Y).2 = _)]

@[simp] theorem groupoid_src (q : pullbackSpace a.anchor X.src) :
    a.groupoid.src q = (q : Mor × Y).2 := rfl
@[simp] theorem groupoid_tgt (q : pullbackSpace a.anchor X.src) : a.groupoid.tgt q = a.act q :=
  rfl

theorem groupoid_comp_val {q' q : pullbackSpace a.anchor X.src}
    (h : a.groupoid.src q' = a.groupoid.tgt q) :
    (a.groupoid.comp q' q : Mor × Y) = (X.comp (q' : Mor × Y).1 (q : Mor × Y).1, (q : Mor × Y).2) :=
  morComp_val h

end GroupoidAction

/-! ### Strong bundle uniformizers over a given uniformizer -/

/-- **The data `Γ` of a strong bundle uniformizer `(Ψ, Γ)` over a given uniformizer
`Ψ : G ⋉ O → B`** (Definition 19.6.1 (1) with the base `O`, the group `G` and the functor `Ψ` those
of `Ψ`): a strong bundle `Q : W → O` on which `G` acts by strong bundle maps covering its action on
`O`, and a functor `Γ : G ⋉ W → E_B`, injective on objects and fully faithful, with
`P_B ∘ Γ = Ψ ∘ (Id ⋉ Q)` and `Γ : W_o → μ_B(Ψ(o))` a topological linear isomorphism. -/
structure StrongBundleOver (μ : B.BanFunctor) (Ψ : B.Uniformizer) : Type (u + 1) where
  /-- The total space `W`. -/
  W : Type u
  [topW : TopologicalSpace W]
  [t2W : T2Space W]
  [paraW : ParacompactSpace W]
  [actW : MulAction Ψ.G W]
  /-- The projection `Q : W → O`. -/
  Q : W → Ψ.O
  [addW : ∀ o, AddCommGroup (Q ⁻¹' {o})]
  [modW : ∀ o, Module ℝ (Q ⁻¹' {o})]
  /-- The strong bundle structure of `Q : W → O`. -/
  bundle : StrongBundle Ψ.P Q
  Q_smul : ∀ (g : Ψ.G) (w : W), Q (g • w) = g • Q w
  /-- `G` acts by strong bundle maps covering its action on `O`. -/
  isStrongBundleMap_smul : ∀ g : Ψ.G, bundle.IsStrongBundleMap bundle (fun y => g • y)
    (fun w => g • w)
  /-- The functor `Γ : G ⋉ W → E_B`. -/
  functor : GroupoidFunctor (GroupoidStr.translation Ψ.G W) μ.cat.toGroupoidStr
  injective_obj : Injective functor.obj
  full : functor.toFunctor.Full
  faithful : functor.toFunctor.Faithful
  /-- `P_B ∘ Γ = Ψ ∘ Q` on objects. -/
  P_obj : ∀ w, μ.P (functor.obj w) = Ψ.obj (Q w)
  /-- `P_B ∘ Γ = Ψ ∘ (Id ⋉ Q)` on morphisms. -/
  mor_fst : ∀ (g : Ψ.G) (w : W), ((functor.mor (g, w) : μ.cat.Mor) : B.Mor × μ.E).1 =
    Ψ.mor (g, Q w)
  /-- `A : Q⁻¹(o) → μ_B(Ψ(o))`, the restriction of `Γ` to the fibres. -/
  fiberCLE : ∀ o, Q ⁻¹' {o} ≃L[ℝ] μ.P ⁻¹' {Ψ.obj o}
  fiberCLE_apply : ∀ o (v : Q ⁻¹' {o}), (fiberCLE o v : μ.E) = functor.obj v

namespace StrongBundleOver

attribute [instance] topW t2W paraW actW addW modW

variable {μ : B.BanFunctor} {Ψ : B.Uniformizer} (Γ : StrongBundleOver μ Ψ)

/-- **The functor `Γ : G ⋉ W → E_B`** as a uniformizer of `E_B` (Definition 19.6.1 (2)). -/
abbrev toUniformizer : μ.cat.Uniformizer where
  O := Γ.W
  P := Γ.bundle.toMPolyfold0
  G := Ψ.G
  smooth_smul g := (Γ.isStrongBundleMap_smul g).isScSmoothMap
  functor := Γ.functor
  injective_obj := Γ.injective_obj
  full := Γ.full
  faithful := Γ.faithful

/-- **The structure (1) of Definition 19.6.1 on `Γ`**, with underlying uniformizer `Ψ`. -/
abbrev toStr : StrongBundleStr μ Γ.toUniformizer where
  O := Ψ.O
  PO := Ψ.P
  actO := Ψ.act
  smooth_smul := Ψ.smooth_smul
  functor := Ψ.functor
  injective_obj := Ψ.injective_obj
  full := Ψ.full
  faithful := Ψ.faithful
  p := Γ.Q
  B := Γ.bundle
  toMPolyfold0_eq := rfl
  p_smul := Γ.Q_smul
  isStrongBundleMap_smul := Γ.isStrongBundleMap_smul
  P_obj := Γ.P_obj
  mor_fst := Γ.mor_fst
  fiberCLE := Γ.fiberCLE
  fiberCLE_apply := Γ.fiberCLE_apply

/-- **The underlying uniformizer of `(Ψ, Γ)` is `Ψ`.** -/
theorem toStr_toBase : Γ.toStr.toBase = Ψ := rfl

/-- `A(w) ∈ μ_B(Ψ(Q w))`, the fibre part of `Γ(w)`. -/
def amap (w : Γ.W) : μ.P ⁻¹' {Ψ.obj (Γ.Q w)} := Γ.fiberCLE (Γ.Q w) ⟨w, rfl⟩

/-- **(19.46)**: `Γ(w) = (Ψ(Q w), A(w))`: `Γ(w)` is `A(w)`, an element of the fibre over
`Ψ(Q(w))`. -/
theorem obj_eq (w : Γ.W) : Γ.functor.obj w = (Γ.amap w : μ.E) ∧
    μ.P (Γ.functor.obj w) = Ψ.obj (Γ.Q w) :=
  ⟨(Γ.fiberCLE_apply (Γ.Q w) ⟨w, rfl⟩).symm, Γ.P_obj w⟩

end StrongBundleOver

/-! ### Definition 19.8.1 -/

/-- **2021 Definition 19.8.1, p. 932 (uniformizer for a bundle covering pull-back `(P, μ_B)` at
`β`)**: a triple `(Ψ, Ψ̂, Γ)` in which `(Ψ, Ψ̂)` is a uniformizer for the finite-to-one covering
functor `P` at `β` (Definition 19.7.3, `Ψh`) and `(Ψ, Γ)` is a strong bundle uniformizer for
`P_B : E_B → B` (Definition 19.6.1) with the same `Ψ` (`bun`), so that (19.45) commutes. -/
structure PullbackUniformizer (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr)
    (μ : B.BanFunctor) (β : B.Obj) : Type (u + 1) where
  /-- The proper covering uniformizer `(Ψ, Ψ̂)`. -/
  Ψh : CoveringUniformizer P β
  /-- The strong bundle uniformizer `Γ` over `Ψ`. -/
  bun : StrongBundleOver μ Ψh.Ψ

namespace PullbackUniformizer

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} {μ : B.BanFunctor}
  {β β' β'' : B.Obj} (x : PullbackUniformizer P μ β) (y : PullbackUniformizer P μ β')

/-- The functor `Γ : W → E_B`. -/
abbrev Γ : μ.cat.Uniformizer := x.bun.toUniformizer

/-- The structure (1) of Definition 19.6.1 on `Γ`. -/
abbrev str : StrongBundleStr μ x.Γ := x.bun.toStr

/-- **`(Ψ, Γ)` is a strong bundle uniformizer at `β`** (Definition 19.6.1). -/
def toStrongBundleUniformizer : StrongBundleUniformizer μ β :=
  ⟨x.Γ, x.str, ⟨x.Ψh.model.pt, x.Ψh.obj_pt⟩⟩

@[simp] theorem toStrongBundleUniformizer_base : x.toStrongBundleUniformizer.str.toBase = x.Ψh.Ψ :=
  rfl

/-- **2021 Definition 19.8.1, the diagram (19.45) and (19.46)**: `P ∘ Ψ̂ = Ψ ∘ τ` and
`P_B ∘ Γ = Ψ ∘ Q` on objects and morphisms, and `Γ(w) = (Ψ(Q(w)), A(w))`. -/
theorem definition_19_8_1 :
    (∀ e, P.obj (x.Ψh.hat.obj e) = x.Ψh.Ψ.obj (x.Ψh.τ.obj e)) ∧
      (∀ φ, P.mor (x.Ψh.hat.mor φ) = x.Ψh.Ψ.mor (x.Ψh.τ.mor φ)) ∧
      (∀ w, μ.proj.obj (x.Γ.obj w) = x.Ψh.Ψ.obj (x.bun.Q w)) ∧
      (∀ (g : x.Ψh.Ψ.G) (w : x.bun.W),
        μ.proj.mor (x.Γ.mor (g, w)) = x.Ψh.Ψ.mor (g, x.bun.Q w)) ∧
      ∀ w, x.Γ.obj w = (x.bun.amap w : μ.E) :=
  ⟨x.Ψh.obj_comm, x.Ψh.mor_comm, x.bun.P_obj, x.bun.mor_fst, fun w => (x.bun.obj_eq w).1⟩

/-! #### The transition sets (19.47) and Lemma 19.8.3 -/

/-- **The transition set `M(Γ, Γ')`** (19.47): the triples `(w, (φ, A(w)), w')`. -/
abbrev TransG : Type u := x.Γ.Trans y.Γ

/-- **The map `m : M(Γ, Γ') → M(Ψ, Ψ')`** (19.47), `m(w, (φ, A(w)), w') = (Q(w), φ, Q'(w'))`. -/
abbrev mG (h : x.TransG y) : x.Ψh.Ψ.Trans y.Ψh.Ψ := x.str.proj y.str h

/-- **The map `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')`** (19.47), `p(ê, φ̂, ê') = (τ(ê), P(φ̂), τ'(ê'))`. -/
abbrev pHat (a : x.Ψh.Trans y.Ψh) : x.Ψh.Ψ.Trans y.Ψh.Ψ := x.Ψh.transMap y.Ψh a

/-- **2021 Lemma 19.8.3, p. 933, the identities (19.48)**: for `(w, (φ, A(w)), w') ∈ M(Γ, Γ')`
with `m(w, (φ, A(w)), w') = (e, φ, e')`: `s(φ) = Ψ(e)`, `t(φ) = Ψ'(e')`, `Q(w) = e`,
`Q'(w') = e'` and `A'(w') = μ_B(φ)(A(w))`. -/
theorem lemma_19_8_3 (h : x.TransG y) :
    B.toGroupoidStr.src (x.mG y h).mor = x.Ψh.Ψ.obj (x.mG y h).src ∧
      B.toGroupoidStr.tgt (x.mG y h).mor = y.Ψh.Ψ.obj (x.mG y h).tgt ∧
      x.bun.Q h.src = (x.mG y h).src ∧ y.bun.Q h.tgt = (x.mG y h).tgt ∧
      (y.bun.amap h.tgt : μ.E) = μ.act ⟨((x.mG y h).mor, (x.bun.amap h.src : μ.E)),
        (show μ.P (x.bun.amap h.src : μ.E) = _ from (x.bun.amap h.src).2).trans
          (x.mG y h).src_mor.symm⟩ := by
  refine ⟨(x.mG y h).src_mor, (x.mG y h).tgt_mor, rfl, rfl, ?_⟩
  refine (y.bun.obj_eq h.tgt).1.symm.trans (h.tgt_mor.symm.trans ?_)
  refine μ.act_congr (Prod.ext rfl ?_)
  exact h.src_mor.trans (x.bun.obj_eq h.src).1

/-! #### The pull-back `τ*W` and the functor `Γ̂ : τ*W → P*E_B` -/

/-- The objects `(ê, w)` of `τ*W`, `τ(ê) = Q(w)`. -/
abbrev TauW : Type u := pullbackSpace x.bun.Q x.Ψh.τ.obj

/-- `τ(σ̂) = (g, o)` acts on `W` by `g`. -/
abbrev tauG (σ : x.Ψh.MorE) : x.Ψh.Ψ.G := (x.Ψh.τ.mor σ).1

theorem tau_mor_snd (σ : x.Ψh.MorE) : (x.Ψh.τ.mor σ).2 = x.Ψh.τ.obj (x.Ψh.E.src σ) :=
  x.Ψh.τ.src_mor σ

theorem tau_obj_tgt (σ : x.Ψh.MorE) :
    x.Ψh.τ.obj (x.Ψh.E.tgt σ) = x.tauG σ • x.Ψh.τ.obj (x.Ψh.E.src σ) := by
  rw [← x.tau_mor_snd σ]; exact (x.Ψh.τ.tgt_mor σ).symm

/-- **The action of `Ê` on `τ*W`** (p. 936): `σ̂ ∗ (s(σ̂), w) = (t(σ̂), μ_W(τ(σ̂))(w))`. -/
def tauWAction : GroupoidAction x.Ψh.E.toGroupoidStr x.TauW where
  anchor y := (y : x.Ψh.ObjE × x.bun.W).1
  act q := ⟨(x.Ψh.E.tgt (q : x.Ψh.MorE × x.TauW).1,
      x.tauG (q : x.Ψh.MorE × x.TauW).1 • ((q : x.Ψh.MorE × x.TauW).2 : x.Ψh.ObjE × x.bun.W).2),
    by
      obtain ⟨⟨σ, ⟨⟨e, w⟩, hw⟩⟩, hq⟩ := q
      have hw' : x.bun.Q w = x.Ψh.τ.obj e := hw
      have hq' : e = x.Ψh.E.src σ := hq
      change x.bun.Q (x.tauG σ • w) = x.Ψh.τ.obj (x.Ψh.E.tgt σ)
      rw [x.bun.Q_smul, hw', hq', x.tau_obj_tgt]⟩
  anchor_act _ := rfl
  act_unit y := by
    apply Subtype.ext
    change (x.Ψh.E.tgt (x.Ψh.E.unit _), x.tauG (x.Ψh.E.unit _) • _) = _
    rw [x.Ψh.E.tgt_unit]
    refine Prod.ext rfl ?_
    change (x.Ψh.τ.mor (x.Ψh.E.unit _)).1 • _ = _
    rw [x.Ψh.τ.mor_unit]
    exact one_smul _ _
  act_comp ψ γ y h₁ h₂ := by
    apply Subtype.ext
    refine Prod.ext (x.Ψh.E.tgt_comp _ _ h₂) ?_
    change (x.Ψh.τ.mor (x.Ψh.E.comp ψ γ)).1 • _ = (x.Ψh.τ.mor ψ).1 • (x.Ψh.τ.mor γ).1 • _
    rw [x.Ψh.τ.mor_comp _ _ h₂, ← mul_smul]
    rfl

/-- **The groupoid `τ*W`** (p. 936): objects `(ê, w)` with `τ(ê) = Q(w)`, morphisms
`(σ̂, (s(σ̂), w))`, `t(σ̂, w) = (t(σ̂), μ_W(τ(σ̂))(w))`. -/
abbrev tauW : GroupoidStr x.TauW (pullbackSpace x.tauWAction.anchor x.Ψh.E.src) :=
  x.tauWAction.groupoid

/-- **`τ̂ : τ*W → W`**, `(ê, w) ↦ w`, and `τ*Q : τ*W → Ê`, `(ê, w) ↦ ê`. -/
abbrev tauWProj (y : x.TauW) : x.bun.W := (y : x.Ψh.ObjE × x.bun.W).2

/-- The object `Γ̂(ê, w) = (Ψ̂(ê), Γ(w))` of `P*E_B`. -/
def gammaHatObj (y : x.TauW) : (μ.pull P).E :=
  BanFunctor.pullMk (x.Ψh.hat.obj (y : x.Ψh.ObjE × x.bun.W).1) (x.Γ.obj (y : x.Ψh.ObjE × x.bun.W).2)
    (by
      rw [x.bun.P_obj, x.Ψh.obj_comm]
      exact congrArg x.Ψh.Ψ.obj y.2)

@[simp] theorem pullPt_gammaHatObj (y : x.TauW) :
    BanFunctor.pullPt (x.gammaHatObj y) =
      (x.Ψh.hat.obj (y : x.Ψh.ObjE × x.bun.W).1, x.Γ.obj (y : x.Ψh.ObjE × x.bun.W).2) := rfl

/-- `Γ(μ_W(τ(σ̂))(w)) = μ_B(P(Ψ̂(σ̂)))(Γ(w))`. -/
theorem obj_tauG_smul (q : pullbackSpace x.tauWAction.anchor x.Ψh.E.src) :
    x.Γ.obj (x.tauG (q : x.Ψh.MorE × x.TauW).1 •
        ((q : x.Ψh.MorE × x.TauW).2 : x.Ψh.ObjE × x.bun.W).2) =
      μ.act ⟨(P.mor (x.Ψh.hat.mor (q : x.Ψh.MorE × x.TauW).1),
        x.Γ.obj ((q : x.Ψh.MorE × x.TauW).2 : x.Ψh.ObjE × x.bun.W).2), by
          obtain ⟨⟨σ, ⟨⟨e, w⟩, hw⟩⟩, hq⟩ := q
          change μ.P (x.Γ.obj w) = B.toGroupoidStr.src (P.mor (x.Ψh.hat.mor σ))
          rw [P.src_mor, x.Ψh.hat.src_mor, x.bun.P_obj, x.Ψh.obj_comm]
          exact (congrArg x.Ψh.Ψ.obj hw).trans (congrArg _ (congrArg _ hq))⟩ := by
  obtain ⟨⟨σ, ⟨⟨e, w⟩, hw⟩⟩, hq⟩ := q
  have hw' : x.bun.Q w = x.Ψh.τ.obj e := hw
  have hq' : e = x.Ψh.E.src σ := hq
  change x.Γ.obj (x.tauG σ • w) = _
  rw [x.str.obj_smul]
  refine μ.act_congr (Prod.ext ?_ rfl)
  change x.Ψh.Ψ.mor ((x.Ψh.τ.mor σ).1, x.bun.Q w) = P.mor (x.Ψh.hat.mor σ)
  rw [x.Ψh.mor_comm, hw', hq', ← x.tau_mor_snd]

/-- **2021 (19.55), p. 936: the functor `Γ̂ : τ*W → P*E_B`**, `Γ̂(ê, w) = (Ψ̂(ê), Γ(w))`,
`Γ̂(σ̂, w) = (Ψ̂(σ̂), Γ(w))`. -/
def gammaHat : GroupoidFunctor x.tauW (μ.pull P).cat.toGroupoidStr where
  obj := x.gammaHatObj
  mor q := ⟨(x.Ψh.hat.mor (q : x.Ψh.MorE × x.TauW).1, x.gammaHatObj (q : x.Ψh.MorE × x.TauW).2),
    by
      obtain ⟨⟨σ, y⟩, hq⟩ := q
      change x.Ψh.hat.obj (y : x.Ψh.ObjE × x.bun.W).1 = A.toGroupoidStr.src (x.Ψh.hat.mor σ)
      rw [x.Ψh.hat.src_mor]
      exact congrArg _ (hq : _ = _)⟩
  src_mor _ := rfl
  tgt_mor q := by
    apply BanFunctor.pullPt_injective
    change BanFunctor.pullPt ((μ.pull P).act _) = _
    rw [BanFunctor.pull_act]
    change (A.toGroupoidStr.tgt (x.Ψh.hat.mor (q : x.Ψh.MorE × x.TauW).1), _) =
      (x.Ψh.hat.obj (x.Ψh.E.tgt (q : x.Ψh.MorE × x.TauW).1), x.Γ.obj (x.tauG _ • _))
    rw [x.obj_tauG_smul, x.Ψh.hat.tgt_mor]
    rfl
  mor_comp φ ψ h := by
    have h' : x.Ψh.E.src (φ : x.Ψh.MorE × x.TauW).1 = x.Ψh.E.tgt (ψ : x.Ψh.MorE × x.TauW).1 :=
      GroupoidAction.src_eq_tgt_of_eq_act h
    apply Subtype.ext
    change (x.Ψh.hat.mor ((x.tauWAction.morComp φ ψ : x.Ψh.MorE × x.TauW).1),
      x.gammaHatObj ((x.tauWAction.morComp φ ψ : x.Ψh.MorE × x.TauW).2)) =
        ((μ.pull P).morComp _ _ : A.Mor × (μ.pull P).E)
    have h2 : (((⟨(x.Ψh.hat.mor (φ : x.Ψh.MorE × x.TauW).1,
        x.gammaHatObj (φ : x.Ψh.MorE × x.TauW).2), by
          obtain ⟨⟨σ, y⟩, hq⟩ := φ
          change x.Ψh.hat.obj (y : x.Ψh.ObjE × x.bun.W).1 = A.toGroupoidStr.src (x.Ψh.hat.mor σ)
          rw [x.Ψh.hat.src_mor]
          exact congrArg _ (hq : _ = _)⟩ : (μ.pull P).cat.Mor)) : A.Mor × (μ.pull P).E).2 =
        (μ.pull P).act ⟨(x.Ψh.hat.mor (ψ : x.Ψh.MorE × x.TauW).1,
          x.gammaHatObj (ψ : x.Ψh.MorE × x.TauW).2), by
          obtain ⟨⟨σ, y⟩, hq⟩ := ψ
          change x.Ψh.hat.obj (y : x.Ψh.ObjE × x.bun.W).1 = A.toGroupoidStr.src (x.Ψh.hat.mor σ)
          rw [x.Ψh.hat.src_mor]
          exact congrArg _ (hq : _ = _)⟩ := by
      apply BanFunctor.pullPt_injective
      rw [BanFunctor.pull_act]
      have hφ : (φ : x.Ψh.MorE × x.TauW).2 = x.tauWAction.act ψ := h
      change BanFunctor.pullPt (x.gammaHatObj (φ : x.Ψh.MorE × x.TauW).2) = _
      rw [hφ]
      change (x.Ψh.hat.obj (x.Ψh.E.tgt (ψ : x.Ψh.MorE × x.TauW).1), x.Γ.obj (x.tauG _ • _)) = _
      rw [x.obj_tauG_smul, x.Ψh.hat.tgt_mor]
      rfl
    rw [GroupoidAction.morComp_val h, BanFunctor.morComp_val h2]
    exact Prod.ext (x.Ψh.hat.mor_comp _ _ h') rfl
  mor_unit y := by
    apply Subtype.ext
    refine Prod.ext (x.Ψh.hat.mor_unit _) rfl

/-- **`Γ̂` is injective on objects** (Theorem 19.8.6). -/
theorem injective_gammaHat : Injective x.gammaHat.obj := by
  intro y₁ y₂ h
  have h' := congrArg BanFunctor.pullPt h
  simp only [gammaHat, pullPt_gammaHatObj, Prod.mk.injEq] at h'
  exact Subtype.ext (Prod.ext (x.Ψh.injective_hat h'.1) (x.bun.injective_obj h'.2))

/-- **`Γ̂` is faithful** (Theorem 19.8.6). -/
theorem faithful_gammaHat : x.gammaHat.toFunctor.Faithful := by
  refine (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs ht he => ?_
  have hm : x.Ψh.hat.mor (φ : x.Ψh.MorE × x.TauW).1 = x.Ψh.hat.mor (φ' : x.Ψh.MorE × x.TauW).1 :=
    congrArg (fun q : (μ.pull P).cat.Mor => (q : A.Mor × (μ.pull P).E).1) he
  have hs' : (φ : x.Ψh.MorE × x.TauW).2 = (φ' : x.Ψh.MorE × x.TauW).2 := hs
  have ht' : x.tauWAction.act φ = x.tauWAction.act φ' := ht
  have hsE : x.Ψh.E.src (φ : x.Ψh.MorE × x.TauW).1 = x.Ψh.E.src (φ' : x.Ψh.MorE × x.TauW).1 :=
    (φ.2 : _ = _).symm.trans ((congrArg (fun y : x.TauW => (y : x.Ψh.ObjE × x.bun.W).1) hs').trans
      (φ'.2 : _ = _))
  have htE : x.Ψh.E.tgt (φ : x.Ψh.MorE × x.TauW).1 = x.Ψh.E.tgt (φ' : x.Ψh.MorE × x.TauW).1 :=
    congrArg (fun y : x.TauW => (y : x.Ψh.ObjE × x.bun.W).1) ht'
  have hσ := (GroupoidFunctor.faithful_iff _).1 x.Ψh.faithful_hat _ _ hsE htE hm
  exact Subtype.ext (Prod.ext hσ hs')

/-- **`Γ̂` is full** (Theorem 19.8.6). -/
theorem full_gammaHat : x.gammaHat.toFunctor.Full := by
  refine (GroupoidFunctor.full_iff _).2 fun y₁ y₂ ψ hs ht => ?_
  obtain ⟨⟨e₁, w₁⟩, hw₁⟩ := y₁
  obtain ⟨⟨e₂, w₂⟩, hw₂⟩ := y₂
  obtain ⟨⟨φ, v⟩, hψ⟩ := ψ
  have hs' : v = x.gammaHatObj ⟨(e₁, w₁), hw₁⟩ := hs
  subst hs'
  have ht' : (μ.pull P).act ⟨(φ, x.gammaHatObj ⟨(e₁, w₁), hw₁⟩), hψ⟩ =
      x.gammaHatObj ⟨(e₂, w₂), hw₂⟩ := ht
  have ht'' := congrArg BanFunctor.pullPt ht'
  rw [BanFunctor.pull_act] at ht''
  simp only [pullPt_gammaHatObj, Prod.mk.injEq] at ht''
  have hφs : A.toGroupoidStr.src φ = x.Ψh.hat.obj e₁ := hψ.symm
  obtain ⟨σ, hσs, hσt, hσ⟩ :=
    (GroupoidFunctor.full_iff _).1 x.Ψh.full_hat e₁ e₂ φ hφs ht''.1
  have hq : x.tauWAction.anchor ⟨(e₁, w₁), hw₁⟩ = x.Ψh.E.src σ := hσs.symm
  refine ⟨⟨(σ, ⟨(e₁, w₁), hw₁⟩), hq⟩, rfl, ?_, ?_⟩
  · apply Subtype.ext
    refine Prod.ext hσt (x.bun.injective_obj ?_)
    have := x.obj_tauG_smul ⟨(σ, ⟨(e₁, w₁), hw₁⟩), hq⟩
    refine this.trans (Eq.trans ?_ ht''.2)
    refine μ.act_congr (Prod.ext ?_ rfl)
    change P.mor (x.Ψh.hat.mor σ) = P.mor φ
    rw [hσ]
  · exact Subtype.ext (Prod.ext hσ rfl)

/-- **The diagram (19.61) on objects and morphisms**: `P*P_B ∘ Γ̂ = Ψ̂ ∘ τ*Q` and the forgetful
functor `P*E_B → E_B` composed with `Γ̂` is `Γ ∘ τ̂`. -/
theorem gammaHat_comm (y : x.TauW) (q : pullbackSpace x.tauWAction.anchor x.Ψh.E.src) :
    (μ.pull P).proj.obj (x.gammaHat.obj y) = x.Ψh.hat.obj (y : x.Ψh.ObjE × x.bun.W).1 ∧
      (μ.pull P).proj.mor (x.gammaHat.mor q) = x.Ψh.hat.mor (q : x.Ψh.MorE × x.TauW).1 ∧
      (μ.pullToE P).obj (x.gammaHat.obj y) = x.Γ.obj (x.tauWProj y) ∧
      ((μ.pullToE P).mor (x.gammaHat.mor q) : B.Mor × μ.E).1 =
        x.Ψh.Ψ.mor (x.Ψh.τ.mor (q : x.Ψh.MorE × x.TauW).1) :=
  ⟨rfl, rfl, rfl, x.Ψh.mor_comm _⟩

end PullbackUniformizer

/-! ### Definition 19.8.2 -/

/-- **2021 Definition 19.8.2, p. 932 (uniformizer construction for `(P, μ_B)`)**: a set `F̃(β)`
of uniformizers `(Ψ, Ψ̂, Γ)` for the bundle covering pull-back at every object `β`. -/
structure PullbackUniformizerConstruction (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr)
    (μ : B.BanFunctor) : Type (u + 1) where
  /-- The sets `F̃(β)`. -/
  F : ∀ β : B.Obj, Set (PullbackUniformizer P μ β)

namespace PullbackUniformizerConstruction

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} {μ : B.BanFunctor}
  (Ft : PullbackUniformizerConstruction P μ)

/-- **(3) The induced uniformizer construction `F̂` for `P`** (Definition 19.7.7):
`F̂(β) = {(Ψ, Ψ̂) | (Ψ, Ψ̂, Γ) ∈ F̃(β)}`. -/
def hatU : CoveringUniformizerConstruction P := ⟨fun β => (fun x => x.Ψh) '' Ft.F β⟩

/-- **(1) The induced uniformizer construction `F` for `B`** (Definition 19.1.3), induced by
`F̂`. -/
abbrev toUniformizerConstruction : B.UniformizerConstruction := Ft.hatU.toUniformizerConstruction

/-- **(2) The induced strong bundle uniformizers `F̄(β)` for `P_B`** (Definition 19.6.3): the
strong bundle uniformizers `(Ψ, Γ)` at `β` of the members of `F̃(β)`. -/
def barF (β : B.Obj) : Set (StrongBundleUniformizer μ β) :=
  (fun x : PullbackUniformizer P μ β => x.toStrongBundleUniformizer) '' Ft.F β

/-- **2021 Definition 19.8.2, (1)–(3)**: `F̂` and `F̄` both induce `F`. -/
theorem definition_19_8_2 (β : B.Obj) :
    (fun Ψh : CoveringUniformizer P β => Ψh.Ψ) '' Ft.hatU.F β = Ft.toUniformizerConstruction.F β ∧
      (fun Γ : StrongBundleUniformizer μ β => Γ.str.toBase) '' Ft.barF β =
        Ft.toUniformizerConstruction.F β := by
  refine ⟨rfl, ?_⟩
  change _ = (fun Ψh : CoveringUniformizer P β => Ψh.Ψ) '' ((fun x => x.Ψh) '' Ft.F β)
  rw [barF, image_image, image_image]
  rfl

/-- A member of `F̃`: `β` and `(Ψ, Ψ̂, Γ) ∈ F̃(β)`. -/
structure Unif where
  /-- The object `β`. -/
  β : B.Obj
  /-- The uniformizer `(Ψ, Ψ̂, Γ)`. -/
  x : PullbackUniformizer P μ β
  mem : x ∈ Ft.F β

variable {Ft}

/-- The member `(Ψ, Ψ̂)` of `F̂`. -/
def Unif.toHat (x : Ft.Unif) : Ft.hatU.Unif := ⟨x.β, x.x.Ψh, x.x, x.mem, rfl⟩

@[simp] theorem Unif.toHat_Ψh (x : Ft.Unif) : x.toHat.Ψh = x.x.Ψh := rfl

end PullbackUniformizerConstruction

end GroupoidalCategory

end Polyfold
