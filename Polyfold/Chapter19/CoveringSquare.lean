import Polyfold.Chapter19.CoveringPullbackDiagram
import Polyfold.Chapter8.Book
import Polyfold.Chapter10.StrongBundleWeakFibredProductPullback

/-!
# Bundle covering squares and their uniformizers (HWZ 2021 §19.8, pp. 939–947)

2021 Definition 19.8.7 (bundle covering square `𝔈`), Definition 19.8.8 (strong ep-bundle covering
model `K`), Remark 19.8.9, Definition 19.8.10 (uniformizer `Γ̂ : K → 𝔈`), Remark 19.8.11 and
Lemma 19.8.12, pp. 939–947.

A bundle covering square is a finite-to-one covering functor `P : A → B` with functors
`μ_A : A → Ban`, `μ_B : B → Ban` and a natural isomorphism `Θ : μ_A → μ_B ∘ P` (19.62)–(19.64); it
gives the bundle categories `E_A`, `E_B`, the projections `P_A`, `P_B` and the functor
`P̂ : E_A → E_B`, `(α, v̂) ↦ (P(α), Θ_α(v̂))`, `(φ̂, v̂) ↦ (P(φ̂), Θ_{s(φ̂)}(v̂))` (19.69), and the
square (19.70), (19.71) commutes.  The pull-back `(P, μ_B)` of Definition 19.8.1 is the case
`μ_A = μ_B ∘ P`, `Θ = id` (`BundleCoveringSquare.ofPull`).

A strong ep-bundle covering model (19.72) consists of strong bundles `Q̂ : Ŵ → Ê` and
`Q : W → E = G ⋉ O_β` over ep-groupoids and a proper strong bundle covering `Ξ : Ŵ → W` covering
`τ : Ê → E` (Definition 8.5.9).  A uniformizer `Γ̂ : K → 𝔈` at `β` (19.76), (19.77) is such a
model together with uniformizers `Ψ`, `Ψ̂`, `Γ`, `Γ̂` with (1) `(Ψ, Ψ̂)` a uniformizer for `P`,
(2) `(Γ, Ψ)` a strong bundle uniformizer for `P_B`, (3) `(Γ̂, Ψ̂)` one for `P_A` (Remark 19.6.2),
and `P̂ ∘ Γ̂ = Γ ∘ Ξ`.  Lemma 19.8.12: `Γ̂` determines `Ψ̂` (by the zero section), `Ψ` (Lemma
19.7.5) and `Γ = P̂ ∘ Γ̂ ∘ Ξ⁻¹`, and conversely `Γ̂ = P̂⁻¹ ∘ Γ ∘ Ξ` (19.84).

## What is formalized

* `BundleCoveringSquare` (**Definition 19.8.7**), `ThetaE`, `Phat` (19.69), `definition_19_8_7`
  ((19.70), (19.71)); `BundleCoveringSquare.ofPull` (the square of a bundle covering pull-back
  diagram; the witness `reflAbsSquare` for the reflection bundle on `ℤ/2 ⋉ ℝ` and the covering
  `absCovP` is in `CoveringPullbackExamples`).
* `epAction` (the action groupoid of a strong bundle over an ep-groupoid: morphisms `(σ̂, ŵ)`,
  `s = ŵ`, `t = μ̂(σ̂, ŵ)`).
* `StrongEpBundleCoveringModel` (**Definition 19.8.8**); `smul` on `W` (the action of `G` on `W`
  given by `μ`), `Q_smul`, `isStrongBundleMap_smul`, `xiFunctor` (`Ξ` as a functor),
  `xi_mu` (**(19.75)**), `definition_19_8_8`, `remark_19_8_9` (**Remark 19.8.9**).
* `SquareUniformizer` (**Definition 19.8.10**), `toStrongBundleOver`, `toPullbackUniformizer`,
  `definition_19_8_10` ((1)–(3) and (19.77)), `relations_19_82` (**(19.82), (19.83)**).
* `lemma_19_8_12` (**Lemma 19.8.12**) and `formula_19_84` (**(19.84), (19.85)**).

Remark 19.8.11 (applications to stable maps) has no mathematical content to formalize.

## Readings

* Definition 19.8.7: `Θ` is a family of topological linear isomorphisms
  `Θ_α : μ_A(α) → μ_B(P(α))` with (19.64); naturality is stated as
  `Θ_{t(φ̂)}(μ_A(φ̂)(v)) = μ_B(P(φ̂))(Θ_{s(φ̂)}(v))`.  `P` is a finite-to-one covering functor
  (`IsFiniteToOneCovering`).
* Definition 19.8.8 cites "proper covering functor (Definition 8.5.1) with `E = G ⋉ O_β`" while
  Definition 19.8.1 uses proper covering models (Definition 17.8.4): we read Definition 17.8.4
  throughout, so `K` is taken over a proper covering model `τ : Ê → G ⋉ O_β` (its point is
  `o_β`); Definition 8.5.9 is used verbatim for `Ξ` (`IsProperStrongBundleCovering2021`), which
  contains that `τ` is a proper covering functor in the sense of Definition 8.5.1.  This is the
  condition `isProper` of an object of Chapter 11's `SBPC` (Remark 11.6.9); `K` is stated with
  its strong bundles over the ep-groupoids `Ê` and `G ⋉ O_β` directly.
* Definition 19.8.10 (2): the action of `G` on `W` in Definition 19.6.1 is the one given by the
  strong bundle structure `μ` of `Q : W → G ⋉ O` (`g ∗ w = μ((g, Q(w)), w)`), which acts by
  strong bundle maps (`isStrongBundleMap_smul`).  (3) is read as Definition 19.6.1 with the
  base ep-groupoid `Ê` in place of `G ⋉ O` (Remark 19.6.2): `Γ̂` is a fully faithful functor from
  the action groupoid of `Ŵ`, injective on objects, over `Ψ̂`, and a topological linear
  isomorphism on the fibres.
* Lemma 19.8.12, "`Γ̂` determines the other three functors": `Ψ̂ = P_A ∘ Γ̂ ∘ 0` on objects and
  morphisms; every functor `Ψ'` with `P ∘ Ψ̂ = Ψ' ∘ τ` is `Ψ`; `Γ(w) = P̂(Γ̂(ŵ))` for every `ŵ`
  over `w` (`Ξ` is surjective), and `Γ` on morphisms is `(g, w) ↦ (Ψ(g, Q(w)), Γ(w))`.
  "The three latter functors determine `Γ̂`": (19.84) on objects, and `Γ̂` on morphisms is
  `(σ̂, ŵ) ↦ (Ψ̂(σ̂), Γ̂(ŵ))`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace Polyfold

noncomputable section

universe u

open Set Function Topology

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

variable {A B : GroupoidalCategory.{u}}

/-! ### Definition 19.8.7 -/

/-- **2021 Definition 19.8.7, p. 941 (bundle covering square `𝔈`)**: a finite-to-one covering
functor `P : A → B`, functors `μ_A : A → Ban`, `μ_B : B → Ban` and a natural isomorphism
`Θ : μ_A → μ_B ∘ P` (19.62)–(19.64). -/
structure BundleCoveringSquare (A B : GroupoidalCategory.{u}) : Type (u + 1) where
  /-- The finite-to-one covering functor `P : A → B`. -/
  P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr
  isFiniteToOneCovering : IsFiniteToOneCovering P
  /-- `μ_A : A → Ban`. -/
  μA : A.BanFunctor
  /-- `μ_B : B → Ban`. -/
  μB : B.BanFunctor
  /-- (19.63) `Θ_α : μ_A(α) → μ_B(P(α))`. -/
  Θ : ∀ α : A.Obj, μA.P ⁻¹' {α} ≃L[ℝ] μB.P ⁻¹' {P.obj α}
  /-- (19.64) `Θ_{α'} ∘ μ_A(φ̂) = μ_B(P(φ̂)) ∘ Θ_α` for `φ̂ : α → α'`. -/
  Θ_lift : ∀ (φ : A.Mor) (v : μA.P ⁻¹' {A.toGroupoidStr.src φ}),
    (Θ (A.toGroupoidStr.tgt φ) (μA.lift φ v) : μB.E) = μB.act ⟨(P.mor φ, (Θ _ v : μB.E)),
      (show μB.P (Θ _ v : μB.E) = _ from (Θ _ v).2).trans (P.src_mor φ).symm⟩

namespace BundleCoveringSquare

variable (S : BundleCoveringSquare A B)

/-- `Θ` on the total space: `(α, v̂) ↦ Θ_α(v̂)`. -/
def ThetaE (e : S.μA.E) : S.μB.E := S.Θ (S.μA.P e) ⟨e, rfl⟩

theorem ThetaE_eq (α : A.Obj) (v : S.μA.P ⁻¹' {α}) : S.ThetaE v = (S.Θ α v : S.μB.E) := by
  obtain ⟨e, he⟩ := v
  have he' : S.μA.P e = α := he
  subst he'
  rfl

theorem P_ThetaE (e : S.μA.E) : S.μB.P (S.ThetaE e) = S.P.obj (S.μA.P e) :=
  (S.Θ (S.μA.P e) ⟨e, rfl⟩).2

/-- `P̂` on a morphism `(φ̂, v̂)`: `(P(φ̂), Θ_{s(φ̂)}(v̂))`. -/
def PhatMor (q : S.μA.cat.Mor) : S.μB.cat.Mor :=
  ⟨(S.P.mor (q : A.Mor × S.μA.E).1, S.ThetaE (q : A.Mor × S.μA.E).2),
    (S.P_ThetaE _).trans ((congrArg S.P.obj q.2).trans (S.P.src_mor _).symm)⟩

theorem act_PhatMor (q : S.μA.cat.Mor) : S.μB.act (S.PhatMor q) = S.ThetaE (S.μA.act q) := by
  rw [S.ThetaE_eq (A.toGroupoidStr.tgt (q : A.Mor × S.μA.E).1) ⟨_, S.μA.P_act q⟩]
  change _ = (S.Θ _ (S.μA.lift (q : A.Mor × S.μA.E).1 ⟨(q : A.Mor × S.μA.E).2, q.2⟩) : S.μB.E)
  rw [S.Θ_lift]
  exact S.μB.act_congr (Prod.ext rfl
    (S.ThetaE_eq (A.toGroupoidStr.src (q : A.Mor × S.μA.E).1) ⟨_, q.2⟩))

/-- **2021 (19.69): the functor `P̂ : E_A → E_B`**, `(α, v̂) ↦ (P(α), Θ_α(v̂))`,
`(φ̂, v̂) ↦ (P(φ̂), Θ_{s(φ̂)}(v̂))`. -/
def Phat : GroupoidFunctor S.μA.cat.toGroupoidStr S.μB.cat.toGroupoidStr where
  obj := S.ThetaE
  mor := S.PhatMor
  src_mor _ := rfl
  tgt_mor q := S.act_PhatMor q
  mor_comp φ ψ h := by
    have h2 : ((S.PhatMor φ : S.μB.cat.Mor) : B.Mor × S.μB.E).2 = S.μB.act (S.PhatMor ψ) := by
      rw [act_PhatMor]
      exact congrArg S.ThetaE h
    apply Subtype.ext
    change (S.P.mor ((S.μA.morComp φ ψ : A.Mor × S.μA.E).1),
        S.ThetaE ((S.μA.morComp φ ψ : A.Mor × S.μA.E).2)) = (S.μB.morComp _ _ : B.Mor × S.μB.E)
    rw [S.μA.morComp_val h, S.μB.morComp_val h2]
    exact Prod.ext (S.P.mor_comp _ _ (BanFunctor.src_eq_tgt_of_eq_act h)) rfl
  mor_unit e := by
    apply Subtype.ext
    exact Prod.ext ((S.P.mor_unit _).trans (congrArg _ (S.P_ThetaE e).symm)) rfl

/-- **2021 Definition 19.8.7, the square `𝔈` (19.70), (19.71)**: `P_B ∘ P̂ = P ∘ P_A` on objects
and morphisms, and `P̂` is, on the fibre over `α`, the topological linear isomorphism `Θ_α`. -/
theorem definition_19_8_7 :
    (∀ e, S.μB.proj.obj (S.Phat.obj e) = S.P.obj (S.μA.proj.obj e)) ∧
      (∀ q, S.μB.proj.mor (S.Phat.mor q) = S.P.mor (S.μA.proj.mor q)) ∧
      ∀ (α : A.Obj) (v : S.μA.P ⁻¹' {α}), S.Phat.obj v = (S.Θ α v : S.μB.E) :=
  ⟨S.P_ThetaE, fun _ => rfl, S.ThetaE_eq⟩

/-- `P̂` is injective on objects (it is injective on every fibre and covers `P` on the base). -/
theorem ThetaE_injective_fiber {e e' : S.μA.E} (h : S.μA.P e = S.μA.P e')
    (h' : S.ThetaE e = S.ThetaE e') : e = e' := by
  rw [S.ThetaE_eq (S.μA.P e') ⟨e, h⟩, S.ThetaE_eq (S.μA.P e') ⟨e', rfl⟩] at h'
  exact congrArg Subtype.val ((S.Θ _).injective (Subtype.ext h'))

end BundleCoveringSquare

/-! ### The bundle covering square of a bundle covering pull-back diagram -/

/-- **The bundle covering square of `(P, μ_B)`**: `μ_A = μ_B ∘ P` (`μ_B.pull P`) and
`Θ_α : (μ_B ∘ P)(α) = μ_B(P(α))` the identity. -/
def BundleCoveringSquare.ofPull (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr)
    (hP : IsFiniteToOneCovering P) (μ : B.BanFunctor) : BundleCoveringSquare A B where
  P := P
  isFiniteToOneCovering := hP
  μA := μ.pull P
  μB := μ
  Θ := μ.pullFiberCLE P
  Θ_lift φ v := by
    change (BanFunctor.pullPt ((μ.pull P).lift φ v : (μ.pull P).E)).2 = _
    rw [show ((μ.pull P).lift φ v : (μ.pull P).E) = (μ.pull P).act ⟨(φ, v), v.2⟩ from rfl,
      BanFunctor.pull_act]
    exact μ.act_congr rfl

/-! ### Strong bundles over ep-groupoids as groupoid actions -/

section EpAction

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {Pw : W → Obj}
  [∀ x, AddCommGroup (Pw ⁻¹' {x})] [∀ x, Module ℝ (Pw ⁻¹' {x})] {BW : StrongBundle X.PObj Pw}

/-- **The action of `X` on `W`** given by a strong bundle `(W, μ)` over the ep-groupoid `X`
(Definition 8.3.1); its action groupoid has the morphisms `(σ, w)` with `s(σ) = P(w)`,
`s(σ, w) = w`, `t(σ, w) = μ(σ, w)` (p. 942). -/
def epAction (μ : EpStrongBundle X BW) : GroupoidAction X.toGroupoidStr W where
  anchor := Pw
  act := μ.μ
  anchor_act := μ.P_μ
  act_unit w := μ.μ_unit w
  act_comp ψ γ w h₁ h₂ := μ.μ_comp ψ γ w h₁ h₂

end EpAction

/-! ### Definition 19.8.8 -/

section Model

variable {G O : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O] {PO : MPolyfold O}
  {hP : ∀ g : G, PO.IsScSmoothMap PO fun y => g • y}
  {ObjE MorE : Type u} [TopologicalSpace ObjE] [T2Space ObjE] [ParacompactSpace ObjE]
  [TopologicalSpace MorE] [T2Space MorE] [ParacompactSpace MorE] {E : EpGroupoid ObjE MorE}
  {τ : EpFunctor E (actionEpGroupoid hP)}

/-- **2021 Definition 19.8.8, p. 943 (strong ep-bundle covering model `K`)**, (19.72)–(19.74):
over a proper covering model `τ : Ê → E = G ⋉ O_β` (Definition 17.8.4, point `o_β`), strong
bundles `Q : W → E` and `Q̂ : Ŵ → Ê` over the ep-groupoids (Definition 8.3.1) and a proper strong
bundle covering `Ξ : Ŵ → W` covering `τ` (Definition 8.5.9). -/
structure StrongEpBundleCoveringModel (M : ProperCoveringModel τ) : Type (u + 1) where
  /-- The total space `W`. -/
  W : Type u
  [topW : TopologicalSpace W]
  [t2W : T2Space W]
  [paraW : ParacompactSpace W]
  /-- `Q : W → O`. -/
  Q : W → O
  [addW : ∀ o, AddCommGroup (Q ⁻¹' {o})]
  [modW : ∀ o, Module ℝ (Q ⁻¹' {o})]
  /-- The strong bundle `Q`. -/
  BW : StrongBundle PO Q
  /-- The structure `μ` of `Q : W → G ⋉ O` (Definition 8.3.1). -/
  μW : EpStrongBundle (actionEpGroupoid hP) BW
  /-- The total space `Ŵ`. -/
  Wh : Type u
  [topWh : TopologicalSpace Wh]
  [t2Wh : T2Space Wh]
  [paraWh : ParacompactSpace Wh]
  /-- `Q̂ : Ŵ → Ê`. -/
  Qh : Wh → ObjE
  [addWh : ∀ e, AddCommGroup (Qh ⁻¹' {e})]
  [modWh : ∀ e, Module ℝ (Qh ⁻¹' {e})]
  /-- The strong bundle `Q̂`. -/
  BWh : StrongBundle E.PObj Qh
  /-- The structure `μ̂` of `Q̂ : Ŵ → Ê`. -/
  μWh : EpStrongBundle E BWh
  /-- `Ξ : Ŵ → W`. -/
  Ξ : Wh → W
  /-- `Ξ` is a proper strong bundle covering functor covering `τ` (Definition 8.5.9). -/
  isCovering :
    haveI := BW.paracompactSpace_pullback (actionEpGroupoid hP).PMor (actionEpGroupoid hP).src
    haveI := BWh.paracompactSpace_pullback E.PMor E.src
    μWh.IsProperStrongBundleCovering2021 μW τ Ξ

namespace StrongEpBundleCoveringModel

attribute [instance] topW t2W paraW addW modW topWh t2Wh paraWh addWh modWh

variable {M : ProperCoveringModel τ} (K : StrongEpBundleCoveringModel M)

/-- **The action of `G` on `W`**: `g ∗ w = μ((g, Q(w)), w)`. -/
def smul (g : G) (w : K.W) : K.W := K.μW.μ ⟨((g, K.Q w), w), rfl⟩

theorem Q_smul (g : G) (w : K.W) : K.Q (K.smul g w) = g • K.Q w := K.μW.P_μ _

theorem smul_one (w : K.W) : K.smul 1 w = w := K.μW.μ_unit w

theorem smul_mul (g h : G) (w : K.W) : K.smul (g * h) w = K.smul g (K.smul h w) := by
  have := K.μW.μ_comp (g, K.Q (K.smul h w)) (h, K.Q w) w rfl (K.Q_smul h w)
  exact this

/-- `G` acts on `W` through `μ`. -/
instance instMulAction : MulAction G K.W where
  smul := K.smul
  one_smul := K.smul_one
  mul_smul := K.smul_mul

theorem smul_def (g : G) (w : K.W) : g • w = K.μW.μ ⟨((g, K.Q w), w), rfl⟩ := rfl

/-- **`G` acts by strong bundle maps covering its action on `O`**: `w ↦ μ((g, Q(w)), w)` is
`μ` composed with the strong bundle map `w ↦ ((g, Q(w)), w)` into the pull-back. -/
theorem isStrongBundleMap_smul (g : G) :
    K.BW.IsStrongBundleMap K.BW (fun o => g • o) (fun w => g • w) := by
  have := K.BW.paracompactSpace_pullback (actionEpGroupoid hP).PMor (actionEpGroupoid hP).src
  have hl : PO.IsScSmoothMap (actionEpGroupoid hP).PMor fun o => (g, o) := isScSmoothMap_sheet g
  have hΘ : K.BW.IsStrongBundleMap K.BW ((actionEpGroupoid hP).src ∘ fun o => (g, o)) id :=
    StrongBundle.IsStrongBundleMap.id K.BW
  exact K.μW.isStrongBundleMap.comp
    (K.BW.isStrongBundleMap_pullbackPair (actionEpGroupoid hP).isScSmoothMap_src hl hΘ)

/-- `Ξ` on morphisms: `(σ̂, ŵ) ↦ (τ(σ̂), Ξ(ŵ))`. -/
def xiMor (q : pullbackSpace K.Qh E.src) : pullbackSpace K.Q (actionEpGroupoid hP).src :=
  ⟨(τ.mor (q : MorE × K.Wh).1, K.Ξ (q : MorE × K.Wh).2), by
    have := K.BW.paracompactSpace_pullback (actionEpGroupoid hP).PMor (actionEpGroupoid hP).src
    have := K.BWh.paracompactSpace_pullback E.PMor E.src
    change K.Q (K.Ξ _) = (actionEpGroupoid hP).src (τ.mor _)
    rw [K.isCovering.isMap.isStrongBundleMap.covers, τ.src_mor]
    exact congrArg τ.obj q.2⟩

theorem xi_mu' (q : pullbackSpace K.Qh E.src) : K.Ξ (K.μWh.μ q) = K.μW.μ (K.xiMor q) := by
  have := K.BW.paracompactSpace_pullback (actionEpGroupoid hP).PMor (actionEpGroupoid hP).src
  have := K.BWh.paracompactSpace_pullback E.PMor E.src
  obtain ⟨⟨σ, w⟩, hq⟩ := q
  exact K.isCovering.isMap.map_μ σ w hq

/-- **`Ξ` as a functor** of the action groupoids: `ŵ ↦ Ξ(ŵ)`, `(σ̂, ŵ) ↦ (τ(σ̂), Ξ(ŵ))` (p. 943). -/
def xiFunctor : GroupoidFunctor (epAction K.μWh).groupoid (epAction K.μW).groupoid where
  obj := K.Ξ
  mor := K.xiMor
  src_mor _ := rfl
  tgt_mor q := (K.xi_mu' q).symm
  mor_comp φ ψ h := by
    have h' : (φ : MorE × K.Wh).2 = K.μWh.μ ψ := h
    have h2 : ((K.xiMor φ : pullbackSpace K.Q (actionEpGroupoid hP).src) :
        (G × O) × K.W).2 = (epAction K.μW).act (K.xiMor ψ) := by
      change K.Ξ (φ : MorE × K.Wh).2 = K.μW.μ _
      rw [h']
      exact K.xi_mu' ψ
    apply Subtype.ext
    change (τ.mor (((epAction K.μWh).morComp φ ψ : MorE × K.Wh)).1,
        K.Ξ (((epAction K.μWh).morComp φ ψ : MorE × K.Wh)).2) =
      ((epAction K.μW).morComp (K.xiMor φ) (K.xiMor ψ) : (G × O) × K.W)
    rw [GroupoidAction.morComp_val h']
    refine Eq.trans ?_ (GroupoidAction.morComp_val h2).symm
    exact Prod.ext (τ.mor_comp _ _ (GroupoidAction.src_eq_tgt_of_eq_act h')) rfl
  mor_unit w := by
    have := K.BW.paracompactSpace_pullback (actionEpGroupoid hP).PMor (actionEpGroupoid hP).src
    have := K.BWh.paracompactSpace_pullback E.PMor E.src
    apply Subtype.ext
    exact Prod.ext ((τ.mor_unit _).trans
      (congrArg _ (K.isCovering.isMap.isStrongBundleMap.covers w).symm)) rfl

/-- **2021 (19.75), p. 942**: `Ξ(μ̂(σ̂, ŵ)) = μ(τ(σ̂), Ξ(ŵ))`. -/
theorem xi_mu (q : pullbackSpace K.Qh E.src) :
    K.Ξ (K.μWh.μ q) = K.μW.μ ((K.xiFunctor).mor q) := (K.xiFunctor.tgt_mor q).symm

/-- **2021 Definition 19.8.8**: `Q ∘ Ξ = τ ∘ Q̂`, `Ξ` is fibrewise linear, surjective, a local
strong bundle isomorphism, and (19.75). -/
theorem definition_19_8_8 :
    (∀ w, K.Q (K.Ξ w) = τ.obj (K.Qh w)) ∧ Surjective K.Ξ ∧ τ.IsProperCovering ∧
      ∀ q, K.Ξ (K.μWh.μ q) = K.μW.μ ((K.xiFunctor).mor q) := by
  have := K.BW.paracompactSpace_pullback (actionEpGroupoid hP).PMor (actionEpGroupoid hP).src
  have := K.BWh.paracompactSpace_pullback E.PMor E.src
  exact ⟨K.isCovering.isMap.isStrongBundleMap.covers, K.isCovering.surjective,
    K.isCovering.isProperCovering, K.xi_mu⟩

/-- **2021 Remark 19.8.9, p. 943**: compared with Definition 8.5.9, a strong ep-bundle covering
model is a proper strong bundle covering whose base `E` has the special form `G ⋉ O_β`. -/
theorem remark_19_8_9 :
    haveI := K.BW.paracompactSpace_pullback (actionEpGroupoid hP).PMor (actionEpGroupoid hP).src
    haveI := K.BWh.paracompactSpace_pullback E.PMor E.src
    K.μWh.IsProperStrongBundleCovering2021 K.μW τ K.Ξ ∧
      (actionEpGroupoid hP).toGroupoidStr = GroupoidStr.translation G O :=
  ⟨K.isCovering, rfl⟩

end StrongEpBundleCoveringModel

end Model

/-! ### Definition 19.8.10 -/

/-- **2021 Definition 19.8.10, p. 943 (uniformizer `Γ̂ : K → 𝔈` at `β`)**: a strong ep-bundle
covering model `K` (over the proper covering model of `(Ψ, Ψ̂)`) and four uniformizers
`Ψ : E → B`, `Ψ̂ : Ê → A`, `Γ : W → E_B`, `Γ̂ : Ŵ → E_A` (19.76) such that (1) `(Ψ, Ψ̂)` is a
uniformizer for `P` (Definition 19.7.3; `Ψh`), (2) `(Γ, Ψ)` is a strong bundle uniformizer for
`P_B` (Definition 19.6.1), (3) `(Γ̂, Ψ̂)` is one for `P_A` (Remark 19.6.2), and (19.77)
`P̂ ∘ Γ̂ = Γ ∘ Ξ`. -/
structure SquareUniformizer (S : BundleCoveringSquare A B) (β : B.Obj) : Type (u + 1) where
  /-- (1) The uniformizer `(Ψ, Ψ̂)` for `P`. -/
  Ψh : CoveringUniformizer S.P β
  /-- The strong ep-bundle covering model `K`. -/
  K : StrongEpBundleCoveringModel Ψh.model
  /-- (2) The functor `Γ : W → E_B`. -/
  Γ : GroupoidFunctor (GroupoidStr.translation Ψh.Ψ.G K.W) S.μB.cat.toGroupoidStr
  injective_Γ : Injective Γ.obj
  full_Γ : Γ.toFunctor.Full
  faithful_Γ : Γ.toFunctor.Faithful
  /-- (2) (19.78) `P_B ∘ Γ = Ψ ∘ Q` on objects. -/
  P_obj : ∀ w, S.μB.P (Γ.obj w) = Ψh.Ψ.obj (K.Q w)
  /-- (2) (19.79) `P_B ∘ Γ = Ψ ∘ Q` on morphisms. -/
  mor_fst : ∀ (g : Ψh.Ψ.G) (w : K.W), ((Γ.mor (g, w) : S.μB.cat.Mor) : B.Mor × S.μB.E).1 =
    Ψh.Ψ.mor (g, K.Q w)
  /-- (2) `A : Q⁻¹(e) → P_B⁻¹(Ψ(e))`. -/
  fiberCLE : ∀ o, K.Q ⁻¹' {o} ≃L[ℝ] S.μB.P ⁻¹' {Ψh.Ψ.obj o}
  fiberCLE_apply : ∀ o (v : K.Q ⁻¹' {o}), (fiberCLE o v : S.μB.E) = Γ.obj v
  /-- (3) The functor `Γ̂ : Ŵ → E_A`. -/
  Γh : GroupoidFunctor (epAction K.μWh).groupoid S.μA.cat.toGroupoidStr
  injective_Γh : Injective Γh.obj
  full_Γh : Γh.toFunctor.Full
  faithful_Γh : Γh.toFunctor.Faithful
  /-- (3) (19.80) `P_A ∘ Γ̂ = Ψ̂ ∘ Q̂` on objects. -/
  PA_obj : ∀ w, S.μA.P (Γh.obj w) = Ψh.hat.obj (K.Qh w)
  /-- (3) (19.81) `P_A ∘ Γ̂ = Ψ̂ ∘ Q̂` on morphisms. -/
  PA_mor : ∀ q, ((Γh.mor q : S.μA.cat.Mor) : A.Mor × S.μA.E).1 =
    Ψh.hat.mor (q : Ψh.MorE × K.Wh).1
  /-- (3) `Â : Q̂⁻¹(ê) → P_A⁻¹(Ψ̂(ê))`. -/
  fiberCLEh : ∀ e, K.Qh ⁻¹' {e} ≃L[ℝ] S.μA.P ⁻¹' {Ψh.hat.obj e}
  fiberCLEh_apply : ∀ e (v : K.Qh ⁻¹' {e}), (fiberCLEh e v : S.μA.E) = Γh.obj v
  /-- (19.77) `P̂ ∘ Γ̂ = Γ ∘ Ξ` on objects. -/
  comm_obj : ∀ w, S.Phat.obj (Γh.obj w) = Γ.obj (K.Ξ w)

namespace SquareUniformizer

variable {S : BundleCoveringSquare A B} {β : B.Obj} (x : SquareUniformizer S β)

/-- **(2) `(Γ, Ψ)` as a strong bundle uniformizer over `Ψ`** (Definition 19.6.1), with the action
of `G` on `W` given by `μ`. -/
def toStrongBundleOver : StrongBundleOver S.μB x.Ψh.Ψ where
  W := x.K.W
  Q := x.K.Q
  bundle := x.K.BW
  Q_smul := x.K.Q_smul
  isStrongBundleMap_smul := x.K.isStrongBundleMap_smul
  functor := x.Γ
  injective_obj := x.injective_Γ
  full := x.full_Γ
  faithful := x.faithful_Γ
  P_obj := x.P_obj
  mor_fst := x.mor_fst
  fiberCLE := x.fiberCLE
  fiberCLE_apply := x.fiberCLE_apply

/-- **`(Ψ, Ψ̂, Γ)` is a uniformizer for the bundle covering pull-back `(P, μ_B)`**
(Definition 19.8.1). -/
def toPullbackUniformizer : PullbackUniformizer S.P S.μB β := ⟨x.Ψh, x.toStrongBundleOver⟩

/-- `Γ̂` on morphisms: `Γ̂(σ̂, ŵ) = (Ψ̂(σ̂), Γ̂(ŵ))` (19.81). -/
theorem Γh_mor_val (q : pullbackSpace x.K.Qh x.Ψh.E.src) :
    ((x.Γh.mor q : S.μA.cat.Mor) : A.Mor × S.μA.E) =
      (x.Ψh.hat.mor (q : x.Ψh.MorE × x.K.Wh).1, x.Γh.obj (q : x.Ψh.MorE × x.K.Wh).2) :=
  Prod.ext (x.PA_mor q) (x.Γh.src_mor q)

/-- `Γ` on morphisms: `Γ(g, w) = (Ψ(g, Q(w)), Γ(w))` (19.79). -/
theorem Γ_mor_val (g : x.Ψh.Ψ.G) (w : x.K.W) :
    ((x.Γ.mor (g, w) : S.μB.cat.Mor) : B.Mor × S.μB.E) = (x.Ψh.Ψ.mor (g, x.K.Q w), x.Γ.obj w) :=
  Prod.ext (x.mor_fst g w) (x.Γ.src_mor (g, w))

/-- **(19.77) on morphisms**: `P̂(Γ̂(σ̂, ŵ)) = Γ(τ(σ̂), Ξ(ŵ))`. -/
theorem comm_mor (q : pullbackSpace x.K.Qh x.Ψh.E.src) :
    S.Phat.mor (x.Γh.mor q) = x.Γ.mor ((x.Ψh.τ.mor (q : x.Ψh.MorE × x.K.Wh).1).1,
      x.K.Ξ (q : x.Ψh.MorE × x.K.Wh).2) := by
  apply Subtype.ext
  change (S.P.mor ((x.Γh.mor q : S.μA.cat.Mor) : A.Mor × S.μA.E).1,
    S.ThetaE ((x.Γh.mor q : S.μA.cat.Mor) : A.Mor × S.μA.E).2) = _
  rw [x.Γh_mor_val, x.Γ_mor_val]
  have hq : (x.Ψh.τ.mor (q : x.Ψh.MorE × x.K.Wh).1).2 =
      x.K.Q (x.K.Ξ (q : x.Ψh.MorE × x.K.Wh).2) := by
    have := x.K.BW.paracompactSpace_pullback (actionEpGroupoid x.Ψh.Ψ.smooth_smul).PMor
      (actionEpGroupoid x.Ψh.Ψ.smooth_smul).src
    have := x.K.BWh.paracompactSpace_pullback x.Ψh.E.PMor x.Ψh.E.src
    rw [x.K.isCovering.isMap.isStrongBundleMap.covers]
    exact (x.Ψh.τ.src_mor _).trans (congrArg x.Ψh.τ.obj q.2.symm)
  refine Prod.ext ?_ (x.comm_obj _)
  rw [x.Ψh.mor_comm, ← hq]

/-- **2021 Definition 19.8.10, (1)–(3) and (19.77)**: `(Ψ, Ψ̂)` is a uniformizer for `P` at `β`,
`(Ψ, Ψ̂, Γ)` a uniformizer for `(P, μ_B)` (so `(Γ, Ψ)` is a strong bundle uniformizer for `P_B`),
`Γ̂` is injective on objects, fully faithful, over `Ψ̂` and fibrewise a topological linear
isomorphism, and the diagram (19.77) commutes on objects and morphisms. -/
theorem definition_19_8_10 :
    x.Ψh.Ψ.obj x.Ψh.model.pt = β ∧
      (x.toPullbackUniformizer.toStrongBundleUniformizer.str.toBase = x.Ψh.Ψ) ∧
      (Injective x.Γh.obj ∧ x.Γh.toFunctor.Full ∧ x.Γh.toFunctor.Faithful) ∧
      (∀ w, S.μA.P (x.Γh.obj w) = x.Ψh.hat.obj (x.K.Qh w)) ∧
      (∀ w, S.Phat.obj (x.Γh.obj w) = x.Γ.obj (x.K.Ξ w)) ∧
      ∀ q, S.Phat.mor (x.Γh.mor q) = x.Γ.mor ((x.Ψh.τ.mor (q : x.Ψh.MorE × x.K.Wh).1).1,
        x.K.Ξ (q : x.Ψh.MorE × x.K.Wh).2) :=
  ⟨x.Ψh.obj_pt, rfl, ⟨x.injective_Γh, x.full_Γh, x.faithful_Γh⟩, x.PA_obj, x.comm_obj, x.comm_mor⟩

/-- **2021 (19.82), (19.83), p. 946**: `P ∘ Ψ̂ = Ψ ∘ τ` on objects and morphisms,
`Θ_{Ψ̂(ê)} ∘ Â = A ∘ Ξ` and `Q ∘ Ξ = τ ∘ Q̂`. -/
theorem relations_19_82 :
    (∀ e, S.P.obj (x.Ψh.hat.obj e) = x.Ψh.Ψ.obj (x.Ψh.τ.obj e)) ∧
      (∀ σ, S.P.mor (x.Ψh.hat.mor σ) = x.Ψh.Ψ.mor (x.Ψh.τ.mor σ)) ∧
      (∀ w, (S.Θ _ (x.fiberCLEh (x.K.Qh w) ⟨w, rfl⟩) : S.μB.E) = x.Γ.obj (x.K.Ξ w)) ∧
      ∀ w, x.K.Q (x.K.Ξ w) = x.Ψh.τ.obj (x.K.Qh w) := by
  have := x.K.BW.paracompactSpace_pullback (actionEpGroupoid x.Ψh.Ψ.smooth_smul).PMor
    (actionEpGroupoid x.Ψh.Ψ.smooth_smul).src
  have := x.K.BWh.paracompactSpace_pullback x.Ψh.E.PMor x.Ψh.E.src
  refine ⟨x.Ψh.obj_comm, x.Ψh.mor_comm, fun w => ?_, x.K.isCovering.isMap.isStrongBundleMap.covers⟩
  rw [← S.ThetaE_eq, x.fiberCLEh_apply]
  exact x.comm_obj w

/-! ### Lemma 19.8.12 -/

/-- The zero `0_ê` of the fibre `Q̂⁻¹(ê)`. -/
def zeroH (e : x.Ψh.ObjE) : x.K.Wh := ((0 : x.K.Qh ⁻¹' {e}) : x.K.Wh)

theorem Qh_zeroH (e : x.Ψh.ObjE) : x.K.Qh (x.zeroH e) = e := (0 : x.K.Qh ⁻¹' {e}).2

/-- **2021 Lemma 19.8.12, p. 946**: (i) `Γ̂` determines `Ψ̂`: `Ψ̂(ê) = P_A(Γ̂(0_ê))` and
`Ψ̂(σ̂) = P_A(Γ̂(σ̂, 0_{s(σ̂)}))`; (ii) `Ψ` is the only functor `Ψ'` with `P ∘ Ψ̂ = Ψ' ∘ τ`
(Lemma 19.7.5); (iii) `Γ = P̂ ∘ Γ̂ ∘ Ξ⁻¹`: `Γ(w) = P̂(Γ̂(ŵ))` for every `ŵ` with `Ξ(ŵ) = w`, such
`ŵ` exist, and `Γ(g, w) = (Ψ(g, Q(w)), Γ(w))`; (iv) conversely `Γ̂` is determined by `Ψ̂`, `Γ`
and `Ξ`: `Γ̂(ŵ) = Θ_{Ψ̂(Q̂(ŵ))}⁻¹(Γ(Ξ(ŵ)))` (19.84) and `Γ̂(σ̂, ŵ) = (Ψ̂(σ̂), Γ̂(ŵ))`. -/
theorem lemma_19_8_12 :
    ((∀ e, x.Ψh.hat.obj e = S.μA.P (x.Γh.obj (x.zeroH e))) ∧
      ∀ σ, x.Ψh.hat.mor σ = ((x.Γh.mor ⟨(σ, x.zeroH (x.Ψh.E.src σ)), x.Qh_zeroH _⟩ :
        S.μA.cat.Mor) : A.Mor × S.μA.E).1) ∧
    (∀ Ψ' : GroupoidFunctor (GroupoidStr.translation x.Ψh.Ψ.G x.Ψh.Ψ.O) B.toGroupoidStr,
      (∀ e, S.P.obj (x.Ψh.hat.obj e) = Ψ'.obj (x.Ψh.τ.obj e)) →
      (∀ σ, S.P.mor (x.Ψh.hat.mor σ) = Ψ'.mor (x.Ψh.τ.mor σ)) → Ψ' = x.Ψh.Ψ.functor) ∧
    ((∀ w, x.Γ.obj (x.K.Ξ w) = S.Phat.obj (x.Γh.obj w)) ∧ Surjective x.K.Ξ ∧
      ∀ g w, ((x.Γ.mor (g, w) : S.μB.cat.Mor) : B.Mor × S.μB.E) =
        (x.Ψh.Ψ.mor (g, x.K.Q w), x.Γ.obj w)) ∧
    ((∀ w, ∃ h : S.μB.P (x.Γ.obj (x.K.Ξ w)) = S.P.obj (x.Ψh.hat.obj (x.K.Qh w)),
      x.Γh.obj w = ((S.Θ (x.Ψh.hat.obj (x.K.Qh w))).symm ⟨x.Γ.obj (x.K.Ξ w), h⟩ : S.μA.E)) ∧
      ∀ q, ((x.Γh.mor q : S.μA.cat.Mor) : A.Mor × S.μA.E) =
        (x.Ψh.hat.mor (q : x.Ψh.MorE × x.K.Wh).1, x.Γh.obj (q : x.Ψh.MorE × x.K.Wh).2)) := by
  have := x.K.BW.paracompactSpace_pullback (actionEpGroupoid x.Ψh.Ψ.smooth_smul).PMor
    (actionEpGroupoid x.Ψh.Ψ.smooth_smul).src
  have := x.K.BWh.paracompactSpace_pullback x.Ψh.E.PMor x.Ψh.E.src
  refine ⟨⟨fun e => ?_, fun σ => (x.PA_mor ⟨(σ, x.zeroH (x.Ψh.E.src σ)), x.Qh_zeroH _⟩).symm⟩,
    fun Ψ' h h' => x.Ψh.remark_19_7_6 Ψ' h h',
    ⟨fun w => (x.comm_obj w).symm, x.K.isCovering.surjective, x.Γ_mor_val⟩,
    ⟨fun w => ?_, x.Γh_mor_val⟩⟩
  · rw [x.PA_obj, x.Qh_zeroH]
  · have hw : S.μA.P (x.Γh.obj w) = x.Ψh.hat.obj (x.K.Qh w) := x.PA_obj w
    have e1 : (S.Θ (x.Ψh.hat.obj (x.K.Qh w)) ⟨x.Γh.obj w, hw⟩ : S.μB.E) = x.Γ.obj (x.K.Ξ w) :=
      (S.ThetaE_eq _ ⟨_, hw⟩).symm.trans (x.comm_obj w)
    refine ⟨e1 ▸ (S.Θ _ ⟨x.Γh.obj w, hw⟩).2, ?_⟩
    have e2 : (⟨x.Γ.obj (x.K.Ξ w), e1 ▸ (S.Θ _ ⟨x.Γh.obj w, hw⟩).2⟩ :
        S.μB.P ⁻¹' {S.P.obj (x.Ψh.hat.obj (x.K.Qh w))}) = S.Θ _ ⟨x.Γh.obj w, hw⟩ :=
      Subtype.ext e1.symm
    rw [e2, ContinuousLinearEquiv.symm_apply_apply]

/-- **2021 (19.84), (19.85), p. 947**: `P̂(Γ̂(ŵ)) = Γ(Ξ(ŵ))`, i.e.
`(P(Ψ̂(ê)), Θ_{Ψ̂(ê)}(Â(ŵ))) = (Ψ(τ(ê)), A(Ξ(ŵ)))` with `ê = Q̂(ŵ)`. -/
theorem formula_19_84 (w : x.K.Wh) :
    S.μB.P (S.Phat.obj (x.Γh.obj w)) = x.Ψh.Ψ.obj (x.Ψh.τ.obj (x.K.Qh w)) ∧
      S.Phat.obj (x.Γh.obj w) = x.Γ.obj (x.K.Ξ w) := by
  refine ⟨?_, x.comm_obj w⟩
  change S.μB.P (S.ThetaE (x.Γh.obj w)) = _
  rw [S.P_ThetaE, x.PA_obj, x.Ψh.obj_comm]

end SquareUniformizer

end GroupoidalCategory

end

end Polyfold
