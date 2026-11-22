import Polyfold.Chapter18.LinearizationTransport
import Polyfold.Chapter18.ModelTransfer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, pp. 844–845: **(18.1), Definition 18.1.3, Definition 18.1.4, (18.2) and `φ_*`**.

# The linearization of a section functor at a solution object

## The text, paraphrased

At an object `α` with `f(α) = 0`, take `Ψ̄ ∈ F̄(α)` covering `Ψ`, `Ψ(q₀) = α`, and put
`f'(α)([α, Ψ, h]) = (α, Ψ̄(q₀)(f'_Ψ̄(q₀) h))` (18.1); it does not depend on `Ψ̄`
(Definition 18.1.3: the linearization of `f` at the solution object `α`).  At a smooth object,
`Lin(f, α)` is the set of the `f'_s(α)[α, Ψ, h] = (α, Ψ̄(q₀)((f_Ψ̄ − s)'(q₀) h))` for local
sc⁺-sections `s` with `s(q₀) = f_Ψ̄(q₀)` (Definition 18.1.4); at a zero it contains `f'(α)`.
For `φ : α → α'` and `f(α) = 0`, `f(α') = 0` and `φ̂ ∘ f'(α) = f'(α') ∘ Tφ` (18.2); `φ_*(L) =
φ̂ ∘ L ∘ Tφ⁻¹` maps `Lin(f, α)` to `Lin(f, α')`, with `(φ'φ)_* = φ'_* φ_*` and `(1_α)_* = Id`.

## What is formalized

* `VectorBundle.fiberCast`, `VectorBundle.morFiber φ hs ht : μ(α) ≃L[ℝ] μ(α')` (the text's
  `φ̂ = μ(φ)` between the fibres over `α = s(φ)` and `α' = t(φ)`), with `act_objMk_morFiber`,
  `morFiber_unit`, `morFiber_comp`.
* `SectionFunctor.toFun_eq_zero_of_mor`: `f(α) = 0` gives `f(α') = 0` along `φ : α → α'`.
* `StrongPolyfoldBundleConstruction.sectionLin hf α h0 hΨ x hx : T_αC →ₗ[ℝ] μ(α)`: the right
  side of (18.1) for one `Ψ̄ ∈ F̄(α)` and the level-`1` point `x` with `Ψ(x) = α`, through the
  chart `S_Ψ : T_αC ≃L T_xO` of Proposition 17.2.4; `objMk_sectionLin` is (18.1).
  `sectionLin_indep`: it does not depend on `(Ψ̄, x)` (the transition law
  `linZeroAt_transTangent` at `(x, 1_α, x')`, with `μ(1_α) = 1`).
* **`linearization hf α h0 hne`** (Definition 18.1.3), through a chosen `Ψ̄ ∈ F̄(α)`;
  **`definition_18_1_3`**: it is `sectionLin` for every `Ψ̄ ∈ F̄(α)`; `equation_18_1`.
* **`equation_18_2`**: `μ(φ)(f'(α) e) = f'(α')(Tφ e)` in `E`; `equation_18_2_comp`:
  `φ̂ ∘ f'(α) = f'(α') ∘ Tφ`.
* `linPush φ hs ht L = φ̂ ∘ L ∘ Tφ⁻¹` (`φ_*`), `linPush_unit`, `linPush_comp`,
  `linPush_linearization` (`φ_* f'(α) = f'(α')`).
* **`linSet`** (Definition 18.1.4): the operators `(f_Ψ̄ + s)'(q₀)` read through `S_Ψ` and
  `Ψ̄(q₀)`, for `Ψ̄ ∈ F̄(α)` and sc⁺-sections `s` with `(f_Ψ̄ + s)(q₀) = 0`;
  `linearization_mem_linSet`: `f'(α) ∈ Lin(f, α)` at a zero.

## Readings

* The text's `f − s` with `s(q₀) = f_Ψ̄(q₀)` is `f + s` with `(f + s)(q₀) = 0` (`sectionAdd`), as
  in Part I's `ChartPoint.linSet`; the sections `s` are global sc⁺-sections of `K → O`.
* `T_αC` carries its linear structure only for `α ∈ C¹` with `F(α) ≠ ∅` (`Fact (S.TangentObj α)`,
  Chapter 17), so `f'(α)` and `Lin(f, α)` are stated for such `α`, at level `1` (where Part I's
  `f'(q₀)` is defined); the text states Definition 18.1.4 at smooth objects.
* The linearization uses only that the representatives are sc-smooth
  (`IsScSmoothSectionFunctor`, implied by Definition 18.1.1).
* `Ψ̄(q₀) : K_{q₀} → μ(α)` is the fibre isomorphism `Ψ̄.fiber q₀`, followed by the identification
  `μ(Ψ(q₀)) = μ(α)` (`fiberCast`).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor

variable {C : GCT.{u}} (V : C.VectorBundle)

/-! ### The fibre maps `φ̂ = μ(φ)` -/

/-- The identification `μ(α) = μ(β)` for `α = β`. -/
def fiberCast {α β : C.Obj} (h : α = β) : V.V α ≃L[ℝ] V.V β :=
  h ▸ ContinuousLinearEquiv.refl ℝ (V.V α)

theorem objMk_fiberCast {α β : C.Obj} (h : α = β) (v : V.V α) :
    V.objMk β (V.fiberCast h v) = V.objMk α v := by
  subst h; rfl

/-- **`φ̂ = μ(φ) : μ(α) → μ(α')`** for `φ : α → α'` (2021 p. 845). -/
def morFiber (φ : C.Mor) {α α' : C.Obj} (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') : V.V α ≃L[ℝ] V.V α' :=
  (V.fiberCast hs.symm).trans ((V.map φ).trans (V.fiberCast ht))

variable {V}

theorem act_objMk_morFiber (φ : C.Mor) {α α' : C.Obj} (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (v : V.V α)
    (h : V.base (V.objMk α v) = C.toGroupoidStr.src φ) :
    V.act φ (V.objMk α v) h = V.objMk α' (V.morFiber φ hs ht v) := by
  subst hs ht; rfl

/-- `μ(1_α) = 1`. -/
theorem morFiber_unit (α : C.Obj) :
    V.morFiber (C.toGroupoidStr.unit α) (C.toGroupoidStr.src_unit α)
      (C.toGroupoidStr.tgt_unit α) = ContinuousLinearEquiv.refl ℝ _ := by
  refine ContinuousLinearEquiv.ext (funext fun v => ?_)
  refine objMk_eq_iff.1 ?_
  rw [← act_objMk_morFiber _ _ _ v (C.toGroupoidStr.src_unit α).symm]
  exact act_unit' _ _

/-- `μ(ψ ∘ φ) = μ(ψ) ∘ μ(φ)`. -/
theorem morFiber_comp {α α' α'' : C.Obj} (φ ψ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hs' : C.toGroupoidStr.src ψ = α')
    (ht' : C.toGroupoidStr.tgt ψ = α'') :
    V.morFiber (C.toGroupoidStr.comp ψ φ)
        ((C.toGroupoidStr.src_comp ψ φ (hs'.trans ht.symm)).trans hs)
        ((C.toGroupoidStr.tgt_comp ψ φ (hs'.trans ht.symm)).trans ht') =
      (V.morFiber φ hs ht).trans (V.morFiber ψ hs' ht') := by
  refine ContinuousLinearEquiv.ext (funext fun v => ?_)
  refine objMk_eq_iff.1 ?_
  have h1 : V.base (V.objMk α v) = C.toGroupoidStr.src (C.toGroupoidStr.comp ψ φ) :=
    ((C.toGroupoidStr.src_comp ψ φ (hs'.trans ht.symm)).trans hs).symm
  rw [ContinuousLinearEquiv.trans_apply]
  exact (act_objMk_morFiber _ _ _ v h1).symm.trans ((act_comp' ψ φ (hs'.trans ht.symm) _ h1).trans
    ((act_congr rfl (act_objMk_morFiber φ hs ht v hs.symm) _ hs'.symm).trans
      (act_objMk_morFiber ψ hs' ht' _ hs'.symm)))

end GCT.VectorBundle

namespace GCT.VectorBundle.SectionFunctor

variable {C : GCT.{u}} {V : C.VectorBundle} (f : V.SectionFunctor)

/-- **`f(α) = 0` implies `f(α') = 0`** along a morphism `φ : α → α'` (2021 p. 845). -/
theorem toFun_eq_zero_of_mor {φ : C.Mor} {α α' : C.Obj} (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (h0 : f.toFun α = V.objMk α 0) :
    f.toFun α' = V.objMk α' 0 := by
  rw [f.toFun_eq_act hs ht ((f.base_toFun α).trans hs.symm), V.act_congr rfl h0 _ hs.symm,
    V.act_objMk_zero hs, ht]

end GCT.VectorBundle.SectionFunctor

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-- **The chart `S_{Ψ'}` of `Tφ`**: `S_{Ψ'}(Tφ e) = Tσ(S_Ψ e)` for `σ` of `(q, φ, q')`,
`Ψ(q) = α`, `Ψ'(q') = α'` (2021 (17.31), read in the charts of Proposition 17.2.4). -/
theorem tangentChartCLE_tangentMorCLE {α α' : C.Obj} [hα : Fact (S.TangentObj α)]
    [hα' : Fact (S.TangentObj α')] (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (Ψ Ψ' : S.Unif) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) (x' : Ψ'.1.P.Level 1)
    (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α') (e : S.TangentSpaceAt α) :
    S.tangentChartCLE α' Ψ' x' hx' (S.tangentMorCLE φ hs ht e) =
      S.transTangent (S.morTr (Ψ.1.P.levelVal 1 x) φ (Ψ'.1.P.levelVal 1 x') hx hs hx' ht) rfl rfl
        (S.tangentChartCLE α Ψ x hx e) := by
  refine Subtype.ext ?_
  have e1 : S.tangentChartCLE α' Ψ' x' hx' (S.tangentMorCLE φ hs ht e) =
      S.transTangent (S.unitTr _ _ (obj_refPoint hα'.out) hx') rfl rfl
        (S.transTangent (S.morTr _ φ _ (obj_refPoint hα.out) hs (obj_refPoint hα'.out) ht) rfl rfl
          (S.refChartCLE α e)) :=
    congrArg (S.transTangent (S.unitTr _ _ (obj_refPoint hα'.out) hx') rfl rfl)
      (ContinuousLinearEquiv.apply_symm_apply _ _)
  have e2 : S.tangentChartCLE α Ψ x hx e =
      S.transTangent (S.unitTr _ _ (obj_refPoint hα.out) hx) rfl rfl (S.refChartCLE α e) := rfl
  rw [e1, e2]
  erw [transTangent_apply, transTangent_apply, transTangent_apply, transTangent_apply]
  have hh := levelVal_tangentProj_of_mem (S.refChartCLE α e).2
  rw [← transMap_comp' (S.unitTr _ _ (obj_refPoint hα'.out) hx')
      (S.morTr _ φ _ (obj_refPoint hα.out) hs (obj_refPoint hα'.out) ht)
      (S.morTr _ φ (Ψ'.1.P.levelVal 1 x') (obj_refPoint hα.out) hs hx' ht)
      rfl (GroupoidStr.unit_comp_of_eq ht).symm rfl rfl hh,
    ← transMap_comp' (S.morTr (Ψ.1.P.levelVal 1 x) φ (Ψ'.1.P.levelVal 1 x') hx hs hx' ht)
      (S.unitTr _ _ (obj_refPoint hα.out) hx)
      (S.morTr _ φ (Ψ'.1.P.levelVal 1 x') (obj_refPoint hα.out) hs hx' ht)
      rfl (GroupoidStr.comp_unit_of_eq hs).symm rfl rfl hh]

end GCT.PolyfoldConstruction

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor StrongBundleUniformizerConstruction
  StrongBundleUniformizerData PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S) {f : V.SectionFunctor}

/-- **A zero of `f` is a zero of every representative**: `f(α) = 0` and `Ψ(q) = α` give
`f_Ψ̄(q) = 0`. -/
theorem isZeroAt_localRep {α : C.Obj} (h0 : f.toFun α = V.objMk α 0)
    {Ψ : V.StrongBundleUniformizerData} {q : Ψ.base.O} (hq : Ψ.base.obj q = α) :
    IsZeroAt Ψ.p (Ψ.localRep f) q := by
  subst hq
  refine (Ψ.localRep_eq_iff f q _).2 ?_
  rw [Ψ.obj_of_eq (proj_fiberZero Ψ.p q), h0]
  have e : (⟨fiberZero Ψ.p q, proj_fiberZero Ψ.p q⟩ : Ψ.p ⁻¹' {q}) = 0 := rfl
  rw [e, map_zero]

/-- The linearization `f'(α)` read through one strong bundle uniformizer `Ψ̄ ∈ F̄(α)` and the
level-`1` point `x` with `Ψ(x) = α`: `e ↦ Ψ̄(x)(f'_Ψ̄(x)(S_Ψ e))` (the right side of (18.1)). -/
def sectionLin (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)]
    (h0 : f.toFun α = V.objMk α 0) {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α)
    (x : Ψ.1.base.P.Level 1) (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) :
    S.TangentSpaceAt α →ₗ[ℝ] V.V α :=
  (V.fiberCast hx).toLinearMap ∘ₗ (Ψ.1.fiber (Ψ.1.base.P.levelVal 1 x)).toLinearMap ∘ₗ
    Ψ.1.B.linZeroAt (hf α Ψ.1 hΨ) x (isZeroAt_localRep h0 hx) ∘ₗ
      (S.tangentChartCLE α (Q.baseUnif Ψ) x hx).toLinearMap

/-- **(18.1)** for one `Ψ̄`: `(α, f'(α) e) = Ψ̄(f'_Ψ̄(x)(S_Ψ e))`. -/
theorem objMk_sectionLin (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] (h0 : f.toFun α = V.objMk α 0) {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α)
    (x : Ψ.1.base.P.Level 1) (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α)
    (e : S.TangentSpaceAt α) :
    V.objMk α (Q.sectionLin hf α h0 hΨ x hx e) =
      Ψ.1.obj (Ψ.1.B.linZeroAt (hf α Ψ.1 hΨ) x (isZeroAt_localRep h0 hx)
        (S.tangentChartCLE α (Q.baseUnif Ψ) x hx e)) := by
  set k := Ψ.1.B.linZeroAt (hf α Ψ.1 hΨ) x (isZeroAt_localRep h0 hx)
    (S.tangentChartCLE α (Q.baseUnif Ψ) x hx e)
  rw [Ψ.1.obj_of_eq k.2]
  exact V.objMk_fiberCast hx _

/-- **The definition does not depend on the choice of `Ψ̄`** (2021 p. 845): `sectionLin` is the
same for any two strong bundle uniformizers in `F̄(α)` and their points over `α`. -/
theorem sectionLin_indep (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] (h0 : f.toFun α = V.objMk α 0) {Ψ₁ Ψ₂ : Q.Unif}
    (hΨ₁ : Ψ₁.1 ∈ Q.F α) (hΨ₂ : Ψ₂.1 ∈ Q.F α) (x₁ : Ψ₁.1.base.P.Level 1)
    (hx₁ : Ψ₁.1.base.obj (Ψ₁.1.base.P.levelVal 1 x₁) = α) (x₂ : Ψ₂.1.base.P.Level 1)
    (hx₂ : Ψ₂.1.base.obj (Ψ₂.1.base.P.levelVal 1 x₂) = α) :
    Q.sectionLin hf α h0 hΨ₁ x₁ hx₁ = Q.sectionLin hf α h0 hΨ₂ x₂ hx₂ := by
  refine LinearMap.ext fun e => objMk_eq_iff.1 ?_
  rw [objMk_sectionLin, objMk_sectionLin]
  set a := S.unitTr (Ψ := Q.baseUnif Ψ₁) (Ψ' := Q.baseUnif Ψ₂) _ _ hx₁ hx₂
  have hT : S.tangentChartCLE α (Q.baseUnif Ψ₂) x₂ hx₂ e =
      S.transTangent a rfl rfl (S.tangentChartCLE α (Q.baseUnif Ψ₁) x₁ hx₁ e) := by
    have h := tangentChart_symm_trans (S := S) (Q.baseUnif Ψ₁) (Q.base_mem α _ hΨ₁) x₁ hx₁
      (Q.baseUnif Ψ₂) (Q.base_mem α _ hΨ₂) x₂ hx₂ (S.tangentChartCLE α (Q.baseUnif Ψ₁) x₁ hx₁ e)
    rw [coe_tangentChartCLE α (Q.baseUnif Ψ₁) (Q.base_mem α _ hΨ₁) x₁ hx₁,
      Equiv.symm_apply_apply] at h
    rw [coe_tangentChartCLE α (Q.baseUnif Ψ₁) (Q.base_mem α _ hΨ₁) x₁ hx₁,
      coe_tangentChartCLE α (Q.baseUnif Ψ₂) (Q.base_mem α _ hΨ₂) x₂ hx₂]
    exact h
  rw [hT, Q.linZeroAt_transTangent f Ψ₁ Ψ₂ a (hf α Ψ₁.1 hΨ₁) (hf α Ψ₂.1 hΨ₂) rfl rfl
    (isZeroAt_localRep h0 hx₁) (isZeroAt_localRep h0 hx₂)]
  erw [obj_transAct]
  exact (act_unit' _ _).symm

/-! ### Definition 18.1.3 -/

/-- A chosen strong bundle uniformizer `Ψ̄_α ∈ F̄(α)`. -/
def refBundleUnif {α : C.Obj} (hne : (Q.F α).Nonempty) : Q.Unif := ⟨hne.some, α, hne.some_mem⟩

theorem refBundleUnif_mem {α : C.Obj} (hne : (Q.F α).Nonempty) :
    (Q.refBundleUnif hne).1 ∈ Q.F α := hne.some_mem

/-- The level-`1` point `q₀` of `Ψ̄_α` with `Ψ(q₀) = α` (for `α ∈ C¹`). -/
def refBundlePoint {α : C.Obj} (hα : S.HasRegularity 1 α) (hne : (Q.F α).Nonempty) :
    (Q.refBundleUnif hne).1.base.P.Level 1 :=
  (Q.refBundleUnif hne).1.base.P.levelMk 1
    (pointOf (Ψ := Q.baseUnif (Q.refBundleUnif hne)) (Q.base_mem α _ (Q.refBundleUnif_mem hne)))
    (pointOf_mem (Ψ := Q.baseUnif (Q.refBundleUnif hne)) (Q.base_mem α _ (Q.refBundleUnif_mem hne))
      hα)

theorem obj_refBundlePoint {α : C.Obj} (hα : S.HasRegularity 1 α) (hne : (Q.F α).Nonempty) :
    (Q.refBundleUnif hne).1.base.obj
      ((Q.refBundleUnif hne).1.base.P.levelVal 1 (Q.refBundlePoint hα hne)) = α := by
  rw [refBundlePoint, MPolyfold.levelVal_levelMk]
  exact obj_pointOf (Ψ := Q.baseUnif (Q.refBundleUnif hne)) _

variable (f) in
/-- **Definition 18.1.3, p. 845: the linearization `f'(α) : T_αC → E_α` of the section functor
`f` at the solution object `α`**, defined by (18.1) through a chosen `Ψ̄ ∈ F̄(α)`; by
`definition_18_1_3` it is the right side of (18.1) for every `Ψ̄ ∈ F̄(α)`. -/
def linearization (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [hα : Fact (S.TangentObj α)]
    (h0 : f.toFun α = V.objMk α 0) (hne : (Q.F α).Nonempty) : S.TangentSpaceAt α →ₗ[ℝ] V.V α :=
  Q.sectionLin hf α h0 (Q.refBundleUnif_mem hne) (Q.refBundlePoint hα.out.1 hne)
    (Q.obj_refBundlePoint hα.out.1 hne)

/-- **Definition 18.1.3 (well-definedness)**: "the definition does not depend on the choice of
`Ψ̄`" (p. 845): for every `Ψ̄ ∈ F̄(α)` and its point `x` over `α`, (18.1) through `Ψ̄` gives
`f'(α)`. -/
theorem definition_18_1_3 (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] (h0 : f.toFun α = V.objMk α 0) (hne : (Q.F α).Nonempty)
    {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) :
    Q.sectionLin hf α h0 hΨ x hx = Q.linearization f hf α h0 hne :=
  Q.sectionLin_indep hf α h0 hΨ _ x hx _ _

/-- **(18.1)**: `f'(α)([α, Ψ, h]) = (α, Ψ̄(q₀)(f'_Ψ̄(q₀) h))`, for every `Ψ̄ ∈ F̄(α)`; the tangent
vector `[α, Ψ, h]` is `S_Ψ⁻¹ h`. -/
theorem equation_18_1 (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)]
    (h0 : f.toFun α = V.objMk α 0) (hne : (Q.F α).Nonempty) {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α)
    (x : Ψ.1.base.P.Level 1) (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α)
    (h : Ψ.1.base.P.tangentFiber x) :
    V.objMk α (Q.linearization f hf α h0 hne ((S.tangentChartCLE α (Q.baseUnif Ψ) x hx).symm h)) =
      Ψ.1.obj (Ψ.1.B.linZeroAt (hf α Ψ.1 hΨ) x (isZeroAt_localRep h0 hx) h) := by
  rw [← Q.definition_18_1_3 hf α h0 hne hΨ x hx, objMk_sectionLin,
    ContinuousLinearEquiv.apply_symm_apply]

/-! ### (18.2) and `φ_*` -/

/-- **(18.2)**, p. 845: for `φ : α → α'` and `f(α) = 0` (so `f(α') = 0`,
`SectionFunctor.toFun_eq_zero_of_mor`), `μ(φ)(f'(α) e) = f'(α')(Tφ e)`. -/
theorem equation_18_2 (hf : Q.IsScSmoothSectionFunctor f) {α α' : C.Obj}
    [Fact (S.TangentObj α)] [Fact (S.TangentObj α')] (φ : C.Mor)
    (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
    (h0 : f.toFun α = V.objMk α 0) (hne : (Q.F α).Nonempty) (hne' : (Q.F α').Nonempty)
    (e : S.TangentSpaceAt α) :
    V.act φ (V.objMk α (Q.linearization f hf α h0 hne e)) hs.symm =
      V.objMk α' (Q.linearization f hf α' (f.toFun_eq_zero_of_mor hs ht h0) hne'
        (S.tangentMorCLE φ hs ht e)) := by
  have h0' := f.toFun_eq_zero_of_mor hs ht h0
  set Ψ := Q.refBundleUnif hne
  set Ψ' := Q.refBundleUnif hne'
  have hx := Q.obj_refBundlePoint (Fact.out : S.TangentObj α).1 hne
  have hx' := Q.obj_refBundlePoint (Fact.out : S.TangentObj α').1 hne'
  set x := Q.refBundlePoint (Fact.out : S.TangentObj α).1 hne
  set x' := Q.refBundlePoint (Fact.out : S.TangentObj α').1 hne'
  have e1 : V.objMk α (Q.linearization f hf α h0 hne e) =
      Ψ.1.obj (Ψ.1.B.linZeroAt (hf α Ψ.1 (Q.refBundleUnif_mem hne)) x (isZeroAt_localRep h0 hx)
        (S.tangentChartCLE α (Q.baseUnif Ψ) x hx e)) := by
    rw [← Q.definition_18_1_3 hf α h0 hne (Q.refBundleUnif_mem hne) x hx, objMk_sectionLin]
  have e2 : V.objMk α' (Q.linearization f hf α' h0' hne' (S.tangentMorCLE φ hs ht e)) =
      Ψ'.1.obj (Ψ'.1.B.linZeroAt (hf α' Ψ'.1 (Q.refBundleUnif_mem hne')) x'
        (isZeroAt_localRep h0' hx') (S.tangentChartCLE α' (Q.baseUnif Ψ') x' hx'
          (S.tangentMorCLE φ hs ht e))) := by
    rw [← Q.definition_18_1_3 hf α' h0' hne' (Q.refBundleUnif_mem hne') x' hx',
      objMk_sectionLin]
  rw [e2, tangentChartCLE_tangentMorCLE φ hs ht (Q.baseUnif Ψ) (Q.baseUnif Ψ') x hx x' hx' e,
    Q.linZeroAt_transTangent f Ψ Ψ' _ (hf α Ψ.1 (Q.refBundleUnif_mem hne))
      (hf α' Ψ'.1 (Q.refBundleUnif_mem hne')) rfl rfl (isZeroAt_localRep h0 hx)
      (isZeroAt_localRep h0' hx')]
  erw [obj_transAct]
  exact act_congr rfl e1 _ _

/-- **(18.2)**, operator form: `φ̂ ∘ f'(α) = f'(α') ∘ Tφ`. -/
theorem equation_18_2_comp (hf : Q.IsScSmoothSectionFunctor f) {α α' : C.Obj}
    [Fact (S.TangentObj α)] [Fact (S.TangentObj α')] (φ : C.Mor)
    (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
    (h0 : f.toFun α = V.objMk α 0) (hne : (Q.F α).Nonempty) (hne' : (Q.F α').Nonempty) :
    (V.morFiber φ hs ht).toLinearMap ∘ₗ Q.linearization f hf α h0 hne =
      Q.linearization f hf α' (f.toFun_eq_zero_of_mor hs ht h0) hne' ∘ₗ
        (S.tangentMorCLE φ hs ht).toLinearMap := by
  refine LinearMap.ext fun e => objMk_eq_iff.1 ?_
  change V.objMk α' (V.morFiber φ hs ht (Q.linearization f hf α h0 hne e)) = _
  rw [← act_objMk_morFiber φ hs ht _ hs.symm]
  exact Q.equation_18_2 hf φ hs ht h0 hne hne' e

/-- **`φ_*(L) = φ̂ ∘ L ∘ Tφ⁻¹`** (2021 p. 845), on all linear maps `T_αC → μ(α)`. -/
def linPush {α α' : C.Obj} [Fact (S.TangentObj α)] [Fact (S.TangentObj α')] (φ : C.Mor)
    (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
    (L : S.TangentSpaceAt α →ₗ[ℝ] V.V α) : S.TangentSpaceAt α' →ₗ[ℝ] V.V α' :=
  (V.morFiber φ hs ht).toLinearMap ∘ₗ L ∘ₗ (S.tangentMorCLE φ hs ht).symm.toLinearMap

/-- `φ_* f'(α) = f'(α')`, a form of (18.2). -/
theorem linPush_linearization (hf : Q.IsScSmoothSectionFunctor f) {α α' : C.Obj}
    [Fact (S.TangentObj α)] [Fact (S.TangentObj α')] (φ : C.Mor)
    (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
    (h0 : f.toFun α = V.objMk α 0) (hne : (Q.F α).Nonempty) (hne' : (Q.F α').Nonempty) :
    linPush φ hs ht (Q.linearization f hf α h0 hne) =
      Q.linearization f hf α' (f.toFun_eq_zero_of_mor hs ht h0) hne' := by
  refine LinearMap.ext fun e => ?_
  have h := congrArg (fun L => L ((S.tangentMorCLE φ hs ht).symm e))
    (Q.equation_18_2_comp hf φ hs ht h0 hne hne')
  simp only [LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearEquiv.apply_symm_apply] at h
  exact h

omit Q in
/-- **`(1_α)_* = Id`** (2021 p. 845). -/
theorem linPush_unit {α : C.Obj} [Fact (S.TangentObj α)] (L : S.TangentSpaceAt α →ₗ[ℝ] V.V α) :
    linPush (V := V) (S := S) (C.toGroupoidStr.unit α) (C.toGroupoidStr.src_unit α)
      (C.toGroupoidStr.tgt_unit α) L = L := by
  refine LinearMap.ext fun e => ?_
  simp only [linPush, LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv,
    morFiber_unit, (proposition_17_2_5 (S := S)).2.1 α, ContinuousLinearEquiv.refl_symm,
    ContinuousLinearEquiv.coe_refl', id]

omit Q in
/-- **`(φ' ∘ φ)_* = φ'_* ∘ φ_*`** (2021 p. 845). -/
theorem linPush_comp {α α' α'' : C.Obj} [Fact (S.TangentObj α)] [Fact (S.TangentObj α')]
    [Fact (S.TangentObj α'')] (φ ψ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hs' : C.toGroupoidStr.src ψ = α')
    (ht' : C.toGroupoidStr.tgt ψ = α'') (L : S.TangentSpaceAt α →ₗ[ℝ] V.V α) :
    linPush (V := V) (S := S) (C.toGroupoidStr.comp ψ φ)
        ((C.toGroupoidStr.src_comp ψ φ (hs'.trans ht.symm)).trans hs)
        ((C.toGroupoidStr.tgt_comp ψ φ (hs'.trans ht.symm)).trans ht') L =
      linPush ψ hs' ht' (linPush φ hs ht L) := by
  refine LinearMap.ext fun e => ?_
  simp only [linPush, LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv,
    morFiber_comp φ ψ hs ht hs' ht', (proposition_17_2_5 (S := S)).2.2 α α' α'' φ ψ hs ht hs' ht',
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_trans_apply]

/-! ### Definition 18.1.4 -/

variable (f) in
/-- **Definition 18.1.4, p. 845: the set `Lin(f, α)` of linearizations at `α`**: the operators
`e ↦ Ψ̄(q₀)((f_Ψ̄ + s)'(q₀)(S_Ψ e))` for `Ψ̄ ∈ F̄(α)`, `Ψ(q₀) = α`, and sc⁺-sections `s` of
`K → O` with `(f_Ψ̄ + s)(q₀) = 0` (the text's `f − s` with `s(q₀) = f_Ψ̄(q₀)`, see the module
docstring). -/
def linSet (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)] :
    Set (S.TangentSpaceAt α →ₗ[ℝ] V.V α) :=
  {L | ∃ (Ψ : Q.Unif) (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) (s : Ψ.1.base.O → Ψ.1.K)
    (hs : Ψ.1.B.IsScPlusSection s)
    (h0 : IsZeroAt Ψ.1.p (sectionAdd Ψ.1.p (Ψ.1.localRep f) s) (Ψ.1.base.P.levelVal 1 x)),
    L = (V.fiberCast hx).toLinearMap ∘ₗ (Ψ.1.fiber (Ψ.1.base.P.levelVal 1 x)).toLinearMap ∘ₗ
      Ψ.1.B.linZeroAt ((hf α Ψ.1 hΨ).sectionAdd hs) x h0 ∘ₗ
        (S.tangentChartCLE α (Q.baseUnif Ψ) x hx).toLinearMap}

/-- **At a zero, `f'(α) ∈ Lin(f, α)`** (2021 p. 845, after Definition 18.1.4), with `s = 0`. -/
theorem linearization_mem_linSet (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [hα : Fact (S.TangentObj α)] (h0 : f.toFun α = V.objMk α 0) (hne : (Q.F α).Nonempty) :
    Q.linearization f hf α h0 hne ∈ Q.linSet f hf α := by
  set Ψ := Q.refBundleUnif hne
  have hx := Q.obj_refBundlePoint hα.out.1 hne
  have he := sectionAdd_fiberZero (Ψ.1.isSection_localRep f)
  have h0' : IsZeroAt Ψ.1.p (sectionAdd Ψ.1.p (Ψ.1.localRep f) (fiberZero Ψ.1.p))
      (Ψ.1.base.P.levelVal 1 (Q.refBundlePoint hα.out.1 hne)) := by
    rw [he]; exact isZeroAt_localRep h0 hx
  refine ⟨Ψ, Q.refBundleUnif_mem hne, _, hx, fiberZero Ψ.1.p,
    StrongBundle.isScPlusSection_fiberZero, h0', ?_⟩
  rw [← Ψ.1.B.linZeroAt_congr he.symm (hf α Ψ.1 (Q.refBundleUnif_mem hne))
    ((hf α Ψ.1 (Q.refBundleUnif_mem hne)).sectionAdd StrongBundle.isScPlusSection_fiberZero) _
    (isZeroAt_localRep h0 hx) h0']
  rfl

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
