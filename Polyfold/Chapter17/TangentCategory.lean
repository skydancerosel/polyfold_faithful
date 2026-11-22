import Polyfold.Chapter17.TangentVectors
import Polyfold.Chapter17.LevelOneCategory
import Polyfold.Chapter17.PolyfoldConstructionExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.2 (pp. 770–773): **Definition 17.2.6**, **Lemma 17.2.7**, **Remark 17.2.8**, the projection
functor `P : TC → C¹` ((17.33), (17.34)), the tangent uniformizer `TΨ` ((17.35)–(17.40)),
**Lemma 17.2.9** and **Lemma 17.2.10**.  Numbers and pages are the 2021 text's.

# The tangent category `TC` of a polyfold `C = (C, F, M)`

## The text, paraphrased

(**Definition 17.2.6**, p. 770) The tangent category `TC` has as objects the tangent vectors
`[α, Ψ, h] ∈ T_αC`, `α ∈ C¹`, and as morphisms the tuples `([α, Ψ, h], φ, Tφ([α, Ψ, h]))` with
`s(φ) = α`; `s` and `t` are the first and last entries.  Every morphism is invertible and between
two objects there are finitely many morphisms.  (**Lemma 17.2.7**) `TC` is a groupoidal category.
(**Remark 17.2.8**) Equivalently: objects `(α, e)`, `e ∈ μ_C(α)`, and morphisms `(φ, e)`,
`e ∈ μ_C(s(φ))`, `s(φ, e) = (s(φ), e)`, `t(φ, e) = (t(φ), Tφ(e))`.  (pp. 771–772) `P : TC → C¹`,
`P([α, Ψ, h]) = α`, `P(h̄, φ, h̄') = φ` is a functor (17.34).  For `Ψ ∈ F(α)` the tangent
uniformizer `TΨ : TO → TC` is `TΨ(h) = [Ψ(τ(h)), Ψ', Tσ(h)]` (17.36), `Ψ' ∈ F(Ψ(τ(h)))` and `σ` of
`(τ(h), 1, q') ∈ M(Ψ, Ψ')`; (**Lemma 17.2.9**) it does not depend on `Ψ'`.  On morphisms
`TΨ(g, h) = (TΨ(h), Ψ(g, q), T(Ψ(g, q))TΨ(h))` (17.39), and "the obvious identity"
`TΨ(g ∗ h) = T(Ψ(g, q))(TΨ(h))` gives (17.40).  (**Lemma 17.2.10**) `TΨ : G ⋉ TO → TC` is a
well-defined functor.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `TangentCatObj` (the objects), `TangentCatMor` (the morphisms), `tangentCatGroupoid` (the
  groupoid), `tangentCategory : GroupoidalCategory.{max u 1}` and **`lemma_17_2_7`**.
* **Definition 17.2.6**: `tangentCatObjEquiv : TangentCatObj ≃ Σ α, T_αC` (the objects are the
  tangent vectors), `tangentCatMorEquiv` (the morphisms are the pairs `(h̄, φ)` with `s(φ) = α`,
  the third entry being determined), **`definition_17_2_6`** (`t(h̄, φ, ·) = Tφ(h̄)`).
* **Remark 17.2.8**: `remarkMorEquiv : TangentCatMor ≃ Σ φ, μ_C(s(φ))`, **`remark_17_2_8`**.
* `tangentCatProj : TC → C¹` (17.33), (17.34), a `GroupoidFunctor` into `regSub 1`;
  `surjective_tangentCatProj_obj`.
* `tangentUnifObj` (`TΨ` on objects, (17.36)), **`lemma_17_2_9`** (independence of `Ψ'`),
  `tangentUnifObj_spec` ((17.36) for every choice of `Ψ'`).
* The action `g ∗ h = T(g ∗ ·)(h)` of `G` on `TO`
  (`GroupoidalCategory.Uniformizer.tangentMulAction`), `tangentTranslation Ψ` (`G ⋉ TO`),
  `tangentUnifMor` ((17.39)), `transMap_hat_of_continuous`, **`lemma_17_2_10_of_continuous`**
  and `tangentUnifFunctor` (`TΨ : G ⋉ TO → TC` for continuous `Ψ̂`), `lemma_17_2_10_mor` (the
  laws of Lemma 17.2.10 that hold for every `Ψ`); the witness `reflectionTangentUnifFunctor`,
  `reflection_lemma_17_2_10`.

## Readings

* `TC` is built in the universe `max u 1` of `TO`: an object is `α` with `T_αC ≠ ∅` and a vector
  of the reference fibre `T_{q_α}O_α` of Proposition 17.2.4 (`S_{Ψ_α}` identifies it with
  `T_αC`, `tangentCatObjEquiv`); the text's `T_αC` lives one universe higher, since its tuples
  contain uniformizers.  A morphism is its source and `φ` with `s(φ) = α`, the target `Tφ(h̄)`
  being determined.  We read "`α` varies over `C¹`" as `α ∈ C¹` with `F(α) ≠ ∅` (`TangentObj`),
  which for `HasUniformizers` is `α ∈ C¹` (`tangentObj_iff`).
* "Let `C` be a polyfold" is read to include `F(β) ≠ ∅` for every `β` (`HasUniformizers`):
  (17.36) picks `Ψ' ∈ F(Ψ(τ(h)))`.
* `G ⋉ TO` is read as the translation groupoid of `ULift G` acting through `g ∗ h = T(g ∗ ·)(h)`
  (the lift only matches universes).
* Lemma 17.2.10 rests on "the obvious identity" `TΨ(g ∗ h) = T(Ψ(g, q))(TΨ(h))`, that is,
  `σ = (g ∗ ·)` near `q` for the `σ` of `Ψ̂(g, q) ∈ M(Ψ, Ψ)`.  We prove it when `Ψ̂` is continuous
  (`transMap_hat_of_continuous`), the hypothesis under which Lemma 17.1.9 holds
  (`lemma_17_1_9_of_continuous`); the remaining functor laws hold for every `Ψ`
  (`lemma_17_2_10_mor`).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

/-! ### The action of `G` on `TO` -/

namespace GroupoidalCategory.Uniformizer

variable {D : GroupoidalCategory.{u}} (Ψ : D.Uniformizer)

theorem tangentMap_congr_fun {f f' : Ψ.O → Ψ.O} (h : f = f') (hf : Ψ.P.IsScSmoothMap Ψ.P f)
    (hf' : Ψ.P.IsScSmoothMap Ψ.P f') : MPolyfold.tangentMap hf = MPolyfold.tangentMap hf' := by
  subst h; rfl

/-- **The action `g ∗ h = T(g ∗ ·)(h)` of `G` on `TO`** (2021 p. 773, `G ⋉ TO`). -/
instance tangentMulAction : MulAction Ψ.G Ψ.P.TangentSpace where
  smul g k := MPolyfold.tangentMap (Ψ.smooth_smul g) k
  one_smul k := by
    change MPolyfold.tangentMap (Ψ.smooth_smul 1) k = k
    rw [tangentMap_congr_fun Ψ (funext (one_smul Ψ.G)) (Ψ.smooth_smul 1)
      MPolyfold.isScSmoothMap_id, MPolyfold.tangentMap_id]
    rfl
  mul_smul g g' k := by
    change MPolyfold.tangentMap (Ψ.smooth_smul (g * g')) k =
      MPolyfold.tangentMap (Ψ.smooth_smul g) (MPolyfold.tangentMap (Ψ.smooth_smul g') k)
    rw [tangentMap_congr_fun Ψ (funext (mul_smul g g')) (Ψ.smooth_smul (g * g'))
      ((Ψ.smooth_smul g).comp (Ψ.smooth_smul g')), MPolyfold.tangentMap_comp]
    rfl

theorem tangent_smul_def (g : Ψ.G) (k : Ψ.P.TangentSpace) :
    g • k = MPolyfold.tangentMap (Ψ.smooth_smul g) k := rfl

theorem levelVal_tangentProj_smul (g : Ψ.G) (k : Ψ.P.TangentSpace) :
    Ψ.P.levelVal 1 (Ψ.P.tangentProj (g • k)) = g • Ψ.P.levelVal 1 (Ψ.P.tangentProj k) :=
  MPolyfold.levelVal_tangentProj_tangentMap _ k

end GroupoidalCategory.Uniformizer

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-! ### Two- and three-fold composites of the maps `Tσ` -/

/-- `Tσ_a ∘ Tσ_b = Tσ_{a'} ∘ Tσ_{b'}` near `s(b)` when `a ∘ b` and `a' ∘ b'` have the same
entries. -/
theorem transMap_transMap_eq {Ψ Ψ' Ψ'' Ψ₂ : S.Unif} (a : S.Tr Ψ' Ψ'') (b : S.Tr Ψ Ψ')
    (a' : S.Tr Ψ₂ Ψ'') (b' : S.Tr Ψ Ψ₂) (hs : a.src = b.tgt) (hs' : a'.src = b'.tgt)
    (h₁ : b.src = b'.src)
    (h₂ : C.toGroupoidStr.comp a.mor b.mor = C.toGroupoidStr.comp a'.mor b'.mor)
    (h₃ : a.tgt = a'.tgt) {h : Ψ.1.P.TangentSpace}
    (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = b.src) :
    S.transMap a (S.transMap b h) = S.transMap a' (S.transMap b' h) :=
  (transMap_comp a b (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt hs) hs hh).symm.trans
    (transMap_comp' a' b' _ h₁ h₂ h₃ hs' (hh.trans h₁))

/-- `Tσ_a ∘ Tσ_b = id` near `s(b)` when `a ∘ b` is a unit. -/
theorem transMap_transMap_eq_self {Ψ Ψ' : S.Unif} (a : S.Tr Ψ' Ψ) (b : S.Tr Ψ Ψ')
    (hs : a.src = b.tgt)
    (h₂ : C.toGroupoidStr.comp a.mor b.mor = C.toGroupoidStr.unit (Ψ.1.obj b.src))
    (h₃ : a.tgt = b.src) {h : Ψ.1.P.TangentSpace}
    (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = b.src) :
    S.transMap a (S.transMap b h) = h :=
  (transMap_comp' a b (S.unitTr b.src b.src rfl rfl) rfl h₂.symm h₃.symm hs hh).symm.trans
    (transMap_unitTr_self b.src rfl hh)

/-- `Tσ_a ∘ Tσ_b ∘ Tσ_c = Tσ_{a'} ∘ Tσ_{b'}` near `s(c)` when `a ∘ b ∘ c` and `a' ∘ b'` have the
same entries. -/
theorem transMap_three_eq {Ψ Ψ' Ψ'' Ψ''' Ψ₂ : S.Unif} (a : S.Tr Ψ'' Ψ''') (b : S.Tr Ψ' Ψ'')
    (c : S.Tr Ψ Ψ') (a' : S.Tr Ψ₂ Ψ''') (b' : S.Tr Ψ Ψ₂) (hab : a.src = b.tgt)
    (hbc : b.src = c.tgt) (hs' : a'.src = b'.tgt) (h₁ : c.src = b'.src)
    (h₂ : C.toGroupoidStr.comp (C.toGroupoidStr.comp a.mor b.mor) c.mor =
      C.toGroupoidStr.comp a'.mor b'.mor)
    (h₃ : a.tgt = a'.tgt) {h : Ψ.1.P.TangentSpace}
    (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = c.src) :
    S.transMap a (S.transMap b (S.transMap c h)) = S.transMap a' (S.transMap b' h) :=
  (transMap_comp a b (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt hab) hab
    ((base_transMap c hh).trans hbc.symm)).symm.trans
    (transMap_transMap_eq _ c a' b' hbc hs' h₁ h₂ h₃ hh)

/-- `Tσ_a ∘ Tσ_b ∘ Tσ_c = id` near `s(c)` when `a ∘ b ∘ c` is a unit. -/
theorem transMap_three_eq_self {Ψ Ψ' Ψ'' : S.Unif} (a : S.Tr Ψ'' Ψ) (b : S.Tr Ψ' Ψ'')
    (c : S.Tr Ψ Ψ') (hab : a.src = b.tgt) (hbc : b.src = c.tgt)
    (h₂ : C.toGroupoidStr.comp (C.toGroupoidStr.comp a.mor b.mor) c.mor =
      C.toGroupoidStr.unit (Ψ.1.obj c.src))
    (h₃ : a.tgt = c.src) {h : Ψ.1.P.TangentSpace}
    (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = c.src) :
    S.transMap a (S.transMap b (S.transMap c h)) = h :=
  (transMap_comp a b (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt hab) hab
    ((base_transMap c hh).trans hbc.symm)).symm.trans
    (transMap_transMap_eq_self _ c hbc h₂ h₃ hh)

/-! ### Reference points and the elements between them -/

theorem TangentObj.of_eq {α β : C.Obj} (h : α = β) (hα : S.TangentObj α) : S.TangentObj β :=
  h ▸ hα

/-- For `HasUniformizers`, `T_αC ≠ ∅` iff `α ∈ C¹`. -/
theorem tangentObj_iff (hU : S.HasUniformizers) (α : C.Obj) :
    S.TangentObj α ↔ α ∈ S.regSet 1 :=
  ⟨fun h => h.1, fun h => ⟨h, hU α⟩⟩

variable (S) in
/-- The reference point `q_α ∈ O_α` of Proposition 17.2.4. -/
abbrev refQ {α : C.Obj} (hα : S.TangentObj α) : (S.refUnif hα).1.O :=
  (S.refUnif hα).1.P.levelVal 1 (S.refPoint hα)

variable (S) in
/-- `(q_α, φ, q_{α'}) ∈ M(Ψ_α, Ψ_{α'})` for `φ : α → α'`. -/
abbrev refTr {α α' : C.Obj} (hα : S.TangentObj α) (hα' : S.TangentObj α') (φ : C.Mor)
    (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α') :
    S.Tr (S.refUnif hα) (S.refUnif hα') :=
  S.morTr (S.refQ hα) φ (S.refQ hα') (obj_refPoint hα) hs (obj_refPoint hα') ht

variable (S) in
/-- `(q_α, 1_β, q_β) ∈ M(Ψ_α, Ψ_β)` for `α = β`. -/
abbrev refUnitTr {α β : C.Obj} (hα : S.TangentObj α) (hβ : S.TangentObj β) (h : α = β) :
    S.Tr (S.refUnif hα) (S.refUnif hβ) :=
  S.unitTr (S.refQ hα) (S.refQ hβ) ((obj_refPoint hα).trans h) (obj_refPoint hβ)

/-! ### Definition 17.2.6: objects and morphisms -/

variable (S) in
/-- **The objects of the tangent category `TC`** (2021 Definition 17.2.6, p. 770): `α` with
`T_αC ≠ ∅` and a vector of the reference fibre `T_{q_α}O_α`, which `S_{Ψ_α}` identifies with
`T_αC` (`tangentCatObjEquiv`). -/
structure TangentCatObj : Type (max u 1) where
  /-- The object `α = P(h̄)` of `C¹`. -/
  base : C.Obj
  isObj : S.TangentObj base
  /-- `S_{Ψ_α}(h̄)`. -/
  vec : (S.refUnif isObj).1.P.tangentFiber (S.refPoint isObj)

/-- Two objects of `TC` over equal objects of `C` are equal if `Tσ` of `(q_α, 1, q_β)` maps the
one vector to the other. -/
theorem TangentCatObj.ext_of {e e' : S.TangentCatObj} (h : e.base = e'.base)
    (hv : S.transMap (S.refUnitTr e.isObj e'.isObj h) e.vec.1 = e'.vec.1) : e = e' := by
  obtain ⟨α, hα, v⟩ := e
  obtain ⟨β, hβ, w⟩ := e'
  dsimp only at h hv
  subst h
  have hvw : v.1 = w.1 :=
    (transMap_unitTr_self _ _ (levelVal_tangentProj_of_mem v.2)).symm.trans hv
  exact congrArg (TangentCatObj.mk α hα) (Subtype.ext hvw)

/-- The converse of `TangentCatObj.ext_of`. -/
theorem TangentCatObj.transMap_vec_of_eq {e e' : S.TangentCatObj} (h : e = e') :
    S.transMap (S.refUnitTr e.isObj e'.isObj (congrArg TangentCatObj.base h)) e.vec.1 =
      e'.vec.1 := by
  subst h
  exact transMap_unitTr_self _ _ (levelVal_tangentProj_of_mem e.vec.2)

variable (S) in
/-- `Tσ(q_α)` of `(q_α, φ, q_{α'})` on the reference fibres (`Tφ` through `S_{Ψ_α}`,
`S_{Ψ_{α'}}`). -/
def refMorVec {α α' : C.Obj} (hα : S.TangentObj α) (hα' : S.TangentObj α') (φ : C.Mor)
    (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
    (v : (S.refUnif hα).1.P.tangentFiber (S.refPoint hα)) :
    (S.refUnif hα').1.P.tangentFiber (S.refPoint hα') :=
  ⟨S.transMap (S.refTr hα hα' φ hs ht) v.1, transMap_mem_fiber _ rfl rfl v.2⟩

variable (S) in
/-- **The morphisms of `TC`** (2021 Definition 17.2.6, p. 770): `(h̄, φ, Tφ(h̄))` with
`s(φ) = P(h̄)`, given by `h̄` and `φ` (the target `TangentCatMor.tgt`). -/
structure TangentCatMor : Type (max u 1) where
  /-- The source `h̄`. -/
  src : S.TangentCatObj
  /-- The morphism `φ` of `C`. -/
  mor : C.Mor
  src_eq : C.toGroupoidStr.src mor = src.base
  isObj_tgt : S.TangentObj (C.toGroupoidStr.tgt mor)

namespace TangentCatMor

/-- **The target `Tφ(h̄)`** of `(h̄, φ, Tφ(h̄))`. -/
def tgt (Φ : S.TangentCatMor) : S.TangentCatObj :=
  ⟨_, Φ.isObj_tgt, S.refMorVec Φ.src.isObj Φ.isObj_tgt Φ.mor Φ.src_eq rfl Φ.src.vec⟩

theorem ext' {Φ Φ' : S.TangentCatMor} (h₁ : Φ.src = Φ'.src) (h₂ : Φ.mor = Φ'.mor) :
    Φ = Φ' := by
  cases Φ; cases Φ'; cases h₁; cases h₂; rfl

open scoped Classical in
/-- The composite `(h̄', ψ, ·) ∘ (h̄, φ, ·) = (h̄, ψ ∘ φ, ·)` (meant for composable pairs). -/
def comp (Φ Ψ : S.TangentCatMor) : S.TangentCatMor :=
  if h : C.toGroupoidStr.src Φ.mor = C.toGroupoidStr.tgt Ψ.mor then
    ⟨Ψ.src, C.toGroupoidStr.comp Φ.mor Ψ.mor, (C.toGroupoidStr.src_comp _ _ h).trans Ψ.src_eq,
      TangentObj.of_eq (C.toGroupoidStr.tgt_comp _ _ h).symm Φ.isObj_tgt⟩
  else Ψ

theorem comp_src {Φ Ψ : S.TangentCatMor}
    (h : C.toGroupoidStr.src Φ.mor = C.toGroupoidStr.tgt Ψ.mor) : (Φ.comp Ψ).src = Ψ.src := by
  rw [comp, dif_pos h]

theorem comp_mor {Φ Ψ : S.TangentCatMor}
    (h : C.toGroupoidStr.src Φ.mor = C.toGroupoidStr.tgt Ψ.mor) :
    (Φ.comp Ψ).mor = C.toGroupoidStr.comp Φ.mor Ψ.mor := by
  rw [comp, dif_pos h]

/-- The inverse `(Tφ(h̄), φ⁻¹, h̄)`. -/
def inv (Φ : S.TangentCatMor) : S.TangentCatMor :=
  ⟨Φ.tgt, C.toGroupoidStr.inv Φ.mor, C.toGroupoidStr.src_inv _,
    TangentObj.of_eq ((C.toGroupoidStr.tgt_inv _).trans Φ.src_eq).symm Φ.src.isObj⟩

theorem mor_composable {Φ Ψ : S.TangentCatMor} (h : Φ.src = Ψ.tgt) :
    C.toGroupoidStr.src Φ.mor = C.toGroupoidStr.tgt Ψ.mor :=
  Φ.src_eq.trans (congrArg TangentCatObj.base h)

theorem tgt_comp (Φ Ψ : S.TangentCatMor) (h : Φ.src = Ψ.tgt) : (Φ.comp Ψ).tgt = Φ.tgt := by
  have hm := mor_composable h
  obtain ⟨e, φ, hφ, hφt⟩ := Φ
  dsimp only at h hm
  subst h
  simp only [comp, dif_pos hm]
  refine TangentCatObj.ext_of (C.toGroupoidStr.tgt_comp _ _ hm) ?_
  refine transMap_transMap_eq _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · exact GroupoidStr.unit_comp_of_eq (C.toGroupoidStr.tgt_comp _ _ hm)
  · rfl
  · exact levelVal_tangentProj_of_mem Ψ.src.vec.2

theorem tgt_inv (Φ : S.TangentCatMor) : Φ.inv.tgt = Φ.src := by
  refine TangentCatObj.ext_of ((C.toGroupoidStr.tgt_inv _).trans Φ.src_eq) ?_
  refine transMap_three_eq_self
    (S.refUnitTr Φ.inv.isObj_tgt Φ.src.isObj ((C.toGroupoidStr.tgt_inv _).trans Φ.src_eq))
    (S.refTr Φ.isObj_tgt Φ.inv.isObj_tgt (C.toGroupoidStr.inv Φ.mor)
      (C.toGroupoidStr.src_inv _) rfl)
    (S.refTr Φ.src.isObj Φ.isObj_tgt Φ.mor Φ.src_eq rfl) rfl rfl ?_ rfl
    (levelVal_tangentProj_of_mem Φ.src.vec.2)
  change C.toGroupoidStr.comp (C.toGroupoidStr.comp (C.toGroupoidStr.unit Φ.src.base)
    (C.toGroupoidStr.inv Φ.mor)) Φ.mor = C.toGroupoidStr.unit _
  rw [GroupoidStr.unit_comp_of_eq ((C.toGroupoidStr.tgt_inv _).trans Φ.src_eq),
    C.toGroupoidStr.inv_comp, Φ.src_eq]
  exact congrArg C.toGroupoidStr.unit (obj_refPoint _).symm

end TangentCatMor

/-- The unit `(h̄, 1_α, h̄)`. -/
def TangentCatObj.unitMor (e : S.TangentCatObj) : S.TangentCatMor :=
  ⟨e, C.toGroupoidStr.unit e.base, C.toGroupoidStr.src_unit _,
    TangentObj.of_eq (C.toGroupoidStr.tgt_unit _).symm e.isObj⟩

theorem TangentCatObj.tgt_unitMor (e : S.TangentCatObj) : e.unitMor.tgt = e := by
  refine TangentCatObj.ext_of (C.toGroupoidStr.tgt_unit _) ?_
  refine transMap_transMap_eq_self _ _ ?_ ?_ ?_ ?_
  · rfl
  · change C.toGroupoidStr.comp (C.toGroupoidStr.unit e.base) (C.toGroupoidStr.unit e.base) =
      C.toGroupoidStr.unit _
    rw [GroupoidStr.unit_comp_of_eq (C.toGroupoidStr.tgt_unit _)]
    exact congrArg C.toGroupoidStr.unit (obj_refPoint _).symm
  · rfl
  · exact levelVal_tangentProj_of_mem e.vec.2

variable (S) in
/-- **The groupoid `TC`** (2021 Definition 17.2.6, p. 770): `s(h̄, φ, h̄') = h̄`,
`t(h̄, φ, h̄') = h̄' = Tφ(h̄)`, `(h̄', ψ, h̄'') ∘ (h̄, φ, h̄') = (h̄, ψ ∘ φ, h̄'')`;
"every morphism is invertible". -/
def tangentCatGroupoid : GroupoidStr S.TangentCatObj S.TangentCatMor where
  src Φ := Φ.src
  tgt Φ := Φ.tgt
  comp := TangentCatMor.comp
  unit := TangentCatObj.unitMor
  inv := TangentCatMor.inv
  src_comp _ _ h := TangentCatMor.comp_src (TangentCatMor.mor_composable h)
  tgt_comp := TangentCatMor.tgt_comp
  comp_assoc Φ Ψ X h₁ h₂ := by
    have hm₁ := TangentCatMor.mor_composable h₁
    have hm₂ := TangentCatMor.mor_composable h₂
    have hm₃ : C.toGroupoidStr.src (Φ.comp Ψ).mor = C.toGroupoidStr.tgt X.mor := by
      rw [TangentCatMor.comp_mor hm₁, C.toGroupoidStr.src_comp _ _ hm₁]; exact hm₂
    have hm₄ : C.toGroupoidStr.src Φ.mor = C.toGroupoidStr.tgt (Ψ.comp X).mor := by
      rw [TangentCatMor.comp_mor hm₂, C.toGroupoidStr.tgt_comp _ _ hm₂]; exact hm₁
    refine TangentCatMor.ext' ?_ ?_
    · rw [TangentCatMor.comp_src hm₃, TangentCatMor.comp_src hm₄, TangentCatMor.comp_src hm₂]
    · rw [TangentCatMor.comp_mor hm₃, TangentCatMor.comp_mor hm₄, TangentCatMor.comp_mor hm₁,
        TangentCatMor.comp_mor hm₂, C.toGroupoidStr.comp_assoc _ _ _ hm₁ hm₂]
  src_unit _ := rfl
  tgt_unit := TangentCatObj.tgt_unitMor
  comp_unit Φ := by
    have hm : C.toGroupoidStr.src Φ.mor = C.toGroupoidStr.tgt Φ.src.unitMor.mor :=
      Φ.src_eq.trans (C.toGroupoidStr.tgt_unit _).symm
    refine TangentCatMor.ext' (TangentCatMor.comp_src hm) ?_
    rw [TangentCatMor.comp_mor hm]
    exact GroupoidStr.comp_unit_of_eq Φ.src_eq
  unit_comp Φ := by
    have hm : C.toGroupoidStr.src Φ.tgt.unitMor.mor = C.toGroupoidStr.tgt Φ.mor :=
      C.toGroupoidStr.src_unit _
    refine TangentCatMor.ext' (TangentCatMor.comp_src hm) ?_
    rw [TangentCatMor.comp_mor hm]
    exact C.toGroupoidStr.unit_comp _
  src_inv _ := rfl
  tgt_inv := TangentCatMor.tgt_inv
  comp_inv Φ := by
    have hm : C.toGroupoidStr.src Φ.mor = C.toGroupoidStr.tgt Φ.inv.mor :=
      (C.toGroupoidStr.tgt_inv _).symm
    refine TangentCatMor.ext' (TangentCatMor.comp_src hm) ?_
    rw [TangentCatMor.comp_mor hm]
    exact C.toGroupoidStr.comp_inv _
  inv_comp Φ := by
    have hm : C.toGroupoidStr.src Φ.inv.mor = C.toGroupoidStr.tgt Φ.mor :=
      C.toGroupoidStr.src_inv _
    refine TangentCatMor.ext' (TangentCatMor.comp_src hm) ?_
    rw [TangentCatMor.comp_mor hm]
    exact (C.toGroupoidStr.inv_comp _).trans (congrArg _ Φ.src_eq)

theorem tangentCatGroupoid_src (Φ : S.TangentCatMor) : S.tangentCatGroupoid.src Φ = Φ.src := rfl

theorem tangentCatGroupoid_tgt (Φ : S.TangentCatMor) : S.tangentCatGroupoid.tgt Φ = Φ.tgt := rfl

/-- **Lemma 17.2.7, the finiteness** (2021 p. 770): between two objects of `TC` there are only
finitely many morphisms. -/
theorem finite_tangentCatMor (e e' : S.TangentCatObj) :
    (S.tangentCatGroupoid.mor e e').Finite := by
  refine Set.Finite.of_finite_image (f := TangentCatMor.mor)
    ((C.finite_mor e.base e'.base).subset ?_) ?_
  · rintro _ ⟨Φ, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨Φ.src_eq.trans (congrArg TangentCatObj.base h₁), congrArg TangentCatObj.base h₂⟩
  · intro Φ h Φ' h' hm
    exact TangentCatMor.ext' (h.1.trans h'.1.symm) hm

variable (S) in
/-- **The tangent category `TC`** (2021 Definition 17.2.6 and Lemma 17.2.7, p. 770), a groupoidal
category in the universe `max u 1` of `TO`. -/
def tangentCategory : GroupoidalCategory.{max u 1} where
  Obj := S.TangentCatObj
  Mor := S.TangentCatMor
  toGroupoidStr := S.tangentCatGroupoid
  finite_mor := finite_tangentCatMor

/-- **Lemma 17.2.7** (2021 p. 770): `TC` is a groupoidal category: a groupoid (every morphism
is invertible, `tangentCatGroupoid`) with finite morphism sets, whose orbit space `|TC|` is a
set (a type). -/
theorem lemma_17_2_7 :
    S.tangentCategory.toGroupoidStr = S.tangentCatGroupoid ∧
      ∀ e e' : S.tangentCategory.Obj, (S.tangentCategory.toGroupoidStr.mor e e').Finite :=
  ⟨rfl, S.tangentCategory.finite_mor⟩

/-! ### Definition 17.2.6 and Remark 17.2.8 in the text's form -/

variable (S) in
/-- **The objects of `TC` are the tangent vectors `[α, Ψ, h] ∈ T_αC`** (2021
Definition 17.2.6): `h̄ ↦ (P(h̄), S_{Ψ_α}⁻¹(vec))`. -/
def tangentCatObjEquiv : S.TangentCatObj ≃ Σ α : C.Obj, S.TangentSpaceAt α where
  toFun e := ⟨e.base, (S.refChart e.isObj).symm e.vec⟩
  invFun p := ⟨p.1, tangentObj_of_tangentSpaceAt p.2, S.refChart _ p.2⟩
  left_inv e := by
    obtain ⟨α, hα, v⟩ := e
    exact congrArg (TangentCatObj.mk α hα) ((S.refChart hα).apply_symm_apply v)
  right_inv p := by
    obtain ⟨α, v⟩ := p
    exact congrArg (Sigma.mk α) ((S.refChart _).symm_apply_apply v)

theorem tangentCatObjEquiv_fst (e : S.TangentCatObj) :
    (S.tangentCatObjEquiv e).1 = e.base := rfl

variable (S) in
/-- **The morphisms of `TC` are the tuples `(h̄, φ, Tφ(h̄))` with `s(φ) = α`** (2021
Definition 17.2.6): the pairs `(h̄, φ)`, `h̄ ∈ T_αC`, `s(φ) = α`, `t(φ)` on level `1` with
`F(t(φ)) ≠ ∅`. -/
def tangentCatMorEquiv : S.TangentCatMor ≃
    {p : (Σ α : C.Obj, S.TangentSpaceAt α) × C.Mor //
      C.toGroupoidStr.src p.2 = p.1.1 ∧ S.TangentObj (C.toGroupoidStr.tgt p.2)} where
  toFun Φ := ⟨(S.tangentCatObjEquiv Φ.src, Φ.mor), Φ.src_eq, Φ.isObj_tgt⟩
  invFun p := ⟨S.tangentCatObjEquiv.symm p.1.1, p.1.2, p.2.1, p.2.2⟩
  left_inv Φ := TangentCatMor.ext' (S.tangentCatObjEquiv.symm_apply_apply Φ.src) rfl
  right_inv p := Subtype.ext (Prod.ext (S.tangentCatObjEquiv.apply_symm_apply p.1.1) rfl)

/-- **Definition 17.2.6, `t(h̄, φ, Tφ(h̄)) = Tφ(h̄)`** (2021 p. 770): through
`tangentCatObjEquiv`, the target of a morphism is `Tφ` (Proposition 17.2.5) of its source. -/
theorem definition_17_2_6 (Φ : S.TangentCatMor) [Fact (S.TangentObj Φ.src.base)]
    [Fact (S.TangentObj (C.toGroupoidStr.tgt Φ.mor))] :
    S.tangentCatObjEquiv Φ.tgt = ⟨C.toGroupoidStr.tgt Φ.mor,
      S.tangentMorCLE Φ.mor Φ.src_eq rfl (S.tangentCatObjEquiv Φ.src).2⟩ := by
  refine congrArg (Sigma.mk _) ?_
  have h₁ : (S.refChartCLE Φ.src.base) ((S.refChart Φ.src.isObj).symm Φ.src.vec) = Φ.src.vec :=
    (S.refChart _).apply_symm_apply _
  have h₂ : S.transTangent (S.refTr Φ.src.isObj Φ.isObj_tgt Φ.mor Φ.src_eq rfl) rfl rfl
      Φ.src.vec = S.refMorVec Φ.src.isObj Φ.isObj_tgt Φ.mor Φ.src_eq rfl Φ.src.vec :=
    Subtype.ext (transTangent_apply _ _ _ _)
  change (S.refChart Φ.isObj_tgt).symm (S.refMorVec Φ.src.isObj Φ.isObj_tgt Φ.mor Φ.src_eq rfl
      Φ.src.vec) = (S.refChartCLE (C.toGroupoidStr.tgt Φ.mor)).symm
    (S.transTangent (S.refTr Φ.src.isObj Φ.isObj_tgt Φ.mor Φ.src_eq rfl) rfl rfl
      ((S.refChartCLE Φ.src.base) ((S.refChart Φ.src.isObj).symm Φ.src.vec)))
  rw [h₁, h₂]
  rfl

variable (S) in
/-- **Remark 17.2.8, the morphisms** (2021 p. 770): the pairs `(φ, e)`, `φ` a morphism with
`t(φ)` on level `1` (and `F(t(φ)) ≠ ∅`), `e ∈ μ_C(s(φ)) = T_{s(φ)}C`. -/
def remarkMorEquiv : S.TangentCatMor ≃
    Σ φ : {φ : C.Mor // S.TangentObj (C.toGroupoidStr.tgt φ)},
      S.TangentSpaceAt (C.toGroupoidStr.src φ.1) where
  toFun Φ := ⟨⟨Φ.mor, Φ.isObj_tgt⟩, S.tangentVector ⟨S.refUnif Φ.src.isObj,
    by rw [Φ.src_eq]; exact refUnif_mem Φ.src.isObj, Φ.src.vec.1,
    ((congrArg (S.refUnif Φ.src.isObj).1.obj (levelVal_tangentProj_of_mem Φ.src.vec.2)).trans
      (obj_refPoint Φ.src.isObj)).trans Φ.src_eq.symm⟩⟩
  invFun p := ⟨S.tangentCatObjEquiv.symm
    (⟨C.toGroupoidStr.src p.1.1, p.2⟩ : Σ α : C.Obj, S.TangentSpaceAt α), p.1.1, rfl, p.1.2⟩
  left_inv Φ := by
    refine TangentCatMor.ext' (TangentCatObj.ext_of Φ.src_eq ?_) rfl
    refine transMap_transMap_eq_self _ _ ?_ ?_ ?_ ?_
    · rfl
    · change C.toGroupoidStr.comp (C.toGroupoidStr.unit Φ.src.base)
        (C.toGroupoidStr.unit (C.toGroupoidStr.src Φ.mor)) = C.toGroupoidStr.unit _
      exact (GroupoidStr.unit_comp_of_eq ((C.toGroupoidStr.tgt_unit _).trans Φ.src_eq)).trans
        (congrArg _ (Φ.src_eq.trans ((congrArg (S.refUnif Φ.src.isObj).1.obj
          (levelVal_tangentProj_of_mem Φ.src.vec.2)).trans (obj_refPoint Φ.src.isObj)).symm))
    · exact (levelVal_tangentProj_of_mem Φ.src.vec.2).symm
    · rfl
  right_inv p := by
    obtain ⟨⟨φ, ht⟩, e⟩ := p
    exact congrArg (Sigma.mk (⟨φ, ht⟩ : {φ : C.Mor // S.TangentObj (C.toGroupoidStr.tgt φ)}))
      ((S.refChart _).symm_apply_apply e)

/-- **Remark 17.2.8** (2021 p. 770): through `tangentCatObjEquiv` and `remarkMorEquiv`,
`s(φ, e) = (s(φ), e)` and `t(φ, e) = (t(φ), Tφ(e))`. -/
theorem remark_17_2_8 (φ : C.Mor) (ht : S.TangentObj (C.toGroupoidStr.tgt φ))
    (e : S.TangentSpaceAt (C.toGroupoidStr.src φ))
    [Fact (S.TangentObj (C.toGroupoidStr.src φ))] [Fact (S.TangentObj (C.toGroupoidStr.tgt φ))] :
    S.tangentCatObjEquiv (S.remarkMorEquiv.symm ⟨⟨φ, ht⟩, e⟩).src =
        ⟨C.toGroupoidStr.src φ, e⟩ ∧
      S.tangentCatObjEquiv (S.remarkMorEquiv.symm ⟨⟨φ, ht⟩, e⟩).tgt =
        ⟨C.toGroupoidStr.tgt φ, S.tangentMorCLE φ rfl rfl e⟩ := by
  refine ⟨S.tangentCatObjEquiv.apply_symm_apply _, ?_⟩
  refine (@definition_17_2_6 _ _ (S.remarkMorEquiv.symm ⟨⟨φ, ht⟩, e⟩)
    (inferInstance : Fact (S.TangentObj (C.toGroupoidStr.src φ)))
    (inferInstance : Fact (S.TangentObj (C.toGroupoidStr.tgt φ)))).trans ?_
  exact congrArg (fun e' => (⟨C.toGroupoidStr.tgt φ, S.tangentMorCLE φ rfl rfl e'⟩ :
    Σ α : C.Obj, S.TangentSpaceAt α)) ((S.refChart _).symm_apply_apply e)

/-! ### The projection functor `P : TC → C¹` -/

variable (S) in
/-- **`P : TC → C¹`** (2021 (17.33), (17.34), p. 771): `P([α, Ψ, h]) = α`, `P(h̄, φ, h̄') = φ`,
into the full subgroupoid `C¹` of the objects of regularity `≥ 1`. -/
def tangentCatProj : GroupoidFunctor S.tangentCatGroupoid (S.regSub 1) where
  obj e := ⟨e.base, e.isObj.1⟩
  mor Φ := ⟨Φ.mor, by rw [Φ.src_eq]; exact Φ.src.isObj.1, Φ.isObj_tgt.1⟩
  src_mor Φ := Subtype.ext Φ.src_eq
  tgt_mor _ := rfl
  mor_comp Φ Ψ h := by
    have hm := TangentCatMor.mor_composable h
    refine Subtype.ext ?_
    change (Φ.comp Ψ).mor = ((C.toGroupoidStr.fullSub (S.regSet 1)).comp _ _).1
    rw [TangentCatMor.comp_mor hm]
    simp only [GroupoidStr.fullSub, dif_pos hm]
  mor_unit _ := rfl

/-- `P` is surjective on objects for `HasUniformizers`: every `α ∈ C¹` carries the vector `0`. -/
theorem surjective_tangentCatProj_obj (hU : S.HasUniformizers) :
    Surjective (S.tangentCatProj).obj := by
  rintro ⟨α, hα⟩
  exact ⟨⟨α, (tangentObj_iff hU α).2 hα, 0⟩, rfl⟩

/-! ### The tangent uniformizer `TΨ` on objects, Lemma 17.2.9 -/

/-- `τ(h) ∈ O` for `h ∈ TO`. -/
abbrev basePt (Ψ : S.Unif) (k : Ψ.1.P.TangentSpace) : Ψ.1.O :=
  Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj k)

theorem tangentObj_of_unif (hU : S.HasUniformizers) (Ψ : S.Unif) (k : Ψ.1.P.TangentSpace) :
    S.TangentObj (Ψ.1.obj (basePt Ψ k)) :=
  ⟨⟨Ψ, _, C.toGroupoidStr.isomorphic_refl _, MPolyfold.levelVal_mem _⟩, hU _⟩

variable (S) in
/-- **The tangent uniformizer `TΨ : TO → TC` on objects** (2021 (17.35), (17.36), p. 771):
`TΨ(h) = [Ψ(τ(h)), Ψ', Tσ(h)]`, with `Ψ' = Ψ_{Ψ(τ(h))}` the reference uniformizer (for every
other choice: `tangentUnifObj_spec`). -/
def tangentUnifObj (hU : S.HasUniformizers) (Ψ : S.Unif) (k : Ψ.1.P.TangentSpace) :
    S.TangentCatObj :=
  ⟨_, tangentObj_of_unif hU Ψ k,
    ⟨S.transMap (S.unitTr (basePt Ψ k) (S.refQ (tangentObj_of_unif hU Ψ k)) rfl
      (obj_refPoint _)) k, transMap_mem_fiber _ rfl rfl (rfl : Ψ.1.P.tangentProj k = _)⟩⟩

theorem tangentUnifObj_base (hU : S.HasUniformizers) (Ψ : S.Unif) (k : Ψ.1.P.TangentSpace) :
    (S.tangentUnifObj hU Ψ k).base = Ψ.1.obj (basePt Ψ k) := rfl

/-- **Lemma 17.2.9** (2021 p. 773): `TΨ(h) = [Ψ(q), Ψ', Tσ(h)]`, `q = τ(h)`, does not depend on
`Ψ' ∈ F(Ψ(q))` (nor on `q'` with `Ψ'(q') = Ψ(q)`): for `Ψ''` the classes agree, since
`σ'' ∘ σ = σ'` near `q`. -/
theorem lemma_17_2_9 (Ψ : S.Unif) (k : Ψ.1.P.TangentSpace) (Ψ₁ : S.Unif)
    (hΨ₁ : Ψ₁.1 ∈ S.F (Ψ.1.obj (basePt Ψ k))) (q₁ : Ψ₁.1.O)
    (hq₁ : Ψ₁.1.obj q₁ = Ψ.1.obj (basePt Ψ k)) (Ψ₂ : S.Unif)
    (hΨ₂ : Ψ₂.1 ∈ S.F (Ψ.1.obj (basePt Ψ k))) (q₂ : Ψ₂.1.O)
    (hq₂ : Ψ₂.1.obj q₂ = Ψ.1.obj (basePt Ψ k)) :
    S.tangentVector ⟨Ψ₁, hΨ₁, S.transMap (S.unitTr (basePt Ψ k) q₁ rfl hq₁) k,
        (congrArg Ψ₁.1.obj (base_transMap _ rfl)).trans hq₁⟩ =
      S.tangentVector ⟨Ψ₂, hΨ₂, S.transMap (S.unitTr (basePt Ψ k) q₂ rfl hq₂) k,
        (congrArg Ψ₂.1.obj (base_transMap _ rfl)).trans hq₂⟩ := by
  refine Quotient.sound ?_
  change S.transMap (S.unitTr _ _ _ _) (S.transMap _ k) = S.transMap _ k
  exact (congrFun (transMap_unitTr_congr (base_transMap _ rfl) (base_transMap _ rfl) _ _ hq₁ hq₂)
    _).trans (transMap_unitTr_comp (basePt Ψ k) q₁ q₂ rfl hq₁ hq₂ rfl)

/-- **(17.36) for every choice of `Ψ'`**: through `tangentCatObjEquiv`,
`TΨ(h) = [Ψ(τ(h)), Ψ', Tσ(h)]` for every `Ψ' ∈ F(Ψ(τ(h)))` and `Ψ'(q') = Ψ(τ(h))`. -/
theorem tangentUnifObj_spec (hU : S.HasUniformizers) (Ψ : S.Unif) (k : Ψ.1.P.TangentSpace)
    (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F (Ψ.1.obj (basePt Ψ k))) (q' : Ψ'.1.O)
    (hq' : Ψ'.1.obj q' = Ψ.1.obj (basePt Ψ k)) :
    S.tangentCatObjEquiv (S.tangentUnifObj hU Ψ k) = ⟨Ψ.1.obj (basePt Ψ k),
      S.tangentVector ⟨Ψ', hΨ', S.transMap (S.unitTr (basePt Ψ k) q' rfl hq') k,
        (congrArg Ψ'.1.obj (base_transMap _ rfl)).trans hq'⟩⟩ :=
  congrArg (Sigma.mk _) (lemma_17_2_9 Ψ k (S.refUnif (tangentObj_of_unif hU Ψ k))
    (refUnif_mem _) _ (obj_refPoint _) Ψ' hΨ' q' hq')

/-! ### The tangent uniformizer on morphisms, Lemma 17.2.10 -/

variable (S) in
/-- **`G ⋉ TO`** (2021 (17.35), p. 771): the translation groupoid of `G` acting on `TO` by
`g ∗ h = T(g ∗ ·)(h)` (through `ULift G`, which only matches universes). -/
abbrev tangentTranslation (Ψ : S.Unif) :
    GroupoidStr Ψ.1.P.TangentSpace (ULift.{1} Ψ.1.G × Ψ.1.P.TangentSpace) :=
  GroupoidStr.translation (ULift.{1} Ψ.1.G) Ψ.1.P.TangentSpace

theorem basePt_smul (Ψ : S.Unif) (g : ULift.{1} Ψ.1.G) (k : Ψ.1.P.TangentSpace) :
    basePt Ψ (g • k) = g.down • basePt Ψ k :=
  GroupoidalCategory.Uniformizer.levelVal_tangentProj_smul _ g.down k

variable (S) in
/-- **`TΨ(g, h) = (TΨ(h), Ψ(g, q), T(Ψ(g, q))TΨ(h))`** (2021 (17.39), p. 773), `q = τ(h)`. -/
def tangentUnifMor (hU : S.HasUniformizers) (Ψ : S.Unif)
    (p : ULift.{1} Ψ.1.G × Ψ.1.P.TangentSpace) : S.TangentCatMor :=
  ⟨S.tangentUnifObj hU Ψ p.2, Ψ.1.mor (p.1.down, basePt Ψ p.2), Ψ.1.src_mor _,
    ⟨(tangentObj_of_unif hU Ψ p.2).1.of_isomorphic ⟨_, Ψ.1.src_mor _, rfl⟩, hU _⟩⟩

theorem tangentUnifMor_src (hU : S.HasUniformizers) (Ψ : S.Unif)
    (p : ULift.{1} Ψ.1.G × Ψ.1.P.TangentSpace) :
    (S.tangentUnifMor hU Ψ p).src = S.tangentUnifObj hU Ψ p.2 := rfl

/-- `TΨ` respects composition (for every `Ψ`). -/
theorem tangentUnifMor_comp (hU : S.HasUniformizers) (Ψ : S.Unif)
    (p p' : ULift.{1} Ψ.1.G × Ψ.1.P.TangentSpace) (h : p.2 = p'.1 • p'.2) :
    S.tangentUnifMor hU Ψ (p.1 * p'.1, p'.2) =
      (S.tangentUnifMor hU Ψ p).comp (S.tangentUnifMor hU Ψ p') := by
  have hq : basePt Ψ p.2 = p'.1.down • basePt Ψ p'.2 := by
    rw [h]; exact basePt_smul Ψ p'.1 p'.2
  have hm : C.toGroupoidStr.src (S.tangentUnifMor hU Ψ p).mor =
      C.toGroupoidStr.tgt (S.tangentUnifMor hU Ψ p').mor := by
    change C.toGroupoidStr.src (Ψ.1.mor _) = C.toGroupoidStr.tgt (Ψ.1.mor _)
    rw [Ψ.1.src_mor, Ψ.1.tgt_mor]; exact congrArg Ψ.1.obj hq
  refine TangentCatMor.ext' (TangentCatMor.comp_src hm).symm ?_
  rw [TangentCatMor.comp_mor hm]
  change Ψ.1.mor ((p.1 * p'.1).down, basePt Ψ p'.2) = C.toGroupoidStr.comp
    (Ψ.1.mor (p.1.down, basePt Ψ p.2)) (Ψ.1.mor (p'.1.down, basePt Ψ p'.2))
  rw [hq]
  exact Ψ.1.functor.mor_comp (p.1.down, p'.1.down • basePt Ψ p'.2) (p'.1.down, basePt Ψ p'.2) rfl

/-- `TΨ` respects units (for every `Ψ`). -/
theorem tangentUnifMor_one (hU : S.HasUniformizers) (Ψ : S.Unif) (k : Ψ.1.P.TangentSpace) :
    S.tangentUnifMor hU Ψ (1, k) = (S.tangentUnifObj hU Ψ k).unitMor :=
  TangentCatMor.ext' rfl (Ψ.1.functor.mor_unit (basePt Ψ k))

/-- **`σ = (g ∗ ·)` near `q` for `Ψ̂(g, q) ∈ M(Ψ, Ψ)`, if `Ψ̂` is continuous**: then
`p ↦ Ψ̂(g, p)` is a continuous local section of `s` through `Ψ̂(g, q)`, so
`Tσ(h) = T(g ∗ ·)(h) = g ∗ h` for `h` over `q`. -/
theorem transMap_hat_of_continuous {Ψ : S.Unif} (hc : Continuous (S.hat Ψ)) (g : Ψ.1.G)
    (k : Ψ.1.P.TangentSpace) : S.transMap (S.hat Ψ (g, basePt Ψ k)) k = g • k := by
  set T := S.triple (S.hat Ψ (g, basePt Ψ k))
  obtain ⟨W', hW'o, hqW', hW'sub, hW'eq⟩ := T.exists_srcInv_eq (f := fun p => S.hat Ψ (g, p))
    isOpen_univ (mem_univ _) (hc.comp (Continuous.prodMk_right g)).continuousOn
    (fun p _ => rfl) rfl
  have hσ : EqOn T.sigma (fun y => g • y) W' := fun p hp => by
    change (T.srcInv p).tgt = g • p
    rw [hW'eq p hp]; rfl
  have hmem : k ∈ Ψ.1.P.tangentPreimage W' := by
    rw [MPolyfold.mem_tangentPreimage]; exact hqW'
  exact (MPolyfold.tangentMapOn_congr T.isScSmoothOn_sigma (Ψ.1.smooth_smul g) hW'o
    (fun p hp => (hW'sub hp).2) (subset_univ _) hσ hmem).trans
    (congrFun (MPolyfold.tangentMapOn_univ (Ψ.1.smooth_smul g)) k)

/-- **The identity `TΨ(g ∗ h) = T(Ψ(g, q))(TΨ(h))` of (17.40), for continuous `Ψ̂`**: the target
of `TΨ(g, h)` is `TΨ(g ∗ h)`. -/
theorem tangentUnifMor_tgt_of_continuous (hU : S.HasUniformizers) (Ψ : S.Unif)
    (hc : Continuous (S.hat Ψ)) (p : ULift.{1} Ψ.1.G × Ψ.1.P.TangentSpace) :
    (S.tangentUnifMor hU Ψ p).tgt = S.tangentUnifObj hU Ψ (p.1 • p.2) := by
  obtain ⟨g, k⟩ := p
  have hq : basePt Ψ (g • k) = g.down • basePt Ψ k := basePt_smul Ψ g k
  have hb : C.toGroupoidStr.tgt (Ψ.1.mor (g.down, basePt Ψ k)) = Ψ.1.obj (basePt Ψ (g • k)) :=
    (Ψ.1.tgt_mor _).trans (congrArg Ψ.1.obj hq.symm)
  refine TangentCatObj.ext_of hb ?_
  have h₂ : C.toGroupoidStr.comp (C.toGroupoidStr.comp
      (C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ (g • k)))) (Ψ.1.mor (g.down, basePt Ψ k)))
      (C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ k))) =
      C.toGroupoidStr.comp (C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ (g • k))))
        (Ψ.1.mor (g.down, basePt Ψ k)) :=
    GroupoidStr.comp_unit_of_eq ((C.toGroupoidStr.src_comp _ _
      ((C.toGroupoidStr.src_unit _).trans hb.symm)).trans (Ψ.1.src_mor _))
  exact (transMap_three_eq
    (S.refUnitTr (S.tangentUnifMor hU Ψ (g, k)).isObj_tgt (tangentObj_of_unif hU Ψ (g • k)) hb)
    (S.refTr (tangentObj_of_unif hU Ψ k) (S.tangentUnifMor hU Ψ (g, k)).isObj_tgt
      (Ψ.1.mor (g.down, basePt Ψ k)) (Ψ.1.src_mor _) rfl)
    (S.unitTr (basePt Ψ k) (S.refQ (tangentObj_of_unif hU Ψ k)) rfl (obj_refPoint _))
    (S.unitTr (basePt Ψ (g • k)) (S.refQ (tangentObj_of_unif hU Ψ (g • k))) rfl (obj_refPoint _))
    (S.hat Ψ (g.down, basePt Ψ k)) rfl rfl hq rfl h₂ rfl rfl).trans
    (congrArg (S.transMap _) (transMap_hat_of_continuous hc g.down k))

variable (S) in
/-- **The tangent uniformizer `TΨ : G ⋉ TO → TC`** (2021 (17.35), (17.39), Lemma 17.2.10), a
functor when `Ψ̂` is continuous. -/
def tangentUnifFunctor (hU : S.HasUniformizers) (Ψ : S.Unif) (hc : Continuous (S.hat Ψ)) :
    GroupoidFunctor (S.tangentTranslation Ψ) S.tangentCatGroupoid where
  obj := S.tangentUnifObj hU Ψ
  mor := S.tangentUnifMor hU Ψ
  src_mor _ := rfl
  tgt_mor p := tangentUnifMor_tgt_of_continuous hU Ψ hc p
  mor_comp p p' h := tangentUnifMor_comp hU Ψ p p' h
  mor_unit k := tangentUnifMor_one hU Ψ k

/-- **The laws of Lemma 17.2.10 that hold for every `Ψ`** (2021 p. 773): `s(TΨ(g, h)) = TΨ(h)`,
`TΨ((g, g' ∗ h) ∘ (g', h)) = TΨ(g, g' ∗ h) ∘ TΨ(g', h)` and `TΨ(1, h) = 1_{TΨ(h)}`. -/
theorem lemma_17_2_10_mor (hU : S.HasUniformizers) (Ψ : S.Unif) :
    (∀ p, S.tangentCatGroupoid.src (S.tangentUnifMor hU Ψ p) =
      S.tangentUnifObj hU Ψ ((S.tangentTranslation Ψ).src p)) ∧
    (∀ p p', (S.tangentTranslation Ψ).src p = (S.tangentTranslation Ψ).tgt p' →
      S.tangentUnifMor hU Ψ ((S.tangentTranslation Ψ).comp p p') =
        S.tangentCatGroupoid.comp (S.tangentUnifMor hU Ψ p) (S.tangentUnifMor hU Ψ p')) ∧
    ∀ k, S.tangentUnifMor hU Ψ ((S.tangentTranslation Ψ).unit k) =
      S.tangentCatGroupoid.unit (S.tangentUnifObj hU Ψ k) :=
  ⟨fun _ => rfl, fun p p' h => tangentUnifMor_comp hU Ψ p p' h, tangentUnifMor_one hU Ψ⟩

/-- **Lemma 17.2.10, for continuous `Ψ̂`** (2021 p. 773): `TΨ : G ⋉ TO → TC`,
`h ↦ TΨ(h)`, `(g, h) ↦ (TΨ(h), Ψ(g, q), T(Ψ(g, q))TΨ(h))`, is a well-defined functor, and
`TΨ(g ∗ h) = T(Ψ(g, q))(TΨ(h))` (17.40).  (`Ψ̂` is continuous whenever Lemma 17.1.9 holds,
`lemma_17_1_9_of_continuous`.) -/
theorem lemma_17_2_10_of_continuous (hU : S.HasUniformizers) (Ψ : S.Unif)
    (hc : Continuous (S.hat Ψ)) :
    (S.tangentUnifFunctor hU Ψ hc).obj = S.tangentUnifObj hU Ψ ∧
      (S.tangentUnifFunctor hU Ψ hc).mor = S.tangentUnifMor hU Ψ ∧
      ∀ p, (S.tangentUnifMor hU Ψ p).tgt = S.tangentUnifObj hU Ψ (p.1 • p.2) :=
  ⟨rfl, rfl, tangentUnifMor_tgt_of_continuous hU Ψ hc⟩

/-- **The witness of the hypothesis of `lemma_17_2_10_of_continuous`**: for the reflection
construction (`ℤ/2` acting on `ℝ` by `x ↦ -x`, which has a non-fixed point,
`LocalUniformizer.reflection_isCentredAt`), `Ψ̂` is continuous, so `TΨ` is a functor. -/
def reflectionTangentUnifFunctor :
    GroupoidFunctor (reflectionConstruction.tangentTranslation reflectionUnif)
      reflectionConstruction.tangentCatGroupoid :=
  reflectionConstruction.tangentUnifFunctor reflectionConstruction_hasUniformizers reflectionUnif
    reflection_continuous_hat

theorem reflection_lemma_17_2_10 :
    ∀ p, (reflectionConstruction.tangentUnifMor reflectionConstruction_hasUniformizers
      reflectionUnif p).tgt = reflectionConstruction.tangentUnifObj
        reflectionConstruction_hasUniformizers reflectionUnif
          ((reflectionConstruction.tangentTranslation reflectionUnif).tgt p) :=
  (lemma_17_2_10_of_continuous _ _ reflection_continuous_hat).2.2

end GCT.PolyfoldConstruction

end Polyfold
