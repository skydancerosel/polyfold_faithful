import Polyfold.Chapter15.LinearizationFunctor
import Polyfold.Chapter10.StrongBundleEquivalenceExamples
import Polyfold.Chapter3.ParamPerturbation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.1, preamble (p. 683) and Theorem 15.1.1 (p. 684; 2017: §15.1, Theorem 15.1): the action
`φ ↦ φ_*` of the morphisms on `GrF`, **the category `GrF(X)`**, and `T(f, Λ)` as a section
functor of `GrF(X) → X_∞`.

## The text, paraphrased

(p. 683) A morphism `φ : x → y` acts on the formal sums `GrF(x)` by
`φ_*(∑ σ_L · L) = ∑ σ_L · μ(φ, ·) ∘ L ∘ (Tφ)⁻¹`; this makes `GrF(X)` a category over `X`, and a
section functor of `GrF(X) → X_∞` assigns to each `x` an element of `GrF(x)` compatibly with the
morphisms.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `muLin_comp`, `muLin_unit`: `μ(ψ ∘ φ, ·) = μ(ψ, ·) ∘ μ(φ, ·)` and `μ(1_x, ·) = id` on the fibres.
* `tangentMorCLE_comp_symm_apply`, `tangentMorCLE_unit_symm_apply`: `(T(ψ ∘ φ))⁻¹ = (Tφ)⁻¹ ∘ (Tψ)⁻¹`
  and `(T1_x)⁻¹ = id` (from Chapter 8's `tangentMor_comp` and Chapter 9's `tangentMor_unit_of_eq`).
* `conjOp_comp`, `conjOp_unit`, and **`grfPush_comp`**: `(ψ ∘ φ)_* = ψ_* ∘ φ_*`;
  **`grfPush_unit`**: `(1_x)_* = id`.
* `GrFObj A` (pairs `(x, a)`, `x ∈ X₁`, `a ∈ GrF(x)`) with the **category** `GrFObj.instCategory`:
  a morphism `(x, a) → (y, b)` is a morphism `φ : x → y` of `X` with `φ_* a = b`; composition is
  the composition of `X`, which is well defined by `grfPush_comp`.
* `grfProj : GrFObj A ⥤ A.X.toGroupoidStr.Ob`, the projection `GrF(X) → X`.
* **`linearizationFunctor`** (Theorem 15.1.1, the functor property restated): for an sc-Fredholm
  section functor `f` and an sc⁺-multisection `Λ`, `x ↦ (x, T(f, Λ)(x))` is a functor from the
  groupoid `X₁` (Chapter 7's `liftOne`) to `GrF(X)`; `linearizationFunctor_comp_grfProj_obj`: it is a
  section of the projection.
* Witnesses: `GrFObj.zero x`, the object `(x, 0)`; `grfHomOfMor φ a : (x, a) ⟶ (y, φ_* a)`
  for every morphism `φ`; `grfObj_epSEP`, `nonempty_grfHom_epSEP`: on `ℝⁿ × ℝᵏ → ℝⁿ`
  (Chapter 10's `epSEP`), `GrF(X)` has an object and its identity morphism.

## Reading

"Smooth points" is read as level-`1` points, as in `theorem_15_1_1_functor`.  The objects are
pairs over level-`1` points; `GrF(x)` is all finitely supported sums of linear maps (the
summands that occur in `T(f, Λ)` are sc-Fredholm by `linearization_summand_isScFredholm`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### `μ` and `Tφ` along compositions and units -/

/-- **`μ(ψ ∘ φ, ·) = μ(ψ, ·) ∘ μ(φ, ·)`** on `W_x` (the axiom `μ_comp` of Definition 8.3.1). -/
theorem muLin_comp (ψ φ : A.Mor) {x y z : A.Obj} (hx : A.X.src φ = x) (hy : A.X.tgt φ = y)
    (hy' : A.X.src ψ = y) (hz : A.X.tgt ψ = z) :
    muLin (A.X.comp ψ φ) ((A.X.src_comp ψ φ (hy'.trans hy.symm)).trans hx)
        ((A.X.tgt_comp ψ φ (hy'.trans hy.symm)).trans hz) =
      muLin ψ hy' hz ∘ₗ muLin φ hx hy := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  have hv : A.P v = A.X.src φ := (mem_singleton_iff.1 v.2).trans hx.symm
  rw [LinearMap.comp_apply, muLin_apply, muLin_apply, A.E.μ_comp ψ φ v hv (hy'.trans hy.symm)]
  refine A.E.μ_congr ?_
  exact Prod.ext rfl (muLin_apply φ hx hy v).symm

/-- **`μ(1_x, ·) = id`** on `W_x` (the axiom `μ_unit` of Definition 8.3.1). -/
theorem muLin_unit (x : A.Obj) :
    muLin (A.X.unit x) (A.X.src_unit x) (A.X.tgt_unit x) = LinearMap.id := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  have hv : A.P v = x := mem_singleton_iff.1 v.2
  rw [muLin_apply, LinearMap.id_apply]
  refine (A.E.μ_congr ?_).trans (A.E.μ_unit (v : A.W))
  change ((A.X.unit x, (v : A.W)) : A.Mor × A.W) = (A.X.unit (A.P v), (v : A.W))
  rw [hv]

lemma levelVal_tangentProj_of_mem {x : A.X.PObj.Level 1} (a : A.X.PObj.tangentFiber x) :
    A.X.PObj.levelVal 1 (A.X.PObj.tangentProj a.1) = A.X.PObj.levelVal 1 x :=
  (A.X.mem_tangentFiberAt).1 ((A.X.mem_tangentFiber_iff_mem_tangentFiberAt).1 a.2)

/-- **`(T(ψ ∘ φ))⁻¹ = (Tφ)⁻¹ ∘ (Tψ)⁻¹`** on `T_zX`. -/
theorem tangentMorCLE_comp_symm_apply {φ ψ : A.Mor} (hφ : φ ∈ A.X.PMor.levelSet 1)
    (hψ : ψ ∈ A.X.PMor.levelSet 1) {x y z : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    (hy' : A.X.PObj.levelVal 1 y = A.X.src ψ) (hz : A.X.PObj.levelVal 1 z = A.X.tgt ψ)
    (α : A.X.PObj.tangentFiber z) :
    (A.X.tangentMorCLE (A.X.comp_mem_levelSet hψ (hy'.symm.trans hy))
        (hx.trans (A.X.src_comp ψ φ (hy'.symm.trans hy)).symm)
        (hz.trans (A.X.tgt_comp ψ φ (hy'.symm.trans hy)).symm)).symm α =
      (A.X.tangentMorCLE hφ hx hy).symm ((A.X.tangentMorCLE hψ hy' hz).symm α) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [EpGroupoid.tangentMorCLE_apply,
    A.X.tangentMor_comp hφ (hy'.symm.trans hy)
      ((levelVal_tangentProj_of_mem _).trans hx),
    ← EpGroupoid.tangentMorCLE_apply A.X hφ hx hy, ContinuousLinearEquiv.apply_symm_apply,
    ← EpGroupoid.tangentMorCLE_apply A.X hψ hy' hz, ContinuousLinearEquiv.apply_symm_apply]

/-- **`(T1_x)⁻¹ = id`** on `T_xX`. -/
theorem tangentMorCLE_unit_symm_apply {x : A.X.PObj.Level 1}
    (h1 : A.X.unit (A.X.PObj.levelVal 1 x) ∈ A.X.PMor.levelSet 1)
    (α : A.X.PObj.tangentFiber x) :
    (A.X.tangentMorCLE h1 (A.X.src_unit _).symm (A.X.tgt_unit _).symm).symm α = α := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [EpGroupoid.tangentMorCLE_apply, A.X.tangentMor_unit_of_eq (levelVal_tangentProj_of_mem α)]

/-! ### `(ψ ∘ φ)_* = ψ_* ∘ φ_*` and `(1_x)_* = id` -/

/-- `L ↦ μ(φ, ·) ∘ L ∘ (Tφ)⁻¹` along a composite. -/
theorem conjOp_comp {φ ψ : A.Mor} (hφ : φ ∈ A.X.PMor.levelSet 1)
    (hψ : ψ ∈ A.X.PMor.levelSet 1) {x y z : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    (hy' : A.X.PObj.levelVal 1 y = A.X.src ψ) (hz : A.X.PObj.levelVal 1 z = A.X.tgt ψ)
    (L : A.X.PObj.tangentFiber x →ₗ[ℝ] A.P ⁻¹' {A.X.PObj.levelVal 1 x}) :
    conjOp (A.X.comp ψ φ) (A.X.comp_mem_levelSet hψ (hy'.symm.trans hy))
        (hx.trans (A.X.src_comp ψ φ (hy'.symm.trans hy)).symm)
        (hz.trans (A.X.tgt_comp ψ φ (hy'.symm.trans hy)).symm) L =
      conjOp ψ hψ hy' hz (conjOp φ hφ hx hy L) := by
  refine LinearMap.ext fun α => ?_
  rw [conjOp_apply, conjOp_apply, conjOp_apply,
    tangentMorCLE_comp_symm_apply hφ hψ hx hy hy' hz α]
  exact LinearMap.congr_fun (muLin_comp ψ φ hx.symm hy.symm hy'.symm hz.symm) _

/-- **`(ψ ∘ φ)_* = ψ_* ∘ φ_*`** (2021 p. 683): the action on `GrF` is functorial. -/
theorem grfPush_comp {φ ψ : A.Mor} (hφ : φ ∈ A.X.PMor.levelSet 1)
    (hψ : ψ ∈ A.X.PMor.levelSet 1) {x y z : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    (hy' : A.X.PObj.levelVal 1 y = A.X.src ψ) (hz : A.X.PObj.levelVal 1 z = A.X.tgt ψ)
    (a : GrF x) :
    grfPush (A.X.comp ψ φ) (A.X.comp_mem_levelSet hψ (hy'.symm.trans hy))
        (hx.trans (A.X.src_comp ψ φ (hy'.symm.trans hy)).symm)
        (hz.trans (A.X.tgt_comp ψ φ (hy'.symm.trans hy)).symm) a =
      grfPush ψ hψ hy' hz (grfPush φ hφ hx hy a) := by
  unfold grfPush
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext L
  exact conjOp_comp hφ hψ hx hy hy' hz L

/-- `μ(1_x, ·) ∘ L ∘ (T1_x)⁻¹ = L`. -/
theorem conjOp_unit {x : A.X.PObj.Level 1}
    (h1 : A.X.unit (A.X.PObj.levelVal 1 x) ∈ A.X.PMor.levelSet 1)
    (L : A.X.PObj.tangentFiber x →ₗ[ℝ] A.P ⁻¹' {A.X.PObj.levelVal 1 x}) :
    conjOp (A.X.unit (A.X.PObj.levelVal 1 x)) h1 (A.X.src_unit _).symm (A.X.tgt_unit _).symm L =
      L := by
  refine LinearMap.ext fun α => ?_
  rw [conjOp_apply, tangentMorCLE_unit_symm_apply h1 α]
  exact LinearMap.congr_fun (muLin_unit (A.X.PObj.levelVal 1 x)) _

/-- **`(1_x)_* = id`** on `GrF(x)` (2021 p. 683). -/
theorem grfPush_unit {x : A.X.PObj.Level 1}
    (h1 : A.X.unit (A.X.PObj.levelVal 1 x) ∈ A.X.PMor.levelSet 1) (a : GrF x) :
    grfPush (A.X.unit (A.X.PObj.levelVal 1 x)) h1 (A.X.src_unit _).symm (A.X.tgt_unit _).symm a =
      a := by
  unfold grfPush
  have : conjOp (A.X.unit (A.X.PObj.levelVal 1 x)) h1 (A.X.src_unit _).symm
      (A.X.tgt_unit _).symm = id := funext fun L => conjOp_unit h1 L
  rw [this, Finsupp.mapDomain_id]

/-! ### The category `GrF(X)` -/

variable (A) in
/-- **The objects of `GrF(X)`** (2021 p. 683): pairs `(x, a)` with `x ∈ X₁` and `a ∈ GrF(x)`. -/
structure GrFObj : Type (max u 1) where
  /-- The base point `x ∈ X₁`. -/
  pt : A.X.PObj.Level 1
  /-- The formal sum `a ∈ GrF(x)`. -/
  val : GrF (A := A) pt

/-- **The morphisms `(x, a) → (y, b)` of `GrF(X)`**: morphisms `φ : x → y` of `X` with
`φ_* a = b`. -/
def GrFHom (a b : GrFObj A) : Type u :=
  {φ : A.Mor // ∃ (hx : A.X.PObj.levelVal 1 a.pt = A.X.src φ)
    (hy : A.X.PObj.levelVal 1 b.pt = A.X.tgt φ),
      grfPush φ (mem_levelSet_one_of_src hx) hx hy a.val = b.val}

namespace GrFHom

/-- The identity `(x, a) → (x, a)`: the unit `1_x`. -/
def id (a : GrFObj A) : GrFHom a a :=
  ⟨A.X.unit (A.X.PObj.levelVal 1 a.pt), (A.X.src_unit _).symm, (A.X.tgt_unit _).symm,
    grfPush_unit _ a.val⟩

lemma src_eq {a b : GrFObj A} (f : GrFHom a b) : A.X.PObj.levelVal 1 a.pt = A.X.src f.1 :=
  f.2.1

lemma tgt_eq {a b : GrFObj A} (f : GrFHom a b) : A.X.PObj.levelVal 1 b.pt = A.X.tgt f.1 :=
  f.2.2.1

lemma push_eq {a b : GrFObj A} (f : GrFHom a b) :
    grfPush f.1 (mem_levelSet_one_of_src f.src_eq) f.src_eq f.tgt_eq a.val = b.val :=
  f.2.2.2

/-- The composite `g ∘ f`, by the composition of `X` (well defined by `grfPush_comp`). -/
def comp {a b c : GrFObj A} (f : GrFHom a b) (g : GrFHom b c) : GrFHom a c :=
  ⟨A.X.comp g.1 f.1, f.src_eq.trans (A.X.src_comp g.1 f.1 (g.src_eq.symm.trans f.tgt_eq)).symm,
    g.tgt_eq.trans (A.X.tgt_comp g.1 f.1 (g.src_eq.symm.trans f.tgt_eq)).symm, by
      rw [grfPush_comp (mem_levelSet_one_of_src f.src_eq) (mem_levelSet_one_of_src g.src_eq)
        f.src_eq f.tgt_eq g.src_eq g.tgt_eq, f.push_eq, g.push_eq]⟩

lemma id_comp {a b : GrFObj A} (f : GrFHom a b) : comp (id a) f = f :=
  Subtype.ext (GroupoidStr.comp_unit_of_eq (G := A.X.toGroupoidStr) f.src_eq.symm)

lemma comp_id {a b : GrFObj A} (f : GrFHom a b) : comp f (id b) = f :=
  Subtype.ext (GroupoidStr.unit_comp_of_eq (G := A.X.toGroupoidStr) f.tgt_eq.symm)

lemma assoc {a b c d : GrFObj A} (f : GrFHom a b) (g : GrFHom b c) (h : GrFHom c d) :
    comp (comp f g) h = comp f (comp g h) :=
  Subtype.ext (A.X.comp_assoc h.1 g.1 f.1 (h.src_eq.symm.trans g.tgt_eq)
    (g.src_eq.symm.trans f.tgt_eq)).symm

end GrFHom

/-- **`GrF(X)` is a category** (2021 p. 683): composition is the composition `m` of `X`, the
identities are the units. -/
instance GrFObj.instCategory : Category.{u} (GrFObj A) where
  Hom := GrFHom
  id := GrFHom.id
  comp := GrFHom.comp
  id_comp := GrFHom.id_comp
  comp_id := GrFHom.comp_id
  assoc := GrFHom.assoc

@[simp] lemma GrFObj.comp_val {a b c : GrFObj A} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g : GrFHom a c).1 = A.X.comp (g : GrFHom b c).1 (f : GrFHom a b).1 := rfl

@[simp] lemma GrFObj.id_val (a : GrFObj A) :
    (𝟙 a : GrFHom a a).1 = A.X.unit (A.X.PObj.levelVal 1 a.pt) := rfl

/-- The object `(x, 0)` of `GrF(X)`. -/
def GrFObj.zero (x : A.X.PObj.Level 1) : GrFObj A := ⟨x, 0⟩

/-- **Every morphism `φ : x → y` of `X` gives `(x, a) ⟶ (y, φ_* a)`** in `GrF(X)`. -/
def grfHomOfMor (φ : A.Mor) {x y : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x = A.X.src φ)
    (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ) (a : GrF x) :
    (⟨x, a⟩ : GrFObj A) ⟶ ⟨y, grfPush φ (mem_levelSet_one_of_src hx) hx hy a⟩ :=
  (⟨φ, hx, hy, rfl⟩ : GrFHom _ _)

/-- **The projection `GrF(X) → X`**, `(x, a) ↦ x`, `φ ↦ φ`. -/
def grfProj : GrFObj A ⥤ A.X.toGroupoidStr.Ob where
  obj a := A.X.toGroupoidStr.toOb (A.X.PObj.levelVal 1 a.pt)
  map {a b} f := GroupoidStr.homMk (G := A.X.toGroupoidStr) (f : GrFHom a b).1
    (GrFHom.src_eq f).symm (GrFHom.tgt_eq f).symm
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ### Theorem 15.1.1: `T(f, Λ)` is a section functor of `GrF(X) → X` -/

/-- **Theorem 15.1.1 (2021 p. 684), the functor property, as a functor**: for an sc-Fredholm
section functor `f` and an sc⁺-multisection `Λ`, `x ↦ (x, T(f, Λ)(x))`, `φ ↦ φ` is a functor
from the groupoid `X₁` to `GrF(X)` (`theorem_15_1_1_functor` gives the morphisms). -/
def linearizationFunctor {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) :
    A.X.liftOne.toGroupoidStr.Ob ⥤ GrFObj A where
  obj x := ⟨x, linearization f Λ x⟩
  map {x y} φ := ⟨A.X.PMor.levelVal 1 φ.1,
    by
      have h : φ.1 ∈ A.X.liftOne.mor x y := φ.2
      have hx : A.X.PObj.levelVal 1 x = A.X.src (A.X.PMor.levelVal 1 φ.1) :=
        (congrArg (A.X.PObj.levelVal 1) h.1).symm
      have hy : A.X.PObj.levelVal 1 y = A.X.tgt (A.X.PMor.levelVal 1 φ.1) :=
        (congrArg (A.X.PObj.levelVal 1) h.2).symm
      exact ⟨hx, hy, (theorem_15_1_1_functor hf hΛ _ hx hy).symm⟩⟩
  map_id _ := rfl
  map_comp {x y z} φ ψ := Subtype.ext (A.X.liftOne_comp_val (φ := ψ.1) (ψ := φ.1)
    (ψ.2.1.trans φ.2.2.symm))

/-- `T(f, Λ)` is a section: composed with the projection it is `x ↦ x`. -/
theorem linearizationFunctor_comp_grfProj_obj {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (x : A.X.liftOne.toGroupoidStr.Ob) :
    (linearizationFunctor hf hΛ ⋙ grfProj).obj x =
      A.X.toGroupoidStr.toOb (A.X.PObj.levelVal 1 (show A.X.PObj.Level 1 from x)) := rfl

/-- The value of the functor is `T(f, Λ)(x)`. -/
theorem linearizationFunctor_obj {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (x : A.X.liftOne.toGroupoidStr.Ob) :
    ((linearizationFunctor hf hΛ).obj x).val = linearization f Λ x := rfl

/-! ### Witness: `ℝⁿ × ℝᵏ → ℝⁿ` -/

/-- **Witness**: on `ℝⁿ × ℝᵏ → ℝⁿ` (Chapter 10's `epSEP`) `GrF(X)` has the object `(0, 0)`. -/
def grfObj_epSEP (n k : ℕ) : GrFObj (StrongBundleEquivalenceExamples.epSEP n k) :=
  GrFObj.zero ((StrongBundleEquivalenceExamples.epSEP n k).X.PObj.levelMk 1 (0 : Fin n → ℝ) (by
    change (0 : Fin n → ℝ) ∈ (rnPolyfold n).levelSet 1
    rw [rnPolyfold_levelSet]; trivial))

/-- **Witness**: the identity morphism of `(0, 0)`, i.e. `GrF(X)` is a nonempty category. -/
theorem nonempty_grfHom_epSEP (n k : ℕ) :
    Nonempty (grfObj_epSEP n k ⟶ grfObj_epSEP n k) := ⟨𝟙 _⟩

end SBLocalization

end Polyfold
