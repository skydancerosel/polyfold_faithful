import Polyfold.Chapter9.GapP2_E3_FormEvalInfty
import Polyfold.Chapter5.PartitionsOfUnity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.5,
**Theorem 9.5.18, proof, p. 451: `ω_k = β_k ω`**, with `(β_k)` an sc-smooth partition of unity
of the ep-groupoid (Definition 7.5.5) and `ω` an sc-differential form of the ep-groupoid
(Definition 8.2.1).  Numbers and pages are the 2021 text's.

# The product of an invariant sc-smooth function with a form of an ep-groupoid

## What is formalized

* `MPolyfold.formSmulFun β ω`, the pointwise product `(βω)_x = β(x) ω_x` of a function
  `β : X → ℝ` and a family `ω` of alternating forms on the tangent spaces;
  `formSmulFun_mem_scForms`: **`βω ∈ Ωᵏ(X)` for `β` sc-smooth and `ω ∈ Ωᵏ(X)`** (Definition
  4.4.1; in a chart the representative is `(β ∘ φ⁻¹ ∘ π) · ω_φ`, `chartForm_formSmulFun`);
  `formLower_formSmulFun` (the product commutes with the pull-back to `X¹`).
* `EpGroupoid.formSmulFun_mem_epForms`: **`βω ∈ Ωᵏ_ep(X)` for `ω ∈ Ωᵏ_ep(X)` and `β` sc-smooth
  with `β(s(φ)) = β(t(φ))` for all morphisms `φ`** (Definition 8.2.1).
* For a bundled ep-groupoid `A`: `EP.levelBase` (the inclusion `Xⁱ → X` on objects),
  `EP.liftFun β i = β|Xⁱ` with `isScSmoothMap_liftFun`, `liftFun_src_eq_tgt`;
  `EP.epFormsSmul : Ωᵏ_ep(Xⁱ) → Ωᵏ_ep(Xⁱ)`, commuting with the directed system
  (`epFormsSmul_epFormsStep`, `epFormsSmul_epFormsMap`), and
  **`EP.epFormsInftySmul : Ωᵏ_{ep,∞}(X) → Ωᵏ_{ep,∞}(X)`**, `[ω] ↦ [βω]`
  (`epFormsInftySmul_of`).
* **`EP.epFormsInftyEval_epFormsInftySmul`**: on the tangent space `T_yN` of a smooth
  finite-dimensional submanifold `N`, `(βω)(α) = β(y) ω(α)`.
* **`EP.sum_epFormsInftySmul`**: `∑ₖ β_k ω = ω` if `∑ₖ β_k = 1` (a finite family).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {φ : MChart X} {k n : ℕ}

/-- **The product `βω`** of a function `β : X → ℝ` and a family `ω` of alternating forms on the
tangent spaces: `(βω)_x = β(x) ω_x` (2021 Theorem 9.5.18, proof, p. 451: `ω_k = β_k ω`). -/
def formSmulFun (β : X → ℝ) (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ :=
  fun x => β (P.levelVal 1 x) • ω x

lemma formSmulFun_apply (β : X → ℝ) (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (x : P.Level 1) (a : Fin k → P.tangentFiber x) :
    formSmulFun β ω x a = β (P.levelVal 1 x) * ω x a := rfl

lemma formSmulFun_add (β : X → ℝ) (ω τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formSmulFun β (ω + τ) = formSmulFun β ω + formSmulFun β τ :=
  funext fun x => smul_add (β (P.levelVal 1 x)) (ω x) (τ x)

lemma formSmulFun_smul (β : X → ℝ) (c : ℝ)
    (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formSmulFun β (c • ω) = c • formSmulFun β ω :=
  funext fun x => smul_comm (β (P.levelVal 1 x)) c (ω x)

/-- **The local representative of `βω`**: `(βω)_φ(y, h) = β(φ⁻¹(y)) ω_φ(y, h)`. -/
theorem chartForm_formSmulFun (hφ : P.IsChart φ) (β : X → ℝ)
    (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) (q : (φ.model.E.whitney k) 0) :
    chartForm hφ (formSmulFun β ω) q =
      β (φ.symm (φ.model.E.toBase 1 q.1)) * chartForm hφ ω q := by
  unfold chartForm
  split_ifs with hq
  · rfl
  · rw [mul_zero]

/-- The base point `(y, h₁, …, h_k) ↦ y` (read in `E₀`) is sc-smooth from `⊕ₖ TO` to `O`. -/
theorem isScSmoothRetractMap_whitneyBase {E : ScBanach} {C O : Set (E 0)}
    (hO : IsScRetract E C O) (k : ℕ) :
    IsScSmoothRetractMap (E.whitney k) (E.whitneySet k C) (retractWhitney E C O k) E C O
      fun q => E.toBase 1 q.1 :=
  (E.shiftIncl.comp (ScBanach.prodFstOp E.shift (E.fiberPow k))).isScSmoothRetractMap
    (hO.whitney k) fun _ hq => hq.1

/-- **2021 Theorem 9.5.18, proof, p. 451 (`ω_k = β_k ω`): the product of an sc-smooth function
and an sc-differential form (Definition 4.4.1) is an sc-differential form.** -/
theorem formSmulFun_mem_scForms {β : X → ℝ} (hβ : P.IsScSmoothMap realPolyfold β)
    {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hω : ω ∈ P.scForms k) :
    formSmulFun β ω ∈ P.scForms k := fun φ hφ => by
  have h1 := (hβ.real_chart hφ).comp (isScSmoothRetractMap_whitneyBase φ.model.isScRetract k)
    φ.model.isScRetract
  have h2 : IsScSmoothRetractMap (φ.model.E.whitney k) (φ.model.E.whitneySet k φ.model.C)
      (retractWhitney φ.model.E φ.model.C φ.model.O k) realSc univ univ (chartForm hφ ω) :=
    hω hφ
  exact (h1.real_mul h2).congr fun q _ => (chartForm_formSmulFun hφ β ω q).symm

/-- The product commutes with the pull-back along `X¹ → X`: `ι^*(βω) = (β ∘ ι) ι^*ω`. -/
theorem formLower_formSmulFun (β : X → ℝ)
    (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formLower (formSmulFun β ω) = formSmulFun (β ∘ P.levelVal 1) (formLower ω) := rfl

/-- `β|X¹` is sc-smooth on `X¹`. -/
theorem IsScSmoothMap.real_comp_levelVal {β : X → ℝ} (hβ : P.IsScSmoothMap realPolyfold β) :
    P.shift.IsScSmoothMap realPolyfold (β ∘ P.levelVal 1) :=
  hβ.comp (remark_4_1_3_levelVal P)

/-- The values of `βω` on tangent vectors over the point `y`: `(βω)(α) = β(y) ω(α)`. -/
theorem evalFamily_formSmulFun (β : X → ℝ)
    (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin n]→ₗ[ℝ] ℝ) {y : X}
    {α : Fin n → P.TangentSpace} (hα : ∀ i, P.levelVal 1 (P.tangentProj (α i)) = y) :
    evalFamily (formSmulFun β ω) α = β y * evalFamily ω α := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [evalFamily_of_eq_zero hn, evalFamily_of_eq_zero hn, mul_zero]
  obtain ⟨x, a, hx, ha⟩ := exists_fiber_lift hα hn
  obtain rfl : (fun i => (a i : P.TangentSpace)) = α := funext ha
  rw [evalFamily_eq hn, evalFamily_eq hn, formSmulFun_apply, hx]

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor) {k : ℕ}

/-- **2021 Theorem 9.5.18, proof, p. 451 (`ω_k = β_k ω`): for an sc-smooth function `β` on the
objects which is constant on the orbits (as the functions of an sc-smooth partition of unity of
the ep-groupoid, Definition 7.5.5) and `ω ∈ Ωᵏ_ep(X)` (Definition 8.2.1), `βω ∈ Ωᵏ_ep(X)`.** -/
theorem formSmulFun_mem_epForms {β : Obj → ℝ} (hβ : X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : Mor, β (X.src φ) = β (X.tgt φ))
    {ω : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hω : ω ∈ X.epForms k) :
    MPolyfold.formSmulFun β ω ∈ X.epForms k := by
  refine ⟨MPolyfold.formSmulFun_mem_scForms hβ hω.1, fun φ hφ x y hx hy => ?_⟩
  ext a
  have h := IsMorCompatible.apply X hω.2 hφ hx hy a
  change β (X.PObj.levelVal 1 y) * ω y (fun i => X.tangentMorCLE hφ hx hy (a i)) =
    β (X.PObj.levelVal 1 x) * ω x a
  rw [h, hx, hy, hinv φ]

end EpGroupoid

namespace EP

variable (A : EP.{u}) (β : A.Obj → ℝ) (k : ℕ) {n : ℕ}

/-- The inclusion `Xⁱ → X` on objects. -/
def levelBase : ∀ i : ℕ, (A.lift i).Obj → A.Obj
  | 0 => id
  | i + 1 => levelBase i ∘ (A.lift i).X.PObj.levelVal 1

/-- The restriction `β|Xⁱ` of a function on the objects to the objects of `Xⁱ`. -/
def liftFun (i : ℕ) : (A.lift i).Obj → ℝ := β ∘ A.levelBase i

lemma liftFun_zero : A.liftFun β 0 = β := rfl

lemma liftFun_succ (i : ℕ) :
    A.liftFun β (i + 1) = A.liftFun β i ∘ (A.lift i).X.PObj.levelVal 1 := rfl

variable {β}

/-- `β|Xⁱ` is sc-smooth on `Xⁱ`. -/
theorem isScSmoothMap_liftFun (hβ : A.X.PObj.IsScSmoothMap realPolyfold β) :
    ∀ i : ℕ, (A.lift i).X.PObj.IsScSmoothMap realPolyfold (A.liftFun β i)
  | 0 => hβ
  | i + 1 => MPolyfold.IsScSmoothMap.real_comp_levelVal (isScSmoothMap_liftFun hβ i)

/-- `β|Xⁱ` is constant on the orbits of `Xⁱ`. -/
theorem liftFun_src_eq_tgt (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) :
    ∀ (i : ℕ) (φ : (A.lift i).Mor),
      A.liftFun β i ((A.lift i).X.src φ) = A.liftFun β i ((A.lift i).X.tgt φ)
  | 0, φ => hinv φ
  | i + 1, φ => liftFun_src_eq_tgt hinv i ((A.lift i).X.PMor.levelVal 1 φ)

variable (β)

/-- **`ω ↦ βω` on `Ωᵏ_ep(Xⁱ)`** (2021 Theorem 9.5.18, proof, p. 451: `ω_k = β_k ω`), for `β`
sc-smooth and constant on the orbits (Definition 7.5.5). -/
def epFormsSmul (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (i : ℕ) :
    A.epForms k i →ₗ[ℝ] A.epForms k i where
  toFun ω := ⟨MPolyfold.formSmulFun (A.liftFun β i) ω.1,
    (A.lift i).X.formSmulFun_mem_epForms (A.isScSmoothMap_liftFun hβ i)
      (A.liftFun_src_eq_tgt hinv i) ω.2⟩
  map_add' ω τ := Subtype.ext (MPolyfold.formSmulFun_add _ ω.1 τ.1)
  map_smul' c ω := Subtype.ext (MPolyfold.formSmulFun_smul _ c ω.1)

variable {β}

lemma coe_epFormsSmul (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (i : ℕ) (ω : A.epForms k i) :
    (A.epFormsSmul β k hβ hinv i ω).1 = MPolyfold.formSmulFun (A.liftFun β i) ω.1 := rfl

/-- The product commutes with the steps of the directed system. -/
theorem epFormsSmul_epFormsStep (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (i : ℕ) (ω : A.epForms k i) :
    A.epFormsSmul β k hβ hinv (i + 1) (A.epFormsStep k i ω) =
      A.epFormsStep k i (A.epFormsSmul β k hβ hinv i ω) :=
  Subtype.ext (MPolyfold.formLower_formSmulFun (A.liftFun β i) ω.1).symm

/-- The product commutes with the maps of the directed system. -/
theorem epFormsSmul_epFormsMap (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) {i j : ℕ} (h : i ≤ j)
    (ω : A.epForms k i) :
    A.epFormsSmul β k hβ hinv j (A.epFormsMap k i j h ω) =
      A.epFormsMap k i j h (A.epFormsSmul β k hβ hinv i ω) := by
  induction j, h using Nat.le_induction with
  | base => rw [epFormsMap_self]; rfl
  | succ j hij ih =>
    rw [epFormsMap_succ A k hij, LinearMap.comp_apply, epFormsSmul_epFormsStep, ih,
      LinearMap.comp_apply]

variable (β)

/-- **2021 Theorem 9.5.18, proof, p. 451: `ω ↦ βω` on `Ωᵏ_{ep,∞}(X)`** (`ω_k = β_k ω`), for an
sc-smooth function `β` on the objects which is constant on the orbits (the functions of an
sc-smooth partition of unity of the ep-groupoid, Definition 7.5.5): `β[ω] = [βω]`. -/
def epFormsInftySmul (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) :
    A.epFormsInfty k →ₗ[ℝ] A.epFormsInfty k :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(A.epForms k i)) (A.epFormsMap k)
    (fun i => (A.epFormsInftyOf k i).comp (A.epFormsSmul β k hβ hinv i)) fun i j h ω => by
      simp only [LinearMap.comp_apply]
      rw [epFormsSmul_epFormsMap, epFormsInftyOf_epFormsMap]

variable {β}

/-- `β[ω] = [βω]`. -/
theorem epFormsInftySmul_of (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (i : ℕ) (ω : A.epForms k i) :
    A.epFormsInftySmul β k hβ hinv (A.epFormsInftyOf k i ω) =
      A.epFormsInftyOf k i (A.epFormsSmul β k hβ hinv i ω) :=
  Module.DirectLimit.lift_of _ _ _

/-! ### The values of `βω` -/

/-- If on the tangent spaces `T_yN`, `y ∈ N`, of the submanifolds of `Xⁱ` the evaluation `g` is
`β(y)` times `f`, the same holds for the evaluations read on the tangent vectors of `X`. -/
theorem lowerEvIter_mul_fun (β : A.Obj → ℝ) :
    ∀ (i : ℕ) {f g : (Fin n → (A.lift i).X.PObj.TangentSpace) → ℝ},
      (∀ (N : Set (A.lift i).Obj) (y : (A.lift i).Obj), (A.lift i).X.PObj.IsSmoothSubmanifold N →
        y ∈ N → ∀ γ : Fin n → (A.lift i).X.PObj.TangentSpace,
        (∀ j, γ j ∈ (A.lift i).X.PObj.submanifoldTangent N y) →
        g γ = A.liftFun β i y * f γ) →
      ∀ {N : Set A.Obj} {y : A.Obj}, A.X.PObj.IsSmoothSubmanifold N → y ∈ N →
      ∀ {α : Fin n → A.X.PObj.TangentSpace}, (∀ j, α j ∈ A.X.PObj.submanifoldTangent N y) →
      A.lowerEvIter i g α = β y * A.lowerEvIter i f α
  | 0, _, _, h, N, y, hN, hy, α, hα => h N y hN hy α hα
  | i + 1, f, g, h, _, _, hN, hy, _, hα =>
    lowerEvIter_mul_fun β i (fun N' y' hN' hy' γ hγ => by
      choose δ hδ hδm using fun j =>
        MPolyfold.exists_tangentLower_eq_of_mem_submanifoldTangent hN' (hγ j)
      rw [MPolyfold.lowerEv_eq g δ hδ, MPolyfold.lowerEv_eq f δ hδ,
        h _ ((A.lift i).X.PObj.levelMk 1 y' (hN'.mem_levelSet_one hy')) hN'.levelOne hy' δ hδm]
      rfl) hN hy hα

/-- **2021 Theorem 9.5.18, proof, p. 451 (`ω_k = β_k ω`): the values of `βω`** on the tangent
space `T_yN` of a smooth finite-dimensional submanifold `N` of the object M-polyfold:
`(βω)(α₁, …, αₙ) = β(y) ω(α₁, …, αₙ)`. -/
theorem epFormsInftyEval_epFormsInftySmul (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (a : A.epFormsInfty n) {N : Set A.Obj}
    (hN : A.X.PObj.IsSmoothSubmanifold N) {y : A.Obj} (hy : y ∈ N)
    {α : Fin n → A.X.PObj.TangentSpace} (hα : ∀ i, α i ∈ A.X.PObj.submanifoldTangent N y) :
    (A.epFormsInftyEval n).ev (A.epFormsInftySmul β n hβ hinv a) α =
      β y * (A.epFormsInftyEval n).ev a α := by
  obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq n a
  have ht : A.IsEvalTuple α := Or.inl ⟨N, y, hN, hy, hα⟩
  rw [epFormsInftySmul_of, epFormsInftyEval_of, epFormsInftyEval_of,
    A.epFormsLevelEval_ev n i _ ht, A.epFormsLevelEval_ev n i _ ht]
  exact A.lowerEvIter_mul_fun β i (fun _ _ _ _ γ hγ =>
    MPolyfold.evalFamily_formSmulFun (A.liftFun β i) ω.1
      fun j => MPolyfold.levelVal_tangentProj_of_mem (hγ j)) hN hy hα

/-! ### Partitions of unity -/

/-- **2021 Theorem 9.5.18, proof, p. 451: `∑ₖ β_k ω = ω`** on `Ωᵏ_ep(Xⁱ)` for finitely many
sc-smooth invariant functions with `∑ₖ β_k = 1`. -/
theorem sum_epFormsSmul {ι : Type*} (s : Finset ι) (b : ι → A.Obj → ℝ)
    (hb : ∀ j, A.X.PObj.IsScSmoothMap realPolyfold (b j))
    (hinv : ∀ j, ∀ φ : A.Mor, b j (A.X.src φ) = b j (A.X.tgt φ))
    (hsum : ∀ x, ∑ j ∈ s, b j x = 1) (i : ℕ) (ω : A.epForms k i) :
    ∑ j ∈ s, A.epFormsSmul (b j) k (hb j) (hinv j) i ω = ω := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  funext x
  rw [Finset.sum_apply]
  change ∑ j ∈ s, b j (A.levelBase i ((A.lift i).X.PObj.levelVal 1 x)) • ω.1 x = ω.1 x
  rw [← Finset.sum_smul, hsum, one_smul]

/-- **2021 Theorem 9.5.18, proof, p. 451: `ω = ∑ₖ β_k ω`** in `Ωᵏ_{ep,∞}(X)`, for finitely many
sc-smooth functions `β_k` on the objects, constant on the orbits, with `∑ₖ β_k = 1` (a finite
sc-smooth partition of unity of the ep-groupoid, Definition 7.5.5). -/
theorem sum_epFormsInftySmul {ι : Type*} (s : Finset ι) (b : ι → A.Obj → ℝ)
    (hb : ∀ j, A.X.PObj.IsScSmoothMap realPolyfold (b j))
    (hinv : ∀ j, ∀ φ : A.Mor, b j (A.X.src φ) = b j (A.X.tgt φ))
    (hsum : ∀ x, ∑ j ∈ s, b j x = 1) (a : A.epFormsInfty k) :
    ∑ j ∈ s, A.epFormsInftySmul (b j) k (hb j) (hinv j) a = a := by
  obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq k a
  simp only [epFormsInftySmul_of]
  rw [← map_sum, A.sum_epFormsSmul k s b hb hinv hsum i ω]

end EP

end Polyfold
