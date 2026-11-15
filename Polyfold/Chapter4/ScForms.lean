import Polyfold.Chapter2.TangentLiftAll
import Polyfold.Chapter2.TangentSpaceLinear

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4
"Sc-Differential Forms" (p. 195): the Whitney sum `⊕ₖ TX` ("an easy exercise"),
**Definition 4.4.1**, the directed system **(4.4)** and **Definition 4.4.2** (2017 / preprint:
Definition 4.25).  Numbers and pages are the 2021 text's.

# Sc-differential forms and the direct limit `Ωᵏ_∞(X)`

## The text, paraphrased

(p. 195) The Whitney sum `TX ⊕ ⋯ ⊕ TX → X¹` of `k` copies of the tangent bundle is an sc-smooth
bundle.  (Definition 4.4.1) An sc-differential `k`-form is an sc-smooth map `ω : ⊕ₖ TX → ℝ`,
linear in each argument and skew-symmetric; they form the vector space `Ωᵏ(X)`.  Pulling back by
the inclusions `X^{i+1} → X^i` gives the directed system (4.4) `Ωᵏ(X) → ⋯ → Ωᵏ(Xⁱ) → Ωᵏ(Xⁱ⁺¹)
→ ⋯`, with direct limit the vector space `Ωᵏ_∞(X)`.  (Definition 4.4.2) Its elements are the
sc-differential `k`-forms on `X_∞`; `Ω*_∞(X) = ⊕ₖ Ωᵏ_∞(X)`.

## What is formalized

* **The Whitney sum in a local model.**  `ScBanach.fiberPow E k` (`E ⊕ ⋯ ⊕ E` as an iterated
  product, with `fiberVecL`/`fiberPackL : (E^k)_m ≅ (Fin k → E_m)`), `ScBanach.whitney E k =
  E¹ ⊕ E^k`, `whitneySet k U = U¹ ⊕ E^k`, `retractWhitney E C O k = ⊕ₖ TO`.
  `ScRetraction.whitney`, `IsScRetract.whitney`: **`⊕ₖ TO` is an sc-retract** (of `⊕ₖ Tr`);
  `IsScSmoothRetractMap.whitney`: **`⊕ₖ Tf` is sc-smooth** for `f` sc-smooth between retracts.
  This is the text's exercise in the charts `⊕ₖ Tφ`.
* **Definition 4.4.1 in a local model**: `IsRetractScForm E C O k ω` (sc-smooth on `⊕ₖ TO`,
  alternating `k`-linear on each `(T_xO)^k`).
* **Definition 4.4.1 on an M-polyfold**: a form is a family `ω(x)` of alternating `k`-linear maps
  on the tangent spaces `T_xX`, `x ∈ X¹` (whose linear structure is `TangentSpaceLinear.lean`);
  `chartForm hφ ω : ⊕ₖ TO → ℝ` is its representative in the chart `⊕ₖ Tφ` (`chartForm_eq`), and
  `MPolyfold.IsScForm P k ω` asks it to be sc-smooth in every chart of the maximal atlas.
  `chartForm_transition` (chart change), `isScForm_of_cover` (a covering family of charts
  suffices), `IsScForm.isRetractScForm` (the representatives are local forms).
  `MPolyfold.scForms P k : Submodule ℝ _` is **the vector space `Ωᵏ(X)`**; witness
  `constForm_mem_scForms` (constant `0`-forms).
* **The pull-back along `X¹ → X`**: `lowerFiberCLM x : T_x(X¹) →L T_xX` (the inclusion
  `tangentLower` on fibres), `formLower`, `formLowerₗ`, and `formLower_mem_scForms`: pull-backs of
  sc-forms are sc-forms (`chartForm_formLower`: in level charts it is `ω_φ ∘ (⊕ₖ T(O¹) → ⊕ₖ TO)`,
  `isScSmoothRetractMap_whitneyIncl`).
* **(4.4) and Definition 4.4.2**: `BundledMPolyfold.forms A k i = Ωᵏ(Xⁱ)`, `formsStep`,
  `formsMap` (the directed system, `directedSystem_forms`), `formsInfty A k = Ωᵏ_∞(X)` (Mathlib's
  `Module.DirectLimit`), `formsInftyOf` (the class `[ω]`, `formsInftyOf_formsMap`),
  `formsInftyGraded A = Ω*_∞(X)` (a `DirectSum`).

## The reading

* "An sc-smooth map `⊕ₖ TX → ℝ`" is read in the charts `⊕ₖ Tφ`, `φ` in the maximal atlas of `X`:
  these are the charts of the Whitney sum as an M-polyfold, which is not built as a separate
  object.  The fibrewise conditions are built into the type (alternating maps on `T_xX`).
* In `IsRetractScForm` the fibre condition is phrased as agreement on `(T_xO)^k` with an
  alternating map on `E^k`, equivalent since `T_xO` has a linear complement.
-/
open Set Function

noncomputable section

namespace Polyfold

/-! ### The fibre `E ⊕ ⋯ ⊕ E` of the Whitney sum -/

namespace ScBanach

/-- The `k`-fold direct sum `E ⊕ ⋯ ⊕ E` (the fibre of the Whitney sum of `k` copies of `TE`), as an
iterated product `E ⊕ (E ⊕ (⋯ ⊕ 0))`. -/
def fiberPow (E : ScBanach) : ℕ → ScBanach
  | 0 => ScBanach.const (Fin 0 → ℝ)
  | k + 1 => E.prod (E.fiberPow k)

variable (E : ScBanach)

@[simp] lemma fiberPow_zero : E.fiberPow 0 = ScBanach.const (Fin 0 → ℝ) := rfl
@[simp] lemma fiberPow_succ (k : ℕ) : E.fiberPow (k + 1) = E.prod (E.fiberPow k) := rfl

/-- The `k` vectors of a point of `E^k` on level `m`. -/
def fiberVecL (m : ℕ) : ∀ k, (E.fiberPow k) m →L[ℝ] (Fin k → E m)
  | 0 => 0
  | k + 1 => ContinuousLinearMap.pi fun i : Fin (k + 1) =>
      Fin.cases (motive := fun _ => (E.fiberPow (k + 1)) m →L[ℝ] E m)
        (ContinuousLinearMap.fst ℝ (E m) ((E.fiberPow k) m))
        (fun j => (ContinuousLinearMap.proj j).comp
          ((fiberVecL m k).comp (ContinuousLinearMap.snd ℝ (E m) ((E.fiberPow k) m)))) i

/-- The point of `E^k` on level `m` with the given `k` vectors. -/
def fiberPackL (m : ℕ) : ∀ k, (Fin k → E m) →L[ℝ] (E.fiberPow k) m
  | 0 => 0
  | k + 1 => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + 1) => E m) 0).prod
      ((fiberPackL m k).comp (ContinuousLinearMap.pi fun j : Fin k =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + 1) => E m) j.succ))

variable {E}

@[simp] lemma fiberVecL_succ_zero {m k : ℕ} (p : (E.fiberPow (k + 1)) m) :
    E.fiberVecL m (k + 1) p 0 = p.1 := rfl

@[simp] lemma fiberVecL_succ_succ {m k : ℕ} (p : (E.fiberPow (k + 1)) m) (j : Fin k) :
    E.fiberVecL m (k + 1) p j.succ = E.fiberVecL m k p.2 j := rfl

lemma fiberVecL_succ {m k : ℕ} (p : (E.fiberPow (k + 1)) m) :
    E.fiberVecL m (k + 1) p = Fin.cons p.1 (E.fiberVecL m k p.2) := by
  ext i; refine Fin.cases rfl (fun j => rfl) i

@[simp] lemma fiberPackL_succ_fst {m k : ℕ} (v : Fin (k + 1) → E m) :
    (E.fiberPackL m (k + 1) v).1 = v 0 := rfl

@[simp] lemma fiberPackL_succ_snd {m k : ℕ} (v : Fin (k + 1) → E m) :
    (E.fiberPackL m (k + 1) v).2 = E.fiberPackL m k (Fin.tail v) := rfl

@[simp] lemma fiberVecL_fiberPackL {m : ℕ} : ∀ {k} (v : Fin k → E m),
    E.fiberVecL m k (E.fiberPackL m k v) = v
  | 0, v => funext fun i => i.elim0
  | k + 1, v => by
    rw [fiberVecL_succ, fiberPackL_succ_fst, fiberPackL_succ_snd, fiberVecL_fiberPackL]
    exact Fin.cons_self_tail v

@[simp] lemma fiberPackL_fiberVecL {m : ℕ} : ∀ {k} (p : (E.fiberPow k) m),
    E.fiberPackL m k (E.fiberVecL m k p) = p
  | 0, p => Subsingleton.elim (α := Fin 0 → ℝ) _ _
  | k + 1, p => by
    refine Prod.ext rfl ?_
    rw [fiberPackL_succ_snd, fiberVecL_succ, Fin.tail_cons, fiberPackL_fiberVecL]

/-- `E^k ≅ (Fin k → E)` on level `m`. -/
def fiberEquivL (m k : ℕ) : (E.fiberPow k) m ≃L[ℝ] (Fin k → E m) :=
  ContinuousLinearEquiv.equivOfInverse (E.fiberVecL m k) (E.fiberPackL m k)
    fiberPackL_fiberVecL fiberVecL_fiberPackL

/-- The vectors commute with the inclusions of the levels. -/
lemma fiberVecL_incl {m : ℕ} : ∀ {k} (p : (E.fiberPow k) (m + 1)) (i : Fin k),
    E.fiberVecL m k ((E.fiberPow k).incl m p) i = E.incl m (E.fiberVecL (m + 1) k p i)
  | 0, _, i => i.elim0
  | k + 1, p, i => by
    refine Fin.cases rfl (fun j => ?_) i
    rw [fiberVecL_succ_succ, fiberVecL_succ_succ]
    exact fiberVecL_incl (k := k) p.2 j

lemma fiberVecL_toBase {m k : ℕ} (p : (E.fiberPow k) m) (i : Fin k) :
    E.fiberVecL 0 k ((E.fiberPow k).toBase m p) i = E.toBase m (E.fiberVecL m k p i) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [ScScale.toBase_succ, ScScale.toBase_succ, ih, fiberVecL_incl]

end ScBanach

/-! ### The Whitney sum `⊕ₖ TE` and the maps `⊕ₖ Tg` -/

namespace ScBanach

/-- The ambient sc-Banach space `E¹ ⊕ E^k` of the Whitney sum `TE ⊕ ⋯ ⊕ TE` (`k` copies, over
`E¹`): a point is `(y, h₁, …, h_k)` with `y ∈ E₁`, `hᵢ ∈ E₀`. -/
abbrev whitney (E : ScBanach) (k : ℕ) : ScBanach := E.shift.prod (E.fiberPow k)

/-- `U¹ ⊕ E^k ⊆ E¹ ⊕ E^k`, the Whitney sum of `k` copies of `TU = U¹ ⊕ E`. -/
def whitneySet (E : ScBanach) (k : ℕ) (U : Set (E 0)) : Set ((E.whitney k) 0) :=
  E.lvlSet U 1 ×ˢ univ

/-- The `k` vectors `(h₁, …, h_k)` of a point of `E¹ ⊕ E^k`. -/
abbrev whitneyVec {E : ScBanach} {k : ℕ} (q : (E.whitney k) 0) : Fin k → E 0 :=
  E.fiberVecL 0 k q.2

/-- The point `(y, h₁, …, h_k)` of `E¹ ⊕ E^k`. -/
abbrev whitneyMk {E : ScBanach} {k : ℕ} (y : E 1) (v : Fin k → E 0) : (E.whitney k) 0 :=
  (y, E.fiberPackL 0 k v)

@[simp] lemma whitneyVec_mk {E : ScBanach} {k : ℕ} (y : E 1) (v : Fin k → E 0) :
    whitneyVec (whitneyMk y v) = v := fiberVecL_fiberPackL v

lemma mem_whitneySet {E : ScBanach} {k : ℕ} {U : Set (E 0)} {q : (E.whitney k) 0} :
    q ∈ E.whitneySet k U ↔ q.1 ∈ E.lvlSet U 1 := by
  simp [whitneySet]

end ScBanach

variable {E F : ScBanach}

lemma IsPartialQuadrant.whitneySet {C : Set (E 0)} (hC : IsPartialQuadrant E C) (k : ℕ) :
    IsPartialQuadrant (E.whitney k) (E.whitneySet k C) :=
  hC.shift.prod_univ _

lemma IsRelOpenInQuadrant.whitneySet {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    (k : ℕ) : IsRelOpenInQuadrant (E.whitney k) (E.whitneySet k C) (E.whitneySet k U) :=
  hU.shift.prod_univ _

/-- The projection `(y, h₁, h₂, …) ↦ (y, h₁)` of `E¹ ⊕ E^{k+1}` onto `TE`. -/
def ScBanach.whitneyHead (E : ScBanach) (k : ℕ) : ScOperator (E.whitney (k + 1)) E.tangent where
  lvl m := (ContinuousLinearMap.id ℝ (E (m + 1))).prodMap
    (ContinuousLinearMap.fst ℝ (E m) ((E.fiberPow k) m))
  incl_comm _ _ := rfl

/-- The projection `(y, h₁, h₂, …) ↦ (y, h₂, …)` of `E¹ ⊕ E^{k+1}` onto `E¹ ⊕ E^k`. -/
def ScBanach.whitneyTail (E : ScBanach) (k : ℕ) : ScOperator (E.whitney (k + 1)) (E.whitney k) where
  lvl m := (ContinuousLinearMap.id ℝ (E (m + 1))).prodMap
    (ContinuousLinearMap.snd ℝ (E m) ((E.fiberPow k) m))
  incl_comm _ _ := rfl

/-- The fibre part `(y, h₁, …, h_k) ↦ (Dg(y)h₁, …, Dg(y)h_k)` of `⊕ₖ Tg`. -/
def whitneyFib (U : Set (E 0)) (g : E 0 → F 0) : ∀ k, (E.whitney k) 0 → (F.fiberPow k) 0
  | 0 => fun _ => (0 : Fin 0 → ℝ)
  | k + 1 => fun q => (scDeriv U g q.1 q.2.1, whitneyFib U g k (q.1, q.2.2))

/-- **The Whitney sum `⊕ₖ Tg` of the tangent map**:
`(y, h₁, …, h_k) ↦ (g(y), Dg(y)h₁, …, Dg(y)h_k)` (on level `1` in `y`). -/
def whitneyMap (U : Set (E 0)) (g : E 0 → F 0) (k : ℕ) (q : (E.whitney k) 0) : (F.whitney k) 0 :=
  (levelMap g 1 q.1, whitneyFib U g k q)

lemma whitneyVec_whitneyFib (U : Set (E 0)) (g : E 0 → F 0) :
    ∀ (k : ℕ) (q : (E.whitney k) 0) (i : Fin k),
      F.fiberVecL 0 k (whitneyFib U g k q) i = scDeriv U g q.1 (ScBanach.whitneyVec q i)
  | 0, _, i => i.elim0
  | k + 1, q, i => by
    refine Fin.cases rfl (fun j => ?_) i
    exact whitneyVec_whitneyFib U g k (q.1, q.2.2) j

@[simp] lemma whitneyMap_fst (U : Set (E 0)) (g : E 0 → F 0) (k : ℕ) (q : (E.whitney k) 0) :
    (whitneyMap U g k q).1 = levelMap g 1 q.1 := rfl

@[simp] lemma whitneyVec_whitneyMap (U : Set (E 0)) (g : E 0 → F 0) (k : ℕ)
    (q : (E.whitney k) 0) (i : Fin k) :
    ScBanach.whitneyVec (whitneyMap U g k q) i = scDeriv U g q.1 (ScBanach.whitneyVec q i) :=
  whitneyVec_whitneyFib U g k q i

/-- `⊕ₖ Tg` is determined by `g(y)` and the vectors `Dg(y)hᵢ`. -/
lemma whitneyMap_eq_mk (U : Set (E 0)) (g : E 0 → F 0) (k : ℕ) (q : (E.whitney k) 0) :
    whitneyMap U g k q = ScBanach.whitneyMk (levelMap g 1 q.1)
      (fun i => scDeriv U g q.1 (ScBanach.whitneyVec q i)) := by
  refine Prod.ext rfl ?_
  change whitneyFib U g k q = _
  rw [← (F.fiberPackL_fiberVecL (whitneyFib U g k q))]
  congr 1
  funext i
  exact whitneyVec_whitneyFib U g k q i

/-- The fibre part of `⊕ₖ Tg` is sc-smooth on `U¹ ⊕ E^k`. -/
theorem IsScSmooth.whitneyFib {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    {g : E 0 → F 0} (hg : IsScSmooth U g) :
    ∀ k, IsScSmooth (E.whitneySet k U) (Polyfold.whitneyFib U g k)
  | 0 => fun n => IsSck.zero (hU.whitneySet 0).isScDomain n
  | k + 1 => by
    have hS := (hU.whitneySet (k + 1)).isScDomain
    have hT : IsScSmooth (E.tangentSet U) (tangentMap U g) := (isScSmooth_iff.1 hg).2
    have h1 : IsScSmooth (E.whitneySet (k + 1) U)
        ((ScBanach.prodSndOp F.shift F 0) ∘ (tangentMap U g ∘ E.whitneyHead k 0)) :=
      IsScSmooth.comp hS (isScDomain_univ _)
        ((ScBanach.prodSndOp F.shift F).isScSmooth (isScDomain_univ _))
        (IsScSmooth.comp hS hU.isScDomain.tangentSet hT
          ((E.whitneyHead k).isScSmooth hS) fun q hq => (ScBanach.mem_whitneySet.1 hq :))
        (mapsTo_univ _ _)
    have h2 : IsScSmooth (E.whitneySet (k + 1) U)
        (Polyfold.whitneyFib U g k ∘ E.whitneyTail k 0) :=
      IsScSmooth.comp hS (hU.whitneySet k).isScDomain (IsScSmooth.whitneyFib hU hg k)
        ((E.whitneyTail k).isScSmooth hS)
        fun q hq => ScBanach.mem_whitneySet.2 (ScBanach.mem_whitneySet.1 hq)
    exact h1.scPair hS h2

/-- **`⊕ₖ Tg` is sc-smooth** on `U¹ ⊕ E^k` for an sc-smooth `g` on `U`. -/
theorem IsScSmooth.whitneyMap {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    {g : E 0 → F 0} (hg : IsScSmooth U g) (k : ℕ) :
    IsScSmooth (E.whitneySet k U) (Polyfold.whitneyMap U g k) := by
  have hS := (hU.whitneySet k).isScDomain
  have h1 : IsScSmooth (F := F.shift) (E.whitneySet k U)
      ((levelMap g 1 : E.shift 0 → F.shift 0) ∘ (ScBanach.prodFstOp E.shift (E.fiberPow k) 0)) :=
    IsScSmooth.comp hS hU.isScDomain.shift
      (hg.shift hU.isScDomain : IsScSmooth (E := E.shift) (F := F.shift) _ _)
      ((ScBanach.prodFstOp E.shift (E.fiberPow k)).isScSmooth hS)
      fun q hq => (ScBanach.mem_whitneySet.1 hq :)
  exact h1.scPair hS (hg.whitneyFib hU k)

/-! ### The Whitney sum of a retract (2021 p. 195, "an easy exercise", in a local model) -/

/-- **The Whitney sum `⊕ₖ TO`** of the retract `(O, C, E)`:
`{(x, h₁, …, h_k) | x ∈ O₁, hᵢ ∈ T_xO}` inside `E¹ ⊕ E^k`. -/
def retractWhitney (E : ScBanach) (C O : Set (E 0)) (k : ℕ) : Set ((E.whitney k) 0) :=
  {q | q.1 ∈ E.lvlSet O 1 ∧
    ∀ i, ((q.1, ScBanach.whitneyVec q i) : E.tangent 0) ∈ retractTangent E C O}

lemma whitneyMk_fst_vec {k : ℕ} (q : (E.whitney k) 0) :
    ScBanach.whitneyMk q.1 (ScBanach.whitneyVec q) = q :=
  Prod.ext rfl (E.fiberPackL_fiberVecL q.2)

lemma mem_retractWhitney_mk {C O : Set (E 0)} {k : ℕ} {x : E 1} {v : Fin k → E 0} :
    ScBanach.whitneyMk x v ∈ retractWhitney E C O k ↔
      x ∈ E.lvlSet O 1 ∧ ∀ i, ((x, v i) : E.tangent 0) ∈ retractTangent E C O := by
  simp [retractWhitney]

namespace ScRetraction

variable {C : Set (E 0)} (R : ScRetraction E C)

/-- **The Whitney retraction** `⊕ₖ Tr : U¹ ⊕ E^k → U¹ ⊕ E^k`,
`(y, h₁, …, h_k) ↦ (r(y), Dr(y)h₁, …, Dr(y)h_k)`: an sc-smooth retraction onto `⊕ₖ TO`
(`whitney_retract`). -/
def whitney (k : ℕ) : ScRetraction (E.whitney k) (E.whitneySet k C) where
  U := E.whitneySet k R.U
  toFun := whitneyMap R.U R k
  relOpen := R.relOpen.whitneySet k
  mapsTo q hq := ScBanach.mem_whitneySet.2 (R.shift.mapsTo (ScBanach.mem_whitneySet.1 hq))
  isScSmooth := R.isScSmooth.whitneyMap R.relOpen k
  idem q hq := by
    have hy : q.1 ∈ E.lvlSet R.U 1 := ScBanach.mem_whitneySet.1 hq
    rw [whitneyMap_eq_mk R.U R k (whitneyMap R.U R k q)]
    conv_rhs => rw [whitneyMap_eq_mk R.U R k q]
    refine Prod.ext (R.shift.idem q.1 hy) (congrArg (E.fiberPackL 0 k) (funext fun i => ?_))
    rw [whitneyVec_whitneyMap]
    have hq' : ((q.1, ScBanach.whitneyVec q i) : E.tangent 0) ∈ E.tangentSet R.U := hy
    exact congrArg Prod.snd (R.tangentMap_tangentMap hq')

@[simp] lemma whitney_U (k : ℕ) : (R.whitney k).U = E.whitneySet k R.U := rfl
@[simp] lemma whitney_apply (k : ℕ) (q : (E.whitney k) 0) :
    R.whitney k q = whitneyMap R.U R k q := rfl

/-- `⊕ₖ Tr` fixes the points of `⊕ₖ TO`. -/
lemma whitneyMap_eq_self {k : ℕ} {q : (E.whitney k) 0} (hq : q ∈ retractWhitney E C R.retract k) :
    whitneyMap R.U R k q = q := by
  rw [whitneyMap_eq_mk]
  conv_rhs => rw [← whitneyMk_fst_vec q]
  refine Prod.ext (R.levelMap_one_eq_self hq.1) (congrArg (E.fiberPackL 0 k) (funext fun i => ?_))
  have h := hq.2 i
  rw [retractTangent_eq] at h
  exact (R.mem_tangent_iff_of_mem hq.1).1 h

/-- **`⊕ₖ TO` is the retract of the Whitney retraction**: `(⊕ₖ Tr)(U¹ ⊕ E^k) = ⊕ₖ TO`. -/
theorem whitney_retract (k : ℕ) : (R.whitney k).retract = retractWhitney E C R.retract k := by
  ext q
  constructor
  · rintro ⟨q', hq', rfl⟩
    have hy : q'.1 ∈ E.lvlSet R.U 1 := ScBanach.mem_whitneySet.1 hq'
    refine ⟨?_, fun i => ?_⟩
    · rw [← R.shift_retract]; exact R.shift.mapsTo_retract hy
    · change ((levelMap R 1 q'.1, ScBanach.whitneyVec (whitneyMap R.U R k q') i) :
        E.tangent 0) ∈ _
      rw [whitneyVec_whitneyMap, retractTangent_eq]
      exact R.mem_tangent_iff_exists.2 ⟨q'.1, hy, _, rfl⟩
  · intro hq
    exact ⟨q, ScBanach.mem_whitneySet.2 (R.lvlSet_retract_subset 1 hq.1), R.whitneyMap_eq_self hq⟩

end ScRetraction

/-- **The Whitney sum `⊕ₖ TO` of an sc-retract is an sc-retract** (2021 p. 195, "it is an easy
exercise to show that the associated Whitney sum `TX ⊕ ⋯ ⊕ TX → X¹` is an sc-smooth bundle", in a
local model): `(⊕ₖ TO, C¹ ⊕ E^k, E¹ ⊕ E^k)` is the retract of `⊕ₖ Tr`. -/
theorem IsScRetract.whitney {C O : Set (E 0)} (hO : IsScRetract E C O) (k : ℕ) :
    IsScRetract (E.whitney k) (E.whitneySet k C) (retractWhitney E C O k) := by
  obtain ⟨R, rfl⟩ := hO
  exact ⟨R.whitney k, R.whitney_retract k⟩

/-- The Whitney sum `(⊕ₖ TO, C¹ ⊕ E^k, E¹ ⊕ E^k)` of a local model, as a local model. -/
def LocalModel.whitney (M : LocalModel) (k : ℕ) : LocalModel :=
  ⟨M.E.whitney k, M.E.whitneySet k M.C, retractWhitney M.E M.C M.O k, M.isScRetract.whitney k⟩

/-! ### The Whitney sum `⊕ₖ Tf` of a map between retracts -/

/-- `⊕ₖ Tf : ⊕ₖ TO → ⊕ₖ TO'`, `(x, h₁, …, h_k) ↦ (f(x), Df(x)h₁, …, Df(x)h_k)`, for a map `f`
between retracts, with `Tf = retractTangentMap` (Definition 2.1.14: `Df(x) = D(f ∘ r)(x)`). -/
def retractWhitneyMap (E : ScBanach) (C O : Set (E 0)) (f : E 0 → F 0) (k : ℕ)
    (q : (E.whitney k) 0) : (F.whitney k) 0 :=
  ScBanach.whitneyMk (levelMap f 1 q.1)
    (fun i => (retractTangentMap E C O f (q.1, ScBanach.whitneyVec q i)).2)

/-- On `⊕ₖ TO`, `⊕ₖ Tf ∘ ⊕ₖ Tr = ⊕ₖ T(f ∘ r)` for a retraction `r` onto `O`. -/
lemma retractWhitneyMap_comp_whitney {C : Set (E 0)} {C' O' : Set (F 0)} {f : E 0 → F 0}
    (R : ScRetraction E C) (hf : IsScSmoothRetractMap E C R.retract F C' O' f) (k : ℕ) :
    EqOn (retractWhitneyMap E C R.retract f k ∘ R.whitney k) (whitneyMap R.U (f ∘ R) k)
      (E.whitneySet k R.U) := by
  intro q hq
  have hy : q.1 ∈ E.lvlSet R.U 1 := ScBanach.mem_whitneySet.1 hq
  have hfR : IsScSmooth R.U (f ∘ R) := hf.comp_isScSmooth R rfl
  rw [Function.comp_apply, R.whitney_apply, whitneyMap_eq_mk R.U (f ∘ R) k q, retractWhitneyMap]
  refine Prod.ext ?_ (congrArg (F.fiberPackL 0 k) (funext fun i => ?_))
  · exact ((hf.isSc0 R.isScRetract).levelMap_comp R.isSc1.isSc0 R.mapsTo_retract hy).symm
  · have hp : ((levelMap R 1 q.1, scDeriv R.U R q.1 (ScBanach.whitneyVec q i)) : E.tangent 0) ∈
        retractTangent E C R.retract := by
      rw [retractTangent_eq]; exact R.mem_tangent_iff_exists.2 ⟨q.1, hy, _, rfl⟩
    have hpU : ((q.1, ScBanach.whitneyVec q i) : E.tangent 0) ∈ E.tangentSet R.U := hy
    change (retractTangentMap E C R.retract f
      ((whitneyMap R.U R k q).1, ScBanach.whitneyVec (whitneyMap R.U R k q) i)).2 = _
    rw [whitneyVec_whitneyMap, whitneyMap_fst, retractTangentMap_apply hf R rfl hp]
    obtain ⟨_, hchain⟩ := theorem_1_3_1' R.isScDomain R.isScDomain R.isSc1 hfR.isSc1 R.mapsTo
    have hcongr := hfR.isSc1.tangentMap_congr R.isScDomain
      (f' := (f ∘ R) ∘ R) fun y hy => by simp [R.idem y hy]
    have := (hchain hpU).symm.trans (hcongr hpU).symm
    exact congrArg Prod.snd this

/-- **`⊕ₖ Tf` is sc-smooth** between the Whitney sums `⊕ₖ TO → ⊕ₖ TO'` for an sc-smooth `f`
between retracts (the functoriality behind "the Whitney sum is an sc-smooth bundle", p. 195). -/
theorem IsScSmoothRetractMap.whitney {C O : Set (E 0)} {C' O' : Set (F 0)} {f : E 0 → F 0}
    (hf : IsScSmoothRetractMap E C O F C' O' f) (hO : IsScRetract E C O)
    (hO' : IsScRetract F C' O') (k : ℕ) :
    IsScSmoothRetractMap (E.whitney k) (E.whitneySet k C) (retractWhitney E C O k)
      (F.whitney k) (F.whitneySet k C') (retractWhitney F C' O' k)
      (retractWhitneyMap E C O f k) := by
  obtain ⟨R, rfl⟩ := hO
  rw [isScSmoothRetractMap_iff_exists (R.isScRetract.whitney k)]
  refine ⟨fun q hq => ?_, R.whitney k, R.whitney_retract k, ?_⟩
  · refine mem_retractWhitney_mk.2 ⟨hf.mapsTo_levelMap R.isScRetract 1 hq.1, fun i => ?_⟩
    have h1 := hf.tangentMap_mapsTo R.isScRetract hO' (hq.2 i)
    rw [retractTangentMap_apply hf R rfl (hq.2 i)] at h1 ⊢
    have h2 : levelMap (f ∘ R) 1 q.1 = levelMap f 1 q.1 := by
      have hx : R (E.toBase 1 q.1) = E.toBase 1 q.1 := R.apply_eq_self_of_mem_retract hq.1
      simp only [levelMap, Function.comp_apply, hx]
    rw [h2] at h1
    exact h1
  · exact ((hf.comp_isScSmooth R rfl).whitneyMap R.relOpen k).congr (R.whitney k).isScDomain
      (retractWhitneyMap_comp_whitney R hf k).symm

/-! ### Sc-differential forms in a local model (Definition 4.4.1) -/

/-- **2021 Definition 4.4.1 in a local model** `(O, C, E)`: an sc-differential `k`-form is a map
`ω : ⊕ₖ TO → ℝ` which is sc-smooth between the retracts `(⊕ₖ TO, C¹ ⊕ E^k, E¹ ⊕ E^k)` and `ℝ`,
and on every fibre `(T_xO)^k`, `x ∈ O₁`, is multilinear and alternating.  The last condition is
stated as: `ω(x, ·)` agrees on `(T_xO)^k` with an alternating map on `E₀^k` — equivalent, since
`T_xO = Dr(x)E` is the range of a continuous projection (an alternating map `a` on `T_xO` extends
to `a ∘ Dr(x)^k`). -/
structure IsRetractScForm (E : ScBanach) (C O : Set (E 0)) (k : ℕ) (ω : (E.whitney k) 0 → ℝ) :
    Prop where
  isScSmooth : IsScSmoothRetractMap (E.whitney k) (E.whitneySet k C) (retractWhitney E C O k)
    (ScBanach.const ℝ) univ univ ω
  alternating : ∀ x ∈ E.lvlSet O 1, ∃ a : E 0 [⋀^Fin k]→ₗ[ℝ] ℝ, ∀ v : Fin k → E 0,
    (∀ i, v i ∈ tangentSpace E C O x) → ω (ScBanach.whitneyMk x v) = a v

/-- **Witness**: the zero form is an sc-differential `k`-form on every local model. -/
theorem isRetractScForm_zero {C O : Set (E 0)} (k : ℕ) :
    IsRetractScForm E C O k (fun _ => 0) where
  isScSmooth := ⟨mapsTo_univ _ _, fun R _ n => IsSck.zero R.isScDomain n⟩
  alternating _ _ := ⟨0, fun _ _ => rfl⟩

/-! ### The inclusion `⊕ₖ T(O¹) → ⊕ₖ TO` -/

namespace ScBanach

variable (E) in
/-- The fibre part `(E¹)^k → E^k` of the inclusion of the levels, on level `m`. -/
def fiberInclL (m k : ℕ) : (E.shift.fiberPow k) m →L[ℝ] (E.fiberPow k) m :=
  (E.fiberPackL m k).comp
    ((ContinuousLinearMap.pi fun i : Fin k => (E.incl m).comp (ContinuousLinearMap.proj i)).comp
      (E.shift.fiberVecL m k))

lemma fiberVecL_injective {m k : ℕ} : Injective (E.fiberVecL m k) := fun p p' h => by
  rw [← fiberPackL_fiberVecL p, h, fiberPackL_fiberVecL]

@[simp] lemma fiberVecL_fiberInclL {m k : ℕ} (p : (E.shift.fiberPow k) m) (i : Fin k) :
    E.fiberVecL m k (E.fiberInclL m k p) i = E.incl m (E.shift.fiberVecL m k p i) := by
  simp [fiberInclL]

variable (E) in
/-- **The inclusion `⊕ₖ T(E¹) → ⊕ₖ TE`** (the points of `(E¹)¹ ⊕ (E¹)^k` read one level lower),
an sc-operator. -/
def whitneyIncl (k : ℕ) : ScOperator (E.shift.whitney k) (E.whitney k) where
  lvl m := (E.shift.incl m).prodMap (E.fiberInclL m k)
  incl_comm m q := by
    refine Prod.ext rfl (fiberVecL_injective (funext fun i => ?_))
    change E.fiberVecL m k ((E.fiberPow k).incl m (E.fiberInclL (m + 1) k q.2)) i =
      E.fiberVecL m k (E.fiberInclL m k ((E.shift.fiberPow k).incl m q.2)) i
    rw [fiberVecL_incl, fiberVecL_fiberInclL, fiberVecL_fiberInclL, fiberVecL_incl (E := E.shift)]

lemma whitneyIncl_fst {k : ℕ} (q : (E.shift.whitney k) 0) :
    (E.whitneyIncl k 0 q).1 = E.shift.toBase 1 q.1 := rfl

lemma whitneyVec_whitneyIncl {k : ℕ} (q : (E.shift.whitney k) 0) (i : Fin k) :
    whitneyVec (E.whitneyIncl k 0 q) i = E.toBase 1 (whitneyVec q i) :=
  fiberVecL_fiberInclL _ _

end ScBanach

/-- The inclusion maps `⊕ₖ T(O¹)` into `⊕ₖ TO`. -/
lemma mapsTo_whitneyIncl {C O : Set (E 0)} (hO : IsScRetract E C O) (k : ℕ) :
    MapsTo (E.whitneyIncl k 0) (retractWhitney E.shift (E.lvlSet C 1) (E.lvlSet O 1) k)
      (retractWhitney E C O k) := fun q hq => by
  refine ⟨hq.1, fun i => ?_⟩
  have h := hq.2 i
  rw [retractTangent_shift_of_isScRetract hO, ScBanach.mem_lvlSet, ScBanach.prod_toBase] at h
  rw [ScBanach.whitneyVec_whitneyIncl]
  exact h

/-- **The inclusion `⊕ₖ T(O¹) → ⊕ₖ TO` is sc-smooth** (the restriction of an sc-operator). -/
theorem isScSmoothRetractMap_whitneyIncl {C O : Set (E 0)} (hO : IsScRetract E C O) (k : ℕ) :
    IsScSmoothRetractMap (E.shift.whitney k) (E.shift.whitneySet k (E.lvlSet C 1))
      (retractWhitney E.shift (E.lvlSet C 1) (E.lvlSet O 1) k) (E.whitney k) (E.whitneySet k C)
      (retractWhitney E C O k) (E.whitneyIncl k 0) :=
  (E.whitneyIncl k).isScSmoothRetractMap (hO.shift.whitney k) (mapsTo_whitneyIncl hO k)

/-! ### Real-valued sc-smooth maps on a retract -/

/-- A constant real function is sc-smooth on every sc-domain. -/
theorem isScSmooth_const_real {G : ScBanach} {V : Set (G 0)} (hV : IsScDomain G V) (c : ℝ) :
    IsScSmooth (E := G) (F := ScBanach.const ℝ) V fun _ => c := by
  refine IsScSmooth.of_contDiffOn_levels hV (fun m _ _ => ⟨c, ScBanach.const_toBase ℝ m c⟩)
    fun m => ?_
  have : ∀ z ∈ G.lvlSet V m, levelMap (E := G) (F := ScBanach.const ℝ) (fun _ => c) m z = c :=
    fun z _ => levelMap_eq_of_toBase_eq (ScBanach.const_toBase ℝ m c)
  exact contDiffOn_const.congr this

variable {C O : Set (E 0)} {f g : E 0 → (ScBanach.const ℝ) 0}

theorem IsScSmoothRetractMap.real_const (c : ℝ) :
    IsScSmoothRetractMap E C O (ScBanach.const ℝ) univ univ fun _ => c :=
  ⟨mapsTo_univ _ _, fun R _ => isScSmooth_const_real R.isScDomain c⟩

theorem IsScSmoothRetractMap.real_add'
    (hf : IsScSmoothRetractMap E C O (ScBanach.const ℝ) univ univ f)
    (hg : IsScSmoothRetractMap E C O (ScBanach.const ℝ) univ univ g) :
    IsScSmoothRetractMap E C O (ScBanach.const ℝ) univ univ fun q => f q + g q :=
  ⟨mapsTo_univ _ _, fun R hR n =>
    IsSck.add R.isScDomain (hf.comp_isScSmooth R hR n) (hg.comp_isScSmooth R hR n)⟩

theorem IsScSmoothRetractMap.real_const_mul (c : ℝ)
    (hf : IsScSmoothRetractMap E C O (ScBanach.const ℝ) univ univ f) :
    IsScSmoothRetractMap E C O (ScBanach.const ℝ) univ univ fun q => c * f q :=
  ⟨mapsTo_univ _ _, fun R hR n => by
    have h := IsSck.comp R.isScDomain (isScDomain_univ _)
      ((ScOperator.ofConst (c • ContinuousLinearMap.id ℝ ℝ)).isScSmooth (isScDomain_univ _) n)
      (hf.comp_isScSmooth R hR n) (mapsTo_univ _ _)
    convert h using 1
    funext z; simp [ScOperator.ofConst]⟩

/-- **The Whitney sum over an open part**: `⊕ₖ T(O ∩ W) = ⊕ₖ TO ∩ {(x, h) | x ∈ W}`. -/
theorem retractWhitney_inter_isOpen (hO : IsScRetract E C O) {W : Set (E 0)} (hW : IsOpen W)
    (k : ℕ) :
    retractWhitney E C (O ∩ W) k = retractWhitney E C O k ∩ {q | E.toBase 1 q.1 ∈ W} := by
  ext q
  simp only [retractWhitney, retractTangent_inter_isOpen hO hW, mem_inter_iff, mem_ofPred_eq,
    mem_prod, mem_univ, and_true, ScBanach.mem_lvlSet]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, fun i => (h3 i).1⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, h2⟩, fun i => ⟨h3 i, h2⟩⟩

lemma retractWhitney_inter_subset (hO : IsScRetract E C O) {W : Set (E 0)} (hW : IsOpen W)
    (k : ℕ) : retractWhitney E C (O ∩ W) k ⊆ retractWhitney E C O k := by
  rw [retractWhitney_inter_isOpen hO hW]; exact inter_subset_left

/-! ### Sc-differential forms on an M-polyfold (Definition 4.4.1) -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ ψ : MChart X} {k : ℕ}

/-- The point `φ⁻¹(y) ∈ X¹` over `y ∈ O₁`. -/
def chartPoint (hφ : P.IsChart φ) {y : φ.model.E 1} (hy : y ∈ φ.model.E.lvlSet φ.model.O 1) :
    P.Level 1 :=
  P.levelMk 1 (φ.symm (φ.model.E.toBase 1 y))
    ((P.mem_levelSet_iff hφ (φ.symm_mapsTo hy)).2 (by rw [φ.apply_symm_apply hy]; exact ⟨y, rfl⟩))

variable (hφ : P.IsChart φ)

@[simp] lemma levelVal_chartPoint {y : φ.model.E 1} (hy : y ∈ φ.model.E.lvlSet φ.model.O 1) :
    P.levelVal 1 (chartPoint hφ hy) = φ.symm (φ.model.E.toBase 1 y) := rfl

lemma chartPoint_mem_source {y : φ.model.E 1} (hy : y ∈ φ.model.E.lvlSet φ.model.O 1) :
    P.levelVal 1 (chartPoint hφ hy) ∈ φ.source :=
  φ.symm_mapsTo hy

lemma levelLift_chartPoint {y : φ.model.E 1} (hy : y ∈ φ.model.E.lvlSet φ.model.O 1) :
    levelLift φ 1 (P.levelVal 1 (chartPoint hφ hy)) = y := by
  apply φ.model.E.toBase_injective 1
  rw [P.toBase_levelLift hφ (chartPoint_mem_source hφ hy) (levelVal_mem _)]
  exact φ.apply_symm_apply hy

lemma chartPoint_levelLift {x : P.Level 1} (hx : P.levelVal 1 x ∈ φ.source) :
    chartPoint hφ (levelLift_mem_lvlSet_one hφ hx) = x := by
  apply level_ext
  rw [levelVal_chartPoint, P.toBase_levelLift hφ hx (levelVal_mem x), φ.symm_apply_apply hx]

/-- `[(φ⁻¹(y), φ, h)] ∈ T_{φ⁻¹(y)}X` for `(y, h) ∈ TO`. -/
lemma mk_ofVec_mem_fiber_chartPoint {y : φ.model.E 1} (hy : y ∈ φ.model.E.lvlSet φ.model.O 1)
    {h : φ.model.E 0}
    (ha : ((y, h) : φ.model.E.tangent 0) ∈ retractTangent φ.model.E φ.model.C φ.model.O) :
    TangentSpace.mk (TangentPre.ofVec hφ ha) ∈ P.tangentFiber (chartPoint hφ hy) := by
  change P.tangentProj _ = _
  apply level_ext
  rw [tangentProj_mk, TangentPre.ofVec_x]; rfl

/-- Two evaluations of a family of forms agree when the base points and the vectors agree. -/
lemma altFamily_congr (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) {x x' : P.Level 1}
    (h : x = x') (α : Fin k → P.tangentFiber x) (α' : Fin k → P.tangentFiber x')
    (hα : ∀ i, (α i : P.TangentSpace) = α' i) : ω x α = ω x' α' := by
  subst h; congr 1; funext i; exact Subtype.ext (hα i)

open scoped Classical in
/-- **The local representative** `ω_φ : ⊕ₖ TO → ℝ` of a family `ω` of alternating forms on the
tangent spaces, in the chart `⊕ₖ Tφ` of `⊕ₖ TX`:
`ω_φ(y, h₁, …, h_k) = ω(φ⁻¹(y))((Tφ)⁻¹(y, h₁), …, (Tφ)⁻¹(y, h_k))` on `⊕ₖ TO` (`0` elsewhere). -/
def chartForm (hφ : P.IsChart φ) (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (q : (φ.model.E.whitney k) 0) : ℝ :=
  if hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k then
    ω (chartPoint hφ hq.1) fun i => ⟨TangentSpace.mk (TangentPre.ofVec hφ (hq.2 i)),
      mk_ofVec_mem_fiber_chartPoint hφ hq.1 (hq.2 i)⟩
  else 0

/-- **The local representative in charts**: if `Tφ(αᵢ) = (y, hᵢ)` for `αᵢ ∈ T_xX`, then
`ω_φ(y, h₁, …, h_k) = ω(x)(α₁, …, α_k)`. -/
theorem chartForm_eq (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) {x : P.Level 1}
    (hx : P.levelVal 1 x ∈ φ.source) (α : Fin k → P.tangentFiber x)
    {q : (φ.model.E.whitney k) 0} (hq1 : q.1 = levelLift φ 1 (P.levelVal 1 x))
    (hq2 : ∀ i, ScBanach.whitneyVec q i = (tangentChartMap hφ (α i)).2) :
    chartForm hφ ω q = ω x α := by
  have hmem : ∀ i, ((q.1, ScBanach.whitneyVec q i) : φ.model.E.tangent 0) =
      tangentChartMap hφ (α i) := fun i =>
    Prod.ext (by rw [hq1, tangentChartMap_fst_of_mem_fiber hφ hx (α i).2]) (hq2 i)
  have hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k :=
    ⟨by rw [hq1]; exact levelLift_mem_lvlSet_one hφ hx, fun i => by
      rw [hmem i]; exact tangentChartMap_mem hφ (mem_tangentChartSet_of_mem_fiber hx (α i).2)⟩
  rw [chartForm, dif_pos hq]
  refine altFamily_congr ω ?_ _ _ fun i => ?_
  · apply level_ext
    rw [levelVal_chartPoint, hq1, P.toBase_levelLift hφ hx (levelVal_mem x), φ.symm_apply_apply hx]
  · exact tangentChartMap_injOn hφ
      (mem_tangentChartSet_of_mem_fiber (chartPoint_mem_source hφ hq.1)
        (mk_ofVec_mem_fiber_chartPoint hφ hq.1 (hq.2 i)))
      (mem_tangentChartSet_of_mem_fiber hx (α i).2)
      (by rw [tangentChartMap_mk_ofVec, hmem i])

lemma chartForm_of_not_mem (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    {q : (φ.model.E.whitney k) 0} (hq : q ∉ retractWhitney φ.model.E φ.model.C φ.model.O k) :
    chartForm hφ ω q = 0 := dif_neg hq

lemma chartForm_add (ω τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (q : (φ.model.E.whitney k) 0) : chartForm hφ (ω + τ) q = chartForm hφ ω q + chartForm hφ τ q := by
  unfold chartForm; split_ifs <;> simp

lemma chartForm_smul (c : ℝ) (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (q : (φ.model.E.whitney k) 0) : chartForm hφ (c • ω) q = c * chartForm hφ ω q := by
  unfold chartForm; split_ifs <;> simp

lemma chartForm_zero (q : (φ.model.E.whitney k) 0) :
    chartForm hφ (0 : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) q = 0 := by
  unfold chartForm; split_ifs <;> simp

omit [T2Space X] [ParacompactSpace X] in
/-- The image of a chart over an open set is the retract cut by an open set. -/
lemma exists_overlap_eq_inter (ψ : MChart X) :
    ∃ W, IsOpen W ∧ φ.overlap ψ = φ.model.O ∩ W := by
  obtain ⟨W, hW, hWeq⟩ := φ.exists_isOpen_image_eq inter_subset_left
    (φ.isOpen_source.inter ψ.isOpen_source)
  exact ⟨W, hW, hWeq⟩

omit [T2Space X] [ParacompactSpace X] in
lemma retractWhitney_overlap_subset (ψ : MChart X) :
    retractWhitney φ.model.E φ.model.C (φ.overlap ψ) k ⊆
      retractWhitney φ.model.E φ.model.C φ.model.O k := by
  obtain ⟨W, hW, hWeq⟩ := exists_overlap_eq_inter (φ := φ) ψ
  rw [hWeq]; exact retractWhitney_inter_subset φ.model.isScRetract hW k

include hφ in
/-- On level `1`, the transition map sends `φ(x)` to `ψ(x)`. -/
lemma levelMap_transition_levelLift {ψ : MChart X} (hψ : P.IsChart ψ) {x : P.Level 1}
    (hx : P.levelVal 1 x ∈ φ.source) (hx' : P.levelVal 1 x ∈ ψ.source) :
    levelMap (φ.transition ψ) 1 (levelLift φ 1 (P.levelVal 1 x)) =
      levelLift ψ 1 (P.levelVal 1 x) := by
  have hov : φ.model.E.toBase 1 (levelLift φ 1 (P.levelVal 1 x)) ∈ φ.overlap ψ := by
    rw [P.toBase_levelLift hφ hx (levelVal_mem x)]; exact φ.mem_overlap ψ hx hx'
  apply ψ.model.E.toBase_injective 1
  rw [((hφ.compatible hψ (P := P)).1.isSc0 (φ.isScRetract_overlap ψ)).toBase_levelMap (m := 1)
      (x := levelLift φ 1 (P.levelVal 1 x)) hov,
    P.toBase_levelLift hφ hx (levelVal_mem x), P.toBase_levelLift hψ hx' (levelVal_mem x),
    φ.transition_apply ψ hx]

/-- **Chart change for the local representatives**: on `⊕ₖ T(φ(V ∩ V'))`,
`ω_ψ ∘ ⊕ₖ T(ψ ∘ φ⁻¹) = ω_φ`. -/
theorem chartForm_transition {ψ : MChart X} (hψ : P.IsChart ψ)
    (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    {q : (φ.model.E.whitney k) 0} (hq : q ∈ retractWhitney φ.model.E φ.model.C (φ.overlap ψ) k) :
    chartForm hψ ω (retractWhitneyMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ) k q) =
      chartForm hφ ω q := by
  have hq' := retractWhitney_overlap_subset (k := k) ψ hq
  conv_rhs => rw [chartForm, dif_pos hq']
  set x := chartPoint hφ hq'.1
  have hx : P.levelVal 1 x ∈ φ.source := chartPoint_mem_source hφ hq'.1
  have hx' : P.levelVal 1 x ∈ ψ.source := by
    obtain ⟨z, hz, hzeq⟩ := (show φ.model.E.toBase 1 q.1 ∈ φ.overlap ψ from hq.1)
    rw [levelVal_chartPoint, ← hzeq, φ.symm_apply_apply hz.1]; exact hz.2
  have hlift : levelLift φ 1 (P.levelVal 1 x) = q.1 := levelLift_chartPoint hφ hq'.1
  refine chartForm_eq hψ ω hx' _ ?_ fun i => ?_
  · change levelMap (φ.transition ψ) 1 q.1 = _
    rw [← hlift, levelMap_transition_levelLift hφ hψ hx hx']
  · rw [retractWhitneyMap, ScBanach.whitneyVec_mk]
    show _ = (tangentChartMap hψ (TangentSpace.mk (TangentPre.ofVec hφ (hq'.2 i)))).2
    rw [tangentChartMap_mk_ofVec_of_mem hφ hψ (hq'.2 i) (hq.2 i)]

/-! ### The definition and the vector space `Ωᵏ(X)` -/

/-- The family `ω` is sc-smooth on the Whitney sum `⊕ₖ TO` in the chart `⊕ₖ Tφ`. -/
def IsChartScSmooth (hφ : P.IsChart φ) (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    Prop :=
  IsScSmoothRetractMap (φ.model.E.whitney k) (φ.model.E.whitneySet k φ.model.C)
    (retractWhitney φ.model.E φ.model.C φ.model.O k) (ScBanach.const ℝ) univ univ (chartForm hφ ω)

variable (P k) in
/-- **2021 Definition 4.4.1 (p. 195)** (2017 / preprint: Definition 4.25): an **sc-differential
`k`-form** on `X` is a map `ω : ⊕ₖ TX → ℝ` which is linear in each argument and skew-symmetric —
here a family of alternating `k`-linear maps `ω(x)` on the tangent spaces `T_xX`, `x ∈ X¹` — and
sc-smooth: its local representative `ω_φ : ⊕ₖ TO → ℝ` (`chartForm`) is sc-smooth in every chart
`⊕ₖ Tφ` of `⊕ₖ TX` (`IsChartScSmooth`).  `φ` runs over the maximal atlas; by
`isScForm_of_cover` a covering family of charts suffices. -/
def IsScForm (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) : Prop :=
  ∀ ⦃φ : MChart X⦄ (hφ : P.IsChart φ), IsChartScSmooth hφ ω

/-- **Sc-smoothness of a form is local**: if `ω_φ` is sc-smooth in charts `φ` whose domains cover
`X¹`, then `ω_ψ` is sc-smooth in every chart `ψ` (chart change `chartForm_transition`, the
sc-smoothness of `⊕ₖ T(φ ∘ ψ⁻¹)` and locality, `IsScSmoothRetractMap.of_locally`). -/
theorem isChartScSmooth_of_cover (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (h : ∀ x : P.Level 1, ∃ (φ : MChart X) (hφ : P.IsChart φ), P.levelVal 1 x ∈ φ.source ∧
      IsChartScSmooth hφ ω)
    {ψ : MChart X} (hψ : P.IsChart ψ) : IsChartScSmooth hψ ω := by
  refine IsScSmoothRetractMap.of_locally (mapsTo_univ _ _) fun q hq => ?_
  obtain ⟨φ, hφ, hxφ, hsm⟩ := h (chartPoint hψ hq.1)
  obtain ⟨W, hW, hWeq⟩ := exists_overlap_eq_inter (φ := ψ) φ
  have hqW : ψ.model.E.toBase 1 q.1 ∈ ψ.overlap φ :=
    ⟨_, ⟨chartPoint_mem_source hψ hq.1, hxφ⟩, ψ.apply_symm_apply hq.1⟩
  refine ⟨{q | ψ.model.E.toBase 1 q.1 ∈ W},
    hW.preimage ((ψ.model.E.toBase 1).continuous.comp continuous_fst), (hWeq ▸ hqW).2, ?_⟩
  rw [← retractWhitney_inter_isOpen ψ.model.isScRetract hW, ← hWeq]
  have ht := ((hψ.compatible hφ (P := P)).1.whitney (ψ.isScRetract_overlap φ)
    (φ.isScRetract_overlap ψ) k).mono_target
    (((hψ.compatible hφ (P := P)).1.whitney (ψ.isScRetract_overlap φ)
      (φ.isScRetract_overlap ψ) k).mapsTo.mono_right (retractWhitney_overlap_subset (φ := φ) ψ))
  exact (hsm.comp ht (φ.model.isScRetract.whitney k)).congr fun q hq =>
    chartForm_transition hψ hφ ω hq

theorem isScForm_of_cover (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (h : ∀ x : P.Level 1, ∃ (φ : MChart X) (hφ : P.IsChart φ), P.levelVal 1 x ∈ φ.source ∧
      IsChartScSmooth hφ ω) : P.IsScForm k ω :=
  fun _ hψ => isChartScSmooth_of_cover ω h hψ

variable (P k) in
/-- **The vector space `Ωᵏ(X)`** of sc-differential `k`-forms (2021 Definition 4.4.1, p. 195). -/
def scForms : Submodule ℝ (∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) where
  carrier := {ω | P.IsScForm k ω}
  zero_mem' := fun φ hφ => by
    have h : chartForm hφ (0 : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) =
        fun _ => 0 := funext (chartForm_zero hφ)
    rw [IsChartScSmooth, h]; exact IsScSmoothRetractMap.real_const 0
  add_mem' := fun {ω τ} hω hτ φ hφ => by
    have h : chartForm hφ (ω + τ) = fun q => chartForm hφ ω q + chartForm hφ τ q :=
      funext (chartForm_add hφ ω τ)
    rw [IsChartScSmooth, h]; exact (hω hφ).real_add' (hτ hφ)
  smul_mem' := fun c ω hω φ hφ => by
    have h : chartForm hφ (c • ω) = fun q => c * chartForm hφ ω q :=
      funext (chartForm_smul hφ c ω)
    rw [IsChartScSmooth, h]; exact (hω hφ).real_const_mul c

lemma mem_scForms {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} :
    ω ∈ P.scForms k ↔ P.IsScForm k ω := Iff.rfl

/-- The constant `0`-form `c`: `ω(x) = c` on `(T_xX)⁰`. -/
def constForm (P : MPolyfold X) (c : ℝ) : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin 0]→ₗ[ℝ] ℝ :=
  fun _ => AlternatingMap.constOfIsEmpty ℝ _ (Fin 0) c

/-- **Witness** (Definition 4.4.1 quantifies over all charts of the maximal atlas): the constant
`0`-forms are sc-differential forms, so `Ω⁰(X) ≠ 0` for `X ≠ ∅`. -/
theorem constForm_mem_scForms (c : ℝ) : P.constForm c ∈ P.scForms 0 := fun φ hφ => by
  refine (IsScSmoothRetractMap.real_const c).congr fun q hq => ?_
  rw [chartForm, dif_pos hq]; rfl

/-- **The chart representative of an sc-form is a local sc-form** (`IsRetractScForm`): on each
fibre `(T_yO)^k` it is the alternating map `ω(φ⁻¹(y))` read through `Tφ`, extended to `E^k` by
a linear projection `E → T_yO`. -/
theorem IsScForm.isRetractScForm {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : P.IsScForm k ω) : IsRetractScForm φ.model.E φ.model.C φ.model.O k (chartForm hφ ω) where
  isScSmooth := hω hφ
  alternating y hy := by
    set x := chartPoint hφ hy
    have hx : P.levelVal 1 x ∈ φ.source := chartPoint_mem_source hφ hy
    have hlift : levelLift φ 1 (P.levelVal 1 x) = y := levelLift_chartPoint hφ hy
    obtain ⟨S, hS⟩ := Submodule.exists_isCompl (tangentFiberModel hφ hx)
    let π := Submodule.projectionOnto _ S hS
    let e := tangentFiberLinearEquiv hφ hx
    refine ⟨(ω x).compLinearMap (e.symm.toLinearMap ∘ₗ π), fun v hv => ?_⟩
    have hvm : ∀ i, v i ∈ tangentFiberModel hφ hx := fun i =>
      (mem_tangentFiberModel hφ hx).2 (by rw [hlift]; exact hv i)
    have hπ : ∀ i, (π (v i) : φ.model.E 0) = v i := fun i =>
      congrArg Subtype.val (Submodule.projectionOnto_apply_left hS ⟨v i, hvm i⟩)
    refine chartForm_eq hφ ω hx _ hlift.symm fun i => ?_
    rw [ScBanach.whitneyVec_mk]
    change v i = ((e (e.symm (π (v i))) : tangentFiberModel hφ hx) : φ.model.E 0)
    rw [LinearEquiv.apply_symm_apply, hπ]

/-! ### The pull-back along the inclusion `X¹ → X` -/

section Lower

variable {x : P.shift.Level 1}

/-- The base point in `X` of a point of `X²`. -/
abbrev liftBase (x : P.shift.Level 1) : X := P.levelVal 1 (P.shift.levelVal 1 x)

lemma tangentLower_mem_tangentFiber (α : P.shift.tangentFiber x) :
    tangentLower α.1 ∈ P.tangentFiber (P.shift.levelVal 1 x) := by
  change P.tangentProj _ = _
  rw [tangentProj_tangentLower, show P.shift.tangentProj α.1 = x from α.2]

/-- In a chart `φ` of `X` and its level chart `φ¹`, the inclusion `T_x(X¹) → T_xX` is the
inclusion `E₁ → E₀` of the vectors. -/
lemma tangentChartMap_tangentLower_snd (α : P.shift.tangentFiber x) (hx : liftBase x ∈ φ.source)
    (y₀ : P.Level 1) :
    (tangentChartMap hφ (tangentLower α.1)).2 =
      φ.model.E.toBase 1 (tangentChartMap (P.shift_isChart hφ y₀) α.1).2 := by
  have hs : shiftBase α.1 ∈ φ.source := by
    simp only [shiftBase]; rw [show P.shift.tangentProj α.1 = x from α.2]; exact hx
  rw [tangentChartMap_tangentLower α.1 hφ hs y₀]
  exact congrArg Prod.snd
    (ScBanach.prod_toBase φ.model.E.shift φ.model.E 1 (tangentChartMap (P.shift_isChart hφ y₀) α.1))

variable (x) in
/-- **The inclusion `T_x(X¹) → T_xX`** (2021 p. 41, `T(X¹) → TX`) on the fibre over `x ∈ X²`, as
a continuous linear map (it is `E₁ → E₀` in charts, `fiberMapCLM`). -/
def lowerFiberCLM : P.shift.tangentFiber x →L[ℝ] P.tangentFiber (P.shift.levelVal 1 x) :=
  fiberMapCLM (F := fun α => ⟨tangentLower α.1, tangentLower_mem_tangentFiber α⟩)
    (P.shift_isChart (P.someChart_isChart (liftBase x)) (P.shift.levelVal 1 x))
    (P.mem_someChart_source (liftBase x)) (P.someChart_isChart (liftBase x))
    (P.mem_someChart_source (liftBase x)) ((P.someChart (liftBase x)).model.E.toBase 1)
    fun α => tangentChartMap_tangentLower_snd _ α (P.mem_someChart_source _) _

@[simp] lemma coe_lowerFiberCLM_apply (α : P.shift.tangentFiber x) :
    (lowerFiberCLM x α : P.TangentSpace) = tangentLower α.1 :=
  congrArg Subtype.val (fiberMapCLM_apply _ _ _ _ _ _ α)

/-- **The pull-back of a family of forms along the inclusion `X¹ → X`**:
`(ι^*ω)(x)(α₁, …, α_k) = ω(x)(α₁, …, α_k)` for `αᵢ ∈ T_x(X¹) ⊆ T_xX`. -/
def formLower (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    ∀ x : P.shift.Level 1, P.shift.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ :=
  fun x => (ω (P.shift.levelVal 1 x)).compLinearMap
    (lowerFiberCLM x : P.shift.tangentFiber x →ₗ[ℝ] P.tangentFiber (P.shift.levelVal 1 x))

lemma formLower_apply (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (x : P.shift.Level 1) (α : Fin k → P.shift.tangentFiber x) :
    formLower ω x α = ω (P.shift.levelVal 1 x) fun i => lowerFiberCLM x (α i) := rfl

variable (P k) in
/-- The pull-back `ω ↦ ι^*ω` is linear. -/
def formLowerₗ : (∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) →ₗ[ℝ]
    (∀ x : P.shift.Level 1, P.shift.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) where
  toFun := formLower
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The local representative of the pull-back**: in the level chart `φ¹`,
`(ι^*ω)_{φ¹} = ω_φ ∘ (⊕ₖ T(O¹) → ⊕ₖ TO)`. -/
theorem chartForm_formLower (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (y₀ : P.Level 1) {q : (φ.model.E.shift.whitney k) 0}
    (hq : q ∈ retractWhitney φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet φ.model.O 1) k) :
    chartForm (P.shift_isChart hφ y₀) (formLower ω) q =
      chartForm hφ ω (φ.model.E.whitneyIncl k 0 q) := by
  have hχ := P.shift_isChart hφ y₀
  have hq' : q ∈ retractWhitney (levelChart hφ y₀).model.E (levelChart hφ y₀).model.C
      (levelChart hφ y₀).model.O k := hq
  conv_lhs => unfold chartForm
  split_ifs with h
  swap; · exact absurd hq' h
  rw [formLower_apply]
  have hsrc : P.shift.levelVal 1 (chartPoint hχ h.1) ∈ (levelChart hφ y₀).source :=
    chartPoint_mem_source hχ h.1
  have hx : liftBase (chartPoint hχ h.1) ∈ φ.source := hsrc
  refine (chartForm_eq hφ ω hx _ ?_ fun i => ?_).symm
  · have h1 := P.shift.toBase_levelLift hχ hsrc (levelVal_mem _)
    rw [levelLift_chartPoint hχ h.1, levelChart_apply] at h1
    exact h1
  · rw [ScBanach.whitneyVec_whitneyIncl, coe_lowerFiberCLM_apply,
      tangentChartMap_tangentLower_snd hφ _ hx y₀]
    exact congrArg (fun a => φ.model.E.toBase 1 (Prod.snd a))
      (tangentChartMap_mk_ofVec hχ (h.2 i)).symm

/-- **The pull-back of an sc-form along `X¹ → X` is an sc-form** on `X¹` (2021 p. 195, the maps
of the directed system (4.4)): sc-smooth in the level charts, which cover `X²`. -/
theorem formLower_mem_scForms {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : ω ∈ P.scForms k) : formLower ω ∈ P.shift.scForms k := by
  refine isScForm_of_cover _ fun x => ⟨levelChart (P.someChart_isChart (liftBase x))
    (P.shift.levelVal 1 x), P.shift_isChart _ _, P.mem_someChart_source _, ?_⟩
  have hφ := P.someChart_isChart (liftBase x)
  have hO := (P.someChart (liftBase x)).model.isScRetract
  exact ((hω hφ).comp (isScSmoothRetractMap_whitneyIncl hO k) (hO.whitney k)).congr
    fun q hq => (chartForm_formLower hφ ω (P.shift.levelVal 1 x) hq).symm

end Lower

end MPolyfold

/-! ### The directed system (4.4) and `Ωᵏ_∞(X)` (Definition 4.4.2) -/

namespace BundledMPolyfold

universe u

variable (A : BundledMPolyfold.{u}) (k : ℕ)

/-- `Ωᵏ(X^i)`, the sc-differential `k`-forms on the lift `X^i`. -/
abbrev forms (i : ℕ) := (A.lift i).P.scForms k

/-- The pull-back `Ωᵏ(X^i) → Ωᵏ(X^{i+1})` along the inclusion `X^{i+1} → X^i`. -/
def formsStep (i : ℕ) : A.forms k i →ₗ[ℝ] A.forms k (i + 1) :=
  LinearMap.codRestrict (A.forms k (i + 1))
    ((MPolyfold.formLowerₗ (A.lift i).P k).domRestrict (A.forms k i))
    fun ω => MPolyfold.formLower_mem_scForms ω.2

/-- **The directed system (4.4)** (2021 p. 195): `Ωᵏ(X^i) → Ωᵏ(X^j)` for `i ≤ j`, the composite
of the pull-backs. -/
def formsMap (i j : ℕ) (h : i ≤ j) : A.forms k i →ₗ[ℝ] A.forms k j :=
  Nat.leRecOn (C := fun j => A.forms k i →ₗ[ℝ] A.forms k j) h
    (fun {n} g => (A.formsStep k n).comp g) LinearMap.id

lemma formsMap_self (i : ℕ) : A.formsMap k i i le_rfl = LinearMap.id :=
  Nat.leRecOn_self _

lemma formsMap_succ {i j : ℕ} (h : i ≤ j) (h' : i ≤ j + 1) :
    A.formsMap k i (j + 1) h' = (A.formsStep k j).comp (A.formsMap k i j h) :=
  Nat.leRecOn_succ h _

lemma formsMap_comp {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    (A.formsMap k j l hjl).comp (A.formsMap k i j hij) = A.formsMap k i l (hij.trans hjl) := by
  induction l, hjl using Nat.le_induction with
  | base => rw [formsMap_self]; rfl
  | succ l hjl ih =>
    rw [formsMap_succ A k hjl, formsMap_succ A k (hij.trans hjl), LinearMap.comp_assoc, ih]

instance directedSystem_forms :
    DirectedSystem (fun i => ↥(A.forms k i)) fun i j h => ⇑(A.formsMap k i j h) where
  map_self i ω := by rw [formsMap_self]; rfl
  map_map _ _ _ hij hjk ω := LinearMap.congr_fun (A.formsMap_comp k hij hjk) ω

/-- **2021 Definition 4.4.2 (p. 195)** (2017 / preprint: Definition 4.25): `Ωᵏ_∞(X)`, the
sc-differential `k`-forms on `X_∞`, the direct limit of the system (4.4).  It is a real vector
space (the direct limit of modules). -/
abbrev formsInfty : Type _ := Module.DirectLimit (fun i => ↥(A.forms k i)) (A.formsMap k)

/-- The class `[ω] ∈ Ωᵏ_∞(X)` of an sc-form `ω ∈ Ωᵏ(X^i)`. -/
abbrev formsInftyOf (i : ℕ) : A.forms k i →ₗ[ℝ] A.formsInfty k :=
  Module.DirectLimit.of ℝ ℕ (fun i => ↥(A.forms k i)) (A.formsMap k) i

/-- A form and its pull-back to `X^j` have the same class. -/
theorem formsInftyOf_formsMap {i j : ℕ} (h : i ≤ j) (ω : A.forms k i) :
    A.formsInftyOf k j (A.formsMap k i j h ω) = A.formsInftyOf k i ω :=
  Module.DirectLimit.of_f

/-- `Ω*_∞(X) = ⊕ₖ Ωᵏ_∞(X)` (2021 p. 195, after Definition 4.4.2). -/
abbrev formsInftyGraded : Type _ := DirectSum ℕ fun k => A.formsInfty k

end BundledMPolyfold

end Polyfold
