import Polyfold.Basic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.1,
Definitions 1.1.1, 1.1.4, 1.1.5, 1.1.6 (preprint 1.1, 1.3, 1.4, 1.5), Propositions 1.1.7 and 1.1.8 (preprint 1.6 and 1.7).

# Sc-Banach spaces, sc-operators, sc-subspaces, sc-splittings

## The text, paraphrased

(Definition 1.1.1 (preprint 1.1)) An sc-structure on a Banach space `E` is a decreasing sequence of Banach spaces `E
= E₀ ⊃ E₁ ⊃ E₂ ⊃ …` such that (1) every inclusion `E_{m+1} → E_m` is compact and (2) the
intersection `E_∞ = ⋂ E_m` is dense in every `E_m`. The level shift `E^k` has levels `(E^k)_m =
E_{k+m}`; a direct sum `E ⊕ F` has levels `E_m ⊕ F_m`; a finite-dimensional space has exactly one
sc-structure, the constant one. (Definition 1.1.4 (preprint 1.3)) A linear map `T : E → F` is an sc-operator if
`T(E_m) ⊂ F_m` with `T : E_m → F_m` continuous for every `m`; an sc-isomorphism is a bijective
sc-operator with sc-operator inverse. (Definition 1.1.5 (preprint 1.4)) An sc⁺-operator is an sc-operator `S : E →
F` with `S(E_m) ⊂ F_{m+1}` and `S : E → F¹` an sc-operator; it is then compact on every level.
(Definition 1.1.6 (preprint 1.5)) A closed subspace `F ⊂ E` is an sc-subspace if `F_m = F ∩ E_m` is an sc-structure
on `F`; an sc-complement of `F` is an algebraic complement `G` such that `G_m = G ∩ E_m` is an
sc-structure on `G` and `E_m = F_m ⊕ G_m` is a topological direct sum for every `m` (an
sc-splitting). (Proposition 1.1.7 (preprint 1.6)) A finite-dimensional subspace is an sc-subspace iff it lies in
`E_∞`, and then it has an sc-complement. (Proposition 1.1.8 (preprint 1.7)) If `A` is an sc-subspace then `E/A` with
the filtration `E_m/A_m` is an sc-Banach space.

## What is formalized

* `Polyfold.ScScale`: an indexed family `lvl : ℕ → Type` of real Banach spaces with continuous
  linear injections `incl m : lvl (m+1) →L[ℝ] lvl m` that are compact operators (condition (1)).
  `ScScale.toBase m : lvl m →L[ℝ] lvl 0` is the composite inclusion `E_m → E₀`, and
  `ScScale.smooth : Submodule ℝ (lvl 0)` is `E_∞`, the set of points of `E₀` that lift to every
  level.  `ScScale.smoothLvl m = toBase m ⁻¹' smooth` is `E_∞` viewed inside `E_m`.
* `Polyfold.ScBanach`: an `ScScale` with condition (2), `dense_smooth : ∀ m, Dense (smoothLvl m)`.
  The weaker "the image of `E_{m+k}` is dense in `E_m`" is `ScBanach.denseRange_inclK`.
* `ScBanach.const V` (finite-dimensional `V`, constant structure), `ScBanach.prod E F`
  (`E ⊕ F`), `ScBanach.shift E` (`E¹`; `E^k` is the `k`-fold iterate `ScBanach.shiftK`).
* `Polyfold.ScOperator E F` (Definition 1.1.4 (preprint 1.3)): a family of continuous linear maps
  `T m : E m →L[ℝ] F m` commuting with the inclusions.  `Polyfold.IsScOperator T₀` is the
  predicate on `T₀ : E 0 →L[ℝ] F 0`; the two are equivalent (`ScOperator.isScOperator`,
  `IsScOperator.toScOperator`).  `Polyfold.ScIso E F`: level-wise continuous linear equivalences
  commuting with the inclusions.
* `Polyfold.ScPlus E F := ScOperator E F.shift` (Definition 1.1.5 (preprint 1.4)), `ScPlus.toScOperator` is the
  underlying sc-operator `E → F`, `ScPlus.isCompactOperator` is the compactness on every level.
* `ScBanach.levelSub A m = A ∩ E_m` (as `A.comap (toBase m)`), `ScBanach.IsScSubspace`
  (Definition 1.1.6 (preprint 1.5)), `ScBanach.ofSubspace` (the sc-Banach space `F` of Definition 1.1.6 (preprint 1.5)),
  `ScBanach.IsScSplitting F G` (sc-complement / sc-splitting).
* `ScBanach.proposition_1_1_7_iff`, `ScBanach.proposition_1_1_7` (**Proposition 1.1.7 (preprint 1.6)**),
  `ScBanach.quotient` and `ScBanach.proposition_1_1_8` (**Proposition 1.1.8 (preprint 1.7)**).

## What the text leaves implicit, and the choices made

* The text's `E_m` are subsets of `E₀`; here they are separate types with injective compact
  inclusions (PLAN.md).  `x ∈ E_m` for `x ∈ E₀` becomes `x ∈ Set.range (toBase m)`, and the
  intersection `E_∞` is `smooth`.  Nothing in Chapter 1 needs the identification of `E_{m}`
  with a subset of `E_{m-1}` beyond injectivity.
* The text does not say the inclusions are injective (it is implicit in "`E_{m+1} ⊂ E_m`");
  injectivity is a field, `incl_injective`.
* Condition (2) is stated as density of `E_∞ ∩ E_m` in `E_m` for every `m`, exactly as in the
  text.  The weaker "`E_{m+1}` is dense in `E_m`" (true for all `m`) does *not* obviously
  imply it, so the strong form is the axiom.
* An sc⁺-operator is defined as an sc-operator into the shifted space `F¹` (Definition 1.1.5 (preprint 1.4) says
  `S : E → F¹` is an sc-operator and `S(E_m) ⊂ F_{m+1}`; the latter is the former).
* Definition 1.1.6 (preprint 1.5) asks for the subspace `F` to be closed and for `(F_m)` to be an sc-structure; the
  compactness of `F_{m+1} → F_m` is automatic (restriction of a compact operator), so
  `IsScSubspace` asks only for closedness and density of `F ∩ E_∞` in every `F_m`.  For the
  sc-complement, the topological direct sum `E_m = F_m ⊕ G_m` follows from `IsCompl` of the
  closed subspaces `F_m`, `G_m` (closed graph theorem), so `IsScSplitting` asks only for
  `IsCompl` on every level; `IsScSplitting.closedComplemented` records the consequence.
* Proposition 1.1.8 (preprint 1.7) is stated for an sc-subspace `A`; the proof uses only that `A` is closed, so
  `ScBanach.quotient` takes `IsClosed A`.  The levels `E_m/A_m` are the abstract quotients
  `E m ⧸ levelSub A m`, with the inclusion `E_{m+1}/A_{m+1} → E_m/A_m` induced by `incl m`;
  the text's identification of `E_m/A_m` with a subset of `E/A` is the injectivity of this
  inclusion, which holds because `A_m = A ∩ E_m` is the *full* preimage of `A`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-- A **scale of Banach spaces** (condition (1) of Definition 1.1.1 (preprint 1.1)): real Banach spaces
`lvl m`, `m ∈ ℕ`, with injective compact continuous linear inclusions `lvl (m+1) → lvl m`. -/
structure ScScale where
  /-- The level `m` Banach space `E_m`. -/
  lvl : ℕ → Type
  [normed : ∀ m, NormedAddCommGroup (lvl m)]
  [space : ∀ m, NormedSpace ℝ (lvl m)]
  [complete : ∀ m, CompleteSpace (lvl m)]
  /-- The inclusion `E_{m+1} → E_m`. -/
  incl : ∀ m, lvl (m + 1) →L[ℝ] lvl m
  incl_injective : ∀ m, Function.Injective (incl m)
  incl_isCompactOperator : ∀ m, IsCompactOperator (incl m)

attribute [instance] ScScale.normed ScScale.space ScScale.complete

instance : CoeFun ScScale (fun _ => ℕ → Type) := ⟨ScScale.lvl⟩

namespace ScScale

variable (E : ScScale)

/-- The composite inclusion `E_m → E₀`. -/
def toBase : ∀ m, E m →L[ℝ] E 0
  | 0 => ContinuousLinearMap.id ℝ (E 0)
  | m + 1 => (toBase m).comp (E.incl m)

@[simp] lemma toBase_zero (x : E 0) : E.toBase 0 x = x := rfl

lemma toBase_succ (m : ℕ) (x : E (m + 1)) : E.toBase (m + 1) x = E.toBase m (E.incl m x) := rfl

lemma toBase_injective : ∀ m, Function.Injective (E.toBase m)
  | 0 => fun _ _ h => h
  | m + 1 => fun _ _ h => E.incl_injective m (toBase_injective m h)

/-- The composite inclusion `E_{m+k} → E_m`. -/
def inclK (m : ℕ) : ∀ k, E (m + k) →L[ℝ] E m
  | 0 => ContinuousLinearMap.id ℝ (E m)
  | k + 1 => (inclK m k).comp (E.incl (m + k))

@[simp] lemma inclK_zero (m : ℕ) (x : E m) : E.inclK m 0 x = x := rfl

lemma inclK_succ (m k : ℕ) (x : E (m + k + 1)) :
    E.inclK m (k + 1) x = E.inclK m k (E.incl (m + k) x) := rfl

lemma toBase_inclK (m : ℕ) : ∀ k (x : E (m + k)), E.toBase m (E.inclK m k x) = E.toBase (m + k) x
  | 0, _ => rfl
  | k + 1, x => toBase_inclK m k (E.incl (m + k) x)

lemma inclK_injective (m k : ℕ) : Function.Injective (E.inclK m k) := fun x y h =>
  E.toBase_injective (m + k) (by rw [← E.toBase_inclK, h, E.toBase_inclK])

/-- `E_∞ = ⋂ E_m`: the **smooth points**, as the subspace of `E₀` of points lifting to every
level. -/
def smooth : Submodule ℝ (E 0) := ⨅ m, LinearMap.range (E.toBase m : E m →ₗ[ℝ] E 0)

lemma mem_smooth_iff {x : E 0} : x ∈ E.smooth ↔ ∀ m, ∃ y : E m, E.toBase m y = x := by
  simp [smooth, Submodule.mem_iInf, LinearMap.mem_range]

/-- `E_∞` seen inside `E_m`: the points of `E_m` that lift to every level. -/
def smoothLvl (m : ℕ) : Set (E m) := E.toBase m ⁻¹' (E.smooth : Set (E 0))

lemma mem_smoothLvl_iff {m : ℕ} {x : E m} :
    x ∈ E.smoothLvl m ↔ ∀ j, ∃ y : E j, E.toBase j y = E.toBase m x := by
  simp [smoothLvl, mem_smooth_iff]

/-- A smooth point of `E_m` lifts to every `E_{m+k}`. -/
lemma exists_inclK_of_mem_smoothLvl {m : ℕ} {x : E m} (hx : x ∈ E.smoothLvl m) (k : ℕ) :
    ∃ y : E (m + k), E.inclK m k y = x := by
  obtain ⟨y, hy⟩ := E.mem_smoothLvl_iff.1 hx (m + k)
  exact ⟨y, E.toBase_injective m (by rw [E.toBase_inclK, hy])⟩

lemma smoothLvl_zero : E.smoothLvl 0 = (E.smooth : Set (E 0)) := rfl

lemma incl_mem_smoothLvl {m : ℕ} {x : E (m + 1)} (hx : x ∈ E.smoothLvl (m + 1)) :
    E.incl m x ∈ E.smoothLvl m := hx

lemma inclK_mem_smoothLvl {m k : ℕ} {x : E (m + k)} (hx : x ∈ E.smoothLvl (m + k)) :
    E.inclK m k x ∈ E.smoothLvl m := by
  simp only [smoothLvl, mem_preimage, E.toBase_inclK] at hx ⊢; exact hx

lemma smoothLvl_submodule_closed_sub {m : ℕ} {x y : E m} (hx : x ∈ E.smoothLvl m)
    (hy : y ∈ E.smoothLvl m) : x - y ∈ E.smoothLvl m := by
  simp only [smoothLvl, mem_preimage, map_sub, SetLike.mem_coe] at hx hy ⊢
  exact E.smooth.sub_mem hx hy

end ScScale

/-- An **sc-Banach space** (Definition 1.1.1 (preprint 1.1)): a scale of Banach spaces with compact inclusions in
which the smooth points `E_∞` are dense in every level `E_m`. -/
structure ScBanach extends ScScale where
  dense_smooth : ∀ m, Dense (toScScale.smoothLvl m)

instance : CoeFun ScBanach (fun _ => ℕ → Type) := ⟨fun E => E.lvl⟩

namespace ScBanach

variable (E : ScBanach)

/-- The image of `E_{m+k}` is dense in `E_m` (the weaker form of condition (2)). -/
lemma denseRange_inclK (m k : ℕ) : DenseRange (E.inclK m k) :=
  (E.dense_smooth m).mono fun _ hx => E.exists_inclK_of_mem_smoothLvl hx k

lemma denseRange_incl (m : ℕ) : DenseRange (E.incl m) := by
  have := E.denseRange_inclK m 1
  simpa [ScScale.inclK] using this

/-! ### The constant structure on a finite-dimensional space -/

/-- The constant scale `E_m = V` on a finite-dimensional space `V`. -/
abbrev constScale (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ScScale where
  lvl _ := V
  incl _ := ContinuousLinearMap.id ℝ V
  incl_injective _ := fun _ _ h => h
  incl_isCompactOperator _ := by
    simpa [ContinuousLinearMap.coe_id'] using
      (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ) (E := V)).2 inferInstance

lemma constScale_toBase (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (m : ℕ) (x : (constScale V) m) : (constScale V).toBase m x = x := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih _

lemma constScale_smoothLvl (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (m : ℕ) : (constScale V).smoothLvl m = univ := by
  ext x
  refine ⟨fun _ => mem_univ _, fun _ => ((constScale V).mem_smoothLvl_iff).2 fun j => ?_⟩
  exact ⟨show (constScale V) j from x, by rw [constScale_toBase, constScale_toBase]⟩

/-- The constant sc-structure `E_m = V` on a finite-dimensional space `V` (Definition 1.1.1 (preprint 1.1)). -/
abbrev const (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ScBanach where
  toScScale := constScale V
  dense_smooth m := by rw [constScale_smoothLvl]; exact dense_univ

@[simp] lemma const_lvl (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (m : ℕ) : (const V) m = V := rfl

lemma const_toBase (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (m : ℕ) (x : V) : (const V).toBase m x = x := constScale_toBase V m x

/-! ### Direct sums -/

/-- The direct sum `E ⊕ F` of two scales, with levels `E_m × F_m`. -/
abbrev prodScale (E F : ScScale) : ScScale where
  lvl m := E m × F m
  incl m := (E.incl m).prodMap (F.incl m)
  incl_injective m := Prod.map_injective.2 ⟨E.incl_injective m, F.incl_injective m⟩
  incl_isCompactOperator m := by
    obtain ⟨K, hK, hK'⟩ := E.incl_isCompactOperator m
    obtain ⟨L, hL, hL'⟩ := F.incl_isCompactOperator m
    refine ⟨K ×ˢ L, hK.prod hL, ?_⟩
    rw [ContinuousLinearMap.coe_prodMap', Set.preimage_prod_map_prod, nhds_prod_eq]
    exact Filter.prod_mem_prod hK' hL'

lemma prodScale_toBase (E F : ScScale) (m : ℕ) (x : (prodScale E F) m) :
    (prodScale E F).toBase m x = ((E.toBase m x.1, F.toBase m x.2) : (prodScale E F) 0) := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih _

lemma prodScale_smoothLvl (E F : ScScale) (m : ℕ) :
    (prodScale E F).smoothLvl m = E.smoothLvl m ×ˢ F.smoothLvl m := by
  ext p
  change _ ↔ p.1 ∈ E.smoothLvl m ∧ p.2 ∈ F.smoothLvl m
  constructor
  · intro h
    have h' := ((prodScale E F).mem_smoothLvl_iff).1 h
    refine ⟨(E.mem_smoothLvl_iff).2 fun j => ?_, (F.mem_smoothLvl_iff).2 fun j => ?_⟩
    · obtain ⟨z, hz⟩ := h' j
      rw [prodScale_toBase, prodScale_toBase] at hz
      exact ⟨z.1, congrArg Prod.fst hz⟩
    · obtain ⟨z, hz⟩ := h' j
      rw [prodScale_toBase, prodScale_toBase] at hz
      exact ⟨z.2, congrArg Prod.snd hz⟩
  · rintro ⟨h₁, h₂⟩
    refine ((prodScale E F).mem_smoothLvl_iff).2 fun j => ?_
    obtain ⟨a, ha⟩ := (E.mem_smoothLvl_iff).1 h₁ j
    obtain ⟨b, hb⟩ := (F.mem_smoothLvl_iff).1 h₂ j
    refine ⟨show (prodScale E F) j from (a, b), ?_⟩
    rw [prodScale_toBase, prodScale_toBase]
    exact Prod.ext ha hb

/-- The direct sum `E ⊕ F` of sc-Banach spaces (Definition 1.1.1 (preprint 1.1)), with levels `E_m × F_m`. -/
abbrev prod (E F : ScBanach) : ScBanach where
  toScScale := prodScale E.toScScale F.toScScale
  dense_smooth m := by
    rw [prodScale_smoothLvl]
    exact (E.dense_smooth m).prod (F.dense_smooth m)

@[simp] lemma prod_lvl (E F : ScBanach) (m : ℕ) : (E.prod F) m = (E m × F m) := rfl

lemma prod_toBase (E F : ScBanach) (m : ℕ) (x : (E.prod F) m) :
    (E.prod F).toBase m x = ((E.toBase m x.1, F.toBase m x.2) : (E.prod F) 0) :=
  prodScale_toBase _ _ m x

lemma prod_smoothLvl (E F : ScBanach) (m : ℕ) :
    (E.prod F).smoothLvl m = E.smoothLvl m ×ˢ F.smoothLvl m := prodScale_smoothLvl _ _ m

/-! ### The level shift -/

/-- The shifted scale `E¹` with levels `(E¹)_m = E_{m+1}`. -/
abbrev shiftScale (E : ScScale) : ScScale where
  lvl m := E (m + 1)
  incl m := E.incl (m + 1)
  incl_injective m := E.incl_injective (m + 1)
  incl_isCompactOperator m := E.incl_isCompactOperator (m + 1)

lemma shiftScale_toBase (E : ScScale) (m : ℕ) (x : E (m + 1)) :
    E.toBase (m + 1) x = E.toBase 1 ((shiftScale E).toBase m x) := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih _

lemma shiftScale_smoothLvl (E : ScScale) (m : ℕ) :
    (shiftScale E).smoothLvl m = E.smoothLvl (m + 1) := by
  ext x
  constructor
  · intro h
    refine (E.mem_smoothLvl_iff (m := m + 1) (x := x)).2 fun j => ?_
    obtain ⟨y, hy⟩ := ((shiftScale E).mem_smoothLvl_iff).1 h j
    refine ⟨E.incl j y, ?_⟩
    rw [shiftScale_toBase E m x, ← hy]
    exact shiftScale_toBase E j y
  · intro h
    refine ((shiftScale E).mem_smoothLvl_iff).2 fun j => ?_
    obtain ⟨y, hy⟩ := (E.mem_smoothLvl_iff (m := m + 1) (x := x)).1 h (j + 1)
    refine ⟨y, ?_⟩
    rw [shiftScale_toBase E j y, shiftScale_toBase E m x] at hy
    exact E.toBase_injective 1 hy

/-- The level shift `E¹` (Definition 1.1.1 (preprint 1.1)), with levels `(E¹)_m = E_{m+1}`. -/
abbrev shift (E : ScBanach) : ScBanach where
  toScScale := shiftScale E.toScScale
  dense_smooth m := by rw [shiftScale_smoothLvl]; exact E.dense_smooth (m + 1)

@[simp] lemma shift_lvl (m : ℕ) : E.shift m = E (m + 1) := rfl

lemma shift_incl (m : ℕ) (x : E (m + 1 + 1)) : E.shift.incl m x = E.incl (m + 1) x := rfl

lemma shift_toBase (m : ℕ) (x : E (m + 1)) :
    E.toBase (m + 1) x = E.toBase 1 (E.shift.toBase m x) := shiftScale_toBase _ m x

lemma shift_smoothLvl (m : ℕ) : E.shift.smoothLvl m = E.smoothLvl (m + 1) :=
  shiftScale_smoothLvl _ m

/-- The `k`-fold level shift `E^k`. -/
def shiftK (E : ScBanach) : ℕ → ScBanach
  | 0 => E
  | k + 1 => (shiftK E k).shift

end ScBanach

/-! ### Sc-operators (Definition 1.1.4 (preprint 1.3)), sc-isomorphisms, sc⁺-operators (Definition 1.1.5 (preprint 1.4)) -/

/-- An **sc-operator** `T : E → F` (Definition 1.1.4 (preprint 1.3)): continuous linear maps `T m : E_m → F_m` on
every level, compatible with the inclusions.  The text's `T : E → F` is `T 0`; the level maps
are determined by it (`ScOperator.ext_base`). -/
structure ScOperator (E F : ScBanach) where
  /-- The level `m` map `T : E_m → F_m`. -/
  lvl : ∀ m, E m →L[ℝ] F m
  incl_comm : ∀ m (x : E (m + 1)), F.incl m (lvl (m + 1) x) = lvl m (E.incl m x)

namespace ScOperator

variable {E F G : ScBanach}

instance : CoeFun (ScOperator E F) (fun _ => ∀ m, E m →L[ℝ] F m) := ⟨ScOperator.lvl⟩

lemma toBase_comm (T : ScOperator E F) (m : ℕ) (x : E m) :
    F.toBase m (T m x) = T 0 (E.toBase m x) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ScScale.toBase_succ, T.incl_comm, ih]; rfl

/-- The level maps of an sc-operator are determined by the base map `T 0`. -/
lemma ext_base {T T' : ScOperator E F} (h : T 0 = T' 0) : T = T' := by
  obtain ⟨T, hT⟩ := T
  obtain ⟨T', hT'⟩ := T'
  simp only at h
  congr
  ext m x
  apply F.toBase_injective m
  rw [toBase_comm ⟨T, hT⟩ m x, toBase_comm ⟨T', hT'⟩ m x]
  simp only [h]

/-- The identity sc-operator. -/
def id (E : ScBanach) : ScOperator E E where
  lvl m := ContinuousLinearMap.id ℝ (E m)
  incl_comm _ _ := rfl

/-- Composition of sc-operators. -/
def comp (S : ScOperator F G) (T : ScOperator E F) : ScOperator E G where
  lvl m := (S m).comp (T m)
  incl_comm m x := by simp only [ContinuousLinearMap.comp_apply, S.incl_comm, T.incl_comm]

@[simp] lemma comp_apply (S : ScOperator F G) (T : ScOperator E F) (m : ℕ) (x : E m) :
    S.comp T m x = S m (T m x) := rfl

/-- Sum of sc-operators. -/
def add (S T : ScOperator E F) : ScOperator E F where
  lvl m := S m + T m
  incl_comm m x := by simp only [add_apply, map_add, S.incl_comm, T.incl_comm]

instance : Add (ScOperator E F) := ⟨add⟩

@[simp] lemma add_apply (S T : ScOperator E F) (m : ℕ) (x : E m) : (S + T) m x = S m x + T m x :=
  rfl

/-- Sc-operators map smooth points to smooth points. -/
lemma mapsTo_smoothLvl (T : ScOperator E F) (m : ℕ) :
    MapsTo (T m) (E.smoothLvl m) (F.smoothLvl m) := by
  intro x hx
  rw [ScScale.mem_smoothLvl_iff] at hx ⊢
  intro j
  obtain ⟨y, hy⟩ := hx j
  exact ⟨T j y, by rw [toBase_comm, toBase_comm, hy]⟩

end ScOperator

/-- `T₀ : E₀ → F₀` **is an sc-operator** (Definition 1.1.4 (preprint 1.3), as a predicate on the base map): for
every `m` it maps `E_m` into `F_m` by a continuous linear map. -/
def IsScOperator {E F : ScBanach} (T₀ : E 0 →L[ℝ] F 0) : Prop :=
  ∀ m, ∃ Tm : E m →L[ℝ] F m, ∀ x, F.toBase m (Tm x) = T₀ (E.toBase m x)

lemma ScOperator.isScOperator {E F : ScBanach} (T : ScOperator E F) : IsScOperator (T 0) :=
  fun m => ⟨T m, T.toBase_comm m⟩

/-- The sc-operator with a given base map. -/
def IsScOperator.toScOperator {E F : ScBanach} {T₀ : E 0 →L[ℝ] F 0} (h : IsScOperator T₀) :
    ScOperator E F where
  lvl m := (h m).choose
  incl_comm m x := by
    apply F.toBase_injective m
    rw [(h m).choose_spec, ← ScScale.toBase_succ, (h (m + 1)).choose_spec]; rfl

@[simp] lemma IsScOperator.toScOperator_zero {E F : ScBanach} {T₀ : E 0 →L[ℝ] F 0}
    (h : IsScOperator T₀) : h.toScOperator 0 = T₀ := by
  ext x
  have := (h 0).choose_spec x
  change (h 0).choose x = T₀ x
  simpa using this

/-- An **sc-isomorphism** (Definition 1.1.4 (preprint 1.3)): a bijective sc-operator whose inverse is an
sc-operator, i.e. continuous linear equivalences on every level, compatible with the
inclusions. -/
structure ScIso (E F : ScBanach) where
  /-- The level `m` equivalence `E_m ≃ F_m`. -/
  lvl : ∀ m, E m ≃L[ℝ] F m
  incl_comm : ∀ m (x : E (m + 1)), F.incl m (lvl (m + 1) x) = lvl m (E.incl m x)

namespace ScIso

variable {E F G : ScBanach}

instance : CoeFun (ScIso E F) (fun _ => ∀ m, E m ≃L[ℝ] F m) := ⟨ScIso.lvl⟩

/-- The underlying sc-operator. -/
def toScOperator (T : ScIso E F) : ScOperator E F where
  lvl m := (T m : E m →L[ℝ] F m)
  incl_comm := T.incl_comm

@[simp] lemma toScOperator_apply (T : ScIso E F) (m : ℕ) (x : E m) : T.toScOperator m x = T m x :=
  rfl

/-- The inverse sc-isomorphism. -/
def symm (T : ScIso E F) : ScIso F E where
  lvl m := (T m).symm
  incl_comm m y := by
    apply (T m).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, ← T.incl_comm,
      ContinuousLinearEquiv.apply_symm_apply]

@[simp] lemma symm_apply (T : ScIso E F) (m : ℕ) (y : F m) : T.symm m y = (T m).symm y := rfl

/-- Composition of sc-isomorphisms. -/
def trans (T : ScIso E F) (S : ScIso F G) : ScIso E G where
  lvl m := (T m).trans (S m)
  incl_comm m x := by
    simp only [ContinuousLinearEquiv.trans_apply]; rw [S.incl_comm, T.incl_comm]

lemma toBase_comm (T : ScIso E F) (m : ℕ) (x : E m) :
    F.toBase m (T m x) = T 0 (E.toBase m x) := T.toScOperator.toBase_comm m x

lemma symm_toBase_comm (T : ScIso E F) (m : ℕ) (y : F m) :
    E.toBase m ((T m).symm y) = (T 0).symm (F.toBase m y) := T.symm.toBase_comm m y

/-- The identity sc-isomorphism. -/
def refl (E : ScBanach) : ScIso E E where
  lvl m := ContinuousLinearEquiv.refl ℝ (E m)
  incl_comm _ _ := rfl

end ScIso

/-- An **sc⁺-operator** `E → F` (Definition 1.1.5 (preprint 1.4)): an sc-operator `E → F¹` into the shifted space,
i.e. it raises the level by one. -/
abbrev ScPlus (E F : ScBanach) := ScOperator E F.shift

namespace ScBanach

/-- The inclusion `F¹ → F` as an sc-operator (level `m`: `F_{m+1} → F_m`). -/
def shiftIncl (F : ScBanach) : ScOperator F.shift F where
  lvl m := F.incl m
  incl_comm _ _ := rfl

end ScBanach

namespace ScPlus

variable {E F : ScBanach}

/-- The sc-operator `E → F` underlying an sc⁺-operator. -/
def toScOperator (S : ScPlus E F) : ScOperator E F := F.shiftIncl.comp S

@[simp] lemma toScOperator_apply (S : ScPlus E F) (m : ℕ) (x : E m) :
    S.toScOperator m x = F.incl m (S m x) := rfl

/-- An sc⁺-operator is compact on every level (the remark after Definition 1.1.5 (preprint 1.4)). -/
lemma isCompactOperator (S : ScPlus E F) (m : ℕ) : IsCompactOperator (S.toScOperator m) :=
  (F.incl_isCompactOperator m).comp_clm (S m)

end ScPlus

namespace ScBanach

variable (E : ScBanach)

/-! ### Sc-subspaces and sc-splittings (Definition 1.1.6 (preprint 1.5)) -/

/-- The level `m` part `A_m = A ∩ E_m` of a subspace `A ⊆ E₀`, as a subspace of `E_m`. -/
def levelSub (A : Submodule ℝ (E 0)) (m : ℕ) : Submodule ℝ (E m) :=
  A.comap (E.toBase m : E m →ₗ[ℝ] E 0)

lemma mem_levelSub {A : Submodule ℝ (E 0)} {m : ℕ} {x : E m} :
    x ∈ E.levelSub A m ↔ E.toBase m x ∈ A := Iff.rfl

@[simp] lemma levelSub_zero (A : Submodule ℝ (E 0)) : E.levelSub A 0 = A := by
  ext x; simp [mem_levelSub]

lemma incl_mem_levelSub {A : Submodule ℝ (E 0)} {m : ℕ} {x : E (m + 1)}
    (hx : x ∈ E.levelSub A (m + 1)) : E.incl m x ∈ E.levelSub A m := hx

lemma isClosed_levelSub {A : Submodule ℝ (E 0)} (hA : IsClosed (A : Set (E 0))) (m : ℕ) :
    IsClosed (E.levelSub A m : Set (E m)) := hA.preimage (E.toBase m).continuous

/-- `A` is an **sc-subspace** of `E` (Definition 1.1.6 (preprint 1.5)): a closed subspace such that the filtration
`A_m = A ∩ E_m` is an sc-structure on `A`, i.e. the smooth points `A ∩ E_∞` are dense in every
`A_m` (the compactness of `A_{m+1} → A_m` is automatic). -/
def IsScSubspace (A : Submodule ℝ (E 0)) : Prop :=
  IsClosed (A : Set (E 0)) ∧
    ∀ m, (E.levelSub A m : Set (E m)) ⊆ closure (E.levelSub A m ∩ E.smoothLvl m)

lemma IsScSubspace.isClosed {A : Submodule ℝ (E 0)} (h : E.IsScSubspace A) :
    IsClosed (A : Set (E 0)) := h.1

/-- A closed subspace `A` with the induced filtration `A_m = A ∩ E_m`, as a scale. -/
def ofSubspaceScale {A : Submodule ℝ (E 0)} (hA : IsClosed (A : Set (E 0))) : ScScale where
  lvl m := E.levelSub A m
  complete m := by
    have := E.isClosed_levelSub hA m
    infer_instance
  incl m := ((E.incl m).comp (E.levelSub A (m + 1)).subtypeL).codRestrict (E.levelSub A m)
    fun x => E.incl_mem_levelSub x.2
  incl_injective m x y hxy := by
    apply Subtype.ext
    apply E.incl_injective m
    exact congrArg Subtype.val hxy
  incl_isCompactOperator m :=
    ((E.incl_isCompactOperator m).comp_clm (E.levelSub A (m + 1)).subtypeL).codRestrict _
      (E.isClosed_levelSub hA m)

lemma ofSubspaceScale_coe_toBase {A : Submodule ℝ (E 0)} (hA : IsClosed (A : Set (E 0))) (m : ℕ)
    (x : (E.ofSubspaceScale hA) m) :
    ((E.ofSubspaceScale hA).toBase m x).1 = E.toBase m x.1 := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih _

lemma mem_ofSubspaceScale_smoothLvl {A : Submodule ℝ (E 0)} (hA : IsClosed (A : Set (E 0)))
    (m : ℕ) (x : (E.ofSubspaceScale hA) m) :
    x ∈ (E.ofSubspaceScale hA).smoothLvl m ↔ x.1 ∈ E.smoothLvl m := by
  rw [ScScale.mem_smoothLvl_iff, ScScale.mem_smoothLvl_iff]
  constructor
  · intro h j
    obtain ⟨y, hy⟩ := h j
    refine ⟨y.1, ?_⟩
    rw [← ofSubspaceScale_coe_toBase, ← ofSubspaceScale_coe_toBase, hy]
  · intro h j
    obtain ⟨y, hy⟩ := h j
    have hyA : y ∈ E.levelSub A j := by
      rw [mem_levelSub, hy]; exact x.2
    refine ⟨show (E.ofSubspaceScale hA) j from ⟨y, hyA⟩, Subtype.ext ?_⟩
    rw [ofSubspaceScale_coe_toBase, ofSubspaceScale_coe_toBase]
    exact hy

lemma ofSubspaceScale_smoothLvl {A : Submodule ℝ (E 0)} (hA : IsClosed (A : Set (E 0))) (m : ℕ) :
    (E.ofSubspaceScale hA).smoothLvl m =
      (Subtype.val ⁻¹' E.smoothLvl m : Set (E.levelSub A m)) :=
  Set.ext fun x => E.mem_ofSubspaceScale_smoothLvl hA m x

/-- An sc-subspace `A` with the induced sc-structure `A_m = A ∩ E_m` (Definition 1.1.6 (preprint 1.5)). -/
def ofSubspace {A : Submodule ℝ (E 0)} (h : E.IsScSubspace A) : ScBanach where
  toScScale := E.ofSubspaceScale h.isClosed
  dense_smooth m := by
    have hd : Dense (Subtype.val ⁻¹' E.smoothLvl m : Set (E.levelSub A m)) := by
      refine (Subtype.dense_iff (s := (E.levelSub A m : Set (E m)))).2 fun x hx => ?_
      refine closure_mono ?_ (h.2 m hx)
      rintro y ⟨hy1, hy2⟩
      exact ⟨⟨y, hy1⟩, hy2, rfl⟩
    rw [ofSubspaceScale_smoothLvl]
    exact hd

/-- `E = F ⊕ G` is an **sc-splitting** (Definition 1.1.6 (preprint 1.5)): `F` and `G` are sc-subspaces and
`E_m = F_m ⊕ G_m` on every level.  The direct sum is automatically topological
(`IsScSplitting.closedComplemented`). -/
def IsScSplitting (F G : Submodule ℝ (E 0)) : Prop :=
  E.IsScSubspace F ∧ E.IsScSubspace G ∧ ∀ m, IsCompl (E.levelSub F m) (E.levelSub G m)

lemma IsScSplitting.closedComplemented {F G : Submodule ℝ (E 0)} (h : E.IsScSplitting F G)
    (m : ℕ) : (E.levelSub F m).ClosedComplemented :=
  Submodule.ClosedComplemented.of_isCompl_isClosed (h.2.2 m) (E.isClosed_levelSub h.1.1 m)
    (E.isClosed_levelSub h.2.1.1 m)

lemma IsScSplitting.symm {F G : Submodule ℝ (E 0)} (h : E.IsScSplitting F G) :
    E.IsScSplitting G F := ⟨h.2.1, h.1, fun m => (h.2.2 m).symm⟩

/-! ### Proposition 1.1.7 (preprint 1.6) -/

/-- **Proposition 1.1.7 (preprint 1.6)**, first part: a finite-dimensional subspace `F` is an sc-subspace iff
`F ⊆ E_∞`. -/
theorem proposition_1_1_7_iff (F : Submodule ℝ (E 0)) [FiniteDimensional ℝ F] :
    E.IsScSubspace F ↔ F ≤ E.smooth := by
  constructor
  · intro h
    have h0 := h.2 0
    have : FiniteDimensional ℝ (F ⊓ E.smooth : Submodule ℝ (E 0)) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have hcl : IsClosed ((F ⊓ E.smooth : Submodule ℝ (E 0)) : Set (E 0)) :=
      Submodule.closed_of_finiteDimensional _
    intro x hx
    have hx' : x ∈ closure ((F ⊓ E.smooth : Submodule ℝ (E 0)) : Set (E 0)) := by
      rw [Submodule.coe_inf]
      exact h0 (by rwa [levelSub_zero])
    rw [hcl.closure_eq] at hx'
    exact hx'.2
  · intro hF
    refine ⟨Submodule.closed_of_finiteDimensional F, fun m x hx => subset_closure ⟨hx, ?_⟩⟩
    exact hF hx

/-- `E.toBase m` restricted to `F_m → F`. -/
private def levelRestrict (F : Submodule ℝ (E 0)) (m : ℕ) : E.levelSub F m →ₗ[ℝ] F :=
  (E.toBase m : E m →ₗ[ℝ] E 0).restrict fun _ hx => hx

private lemma levelRestrict_bijective (F : Submodule ℝ (E 0)) (hF : F ≤ E.smooth) (m : ℕ) :
    Bijective (E.levelRestrict F m) := by
  refine ⟨fun x y hxy => Subtype.ext (E.toBase_injective m (congrArg Subtype.val hxy)), fun y => ?_⟩
  obtain ⟨x, hx⟩ := (ScScale.mem_smooth_iff E.toScScale).1 (hF y.2) m
  exact ⟨⟨x, by rw [mem_levelSub, hx]; exact y.2⟩, Subtype.ext hx⟩

/-- `F_m ≃ F` for a subspace `F ⊆ E_∞`. -/
private def levelEquiv (F : Submodule ℝ (E 0)) (hF : F ≤ E.smooth) (m : ℕ) :
    E.levelSub F m ≃ₗ[ℝ] F :=
  LinearEquiv.ofBijective _ (E.levelRestrict_bijective F hF m)

private lemma levelEquiv_apply (F : Submodule ℝ (E 0)) (hF : F ≤ E.smooth) (m : ℕ)
    (x : E.levelSub F m) : (E.levelEquiv F hF m x : E 0) = E.toBase m x := rfl

/-- The level-`m` projection onto a finite-dimensional subspace `F ⊆ E_∞` induced by a
continuous projection `p : E₀ → F`. -/
private def finProj (F : Submodule ℝ (E 0)) [FiniteDimensional ℝ F] (hF : F ≤ E.smooth)
    (p : E 0 →L[ℝ] F) (m : ℕ) : E m →L[ℝ] E.levelSub F m :=
  haveI : FiniteDimensional ℝ (E.levelSub F m) :=
    LinearEquiv.finiteDimensional (E.levelEquiv F hF m).symm
  (LinearMap.toContinuousLinearMap (E.levelEquiv F hF m).symm.toLinearMap).comp
    (p.comp (E.toBase m))

private lemma finProj_apply_of_mem (F : Submodule ℝ (E 0)) [FiniteDimensional ℝ F]
    (hF : F ≤ E.smooth) (p : E 0 →L[ℝ] F) (hp : ∀ x : F, p x = x) (m : ℕ)
    (x : E.levelSub F m) : E.finProj F hF p m x = x := by
  change (E.levelEquiv F hF m).symm (p (E.toBase m x)) = x
  rw [hp ⟨E.toBase m x, x.2⟩]
  apply (E.levelEquiv F hF m).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

private lemma coe_finProj_mem (F : Submodule ℝ (E 0)) [FiniteDimensional ℝ F] (hF : F ≤ E.smooth)
    (p : E 0 →L[ℝ] F) (m : ℕ) (x : E m) :
    E.toBase m (E.finProj F hF p m x : E m) ∈ F := (E.finProj F hF p m x).2

private lemma finProj_eq_zero_iff (F : Submodule ℝ (E 0)) [FiniteDimensional ℝ F]
    (hF : F ≤ E.smooth) (p : E 0 →L[ℝ] F) (m : ℕ) (x : E m) :
    E.finProj F hF p m x = 0 ↔ p (E.toBase m x) = 0 := by
  change (E.levelEquiv F hF m).symm (p (E.toBase m x)) = 0 ↔ _
  exact LinearEquiv.map_eq_zero_iff _

/-- **Proposition 1.1.7 (preprint 1.6)**, second part: a finite-dimensional sc-subspace `F ⊆ E_∞` has an
sc-complement. -/
theorem proposition_1_1_7 (F : Submodule ℝ (E 0)) [FiniteDimensional ℝ F] (hF : F ≤ E.smooth) :
    ∃ G : Submodule ℝ (E 0), E.IsScSplitting F G := by
  obtain ⟨p, hp⟩ := Submodule.ClosedComplemented.of_finiteDimensional F
  refine ⟨LinearMap.ker (p : E 0 →ₗ[ℝ] F), (E.proposition_1_1_7_iff F).2 hF,
    ⟨p.isClosed_ker, fun m => ?_⟩, fun m => ?_⟩
  · -- density of the smooth points of `G_m = ker P_m`
    intro g hg
    have hg0 : E.finProj F hF p m g = 0 := (E.finProj_eq_zero_iff F hF p m g).2 hg
    let Q : E m →L[ℝ] E m :=
      ContinuousLinearMap.id ℝ (E m) - (E.levelSub F m).subtypeL.comp (E.finProj F hF p m)
    have hQg : Q g = g := by simp [Q, hg0]
    have hQ : MapsTo Q (E.smoothLvl m)
        (E.levelSub (LinearMap.ker (p : E 0 →ₗ[ℝ] F)) m ∩ E.smoothLvl m) := by
      intro x hx
      refine ⟨?_, ?_⟩
      · rw [SetLike.mem_coe, mem_levelSub, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
          ← E.finProj_eq_zero_iff F hF p m]
        simp only [Q, sub_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, map_sub]
        rw [E.finProj_apply_of_mem F hF p hp m, sub_self]
      · simp only [Q, sub_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
        exact E.smoothLvl_submodule_closed_sub hx (hF (E.coe_finProj_mem F hF p m x))
    have hcl : g ∈ closure (E.smoothLvl m) := by
      rw [(E.dense_smooth m).closure_eq]; exact mem_univ _
    rw [← hQg]
    exact closure_mono (image_subset_iff.2 hQ)
      (image_closure_subset_closure_image Q.continuous ⟨g, hcl, rfl⟩)
  · have hker : E.levelSub (LinearMap.ker (p : E 0 →ₗ[ℝ] F)) m =
        LinearMap.ker (E.finProj F hF p m : E m →ₗ[ℝ] E.levelSub F m) := by
      ext x
      rw [mem_levelSub, LinearMap.mem_ker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.coe_coe, E.finProj_eq_zero_iff F hF p m]
    rw [hker]
    exact LinearMap.isCompl_of_proj (E.finProj_apply_of_mem F hF p hp m)

/-! ### Proposition 1.1.8 (preprint 1.7): quotients -/

section Quotient

variable {A : Submodule ℝ (E 0)}

/-- The inclusion `E_{m+1}/A_{m+1} → E_m/A_m` induced by `incl m`. -/
private def quotIncl (m : ℕ) :
    (E (m + 1) ⧸ E.levelSub A (m + 1)) →L[ℝ] (E m ⧸ E.levelSub A m) :=
  (E.levelSub A (m + 1)).liftQL ((E.levelSub A m).mkQL.comp (E.incl m)) fun _ hx =>
    (Submodule.Quotient.mk_eq_zero _).2 hx

private lemma quotIncl_mk (m : ℕ) (x : E (m + 1)) :
    E.quotIncl (A := A) m (Submodule.Quotient.mk x) = Submodule.Quotient.mk (E.incl m x) := rfl

private lemma quotIncl_injective (m : ℕ) : Injective (E.quotIncl (A := A) m) := by
  have h : LinearMap.ker (E.quotIncl (A := A) m :
      (E (m + 1) ⧸ E.levelSub A (m + 1)) →ₗ[ℝ] (E m ⧸ E.levelSub A m)) = ⊥ := by
    apply Submodule.ker_liftQ_eq_bot
    intro x hx
    have hx' : (Submodule.Quotient.mk (E.incl m x) : E m ⧸ E.levelSub A m) = 0 := hx
    exact (Submodule.Quotient.mk_eq_zero (E.levelSub A m)).1 hx'
  exact LinearMap.ker_eq_bot.1 h

private lemma quotIncl_isCompactOperator (m : ℕ) : IsCompactOperator (E.quotIncl (A := A) m) := by
  obtain ⟨K, hK, hKmem⟩ := (E.incl_isCompactOperator m).clm_comp (E.levelSub A m).mkQL
  refine ⟨K, hK, ?_⟩
  have hopen : IsOpenMap (E.levelSub A (m + 1)).mkQL :=
    (Submodule.isOpenQuotientMap_mkQL _).isOpenMap
  have := hopen.image_mem_nhds hKmem
  rw [map_zero] at this
  refine mem_of_superset this ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hx

/-- The quotient scale `E/A` with levels `E_m / A_m`, for a closed subspace `A`. -/
def quotientScale (hA : IsClosed (A : Set (E 0))) : ScScale where
  lvl m := E m ⧸ E.levelSub A m
  normed m := haveI := E.isClosed_levelSub hA m; inferInstance
  incl m := E.quotIncl m
  incl_injective m := E.quotIncl_injective m
  incl_isCompactOperator m := E.quotIncl_isCompactOperator m

lemma quotientScale_toBase_mk (hA : IsClosed (A : Set (E 0))) (m : ℕ) (x : E m) :
    (E.quotientScale hA).toBase m (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (p := E.levelSub A 0) (E.toBase m x) := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih _

/-- **Proposition 1.1.8 (preprint 1.7)**: the quotient `E/A` of an sc-Banach space by a closed subspace `A`, with
the filtration `E_m/A_m`. -/
def quotient (hA : IsClosed (A : Set (E 0))) : ScBanach where
  toScScale := E.quotientScale hA
  dense_smooth m := by
    have hd : DenseRange (E.levelSub A m).mkQL := (Submodule.mkQ_surjective _).denseRange
    refine (hd.dense_image (E.levelSub A m).mkQL.continuous (E.dense_smooth m)).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ((E.quotientScale hA).mem_smoothLvl_iff).2 fun j => ?_
    obtain ⟨y, hy⟩ := (E.mem_smoothLvl_iff).1 hx j
    refine ⟨show (E.quotientScale hA) j from Submodule.Quotient.mk y, ?_⟩
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply, quotientScale_toBase_mk, quotientScale_toBase_mk,
      hy]

/-- The quotient map `E → E/A` as an sc-operator. -/
def quotientMap (hA : IsClosed (A : Set (E 0))) : ScOperator E (E.quotient hA) where
  lvl m := (E.levelSub A m).mkQL
  incl_comm _ _ := rfl

/-- **Proposition 1.1.8 (preprint 1.7)**, as a statement: there is an sc-Banach space `E/A` with a level-wise
surjective sc-operator `E → E/A` whose level-`m` kernel is `A_m = A ∩ E_m`. -/
theorem proposition_1_1_8 (hA : IsClosed (A : Set (E 0))) : ∃ (Q : ScBanach) (q : ScOperator E Q),
    (∀ m, Function.Surjective (q m)) ∧ ∀ m, LinearMap.ker (q m : E m →ₗ[ℝ] Q m) = E.levelSub A m :=
  ⟨E.quotient hA, E.quotientMap hA, fun _ => Submodule.mkQ_surjective _,
    fun _ => Submodule.ker_mkQ _⟩

end Quotient

end ScBanach

end Polyfold
