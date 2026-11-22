import Polyfold.Chapter17.ModelProperties

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 765–767): the regularity of objects and the filtration `C_∞ → ⋯ → C_1 → C_0 = C`
(p. 765), and **Definition 17.1.30** (the degeneracy functor `d : C → ℕ` and the boundary
`∂C`).  Numbers and pages are the 2021 text's.

# Regularity and degeneracy in a polyfold `C = (C, F, M)`

## The text, paraphrased

(p. 765) Pick `Ψ ∈ F(α)` and write `α = Ψ(q)`; `α` has regularity `i ∈ ℕ ∪ {∞}` if `q ∈ O_i`.  If
`i < k` and `q ∈ O_k`, `α` also has regularity `i`.  `mI(α) ∈ ℕ ∪ {+∞}` is the maximal such `i`.
This is independent of the choice of `Ψ ∈ F(α)`; isomorphic objects have the same regularity,
since `s` and `t` are local sc-diffeomorphisms.  Hence the regularity filtration
`C_∞ → ⋯ → C_i → C_{i-1} → ⋯ → C_0 = C` of full subcategories, which descends to isomorphism
classes.  (Definition 17.1.30, p. 767) The degeneracy functor `d : C → ℕ` is `d(α) = d_O(q)` for
`Ψ ∈ F(α)`, `Ψ(q) = α`, `d_O` the degeneracy index of `O`; the boundary `∂C` is the full
subcategory of the objects with `d(α) ≥ 1`.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `exists_tr_of_isomorphic`: an isomorphism `Ψ(q) ≅ Ψ'(q')` is a point `(q, φ, q')` of
  `M(Ψ, Ψ')`; `mem_levelSet_iff_of_isomorphic`, `maxLevel_eq_of_isomorphic`,
  `degIndex_eq_of_isomorphic` (the text's "`s` and `t` are local sc-diffeomorphisms").
* `HasRegularity m α` (`α ≅ Ψ(q)` with `q ∈ O_m` for some uniformizer `Ψ` of `F`), with
  **`hasRegularity_iff`** (for every uniformizer `Ψ` and `Ψ(q) ≅ α`: `α` has regularity `m` iff
  `q ∈ O_m`), `regularity_eq_of_mem` (the text's form for `Ψ ∈ F(α)`, `Ψ(q) = α`),
  `HasRegularity.of_isomorphic`, `HasRegularity.mono`, `IsSmoothObj` (regularity `∞`),
  `maxRegularity` (`mI(α) ∈ ℕ∞`, `maxRegularity_eq`, `le_maxRegularity_iff`,
  `maxRegularity_eq_top_iff`).
* The filtration: `regSet m` (the objects of `C_m`), `regSetInf` (`C_∞`), `regSet_antitone`,
  `regSetInf_subset`, `regSet_zero` (`C_0 = C`, for a polyfold construction whose footprints cover
  `|C|`), `isSaturated_regSet` (it descends to isomorphism classes), the full subcategories
  `regSub m`, `regSubInf` and the inclusion functors `regIncl`, `regInclInf`
  (`C_k → C_m`, `C_∞ → C_m`).
* The model: `hasRegularity_modelFunctor_obj` (`Γ_Ψ(x)` has regularity `m` iff `x ∈ (X_Ψ)_m`),
  `maxRegularity_modelFunctor_obj`, `degIndex_modelFunctor_obj`.
* **Definition 17.1.30**: `degIndex` (`d`), `degIndex_eq` (for every uniformizer and
  `Ψ(q) ≅ α`), `definition_17_1_30` (the text's form), `degIndex_eq_of_iso` (`d` is a functor to
  the discrete category `ℕ`), `boundarySet`, `boundary` (`∂C`, the full subcategory),
  `isSaturated_boundarySet`; under (ZHOU) `degIndex_polyfoldClass` (`d` is the degeneracy index of
  the polyfold `(|C|, c_C)`, Definition 16.1.14).

## Readings

* "Pick `Ψ ∈ F(α)`" presupposes `F(α) ≠ ∅` (implicit in the text, `HasUniformizers`).  We define
  the regularity and the degeneracy index through any uniformizer `Ψ` of `F` and any `q` with
  `Ψ(q) ≅ α` (`HasRegularity`, `degIndex`); `hasRegularity_iff`, `degIndex_eq` show that this is
  the text's definition for every `Ψ ∈ F(α)` (and every uniformizer at all), and it needs no
  choice of `Ψ ∈ F(α)`.  An object that no footprint contains has no regularity (`d = 0` there).
* `C_0 = C` needs every object in some footprint (`HasCoveringUniformizers`).
* The full subcategories `C_i` are the full subgroupoids on `regSet i`; the "→" of the filtration
  are the inclusion functors.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

universe u

namespace Polyfold

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction)

/-! ### Transfer along transition sets -/

variable {S} in
/-- **An isomorphism `Ψ(q) ≅ Ψ'(q')` is a point `(q, φ, q')` of `M(Ψ, Ψ')`.** -/
theorem exists_tr_of_isomorphic {Ψ Ψ' : S.Unif} {q : Ψ.1.O} {q' : Ψ'.1.O}
    (h : C.toGroupoidStr.Isomorphic (Ψ.1.obj q) (Ψ'.1.obj q')) :
    ∃ a : S.Tr Ψ Ψ', a.src = q ∧ a.tgt = q' := by
  obtain ⟨φ, hs, ht⟩ := h
  exact ⟨⟨q, φ, q', hs, ht⟩, rfl, rfl⟩

variable {S} in
/-- **Isomorphic objects have points on the same levels** (`s`, `t` are local
sc-diffeomorphisms, Definition 17.1.8 (a)). -/
theorem mem_levelSet_iff_of_isomorphic {Ψ Ψ' : S.Unif} {q : Ψ.1.O} {q' : Ψ'.1.O}
    (h : C.toGroupoidStr.Isomorphic (Ψ.1.obj q) (Ψ'.1.obj q')) (m : ℕ) :
    q ∈ Ψ.1.P.levelSet m ↔ q' ∈ Ψ'.1.P.levelSet m := by
  obtain ⟨a, rfl, rfl⟩ := exists_tr_of_isomorphic h
  exact ((S.isLocalScDiffeo_trSrc Ψ Ψ').mem_levelSet_iff a m).trans
    ((S.isLocalScDiffeo_trTgt Ψ Ψ').mem_levelSet_iff a m).symm

variable {S} in
/-- `ml(q) = ml(q')` for `Ψ(q) ≅ Ψ'(q')`. -/
theorem maxLevel_eq_of_isomorphic {Ψ Ψ' : S.Unif} {q : Ψ.1.O} {q' : Ψ'.1.O}
    (h : C.toGroupoidStr.Isomorphic (Ψ.1.obj q) (Ψ'.1.obj q')) :
    Ψ.1.P.maxLevel q = Ψ'.1.P.maxLevel q' := by
  simp only [MPolyfold.maxLevel, mem_levelSet_iff_of_isomorphic h]

variable {S} in
/-- `d_O(q) = d_{O'}(q')` for `Ψ(q) ≅ Ψ'(q')`. -/
theorem degIndex_eq_of_isomorphic {Ψ Ψ' : S.Unif} {q : Ψ.1.O} {q' : Ψ'.1.O}
    (h : C.toGroupoidStr.Isomorphic (Ψ.1.obj q) (Ψ'.1.obj q')) :
    Ψ.1.P.degIndex q = Ψ'.1.P.degIndex q' := by
  obtain ⟨a, rfl, rfl⟩ := exists_tr_of_isomorphic h
  exact ((S.isLocalScDiffeo_trSrc Ψ Ψ').degIndex_eq a).trans
    ((S.isLocalScDiffeo_trTgt Ψ Ψ').degIndex_eq a).symm

/-! ### Regularity (p. 765) -/

/-- **`α` has regularity `m`** (2021 p. 765): `α ≅ Ψ(q)` for a uniformizer `Ψ` of `F` and a point
`q ∈ O_m` (independent of the choices, `hasRegularity_iff`). -/
def HasRegularity (m : ℕ) (α : C.Obj) : Prop :=
  ∃ (Ψ : S.Unif) (q : Ψ.1.O), C.toGroupoidStr.Isomorphic (Ψ.1.obj q) α ∧ q ∈ Ψ.1.P.levelSet m

variable {S}

/-- **The regularity does not depend on the choices** (p. 765): for every uniformizer `Ψ` of `F`
and every `q` with `Ψ(q) ≅ α`, `α` has regularity `m` iff `q ∈ O_m`. -/
theorem hasRegularity_iff (Ψ : S.Unif) {q : Ψ.1.O} {α : C.Obj}
    (h : C.toGroupoidStr.Isomorphic (Ψ.1.obj q) α) (m : ℕ) :
    S.HasRegularity m α ↔ q ∈ Ψ.1.P.levelSet m := by
  refine ⟨fun ⟨Ψ', q', h', hq'⟩ => ?_, fun hq => ⟨Ψ, q, h, hq⟩⟩
  exact (mem_levelSet_iff_of_isomorphic (h'.trans h.symm) m).1 hq'

/-- **The text's definition** (p. 765): for `Ψ ∈ F(α)` and `Ψ(q) = α`, `α` has regularity `m`
iff `q ∈ O_m`. -/
theorem regularity_eq_of_mem {α : C.Obj} {Ψ : C.LocalUniformizer} (hΨ : Ψ ∈ S.F α)
    {q : Ψ.O} (hq : Ψ.obj q = α) (m : ℕ) :
    S.HasRegularity m α ↔ q ∈ Ψ.P.levelSet m := by
  subst hq
  exact hasRegularity_iff ⟨Ψ, Ψ.obj q, hΨ⟩ (GroupoidStr.isomorphic_refl _ _) m

/-- **Isomorphic objects have the same regularity** (p. 766). -/
theorem HasRegularity.of_isomorphic {m : ℕ} {α β : C.Obj} (h : S.HasRegularity m α)
    (hαβ : C.toGroupoidStr.Isomorphic α β) : S.HasRegularity m β := by
  obtain ⟨Ψ, q, h', hq⟩ := h
  exact ⟨Ψ, q, h'.trans hαβ, hq⟩

theorem hasRegularity_iff_of_isomorphic {m : ℕ} {α β : C.Obj}
    (hαβ : C.toGroupoidStr.Isomorphic α β) : S.HasRegularity m α ↔ S.HasRegularity m β :=
  ⟨fun h => h.of_isomorphic hαβ, fun h => h.of_isomorphic hαβ.symm⟩

/-- **Regularity `k` implies regularity `m ≤ k`** (p. 765). -/
theorem HasRegularity.mono {m k : ℕ} {α : C.Obj} (h : S.HasRegularity k α) (hmk : m ≤ k) :
    S.HasRegularity m α := by
  obtain ⟨Ψ, q, h', hq⟩ := h
  exact ⟨Ψ, q, h', Ψ.1.P.levelSet_antitone hmk hq⟩

/-- `α` has regularity `0` iff `α` lies in some footprint. -/
theorem hasRegularity_zero_iff {α : C.Obj} :
    S.HasRegularity 0 α ↔ ∃ Ψ : S.Unif, C.toGroupoidStr.π α ∈ Ψ.1.footprint := by
  constructor
  · rintro ⟨Ψ, q, h, -⟩
    exact ⟨Ψ, Ψ.1.mem_footprint_iff.2 ⟨q, (GroupoidStr.π_eq_π_iff _).2 h⟩⟩
  · rintro ⟨Ψ, hα⟩
    obtain ⟨q, hq⟩ := Ψ.1.mem_footprint_iff.1 hα
    exact ⟨Ψ, q, (GroupoidStr.π_eq_π_iff _).1 hq, by rw [MPolyfold.levelSet_zero]; trivial⟩

/-- Every object of `C` has regularity `0` when the footprints cover `|C|` (`C_0 = C`). -/
theorem hasRegularity_zero (h : S.HasCoveringUniformizers) (α : C.Obj) :
    S.HasRegularity 0 α := by
  obtain ⟨c⟩ := S.exists_coveringFamily_iff.2 h
  obtain ⟨i, hi⟩ := mem_iUnion.1 (c.cover.symm ▸ mem_univ (C.toGroupoidStr.π α))
  exact hasRegularity_zero_iff.2 ⟨c.Ψ i, hi⟩

variable (S)

/-- **`α` is smooth** (regularity `∞`, p. 765): it has every regularity `m ∈ ℕ`. -/
def IsSmoothObj (α : C.Obj) : Prop := ∀ m : ℕ, S.HasRegularity m α

/-- **`mI(α) ∈ ℕ ∪ {+∞}`** (p. 766): the maximal regularity of `α`. -/
def maxRegularity (α : C.Obj) : ℕ∞ := ⨆ (m : ℕ) (_ : S.HasRegularity m α), (m : ℕ∞)

variable {S}

/-- `mI(α) = ml(q)` for every uniformizer `Ψ` and `Ψ(q) ≅ α`. -/
theorem maxRegularity_eq (Ψ : S.Unif) {q : Ψ.1.O} {α : C.Obj}
    (h : C.toGroupoidStr.Isomorphic (Ψ.1.obj q) α) : S.maxRegularity α = Ψ.1.P.maxLevel q := by
  simp only [maxRegularity, MPolyfold.maxLevel, hasRegularity_iff Ψ h]

/-- `m ≤ mI(α)` iff `α` has regularity `m` (for `α` in some footprint). -/
theorem le_maxRegularity_iff {α : C.Obj} (h0 : S.HasRegularity 0 α) {m : ℕ} :
    (m : ℕ∞) ≤ S.maxRegularity α ↔ S.HasRegularity m α := by
  obtain ⟨Ψ, q, h, -⟩ := h0
  rw [maxRegularity_eq Ψ h, MPolyfold.le_maxLevel_iff, hasRegularity_iff Ψ h]

/-- `mI(α) = ∞` iff `α` is smooth (for `α` in some footprint). -/
theorem maxRegularity_eq_top_iff {α : C.Obj} (h0 : S.HasRegularity 0 α) :
    S.maxRegularity α = ⊤ ↔ S.IsSmoothObj α := by
  rw [ENat.eq_top_iff_forall_ge]
  exact forall_congr' fun m => le_maxRegularity_iff h0

/-- Isomorphic objects have the same `mI`. -/
theorem maxRegularity_eq_of_isomorphic {α β : C.Obj} (hαβ : C.toGroupoidStr.Isomorphic α β) :
    S.maxRegularity α = S.maxRegularity β := by
  simp only [maxRegularity, hasRegularity_iff_of_isomorphic hαβ]

/-! ### The regularity filtration `C_∞ → ⋯ → C_1 → C_0 = C` -/

variable (S)

/-- **The objects of `C_m`** (p. 766): those of regularity `m`. -/
def regSet (m : ℕ) : Set C.Obj := {α | S.HasRegularity m α}

/-- **The objects of `C_∞`**: the smooth objects. -/
def regSetInf : Set C.Obj := {α | S.IsSmoothObj α}

theorem regSet_antitone : Antitone S.regSet := fun _ _ hmk _ h => HasRegularity.mono h hmk

theorem regSetInf_eq : S.regSetInf = ⋂ m, S.regSet m := by
  ext α
  simp [regSetInf, regSet, IsSmoothObj]

theorem regSetInf_subset (m : ℕ) : S.regSetInf ⊆ S.regSet m := fun _ h => h m

/-- **`C_0 = C`** when the footprints cover `|C|`. -/
theorem regSet_zero (h : S.HasCoveringUniformizers) : S.regSet 0 = univ :=
  eq_univ_of_forall (hasRegularity_zero h)

/-- **The filtration descends to isomorphism classes**: `C_m` is saturated. -/
theorem isSaturated_regSet (m : ℕ) :
    C.toGroupoidStr.π ⁻¹' (C.toGroupoidStr.π '' S.regSet m) = S.regSet m := by
  refine Subset.antisymm (fun α ⟨β, hβ, he⟩ => ?_) (subset_preimage_image _ _)
  exact HasRegularity.of_isomorphic hβ ((GroupoidStr.π_eq_π_iff _).1 he)

theorem isSaturated_regSetInf :
    C.toGroupoidStr.π ⁻¹' (C.toGroupoidStr.π '' S.regSetInf) = S.regSetInf := by
  refine Subset.antisymm (fun α ⟨β, hβ, he⟩ m => ?_) (subset_preimage_image _ _)
  exact HasRegularity.of_isomorphic (hβ m) ((GroupoidStr.π_eq_π_iff _).1 he)

/-- **The full subcategory `C_m`** (p. 766). -/
abbrev regSub (m : ℕ) : GroupoidStr (S.regSet m) (C.toGroupoidStr.morOn (S.regSet m)) :=
  C.toGroupoidStr.fullSub (S.regSet m)

/-- **The full subcategory `C_∞`**. -/
abbrev regSubInf : GroupoidStr S.regSetInf (C.toGroupoidStr.morOn S.regSetInf) :=
  C.toGroupoidStr.fullSub S.regSetInf

/-- The inclusion of full subgroupoids `A ⊆ B`. -/
def fullSubIncl {A B : Set C.Obj} (hAB : A ⊆ B) :
    GroupoidFunctor (C.toGroupoidStr.fullSub A) (C.toGroupoidStr.fullSub B) where
  obj α := ⟨α.1, hAB α.2⟩
  mor φ := ⟨φ.1, hAB φ.2.1, hAB φ.2.2⟩
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp φ ψ h := by
    have h' : C.toGroupoidStr.src φ.1 = C.toGroupoidStr.tgt ψ.1 := congrArg Subtype.val h
    apply Subtype.ext
    simp only [GroupoidStr.fullSub, dif_pos h']
  mor_unit _ := rfl

/-- **The arrow `C_k → C_m`** (`m ≤ k`) of the filtration. -/
abbrev regIncl {m k : ℕ} (hmk : m ≤ k) :
    GroupoidFunctor (S.regSub k) (S.regSub m) :=
  fullSubIncl (S.regSet_antitone hmk)

/-- **The arrow `C_∞ → C_m`** of the filtration. -/
abbrev regInclInf (m : ℕ) : GroupoidFunctor S.regSubInf (S.regSub m) :=
  fullSubIncl (S.regSetInf_subset m)

/-! ### Regularity through the model `X_Ψ` -/

variable {ι : Type u} (Ψ : ι → S.Unif)

/-- **`Γ_Ψ(x)` has regularity `m` iff `x ∈ (X_Ψ)_m`.** -/
theorem hasRegularity_modelFunctor_obj (x : S.ModelObj Ψ) (m : ℕ) :
    S.HasRegularity m ((S.modelFunctor Ψ).obj x) ↔ x ∈ (S.modelEP Ψ).X.PObj.levelSet m := by
  obtain ⟨i, q⟩ := x
  exact (hasRegularity_iff (Ψ i) (GroupoidStr.isomorphic_refl _ _) m).trans
    (MPolyfold.mem_levelSet_sigma_iff (fun i => (Ψ i).1.P) q m).symm

/-- `mI(Γ_Ψ(x)) = ml(x)` in `X_Ψ`. -/
theorem maxRegularity_modelFunctor_obj (x : S.ModelObj Ψ) :
    S.maxRegularity ((S.modelFunctor Ψ).obj x) = (S.modelEP Ψ).X.PObj.maxLevel x := by
  simp only [maxRegularity, MPolyfold.maxLevel, hasRegularity_modelFunctor_obj]
  rfl

/-! ### Definition 17.1.30: the degeneracy functor and the boundary -/

open Classical in
/-- **2021 Definition 17.1.30, p. 767, the degeneracy functor `d : C → ℕ`**: `d(α) = d_O(q)` for
a uniformizer `Ψ` of `F` and `Ψ(q) ≅ α` (independent of the choices, `degIndex_eq`; `0` if `α`
lies in no footprint). -/
def degIndex (α : C.Obj) : ℕ :=
  if h : ∃ (Ψ : S.Unif) (q : Ψ.1.O), C.toGroupoidStr.Isomorphic (Ψ.1.obj q) α then
    h.choose.1.P.degIndex h.choose_spec.choose
  else 0

variable {S}

/-- **`d(α) = d_O(q)` for every uniformizer `Ψ` and `Ψ(q) ≅ α`.** -/
theorem degIndex_eq (Φ : S.Unif) {q : Φ.1.O} {α : C.Obj}
    (h : C.toGroupoidStr.Isomorphic (Φ.1.obj q) α) : S.degIndex α = Φ.1.P.degIndex q := by
  have hex : ∃ (Ψ : S.Unif) (q : Ψ.1.O), C.toGroupoidStr.Isomorphic (Ψ.1.obj q) α :=
    ⟨Φ, q, h⟩
  rw [degIndex, dif_pos hex]
  exact degIndex_eq_of_isomorphic (hex.choose_spec.choose_spec.trans h.symm)

/-- **2021 Definition 17.1.30, p. 767**, the text's form: for `Ψ ∈ F(α)` and `Ψ(q) = α`,
`d(α) = d_O(q)`. -/
theorem definition_17_1_30 {α : C.Obj} {Ψ : C.LocalUniformizer} (hΨ : Ψ ∈ S.F α)
    {q : Ψ.O} (hq : Ψ.obj q = α) : S.degIndex α = Ψ.P.degIndex q := by
  subst hq
  exact degIndex_eq ⟨Ψ, Ψ.obj q, hΨ⟩ (GroupoidStr.isomorphic_refl _ _)

/-- **`d` is a functor to the discrete category `ℕ`**: isomorphic objects have the same
degeneracy index. -/
theorem degIndex_eq_of_iso {α β : C.Obj} (hαβ : C.toGroupoidStr.Isomorphic α β) :
    S.degIndex α = S.degIndex β := by
  by_cases h : ∃ (Ψ : S.Unif) (q : Ψ.1.O), C.toGroupoidStr.Isomorphic (Ψ.1.obj q) α
  · obtain ⟨Ψ, q, hq⟩ := h
    rw [degIndex_eq Ψ hq, degIndex_eq Ψ (hq.trans hαβ)]
  · have h' : ¬ ∃ (Ψ : S.Unif) (q : Ψ.1.O), C.toGroupoidStr.Isomorphic (Ψ.1.obj q) β :=
      fun ⟨Ψ, q, hq⟩ => h ⟨Ψ, q, hq.trans hαβ.symm⟩
    rw [degIndex, dif_neg h, degIndex, dif_neg h']

/-- `d(Γ_Ψ(x)) = d_X(x)` in the model `X_Ψ`. -/
theorem degIndex_modelFunctor_obj (x : S.ModelObj Ψ) :
    S.degIndex ((S.modelFunctor Ψ).obj x) = (S.modelEP Ψ).X.PObj.degIndex x := by
  obtain ⟨i, q⟩ := x
  exact (degIndex_eq (Ψ i) (GroupoidStr.isomorphic_refl _ _)).trans
    (MPolyfold.degIndex_sigma (fun i => (Ψ i).1.P) q).symm

variable (S)

/-- **The objects of the boundary `∂C`** (Definition 17.1.30): `d(α) ≥ 1`. -/
def boundarySet : Set C.Obj := {α | 1 ≤ S.degIndex α}

/-- **The boundary `∂C`** (Definition 17.1.30), the full subcategory on `boundarySet`. -/
abbrev boundary : GroupoidStr S.boundarySet (C.toGroupoidStr.morOn S.boundarySet) :=
  C.toGroupoidStr.fullSub S.boundarySet

/-- `∂C` is saturated (it is a union of isomorphism classes). -/
theorem isSaturated_boundarySet :
    C.toGroupoidStr.π ⁻¹' (C.toGroupoidStr.π '' S.boundarySet) = S.boundarySet := by
  refine Subset.antisymm (fun α ⟨β, hβ, he⟩ => ?_) (subset_preimage_image _ _)
  change 1 ≤ S.degIndex α
  rw [← degIndex_eq_of_iso ((GroupoidStr.π_eq_π_iff _).1 he)]
  exact hβ

/-- **Under (ZHOU), `d` is the degeneracy index of the polyfold `(|C|, c_C)`** (Theorem 17.1.26,
Definition 16.1.14): `d_{|C|}(|α|) = d(α)`. -/
theorem degIndex_polyfoldClass (h : S.IsZhou) (α : C.Obj) :
    (S.polyfoldClass h).degIndex (C.toGroupoidStr.π α) = S.degIndex α := by
  obtain ⟨c, -⟩ := id h
  obtain ⟨i, hi⟩ := mem_iUnion.1 (c.cover.symm ▸ mem_univ (C.toGroupoidStr.π α))
  obtain ⟨q, hq⟩ := (c.Ψ i).1.mem_footprint_iff.1 hi
  have hx : (S.modelPolyfoldStructure c (h.model c)).β
      ((S.modelPolyfoldStructure c (h.model c)).X.X.π ⟨i, q⟩) = C.toGroupoidStr.π α := hq
  rw [PolyfoldClass.definition_16_1_14 _ _ (S.polyfoldClass_eq h c) hx,
    degIndex_eq (c.Ψ i) ((GroupoidStr.π_eq_π_iff _).1 hq)]
  exact MPolyfold.degIndex_sigma (fun i => (c.Ψ i).1.P) q

end GCT.PolyfoldConstruction

end Polyfold
