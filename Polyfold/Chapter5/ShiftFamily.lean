import Polyfold.Chapter2.TangentLiftAll
import Polyfold.Chapter5.Corollary58
import Polyfold.Chapter5.ShiftTameResearch

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Corollary 5.2.5,
2021 p. 213**, for all `i` at once.

# The family `P^i : Y^i → X^i` and Corollary 5.2.5 for every `i`

The text states Corollary 5.2.5 for the sections `f^i` of `P^i : Y^i → X^i`, "obtained by raising
the index", for every `i`.  `corollary_5_2_5` (`Corollary58.lean`) is the case `i = 1` for an
arbitrary strong bundle, with `P¹ = StrongBundle.shift`; `corollary_5_2_5_two` iterates it once.
Here the strong bundles `P^i` form one family indexed by `i : ℕ`.

The total space `Y^{i+1}` is a type built from `P^i` (the level `Y^i_{1,1}`), so the family is a
family of *bundled* strong bundles, as the family `X^i` of `BundledMPolyfold.lift`
(`TangentLiftAll.lean`, 2021 p. 37):

* `BundledStrongBundle`: a strong bundle `P : Y → X` over an M-polyfold, bundled with its base
  (a `BundledMPolyfold`) and its total space.  `BundledStrongBundle.of B` bundles a given `B`.
* `BundledStrongBundle.lift S i` (**`P^i : Y^i → X^i`**): `P⁰ = P`, `P^{i+1} = (P^i)¹`.  Its base
  is the lift `X^i` of the base (`lift_base`).
* `BundledStrongBundle.sectionLift S f i` (**`f^i`**): `f⁰ = f`, `f^{i+1} = (f^i)¹`.
* **`corollary_5_2_5_family`**: for every `i`, `f^i` is an sc-Fredholm section of `P^i` with
  compact solution set (and `corollary_5_2_5_tame_family` with tame germ data).
* **The instances `i = 1, 2`**: the statement `Corollary525 S f i` of the family is, for
  `S = of B` and `i = 1, 2`, literally the statement of `corollary_5_2_5` and of
  `corollary_5_2_5_two` (`corollary525_of_one_iff`, `corollary525_of_two_iff`, proved by `Iff.rfl`);
  `corollary_5_2_5_family_one`, `corollary_5_2_5_family_two` recover those two theorems from the
  family.

The identifications with the text's reading (`X^i` is `X_i`, `Y^i` is `Y_{i,i}`, `f^i = f|_{X_i}`)
are given by the inclusions `baseIncl i : X^i → X` and `totalIncl i : Y^i → Y` (the identity on
underlying points), not by equalities of types:

* `baseIncl_injective`, `range_baseIncl` (the range is `X_i`), `mem_levelSet_baseIncl`
  (`(X^i)_m = X_{m+i}`);
* `totalIncl_injective`, `range_totalIncl` (the range is `Y_{i,i}`), `mem_doubleLevel_totalIncl`
  (`(Y^i)_{m,k} = Y_{m+i,k+i}`, `k ≤ m + 1`);
* `proj_totalIncl` (`P ∘ incl = incl ∘ P^i`), `totalIncl_sectionLift` (`f^i(x) = f(x)` for an
  sc-smooth `f`), `solutionSet_sectionLift` (the solutions of `f^i` are those of `f` in `X_i`).

Tameness of `X` is not used (the 2021 statement does not assume it), as in `corollary_5_2_5`.
-/

open Set Function

noncomputable section

namespace Polyfold

universe u v

open MPolyfold

set_option linter.checkUnivs false in
/-- **A strong bundle bundled with its base and total space** (so that the index raises
`P^i : Y^i → X^i` form a family indexed by `i`): a `BundledMPolyfold` base `X`, a paracompact
Hausdorff total space `Y` with linear fibres, and a strong bundle `P : Y → X`
(Definition 2.6.5, 2021 p. 68). -/
structure BundledStrongBundle where
  /-- The base M-polyfold `X`. -/
  base : BundledMPolyfold.{u}
  /-- The total space `Y`. -/
  total : Type v
  [instTop : TopologicalSpace total]
  [instT2 : T2Space total]
  [instPara : ParacompactSpace total]
  /-- The projection `P : Y → X`. -/
  proj : total → base.carrier
  [instAdd : ∀ x, AddCommGroup (proj ⁻¹' {x})]
  [instMod : ∀ x, Module ℝ (proj ⁻¹' {x})]
  /-- The strong bundle structure. -/
  B : StrongBundle base.P proj

attribute [instance] BundledStrongBundle.instTop BundledStrongBundle.instT2
  BundledStrongBundle.instPara BundledStrongBundle.instAdd BundledStrongBundle.instMod

namespace BundledStrongBundle

/-- A given strong bundle `P : Y → X`, bundled. -/
def of {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
    [iA : ∀ x, AddCommGroup (P ⁻¹' {x})] [iM : ∀ x, Module ℝ (P ⁻¹' {x})]
    (B : StrongBundle PX P) : BundledStrongBundle.{u, v} :=
  @BundledStrongBundle.mk (BundledMPolyfold.of PX) Y _ _ _ P iA iM B

variable (S : BundledStrongBundle.{u, v})

/-- **The shifted strong bundle `P¹ : Y¹ → X¹`** (`StrongBundle.shift`), bundled. -/
def shift : BundledStrongBundle.{u, v} where
  base := S.base.shift
  total := S.B.ShiftSpace
  proj := S.B.shiftProj
  instAdd := S.B.shiftFiber_addCommGroup
  instMod := S.B.shiftFiber_module
  B := S.B.shift

/-- **The family `P^i : Y^i → X^i`** (Corollary 5.2.5, 2021 p. 213): `P⁰ = P`,
`P^{i+1} = (P^i)¹`. -/
def lift : ℕ → BundledStrongBundle.{u, v}
  | 0 => S
  | i + 1 => (lift i).shift

@[simp] lemma lift_zero : S.lift 0 = S := rfl

lemma lift_succ (i : ℕ) : S.lift (i + 1) = (S.lift i).shift := rfl

/-- **`P^{i+1} = (P¹)^i`**: the two recursions agree. -/
theorem lift_succ' : ∀ i : ℕ, S.lift (i + 1) = S.shift.lift i
  | 0 => rfl
  | i + 1 => congrArg shift (lift_succ' i)

/-- **The base of `P^i` is the lift `X^i` of the base** (`BundledMPolyfold.lift`, 2021 p. 37). -/
theorem lift_base : ∀ i : ℕ, (S.lift i).base = S.base.lift i
  | 0 => rfl
  | i + 1 => congrArg BundledMPolyfold.shift (lift_base i)

/-- **The section `f^i : X^i → Y^i`** of `P^i`, "obtained by raising the index" (2021 p. 213):
`f⁰ = f`, `f^{i+1} = (f^i)¹` (`StrongBundle.sectionShift`). -/
def sectionLift (f : S.base.carrier → S.total) :
    (i : ℕ) → (S.lift i).base.carrier → (S.lift i).total
  | 0 => f
  | i + 1 => (S.lift i).B.sectionShift (sectionLift f i)

/-- The inclusion `X^i → X` (the identity on underlying points). -/
def baseIncl : (i : ℕ) → (S.lift i).base.carrier → S.base.carrier
  | 0 => id
  | i + 1 => fun x => baseIncl i ((S.lift i).base.P.levelVal 1 x)

/-- The inclusion `Y^i → Y` (the identity on underlying points). -/
def totalIncl : (i : ℕ) → (S.lift i).total → S.total
  | 0 => id
  | i + 1 => fun y => totalIncl i ((S.lift i).B.toMPolyfold0.levelVal 1 y)

/-! ### The identifications `X^i = X_i`, `Y^i = Y_{i,i}` -/

theorem baseIncl_injective : ∀ i, Injective (S.baseIncl i)
  | 0 => injective_id
  | i + 1 => fun _ _ h => level_ext (baseIncl_injective i h)

theorem totalIncl_injective : ∀ i, Injective (S.totalIncl i)
  | 0 => injective_id
  | i + 1 => fun _ _ h => level_ext (totalIncl_injective i h)

/-- **`(X^i)_m = X_{m+i}`** through the inclusion. -/
theorem mem_levelSet_baseIncl : ∀ (i : ℕ) (x : (S.lift i).base.carrier) (m : ℕ),
    x ∈ (S.lift i).base.P.levelSet m ↔ S.baseIncl i x ∈ S.base.P.levelSet (m + i)
  | 0, _, _ => Iff.rfl
  | i + 1, x, m => by
    refine (mem_shift_levelSet_iff (PX := (S.lift i).base.P) x).trans ?_
    rw [mem_levelSet_baseIncl i, show m + 1 + i = m + (i + 1) by omega]
    rfl

/-- Every point of `X_{m+i}` comes from a point of `(X^i)_m`. -/
theorem exists_baseIncl_eq : ∀ (i m : ℕ) (z : S.base.carrier), z ∈ S.base.P.levelSet (m + i) →
    ∃ x ∈ (S.lift i).base.P.levelSet m, S.baseIncl i x = z
  | 0, _, z, hz => ⟨z, hz, rfl⟩
  | i + 1, m, z, hz => by
    obtain ⟨x, hx, rfl⟩ := exists_baseIncl_eq i (m + 1) z
      (by rwa [show m + 1 + i = m + (i + 1) by omega])
    let x' := (S.lift i).base.P.levelMk 1 x
      ((S.lift i).base.P.levelSet_antitone (by omega : 1 ≤ m + 1) hx)
    exact ⟨x', (mem_shift_levelSet_iff (PX := (S.lift i).base.P) x').2 hx, rfl⟩

/-- **The points of `X^i` are those of `X_i`.** -/
theorem range_baseIncl (i : ℕ) : range (S.baseIncl i) = S.base.P.levelSet i := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    have := (S.mem_levelSet_baseIncl i x 0).1 (by rw [levelSet_zero]; trivial)
    rwa [Nat.zero_add] at this
  · intro hz
    obtain ⟨x, -, hx⟩ := S.exists_baseIncl_eq i 0 z (by rwa [Nat.zero_add])
    exact ⟨x, hx⟩

/-- **`(Y^i)_{m,k} = Y_{m+i,k+i}`** (`k ≤ m + 1`) through the inclusion. -/
theorem mem_doubleLevel_totalIncl : ∀ (i : ℕ) (y : (S.lift i).total) (m k : ℕ), k ≤ m + 1 →
    (y ∈ (S.lift i).B.doubleLevel m k ↔ S.totalIncl i y ∈ S.B.doubleLevel (m + i) (k + i))
  | 0, _, _, _, _ => Iff.rfl
  | i + 1, y, m, k, hk => by
    refine ((S.lift i).B.mem_shift_doubleLevel_iff y hk).trans ?_
    rw [mem_doubleLevel_totalIncl i _ (m + 1) (k + 1) (by omega),
      show m + 1 + i = m + (i + 1) by omega, show k + 1 + i = k + (i + 1) by omega]
    rfl

omit S in
/-- `Y_{m+1,k+1} ⊆ Y[0]_1 = Y_{1,1}`. -/
lemma doubleLevel_succ_subset_levelSet0_one (T : BundledStrongBundle.{u, v}) (m k : ℕ) :
    T.B.doubleLevel (m + 1) (k + 1) ⊆ T.B.toMPolyfold0.levelSet 1 := by
  intro y hy
  obtain ⟨c, hc, hyc⟩ := T.B.atlas.cover y
  obtain ⟨h1, h2⟩ := hy c hc hyc
  exact (StrongBundle.mem_levelSet0_iff (T.B.isChart_of_mem hc) hyc).2
    ⟨StrongBundle.range_toBase_mono _ (by omega) h1,
      StrongBundle.range_toBase_mono _ (by omega) h2⟩

omit S in
/-- `Y_{0,0} = Y`. -/
lemma doubleLevel_zero_zero (T : BundledStrongBundle.{u, v}) (y : T.total) :
    y ∈ T.B.doubleLevel 0 0 :=
  fun _ _ _ => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- Every point of `Y_{m+i,k+i}` comes from a point of `(Y^i)_{m,k}`. -/
theorem exists_totalIncl_eq : ∀ (i m k : ℕ), k ≤ m + 1 → ∀ z : S.total,
    z ∈ S.B.doubleLevel (m + i) (k + i) →
      ∃ y ∈ (S.lift i).B.doubleLevel m k, S.totalIncl i y = z
  | 0, _, _, _, z, hz => ⟨z, hz, rfl⟩
  | i + 1, m, k, hk, z, hz => by
    obtain ⟨y, hy, rfl⟩ := exists_totalIncl_eq i (m + 1) (k + 1) (by omega) z
      (by rwa [show m + 1 + i = m + (i + 1) by omega, show k + 1 + i = k + (i + 1) by omega])
    let y' := (S.lift i).B.toMPolyfold0.levelMk 1 y
      (doubleLevel_succ_subset_levelSet0_one (S.lift i) m k hy)
    exact ⟨y', ((S.lift i).B.mem_shift_doubleLevel_iff y' hk).2 hy, rfl⟩

/-- **The points of `Y^i` are those of `Y_{i,i}`.** -/
theorem range_totalIncl (i : ℕ) : range (S.totalIncl i) = S.B.doubleLevel i i := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    have := (S.mem_doubleLevel_totalIncl i y 0 0 (by omega)).1 (doubleLevel_zero_zero _ y)
    rwa [Nat.zero_add] at this
  · intro hz
    obtain ⟨y, -, hy⟩ := S.exists_totalIncl_eq i 0 0 (by omega) z (by rwa [Nat.zero_add])
    exact ⟨y, hy⟩

/-- **`P ∘ incl = incl ∘ P^i`.** -/
theorem proj_totalIncl : ∀ (i : ℕ) (y : (S.lift i).total),
    S.proj (S.totalIncl i y) = S.baseIncl i ((S.lift i).proj y)
  | 0, _ => rfl
  | i + 1, _ => proj_totalIncl i _

/-! ### The sections `f^i` -/

variable {S} {f : S.base.carrier → S.total}

/-- `f^i` is sc-smooth for an sc-smooth `f`. -/
theorem isScSmoothSection_sectionLift (hf : S.B.IsScSmoothSection f) :
    ∀ i, (S.lift i).B.IsScSmoothSection (S.sectionLift f i)
  | 0 => hf
  | i + 1 => (isScSmoothSection_sectionLift hf i).shift

/-- **`f^i(x) = f(x)`** on the underlying points, for an sc-smooth `f`. -/
theorem totalIncl_sectionLift (hf : S.B.IsScSmoothSection f) :
    ∀ (i : ℕ) (x : (S.lift i).base.carrier),
      S.totalIncl i (S.sectionLift f i x) = f (S.baseIncl i x)
  | 0, _ => rfl
  | i + 1, x =>
    (congrArg (S.totalIncl i)
      (StrongBundle.levelVal_sectionShift (isScSmoothSection_sectionLift hf i) x)).trans
      (totalIncl_sectionLift hf i _)

/-- **The solutions of `f^i` are the solutions of `f` in `X_i`.** -/
theorem solutionSet_sectionLift (hf : S.B.IsScSmoothSection f) :
    ∀ i, solutionSet (S.lift i).proj (S.sectionLift f i) =
      S.baseIncl i ⁻¹' solutionSet S.proj f
  | 0 => rfl
  | i + 1 => by
    change solutionSet (S.lift i).B.shiftProj ((S.lift i).B.sectionShift (S.sectionLift f i)) = _
    rw [StrongBundle.solutionSet_sectionShift (isScSmoothSection_sectionLift hf i),
      solutionSet_sectionLift hf i]
    rfl

/-! ### Corollary 5.2.5 for every `i` -/

variable (S f) in
/-- **The statement of Corollary 5.2.5 for `i`** (2021 p. 213): `f^i` is an sc-Fredholm section of
`P^i : Y^i → X^i` with compact solution set. -/
def Corollary525 (i : ℕ) : Prop :=
  (S.lift i).B.IsScFredholmSection (S.sectionLift f i) ∧
    IsCompact (solutionSet (S.lift i).proj (S.sectionLift f i))

/-- **Corollary 5.2.5, 2021 p. 213, for all `i`**: if `f` is an sc-Fredholm section of the strong
bundle `P : Y → X` (Definition 3.1.16, the germ reading) with compact solution set, then for every
`i` the section `f^i` is an sc-Fredholm section of `P^i : Y^i → X^i` with compact solution set.
Tameness is not used. -/
theorem corollary_5_2_5_family (hf : S.B.IsScFredholmSection f)
    (hS : IsCompact (solutionSet S.proj f)) : ∀ i, Corollary525 S f i
  | 0 => ⟨hf, hS⟩
  | i + 1 =>
    corollary_5_2_5 (corollary_5_2_5_family hf hS i).1 (corollary_5_2_5_family hf hS i).2

/-- **Corollary 5.2.5, 2021 p. 213, for all `i`, with tame germ data** (`corollary_5_2_5_tame`
iterated). -/
theorem corollary_5_2_5_tame_family (hf : S.B.IsScFredholmSectionTame f)
    (hS : IsCompact (solutionSet S.proj f)) :
    ∀ i, (S.lift i).B.IsScFredholmSectionTame (S.sectionLift f i) ∧
      IsCompact (solutionSet (S.lift i).proj (S.sectionLift f i))
  | 0 => ⟨hf, hS⟩
  | i + 1 =>
    corollary_5_2_5_tame (corollary_5_2_5_tame_family hf hS i).1
      (corollary_5_2_5_tame_family hf hS i).2

/-! ### The instances `i = 1, 2` -/

section Instances

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y}

/-- For `i = 1` the statement of the family is that of `corollary_5_2_5`. -/
theorem corollary525_of_one_iff :
    Corollary525 (of B) g 1 ↔
      (B.shift.IsScFredholmSection (B.sectionShift g) ∧
        IsCompact (solutionSet B.shiftProj (B.sectionShift g))) :=
  Iff.rfl

/-- For `i = 2` the statement of the family is that of `corollary_5_2_5_two`. -/
theorem corollary525_of_two_iff :
    Corollary525 (of B) g 2 ↔
      (B.shift.shift.IsScFredholmSection (B.shift.sectionShift (B.sectionShift g)) ∧
        IsCompact (solutionSet B.shift.shiftProj (B.shift.sectionShift (B.sectionShift g)))) :=
  Iff.rfl

/-- **`corollary_5_2_5` is the instance `i = 1` of `corollary_5_2_5_family`.** -/
theorem corollary_5_2_5_family_one (hg : B.IsScFredholmSection g)
    (hS : IsCompact (solutionSet P g)) :
    B.shift.IsScFredholmSection (B.sectionShift g) ∧
      IsCompact (solutionSet B.shiftProj (B.sectionShift g)) :=
  corollary_5_2_5_family (S := of B) hg hS 1

/-- **`corollary_5_2_5_two` is the instance `i = 2` of `corollary_5_2_5_family`.** -/
theorem corollary_5_2_5_family_two (hg : B.IsScFredholmSection g)
    (hS : IsCompact (solutionSet P g)) :
    B.shift.shift.IsScFredholmSection (B.shift.sectionShift (B.sectionShift g)) ∧
      IsCompact (solutionSet B.shift.shiftProj (B.shift.sectionShift (B.sectionShift g))) :=
  corollary_5_2_5_family (S := of B) hg hS 2

end Instances

end BundledStrongBundle

end Polyfold
