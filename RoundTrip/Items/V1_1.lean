import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_1

/-! Round trip for V1_1 (Definition 1.1: sc-structures, sc-Banach spaces, the constant structure,
sums and level shifts).

`A` is the conjunction of the types of the theorems `ScBanach.denseRange_inclK`,
`ScBanach.constScale_smoothLvl`, `ScBanach.prod_smoothLvl` and `ScBanach.shift_smoothLvl` (no
universe parameters: the levels of `ScScale` live in `Type`); `ScScale`, `toBase`, `smooth`,
`smoothLvl`, `ScBanach`, `const`, `prod`, `shift`, `shiftK`, `lvlSet` are vocabulary.  `B` says
(1)/(2) the project's `ScBanach` is exactly the text's sc-structure (up to level-wise isomorphism
compatible with the inclusions), (3) the constant structure on a finite-dimensional space is an
sc-structure and the only one, (4)/(5) sums and level shifts of sc-structures are sc-structures.

* `A → B` (proved): (1)/(2) are glue (`isScStructure_iff`: for a scale, the text's conditions are
  the fields plus the density of `smoothLvl`); (3a) uses `A`'s `constScale_smoothLvl`; (3b) uses
  `A`'s `denseRange_inclK` (the dense range of `E_{m+1} → E_m` is a subspace of a
  finite-dimensional space, hence everything, so the inclusion is an isomorphism); (4) uses `A`'s
  `prod_smoothLvl`; (5) is proved directly (the smooth points of `E^k` at level `m` are those of
  `E` at level `k+m`).
* `B → A` (proved): `denseRange_inclK` and `constScale_smoothLvl` from `B`'s (1) and (3a) (dense
  subspaces of finite-dimensional spaces are everything); `prod_smoothLvl` and `shift_smoothLvl`
  are set equalities about the project's constructions which `B` (density only) does not
  express; they are re-proved from the definitions. -/

namespace RoundTrip.V1_1
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScBanach.denseRange_inclK) ∧
    (type_of% @Polyfold.ScBanach.constScale_smoothLvl) ∧
    (type_of% @Polyfold.ScBanach.prod_smoothLvl) ∧
    (type_of% @Polyfold.ScBanach.shift_smoothLvl)

theorem A_holds : A :=
  ⟨@Polyfold.ScBanach.denseRange_inclK, @Polyfold.ScBanach.constScale_smoothLvl,
    @Polyfold.ScBanach.prod_smoothLvl, @Polyfold.ScBanach.shift_smoothLvl⟩

section Glue

theorem inclTo0_eq (S : ScScale) : ∀ m (x : S.lvl m), inclTo0 S.lvl S.incl m x = S.toBase m x
  | 0, _ => rfl
  | m + 1, x => inclTo0_eq S m (S.incl m x)

theorem preimage_smoothPts (S : ScScale) (m : ℕ) :
    inclTo0 S.lvl S.incl m ⁻¹' smoothPts S.lvl S.incl = S.smoothLvl m := by
  ext x
  simp only [Set.mem_preimage, smoothPts, Set.mem_iInter, Set.mem_range, inclTo0_eq,
    ScScale.mem_smoothLvl_iff]

/-- For a scale, the text's sc-structure conditions are the project's density condition. -/
theorem isScStructure_iff (S : ScScale) :
    IsScStructure S.lvl S.incl ↔ ∀ m, Dense (S.smoothLvl m) := by
  constructor
  · intro h m
    rw [← preimage_smoothPts]
    exact h.2.2.2 m
  · intro h
    refine ⟨S.complete, S.incl_injective, S.incl_isCompactOperator, fun m => ?_⟩
    rw [preimage_smoothPts]
    exact h m

section Mk

variable (X : ℕ → Type) [∀ m, NormedAddCommGroup (X m)] [∀ m, NormedSpace ℝ (X m)]
  (ι : ∀ m, X (m + 1) →L[ℝ] X m)

/-- The project's scale of a text sc-structure. -/
abbrev mkScale (h : IsScStructure X ι) : ScScale where
  lvl := X
  complete := h.1
  incl := ι
  incl_injective := h.2.1
  incl_isCompactOperator := h.2.2.1

/-- The project's sc-Banach space of a text sc-structure. -/
abbrev mkB (h : IsScStructure X ι) : ScBanach where
  toScScale := mkScale X ι h
  dense_smooth := (isScStructure_iff (mkScale X ι h)).1 h

end Mk

/-- A point of `E_n` lies in every `E_j`, `j ≤ n`. -/
theorem range_toBase_anti (S : ScScale) {j n : ℕ} (h : j ≤ n) :
    Set.range (S.toBase n) ⊆ Set.range (S.toBase j) := by
  induction h with
  | refl => exact subset_rfl
  | @step n _ ih =>
    rintro _ ⟨x, rfl⟩
    exact ih ⟨S.incl n x, rfl⟩

/-- The composite inclusions of the shifted structure `(E^k)_m = E_{k+m}` are `inclK`. -/
theorem inclTo0_shift (S : ScScale) (k : ℕ) : ∀ m (x : S.lvl (k + m)),
    inclTo0 (fun m => S.lvl (k + m)) (fun m => S.incl (k + m)) m x = S.inclK k m x
  | 0, _ => rfl
  | m + 1, x => inclTo0_shift S k m (S.incl (k + m) x)

/-- The smooth points of `E^k` at level `m` are those of `E` at level `k + m`. -/
theorem shift_preimage (S : ScScale) (k m : ℕ) :
    inclTo0 (fun m => S.lvl (k + m)) (fun m => S.incl (k + m)) m ⁻¹'
        smoothPts (fun m => S.lvl (k + m)) (fun m => S.incl (k + m)) = S.smoothLvl (k + m) := by
  ext x
  simp only [Set.mem_preimage, smoothPts, Set.mem_iInter, Set.mem_range, inclTo0_shift]
  rw [ScScale.mem_smoothLvl_iff]
  constructor
  · intro H j
    obtain ⟨y, hy⟩ := H j
    have h1 : S.toBase (k + j) y = S.toBase (k + m) x := by
      rw [← S.toBase_inclK, hy, S.toBase_inclK]
    exact range_toBase_anti S (Nat.le_add_left j k) ⟨y, h1⟩
  · intro H j
    obtain ⟨y, hy⟩ := H (k + j)
    exact ⟨y, S.toBase_injective k (by rw [S.toBase_inclK, S.toBase_inclK, hy])⟩

end Glue

theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun E => (isScStructure_iff E.toScScale).2 E.dense_smooth, ?_, ?_, ?_, ?_, ?_⟩
  · -- (2) every text sc-structure is an `ScBanach`
    intro X _ _ ι h
    exact ⟨mkB X ι h, fun m => ContinuousLinearEquiv.refl ℝ (X m), fun _ _ => rfl⟩
  · -- (3a) the constant structure
    intro V _ _ _
    refine (isScStructure_iff (ScBanach.constScale V)).2 fun m => ?_
    rw [hA.2.1 V m]
    exact dense_univ
  · -- (3b) uniqueness in finite dimension
    intro X _ _ ι h hfin m
    let S := mkB X ι h
    have hfd : ∀ n, FiniteDimensional ℝ (X n) := fun n =>
      FiniteDimensional.of_injective (S.toBase n : X n →ₗ[ℝ] X 0) (S.toBase_injective n)
    have hd : DenseRange (ι m) := hA.1 S m 1
    have hcl : IsClosed (Set.range (ι m)) :=
      (LinearMap.range (ι m : X (m + 1) →ₗ[ℝ] X m)).closed_of_finiteDimensional
    have hs : Set.range (ι m) = Set.univ := by
      rw [← hcl.closure_eq]; exact hd.closure_eq
    have := h.1 (m + 1)
    refine ⟨ContinuousLinearEquiv.ofBijective (ι m)
      (LinearMap.ker_eq_bot.2 (h.2.1 m)) (LinearMap.range_eq_top.2 fun y => ?_), rfl⟩
    have : y ∈ Set.range (ι m) := hs ▸ Set.mem_univ y
    exact this
  · -- (4) direct sums
    intro X Y _ _ _ _ ι κ hX hY
    refine (isScStructure_iff ((mkB X ι hX).prod (mkB Y κ hY)).toScScale).2 fun m => ?_
    rw [hA.2.2.1]
    exact ((mkB X ι hX).dense_smooth m).prod ((mkB Y κ hY).dense_smooth m)
  · -- (5) level shifts
    intro X _ _ ι h k
    have hS := (isScStructure_iff (mkScale X ι h)).1 h
    refine ⟨fun m => h.1 (k + m), fun m => h.2.1 (k + m), fun m => h.2.2.1 (k + m), fun m => ?_⟩
    show Dense (inclTo0 (fun m => (mkScale X ι h).lvl (k + m))
      (fun m => (mkScale X ι h).incl (k + m)) m ⁻¹'
        smoothPts (fun m => (mkScale X ι h).lvl (k + m)) (fun m => (mkScale X ι h).incl (k + m)))
    rw [shift_preimage]
    exact hS (k + m)

/-- `prod_smoothLvl`, re-proved from the definitions. -/
theorem prod_smoothLvl' (E F : ScBanach) (m : ℕ) :
    (E.prod F).smoothLvl m = E.smoothLvl m ×ˢ F.smoothLvl m := by
  ext p
  rw [ScScale.mem_smoothLvl_iff, Set.mem_prod, ScScale.mem_smoothLvl_iff,
    ScScale.mem_smoothLvl_iff]
  constructor
  · intro h
    refine ⟨fun j => ?_, fun j => ?_⟩
    · obtain ⟨z, hz⟩ := h j
      rw [ScBanach.prod_toBase, ScBanach.prod_toBase] at hz
      exact ⟨z.1, congrArg Prod.fst hz⟩
    · obtain ⟨z, hz⟩ := h j
      rw [ScBanach.prod_toBase, ScBanach.prod_toBase] at hz
      exact ⟨z.2, congrArg Prod.snd hz⟩
  · rintro ⟨h1, h2⟩ j
    obtain ⟨a, ha⟩ := h1 j
    obtain ⟨b, hb⟩ := h2 j
    refine ⟨show (E.prod F) j from (a, b), ?_⟩
    rw [ScBanach.prod_toBase, ScBanach.prod_toBase]
    exact Prod.ext ha hb

/-- `shift_smoothLvl`, re-proved from the definitions. -/
theorem shift_smoothLvl' (E : ScBanach) (m : ℕ) : E.shift.smoothLvl m = E.smoothLvl (m + 1) := by
  ext x
  rw [ScScale.mem_smoothLvl_iff, ScScale.mem_smoothLvl_iff]
  constructor
  · intro h j
    obtain ⟨y, hy⟩ := h j
    refine ⟨E.incl j y, ?_⟩
    rw [ScBanach.shift_toBase E m x, ← hy]
    exact ScBanach.shift_toBase E j y
  · intro h j
    obtain ⟨y, hy⟩ := h (j + 1)
    refine ⟨y, ?_⟩
    rw [ScBanach.shift_toBase E j y, ScBanach.shift_toBase E m x] at hy
    exact E.toBase_injective 1 hy

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun E m k => ?_, fun V _ _ _ m => ?_, prod_smoothLvl', shift_smoothLvl'⟩
  · have hd : Dense (E.smoothLvl m) := (isScStructure_iff E.toScScale).1 (hB.1 E) m
    exact hd.mono fun x hx => E.exists_inclK_of_mem_smoothLvl hx k
  · have hd : Dense ((ScBanach.constScale V).smoothLvl m) :=
      (isScStructure_iff (ScBanach.constScale V)).1 (hB.2.2.1 V) m
    have hcl : IsClosed ((ScBanach.constScale V).smoothLvl m) :=
      ((ScBanach.constScale V).smooth.comap
        ((ScBanach.constScale V).toBase m : V →ₗ[ℝ] V)).closed_of_finiteDimensional
    rw [← hcl.closure_eq]
    exact hd.closure_eq

#rt_check RoundTrip.V1_1.A_to_B [Polyfold.ScBanach.denseRange_inclK,
  Polyfold.ScBanach.constScale_smoothLvl, Polyfold.ScBanach.prod_smoothLvl,
  Polyfold.ScBanach.shift_smoothLvl]
#rt_check RoundTrip.V1_1.B_to_A [Polyfold.ScBanach.denseRange_inclK,
  Polyfold.ScBanach.constScale_smoothLvl, Polyfold.ScBanach.prod_smoothLvl,
  Polyfold.ScBanach.shift_smoothLvl]
#rt_overlap RoundTrip.V1_1.B_to_A [Polyfold.ScBanach.denseRange_inclK,
  Polyfold.ScBanach.constScale_smoothLvl, Polyfold.ScBanach.prod_smoothLvl,
  Polyfold.ScBanach.shift_smoothLvl]

end RoundTrip.V1_1
