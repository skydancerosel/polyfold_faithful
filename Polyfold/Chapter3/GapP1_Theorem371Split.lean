import Polyfold.Chapter3.GoodPosition
import Polyfold.Chapter2.StrongBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Theorem 3.7.1**
(preprint 3.58), p. 140: the first steps of the reduction of a general sc-splitting to the
coordinates of the proof.

# Coordinates for an sc-splitting `E = B ⊕ X` with `B ⊆ E_∞` finite-dimensional

`Polyfold.theorem_3_7_1` is stated in the coordinates `E = ℝⁿ ⊕ X`, `C = C̃ ⊕ X` of the text's
proof (row V3.89).  The text's hypotheses are a general sc-splitting `E = B ⊕ X` with `B`
finite-dimensional and `X ⊆ C`.  This file supplies the coordinates on the source side:

* `ScBanach.splitScIso hBX hBs : ScIso E (B ⊕ X)`: for an sc-splitting `E = B ⊕ X` with
  `B ⊆ E_∞` finite-dimensional, `v ↦ (π_B v, v − π_B v)` on every level (`π_B v` lifted to `E_m`,
  `smoothLiftB`); `splitScIso_zero_fst`, `splitScIso_symm_apply`;
* `IsPartialQuadrant.add_mem`: a partial quadrant is closed under addition, hence
  `IsPartialQuadrant.add_mem_iff_of_mem`: `x ∈ C` with `-x ∈ C` gives `c + x ∈ C ↔ c ∈ C`;
* `isInGoodPosition_of_isScSplitting`: if `X ⊆ C`, then `B` is in good position to `C`, with good
  complement `X`;
* **`isPartialQuadrant_of_isScSplitting`**: then `C ∩ B` is a partial quadrant in `B`
  (Proposition 3.1.25), and **`splitScIso_preimage`**: the coordinates carry `C` onto
  `(C ∩ B) ⊕ X`, a partial quadrant of `B ⊕ X` (`isPartialQuadrant_split`).

In the coordinates of `splitScIso`, the partial quadrant is therefore of the form `C̃ ⊕ X` of the
proof; the remaining steps of the reduction (row V3.89) are listed in the hand-over note.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

namespace ScBanach

variable {E : ScBanach} {B X : Submodule ℝ (E 0)}

/-- The base level of an sc-splitting is an algebraic splitting. -/
lemma IsScSplitting.isCompl_zero (hBX : E.IsScSplitting B X) : IsCompl B X := by
  have := hBX.2.2 0
  rwa [levelSub_zero, levelSub_zero] at this

/-- The continuous projection `π_B : E₀ → B` along `X`. -/
def splitProjB (hBX : E.IsScSplitting B X) : E 0 →L[ℝ] B :=
  B.projectionOntoL X
    (Submodule.IsCompl.isTopCompl_of_isClosed hBX.isCompl_zero hBX.1.1 hBX.2.1.1)

lemma splitProjB_apply (hBX : E.IsScSplitting B X) (v : E 0) :
    (splitProjB hBX v : E 0) = B.projection X hBX.isCompl_zero v := by
  rw [splitProjB, congrFun (Submodule.coe_projectionOntoL _) v,
    Submodule.coe_projectionOnto_apply]

lemma splitProjB_apply_left (hBX : E.IsScSplitting B X) (b : B) : splitProjB hBX b = b :=
  Submodule.projectionOntoL_apply_left _ b

lemma splitProjB_apply_right (hBX : E.IsScSplitting B X) {x : E 0} (hx : x ∈ X) :
    splitProjB hBX x = 0 :=
  Submodule.projectionOntoL_apply_right _ ⟨x, hx⟩

lemma sub_splitProjB_mem (hBX : E.IsScSplitting B X) (v : E 0) :
    v - (splitProjB hBX v : E 0) ∈ X := by
  rw [splitProjB_apply]; exact Submodule.sub_projection_mem _ v

variable (hBs : B ≤ E.smooth)

/-- The lift of `b ∈ B ⊆ E_∞` to the level `m`. -/
def smoothLiftB (m : ℕ) (b : B) : E m :=
  ((ScScale.mem_smooth_iff E.toScScale).1 (hBs b.2) m).choose

lemma toBase_smoothLiftB (m : ℕ) (b : B) : E.toBase m (smoothLiftB hBs m b) = b :=
  ((ScScale.mem_smooth_iff E.toScScale).1 (hBs b.2) m).choose_spec

/-- The lift `B → E_m` as a linear map. -/
def liftBLin (m : ℕ) : B →ₗ[ℝ] E m where
  toFun := smoothLiftB hBs m
  map_add' a b := E.toBase_injective m (by
    rw [map_add, toBase_smoothLiftB, toBase_smoothLiftB, toBase_smoothLiftB, Submodule.coe_add])
  map_smul' t b := E.toBase_injective m (by
    rw [map_smul, toBase_smoothLiftB, toBase_smoothLiftB, Submodule.coe_smul, RingHom.id_apply])

variable [FiniteDimensional ℝ B]

/-- The lift `B → E_m`, continuous since `B` is finite-dimensional. -/
def liftB (m : ℕ) : B →L[ℝ] E m := LinearMap.toContinuousLinearMap (liftBLin hBs m)

lemma liftB_apply (m : ℕ) (b : B) : liftB hBs m b = smoothLiftB hBs m b := rfl

lemma toBase_liftB (m : ℕ) (b : B) : E.toBase m (liftB hBs m b) = b := toBase_smoothLiftB hBs m b

lemma incl_liftB (m : ℕ) (b : B) : E.incl m (liftB hBs (m + 1) b) = liftB hBs m b :=
  E.toBase_injective m (by rw [← E.toBase_succ, toBase_liftB, toBase_liftB])

variable (hBX : E.IsScSplitting B X)

lemma sub_liftB_mem (m : ℕ) (v : E m) :
    v - liftB hBs m (splitProjB hBX (E.toBase m v)) ∈ E.levelSub X m := by
  rw [mem_levelSub, map_sub, toBase_liftB]; exact sub_splitProjB_mem hBX _

/-- The forward map `v ↦ (π_B v, v − π_B v)` on level `m`. -/
def splitFwdL (m : ℕ) : E m →L[ℝ] B × E.levelSub X m :=
  ((splitProjB hBX).comp (E.toBase m)).prod
    ((ContinuousLinearMap.id ℝ (E m) -
      (liftB hBs m).comp ((splitProjB hBX).comp (E.toBase m))).codRestrict (E.levelSub X m)
      (sub_liftB_mem hBs hBX m))

/-- The backward map `(b, x) ↦ b + x` on level `m`. -/
def splitBwdL (m : ℕ) : B × E.levelSub X m →L[ℝ] E m :=
  (liftB hBs m).comp (ContinuousLinearMap.fst ℝ B (E.levelSub X m)) +
    (E.levelSub X m).subtypeL.comp (ContinuousLinearMap.snd ℝ B (E.levelSub X m))

lemma splitFwdL_apply (m : ℕ) (v : E m) :
    splitFwdL hBs hBX m v = (splitProjB hBX (E.toBase m v),
      ⟨v - liftB hBs m (splitProjB hBX (E.toBase m v)), sub_liftB_mem hBs hBX m v⟩) := rfl

lemma splitBwdL_apply (m : ℕ) (p : B × E.levelSub X m) :
    splitBwdL hBs m p = liftB hBs m p.1 + (p.2 : E m) := rfl

lemma splitBwdL_splitFwdL (m : ℕ) (v : E m) : splitBwdL hBs m (splitFwdL hBs hBX m v) = v := by
  rw [splitBwdL_apply, splitFwdL_apply]
  exact add_sub_cancel _ v

lemma splitFwdL_splitBwdL (m : ℕ) (p : B × E.levelSub X m) :
    splitFwdL hBs hBX m (splitBwdL hBs m p) = p := by
  have hπ : splitProjB hBX (E.toBase m (splitBwdL hBs m p)) = p.1 := by
    rw [splitBwdL_apply, map_add, toBase_liftB, map_add, splitProjB_apply_left,
      splitProjB_apply_right hBX (x := E.toBase m (p.2 : E m)) p.2.2, add_zero]
  rw [splitFwdL_apply]
  refine Prod.ext hπ (Subtype.ext ?_)
  change splitBwdL hBs m p - liftB hBs m (splitProjB hBX (E.toBase m (splitBwdL hBs m p))) =
    (p.2 : E m)
  rw [hπ, splitBwdL_apply, add_sub_cancel_left]

/-- **The coordinates of an sc-splitting `E = B ⊕ X` with `B ⊆ E_∞` finite-dimensional**: the
sc-isomorphism `E ≅ B ⊕ X`, `v ↦ (π_B v, v − π_B v)`. -/
def splitScIso : ScIso E ((ScBanach.const B).prod (E.ofSubspace hBX.2.1)) where
  lvl m := ContinuousLinearEquiv.equivOfInverse (splitFwdL hBs hBX m) (splitBwdL hBs m)
    (splitBwdL_splitFwdL hBs hBX m) (splitFwdL_splitBwdL hBs hBX m)
  incl_comm m v := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change splitProjB hBX (E.toBase (m + 1) v) = splitProjB hBX (E.toBase m (E.incl m v))
      rw [E.toBase_succ]
    · change E.incl m (v - liftB hBs (m + 1) (splitProjB hBX (E.toBase (m + 1) v))) =
        E.incl m v - liftB hBs m (splitProjB hBX (E.toBase m (E.incl m v)))
      rw [map_sub, incl_liftB, E.toBase_succ]

lemma splitScIso_zero_fst (v : E 0) : (splitScIso hBs hBX 0 v).1 = splitProjB hBX v := rfl

lemma splitScIso_zero_snd (v : E 0) :
    (show E.levelSub X 0 from (splitScIso hBs hBX 0 v).2).1 = v - (splitProjB hBX v : E 0) := by
  change v - liftB hBs 0 (splitProjB hBX (E.toBase 0 v)) = _
  rw [E.toBase_zero]
  congr 1
  exact toBase_liftB hBs 0 _

lemma splitScIso_symm_apply (m : ℕ) (p : B × E.levelSub X m) :
    (splitScIso hBs hBX m).symm p = liftB hBs m p.1 + (p.2 : E m) := rfl

end ScBanach

/-! ### The partial quadrant in the coordinates of the splitting -/

section Quadrant

variable {E : ScBanach} {C : Set (E 0)}

/-- A partial quadrant is closed under addition. -/
lemma IsPartialQuadrant.add_mem (hC : IsPartialQuadrant E C) {x y : E 0} (hx : x ∈ C)
    (hy : y ∈ C) : x + y ∈ C := by
  obtain ⟨n, W, T, rfl⟩ := hC
  intro i
  have h1 : 0 ≤ (T 0 x).1 i := hx i
  have h2 : 0 ≤ (T 0 y).1 i := hy i
  change 0 ≤ (T 0 (x + y)).1 i
  rw [map_add]
  exact add_nonneg h1 h2

/-- Adding an element of the lineality space does not change membership in a partial quadrant. -/
lemma IsPartialQuadrant.add_mem_iff_of_mem (hC : IsPartialQuadrant E C) {x : E 0} (hx : x ∈ C)
    (hx' : -x ∈ C) (c : E 0) : c + x ∈ C ↔ c ∈ C := by
  refine ⟨fun h => ?_, fun h => IsPartialQuadrant.add_mem hC h hx⟩
  have := IsPartialQuadrant.add_mem hC h hx'
  rwa [add_neg_cancel_right] at this

variable {B X : Submodule ℝ (E 0)}

/-- **`B` is in good position to `C` when `X ⊆ C`**, for an sc-splitting `E = B ⊕ X`: `X` is a
good complement (with any `ε`), and the projection of an interior point of `C` to `B` is interior
to `C ∩ B` in `B`. -/
theorem isInGoodPosition_of_isScSplitting (hC : IsPartialQuadrant E C)
    (hBX : E.IsScSplitting B X) (hXC : (X : Set (E 0)) ⊆ C) : IsInGoodPosition E C B := by
  have hXl : ∀ x ∈ X, ∀ c : E 0, c + x ∈ C ↔ c ∈ C := fun x hx c =>
    IsPartialQuadrant.add_mem_iff_of_mem hC (hXC hx) (hXC (X.neg_mem hx)) c
  refine ⟨?_, ⟨X, hBX.isCompl_zero, 1, one_pos, fun b _ x hx _ => (hXl x hx b).symm⟩⟩
  -- an interior point of `C`
  obtain ⟨c, hc⟩ := IsPartialQuadrant.interior_lvlSet_nonempty hC 0
  rw [ScBanach.lvlSet_zero] at hc
  set b : B := ScBanach.splitProjB hBX c
  have hxc : (b : E 0) - c ∈ X := by
    have := X.neg_mem (ScBanach.sub_splitProjB_mem hBX c)
    rwa [neg_sub] at this
  -- `interior C + x ⊆ interior C` for `x ∈ X`
  have hbint : (b : E 0) ∈ interior C := by
    obtain ⟨U, hUC, hUo, hcU⟩ := mem_interior.1 hc
    refine mem_interior.2 ⟨(fun v => v + ((b : E 0) - c)) '' U, ?_, isOpenMap_add_right _ U hUo,
      ⟨c, hcU, add_sub_cancel c _⟩⟩
    rintro _ ⟨v, hv, rfl⟩
    exact (hXl _ hxc v).2 (hUC hv)
  refine ⟨b, ?_⟩
  have hopen : IsOpen (Subtype.val ⁻¹' interior C : Set B) :=
    isOpen_interior.preimage continuous_subtype_val
  exact mem_interior.2 ⟨_, preimage_mono interior_subset, hopen, hbint⟩

/-- **`C ∩ B` is a partial quadrant in `B`** when `X ⊆ C` (Proposition 3.1.25 (preprint 3.22)
with `isInGoodPosition_of_isScSplitting`). -/
theorem isPartialQuadrant_of_isScSplitting (hC : IsPartialQuadrant E C)
    (hBX : E.IsScSplitting B X) [FiniteDimensional ℝ B] (hXC : (X : Set (E 0)) ⊆ C) :
    IsPartialQuadrant (ScBanach.const B) (Subtype.val ⁻¹' C) :=
  proposition_3_1_25 hC (isInGoodPosition_of_isScSplitting hC hBX hXC)

/-- **The coordinates carry `C` onto `(C ∩ B) ⊕ X`**: for `X ⊆ C`, `v ∈ C ↔ π_B v ∈ C`. -/
theorem splitScIso_preimage (hC : IsPartialQuadrant E C) (hBX : E.IsScSplitting B X)
    (hBs : B ≤ E.smooth) [FiniteDimensional ℝ B] (hXC : (X : Set (E 0)) ⊆ C) :
    ScBanach.splitScIso hBs hBX 0 ⁻¹'
      ((Subtype.val ⁻¹' C : Set B) ×ˢ (univ : Set ((E.ofSubspace hBX.2.1) 0))) = C := by
  ext v
  simp only [mem_preimage, mem_prod, mem_univ, and_true]
  rw [ScBanach.splitScIso_zero_fst]
  have hx := ScBanach.sub_splitProjB_mem hBX v
  have h := IsPartialQuadrant.add_mem_iff_of_mem hC (hXC hx) (hXC (X.neg_mem hx))
    (ScBanach.splitProjB hBX v : E 0)
  rw [add_sub_cancel] at h
  exact h.symm

/-- In the coordinates of the splitting, `(C ∩ B) ⊕ X` is a partial quadrant of `B ⊕ X`. -/
theorem isPartialQuadrant_split (hC : IsPartialQuadrant E C) (hBX : E.IsScSplitting B X)
    [FiniteDimensional ℝ B] (hXC : (X : Set (E 0)) ⊆ C) :
    IsPartialQuadrant ((ScBanach.const B).prod (E.ofSubspace hBX.2.1))
      ((Subtype.val ⁻¹' C : Set B) ×ˢ (univ : Set ((E.ofSubspace hBX.2.1) 0))) :=
  IsPartialQuadrant.prod_univ (isPartialQuadrant_of_isScSplitting hC hBX hXC) _

end Quadrant

end Polyfold
