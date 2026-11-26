import GWMemoir.HalfCylinders
import GWMemoir.Witnesses

/-!
# The section spaces `H^{3,δ₀}_c(S, u*TQ)` and `E_u` (Memoir pp. 66–68)

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §3.1, pp. 66–68.

The memoir defines `H^{3,δ₀}_c(S, u*TQ)` as the sections of class `(3, δ₀)` with matching
asymptotic constants at the nodes, normed by a finite sum of semi-norms (p. 66): around a point
which is not nodal, the `H³` norm of a cut-off of the section in a disc chart and a
trivialization; at a nodal point `x`, in positive holomorphic polar coordinates `σ_x` and a chart
`ψ` of `Q` at `u(x)`, `|c|² + ‖β⁺(v⁺ - c)‖²_{3,δ₀}` with `v⁺ = Tψ ∘ η ∘ σ_x` and `c` the asymptotic
constant.  "Using a suitable choice of finitely many semi-norms of this type, one can define
complete norms".  We write this as follows.

* `finPiSc F`: the finite product of sc-Banach spaces (levels `∏ᵢ (F i)_m`, sup norm).
* `SectionAtlas X u`: a fixed choice of the semi-norms: disc charts placed in the strip
  `ℝ × (0,1)` as in `IsHlocNear` (centre `z`, scale `ε`), avoiding the nodal points, and at every
  nodal point a holomorphic chart with polar coordinates from `s₀` on, as in `IsClassNear`; the
  regions where the cut-offs are `1` cover `S`.  The trivialization of `u*TQ` on a piece is the
  tangent coordinate change of `Q` to the chart at `u(z)`; vectors are taken in coordinates of a
  basis of `E`, so that every block is real-valued.
* `blocks δ A`: the product `∏_{discs × coordinates} H^{3+m,δ_m}(ℝ × S¹) ×
  ∏_{nodal points × coordinates} (ℝ ⊕ H^{3+m,δ_m}(ℝ × S¹))`.  The disc representatives have
  compact support in the strip, so the weight does not change their norm class (strip-placed
  `H^{3+m}`).  The neck block is `scCylC` of `GWMemoir.HalfCylinders`, `(c, β⁺(v⁺ - c))`: the
  cut-off vanishes for `s ≤ 0`, so its norm on `ℝ × S¹` is the memoir's norm on `ℝ⁺ × S¹`.  At both
  points of a nodal pair we use positive polar coordinates; the memoir's negative coordinates at
  `y` differ by the reflection `(s, t) ↦ (-s, -t)`, which preserves the norms.
* `sectionsSub δ A`: the tuples of local representatives of the sections `η` along `u` that are
  continuous and have matching values at the nodal pairs (the asymptotic constants `η(x) = η(y)`).
  `sectionSpace δ A` is its closure.  The memoir's statement that the norm is complete is
  `SectionsClosed` (the set of representatives is closed); under it the two agree
  (`sectionSpace_eq`), and the level `m` of the induced scale (`sectionScale`) consists of the
  sections whose representatives lie in `H^{3+m,δ_m}`, i.e. of class `(3+m, δ_m)`
  (`mem_sectionScale_iff`).  The density of the smooth sections in each level, which makes it an
  sc-Banach space, is the named proposition `SectionsDense` (`sectionSc`).
* `LinearConstraints X`: points `z ∈ Σ` and linear subspaces `H_{u(z)} ⊆ T_{u(z)}Q`;
  `constraintsSub` and its closure `uSpace` are `E_u = {η | η(z) ∈ H_{u(z)}, z ∈ Σ}` (p. 68).  The
  point evaluations are continuous on `H³` (Sobolev embedding, not formalized), which is
  `ConstraintsClosed`.
* Witnesses: `exists_sectionAtlas` (a surface without nodes has an atlas, by compactness, for any
  continuous `u`), and `constBlocks_mem` (for a constant map, a constant section has its
  representatives in the blocks).
* The independence of the choice of atlas (equivalence of the norms) is not formalized.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Set Filter Topology MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Finite products of sc-Banach spaces -/

section Pi

variable {ι : Type} [Fintype ι]

/-- The product `∏ᵢ F i` of finitely many scales, with levels `∏ᵢ (F i)_m` (sup norm). -/
def finPiScale (F : ι → ScScale) : ScScale where
  lvl m := ∀ i, F i m
  incl m := ContinuousLinearMap.pi fun i => ((F i).incl m).comp (ContinuousLinearMap.proj i)
  incl_injective m x y h := funext fun i => (F i).incl_injective m (congrFun h i)
  incl_isCompactOperator m := by
    choose K hK hK' using fun i => (F i).incl_isCompactOperator m
    refine ⟨Set.pi univ K, isCompact_univ_pi hK, ?_⟩
    have : (ContinuousLinearMap.pi fun i => ((F i).incl m).comp (ContinuousLinearMap.proj i)) ⁻¹'
        Set.pi univ K = Set.pi univ fun i => (F i).incl m ⁻¹' K i := by
      ext x; simp
    rw [this]
    exact set_pi_mem_nhds finite_univ fun i _ => hK' i

lemma finPiScale_toBase (F : ι → ScScale) (m : ℕ) (x : (finPiScale F) m) :
    (finPiScale F).toBase m x = ((fun i => (F i).toBase m (x i)) : (finPiScale F) 0) := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih _

/-- The product of finitely many sc-Banach spaces. -/
def finPiSc (F : ι → ScBanach) : ScBanach where
  toScScale := finPiScale fun i => (F i).toScScale
  dense_smooth m := by
    refine (dense_pi univ fun i _ => (F i).dense_smooth m).mono ?_
    intro x hx
    refine ((finPiScale fun i => (F i).toScScale).mem_smoothLvl_iff).2 fun j => ?_
    choose y hy using fun i => ((F i).mem_smoothLvl_iff).1 (hx i (mem_univ i)) j
    refine ⟨show (finPiScale fun i => (F i).toScScale) j from y, ?_⟩
    exact (finPiScale_toBase _ j y).trans ((funext hy).trans (finPiScale_toBase _ m x).symm)

end Pi

/-! ## 2. The atlas of semi-norms -/

section Atlas

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} (X : NodalSurface m) (u : X.S → Q)

/-- The cut-off of the disc semi-norms, `1` for `r ≤ 1/4`, `0` for `r² ≥ 1/8`, where
`r² = s² + (t - 1/2)²` (the cut-off of `IsHlocNear`). -/
def discCut (p : ℝ × ℝ) : ℝ := Real.smoothTransition (2 - 16 * (p.1 ^ 2 + (p.2 - 1 / 2) ^ 2))

/-- The point of `S` at the strip coordinate `p` of the disc chart centred at `z`, scale `ε`. -/
def NodalSurface.discPt (z : X.S) (ε : ℝ) (p : ℝ × ℝ) : X.S :=
  (extChartAt 𝓘(ℝ, E2) z).symm (X.place z ε p)

/-- A fixed choice of the semi-norms of Memoir p. 66: disc charts away from the nodes and polar
coordinates at the nodal points, whose regions (where the cut-offs are `1`) cover `S`. -/
structure SectionAtlas where
  /-- The number of disc charts. -/
  nd : ℕ
  center : Fin nd → X.S
  ε : Fin nd → ℝ
  ε_pos : ∀ i, 0 < ε i
  disc_chart : ∀ i (p : ℝ × ℝ), p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 < 1 / 8 →
    X.place (center i) (ε i) p ∈ (extChartAt 𝓘(ℝ, E2) (center i)).target ∧
      u (X.discPt (center i) (ε i) p) ∈ (extChartAt 𝓘(ℝ, E) (u (center i))).source
  disc_avoid : ∀ i (p : ℝ × ℝ), p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 < 1 / 8 →
    ∀ q ∈ X.nodes, X.discPt (center i) (ε i) p ∉ q
  /-- The number of neck charts, one at each nodal point. -/
  nn : ℕ
  node : Fin nn → X.S
  hol : Fin nn → OpenPartialHomeomorph X.S ℂ
  s0 : Fin nn → ℝ
  isHol : ∀ j, X.IsHolChart (hol j) (node j)
  neck_chart : ∀ j (p : ℝ × ℝ), s0 j ≤ p.1 →
    X.polar (hol j) p ∈ (hol j).source ∧
      u (X.polar (hol j) p) ∈ (extChartAt 𝓘(ℝ, E) (u (node j))).source
  node_nodal : ∀ j, ∃ q ∈ X.nodes, node j ∈ q
  nodal_node : ∀ q ∈ X.nodes, ∀ x ∈ q, ∃ j, node j = x
  cover : ∀ y : X.S,
    (∃ i, ∃ p : ℝ × ℝ, p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 ≤ 1 / 16 ∧ y = X.discPt (center i) (ε i) p) ∨
      ∃ j, y = node j ∨ ∃ p : ℝ × ℝ, s0 j + 1 ≤ p.1 ∧ y = X.polar (hol j) p

variable {X u}
variable (A : SectionAtlas (E := E) X u)

/-- The `k`-th coordinate in the fixed basis of `E`. -/
abbrev crd (k : Fin (Module.finrank ℝ E)) : E →ₗ[ℝ] ℝ := (Module.finBasis ℝ E).coord k

/-- A section of `u*TQ`: `η x ∈ T_{u(x)}Q`, which is `E` (Mathlib's `TangentSpace`), the vector
being read in the chart of `Q` at `u(x)`. -/
abbrev Section (E : Type) {m : ℕ} (X : NodalSurface m) : Type := X.S → E

/-- The local representative of `η` in the disc chart `i`, coordinate `k`:
`β(p) · e_k*(Γ_i η(z_p))`, `Γ_i` the tangent coordinate change of `Q` to the chart at `u(zᵢ)`. -/
def discRep (i : Fin A.nd) (k : Fin (Module.finrank ℝ E)) (η : Section E X) : ℝ × ℝ → ℝ :=
  fun p => discCut p * crd k (tangentCoordChange 𝓘(ℝ, E) (u (X.discPt (A.center i) (A.ε i) p))
    (u (A.center i)) (u (X.discPt (A.center i) (A.ε i) p)) (η (X.discPt (A.center i) (A.ε i) p)))

/-- The asymptotic constant at the nodal point `j`, coordinate `k`: `e_k*(η(x_j))`. -/
def neckConst (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) (η : Section E X) : ℝ :=
  crd k (η (A.node j))

/-- The neck representative `β⁺(s) (v⁺(s,t) - c)`, `v⁺ = e_k*(Γ_j η ∘ σ_j)(s + s₀, t)`. -/
def neckRep (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) (η : Section E X) : ℝ × ℝ → ℝ :=
  fun p => Real.smoothTransition p.1 *
    (crd k (tangentCoordChange 𝓘(ℝ, E) (u (X.polar (A.hol j) (p.1 + A.s0 j, p.2)))
      (u (A.node j)) (u (X.polar (A.hol j) (p.1 + A.s0 j, p.2)))
      (η (X.polar (A.hol j) (p.1 + A.s0 j, p.2)))) - neckConst A j k η)

variable (u) in
/-- `η` is continuous, read in the tangent coordinates of `Q` at each point. -/
def IsContSection (η : Section E X) : Prop :=
  ∀ x, ContinuousAt (fun y => tangentCoordChange 𝓘(ℝ, E) (u y) (u x) (u y) (η y)) x

variable (X) in
/-- Matching values at the nodal pairs: `η(x) = η(y) ∈ T_{u(x)}Q`. -/
def IsMatchingSection (η : Section E X) : Prop :=
  ∀ x y, s(x, y) ∈ X.nodes → (η x : E) = η y

variable (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The block space: `∏_{discs × coordinates} H^{3+m,δ_m}(ℝ × S¹) ×
∏_{nodal points × coordinates} (ℝ ⊕ H^{3+m,δ_m}(ℝ × S¹))`. -/
def blocks : ScBanach :=
  (finPiSc fun _ : Fin A.nd × Fin (Module.finrank ℝ E) => Neck.scCyl δ h0 hmono).prod
    (finPiSc fun _ : Fin A.nn × Fin (Module.finrank ℝ E) => Neck.scCylC δ h0 hmono)

variable {A δ h0 hmono}

/-- The disc block `(i, k)` of a level-`0` element. -/
def discBlock (v : (blocks A δ h0 hmono) 0) (i : Fin A.nd) (k : Fin (Module.finrank ℝ E)) :
    H 3 (Neck.δ_nonneg δ h0 hmono 0) := v.1 (i, k)

/-- The neck block `(j, k)`: the constant and the cut-off remainder. -/
def neckBlock (v : (blocks A δ h0 hmono) 0) (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) :
    ℝ × H 3 (Neck.δ_nonneg δ h0 hmono 0) := v.2 (j, k)

/-- `v` is the tuple of local representatives of `η`. -/
def IsRep (η : Section E X) (v : (blocks A δ h0 hmono) 0) : Prop :=
  (∀ i k, (H.val (discBlock v i k) : ℝ × ℝ → ℝ) =ᵐ[cyl] discRep A i k η) ∧
    ∀ j k, (neckBlock v j k).1 = neckConst A j k η ∧
      (H.val (neckBlock v j k).2 : ℝ × ℝ → ℝ) =ᵐ[cyl] neckRep A j k η

lemma discRep_add (i k) (η η' : Section E X) :
    discRep A i k (η + η') = discRep A i k η + discRep A i k η' := by
  funext p; simp only [discRep, Pi.add_apply, map_add, mul_add]

lemma discRep_smul (i k) (c : ℝ) (η : Section E X) :
    discRep A i k (c • η) = c • discRep A i k η := by
  funext p; simp only [discRep, Pi.smul_apply, map_smul, smul_eq_mul]; ring

lemma neckRep_add (j k) (η η' : Section E X) :
    neckRep A j k (η + η') = neckRep A j k η + neckRep A j k η' := by
  funext p; simp only [neckRep, neckConst, Pi.add_apply, map_add]; ring

lemma neckRep_smul (j k) (c : ℝ) (η : Section E X) :
    neckRep A j k (c • η) = c • neckRep A j k η := by
  funext p; simp only [neckRep, neckConst, Pi.smul_apply, map_smul, smul_eq_mul]; ring

lemma val_add_ae {k : ℕ} {d : ℝ} {hd : 0 ≤ d} (a b : H k hd) :
    (H.val (a + b) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => H.val a x + H.val b x :=
  Lp.coeFn_add (H.val a) (H.val b)

lemma val_smul_ae {k : ℕ} {d : ℝ} {hd : 0 ≤ d} (c : ℝ) (a : H k hd) :
    (H.val (c • a) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => c • H.val a x :=
  Lp.coeFn_smul c (H.val a)

lemma val_zero_ae {k : ℕ} {d : ℝ} {hd : 0 ≤ d} :
    (H.val (0 : H k hd) : ℝ × ℝ → ℝ) =ᵐ[cyl] 0 :=
  Lp.coeFn_zero ℝ 2 cyl

lemma discBlock_zero (i k) : discBlock (0 : (blocks A δ h0 hmono) 0) i k = 0 := rfl

lemma neckBlock_zero (j k) : neckBlock (0 : (blocks A δ h0 hmono) 0) j k = 0 := rfl

lemma isRep_zero : IsRep (A := A) (δ := δ) (h0 := h0) (hmono := hmono) (0 : Section E X) 0 := by
  refine ⟨fun i k => ?_, fun j k => ⟨?_, ?_⟩⟩
  · rw [discBlock_zero]
    filter_upwards [val_zero_ae (k := 3) (hd := Neck.δ_nonneg δ h0 hmono 0)] with p hp
    rw [hp]; simp [discRep]
  · rw [neckBlock_zero]; simp [neckConst]
  · rw [show (neckBlock (0 : (blocks A δ h0 hmono) 0) j k).2 = 0 from rfl]
    filter_upwards [val_zero_ae (k := 3) (hd := Neck.δ_nonneg δ h0 hmono 0)] with p hp
    rw [hp]; simp [neckRep, neckConst]

lemma IsRep.add {η η' : Section E X} {v v' : (blocks A δ h0 hmono) 0} (h : IsRep η v)
    (h' : IsRep η' v') : IsRep (η + η') (v + v') := by
  refine ⟨fun i k => ?_, fun j k => ⟨?_, ?_⟩⟩
  · rw [discRep_add]
    filter_upwards [val_add_ae (discBlock v i k) (discBlock v' i k), h.1 i k, h'.1 i k]
      with p h1 h2 h3
    exact h1.trans (by rw [h2, h3]; rfl)
  · change (neckBlock v j k).1 + (neckBlock v' j k).1 = _
    rw [(h.2 j k).1, (h'.2 j k).1]
    simp [neckConst]
  · rw [neckRep_add]
    filter_upwards [val_add_ae (neckBlock v j k).2 (neckBlock v' j k).2, (h.2 j k).2,
      (h'.2 j k).2] with p h1 h2 h3
    exact h1.trans (by rw [h2, h3]; rfl)

lemma IsRep.smul {η : Section E X} {v : (blocks A δ h0 hmono) 0} (h : IsRep η v) (c : ℝ) :
    IsRep (c • η) (c • v) := by
  refine ⟨fun i k => ?_, fun j k => ⟨?_, ?_⟩⟩
  · rw [discRep_smul]
    filter_upwards [val_smul_ae c (discBlock v i k), h.1 i k] with p h1 h2
    exact h1.trans (by rw [h2]; rfl)
  · change c • (neckBlock v j k).1 = _
    rw [(h.2 j k).1]
    simp [neckConst]
  · rw [neckRep_smul]
    filter_upwards [val_smul_ae c (neckBlock v j k).2, (h.2 j k).2] with p h1 h2
    exact h1.trans (by rw [h2]; rfl)

lemma isContSection_zero : IsContSection u (0 : Section E X) := fun x => by
  simp only [Pi.zero_apply, map_zero]; exact continuousAt_const

lemma IsContSection.add {η η' : Section E X} (h : IsContSection u η) (h' : IsContSection u η') :
    IsContSection u (η + η') := fun x => by
  simp only [Pi.add_apply, map_add]; exact (h x).add (h' x)

lemma IsContSection.smul {η : Section E X} (h : IsContSection u η) (c : ℝ) :
    IsContSection u (c • η) := fun x => by
  simp only [Pi.smul_apply, map_smul]; exact (h x).const_smul c

variable (A δ h0 hmono)

/-- The tuples of local representatives of the continuous sections `η` along `u` with matching
values at the nodal pairs. -/
def sectionsSub : Submodule ℝ ((blocks A δ h0 hmono) 0) where
  carrier := {v | ∃ η : Section E X, IsContSection u η ∧ IsMatchingSection X η ∧ IsRep η v}
  zero_mem' := ⟨(0 : Section E X), isContSection_zero (u := u), fun _ _ _ => rfl, isRep_zero⟩
  add_mem' := by
    rintro v v' ⟨η, hc, hm, hr⟩ ⟨η', hc', hm', hr'⟩
    refine ⟨η + η', hc.add hc', fun x y hxy => ?_, hr.add hr'⟩
    change (η x : E) + η' x = η y + η' y
    rw [hm x y hxy, hm' x y hxy]
  smul_mem' := by
    rintro c v ⟨η, hc, hm, hr⟩
    refine ⟨c • η, hc.smul c, fun x y hxy => ?_, hr.smul c⟩
    change c • (η x : E) = c • η y
    rw [hm x y hxy]

/-- **`H^{3,δ₀}_c(S, u*TQ)`** (Memoir p. 66), as a closed subspace of the block space: the closure
of the representatives of the sections. -/
def sectionSpace : Submodule ℝ ((blocks A δ h0 hmono) 0) :=
  (sectionsSub A δ h0 hmono).topologicalClosure

lemma isClosed_sectionSpace :
    IsClosed (sectionSpace A δ h0 hmono : Set ((blocks A δ h0 hmono) 0)) :=
  Submodule.isClosed_topologicalClosure _

/-- The memoir's completeness of the norm (p. 66): the representatives of the sections of class
`(3, δ₀)` form a closed set. -/
def SectionsClosed : Prop := IsClosed (sectionsSub A δ h0 hmono : Set ((blocks A δ h0 hmono) 0))

theorem sectionSpace_eq (h : SectionsClosed A δ h0 hmono) :
    sectionSpace A δ h0 hmono = sectionsSub A δ h0 hmono :=
  IsClosed.submodule_topologicalClosure_eq h

/-- The scale of `H^{3,δ₀}_c(S, u*TQ)`: levels `A_m = A ∩ (blocks)_m`, with compact inclusions. -/
def sectionScale : ScScale :=
  (blocks A δ h0 hmono).ofSubspaceScale (isClosed_sectionSpace A δ h0 hmono)

/-- Level `m` of the scale: the sections whose representatives lie in the level-`m` blocks
`H^{3+m,δ_m}`, i.e. the sections of class `(3+m, δ_m)` (given `SectionsClosed`). -/
theorem mem_sectionScale_iff (h : SectionsClosed A δ h0 hmono) (k : ℕ)
    (v : (blocks A δ h0 hmono) k) :
    v ∈ (blocks A δ h0 hmono).levelSub (sectionSpace A δ h0 hmono) k ↔
      ∃ η : Section E X, IsContSection u η ∧ IsMatchingSection X η ∧
        IsRep η ((blocks A δ h0 hmono).toBase k v) := by
  rw [ScBanach.mem_levelSub, sectionSpace_eq A δ h0 hmono h]; rfl

/-- The smooth sections are dense in every level (Definition 1.1.6 of the book). -/
def SectionsDense : Prop := (blocks A δ h0 hmono).IsScSubspace (sectionSpace A δ h0 hmono)

/-- `H^{3,δ₀}_c(S, u*TQ)` as an sc-Banach space, given the density of the smooth sections. -/
def sectionSc (h : SectionsDense A δ h0 hmono) : ScBanach := (blocks A δ h0 hmono).ofSubspace h

/-! ## 3. The linear constraints and `E_u` (Memoir p. 68) -/

variable (X) in
/-- Linear constraints at the stabilizing points `z ∈ Σ`: linear subspaces `H_{u(z)}` of
`T_{u(z)}Q = E` (in good data, `H_{u(z)} = T_{u(z)}M_{u(z)}`, Definition 3.6 (4)). -/
structure LinearConstraints (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  ns : ℕ
  pt : Fin ns → X.S
  H : Fin ns → Submodule ℝ E

variable (C : LinearConstraints X E)

/-- The representatives of the sections satisfying the linear constraints. -/
def constraintsSub : Submodule ℝ ((blocks A δ h0 hmono) 0) where
  carrier := {v | ∃ η : Section E X, IsContSection u η ∧ IsMatchingSection X η ∧ IsRep η v ∧
    ∀ l, (η (C.pt l) : E) ∈ C.H l}
  zero_mem' := ⟨(0 : Section E X), isContSection_zero (u := u), fun _ _ _ => rfl, isRep_zero,
    fun l => (C.H l).zero_mem⟩
  add_mem' := by
    rintro v v' ⟨η, hc, hm, hr, hH⟩ ⟨η', hc', hm', hr', hH'⟩
    refine ⟨η + η', hc.add hc', fun x y hxy => ?_, hr.add hr', fun l => (C.H l).add_mem (hH l)
      (hH' l)⟩
    change (η x : E) + η' x = η y + η' y
    rw [hm x y hxy, hm' x y hxy]
  smul_mem' := by
    rintro c v ⟨η, hc, hm, hr, hH⟩
    refine ⟨c • η, hc.smul c, fun x y hxy => ?_, hr.smul c, fun l => (C.H l).smul_mem c (hH l)⟩
    change c • (η x : E) = c • η y
    rw [hm x y hxy]

/-- **`E_u = {η ∈ H^{3,δ₀}_c(u*TQ) | η(z) ∈ H_{u(z)} for z ∈ Σ}`** (Memoir p. 68). -/
def uSpace : Submodule ℝ ((blocks A δ h0 hmono) 0) :=
  (constraintsSub A δ h0 hmono C).topologicalClosure

/-- The point evaluations at `Σ` are continuous on the sections of class `(3, δ₀)`. -/
def ConstraintsClosed : Prop :=
  IsClosed (constraintsSub A δ h0 hmono C : Set ((blocks A δ h0 hmono) 0))

theorem uSpace_eq (h : ConstraintsClosed A δ h0 hmono C) :
    uSpace A δ h0 hmono C = constraintsSub A δ h0 hmono C :=
  IsClosed.submodule_topologicalClosure_eq h

theorem constraintsSub_le : constraintsSub A δ h0 hmono C ≤ sectionsSub A δ h0 hmono :=
  fun _ ⟨η, hc, hm, hr, _⟩ => ⟨η, hc, hm, hr⟩

/-- `E_u ⊆ H^{3,δ₀}_c(S, u*TQ)`. -/
theorem uSpace_le : uSpace A δ h0 hmono C ≤ sectionSpace A δ h0 hmono :=
  Submodule.topologicalClosure_mono (constraintsSub_le A δ h0 hmono C)

/-- Without constraints (`H_{u(z)} = T_{u(z)}Q`), `E_u` is the whole section space. -/
theorem uSpace_top (hC : ∀ l, C.H l = ⊤) : uSpace A δ h0 hmono C = sectionSpace A δ h0 hmono := by
  have : constraintsSub A δ h0 hmono C = sectionsSub A δ h0 hmono := by
    refine le_antisymm (constraintsSub_le A δ h0 hmono C) fun v ⟨η, hc, hm, hr⟩ =>
      ⟨η, hc, hm, hr, fun l => by rw [hC l]; trivial⟩
  rw [uSpace, this]; rfl

/-- The `E_u`-scale, levels `E_u ∩ (blocks)_m`. -/
def uScale : ScScale :=
  (blocks A δ h0 hmono).ofSubspaceScale (Submodule.isClosed_topologicalClosure
    (constraintsSub A δ h0 hmono C))

end Atlas

/-! ## 4. Witnesses -/

section Witness

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} (X : NodalSurface m)

lemma norm_sq_single_add_single (a b : ℝ) :
    ‖EuclideanSpace.single (0 : Fin 2) a + EuclideanSpace.single 1 b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp

lemma single_add_single_eq (w : E2) :
    EuclideanSpace.single (0 : Fin 2) (w 0) + EuclideanSpace.single 1 (w 1) = w := by
  ext i; fin_cases i <;> simp

/-- **Witness**: a noded Riemann surface without nodes has an atlas of disc charts, for every
continuous `u` (compactness of `S`). -/
theorem exists_sectionAtlas (u : X.S → Q) (hu : Continuous u) (hX : X.nodes = ∅) :
    Nonempty (SectionAtlas (E := E) X u) := by
  have hW : ∀ z : X.S, ∃ ε > 0, ∀ w ∈ Metric.ball (extChartAt 𝓘(ℝ, E2) z z) ε,
      w ∈ (extChartAt 𝓘(ℝ, E2) z).target ∧
        u ((extChartAt 𝓘(ℝ, E2) z).symm w) ∈ (extChartAt 𝓘(ℝ, E) (u z)).source := by
    intro z
    have h1 : (extChartAt 𝓘(ℝ, E2) z).target ∈ 𝓝 (extChartAt 𝓘(ℝ, E2) z z) :=
      extChartAt_target_mem_nhds z
    have h2 : (fun w => u ((extChartAt 𝓘(ℝ, E2) z).symm w)) ⁻¹' (extChartAt 𝓘(ℝ, E) (u z)).source
        ∈ 𝓝 (extChartAt 𝓘(ℝ, E2) z z) := by
      have hc : ContinuousAt (fun w => u ((extChartAt 𝓘(ℝ, E2) z).symm w))
          (extChartAt 𝓘(ℝ, E2) z z) :=
        hu.continuousAt.comp (continuousAt_extChartAt_symm z)
      refine hc.preimage_mem_nhds ?_
      rw [extChartAt_to_inv]
      exact extChartAt_source_mem_nhds (u z)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem h1 h2)
    exact ⟨ε, hε, fun w hw => hball hw⟩
  choose ε hε hball using hW
  set U : X.S → Set X.S := fun z => (extChartAt 𝓘(ℝ, E2) z).source ∩
    (extChartAt 𝓘(ℝ, E2) z) ⁻¹' Metric.ball (extChartAt 𝓘(ℝ, E2) z z) (ε z / 4) with hU
  have hUo : ∀ z, IsOpen (U z) := fun z =>
    (continuousOn_extChartAt z).isOpen_inter_preimage (isOpen_extChartAt_source z)
      Metric.isOpen_ball
  have hUz : ∀ z, z ∈ U z := fun z =>
    ⟨mem_extChartAt_source z, Metric.mem_ball_self (by linarith [hε z])⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun y _ => mem_iUnion.2 ⟨y, hUz y⟩)
  have hplace : ∀ z (p : ℝ × ℝ), p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 < 1 / 8 →
      X.place z (ε z) p ∈ Metric.ball (extChartAt 𝓘(ℝ, E2) z z) (ε z) := by
    intro z p hp
    rw [Metric.mem_ball, NodalSurface.place, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (hε z).le]
    have hn :
        ‖EuclideanSpace.single (0 : Fin 2) p.1 + EuclideanSpace.single 1 (p.2 - 1 / 2)‖ < 1 := by
      have := norm_sq_single_add_single p.1 (p.2 - 1 / 2)
      nlinarith [norm_nonneg (EuclideanSpace.single (0 : Fin 2) p.1 +
        EuclideanSpace.single 1 (p.2 - 1 / 2))]
    have := hε z
    nlinarith
  refine ⟨{
    nd := t.card
    center := fun i => (t.equivFin.symm i).1
    ε := fun i => ε (t.equivFin.symm i).1
    ε_pos := fun i => hε _
    disc_chart := fun i p hp => hball _ _ (hplace _ p hp)
    disc_avoid := fun i p _ q hq => by rw [hX] at hq; exact absurd hq (notMem_empty q)
    nn := 0
    node := Fin.elim0
    hol := Fin.elim0
    s0 := Fin.elim0
    isHol := fun j => j.elim0
    neck_chart := fun j => j.elim0
    node_nodal := fun j => j.elim0
    nodal_node := fun q hq => by rw [hX] at hq; exact absurd hq (notMem_empty q)
    cover := fun y => Or.inl ?_ }⟩
  obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  obtain ⟨hys, hyb⟩ := hyz
  refine ⟨t.equivFin ⟨z, hzt⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  set w : E2 := (ε z)⁻¹ • (extChartAt 𝓘(ℝ, E2) z y - extChartAt 𝓘(ℝ, E2) z z) with hw
  have hεz := hε z
  have hwn : ‖w‖ < 1 / 4 := by
    rw [hw, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hεz.le), ← dist_eq_norm]
    rw [mem_preimage, Metric.mem_ball] at hyb
    rw [inv_mul_lt_iff₀ hεz]; linarith
  refine ⟨(w 0, w 1 + 1 / 2), ?_, ?_⟩
  · have h := norm_sq_single_add_single (w 0) (w 1)
    rw [single_add_single_eq] at h
    simp only [add_sub_cancel_right]
    nlinarith [norm_nonneg w]
  · have hpl : X.place z (ε z) (w 0, w 1 + 1 / 2) = extChartAt 𝓘(ℝ, E2) z y := by
      rw [NodalSurface.place]
      simp only [add_sub_cancel_right]
      rw [single_add_single_eq, hw, smul_smul, mul_inv_cancel₀ hεz.ne', one_smul,
        add_sub_cancel]
    rw [NodalSurface.discPt, hpl, (extChartAt 𝓘(ℝ, E2) z).left_inv hys]

variable {X}

/-- The level-`0` blocks of the constant section `e` along a constant map: `β · e_k*(e)` on the
discs (the test function `bumpPer`), and `(e_k*(e), 0)` at the nodal points. -/
def constBlocks {q : Q} (A : SectionAtlas (E := E) X (fun _ => q)) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0)
    (hmono : StrictMono δ) (e : E) : (blocks A δ h0 hmono) 0 :=
  (fun ik => toH (3 + 0) (Neck.δ_nonneg δ h0 hmono 0) (isTest_bumpPer (crd ik.2 e)),
    fun jk => (crd jk.2 e, 0))

/-- **Witness**: for a constant map `u ≡ q`, the constant sections `η ≡ e` are continuous, have
matching values, and their local representatives lie in the blocks, so they belong to
`H^{3,δ₀}_c(S, u*TQ)`. -/
theorem constBlocks_mem {q : Q} (A : SectionAtlas (E := E) X (fun _ => q)) (δ : ℕ → ℝ)
    (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (e : E) :
    constBlocks A δ h0 hmono e ∈ sectionsSub A δ h0 hmono := by
  have hT : ∀ v : E, tangentCoordChange 𝓘(ℝ, E) q q q v = v := fun v =>
    tangentCoordChange_self (mem_extChartAt_source q)
  refine ⟨fun _ => e, fun x => ?_, fun _ _ _ => rfl, fun i k => ?_, fun j k => ⟨rfl, ?_⟩⟩
  · simp only [hT]; exact continuousAt_const
  · have h1 : (H.val (discBlock (constBlocks A δ h0 hmono e) i k) : ℝ × ℝ → ℝ) =ᵐ[cyl]
        bumpPer (crd k e) := MemLp.coeFn_toLp ((isTest_bumpPer _).memLp 2)
    filter_upwards [h1, bumpPer_ae_eq (crd k e)] with p hp1 hp2
    rw [hp1, hp2, discRep, hT]; rfl
  · rw [show (neckBlock (constBlocks A δ h0 hmono e) j k).2 = 0 from rfl]
    filter_upwards [val_zero_ae (k := 3) (hd := Neck.δ_nonneg δ h0 hmono 0)] with p hp
    rw [hp, neckRep, hT, neckConst, sub_self, mul_zero]; rfl

/-- The three-pointed sphere carries an atlas for the constant map at any `q`. -/
theorem sphere3_sectionAtlas (q : Q) : Nonempty (SectionAtlas (E := E) sphere3 (fun _ => q)) :=
  exists_sectionAtlas sphere3 _ continuous_const rfl

end Witness

end GWMemoir
