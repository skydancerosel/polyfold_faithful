import Polyfold.Chapter5.Transversality
import Polyfold.Chapter3.NonVacuity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), §5.3, p. 174 (after
Lemma 5.3.3 (preprint 5.11)): the allowable sections `Γ^{+,1}_U(P)` and the uniform distance `ρ`.

# The metric space `(Γ^{+,1}_U(P), ρ)`, and when it is not complete

## The text, paraphrased

For an auxiliary norm `N` (Definition 5.1.1 (preprint 5.1)) and an open `U ⊆ X`, `Γ^{+,1}_U(P)` is the set of
sc⁺-sections `s` with `supp(s) ⊆ U` and `N(s(x)) ≤ 1` for all `x`.  It "becomes a metric space
with respect to the uniform distance `ρ(s, s') = sup_x N(s(x) − s'(x))`.  The metric space
`(Γ^{+,1}_U(P), ρ)` is not complete."  No proof or example is given (comparison item V5.21, gap
G.42).

## What is formalized

* `StrongBundle.allowableDist B N U s s'` is `ρ(s, s') = sup_x N(s(x) − s'(x))`, the supremum of
  the project's pointwise distance `StrongBundle.sectionDistAt`.  For an auxiliary norm the
  supremum is finite, `ρ ≤ 2` (`allowableDist_le_two`: `N(s(x) − s'(x)) ≤ N(s(x)) + N(s'(x))`),
  and `ρ` is a metric: `allowableDist_self`, `allowableDist_comm`, `allowableDist_triangle`,
  `eq_of_allowableDist_eq_zero` (the last from "`N` is a norm on the fibres", Definition 5.1.1 (preprint 5.1) (1)).
  `StrongBundle.allowableMetric U hN` is the metric space structure on `Γ^{+,1}_U(P)`, and
  `StrongBundle.AllowableSpace U hN` is `Γ^{+,1}_U(P)` as a type carrying it.
* **Not complete, on the trivial bundle `ℝ × ℝ → ℝ`** (`TrivialBundle.bundle 1 1`, the bundle of
  `NonVacuity.lean`), with the fibre norm `N(x, v) = |v|` (`TrivialBundle.fibNorm`; it is an
  auxiliary norm, `TrivialBundle.isAuxNorm_fibNorm`) and `U = ℝ`: the allowable sections
  `s_j(x) = (x, √(x² + 1/(j+1)²) / (2√(1 + x²)))` form a `ρ`-Cauchy sequence whose uniform limit
  `x ↦ (x, |x| / (2√(1 + x²)))` is not differentiable at `0`, while every sc⁺-section of the
  trivial bundle has a differentiable fibre part
  (`TrivialBundle.differentiable_snd_of_isScPlusSection`).
  `TrivialBundle.not_completeSpace_allowableSections`.
* **The statement needs a hypothesis.**  `(Γ^{+,1}_U(P), ρ)` *is* complete when `U = ∅` (it is the
  single point `0`, `StrongBundle.completeSpace_allowableSections_empty`) and when `X` is a point
  and the fibre is finite-dimensional (`TrivialBundle.bundle 0 k`: `Γ^{+,1}_U(P)` is the closed
  unit ball of `ℝᵏ` or `{0}`, `TrivialBundle.completeSpace_allowableSections_point`).

## What the text leaves implicit, and the choices made

* The sup is finite because allowable sections satisfy `N(s(x)) ≤ 1`; it is an `ℝ`-valued `⨆`
  (`0` over an empty `X`).  The metric is a `def`, not an instance: `Γ^{+,1}_U(P) ⊆ (X → Y)`
  carries other structures (the product topology, and on `ℝ × ℝ` a product uniformity).
* "Not complete" is proved for one bundle; a general sufficient condition (e.g. `U` contains a
  non-isolated point over which the fibre is nonzero) is not formalized.  The two complete cases
  show that some hypothesis of this kind is needed.
* The text uses `ρ` only through "dense in `(Γ^{+,1}_U(P), ρ)`" (Theorems 5.3.5, 5.3.10 (preprint 5.13, 5.18)), which the
  project states with the pointwise bound `N(s(x) − s'(x)) ≤ ε` (`sectionDistAt`); that bound is
  `ρ(s, s') ≤ ε` (`allowableDist_le_iff`).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

section Metric

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundle

variable {B : StrongBundle PX P} {N : B.One → ℝ} {U : Set X}

/-- The value `s(x) ∈ (Y_{0,1})_x` of an allowable section. -/
def allowableVal (s : B.allowableSections N U) (x : X) : B.oneFiber x :=
  ⟨⟨(s : X → Y) x, s.2.1.1 x⟩, s.2.1.mem_oneSet x⟩

/-- The pointwise distance of two allowable sections, in the fibre `(Y_{0,1})_x`. -/
lemma sectionDistAt_allowable (s s' : B.allowableSections N U) (x : X) :
    B.sectionDistAt N s.2.1 s'.2.1 x = N (B.toOne (allowableVal s x - allowableVal s' x)) := rfl

/-- `N(s(x)) ≤ 1` for an allowable section. -/
lemma allowableVal_le_one (s : B.allowableSections N U) (x : X) :
    N (B.toOne (allowableVal s x)) ≤ 1 :=
  s.2.2.2 x (s.2.1.mem_oneSet x)

/-- `N(−v) = N(v)` on the fibres (Definition 5.1.1 (preprint 5.1) (1)). -/
lemma IsAuxNorm.neg (hN : B.IsAuxNorm N) {x : X} (v : B.oneFiber x) :
    N (B.toOne (-v)) = N (B.toOne v) := by
  have := (hN.fiber x).smul (-1) v
  rwa [neg_one_smul, abs_neg, abs_one, one_mul] at this

/-- `N(v − w) ≤ N(v) + N(w)` on the fibres. -/
lemma IsAuxNorm.sub_le (hN : B.IsAuxNorm N) {x : X} (v w : B.oneFiber x) :
    N (B.toOne (v - w)) ≤ N (B.toOne v) + N (B.toOne w) := by
  rw [sub_eq_add_neg, ← hN.neg w]; exact (hN.fiber x).add_le v (-w)

/-- `N(v − w) = N(w − v)` on the fibres. -/
lemma IsAuxNorm.sub_comm (hN : B.IsAuxNorm N) {x : X} (v w : B.oneFiber x) :
    N (B.toOne (v - w)) = N (B.toOne (w - v)) := by
  rw [← neg_sub, hN.neg]

/-- The triangle inequality for `N` on the fibres. -/
lemma IsAuxNorm.sub_triangle (hN : B.IsAuxNorm N) {x : X} (v w z : B.oneFiber x) :
    N (B.toOne (v - z)) ≤ N (B.toOne (v - w)) + N (B.toOne (w - z)) := by
  have := (hN.fiber x).add_le (v - w) (w - z)
  rwa [sub_add_sub_cancel] at this

variable (B N U) in
/-- **The uniform distance `ρ(s, s') = sup_x N(s(x) − s'(x))` on `Γ^{+,1}_U(P)`** (§5.3, p. 174;
comparison item V5.21, gap G.42). -/
def allowableDist (s s' : B.allowableSections N U) : ℝ :=
  ⨆ x, B.sectionDistAt N s.2.1 s'.2.1 x

/-- `N(s(x) − s'(x)) ≤ 2` for allowable sections. -/
theorem sectionDistAt_le_two (hN : B.IsAuxNorm N) (s s' : B.allowableSections N U) (x : X) :
    B.sectionDistAt N s.2.1 s'.2.1 x ≤ 2 := by
  rw [sectionDistAt_allowable]
  linarith [hN.sub_le (allowableVal s x) (allowableVal s' x), allowableVal_le_one s x,
    allowableVal_le_one s' x]

/-- The supremum defining `ρ` is finite. -/
theorem bddAbove_sectionDistAt (hN : B.IsAuxNorm N) (s s' : B.allowableSections N U) :
    BddAbove (range fun x => B.sectionDistAt N s.2.1 s'.2.1 x) :=
  ⟨2, by rintro _ ⟨x, rfl⟩; exact sectionDistAt_le_two hN s s' x⟩

/-- `N(s(x) − s'(x)) ≤ ρ(s, s')`. -/
theorem sectionDistAt_le_allowableDist (hN : B.IsAuxNorm N) (s s' : B.allowableSections N U)
    (x : X) : B.sectionDistAt N s.2.1 s'.2.1 x ≤ B.allowableDist N U s s' :=
  le_ciSup (bddAbove_sectionDistAt hN s s') x

/-- **`ρ` is finite**: `ρ(s, s') ≤ 2` on `Γ^{+,1}_U(P)`. -/
theorem allowableDist_le_two (hN : B.IsAuxNorm N) (s s' : B.allowableSections N U) :
    B.allowableDist N U s s' ≤ 2 :=
  Real.iSup_le (fun x => sectionDistAt_le_two hN s s' x) (by norm_num)

/-- `ρ ≥ 0`. -/
theorem allowableDist_nonneg (hN : B.IsAuxNorm N) (s s' : B.allowableSections N U) :
    0 ≤ B.allowableDist N U s s' :=
  Real.iSup_nonneg fun _ => hN.nonneg _

/-- The pointwise form used by the project's density statements: `ρ(s, s') ≤ ε` iff
`N(s(x) − s'(x)) ≤ ε` for all `x` (`ε ≥ 0`). -/
theorem allowableDist_le_iff (hN : B.IsAuxNorm N) (s s' : B.allowableSections N U) {ε : ℝ}
    (hε : 0 ≤ ε) : B.allowableDist N U s s' ≤ ε ↔ ∀ x, B.sectionDistAt N s.2.1 s'.2.1 x ≤ ε :=
  ⟨fun h x => (sectionDistAt_le_allowableDist hN s s' x).trans h, fun h => Real.iSup_le h hε⟩

/-- `ρ(s, s) = 0`. -/
theorem allowableDist_self (hN : B.IsAuxNorm N) (s : B.allowableSections N U) :
    B.allowableDist N U s s = 0 := by
  refine le_antisymm (Real.iSup_le (fun x => ?_) le_rfl) (allowableDist_nonneg hN s s)
  rw [sectionDistAt_allowable, sub_self]
  exact (hN.fiber x).map_zero.le

/-- `ρ` is symmetric. -/
theorem allowableDist_comm (hN : B.IsAuxNorm N) (s s' : B.allowableSections N U) :
    B.allowableDist N U s s' = B.allowableDist N U s' s := by
  unfold allowableDist
  congr 1
  funext x
  rw [sectionDistAt_allowable, sectionDistAt_allowable, hN.sub_comm]

/-- The triangle inequality for `ρ`. -/
theorem allowableDist_triangle (hN : B.IsAuxNorm N) (s s' s'' : B.allowableSections N U) :
    B.allowableDist N U s s'' ≤ B.allowableDist N U s s' + B.allowableDist N U s' s'' := by
  refine Real.iSup_le (fun x => ?_)
    (add_nonneg (allowableDist_nonneg hN s s') (allowableDist_nonneg hN s' s''))
  rw [sectionDistAt_allowable]
  refine (hN.sub_triangle _ (allowableVal s' x) _).trans (add_le_add ?_ ?_)
  · exact sectionDistAt_le_allowableDist hN s s' x
  · exact sectionDistAt_le_allowableDist hN s' s'' x

/-- `ρ(s, s') = 0` implies `s = s'` (`N` vanishes only at `0_x`). -/
theorem eq_of_allowableDist_eq_zero (hN : B.IsAuxNorm N) {s s' : B.allowableSections N U}
    (h : B.allowableDist N U s s' = 0) : s = s' := by
  refine Subtype.ext (funext fun x => ?_)
  have h1 : B.sectionDistAt N s.2.1 s'.2.1 x = 0 :=
    le_antisymm (h ▸ sectionDistAt_le_allowableDist hN s s' x) (hN.nonneg _)
  rw [sectionDistAt_allowable] at h1
  have h2 := sub_eq_zero.1 ((hN.fiber x).eq_zero _ h1)
  exact congrArg (fun v : B.oneFiber x => ((v : P ⁻¹' {x}) : Y)) h2

variable (U) in
/-- **`(Γ^{+,1}_U(P), ρ)` is a metric space** (§5.3, p. 174), for an auxiliary norm `N`
(comparison item V5.21, gap G.42). -/
@[reducible] def allowableMetric (hN : B.IsAuxNorm N) : MetricSpace (B.allowableSections N U) where
  dist := B.allowableDist N U
  dist_self := allowableDist_self hN
  dist_comm := allowableDist_comm hN
  dist_triangle := allowableDist_triangle hN
  eq_of_dist_eq_zero := eq_of_allowableDist_eq_zero hN

set_option linter.unusedVariables false in
variable (U) in
/-- `Γ^{+,1}_U(P)` as a type carrying the metric `ρ` (a type synonym: the set of sections
`X → Y` carries other structures, e.g. the product topology). -/
def AllowableSpace (hN : B.IsAuxNorm N) : Type (max u v) := B.allowableSections N U

instance (hN : B.IsAuxNorm N) : MetricSpace (AllowableSpace U hN) := allowableMetric U hN

/-- An allowable section as a point of the metric space. -/
def AllowableSpace.mk (hN : B.IsAuxNorm N) (s : B.allowableSections N U) : AllowableSpace U hN := s

/-- The allowable section underlying a point of the metric space. -/
def AllowableSpace.sec {hN : B.IsAuxNorm N} (s : AllowableSpace U hN) : B.allowableSections N U := s

@[simp] lemma AllowableSpace.sec_mk (hN : B.IsAuxNorm N) (s : B.allowableSections N U) :
    (AllowableSpace.mk hN s).sec = s := rfl

/-- The distance of `AllowableSpace` is `ρ`. -/
lemma AllowableSpace.dist_eq {hN : B.IsAuxNorm N} (s s' : AllowableSpace U hN) :
    dist s s' = B.allowableDist N U s.sec s'.sec := rfl

/-- With `U = ∅` the only allowable section is the zero section. -/
theorem subsingleton_allowableSections_empty :
    Subsingleton (B.allowableSections N (∅ : Set X)) := by
  refine ⟨fun s s' => Subtype.ext (funext fun x => ?_)⟩
  have hz : ∀ t : B.allowableSections N (∅ : Set X), (t : X → Y) x = fiberZero P x := fun t => by
    by_contra h
    exact (t.2.2.1 (subset_closure (show x ∈ {x | (t : X → Y) x ≠ fiberZero P x} from h))).elim
  rw [hz s, hz s']

/-- **The text's "not complete" needs a hypothesis**: for `U = ∅`, `(Γ^{+,1}_U(P), ρ)` is a single
point, hence complete. -/
theorem completeSpace_allowableSections_empty (hN : B.IsAuxNorm N) :
    CompleteSpace (AllowableSpace (∅ : Set X) hN) := by
  have hsub : Subsingleton (AllowableSpace (∅ : Set X) hN) :=
    subsingleton_allowableSections_empty (B := B) (N := N)
  refine Metric.complete_of_cauchySeq_tendsto fun u _ => ⟨u 0, ?_⟩
  have : u = fun _ => u 0 := funext fun j => Subsingleton.elim _ _
  rw [this]; exact tendsto_const_nhds

end StrongBundle

end Metric

/-! ### The trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ`: its fibre norm and its sc⁺-sections -/

namespace TrivialBundle

variable {n k : ℕ}

/-- `ι : ℝᵏ = F₁ → F₀ = ℝᵏ` is the identity, so `ι⁻¹ = id` on its range. -/
lemma invFun_toBase_one (v : Fin k → ℝ) : invFun ((rnSc k).toBase 1) v = v := by
  have h := leftInverse_invFun ((rnSc k).toBase_injective 1) v
  rwa [ScBanach.const_toBase] at h

/-- `Y_{0,1} = Y` for the trivial bundle (constant structures). -/
lemma oneSet_eq : (bundle n k).oneSet = univ := by
  refine eq_univ_of_forall fun y => ?_
  rintro c ⟨a, rfl⟩ -
  exact (bijective_toBase_const _ 1).2 _

/-- The fibre coordinate is linear: `(v − w)₂ = v₂ − w₂`. -/
lemma snd_sub {x : Fin n → ℝ} (v w : proj n k ⁻¹' {x}) :
    ((v - w : proj n k ⁻¹' {x}) : (Fin n → ℝ) × (Fin k → ℝ)).2 =
      (v : (Fin n → ℝ) × (Fin k → ℝ)).2 - (w : (Fin n → ℝ) × (Fin k → ℝ)).2 :=
  ((fibEquiv x).linearEquiv ℝ).map_sub v w

lemma snd_add {x : Fin n → ℝ} (v w : proj n k ⁻¹' {x}) :
    ((v + w : proj n k ⁻¹' {x}) : (Fin n → ℝ) × (Fin k → ℝ)).2 =
      (v : (Fin n → ℝ) × (Fin k → ℝ)).2 + (w : (Fin n → ℝ) × (Fin k → ℝ)).2 :=
  ((fibEquiv x).linearEquiv ℝ).map_add v w

lemma snd_smul {x : Fin n → ℝ} (t : ℝ) (v : proj n k ⁻¹' {x}) :
    ((t • v : proj n k ⁻¹' {x}) : (Fin n → ℝ) × (Fin k → ℝ)).2 =
      t • (v : (Fin n → ℝ) × (Fin k → ℝ)).2 :=
  ((fibEquiv x).linearEquiv ℝ).map_smul t v

lemma snd_zero (x : Fin n → ℝ) :
    ((0 : proj n k ⁻¹' {x}) : (Fin n → ℝ) × (Fin k → ℝ)).2 = 0 :=
  ((fibEquiv x).linearEquiv ℝ).map_zero

lemma fst_fiber {x : Fin n → ℝ} (v : proj n k ⁻¹' {x}) :
    (v : (Fin n → ℝ) × (Fin k → ℝ)).1 = x := v.2

/-- **The fibre norm** `N(x, v) = |v|` on `Y[1]` of the trivial bundle. -/
def fibNorm : (bundle n k).One → ℝ := fun w => ‖((bundle n k).oneVal w).2‖

/-- **The fibre norm is an auxiliary norm** (Definition 5.1.1 (preprint 5.1)). -/
theorem isAuxNorm_fibNorm : (bundle n k).IsAuxNorm (fibNorm (n := n) (k := k)) where
  continuous := (continuous_norm.comp continuous_snd).comp (bundle n k).continuous_oneVal
  fiber x :=
    { eq_zero := fun v hv => by
        have h0 : ((v : proj n k ⁻¹' {x}) : (Fin n → ℝ) × (Fin k → ℝ)).2 = 0 := norm_eq_zero.1 hv
        refine Subtype.ext ((fibEquiv x).injective ?_)
        change ((v : proj n k ⁻¹' {x}) : (Fin n → ℝ) × (Fin k → ℝ)).2 =
          ((0 : proj n k ⁻¹' {x}) : (Fin n → ℝ) × (Fin k → ℝ)).2
        rw [h0, snd_zero]
      smul := fun t v => by
        change ‖((t • (v : proj n k ⁻¹' {x}) : proj n k ⁻¹' {x}) :
          (Fin n → ℝ) × (Fin k → ℝ)).2‖ = |t| * ‖((v : proj n k ⁻¹' {x}) :
            (Fin n → ℝ) × (Fin k → ℝ)).2‖
        rw [snd_smul, norm_smul, Real.norm_eq_abs]
      add_le := fun v w => by
        change ‖(((v : proj n k ⁻¹' {x}) + (w : proj n k ⁻¹' {x}) : proj n k ⁻¹' {x}) :
          (Fin n → ℝ) × (Fin k → ℝ)).2‖ ≤ ‖((v : proj n k ⁻¹' {x}) :
            (Fin n → ℝ) × (Fin k → ℝ)).2‖ + ‖((w : proj n k ⁻¹' {x}) :
              (Fin n → ℝ) × (Fin k → ℝ)).2‖
        rw [snd_add]; exact norm_add_le _ _
      complete := fun u hu => by
        set a : ℕ → Fin k → ℝ := fun j => ((u j : proj n k ⁻¹' {x}) :
          (Fin n → ℝ) × (Fin k → ℝ)).2 with ha
        have hsub : ∀ i j, fibNorm ((bundle n k).toOne (u i - u j)) = ‖a i - a j‖ := fun i j => by
          change ‖(((u i : proj n k ⁻¹' {x}) - (u j : proj n k ⁻¹' {x}) : proj n k ⁻¹' {x}) :
            (Fin n → ℝ) × (Fin k → ℝ)).2‖ = _
          rw [snd_sub]
        have hc : CauchySeq a := by
          refine Metric.cauchySeq_iff.2 fun ε hε => ?_
          obtain ⟨N₀, hN₀⟩ := hu ε hε
          exact ⟨N₀, fun i hi j hj => by rw [dist_eq_norm, ← hsub]; exact hN₀ i hi j hj⟩
        obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
        let v₀ : proj n k ⁻¹' {x} := ⟨(x, b), rfl⟩
        have hv₀ : v₀ ∈ (bundle n k).oneFiber x := by
          change ((v₀ : proj n k ⁻¹' {x}) : (Fin n → ℝ) × (Fin k → ℝ)) ∈ (bundle n k).oneSet
          rw [oneSet_eq]; exact mem_univ _
        refine ⟨⟨v₀, hv₀⟩, ?_⟩
        have e : ∀ j, fibNorm ((bundle n k).toOne (u j - ⟨v₀, hv₀⟩)) = ‖a j - b‖ := fun j => by
          change ‖(((u j : proj n k ⁻¹' {x}) - v₀ : proj n k ⁻¹' {x}) :
            (Fin n → ℝ) × (Fin k → ℝ)).2‖ = _
          rw [snd_sub]
        simp only [e]
        exact tendsto_iff_norm_sub_tendsto_zero.1 hb }
  tendsto_zeroOne := fun w x hP hN => by
    refine TopologicalSpace.tendsto_nhds_generateFrom_iff.2 ?_
    rintro s ⟨c, ⟨a, rfl⟩, W, hW, rfl⟩ ⟨-, hz⟩
    have hlift : ∀ y : (Fin n → ℝ) × (Fin k → ℝ), (chart (k := k) a).liftOne y = (y.1 - a, y.2) :=
      fun y => Prod.ext rfl (invFun_toBase_one _)
    have hz' : ((x - a, 0) : (Fin n → ℝ) × (Fin k → ℝ)) ∈ W := by
      have := hz
      change (chart (k := k) a).liftOne (fiberZero (proj n k) x) ∈ W at this
      rwa [hlift] at this
    have h1 : Tendsto (fun j => (((bundle n k).oneVal (w j)).1 - a, ((bundle n k).oneVal (w j)).2))
        atTop (𝓝 ((x - a, 0) : (Fin n → ℝ) × (Fin k → ℝ))) := by
      refine (hP.sub_const a).prodMk_nhds ?_
      exact tendsto_zero_iff_norm_tendsto_zero.2 hN
    filter_upwards [h1 (hW.mem_nhds hz')] with j hj
    refine ⟨mem_univ _, ?_⟩
    change (chart (k := k) a).liftOne ((bundle n k).oneVal (w j)) ∈ W
    rw [hlift]; exact hj

/-- The distance of two sc⁺-sections at `x`, for the fibre norm: `|s(x)₂ − s'(x)₂|`. -/
lemma sectionDistAt_fibNorm {s s' : (Fin n → ℝ) → (Fin n → ℝ) × (Fin k → ℝ)}
    (hs : (bundle n k).IsScPlusSection s) (hs' : (bundle n k).IsScPlusSection s') (x : Fin n → ℝ) :
    (bundle n k).sectionDistAt fibNorm hs hs' x = ‖(s x).2 - (s' x).2‖ := by
  change ‖(((⟨s x, hs.1 x⟩ : proj n k ⁻¹' {x}) - ⟨s' x, hs'.1 x⟩ : proj n k ⁻¹' {x}) :
    (Fin n → ℝ) × (Fin k → ℝ)).2‖ = _
  rw [snd_sub]

/-- **The graph of a `C^∞` map is an sc⁺-section** of the trivial bundle. -/
theorem isScPlusSection_graphSection {φ : (Fin n → ℝ) → (Fin k → ℝ)} (hφ : ContDiff ℝ ∞ φ) :
    (bundle n k).IsScPlusSection (graphSection φ) := by
  refine ⟨isSection_graphSection, ?_⟩
  rintro c ⟨a, rfl⟩
  refine ⟨fun x _ => (bijective_toBase_const _ 1).2 _, ?_⟩
  have hbE1 : ∀ m, Bijective (((rnSc n).prod (rnSc k).shift).toBase m) :=
    bijective_toBase_prod (bijective_toBase_const _)
      (bijective_toBase_shift (bijective_toBase_const _))
  have h := isScSmoothRetractMap_of_bijective_toBase (E := rnSc n)
    (E' := (rnSc n).prod (rnSc k).shift)
    (bijective_toBase_const _) hbE1 (rn_relOpen_univ n) (O' := strongShiftOne (chart (k := k) a).K)
    (C' := (chart (k := k) a).φ.model.C ×ˢ univ) (fun z _ => by
      change (_, _) ∈ (chart (k := k) a).R '' ((chart (k := k) a).U ×ˢ univ)
      exact ⟨_, ⟨mem_univ _, mem_univ _⟩, rfl⟩)
    (g := fun z => (z + a - a, φ (z + a)))
    (((contDiff_id.add contDiff_const).sub contDiff_const).prodMk
      (hφ.comp (contDiff_id.add contDiff_const)))
  refine h.congr fun z _ => ?_
  exact Prod.ext rfl (invFun_toBase_one _).symm

/-- **Every sc⁺-section of the trivial bundle has a differentiable fibre part**: in the chart
`Φ = id`, its representative `z ↦ (z, s(z)₂)` is sc-smooth into `ℝⁿ ⊕ (ℝᵏ)¹`, hence `C¹`
(Proposition 1.2.3 (preprint 1.18)). -/
theorem differentiable_snd_of_isScPlusSection {s : (Fin n → ℝ) → (Fin n → ℝ) × (Fin k → ℝ)}
    (hs : (bundle n k).IsScPlusSection s) : Differentiable ℝ fun x => (s x).2 := by
  obtain ⟨-, h⟩ := hs.2 (chart 0) (mem_range_self 0)
  have hR := h.comp_isScSmooth (ScRetraction.id (rn_relOpen_univ n)) (image_id _)
  have h1 := (hR 1).contDiffOn_base (ScRetraction.id (rn_relOpen_univ n)).isScDomain
  have h2 : ContDiff ℝ 1
      (fun z : Fin n → ℝ => StrongBundle.localRepOne (chart (k := k) 0) s z) := by
    rw [← contDiffOn_univ]
    refine (h1.congr fun z _ => ?_)
    change StrongBundle.localRepOne (chart (k := k) 0) s z =
      StrongBundle.localRepOne (chart (k := k) 0) s ((rnSc n).toBase 1 z)
    rw [ScBanach.const_toBase]
  have h3 : (fun x => (s x).2) = fun z => (StrongBundle.localRepOne (chart (k := k) 0) s z).2 := by
    funext z
    change (s z).2 = invFun ((rnSc k).toBase 1) (s (z + 0)).2
    rw [invFun_toBase_one, add_zero]
  rw [h3]
  exact (h2.snd).differentiable one_ne_zero

/-! ### The example: `Γ^{+,1}_ℝ(ℝ × ℝ → ℝ)` is not complete -/

/-- `w(t) = 1 / (2√(1 + t²))`. -/
def wt (t : ℝ) : ℝ := 1 / (2 * √(1 + t ^ 2))

lemma one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

lemma sqrt_one_add_sq_pos (t : ℝ) : 0 < √(1 + t ^ 2) := Real.sqrt_pos.2 (one_add_sq_pos t)

lemma wt_pos (t : ℝ) : 0 < wt t := by unfold wt; have := sqrt_one_add_sq_pos t; positivity

lemma wt_le_half (t : ℝ) : wt t ≤ 1 / 2 := by
  unfold wt
  have h1 : 1 ≤ √(1 + t ^ 2) := Real.one_le_sqrt.2 (by nlinarith)
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

lemma wt_mul_sqrt (t : ℝ) : wt t * √(1 + t ^ 2) = 1 / 2 := by
  unfold wt; have := (sqrt_one_add_sq_pos t).ne'; field_simp

lemma contDiff_wt : ContDiff ℝ ∞ wt := by
  unfold wt
  refine contDiff_const.div (contDiff_const.mul ((contDiff_const.add (contDiff_id.pow 2)).sqrt
    fun t => (one_add_sq_pos t).ne')) fun t => by have := sqrt_one_add_sq_pos t; positivity

/-- `ε_j = 1/(j+1)`. -/
def eps (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

lemma eps_pos (j : ℕ) : 0 < eps j := by unfold eps; positivity

lemma eps_le_one (j : ℕ) : eps j ≤ 1 := by
  unfold eps; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- `|√(t² + ε²) − |t|| ≤ ε`. -/
lemma abs_sqrt_sub_abs_le (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) : abs (√(t ^ 2 + ε ^ 2) - |t|) ≤ ε := by
  have h1 : |t| ≤ √(t ^ 2 + ε ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 : √(t ^ 2 + ε ^ 2) ≤ |t| + ε := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs t, abs_nonneg t]
  rw [abs_of_nonneg (by linarith)]; linarith

/-- The approximating fibre parts `φ_j(x) = √(x² + ε_j²) w(x)`. -/
def approx (j : ℕ) (x : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => √(x 0 ^ 2 + eps j ^ 2) * wt (x 0)

/-- The limit `φ(x) = |x| w(x)`, not differentiable at `0`. -/
def limitFn (x : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => |x 0| * wt (x 0)

lemma contDiff_approx (j : ℕ) : ContDiff ℝ ∞ (approx j) := by
  refine contDiff_pi.2 fun _ => ?_
  have h0 : ContDiff ℝ ∞ fun x : Fin 1 → ℝ => x 0 := contDiff_apply ℝ ℝ 0
  refine ContDiff.mul ((h0.pow 2).add contDiff_const |>.sqrt fun x => ?_) (contDiff_wt.comp h0)
  have := eps_pos j; positivity

lemma abs_approx_le_half (j : ℕ) (x : Fin 1 → ℝ) : |approx j x 0| ≤ 1 / 2 := by
  have h1 : √(x 0 ^ 2 + eps j ^ 2) ≤ √(1 + x 0 ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [eps_le_one j, eps_pos j])
  change |√(x 0 ^ 2 + eps j ^ 2) * wt (x 0)| ≤ 1 / 2
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (wt_pos _).le), ← wt_mul_sqrt (x 0),
    mul_comm (wt (x 0))]
  exact mul_le_mul_of_nonneg_right h1 (wt_pos _).le

lemma abs_approx_sub_limitFn (j : ℕ) (x : Fin 1 → ℝ) :
    |approx j x 0 - limitFn x 0| ≤ eps j / 2 := by
  change |√(x 0 ^ 2 + eps j ^ 2) * wt (x 0) - |x 0| * wt (x 0)| ≤ eps j / 2
  rw [← sub_mul, abs_mul, abs_of_pos (wt_pos _)]
  calc abs (√(x 0 ^ 2 + eps j ^ 2) - |x 0|) * wt (x 0) ≤ eps j * (1 / 2) :=
        mul_le_mul (abs_sqrt_sub_abs_le _ (eps_pos j).le) (wt_le_half _) (wt_pos _).le
          (eps_pos j).le
    _ = eps j / 2 := by ring

/-- The norm on `ℝ¹ = Fin 1 → ℝ` is the absolute value of the coordinate. -/
lemma norm_fin_one (v : Fin 1 → ℝ) : ‖v‖ = |v 0| := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => ?_) ?_
  · rw [Subsingleton.elim i 0, Real.norm_eq_abs]
  · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v 0

/-- The sections `s_j(x) = (x, φ_j(x))` are allowable: sc⁺, and `N(s_j(x)) ≤ 1/2`. -/
lemma graphSection_approx_mem (j : ℕ) :
    graphSection (approx j) ∈ (bundle 1 1).allowableSections fibNorm univ := by
  refine ⟨isScPlusSection_graphSection (contDiff_approx j), subset_univ _, fun x _ => ?_⟩
  change ‖approx j x‖ ≤ 1
  rw [norm_fin_one]; linarith [abs_approx_le_half j x]

/-- `t ↦ |t| w(t)` is not differentiable at `0` (`w(0) = 1/2 ≠ 0`). -/
lemma not_differentiableAt_limit :
    ¬ DifferentiableAt ℝ (fun t : ℝ => |t| * wt t) 0 := by
  intro h
  have hw : DifferentiableAt ℝ wt 0 := (contDiff_wt.differentiable (by simp)) 0
  have h2 : DifferentiableAt ℝ (fun t => |t| * wt t / wt t) 0 := h.div hw (wt_pos 0).ne'
  have h3 : (fun t => |t| * wt t / wt t) = abs := funext fun t => by
    rw [mul_div_assoc, div_self (wt_pos t).ne', mul_one]
  rw [h3] at h2
  exact not_differentiableAt_abs_zero h2

/-- **`(Γ^{+,1}_U(P), ρ)` is not complete** (§5.3, p. 174; comparison item V5.21, gap G.42), for the
trivial bundle `ℝ × ℝ → ℝ`, the fibre norm and `U = ℝ`: the allowable sections
`s_j(x) = (x, √(x² + 1/(j+1)²)/(2√(1 + x²)))` form a `ρ`-Cauchy sequence (`ρ(s_i, s_j) ≤ (ε_i +
ε_j)/2`) with no limit in `Γ^{+,1}_U(P)`: a limit `s` would have fibre part `|x|/(2√(1 + x²))`
(pointwise limits), which is not differentiable at `0`, while `s` is sc⁺. -/
theorem not_completeSpace_allowableSections :
    ¬ CompleteSpace (StrongBundle.AllowableSpace (B := bundle 1 1) univ isAuxNorm_fibNorm) := by
  intro hc
  let S : ℕ → StrongBundle.AllowableSpace (B := bundle 1 1) univ isAuxNorm_fibNorm := fun j =>
    StrongBundle.AllowableSpace.mk _ ⟨graphSection (approx j), graphSection_approx_mem j⟩
  have hdist : ∀ i j, dist (S i) (S j) ≤ (eps i + eps j) / 2 := fun i j => by
    rw [StrongBundle.AllowableSpace.dist_eq]
    refine Real.iSup_le (fun x => ?_) (by have := eps_pos i; have := eps_pos j; positivity)
    rw [sectionDistAt_fibNorm, norm_fin_one]
    change |approx i x 0 - approx j x 0| ≤ _
    calc |approx i x 0 - approx j x 0|
        ≤ |approx i x 0 - limitFn x 0| + |approx j x 0 - limitFn x 0| := by
          rw [abs_sub_comm (approx j x 0)]; exact abs_sub_le _ _ _
      _ ≤ eps i / 2 + eps j / 2 :=
          add_le_add (abs_approx_sub_limitFn i x) (abs_approx_sub_limitFn j x)
      _ = (eps i + eps j) / 2 := by ring
  have heps : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hS : CauchySeq S := by
    refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (heps.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨N₀, fun j hj => ?_⟩
    have h1 := hN₀ j hj
    have h2 := hN₀ N₀ le_rfl
    linarith [hdist j N₀]
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete hS
  have hd : Tendsto (fun j => dist (S j) s) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.1 hs
  set σ : (Fin 1 → ℝ) → (Fin 1 → ℝ) × (Fin 1 → ℝ) := s.sec.1 with hσ
  -- the fibre part of the limit is the limit function
  have hval : ∀ x, (σ x).2 0 = limitFn x 0 := by
    intro x
    have h1 : Tendsto (fun j => approx j x 0) atTop (𝓝 ((σ x).2 0)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
        (fun j => ?_) hd)
      have := StrongBundle.sectionDistAt_le_allowableDist isAuxNorm_fibNorm (S j).sec s.sec x
      rw [sectionDistAt_fibNorm, norm_fin_one] at this
      rw [Real.norm_eq_abs, StrongBundle.AllowableSpace.dist_eq]; exact this
    have h2 : Tendsto (fun j => approx j x 0) atTop (𝓝 (limitFn x 0)) := by
      have h3 : Tendsto (fun j => eps j / 2) atTop (𝓝 0) := by
        simpa using heps.div_const 2
      refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
        (fun j => ?_) h3)
      rw [Real.norm_eq_abs]; exact abs_approx_sub_limitFn j x
    exact tendsto_nhds_unique h1 h2
  have hdiff : Differentiable ℝ fun x => (σ x).2 := differentiable_snd_of_isScPlusSection s.sec.2.1
  have hc1 : Differentiable ℝ fun t : ℝ => (fun _ : Fin 1 => t) :=
    differentiable_pi.2 fun _ => differentiable_id
  have h0 : DifferentiableAt ℝ (fun t : ℝ => (σ (fun _ => t)).2 0) 0 := by
    have := (differentiable_apply (𝕜 := ℝ) (F' := fun _ : Fin 1 => ℝ) 0).comp (hdiff.comp hc1)
    exact this 0
  have h3 : (fun t : ℝ => (σ (fun _ => t)).2 0) = fun t => |t| * wt t := funext fun t => hval _
  rw [h3] at h0
  exact not_differentiableAt_limit h0

/-! ### Over a point, `Γ^{+,1}_U(P)` is complete -/

/-- Over the point `ℝ⁰` every section is the graph of a constant, hence sc⁺. -/
lemma isScPlusSection_of_isSection_point {s : (Fin 0 → ℝ) → (Fin 0 → ℝ) × (Fin k → ℝ)}
    (hs : IsSection (proj 0 k) s) : (bundle 0 k).IsScPlusSection s := by
  have e : s = graphSection fun _ => (s 0).2 := funext fun x => by
    rw [Subsingleton.elim x 0]; exact Prod.ext (hs 0) rfl
  rw [e]; exact isScPlusSection_graphSection contDiff_const

/-- **Over a point with finite-dimensional fibre, `(Γ^{+,1}_U(P), ρ)` is complete**: it is the
closed unit ball of `ℝᵏ` (if `U ∋ 0`).  So the text's "not complete" (§5.3, p. 174) needs a
hypothesis on `X`, `U` and the fibres (comparison item V5.21, gap G.42). -/
theorem completeSpace_allowableSections_point (U : Set (Fin 0 → ℝ)) :
    CompleteSpace (StrongBundle.AllowableSpace (B := bundle 0 k) U isAuxNorm_fibNorm) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  set a : ℕ → Fin k → ℝ := fun j => (((u j).sec : (Fin 0 → ℝ) → (Fin 0 → ℝ) × (Fin k → ℝ)) 0).2
    with ha
  have hdist : ∀ i j, ‖a i - a j‖ ≤ dist (u i) (u j) := fun i j => by
    have := StrongBundle.sectionDistAt_le_allowableDist isAuxNorm_fibNorm (u i).sec (u j).sec 0
    rwa [sectionDistAt_fibNorm] at this
  have hc : CauchySeq a := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N₀, hN₀⟩ := Metric.cauchySeq_iff.1 hu ε hε
    exact ⟨N₀, fun i hi j hj => by
      rw [dist_eq_norm]; exact (hdist i j).trans_lt (hN₀ i hi j hj)⟩
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
  -- the limit section
  let s₀ : (Fin 0 → ℝ) → (Fin 0 → ℝ) × (Fin k → ℝ) := graphSection fun _ => b
  have hs₀ : (bundle 0 k).IsScPlusSection s₀ := isScPlusSection_graphSection contDiff_const
  have hb1 : ‖b‖ ≤ 1 := by
    refine le_of_tendsto hb.norm (Eventually.of_forall fun j => ?_)
    exact (u j).sec.2.2.2 0 ((u j).sec.2.1.mem_oneSet 0)
  -- the support condition: `s₀` vanishes unless some `u j` does not
  have hsupp : sectionSupport (proj 0 k) s₀ ⊆ U := by
    by_cases hb0 : b = 0
    · intro x hx
      have : {x | s₀ x ≠ fiberZero (proj 0 k) x} = ∅ := by
        refine eq_empty_of_forall_notMem fun y hy => hy ?_
        exact Prod.ext (Subsingleton.elim _ _) (by change b = _; rw [hb0]; exact (snd_zero y).symm)
      rw [sectionSupport, this, closure_empty] at hx; exact hx.elim
    · have hev : ∀ᶠ j in atTop, a j ≠ 0 := hb.eventually (isOpen_ne.mem_nhds hb0)
      obtain ⟨j, hj⟩ := hev.exists
      have hj' : (0 : Fin 0 → ℝ) ∈ U := (u j).sec.2.2.1 (subset_closure (show (0 : Fin 0 → ℝ) ∈
        {x | ((u j).sec : (Fin 0 → ℝ) → (Fin 0 → ℝ) × (Fin k → ℝ)) x ≠ fiberZero (proj 0 k) x} from
          fun h => hj (by rw [ha]; simp only; rw [h]; exact snd_zero 0)))
      intro x _; rw [Subsingleton.elim x 0]; exact hj'
  let s : StrongBundle.AllowableSpace (B := bundle 0 k) U isAuxNorm_fibNorm :=
    StrongBundle.AllowableSpace.mk _ ⟨s₀, hs₀, hsupp, fun x _ => hb1⟩
  refine ⟨s, tendsto_iff_dist_tendsto_zero.2 ?_⟩
  have e : ∀ j, dist (u j) s = ‖a j - b‖ := fun j => by
    rw [StrongBundle.AllowableSpace.dist_eq]
    refine le_antisymm (Real.iSup_le (fun x => ?_) (norm_nonneg _)) ?_
    · rw [sectionDistAt_fibNorm, Subsingleton.elim x 0]; rfl
    · have := StrongBundle.sectionDistAt_le_allowableDist isAuxNorm_fibNorm (u j).sec s.sec 0
      rwa [sectionDistAt_fibNorm] at this
  simp only [e]
  exact tendsto_iff_norm_sub_tendsto_zero.1 hb

end TrivialBundle

end Polyfold
