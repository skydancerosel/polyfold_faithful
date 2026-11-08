import Polyfold.Chapter10.Equivalence
import Polyfold.Chapter6.PathCategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.1 "Equivalences": **Remark 10.1.11** (p. 470; 2017: Remark 10.1,
p. 340) and **Example 10.1.15** (p. 474; 2017: Example 10.1, p. 341).  Numbers and pages are
the 2021 text's, the 2017 ones in parentheses.

# Two examples on equivalences

## The text, paraphrased

(Remark 10.1.11, p. 470 (2017: Remark 10.1, p. 340)) In Proposition 10.1.10 (1) (for
equivalences `F, G` with `|F| = |G|`, a local sc-smooth family `α_z : F(z) → G(z)`) the value
`α_x` cannot be prescribed: in the translation groupoid of `ℤ/2` acting on `ℝ²` by `z ↦ -z`,
with `F = id` and `G = -id`, the identity morphism `F(0) → G(0)` does not lie in an sc-smooth
local family.

(Example 10.1.15, p. 474 (2017: Example 10.1, p. 341)) The equivalence hypothesis of Proposition
10.1.14 cannot be dropped: for `X = ℤ/4 ⋉ ℝ` (`1, 3` acting by `x ↦ -x`, `2` trivially),
`Y = ℤ/4 ⋉ ℝ²` (rotations by multiples of `90°`) and `Φ(x) = 0`, `Φ(i, x) = (i, 0)`, one has
`T_x = {(0, x), (2, x)}`, `Y = Y_R`, `[(1, x)] = [(3, x)]` in `X_R`, but `Φ(1, x) = (1, 0)` and
`Φ(3, x) = (3, 0)` are different in `Y_R`; so `Φ` does not pass to the reduced groupoids.

## What is formalized

* `Examples.pointReflectionEpGroupoid` (`ℤ/2 ⋉ ℝ²`, `ℤ/2 = ℤˣ`), `negFunctor` (`G = -id`),
  `isEquivalence_negFunctor` (a further non-identity equivalence), `orbitMap_id_eq_negFunctor`
  (`|id| = |G|`), `remark_10_1_11_family` (`α_z = (-1, z)` is an sc-smooth family
  `F(z) → G(z)`, so Proposition 10.1.10 (1) holds here), and **Remark 10.1.11** as
  `remark_10_1_11` (no family `α` continuous at `0` with `α_0 = 1_0`) and
  `remark_10_1_11_scSmooth` (no sc-smooth one on an open neighbourhood of `0`).
* `Examples.example1015X`, `example1015Y`, `example1015Functor` (`Φ`, an sc-smooth functor),
  `example1015X_reducedπ_one_eq_three`, `example1015Y_reducedπ_one_ne_three`, and
  **Example 10.1.15** as `example_10_1_15` (no map `Φ_R` with `Φ_R[φ] = [Φ(φ)]`).

## What the text leaves implicit, and the choices made

* `ℤ/2` is `ℤˣ = {±1}`, `ℤ/4` is `Multiplicative (ZMod 4)`; the actions are `MulAction.compHom`
  along `i ↦ (-1)^i` (`z4SignHom`) and `i ↦ (quarter turn)^i` (`z4RotHom`), used as local
  instances.  The translation groupoids are the existing `actionEpGroupoid` (Chapter 7).
* Remark 10.1.11 is proved in the stronger form "not even continuous at `0`".  Example 10.1.15 is
  stated without Hausdorff hypotheses: no map of the reduced morphism spaces is compatible with
  `Φ`, whatever the topologies.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace EpGroupoid.Examples

/-- In `ℝⁿ`, `z = -z` only for `z = 0`. -/
theorem rn_eq_zero_of_eq_neg {n : ℕ} {z : Fin n → ℝ} (h : z = -z) : z = 0 := by
  funext i
  have := congrFun h i
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  linarith

/-- No neighbourhood of `0 ∈ ℝⁿ` (`n ≥ 1`) consists of points with `z = -z`. -/
theorem not_eventually_eq_neg {n : ℕ} [NeZero n] :
    ¬ ∀ᶠ z in 𝓝 (0 : Fin n → ℝ), z = -z := by
  intro h
  obtain ⟨z, hz, hz0⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := {(0 : Fin n → ℝ)}ᶜ))).exists
  exact hz0 (rn_eq_zero_of_eq_neg hz)

/-! ### Remark 10.1.11: `ℤ/2 ⋉ ℝ²` with `F = id` and `G = -id` -/

/-- `ℤˣ = {±1}` acts on `ℝⁿ` by the sc-smooth maps `z ↦ ±z`. -/
theorem isScSmoothMap_units_smul_rn (n : ℕ) (k : ℤˣ) :
    (rnPolyfold n).IsScSmoothMap (rnPolyfold n) fun z : Fin n → ℝ => k • z := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp only [one_smul]
    exact MPolyfold.isScSmoothMap_id
  · simp only [Units.neg_smul, one_smul]
    exact (isLocalScDiffeo_rn_neg n).isScSmoothMap

/-- **`ℤ/2 ⋉ ℝ²`** (2021 Remark 10.1.11): `ℤ/2 = ℤˣ` acting on `ℝ²` by `z ↦ -z`; a morphism
`(k, z)` goes from `z` to `k • z`. -/
def pointReflectionEpGroupoid : EpGroupoid (Fin 2 → ℝ) (ℤˣ × (Fin 2 → ℝ)) :=
  actionEpGroupoid (isScSmoothMap_units_smul_rn 2)

/-- **The functor `G = -id`** of `ℤ/2 ⋉ ℝ²`: `z ↦ -z`, `(k, z) ↦ (k, -z)`. -/
def negFunctor : EpFunctor pointReflectionEpGroupoid pointReflectionEpGroupoid where
  obj z := -z
  mor p := (p.1, -p.2)
  src_mor _ := rfl
  tgt_mor p := smul_neg p.1 p.2
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := (isLocalScDiffeo_rn_neg 2).isScSmoothMap
  isScSmoothMap_mor := isScSmoothMap_prod_discrete_iff.2 fun k =>
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete k)
      (isLocalScDiffeo_rn_neg 2).isScSmoothMap

/-- `G = -id` is an equivalence (a second non-identity witness for Definition 10.1.1). -/
theorem isEquivalence_negFunctor : negFunctor.IsEquivalence :=
  negFunctor.lemma_10_1_2
    { faithful := (GroupoidFunctor.faithful_iff _).2 fun _ _ _ _ he => by
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        exact Prod.ext h1 (neg_injective h2)
      full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => by
        have hs' : ψ.2 = -x := hs
        have ht' : ψ.1 • ψ.2 = -x' := ht
        refine ⟨(ψ.1, x), rfl, ?_, Prod.ext rfl hs'.symm⟩
        change ψ.1 • x = x'
        rw [hs', smul_neg] at ht'
        exact neg_injective ht'
      essSurj := (GroupoidFunctor.essSurj_iff _).2 fun y =>
        ⟨-y, pointReflectionEpGroupoid.unit y, (neg_neg y).symm, one_smul _ y⟩ }
    (isLocalScDiffeo_rn_neg 2)

/-- `|F| = |G|` for `F = id` and `G = -id`: `(-1, z) : z → -z`. -/
theorem orbitMap_id_eq_negFunctor :
    (EpFunctor.id pointReflectionEpGroupoid).orbitMap = negFunctor.orbitMap := by
  funext q
  induction q using Quotient.inductionOn with | h z => ?_
  change pointReflectionEpGroupoid.π z = pointReflectionEpGroupoid.π (-z)
  exact pointReflectionEpGroupoid.π_eq_π_iff.2
    ⟨((-1 : ℤˣ), z), rfl, by
      change (-1 : ℤˣ) • z = -z
      rw [Units.neg_smul, one_smul]⟩

/-- **Proposition 10.1.10 (1) holds in the example**: `α_z = (-1, z) : F(z) → G(z)` is an
sc-smooth family. -/
theorem remark_10_1_11_family :
    pointReflectionEpGroupoid.PObj.IsScSmoothMap pointReflectionEpGroupoid.PMor
      (fun z => ((-1 : ℤˣ), z)) ∧
      ∀ z, pointReflectionEpGroupoid.src ((-1 : ℤˣ), z) =
          (EpFunctor.id pointReflectionEpGroupoid).obj z ∧
        pointReflectionEpGroupoid.tgt ((-1 : ℤˣ), z) = negFunctor.obj z :=
  ⟨isScSmoothMap_sheet (-1), fun z => ⟨rfl, by
    change (-1 : ℤˣ) • z = -z
    rw [Units.neg_smul, one_smul]⟩⟩

/-- **2021 Remark 10.1.11, p. 470 (2017: Remark 10.1, p. 340)**: in `ℤ/2 ⋉ ℝ²` with `F = id`,
`G = -id` (`|F| = |G|`), the morphism `1_0 : F(0) → G(0)` does not lie in a local family
`α_z : F(z) → G(z)`, not even a family continuous at `0`. -/
theorem remark_10_1_11 :
    ¬ ∃ α : (Fin 2 → ℝ) → ℤˣ × (Fin 2 → ℝ), ContinuousAt α 0 ∧
      α 0 = pointReflectionEpGroupoid.unit 0 ∧
      ∀ᶠ z in 𝓝 0, pointReflectionEpGroupoid.src (α z) =
          (EpFunctor.id pointReflectionEpGroupoid).obj z ∧
        pointReflectionEpGroupoid.tgt (α z) = negFunctor.obj z := by
  rintro ⟨α, hc, h0, hα⟩
  have h1 : ∀ᶠ z in 𝓝 (0 : Fin 2 → ℝ), (α z).1 = 1 := by
    have := ((continuous_fst.tendsto (α 0)).comp hc).eventually
      ((isOpen_discrete {(α 0).1}).mem_nhds (mem_singleton _))
    filter_upwards [this] with z hz
    have hz' : (α z).1 = (α 0).1 := hz
    rw [hz', h0]
    rfl
  refine not_eventually_eq_neg (n := 2) ?_
  filter_upwards [h1, hα] with z h1 ⟨hs, ht⟩
  have hs' : (α z).2 = z := hs
  have ht' : (α z).1 • (α z).2 = -z := ht
  rwa [h1, hs', one_smul] at ht'

/-- Remark 10.1.11 for sc-smooth local families on an open neighbourhood of `0`. -/
theorem remark_10_1_11_scSmooth :
    ¬ ∃ (U : Set (Fin 2 → ℝ)) (α : (Fin 2 → ℝ) → ℤˣ × (Fin 2 → ℝ)), IsOpen U ∧ 0 ∈ U ∧
      pointReflectionEpGroupoid.PObj.IsScSmoothOn pointReflectionEpGroupoid.PMor α U ∧
      α 0 = pointReflectionEpGroupoid.unit 0 ∧
      ∀ z ∈ U, pointReflectionEpGroupoid.src (α z) =
          (EpFunctor.id pointReflectionEpGroupoid).obj z ∧
        pointReflectionEpGroupoid.tgt (α z) = negFunctor.obj z := by
  rintro ⟨U, α, hU, h0U, hα, h0, hst⟩
  exact remark_10_1_11 ⟨α, hα.continuousOn.continuousAt (hU.mem_nhds h0U), h0,
    Filter.mem_of_superset (hU.mem_nhds h0U) fun z hz => hst z hz⟩

/-! ### Example 10.1.15: `ℤ/4 ⋉ ℝ → ℤ/4 ⋉ ℝ²` does not pass to the reduced groupoids -/

section Example15

local notation "Z₄" => Multiplicative (ZMod 4)

/-- The sign `(-1)^i` of `i ∈ ℤ/4` (the action of `ℤ/4` on `ℝ` in Example 10.1.15). -/
def z4Sign (i : Z₄) : ℤˣ := if (Multiplicative.toAdd i).val % 2 = 0 then 1 else -1

/-- `i ↦ (-1)^i` as a homomorphism `ℤ/4 → ℤˣ`. -/
def z4SignHom : Z₄ →* ℤˣ where
  toFun := z4Sign
  map_one' := by decide
  map_mul' := by decide

/-- The quarter turn `(a, b) ↦ (-b, a)` of `ℝ²`. -/
def quarterTurn (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![-(y 1), y 0]

theorem quarterTurn_quarterTurn (y : Fin 2 → ℝ) : quarterTurn (quarterTurn y) = -y := by
  funext i
  fin_cases i <;> simp [quarterTurn]

theorem isPeriodicPt_quarterTurn (y : Fin 2 → ℝ) : IsPeriodicPt quarterTurn 4 y := by
  change quarterTurn (quarterTurn (quarterTurn (quarterTurn y))) = y
  rw [quarterTurn_quarterTurn, quarterTurn_quarterTurn, neg_neg]

theorem quarterTurn_iterate_zero (n : ℕ) : quarterTurn^[n] 0 = 0 :=
  Function.iterate_fixed (by funext i; fin_cases i <;> simp [quarterTurn]) n

theorem contDiff_quarterTurn_iterate (n : ℕ) : ContDiff ℝ ∞ (quarterTurn^[n]) := by
  have h : ContDiff ℝ ∞ quarterTurn := contDiff_pi.2 fun i => by
    fin_cases i
    · simpa [quarterTurn] using (contDiff_apply ℝ ℝ (1 : Fin 2)).neg
    · simpa [quarterTurn] using contDiff_apply ℝ ℝ (0 : Fin 2)
  induction n with
  | zero => exact contDiff_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact h.comp ih

/-- `i ↦ (quarter turn)^i` as a homomorphism `ℤ/4 → End(ℝ²)` (counter-clockwise rotation). -/
def z4RotHom : Z₄ →* Function.End (Fin 2 → ℝ) where
  toFun i := quarterTurn^[(Multiplicative.toAdd i).val]
  map_one' := rfl
  map_mul' i j := by
    funext y
    change quarterTurn^[(Multiplicative.toAdd i + Multiplicative.toAdd j).val] y =
      quarterTurn^[(Multiplicative.toAdd i).val] (quarterTurn^[(Multiplicative.toAdd j).val] y)
    rw [ZMod.val_add, (isPeriodicPt_quarterTurn y).iterate_mod_apply, Function.iterate_add_apply]

/-- `ℤ/4` acting on `ℝ` by `i • x = (-1)^i x`. -/
@[reducible] def z4LineAction : MulAction Z₄ (Fin 1 → ℝ) := MulAction.compHom _ z4SignHom

/-- `ℤ/4` acting on `ℝ²` by rotations by multiples of `90°`. -/
@[reducible] def z4PlaneAction : MulAction Z₄ (Fin 2 → ℝ) := MulAction.compHom _ z4RotHom

attribute [local instance] z4LineAction z4PlaneAction

theorem z4_smul_line (i : Z₄) (x : Fin 1 → ℝ) : i • x = z4Sign i • x := rfl

theorem z4_smul_plane (i : Z₄) (y : Fin 2 → ℝ) :
    i • y = quarterTurn^[(Multiplicative.toAdd i).val] y := rfl

/-- **`X = ℤ/4 ⋉ ℝ`** of Example 10.1.15 (`1` and `3` act by `x ↦ -x`, `2` trivially). -/
def example1015X : EpGroupoid (Fin 1 → ℝ) (Z₄ × (Fin 1 → ℝ)) :=
  actionEpGroupoid fun i => isScSmoothMap_units_smul_rn 1 (z4Sign i)

/-- **`Y = ℤ/4 ⋉ ℝ²`** of Example 10.1.15 (rotations by multiples of `90°`). -/
def example1015Y : EpGroupoid (Fin 2 → ℝ) (Z₄ × (Fin 2 → ℝ)) :=
  actionEpGroupoid fun i => isScSmoothMap_rn_of_contDiff (σ := fun y => i • y)
    (contDiff_quarterTurn_iterate (Multiplicative.toAdd i).val)

theorem zero_mem_smoothSet_rn : (0 : Fin 2 → ℝ) ∈ (rnPolyfold 2).smoothSet :=
  MPolyfold.maxLevel_eq_top_iff.1 (rnPolyfold_maxLevel 2 0)

/-- **The functor `Φ`** of Example 10.1.15: `Φ(x) = 0`, `Φ(i, x) = (i, 0)`. -/
def example1015Functor : EpFunctor example1015X example1015Y where
  obj _ := 0
  mor p := (p.1, 0)
  src_mor _ := rfl
  tgt_mor _ := quarterTurn_iterate_zero _
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := isScSmoothMap_const_of_mem_smoothSet zero_mem_smoothSet_rn
  isScSmoothMap_mor := isScSmoothMap_prod_discrete_iff.2 fun k =>
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete k)
      (isScSmoothMap_const_of_mem_smoothSet zero_mem_smoothSet_rn)

theorem z4_inv_three_mul_one :
    (Multiplicative.ofAdd 3 : Z₄)⁻¹ * Multiplicative.ofAdd 1 = Multiplicative.ofAdd 2 := by
  decide

/-- `(2, x) ∈ 𝐗^T`: `2` acts trivially on `ℝ`. -/
theorem example1015X_two_mem_nonEffectivePart (x : Fin 1 → ℝ) :
    ((Multiplicative.ofAdd 2 : Z₄), x) ∈ example1015X.nonEffectivePart := by
  rw [example1015X.mem_nonEffectivePart_iff]
  have hO : IsOpen ({(Multiplicative.ofAdd 2 : Z₄)} ×ˢ univ : Set (Z₄ × (Fin 1 → ℝ))) :=
    (isOpen_discrete _).prod isOpen_univ
  filter_upwards [hO.mem_nhds ⟨rfl, mem_univ _⟩] with ψ hψ
  change ψ.2 = ψ.1 • ψ.2
  rw [mem_singleton_iff.1 hψ.1, z4_smul_line, show z4Sign (Multiplicative.ofAdd 2) = 1 by decide,
    one_smul]

/-- `(2, 0) ∉ 𝐘^T`: the half turn is the identity only at `0`. -/
theorem example1015Y_two_not_mem_nonEffectivePart :
    ((Multiplicative.ofAdd 2 : Z₄), (0 : Fin 2 → ℝ)) ∉ example1015Y.nonEffectivePart := by
  intro h
  have h' := ((continuous_const.prodMk continuous_id).tendsto (0 : Fin 2 → ℝ)).eventually
    (example1015Y.mem_nonEffectivePart_iff.1 h)
  refine not_eventually_eq_neg (n := 2) ?_
  filter_upwards [h'] with y hy
  change y = (Multiplicative.ofAdd 2 : Z₄) • y at hy
  rwa [z4_smul_plane, show (Multiplicative.toAdd (Multiplicative.ofAdd 2 : Z₄)).val = 2 from rfl,
    Function.iterate_succ_apply, Function.iterate_one, quarterTurn_quarterTurn] at hy

/-- In `X_R`: `[(1, x)] = [(3, x)]`. -/
theorem example1015X_reducedπ_one_eq_three (x : Fin 1 → ℝ) :
    example1015X.reducedπ ((Multiplicative.ofAdd 1 : Z₄), x) =
      example1015X.reducedπ ((Multiplicative.ofAdd 3 : Z₄), x) := by
  refine example1015X.reducedπ_eq_iff_comp_inv.2 ⟨?_, ?_⟩
  · change (Multiplicative.ofAdd 1 : Z₄) • x = (Multiplicative.ofAdd 3 : Z₄) • x
    rw [z4_smul_line, z4_smul_line, show z4Sign (Multiplicative.ofAdd 1) = -1 by decide,
      show z4Sign (Multiplicative.ofAdd 3) = -1 by decide]
  · change ((Multiplicative.ofAdd 3 : Z₄)⁻¹ * Multiplicative.ofAdd 1, x) ∈ _
    rw [z4_inv_three_mul_one]
    exact example1015X_two_mem_nonEffectivePart x

/-- In `Y_R = Y`: `[(1, 0)] ≠ [(3, 0)]`. -/
theorem example1015Y_reducedπ_one_ne_three :
    example1015Y.reducedπ ((Multiplicative.ofAdd 1 : Z₄), (0 : Fin 2 → ℝ)) ≠
      example1015Y.reducedπ ((Multiplicative.ofAdd 3 : Z₄), (0 : Fin 2 → ℝ)) := by
  intro h
  have h' := (example1015Y.reducedπ_eq_iff_comp_inv.1 h).2
  change ((Multiplicative.ofAdd 3 : Z₄)⁻¹ * Multiplicative.ofAdd 1, (0 : Fin 2 → ℝ)) ∈ _ at h'
  rw [z4_inv_three_mul_one] at h'
  exact example1015Y_two_not_mem_nonEffectivePart h'

/-- **2021 Example 10.1.15, p. 474 (2017: Example 10.1, p. 341)**: the sc-smooth functor
`Φ : ℤ/4 ⋉ ℝ → ℤ/4 ⋉ ℝ²`, `Φ(i, x) = (i, 0)`, does not pass to the reduced morphism spaces: no
map `Φ_R` satisfies `Φ_R [φ] = [Φ(φ)]`.  So the equivalence hypothesis of Proposition 10.1.14
cannot be dropped. -/
theorem example_10_1_15 :
    ¬ ∃ f : example1015X.ReducedMor → example1015Y.ReducedMor,
      ∀ φ, f (example1015X.reducedπ φ) = example1015Y.reducedπ (example1015Functor.mor φ) := by
  rintro ⟨f, hf⟩
  refine example1015Y_reducedπ_one_ne_three ?_
  have h1 := hf ((Multiplicative.ofAdd 1 : Z₄), 0)
  have h3 := hf ((Multiplicative.ofAdd 3 : Z₄), 0)
  rw [example1015X_reducedπ_one_eq_three] at h1
  exact h1.symm.trans h3

end Example15

end EpGroupoid.Examples

end Polyfold
