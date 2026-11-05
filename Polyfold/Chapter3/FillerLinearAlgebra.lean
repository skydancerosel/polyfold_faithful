import Polyfold.Chapter1.FredholmIndex

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
**Proposition 3.5 (Filler)**: the linear algebra of the matrix representation of `Dg(0)`.

# The linear algebra of a filler

## The text, paraphrased

(After Definition 3.4) With the splittings `E = Dr(0)E ⊕ (1 − Dr(0))E` and `F = ρ(0)F ⊕ (1 − ρ(0))F`,
`Dg(0)` has the matrix `[[Tf(0), B], [0, C]]` where `C = (1 − ρ(0))Dg(0)(1 − Dr(0))` restricted to
`(1 − Dr(0))E = ker Dr(0)` is an isomorphism onto `ker ρ(0)` by condition (3) of the filler, so that
`ker Dg(0) = ker Tf(0) ⊕ {0}`.  (Proposition 3.5) (1) `Tf(0) : Dr(0)E → ρ(0)F` is surjective iff
`Dg(0) : E → F` is; (2) `Tf(0)` is Fredholm iff `Dg(0)` is, and `ind Tf(0) = ind Dg(0)`.  Proof of
(2): `Dg(0) = [[1, BC⁻¹], [0, 1]] ∘ [[A, 0], [0, C]]`, the first factor an isomorphism (index `0`),
the indices of a composition add.

## What is formalized

The abstract statement, for Banach spaces `E`, `F` with idempotent bounded operators `p`, `q`, a
bounded `L : E → F` with `(1 − q)Lp = 0` and `(1 − q)L : ker p → ker q` a topological isomorphism
`Φ`; `A = L|_{range p} : range p → range q` is `Polyfold.fillerRestrict`.
* `Polyfold.fillerRestrict_surjective_iff` (**Proposition 3.5 (1)**).
* `Polyfold.fillerRestrict_kerEquiv` (`ker A ≃ ker L`: the text's `ker Dg(0) = ker Tf(0) ⊕ {0}`),
  `Polyfold.fillerRestrict_cokerEquiv` (`range q / range A ≃ F / range L`).
* `Polyfold.fillerRestrict_isFredholm_iff` and `Polyfold.fredholmIndex_fillerRestrict`
  (**Proposition 3.5 (2)**), `Polyfold.proposition_3_5` (the three statements together).

## What the text leaves implicit, and the choices made

* The text's proof of (2) goes through the composition formula and the additivity of the index.
  The Lean proof instead exhibits the isomorphisms `ker A ≃ ker L` and `coker A ≃ coker L`
  directly (both are the statement `(1 − q)Lw = 0 ⟹ w ∈ range p`, i.e. the injectivity of `C`,
  and the solvability of `(1 − q)Lz = (1 − q)y`, the surjectivity of `C`), which gives the index
  equality for the index `dim ker − dim coker` without any finiteness assumption, and the
  Fredholm property (finite kernel, closed range, finite cokernel; `isFredholm_of_banach`) in
  both directions.  Closedness of the range transfers through `range A = range L ∩ range q` and
  `range L = M⁻¹(range A)` for the continuous `M(y) = y − L C⁻¹(1 − q)y`; this uses the continuity
  of `C⁻¹`, i.e. that `C` is a *topological* isomorphism as the text requires in (3).
* `Tf(0)` is "the restriction of `D(f ∘ r)(0)` to `T₀O`"; with `D(f ∘ r)(0) = Dg(0)Dr(0)` and
  `(1 − ρ(0))Dg(0)Dr(0) = 0` it is `Dg(0)|_{range Dr(0)}` with values in `range ρ(0)`, which is
  `fillerRestrict` (the derivative identities are in `FillerLinearization.lean`).
-/

open Set Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

section FillerLinearAlgebra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (p : E →L[ℝ] E) (q : F →L[ℝ] F) (L : E →L[ℝ] F)

/-- The range of a bounded operator `M → M`, as a submodule (abbreviation). -/
abbrev rangeS {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] (f : M →L[ℝ] M) :
    Submodule ℝ M := LinearMap.range (f : M →ₗ[ℝ] M)

/-- `A = L|_{range p} : range p → range q`, the text's `Tf(0) : Dr(0)E → ρ(0)F` (well defined by
`(1 − q)Lp = 0`). -/
def fillerRestrict (h1 : ∀ x, q (L (p x)) = L (p x)) :
    ↥(rangeS p) →L[ℝ] ↥(rangeS q) :=
  (L.comp (LinearMap.range (p : E →ₗ[ℝ] E)).subtypeL).codRestrict _ fun x => by
    obtain ⟨x, y, rfl⟩ := x
    exact ⟨L (p y), h1 y⟩

@[simp] lemma fillerRestrict_apply (h1 : ∀ x, q (L (p x)) = L (p x))
    (x : ↥(rangeS p)) : (fillerRestrict p q L h1 x : F) = L x := rfl

/-- `A` as a linear map. -/
def fillerRestrictₗ (h1 : ∀ x, q (L (p x)) = L (p x)) :
    ↥(rangeS p) →ₗ[ℝ] ↥(rangeS q) :=
  (fillerRestrict p q L h1).toLinearMap

@[simp] lemma fillerRestrictₗ_apply (h1 : ∀ x, q (L (p x)) = L (p x))
    (x : ↥(rangeS p)) : (fillerRestrictₗ p q L h1 x : F) = L x := rfl

lemma ker_fillerRestrict (h1 : ∀ x, q (L (p x)) = L (p x)) :
    LinearMap.ker (fillerRestrict p q L h1 : ↥(rangeS p) →ₗ[ℝ] ↥(rangeS q)) =
      LinearMap.ker (fillerRestrictₗ p q L h1) := rfl

lemma range_fillerRestrict (h1 : ∀ x, q (L (p x)) = L (p x)) :
    LinearMap.range (fillerRestrict p q L h1 : ↥(rangeS p) →ₗ[ℝ] ↥(rangeS q)) =
      LinearMap.range (fillerRestrictₗ p q L h1) := rfl

/-- The range of an idempotent bounded operator is closed (`range p = {x | p x = x}`). -/
lemma isClosed_range_of_idem {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : M →L[ℝ] M) (hf : ∀ x, f (f x) = f x) : IsClosed (LinearMap.range (f : M →ₗ[ℝ] M) : Set M) := by
  have : (LinearMap.range (f : M →ₗ[ℝ] M) : Set M) = {x | f x = x} := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => by rw [← hy]; exact hf y, fun h => ⟨x, h⟩⟩
  rw [this]
  exact isClosed_eq f.continuous continuous_id

variable {p q L}
variable (hp : ∀ x, p (p x) = p x) (hq : ∀ y, q (q y) = q y) (h1 : ∀ x, q (L (p x)) = L (p x))
  (Φ : ↥(LinearMap.ker (p : E →ₗ[ℝ] E)) ≃L[ℝ] ↥(LinearMap.ker (q : F →ₗ[ℝ] F)))
  (hΦ : ∀ v : ↥(LinearMap.ker (p : E →ₗ[ℝ] E)), ((Φ v : ↥(LinearMap.ker (q : F →ₗ[ℝ] F))) : F) =
    L v - q (L v))

include hp h1 hΦ in
/-- Injectivity of `C`: `(1 − q)Lw = 0` forces `w ∈ range p`. -/
lemma fillerRestrict_mem_range_of (w : E) (hw : L w - q (L w) = 0) : p w = w := by
  have hv : w - p w ∈ LinearMap.ker (p : E →ₗ[ℝ] E) := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hp, sub_self]
  have h2 : ((Φ ⟨w - p w, hv⟩ : ↥(LinearMap.ker (q : F →ₗ[ℝ] F))) : F) = 0 := by
    rw [hΦ]
    change L (w - p w) - q (L (w - p w)) = 0
    rw [map_sub, map_sub, h1]
    have : L w - L (p w) - (q (L w) - L (p w)) = L w - q (L w) := by abel
    rw [this, hw]
  have h3 : Φ ⟨w - p w, hv⟩ = 0 := Subtype.ext h2
  have h4 : (⟨w - p w, hv⟩ : ↥(LinearMap.ker (p : E →ₗ[ℝ] E))) = 0 := by
    rw [← Φ.map_eq_zero_iff]; exact h3
  have h5 : w - p w = 0 := congrArg Subtype.val h4
  exact (sub_eq_zero.1 h5).symm

include hΦ in
/-- Surjectivity of `C`: `(1 − q)Lz = y` is solvable in `ker p` for `y ∈ ker q`. -/
lemma fillerRestrict_exists_of (y : F) (hy : q y = 0) : ∃ z, p z = 0 ∧ L z - q (L z) = y := by
  have hyk : y ∈ LinearMap.ker (q : F →ₗ[ℝ] F) := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]; exact hy
  refine ⟨Φ.symm ⟨y, hyk⟩, (Φ.symm ⟨y, hyk⟩).2, ?_⟩
  rw [← hΦ, Φ.apply_symm_apply]

include hq in
lemma fillerRestrict_q_sub (y : F) : q (y - q y) = 0 := by rw [map_sub, hq, sub_self]

include hp hq h1 hΦ in
/-- **Proposition 3.5 (1)**: `A : range p → range q` is surjective iff `L : E → F` is. -/
theorem fillerRestrict_surjective_iff :
    Surjective (fillerRestrict p q L h1) ↔ Surjective L := by
  constructor
  · intro hA y
    obtain ⟨z, hz, hLz⟩ := fillerRestrict_exists_of Φ hΦ (y - q y) (fillerRestrict_q_sub hq y)
    have hmem : y - L z ∈ LinearMap.range (q : F →ₗ[ℝ] F) := by
      refine ⟨y - L z, ?_⟩
      rw [ContinuousLinearMap.coe_coe, map_sub]
      have : y - L z = (y - q y) - (L z - q (L z)) + (q y - q (L z)) := by abel
      rw [this, hLz, sub_self, zero_add]
    obtain ⟨x, hx⟩ := hA ⟨y - L z, hmem⟩
    refine ⟨x + z, ?_⟩
    have hx' : L x = y - L z := congrArg Subtype.val hx
    rw [map_add, hx', sub_add_cancel]
  · intro hL y
    obtain ⟨w, hw⟩ := hL y
    have hqy : q (y : F) = y := by
      obtain ⟨y, y', rfl⟩ := y
      exact hq y'
    have hpw : p w = w :=
      fillerRestrict_mem_range_of hp h1 Φ hΦ w (by rw [hw, hqy, sub_self])
    exact ⟨⟨w, w, hpw⟩, Subtype.ext (by rw [fillerRestrict_apply]; exact hw)⟩

/-- The inclusion `ker A → ker L`. -/
def fillerRestrict_kerMap (h1 : ∀ x, q (L (p x)) = L (p x)) :
    ↥(LinearMap.ker (fillerRestrictₗ p q L h1)) →ₗ[ℝ] ↥(LinearMap.ker (L : E →ₗ[ℝ] F)) where
  toFun x := ⟨((x : ↥(rangeS p)) : E), by
    have hx := x.2
    rw [LinearMap.mem_ker] at hx
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    exact congrArg Subtype.val hx⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma fillerRestrict_kerMap_injective (h1 : ∀ x, q (L (p x)) = L (p x)) :
    Injective (fillerRestrict_kerMap h1) := fun x y hxy => by
  have h := Subtype.ext_iff.1 hxy
  exact Subtype.ext (Subtype.ext h)

include hp hΦ in
lemma fillerRestrict_kerMap_surjective :
    Surjective (fillerRestrict_kerMap h1) := fun w => by
  have hw : L w = 0 := w.2
  have hpw : p w = w :=
    fillerRestrict_mem_range_of hp h1 Φ hΦ w (by rw [hw, map_zero, sub_self])
  refine ⟨⟨⟨w, LinearMap.mem_range.2 ⟨w, hpw⟩⟩, ?_⟩, rfl⟩
  rw [LinearMap.mem_ker]
  exact Subtype.ext (by rw [fillerRestrictₗ_apply]; exact hw)

include hp h1 hΦ in
/-- `ker A ≃ ker L` (the text's `ker Dg(0) = ker Tf(0) ⊕ {0}`). -/
def fillerRestrict_kerEquiv :
    ↥(LinearMap.ker (fillerRestrictₗ p q L h1)) ≃ₗ[ℝ] ↥(LinearMap.ker (L : E →ₗ[ℝ] F)) :=
  LinearEquiv.ofBijective (fillerRestrict_kerMap h1)
    ⟨fillerRestrict_kerMap_injective h1, fillerRestrict_kerMap_surjective hp h1 Φ hΦ⟩

include hp hq h1 hΦ in
/-- `range A = {y ∈ range q | y ∈ range L}`. -/
lemma fillerRestrict_mem_range_iff (y : ↥(rangeS q)) :
    y ∈ LinearMap.range (fillerRestrictₗ p q L h1) ↔ (y : F) ∈ LinearMap.range (L : E →ₗ[ℝ] F) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨w, hw⟩
    have hqy : q (y : F) = y := by
      obtain ⟨y, y', rfl⟩ := y
      exact hq y'
    rw [ContinuousLinearMap.coe_coe] at hw
    have hpw : p w = w :=
      fillerRestrict_mem_range_of hp h1 Φ hΦ w (by rw [hw, hqy, sub_self])
    exact ⟨⟨w, LinearMap.mem_range.2 ⟨w, hpw⟩⟩,
      Subtype.ext (by rw [fillerRestrictₗ_apply]; exact hw)⟩

include hp hq h1 hΦ in
/-- `coker A = range q / range A ≃ F / range L = coker L`. -/
def fillerRestrict_cokerEquiv :
    (↥(rangeS q) ⧸ LinearMap.range (fillerRestrictₗ p q L h1)) ≃ₗ[ℝ]
      (F ⧸ LinearMap.range (L : E →ₗ[ℝ] F)) := by
  set Θ : ↥(rangeS q) →ₗ[ℝ] F ⧸ LinearMap.range (L : E →ₗ[ℝ] F) :=
    (LinearMap.range (L : E →ₗ[ℝ] F)).mkQ.comp (LinearMap.range (q : F →ₗ[ℝ] F)).subtype with hΘ
  have hsurj : Surjective Θ := by
    intro c
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ c
    obtain ⟨z, hz, hLz⟩ := fillerRestrict_exists_of Φ hΦ (y - q y) (fillerRestrict_q_sub hq y)
    have hmem : y - L z ∈ LinearMap.range (q : F →ₗ[ℝ] F) := by
      refine ⟨y - L z, ?_⟩
      rw [ContinuousLinearMap.coe_coe, map_sub]
      have : y - L z = (y - q y) - (L z - q (L z)) + (q y - q (L z)) := by abel
      rw [this, hLz, sub_self, zero_add]
    refine ⟨⟨y - L z, hmem⟩, ?_⟩
    change Submodule.mkQ _ (y - L z) = Submodule.mkQ _ y
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨-z, ?_⟩
    rw [ContinuousLinearMap.coe_coe, map_neg]; abel
  have hker : LinearMap.ker Θ = LinearMap.range (fillerRestrictₗ p q L h1) := by
    ext y
    rw [LinearMap.mem_ker, fillerRestrict_mem_range_iff hp hq h1 Φ hΦ]
    change Submodule.mkQ _ (y : F) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective Θ hsurj)

include hp hq h1 hΦ in
/-- **Proposition 3.5 (2), the index**: `ind A = ind L` (as `dim ker − dim coker`, with no
finiteness assumption). -/
theorem fredholmIndex_fillerRestrict :
    fredholmIndex (fillerRestrict p q L h1) = fredholmIndex L := by
  unfold fredholmIndex linIndex
  rw [ker_fillerRestrict, range_fillerRestrict, (fillerRestrict_kerEquiv hp h1 Φ hΦ).finrank_eq,
    (fillerRestrict_cokerEquiv hp hq h1 Φ hΦ).finrank_eq]

include hp hq h1 hΦ in
/-- The range of `A` is closed in `range q` when the range of `L` is closed. -/
lemma fillerRestrict_isClosed_range_of (hL : IsClosed (LinearMap.range (L : E →ₗ[ℝ] F) : Set F)) :
    IsClosed (LinearMap.range (fillerRestrictₗ p q L h1) :
      Set ↥(rangeS q)) := by
  have : (LinearMap.range (fillerRestrictₗ p q L h1) :
      Set ↥(rangeS q)) =
      Subtype.val ⁻¹' (LinearMap.range (L : E →ₗ[ℝ] F) : Set F) := by
    ext y
    exact fillerRestrict_mem_range_iff hp hq h1 Φ hΦ y
  rw [this]
  exact hL.preimage continuous_subtype_val

include hp hq h1 hΦ in
/-- The range of `L` is closed when the range of `A` is closed in `range q`: `range L` is the
preimage of `range A` under the continuous map `y ↦ y − L C⁻¹(1 − q)y`. -/
lemma isClosed_range_of_fillerRestrict
    (hA : IsClosed (LinearMap.range (fillerRestrictₗ p q L h1) :
      Set ↥(rangeS q))) :
    IsClosed (LinearMap.range (L : E →ₗ[ℝ] F) : Set F) := by
  -- `z(y) = C⁻¹((1 − q)y)`
  set zmap : F → E := fun y => (Φ.symm ⟨y - q y, by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]; exact fillerRestrict_q_sub hq y⟩ : E)
    with hzmap
  have hzcont : Continuous zmap := by
    refine continuous_subtype_val.comp (Φ.symm.continuous.comp ?_)
    exact (continuous_id.sub q.continuous).subtype_mk _
  have hzprop : ∀ y, p (zmap y) = 0 ∧ L (zmap y) - q (L (zmap y)) = y - q y := fun y => by
    refine ⟨(Φ.symm ⟨y - q y, _⟩).2, ?_⟩
    rw [hzmap]
    simp only
    rw [← hΦ, Φ.apply_symm_apply]
  -- `M(y) = y − L z(y) ∈ range q`
  have hMmem : ∀ y, y - L (zmap y) ∈ LinearMap.range (q : F →ₗ[ℝ] F) := fun y => by
    refine ⟨y - L (zmap y), ?_⟩
    rw [ContinuousLinearMap.coe_coe, map_sub]
    have : y - L (zmap y) = (y - q y) - (L (zmap y) - q (L (zmap y))) + (q y - q (L (zmap y))) := by
      abel
    rw [this, (hzprop y).2, sub_self, zero_add]
  set M : F → ↥(rangeS q) := fun y => ⟨y - L (zmap y), hMmem y⟩ with hM
  have hMcont : Continuous M :=
    (continuous_id.sub (L.continuous.comp hzcont)).subtype_mk _
  have hpre : (LinearMap.range (L : E →ₗ[ℝ] F) : Set F) =
      M ⁻¹' (LinearMap.range (fillerRestrictₗ p q L h1) :
        Set ↥(rangeS q)) := by
    ext y
    simp only [SetLike.mem_coe, mem_preimage, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨w, rfl⟩
      have hwz : L (w - zmap (L w)) - q (L (w - zmap (L w))) = 0 := by
        have h := (hzprop (L w)).2
        calc L (w - zmap (L w)) - q (L (w - zmap (L w)))
            = (L w - q (L w)) - (L (zmap (L w)) - q (L (zmap (L w)))) := by
              rw [map_sub, map_sub]; abel
          _ = 0 := by rw [h, sub_self]
      have hpw : p (w - zmap (L w)) = w - zmap (L w) :=
        fillerRestrict_mem_range_of hp h1 Φ hΦ _ hwz
      refine ⟨⟨w - zmap (L w), LinearMap.mem_range.2 ⟨w - zmap (L w), hpw⟩⟩, Subtype.ext ?_⟩
      rw [fillerRestrictₗ_apply]
      change L (w - zmap (L w)) = L w - L (zmap (L w))
      rw [map_sub]
    · rintro ⟨x, hx⟩
      have hx' : L x = y - L (zmap y) := congrArg Subtype.val hx
      exact ⟨x + zmap y, by rw [map_add, hx', sub_add_cancel]⟩
  rw [hpre]
  exact hA.preimage hMcont

include hp hq h1 hΦ in
/-- **Proposition 3.5 (2), the Fredholm property**: `A` is Fredholm iff `L` is. -/
theorem fillerRestrict_isFredholm_iff :
    IsFredholm (fillerRestrict p q L h1) ↔ IsFredholm L := by
  have : CompleteSpace ↥(rangeS p) :=
    (isClosed_range_of_idem p hp).completeSpace_coe
  have : CompleteSpace ↥(rangeS q) :=
    (isClosed_range_of_idem q hq).completeSpace_coe
  constructor
  · intro hA
    refine isFredholm_of_banach L ?_ (isClosed_range_of_fillerRestrict hp hq h1 Φ hΦ
      (by have := hA.isClosed_range; rwa [range_fillerRestrict] at this)) ?_
    · have := hA.finite_ker
      rw [ker_fillerRestrict] at this
      exact Module.Finite.equiv (fillerRestrict_kerEquiv hp h1 Φ hΦ)
    · have := hA.finite_coker
      rw [range_fillerRestrict] at this
      exact Module.Finite.equiv (fillerRestrict_cokerEquiv hp hq h1 Φ hΦ)
  · intro hL
    refine isFredholm_of_banach _ ?_ (by
      have := fillerRestrict_isClosed_range_of hp hq h1 Φ hΦ hL.isClosed_range
      rwa [range_fillerRestrict]) ?_
    · have := hL.finite_ker
      rw [ker_fillerRestrict]
      exact Module.Finite.equiv (fillerRestrict_kerEquiv hp h1 Φ hΦ).symm
    · have := hL.finite_coker
      rw [range_fillerRestrict]
      exact Module.Finite.equiv (fillerRestrict_cokerEquiv hp hq h1 Φ hΦ).symm

include hp hq h1 hΦ in
/-- **Proposition 3.5 (Filler), the linear algebra**: for idempotent `p : E → E`, `q : F → F` and
`L : E → F` with `(1 − q)Lp = 0` and `(1 − q)L : ker p → ker q` a topological isomorphism (the
matrix `[[A, B], [0, C]]` of `Dg(0)` with `C` an isomorphism), the restriction
`A = L|_{range p} : range p → range q` (the text's `Tf(0) : Dr(0)E → ρ(0)F`) satisfies:
(1) `A` is surjective iff `L` is; (2) `A` is Fredholm iff `L` is, and `ind A = ind L`. -/
theorem proposition_3_5 :
    (Surjective (fillerRestrict p q L h1) ↔ Surjective L) ∧
      (IsFredholm (fillerRestrict p q L h1) ↔ IsFredholm L) ∧
      fredholmIndex (fillerRestrict p q L h1) = fredholmIndex L :=
  ⟨fillerRestrict_surjective_iff hp hq h1 Φ hΦ, fillerRestrict_isFredholm_iff hp hq h1 Φ hΦ,
    fredholmIndex_fillerRestrict hp hq h1 Φ hΦ⟩

end FillerLinearAlgebra

end Polyfold
