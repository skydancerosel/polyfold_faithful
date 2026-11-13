import Polyfold.Chapter7.ReducedNotHausdorff
import Polyfold.Chapter1.ExpositionLemmas

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.5,
**Remark 9.5.20** (pp. 451–452; 2017: Remark 9.8), gap G.110: the sc-retract behind the
remark's M-polyfold `X = {(−1,0)} ∪ ((−1,1) × B) ∪ {(1,0)} ⊆ ℝ × ℂ`.

# A retract whose dimension jumps `0 → 3 → 0`

The remark asserts that `X` "can be equipped with an M-polyfold structure".  `X` is not locally
compact at `(±1, 0)`, so a chart there is infinite-dimensional; the points `(±1,0)` are boundary
points (`∂X = {(±1,0)}`, p. 452).  This file builds one global model:

* `E = ℝ² ⊕ (X_w ⊕ X_w)`, `X_w` the weighted sequence space of Remark 4.1.3's example
  (`ScOneExample.X`), with the partial quadrant `C = [0,∞)² ⊕ (X_w ⊕ X_w)` (`quadrant 2`).
* `L(p) = fam(p₀p₁) ⊕ fam(p₀p₁)` (`K3.L`), Remark 4.1.3's moving rank-one projections
  (`RemarkFourThree.fam`, `0` for `t ≤ 0`) composed with `G(p) = p₀p₁`, on both factors; a loss
  family (`IsLossFamily.comp_contDiff`, `IsLossFamily.diag`).
* `ρ(p) = 2p/|p|`, the radial retraction of `[0,∞)² \ {0}` onto the quarter circle of radius `2`
  (it keeps the faces `{pᵢ = 0}`).
* **`K3.Rt`**: the sc-smooth retraction `r(p, a, b) = (ρ p, L(ρ p)(a, b))` of
  `U = C \ {p = 0}` (`ScRetraction E C`).  Its retract `O = r(U)` (`K3.mem_O_iff`) is the quarter
  circle with a plane `ℝβ ⊕ ℝβ` over each interior point and the point `0` over each end.

The remark's set `X` and its chart onto `O` are in `GapP3_K3_MPolyfold.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### Loss families: reparametrization and the diagonal family -/

section LossFamilyOps

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V'] {Z W : ScBanach}

set_option linter.unusedSectionVars false

/-- A loss family composed with a `C^∞` reparametrization `g : V' → V` is a loss family. -/
theorem IsLossFamily.comp_contDiff {L : V → ∀ m, Z m →L[ℝ] W m} (h : IsLossFamily L)
    {g : V' → V} (hg : ContDiff ℝ ∞ g) : IsLossFamily fun p => L (g p) where
  toBase p m z := h.toBase (g p) m z
  continuous m := (h.continuous m).comp ((hg.continuous.comp continuous_fst).prodMk continuous_snd)
  contDiff m := (h.contDiff m).comp hg

/-- The diagonal family `L(p) ⊕ L(p)` on `Z ⊕ Z`. -/
def diagFam (L : V → ∀ m, Z m →L[ℝ] Z m) (p : V) (m : ℕ) : (Z.prod Z) m →L[ℝ] (Z.prod Z) m :=
  (L p m).prodMap (L p m)

lemma diagFam_apply (L : V → ∀ m, Z m →L[ℝ] Z m) (p : V) (m : ℕ) (z : (Z.prod Z) m) :
    diagFam L p m z = ((L p m z.1, L p m z.2) : Z m × Z m) := rfl

/-- The diagonal of a loss family is a loss family. -/
theorem IsLossFamily.diag {L : V → ∀ m, Z m →L[ℝ] Z m} (h : IsLossFamily L) :
    IsLossFamily (diagFam L) where
  toBase p m z := by
    rw [ScBanach.prod_toBase, ScBanach.prod_toBase Z Z m z]
    exact Prod.ext (h.toBase p m z.1) (h.toBase p m z.2)
  continuous m :=
    ((h.continuous m).comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      ((h.continuous m).comp (continuous_fst.prodMk continuous_snd.snd))
  contDiff m := by
    have e : (fun p => (diagFam L p m).comp ((Z.prod Z).incl m)) = fun p =>
        ContinuousLinearMap.prodMapL ℝ _ _ _ _ ((L p m).comp (Z.incl m), (L p m).comp (Z.incl m)) := by
      funext p
      ext z <;> rfl
    rw [e]
    exact (ContinuousLinearMap.prodMapL ℝ _ _ _ _).contDiff.comp ((h.contDiff m).prodMk (h.contDiff m))

end LossFamilyOps

namespace K3

open RemarkFourThree ScOneExample

/-! ### The model space and the family -/

/-- The fibre `X_w ⊕ X_w` (`X_w` = Remark 4.1.3's weighted sequence space). -/
abbrev Z2 : ScBanach := X.prod X

/-- The base `ℝ²`. -/
abbrev V2 : Type := Fin 2 → ℝ

/-- The model `E = ℝ² ⊕ (X_w ⊕ X_w)`. -/
abbrev E : ScBanach := (ScBanach.const V2).prod Z2

/-- `G(p) = p₀ p₁`, positive on the open quarter plane, `0` on its faces. -/
def G (p : V2) : ℝ := p 0 * p 1

lemma contDiff_G : ContDiff ℝ ∞ G :=
  (contDiff_apply ℝ ℝ (0 : Fin 2)).mul (contDiff_apply ℝ ℝ (1 : Fin 2))

/-- `L(p) = fam(G p) ⊕ fam(G p)` on `X_w ⊕ X_w`. -/
def L : V2 → ∀ m, Z2 m →L[ℝ] Z2 m := diagFam fun p => fam (G p)

theorem isLossFamily_L : IsLossFamily L :=
  (isLossFamily_fam.comp_contDiff contDiff_G).diag

lemma L_apply (p : V2) (m : ℕ) (z : Z2 m) : L p m z = ((fam (G p) m z.1, fam (G p) m z.2) : _) :=
  rfl

theorem L_idem (p : V2) (z : Z2 0) : L p 0 (L p 0 z) = L p 0 z :=
  Prod.ext (fam_idem _ _) (fam_idem _ _)

/-! ### The radial retraction of the quarter plane -/

/-- The Euclidean length `|p|`. -/
def len (p : V2) : ℝ := √(p 0 ^ 2 + p 1 ^ 2)

lemma sq_add_sq_pos {p : V2} (hp : p ≠ 0) : 0 < p 0 ^ 2 + p 1 ^ 2 := by
  by_contra h
  apply hp
  have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
  have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
  funext i
  fin_cases i
  · exact h0
  · exact h1

lemma len_pos {p : V2} (hp : p ≠ 0) : 0 < len p := Real.sqrt_pos.2 (sq_add_sq_pos hp)

/-- `ρ(p) = 2p/|p|`. -/
def ρ (p : V2) : V2 := (2 / len p) • p

lemma ρ_apply (p : V2) (i : Fin 2) : ρ p i = 2 / len p * p i := rfl

lemma len_smul {p : V2} {c : ℝ} (hc : 0 ≤ c) : len (c • p) = c * len p := by
  unfold len
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (c * p 0) ^ 2 + (c * p 1) ^ 2 = c ^ 2 * (p 0 ^ 2 + p 1 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

lemma len_ρ {p : V2} (hp : p ≠ 0) : len (ρ p) = 2 := by
  rw [ρ, len_smul (div_nonneg zero_le_two (len_pos hp).le)]
  field_simp [(len_pos hp).ne']

lemma ρ_ne_zero {p : V2} (hp : p ≠ 0) : ρ p ≠ 0 := by
  intro h
  have := len_ρ hp
  rw [h, len] at this
  simp at this

lemma ρ_ρ {p : V2} (hp : p ≠ 0) : ρ (ρ p) = ρ p := by
  change (2 / len (ρ p)) • ρ p = ρ p
  rw [len_ρ hp, div_self two_ne_zero, one_smul]

lemma ρ_nonneg {p : V2} (hp : ∀ i, 0 ≤ p i) (hp0 : p ≠ 0) (i : Fin 2) : 0 ≤ ρ p i :=
  mul_nonneg (div_nonneg zero_le_two (len_pos hp0).le) (hp i)

lemma contDiffOn_ρ : ContDiffOn ℝ ∞ ρ {p | p ≠ 0} := by
  have hlen : ContDiffOn ℝ ∞ len {p | p ≠ 0} := by
    refine ContDiffOn.sqrt ?_ fun p hp => (sq_add_sq_pos hp).ne'
    exact (((contDiff_apply ℝ ℝ (0 : Fin 2)).pow 2).add
      ((contDiff_apply ℝ ℝ (1 : Fin 2)).pow 2)).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun p : V2 => 2 / len p) {p | p ≠ 0} :=
    (contDiffOn_const (c := (2 : ℝ))).div hlen fun p hp => (len_pos hp).ne'
  exact h2.smul contDiffOn_id

/-! ### The retraction -/

/-- The base map `(p, z) ↦ (ρ p, z)`. -/
def base (q : E 0) : E 0 := (ρ q.1, q.2)

/-- The domain `U = C \ {p = 0}`. -/
def Udom : Set (E 0) := {q | q.1 ≠ 0} ∩ quadrant 2 Z2 0

lemma isRelOpen_Udom : IsRelOpenInQuadrant E (quadrant 2 Z2 0) Udom :=
  ⟨⟨2, Z2, ScIso.refl _, by ext; rfl⟩, {q | q.1 ≠ 0},
    isOpen_ne_fun continuous_fst continuous_const, rfl⟩

lemma isScSmooth_base : IsScSmooth (E := E) Udom base := by
  have h1 : IsScSmooth (E := E) (F := ScBanach.const V2) Udom fun q => ρ q.1 := by
    refine IsScSmooth.of_contDiffOn_finiteDimensional isRelOpen_Udom.isScDomain ?_
    exact contDiffOn_ρ.comp (contDiff_fst.contDiffOn) fun q hq => hq.1
  exact h1.scPair isRelOpen_Udom.isScDomain
    ((ScBanach.prodSndOp _ _).isScSmooth isRelOpen_Udom.isScDomain)

lemma base_mem_Udom {q : E 0} (hq : q ∈ Udom) : base q ∈ Udom :=
  ⟨ρ_ne_zero hq.1, fun i => ρ_nonneg hq.2 hq.1 i⟩

/-- **The sc-smooth retraction** `r(p, a, b) = (ρ p, L(ρ p)(a, b))` of `U = C \ {p = 0}`, `C` the
partial quadrant `[0,∞)² ⊕ (X_w ⊕ X_w)`. -/
def Rt : ScRetraction E (quadrant 2 Z2 0) where
  U := Udom
  toFun q := famRetr L (base q)
  relOpen := isRelOpen_Udom
  mapsTo q hq := base_mem_Udom hq
  isScSmooth := by
    have h := isLossFamily_L.isScSmooth_famRetr.comp isRelOpen_Udom.isScDomain
      (isScDomain_univ _) isScSmooth_base (mapsTo_univ _ _)
    exact h
  idem q hq := by
    change (ρ (ρ q.1), L (ρ (ρ q.1)) 0 (L (ρ q.1) 0 q.2)) = (ρ q.1, L (ρ q.1) 0 q.2)
    rw [ρ_ρ hq.1, L_idem]

lemma Rt_apply (q : E 0) : Rt q = (ρ q.1, L (ρ q.1) 0 q.2) := rfl

/-- The retract `O = r(U)`. -/
abbrev O : Set (E 0) := Rt.retract

/-- The quarter circle of radius `2`. -/
def arc : Set V2 := {p | (∀ i, 0 ≤ p i) ∧ len p = 2}

lemma ne_zero_of_mem_arc {p : V2} (hp : p ∈ arc) : p ≠ 0 := by
  rintro rfl
  have := hp.2
  simp [len] at this

lemma ρ_of_mem_arc {p : V2} (hp : p ∈ arc) : ρ p = p := by
  rw [ρ, hp.2, div_self two_ne_zero, one_smul]

/-- **The retract**: `q ∈ O` iff `q.1` lies on the quarter circle and `q.2` in the range of
`L(q.1)`. -/
theorem mem_O_iff (q : E 0) : q ∈ O ↔ q.1 ∈ arc ∧ L q.1 0 q.2 = q.2 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨fun i => ρ_nonneg hp.2 hp.1 i, len_ρ hp.1⟩, ?_⟩
    exact L_idem _ _
  · rintro ⟨h1, h2⟩
    refine ⟨q, ⟨ne_zero_of_mem_arc h1, h1.1⟩, ?_⟩
    rw [Rt_apply, ρ_of_mem_arc h1, h2]

end K3

end Polyfold
