import Polyfold.Chapter3.GermLevels

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.3,
Definition 3.28, Theorems 3.29 and 3.30 (existence and sc¹-regularity of the solution germ of an
sc⁰-contraction germ).  The induction to sc^k (Lemmas 3.31–3.32, Theorem 3.33) is in `GermIFT.lean`.

# Contraction germs: existence and sc¹-regularity of the solution germ

## The text, paraphrased

(Definition 3.28) An sc⁰-germ `f : O(C̃ ⊕ W, 0) → (W, 0)`, `C̃ = [0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ`, is an
**sc⁰-contraction germ** if `f(a, w) = w − B(a, w)` and for every `ε > 0` and `m ≥ 0`,
`|B(a, w) − B(a, w')|_m ≤ ε |w − w'|_m` for all `(a, w)`, `(a, w')` on level `m` sufficiently close
to `(0, 0)`.  (Theorem 3.29) It admits a uniquely determined sc⁰-solution germ
`δ : O(C̃, 0) → (W, 0)` with `f(a, δ(a)) = 0`: Banach's fixed point theorem, level by level, the
solutions on the levels agreeing by uniqueness.  (Theorem 3.30, from [21, Theorem 2.3], no proof
in the text) If `f` is sc¹ then `δ` is sc¹.  (Lemma 3.31) If `f` is sc^k and `δ` is sc^j, then
`f⁽¹⁾(v, b, u, w) = (u − B(v, u), w − DB(v, δ(v))(b, w))` is an sc⁰-contraction germ of class
`sc^{min(k−1, j)}` with solution germ `Tδ`.  (Lemma 3.32, Theorem 3.33) Iterating, if `f` is sc^k
then `δ` is sc^k.  (Theorem 3.35) The same for any finite-dimensional partial quadrant `C̃`.

## What is formalized

* `Polyfold.IsSc0ContractionGerm` (**Definition 3.28**, with the text's balls, for any convex `C̃`),
  and the working form `Polyfold.ContractionGerm P C̃ W`: the germ data together with explicit
  regions `N m ⊆ P` (open neighbourhoods of `0`), `K m ⊆ O m ⊆ W_m` (`K` closed, `O` open) on
  which `B(a, ·)` is a `1/2`-contraction (`O`) and self-mapping (`K`).
  `IsSc0ContractionGerm.toContractionGerm` (**the construction behind Theorem 3.29**, in
  `GermIFT.lean`) produces it from Definition 3.28 with balls.
* `ContractionGerm.sol` (the solution germ `δ`), `ContractionGerm.germ s` (the germs
  `(N (m+s) ∩ C̃)_m`), `ContractionGerm.IsSolutionGerm`; **Theorem 3.29** (`theorem_3_29`):
  existence, uniqueness in `O 0`, sc⁰; **Theorem 3.30** (`theorem_3_30`): `δ` is an sc¹-germ on
  `germ 1`.  (Lemmas 3.31–3.32, Theorem 3.33, Corollary 3.34 and Theorem 3.35 are in
  `GermIFT.lean`.)

## What the text leaves implicit, and the choices made (the findings)

* **Theorem 3.30 has no proof in the text** ([21, Theorem 2.3] is cited).  The proof given here:
  for `a₀` with `(a₀, δ(a₀)) ∈ U₂` the candidate derivative `A = (1 − D₂B)⁻¹D₁B` maps into `W₁`
  (the level-`1` operators exist at points of `U₂`), so `w₀ + Ah` is an `E₁`-increment of size
  `O(|h|)`, the sc¹-remainder of `B` is `o(|h|)`, and the `1/2`-contraction on level `0` gives
  `|δ(a₀+h) − δ(a₀) − Ah|₀ ≤ 2·o(|h|)`.  At points with `(a₀, δ(a₀)) ∈ U₁ ∖ U₂` the argument
  does not apply (`Ah ∉ W₁`); the conclusion holds for the **re-indexed germ `V_m := N(m+1) ∩ C̃`**
  (`germ 1`).  Re-indexing is legitimate here only because the domain `C̃ ⊆ P` is
  finite-dimensional (all levels of `P` coincide), which the text does not remark.  Each
  application of Theorem 3.30 in the induction of Theorem 3.33 costs one more shift: `δ` is sc^k
  on `germ s` for some `s` depending on `k` (the proof gives `s = 2^k − 1`, see `GermIFT.lean`;
  one germ for all `k` is the diagonal germ of `GermIFTSmooth.lean`).
* **The solution germ of `f⁽¹⁾` is a germ at `(0, 0) ∈ TC̃`, but `Tδ` must be controlled on
  `V_{m+1} ⊕ ℝⁿ`** (the fibre of the tangent germ is the whole space).  The text identifies the two
  by uniqueness without comment.  Here the contraction regions are kept explicit so that the
  regions of `f⁽¹⁾` are of the form `(N' × ℝⁿ) × (K_{m+1} × W_m)`: unbounded in the tangent
  directions, where `B⁽¹⁾` is affine.  Definition 3.28's balls do not express this, which is
  why the working form `ContractionGerm` carries the regions.
* Lemma 3.31's "as one verifies by comparing `Tf` with `f⁽¹⁾`" is the chain rule for germs with
  the maps `σ(v, b, u, w) = ((v, u), (b, w))` and `Γ(v, b, u, w) = ((v, δ(v)), (b, w))`, where
  `v ↦ δ(v) ∈ W₁` is the level-shifted germ (Proposition 1.17 for germs, `IsSckGerm.shift`).
* Lemma 3.9's estimate `|D₂B(a, w)ζ|_m ≤ ε|ζ|_m` needs differentiability of `B : U_{m+1} → W_m`
  (Proposition 1.16), proved for germs in `GermLevels.lean`; the text's proof says "recalling
  Proposition 1.17".
-/

open Set Filter Topology Function Asymptotics Metric

noncomputable section

namespace Polyfold

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

/-! ### The parameter product `P ⊕ W` -/

/-- `P ⊕ W` for a finite-dimensional `P` with the constant structure; its level `m` is `P × W_m`. -/
abbrev ScBanach.paramProd (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (W : ScBanach) : ScBanach := (ScBanach.const P).prod W

namespace ScBanach

variable (W)

lemma paramProd_toBase (m : ℕ) (p : (paramProd P W) m) :
    (paramProd P W).toBase m p = ((p.1, W.toBase m p.2) : P × W 0) := by
  rw [prod_toBase, const_toBase]

lemma paramProd_incl (m : ℕ) (p : (paramProd P W) (m + 1)) :
    (paramProd P W).incl m p = ((p.1, W.incl m p.2) : P × W m) := rfl

lemma paramProd_shift_toBase (m : ℕ) (p : (paramProd P W) (m + 1)) :
    (paramProd P W).shift.toBase m p = ((p.1, W.shift.toBase m p.2) : P × W 1) := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih _

lemma paramProd_lvlSet (C : Set P) (m : ℕ) :
    (paramProd P W).lvlSet (C ×ˢ univ) m = C ×ˢ univ := by
  ext p; rw [mem_lvlSet, paramProd_toBase]; simp

lemma const_lvlSet (C : Set P) (m : ℕ) : (ScBanach.const P).lvlSet C m = C := by
  ext a; rw [mem_lvlSet, const_toBase]

end ScBanach

/-- The finite-dimensional source `C̃ ⊆ P`: `0 ∈ C̃`, convex, nonempty interior (the data of
`IsQuadrantLike (const P) C̃`). -/
lemma isQuadrantLike_const_iff :
    IsQuadrantLike (ScBanach.const P) Ct ↔ (0 : P) ∈ Ct ∧ Convex ℝ Ct ∧ (interior Ct).Nonempty := by
  constructor
  · intro h
    exact ⟨h.zero_mem, by simpa [ScBanach.const_lvlSet] using h.convex 0,
      by simpa [ScBanach.const_lvlSet] using h.interior_nonempty 0⟩
  · rintro ⟨h0, hc, hi⟩
    exact ⟨h0, fun m => by simpa [ScBanach.const_lvlSet] using hc,
      fun m => by simpa [ScBanach.const_lvlSet] using hi⟩

lemma IsQuadrantLike.paramProd (hC : IsQuadrantLike (ScBanach.const P) Ct) (W : ScBanach) :
    IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ univ) := by
  obtain ⟨h0, hc, hi⟩ := isQuadrantLike_const_iff.1 hC
  exact isQuadrantLike_prod_univ h0 hc hi W

lemma IsQuadrantLike.prod_univ_const (hC : IsQuadrantLike (ScBanach.const P) Ct)
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] :
    IsQuadrantLike (ScBanach.const (P × Q)) (Ct ×ˢ univ) := by
  obtain ⟨h0, hc, hi⟩ := isQuadrantLike_const_iff.1 hC
  refine isQuadrantLike_const_iff.2 ⟨⟨h0, mem_univ _⟩, hc.prod convex_univ, ?_⟩
  rw [interior_prod_eq, interior_univ]; exact hi.prod univ_nonempty

/-! ### Definition 3.28 -/

/-- The level-`m` map `B_m : P × W_m → W_m` of `B : P × W₀ → W₀` (meaningful where `B` maps
`P × W_m` into `W_m`). -/
abbrev levelB (B : P × W 0 → W 0) (m : ℕ) (p : P × W m) : W m :=
  levelMap (E := ScBanach.paramProd P W) (F := W) B m p

@[simp] lemma levelB_zero (B : P × W 0 → W 0) (p : P × W 0) : levelB B 0 p = B p :=
  levelMap_zero (E := ScBanach.paramProd P W) (F := W) B p

/-- **Definition 3.28**: `f(a, w) = w − B(a, w)` is an **sc⁰-contraction germ** on the germ `G`
around `0 ∈ C̃ ⊕ W`: `B` is an sc⁰-germ with `B(0, 0) = 0`, and for every `ε > 0` and `m` there
is `r > 0` such that `|B(a, w) − B(a, w')|_m ≤ ε|w − w'|_m` for `a ∈ C̃`, `|a| < r`,
`|w|_m, |w'|_m < r` (such points lying in `U_m`). -/
structure IsSc0ContractionGerm (Ct : Set P) (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ))
    (B : P × W 0 → W 0) : Prop where
  isSc0 : IsSc0Germ G B
  B_zero : B (0, 0) = 0
  contraction : ∀ ε > 0, ∀ m, ∃ r > 0, ∀ a ∈ Ct, ‖a‖ < r → ∀ w w' : W m, ‖w‖ < r → ‖w'‖ < r →
    ((a, w) : P × W m) ∈ G.U m ∧ ‖levelB B m (a, w) - levelB B m (a, w')‖ ≤ ε * ‖w - w'‖

/-- The contraction germ `f = w − B(a, w)` of Definition 3.28, as a map. -/
def contractionMap (B : P × W 0 → W 0) : P × W 0 → W 0 := fun p => p.2 - B p

/-- **The working form of a contraction germ**: the data of Definition 3.28 together with explicit
regions: open neighbourhoods `N m` of `0` in `P` (decreasing), open `O m ∋ 0` and closed
`K m ⊆ O m` in `W_m`, compatible with the inclusions, such that for `a ∈ N m ∩ C̃` the map
`B_m(a, ·)` is a `1/2`-contraction on `O m` and maps `K m` into itself, all of `N m × O m` lying
in `U_m`. -/
structure ContractionGerm (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (Ct : Set P) (W : ScBanach) where
  /-- The map `B`, `f(a, w) = w − B(a, w)`. -/
  B : P × W 0 → W 0
  /-- The germ of neighbourhoods `O(C̃ ⊕ W, 0)`. -/
  G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)
  B_zero : B (0, 0) = 0
  isSc0 : IsSc0Germ G B
  N : ℕ → Set P
  N_open : ∀ m, IsOpen (N m)
  N_zero : ∀ m, (0 : P) ∈ N m
  N_anti : ∀ m, N (m + 1) ⊆ N m
  O : ∀ m, Set (W m)
  K : ∀ m, Set (W m)
  O_open : ∀ m, IsOpen (O m)
  K_closed : ∀ m, IsClosed (K m)
  K_zero : ∀ m, (0 : W m) ∈ K m
  K_sub : ∀ m, K m ⊆ O m
  K_incl : ∀ m, ∀ w ∈ K (m + 1), W.incl m w ∈ K m
  mem_G : ∀ m, ∀ a ∈ N m ∩ Ct, ∀ w ∈ O m, ((a, w) : P × W m) ∈ G.U m
  mapsTo : ∀ m, ∀ a ∈ N m ∩ Ct, MapsTo (fun w => levelB B m (a, w)) (K m) (K m)
  contr : ∀ m, ∀ a ∈ N m ∩ Ct, ∀ w ∈ O m, ∀ w' ∈ O m,
    ‖levelB B m (a, w) - levelB B m (a, w')‖ ≤ (1 / 2) * ‖w - w'‖

namespace ContractionGerm

variable (𝒞 : ContractionGerm P Ct W)

lemma N_anti_le {m n : ℕ} (h : m ≤ n) : 𝒞.N n ⊆ 𝒞.N m := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact (𝒞.N_anti _).trans ih

lemma zero_mem_O (m : ℕ) : (0 : W m) ∈ 𝒞.O m := 𝒞.K_sub m (𝒞.K_zero m)

lemma K_inclK {m k : ℕ} {w : W (m + k)} (hw : w ∈ 𝒞.K (m + k)) : W.inclK m k w ∈ 𝒞.K m := by
  induction k with
  | zero => exact hw
  | succ k ih => exact ih (𝒞.K_incl _ w hw)

/-- The level-`m` fixed points exist in `K m`. -/
lemma exists_fixed (m : ℕ) {a : P} (ha : a ∈ 𝒞.N m ∩ Ct) :
    ∃ w ∈ 𝒞.K m, levelB 𝒞.B m (a, w) = w := by
  set g : W m → W m := fun w => levelB 𝒞.B m (a, w) with hg
  have hsf : MapsTo g (𝒞.K m) (𝒞.K m) := 𝒞.mapsTo m a ha
  have hsc : IsComplete (𝒞.K m) := (𝒞.K_closed m).isComplete
  have hcontr : ContractingWith (1 / 2 : NNReal) (hsf.restrict g (𝒞.K m) (𝒞.K m)) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun w w' => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have := 𝒞.contr m a ha w.1 (𝒞.K_sub m w.2) w'.1 (𝒞.K_sub m w'.2)
    simpa using this
  obtain ⟨y, hy, hfix, -⟩ := hcontr.exists_fixedPoint' hsc hsf (𝒞.K_zero m) (edist_ne_top _ _)
  exact ⟨y, hy, hfix⟩

/-- Uniqueness of fixed points in `O m`. -/
lemma fixed_unique (m : ℕ) {a : P} (ha : a ∈ 𝒞.N m ∩ Ct) {w w' : W m} (hw : w ∈ 𝒞.O m)
    (hw' : w' ∈ 𝒞.O m) (h : levelB 𝒞.B m (a, w) = w) (h' : levelB 𝒞.B m (a, w') = w') :
    w = w' := by
  have := 𝒞.contr m a ha w hw w' hw'
  rw [h, h'] at this
  have h2 : ‖w - w'‖ ≤ 0 := by linarith
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)

open scoped Classical in
/-- The level-`m` solution `δ_m(a) ∈ K m` (junk outside `N m ∩ C̃`). -/
def fixLvl (m : ℕ) (a : P) : W m :=
  if h : a ∈ 𝒞.N m ∩ Ct then (𝒞.exists_fixed m h).choose else 0

lemma fixLvl_mem_K (m : ℕ) {a : P} (ha : a ∈ 𝒞.N m ∩ Ct) : 𝒞.fixLvl m a ∈ 𝒞.K m := by
  rw [fixLvl, dif_pos ha]; exact (𝒞.exists_fixed m ha).choose_spec.1

lemma fixLvl_mem_O (m : ℕ) {a : P} (ha : a ∈ 𝒞.N m ∩ Ct) : 𝒞.fixLvl m a ∈ 𝒞.O m :=
  𝒞.K_sub m (𝒞.fixLvl_mem_K m ha)

lemma fixLvl_fixed (m : ℕ) {a : P} (ha : a ∈ 𝒞.N m ∩ Ct) :
    levelB 𝒞.B m (a, 𝒞.fixLvl m a) = 𝒞.fixLvl m a := by
  rw [fixLvl, dif_pos ha]; exact (𝒞.exists_fixed m ha).choose_spec.2

lemma mem_G_fixLvl (m : ℕ) {a : P} (ha : a ∈ 𝒞.N m ∩ Ct) :
    ((a, 𝒞.fixLvl m a) : P × W m) ∈ 𝒞.G.U m :=
  𝒞.mem_G m a ha _ (𝒞.fixLvl_mem_O m ha)

lemma eq_fixLvl (m : ℕ) {a : P} (ha : a ∈ 𝒞.N m ∩ Ct) {w : W m} (hw : w ∈ 𝒞.O m)
    (h : levelB 𝒞.B m (a, w) = w) : w = 𝒞.fixLvl m a :=
  𝒞.fixed_unique m ha hw (𝒞.fixLvl_mem_O m ha) h (𝒞.fixLvl_fixed m ha)

/-- The level-`(m+1)` solution is the level-`m` solution (compatibility along the inclusion). -/
lemma incl_fixLvl (m : ℕ) {a : P} (ha : a ∈ 𝒞.N (m + 1) ∩ Ct) :
    W.incl m (𝒞.fixLvl (m + 1) a) = 𝒞.fixLvl m a := by
  have ha' : a ∈ 𝒞.N m ∩ Ct := ⟨𝒞.N_anti m ha.1, ha.2⟩
  refine 𝒞.eq_fixLvl m ha' (𝒞.K_sub m (𝒞.K_incl m _ (𝒞.fixLvl_mem_K (m + 1) ha))) ?_
  have := 𝒞.isSc0.incl_levelMap (𝒞.mem_G_fixLvl (m + 1) ha)
  rw [ScBanach.paramProd_incl] at this
  have h2 : W.incl m (levelB 𝒞.B (m + 1) (a, 𝒞.fixLvl (m + 1) a)) =
      levelB 𝒞.B m (a, W.incl m (𝒞.fixLvl (m + 1) a)) := this
  rw [← h2]
  exact congrArg _ (𝒞.fixLvl_fixed (m + 1) ha)

lemma shift_toBase_fixLvl (m : ℕ) {a : P} (ha : a ∈ 𝒞.N (m + 1) ∩ Ct) :
    W.shift.toBase m (𝒞.fixLvl (m + 1) a) = 𝒞.fixLvl 1 a := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have := ih ⟨𝒞.N_anti _ ha.1, ha.2⟩
    rw [← this]
    change W.shift.toBase m (W.shift.incl m _) = W.shift.toBase m _
    rw [ScBanach.shift_incl, 𝒞.incl_fixLvl (m + 1) ha]

/-- **The solution germ `δ`** (Theorem 3.29): the level-`0` fixed point. -/
def sol : P → W 0 := 𝒞.fixLvl 0

lemma toBase_fixLvl (m : ℕ) {a : P} (ha : a ∈ 𝒞.N m ∩ Ct) :
    W.toBase m (𝒞.fixLvl m a) = 𝒞.sol a := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [ScScale.toBase_succ, 𝒞.incl_fixLvl m ha]
    exact ih ⟨𝒞.N_anti m ha.1, ha.2⟩

lemma sol_fixed {a : P} (ha : a ∈ 𝒞.N 0 ∩ Ct) : 𝒞.B (a, 𝒞.sol a) = 𝒞.sol a := by
  have := 𝒞.fixLvl_fixed 0 ha
  rwa [levelB_zero] at this

lemma sol_zero : 𝒞.sol 0 = 0 := by
  have h0 : (0 : P) ∈ 𝒞.N 0 ∩ Ct := ⟨𝒞.N_zero 0, by
    have := 𝒞.G.U_subset 0 (𝒞.G.zero_mem 0)
    rw [ScBanach.lvlSet_zero] at this
    exact this.1⟩
  have := 𝒞.eq_fixLvl 0 h0 (𝒞.zero_mem_O 0) (by rw [levelB_zero]; exact 𝒞.B_zero)
  exact this.symm

/-- **Uniqueness (Theorem 3.29)**: a solution `w ∈ O 0` of `w = B(a, w)`, `a ∈ N 0 ∩ C̃`, is
`δ(a)`. -/
lemma eq_sol {a : P} (ha : a ∈ 𝒞.N 0 ∩ Ct) {w : W 0} (hw : w ∈ 𝒞.O 0) (h : 𝒞.B (a, w) = w) :
    w = 𝒞.sol a :=
  𝒞.eq_fixLvl 0 ha hw (by rw [levelB_zero]; exact h)

lemma levelMap_sol (m : ℕ) {a : P} (ha : a ∈ 𝒞.N m ∩ Ct) :
    levelMap (E := ScBanach.const P) 𝒞.sol m a = 𝒞.fixLvl m a :=
  levelMap_eq_of_toBase_eq (by rw [ScBanach.const_toBase]; exact 𝒞.toBase_fixLvl m ha)

/-- Continuity of the level-`m` solution in the parameter. -/
lemma continuousOn_fixLvl (m : ℕ) : ContinuousOn (𝒞.fixLvl m) (𝒞.N m ∩ Ct) := by
  intro a ha
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- continuity of `B_m(·, δ_m(a))` at `(a, δ_m(a))`
  have hc := 𝒞.isSc0.continuousOn m _ (𝒞.mem_G_fixLvl m ha)
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun a' ha' haa' => ?_⟩
  have hmem : ((a', 𝒞.fixLvl m a) : P × W m) ∈ 𝒞.G.U m := 𝒞.mem_G m a' ha' _ (𝒞.fixLvl_mem_O m ha)
  have hd : dist ((a', 𝒞.fixLvl m a) : P × W m) (a, 𝒞.fixLvl m a) < δ := by
    rw [Prod.dist_eq, dist_self]; exact max_lt haa' hδ
  have h1 : ‖levelB 𝒞.B m (a', 𝒞.fixLvl m a) - levelB 𝒞.B m (a, 𝒞.fixLvl m a)‖ < ε / 2 := by
    have := hδ' hmem hd
    rwa [dist_eq_norm] at this
  rw [dist_eq_norm]
  -- the contraction estimate
  have h2 := 𝒞.contr m a' ha' _ (𝒞.fixLvl_mem_O m ha') _ (𝒞.fixLvl_mem_O m ha)
  rw [𝒞.fixLvl_fixed m ha'] at h2
  have h3 : ‖𝒞.fixLvl m a' - 𝒞.fixLvl m a‖ ≤
      ‖𝒞.fixLvl m a' - levelB 𝒞.B m (a', 𝒞.fixLvl m a)‖ +
        ‖levelB 𝒞.B m (a', 𝒞.fixLvl m a) - levelB 𝒞.B m (a, 𝒞.fixLvl m a)‖ := by
    rw [𝒞.fixLvl_fixed m ha]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  linarith

/-! ### The germs `(N (m+s) ∩ C̃)_m` and the solution germ property -/

/-- The germ of neighbourhoods `V_m = N(m + s) ∩ C̃` of `0` in `C̃ ⊆ P`. -/
def germ (hC : IsQuadrantLike (ScBanach.const P) Ct) (s : ℕ) : ScNbhdGerm (ScBanach.const P) Ct where
  U m := 𝒞.N (m + s) ∩ Ct
  nested m a ha := ⟨𝒞.N_anti_le (by omega) ha.1, ha.2⟩
  zero_mem m := ⟨𝒞.N_zero _, hC.zero_mem⟩
  relOpen m := ⟨𝒞.N (m + s), 𝒞.N_open _, by rw [ScBanach.const_lvlSet]⟩

@[simp] lemma germ_U (hC : IsQuadrantLike (ScBanach.const P) Ct) (s m : ℕ) :
    (𝒞.germ hC s).U m = 𝒞.N (m + s) ∩ Ct := rfl

lemma germ_U_subset (hC : IsQuadrantLike (ScBanach.const P) Ct) {s t : ℕ} (h : s ≤ t) (m : ℕ) :
    (𝒞.germ hC t).U m ⊆ (𝒞.germ hC s).U m :=
  fun a ha => ⟨𝒞.N_anti_le (by omega) ha.1, ha.2⟩

/-- `δ : V → W` is a **solution germ** of the contraction germ: an sc⁰-germ on `V` with
`δ(0) = 0`, `(a, δ_m(a)) ∈ U_m` for `a ∈ V_m`, and `B(a, δ(a)) = δ(a)` on `V₀`. -/
structure IsSolutionGerm (V : ScNbhdGerm (ScBanach.const P) Ct) (δ : P → W 0) : Prop where
  isSc0 : IsSc0Germ V δ
  zero : δ 0 = 0
  mem_G : ∀ m, ∀ a ∈ V.U m, ((a, levelMap (E := ScBanach.const P) δ m a) : P × W m) ∈ 𝒞.G.U m
  fixed : ∀ a ∈ V.U 0, 𝒞.B (a, δ a) = δ a

/-- **Theorem 3.29 (Existence)**: the sc⁰-contraction germ admits the sc⁰-solution germ `δ` on
`V_m = N m ∩ C̃`, uniquely determined among the solutions in `O 0`. -/
theorem _root_.Polyfold.theorem_3_29 (hC : IsQuadrantLike (ScBanach.const P) Ct) :
    𝒞.IsSolutionGerm (𝒞.germ hC 0) 𝒞.sol ∧
      ∀ a ∈ 𝒞.N 0 ∩ Ct, ∀ w ∈ 𝒞.O 0, 𝒞.B (a, w) = w → w = 𝒞.sol a := by
  refine ⟨⟨⟨fun m a ha => ?_, fun m => ?_⟩, 𝒞.sol_zero, fun m a ha => ?_, fun a ha => ?_⟩,
    fun a ha w hw h => 𝒞.eq_sol ha hw h⟩
  · rw [ScBanach.const_toBase]
    exact ⟨𝒞.fixLvl m a, 𝒞.toBase_fixLvl m (by simpa using ha)⟩
  · exact (𝒞.continuousOn_fixLvl m).congr fun a ha => 𝒞.levelMap_sol m (by simpa using ha)
  · rw [𝒞.levelMap_sol m (by simpa using ha)]
    exact 𝒞.mem_G_fixLvl m (by simpa using ha)
  · exact 𝒞.sol_fixed (by simpa using ha)

/-- The solution germ property restricts to the smaller germs `germ s`. -/
lemma isSolutionGerm_germ (hC : IsQuadrantLike (ScBanach.const P) Ct) (s : ℕ) :
    𝒞.IsSolutionGerm (𝒞.germ hC s) 𝒞.sol := by
  have h := (theorem_3_29 𝒞 hC).1
  have hsub := 𝒞.germ_U_subset hC (Nat.zero_le s)
  exact ⟨h.isSc0.mono hsub, h.zero, fun m a ha => h.mem_G m a (hsub m ha),
    fun a ha => h.fixed a (hsub 0 ha)⟩


/-! ### Lemma 3.9 at level `m`: the fibre derivative is small -/

/-- A linear map of norm `≤ 1/2` has no nonzero fixed point. -/
lemma eq_zero_of_norm_le_half {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : Z →L[ℝ] Z} (hT : ‖T‖ ≤ 1 / 2) {ζ : Z} (h : T ζ = ζ) : ζ = 0 := by
  have h1 : ‖ζ‖ ≤ 1 / 2 * ‖ζ‖ := by
    calc ‖ζ‖ = ‖T ζ‖ := by rw [h]
      _ ≤ ‖T‖ * ‖ζ‖ := T.le_opNorm ζ
      _ ≤ 1 / 2 * ‖ζ‖ := by gcongr
  have h2 : ‖ζ‖ ≤ 0 := by linarith
  exact norm_le_zero_iff.1 h2

variable {D : (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] W 0}

/-- **Lemma 3.9 on level `m`** (with the constant `1/2`): for `(a, w) ∈ U_{m+1}` with
`a ∈ N (m+1) ∩ C̃`, `w ∈ O (m+1)` and `ι w ∈ O m`, the level-`m` operator `Df(a, w)` satisfies
`|D₂B(a, w) ζ|_m ≤ (1/2)|ζ|_m` for all `ζ ∈ W_m`.  Proof: for `ζ ∈ W_{m+1}` the difference quotient
of `B_m(a, ι w + t ζ)` is bounded by the contraction constant, and `B : U_{m+1} → W_m` is
differentiable (Proposition 1.16); then density of `W_{m+1}` in `W_m`. -/
lemma norm_levelDeriv_snd_le (hC : IsQuadrantLike (ScBanach.const P) Ct)
    (hB : IsSc1GermWith 𝒞.G 𝒞.B D) {m : ℕ} {a : P} (ha : a ∈ 𝒞.N (m + 1) ∩ Ct) {w : W (m + 1)}
    (hw : w ∈ 𝒞.O (m + 1)) (hw' : W.incl m w ∈ 𝒞.O m) (ζ : W m) :
    ‖levelDeriv D m ((a, w) : (ScBanach.paramProd P W) (m + 1)) ((0 : P), ζ)‖ ≤ 1 / 2 * ‖ζ‖ := by
  set E := ScBanach.paramProd P W with hE
  set L : W m →L[ℝ] W m :=
    (levelDeriv D m ((a, w) : E (m + 1))).comp (ContinuousLinearMap.inr ℝ P (W m)) with hL
  change ‖L ζ‖ ≤ 1 / 2 * ‖ζ‖
  have hclosed : IsClosed {ζ : W m | ‖L ζ‖ ≤ 1 / 2 * ‖ζ‖} :=
    isClosed_le (L.continuous.norm) (continuous_const.mul continuous_norm)
  refine (W.denseRange_incl m).induction_on ζ hclosed fun ζ' => ?_
  -- the point `x = (a, w) ∈ U_{m+1}` and the curve `t ↦ x + t (0, ζ')`
  have ha' : a ∈ 𝒞.N m ∩ Ct := ⟨𝒞.N_anti m ha.1, ha.2⟩
  have hx : ((a, w) : E (m + 1)) ∈ 𝒞.G.U (m + 1) := 𝒞.mem_G (m + 1) a ha w hw
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.isOpen_iff.1 (𝒞.O_open (m + 1)) w hw
  obtain ⟨r₀, hr₀, hr₀'⟩ := Metric.isOpen_iff.1 (𝒞.O_open m) _ hw'
  set η : ℝ := min (r₁ / (‖ζ'‖ + 1)) (r₀ / (‖W.incl m ζ'‖ + 1)) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hmem₁ : ∀ t ∈ Ico (0 : ℝ) η, w + t • ζ' ∈ 𝒞.O (m + 1) := by
    intro t ht
    refine hr₁' ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    calc t * ‖ζ'‖ ≤ (r₁ / (‖ζ'‖ + 1)) * ‖ζ'‖ :=
          mul_le_mul_of_nonneg_right (ht.2.le.trans (min_le_left _ _)) (norm_nonneg _)
      _ < r₁ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg ζ']
  have hmem₀ : ∀ t ∈ Ico (0 : ℝ) η, W.incl m w + t • W.incl m ζ' ∈ 𝒞.O m := by
    intro t ht
    refine hr₀' ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    calc t * ‖W.incl m ζ'‖ ≤ (r₀ / (‖W.incl m ζ'‖ + 1)) * ‖W.incl m ζ'‖ :=
          mul_le_mul_of_nonneg_right (ht.2.le.trans (min_le_right _ _)) (norm_nonneg _)
      _ < r₀ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (W.incl m ζ')]
  set γ : ℝ → E (m + 1) := fun t => ((a, w) : E (m + 1)) + t • ((0 : P), ζ') with hγ
  have hγmem : ∀ t ∈ Ico (0 : ℝ) η, γ t ∈ 𝒞.G.U (m + 1) := fun t ht => by
    have : γ t = ((a, w + t • ζ') : E (m + 1)) := by
      simp only [hγ, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]
    rw [this]; exact 𝒞.mem_G (m + 1) a ha _ (hmem₁ t ht)
  have hγd : HasDerivWithinAt γ ((0 : P), ζ') (Ico 0 η) 0 := by
    simpa [hγ] using ((hasDerivAt_id (0 : ℝ)).smul_const (((0 : P), ζ') : E (m + 1))).const_add
      ((a, w) : E (m + 1)) |>.hasDerivWithinAt
  -- the derivative of `φ = B_m ∘ ι ∘ γ` at `0`
  set φ : ℝ → W m := fun t => levelMap 𝒞.B m (E.incl m (γ t)) with hφ
  have hφd : HasDerivWithinAt φ (L (W.incl m ζ')) (Ico 0 η) 0 := by
    have h0 : γ 0 = ((a, w) : E (m + 1)) := by simp [hγ]
    have hF : HasFDerivWithinAt (levelMap 𝒞.B m ∘ E.incl m)
        ((levelDeriv D m ((a, w) : E (m + 1))).comp (E.incl m)) (𝒞.G.U (m + 1)) (γ 0) := by
      rw [h0]; exact hB.hasFDerivWithinAt_level (hC.paramProd W) hx
    exact hF.comp_hasDerivWithinAt (0 : ℝ) hγd hγmem
  -- the slope bound
  have hslope : ∀ t ∈ Ico (0 : ℝ) η \ {0}, ‖slope φ 0 t‖ ≤ 1 / 2 * ‖W.incl m ζ'‖ := by
    rintro t ⟨ht, ht0⟩
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm (by simpa using ht0))
    have hφt : φ t = levelB 𝒞.B m (a, W.incl m w + t • W.incl m ζ') := by
      simp only [hφ, hγ, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]
      change levelB 𝒞.B m (a, W.incl m (w + t • ζ')) = _
      rw [map_add, map_smul]
    have hφ0 : φ 0 = levelB 𝒞.B m (a, W.incl m w) := by
      simp only [hφ, hγ, zero_smul, add_zero]; rfl
    have hc := 𝒞.contr m a ha' _ (hmem₀ t ht) _ hw'
    rw [slope_def_module, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos htpos, hφt,
      hφ0]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at hc
    rw [inv_mul_le_iff₀ htpos]
    linarith
  have hne : (𝓝[Ico (0 : ℝ) η \ {0}] 0).NeBot := by
    rw [Ico_sdiff_left]
    exact mem_closure_iff_nhdsWithin_neBot.1 (by
      rw [closure_Ioo hη0.ne]; exact left_mem_Icc.2 hη0.le)
  have hlim : Tendsto (fun t => ‖slope φ 0 t‖) (𝓝[Ico (0 : ℝ) η \ {0}] 0)
      (𝓝 ‖L (W.incl m ζ')‖) :=
    (hasDerivWithinAt_iff_tendsto_slope.1 hφd).norm
  have := le_of_tendsto hlim (eventually_nhdsWithin_of_forall hslope)
  change ‖L (W.incl m ζ')‖ ≤ 1 / 2 * ‖W.incl m ζ'‖
  exact this

/-! ### Theorem 3.30: the solution germ is sc¹ -/

/-- The level-`m` operator `Df(a, δ_{m+1}(a)) : P × W_m → W_m` at the solution point. -/
def Lop (m : ℕ) (a : P) : (ScBanach.paramProd P W) m →L[ℝ] W m :=
  levelDeriv D m ((a, 𝒞.fixLvl (m + 1) a) : (ScBanach.paramProd P W) (m + 1))

/-- `D₂B(a, δ(a)) : W_m → W_m`. -/
def Top (m : ℕ) (a : P) : W m →L[ℝ] W m := (𝒞.Lop (D := D) m a).comp (ContinuousLinearMap.inr ℝ P (W m))

/-- The candidate derivative `Dδ(a) = (1 − D₂B)⁻¹ D₁B : P → W_m` of the solution germ. -/
def Aop (m : ℕ) (a : P) : P →L[ℝ] W m :=
  (Ring.inverse (1 - 𝒞.Top (D := D) m a)).comp ((𝒞.Lop (D := D) m a).comp (ContinuousLinearMap.inl ℝ P (W m)))

open scoped Classical in
/-- The derivative family of the solution germ on `germ 1`. -/
def solDeriv : (ScBanach.const P) 1 → (ScBanach.const P) 0 →L[ℝ] W 0 := fun a =>
  if a ∈ 𝒞.N 2 ∩ Ct then 𝒞.Aop (D := D) 0 a else 0

lemma solDeriv_of_mem {a : P} (ha : a ∈ 𝒞.N 2 ∩ Ct) :
    𝒞.solDeriv (D := D) a = 𝒞.Aop (D := D) 0 a := by
  rw [solDeriv, if_pos ha]

/-- `Lop (h, ζ) = Lop (h, 0) + Top ζ`. -/
lemma Lop_apply (m : ℕ) (a : P) (h : P) (ζ : W m) :
    𝒞.Lop (D := D) m a (h, ζ) = 𝒞.Lop (D := D) m a (h, 0) + 𝒞.Top (D := D) m a ζ := by
  simp only [Top, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rw [← map_add]; congr 1; simp

variable (hC : IsQuadrantLike (ScBanach.const P) Ct) (hB : IsSc1GermWith 𝒞.G 𝒞.B D)
include hC hB

lemma norm_Top_le {m : ℕ} {a : P} (ha : a ∈ 𝒞.N (m + 1) ∩ Ct) : ‖𝒞.Top (D := D) m a‖ ≤ 1 / 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun ζ => ?_
  exact 𝒞.norm_levelDeriv_snd_le hC hB ha (𝒞.fixLvl_mem_O (m + 1) ha)
    (by rw [𝒞.incl_fixLvl m ha]; exact 𝒞.fixLvl_mem_O m ⟨𝒞.N_anti m ha.1, ha.2⟩) ζ

lemma isUnit_one_sub_Top {m : ℕ} {a : P} (ha : a ∈ 𝒞.N (m + 1) ∩ Ct) :
    IsUnit (1 - 𝒞.Top (D := D) m a) :=
  isUnit_one_sub_of_norm_lt_one (lt_of_le_of_lt (𝒞.norm_Top_le hC hB ha) (by norm_num))

/-- The defining identity of the candidate derivative: `Df(a, δ(a))(h, Dδ(a)h) = Dδ(a)h`. -/
lemma Lop_Aop {m : ℕ} {a : P} (ha : a ∈ 𝒞.N (m + 1) ∩ Ct) (h : P) :
    𝒞.Lop (D := D) m a (h, 𝒞.Aop (D := D) m a h) = 𝒞.Aop (D := D) m a h := by
  rw [𝒞.Lop_apply]
  have hu := 𝒞.isUnit_one_sub_Top hC hB ha
  have key : (1 - 𝒞.Top (D := D) m a) (𝒞.Aop (D := D) m a h) = 𝒞.Lop (D := D) m a (h, 0) := by
    simp only [Aop, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    have := congrArg (fun T : W m →L[ℝ] W m => T (𝒞.Lop (D := D) m a (h, 0)))
      (Ring.mul_inverse_cancel (1 - 𝒞.Top (D := D) m a) hu)
    simpa using this
  change 𝒞.Aop (D := D) m a h - 𝒞.Top (D := D) m a (𝒞.Aop (D := D) m a h) =
    𝒞.Lop (D := D) m a (h, 0) at key
  rw [← key]; abel

/-- Uniqueness of solutions of `Lop (h, ζ) = ζ`. -/
lemma eq_Aop {m : ℕ} {a : P} (ha : a ∈ 𝒞.N (m + 1) ∩ Ct) {h : P} {ζ : W m}
    (hζ : 𝒞.Lop (D := D) m a (h, ζ) = ζ) : ζ = 𝒞.Aop (D := D) m a h := by
  have h1 := 𝒞.Lop_Aop hC hB ha h
  have h2 : 𝒞.Top (D := D) m a (ζ - 𝒞.Aop (D := D) m a h) = ζ - 𝒞.Aop (D := D) m a h := by
    have := congrArg₂ (· - ·) hζ h1
    simp only at this
    rw [𝒞.Lop_apply m a h ζ, 𝒞.Lop_apply m a h (𝒞.Aop (D := D) m a h)] at this
    rw [map_sub, ← this]; abel
  exact sub_eq_zero.1 (eq_zero_of_norm_le_half (𝒞.norm_Top_le hC hB ha) h2)

omit hC in
/-- `ι_m ∘ Lop m a = Lop 0 a ∘ ι_m` at solution points. -/
lemma toBase_Lop {m : ℕ} {a : P} (ha : a ∈ 𝒞.N (m + 1) ∩ Ct) (v : (ScBanach.paramProd P W) m) :
    W.toBase m (𝒞.Lop (D := D) m a v) = 𝒞.Lop (D := D) 0 a ((v.1, W.toBase m v.2)) := by
  simp only [Lop, levelDeriv_zero]
  rw [hB.toBase_levelDeriv (𝒞.mem_G_fixLvl (m + 1) ha), ScBanach.paramProd_shift_toBase,
    ScBanach.paramProd_toBase, 𝒞.shift_toBase_fixLvl m ha]

/-- The candidate derivatives are compatible with the inclusions. -/
lemma toBase_Aop {m : ℕ} {a : P} (ha : a ∈ 𝒞.N (m + 1) ∩ Ct) (h : P) :
    W.toBase m (𝒞.Aop (D := D) m a h) = 𝒞.Aop (D := D) 0 a h := by
  have ha0 : a ∈ 𝒞.N 1 ∩ Ct := ⟨𝒞.N_anti_le (by omega) ha.1, ha.2⟩
  refine 𝒞.eq_Aop hC hB ha0 ?_
  have := 𝒞.toBase_Lop hB ha (h, 𝒞.Aop (D := D) m a h)
  simp only at this
  rw [← this, 𝒞.Lop_Aop hC hB ha]

/-- **The differentiability step of Theorem 3.30**: `δ` is differentiable at `a₀ ∈ N 2 ∩ C̃` within
`N 2 ∩ C̃` with derivative `Aop 0 a₀`, by the approximate fixed point `δ(a₀) + Aop 1 a₀ h ∈ W₁`
and the `1/2`-contraction on level `0`. -/
lemma hasFDerivWithinAt_sol {a₀ : P} (ha₀ : a₀ ∈ 𝒞.N 2 ∩ Ct) :
    HasFDerivWithinAt 𝒞.sol (𝒞.Aop (D := D) 0 a₀) (𝒞.N 2 ∩ Ct) a₀ := by
  set E := ScBanach.paramProd P W with hE
  have ha₁ : a₀ ∈ 𝒞.N 1 ∩ Ct := ⟨𝒞.N_anti 1 ha₀.1, ha₀.2⟩
  have ha₀' : a₀ ∈ 𝒞.N 0 ∩ Ct := ⟨𝒞.N_anti_le (by omega) ha₀.1, ha₀.2⟩
  set A₁ := 𝒞.Aop (D := D) 1 a₀ with hA₁
  set A₀ := 𝒞.Aop (D := D) 0 a₀ with hA₀
  have hA₁₀ : ∀ h, W.toBase 1 (A₁ h) = A₀ h := fun h => 𝒞.toBase_Aop hC hB ha₀ h
  set x₁ : E 1 := (a₀, 𝒞.fixLvl 1 a₀) with hx₁
  have hx₁U : x₁ ∈ 𝒞.G.U 1 := 𝒞.mem_G_fixLvl 1 ha₁
  have hx₁B : E.toBase 1 x₁ = ((a₀, 𝒞.sol a₀) : P × W 0) := by
    rw [ScBanach.paramProd_toBase, 𝒞.toBase_fixLvl 1 ha₁]
  -- the key identity on level 0
  have hkey : ∀ h, D x₁ ((h, A₀ h) : P × W 0) = A₀ h := fun h => by
    have := 𝒞.Lop_Aop hC hB ha₁ h
    simpa [Lop, levelDeriv_zero] using this
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  -- the little-o of `B` at `x₁`
  have hlo := isLittleO_iff.1 (hasFDerivWithinAt_iff_isLittleO.1 (hB.hasFDerivWithinAt x₁ hx₁U))
    (show (0 : ℝ) < c / (2 * (1 + ‖A₁‖)) by positivity)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hlo)
  -- the radii for staying in `O 1` and `O 0`
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.isOpen_iff.1 (𝒞.O_open 1) _ (𝒞.fixLvl_mem_O 1 ha₁)
  obtain ⟨r₀, hr₀, hr₀'⟩ := Metric.isOpen_iff.1 (𝒞.O_open 0) _ (𝒞.fixLvl_mem_O 0 ha₀')
  set η : ℝ := min (min (r₁ / (‖A₁‖ + 1)) (r₀ / (‖A₀‖ + 1))) (δ / (1 + ‖A₁‖)) with hη
  have hη0 : 0 < η := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have ev1 : ∀ᶠ a in 𝓝[𝒞.N 2 ∩ Ct] a₀, a ∈ 𝒞.N 2 ∩ Ct := self_mem_nhdsWithin
  have ev2 : ∀ᶠ a in 𝓝[𝒞.N 2 ∩ Ct] a₀, dist a a₀ < η :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds a₀ hη0)
  filter_upwards [ev1, ev2] with a ha haη
  set h := a - a₀ with hh
  have hhη : ‖h‖ < η := by rw [hh, ← dist_eq_norm]; exact haη
  have ha1 : a ∈ 𝒞.N 1 ∩ Ct := ⟨𝒞.N_anti 1 ha.1, ha.2⟩
  have ha0 : a ∈ 𝒞.N 0 ∩ Ct := ⟨𝒞.N_anti_le (by omega) ha.1, ha.2⟩
  -- the increment `k = (h, A₁ h) ∈ E₁`
  set k : E 1 := (h, A₁ h) with hk
  have hknorm : ‖k‖ ≤ (1 + ‖A₁‖) * ‖h‖ := by
    rw [Prod.norm_def]
    refine max_le (by nlinarith [norm_nonneg h, norm_nonneg A₁]) ?_
    calc ‖A₁ h‖ ≤ ‖A₁‖ * ‖h‖ := A₁.le_opNorm h
      _ ≤ (1 + ‖A₁‖) * ‖h‖ := by nlinarith [norm_nonneg h]
  have hkδ : ‖k‖ < δ := by
    calc ‖k‖ ≤ (1 + ‖A₁‖) * ‖h‖ := hknorm
      _ < (1 + ‖A₁‖) * (δ / (1 + ‖A₁‖)) := by
          gcongr
          exact lt_of_lt_of_le hhη (min_le_right _ _)
      _ = δ := by field_simp
  have hzO1 : 𝒞.fixLvl 1 a₀ + A₁ h ∈ 𝒞.O 1 := by
    refine hr₁' ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    calc ‖A₁ h‖ ≤ ‖A₁‖ * ‖h‖ := A₁.le_opNorm h
      _ ≤ ‖A₁‖ * (r₁ / (‖A₁‖ + 1)) := by
          gcongr
          exact (lt_of_lt_of_le hhη ((min_le_left _ _).trans (min_le_left _ _))).le
      _ < r₁ := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg A₁]
  have hzO0 : 𝒞.sol a₀ + A₀ h ∈ 𝒞.O 0 := by
    refine hr₀' ?_
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖𝒞.sol a₀ + A₀ h - 𝒞.sol a₀‖ < r₀
    rw [add_sub_cancel_left]
    calc ‖A₀ h‖ ≤ ‖A₀‖ * ‖h‖ := A₀.le_opNorm h
      _ ≤ ‖A₀‖ * (r₀ / (‖A₀‖ + 1)) := by
          gcongr
          exact (lt_of_lt_of_le hhη ((min_le_left _ _).trans (min_le_right _ _))).le
      _ < r₀ := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg A₀]
  have hzU : x₁ + k ∈ 𝒞.G.U 1 := by
    have : x₁ + k = ((a, 𝒞.fixLvl 1 a₀ + A₁ h) : E 1) := by
      refine Prod.ext ?_ rfl
      show a₀ + (a - a₀) = a
      exact add_sub_cancel a₀ a
    rw [this]; exact 𝒞.mem_G 1 a ha1 _ hzO1
  -- the remainder of `B`
  have hrem := hδ' (by rw [dist_eq_norm, add_sub_cancel_left]; exact hkδ) hzU
  rw [add_sub_cancel_left] at hrem
  have hz : E.toBase 1 (x₁ + k) = ((a, 𝒞.sol a₀ + A₀ h) : P × W 0) := by
    rw [ScBanach.paramProd_toBase]
    refine Prod.ext ?_ ?_
    · show a₀ + (a - a₀) = a
      exact add_sub_cancel a₀ a
    · show W.toBase 1 (𝒞.fixLvl 1 a₀ + A₁ h) = 𝒞.sol a₀ + A₀ h
      rw [map_add, 𝒞.toBase_fixLvl 1 ha₁, hA₁₀]
  have hkB : E.toBase 1 k = ((h, A₀ h) : P × W 0) := by
    rw [ScBanach.paramProd_toBase]; simp only [hk, hA₁₀]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply] at hrem
  rw [hz, hx₁B, hkB, hkey, 𝒞.sol_fixed ha₀'] at hrem
  set r := 𝒞.B (a, 𝒞.sol a₀ + A₀ h) - 𝒞.sol a₀ - A₀ h with hr
  have hr' : ‖r‖ ≤ c / 2 * ‖h‖ := by
    calc ‖r‖ ≤ c / (2 * (1 + ‖A₁‖)) * ‖k‖ := hrem
      _ ≤ c / (2 * (1 + ‖A₁‖)) * ((1 + ‖A₁‖) * ‖h‖) := by gcongr
      _ = c / 2 * ‖h‖ := by field_simp
  -- the contraction on level 0
  have hc0 := 𝒞.contr 0 a ha0 _ (𝒞.fixLvl_mem_O 0 ha0) _ hzO0
  rw [levelB_zero, levelB_zero] at hc0
  change ‖𝒞.B (a, 𝒞.sol a) - 𝒞.B (a, 𝒞.sol a₀ + A₀ h)‖ ≤ 1 / 2 * ‖𝒞.sol a - (𝒞.sol a₀ + A₀ h)‖ at hc0
  rw [𝒞.sol_fixed ha0] at hc0
  have hid : 𝒞.sol a - 𝒞.B (a, 𝒞.sol a₀ + A₀ h) = (𝒞.sol a - (𝒞.sol a₀ + A₀ h)) - r := by
    rw [hr]; abel
  rw [hid] at hc0
  have htri : ‖𝒞.sol a - (𝒞.sol a₀ + A₀ h)‖ ≤ ‖𝒞.sol a - (𝒞.sol a₀ + A₀ h) - r‖ + ‖r‖ :=
    norm_le_norm_sub_add _ _
  have hfinal : ‖𝒞.sol a - (𝒞.sol a₀ + A₀ h)‖ ≤ c * ‖h‖ := by linarith
  change ‖𝒞.sol a - 𝒞.sol a₀ - A₀ (a - a₀)‖ ≤ c * ‖a - a₀‖
  rw [← hh, sub_sub]
  exact hfinal

/-- The level-`m` tangent map of the solution germ is `(a, h) ↦ (δ_{m+1}(a), Aop m a h)`. -/
lemma tangent_toBase_sol {m : ℕ} {a : P} (ha : a ∈ 𝒞.N (m + 2) ∩ Ct) (h : P) :
    W.tangent.toBase m ((𝒞.fixLvl (m + 1) a, 𝒞.Aop (D := D) m a h) : W.tangent m) =
      tangentMapWith 𝒞.sol (𝒞.solDeriv (D := D))
        ((ScBanach.const P).tangent.toBase m ((a, h) : (ScBanach.const P).tangent m)) := by
  have ha1 : a ∈ 𝒞.N (m + 1) ∩ Ct := ⟨𝒞.N_anti _ ha.1, ha.2⟩
  have ha2 : a ∈ 𝒞.N 2 ∩ Ct := ⟨𝒞.N_anti_le (by omega) ha.1, ha.2⟩
  rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase]
  change ((W.shift.toBase m (𝒞.fixLvl (m + 1) a), W.toBase m (𝒞.Aop (D := D) m a h)) : W.tangent 0) =
    (levelMap (E := ScBanach.const P) 𝒞.sol 1 ((ScBanach.const P).shift.toBase m a),
      𝒞.solDeriv (D := D) ((ScBanach.const P).shift.toBase m a) ((ScBanach.const P).toBase m h))
  have hsh : (ScBanach.const P).shift.toBase m a = a := by
    have := ScBanach.const_toBase P (m + 1) a
    rw [ScBanach.shift_toBase, ScBanach.const_toBase] at this
    exact this
  rw [hsh, ScBanach.const_toBase, 𝒞.shift_toBase_fixLvl m ha1, 𝒞.toBase_Aop hC hB ha1,
    𝒞.levelMap_sol 1 ⟨𝒞.N_anti_le (by omega) ha.1, ha.2⟩, 𝒞.solDeriv_of_mem ha2]

/-- Continuity of `(a, h) ↦ Aop m a h` on `(N (m+2) ∩ C̃) × P`, from the joint continuity of the
level operators and the `1/2`-contraction. -/
lemma continuousOn_Aop (m : ℕ) :
    ContinuousOn (fun q : P × P => 𝒞.Aop (D := D) m q.1 q.2) ((𝒞.N (m + 2) ∩ Ct) ×ˢ univ) := by
  set E := ScBanach.paramProd P W with hE
  intro q hq
  have hq1 : q.1 ∈ 𝒞.N (m + 1) ∩ Ct := ⟨𝒞.N_anti _ hq.1.1, hq.1.2⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set ζ := 𝒞.Aop (D := D) m q.1 q.2 with hζ
  -- the continuous map `(a', h') ↦ Lop m a' (h', ζ)`
  have hF : ContinuousOn (fun q' : P × P => 𝒞.Lop (D := D) m q'.1 (q'.2, ζ))
      ((𝒞.N (m + 1) ∩ Ct) ×ˢ univ) := by
    refine (hB.continuousOn_levelDeriv m).comp
      (f := fun q' : P × P => (((q'.1, 𝒞.fixLvl (m + 1) q'.1) : E (m + 1)), ((q'.2, ζ) : E m))) ?_ ?_
    · refine ContinuousOn.prodMk (ContinuousOn.prodMk continuousOn_fst ?_) (by fun_prop)
      exact (𝒞.continuousOn_fixLvl (m + 1)).comp continuousOn_fst fun q' hq' => hq'.1
    · intro q' hq'
      exact ⟨𝒞.mem_G_fixLvl (m + 1) hq'.1, mem_univ _⟩
  have hFq := hF q ⟨hq1, mem_univ _⟩
  rw [Metric.continuousWithinAt_iff] at hFq
  obtain ⟨δ, hδ, hδ'⟩ := hFq (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun q' hq' hqq' => ?_⟩
  have hq'1 : q'.1 ∈ 𝒞.N (m + 1) ∩ Ct := ⟨𝒞.N_anti _ hq'.1.1, hq'.1.2⟩
  have h1 := hδ' ⟨hq'1, mem_univ _⟩ hqq'
  rw [dist_eq_norm] at h1 ⊢
  set ζ' := 𝒞.Aop (D := D) m q'.1 q'.2 with hζ'
  -- `ζ' − ζ = Top q'.1 (ζ' − ζ) + [Lop q'.1 (q'.2, ζ) − Lop q.1 (q.2, ζ)]`
  have hζfix : 𝒞.Lop (D := D) m q.1 (q.2, ζ) = ζ := 𝒞.Lop_Aop hC hB hq1 q.2
  have hζ'fix : 𝒞.Lop (D := D) m q'.1 (q'.2, ζ') = ζ' := 𝒞.Lop_Aop hC hB hq'1 q'.2
  have hT := 𝒞.norm_Top_le hC hB hq'1
  have hid : ζ' - ζ = 𝒞.Top (D := D) m q'.1 (ζ' - ζ) +
      (𝒞.Lop (D := D) m q'.1 (q'.2, ζ) - 𝒞.Lop (D := D) m q.1 (q.2, ζ)) := by
    rw [map_sub, hζfix]
    conv_lhs => rw [← hζ'fix]
    rw [𝒞.Lop_apply m q'.1 q'.2 ζ', 𝒞.Lop_apply m q'.1 q'.2 ζ]
    abel
  have hT' : ‖𝒞.Top (D := D) m q'.1 (ζ' - ζ)‖ ≤ 1 / 2 * ‖ζ' - ζ‖ :=
    calc ‖𝒞.Top (D := D) m q'.1 (ζ' - ζ)‖ ≤ ‖𝒞.Top (D := D) m q'.1‖ * ‖ζ' - ζ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 / 2 * ‖ζ' - ζ‖ := by gcongr
  have h2 : ‖ζ' - ζ‖ ≤ ‖𝒞.Top (D := D) m q'.1 (ζ' - ζ)‖ +
      ‖𝒞.Lop (D := D) m q'.1 (q'.2, ζ) - 𝒞.Lop (D := D) m q.1 (q.2, ζ)‖ := by
    conv_lhs => rw [hid]
    exact norm_add_le _ _
  linarith

/-- **Theorem 3.30** (sc¹-regularity of the solution germ): if the sc⁰-contraction germ is sc¹,
the solution germ `δ` is an sc¹-germ **on the re-indexed germ `V_m = N(m+1) ∩ C̃`** (`germ 1`),
with derivative family `solDeriv`.  (See the module docstring for the shift.) -/
theorem isSc1GermWith_sol : IsSc1GermWith (𝒞.germ hC 1) 𝒞.sol (𝒞.solDeriv (D := D)) where
  isSc0 := (𝒞.isSolutionGerm_germ hC 1).isSc0
  hasFDerivWithinAt a ha := by
    have ha2 : a ∈ 𝒞.N 2 ∩ Ct := ha
    have h1 := 𝒞.hasFDerivWithinAt_sol hC hB ha2
    have hfun : 𝒞.sol ∘ (ScBanach.const P).toBase 1 = 𝒞.sol :=
      funext fun x => congrArg 𝒞.sol (ScBanach.const_toBase P 1 x)
    have hset : (𝒞.germ hC 1).U 1 = 𝒞.N 2 ∩ Ct := rfl
    rw [hfun, hset, 𝒞.solDeriv_of_mem ha2]
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp only [ContinuousLinearMap.comp_apply]
    rw [ScBanach.constScale_toBase]
  tangent_isSc0 := by
    refine ⟨fun m q hq => ?_, fun m => ?_⟩
    · have hq1 : q.1 ∈ 𝒞.N (m + 2) ∩ Ct := hq.1
      exact ⟨(𝒞.fixLvl (m + 1) q.1, 𝒞.Aop (D := D) m q.1 q.2), 𝒞.tangent_toBase_sol hC hB hq1 q.2⟩
    · have hU : (𝒞.germ hC 1).tangent.U m = (𝒞.N (m + 2) ∩ Ct) ×ˢ univ := rfl
      rw [hU]
      refine ContinuousOn.congr (f := fun q : P × P =>
        ((𝒞.fixLvl (m + 1) q.1, 𝒞.Aop (D := D) m q.1 q.2) : W.tangent m)) ?_ fun q hq => ?_
      · refine ContinuousOn.prodMk ?_ (𝒞.continuousOn_Aop hC hB m)
        exact (𝒞.continuousOn_fixLvl (m + 1)).comp continuousOn_fst
          fun q hq => ⟨𝒞.N_anti _ hq.1.1, hq.1.2⟩
      · exact levelMap_eq_of_toBase_eq (𝒞.tangent_toBase_sol hC hB hq.1 q.2)

omit hC hB in
/-- **Theorem 3.30**, as stated: an sc¹ sc⁰-contraction germ has an sc¹ solution germ. -/
theorem _root_.Polyfold.theorem_3_30 (hC : IsQuadrantLike (ScBanach.const P) Ct)
    (hB : IsSc1Germ 𝒞.G 𝒞.B) :
    𝒞.IsSolutionGerm (𝒞.germ hC 1) 𝒞.sol ∧ IsSckGerm 1 (𝒞.germ hC 1) 𝒞.sol := by
  obtain ⟨D, hD⟩ := hB
  have h1 := 𝒞.isSc1GermWith_sol hC hD
  refine ⟨𝒞.isSolutionGerm_germ hC 1, h1.isSc1Germ, ?_⟩
  exact (IsSc1Germ.tangentMapGerm_isSc0 h1.isSc1Germ)

end ContractionGerm

end Polyfold
