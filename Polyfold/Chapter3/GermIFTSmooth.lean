import Polyfold.Chapter3.GermFilling
import Polyfold.Chapter3.SolutionLinearization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.3,
Corollary 3.3.7 (preprint 3.34) ("in particular, `δ` is sc-smooth at the smooth point `0`") and Theorem 3.35
("if `f` is sc-smooth, so is its solution germ"), on **one** germ of neighbourhoods; Lemma 3.3.4 (preprint 3.31)
("`f⁽¹⁾` is an sc⁰-contraction germ") in the sense of Definition 3.3.1 (preprint 3.28).

# The solution germ is an sc-smooth germ: one germ for all `k`

## The text, paraphrased

(Corollary 3.3.7 (preprint 3.34)) If the sc⁰-contraction germ `f(a, w) = w − B(a, w)` is sc-smooth, then for all
`m, k` there is a relatively open `V_{m,k} ∋ 0` in `C̃` with `δ(V_{m,k}) ⊆ W_m` and
`δ : V_{m,k} → W_m` of class `C^k`; in particular, `δ` is sc-smooth at the smooth point `0`.
(Theorem 3.35) For a finite-dimensional partial quadrant `C̃`, if the sc⁰-contraction germ `f` is
of class sc^k, so is its solution germ; if `f` is sc-smooth, so is its solution germ.

## What is formalized

* `ScNbhdGerm.inter` (the intersection of two germs of neighbourhoods) and, for the constant
  structure of a finite-dimensional `P`, `ScNbhdGerm.ofOpen` (the germ `(u ∩ C̃)_m` of an open
  `u ∋ 0`).
* `isSckGerm_of_levels` (**locality of sc^k in the levels**): `f` is an sc^k-germ on `G'` as soon
  as for every `j` there is a germ `G_j`, containing `G'` on the levels `≥ j`
  (`G'_{m+j} ⊆ (G_j)_{m+j}`), on which `f` is sc^j.  The `j`-th tangent germ of `f` on `G'` only
  involves the levels `≥ j` of `G'`.  `isScSmoothGerm_of_levels`: the same for every `k`.
* `ContractionGerm.germDiag`, the germ `V_m = N(m + t_m) ∩ C̃` for a nondecreasing shift
  `t : ℕ → ℕ`; `ContractionGerm.diagShift s m = Σ_{j ≤ m} s_j`;
  `ContractionGerm.isScSmoothGerm_germDiag`: if `δ` is sc^k on `germ s_k` for every `k`, it is
  sc-smooth on the diagonal germ `germDiag (diagShift s)`.
* **Corollary 3.3.7 (preprint 3.34), "`δ` is sc-smooth"** (`corollary_3_3_7_isScSmoothGerm`) and **Theorem 3.35,
  second sentence** (`theorem_3_35_isScSmoothGerm_preprint`, `C̃` a partial quadrant): for an sc-smooth
  working-form contraction germ, the solution germ `δ = sol` is an sc-smooth germ
  (`IsScSmoothGerm`, sc^k for every `k`) on **one** germ `germDiag t`, and is a solution germ there.
* **Theorem 3.35 in the text's form** (`theorem_3_35_of_isSc0ContractionGerm_preprint`): for an
  sc⁰-contraction germ of Definition 3.3.1 (preprint 3.28) and **any** representative `(V, δ)` of its solution germ
  (an sc⁰-germ with `δ(0) = 0` and `f(a, δ(a)) = 0` on `V₀`): if `f` is sc^k, `δ` is sc^k on a
  smaller germ `V' ⊆ V`; if `f` is sc-smooth, `δ` is sc-smooth on one smaller germ `V' ⊆ V`.
  Supporting lemmas: `isSckGerm_contractionMap_iff` (`f = w − B` is sc^k iff `B` is) and
  `IsSc0ContractionGerm.exists_eq_sol` (a representative agrees with the constructed `sol` near
  `0`, by uniqueness of the fixed point in `O₀`).

* **Lemma 3.3.4 (preprint 3.31), "`f⁽¹⁾` is an sc⁰-contraction germ", in the sense of Definition 3.3.1 (preprint 3.28)**
  (`ContractionGerm.isSc0ContractionGerm_next`): if the working form satisfies Definition 3.3.1 (preprint 3.28)
  (e.g. `h.toContractionGerm`), so does `f⁽¹⁾` on its germ `nextG s`; the project's
  `ContractionGerm.next` only records a `1/2`-contraction.  It rests on Lemma 3.1.9 (preprint 3.9) on level `m`
  with an arbitrary `ε` (`IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le`,
  `SolutionLinearization.lean`, which is why this file imports that one).

These are round-trip items V3.31 and V3.32 (`RoundTrip/Items/V3_31.lean`, `V3_32.lean`), where the
locality lemma and the diagonal germ were first proved, and V3.28 (`RoundTrip/Items/V3_28.lean`,
the Definition 3.3.1 (preprint 3.28) estimate for `f⁽¹⁾` inside its `A_to_B`); moved here and simplified (for the
working form, the diagonal germ is `N(m + t_m) ∩ C̃` itself, and the Definition 3.3.1 (preprint 3.28) estimate is
stated for `next s`, any `s`).

## What the text leaves implicit, and the choices made (the findings)

* **One germ for all `k`.**  The proof of Theorem 3.3.6 (preprint 3.33) shifts the germ at every induction step:
  `δ` is sc^k on `germ s_k = (N(m + s_k) ∩ C̃)_m` with `s_k = 2^k − 1` (`theorem_3_3_6`,
  `theorem_3_3_6_smooth`, `corollary_3_3_7`, `theorem_3_35_smooth_preprint` keep this `k`-dependent form).
  With a germ as a fixed sequence of sets (Definition 3.1.1 (preprint 3.1) here), "sc-smooth" (Definition 3.1.2 (preprint 3.2),
  `IsScSmoothGerm`) asks for sc^k for every `k` on the *same* sequence.  Since sc^j only involves
  the levels `≥ j` (`isSckGerm_of_levels`), the diagonal `t_m = Σ_{j ≤ m} s_j` works: on level
  `m + j` the diagonal germ lies in `germ s_j`.  With `s_k = 2^k − 1` the diagonal shift is
  `t_m = 2^{m+1} − m − 2`, so `V_m = N(2^{m+1} − 2) ∩ C̃` shrinks fast, but it is a germ of
  neighbourhoods and the text's germs are "up to shrinking" anyway.  So the text's statement holds
  as written, and the `k`-dependent reading (Findings Chapter 3, item 2) was only a limitation of
  the earlier formal statements.
* **`f` versus `B`.**  The text's hypothesis is on `f = w − B`; the project's working-form theorems
  take it on `B`.  They are equivalent (`isSckGerm_contractionMap_iff`: `f = pr₂ − B`, a difference
  with an sc-operator).
* **Any representative.**  The text's "its solution germ" is a germ:
  `theorem_3_35_of_isSc0ContractionGerm_preprint` takes an arbitrary representative `(V, δ)`; it agrees
  with the constructed `sol` on `V₀ ∩ N₀ ∩ {δ ∈ O₀}` (`IsSc0ContractionGerm.exists_eq_sol`), which
  is where `V'` is cut down to.  The condition `(a, δ(a)) ∈ U₀` of a solution germ is not needed
  for this.
* **Lemma 3.3.4 (preprint 3.31) and Definition 3.3.1 (preprint 3.28).**  The text asserts that `f⁽¹⁾` is an sc⁰-contraction germ,
  i.e. Definition 3.3.1 (preprint 3.28) for `B⁽¹⁾(v, b, u, w) = (B(v, u), DB(v, δ(v))(b, w))`: an `ε`-contraction
  for every `ε` near `0` on every level.  Its second component needs the smallness
  `|D₂B(a, w)|_m ≤ ε` near `0` on level `m` (Lemma 3.1.9 (preprint 3.9), which the text states on all levels), and
  `δ_{m+1}(v)` small for `v` small (continuity of `δ_m` at `0`).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold


/-- For the constant structure of a finite-dimensional `P`: the germ `(u ∩ C̃)_m` of an open
`u ∋ 0`. -/
def ScNbhdGerm.ofOpen {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {Ct : Set P} (hC : IsQuadrantLike (ScBanach.const P) Ct) {u : Set P} (hu : IsOpen u)
    (h0 : (0 : P) ∈ u) : ScNbhdGerm (ScBanach.const P) Ct where
  U _ := u ∩ Ct
  nested _ _ hx := hx
  zero_mem _ := ⟨h0, hC.zero_mem⟩
  relOpen _ := ⟨u, hu, by rw [ScBanach.const_lvlSet]⟩

@[simp] lemma ScNbhdGerm.ofOpen_U {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {Ct : Set P} (hC : IsQuadrantLike (ScBanach.const P) Ct) {u : Set P}
    (hu : IsOpen u) (h0 : (0 : P) ∈ u) (m : ℕ) : (ScNbhdGerm.ofOpen hC hu h0).U m = u ∩ Ct := rfl

/-! ### Locality of sc^k in the levels -/

/-- **Locality of sc^k in the levels** (round-trip items V3.31, V3.32, `isSckGerm_of_levels`):
`f` is an sc^k-germ on `G'` as soon as for every `j` it is an sc^j-germ on some germ `G_j`
containing `G'` on the levels `≥ j` (`G'_{m+j} ⊆ (G_j)_{m+j}` for all `m`).  The `j`-th iterated
tangent germ `T^j G'` only involves the levels `≥ j` of `G'`. -/
theorem isSckGerm_of_levels : ∀ (k : ℕ) {E F : ScBanach} {C : Set (E 0)},
    IsQuadrantLike E C → ∀ (G' : ScNbhdGerm E C) (f : E 0 → F 0),
    (∀ j : ℕ, ∃ Gj : ScNbhdGerm E C, (∀ m, G'.U (m + j) ⊆ Gj.U (m + j)) ∧ IsSckGerm j Gj f) →
    IsSckGerm k G' f
  | 0, _, _, _, _, G', f, hG => by
    obtain ⟨G0, hsub, h0⟩ := hG 0
    exact IsSc0Germ.mono (h0 : IsSc0Germ G0 f) fun m => hsub m
  | k + 1, E, F, C, hC, G', f, hG => by
    obtain ⟨G0, hsub0, h0⟩ := hG 0
    obtain ⟨G1, hsub1, h1⟩ := hG 1
    obtain ⟨D, hD⟩ := (h1 : IsSckGerm (0 + 1) G1 f).1
    have hsub1' : ∀ m, G'.U (m + 1) ⊆ G1.U (m + 1) := hsub1
    have hG'1 : IsSc1Germ G' f :=
      ⟨D, { isSc0 := IsSc0Germ.mono (h0 : IsSc0Germ G0 f) fun m => hsub0 m
            hasFDerivWithinAt := fun x hx =>
              (hD.hasFDerivWithinAt x (hsub1' 0 hx)).mono (hsub1' 0)
            tangent_isSc0 := hD.tangent_isSc0.mono fun m _ hp =>
              (ScNbhdGerm.mem_tangent_U _).2 (hsub1' m ((ScNbhdGerm.mem_tangent_U _).1 hp)) }⟩
    refine ⟨hG'1, isSckGerm_of_levels k hC.tangentSet G'.tangent (tangentMapGerm G' f)
      fun j => ?_⟩
    obtain ⟨Gj, hsubj, hj⟩ := hG (j + 1)
    let K := Gj.inter G'
    have hK : IsSckGerm (j + 1) K f := IsSckGerm.mono hC (fun m _ hx => hx.1) hj
    have hKG' : ∀ m, K.U m ⊆ G'.U m := fun m _ hx => hx.2
    refine ⟨K.tangent, fun m p hp => ?_, ?_⟩
    · exact (ScNbhdGerm.mem_tangent_U _).2
        ⟨hsubj m ((ScNbhdGerm.mem_tangent_U _).1 hp), (ScNbhdGerm.mem_tangent_U _).1 hp⟩
    · exact IsSckGerm.congr hC.tangentSet (hG'1.tangentMapGerm_mono hC hKG') hK.2

/-- **Locality of sc-smoothness in the levels**: `f` is an sc-smooth germ on `G'` if for every `j`
it is sc^j on a germ containing `G'` on the levels `≥ j` (round-trip items V3.31, V3.32). -/
theorem isScSmoothGerm_of_levels {E F : ScBanach} {C : Set (E 0)} (hC : IsQuadrantLike E C)
    (G' : ScNbhdGerm E C) (f : E 0 → F 0)
    (hG : ∀ j : ℕ, ∃ Gj : ScNbhdGerm E C, (∀ m, G'.U (m + j) ⊆ Gj.U (m + j)) ∧ IsSckGerm j Gj f) :
    IsScSmoothGerm G' f :=
  fun k => isSckGerm_of_levels k hC G' f hG

/-! ### The diagonal germ of a contraction germ -/

namespace ContractionGerm

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P} (𝒞 : ContractionGerm P Ct W)
  (hC : IsQuadrantLike (ScBanach.const P) Ct)

/-- The **diagonal germ** `V_m = N(m + t_m) ∩ C̃` of `0` in `C̃`, for a nondecreasing shift `t`. -/
def germDiag (t : ℕ → ℕ) (ht : ∀ m, t m ≤ t (m + 1)) : ScNbhdGerm (ScBanach.const P) Ct where
  U m := 𝒞.N (m + t m) ∩ Ct
  nested m a ha := ⟨𝒞.N_anti_le (by have := ht m; omega) ha.1, ha.2⟩
  zero_mem m := ⟨𝒞.N_zero _, hC.zero_mem⟩
  relOpen m := ⟨𝒞.N (m + t m), 𝒞.N_open _, by rw [ScBanach.const_lvlSet]⟩

@[simp] lemma germDiag_U (t : ℕ → ℕ) (ht : ∀ m, t m ≤ t (m + 1)) (m : ℕ) :
    (𝒞.germDiag hC t ht).U m = 𝒞.N (m + t m) ∩ Ct := rfl

/-- The diagonal germ lies in `germ 0 = (N m ∩ C̃)_m`, so the solution germ property restricts
to it. -/
lemma isSolutionGerm_germDiag (t : ℕ → ℕ) (ht : ∀ m, t m ≤ t (m + 1)) :
    𝒞.IsSolutionGerm (𝒞.germDiag hC t ht) 𝒞.sol := by
  have h := 𝒞.isSolutionGerm_germ hC 0
  have hsub : ∀ m, (𝒞.germDiag hC t ht).U m ⊆ (𝒞.germ hC 0).U m :=
    fun m a ha => ⟨𝒞.N_anti_le (by omega) ha.1, ha.2⟩
  exact ⟨h.isSc0.mono hsub, h.zero, fun m a ha => h.mem_G m a (hsub m ha),
    fun a ha => h.fixed a (hsub 0 ha)⟩

/-- The partial sums `t_m = Σ_{j ≤ m} s_j` of a sequence of shifts. -/
def diagShift (s : ℕ → ℕ) (m : ℕ) : ℕ := ∑ j ∈ Finset.range (m + 1), s j

/-- The partial sums are nondecreasing. -/
lemma diagShift_succ (s : ℕ → ℕ) (m : ℕ) : diagShift s m ≤ diagShift s (m + 1) := by
  unfold diagShift
  rw [Finset.sum_range_succ _ (m + 1)]
  omega

/-- `s_j ≤ t_m` for `j ≤ m`. -/
lemma le_diagShift (s : ℕ → ℕ) {j m : ℕ} (hjm : j ≤ m) : s j ≤ diagShift s m :=
  Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hjm))

/-- **The diagonal germ** (round-trip items V3.31, V3.32): if for every `k` the solution germ is
sc^k on `germ s_k = (N(m + s_k) ∩ C̃)_m`, then it is an sc-smooth germ on the one germ
`V_m = N(m + Σ_{j ≤ m} s_j) ∩ C̃`.  On level `m + j` this germ lies in `germ s_j`, so
`isSckGerm_of_levels` applies. -/
theorem isScSmoothGerm_germDiag {s : ℕ → ℕ} (hs : ∀ k, IsSckGerm k (𝒞.germ hC (s k)) 𝒞.sol) :
    IsScSmoothGerm (𝒞.germDiag hC (diagShift s) (diagShift_succ s)) 𝒞.sol :=
  isScSmoothGerm_of_levels hC _ _ fun j =>
    ⟨𝒞.germ hC (s j), fun m a ha =>
      ⟨𝒞.N_anti_le (by have := le_diagShift s (show j ≤ m + j by omega); omega) ha.1, ha.2⟩,
      hs j⟩

/-- **Corollary 3.3.7 (preprint 3.34), "in particular, `δ` is sc-smooth at the smooth point `0`"**, on one germ
(round-trip item V3.31): if the working-form sc⁰-contraction germ is sc-smooth, its solution germ
`δ = sol` is an sc-smooth germ (`IsScSmoothGerm`: sc^k for **every** `k` on the **same** germ) on
the diagonal germ `V_m = N(m + t_m) ∩ C̃` for some nondecreasing `t`, and is a solution germ there.
This strengthens `theorem_3_3_6_smooth` and `corollary_3_3_7`, where the germ depends on `k`. -/
theorem _root_.Polyfold.corollary_3_3_7_isScSmoothGerm (hB : IsScSmoothGerm 𝒞.G 𝒞.B) :
    ∃ (t : ℕ → ℕ) (ht : ∀ m, t m ≤ t (m + 1)),
      𝒞.IsSolutionGerm (𝒞.germDiag hC t ht) 𝒞.sol ∧
        IsScSmoothGerm (𝒞.germDiag hC t ht) 𝒞.sol := by
  choose s hs using fun k => theorem_3_3_6_smooth 𝒞 hC hB k
  exact ⟨diagShift s, diagShift_succ s, 𝒞.isSolutionGerm_germDiag hC _ _,
    𝒞.isScSmoothGerm_germDiag hC fun k => (hs k).2⟩

/-- **Theorem 3.35, second sentence, on one germ** (round-trip item V3.32): for `C̃` a
finite-dimensional partial quadrant, if the working-form sc⁰-contraction germ is sc-smooth, so is
its solution germ — sc^k for every `k` on one germ `V_m = N(m + t_m) ∩ C̃`.  Strengthens
`theorem_3_35_smooth_preprint` (a `k`-dependent germ). -/
theorem _root_.Polyfold.theorem_3_35_isScSmoothGerm_preprint (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (hB : IsScSmoothGerm 𝒞.G 𝒞.B) :
    ∃ (t : ℕ → ℕ) (ht : ∀ m, t m ≤ t (m + 1)),
      𝒞.IsSolutionGerm (𝒞.germDiag hC.isQuadrantLike t ht) 𝒞.sol ∧
        IsScSmoothGerm (𝒞.germDiag hC.isQuadrantLike t ht) 𝒞.sol :=
  corollary_3_3_7_isScSmoothGerm 𝒞 hC.isQuadrantLike hB

end ContractionGerm

/-! ### Theorem 3.35 for Definition 3.3.1 (preprint 3.28) and any representative of the solution germ -/

section TextForm

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

/-- **`f = w − B(a, w)` is of class sc^k iff `B` is** (the text's hypotheses are on `f`, the
project's working-form theorems on `B`): `f = pr₂ − B` and `B = pr₂ − f`, differences with the
sc-operator `pr₂` (round-trip items V3.28, V3.31, V3.32). -/
theorem isSckGerm_contractionMap_iff {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)}
    {B : P × W 0 → W 0} {k : ℕ} (hCG : IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ univ)) :
    IsSckGerm k G (contractionMap B) ↔ IsSckGerm k G B := by
  let sub : ScOperator (W.prod W) W :=
    { lvl := fun m => ContinuousLinearMap.fst ℝ (W m) (W m) - ContinuousLinearMap.snd ℝ (W m) (W m)
      incl_comm := fun m x => by
        change W.incl m (x.1 - x.2) = W.incl m x.1 - W.incl m x.2
        exact map_sub _ _ _ }
  have h2 : IsSckGerm k G ((ScBanach.sndOp (ScBanach.const P) W) 0) :=
    ScOperator.isSckGerm k _ G hCG
  constructor
  · intro hk
    refine IsSckGerm.congr hCG (fun p _ => ?_) ((IsSckGerm.pair hCG h2 hk).operator_comp hCG sub)
    change p.2 - (p.2 - B p) = B p
    abel
  · intro hk
    exact IsSckGerm.congr hCG (fun p _ => rfl) ((IsSckGerm.pair hCG h2 hk).operator_comp hCG sub)

namespace IsSc0ContractionGerm

variable {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
  (h : IsSc0ContractionGerm Ct G B)

include h in
/-- **Any representative of the solution germ is `sol` near `0`** (uniqueness in Theorem 3.3.2 (preprint 3.29)):
if `δ` is an sc⁰-germ on `V` with `δ(0) = 0` and `f(a, δ(a)) = 0` on `V₀`, then `δ = sol` (the
solution of the working form `h.toContractionGerm`) on `V₀ ∩ N₀ ∩ u` for an open `u ∋ 0` (namely
`u` with `u ∩ V₀ = δ⁻¹(O₀) ∩ V₀`). -/
lemma exists_eq_sol {V : ScNbhdGerm (ScBanach.const P) Ct} {δ : P → W 0} (hδ0 : IsSc0Germ V δ)
    (hδzero : δ 0 = 0) (hδsol : ∀ a ∈ V.U 0, contractionMap B (a, δ a) = 0) :
    ∃ u : Set P, IsOpen u ∧ (0 : P) ∈ u ∧
      ∀ a ∈ V.U 0, a ∈ h.toContractionGerm.N 0 → a ∈ u → δ a = h.toContractionGerm.sol a := by
  set 𝒞 := h.toContractionGerm with h𝒞
  have hcont : ContinuousOn δ (V.U 0) :=
    (hδ0.continuousOn 0).congr fun a _ => (levelMap_zero δ a).symm
  obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hcont) (𝒞.O 0) (𝒞.O_open 0)
  have hu0 : (0 : P) ∈ u := by
    have : (0 : P) ∈ δ ⁻¹' 𝒞.O 0 ∩ V.U 0 :=
      ⟨by rw [Set.mem_preimage, hδzero]; exact 𝒞.zero_mem_O 0, V.zero_mem 0⟩
    rw [hueq] at this
    exact this.1
  refine ⟨u, hu, hu0, fun a haV haN hau => ?_⟩
  have haC : a ∈ Ct := by
    have := V.U_subset 0 haV
    rwa [ScBanach.const_lvlSet] at this
  have hO : δ a ∈ 𝒞.O 0 := by
    have : a ∈ u ∩ V.U 0 := ⟨hau, haV⟩
    rw [← hueq] at this
    exact this.1
  have hfix : 𝒞.B (a, δ a) = δ a := by
    have := hδsol a haV
    change δ a - B (a, δ a) = 0 at this
    exact (sub_eq_zero.1 this).symm
  exact 𝒞.eq_sol ⟨haN, haC⟩ hO hfix

end IsSc0ContractionGerm

/-- **Theorem 3.35 (and Corollary 3.34's "in particular") in the text's form** (round-trip items
V3.31, V3.32): let `f(a, w) = w − B(a, w)` be an sc⁰-contraction germ (Definition 3.3.1 (preprint 3.28)) on a
quadrant-like `C̃` (e.g. a finite-dimensional partial quadrant), and let `(V, δ)` be **any**
representative of its solution germ: an sc⁰-germ with `δ(0) = 0` and `f(a, δ(a)) = 0` on `V₀`.
(1) If `f` is of class sc^k, then `δ` is an sc^k-germ on some germ `V' ⊆ V`.
(2) If `f` is sc-smooth, then `δ` is an sc-smooth germ on **one** germ `V' ⊆ V` (sc^k for every
`k` on the same `V'`; the diagonal germ of `ContractionGerm.isScSmoothGerm_germDiag`). -/
theorem theorem_3_35_of_isSc0ContractionGerm_preprint (hC : IsQuadrantLike (ScBanach.const P) Ct)
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
    (h : IsSc0ContractionGerm Ct G B) {V : ScNbhdGerm (ScBanach.const P) Ct} {δ : P → W 0}
    (hδ0 : IsSc0Germ V δ) (hδzero : δ 0 = 0)
    (hδsol : ∀ a ∈ V.U 0, contractionMap B (a, δ a) = 0) :
    (∀ k, IsSckGerm k G (contractionMap B) →
      ∃ V' : ScNbhdGerm (ScBanach.const P) Ct, (∀ m, V'.U m ⊆ V.U m) ∧ IsSckGerm k V' δ) ∧
    (IsScSmoothGerm G (contractionMap B) →
      ∃ V' : ScNbhdGerm (ScBanach.const P) Ct, (∀ m, V'.U m ⊆ V.U m) ∧ IsScSmoothGerm V' δ) := by
  have hCG : IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ univ) := hC.paramProd W
  set 𝒞 := h.toContractionGerm with h𝒞
  obtain ⟨u, hu, hu0, hagree⟩ := h.exists_eq_sol hδ0 hδzero hδsol
  -- `V' = V ∩ H ∩ (u ∩ C̃)` for a germ `H` of the form `(N(m + t_m) ∩ C̃)_m`, `t 0 ≥ 0`
  have key : ∀ (H : ScNbhdGerm (ScBanach.const P) Ct), (∀ a ∈ H.U 0, a ∈ 𝒞.N 0) →
      EqOn 𝒞.sol δ ((V.inter (H.inter (ScNbhdGerm.ofOpen hC hu hu0))).U 0) :=
    fun H hH a ha => (hagree a ha.1 (hH a ha.2.1) ha.2.2.1).symm
  have hsub : ∀ (H : ScNbhdGerm (ScBanach.const P) Ct) m,
      (V.inter (H.inter (ScNbhdGerm.ofOpen hC hu hu0))).U m ⊆ H.U m := fun _ _ _ ha => ha.2.1
  refine ⟨fun k hk => ?_, fun hf => ?_⟩
  · have hB : IsSckGerm k 𝒞.G 𝒞.B := (isSckGerm_contractionMap_iff hCG).1 hk
    obtain ⟨s, -, hs⟩ := theorem_3_3_6 𝒞 hC hB
    refine ⟨V.inter ((𝒞.germ hC s).inter (ScNbhdGerm.ofOpen hC hu hu0)), fun m a ha => ha.1, ?_⟩
    exact IsSckGerm.congr hC (key _ fun a ha => 𝒞.N_anti_le (by omega) ha.1)
      (IsSckGerm.mono hC (hsub _) hs)
  · have hB : IsScSmoothGerm 𝒞.G 𝒞.B := fun k => (isSckGerm_contractionMap_iff hCG).1 (hf k)
    obtain ⟨t, ht, -, hsm⟩ := corollary_3_3_7_isScSmoothGerm 𝒞 hC hB
    refine ⟨V.inter ((𝒞.germDiag hC t ht).inter (ScNbhdGerm.ofOpen hC hu hu0)),
      fun m a ha => ha.1, fun k => ?_⟩
    exact IsSckGerm.congr hC (key _ fun a ha => 𝒞.N_anti_le (by omega) ha.1)
      (IsSckGerm.mono hC (hsub _) (hsm k))

end TextForm

/-! ### Lemma 3.3.4 (preprint 3.31): `f⁽¹⁾` is an sc⁰-contraction germ in the sense of Definition 3.3.1 (preprint 3.28) -/

section NextContraction

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

namespace ContractionGerm

variable (𝒞 : ContractionGerm P Ct W) (hC : IsQuadrantLike (ScBanach.const P) Ct)
  {D : (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] W 0}
  (hB : IsSc1GermWith 𝒞.G 𝒞.B D)

/-- **Lemma 3.3.4 (preprint 3.31), "`f⁽¹⁾` is an sc⁰-contraction germ"** in the sense of **Definition 3.3.1 (preprint 3.28)**
(round-trip item V3.28): if the working-form germ `f = w − B(a, w)` satisfies Definition 3.3.1 (preprint 3.28)
(`ε`-contraction for every `ε > 0` on every level, e.g. `𝒞 = h.toContractionGerm`), then so does
`f⁽¹⁾(v, b, u, w) = (u − B(v, u), w − DB(v, δ(v))(b, w))` on its germ `nextG s`, for every `s`.
The project's `ContractionGerm.next` only records a `1/2`-contraction on explicit regions.  Proof:
on level `m` the first component is Definition 3.3.1 (preprint 3.28) for `B` on level `m + 1`; the second is
`|D₂B(v, δ_{m+1}(v))ζ|_m ≤ ε|ζ|_m` (`exists_norm_levelDeriv_snd_le`), using the continuity of
`δ_m` at `0`. -/
theorem isSc0ContractionGerm_next (h : IsSc0ContractionGerm Ct 𝒞.G 𝒞.B) (s : ℕ) :
    IsSc0ContractionGerm (Ct ×ˢ univ) (𝒞.next hC hB s).G (𝒞.next hC hB s).B := by
  refine ⟨(𝒞.next hC hB s).isSc0, (𝒞.next hC hB s).B_zero, fun ε hε m => ?_⟩
  obtain ⟨r₁, hr₁, H₁⟩ := h.contraction ε hε (m + 1)
  obtain ⟨r₂, hr₂, H₂⟩ := IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le hC h hB hε m
  -- continuity of `δ_m = fixLvl m` at `0`
  have h0m : (0 : P) ∈ 𝒞.N m ∩ Ct := ⟨𝒞.N_zero m, hC.zero_mem⟩
  have hfix0 : 𝒞.fixLvl m 0 = 0 :=
    (𝒞.eq_fixLvl m h0m (𝒞.zero_mem_O m) (h.levelB_zero_eq m)).symm
  have hcf := 𝒞.continuousOn_fixLvl m 0 h0m
  rw [Metric.continuousWithinAt_iff] at hcf
  obtain ⟨ρ, hρ, Hρ⟩ := hcf r₂ hr₂
  obtain ⟨ρN, hρN, HN⟩ := Metric.isOpen_iff.1 (𝒞.N_open (m + 1 + s)) 0 (𝒞.N_zero (m + 1 + s))
  obtain ⟨ρO, hρO, HO⟩ := Metric.isOpen_iff.1 (𝒞.O_open (m + 1)) 0 (𝒞.zero_mem_O (m + 1))
  refine ⟨min (min r₁ r₂) (min ρ (min ρN ρO)), by positivity, ?_⟩
  rintro ⟨v, b⟩ ⟨hvC, -⟩ har ⟨u₁, w₁⟩ ⟨u₂, w₂⟩ hw₁ hw₂
  have hvr : ‖v‖ < min (min r₁ r₂) (min ρ (min ρN ρO)) :=
    (norm_fst_le ((v, b) : P × P)).trans_lt har
  have hu₁r : ‖u₁‖ < min (min r₁ r₂) (min ρ (min ρN ρO)) :=
    (norm_fst_le ((u₁, w₁) : W (m + 1) × W m)).trans_lt hw₁
  have hu₂r : ‖u₂‖ < min (min r₁ r₂) (min ρ (min ρN ρO)) :=
    (norm_fst_le ((u₂, w₂) : W (m + 1) × W m)).trans_lt hw₂
  simp only [lt_min_iff] at hvr hu₁r hu₂r
  have hvN : v ∈ 𝒞.N (m + 1 + s) := HN (by rw [Metric.mem_ball, dist_zero_right]; exact hvr.2.2.1)
  have hv : v ∈ 𝒞.N (m + 1) ∩ Ct := ⟨𝒞.N_anti_le (by omega) hvN, hvC⟩
  have hu₁O : u₁ ∈ 𝒞.O (m + 1) :=
    HO (by rw [Metric.mem_ball, dist_zero_right]; exact hu₁r.2.2.2)
  have hu₂O : u₂ ∈ 𝒞.O (m + 1) :=
    HO (by rw [Metric.mem_ball, dist_zero_right]; exact hu₂r.2.2.2)
  refine ⟨⟨𝒞.mem_G (m + 1) v hv u₁ hu₁O, hvN⟩, ?_⟩
  change ‖levelB (𝒞.nextB D) m ((v, b), (u₁, w₁)) - levelB (𝒞.nextB D) m ((v, b), (u₂, w₂))‖ ≤
    ε * ‖(((u₁, w₁) : W.tangent m) - (u₂, w₂))‖
  rw [𝒞.levelB_next hB hv hu₁O w₁, 𝒞.levelB_next hB hv hu₂O w₂]
  have h1 := (H₁ v hvC hvr.1.1 u₁ u₂ hu₁r.1.1 hu₂r.1.1).2
  have hincl : ‖W.incl m (𝒞.fixLvl (m + 1) v)‖ < r₂ := by
    rw [𝒞.incl_fixLvl m hv]
    have := Hρ (x := v) ⟨𝒞.N_anti m hv.1, hvC⟩ (by rw [dist_zero_right]; exact hvr.2.1)
    rwa [hfix0, dist_zero_right] at this
  have h2 : ‖𝒞.Lop (D := D) m v (b, w₁) - 𝒞.Lop (D := D) m v (b, w₂)‖ ≤ ε * ‖w₁ - w₂‖ := by
    rw [← map_sub]
    have : ((b, w₁) : (ScBanach.paramProd P W) m) - (b, w₂) = ((0 : P), w₁ - w₂) := by
      ext <;> simp
    rw [this]
    have hnorm : ‖(ScBanach.paramProd P W).incl m
        ((v, 𝒞.fixLvl (m + 1) v) : (ScBanach.paramProd P W) (m + 1))‖ < r₂ := by
      rw [ScBanach.paramProd_incl, Prod.norm_def]
      exact max_lt hvr.1.2 hincl
    exact H₂ _ (𝒞.mem_G_fixLvl (m + 1) hv) hnorm (w₁ - w₂)
  change max ‖levelB 𝒞.B (m + 1) (v, u₁) - levelB 𝒞.B (m + 1) (v, u₂)‖
      ‖𝒞.Lop (D := D) m v (b, w₁) - 𝒞.Lop (D := D) m v (b, w₂)‖ ≤
    ε * max ‖u₁ - u₂‖ ‖w₁ - w₂‖
  refine max_le (h1.trans ?_) (h2.trans ?_) <;> gcongr
  · exact le_max_left _ _
  · exact le_max_right _ _

end ContractionGerm

end NextContraction

end Polyfold
