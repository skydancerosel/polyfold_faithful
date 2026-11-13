import Polyfold.Chapter5.P3R_Reflexive2021
import Polyfold.Chapter5.Compactness
import Polyfold.Chapter5.Transversality
import Polyfold.Chapter3.NonVacuity
import Polyfold.Chapter3.TameGermsG
import Polyfold.Chapter2.Metrizable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.2, pp. 214–216:
**Definition 5.2.6, Proposition 5.2.7, Theorem 5.2.8, Remarks 5.2.9 and 5.2.10**
(2017: Definition 5.6, Proposition 5.3, Theorem 5.4, Remarks 5.1 and 5.2).

# Reflexive local compactness

## The text, paraphrased

With `N(y) = ∞` for `y ∉ Y_{0,1}`: (Definition 5.2.6) for a strong bundle with reflexive
`(0, 1)`-fibres and a regularizing sc-smooth section `f`, `f` has the **reflexive local
compactness property** if for every reflexive auxiliary norm `N` and every `x ∈ X` there is an open
`U(x)` with `cl_X {q ∈ U(x) | N(f(q)) ≤ 1}` compact (printed `N(f(x))`).  (Proposition 5.2.7) If `f`
is moreover reflexive locally compact, then (1) every `x ∈ X₀ \ X₁` has, for every reflexive
auxiliary norm, a neighbourhood on which `N(f(q)) > 1`; (2) the same holds at every `x` with
`N(f(x)) > 1`.  Proof of (2): a sequence `x_k → x` with `N(f(x_k)) ≤ 1` has a subsequence with
`f(x_k)` mixed convergent to some `h`; then `N(h) ≤ 1` and `f(x) = h`.  (After the proof) For `U`
open, `cl_X {x ∈ U | N(f(x)) ≤ 1} ⊆ {x ∈ cl_X(U) | N(f(x)) ≤ 1}`.  (Theorem 5.2.8) Over a tame
M-polyfold with reflexive `(0, 1)`-fibres, let `f` be sc-Fredholm with compact solution set and the
reflexive local compactness property, `N` a reflexive auxiliary norm, `U_∂` an open neighbourhood in
`∂X` of `S_∂ = {x ∈ ∂X | f(x) = 0}` with `cl {x ∈ U_∂ | N(f(x)) ≤ 1}` compact.  Then there is an
open `U ⊇ S` with `U ∩ ∂X = U_∂` and `cl {x ∈ U | N(f(x)) ≤ 1}` compact.  (Remark 5.2.9) This
says that `(U_∂, N)` controlling compactness on the boundary extends to `(U, N)`.  (Remark 5.2.10)
The theorem is used in inductive perturbation arguments (SFT).

## What is formalized

* `StrongBundle.HasReflexiveLocalCompactness` (**Definition 5.2.6**).
* `StrongBundle.exists_nhds_not_auxLe` (**Proposition 5.2.7 (2)** for every continuous section;
  reflexive local compactness and regularity are not used),
  `StrongBundle.not_auxLe_of_not_mem_levelSet`
  (the step of (1): a regularizing section has `N(f(x)) = ∞` off `X₁`),
  **`Polyfold.proposition_5_2_7`** (the book form, both parts).
* `StrongBundle.isClosed_setOf_auxLe` (`{x | N(f(x)) ≤ 1}` is closed) and
  `StrongBundle.closure_auxLe_subset` (the remark after the proof of Proposition 5.2.7).
* `Polyfold.theorem_5_2_8_of_continuous` (**Theorem 5.2.8** for every continuous section with
  compact solution set, over any M-polyfold) and **`Polyfold.theorem_5_2_8`** (the book form:
  tame, sc-Fredholm).  Remark 5.2.9 is the statement of Theorem 5.2.8 in words; Remark 5.2.10 has
  no mathematical content.
* Satisfiability: on the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` every section is reflexive locally compact
  (`TrivialBundle.hasReflexiveLocalCompactness_bundle`), and `TrivialBundle.theorem_5_2_8_witness`
  exhibits all hypotheses of the book form of Theorem 5.2.8 at once (the graph section of `id`).

## What the text leaves implicit, and the choices made

* `N(f(x)) ≤ 1` with the convention `N = ∞` off `Y_{0,1}` is the project's `B.AuxLe N (f x) 1`
  (Definition 5.2.1); `N(f(x)) > 1` is its negation.  In Definition 5.2.6 the printed
  `N(f(x)) ≤ 1` inside `{q ∈ U(x) | …}` is read as `N(f(q)) ≤ 1`.
* Definition 5.2.6 is stated as the compactness property alone; its standing assumptions (reflexive
  fibres, `f` sc-smooth and regularizing) are hypotheses of the statements that use it.
* **Proposition 5.2.7 (2)** only uses that `f` is a continuous section, that the fibres are
  reflexive and that `N` is a reflexive auxiliary norm (the sequence argument needs `X` first
  countable: an M-polyfold is metrizable, Theorem 2.3.10).  The mixed convergent subsequence is
  `exists_mixedTendsto_subseq` (bounded fibre parts in a reflexive chart, Lemma 5.1.2 and weak
  sequential compactness); "`h_k → h` in `Y_{0,0}`" is `MixedTendsto.tendsto_oneVal`.
  (1) uses that `f` is regularizing: `f(x) ∈ Y_{0,1}` forces `x ∈ X₁`.
* **Theorem 5.2.8.**  "`U_∂` open in `∂X`" is read as `U_∂ = W ∩ ∂X` for some open `W ⊆ X`, and
  closures are in `X`.  The proof follows the text: `{N∘f ≤ 1}` is closed (Proposition 5.2.7 (2)),
  so the set `Ũ` of the text may be taken as `U(x̄₁) ∪ … ∪ U(x̄_ℓ) ∪ {N∘f > 1}`; the solutions off
  `Ũ` are interior points (`∂X` is closed) and get finitely many neighbourhoods inside `X \ ∂X`;
  `V = W ∪ (X \ ∂X)`.  Tameness and the sc-Fredholm property are not used; only continuity of `f`,
  compactness of the solution set and the reflexive local compactness for the given `N`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundle

variable {B : StrongBundle PX P} {f : X → Y}

/-! ### Definition 5.2.6 -/

variable (B) in
/-- **2021 Definition 5.2.6, p. 214** (2017: Definition 5.6): the section `f` has the **reflexive
local compactness property**: for every reflexive auxiliary norm `N` and every `x ∈ X` there is an
open `U(x) ∋ x` (on level 0) with `cl_X {q ∈ U(x) | N(f(q)) ≤ 1}` compact. -/
def HasReflexiveLocalCompactness (f : X → Y) : Prop :=
  ∀ N : B.One → ℝ, B.IsReflexiveAuxNorm N → ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    IsCompact (closure {q ∈ U | B.AuxLe N (f q) 1})

/-! ### Proposition 5.2.7 -/

/-- **Proposition 5.2.7 (2), for continuous sections**: if `N(f(x)) > 1` (including
`f(x) ∉ Y_{0,1}`)
for a reflexive auxiliary norm `N`, then `N(f(q)) > 1` on a neighbourhood of `x`. -/
theorem exists_nhds_not_auxLe (hB : B.HasReflexiveFibers) (hf : IsSection P f)
    (hfc : Continuous f) {N : B.One → ℝ} (hN : B.IsReflexiveAuxNorm N) {x : X}
    (hx : ¬ B.AuxLe N (f x) 1) : ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ q ∈ V, ¬ B.AuxLe N (f q) 1 := by
  by_contra H
  push Not at H
  have hcl : x ∈ closure {q | B.AuxLe N (f q) 1} := by
    rw [mem_closure_iff]
    intro V hV hxV
    obtain ⟨q, hq, hq'⟩ := H V hV hxV
    exact ⟨q, hq, hq'⟩
  have := PX.metrizableSpace
  obtain ⟨xs, hxs, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  choose h1 hle using hxs
  set w : ℕ → B.One := fun k => B.oneMk (f (xs k)) (h1 k) with hw
  have hPw : Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 x) :=
    hlim.congr fun k => (hf (xs k)).symm
  obtain ⟨φ, hφ, y, -, hm⟩ :=
    exists_mixedTendsto_subseq hB hN.toIsAuxNorm hPw (r := 1) (Eventually.of_forall hle)
  have hY := hm.tendsto_oneVal
  have hfx : Tendsto (fun k => f (xs (φ k))) atTop (𝓝 (f x)) :=
    (hfc.tendsto x).comp (hlim.comp hφ.tendsto_atTop)
  have hyfx : B.oneVal y = f x := tendsto_nhds_unique hY hfx
  have hNy : N y ≤ 1 := hN.le_of_frequently_le hm (Frequently.of_forall fun k => hle (φ k))
  apply hx
  refine ⟨hyfx ▸ B.oneVal_mem y, ?_⟩
  have e : B.oneMk (f x) (hyfx ▸ B.oneVal_mem y) = y :=
    B.oneVal_injective (by rw [oneVal_oneMk, hyfx])
  rw [e]; exact hNy

/-- `Y_{0,1} ⊆ Y_{0,1}` in the double filtration: `Y_{0,1} = Y[1] ⊆ Y_{0,1}` (the base component is
on level 0). -/
lemma oneSet_subset_doubleLevel : B.oneSet ⊆ B.doubleLevel 0 1 :=
  fun _ hy c hc hs => ⟨⟨_, rfl⟩, hy c hc hs⟩

/-- **The step of Proposition 5.2.7 (1)**: for a regularizing section, `N(f(x)) = ∞` (so `> 1`)
at every `x ∈ X₀ \ X₁`. -/
theorem not_auxLe_of_not_mem_levelSet
    (hreg : ∀ m, ∀ x ∈ PX.levelSet m, f x ∈ B.doubleLevel m (m + 1) → x ∈ PX.levelSet (m + 1))
    {N : B.One → ℝ} {x : X} (hx : x ∉ PX.levelSet 1) : ¬ B.AuxLe N (f x) 1 := by
  rintro ⟨h1, -⟩
  exact hx (hreg 0 x (by rw [PX.levelSet_zero]; exact mem_univ x) (oneSet_subset_doubleLevel h1))

/-- **`{x | N(f(x)) ≤ 1}` is closed** (Proposition 5.2.7 (2)). -/
theorem isClosed_setOf_auxLe (hB : B.HasReflexiveFibers) (hf : IsSection P f)
    (hfc : Continuous f) {N : B.One → ℝ} (hN : B.IsReflexiveAuxNorm N) :
    IsClosed {x | B.AuxLe N (f x) 1} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨V, hVo, hxV, hV⟩ := exists_nhds_not_auxLe hB hf hfc hN hx
  exact ⟨V, fun q hq => hV q hq, hVo, hxV⟩

/-- **The remark after Proposition 5.2.7**: for every `U`,
`cl_X {x ∈ U | N(f(x)) ≤ 1} ⊆ {x ∈ cl_X(U) | N(f(x)) ≤ 1}`. -/
theorem closure_auxLe_subset (hB : B.HasReflexiveFibers) (hf : IsSection P f)
    (hfc : Continuous f) {N : B.One → ℝ} (hN : B.IsReflexiveAuxNorm N) (U : Set X) :
    closure {x ∈ U | B.AuxLe N (f x) 1} ⊆ {x ∈ closure U | B.AuxLe N (f x) 1} := by
  intro x hx
  refine ⟨closure_mono (fun q hq => hq.1) hx, ?_⟩
  have := (isClosed_setOf_auxLe hB hf hfc hN).closure_subset_iff.2
    (fun q (hq : q ∈ {x ∈ U | B.AuxLe N (f x) 1}) => hq.2)
  exact this hx

end StrongBundle

open StrongBundle in
/-- **2021 Proposition 5.2.7, p. 214** (2017: Proposition 5.3): for a strong bundle with reflexive
`(0, 1)`-fibres and an sc-smooth, regularizing section `f` with the reflexive local compactness
property, and a reflexive auxiliary norm `N`: (1) every `x ∈ X₀ \ X₁` has a neighbourhood `V` with
`N(f(q)) > 1` for `q ∈ V`; (2) every `x` with `N(f(x)) > 1` has such a neighbourhood. -/
theorem proposition_5_2_7 {B : StrongBundle PX P} {f : X → Y} (hB : B.HasReflexiveFibers)
    (hf : B.IsScSmoothSection f)
    (hreg : ∀ m, ∀ x ∈ PX.levelSet m, f x ∈ B.doubleLevel m (m + 1) → x ∈ PX.levelSet (m + 1))
    (_hlc : B.HasReflexiveLocalCompactness f) {N : B.One → ℝ} (hN : B.IsReflexiveAuxNorm N) :
    (∀ x, x ∉ PX.levelSet 1 → ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ q ∈ V, ¬ B.AuxLe N (f q) 1) ∧
      (∀ x, ¬ B.AuxLe N (f x) 1 →
        ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ q ∈ V, ¬ B.AuxLe N (f q) 1) := by
  have hfc : Continuous f := continuousOn_univ.1 hf.2.continuousOn
  exact ⟨fun x hx => exists_nhds_not_auxLe hB hf.1 hfc hN (not_auxLe_of_not_mem_levelSet hreg hx),
    fun x hx => exists_nhds_not_auxLe hB hf.1 hfc hN hx⟩

open StrongBundle in
/-- **Theorem 5.2.8 for continuous sections** (the text's proof uses only continuity, a compact
solution set and the reflexive local compactness for the given `N`; no tameness): if
`U_∂ = W ∩ ∂X` (`W` open) contains `S_∂ = S ∩ ∂X` and `cl {x ∈ U_∂ | N(f(x)) ≤ 1}` is compact, there
is an open `U ⊇ S` with `U ∩ ∂X = U_∂` and `cl {x ∈ U | N(f(x)) ≤ 1}` compact. -/
theorem theorem_5_2_8_of_continuous {B : StrongBundle PX P} {f : X → Y}
    (hB : B.HasReflexiveFibers) (hf : IsSection P f) (hfc : Continuous f)
    (hS : IsCompact (solutionSet P f)) (hlc : B.HasReflexiveLocalCompactness f)
    {N : B.One → ℝ} (hN : B.IsReflexiveAuxNorm N) {Ub : Set X}
    (hUb : ∃ W : Set X, IsOpen W ∧ Ub = W ∩ PX.boundary)
    (hSUb : solutionSet P f ∩ PX.boundary ⊆ Ub)
    (hcpt : IsCompact (closure {x ∈ Ub | B.AuxLe N (f x) 1})) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧ U ∩ PX.boundary = Ub ∧
      IsCompact (closure {x ∈ U | B.AuxLe N (f x) 1}) := by
  classical
  set A : Set X := {x | B.AuxLe N (f x) 1} with hAdef
  have hA : IsClosed A := isClosed_setOf_auxLe hB hf hfc hN
  have hBd : IsClosed PX.boundary := PX.isClosed_boundary
  choose Uq hUqo hxUq hUqc using hlc N hN
  -- the boundary part: finitely many `U(x̄ᵢ)` cover `cl {x ∈ U_∂ | N(f(x)) ≤ 1}`
  obtain ⟨t, -, ht⟩ := hcpt.elim_nhds_subcover Uq fun x _ => (hUqo x).mem_nhds (hxUq x)
  set U1 : Set X := ⋃ q ∈ t, Uq q with hU1
  set Ut : Set X := U1 ∪ Aᶜ with hUt
  have hUto : IsOpen Ut :=
    (isOpen_biUnion fun q _ => hUqo q).union hA.isOpen_compl
  have hUbUt : Ub ⊆ Ut := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inl (ht (subset_closure ⟨hx, hxA⟩))
    · exact Or.inr hxA
  -- the interior solutions off `Ũ`
  set S' : Set X := solutionSet P f \ Ut with hS'
  have hS'c : IsCompact S' := hS.diff hUto
  have hS'int : ∀ x ∈ S', x ∉ PX.boundary := fun x hx hxb =>
    hx.2 (hUbUt (hSUb ⟨hx.1, hxb⟩))
  obtain ⟨t2, -, ht2⟩ := hS'c.elim_nhds_subcover (fun x => Uq x ∩ PX.boundaryᶜ) fun x hx =>
    inter_mem ((hUqo x).mem_nhds (hxUq x)) (hBd.isOpen_compl.mem_nhds (hS'int x hx))
  set U' : Set X := Ut ∪ ⋃ x ∈ t2, (Uq x ∩ PX.boundaryᶜ) with hU'
  have hU'o : IsOpen U' :=
    hUto.union (isOpen_biUnion fun x _ => (hUqo x).inter hBd.isOpen_compl)
  -- the compact set controlling `{x ∈ U' | N(f(x)) ≤ 1}`
  set T : Set X := (⋃ q ∈ t, closure {x ∈ Uq q | B.AuxLe N (f x) 1}) ∪
    ⋃ x ∈ t2, closure {y ∈ Uq x | B.AuxLe N (f y) 1} with hT
  have hTc : IsCompact T :=
    (t.isCompact_biUnion fun q _ => hUqc q).union (t2.isCompact_biUnion fun x _ => hUqc x)
  have hU'T : {x ∈ U' | B.AuxLe N (f x) 1} ⊆ T := by
    rintro x ⟨hxU', hxA⟩
    rcases hxU' with (hx1 | hx2) | hx3
    · obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.1 hx1
      exact Or.inl (mem_iUnion₂.2 ⟨q, hq, subset_closure ⟨hxq, hxA⟩⟩)
    · exact absurd hxA hx2
    · obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.1 hx3
      exact Or.inr (mem_iUnion₂.2 ⟨q, hq, subset_closure ⟨hxq.1, hxA⟩⟩)
  -- `V` with `V ∩ ∂X = U_∂`
  obtain ⟨W, hWo, rfl⟩ := hUb
  set V : Set X := W ∪ PX.boundaryᶜ with hV
  refine ⟨U' ∩ V, hU'o.inter (hWo.union hBd.isOpen_compl), ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · by_cases hxt : x ∈ Ut
      · exact Or.inl hxt
      · exact Or.inr (ht2 ⟨hx, hxt⟩)
    · by_cases hxb : x ∈ PX.boundary
      · exact Or.inl (hSUb ⟨hx, hxb⟩).1
      · exact Or.inr hxb
  · ext x
    constructor
    · rintro ⟨⟨-, hxV⟩, hxb⟩
      rcases hxV with hxW | hxb'
      · exact ⟨hxW, hxb⟩
      · exact absurd hxb hxb'
    · rintro ⟨hxW, hxb⟩
      exact ⟨⟨Or.inl (hUbUt ⟨hxW, hxb⟩), Or.inl hxW⟩, hxb⟩
  · refine hTc.of_isClosed_subset isClosed_closure ?_
    refine closure_minimal (fun x hx => hU'T ⟨hx.1.1, hx.2⟩) hTc.isClosed

open StrongBundle in
/-- **2021 Theorem 5.2.8, p. 215** (2017: Theorem 5.4; Remark 5.2.9 restates it): let `P : Y → X` be
a strong bundle over a tame M-polyfold with reflexive `(0, 1)`-fibres, `f` an sc-Fredholm section
with compact solution set `S` and the reflexive local compactness property, `N` a reflexive
auxiliary norm, and `U_∂` an open neighbourhood in `∂X` of `S_∂ = {x ∈ ∂X | f(x) = 0}` with
`cl {x ∈ U_∂ | N(f(x)) ≤ 1}` compact.  Then there is an open neighbourhood `U` of `S` with
(1) `U ∩ ∂X = U_∂` and (2) `cl {x ∈ U | N(f(x)) ≤ 1}` compact. -/
theorem theorem_5_2_8 {B : StrongBundle PX P} {f : X → Y} (_hT : PX.IsTame)
    (hB : B.HasReflexiveFibers) (hf : B.IsScFredholmSection f)
    (hS : IsCompact (solutionSet P f)) (hlc : B.HasReflexiveLocalCompactness f)
    {N : B.One → ℝ} (hN : B.IsReflexiveAuxNorm N) {Ub : Set X}
    (hUb : ∃ W : Set X, IsOpen W ∧ Ub = W ∩ PX.boundary)
    (hSUb : solutionSet P f ∩ PX.boundary ⊆ Ub)
    (hcpt : IsCompact (closure {x ∈ Ub | B.AuxLe N (f x) 1})) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧ U ∩ PX.boundary = Ub ∧
      IsCompact (closure {x ∈ U | B.AuxLe N (f x) 1}) :=
  theorem_5_2_8_of_continuous hB hf.isScSmooth.1
    (continuousOn_univ.1 hf.isScSmooth.2.continuousOn) hS hlc hN hUb hSUb hcpt

/-! ### Satisfiability on the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` -/

namespace TrivialBundle

variable {n k : ℕ}

/-- The trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` has reflexive `(0, 1)`-fibres (Definition 5.1.4): the
fibre model `ℝᵏ` is finite-dimensional. -/
theorem hasReflexiveFibers_bundle : (bundle n k).HasReflexiveFibers :=
  StrongBundle.hasReflexiveFibers_of_atlas fun c hc => by
    obtain ⟨a, rfl⟩ := hc
    exact isReflexive_of_finiteDimensional (F := Fin k → ℝ)

/-- A reflexive auxiliary norm exists on the trivial bundle (Definition 5.1.7 is satisfiable). -/
theorem exists_isReflexiveAuxNorm_bundle : ∃ N, (bundle n k).IsReflexiveAuxNorm N :=
  proposition_5_1_8_exists hasReflexiveFibers_bundle

/-- Every section of the trivial bundle has the reflexive local compactness property (Definition
5.2.6 is satisfiable): bounded balls of `ℝⁿ` have compact closure. -/
theorem hasReflexiveLocalCompactness_bundle (f : (Fin n → ℝ) → (Fin n → ℝ) × (Fin k → ℝ)) :
    (bundle n k).HasReflexiveLocalCompactness f := fun _ _ x =>
  ⟨Metric.ball x 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos,
    (isCompact_closedBall x 1).of_isClosed_subset isClosed_closure
      (closure_minimal (fun _ hq => Metric.ball_subset_closedBall hq.1) Metric.isClosed_closedBall)⟩

/-- **All hypotheses of Theorem 5.2.8 hold at once** for the graph section `x ↦ (x, x)` of
`ℝⁿ × ℝⁿ → ℝⁿ` (`ℝⁿ` is tame without boundary, `U_∂ = ∅`). -/
theorem theorem_5_2_8_witness :
    (rnPolyfold n).IsTame ∧ (bundle n n).HasReflexiveFibers ∧
      (bundle n n).IsScFredholmSection (graphSection id) ∧
      IsCompact (solutionSet (proj n n) (graphSection id)) ∧
      (bundle n n).HasReflexiveLocalCompactness (graphSection id) ∧
      (∃ N, (bundle n n).IsReflexiveAuxNorm N) ∧
      (∃ W : Set (Fin n → ℝ), IsOpen W ∧ (∅ : Set (Fin n → ℝ)) = W ∩ (rnPolyfold n).boundary) ∧
      solutionSet (proj n n) (graphSection id) ∩ (rnPolyfold n).boundary ⊆ ∅ ∧
      ∀ N, IsCompact (closure {x ∈ (∅ : Set (Fin n → ℝ)) |
        (bundle n n).AuxLe N (graphSection id x) 1}) := by
  have hbd : (rnPolyfold n).boundary = ∅ := by
    ext x
    simp only [MPolyfold.boundary, mem_ofPred_eq, rnPolyfold_degIndex, mem_empty_iff_false,
      iff_false]
    omega
  have hsol : solutionSet (proj n n) (graphSection (id : (Fin n → ℝ) → (Fin n → ℝ))) = {0} := by
    ext x
    change IsZeroAt _ _ x ↔ _
    rw [isZeroAt_graphSection_iff]; rfl
  refine ⟨rnPolyfold_isTame, hasReflexiveFibers_bundle,
    (isScFredholmSection_graphSection_wholeChart contDiff_id).isScFredholmSection, ?_,
    hasReflexiveLocalCompactness_bundle _, exists_isReflexiveAuxNorm_bundle,
    ⟨∅, isOpen_empty, (empty_inter _).symm⟩, ?_, fun N => ?_⟩
  · rw [hsol]; exact isCompact_singleton
  · rw [hbd, inter_empty]
  · have : {x ∈ (∅ : Set (Fin n → ℝ)) | (bundle n n).AuxLe N (graphSection id x) 1} = ∅ := by
      ext x; simp
    rw [this, closure_empty]; exact isCompact_empty

end TrivialBundle

end Polyfold
