import Polyfold.Chapter5.Transversality

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §5.3:
**Definition 5.3.13 (preprint 5.20)** (generalized compact homotopy), **Lemmas 5.3.16 and 5.3.17 (preprint 5.23 and 5.24)** (the two lemmas of the
proof of Theorem 5.3.15 (preprint 5.22)) *(book 2017: Definition 5.10, Lemmas 5.4 and 5.5 of the proof of Theorem 5.8;
see `BookConcordance.md`)*.

# Generalized compact homotopies and the lemmas of the Morse-type theorem

## The text, paraphrased

(Definition 5.3.13 (preprint 5.20)) Given two compact sc-Fredholm problems `(fᵢ, Pᵢ)`, `fᵢ` an sc-Fredholm section of
the tame strong bundle `Pᵢ : Yᵢ → Xᵢ` with compact solution set, a *generalized compact homotopy*
between them is a tame strong bundle `P : Y → X` with an sc-Fredholm section `f` with compact
solution set, and an sc-smooth surjection `t : X → [0, 1]` such that the preimages `X_t` are tame
M-polyfolds, `f_t = f|X_t` is an sc-Fredholm section of `Y|X_t`, and `(f|Xᵢ, P|Yᵢ) = (fᵢ, Pᵢ)` for
`i = 0, 1`.  (Remark 5.3.14 (preprint 5.21)) One should rather ask for isomorphic problems.  (Theorem 5.3.15 (preprint 5.22)) Under
bump functions, `Xᵢ` without boundary, `(fᵢ, x)` in general position and `∂X = X₀ ⊔ X₁`, a small
`s₀` vanishing near `∂X` makes `(f + s₀, x)` in general position and `t|S_{f+s₀}` Morse.  In the
proof, at a critical point `x` of `t|S`, "we find a one-dimensional smooth sc-subspace `Z` with
`T_xX = Z ⊕ ker dt(x)`".  (Lemma 5.3.16 (preprint 5.23)) For `τ ∈ T*_xS` there is a unique `b_τ : T_xS → Z` with
`dt(x) ∘ b_τ = τ`; then also `dt(x) ∘ (b_τ + a) = τ` for `a : T_xS → ker dt(x)`.  (Lemma 5.3.17 (preprint 5.24)) There
is an sc⁺-section `s` with small support, `s(x) = 0` and `f'(x) ∘ b_τ + s'(x)|T_xS = 0`.  *Proof*:
`f'(x) ∘ b_τ` has (at most) one-dimensional image spanned by a smooth `e`; with `K` its kernel and
`L` a complement in `T_xS`, `j : L → ℝ` an isomorphism, and `S` written as a graph, the section
`s(k + l + δ(k + l) + v) = R(·, β(·) j(l) e)` has `s(0) = 0` and `s'(0)(δk + δl) = j(δl) e`; a
multiple of `s` does the job.

## What is formalized

* `StrongBundle.IsGenCompactHomotopy` (**Definition 5.3.13 (preprint 5.20)**): `X` tame, `f` an sc-Fredholm section
  with tame germ data (Definition 3.6.4 (preprint 3.51)) and compact solution set, `t : X → ℝ` sc-smooth with
  `t(X) = [0, 1]`, and for every `τ ∈ [0, 1]` the fibre `X_τ = t⁻¹(τ)` a sub-M-polyfold with tame
  induced structure on which the restriction `f|X_τ` (`restrictSection`, the section `a ↦ (a, f(a))`
  of the pull-back `ι*Y` along the inclusion, Proposition 2.6.8 (preprint 2.54)) is an sc-Fredholm section with tame
  germ data.  `IsGenCompactHomotopy.isCompact_solutionSet_restrict`: the restricted problems have
  compact solution sets (the text's "compact sc-Fredholm problems" at the ends).
* `lemma_5_3_16_preprint` (**Lemma 5.3.16 (preprint 5.23)**, linear algebra): for `T = Z ⊕ ker ℓ` and `τ : S → ℝ` there is a
  unique `b : S → Z` with `ℓ ∘ b = τ`, and `ℓ ∘ (b + a) = τ` for `a` with values in `ker ℓ`.
  `exists_isCompl_ker_of_ne_zero` (the existence of `Z`, spanned by a vector of any given algebraic
  spanning set; the dense smooth vectors are not one in infinite dimensions, and the smooth `Z` of
  the text comes from density instead, Findings Chapter 5 item 101) and `ne_zero_of_isCompl_ker` (**the hidden hypothesis** of Theorem
  5.22: a one-dimensional `Z` with `T = Z ⊕ ker ℓ` exists only if `ℓ ≠ 0`, i.e. `dt(x) ≠ 0`).
* `scDeriv_smul_apply`: the product rule `D(a·w)(z) = Da(z)·w(z) + a(z)·Dw(z)` at a level-`1`
  point.
* `exists_scPlusSection_linAt` (**the construction of Lemma 5.3.17 (preprint 5.24)**, in a chart): for a strong
  bundle chart `c` around a smooth point `x`, a smooth point `e` of the fibre over `x`, a continuous
  linear functional `ℓ` on the model space and an open `U ∋ x`, an sc⁺-section `s` with
  `s(x) = 0`, `supp(s) ⊆ U` and `Lin_s(z)v = ℓ(v)·Φ(e)₂` for all `v ∈ T_zO`: `s = g·sₑ` with `sₑ`
  the sc⁺-section through `e` of Lemma 5.3.3 (preprint 5.11) and `g = β·ℓ(φ(·) − φ(x))` (`β` a bump function equal
  to `1` near `x`), by the product rule (`IsScPlusSection.smul_left`).
* `lemma_5_3_17` (**Lemma 5.3.17 (preprint 5.24)**): for an sc-Fredholm section `f`, a finite-dimensional subspace `K`
  of `T_zO` (the text's `T_xS = ker f'(x)`), a linear `b : K → T_zO` (the text's `b_τ`) such that
  `Lin_f(z) ∘ b` has values in the line spanned by `Φ(e)₂` for a smooth point `e` of the fibre
  (the text's "one-dimensional image spanned by some smooth point `e`"), there is an sc⁺-section
  `s` with `s(x) = 0`, `supp(s) ⊆ U` and `Lin_f(z)(b v) + Lin_s(z)v = 0` for `v ∈ K`.

## What the text leaves implicit, and the choices made

* **Definition 5.3.13 (preprint 5.20)**: `t` is read as an sc-smooth function `X → ℝ` with image `[0, 1]`; "`X_t` is a
  tame M-polyfold" as "a sub-M-polyfold (Definition 2.19) whose induced structure is tame"; "`f|X_t`
  is an sc-Fredholm section of `Y|X_t`" through the pull-back bundle of Proposition 2.6.8 (preprint 2.54) along the
  inclusion (sc-smooth by Proposition 2.3.19 (preprint 2.21)), with tame germ data as for the tame strong bundle `P`.
  "`(f|Xᵢ, P|Yᵢ) = (fᵢ, Pᵢ)`" identifies the end problems with the restrictions; the formalization
  takes the restrictions as the end problems (the identification up to isomorphism of Remark 5.3.14 (preprint 5.21)
  is `StrongBundle.IsGenCompactHomotopyBetween`, `CompactHomotopyIso.lean`).
* **Lemma 5.3.16 (preprint 5.23)** is linear algebra; "sc-operator" is automatic (`T_xS` is finite-dimensional and
  `Z` smooth).  **Hidden hypothesis of Theorem 5.3.15 (preprint 5.22)**: the decomposition `T_xX = Z ⊕ ker dt(x)`
  with `dim Z = 1` needs `dt(x) ≠ 0` (`ne_zero_of_isCompl_ker`), i.e. `t` a submersion at the
  critical points of `t|S`; the text does not assume it.
* **Lemma 5.3.17 (preprint 5.24)**: the graph `q ↦ q + δ(q)` of the text is not needed: the section is built from a
  continuous linear functional `ℓ` on the whole model space extending `−λ` (Hahn–Banach on the
  finite-dimensional `K`), where `Lin_f(z)(b v) = λ(v)·e`.  The linearization `s'(x)` is read in a
  chart (`linAt`), as everywhere in Chapter 5.  The text's case distinction ("if the operator is
  zero take `s = 0`") is not needed.
* **Theorem 5.3.15 (preprint 5.22) (Morse-type structure)** is formalized since 2026-11-12 in the
  files `Theorem5315_*.lean` (`theorem_5_3_15`, `Theorem5315_Final.lean`), with no added hypothesis:
  the 2021 Definition 5.3.13 (3) supplies `dt(x) ≠ 0`, the parametric Sard step is done with Lagrange
  multipliers on level sets of the solution manifold of `f + Σ μ_j σ_j` (no trivialization `Φ_λ`),
  and "Morse-type" is read through smooth parametrizations of the solution set.
* **Theorem 5.27 (cobordism between good position perturbations) is not formalized**: the text
  leaves its proof to the reader.
-/

open Set Filter Topology Function Module ContinuousLinearMap
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### Lemma 5.3.16 (preprint 5.23): linear algebra -/

section Lemma523

variable {T S : Type*} [AddCommGroup T] [Module ℝ T] [AddCommGroup S] [Module ℝ S]

/-- **Lemma 5.3.16 (preprint 5.23)**: let `ℓ : T → ℝ` be linear and nonzero (the text's `dt(x)` on `T_xX`; the
hidden hypothesis, `ne_zero_of_isCompl_ker`) and `Z` a complement of `ker ℓ` (`T = Z ⊕ ker ℓ`).
For every linear `τ : S → ℝ` (`τ ∈ T*_xS`) there is a unique linear `b : S → Z` with `ℓ ∘ b = τ`
(`b_τ`), and for every linear `b, a : S → T` with `ℓ ∘ b = τ` and `a` with values in `ker ℓ`,
`ℓ ∘ (b + a) = τ`.  (`T_xS` is finite-dimensional and `Z` smooth, so `b` is an sc-operator.) -/
theorem lemma_5_3_16_preprint {ℓ : T →ₗ[ℝ] ℝ} (hℓ : ℓ ≠ 0) {Z : Submodule ℝ T}
    (hZ : IsCompl Z (LinearMap.ker ℓ)) (τ : S →ₗ[ℝ] ℝ) :
    (∃! b : S →ₗ[ℝ] Z, ℓ ∘ₗ Z.subtype ∘ₗ b = τ) ∧
      ∀ b a : S →ₗ[ℝ] T, ℓ ∘ₗ b = τ → (∀ v, a v ∈ LinearMap.ker ℓ) → ℓ ∘ₗ (b + a) = τ := by
  -- `ℓ|_Z : Z → ℝ` is an isomorphism
  have hinj : Function.Injective (ℓ ∘ₗ Z.subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨w, hw⟩ hwk
    have h1 : w ∈ Z ⊓ LinearMap.ker ℓ := ⟨hw, hwk⟩
    rw [hZ.inf_eq_bot, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot]
    exact Subtype.ext h1
  have hsurj : Function.Surjective (ℓ ∘ₗ Z.subtype) := by
    intro r
    obtain ⟨w, hw⟩ : ∃ w, ℓ w ≠ 0 := by
      by_contra h; push Not at h; exact hℓ (LinearMap.ext h)
    have hw' : w ∈ Z ⊔ LinearMap.ker ℓ := by rw [hZ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨z, hz, k, hk, rfl⟩ := Submodule.mem_sup.1 hw'
    have hk0 : ℓ k = 0 := hk
    have hz0 : ℓ z ≠ 0 := by rwa [map_add, hk0, add_zero] at hw
    refine ⟨(r / ℓ z) • ⟨z, hz⟩, ?_⟩
    simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply, map_smul,
      smul_eq_mul]
    field_simp
  have hbij : Function.Bijective (ℓ ∘ₗ Z.subtype) := ⟨hinj, hsurj⟩
  set e := LinearEquiv.ofBijective (ℓ ∘ₗ Z.subtype) hbij with he
  refine ⟨⟨e.symm.toLinearMap ∘ₗ τ, ?_, fun b hb => ?_⟩, fun b a hb ha => ?_⟩
  · ext v
    change (ℓ ∘ₗ Z.subtype) (e.symm (τ v)) = τ v
    exact e.apply_symm_apply (τ v)
  · refine LinearMap.ext fun v => ?_
    have h1 : (ℓ ∘ₗ Z.subtype) (b v) = τ v := congrArg (fun F : S →ₗ[ℝ] ℝ => F v) hb
    change b v = e.symm (τ v)
    rw [← h1]
    exact (e.symm_apply_apply (b v)).symm
  · ext v
    have h2 : ℓ (a v) = 0 := ha v
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, h2, add_zero]
    exact congrArg (fun F : S →ₗ[ℝ] ℝ => F v) hb

/-- **The hidden hypothesis of Theorem 5.3.15 (preprint 5.22)**: a nonzero complement `Z` of `ker ℓ` (the text's
one-dimensional `Z` with `T_xX = Z ⊕ ker dt(x)`) exists only if `ℓ ≠ 0`, i.e. `dt(x) ≠ 0`.  (For
`ℓ = 0`, `ker ℓ = T` and the only complement is `0`; then `b_τ` of Lemma 5.3.16 (preprint 5.23) exists only for
`τ = 0`.) -/
theorem ne_zero_of_isCompl_ker {ℓ : T →ₗ[ℝ] ℝ} {Z : Submodule ℝ T}
    (hZ : IsCompl Z (LinearMap.ker ℓ)) (hZ0 : Z ≠ ⊥) : ℓ ≠ 0 := by
  rintro rfl
  apply hZ0
  have := hZ.inf_eq_bot
  rwa [LinearMap.ker_zero, inf_top_eq] at this

/-- **The one-dimensional complement of `ker ℓ`** ("since `x` is a smooth point, we find a
one-dimensional smooth linear sc-subspace `Z ⊆ T_xX` with `T_xX = Z ⊕ ker dt(x)`"): if `ℓ ≠ 0` and
`D` spans `T` algebraically (in finite dimensions any dense set does; the dense smooth vectors of
an infinite-dimensional `T_xX` need not), then `Z = ℝ e` for some `e ∈ D`
is a one-dimensional complement of `ker ℓ`. -/
theorem exists_isCompl_ker_of_ne_zero {ℓ : T →ₗ[ℝ] ℝ} (hℓ : ℓ ≠ 0) {D : Set T}
    (hD : Submodule.span ℝ D = ⊤) :
    ∃ e ∈ D, ℓ e ≠ 0 ∧ IsCompl (ℝ ∙ e) (LinearMap.ker ℓ) := by
  obtain ⟨e, heD, he⟩ : ∃ e ∈ D, ℓ e ≠ 0 := by
    by_contra h
    push Not at h
    apply hℓ
    have : Submodule.span ℝ D ≤ LinearMap.ker ℓ := Submodule.span_le.2 fun x hx => h x hx
    rw [hD, top_le_iff] at this
    exact LinearMap.ker_eq_top.1 this
  refine ⟨e, heD, he, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx1
    have : a * ℓ e = 0 := by
      have h2 : ℓ (a • e) = 0 := hx2
      rwa [map_smul, smul_eq_mul] at h2
    rcases mul_eq_zero.1 this with h | h
    · rw [h, zero_smul]; exact Submodule.zero_mem _
    · exact absurd h he
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = (ℓ x / ℓ e) • e + (x - (ℓ x / ℓ e) • e) := by abel
    rw [hx]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)) ?_
    change ℓ (x - (ℓ x / ℓ e) • e) = 0
    rw [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring

end Lemma523

/-! ### Definition 5.3.13 (preprint 5.20): generalized compact homotopies -/

section Def520

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

variable (P) in
/-- **The restriction `f|A` of a section to a subset `A ⊆ X`**, as the section `a ↦ (a, f(a))` of
the pull-back `ι*Y → A` of `P` along the inclusion `ι : A → X` (the text's section of `Y|A`). -/
def restrictSection (A : Set X) (f : X → Y) (hf : IsSection P f) :
    A → pullbackSpace P (Subtype.val : A → X) :=
  fun a => ⟨((a, f a) : A × Y), hf a⟩

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The zeros of the restriction are the zeros of `f` in `A`. -/
lemma isZeroAt_restrictSection_iff {A : Set X} {f : X → Y} (hf : IsSection P f) (a : A) :
    IsZeroAt (pullbackProj P (Subtype.val : A → X)) (restrictSection P A f hf) a ↔
      IsZeroAt P f a := by
  constructor
  · intro h
    exact congrArg (fun q : pullbackSpace P (Subtype.val : A → X) => q.1.2) h
  · intro h
    exact Subtype.ext (Prod.ext rfl h)

variable (B : StrongBundle PX P)

/-- **Definition 5.3.13 (preprint 5.20) (generalized compact homotopy)**: the tame strong bundle `P : Y → X` (`X`
tame, `f` with tame germ data, Definition 3.6.4 (preprint 3.51)) with the sc-Fredholm section `f` and the sc-smooth
function `t : X → ℝ` is a **generalized compact homotopy** (between the compact sc-Fredholm
problems obtained by restricting to `X₀ = t⁻¹(0)` and `X₁ = t⁻¹(1)`) if `f` has a compact solution
set, `t(X) = [0, 1]`, and for every `τ ∈ [0, 1]` the fibre `X_τ = t⁻¹(τ)` is a sub-M-polyfold of
`X` whose induced structure is tame, and the restriction `f_τ = f|X_τ` (`restrictSection`) is an
sc-Fredholm section, with tame germ data, of the pull-back `Y|X_τ = ι*Y` of `P` along the
inclusion `ι : X_τ → X` (Proposition 2.6.8 (preprint 2.54), `StrongBundle.pullback`; `ι` is sc-smooth by
Proposition 2.3.19 (preprint 2.21)).  The text's `(f|Xᵢ, P|Yᵢ) = (fᵢ, Pᵢ)` identifies the given end problems with
these restrictions (Remark 5.3.14 (preprint 5.21): up to an isomorphism, see
`StrongBundle.IsGenCompactHomotopyBetween` in `CompactHomotopyIso.lean`). -/
structure StrongBundle.IsGenCompactHomotopy (f : X → Y) (t : X → ℝ) : Prop where
  isTame : PX.IsTame
  isScFredholm : B.IsScFredholmSectionTame f
  isCompact : IsCompact (solutionSet P f)
  isScSmooth_t : PX.IsScSmoothMap realPolyfold t
  range_t : range t = Icc 0 1
  fibre : ∀ τ ∈ Icc (0 : ℝ) 1, ∃ hsub : PX.IsSubMPolyfold (t ⁻¹' {τ}),
    haveI := PX.paracompactSpace_subtype (t ⁻¹' {τ})
    (MPolyfold.subPolyfold hsub).IsTame ∧
    haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : t ⁻¹' {τ} → X))
      (MPolyfold.subPolyfold hsub) B
    (B.pullback (MPolyfold.subPolyfold_inclusion_isScSmooth hsub)).IsScFredholmSectionTame
      (restrictSection P (t ⁻¹' {τ}) f isScFredholm.isScSmooth.1)

variable {B}

/-- **The restricted problems are compact sc-Fredholm problems** (the text's hypothesis on
`(fᵢ, Pᵢ)`): the solution set of `f|X_τ` is compact, as the trace of the compact `S_f` on the
closed fibre `X_τ`. -/
theorem StrongBundle.IsGenCompactHomotopy.isCompact_solutionSet_restrict {f : X → Y} {t : X → ℝ}
    (h : B.IsGenCompactHomotopy f t) (τ : ℝ) :
    IsCompact (solutionSet (pullbackProj P (Subtype.val : t ⁻¹' {τ} → X))
      (restrictSection P (t ⁻¹' {τ}) f h.isScFredholm.isScSmooth.1)) := by
  have hcont : Continuous t := continuousOn_univ.1 h.isScSmooth_t.continuousOn
  have hcl : IsClosed (t ⁻¹' {τ}) := isClosed_singleton.preimage hcont
  have heq : solutionSet (pullbackProj P (Subtype.val : t ⁻¹' {τ} → X))
      (restrictSection P (t ⁻¹' {τ}) f h.isScFredholm.isScSmooth.1) =
      Subtype.val ⁻¹' solutionSet P f := by
    ext a
    exact isZeroAt_restrictSection_iff h.isScFredholm.isScSmooth.1 a
  rw [heq]
  exact hcl.isClosedEmbedding_subtypeVal.isCompact_preimage h.isCompact

end Def520

/-! ### Two derivative rules at a level-`1` point -/

section DerivRules

variable {E F : ScBanach}

/-- **The product rule at a level-`1` point**: `D(a·w)(z)v = Da(z)v·w(z) + a(z)·Dw(z)v` for
sc-smooth `a : U → ℝ` and `w : U → F`. -/
theorem scDeriv_smul_apply {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) {a : E 0 → ℝ}
    {w : E 0 → F 0} (ha : IsScSmooth (F := ScBanach.const ℝ) U a) (hw : IsScSmooth U w)
    {z : E 1} (hz : z ∈ E.lvlSet U 1) (v : E 0) :
    scDeriv U (fun u => a u • w u) z v =
      scDeriv (F := ScBanach.const ℝ) U a z v • w (E.toBase 1 z) +
        a (E.toBase 1 z) • scDeriv U w z v := by
  have hp : IsScSmooth U (fun u => a u • w u) := ha.smul hU.isScDomain hw
  have d1 := hp.isSc1.isSc1With_scDeriv.hasFDerivWithinAt z hz
  have da : HasFDerivWithinAt (fun y : E 1 => a (E.toBase 1 y))
      (((scDeriv (F := ScBanach.const ℝ) U a z : E 0 →L[ℝ] ℝ)).comp (E.toBase 1))
      (E.lvlSet U 1) z := ha.isSc1.isSc1With_scDeriv.hasFDerivWithinAt z hz
  have dw := hw.isSc1.isSc1With_scDeriv.hasFDerivWithinAt z hz
  set L : E 0 →L[ℝ] F 0 := a (E.toBase 1 z) • scDeriv U w z +
    ((scDeriv (F := ScBanach.const ℝ) U a z : E 0 →L[ℝ] ℝ)).smulRight (w (E.toBase 1 z)) with hL
  have d2 : HasFDerivWithinAt ((fun u => a u • w u) ∘ E.toBase 1) (L.comp (E.toBase 1))
      (E.lvlSet U 1) z := by
    have := da.fun_smul dw
    refine this.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun y => ?_
    simp only [hL, add_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have heq := ContinuousLinearMap.ext_of_comp_toBase_one
    ((hU.isScDomain.uniqueDiffWithinAt 1 z hz).eq d1 d2)
  rw [heq, hL, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, add_comm]

/-- **The chain rule with an affine functional**: `D(ℓ(ρ(·) − p))(z) = ℓ ∘ Dρ(z)`. -/
theorem scDeriv_clm_sub_apply {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    {ρ : E 0 → E 0} (hρ : IsScSmooth U ρ) (ℓ : E 0 →L[ℝ] ℝ) (p : E 0) {z : E 1}
    (hz : z ∈ E.lvlSet U 1) (v : E 0) :
    scDeriv (F := ScBanach.const ℝ) U (fun u => ℓ (ρ u - p)) z v = ℓ (scDeriv U ρ z v) := by
  have hout : IsScSmooth (E := E) (F := ScBanach.const ℝ) univ (fun q => ℓ (q - p)) :=
    IsScSmooth.of_contDiffOn_finiteDimensional (isScDomain_univ _)
      ((ℓ.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
  have hc : IsScSmooth (F := ScBanach.const ℝ) U ((fun q => ℓ (q - p)) ∘ ρ) :=
    IsScSmooth.comp hU.isScDomain (isScDomain_univ _) hout hρ (mapsTo_univ _ _)
  have d1 := hc.isSc1.isSc1With_scDeriv.hasFDerivWithinAt z hz
  have dρ := hρ.isSc1.isSc1With_scDeriv.hasFDerivWithinAt z hz
  have d2 : HasFDerivWithinAt ((fun u => ℓ (ρ u - p)) ∘ E.toBase 1)
      ((ℓ.comp (scDeriv U ρ z)).comp (E.toBase 1)) (E.lvlSet U 1) z :=
    ℓ.hasFDerivAt.comp_hasFDerivWithinAt z (dρ.sub_const p)
  have heq := ContinuousLinearMap.ext_of_comp_toBase_one
    ((hU.isScDomain.uniqueDiffWithinAt 1 z hz).eq d1 d2)
  change scDeriv (F := ScBanach.const ℝ) U ((fun q => ℓ (q - p)) ∘ ρ) z v = _
  rw [heq]
  rfl

end DerivRules

/-! ### Lemma 5.3.17 (preprint 5.24) -/

section Lemma524

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

open scoped Classical in
/-- The function `g(y) = β(y)·ℓ(φ(y) − φ(x))` on `dom φ`, `0` outside (the scalar factor of the
section of Lemma 5.3.17 (preprint 5.24)). -/
def chartLinCutoff (φ : MChart X) (β : X → ℝ) (ℓ : φ.model.E 0 →L[ℝ] ℝ) (x y : X) : ℝ :=
  if y ∈ φ.source then β y * ℓ (φ y - φ x) else 0

omit [T2Space X] [ParacompactSpace X] in
lemma chartLinCutoff_of_mem {φ : MChart X} {β : X → ℝ} {ℓ : φ.model.E 0 →L[ℝ] ℝ} {x y : X}
    (hy : y ∈ φ.source) : chartLinCutoff φ β ℓ x y = β y * ℓ (φ y - φ x) := by
  simp only [chartLinCutoff, if_pos hy]

/-- `g = β·ℓ(φ(·) − φ(x))` is sc-smooth when `β` is, with `supp(β) ⊆ dom φ`. -/
theorem isScSmoothMap_chartLinCutoff {φ : MChart X} (hφ : PX.IsChart φ) {β : X → ℝ}
    (hβ : PX.IsScSmoothMap realPolyfold β) (hβs : tsupport β ⊆ φ.source)
    (ℓ : φ.model.E 0 →L[ℝ] ℝ) (x : X) :
    PX.IsScSmoothMap realPolyfold (chartLinCutoff φ β ℓ x) := by
  refine isScSmoothMap_real_of_local fun y => ?_
  by_cases hy : y ∈ φ.source
  · refine ⟨φ, φ.source, hφ, φ.isOpen_source, hy, subset_rfl, ?_⟩
    rw [φ.image_source]
    have hβ1 := hβ.real_chart hφ
    refine ⟨mapsTo_univ _ _, fun R hR => ?_⟩
    have hU := R.isScDomain
    have h1 := hβ1.comp_isScSmooth R hR
    have hout : IsScSmooth (E := φ.model.E) (F := ScBanach.const ℝ) univ
        (fun q => ℓ (q - φ x)) :=
      IsScSmooth.of_contDiffOn_finiteDimensional (isScDomain_univ _)
        ((ℓ.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
    have h2 : IsScSmooth (F := ScBanach.const ℝ) R.U ((fun q => ℓ (q - φ x)) ∘ R) :=
      IsScSmooth.comp hU (isScDomain_univ _) hout R.isScSmooth (mapsTo_univ _ _)
    have h3 := IsScSmooth.smul (F := ScBanach.const ℝ) hU h1 h2
    refine h3.congr hU fun u hu => ?_
    have hRu : R u ∈ φ.model.O := hR ▸ R.apply_mem_retract hu
    change (β ∘ φ.symm) (R u) • ℓ (R u - φ x) = chartLinCutoff φ β ℓ x (φ.symm (R u))
    rw [chartLinCutoff_of_mem (φ.symm_mapsTo hRu), φ.apply_symm_apply hRu, smul_eq_mul]
    rfl
  · have hyt : y ∉ tsupport β := fun h => hy (hβs h)
    obtain ⟨φ', hφ', hyφ'⟩ := PX.exists_isChart_mem_source y
    set V := φ'.source ∩ (tsupport β)ᶜ with hV
    have hVo : IsOpen V := φ'.isOpen_source.inter (isClosed_tsupport β).isOpen_compl
    have hzero : ∀ y' ∈ V, chartLinCutoff φ β ℓ x y' = 0 := fun y' hy' => by
      by_cases h : y' ∈ φ.source
      · rw [chartLinCutoff_of_mem h, image_eq_zero_of_notMem_tsupport hy'.2, zero_mul]
      · simp only [chartLinCutoff, if_neg h]
    refine ⟨φ', V, hφ', hVo, ⟨hyφ', hyt⟩, inter_subset_left, mapsTo_univ _ _, fun R hR => ?_⟩
    have hU := R.isScDomain
    refine (IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) (f := fun _ => (0 : ℝ)) hU
      contDiffOn_const).congr hU fun u hu => ?_
    have hRu : R u ∈ φ' '' V := hR ▸ R.apply_mem_retract hu
    obtain ⟨y', hy', hy'e⟩ := hRu
    change (0 : ℝ) = chartLinCutoff φ β ℓ x (φ'.symm (R u))
    rw [← hy'e, φ'.symm_apply_apply hy'.1, hzero y' hy']

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] in
/-- The support of `g·s` is contained in the support of `s`. -/
lemma sectionSupport_sectionSmul_subset {s : X → Y} (hs : IsSection P s) (g : X → ℝ) :
    sectionSupport P (sectionSmul P g s) ⊆ sectionSupport P s := by
  refine closure_mono fun y hy h0 => hy ?_
  rw [sectionSmul_apply hs]
  have : (⟨s y, hs y⟩ : P ⁻¹' {y}) = 0 := Subtype.ext h0
  rw [this, smul_zero]; rfl

omit [T2Space Y] [ParacompactSpace Y] in
/-- The principal part of `g·s` is `(g ∘ φ⁻¹)·ŝ` on `O`. -/
lemma principal_sectionSmul (c : StrongBundleChart PX P) {s : X → Y} (hs : IsSection P s)
    (g : X → ℝ) {u : c.φ.model.E 0} (hu : u ∈ c.φ.model.O) :
    c.principal (sectionSmul P g s) u = g (c.φ.symm u) • c.principal s u := by
  unfold StrongBundleChart.principal
  rw [sectionSmul_apply hs]
  exact (c.fiber_linear _ (c.φ.symm_mapsTo hu)).map_smul _ _

/-- **The construction of Lemma 5.3.17 (preprint 5.24), in a chart**: let `X` admit sc-smooth bump functions, `c`
a strong bundle chart around the smooth point `x`, `z` the level-`1` point over `φ(x)`, `e` a
smooth point of the fibre over `x`, `ℓ` a continuous linear functional on the model space `E` and
`U ∋ x` open.  Then there is an sc⁺-section `s` with `s(x) = 0`, `supp(s) ⊆ U` and
`Lin_s(z)v = ℓ(v)·Φ(e)₂` for every `v ∈ T_zO` (the text's `s'(0)(δk + δl) = j(δl)e`).  *Proof*:
`s = g·sₑ` with `sₑ` the sc⁺-section of Lemma 5.3.3 (preprint 5.11) through `e` (supported in `U ∩ dom φ`) and
`g = β·ℓ(φ(·) − φ(x))`, `β` a bump function with `β ≡ 1` near `x` and `supp(β) ⊆ dom φ`; `s` is
sc⁺ by the product rule (`IsScPlusSection.smul_left`), `s(x) = g(x)·e = 0`, and in the chart
`Lin_s(z)v = D(g ∘ φ⁻¹ ∘ r)(z)v·ŝₑ(φ(x)) + g(x)·Lin_{sₑ}(z)v = ℓ(Dr(z)v)·Φ(e)₂ = ℓ(v)·Φ(e)₂`
(`g ∘ φ⁻¹ = ℓ(· − φ(x))` near `φ(x)` on `O`, and `Dr(z) = 1` on `T_zO`). -/
theorem exists_scPlusSection_linAt (hbump : PX.AdmitsBumpFunctions) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {x : X} (hxc : x ∈ c.φ.source) (hx : x ∈ PX.smoothSet)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ x) {e : Y}
    (he : e ∈ B.toMPolyfold0.smoothSet) (hex : P e = x) (ℓ : c.φ.model.E 0 →L[ℝ] ℝ)
    {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ s : X → Y, B.IsScPlusSection s ∧ s x = fiberZero P x ∧ sectionSupport P s ⊆ U ∧
      ∀ v : ↥(rangeS (scDeriv c.U (r c.R) z)),
        linAt c.U c.R (c.principal s) z v = ℓ v • (c e).2 := by
  obtain ⟨N, hN⟩ := proposition_5_1_3_exists (B := B)
  obtain ⟨-, se, hse, hsex, hsesupp, -⟩ :=
    lemma_5_3_3 hbump hN hx he hex one_pos (hU.inter c.φ.isOpen_source) ⟨hxU, hxc⟩
  obtain ⟨β, hβ, -, -, hβs, hβ1⟩ := proposition_5_5_3 hbump c.φ.isOpen_source hxc
  set g := chartLinCutoff c.φ β ℓ x with hgdef
  have hg : PX.IsScSmoothMap realPolyfold g := isScSmoothMap_chartLinCutoff c.isChart hβ hβs ℓ x
  have hgx : g x = 0 := by rw [hgdef, chartLinCutoff_of_mem hxc, sub_self, map_zero, mul_zero]
  have hses : IsSection P se := hse.1
  refine ⟨sectionSmul P g se, hse.smul_left hg, ?_, ?_, fun v => ?_⟩
  · rw [sectionSmul_apply hses, hgx, zero_smul]; rfl
  · exact (sectionSupport_sectionSmul_subset hses g).trans (hsesupp.trans inter_subset_left)
  -- the derivative
  have hUq := c.relOpen
  have hR := c.isRetraction
  have hxO : c.φ x ∈ c.φ.model.O := c.φ.mapsTo_model x hxc
  have hxO' : c.φ x ∈ r c.R '' c.U := c.r_image ▸ hxO
  have hz1 : z ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, hz]; exact mem_U_of_mem_O hR hxO'
  have hrx : r c.R (c.φ x) = c.φ x := r_eq_self hR hxO'
  have hrs : IsScSmooth c.U (r c.R) := r_isScSmooth hUq hR
  -- the two factors on `U`
  set a : c.φ.model.E 0 → ℝ := fun u => g (c.φ.symm (r c.R u)) with ha
  set w : c.φ.model.E 0 → c.F 0 := c.principal se ∘ r c.R with hw
  have has : IsScSmooth (F := ScBanach.const ℝ) c.U a :=
    ((hg.real_chart c.isChart).comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen)
      c.base_retract).congr hUq.isScDomain fun _ _ => rfl
  have hws : IsScSmooth c.U w := by
    have hlift : IsScSmooth (F := c.F.shift) c.U
        fun u => c.principalLift se (r c.R u) :=
      ((hse.isScSmoothRetractMap_one hc).comp_isScSmooth
        (c.isRetraction.baseRetraction c.relOpen) c.base_retract).snd hUq.isScDomain |>.congr
          hUq.isScDomain fun _ _ => rfl
    exact (hlift.toBase_shift hUq.isScDomain).congr hUq.isScDomain fun u hu =>
      hse.toBase_principalLift hc (c.r_mem_O hu)
  have hprod : EqOn (c.principal (sectionSmul P g se) ∘ r c.R) (fun u => a u • w u) c.U :=
    fun u hu => principal_sectionSmul c hses g (c.r_mem_O hu)
  have hss : IsScSmooth c.U (fun u => a u • w u) := has.smul hUq.isScDomain hws
  have hsr : IsSc1 c.U (c.principal (sectionSmul P g se) ∘ r c.R) :=
    (hss.congr hUq.isScDomain fun u hu => (hprod hu).symm).isSc1
  -- `a = ℓ(r(·) − φ(x))` near `z`
  obtain ⟨W, hWsub, hWo, hxW⟩ := eventually_nhds_iff.1 hβ1
  obtain ⟨G, hGo, hG⟩ := c.φ.exists_isOpen_image_eq (s := W ∩ c.φ.source) inter_subset_right
    (hWo.inter c.φ.isOpen_source)
  obtain ⟨G', hG'o, hG'⟩ := (continuousOn_iff'.1 hrs.isSc1.isSc0.continuousOn_base) G hGo
  obtain ⟨O₀, hO₀, hUO₀⟩ := hUq.relOpen
  set U' := c.U ∩ r c.R ⁻¹' G with hU'
  have hU'rel : IsRelOpenInQuadrant c.φ.model.E c.φ.model.C U' := by
    refine ⟨hUq.isPartialQuadrant, O₀ ∩ G', hO₀.inter hG'o, ?_⟩
    rw [hU', inter_comm c.U, hG', hUO₀]
    ext u; simp only [mem_inter_iff]; tauto
  have hxG : c.φ x ∈ G := by
    have : c.φ x ∈ c.φ '' (W ∩ c.φ.source) := ⟨x, ⟨hxW, hxc⟩, rfl⟩
    rw [hG] at this; exact this.2
  have hz1' : z ∈ c.φ.model.E.lvlSet U' 1 := by
    refine ⟨hz1, ?_⟩
    change r c.R (c.φ.model.E.toBase 1 z) ∈ G
    rw [hz, hrx]; exact hxG
  have haeq : EqOn a (fun u => ℓ (r c.R u - c.φ x)) U' := by
    intro u hu
    have hruO : r c.R u ∈ c.φ.model.O := c.r_mem_O hu.1
    have hru : r c.R u ∈ c.φ '' (W ∩ c.φ.source) := by rw [hG]; exact ⟨hruO, hu.2⟩
    obtain ⟨y, hy, hyu⟩ := hru
    change g (c.φ.symm (r c.R u)) = ℓ (r c.R u - c.φ x)
    rw [← hyu, c.φ.symm_apply_apply hy.2, hgdef, chartLinCutoff_of_mem hy.2, hWsub y hy.1,
      one_mul]
  have hout : IsScSmooth (E := c.φ.model.E) (F := ScBanach.const ℝ) univ
      (fun q => ℓ (q - c.φ x)) :=
    IsScSmooth.of_contDiffOn_finiteDimensional (isScDomain_univ _)
      ((ℓ.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
  have hℓs : IsScSmooth (F := ScBanach.const ℝ) c.U ((fun q => ℓ (q - c.φ x)) ∘ r c.R) :=
    IsScSmooth.comp hUq.isScDomain (isScDomain_univ _) hout hrs (mapsTo_univ _ _)
  have hDa : scDeriv (F := ScBanach.const ℝ) c.U a z =
      scDeriv (F := ScBanach.const ℝ) c.U (fun u => ℓ (r c.R u - c.φ x)) z :=
    scDeriv_eq_of_eqOn_relOpen hU'rel has.isSc1 hℓs.isSc1 inter_subset_left inter_subset_left
      haeq hz1'
  -- assemble
  have hv : scDeriv c.U (r c.R) z (v : c.φ.model.E 0) = v := by
    obtain ⟨w', hw'⟩ := v.2
    rw [← hw']
    exact scDeriv_r_idem_at hUq hR (by rw [hz]; exact hxO') w'
  rw [linAt_apply, scDeriv_eq_of_eqOn_relOpen hUq hsr hss.isSc1 subset_rfl subset_rfl hprod hz1,
    scDeriv_smul_apply hUq has hws hz1, hDa, scDeriv_clm_sub_apply hUq hrs ℓ (c.φ x) hz1, hv]
  have ha0 : a (c.φ.model.E.toBase 1 z) = 0 := by
    change g (c.φ.symm (r c.R (c.φ.model.E.toBase 1 z))) = 0
    rw [hz, hrx, c.φ.symm_apply_apply hxc, hgx]
  have hw0 : w (c.φ.model.E.toBase 1 z) = (c e).2 := by
    change c.principal se (r c.R (c.φ.model.E.toBase 1 z)) = (c e).2
    rw [hz, hrx]
    unfold StrongBundleChart.principal
    rw [c.φ.symm_apply_apply hxc, hsex]
  rw [ha0, hw0, zero_smul, add_zero]

/-- **Lemma 5.3.17 (preprint 5.24)**: let `X` admit sc-smooth bump functions, `f` a section of the strong bundle
`P` (in the text sc-Fredholm with `f(x) = 0`), `c` a strong bundle chart around the smooth point
`x`, `z` the level-`1` point over `φ(x)`, `K ⊆ T_zO` a finite-dimensional subspace (the text's
`T_xS = ker f'(x)`, finite-dimensional by Proposition 3.6.5 (preprint 3.52)) and `b : K → T_zO` linear (the text's
`b_τ` of Lemma 5.3.16 (preprint 5.23)) such that `Lin_f(z) ∘ b` takes values in the line spanned by `Φ(e)₂` for a
smooth point `e` of the fibre over `x` (the text: "the operator has a one-dimensional image spanned
by some smooth point `e ∈ Y_x`").  Then for every open `U ∋ x` there is an sc⁺-section `s` with
(1) `s(x) = 0`, `supp(s) ⊆ U`, and (2) `f'(x) ∘ b + s'(x)|_K = 0`, i.e.
`Lin_f(z)(b v) + Lin_s(z)v = 0` for `v ∈ K`.  *Proof*: write `Lin_f(z)(b v) = λ(v)·Φ(e)₂` with `λ`
linear on `K`, extend `−λ` to a continuous linear functional `ℓ` on the model space (Hahn–Banach),
and apply `exists_scPlusSection_linAt`.  (The text's graph `q ↦ q + δ(q)` and its case "the
operator is zero" are not needed.) -/
theorem lemma_5_3_17 (hbump : PX.AdmitsBumpFunctions) (f : X → Y) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {x : X} (hxc : x ∈ c.φ.source) (hx : x ∈ PX.smoothSet)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (K : Submodule ℝ ↥(rangeS (scDeriv c.U (r c.R) z))) [FiniteDimensional ℝ K]
    (b : K →ₗ[ℝ] ↥(rangeS (scDeriv c.U (r c.R) z))) {e : Y}
    (he : e ∈ B.toMPolyfold0.smoothSet) (hex : P e = x)
    (hb : ∀ v, ∃ a : ℝ, linAt c.U c.R (c.principal f) z (b v) = a • (c e).2)
    {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ s : X → Y, B.IsScPlusSection s ∧ s x = fiberZero P x ∧ sectionSupport P s ⊆ U ∧
      ∀ v : K, linAt c.U c.R (c.principal f) z (b v) + linAt c.U c.R (c.principal s) z v = 0 := by
  classical
  set e₀ := (c e).2 with he₀
  set M : K →ₗ[ℝ] c.F 0 :=
    (linAt c.U c.R (c.principal f) z : ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0) ∘ₗ b
    with hM
  -- `M = λ(·)·e₀` for a linear `λ : K → ℝ`
  obtain ⟨lam, hlam⟩ : ∃ lam : K →ₗ[ℝ] ℝ, ∀ v, M v = lam v • e₀ := by
    by_cases h0 : e₀ = 0
    · refine ⟨0, fun v => ?_⟩
      obtain ⟨a, ha⟩ := hb v
      rw [LinearMap.zero_apply, zero_smul]
      change linAt c.U c.R (c.principal f) z (b v) = 0
      rw [ha, h0, smul_zero]
    · have hrange : ∀ v, M v ∈ ℝ ∙ e₀ := fun v => by
        obtain ⟨a, ha⟩ := hb v
        change linAt c.U c.R (c.principal f) z (b v) ∈ ℝ ∙ e₀
        rw [ha]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e₀)
      set iso := LinearEquiv.toSpanNonzeroSingleton ℝ (c.F 0) e₀ h0
      refine ⟨iso.symm.toLinearMap ∘ₗ M.codRestrict (ℝ ∙ e₀) hrange, fun v => ?_⟩
      have h1 := iso.apply_symm_apply (M.codRestrict (ℝ ∙ e₀) hrange v)
      have h2 := congrArg Subtype.val h1
      rw [LinearEquiv.toSpanNonzeroSingleton_apply] at h2
      exact h2.symm
  -- extend `−λ` to `ℓ : E →L ℝ`
  set ψ : K →ₗ[ℝ] c.φ.model.E 0 := (rangeS (scDeriv c.U (r c.R) z)).subtype ∘ₗ K.subtype
    with hψ
  have hinj : Function.Injective ψ := Subtype.val_injective.comp Subtype.val_injective
  set eK := LinearEquiv.ofInjective ψ hinj with heK
  have : FiniteDimensional ℝ (LinearMap.range ψ) := LinearMap.finiteDimensional_range ψ
  set μ : LinearMap.range ψ →ₗ[ℝ] ℝ := -(lam ∘ₗ eK.symm.toLinearMap) with hμ
  obtain ⟨ℓ, hℓ, -⟩ :=
    exists_extension_norm_eq (LinearMap.range ψ) (LinearMap.toContinuousLinearMap μ)
  have hℓv : ∀ v : K, ℓ (ψ v) = -lam v := fun v => by
    have h1 := hℓ (eK v)
    rw [LinearMap.coe_toContinuousLinearMap', hμ, LinearMap.neg_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1
    exact h1
  obtain ⟨s, hs, hsx, hsupp, hlin⟩ := exists_scPlusSection_linAt hbump hc hxc hx hz he hex ℓ hU hxU
  refine ⟨s, hs, hsx, hsupp, fun v => ?_⟩
  have h1 : linAt c.U c.R (c.principal f) z (b v) = lam v • e₀ := hlam v
  rw [h1, hlin, ← he₀]
  have h2 : ℓ ((v : ↥(rangeS (scDeriv c.U (r c.R) z))) : c.φ.model.E 0) = -lam v := hℓv v
  rw [h2, neg_smul, add_neg_cancel]

end Lemma524

end Polyfold
