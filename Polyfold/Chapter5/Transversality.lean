import Polyfold.Chapter5.Compactness
import Polyfold.Chapter5.BumpFunctions
import Polyfold.Chapter3.GlobalIFTIndex
import Polyfold.Chapter3.GlobalIFTIndexG
import Polyfold.Chapter3.FredholmGermLinearizationG
import Polyfold.Chapter3.LinearizationChartsG
import Polyfold.Chapter4.LocalStructure
import Polyfold.Chapter4.Families

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §5.3:
**Definition 5.15** (transversal to the zero section), **Definition 5.17** (general position of
`(f, x)`), **Lemma 5.26** (general position implies good position), and **Theorem 5.13**
(perturbation and transversality, interior case), with the lemmas its proof uses without stating
them *(book 2017: Definitions 5.8, 5.9, Theorem 5.5; Lemma 5.26 is the unnumbered sentence
"Clearly general position implies good position", p. 166; see `BookConcordance.md`)*.

# Perturbation and transversality: the interior case

## The text, paraphrased

(Definition 5.15) An sc-Fredholm section `g` is *transversal to the zero section* if at every
zero `x` the linearization `g'(x) : T_xX → Y_x` is surjective.  (Definition 5.17) `(f, x)`,
`f(x) = 0`, is *in general position* if `f'(x)` is surjective and `ker f'(x)` has an
sc-complement contained in the reduced tangent space `T^R_xX`.  (Lemma 5.26, used after Theorem
5.19) "Clearly general position implies good position."  (Theorem 5.13) `P : Y → X` a strong
bundle over an M-polyfold with `∂X = ∅` admitting sc-smooth bump functions, `f` an sc-Fredholm
section with compact solution set, `N` an auxiliary norm.  There is an open `U ⊇ S_f` such that
for every `s ∈ Γ⁺(P)` with `supp(s) ⊆ U` and `N(s(x)) ≤ 1` ("`N(f(x)) ≤ 1`" in the text) the
solution set `S_{f+s}` is compact, and a dense subset `O ⊆ (Γ^{+,1}_U(P), ρ)` such that for
`s ∈ O` the section `f + s` is transversal and `S_{f+s}` is a compact smooth manifold without
boundary.  Proof: given `s₀'` and `ε`, take `s₀ = δ s₀'`; at every `x ∈ S_{f+s₀}` finitely many
allowable sc⁺-sections span `Y_x` together with the range of `(f + s₀)'(x)`; the parametrized
section `F(λ, y) = f(y) + s₀(y) + Σ λⱼ tⱼ(y)` (Theorem 3.18) has surjective linearization at
`(0, x)`, hence (Theorem 3.19) at `(0, y)` for zeros `y` near `x`; a finite subcover gives
`t₁, …, t_m`; by the implicit function theorem `S̃ = F⁻¹(0)` is a smooth manifold near
`{0} × S_{f+s₀}`; for a regular value `λ₀` of the projection `S̃ → ℝᵐ` "it is easily verified
that `f + s₀ + s(λ₀, ·)` is transversal".

## What is formalized

* `StrongBundle.IsTransversal` (**Definition 5.15**): `IsLinSurjAt` at every zero (the chart
  form of "`g'(x)` surjective", chart independent by `linAt_chart_independence`;
  `StrongBundle.IsLinSurjAt.linAt_surjective`, `GlobalIFTIndex.lean`, states the surjectivity in
  every chart).
* `StrongBundle.IsGeneralPositionGerm` (**Definition 5.17**, in a chart): in a tame strong bundle
  chart around the zero (`IsTameChart`), `Lin(z)` is onto `K_z`, and for every presentation `T` of the partial
  quadrant the kernel of `Lin(z)` has an sc-complement in `T_zO` contained in `T^R_zO`
  (`reducedTangentSpaceWith`, the form of Definition 4.21 in `Chapter4/Submanifolds.lean`).
* `isInGoodPositionIn_of_scComplement_le_reduced` and
  `StrongBundle.IsGeneralPositionGerm.isGoodPositionGerm` (**Lemma 5.26**): a subspace of `T_zO`
  with an sc-complement inside `T^R_zO` is in good position to the partial cone (with the
  interior condition of Definition 3.21, which the text omits), so general position gives
  Definition 3.53 (`isGoodPositionGerm_of_linAt_surj`);
  `StrongBundle.IsGeneralPositionGerm.isGoodPositionGermTame`: the same in the tame chart of the
  germ data, for a section with tame germ data.
* `surjective_of_forall_exists_ker_fst` and `forall_exists_ker_fst_of_surjective` (**"regular
  value ⟺ transversal", the linear algebra**): for `M(a, u) = L u + Σ aᵢ eᵢ` onto, the
  projection `ker M → ℝᵐ` is onto iff `L` is onto.
* `exists_fin_mem_of_dense_of_closedComplemented`: a closed subspace of finite codimension and
  a dense subspace: finitely many vectors of the dense subspace span a complement (the
  smooth vectors needed for Lemma 5.11).
* **The parametrized section and its slices**: `paramSlice` (the section `g + Σ λᵢ tᵢ` of `P`
  at the parameter `λ`), `isZeroAt_paramSection_iff` (the zeros of `F` are the pairs `(λ, y)`
  with `y` a zero of the slice), `paramSlice_eq_sectionAdd`, `isScFredholmSection_paramSlice`
  (Theorem 3.15), `isScPlusSection_paramSlice`, `principal_paramSlice`, `sectionAdd_paramSlice`,
  `paramSlice_zero`; `mem_K_ofProd_zero_iff` (the fibre of the product chart over `(0, 0)`),
  `linAt_congr`.
* **"It is easily verified" (regular value ⟹ transversal)**: `isLinSurjAt_paramSlice_of_ker_fst`:
  if `Lin_F` is onto at `(λ, y)` and `ker Lin_F(0)` in the product chart `(r ↦ r − λ) × Φ` of a
  chart `Φ` centred at `y` projects onto `ℝᵐ`, the slice is transversal at `y`
  (`linAt_paramSection` of `ParamPerturbation.lean`).  Conversely
  `isLinSurjAt_paramSection_zero_of_spanning`: `F` is transversal at `(0, y)` when the sections
  span `K₀` together with the range of `Lin_g(0)`.
* **The spanning sections** (`exists_spanning_sections`): at a zero of an sc-Fredholm section,
  finitely many allowable sc⁺-sections whose values span a complement of the range of `Lin(0)`
  in `K₀`, from Proposition 3.52, the density of the smooth vectors `ρ(0)F_∞ ⊆ K₀ ∩ F_∞` and
  Lemma 5.11, rescaled so that `N ≤ 1`.
* **The openness steps**: `exists_isOpen_isLinSurjAt_zero_near` (transversality of `F_x` at
  `(0, x)` propagates to the zeros `y` near `x`: Theorem 3.54 (1)),
  `isLinSurjAt_paramSection_zero_of_comp` (adding sections keeps the transversality),
  `exists_isOpen_goodPosition_of_isLinSurjAt` (an open `V ⊇ {0} × S_g` of zeros of `F` in good
  position), `isWithoutBoundary_prod_rn` (`ℝᵐ × X` has no boundary), `isClosed_solutionSet`.
* **The omitted step** `exists_pos_forall_mem_of_isCompact`: for a compact `Z ⊆ ℝᵐ × X` and an
  open `V` containing `Z ∩ {λ = 0}`, `Z ∩ {|λ| < δ} ⊆ V` for some `δ > 0`; with Remark 5.12 for
  the allowable perturbations `s₀ + Σ λᵢ tᵢ` (`auxLe_paramSlice`,
  `sectionSupport_paramSlice_subset`,
  `isZeroAt_paramSlice_of_not_mem_support`), every zero of `F(λ, ·)` with `|λ|` small lies in `V`.
* **The Sard step** `exists_null_isLinSurjAt_paramSlice_near`: at a zero `z₀` of `F` in good
  position, the regular tangent germ chart `D` of Theorem 3.54 (2), the `C^∞` map
  `q = p ∘ D.φ⁻¹ ∘ Γ` on the finite-dimensional model `V`, Sard's theorem on the strata of `V`
  (`measure_image_stratCritSet`), and, at a zero over a regular value, the derivative of
  `gmap = ψ ∘ D.φ⁻¹ ∘ Γ` (`ψ` the product chart) with values in `T₀O ∩ ker Lin_F(0)`.
* **Theorem 5.13**: `theorem_5_13_generic` (the generic form: for almost every small `λ` the
  perturbation `s₀ + Σ λᵢ tᵢ` is allowable, `f + s₀ + Σ λᵢ tᵢ` is transversal, its solution set
  is compact and, if non-empty, a smooth manifold without boundary of dimension the Fredholm
  index, `StrongBundle.SolutionSetIsManifold`), and `theorem_5_13` (the text's dense-set form,
  with the pointwise distance `StrongBundle.sectionDistAt`), for `f` with tame germ data
  (`IsScFredholmSectionTame`, Definition 3.51); the parametrized sections then have tame germ data
  by `theorem_3_18_tame`.

## What the text leaves implicit, and the choices made (the findings)

* **Definitions 5.15 and 5.17 are stated in `T_xX`** (gap G.7/G.13): here in charts, with the
  linearization `Lin(z)` of `LinearizationCharts.lean`, and for Definition 5.17 with the reduced
  tangent space `T^R_zO` of Definition 2.27 and the presentation `T` of the partial quadrant.
  The chart independence of Definition 5.15 is `IsLinSurjAt.linAt_surjective`; that of Definition
  5.17 (transport of the sc-complement by `D(τ ∘ r)(z)`, Proposition 2.30) is proved in
  `GeneralPosition.lean` (`exists_isGeneralPositionGerm_iff`, Finding 82).
* **Lemma 5.26** needs the interior condition of Definition 3.21 and the tameness of the chart
  (for `dim T_zO/T^R_zO = d_C(z)`, Proposition 2.36); the text argues in basic germ coordinates.
* **Tameness.**  The text assumes a tame strong bundle in §5.3 but not in Theorem 5.13; the
  implicit function theorems of §3.6 need the germ data in tame strong bundle charts (Definitions
  3.50, 3.51: `IsScFredholmSectionTame`, `IsGoodPositionGermTame`, `TameGerms.lean`), so Theorem
  5.13 takes `f` with tame germ data, and the parametrized sections `F` on `ℝᵏ × X` inherit it
  (`theorem_3_18_tame`: the product chart of a tame chart is tame).  (An earlier version assumed
  the base retraction of every compatible chart of `P` and of the pull-backs `π*P` tame, which no
  strong bundle over a nonempty base satisfies; Findings, Chapter 3 items 190–199 and Chapter 5
  items 74–79.)  Definition 5.17 is stated in a tame chart (`IsTameChart`), where `T^R_zO` and
  the count `dim T_zO/T^R_zO = d_C(z)` of Lemma 5.26 make sense.
* **"`N(f(x)) ≤ 1`" is `N(s(x)) ≤ 1`**, "`(f, x)` in good position" is `(f + s, x)`, and
  "`N(s₀(y) + s(λ₀, y)) ≤ 1 − ε/2`" is `≤ 1`; "generic" is made precise as "for every `λ` outside
  a Lebesgue null set, `|λ| < δ`".
* **The omitted step**: that for small `λ` every zero of `F(λ, ·)` lies in the neighbourhood
  where `F'` is onto needs the compactness of `{(λ, y) | |λ| ≤ δ₁, F(λ, y) = 0}` (Remark 5.12).
* **"It is easily verified"**: only the direction "regular value ⟹ transversal" is needed, and it
  needs only `range D(gmap)(v) ⊆ ker Lin_F`, not `T_zS̃ = ker F'(z)`; the text's "⟺" (the
  converse, by the dimension count `dim T_zS̃ = dim ker F'(z)`) is not formalized.  Sard's theorem
  is applied in the stratified form of `Chapter4/FamiliesLocal.lean`, which avoids showing that
  the points of the model `V` over the zeros are interior points (they are, since `∂X = ∅`).
* **The metric `ρ`** on `Γ^{+,1}_U(P)` is not built as a metric space; density is stated
  pointwise, `∀ ε > 0, ∃ s, ∀ x, N(s(x) − s'(x)) ≤ ε`.
* **The empty solution set**: Theorem 3.56 as formalized needs a non-empty solution set, so the
  manifold conclusion is stated under that hypothesis (an empty set is trivially a manifold).
-/

open Set Filter Topology Function Module ContinuousLinearMap MeasureTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### The linear algebra of "regular value ⟺ transversal" -/

section LinearAlgebra

variable {T K : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup K]
  [NormedSpace ℝ K]

/-- **"A regular value of the projection gives transversality"** (the linear algebra of the
text's "it is easily verified"): let `M(a, u) = L u + Σ aᵢ eᵢ : ℝᵐ ⊕ T → K` be onto, and suppose
the projection `ker M → ℝᵐ` is onto.  Then `L` is onto. -/
theorem surjective_of_forall_exists_ker_fst {m : ℕ} (L : T →L[ℝ] K) (e : Fin m → K)
    (hM : ∀ k, ∃ (a : Fin m → ℝ) (u : T), L u + ∑ i, a i • e i = k)
    (hker : ∀ a : Fin m → ℝ, ∃ u, L u + ∑ i, a i • e i = 0) : Surjective L := by
  intro k
  obtain ⟨a, u, hu⟩ := hM k
  obtain ⟨u', hu'⟩ := hker a
  refine ⟨u - u', ?_⟩
  rw [map_sub, ← hu, eq_neg_of_add_eq_zero_left hu', sub_neg_eq_add]

/-- **"Transversality gives a regular value"**: if `L` is onto then the projection
`ker M → ℝᵐ` is onto, `M(a, u) = L u + Σ aᵢ eᵢ`. -/
theorem forall_exists_ker_fst_of_surjective {m : ℕ} (L : T →L[ℝ] K) (e : Fin m → K)
    (hL : Surjective L) (a : Fin m → ℝ) : ∃ u, L u + ∑ i, a i • e i = 0 := by
  obtain ⟨u, hu⟩ := hL (-∑ i, a i • e i)
  exact ⟨u, by rw [hu, neg_add_cancel]⟩

/-- **Finitely many vectors of a dense subspace span a complement of a closed subspace of finite
codimension**: for `R ⊆ K` closed, topologically complemented, of finite codimension, and `D`
dense in `K`, there are `d₁, …, d_k ∈ D` with `K = R + span{dᵢ}`.  (With `π` a continuous
projection onto `R`, `Q = ker π` is finite-dimensional and `(1 − π)(D)` is a dense, hence
closed, hence full subspace of `Q`.) -/
theorem exists_fin_mem_of_dense_of_closedComplemented [CompleteSpace K] {R D : Submodule ℝ K}
    (hR : R.ClosedComplemented) (hco : R.CoFG) (hD : Dense (D : Set K)) :
    ∃ (k : ℕ) (d : Fin k → K), (∀ i, d i ∈ D) ∧
      ∀ x, ∃ (r : K) (_ : r ∈ R) (a : Fin k → ℝ), x = r + ∑ i, a i • d i := by
  classical
  obtain ⟨π, hπ⟩ := hR
  set p : K →L[ℝ] K := R.subtypeL.comp π with hp
  have hpR : ∀ x, p x ∈ R := fun x => (π x).2
  have hpr : ∀ r ∈ R, p r = r := fun r hr => by
    change ((π r : R) : K) = r
    rw [hπ ⟨r, hr⟩]
  have hpp : ∀ x, p (p x) = p x := fun x => hpr _ (hpR x)
  set q : K →L[ℝ] K := ContinuousLinearMap.id ℝ K - p with hq
  set Q : Submodule ℝ K := LinearMap.ker (p : K →ₗ[ℝ] K) with hQ
  have hqQ : ∀ x, q x ∈ Q := fun x => by
    change p (x - p x) = 0
    rw [map_sub, hpp, sub_self]
  have hqx : ∀ x ∈ Q, q x = x := fun x hx => by
    change x - p x = x
    have : p x = 0 := hx
    rw [this, sub_zero]
  have hkerq : ∀ x, q x = 0 → x ∈ R := fun x hx => by
    have : x = p x := by
      change x - p x = 0 at hx
      exact (sub_eq_zero.1 hx)
    rw [this]; exact hpR x
  -- `Q ≅ K ⧸ R` is finite-dimensional
  have hfin : FiniteDimensional ℝ Q := by
    have hco' : Module.Finite ℝ (K ⧸ R) := hco
    let φ : Q →ₗ[ℝ] K ⧸ R := R.mkQ.comp Q.subtype
    have hinj : Injective φ := by
      intro x y hxy
      have h1 : R.mkQ (x : K) = R.mkQ (y : K) := hxy
      have h2 : (x : K) - y ∈ R := (Submodule.Quotient.eq R).1 h1
      have h3 : p ((x : K) - y) = (x : K) - y := hpr _ h2
      have h4 : p ((x : K) - y) = 0 := by
        rw [map_sub]
        have hx : p x = 0 := x.2
        have hy : p y = 0 := y.2
        rw [hx, hy, sub_self]
      exact Subtype.ext (sub_eq_zero.1 (h3.symm.trans h4))
    have hsurj : Surjective φ := by
      intro z
      induction z using Submodule.Quotient.induction_on with
      | H x =>
        refine ⟨⟨q x, hqQ x⟩, ?_⟩
        change R.mkQ (q x) = R.mkQ x
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        change x - p x - x ∈ R
        rw [sub_sub_cancel_left]
        exact R.neg_mem (hpR x)
    exact Module.Finite.equiv (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm
  -- `q(D)` is a dense subspace of `Q`, hence all of `Q`
  set D' : Submodule ℝ K := D.map (q : K →ₗ[ℝ] K) with hD'
  have hD'Q : D' ≤ Q := by
    rintro _ ⟨x, -, rfl⟩
    exact hqQ x
  have hD'fin : FiniteDimensional ℝ D' := Submodule.finiteDimensional_of_le hD'Q
  have hD'closed : IsClosed (D' : Set K) := D'.closed_of_finiteDimensional
  have hQD' : ∀ x ∈ Q, x ∈ D' := by
    intro x hx
    have h1 : x ∈ closure (q '' (D : Set K)) := by
      rw [← hqx x hx]
      refine image_closure_subset_closure_image q.continuous ⟨x, ?_, rfl⟩
      rw [hD.closure_eq]; exact mem_univ x
    have h2 : closure (q '' (D : Set K)) ⊆ (D' : Set K) := by
      refine closure_minimal (fun y hy => ?_) hD'closed
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨z, hz, rfl⟩
    exact h2 h1
  -- a finite spanning family of `Q`
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin' ℝ Q
  have hgD' : ∀ i, ((g (Pi.single i 1) : Q) : K) ∈ D' := fun i => hQD' _ (g (Pi.single i 1)).2
  choose d hdD hdq using fun i => (Submodule.mem_map.1 (hgD' i))
  refine ⟨k, d, hdD, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hg ⟨q x, hqQ x⟩
  have hqx' : q x = ∑ i, a i • q (d i) := by
    have h1 : (g a : K) = q x := congrArg Subtype.val ha
    rw [← h1]
    have h2 : a = ∑ i, a i • (Pi.single i 1 : Fin k → ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [h2]
    rw [map_sum]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show q (d i) = (g (Pi.single i 1) : K) from hdq i]
  refine ⟨x - ∑ i, a i • d i, hkerq _ ?_, a, by abel⟩
  rw [map_sub, map_sum]
  simp only [map_smul]
  rw [← hqx', sub_self]

end LinearAlgebra

/-! ### A subspace with an sc-complement inside `T^R_zO` is in good position (Lemma 5.26, the
linear algebra) -/

section GoodPositionCore

variable {E : ScBanach} {n : ℕ} {Wq : ScBanach} {C : Set (E 0)}

/-- **A subspace of `T_zO` with an sc-complement inside `T^R_zO` is in good position to the partial
cone `C_zO` inside `T_zO`** (the linear algebra of Lemma 5.26, with the interior condition of
Definition 3.21 that the text omits): for a tame retraction `r` and a smooth point `z` of the
retract, let `N ⊆ T_zO` and `B ⊆ T^R_zO = T_zO ∩ E_z` with `T_zO = N ⊕ B`.  Then `N` is in good
position to `C_z` inside `T_zO` with good complement `B` (adding a vector of `E_z` does not change
membership in `C_z`), and `N ∩ C_z` has non-empty interior in `N`: the coordinates `λᵢ`,
`i ∈ I(z)`, map `T_zO` onto `ℝ^{I(z)}` (`dim T_zO/T^R_zO = d_C(z)`, Proposition 2.36) and vanish
on `B`, so a vector of `N` with all these coordinates equal to `1` is interior.  (The argument of
`IsGeneralPositionRetractAt.isGoodPositionRetractAt`, `Chapter4/LocalStructure.lean`, for a
subspace that is not given as a tangent space.) -/
theorem isInGoodPositionIn_of_scComplement_le_reduced
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) {R : ScRetraction E C}
    (hR : R.IsTameWith T) {z : E 1} (hz : z ∈ E.lvlSet R.retract 1) (hzs : z ∈ E.smoothLvl 1)
    {N B : Submodule ℝ (E 0)} (hBM : B ≤ reducedTangentSpaceWith R T z) (hNB : N ⊓ B = ⊥)
    (hMNB : N ⊔ B = LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0)) :
    IsInGoodPositionIn E (LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0))
      (partialQuadrantAtWith T (E.toBase 1 z)) N := by
  classical
  set e := E.toBase 1 z with he
  have hBE : ∀ b ∈ B, ∀ i, (T 0 e).1 i = 0 → (T 0 b).1 i = 0 := fun b hb i hi =>
    (mem_minimalSubspaceWith T).1 (hBM hb).2 i hi
  refine ⟨hMNB ▸ le_sup_left, ?_, B, fun b hb => (hBM hb).1, hNB, hMNB, 1, one_pos,
    fun x _ b hb _ => ?_⟩
  · -- interior points: `λ_{I(z)}` maps `M` onto `ℝ^{I(z)}`
    set M := LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0) with hMdef
    set f : M →ₗ[ℝ] ({i : Fin n // (T 0 e).1 i = 0} → ℝ) :=
      (coordMapL T e : E 0 →ₗ[ℝ] _) ∘ₗ M.subtype with hf
    have hker : LinearMap.ker f = (reducedTangentSpaceWith R T z).comap M.subtype := by
      ext ⟨v, hv⟩
      simp only [hf, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
        Submodule.mem_comap, reducedTangentSpaceWith, Submodule.mem_inf]
      exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩
    have hq := quotDim_reducedTangentSpaceWith_eq hR hz hzs
    rw [quotDim, ← hker] at hq
    have hrange : LinearMap.range f = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← (LinearMap.quotKerEquivRange f).finrank_eq, hq, Module.finrank_fintype_fun_eq_card,
        Fintype.card_subtype]
      rfl
    obtain ⟨m, hm⟩ : (fun _ => (1 : ℝ)) ∈ LinearMap.range f := by
      rw [hrange]; exact Submodule.mem_top
    have hmM : (m : E 0) ∈ N ⊔ B := by rw [hMNB]; exact m.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmM
    have ha1 : ∀ i, (T 0 e).1 i = 0 → (T 0 a).1 i = 1 := fun i hi => by
      have h1 := congrFun hm ⟨i, hi⟩
      simp only [hf, LinearMap.comp_apply, Submodule.coe_subtype, ContinuousLinearMap.coe_coe,
        coordMapL_apply] at h1
      rw [← hab, map_add, Prod.fst_add, Pi.add_apply, hBE b hb i hi, add_zero] at h1
      exact h1
    set G : Set N := ⋂ i : {i : Fin n // (T 0 e).1 i = 0}, {u : N | 0 < (T 0 (u : E 0)).1 i}
      with hG
    have hGo : IsOpen G := by
      refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ?_
      exact (continuous_apply _).comp
        (continuous_fst.comp ((T 0).continuous.comp continuous_subtype_val))
    have hGC : G ⊆ Subtype.val ⁻¹' partialQuadrantAtWith T e := fun u hu i hi =>
      (mem_iInter.1 hu ⟨i, hi⟩).le
    have haG : (⟨a, ha⟩ : N) ∈ G := mem_iInter.2 fun i => by
      change 0 < (T 0 a).1 i.1
      rw [ha1 i.1 i.2]; exact one_pos
    exact ⟨_, interior_maximal hGC hGo haG⟩
  · -- `B ⊆ E_z` is a good complement
    change (∀ i, (T 0 e).1 i = 0 → 0 ≤ (T 0 x).1 i) ↔ ∀ i, (T 0 e).1 i = 0 → 0 ≤ (T 0 (x + b)).1 i
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [map_add, Prod.fst_add, Pi.add_apply, hBE b hb i hi, add_zero]

end GoodPositionCore

/-! ### Definitions 5.15 and 5.17, and Lemma 5.26 -/

section Defs

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

variable (B) in
/-- **Definition 5.15**: the section `g` of the strong bundle `P : Y → X` is **transversal to the
zero section** if at every zero `x` the linearization `g'(x) : T_xX → Y_x` is surjective
(`IsLinSurjAt`: `Lin(z) : T_zO → K_z` onto in a strong bundle chart around `x`, hence in every
chart by `StrongBundle.linAt_chart_independence`). -/
def StrongBundle.IsTransversal (g : X → Y) : Prop := ∀ x, IsZeroAt P g x → B.IsLinSurjAt g x

/-- The kernel of the linearization `Lin(z) : T_zO → F` at a point of a strong bundle chart, as a
subspace of `E₀` (contained in `T_zO`). -/
def StrongBundleChart.linKer (c : StrongBundleChart PX P) (f : X → Y) (z : c.φ.model.E 1) :
    Submodule ℝ (c.φ.model.E 0) :=
  (LinearMap.ker (linAt c.U c.R (c.principal f) z :
    ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0)).map (rangeS (scDeriv c.U (r c.R) z)).subtype

variable (B) in
/-- **Definition 5.17 (general position), in a chart**: `(f, y)`, `f(y) = 0`, is **in general
position** if in a tame strong bundle chart `c` around `y` (`IsTameChart`; the reduced tangent
space and Lemma 5.26 are about tame retracts), at a level-`1` point `z` over `φ(y)`,
the linearization `Lin(z) : T_zO → K_z` (`linAt`) is onto, and for every presentation `T` of the
partial quadrant `C` the kernel `ker Lin(z)` has an sc-complement `B` in `T_zO` contained in the
reduced tangent space `T^R_zO = T_zO ∩ E_z` (`reducedTangentSpaceWith`, Definitions 2.27, 2.38):
an sc-subspace `B` with `(T_zO)_m = (ker Lin(z))_m ⊕ B_m` on every level, the form of Definition
4.21 in `Chapter4/Submanifolds.lean`.  (The text states the definition in `T_yX`, gap G.7.) -/
def StrongBundle.IsGeneralPositionGerm (f : X → Y) (y : X) : Prop :=
  ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : y ∈ c.φ.source) (z : c.φ.model.E 1),
    c.φ.model.E.toBase 1 z = c.φ y ∧
    (∀ k, (c.φ y, k) ∈ c.K → ∃ x, linAt c.U c.R (c.principal f) z x = k) ∧
    ∀ {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
      c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0 →
      ∃ Bc : Submodule ℝ (c.φ.model.E 0),
        Bc ≤ reducedTangentSpaceWith (c.isRetraction.baseRetraction c.relOpen) T z ∧
        c.φ.model.E.IsScSubspace Bc ∧
        ∀ m, Disjoint (c.φ.model.E.levelSub (c.linKer f z) m) (c.φ.model.E.levelSub Bc m) ∧
          c.φ.model.E.levelSub (c.linKer f z) m ⊔ c.φ.model.E.levelSub Bc m =
            c.φ.model.E.levelSub (rangeS (scDeriv c.U (r c.R) z)) m

/-- **Definition 5.17 contains the surjectivity**: a germ in general position is transversal at
its point. -/
theorem StrongBundle.IsGeneralPositionGerm.isLinSurjAt {y : X}
    (h : B.IsGeneralPositionGerm f y) : B.IsLinSurjAt f y := by
  obtain ⟨c, hc, hyV, z, hz, hsurj, -⟩ := h
  exact ⟨c, hc.1, hyV, z, hz, hsurj⟩

/-- **Lemma 5.26 (general position implies good position)** ("Clearly general position implies
good position", after Theorem 5.19).  Let `f` be an sc-Fredholm section of a strong bundle,
`f(y) = 0`, and `(f, y)` in general position (Definition 5.17, in a tame chart).  Then `(f, y)` is
in good position (Definition 3.53, `IsGoodPositionGerm`).  *Proof*: in the chart of
Definition 5.17, `Lin(z)` is onto, and `ker Lin(z)` has an sc-complement `B ⊆ T^R_zO`; by
`isInGoodPositionIn_of_scComplement_le_reduced` (the tameness of the chart enters through
`dim T_zO/T^R_zO = d_C(z)`) the kernel is in good position to the partial cone `C_zO` inside
`T_zO`, with the interior condition of Definition 3.21 that the text omits; then
`isGoodPositionGerm_of_linAt_surj` assembles Definition 3.53 in the chart centred at `y`. -/
theorem StrongBundle.IsGeneralPositionGerm.isGoodPositionGerm (hf : B.IsScFredholmSection f)
    {y : X} (hy0 : IsZeroAt P f y) (h : B.IsGeneralPositionGerm f y) :
    B.IsGoodPositionGerm f y := by
  obtain ⟨c, hc, hyV, z, hz, hsurj, hgen⟩ := h
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  obtain ⟨Bc, hBM, -, hsplit⟩ := hgen T hT
  set R := c.isRetraction.baseRetraction c.relOpen with hRdef
  have hRT : R.IsTameWith T := hc.2 n Wq T hT
  have hys : y ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hy0
  have hzR : z ∈ c.φ.model.E.lvlSet R.retract 1 := by
    change c.φ.model.E.toBase 1 z ∈ R.retract
    rw [c.base_retract, hz]; exact c.φ.mapsTo_model y hyV
  have hzs : z ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 z ∈ c.φ.model.E.smooth
    rw [hz]; exact (PX.mem_smoothSet_iff c.isChart hyV).1 hys
  have h0 := hsplit 0
  rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero, ScBanach.levelSub_zero] at h0
  have hker := isInGoodPositionIn_of_scComplement_le_reduced T hRT hzR hzs hBM h0.1.eq_bot h0.2
  rw [hz] at hker
  exact StrongBundle.isGoodPositionGerm_of_linAt_surj hf.isScSmooth (hf.germ y hys) hy0 hc.1 hyV
    hz T hT hsurj hker

/-- **Lemma 5.26 in a tame chart**: for an sc-Fredholm section with tame germ data
(`IsScFredholmSectionTame`, Definition 3.51), a zero in general position is in good position in
the tame chart of its germ data (`IsGeneralPositionGerm.isGoodPositionGerm` and
`IsGoodPositionGerm.toTame`), the form the implicit function theorems of §3.6 take. -/
theorem StrongBundle.IsGeneralPositionGerm.isGoodPositionGermTame
    (hf : B.IsScFredholmSectionTame f) {y : X} (hy0 : IsZeroAt P f y)
    (h : B.IsGeneralPositionGerm f y) : B.IsGoodPositionGermTame f y :=
  (h.isGoodPositionGerm hf.toIsScFredholmSection hy0).toTame hf.isScSmooth
    (hf.germTame y (hf.mem_smoothSet_of_isZeroAt hy0)) hy0

end Defs

/-! ### Spanning sc⁺-sections at a zero (the first step of the proof of Theorem 5.13) -/

section Spanning

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] in
/-- The support of `t·s` is contained in the support of `s`. -/
lemma sectionSupport_sectionSmul_const_subset {s : X → Y} (hs : IsSection P s) (t : ℝ) :
    sectionSupport P (sectionSmul P (fun _ => t) s) ⊆ sectionSupport P s := by
  refine closure_mono fun x hx h0 => hx ?_
  rw [sectionSmul_apply hs]
  have : (⟨s x, hs x⟩ : P ⁻¹' {x}) = 0 := Subtype.ext h0
  rw [this, smul_zero]; rfl

/-- `N((t·s)(x)) = |t|·N(s(x))` for a constant `t` (`N` is a norm on the fibres). -/
lemma StrongBundle.IsAuxNorm.oneMk_sectionSmul_const {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    {s : X → Y} (hs : B.IsScPlusSection s) (t : ℝ) (x : X)
    (hx : sectionSmul P (fun _ => t) s x ∈ B.oneSet) :
    N (B.oneMk _ hx) = |t| * N (B.oneMk (s x) (hs.mem_oneSet x)) := by
  set w : B.oneFiber x := ⟨⟨s x, hs.1 x⟩, hs.mem_oneSet x⟩
  have h1 : B.oneMk (sectionSmul P (fun _ => t) s x) hx = B.toOne (t • w) := by
    apply B.oneVal_injective
    rw [StrongBundle.oneVal_oneMk, StrongBundle.oneVal_toOne]
    exact sectionSmul_apply hs.1 x
  rw [h1, hN.smul]
  rfl

omit [T2Space Y] [ParacompactSpace Y] in
/-- The principal part of `t·s` is `t·ŝ`. -/
lemma principal_sectionSmul_const (c : StrongBundleChart PX P) {s : X → Y} (hs : IsSection P s)
    (t : ℝ) {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) :
    c.principal (sectionSmul P (fun _ => t) s) z = t • c.principal s z := by
  unfold StrongBundleChart.principal
  rw [sectionSmul_apply hs]
  exact (c.fiber_linear _ (c.φ.symm_mapsTo hz)).map_smul t _

/-- A point `Φ⁻¹(z, k)` with `z` and `k` smooth is a smooth point of `Y[0]`. -/
lemma mem_smoothSet_toMPolyfold0_of_chart {c : StrongBundleChart PX P} (hc : B.IsChart c)
    {z : c.φ.model.E 0} {k : c.F 0} (hzk : (z, k) ∈ c.K) (hz : z ∈ c.φ.model.E.smooth)
    (hk : k ∈ c.F.smooth) : c.toPartialEquiv.symm (z, k) ∈ B.toMPolyfold0.smoothSet := by
  refine mem_iInter.2 fun m => ?_
  rw [B.toMPolyfold0.mem_levelSet_iff hc.toMChart (c.symm_mem_source hzk)]
  obtain ⟨z', hz'⟩ := c.φ.model.E.mem_smooth_iff.1 hz m
  obtain ⟨k', hk'⟩ := c.F.mem_smooth_iff.1 hk m
  refine ⟨(z', k'), ?_⟩
  change (c.φ.model.E.prod c.F).toBase m (z', k') = c (c.toPartialEquiv.symm (z, k))
  rw [ScBanach.prod_toBase, hz', hk', c.apply_symm hzk]

/-- **Spanning sc⁺-sections at a zero** (the text: "for every `x ∈ S_{f+s₀}` we find finitely many
allowable sc⁺-sections `s¹_x, …, s^{k_x}_x` such that the range of `(f + s₀)'(x)` together with
the sections `s^j_x` span `Y_x`").  Let `X` admit sc-smooth bump functions, `N` be an auxiliary
norm, `g` an sc-Fredholm section, `y` a zero of `g` and `U ∋ y` open.  Then there are finitely
many sc⁺-sections `s₁, …, s_k` with `supp(sᵢ) ⊆ U` and `N(sᵢ(x)) ≤ 1` for all `x` (allowable),
and a strong bundle chart `c` centred at `y` (the chart of Definition 3.11) in which
`Lin(0)(T₀O) + span{ŝᵢ(0)} = K₀`.  *Proof*: `Lin(0)` is Fredholm (Proposition 3.52), so its range
is closed, complemented and of finite codimension in `K₀ = ρ(0)F`; the smooth vectors
`ρ(0)F_∞ ⊆ K₀ ∩ F_∞` are dense in `K₀`, so finitely many of them span a complement
(`exists_fin_mem_of_dense_of_closedComplemented`); each is `Φ(eᵢ)₂` for a smooth point `eᵢ` of
the fibre over `y`, and Lemma 5.11 gives `sᵢ` with `sᵢ(y) = eᵢ`, `supp(sᵢ) ⊆ U` and
`N(sᵢ(x)) < N(eᵢ) + 1`; rescaling by `1/(N(eᵢ) + 1)` makes the sections allowable.  (The text does
not say how the spanning sections are found; the density of the smooth vectors is the point.) -/
theorem exists_spanning_sections (hbump : PX.AdmitsBumpFunctions) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) {g : X → Y} (hg : B.IsScFredholmSection g) {y : X}
    (hy0 : IsZeroAt P g y) {U : Set X} (hU : IsOpen U) (hyU : y ∈ U) :
    ∃ (k : ℕ) (s : Fin k → X → Y), (∀ i, B.IsScPlusSection (s i)) ∧
      (∀ i, sectionSupport P (s i) ⊆ U) ∧
      (∀ i x (hx : s i x ∈ B.oneSet), N (B.oneMk (s i x) hx) ≤ 1) ∧
      ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : y ∈ c.φ.source) (_ : c.φ y = 0),
        ∀ k', ((0 : c.φ.model.E 0), k') ∈ c.K →
          ∃ (u : ↥(rangeS (scDeriv c.U (r c.R) 0))) (a : Fin k → ℝ),
            linAt c.U c.R (c.principal g) 0 u + ∑ i, a i • c.principal (s i) 0 = k' := by
  classical
  have hgs : IsSection P g := hg.isScSmooth.1
  have hys : y ∈ PX.smoothSet := hg.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨c, hc, hyV, hφ0, h0U, gf, hfill, G, -, -, Dg, hDg, h1, n, Nn, -, -, hFred, -⟩ :=
    proposition_3_52 hgs (hg.germ y hys) hy0
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model y hyV
  have hfr : IsSc1 c.U (c.principal g ∘ r c.R) := hg.isScSmooth.isSc1_principal_comp_r hc
  set L := fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0U) (Dg 0) h1
    with hLdef
  have hL : ∀ x, (L x : c.F 0) = linAt c.U c.R (c.principal g) 0 x := fun x =>
    hfill.fillerRestrict_eq_linAt c.relOpen c.isRetraction h0O hfr hDg h1 x
  have : CompleteSpace ↥(rangeS (ρCLM c.isRetraction h0U)) :=
    (isClosed_range_of_idem _ fun k => ρ_ρ c.isRetraction h0O k).completeSpace_coe
  -- the smooth vectors of `K₀` are dense
  have hρsm : ∀ h ∈ c.F.smooth, ρCLM c.isRetraction h0U h ∈ c.F.smooth := by
    intro h hh
    refine c.F.mem_smooth_iff.2 fun m => ?_
    obtain ⟨h', hh'⟩ := c.F.mem_smooth_iff.1 hh m
    exact (c.isRetraction.preserves_filtration m m (Nat.le_succ m) 0 h0U ⟨0, map_zero _⟩ h
      ⟨h', hh'⟩).2
  set D : Submodule ℝ ↥(rangeS (ρCLM c.isRetraction h0U)) :=
    c.F.smooth.comap (rangeS (ρCLM c.isRetraction h0U)).subtype with hDdef
  have hD : Dense (D : Set ↥(rangeS (ρCLM c.isRetraction h0U))) := by
    set ρ' : c.F 0 → ↥(rangeS (ρCLM c.isRetraction h0U)) :=
      fun h => ⟨ρCLM c.isRetraction h0U h, ⟨h, rfl⟩⟩ with hρ'
    have hcont : Continuous ρ' := (ρCLM c.isRetraction h0U).continuous.subtype_mk _
    have hdr : DenseRange ρ' := by
      refine Function.Surjective.denseRange ?_
      rintro ⟨k, k', hk'⟩
      exact ⟨k', Subtype.ext hk'⟩
    have hsm : Dense (c.F.smooth : Set (c.F 0)) := c.F.dense_smooth 0
    refine (hdr.dense_image hcont hsm).mono ?_
    rintro _ ⟨h, hh, rfl⟩
    exact hρsm h hh
  obtain ⟨k, d, hdD, hspan⟩ := exists_fin_mem_of_dense_of_closedComplemented
    hFred.closedComplemented_range hFred.finite_coker hD
  -- the vectors `eᵢ = dᵢ ∈ K₀ ∩ F_∞` as smooth points of `Y`
  have hdK : ∀ i, ((0 : c.φ.model.E 0), (d i : c.F 0)) ∈ c.K := fun i =>
    (mem_rangeS_ρCLM_iff c.isRetraction h0O h0U).1 (d i).2
  have hdsm : ∀ i, (d i : c.F 0) ∈ c.F.smooth := fun i => hdD i
  have hφsymm0 : c.φ.symm 0 = y := by rw [← hφ0]; exact c.φ.symm_apply_apply hyV
  set e : Fin k → Y := fun i => c.toPartialEquiv.symm (0, (d i : c.F 0)) with hedef
  have hPe : ∀ i, P (e i) = y := fun i => by
    change P (c.toPartialEquiv.symm (0, (d i : c.F 0))) = y
    rw [c.proj_symm (hdK i)]; exact hφsymm0
  have hesm : ∀ i, e i ∈ B.toMPolyfold0.smoothSet := fun i =>
    mem_smoothSet_toMPolyfold0_of_chart hc (hdK i) c.φ.model.E.smooth.zero_mem (hdsm i)
  -- Lemma 5.11 at each `eᵢ`
  have hsec : ∀ i, ∃ he1 : e i ∈ B.oneSet, ∃ s : X → Y, B.IsScPlusSection s ∧ s y = e i ∧
      sectionSupport P s ⊆ U ∧
      ∀ x (hx : s x ∈ B.oneSet), N (B.oneMk (s x) hx) < N (B.oneMk (e i) he1) + 1 :=
    fun i => lemma_5_11 hbump hN hys (hesm i) (hPe i) one_pos hU hyU
  choose he1 s hs hsy hssupp hsN using hsec
  -- rescale by `1/Mᵢ`, `Mᵢ = N(eᵢ) + 1`
  set M : Fin k → ℝ := fun i => N (B.oneMk (e i) (he1 i)) + 1 with hMdef
  have hMpos : ∀ i, 0 < M i := fun i => by
    have := hN.nonneg (B.oneMk (e i) (he1 i))
    simp only [hMdef]; linarith
  set s' : Fin k → X → Y := fun i => sectionSmul P (fun _ => (M i)⁻¹) (s i) with hs'def
  refine ⟨k, s', fun i => (hs i).smul_left (isScSmoothMap_real_const _),
    fun i => (sectionSupport_sectionSmul_const_subset (hs i).1 _).trans (hssupp i),
    fun i x hx => ?_, c, hc, hyV, hφ0, fun k' hk' => ?_⟩
  · rw [hN.oneMk_sectionSmul_const (hs i) _ x hx, abs_of_pos (inv_pos.2 (hMpos i))]
    have := hsN i x ((hs i).mem_oneSet x)
    calc (M i)⁻¹ * N (B.oneMk (s i x) ((hs i).mem_oneSet x)) ≤ (M i)⁻¹ * M i :=
          mul_le_mul_of_nonneg_left this.le (inv_pos.2 (hMpos i)).le
      _ = 1 := inv_mul_cancel₀ (hMpos i).ne'
  · -- the spanning
    have hk'K : k' ∈ rangeS (ρCLM c.isRetraction h0U) :=
      (mem_rangeS_ρCLM_iff c.isRetraction h0O h0U).2 hk'
    obtain ⟨rr, hrr, a, hk'eq⟩ := hspan ⟨k', hk'K⟩
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hrr
    refine ⟨u, fun i => a i * M i, ?_⟩
    have h0O' : (0 : c.φ.model.E 0) ∈ c.φ.model.O := by
      rw [← hφ0]; exact c.φ.mapsTo_model y hyV
    have hprin : ∀ i, c.principal (s' i) 0 = (M i)⁻¹ • (d i : c.F 0) := fun i => by
      change c.principal (sectionSmul P (fun _ => (M i)⁻¹) (s i)) 0 = _
      rw [principal_sectionSmul_const c (hs i).1 _ h0O']
      unfold StrongBundleChart.principal
      rw [hφsymm0, hsy i]
      change (M i)⁻¹ • (c (c.toPartialEquiv.symm (0, (d i : c.F 0)))).2 = _
      rw [c.apply_symm (hdK i)]
    have hval : k' = (rr : c.F 0) + ∑ i, a i • (d i : c.F 0) := by
      have := congrArg Subtype.val hk'eq
      simpa using this
    have hu' : (rr : c.F 0) = linAt c.U c.R (c.principal g) 0 u := by
      rw [← hu]; exact hL u
    rw [hval, hu']
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hprin i, smul_smul, mul_assoc, mul_inv_cancel₀ (hMpos i).ne', mul_one]

end Spanning

/-! ### The parametrized section `F(λ, y) = g(y) + Σ λᵢ tᵢ(y)` and its slices -/

section Param

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

open StrongRetr

/-- **The slice `g + Σ λᵢ tᵢ`** of the parametrized section `F(λ, y) = g(y) + Σ λᵢ tᵢ(y)` of
Theorem 3.18 at the parameter `λ`: the section `y ↦ F(λ, y)` of `P` (the text's
`f + s₀ + s(λ₀, ·)`). -/
def paramSlice (g : X → Y) (hg : IsSection P g) (t : Fin m → X → Y)
    (ht : ∀ i, IsSection P (t i)) (lam : Fin m → ℝ) (y : X) : Y :=
  (((⟨g y, hg y⟩ : P ⁻¹' {y}) + fiberComb t ht (lam, y) : P ⁻¹' {y}) : Y)

variable {g : X → Y} {hg : IsSection P g} {t : Fin m → X → Y} {ht : ∀ i, IsSection P (t i)}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
lemma isSection_paramSlice (lam : Fin m → ℝ) : IsSection P (paramSlice g hg t ht lam) :=
  fun y => ((⟨g y, hg y⟩ : P ⁻¹' {y}) + fiberComb t ht (lam, y) : P ⁻¹' {y}).2

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `F(z) = (z, F(λ, y))` in `π*Y ⊆ (ℝᵐ × X) × Y`. -/
lemma paramSection_val (z : (Fin m → ℝ) × X) :
    (paramSection g hg t ht z : ((Fin m → ℝ) × X) × Y) = (z, paramSlice g hg t ht z.1 z.2) := rfl

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- **The zeros of `F`** are the pairs `(λ, y)` with `y` a zero of the slice `g + Σ λᵢ tᵢ`. -/
lemma isZeroAt_paramSection_iff (z : (Fin m → ℝ) × X) :
    IsZeroAt (pullbackProj P Prod.snd) (paramSection g hg t ht) z ↔
      IsZeroAt P (paramSlice g hg t ht z.1) z.2 := by
  rw [IsZeroAt, IsZeroAt, Subtype.ext_iff, paramSection_val]
  change (z, paramSlice g hg t ht z.1 z.2) = (z, fiberZero P z.2) ↔ _
  rw [Prod.mk.injEq]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- The slice is `g + Σ λᵢ·tᵢ`, as a global section (`sectionAdd`, `sectionSum`, `sectionSmul`). -/
lemma paramSlice_eq_sectionAdd (lam : Fin m → ℝ) :
    paramSlice g hg t ht lam =
      sectionAdd P g (sectionSum P Finset.univ fun i => sectionSmul P (fun _ => lam i) (t i)) := by
  classical
  funext y
  have hsm : ∀ i, IsSection P (sectionSmul P (fun _ => lam i) (t i)) := fun i =>
    (ht i).sectionSmul
  have hsum :
    IsSection P (sectionSum P Finset.univ fun i => sectionSmul P (fun _ => lam i) (t i)) :=
    fun x => by
      rw [sectionSum_apply hsm]
      exact ((∑ i, (⟨_, hsm i x⟩ : P ⁻¹' {x}) : P ⁻¹' {x})).2
  have hfc : (⟨sectionSum P Finset.univ (fun i => sectionSmul P (fun _ => lam i) (t i)) y,
      hsum y⟩ : P ⁻¹' {y}) = fiberComb t ht (lam, y) := by
    apply Subtype.ext
    change sectionSum P Finset.univ (fun i => sectionSmul P (fun _ => lam i) (t i)) y =
      ((fiberComb t ht (lam, y) : P ⁻¹' {y}) : Y)
    rw [sectionSum_apply hsm]
    congr 1
    unfold fiberComb
    exact Finset.sum_congr rfl fun i _ =>
      Subtype.ext (sectionSmul_apply (f := fun _ => lam i) (ht i) y)
  rw [sectionAdd_apply hg hsum, hfc]
  rfl

variable {B : StrongBundle PX P}

/-- **The slices are sc-Fredholm sections** (Theorem 3.15: `Σ λᵢ tᵢ` is an sc⁺-section). -/
theorem isScFredholmSection_paramSlice (hgF : B.IsScFredholmSection g)
    (htp : ∀ i, B.IsScPlusSection (t i)) (lam : Fin m → ℝ) :
    B.IsScFredholmSection (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) lam) := by
  rw [paramSlice_eq_sectionAdd]
  exact theorem_3_15 hgF (StrongBundle.isScPlusSection_sectionSum _ fun i =>
    (htp i).smul_left (isScSmoothMap_real_const _))

omit [T2Space Y] [ParacompactSpace Y] in
/-- The principal part of the slice: `ĝ + Σ λᵢ t̂ᵢ` on `O`. -/
lemma principal_paramSlice (c : StrongBundleChart PX P) (lam : Fin m → ℝ) {z : c.φ.model.E 0}
    (hz : z ∈ c.φ.model.O) :
    c.principal (paramSlice g hg t ht lam) z =
      c.principal g z + ∑ i, lam i • c.principal (t i) z := by
  have hx : c.φ.symm z ∈ c.φ.source := c.φ.symm_mapsTo hz
  unfold StrongBundleChart.principal paramSlice
  rw [c.snd_add hx]
  congr 1
  set Lf : P ⁻¹' {c.φ.symm z} →ₗ[ℝ] c.F 0 := IsLinearMap.mk' _ (c.fiber_linear _ hx) with hLf
  change Lf (fiberComb t ht (lam, c.φ.symm z)) = ∑ i, lam i • Lf ⟨t i (c.φ.symm z), ht i _⟩
  unfold fiberComb
  rw [map_sum]
  simp only [map_smul]

end Param

/-! ### The linearization of a slice from the linearization of `F` in the product chart -/

section ParamLin

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- `Lin(z)` depends only on the principal part on `O = r(U)`. -/
lemma linAt_congr (hU : IsRelOpenInQuadrant E C U) {f₁ f₂ : E 0 → F 0}
    (hf₁ : IsSc1 U (f₁ ∘ r R)) (hf₂ : IsSc1 U (f₂ ∘ r R)) (heq : ∀ u ∈ r R '' U, f₁ u = f₂ u)
    {z : E 1} (hz : z ∈ E.lvlSet U 1) (x : ↥(rangeS (scDeriv U (r R) z))) :
    linAt U R f₁ z x = linAt U R f₂ z x := by
  have hEq : EqOn (f₁ ∘ r R) (f₂ ∘ r R) U := fun u hu => heq _ ⟨u, hu, rfl⟩
  simp only [linAt_apply]
  rw [scDeriv_eq_of_eqOn_relOpen hU hf₁ hf₂ subset_rfl subset_rfl hEq hz]

end ParamLin

section ParamChart

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin m → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
  {B : StrongBundle PX P}

open StrongRetr

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))] in
/-- The product chart `(r ↦ r − r₀) × φ` at `(r₀, y)` is centred there when `φ(y) = 0`. -/
lemma ofProd_apply_eq_zero (c : StrongBundleChart PX P) (r₀ : Fin m → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)) {y : X} (hφ0 : c.φ y = 0) :
    ((PullbackChartData.ofProd c r₀).toChart q₀).φ (r₀, y) = 0 :=
  Prod.ext (sub_self _) hφ0

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))] in
/-- **The fibre of the product chart over `(0, 0)`** is the fibre `K₀` of `c`:
`((0, 0), k) ∈ K_g ↔ (0, k) ∈ K` (`g(0, 0) = φ(φ⁻¹(0)) = 0`). -/
lemma mem_K_ofProd_zero_iff (c : StrongBundleChart PX P) (r₀ : Fin m → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))
    (h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O) (k : c.F 0) :
    ((0 : ((PullbackChartData.ofProd c r₀).toChart q₀).φ.model.E 0), k) ∈
      ((PullbackChartData.ofProd c r₀).toChart q₀).K ↔ (0, k) ∈ c.K := by
  change _ ∈ pullbackRetraction (PullbackChartData.ofProd c r₀).c.R
    (PullbackChartData.ofProd c r₀).RZ
    (PullbackChartData.ofProd c r₀).g '' ((PullbackChartData.ofProd c r₀).RZ.U ×ˢ univ) ↔ _
  rw [(PullbackChartData.ofProd c r₀).image_eq_Kg]
  have hg0 : (PullbackChartData.ofProd c r₀).g 0 = 0 := by
    change c.φ (((rnChart m r₀).prod c.φ).symm 0).2 = 0
    rw [MChart.prod_symm_apply]
    exact c.φ.apply_symm_apply h0O
  have h0R : (0 : ((PullbackChartData.ofProd c r₀).toChart q₀).φ.model.E 0) ∈
      (PullbackChartData.ofProd c r₀).RZ.retract := by
    rw [(PullbackChartData.ofProd c r₀).RZ_retract]
    exact ⟨mem_univ _, h0O⟩
  change (0 : ((PullbackChartData.ofProd c r₀).toChart q₀).φ.model.E 0) ∈
      (PullbackChartData.ofProd c r₀).RZ.retract ∧
      ((PullbackChartData.ofProd c r₀).g 0, k) ∈ c.K ↔ _
  rw [hg0]
  exact ⟨fun h => h.2, fun h => ⟨h0R, h⟩⟩

/-- **Transversality of a slice from the linearization of `F` in the product chart** (the text's
"it is easily verified that `f + s₀ + s(λ₀, ·)` is transversal to the zero section", in the
direction needed for Theorem 5.13).  Let `g` be sc-Fredholm, `tᵢ` sc⁺-sections, `y` a zero of the
slice `g_λ = g + Σ λᵢ tᵢ`, and `c` a strong bundle chart centred at `y`.  If the linearization of
`F` at `(λ, y)` is onto (`IsLinSurjAt`, in any chart) and the kernel of `Lin_F(0)` in the product
chart `(r ↦ r − λ) × Φ` projects onto `ℝᵐ` (every `a ∈ ℝᵐ` is the `ℝᵐ`-component of a kernel
vector), then `g_λ'(y)` is onto in `c`.  *Proof*: `Lin_F(0)(a, u) = Lin_{g_λ}(0)u + Σ aᵢ t̂ᵢ(0)`
(`linAt_paramSection`) and `surjective_of_forall_exists_ker_fst`. -/
theorem isLinSurjAt_paramSlice_of_ker_fst (hgF : B.IsScFredholmSection g)
    (htp : ∀ i, B.IsScPlusSection (t i)) {c : StrongBundleChart PX P} (hc : B.IsChart c) {y : X}
    (hyV : y ∈ c.φ.source) (hφ0 : c.φ y = 0) (lam : Fin m → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))
    (hy0 : IsZeroAt P (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) lam) y)
    (hsurj : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsLinSurjAt
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) (lam, y))
    (hker : ∀ a : Fin m → ℝ, ∃ (w : (Fin m → ℝ) × c.φ.model.E 0)
      (hw : w ∈ rangeS (scDeriv ((PullbackChartData.ofProd c lam).toChart q₀).U
        (r ((PullbackChartData.ofProd c lam).toChart q₀).R) 0)),
        w.1 = a ∧
        linAt ((PullbackChartData.ofProd c lam).toChart q₀).U
          ((PullbackChartData.ofProd c lam).toChart q₀).R
          (((PullbackChartData.ofProd c lam).toChart q₀).principal
            (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1)) 0 ⟨w, hw⟩ = 0) :
    B.IsLinSurjAt (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) lam) y := by
  have hχc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart
      ((PullbackChartData.ofProd c lam).toChart q₀) :=
    (PullbackChartData.ofProd c lam).isChart_toChart B _ hc q₀
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := by
    rw [← hφ0]; exact c.φ.mapsTo_model y hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U :=
    mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hzV' : (lam, y) ∈ ((PullbackChartData.ofProd c lam).toChart q₀).φ.source :=
    ⟨mem_univ _, hyV⟩
  have hχ0 : ((PullbackChartData.ofProd c lam).toChart q₀).φ (lam, y) = 0 :=
    ofProd_apply_eq_zero c lam q₀ hφ0
  have hz' : ((PullbackChartData.ofProd c lam).toChart q₀).φ.model.E.toBase 1
      (0 : ((PullbackChartData.ofProd c lam).toChart q₀).φ.model.E 1) =
      ((PullbackChartData.ofProd c lam).toChart q₀).φ (lam, y) := by
    rw [map_zero, hχ0]
  have hFz : IsZeroAt (pullbackProj P Prod.snd)
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) (lam, y) :=
    (isZeroAt_paramSection_iff (lam, y)).2 hy0
  have hFsm := (theorem_3_18 hgF htp).isScSmooth
  have hsurjχ := hsurj.linAt_surjective hFsm hFz hχc hzV' hz'
  -- the linearization of the slice in `c`, and the formula for `Lin_F(0)`
  have hglF : B.IsScFredholmSection (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) lam) :=
    isScFredholmSection_paramSlice hgF htp lam
  have hfr₁ :
    IsSc1 c.U ((fun u => c.principal g u + ∑ i, lam i • c.principal (t i) u) ∘ r c.R) := by
    have hfr : IsScSmooth c.U (c.principal g ∘ r c.R) :=
      (((hgF.isScSmooth.isScSmoothRetractMap hc).comp_isScSmooth
        (c.isRetraction.baseRetraction c.relOpen) c.base_retract).snd
          c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl
    have hsr : ∀ i, IsScSmooth c.U (c.principal (t i) ∘ r c.R) := fun i => by
      have hlift : IsScSmooth (F := c.F.shift) c.U
          fun u => c.principalLift (t i) (r c.R u) :=
        ((((htp i).isScSmoothRetractMap_one hc).comp_isScSmooth
          (c.isRetraction.baseRetraction c.relOpen) c.base_retract).snd
            c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl
      exact (hlift.toBase_shift c.relOpen.isScDomain).congr c.relOpen.isScDomain
        fun u hu => (htp i).toBase_principalLift hc (c.r_mem_O hu)
    have hconst : ∀ i, IsScSmooth (F := ScBanach.const ℝ) c.U fun _ => lam i := fun i =>
      IsScSmooth.of_contDiffOn_finiteDimensional c.relOpen.isScDomain contDiffOn_const
    exact ((hfr.add c.relOpen.isScDomain (IsScSmooth.finsetSum c.relOpen.isScDomain _
      fun i _ => (hconst i).smul c.relOpen.isScDomain (hsr i))).congr c.relOpen.isScDomain
        fun _ _ => rfl).isSc1
  have hfr₂ : IsSc1 c.U (c.principal (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) lam) ∘
      r c.R) := hglF.isScSmooth.isSc1_principal_comp_r hc
  have h01 : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  have hLeq : ∀ v, linAt c.U c.R (fun u => c.principal g u + ∑ i, lam i • c.principal (t i) u) 0 v =
      linAt c.U c.R (c.principal (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) lam)) 0 v :=
    fun v => linAt_congr c.relOpen hfr₁ hfr₂
      (fun u hu => (principal_paramSlice c lam (c.r_image ▸ hu)).symm) h01 v
  -- `Lin_F(0)(a, u) = L u + Σ aᵢ eᵢ`
  have hform : ∀ (w : (Fin m → ℝ) × c.φ.model.E 0)
      (hw : w ∈ rangeS (scDeriv ((PullbackChartData.ofProd c lam).toChart q₀).U
        (r ((PullbackChartData.ofProd c lam).toChart q₀).R) 0)),
      linAt ((PullbackChartData.ofProd c lam).toChart q₀).U
        ((PullbackChartData.ofProd c lam).toChart q₀).R
        (((PullbackChartData.ofProd c lam).toChart q₀).principal
          (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1)) 0 ⟨w, hw⟩ =
        linAt c.U c.R (c.principal (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) lam)) 0
          ⟨w.2, PullbackChartData.ofProd_mem_tangent c lam q₀ h0U hw⟩ +
          ∑ i, w.1 i • c.principal (t i) 0 := fun w hw => by
    rw [linAt_paramSection hgF htp hc h0O lam q₀ hw, hLeq]
  -- the two hypotheses of the linear algebra
  have hM : ∀ k, (0, k) ∈ c.K → ∃ (a : Fin m → ℝ) (u : ↥(rangeS (scDeriv c.U (r c.R) 0))),
      linAt c.U c.R (c.principal (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) lam)) 0 u +
        ∑ i, a i • c.principal (t i) 0 = k := by
    intro k hk
    have hkχ : (((PullbackChartData.ofProd c lam).toChart q₀).φ (lam, y), k) ∈
        ((PullbackChartData.ofProd c lam).toChart q₀).K := by
      rw [hχ0]; exact (mem_K_ofProd_zero_iff c lam q₀ h0O k).2 hk
    obtain ⟨⟨w, hw⟩, hwk⟩ := hsurjχ k hkχ
    exact ⟨w.1, ⟨w.2, PullbackChartData.ofProd_mem_tangent c lam q₀ h0U hw⟩,
      (hform w hw).symm.trans hwk⟩
  have hker' : ∀ a : Fin m → ℝ, ∃ u : ↥(rangeS (scDeriv c.U (r c.R) 0)),
      linAt c.U c.R (c.principal (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) lam)) 0 u +
        ∑ i, a i • c.principal (t i) 0 = 0 := by
    intro a
    obtain ⟨w, hw, hwa, hw0⟩ := hker a
    refine ⟨⟨w.2, PullbackChartData.ofProd_mem_tangent c lam q₀ h0U hw⟩, ?_⟩
    rw [← hwa, ← hform w hw]
    exact hw0
  refine ⟨c, hc, hyV, 0, by rw [map_zero, hφ0], fun k hk => ?_⟩
  rw [hφ0] at hk
  obtain ⟨a, u, hu⟩ := hM k hk
  obtain ⟨u', hu'⟩ := hker' a
  refine ⟨u - u', ?_⟩
  rw [map_sub, ← hu, eq_neg_of_add_eq_zero_left hu', sub_neg_eq_add]

/-- **Transversality of `F` at `(0, y)` from spanning sections at `y`** (the text: "the
linearization at the point `(0, x)` is surjective"): if in a chart `c` centred at the zero `y`
of `g` the range of `Lin_g(0)` and the vectors `t̂ᵢ(0)` span `K₀`, then the linearization of
`F(λ, y) = g(y) + Σ λᵢ tᵢ(y)` at `(0, y)` is onto (in the product chart, by
`linAt_paramSection_zero` and `D(1 × r)(0) = 1 × Dr(0)`). -/
theorem isLinSurjAt_paramSection_zero_of_spanning (hgF : B.IsScFredholmSection g)
    (htp : ∀ i, B.IsScPlusSection (t i)) {c : StrongBundleChart PX P} (hc : B.IsChart c) {y : X}
    (hyV : y ∈ c.φ.source) (hφ0 : c.φ y = 0)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))
    (hspan : ∀ k', ((0 : c.φ.model.E 0), k') ∈ c.K →
      ∃ (u : ↥(rangeS (scDeriv c.U (r c.R) 0))) (a : Fin m → ℝ),
        linAt c.U c.R (c.principal g) 0 u + ∑ i, a i • c.principal (t i) 0 = k') :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsLinSurjAt
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) (0, y) := by
  have hχc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart
      ((PullbackChartData.ofProd c 0).toChart q₀) :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc q₀
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := by
    rw [← hφ0]; exact c.φ.mapsTo_model y hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U :=
    mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hzV' : (0, y) ∈ ((PullbackChartData.ofProd c 0).toChart q₀).φ.source :=
    ⟨mem_univ _, hyV⟩
  have hχ0 : ((PullbackChartData.ofProd c 0).toChart q₀).φ (0, y) = 0 :=
    ofProd_apply_eq_zero c 0 q₀ hφ0
  refine ⟨_, hχc, hzV', 0, by rw [map_zero, hχ0], fun k hk => ?_⟩
  rw [hχ0] at hk
  obtain ⟨u, a, hua⟩ := hspan k ((mem_K_ofProd_zero_iff c 0 q₀ h0O k).1 hk)
  obtain ⟨u₀, hu₀⟩ := u.2
  have hw : ((a, (u : c.φ.model.E 0)) : (Fin m → ℝ) × c.φ.model.E 0) ∈
      rangeS (scDeriv ((PullbackChartData.ofProd c 0).toChart q₀).U
        (r ((PullbackChartData.ofProd c 0).toChart q₀).R) 0) := by
    refine ⟨(a, u₀), ?_⟩
    exact (PullbackChartData.ofProd_scDeriv_r c 0 q₀ h0U (a, u₀)).trans (Prod.ext rfl hu₀)
  refine ⟨⟨_, hw⟩, ?_⟩
  rw [linAt_paramSection_zero hgF htp hc h0O q₀ hw]
  exact hua

end ParamChart

/-! ### `ℝᵐ × X` has no boundary when `X` has none; the solution set is closed -/

section Boundaryless

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- `d_{ℝᵐ} ≡ 0` (the chart `id` of `ℝᵐ` has `C = ℝᵐ`, no half-line coordinates). -/
lemma rnPolyfold_degIndex (m : ℕ) (a : Fin m → ℝ) : (rnPolyfold m).degIndex a = 0 := by
  refine Nat.le_zero.1 (((rnPolyfold m).degIndex_le (isChart_rnChart (n := m) 0)
    (show a ∈ (rnChart m 0).source from mem_univ a)).trans ?_)
  change Polyfold.degIndex (rnSc m) univ (a - 0) ≤ 0
  rw [degIndex_eq (rnPres m) rnPres_eq (mem_univ _)]
  simp [degIndexWith, quadrantDeg]

/-- **`ℝᵐ × X` has no boundary when `X` has none** (`d_{ℝᵐ × X} ≤ d_{ℝᵐ} + d_X`, exposition
Lemma 4.D, `MPolyfold.degIndex_prod_le`). -/
theorem isWithoutBoundary_prod_rn (m : ℕ) [ParacompactSpace ((Fin m → ℝ) × X)]
    (hX : PX.IsWithoutBoundary) : ((rnPolyfold m).prod PX).IsWithoutBoundary := by
  rintro ⟨a, x⟩
  have := MPolyfold.degIndex_prod_le (rnPolyfold m) PX a x
  rw [rnPolyfold_degIndex, hX x] at this
  exact Nat.le_zero.1 this

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **The solution set of an sc-smooth section is closed** (`X` is metrizable, and a limit of
zeros is a zero, `IsScSmoothSection.isZeroAt_of_tendsto`). -/
theorem isClosed_solutionSet {f : X → Y} (hf : B.IsScSmoothSection f) :
    IsClosed (solutionSet P f) := by
  have := PX.metrizableSpace
  let _ := TopologicalSpace.metrizableSpaceMetric X
  exact IsSeqClosed.isClosed fun x y hx hlim => hf.isZeroAt_of_tendsto hx hlim

end Boundaryless

/-! ### A finite subfamily spans; the open set of zeros in good position; the small parameters -/

section Cover

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y}

open StrongRetr

/-- A linear combination over a subfamily `v ∘ ι` is a linear combination over the family. -/
lemma exists_sum_comp_eq {ι₁ ι₂ M : Type*} [Fintype ι₁] [Fintype ι₂] [AddCommGroup M]
    [Module ℝ M] (ι : ι₁ → ι₂) (a : ι₁ → ℝ) (v : ι₂ → M) :
    ∃ a' : ι₂ → ℝ, ∑ j, a' j • v j = ∑ i, a i • v (ι i) := by
  classical
  refine ⟨fun j => ∑ i ∈ Finset.univ.filter (fun i => ι i = j), a i, ?_⟩
  simp_rw [Finset.sum_smul]
  rw [← Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (ι i))
    (fun i => a i • v (ι i))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.1 hi).2]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- The slice at `λ = 0` is `g`. -/
lemma paramSlice_zero {m : ℕ} (hg : IsSection P g) {t : Fin m → X → Y}
    (ht : ∀ i, IsSection P (t i)) : paramSlice g hg t ht 0 = g := by
  funext y
  change ((((⟨g y, hg y⟩ : P ⁻¹' {y}) + fiberComb t ht (0, y)) : P ⁻¹' {y}) : Y) = g y
  have : fiberComb t ht (0, y) = 0 := by
    unfold fiberComb
    exact Finset.sum_eq_zero fun i _ => zero_smul ℝ _
  rw [this, add_zero]

/-- **Adding sections keeps the transversality of `F` at `(0, y)`** (the text: "adding more
sections, the properties (i)–(ii) will still hold", proof of Theorem 5.18, used implicitly in the
proof of Theorem 5.13 when the finitely many families are united): if the parametrized section of
a subfamily `s`, `sᵢ = t_{ι(i)}`, is transversal at `(0, y)`, so is the parametrized section of
`t`.  In the chart of Definition 3.11 centred at `y`, `Lin_g(0)(T₀O) + span{t̂_{ι(i)}(0)} = K₀`
implies `Lin_g(0)(T₀O) + span{t̂_j(0)} = K₀`. -/
theorem isLinSurjAt_paramSection_zero_of_comp {k m : ℕ} [ParacompactSpace ((Fin k → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
    [ParacompactSpace ((Fin m → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
    (hgF : B.IsScFredholmSection g) {t : Fin m → X → Y} (htp : ∀ i, B.IsScPlusSection (t i))
    (ι : Fin k → Fin m) {s : Fin k → X → Y} (hsp : ∀ i, B.IsScPlusSection (s i))
    (hs_eq : ∀ i, s i = t (ι i)) {y : X} (hy0 : IsZeroAt P g y)
    (hs : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsLinSurjAt
      (paramSection g hgF.isScSmooth.1 s fun i => (hsp i).1) (0, y)) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsLinSurjAt
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) (0, y) := by
  have hys : y ∈ PX.smoothSet := hgF.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨-, c, hc, hyV, hφ0, -⟩ := hgF.germ y hys
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := by
    rw [← hφ0]; exact c.φ.mapsTo_model y hyV
  set q₀ := paramSection g hgF.isScSmooth.1 s (fun i => (hsp i).1) (0, y) with hq₀
  have hχc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsChart
      ((PullbackChartData.ofProd c 0).toChart q₀) :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc q₀
  have hzV' : (0, y) ∈ ((PullbackChartData.ofProd c 0).toChart q₀).φ.source :=
    ⟨mem_univ _, hyV⟩
  have hχ0 : ((PullbackChartData.ofProd c 0).toChart q₀).φ (0, y) = 0 :=
    ofProd_apply_eq_zero c 0 q₀ hφ0
  have hz' : ((PullbackChartData.ofProd c 0).toChart q₀).φ.model.E.toBase 1
      (0 : ((PullbackChartData.ofProd c 0).toChart q₀).φ.model.E 1) =
      ((PullbackChartData.ofProd c 0).toChart q₀).φ (0, y) := by
    rw [map_zero, hχ0]
  have hFz : IsZeroAt (pullbackProj P Prod.snd)
      (paramSection g hgF.isScSmooth.1 s fun i => (hsp i).1) (0, y) := by
    rw [isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice g hgF.isScSmooth.1 s (fun i => (hsp i).1) 0) y
    rw [paramSlice_zero]; exact hy0
  have hFsm := (theorem_3_18 hgF hsp).isScSmooth
  have hsχ := hs.linAt_surjective hFsm hFz hχc hzV' hz'
  -- spanning for the subfamily, in `c`
  have hspan : ∀ k', ((0 : c.φ.model.E 0), k') ∈ c.K →
      ∃ (u : ↥(rangeS (scDeriv c.U (r c.R) 0))) (a : Fin m → ℝ),
        linAt c.U c.R (c.principal g) 0 u + ∑ j, a j • c.principal (t j) 0 = k' := by
    intro k' hk'
    have hkχ : (((PullbackChartData.ofProd c 0).toChart q₀).φ (0, y), k') ∈
        ((PullbackChartData.ofProd c 0).toChart q₀).K := by
      rw [hχ0]; exact (mem_K_ofProd_zero_iff c 0 q₀ h0O k').2 hk'
    obtain ⟨⟨w, hw⟩, hwk⟩ := hsχ k' hkχ
    rw [linAt_paramSection_zero hgF hsp hc h0O q₀ hw] at hwk
    obtain ⟨a', ha'⟩ := exists_sum_comp_eq ι w.1 fun j => c.principal (t j) 0
    refine ⟨⟨w.2, PullbackChartData.ofProd_mem_tangent c 0 q₀
      (mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)) hw⟩, a', ?_⟩
    rw [ha']
    refine Eq.trans ?_ hwk
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hs_eq i]
  exact isLinSurjAt_paramSection_zero_of_spanning hgF htp hc hyV hφ0
    (paramSection g hgF.isScSmooth.1 t (fun i => (htp i).1) (0, y)) hspan

/-- **The zeros of `F` near `{0} × S_g` are in good position** (the text: "by the implicit
function theorem we find an open neighbourhood `U ⊆ ℝᵐ ⊕ X` of `{0} × S_{f+s₀}` such that the
section `F` has a surjective linearization at every solution `(λ, y) ∈ U`"): for `X` without
boundary and `F` transversal at every `(0, y)`, `y ∈ S_g`, there is an open `V ⊇ {0} × S_g` all of
whose zeros of `F` are in good position (Theorem 3.54 (1) at each `(0, y)`, and the union). -/
theorem exists_isOpen_goodPosition_of_isLinSurjAt {m : ℕ} [ParacompactSpace ((Fin m → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
    (hX : PX.IsWithoutBoundary) (hgF : B.IsScFredholmSectionTame g) {t : Fin m → X → Y}
    (htp : ∀ i, B.IsScPlusSection (t i))
    (hsurj : ∀ y, IsZeroAt P g y →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsLinSurjAt
        (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) (0, y)) :
    ∃ V : Set ((Fin m → ℝ) × X), IsOpen V ∧ (∀ y, IsZeroAt P g y → (0, y) ∈ V) ∧
      ∀ z ∈ V, IsZeroAt (pullbackProj P Prod.snd)
        (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) z →
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGoodPositionGermTame
          (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) z := by
  have hF := theorem_3_18_tame hgF htp
  have hXZ := isWithoutBoundary_prod_rn (PX := PX) m hX
  have hloc : ∀ y, IsZeroAt P g y → ∃ V : Set ((Fin m → ℝ) × X), IsOpen V ∧ (0, y) ∈ V ∧
      ∀ z ∈ V, IsZeroAt (pullbackProj P Prod.snd)
        (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) z →
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGoodPositionGermTame
          (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) z := by
    intro y hy
    have hz0 : IsZeroAt (pullbackProj P Prod.snd)
        (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) (0, y) := by
      rw [isZeroAt_paramSection_iff]
      change IsZeroAt P (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) 0) y
      rw [paramSlice_zero]; exact hy
    have hgp := StrongBundle.isGoodPositionGerm_of_isLinSurjAt hF hz0 (hXZ (0, y))
      (hsurj y hy)
    exact theorem_3_54_one' hF hgp hz0
  choose! V hVo hzV hall using hloc
  refine ⟨⋃ y ∈ solutionSet P g, V y, isOpen_biUnion fun y hy => hVo y hy,
    fun y hy => mem_biUnion hy (hzV y hy), fun z hz hz0 => ?_⟩
  obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 hz
  exact hall y hy z hzy hz0

/-- **Transversality of `F` at `(0, x)` propagates to the zeros `y` of `g` near `x`** (the text:
"in view of the interior case of the implicit function theorem, Theorem 3.19, there exists an open
neighbourhood `U(x)` of `x` such that for every `(0, y)` with `y ∈ U(x) ∩ S_{f+s₀}` the
linearization of the above section is surjective"): Theorem 3.54 (1) for `F` at `(0, x)`, and
`U(x) = {y | (0, y) ∈ V}`. -/
theorem exists_isOpen_isLinSurjAt_zero_near {k : ℕ} [ParacompactSpace ((Fin k → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
    (hX : PX.IsWithoutBoundary) (hgF : B.IsScFredholmSectionTame g) {s : Fin k → X → Y}
    (hsp : ∀ i, B.IsScPlusSection (s i))
    {x : X} (hx : IsZeroAt P g x)
    (hsurj : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsLinSurjAt
      (paramSection g hgF.isScSmooth.1 s fun i => (hsp i).1) (0, x)) :
    ∃ Ux : Set X, IsOpen Ux ∧ x ∈ Ux ∧ ∀ y ∈ Ux, IsZeroAt P g y →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsLinSurjAt
        (paramSection g hgF.isScSmooth.1 s fun i => (hsp i).1) (0, y) := by
  have hF := theorem_3_18_tame hgF hsp
  have hXZ := isWithoutBoundary_prod_rn (PX := PX) k hX
  have hz0 : ∀ y, IsZeroAt P g y → IsZeroAt (pullbackProj P Prod.snd)
      (paramSection g hgF.isScSmooth.1 s fun i => (hsp i).1) (0, y) := fun y hy => by
    rw [isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice g hgF.isScSmooth.1 s (fun i => (hsp i).1) 0) y
    rw [paramSlice_zero]; exact hy
  have hgp := StrongBundle.isGoodPositionGerm_of_isLinSurjAt hF (hz0 x hx) (hXZ (0, x)) hsurj
  obtain ⟨V, hVo, hxV, hall⟩ := theorem_3_54_one' hF hgp (hz0 x hx)
  refine ⟨Prod.mk 0 ⁻¹' V, hVo.preimage (continuous_const.prodMk continuous_id), hxV,
    fun y hy hy0 => ?_⟩
  exact (hall (0, y) hy (hz0 y hy0)).isGoodPositionGerm.isLinSurjAt hF.isScSmooth

omit [T2Space X] [ParacompactSpace X] in
/-- **The omitted step of the proof of Theorem 5.13**: if `Z ⊆ ℝᵐ × X` is compact and the open set
`V` contains the part of `Z` over `λ = 0`, then `V` contains the part of `Z` over a ball
`|λ| < δ` (the projection of the compact set `Z ∖ V` to `ℝᵐ` is closed and misses `0`). -/
lemma exists_pos_forall_mem_of_isCompact {m : ℕ} {Z V : Set ((Fin m → ℝ) × X)}
    (hZ : IsCompact Z) (hV : IsOpen V) (h0 : ∀ z ∈ Z, z.1 = 0 → z ∈ V) :
    ∃ δ > 0, ∀ z ∈ Z, ‖z.1‖ < δ → z ∈ V := by
  have hc : IsCompact (Z \ V) := hZ.diff hV
  have hcl : IsClosed (Prod.fst '' (Z \ V)) := (hc.image continuous_fst).isClosed
  have h0n : (0 : Fin m → ℝ) ∈ (Prod.fst '' (Z \ V))ᶜ := by
    rintro ⟨z, ⟨hzZ, hzV⟩, hz0⟩
    exact hzV (h0 z hzZ hz0)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl 0 h0n
  refine ⟨δ, hδ, fun z hz hlt => ?_⟩
  by_contra hzV
  exact hball (mem_ball_zero_iff.2 hlt) ⟨z, ⟨hz, hzV⟩, rfl⟩

end Cover

/-! ### The perturbations `s₀ + Σ λᵢ tᵢ` are allowable for small `λ` -/

section Allowable

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- The triangle inequality for finite sums in a fibre of `Y_{0,1}`. -/
lemma StrongBundle.IsAuxNorm.toOne_sum_le {N : B.One → ℝ} (hN : B.IsAuxNorm N) {x : X}
    {ι : Type*} (s : Finset ι) (v : ι → B.oneFiber x) :
    N (B.toOne (∑ i ∈ s, v i)) ≤ ∑ i ∈ s, N (B.toOne (v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ((hN.fiber x).map_zero).le
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ((hN.fiber x).add_le _ _).trans (add_le_add le_rfl ih)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `f + (s₀ + Σ λᵢ tᵢ) = (f + s₀) + Σ λᵢ tᵢ`. -/
lemma sectionAdd_paramSlice {m : ℕ} {f s₀ : X → Y} (hf : IsSection P f) (hs₀ : IsSection P s₀)
    {t : Fin m → X → Y} (ht : ∀ i, IsSection P (t i)) (lam : Fin m → ℝ) :
    sectionAdd P f (paramSlice s₀ hs₀ t ht lam) =
      paramSlice (sectionAdd P f s₀) (hf.sectionAdd hs₀) t ht lam := by
  funext y
  rw [sectionAdd_apply hf (isSection_paramSlice lam)]
  change ((((⟨f y, hf y⟩ : P ⁻¹' {y}) +
      ⟨paramSlice s₀ hs₀ t ht lam y, isSection_paramSlice lam y⟩ : P ⁻¹' {y})) : Y) =
    ((((⟨sectionAdd P f s₀ y, hf.sectionAdd hs₀ y⟩ : P ⁻¹' {y}) + fiberComb t ht (lam, y)) :
      P ⁻¹' {y}) : Y)
  congr 1
  have h1 : (⟨paramSlice s₀ hs₀ t ht lam y, isSection_paramSlice lam y⟩ : P ⁻¹' {y}) =
      ⟨s₀ y, hs₀ y⟩ + fiberComb t ht (lam, y) := Subtype.ext rfl
  have h2 : (⟨sectionAdd P f s₀ y, hf.sectionAdd hs₀ y⟩ : P ⁻¹' {y}) =
      ⟨f y, hf y⟩ + ⟨s₀ y, hs₀ y⟩ := Subtype.ext (sectionAdd_apply hf hs₀ y)
  rw [h1, h2, add_assoc]

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] in
/-- Off the supports of `s₀` and of the `tᵢ`, the perturbation `s₀ + Σ λᵢ tᵢ` vanishes. -/
lemma isZeroAt_paramSlice_of_not_mem_support {m : ℕ} {s₀ : X → Y} (hs₀ : IsSection P s₀)
    {t : Fin m → X → Y} (ht : ∀ i, IsSection P (t i)) (lam : Fin m → ℝ) {x : X}
    (hx₀ : x ∉ sectionSupport P s₀) (hxt : ∀ i, x ∉ sectionSupport P (t i)) :
    IsZeroAt P (paramSlice s₀ hs₀ t ht lam) x := by
  have hz : ∀ {s : X → Y}, x ∉ sectionSupport P s → s x = fiberZero P x := fun {s} h =>
    not_not.1 fun hne => h (subset_closure hne)
  have h0 : (⟨s₀ x, hs₀ x⟩ : P ⁻¹' {x}) = 0 := Subtype.ext (hz hx₀)
  have ht0 : ∀ i, (⟨t i x, ht i x⟩ : P ⁻¹' {x}) = 0 := fun i => Subtype.ext (hz (hxt i))
  change ((((⟨s₀ x, hs₀ x⟩ : P ⁻¹' {x}) + fiberComb t ht (lam, x)) : P ⁻¹' {x}) : Y) =
    fiberZero P x
  have hfc : fiberComb t ht (lam, x) = 0 := by
    unfold fiberComb
    exact Finset.sum_eq_zero fun i _ => by rw [ht0 i, smul_zero]
  rw [h0, hfc, add_zero]; rfl

/-- The perturbation `s₀ + Σ λᵢ tᵢ` is an sc⁺-section. -/
theorem isScPlusSection_paramSlice {m : ℕ} {s₀ : X → Y} (hs₀ : B.IsScPlusSection s₀)
    {t : Fin m → X → Y} (htp : ∀ i, B.IsScPlusSection (t i)) (lam : Fin m → ℝ) :
    B.IsScPlusSection (paramSlice s₀ hs₀.1 t (fun i => (htp i).1) lam) := by
  rw [paramSlice_eq_sectionAdd]
  exact hs₀.add (StrongBundle.isScPlusSection_sectionSum _ fun i =>
    (htp i).smul_left (isScSmoothMap_real_const _))

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] in
/-- The support of `s₀ + Σ λᵢ tᵢ` lies in the union of the supports (a closed set). -/
lemma sectionSupport_paramSlice_subset {m : ℕ} {s₀ : X → Y} (hs₀ : IsSection P s₀)
    {t : Fin m → X → Y} (ht : ∀ i, IsSection P (t i)) (lam : Fin m → ℝ) :
    sectionSupport P (paramSlice s₀ hs₀ t ht lam) ⊆
      sectionSupport P s₀ ∪ ⋃ i, sectionSupport P (t i) := by
  refine closure_minimal (fun x hx => ?_)
    (isClosed_closure.union (isClosed_iUnion_of_finite fun i => isClosed_closure))
  by_contra hxn
  rw [mem_union, not_or, mem_iUnion, not_exists] at hxn
  exact hx (isZeroAt_paramSlice_of_not_mem_support hs₀ ht lam hxn.1 hxn.2)

/-- **The perturbation `s₀ + Σ λᵢ tᵢ` is allowable for small `λ`** (the text: "there is a number
`δ₀ > 0` such that `|λ| < δ₀` implies `N(Σ λⱼ tⱼ(y)) < ε/2`", and "`N(s₀(y) + s(λ₀, y)) ≤ 1`"):
if `N(s₀(x)) ≤ 1 − ε` and `N(tᵢ(x)) ≤ 1` for all `x`, then `N(s₀(x) + Σ λᵢ tᵢ(x)) ≤ 1` whenever
`m·|λ| ≤ ε` (`|λ|` the maximum norm). -/
theorem auxLe_paramSlice {m : ℕ} {N : B.One → ℝ} (hN : B.IsAuxNorm N) {s₀ : X → Y}
    (hs₀ : B.IsScPlusSection s₀) {t : Fin m → X → Y} (htp : ∀ i, B.IsScPlusSection (t i))
    {ε : ℝ} (hs₀N : ∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ 1 - ε)
    (htN : ∀ i x (hx : t i x ∈ B.oneSet), N (B.oneMk (t i x) hx) ≤ 1) {lam : Fin m → ℝ}
    (hlam : (m : ℝ) * ‖lam‖ ≤ ε) (x : X) :
    B.AuxLe N (paramSlice s₀ hs₀.1 t (fun i => (htp i).1) lam x) 1 := by
  set v : B.oneFiber x := ⟨⟨s₀ x, hs₀.1 x⟩, hs₀.mem_oneSet x⟩ with hv
  set w : Fin m → B.oneFiber x := fun i => ⟨⟨t i x, (htp i).1 x⟩, (htp i).mem_oneSet x⟩ with hw
  set u : B.oneFiber x := v + ∑ i, lam i • w i with hu
  have hu' : ((u : P ⁻¹' {x}) : Y) = paramSlice s₀ hs₀.1 t (fun i => (htp i).1) lam x := by
    change ((((v + ∑ i, lam i • w i : B.oneFiber x) : P ⁻¹' {x})) : Y) = _
    rw [Submodule.coe_add, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    rfl
  have hmem : paramSlice s₀ hs₀.1 t (fun i => (htp i).1) lam x ∈ B.oneSet := hu' ▸ u.2
  refine ⟨hmem, ?_⟩
  have h1 : B.oneMk _ hmem = B.toOne u := by
    apply B.oneVal_injective
    rw [StrongBundle.oneVal_oneMk, StrongBundle.oneVal_toOne, hu']
  rw [h1]
  have hvN : N (B.toOne v) ≤ 1 - ε := hs₀N x (hs₀.mem_oneSet x)
  have hwN : ∀ i, N (B.toOne (w i)) ≤ 1 := fun i => htN i x ((htp i).mem_oneSet x)
  have hli : ∀ i, |lam i| ≤ ‖lam‖ := fun i => by
    have := norm_le_pi_norm lam i
    rwa [Real.norm_eq_abs] at this
  calc N (B.toOne (v + ∑ i, lam i • w i))
      ≤ N (B.toOne v) + N (B.toOne (∑ i, lam i • w i)) := (hN.fiber x).add_le _ _
    _ ≤ (1 - ε) + ∑ i, N (B.toOne (lam i • w i)) :=
        add_le_add hvN (hN.toOne_sum_le _ _)
    _ = (1 - ε) + ∑ i, |lam i| * N (B.toOne (w i)) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => hN.smul (w i) (lam i)
    _ ≤ (1 - ε) + ∑ _i : Fin m, ‖lam‖ * 1 :=
        add_le_add le_rfl (Finset.sum_le_sum fun i _ =>
          mul_le_mul (hli i) (hwN i) (hN.nonneg _) (norm_nonneg _))
    _ = (1 - ε) + (m : ℝ) * ‖lam‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    _ ≤ 1 := by linarith

end Allowable

/-! ### The Sard step: regular values of the projection `S̃ → ℝᵐ` give transversal slices -/

section Sard

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin m → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
  {B : StrongBundle PX P} {g : X → Y}

open StrongRetr

set_option maxHeartbeats 3200000 in
-- destructuring the tangent germ chart of `theorem_3_54_index` and the product chart
/-- **The Sard step of the proof of Theorem 5.13, at one point of `S̃`** (the text: "`S̃ = F⁻¹(0)`
is a smooth manifold ... taking a regular value `λ₀` for the projection `S̃ → ℝᵐ`, it is easily
verified that `f + s₀ + s(λ₀, ·)` is transversal to the zero section").  Let `z₀` be a zero of
`F(λ, y) = g(y) + Σ λᵢ tᵢ(y)` in good position.  Then there are an open `W ∋ z₀` and a Lebesgue
null set `CV ⊆ ℝᵐ` such that for every zero `z = (λ, y) ∈ W` of `F` with `λ ∉ CV`, the slice
`g + Σ λᵢ tᵢ` is transversal at `y`.  *Proof*: Theorem 3.54 (2) gives the regular tangent germ
chart `D` of `S̃` at `z₀` (model `V ⊆ N ∩ C`, graph map `Γ`, `D.φ⁻¹ ∘ Γ` the parametrization of
`S̃ ∩ W`, `W = D.φ.source`); `q = p ∘ D.φ⁻¹ ∘ Γ : V → ℝᵐ` is `C^∞` (sc-smooth on the
finite-dimensional `V`); Sard's theorem on the strata of `V` (`measure_image_stratCritSet`) makes
the stratified critical values `CV` null.  At a zero `z = D.φ⁻¹(Γ(v))` with `q(v) = λ ∉ CV`, the
derivative of `q` on the stratum through `v` is onto `ℝᵐ`; in the product chart `(r ↦ r − λ) × Φ`
of a chart `Φ` centred at `y`, the map `gmap = ψ ∘ D.φ⁻¹ ∘ Γ` has `q = pr₁ ∘ gmap + λ`, its
derivative takes values in `T₀O` and in `ker Lin_F(0)` (chain rule: `F̂ ∘ r ∘ gmap = 0`), so
`ker Lin_F(0)` projects onto `ℝᵐ`, and `isLinSurjAt_paramSlice_of_ker_fst` concludes.  Only the
direction "regular value ⟹ transversal" is needed; the stratified form of Sard's theorem avoids
the question whether `v` is interior to `V`. -/
theorem exists_null_isLinSurjAt_paramSlice_near (hgF : B.IsScFredholmSectionTame g)
    {t : Fin m → X → Y} (htp : ∀ i, B.IsScPlusSection (t i))
    {z₀ : (Fin m → ℝ) × X}
    (hz₀ : IsZeroAt (pullbackProj P Prod.snd)
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) z₀)
    (hgp : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGoodPositionGermTame
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) z₀) :
    ∃ W : Set ((Fin m → ℝ) × X), IsOpen W ∧ z₀ ∈ W ∧ ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
      ∀ z ∈ W, IsZeroAt (pullbackProj P Prod.snd)
        (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) z →
        z.1 ∉ CV →
      B.IsLinSurjAt (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) z.1) z.2 := by
  classical
  have hF := theorem_3_18_tame hgF htp
  have hFsm := hF.isScSmooth
  have hFsec : IsSection (pullbackProj P Prod.snd)
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) := hFsm.1
  obtain ⟨Vx, d, hVxo, hz₀Vx, hgood, D, hreg, hDsrc, -⟩ := theorem_3_54_index hF hgp hz₀
  -- the tame retraction of the chart `D.φ`
  obtain ⟨RD, hRD, -⟩ := D.tame
  have hRDU : D.φ.model.O ⊆ RD.U := by rw [← hRD]; exact RD.retract_subset
  -- `q = p ∘ D.φ⁻¹ ∘ Γ : V → ℝᵐ` is sc-smooth, hence `C^∞`
  set q : D.N → Fin m → ℝ := fun v => (D.φ.symm (D.Γ v)).1 with hqdef
  have hfst := (MPolyfold.isScSmoothMap_fst (rnPolyfold m) PX).smooth D.φ (rnChart m 0) D.isChart
    (isChart_rnChart 0) D.φ.source D.φ.isOpen_source (fun z hz => ⟨mem_univ _, hz⟩)
    (fun _ _ => mem_univ _)
  rw [D.φ.image_source] at hfst
  have hfstR : IsScSmooth RD.U ((rnChart m 0 ∘ Prod.fst ∘ D.φ.symm) ∘ RD) :=
    hfst.comp_isScSmooth RD hRD
  have hΓ : IsScSmooth (E := ScBanach.const D.N) D.V D.Γ := D.Γ_isScSmooth hreg
  have hVdom := D.V_isRelOpenInQuadrant.isScDomain
  have hΓmaps : MapsTo D.Γ D.V RD.U := fun v hv => hRDU (D.Γ_mem_O hv)
  have hq : IsScSmooth (E := ScBanach.const D.N) (F := rnSc m) D.V q :=
    (IsScSmooth.comp hVdom RD.isScDomain hfstR hΓ hΓmaps).congr hVdom fun v hv => by
      change (rnChart m 0) (D.φ.symm (RD (D.Γ v))).1 = q v
      rw [RD.apply_eq_self_of_mem_retract (hRD ▸ D.Γ_mem_O hv), rnChart_apply, sub_zero]
  have hqC : ContDiffOn ℝ ∞ q D.V := (isScSmooth_iff_contDiffOn_const hVdom q).1 hq
  -- Sard on the strata of `V`
  obtain ⟨n', W', TN, hTN⟩ := D.isPartialQuadrant
  let ℓ : D.N →ₗ[ℝ] (Fin n' → ℝ) :=
    { toFun := fun v => (TN 0 v).1
      map_add' := fun u v => by simp
      map_smul' := fun c v => by simp }
  have hquad : (Subtype.val ⁻¹' D.φ.model.C : Set D.N) = quadC ℓ := by rw [hTN]; rfl
  obtain ⟨ON, hONo, hVeq⟩ := D.V_relOpen
  have hV' : D.V = ON ∩ quadC ℓ := by rw [hVeq, hquad]
  have hqC' : ContDiffOn ℝ ∞ q (ON ∩ quadC ℓ) := by rw [← hV']; exact hqC
  have hnull : volume (q '' stratCritSet ℓ q (ON ∩ quadC ℓ)) = 0 :=
    measure_image_stratCritSet ℓ volume hONo hqC'
  refine ⟨Vx, hVxo, hz₀Vx, q '' stratCritSet ℓ q (ON ∩ quadC ℓ), hnull,
    fun z hzVx hz0 hzCV => ?_⟩
  -- the point `v ∈ V` over `z`
  have hzsrc : z ∈ D.φ.source := hDsrc ▸ hzVx
  obtain ⟨hvV, hzΓ⟩ := D.exists_eq_Γ ⟨hz0, hzsrc⟩
  set v := D.π (D.φ z) with hvdef
  have hΓz : D.φ.symm (D.Γ v) = z := by rw [← hzΓ]; exact D.φ.symm_apply_apply hzsrc
  have hqv : q v = z.1 := by change (D.φ.symm (D.Γ v)).1 = z.1; rw [hΓz]
  have hvU : v ∈ ON ∩ quadC ℓ := by rw [← hV']; exact hvV
  have hvreg : v ∉ stratCritSet ℓ q (ON ∩ quadC ℓ) := fun h => hzCV ⟨v, h, hqv⟩
  have hregs : Surjective ((fderivWithin ℝ q (ON ∩ quadC ℓ) v).comp
      (stratSub ℓ (zeroSetOf ℓ v)).subtypeL) := by
    by_contra h; exact hvreg ⟨hvU, h⟩
  -- the chart `c` of `P` centred at `y = z.2`, and the product chart `ψ = (r ↦ r − λ) × φ`
  have hy0 : IsZeroAt P (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) z.1) z.2 :=
    (isZeroAt_paramSection_iff z).1 hz0
  have hglF : B.IsScFredholmSection (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) z.1) :=
    isScFredholmSection_paramSlice hgF.toIsScFredholmSection htp z.1
  have hys : z.2 ∈ PX.smoothSet := hglF.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨-, c, hc, hyV, hφ0, -⟩ := hglF.germ z.2 hys
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := by
    rw [← hφ0]; exact c.φ.mapsTo_model _ hyV
  set q₀ := paramSection g hgF.isScSmooth.1 t (fun i => (htp i).1) z with hq₀
  have hχc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart
      ((PullbackChartData.ofProd c z.1).toChart q₀) :=
    (PullbackChartData.ofProd c z.1).isChart_toChart B _ hc q₀
  have hzψ : z ∈ (PullbackChartData.ofProd c z.1).ψ.source := ⟨mem_univ _, hyV⟩
  have hψz : (PullbackChartData.ofProd c z.1).ψ z = 0 := Prod.ext (sub_self _) hφ0
  -- the transition `D.φ → ψ` on the overlap, with the restricted retraction `R_W`
  have hcomp : D.φ.Compatible (PullbackChartData.ofProd c z.1).ψ :=
    D.isChart.compatible (PullbackChartData.ofProd c z.1).isChart (P := (rnPolyfold m).prod PX)
  obtain ⟨Wov, hWovo, hWov⟩ := D.φ.exists_isOpen_image_eq
    (s := D.φ.source ∩ (PullbackChartData.ofProd c z.1).ψ.source) inter_subset_left
    (D.φ.isOpen_source.inter (PullbackChartData.ofProd c z.1).ψ.isOpen_source)
  have hRW : (RD.restrict hWovo).retract = D.φ.overlap (PullbackChartData.ofProd c z.1).ψ := by
    rw [ScRetraction.restrict_retract, hRD]; exact hWov.symm
  have htransR : IsScSmooth (RD.restrict hWovo).U
      (D.φ.transition (PullbackChartData.ofProd c z.1).ψ ∘ RD.restrict hWovo) :=
    hcomp.1.comp_isScSmooth (RD.restrict hWovo) hRW
  -- the relatively open `V' = V ∩ u` on which `Γ` lands in the overlap
  obtain ⟨u, huo, hu⟩ := (continuousOn_iff'.1 D.Γ_continuousOn) Wov hWovo
  have hΓW : ∀ w ∈ D.V ∩ u, D.Γ w ∈ Wov := fun w hw => by
    have : w ∈ u ∩ D.V := ⟨hw.2, hw.1⟩
    rw [← hu] at this; exact this.1
  have hvu : v ∈ u := by
    have hΓvW : D.Γ v ∈ Wov := by
      have : D.Γ v ∈ D.φ.model.O ∩ Wov := by
        rw [← hWov, ← hzΓ]; exact ⟨z, ⟨hzsrc, hzψ⟩, rfl⟩
      exact this.2
    have : v ∈ D.Γ ⁻¹' Wov ∩ D.V := ⟨hΓvW, hvV⟩
    rw [hu] at this; exact this.1
  have hvV' : v ∈ D.V ∩ u := ⟨hvV, hvu⟩
  have hV'dom : IsRelOpenInQuadrant (ScBanach.const D.N) (Subtype.val ⁻¹' D.φ.model.C)
      (D.V ∩ u) := D.V_isRelOpenInQuadrant.inter_isOpen huo
  have hΓψ : ∀ w ∈ D.V ∩ u, D.φ.symm (D.Γ w) ∈ (PullbackChartData.ofProd c z.1).ψ.source := by
    intro w hw
    have : D.Γ w ∈ D.φ '' (D.φ.source ∩ (PullbackChartData.ofProd c z.1).ψ.source) := by
      rw [hWov]; exact ⟨D.Γ_mem_O hw.1, hΓW w hw⟩
    obtain ⟨z', ⟨hz'1, hz'2⟩, hz'e⟩ := this
    rw [← hz'e, D.φ.symm_apply_apply hz'1]; exact hz'2
  -- `gmap = ψ ∘ D.φ⁻¹ ∘ Γ`, sc-smooth on `V'`
  set gmap : D.N → (Fin m → ℝ) × c.φ.model.E 0 :=
    fun w => (PullbackChartData.ofProd c z.1).ψ (D.φ.symm (D.Γ w)) with hgmapdef
  have hΓ' : IsScSmooth (E := ScBanach.const D.N) (D.V ∩ u) D.Γ :=
    hΓ.of_subset hV'dom.isScDomain inter_subset_left
  have hΓmapsW : MapsTo D.Γ (D.V ∩ u) (RD.restrict hWovo).U := fun w hw =>
    ⟨hRDU (D.Γ_mem_O hw.1), by
      change RD (D.Γ w) ∈ Wov
      rw [RD.apply_eq_self_of_mem_retract (hRD ▸ D.Γ_mem_O hw.1)]
      exact hΓW w hw⟩
  have hgmap : IsScSmooth (E := ScBanach.const D.N) (F := (rnSc m).prod c.φ.model.E)
      (D.V ∩ u) gmap :=
    (IsScSmooth.comp hV'dom.isScDomain (RD.restrict hWovo).isScDomain htransR hΓ'
      hΓmapsW).congr hV'dom.isScDomain fun w hw => by
        change D.φ.transition (PullbackChartData.ofProd c z.1).ψ (RD (D.Γ w)) = gmap w
        rw [RD.apply_eq_self_of_mem_retract (hRD ▸ D.Γ_mem_O hw.1)]
        rfl
  -- the derivative of `q` at `v` on `V'`: `q = pr₁ ∘ gmap + λ`
  have hder_g : HasFDerivWithinAt gmap
    (scDeriv (E := ScBanach.const D.N) (F := (rnSc m).prod c.φ.model.E) (D.V ∩ u) gmap v)
      (D.V ∩ u) v :=
    hasFDerivWithinAt_scDeriv_const' (V := D.N) (F := (rnSc m).prod c.φ.model.E) hgmap.isSc1 hvV'
  have hqg : ∀ w, q w = (gmap w).1 + z.1 := fun w => by
    change (D.φ.symm (D.Γ w)).1 = ((D.φ.symm (D.Γ w)).1 - z.1) + z.1
    rw [sub_add_cancel]
  have hder_q : HasFDerivWithinAt q ((ContinuousLinearMap.fst ℝ (Fin m → ℝ) (c.φ.model.E 0)).comp
      (scDeriv (E := ScBanach.const D.N) (F := (rnSc m).prod c.φ.model.E) (D.V ∩ u) gmap v))
      (D.V ∩ u) v :=
    (hder_g.fst.add_const z.1).congr (fun w _ => hqg w) (hqg v)
  have hv1 : v ∈ (ScBanach.const D.N).lvlSet (D.V ∩ u) 1 := by
    rw [ScBanach.lvlSet_const]; exact hvV'
  have huniq : UniqueDiffWithinAt ℝ (D.V ∩ u) v := by
    have := hV'dom.isScDomain.uniqueDiffWithinAt 1 v hv1
    rwa [ScBanach.lvlSet_const] at this
  have hfd : fderivWithin ℝ q (ON ∩ quadC ℓ) v =
      (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (c.φ.model.E 0)).comp
        (scDeriv (E := ScBanach.const D.N) (F := (rnSc m).prod c.φ.model.E) (D.V ∩ u) gmap v) := by
    rw [← hV', ← fderivWithin_inter (huo.mem_nhds hvu)]
    exact hder_q.fderivWithin huniq
  rw [hfd] at hregs
  -- the values of `D gmap(v)` lie in `T₀O` and in `ker Lin_F(0)` of the product chart
  have hgmapO : ∀ w ∈ D.V ∩ u, gmap w ∈ (PullbackChartData.ofProd c z.1).ψ.model.O :=
    fun w hw => (PullbackChartData.ofProd c z.1).ψ.mapsTo_model _ (hΓψ w hw)
  have hmapsU : MapsTo gmap (D.V ∩ u) ((PullbackChartData.ofProd c z.1).toChart q₀).U :=
    fun w hw => mem_U_of_mem_O ((PullbackChartData.ofProd c z.1).toChart q₀).isRetraction
      (((PullbackChartData.ofProd c z.1).toChart q₀).r_image ▸ hgmapO w hw)
  have hrχ := r_isScSmooth ((PullbackChartData.ofProd c z.1).toChart q₀).relOpen
    ((PullbackChartData.ofProd c z.1).toChart q₀).isRetraction
  have hrg : IsSc1 (E := ScBanach.const D.N) (D.V ∩ u)
      (r ((PullbackChartData.ofProd c z.1).toChart q₀).R ∘ gmap) :=
    (IsScSmooth.comp hV'dom.isScDomain
      ((PullbackChartData.ofProd c z.1).toChart q₀).relOpen.isScDomain hrχ hgmap hmapsU).isSc1
  have hrg_eq : EqOn (r ((PullbackChartData.ofProd c z.1).toChart q₀).R ∘ gmap) gmap (D.V ∩ u) :=
    fun w hw => r_eq_self ((PullbackChartData.ofProd c z.1).toChart q₀).isRetraction
      (((PullbackChartData.ofProd c z.1).toChart q₀).r_image ▸ hgmapO w hw)
  have hgv0 : gmap v = 0 := by
    change (PullbackChartData.ofProd c z.1).ψ (D.φ.symm (D.Γ v)) = 0
    rw [hΓz]; exact hψz
  have hlev : levelMap (E := ScBanach.const D.N)
      (F := ((PullbackChartData.ofProd c z.1).toChart q₀).φ.model.E) gmap 1 v =
      (0 : ((PullbackChartData.ofProd c z.1).toChart q₀).φ.model.E 1) :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, ScBanach.const_toBase D.N 1 v, hgv0]; rfl)
  have hDg_mem : ∀ n,
    scDeriv (E := ScBanach.const D.N) (F := (rnSc m).prod c.φ.model.E) (D.V ∩ u) gmap v n ∈
      rangeS (scDeriv ((PullbackChartData.ofProd c z.1).toChart q₀).U
        (r ((PullbackChartData.ofProd c z.1).toChart q₀).R) 0) := fun n => by
    refine ⟨scDeriv (E := ScBanach.const D.N) (F := (rnSc m).prod c.φ.model.E) (D.V ∩ u) gmap v n,
      ?_⟩
    have h1 := scDeriv_comp_apply' hV'dom ((PullbackChartData.ofProd c z.1).toChart q₀).relOpen
      hgmap.isSc1 hrχ.isSc1 hmapsU hv1 n
    rw [hlev] at h1
    exact h1.trans (congrArg (fun L : D.N →L[ℝ] _ => L n) (scDeriv_eq_of_eqOn_relOpen hV'dom hrg
      hgmap.isSc1 subset_rfl subset_rfl hrg_eq hv1))
  have hFr : IsSc1 ((PullbackChartData.ofProd c z.1).toChart q₀).U
      (((PullbackChartData.ofProd c z.1).toChart q₀).principal
        (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) ∘
          r ((PullbackChartData.ofProd c z.1).toChart q₀).R) :=
    hFsm.isSc1_principal_comp_r hχc
  have hFg : IsSc1 (E := ScBanach.const D.N) (D.V ∩ u)
      ((((PullbackChartData.ofProd c z.1).toChart q₀).principal
        (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) ∘
          r ((PullbackChartData.ofProd c z.1).toChart q₀).R) ∘ gmap) :=
    (theorem_1_21' hV'dom.isScDomain
      ((PullbackChartData.ofProd c z.1).toChart q₀).relOpen.isScDomain
      hgmap.isSc1 hFr hmapsU).1
  have hF0 : EqOn ((((PullbackChartData.ofProd c z.1).toChart q₀).principal
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) ∘
        r ((PullbackChartData.ofProd c z.1).toChart q₀).R) ∘ gmap)
      (fun _ => (0 : c.F 0)) (D.V ∩ u) := fun w hw => by
    have hr : r ((PullbackChartData.ofProd c z.1).toChart q₀).R (gmap w) = gmap w := hrg_eq hw
    change ((PullbackChartData.ofProd c z.1).toChart q₀).principal _
      (r ((PullbackChartData.ofProd c z.1).toChart q₀).R (gmap w)) = 0
    rw [hr]
    exact (((PullbackChartData.ofProd c z.1).toChart q₀).isZeroAt_iff hFsec (hΓψ w hw)).1
      (D.symm_Γ_mem hw.1).1
  have hDg_ker : ∀ n, scDeriv ((PullbackChartData.ofProd c z.1).toChart q₀).U
      (((PullbackChartData.ofProd c z.1).toChart q₀).principal
        (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) ∘
          r ((PullbackChartData.ofProd c z.1).toChart q₀).R) 0
        (scDeriv (E := ScBanach.const D.N) (F := (rnSc m).prod c.φ.model.E) (D.V ∩ u) gmap v n) =
          0 := fun n => by
    have h1 := scDeriv_comp_apply' hV'dom ((PullbackChartData.ofProd c z.1).toChart q₀).relOpen
      hgmap.isSc1 hFr hmapsU hv1 n
    rw [hlev] at h1
    refine h1.trans ?_
    have h2 : scDeriv (E := ScBanach.const D.N) (D.V ∩ u)
        ((((PullbackChartData.ofProd c z.1).toChart q₀).principal
          (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) ∘
            r ((PullbackChartData.ofProd c z.1).toChart q₀).R) ∘ gmap) v = 0 := by
      have hd1 := hasFDerivWithinAt_scDeriv_const' (V := D.N) (F := c.F) hFg hvV'
      have hd2 : HasFDerivWithinAt ((((PullbackChartData.ofProd c z.1).toChart q₀).principal
          (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) ∘
            r ((PullbackChartData.ofProd c z.1).toChart q₀).R) ∘ gmap)
          (0 : D.N →L[ℝ] c.F 0) (D.V ∩ u) v :=
        (hasFDerivWithinAt_const (0 : c.F 0) v (D.V ∩ u)).congr (fun w hw => hF0 hw) (hF0 hvV')
      exact huniq.eq hd1 hd2
    rw [h2]; rfl
  -- conclusion
  have hsurjF : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsLinSurjAt
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) z :=
    (hgood z hzVx hz0).1.isGoodPositionGerm.isLinSurjAt hFsm
  refine isLinSurjAt_paramSlice_of_ker_fst hgF.toIsScFredholmSection htp hc hyV hφ0 z.1 q₀ hy0 hsurjF
    fun a => ?_
  obtain ⟨⟨n, hn⟩, hna⟩ := hregs a
  exact ⟨scDeriv (E := ScBanach.const D.N) (F := (rnSc m).prod c.φ.model.E) (D.V ∩ u) gmap v n,
    hDg_mem n, hna, hDg_ker n⟩

end Sard

/-! ### Theorem 5.13 -/

section Theorem513

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

variable (B) in
/-- **"`S_h` is a sub-M-polyfold whose induced structure is that of a compact smooth manifold
without boundary"**, as Theorem 3.56 gives it (`theorem_3_56_of_surjective`): the solution set of
`h` is a sub-M-polyfold whose induced structure is tame, a manifold without boundary of locally
constant dimension, with regular tangent germ data at every zero whose dimension is the Fredholm
index of `h'(y)` (`IsSurjLinOfIndex`).  (Compactness is stated separately.) -/
def StrongBundle.SolutionSetIsManifold (h : X → Y) : Prop :=
  ∃ hsub : PX.IsSubMPolyfold (solutionSet P h),
    haveI := PX.paracompactSpace_subtype (solutionSet P h)
    (MPolyfold.subPolyfold hsub).IsTame ∧
      (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
      (MPolyfold.subPolyfold hsub).IsWithoutBoundary ∧
      ∀ x ∈ solutionSet P h, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P h) x d,
        D.IsRegular ∧ (∀ y ∈ solutionSet P h ∩ D.φ.source,
          ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P h) y n'), n' = d) ∧
        ∀ y ∈ solutionSet P h ∩ D.φ.source, B.IsSurjLinOfIndex h y d

set_option maxHeartbeats 3200000 in
-- the assembly of the proof: several large existentials are destructured
/-- **Theorem 5.13 (perturbation and transversality, interior case), generic form.**  Let
`P : Y → X` be a strong bundle over an M-polyfold `X` with `∂X = ∅` which admits sc-smooth bump
functions, `f` an sc-Fredholm section with compact solution set and with tame germ data
(`IsScFredholmSectionTame`, Definition 3.51: the standing tameness of §3.6 and §5.3), `N` an
auxiliary norm.  Then there is an open neighbourhood `U` of `S_f` such that
(1) for every allowable `s ∈ Γ^{+,1}_U(P)` (sc⁺, `supp(s) ⊆ U`, `N(s(x)) ≤ 1`) the solution set
`S_{f+s}` is compact, and (2) for every sc⁺-section `s₀` with `supp(s₀) ⊆ U` and
`N(s₀(x)) ≤ 1 − ε` (`ε > 0`) there are finitely many allowable sc⁺-sections `t₁, …, t_m`, a
`δ > 0` and a Lebesgue null set `CV ⊆ ℝᵐ` such that for every `λ` with `|λ| < δ`, `λ ∉ CV`
(a set of full measure in the ball), the perturbation `s_λ = s₀ + Σ λᵢ tᵢ` is allowable,
`f + s_λ` is transversal to the zero section (Definition 5.15), `S_{f+s_λ}` is compact, and, if
non-empty, a sub-M-polyfold whose induced structure is that of a smooth manifold without boundary
with dimension the Fredholm index (Theorem 3.56).  The dense-set form of the text is
`theorem_5_13`.

*Proof* (the text's, with the omitted steps): `U` and the compactness from Theorem 5.5 and Remark
5.12; at every zero of `g = f + s₀` the spanning sections of `exists_spanning_sections`, the
transversality of the parametrized section `F_x` at `(0, x)` and at `(0, y)` for `y` near `x`
(`exists_isOpen_isLinSurjAt_zero_near`); a finite subcover of the compact `S_g`, the united family
`t` (`isLinSurjAt_paramSection_zero_of_comp`); the open set `V ⊇ {0} × S_g` of zeros of `F` in
good position (`exists_isOpen_goodPosition_of_isLinSurjAt`); the compact set
`Z = {(λ, y) | |λ| ≤ δ₁, F(λ, y) = 0}` (Remark 5.12 for the allowable `s_λ`) and the small `δ₀`
with `Z ∩ {|λ| < δ₀} ⊆ V` (`exists_pos_forall_mem_of_isCompact`, the omitted step); the Sard step
`exists_null_isLinSurjAt_paramSlice_near` at the points of the compact
`Z₀ = Z ∩ {|λ| ≤ δ/2}`, a finite subcover and the union of the null sets. -/
theorem theorem_5_13_generic (hX : PX.IsWithoutBoundary) (hbump : PX.AdmitsBumpFunctions)
    {f : X → Y} (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f))
    {N : B.One → ℝ} (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ (s₀ : X → Y) (hs₀ : B.IsScPlusSection s₀), sectionSupport P s₀ ⊆ U → ∀ ε > 0,
        (∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ 1 - ε) →
        ∃ (m : ℕ) (t : Fin m → X → Y) (ht : ∀ i, B.IsScPlusSection (t i)),
          (∀ i, sectionSupport P (t i) ⊆ U) ∧
          (∀ i x (hx : t i x ∈ B.oneSet), N (B.oneMk (t i x) hx) ≤ 1) ∧
          ∃ δ > 0, ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
            ∀ lam : Fin m → ℝ, ‖lam‖ < δ → lam ∉ CV →
              paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam ∈ B.allowableSections N U ∧
              B.IsTransversal (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)) ∧
              IsCompact (solutionSet P
                (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam))) ∧
              ((solutionSet P
                (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam))).Nonempty →
                B.SolutionSetIsManifold
                  (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam))) := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  -- Theorem 5.5: the neighbourhood `U` and the compact closure
  obtain ⟨-, hprop⟩ := theorem_5_5 hf.toIsScFredholmSection hS
  obtain ⟨U, hUo, hSU, hK⟩ := hprop N hN
  -- (1) compactness for allowable sections (Remark 5.12, and the solution set is closed)
  have hcpt : ∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s)) := by
    rintro s ⟨hs, hssupp, hsN⟩
    have hsU : ∀ x ∉ U, IsZeroAt P s x := fun x hx =>
      not_not.1 fun hne => hx (hssupp (subset_closure hne))
    have hsN' : ∀ x, B.AuxLe N (s x) 1 := fun x => ⟨hs.mem_oneSet x, hsN x _⟩
    obtain ⟨-, hcl⟩ := remark_5_12 hN hfs hSU hK hs.1 hsU hsN'
    exact hcl.of_isClosed_subset
      (isClosed_solutionSet (theorem_3_15 hf.toIsScFredholmSection hs).isScSmooth)
      subset_closure
  refine ⟨U, hUo, hSU, hcpt, ?_⟩
  intro s₀ hs₀ hs₀supp ε hε hs₀N
  -- `g = f + s₀`, sc-Fredholm with compact solution set inside `U`
  have hgFt : B.IsScFredholmSectionTame (sectionAdd P f s₀) := theorem_3_15_tame hf hs₀
  have hgF : B.IsScFredholmSection (sectionAdd P f s₀) := hgFt.toIsScFredholmSection
  have hs₀alw : s₀ ∈ B.allowableSections N U :=
    ⟨hs₀, hs₀supp, fun x hx => (hs₀N x hx).trans (by linarith)⟩
  have hSg : IsCompact (solutionSet P (sectionAdd P f s₀)) := hcpt s₀ hs₀alw
  have hSgU : solutionSet P (sectionAdd P f s₀) ⊆ U := by
    have hs₀U : ∀ x ∉ U, IsZeroAt P s₀ x := fun x hx =>
      not_not.1 fun hne => hx (hs₀supp (subset_closure hne))
    have hs₀N' : ∀ x, B.AuxLe N (s₀ x) 1 := fun x => ⟨hs₀.mem_oneSet x, hs₀alw.2.2 x _⟩
    exact fun x hx => ((remark_5_12 hN hfs hSU hK hs₀.1 hs₀U hs₀N').1 hx).1
  -- spanning sections at every zero of `g`, and the neighbourhood where `F_x` is transversal
  have hspan : ∀ x : solutionSet P (sectionAdd P f s₀),
      ∃ (k : ℕ) (s : Fin k → X → Y) (hsp : ∀ i, B.IsScPlusSection (s i)),
        (∀ i, sectionSupport P (s i) ⊆ U) ∧
        (∀ i x (hx : s i x ∈ B.oneSet), N (B.oneMk (s i x) hx) ≤ 1) ∧
        ∃ Ux : Set X, IsOpen Ux ∧ (x : X) ∈ Ux ∧ ∀ y ∈ Ux, IsZeroAt P (sectionAdd P f s₀) y →
          have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
          have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
            ((rnPolyfold k).prod PX) B
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsLinSurjAt
            (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 s fun i => (hsp i).1) (0, y) := by
    intro x
    obtain ⟨x, hx⟩ := x
    obtain ⟨k, s, hsp, hsupp, hsN, c, hc, hxV, hφ0, hsp_span⟩ :=
      exists_spanning_sections hbump hN hgF hx hUo (hSgU hx)
    have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
    have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
      ((rnPolyfold k).prod PX) B
    have hsurj := isLinSurjAt_paramSection_zero_of_spanning hgF hsp hc hxV hφ0
      (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 s (fun i => (hsp i).1) (0, x)) hsp_span
    obtain ⟨Ux, hUxo, hxUx, hUx⟩ :=
      exists_isOpen_isLinSurjAt_zero_near hX hgFt hsp hx hsurj
    exact ⟨k, s, hsp, hsupp, hsN, Ux, hUxo, hxUx, hUx⟩
  choose k s hsp hsupp hsN Ux hUxo hxUx hUx using hspan
  -- a finite subcover of the compact `S_g`
  obtain ⟨T, hT⟩ := hSg.elim_finite_subcover Ux hUxo
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxUx ⟨x, hx⟩⟩)
  -- the united family `t`, indexed by `Fin m`
  let e := Fintype.equivFin (Σ x : T, Fin (k x.1))
  set m := Fintype.card (Σ x : T, Fin (k x.1)) with hm
  set t : Fin m → X → Y := fun j => s (e.symm j).1.1 (e.symm j).2 with htdef
  have ht : ∀ j, B.IsScPlusSection (t j) := fun j => hsp _ _
  have htsupp : ∀ j, sectionSupport P (t j) ⊆ U := fun j => hsupp _ _
  have htN : ∀ j x (hx : t j x ∈ B.oneSet), N (B.oneMk (t j x) hx) ≤ 1 := fun j x hx =>
    hsN _ _ x hx
  have := MPolyfold.paracompactSpace_prod (rnPolyfold m) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin m → ℝ) × X → X))
    ((rnPolyfold m).prod PX) B
  -- `F` is transversal at `(0, y)` for every zero `y` of `g`
  have hsurjAll : ∀ y, IsZeroAt P (sectionAdd P f s₀) y →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsLinSurjAt
        (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) (0, y) := by
    intro y hy
    obtain ⟨x, hxT, hyUx⟩ := mem_iUnion₂.1 (hT hy)
    have := MPolyfold.paracompactSpace_prod (rnPolyfold (k x)) PX
    have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin (k x) → ℝ) × X → X))
      ((rnPolyfold (k x)).prod PX) B
    have hsx := hUx x y hyUx hy
    refine isLinSurjAt_paramSection_zero_of_comp hgF ht (fun i => e ⟨⟨x, hxT⟩, i⟩) (hsp x)
      (fun i => ?_) hy hsx
    have := congrArg (fun σ : (Σ x : T, Fin (k x.1)) => s σ.1.1 σ.2)
      (e.symm_apply_apply ⟨⟨x, hxT⟩, i⟩)
    exact this.symm
  -- the open set `V ⊇ {0} × S_g` of zeros of `F` in good position
  obtain ⟨V, hVo, h0V, hVgood⟩ :=
    exists_isOpen_goodPosition_of_isLinSurjAt hX hgFt ht hsurjAll
  -- the perturbations `s_λ` are allowable for `|λ| ≤ δ₁ = ε/(m + 1)`
  set δ₁ : ℝ := ε / (m + 1) with hδ₁
  have hδ₁pos : 0 < δ₁ := div_pos hε (by positivity)
  have hallow : ∀ lam : Fin m → ℝ, ‖lam‖ ≤ δ₁ →
      ∀ x, B.AuxLe N (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x) 1 := fun lam hlam x =>
    auxLe_paramSlice hN hs₀ ht hs₀N htN (by
      calc (m : ℝ) * ‖lam‖ ≤ m * δ₁ := mul_le_mul_of_nonneg_left hlam (by positivity)
        _ = ε * (m / (m + 1)) := by rw [hδ₁]; ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
            ((div_le_one (by positivity)).2 (by linarith)) hε.le
        _ = ε := mul_one ε) x
  have hsuppl : ∀ lam : Fin m → ℝ, ∀ x ∉ U,
      IsZeroAt P (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) x := fun lam x hx =>
    isZeroAt_paramSlice_of_not_mem_support hs₀.1 _ lam (fun h => hx (hs₀supp h))
      fun i h => hx (htsupp i h)
  have hslice : ∀ lam : Fin m → ℝ, sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) =
      paramSlice (sectionAdd P f s₀) hgF.isScSmooth.1 t (fun i => (ht i).1) lam := fun lam =>
    sectionAdd_paramSlice hfs hs₀.1 _ lam
  -- the zeros of `F` over `|λ| ≤ δ₁` form a compact set `Z`
  set Z : Set ((Fin m → ℝ) × X) := {z | ‖z.1‖ ≤ δ₁ ∧ IsZeroAt (pullbackProj P Prod.snd)
    (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) z} with hZdef
  have hZsub : Z ⊆ Metric.closedBall (0 : Fin m → ℝ) δ₁ ×ˢ closure {x ∈ U | B.AuxLe N (f x) 1} := by
    rintro ⟨lam, x⟩ ⟨hlam, hz⟩
    refine ⟨mem_closedBall_zero_iff.2 hlam, ?_⟩
    have hx' : IsZeroAt P (paramSlice (sectionAdd P f s₀) hgF.isScSmooth.1 t
        (fun i => (ht i).1) lam) x := (isZeroAt_paramSection_iff (lam, x)).1 hz
    rw [← hslice lam] at hx'
    exact subset_closure ((remark_5_12 hN hfs hSU hK (isSection_paramSlice lam) (hsuppl lam)
      (hallow lam hlam)).1 hx')
  have hZclosed : IsClosed Z :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_solutionSet (theorem_3_18 hgF ht).isScSmooth)
  have hZ : IsCompact Z :=
    ((isCompact_closedBall _ _).prod hK).of_isClosed_subset hZclosed hZsub
  -- the omitted step: `Z ∩ {|λ| < δ₀} ⊆ V`
  obtain ⟨δ₀, hδ₀, hδ₀V⟩ := exists_pos_forall_mem_of_isCompact hZ hVo fun z hz hz1 => by
    have hz2 : IsZeroAt P (sectionAdd P f s₀) z.2 := by
      have := (isZeroAt_paramSection_iff z).1 hz.2
      rw [hz1, paramSlice_zero] at this; exact this
    have hz' : z = (0, z.2) := Prod.ext hz1 rfl
    rw [hz']; exact h0V z.2 hz2
  -- the Sard step on the compact `Z₀ = Z ∩ {|λ| ≤ δ/2}`, `δ = min δ₀ δ₁`
  set δ : ℝ := min δ₀ δ₁ with hδ
  have hδpos : 0 < δ := lt_min hδ₀ hδ₁pos
  set Z₀ : Set ((Fin m → ℝ) × X) := {z | ‖z.1‖ ≤ δ / 2 ∧ IsZeroAt (pullbackProj P Prod.snd)
    (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) z} with hZ₀def
  have hZ₀Z : Z₀ ⊆ Z := fun z hz => ⟨hz.1.trans (by linarith [min_le_right δ₀ δ₁]), hz.2⟩
  have hZ₀closed : IsClosed Z₀ :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_solutionSet (theorem_3_18 hgF ht).isScSmooth)
  have hZ₀ : IsCompact Z₀ := hZ.of_isClosed_subset hZ₀closed hZ₀Z
  have hZ₀V : ∀ z ∈ Z₀, z ∈ V := fun z hz =>
    hδ₀V z (hZ₀Z hz) (by linarith [min_le_left δ₀ δ₁, hz.1])
  have hloc : ∀ z : Z₀, ∃ W : Set ((Fin m → ℝ) × X), IsOpen W ∧ (z : (Fin m → ℝ) × X) ∈ W ∧
      ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
        ∀ z' ∈ W, IsZeroAt (pullbackProj P Prod.snd)
          (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) z' →
          z'.1 ∉ CV → B.IsLinSurjAt (paramSlice (sectionAdd P f s₀) hgF.isScSmooth.1 t
            (fun i => (ht i).1) z'.1) z'.2 := fun z =>
    exists_null_isLinSurjAt_paramSlice_near hgFt ht z.2.2
      (hVgood z (hZ₀V z z.2) z.2.2)
  choose W hWo hzW CV hCV hWtr using hloc
  obtain ⟨T', hT'⟩ := hZ₀.elim_finite_subcover W hWo
    (fun z hz => mem_iUnion.2 ⟨⟨z, hz⟩, hzW ⟨z, hz⟩⟩)
  refine ⟨m, t, ht, htsupp, htN, δ / 2, by positivity, ⋃ z ∈ T', CV z, ?_,
    fun lam hlam hlamCV => ?_⟩
  · exact (measure_biUnion_null_iff T'.countable_toSet).2 fun z _ => hCV z
  -- the conclusions for `λ`
  have hlam₁ : ‖lam‖ ≤ δ₁ := by linarith [min_le_right δ₀ δ₁]
  have hsl : B.IsScPlusSection (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) :=
    isScPlusSection_paramSlice hs₀ ht lam
  have halw : paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam ∈ B.allowableSections N U := by
    refine ⟨hsl, (sectionSupport_paramSlice_subset hs₀.1 _ lam).trans
      (union_subset hs₀supp (iUnion_subset htsupp)), fun x hx => ?_⟩
    obtain ⟨hx', h⟩ := hallow lam hlam₁ x
    exact h
  have htrans :
      B.IsTransversal (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)) := by
    intro y hy
    rw [hslice lam] at hy ⊢
    have hzZ₀ : (lam, y) ∈ Z₀ := ⟨hlam.le, (isZeroAt_paramSection_iff (lam, y)).2 hy⟩
    obtain ⟨z, hzT', hzW'⟩ := mem_iUnion₂.1 (hT' hzZ₀)
    have hlamCV' : lam ∉ CV z := fun h => hlamCV (mem_iUnion₂.2 ⟨z, hzT', h⟩)
    exact hWtr z (lam, y) hzW' ((isZeroAt_paramSection_iff (lam, y)).2 hy) hlamCV'
  refine ⟨halw, htrans, hcpt _ halw, fun hne => ?_⟩
  exact theorem_3_56_of_surjective hX (theorem_3_15_tame hf hsl) htrans hne

variable (B) in
/-- **The distance `N(s(x) − s'(x))` of two sc⁺-sections at `x`**: the text's uniform distance
`ρ(s, s') = sup_x N(s(x) − s'(x))` on `Γ^{+,1}_U(P)`, pointwise (the difference is taken in the
fibre `(Y_{0,1})_x`). -/
def StrongBundle.sectionDistAt (N : B.One → ℝ) {s s' : X → Y} (hs : B.IsScPlusSection s)
    (hs' : B.IsScPlusSection s') (x : X) : ℝ :=
  N (B.toOne ((⟨⟨s x, hs.1 x⟩, hs.mem_oneSet x⟩ : B.oneFiber x) -
    ⟨⟨s' x, hs'.1 x⟩, hs'.mem_oneSet x⟩))

set_option maxHeartbeats 1600000 in
-- the fibre arithmetic in `(Y_{0,1})_x` with the destructured generic form
/-- **Theorem 5.13 (perturbation and transversality, interior case)**, the text's dense-set
form.  Let `P : Y → X` be a strong bundle over an M-polyfold `X` with `∂X = ∅` which admits
sc-smooth bump functions, `f` an sc-Fredholm section with compact solution set, `N` an auxiliary
norm (and `f` with tame germ data, as in `theorem_5_13_generic`).  Then there is an open neighbourhood
`U` of `S_f` such that for every allowable section `s ∈ Γ^{+,1}_U(P)` the solution set `S_{f+s}`
is compact, and the allowable sections `s` for which `f + s` is transversal to the zero section
and `S_{f+s}` is a compact smooth manifold without boundary are dense in `(Γ^{+,1}_U(P), ρ)`: for
every allowable `s'` and `ε > 0` there is such an `s` with `N(s(x) − s'(x)) ≤ ε` for all `x`.
*Proof* (the text's): `s₀ = (1 − ε'/2)s'`, `ε' = min(ε, 1)`, has `N(s₀) ≤ 1 − ε'/2`; the generic
form gives `t`, `δ`, `CV`; a `λ ∉ CV` with `|λ| < δ` and `m|λ| ≤ ε'/2` exists because `CV` is
null and the ball has positive measure; `s = s₀ + Σ λᵢ tᵢ` satisfies
`N(s − s') ≤ (ε'/2)N(s') + Σ|λᵢ| N(tᵢ) ≤ ε'`.  (The text's "`N(s₀(y) + s(λ₀, y)) ≤ 1 − ε/2`" is
a slip for `≤ 1`.) -/
theorem theorem_5_13 (hX : PX.IsWithoutBoundary) (hbump : PX.AdmitsBumpFunctions)
    {f : X → Y} (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f))
    {N : B.One → ℝ} (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ (s' : X → Y) (hs' : B.IsScPlusSection s'), s' ∈ B.allowableSections N U → ∀ ε > 0,
        ∃ (s : X → Y) (hs : B.IsScPlusSection s), s ∈ B.allowableSections N U ∧
          (∀ x, B.sectionDistAt N hs hs' x ≤ ε) ∧
          B.IsTransversal (sectionAdd P f s) ∧ IsCompact (solutionSet P (sectionAdd P f s)) ∧
          ((solutionSet P (sectionAdd P f s)).Nonempty →
            B.SolutionSetIsManifold (sectionAdd P f s)) := by
  classical
  obtain ⟨U, hUo, hSU, hcpt, hgen⟩ := theorem_5_13_generic hX hbump hf hS hN
  refine ⟨U, hUo, hSU, hcpt, fun s' hs' hs'alw ε hε => ?_⟩
  obtain ⟨-, hs'supp, hs'N⟩ := hs'alw
  -- `ε' = min ε 1`, `θ = 1 − ε'/2`, `s₀ = θ s'`
  set ε' : ℝ := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'le1 : ε' ≤ 1 := min_le_right _ _
  set θ : ℝ := 1 - ε' / 2 with hθ
  have hθpos : 0 < θ := by rw [hθ]; linarith
  set s₀ : X → Y := sectionSmul P (fun _ => θ) s' with hs₀def
  have hs₀ : B.IsScPlusSection s₀ := hs'.smul_left (isScSmoothMap_real_const _)
  have hs₀supp : sectionSupport P s₀ ⊆ U :=
    (sectionSupport_sectionSmul_const_subset hs'.1 θ).trans hs'supp
  have hs₀N : ∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ 1 - ε' / 2 := fun x hx => by
    rw [hN.oneMk_sectionSmul_const hs' θ x hx, abs_of_pos hθpos]
    calc θ * N (B.oneMk (s' x) (hs'.mem_oneSet x)) ≤ θ * 1 :=
          mul_le_mul_of_nonneg_left (hs'N x _) hθpos.le
      _ = 1 - ε' / 2 := by rw [mul_one]
  obtain ⟨m, t, ht, htsupp, htN, δ, hδ, CV, hCV, hlam⟩ :=
    hgen s₀ hs₀ hs₀supp (ε' / 2) (by positivity) hs₀N
  -- a parameter `λ ∉ CV` with `|λ| < δ` and `m|λ| ≤ ε'/2`
  set r : ℝ := min δ (ε' / (2 * (m + 1))) with hr
  have hrpos : 0 < r := lt_min hδ (by positivity)
  obtain ⟨lam, hlamr, hlamCV⟩ : ∃ lam ∈ Metric.ball (0 : Fin m → ℝ) r, lam ∉ CV := by
    by_contra h
    have h1 : Metric.ball (0 : Fin m → ℝ) r ⊆ CV := fun lam hl => by
      by_contra hc
      exact h ⟨lam, hl, hc⟩
    have h2 := measure_mono_null h1 hCV
    exact (Metric.measure_ball_pos volume (0 : Fin m → ℝ) hrpos).ne' h2
  have hlamδ : ‖lam‖ < δ := lt_of_lt_of_le (mem_ball_zero_iff.1 hlamr) (min_le_left _ _)
  have hlamε : (m : ℝ) * ‖lam‖ ≤ ε' / 2 := by
    have h1 : ‖lam‖ ≤ ε' / (2 * (m + 1)) :=
      (mem_ball_zero_iff.1 hlamr).le.trans (min_le_right _ _)
    calc (m : ℝ) * ‖lam‖ ≤ m * (ε' / (2 * (m + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (ε' / 2) * (m / (m + 1)) := by field_simp
      _ ≤ (ε' / 2) * 1 := mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity)).2 (by linarith)) (by positivity)
      _ = ε' / 2 := mul_one _
  obtain ⟨halw, htrans, hcompact, hmfd⟩ := hlam lam hlamδ hlamCV
  have hsl : B.IsScPlusSection (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) :=
    isScPlusSection_paramSlice hs₀ ht lam
  refine ⟨_, hsl, halw, fun x => ?_, htrans, hcompact, hmfd⟩
  -- the distance: `s(x) − s'(x) = (θ − 1) s'(x) + Σ λᵢ tᵢ(x)` in the fibre
  set u' : B.oneFiber x := ⟨⟨s' x, hs'.1 x⟩, hs'.mem_oneSet x⟩ with hu'
  set w : Fin m → B.oneFiber x := fun i => ⟨⟨t i x, (ht i).1 x⟩, (ht i).mem_oneSet x⟩ with hw
  have hu : (⟨⟨paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x, hsl.1 x⟩, hsl.mem_oneSet x⟩ :
      B.oneFiber x) = θ • u' + ∑ i, lam i • w i := by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    apply Subtype.ext
    change paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x = _
    unfold paramSlice
    have h1 : (⟨s₀ x, hs₀.1 x⟩ : P ⁻¹' {x}) = θ • ⟨s' x, hs'.1 x⟩ :=
      Subtype.ext (sectionSmul_apply (f := fun _ => θ) hs'.1 x)
    rw [h1]
    rfl
  have hdiff : (⟨⟨paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x, hsl.1 x⟩, hsl.mem_oneSet x⟩ :
      B.oneFiber x) - u' = (θ - 1) • u' + ∑ i, lam i • w i := by
    rw [hu, add_sub_right_comm, hθ]
    simp only [sub_smul, one_smul]
  have hli : ∀ i, |lam i| ≤ ‖lam‖ := fun i => by
    have := norm_le_pi_norm lam i
    rwa [Real.norm_eq_abs] at this
  have hwN : ∀ i, N (B.toOne (w i)) ≤ 1 := fun i => htN i x ((ht i).mem_oneSet x)
  have hu'N : N (B.toOne u') ≤ 1 := hs'N x _
  change N (B.toOne (_ - u')) ≤ ε
  rw [hdiff]
  calc N (B.toOne ((θ - 1) • u' + ∑ i, lam i • w i))
      ≤ N (B.toOne ((θ - 1) • u')) + N (B.toOne (∑ i, lam i • w i)) := (hN.fiber x).add_le _ _
    _ = |θ - 1| * N (B.toOne u') + N (B.toOne (∑ i, lam i • w i)) := by rw [hN.smul]
    _ ≤ (ε' / 2) * 1 + ∑ i, N (B.toOne (lam i • w i)) := by
        refine add_le_add ?_ (hN.toOne_sum_le _ _)
        have hθ1 : |θ - 1| = ε' / 2 := by
          rw [hθ, show (1 - ε' / 2 - 1 : ℝ) = -(ε' / 2) by ring, abs_neg,
            abs_of_pos (by positivity)]
        rw [hθ1]
        exact mul_le_mul_of_nonneg_left hu'N (by positivity)
    _ = ε' / 2 + ∑ i, |lam i| * N (B.toOne (w i)) := by
        rw [mul_one]
        congr 1
        exact Finset.sum_congr rfl fun i _ => hN.smul (w i) (lam i)
    _ ≤ ε' / 2 + ∑ _i : Fin m, ‖lam‖ * 1 :=
        add_le_add le_rfl (Finset.sum_le_sum fun i _ =>
          mul_le_mul (hli i) (hwN i) (hN.nonneg _) (norm_nonneg _))
    _ = ε' / 2 + (m : ℝ) * ‖lam‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    _ ≤ ε := by linarith

end Theorem513

end Polyfold
