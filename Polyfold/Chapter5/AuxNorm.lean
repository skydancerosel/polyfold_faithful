import Polyfold.Chapter2.StrongBundleOne
import Polyfold.Chapter3.StrongBundleSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §5.1,
**Definition 5.1, Lemma 5.2, Proposition 5.3** (auxiliary norms)
*(book 2017: Definition 5.1, Lemma 5.1, Proposition 5.1; see `BookConcordance.md`)*.

# Auxiliary norms

## The text, paraphrased

(§5.1) For a strong bundle `P : Y → X` over a tame M-polyfold, the subset `Y_{0,1}` of
biregularity `(0, 1)` is a topological space, `P : Y_{0,1} → X` is continuous, and the fibres
`Y_x = P⁻¹(x)` are Banach spaces.  (Definition 5.1) An auxiliary norm is a continuous
`N : Y_{0,1} → ℝ` such that (1) the restriction of `N` to a fibre is a complete norm, and (2) if
`(w_k) ⊆ Y_{0,1}` with `P(w_k) → x` and `N(w_k) → 0`, then `w_k → 0_x` in `Y_{0,1}`.
(Lemma 5.2) For a continuous `N : Y_{0,1} → ℝ` which is fibrewise a complete norm, (i) `N` is an
auxiliary norm iff (ii) every `x` has a strong bundle isomorphism `Φ : Y|V → K` and constants
`0 < c < C` with `c·N(w) ≤ |h|₁ ≤ C·N(w)` for `w ∈ P⁻¹(V)`, `Φ(w) = (p, h)`.  Proof of (i) ⇒ (ii):
by continuity `N < 1` on a neighbourhood `|p − q|₀ + |h|₁ < ε` of `0_x`, and homogeneity gives
`N(w) ≤ (2/ε)|h|₁`; if no `c` existed, sequences `|h_k|₁ = 1`, `N(w_k) → 0`, `P(w_k) → x` would
contradict (2).  (ii) ⇒ (i) is "obvious".  (Proposition 5.3) Auxiliary norms exist (a partition
of unity on the paracompact `X`, pulling back `|·|₁` by strong bundle charts), and for two of them
there is a continuous `f : X → (0, ∞)` with `f(x)·N₀ ≤ N₁ ≤ (1/f(x))·N₀` on `P⁻¹(x)`.

## What is formalized

* **The charts `Φ[1]` for every strong bundle chart of `P`** (compatible with the atlas, not only
  those of the atlas): `StrongBundle.mem_oneSet_iff_of_isChart`, `StrongBundle.oneChartOf` (the
  chart `Φ[1] : P⁻¹(V)[1] → K[1]` of `Y[1]`), `StrongBundle.isChart_oneChartOf` (a chart of the
  M-polyfold `Y[1]`), `oneChartOf_overlap`, `oneChartOf_transition`, `oneChartOf_compatible`.
* **The fibre `(Y_{0,1})_x`** as a submodule of `P⁻¹(x)`: `StrongBundle.oneFiber`, with
  `StrongBundle.toOne`, `StrongBundle.ofOne` (the passage between the fibre and `Y[1]`) and
  `StrongBundle.zeroOne` (the zero `0_x` in `Y[1]`); **its norm `|·|₁` read in a strong bundle
  chart**: the injective linear map `StrongBundle.liftOneFiber : (Y_{0,1})_x → F₁`
  (`liftOneFiber_injective`), its range (`mem_range_liftOneFiber`, `isClosed_slice`) and
  `StrongBundle.complete_liftOneFiber` (**the fibre is complete for `|·|₁`**).
* `StrongBundle.IsCompleteFiberNorm` (**Definition 5.1 (1)**) and `StrongBundle.IsAuxNorm`
  (**Definition 5.1**), with `IsAuxNorm.nonneg`, `IsAuxNorm.smul`.
* **Lemma 5.2**: `StrongBundle.exists_le_mul_norm_liftOne` (the upper bound `g ≤ C·|h|₁` for any
  `g` continuous at `0_x` and homogeneous on the fibres), `IsAuxNorm.exists_norm_liftOne_le` (the
  lower bound, from (2) by contradiction), `IsAuxNorm.exists_bounds` (**(i) ⇒ (ii) in every
  strong bundle chart around `x`**) and `Polyfold.lemma_5_2` (the equivalence).
* **Proposition 5.3**: `StrongBundle.gluedNorm` (`N(w) = Σᵢ ρᵢ(P(w))·|Φᵢ[1](w)|₁`),
  `continuous_gluedNorm`, `isCompleteFiberNorm_gluedNorm`, `gluedNorm_bounds`,
  `Polyfold.proposition_5_3_exists` (**existence**) and `Polyfold.proposition_5_3_compare`
  (**comparison by a continuous `f : X → (0, ∞)`**, by
  `exists_continuous_forall_mem_convex_of_local_const`).
  The auxiliary comparisons `exists_norm_liftOne_le_mul` (the norms `|·|₁` of two charts are
  locally comparable), `exists_uniform_comparison` and `complete_of_bounds`.

## What the text leaves implicit, and the choices made

* **The fibres of `Y_{0,1}` carry no normed structure in the project** (only the fibres `P⁻¹(x)`
  carry linear structures).  The fibre `(Y_{0,1})_x` is defined here as the subspace of `P⁻¹(x)`
  whose points lie in `Y_{0,1}`; it is a subspace because the charts are linear on the fibres and
  `F₁ ⊆ F₀` is a subspace.  The text's `|h|₁` is the `F₁`-norm of the fibre component of
  `Φ[1](w)`; it depends on the chart, but any two are equivalent on each fibre and locally uniformly
  (`exists_norm_liftOne_le_mul`: continuity of `Φ'[1] ∘ Φ[1]⁻¹` at the zero section and fibre
  linearity, the argument of the first half of Lemma 5.2).
* **"Complete norm" (Definition 5.1 (1)) is read as: `N` is a norm on `(Y_{0,1})_x` and the fibre
  with `N` is complete** (`IsCompleteFiberNorm`: `N(v) = 0 ⇒ v = 0`, `N(tv) = |t|N(v)`, the triangle
  inequality, and every `N`-Cauchy sequence converges).  The fibre with the chart norm `|·|₁` is
  complete because it is the slice `{h ∈ F₁ | (φ(x), h) ∈ K[1]}`, closed as the fixed point set of
  the continuous `h ↦ R[1](φ(x), h)`; the text takes this for granted ("the fibers have the
  structure of Banach spaces").
* `N` is a function on `Y[1]` (`B.One`, the set `Y_{0,1}` with the topology of §2.5), so its
  continuity and the convergence `w_k → 0_x` in (2) are in that topology, as the text says.
  Condition (2) is stated with sequences, as in the text.
* **Lemma 5.2 (ii)** is stated with a strong bundle chart of `P` (`B.IsChart`), the text's "strong
  bundle isomorphism `Φ : Y|V → K`", and a neighbourhood `V ⊆ dom φ` of `x`; the text's `V` is the
  domain of `Φ`, but its own proof only gives the bounds "for `P(w)` close to `x`", so `V` is a
  neighbourhood on which they hold.  The direction (i) ⇒ (ii) holds in *every* strong bundle chart
  around `x` (`IsAuxNorm.exists_bounds`), which Proposition 5.3 uses.  The direction (ii) ⇒ (i),
  "obvious" in the text, needs that `Φ[1]` is a homeomorphism onto `K[1]` for a chart compatible
  with the atlas (`oneChartOf`): `Φ[1](w_k) → (φ(x), 0)` gives `w_k → 0_x`.
* **The proof of Lemma 5.2 needs no metrizability**: the contradiction argument uses the
  neighbourhoods `φ⁻¹(B(φ(x), 1/(k + 1)))` of the chart, whose points converge to `x` because `φ⁻¹`
  is continuous on `O`.
* **Proposition 5.3, existence.**  The glued norm `Σᵢ ρᵢ(P(w))·|Φᵢ[1](w)|₁` (over the charts of
  the atlas, `(ρᵢ)` a partition of unity subordinate to their domains, which exists since `X` is
  paracompact and Hausdorff, hence normal) is continuous on `Y[1]` (each term has closed support in
  the domain of `Φᵢ[1]`, and the sum is locally finite), a norm on each fibre, complete and
  comparable to the norm of any chart near each point (the finitely many charts meeting a
  neighbourhood of `x` are uniformly comparable there); Lemma 5.2 (ii) ⇒ (i) concludes.  The text
  gives one sentence.
* **Proposition 5.3, comparison.**  The text's "the local compatibility implies the existence of
  `f`" is: Lemma 5.2 (i) ⇒ (ii) for `N₀` and `N₁` in the same chart around `x` gives a local
  constant `r_x > 0` with `r_x N₀ ≤ N₁` and `r_x N₁ ≤ N₀` near `x`; the set of admissible `r` at
  each point is convex, so a partition of unity glues the constants into a continuous `f`
  (`exists_continuous_forall_mem_convex_of_local_const`).
* **Tameness is not used**: §5.1 places the strong bundle over a tame M-polyfold, but Definition
  5.1, Lemma 5.2 and Proposition 5.3 hold for every strong bundle (Lemma 5.2 is stated in the text
  without tameness).
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundle

/-! ### The charts `Φ[1]` of `Y[1]` for every strong bundle chart of `P` -/

section OneChartOf

variable {B : StrongBundle PX P} {c : StrongBundleChart PX P}

/-- `Y_{0,1}` read in a strong bundle chart of `P` (compatible with the atlas, not necessarily a
member of it): `y ∈ Y_{0,1}` iff the fibre component of `Φ(y)` lies in `F₁`. -/
theorem mem_oneSet_iff_of_isChart (hc : B.IsChart c) {y : Y} (hy : y ∈ c.toPartialEquiv.source) :
    y ∈ B.oneSet ↔ (c y).2 ∈ range (c.F.toBase 1) := by
  obtain ⟨c', hc', hy'⟩ := B.atlas.cover y
  rw [B.mem_oneSet_iff hc' hy']
  have hcomp := hc c' hc'
  constructor
  · intro h
    have := hcomp.2.2.2.2.2 (c' y) ⟨y, ⟨hy', hy⟩, rfl⟩ h
    rwa [c'.transition_apply c hy'] at this
  · intro h
    have := hcomp.2.2.2.2.1 (c y) ⟨y, ⟨hy, hy'⟩, rfl⟩ h
    rwa [c.transition_apply c' hy] at this

lemma symm_mem_oneSet_of_isChart (hc : B.IsChart c) {z : (c.φ.model.E.prod c.F.shift) 0}
    (hz : z ∈ strongShiftOne c.K) : c.toPartialEquiv.symm (z.1, c.F.toBase 1 z.2) ∈ B.oneSet := by
  have hz' : (z.1, c.F.toBase 1 z.2) ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hz
  rw [mem_oneSet_iff_of_isChart hc (c.toPartialEquiv.map_target hz'),
    c.toPartialEquiv.right_inv hz']
  exact ⟨z.2, rfl⟩

open scoped Classical in
/-- The inverse `K[1] → P⁻¹(V)[1]` of `Φ[1]` for a strong bundle chart of `P`, with the junk value
`y₀`. -/
def oneChartInvOf (hc : B.IsChart c) (y₀ : B.One) (z : (c.φ.model.E.prod c.F.shift) 0) : B.One :=
  if h : z ∈ strongShiftOne c.K then B.oneMk _ (symm_mem_oneSet_of_isChart hc h) else y₀

lemma oneVal_oneChartInvOf (hc : B.IsChart c) (y₀ : B.One) {z : (c.φ.model.E.prod c.F.shift) 0}
    (hz : z ∈ strongShiftOne c.K) :
    B.oneVal (oneChartInvOf hc y₀ z) = c.toPartialEquiv.symm (z.1, c.F.toBase 1 z.2) := by
  unfold oneChartInvOf; rw [dif_pos hz]; rfl

omit [T2Space Y] [ParacompactSpace Y] in
lemma liftOne_symm' {z : (c.φ.model.E.prod c.F.shift) 0} (hz : z ∈ strongShiftOne c.K) :
    c.liftOne (c.toPartialEquiv.symm (z.1, c.F.toBase 1 z.2)) = z := by
  have hz' : (z.1, c.F.toBase 1 z.2) ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hz
  unfold StrongBundleChart.liftOne
  rw [show c (c.toPartialEquiv.symm (z.1, c.F.toBase 1 z.2)) = (z.1, c.F.toBase 1 z.2) from
    c.toPartialEquiv.right_inv hz']
  exact Prod.ext rfl (c.F.toBase_injective 1 (Function.invFun_eq ⟨z.2, rfl⟩))

/-- For two strong bundle charts `c'`, `c` and `y ∈ Y_{0,1}` in both domains,
`(Φ ∘ Φ'⁻¹)[1](Φ'[1](y)) = Φ[1](y)`. -/
lemma shiftFiber_transition_liftOne {c' : StrongBundleChart PX P}
    {y : Y} (hy' : y ∈ c'.toPartialEquiv.source) (h1 : y ∈ B.oneSet) (hc' : B.IsChart c') :
    shiftFiber (c'.transition c) (c'.liftOne y) = c.liftOne y := by
  have h2 : (c' y).2 ∈ range (c'.F.toBase 1) := (mem_oneSet_iff_of_isChart hc' hy').1 h1
  unfold shiftFiber
  rw [c'.toBase_liftOne h2, c'.transition_apply c hy']
  rfl

/-- `Φ'[1](y) ∈ Φ'(P⁻¹(V ∩ V'))[1]` for `y ∈ Y_{0,1}` in both domains. -/
lemma liftOne_mem_overlap (hc' : B.IsChart c) {c' : StrongBundleChart PX P} {y : Y}
    (hy : y ∈ c.toPartialEquiv.source) (hy' : y ∈ c'.toPartialEquiv.source) (h1 : y ∈ B.oneSet) :
    c.liftOne y ∈ strongShiftOne (c.overlap c') := by
  have h2 : (c y).2 ∈ range (c.F.toBase 1) := (mem_oneSet_iff_of_isChart hc' hy).1 h1
  change ((c.liftOne y).1, c.F.toBase 1 (c.liftOne y).2) ∈ c.overlap c'
  rw [c.toBase_liftOne h2]
  exact ⟨y, ⟨hy, hy'⟩, rfl⟩

/-- **The chart `Φ[1] : P⁻¹(V)[1] → K[1]` of `Y[1]` for a strong bundle chart `Φ` of `P`**
(compatible with the atlas, not necessarily in it; for a chart of the atlas it is
`StrongBundle.oneChart`). -/
def oneChartOf (hc : B.IsChart c) (y₀ : B.One) : MChart B.One where
  model := ⟨c.φ.model.E.prod c.F.shift, c.φ.model.C ×ˢ univ, strongShiftOne c.K,
    c.isScRetract_one⟩
  toPartialEquiv :=
    { toFun := fun y => c.liftOne (B.oneVal y)
      invFun := oneChartInvOf hc y₀
      source := {y | B.oneVal y ∈ c.toPartialEquiv.source}
      target := strongShiftOne c.K
      map_source' := fun y hy =>
        c.liftOne_mem hy ((mem_oneSet_iff_of_isChart hc hy).1 (B.oneVal_mem y))
      map_target' := fun z hz => by
        change B.oneVal (oneChartInvOf hc y₀ z) ∈ c.toPartialEquiv.source
        rw [oneVal_oneChartInvOf hc y₀ hz]
        exact c.toPartialEquiv.map_target (by rw [c.target_eq]; exact hz)
      left_inv' := fun y hy => by
        have hy1 := (mem_oneSet_iff_of_isChart hc hy).1 (B.oneVal_mem y)
        apply B.oneVal_injective
        rw [oneVal_oneChartInvOf hc y₀ (c.liftOne_mem hy hy1), c.toBase_liftOne hy1]
        exact c.toPartialEquiv.left_inv hy
      right_inv' := fun z hz => by
        change c.liftOne (B.oneVal (oneChartInvOf hc y₀ z)) = z
        rw [oneVal_oneChartInvOf hc y₀ hz]
        exact liftOne_symm' hz }
  isOpen_source := by
    change IsOpen (B.oneVal ⁻¹' c.toPartialEquiv.source)
    exact (c.isOpen_source B.continuous).preimage B.continuous_oneVal
  target_eq := rfl
  continuousOn_toFun := by
    intro y hy
    obtain ⟨c', hc', hyc'⟩ := B.atlas.cover (B.oneVal y)
    have hc'' : B.IsChart c' := B.isChart_of_mem hc'
    set S : Set B.One :=
      {w | B.oneVal w ∈ c.toPartialEquiv.source ∩ c'.toPartialEquiv.source} with hS
    have hSo : IsOpen S :=
      ((c.isOpen_source B.continuous).inter (c'.isOpen_source B.continuous)).preimage
        B.continuous_oneVal
    have h1 : ContinuousOn (fun w => c'.liftOne (B.oneVal w)) S :=
      (oneChart hc' y).continuousOn_toFun.mono fun w hw => hw.2
    have h2 : ContinuousOn (shiftFiber (c'.transition c)) (strongShiftOne (c'.overlap c)) :=
      (hc c' hc').2.2.2.1.continuousOn (c'.isScRetract_overlap_one c B.continuous)
    have h3 : ContinuousOn (fun w => shiftFiber (c'.transition c) (c'.liftOne (B.oneVal w))) S :=
      h2.comp h1 fun w hw => liftOne_mem_overlap hc'' hw.2 hw.1 (B.oneVal_mem w)
    have h4 : ContinuousOn (fun w => c.liftOne (B.oneVal w)) S :=
      h3.congr fun w hw =>
        (shiftFiber_transition_liftOne hw.2 (B.oneVal_mem w) hc'').symm
    exact (h4.continuousAt (hSo.mem_nhds ⟨hy, hyc'⟩)).continuousWithinAt
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨c', hc', W, hW, rfl⟩
    obtain ⟨W₀, hW₀, hW₀eq⟩ := c.overlap_eq_inter c' B.continuous
    have hcont : ContinuousOn (shiftFiber (c.transition c')) (strongShiftOne (c.overlap c')) :=
      (hc c' hc').2.2.1.continuousOn (c.isScRetract_overlap_one c' B.continuous)
    obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hcont) W hW
    set g : (c.φ.model.E.prod c.F.shift) 0 → c.φ.model.E 0 × c.F 0 :=
      fun p => (p.1, c.F.toBase 1 p.2) with hg
    have hgc : Continuous g := continuous_fst.prodMk ((c.F.toBase 1).continuous.comp continuous_snd)
    refine isOpen_induced_iff.2 ⟨g ⁻¹' W₀ ∩ u, (hW₀.preimage hgc).inter hu, ?_⟩
    ext ⟨z, hz⟩
    rw [iff_comm]
    have hz' : (z.1, c.F.toBase 1 z.2) ∈ c.toPartialEquiv.target := by
      rw [c.target_eq]; exact hz
    change (B.oneVal (oneChartInvOf hc y₀ z) ∈ c'.toPartialEquiv.source ∧
      c'.liftOne (B.oneVal (oneChartInvOf hc y₀ z)) ∈ W) ↔ _
    rw [oneVal_oneChartInvOf hc y₀ hz]
    have hov : z ∈ strongShiftOne (c.overlap c') ↔
        c.toPartialEquiv.symm (z.1, c.F.toBase 1 z.2) ∈ c'.toPartialEquiv.source := by
      constructor
      · rintro ⟨y, hy, hyeq⟩
        rw [← hyeq, c.toPartialEquiv.left_inv hy.1]; exact hy.2
      · intro h
        exact ⟨_, ⟨c.toPartialEquiv.map_target hz', h⟩, c.toPartialEquiv.right_inv hz'⟩
    have hsf : c'.liftOne (c.toPartialEquiv.symm (z.1, c.F.toBase 1 z.2)) =
        shiftFiber (c.transition c') z := rfl
    rw [hsf]
    have hovW : z ∈ strongShiftOne (c.overlap c') ↔ g z ∈ W₀ := by
      change (z.1, c.F.toBase 1 z.2) ∈ c.overlap c' ↔ _
      rw [hW₀eq]; exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
    constructor
    · rintro ⟨h1, h2⟩
      have hzov : z ∈ strongShiftOne (c.overlap c') := hov.2 h1
      have : z ∈ shiftFiber (c.transition c') ⁻¹' W ∩ strongShiftOne (c.overlap c') := ⟨h2, hzov⟩
      rw [hueq] at this
      exact ⟨hovW.1 hzov, this.1⟩
    · rintro ⟨h1, h2⟩
      have hzov : z ∈ strongShiftOne (c.overlap c') := hovW.2 h1
      refine ⟨hov.1 hzov, ?_⟩
      have : z ∈ u ∩ strongShiftOne (c.overlap c') := ⟨h2, hzov⟩
      rw [← hueq] at this
      exact this.1

lemma oneChartOf_apply (hc : B.IsChart c) (y₀ : B.One) (y : B.One) :
    oneChartOf hc y₀ y = c.liftOne (B.oneVal y) := rfl

lemma oneChartOf_source (hc : B.IsChart c) (y₀ : B.One) :
    (oneChartOf hc y₀).source = {y | B.oneVal y ∈ c.toPartialEquiv.source} := rfl

lemma mem_oneChartOf_source (hc : B.IsChart c) (y₀ : B.One) {y : B.One} :
    y ∈ (oneChartOf hc y₀).source ↔ P (B.oneVal y) ∈ c.φ.source := by
  change B.oneVal y ∈ c.toPartialEquiv.source ↔ _
  rw [c.source_eq]; rfl

lemma oneChartOf_symm_apply (hc : B.IsChart c) (y₀ : B.One) {z : (c.φ.model.E.prod c.F.shift) 0}
    (hz : z ∈ strongShiftOne c.K) :
    B.oneVal ((oneChartOf hc y₀).symm z) = c.toPartialEquiv.symm (z.1, c.F.toBase 1 z.2) :=
  oneVal_oneChartInvOf hc y₀ hz

/-- The chart `Φ[1]` of a chart of the atlas is `oneChart`. -/
lemma oneChart_eq_oneChartOf (hc : c ∈ B.atlas.charts) (y₀ : B.One) :
    oneChart hc y₀ = oneChartOf (B.isChart_of_mem hc) y₀ := rfl

/-- The overlap of two charts `Φ[1]`, `Φ'[1]` is `Φ(P⁻¹(V ∩ V'))[1]`. -/
lemma oneChartOf_overlap (hc : B.IsChart c) (y₀ : B.One) {c' : StrongBundleChart PX P}
    (hc' : B.IsChart c') (y₀' : B.One) :
    (oneChartOf hc y₀).overlap (oneChartOf hc' y₀') = strongShiftOne (c.overlap c') := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
    exact liftOne_mem_overlap hc hy hy' (B.oneVal_mem y)
  · rintro ⟨w, ⟨hw, hw'⟩, hweq⟩
    have hw1 : w ∈ B.oneSet :=
      (mem_oneSet_iff_of_isChart hc hw).2 (by rw [hweq]; exact ⟨z.2, rfl⟩)
    refine ⟨B.oneMk w hw1, ⟨hw, hw'⟩, ?_⟩
    change c.liftOne w = z
    unfold StrongBundleChart.liftOne
    rw [hweq]
    exact Prod.ext rfl (c.F.toBase_injective 1 (Function.invFun_eq ⟨z.2, rfl⟩))

lemma oneChartOf_transition (hc : B.IsChart c) (y₀ : B.One) {c' : StrongBundleChart PX P}
    (hc' : B.IsChart c') (y₀' : B.One) {z : (c.φ.model.E.prod c.F.shift) 0}
    (hz : z ∈ strongShiftOne c.K) :
    (oneChartOf hc y₀).transition (oneChartOf hc' y₀') z = shiftFiber (c.transition c') z := by
  change c'.liftOne (B.oneVal ((oneChartOf hc y₀).symm z)) = _
  rw [oneChartOf_symm_apply hc y₀ hz]
  rfl

/-- The charts `Φ[1]` of two compatible strong bundle charts are compatible charts of `Y[1]`: the
transition maps are the `[1]`-transitions of Definition 2.50. -/
theorem oneChartOf_compatible (hc : B.IsChart c) (y₀ : B.One) {c' : StrongBundleChart PX P}
    (hc' : c' ∈ B.atlas.charts) (y₀' : B.One) :
    (oneChartOf hc y₀).Compatible (oneChartOf (B.isChart_of_mem hc') y₀') := by
  have h := hc c' hc'
  constructor
  · rw [oneChartOf_overlap hc y₀ (B.isChart_of_mem hc') y₀',
      oneChartOf_overlap (B.isChart_of_mem hc') y₀' hc y₀]
    refine h.2.2.1.congr fun z hz => ?_
    exact (oneChartOf_transition hc y₀ (B.isChart_of_mem hc') y₀'
      (strongShiftOne_mono (c.overlap_subset_K c') hz)).symm
  · rw [oneChartOf_overlap (B.isChart_of_mem hc') y₀' hc y₀,
      oneChartOf_overlap hc y₀ (B.isChart_of_mem hc') y₀']
    refine h.2.2.2.1.congr fun z hz => ?_
    exact (oneChartOf_transition (B.isChart_of_mem hc') y₀' hc y₀
      (strongShiftOne_mono (c'.overlap_subset_K c) hz)).symm

/-- **`Φ[1]` is a chart of the M-polyfold `Y[1]`** for every strong bundle chart `Φ` of `P`. -/
theorem isChart_oneChartOf (hc : B.IsChart c) (y₀ : B.One) :
    B.toMPolyfold1.IsChart (oneChartOf hc y₀) := by
  rintro _ ⟨c', hc', y₀', rfl⟩
  rw [oneChart_eq_oneChartOf]
  exact oneChartOf_compatible hc y₀ hc' y₀'

end OneChartOf

/-! ### The fibre `(Y_{0,1})_x` and its norms `|·|₁` read in charts -/

section Fiber

variable (B : StrongBundle PX P)

lemma fiberZero_mem_oneSet (x : X) : fiberZero P x ∈ B.oneSet := by
  obtain ⟨c, hc, hx⟩ := exists_chart_mem B x
  have hsrc : fiberZero P x ∈ c.toPartialEquiv.source :=
    c.mem_source_of_proj (by rw [proj_fiberZero P]; exact hx)
  rw [B.mem_oneSet_iff hc hsrc, c.snd_fiberZero hx]
  exact ⟨0, map_zero _⟩

/-- **The fibre `(Y_{0,1})_x` over `x`** (the text's "the fibres `Y_x` have the structure of Banach
spaces", for the part of biregularity `(0, 1)`): the points of the fibre `P⁻¹(x)` that lie in
`Y_{0,1}` (fibre component in `F₁` in the strong bundle charts), a linear subspace of `P⁻¹(x)`. -/
def oneFiber (x : X) : Submodule ℝ (P ⁻¹' {x}) where
  carrier := {v | (v : Y) ∈ B.oneSet}
  zero_mem' := B.fiberZero_mem_oneSet x
  add_mem' := by
    intro v w hv hw
    obtain ⟨c, hc, hx⟩ := exists_chart_mem B x
    have hsrc : ∀ u : P ⁻¹' {x}, (u : Y) ∈ c.toPartialEquiv.source := fun u =>
      c.mem_source_of_proj (by rw [show P u = x from u.2]; exact hx)
    obtain ⟨a, ha⟩ := (B.mem_oneSet_iff hc (hsrc v)).1 hv
    obtain ⟨b, hb⟩ := (B.mem_oneSet_iff hc (hsrc w)).1 hw
    change ((v + w : P ⁻¹' {x}) : Y) ∈ B.oneSet
    rw [B.mem_oneSet_iff hc (hsrc _), c.snd_add hx]
    exact ⟨a + b, by rw [map_add, ha, hb]⟩
  smul_mem' := by
    intro t v hv
    obtain ⟨c, hc, hx⟩ := exists_chart_mem B x
    have hsrc : ∀ u : P ⁻¹' {x}, (u : Y) ∈ c.toPartialEquiv.source := fun u =>
      c.mem_source_of_proj (by rw [show P u = x from u.2]; exact hx)
    obtain ⟨a, ha⟩ := (B.mem_oneSet_iff hc (hsrc v)).1 hv
    change ((t • v : P ⁻¹' {x}) : Y) ∈ B.oneSet
    rw [B.mem_oneSet_iff hc (hsrc _), (c.fiber_linear x hx).map_smul]
    exact ⟨t • a, by rw [map_smul, ha]⟩

/-- A point of the fibre `(Y_{0,1})_x` as a point of `Y[1]`. -/
def toOne {x : X} (v : B.oneFiber x) : B.One := B.oneMk ((v : P ⁻¹' {x}) : Y) v.2

/-- A point of `Y[1]` as a point of its fibre `(Y_{0,1})_{P(w)}`. -/
def ofOne (w : B.One) : B.oneFiber (P (B.oneVal w)) := ⟨⟨B.oneVal w, rfl⟩, B.oneVal_mem w⟩

lemma toOne_ofOne (w : B.One) : B.toOne (B.ofOne w) = w := rfl

lemma oneVal_toOne {x : X} (v : B.oneFiber x) :
    B.oneVal (B.toOne v) = ((v : P ⁻¹' {x}) : Y) := rfl

lemma proj_oneVal_toOne {x : X} (v : B.oneFiber x) : P (B.oneVal (B.toOne v)) = x :=
  (v : P ⁻¹' {x}).2

/-- The zero `0_x` of the fibre over `x`, as a point of `Y[1]`. -/
def zeroOne (x : X) : B.One := B.toOne (0 : B.oneFiber x)

lemma oneVal_zeroOne (x : X) : B.oneVal (B.zeroOne x) = fiberZero P x := rfl

lemma proj_oneVal_zeroOne (x : X) : P (B.oneVal (B.zeroOne x)) = x := proj_fiberZero P x

variable {B}

section ChartNorm

variable {c : StrongBundleChart PX P}

omit [T2Space Y] [ParacompactSpace Y] in
lemma fst_liftOne {y : Y} (hy : P y ∈ c.φ.source) : (c.liftOne y).1 = c.φ (P y) :=
  c.fst_apply hy

lemma toBase_liftOne_snd (hc : B.IsChart c) {y : Y} (hy : y ∈ c.toPartialEquiv.source)
    (h1 : y ∈ B.oneSet) : c.F.toBase 1 (c.liftOne y).2 = (c y).2 :=
  Function.invFun_eq ((mem_oneSet_iff_of_isChart hc hy).1 h1)

omit [T2Space Y] [ParacompactSpace Y] in
/-- `Φ[1](0_x) = (φ(x), 0)`. -/
lemma liftOne_fiberZero {x : X} (hx : x ∈ c.φ.source) :
    c.liftOne (fiberZero P x) = (c.φ x, 0) := by
  refine Prod.ext ?_ ?_
  · rw [fst_liftOne (by rw [proj_fiberZero P]; exact hx), proj_fiberZero P]
  · change Function.invFun (c.F.toBase 1) (c (fiberZero P x)).2 = 0
    rw [c.snd_fiberZero hx]
    have := Function.leftInverse_invFun (c.F.toBase_injective 1) (0 : c.F 1)
    rwa [map_zero] at this

omit [T2Space Y] [ParacompactSpace Y] in
lemma mem_source_of_mem_fiber {x : X} (hx : x ∈ c.φ.source) (v : P ⁻¹' {x}) :
    (v : Y) ∈ c.toPartialEquiv.source :=
  c.mem_source_of_proj (by rw [show P v = x from v.2]; exact hx)

/-- **The norm `|·|₁` of the fibre `(Y_{0,1})_x` read in a strong bundle chart**: the fibre
component of `Φ[1]`, a linear map `(Y_{0,1})_x → F₁` (`Φ` is linear on the fibres). -/
def liftOneFiber (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source) : B.oneFiber x →ₗ[ℝ] c.F 1 where
  toFun v := (c.liftOne ((v : P ⁻¹' {x}) : Y)).2
  map_add' v w := by
    apply c.F.toBase_injective 1
    have hs := mem_source_of_mem_fiber hx
    rw [map_add, toBase_liftOne_snd hc (hs _) (v + w).2, toBase_liftOne_snd hc (hs _) v.2,
      toBase_liftOne_snd hc (hs _) w.2]
    exact c.snd_add hx v w
  map_smul' t v := by
    apply c.F.toBase_injective 1
    have hs := mem_source_of_mem_fiber hx
    rw [RingHom.id_apply, map_smul, toBase_liftOne_snd hc (hs _) (t • v).2,
      toBase_liftOne_snd hc (hs _) v.2]
    exact (c.fiber_linear x hx).map_smul t v

lemma liftOneFiber_apply (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source) (v : B.oneFiber x) :
    liftOneFiber hc hx v = (c.liftOne ((v : P ⁻¹' {x}) : Y)).2 := rfl

lemma liftOneFiber_ofOne (hc : B.IsChart c) (w : B.One) (hw : P (B.oneVal w) ∈ c.φ.source) :
    liftOneFiber hc hw (B.ofOne w) = (c.liftOne (B.oneVal w)).2 := rfl

lemma liftOneFiber_injective (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source) :
    Injective (liftOneFiber hc hx) := by
  intro v w hvw
  have hs := mem_source_of_mem_fiber hx
  have h2 : (c ((v : P ⁻¹' {x}) : Y)).2 = (c ((w : P ⁻¹' {x}) : Y)).2 := by
    rw [← toBase_liftOne_snd hc (hs _) v.2, ← toBase_liftOne_snd hc (hs _) w.2]
    exact congrArg (c.F.toBase 1) hvw
  have h1 : (c ((v : P ⁻¹' {x}) : Y)).1 = (c ((w : P ⁻¹' {x}) : Y)).1 := by
    rw [c.covers _ (hs _), c.covers _ (hs _),
      show P ((v : P ⁻¹' {x}) : Y) = x from (v : P ⁻¹' {x}).2,
      show P ((w : P ⁻¹' {x}) : Y) = x from (w : P ⁻¹' {x}).2]
  exact Subtype.ext (Subtype.ext (c.toPartialEquiv.injOn (hs _) (hs _) (Prod.ext h1 h2)))

lemma liftOneFiber_eq_zero_iff (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source)
    {v : B.oneFiber x} : liftOneFiber hc hx v = 0 ↔ v = 0 := by
  constructor
  · intro h
    exact liftOneFiber_injective hc hx (h.trans (map_zero _).symm)
  · rintro rfl; exact map_zero _

/-- The values of `|·|₁` in a chart: the fibre `(Y_{0,1})_x` is mapped onto the slice
`{h ∈ F₁ | (φ(x), h) ∈ K[1]}`. -/
lemma mem_range_liftOneFiber (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source) {h : c.F 1}
    (hh : (c.φ x, h) ∈ strongShiftOne c.K) : ∃ v, liftOneFiber hc hx v = h := by
  have hz' : (c.φ x, c.F.toBase 1 h) ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hh
  set y := c.toPartialEquiv.symm (c.φ x, c.F.toBase 1 h) with hydef
  have hys : y ∈ c.toPartialEquiv.source := c.toPartialEquiv.map_target hz'
  have hcy : c y = (c.φ x, c.F.toBase 1 h) := c.toPartialEquiv.right_inv hz'
  have hPy : P y = x := by
    have hPys : P y ∈ c.φ.source := by rw [c.source_eq] at hys; exact hys
    have h1 := c.covers y hys
    rw [hcy] at h1
    exact c.φ.toPartialEquiv.injOn hPys hx h1.symm
  have hy1 : y ∈ B.oneSet := (mem_oneSet_iff_of_isChart hc hys).2 (by rw [hcy]; exact ⟨h, rfl⟩)
  refine ⟨⟨⟨y, hPy⟩, hy1⟩, ?_⟩
  rw [liftOneFiber_apply]
  change Function.invFun (c.F.toBase 1) (c y).2 = h
  rw [hcy]
  exact Function.leftInverse_invFun (c.F.toBase_injective 1) h

lemma liftOneFiber_mem (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source) (v : B.oneFiber x) :
    (c.φ x, liftOneFiber hc hx v) ∈ strongShiftOne c.K := by
  have hs := mem_source_of_mem_fiber hx
  have := c.liftOne_mem (hs v) ((mem_oneSet_iff_of_isChart hc (hs v)).1 v.2)
  have h1 : c.liftOne ((v : P ⁻¹' {x}) : Y) = (c.φ x, liftOneFiber hc hx v) := by
    refine Prod.ext ?_ rfl
    rw [fst_liftOne (by rw [show P ((v : P ⁻¹' {x}) : Y) = x from (v : P ⁻¹' {x}).2]; exact hx),
      show P ((v : P ⁻¹' {x}) : Y) = x from (v : P ⁻¹' {x}).2]
  rwa [h1] at this

omit [T2Space Y] [ParacompactSpace Y] in
/-- The slice `{h ∈ F₁ | (u, h) ∈ K[1]}` over `u ∈ O` is closed in `F₁` (it is the fixed point set
of the continuous map `h ↦ R[1](u, h)`). -/
lemma isClosed_slice {u : c.φ.model.E 0} (hu : u ∈ c.φ.model.O) :
    IsClosed {h : c.F 1 | (u, h) ∈ strongShiftOne c.K} := by
  set R1 := c.isRetraction.toScRetractionOne c.relOpen
  have hret : R1.retract = strongShiftOne c.K := c.isRetraction.toScRetractionOne_retract c.relOpen
  have huU : u ∈ c.U := by
    rw [← c.base_retract] at hu
    exact (c.isRetraction.baseRetraction c.relOpen).retract_subset hu
  have hmaps : ∀ h : c.F 1, ((u, h) : (c.φ.model.E.prod c.F.shift) 0) ∈ R1.U :=
    fun h => ⟨huU, mem_univ _⟩
  have hcont : Continuous fun h : c.F 1 => R1 ((u, h) : (c.φ.model.E.prod c.F.shift) 0) :=
    R1.isSc1.isSc0.continuousOn_base.comp_continuous (continuous_const.prodMk continuous_id)
      hmaps
  have heq : {h : c.F 1 | (u, h) ∈ strongShiftOne c.K} =
      {h : c.F 1 | R1 ((u, h) : (c.φ.model.E.prod c.F.shift) 0) = (u, h)} := by
    ext h
    change (u, h) ∈ strongShiftOne c.K ↔ R1 ((u, h) : (c.φ.model.E.prod c.F.shift) 0) = (u, h)
    rw [← hret, R1.mem_retract_iff]
    exact ⟨fun h' => h'.2, fun h' => ⟨hmaps h, h'⟩⟩
  rw [heq]
  exact isClosed_eq hcont (continuous_const.prodMk continuous_id)

/-- **The fibre `(Y_{0,1})_x` is complete for the norm `|·|₁` of a chart**: a Cauchy sequence for
`|Φ[1](·)|₁` converges. -/
theorem complete_liftOneFiber (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source)
    (u : ℕ → B.oneFiber x)
    (hu : ∀ ε > 0, ∃ n, ∀ m ≥ n, ∀ k ≥ n, ‖liftOneFiber hc hx (u m - u k)‖ < ε) :
    ∃ v, Tendsto (fun k => ‖liftOneFiber hc hx (u k - v)‖) atTop (𝓝 0) := by
  set L := liftOneFiber hc hx
  have hcs : CauchySeq fun k => L (u k) := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨n, hn⟩ := hu ε hε
    exact ⟨n, fun m hm k hk => by rw [dist_eq_norm, ← map_sub]; exact hn m hm k hk⟩
  obtain ⟨h, hh⟩ := cauchySeq_tendsto_of_complete hcs
  have hmem : (c.φ x, h) ∈ strongShiftOne c.K :=
    (isClosed_slice (c.φ.mapsTo_model x hx)).mem_of_tendsto hh
      (Eventually.of_forall fun k => liftOneFiber_mem hc hx (u k))
  obtain ⟨v, hv⟩ := mem_range_liftOneFiber hc hx hmem
  refine ⟨v, ?_⟩
  have := (tendsto_iff_norm_sub_tendsto_zero.1 hh)
  refine this.congr fun k => ?_
  rw [map_sub, hv]

end ChartNorm

end Fiber

/-! ### Definition 5.1: auxiliary norms -/

section Def51

variable (B : StrongBundle PX P)

/-- **Definition 5.1 (1)** at one point: the restriction of `N : Y_{0,1} → ℝ` to the fibre
`(Y_{0,1})_x` is a norm, and the fibre with this norm is complete (Cauchy sequences converge). -/
structure IsCompleteFiberNorm (N : B.One → ℝ) (x : X) : Prop where
  eq_zero : ∀ v : B.oneFiber x, N (B.toOne v) = 0 → v = 0
  smul : ∀ (t : ℝ) (v : B.oneFiber x), N (B.toOne (t • v)) = |t| * N (B.toOne v)
  add_le : ∀ v w : B.oneFiber x, N (B.toOne (v + w)) ≤ N (B.toOne v) + N (B.toOne w)
  complete : ∀ u : ℕ → B.oneFiber x,
    (∀ ε > 0, ∃ n, ∀ m ≥ n, ∀ k ≥ n, N (B.toOne (u m - u k)) < ε) →
      ∃ v, Tendsto (fun k => N (B.toOne (u k - v))) atTop (𝓝 0)

/-- **Definition 5.1**: an **auxiliary norm** for the strong bundle `P : Y → X` is a continuous map
`N : Y_{0,1} → ℝ` (on `Y[1]`, the set `Y_{0,1}` with its topology) such that (1) its restriction
to every fibre `(Y_{0,1})_x` is a complete norm, and (2) if `(w_k)` is a sequence in `Y_{0,1}` with
`P(w_k) → x` in `X` and `N(w_k) → 0`, then `w_k → 0_x` in `Y_{0,1}`. -/
structure IsAuxNorm (N : B.One → ℝ) : Prop where
  continuous : Continuous N
  fiber : ∀ x, B.IsCompleteFiberNorm N x
  tendsto_zeroOne : ∀ (w : ℕ → B.One) (x : X),
    Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 x) →
      Tendsto (fun k => N (w k)) atTop (𝓝 0) → Tendsto w atTop (𝓝 (B.zeroOne x))

variable {B}

lemma IsCompleteFiberNorm.map_zero {N : B.One → ℝ} {x : X} (h : B.IsCompleteFiberNorm N x) :
    N (B.zeroOne x) = 0 := by
  have := h.smul 0 0
  rwa [zero_smul, abs_zero, zero_mul] at this

lemma IsCompleteFiberNorm.nonneg {N : B.One → ℝ} {x : X} (h : B.IsCompleteFiberNorm N x)
    (v : B.oneFiber x) : 0 ≤ N (B.toOne v) := by
  have h1 := h.add_le v (-v)
  have h2 := h.smul (-1) v
  rw [neg_one_smul, abs_neg, abs_one, one_mul] at h2
  rw [add_neg_cancel, h2] at h1
  have h0 : N (B.toOne 0) = 0 := h.map_zero
  linarith

lemma IsAuxNorm.nonneg {N : B.One → ℝ} (hN : B.IsAuxNorm N) (w : B.One) : 0 ≤ N w :=
  (hN.fiber _).nonneg (B.ofOne w)

lemma IsAuxNorm.smul {N : B.One → ℝ} (hN : B.IsAuxNorm N) {y : X} (v : B.oneFiber y) (t : ℝ) :
    N (B.toOne (t • v)) = |t| * N (B.toOne v) :=
  (hN.fiber y).smul t v

/-! ### The local comparison with the norms of the charts (Lemma 5.2) -/

variable {c : StrongBundleChart PX P}

/-- **The upper bound of Lemma 5.2, from continuity at the zero section** (the first half of the
text's proof of "(i) ⇒ (ii)"): if `g : Y_{0,1} → ℝ` is continuous at `0_x` and positively
homogeneous on the fibres near `x`, then `g(w) ≤ C·|h|₁` for `P(w)` near `x`, where `Φ[1](w) =
(p, h)` in a strong bundle chart `Φ` around `x`.  (The text: "`N(y) < 1` for
`|p − q|₀ + |h|₁ < ε` ... we infer `N(w) ≤ (2/ε)·|h|₁`".) -/
theorem exists_le_mul_norm_liftOne (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source)
    {g : B.One → ℝ} (hg : ContinuousAt g (B.zeroOne x)) {W : Set X} (hW : W ∈ 𝓝 x)
    (hhom : ∀ y ∈ W, ∀ (v : B.oneFiber y) (t : ℝ), g (B.toOne (t • v)) = |t| * g (B.toOne v)) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ c.φ.source ∧ ∃ C, 0 < C ∧
      ∀ w : B.One, P (B.oneVal w) ∈ V → g w ≤ C * ‖(c.liftOne (B.oneVal w)).2‖ := by
  set y₀ := B.zeroOne x with hy₀def
  set χ := oneChartOf hc y₀ with hχ
  have hy₀ : y₀ ∈ χ.source :=
    (mem_oneChartOf_source hc y₀).2 (by rw [proj_oneVal_zeroOne B]; exact hx)
  have hχy₀ : χ y₀ = (c.φ x, 0) := liftOne_fiberZero hx
  have hg0 : g y₀ = 0 := by
    have := hhom x (mem_of_mem_nhds hW) 0 0
    rwa [zero_smul, abs_zero, zero_mul] at this
  have hz₀ : χ y₀ ∈ χ.model.O := χ.mapsTo_model y₀ hy₀
  have hcw : ContinuousWithinAt (g ∘ χ.symm) χ.model.O (χ y₀) := by
    have h1 := χ.continuousOn_invFun (χ y₀) hz₀
    refine ContinuousAt.comp_continuousWithinAt ?_ h1
    rw [χ.symm_apply_apply hy₀]; exact hg
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.1 hcw 1 one_pos
  set V : Set X := c.φ.source ∩ c.φ ⁻¹' Metric.ball (c.φ x) δ ∩ interior W with hVdef
  have hVo : IsOpen V :=
    (c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source Metric.isOpen_ball).inter
      isOpen_interior
  refine ⟨V, hVo, ⟨⟨hx, Metric.mem_ball_self hδ⟩, mem_interior_iff_mem_nhds.2 hW⟩,
    fun y hy => hy.1.1, 2 / δ, by positivity, fun w hw => ?_⟩
  set y := P (B.oneVal w) with hydef
  have hyc : y ∈ c.φ.source := hw.1.1
  have hyW : y ∈ W := interior_subset hw.2
  set L := liftOneFiber hc hyc with hL
  set v := B.ofOne w with hv
  have hLv : (c.liftOne (B.oneVal w)).2 = L v := rfl
  rw [hLv]
  rcases (norm_nonneg (L v)).lt_or_eq with hpos | hzero
  · set t := δ / (2 * ‖L v‖) with ht
    have htpos : 0 < t := by positivity
    set w' := B.toOne (t • v) with hw'
    have hw'src : w' ∈ χ.source := (mem_oneChartOf_source hc y₀).2 (by
      rw [hw', proj_oneVal_toOne B]; exact hyc)
    have hχw' : χ w' = (c.φ y, t • L v) := by
      refine Prod.ext ?_ ?_
      · change (c.liftOne (B.oneVal w')).1 = c.φ y
        rw [fst_liftOne (by rw [hw', proj_oneVal_toOne B]; exact hyc), hw', proj_oneVal_toOne B]
      · change L (t • v) = t • L v
        exact map_smul L t v
    have hdist : dist (χ w') (χ y₀) < δ := by
      rw [hχw', hχy₀]
      change dist ((c.φ y, t • L v) : c.φ.model.E 0 × c.F 1)
        ((c.φ x, 0) : c.φ.model.E 0 × c.F 1) < δ
      rw [Prod.dist_eq, dist_zero_right, norm_smul, Real.norm_of_nonneg htpos.le]
      refine max_lt hw.1.2 ?_
      rw [ht, div_mul_eq_mul_div, mul_div_mul_right _ _ hpos.ne']
      linarith
    have h1 := hδg (χ.mapsTo_model w' hw'src) hdist
    simp only [Function.comp_apply, χ.symm_apply_apply hw'src, χ.symm_apply_apply hy₀, hg0,
      Real.dist_eq, sub_zero] at h1
    have h2 : g w' = t * g w := by
      rw [hw', hhom y hyW v t, abs_of_pos htpos]; rfl
    have h3 : t * g w < 1 := by rw [← h2]; exact lt_of_abs_lt h1
    have h4 : g w < 1 / t := by rw [lt_div_iff₀ htpos, mul_comm]; exact h3
    calc g w ≤ 1 / t := h4.le
      _ = 2 / δ * ‖L v‖ := by rw [ht]; field_simp
  · have hv0 : v = 0 := (liftOneFiber_eq_zero_iff hc hyc).1 (norm_eq_zero.1 hzero.symm)
    have : g w = 0 := by
      have h := hhom y hyW 0 0
      rw [zero_smul, abs_zero, zero_mul] at h
      rw [← toOne_ofOne B w, ← hv, hv0]; exact h
    rw [this, ← hzero, mul_zero]

/-- **The lower bound of Lemma 5.2, from condition (2) of Definition 5.1** (the second half of the
text's proof of "(i) ⇒ (ii)", by contradiction with sequences): for an auxiliary norm `N`,
`|h|₁ ≤ A·N(w)` for `P(w)` near `x`. -/
theorem IsAuxNorm.exists_norm_liftOne_le {N : B.One → ℝ} (hN : B.IsAuxNorm N) (hc : B.IsChart c)
    {x : X} (hx : x ∈ c.φ.source) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ c.φ.source ∧ ∃ A, 0 < A ∧
      ∀ w : B.One, P (B.oneVal w) ∈ V → ‖(c.liftOne (B.oneVal w)).2‖ ≤ A * N w := by
  by_contra H
  push Not at H
  set V : ℕ → Set X := fun k => c.φ.source ∩ c.φ ⁻¹' Metric.ball (c.φ x) (1 / ((k : ℝ) + 1))
    with hVdef
  have hVo : ∀ k, IsOpen (V k) := fun k =>
    c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source Metric.isOpen_ball
  have hxV : ∀ k, x ∈ V k := fun k => ⟨hx, Metric.mem_ball_self (by positivity)⟩
  choose w hwV hwlt using fun k : ℕ =>
    H (V k) (hVo k) (hxV k) inter_subset_left ((k : ℝ) + 1) (by positivity)
  -- normalize
  set y : ℕ → X := fun k => P (B.oneVal (w k)) with hy
  have hyc : ∀ k, y k ∈ c.φ.source := fun k => (hwV k).1
  set h : ℕ → ℝ := fun k => ‖(c.liftOne (B.oneVal (w k))).2‖ with hh
  have hNnn : ∀ k, 0 ≤ N (w k) := fun k => hN.nonneg (w k)
  have hhpos : ∀ k, 0 < h k := fun k => by
    have := hwlt k
    have : 0 ≤ ((k : ℝ) + 1) * N (w k) := by have := hNnn k; positivity
    linarith
  set w' : ℕ → B.One := fun k => B.toOne ((h k)⁻¹ • B.ofOne (w k)) with hw'
  have hNw' : ∀ k, N (w' k) = (h k)⁻¹ * N (w k) := fun k => by
    rw [hw', hN.smul, abs_inv, abs_of_pos (hhpos k)]; rfl
  have hNw'lt : ∀ k, N (w' k) < 1 / ((k : ℝ) + 1) := fun k => by
    rw [hNw', inv_mul_eq_div, div_lt_div_iff₀ (hhpos k) (by positivity), one_mul, mul_comm]
    exact hwlt k
  have hnorm1 : ∀ k, ‖(c.liftOne (B.oneVal (w' k))).2‖ = 1 := fun k => by
    change ‖liftOneFiber hc (hyc k) ((h k)⁻¹ • B.ofOne (w k))‖ = 1
    rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hhpos k).le),
      liftOneFiber_ofOne]
    exact inv_mul_cancel₀ (hhpos k).ne'
  -- `P(w'_k) → x`
  have hφy : Tendsto (fun k => c.φ (y k)) atTop (𝓝 (c.φ x)) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun k => (Metric.mem_ball.1 (hwV k).2).le) tendsto_one_div_add_atTop_nhds_zero_nat)
  have hyx : Tendsto y atTop (𝓝 x) := by
    have h1 : ContinuousWithinAt c.φ.symm c.φ.model.O (c.φ x) :=
      c.φ.continuousOn_invFun _ (c.φ.mapsTo_model x hx)
    have h2 := h1.tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hφy, Eventually.of_forall fun k => c.φ.mapsTo_model _ (hyc k)⟩)
    rw [c.φ.symm_apply_apply hx] at h2
    exact h2.congr fun k => c.φ.symm_apply_apply (hyc k)
  have hPw' : ∀ k, P (B.oneVal (w' k)) = y k := fun k => proj_oneVal_toOne B _
  have hN0 : Tendsto (fun k => N (w' k)) atTop (𝓝 0) :=
    squeeze_zero (fun k => hN.nonneg _) (fun k => (hNw'lt k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := hN.tendsto_zeroOne w' x (by simpa only [hPw'] using hyx) hN0
  -- the chart `Φ[1]` is continuous at `0_x`
  set χ := oneChartOf hc (B.zeroOne x) with hχ
  have hy₀ : B.zeroOne x ∈ χ.source :=
    (mem_oneChartOf_source hc _).2 (by rw [proj_oneVal_zeroOne B]; exact hx)
  have hχc : ContinuousAt χ (B.zeroOne x) :=
    χ.continuousOn_toFun.continuousAt (χ.isOpen_source.mem_nhds hy₀)
  have hχy₀ : χ (B.zeroOne x) = (c.φ x, 0) := liftOne_fiberZero hx
  have h3 : Tendsto (fun k => χ (w' k)) atTop (𝓝 (c.φ x, 0)) := by
    have := hχc.tendsto.comp hlim
    rw [hχy₀] at this
    exact this
  have h3' : Tendsto (fun k => ‖(χ (w' k)).2‖) atTop (𝓝 0) := by
    have h := ((continuous_snd.tendsto _).comp h3).norm
    simp only [norm_zero] at h
    exact h
  have h4 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) :=
    h3'.congr fun k => hnorm1 k
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h4)

/-- **Lemma 5.2, "(i) ⇒ (ii)", in every strong bundle chart**: for an auxiliary norm `N` and a
strong bundle chart `Φ` of `P` around `x`, there are a neighbourhood `V ⊆ dom φ` of `x` and
constants `0 < a < A` with `a·N(w) ≤ |h|₁ ≤ A·N(w)` for `w ∈ Y_{0,1}`, `P(w) ∈ V`,
`Φ[1](w) = (p, h)`. -/
theorem IsAuxNorm.exists_bounds {N : B.One → ℝ} (hN : B.IsAuxNorm N) (hc : B.IsChart c) {x : X}
    (hx : x ∈ c.φ.source) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ c.φ.source ∧ ∃ a A : ℝ, 0 < a ∧ a < A ∧
      ∀ w : B.One, P (B.oneVal w) ∈ V →
        a * N w ≤ ‖(c.liftOne (B.oneVal w)).2‖ ∧ ‖(c.liftOne (B.oneVal w)).2‖ ≤ A * N w := by
  obtain ⟨V₁, hV₁o, hxV₁, hV₁c, C, hC, hV₁⟩ := exists_le_mul_norm_liftOne hc hx
    hN.continuous.continuousAt univ_mem fun y _ v t => hN.smul v t
  obtain ⟨V₂, hV₂o, hxV₂, -, A, hA, hV₂⟩ := hN.exists_norm_liftOne_le hc hx
  refine ⟨V₁ ∩ V₂, hV₁o.inter hV₂o, ⟨hxV₁, hxV₂⟩, inter_subset_left.trans hV₁c,
    min (1 / C) (A / 2), A, lt_min (by positivity) (by positivity),
    (min_le_right _ _).trans_lt (by linarith), fun w hw => ⟨?_, hV₂ w hw.2⟩⟩
  have h1 := hV₁ w hw.1
  calc min (1 / C) (A / 2) * N w ≤ 1 / C * N w :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (hN.nonneg w)
    _ ≤ ‖(c.liftOne (B.oneVal w)).2‖ := by
        rw [one_div_mul_eq_div, div_le_iff₀ hC, mul_comm]; exact h1

/-- **Lemma 5.2**: for a continuous `N : Y_{0,1} → ℝ` which is a complete norm on every fibre,
`N` is an auxiliary norm if and only if (ii) every `x ∈ X` lies in the domain of a strong bundle
chart `Φ` of `P` with a neighbourhood `V` of `x` and constants `0 < a < A` such that
`a·N(w) ≤ |h|₁ ≤ A·N(w)` for all `w ∈ Y_{0,1}` with `P(w) ∈ V`, where `Φ(w) = (p, h)`. -/
theorem _root_.Polyfold.lemma_5_2 {N : B.One → ℝ} (hcont : Continuous N)
    (hfib : ∀ x, B.IsCompleteFiberNorm N x) :
    B.IsAuxNorm N ↔ ∀ x, ∃ c : StrongBundleChart PX P, B.IsChart c ∧
      ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ c.φ.source ∧ ∃ a A : ℝ, 0 < a ∧ a < A ∧
        ∀ w : B.One, P (B.oneVal w) ∈ V →
          a * N w ≤ ‖(c.liftOne (B.oneVal w)).2‖ ∧ ‖(c.liftOne (B.oneVal w)).2‖ ≤ A * N w := by
  constructor
  · intro hN x
    obtain ⟨c, hc, hx⟩ := exists_chart_mem B x
    exact ⟨c, B.isChart_of_mem hc, hN.exists_bounds (B.isChart_of_mem hc) hx⟩
  · intro H
    refine ⟨hcont, hfib, fun w x hP hN0 => ?_⟩
    obtain ⟨c, hc, V, hVo, hxV, hVc, a, A, ha, haA, hV⟩ := H x
    have hx : x ∈ c.φ.source := hVc hxV
    set χ := oneChartOf hc (B.zeroOne x) with hχ
    have hy₀ : B.zeroOne x ∈ χ.source :=
      (mem_oneChartOf_source hc _).2 (by rw [proj_oneVal_zeroOne B]; exact hx)
    have hχy₀ : χ (B.zeroOne x) = (c.φ x, 0) := liftOne_fiberZero hx
    have hev : ∀ᶠ k in atTop, P (B.oneVal (w k)) ∈ V := hP.eventually (hVo.mem_nhds hxV)
    have hsrc : ∀ᶠ k in atTop, w k ∈ χ.source :=
      hev.mono fun k hk => (mem_oneChartOf_source hc _).2 (hVc hk)
    -- `Φ[1](w_k) → (φ(x), 0)`
    have h1 : Tendsto (fun k => (χ (w k)).1) atTop (𝓝 (c.φ x)) := by
      have hφ : ContinuousAt c.φ x :=
        c.φ.continuousOn_toFun.continuousAt (c.φ.isOpen_source.mem_nhds hx)
      refine (hφ.tendsto.comp hP).congr' (hev.mono fun k hk => ?_)
      exact (fst_liftOne (hVc hk)).symm
    have h2 : Tendsto (fun k => (χ (w k)).2) atTop (𝓝 0) := by
      have hA : Tendsto (fun k => A * N (w k)) atTop (𝓝 0) := by
        simpa only [mul_zero] using hN0.const_mul A
      exact squeeze_zero_norm' (hev.mono fun k hk => (hV (w k) hk).2) hA
    have h3 : Tendsto (fun k => χ (w k)) atTop (𝓝 (χ (B.zeroOne x))) := by
      rw [hχy₀]; exact h1.prodMk_nhds h2
    have h4 := (χ.continuousOn_invFun _ (χ.mapsTo_model _ hy₀)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨h3, hsrc.mono fun k hk => χ.mapsTo_model _ hk⟩)
    rw [χ.toPartialEquiv.left_inv hy₀] at h4
    exact h4.congr' (hsrc.mono fun k hk => χ.toPartialEquiv.left_inv hk)

end Def51

/-! ### Proposition 5.3 -/

section Prop53

variable {B : StrongBundle PX P}

/-- **The norms `|·|₁` of two strong bundle charts around `x` are locally comparable**: Lemma 5.2's
upper bound (continuity at the zero section and homogeneity) for `g = |Φ₁[1](·)|₁`. -/
theorem exists_norm_liftOne_le_mul {c₁ c₂ : StrongBundleChart PX P} (hc₁ : B.IsChart c₁)
    (hc₂ : B.IsChart c₂) {x : X} (hx₁ : x ∈ c₁.φ.source) (hx₂ : x ∈ c₂.φ.source) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ c₂.φ.source ∧ ∃ C, 0 < C ∧ ∀ w : B.One, P (B.oneVal w) ∈ V →
      ‖(c₁.liftOne (B.oneVal w)).2‖ ≤ C * ‖(c₂.liftOne (B.oneVal w)).2‖ := by
  refine exists_le_mul_norm_liftOne hc₂ hx₂ (g := fun w => ‖(c₁.liftOne (B.oneVal w)).2‖) ?_
    (c₁.φ.isOpen_source.mem_nhds hx₁) ?_
  · set χ := oneChartOf hc₁ (B.zeroOne x)
    have hy₀ : B.zeroOne x ∈ χ.source :=
      (mem_oneChartOf_source hc₁ _).2 (by rw [proj_oneVal_zeroOne B]; exact hx₁)
    exact (χ.continuousOn_toFun.continuousAt (χ.isOpen_source.mem_nhds hy₀)).snd.norm
  · intro y hy v t
    change ‖liftOneFiber hc₁ hy (t • v)‖ = |t| * ‖liftOneFiber hc₁ hy v‖
    rw [map_smul, norm_smul, Real.norm_eq_abs]

/-- The norms `|·|₁` of finitely many strong bundle charts around `x` and of one more chart `c'`
are comparable near `x`, with one constant. -/
theorem exists_uniform_comparison {ι : Type*} {c : ι → StrongBundleChart PX P}
    (hc : ∀ i, B.IsChart (c i)) {c' : StrongBundleChart PX P} (hc' : B.IsChart c') {x : X}
    (hx' : x ∈ c'.φ.source) (is : Finset ι) (hx : ∀ i ∈ is, x ∈ (c i).φ.source) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ c'.φ.source ∧ ∃ C, 0 < C ∧ ∀ i ∈ is, ∀ w : B.One,
      P (B.oneVal w) ∈ V →
        ‖((c i).liftOne (B.oneVal w)).2‖ ≤ C * ‖(c'.liftOne (B.oneVal w)).2‖ ∧
        ‖(c'.liftOne (B.oneVal w)).2‖ ≤ C * ‖((c i).liftOne (B.oneVal w)).2‖ := by
  classical
  induction is using Finset.induction_on with
  | empty =>
    exact ⟨c'.φ.source, c'.φ.isOpen_source, hx', subset_rfl, 1, one_pos,
      fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert j is hj ih =>
    obtain ⟨V, hVo, hxV, hVc, C, hC, hV⟩ := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hxj := hx j (Finset.mem_insert_self j is)
    obtain ⟨V₁, hV₁o, hxV₁, -, C₁, hC₁, hV₁⟩ := exists_norm_liftOne_le_mul (hc j) hc' hxj hx'
    obtain ⟨V₂, hV₂o, hxV₂, -, C₂, hC₂, hV₂⟩ := exists_norm_liftOne_le_mul hc' (hc j) hx' hxj
    set D := max C (max C₁ C₂) with hD
    have hCD : C ≤ D := le_max_left _ _
    have hC₁D : C₁ ≤ D := (le_max_left _ _).trans (le_max_right _ _)
    have hC₂D : C₂ ≤ D := (le_max_right _ _).trans (le_max_right _ _)
    refine ⟨V ∩ V₁ ∩ V₂, (hVo.inter hV₁o).inter hV₂o, ⟨⟨hxV, hxV₁⟩, hxV₂⟩,
      inter_subset_left.trans (inter_subset_left.trans hVc), D, hC.trans_le hCD,
      fun i hi w hw => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨(hV₁ w hw.1.2).trans (mul_le_mul_of_nonneg_right hC₁D (norm_nonneg _)),
        (hV₂ w hw.2).trans (mul_le_mul_of_nonneg_right hC₂D (norm_nonneg _))⟩
    · obtain ⟨h1, h2⟩ := hV i hi w hw.1.1
      exact ⟨h1.trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg _)),
        h2.trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg _))⟩

/-- A function on `Y_{0,1}` squeezed between multiples of the norm `|·|₁` of a chart on the fibre
over `x` makes that fibre complete. -/
theorem complete_of_bounds {g : B.One → ℝ} {c : StrongBundleChart PX P} (hc : B.IsChart c)
    {x : X} (hx : x ∈ c.φ.source) {a A : ℝ} (ha : 0 < a)
    (hlow : ∀ v : B.oneFiber x, a * ‖liftOneFiber hc hx v‖ ≤ g (B.toOne v))
    (hup : ∀ v : B.oneFiber x, g (B.toOne v) ≤ A * ‖liftOneFiber hc hx v‖)
    (u : ℕ → B.oneFiber x)
    (hu : ∀ ε > 0, ∃ n, ∀ m ≥ n, ∀ k ≥ n, g (B.toOne (u m - u k)) < ε) :
    ∃ v, Tendsto (fun k => g (B.toOne (u k - v))) atTop (𝓝 0) := by
  have hcs : ∀ ε > 0, ∃ n, ∀ m ≥ n, ∀ k ≥ n, ‖liftOneFiber hc hx (u m - u k)‖ < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := hu (a * ε) (by positivity)
    refine ⟨n, fun m hm k hk => ?_⟩
    have := (hlow (u m - u k)).trans_lt (hn m hm k hk)
    exact lt_of_mul_lt_mul_left this ha.le
  obtain ⟨v, hv⟩ := complete_liftOneFiber hc hx u hcs
  refine ⟨v, squeeze_zero (fun k => ?_) (fun k => hup (u k - v)) ?_⟩
  · exact (mul_nonneg ha.le (norm_nonneg _)).trans (hlow _)
  · simpa only [mul_zero] using hv.const_mul A

variable {ι : Type*} {c : ι → StrongBundleChart PX P} {ρ : PartitionOfUnity ι X univ}

variable (B) in
/-- **The glued norm of the proof of Proposition 5.3**: `N(w) = Σᵢ ρᵢ(P(w))·|Φᵢ[1](w)|₁` for a
family of strong bundle charts `Φᵢ` and a partition of unity `(ρᵢ)` subordinate to their domains
(the text: "a partition of unity argument ... pulling back by strong bundle maps the standard norm
`|·|₁` to the fibers"). -/
def gluedNorm (c : ι → StrongBundleChart PX P) (ρ : PartitionOfUnity ι X univ) (w : B.One) : ℝ :=
  ∑ᶠ i, ρ i (P (B.oneVal w)) * ‖((c i).liftOne (B.oneVal w)).2‖

omit [T2Space X] [ParacompactSpace X] in
lemma sum_partition_eq_one {is : Finset ι} {z : X} (hz : (support fun i => ρ i z) ⊆ is) :
    ∑ i ∈ is, ρ i z = 1 := by
  rw [← finsum_eq_sum_of_support_subset _ hz]; exact ρ.sum_eq_one (mem_univ z)

lemma gluedNorm_eq_sum {is : Finset ι} {w : B.One}
    (hz : (support fun i => ρ i (P (B.oneVal w))) ⊆ is) :
    gluedNorm B c ρ w =
      ∑ i ∈ is, ρ i (P (B.oneVal w)) * ‖((c i).liftOne (B.oneVal w)).2‖ :=
  finsum_eq_sum_of_support_subset _ ((support_mul_subset_left _ _).trans hz)

lemma gluedNorm_nonneg (w : B.One) : 0 ≤ gluedNorm B c ρ w :=
  finsum_nonneg fun i => mul_nonneg (ρ.nonneg i _) (norm_nonneg _)

/-- The glued norm is continuous on `Y[1]`: a locally finite sum of continuous functions
(`ρᵢ ∘ P` has closed support inside the domain of `Φᵢ[1]`). -/
theorem continuous_gluedNorm (hc : ∀ i, B.IsChart (c i))
    (hρ : ρ.IsSubordinate fun i => (c i).φ.source) : Continuous (gluedNorm B c ρ) := by
  have hPc : Continuous fun w : B.One => P (B.oneVal w) := B.continuous.comp B.continuous_oneVal
  apply continuous_finsum
  · intro i
    set S := {w : B.One | P (B.oneVal w) ∈ (c i).φ.source} with hS
    have hSo : IsOpen S := (c i).φ.isOpen_source.preimage hPc
    have hcont : ContinuousOn
        (fun w : B.One => ρ i (P (B.oneVal w)) * ‖((c i).liftOne (B.oneVal w)).2‖) S := by
      refine ((ρ i).continuous.comp hPc).continuousOn.mul ?_
      intro w hw
      have h1 := (oneChartOf (hc i) w).continuousOn_toFun w ((mem_oneChartOf_source _ _).2 hw)
      exact (h1.snd.norm).mono fun z hz => (mem_oneChartOf_source _ _).2 hz
    refine hcont.continuous_of_tsupport_subset hSo ?_
    refine (tsupport_mul_subset_left).trans ?_
    exact (tsupport_comp_subset_preimage (ρ i) hPc).trans (preimage_mono (hρ i))
  · exact (ρ.locallyFinite.preimage_continuous hPc).subset fun i => support_mul_subset_left _ _

/-- **The glued norm against the norm `|·|₁` of any chart around `x`**, near `x`. -/
theorem gluedNorm_bounds (hc : ∀ i, B.IsChart (c i))
    (hρ : ρ.IsSubordinate fun i => (c i).φ.source) {c' : StrongBundleChart PX P}
    (hc' : B.IsChart c') {x : X} (hx' : x ∈ c'.φ.source) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ c'.φ.source ∧ ∃ C, 0 < C ∧ ∀ w : B.One, P (B.oneVal w) ∈ V →
      gluedNorm B c ρ w ≤ C * ‖(c'.liftOne (B.oneVal w)).2‖ ∧
        ‖(c'.liftOne (B.oneVal w)).2‖ ≤ C * gluedNorm B c ρ w := by
  obtain ⟨is, n, hn, hnsub, hsupp⟩ :=
    ρ.locallyFinite.exists_finset_nhds_support_subset hρ (fun i => (c i).φ.isOpen_source) x
  have hxis : ∀ i ∈ is, x ∈ (c i).φ.source := fun i hi =>
    mem_iInter₂.1 (hnsub (mem_of_mem_nhds hn)) i hi
  obtain ⟨V, hVo, hxV, hVc, C, hC, hV⟩ := exists_uniform_comparison hc hc' hx' is hxis
  refine ⟨V ∩ interior n, hVo.inter isOpen_interior, ⟨hxV, mem_interior_iff_mem_nhds.2 hn⟩,
    inter_subset_left.trans hVc, C, hC, fun w hw => ?_⟩
  have hzn : P (B.oneVal w) ∈ n := interior_subset hw.2
  rw [gluedNorm_eq_sum (hsupp _ hzn)]
  have h1 := sum_partition_eq_one (ρ := ρ) (hsupp _ hzn)
  constructor
  · calc ∑ i ∈ is, ρ i (P (B.oneVal w)) * ‖((c i).liftOne (B.oneVal w)).2‖
        ≤ ∑ i ∈ is, ρ i (P (B.oneVal w)) * (C * ‖(c'.liftOne (B.oneVal w)).2‖) :=
          Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hV i hi w hw.1).1 (ρ.nonneg i _)
      _ = C * ‖(c'.liftOne (B.oneVal w)).2‖ := by rw [← Finset.sum_mul, h1, one_mul]
  · calc ‖(c'.liftOne (B.oneVal w)).2‖
        = ∑ i ∈ is, ρ i (P (B.oneVal w)) * ‖(c'.liftOne (B.oneVal w)).2‖ := by
          rw [← Finset.sum_mul, h1, one_mul]
      _ ≤ ∑ i ∈ is, ρ i (P (B.oneVal w)) * (C * ‖((c i).liftOne (B.oneVal w)).2‖) :=
          Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hV i hi w hw.1).2 (ρ.nonneg i _)
      _ = C * ∑ i ∈ is, ρ i (P (B.oneVal w)) * ‖((c i).liftOne (B.oneVal w)).2‖ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

/-- **The glued norm is a complete norm on every fibre** (Definition 5.1 (1)). -/
theorem isCompleteFiberNorm_gluedNorm (hc : ∀ i, B.IsChart (c i))
    (hρ : ρ.IsSubordinate fun i => (c i).φ.source) (x : X) :
    B.IsCompleteFiberNorm (gluedNorm B c ρ) x := by
  obtain ⟨is, n, hn, hnsub, hsupp⟩ :=
    ρ.locallyFinite.exists_finset_nhds_support_subset hρ (fun i => (c i).φ.isOpen_source) x
  have hxis : ∀ i ∈ is, x ∈ (c i).φ.source := fun i hi =>
    mem_iInter₂.1 (hnsub (mem_of_mem_nhds hn)) i hi
  have hxn : x ∈ n := mem_of_mem_nhds hn
  have hsum : ∀ v : B.oneFiber x, gluedNorm B c ρ (B.toOne v) =
      ∑ i ∈ is, ρ i x * ‖((c i).liftOne (B.oneVal (B.toOne v))).2‖ := fun v => by
    have h := gluedNorm_eq_sum (c := c) (ρ := ρ) (w := B.toOne v)
      (by rw [proj_oneVal_toOne B]; exact hsupp x hxn)
    rwa [proj_oneVal_toOne B] at h
  have h1 := sum_partition_eq_one (ρ := ρ) (hsupp x hxn)
  -- the chart terms are fibrewise linear
  have hsm : ∀ i ∈ is, ∀ (t : ℝ) (v : B.oneFiber x),
      ‖((c i).liftOne (B.oneVal (B.toOne (t • v)))).2‖ =
        |t| * ‖((c i).liftOne (B.oneVal (B.toOne v))).2‖ := fun i hi t v => by
    change ‖liftOneFiber (hc i) (hxis i hi) (t • v)‖ = |t| * ‖liftOneFiber (hc i) (hxis i hi) v‖
    rw [map_smul, norm_smul, Real.norm_eq_abs]
  have had : ∀ i ∈ is, ∀ v w : B.oneFiber x,
      ‖((c i).liftOne (B.oneVal (B.toOne (v + w)))).2‖ ≤
        ‖((c i).liftOne (B.oneVal (B.toOne v))).2‖ +
          ‖((c i).liftOne (B.oneVal (B.toOne w))).2‖ := fun i hi v w => by
    change ‖liftOneFiber (hc i) (hxis i hi) (v + w)‖ ≤
      ‖liftOneFiber (hc i) (hxis i hi) v‖ + ‖liftOneFiber (hc i) (hxis i hi) w‖
    rw [map_add]; exact norm_add_le _ _
  -- the comparison with an atlas chart around `x`
  obtain ⟨c', hc'm, hx'⟩ := exists_chart_mem B x
  have hc' := B.isChart_of_mem hc'm
  obtain ⟨V, -, hxV, -, C, hC, hV⟩ := gluedNorm_bounds hc hρ hc' hx'
  have hb : ∀ v : B.oneFiber x, gluedNorm B c ρ (B.toOne v) ≤ C * ‖liftOneFiber hc' hx' v‖ ∧
      ‖liftOneFiber hc' hx' v‖ ≤ C * gluedNorm B c ρ (B.toOne v) := fun v =>
    hV (B.toOne v) (by rw [proj_oneVal_toOne B]; exact hxV)
  refine ⟨fun v hv => ?_, fun t v => ?_, fun v w => ?_, ?_⟩
  · have h0 := (hb v).2
    rw [hv, mul_zero] at h0
    exact (liftOneFiber_eq_zero_iff hc' hx').1 (norm_le_zero_iff.1 h0)
  · rw [hsum, hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by rw [hsm i hi]; ring
  · rw [hsum, hsum, hsum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i hi => by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (had i hi v w) (ρ.nonneg i x)
  · refine complete_of_bounds hc' hx' (a := 1 / C) (A := C) (by positivity) (fun v => ?_)
      (fun v => (hb v).1)
    rw [one_div_mul_eq_div, div_le_iff₀ hC, mul_comm]; exact (hb v).2

/-- **Proposition 5.3, existence**: every strong bundle `P : Y → X` admits an auxiliary norm
(the glued norm `Σᵢ ρᵢ(P(w))·|Φᵢ[1](w)|₁` over the charts of the atlas, for a partition of unity
of the paracompact Hausdorff space `X` subordinate to their domains; Definition 5.1 through
Lemma 5.2). -/
theorem _root_.Polyfold.proposition_5_3_exists : ∃ N : B.One → ℝ, B.IsAuxNorm N := by
  set c : B.atlas.charts → StrongBundleChart PX P := fun i => i.1 with hcdef
  have hc : ∀ i, B.IsChart (c i) := fun i => B.isChart_of_mem i.2
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i => (c i).φ.source) (fun i => (c i).φ.isOpen_source) fun x _ => by
      obtain ⟨c₀, hc₀, hx⟩ := exists_chart_mem B x
      exact mem_iUnion.2 ⟨⟨c₀, hc₀⟩, hx⟩
  refine ⟨gluedNorm B c ρ, (lemma_5_2 (continuous_gluedNorm hc hρ)
    (isCompleteFiberNorm_gluedNorm hc hρ)).2 fun x => ?_⟩
  obtain ⟨c', hc'm, hx'⟩ := exists_chart_mem B x
  have hc' := B.isChart_of_mem hc'm
  obtain ⟨V, hVo, hxV, hVc, C, hC, hV⟩ := gluedNorm_bounds hc hρ hc' hx'
  refine ⟨c', hc', V, hVo, hxV, hVc, 1 / C, C + 1 / C, by positivity,
    by linarith [one_div_pos.2 hC], fun w hw => ⟨?_, ?_⟩⟩
  · rw [one_div_mul_eq_div, div_le_iff₀ hC, mul_comm]; exact (hV w hw).1
  · exact (hV w hw).2.trans (mul_le_mul_of_nonneg_right (by linarith [one_div_pos.2 hC])
      (gluedNorm_nonneg w))

/-- **Proposition 5.3, comparison**: for two auxiliary norms `N₀`, `N₁` there is a continuous
`f : X → (0, ∞)` with `f(x)·N₀(w) ≤ N₁(w) ≤ (1/f(x))·N₀(w)` for all `w ∈ P⁻¹(x) ∩ Y_{0,1}` ("the
local compatibility implies the existence of `f`": Lemma 5.2 in one chart around each point gives
local constants, glued by a partition of unity). -/
theorem _root_.Polyfold.proposition_5_3_compare {N₀ N₁ : B.One → ℝ} (h₀ : B.IsAuxNorm N₀)
    (h₁ : B.IsAuxNorm N₁) :
    ∃ f : X → ℝ, Continuous f ∧ (∀ x, 0 < f x) ∧ ∀ w : B.One,
      f (P (B.oneVal w)) * N₀ w ≤ N₁ w ∧ N₁ w ≤ (f (P (B.oneVal w)))⁻¹ * N₀ w := by
  set t : X → Set ℝ := fun y => {r | 0 < r ∧ ∀ w : B.One, P (B.oneVal w) = y →
    r * N₀ w ≤ N₁ w ∧ r * N₁ w ≤ N₀ w} with htdef
  have hconv : ∀ y, Convex ℝ (t y) := by
    intro y r hr s hs a b ha hb hab
    have hm : 0 < min r s := lt_min hr.1 hs.1
    refine ⟨?_, fun w hw => ⟨?_, ?_⟩⟩
    · have h1 : a * min r s ≤ a * r := mul_le_mul_of_nonneg_left (min_le_left _ _) ha
      have h2 : b * min r s ≤ b * s := mul_le_mul_of_nonneg_left (min_le_right _ _) hb
      have h3 : (a + b) * min r s = min r s := by rw [hab, one_mul]
      simp only [smul_eq_mul]
      nlinarith
    · have h1 := mul_le_mul_of_nonneg_left (hr.2 w hw).1 ha
      have h2 := mul_le_mul_of_nonneg_left (hs.2 w hw).1 hb
      simp only [smul_eq_mul]
      calc (a * r + b * s) * N₀ w = a * (r * N₀ w) + b * (s * N₀ w) := by ring
        _ ≤ a * N₁ w + b * N₁ w := add_le_add h1 h2
        _ = N₁ w := by rw [← add_mul, hab, one_mul]
    · have h1 := mul_le_mul_of_nonneg_left (hr.2 w hw).2 ha
      have h2 := mul_le_mul_of_nonneg_left (hs.2 w hw).2 hb
      simp only [smul_eq_mul]
      calc (a * r + b * s) * N₁ w = a * (r * N₁ w) + b * (s * N₁ w) := by ring
        _ ≤ a * N₀ w + b * N₀ w := add_le_add h1 h2
        _ = N₀ w := by rw [← add_mul, hab, one_mul]
  have hloc : ∀ y : X, ∃ r : ℝ, ∀ᶠ z in 𝓝 y, r ∈ t z := by
    intro y
    obtain ⟨c, hcm, hy⟩ := exists_chart_mem B y
    have hc := B.isChart_of_mem hcm
    obtain ⟨V₀, hV₀o, hyV₀, -, a₀, A₀, ha₀, haA₀, hV₀⟩ := h₀.exists_bounds hc hy
    obtain ⟨V₁, hV₁o, hyV₁, -, a₁, A₁, ha₁, haA₁, hV₁⟩ := h₁.exists_bounds hc hy
    have hA₀ : 0 < A₀ := ha₀.trans haA₀
    have hA₁ : 0 < A₁ := ha₁.trans haA₁
    refine ⟨min (a₁ / A₀) (a₀ / A₁), ?_⟩
    filter_upwards [(hV₀o.inter hV₁o).mem_nhds ⟨hyV₀, hyV₁⟩] with z hz
    refine ⟨lt_min (by positivity) (by positivity), fun w hw => ?_⟩
    rw [← hw] at hz
    obtain ⟨h0a, h0b⟩ := hV₀ w hz.1
    obtain ⟨h1a, h1b⟩ := hV₁ w hz.2
    have hN₀ := h₀.nonneg w
    have hN₁ := h₁.nonneg w
    constructor
    · calc min (a₁ / A₀) (a₀ / A₁) * N₀ w ≤ a₀ / A₁ * N₀ w :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hN₀
        _ ≤ N₁ w := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hA₁]; linarith
    · calc min (a₁ / A₀) (a₀ / A₁) * N₁ w ≤ a₁ / A₀ * N₁ w :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hN₁
        _ ≤ N₀ w := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hA₀]; linarith
  obtain ⟨g, hg⟩ := exists_continuous_forall_mem_convex_of_local_const hconv hloc
  refine ⟨g, g.continuous, fun x => (hg x).1, fun w => ⟨((hg _).2 w rfl).1, ?_⟩⟩
  have hpos := (hg (P (B.oneVal w))).1
  rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
  exact ((hg _).2 w rfl).2

end Prop53

end StrongBundle

end Polyfold
