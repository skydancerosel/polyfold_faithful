import Polyfold.Chapter2.SubMPolyfold
import Polyfold.Chapter1.ExpositionLemmas

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.2,
**Theorem 2.16** (with Appendix 2.6.2: Theorem 2.55, Lemma 2.56, Proposition 2.57),
**Proposition 2.19 (3)** (Appendix 2.6.3) and **Proposition 2.21 (3), (4)**.

# Metrizability of `X_m`, `X_∞`, `TX`; tangent spaces of sub-M-polyfolds

## The text, paraphrased

(Theorem 2.16) For an M-polyfold `X` and every `m ≥ 0`, `X_m` is metrizable, in particular
paracompact; `X_∞` is metrizable.  (Appendix) By Smirnov's theorem (Theorem 2.55: a paracompact
Hausdorff locally metrizable space is metrizable), Lemma 2.56 (Michael: a regular space is
paracompact iff every open cover has a closed locally finite refinement) and Proposition 2.57 (a
regular space with a locally finite closed cover by paracompact subspaces is paracompact): `X_m`
is paracompact, hence metrizable.  (Proposition 2.19 (3)) `TX` is metrizable, hence paracompact.
(Proposition 2.21 (3)) For a sub-M-polyfold `A` and a smooth `a ∈ A`, `T_aA` has an sc-complement
in `T_aX`; (4) for an sc-smooth retraction `s : W → W` onto `W ∩ A`, `Ts(a)T_aX = T_aA`.  *Proof*
in coordinates: `t = s ∘ r`, `T_aA = Dt(a)E = Ds(a)T_aO`, and
`T_aO = Ds(a)Dr(a)E ⊕ (I − Ds(a))Dr(a)E`.

## What is formalized

* `Polyfold.metrizableSpace_of_partition`: a space with open metrizable subspaces `V_i` and a
  locally finite family of continuous `ρ_i ≥ 0`, `supp ρ_i ⊆ V_i`, not all vanishing at any point,
  is metrizable.  The metric is `∑ᶠ_i |ρ_i(x) − ρ_i(y)| + min(ρ_i(x), ρ_i(y))·min(d_i(x, y), 1)`
  (a locally finite sum of cone metrics; `cone_triangle`, `truncDist`).
* `Polyfold.metrizableSpace_of_pullback` (the partition of unity of `X`, pulled back along a
  continuous `π : Y → X`) and `Polyfold.metrizableSpace_of_locally` (**Smirnov's theorem**,
  Theorem 2.55); `paracompactSpace_of_metrizableSpace` (Stone, from Mathlib);
  `metrizableSpace_pi_nat` (countable products, from Mathlib).
* `MChart.sourceHomeomorph` (`V ≅ O`), `MChart.metrizableSpace_source`;
  `MPolyfold.isEmbedding_levelLift` (`V_m ≅ O_m ⊆ E_m`, the text's "`φ : V_m → O_m` is a
  homeomorphism", for every `m`).
* `MPolyfold.metrizableSpace` (`X`), `MPolyfold.metrizableSpace_level` (`X_m`), the instance
  `MPolyfold.paracompactSpace_level`, `MPolyfold.SmoothLevel` (`X_∞` with the initial topology
  of the inclusions `X_∞ → X_m`, `smoothLevel_topology_eq`),
  `MPolyfold.metrizableSpace_smoothLevel`, and
  `Polyfold.theorem_2_16` (**Theorem 2.16**).  `MPolyfold.paracompactSpace_subtype`: every subset
  of an M-polyfold, in particular every sub-M-polyfold, is paracompact.
* `MPolyfold.metrizableSpace_tangentSpace`, the instance `MPolyfold.paracompactSpace_tangentSpace`,
  `Polyfold.proposition_2_19_3` (**Proposition 2.19 (3)**).
* `ScRetraction.compRetraction` (`t = s ∘ r`), `Polyfold.proposition_2_21_3`,
  `Polyfold.proposition_2_21_4` (**Proposition 2.21 (3), (4)**, in a chart).

## What the text leaves implicit, and the choices made

* **No hypothesis is added for Theorem 2.16.**  The text's route needs the regularity of `X_m`
  for Proposition 2.57, which it does not prove (true here because `X_m → X` is continuous and `X`
  is regular).  The formal proof avoids Lemma 2.56 and Proposition 2.57: the partition of unity of
  the paracompact Hausdorff space `X` subordinate to a chart cover, pulled back to `X_m` (or to
  `TX`, along `TX → X¹ → X`), already gives a metric (`metrizableSpace_of_pullback`);
  paracompactness follows by Stone's theorem.  Smirnov's theorem is proved in this form (it is
  not in Mathlib).
* The topology of `X_∞` is not defined in the text; it is taken to be the initial topology of the
  inclusions `X_∞ → X_m` (equivalently, induced by `X_∞ → ∏_m X_m`).
* With these instances the hypotheses `[ParacompactSpace (P.Level 1)]` of `MPolyfold.shift` and
  `[ParacompactSpace P.TangentSpace]` of `MPolyfold.tangentPolyfold` are satisfied automatically;
  for a sub-M-polyfold `A`, `MPolyfold.subPolyfold` is applied with
  `haveI := P.paracompactSpace_subtype A`.
* Proposition 2.21 (3), (4) are stated in a chart, as the text proves them: `O = r(U)` is the
  chart image of an open piece of `X`, `A ∩ O = s(O)`, and the tangent spaces are those of the
  retracts `O` and `s(O)` (Definition 2.17).  The text's `Ds(a)` is `D(s ∘ r)(a)`; the
  sc-complement is `(Dr(a) − Dt(a))E` and "sc-complement" is the levelwise direct sum of two
  sc-subspaces of `E` inside `T_aO` (the sc-structure of `T_aO` at the smooth point `a`).  The
  key identities `Dr(a)Dt(a) = Dt(a) = Dt(a)Dr(a)` come from `r ∘ t = t = t ∘ r`.  Transporting
  to `T_aX` by `Tφ(a)` is not done (the fibres of `TX` carry no sc-structure in this project:
  gap G.7 of the report).
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

/-! ### A metrization lemma: locally finite partitions with metrizable carriers -/

section Metrization

variable {Y : Type*} [TopologicalSpace Y] {ι : Type*}

/-- The elementary triangle inequality behind the cone metric `|s − t| + min(s, t)·δ(p, q)`
(`δ ≤ 1`). -/
lemma cone_triangle {a b c dxy dyz dxz : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h0xy : 0 ≤ dxy) (h0yz : 0 ≤ dyz) (h1xz : dxz ≤ 1)
    (htri : 0 < min a c → 0 < b → dxz ≤ dxy + dyz) :
    |a - c| + min a c * dxz ≤ (|a - b| + min a b * dxy) + (|b - c| + min b c * dyz) := by
  have habs : |a - c| ≤ |a - b| + |b - c| := abs_sub_le a b c
  rcases le_or_gt (min a c) b with hmb | hbm
  · rcases eq_or_lt_of_le (le_min ha hc) with hm0 | hmpos
    · rw [← hm0, zero_mul, add_zero]
      nlinarith [mul_nonneg (le_min ha hb) h0xy, mul_nonneg (le_min hb hc) h0yz]
    · have hbpos : 0 < b := lt_of_lt_of_le hmpos hmb
      have ht := htri hmpos hbpos
      have h1 : min a c ≤ min a b := le_min (min_le_left _ _) (le_trans (le_refl _) hmb)
      have h2 : min a c ≤ min b c := le_min hmb (min_le_right _ _)
      have h3 : min a c * dxz ≤ min a c * dxy + min a c * dyz := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left ht (le_min ha hc)
      have h4 : min a c * dxy ≤ min a b * dxy := mul_le_mul_of_nonneg_right h1 h0xy
      have h5 : min a c * dyz ≤ min b c * dyz := mul_le_mul_of_nonneg_right h2 h0yz
      linarith
  · -- `b < min a c`: then `min a b = min b c = b`
    have hab : min a b = b := min_eq_right (le_of_lt (lt_of_lt_of_le hbm (min_le_left _ _)))
    have hbc : min b c = b := min_eq_left (le_of_lt (lt_of_lt_of_le hbm (min_le_right _ _)))
    rw [hab, hbc]
    have hba : b ≤ a := le_of_lt (lt_of_lt_of_le hbm (min_le_left _ _))
    have hbc' : b ≤ c := le_of_lt (lt_of_lt_of_le hbm (min_le_right _ _))
    rw [abs_of_nonneg (sub_nonneg.2 hba), abs_of_nonpos (sub_nonpos.2 hbc')]
    have hsum : |a - c| + 2 * min a c = a + c := by
      rcases le_total a c with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]; ring
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · rw [← hb0]
      nlinarith [mul_le_mul_of_nonneg_left h1xz (le_min ha hc)]
    · have ht := htri (lt_of_le_of_lt hb hbm) hbpos
      have h6 : (min a c - b) * dxz ≤ (min a c - b) * 1 :=
        mul_le_mul_of_nonneg_left h1xz (by linarith)
      have h7 : b * dxz ≤ b * (dxy + dyz) := mul_le_mul_of_nonneg_left ht hb
      nlinarith

end Metrization

section TruncDist

variable {Y : Type*}

open scoped Classical in
/-- The truncated distance `δ(x, y) = min(d(x, y), 1)` of a metric on `V ⊆ Y`, extended by `1`
off `V × V`. -/
def truncDist (V : Set Y) (m : MetricSpace V) (x y : Y) : ℝ :=
  if h : x ∈ V ∧ y ∈ V then min (@dist V m.toDist ⟨x, h.1⟩ ⟨y, h.2⟩) 1 else 1

variable (V : Set Y) (m : MetricSpace V)

lemma truncDist_nonneg (x y : Y) : 0 ≤ truncDist V m x y := by
  unfold truncDist; split_ifs
  · exact le_min (@dist_nonneg V m.toPseudoMetricSpace _ _) zero_le_one
  · exact zero_le_one

lemma truncDist_le_one (x y : Y) : truncDist V m x y ≤ 1 := by
  unfold truncDist; split_ifs
  · exact min_le_right _ _
  · exact le_rfl

lemma truncDist_self {x : Y} (hx : x ∈ V) : truncDist V m x x = 0 := by
  unfold truncDist; rw [dif_pos ⟨hx, hx⟩, @dist_self V m.toPseudoMetricSpace]; simp

lemma truncDist_comm (x y : Y) : truncDist V m x y = truncDist V m y x := by
  unfold truncDist
  by_cases h : x ∈ V ∧ y ∈ V
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩, @dist_comm V m.toPseudoMetricSpace]
  · rw [dif_neg h, dif_neg fun h' => h ⟨h'.2, h'.1⟩]

lemma truncDist_triangle {x y z : Y} (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V) :
    truncDist V m x z ≤ truncDist V m x y + truncDist V m y z := by
  unfold truncDist
  rw [dif_pos ⟨hx, hz⟩, dif_pos ⟨hx, hy⟩, dif_pos ⟨hy, hz⟩]
  have ht := @dist_triangle V m.toPseudoMetricSpace ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
  rcases le_total (@dist V m.toDist ⟨x, hx⟩ ⟨y, hy⟩) 1 with h₁ | h₁ <;>
    rcases le_total (@dist V m.toDist ⟨y, hy⟩ ⟨z, hz⟩) 1 with h₂ | h₂
  · rw [min_eq_left h₁, min_eq_left h₂]
    exact (min_le_left _ _).trans ht
  · rw [min_eq_left h₁, min_eq_right h₂]
    exact (min_le_right _ _).trans
      (by linarith [@dist_nonneg V m.toPseudoMetricSpace ⟨x, hx⟩ ⟨y, hy⟩])
  · rw [min_eq_right h₁, min_eq_left h₂]
    exact (min_le_right _ _).trans
      (by linarith [@dist_nonneg V m.toPseudoMetricSpace ⟨y, hy⟩ ⟨z, hz⟩])
  · rw [min_eq_right h₁, min_eq_right h₂]
    exact (min_le_right _ _).trans (by norm_num)

lemma truncDist_eq_zero {x y : Y} (h : truncDist V m x y = 0) : x = y := by
  unfold truncDist at h
  split_ifs at h with hxy
  · have h1 : @dist V m.toDist ⟨x, hxy.1⟩ ⟨y, hxy.2⟩ = 0 := by
      rcases le_total (@dist V m.toDist ⟨x, hxy.1⟩ ⟨y, hxy.2⟩) 1 with h' | h'
      · rwa [min_eq_left h'] at h
      · rw [min_eq_right h'] at h; exact absurd h one_ne_zero
    have := @eq_of_dist_eq_zero V m _ _ h1
    exact congrArg Subtype.val this
  · exact absurd h one_ne_zero

lemma truncDist_lt {x y : Y} (hx : x ∈ V) (hy : y ∈ V) {r : ℝ} (hr : r ≤ 1)
    (h : truncDist V m x y < r) : @dist V m.toDist ⟨x, hx⟩ ⟨y, hy⟩ < r := by
  unfold truncDist at h
  rw [dif_pos ⟨hx, hy⟩] at h
  rcases le_total (@dist V m.toDist ⟨x, hx⟩ ⟨y, hy⟩) 1 with h' | h'
  · rwa [min_eq_left h'] at h
  · rw [min_eq_right h'] at h; linarith

end TruncDist

section Metrization

variable {Y : Type*} [TopologicalSpace Y] {ι : Type*}

/-- **The metrization lemma** (Smirnov's theorem in the form needed for Theorem 2.16 and
Proposition 2.19 (3)): a space `Y` with open metrizable subspaces `V_i` and continuous functions
`ρ_i ≥ 0` with `supp ρ_i ⊆ V_i`, locally finite supports and `∀ y, ∃ i, ρ_i(y) > 0` is metrizable.
The metric is the locally finite sum of the cone metrics
`e_i(x, y) = |ρ_i(x) − ρ_i(y)| + min(ρ_i(x), ρ_i(y)) · min(d_i(x, y), 1)`. -/
theorem metrizableSpace_of_partition (V : ι → Set Y) (hVo : ∀ i, IsOpen (V i))
    [hm : ∀ i, MetrizableSpace (V i)] (ρ : ι → Y → ℝ) (hρc : ∀ i, Continuous (ρ i))
    (hρ0 : ∀ i y, 0 ≤ ρ i y) (hsupp : ∀ i, tsupport (ρ i) ⊆ V i)
    (hlf : LocallyFinite fun i => tsupport (ρ i)) (hpos : ∀ y, ∃ i, 0 < ρ i y) :
    MetrizableSpace Y := by
  classical
  let m : ∀ i, MetricSpace (V i) := fun i => metrizableSpaceMetric (V i)
  let δ : ι → Y → Y → ℝ := fun i => truncDist (V i) (m i)
  let e : ι → Y → Y → ℝ := fun i x y => |ρ i x - ρ i y| + min (ρ i x) (ρ i y) * δ i x y
  let D : Y → Y → ℝ := fun x y => ∑ᶠ i, e i x y
  have hρV : ∀ i y, y ∉ V i → ρ i y = 0 := fun i y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hsupp i h)
  have hρV' : ∀ i y, 0 < ρ i y → y ∈ V i := fun i y hy => by
    by_contra h; rw [hρV i y h] at hy; exact lt_irrefl _ hy
  have he0 : ∀ i x y, 0 ≤ e i x y := fun i x y =>
    add_nonneg (abs_nonneg _) (mul_nonneg (le_min (hρ0 i x) (hρ0 i y)) (truncDist_nonneg _ _ _ _))
  have hezero : ∀ i x y, x ∉ tsupport (ρ i) → y ∉ tsupport (ρ i) → e i x y = 0 := by
    intro i x y hx hy
    simp only [e, image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy,
      sub_zero, abs_zero, min_self, zero_mul, add_zero]
  have hfin : ∀ x y, (fun i => e i x y).HasFiniteSupport := by
    intro x y
    refine ((hlf.point_finite x).union (hlf.point_finite y)).subset fun i hi => ?_
    by_contra h
    simp only [mem_union, mem_ofPred_eq, not_or] at h
    exact hi (hezero i x y h.1 h.2)
  have hD0 : ∀ x y, 0 ≤ D x y := fun x y => finsum_nonneg fun i => he0 i x y
  have hele : ∀ i x y, e i x y ≤ D x y := fun i x y => single_le_finsum i (hfin x y) (he0 · x y)
  -- metric axioms
  have hself : ∀ x, D x x = 0 := by
    intro x
    refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
    simp only [e, sub_self, abs_zero, zero_add, min_self]
    by_cases hx : x ∈ V i
    · simp only [δ, truncDist_self _ _ hx, mul_zero]
    · simp only [hρV i x hx, zero_mul]
  have hcomm : ∀ x y, D x y = D y x := by
    intro x y
    refine finsum_congr fun i => ?_
    simp only [e, δ]
    rw [abs_sub_comm, min_comm, truncDist_comm]
  have htri : ∀ x y z, D x z ≤ D x y + D y z := by
    intro x y z
    rw [← finsum_add_distrib (hfin x y) (hfin y z)]
    refine finsum_le_finsum' (hfin x z) ((hfin x y).add (hfin y z)) fun i => ?_
    refine cone_triangle (hρ0 i x) (hρ0 i y) (hρ0 i z) (truncDist_nonneg _ _ _ _)
      (truncDist_nonneg _ _ _ _) (truncDist_le_one _ _ _ _) fun hac hb => ?_
    exact truncDist_triangle _ _ (hρV' i x (lt_of_lt_of_le hac (min_le_left _ _)))
      (hρV' i y hb) (hρV' i z (lt_of_lt_of_le hac (min_le_right _ _)))
  have heq : ∀ x y, D x y = 0 → x = y := by
    intro x y h
    obtain ⟨i, hi⟩ := hpos x
    have h1 : e i x y = 0 := le_antisymm (h ▸ hele i x y) (he0 i x y)
    have h2 : |ρ i x - ρ i y| = 0 := by
      have := add_eq_zero_iff_of_nonneg (abs_nonneg _)
        (mul_nonneg (le_min (hρ0 i x) (hρ0 i y)) (truncDist_nonneg _ _ _ _)) |>.1 h1
      exact this.1
    have h3 : min (ρ i x) (ρ i y) * δ i x y = 0 := by
      have := add_eq_zero_iff_of_nonneg (abs_nonneg _)
        (mul_nonneg (le_min (hρ0 i x) (hρ0 i y)) (truncDist_nonneg _ _ _ _)) |>.1 h1
      exact this.2
    have hxy : ρ i y = ρ i x := by
      rw [abs_eq_zero, sub_eq_zero] at h2; exact h2.symm
    rw [hxy, min_self] at h3
    have h4 : δ i x y = 0 := (mul_eq_zero.1 h3).resolve_left hi.ne'
    exact truncDist_eq_zero _ _ h4
  -- continuity of `y ↦ D x y`
  have hcont : ∀ x, Continuous fun y => D x y := by
    intro x
    refine continuous_finsum (fun i => ?_) ?_
    · -- continuity of `y ↦ e i x y`
      refine ((continuous_const.sub (hρc i)).abs).add ?_
      by_cases hx : x ∈ tsupport (ρ i)
      · have hxV : x ∈ V i := hsupp i hx
        refine continuous_iff_continuousAt.2 fun y₀ => ?_
        by_cases hy₀ : y₀ ∈ tsupport (ρ i)
        · have hy₀V : y₀ ∈ V i := hsupp i hy₀
          have hd : ContinuousOn (fun y => δ i x y) (V i) := by
            rw [continuousOn_iff_continuous_domRestrict]
            have : (V i).domRestrict (fun y => δ i x y) =
                fun y : V i => min (@dist (V i) (m i).toDist ⟨x, hxV⟩ y) 1 := by
              funext y
              change truncDist (V i) (m i) x y = _
              unfold truncDist
              rw [dif_pos (And.intro hxV y.2)]
            rw [this]
            exact (@Continuous.dist (V i) (V i) (m i).toPseudoMetricSpace _ _ _
              continuous_const continuous_id).min continuous_const
          exact ((continuous_const.min (hρc i)).continuousAt).mul
            (hd.continuousAt ((hVo i).mem_nhds hy₀V))
        · have hev : (fun y => min (ρ i x) (ρ i y) * δ i x y) =ᶠ[𝓝 y₀] fun _ => 0 := by
            have : (tsupport (ρ i))ᶜ ∈ 𝓝 y₀ := (isClosed_tsupport _).isOpen_compl.mem_nhds hy₀
            filter_upwards [this] with y hy
            rw [image_eq_zero_of_notMem_tsupport hy, min_eq_right (hρ0 i x), zero_mul]
          exact (continuousAt_congr hev).2 continuousAt_const
      · have : (fun y => min (ρ i x) (ρ i y) * δ i x y) = fun _ => 0 := by
          funext y
          rw [image_eq_zero_of_notMem_tsupport hx, min_eq_left (hρ0 i y), zero_mul]
        rw [this]; exact continuous_const
    · -- local finiteness of the supports
      intro y₀
      obtain ⟨N, hN, hNfin⟩ := hlf y₀
      refine ⟨N, hN, (hNfin.union (hlf.point_finite x)).subset fun i hi => ?_⟩
      obtain ⟨y, hy, hyN⟩ := hi
      by_cases hx : x ∈ tsupport (ρ i)
      · exact Or.inr hx
      · left
        by_contra hy'
        have hyt : y ∉ tsupport (ρ i) := fun h => hy' ⟨y, h, hyN⟩
        exact hy (hezero i x y hx hyt)
  -- the topology of `D` is the topology of `Y`
  have H : ∀ s : Set Y, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, D x y < ε → y ∈ s := by
    intro s
    constructor
    · intro hs x hxs
      obtain ⟨i, hi⟩ := hpos x
      have hxV : x ∈ V i := hρV' i x hi
      have hsV : IsOpen (Subtype.val ⁻¹' s : Set (V i)) := hs.preimage continuous_subtype_val
      obtain ⟨r, hr, hball⟩ := (@Metric.isOpen_iff (V i) (m i).toPseudoMetricSpace _).1 hsV
        ⟨x, hxV⟩ hxs
      set r' := min r 1 with hr'
      have hr'pos : 0 < r' := lt_min hr zero_lt_one
      refine ⟨ρ i x / 2 * r', mul_pos (half_pos hi) hr'pos, fun y hy => ?_⟩
      have hey := lt_of_le_of_lt (hele i x y) hy
      have habs : |ρ i x - ρ i y| < ρ i x / 2 * r' :=
        lt_of_le_of_lt (le_add_of_nonneg_right
          (mul_nonneg (le_min (hρ0 i x) (hρ0 i y)) (truncDist_nonneg _ _ _ _))) hey
      have hr'1 : r' ≤ 1 := min_le_right _ _
      have hyρ : ρ i x / 2 < ρ i y := by
        have : ρ i x / 2 * r' ≤ ρ i x / 2 := by
          nlinarith [half_pos hi]
        have := abs_sub_lt_iff.1 (lt_of_lt_of_le habs this)
        linarith [this.1]
      have hyV : y ∈ V i := hρV' i y (lt_trans (half_pos hi) hyρ)
      have hmin : ρ i x / 2 ≤ min (ρ i x) (ρ i y) := le_min (by linarith) hyρ.le
      have hδ : ρ i x / 2 * δ i x y < ρ i x / 2 * r' := by
        have h1 : ρ i x / 2 * δ i x y ≤ min (ρ i x) (ρ i y) * δ i x y :=
          mul_le_mul_of_nonneg_right hmin (truncDist_nonneg _ _ _ _)
        have h2 : min (ρ i x) (ρ i y) * δ i x y ≤ e i x y :=
          le_add_of_nonneg_left (abs_nonneg _)
        linarith
      have hδ' : δ i x y < r' := lt_of_mul_lt_mul_left hδ (half_pos hi).le
      have hdist := truncDist_lt _ _ hxV hyV hr'1 hδ'
      have : (⟨y, hyV⟩ : V i) ∈ Metric.ball (⟨x, hxV⟩ : V i) r := by
        rw [Metric.mem_ball, dist_comm]
        exact lt_of_lt_of_le hdist (min_le_left _ _)
      exact hball this
    · intro h
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨ε, hε, hsub⟩ := h x hx
      refine Filter.mem_of_superset ((isOpen_lt (hcont x) continuous_const).mem_nhds ?_)
        fun y hy => hsub y hy
      change D x x < ε
      rw [hself]; exact hε
  let _ : MetricSpace Y := MetricSpace.ofDistTopology D hself hcomm htri H heq
  infer_instance

/-- **Smirnov's theorem, pulled back** (the form used for `X_m`, `TX`): if `π : Y → X` is
continuous into a paracompact Hausdorff space and every point of `X` has an open neighbourhood `U`
with `π⁻¹(U)` metrizable, then `Y` is metrizable.  (The partition of unity of `X` subordinate to
the `U`'s, pulled back by `π`, feeds `metrizableSpace_of_partition`.) -/
theorem metrizableSpace_of_pullback {X : Type*} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (π : Y → X) (hπ : Continuous π)
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ MetrizableSpace (π ⁻¹' U)) :
    MetrizableSpace Y := by
  choose U hUo hxU hUm using h
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hUo
    fun x _ => mem_iUnion.2 ⟨x, hxU x⟩
  have : ∀ x, MetrizableSpace (π ⁻¹' U x) := hUm
  refine metrizableSpace_of_partition (fun x => π ⁻¹' U x) (fun x => (hUo x).preimage hπ)
    (fun x => f x ∘ π) (fun x => (f x).continuous.comp hπ) (fun x y => f.nonneg x (π y))
    (fun x => (tsupport_comp_subset_preimage _ hπ).trans (preimage_mono (hf x)))
    ((f.locallyFinite.closure.preimage_continuous hπ).subset fun x =>
      tsupport_comp_subset_preimage _ hπ)
    fun y => f.exists_pos (mem_univ (π y))

/-- **Smirnov's metrization theorem** (preprint Theorem 2.55): a paracompact Hausdorff space in
which every point has a metrizable open neighbourhood is metrizable. -/
theorem metrizableSpace_of_locally {X : Type*} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ MetrizableSpace U) :
    MetrizableSpace X :=
  metrizableSpace_of_pullback id continuous_id h

/-- A metrizable space is paracompact (A. H. Stone). -/
theorem paracompactSpace_of_metrizableSpace (X : Type*) [TopologicalSpace X]
    [MetrizableSpace X] : ParacompactSpace X := by
  let _ := metrizableSpaceMetric X
  infer_instance

end Metrization

/-- A countable product of metrizable spaces is metrizable. -/
theorem metrizableSpace_pi_nat (A : ℕ → Type*) [∀ i, TopologicalSpace (A i)]
    [∀ i, MetrizableSpace (A i)] : MetrizableSpace (∀ i, A i) := by
  let _ := fun i => metrizableSpaceMetric (A i)
  let _ : MetricSpace (∀ i, A i) := PiCountable.metricSpace
  infer_instance

/-! ### Charts are metrizable -/

namespace MChart

universe u

variable {X : Type u} [TopologicalSpace X] (φ : MChart X)

/-- A chart `φ : V → O` is a homeomorphism of `V` onto the retract `O ⊆ E₀`. -/
def sourceHomeomorph : φ.source ≃ₜ φ.model.O where
  toFun x := ⟨φ x, φ.mapsTo_model x x.2⟩
  invFun z := ⟨φ.symm z, φ.symm_mapsTo z.2⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x.2)
  right_inv z := Subtype.ext (φ.apply_symm_apply z.2)
  continuous_toFun :=
    (φ.continuousOn_toFun.comp_continuous continuous_subtype_val fun x => x.2).subtype_mk _
  continuous_invFun :=
    (φ.continuousOn_invFun.comp_continuous continuous_subtype_val fun z => z.2).subtype_mk _

/-- The domain of a chart is metrizable (it is homeomorphic to a subset of the Banach space
`E₀`). -/
theorem metrizableSpace_source : MetrizableSpace φ.source :=
  φ.sourceHomeomorph.isEmbedding.metrizableSpace

end MChart

/-! ### Theorem 2.16: `X`, `X_m` and `X_∞` are metrizable -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

include P in
/-- **Theorem 2.16**, `m = 0`: an M-polyfold is metrizable (Smirnov's theorem: paracompact,
Hausdorff, and locally homeomorphic to subsets of Banach spaces). -/
theorem metrizableSpace : MetrizableSpace X := by
  refine metrizableSpace_of_locally fun x => ?_
  obtain ⟨φ, -, hx⟩ := P.exists_isChart_mem_source x
  exact ⟨φ.source, φ.isOpen_source, hx, φ.metrizableSpace_source⟩

/-- In the level `X_m`, the points of a chart domain `V` form the set `V_m`, and
`x ↦ φ(x) ∈ O_m ⊆ E_m` is an embedding of `V_m` (the text: "`φ : V_m → O_m` is a homeomorphism"). -/
theorem isEmbedding_levelLift {φ : MChart X} (hφ : P.IsChart φ) (m : ℕ) :
    Topology.IsEmbedding fun x : (P.levelVal m ⁻¹' φ.source : Set (P.Level m)) =>
      levelLift φ m (P.levelVal m x) := by
  set f := fun x : (P.levelVal m ⁻¹' φ.source : Set (P.Level m)) =>
    levelLift φ m (P.levelVal m x) with hf
  have hbase : ∀ x : (P.levelVal m ⁻¹' φ.source : Set (P.Level m)),
      φ.model.E.toBase m (f x) = φ (P.levelVal m x) := fun x =>
    P.toBase_levelLift hφ x.2 (levelVal_mem x.1)
  refine ⟨⟨le_antisymm ?_ ?_⟩, ?_⟩
  · -- `f` is continuous
    rw [← continuous_iff_le_induced]
    rw [continuous_def]
    intro W hW
    have := (isOpen_level_basic hφ hW).preimage
      (continuous_subtype_val (p := fun x : P.Level m => x ∈ P.levelVal m ⁻¹' φ.source))
    convert this using 1
    ext x
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  · -- every generator of the topology of `X_m` is open for the induced topology
    change TopologicalSpace.induced f _ ≤ TopologicalSpace.induced Subtype.val
      (TopologicalSpace.generateFrom (P.levelBasis m))
    rw [induced_generateFrom_eq]
    refine TopologicalSpace.le_generateFrom_iff_subset_isOpen.2 ?_
    rintro _ ⟨_, ⟨ψ, hψ, W, hW, rfl⟩, rfl⟩
    obtain ⟨W₀, hW₀, hW₀eq⟩ := φ.exists_isOpen_image_eq (s := φ.source ∩ ψ.source)
      inter_subset_left (φ.isOpen_source.inter ψ.isOpen_source)
    have hcont : ContinuousOn (levelMap (φ.transition ψ) m) (φ.model.E.lvlSet (φ.overlap ψ) m) :=
      (hφ.compatible hψ (P := P)).1.continuousOn_levelMap (φ.isScRetract_overlap ψ) m
    obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hcont) W hW
    have hov : φ.overlap ψ = φ.model.O ∩ W₀ := hW₀eq
    refine isOpen_induced_iff.2 ⟨φ.model.E.lvlSet W₀ m ∩ u,
      (φ.model.E.isOpen_lvlSet hW₀ m).inter hu, ?_⟩
    ext x
    have hxV : P.levelVal m x ∈ φ.source := x.2
    have hxO : φ (P.levelVal m x) ∈ φ.model.O := φ.mapsTo_model _ hxV
    change (f x ∈ φ.model.E.lvlSet W₀ m ∧ f x ∈ u) ↔
      (P.levelVal m x ∈ ψ.source ∧ levelLift ψ m (P.levelVal m x) ∈ W)
    have hz1 : f x ∈ φ.model.E.lvlSet (φ.overlap ψ) m ↔ P.levelVal m x ∈ ψ.source := by
      rw [ScBanach.mem_lvlSet, hbase]
      constructor
      · rintro ⟨y, hy, hyeq⟩
        rw [← φ.toPartialEquiv.injOn hy.1 hxV hyeq]; exact hy.2
      · intro h; exact ⟨_, ⟨hxV, h⟩, rfl⟩
    have hz2 : levelLift ψ m (P.levelVal m x) = levelMap (φ.transition ψ) m (f x) := by
      change Function.invFun (ψ.model.E.toBase m) (ψ (P.levelVal m x)) =
        Function.invFun (ψ.model.E.toBase m) (φ.transition ψ (φ.model.E.toBase m (f x)))
      rw [hbase, φ.transition_apply ψ hxV]
    rw [hz2]
    constructor
    · rintro ⟨h1, h2⟩
      have hzov : f x ∈ φ.model.E.lvlSet (φ.overlap ψ) m := by
        rw [ScBanach.mem_lvlSet, hov]
        exact ⟨by rw [hbase]; exact hxO, h1⟩
      have : f x ∈ u ∩ φ.model.E.lvlSet (φ.overlap ψ) m := ⟨h2, hzov⟩
      rw [← hueq] at this
      exact ⟨hz1.1 hzov, this.1⟩
    · rintro ⟨h1, h2⟩
      have hzov := hz1.2 h1
      have : f x ∈ levelMap (φ.transition ψ) m ⁻¹' W ∩ φ.model.E.lvlSet (φ.overlap ψ) m :=
        ⟨h2, hzov⟩
      rw [hueq] at this
      refine ⟨?_, this.1⟩
      have h3 : φ.model.E.toBase m (f x) ∈ φ.model.O ∩ W₀ := hov ▸ hzov
      exact h3.2
  · -- `f` is injective
    intro x y hxy
    have h := congrArg (φ.model.E.toBase m) hxy
    simp only [hbase] at h
    exact Subtype.ext (level_ext (φ.toPartialEquiv.injOn x.2 y.2 h))

/-- **Theorem 2.16**: the level `X_m` of an M-polyfold is metrizable. -/
theorem metrizableSpace_level (m : ℕ) : MetrizableSpace (P.Level m) := by
  refine metrizableSpace_of_pullback (P.levelVal m) (continuous_levelVal m) fun x => ?_
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source x
  exact ⟨φ.source, φ.isOpen_source, hx, (P.isEmbedding_levelLift hφ m).metrizableSpace⟩

/-- **Theorem 2.16**: the level `X_m` of an M-polyfold is paracompact. -/
instance paracompactSpace_level (m : ℕ) : ParacompactSpace (P.Level m) :=
  have := P.metrizableSpace_level m
  paracompactSpace_of_metrizableSpace _

/-- `X_∞ = ⋂ X_m` as a type. -/
def SmoothLevel : Type u := P.smoothSet

/-- The inclusion `X_∞ → ∏_m X_m`. -/
def smoothIncl (x : P.SmoothLevel) (m : ℕ) : P.Level m :=
  P.levelMk m (x : P.smoothSet).1 (mem_iInter.1 (x : P.smoothSet).2 m)

/-- The topology of `X_∞`: the initial topology of the inclusions `X_∞ → X_m` (which the text does
not define; `smoothLevel_topology_eq`). -/
instance : TopologicalSpace P.SmoothLevel := TopologicalSpace.induced P.smoothIncl inferInstance

/-- The topology of `X_∞` is the coarsest making all inclusions `X_∞ → X_m` continuous. -/
theorem smoothLevel_topology_eq :
    (inferInstance : TopologicalSpace P.SmoothLevel) =
      ⨅ m, TopologicalSpace.induced (fun x => P.smoothIncl x m) inferInstance := by
  change TopologicalSpace.induced P.smoothIncl (⨅ m, TopologicalSpace.induced (fun f => f m) _) = _
  rw [induced_iInf]
  simp only [induced_compose]
  rfl

/-- **Theorem 2.16**: `X_∞` is metrizable. -/
theorem metrizableSpace_smoothLevel : MetrizableSpace P.SmoothLevel := by
  have := fun m => P.metrizableSpace_level m
  have := metrizableSpace_pi_nat P.Level
  refine (show Topology.IsEmbedding P.smoothIncl from ⟨⟨rfl⟩, fun x y h => ?_⟩).metrizableSpace
  have := congrArg (fun f => P.levelVal 0 (f 0)) h
  exact Subtype.ext this

/-- **Theorem 2.16**: for an M-polyfold `X`, every `X_m` is metrizable and in particular
paracompact, and `X_∞` is metrizable. -/
theorem _root_.Polyfold.theorem_2_16 :
    MetrizableSpace X ∧ (∀ m, MetrizableSpace (P.Level m) ∧ ParacompactSpace (P.Level m)) ∧
      MetrizableSpace P.SmoothLevel :=
  ⟨P.metrizableSpace, fun m => ⟨P.metrizableSpace_level m, inferInstance⟩,
    P.metrizableSpace_smoothLevel⟩

include P in
/-- A subset of an M-polyfold is metrizable, hence paracompact: in particular a sub-M-polyfold
`A` (Proposition 2.21, whose `MPolyfold.subPolyfold` takes `[ParacompactSpace A]`). -/
theorem paracompactSpace_subtype (A : Set X) : ParacompactSpace A := by
  have := P.metrizableSpace
  exact paracompactSpace_of_metrizableSpace A

/-- **Proposition 2.19 (3)**: the tangent space `TX` is metrizable. -/
theorem metrizableSpace_tangentSpace : MetrizableSpace P.TangentSpace := by
  refine metrizableSpace_of_pullback (fun α => P.levelVal 1 (P.tangentProj α))
    P.continuous_levelVal_tangentProj fun x => ?_
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source x
  refine ⟨φ.source, φ.isOpen_source, hx, ?_⟩
  rcases isEmpty_or_nonempty P.TangentSpace with h | ⟨⟨α₀⟩⟩
  · have : IsEmpty ((fun α => P.levelVal 1 (P.tangentProj α)) ⁻¹' φ.source) :=
      ⟨fun a => h.false a.1⟩
    infer_instance
  · exact (tangentChart hφ α₀).metrizableSpace_source

/-- **Proposition 2.19 (3)**: the tangent space `TX` is paracompact. -/
instance paracompactSpace_tangentSpace : ParacompactSpace P.TangentSpace :=
  have := P.metrizableSpace_tangentSpace
  paracompactSpace_of_metrizableSpace _

/-- **Proposition 2.19 (3)**: `TX` is metrizable and paracompact. -/
theorem _root_.Polyfold.proposition_2_19_3 :
    MetrizableSpace P.TangentSpace ∧ ParacompactSpace P.TangentSpace :=
  ⟨P.metrizableSpace_tangentSpace, inferInstance⟩

end MPolyfold

/-! ### Proposition 2.21 (3), (4): tangent spaces of sub-M-polyfolds, in a chart -/

section Prop221

variable {E : ScBanach} {C : Set (E 0)}

/-- An identity between base maps of sc-operators holds on every level. -/
lemma ScOperator.lvl_comp_of_base {A B D : ScOperator E E}
    (h : ∀ v, A 0 (B 0 v) = D 0 v) (m : ℕ) (x : E m) : A m (B m x) = D m x := by
  apply E.toBase_injective m
  rw [A.toBase_comm, B.toBase_comm, D.toBase_comm, h]

lemma ScOperator.lvl_comp_eq_zero_of_base {A B : ScOperator E E}
    (h : ∀ v, A 0 (B 0 v) = 0) (m : ℕ) (x : E m) : A m (B m x) = 0 := by
  apply E.toBase_injective m
  rw [A.toBase_comm, B.toBase_comm, h, map_zero]

lemma ScOperator.lvl_eq_add_of_base {A B D : ScOperator E E}
    (h : ∀ v, A 0 v = B 0 v + D 0 v) (m : ℕ) (x : E m) : A m x = B m x + D m x := by
  apply E.toBase_injective m
  rw [map_add, A.toBase_comm, B.toBase_comm, D.toBase_comm, h]

/-- The retraction `t = s ∘ r : U → U` onto `s(O)`, for a retraction `r` onto `O` and an sc-smooth
`s : O → O` with `s ∘ s = s` (Proposition 2.10 (2), the text's `t` in the proof of Proposition
2.21 (3)). -/
def ScRetraction.compRetraction (R : ScRetraction E C) {s : E 0 → E 0}
    (hs : IsScSmoothRetractMap E C R.retract E C R.retract s)
    (hss : ∀ x ∈ R.retract, s (s x) = s x) : ScRetraction E C where
  U := R.U
  toFun := s ∘ R
  relOpen := R.relOpen
  mapsTo y hy := R.retract_subset (hs.mapsTo (R.apply_mem_retract hy))
  isScSmooth := hs.comp_isScSmooth R rfl
  idem y hy := by
    simp only [Function.comp_apply]
    rw [R.apply_eq_self_of_mem_retract (hs.mapsTo (R.apply_mem_retract hy)),
      hss _ (R.apply_mem_retract hy)]

lemma ScRetraction.compRetraction_retract (R : ScRetraction E C) {s : E 0 → E 0}
    (hs : IsScSmoothRetractMap E C R.retract E C R.retract s)
    (hss : ∀ x ∈ R.retract, s (s x) = s x) :
    (R.compRetraction hs hss).retract = s '' R.retract := by
  change (s ∘ R) '' R.U = s '' R.retract
  rw [image_comp]; rfl

/-- **Proposition 2.21 (3)**, in a chart: let `O = r(U)` (an open piece of `X` in a chart), `A ∩ O =
s(O)` for an sc-smooth retraction `s : O → O`, `t = s ∘ r`, and `a ∈ A` smooth.  Then
`T_aA = Dt(a)E` and `T_aO = Dr(a)E` satisfy `T_aA ⊆ T_aO` and
`T_aO = T_aA ⊕ (Dr(a) − Dt(a))E` as an sc-splitting: both summands are sc-subspaces of `E` and the
sum is direct on every level.  (`Dr(a)`, `Dt(a)` are commuting sc-projections with
`Dr(a)Dt(a) = Dt(a)Dr(a) = Dt(a)`.) -/
theorem proposition_2_21_3 (R : ScRetraction E C) {s : E 0 → E 0}
    (hs : IsScSmoothRetractMap E C R.retract E C R.retract s)
    (hss : ∀ x ∈ R.retract, s (s x) = s x) {a : E 1} (ha : a ∈ E.lvlSet (s '' R.retract) 1)
    (has : a ∈ E.smoothLvl 1) :
    tangentSpace E C R.retract a = (LinearMap.range (scDeriv R.U R a : E 0 →ₗ[ℝ] E 0) : Set (E 0)) ∧
      tangentSpace E C (s '' R.retract) a =
        (LinearMap.range (scDeriv R.U (s ∘ R) a : E 0 →ₗ[ℝ] E 0) : Set (E 0)) ∧
      LinearMap.range (scDeriv R.U (s ∘ R) a : E 0 →ₗ[ℝ] E 0) ≤
        LinearMap.range (scDeriv R.U R a : E 0 →ₗ[ℝ] E 0) ∧
      E.IsScSubspace (LinearMap.range (scDeriv R.U (s ∘ R) a : E 0 →ₗ[ℝ] E 0)) ∧
      E.IsScSubspace (LinearMap.range (scDeriv R.U R a - scDeriv R.U (s ∘ R) a : E 0 →ₗ[ℝ] E 0)) ∧
      ∀ m, Disjoint (E.levelSub (LinearMap.range (scDeriv R.U (s ∘ R) a : E 0 →ₗ[ℝ] E 0)) m)
          (E.levelSub (LinearMap.range (scDeriv R.U R a - scDeriv R.U (s ∘ R) a :
            E 0 →ₗ[ℝ] E 0)) m) ∧
        E.levelSub (LinearMap.range (scDeriv R.U (s ∘ R) a : E 0 →ₗ[ℝ] E 0)) m ⊔
          E.levelSub (LinearMap.range (scDeriv R.U R a - scDeriv R.U (s ∘ R) a :
            E 0 →ₗ[ℝ] E 0)) m =
          E.levelSub (LinearMap.range (scDeriv R.U R a : E 0 →ₗ[ℝ] E 0)) m := by
  set ρ := R.compRetraction hs hss with hρ
  have hρret : ρ.retract = s '' R.retract := R.compRetraction_retract hs hss
  have hsV : s '' R.retract ⊆ R.retract := by rintro _ ⟨x, hx, rfl⟩; exact hs.mapsTo hx
  have ha1 : a ∈ E.lvlSet R.retract 1 := hsV ha
  have ha1ρ : a ∈ E.lvlSet ρ.retract 1 := by rw [ScBanach.mem_lvlSet, hρret]; exact ha
  have haU : a ∈ E.lvlSet R.U 1 := R.lvlSet_retract_subset 1 ha1
  set P := scDeriv R.U R a with hP
  set Q := scDeriv R.U (s ∘ R) a with hQ
  have hQρ : Q = scDeriv ρ.U ρ a := rfl
  have hPP : ∀ v, P (P v) = P v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self ha1)
  have hQQ : ∀ v, Q (Q v) = Q v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (ρ.scDeriv_comp_self ha1ρ)
  -- `r ∘ t = t` and `t ∘ r = t` on `U`, hence `PQ = Q = QP`
  have hRρ : EqOn (R ∘ ρ) ρ R.U := fun y hy =>
    R.apply_eq_self_of_mem_retract (hs.mapsTo (R.apply_mem_retract hy))
  have hρR : EqOn (ρ ∘ R) ρ R.U := fun y hy => by
    change s (R (R y)) = s (R y); rw [R.idem y hy]
  have hPQ : ∀ v, P (Q v) = Q v := by
    intro v
    have h1 := scDeriv_comp_apply R.relOpen R.relOpen ρ.isSc1 R.isSc1 ρ.mapsTo haU v
    rw [ρ.levelMap_one_eq_self ha1ρ] at h1
    change scDeriv R.U R a (scDeriv R.U ρ a v) = scDeriv R.U ρ a v
    rw [h1]
    have h2 := IsSc1.tangentMap_congr R.isScDomain
      (theorem_1_21 R.relOpen R.relOpen ρ.isSc1 R.isSc1 ρ.mapsTo).1 hRρ
      (show ((a, v) : E.tangent 0) ∈ E.tangentSet R.U from haU)
    exact congrArg Prod.snd h2
  have hQP : ∀ v, Q (P v) = Q v := by
    intro v
    have h1 := scDeriv_comp_apply R.relOpen R.relOpen R.isSc1 ρ.isSc1 R.mapsTo haU v
    rw [R.levelMap_one_eq_self ha1] at h1
    change scDeriv R.U ρ a (scDeriv R.U R a v) = scDeriv R.U ρ a v
    rw [h1]
    have h2 := IsSc1.tangentMap_congr R.isScDomain
      (theorem_1_21 R.relOpen R.relOpen R.isSc1 ρ.isSc1 R.mapsTo).1 hρR
      (show ((a, v) : E.tangent 0) ∈ E.tangentSet R.U from haU)
    exact congrArg Prod.snd h2
  -- the sc-operators `P`, `Q`, `P − Q`
  have hPop : IsScOperator P := R.isSc1.isSc1With_scDeriv.scOperator_deriv haU has
  have hQop : IsScOperator Q := ρ.isSc1.isSc1With_scDeriv.scOperator_deriv haU has
  have hDop : IsScOperator (P - Q) := fun m => by
    obtain ⟨Pm, hPm⟩ := hPop m
    obtain ⟨Qm, hQm⟩ := hQop m
    exact ⟨Pm - Qm, fun x => by simp [hPm, hQm]⟩
  set Pₒ := hPop.toScOperator
  set Qₒ := hQop.toScOperator
  set Dₒ := hDop.toScOperator
  have hP0 : Pₒ 0 = P := hPop.toScOperator_zero
  have hQ0 : Qₒ 0 = Q := hQop.toScOperator_zero
  have hD0 : Dₒ 0 = P - Q := hDop.toScOperator_zero
  have hQQ' : ∀ v, Qₒ 0 (Qₒ 0 v) = Qₒ 0 v := by rw [hQ0]; exact hQQ
  have hDD' : ∀ v, Dₒ 0 (Dₒ 0 v) = Dₒ 0 v := by
    rw [hD0]; intro v
    simp only [sub_apply, map_sub, hPP, hPQ, hQP, hQQ, sub_self, sub_zero]
  have hPP' : ∀ v, Pₒ 0 (Pₒ 0 v) = Pₒ 0 v := by rw [hP0]; exact hPP
  have hQD : ∀ v, Qₒ 0 (Dₒ 0 v) = 0 := by
    rw [hQ0, hD0]; intro v
    simp only [sub_apply, map_sub, hQP, hQQ, sub_self]
  have hPQ' : ∀ v, Pₒ 0 (Qₒ 0 v) = Qₒ 0 v := by rw [hP0, hQ0]; exact hPQ
  have hPD' : ∀ v, Pₒ 0 (Dₒ 0 v) = Dₒ 0 v := by
    rw [hP0, hD0]; intro v
    simp only [sub_apply, map_sub, hPP, hPQ]
  have hsum : ∀ v, Pₒ 0 v = Qₒ 0 v + Dₒ 0 v := by
    rw [hP0, hQ0, hD0]; intro v
    simp only [sub_apply]; abel
  have hsplitQ := ScBanach.isScSplitting_of_idem Qₒ hQQ'
  have hsplitD := ScBanach.isScSplitting_of_idem Dₒ hDD'
  rw [hQ0] at hsplitQ
  rw [hD0, ContinuousLinearMap.toLinearMap_sub] at hsplitD
  refine ⟨tangentSpace_eq_coe_submodule R ha1, ?_, ?_, hsplitQ.1, hsplitD.1, fun m => ?_⟩
  · rw [← hρret]; exact tangentSpace_eq_coe_submodule ρ ha1ρ
  · rintro _ ⟨v, rfl⟩
    exact ⟨Q v, hPQ v⟩
  · -- the levelwise direct sum
    have hlQ := Qₒ.levelSub_range_eq hQQ' m
    have hlD := Dₒ.levelSub_range_eq hDD' m
    have hlP := Pₒ.levelSub_range_eq hPP' m
    rw [hQ0] at hlQ; rw [hD0, ContinuousLinearMap.toLinearMap_sub] at hlD; rw [hP0] at hlP
    rw [hlQ, hlD, hlP]
    have hQQm := Qₒ.idem_lvl hQQ' m
    have hQDm := ScOperator.lvl_comp_eq_zero_of_base hQD m
    have hPQm := ScOperator.lvl_comp_of_base hPQ' m
    have hPDm := ScOperator.lvl_comp_of_base hPD' m
    have hsumm := ScOperator.lvl_eq_add_of_base hsum m
    refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      rintro v ⟨x, rfl⟩ ⟨y, hy⟩
      have h1 : Qₒ m (Qₒ m x) = Qₒ m x := hQQm x
      change Qₒ m x = 0
      rw [← h1]
      rw [show Qₒ m x = Dₒ m y from hy.symm, hQDm]
    · apply le_antisymm
      · refine sup_le ?_ ?_
        · rintro _ ⟨x, rfl⟩; exact ⟨Qₒ m x, hPQm x⟩
        · rintro _ ⟨x, rfl⟩; exact ⟨Dₒ m x, hPDm x⟩
      · rintro _ ⟨x, rfl⟩
        change Pₒ m x ∈ _
        rw [hsumm x]
        exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

/-- **Proposition 2.21 (4)**, in a chart: with `s`, `t = s ∘ r` and a smooth `a ∈ A` as in
`proposition_2_21_3`, the induced map `s : O → s(O) = A ∩ O` is sc-smooth and its tangent map at
`a` maps `T_aO` onto `T_aA`: `Ts(a)(T_aO) = T_aA`. -/
theorem proposition_2_21_4 (R : ScRetraction E C) {s : E 0 → E 0}
    (hs : IsScSmoothRetractMap E C R.retract E C R.retract s)
    (hss : ∀ x ∈ R.retract, s (s x) = s x) {a : E 1} (ha : a ∈ E.lvlSet (s '' R.retract) 1) :
    IsScSmoothRetractMap E C R.retract E C (s '' R.retract) s ∧
      (fun h => (retractTangentMap E C R.retract s ((a, h) : E.tangent 0)).2) ''
          tangentSpace E C R.retract a = tangentSpace E C (s '' R.retract) a := by
  set ρ := R.compRetraction hs hss with hρ
  have hρret : ρ.retract = s '' R.retract := R.compRetraction_retract hs hss
  have hsV : s '' R.retract ⊆ R.retract := by rintro _ ⟨x, hx, rfl⟩; exact hs.mapsTo hx
  have ha1 : a ∈ E.lvlSet R.retract 1 := hsV ha
  have ha1ρ : a ∈ E.lvlSet ρ.retract 1 := by rw [ScBanach.mem_lvlSet, hρret]; exact ha
  have haU : a ∈ E.lvlSet R.U 1 := R.lvlSet_retract_subset 1 ha1
  have hs' : IsScSmoothRetractMap E C R.retract E C (s '' R.retract) s :=
    (isScSmoothRetractMap_iff_exists R.isScRetract).2
      ⟨fun x hx => ⟨x, hx, rfl⟩, R, rfl, hs.comp_isScSmooth R rfl⟩
  refine ⟨hs', ?_⟩
  set P := scDeriv R.U R a with hP
  set Q := scDeriv R.U (s ∘ R) a with hQ
  have hPP : ∀ v, P (P v) = P v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self ha1)
  have hρR : EqOn (ρ ∘ R) ρ R.U := fun y hy => by
    change s (R (R y)) = s (R y); rw [R.idem y hy]
  have hQP : ∀ v, Q (P v) = Q v := by
    intro v
    have h1 := scDeriv_comp_apply R.relOpen R.relOpen R.isSc1 ρ.isSc1 R.mapsTo haU v
    rw [R.levelMap_one_eq_self ha1] at h1
    change scDeriv R.U ρ a (scDeriv R.U R a v) = scDeriv R.U ρ a v
    rw [h1]
    have h2 := IsSc1.tangentMap_congr R.isScDomain
      (theorem_1_21 R.relOpen R.relOpen R.isSc1 ρ.isSc1 R.mapsTo).1 hρR
      (show ((a, v) : E.tangent 0) ∈ E.tangentSet R.U from haU)
    exact congrArg Prod.snd h2
  -- `Ts(a) = T(s ∘ r)(a, ·) = Q` on `T_aO`
  have hTs : ∀ h ∈ tangentSpace E C R.retract a,
      (retractTangentMap E C R.retract s ((a, h) : E.tangent 0)).2 = Q h := by
    intro h hh
    have := retractTangentMap_eqOn hs' R rfl (show ((a, h) : E.tangent 0) ∈
      retractTangent E C R.retract from hh)
    rw [this]; rfl
  have hmem : ∀ u, P u ∈ tangentSpace E C R.retract a := fun u => by
    rw [tangentSpace_eq_coe_submodule R ha1]; exact ⟨u, rfl⟩
  rw [← hρret, tangentSpace_eq_coe_submodule ρ ha1ρ]
  ext w
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [tangentSpace_eq_coe_submodule R ha1] at hh
    obtain ⟨u, rfl⟩ := hh
    change (retractTangentMap E C R.retract s ((a, P u) : E.tangent 0)).2 ∈ _
    rw [hTs _ (hmem u)]
    exact ⟨P u, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨P u, hmem u, ?_⟩
    change (retractTangentMap E C R.retract s ((a, P u) : E.tangent 0)).2 = _
    rw [hTs _ (hmem u)]
    exact hQP u

end Prop221

end Polyfold
