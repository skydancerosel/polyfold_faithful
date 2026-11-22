import Polyfold.Chapter18.AuxiliaryNormsDirectExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18, §18.1,
pp. 846–847: **Definition 18.1.7 as printed and Lemma 18.1.8**.  Numbers and pages are the 2021
text's.

## The text, paraphrased

Definition 18.1.7 (p. 846): an auxiliary norm for a strong polyfold bundle `P : E → C` is a functor
`N : E → [0, ∞]` with (1) `N = +∞` off `E_{0,1}`, (2) a complete norm on every fibre of `E_{0,1}`,
(3) `|P(h_k)| → |α|` and `|N|(|h_k|) → 0` imply `|h_k| → |0_α|` in `|E_{0,1}|`.  Lemma 18.1.8
(p. 847, proof left to the reader): `N` is an auxiliary norm iff `N ∘ Γ̄_Ψ̄` is an auxiliary norm
of the strong bundle `W_Ψ̄ → X_Ψ` over the ep-groupoid (Definition 12.2.1) for a covering family.

## The reading

Definition 12.2.1 asks the auxiliary norm to be a **continuous** map `N : W_{0,1} → [0, ∞)`.
Definition 18.1.7 is introduced by "we import the notion of an auxiliary norm from the ep-groupoid
context into the categorical framework", but its printed clauses (a functor into `[0, ∞]`, (1),
(2), (3)) ask for no continuity of `|N|` on `|E_{0,1}|`, and none of them forces it: `E` carries no
topology on its objects, "functor" only makes `N` constant along the morphisms of `E`, and (3) is
a condition at the zero section only.  We read Definition 18.1.7 as Definition 12.2.1, continuity
included (l. 41710, "import the notion"): `IsAuxNormDirect` (`AuxiliaryNormsDirect.lean`), for
which `lemma_18_1_8` proves Lemma 18.1.8.  `IsAuxNormBook` is the printed clauses alone; this file
shows why the continuity has to come along.

## What is formalized

* `baseScale a N : e ↦ a(|P(e)|) · N(e)`; `IsAuxNormBook.baseScale`: for every `a ≥ 1` (no
  continuity), `a(|P|) · N` satisfies Definition 18.1.7 as printed when `N` does.
* `IsAuxNormDirect.continuousAt_baseScale`, `IsAuxNormDirect.not_isAuxNormDirect_baseScale`: if
  `N` and `a(|P|) · N` both have continuous `|·|`, then `a ∘ |P|` is continuous on `|E_{0,1}|`
  wherever `|N| ≠ 0`; so a factor discontinuous there gives no auxiliary norm in the direct form.
* On the reflection bundle `P : E → ℤ/2 ⋉ ℝ` (`reflQ`, fibre `ℝ`, `−1` acting by `v ↦ −v`):
  `reflJump` (`a(|0|) = 1` at the point with isotropy `ℤ/2`, `a = 2` elsewhere), the continuous
  path `t ↦ |(t, 1)|` in `|E_{0,1}|` (`reflPathOrbit`, read in the model of one copy of `Ψ̄`), and
  `not_continuousAt_reflJump_oneBase`.  `reflQ_baseScale_witness`: for an auxiliary norm `N₀`,
  `N = a(|P|) · N₀` satisfies Definition 18.1.7 as printed, and `N ∘ Γ̄_Ψ̄` is an auxiliary norm
  (Definition 12.2.1) in no covering model.
* **`lemma_18_1_8_book_without_continuity`**: the "⇒" half of Lemma 18.1.8 for the printed
  clauses of Definition 18.1.7 without the continuity of Definition 12.2.1 does not hold.  The "⇐" half
  holds for that form (`IsAuxNormIn.isAuxNormBook`); Lemma 18.1.8 as we read it (Definition 18.1.7
  with the continuity of Definition 12.2.1) is `lemma_18_1_8`, restated as
  `isAuxNormIn_iff_isAuxNormBook_continuous`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter
open scoped ENNReal

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor

variable {C : GCT.{u}} {V : C.VectorBundle}

/-- `e ↦ |P(e)|` is constant along the morphisms of `E`. -/
theorem isMorInvariant_π_base : IsMorInvariant (V := V) fun e => C.toGroupoidStr.π (V.base e) :=
  fun a => congrArg V.proj.orbitMap ((GroupoidStr.π_eq_π_iff _).2 ⟨a, rfl, rfl⟩).symm

variable (V) in
/-- **`N` rescaled by a function of the base point**: `e ↦ a(|P(e)|) · N(e)`. -/
def baseScale (a : C.toGroupoidStr.OrbitSpace → ℝ) (N : V.EObj → ℝ≥0∞) (e : V.EObj) : ℝ≥0∞ :=
  ENNReal.ofReal (a (C.toGroupoidStr.π (V.base e))) * N e

namespace StrongPolyfoldBundleConstruction

variable {S : C.PolyfoldConstruction} {Q : V.StrongPolyfoldBundleConstruction S}

/-- A complete norm times a constant `0 < t < ∞` is a complete norm. -/
theorem IsCompleteNormOn.const_mul {F : Type*} [AddCommGroup F] [Module ℝ F] {n : F → ℝ≥0∞}
    {A : Set F} (h : IsCompleteNormOn n A) {t : ℝ≥0∞} (ht0 : t ≠ 0) (htop : t ≠ ⊤) :
    IsCompleteNormOn (fun v => t * n v) A where
  ne_top v hv := ENNReal.mul_ne_top htop (h.ne_top v hv)
  eq_zero v hv h0 := h.eq_zero v hv ((mul_eq_zero.1 h0).resolve_left ht0)
  smul s v hv := by
    rw [h.smul s v hv, mul_left_comm]
  add_le v hv w hw := by
    rw [← mul_add]
    gcongr
    exact h.add_le v hv w hw
  complete u hu hC := by
    obtain ⟨v, hv, ht⟩ := h.complete u hu fun ε hε => by
      obtain ⟨m, hm⟩ := hC (t * ε) (ENNReal.mul_pos ht0 hε.ne')
      refine ⟨m, fun i hi j hj => lt_of_not_ge fun hle => (hm i hi j hj).not_ge ?_⟩
      gcongr
    refine ⟨v, hv, ?_⟩
    have := ENNReal.Tendsto.const_mul ht (Or.inr htop)
    rwa [mul_zero] at this

theorem baseScale_objMk (a : C.toGroupoidStr.OrbitSpace → ℝ) (N : V.EObj → ℝ≥0∞) (α : C.Obj)
    (v : V.V α) :
    V.baseScale a N (V.objMk α v) = ENNReal.ofReal (a (C.toGroupoidStr.π α)) * N (V.objMk α v) :=
  rfl

/-- **Definition 18.1.7 as printed is kept by a factor `a(|P(e)|) ≥ 1`**, whatever `a` is:
(1) and (2) because `a` is a positive constant on every fibre, (3) because `N ≤ a(|P|) · N`. -/
theorem IsAuxNormBook.baseScale {N : V.EObj → ℝ≥0∞} (h : Q.IsAuxNormBook N)
    {a : C.toGroupoidStr.OrbitSpace → ℝ} (ha : ∀ z, 1 ≤ a z) :
    Q.IsAuxNormBook (V.baseScale a N) where
  isMorInvariant φ := by
    have e := isMorInvariant_π_base (V := V) φ
    unfold GCT.VectorBundle.baseScale
    simp only at e
    rw [e, h.isMorInvariant φ]
  eq_top e he := by
    unfold GCT.VectorBundle.baseScale
    rw [h.eq_top e he]
    exact ENNReal.mul_top (ENNReal.ofReal_pos.2 (zero_lt_one.trans_le (ha _))).ne'
  fiber α := by
    unfold FiberCond
    simp only [baseScale_objMk]
    exact (h.fiber α).const_mul (ENNReal.ofReal_pos.2 (zero_lt_one.trans_le (ha _))).ne'
      ENNReal.ofReal_ne_top
  tendsto_zero hk hh α z hz hP h0 := by
    refine h.tendsto_zero hk hh α z hz hP ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le)
      fun k => ?_
    refine le_mul_of_one_le_left zero_le ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (ha _)

/-- `|P|(z)` is `|P(e)|` for the representative `e` used by `|N|`. -/
theorem oneBase_eq_π_base_out (z : Q.EOneOrbit) :
    Q.oneBase z = C.toGroupoidStr.π (V.base (Q.oneClass z).out) := by
  unfold oneBase
  conv_lhs => rw [← Quotient.out_eq (Q.oneClass z)]
  rfl

theorem oneNorm_baseScale (a : C.toGroupoidStr.OrbitSpace → ℝ) (N : V.EObj → ℝ≥0∞)
    (z : Q.EOneOrbit) :
    Q.oneNorm (V.baseScale a N) z = ENNReal.ofReal (a (Q.oneBase z)) * Q.oneNorm N z := by
  rw [oneBase_eq_π_base_out]
  rfl

/-- **If `N` and `a(|P|) · N` both satisfy Definition 18.1.7 with continuity, then `a ∘ |P|` is
continuous on `|E_{0,1}|` wherever `|N| ≠ 0`** (`a ∘ |P| = |a(|P|) · N| / |N|` there). -/
theorem IsAuxNormDirect.continuousAt_baseScale {N : V.EObj → ℝ≥0∞} (h₀ : Q.IsAuxNormDirect N)
    {a : C.toGroupoidStr.OrbitSpace → ℝ} (ha : ∀ z, 0 ≤ a z)
    (h : Q.IsAuxNormDirect (V.baseScale a N)) {z₀ : Q.EOneOrbit} (hz₀ : Q.oneNorm N z₀ ≠ 0) :
    ContinuousAt (fun z => a (Q.oneBase z)) z₀ := by
  have hopen : IsOpen {z | Q.oneNorm N z ≠ 0} := isOpen_ne_fun h₀.continuous continuous_const
  have heq : (fun z => (Q.oneNorm (V.baseScale a N) z).toReal / (Q.oneNorm N z).toReal) =ᶠ[𝓝 z₀]
      fun z => a (Q.oneBase z) := by
    filter_upwards [hopen.mem_nhds hz₀] with z hz
    rw [oneNorm_baseScale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (ha _)]
    have : (Q.oneNorm N z).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨hz, h₀.oneNorm_ne_top z⟩
    field_simp
  refine ContinuousAt.congr ?_ heq
  refine ContinuousAt.div ?_ ?_ (ENNReal.toReal_ne_zero.2 ⟨hz₀, h₀.oneNorm_ne_top z₀⟩)
  · exact (ENNReal.continuousAt_toReal (h.oneNorm_ne_top z₀)).comp h.continuous.continuousAt
  · exact (ENNReal.continuousAt_toReal (h₀.oneNorm_ne_top z₀)).comp h₀.continuous.continuousAt

/-- **A factor `a(|P|)` discontinuous at a point of `|E_{0,1}|` where `|N| ≠ 0` breaks the
continuity of Definition 18.1.7**: then `a(|P|) · N` is not an auxiliary norm in the direct
form, i.e. (Lemma 18.1.8) not one in any covering model. -/
theorem IsAuxNormDirect.not_isAuxNormDirect_baseScale {N : V.EObj → ℝ≥0∞}
    (h₀ : Q.IsAuxNormDirect N) {a : C.toGroupoidStr.OrbitSpace → ℝ} (ha : ∀ z, 0 ≤ a z)
    {z₀ : Q.EOneOrbit} (hz₀ : Q.oneNorm N z₀ ≠ 0)
    (hdisc : ¬ ContinuousAt (fun z => a (Q.oneBase z)) z₀) :
    ¬ Q.IsAuxNormDirect (V.baseScale a N) :=
  fun h => hdisc (h₀.continuousAt_baseScale ha h hz₀)

/-- **Lemma 18.1.8 for Definition 18.1.7 as printed, with continuity**: `N ∘ Γ̄_Ψ̄` is an auxiliary norm
in the covering model `c` (Definition 12.2.1) iff `N` satisfies Definition 18.1.7 as printed and
`|N|` is continuous on `|E_{0,1}|` (`lemma_18_1_8`). -/
theorem isAuxNormIn_iff_isAuxNormBook_continuous (c : Q.BundleCoveringFamily)
    {N : V.EObj → ℝ≥0∞} :
    Q.IsAuxNormIn c.Ψ N ↔ Q.IsAuxNormBook N ∧ Continuous (Q.oneNorm N) :=
  (lemma_18_1_8 c).symm.trans
    ⟨fun h => ⟨h.toIsAuxNormBook, h.continuous⟩, fun h => ⟨h.1, h.2⟩⟩

end StrongPolyfoldBundleConstruction

namespace ReflectionBundle

open StrongPolyfoldBundleConstruction PolyfoldConstruction TrivialBundle

/-- **The factor `a`**: `a(|0|) = 1` at the point `|0|` with isotropy `ℤ/2`, `a = 2` elsewhere. -/
def reflJump (z : GCT.reflection.toGroupoidStr.OrbitSpace) : ℝ :=
  2 - ({GCT.reflection.toGroupoidStr.π 0} : Set _).indicator (fun _ => 1) z

theorem reflection_π_ne_π_zero {x : Fin 1 → ℝ} (hx : x ≠ 0) :
    GCT.reflection.toGroupoidStr.π x ≠ GCT.reflection.toGroupoidStr.π 0 := by
  intro h
  obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h
  change φ.2 = x at hs
  change φ.1 • φ.2 = 0 at ht
  rw [hs] at ht
  exact hx ((smul_eq_zero_iff_eq φ.1).1 ht)

theorem reflJump_π_zero : reflJump (GCT.reflection.toGroupoidStr.π 0) = 1 := by
  unfold reflJump
  rw [indicator_of_mem (mem_singleton _)]
  norm_num

theorem reflJump_π_of_ne {x : Fin 1 → ℝ} (hx : x ≠ 0) :
    reflJump (GCT.reflection.toGroupoidStr.π x) = 2 := by
  unfold reflJump
  rw [indicator_of_notMem (show GCT.reflection.toGroupoidStr.π x ∉
    ({GCT.reflection.toGroupoidStr.π 0} : Set _) from fun h => reflection_π_ne_π_zero hx h)]
  norm_num

theorem one_le_reflJump (z : GCT.reflection.toGroupoidStr.OrbitSpace) : 1 ≤ reflJump z := by
  by_cases hz : z ∈ ({GCT.reflection.toGroupoidStr.π 0} : Set _)
  · rw [mem_singleton_iff.1 hz, reflJump_π_zero]
  · unfold reflJump
    rw [indicator_of_notMem hz]
    norm_num

/-- The point `(t, 1)` of `K = ℝ × ℝ`. -/
abbrev reflPathK (t : ℝ) : K := (fun _ => t, fun _ => 1)

theorem reflK_mem_oneSet (k : K) : k ∈ (bundle 1 1).oneSet :=
  ((bundle 1 1).mem_oneSet_iff (c := chart 0) (mem_range_self 0) (mem_univ _)).2
    ((bijective_toBase_const _ 1).2 _)

/-- `t ↦ (t, 1)` is continuous into `K[1]`. -/
theorem continuous_reflPathK_one :
    Continuous fun t : ℝ => (bundle 1 1).oneMk (reflPathK t) (reflK_mem_oneSet _) := by
  change @Continuous _ _ _ (TopologicalSpace.generateFrom _) _
  rw [continuous_generateFrom_iff]
  rintro s ⟨c, ⟨a, rfl⟩, W, hW, rfl⟩
  have hc : Continuous fun t : ℝ => (chart (n := 1) (k := 1) a).liftOne (reflPathK t) := by
    unfold StrongBundleChart.liftOne
    simp only [chart_apply]
    exact ((continuous_pi fun _ => continuous_id).sub continuous_const).prodMk continuous_const
  convert hW.preimage hc using 1
  ext t
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- The point `(t, 1)` of `W[1]` for the model of one copy of `Ψ̄`. -/
abbrev reflModelOne (t : ℝ) : (reflQ.modelSEP reflSingle.Ψ).B.One :=
  (StrongBundle.sigmaOneEquiv fun i => (reflSingle.Ψ i).1.B).symm
    ⟨(), (bundle 1 1).oneMk (reflPathK t) (reflK_mem_oneSet _)⟩

theorem continuous_reflModelOne : Continuous reflModelOne :=
  continuousOn_univ.1 (StrongBundle.isScSmoothMap_sigmaOneEquiv_symm
    (fun i => (reflSingle.Ψ i).1.B)).continuousOn |>.comp
    (continuous_sigmaMk.comp continuous_reflPathK_one)

/-- **The path `t ↦ |(t, 1)|` in `|E_{0,1}|`**. -/
abbrev reflPathOrbit (t : ℝ) : reflQ.EOneOrbit :=
  reflQ.oneHomeomorph reflSingle (Quotient.mk _ (reflModelOne t))

theorem continuous_reflPathOrbit : Continuous reflPathOrbit :=
  (reflQ.oneHomeomorph reflSingle).continuous.comp
    (continuous_quotient_mk'.comp continuous_reflModelOne)

theorem oneBase_reflPathOrbit (t : ℝ) :
    reflQ.oneBase (reflPathOrbit t) = GCT.reflection.toGroupoidStr.π fun _ => t :=
  rfl

theorem isOneObj_reflPath (t : ℝ) : reflQ.IsOneObj (reflV.objMk (fun _ => t) fun _ => 1) :=
  (isOneObj_bundleModelObj_iff reflSingle _).2
    ((reflQ.modelSEP reflSingle.Ψ).B.oneVal_mem (reflModelOne t))

theorem oneNorm_reflPathOrbit {N : reflV.EObj → ℝ≥0∞} (hN : IsMorInvariant N) (t : ℝ) :
    reflQ.oneNorm N (reflPathOrbit t) = N (reflV.objMk (fun _ => t) fun _ => 1) :=
  oneNorm_oneHomeomorph_mk reflSingle hN _

/-- **`a(|P|)` is not continuous on `|E_{0,1}|` at `|(0, 1)|`**: along `|(t, 1)| → |(0, 1)|` it is
`2` for `t ≠ 0` and `1` at `t = 0`. -/
theorem not_continuousAt_reflJump_oneBase :
    ¬ ContinuousAt (fun z => reflJump (reflQ.oneBase z)) (reflPathOrbit 0) := by
  intro hc
  have h1 := (hc.comp (continuous_reflPathOrbit.continuousAt (x := 0))).tendsto
  have e0 : ((fun z => reflJump (reflQ.oneBase z)) ∘ reflPathOrbit) 0 = 1 := by
    simp only [Function.comp_apply, oneBase_reflPathOrbit]
    exact reflJump_π_zero
  rw [e0] at h1
  have h2 : Tendsto ((fun z => reflJump (reflQ.oneBase z)) ∘ reflPathOrbit) (𝓝[≠] 0) (𝓝 2) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Function.comp_apply, oneBase_reflPathOrbit]
    refine (reflJump_π_of_ne fun h => ht ?_).symm
    exact congrFun h 0
  have := tendsto_nhds_unique (tendsto_nhdsWithin_of_tendsto_nhds h1) h2
  norm_num at this

/-- **On the reflection bundle, `a(|P|) · N₀` satisfies Definition 18.1.7 as printed and is not
an auxiliary norm in the direct form**, for every auxiliary norm `N₀` (direct form). -/
theorem isAuxNormBook_reflJump {N₀ : reflV.EObj → ℝ≥0∞} (h₀ : reflQ.IsAuxNormDirect N₀) :
    reflQ.IsAuxNormBook (reflV.baseScale reflJump N₀) ∧
      ¬ reflQ.IsAuxNormDirect (reflV.baseScale reflJump N₀) := by
  refine ⟨h₀.toIsAuxNormBook.baseScale one_le_reflJump, ?_⟩
  refine h₀.not_isAuxNormDirect_baseScale (fun z => zero_le_one.trans (one_le_reflJump z))
    (z₀ := reflPathOrbit 0) ?_ not_continuousAt_reflJump_oneBase
  rw [oneNorm_reflPathOrbit h₀.isMorInvariant]
  intro h0
  have hv := (h₀.fiber (fun _ => 0)).eq_zero (fun _ => 1) (isOneObj_reflPath 0) h0
  exact one_ne_zero (congrFun hv 0)

/-- **Witness**: an auxiliary norm `N₀` (Definition 18.1.7 with continuity) and
`N = a(|P|) · N₀` satisfying Definition 18.1.7 as printed, while `N ∘ Γ̄_Ψ̄` is an auxiliary norm
(Definition 12.2.1) in no covering model. -/
theorem reflQ_baseScale_witness :
    ∃ N₀ : reflV.EObj → ℝ≥0∞, reflQ.IsAuxNormDirect N₀ ∧
      reflQ.IsAuxNormBook (reflV.baseScale reflJump N₀) ∧
      ¬ reflQ.IsAuxNormDirect (reflV.baseScale reflJump N₀) ∧
      ∀ c : reflQ.BundleCoveringFamily, ¬ reflQ.IsAuxNormIn c.Ψ (reflV.baseScale reflJump N₀) := by
  obtain ⟨N₀, h₀⟩ := reflQ_exists_isAuxNormDirect
  obtain ⟨hb, hd⟩ := isAuxNormBook_reflJump h₀
  exact ⟨N₀, h₀, hb, hd, fun c hc => hd ((lemma_18_1_8 c).2 hc)⟩

/-- **Lemma 18.1.8, p. 847, "⇒", for Definition 18.1.7 without the continuity of Definition
12.2.1** (why we read the continuity into Definition 18.1.7, l. 41710): on the reflection bundle
there is `N : E → [0, ∞]` satisfying Definition 18.1.7 as printed (`IsAuxNormBook`) such that
`N ∘ Γ̄_Ψ̄` is an auxiliary norm (Definition 12.2.1) in no covering model, namely `N = a(|P|) · N₀`
with `a = reflJump ∈ {1, 2}` discontinuous at the isotropy point `|0|`.  With the continuity of
Definition 12.2.1 in Definition 18.1.7, as we read it, the lemma holds (`lemma_18_1_8`). -/
theorem lemma_18_1_8_book_without_continuity :
    ¬ ∀ N : reflV.EObj → ℝ≥0∞, reflQ.IsAuxNormBook N →
      ∃ c : reflQ.BundleCoveringFamily, reflQ.IsAuxNormIn c.Ψ N := by
  intro h
  obtain ⟨N₀, -, hb, -, hc⟩ := reflQ_baseScale_witness
  obtain ⟨c, hc'⟩ := h _ hb
  exact hc c hc'

end ReflectionBundle

end GCT.VectorBundle

end Polyfold
