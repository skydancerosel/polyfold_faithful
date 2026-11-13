import Polyfold.Chapter15.ProductEpBundle
import Polyfold.Chapter8.Book2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), §15.3, products remark after
**Definition 15.3.3** (pp. 692–693; 2017: after Definition 15.3): the auxiliary norm
`N × N' = max(N, N')` of the product (gap G.160 (d), first part).

# The product auxiliary norm

## What is formalized

* `StrongBundle.prodOneFiberFst`, `prodOneFiberSnd`, `prodOneFiberMk`: the fibre
  `((W × W')_{0,1})_{(x, x')} ≅ (W_{0,1})_x × (W'_{0,1})_{x'}`.
* `StrongBundle.prodAuxNorm N N'` (`(N × N')(w, w') = max(N(w), N'(w'))`) and
  `StrongBundle.isAuxNorm_prodAuxNorm` (Definition 5.1.1 (preprint 5.1): it is an auxiliary norm
  of `W × W'` if `N`, `N'` are auxiliary norms).
* `EpStrongBundle.isAuxNorm_prodAuxNorm` (Definition 8.3.5 (2021): also the `μ × μ'`-invariance).
-/

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u v u' v'

namespace StrongBundle

section PartOne

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  [ParacompactSpace (X × X')] [ParacompactSpace (Y × Y')]
  (B : StrongBundle PX P) (B' : StrongBundle PX' P')

/-- The first component of a vector of `((W × W')_{0,1})_{(x, x')}`. -/
def prodOneFiberFst {p : X × X'} (v : (B.prod B').oneFiber p) : B.oneFiber p.1 :=
  ⟨(prodFiberCLE P P' p v).1, ((B.mem_oneSet_prod B').1 v.2).1⟩

/-- The second component of a vector of `((W × W')_{0,1})_{(x, x')}`. -/
def prodOneFiberSnd {p : X × X'} (v : (B.prod B').oneFiber p) : B'.oneFiber p.2 :=
  ⟨(prodFiberCLE P P' p v).2, ((B.mem_oneSet_prod B').1 v.2).2⟩

/-- The vector `(a, b)` of `((W × W')_{0,1})_{(x, x')}`. -/
def prodOneFiberMk {p : X × X'} (a : B.oneFiber p.1) (b : B'.oneFiber p.2) :
    (B.prod B').oneFiber p :=
  ⟨(prodFiberCLE P P' p).symm ((a : P ⁻¹' {p.1}), (b : P' ⁻¹' {p.2})),
    (B.mem_oneSet_prod B').2 ⟨a.2, b.2⟩⟩

variable {B B'}

@[simp] lemma prodOneFiberFst_mk {p : X × X'} (a : B.oneFiber p.1) (b : B'.oneFiber p.2) :
    B.prodOneFiberFst B' (B.prodOneFiberMk B' a b) = a := rfl

@[simp] lemma prodOneFiberSnd_mk {p : X × X'} (a : B.oneFiber p.1) (b : B'.oneFiber p.2) :
    B.prodOneFiberSnd B' (B.prodOneFiberMk B' a b) = b := rfl

lemma prodOneFiberMk_fst_snd {p : X × X'} (v : (B.prod B').oneFiber p) :
    B.prodOneFiberMk B' (B.prodOneFiberFst B' v) (B.prodOneFiberSnd B' v) = v := rfl

lemma prodOneFiber_ext {p : X × X'} {v w : (B.prod B').oneFiber p}
    (h₁ : B.prodOneFiberFst B' v = B.prodOneFiberFst B' w)
    (h₂ : B.prodOneFiberSnd B' v = B.prodOneFiberSnd B' w) : v = w := by
  rw [← prodOneFiberMk_fst_snd v, ← prodOneFiberMk_fst_snd w, h₁, h₂]

lemma prodOneFiberFst_add {p : X × X'} (v w : (B.prod B').oneFiber p) :
    B.prodOneFiberFst B' (v + w) = B.prodOneFiberFst B' v + B.prodOneFiberFst B' w :=
  Subtype.ext (congrArg Prod.fst ((prodFiberCLE P P' p).map_add v.1 w.1))

lemma prodOneFiberSnd_add {p : X × X'} (v w : (B.prod B').oneFiber p) :
    B.prodOneFiberSnd B' (v + w) = B.prodOneFiberSnd B' v + B.prodOneFiberSnd B' w :=
  Subtype.ext (congrArg Prod.snd ((prodFiberCLE P P' p).map_add v.1 w.1))

lemma prodOneFiberFst_sub {p : X × X'} (v w : (B.prod B').oneFiber p) :
    B.prodOneFiberFst B' (v - w) = B.prodOneFiberFst B' v - B.prodOneFiberFst B' w :=
  Subtype.ext (congrArg Prod.fst ((prodFiberCLE P P' p).map_sub v.1 w.1))

lemma prodOneFiberSnd_sub {p : X × X'} (v w : (B.prod B').oneFiber p) :
    B.prodOneFiberSnd B' (v - w) = B.prodOneFiberSnd B' v - B.prodOneFiberSnd B' w :=
  Subtype.ext (congrArg Prod.snd ((prodFiberCLE P P' p).map_sub v.1 w.1))

lemma prodOneFiberFst_smul {p : X × X'} (t : ℝ) (v : (B.prod B').oneFiber p) :
    B.prodOneFiberFst B' (t • v) = t • B.prodOneFiberFst B' v :=
  Subtype.ext (congrArg Prod.fst ((prodFiberCLE P P' p).map_smul t v.1))

lemma prodOneFiberSnd_smul {p : X × X'} (t : ℝ) (v : (B.prod B').oneFiber p) :
    B.prodOneFiberSnd B' (t • v) = t • B.prodOneFiberSnd B' v :=
  Subtype.ext (congrArg Prod.snd ((prodFiberCLE P P' p).map_smul t v.1))

lemma prodOneFiberFst_zero {p : X × X'} : B.prodOneFiberFst B' (0 : (B.prod B').oneFiber p) = 0 :=
  Subtype.ext (congrArg Prod.fst ((prodFiberCLE P P' p).map_zero))

lemma prodOneFiberSnd_zero {p : X × X'} : B.prodOneFiberSnd B' (0 : (B.prod B').oneFiber p) = 0 :=
  Subtype.ext (congrArg Prod.snd ((prodFiberCLE P P' p).map_zero))

lemma prodOneHomeomorph_toOne_fst {p : X × X'} (v : (B.prod B').oneFiber p) :
    (B.prodOneHomeomorph B' ((B.prod B').toOne v)).1 = B.toOne (B.prodOneFiberFst B' v) := rfl

lemma prodOneHomeomorph_toOne_snd {p : X × X'} (v : (B.prod B').oneFiber p) :
    (B.prodOneHomeomorph B' ((B.prod B').toOne v)).2 = B'.toOne (B.prodOneFiberSnd B' v) := rfl

variable (B B')

/-- **The product auxiliary norm** `(N × N')(w, w') = max(N(w), N'(w'))` on `(W × W')_{0,1}`
(the text's `N × N'`, p. 692). -/
def prodAuxNorm (N : B.One → ℝ) (N' : B'.One → ℝ) (w : (B.prod B').One) : ℝ :=
  max (N (B.prodOneHomeomorph B' w).1) (N' (B.prodOneHomeomorph B' w).2)

variable {B B'}

lemma prodAuxNorm_toOne (N : B.One → ℝ) (N' : B'.One → ℝ) {p : X × X'}
    (v : (B.prod B').oneFiber p) :
    B.prodAuxNorm B' N N' ((B.prod B').toOne v) =
      max (N (B.toOne (B.prodOneFiberFst B' v))) (N' (B'.toOne (B.prodOneFiberSnd B' v))) := rfl

/-- **`N × N'` is an auxiliary norm** (Definition 5.1.1 (preprint 5.1)) of the product strong
bundle when `N` and `N'` are auxiliary norms. -/
theorem isAuxNorm_prodAuxNorm {N : B.One → ℝ} {N' : B'.One → ℝ} (hN : B.IsAuxNorm N)
    (hN' : B'.IsAuxNorm N') : (B.prod B').IsAuxNorm (B.prodAuxNorm B' N N') where
  continuous :=
    (hN.continuous.comp (continuous_fst.comp (B.prodOneHomeomorph B').continuous)).max
      (hN'.continuous.comp (continuous_snd.comp (B.prodOneHomeomorph B').continuous))
  fiber p := by
    have f₁ := hN.fiber p.1
    have f₂ := hN'.fiber p.2
    refine ⟨fun v hv => ?_, fun t v => ?_, fun v w => ?_, fun u hu => ?_⟩
    · rw [prodAuxNorm_toOne] at hv
      have n₁ := f₁.nonneg (B.prodOneFiberFst B' v)
      have n₂ := f₂.nonneg (B.prodOneFiberSnd B' v)
      have z₁ := f₁.eq_zero _ (le_antisymm (hv ▸ le_max_left _ _) n₁)
      have z₂ := f₂.eq_zero _ (le_antisymm (hv ▸ le_max_right _ _) n₂)
      exact prodOneFiber_ext (z₁.trans prodOneFiberFst_zero.symm)
        (z₂.trans prodOneFiberSnd_zero.symm)
    · rw [prodAuxNorm_toOne, prodAuxNorm_toOne, prodOneFiberFst_smul, prodOneFiberSnd_smul,
        f₁.smul, f₂.smul, mul_max_of_nonneg _ _ (abs_nonneg t)]
    · rw [prodAuxNorm_toOne, prodAuxNorm_toOne, prodAuxNorm_toOne, prodOneFiberFst_add,
        prodOneFiberSnd_add]
      refine max_le ((f₁.add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
        ((f₂.add_le _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _)))
    · have hc₁ : ∀ ε > 0, ∃ n, ∀ m ≥ n, ∀ k ≥ n,
          N (B.toOne (B.prodOneFiberFst B' (u m) - B.prodOneFiberFst B' (u k))) < ε :=
        fun ε hε => (hu ε hε).imp fun n hn m hm k hk => by
          have := hn m hm k hk
          rw [prodAuxNorm_toOne, prodOneFiberFst_sub] at this
          exact (le_max_left _ _).trans_lt this
      have hc₂ : ∀ ε > 0, ∃ n, ∀ m ≥ n, ∀ k ≥ n,
          N' (B'.toOne (B.prodOneFiberSnd B' (u m) - B.prodOneFiberSnd B' (u k))) < ε :=
        fun ε hε => (hu ε hε).imp fun n hn m hm k hk => by
          have := hn m hm k hk
          rw [prodAuxNorm_toOne, prodOneFiberSnd_sub] at this
          exact (le_max_right _ _).trans_lt this
      obtain ⟨a, ha⟩ := f₁.complete _ hc₁
      obtain ⟨b, hb⟩ := f₂.complete _ hc₂
      refine ⟨B.prodOneFiberMk B' a b, ?_⟩
      have h := ha.max hb
      rw [max_self] at h
      refine h.congr fun k => ?_
      rw [prodAuxNorm_toOne, prodOneFiberFst_sub, prodOneFiberSnd_sub, prodOneFiberFst_mk,
        prodOneFiberSnd_mk]
  tendsto_zeroOne w x hP hN₀ := by
    have hP₁ : Tendsto (fun k => P (B.oneVal (B.prodOneHomeomorph B' (w k)).1)) atTop
        (𝓝 x.1) := (continuous_fst.tendsto x).comp hP
    have hP₂ : Tendsto (fun k => P' (B'.oneVal (B.prodOneHomeomorph B' (w k)).2)) atTop
        (𝓝 x.2) := (continuous_snd.tendsto x).comp hP
    have hz₁ : Tendsto (fun k => N (B.prodOneHomeomorph B' (w k)).1) atTop (𝓝 0) :=
      squeeze_zero (fun k => hN.nonneg _) (fun k => le_max_left _ _) hN₀
    have hz₂ : Tendsto (fun k => N' (B.prodOneHomeomorph B' (w k)).2) atTop (𝓝 0) :=
      squeeze_zero (fun k => hN'.nonneg _) (fun k => le_max_right _ _) hN₀
    have h := (hN.tendsto_zeroOne _ x.1 hP₁ hz₁).prodMk_nhds (hN'.tendsto_zeroOne _ x.2 hP₂ hz₂)
    have h' := ((B.prodOneHomeomorph B').symm.continuous.tendsto _).comp h
    exact h'

end PartOne

end StrongBundle

namespace EpStrongBundle

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Obj' Mor' : Type u'} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  [ParacompactSpace (Obj × Obj')] [ParacompactSpace (Mor × Mor')]
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {W' : Type v'} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  [ParacompactSpace (W × W')]
  {B : StrongBundle X.PObj P} {B' : StrongBundle X'.PObj P'}
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}

/-- **`N × N'` is an auxiliary norm of `(W × W', μ × μ')`** (Definition 8.3.5 (2021), p. 379;
the text's `N × N'` after Definition 15.3.3, p. 692). -/
theorem isAuxNorm_prodAuxNorm {N : B.One → ℝ} {N' : B'.One → ℝ} (hN : E.IsAuxNorm N)
    (hN' : E'.IsAuxNorm N') : (E.prod E').IsAuxNorm (B.prodAuxNorm B' N N') where
  isAuxNorm := StrongBundle.isAuxNorm_prodAuxNorm hN.isAuxNorm hN'.isAuxNorm
  map_μ h k φ hk hμ := by
    have e₁ := hN.map_μ (B.prodOneHomeomorph B' h).1 (B.prodOneHomeomorph B' k).1 φ.1
      (congrArg Prod.fst hk) (congrArg Prod.fst hμ)
    have e₂ := hN'.map_μ (B.prodOneHomeomorph B' h).2 (B.prodOneHomeomorph B' k).2 φ.2
      (congrArg Prod.snd hk) (congrArg Prod.snd hμ)
    change max _ _ = max _ _
    rw [e₁, e₂]

end EpStrongBundle

end Polyfold
