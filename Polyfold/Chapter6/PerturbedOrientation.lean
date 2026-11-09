import Polyfold.Chapter6.OrientationMainClean
import Polyfold.Chapter5.MainTheoremsBookForm
import Polyfold.Chapter6.ProductOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
the last paragraph of the proof of **Theorem 6.6.18** (preprint Theorem 6.41, p. 229), and
§6.7, p. 276, the paragraph before Theorem 6.7.1 (with **Theorem 5.3.10**, preprint
Theorem 5.18).

# The orientation of a perturbation `f + s` inherited from `f` (gap G.69)

## The text, paraphrased

If `f` is not in general position, one takes a small perturbation `s` supported near the zero set
of `f`; then `S_{f+s}` has a natural orientation coming from `o_f`, since `det((f + s)'(x))` is
oriented by `DET(f, x)` for `x ∈ S_{f+s}`.  Before Theorem 6.7.1: by Theorem 5.3.10 there are
such `s` (supported in `U`, `N(s) ≤ 1`) with `(f + s, x)` in general position at every zero, and
`S_{f+s}` is a compact manifold with boundary with corners with the natural orientation induced
from the orientation `o` of `f`.

## What is formalized

* `IsStabKernels.sectionTransfer`, `IsStabKernels.orRay_sectionTransfer`,
  `IsStabKernels.push_sectionTransfer`:
  stabilized kernels of `(g, S_q)` are stabilized kernels of `(g', S'_q)` when
  `g + S_q = g' + S'_q`, and the push-forwards correspond under `Or^g = Or^{g'}`
  (`Lin(g, x) = Lin(g', x)`).
* `IsPush.transfer`: a push-forward of `g = g' + d` (`d` sc⁺) is, conjugated by
  `Or^g = Or^{g'}`, a push-forward of `g'` (datum `S̃ ↦ d̃ + S̃`, `d̃` the `t`-constant lift).
* `HasLocalPropagation.of_sectionAdd`, `IsOrientableNbhd.of_sectionAdd`: orientable
  neighbourhoods of `f + s` are orientable neighbourhoods of `f`.
* `toChartOr_orSectionAdd`: `Or^f = Or^{f+s}` commutes with the change of chart.
* `isSectionOrientation_sectionAdd`, `SectionOrientation.sectionAdd`: **an orientation `o` of
  `f` is an orientation of `f + s`** (Definition 6.6.16), through
  `Or_x^f = Or_x^{f+s}` (`ChartPoint.orSectionAdd`).
* `isNaturalSolutionOrientation`: the natural orientation of the solution set
  (`IsNaturalSolutionOrientation`) holds for every orientation of every tame `f` in general
  position at its zeros; properness and the tameness of `X` are needed only for the manifold
  structure.
* `theorem_6_6_18_perturbation`: **Theorem 5.3.10 with the inherited orientation**: for an
  oriented `f` with compact solution set, the dense set `O` of Theorem 5.3.10 consists of
  perturbations `s` for which `S_{f+s}` is a compact manifold with boundary with corners in
  general position with the natural orientation given by `o.sectionAdd s`.

## What this makes unnecessary

* Gap G.69 (the perturbation paragraph of Theorem 6.6.18): the inherited orientation is an
  orientation of `f + s` in the sense of Definition 6.6.16, not only pointwise
  (`SolutionOrientationCharts.lean` gave `orSectionAdd` and the tangent orientations).
* The hypotheses `hX : PX.IsTame` and `hP : B.IsProper f` of `theorem_6_6_18` for the orientation
  part (`isNaturalSolutionOrientation`).
-/

open Module Bundle Topology Set Filter

noncomputable section

namespace Polyfold

universe u v

/-! ### `congrDetOn` and conjugation -/

section CongrConj

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- The inverse of `congrDetOn h` is `congrDetOn h.symm`. -/
theorem LineOrientation.congrDetOn_symm {C C' : Set (E →L[ℝ] F)} (h : C = C')
    (hC : ∀ T ∈ C, T.IsFredholm) (hC' : ∀ T ∈ C', T.IsFredholm) :
    (LineOrientation.congrDetOn h hC hC').symm = LineOrientation.congrDetOn h.symm hC' hC := by
  subst h
  rfl

/-- Conjugation commutes with `congrDetOn`. -/
theorem LineOrientation.conj_congrDetOn (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F')
    {C₁ C₂ : Set (E →L[ℝ] F)} {C₁' C₂' : Set (E' →L[ℝ] F')} (h : C₁ = C₂) (h' : C₁' = C₂')
    (hC₁ : ∀ T ∈ C₁, T.IsFredholm) (hC₂ : ∀ T ∈ C₂, T.IsFredholm)
    (hC₁' : ∀ T ∈ C₁', T.IsFredholm) (hC₂' : ∀ T ∈ C₂', T.IsFredholm)
    (hmem₁ : ∀ S' ∈ C₁', ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∈ C₁)
    (hmem₂ : ∀ S' ∈ C₂', ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∈ C₂)
    (o : LineOrientation (DetOn C₁ hC₁)) :
    (LineOrientation.congrDetOn h hC₁ hC₂ o).conj (hC' := hC₂') A Γ hmem₂ =
      LineOrientation.congrDetOn h' hC₁' hC₂' (o.conj (hC' := hC₁') A Γ hmem₁) := by
  subst h h'
  rfl

end CongrConj

/-! ### `(f + s) + (−s) = f` -/

section Neg

variable {X : Type u} {Y : Type v} {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]
  [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **`(f + s) + (−1)·s = f`** for sections. -/
lemma sectionAdd_sectionAdd_neg {f s : X → Y} (hf : IsSection P f) (hs : IsSection P s) :
    sectionAdd P (sectionAdd P f s) (sectionSmul P (fun _ => (-1 : ℝ)) s) = f := by
  funext x
  rw [sectionAdd_apply (hf.sectionAdd hs) hs.sectionSmul]
  have hA : (⟨sectionAdd P f s x, (hf.sectionAdd hs) x⟩ : P ⁻¹' {x}) =
      ⟨f x, hf x⟩ + ⟨s x, hs x⟩ := Subtype.ext (sectionAdd_apply hf hs x)
  have h1 : (⟨sectionSmul P (fun _ => (-1 : ℝ)) s x, hs.sectionSmul x⟩ : P ⁻¹' {x}) =
      (-1 : ℝ) • ⟨s x, hs x⟩ := Subtype.ext (sectionSmul_apply (f := fun _ => (-1 : ℝ)) hs x)
  rw [hA, h1, neg_one_smul, add_neg_cancel_right]

end Neg

/-! ### Transfer of stabilized kernels and push-forwards -/

section Transfer

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x)

/-- **`Lin(g, x) = Lin(g', x)`** for `g = g' + d`, `d` an sc⁺-section. -/
theorem linSet_eq_of_sectionAdd {g g' d : X → Y} (hg' : IsSection P g')
    (hd : B.IsScPlusSection d) (hgd : sectionAdd P g' d = g) : p.linSet g = p.linSet g' := by
  rw [← hgd]
  exact p.linSet_sectionAdd hg' hd

/-- `(g + S)'(x) = (g' + S')'(x)` when `g + S = g' + S'`. -/
theorem stabT_congr {g g' S S' : X → Y} (hg : B.IsScFredholmSection g)
    (hg' : B.IsScFredholmSection g') (hS : B.IsScPlusSection S) (hS' : B.IsScPlusSection S')
    (hx : IsZeroAt P (sectionAdd P g S) x) (hx' : IsZeroAt P (sectionAdd P g' S') x)
    (heq : sectionAdd P g S = sectionAdd P g' S') :
    p.stabT hg hS hx = p.stabT hg' hS' hx' :=
  ContinuousLinearMap.ext fun v => Subtype.ext (by rw [coe_stabT, coe_stabT, heq])

/-- **`Or_x^g = Or_x^{g'}`** when `Lin(g, x) = Lin(g', x)` (`congrDetOn`). -/
def orCongr {g g' : X → Y} (hg : B.IsScFredholmSection g) (hg' : B.IsScFredholmSection g')
    (h : p.linSet g = p.linSet g') : p.Or g hg ≃ p.Or g' hg' :=
  LineOrientation.congrDetOn h _ _

/-- `orCongr` does not change the values. -/
theorem orCongr_apply {g g' : X → Y} (hg : B.IsScFredholmSection g)
    (hg' : B.IsScFredholmSection g') (h : p.linSet g = p.linSet g') (o : p.Or g hg)
    {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet g') :
    p.orCongr hg hg' h o ⟨L, hL⟩ = o ⟨L, h ▸ hL⟩ :=
  LineOrientation.congrDetOn_apply h _ _ o hL

/-- The inverse of `orCongr h` is `orCongr h.symm`. -/
theorem orCongr_symm {g g' : X → Y} (hg : B.IsScFredholmSection g)
    (hg' : B.IsScFredholmSection g') (h : p.linSet g = p.linSet g') :
    (p.orCongr hg hg' h).symm = p.orCongr hg' hg h.symm :=
  LineOrientation.congrDetOn_symm h _ _

/-- `orSectionAdd` is `orCongr`. -/
theorem orSectionAdd_eq_orCongr {f s : X → Y} (hf : B.IsScFredholmSection f)
    (hs : B.IsScPlusSection s) (h : p.linSet f = p.linSet (sectionAdd P f s)) :
    p.orSectionAdd hf hs = p.orCongr hf (theorem_3_15 hf hs) h :=
  rfl

/-- `orEquivRay` of `orCongr o` is `orEquivRay` of `o`. -/
theorem orEquivRay_orCongr {g g' : X → Y} (hg : B.IsScFredholmSection g)
    (hg' : B.IsScFredholmSection g') (h : p.linSet g = p.linSet g') {L : ↥p.T →L[ℝ] ↥p.K}
    (hL : L ∈ p.linSet g') (o : p.Or g hg) :
    p.orEquivRay hg' hL (p.orCongr hg hg' h o) = p.orEquivRay hg (h ▸ hL) o :=
  p.orCongr_apply hg hg' h o hL

/-- The last two steps of `orRay` depend on the operator only, and `orCongr` does not change
the value at an operator. -/
theorem stabRay_orCongr_aux {g g' : X → Y} (hg : B.IsScFredholmSection g)
    (hg' : B.IsScFredholmSection g') (h : p.linSet g = p.linSet g') (o : p.Or g hg)
    {T₁ T₂ : ↥p.T →L[ℝ] ↥p.K} (hT : T₁ = T₂) (hT₁ : T₁ ∈ p.linSet g') (hT₂ : T₂ ∈ p.linSet g)
    {k : ℕ} (φ : (Fin k → ℝ) →L[ℝ] ↥p.K) (hs₁ : Function.Surjective (T₁.coprod φ))
    (hs₂ : Function.Surjective (T₂.coprod φ)) {L : Submodule ℝ (p.c.φ.model.E 0 × (Fin k → ℝ))}
    [FiniteDimensional ℝ L]
    (hL₁ : L = (LinearMap.ker ((T₁.coprod φ : _ →L[ℝ] ↥p.K) :
          ↥p.T × (Fin k → ℝ) →ₗ[ℝ] ↥p.K)).map
        (((p.T.subtypeL.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ))) :
          ↥p.T × (Fin k → ℝ) →L[ℝ] p.c.φ.model.E 0 × (Fin k → ℝ)) :
            ↥p.T × (Fin k → ℝ) →ₗ[ℝ] p.c.φ.model.E 0 × (Fin k → ℝ)))
    (hL₂ : L = (LinearMap.ker ((T₂.coprod φ : _ →L[ℝ] ↥p.K) :
          ↥p.T × (Fin k → ℝ) →ₗ[ℝ] ↥p.K)).map
        (((p.T.subtypeL.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ))) :
          ↥p.T × (Fin k → ℝ) →L[ℝ] p.c.φ.model.E 0 × (Fin k → ℝ)) :
            ↥p.T × (Fin k → ℝ) →ₗ[ℝ] p.c.φ.model.E 0 × (Fin k → ℝ))) :
    stabRayEquiv (p.isFredholm_of_mem_linSet hg' _ hT₁) hs₁
        (kerEquivMap p.T.subtypeL Subtype.val_injective hL₁)
        (MulAction.toPerm (stabSign T₁) (p.orEquivRay hg' hT₁ (p.orCongr hg hg' h o))) =
      stabRayEquiv (p.isFredholm_of_mem_linSet hg _ hT₂) hs₂
        (kerEquivMap p.T.subtypeL Subtype.val_injective hL₂)
        (MulAction.toPerm (stabSign T₂) (p.orEquivRay hg hT₂ o)) := by
  subst hT
  exact congrArg (stabRayEquiv _ hs₁ _) (congrArg (MulAction.toPerm (stabSign T₁))
    (p.orEquivRay_orCongr hg hg' h hT₁ o))

variable {f s : X → Y}

/-- **`Or^f = Or^{f+s}` commutes with the change of chart point** (`orTransfer`). -/
theorem orTransfer_orSectionAdd (p' : ChartPoint B x) (hf : B.IsScFredholmSection f)
    (hs : B.IsScPlusSection s) (hx : x ∈ PX.smoothSet) (o : p.Or f hf) :
    p.orTransfer p' (theorem_3_15 hf hs) hx (p.orSectionAdd hf hs o) =
      p'.orSectionAdd hf hs (p.orTransfer p' hf hx o) :=
  LineOrientation.conj_congrDetOn _ _ _ _ _ _ _ _ _ _ o

end ChartPoint

section StabKernels

variable {Q : Type*} [TopologicalSpace Q] {c : StrongBundleChart PX P} {hc : B.IsChart c}
  {y : Q → X} {hy : ∀ q, y q ∈ c.φ.source} {g g' : X → Y} {S S' : Q → X → Y} {k : ℕ}
  {s : Fin k → Q → X → Y} {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}

/-- **Transfer of stabilized kernels**: stabilized kernels of `(g, S_q)` are stabilized kernels of
`(g', S'_q)` when `g + S_q = g' + S'_q` (they depend on the sums only). -/
theorem IsStabKernels.sectionTransfer (hΛ : IsStabKernels g c hc y hy S s Λ)
    (hS' : ∀ q, B.IsScPlusSection (S' q))
    (heq : ∀ q, sectionAdd P g (S q) = sectionAdd P g' (S' q)) :
    IsStabKernels g' c hc y hy S' s Λ where
  isScPlusSection := hS'
  zero q := heq q ▸ hΛ.zero q
  isSection := hΛ.isSection
  exists_lift := hΛ.exists_lift
  spec q _ hq hxc z hz T hT φ hφ :=
    hΛ.spec q hq hxc z hz T (fun v => by rw [heq q]; exact hT v) φ hφ

variable [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]

omit [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q] in
/-- **`orRay` under the transfer**: reading `o ∈ Or^g` in `λ(Λ)` is reading the same orientation,
as an element of `Or^{g'}`, through the transferred kernels. -/
theorem IsStabKernels.orRay_sectionTransfer (hΛ : IsStabKernels g c hc y hy S s Λ)
    (hS' : ∀ q, B.IsScPlusSection (S' q))
    (heq : ∀ q, sectionAdd P g (S q) = sectionAdd P g' (S' q))
    (hg : B.IsScFredholmSection g) (hg' : B.IsScFredholmSection g')
    (hlin : ∀ {x : X} (p : ChartPoint B x), p.linSet g = p.linSet g') (q : Q) {x : X}
    (hq : y q = x) (hx : x ∈ PX.smoothSet) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ x) (o : (chartPt c hc (hq ▸ hy q) z hz).Or g hg) :
    (hΛ.sectionTransfer hS' heq).orRay hg' q hq hx z hz
        ((chartPt c hc (hq ▸ hy q) z hz).orCongr hg hg' (hlin _) o) =
      hΛ.orRay hg q hq hx z hz o := by
  subst hq
  have h0 : IsZeroAt P (sectionAdd P g (S q)) (y q) := hΛ.zero q
  have h0' : IsZeroAt P (sectionAdd P g' (S' q)) (y q) := heq q ▸ hΛ.zero q
  exact (chartPt c hc (hy q) z hz).stabRay_orCongr_aux hg hg' (hlin _) o
    ((chartPt c hc (hy q) z hz).stabT_congr hg' hg (hS' q) (hΛ.isScPlusSection q) h0' h0
      (heq q).symm) _ _ _ _ _ _ _

/-- **The push-forward under the transfer**: `φ'_*(o) = φ_*(o)` under `Or^g = Or^{g'}`. -/
theorem IsStabKernels.push_sectionTransfer (hΛ : IsStabKernels g c hc y hy S s Λ)
    (hS' : ∀ q, B.IsScPlusSection (S' q))
    (heq : ∀ q, sectionAdd P g (S q) = sectionAdd P g' (S' q))
    (hg : B.IsScFredholmSection g) (hg' : B.IsScFredholmSection g')
    (hlin : ∀ {x : X} (p : ChartPoint B x), p.linSet g = p.linSet g') (a b : Q)
    {x₀ x₁ : X} (ha : y a = x₀) (hb : y b = x₁) (hx₀ : x₀ ∈ PX.smoothSet)
    (hx₁ : x₁ ∈ PX.smoothSet) (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁)
    (o : (chartPt c hc (ha ▸ hy a) z₀ hz₀).Or g hg) :
    (hΛ.sectionTransfer hS' heq).push hg' a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁
        ((chartPt c hc (ha ▸ hy a) z₀ hz₀).orCongr hg hg' (hlin _) o) =
      (chartPt c hc (hb ▸ hy b) z₁ hz₁).orCongr hg hg' (hlin _)
        (hΛ.push hg a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ o) := by
  rw [IsStabKernels.push_eq_orRay, IsStabKernels.push_eq_orRay]
  simp only [Equiv.trans_apply]
  rw [hΛ.orRay_sectionTransfer hS' heq hg hg' hlin, Equiv.symm_apply_eq,
    hΛ.orRay_sectionTransfer hS' heq hg hg' hlin, Equiv.apply_symm_apply]

end StabKernels

variable {f s : X → Y}

/-- **`Or_y^f = Or_y^{f+s}` commutes with reading in a chart** (`toChartOr`). -/
theorem toChartOr_orSectionAdd (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSection s) {y : X}
    (hy : y ∈ PX.smoothSet) (o : Orx f hf y hy) (c : StrongBundleChart PX P) (hc : B.IsChart c)
    (hyc : y ∈ c.φ.source) :
    toChartOr (theorem_3_15 hf hs) hy c hc hyc
        ((chartPtOf (orChart B y) (isChart_orChart y) (mem_orChart y) hy).orSectionAdd hf hs o) =
      (chartPtOf c hc hyc hy).orSectionAdd hf hs (toChartOr hf hy c hc hyc o) :=
  ChartPoint.orTransfer_orSectionAdd _ _ hf hs hy o

end Transfer

/-! ### Push-forwards and orientable neighbourhoods of `f` and of `f + s` -/

section Push

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **Transfer of push-forwards**: for `g = g' + d` with `d` an sc⁺-section, a push-forward `e`
of `g` along `γ` is, conjugated by `Or^g = Or^{g'}` (`orCongr`), a push-forward of `g'`: the
datum `S̃` of `g` gives the datum `d̃ + S̃` of `g'` (`d̃` the `t`-constant lift of `d`), with the
same sections `sᵢ` and the same stabilized kernels (`IsStabKernels.sectionTransfer`). -/
theorem IsPush.sectionTransfer {g g' d : X → Y} (hg : B.IsScFredholmSection g)
    (hg' : B.IsScFredholmSection g') (hd : B.IsScPlusSection d) (hgd : sectionAdd P g' d = g)
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {γ : (Fin 1 → ℝ) → X}
    {hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source} {x₀ x₁ : X}
    {h₀ : γ (pt1 0) = x₀} {h₁ : γ (pt1 1) = x₁} {hx₀ : x₀ ∈ c.φ.source}
    {hx₁ : x₁ ∈ c.φ.source} {hs₀ : x₀ ∈ PX.smoothSet} {hs₁ : x₁ ∈ PX.smoothSet}
    {e : (chartPtOf c hc hx₀ hs₀).Or g hg ≃ (chartPtOf c hc hx₁ hs₁).Or g hg}
    (he : IsPush g hg c hc γ hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁ e) :
    IsPush g' hg' c hc γ hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁
      (((chartPtOf c hc hx₀ hs₀).orCongr hg hg'
          ((chartPtOf c hc hx₀ hs₀).linSet_eq_of_sectionAdd hg'.isScSmooth.1 hd hgd)).symm.trans
        (e.trans ((chartPtOf c hc hx₁ hs₁).orCongr hg hg'
          ((chartPtOf c hc hx₁ hs₁).linSet_eq_of_sectionAdd hg'.isScSmooth.1 hd hgd)))) := by
  obtain ⟨S, hS, hz, k, s, hs, Λ, hΛ, rfl⟩ := he
  have hdl := isScPlusSection_constLift (B := B) hd
  have hS' := hdl.add hS
  have hslice : ∀ t : Fin 1 → ℝ,
      pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (constLift d hd.1) S) t =
        sectionAdd P d (pullbackSlice S t) := fun t => by
    rw [pullbackSlice_sectionAdd hdl.1 hS.1, pullbackSlice_constLift]
  have hsum : ∀ t : Fin 1 → ℝ, sectionAdd P g (pullbackSlice S t) =
      sectionAdd P g' (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (constLift d hd.1) S)
        t) := fun t => by
    rw [hslice, ← sectionAdd_assoc hg'.isScSmooth.1 hd.1 (hS.1.pullbackSlice t), hgd]
  have hlin : ∀ {x : X} (p : ChartPoint B x), p.linSet g = p.linSet g' := fun p =>
    p.linSet_eq_of_sectionAdd hg'.isScSmooth.1 hd hgd
  have hSl : ∀ q : Icc (0 : Fin 1 → ℝ) 1, B.IsScPlusSection
      (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (constLift d hd.1) S) q) := fun q => by
    rw [hslice]
    exact hd.add (hΛ.isScPlusSection q)
  have hpl : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) g hg.isScSmooth.1) :=
    isSection_pullbackLift _
  have hpl' : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) g' hg'.isScSmooth.1) :=
    isSection_pullbackLift _
  refine ⟨_, hS', hz.mono fun q hq => ?_, k, s, hs, Λ,
    hΛ.sectionTransfer hSl fun q => hsum q, Equiv.ext fun o' => ?_⟩
  · rw [isZeroAt_pullback_iff_pullbackSlice (hpl'.sectionAdd hS'.1),
      pullbackSlice_sectionAdd_paramLift hg'.isScSmooth.1 hS'.1, ← hsum q,
      ← pullbackSlice_sectionAdd_paramLift hg.isScSmooth.1 hS.1,
      ← isZeroAt_pullback_iff_pullbackSlice (hpl.sectionAdd hS.1)]
    exact hq
  · have h := hΛ.push_sectionTransfer hSl (fun q => hsum q) hg hg' hlin
      ⟨pt1 0, pt1_mem_Icc (left_mem_Icc.2 zero_le_one)⟩
      ⟨pt1 1, pt1_mem_Icc (right_mem_Icc.2 zero_le_one)⟩ h₀ h₁ hs₀ hs₁
      (exists_lift_of_smooth c hx₀ hs₀).choose (exists_lift_of_smooth c hx₀ hs₀).choose_spec
      (exists_lift_of_smooth c hx₁ hs₁).choose (exists_lift_of_smooth c hx₁ hs₁).choose_spec
      (((chartPtOf c hc hx₀ hs₀).orCongr hg hg' (hlin _)).symm o')
    refine h.symm.trans (congrArg _ ?_)
    exact ((chartPtOf c hc hx₀ hs₀).orCongr hg hg' (hlin _)).apply_symm_apply o'

variable {f s : X → Y}

/-- **A push-forward of `f + s` is a push-forward of `f`** under `Or^f = Or^{f+s}`. -/
theorem IsPush.of_sectionAdd (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSection s)
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {γ : (Fin 1 → ℝ) → X}
    {hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source} {x₀ x₁ : X}
    {h₀ : γ (pt1 0) = x₀} {h₁ : γ (pt1 1) = x₁} {hx₀ : x₀ ∈ c.φ.source}
    {hx₁ : x₁ ∈ c.φ.source} {hs₀ : x₀ ∈ PX.smoothSet} {hs₁ : x₁ ∈ PX.smoothSet}
    {e : (chartPtOf c hc hx₀ hs₀).Or (sectionAdd P f s) (theorem_3_15 hf hs) ≃
      (chartPtOf c hc hx₁ hs₁).Or (sectionAdd P f s) (theorem_3_15 hf hs)}
    (he : IsPush (sectionAdd P f s) (theorem_3_15 hf hs) c hc γ hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁ e) :
    IsPush f hf c hc γ hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁
      (((chartPtOf c hc hx₀ hs₀).orSectionAdd hf hs).trans
        (e.trans ((chartPtOf c hc hx₁ hs₁).orSectionAdd hf hs).symm)) := by
  have key := IsPush.sectionTransfer (theorem_3_15 hf hs) hf hs rfl he
  rwa [ChartPoint.orCongr_symm, ← (chartPtOf c hc hx₁ hs₁).orCongr_symm hf (theorem_3_15 hf hs)
    ((chartPtOf c hc hx₁ hs₁).linSet_sectionAdd hf.isScSmooth.1 hs).symm] at key

/-- **A push-forward of `f` is a push-forward of `f + s`** under `Or^f = Or^{f+s}`
(`g' = f + s`, `d = −s`, `sectionAdd_sectionAdd_neg`). -/
theorem IsPush.sectionAdd (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSection s)
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {γ : (Fin 1 → ℝ) → X}
    {hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source} {x₀ x₁ : X}
    {h₀ : γ (pt1 0) = x₀} {h₁ : γ (pt1 1) = x₁} {hx₀ : x₀ ∈ c.φ.source}
    {hx₁ : x₁ ∈ c.φ.source} {hs₀ : x₀ ∈ PX.smoothSet} {hs₁ : x₁ ∈ PX.smoothSet}
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf}
    (he : IsPush f hf c hc γ hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁ e) :
    IsPush (sectionAdd P f s) (theorem_3_15 hf hs) c hc γ hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁
      (((chartPtOf c hc hx₀ hs₀).orSectionAdd hf hs).symm.trans
        (e.trans ((chartPtOf c hc hx₁ hs₁).orSectionAdd hf hs))) :=
  IsPush.sectionTransfer hf (theorem_3_15 hf hs)
    (hs.smul_left (isScSmoothMap_real_const (-1)))
    (sectionAdd_sectionAdd_neg hf.isScSmooth.1 hs.1) he

/-- **The local propagation property of `f + s` gives that of `f`** in the same chart and on
the same set (`IsPush.of_sectionAdd`, `IsPush.sectionAdd`). -/
theorem HasLocalPropagation.of_sectionAdd (hf : B.IsScFredholmSection f)
    (hs : B.IsScPlusSection s) {c : StrongBundleChart PX P} {hc : B.IsChart c} {U : Set X}
    (hU : HasLocalPropagation (sectionAdd P f s) (theorem_3_15 hf hs) c hc U) :
    HasLocalPropagation f hf c hc U where
  subset := hU.subset
  exists_isPush γ hγs hγ _ _ h₀ h₁ hx₀ hx₁ hs₀ hs₁ := by
    obtain ⟨e, he⟩ := hU.exists_isPush γ hγs hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁
    exact ⟨_, he.of_sectionAdd hf hs⟩
  eq γ₀ γ₁ hγ₀s hγ₁s hγ₀ hγ₁ _ _ h₀₀ h₀₁ h₁₀ h₁₁ hx₀ hx₁ hs₀ hs₁ e₀ e₁ he₀ he₁ := by
    have h := hU.eq γ₀ γ₁ hγ₀s hγ₁s hγ₀ hγ₁ h₀₀ h₀₁ h₁₀ h₁₁ hx₀ hx₁ hs₀ hs₁ _ _
      (he₀.sectionAdd hf hs) (he₁.sectionAdd hf hs)
    refine Equiv.ext fun o => ((chartPtOf c hc hx₁ hs₁).orSectionAdd hf hs).injective ?_
    have h' := congrArg (fun e => e ((chartPtOf c hc hx₀ hs₀).orSectionAdd hf hs o)) h
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using h'

/-- **Orientable neighbourhoods of `f + s` are orientable neighbourhoods of `f`.** -/
theorem IsOrientableNbhd.of_sectionAdd (hf : B.IsScFredholmSection f)
    (hs : B.IsScPlusSection s) {c : StrongBundleChart PX P} {hc : B.IsChart c} {U V : Set X}
    {x : X} (hN : IsOrientableNbhd (sectionAdd P f s) (theorem_3_15 hf hs) c hc U V x) :
    IsOrientableNbhd f hf c hc U V x :=
  ⟨hN.hasLocalPropagation.of_sectionAdd hf hs, hN.isOpen_U, hN.isOpen_V, hN.subset, hN.mem,
    hN.path⟩

/-- **Gap G.69: an orientation of `f` is an orientation of `f + s`** (Definition 6.6.16): the
map `y ↦ o_y ∈ Or_y^f = Or_y^{f+s}` is a continuous orientation over every orientable
neighbourhood of `f + s` (an orientable neighbourhood of `f`, `IsOrientableNbhd.of_sectionAdd`;
push-forwards of `f + s` are push-forwards of `f`, `IsPush.of_sectionAdd`). -/
theorem isSectionOrientation_sectionAdd (hf : B.IsScFredholmSection f)
    (hs : B.IsScPlusSection s) {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (ho : IsSectionOrientation f hf o) :
    IsSectionOrientation (sectionAdd P f s) (theorem_3_15 hf hs) fun y hy =>
      (chartPtOf (orChart B y) (isChart_orChart y) (mem_orChart y) hy).orSectionAdd hf hs
        (o y hy) := by
  intro x hx c hc U V hN γ hγs hγ y₁ y₂ hy₁ hy₂ hs₁ hs₂ h₀ h₁ e he
  have key := ho x hx c hc U V (hN.of_sectionAdd hf hs) γ hγs hγ hy₁ hy₂ hs₁ hs₂ h₀ h₁ _
    (he.of_sectionAdd hf hs)
  simp only [restrictOr] at key ⊢
  rw [toChartOr_orSectionAdd, toChartOr_orSectionAdd]
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_eq] at key
  exact key

end Push

/-! ### The orientation of `f + s` and the natural orientation of `S_{f+s}` -/

section Main

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f s : X → Y}

/-- **The orientation of `f + s` inherited from an orientation `o` of `f`** (Theorem 6.6.18, last
paragraph): `y ↦ o_y ∈ Or_y^f = Or_y^{f+s}` (`isSectionOrientation_sectionAdd`). -/
def SectionOrientation.sectionAdd {hf : B.IsScFredholmSection f}
    (o : SectionOrientation f hf) (hs : B.IsScPlusSection s) :
    SectionOrientation (sectionAdd P f s) (theorem_3_15 hf hs) :=
  ⟨fun y hy => (chartPtOf (orChart B y) (isChart_orChart y) (mem_orChart y) hy).orSectionAdd hf hs
    (o.1 y hy), by
    have := paracompactSpace_rn_prod PX
    have := paracompactSpace_rn_pullback B
    exact isSectionOrientation_sectionAdd hf hs o.2⟩

/-- **The natural orientation of the solution set** (`IsNaturalSolutionOrientation`) holds for
every orientation `o` of a tame `f` in general position at its zeros: neither the tameness of
`X` nor properness is used (`tangentOrAt_toChartOr`,
`isLineOrientation_tangentOr_of_isSectionOrientation`). -/
theorem isNaturalSolutionOrientation (hf : B.IsScFredholmSectionTame f)
    (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x)
    (o : SectionOrientation f hf.toIsScFredholmSection) :
    IsNaturalSolutionOrientation f hf hgp o where
  chart_indep x hs hx0 _ _ hc hc' hxc hxc' :=
    tangentOrAt_toChartOr hf.toIsScFredholmSection hs hx0 _ (o.1 x hs) hc hc' hxc hxc'
  continuous := by
    have := paracompactSpace_rn_prod PX
    have := paracompactSpace_rn_pullback B
    exact fun _ hx₀ _ _ _ _ hN γ hγs hγV hγ0 =>
      isLineOrientation_tangentOr_of_isSectionOrientation hf o.2 hx₀ hN hγs hγV hγ0
        fun q hq => hgp (γ q) (hγ0 q hq)

/-- **Theorem 6.6.18 for `f + s`** (the last paragraph of its proof, gap G.69): for an
orientation `o` of `f` and an sc⁺-section `s` with `f + s` proper and in general position at its
zeros, `S_{f+s}` is a compact manifold with boundary with corners in general position with the
natural orientation given by the inherited orientation `o.sectionAdd hs`. -/
theorem theorem_6_6_18_sectionAdd (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    (hs : B.IsScPlusSection s) (hP : B.IsProper (sectionAdd P f s))
    (hgp : ∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x)
    (o : SectionOrientation f hf.toIsScFredholmSection) :
    B.SolutionSetInGeneralPosition (sectionAdd P f s) ∧
      IsNaturalSolutionOrientation (sectionAdd P f s) (theorem_3_15_tame hf hs) hgp
        (o.sectionAdd hs) :=
  theorem_6_6_18 hX (theorem_3_15_tame hf hs) hP hgp (o.sectionAdd hs)

/-- **Theorem 5.3.10 with the inherited orientation** (§6.7, p. 276; gap G.69): for an oriented
tame `f` with compact solution set over a tame M-polyfold with bump functions and an auxiliary
norm `N`, there is an open `U ⊇ S_f` such that `S_{f+s}` is compact for every
`s ∈ Γ^{+,1}_U(P)`, and a dense subset `O ⊆ Γ^{+,1}_U(P)` (in the pointwise reading of
`theorem_5_3_10_2021`) such that for every `s ∈ O`, `S_{f+s}` is a compact manifold with boundary
with corners in general position, with the natural orientation given by the orientation
`o.sectionAdd hs` of `f + s` inherited from `o`. -/
theorem theorem_6_6_18_perturbation (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) (o : SectionOrientation f hf.toIsScFredholmSection) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∃ O ⊆ B.allowableSections N U,
        (∀ (s' : X → Y) (hs' : B.IsScPlusSection s'), s' ∈ B.allowableSections N U → ∀ ε > 0,
          ∃ (s : X → Y) (hs : B.IsScPlusSection s), s ∈ O ∧ ∀ x, B.sectionDistAt N hs hs' x ≤ ε) ∧
        ∀ (s : X → Y) (hs : B.IsScPlusSection s), s ∈ O →
          ∃ hgp : ∀ x, IsZeroAt P (sectionAdd P f s) x →
              B.IsGeneralPositionGerm (sectionAdd P f s) x,
            B.SolutionSetInGeneralPosition (sectionAdd P f s) ∧
              IsNaturalSolutionOrientation (sectionAdd P f s) (theorem_3_15_tame hf hs) hgp
                (o.sectionAdd hs) := by
  obtain ⟨U, hUo, hSU, hcpt, hdense⟩ := theorem_5_18_dense hX hbump hf hS hN
  refine ⟨U, hUo, hSU, hcpt,
    {s | s ∈ B.allowableSections N U ∧ B.SolutionSetInGeneralPosition (sectionAdd P f s)},
    fun s hs => hs.1, fun s' hs' hs'alw ε hε => ?_, fun s hs hsO =>
      ⟨hsO.2.2.1, hsO.2, isNaturalSolutionOrientation _ _ _⟩⟩
  obtain ⟨s, hs, halw, hd, hgp⟩ := hdense s' hs' hs'alw ε hε
  exact ⟨s, hs, ⟨halw, hgp⟩, hd⟩

end Main

end Polyfold
