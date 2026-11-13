import Polyfold.Chapter12.MorphismIso
import Polyfold.Chapter6.OrientationMainClean
import Polyfold.Chapter10.EquivalenceZhou

/-!
# §12.5 The action of morphisms on `Lin(f, x)` and on orientations (Lemma 12.5.1)

HWZ 2021, §12.5, pp. 592–593 (2017: §12.5, Lemma 12.2).  `(P : W → X, μ)` is a strong bundle
over an ep-groupoid and `f` an sc-Fredholm section functor.  For a morphism `φ : x → x'` between
smooth objects the text defines `φ_* S = μ(φ, S ∘ (Tφ)⁻¹)` on `Lin(f, x)`.

Reading.  `Lin(f, x)`, `T_xX` and `W_x` are read as in Part I, in a chart point at `x`
(`ChartPoint`, `linSet`); `Or_x^f = Orx` is read in the chosen chart point `orPt`.  The map `φ`
is realized by the local strong bundle isomorphism `E.morIso φ` of the sheet of `φ`
(`MorphismIso`), and a chart at `x` inside the sheet is carried to a chart at `x'`
(`LocalIso.pullPt`).  Then `Tφ = morTx` and `μ(φ, ·) = morKx` are the identifications of Part I
from the chosen chart point at `x` to the carried one and from there to the chosen chart point
at `x'`; `φ_* = linMor`.  Part I's `Lin(f, x) ≠ ∅` needs sc⁺-sections through smooth fibre
points (`hsec`), a consequence of bump functions
(`MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough`).

* Generic part (`StrongBundle.LocalIso`): `orPull`, `morT`/`morK`, `orVia` (the orientation map
  of a local isomorphism through an intermediate chart point), `orVia_apply` (it is a
  conjugation), `morT_eq`/`orVia_eq` (independent of the intermediate chart point), `morT_comp`
  (composition for local isomorphisms with the same germ).
* `morTx_comp`, `morTx_unit`, `morTx_inv` and the fibre forms: `T(ψφ) = Tψ Tφ`, `T(1) = Id`.
* `lemma_12_5_1_one`, `lemma_12_5_1_two`, `lemma_12_5_1_three_unit`, `lemma_12_5_1_three_comp`:
  **Lemma 12.5.1 (1)–(3)**.
* `orMor`: `φ_*` on orientations (p. 593), with `orMor_comp`, `orMor_unit`, `orMor_inv`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr

universe u v

/-! ### Carrying orientations along a local isomorphism -/

namespace StrongBundle.LocalIso

section OrVia

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {U U' : Set X} (L : LocalIso B B U U') {x x' : X}

/-- The identity of `T_zO` from a chart point to its carried chart point. -/
abbrev castT (a : ChartPoint B x) (ha : a.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x) :
    ↥a.T ≃L[ℝ] ↥(L.pullPt a ha hx' hϕ).T :=
  ContinuousLinearEquiv.refl ℝ ↥a.T

/-- The identity of `K_z` from a chart point to its carried chart point. -/
abbrev castK (a : ChartPoint B x) (ha : a.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x) :
    ↥a.K ≃L[ℝ] ↥(L.pullPt a ha hx' hϕ).K :=
  ContinuousLinearEquiv.refl ℝ ↥a.K

variable {L} in
theorem castT_mem {a : ChartPoint B x} {ha : a.c.φ.source ⊆ U'} {hx' : x' ∈ U} {hϕ : L.ϕ x' = x}
    (hlin : (L.pullPt a ha hx' hϕ).linSet f = a.linSet f) :
    ∀ S ∈ (L.pullPt a ha hx' hϕ).linSet f, (((L.castK a ha hx' hϕ).symm :
      ↥(L.pullPt a ha hx' hϕ).K →L[ℝ] ↥a.K) ∘L S ∘L (L.castT a ha hx' hϕ : ↥a.T →L[ℝ] _)) ∈
        a.linSet f := fun S hS => by
  rw [← hlin]; exact hS

variable {L} in
theorem castT_mem_symm {a : ChartPoint B x} {ha : a.c.φ.source ⊆ U'} {hx' : x' ∈ U}
    {hϕ : L.ϕ x' = x} (hlin : (L.pullPt a ha hx' hϕ).linSet f = a.linSet f) :
    ∀ S ∈ a.linSet f, ((((L.castK a ha hx' hϕ).symm.symm : ↥a.K →L[ℝ]
      ↥(L.pullPt a ha hx' hϕ).K)) ∘L S ∘L ((L.castT a ha hx' hϕ).symm :
        ↥(L.pullPt a ha hx' hϕ).T →L[ℝ] ↥a.T)) ∈ (L.pullPt a ha hx' hϕ).linSet f :=
  fun S hS => by rw [hlin]; exact hS

/-- **`Or_x^f` read in a chart point and in the carried chart point**: the two sets `Lin(f, ·)`
coincide (`linSet_pullPt`), so an orientation is carried unchanged. -/
def orPull (hf : B.IsScFredholmSection f) (a : ChartPoint B x) (ha : a.c.φ.source ⊆ U')
    (hx' : x' ∈ U) (hϕ : L.ϕ x' = x) (hlin : (L.pullPt a ha hx' hϕ).linSet f = a.linSet f) :
    a.Or f hf ≃ (L.pullPt a ha hx' hϕ).Or f hf where
  toFun o := o.conj (hC' := (L.pullPt a ha hx' hϕ).isFredholm_of_mem_linSet hf)
    (L.castT a ha hx' hϕ) (L.castK a ha hx' hϕ) (castT_mem hlin)
  invFun o := o.conj (hC' := a.isFredholm_of_mem_linSet hf)
    (L.castT a ha hx' hϕ).symm (L.castK a ha hx' hϕ).symm (castT_mem_symm hlin)
  left_inv o := (LineOrientation.conj_trans
    (hC' := (L.pullPt a ha hx' hϕ).isFredholm_of_mem_linSet hf)
    (hC'' := a.isFredholm_of_mem_linSet hf) _ _ _ _ (castT_mem hlin) (castT_mem_symm hlin)
    (conj_mem_trans _ _ _ _ (castT_mem hlin) (castT_mem_symm hlin)) o).trans
    ((LineOrientation.conj_congr (hC' := a.isFredholm_of_mem_linSet hf)
      (A₂ := ContinuousLinearEquiv.refl ℝ ↥a.T) (Γ₂ := ContinuousLinearEquiv.refl ℝ ↥a.K)
      (fun _ => rfl) (fun _ => rfl) _ (conj_mem_refl _) o).trans (LineOrientation.conj_refl _ o))
  right_inv o := (LineOrientation.conj_trans (hC' := a.isFredholm_of_mem_linSet hf)
    (hC'' := (L.pullPt a ha hx' hϕ).isFredholm_of_mem_linSet hf) _ _ _ _ (castT_mem_symm hlin)
    (castT_mem hlin) (conj_mem_trans _ _ _ _ (castT_mem_symm hlin) (castT_mem hlin)) o).trans
    ((LineOrientation.conj_congr (hC' := (L.pullPt a ha hx' hϕ).isFredholm_of_mem_linSet hf)
      (A₂ := ContinuousLinearEquiv.refl ℝ ↥(L.pullPt a ha hx' hϕ).T)
      (Γ₂ := ContinuousLinearEquiv.refl ℝ ↥(L.pullPt a ha hx' hϕ).K)
      (fun _ => rfl) (fun _ => rfl) _ (conj_mem_refl _) o).trans (LineOrientation.conj_refl _ o))

/-- **The map `T_xX → T_{x'}X` of `L` read in chart points `q` at `x` and `q'` at `x'`**, through
a chart point `a` at `x` inside `U'`: `D(τ ∘ r)` from `q` to `a`, the identity to the carried
chart point, and `D(τ ∘ r)` from it to `q'`. -/
def morT (q : ChartPoint B x) (q' : ChartPoint B x') (a : ChartPoint B x) (ha : a.c.φ.source ⊆ U')
    (hx' : x' ∈ U) (hϕ : L.ϕ x' = x) : ↥q.T ≃L[ℝ] ↥q'.T :=
  ((q.transferT a).trans (L.castT a ha hx' hϕ)).trans ((L.pullPt a ha hx' hϕ).transferT q')

/-- **The map `Y_x → Y_{x'}` of `L`** read in chart points, as `morT`. -/
def morK (q : ChartPoint B x) (q' : ChartPoint B x') (a : ChartPoint B x) (ha : a.c.φ.source ⊆ U')
    (hx' : x' ∈ U) (hϕ : L.ϕ x' = x) : ↥q.K ≃L[ℝ] ↥q'.K :=
  ((q.transferK a).trans (L.castK a ha hx' hϕ)).trans ((L.pullPt a ha hx' hϕ).transferK q')

theorem morT_apply (q : ChartPoint B x) (q' : ChartPoint B x') (a : ChartPoint B x)
    (ha : a.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x) (v : ↥q.T) :
    L.morT q q' a ha hx' hϕ v = (L.pullPt a ha hx' hϕ).transferT q' (q.transferT a v) := rfl

theorem morK_apply (q : ChartPoint B x) (q' : ChartPoint B x') (a : ChartPoint B x)
    (ha : a.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x) (k : ↥q.K) :
    L.morK q q' a ha hx' hϕ k = (L.pullPt a ha hx' hϕ).transferK q' (q.transferK a k) := rfl

variable {L} in
/-- The hypothesis of `LineOrientation.conj` for `morT`, `morK`. -/
theorem morT_mem (hf : B.IsScFredholmSection f) {q : ChartPoint B x} {q' : ChartPoint B x'}
    {a : ChartPoint B x} {ha : a.c.φ.source ⊆ U'} {hx' : x' ∈ U} {hϕ : L.ϕ x' = x}
    (hlin : (L.pullPt a ha hx' hϕ).linSet f = a.linSet f) (hxs : x ∈ PX.smoothSet)
    (hx's : x' ∈ PX.smoothSet) :
    ∀ S' ∈ q'.linSet f, (((L.morK q q' a ha hx' hϕ).symm : ↥q'.K →L[ℝ] ↥q.K) ∘L S' ∘L
      (L.morT q q' a ha hx' hϕ : ↥q.T →L[ℝ] ↥q'.T)) ∈ q.linSet f :=
  conj_mem_trans _ _ _ _ (conj_mem_trans _ _ _ _ (q.transfer_mem_linSet a hf hxs) (castT_mem hlin))
    ((L.pullPt a ha hx' hϕ).transfer_mem_linSet q' hf hx's)

/-- **The orientation map of `L` read in chart points**: `orTransfer` from `q` to `a`, `orPull`,
and `orTransfer` from the carried chart point to `q'`. -/
def orVia (hf : B.IsScFredholmSection f) (q : ChartPoint B x) (q' : ChartPoint B x')
    (a : ChartPoint B x) (ha : a.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x)
    (hlin : (L.pullPt a ha hx' hϕ).linSet f = a.linSet f) (hxs : x ∈ PX.smoothSet)
    (hx's : x' ∈ PX.smoothSet) : q.Or f hf ≃ q'.Or f hf :=
  (q.orTransfer a hf hxs).trans ((L.orPull hf a ha hx' hϕ hlin).trans
    ((L.pullPt a ha hx' hϕ).orTransfer q' hf hx's))

/-- **`orVia` is the conjugation by `morT` and `morK`.** -/
theorem orVia_apply (hf : B.IsScFredholmSection f) (q : ChartPoint B x) (q' : ChartPoint B x')
    (a : ChartPoint B x) (ha : a.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x)
    (hlin : (L.pullPt a ha hx' hϕ).linSet f = a.linSet f) (hxs : x ∈ PX.smoothSet)
    (hx's : x' ∈ PX.smoothSet) (o : q.Or f hf) :
    L.orVia hf q q' a ha hx' hϕ hlin hxs hx's o =
      o.conj (hC' := q'.isFredholm_of_mem_linSet hf) (L.morT q q' a ha hx' hϕ)
        (L.morK q q' a ha hx' hϕ) (morT_mem hf hlin hxs hx's) := by
  have e1 := LineOrientation.conj_trans (hC' := a.isFredholm_of_mem_linSet hf)
    (hC'' := (L.pullPt a ha hx' hϕ).isFredholm_of_mem_linSet hf) _ _ _ _
    (q.transfer_mem_linSet a hf hxs) (castT_mem hlin)
    (conj_mem_trans _ _ _ _ (q.transfer_mem_linSet a hf hxs) (castT_mem hlin)) o
  have e2 := LineOrientation.conj_trans
    (hC' := (L.pullPt a ha hx' hϕ).isFredholm_of_mem_linSet hf)
    (hC'' := q'.isFredholm_of_mem_linSet hf) _ _ _ _
    (conj_mem_trans _ _ _ _ (q.transfer_mem_linSet a hf hxs) (castT_mem hlin))
    ((L.pullPt a ha hx' hϕ).transfer_mem_linSet q' hf hx's) (morT_mem hf hlin hxs hx's) o
  exact (congrArg (fun o' => LineOrientation.conj (hC' := q'.isFredholm_of_mem_linSet hf) _ _
    ((L.pullPt a ha hx' hϕ).transfer_mem_linSet q' hf hx's) o') e1).trans e2

/-- **`morT` does not depend on the intermediate chart point.** -/
theorem morT_eq (q : ChartPoint B x) (q' : ChartPoint B x') {a b : ChartPoint B x}
    (ha : a.c.φ.source ⊆ U') (hb : b.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x)
    (v : ↥q.T) : L.morT q q' a ha hx' hϕ v = L.morT q q' b hb hx' hϕ v := by
  rw [morT_apply, morT_apply, ← q.transferT_trans_apply a b v]
  set w : ↥(L.pullPt a ha hx' hϕ).T := q.transferT a v
  have h1 := ((L.pullPt a ha hx' hϕ).transferT_trans_apply (L.pullPt b hb hx' hϕ) q' w).symm
  have h2 : (L.pullPt a ha hx' hϕ).transferT (L.pullPt b hb hx' hϕ) w =
      (a.transferT b w : ↥(L.pullPt b hb hx' hϕ).T) :=
    Subtype.ext (transferT_pullPt L ha hb hx' hϕ w)
  exact h1.trans (congrArg ((L.pullPt b hb hx' hϕ).transferT q') h2)

/-- **`morK` does not depend on the intermediate chart point.** -/
theorem morK_eq (q : ChartPoint B x) (q' : ChartPoint B x') {a b : ChartPoint B x}
    (ha : a.c.φ.source ⊆ U') (hb : b.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x)
    (k : ↥q.K) : L.morK q q' a ha hx' hϕ k = L.morK q q' b hb hx' hϕ k := by
  rw [morK_apply, morK_apply, ← q.transferK_trans_apply a b k]
  set w : ↥(L.pullPt a ha hx' hϕ).K := q.transferK a k
  have h1 := ((L.pullPt a ha hx' hϕ).transferK_trans_apply (L.pullPt b hb hx' hϕ) q' w).symm
  have h2 : (L.pullPt a ha hx' hϕ).transferK (L.pullPt b hb hx' hϕ) w =
      (a.transferK b w : ↥(L.pullPt b hb hx' hϕ).K) :=
    Subtype.ext (transferK_pullPt L ha hb hx' hϕ w)
  exact h1.trans (congrArg ((L.pullPt b hb hx' hϕ).transferK q') h2)

/-- **`orVia` does not depend on the intermediate chart point.** -/
theorem orVia_eq (hf : B.IsScFredholmSection f) (q : ChartPoint B x) (q' : ChartPoint B x')
    {a b : ChartPoint B x} (ha : a.c.φ.source ⊆ U') (hb : b.c.φ.source ⊆ U') (hx' : x' ∈ U)
    (hϕ : L.ϕ x' = x) (hla : (L.pullPt a ha hx' hϕ).linSet f = a.linSet f)
    (hlb : (L.pullPt b hb hx' hϕ).linSet f = b.linSet f) (hxs : x ∈ PX.smoothSet)
    (hx's : x' ∈ PX.smoothSet) :
    L.orVia hf q q' a ha hx' hϕ hla hxs hx's = L.orVia hf q q' b hb hx' hϕ hlb hxs hx's :=
  Equiv.ext fun o => by
    rw [orVia_apply, orVia_apply]
    exact LineOrientation.conj_congr (L.morT_eq q q' ha hb hx' hϕ) (L.morK_eq q q' ha hb hx' hϕ)
      _ _ o

/-- **Composing the maps of `L` and `L₂` is the map of `L₃`** when `L ∘ L₂` and `L₃` have the
same germ at `x''`: read through `a` and its carried chart point. -/
theorem morT_comp {U₂ U₂' U₃ U₃' : Set X} {L₂ : LocalIso B B U₂ U₂'} {L₃ : LocalIso B B U₃ U₃'}
    {x'' : X} (q : ChartPoint B x) (q' : ChartPoint B x') (q'' : ChartPoint B x'')
    (a : ChartPoint B x) (h₁ : a.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x)
    (h₂ : (L.pullPt a h₁ hx' hϕ).c.φ.source ⊆ U₂') (hx'' : x'' ∈ U₂) (hϕ₂ : L₂.ϕ x'' = x')
    (h₃ : a.c.φ.source ⊆ U₃') (hx''₃ : x'' ∈ U₃) (hϕ₃ : L₃.ϕ x'' = x)
    (hG : GermAgree L L₂ L₃ x'') (v : ↥q.T) :
    L₂.morT q' q'' (L.pullPt a h₁ hx' hϕ) h₂ hx'' hϕ₂ (L.morT q q' a h₁ hx' hϕ v) =
      L₃.morT q q'' a h₃ hx''₃ hϕ₃ v := by
  rw [morT_apply, morT_apply, morT_apply]
  have h1 := ((L.pullPt a h₁ hx' hϕ).transferT_trans_apply q' (L.pullPt a h₁ hx' hϕ)
    (q.transferT a v)).trans ((L.pullPt a h₁ hx' hϕ).transferT_self_apply (q.transferT a v))
  have h2 : (L₃.pullPt a h₃ hx''₃ hϕ₃).transferT
      (L₂.pullPt (L.pullPt a h₁ hx' hϕ) h₂ hx'' hϕ₂) (q.transferT a v) = q.transferT a v :=
    Subtype.ext (transferT_pullPt_pullPt a hx' hϕ h₁ h₂ hx'' hϕ₂ h₃ hx''₃ hϕ₃ hG _)
  rw [h1]
  exact (congrArg ((L₂.pullPt (L.pullPt a h₁ hx' hϕ) h₂ hx'' hϕ₂).transferT q'') h2).symm.trans
    (ChartPoint.transferT_trans_apply _ _ _ _)

/-- The fibre form of `morT_comp`. -/
theorem morK_comp {U₂ U₂' U₃ U₃' : Set X} {L₂ : LocalIso B B U₂ U₂'} {L₃ : LocalIso B B U₃ U₃'}
    {x'' : X} (q : ChartPoint B x) (q' : ChartPoint B x') (q'' : ChartPoint B x'')
    (a : ChartPoint B x) (h₁ : a.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x)
    (h₂ : (L.pullPt a h₁ hx' hϕ).c.φ.source ⊆ U₂') (hx'' : x'' ∈ U₂) (hϕ₂ : L₂.ϕ x'' = x')
    (h₃ : a.c.φ.source ⊆ U₃') (hx''₃ : x'' ∈ U₃) (hϕ₃ : L₃.ϕ x'' = x)
    (hG : GermAgree L L₂ L₃ x'') (k : ↥q.K) :
    L₂.morK q' q'' (L.pullPt a h₁ hx' hϕ) h₂ hx'' hϕ₂ (L.morK q q' a h₁ hx' hϕ k) =
      L₃.morK q q'' a h₃ hx''₃ hϕ₃ k := by
  rw [morK_apply, morK_apply, morK_apply]
  have h1 := ((L.pullPt a h₁ hx' hϕ).transferK_trans_apply q' (L.pullPt a h₁ hx' hϕ)
    (q.transferK a k)).trans ((L.pullPt a h₁ hx' hϕ).transferK_self_apply (q.transferK a k))
  have h2 : (L₃.pullPt a h₃ hx''₃ hϕ₃).transferK
      (L₂.pullPt (L.pullPt a h₁ hx' hϕ) h₂ hx'' hϕ₂) (q.transferK a k) = q.transferK a k :=
    Subtype.ext (transferK_pullPt_pullPt a hx' hϕ h₁ h₂ hx'' hϕ₂ h₃ hx''₃ hϕ₃ hG _)
  rw [h1]
  exact (congrArg ((L₂.pullPt (L.pullPt a h₁ hx' hϕ) h₂ hx'' hϕ₂).transferK q'') h2).symm.trans
    (ChartPoint.transferK_trans_apply _ _ _ _)

end OrVia

end StrongBundle.LocalIso

/-! ### The action of a morphism on `Lin(f, x)` and on `Or_x^f` -/

section Mor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

variable (B) in
/-- The chosen chart point at a smooth `x` (the one `Orx` is read in). -/
abbrev orPt (x : Obj) (hs : x ∈ X.PObj.smoothSet) : ChartPoint B x :=
  chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hs

variable (B) in
/-- The chosen chart at `x` restricted to `V ∩ dom`, as a chart point at a smooth `x ∈ V`. -/
def restrPt (x : Obj) {V : Set Obj} (hV : IsOpen V) (hxV : x ∈ V)
    (hs : x ∈ X.PObj.smoothSet) : ChartPoint B x :=
  chartPtOf ((orChart B x).restrict (s := (orChart B x).φ.source ∩ V) inter_subset_left
    ((orChart B x).φ.isOpen_source.inter hV)) ((isChart_orChart x).restrict _ _)
    ⟨mem_orChart x, hxV⟩ hs

theorem restrPt_sub (x : Obj) {V : Set Obj} (hV : IsOpen V) (hxV : x ∈ V)
    (hs : x ∈ X.PObj.smoothSet) : (restrPt B x hV hxV hs).c.φ.source ⊆ V :=
  fun _ hw => hw.2

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- An sc-Fredholm section functor is functorial (the first half of the definition). -/
theorem functorial_of_isScFredholmSectionFunctor (hF : E.IsScFredholmSectionFunctor f) :
    E.IsFunctorialSection hF.2.isScSmooth.1 := by
  obtain ⟨⟨_, h⟩, _⟩ := hF
  exact h

omit [ParacompactSpace (pullbackSpace P X.src)] in
theorem mem_tgtSet {σ : Mor} {x' : Obj} (hx' : X.tgt σ = x') : x' ∈ (X.sheetAt σ).tgtSet :=
  hx' ▸ tgt_mem_morIso σ

omit [ParacompactSpace (pullbackSpace P X.src)] in
theorem mem_srcSet {σ : Mor} {x : Obj} (hx : X.src σ = x) : x ∈ (X.sheetAt σ).srcSet :=
  hx ▸ src_mem_morIso σ

omit [ParacompactSpace (pullbackSpace P X.src)] in
theorem isOpen_srcSet (σ : Mor) : IsOpen (X.sheetAt σ).srcSet :=
  (X.sheetAt σ).isScDiffeoOn_src.isOpen_target

theorem morIso_ϕ_eq {σ : Mor} {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x') :
    (E.morIso σ).ϕ x' = x := by
  subst hx hx'; exact E.morIso_ϕ_tgt σ

/-- `Lin(f, ·)` in a chart point inside `s(sheet)` and in its carried chart point coincide. -/
theorem linSet_pullPt_mor (hF : E.IsScFredholmSectionFunctor f)
    (hsec : B.HasScPlusSectionsThrough) (σ : Mor) {x x' : Obj} (hx : X.src σ = x)
    (hx' : X.tgt σ = x') (a : ChartPoint B x) (ha : a.c.φ.source ⊆ (X.sheetAt σ).srcSet)
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    ((E.morIso σ).pullPt a ha (mem_tgtSet hx') (E.morIso_ϕ_eq hx hx')).linSet f = a.linSet f :=
  StrongBundle.LocalIso.linSet_pullPt hF.2
    (E.eqOn_morIso σ _ (E.functorial_of_isScFredholmSectionFunctor hF)) hsec hs hs'

/-- **`Tφ : T_xX → T_{x'}X`** for a morphism `σ : x → x'`, read in the chosen chart points
(through the chosen chart at `x` restricted to `s(sheet)`). -/
def morTx (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    ↥(orPt B x hs).T ≃L[ℝ] ↥(orPt B x' hs').T :=
  (E.morIso σ).morT (orPt B x hs) (orPt B x' hs')
    (restrPt B x (isOpen_srcSet σ) (mem_srcSet hx) hs) (restrPt_sub _ _ _ _) (mem_tgtSet hx')
    (E.morIso_ϕ_eq hx hx')

/-- **`μ(σ, ·) : W_x → W_{x'}`** for a morphism `σ : x → x'`, read in the chosen chart points. -/
def morKx (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    ↥(orPt B x hs).K ≃L[ℝ] ↥(orPt B x' hs').K :=
  (E.morIso σ).morK (orPt B x hs) (orPt B x' hs')
    (restrPt B x (isOpen_srcSet σ) (mem_srcSet hx) hs) (restrPt_sub _ _ _ _) (mem_tgtSet hx')
    (E.morIso_ϕ_eq hx hx')

theorem morTx_eq (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (a : ChartPoint B x)
    (ha : a.c.φ.source ⊆ (X.sheetAt σ).srcSet) (v : ↥(orPt B x hs).T) :
    E.morTx σ hx hx' hs hs' v = (E.morIso σ).morT (orPt B x hs) (orPt B x' hs') a ha
      (mem_tgtSet hx') (E.morIso_ϕ_eq hx hx') v :=
  (E.morIso σ).morT_eq _ _ _ _ _ _ v

theorem morKx_eq (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (a : ChartPoint B x)
    (ha : a.c.φ.source ⊆ (X.sheetAt σ).srcSet) (k : ↥(orPt B x hs).K) :
    E.morKx σ hx hx' hs hs' k = (E.morIso σ).morK (orPt B x hs) (orPt B x' hs') a ha
      (mem_tgtSet hx') (E.morIso_ϕ_eq hx hx') k :=
  (E.morIso σ).morK_eq _ _ _ _ _ _ k

theorem morTx_congr {σ σ' : Mor} (h : σ = σ') {x x' : Obj} (hx : X.src σ = x)
    (hx' : X.tgt σ = x') (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (v) :
    E.morTx σ hx hx' hs hs' v = E.morTx σ' (h ▸ hx) (h ▸ hx') hs hs' v := by
  subst h; rfl

theorem morKx_congr {σ σ' : Mor} (h : σ = σ') {x x' : Obj} (hx : X.src σ = x)
    (hx' : X.tgt σ = x') (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (k) :
    E.morKx σ hx hx' hs hs' k = E.morKx σ' (h ▸ hx) (h ▸ hx') hs hs' k := by
  subst h; rfl

/-! #### Composition -/

section Comp

variable {φ ψ : Mor} {x y z : Obj} (hφx : X.src φ = x) (hφy : X.tgt φ = y) (hψy : X.src ψ = y)
  (hψz : X.tgt ψ = z)

include hφx hφy hψy in
omit [ParacompactSpace (pullbackSpace P X.src)] in
theorem src_comp_eq : X.src (X.comp ψ φ) = x :=
  (X.src_comp ψ φ (hψy.trans hφy.symm)).trans hφx

include hφy hψy hψz in
omit [ParacompactSpace (pullbackSpace P X.src)] in
theorem tgt_comp_eq : X.tgt (X.comp ψ φ) = z :=
  (X.tgt_comp ψ φ (hψy.trans hφy.symm)).trans hψz

/-- The open set `s(sheet φ) ∩ s(sheet ψφ) ∩ g_φ⁻¹(s(sheet ψ))` around `x`. -/
def compSet (φ ψ : Mor) : Set Obj :=
  (X.sheetAt φ).srcSet ∩ (X.sheetAt (X.comp ψ φ)).srcSet ∩
    ((X.sheetAt φ).srcSet ∩ (E.morIso φ).g ⁻¹' (X.sheetAt ψ).srcSet)

theorem isOpen_compSet (φ ψ : Mor) : IsOpen (E.compSet φ ψ) :=
  ((isOpen_srcSet φ).inter (isOpen_srcSet _)).inter
    ((E.morIso φ).base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage (isOpen_srcSet φ)
      (isOpen_srcSet ψ))

include hφx hφy hψy in
theorem mem_compSet : x ∈ E.compSet φ ψ := by
  refine ⟨⟨mem_srcSet hφx, mem_srcSet (src_comp_eq hφx hφy hψy)⟩, mem_srcSet hφx, ?_⟩
  change (E.morIso φ).g x ∈ (X.sheetAt ψ).srcSet
  rw [← E.morIso_ϕ_eq hφx hφy, (E.morIso φ).base.left_inv _ (mem_tgtSet hφy)]
  exact mem_srcSet hψy

/-- **`T(ψ ∘ φ) = Tψ ∘ Tφ`** in the chosen chart points. -/
theorem morTx_comp (hs : x ∈ X.PObj.smoothSet) (hs' : y ∈ X.PObj.smoothSet)
    (hs'' : z ∈ X.PObj.smoothSet) (v : ↥(orPt B x hs).T) :
    E.morTx ψ hψy hψz hs' hs'' (E.morTx φ hφx hφy hs hs' v) =
      E.morTx (X.comp ψ φ) (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hs hs'' v := by
  have hxC := E.mem_compSet hφx hφy hψy (ψ := ψ)
  have haφ : (restrPt B x (E.isOpen_compSet φ ψ) hxC hs).c.φ.source ⊆ (X.sheetAt φ).srcSet :=
    fun w hw => (restrPt_sub x (E.isOpen_compSet φ ψ) hxC hs hw).1.1
  have haC : (restrPt B x (E.isOpen_compSet φ ψ) hxC hs).c.φ.source ⊆
      (X.sheetAt (X.comp ψ φ)).srcSet := fun w hw =>
    (restrPt_sub x (E.isOpen_compSet φ ψ) hxC hs hw).1.2
  have hbψ : ((E.morIso φ).pullPt (restrPt B x (E.isOpen_compSet φ ψ) hxC hs) haφ
      (mem_tgtSet hφy) (E.morIso_ϕ_eq hφx hφy)).c.φ.source ⊆ (X.sheetAt ψ).srcSet :=
    fun w hw => by
      have h1 : (E.morIso φ).g ((E.morIso φ).ϕ w) ∈ (X.sheetAt ψ).srcSet :=
        (restrPt_sub x (E.isOpen_compSet φ ψ) hxC hs hw.2).2.2
      rwa [(E.morIso φ).base.left_inv w hw.1] at h1
  rw [E.morTx_eq φ hφx hφy hs hs' _ haφ, E.morTx_eq ψ hψy hψz hs' hs'' _ hbψ,
    E.morTx_eq _ _ _ hs hs'' _ haC]
  exact StrongBundle.LocalIso.morT_comp _ _ _ _ _ _ _ _ hbψ _ _ haC _ _
    (hψz ▸ E.germAgree_morIso_comp (hψy.trans hφy.symm)) v

/-- **`μ(ψ ∘ φ, ·) = μ(ψ, ·) ∘ μ(φ, ·)`** in the chosen chart points. -/
theorem morKx_comp (hs : x ∈ X.PObj.smoothSet) (hs' : y ∈ X.PObj.smoothSet)
    (hs'' : z ∈ X.PObj.smoothSet) (k : ↥(orPt B x hs).K) :
    E.morKx ψ hψy hψz hs' hs'' (E.morKx φ hφx hφy hs hs' k) =
      E.morKx (X.comp ψ φ) (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hs hs'' k := by
  have hxC := E.mem_compSet hφx hφy hψy (ψ := ψ)
  have haφ : (restrPt B x (E.isOpen_compSet φ ψ) hxC hs).c.φ.source ⊆ (X.sheetAt φ).srcSet :=
    fun w hw => (restrPt_sub x (E.isOpen_compSet φ ψ) hxC hs hw).1.1
  have haC : (restrPt B x (E.isOpen_compSet φ ψ) hxC hs).c.φ.source ⊆
      (X.sheetAt (X.comp ψ φ)).srcSet := fun w hw =>
    (restrPt_sub x (E.isOpen_compSet φ ψ) hxC hs hw).1.2
  have hbψ : ((E.morIso φ).pullPt (restrPt B x (E.isOpen_compSet φ ψ) hxC hs) haφ
      (mem_tgtSet hφy) (E.morIso_ϕ_eq hφx hφy)).c.φ.source ⊆ (X.sheetAt ψ).srcSet :=
    fun w hw => by
      have h1 : (E.morIso φ).g ((E.morIso φ).ϕ w) ∈ (X.sheetAt ψ).srcSet :=
        (restrPt_sub x (E.isOpen_compSet φ ψ) hxC hs hw.2).2.2
      rwa [(E.morIso φ).base.left_inv w hw.1] at h1
  rw [E.morKx_eq φ hφx hφy hs hs' _ haφ, E.morKx_eq ψ hψy hψz hs' hs'' _ hbψ,
    E.morKx_eq _ _ _ hs hs'' _ haC]
  exact StrongBundle.LocalIso.morK_comp _ _ _ _ _ _ _ _ hbψ _ _ haC _ _
    (hψz ▸ E.germAgree_morIso_comp (hψy.trans hφy.symm)) k

end Comp


/-! #### Units and inverses -/

omit [ParacompactSpace (pullbackSpace P X.src)] in
theorem comp_unit_unit (x : Obj) : X.comp (X.unit x) (X.unit x) = X.unit x := by
  have h := X.comp_unit (X.unit x)
  rwa [X.src_unit] at h

/-- **`T(1_x) = Id`**. -/
theorem morTx_unit {σ : Mor} {x : Obj} (h : σ = X.unit x) (hx : X.src σ = x) (hx' : X.tgt σ = x)
    (hs : x ∈ X.PObj.smoothSet) (v : ↥(orPt B x hs).T) : E.morTx σ hx hx' hs hs v = v := by
  subst h
  have key := E.morTx_comp hx hx' hx hx' hs hs hs v
  rw [E.morTx_congr (comp_unit_unit x)] at key
  exact (E.morTx (X.unit x) hx hx' hs hs).injective key

/-- **`μ(1_x, ·) = Id`**. -/
theorem morKx_unit {σ : Mor} {x : Obj} (h : σ = X.unit x) (hx : X.src σ = x) (hx' : X.tgt σ = x)
    (hs : x ∈ X.PObj.smoothSet) (k : ↥(orPt B x hs).K) : E.morKx σ hx hx' hs hs k = k := by
  subst h
  have key := E.morKx_comp hx hx' hx hx' hs hs hs k
  rw [E.morKx_congr (comp_unit_unit x)] at key
  exact (E.morKx (X.unit x) hx hx' hs hs).injective key

/-- **`T(φ⁻¹) ∘ Tφ = Id`**. -/
theorem morTx_inv {φ : Mor} {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (v : ↥(orPt B x hs).T) :
    E.morTx (X.inv φ) ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) hs' hs
      (E.morTx φ hx hx' hs hs' v) = v :=
  (E.morTx_comp hx hx' ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) hs hs' hs v).trans
    (E.morTx_unit ((X.inv_comp φ).trans (congrArg X.unit hx)) _ _ hs v)

/-- **`μ(φ⁻¹, ·) ∘ μ(φ, ·) = Id`**. -/
theorem morKx_inv {φ : Mor} {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (k : ↥(orPt B x hs).K) :
    E.morKx (X.inv φ) ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) hs' hs
      (E.morKx φ hx hx' hs hs' k) = k :=
  (E.morKx_comp hx hx' ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) hs hs' hs k).trans
    (E.morKx_unit ((X.inv_comp φ).trans (congrArg X.unit hx)) _ _ hs k)

theorem morTx_inv_eq_symm {φ : Mor} {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (v : ↥(orPt B x' hs').T) :
    E.morTx (X.inv φ) ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) hs' hs v =
      (E.morTx φ hx hx' hs hs').symm v := by
  conv_lhs => rw [← (E.morTx φ hx hx' hs hs').apply_symm_apply v]
  exact E.morTx_inv hx hx' hs hs' _

theorem morKx_inv_eq_symm {φ : Mor} {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (k : ↥(orPt B x' hs').K) :
    E.morKx (X.inv φ) ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) hs' hs k =
      (E.morKx φ hx hx' hs hs').symm k := by
  conv_lhs => rw [← (E.morKx φ hx hx' hs hs').apply_symm_apply k]
  exact E.morKx_inv hx hx' hs hs' _

/-! #### The action on `Lin(f, x)` (Lemma 12.5.1) -/

section Action

variable (hF : E.IsScFredholmSectionFunctor f) (hsec : B.HasScPlusSectionsThrough)

include hF hsec in
/-- The conjugate `μ(σ, ·)⁻¹ ∘ S' ∘ Tσ` of a member of `Lin(f, x')` is a member of `Lin(f, x)`. -/
theorem morTx_mem (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    ∀ S' ∈ (orPt B x' hs').linSet f, (((E.morKx σ hx hx' hs hs').symm :
      ↥(orPt B x' hs').K →L[ℝ] ↥(orPt B x hs).K) ∘L S' ∘L
        (E.morTx σ hx hx' hs hs' : ↥(orPt B x hs).T →L[ℝ] ↥(orPt B x' hs').T)) ∈
          (orPt B x hs).linSet f :=
  StrongBundle.LocalIso.morT_mem hF.2 (E.linSet_pullPt_mor hF hsec σ hx hx' _ _ hs hs') hs hs'

/-- **`φ_* S = μ(φ, ·) ∘ S ∘ (Tφ)⁻¹`** (p. 592), read in the chosen chart points. -/
def linMor (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet)
    (S : ↥(orPt B x hs).T →L[ℝ] ↥(orPt B x hs).K) : ↥(orPt B x' hs').T →L[ℝ] ↥(orPt B x' hs').K :=
  (E.morKx σ hx hx' hs hs' : ↥(orPt B x hs).K →L[ℝ] ↥(orPt B x' hs').K) ∘L S ∘L
    ((E.morTx σ hx hx' hs hs').symm : ↥(orPt B x' hs').T →L[ℝ] ↥(orPt B x hs).T)

theorem linMor_apply (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet)
    (S : ↥(orPt B x hs).T →L[ℝ] ↥(orPt B x hs).K) (v : ↥(orPt B x' hs').T) :
    E.linMor σ hx hx' hs hs' S v = E.morKx σ hx hx' hs hs' (S ((E.morTx σ hx hx' hs hs').symm v)) :=
  rfl

include hF hsec in
/-- **Lemma 12.5.1 (1)**, p. 592 (2017: Lemma 12.2 (1)): for a morphism `φ : x → x'` between
smooth points and `S ∈ Lin(f, x)`, `φ_* S ∈ Lin(f, x')`.  Here `f` is an sc-Fredholm section
functor and `Lin` is read in the chosen chart points (Part I, Definition 6.2.1); `hsec`
(sc⁺-sections through smooth fibre points) is Part I's standing hypothesis for `Lin(f, x) ≠ ∅`. -/
theorem lemma_12_5_1_one (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet)
    {S : ↥(orPt B x hs).T →L[ℝ] ↥(orPt B x hs).K} (hS : S ∈ (orPt B x hs).linSet f) :
    E.linMor σ hx hx' hs hs' S ∈ (orPt B x' hs').linSet f := by
  have h := E.morTx_mem hF hsec (X.inv σ) ((X.src_inv σ).trans hx') ((X.tgt_inv σ).trans hx)
    hs' hs S hS
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  change E.morKx σ hx hx' hs hs' (S ((E.morTx σ hx hx' hs hs').symm v)) =
    (E.morKx (X.inv σ) ((X.src_inv σ).trans hx') ((X.tgt_inv σ).trans hx) hs' hs).symm
      (S (E.morTx (X.inv σ) ((X.src_inv σ).trans hx') ((X.tgt_inv σ).trans hx) hs' hs v))
  rw [E.morTx_inv_eq_symm hx hx' hs hs', ContinuousLinearEquiv.eq_symm_apply,
    E.morKx_inv_eq_symm hx hx' hs hs', ContinuousLinearEquiv.symm_apply_apply]

/-- `φ_*` is injective (it is the conjugation by two isomorphisms). -/
theorem linMor_injective (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    Function.Injective (E.linMor σ hx hx' hs hs') := fun S₁ S₂ h =>
  ContinuousLinearMap.ext fun v => by
    have h1 := DFunLike.congr_fun h (E.morTx σ hx hx' hs hs' v)
    rw [linMor_apply, linMor_apply, ContinuousLinearEquiv.symm_apply_apply] at h1
    exact (E.morKx σ hx hx' hs hs').injective h1

include hF hsec in
/-- **Lemma 12.5.1 (2)**, p. 592 (2017: Lemma 12.2 (2)): `φ_* : Lin(f, x) → Lin(f, x')` is a
bijection. -/
theorem lemma_12_5_1_two (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    Set.BijOn (E.linMor σ hx hx' hs hs') ((orPt B x hs).linSet f) ((orPt B x' hs').linSet f) := by
  refine ⟨fun S hS => E.lemma_12_5_1_one hF hsec σ hx hx' hs hs' hS,
    (E.linMor_injective σ hx hx' hs hs').injOn, fun S' hS' => ?_⟩
  refine ⟨_, E.morTx_mem hF hsec σ hx hx' hs hs' S' hS', ContinuousLinearMap.ext fun v => ?_⟩
  change E.morKx σ hx hx' hs hs' ((E.morKx σ hx hx' hs hs').symm
    (S' (E.morTx σ hx hx' hs hs' ((E.morTx σ hx hx' hs hs').symm v)))) = S' v
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- `(1_x)_*` read with `1_x : x → x`. -/
theorem src_unit_eq (x : Obj) : X.src (X.unit x) = x := X.src_unit x

/-- **Lemma 12.5.1 (3), units**, p. 592 (2017: Lemma 12.2 (3)): `(1_x)_* = Id_{Lin(f, x)}`. -/
theorem lemma_12_5_1_three_unit (x : Obj) (hs : x ∈ X.PObj.smoothSet)
    (S : ↥(orPt B x hs).T →L[ℝ] ↥(orPt B x hs).K) :
    E.linMor (X.unit x) (X.src_unit x) (X.tgt_unit x) hs hs S = S :=
  ContinuousLinearMap.ext fun v => by
    rw [linMor_apply, E.morKx_unit rfl]
    congr 1
    rw [ContinuousLinearEquiv.symm_apply_eq, E.morTx_unit rfl]

/-- **Lemma 12.5.1 (3), composition**, p. 592 (2017: Lemma 12.2 (3)): `(ψ ∘ φ)_* = ψ_* ∘ φ_*`
for `s(ψ) = t(φ)`. -/
theorem lemma_12_5_1_three_comp {φ ψ : Mor} {x y z : Obj} (hφx : X.src φ = x) (hφy : X.tgt φ = y)
    (hψy : X.src ψ = y) (hψz : X.tgt ψ = z) (hs : x ∈ X.PObj.smoothSet)
    (hs' : y ∈ X.PObj.smoothSet) (hs'' : z ∈ X.PObj.smoothSet)
    (S : ↥(orPt B x hs).T →L[ℝ] ↥(orPt B x hs).K) :
    E.linMor (X.comp ψ φ) (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hs hs'' S =
      E.linMor ψ hψy hψz hs' hs'' (E.linMor φ hφx hφy hs hs' S) :=
  ContinuousLinearMap.ext fun v => by
    rw [linMor_apply, linMor_apply, linMor_apply, E.morKx_comp hφx hφy hψy hψz hs hs' hs'']
    congr 2
    rw [ContinuousLinearEquiv.symm_apply_eq, ← E.morTx_comp hφx hφy hψy hψz hs hs' hs'',
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]


/-! #### The action on orientations -/

/-- **`φ_* : Or_x^f → Or_{x'}^f`** (p. 593): an orientation `o` of `DET(f, x)` goes to
`φ_* S ↦ φ_* (o(S))`.  Read in the chosen chart points, it is the conjugation of Part I by
`Tφ` and `μ(φ, ·)` (`orMor_apply`). -/
def orMor (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    Orx f hF.2 x hs ≃ Orx f hF.2 x' hs' :=
  (E.morIso σ).orVia hF.2 (orPt B x hs) (orPt B x' hs')
    (restrPt B x (isOpen_srcSet σ) (mem_srcSet hx) hs) (restrPt_sub _ _ _ _) (mem_tgtSet hx')
    (E.morIso_ϕ_eq hx hx') (E.linSet_pullPt_mor hF hsec σ hx hx' _ _ hs hs') hs hs'

/-- **`φ_*` is the conjugation by `Tφ` and `μ(φ, ·)`**: `(φ_* o)(φ_* S) = conjDet (o(S))`. -/
theorem orMor_apply (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (o : Orx f hF.2 x hs) :
    E.orMor hF hsec σ hx hx' hs hs' o =
      o.conj (hC' := (orPt B x' hs').isFredholm_of_mem_linSet hF.2) (E.morTx σ hx hx' hs hs')
        (E.morKx σ hx hx' hs hs') (E.morTx_mem hF hsec σ hx hx' hs hs') :=
  StrongBundle.LocalIso.orVia_apply _ _ _ _ _ _ _ _ _ _ _ o

theorem orMor_congr {σ σ' : Mor} (h : σ = σ') {x x' : Obj} (hx : X.src σ = x)
    (hx' : X.tgt σ = x') (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    E.orMor hF hsec σ hx hx' hs hs' = E.orMor hF hsec σ' (h ▸ hx) (h ▸ hx') hs hs' := by
  subst h; rfl

/-- **`(ψ ∘ φ)_* = ψ_* ∘ φ_*` on orientations.** -/
theorem orMor_comp {φ ψ : Mor} {x y z : Obj} (hφx : X.src φ = x) (hφy : X.tgt φ = y)
    (hψy : X.src ψ = y) (hψz : X.tgt ψ = z) (hs : x ∈ X.PObj.smoothSet)
    (hs' : y ∈ X.PObj.smoothSet) (hs'' : z ∈ X.PObj.smoothSet) :
    (E.orMor hF hsec φ hφx hφy hs hs').trans (E.orMor hF hsec ψ hψy hψz hs' hs'') =
      E.orMor hF hsec (X.comp ψ φ) (src_comp_eq hφx hφy hψy) (tgt_comp_eq hφy hψy hψz) hs hs'' :=
  Equiv.ext fun o => by
    rw [Equiv.trans_apply, orMor_apply, orMor_apply, orMor_apply]
    exact (LineOrientation.conj_trans (hC' := (orPt B y hs').isFredholm_of_mem_linSet hF.2)
      (hC'' := (orPt B z hs'').isFredholm_of_mem_linSet hF.2) _ _ _ _
      (E.morTx_mem hF hsec φ hφx hφy hs hs') (E.morTx_mem hF hsec ψ hψy hψz hs' hs'')
      (conj_mem_trans _ _ _ _ (E.morTx_mem hF hsec φ hφx hφy hs hs')
        (E.morTx_mem hF hsec ψ hψy hψz hs' hs'')) o).trans
      (LineOrientation.conj_congr (hC' := (orPt B z hs'').isFredholm_of_mem_linSet hF.2)
        (fun v => E.morTx_comp hφx hφy hψy hψz hs hs' hs'' v)
        (fun k => E.morKx_comp hφx hφy hψy hψz hs hs' hs'' k) _ _ o)

/-- **`(1_x)_* = Id` on orientations.** -/
theorem orMor_unit {σ : Mor} {x : Obj} (h : σ = X.unit x) (hx : X.src σ = x) (hx' : X.tgt σ = x)
    (hs : x ∈ X.PObj.smoothSet) : E.orMor hF hsec σ hx hx' hs hs = Equiv.refl _ :=
  Equiv.ext fun o => by
    rw [orMor_apply]
    exact (LineOrientation.conj_congr (hC' := (orPt B x hs).isFredholm_of_mem_linSet hF.2)
      (A₂ := ContinuousLinearEquiv.refl ℝ _) (Γ₂ := ContinuousLinearEquiv.refl ℝ _)
      (fun v => E.morTx_unit h hx hx' hs v) (fun k => E.morKx_unit h hx hx' hs k) _
      (conj_mem_refl _) o).trans (LineOrientation.conj_refl _ o)

/-- **`(φ⁻¹)_* = (φ_*)⁻¹` on orientations.** -/
theorem orMor_inv {φ : Mor} {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) :
    E.orMor hF hsec (X.inv φ) ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) hs' hs =
      (E.orMor hF hsec φ hx hx' hs hs').symm := by
  have h := (E.orMor_comp hF hsec hx hx' ((X.src_inv φ).trans hx') ((X.tgt_inv φ).trans hx) hs
    hs' hs).trans (E.orMor_unit hF hsec ((X.inv_comp φ).trans (congrArg X.unit hx)) _ _ hs)
  refine Equiv.ext fun o' => ?_
  have h1 := DFunLike.congr_fun h ((E.orMor hF hsec φ hx hx' hs hs').symm o')
  rw [Equiv.trans_apply, Equiv.apply_symm_apply] at h1
  exact h1

end Action

end EpStrongBundle

end Mor

end Polyfold
