import GWMemoir.SectionSpaces
import GWMemoir.Scales
import GWMemoir.CauchyRiemann

/-!
# The fibre spaces of `W` (Memoir §1.2, p. 7; §2.4, p. 51)

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (the bundle
`p : W → Z`, pp. 6–7) and §2.4 (the bundle scales `H^{2+m,δ_m}`, p. 51).

The fibre of `W` over a stable map `u` on bi-level `(m, k)` consists of the `(0,1)`-forms `ξ`
along `u`, anti-linear off the nodes, of class `H^{k+2}_loc` off the nodes and of class
`(k + 2, δ_k)` at the nodal points, read there in polar coordinates as
`(s, t) ↦ Tψ(u(σ(s, t))) ξ(σ(s, t))(∂_s σ(s, t))` (p. 7).  As for the sections
(`GWMemoir.SectionSpaces`), we write the fibre as a closed subspace of a finite product over a
fixed atlas.

* `formAt u z ξ y`: `ξ(y)` read in the chart of `S` at `z` and the chart of `Q` at `u(z)`,
  `Γ ∘ ξ(y) ∘ T`, with the tangent coordinate changes of `Q` and `S`.
* `fibreBlocks A δ`: over a `SectionAtlas A` (`GWMemoir.SectionSpaces`), the product
  `∏_{discs × directions × coordinates} H^{2+m,δ_m}(ℝ × S¹) ×
  ∏_{nodal points × coordinates} H^{2+m,δ_m}(ℝ × S¹)`, built from `Neck.scCylOff 2`
  (`GWMemoir.Scales`).  A disc block holds `β · e_k*(formAt (∂_d))` in the strip coordinates of
  the disc (`d = 0, 1`); a neck block holds `β⁺(s - s₀) · e_k*(formInPolar)`, the cut-off of the
  memoir's polar expression (`IsFormClassNear`).  No asymptotic constants: the forms decay.  The
  value on `∂_t σ` is not recorded: it is `-J` of the value on `∂_s σ` by anti-linearity.
* `IsFormRep A ξ v`: `v` is the tuple of local representatives of `ξ`; it is unique
  (`IsFormRep.unique`) and linear in `ξ`.
* `formsSub J A δ`: the representatives of the forms anti-linear off the nodes; `fibreSpace` is its
  closure.  `FormsClosed` (the memoir's completeness, as for `SectionsClosed`) and `FormsDense`
  (density of the smooth points, Definition 1.1.6) are the named propositions; under them the
  fibre is `formsSub` (`fibreSpace_eq`), its level `m` consists of the forms of class
  `(2+m, δ_m)` (`mem_fibreScale_iff`), and it is an sc-Banach space (`fibreSc`).
* `IsContForm u ξ`: `ξ` is continuous, read in every pair of charts.
* **`IsFormRep.eq_zero_of_cover`**: a continuous form whose representatives vanish is `0` on the
  disc regions of the atlas; on a surface without nodes it is `0` (`IsFormRep.eq_zero`).
* `isFormRep_dbar_const`: for a constant map, `∂̄_J u = 0` and its representative is `0`.
* Pull-backs: `pullbackForm_of_eq_id`, `pullbackForm_trans` (chain rule), and
  `IsAntiOff.pullback` (isomorphisms preserve the nodes and anti-linearity).

## Readings

* The memoir's fibre condition is local (at every point, in some chart); the atlas samples
  finitely many charts.  That the two agree, and that the norm does not depend on the atlas, is
  the same change of coordinates in `H^{2,δ}` as for the sections; it is not formalized.
* Forms are functions on `S`; two forms with the same representatives agree almost everywhere in
  every chart, and, if both are continuous, everywhere on the regions of the atlas.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Set Filter Topology MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-! ## 1. Forms read in charts -/

section Charts

variable {m : ℕ} {X : NodalSurface m}

/-- A form along `u`: `ξ(y) : T_yS → T_{u(y)}Q`, in Mathlib's tangent identifications. -/
abbrev Form (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (X : NodalSurface m) : Type := X.S → E2 →L[ℝ] E

/-- `ξ(y)` read in the chart of `S` at `z` and of `Q` at `u(z)`: `Γ_{u(z)} ∘ ξ(y) ∘ T_z`. -/
def formAt (u : X.S → Q) (z : X.S) (ξ : Form E X) (y : X.S) : E2 →L[ℝ] E :=
  (tangentCoordChange 𝓘(ℝ, E) (u y) (u z) (u y)).comp
    ((ξ y).comp (tangentCoordChange 𝓘(ℝ, E2) z y y))

lemma formAt_add (u : X.S → Q) (z : X.S) (ξ η : Form E X) (y : X.S) :
    formAt u z (ξ + η) y = formAt u z ξ y + formAt u z η y := by
  ext v; simp [formAt]

lemma formAt_smul (u : X.S → Q) (z : X.S) (c : ℝ) (ξ : Form E X) (y : X.S) :
    formAt u z (c • ξ) y = c • formAt u z ξ y := by
  ext v; simp [formAt]

lemma formAt_zero (u : X.S → Q) (z : X.S) (y : X.S) :
    formAt u z (0 : Form E X) y = 0 := by
  ext v; simp [formAt]

variable (u : X.S → Q)

/-- **`ξ` is continuous**: read in the charts at `z` and `u(z)`, it is continuous on the common
domain of the charts, for every `z`. -/
def IsContForm (ξ : Form E X) : Prop :=
  ∀ z, ContinuousOn (formAt u z ξ)
    ((extChartAt 𝓘(ℝ, E2) z).source ∩ u ⁻¹' (extChartAt 𝓘(ℝ, E) (u z)).source)

variable {u}

lemma IsContForm.sub {ξ η : Form E X} (h : IsContForm u ξ) (h' : IsContForm u η) :
    IsContForm u (ξ - η) := fun z => by
  have : formAt u z (ξ - η) = fun y => formAt u z ξ y - formAt u z η y := by
    funext y; ext v; simp [formAt]
  rw [this]; exact (h z).sub (h' z)

/-- `ξ(y) = 0` if `ξ` read in the charts at `z` vanishes at `y`, for `y` in the chart domains. -/
lemma eq_zero_of_formAt {ξ : Form E X} {z y : X.S} (hy : y ∈ (extChartAt 𝓘(ℝ, E2) z).source)
    (hu : u y ∈ (extChartAt 𝓘(ℝ, E) (u z)).source) (h : formAt u z ξ y = 0) : ξ y = 0 := by
  ext v
  have h1 := congrArg (fun L => tangentCoordChange 𝓘(ℝ, E) (u z) (u y) (u y)
    (L (tangentCoordChange 𝓘(ℝ, E2) y z y v))) h
  simp only [formAt, ContinuousLinearMap.comp_apply, zero_apply, map_zero] at h1
  rw [tangentCoordChange_comp (w := u y) (x := u z) (y := u y)
      ⟨⟨mem_extChartAt_source _, hu⟩, mem_extChartAt_source _⟩,
    tangentCoordChange_self (mem_extChartAt_source _),
    tangentCoordChange_comp (w := y) (x := z) (y := y)
      ⟨⟨mem_extChartAt_source _, hy⟩, mem_extChartAt_source _⟩,
    tangentCoordChange_self (mem_extChartAt_source _)] at h1
  simpa using h1

end Charts

/-! ## 2. The block space and the representatives -/

section Blocks

variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q} (A : SectionAtlas (E := E) X u)

/-- The local representative of `ξ` in the disc chart `i`, direction `d`, coordinate `k`:
`β(p) · e_k*(Γ ξ(z_p)(∂_d))` (the expression of `IsFormHlocNear`). -/
def formDiscRep (i : Fin A.nd) (d : Fin 2) (k : Fin (Module.finrank ℝ E)) (ξ : Form E X) :
    ℝ × ℝ → ℝ :=
  fun p => discCut p * crd k (formAt u (A.center i) ξ (X.discPt (A.center i) (A.ε i) p)
    (EuclideanSpace.single d 1))

/-- The local representative of `ξ` at the nodal point `j`, coordinate `k`:
`β⁺(s - s₀) · e_k*(Tψ(u(σ)) ξ(σ)(∂_s σ))` (the expression of `IsFormClassNear`, p. 7). -/
def formNeckRep (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) (ξ : Form E X) : ℝ × ℝ → ℝ :=
  fun p => Real.smoothTransition (p.1 - A.s0 j) *
    crd k (X.formInPolar u ξ (A.hol j) (A.node j) p)

variable (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- **The block space of the fibre**: `∏_{discs × directions × coordinates} H^{2+m,δ_m}(ℝ × S¹) ×
∏_{nodal points × coordinates} H^{2+m,δ_m}(ℝ × S¹)` (`scCylOff 2`, Memoir p. 51). -/
def fibreBlocks : ScBanach :=
  (finPiSc fun _ : Fin A.nd × Fin 2 × Fin (Module.finrank ℝ E) => Neck.scCylOff 2 δ h0 hmono).prod
    (finPiSc fun _ : Fin A.nn × Fin (Module.finrank ℝ E) => Neck.scCylOff 2 δ h0 hmono)

variable {A δ h0 hmono}

/-- The disc block `(i, d, k)` of a level-`0` element. -/
def fDiscBlock (v : (fibreBlocks A δ h0 hmono) 0) (i : Fin A.nd) (d : Fin 2)
    (k : Fin (Module.finrank ℝ E)) : H 2 (Neck.δ_nonneg δ h0 hmono 0) := v.1 (i, d, k)

/-- The neck block `(j, k)` of a level-`0` element. -/
def fNeckBlock (v : (fibreBlocks A δ h0 hmono) 0) (j : Fin A.nn)
    (k : Fin (Module.finrank ℝ E)) : H 2 (Neck.δ_nonneg δ h0 hmono 0) := v.2 (j, k)

/-- `v` is the tuple of local representatives of `ξ`. -/
def IsFormRep (ξ : Form E X) (v : (fibreBlocks A δ h0 hmono) 0) : Prop :=
  (∀ i d k, (H.val (fDiscBlock v i d k) : ℝ × ℝ → ℝ) =ᵐ[cyl] formDiscRep A i d k ξ) ∧
    ∀ j k, (H.val (fNeckBlock v j k) : ℝ × ℝ → ℝ) =ᵐ[cyl] formNeckRep A j k ξ

lemma formDiscRep_add (i d k) (ξ η : Form E X) :
    formDiscRep A i d k (ξ + η) = formDiscRep A i d k ξ + formDiscRep A i d k η := by
  funext p; simp only [formDiscRep, formAt_add, Pi.add_apply, add_apply, map_add, mul_add]

lemma formDiscRep_smul (i d k) (c : ℝ) (ξ : Form E X) :
    formDiscRep A i d k (c • ξ) = c • formDiscRep A i d k ξ := by
  funext p
  simp only [formDiscRep, formAt_smul, Pi.smul_apply, smul_apply, map_smul, smul_eq_mul]; ring

lemma formInPolar_add (φ : OpenPartialHomeomorph X.S ℂ) (x : X.S) (ξ η : Form E X) (p : ℝ × ℝ) :
    X.formInPolar u (ξ + η) φ x p = X.formInPolar u ξ φ x p + X.formInPolar u η φ x p := by
  unfold NodalSurface.formInPolar
  exact map_add _ _ _

lemma formInPolar_smul (φ : OpenPartialHomeomorph X.S ℂ) (x : X.S) (c : ℝ) (ξ : Form E X)
    (p : ℝ × ℝ) : X.formInPolar u (c • ξ) φ x p = c • X.formInPolar u ξ φ x p := by
  unfold NodalSurface.formInPolar
  exact map_smul _ _ _

lemma formNeckRep_add (j k) (ξ η : Form E X) :
    formNeckRep A j k (ξ + η) = formNeckRep A j k ξ + formNeckRep A j k η := by
  funext p; simp only [formNeckRep, formInPolar_add, Pi.add_apply, map_add, mul_add]

lemma formNeckRep_smul (j k) (c : ℝ) (ξ : Form E X) :
    formNeckRep A j k (c • ξ) = c • formNeckRep A j k ξ := by
  funext p
  simp only [formNeckRep, formInPolar_smul, Pi.smul_apply, map_smul, smul_eq_mul]; ring

lemma isFormRep_zero :
    IsFormRep (A := A) (δ := δ) (h0 := h0) (hmono := hmono) (0 : Form E X) 0 := by
  refine ⟨fun i d k => ?_, fun j k => ?_⟩
  · filter_upwards [val_zero_ae (k := 2) (hd := Neck.δ_nonneg δ h0 hmono 0)] with p hp
    rw [show fDiscBlock (0 : (fibreBlocks A δ h0 hmono) 0) i d k = 0 from rfl, hp]
    simp [formDiscRep, formAt_zero]
  · filter_upwards [val_zero_ae (k := 2) (hd := Neck.δ_nonneg δ h0 hmono 0)] with p hp
    rw [show fNeckBlock (0 : (fibreBlocks A δ h0 hmono) 0) j k = 0 from rfl, hp]
    simp only [formNeckRep, Pi.zero_apply]
    rw [show (0 : Form E X) = fun _ => 0 from rfl, NodalSurface.formInPolar_zero]
    simp

lemma IsFormRep.add {ξ η : Form E X} {v w : (fibreBlocks A δ h0 hmono) 0} (h : IsFormRep ξ v)
    (h' : IsFormRep η w) : IsFormRep (ξ + η) (v + w) := by
  refine ⟨fun i d k => ?_, fun j k => ?_⟩
  · rw [formDiscRep_add]
    filter_upwards [val_add_ae (fDiscBlock v i d k) (fDiscBlock w i d k), h.1 i d k, h'.1 i d k]
      with p h1 h2 h3
    exact h1.trans (by rw [h2, h3]; rfl)
  · rw [formNeckRep_add]
    filter_upwards [val_add_ae (fNeckBlock v j k) (fNeckBlock w j k), h.2 j k, h'.2 j k]
      with p h1 h2 h3
    exact h1.trans (by rw [h2, h3]; rfl)

lemma IsFormRep.smul {ξ : Form E X} {v : (fibreBlocks A δ h0 hmono) 0} (h : IsFormRep ξ v)
    (c : ℝ) : IsFormRep (c • ξ) (c • v) := by
  refine ⟨fun i d k => ?_, fun j k => ?_⟩
  · rw [formDiscRep_smul]
    filter_upwards [val_smul_ae c (fDiscBlock v i d k), h.1 i d k] with p h1 h2
    exact h1.trans (by rw [h2]; rfl)
  · rw [formNeckRep_smul]
    filter_upwards [val_smul_ae c (fNeckBlock v j k), h.2 j k] with p h1 h2
    exact h1.trans (by rw [h2]; rfl)

lemma H_ext_ae {k : ℕ} {d : ℝ} {hd : 0 ≤ d} {a b : H k hd}
    (h : (H.val a : ℝ × ℝ → ℝ) =ᵐ[cyl] H.val b) : a = b :=
  Subtype.ext (Lp.ext h)

/-- **The representatives are unique.** -/
theorem IsFormRep.unique {ξ : Form E X} {v w : (fibreBlocks A δ h0 hmono) 0} (h : IsFormRep ξ v)
    (h' : IsFormRep ξ w) : v = w := by
  refine Prod.ext (funext fun ⟨i, d, k⟩ => ?_) (funext fun ⟨j, k⟩ => ?_)
  · exact H_ext_ae ((h.1 i d k).trans (h'.1 i d k).symm)
  · exact H_ext_ae ((h.2 j k).trans (h'.2 j k).symm)

/-- Forms with the same representatives have the same differences: `ξ - η` has representative
`v - w`. -/
lemma IsFormRep.sub {ξ η : Form E X} {v w : (fibreBlocks A δ h0 hmono) 0} (h : IsFormRep ξ v)
    (h' : IsFormRep η w) : IsFormRep (ξ - η) (v - w) := by
  have := h.add (h'.smul (-1))
  simpa [sub_eq_add_neg] using this

end Blocks

/-! ## 3. The fibre space -/

section Fibre

variable (J : AlmostComplexStructure E Q)
variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q} (A : SectionAtlas (E := E) X u)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

variable (X u) in
/-- `ξ(x)` is anti-linear, `J(u(x)) ∘ ξ(x) = -ξ(x) ∘ j_x`, at every point off the nodes. -/
def IsAntiOff (ξ : Form E X) : Prop :=
  ∀ x, (∀ p ∈ X.nodes, x ∉ p) → ξ x ∈ X.antiLinearForms J (u x) x

lemma isAntiOff_zero : IsAntiOff J X u (0 : Form E X) := fun _ _ => Submodule.zero_mem _

lemma IsAntiOff.add {ξ η : Form E X} (h : IsAntiOff J X u ξ) (h' : IsAntiOff J X u η) :
    IsAntiOff J X u (ξ + η) := fun x hx => Submodule.add_mem _ (h x hx) (h' x hx)

lemma IsAntiOff.smul {ξ : Form E X} (h : IsAntiOff J X u ξ) (c : ℝ) :
    IsAntiOff J X u (c • ξ) := fun x hx => Submodule.smul_mem _ c (h x hx)

/-- The forms anti-linear off the nodes which have representatives in the blocks. -/
def formsDom : Submodule ℝ (Form E X) where
  carrier := {ξ | IsAntiOff J X u ξ ∧ ∃ v : (fibreBlocks A δ h0 hmono) 0, IsFormRep ξ v}
  zero_mem' := ⟨isAntiOff_zero J, 0, isFormRep_zero⟩
  add_mem' := by
    rintro ξ η ⟨ha, v, hv⟩ ⟨ha', w, hw⟩
    exact ⟨ha.add J ha', v + w, hv.add hw⟩
  smul_mem' := by
    rintro c ξ ⟨ha, v, hv⟩
    exact ⟨ha.smul J c, c • v, hv.smul c⟩

/-- The representatives of the forms anti-linear off the nodes. -/
def formsSub : Submodule ℝ ((fibreBlocks A δ h0 hmono) 0) where
  carrier := {v | ∃ ξ : Form E X, IsAntiOff J X u ξ ∧ IsFormRep ξ v}
  zero_mem' := ⟨0, isAntiOff_zero J, isFormRep_zero⟩
  add_mem' := by
    rintro v w ⟨ξ, ha, hv⟩ ⟨η, ha', hw⟩
    exact ⟨ξ + η, ha.add J ha', hv.add hw⟩
  smul_mem' := by
    rintro c v ⟨ξ, ha, hv⟩
    exact ⟨c • ξ, ha.smul J c, hv.smul c⟩

/-- **The fibre of `W` over `u`** (Memoir p. 7), level `0`: the closure of the representatives of
the anti-linear forms in the block space. -/
def fibreSpace : Submodule ℝ ((fibreBlocks A δ h0 hmono) 0) :=
  (formsSub J A δ h0 hmono).topologicalClosure

lemma isClosed_fibreSpace :
    IsClosed (fibreSpace J A δ h0 hmono : Set ((fibreBlocks A δ h0 hmono) 0)) :=
  Submodule.isClosed_topologicalClosure _

lemma formsSub_le : formsSub J A δ h0 hmono ≤ fibreSpace J A δ h0 hmono :=
  Submodule.le_topologicalClosure _

instance fibreSpace_completeSpace : CompleteSpace (fibreSpace J A δ h0 hmono) :=
  (isClosed_fibreSpace J A δ h0 hmono).completeSpace_coe

/-- The memoir's completeness of the norm: the representatives of the forms form a closed set. -/
def FormsClosed : Prop := IsClosed (formsSub J A δ h0 hmono : Set ((fibreBlocks A δ h0 hmono) 0))

theorem fibreSpace_eq (h : FormsClosed J A δ h0 hmono) :
    fibreSpace J A δ h0 hmono = formsSub J A δ h0 hmono :=
  IsClosed.submodule_topologicalClosure_eq h

/-- The scale of the fibre: levels `F_m = F ∩ (blocks)_m`, with compact inclusions. -/
def fibreScale : ScScale :=
  (fibreBlocks A δ h0 hmono).ofSubspaceScale (isClosed_fibreSpace J A δ h0 hmono)

/-- Level `m` of the fibre scale: the anti-linear forms whose representatives lie in the
level-`m` blocks `H^{2+m,δ_m}`, i.e. the forms of class `(2+m, δ_m)` (given `FormsClosed`). -/
theorem mem_fibreScale_iff (h : FormsClosed J A δ h0 hmono) (k : ℕ)
    (v : (fibreBlocks A δ h0 hmono) k) :
    v ∈ (fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) k ↔
      ∃ ξ : Form E X, IsAntiOff J X u ξ ∧ IsFormRep ξ ((fibreBlocks A δ h0 hmono).toBase k v) := by
  rw [ScBanach.mem_levelSub, fibreSpace_eq J A δ h0 hmono h]; rfl

/-- The smooth points are dense in every level of the fibre (Definition 1.1.6). -/
def FormsDense : Prop := (fibreBlocks A δ h0 hmono).IsScSubspace (fibreSpace J A δ h0 hmono)

/-- The fibre as an sc-Banach space, given the density of the smooth points. -/
def fibreSc (h : FormsDense J A δ h0 hmono) : ScBanach :=
  (fibreBlocks A δ h0 hmono).ofSubspace h

variable {J A δ h0 hmono}

/-- The representative of a form of `formsDom`, as an element of the fibre. -/
def formRep (ξ : formsDom J A δ h0 hmono) : fibreSpace J A δ h0 hmono :=
  ⟨ξ.2.2.choose, formsSub_le J A δ h0 hmono ⟨ξ.1, ξ.2.1, ξ.2.2.choose_spec⟩⟩

lemma isFormRep_formRep (ξ : formsDom J A δ h0 hmono) :
    IsFormRep (ξ : Form E X) (formRep ξ : (fibreBlocks A δ h0 hmono) 0) :=
  ξ.2.2.choose_spec

lemma formRep_eq {ξ : formsDom J A δ h0 hmono} {v : (fibreBlocks A δ h0 hmono) 0}
    (h : IsFormRep (ξ : Form E X) v) : (formRep ξ : (fibreBlocks A δ h0 hmono) 0) = v :=
  (isFormRep_formRep ξ).unique h

variable (J A δ h0 hmono) in
/-- **`ξ ↦` its representative, a linear map from the forms to the fibre.** -/
def formRepL : formsDom J A δ h0 hmono →ₗ[ℝ] fibreSpace J A δ h0 hmono where
  toFun := formRep
  map_add' ξ η := Subtype.ext <| formRep_eq ((isFormRep_formRep ξ).add (isFormRep_formRep η))
  map_smul' c ξ := Subtype.ext <| formRep_eq ((isFormRep_formRep ξ).smul c)

end Fibre

/-! ## 4. Continuous forms with vanishing representatives -/

section Vanish

/-- Every neighbourhood of a point of the open strip `ℝ × (0, 1)` has positive measure. -/
lemma cyl_pos_of_mem_nhds {p₀ : ℝ × ℝ} (h1 : 0 < p₀.2) (h2 : p₀.2 < 1) {W : Set (ℝ × ℝ)}
    (hW : W ∈ 𝓝 p₀) : 0 < cyl W := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hW
  set r' := min r (min p₀.2 (1 - p₀.2)) with hr'
  have hr'0 : 0 < r' := lt_min hr (lt_min h1 (by linarith))
  have hsub : Metric.ball p₀.1 r' ×ˢ Metric.ball p₀.2 r' ⊆ W := by
    refine Subset.trans ?_ hball
    rw [← ball_prod_same]
    exact prod_mono (Metric.ball_subset_ball (min_le_left _ _))
      (Metric.ball_subset_ball (min_le_left _ _))
  have hI : Metric.ball p₀.2 r' ⊆ Ioc (0 : ℝ) 1 := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
    have : r' ≤ p₀.2 := (min_le_right _ _).trans (min_le_left _ _)
    have : r' ≤ 1 - p₀.2 := (min_le_right _ _).trans (min_le_right _ _)
    constructor <;> linarith
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [cyl, Measure.prod_prod, Measure.restrict_apply Metric.isOpen_ball.measurableSet,
    inter_eq_left.2 hI, Real.volume_ball, Real.volume_ball]
  have : (0 : ℝ) < 2 * r' := by linarith
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 this).ne' (ENNReal.ofReal_pos.2 this).ne'

/-- A function continuous at a point of the open strip and almost everywhere `0` vanishes there. -/
lemma eq_zero_of_ae_of_continuousAt {g : ℝ × ℝ → ℝ} {p₀ : ℝ × ℝ} (h1 : 0 < p₀.2) (h2 : p₀.2 < 1)
    (hg : ContinuousAt g p₀) (h : g =ᵐ[cyl] 0) : g p₀ = 0 := by
  by_contra hne
  have hW : {p | g p ≠ 0} ∈ 𝓝 p₀ := hg.eventually_ne hne
  have h0 : cyl {p | ¬ g p = (0 : ℝ × ℝ → ℝ) p} = 0 := ae_iff.1 h
  exact (cyl_pos_of_mem_nhds h1 h2 hW).ne' h0

lemma discCut_eq_one {p : ℝ × ℝ} (h : p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 ≤ 1 / 16) : discCut p = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma single_eq_smul (d : Fin 2) (a : ℝ) :
    EuclideanSpace.single d a = a • EuclideanSpace.single d (1 : ℝ) := by
  ext i; by_cases hi : i = d <;> simp [hi]

lemma continuous_place {m : ℕ} (X : NodalSurface m) (z : X.S) (ε : ℝ) :
    Continuous (X.place z ε) := by
  have : X.place z ε = fun p => extChartAt 𝓘(ℝ, E2) z z + ε • (p.1 • EuclideanSpace.single 0 1 +
      (p.2 - 1 / 2) • EuclideanSpace.single 1 (1 : ℝ)) := by
    funext p; unfold NodalSurface.place; rw [← single_eq_smul, ← single_eq_smul]
  rw [this]
  fun_prop

lemma E2_ext {L L' : E2 →L[ℝ] E} (h : ∀ d : Fin 2, L (EuclideanSpace.single d 1) =
    L' (EuclideanSpace.single d 1)) : L = L' := by
  ext w
  rw [← single_add_single_eq w]
  rw [single_eq_smul 0 (w 0), single_eq_smul 1 (w 1), map_add, map_add, map_smul, map_smul,
    map_smul, map_smul, h 0, h 1]

variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q} {A : SectionAtlas (E := E) X u}
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

/-- **A continuous form whose disc representatives vanish is `0` on the disc regions.** -/
theorem IsFormRep.eq_zero_on_disc {ξ : Form E X} (hc : IsContForm u ξ)
    (h : IsFormRep (A := A) (δ := δ) (h0 := h0) (hmono := hmono) ξ 0) (i : Fin A.nd)
    {p₀ : ℝ × ℝ} (hp₀ : p₀.1 ^ 2 + (p₀.2 - 1 / 2) ^ 2 ≤ 1 / 16) :
    ξ (X.discPt (A.center i) (A.ε i) p₀) = 0 := by
  set z := A.center i
  set U : Set (ℝ × ℝ) := {p | p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 < 1 / 8}
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hp₀U : p₀ ∈ U := by
    change p₀.1 ^ 2 + (p₀.2 - 1 / 2) ^ 2 < 1 / 8
    linarith
  have hy : ∀ p ∈ U, ContinuousWithinAt (X.discPt z (A.ε i)) U p := fun p hp =>
    ((continuousAt_extChartAt_symm'' (A.disc_chart i p hp).1).comp
      (continuous_place X z (A.ε i)).continuousAt
      ).continuousWithinAt
  have hmaps : MapsTo (X.discPt z (A.ε i)) U
      ((extChartAt 𝓘(ℝ, E2) z).source ∩ u ⁻¹' (extChartAt 𝓘(ℝ, E) (u z)).source) :=
    fun p hp => ⟨(extChartAt 𝓘(ℝ, E2) z).map_target (A.disc_chart i p hp).1,
      (A.disc_chart i p hp).2⟩
  have hF : ContinuousAt (fun p => formAt u z ξ (X.discPt z (A.ε i) p)) p₀ :=
    (((hc z).continuousWithinAt (hmaps hp₀U)).comp (hy p₀ hp₀U) hmaps).continuousAt
      (hU.mem_nhds hp₀U)
  have hp2 : 1 / 4 ≤ p₀.2 ∧ p₀.2 ≤ 3 / 4 := by
    constructor <;> nlinarith [sq_nonneg p₀.1, sq_nonneg (p₀.2 - 1 / 4), sq_nonneg (p₀.2 - 3 / 4)]
  have hzero : formAt u z ξ (X.discPt z (A.ε i) p₀) = 0 := by
    refine E2_ext fun d => ?_
    refine (Module.finBasis ℝ E).ext_elem fun k => ?_
    have hae : formDiscRep A i d k ξ =ᵐ[cyl] 0 :=
      (h.1 i d k).symm.trans (val_zero_ae (k := 2) (hd := Neck.δ_nonneg δ h0 hmono 0))
    have hcont : ContinuousAt (formDiscRep A i d k ξ) p₀ := by
      unfold formDiscRep discCut
      refine ContinuousAt.mul (by fun_prop) ?_
      exact (crd k).continuous_of_finiteDimensional.continuousAt.comp
        ((ContinuousLinearMap.apply ℝ E (EuclideanSpace.single d 1)).continuous.continuousAt.comp
          hF)
    have := eq_zero_of_ae_of_continuousAt (by linarith) (by linarith) hcont hae
    rw [formDiscRep, discCut_eq_one hp₀, one_mul] at this
    simpa using this
  exact eq_zero_of_formAt (hmaps hp₀U).1 (hmaps hp₀U).2 hzero

/-- **On a surface without nodes, a continuous form with representative `0` is `0`.** -/
theorem IsFormRep.eq_zero (hX : X.nodes = ∅) {ξ : Form E X} (hc : IsContForm u ξ)
    (h : IsFormRep (A := A) (δ := δ) (h0 := h0) (hmono := hmono) ξ 0) : ξ = 0 := by
  funext y
  rcases A.cover y with ⟨i, p, hp, rfl⟩ | ⟨j, -⟩
  · exact h.eq_zero_on_disc hc i hp
  · obtain ⟨q, hq, -⟩ := A.node_nodal j
    rw [hX] at hq
    exact absurd hq (notMem_empty q)

/-- **Two continuous forms with the same representative agree** (no nodes). -/
theorem IsFormRep.inj (hX : X.nodes = ∅) {ξ η : Form E X} (hξ : IsContForm u ξ)
    (hη : IsContForm u η) {v : (fibreBlocks A δ h0 hmono) 0} (h : IsFormRep ξ v)
    (h' : IsFormRep η v) : ξ = η :=
  sub_eq_zero.1 (IsFormRep.eq_zero hX (hξ.sub hη) (by simpa using h.sub h'))

end Vanish

/-! ## 5. The constant maps -/

section Const

variable (J : AlmostComplexStructure E Q) {m : ℕ} {X : NodalSurface m} (q : Q)

/-- `∂̄_J` of a constant map is the zero form. -/
theorem dbar_const_eq_zero : X.dbar J (fun _ => q) = (0 : Form E X) :=
  funext fun x => X.dbar_const J q x

/-- **For a constant map, `∂̄_J u` has representative `0` in every atlas**: `∂̄_J u = 0` in the
fibre. -/
theorem isFormRep_dbar_const (A : SectionAtlas (E := E) X (fun _ => q)) (δ : ℕ → ℝ)
    (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) :
    IsFormRep (A := A) (δ := δ) (h0 := h0) (hmono := hmono) (X.dbar J (fun _ => q)) 0 := by
  rw [dbar_const_eq_zero]; exact isFormRep_zero

end Const

/-! ## 6. Pull-backs of forms -/

section Pullback

namespace NodalSurface.Iso

variable {m : ℕ} {X Y Z : NodalSurface m}

/-- The pull-back by an isomorphism whose map is the identity is the identity. -/
theorem pullbackForm_of_eq_id (f : Iso X X) (hf : ∀ x, f.φ x = x) (ξ : Form E X) :
    f.pullbackForm ξ = ξ := by
  have h : (f.φ : X.S → X.S) = id := funext hf
  funext x
  change (ξ (f.φ x)).comp (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) (f.φ : X.S → X.S) x) = ξ x
  rw [h, mfderiv_id]
  rfl

/-- `(g ∘ f)^* = f^* ∘ g^*` (chain rule). -/
theorem pullbackForm_trans (f : Iso X Y) (g : Iso Y Z) (ξ : Form E Z) :
    (f.trans g).pullbackForm ξ = f.pullbackForm (g.pullbackForm ξ) := by
  funext x
  change (ξ (g.φ (f.φ x))).comp (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) (f.φ.trans g.φ : X.S → Z.S) x) =
    ((ξ (g.φ (f.φ x))).comp (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) g.φ (f.φ x))).comp
      (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ x)
  rw [Diffeomorph.coe_trans, mfderiv_comp x (g.mdifferentiableAt _) (f.mdifferentiableAt x)]
  rfl

end NodalSurface.Iso

variable (J : AlmostComplexStructure E Q) {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ}

/-- The pull-back by an isomorphism of stable maps preserves anti-linearity off the nodes. -/
theorem IsAntiOff.pullback {α β : StableMap om m k δ} (f : α.Iso β) {ξ : Form E β.dom}
    (h : IsAntiOff J β.dom β.u ξ) : IsAntiOff J α.dom α.u (f.φ.pullbackForm ξ) := by
  intro x hx
  have hfx : ∀ p ∈ β.dom.nodes, f.φ.φ x ∉ p := by
    intro p hp hxp
    rw [← f.φ.nodes] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨a, ha, hfa⟩ := Sym2.mem_map.1 hxp
    exact hx q hq (f.φ.φ.injective hfa ▸ ha)
  have := f.φ.pullbackForm_mem J (h _ hfx)
  rwa [f.comm x] at this

theorem pullbackForm_symm_trans {α β : StableMap om m k δ} (f : α.Iso β) (ξ : Form E β.dom) :
    f.symm.φ.pullbackForm (f.φ.pullbackForm ξ) = ξ := by
  rw [← NodalSurface.Iso.pullbackForm_trans]
  exact NodalSurface.Iso.pullbackForm_of_eq_id _ (fun y => f.φ.φ.apply_symm_apply y) ξ

theorem pullbackForm_trans_symm {α β : StableMap om m k δ} (f : α.Iso β) (ξ : Form E α.dom) :
    f.φ.pullbackForm (f.symm.φ.pullbackForm ξ) = ξ := by
  rw [← NodalSurface.Iso.pullbackForm_trans]
  exact NodalSurface.Iso.pullbackForm_of_eq_id _ (fun x => f.φ.φ.symm_apply_apply x) ξ

theorem pullbackForm_trans_symm' {α β γ : StableMap om m k δ} (g : α.Iso β) (f : β.Iso γ)
    (ξ : Form E α.dom) :
    (g.trans f).symm.φ.pullbackForm ξ = f.symm.φ.pullbackForm (g.symm.φ.pullbackForm ξ) := by
  rw [← NodalSurface.Iso.pullbackForm_trans]
  rfl

end Pullback

end GWMemoir
