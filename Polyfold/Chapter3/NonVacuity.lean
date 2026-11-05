import Polyfold.Chapter3.GlobalIFTTheorems
import Polyfold.Chapter3.ParamPerturbation

/-!
# The hypotheses of the §3.6 implicit function theorems are satisfiable

A **non-vacuity witness** for the global implicit function theorems of §3.6 (Theorems 3.54, 3.56,
3.57, Corollary 3.24): the trivial strong bundle `ℝⁿ × ℝᵏ → ℝⁿ` over the M-polyfold `ℝⁿ` and the
section `x ↦ (x, φ(x))` of a `C^∞` map `φ : ℝⁿ → ℝᵏ` satisfy the hypotheses `IsScFredholmSectionWholeChart`
and "`(f, x)` is in good position in a tame chart at every zero" (`IsGoodPositionGermTameWholeChart`) as soon
as `Dφ(x)` is onto at every zero of `φ`.  The conclusion of Theorem 3.57 is then the classical
regular value theorem for `φ⁻¹(0)` (`theorem_3_57_trivialBundle`).

This is not in the text.  It was added after the §3.6 theorems were found to have been vacuously
true under an earlier formalization (the hypothesis `htame` quantified over all compatible charts,
`TameVacuity.lean`; Findings, Chapter 3 items 190–199): the witness checks that the repaired
hypotheses can hold (Findings, Chapter 3 item 200).  It has no boundary (`C = ℝⁿ`) and
finite-dimensional fibres; the boundary case of good position is `NonVacuityCorner.lean`
(item 201), and the infinite-dimensional contraction part of a basic germ is not exercised.

## What is formalized

* `TrivialBundle.proj n k : ℝⁿ × ℝᵏ → ℝⁿ` with the fibre structure transported from `ℝᵏ`
  (`fibEquiv`), the translation strong bundle charts `TrivialBundle.chart a`
  (`(x, v) ↦ (x − a, v)`, the identity strong bundle retraction on `ℝⁿ ◁ ℝᵏ`), pairwise compatible
  (`chart_compatible`), and the strong bundle `TrivialBundle.bundle n k`.
* `TrivialBundle.graphSection φ : x ↦ (x, φ(x))`; for `φ` of class `C^∞` it is an sc-Fredholm
  section (`isScFredholmSection_graphSection_wholeChart`), with tame germ data at every point
  (`isScFredholmGermTame_graphSection_wholeChart`), in good position in a tame chart at every zero `x` where
  `Dφ(x)` is onto (`isGoodPositionGermTame_graphSection_wholeChart`).
* `theorem_3_57_trivialBundle`: Theorem 3.57 applied to it.

The helper `isScSmooth_of_bijective_toBase` (a `C^∞` map between sc-Banach spaces whose inclusions
`E_m → E_0` are bijective, e.g. products of finite-dimensional spaces with the constant structure,
is sc-smooth) and `isStrongBundleRetraction_id` (the identity of `univ ◁ F`) are stated in general.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### Sc-smoothness when every inclusion `E_m → E_0` is bijective -/

section Flat

variable {E F : ScBanach}

/-- **A `C^∞` map between sc-Banach spaces with bijective inclusions `E_m → E_0`, `F_m → F_0` is
sc-smooth**: its level maps are `f` conjugated by the (continuous linear) inclusions. -/
theorem isScSmooth_of_bijective_toBase (hE : ∀ m, Bijective (E.toBase m))
    (hF : ∀ m, Bijective (F.toBase m)) {U : Set (E 0)} (hU : IsScDomain E U) {f : E 0 → F 0}
    (hf : ContDiffOn ℝ ∞ f U) : IsScSmooth U f := by
  refine IsScSmooth.of_contDiffOn_levels hU (fun m x _ => (hF m).2 _) fun m => ?_
  let eE := ContinuousLinearEquiv.ofBijective (E.toBase m)
    (LinearMap.ker_eq_bot.2 (hE m).1) (LinearMap.range_eq_top.2 (hE m).2)
  let eF := ContinuousLinearEquiv.ofBijective (F.toBase m)
    (LinearMap.ker_eq_bot.2 (hF m).1) (LinearMap.range_eq_top.2 (hF m).2)
  have hl : levelMap f m = eF.symm ∘ f ∘ eE := funext fun x =>
    levelMap_eq_of_toBase_eq (by
      change eF (eF.symm (f (eE x))) = f (E.toBase m x)
      rw [ContinuousLinearEquiv.apply_symm_apply]; rfl)
  rw [hl]
  exact eF.symm.contDiff.comp_contDiffOn (hf.comp eE.contDiff.contDiffOn fun x hx => hx)

lemma bijective_toBase_const (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (m : ℕ) : Bijective ((ScBanach.const V).toBase m) := by
  have : ⇑((ScBanach.const V).toBase m) = id := funext (ScBanach.const_toBase V m)
  rw [this]; exact bijective_id

lemma bijective_toBase_prod (hE : ∀ m, Bijective (E.toBase m)) (hF : ∀ m, Bijective (F.toBase m))
    (m : ℕ) : Bijective ((E.prod F).toBase m) := by
  have : ⇑((E.prod F).toBase m) = Prod.map (E.toBase m) (F.toBase m) :=
    funext (ScBanach.prod_toBase E F m)
  rw [this]; exact (hE m).prodMap (hF m)

lemma bijective_toBase_shift (hE : ∀ m, Bijective (E.toBase m)) (m : ℕ) :
    Bijective (E.shift.toBase m) := by
  refine ⟨fun x y hxy => (hE (m + 1)).1 ?_, fun z => ?_⟩
  · rw [ScBanach.shift_toBase (E := E) (m := m) (x := x),
      ScBanach.shift_toBase (E := E) (m := m) (x := y), hxy]
  · obtain ⟨x, hx⟩ := (hE (m + 1)).2 (E.toBase 1 z)
    exact ⟨x, (hE 1).1 (by rw [← ScBanach.shift_toBase (E := E) (m := m) (x := x), hx])⟩

/-- On `univ` of a finite-dimensional space with the constant structure, the sc-derivative of a
`C^∞` map into a finite-dimensional space is the classical derivative. -/
lemma scDeriv_univ_const {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
    {f : V → V'} (hf : ContDiff ℝ ∞ f) (v : V) :
    scDeriv (E := ScBanach.const V) (F := ScBanach.const V') univ f v = fderiv ℝ f v := by
  have hf1 : IsSc1 (E := ScBanach.const V) (F := ScBanach.const V') univ f :=
    (isScSmooth_of_bijective_toBase (bijective_toBase_const V) (bijective_toBase_const V')
      (isScDomain_univ _) hf.contDiffOn).isSc1
  have h1 := hf1.isSc1With_scDeriv.hasFDerivWithinAt (v : (ScBanach.const V) 1) (mem_univ _)
  rw [ScBanach.lvlSet_const] at h1
  have e1 : (f ∘ ⇑((ScBanach.const V).toBase 1)) = f :=
    funext fun x => congrArg f (ScBanach.const_toBase V 1 x)
  have e2 : (scDeriv (E := ScBanach.const V) (F := ScBanach.const V') univ f v).comp
      ((ScBanach.const V).toBase 1) = scDeriv (E := ScBanach.const V) (F := ScBanach.const V')
        univ f v := by
    ext x; exact congrArg _ (ScBanach.const_toBase V 1 x)
  rw [e1, e2] at h1
  exact (hasFDerivWithinAt_univ.1 h1).fderiv.symm

/-- `C^∞` maps out of `univ` between spaces with bijective inclusions are sc-smooth maps between
the retracts `univ`. -/
theorem isScSmoothRetractMap_of_bijective_toBase {E' : ScBanach} (hE : ∀ m, Bijective (E.toBase m))
    (hE' : ∀ m, Bijective (E'.toBase m)) {C : Set (E 0)} (hC : IsRelOpenInQuadrant E C univ)
    {C' O' : Set (E' 0)} {g : E 0 → E' 0} (hmaps : MapsTo g univ O') (hg : ContDiff ℝ ∞ g) :
    IsScSmoothRetractMap E C univ E' C' O' g :=
  (isScSmoothRetractMap_iff_exists hC.isScRetract).2
    ⟨hmaps, ScRetraction.id hC, image_id _,
      isScSmooth_of_bijective_toBase hE hE' hC.isScDomain (f := g ∘ ScRetraction.id hC)
        hg.contDiffOn⟩

end Flat

/-! ### The identity strong bundle retraction -/

/-- The identity of `univ ◁ F` is a strong bundle retraction. -/
theorem isStrongBundleRetraction_id {E F : ScBanach} :
    IsStrongBundleRetraction (E := E) (F := F) univ id where
  mapsTo := mapsTo_id _
  fst_independent _ _ _ _ := rfl
  fiber_linear _ _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  preserves_filtration _ _ _ _ _ hu _ hh := ⟨hu, hh⟩
  isScSmooth_zero := by
    rw [univ_prod_univ]; exact isScSmooth_id (isScDomain_univ _)
  isScSmooth_one := by
    rw [univ_prod_univ]
    refine (isScSmooth_id (isScDomain_univ _)).congr (isScDomain_univ _) fun p _ => ?_
    change p = (p.1, invFun (F.toBase 1) (F.toBase 1 p.2))
    rw [leftInverse_invFun (F.toBase_injective 1)]
  idem _ _ := rfl

/-! ### The trivial strong bundle `ℝⁿ × ℝᵏ → ℝⁿ` -/

namespace TrivialBundle

variable (n k : ℕ)

/-- The projection `ℝⁿ × ℝᵏ → ℝⁿ`. -/
def proj : (Fin n → ℝ) × (Fin k → ℝ) → (Fin n → ℝ) := Prod.fst

variable {n k}

@[simp] lemma proj_apply (y : (Fin n → ℝ) × (Fin k → ℝ)) : proj n k y = y.1 := rfl

/-- The fibre `proj⁻¹(x) ≃ ℝᵏ`. -/
def fibEquiv (x : Fin n → ℝ) : proj n k ⁻¹' {x} ≃ (Fin k → ℝ) where
  toFun y := y.1.2
  invFun v := ⟨(x, v), rfl⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    simp only [mem_preimage, proj_apply, mem_singleton_iff] at h
    subst h; rfl
  right_inv _ := rfl

instance (x : Fin n → ℝ) : AddCommGroup (proj n k ⁻¹' {x}) := (fibEquiv x).addCommGroup

instance (x : Fin n → ℝ) : Module ℝ (proj n k ⁻¹' {x}) := (fibEquiv x).module ℝ

/-- The fibre projection `v ↦ v₂` is linear for the transported structure. -/
lemma isLinearMap_fibEquiv (x : Fin n → ℝ) : IsLinearMap ℝ (fibEquiv (k := k) x) :=
  ((fibEquiv x).linearEquiv ℝ).toLinearMap.isLinear

/-- The translation strong bundle chart `(x, v) ↦ (x − a, v)`, over the chart `x ↦ x − a` of `ℝⁿ`,
with the identity strong bundle retraction on `ℝⁿ ◁ ℝᵏ`. -/
def chart (a : Fin n → ℝ) : StrongBundleChart (rnPolyfold n) (proj n k) where
  φ := rnChart n a
  isChart := isChart_rnChart a
  F := rnSc k
  U := univ
  R := id
  relOpen := rn_relOpen_univ n
  isRetraction := isStrongBundleRetraction_id
  base_retract := by
    change (fun u => u) '' univ = univ
    exact image_univ_of_surjective surjective_id
  toPartialEquiv := ((Equiv.subRight a).prodCongr (Equiv.refl (Fin k → ℝ))).toPartialEquiv
  source_eq := preimage_univ.symm
  target_eq := by
    change univ = id '' (univ ×ˢ univ)
    rw [univ_prod_univ, image_id]
  continuousOn_toFun := ((continuous_sub_right a).prodMap continuous_id).continuousOn
  continuousOn_invFun := ((continuous_add_const a).prodMap continuous_id).continuousOn
  covers _ _ := rfl
  fiber_linear x _ := isLinearMap_fibEquiv x

@[simp] lemma chart_apply (a : Fin n → ℝ) (y : (Fin n → ℝ) × (Fin k → ℝ)) :
    chart a y = (y.1 - a, y.2) := rfl

lemma chart_overlap (a b : Fin n → ℝ) : (chart (k := k) a).overlap (chart b) = univ := by
  refine eq_univ_of_forall fun (p : (Fin n → ℝ) × (Fin k → ℝ)) =>
    ⟨(p.1 + a, p.2), ⟨mem_univ _, mem_univ _⟩, ?_⟩
  change (p.1 + a - a, p.2) = p
  rw [add_sub_cancel_right]

lemma bijective_toBase_model (m : ℕ) : Bijective (((rnSc n).prod (rnSc k)).toBase m) :=
  bijective_toBase_prod (bijective_toBase_const _) (bijective_toBase_const _) m

lemma relOpen_model : IsRelOpenInQuadrant ((rnSc n).prod (rnSc k)) (univ ×ˢ univ) univ := by
  rw [← univ_prod_univ]; exact (rn_relOpen_univ n).prod_univ (rnSc k)

/-- The transition maps `(u, v) ↦ (u + a − b, v)` as sc-smooth maps of `univ`. -/
lemma isScSmoothRetractMap_transition (a b : Fin n → ℝ) :
    IsScSmoothRetractMap ((rnSc n).prod (rnSc k)) (univ ×ˢ univ) univ ((rnSc n).prod (rnSc k))
      (univ ×ˢ univ) univ (fun p : (Fin n → ℝ) × (Fin k → ℝ) => (p.1 + a - b, p.2)) :=
  isScSmoothRetractMap_of_bijective_toBase bijective_toBase_model bijective_toBase_model
    relOpen_model (mapsTo_univ _ _)
    (((contDiff_fst.add contDiff_const).sub contDiff_const).prodMk contDiff_snd)

/-- Two translation strong bundle charts are compatible. -/
theorem chart_compatible (a b : Fin n → ℝ) : (chart (k := k) a).Compatible (chart b) := by
  have hs : ∀ a b : Fin n → ℝ, strongShiftOne ((chart (k := k) a).overlap (chart b)) = univ :=
    fun a b => by rw [chart_overlap]; rfl
  have hsf : ∀ a b : Fin n → ℝ,
      shiftFiber ((chart (k := k) a).transition (chart b)) =
        fun p : (Fin n → ℝ) × (Fin k → ℝ) => (p.1 + a - b, p.2) :=
    fun a b => funext fun p => Prod.ext rfl (by
      change invFun ((rnSc k).toBase 1) ((rnSc k).toBase 1 p.2) = p.2
      exact leftInverse_invFun ((rnSc k).toBase_injective 1) p.2)
  have hr : ∀ v : Fin k → ℝ, v ∈ range ((rnSc k).toBase 1) := fun v =>
    (bijective_toBase_const _ 1).2 v
  refine ⟨?_, ?_, ?_, ?_, fun _ _ _ => hr _, fun _ _ _ => hr _⟩
  · rw [chart_overlap, chart_overlap]; exact isScSmoothRetractMap_transition a b
  · rw [chart_overlap, chart_overlap]; exact isScSmoothRetractMap_transition b a
  · rw [hs, hs, hsf]; exact isScSmoothRetractMap_transition a b
  · rw [hs, hs, hsf]; exact isScSmoothRetractMap_transition b a

variable (n k) in
/-- **The trivial strong bundle** `ℝⁿ × ℝᵏ → ℝⁿ`, with the translation charts. -/
def bundle : StrongBundle (rnPolyfold n) (proj n k) where
  continuous := continuous_fst
  surjective x := ⟨(x, 0), rfl⟩
  banachable x := ⟨Fin k → ℝ, inferInstance, inferInstance, inferInstance,
    ⟨{ toLinearEquiv := (fibEquiv x).linearEquiv ℝ
       continuous_toFun := continuous_snd.comp continuous_subtype_val
       continuous_invFun :=
        (continuous_const.prodMk continuous_id).subtype_mk fun _ => rfl }⟩⟩
  atlas :=
    { charts := range chart
      compatible := by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        exact chart_compatible a b
      cover := fun y => ⟨chart 0, mem_range_self 0, mem_univ y⟩ }

lemma isChart_chart (a : Fin n → ℝ) : (bundle n k).IsChart (chart a) :=
  StrongBundle.isChart_of_mem (B := bundle n k) (mem_range_self a)

/-! ### Conjugation to a basic germ in finite dimensions -/

/-- The zero sc-Banach space `ℝ⁰`, the `W` of the basic germs below. -/
abbrev zeroSc : ScBanach := ScBanach.const (Fin 0 → ℝ)

instance (m : ℕ) : Subsingleton (zeroSc m) := inferInstanceAs (Subsingleton (Fin 0 → ℝ))

lemma bijective_toBase_param (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (m : ℕ) : Bijective ((ScBanach.paramProd P zeroSc).toBase m) :=
  bijective_toBase_prod (bijective_toBase_const _) (bijective_toBase_const _) m

/-- **A `C^∞` map `κ : ℝⁿ → ℝᵏ` with `κ(0) = 0` is conjugated to a basic germ** (Definition 3.11,
second paragraph): with `W = 0`, `Ψ(u, v) = ((u, 0), (v, 0))` and the basic germ
`h(a, w) = (κ(a), w)` (`B = 0`). -/
theorem isConjugateToBasicGerm_of_contDiff {κ : (Fin n → ℝ) → (Fin k → ℝ)}
    (hκ : ContDiff ℝ ∞ κ) (hκ0 : κ 0 = 0) :
    IsConjugateToBasicGerm (E := rnSc n) (F := rnSc k) univ κ := by
  have hU' : IsRelOpenInQuadrant (ScBanach.paramProd (Fin n → ℝ) zeroSc) (univ ×ˢ univ) univ := by
    rw [← univ_prod_univ]; exact (rn_relOpen_univ n).prod_univ zeroSc
  have hO : ∃ O : Set ((ScBanach.paramProd (Fin n → ℝ) zeroSc) 0), IsOpen O ∧
      (univ : Set ((ScBanach.paramProd (Fin n → ℝ) zeroSc) 0)) = O ∩ univ ×ˢ univ :=
    ⟨univ, isOpen_univ, by rw [univ_inter, univ_prod_univ]⟩
  have hQ : IsQuadrantLike (ScBanach.paramProd (Fin n → ℝ) zeroSc) (univ ×ˢ univ) :=
    (isQuadrantLike_const_iff.2 ⟨mem_univ _, convex_univ, by
      rw [interior_univ]; exact univ_nonempty⟩).paramProd zeroSc
  have hdom : IsScDomain ((rnSc n).prod (rnSc k)) (univ ×ˢ univ) := by
    rw [univ_prod_univ]; exact isScDomain_univ _
  have hbE : ∀ m, Bijective (((rnSc n).prod (rnSc k)).toBase m) := bijective_toBase_model
  have hbE1 : ∀ m, Bijective (((rnSc n).prod (rnSc k).shift).toBase m) :=
    bijective_toBase_prod (bijective_toBase_const _)
      (bijective_toBase_shift (bijective_toBase_const _))
  have hbE' : ∀ m, Bijective (((ScBanach.paramProd (Fin n → ℝ) zeroSc).prod
      (ScBanach.paramProd (Fin k → ℝ) zeroSc)).toBase m) :=
    bijective_toBase_prod (bijective_toBase_param _) (bijective_toBase_param _)
  have hbE'1 : ∀ m, Bijective (((ScBanach.paramProd (Fin n → ℝ) zeroSc).prod
      (ScBanach.paramProd (Fin k → ℝ) zeroSc).shift).toBase m) :=
    bijective_toBase_prod (bijective_toBase_param _)
      (bijective_toBase_shift (bijective_toBase_param _))
  have hdom' : IsScDomain ((ScBanach.paramProd (Fin n → ℝ) zeroSc).prod
      (ScBanach.paramProd (Fin k → ℝ) zeroSc)) (univ ×ˢ univ) := by
    rw [univ_prod_univ]; exact isScDomain_univ _
  have hdom'1 : IsScDomain ((ScBanach.paramProd (Fin n → ℝ) zeroSc).prod
      (ScBanach.paramProd (Fin k → ℝ) zeroSc).shift) (univ ×ˢ univ) := by
    rw [univ_prod_univ]; exact isScDomain_univ _
  have hdom1 : IsScDomain ((rnSc n).prod (rnSc k).shift) (univ ×ˢ univ) := by
    rw [univ_prod_univ]; exact isScDomain_univ _
  -- the inclusions `F_1 → F_0` are the identity
  have hι : ∀ v : Fin k → ℝ, (rnSc k).toBase 1 v = v := ScBanach.const_toBase _ 1
  have hι' : ∀ q : (ScBanach.paramProd (Fin k → ℝ) zeroSc) 1,
      (ScBanach.paramProd (Fin k → ℝ) zeroSc).toBase 1 q = q := fun q =>
    Prod.ext rfl (Subsingleton.elim _ _)
  let Ψ : (Fin n → ℝ) × (Fin k → ℝ) → ((Fin n → ℝ) × (Fin 0 → ℝ)) × ((Fin k → ℝ) × (Fin 0 → ℝ)) :=
    fun p => ((p.1, 0), (p.2, 0))
  let Ψ' : ((Fin n → ℝ) × (Fin 0 → ℝ)) × ((Fin k → ℝ) × (Fin 0 → ℝ)) → (Fin n → ℝ) × (Fin k → ℝ) :=
    fun q => (q.1.1, q.2.1)
  have hΨ : ContDiff ℝ ∞ Ψ :=
    (contDiff_fst.prodMk contDiff_const).prodMk (contDiff_snd.prodMk contDiff_const)
  have hΨ' : ContDiff ℝ ∞ Ψ' := contDiff_fst.fst.prodMk contDiff_snd.fst
  refine ⟨Fin n → ℝ, Fin k → ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, zeroSc, univ, univ, Ψ, Ψ', ScNbhdGerm.ofSet hO (mem_univ 0),
    fun p => (κ p.1, p.2), fun _ => 0, isPartialQuadrant_univ _, hU', ?_, rfl, subset_univ _,
    ?_, Eventually.of_forall fun _ _ => rfl⟩
  · refine ⟨⟨fun _ _ => ⟨mem_univ _, mem_univ _⟩, fun _ _ _ _ => rfl,
      fun _ _ => ⟨fun _ _ => Prod.ext rfl (Subsingleton.elim _ _),
        fun _ _ => Prod.ext rfl (Subsingleton.elim _ _)⟩,
      fun m l _ _ _ _ _ _ => ⟨(bijective_toBase_param _ m).2 _, (bijective_toBase_param _ l).2 _⟩,
      isScSmooth_of_bijective_toBase hbE hbE' hdom (f := Ψ) hΨ.contDiffOn,
      ?_⟩, ⟨fun _ _ => ⟨mem_univ _, mem_univ _⟩, fun _ _ _ _ => rfl,
      fun _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩,
      fun m l _ _ _ _ _ _ => ⟨(bijective_toBase_const _ m).2 _, (bijective_toBase_const _ l).2 _⟩,
      isScSmooth_of_bijective_toBase hbE' hbE hdom' (f := Ψ') hΨ'.contDiffOn, ?_⟩,
      fun _ _ => rfl, fun q _ => Prod.ext (Prod.ext rfl (Subsingleton.elim _ _))
        (Prod.ext rfl (Subsingleton.elim _ _))⟩
    · refine (isScSmooth_of_bijective_toBase hbE1 hbE'1 hdom1 (f := Ψ)
        hΨ.contDiffOn).congr hdom1 fun p _ => ?_
      refine Prod.ext rfl ?_
      change ((p.2, 0) : (ScBanach.paramProd (Fin k → ℝ) zeroSc) 1) =
        invFun ((ScBanach.paramProd (Fin k → ℝ) zeroSc).toBase 1) ((rnSc k).toBase 1 p.2, 0)
      rw [hι, ← hι' (p.2, 0), leftInverse_invFun
        ((ScBanach.paramProd (Fin k → ℝ) zeroSc).toBase_injective 1)]
      exact hι' _
    · refine (isScSmooth_of_bijective_toBase hbE'1 hbE1 hdom'1 (f := Ψ')
        hΨ'.contDiffOn).congr hdom'1 fun p _ => ?_
      refine Prod.ext rfl ?_
      change (p.2.1 : (rnSc k) 1) =
        invFun ((rnSc k).toBase 1) ((ScBanach.paramProd (Fin k → ℝ) zeroSc).toBase 1 p.2).1
      rw [hι', ← hι p.2.1, leftInverse_invFun ((rnSc k).toBase_injective 1)]
      exact hι _
  · refine ⟨?_, Prod.ext hκ0 rfl, fun x _ => (sub_zero _).symm, ?_⟩
    · exact IsScSmooth.isScSmoothGerm hQ hO (mem_univ 0)
        (isScSmooth_of_bijective_toBase (bijective_toBase_param _) (bijective_toBase_param _)
          (isScDomain_univ _) ((hκ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn)
    · refine ⟨?_, rfl, fun ε hε m => ⟨1, one_pos, fun a _ _ w w' _ _ => ⟨mem_univ _, ?_⟩⟩⟩
      · exact IsScSmooth.isScSmoothGerm hQ hO (mem_univ 0)
          (isScSmooth_of_bijective_toBase (bijective_toBase_param _) (bijective_toBase_const _)
            (isScDomain_univ _) contDiffOn_const) 0
      · simp only [Subsingleton.elim w w', sub_self, norm_zero, mul_zero, le_refl]

/-! ### The graph section `x ↦ (x, φ(x))` -/

variable {φ : (Fin n → ℝ) → (Fin k → ℝ)}

/-- The section `x ↦ (x, φ(x))` of `ℝⁿ × ℝᵏ → ℝⁿ`. -/
def graphSection (φ : (Fin n → ℝ) → (Fin k → ℝ)) (x : Fin n → ℝ) : (Fin n → ℝ) × (Fin k → ℝ) :=
  (x, φ x)

lemma isSection_graphSection : IsSection (proj n k) (graphSection φ) := fun _ => rfl

lemma rnPolyfold_smoothSet : (rnPolyfold n).smoothSet = univ := by
  refine eq_univ_of_forall fun x => mem_iInter.2 fun m => ?_
  rw [rnPolyfold_levelSet]; exact mem_univ x

/-- `(f, x)` is zero iff `φ(x) = 0`. -/
lemma isZeroAt_graphSection_iff {x : Fin n → ℝ} :
    IsZeroAt (proj n k) (graphSection φ) x ↔ φ x = 0 := by
  constructor
  · intro h
    exact congrArg (fun y : proj n k ⁻¹' {x} => fibEquiv x y) (Subtype.ext h :
      (⟨graphSection φ x, rfl⟩ : proj n k ⁻¹' {x}) = 0)
  · intro h
    change (graphSection φ x) = ((0 : proj n k ⁻¹' {x}) : (Fin n → ℝ) × (Fin k → ℝ))
    refine Prod.ext ((0 : proj n k ⁻¹' {x}).2).symm ?_
    rw [graphSection, h]; rfl

lemma isTameChart_chart (a : Fin n → ℝ) : (bundle n k).IsTameChart (chart a) :=
  StrongBundle.isTameChart_of_eqOn_id (isChart_chart a) fun _ _ => rfl

/-- **The graph section is sc-smooth.** -/
theorem isScSmoothSection_graphSection (hφ : ContDiff ℝ ∞ φ) :
    (bundle n k).IsScSmoothSection (graphSection φ) := by
  refine ⟨isSection_graphSection, MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ
    (continuous_id.prodMk hφ.continuous).continuousOn fun x _ => ?_⟩
  refine ⟨rnChart n 0, (chart 0).toMChart continuous_fst, univ, isChart_rnChart 0,
    (bundle n k).isChart_toMChart (mem_range_self 0), isOpen_univ, mem_univ x,
    fun z _ => ⟨mem_univ _, mem_univ _⟩, fun z _ => mem_univ _, ?_⟩
  have himg : (rnChart n 0).toPartialEquiv '' univ = univ :=
    image_univ_of_surjective (Equiv.subRight (0 : Fin n → ℝ)).surjective
  rw [himg]
  exact isScSmoothRetractMap_of_bijective_toBase (bijective_toBase_const _)
    bijective_toBase_model (rn_relOpen_univ n)
    (fun u _ => ⟨_, ⟨mem_univ _, mem_univ _⟩, rfl⟩)
    (((contDiff_id.add contDiff_const).sub contDiff_const).prodMk
      (hφ.comp (contDiff_id.add contDiff_const)))

/-- The principal part of the graph section in the chart centred at `x₀`: `u ↦ φ(u + x₀)`. -/
lemma principal_graphSection (x₀ : Fin n → ℝ) (u : Fin n → ℝ) :
    (chart (k := k) x₀).principal (graphSection φ) u = φ (u + x₀) := rfl

/-- The base retraction `r` of the translation charts is the identity, with derivative `1`. -/
lemma scDeriv_r (a : Fin n → ℝ) :
    scDeriv (chart (k := k) a).U (StrongRetr.r (chart (k := k) a).R) 0 =
      ContinuousLinearMap.id ℝ _ := by
  have := scDeriv_univ_const (V := Fin n → ℝ) (V' := Fin n → ℝ) contDiff_id 0
  rw [fderiv_id] at this
  exact this

/-- The principal part `u ↦ φ(u + x₀)` of the graph section in the chart centred at `x₀`. -/
def loc (φ : (Fin n → ℝ) → (Fin k → ℝ)) (x₀ : Fin n → ℝ) : (Fin n → ℝ) → (Fin k → ℝ) :=
  fun u => φ (u + x₀)

lemma contDiff_loc (hφ : ContDiff ℝ ∞ φ) (x₀ : Fin n → ℝ) : ContDiff ℝ ∞ (loc φ x₀) :=
  hφ.comp (contDiff_id.add contDiff_const)

lemma scDeriv_loc (hφ : ContDiff ℝ ∞ φ) (x₀ : Fin n → ℝ) :
    scDeriv (F := (chart (k := k) x₀).F) (chart (k := k) x₀).U (loc φ x₀) 0 = fderiv ℝ φ x₀ := by
  have := scDeriv_univ_const (V := Fin n → ℝ) (V' := Fin k → ℝ) (contDiff_loc hφ x₀) 0
  have h2 : fderiv ℝ (loc φ x₀) 0 = fderiv ℝ φ x₀ := by
    rw [show loc φ x₀ = fun u => φ (u + x₀) from rfl, fderiv_comp_add_right, zero_add]
  rw [h2] at this
  exact this

/-- Condition (3) of Definition 3.4 when `ker Dr(0) = 0` and `ker ρ(0) = 0`. -/
lemma exists_kerEquiv_of_injective {M M' : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup M'] [NormedSpace ℝ M']
    (A : M →L[ℝ] M) (B : M' →L[ℝ] M') (D : M →L[ℝ] M') (hA : ∀ v, A v = 0 → v = 0)
    (hB : ∀ v, B v = 0 → v = 0) :
    ∃ Φ : LinearMap.ker (A : M →ₗ[ℝ] M) ≃L[ℝ] LinearMap.ker (B : M' →ₗ[ℝ] M'),
      ∀ v, (Φ v : M') = D (v : M) := by
  have : Subsingleton (LinearMap.ker (A : M →ₗ[ℝ] M)) :=
    ⟨fun a b => Subtype.ext ((hA a a.2).trans (hA b b.2).symm)⟩
  have : Subsingleton (LinearMap.ker (B : M' →ₗ[ℝ] M')) :=
    ⟨fun a b => Subtype.ext ((hB a a.2).trans (hB b b.2).symm)⟩
  refine ⟨{ toLinearEquiv := LinearEquiv.ofSubsingleton _ _
            continuous_toFun := continuous_of_const fun _ _ => Subsingleton.elim _ _
            continuous_invFun := continuous_of_const fun _ _ => Subsingleton.elim _ _ },
    fun v => ?_⟩
  rw [hA v v.2, map_zero]
  exact hB _ (LinearMap.mem_ker.1 (Subtype.prop _))

/-- Every subspace is in good position to the partial cone `C = E` (any complement is good). -/
lemma isInGoodPositionIn_univ {E : ScBanach} (N : Submodule ℝ (E 0)) :
    IsInGoodPositionIn E ⊤ univ N := by
  obtain ⟨P, hP⟩ := Submodule.exists_isCompl N
  refine ⟨le_top, ⟨0, ?_⟩, P, le_top, hP.inf_eq_bot, hP.sup_eq_top, 1, one_pos,
    fun _ _ _ _ _ => iff_of_true (mem_univ _) (mem_univ _)⟩
  rw [preimage_univ, interior_univ]; exact mem_univ _

/-- **The germ data of the graph section in the chart centred at `x₀`**: the filled version is the
principal part `g = loc φ x₀` itself (the retraction is the identity), the sc⁺-section is the
constant `φ(x₀)`, and `g − φ(x₀)` is conjugated to a basic germ
(`isConjugateToBasicGerm_of_contDiff`). -/
theorem germData_graphSection (hφ : ContDiff ℝ ∞ φ) (x₀ : Fin n → ℝ) :
    IsFilledVersion (chart (k := k) x₀).relOpen (chart x₀).isRetraction (mem_univ 0)
        ((chart x₀).principal (graphSection φ)) (loc φ x₀) ∧
      IsScSmooth (E := rnSc n) (F := (rnSc k).shift) univ (fun _ => (φ x₀ : (rnSc k).shift 0)) ∧
      (rnSc k).toBase 1 (φ x₀) = loc φ x₀ 0 ∧
      IsConjugateToBasicGerm (E := rnSc n) (F := rnSc k) univ (fun u => loc φ x₀ u - φ x₀) := by
  refine ⟨⟨isScSmooth_of_bijective_toBase (bijective_toBase_const _) (bijective_toBase_const _)
      (isScDomain_univ _) (contDiff_loc hφ x₀).contDiffOn, ⟨Eventually.of_forall fun _ _ => rfl,
      Eventually.of_forall fun y _ _ => ⟨y, mem_univ y, rfl⟩, ?_,
      exists_kerEquiv_of_injective _ _ _ (fun v hv => by rwa [scDeriv_r] at hv)
        fun v hv => hv⟩⟩,
    isScSmooth_of_bijective_toBase (bijective_toBase_const _)
      (bijective_toBase_shift (bijective_toBase_const _)) (isScDomain_univ _) contDiffOn_const,
    by rw [ScBanach.const_toBase]; exact congrArg φ (zero_add x₀).symm, ?_⟩
  · refine ((isScSmooth_of_bijective_toBase (bijective_toBase_const _) (bijective_toBase_const _)
      (isScDomain_univ _) (contDiffOn_const (c := (0 : Fin k → ℝ)))).congr (isScDomain_univ _)
      fun y _ => ?_).isSc1
    change (0 : Fin k → ℝ) = loc φ x₀ y - loc φ x₀ y
    rw [sub_self]
  · refine isConjugateToBasicGerm_of_contDiff ((contDiff_loc hφ x₀).sub contDiff_const) ?_
    change φ (0 + x₀) - φ x₀ = 0
    rw [zero_add, sub_self]

/-- **Tame germ data of the graph section at every point** (Definition 3.50). -/
theorem isScFredholmGermTame_graphSection_wholeChart (hφ : ContDiff ℝ ∞ φ) (x₀ : Fin n → ℝ) :
    (bundle n k).IsScFredholmGermTameWholeChart (graphSection φ) x₀ := by
  obtain ⟨hfill, hs, hs0, hconj⟩ := germData_graphSection (k := k) hφ x₀
  exact ⟨by rw [rnPolyfold_smoothSet]; exact mem_univ x₀, chart x₀, isTameChart_chart x₀,
    mem_univ x₀, sub_self x₀, mem_univ 0, loc φ x₀, fun _ => φ x₀, hfill, hs, hs0, hconj⟩

/-- **The graph section is in good position in a tame chart at every zero `x₀` where `Dφ(x₀)` is
onto** (Definition 3.53): `Tf̃(0) = Dφ(x₀)` is onto `ρ(0)F = ℝᵏ`, and its kernel is in good
position to the partial cone `C = ℝⁿ` (every subspace is: any complement is good).  (Good position
does not use `φ(x₀) = 0`; Definition 3.53 is only applied at zeros.) -/
theorem isGoodPositionGermTame_graphSection_wholeChart (hφ : ContDiff ℝ ∞ φ) {x₀ : Fin n → ℝ}
    (hsurj : Surjective (fderiv ℝ φ x₀)) :
    (bundle n k).IsGoodPositionGermTameWholeChart (graphSection φ) x₀ := by
  obtain ⟨hfill, hs, hs0, hconj⟩ := germData_graphSection (k := k) hφ x₀
  have htop : rangeS (scDeriv (chart (k := k) x₀).U (StrongRetr.r (chart (k := k) x₀).R) 0) =
      ⊤ := by
    rw [rangeS, scDeriv_r]; exact LinearMap.range_id
  refine ⟨by rw [rnPolyfold_smoothSet]; exact mem_univ x₀, chart x₀, isTameChart_chart x₀,
    mem_univ x₀, sub_self x₀, mem_univ 0, loc φ x₀, fun _ => φ x₀, hfill, hs, hs0, hconj,
    fun y _ => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hsurj y
    refine ⟨x, by rw [htop]; exact Submodule.mem_top, ?_⟩
    rw [scDeriv_loc hφ x₀]; exact hx
  · rw [htop]; exact isInGoodPositionIn_univ _

/-! ### The graph section is sc-Fredholm, and Theorem 3.57 applies -/

/-- **The graph section of a `C^∞` map is an sc-Fredholm section** (Definition 3.14): sc-smooth,
regularizing (every point is smooth), with (tame) germ data at every point. -/
theorem isScFredholmSection_graphSection_wholeChart (hφ : ContDiff ℝ ∞ φ) :
    (bundle n k).IsScFredholmSectionWholeChart (graphSection φ) where
  isScSmooth := isScSmoothSection_graphSection hφ
  regularizing m x _ _ := by rw [rnPolyfold_levelSet]; exact mem_univ x
  germ x _ := (isScFredholmGermTame_graphSection_wholeChart hφ x).isScFredholmGerm

/-- The graph section has tame germ data at every point (Definition 3.51). -/
theorem isScFredholmSectionTame_graphSection_wholeChart (hφ : ContDiff ℝ ∞ φ) :
    (bundle n k).IsScFredholmSectionTameWholeChart (graphSection φ) where
  toIsScFredholmSectionWholeChart := isScFredholmSection_graphSection_wholeChart hφ
  germTame x _ := isScFredholmGermTame_graphSection_wholeChart hφ x

/-- **The hypotheses of Theorem 3.57 hold** for the graph section of a `C^∞` map `φ : ℝⁿ → ℝᵏ`
with `0` a regular value: sc-Fredholm, and in good position in a tame chart at every zero. -/
theorem hypotheses_theorem_3_57_graphSection_wholeChart (hφ : ContDiff ℝ ∞ φ)
    (hreg : ∀ x, φ x = 0 → Surjective (fderiv ℝ φ x)) :
    (bundle n k).IsScFredholmSectionWholeChart (graphSection φ) ∧
      ∀ x, IsZeroAt (proj n k) (graphSection φ) x →
        (bundle n k).IsGoodPositionGermTameWholeChart (graphSection φ) x :=
  ⟨isScFredholmSection_graphSection_wholeChart hφ, fun x hx =>
    isGoodPositionGermTame_graphSection_wholeChart hφ (hreg x (isZeroAt_graphSection_iff.1 hx))⟩

/-- **Theorem 3.57 for the trivial bundle (the regular value theorem)**: if `φ : ℝⁿ → ℝᵏ` is `C^∞`
with `0` a regular value and `φ⁻¹(0) ≠ ∅`, the solution set of the graph section, `φ⁻¹(0)`, is a
tame sub-M-polyfold of `ℝⁿ` with the structure of a manifold with corners, of locally constant
dimension.  The point is that the hypotheses of `theorem_3_57_wholeChart` are met (they are not vacuous). -/
theorem theorem_3_57_trivialBundle (hφ : ContDiff ℝ ∞ φ)
    (hreg : ∀ x, φ x = 0 → Surjective (fderiv ℝ φ x)) (hne : ∃ x, φ x = 0) :
    ∃ hsub : (rnPolyfold n).IsSubMPolyfold (solutionSet (proj n k) (graphSection φ)),
      haveI := (rnPolyfold n).paracompactSpace_subtype (solutionSet (proj n k) (graphSection φ))
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        ∀ x ∈ solutionSet (proj n k) (graphSection φ), ∃ d : ℕ,
          ∃ D : (rnPolyfold n).TangentGermChart (solutionSet (proj n k) (graphSection φ)) x d,
            D.IsRegular ∧ ∀ y ∈ solutionSet (proj n k) (graphSection φ) ∩ D.φ.source,
              ∀ (n' : ℕ) (_ : (rnPolyfold n).TangentGermChart
                (solutionSet (proj n k) (graphSection φ)) y n'), n' = d := by
  obtain ⟨hf, hall⟩ := hypotheses_theorem_3_57_graphSection_wholeChart hφ hreg
  obtain ⟨x, hx⟩ := hne
  exact theorem_3_57_wholeChart hf hall ⟨x, isZeroAt_graphSection_iff.2 hx⟩

/-- **The hypotheses hold for every surjective linear map** `L : ℝⁿ → ℝᵏ` (the solution set is the
subspace `ker L`). -/
theorem hypotheses_theorem_3_57_linear_wholeChart (L : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ)) (hL : Surjective L) :
    (bundle n k).IsScFredholmSectionWholeChart (graphSection L) ∧
      ∀ x, IsZeroAt (proj n k) (graphSection L) x →
        (bundle n k).IsGoodPositionGermTameWholeChart (graphSection L) x :=
  hypotheses_theorem_3_57_graphSection_wholeChart L.contDiff fun x _ => by rw [L.fderiv]; exact hL

/-- The linear map `ℝ² → ℝ¹`, `(x, y) ↦ x`. -/
def exampleMap : (Fin 2 → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj 0

/-- **A concrete instance of Theorem 3.57**: for the section `(x, y) ↦ ((x, y), x)` of the trivial
bundle `ℝ² × ℝ → ℝ²`, the solution set (the line `x = 0`) is a sub-M-polyfold of `ℝ²` with the
structure of a manifold with corners. -/
theorem theorem_3_57_example :
    ∃ hsub : (rnPolyfold 2).IsSubMPolyfold (solutionSet (proj 2 1) (graphSection exampleMap)),
      haveI := (rnPolyfold 2).paracompactSpace_subtype
        (solutionSet (proj 2 1) (graphSection exampleMap))
      (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc := by
  have hsurj : Surjective exampleMap := fun y =>
    ⟨fun _ => y 0, funext fun j => by fin_cases j; rfl⟩
  obtain ⟨hsub, -, h2, -⟩ := theorem_3_57_trivialBundle exampleMap.contDiff
    (fun x _ => by rw [exampleMap.fderiv]; exact hsurj) ⟨0, map_zero _⟩
  exact ⟨hsub, h2⟩

end TrivialBundle

end Polyfold
