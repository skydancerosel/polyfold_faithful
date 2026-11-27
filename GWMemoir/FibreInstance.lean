import GWMemoir.Fibres
import GWMemoir.CauchyRiemannFredholm
import GWMemoir.SphereStability

/-!
# Fibre representations for the GW data

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (p. 7) and §1.3
(p. 8), with the fibre spaces of `GWMemoir.Fibres`.

## What is formalized

* **Point-supported fibre elements** (`exists_pointFibreElement`): on a stable map without nodes
  and a target of positive dimension, for every point `x₀` and every class `(k, δ)` there is a
  nonzero fibre element (`IsFibreElement`) vanishing off `x₀`; its representatives in every atlas
  are `0` (`isFormRep_zero_of_point`).  Hence **no map injective on all fibre elements factors
  through the fibre spaces** (`not_factor_of_injOn_fibreElements`): the injectivity on fibre
  elements asks to separate forms which agree almost everywhere.  This is why
  `FibreRepresentation` (`GWMemoir.FibreRepresentation`) is defined on the forms with
  representatives and asks the injectivity on continuous fibre elements.
* `gwSub Ob`: the full subcategory of stable maps on a set `Ob` (finite isomorphism sets), with
  the inclusion as label `subLabel`.
* `PullbackBounded`: the change of coordinates for the fibres, the named proposition of analysis
  (the pull-back by an isomorphism is bounded between the fibre spaces of two atlases).  Witness:
  isomorphisms that are the identity (`pullbackBounded_of_id`).
* `fibreFunctor`: the functor `μ : gwSub Ob → Ban`, `μ(α) = ` the fibre of `α` over a chosen atlas,
  `μ(φ) = (φ^*)⁻¹`; the functor laws are proved from the uniqueness of the representatives and
  their density.
* **`fibreRepresentation`**: the instance on every full subcategory of stable maps without nodes,
  given `PullbackBounded`.  **`constFibreRepresentation`**: on the category of the constant maps
  from the three-pointed sphere, with no named proposition; `constFibreRepresentation_dbar`:
  `∂̄_J` of a constant map is `0` in it.
* **`memoir_theorem_1_11_fibre_nonvacuous`**: on the constant maps from the three-pointed sphere,
  the hypotheses of `memoir_theorem_1_11` on the fibre (the label, a Banach functor, a fibre
  representation, `DbarInDom`, `DbarRegularC`) hold together, with a nonempty category;
  `memoir_theorem_1_11_fibre_const`: they hold for every vector bundle GCT over the GW base of the
  constant maps whose Banach functor is `fibreFunctor`.

## Readings

* An identification of the fibre asking `ι_a` linear and natural on all forms and injective on all
  fibre elements has no instance through the fibre spaces: fibre elements are functions on `S`,
  while the Sobolev norms of p. 7 do not see a change on a null set.  `FibreRepresentation`
  states the identification on the classes, with the injectivity on continuous forms (`∂̄_J u` is
  continuous for `u` of class `(3, δ₀)`).
* The objects of `gwSub` live in `Type 1`; the fibres are lifted (`ULift`).
* `PullbackBounded` is the change of charts of `S` and of the trivializations of `u*TQ` in
  `H^{2,δ₀}`, as for the sections; at the nodal points it uses `δ₀ < 2π`.
* Not built here: the topology on `|E_μ|` of Definition 17.7.1 (a vector bundle GCT), the
  comparison of `μ` with the bundle of Theorem 1.10, atlases at stable maps with nodes, and the
  injectivity on the neck blocks (the polar coordinates are local diffeomorphisms).  For the
  base, a uniformizer construction on the constant maps (Definition 19.1.3) with Theorems 3.13,
  3.22, 1.6 is not built either; `memoir_theorem_1_11_fibre_const` takes the base as given.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Set Function Filter Topology MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-! ## 1. Point-supported forms -/

section Point

lemma cyl_subsingleton {s : Set (ℝ × ℝ)} (hs : s.Subsingleton) : cyl s = 0 := by
  rcases hs.eq_empty_or_singleton with rfl | ⟨p, rfl⟩
  · exact measure_empty
  · refine measure_mono_null (show ({p} : Set (ℝ × ℝ)) ⊆ {p.1} ×ˢ univ from
      singleton_subset_iff.2 ⟨mem_singleton p.1, mem_univ p.2⟩) ?_
    rw [cyl, Measure.prod_prod, Real.volume_singleton, zero_mul]

lemma memH_of_ae_zero {k : ℕ} {δ : ℝ} {f : ℝ × ℝ → ℝ} (h : f =ᵐ[cyl] 0) : MemH k δ f :=
  fun a b hab => by
    obtain ⟨g, hg, hgl⟩ := memH_zero k δ a b hab
    exact ⟨g, hg.congr_ae h.symm (ae_eq_refl _), hgl⟩

lemma place_injective {m : ℕ} (X : NodalSurface m) (x : X.S) {ε : ℝ} (hε : ε ≠ 0) :
    Injective (X.place x ε) := by
  intro p p' h
  unfold NodalSurface.place at h
  have h2 := smul_right_injective E2 hε (add_left_cancel h)
  have a := congrArg (fun w : E2 => w 0) h2
  have b := congrArg (fun w : E2 => w 1) h2
  simp only [PiLp.add_apply, PiLp.single_apply] at a b
  norm_num at a b
  exact Prod.ext a (by linarith)

/-- A cut-off disc expression of a function of the point vanishes almost everywhere if the
function vanishes off one point. -/
lemma discExpr_ae_zero {m : ℕ} {X : NodalSurface m} (x : X.S) {ε : ℝ} (hε : ε ≠ 0)
    (hs : ∀ p : ℝ × ℝ, p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 < 1 / 8 →
      X.place x ε p ∈ (extChartAt 𝓘(ℝ, E2) x).target)
    (x₀ : X.S) (G : X.S → ℝ) (hG : ∀ y, y ≠ x₀ → G y = 0) :
    (fun p => discCut p * G ((extChartAt 𝓘(ℝ, E2) x).symm (X.place x ε p))) =ᵐ[cyl] 0 := by
  refine ae_iff.2 (measure_mono_null ?_ (cyl_subsingleton (s :=
    {p | X.place x ε p = extChartAt 𝓘(ℝ, E2) x x₀}) fun p hp p' hp' =>
      place_injective X x hε (hp.trans hp'.symm)))
  intro p hp
  simp only [Pi.zero_apply, mem_ofPred_eq] at hp ⊢
  by_cases hr : p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 < 1 / 8
  · by_cases hy : (extChartAt 𝓘(ℝ, E2) x).symm (X.place x ε p) = x₀
    · rw [← hy, (extChartAt 𝓘(ℝ, E2) x).right_inv (hs p hr)]
    · exact absurd (by rw [hG _ hy, mul_zero]) hp
  · exact absurd (by rw [discCut, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]) hp

variable (J : AlmostComplexStructure E Q)

/-- The anti-linear part `½ (L + J(y) ∘ L ∘ j_x)` of a linear map `L`. -/
def antiPart {m : ℕ} (X : NodalSurface m) (y : Q) (x : X.S) (L : E2 →L[ℝ] E) : E2 →L[ℝ] E :=
  (1 / 2 : ℝ) • (L + (J.J y).comp (L.comp (X.j.J x)))

lemma antiPart_mem {m : ℕ} (X : NodalSurface m) (y : Q) (x : X.S) (L : E2 →L[ℝ] E) :
    antiPart J X y x L ∈ X.antiLinearForms J y x := by
  rw [NodalSurface.mem_antiLinearForms]
  intro v
  simp only [antiPart, smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, map_smul, map_add, J.J_J, X.j.J_J, map_neg]
  module

/-- `½ (λ ⊗ e + J (λ ⊗ e) j) ≠ 0` for `e ≠ 0`, `λ` the first coordinate: `J` has no real
eigenvalue. -/
lemma antiPart_ne_zero {m : ℕ} (X : NodalSurface m) (y : Q) (x : X.S) {e : E} (he : e ≠ 0) :
    antiPart J X y x ((EuclideanSpace.proj 0 : E2 →L[ℝ] ℝ).smulRight e) ≠ 0 := by
  intro h
  set b := (X.j.J x (EuclideanSpace.single 0 1)) 0
  have h1 : e + b • J.J y e = 0 := by
    have := congrArg (fun L => (2 : ℝ) • L (EuclideanSpace.single 0 1)) h
    simp only [antiPart, smul_apply, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
      zero_apply, smul_zero, smul_smul] at this
    simpa [b] using this
  have h2 : J.J y e - b • e = 0 := by
    have := congrArg (J.J y) h1
    simp only [map_add, map_smul, J.J_J, map_zero] at this
    rw [← this]; module
  have h3 : (1 + b ^ 2) • e = 0 := by linear_combination (norm := module) h1 - b • h2
  rcases smul_eq_zero.1 h3 with h4 | h4
  · nlinarith [sq_nonneg b]
  · exact he h4

variable {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ}

open Classical in
/-- The form `ξ(x₀) = ½ (λ ⊗ e + J λ ⊗ e j)`, `ξ(x) = 0` for `x ≠ x₀`. -/
def ptForm (α : StableMap om m k δ) (x₀ : α.dom.S) (e : E) : Form E α.dom := fun x =>
  if x = x₀ then antiPart J α.dom (α.u x₀) x₀ ((EuclideanSpace.proj 0 : E2 →L[ℝ] ℝ).smulRight e)
  else 0

lemma ptForm_of_ne (α : StableMap om m k δ) (x₀ : α.dom.S) (e : E) {x : α.dom.S} (hx : x ≠ x₀) :
    ptForm J α x₀ e x = 0 := if_neg hx

/-- **A point-supported fibre element**: on a stable map without nodes, the form `ptForm` is a
fibre element of every class `(k', δ')`. -/
theorem isFibreElement_ptForm (α : StableMap om m k δ) (hX : α.dom.nodes = ∅) (x₀ : α.dom.S)
    (e : E) (k' : ℕ) (δ' : ℝ) : IsFibreElement J α k' δ' (ptForm J α x₀ e) := by
  refine ⟨fun x _ => ?_, fun p hp => by rw [hX] at hp; exact absurd hp (notMem_empty p),
    fun x hx => ?_⟩
  · by_cases hx : x = x₀
    · subst hx
      rw [ptForm, if_pos rfl]
      exact antiPart_mem J _ _ _ _
    · rw [ptForm_of_ne J α x₀ e hx]; exact Submodule.zero_mem _
  · obtain ⟨ε, hε, hs, -⟩ := α.regular x hx
    refine ⟨ε, hε, hs, fun i ℓ => memH_of_ae_zero ?_⟩
    have := discExpr_ae_zero x hε.ne' (fun p hp => (hs p hp).1) x₀
      (fun y => ℓ (tangentCoordChange 𝓘(ℝ, E) (α.u y) (α.u x) (α.u y)
        (ptForm J α x₀ e y (tangentCoordChange 𝓘(ℝ, E2) x y y (EuclideanSpace.single i 1)))))
      fun y hy => by simp [ptForm_of_ne J α x₀ e hy]
    exact this

/-- **Nonzero fibre elements vanishing off a point** (target of positive dimension, no nodes). -/
theorem exists_pointFibreElement [Nontrivial E] (α : StableMap om m k δ) (hX : α.dom.nodes = ∅)
    (x₀ : α.dom.S) (k' : ℕ) (δ' : ℝ) :
    ∃ ξ : Form E α.dom, ξ ≠ 0 ∧ (∀ x, x ≠ x₀ → ξ x = 0) ∧ IsFibreElement J α k' δ' ξ := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  refine ⟨ptForm J α x₀ e, fun h => ?_, fun x hx => ptForm_of_ne J α x₀ e hx,
    isFibreElement_ptForm J α hX x₀ e k' δ'⟩
  have := congrFun h x₀
  rw [ptForm, if_pos rfl] at this
  exact antiPart_ne_zero J _ _ _ he this

/-- A form vanishing off a point has representative `0` in every atlas of a surface without
nodes. -/
theorem isFormRep_zero_of_point {X : NodalSurface m} {u : X.S → Q} (hX : X.nodes = ∅)
    (A : SectionAtlas (E := E) X u) (δs : ℕ → ℝ) (h0 : 0 ≤ δs 0) (hmono : StrictMono δs)
    {ξ : Form E X} (x₀ : X.S) (hξ : ∀ x, x ≠ x₀ → ξ x = 0) :
    IsFormRep (A := A) (δ := δs) (h0 := h0) (hmono := hmono) ξ 0 := by
  refine ⟨fun i d k => ?_, fun j => ?_⟩
  · refine (val_zero_ae (k := 2) (hd := Neck.δ_nonneg δs h0 hmono 0)).trans ?_
    refine (discExpr_ae_zero (A.center i) (A.ε_pos i).ne' (fun p hp => (A.disc_chart i p hp).1)
      x₀ (fun y => crd k (formAt u (A.center i) ξ y (EuclideanSpace.single d 1)))
      fun y hy => ?_).symm
    simp [formAt, hξ y hy]
  · obtain ⟨q, hq, -⟩ := A.node_nodal j
    rw [hX] at hq
    exact absurd hq (notMem_empty q)

lemma NodalSurface.nonempty {m : ℕ} (X : NodalSurface m) : Nonempty X.S := by
  obtain ⟨q⟩ := X.connected.toNonempty
  exact ⟨(Quot.exists_rep q).choose⟩

/-- **No map injective on all fibre elements factors through the fibre spaces**: at a stable map
without nodes, for every atlas, every map `ι` on the forms injective on the fibre elements of
class `(k', δ')` and every map `T` on the blocks, `ι(ξ) = T(v)` for all representatives `v` of
`ξ` is impossible (target of positive dimension).  The identification of the fibre is therefore
read on the classes, with the injectivity on continuous forms (`FibreRepresentation`). -/
theorem not_factor_of_injOn_fibreElements [Nontrivial E] (α : StableMap om m k δ)
    (hX : α.dom.nodes = ∅) {k' : ℕ} {δ' : ℝ} {W : Type*} (ι : Form E α.dom → W)
    (hinj : InjOn ι {ξ | IsFibreElement J α k' δ' ξ}) (A : SectionAtlas (E := E) α.dom α.u)
    (δs : ℕ → ℝ) (h0 : 0 ≤ δs 0) (hmono : StrictMono δs)
    (T : (fibreBlocks A δs h0 hmono) 0 → W) :
    ¬ ∀ ξ v, IsFormRep (A := A) ξ v → ι ξ = T v := by
  intro hT
  obtain ⟨x₀⟩ := α.dom.nonempty
  obtain ⟨ξ, hne, hsupp, hfib⟩ := exists_pointFibreElement J α hX x₀ k' δ'
  have h1 := hT ξ 0 (isFormRep_zero_of_point hX A δs h0 hmono x₀ hsupp)
  have h2 := hT 0 0 isFormRep_zero
  exact hne (hinj hfib (isFibreElement_zero J α k' δ') (h1.trans h2.symm))

end Point

/-! ## 2. Full subcategories of stable maps -/

section Sub

variable {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ}

/-- **The full subcategory of stable maps on `Ob`** (Definition 17.1.1 (1)–(3)), given finite
isomorphism sets between its objects. -/
def gwSub (Ob : Set (StableMap om m k δ))
    (hfin : ∀ α ∈ Ob, ∀ β ∈ Ob, Finite (StableMap.Iso α β)) : GroupoidalCategory.{1} where
  Obj := Ob
  Mor := (gwGroupoid om m k δ).morOn Ob
  toGroupoidStr := (gwGroupoid om m k δ).fullSub Ob
  finite_mor a b := by
    have hf : ((gwGroupoid om m k δ).mor a.1 b.1).Finite := by
      rw [gwGroupoid_mor]
      have := hfin a.1 a.2 b.1 b.2
      exact Set.finite_range _
    refine (hf.preimage Subtype.val_injective.injOn).subset fun φ hφ => ?_
    exact ⟨congrArg Subtype.val hφ.1, congrArg Subtype.val hφ.2⟩

variable (Ob : Set (StableMap om m k δ)) (hfin : ∀ α ∈ Ob, ∀ β ∈ Ob, Finite (StableMap.Iso α β))

/-- The inclusion as label: `L(α) = α`, `L(φ) = φ`. -/
def subLabel : StableMapLabel om m k δ (gwSub Ob hfin) where
  obj a := a.1
  iso φ := φ.1.2.2

end Sub

/-! ## 3. The fibre functor -/

section Functor

variable (J : AlmostComplexStructure E Q) {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ}
  (δs : ℕ → ℝ) (h0 : 0 ≤ δs 0) (hmono : StrictMono δs)

/-- **The change of coordinates for the fibres** (named proposition of analysis): for an
isomorphism `f : α → β` and atlases `A` of `α`, `B` of `β`, the pull-back `ξ ↦ ξ ∘ Tf` is a bounded
operator between the fibre spaces, `T(rep ξ) = rep(f^* ξ)`. -/
def PullbackBounded {α β : StableMap om m k δ} (A : SectionAtlas (E := E) α.dom α.u)
    (B : SectionAtlas (E := E) β.dom β.u) (f : α.Iso β) : Prop :=
  ∃ T : fibreSpace J B δs h0 hmono →L[ℝ] fibreSpace J A δs h0 hmono,
    ∀ ξ : formsDom J B δs h0 hmono,
      IsFormRep (A := A) (δ := δs) (h0 := h0) (hmono := hmono) (f.φ.pullbackForm ξ.1)
        (T (formRep ξ))

/-- **Witness**: an isomorphism which is the identity, and one atlas. -/
theorem pullbackBounded_of_id {α : StableMap om m k δ} (A : SectionAtlas (E := E) α.dom α.u)
    (f : α.Iso α) (hf : ∀ x, f.φ.φ x = x) : PullbackBounded J δs h0 hmono A A f :=
  ⟨ContinuousLinearMap.id ℝ _, fun ξ => by
    rw [NodalSurface.Iso.pullbackForm_of_eq_id _ hf]
    exact isFormRep_formRep ξ⟩

variable {J δs h0 hmono}

/-- Two continuous linear maps on the fibre agreeing on the representatives agree. -/
theorem fibre_ext {m' : ℕ} {X : NodalSurface m'} {u : X.S → Q} {A : SectionAtlas (E := E) X u}
    {W : Type*} [TopologicalSpace W] [AddCommMonoid W] [Module ℝ W] [T2Space W]
    {S S' : fibreSpace J A δs h0 hmono →L[ℝ] W}
    (h : ∀ ξ : formsDom J A δs h0 hmono, S (formRep ξ) = S' (formRep ξ)) : S = S' := by
  have hd : Dense {w : fibreSpace J A δs h0 hmono |
      (w : (fibreBlocks A δs h0 hmono) 0) ∈ formsSub J A δs h0 hmono} := by
    rw [Subtype.dense_iff]
    intro x hx
    have hsub : (formsSub J A δs h0 hmono : Set ((fibreBlocks A δs h0 hmono) 0)) ⊆
        Subtype.val '' {w : fibreSpace J A δs h0 hmono |
          (w : (fibreBlocks A δs h0 hmono) 0) ∈ formsSub J A δs h0 hmono} :=
      fun y hy => ⟨⟨y, formsSub_le J A δs h0 hmono hy⟩, hy, rfl⟩
    refine closure_mono hsub ?_
    rwa [← Submodule.topologicalClosure_coe]
  refine ContinuousLinearMap.ext (congrFun (Continuous.ext_on hd S.continuous S'.continuous ?_))
  rintro ⟨w, hw⟩ ⟨ξ, ha, hr⟩
  have := h ⟨ξ, ha, w, hr⟩
  rwa [show formRep (⟨ξ, ha, w, hr⟩ : formsDom J A δs h0 hmono) = ⟨w, hw⟩ from
    Subtype.ext (formRep_eq hr)] at this

lemma formRep_congr {m' : ℕ} {X : NodalSurface m'} {u : X.S → Q} {A : SectionAtlas (E := E) X u}
    {ξ η : formsDom J A δs h0 hmono} (h : ξ.1 = η.1) : formRep ξ = formRep η := by
  rw [Subtype.ext h]

variable {Ob : Set (StableMap om m k δ)} {hfin : ∀ α ∈ Ob, ∀ β ∈ Ob, Finite (StableMap.Iso α β)}
  (At : ∀ a : Ob, SectionAtlas (E := E) a.1.dom a.1.u)

variable (J δs h0 hmono hfin) in
/-- `PullbackBounded` for every morphism of the full subcategory, with the atlases `At`. -/
def AllPullbackBounded : Prop :=
  ∀ φ : (gwSub Ob hfin).Mor, PullbackBounded J δs h0 hmono
    (At ((gwSub Ob hfin).toGroupoidStr.src φ)) (At ((gwSub Ob hfin).toGroupoidStr.tgt φ)) φ.1.2.2

variable {At} (hPB : AllPullbackBounded J δs h0 hmono hfin At)

/-- The pull-back `φ^* : μ(t φ) → μ(s φ)`. -/
def pullOp (φ : (gwSub Ob hfin).Mor) :
    fibreSpace J (At ((gwSub Ob hfin).toGroupoidStr.tgt φ)) δs h0 hmono →L[ℝ]
      fibreSpace J (At ((gwSub Ob hfin).toGroupoidStr.src φ)) δs h0 hmono :=
  (hPB φ).choose

include hPB in
lemma pullbackForm_mem_dom (φ : (gwSub Ob hfin).Mor)
    (ξ : formsDom J (At ((gwSub Ob hfin).toGroupoidStr.tgt φ)) δs h0 hmono) :
    φ.1.2.2.φ.pullbackForm ξ.1 ∈
      formsDom J (At ((gwSub Ob hfin).toGroupoidStr.src φ)) δs h0 hmono :=
  ⟨ξ.2.1.pullback J φ.1.2.2, _, (hPB φ).choose_spec ξ⟩

theorem pullOp_rep' (φ : (gwSub Ob hfin).Mor)
    (ξ : formsDom J (At ((gwSub Ob hfin).toGroupoidStr.tgt φ)) δs h0 hmono)
    (η : formsDom J (At ((gwSub Ob hfin).toGroupoidStr.src φ)) δs h0 hmono)
    (h : η.1 = φ.1.2.2.φ.pullbackForm ξ.1) : pullOp hPB φ (formRep ξ) = formRep η := by
  apply Subtype.ext
  exact (formRep_eq (ξ := η) (h ▸ (hPB φ).choose_spec ξ)).symm

theorem pullOp_rep (φ : (gwSub Ob hfin).Mor)
    (ξ : formsDom J (At ((gwSub Ob hfin).toGroupoidStr.tgt φ)) δs h0 hmono) :
    pullOp hPB φ (formRep ξ) =
      formRep ⟨φ.1.2.2.φ.pullbackForm ξ.1, pullbackForm_mem_dom hPB φ ξ⟩ := by
  apply Subtype.ext
  exact (formRep_eq (ξ := ⟨φ.1.2.2.φ.pullbackForm ξ.1, pullbackForm_mem_dom hPB φ ξ⟩)
    ((hPB φ).choose_spec ξ)).symm

/-- The push-forward `μ(φ) = (φ⁻¹)^* : μ(s φ) → μ(t φ)`. -/
def pushOp (φ : (gwSub Ob hfin).Mor) :
    fibreSpace J (At ((gwSub Ob hfin).toGroupoidStr.src φ)) δs h0 hmono →L[ℝ]
      fibreSpace J (At ((gwSub Ob hfin).toGroupoidStr.tgt φ)) δs h0 hmono :=
  pullOp hPB ((gwSub Ob hfin).toGroupoidStr.inv φ)

theorem pushOp_rep (φ : (gwSub Ob hfin).Mor)
    (ξ : formsDom J (At ((gwSub Ob hfin).toGroupoidStr.src φ)) δs h0 hmono) :
    pushOp hPB φ (formRep ξ) =
      formRep ⟨φ.1.2.2.symm.φ.pullbackForm ξ.1,
        pullbackForm_mem_dom hPB ((gwSub Ob hfin).toGroupoidStr.inv φ) ξ⟩ :=
  pullOp_rep hPB ((gwSub Ob hfin).toGroupoidStr.inv φ) ξ

theorem pullOp_pushOp (φ : (gwSub Ob hfin).Mor) (x) : pullOp hPB φ (pushOp hPB φ x) = x := by
  have := fibre_ext (S := (pullOp hPB φ).comp (pushOp hPB φ)) (S' := ContinuousLinearMap.id ℝ _)
    fun ξ => by
      rw [ContinuousLinearMap.comp_apply, pushOp_rep, ContinuousLinearMap.id_apply]
      exact pullOp_rep' hPB φ _ ξ (pullbackForm_trans_symm φ.1.2.2 ξ.1).symm
  exact congrArg (fun S => S x) this

theorem pushOp_pullOp (φ : (gwSub Ob hfin).Mor) (x) : pushOp hPB φ (pullOp hPB φ x) = x := by
  have := fibre_ext (S := (pushOp hPB φ).comp (pullOp hPB φ)) (S' := ContinuousLinearMap.id ℝ _)
    fun ξ => by
      rw [ContinuousLinearMap.comp_apply, pullOp_rep, ContinuousLinearMap.id_apply]
      exact pullOp_rep' hPB ((gwSub Ob hfin).toGroupoidStr.inv φ) _ ξ
        (pullbackForm_symm_trans φ.1.2.2 ξ.1).symm
  exact congrArg (fun S => S x) this

/-- `μ(φ)` on the lifted fibres (the objects of `gwSub` live in `Type 1`). -/
def fibreMap (φ : (gwSub Ob hfin).Mor) :
    ULift.{1} (fibreSpace J (At ((gwSub Ob hfin).toGroupoidStr.src φ)) δs h0 hmono) ≃L[ℝ]
      ULift.{1} (fibreSpace J (At ((gwSub Ob hfin).toGroupoidStr.tgt φ)) δs h0 hmono) :=
  ContinuousLinearEquiv.ulift.trans
    ((ContinuousLinearEquiv.equivOfInverse (pushOp hPB φ) (pullOp hPB φ) (pullOp_pushOp hPB φ)
      (pushOp_pullOp hPB φ)).trans ContinuousLinearEquiv.ulift.symm)

theorem fibreMap_apply (φ : (gwSub Ob hfin).Mor) (x) :
    fibreMap hPB φ x = ULift.up (pushOp hPB φ x.down) := rfl

theorem pushOp_rep' (φ : (gwSub Ob hfin).Mor)
    (ξ : formsDom J (At ((gwSub Ob hfin).toGroupoidStr.src φ)) δs h0 hmono)
    (η : formsDom J (At ((gwSub Ob hfin).toGroupoidStr.tgt φ)) δs h0 hmono)
    (h : η.1 = φ.1.2.2.symm.φ.pullbackForm ξ.1) : pushOp hPB φ (formRep ξ) = formRep η :=
  pullOp_rep' hPB ((gwSub Ob hfin).toGroupoidStr.inv φ) ξ η h

theorem pushOp_unit (a : (gwSub Ob hfin).Obj) :
    pushOp hPB ((gwSub Ob hfin).toGroupoidStr.unit a) = ContinuousLinearMap.id ℝ _ :=
  fibre_ext fun ξ => pushOp_rep' hPB _ ξ ξ
    (NodalSurface.Iso.pullbackForm_of_eq_id _ (fun _ => rfl) ξ.1).symm

lemma sigmaAct_congr' {Obj Mor : Type 1} {V : Obj → Type 1} (src tgt : Mor → Obj)
    (mp : ∀ φ, V (src φ) → V (tgt φ)) {φ φ' : Mor} (hφ : φ = φ') (e : Σ a, V a)
    (h : e.1 = src φ) (h' : e.1 = src φ') :
    GroupoidalCategory.sigmaAct src tgt mp φ e h =
      GroupoidalCategory.sigmaAct src tgt mp φ' e h' := by
  subst hφ; rfl

/-- **The functor `μ : gwSub Ob → Ban`** (2021 p. 824): `μ(α)` the fibre of `W` over `α`
(`fibreSpace`, over the atlas `At α`), `μ(φ) = (φ^*)⁻¹`. -/
def fibreFunctor : GroupoidalCategory.BanachFunctor (gwSub Ob hfin) where
  V a := ULift.{1} (fibreSpace J (At a) δs h0 hmono)
  normed _ := ULift.normedAddCommGroup
  space _ := ULift.normedSpace
  complete a := @ULift.instCompleteSpace _ _
    (fibreSpace_completeSpace J (At a) δs h0 hmono)
  map φ := fibreMap hPB φ
  act_unit e h := by
    obtain ⟨a, v⟩ := e
    refine congrArg (Sigma.mk a) ?_
    apply ULift.ext
    change pushOp hPB ((gwSub Ob hfin).toGroupoidStr.unit a) v.down = v.down
    rw [pushOp_unit]
    rfl
  act_comp φ ψ hφψ e h := by
    obtain ⟨⟨β, γ, f⟩, hφ⟩ := φ
    obtain ⟨⟨α, β', g⟩, hψ⟩ := ψ
    have hb : β = β' := congrArg Subtype.val hφψ
    subst hb
    have hφ' : β ∈ Ob ∧ γ ∈ Ob := hφ
    have hψ' : α ∈ Ob ∧ β ∈ Ob := hψ
    obtain ⟨a, v⟩ := e
    change a = ⟨α, hψ'.1⟩ at h
    subst h
    have hc : (gwSub Ob hfin).toGroupoidStr.comp ⟨⟨β, γ, f⟩, hφ⟩ ⟨⟨α, β, g⟩, hψ⟩ =
        ⟨⟨α, γ, g.trans f⟩, hψ'.1, hφ'.2⟩ := by
      apply Subtype.ext
      change ((gwGroupoid om m k δ).fullSub Ob).comp ⟨⟨β, γ, f⟩, hφ⟩ ⟨⟨α, β, g⟩, hψ⟩ =
        (⟨α, γ, g.trans f⟩ : GWMor om m k δ)
      simp only [GroupoidStr.fullSub]
      rw [dif_pos (show (gwGroupoid om m k δ).src ⟨β, γ, f⟩ = (gwGroupoid om m k δ).tgt ⟨α, β, g⟩
        from rfl)]
      exact GWMor.comp_mk f g
    rw [sigmaAct_congr' _ _ _ hc _ _ rfl]
    refine congrArg (Sigma.mk (⟨γ, hφ'.2⟩ : (gwSub Ob hfin).Obj)) ?_
    apply ULift.ext
    change pushOp hPB (⟨⟨α, γ, g.trans f⟩, hψ'.1, hφ'.2⟩ : (gwSub Ob hfin).Mor) v.down =
      pushOp hPB (⟨⟨β, γ, f⟩, hφ⟩ : (gwSub Ob hfin).Mor)
        (pushOp hPB (⟨⟨α, β, g⟩, hψ⟩ : (gwSub Ob hfin).Mor) v.down)
    have hS : pushOp hPB (⟨⟨α, γ, g.trans f⟩, hψ'.1, hφ'.2⟩ : (gwSub Ob hfin).Mor) =
        (pushOp hPB (⟨⟨β, γ, f⟩, hφ⟩ : (gwSub Ob hfin).Mor)).comp
          (pushOp hPB (⟨⟨α, β, g⟩, hψ⟩ : (gwSub Ob hfin).Mor)) := by
      refine fibre_ext fun ξ => ?_
      have e1 := pushOp_rep hPB (⟨⟨α, β, g⟩, hψ⟩ : (gwSub Ob hfin).Mor) ξ
      have heq := pullbackForm_trans_symm' g f ξ.1
      exact (pushOp_rep hPB _ ξ).trans ((pushOp_rep' hPB (⟨⟨β, γ, f⟩, hφ⟩ : (gwSub Ob hfin).Mor)
        _ _ heq).symm.trans (congrArg (pushOp hPB (⟨⟨β, γ, f⟩, hφ⟩ : (gwSub Ob hfin).Mor))
          e1.symm))
    rw [hS]
    rfl

end Functor

/-! ## 4. The instances -/

section Instance

variable (J : AlmostComplexStructure E Q) {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ}
  (δs : ℕ → ℝ) (h0 : 0 ≤ δs 0) (hmono : StrictMono δs)
  {Ob : Set (StableMap om m k δ)} {hfin : ∀ α ∈ Ob, ∀ β ∈ Ob, Finite (StableMap.Iso α β)}

/-- The atlases of the stable maps without nodes (`exists_sectionAtlas`). -/
def noNodeAtlas (hOb : ∀ α ∈ Ob, α.dom.nodes = ∅) (a : Ob) :
    SectionAtlas (E := E) a.1.dom a.1.u :=
  (exists_sectionAtlas a.1.dom a.1.u a.1.continuous (hOb a.1 a.2)).some

variable {J δs h0 hmono} {At : ∀ a : Ob, SectionAtlas (E := E) a.1.dom a.1.u}
  (hPB : AllPullbackBounded J δs h0 hmono hfin At)

/-- **The fibre representation of the GW data on a full subcategory of stable maps without
nodes** (memoir p. 7), given the change of coordinates `PullbackBounded`: `dom a` the forms with
representatives in the atlas `At a`, `ι_a(ξ)` the representative. -/
def fibreRepresentation (hOb : ∀ α ∈ Ob, α.dom.nodes = ∅) (k' : ℕ) (δ' : ℝ) :
    FibreRepresentation om m k δ (subLabel Ob hfin) (fibreFunctor hPB) J k' δ' where
  dom a := formsDom J (At a) δs h0 hmono
  ι a := (ContinuousLinearEquiv.ulift (R₁ := ℝ)
    (M₁ := fibreSpace J (At a) δs h0 hmono)).symm.toLinearEquiv.toLinearMap.comp
      (formRepL J (At a) δs h0 hmono)
  pullback_mem φ ξ' h := pullbackForm_mem_dom hPB φ ⟨ξ', h⟩
  natural φ ξ' := by
    apply ULift.ext
    exact pushOp_rep' hPB φ _ ξ' (pullbackForm_symm_trans φ.1.2.2 ξ'.1).symm
  injOn a ξ hξ η hη h := by
    have h1 : formRep ξ = formRep η := congrArg ULift.down h
    have hr := isFormRep_formRep ξ
    rw [h1] at hr
    exact Subtype.ext (IsFormRep.inj (hOb a.1 a.2) hξ.2 hη.2 hr (isFormRep_formRep η))

/-- The constant maps from the three-pointed sphere. -/
def constOb (om : SymplecticForm E Q) (k : ℕ) (δ : ℝ) : Set (StableMap om 3 k δ) :=
  range fun q => constStableMap om q k δ

lemma constOb_noNodes : ∀ α ∈ constOb om k δ, α.dom.nodes = ∅ := by
  rintro _ ⟨q, rfl⟩; rfl

lemma eq_of_iso_const {q q' : Q} (f : (constStableMap om q k δ).Iso (constStableMap om q' k δ)) :
    q' = q :=
  f.comm (pt 0)

lemma constOb_finite : ∀ α ∈ constOb om k δ, ∀ β ∈ constOb om k δ, Finite (StableMap.Iso α β) := by
  rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩
  by_cases h : Nonempty ((constStableMap om q k δ).Iso (constStableMap om q' k δ))
  · obtain ⟨f⟩ := h
    obtain rfl := eq_of_iso_const f
    exact finite_iso_constStableMap om _ k δ
  · have := not_nonempty_iff.1 h
    infer_instance

variable (J δs h0 hmono) in
/-- **The change of coordinates holds on the constant maps** (no named proposition): every
isomorphism of constant maps from the three-pointed sphere is the identity. -/
theorem constOb_pullbackBounded :
    AllPullbackBounded J δs h0 hmono (constOb_finite (om := om) (k := k) (δ := δ))
      (noNodeAtlas constOb_noNodes) := by
  rintro ⟨⟨α, β, f⟩, hφ⟩
  have hφ' : α ∈ constOb om k δ ∧ β ∈ constOb om k δ := hφ
  obtain ⟨⟨q, rfl⟩, ⟨q', rfl⟩⟩ := hφ'
  obtain rfl := eq_of_iso_const f
  exact pullbackBounded_of_id J δs h0 hmono _ f (fun x => sphere3_iso_apply f.φ x)

variable (J δs h0 hmono) in
/-- **The fibre representation of the GW data on the constant maps from the three-pointed
sphere**, with no named proposition. -/
def constFibreRepresentation (om : SymplecticForm E Q) (k : ℕ) (δ : ℝ) (k' : ℕ) (δ' : ℝ) :=
  fibreRepresentation (constOb_pullbackBounded (om := om) (k := k) (δ := δ) J δs h0 hmono)
    constOb_noNodes k' δ'

variable (J δs h0 hmono) in
/-- On the constant maps, `∂̄_J` lies in the domain and is a continuous fibre element. -/
theorem constFibreRepresentation_dbarInDom (om : SymplecticForm E Q) (k : ℕ) (δ : ℝ) (k' : ℕ)
    (δ' : ℝ) : DbarInDom (constFibreRepresentation J δs h0 hmono om k δ k' δ') := by
  rintro ⟨_, ⟨q, rfl⟩⟩
  change (constStableMap om q k δ).dom.dbar J (fun _ => q) ∈ formsDom J _ δs h0 hmono
  rw [dbar_const_eq_zero]
  exact Submodule.zero_mem _

variable (J) in
theorem const_dbarRegularC (om : SymplecticForm E Q) (k : ℕ) (δ : ℝ) (k' : ℕ) (δ' : ℝ) :
    DbarRegularC (subLabel (constOb om k δ) constOb_finite) J k' δ' := by
  rintro ⟨_, ⟨q, rfl⟩⟩
  change IsFibreElement J _ k' δ' ((constStableMap om q k δ).dom.dbar J (fun _ => q)) ∧
    IsContForm _ ((constStableMap om q k δ).dom.dbar J (fun _ => q))
  rw [dbar_const_eq_zero]
  exact ⟨isFibreElement_zero J _ k' δ', isContForm_zero _⟩

variable (J δs h0 hmono) in
/-- **`∂̄_J` of a constant map is `0` in the fibre**, and every object of the category of
constant maps is a zero of `∂̄_J`, consistently with `dbar_eq_zero_iff`. -/
theorem constFibreRepresentation_dbar (om : SymplecticForm E Q) (k : ℕ) (δ : ℝ) (k' : ℕ)
    (δ' : ℝ) (a : (gwSub (constOb om k δ) constOb_finite).Obj) :
    (constFibreRepresentation J δs h0 hmono om k δ k' δ').dbar
      (constFibreRepresentation_dbarInDom J δs h0 hmono om k δ k' δ') a = 0 := by
  rw [FibreRepresentation.dbar_eq_zero_iff _ _ (const_dbarRegularC J om k δ k' δ')]
  obtain ⟨_, ⟨q, rfl⟩⟩ := a
  exact isHolomorphic_constStableMap om J q k δ

end Instance

/-! ## 5. Non-vacuity of the fibre hypotheses of Theorem 1.11 -/

section NonVacuity

open GroupoidalCategory GroupoidalCategory.BasicConstruction

variable (J : AlmostComplexStructure E Q)

/-- **The fibre hypotheses of Memoir Theorem 1.11 hold together** (non-degenerate witness): for
every target `Q` with a point and every class `(k', δ')`, on the category
of the constant maps from the three-pointed sphere (nonempty) there are a label, a Banach functor
(the fibres of `W`) and a fibre representation with `∂̄_J` in its domain (`DbarInDom`) and a
continuous fibre element (`DbarRegularC`); `∂̄_J` is natural and every object is `J`-holomorphic.
No named proposition is assumed. -/
theorem memoir_theorem_1_11_fibre_nonvacuous [Nonempty Q] (om : SymplecticForm E Q) (k : ℕ)
    (δ : ℝ) (k' : ℕ) (δ' : ℝ) :
    ∃ (C : GroupoidalCategory.{1}) (L : StableMapLabel om 3 k δ C) (μ : BanachFunctor C)
      (ι : FibreRepresentation om 3 k δ L μ J k' δ') (hd : DbarInDom ι),
      Nonempty C.Obj ∧ DbarRegularC L J k' δ' ∧
      (∀ φ : C.Mor, μ.map φ (ι.dbar hd (C.toGroupoidStr.src φ)) =
        ι.dbar hd (C.toGroupoidStr.tgt φ)) ∧
      ∀ a, ι.dbar hd a = 0 ∧ (L.obj a).IsHolomorphic J := by
  obtain ⟨q⟩ := ‹Nonempty Q›
  have h0 : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) := le_of_eq Nat.cast_zero.symm
  have hmono : StrictMono fun n : ℕ => (n : ℝ) := Nat.strictMono_cast
  refine ⟨_, _, _, _, constFibreRepresentation_dbarInDom J _ h0 hmono om k δ k' δ',
    ⟨⟨_, q, rfl⟩⟩, const_dbarRegularC J om k δ k' δ', FibreRepresentation.dbar_natural _ _,
    fun a => ⟨constFibreRepresentation_dbar J _ h0 hmono om k δ k' δ' a, ?_⟩⟩
  obtain ⟨_, ⟨q', rfl⟩⟩ := a
  exact isHolomorphic_constStableMap om J q' k δ

variable {J} {δs : ℕ → ℝ} {h0 : 0 ≤ δs 0} {hmono : StrictMono δs}

/-- **The fibre hypotheses of Memoir Theorem 1.11 on the GW base of the constant maps**: for
every base `Z` built on the category of the constant maps from the three-pointed sphere (the
data and named propositions of `memoir_theorem_1_10`) and every vector bundle GCT over it whose
Banach functor is `fibreFunctor`, the hypotheses of `memoir_theorem_1_11` on the fibre have an
instance: a fibre representation `ιV` of `V` with `DbarInDom ιV` and `DbarRegularC`. -/
theorem memoir_theorem_1_11_fibre_const {om : SymplecticForm E Q} {k : ℕ} {δ : ℝ} {k' : ℕ}
    {δ' : ℝ} {U : (gwSub (constOb om k δ) constOb_finite).UniformizerConstruction}
    {CS : CSPred U} {h310 : U.HasClassUniformizers} {H : Theorem_3_13 U CS}
    {hCS : CSClosed U CS} {hPF : PointFinite U}
    {h322 : Theorem_3_22 U (gwTransitionData H hCS hPF)}
    {h16 : Theorem_1_6_sc U (gwTransitionData H hCS hPF) h310}
    (V : (gwGCT h310 H hCS hPF h322 h16).VectorBundle)
    (hV : V.toBanachFunctor = fibreFunctor (constOb_pullbackBounded J δs h0 hmono)) :
    ∃ (ιV : FibreRepresentation om 3 k δ (subLabel (constOb om k δ) constOb_finite)
      V.toBanachFunctor J k' δ') (_ : DbarInDom ιV),
      DbarRegularC (subLabel (constOb om k δ) constOb_finite) J k' δ' := by
  have key : ∀ μ : BanachFunctor (gwSub (constOb om k δ) constOb_finite),
      μ = fibreFunctor (constOb_pullbackBounded J δs h0 hmono) →
      ∃ (ιV : FibreRepresentation om 3 k δ (subLabel (constOb om k δ) constOb_finite) μ J k' δ')
        (_ : DbarInDom ιV), DbarRegularC (subLabel (constOb om k δ) constOb_finite) J k' δ' := by
    rintro μ rfl
    exact ⟨_, constFibreRepresentation_dbarInDom J δs h0 hmono om k δ k' δ',
      const_dbarRegularC J om k δ k' δ'⟩
  exact key V.toBanachFunctor hV

end NonVacuity

end GWMemoir
