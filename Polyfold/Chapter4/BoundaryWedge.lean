import Polyfold.Chapter4.BoundaryForms2021
import Polyfold.Chapter4.ScFormsWedge2021b

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, pp. 198–199
(2017 p. 150; preprint p. 168): the wedge product on the forms on `∂X`, needed for "the
differential algebra `Ω*_∞(X, ∂X)`" of p. 199.

# The wedge product of forms on `∂X`

Forms on `∂X` are read, as in `BoundaryForms2021.lean`, as the sc-forms on the tame boundary `bX`
that agree over `B : bX → X` (with their `d`); more generally, for an sc-smooth `f : X → Y`, the
forms agreeing over `f` (`agreeDForms f`, direct limit `agreeDFormsInfty f`).  This file puts the
wedge product of `ScFormsWedge2021.lean` on these forms.

## What is proved

* `IsAgreeingOver.formWedge`, `IsAgreeingOver.formCast`: the wedge product and the change of
  degree preserve the agreement; `formsWedge_mem_agreeDForms`: `Ωᵏ(∂Xⁱ) ∧ Ωˡ(∂Xⁱ) ⊆ Ωᵏ⁺ˡ(∂Xⁱ)`
  (the agreement of `d(τ ∧ σ)` by the Leibniz rule `formsD_formsWedge`).
* `agreeDFormsInftyWedge f k l : Ωᵏ_∞ × Ωˡ_∞ → Ωᵏ⁺ˡ_∞` on the agreeing forms, bilinear,
  `[τ] ∧ [σ] = [τ ∧ σ]` (`agreeDFormsInftyWedge_of_of`).
* The Leibniz rule (`agreeDFormsInftyD_agreeDFormsInftyWedge`), associativity
  (`agreeDFormsInftyWedge_assoc`), the unit `f^*1` on both sides
  (`agreeDFormsInftyCast_agreeDFormsInftyOne_wedge`, `agreeDFormsInftyWedge_agreeDFormsInftyOne`).
* `f^*` is multiplicative (`agreeInftyPullback_formsInftyWedge`), and so is the inclusion into
  `Ω*_∞(X)` (`agreeDFormsInftyIncl_agreeDFormsInftyWedge`).
* For `f = B`: `bFormsInftyWedge`, with `j^*(ω ∧ η) = j^*ω ∧ j^*η` (`jStar_formsInftyWedge`).
-/

open Set Function

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {f : X → Y} {k l : ℕ}

/-- **The wedge product preserves agreement over `f`**: if `ω` and `τ` agree over `f`, so does
`ω ∧ τ`, term by term in the wedge formula. -/
theorem IsAgreeingOver.formWedge {hf : P.IsScSmoothMap Q f}
    {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    {τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin l]→ₗ[ℝ] ℝ}
    (hω : IsAgreeingOver hf ω) (hτ : IsAgreeingOver hf τ) :
    IsAgreeingOver hf (MPolyfold.formWedge ω τ) := by
  intro x x' hx α α' hα
  rw [formWedge_apply, formWedge_apply]
  unfold wedgeFun wedgeFunAux
  refine congrArg _ (Finset.sum_congr rfl fun σ _ => ?_)
  rw [hω hx _ _ fun i => hα _, hτ hx _ _ fun j => hα _]

/-- **Changing the degree preserves agreement over `f`.** -/
theorem IsAgreeingOver.formCast {hf : P.IsScSmoothMap Q f} {k' : ℕ} (h : k = k')
    {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hω : IsAgreeingOver hf ω) :
    IsAgreeingOver hf (MPolyfold.formCast h ω) := fun _ _ hx _ _ hα =>
  hω hx _ _ fun _ => hα _

end MPolyfold

namespace BundledMPolyfold

open MPolyfold

universe u v

attribute [local instance high] wedgeAddCommMonoidFormsInfty wedgeModuleFormsInfty

variable {A : BundledMPolyfold.{u}} {B : BundledMPolyfold.{v}} (f : ScMap A.P B.P) {k l m : ℕ}

/-! ### On `Ωᵏ(Xⁱ)` -/

theorem formsWedge_mem_agreeForms {i : ℕ} {ω : A.forms k i} {τ : A.forms l i}
    (hω : ω ∈ agreeForms f k i) (hτ : τ ∈ agreeForms f l i) :
    A.formsWedge k l i ω τ ∈ agreeForms f (k + l) i :=
  IsAgreeingOver.formWedge hω hτ

theorem formsCast_mem_agreeForms {k' : ℕ} (h : k = k') {i : ℕ} {ω : A.forms k i}
    (hω : ω ∈ agreeForms f k i) : A.formsCast h i ω ∈ agreeForms f k' i := by
  subst h
  exact hω

/-- **`Ωᵏ(∂Xⁱ) ∧ Ωˡ(∂Xⁱ) ⊆ Ωᵏ⁺ˡ(∂Xⁱ)`**, for the forms agreeing (with their `d`) over `f`: the
agreement of `d(ω ∧ τ) = dω ∧ ι^*τ ± ι^*ω ∧ dτ` follows from that of its four factors. -/
theorem formsWedge_mem_agreeDForms {i : ℕ} {ω : A.forms k i} {τ : A.forms l i}
    (hω : ω ∈ agreeDForms f k i) (hτ : τ ∈ agreeDForms f l i) :
    A.formsWedge k l i ω τ ∈ agreeDForms f (k + l) i := by
  refine ⟨formsWedge_mem_agreeForms f hω.1 hτ.1, ?_⟩
  change A.formsD (k + l) i (A.formsWedge k l i ω τ) ∈ agreeForms f (k + l + 1) (i + 1)
  rw [A.formsD_formsWedge (Nat.add_right_comm k 1 l)]
  refine add_mem (formsCast_mem_agreeForms f _ (formsWedge_mem_agreeForms f hω.2
    (formsStep_mem_agreeForms f l hτ.1))) (Submodule.smul_mem _ _ ?_)
  exact formsWedge_mem_agreeForms f (formsStep_mem_agreeForms f k hω.1) hτ.2

variable (k l) in
/-- The wedge product `Ωᵏ(∂Xⁱ) × Ωˡ(∂Xⁱ) → Ωᵏ⁺ˡ(∂Xⁱ)` on the agreeing forms, bilinear. -/
def agreeDFormsWedge (i : ℕ) :
    agreeDForms f k i →ₗ[ℝ] agreeDForms f l i →ₗ[ℝ] agreeDForms f (k + l) i :=
  LinearMap.mk₂ ℝ (fun ω τ => ⟨A.formsWedge k l i ω τ, formsWedge_mem_agreeDForms f ω.2 τ.2⟩)
    (fun _ _ _ => Subtype.ext (LinearMap.map_add₂ _ _ _ _))
    (fun _ _ _ => Subtype.ext (LinearMap.map_smul₂ _ _ _ _))
    (fun _ _ _ => Subtype.ext (LinearMap.map_add _ _ _))
    (fun _ _ _ => Subtype.ext (LinearMap.map_smul _ _ _))

@[simp] lemma coe_agreeDFormsWedge (i : ℕ) (ω : agreeDForms f k i) (τ : agreeDForms f l i) :
    (agreeDFormsWedge f k l i ω τ : A.forms (k + l) i) = A.formsWedge k l i ω τ := rfl

theorem agreeDFormsWedge_agreeDFormsMap {i j : ℕ} (h : i ≤ j) (ω : agreeDForms f k i)
    (τ : agreeDForms f l i) :
    agreeDFormsMap f (k + l) i j h (agreeDFormsWedge f k l i ω τ) =
      agreeDFormsWedge f k l j (agreeDFormsMap f k i j h ω) (agreeDFormsMap f l i j h τ) := by
  refine Subtype.ext ?_
  rw [coe_agreeDFormsMap f (k + l) h (agreeDFormsWedge f k l i ω τ),
    coe_agreeDFormsWedge f j (agreeDFormsMap f k i j h ω) (agreeDFormsMap f l i j h τ),
    coe_agreeDFormsMap f k h ω, coe_agreeDFormsMap f l h τ]
  exact A.formsWedge_formsMap h ω.1 τ.1

/-! ### On the direct limit -/

/-- The class of `ω ∧ τ` read at a common level `n ≥ i, j`. -/
def agreeWedgeAt (i j n : ℕ) (hi : i ≤ n) (hj : j ≤ n) (ω : agreeDForms f k i)
    (τ : agreeDForms f l j) : agreeDFormsInfty f (k + l) :=
  agreeDFormsInftyOf f (k + l) n
    (agreeDFormsWedge f k l n (agreeDFormsMap f k i n hi ω) (agreeDFormsMap f l j n hj τ))

theorem agreeDFormsMap_comp_apply {i j n : ℕ} (hij : i ≤ j) (hjn : j ≤ n)
    (ω : agreeDForms f k i) :
    agreeDFormsMap f k j n hjn (agreeDFormsMap f k i j hij ω) =
      agreeDFormsMap f k i n (hij.trans hjn) ω := by
  refine Subtype.ext ?_
  rw [coe_agreeDFormsMap f k hjn (agreeDFormsMap f k i j hij ω), coe_agreeDFormsMap f k hij ω,
    coe_agreeDFormsMap f k (hij.trans hjn) ω]
  exact LinearMap.congr_fun (A.formsMap_comp k hij hjn) ω.1

theorem agreeWedgeAt_le {i j n n' : ℕ} (hi : i ≤ n) (hj : j ≤ n) (hn : n ≤ n')
    (ω : agreeDForms f k i) (τ : agreeDForms f l j) :
    agreeWedgeAt f i j n' (hi.trans hn) (hj.trans hn) ω τ = agreeWedgeAt f i j n hi hj ω τ :=
  (congrArg (agreeDFormsInftyOf f (k + l) n')
    ((congrArg₂ (fun x y => agreeDFormsWedge f k l n' x y) (agreeDFormsMap_comp_apply f hi hn ω)
      (agreeDFormsMap_comp_apply f hj hn τ)).symm.trans
      (agreeDFormsWedge_agreeDFormsMap f hn (agreeDFormsMap f k i n hi ω)
        (agreeDFormsMap f l j n hj τ)).symm)).trans
    (agreeDFormsInftyOf_agreeDFormsMap f (k + l) hn _)

theorem agreeWedgeAt_eq {i j n n' : ℕ} (hi : i ≤ n) (hj : j ≤ n) (hi' : i ≤ n') (hj' : j ≤ n')
    (ω : agreeDForms f k i) (τ : agreeDForms f l j) :
    agreeWedgeAt f i j n hi hj ω τ = agreeWedgeAt f i j n' hi' hj' ω τ :=
  (agreeWedgeAt_le f hi hj (le_max_left n n') ω τ).symm.trans
    (agreeWedgeAt_le f hi' hj' (le_max_right n n') ω τ)

variable (k l) in
/-- `(ω, τ) ↦ [ι^*ω ∧ ι^*τ]`, read on `X^{i+j}`; bilinear. -/
def agreeWedgeAtₗ (i j : ℕ) :
    agreeDForms f k i →ₗ[ℝ] agreeDForms f l j →ₗ[ℝ] agreeDFormsInfty f (k + l) :=
  ((agreeDFormsWedge f k l (i + j)).compl₁₂ (agreeDFormsMap f k i (i + j) (Nat.le_add_right i j))
    (agreeDFormsMap f l j (i + j) (Nat.le_add_left j i))).compr₂
    (agreeDFormsInftyOf f (k + l) (i + j))

theorem agreeWedgeAtₗ_apply (i j : ℕ) (ω : agreeDForms f k i) (τ : agreeDForms f l j) :
    agreeWedgeAtₗ f k l i j ω τ =
      agreeWedgeAt f i j (i + j) (Nat.le_add_right i j) (Nat.le_add_left j i) ω τ :=
  rfl

theorem agreeWedgeAtₗ_agreeDFormsMap {i j j' : ℕ} (h : j ≤ j') (ω : agreeDForms f k i)
    (τ : agreeDForms f l j) :
    agreeWedgeAtₗ f k l i j' ω (agreeDFormsMap f l j j' h τ) = agreeWedgeAtₗ f k l i j ω τ := by
  rw [agreeWedgeAtₗ_apply, agreeWedgeAtₗ_apply]
  refine Eq.trans ?_ (agreeWedgeAt_eq f _ _ (Nat.le_add_right i j')
    (h.trans (Nat.le_add_left j' i)) ω τ).symm
  unfold agreeWedgeAt
  rw [agreeDFormsMap_comp_apply]

variable (k l) in
/-- `ω ↦ ([τ] ↦ [ω ∧ τ])` on `Ωᵏ(∂Xⁱ)`. -/
def agreeDFormsInftyWedgeOf (i : ℕ) :
    agreeDForms f k i →ₗ[ℝ] agreeDFormsInfty f l →ₗ[ℝ] agreeDFormsInfty f (k + l) :=
  (show agreeDFormsInfty f l →ₗ[ℝ] agreeDForms f k i →ₗ[ℝ] agreeDFormsInfty f (k + l) from
    Module.DirectLimit.lift ℝ ℕ (fun j => ↥(agreeDForms f l j)) (agreeDFormsMap f l)
    (fun j => (agreeWedgeAtₗ f k l i j).flip) fun _ _ h τ =>
      LinearMap.ext fun ω => agreeWedgeAtₗ_agreeDFormsMap f h ω τ).flip

theorem agreeDFormsInftyWedgeOf_of (i j : ℕ) (ω : agreeDForms f k i) (τ : agreeDForms f l j) :
    agreeDFormsInftyWedgeOf f k l i ω (agreeDFormsInftyOf f l j τ) =
      agreeWedgeAt f i j (i + j) (Nat.le_add_right i j) (Nat.le_add_left j i) ω τ :=
  LinearMap.congr_fun (Module.DirectLimit.lift_of (R := ℝ) (ι := ℕ)
    (G := fun j => ↥(agreeDForms f l j)) (f := agreeDFormsMap f l)
    (fun j => (agreeWedgeAtₗ f k l i j).flip) (fun _ _ h τ =>
      LinearMap.ext fun ω => agreeWedgeAtₗ_agreeDFormsMap f h ω τ) τ) ω

theorem agreeDFormsInftyWedgeOf_agreeDFormsMap {i i' : ℕ} (h : i ≤ i') (ω : agreeDForms f k i) :
    agreeDFormsInftyWedgeOf f k l i' (agreeDFormsMap f k i i' h ω) =
      agreeDFormsInftyWedgeOf f k l i ω := by
  refine agreeDFormsInfty_hom_ext f l fun j τ => ?_
  rw [agreeDFormsInftyWedgeOf_of, agreeDFormsInftyWedgeOf_of]
  refine Eq.trans ?_ (agreeWedgeAt_eq f (h.trans (Nat.le_add_right i' j)) (Nat.le_add_left j i')
    _ _ ω τ)
  unfold agreeWedgeAt
  rw [agreeDFormsMap_comp_apply]

variable (k l) in
/-- **The wedge product on `Ω*_∞(∂X)`** (more generally on the forms agreeing over `f`):
`[ω] ∧ [τ] = [ω ∧ τ]` for representatives pulled back to a common level. -/
def agreeDFormsInftyWedge :
    agreeDFormsInfty f k →ₗ[ℝ] agreeDFormsInfty f l →ₗ[ℝ] agreeDFormsInfty f (k + l) :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(agreeDForms f k i)) (agreeDFormsMap f k)
    (agreeDFormsInftyWedgeOf f k l) fun _ _ h ω => agreeDFormsInftyWedgeOf_agreeDFormsMap f h ω

theorem agreeDFormsInftyWedge_of (i j : ℕ) (ω : agreeDForms f k i) (τ : agreeDForms f l j) :
    agreeDFormsInftyWedge f k l (agreeDFormsInftyOf f k i ω) (agreeDFormsInftyOf f l j τ) =
      agreeWedgeAt f i j (i + j) (Nat.le_add_right i j) (Nat.le_add_left j i) ω τ :=
  (LinearMap.congr_fun (Module.DirectLimit.lift_of (R := ℝ) (ι := ℕ)
    (G := fun i => ↥(agreeDForms f k i)) (f := agreeDFormsMap f k)
    (agreeDFormsInftyWedgeOf f k l) (fun _ _ h ω => agreeDFormsInftyWedgeOf_agreeDFormsMap f h ω)
    ω) (agreeDFormsInftyOf f l j τ)).trans (agreeDFormsInftyWedgeOf_of f i j ω τ)

/-- `[ω] ∧ [τ] = [ω ∧ τ]` for `ω`, `τ` on the same level. -/
theorem agreeDFormsMap_self (i : ℕ) (ω : agreeDForms f k i) :
    agreeDFormsMap f k i i le_rfl ω = ω := by
  refine Subtype.ext ?_
  rw [coe_agreeDFormsMap f k le_rfl ω, formsMap_self]
  rfl

/-- `[ω] ∧ [τ] = [ω ∧ τ]` for `ω`, `τ` on the same level. -/
theorem agreeDFormsInftyWedge_of_of (i : ℕ) (ω : agreeDForms f k i) (τ : agreeDForms f l i) :
    agreeDFormsInftyWedge f k l (agreeDFormsInftyOf f k i ω) (agreeDFormsInftyOf f l i τ) =
      agreeDFormsInftyOf f (k + l) i (agreeDFormsWedge f k l i ω τ) :=
  ((agreeDFormsInftyWedge_of f i i ω τ).trans
    (agreeWedgeAt_eq f _ _ (le_refl i) (le_refl i) ω τ)).trans
    (congrArg (agreeDFormsInftyOf f (k + l) i)
      (congrArg₂ (fun x y => agreeDFormsWedge f k l i x y) (agreeDFormsMap_self f i ω)
        (agreeDFormsMap_self f i τ)))

/-- Every element of the direct limit is the class of a form at any large level. -/
theorem agreeDFormsInftyOf_agreeDFormsMap' {i j : ℕ} (h : i ≤ j) (ω : agreeDForms f k i) :
    agreeDFormsInftyOf f k i ω = agreeDFormsInftyOf f k j (agreeDFormsMap f k i j h ω) :=
  (agreeDFormsInftyOf_agreeDFormsMap f k h ω).symm

/-- Every element of the direct limit is the class of a form at every level `≥` some `i`. -/
theorem agreeDFormsInfty_exists_of (a : agreeDFormsInfty f k) :
    ∃ i, ∀ n, i ≤ n → ∃ ω : agreeDForms f k n, a = agreeDFormsInftyOf f k n ω := by
  obtain ⟨i, ω, h⟩ := Module.DirectLimit.exists_of a
  exact ⟨i, fun n hn => ⟨agreeDFormsMap f k i n hn ω,
    h.symm.trans (agreeDFormsInftyOf_agreeDFormsMap' f hn ω)⟩⟩


/-! ### Change of degree, the Leibniz rule -/

/-- Reading the degree `k` of `Ωᵏ(∂Xⁱ)` as `k' = k`. -/
def agreeDFormsCast {k' : ℕ} (h : k = k') (i : ℕ) : agreeDForms f k i →ₗ[ℝ] agreeDForms f k' i :=
  h ▸ LinearMap.id

lemma coe_agreeDFormsCast {k' : ℕ} (h : k = k') (i : ℕ) (ω : agreeDForms f k i) :
    (agreeDFormsCast f h i ω : A.forms k' i) = A.formsCast h i ω := by
  subst h; rfl

/-- Reading the degree `k` of `Ωᵏ_∞(∂X)` as `k' = k`. -/
def agreeDFormsInftyCast {k' : ℕ} (h : k = k') :
    agreeDFormsInfty f k →ₗ[ℝ] agreeDFormsInfty f k' :=
  h ▸ LinearMap.id

lemma agreeDFormsInftyCast_of {k' : ℕ} (h : k = k') (i : ℕ) (ω : agreeDForms f k i) :
    agreeDFormsInftyCast f h (agreeDFormsInftyOf f k i ω) =
      agreeDFormsInftyOf f k' i (agreeDFormsCast f h i ω) := by
  subst h; rfl

lemma agreeDFormsInftyCast_rfl (a : agreeDFormsInfty f k) :
    agreeDFormsInftyCast f rfl a = a := rfl

lemma agreeDFormsInftyCast_trans {k' k'' : ℕ} (h : k = k') (h' : k' = k'')
    (a : agreeDFormsInfty f k) :
    agreeDFormsInftyCast f h' (agreeDFormsInftyCast f h a) =
      agreeDFormsInftyCast f (h.trans h') a := by
  subst h h'; rfl

/-- The step `Ωᵏ(∂Xⁱ) → Ωᵏ(∂Xⁱ⁺¹)`. -/
lemma agreeDFormsInftyOf_step (i : ℕ) (ω : agreeDForms f k i) :
    agreeDFormsInftyOf f k (i + 1) ⟨A.formsStep k i ω, formsStep_mem_agreeDForms f k ω.2⟩ =
      agreeDFormsInftyOf f k i ω := by
  refine Eq.trans ?_ (agreeDFormsInftyOf_agreeDFormsMap f k (Nat.le_succ i) ω)
  congr 1
  refine Subtype.ext ?_
  rw [coe_agreeDFormsMap, formsMap_succ A k le_rfl, formsMap_self, LinearMap.comp_id]

/-- **The Leibniz rule on `Ωᵏ(∂Xⁱ)`**: `d(ω ∧ τ) = dω ∧ ι^*τ + (−1)ᵏ ι^*ω ∧ dτ`. -/
theorem agreeDFormsD_agreeDFormsWedge (h : k + 1 + l = k + l + 1) (i : ℕ) (ω : agreeDForms f k i)
    (τ : agreeDForms f l i) :
    agreeDFormsD f (k + l) i (agreeDFormsWedge f k l i ω τ) =
      agreeDFormsCast f h (i + 1) (agreeDFormsWedge f (k + 1) l (i + 1) (agreeDFormsD f k i ω)
        ⟨A.formsStep l i τ, formsStep_mem_agreeDForms f l τ.2⟩) +
      (-1 : ℝ) ^ k • agreeDFormsWedge f k (l + 1) (i + 1)
        ⟨A.formsStep k i ω, formsStep_mem_agreeDForms f k ω.2⟩ (agreeDFormsD f l i τ) := by
  refine Subtype.ext ?_
  rw [Submodule.coe_add, Submodule.coe_smul, coe_agreeDFormsCast]
  exact A.formsD_formsWedge h i ω τ

theorem agreeDFormsInftyD_agreeDFormsInftyWedge_of (h : k + 1 + l = k + l + 1) (n : ℕ)
    (ω : agreeDForms f k n) (τ : agreeDForms f l n) :
    agreeDFormsInftyD f (k + l) (agreeDFormsInftyWedge f k l (agreeDFormsInftyOf f k n ω)
      (agreeDFormsInftyOf f l n τ)) =
      agreeDFormsInftyCast f h (agreeDFormsInftyWedge f (k + 1) l
        (agreeDFormsInftyD f k (agreeDFormsInftyOf f k n ω)) (agreeDFormsInftyOf f l n τ)) +
        (-1 : ℝ) ^ k • agreeDFormsInftyWedge f k (l + 1) (agreeDFormsInftyOf f k n ω)
          (agreeDFormsInftyD f l (agreeDFormsInftyOf f l n τ)) := by
  have e1 : agreeDFormsInftyOf f (k + (l + 1)) (n + 1) (agreeDFormsWedge f k (l + 1) (n + 1)
      ⟨A.formsStep k n ω, formsStep_mem_agreeDForms f k ω.2⟩ (agreeDFormsD f l n τ)) =
      agreeDFormsInftyWedge f k (l + 1) (agreeDFormsInftyOf f k n ω)
        (agreeDFormsInftyD f l (agreeDFormsInftyOf f l n τ)) :=
    (agreeDFormsInftyWedge_of_of f (n + 1) _ _).symm.trans <| by
      rw [agreeDFormsInftyOf_step f n ω, agreeDFormsInftyD_of]
  have e2 : agreeDFormsInftyOf f (k + 1 + l) (n + 1) (agreeDFormsWedge f (k + 1) l (n + 1)
      (agreeDFormsD f k n ω) ⟨A.formsStep l n τ, formsStep_mem_agreeDForms f l τ.2⟩) =
      agreeDFormsInftyWedge f (k + 1) l (agreeDFormsInftyD f k (agreeDFormsInftyOf f k n ω))
        (agreeDFormsInftyOf f l n τ) :=
    (agreeDFormsInftyWedge_of_of f (n + 1) _ _).symm.trans <| by
      rw [agreeDFormsInftyOf_step f n τ, agreeDFormsInftyD_of]
  rw [agreeDFormsInftyWedge_of_of, agreeDFormsInftyD_of, agreeDFormsD_agreeDFormsWedge f h]
  refine (LinearMap.map_add _ _ _).trans (congrArg₂ (· + ·) ?_ ?_)
  · exact (agreeDFormsInftyCast_of f h (n + 1) _).symm.trans (congrArg _ e2)
  · exact (LinearMap.map_smul _ _ _).trans (congrArg _ e1)

/-- **The Leibniz rule on `Ω*_∞(∂X)`**: `d(a ∧ b) = da ∧ b + (−1)ᵏ a ∧ db` for `a` of degree `k`
(the degree `(k + 1) + l` read as `(k + l) + 1`). -/
theorem agreeDFormsInftyD_agreeDFormsInftyWedge (h : k + 1 + l = k + l + 1)
    (a : agreeDFormsInfty f k) (b : agreeDFormsInfty f l) :
    agreeDFormsInftyD f (k + l) (agreeDFormsInftyWedge f k l a b) =
      agreeDFormsInftyCast f h (agreeDFormsInftyWedge f (k + 1) l (agreeDFormsInftyD f k a) b) +
        (-1 : ℝ) ^ k • agreeDFormsInftyWedge f k (l + 1) a (agreeDFormsInftyD f l b) := by
  obtain ⟨i, hi⟩ := agreeDFormsInfty_exists_of f a
  obtain ⟨j, hj⟩ := agreeDFormsInfty_exists_of f b
  obtain ⟨ω, rfl⟩ := hi (i + j) (Nat.le_add_right i j)
  obtain ⟨τ, rfl⟩ := hj (i + j) (Nat.le_add_left j i)
  exact agreeDFormsInftyD_agreeDFormsInftyWedge_of f h (i + j) ω τ

/-! ### Associativity and the unit -/

theorem agreeDFormsWedge_assoc (n : ℕ) (ω : agreeDForms f k n) (τ : agreeDForms f l n)
    (η : agreeDForms f m n) :
    agreeDFormsWedge f (k + l) m n (agreeDFormsWedge f k l n ω τ) η =
      agreeDFormsCast f (Nat.add_assoc k l m).symm n
        (agreeDFormsWedge f k (l + m) n ω (agreeDFormsWedge f l m n τ η)) :=
  Subtype.ext <| by
    rw [coe_agreeDFormsCast f (Nat.add_assoc k l m).symm n
      (agreeDFormsWedge f k (l + m) n ω (agreeDFormsWedge f l m n τ η))]
    exact A.formsWedge_assoc n ω.1 τ.1 η.1

theorem agreeDFormsInftyWedge_assoc_of (n : ℕ) (ω : agreeDForms f k n) (τ : agreeDForms f l n)
    (η : agreeDForms f m n) :
    agreeDFormsInftyWedge f (k + l) m (agreeDFormsInftyWedge f k l (agreeDFormsInftyOf f k n ω)
      (agreeDFormsInftyOf f l n τ)) (agreeDFormsInftyOf f m n η) =
      agreeDFormsInftyCast f (Nat.add_assoc k l m).symm
        (agreeDFormsInftyWedge f k (l + m) (agreeDFormsInftyOf f k n ω)
          (agreeDFormsInftyWedge f l m (agreeDFormsInftyOf f l n τ)
            (agreeDFormsInftyOf f m n η))) :=
  calc _ = agreeDFormsInftyWedge f (k + l) m
          (agreeDFormsInftyOf f (k + l) n (agreeDFormsWedge f k l n ω τ))
          (agreeDFormsInftyOf f m n η) :=
        congrArg (fun x => agreeDFormsInftyWedge f (k + l) m x (agreeDFormsInftyOf f m n η))
          (agreeDFormsInftyWedge_of_of f n ω τ)
    _ = agreeDFormsInftyOf f (k + l + m) n
          (agreeDFormsWedge f (k + l) m n (agreeDFormsWedge f k l n ω τ) η) :=
        agreeDFormsInftyWedge_of_of f n _ _
    _ = agreeDFormsInftyOf f (k + l + m) n (agreeDFormsCast f (Nat.add_assoc k l m).symm n
          (agreeDFormsWedge f k (l + m) n ω (agreeDFormsWedge f l m n τ η))) :=
        congrArg _ (agreeDFormsWedge_assoc f n ω τ η)
    _ = agreeDFormsInftyCast f (Nat.add_assoc k l m).symm (agreeDFormsInftyOf f (k + (l + m)) n
          (agreeDFormsWedge f k (l + m) n ω (agreeDFormsWedge f l m n τ η))) :=
        (agreeDFormsInftyCast_of f _ n _).symm
    _ = agreeDFormsInftyCast f (Nat.add_assoc k l m).symm (agreeDFormsInftyWedge f k (l + m)
          (agreeDFormsInftyOf f k n ω)
          (agreeDFormsInftyOf f (l + m) n (agreeDFormsWedge f l m n τ η))) :=
        congrArg _ (agreeDFormsInftyWedge_of_of f n _ _).symm
    _ = _ := congrArg (fun x => agreeDFormsInftyCast f (Nat.add_assoc k l m).symm
          (agreeDFormsInftyWedge f k (l + m) (agreeDFormsInftyOf f k n ω) x))
          (agreeDFormsInftyWedge_of_of f n τ η).symm

/-- **Associativity on `Ω*_∞(∂X)`**: `(a ∧ b) ∧ c = a ∧ (b ∧ c)`, the degree `k + (l + m)` read
as `(k + l) + m`. -/
theorem agreeDFormsInftyWedge_assoc (a : agreeDFormsInfty f k) (b : agreeDFormsInfty f l)
    (c : agreeDFormsInfty f m) :
    agreeDFormsInftyWedge f (k + l) m (agreeDFormsInftyWedge f k l a b) c =
      agreeDFormsInftyCast f (Nat.add_assoc k l m).symm
        (agreeDFormsInftyWedge f k (l + m) a (agreeDFormsInftyWedge f l m b c)) := by
  obtain ⟨i, hi⟩ := agreeDFormsInfty_exists_of f a
  obtain ⟨j, hj⟩ := agreeDFormsInfty_exists_of f b
  obtain ⟨r, hr⟩ := agreeDFormsInfty_exists_of f c
  obtain ⟨ω, rfl⟩ := hi (i + j + r) (by omega)
  obtain ⟨τ, rfl⟩ := hj (i + j + r) (by omega)
  obtain ⟨η, rfl⟩ := hr (i + j + r) (by omega)
  exact agreeDFormsInftyWedge_assoc_of f _ ω τ η

/-- **The unit `f^*1 ∈ Ω⁰_∞`** of the agreeing forms. -/
def agreeDFormsInftyOne : agreeDFormsInfty f 0 := agreeInftyPullback f 0 B.formsInftyOne

theorem agreePullback_formsOne (n : ℕ) :
    (agreePullback f 0 n (B.formsOne n) : A.forms 0 n) = A.formsOne n :=
  Subtype.ext rfl

theorem agreeDFormsInftyOne_eq (n : ℕ) :
    agreeDFormsInftyOne f = agreeDFormsInftyOf f 0 n (agreePullback f 0 n (B.formsOne n)) := by
  rw [agreeDFormsInftyOne, ← B.formsInftyOf_formsOne n, agreeInftyPullback_of]

theorem agreeDFormsWedge_agreePullback_formsOne (n : ℕ) (τ : agreeDForms f l n) :
    agreeDFormsWedge f l 0 n τ (agreePullback f 0 n (B.formsOne n)) = τ := by
  refine Subtype.ext ?_
  change A.formsWedge l 0 n τ.1 (agreePullback f 0 n (B.formsOne n)).1 = τ.1
  rw [agreePullback_formsOne f n]
  exact A.formsWedge_formsOne n τ.1

theorem agreeDFormsCast_agreeDFormsWedge_formsOne (n : ℕ) (τ : agreeDForms f l n) :
    agreeDFormsCast f (Nat.zero_add l) n
      (agreeDFormsWedge f 0 l n (agreePullback f 0 n (B.formsOne n)) τ) = τ := by
  refine Subtype.ext ?_
  rw [coe_agreeDFormsCast f (Nat.zero_add l) n
    (agreeDFormsWedge f 0 l n (agreePullback f 0 n (B.formsOne n)) τ)]
  change A.formsCast (Nat.zero_add l) n (A.formsWedge 0 l n
    (agreePullback f 0 n (B.formsOne n)).1 τ.1) = τ.1
  rw [agreePullback_formsOne f n]
  exact A.formsCast_formsWedge_formsOne n τ.1

/-- **The unit on the right**: `b ∧ f^*1 = b`. -/
theorem agreeDFormsInftyWedge_agreeDFormsInftyOne (b : agreeDFormsInfty f l) :
    agreeDFormsInftyWedge f l 0 b (agreeDFormsInftyOne f) = b := by
  obtain ⟨j, hj⟩ := agreeDFormsInfty_exists_of f b
  obtain ⟨τ, rfl⟩ := hj j le_rfl
  exact (congrArg (agreeDFormsInftyWedge f l 0 (agreeDFormsInftyOf f l j τ))
    (agreeDFormsInftyOne_eq f j)).trans ((agreeDFormsInftyWedge_of_of f j τ _).trans
      (congrArg (agreeDFormsInftyOf f l j) (agreeDFormsWedge_agreePullback_formsOne f j τ)))

/-- **The unit on the left**: `f^*1 ∧ b = b`, the degree `0 + l` read as `l`. -/
theorem agreeDFormsInftyCast_agreeDFormsInftyOne_wedge (b : agreeDFormsInfty f l) :
    agreeDFormsInftyCast f (Nat.zero_add l)
      (agreeDFormsInftyWedge f 0 l (agreeDFormsInftyOne f) b) = b := by
  obtain ⟨j, hj⟩ := agreeDFormsInfty_exists_of f b
  obtain ⟨τ, rfl⟩ := hj j le_rfl
  exact (congrArg (fun x => agreeDFormsInftyCast f (Nat.zero_add l)
    (agreeDFormsInftyWedge f 0 l x (agreeDFormsInftyOf f l j τ)))
      (agreeDFormsInftyOne_eq f j)).trans
    ((congrArg (agreeDFormsInftyCast f (Nat.zero_add l))
      (agreeDFormsInftyWedge_of_of f j _ τ)).trans
      ((agreeDFormsInftyCast_of f _ j _).trans
        (congrArg (agreeDFormsInftyOf f l j) (agreeDFormsCast_agreeDFormsWedge_formsOne f j τ))))

/-! ### Naturality -/

theorem agreePullback_formsWedge (i : ℕ) (ω : B.forms k i) (τ : B.forms l i) :
    agreePullback f (k + l) i (B.formsWedge k l i ω τ) =
      agreeDFormsWedge f k l i (agreePullback f k i ω) (agreePullback f l i τ) :=
  Subtype.ext (A.formsPullback_formsWedge f i ω τ)

/-- **`f^*(a ∧ b) = f^*a ∧ f^*b`**, with values in the agreeing forms. -/
theorem agreeInftyPullback_formsInftyWedge (a : B.formsInfty k) (b : B.formsInfty l) :
    agreeInftyPullback f (k + l) (B.formsInftyWedge k l a b) =
      agreeDFormsInftyWedge f k l (agreeInftyPullback f k a) (agreeInftyPullback f l b) := by
  obtain ⟨i, ω, rfl⟩ := Module.DirectLimit.exists_of a
  obtain ⟨j, τ, rfl⟩ := Module.DirectLimit.exists_of b
  have e1 := B.formsInftyOf_formsMap k (Nat.le_add_right i j) ω
  have e2 := B.formsInftyOf_formsMap l (Nat.le_add_left j i) τ
  change agreeInftyPullback f (k + l) (B.formsInftyWedge k l (B.formsInftyOf k i ω)
      (B.formsInftyOf l j τ)) = agreeDFormsInftyWedge f k l
      (agreeInftyPullback f k (B.formsInftyOf k i ω))
      (agreeInftyPullback f l (B.formsInftyOf l j τ))
  rw [← e1, ← e2, B.formsInftyWedge_of_of, agreeInftyPullback_of, agreeInftyPullback_of,
    agreeInftyPullback_of]
  exact (congrArg (agreeDFormsInftyOf f (k + l) (i + j)) (agreePullback_formsWedge f _ _ _)).trans
    (agreeDFormsInftyWedge_of_of f _ _ _).symm

/-- The inclusion of the agreeing forms into `Ω*_∞(X)` is multiplicative. -/
theorem agreeDFormsInftyIncl_agreeDFormsInftyWedge (a : agreeDFormsInfty f k)
    (b : agreeDFormsInfty f l) :
    agreeDFormsInftyIncl f (k + l) (agreeDFormsInftyWedge f k l a b) =
      A.formsInftyWedge k l (agreeDFormsInftyIncl f k a) (agreeDFormsInftyIncl f l b) := by
  obtain ⟨i, hi⟩ := agreeDFormsInfty_exists_of f a
  obtain ⟨j, hj⟩ := agreeDFormsInfty_exists_of f b
  obtain ⟨ω, rfl⟩ := hi (i + j) (Nat.le_add_right i j)
  obtain ⟨τ, rfl⟩ := hj (i + j) (Nat.le_add_left j i)
  exact (congrArg (agreeDFormsInftyIncl f (k + l)) (agreeDFormsInftyWedge_of_of f _ ω τ)).trans
    ((agreeDFormsInftyIncl_of f (k + l) _ _).trans
      ((A.formsInftyWedge_of_of _ ω.1 τ.1).symm.trans
        (congrArg₂ (fun x y => A.formsInftyWedge k l x y)
        (agreeDFormsInftyIncl_of f k _ ω).symm (agreeDFormsInftyIncl_of f l _ τ).symm)))

end BundledMPolyfold

/-! ### Forms on `∂X` -/

namespace MPolyfold

open BundledMPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  (hP : P.IsTame)

attribute [local instance high] wedgeAddCommMonoidFormsInfty wedgeModuleFormsInfty

/-- **2021 pp. 198–199: the wedge product on `Ω*_∞(∂X)`**, `Ωᵏ_∞(∂X) × Ωˡ_∞(∂X) → Ωᵏ⁺ˡ_∞(∂X)`,
bilinear, on the forms on `bX` agreeing over `B`. -/
abbrev bFormsInftyWedge (k l : ℕ) :
    bFormsInfty hP k →ₗ[ℝ] bFormsInfty hP l →ₗ[ℝ] bFormsInfty hP (k + l) :=
  agreeDFormsInftyWedge (bdryMap hP) k l

/-- **`j^*(ω ∧ η) = j^*ω ∧ j^*η`** for `ω, η ∈ Ω*_∞(X)`. -/
theorem jStar_formsInftyWedge {k l : ℕ} (ω : (BundledMPolyfold.of P).formsInfty k)
    (η : (BundledMPolyfold.of P).formsInfty l) :
    jStar hP (k + l) ((BundledMPolyfold.of P).formsInftyWedge k l ω η) =
      bFormsInftyWedge hP k l (jStar hP k ω) (jStar hP l η) :=
  agreeInftyPullback_formsInftyWedge _ ω η

end MPolyfold

end Polyfold
