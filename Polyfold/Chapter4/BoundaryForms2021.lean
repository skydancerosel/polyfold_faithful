import Polyfold.Chapter4.ScFormsPullback2021
import Polyfold.Chapter2.TameBoundaryStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, pp. 198–199
(2017 p. 150, after Definition 4.10; preprint p. 168, after Definition 4.27): the relative version
of the sc-de Rham cohomology of Definition 4.4.6 — forms on `∂X`, the pull-back `j^*`, the complex
`Ω*_∞(X, ∂X)` with `d(ω, τ) = (dω, j^*ω − dτ)`, `d ∘ d = 0` and `H*_dR(X, ∂X)`; and the case
`∂X = ∅` used on p. 279 (after the proof of Theorem 6.7.1; 2017: after Theorem 6.4; preprint
p. 233, after Theorem 6.43).

# Forms on `∂X` and the relative complex

## The text, paraphrased

For a tame `X` the inclusion of `∂X` into `X` is sc-smooth on every local face, and local faces
and their intersections are tame M-polyfolds; so, the text says, one may speak of forms on `∂X`
and `∂Xⁱ`.  It sets `Ω*_∞(X, ∂X) = Ω*_∞(X) ⊕ Ω*⁻¹_∞(∂X)` with `d(ω, τ) = (dω, j^*ω − dτ)` for the
inclusion `j : ∂X → X`, notes that `d ∘ d = 0` is easily checked, and calls the cohomology
`H*_dR(X, ∂X)`.

## The reading

`∂X` is not itself an M-polyfold.  We read "forms on `∂X`" through the tame boundary
`B : bX → X` (2021 Theorem 2.7.13 and Definition 2.7.14, `tameBoundaryPolyfold`,
`tameBoundaryMap`): the points of `bX` are the classes `[x, V, θ]` of a point `x ∈ ∂X` and a local
face `θ` through `x`, `bX` is a tame M-polyfold, and `B` forgets the face; through the charts
`Φ_{(x,V,θ)}` every local face is an open piece of `bX` that `B` maps onto the face in `X`.  A form
on `∂X` is then a form on all local faces at once that coincides on their intersections:

* `IsAgreeingOver`, `IsFaceCompatible`: a family `τ` of alternating forms on `T(bXⁱ)` **agrees
  over `B`** if `τ_p(v₁, …, v_k) = τ_{p'}(v'₁, …, v'_k)` whenever `B p = B p'` and
  `TB vⱼ = TB v'ⱼ` for all `j`.  At a corner point `x` the points `p ≠ p'` over `x` are the local
  faces through `x`, and the condition says that their forms agree on the vectors tangent to both.
* `bForms hP k i = Ωᵏ(∂Xⁱ)`: the sc-forms `τ ∈ Ωᵏ(bXⁱ)` such that `τ` agrees over `Bⁱ` **and
  `dτ` agrees over `Bⁱ⁺¹`**.  The second condition makes `d` map `Ωᵏ(∂Xⁱ)` to `Ωᵏ⁺¹(∂Xⁱ⁺¹)`
  (`extD_mem_bForms`, by `d ∘ d = 0`), which the text uses when it writes `dτ`.  For a manifold with
  corners it follows from the first (the corner strata are submanifolds with
  `T(F ∩ F') = TF ∩ TF'`); in the sc-setting that implication would need the corner strata of tame
  retracts as sub-M-polyfolds and common tame charts for two faces at a corner, which the library
  does not have, so we put the condition into the definition.  It excludes no form the text needs:
  `j^*ω` and `d(j^*ω) = j^*(dω)` both agree (`formsPullback_mem_bForms`), and so does `0`.
  `bForms` is the largest family of agreeing forms that `d` maps into itself (`le_bForms`); so if
  the implication holds, `bForms` is exactly the set of agreeing sc-forms.
* `Ωᵏ_∞(∂X)` (`bFormsInfty`) is the direct limit of the `Ωᵏ(∂Xⁱ)` under the maps of (4.4), as
  `Ωᵏ_∞(X)` in Definition 4.4.2.

A form in `Ωᵏ(∂Xⁱ)` gives, through the charts `Φ_{(x,V,θ)}` of `bX`, a form on every local face
`θ`, with the forms of two faces equal (with their `d`) on common tangent vectors: this is the
face-wise datum that is restricted to the faces of solution sets later.

## What is proved

* `IsAgreeingOver` is a linear condition (`isAgreeingOver_zero`, `.add`, `.smul`), satisfied by
  every pull-back (`isAgreeingOver_formPullback`) and preserved by `ι^* : Ωᵏ(X) → Ωᵏ(X¹)`
  (`IsAgreeingOver.formLower`).
* For any sc-smooth `f : X → Y` (bundled): `agreeDForms f k i`, its direct limit
  `agreeDFormsInfty f k` with `d` (`agreeDFormsInftyD`, `d² = 0`), the pull-back `f^*` with values
  in it (`agreeInftyPullback`, `d f^* = f^* d`), the inclusion into `Ωᵏ_∞(X)`
  (`agreeDFormsInftyIncl`, compatible with `d` and with `formsInftyPullback`), and the maximality
  `le_agreeDForms`.
* For `f = B`: `bForms`, `extD_mem_bForms`, `le_bForms`, `bFormsInfty`,
  `bFormsInftyD_comp_bFormsInftyD`, `jStar` (`j^* = B^*`), `jStar_comp_D` (`d j^* = j^* d`),
  `formsPullback_mem_bForms`.
* `RelForms hP k` (`Ω⁰_∞(X)` in degree `0`, `Ωᵏ⁺¹_∞(X) × Ωᵏ_∞(∂X)` in degree `k + 1`), `relD`
  (`d(ω, τ) = (dω, j^*ω − dτ)`), `relD_comp_relD` (`d ∘ d = 0`), `relDeRham hP k`
  (`Hᵏ_dR(X, ∂X)` as a real vector space), `relDeRhamMk`, `relDeRhamMk_eq_iff`.
* `relDeRhamEquivOfNoBoundary`: for `X` without boundary, `bX = ∅` and
  `Hᵏ_dR(X, ∂X) ≃ Hᵏ_sc(X)` (Definition 4.4.6).

## Not formalized

The implication "`τ` agrees over `B` ⇒ `dτ` agrees over `B¹`" (see the reading); the wedge
product, so `Ω*_∞(X, ∂X)` as a differential algebra (the complex is formalized degree by degree,
as a graded vector space).
-/

open Set Function

noncomputable section

namespace Polyfold

namespace MPolyfold

section Agree

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {f : X → Y} {k : ℕ}

/-- **Agreement over `f`**: a family `τ` of alternating `k`-forms on the tangent spaces of `X`
agrees over `f : X → Y` if `τ_x(α₁, …, α_k) = τ_{x'}(α'₁, …, α'_k)` whenever `f(x) = f(x')` and
`Tf αⱼ = Tf α'ⱼ` for all `j`. -/
def IsAgreeingOver (hf : P.IsScSmoothMap Q f)
    (τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) : Prop :=
  ∀ ⦃x x' : P.Level 1⦄, f (P.levelVal 1 x) = f (P.levelVal 1 x') →
    ∀ (α : Fin k → P.tangentFiber x) (α' : Fin k → P.tangentFiber x'),
      (∀ j, tangentMap hf (α j).1 = tangentMap hf (α' j).1) → τ x α = τ x' α'

theorem isAgreeingOver_zero (hf : P.IsScSmoothMap Q f) :
    IsAgreeingOver hf (0 : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :=
  fun _ _ _ _ _ _ => rfl

theorem IsAgreeingOver.add {hf : P.IsScSmoothMap Q f}
    {τ σ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hτ : IsAgreeingOver hf τ) (hσ : IsAgreeingOver hf σ) : IsAgreeingOver hf (τ + σ) :=
  fun _ _ hx α α' hα => by
    simp only [Pi.add_apply, AlternatingMap.add_apply]
    rw [hτ hx α α' hα, hσ hx α α' hα]

theorem IsAgreeingOver.smul {hf : P.IsScSmoothMap Q f}
    {τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (c : ℝ)
    (hτ : IsAgreeingOver hf τ) : IsAgreeingOver hf (c • τ) :=
  fun _ _ hx α α' hα => by
    simp only [Pi.smul_apply, AlternatingMap.smul_apply]
    rw [hτ hx α α' hα]

/-- **The pull-back of a form agrees over the map**: `f^*ω` agrees over `f`. -/
theorem isAgreeingOver_formPullback (hf : P.IsScSmoothMap Q f)
    (ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ) :
    IsAgreeingOver hf (formPullback hf ω) := fun x x' hx α α' hα =>
  (formPullback_eq hf ω α (y := liftLevelOneMap hf x') hx _ fun j => by
    rw [hα j, coe_tangentFiberMap_apply]).trans (formPullback_apply hf ω x' α').symm

/-- **Agreement passes to `X¹`**: if `τ` agrees over `f`, then `ι^*τ` agrees over the index raise
`f¹ : X¹ → Y¹`. -/
theorem IsAgreeingOver.formLower {hf : P.IsScSmoothMap Q f} {f₁ : P.Level 1 → Q.Level 1}
    (hf₁ : ∀ x, Q.levelVal 1 (f₁ x) = f (P.levelVal 1 x))
    (h₁ : P.shift.IsScSmoothMap Q.shift f₁)
    {τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hτ : IsAgreeingOver hf τ) :
    IsAgreeingOver h₁ (formLower τ) := by
  intro x x' hx α α' hα
  rw [formLower_apply, formLower_apply]
  refine hτ ?_ _ _ fun j => ?_
  · rw [← hf₁, ← hf₁, hx]
  · rw [coe_lowerFiberCLM_apply, coe_lowerFiberCLM_apply, ← tangentLower_tangentMap hf hf₁,
      ← tangentLower_tangentMap hf hf₁]
    exact congrArg tangentLower (hα j)

end Agree

end MPolyfold

/-! ### Forms agreeing over an sc-smooth map, on `Xⁱ` and on `X_∞` -/

namespace BundledMPolyfold

open MPolyfold

universe u v

variable {A : BundledMPolyfold.{u}} {B : BundledMPolyfold.{v}} (f : ScMap A.P B.P) (k : ℕ)

/-- `Ωᵏ_∞(X)` is an additive monoid: the instance of its type, stated directly so that the
search is short. -/
@[reducible] def addCommMonoid_formsInfty (A : BundledMPolyfold.{u}) (j : ℕ) :
    AddCommMonoid (A.formsInfty j) :=
  Module.DirectLimit.addCommMonoid _ _

attribute [instance high] addCommMonoid_formsInfty

/-- `Ωᵏ_∞(X)` is a real vector space: the instance of its type, stated directly. -/
@[reducible] def module_formsInfty (A : BundledMPolyfold.{u}) (j : ℕ) :
    Module ℝ (A.formsInfty j) :=
  Module.DirectLimit.module _ _

attribute [instance high] module_formsInfty

/-- The `k`-forms on `Xⁱ` agreeing over `fⁱ : Xⁱ → Yⁱ`. -/
def agreeForms (i : ℕ) : Submodule ℝ (A.forms k i) where
  carrier := {τ | IsAgreeingOver (A.liftMap f i).isScSmoothMap τ.1}
  zero_mem' := isAgreeingOver_zero _
  add_mem' := fun ha hb => ha.add hb
  smul_mem' := fun c _ h => h.smul c

lemma mem_agreeForms {i : ℕ} {τ : A.forms k i} :
    τ ∈ agreeForms f k i ↔ IsAgreeingOver (A.liftMap f i).isScSmoothMap τ.1 := Iff.rfl

/-- The `k`-forms `τ` on `Xⁱ` such that `τ` agrees over `fⁱ` and `dτ` agrees over `fⁱ⁺¹`. -/
def agreeDForms (i : ℕ) : Submodule ℝ (A.forms k i) :=
  agreeForms f k i ⊓ (agreeForms f (k + 1) (i + 1)).comap (A.formsD k i)

lemma mem_agreeDForms {i : ℕ} {τ : A.forms k i} :
    τ ∈ agreeDForms f k i ↔ τ ∈ agreeForms f k i ∧ A.formsD k i τ ∈ agreeForms f (k + 1) (i + 1) :=
  Iff.rfl

/-- **`agreeDForms` is the largest `d`-stable family of agreeing forms**: every family of subspaces
of agreeing forms that `d` maps into itself lies in it. -/
theorem le_agreeDForms {V : ∀ n i, Submodule ℝ (A.forms n i)} (hV : ∀ n i, V n i ≤ agreeForms f n i)
    (hd : ∀ n i (τ : A.forms n i), τ ∈ V n i → A.formsD n i τ ∈ V (n + 1) (i + 1)) (n i : ℕ) :
    V n i ≤ agreeDForms f n i :=
  fun τ hτ => ⟨hV n i hτ, hV (n + 1) (i + 1) (hd n i τ hτ)⟩

theorem formsStep_mem_agreeForms {i : ℕ} {τ : A.forms k i} (h : τ ∈ agreeForms f k i) :
    A.formsStep k i τ ∈ agreeForms f k (i + 1) :=
  IsAgreeingOver.formLower (hf := (A.liftMap f i).isScSmoothMap) (f₁ := A.liftMap f (i + 1))
    (fun _ => rfl) (A.liftMap f (i + 1)).isScSmoothMap h

theorem formsStep_mem_agreeDForms {i : ℕ} {τ : A.forms k i} (h : τ ∈ agreeDForms f k i) :
    A.formsStep k i τ ∈ agreeDForms f k (i + 1) := by
  refine ⟨formsStep_mem_agreeForms f k h.1, ?_⟩
  change A.formsD k (i + 1) (A.formsStep k i τ) ∈ agreeForms f (k + 1) (i + 1 + 1)
  rw [formsD_formsStep]
  exact formsStep_mem_agreeForms f (k + 1) h.2

theorem formsMap_mem_agreeDForms {i j : ℕ} (hij : i ≤ j) {τ : A.forms k i}
    (h : τ ∈ agreeDForms f k i) : A.formsMap k i j hij τ ∈ agreeDForms f k j := by
  induction j, hij using Nat.le_induction with
  | base => rw [formsMap_self]; exact h
  | succ j hij ih =>
    rw [formsMap_succ A k hij, LinearMap.comp_apply]
    exact formsStep_mem_agreeDForms f k ih

/-- The maps `Ωᵏ(Xⁱ) → Ωᵏ(Xʲ)` of the directed system (4.4), restricted. -/
def agreeDFormsMap (i j : ℕ) (h : i ≤ j) : agreeDForms f k i →ₗ[ℝ] agreeDForms f k j :=
  (A.formsMap k i j h).restrict fun _ hτ => formsMap_mem_agreeDForms f k h hτ

@[simp] lemma coe_agreeDFormsMap {i j : ℕ} (h : i ≤ j) (τ : agreeDForms f k i) :
    (agreeDFormsMap f k i j h τ : A.forms k j) = A.formsMap k i j h τ := rfl

instance directedSystem_agreeDForms :
    DirectedSystem (fun i => ↥(agreeDForms f k i)) fun i j h => ⇑(agreeDFormsMap f k i j h) where
  map_self i τ := Subtype.ext (by rw [coe_agreeDFormsMap, formsMap_self]; rfl)
  map_map _ _ _ hij hjk τ := Subtype.ext (by
    rw [coe_agreeDFormsMap, coe_agreeDFormsMap, coe_agreeDFormsMap]
    exact LinearMap.congr_fun (A.formsMap_comp k hij hjk) τ)

/-- The direct limit of the forms agreeing (with their `d`) over `f`.  A `def`, with the
instances below, so that its only additive group structure is `addCommGroup_agreeDFormsInfty`. -/
def agreeDFormsInfty : Type _ :=
  Module.DirectLimit (fun i => ↥(agreeDForms f k i)) (agreeDFormsMap f k)

/-- The additive monoid of the direct limit (not an instance: the instance is
`addCommGroup_agreeDFormsInfty`). -/
@[reducible] def addCommMonoidAgreeDFormsInfty : AddCommMonoid (agreeDFormsInfty f k) :=
  Module.DirectLimit.addCommMonoid _ _

/-- The vector space structure of the direct limit, over `addCommMonoidAgreeDFormsInfty`. -/
@[reducible] def moduleAgreeDFormsInfty :
    @Module ℝ (agreeDFormsInfty f k) _ (addCommMonoidAgreeDFormsInfty f k) :=
  Module.DirectLimit.module _ _

/-- The additive group structure of the direct limit, with `-τ = (-1) • τ`; its additive monoid is
`addCommMonoidAgreeDFormsInfty`. -/
@[reducible] def addCommGroup_agreeDFormsInfty : AddCommGroup (agreeDFormsInfty f k) :=
  @Module.addCommMonoidToAddCommGroup ℝ (agreeDFormsInfty f k) _ (addCommMonoidAgreeDFormsInfty f k)
    (moduleAgreeDFormsInfty f k)

attribute [instance] addCommGroup_agreeDFormsInfty

/-- The vector space structure of the direct limit. -/
@[reducible] def module_agreeDFormsInfty : Module ℝ (agreeDFormsInfty f k) :=
  moduleAgreeDFormsInfty f k

attribute [instance] module_agreeDFormsInfty

/-- The class of a form agreeing over `fⁱ`. -/
abbrev agreeDFormsInftyOf (i : ℕ) : agreeDForms f k i →ₗ[ℝ] agreeDFormsInfty f k :=
  Module.DirectLimit.of ℝ ℕ (fun i => ↥(agreeDForms f k i)) (agreeDFormsMap f k) i

/-- Linear maps out of the direct limit agree if they agree on every `Ωᵏ(Xⁱ)`. -/
theorem agreeDFormsInfty_hom_ext {M : Type*} [AddCommMonoid M] [Module ℝ M]
    {g₁ g₂ : agreeDFormsInfty f k →ₗ[ℝ] M}
    (h : ∀ i (τ : agreeDForms f k i),
      g₁ (agreeDFormsInftyOf f k i τ) = g₂ (agreeDFormsInftyOf f k i τ)) :
    g₁ = g₂ :=
  Module.DirectLimit.hom_ext fun i => LinearMap.ext (h i)

/-- Every element of the direct limit is the class of a form on some `Xⁱ`. -/
theorem agreeDFormsInfty_induction_on {C : agreeDFormsInfty f k → Prop} (z : agreeDFormsInfty f k)
    (h : ∀ i (τ : agreeDForms f k i), C (agreeDFormsInftyOf f k i τ)) : C z :=
  Module.DirectLimit.induction_on z h

theorem agreeDFormsInftyOf_agreeDFormsMap {i j : ℕ} (h : i ≤ j) (τ : agreeDForms f k i) :
    agreeDFormsInftyOf f k j (agreeDFormsMap f k i j h τ) = agreeDFormsInftyOf f k i τ :=
  Module.DirectLimit.of_f

/-! #### `d` -/

theorem formsD_mem_agreeDForms {i : ℕ} {τ : A.forms k i} (h : τ ∈ agreeDForms f k i) :
    A.formsD k i τ ∈ agreeDForms f (k + 1) (i + 1) := by
  refine ⟨h.2, ?_⟩
  change A.formsD (k + 1) (i + 1) (A.formsD k i τ) ∈ agreeForms f (k + 1 + 1) (i + 1 + 1)
  have h0 : A.formsD (k + 1) (i + 1) (A.formsD k i τ) = 0 := Subtype.ext (MPolyfold.extD_extD τ.2)
  rw [h0]
  exact zero_mem _

/-- `d : Ωᵏ(Xⁱ) → Ωᵏ⁺¹(Xⁱ⁺¹)`, restricted. -/
def agreeDFormsD (i : ℕ) : agreeDForms f k i →ₗ[ℝ] agreeDForms f (k + 1) (i + 1) :=
  (A.formsD k i).restrict fun _ h => formsD_mem_agreeDForms f k h

@[simp] lemma coe_agreeDFormsD (i : ℕ) (τ : agreeDForms f k i) :
    (agreeDFormsD f k i τ : A.forms (k + 1) (i + 1)) = A.formsD k i τ := rfl

theorem agreeDFormsD_agreeDFormsMap {i j : ℕ} (h : i ≤ j) (τ : agreeDForms f k i) :
    agreeDFormsD f k j (agreeDFormsMap f k i j h τ) =
      agreeDFormsMap f (k + 1) (i + 1) (j + 1) (Nat.succ_le_succ h) (agreeDFormsD f k i τ) :=
  Subtype.ext (formsD_formsMap A k h τ)

theorem agreeDFormsInftyOf_agreeDFormsD_map {i j : ℕ} (h : i ≤ j) (τ : agreeDForms f k i) :
    agreeDFormsInftyOf f (k + 1) (j + 1) (agreeDFormsD f k j (agreeDFormsMap f k i j h τ)) =
      agreeDFormsInftyOf f (k + 1) (i + 1) (agreeDFormsD f k i τ) := by
  rw [agreeDFormsD_agreeDFormsMap]
  exact agreeDFormsInftyOf_agreeDFormsMap f (k + 1) _ _

/-- `d` on the direct limit. -/
def agreeDFormsInftyD : agreeDFormsInfty f k →ₗ[ℝ] agreeDFormsInfty f (k + 1) :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(agreeDForms f k i)) (agreeDFormsMap f k)
    (fun i => (agreeDFormsInftyOf f (k + 1) (i + 1)).comp (agreeDFormsD f k i)) fun _ _ h τ =>
      agreeDFormsInftyOf_agreeDFormsD_map f k h τ

theorem agreeDFormsInftyD_of (i : ℕ) (τ : agreeDForms f k i) :
    agreeDFormsInftyD f k (agreeDFormsInftyOf f k i τ) =
      agreeDFormsInftyOf f (k + 1) (i + 1) (agreeDFormsD f k i τ) :=
  Module.DirectLimit.lift_of _ _ _

theorem agreeDFormsInftyD_comp_agreeDFormsInftyD :
    (agreeDFormsInftyD f (k + 1)).comp (agreeDFormsInftyD f k) = 0 := by
  refine agreeDFormsInfty_hom_ext f k fun i τ => ?_
  have h : agreeDFormsD f (k + 1) (i + 1) (agreeDFormsD f k i τ) = 0 :=
    Subtype.ext (Subtype.ext (MPolyfold.extD_extD τ.1.2))
  rw [LinearMap.comp_apply, LinearMap.zero_apply, agreeDFormsInftyD_of, agreeDFormsInftyD_of, h]
  exact LinearMap.map_zero _

/-! #### The pull-back `f^*` lands in the agreeing forms -/

theorem formsPullback_mem_agreeDForms (i : ℕ) (ω : B.forms k i) :
    formsPullback f k i ω ∈ agreeDForms f k i := by
  refine ⟨isAgreeingOver_formPullback _ ω.1, ?_⟩
  change A.formsD k i (formsPullback f k i ω) ∈ agreeForms f (k + 1) (i + 1)
  rw [formsD_formsPullback]
  exact isAgreeingOver_formPullback _ _

/-- `(fⁱ)^* : Ωᵏ(Yⁱ) → Ωᵏ(Xⁱ)`, with values in the forms agreeing over `fⁱ`. -/
def agreePullback (i : ℕ) : B.forms k i →ₗ[ℝ] agreeDForms f k i :=
  (formsPullback f k i).codRestrict _ (formsPullback_mem_agreeDForms f k i)

@[simp] lemma coe_agreePullback (i : ℕ) (ω : B.forms k i) :
    (agreePullback f k i ω : A.forms k i) = formsPullback f k i ω := rfl

theorem agreePullback_formsMap {i j : ℕ} (h : i ≤ j) (ω : B.forms k i) :
    agreePullback f k j (B.formsMap k i j h ω) = agreeDFormsMap f k i j h (agreePullback f k i ω) :=
  Subtype.ext (formsPullback_formsMap f k h ω)

theorem agreeDFormsInftyOf_agreePullback_map {i j : ℕ} (h : i ≤ j) (ω : B.forms k i) :
    agreeDFormsInftyOf f k j (agreePullback f k j (B.formsMap k i j h ω)) =
      agreeDFormsInftyOf f k i (agreePullback f k i ω) := by
  rw [agreePullback_formsMap]
  exact agreeDFormsInftyOf_agreeDFormsMap f k _ _

/-- `f^* : Ωᵏ_∞(Y) → Ωᵏ_∞(X)`, with values in the forms agreeing over `f`. -/
def agreeInftyPullback : B.formsInfty k →ₗ[ℝ] agreeDFormsInfty f k :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(B.forms k i)) (B.formsMap k)
    (fun i => (agreeDFormsInftyOf f k i).comp (agreePullback f k i)) fun _ _ h ω =>
      agreeDFormsInftyOf_agreePullback_map f k h ω

theorem agreeInftyPullback_of (i : ℕ) (ω : B.forms k i) :
    agreeInftyPullback f k (B.formsInftyOf k i ω) =
      agreeDFormsInftyOf f k i (agreePullback f k i ω) :=
  Module.DirectLimit.lift_of _ _ _

theorem agreeDFormsD_agreePullback (i : ℕ) (ω : B.forms k i) :
    agreeDFormsD f k i (agreePullback f k i ω) = agreePullback f (k + 1) (i + 1) (B.formsD k i ω) :=
  Subtype.ext (formsD_formsPullback f k i ω)

/-- **`d ∘ f^* = f^* ∘ d`** on the agreeing forms. -/
theorem agreeDFormsInftyD_comp_agreeInftyPullback :
    (agreeDFormsInftyD f k).comp (agreeInftyPullback f k) =
      (agreeInftyPullback f (k + 1)).comp (B.formsInftyD k) := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  change agreeDFormsInftyD f k (agreeInftyPullback f k (B.formsInftyOf k i ω)) =
    agreeInftyPullback f (k + 1) (B.formsInftyD k (B.formsInftyOf k i ω))
  rw [agreeInftyPullback_of, agreeDFormsInftyD_of, formsInftyD_of, agreeInftyPullback_of]
  exact congrArg (agreeDFormsInftyOf f (k + 1) (i + 1)) (agreeDFormsD_agreePullback f k i ω)

/-! #### Forgetting the agreement -/

theorem formsInftyOf_formsMap_coe {i j : ℕ} (h : i ≤ j) (τ : agreeDForms f k i) :
    A.formsInftyOf k j (agreeDFormsMap f k i j h τ : A.forms k j) =
      A.formsInftyOf k i (τ : A.forms k i) :=
  formsInftyOf_formsMap A k h τ

/-- The inclusion of the agreeing forms into `Ωᵏ_∞(X)`. -/
def agreeDFormsInftyIncl : agreeDFormsInfty f k →ₗ[ℝ] A.formsInfty k :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(agreeDForms f k i)) (agreeDFormsMap f k)
    (fun i => (A.formsInftyOf k i).comp (agreeDForms f k i).subtype) fun _ _ h τ =>
      formsInftyOf_formsMap_coe f k h τ

theorem agreeDFormsInftyIncl_of (i : ℕ) (τ : agreeDForms f k i) :
    agreeDFormsInftyIncl f k (agreeDFormsInftyOf f k i τ) = A.formsInftyOf k i τ :=
  Module.DirectLimit.lift_of _ _ _

/-- The inclusion composed with `f^*` is the pull-back `formsInftyPullback`. -/
theorem agreeDFormsInftyIncl_comp_agreeInftyPullback :
    (agreeDFormsInftyIncl f k).comp (agreeInftyPullback f k) = formsInftyPullback f k := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  change agreeDFormsInftyIncl f k (agreeInftyPullback f k (B.formsInftyOf k i ω)) =
    formsInftyPullback f k (B.formsInftyOf k i ω)
  rw [agreeInftyPullback_of, agreeDFormsInftyIncl_of, formsInftyPullback_of]
  rfl

/-- The inclusion commutes with `d`. -/
theorem formsInftyD_comp_agreeDFormsInftyIncl :
    (A.formsInftyD k).comp (agreeDFormsInftyIncl f k) =
      (agreeDFormsInftyIncl f (k + 1)).comp (agreeDFormsInftyD f k) := by
  refine agreeDFormsInfty_hom_ext f k fun i τ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, agreeDFormsInftyIncl_of, agreeDFormsInftyD_of,
    formsInftyD_of, agreeDFormsInftyIncl_of]
  rfl

/-! #### An empty `X` -/

theorem isEmpty_lift_carrier [h : IsEmpty A.carrier] : ∀ i, IsEmpty (A.lift i).carrier
  | 0 => h
  | i + 1 => ⟨fun x => (isEmpty_lift_carrier i).false ((A.lift i).P.levelVal 1 x)⟩

theorem subsingleton_forms [IsEmpty A.carrier] (j i : ℕ) : Subsingleton (A.forms j i) :=
  ⟨fun _ _ => Subtype.ext (funext fun x =>
    ((isEmpty_lift_carrier (A := A) i).false ((A.lift i).P.levelVal 1 x)).elim)⟩

theorem subsingleton_agreeDForms [IsEmpty A.carrier] (i : ℕ) : Subsingleton (agreeDForms f k i) :=
  ⟨fun _ _ => Subtype.ext ((subsingleton_forms (A := A) k i).elim _ _)⟩

/-- **Over an empty `X` there is only the zero form**. -/
theorem subsingleton_agreeDFormsInfty [IsEmpty A.carrier] :
    Subsingleton (agreeDFormsInfty f k) := by
  have h0 : ∀ z : agreeDFormsInfty f k, z = 0 := fun z =>
    agreeDFormsInfty_induction_on f k (C := fun z => z = 0) z fun i τ => by
      rw [(subsingleton_agreeDForms f k i).elim τ 0]
      exact (agreeDFormsInftyOf f k i).map_zero
  exact ⟨fun a b => (h0 a).trans (h0 b).symm⟩

end BundledMPolyfold

/-! ### Forms on `∂X` and the relative complex -/

namespace MPolyfold

open BundledMPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  (hP : P.IsTame) (k : ℕ)

/-- The tame boundary `bX` (2021 Theorem 2.7.13), bundled. -/
abbrev bdry : BundledMPolyfold.{u} := BundledMPolyfold.of (P.tameBoundaryPolyfold hP)

/-- `B : bX → X` (2021 Definition 2.7.14), as an sc-smooth map (Theorem 2.7.13 (3)). -/
def bdryMap : ScMap (bdry hP).P (BundledMPolyfold.of P).P :=
  ⟨P.tameBoundaryMap hP, P.tameBoundaryMap_isScSmooth hP⟩

variable {k} in
/-- **2021 p. 198 (2017 p. 150; preprint p. 168): forms agreeing on intersections of local faces**,
read as agreement over `Bⁱ : bXⁱ → Xⁱ`: on two local faces through the same point the forms coincide
on vectors with the same image in `TXⁱ` (the text's "forms on `∂X`", see the module docstring). -/
def IsFaceCompatible (i : ℕ)
    (τ : ∀ x : ((bdry hP).lift i).P.Level 1, ((bdry hP).lift i).P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    Prop :=
  IsAgreeingOver ((bdry hP).liftMap (bdryMap hP) i).isScSmoothMap τ

/-- **2021 p. 198 (2017 p. 150; preprint p. 168): `Ωᵏ(∂Xⁱ)`**, read as the sc-forms `τ` on `bXⁱ`
such that `τ` agrees over `Bⁱ` and `dτ` agrees over `Bⁱ⁺¹`.  The text gives no definition; the
second condition is explained in the module docstring. -/
abbrev bForms (i : ℕ) : Submodule ℝ ((bdry hP).forms k i) := agreeDForms (bdryMap hP) k i

theorem mem_bForms {i : ℕ} {τ : (bdry hP).forms k i} :
    τ ∈ bForms hP k i ↔ IsFaceCompatible hP i τ.1 ∧ IsFaceCompatible hP (i + 1) (extD τ.1) :=
  Iff.rfl

/-- **`Ω*(∂X)` is the largest subcomplex of agreeing forms**: every family of subspaces of
`Ω*(bX)` consisting of forms that agree over `B`, and mapped into itself by `d`, lies in
`Ω*(∂X)`.  So `Ω*(∂X)` is the agreeing forms whenever they form a complex. -/
theorem le_bForms {V : ∀ n i, Submodule ℝ ((bdry hP).forms n i)}
    (hV : ∀ n i, ∀ τ ∈ V n i, IsFaceCompatible hP i τ.1)
    (hd : ∀ n i (τ : (bdry hP).forms n i), τ ∈ V n i → (bdry hP).formsD n i τ ∈ V (n + 1) (i + 1))
    (n i : ℕ) : V n i ≤ bForms hP n i :=
  le_agreeDForms _ (fun n i τ hτ => hV n i τ hτ) hd n i

/-- **2021 p. 199 (2017 p. 150; preprint p. 168): `d : Ωᵏ(∂Xⁱ) → Ωᵏ⁺¹(∂Xⁱ⁺¹)`**, implicit in the
text's `dτ`: `d` preserves the agreement (of `τ` and of `dτ`), by `d ∘ d = 0`. -/
theorem extD_mem_bForms {i : ℕ} {τ : (bdry hP).forms k i} (h : τ ∈ bForms hP k i) :
    (bdry hP).formsD k i τ ∈ bForms hP (k + 1) (i + 1) :=
  formsD_mem_agreeDForms _ k h

/-- `ι^* : Ωᵏ(∂Xⁱ) → Ωᵏ(∂Xⁱ⁺¹)`, the maps of (4.4) on the forms on `∂X`. -/
theorem formLower_mem_bForms {i : ℕ} {τ : (bdry hP).forms k i} (h : τ ∈ bForms hP k i) :
    (bdry hP).formsStep k i τ ∈ bForms hP k (i + 1) :=
  formsStep_mem_agreeDForms _ k h

/-- **2021 p. 198 (2017 p. 150; preprint p. 168): `Ωᵏ_∞(∂X)`**, the direct limit of the
`Ωᵏ(∂Xⁱ)` under the maps of (4.4), as `Ωᵏ_∞(X)` in Definition 4.4.2. -/
abbrev bFormsInfty : Type _ := agreeDFormsInfty (bdryMap hP) k

/-- **2021 p. 199: `d : Ωᵏ_∞(∂X) → Ωᵏ⁺¹_∞(∂X)`**, the limit of `d : Ωᵏ(∂Xⁱ) → Ωᵏ⁺¹(∂Xⁱ⁺¹)`. -/
abbrev bFormsInftyD : bFormsInfty hP k →ₗ[ℝ] bFormsInfty hP (k + 1) := agreeDFormsInftyD _ k

/-- `d² = 0` on `Ω*_∞(∂X)`. -/
theorem bFormsInftyD_comp_bFormsInftyD :
    (bFormsInftyD hP (k + 1)).comp (bFormsInftyD hP k) = 0 :=
  agreeDFormsInftyD_comp_agreeDFormsInftyD _ k

/-- **2021 p. 199 (2017 p. 150; preprint p. 168): `j^* : Ωᵏ_∞(X) → Ωᵏ_∞(∂X)`** for the inclusion
`j : ∂X → X`, read as `B : bX → X`: the pull-back `B^*` (`formsInftyPullback`), with values in the
forms on `∂X`. -/
abbrev jStar : (BundledMPolyfold.of P).formsInfty k →ₗ[ℝ] bFormsInfty hP k :=
  agreeInftyPullback (bdryMap hP) k

/-- **2021 p. 199 (2017 p. 150; preprint p. 168): `d j^* = j^* d`**, on which the text's
"`d ∘ d = 0`" rests (Findings, Chapter 4, item 121): from `d f^* = f^* d` (2021 p. 198). -/
theorem jStar_comp_D :
    (bFormsInftyD hP k).comp (jStar hP k) =
      (jStar hP (k + 1)).comp ((BundledMPolyfold.of P).formsInftyD k) :=
  agreeDFormsInftyD_comp_agreeInftyPullback _ k

/-- `j^*ω` agrees over `B`: the agreement condition is satisfiable by every pull-back. -/
theorem isFaceCompatible_formPullback (i : ℕ) (ω : (BundledMPolyfold.of P).forms k i) :
    IsFaceCompatible hP i (formsPullback (bdryMap hP) k i ω).1 :=
  isAgreeingOver_formPullback _ _

/-- **`j^*ω ∈ Ωᵏ(∂Xⁱ)`** for every `ω ∈ Ωᵏ(Xⁱ)`: `j^*ω` and `d(j^*ω) = j^*(dω)` agree over `B`. -/
theorem formsPullback_mem_bForms (i : ℕ) (ω : (BundledMPolyfold.of P).forms k i) :
    formsPullback (bdryMap hP) k i ω ∈ bForms hP k i :=
  formsPullback_mem_agreeDForms _ k i ω

/-- `j^*[ω] = [j^*ω]` on representatives. -/
theorem jStar_of (i : ℕ) (ω : (BundledMPolyfold.of P).forms k i) :
    jStar hP k ((BundledMPolyfold.of P).formsInftyOf k i ω) =
      agreeDFormsInftyOf (bdryMap hP) k i ⟨_, formsPullback_mem_bForms hP k i ω⟩ :=
  agreeInftyPullback_of _ k i ω

/-- **2021 p. 199 (2017 p. 150; preprint p. 168): `Ω*_∞(X, ∂X) = Ω*_∞(X) ⊕ Ω*⁻¹_∞(∂X)`**, degree by
degree: `Ω⁰_∞(X)` in degree `0` (`Ω⁻¹ = 0`), `Ωᵏ⁺¹_∞(X) × Ωᵏ_∞(∂X)` in degree `k + 1`. -/
def RelForms : ℕ → Type (max 1 u)
  | 0 => (BundledMPolyfold.of P).formsInfty 0
  | k + 1 => (BundledMPolyfold.of P).formsInfty (k + 1) × bFormsInfty hP k

/-- The additive monoid of `RelForms hP k` (not an instance: the instance is
`addCommGroupRelForms`). -/
@[reducible] def addCommMonoidRelForms : ∀ k, AddCommMonoid (RelForms hP k)
  | 0 => addCommMonoid_formsInfty (BundledMPolyfold.of P) 0
  | k + 1 => @Prod.instAddCommMonoid _ _ (addCommMonoid_formsInfty (BundledMPolyfold.of P) (k + 1))
      AddCommGroup.toAddCommMonoid

/-- The vector space structure of `RelForms hP k`, over `addCommMonoidRelForms`. -/
@[reducible] def moduleRelForms' : ∀ k, @Module ℝ (RelForms hP k) _ (addCommMonoidRelForms hP k)
  | 0 => module_formsInfty (BundledMPolyfold.of P) 0
  | k + 1 => @Prod.instModule ℝ _ _ _ _ _ (module_formsInfty (BundledMPolyfold.of P) (k + 1))
      (module_agreeDFormsInfty (bdryMap hP) k)

/-- `RelForms hP k` is an additive group, with `-η = (-1) • η`. -/
@[reducible] def addCommGroupRelForms : AddCommGroup (RelForms hP k) :=
  @Module.addCommMonoidToAddCommGroup ℝ (RelForms hP k) _ (addCommMonoidRelForms hP k)
    (moduleRelForms' hP k)

attribute [instance] addCommGroupRelForms

/-- `RelForms hP k` is a real vector space. -/
@[reducible] def moduleRelForms : Module ℝ (RelForms hP k) := moduleRelForms' hP k

attribute [instance] moduleRelForms

/-- The relative `d` in degree `0`: `ω ↦ (dω, j^*ω)`. -/
def relDZero : (BundledMPolyfold.of P).formsInfty 0 →ₗ[ℝ]
    (BundledMPolyfold.of P).formsInfty 1 × bFormsInfty hP 0 :=
  LinearMap.prod ((BundledMPolyfold.of P).formsInftyD 0) (jStar hP 0)

/-- The relative `d` in degree `k + 1`: `(ω, τ) ↦ (dω, j^*ω − dτ)`. -/
def relDSucc : (BundledMPolyfold.of P).formsInfty (k + 1) × bFormsInfty hP k →ₗ[ℝ]
    (BundledMPolyfold.of P).formsInfty (k + 1 + 1) × bFormsInfty hP (k + 1) :=
  LinearMap.prod (((BundledMPolyfold.of P).formsInftyD (k + 1)).comp
      (LinearMap.fst ℝ ((BundledMPolyfold.of P).formsInfty (k + 1)) (bFormsInfty hP k)))
    ((jStar hP (k + 1)).comp
        (LinearMap.fst ℝ ((BundledMPolyfold.of P).formsInfty (k + 1)) (bFormsInfty hP k)) -
      (bFormsInftyD hP k).comp
        (LinearMap.snd ℝ ((BundledMPolyfold.of P).formsInfty (k + 1)) (bFormsInfty hP k)))

@[simp] lemma relDZero_apply (ω : (BundledMPolyfold.of P).formsInfty 0) :
    relDZero hP ω = ((BundledMPolyfold.of P).formsInftyD 0 ω, jStar hP 0 ω) := rfl

@[simp] lemma relDSucc_apply (η : (BundledMPolyfold.of P).formsInfty (k + 1) × bFormsInfty hP k) :
    relDSucc hP k η = ((BundledMPolyfold.of P).formsInftyD (k + 1) η.1,
      jStar hP (k + 1) η.1 - bFormsInftyD hP k η.2) := rfl

/-- **2021 p. 199 (2017 p. 150; preprint p. 168): the differential of `Ω*_∞(X, ∂X)`**,
`d(ω, τ) = (dω, j^*ω − dτ)` (and `dω = (dω, j^*ω)` in degree `0`), as printed. -/
def relD : ∀ k, RelForms hP k →ₗ[ℝ] RelForms hP (k + 1)
  | 0 => relDZero hP
  | k + 1 => relDSucc hP k

lemma relD_zero : relD hP 0 = relDZero hP := rfl

lemma relD_succ : relD hP (k + 1) = relDSucc hP k := rfl

theorem relDSucc_comp_relDZero : (relDSucc hP 0).comp (relDZero hP) = 0 := by
  refine LinearMap.ext fun ω => ?_
  rw [LinearMap.comp_apply, relDZero_apply, relDSucc_apply, LinearMap.zero_apply]
  refine Prod.ext ?_ ?_
  · exact LinearMap.congr_fun ((BundledMPolyfold.of P).formsInftyD_comp_formsInftyD 0) ω
  · exact sub_eq_zero.2 (LinearMap.congr_fun (jStar_comp_D hP 0) ω).symm

theorem relDSucc_comp_relDSucc : (relDSucc hP (k + 1)).comp (relDSucc hP k) = 0 := by
  refine LinearMap.ext fun η => ?_
  rw [LinearMap.comp_apply, relDSucc_apply, relDSucc_apply, LinearMap.zero_apply]
  refine Prod.ext ?_ ?_
  · exact LinearMap.congr_fun ((BundledMPolyfold.of P).formsInftyD_comp_formsInftyD (k + 1)) η.1
  · change jStar hP (k + 1 + 1) ((BundledMPolyfold.of P).formsInftyD (k + 1) η.1) -
      bFormsInftyD hP (k + 1) (jStar hP (k + 1) η.1 - bFormsInftyD hP k η.2) = 0
    rw [map_sub, ← LinearMap.comp_apply (bFormsInftyD hP (k + 1)) (jStar hP (k + 1)),
      jStar_comp_D, ← LinearMap.comp_apply (bFormsInftyD hP (k + 1)) (bFormsInftyD hP k),
      bFormsInftyD_comp_bFormsInftyD, LinearMap.zero_apply, sub_zero, LinearMap.comp_apply,
      sub_self]

/-- **2021 p. 199 (2017 p. 150; preprint p. 168): `d ∘ d = 0` on `Ω*_∞(X, ∂X)`** ("one easily
verifies"): proved from `d² = 0` on `Ω*_∞(X)` and `Ω*_∞(∂X)` and `d j^* = j^* d`. -/
theorem relD_comp_relD : ∀ k, (relD hP (k + 1)).comp (relD hP k) = 0
  | 0 => relDSucc_comp_relDZero hP
  | k + 1 => relDSucc_comp_relDSucc hP k

/-- `d(dη) = 0` for every relative form `η`. -/
theorem relD_relD (η : RelForms hP k) : relD hP (k + 1) (relD hP k η) = 0 :=
  LinearMap.congr_fun (relD_comp_relD hP k) η

/-! ### The relative cohomology `H*_dR(X, ∂X)` -/

/-- The image of `d` in `RelForms hP k` (`0` in degree `0`). -/
def relDRange : ∀ k, Submodule ℝ (RelForms hP k)
  | 0 => ⊥
  | k + 1 => LinearMap.range (relD hP k)

theorem relDRange_le_ker : ∀ k, relDRange hP k ≤ LinearMap.ker (relD hP k)
  | 0 => bot_le
  | k + 1 => by
    rintro _ ⟨η, rfl⟩
    exact relD_relD hP k η

/-- **2021 p. 199 (2017 p. 150; preprint p. 168): the relative cohomology `Hᵏ_dR(X, ∂X)`**, degree
by degree: `ker d / im d` of the relative complex, a real vector space. -/
abbrev relDeRham : Type _ :=
  LinearMap.ker (relD hP k) ⧸ (relDRange hP k).comap (LinearMap.ker (relD hP k)).subtype

/-- The class in `Hᵏ_dR(X, ∂X)` of a closed relative form. -/
abbrev relDeRhamMk : LinearMap.ker (relD hP k) →ₗ[ℝ] relDeRham hP k :=
  Submodule.mkQ _

/-- Two closed relative forms have the same class iff they differ by an exact one. -/
theorem relDeRhamMk_eq_iff (η θ : LinearMap.ker (relD hP k)) :
    relDeRhamMk hP k η = relDeRhamMk hP k θ ↔
      (η : RelForms hP k) - (θ : RelForms hP k) ∈ relDRange hP k :=
  Submodule.Quotient.eq _

/-! ### `X` without boundary -/

section NoBoundary

variable {hP}

/-- **For `∂X = ∅` the tame boundary is empty**: `d_X(B p) = d_{bX}(p) + 1 ≥ 1`
(Theorem 2.7.13 (4)). -/
theorem isEmpty_tameBoundarySpace (h : P.IsWithoutBoundary) : IsEmpty (P.TameBoundarySpace hP) :=
  ⟨fun p => by
    have e := P.degIndex_tameBoundaryMap hP p
    rw [h] at e
    omega⟩

/-- For `∂X = ∅`, `Ωᵏ_∞(∂X) = 0`. -/
theorem subsingleton_bFormsInfty (h : P.IsWithoutBoundary) : Subsingleton (bFormsInfty hP k) :=
  haveI : IsEmpty (bdry hP).carrier := isEmpty_tameBoundarySpace (hP := hP) h
  subsingleton_agreeDFormsInfty (A := bdry hP) _ k

/-- For `∂X = ∅`, `RelForms hP k ≃ Ωᵏ_∞(X)`, `(ω, τ) ↦ ω`. -/
def relFormsEquiv (h : P.IsWithoutBoundary) :
    ∀ k, RelForms hP k ≃ₗ[ℝ] (BundledMPolyfold.of P).formsInfty k
  | 0 => LinearEquiv.refl ℝ _
  | k + 1 =>
    haveI := subsingleton_bFormsInfty (hP := hP) k h
    @LinearEquiv.prodUnique ℝ _ _ _ _ _ _ _ (uniqueOfSubsingleton 0)

lemma relFormsEquiv_zero_apply (h : P.IsWithoutBoundary) (ω : RelForms hP 0) :
    relFormsEquiv h 0 ω = ω := rfl

lemma relFormsEquiv_succ_apply (h : P.IsWithoutBoundary) (η : RelForms hP (k + 1)) :
    relFormsEquiv h (k + 1) η =
      (η : (BundledMPolyfold.of P).formsInfty (k + 1) × bFormsInfty hP k).1 := rfl

/-- Under `relFormsEquiv`, the relative `d` is `d`. -/
theorem relFormsEquiv_relD (h : P.IsWithoutBoundary) :
    ∀ k (η : RelForms hP k), relFormsEquiv h (k + 1) (relD hP k η) =
      (BundledMPolyfold.of P).formsInftyD k (relFormsEquiv h k η)
  | 0, _ => rfl
  | _ + 1, _ => rfl

/-- `relFormsEquiv` maps the closed relative forms onto the closed forms. -/
theorem map_ker_relD (h : P.IsWithoutBoundary) :
    (LinearMap.ker (relD hP k)).map
        (relFormsEquiv h k : RelForms hP k →ₗ[ℝ] (BundledMPolyfold.of P).formsInfty k) =
      LinearMap.ker ((BundledMPolyfold.of P).formsInftyD k) := by
  ext ω
  constructor
  · rintro ⟨η, hη, rfl⟩
    have hη' : relD hP k η = 0 := hη
    change (BundledMPolyfold.of P).formsInftyD k (relFormsEquiv h k η) = 0
    rw [← relFormsEquiv_relD, hη', map_zero]
  · intro hω
    have hω' : (BundledMPolyfold.of P).formsInftyD k ω = 0 := hω
    refine ⟨(relFormsEquiv h k).symm ω, ?_, (relFormsEquiv h k).apply_symm_apply ω⟩
    change relD hP k ((relFormsEquiv h k).symm ω) = 0
    apply (relFormsEquiv h (k + 1)).injective
    rw [relFormsEquiv_relD, LinearEquiv.apply_symm_apply, hω', map_zero]

/-- `relFormsEquiv` maps the exact relative forms onto the exact forms. -/
theorem relFormsEquiv_mem_formsInftyDRange_iff (h : P.IsWithoutBoundary) :
    ∀ k (η : RelForms hP k),
      relFormsEquiv h k η ∈ (BundledMPolyfold.of P).formsInftyDRange k ↔ η ∈ relDRange hP k
  | 0, η => by
    change relFormsEquiv h 0 η ∈ (⊥ : Submodule ℝ _) ↔ η ∈ (⊥ : Submodule ℝ (RelForms hP 0))
    rw [Submodule.mem_bot, Submodule.mem_bot]
    rfl
  | k + 1, η => by
    change relFormsEquiv h (k + 1) η ∈ LinearMap.range ((BundledMPolyfold.of P).formsInftyD k) ↔
      η ∈ LinearMap.range (relD hP k)
    constructor
    · rintro ⟨ω, hω⟩
      refine ⟨(relFormsEquiv h k).symm ω, (relFormsEquiv h (k + 1)).injective ?_⟩
      rw [relFormsEquiv_relD, LinearEquiv.apply_symm_apply, hω]
    · rintro ⟨θ, rfl⟩
      exact ⟨relFormsEquiv h k θ, (relFormsEquiv_relD h k θ).symm⟩

/-- For `∂X = ∅`, the closed relative forms are the closed forms. -/
def kerRelDEquiv (h : P.IsWithoutBoundary) :
    LinearMap.ker (relD hP k) ≃ₗ[ℝ] LinearMap.ker ((BundledMPolyfold.of P).formsInftyD k) :=
  ((relFormsEquiv h k).submoduleMap _).trans (LinearEquiv.ofEq _ _ (map_ker_relD k h))

lemma coe_kerRelDEquiv (h : P.IsWithoutBoundary) (η : LinearMap.ker (relD hP k)) :
    (kerRelDEquiv k h η : (BundledMPolyfold.of P).formsInfty k) = relFormsEquiv h k η := rfl

theorem map_kerRelDEquiv (h : P.IsWithoutBoundary) :
    ((relDRange hP k).comap (LinearMap.ker (relD hP k)).subtype).map
        (kerRelDEquiv k h : LinearMap.ker (relD hP k) →ₗ[ℝ] _) =
      ((BundledMPolyfold.of P).formsInftyDRange k).comap
        (LinearMap.ker ((BundledMPolyfold.of P).formsInftyD k)).subtype := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext y
  rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.mem_comap, Submodule.coe_subtype,
    Submodule.coe_subtype, ← relFormsEquiv_mem_formsInftyDRange_iff h k, ← coe_kerRelDEquiv,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- **2021 p. 279 (after the proof of Theorem 6.7.1; 2017: after Theorem 6.4; preprint p. 233):
for `∂X = ∅`, `Hᵏ_dR(X, ∂X) ≃ Hᵏ_sc(X)`** (Definition 4.4.6): the text passes from `H*_dR(X, ∂X)`
to `H*_dR(X)` there; here `bX = ∅`, so the relative complex is `Ω*_∞(X)` with `d`. -/
def relDeRhamEquivOfNoBoundary (h : P.IsWithoutBoundary) :
    relDeRham hP k ≃ₗ[ℝ] (BundledMPolyfold.of P).scDeRham k :=
  Submodule.Quotient.equiv _ _ (kerRelDEquiv k h) (map_kerRelDEquiv k h)

theorem relDeRhamEquivOfNoBoundary_mk (h : P.IsWithoutBoundary) (η : LinearMap.ker (relD hP k)) :
    relDeRhamEquivOfNoBoundary k h (relDeRhamMk hP k η) =
      (BundledMPolyfold.of P).scDeRhamMk k (kerRelDEquiv k h η) := rfl

end NoBoundary

end MPolyfold

end Polyfold
