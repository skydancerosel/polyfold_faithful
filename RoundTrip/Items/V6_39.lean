import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_39

/-! Round trip for V6_39 (continuation along paths and the isomorphisms `Φ_{E_t}`, p. 224).

A (universes at `0`): the continuation lemmas `SubspaceFamily.cont_eq`, `cont_self`, `cont_trans`,
`cont_comp`, `cont_eq_transport` and the push-forward lemmas `propagate_self`, `propagate_trans`,
`propagate_comp` — linear algebra of `λ(L)` over an arbitrary simply connected, locally
path-connected base `Q`, for given stabilized end points.

B: for choices `s, s₁, …, s_k` with the text's pointwise (P), read in a chart, (1) `T_0, T_1 ∈ Lin`,
(2) every `T_t` Fredholm and `T_t ⊕ φ_t` onto, (3) `Φ_{E_t}` bijective, (4) the `L_t` a continuous
family, (5) unique continuation of rays along such a family.

* `A_to_B5`: B's conjunct (5) (for every family over `J` in any normed space) follows from A
  (uniqueness from `cont_eq`; existence is the non-item `exists_lineOrientation_apply_eq`);
  `B3_holds`: conjunct (3) is the non-item `stabIota_bijective`.
* B's (1), (2), (4) are Lemmas 6.29–6.31 under the text's pointwise (P) (general position of `F_t`
  for each fixed `t`, on `ℝᵏ × X`); A says nothing about them, and the project proves the
  corresponding facts (`exists_isStabKernels`, V6_42) only under a different (P) (general position
  of the parametrized section on `ℝᵏ × ℝ × X` near `[0, 1]`, with `f + S = 0` near `[0, 1]`).
  `A ⇒ B` is not proved.
* `B_to_A` is proved OUTRIGHT (`A_outright`, the item's proofs redone from
  `exists_lineOrientation_apply_eq`, `LineOrientation.eq_of_apply_eq`, `transport_comp`), without
  using B: vacuous for the audit.  From B itself A does not follow: B's (5) is only for `J` and
  only under the hypotheses of the passage, A is over every simply connected `Q`.
-/

namespace RoundTrip.V6_39
open Polyfold Set

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.SubspaceFamily.cont_eq.{0, 0} ∧
  type_of% @Polyfold.SubspaceFamily.cont_self.{0, 0} ∧
  type_of% @Polyfold.SubspaceFamily.cont_trans.{0, 0} ∧
  type_of% @Polyfold.SubspaceFamily.cont_comp.{0, 0, 0} ∧
  type_of% @Polyfold.SubspaceFamily.cont_eq_transport.{0, 0} ∧
  type_of% @Polyfold.propagate_self.{0, 0, 0, 0} ∧
  type_of% @Polyfold.propagate_trans.{0, 0, 0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.propagate_comp.{0, 0, 0, 0, 0, 0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.SubspaceFamily.cont_eq.{0, 0}, @Polyfold.SubspaceFamily.cont_self.{0, 0},
    @Polyfold.SubspaceFamily.cont_trans.{0, 0}, @Polyfold.SubspaceFamily.cont_comp.{0, 0, 0},
    @Polyfold.SubspaceFamily.cont_eq_transport.{0, 0}, @Polyfold.propagate_self.{0, 0, 0, 0},
    @Polyfold.propagate_trans.{0, 0, 0, 0, 0, 0, 0, 0},
    @Polyfold.propagate_comp.{0, 0, 0, 0, 0, 0, 0}⟩

/-! ### The parts of B that A (or a non-item lemma) gives -/

/-- B's conjunct (5), for every continuous family over `J` in any normed space. -/
def B5 : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (Λ : SubspaceFamily J W)
    (r : Module.Ray ℝ (Λ.det iccZero)), ∃! ω : LineOrientation Λ.det, ω.1 iccZero = r

/-- `A ⇒ (5)`: uniqueness from A's `cont_eq` (existence from `exists_lineOrientation_apply_eq`). -/
theorem A_to_B5 : A → B5 := by
  intro hA W _ _ Λ r
  obtain ⟨ω, hω⟩ := exists_lineOrientation_apply_eq (L := Λ.det) iccZero r
  refine ⟨ω, hω, fun ω' hω' => ?_⟩
  refine Subtype.ext (funext fun q => ?_)
  have h1 := hA.1 Λ ω' iccZero q
  have h2 := hA.1 Λ ω iccZero q
  change ω' iccZero = r at hω'
  rw [hω'] at h1
  rw [hω] at h2
  exact h1.symm.trans h2

/-- B's conjunct (3) is the non-item `stabIota_bijective`. -/
theorem B3_holds {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} (T : E →L[ℝ] F)
    (φ : (Fin k → ℝ) →L[ℝ] F) (h₁ : T.IsFredholm) (h₂ : Function.Surjective (T.coprod φ)) :
    Function.Bijective (stabIota h₁ h₂) :=
  stabIota_bijective h₁ h₂

/-! ### A outright (the item's proofs redone from non-item lemmas) -/

section Outright

variable {Q : Type} [TopologicalSpace Q] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (Λ : SubspaceFamily Q W)

section
variable [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]

theorem cont_eq' (o : LineOrientation Λ.det) (q₀ q₁ : Q) :
    Λ.cont q₀ q₁ (o q₀) = o q₁ := by
  have h := LineOrientation.eq_of_apply_eq q₀
    (exists_lineOrientation_apply_eq (L := Λ.det) q₀ (o q₀)).choose_spec
  exact congrArg (fun o : LineOrientation Λ.det => o q₁) h

theorem cont_self' (q : Q) (r : Module.Ray ℝ (Λ.det q)) : Λ.cont q q r = r :=
  (exists_lineOrientation_apply_eq (L := Λ.det) q r).choose_spec

theorem cont_trans' (q₀ q₁ q₂ : Q) (r : Module.Ray ℝ (Λ.det q₀)) :
    Λ.cont q₁ q₂ (Λ.cont q₀ q₁ r) = Λ.cont q₀ q₂ r := by
  obtain ⟨o, rfl⟩ := exists_lineOrientation_apply_eq (L := Λ.det) q₀ r
  rw [cont_eq' Λ o q₀ q₁, cont_eq' Λ o q₁ q₂, cont_eq' Λ o q₀ q₂]

theorem cont_comp' {Q' : Type} [TopologicalSpace Q'] [SimplyConnectedSpace Q']
    [LocallyPathConnectedSpace Q'] (g : C(Q', Q)) (q₀ q₁ : Q')
    (r : Module.Ray ℝ (Λ.det (g q₀))) :
    (Λ.comp g).cont q₀ q₁ r = Λ.cont (g q₀) (g q₁) r := by
  obtain ⟨o, rfl⟩ := exists_lineOrientation_apply_eq (L := Λ.det) (g q₀) r
  exact (cont_eq' (Λ.comp g) (o.comp g) q₀ q₁).trans (cont_eq' Λ o (g q₀) (g q₁)).symm

open unitInterval in
theorem cont_eq_transport' (γ : C(I, Q)) (r : Module.Ray ℝ (Λ.det (γ 0))) :
    (Λ.comp γ).transport r = Λ.cont (γ 0) (γ 1) r := by
  obtain ⟨o, rfl⟩ := exists_lineOrientation_apply_eq (L := Λ.det) (γ 0) r
  exact (Λ.transport_comp o γ).trans (cont_eq' Λ o (γ 0) (γ 1)).symm

end

end Outright

section OutrightProp

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

variable {k : ℕ} {T : E →L[ℝ] F} {φ : (Fin k → ℝ) →L[ℝ] F}

variable {Q : Type} [TopologicalSpace Q] [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (Λ : SubspaceFamily Q W)
  {E₁ F₁ : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [CompleteSpace F₁]
  {k₁ : ℕ} {T₁ : E₁ →L[ℝ] F₁} {φ₁ : (Fin k₁ → ℝ) →L[ℝ] F₁}

omit [CompleteSpace E] [CompleteSpace F] in
theorem propagate_self' (q : Q) (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] Λ.L q) (r : Module.Ray ℝ (fredholmDet T)) :
    propagate Λ q q hT hφ ι hT hφ ι r = r :=
  (congrArg (stabRayEquiv hT hφ ι).symm (cont_self' Λ q (stabRayEquiv hT hφ ι r))).trans
    ((stabRayEquiv hT hφ ι).symm_apply_apply r)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E₁] [CompleteSpace F₁] in
theorem propagate_trans' {E₂ F₂ : Type} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [CompleteSpace E₂] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [CompleteSpace F₂]
    {k₂ : ℕ} {T₂ : E₂ →L[ℝ] F₂} {φ₂ : (Fin k₂ → ℝ) →L[ℝ] F₂} (q₀ q₁ q₂ : Q)
    (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] Λ.L q₀)
    (hT₁ : T₁.IsFredholm) (hφ₁ : Function.Surjective (T₁.coprod φ₁))
    (ι₁ : LinearMap.ker ((T₁.coprod φ₁ : E₁ × (Fin k₁ → ℝ) →L[ℝ] F₁) :
      E₁ × (Fin k₁ → ℝ) →ₗ[ℝ] F₁) ≃ₗ[ℝ] Λ.L q₁)
    (hT₂ : T₂.IsFredholm) (hφ₂ : Function.Surjective (T₂.coprod φ₂))
    (ι₂ : LinearMap.ker ((T₂.coprod φ₂ : E₂ × (Fin k₂ → ℝ) →L[ℝ] F₂) :
      E₂ × (Fin k₂ → ℝ) →ₗ[ℝ] F₂) ≃ₗ[ℝ] Λ.L q₂) (r : Module.Ray ℝ (fredholmDet T)) :
    propagate Λ q₁ q₂ hT₁ hφ₁ ι₁ hT₂ hφ₂ ι₂ (propagate Λ q₀ q₁ hT hφ ι hT₁ hφ₁ ι₁ r) =
      propagate Λ q₀ q₂ hT hφ ι hT₂ hφ₂ ι₂ r :=
  (congrArg (fun x : Module.Ray ℝ (Λ.det q₁) => (stabRayEquiv hT₂ hφ₂ ι₂).symm
      (Λ.cont q₁ q₂ x)) ((stabRayEquiv hT₁ hφ₁ ι₁).apply_symm_apply _)).trans
    (congrArg (stabRayEquiv hT₂ hφ₂ ι₂).symm (cont_trans' Λ q₀ q₁ q₂ (stabRayEquiv hT hφ ι r)))

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E₁] [CompleteSpace F₁] in
theorem propagate_comp' {Q' : Type} [TopologicalSpace Q'] [SimplyConnectedSpace Q']
    [LocallyPathConnectedSpace Q'] (g : C(Q', Q)) (q₀ q₁ : Q')
    (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] Λ.L (g q₀))
    (hT₁ : T₁.IsFredholm) (hφ₁ : Function.Surjective (T₁.coprod φ₁))
    (ι₁ : LinearMap.ker ((T₁.coprod φ₁ : E₁ × (Fin k₁ → ℝ) →L[ℝ] F₁) :
      E₁ × (Fin k₁ → ℝ) →ₗ[ℝ] F₁) ≃ₗ[ℝ] Λ.L (g q₁)) (r : Module.Ray ℝ (fredholmDet T)) :
    propagate (Λ.comp g) q₀ q₁ hT hφ ι hT₁ hφ₁ ι₁ r =
      propagate Λ (g q₀) (g q₁) hT hφ ι hT₁ hφ₁ ι₁ r :=
  congrArg (stabRayEquiv hT₁ hφ₁ ι₁).symm (cont_comp' Λ g q₀ q₁ (stabRayEquiv hT hφ ι r))

end OutrightProp

/-- **A outright**, without the item's theorems. -/
theorem A_outright : A :=
  ⟨@cont_eq', @cont_self', @cont_trans', @cont_comp', @cont_eq_transport', @propagate_self',
    @propagate_trans', @propagate_comp'⟩

/-- `B ⇒ A`, OUTRIGHT (the hypothesis is not used): vacuous for the audit. -/
theorem B_to_A : B → A := fun _ => A_outright

#rt_check_soft RoundTrip.V6_39.B_to_A [Polyfold.SubspaceFamily.cont_eq, Polyfold.SubspaceFamily.cont_self,
  Polyfold.SubspaceFamily.cont_trans, Polyfold.SubspaceFamily.cont_comp,
  Polyfold.SubspaceFamily.cont_eq_transport, Polyfold.propagate_self, Polyfold.propagate_trans,
  Polyfold.propagate_comp]
#rt_check_soft RoundTrip.V6_39.A_to_B5 [Polyfold.SubspaceFamily.cont_eq,
  Polyfold.SubspaceFamily.cont_self, Polyfold.SubspaceFamily.cont_trans,
  Polyfold.SubspaceFamily.cont_comp, Polyfold.SubspaceFamily.cont_eq_transport,
  Polyfold.propagate_self, Polyfold.propagate_trans, Polyfold.propagate_comp]
#rt_overlap RoundTrip.V6_39.B_to_A [Polyfold.SubspaceFamily.cont_eq,
  Polyfold.SubspaceFamily.cont_self, Polyfold.SubspaceFamily.cont_trans,
  Polyfold.SubspaceFamily.cont_comp, Polyfold.SubspaceFamily.cont_eq_transport,
  Polyfold.propagate_self, Polyfold.propagate_trans, Polyfold.propagate_comp]

end RoundTrip.V6_39
