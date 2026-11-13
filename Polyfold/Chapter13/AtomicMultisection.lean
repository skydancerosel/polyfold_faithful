import Polyfold.Chapter13.MultisectionSymmetric
import Polyfold.Chapter13.MultisectionConvolution
import Polyfold.Chapter7.PartitionsOfUnity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.5, **Definition 13.5.1** (p. 629; 2017: Definition 13.23) and the multisection built in the
proof of **Theorem 13.5.5** (pp. 633–634).

# Atomic sc⁺-multisections

## The text, paraphrased

(Definition 13.5.1) An sc⁺-multisection functor `Λ : W → ℚ⁺` is atomic if (1) there are a point
`x` and `G_x`-invariant open neighbourhoods `U(x)`, `V(x)` with `cl V(x) ⊆ U(x)` and
`t : s⁻¹(cl U(x)) → X` proper; (2) a symmetric sc⁺-section structure `(sᵢ)_{i ∈ I_x}` on `U(x)`
vanishing outside `V(x)`; (3) for `w' = μ(φ, w)` with `t(φ) ∈ U(x)`,
`Λ(w) = |I_x|⁻¹·#{i | sᵢ(P(w')) = w'}`, and if no morphism joins `P(w)` to `U(x)`, then
`Λ(w) = 1` for `w = 0` and `0` otherwise.

(Proof of Theorem 13.5.5) Given such data, these two formulas define `Λ`; near a point joined to
`U(x)` the structure is pulled back by the local sc-diffeomorphism of a morphism, near any other
point the single zero section represents `Λ`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `AtomicData A`: the data of (1)–(2) (a natural representation `R` with `U(x) = R.U`, the
  properness property, `V(x)`, the index type with its `G_x`-action, the equivariant sections
  vanishing on `U(x) ∖ V(x)`); `AtomicData.count`, `AtomicData.Reach`.
* `AtomicData.IsRelated Λ`: condition (3); **`IsAtomic`** (Definition 13.5.1).
* `AtomicData.count_μ_eq`: the formula of (3) does not depend on the morphism `φ` (equivariance).
* `AtomicData.mult`: the functor defined by (3); `isRelated_mult`, `IsRelated.eq_mult` (it is the
  only functor related to the data), `isWFunctor_mult`, **`isScPlusMultisection_mult`** (it is an
  sc⁺-multisection when `I_x ≠ ∅`), `isAtomic_mult`.
* `IsRelated.symmetricStructure`: the data of an atomic `Λ` is a symmetric sc⁺-section structure
  for `Λ` in the sense of Definition 13.2.5 (`SymmetricStructure`), so (2) holds as printed.
* `domSupp_mult_subset`: `dom-supp(Λ) ⊆ π⁻¹(π(cl V(x)))`.
* Witness: `exists_atomicNbhd`, `AtomicData.zero`, `isAtomic_zeroMultisection` (the trivial
  multisection is atomic, at every point).

## Reading

* "`G_x`-invariant open `U(x)`" carrying a symmetric structure is read, as in Definition 13.2.5
  (`SymmetricStructure`), as the domain of a natural representation; `V(x)` is `G_x`-invariant
  for the natural action and contains `x`.
* The sections `sᵢ` are sc⁺-sections on `U(x)` (`IsScPlusSectionOn`); "vanishing outside `V(x)`"
  is `sᵢ(y) = 0_y` for `y ∈ U(x) ∖ V(x)`.
* For `w' = μ(φ, w)` the count is taken at `P(w') = t(φ)`, as in (3).
* An sc⁺-multisection needs `I_x ≠ ∅` (weights sum to `1`); `isScPlusMultisection_mult` assumes
  it, and it follows from (3) for an sc⁺-multisection `Λ`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle

variable {A : SEP.{u}}

/-! ### Definition 13.5.1 -/

/-- **The data of 2021 Definition 13.5.1 (1)–(2), p. 629**: a point `x`, the domain `U(x)` of a
natural representation of `G_x` with `t : s⁻¹(cl U(x)) → X` proper, an open `G_x`-invariant
`V(x) ∋ x` with `cl V(x) ⊆ U(x)`, and a symmetric family of sc⁺-sections `(sᵢ)_{i ∈ I}` on `U(x)`
(`s_{g(i)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))`) vanishing on `U(x) ∖ V(x)`. -/
structure AtomicData (A : SEP.{u}) where
  /-- The point `x`. -/
  x : A.Obj
  /-- The natural representation on `U(x)`. -/
  R : A.X.NaturalRep x
  /-- `t : s⁻¹(cl U(x)) → X` is proper. -/
  hasPropernessProperty : A.X.HasPropernessProperty R.U
  /-- The neighbourhood `V(x)`. -/
  V : Set A.Obj
  isOpen_V : IsOpen V
  mem_V : x ∈ V
  mapsTo_V : ∀ g, MapsTo (R.Φ g) V V
  closure_V_subset : closure V ⊆ R.U
  /-- The index set `I_x`. -/
  I : Type u
  [fintype : Fintype I]
  [mulAction : MulAction (A.X.Isotropy x) I]
  /-- The sections `sᵢ`. -/
  s : I → A.Obj → A.W
  isScPlusSectionOn : ∀ i, IsScPlusSectionOn A (s i) R.U
  /-- `s_{g(i)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))`. -/
  equivariant : ∀ (g : A.X.Isotropy x) (i : I) (y : A.Obj) (hy : y ∈ R.U),
    s (g • i) (R.Φ g y) =
      A.E.μ ⟨(R.Γ g y, s i y), ((isScPlusSectionOn i).1 y hy).trans (R.src_Γ g y hy).symm⟩
  /-- The sections vanish on `U(x) ∖ V(x)`. -/
  vanish : ∀ i, ∀ y ∈ R.U, y ∉ V → s i y = fiberZero A.P y

attribute [instance] AtomicData.fintype AtomicData.mulAction

namespace AtomicData

variable (D : AtomicData A)

/-- `|I_x|⁻¹·#{i ∈ I_x | sᵢ(P(w)) = w}`. -/
def count (w : A.W) : ℚ≥0 :=
  (Fintype.card D.I : ℚ≥0)⁻¹ * ((Finset.univ.filter fun i => D.s i (A.P w) = w).card : ℚ≥0)

/-- Some morphism joins `y` to a point of `U(x)`. -/
def Reach (y : A.Obj) : Prop := ∃ φ : A.Mor, A.X.src φ = y ∧ A.X.tgt φ ∈ D.R.U

/-- **Condition (3) of Definition 13.5.1**: `Λ(w) = |I_x|⁻¹·#{i | sᵢ(P(w')) = w'}` for
`w' = μ(φ, w)`, `t(φ) ∈ U(x)`; and `Λ(w) = 1` for `w = 0`, `0` otherwise, if no morphism joins
`P(w)` to `U(x)`. -/
def IsRelated (Λ : A.W → ℚ≥0) : Prop :=
  (∀ (w : A.W) (φ : A.Mor) (h : A.P w = A.X.src φ), A.X.tgt φ ∈ D.R.U →
    Λ w = D.count (A.E.μ ⟨(φ, w), h⟩)) ∧
  ∀ w, ¬ D.Reach (A.P w) → Λ w = zeroMultisection A w

/-- **The functor defined by condition (3)** (the `Λ` of the proof of Theorem 13.5.5). -/
def mult (w : A.W) : ℚ≥0 :=
  if h : D.Reach (A.P w) then D.count (A.E.μ ⟨(h.choose, w), h.choose_spec.1.symm⟩)
  else zeroMultisection A w

end AtomicData

/-- **2021 Definition 13.5.1, p. 629 (2017: Definition 13.23)**: an sc⁺-multisection functor
`Λ : W → ℚ⁺` is **atomic** if it is related (condition (3)) to the data (1)–(2) of an
`AtomicData`. -/
def IsAtomic (A : SEP.{u}) (Λ : A.W → ℚ≥0) : Prop :=
  IsScPlusMultisection A Λ ∧ ∃ D : AtomicData A, D.IsRelated Λ

namespace AtomicData

variable (D : AtomicData A)

/-! ### The count is independent of the morphism -/

theorem card_filter_μ_Γ (g : A.X.Isotropy D.x) {y : A.Obj} (hy : y ∈ D.R.U) (w : A.W)
    (hw : A.P w = A.X.src (D.R.Γ g y)) :
    (Finset.univ.filter fun i => D.s i (D.R.Φ g y) = A.E.μ ⟨(D.R.Γ g y, w), hw⟩).card =
      (Finset.univ.filter fun j => D.s j y = w).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  refine Fintype.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g) fun j => ?_).symm
  rw [MulAction.toPerm_apply, D.equivariant g j y hy]
  constructor
  · intro e
    exact A.E.μ_congr (Prod.ext rfl e)
  · intro e
    exact EpStrongBundle.μ_injective_snd A.E _ hw e

/-- **Equivariance of the count**: `#{i | sᵢ(g ∗ y) = μ(Γ(g, y), w)} = #{i | sᵢ(y) = w}`. -/
theorem count_μ_Γ (g : A.X.Isotropy D.x) {y : A.Obj} (hy : y ∈ D.R.U) (w : A.W)
    (hw : A.P w = A.X.src (D.R.Γ g y)) :
    D.count (A.E.μ ⟨(D.R.Γ g y, w), hw⟩) = D.count w := by
  have hwy : A.P w = y := hw.trans (D.R.src_Γ g y hy)
  have hP : A.P (A.E.μ ⟨(D.R.Γ g y, w), hw⟩) = D.R.Φ g y :=
    (A.E.P_μ _).trans (D.R.tgt_Γ g y hy)
  unfold count
  rw [hP, hwy, D.card_filter_μ_Γ g hy w hw]

/-- **The formula of (3) does not depend on `φ`**: for two morphisms `φ, φ'` from `P(w)` into
`U(x)`, `φ' ∘ φ⁻¹` is `Γ(g, t φ)` for some `g ∈ G_x`. -/
theorem count_μ_eq {w : A.W} {φ φ' : A.Mor} (h : A.P w = A.X.src φ) (h' : A.P w = A.X.src φ')
    (ht : A.X.tgt φ ∈ D.R.U) (ht' : A.X.tgt φ' ∈ D.R.U) :
    D.count (A.E.μ ⟨(φ, w), h⟩) = D.count (A.E.μ ⟨(φ', w), h'⟩) := by
  set ψ := A.X.comp φ' (A.X.inv φ) with hψ
  have hc : A.X.src φ' = A.X.tgt (A.X.inv φ) := by rw [A.X.tgt_inv]; exact h'.symm.trans h
  have hψs : A.X.src ψ = A.X.tgt φ := by rw [hψ, A.X.src_comp _ _ hc, A.X.src_inv]
  have hψt : A.X.tgt ψ = A.X.tgt φ' := A.X.tgt_comp _ _ hc
  obtain ⟨g, hg⟩ := D.R.exists_Γ_eq (φ := ψ) ⟨hψs ▸ ht, hψt ▸ ht'⟩
  rw [hψs] at hg
  have hcomp : A.X.comp ψ φ = φ' := by
    have := GroupoidStr.comp_inv_cancel_right (G := A.X.toGroupoidStr) (φ := A.X.inv φ)
      (ψ := φ') hc
    rwa [GroupoidStr.inv_inv] at this
  have hm : A.P (A.E.μ ⟨(φ, w), h⟩) = A.X.src (D.R.Γ g (A.X.tgt φ)) := by
    rw [A.E.P_μ, D.R.src_Γ g _ ht]
  have e0 : A.E.μ ⟨(φ', w), h'⟩ =
      A.E.μ ⟨(A.X.comp ψ φ, w), h.trans (A.X.src_comp ψ φ hψs).symm⟩ :=
    A.E.μ_congr (Prod.ext hcomp.symm rfl)
  have e2 : A.E.μ ⟨(ψ, A.E.μ ⟨(φ, w), h⟩), (A.E.P_μ _).trans hψs.symm⟩ =
      A.E.μ ⟨(D.R.Γ g (A.X.tgt φ), A.E.μ ⟨(φ, w), h⟩), hm⟩ :=
    A.E.μ_congr (Prod.ext hg.symm rfl)
  have e1 : A.E.μ ⟨(φ', w), h'⟩ =
      A.E.μ ⟨(D.R.Γ g (A.X.tgt φ), A.E.μ ⟨(φ, w), h⟩), hm⟩ :=
    e0.trans ((A.E.μ_comp ψ φ w h hψs).trans e2)
  rw [e1, D.count_μ_Γ g ht]

/-! ### The functor `mult` -/

theorem reach_iff_mem_saturation (y : A.Obj) : D.Reach y ↔ y ∈ A.X.saturation D.R.U := by
  constructor
  · rintro ⟨φ, hs, ht⟩
    exact ⟨A.X.tgt φ, ht, by rw [← A.X.π_src_eq_π_tgt, hs]⟩
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hzy.symm
    exact ⟨φ, hs, ht ▸ hz⟩

theorem mult_eq {w : A.W} {φ : A.Mor} (h : A.P w = A.X.src φ) (ht : A.X.tgt φ ∈ D.R.U) :
    D.mult w = D.count (A.E.μ ⟨(φ, w), h⟩) := by
  have hr : D.Reach (A.P w) := ⟨φ, h.symm, ht⟩
  unfold mult
  rw [dif_pos hr]
  exact D.count_μ_eq _ h hr.choose_spec.2 ht

theorem mult_of_not_reach {w : A.W} (h : ¬ D.Reach (A.P w)) : D.mult w = zeroMultisection A w := by
  unfold mult; rw [dif_neg h]

/-- `μ(1_{P(w)}, w) = w`. -/
theorem μ_unit_pair (w : A.W) (h : A.P w = A.X.src (A.X.unit (A.P w))) :
    A.E.μ ⟨(A.X.unit (A.P w), w), h⟩ = w :=
  (A.E.μ_congr rfl).trans (A.E.μ_unit w)

/-- Over `U(x)`, `Λ(w) = |I_x|⁻¹·#{i | sᵢ(P(w)) = w}`. -/
theorem mult_of_mem {w : A.W} (hw : A.P w ∈ D.R.U) : D.mult w = D.count w := by
  have h : A.P w = A.X.src (A.X.unit (A.P w)) := (A.X.src_unit _).symm
  rw [D.mult_eq h (by rw [A.X.tgt_unit]; exact hw), μ_unit_pair w h]

/-- `mult` satisfies condition (3). -/
theorem isRelated_mult : D.IsRelated D.mult :=
  ⟨fun _ _ h ht => D.mult_eq h ht, fun _ h => D.mult_of_not_reach h⟩

/-- **Uniqueness**: a function related to the data by (3) is `mult`. -/
theorem IsRelated.eq_mult {Λ : A.W → ℚ≥0} (h : D.IsRelated Λ) : Λ = D.mult := by
  funext w
  by_cases hr : D.Reach (A.P w)
  · obtain ⟨φ, hs, ht⟩ := hr
    rw [h.1 w φ hs.symm ht, D.mult_eq hs.symm ht]
  · rw [h.2 w hr, D.mult_of_not_reach hr]

/-- **`mult` is a functor** on `(W, 𝐖)`. -/
theorem isWFunctor_mult : IsWFunctor A D.mult := by
  rintro ⟨⟨ψ, w⟩, hq⟩
  have hq' : A.P w = A.X.src ψ := hq
  have hPμ : A.P (A.E.μ ⟨(ψ, w), hq⟩) = A.X.tgt ψ := A.E.P_μ _
  change D.mult (A.E.μ ⟨(ψ, w), hq⟩) = D.mult w
  by_cases hr : D.Reach (A.P w)
  · obtain ⟨φ, hs, ht⟩ := hr
    have hc : A.X.src φ = A.X.tgt (A.X.inv ψ) := by rw [A.X.tgt_inv, hs, hq']
    set φ' := A.X.comp φ (A.X.inv ψ) with hφ'
    have hs' : A.P (A.E.μ ⟨(ψ, w), hq⟩) = A.X.src φ' := by
      rw [hPμ, hφ', A.X.src_comp _ _ hc, A.X.src_inv]
    have ht' : A.X.tgt φ' ∈ D.R.U := by rw [hφ', A.X.tgt_comp _ _ hc]; exact ht
    rw [D.mult_eq hs' ht', D.mult_eq hs.symm ht]
    have hc' : A.X.src φ' = A.X.tgt ψ := by rw [hφ', A.X.src_comp _ _ hc, A.X.src_inv]
    have hcomp : A.X.comp φ' ψ = φ := by
      have := GroupoidStr.comp_inv_cancel_right (G := A.X.toGroupoidStr) (φ := A.X.inv ψ)
        (ψ := φ) hc
      rwa [GroupoidStr.inv_inv] at this
    have e0 : A.E.μ ⟨(φ', A.E.μ ⟨(ψ, w), hq⟩), hs'⟩ =
        A.E.μ ⟨(A.X.comp φ' ψ, w), hq'.trans (A.X.src_comp φ' ψ hc').symm⟩ :=
      (A.E.μ_comp φ' ψ w hq' hc').symm
    have e1 : A.E.μ ⟨(A.X.comp φ' ψ, w), hq'.trans (A.X.src_comp φ' ψ hc').symm⟩ =
        A.E.μ ⟨(φ, w), hs.symm⟩ := A.E.μ_congr (Prod.ext hcomp rfl)
    rw [e0, e1]
  · have hr' : ¬ D.Reach (A.P (A.E.μ ⟨(ψ, w), hq⟩)) := by
      rintro ⟨φ, hs, ht⟩
      have hc : A.X.src φ = A.X.tgt ψ := hs.trans hPμ
      exact hr ⟨A.X.comp φ ψ, by rw [A.X.src_comp _ _ hc, hq'],
        by rw [A.X.tgt_comp _ _ hc]; exact ht⟩
    rw [D.mult_of_not_reach hr', D.mult_of_not_reach hr]
    exact isWFunctor_zeroMultisection A ⟨(ψ, w), hq⟩

/-- `cl V(x)` is proper (a closed subset of the proper `cl U(x)`). -/
theorem isProperSubset_closure_V : A.X.IsProperSubset (closure D.V) :=
  D.hasPropernessProperty.2.of_subset (D.closure_V_subset.trans subset_closure) isClosed_closure

theorem isClosed_saturation_closure_V : IsClosed (A.X.saturation (closure D.V)) :=
  A.X.isClosed_saturation_of_isProperSubset D.isProperSubset_closure_V

/-- The count at a point where all `sᵢ` vanish is the trivial multisection. -/
theorem count_eq_zeroMultisection {w : A.W} (h0 : ∀ i, D.s i (A.P w) = fiberZero A.P (A.P w))
    [Nonempty D.I] : D.count w = zeroMultisection A w := by
  have hcard : (Fintype.card D.I : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  unfold count zeroMultisection
  simp only [h0]
  by_cases hw : w = fiberZero A.P (A.P w)
  · rw [if_pos hw, Finset.filter_true_of_mem fun _ _ => hw.symm, Finset.card_univ,
      inv_mul_cancel₀ hcard]
  · rw [if_neg hw, Finset.filter_false_of_mem fun _ _ h => hw h.symm, Finset.card_empty,
      Nat.cast_zero, mul_zero]

/-- **Off the saturation of `cl V(x)`, `Λ` is trivial.** -/
theorem mult_eq_zeroMultisection [Nonempty D.I] {w : A.W}
    (hw : A.P w ∉ A.X.saturation (closure D.V)) : D.mult w = zeroMultisection A w := by
  by_cases hr : D.Reach (A.P w)
  · obtain ⟨φ, hs, ht⟩ := hr
    have htV : A.X.tgt φ ∉ D.V := fun hV =>
      hw ⟨A.X.tgt φ, subset_closure hV, by rw [← A.X.π_src_eq_π_tgt, hs]⟩
    rw [D.mult_eq hs.symm ht]
    have hPm : A.P (A.E.μ ⟨(φ, w), hs.symm⟩) = A.X.tgt φ := A.E.P_μ _
    rw [D.count_eq_zeroMultisection (fun i => by rw [hPm]; exact D.vanish i _ ht htV)]
    exact isWFunctor_zeroMultisection A ⟨(φ, w), hs.symm⟩
  · exact D.mult_of_not_reach hr

/-- **The domain support**: `dom-supp(Λ) ⊆ π⁻¹(π(cl V(x)))`. -/
theorem domSupp_mult_subset [Nonempty D.I] :
    domSupp D.mult ⊆ A.X.saturation (closure D.V) := by
  refine closure_minimal (fun y hy => ?_) D.isClosed_saturation_closure_V
  obtain ⟨w, hwy, hw0, hpos⟩ := hy
  by_contra hy'
  rw [← hwy] at hy'
  rw [D.mult_eq_zeroMultisection hy', zeroMultisection, if_neg (by rw [hwy]; exact hw0)] at hpos
  exact lt_irrefl _ hpos

theorem saturation_closure_V_subset : A.X.saturation (closure D.V) ⊆ A.X.saturation D.R.U :=
  preimage_mono (image_mono D.closure_V_subset)

/-! ### `mult` is an sc⁺-multisection -/

/-- **Near a point joined to `U(x)`**: the local section structure pulled back by a local
sc-diffeomorphism of a morphism (proof of Theorem 13.5.5, p. 634): on an open `O ∋ x₀`, with
`τ : O → 𝐗` sc-smooth, `t(τ(z)) = z`, `s(τ(z)) ∈ U(x)`, the sections
`s'ᵢ(z) = μ(τ(z), sᵢ(s(τ(z))))` with weights `|I|⁻¹` represent `Λ`. -/
theorem exists_isLocalRepOn_transport [Nonempty D.I] {x₀ : A.Obj} (hx₀ : D.Reach x₀) :
    ∃ (O : Set A.Obj) (τ : A.Obj → A.Mor), IsOpen O ∧ x₀ ∈ O ∧
      A.X.PObj.IsScSmoothOn A.X.PMor τ O ∧
      (∀ z ∈ O, A.X.tgt (τ z) = z ∧ A.X.src (τ z) ∈ D.R.U) ∧
      IsLocalRepOn A D.mult O (fun n => transportSection τ
        (fun z => D.s ((Fintype.equivFin D.I).symm n) (A.X.src (τ z))))
        (fun _ => (Fintype.card D.I : ℚ≥0)⁻¹) := by
  obtain ⟨φ₀, hs₀, ht₀⟩ := hx₀
  obtain ⟨T, V₂, τ, hT, hτ⟩ := A.X.isLocalScDiffeo_tgt (A.X.inv φ₀)
  have hcont : ContinuousOn (A.X.src ∘ τ) V₂ :=
    A.X.continuous_src.comp_continuousOn hτ.isScSmoothOn_inv.continuousOn
  set O : Set A.Obj := V₂ ∩ (A.X.src ∘ τ) ⁻¹' D.R.U with hOdef
  have hO : IsOpen O := hcont.isOpen_inter_preimage hτ.isScSmoothOn_inv.isOpen D.R.isOpen_U
  have hτx₀ : τ x₀ = A.X.inv φ₀ := by
    have := hτ.left_inv (A.X.inv φ₀) hT
    rwa [A.X.tgt_inv, hs₀] at this
  have hx₀O : x₀ ∈ O := by
    refine ⟨?_, ?_⟩
    · have := hτ.mapsTo hT
      rwa [A.X.tgt_inv, hs₀] at this
    · change A.X.src (τ x₀) ∈ D.R.U
      rw [hτx₀, A.X.src_inv]; exact ht₀
  have hτO : A.X.PObj.IsScSmoothOn A.X.PMor τ O := hτ.isScSmoothOn_inv.mono hO inter_subset_left
  have hsτ : A.X.PObj.IsScSmoothOn A.X.PObj (A.X.src ∘ τ) O :=
    MPolyfold.IsScSmoothOn.comp A.X.isScSmoothMap_src hτO (mapsTo_univ _ _)
  have htgt : ∀ z ∈ O, A.X.tgt (τ z) = z := fun z hz => hτ.right_inv z hz.1
  -- the pulled-back sections `s'ᵢ(z) = μ(τ(z), sᵢ(s(τ z)))`
  set S : D.I → A.Obj → A.W := fun i =>
    transportSection τ (fun z => D.s i (A.X.src (τ z))) with hSdef
  have hsrc : ∀ i, ∀ z ∈ O, A.P (D.s i (A.X.src (τ z))) = A.X.src (τ z) := fun i z hz =>
    (D.isScPlusSectionOn i).1 _ hz.2
  have hS : ∀ i, IsScPlusSectionOn A (S i) O := fun i => by
    obtain ⟨-, G, hG, hGs⟩ := D.isScPlusSectionOn i
    exact isScPlusSectionOn_transportSection hτO (G := G ∘ (A.X.src ∘ τ))
      (fun z hz => hG _ hz.2) (MPolyfold.IsScSmoothOn.comp hGs hsτ fun z hz => hz.2)
      (hsrc i) htgt
  have hcard : (Fintype.card D.I : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨O, τ, hO, hx₀O, hτO, fun z hz => ⟨htgt z hz, hz.2⟩,
    isLocalRepOn_of_fintype (K := D.I) S
    (fun _ => (Fintype.card D.I : ℚ≥0)⁻¹) (fun _ => inv_pos.2 (pos_iff_ne_zero.2 hcard)) hS ?_
    fun w hw => ?_⟩
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard]
  · set z := A.P w with hz
    have hzO : z ∈ O := hw
    have h1 : A.P w = A.X.src (A.X.inv (τ z)) := by rw [A.X.src_inv, htgt z hzO]
    have ht1 : A.X.tgt (A.X.inv (τ z)) ∈ D.R.U := by rw [A.X.tgt_inv]; exact hzO.2
    set m := A.E.μ ⟨(A.X.inv (τ z), w), h1⟩ with hm
    have hPm : A.P m = A.X.src (τ z) := by rw [hm, A.E.P_μ, A.X.tgt_inv]
    have hiff : ∀ i, w = S i z ↔ D.s i (A.P m) = m := fun i => by
      rw [hPm]
      change w = transportSection τ (fun z => D.s i (A.X.src (τ z))) z ↔ _
      rw [transportSection_of_mem (hsrc i z hzO)]
      constructor
      · intro e
        have := A.E.μ_inv_μ ⟨(τ z, D.s i (A.X.src (τ z))), hsrc i z hzO⟩
          (by rw [A.E.P_μ]; exact (A.X.src_inv _).symm)
        refine this.symm.trans (A.E.μ_congr (Prod.ext rfl ?_))
        exact e.symm
      · intro e
        have := A.E.μ_μ_inv (τ z) w h1 (by rw [← hm, hPm])
        refine this.symm.trans (A.E.μ_congr (Prod.ext rfl ?_))
        change m = D.s i (A.X.src (τ z))
        exact e.symm
    rw [D.mult_eq h1 ht1, ← hm, count, Finset.natCast_card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_congr (hiff i) rfl rfl]
    split_ifs <;> simp

theorem hasLocalSectionStructure_of_reach [Nonempty D.I] {x₀ : A.Obj} (hx₀ : D.Reach x₀) :
    HasLocalSectionStructure A D.mult x₀ := by
  obtain ⟨O, τ, hO, hx₀O, -, -, h⟩ := D.exists_isLocalRepOn_transport hx₀
  exact hasLocalSectionStructure_of_isLocalRepOn hO hx₀O h

/-- **Away from `cl V(x)`**: the single zero section represents `Λ` (proof of Theorem 13.5.5,
p. 634). -/
theorem hasLocalSectionStructure_of_not_mem [Nonempty D.I] {x₀ : A.Obj}
    (hx₀ : x₀ ∉ A.X.saturation (closure D.V)) : HasLocalSectionStructure A D.mult x₀ := by
  have hO : IsOpen (A.X.saturation (closure D.V))ᶜ := D.isClosed_saturation_closure_V.isOpen_compl
  refine hasLocalSectionStructure_of_isLocalRepOn hO hx₀ (k := 1) (s := fun _ => fiberZero A.P)
    (σ := fun _ => 1) ⟨fun _ => one_pos, fun _ => isScPlusSectionOn_fiberZero hO, by simp,
      fun w hw => ?_⟩
  rw [D.mult_eq_zeroMultisection hw]
  simp [zeroMultisection]

/-- **The proof of Theorem 13.5.5, p. 634**: the functor defined by the data of an atomic
multisection is an **sc⁺-multisection** (when `I_x ≠ ∅`). -/
theorem isScPlusMultisection_mult [Nonempty D.I] : IsScPlusMultisection A D.mult := by
  refine ⟨D.isWFunctor_mult, fun x₀ => ?_⟩
  by_cases hx₀ : D.Reach x₀
  · exact D.hasLocalSectionStructure_of_reach hx₀
  · refine D.hasLocalSectionStructure_of_not_mem fun h => hx₀ ?_
    exact (D.reach_iff_mem_saturation x₀).2 (D.saturation_closure_V_subset h)

/-- `mult` is atomic. -/
theorem isAtomic_mult [Nonempty D.I] : IsAtomic A D.mult :=
  ⟨D.isScPlusMultisection_mult, D, D.isRelated_mult⟩

/-- **Condition (2) as printed**: the data of an atomic `Λ` is a symmetric sc⁺-section structure
for `Λ` on `U(x)` (Definition 13.2.5). -/
def IsRelated.symmetricStructure {Λ : A.W → ℚ≥0} (h : D.IsRelated Λ) :
    SymmetricStructure A Λ D.x where
  R := D.R
  hasPropernessProperty := D.hasPropernessProperty
  I := D.I
  s := D.s
  isScPlusSectionOn := D.isScPlusSectionOn
  equivariant := D.equivariant
  rep w hw := by
    have h1 : A.P w = A.X.src (A.X.unit (A.P w)) := (A.X.src_unit _).symm
    rw [h.1 w _ h1 (by rw [A.X.tgt_unit]; exact hw), μ_unit_pair w h1]
    rfl

/-- The index set of an atomic sc⁺-multisection is not empty. -/
theorem IsRelated.nonempty {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (h : D.IsRelated Λ) :
    Nonempty D.I := by
  by_contra hI
  rw [not_nonempty_iff] at hI
  obtain ⟨w, hw, hpos⟩ := hΛ.suppAt_nonempty D.x
  have hm : A.P w ∈ D.R.U := by rw [hw]; exact D.R.mem_U
  rw [h.eq_mult, D.mult_of_mem hm, count, Fintype.card_eq_zero, Nat.cast_zero, inv_zero,
    zero_mul] at hpos
  exact lt_irrefl _ hpos

end AtomicData

/-! ### Witnesses -/

/-- A natural representation on `U(x) ⊆ W` with the properness property and an invariant open
`V(x) ∋ x` with `cl V(x) ⊆ U(x)` (Theorem 7.1.13 and the proof of Theorem 7.5.7). -/
theorem exists_atomicNbhd (x : A.Obj) {W : Set A.Obj} (hW : IsOpen W) (hx : x ∈ W) :
    ∃ (R : A.X.NaturalRep x) (V : Set A.Obj), A.X.HasPropernessProperty R.U ∧ R.U ⊆ W ∧
      IsOpen V ∧ x ∈ V ∧ (∀ g, MapsTo (R.Φ g) V V) ∧ closure V ⊆ R.U := by
  obtain ⟨V₀, hxV₀, hV₀⟩ := A.X.exists_hasPropernessProperty x
  obtain ⟨R, V, hVo, hxV, hVinv, hVcl, hRU, -⟩ :=
    EpGroupoid.exists_invariant_nhds_of_isOpen A.X x (hW.inter hV₀.1) ⟨hx, hxV₀⟩
  exact ⟨R, V, hV₀.mono R.isOpen_U (hRU.trans inter_subset_right), hRU.trans inter_subset_left,
    hVo, hxV, hVinv, hVcl⟩

/-- The atomic data of the zero section at `x` (one index). -/
def AtomicData.zero (x : A.Obj) : AtomicData A :=
  let h := exists_atomicNbhd (A := A) x isOpen_univ (mem_univ x)
  { x := x
    R := h.choose
    hasPropernessProperty := h.choose_spec.choose_spec.1
    V := h.choose_spec.choose
    isOpen_V := h.choose_spec.choose_spec.2.2.1
    mem_V := h.choose_spec.choose_spec.2.2.2.1
    mapsTo_V := h.choose_spec.choose_spec.2.2.2.2.1
    closure_V_subset := h.choose_spec.choose_spec.2.2.2.2.2
    I := PUnit
    s := fun _ => fiberZero A.P
    isScPlusSectionOn := fun _ => isScPlusSectionOn_fiberZero h.choose.isOpen_U
    equivariant := fun g _ y hy => by
      have e := μ_fiberZero A (h.choose.Γ g y) (isSection_fiberZero _)
      rw [h.choose.tgt_Γ g y hy] at e
      refine e.symm.trans (A.E.μ_congr (Prod.ext rfl ?_))
      change fiberZero A.P (A.X.src (h.choose.Γ g y)) = fiberZero A.P y
      rw [h.choose.src_Γ g y hy]
    vanish := fun _ _ _ _ => rfl }

instance (x : A.Obj) : Nonempty (AtomicData.zero (A := A) x).I := ⟨PUnit.unit⟩

/-- The multisection of the zero-section data is the trivial multisection. -/
theorem AtomicData.zero_mult (x : A.Obj) :
    (AtomicData.zero (A := A) x).mult = zeroMultisection A := by
  set D := AtomicData.zero (A := A) x
  funext w
  by_cases hr : D.Reach (A.P w)
  · obtain ⟨φ, hs, ht⟩ := hr
    rw [D.mult_eq hs.symm ht, D.count_eq_zeroMultisection fun _ => rfl]
    exact isWFunctor_zeroMultisection A ⟨(φ, w), hs.symm⟩
  · exact D.mult_of_not_reach hr

/-- **Definition 13.5.1 is satisfiable**: the trivial multisection is atomic (at every point). -/
theorem isAtomic_zeroMultisection (x : A.Obj) : IsAtomic A (zeroMultisection A) :=
  AtomicData.zero_mult (A := A) x ▸ (AtomicData.zero (A := A) x).isAtomic_mult

end SBLocalization

end Polyfold
