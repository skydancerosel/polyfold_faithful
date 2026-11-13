import Polyfold.Chapter13.AtomicConstruction

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.5, **Theorem 13.5.3** (p. 630; 2017: Theorem 13.6) and the last sentence of **Theorem
13.5.5** (p. 633).

# Atomic sc⁺-multisections are structurable: the local part, and a hypothesis form

## The text, paraphrased

(Theorem 13.5.3) An atomic sc⁺-multisection functor is structurable (Definition 13.3.6).
*Proof*: a good system `U(x)`, index sets `I_x`, symmetric structures `s_x` and correspondences
`τ_{x,x'}` are built by cases: for `x ∈ U(x₀)` the restriction of the atomic structure
(`I_x = I_{x₀}`, `G_x` acting through `γ_x : G_x → G_{x₀}`); for `x` near which `Λ` is trivial the
single zero section (`I_x = {∗}`); otherwise the structure pulled back along a morphism
`φ_x : x → t(φ_x) ∈ cl V(x₀)` by `σ_x = t ∘ (s|U(φ_x))⁻¹`.  The correspondences are the identity
spans over `U(x₀)`, transported by the `σ_x`, and `[{∗} ← I ⇒ I]` resp. `[I ⇐ I → {∗}]` for
points not over `|U(x₀)|`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `AtomicData.IsLocallyTransported Λ y`: the local alternative of the proof at a point `y`: on an
  open `O ∋ y`, `Λ` is represented by the atomic sections transported by a sc-smooth
  `τ : O → 𝐗` (`t(τ(z)) = z`, `s(τ(z)) ∈ U(x₀)`, `s'ᵢ(z) = μ(τ(z), sᵢ(s(τ(z))))`, weights
  `|I|⁻¹`), or `Λ` is trivial over `O`.
* **`theorem_13_5_3_local`**: every point has this alternative (the families `S = (s_x)` of the
  proof, with the index sets `I` resp. `{∗}`).
* **`theorem_13_5_3_hyp`**: Theorem 13.5.3 for any notion `Structurable` for which the local
  alternatives give a structure (`hcrit`, the correspondences of the proof); a witness
  `theorem_13_5_3_hyp_witness`.
* **`theorem_13_5_5_structurable_hyp`**: the last sentence of Theorem 13.5.5 from Theorem 13.5.3,
  as in the text.

## Elsewhere

`hcrit`, the step "the transported structures fit together through correspondences", is no
longer needed: `AtomicStructurable` builds the correspondences as in the text and proves
`theorem_13_5_3 : IsStructurable A Λ ↔ Nonempty A.X.GoodSystem` for atomic `Λ`, with
`theorem_13_5_3_of_paracompact` and `theorem_13_5_5_structurable` (gap G.149, closed).  The
declarations above are kept as supporting declarations.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle

variable {A : SEP.{u}}

namespace AtomicData

variable (D : AtomicData A)

/-- **The local alternative of the proof of Theorem 13.5.3** at `y`: on an open `O ∋ y`, either
`Λ` is represented by the atomic sections transported along a sc-smooth `τ : O → 𝐗` with
`t(τ(z)) = z` and `s(τ(z)) ∈ U(x₀)` (index set `I`, weights `|I|⁻¹`), or `Λ` is trivial over `O`
(index set `{∗}`, the zero section). -/
def IsLocallyTransported (Λ : A.W → ℚ≥0) (y : A.Obj) : Prop :=
  (∃ (O : Set A.Obj) (τ : A.Obj → A.Mor), IsOpen O ∧ y ∈ O ∧
      A.X.PObj.IsScSmoothOn A.X.PMor τ O ∧
      (∀ z ∈ O, A.X.tgt (τ z) = z ∧ A.X.src (τ z) ∈ D.R.U) ∧
      IsLocalRepOn A Λ O (fun n => transportSection τ
        (fun z => D.s ((Fintype.equivFin D.I).symm n) (A.X.src (τ z))))
        (fun _ => (Fintype.card D.I : ℚ≥0)⁻¹)) ∨
    ∃ O : Set A.Obj, IsOpen O ∧ y ∈ O ∧ ∀ w, A.P w ∈ O → Λ w = zeroMultisection A w

end AtomicData

/-- **2021 Theorem 13.5.3, p. 630 (2017: Theorem 13.6), the local part of the proof**: for an
atomic sc⁺-multisection `Λ` with data `D`, every point `y` has the local alternative of the proof:
`Λ` is, near `y`, the atomic structure transported by a local sc-diffeomorphism of a morphism
`y → U(x₀)`, or trivial (the zero section). -/
theorem theorem_13_5_3_local (D : AtomicData A) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (h : D.IsRelated Λ) (y : A.Obj) : D.IsLocallyTransported Λ y := by
  have := AtomicData.IsRelated.nonempty D hΛ h
  rw [AtomicData.IsRelated.eq_mult D h]
  by_cases hy : D.Reach y
  · exact Or.inl (D.exists_isLocalRepOn_transport hy)
  · refine Or.inr ⟨(A.X.saturation (closure D.V))ᶜ,
      D.isClosed_saturation_closure_V.isOpen_compl, fun h' => hy ?_,
      fun w hw => D.mult_eq_zeroMultisection hw⟩
    exact (D.reach_iff_mem_saturation y).2 (D.saturation_closure_V_subset h')

/-- **2021 Theorem 13.5.3, p. 630 (2017: Theorem 13.6), with a hypothesis**: an atomic
sc⁺-multisection is `Structurable` for any notion of structurability (Definition 13.3.6) for
which an sc⁺-multisection with atomic data whose local alternatives hold everywhere is
structurable (`hcrit`: the correspondences of the text's proof).  The local alternatives are
`theorem_13_5_3_local`. -/
theorem theorem_13_5_3_hyp {Structurable : (A.W → ℚ≥0) → Prop}
    (hcrit : ∀ (D : AtomicData A) (Λ : A.W → ℚ≥0), IsScPlusMultisection A Λ → D.IsRelated Λ →
      (∀ y, D.IsLocallyTransported Λ y) → Structurable Λ)
    {Λ : A.W → ℚ≥0} (hΛ : IsAtomic A Λ) : Structurable Λ := by
  obtain ⟨hΛm, D, hD⟩ := hΛ
  exact hcrit D Λ hΛm hD fun y => theorem_13_5_3_local D hΛm hD y

/-- `hcrit` is satisfiable: it holds for `Structurable = IsScPlusMultisection` (and the trivial
multisection is atomic, `isAtomic_zeroMultisection`). -/
theorem theorem_13_5_3_hyp_witness :
    ∀ (D : AtomicData A) (Λ : A.W → ℚ≥0), IsScPlusMultisection A Λ → D.IsRelated Λ →
      (∀ y, D.IsLocallyTransported Λ y) → IsScPlusMultisection A Λ :=
  fun _ _ h _ _ => h

open scoped Classical in
/-- **The last sentence of 2021 Theorem 13.5.5, p. 633**: the atomic `Λ` of Construction II is
structurable, from Theorem 13.5.3 (as in the text). -/
theorem theorem_13_5_5_structurable_hyp {Structurable : (A.W → ℚ≥0) → Prop}
    (h1353 : ∀ Λ, IsAtomic A Λ → Structurable Λ)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {x : A.Obj}
    (hx : x ∈ A.X.PObj.smoothSet) (R : A.X.NaturalRep x) (hprop : A.X.HasPropernessProperty R.U)
    (F : SymmetricFamily A R) [Nonempty F.I] :
    ∃ Λ : A.W → ℚ≥0, IsAtomic A Λ ∧
      (∀ w, A.P w ∉ A.X.saturation R.U → Λ w = zeroMultisection A w) ∧
      (∀ w, A.P w ∈ R.U → Λ w = (Fintype.card F.I : ℚ≥0)⁻¹ *
        ((Finset.univ.filter fun i => F.s i (A.P w) = w).card : ℚ≥0)) ∧ Structurable Λ := by
  obtain ⟨Λ, ⟨hΛ, hout, hin⟩, -⟩ := theorem_13_5_5 hbump hx R hprop F
  exact ⟨Λ, hΛ, hout, hin, h1353 Λ hΛ⟩

end SBLocalization

end Polyfold
