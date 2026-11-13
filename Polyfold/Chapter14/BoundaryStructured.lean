import Polyfold.Chapter14.BoundaryMultisection
import Polyfold.Chapter13.StructurableMultisection
import Polyfold.Chapter13.MultisectionSupport

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.1, pp. 644–646:
**Definition 14.1.7** (structured sc⁺-multisections over `∂X`) and the statement of
**Theorem 14.1.9** (the `∂`-Extension Theorem) (2017: Definition 14.4, Theorem 14.2).

# Structured sc⁺-multisections over the boundary

## The text, paraphrased

(Definition 14.1.7) For a strong bundle over a tame ep-groupoid with paracompact `|X|`, a
structured sc⁺-multisection over `∂X` is a class `[Λ, 𝒰, S, τ]`: `Λ : W|∂X → ℚ⁺` an
sc⁺-multisection functor, (1) `𝒰` a good system for `∂X`, (2) locally constant correspondences
`τ_{x,x'} : 𝒰(x, x') → J(x, x')` with finitely many values, with (a)
`τ_{x',x}(φ⁻¹) = τ_{x,x'}(φ)♯`, (b) `τ_{x,x}(Γ(g, z)) = [I_x ←Id I_x →g I_x]`, (c)
`g' ∗ τ_{x,x'}(φ) ∗ g = τ_{x,x'}(g' ∗ φ ∗ g)`, (3) symmetric sc⁺-section structures `sˣ` on
`U(x)` indexed by `I_x` representing `Λ`, (4) `sˣ'_{b(k)}(t(φ)) = μ(φ, sˣ_{a(k)}(s(φ)))` for
`φ ∈ 𝒰(x, x')` and `τ_{x,x'}(φ) = [I_x ←a I →b I_{x'}]`.  `Λ` is structurable if such a class
exists; the equivalence is "similar to the X-case" (Definition 13.3.8).  (Theorem 14.1.9) If `X`
is tame with paracompact `|X|` and admits sc-smooth partitions of unity, `Λ : W|∂X → ℚ⁺` is
structurable, `N` is an auxiliary norm, `Ũ` a saturated open neighbourhood of `dom-supp(Λ)` and
`f : X → [0, ∞)` a continuous functor supported in `Ũ` with `N(Λ)(x) < f(x)` on `dom-supp(Λ)`,
then there is a structurable `Λ' : W → ℚ⁺` with (1) `N(Λ') ≤ f`, (2) `dom-supp(Λ') ⊆ Ũ`,
(3) `Λ'|(W|∂X) = Λ`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `BoundaryDecoration A Λ` (`(𝒰, S)`: a good system for `∂X` and the structures of
  Definition 14.1.3 on the `U(x)`), `BoundaryDecoration.Tau` (the correspondences `τ` with (2),
  (2)(a)–(c) and (4)), `BoundaryStructuredTuple` (`(Λ, 𝒰, S, τ)`).
  Condition (4) is read pointwise on `𝒰(x, x')`, as printed (Definition 13.3.4 (3) in
  Chapter 13 asks it along the component of `φ`; pointwise on all of `𝒰(x, x')` is the same).
* The equivalence: `BoundaryStructuredTuple.Equiv` (`Λ = Λ'` over `∂X`, open neighbourhoods
  `O(x)` with `O(x) ∩ ∂X ⊆ U(x) ∩ U'(x)`, `I_x = I'_x`, `τ = τ'` on the morphisms between the
  `O(x) ∩ ∂X`), `equivalence`, `setoid`, `BoundaryStructuredMultisection A`; for tame `X` it is
  the literal analogue of Definition 13.3.8 (a good system `𝒰'' ⊆ 𝒰 ∩ 𝒰'`):
  `equiv_iff_goodSystem`.
* `IsBoundaryStructurable A Λ`, with the witness `isBoundaryStructurable_zero` (the zero
  multisection, for tame `X` with paracompact `|X|`).
* `boundaryDomSupp Λ` and **`theorem_14_1_9_statement A : Prop`** (not proved here), with
  `theorem_14_1_9_statement_hyp_witness` (its hypotheses are jointly satisfiable).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### Definition 14.1.7 -/

/-- **Definition 14.1.7 (1), (3)**: a good system `𝒰` for `∂X` and symmetric sc⁺-section
structures `sˣ` on the `U(x)` representing `Λ` (Definition 14.1.3). -/
structure BoundaryDecoration (A : SEP.{u}) (Λ : A.W → ℚ≥0) where
  /-- The good system `𝒰` for `∂X`. -/
  𝒰 : A.X.BoundaryGoodSystem
  /-- The structures `sˣ` on `U(x)`. -/
  S : ∀ x : A.X.PObj.boundary, BoundarySymmetricStructure A Λ (𝒰.nbhd x)

namespace BoundaryDecoration

variable {Λ : A.W → ℚ≥0}

/-- The identity of Definition 14.1.7 (4) for `i ∈ I_x`, `j ∈ I_{x'}` along `φ`:
`sˣ'_j(t(φ)) = μ(φ, sˣᵢ(s(φ)))`. -/
def Compat (D : BoundaryDecoration A Λ) {x x' : A.X.PObj.boundary} (φ : A.Mor) (i : (D.S x).I)
    (j : (D.S x').I) : Prop :=
  (D.S x').s j (A.X.tgt φ) = fibAct φ ((D.S x).s i (A.X.src φ))

/-- **2021 Definition 14.1.7 (2), (4), p. 645 (2017: Definition 14.4)**: correspondences
`τ_{x,x'} : 𝒰(x, x') → J(x, x')` for `x, x' ∈ ∂X`, locally constant (in `𝒰(x, x')`) with
finitely many values, with (a) `τ_{x',x}(φ⁻¹) = τ_{x,x'}(φ)♯`, (b)
`τ_{x,x}(Γ(g, z)) = [I_x ←Id I_x →g I_x]`, (c) `τ(g' ∗ φ ∗ g) = g' ∗ τ(φ) ∗ g`, and (4)
`sˣ'_{b(k)}(t(φ)) = μ(φ, sˣ_{a(k)}(s(φ)))` for every representative `[I_x ←a I →b I_{x'}]` of
`τ_{x,x'}(φ)` (`IndexCorr.Sat`). -/
structure Tau (D : BoundaryDecoration A Λ) where
  /-- The correspondences `τ_{x,x'}` (only their values on `𝒰(x, x')` matter). -/
  τ : ∀ x x' : A.X.PObj.boundary, A.Mor → IndexCorr (D.S x).I (D.S x').I
  locallyConstant : ∀ x x', ∀ φ ∈ D.𝒰.mor x x', ∀ᶠ ψ in 𝓝[D.𝒰.mor x x'] φ, τ x x' ψ = τ x x' φ
  finite : ∀ x x', (τ x x' '' D.𝒰.mor x x').Finite
  /-- (a) -/
  swap : ∀ x x', ∀ φ ∈ D.𝒰.mor x x', τ x' x (A.X.inv φ) = (τ x x' φ).swap
  /-- (b) -/
  diag : ∀ (x : A.X.PObj.boundary) (g : A.X.Isotropy x), ∀ z ∈ D.𝒰.U x,
    τ x x ((D.𝒰.nbhd x).rep.Γ g z) = IndexCorr.ofPerm (α := (D.S x).I) g
  /-- (c) -/
  biact : ∀ x x', ∀ φ ∈ D.𝒰.mor x x', ∀ (g' : A.X.Isotropy x') (g : A.X.Isotropy x),
    τ x x' (EpGroupoid.biact (D.𝒰.nbhd x) (D.𝒰.nbhd x') g' φ g) = IndexCorr.biact g' (τ x x' φ) g
  /-- (4) -/
  compat : ∀ x x', ∀ φ ∈ D.𝒰.mor x x', (τ x x' φ).Sat fun i j => D.Compat φ i j

end BoundaryDecoration

/-- **2021 Definition 14.1.7, p. 644 (2017: Definition 14.4)**: a tuple `(Λ, 𝒰, S, τ)` over
`∂X`. -/
structure BoundaryStructuredTuple (A : SEP.{u}) where
  /-- `Λ : W|∂X → ℚ⁺` (only its values over `∂X` matter). -/
  Λ : A.W → ℚ≥0
  isBoundaryScPlusMultisection : IsBoundaryScPlusMultisection A Λ
  /-- `(𝒰, S)`. -/
  dec : BoundaryDecoration A Λ
  /-- `τ`. -/
  tau : dec.Tau

/-- **Definition 14.1.7, last paragraph**: `Λ : W|∂X → ℚ⁺` is **structurable** if there is a
structured sc⁺-multisection over `∂X` of the form `[Λ, 𝒰, S, τ]`. -/
def IsBoundaryStructurable (A : SEP.{u}) (Λ : A.W → ℚ≥0) : Prop :=
  IsBoundaryScPlusMultisection A Λ ∧ ∃ D : BoundaryDecoration A Λ, Nonempty D.Tau

namespace BoundaryStructuredTuple

/-- **The equivalence of Definition 14.1.7** ("similar to the X-case", Definition 13.3.8):
`Λ = Λ'` over `∂X`, open neighbourhoods `O(x)` of the `x ∈ ∂X` with
`O(x) ∩ ∂X ⊆ U(x) ∩ U'(x)`, `I_x = I'_x`, and `τ_{x,x'} = τ'_{x,x'}` (transported along the
equalities) on the morphisms from `O(x) ∩ ∂X` to `O(x') ∩ ∂X`.  For tame `X` the `O(x)` can be
taken to form a good system (`equiv_iff_goodSystem`). -/
def Equiv (T T' : BoundaryStructuredTuple A) : Prop :=
  (∀ w, A.P w ∈ A.X.PObj.boundary → T.Λ w = T'.Λ w) ∧
  ∃ O : A.X.PObj.boundary → Set A.Obj, (∀ x, IsOpen (O x)) ∧ (∀ x, (x : A.Obj) ∈ O x) ∧
    (∀ x, O x ∩ A.X.PObj.boundary ⊆ T.dec.𝒰.U x ∩ T'.dec.𝒰.U x) ∧
    ∃ hI : ∀ x, (T.dec.S x).I = (T'.dec.S x).I, ∀ x x',
      ∀ φ ∈ A.X.morBetween (O x ∩ A.X.PObj.boundary) (O x' ∩ A.X.PObj.boundary),
        T'.tau.τ x x' φ = (T.tau.τ x x' φ).map (_root_.Equiv.cast (hI x))
          (_root_.Equiv.cast (hI x'))

theorem equivalence : _root_.Equivalence (Equiv (A := A)) where
  refl T := ⟨fun _ _ => rfl, fun x => (T.dec.𝒰.nbhd x).U, fun x => (T.dec.𝒰.nbhd x).isOpen_U,
    fun x => (T.dec.𝒰.nbhd x).mem_U, fun _ _ hy => ⟨hy, hy⟩, fun _ => rfl,
    fun _ _ _ _ => (IndexCorr.map_cast_rfl _).symm⟩
  symm := by
    rintro T T' ⟨hΛ, O, hO, hxO, hsub, hI, hτ⟩
    refine ⟨fun w hw => (hΛ w hw).symm, O, hO, hxO,
      fun x y hy => ⟨(hsub x hy).2, (hsub x hy).1⟩, fun x => (hI x).symm,
      fun x x' φ hφ => ?_⟩
    rw [hτ x x' φ hφ, IndexCorr.map_cast_symm]
  trans := by
    rintro T T' T'' ⟨hΛ₁, O₁, hO₁, hxO₁, hsub₁, hI₁, hτ₁⟩ ⟨hΛ₂, O₂, hO₂, hxO₂, hsub₂, hI₂, hτ₂⟩
    refine ⟨fun w hw => (hΛ₁ w hw).trans (hΛ₂ w hw), fun x => O₁ x ∩ O₂ x,
      fun x => (hO₁ x).inter (hO₂ x), fun x => ⟨hxO₁ x, hxO₂ x⟩,
      fun x y hy => ⟨(hsub₁ x ⟨hy.1.1, hy.2⟩).1, (hsub₂ x ⟨hy.1.2, hy.2⟩).2⟩,
      fun x => (hI₁ x).trans (hI₂ x), fun x x' φ hφ => ?_⟩
    have h₁ : φ ∈ A.X.morBetween (O₁ x ∩ A.X.PObj.boundary) (O₁ x' ∩ A.X.PObj.boundary) :=
      ⟨⟨hφ.1.1.1, hφ.1.2⟩, ⟨hφ.2.1.1, hφ.2.2⟩⟩
    have h₂ : φ ∈ A.X.morBetween (O₂ x ∩ A.X.PObj.boundary) (O₂ x' ∩ A.X.PObj.boundary) :=
      ⟨⟨hφ.1.1.2, hφ.1.2⟩, ⟨hφ.2.1.2, hφ.2.2⟩⟩
    rw [hτ₂ x x' φ h₂, hτ₁ x x' φ h₁, IndexCorr.map_cast_trans]

instance setoid (A : SEP.{u}) : Setoid (BoundaryStructuredTuple A) := ⟨Equiv, equivalence⟩

/-- **For tame `X`, the equivalence of Definition 14.1.7 in the form of Definition 13.3.8**:
`Λ = Λ'` over `∂X`, a good system `𝒰''` for `∂X` with `U''(x) ⊆ U(x) ∩ U'(x)`, `I_x = I'_x` and
`τ = τ'` on `𝒰''(x, x')`. -/
theorem equiv_iff_goodSystem (hX : A.X.IsTame) (T T' : BoundaryStructuredTuple A) :
    Equiv T T' ↔ (∀ w, A.P w ∈ A.X.PObj.boundary → T.Λ w = T'.Λ w) ∧
      ∃ 𝒰'' : A.X.BoundaryGoodSystem, (∀ x, 𝒰''.U x ⊆ T.dec.𝒰.U x ∩ T'.dec.𝒰.U x) ∧
        ∃ hI : ∀ x, (T.dec.S x).I = (T'.dec.S x).I, ∀ x x', ∀ φ ∈ 𝒰''.mor x x',
          T'.tau.τ x x' φ = (T.tau.τ x x' φ).map (_root_.Equiv.cast (hI x))
            (_root_.Equiv.cast (hI x')) := by
  constructor
  · rintro ⟨hΛ, O, hO, hxO, hsub, hI, hτ⟩
    obtain ⟨𝒲, -, h𝒲⟩ := T.dec.𝒰.exists_refinement hX O hO hxO
    have hW : ∀ x, 𝒲.U x ⊆ O x ∩ A.X.PObj.boundary := fun x y hy => ⟨h𝒲 x hy.1, hy.2⟩
    exact ⟨hΛ, 𝒲, fun x => (hW x).trans (hsub x), hI, fun x x' φ hφ =>
      hτ x x' φ (EpGroupoid.morBetween_mono (hW x) (hW x') hφ)⟩
  · rintro ⟨hΛ, 𝒰'', hsub, hI, hτ⟩
    exact ⟨hΛ, fun x => (𝒰''.nbhd x).U, fun x => (𝒰''.nbhd x).isOpen_U,
      fun x => (𝒰''.nbhd x).mem_U, hsub, hI, hτ⟩

end BoundaryStructuredTuple

/-- **2021 Definition 14.1.7, p. 644 (2017: Definition 14.4)**: a **structured sc⁺-multisection
over `∂X`**, a class `[Λ, 𝒰, S, τ]`. -/
def BoundaryStructuredMultisection (A : SEP.{u}) : Type _ :=
  Quotient (BoundaryStructuredTuple.setoid A)

/-- The functor `Λ` over `∂X` of a structured sc⁺-multisection over `∂X` (well defined over
`∂X`; off `∂X` we take the values of a chosen representative). -/
def BoundaryStructuredMultisection.forget (L : BoundaryStructuredMultisection A) : A.W → ℚ≥0 :=
  (Quotient.out L).Λ

theorem BoundaryStructuredMultisection.forget_mk (T : BoundaryStructuredTuple A) {w : A.W}
    (hw : A.P w ∈ A.X.PObj.boundary) :
    BoundaryStructuredMultisection.forget (Quotient.mk _ T) w = T.Λ w :=
  (Quotient.mk_out (s := BoundaryStructuredTuple.setoid A) T).1 w hw

theorem isBoundaryStructurable_iff {Λ : A.W → ℚ≥0} :
    IsBoundaryStructurable A Λ ↔ ∃ T : BoundaryStructuredTuple A, T.Λ = Λ := by
  constructor
  · rintro ⟨hΛ, D, ⟨t⟩⟩
    exact ⟨⟨Λ, hΛ, D, t⟩, rfl⟩
  · rintro ⟨T, rfl⟩
    exact ⟨T.isBoundaryScPlusMultisection, T.dec, ⟨T.tau⟩⟩

/-! ### The zero multisection over `∂X` is structurable (nonvacuity) -/

/-- The structure of the zero multisection over `∂X` on a good system for `∂X`: the zero section
on every `U(x)`, `τ ≡ [{∗} ← {∗} → {∗}]`. -/
def BoundaryDecoration.zeroTau (𝒰 : A.X.BoundaryGoodSystem) :
    (⟨𝒰, fun x => zeroBoundaryStructure (𝒰.nbhd x)⟩ :
      BoundaryDecoration A (zeroMultisection A)).Tau where
  τ _ _ _ := IndexCorr.ofEquiv (_root_.Equiv.refl PUnit.{u + 1})
  locallyConstant _ _ _ _ := Eventually.of_forall fun _ => rfl
  finite _ _ := (finite_singleton (IndexCorr.ofEquiv (_root_.Equiv.refl PUnit.{u + 1}))).subset
    (by rintro _ ⟨_, _, rfl⟩; rfl)
  swap _ _ _ _ := (IndexCorr.swap_ofEquiv_of_subsingleton (α := PUnit.{u + 1}) _).symm
  diag _ _ _ _ := IndexCorr.ofEquiv_eq_of_subsingleton (α := PUnit.{u + 1}) _ _
  biact _ _ _ _ g' g := (IndexCorr.example_13_3_3 g' _ g).symm
  compat _ _ _ _ := IndexCorr.sat_of_forall (fun _ _ => (fibAct_fiberZero rfl rfl).symm) _

/-- **Nonvacuity of Definition 14.1.7**: over a tame ep-groupoid with paracompact orbit space the
zero multisection is structurable over `∂X` (a good system for `∂X` exists by
`theorem_14_1_6_hyp`). -/
theorem isBoundaryStructurable_zero (hX : A.X.IsTame) (hpara : A.X.HasParacompactOrbitSpace) :
    IsBoundaryStructurable A (zeroMultisection A) := by
  obtain ⟨𝒰, -⟩ := A.X.theorem_14_1_6_hyp hX hpara (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  exact ⟨isBoundaryScPlusMultisection_zero hX, _, ⟨BoundaryDecoration.zeroTau 𝒰⟩⟩

/-! ### Theorem 14.1.9 (statement) -/

/-- **`dom-supp(Λ)`** for `Λ : W|∂X → ℚ⁺` (Definition 13.2.14 read over `∂X`): the closure of the
set of `x ∈ ∂X` over which `Λ` charges a nonzero point. -/
def boundaryDomSupp (Λ : A.W → ℚ≥0) : Set A.Obj :=
  closure {x | x ∈ A.X.PObj.boundary ∧ ∃ w, A.P w = x ∧ w ≠ fiberZero A.P x ∧ 0 < Λ w}

theorem boundaryDomSupp_zero : boundaryDomSupp (zeroMultisection A) = ∅ := by
  classical
  rw [boundaryDomSupp, closure_empty_iff, eq_empty_iff_forall_notMem]
  rintro x ⟨-, w, rfl, hw, hpos⟩
  rw [zeroMultisection, if_neg hw] at hpos
  exact lt_irrefl _ hpos

/-- **2021 Theorem 14.1.9 (∂-Extension Theorem), p. 646 (2017: Theorem 14.2)**, as a statement
(proved in §§14.3–14.5; not proved here).  Let `(P : W → X, μ)` be a strong bundle over a tame
ep-groupoid with paracompact orbit space whose M-polyfold `X` admits sc-smooth partitions of
unity, `Λ : W|∂X → ℚ⁺` structurable (Definition 14.1.7), `N` an auxiliary norm (Definition
8.3.5), `Ũ` a saturated open neighbourhood of `dom-supp(Λ)` and `f : X → [0, ∞)` a continuous
functor supported in `Ũ` (`tsupport f ⊆ Ũ`) with `N(Λ)(x) < f(x)` on `dom-supp(Λ)`.  Then there
is a structurable sc⁺-multisection functor `Λ' : W → ℚ⁺` (Definition 13.3.6) with
(1) `N(Λ')(x) ≤ f(x)` for all `x`, (2) `dom-supp(Λ') ⊆ Ũ`, (3) `Λ'|(W|∂X) = Λ`. -/
def theorem_14_1_9_statement (A : SEP.{u}) : Prop :=
  A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
  ∀ Λ : A.W → ℚ≥0, IsBoundaryStructurable A Λ →
  ∀ N : A.B.One → ℝ, A.E.IsAuxNorm N →
  ∀ Ũ : Set A.Obj, IsOpen Ũ → A.X.IsSaturated Ũ → boundaryDomSupp Λ ⊆ Ũ →
  ∀ f : A.Obj → ℝ, Continuous f → (∀ x, 0 ≤ f x) → (∀ φ, f (A.X.tgt φ) = f (A.X.src φ)) →
    tsupport f ⊆ Ũ → (∀ x ∈ boundaryDomSupp Λ, pointwiseNorm N Λ x < f x) →
  ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ x, pointwiseNorm N Λ' x ≤ f x) ∧
    domSupp Λ' ⊆ Ũ ∧ ∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w

/-- **The hypotheses on `Λ`, `Ũ`, `f` in `theorem_14_1_9_statement` are jointly satisfiable**
(for tame `X` with paracompact orbit space): `Λ = 0`, `Ũ = ∅`, `f = 0`. -/
theorem theorem_14_1_9_statement_hyp_witness (hX : A.X.IsTame)
    (hpara : A.X.HasParacompactOrbitSpace) (N : A.B.One → ℝ) :
    IsBoundaryStructurable A (zeroMultisection A) ∧ IsOpen (∅ : Set A.Obj) ∧
      A.X.IsSaturated (∅ : Set A.Obj) ∧ boundaryDomSupp (zeroMultisection A) ⊆ ∅ ∧
      Continuous (fun _ : A.Obj => (0 : ℝ)) ∧ tsupport (fun _ : A.Obj => (0 : ℝ)) ⊆ ∅ ∧
      ∀ x ∈ boundaryDomSupp (zeroMultisection A),
        pointwiseNorm N (zeroMultisection A) x < (fun _ : A.Obj => (0 : ℝ)) x := by
  refine ⟨isBoundaryStructurable_zero hX hpara, isOpen_empty, ?_, by rw [boundaryDomSupp_zero],
    continuous_const, by simp, by simp [boundaryDomSupp_zero]⟩
  simp [GroupoidStr.IsSaturated]

end SBLocalization

end Polyfold
