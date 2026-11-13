import Polyfold.Chapter13.P3D_Structurable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.4, pp. 628–629: **Definition 13.4.5** (commensurable structured sc⁺-multisections and their
commensurable sum) and the locally finite commensurable sum after it (2017: Definition 13.22).

# Commensurable structured sc⁺-multisections

## The text, paraphrased

(Definition 13.4.5, `|X|` paracompact) (1) Two structured `[Λⱼ, 𝒰ⱼ, Sⱼ, τⱼ]` are commensurable if
representatives can be taken with `𝒰₁ = 𝒰₂`, `τ₁ = τ₂` and `I¹_x = I²_x`; such a choice of common
data is denoted `c`.  (2) The commensurable sum `Λ₁ ⊕_c Λ₂` is `[Λ, 𝒰, S, τ]` with the sections
`sˣᵢ = s^{1,x}ᵢ + s^{2,x}ᵢ` and `Λ(w) = |I_x|⁻¹·#{i | sˣᵢ(P(w)) = w}` for `P(w) ∈ U(x)`.  The same
works for a family `([Λⱼ, 𝒰, Sⱼ, τ])_{j ∈ J}` of pairwise commensurable structured
multisections whose underlying family is locally finite ("evident and does not require a
proof").

## What is formalized (namespace `Polyfold.SBLocalization`)

* `CommData A`: a choice `c` of common data: a good system `𝒰`, index types `I_x` with their
  `G_x`-actions, and maps `τ_{x,x'}` with the conditions of Definitions 13.3.4 (1)–(2) and 13.3.6
  that do not involve sections.  `CommData.Over c Λ`: symmetric sections for `Λ` over `c` for which
  `τ` satisfies condition (3) of Definition 13.3.4.  `Over.toTuple`: the structured tuple
  `(Λ, 𝒰, S, τ)`; `CommData.ofTuple`, `Over.ofTuple`: every structured tuple is of this form.
* `IndexCorr.ofEquiv_injective`, `CommData.smul_eq_of_diag`: the `G_x`-actions are determined by
  `τ` (Definition 13.3.6 (1)), so taking them as part of `c` adds nothing to "`τ₁ = τ₂`".
* **Count transport** (`IndexCorr.count_eq_of_sat`): along a correspondence the normalized counts
  `|I_x|⁻¹·#{i | sᵢ = v}` and `|I_{x'}|⁻¹·#{j | s'ⱼ = μ(φ, v)}` agree.  This is why the counting
  formula of (2) defines a functor and does not depend on `x`.
* **Definition 13.4.5 (1)**: `Commensurable L₁ L₂`.
* **Definition 13.4.5 (2) and the locally finite sum**: `CommData.sumSec` (the sections
  `∑ᶠⱼ s^{j,x}ᵢ`), `CommData.sumMult` (the functor of (2)), `CommData.Over.lfSum` (the sum is an
  `Over c`), `CommData.Sections.isScPlusMultisection_sumMult`, `definition_13_4_5_lf` (the sum
  of a locally finite family over `c` is a structured sc⁺-multisection with data `(𝒰, S, τ)`),
  `definition_13_4_5`, `commSum₂` (the binary sum `Λ₁ ⊕_c Λ₂`, sections `s¹ + s²`).

## Readings

* "Locally finite" is Definition 13.2.12 (`IsLocallyFiniteFamily`: an open saturated `O(x)` over
  which only finitely many `Λⱼ` take a positive value at some `w ≠ 0`); the text's condition after
  Definition 13.4.5 is the same with "open".  For functors the two agree.
* The count `|I_x|⁻¹·#{…}` of (2) is taken at `x = P(w)` (`sumMult`), and `Sections.countAt_eq`
  shows it is the count at any `x` with `P(w) ∈ U(x)`.
* `I_x ≠ ∅` is part of `c` (`CommData.nonempty`): it holds for the data of every structured
  sc⁺-multisection (`SymmetricStructureOn.card_pos`) and is needed for an empty family `J`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

/-! ### Count transport along a correspondence -/

namespace IndexCorr

variable {α β : Type u}

theorem ofEquiv_injective [Fintype α] {e e' : α ≃ β} (h : ofEquiv e = ofEquiv e') : e = e' := by
  obtain ⟨c, hc⟩ := mk_eq_mk.1 h
  ext i
  have h1 : c i = i := (hc i).1
  have h2 : e' (c i) = e i := (hc i).2
  rw [h1] at h2
  exact h2.symm

/-- Every condition `R(a(k), b(k))` that holds for all `j ∈ J` holds for the conjunction. -/
theorem sat_iInter {J : Type*} {R : J → α → β → Prop} {τ : IndexCorr α β}
    (h : ∀ j, τ.Sat (R j)) : τ.Sat fun i i' => ∀ j, R j i i' := by
  revert h
  exact ind (fun d h k j => h j k) τ

theorem card_filter_comp_eq {K I : Type u} [Fintype K] [Fintype I] (a : K → I)
    (p : ℕ) (hp : ∀ i, Fintype.card {k // a k = i} = p) (q : I → Prop) [DecidablePred q] :
    (Finset.univ.filter fun k => q (a k)).card = p * (Finset.univ.filter q).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := a) (t := Finset.univ.filter q)
    (fun k hk => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hk).2⟩)]
  rw [Finset.sum_congr rfl (g := fun _ => p), Finset.sum_const, smul_eq_mul, mul_comm]
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [← hp i, Fintype.card_subtype]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro h; exact ⟨h ▸ hi, h⟩

/-- **Count transport along a correspondence**: if a representative `I_x ←a I →b I_{x'}` of `τ`
satisfies `s'_{b(k)} = f(s_{a(k)})` for all `k`, with `f` injective, then
`|I_x|⁻¹·#{i | sᵢ = v} = |I_{x'}|⁻¹·#{j | s'ⱼ = f(v)}` (all fibres of `a`, resp. `b`, have the
same size). -/
theorem count_eq_of_sat [Fintype α] [Fintype β] {γ δ : Type*} {s : α → γ} {s' : β → δ}
    {f : γ → δ} {T : Set γ} (hf : InjOn f T) (hsT : ∀ i, s i ∈ T) {τ : IndexCorr α β}
    (h : τ.Sat fun i j => s' j = f (s i)) {v : γ} (hv : v ∈ T) :
    (Fintype.card α : ℚ≥0)⁻¹ * ((Finset.univ.filter fun i => s i = v).card : ℚ≥0) =
      (Fintype.card β : ℚ≥0)⁻¹ * ((Finset.univ.filter fun j => s' j = f v).card : ℚ≥0) := by
  revert h
  refine ind (fun d h => ?_) τ
  -- the common fibre sizes `p` of `a` and `q` of `b`
  have hfa : ∀ i, Fintype.card {k // d.a k = i} = Nat.card {k // d.a k = i} := fun i =>
    (Nat.card_eq_fintype_card).symm
  have hfb : ∀ j, Fintype.card {k // d.b k = j} = Nat.card {k // d.b k = j} := fun j =>
    (Nat.card_eq_fintype_card).symm
  by_cases hα : IsEmpty α
  · have hK : IsEmpty d.I := ⟨fun k => hα.false (d.a k)⟩
    have hβ : IsEmpty β := ⟨fun j => hK.false (d.surjective_b j).choose⟩
    simp [Fintype.card_eq_zero]
  rw [not_isEmpty_iff] at hα
  obtain ⟨i₀⟩ := hα
  obtain ⟨k₀, hk₀⟩ := d.surjective_a i₀
  set p := Fintype.card {k // d.a k = i₀}
  set q := Fintype.card {k // d.b k = d.b k₀}
  have hp : ∀ i, Fintype.card {k // d.a k = i} = p := fun i => by
    rw [hfa, show p = Nat.card {k // d.a k = i₀} from hfa i₀]; exact d.uniform_a i i₀
  have hq : ∀ j, Fintype.card {k // d.b k = j} = q := fun j => by
    rw [hfb, show q = Nat.card {k // d.b k = d.b k₀} from hfb _]; exact d.uniform_b j (d.b k₀)
  have hp0 : p ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero]
    exact Fintype.card_pos_iff.2 ⟨⟨k₀, hk₀⟩⟩
  have hq0 : q ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero]
    exact Fintype.card_pos_iff.2 ⟨⟨k₀, rfl⟩⟩
  -- `|I| = p·|I_x| = q·|I_{x'}|`
  have hKa : Fintype.card d.I = p * Fintype.card α := by
    have := card_filter_comp_eq d.a p hp (fun _ => True)
    simpa using this
  have hKb : Fintype.card d.I = q * Fintype.card β := by
    have := card_filter_comp_eq d.b q hq (fun _ => True)
    simpa using this
  -- the two counts of `k`
  have hA := card_filter_comp_eq d.a p hp (fun i => s i = v)
  have hB := card_filter_comp_eq d.b q hq (fun j => s' j = f v)
  have hAB : (Finset.univ.filter fun k => s (d.a k) = v) =
      (Finset.univ.filter fun k => s' (d.b k) = f v) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h k]
    exact ⟨fun e => e ▸ rfl, fun e => hf (hsT _) hv e⟩
  rw [hAB] at hA
  rw [← div_eq_inv_mul, ← div_eq_inv_mul]
  have hp' : (p : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.2 hp0
  have hq' : (q : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.2 hq0
  rw [← mul_div_mul_left _ _ hp', ← mul_div_mul_left (((Finset.univ.filter fun j => s' j = f v).card
    : ℕ) : ℚ≥0) _ hq']
  have e1 : (p : ℚ≥0) * ((Finset.univ.filter fun i => s i = v).card : ℚ≥0) =
      (q : ℚ≥0) * ((Finset.univ.filter fun j => s' j = f v).card : ℚ≥0) := by
    exact_mod_cast hA.symm.trans hB
  have e2 : (p : ℚ≥0) * (Fintype.card α : ℚ≥0) = (q : ℚ≥0) * (Fintype.card β : ℚ≥0) := by
    exact_mod_cast hKa.symm.trans hKb
  rw [e1, e2]

end IndexCorr

/-! ### Locality of sc⁺-sections on open sets -/

/-- **Being an sc⁺-section on an open set is local.** -/
theorem IsScPlusSectionOn.of_locally {A : SEP.{u}} {s : A.Obj → A.W} {U : Set A.Obj}
    (hU : IsOpen U)
    (h : ∀ y ∈ U, ∃ U' : Set A.Obj, IsOpen U' ∧ y ∈ U' ∧ U' ⊆ U ∧ IsScPlusSectionOn A s U') :
    IsScPlusSectionOn A s U := by
  have hsec : ∀ y ∈ U, A.P (s y) = y := fun y hy => by
    obtain ⟨U', -, hy', -, h'⟩ := h y hy
    exact h'.1 y hy'
  have hone : ∀ y ∈ U, s y ∈ A.B.oneSet := fun y hy => by
    obtain ⟨U', -, hy', -, h'⟩ := h y hy
    exact h'.mem_oneSet hy'
  let G : A.Obj → A.B.One := fun z =>
    if hz : s z ∈ A.B.oneSet then A.B.oneMk (s z) hz
    else A.B.oneMk _ ((StrongBundle.isScPlusSection_fiberZero (B := A.B)).mem_oneSet z)
  have hG : ∀ z ∈ U, A.B.oneVal (G z) = s z := fun z hz => by
    simp only [G, dif_pos (hone z hz), StrongBundle.oneVal_oneMk]
  refine ⟨hsec, G, hG, MPolyfold.IsScSmoothOn.of_locally hU fun y hy => ?_⟩
  obtain ⟨U', hU', hy', hU'U, -, G', hG', hG's⟩ := h y hy
  refine ⟨U', hU', hy', hU'U, hG's.congr fun z hz => A.B.oneVal_injective ?_⟩
  rw [hG' z hz, hG z (hU'U hz)]

/-! ### Common data of commensurable structured multisections -/

variable {A : SEP.{u}}

/-- **A choice `c` of common data (Definition 13.4.5 (1), p. 628)**: a good system `𝒰`, index
types `I_x` (non-empty) with `G_x`-actions, and maps `τ_{x,x'} : 𝒰(x, x') → J(x, x')` satisfying
the conditions of Definitions 13.3.4 (1)–(2) and 13.3.6 (1)–(2), which do not involve sections. -/
structure CommData (A : SEP.{u}) where
  /-- The good system `𝒰`. -/
  𝒰 : A.X.GoodSystem
  /-- The index sets `I_x`. -/
  I : A.Obj → Type u
  [fintype : ∀ x, Fintype (I x)]
  [mulAction : ∀ x, MulAction (A.X.Isotropy x) (I x)]
  nonempty : ∀ x, Nonempty (I x)
  /-- The maps `τ_{x,x'}`. -/
  τ : ∀ x x' : A.Obj, A.Mor → IndexCorr (I x) (I x')
  locallyConstant : ∀ x x', ∀ φ ∈ 𝒰.mor x x', ∀ᶠ ψ in 𝓝 φ, τ x x' ψ = τ x x' φ
  finite : ∀ x x', (τ x x' '' 𝒰.mor x x').Finite
  biact : ∀ x x', ∀ φ ∈ 𝒰.mor x x', ∀ (g' : A.X.Isotropy x') (g : A.X.Isotropy x),
    τ x x' (𝒰.biact x x' g' φ g) = IndexCorr.biact g' (τ x x' φ) g
  diag : ∀ x (g : A.X.Isotropy x), ∀ y ∈ 𝒰.U x,
    τ x x ((𝒰.nbhd x).rep.Γ g y) = IndexCorr.ofPerm (α := I x) g
  swap : ∀ x x', ∀ φ ∈ 𝒰.mor x' x, τ x' x φ = (τ x x' (A.X.inv φ)).swap

attribute [instance] CommData.fintype CommData.mulAction

namespace CommData

variable (c : CommData A)

/-- **The `G_x`-action on `I_x` is determined by `τ`** (Definition 13.3.6 (1) at `y = x`):
two actions for which `τ_{x,x}(g) = [I_x ←id I_x →g I_x]` coincide. -/
theorem smul_eq_of_diag {x : A.Obj} {α : Type u} [Fintype α] (m₁ m₂ : MulAction (A.X.Isotropy x) α)
    {g : A.X.Isotropy x}
    (h : @IndexCorr.ofPerm α _ _ _ m₁ g = @IndexCorr.ofPerm α _ _ _ m₂ g) (i : α) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ m₁.toSMul) g i =
      @HSMul.hSMul _ _ _ (@instHSMul _ _ m₂.toSMul) g i := by
  have := IndexCorr.ofEquiv_injective h
  exact congrArg (fun e : α ≃ α => e i) this

/-- The identity (3) of Definition 13.3.4 along `ψ` for sections `s` over `c`:
`s^{x'}_j(t(ψ)) = μ(ψ, sˣᵢ(s(ψ)))`. -/
def Compat (s : ∀ x, c.I x → A.Obj → A.W) {x x' : A.Obj} (ψ : A.Mor) (i : c.I x)
    (j : c.I x') : Prop :=
  s x' j (A.X.tgt ψ) = fibAct ψ (s x i (A.X.src ψ))

/-- **Sections over `c`**: symmetric sc⁺-sections `(sˣᵢ)_{i ∈ I_x}` on every `U(x)` (Definition
13.2.5 (1)) for which `τ` satisfies condition (3) of Definition 13.3.4.  (No functor `Λ` yet:
the counting formula defines it, `Sections.mult`.) -/
structure Sections where
  /-- The sections `sˣᵢ`. -/
  s : ∀ x, c.I x → A.Obj → A.W
  isScPlusSectionOn : ∀ x i, IsScPlusSectionOn A (s x i) (c.𝒰.U x)
  equivariant : ∀ x (g : A.X.Isotropy x) (i : c.I x), ∀ y ∈ c.𝒰.U x,
    s x (g • i) ((c.𝒰.nbhd x).rep.Φ g y) = fibAct ((c.𝒰.nbhd x).rep.Γ g y) (s x i y)
  compat : ∀ x x', ∀ φ ∈ c.𝒰.mor x x',
    (c.τ x x' φ).Sat fun i j => ∀ ψ ∈ c.𝒰.comp x x' φ, c.Compat s ψ i j

/-- `|I_x|⁻¹·#{i ∈ I_x | sˣᵢ(P(w)) = w}`. -/
def countAt (s : ∀ x, c.I x → A.Obj → A.W) (x : A.Obj) (w : A.W) : ℚ≥0 :=
  (Fintype.card (c.I x) : ℚ≥0)⁻¹ * ((Finset.univ.filter fun i => s x i (A.P w) = w).card : ℚ≥0)

/-- **The functor of Definition 13.4.5 (2)**: `Λ(w) = |I_x|⁻¹·#{i | sˣᵢ(P(w)) = w}`, at
`x = P(w)`. -/
def sumMult (s : ∀ x, c.I x → A.Obj → A.W) (w : A.W) : ℚ≥0 := c.countAt s (A.P w) w

/-- **Sections over `c` for a given functor `Λ`**: the counting formula (Definition 13.2.5 (2))
holds on every `U(x)`.  The data of a structured `(Λ, 𝒰, S, τ)` with the common `c`. -/
structure Over (Λ : A.W → ℚ≥0) extends c.Sections where
  rep : ∀ x w, A.P w ∈ c.𝒰.U x → Λ w = c.countAt s x w

variable {c}

namespace Sections

variable (S : c.Sections)

theorem P_s {x : A.Obj} (i : c.I x) {y : A.Obj} (hy : y ∈ c.𝒰.U x) : A.P (S.s x i y) = y :=
  (S.isScPlusSectionOn x i).1 y hy

/-- The identity (3) along `φ` itself. -/
theorem compat_self {x x' : A.Obj} {φ : A.Mor} (hφ : φ ∈ c.𝒰.mor x x') :
    (c.τ x x' φ).Sat fun i j => c.Compat S.s φ i j :=
  IndexCorr.sat_mono (fun _ _ H => H φ (c.𝒰.mem_comp hφ)) (S.compat x x' φ hφ)

/-- **Count transport**: `countAt x v = countAt x' (μ(φ, v))` for `φ ∈ 𝒰(x, x')`,
`P(v) = s(φ)`. -/
theorem countAt_fibAct {x x' : A.Obj} {φ : A.Mor} (hφ : φ ∈ c.𝒰.mor x x') {v : A.W}
    (hv : A.P v = A.X.src φ) : c.countAt S.s x v = c.countAt S.s x' (fibAct φ v) := by
  unfold countAt
  rw [P_fibAct hv, hv]
  refine IndexCorr.count_eq_of_sat (s := fun i => S.s x i (A.X.src φ))
    (s' := fun j => S.s x' j (A.X.tgt φ)) (f := fibAct φ) (T := {w | A.P w = A.X.src φ})
    (fun a ha b hb e => ?_) (fun i => S.P_s i hφ.1) (S.compat_self hφ) hv
  rw [fibAct_of ha, fibAct_of hb] at e
  exact EpStrongBundle.μ_injective_snd A.E ha hb e

theorem fibAct_unit {y : A.Obj} {v : A.W} (hv : A.P v = y) : fibAct (A.X.unit y) v = v := by
  subst hv
  rw [fibAct_of (A.X.src_unit _).symm]
  exact (A.E.μ_congr rfl).trans (A.E.μ_unit v)

theorem unit_mem_mor {x y : A.Obj} (hy : y ∈ c.𝒰.U x) : A.X.unit y ∈ c.𝒰.mor x y :=
  ⟨by rw [A.X.src_unit]; exact hy, by rw [A.X.tgt_unit]; exact c.𝒰.mem_U y⟩

/-- **The count does not depend on `x`**: `countAt x w = countAt (P(w)) w` for `P(w) ∈ U(x)`. -/
theorem countAt_eq {x : A.Obj} {w : A.W} (hw : A.P w ∈ c.𝒰.U x) :
    c.countAt S.s x w = c.sumMult S.s w := by
  have h := S.countAt_fibAct (unit_mem_mor hw) (v := w) (A.X.src_unit _).symm
  rwa [fibAct_unit rfl] at h

/-- `Λ` is a functor on `W`. -/
theorem isWFunctor_sumMult : IsWFunctor A (c.sumMult S.s) := by
  rintro ⟨⟨φ, w⟩, hq⟩
  have hq' : A.P w = A.X.src φ := hq
  have hφ : φ ∈ c.𝒰.mor (A.X.src φ) (A.X.tgt φ) := ⟨c.𝒰.mem_U _, c.𝒰.mem_U _⟩
  have h := S.countAt_fibAct hφ hq'
  rw [fibAct_of hq'] at h
  change c.countAt S.s (A.P (A.E.μ ⟨(φ, w), hq⟩)) _ = c.countAt S.s (A.P w) w
  rw [A.E.P_μ, hq', h]

/-- The counting formula on `U(x)` as a sum of weights `|I_x|⁻¹`. -/
theorem countAt_eq_sum (x : A.Obj) (w : A.W) :
    c.countAt S.s x w =
      ∑ i : c.I x, if w = S.s x i (A.P w) then (Fintype.card (c.I x) : ℚ≥0)⁻¹ else 0 := by
  unfold countAt
  rw [Finset.natCast_card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : S.s x i (A.P w) = w
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg fun e => h e.symm, mul_zero]

theorem card_ne_zero (x : A.Obj) : (Fintype.card (c.I x) : ℚ≥0) ≠ 0 := by
  have := c.nonempty x
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

/-- **The functor of the counting formula is an sc⁺-multisection**: on `U(x)` it has the local
representation `(sˣᵢ, |I_x|⁻¹)`. -/
theorem isScPlusMultisection_sumMult : IsScPlusMultisection A (c.sumMult S.s) := by
  refine ⟨S.isWFunctor_sumMult, fun x => hasLocalSectionStructure_of_isLocalRepOn
    (c.𝒰.isOpen_U x) (c.𝒰.mem_U x) (isLocalRepOn_of_fintype (K := c.I x) (S.s x)
      (fun _ => (Fintype.card (c.I x) : ℚ≥0)⁻¹)
      (fun _ => inv_pos.2 (pos_iff_ne_zero.2 (card_ne_zero x))) (S.isScPlusSectionOn x) ?_
      fun w hw => ?_)⟩
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ (card_ne_zero x)]
  · rw [← S.countAt_eq hw, S.countAt_eq_sum]

/-- The sections over `c` are sections over `c` for the functor they define. -/
def toOver : c.Over (c.sumMult S.s) :=
  { S with rep := fun _ _ hw => (S.countAt_eq hw).symm }

end Sections

namespace Over

variable {Λ : A.W → ℚ≥0} (o : c.Over Λ)

/-- **A functor with sections over `c` is the functor of the counting formula.** -/
theorem eq_sumMult : Λ = c.sumMult o.s :=
  funext fun w => (o.rep (A.P w) w (c.𝒰.mem_U _)).trans rfl

theorem isScPlusMultisection (o : c.Over Λ) : IsScPlusMultisection A Λ := by
  rw [o.eq_sumMult]; exact o.toSections.isScPlusMultisection_sumMult

/-- The symmetric structure on `U(x)` (Definition 13.2.5 on the neighbourhood of `𝒰`). -/
def sym (x : A.Obj) : SymmetricStructureOn A Λ (c.𝒰.nbhd x) where
  I := c.I x
  s := o.s x
  isScPlusSectionOn := o.isScPlusSectionOn x
  equivariant := o.equivariant x
  rep := o.rep x

/-- The decoration `(𝒰, S)`. -/
def toDecoration : Decoration A Λ := ⟨c.𝒰, o.sym⟩

/-- The correspondences `τ` of `c` structure the decoration (Definition 13.3.6). -/
def tau : o.toDecoration.Tau where
  τ := c.τ
  isCorrespondence x x' :=
    { locallyConstant := c.locallyConstant x x'
      finite := c.finite x x'
      biact := c.biact x x'
      compat := o.compat x x' }
  diag := c.diag
  swap := c.swap

/-- **The structured tuple `(Λ, 𝒰, S, τ)`** of sections over `c`. -/
def toTuple : StructuredTuple A := ⟨⟨Λ, o.isScPlusMultisection, o.toDecoration⟩, o.tau⟩

@[simp] theorem toTuple_Λ : o.toTuple.Λ = Λ := rfl

/-- The class `[Λ, 𝒰, S, τ]`. -/
def toStructured : StructuredMultisection A := Quotient.mk _ o.toTuple

theorem s_eq_fiberZero {x : A.Obj} {y : A.Obj} (hy : y ∈ c.𝒰.U x)
    (h1 : Λ (fiberZero A.P y) = 1) (i : c.I x) : o.s x i y = fiberZero A.P y :=
  (o.sym x).s_eq_fiberZero o.isScPlusMultisection hy h1 i

end Over

/-! ### Every structured tuple is a tuple over its own data -/

/-- The common data of a structured tuple `(Λ, 𝒰, S, τ)`. -/
def ofTuple (T : StructuredTuple A) : CommData A where
  𝒰 := T.dec.𝒰
  I x := (T.dec.S x).I
  nonempty x := Fintype.card_pos_iff.1 ((T.dec.S x).card_pos T.isScPlusMultisection)
  τ := T.tau.τ
  locallyConstant x x' := (T.tau.isCorrespondence x x').locallyConstant
  finite x x' := (T.tau.isCorrespondence x x').finite
  biact x x' := (T.tau.isCorrespondence x x').biact
  diag := T.tau.diag
  swap := T.tau.swap

/-- The sections of a structured tuple over its own data. -/
def Over.ofTuple (T : StructuredTuple A) : (ofTuple T).Over T.Λ where
  s x := (T.dec.S x).s
  isScPlusSectionOn x := (T.dec.S x).isScPlusSectionOn
  equivariant x := (T.dec.S x).equivariant
  compat x x' := (T.tau.isCorrespondence x x').compat
  rep x := (T.dec.S x).rep

theorem Over.ofTuple_toTuple (T : StructuredTuple A) : (Over.ofTuple T).toTuple = T := rfl

end CommData

/-! ### Definition 13.4.5 (1) -/

/-- **2021 Definition 13.4.5 (1), p. 628 (2017: Definition 13.22)**: two structured
sc⁺-multisections `[Λ₁, 𝒰₁, S₁, τ₁]`, `[Λ₂, 𝒰₂, S₂, τ₂]` are **commensurable** if they have
representatives with the same good system, the same index sets `I_x` and the same `τ`: tuples over a
common choice `c` (`CommData`). -/
def Commensurable (L₁ L₂ : StructuredMultisection A) : Prop :=
  ∃ (c : CommData A) (Λ₁ Λ₂ : A.W → ℚ≥0) (o₁ : c.Over Λ₁) (o₂ : c.Over Λ₂),
    o₁.toStructured = L₁ ∧ o₂.toStructured = L₂

/-- Every structured sc⁺-multisection is commensurable with itself. -/
theorem Commensurable.refl (L : StructuredMultisection A) : Commensurable L L :=
  Quotient.inductionOn L fun T =>
    ⟨_, _, _, CommData.Over.ofTuple T, CommData.Over.ofTuple T, rfl, rfl⟩

theorem Commensurable.symm {L₁ L₂ : StructuredMultisection A} (h : Commensurable L₁ L₂) :
    Commensurable L₂ L₁ := by
  obtain ⟨c, Λ₁, Λ₂, o₁, o₂, h₁, h₂⟩ := h
  exact ⟨c, Λ₂, Λ₁, o₂, o₁, h₂, h₁⟩

/-! ### The commensurable sum of a locally finite family (Definition 13.4.5 (2) and after) -/

/-- `μ(ψ, ∑ᶠⱼ vⱼ) = ∑ᶠⱼ μ(ψ, vⱼ)` for finitely many non-zero `vⱼ`. -/
theorem fibAct_finsum {J : Type*} {ψ : A.Mor} {y y' : A.Obj} (hy : A.X.src ψ = y)
    (hy' : A.X.tgt ψ = y') {f : J → A.P ⁻¹' {y}} {f' : J → A.P ⁻¹' {y'}}
    (hfin : (support f).Finite) (h : ∀ j, (f' j : A.W) = fibAct ψ (f j)) :
    fibAct ψ ((∑ᶠ j, f j : A.P ⁻¹' {y}) : A.W) = ((∑ᶠ j, f' j : A.P ⁻¹' {y'}) : A.W) := by
  subst hy hy'
  rw [fibAct_of (∑ᶠ j, f j).2]
  have e := A.E.fiberMor_apply ψ (∑ᶠ j, f j)
  rw [map_finsum _ hfin] at e
  refine e.symm.trans ?_
  congr 1
  refine finsum_congr fun j => Subtype.ext ?_
  rw [A.E.fiberMor_apply, h j, fibAct_of (f j).2]

namespace CommData

variable {c : CommData A} {J : Type*} {Λ : J → A.W → ℚ≥0}

/-- The fibre value `∑ᶠⱼ s^{j,x}ᵢ(y)` (the summands extended by `0` off `U(x)`). -/
def sumFib (o : ∀ j, c.Over (Λ j)) (x : A.Obj) (i : c.I x) (y : A.Obj) : A.P ⁻¹' {y} :=
  ∑ᶠ j, (⟨extendZero (c.𝒰.U x) ((o j).s x i) y, isSection_extendZero _ _ y⟩ : A.P ⁻¹' {y})

/-- **The sections `sˣᵢ = ∑ᶠⱼ s^{j,x}ᵢ`** of the commensurable sum. -/
def sumSec (o : ∀ j, c.Over (Λ j)) (x : A.Obj) (i : c.I x) (y : A.Obj) : A.W :=
  (sumFib o x i y : A.W)

theorem P_sumSec (o : ∀ j, c.Over (Λ j)) (x : A.Obj) (i : c.I x) (y : A.Obj) :
    A.P (sumSec o x i y) = y := (sumFib o x i y).2

/-- **Local finiteness**: near every point only finitely many summands of `sumSec` are non-zero
(the sections of a `Λⱼ` vanish where `Λⱼ` is trivial). -/
theorem exists_finite_support (o : ∀ j, c.Over (Λ j)) (hlf : IsLocallyFiniteFamily Λ)
    (y₀ : A.Obj) : ∃ O : Set A.Obj, IsOpen O ∧ y₀ ∈ O ∧ ∃ F : Finset J, ∀ j ∉ F, ∀ x (i : c.I x),
      ∀ y ∈ O, extendZero (c.𝒰.U x) ((o j).s x i) y = fiberZero A.P y := by
  obtain ⟨O, hO, -, hy₀, hfin⟩ := hlf y₀
  refine ⟨O, hO, hy₀, hfin.toFinset, fun j hj x i y hy => ?_⟩
  have hj' : j ∉ nontrivIdx Λ O := fun h => hj (hfin.mem_toFinset.2 h)
  by_cases hyx : y ∈ c.𝒰.U x
  · rw [← extendZero_eqOn ((o j).isScPlusSectionOn x i).1 hyx]
    refine (o j).s_eq_fiberZero hyx ?_ i
    have := trivial_of_not_mem_nontrivIdx (fun l => (o l).isScPlusMultisection) hy hj'
      (0 : A.P ⁻¹' {y})
    rw [if_pos rfl] at this
    exact this
  · unfold extendZero
    rw [if_neg fun h => hyx h.1]

theorem support_subset (o : ∀ j, c.Over (Λ j)) {O : Set A.Obj} {F : Finset J}
    (hF : ∀ j ∉ F, ∀ x (i : c.I x), ∀ y ∈ O,
      extendZero (c.𝒰.U x) ((o j).s x i) y = fiberZero A.P y)
    {x : A.Obj} (i : c.I x) {y : A.Obj} (hy : y ∈ O) :
    (support fun j => (⟨extendZero (c.𝒰.U x) ((o j).s x i) y, isSection_extendZero _ _ y⟩ :
      A.P ⁻¹' {y})) ⊆ F := by
  intro j hj
  by_contra hjF
  exact hj (Subtype.ext (hF j hjF x i y hy))

theorem sumSec_eq_sectionSum (o : ∀ j, c.Over (Λ j)) {O : Set A.Obj} {F : Finset J}
    (hF : ∀ j ∉ F, ∀ x (i : c.I x), ∀ y ∈ O,
      extendZero (c.𝒰.U x) ((o j).s x i) y = fiberZero A.P y)
    {x : A.Obj} (i : c.I x) {y : A.Obj} (hy : y ∈ O) :
    sumSec o x i y = sectionSum A.P F (fun j => extendZero (c.𝒰.U x) ((o j).s x i)) y := by
  rw [sectionSum_apply fun j => isSection_extendZero _ _, sumSec, sumFib,
    finsum_eq_sum_of_support_subset _ (support_subset o hF i hy)]

/-- **The sections of the commensurable sum are sections over `c`** (the symmetric structures
`sˣᵢ = ∑ᶠⱼ s^{j,x}ᵢ` with the common `τ`). -/
def lfSections (o : ∀ j, c.Over (Λ j)) (hlf : IsLocallyFiniteFamily Λ) : c.Sections where
  s := sumSec o
  isScPlusSectionOn x i := IsScPlusSectionOn.of_locally (c.𝒰.isOpen_U x) fun y hy => by
    obtain ⟨O, hO, hyO, F, hF⟩ := exists_finite_support o hlf y
    have h1 := isScPlusSectionOn_sectionSum F (c.𝒰.isOpen_U x)
      (fun j => ((o j).isScPlusSectionOn x i).extendZero) (fun j => isSection_extendZero _ _)
    exact ⟨O ∩ c.𝒰.U x, hO.inter (c.𝒰.isOpen_U x), ⟨hyO, hy⟩, inter_subset_right,
      (h1.mono (hO.inter (c.𝒰.isOpen_U x)) inter_subset_right).congr
        fun z hz => (sumSec_eq_sectionSum o hF i hz.1).symm⟩
  equivariant x g i y hy := by
    obtain ⟨O, -, hyO, F, hF⟩ := exists_finite_support o hlf y
    have hgy : (c.𝒰.nbhd x).rep.Φ g y ∈ c.𝒰.U x := (c.𝒰.nbhd x).Φ_mem g hy
    refine (fibAct_finsum ((c.𝒰.nbhd x).src_Γ g hy) ((c.𝒰.nbhd x).tgt_Γ g hy)
      (F.finite_toSet.subset (support_subset o hF i hyO)) fun j => ?_).symm
    change extendZero _ _ _ = fibAct _ (extendZero _ _ _)
    rw [← extendZero_eqOn ((o j).isScPlusSectionOn x _).1 hgy,
      ← extendZero_eqOn ((o j).isScPlusSectionOn x i).1 hy]
    exact (o j).equivariant x g i y hy
  compat x x' φ hφ := by
    refine IndexCorr.sat_mono (fun i i' H ψ hψ => ?_)
      (IndexCorr.sat_iInter fun j => (o j).compat x x' φ hφ)
    have hψ' := c.𝒰.comp_subset x x' φ hψ
    obtain ⟨O, -, hyO, F, hF⟩ := exists_finite_support o hlf (A.X.src ψ)
    refine (fibAct_finsum rfl rfl (F.finite_toSet.subset (support_subset o hF i hyO))
      fun j => ?_).symm
    change extendZero _ _ _ = fibAct _ (extendZero _ _ _)
    rw [← extendZero_eqOn ((o j).isScPlusSectionOn x' i').1 hψ'.2,
      ← extendZero_eqOn ((o j).isScPlusSectionOn x i).1 hψ'.1]
    exact H j ψ hψ

/-- **The commensurable sum `⊕^c_{j ∈ J} Λⱼ`** of a locally finite family over `c`: the functor
`Λ(w) = |I_x|⁻¹·#{i | sˣᵢ(P(w)) = w}` of the sections `sˣᵢ = ∑ᶠⱼ s^{j,x}ᵢ`. -/
def lfSum (o : ∀ j, c.Over (Λ j)) (hlf : IsLocallyFiniteFamily Λ) : A.W → ℚ≥0 :=
  c.sumMult (lfSections o hlf).s

/-- The data `(𝒰, S, τ)` of the commensurable sum. -/
def Over.lfSum (o : ∀ j, c.Over (Λ j)) (hlf : IsLocallyFiniteFamily Λ) :
    c.Over (CommData.lfSum o hlf) :=
  (lfSections o hlf).toOver

/-- **2021 Definition 13.4.5, the locally finite commensurable sum (p. 629)**: for a locally
finite family `(Λⱼ)_{j ∈ J}` of sc⁺-multisections with structures `[Λⱼ, 𝒰, Sⱼ, τ]` over a common
`c`, `Λ = ⊕^c_j Λⱼ` is an sc⁺-multisection, structured by `(𝒰, S, τ)` with the sections
`sˣᵢ = ∑ᶠⱼ s^{j,x}ᵢ` on `U(x)` and `Λ(w) = |I_x|⁻¹·#{i | sˣᵢ(P(w)) = w}` for `P(w) ∈ U(x)`. -/
theorem definition_13_4_5_lf (o : ∀ j, c.Over (Λ j)) (hlf : IsLocallyFiniteFamily Λ) :
    IsScPlusMultisection A (lfSum o hlf) ∧
      (∀ x (i : c.I x) y (hy : y ∈ c.𝒰.U x), (Over.lfSum o hlf).s x i y =
        ((∑ᶠ j, (⟨(o j).s x i y, ((o j).isScPlusSectionOn x i).1 y hy⟩ : A.P ⁻¹' {y}) :
          A.P ⁻¹' {y}) : A.W)) ∧
      ∀ x w, A.P w ∈ c.𝒰.U x → lfSum o hlf w =
        (Fintype.card (c.I x) : ℚ≥0)⁻¹ *
          ((Finset.univ.filter fun i => (Over.lfSum o hlf).s x i (A.P w) = w).card : ℚ≥0) := by
  refine ⟨(Over.lfSum o hlf).isScPlusMultisection, fun x i y hy => ?_,
    fun x w hw => (Over.lfSum o hlf).rep x w hw⟩
  change ((∑ᶠ j, _ : A.P ⁻¹' {y}) : A.W) = _
  congr 1
  exact finsum_congr fun j => Subtype.ext
    (extendZero_eqOn ((o j).isScPlusSectionOn x i).1 hy).symm

/-! ### Finite families and the binary sum -/

/-- A finite family is locally finite. -/
theorem isLocallyFiniteFamily_of_finite [Finite J] (Λ : J → A.W → ℚ≥0) :
    IsLocallyFiniteFamily Λ :=
  fun _ => ⟨univ, isOpen_univ, A.X.isSaturated_univ, mem_univ _, toFinite _⟩

/-- The pair `(Λ₁, Λ₂)` as a family over `Bool`. -/
def pairFam (Λ₁ Λ₂ : A.W → ℚ≥0) : Bool → A.W → ℚ≥0 := fun b => bif b then Λ₁ else Λ₂

/-- The pair of data over `c`. -/
def pairOver {Λ₁ Λ₂ : A.W → ℚ≥0} (o₁ : c.Over Λ₁) (o₂ : c.Over Λ₂) :
    ∀ b, c.Over (pairFam Λ₁ Λ₂ b)
  | true => o₁
  | false => o₂

/-- **2021 Definition 13.4.5 (2), p. 628**: the commensurable sum `Λ₁ ⊕_c Λ₂`. -/
def commSum₂ {Λ₁ Λ₂ : A.W → ℚ≥0} (o₁ : c.Over Λ₁) (o₂ : c.Over Λ₂) : A.W → ℚ≥0 :=
  lfSum (pairOver o₁ o₂) (isLocallyFiniteFamily_of_finite _)

/-- The data `(𝒰, S, τ)` of `Λ₁ ⊕_c Λ₂`. -/
def Over.commSum₂ {Λ₁ Λ₂ : A.W → ℚ≥0} (o₁ : c.Over Λ₁) (o₂ : c.Over Λ₂) :
    c.Over (CommData.commSum₂ o₁ o₂) :=
  Over.lfSum _ _

/-- **2021 Definition 13.4.5 (2), p. 628 (2017: Definition 13.22)**: for commensurable
`[Λ₁, 𝒰, S₁, τ]`, `[Λ₂, 𝒰, S₂, τ]` (data over a common `c`), the commensurable sum
`Λ = Λ₁ ⊕_c Λ₂` is an sc⁺-multisection structured by `(𝒰, S, τ)` with `sˣᵢ = s^{1,x}ᵢ + s^{2,x}ᵢ`
on `U(x)` and `Λ(w) = |I_x|⁻¹·#{i | sˣᵢ(P(w)) = w}` for `P(w) ∈ U(x)`. -/
theorem definition_13_4_5 {Λ₁ Λ₂ : A.W → ℚ≥0} (o₁ : c.Over Λ₁) (o₂ : c.Over Λ₂) :
    IsScPlusMultisection A (commSum₂ o₁ o₂) ∧
      (∀ x (i : c.I x) y (hy : y ∈ c.𝒰.U x), (Over.commSum₂ o₁ o₂).s x i y =
        (((⟨o₁.s x i y, (o₁.isScPlusSectionOn x i).1 y hy⟩ : A.P ⁻¹' {y}) +
          ⟨o₂.s x i y, (o₂.isScPlusSectionOn x i).1 y hy⟩ : A.P ⁻¹' {y}) : A.W)) ∧
      ∀ x w, A.P w ∈ c.𝒰.U x → commSum₂ o₁ o₂ w =
        (Fintype.card (c.I x) : ℚ≥0)⁻¹ *
          ((Finset.univ.filter fun i => (Over.commSum₂ o₁ o₂).s x i (A.P w) = w).card :
            ℚ≥0) := by
  obtain ⟨h1, h2, h3⟩ := definition_13_4_5_lf (pairOver o₁ o₂) (isLocallyFiniteFamily_of_finite _)
  refine ⟨h1, fun x i y hy => ?_, h3⟩
  rw [Over.commSum₂, h2 x i y hy, finsum_eq_sum_of_fintype, Fintype.sum_bool]
  rfl

end CommData

end SBLocalization

end Polyfold
