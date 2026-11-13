import Polyfold.Chapter13.P3M_MultisectionSymmetric
import Polyfold.Chapter13.P3M_MultisectionLocallyFinite
import Polyfold.Chapter13.P3G_GoodSystem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.2, pp. 610–612: **symmetric sc⁺-section structures on the neighbourhoods of a good system**,
the local material behind Definitions 13.2.7–13.2.10 and Lemmas 13.2.11, 13.2.13
(2017: Definitions 13.9–13.12, Lemmas 13.4, 13.5).

# Symmetric sc⁺-section structures on a `NatNbhd`

## The text, paraphrased

(Definition 13.2.5) A symmetric sc⁺-section structure for `Λ` on `U(x)`: finitely many
sc⁺-sections `(sᵢ)_{i ∈ I_x}` on `U(x)`, an action of `G_x` on `I_x` with
`s_{g(i)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))`, and `Λ(w) = |I_x|⁻¹·#{i | sᵢ(P(w)) = w}` over `U(x)`.
(Definitions 13.2.9, 13.2.10, Lemmas 13.2.11, 13.2.13) Sums carry the structures
`(s'_i + s''_j)_{(i, j) ∈ I'_x × I''_x}`, scalar multiples `(a·sᵢ)`, products with a functor
`(β·sᵢ)`, finite sums `(∑_j s^j_{i_j})_{(i_j) ∈ ∏_j I^j_x}`.

## What is formalized

* `EpGroupoid.NatNbhd.Le N' N`: `N' ⊆ N` with the same natural action (the same `Γ`, hence the
  same `Φ`, on `N'`).  `NatNbhd.exists_le_of_finite`: **finitely many neighbourhoods with the
  natural `G_x`-action have a common one** inside any open `V ∋ x`, with the action of a chosen
  one (through the uniqueness of the natural representation near `x`, `NaturalRep.Γ_eqOn`).
* `fibAct ψ v = μ(ψ, v)` and its additivity, homogeneity and value on `0`.
* `SymmetricStructureOn A Λ N`: Definition 13.2.5 on a neighbourhood `N : NatNbhd x` (the
  neighbourhoods of a good system; Agent M's `SymmetricStructure` uses the connected domain of a
  natural representation, and `SymmetricStructure.toOn` converts it).
* The constructions: `restrict` (to `N' ≤ N`), `add` (`I' × I''`, `s'_i + s''_j`), `pi` (finite
  products, `∑_j s^j_{i_j}`), `smul` (`a·sᵢ`), `smulFun` (`β·sᵢ`), `ofTrivial` (the single zero
  section where `Λ` is trivial), and `s_eq_fiberZero` (all sections vanish where `Λ(0_y) = 1`).

## Reading

The book does not say which natural action the intersection `U'(x) ∩ U''(x)` of Definition 13.2.9
(2) carries.  Two natural representations at `x` agree only on the connected component of `x` in
the intersection of their domains, so we use a common invariant neighbourhood inside
`U'(x) ∩ U''(x)` on which both actions agree (`exists_le_of_finite`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

namespace NatNbhd

variable {x : Obj}

/-- `N'` lies inside `N` and carries the same natural action: `N'.U ⊆ N.U` and the two
representations have the same `Γ(g, ·)` on `N'.U`. -/
structure Le (N' N : X.NatNbhd x) : Prop where
  subset : N'.U ⊆ N.U
  Γ_eq : ∀ g, ∀ y ∈ N'.U, N'.rep.Γ g y = N.rep.Γ g y

theorem Le.Φ_eq {N' N : X.NatNbhd x} (h : N'.Le N) (g : X.Isotropy x) {y : Obj}
    (hy : y ∈ N'.U) : N'.rep.Φ g y = N.rep.Φ g y := by
  rw [← N'.tgt_Γ g hy, h.Γ_eq g y hy, N.tgt_Γ g (h.subset hy)]

theorem Le.refl (N : X.NatNbhd x) : N.Le N := ⟨subset_rfl, fun _ _ _ => rfl⟩

theorem Le.trans {N'' N' N : X.NatNbhd x} (h₁ : N''.Le N') (h₂ : N'.Le N) : N''.Le N :=
  ⟨h₁.subset.trans h₂.subset, fun g y hy => (h₁.Γ_eq g y hy).trans (h₂.Γ_eq g y (h₁.subset hy))⟩

theorem le_of_rep_eq {N' N : X.NatNbhd x} (hrep : N'.rep = N.rep) (hsub : N'.U ⊆ N.U) :
    N'.Le N :=
  ⟨hsub, fun g y _ => by rw [hrep]⟩

/-- **Common neighbourhoods**: for `N₀` and finitely many `Nᵢ` (all with the natural
`G_x`-action) and an open `V ∋ x` there is `M` with the action of `N₀`, `M ⊆ V`, `M ≤ N₀` and
`M ≤ Nᵢ` for all `i`.  (Two natural representations agree on the component of `x` in the
intersection of their domains, `NaturalRep.Γ_eqOn`.) -/
theorem exists_le_of_finite {ι : Type*} [Finite ι] (N₀ : X.NatNbhd x) (N : ι → X.NatNbhd x)
    {V : Set Obj} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ M : X.NatNbhd x, M.rep = N₀.rep ∧ M.U ⊆ V ∧ M.Le N₀ ∧ ∀ i, M.Le (N i) := by
  set C : ι → Set Obj := fun i => connectedComponentIn (N₀.rep.U ∩ (N i).rep.U) x
  set V' := V ∩ ⋂ i, ((N i).U ∩ C i)
  have hV' : IsOpen V' := hV.inter (isOpen_iInter_of_finite fun i =>
    (N i).isOpen_U.inter (N₀.rep.isOpen_connectedComponentIn_inter (N i).rep))
  have hxV' : x ∈ V' :=
    ⟨hxV, mem_iInter.2 fun i => ⟨(N i).mem_U, N₀.rep.mem_connectedComponentIn_inter _⟩⟩
  obtain ⟨M, hrep, hsub⟩ := N₀.exists_restrict_subset hV' hxV'
  refine ⟨M, hrep, fun y hy => (hsub hy).2.1, le_of_rep_eq hrep fun y hy => (hsub hy).1,
    fun i => ⟨fun y hy => (mem_iInter.1 (hsub hy).2.2 i).1, fun g y hy => ?_⟩⟩
  rw [hrep]
  exact N₀.rep.Γ_eqOn (N i).rep g (mem_iInter.1 (hsub hy).2.2 i).2

end NatNbhd

end EpGroupoid

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### The fibre maps `μ(ψ, ·)` on points of `W` -/

/-- `μ(ψ, v)` for `P(v) = s(ψ)` (and `v` otherwise). -/
def fibAct (ψ : A.Mor) (v : A.W) : A.W :=
  if h : A.P v = A.X.src ψ then A.E.μ ⟨(ψ, v), h⟩ else v

theorem fibAct_of {ψ : A.Mor} {v : A.W} (h : A.P v = A.X.src ψ) :
    fibAct ψ v = A.E.μ ⟨(ψ, v), h⟩ := dif_pos h

theorem P_fibAct {ψ : A.Mor} {v : A.W} (h : A.P v = A.X.src ψ) :
    A.P (fibAct ψ v) = A.X.tgt ψ := by
  rw [fibAct_of h, A.E.P_μ]

/-- `μ(ψ, 0) = 0`. -/
theorem fibAct_fiberZero {ψ : A.Mor} {y y' : A.Obj} (hy : A.X.src ψ = y) (hy' : A.X.tgt ψ = y') :
    fibAct ψ (fiberZero A.P y) = fiberZero A.P y' := by
  subst hy hy'
  rw [fibAct_of (proj_fiberZero A.P _)]
  exact μ_fiberZero A ψ _

/-- `μ(ψ, f(y) + s(y)) = f'(y') + s'(y')` when `f'(y') = μ(ψ, f(y))` and `s'(y') = μ(ψ, s(y))`. -/
theorem fibAct_sectionAdd {f s f' s' : A.Obj → A.W} (hf : IsSection A.P f)
    (hs : IsSection A.P s) (hf' : IsSection A.P f') (hs' : IsSection A.P s') {ψ : A.Mor}
    {y y' : A.Obj} (hy : A.X.src ψ = y) (hy' : A.X.tgt ψ = y')
    (ef : f' y' = fibAct ψ (f y)) (es : s' y' = fibAct ψ (s y)) :
    fibAct ψ (sectionAdd A.P f s y) = sectionAdd A.P f' s' y' := by
  subst hy hy'
  rw [sectionAdd_apply hf hs, sectionAdd_apply hf' hs',
    fibAct_of ((⟨f _, hf _⟩ + ⟨s _, hs _⟩ : A.P ⁻¹' {A.X.src ψ})).2,
    A.E.μ_add ψ ⟨f _, hf _⟩ ⟨s _, hs _⟩]
  congr 2
  · exact Subtype.ext (ef.trans (fibAct_of (hf _))).symm
  · exact Subtype.ext (es.trans (fibAct_of (hs _))).symm

/-- `μ(ψ, c·f(y)) = c'·f'(y')` when `c = c'` and `f'(y') = μ(ψ, f(y))`. -/
theorem fibAct_sectionSmul {f f' : A.Obj → A.W} {c c' : A.Obj → ℝ} (hf : IsSection A.P f)
    (hf' : IsSection A.P f') {ψ : A.Mor} {y y' : A.Obj} (hy : A.X.src ψ = y)
    (hy' : A.X.tgt ψ = y') (hc : c' y' = c y) (ef : f' y' = fibAct ψ (f y)) :
    fibAct ψ (Polyfold.sectionSmul A.P c f y) = Polyfold.sectionSmul A.P c' f' y' := by
  subst hy hy'
  rw [sectionSmul_apply hf, sectionSmul_apply hf',
    fibAct_of ((c (A.X.src ψ) • ⟨f _, hf _⟩ : A.P ⁻¹' {A.X.src ψ})).2,
    A.E.μ_smul ψ _ ⟨f _, hf _⟩, hc]
  congr 2
  exact Subtype.ext (ef.trans (fibAct_of (hf _))).symm

/-- `μ(ψ, ∑ᵢ fᵢ(y)) = ∑ᵢ f'ᵢ(y')` when `f'ᵢ(y') = μ(ψ, fᵢ(y))`. -/
theorem fibAct_sectionSum {ι : Type*} (T : Finset ι) {f f' : ι → A.Obj → A.W}
    (hf : ∀ i, IsSection A.P (f i)) (hf' : ∀ i, IsSection A.P (f' i)) {ψ : A.Mor}
    {y y' : A.Obj} (hy : A.X.src ψ = y) (hy' : A.X.tgt ψ = y')
    (ef : ∀ i, f' i y' = fibAct ψ (f i y)) :
    fibAct ψ (sectionSum A.P T f y) = sectionSum A.P T f' y' := by
  subst hy hy'
  rw [sectionSum_apply hf, sectionSum_apply hf',
    fibAct_of ((∑ i ∈ T, ⟨f i _, hf i _⟩ : A.P ⁻¹' {A.X.src ψ})).2]
  have e := A.E.fiberMor_apply ψ (∑ i ∈ T, ⟨f i _, hf i _⟩)
  rw [map_sum] at e
  refine e.symm.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => Subtype.ext ?_
  rw [A.E.fiberMor_apply]
  exact (ef i |>.trans (fibAct_of (hf i _))).symm

/-! ### Counting forms of `Λ` -/

/-- The two forms of the counting formula of Definition 13.2.5 (2) over one fibre. -/
theorem count_eq_sum {I : Type*} [Fintype I] (s : I → A.Obj → A.W) {y : A.Obj}
    (hs : ∀ i, A.P (s i y) = y) (u : A.P ⁻¹' {y}) :
    (Fintype.card I : ℚ≥0)⁻¹ *
        ((Finset.univ.filter fun i => s i (A.P (u : A.W)) = u).card : ℚ≥0) =
      ∑ i, if u = (⟨s i y, hs i⟩ : A.P ⁻¹' {y}) then (Fintype.card I : ℚ≥0)⁻¹ else 0 := by
  have hP : A.P (u : A.W) = y := u.2
  rw [Finset.natCast_card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hP]
  by_cases h : s i y = u
  · rw [if_pos h, if_pos (Subtype.ext h.symm), mul_one]
  · rw [if_neg h, if_neg fun e => h (congrArg Subtype.val e).symm, mul_zero]

/-! ### Symmetric structures on a neighbourhood with the natural action -/

/-- **Definition 13.2.5 (p. 610) on a neighbourhood `N` with the natural `G_x`-action**: a finite
index type `I` with a `G_x`-action and sc⁺-sections `(sᵢ)` on `N.U` with
(1) `s_{g(i)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))` and (2) `Λ(w) = |I|⁻¹·#{i | sᵢ(P(w)) = w}` over `N.U`.
(The properness of `t` on `s⁻¹(cl U(x))` is part of the good system, Definition 13.1.2 (1).) -/
structure SymmetricStructureOn (A : SEP.{u}) (Λ : A.W → ℚ≥0) {x : A.Obj}
    (N : A.X.NatNbhd x) where
  /-- The index set `I_x`. -/
  I : Type u
  [fintype : Fintype I]
  [mulAction : MulAction (A.X.Isotropy x) I]
  /-- The sections `sᵢ`. -/
  s : I → A.Obj → A.W
  isScPlusSectionOn : ∀ i, IsScPlusSectionOn A (s i) N.U
  /-- (1) `s_{g(i)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))`. -/
  equivariant : ∀ (g : A.X.Isotropy x) (i : I), ∀ y ∈ N.U,
    s (g • i) (N.rep.Φ g y) = fibAct (N.rep.Γ g y) (s i y)
  /-- (2) `Λ(w) = |I|⁻¹·#{i | sᵢ(P(w)) = w}`. -/
  rep : ∀ w, A.P w ∈ N.U →
    Λ w = (Fintype.card I : ℚ≥0)⁻¹ * ((Finset.univ.filter fun i => s i (A.P w) = w).card : ℚ≥0)

attribute [instance] SymmetricStructureOn.fintype SymmetricStructureOn.mulAction

namespace SymmetricStructureOn

variable {Λ : A.W → ℚ≥0} {x : A.Obj} {N : A.X.NatNbhd x}

theorem P_s (S : SymmetricStructureOn A Λ N) (i : S.I) {y : A.Obj} (hy : y ∈ N.U) :
    A.P (S.s i y) = y := (S.isScPlusSectionOn i).1 y hy

/-- `Λ` over the fibre `W_y`, `y ∈ U`: `Λ(u) = ∑ᵢ [u = sᵢ(y)]·|I|⁻¹`. -/
theorem apply_fib (S : SymmetricStructureOn A Λ N) {y : A.Obj} (hy : y ∈ N.U)
    (u : A.P ⁻¹' {y}) :
    Λ u = ∑ i, if u = (⟨S.s i y, S.P_s i hy⟩ : A.P ⁻¹' {y}) then (Fintype.card S.I : ℚ≥0)⁻¹
      else 0 := by
  have hP : A.P (u : A.W) = y := u.2
  rw [S.rep u (by rw [hP]; exact hy)]
  exact count_eq_sum S.s (fun i => S.P_s i hy) u

/-- The counting formula from its fibre form. -/
theorem rep_of_apply_fib {Λ : A.W → ℚ≥0} {U : Set A.Obj} {I : Type*} [Fintype I]
    {s : I → A.Obj → A.W} (hs : ∀ i, ∀ y ∈ U, A.P (s i y) = y)
    (h : ∀ y (hy : y ∈ U) (u : A.P ⁻¹' {y}),
      Λ u = ∑ i, if u = (⟨s i y, hs i y hy⟩ : A.P ⁻¹' {y}) then (Fintype.card I : ℚ≥0)⁻¹
        else 0) :
    ∀ w, A.P w ∈ U →
      Λ w = (Fintype.card I : ℚ≥0)⁻¹ *
        ((Finset.univ.filter fun i => s i (A.P w) = w).card : ℚ≥0) := fun w hw => by
  have e := h (A.P w) hw ⟨w, rfl⟩
  rw [← count_eq_sum s (fun i => hs i _ hw) ⟨w, rfl⟩] at e
  exact e

/-- The index set of a symmetric structure of an sc⁺-multisection is not empty. -/
theorem card_pos (S : SymmetricStructureOn A Λ N) (hΛ : IsScPlusMultisection A Λ) :
    0 < Fintype.card S.I := by
  by_contra h0
  have h0' : Fintype.card S.I = 0 := Nat.eq_zero_of_not_pos h0
  obtain ⟨w, hw, hpos⟩ := hΛ.suppAt_nonempty x
  rw [S.rep w (hw ▸ N.mem_U), h0', Nat.cast_zero, inv_zero, zero_mul] at hpos
  exact lt_irrefl _ hpos

theorem sum_inv_card (S : SymmetricStructureOn A Λ N) (hΛ : IsScPlusMultisection A Λ) :
    ∑ _i : S.I, (Fintype.card S.I : ℚ≥0)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 (S.card_pos hΛ).ne')

/-- **Where `Λ(0_y) = 1`, all sections of a symmetric structure vanish** (`sᵢ(y)` has weight at
least `|I|⁻¹ > 0`, and `Λ = 0` off the zero over `y`). -/
theorem s_eq_fiberZero (S : SymmetricStructureOn A Λ N) (hΛ : IsScPlusMultisection A Λ)
    {y : A.Obj} (hy : y ∈ N.U) (h1 : Λ (fiberZero A.P y) = 1) (i : S.I) :
    S.s i y = fiberZero A.P y := by
  by_contra hne
  have h0 := (hΛ.apply_fiberZero_eq_one_iff y).1 h1 (S.s i y) (S.P_s i hy) hne
  rw [S.rep _ ((S.P_s i hy).symm ▸ hy)] at h0
  have hc : (Fintype.card S.I : ℚ≥0)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 (S.card_pos hΛ).ne')
  have hk : ((Finset.univ.filter fun j => S.s j (A.P (S.s i y)) = S.s i y).card : ℚ≥0) ≠ 0 := by
    refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, ?_⟩)
    rw [Finset.mem_filter, S.P_s i hy]
    exact ⟨Finset.mem_univ _, rfl⟩
  exact mul_ne_zero hc hk h0

/-! #### Restriction -/

/-- **Restriction** of a symmetric structure to a smaller neighbourhood with the same action. -/
def restrict (S : SymmetricStructureOn A Λ N) {N' : A.X.NatNbhd x} (h : N'.Le N) :
    SymmetricStructureOn A Λ N' where
  I := S.I
  s := S.s
  isScPlusSectionOn i := (S.isScPlusSectionOn i).mono N'.isOpen_U h.subset
  equivariant g i y hy := by
    rw [h.Φ_eq g hy, h.Γ_eq g y hy]
    exact S.equivariant g i y (h.subset hy)
  rep w hw := S.rep w (h.subset hw)

@[simp] theorem restrict_I (S : SymmetricStructureOn A Λ N) {N' : A.X.NatNbhd x}
    (h : N'.Le N) : (S.restrict h).I = S.I := rfl

@[simp] theorem restrict_s (S : SymmetricStructureOn A Λ N) {N' : A.X.NatNbhd x}
    (h : N'.Le N) : (S.restrict h).s = S.s := rfl

/-- Two symmetric structures for `Λ` on the same neighbourhood are equivalent (Definition 13.2.8
at one point) if there is a `G_x`-equivariant bijection of the index sets matching the sections
on a smaller neighbourhood `V ∋ x`. -/
def EquivOn (S S' : SymmetricStructureOn A Λ N) (V : Set A.Obj) : Prop :=
  ∃ b : S.I ≃ S'.I, (∀ (g : A.X.Isotropy x) i, b (g • i) = g • b i) ∧
    ∀ i, ∀ y ∈ V, S'.s (b i) y = S.s i y

end SymmetricStructureOn

/-! ### Agent M's structures as structures on a `NatNbhd` -/

/-- A symmetric structure in the sense of `SymmetricStructure` (on the domain of a natural
representation) is one on the corresponding `NatNbhd`. -/
def SymmetricStructure.toOn {Λ : A.W → ℚ≥0} {x : A.Obj} (S : SymmetricStructure A Λ x) :
    SymmetricStructureOn A Λ (NatNbhd.ofRep S.R) where
  I := S.I
  s := S.s
  isScPlusSectionOn := S.isScPlusSectionOn
  equivariant g i y hy := (S.equivariant g i y hy).trans (fibAct_of _).symm
  rep := S.rep

/-- **Lemma 13.2.6 on a `NatNbhd`**: every sc⁺-multisection has, at every `x`, a symmetric
structure on some neighbourhood with the natural `G_x`-action. -/
theorem exists_symmetricStructureOn {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (x : A.Obj) : ∃ N : A.X.NatNbhd x, Nonempty (SymmetricStructureOn A Λ N) :=
  let S := (lemma_13_2_6 hΛ x).some
  ⟨NatNbhd.ofRep S.R, ⟨S.toOn⟩⟩

namespace SymmetricStructureOn

variable {x : A.Obj} {N : A.X.NatNbhd x}

/-! #### The sum (Definition 13.2.9 (3)) -/

theorem extendZero_apply_of {U : Set A.Obj} {s₁ : A.Obj → A.W} {y : A.Obj} (hy : y ∈ U)
    (h : A.P (s₁ y) = y) : extendZero U s₁ y = s₁ y := by
  unfold extendZero; rw [if_pos ⟨hy, h⟩]

/-- The section `s'_i + s''_j` (the summands extended by `0` off `U`). -/
def addSection (U : Set A.Obj) (s₁ s₂ : A.Obj → A.W) : A.Obj → A.W :=
  sectionAdd A.P (extendZero U s₁) (extendZero U s₂)

theorem addSection_apply {U : Set A.Obj} {s₁ s₂ : A.Obj → A.W} {y : A.Obj} (hy : y ∈ U)
    (h₁ : A.P (s₁ y) = y) (h₂ : A.P (s₂ y) = y) :
    addSection U s₁ s₂ y = ((⟨s₁ y, h₁⟩ + ⟨s₂ y, h₂⟩ : A.P ⁻¹' {y}) : A.W) := by
  rw [addSection, sectionAdd_apply (isSection_extendZero U s₁) (isSection_extendZero U s₂)]
  congr 2
  · exact Subtype.ext (extendZero_apply_of hy h₁)
  · exact Subtype.ext (extendZero_apply_of hy h₂)

/-- **Definition 13.2.9 (3), at one point**: symmetric structures `(s'_i)` for `Λ'` and `(s''_j)`
for `Λ''` on the same neighbourhood give the symmetric structure `(s'_i + s''_j)` on
`I' × I''` (with the diagonal action `g(i, j) = (g(i), g(j))`) for `Λ' ⊕ Λ''`. -/
def add {Λ' Λ'' : A.W → ℚ≥0} (S' : SymmetricStructureOn A Λ' N)
    (S'' : SymmetricStructureOn A Λ'' N) :
    SymmetricStructureOn A (multisectionAdd Λ' Λ'') N where
  I := S'.I × S''.I
  s κ := addSection N.U (S'.s κ.1) (S''.s κ.2)
  isScPlusSectionOn κ := IsScPlusSectionOn.sectionAdd N.isOpen_U
    (S'.isScPlusSectionOn κ.1).extendZero (S''.isScPlusSectionOn κ.2).extendZero
    (isSection_extendZero _ _) (isSection_extendZero _ _)
  equivariant g κ y hy := by
    have hgy : N.rep.Φ g y ∈ N.U := N.Φ_mem g hy
    refine (fibAct_sectionAdd (isSection_extendZero _ _) (isSection_extendZero _ _)
      (isSection_extendZero _ _) (isSection_extendZero _ _) (N.src_Γ g hy) (N.tgt_Γ g hy)
      ?_ ?_).symm
    · rw [← extendZero_eqOn (S'.isScPlusSectionOn _).1 hgy,
        ← extendZero_eqOn (S'.isScPlusSectionOn _).1 hy]
      exact S'.equivariant g κ.1 y hy
    · rw [← extendZero_eqOn (S''.isScPlusSectionOn _).1 hgy,
        ← extendZero_eqOn (S''.isScPlusSectionOn _).1 hy]
      exact S''.equivariant g κ.2 y hy
  rep := rep_of_apply_fib (fun κ y hy => by
      rw [addSection_apply hy (S'.P_s κ.1 hy) (S''.P_s κ.2 hy)]
      exact (_ : A.P ⁻¹' {y}).2) fun y hy u => by
    rw [multisectionAdd_fib_rep _ _ _ _ (S'.apply_fib hy) (S''.apply_fib hy) u,
      Fintype.card_prod, Nat.cast_mul, mul_inv]
    refine Finset.sum_congr rfl fun κ _ => if_congr ?_ rfl rfl
    constructor
    · intro e; rw [e]; exact Subtype.ext (addSection_apply hy _ _).symm
    · intro e; rw [e]; exact Subtype.ext (addSection_apply hy _ _)

@[simp] theorem add_I {Λ' Λ'' : A.W → ℚ≥0} (S' : SymmetricStructureOn A Λ' N)
    (S'' : SymmetricStructureOn A Λ'' N) : (S'.add S'').I = (S'.I × S''.I) := rfl

/-! #### Scalar multiples (Definition 13.2.10) -/

/-- The section `a·sᵢ` (extended by `0` off `U`). -/
def smulSection (U : Set A.Obj) (c : A.Obj → ℝ) (s₁ : A.Obj → A.W) : A.Obj → A.W :=
  Polyfold.sectionSmul A.P c (extendZero U s₁)

theorem smulSection_apply {U : Set A.Obj} {c : A.Obj → ℝ} {s₁ : A.Obj → A.W} {y : A.Obj}
    (hy : y ∈ U) (h₁ : A.P (s₁ y) = y) :
    smulSection U c s₁ y = ((c y • ⟨s₁ y, h₁⟩ : A.P ⁻¹' {y}) : A.W) := by
  rw [smulSection, sectionSmul_apply (isSection_extendZero U s₁)]
  congr 2
  exact Subtype.ext (extendZero_apply_of hy h₁)

/-- **Lemma 13.2.11, at one point** (and Definition 13.2.10 for constant `c`): for a function `c`
invariant along the morphisms `Γ(g, y)` and sc-smooth, `(c·sᵢ)` is a symmetric structure for
`(c(P(w))·Λ)(w)`. -/
def smulFun {Λ : A.W → ℚ≥0} (S : SymmetricStructureOn A Λ N) (hΛ : IsScPlusMultisection A Λ)
    {β : A.Obj → ℝ} (hβ : ∀ φ : A.Mor, β (A.X.tgt φ) = β (A.X.src φ))
    (hβs : A.X.PObj.IsScSmoothMap realPolyfold β) :
    SymmetricStructureOn A (multisectionSmulFun β Λ) N where
  I := S.I
  s i := smulSection N.U β (S.s i)
  isScPlusSectionOn i := IsScPlusSectionOn.sectionSmul N.isOpen_U
    (S.isScPlusSectionOn i).extendZero (isSection_extendZero _ _) hβs
  equivariant g i y hy := by
    have hgy : N.rep.Φ g y ∈ N.U := N.Φ_mem g hy
    refine (fibAct_sectionSmul (isSection_extendZero _ _) (isSection_extendZero _ _)
      (N.src_Γ g hy) (N.tgt_Γ g hy) ?_ ?_).symm
    · rw [← N.tgt_Γ g hy, hβ, N.src_Γ g hy]
    · rw [← extendZero_eqOn (S.isScPlusSectionOn _).1 hgy,
        ← extendZero_eqOn (S.isScPlusSectionOn _).1 hy]
      exact S.equivariant g i y hy
  rep := rep_of_apply_fib (fun i y hy => by
      rw [smulSection_apply hy (S.P_s i hy)]
      exact (_ : A.P ⁻¹' {y}).2) fun y hy u => by
    have hP : A.P (u : A.W) = y := u.2
    change multisectionSmul (β (A.P (u : A.W))) Λ u = _
    rw [multisectionSmul_fib, hP, smulAt_eq_sum _ _ (S.sum_inv_card hΛ) (S.apply_fib hy)]
    refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
    constructor
    · intro e; rw [e]; exact Subtype.ext (smulSection_apply hy _).symm
    · intro e; rw [e]; exact Subtype.ext (smulSection_apply hy _)

/-- **Definition 13.2.10, at one point**: `(a·sᵢ)` is a symmetric structure for `aΛ`. -/
def smul {Λ : A.W → ℚ≥0} (S : SymmetricStructureOn A Λ N) (hΛ : IsScPlusMultisection A Λ)
    (a : ℝ) : SymmetricStructureOn A (multisectionSmul a Λ) N :=
  (S.smulFun hΛ (β := fun _ => a) (fun _ => rfl) (isScSmoothMap_real_const a) :
    SymmetricStructureOn A (multisectionSmulFun (fun _ => a) Λ) N)

/-! #### Finite sums (Lemma 13.2.13) -/

/-- The section `∑_j s^j_{κ_j}` (the summands extended by `0` off `U`). -/
def sumSection {ι : Type*} [Fintype ι] (U : Set A.Obj) (s : ι → A.Obj → A.W) :
    A.Obj → A.W :=
  sectionSum A.P Finset.univ fun i => extendZero U (s i)

theorem sumSection_apply {ι : Type*} [Fintype ι] {U : Set A.Obj} {s : ι → A.Obj → A.W}
    {y : A.Obj} (hy : y ∈ U) (h : ∀ i, A.P (s i y) = y) :
    sumSection U s y = ((∑ i, (⟨s i y, h i⟩ : A.P ⁻¹' {y}) : A.P ⁻¹' {y}) : A.W) := by
  rw [sumSection, sectionSum_apply fun i => isSection_extendZero U (s i)]
  congr 2
  exact funext fun i => Subtype.ext (extendZero_apply_of hy (h i))

/-- **Lemma 13.2.13, at one point** (finite sums): symmetric structures `S j` for `Λ_j` on the
same neighbourhood give the symmetric structure `(∑_j s^j_{κ_j})_{κ ∈ ∏_j I^j}` (with the
diagonal action) for the convolution `⊕_j Λ_j`. -/
def pi {ι : Type} [Fintype ι] {Λ : ι → A.W → ℚ≥0}
    (S : ∀ j, SymmetricStructureOn A (Λ j) N) : SymmetricStructureOn A (conv Λ) N where
  I := ∀ j, (S j).I
  s κ := sumSection N.U fun j => (S j).s (κ j)
  isScPlusSectionOn κ := isScPlusSectionOn_sectionSum _ N.isOpen_U
    (fun j => ((S j).isScPlusSectionOn (κ j)).extendZero) fun j => isSection_extendZero _ _
  equivariant g κ y hy := by
    have hgy : N.rep.Φ g y ∈ N.U := N.Φ_mem g hy
    refine (fibAct_sectionSum _ (fun j => isSection_extendZero _ _)
      (fun j => isSection_extendZero _ _) (N.src_Γ g hy) (N.tgt_Γ g hy) fun j => ?_).symm
    rw [← extendZero_eqOn ((S j).isScPlusSectionOn _).1 hgy,
      ← extendZero_eqOn ((S j).isScPlusSectionOn _).1 hy]
    exact (S j).equivariant g (κ j) y hy
  rep := rep_of_apply_fib (fun κ y hy => by
      rw [sumSection_apply hy fun j => (S j).P_s (κ j) hy]
      exact (_ : A.P ⁻¹' {y}).2) fun y hy u => by
    rw [conv_eq_convAt Λ u.2, convAt_eq_sum _ _ (fun j => (S j).apply_fib hy)]
    rw [Fintype.card_pi, Nat.cast_prod, ← Finset.prod_inv_distrib]
    refine Finset.sum_congr rfl fun κ _ => if_congr ?_ rfl rfl
    constructor
    · intro e; exact Subtype.ext ((sumSection_apply hy _).trans e).symm
    · intro e; rw [e]; exact (sumSection_apply hy _).symm

/-! #### The zero section where `Λ` is trivial -/

/-- **The trivial structure** (Proposition 13.3.15 (1)): where `Λ(0_y) = 1` on `U`, the single zero
section with weight `1` is a symmetric structure for `Λ`. -/
def ofTrivial {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (htriv : IsTrivialOn Λ N.U) :
    SymmetricStructureOn A Λ N where
  I := PUnit
  mulAction := { smul := fun _ i => i, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl }
  s _ := fiberZero A.P
  isScPlusSectionOn _ := isScPlusSectionOn_fiberZero N.isOpen_U
  equivariant g _ y hy :=
    (fibAct_fiberZero (N.src_Γ g hy) (N.tgt_Γ g hy)).symm
  rep w hw := by
    rw [Fintype.card_punit, Nat.cast_one, inv_one, one_mul]
    by_cases h0 : w = fiberZero A.P (A.P w)
    · have hc : (Finset.univ.filter fun _ : PUnit => fiberZero A.P (A.P w) = w) = Finset.univ :=
        Finset.filter_true_of_mem fun _ _ => h0.symm
      rw [hc, Finset.card_univ, Fintype.card_punit, Nat.cast_one, h0]
      exact htriv _ hw
    · have hc : (Finset.univ.filter fun _ : PUnit => fiberZero A.P (A.P w) = w) = ∅ :=
        Finset.filter_false_of_mem fun _ _ e => h0 e.symm
      rw [hc, Finset.card_empty, Nat.cast_zero]
      exact (hΛ.apply_fiberZero_eq_one_iff _).1 (htriv _ hw) w rfl h0

end SymmetricStructureOn

end SBLocalization

end Polyfold
