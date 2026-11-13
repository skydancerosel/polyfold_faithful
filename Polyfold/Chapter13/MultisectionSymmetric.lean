import Polyfold.Chapter13.MultisectionSupport

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.2, **Definition 13.2.5** and **Lemma 13.2.6** (pp. 609–610; 2017: Definition 13.5,
Lemma 13.6).

# Symmetric sc⁺-section structures

## The text, paraphrased

(pp. 609–610) Given a local section structure `(s_j, σ_j)` on `U(x)`, write `σ_j = k_j·q/p` and
replace `s_j` by `q·k_j` copies of weight `1/p`; then `Λ(w) = |I|⁻¹·#{i | sᵢ(P(w)) = w}`.  With
`Î = I × G_x` and `s_{(i,g)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))`, and `G_x` acting by `g(i, h) = (i, gh)`,
the family satisfies `s_{g(i)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))`.
(Definition 13.2.5) A symmetric sc⁺-section structure for `Λ` on `U(x)`: a `G_x`-invariant open
`U(x)` with `t : s⁻¹(cl U(x)) → X` proper, finitely many sc⁺-sections `(sᵢ)_{i ∈ I_x}` on `U(x)`
and an action of `G_x` on `I_x` with (1) `s_{g(i)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))`,
(2) `Λ(w) = |I_x|⁻¹·#{i | sᵢ(P(w)) = w}` over `U(x)`.
(Lemma 13.2.6) Every sc⁺-multisection admits locally a symmetric sc⁺-section structure.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `transportSection`, `isScPlusSectionOn_transportSection`: `z ↦ μ(τ(z), b(z))` is an
  sc⁺-section on `U` when `τ` is sc-smooth into the morphisms and `b` is sc-smooth into `W[1]`
  (the sections `s_{(i,g)}`).
* `IsLocalRepOn.exists_equal_weights`: the first step (equal weights `1/p`).
* **`SymmetricStructure`** (Definition 13.2.5): `U(x)` is the domain of a natural representation
  (as in `HasLocalSectionStructure`) with the properness property; the index type is a finite type
  with an action of `G_x`.
* **`lemma_13_2_6`**: every sc⁺-multisection has a symmetric sc⁺-section structure around every
  point, by the text's construction.
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

/-! ### Sections transported by morphisms -/

/-- The section `z ↦ μ(τ(z), b(z))` (with the zero section where `P(b(z)) ≠ s(τ(z))`). -/
def transportSection (τ : A.Obj → A.Mor) (b : A.Obj → A.W) (z : A.Obj) : A.W :=
  if h : A.P (b z) = A.X.src (τ z) then A.E.μ ⟨(τ z, b z), h⟩ else fiberZero A.P z

theorem transportSection_of_mem {τ : A.Obj → A.Mor} {b : A.Obj → A.W} {z : A.Obj}
    (h : A.P (b z) = A.X.src (τ z)) : transportSection τ b z = A.E.μ ⟨(τ z, b z), h⟩ := by
  unfold transportSection; rw [dif_pos h]

/-- **`z ↦ μ(τ(z), b(z))` is an sc⁺-section on `U`** if `τ : U → 𝐗` is sc-smooth with
`t(τ(z)) = z`, and `b` is sc-smooth into `W[1]` with `P(b(z)) = s(τ(z))` (on the level `[1]` the
section is `μ[1] ∘ (τ, b[1])`, as in the proof of `exists_isLocalRepOn_pushMult`). -/
theorem isScPlusSectionOn_transportSection {U : Set A.Obj} {τ : A.Obj → A.Mor}
    {b : A.Obj → A.W} (hτ : A.X.PObj.IsScSmoothOn A.X.PMor τ U) {G : A.Obj → A.B.One}
    (hG : ∀ z ∈ U, A.B.oneVal (G z) = b z) (hGs : A.X.PObj.IsScSmoothOn A.B.toMPolyfold1 G U)
    (hsrc : ∀ z ∈ U, A.P (b z) = A.X.src (τ z)) (htgt : ∀ z ∈ U, A.X.tgt (τ z) = z) :
    IsScPlusSectionOn A (transportSection τ b) U := by
  let ι : A.Obj → pullbackSpace A.P A.X.src := fun z =>
    if hz : A.P (A.B.oneVal (G z)) = A.X.src (τ z) then ⟨(τ z, A.B.oneVal (G z)), hz⟩
    else ⟨(A.X.unit (A.P (A.B.oneVal (G z))), A.B.oneVal (G z)), (A.X.src_unit _).symm⟩
  have hPG : ∀ z ∈ U, A.P (A.B.oneVal (G z)) = A.X.src (τ z) := fun z hz => by
    rw [hG z hz]; exact hsrc z hz
  have hι : ∀ z (hz : z ∈ U), ι z = ⟨(τ z, A.B.oneVal (G z)), hPG z hz⟩ := fun z hz =>
    dif_pos (hPG z hz)
  have hι2 : ∀ z, (ι z : A.Mor × A.W).2 = A.B.oneVal (G z) := fun z => by
    dsimp only [ι]; split_ifs <;> rfl
  have hι1 : ∀ z, ι z ∈ (A.B.pullback A.X.isScSmoothMap_src).oneSet := fun z =>
    (A.B.mem_oneSet_pullback_iff A.X.isScSmoothMap_src _).2 (by rw [hι2]; exact A.B.oneVal_mem _)
  let ι₁ : A.Obj → (A.B.pullback A.X.isScSmoothMap_src).One := fun z =>
    (A.B.pullback A.X.isScSmoothMap_src).oneMk (ι z) (hι1 z)
  have hsm : A.X.PObj.IsScSmoothOn A.B.toMPolyfold1
      (oneRestrict _ A.B A.E.μ A.E.isStrongBundleMap.mapsTo_oneSet ∘ ι₁) U := by
    have ha : A.X.PObj.IsScSmoothOn A.X.PMor
        (pullbackProj A.P A.X.src ∘ (A.B.pullback A.X.isScSmoothMap_src).oneVal ∘ ι₁) U :=
      hτ.congr fun z hz => by
        change τ z = (ι z : A.Mor × A.W).1
        rw [hι z hz]
    have hb1 : A.X.PObj.IsScSmoothOn A.B.toMPolyfold1
        (A.B.pullbackProj'One A.X.isScSmoothMap_src ∘ ι₁) U :=
      hGs.congr fun z _ => A.B.oneVal_injective (by
        change A.B.oneVal (G z) = (ι z : A.Mor × A.W).2
        rw [hι2])
    exact MPolyfold.IsScSmoothOn.comp A.E.isStrongBundleMap.isScSmoothMap_one
      (A.B.isScSmoothOn_to_pullback_one A.X.isScSmoothMap_src ha hb1) (mapsTo_univ _ _)
  refine ⟨fun z hz => ?_, _, fun z hz => ?_, hsm⟩
  · rw [transportSection_of_mem (hsrc z hz), A.E.P_μ]; exact htgt z hz
  · change A.E.μ (ι z) = transportSection τ b z
    rw [transportSection_of_mem (hsrc z hz), hι z hz]
    exact A.E.μ_congr (Prod.ext rfl (hG z hz))

/-! ### Equal weights -/

/-- **p. 609, the first step**: a local representation can be replaced by one with equal weights
`1/p` (each `s_j` repeated `p·σ_j` times), so that `Λ(w) = |I|⁻¹·#{i | sᵢ(P(w)) = w}`. -/
theorem IsLocalRepOn.exists_equal_weights {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ) :
    ∃ (I₁ : Type u) (_ : Fintype I₁) (c : I₁ → Fin k), 0 < Fintype.card I₁ ∧ ∀ w, A.P w ∈ O →
      Λ w = (Fintype.card I₁ : ℚ≥0)⁻¹ *
        ((Finset.univ.filter fun j : I₁ => s (c j) (A.P w) = w).card : ℚ≥0) := by
  set p : ℕ := ∏ i, (σ i).den with hp
  have hp0 : (p : ℚ≥0) ≠ 0 := by
    rw [hp, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (σ i).den_pos.ne'
  set n : Fin k → ℕ := fun i => (σ i).num * ∏ j ∈ Finset.univ.erase i, (σ j).den with hn
  have hσn : ∀ i, (n i : ℚ≥0) = σ i * p := fun i => by
    have hd : ((σ i).den : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.2 (σ i).den_pos.ne'
    have hnum : ((σ i).num : ℚ≥0) = σ i * (σ i).den := (div_eq_iff hd).1 (σ i).num_div_den
    rw [hn, hp, ← Finset.mul_prod_erase Finset.univ (fun j => (σ j).den) (Finset.mem_univ i)]
    push_cast
    rw [hnum, mul_assoc]
  have hcard : (Fintype.card (ULift.{u} (Σ i, Fin (n i))) : ℚ≥0) = p := by
    rw [Fintype.card_ulift, Fintype.card_sigma, Nat.cast_sum]
    simp only [Fintype.card_fin, hσn, ← Finset.sum_mul, h.2.2.1, one_mul]
  refine ⟨ULift.{u} (Σ i, Fin (n i)), inferInstance, fun j => j.down.1, ?_, fun w hw => ?_⟩
  · have : (Fintype.card (ULift.{u} (Σ i, Fin (n i))) : ℚ≥0) ≠ 0 := by rw [hcard]; exact hp0
    exact Nat.pos_of_ne_zero fun e => this (by rw [e, Nat.cast_zero])
  rw [hcard, Finset.natCast_card_filter]
  beta_reduce
  rw [Fintype.sum_equiv Equiv.ulift
    (fun j : ULift.{u} (Σ i, Fin (n i)) => if s j.down.1 (A.P w) = w then (1 : ℚ≥0) else 0)
    (fun j : Σ i, Fin (n i) => if s j.1 (A.P w) = w then (1 : ℚ≥0) else 0) fun _ => rfl,
    Fintype.sum_sigma, h.2.2.2 w hw, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : w = s i (A.P w)
  · have hi' : s i (A.P w) = w := hi.symm
    rw [if_pos hi]
    simp only [hi', ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    rw [hσn, mul_comm (σ i), ← mul_assoc, inv_mul_cancel₀ hp0, one_mul]
  · have hi' : ¬ s i (A.P w) = w := fun e => hi e.symm
    rw [if_neg hi]
    simp only [hi', ↓reduceIte, Finset.sum_const_zero, mul_zero]

/-! ### Definition 13.2.5 -/

/-- **2021 Definition 13.2.5, p. 610 (2017: Definition 13.5)**: a symmetric sc⁺-section
structure for `Λ` on `U(x)`: the domain `U(x)` of a natural representation of `G_x` (the natural
action of `G_x`, as in Definition 13.2.1) with `t : s⁻¹(cl U(x)) → X` proper, a finite index type
`I_x` with an action of `G_x`, and sc⁺-sections `(sᵢ)` on `U(x)` with
(1) `s_{g(i)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))` for `y ∈ U(x)`, and
(2) `Λ(w) = |I_x|⁻¹·#{i | sᵢ(P(w)) = w}` for `P(w) ∈ U(x)`. -/
structure SymmetricStructure (A : SEP.{u}) (Λ : A.W → ℚ≥0) (x : A.Obj) where
  /-- The neighbourhood `U(x)` with the natural action of `G_x`. -/
  R : A.X.NaturalRep x
  /-- `t : s⁻¹(cl_X U(x)) → X` is proper. -/
  hasPropernessProperty : A.X.HasPropernessProperty R.U
  /-- The index set `I_x`. -/
  I : Type u
  [fintype : Fintype I]
  [mulAction : MulAction (A.X.Isotropy x) I]
  /-- The sections `sᵢ`. -/
  s : I → A.Obj → A.W
  isScPlusSectionOn : ∀ i, IsScPlusSectionOn A (s i) R.U
  /-- (1) `s_{g(i)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))`. -/
  equivariant : ∀ (g : A.X.Isotropy x) (i : I) (y : A.Obj) (hy : y ∈ R.U),
    s (g • i) (R.Φ g y) =
      A.E.μ ⟨(R.Γ g y, s i y), ((isScPlusSectionOn i).1 y hy).trans (R.src_Γ g y hy).symm⟩
  /-- (2) `Λ(w) = |I_x|⁻¹·#{i ∈ I_x | sᵢ(P(w)) = w}`. -/
  rep : ∀ w, A.P w ∈ R.U →
    Λ w = (Fintype.card I : ℚ≥0)⁻¹ * ((Finset.univ.filter fun i => s i (A.P w) = w).card : ℚ≥0)

attribute [instance] SymmetricStructure.fintype SymmetricStructure.mulAction

/-! ### Lemma 13.2.6 -/

/-- The action `h • (i, g) = (i, hg)` of `G_x` on `I × G_x` (p. 610). -/
@[reducible] def prodIsotropyAction (I : Type u) (x : A.Obj) :
    MulAction (A.X.Isotropy x) (I × A.X.Isotropy x) where
  smul h p := (p.1, h * p.2)
  one_smul p := by
    change (p.1, 1 * p.2) = p
    rw [one_mul]
  mul_smul h h' p := by
    change (p.1, h * h' * p.2) = (p.1, h * (h' * p.2))
    rw [mul_assoc]

/-- **2021 Lemma 13.2.6, p. 610 (2017: Lemma 13.6)**: every sc⁺-multisection functor admits
locally a symmetric sc⁺-section structure (the text's construction: equal weights, then
`Î = I × G_x` with `s_{(i,g)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))`). -/
theorem lemma_13_2_6 {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (x : A.Obj) :
    Nonempty (SymmetricStructure A Λ x) := by
  -- a local representation on a neighbourhood with the properness property
  obtain ⟨O, k, s₀, σ, hO, hxO, h₀⟩ := hΛ.exists_isLocalRepOn x
  obtain ⟨V, hxV, hV⟩ := A.X.exists_hasPropernessProperty x
  obtain ⟨R, hRU⟩ := A.X.theorem_7_1_13 x (hO.inter hV.1) ⟨hxO, hxV⟩
  have hprop : A.X.HasPropernessProperty R.U :=
    hV.mono R.isOpen_U (hRU.trans inter_subset_right)
  have h₁ := (h₀.mono R.isOpen_U (hRU.trans inter_subset_left)).extendZero
  set s : Fin k → A.Obj → A.W := fun i => extendZero R.U (s₀ i)
  -- equal weights
  obtain ⟨I₁, _, c, hcard0, heq⟩ := h₁.exists_equal_weights
  set t : I₁ → A.Obj → A.W := fun j => s (c j)
  have ht : ∀ j, IsScPlusSectionOn A (t j) R.U := fun j => h₁.2.1 (c j)
  have hPt : ∀ j y, y ∈ R.U → A.P (t j y) = y := fun j y hy => (ht j).1 y hy
  -- the transported sections `s_{(j,g)}(z) = μ(Γ(g, g⁻¹ z), t_j(g⁻¹ z))`
  set Gx := A.X.Isotropy x
  let _ : Fintype Gx := Fintype.ofFinite Gx
  set a : Gx → A.Obj → A.Obj := fun g z => R.Φ g⁻¹ z
  have haU : ∀ g, ∀ z ∈ R.U, a g z ∈ R.U := fun g z hz => R.mapsTo_Φ g⁻¹ hz
  set S : I₁ × Gx → A.Obj → A.W := fun p =>
    transportSection (fun z => R.Γ p.2 (a p.2 z)) (fun z => t p.1 (a p.2 z)) with hSdef
  have hsrcS : ∀ (p : I₁ × Gx), ∀ z ∈ R.U,
      A.P (t p.1 (a p.2 z)) = A.X.src (R.Γ p.2 (a p.2 z)) := fun p z hz => by
    rw [hPt _ _ (haU _ z hz), R.src_Γ _ _ (haU _ z hz)]
  have hΦa : ∀ g, ∀ z ∈ R.U, R.Φ g (a g z) = z := fun g z hz => by
    have := (R.isScDiffeoOn_Φ g).right_inv z hz
    exact this
  have hS : ∀ p (z : A.Obj) (hz : z ∈ R.U), S p z =
      A.E.μ ⟨(R.Γ p.2 (a p.2 z), t p.1 (a p.2 z)), hsrcS p z hz⟩ := fun p z hz =>
    transportSection_of_mem (τ := fun z => R.Γ p.2 (a p.2 z)) (b := fun z => t p.1 (a p.2 z))
      (hsrcS p z hz)
  have hSsc : ∀ p, IsScPlusSectionOn A (S p) R.U := fun p => by
    obtain ⟨-, G, hG, hGs⟩ := ht p.1
    have hasm : A.X.PObj.IsScSmoothOn A.X.PObj (a p.2) R.U :=
      (R.isScDiffeoOn_Φ p.2).isScSmoothOn_inv
    refine isScPlusSectionOn_transportSection
      (MPolyfold.IsScSmoothOn.comp (R.isScSmoothOn_Γ p.2) hasm (haU p.2))
      (G := G ∘ a p.2) (fun z hz => hG _ (haU _ z hz))
      (MPolyfold.IsScSmoothOn.comp hGs hasm (haU p.2)) (hsrcS p) fun z hz => ?_
    rw [R.tgt_Γ _ _ (haU _ z hz)]
    exact hΦa p.2 z hz
  let _ := prodIsotropyAction I₁ x
  refine ⟨SymmetricStructure.mk R hprop (I₁ × Gx) S hSsc ?_ ?_⟩
  · -- (1)
    rintro h ⟨j, g⟩ y hy
    have hy' : a g y ∈ R.U := haU g y hy
    have hhy : R.Φ h y ∈ R.U := R.mapsTo_Φ h hy
    have ha' : a (h * g) (R.Φ h y) = a g y := by
      change R.Φ (h * g)⁻¹ (R.Φ h y) = R.Φ g⁻¹ y
      rw [mul_inv_rev, R.Φ_mul _ _ _ hhy, (R.isScDiffeoOn_Φ h).left_inv y hy]
    have hc : A.X.src (R.Γ h y) = A.X.tgt (R.Γ g (a g y)) := by
      rw [R.src_Γ h y hy, R.tgt_Γ g _ hy', hΦa g y hy]
    change S (j, h * g) (R.Φ h y) = _
    rw [hS (j, h * g) _ hhy]
    have e1 := A.E.μ_comp (R.Γ h y) (R.Γ g (a g y)) (t j (a g y))
      ((hPt j _ hy').trans (R.src_Γ g _ hy').symm) hc
    have hΓ : A.X.comp (R.Γ h y) (R.Γ g (a g y)) = R.Γ (h * g) (a g y) := by
      have := R.Γ_mul h g hy'
      rwa [hΦa g y hy] at this
    refine (A.E.μ_congr ?_).trans (e1.trans (A.E.μ_congr ?_))
    · change (R.Γ (h * g) (a (h * g) (R.Φ h y)), t j (a (h * g) (R.Φ h y))) =
        (A.X.comp (R.Γ h y) (R.Γ g (a g y)), t j (a g y))
      rw [ha', hΓ]
    · change (R.Γ h y, A.E.μ ⟨(R.Γ g (a g y), t j (a g y)), _⟩) = (R.Γ h y, S (j, g) y)
      rw [hS (j, g) y hy]
  · -- (2)
    intro w hw
    set z := A.P w
    have hcardI₁ : (Fintype.card I₁ : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.2 hcard0.ne'
    -- for each `g`, the pull-back `w_g = μ(Γ(g, g⁻¹z)⁻¹, w)` over `g⁻¹ z`
    have hwg : ∀ g : Gx, A.P w = A.X.src (A.X.inv (R.Γ g (a g z))) := fun g => by
      rw [A.X.src_inv, R.tgt_Γ g _ (haU g z hw), hΦa g z hw]
    set wg : Gx → A.W := fun g => A.E.μ ⟨(A.X.inv (R.Γ g (a g z)), w), hwg g⟩
    have hPwg : ∀ g, A.P (wg g) = a g z := fun g => by
      rw [A.E.P_μ, A.X.tgt_inv, R.src_Γ g _ (haU g z hw)]
    have hΛwg : ∀ g, Λ (wg g) = Λ w := fun g => hΛ.1 _
    have hiff : ∀ (j : I₁) (g : Gx), S (j, g) z = w ↔ t j (a g z) = wg g := fun j g => by
      rw [hS (j, g) z hw]
      constructor
      · intro e
        have := A.E.μ_inv_μ ⟨(R.Γ g (a g z), t j (a g z)), hsrcS (j, g) z hw⟩
          (by rw [A.E.P_μ]; exact (A.X.src_inv _).symm)
        exact this.symm.trans (A.E.μ_congr (Prod.ext rfl e))
      · intro e
        have := A.E.μ_μ_inv (R.Γ g (a g z)) w (hwg g) (by
          change A.P (wg g) = _; rw [hPwg, R.src_Γ g _ (haU g z hw)])
        refine Eq.trans ?_ this
        exact A.E.μ_congr (Prod.ext rfl (by exact e))
    have hcount : ∀ g : Gx, (∑ j : I₁, if S (j, g) z = w then (1 : ℚ≥0) else 0) =
        (Fintype.card I₁ : ℚ≥0) * Λ w := fun g => by
      have e := heq (wg g) (by rw [hPwg]; exact haU g z hw)
      rw [hPwg, hΛwg, Finset.natCast_card_filter] at e
      rw [e, ← mul_assoc, mul_inv_cancel₀ hcardI₁, one_mul]
      exact Finset.sum_congr rfl fun j _ => if_congr (hiff j g) rfl rfl
    rw [Finset.natCast_card_filter, Fintype.sum_prod_type_right]
    simp_rw [hcount]
    have hGx : (Fintype.card Gx : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
    field_simp

end SBLocalization

end Polyfold
