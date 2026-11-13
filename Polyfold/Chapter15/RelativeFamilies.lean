import Polyfold.Chapter15.GeneralPositionAssembly
import Polyfold.Chapter15.TransversalExtension
import Polyfold.Chapter13.MultisectionNoInverse

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (Transversal Extension Theorem; 2017: Theorem 15.5), steps (c)–(d),
pp. 698–699: the parameter families relative to a fixed multisection `Λ₀`.

# Parameter families relative to `Λ₀`

## The text, paraphrased

After the extension `Λ₀` of the boundary data (step (b)), the proof "argues as in Theorem 15.3.7":
it takes parameter families `t ↦ Λ_t` whose domain support stays away from `∂X`, so that
`Λ̃ = Λ_t ⊕ Λ₀` still equals `Λ₀` over `∂X`, and the parametrized surjectivity (15.1) is now asked
for the operators of `T(f, Λ₀)(x)` at the points `x` of `supp(Λ₀ ∘ f)`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IsParamOntoAtRel f Λ₀ Λ x`: (15.1) relative to `Λ₀`: for every operator `L` of `T(f, Λ₀)(x)`
  and every branch `i` of a linear representation of the family around `x`,
  `(v, τ) ↦ L v + Σ_j τ_j s_{ij}(x)` maps `T^R_xX × ℝ^ℓ` onto `W_x`.  For `Λ₀` the trivial
  multisection this is GP's `IsParamOntoAt` (`isParamOntoAtRel_zero_iff`).
* `IsParamOntoAtRel.of_reducedOnto`: where `(f, Λ₀)` is already in general position (for example
  at the points of `supp(Λ₀ ∘ f) ∩ ∂X`, by the boundary hypothesis), (15.1) holds for every linear
  family (`τ = 0`).
* Sums: `IsParamOntoAtRel.famAdd_left`, `IsParamOntoAtRel.famAdd_right`.
* `RelGPFamily A f Λ₀ N U g Q`: GP's `GPFamily` with (15.1) relative to `Λ₀` at the points of
  `supp(Λ₀ ∘ f) ∩ Q` and the bound `N(Λ_t) ≤ |t|₁ · g` (`g = h − N(Λ₀)` in the application):
  `RelGPFamily.zero`, `RelGPFamily.add`, `RelGPFamily.mono`, `RelGPFamily.zeroOn` (the empty family
  on a set where `(f, Λ₀)` is in general position).
* `eq_zeroMultisection_of_notMem_domSupp`, **`multisectionAdd_eq_left_of_notMem_domSupp`**: off
  `dom-supp(Λ)` the multisection `Λ` is the trivial one, and `Λ₀ ⊕ Λ = Λ₀` there; this is how
  `Λ̃ = Λ₀` over `∂X` follows from `dom-supp(Λ_t) ∩ ∂X = ∅`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold

variable {A : SEP.{u}}

/-! ### (15.1) relative to `Λ₀` -/

/-- **The parametrized reduced surjectivity relative to `Λ₀`** ((15.1) as used in steps (c)–(d)
of the proof of Theorem 15.3.9, p. 699): in a linear local representation `(Σ_j t_j s_{ij}, σ_i)`
of the family around `x`, for every operator `L` of `T(f, Λ₀)(x)` (Definition 15.1.7), every chart
presentation of `T^R_xX` and every branch `i`, `(v, τ) ↦ L v + Σ_j τ_j s_{ij}(x)` maps
`T^R_xX × ℝ^ℓ` onto `W_x`. -/
def IsParamOntoAtRel (f : A.Obj → A.W) (Λ₀ : A.W → ℚ≥0) {ℓ : ℕ}
    (Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0) (x : A.X.PObj.Level 1) : Prop :=
  ∃ (O : Set A.Obj) (k : ℕ) (s : Fin k → Fin ℓ → A.Obj → A.W) (σ : Fin k → ℚ≥0)
    (hs : ∀ i j, IsSection A.P (s i j)), IsOpen O ∧ A.X.PObj.levelVal 1 x ∈ O ∧
      (∀ t, IsLocalRepOn A (Λ t) O (fun i => paramSec (s i) t) σ) ∧
      ∀ L ∈ (linearization f Λ₀ x).support, ∀ (φ : MChart A.Obj)
        (hφ : A.X.PObj.IsChart φ) (hx : A.X.PObj.levelVal 1 x ∈ φ.source) (m : ℕ)
        (V : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin m → ℝ)).prod V)),
        φ.model.C = T 0 ⁻¹' quadrant m V 0 →
          ∀ i (w : A.P ⁻¹' {A.X.PObj.levelVal 1 x}), ∃ v ∈ reducedTangentFiber hφ hx T,
            ∃ τ : Fin ℓ → ℝ, L v + ∑ j, τ j •
              (⟨s i j (A.X.PObj.levelVal 1 x), hs i j _⟩ : A.P ⁻¹' {A.X.PObj.levelVal 1 x}) = w

/-- For the trivial multisection, (15.1) relative to `Λ₀` is GP's (15.1). -/
theorem isParamOntoAtRel_zero_iff {f : A.Obj → A.W} {ℓ : ℕ} {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0}
    {x : A.X.PObj.Level 1} :
    IsParamOntoAtRel f (zeroMultisection A) Λ x ↔ IsParamOntoAt f Λ x :=
  Iff.rfl

/-- **Where `(f, Λ₀)` is in general position, (15.1) relative to `Λ₀` holds for every linear
family** (take `τ = 0`): this is how the boundary hypothesis of Theorem 15.3.9 enters steps
(c)–(d). -/
theorem IsParamOntoAtRel.of_reducedOnto {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {ℓ : ℕ}
    {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0} {x : A.X.PObj.Level 1} (hred : IsReducedOntoAtPt f Λ₀ x)
    (h : IsLinearFamily Λ) : IsParamOntoAtRel f Λ₀ Λ x := by
  obtain ⟨O, k, s, σ, hO, hx, hs, hr⟩ := h (A.X.PObj.levelVal 1 x)
  refine ⟨O, k, s, σ, hs, hO, hx, hr, ?_⟩
  intro L hL φ hφ hxφ m V T hT i w
  obtain ⟨⟨v, hv⟩, hvw⟩ := hred L hL φ hφ hxφ m V T hT w
  refine ⟨v, hv, 0, ?_⟩
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
  exact hvw

/-- **Relative (15.1) passes to sums, from the first summand.** -/
theorem IsParamOntoAtRel.famAdd_left {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {ℓ ℓ' : ℕ}
    {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0} {Λ' : (Fin ℓ' → ℝ) → A.W → ℚ≥0} {x : A.X.PObj.Level 1}
    (hp : IsParamOntoAtRel f Λ₀ Λ x) (h' : IsLinearFamily Λ') :
    IsParamOntoAtRel f Λ₀ (famAdd Λ Λ') x := by
  classical
  obtain ⟨O, k, s, σ, hs, hO, hx, hr, hon⟩ := hp
  obtain ⟨O', k', s', σ', hO', hx', hs', hr'⟩ := h' (A.X.PObj.levelVal 1 x)
  refine ⟨O ∩ O', _, _, _, fun n j => isSection_append (hs _) (hs' _) j, hO.inter hO', ⟨hx, hx'⟩,
    isLocalRepOn_famAdd (hO.inter hO') hs hs' (fun t => (hr t).mono (hO.inter hO')
      inter_subset_left) (fun t => (hr' t).mono (hO.inter hO') inter_subset_right), ?_⟩
  intro L hL φ hφ hxφ m V T hT n w
  obtain ⟨v, hv, τ, hτ⟩ :=
    hon L hL φ hφ hxφ m V T hT ((Fintype.equivFin (Fin k × Fin k')).symm n).1 w
  refine ⟨v, hv, Fin.append τ 0, ?_⟩
  rw [← hτ, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_smul,
    Finset.sum_const_zero, add_zero]

/-- **Relative (15.1) passes to sums, from the second summand.** -/
theorem IsParamOntoAtRel.famAdd_right {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {ℓ ℓ' : ℕ}
    {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0} {Λ' : (Fin ℓ' → ℝ) → A.W → ℚ≥0} {x : A.X.PObj.Level 1}
    (h : IsLinearFamily Λ) (hp : IsParamOntoAtRel f Λ₀ Λ' x) :
    IsParamOntoAtRel f Λ₀ (famAdd Λ Λ') x := by
  classical
  obtain ⟨O', k', s', σ', hs', hO', hx', hr', hon⟩ := hp
  obtain ⟨O, k, s, σ, hO, hx, hs, hr⟩ := h (A.X.PObj.levelVal 1 x)
  refine ⟨O ∩ O', _, _, _, fun n j => isSection_append (hs _) (hs' _) j, hO.inter hO', ⟨hx, hx'⟩,
    isLocalRepOn_famAdd (hO.inter hO') hs hs' (fun t => (hr t).mono (hO.inter hO')
      inter_subset_left) (fun t => (hr' t).mono (hO.inter hO') inter_subset_right), ?_⟩
  intro L hL φ hφ hxφ m V T hT n w
  obtain ⟨v, hv, τ, hτ⟩ :=
    hon L hL φ hφ hxφ m V T hT ((Fintype.equivFin (Fin k × Fin k')).symm n).2 w
  refine ⟨v, hv, Fin.append 0 τ, ?_⟩
  rw [← hτ, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_smul,
    Finset.sum_const_zero, zero_add]

/-! ### Families relative to `Λ₀` -/

variable (A) in
/-- **The parameter families of steps (c)–(d) of the proof of Theorem 15.3.9 on a set `Q`**
(p. 699, "argue as in Theorem 15.3.7"): a linear family `t ↦ Λ_t` of structurable
sc⁺-multisections with `N(Λ_t)(x) ≤ |t|₁ · g(x)`, `dom-supp(Λ_t) ⊆ U`, and (15.1) relative to
`Λ₀` at every `x ∈ supp(Λ₀ ∘ f) ∩ Q`.  (GP's `GPFamily` is the case `Λ₀` trivial, `g = h`, with
`S_f` in place of `supp(Λ₀ ∘ f)`.) -/
structure RelGPFamily (f : A.Obj → A.W) (Λ₀ : A.W → ℚ≥0) (N : A.B.One → ℝ) (U : Set A.Obj)
    (g : A.Obj → ℝ) (Q : Set A.Obj) where
  /-- The number of parameters. -/
  ℓ : ℕ
  /-- The family. -/
  Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0
  isStructurable : ∀ t, IsStructurable A (Λ t)
  isLinear : IsLinearFamily Λ
  norm_le : ∀ t x, pointwiseNorm N (Λ t) x ≤ (∑ j, |t j|) * g x
  domSupp_subset : ∀ t, domSupp (Λ t) ⊆ U
  paramOnto : ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ Q →
    0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsParamOntoAtRel f Λ₀ Λ x

variable {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {N : A.B.One → ℝ} {U : Set A.Obj} {g : A.Obj → ℝ}

/-- A family on `Q` is a family on every `Q' ⊆ Q`. -/
def RelGPFamily.mono {Q Q' : Set A.Obj} (F : RelGPFamily A f Λ₀ N U g Q) (hQ : Q' ⊆ Q) :
    RelGPFamily A f Λ₀ N U g Q' where
  ℓ := F.ℓ
  Λ := F.Λ
  isStructurable := F.isStructurable
  isLinear := F.isLinear
  norm_le := F.norm_le
  domSupp_subset := F.domSupp_subset
  paramOnto x hx := F.paramOnto x (hQ hx)

/-- The parameter-free family `t ↦ Λ₀` (the trivial multisection) is linear. -/
theorem isLinearFamily_zero : IsLinearFamily (A := A) (ℓ := 0) fun _ => zeroMultisection A :=
  fun _ => ⟨univ, 1, fun _ j => j.elim0, fun _ => 1, isOpen_univ, mem_univ _,
    fun _ j => j.elim0, fun t => by
      simp only [paramSec_fin_zero]
      exact isLocalRepOn_zeroMultisection isOpen_univ⟩

/-- **The empty family on a set where `(f, Λ₀)` is in general position** (`ℓ = 0`, the trivial
multisection): (15.1) relative to `Λ₀` is general position of `(f, Λ₀)` there. -/
def RelGPFamily.zeroOn (h𝒰 : Nonempty A.X.GoodSystem) (hN : A.B.IsAuxNorm N) {Q : Set A.Obj}
    (hQ : ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ Q →
      0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x) :
    RelGPFamily A f Λ₀ N U g Q where
  ℓ := 0
  Λ _ := zeroMultisection A
  isStructurable _ := isStructurable_zeroMultisection_of_goodSystem h𝒰
  isLinear := isLinearFamily_zero
  norm_le t x := by rw [pointwiseNorm_zeroMultisection hN]; simp
  domSupp_subset _ := by rw [domSupp_zeroMultisection]; exact empty_subset _
  paramOnto x hx hpos := IsParamOntoAtRel.of_reducedOnto (hQ x hx hpos) isLinearFamily_zero

/-- **The empty family** on `Q = ∅`, given a good system. -/
def RelGPFamily.zero (h𝒰 : Nonempty A.X.GoodSystem) (hN : A.B.IsAuxNorm N) :
    RelGPFamily A f Λ₀ N U g ∅ :=
  RelGPFamily.zeroOn h𝒰 hN fun _ hx => hx.elim

/-- **The sum of two relative families** (`Λ_t ⊕ Λ'_{t'}`, as in "From local to global",
p. 696): a relative family on `Q ∪ Q'`. -/
def RelGPFamily.add (hN : A.B.IsAuxNorm N) {Q Q' : Set A.Obj}
    (F : RelGPFamily A f Λ₀ N U g Q) (F' : RelGPFamily A f Λ₀ N U g Q') :
    RelGPFamily A f Λ₀ N U g (Q ∪ Q') where
  ℓ := F.ℓ + F'.ℓ
  Λ := famAdd F.Λ F'.Λ
  isStructurable t := proposition_13_3_12 (F.isStructurable _) (F'.isStructurable _)
  isLinear := IsLinearFamily.famAdd F.isLinear F'.isLinear
  norm_le t x := by
    refine (pointwiseNorm_multisectionAdd_le hN (F.isStructurable _).1
      (F'.isStructurable _).1 x).trans ?_
    refine (add_le_add (F.norm_le _ x) (F'.norm_le _ x)).trans_eq ?_
    rw [← add_mul, Fin.sum_univ_add]
    rfl
  domSupp_subset t := (domSupp_multisectionAdd_subset _ _).trans
    (union_subset (F.domSupp_subset _) (F'.domSupp_subset _))
  paramOnto x hx hS := by
    rcases hx with hx | hx
    · exact (F.paramOnto x hx hS).famAdd_left F'.isLinear
    · exact IsParamOntoAtRel.famAdd_right F.isLinear (F'.paramOnto x hx hS)

/-! ### Off the domain support -/

/-- **Off `dom-supp(Λ)` an sc⁺-multisection is the trivial one**: over `x ∉ dom-supp(Λ)` every
branch passes through `0_x`, so `Λ(0_x) = Σ σ_i = 1` and `Λ = 0` elsewhere on `W_x`. -/
theorem eq_zeroMultisection_of_notMem_domSupp {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) {w : A.W} (hw : A.P w ∉ domSupp Λ) :
    Λ w = zeroMultisection A w := by
  classical
  obtain ⟨O, k, s, σ, -, hx, hrep⟩ := hΛ.exists_isLocalRepOn (A.P w)
  have hs0 : ∀ i, s i (A.P w) = fiberZero A.P (A.P w) := by
    intro i
    by_contra hne
    have hmem : s i (A.P w) ∈ suppAt Λ (A.P w) := by
      rw [hrep.suppAt_eq hx]; exact ⟨i, rfl⟩
    exact hw (subset_closure ⟨s i (A.P w), hmem.1, hne, hmem.2⟩)
  rw [hrep.apply_of_proj hx rfl, zeroMultisection]
  simp only [hs0]
  split_ifs with h
  · simp only [hrep.2.2.1]
  · simp only [Finset.sum_const_zero]

/-- **`Λ₀ ⊕ Λ = Λ₀` off `dom-supp(Λ)`** (Definition 13.2.9 with the neutral element, P3D's
`multisectionAdd_zeroMultisection`): if `P(w) ∉ dom-supp(Λ)`, then `(Λ₀ ⊕ Λ)(w) = Λ₀(w)`. -/
theorem multisectionAdd_eq_left_of_notMem_domSupp {Λ Λ' : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (hΛ' : IsScPlusMultisection A Λ') {w : A.W}
    (hw : A.P w ∉ domSupp Λ') : multisectionAdd Λ Λ' w = Λ w := by
  have h : ∀ u : A.P ⁻¹' {A.P w}, Λ' u = zeroMultisection A u := fun u =>
    eq_zeroMultisection_of_notMem_domSupp hΛ' (by
      rw [show A.P (u : A.W) = A.P w from u.2]; exact hw)
  have e : multisectionAdd Λ Λ' w = multisectionAdd Λ (zeroMultisection A) w := by
    unfold multisectionAdd addAt
    refine finsum_congr fun p => ?_
    rw [h p.2]
  rw [e, multisectionAdd_zeroMultisection hΛ]

end SBLocalization

end Polyfold
