import Polyfold.Chapter14.ZLoops
import Polyfold.Chapter13.AtomicConstruction

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.5, pp. 672–679:
**Proposition 14.5.4** (the transport of the local extensions to all `V̂_b`) (2017:
Proposition 14.8), as a statement.

# The transported section structures

## The text, paraphrased

Fix `a ∈ A`.  From the local extension `(ŝᵃᵢ)_{i ∈ I_a}` on `V̂_a` (Proposition 14.4.14) and the
cut-off `β_a` (Lemma 14.5.1) the text builds, for every `b ∈ A`, a symmetric sc⁺-section
structure `(s̃ᵃ_{b,j})_{j ∈ I_b}` on `V̂_b` with (1) `s̃ᵃ_{a,i} = β_a·ŝᵃᵢ` on `V̂_a`, (2) the support
of `s̃ᵃ_{a,i}` is closed in `X` and contained in `V̂_a`, (3) `s̃ᵃ_{b,j} = β_a·s⁰ᵇⱼ` on
`V_b = V̂_b ∩ ∂X`, (4) `s̃ᵃ_{b',β(k)}(t(φ)) = μ(φ, s̃ᵃ_{b,α(k)}(s(φ)))` for `φ ∈ V̂_{b,b'}` and every
representative `[I_b ←α I →β I_{b'}]` of `τ̂_{b,b'}(φ)`.  The proof transports `β_a·ŝᵃ` along the
morphisms from `V̂_a` to `V̂_b`, well defined by the z-arcs of §14.4 (Definitions 14.4.2–14.4.4)
and Proposition 14.4.14 (2), and sc⁺ by the properness of `cl(Ũ(a))` and (14.53).

## What is formalized

* `TransportInput A S`: the data the proof uses, over B2's `ZSetup` `S` (the sets `V̂_a`, the
  index sets `I_a` with their actions, the extended correspondences `τ̂`): the open `V̂_a`, the
  properness of `cl(Ũ(a))`, `τ̂` locally constant, the cut-offs `β_a` (sc-smooth functors with
  (14.53)), the boundary data `s⁰ᵃ` (compatible with `τ̂` over `∂X`) and the local extensions `ŝᵃ`
  (the output of LX's `proposition_14_4_14`: sc⁺ on `V̂_a`, `G_a`-equivariant, `= s⁰ᵃ` on `V_a`,
  equal on `∼_z`-related indices).
* **`proposition_14_5_4_statement T`**: the conclusion (1)–(4), with "symmetric sc⁺-section
  structure on `V̂_b`" read as sc⁺ on `V̂_b` and `G_b`-equivariant (Definition 13.2.5 (1)).
  Not proved here (gap text in the hand-over note).
* `proposition_14_5_4_statement_of_zero`: the statement holds when `ŝ = 0` and `s⁰ = 0` (with
  `s̃ = 0`): it is not contradictory.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-- **The input of Proposition 14.5.4** (2021 pp. 667–672) over a `ZSetup` `S`. -/
structure TransportInput (A : SEP.{u}) (S : A.X.ZSetup) where
  isOpen_V : ∀ a ∈ S.A, IsOpen (S.V a)
  /-- `t : s⁻¹(cl(Ũ(a))) → X` is proper (Definition 7.5.8). -/
  proper : ∀ a ∈ S.A, A.X.IsProperSubset (closure (S.nbhd a).U)
  /-- `τ̂_{a,b}` is locally constant on `V̂_{a,b}`. -/
  locallyConstant : ∀ a ∈ S.A, ∀ b ∈ S.A, ∀ φ ∈ A.X.morBetween (S.V a) (S.V b),
    ∀ᶠ ψ in 𝓝[A.X.morBetween (S.V a) (S.V b)] φ, S.τ a b ψ = S.τ a b φ
  /-- The cut-offs `β_a` of Lemma 14.5.1. -/
  β : A.Obj → A.Obj → ℝ
  isScSmooth_β : ∀ a, A.X.PObj.IsScSmoothMap realPolyfold (β a)
  β_tgt : ∀ a (φ : A.Mor), β a (A.X.tgt φ) = β a (A.X.src φ)
  /-- (14.53): `cl_X({y ∈ Ũ(a) | β_a(y) ≠ 0}) ⊆ V̂_a`. -/
  closure_support_β : ∀ a ∈ S.A, closure {y ∈ (S.nbhd a).U | β a y ≠ 0} ⊆ S.V a
  /-- The boundary sections `s⁰ᵃᵢ` (on `V_a = V̂_a ∩ ∂X`). -/
  s0 : ∀ a, S.I a → A.Obj → A.W
  /-- Definition 14.1.7 (4) for `τ̂ = τ⁰` over `∂X`. -/
  s0_compat : ∀ a ∈ S.A, ∀ b ∈ S.A,
    ∀ φ ∈ A.X.morBetween (S.V a ∩ A.X.PObj.boundary) (S.V b ∩ A.X.PObj.boundary),
      (S.τ a b φ).Sat fun i j => s0 b j (A.X.tgt φ) = fibAct φ (s0 a i (A.X.src φ))
  /-- The local extensions `ŝᵃᵢ` of Proposition 14.4.14. -/
  sh : ∀ a, S.I a → A.Obj → A.W
  isScPlusSectionOn_sh : ∀ a ∈ S.A, ∀ i, IsScPlusSectionOn A (sh a i) (S.V a)
  sh_equivariant : ∀ a ∈ S.A, ∀ (g : A.X.Isotropy a) (i : S.I a), ∀ y ∈ S.V a,
    sh a (g • i) ((S.nbhd a).rep.Φ g y) = fibAct ((S.nbhd a).rep.Γ g y) (sh a i y)
  sh_boundary : ∀ a ∈ S.A, ∀ i, ∀ y ∈ S.V a ∩ A.X.PObj.boundary, sh a i y = s0 a i y
  /-- Proposition 14.4.14 (2): `ŝᵃᵢ(z) = ŝᵃ_{i'}(z)` if `i ∼_z i'`. -/
  sh_zRel : ∀ a ∈ S.A, ∀ z ∈ S.V a, ∀ i i', S.ZRel a z i i' → sh a i z = sh a i' z

/-- **2021 Proposition 14.5.4, p. 673 (2017: Proposition 14.8)**, as a statement (not proved
here): for every `a ∈ A` there are sections `s̃ᵃ_{b,j}`, `b ∈ A`, `j ∈ I_b`, sc⁺ and
`G_b`-equivariant on `V̂_b`, with (1)–(4). -/
def proposition_14_5_4_statement {S : A.X.ZSetup} (T : TransportInput A S) : Prop :=
  ∀ a ∈ S.A, ∃ st : ∀ b, S.I b → A.Obj → A.W,
    (∀ b ∈ S.A, ∀ j, IsScPlusSectionOn A (st b j) (S.V b)) ∧
    (∀ b ∈ S.A, ∀ (g : A.X.Isotropy b) (j : S.I b), ∀ y ∈ S.V b,
      st b (g • j) ((S.nbhd b).rep.Φ g y) = fibAct ((S.nbhd b).rep.Γ g y) (st b j y)) ∧
    -- (1)
    (∀ i, ∀ y ∈ S.V a, st a i y = Polyfold.sectionSmul A.P (T.β a) (T.sh a i) y) ∧
    -- (2)
    (∀ i, ∃ K : Set A.Obj, IsClosed K ∧ K ⊆ S.V a ∧
      ∀ y ∈ S.V a, y ∉ K → st a i y = fiberZero A.P y) ∧
    -- (3)
    (∀ b ∈ S.A, ∀ j, ∀ y ∈ S.V b ∩ A.X.PObj.boundary,
      st b j y = Polyfold.sectionSmul A.P (T.β a) (T.s0 b j) y) ∧
    -- (4)
    (∀ b ∈ S.A, ∀ b' ∈ S.A, ∀ φ ∈ A.X.morBetween (S.V b) (S.V b'),
      (S.τ b b' φ).Sat fun j j' => st b' j' (A.X.tgt φ) = fibAct φ (st b j (A.X.src φ)))

theorem sectionSmul_fiberZero_gl (β : A.Obj → ℝ) :
    Polyfold.sectionSmul A.P β (fiberZero A.P) = fiberZero A.P := by
  funext y
  unfold Polyfold.sectionSmul
  rw [dif_pos (proj_fiberZero A.P y)]
  have e : (⟨fiberZero A.P y, proj_fiberZero A.P y⟩ : A.P ⁻¹' {y}) = 0 := rfl
  rw [e, smul_zero]
  rfl

/-- **The statement is not contradictory**: for vanishing data (`ŝ = 0`, `s⁰ = 0`) it holds with
`s̃ = 0`. -/
theorem proposition_14_5_4_statement_of_zero {S : A.X.ZSetup} (T : TransportInput A S)
    (hsh : ∀ a i, T.sh a i = fiberZero A.P) (hs0 : ∀ a i, T.s0 a i = fiberZero A.P) :
    proposition_14_5_4_statement T := by
  intro a _
  refine ⟨fun _ _ => fiberZero A.P, fun b hb _ =>
    IsScPlusSectionOn.of_isScPlusSection StrongBundle.isScPlusSection_fiberZero (T.isOpen_V b hb),
    fun b hb g _ y hy => (fibAct_fiberZero ((S.nbhd b).src_Γ g (S.V_subset b hb hy))
      ((S.nbhd b).tgt_Γ g (S.V_subset b hb hy))).symm, fun i y _ => ?_,
    fun _ => ⟨∅, isClosed_empty, empty_subset _, fun _ _ _ => rfl⟩, fun b _ j y _ => ?_,
    fun _ _ _ _ _ _ => IndexCorr.sat_of_forall (fun _ _ => (fibAct_fiberZero rfl rfl).symm) _⟩
  · rw [hsh, sectionSmul_fiberZero_gl]
  · rw [hs0, sectionSmul_fiberZero_gl]

end SBLocalization

end Polyfold
