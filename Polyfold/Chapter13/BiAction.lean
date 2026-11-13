import Polyfold.Chapter13.GoodSystem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), Part III, §13.1, pp. 601–602 and
606–607: the **natural bi-action** (Definition 13.1.5, p. 601), **Lemma 13.1.6** (p. 602), the
discussion before Proposition 13.1.9 (pp. 606–607) and **Proposition 13.1.9** (p. 607).
(2017 text: Definition 13.3, Lemma 13.2, Proposition 13.2.)

# The natural bi-action on `𝒰(x, x')` and its components

## The text, paraphrased

(p. 601) For open neighbourhoods `U(x)`, `U(x')` with the natural actions, `G_{x'}` acts from the
left and `G_x` from the right on `𝒰(x, x')` by `g' ∗ φ ∗ g = Γ'(g', t(φ)) ∘ φ ∘ Γ(g, g⁻¹ ∗ s(φ))`,
an sc-smooth map with `s(g' ∗ φ ∗ g) = g⁻¹ ∗ s(φ)`, `t(g' ∗ φ ∗ g) = g' ∗ t(φ)`,
`(g'h') ∗ φ ∗ (gh) = g' ∗ (h' ∗ φ ∗ g) ∗ h` and `1 ∗ φ ∗ 1 = φ`: two commuting actions
(Definition 13.1.5, the natural bi-action).  (p. 602) For a good system, `g' ∗ Σ ∗ g⁻¹` is again a
connected component.  (Lemma 13.1.6) For a component `Σ ⊆ 𝒰(x, x')`: (1) `g' ∗ Σ = Σ` forces
`g' = 1`; (2) `Σ ∗ g = Σ` forces `g = 1`; (3) for two components, `s(Σ₁)` and `s(Σ₂)` are equal
or disjoint, and likewise for `t`.  (pp. 606–607) With `O = s(Σ)`, `O' = t(Σ)`, `G_{x,Σ}` and
`G_{x',Σ}` the stabilisers of `O` and `O'`, and `D_Σ = t ∘ (s|Σ)⁻¹`, every `g ∈ G_{x,Σ}` determines
`g'(g) ∈ G_{x',Σ}` with `g'(g) ∗ D_Σ(z) = D_Σ(g ∗ z)`, and `g ↦ g'(g)` is a homomorphism.
(Proposition 13.1.9) There is a unique group isomorphism `G_{x,Σ} → G_{x',Σ}`, `g ↦ g'(g)`, with
`(s|Σ)⁻¹(g ∗ z) = g'(g) ∗ (s|Σ)⁻¹(z) ∗ g⁻¹` for `z ∈ s(Σ)`.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **Definition 13.1.5**: `biact N N' g' φ g` for `N : NatNbhd X x`, `N' : NatNbhd X x'`; the
  laws `src_biact`, `tgt_biact`, `biact_mem`, `biact_one_one`, `biact_biact` (the text's
  computation), `biact_one_right`, `biact_one_left`, `biact_inv_biact` (inverse);
  `isScSmoothOn_biact` (sc-smooth on `𝒰(x, x')` for fixed `g', g`), `continuousOn_biact`;
  cancellation `biact_left_cancel`, `biact_right_cancel`; `biactMulAction`, the bi-action as a
  `MulAction` of `G_{x'} × G_xᵐᵒᵖ` on `𝒰(x, x')`.
* For a good system `𝒰`: `GoodSystem.components` (the set of components of `𝒰(x, x')`,
  `sUnion_components`, `pairwiseDisjoint_components`), `GoodSystem.image_inv_comp` (`Σ⁻¹` is a
  component of `𝒰(x', x)`), `GoodSystem.biact`, `GoodSystem.image_biact_comp` (`g' ∗ Σ ∗ g` is the
  component of `g' ∗ φ ∗ g`), `GoodSystem.image_biact_comp_of_mem` (if `g' ∗ ψ ∗ g ∈ Σ` for one
  `ψ ∈ Σ`, then `g' ∗ Σ ∗ g = Σ`), `exists_biact_left_of_src`, `exists_biact_right_of_tgt`.
* **Lemma 13.1.6**: `lemma_13_1_6_one`, `lemma_13_1_6_two`, `lemma_13_1_6_three_src`,
  `lemma_13_1_6_three_tgt`, with the pointwise forms `eq_one_of_biact_left_mem`,
  `eq_one_of_biact_right_mem` (one `ψ ∈ Σ` with `g' ∗ ψ ∈ Σ` suffices).
* **Proposition 13.1.9**: `GoodSystem.stabSrc`, `GoodSystem.stabTgt` (`G_{x,Σ}`, `G_{x',Σ}`),
  `proposition_13_1_9` (existence of the isomorphism with the identity, and uniqueness among
  all maps with the identity); `GoodSystem.D` (`D_Σ = t ∘ (s|Σ)⁻¹`) and
  `isScDiffeoOn_D` (`D_Σ : s(Σ) → t(Σ)` is an sc-diffeomorphism) and `proposition_13_1_9_D`
  (`g'(g) ∗ D_Σ(z) = D_Σ(g ∗ z)`, the discussion before it); the isomorphism is
  `MulEquiv.ofBijective (partnerHom hφ)`, `partner hφ g` its value (`partner_spec`,
  `partner_identity`).

## Reading

* The bi-action is defined by the text's formula with the composition nested as
  `Γ'(g', t φ) ∘ (φ ∘ Γ(g, g⁻¹ ∗ s φ))`.  "Sc-smooth map `G_{x'} × 𝒰(x, x') × G_x → 𝒰(x, x')`" is
  read for each pair `(g', g)` (the groups are finite and discrete), as for `Γ` in
  `NaturalRep`.  It is `isScSmoothOn_biact`, from `φ ∗ g = (g⁻¹ ∗ φ⁻¹)⁻¹`.
* **Lemma 13.1.6 (1), (2)** hold in the pointwise form (one `ψ ∈ Σ` with `g' ∗ ψ ∗ 1 ∈ Σ`).
* **Proposition 13.1.9**: `G_{x,Σ} = {g | g ∗ O = O}` as a subgroup of `G_x`.  The text obtains
  `g'(g)` from the morphism `Θ_g(z)` and "smooth dependence on `z`"; we obtain it from
  Lemma 13.1.6 (3) applied to `Σ` and `Σ ∗ g⁻¹` (both components with source set `O`), which also
  gives the isomorphism property (the text proves only the homomorphism property).  The
  uniqueness holds among all maps `G_{x,Σ} → G_{x',Σ}` satisfying the identity.
-/

open Set Filter Topology Function MulOpposite

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-! ### Definition 13.1.5: the natural bi-action -/

section BiAction

variable {x x' : Obj} (N : X.NatNbhd x) (N' : X.NatNbhd x')

/-- **Definition 13.1.5 (the natural bi-action, p. 601; 2017: Definition 13.3)**:
`g' ∗ φ ∗ g = Γ'(g', t(φ)) ∘ φ ∘ Γ(g, g⁻¹ ∗ s(φ))` for `φ ∈ 𝒰(x, x')`. -/
def biact (g' : X.Isotropy x') (φ : Mor) (g : X.Isotropy x) : Mor :=
  X.comp (N'.rep.Γ g' (X.tgt φ)) (X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (X.src φ))))

variable {N N'}

section Laws

variable {φ : Mor} (hφ : φ ∈ X.morBetween N.U N'.U)
include hφ

private theorem mem_y (g : X.Isotropy x) : N.rep.Φ g⁻¹ (X.src φ) ∈ N.U :=
  N.Φ_mem g⁻¹ hφ.1

private theorem tgt_Γy (g : X.Isotropy x) :
    X.tgt (N.rep.Γ g (N.rep.Φ g⁻¹ (X.src φ))) = X.src φ := by
  rw [N.tgt_Γ g (mem_y hφ g), N.Φ_Φ_inv g hφ.1]

private theorem src_inner (g : X.Isotropy x) :
    X.src (X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (X.src φ)))) = N.rep.Φ g⁻¹ (X.src φ) := by
  rw [X.src_comp _ _ (tgt_Γy hφ g).symm, N.src_Γ g (mem_y hφ g)]

private theorem tgt_inner (g : X.Isotropy x) :
    X.tgt (X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (X.src φ)))) = X.tgt φ :=
  X.tgt_comp _ _ (tgt_Γy hφ g).symm

private theorem src_Γ' (g' : X.Isotropy x') : X.src (N'.rep.Γ g' (X.tgt φ)) = X.tgt φ :=
  N'.src_Γ g' hφ.2

private theorem compat (g' : X.Isotropy x') (g : X.Isotropy x) :
    X.src (N'.rep.Γ g' (X.tgt φ)) = X.tgt (X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (X.src φ)))) := by
  rw [src_Γ' hφ, tgt_inner hφ]

/-- `s(g' ∗ φ ∗ g) = g⁻¹ ∗ s(φ)`. -/
theorem src_biact (g' : X.Isotropy x') (g : X.Isotropy x) :
    X.src (biact N N' g' φ g) = N.rep.Φ g⁻¹ (X.src φ) := by
  rw [biact, X.src_comp _ _ (compat hφ g' g), src_inner hφ]

/-- `t(g' ∗ φ ∗ g) = g' ∗ t(φ)`. -/
theorem tgt_biact (g' : X.Isotropy x') (g : X.Isotropy x) :
    X.tgt (biact N N' g' φ g) = N'.rep.Φ g' (X.tgt φ) := by
  rw [biact, X.tgt_comp _ _ (compat hφ g' g), N'.tgt_Γ g' hφ.2]

/-- The bi-action preserves `𝒰(x, x')`. -/
theorem biact_mem (g' : X.Isotropy x') (g : X.Isotropy x) :
    biact N N' g' φ g ∈ X.morBetween N.U N'.U := by
  refine ⟨?_, ?_⟩
  · rw [src_biact hφ]
    exact mem_y hφ g
  · rw [tgt_biact hφ]
    exact N'.Φ_mem g' hφ.2

/-- `g' ∗ φ ∗ 1 = Γ'(g', t φ) ∘ φ`. -/
theorem biact_one_right (g' : X.Isotropy x') :
    biact N N' g' φ 1 = X.comp (N'.rep.Γ g' (X.tgt φ)) φ := by
  rw [biact, inv_one, N.Φ_one hφ.1, N.Γ_one hφ.1, GroupoidStr.comp_unit_of_eq rfl]

/-- `1 ∗ φ ∗ g = φ ∘ Γ(g, g⁻¹ ∗ s φ)`. -/
theorem biact_one_left (g : X.Isotropy x) :
    biact N N' 1 φ g = X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (X.src φ))) := by
  rw [biact, N'.Γ_one hφ.2, GroupoidStr.unit_comp_of_eq (tgt_inner hφ g)]

/-- `1 ∗ φ ∗ 1 = φ`. -/
theorem biact_one_one : biact N N' 1 φ 1 = φ := by
  rw [biact_one_right hφ, N'.Γ_one hφ.2, GroupoidStr.unit_comp_of_eq rfl]

/-- **The text's computation (p. 601)**: `g' ∗ (h' ∗ φ ∗ h) ∗ g = (g' h') ∗ φ ∗ (h g)`: a left
action of `G_{x'}` and a right action of `G_x`, commuting. -/
theorem biact_biact (g' h' : X.Isotropy x') (h g : X.Isotropy x) :
    biact N N' g' (biact N N' h' φ h) g = biact N N' (g' * h') φ (h * g) := by
  set y := N.rep.Φ h⁻¹ (X.src φ) with hy
  have hyU : y ∈ N.U := mem_y hφ h
  set w := N.rep.Φ g⁻¹ y with hw
  have hwU : w ∈ N.U := N.Φ_mem g⁻¹ hyU
  set A := N'.rep.Γ h' (X.tgt φ)
  set B := N.rep.Γ h y
  set C := N'.rep.Γ g' (N'.rep.Φ h' (X.tgt φ))
  set D := N.rep.Γ g w
  have hB : X.tgt B = X.src φ := tgt_Γy hφ h
  have hD : X.tgt D = y := by rw [N.tgt_Γ g hwU, hw, N.Φ_Φ_inv g hyU]
  have hBs : X.src B = y := N.src_Γ h hyU
  have hA : X.src A = X.tgt (X.comp φ B) := compat hφ h' h
  have hAt : X.tgt A = N'.rep.Φ h' (X.tgt φ) := N'.tgt_Γ h' hφ.2
  have hC : X.src C = X.tgt A := by rw [N'.src_Γ g' (N'.Φ_mem h' hφ.2), hAt]
  have hφB : X.src φ = X.tgt B := hB.symm
  have hBD : X.src B = X.tgt D := by rw [hBs, hD]
  have hφBD : X.src (X.comp φ B) = X.tgt D := by rw [X.src_comp _ _ hφB, hBD]
  -- the left-hand side
  have hL : biact N N' g' (biact N N' h' φ h) g =
      X.comp C (X.comp (X.comp A (X.comp φ B)) D) := by
    rw [biact, src_biact hφ, tgt_biact hφ]
    rfl
  -- the right-hand side
  have hR : biact N N' (g' * h') φ (h * g) =
      X.comp (N'.rep.Γ (g' * h') (X.tgt φ))
        (X.comp φ (N.rep.Γ (h * g) (N.rep.Φ (h * g)⁻¹ (X.src φ)))) := rfl
  have hΓ' : X.comp C A = N'.rep.Γ (g' * h') (X.tgt φ) := N'.Γ_mul g' h' hφ.2
  have hwy : N.rep.Φ (h * g)⁻¹ (X.src φ) = w := by
    rw [mul_inv_rev, N.Φ_mul g⁻¹ h⁻¹ hφ.1]
  have hΓ : X.comp B D = N.rep.Γ (h * g) w := by
    have := N.Γ_mul h g hwU
    rwa [hw, N.Φ_Φ_inv g hyU] at this
  have hφBD' : X.src φ = X.tgt (X.comp B D) := by rw [X.tgt_comp _ _ hBD, hB]
  have hA' : X.src A = X.tgt (X.comp φ (X.comp B D)) := by
    rw [X.tgt_comp _ _ hφBD', hA, X.tgt_comp _ _ hφB]
  rw [hL, hR, hwy, ← hΓ', ← hΓ,
    X.comp_assoc A (X.comp φ B) D hA hφBD, X.comp_assoc φ B D hφB hBD,
    ← X.comp_assoc C A _ hC hA']

/-- `g'⁻¹ ∗ (g' ∗ φ ∗ g) ∗ g⁻¹ = φ`. -/
theorem biact_inv_biact (g' : X.Isotropy x') (g : X.Isotropy x) :
    biact N N' g'⁻¹ (biact N N' g' φ g) g⁻¹ = φ := by
  rw [biact_biact hφ, inv_mul_cancel, mul_inv_cancel, biact_one_one hφ]

/-- **Cancellation on the left**: `a ∗ φ ∗ b = a' ∗ φ ∗ b` forces `a = a'`. -/
theorem biact_left_cancel {a a' : X.Isotropy x'} {b : X.Isotropy x}
    (h : biact N N' a φ b = biact N N' a' φ b) : a = a' := by
  have h1 := GroupoidStr.comp_right_cancel (G := X.toGroupoidStr) (compat hφ a b)
    (compat hφ a' b) h
  exact (N'.Γ_inj hφ.2).1 h1

/-- **Cancellation on the right**: `a ∗ φ ∗ b = a ∗ φ ∗ b'` forces `b = b'`. -/
theorem biact_right_cancel {a : X.Isotropy x'} {b b' : X.Isotropy x}
    (h : biact N N' a φ b = biact N N' a φ b') : b = b' := by
  have h1 := GroupoidStr.comp_left_cancel (G := X.toGroupoidStr) (compat hφ a b)
    (compat hφ a b') h
  have hs : N.rep.Φ b⁻¹ (X.src φ) = N.rep.Φ b'⁻¹ (X.src φ) := by
    rw [← src_inner hφ b, ← src_inner hφ b', h1]
  have h2 := GroupoidStr.comp_left_cancel (G := X.toGroupoidStr) (tgt_Γy hφ b).symm
    (tgt_Γy hφ b').symm h1
  rw [hs] at h2
  exact (N.Γ_inj (hs ▸ mem_y hφ b')).1 h2

end Laws

/-- `φ ∗ g = (g⁻¹ ∗ φ⁻¹)⁻¹`: the right action through the inverse map. -/
theorem biact_one_left_eq_inv {φ : Mor} (hφ : X.src φ ∈ N.U) (g : X.Isotropy x) :
    X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (X.src φ))) =
      X.inv (X.comp (N.rep.Γ g⁻¹ (X.tgt (X.inv φ))) (X.inv φ)) := by
  have hy : N.rep.Φ g⁻¹ (X.src φ) ∈ N.U := N.Φ_mem g⁻¹ hφ
  have h1 : N.rep.Γ g (N.rep.Φ g⁻¹ (X.src φ)) = X.inv (N.rep.Γ g⁻¹ (X.src φ)) := by
    have := N.Γ_inv g⁻¹ hφ
    rwa [inv_inv] at this
  have hc : X.src (N.rep.Γ g⁻¹ (X.src φ)) = X.tgt (X.inv φ) := by
    rw [N.src_Γ g⁻¹ hφ, X.tgt_inv]
  rw [X.tgt_inv, GroupoidStr.inv_comp_rev (G := X.toGroupoidStr) hc, GroupoidStr.inv_inv, h1]

/-- **The bi-action is sc-smooth** on `𝒰(x, x')` for fixed `g', g` (Definition 13.1.5). -/
theorem isScSmoothOn_biact (g' : X.Isotropy x') (g : X.Isotropy x) :
    X.PMor.IsScSmoothOn X.PMor (fun φ => biact N N' g' φ g) (X.morBetween N.U N'.U) := by
  have hM := isOpen_morBetween (X := X) N.isOpen_U N'.isOpen_U
  -- the right action `φ ↦ (g⁻¹ ∗ φ⁻¹)⁻¹`
  have hinv := X.isScSmoothMap_inv
  have hleft := N.rep.isScSmoothOn_comp_Γ_tgt g⁻¹
  have hR : X.PMor.IsScSmoothOn X.PMor
      (fun φ => X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (X.src φ)))) (X.morBetween N.U N'.U) := by
    have h1 : X.PMor.IsScSmoothOn X.PMor X.inv (X.morBetween N.U N'.U) :=
      hinv.mono hM (subset_univ _)
    have h2 := MPolyfold.IsScSmoothOn.comp hleft h1 fun φ hφ => by
      change X.tgt (X.inv φ) ∈ N.rep.U
      rw [X.tgt_inv]
      exact N.U_subset hφ.1
    have h3 := MPolyfold.IsScSmoothOn.comp (hinv.mono isOpen_univ (subset_univ _)) h2
      (mapsTo_univ _ _)
    exact h3.congr fun φ hφ => (biact_one_left_eq_inv hφ.1 g).symm
  have hL := N'.rep.isScSmoothOn_comp_Γ_tgt g'
  refine (MPolyfold.IsScSmoothOn.comp hL hR fun φ hφ => ?_).congr fun φ hφ => ?_
  · change X.tgt (X.comp φ _) ∈ N'.rep.U
    rw [tgt_inner hφ]
    exact N'.U_subset hφ.2
  · simp only [Function.comp_apply, biact, tgt_inner hφ]

theorem continuousOn_biact (g' : X.Isotropy x') (g : X.Isotropy x) :
    ContinuousOn (fun φ => biact N N' g' φ g) (X.morBetween N.U N'.U) :=
  (isScSmoothOn_biact g' g).continuousOn

variable (N N') in
/-- **Definition 13.1.5, as a `MulAction`**: the commuting left action of `G_{x'}` and right
action of `G_x` on `𝒰(x, x')`, as an action of `G_{x'} × G_xᵐᵒᵖ`. -/
@[reducible] def biactMulAction :
    MulAction (X.Isotropy x' × (X.Isotropy x)ᵐᵒᵖ) (X.morBetween N.U N'.U) where
  smul p φ := ⟨biact N N' p.1 φ (unop p.2), biact_mem φ.2 p.1 (unop p.2)⟩
  one_smul φ := Subtype.ext (biact_one_one φ.2)
  mul_smul p q φ := Subtype.ext (by
    change biact N N' (p.1 * q.1) φ.1 (unop (p.2 * q.2)) =
      biact N N' p.1 (biact N N' q.1 φ.1 (unop q.2)) (unop p.2)
    rw [biact_biact φ.2, unop_mul])

end BiAction

/-! ### The bi-action on the components of a good system -/

namespace GoodSystem

variable (𝒰 : X.GoodSystem)

/-- The natural bi-action of `G_{x'} × G_x` on `𝒰(x, x')` for the good system `𝒰`. -/
def biact (x x' : Obj) (g' : X.Isotropy x') (φ : Mor) (g : X.Isotropy x) : Mor :=
  EpGroupoid.biact (𝒰.nbhd x) (𝒰.nbhd x') g' φ g

variable {𝒰}

theorem biact_mem {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') (g' : X.Isotropy x')
    (g : X.Isotropy x) : 𝒰.biact x x' g' φ g ∈ 𝒰.mor x x' :=
  EpGroupoid.biact_mem hφ g' g

theorem src_biact {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') (g' : X.Isotropy x')
    (g : X.Isotropy x) : X.src (𝒰.biact x x' g' φ g) = (𝒰.nbhd x).rep.Φ g⁻¹ (X.src φ) :=
  EpGroupoid.src_biact hφ g' g

theorem tgt_biact {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') (g' : X.Isotropy x')
    (g : X.Isotropy x) : X.tgt (𝒰.biact x x' g' φ g) = (𝒰.nbhd x').rep.Φ g' (X.tgt φ) :=
  EpGroupoid.tgt_biact hφ g' g

/-- **`g' ∗ Σ ∗ g` is a connected component** (p. 602): the image of the component of `φ` is
the component of `g' ∗ φ ∗ g`. -/
theorem image_biact_comp {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') (g' : X.Isotropy x')
    (g : X.Isotropy x) :
    (fun ψ => 𝒰.biact x x' g' ψ g) '' 𝒰.comp x x' φ = 𝒰.comp x x' (𝒰.biact x x' g' φ g) := by
  have hmaps : ∀ (a : X.Isotropy x') (b : X.Isotropy x),
      (fun ψ => 𝒰.biact x x' a ψ b) '' 𝒰.comp x x' φ ⊆ 𝒰.comp x x' (𝒰.biact x x' a φ b) := by
    intro a b
    refine IsPreconnected.subset_connectedComponentIn
      ((𝒰.isConnected_comp hφ).isPreconnected.image _
        ((continuousOn_biact a b).mono (𝒰.comp_subset x x' φ)))
      ⟨φ, 𝒰.mem_comp hφ, rfl⟩ ?_
    rintro _ ⟨ψ, hψ, rfl⟩
    exact biact_mem (𝒰.comp_subset x x' φ hψ) a b
  refine (hmaps g' g).antisymm fun ψ hψ => ?_
  have hφ' : 𝒰.biact x x' g' φ g ∈ 𝒰.mor x x' := biact_mem hφ g' g
  have hψM : ψ ∈ 𝒰.mor x x' := 𝒰.comp_subset x x' _ hψ
  -- apply the inverse action
  have hback : (fun χ => 𝒰.biact x x' g'⁻¹ χ g⁻¹) '' 𝒰.comp x x' (𝒰.biact x x' g' φ g) ⊆
      𝒰.comp x x' φ := by
    have h := (show (fun χ => 𝒰.biact x x' g'⁻¹ χ g⁻¹) '' 𝒰.comp x x' (𝒰.biact x x' g' φ g) ⊆
        𝒰.comp x x' (𝒰.biact x x' g'⁻¹ (𝒰.biact x x' g' φ g) g⁻¹) from by
      refine IsPreconnected.subset_connectedComponentIn
        ((𝒰.isConnected_comp hφ').isPreconnected.image _
          ((continuousOn_biact g'⁻¹ g⁻¹).mono (𝒰.comp_subset x x' _)))
        ⟨_, 𝒰.mem_comp hφ', rfl⟩ ?_
      rintro _ ⟨χ, hχ, rfl⟩
      exact biact_mem (𝒰.comp_subset x x' _ hχ) _ _)
    rwa [show 𝒰.biact x x' g'⁻¹ (𝒰.biact x x' g' φ g) g⁻¹ = φ from biact_inv_biact hφ g' g] at h
  refine ⟨𝒰.biact x x' g'⁻¹ ψ g⁻¹, hback ⟨ψ, hψ, rfl⟩, ?_⟩
  change 𝒰.biact x x' g' (𝒰.biact x x' g'⁻¹ ψ g⁻¹) g = ψ
  have := biact_inv_biact hψM g'⁻¹ g⁻¹
  rwa [inv_inv, inv_inv] at this

/-- If `g' ∗ ψ ∗ g ∈ Σ` for one `ψ ∈ Σ`, then `g' ∗ Σ ∗ g = Σ`. -/
theorem image_biact_comp_of_mem {x x' : Obj} {φ ψ : Mor}
    (hψ : ψ ∈ 𝒰.comp x x' φ) {g' : X.Isotropy x'} {g : X.Isotropy x}
    (h : 𝒰.biact x x' g' ψ g ∈ 𝒰.comp x x' φ) :
    (fun χ => 𝒰.biact x x' g' χ g) '' 𝒰.comp x x' φ = 𝒰.comp x x' φ := by
  rw [← 𝒰.comp_eq hψ, image_biact_comp (𝒰.comp_subset x x' φ hψ), 𝒰.comp_eq hψ, 𝒰.comp_eq h]

/-- **Components with overlapping source sets differ by the left action** (proof of Lemma
13.1.6 (3)): if `s(ψ₁) = s(ψ₂)` then `g' ∗ ψ₁ ∗ 1 = ψ₂` for some `g' ∈ G_{x'}`. -/
theorem exists_biact_left_of_src {x x' : Obj} {ψ₁ ψ₂ : Mor} (h₁ : ψ₁ ∈ 𝒰.mor x x')
    (h₂ : ψ₂ ∈ 𝒰.mor x x') (hs : X.src ψ₁ = X.src ψ₂) :
    ∃ g' : X.Isotropy x', 𝒰.biact x x' g' ψ₁ 1 = ψ₂ := by
  set χ := X.comp ψ₂ (X.inv ψ₁)
  have hc : X.src ψ₂ = X.tgt (X.inv ψ₁) := by rw [X.tgt_inv, hs]
  have hχs : X.src χ = X.tgt ψ₁ := by rw [X.src_comp _ _ hc, X.src_inv]
  have hχt : X.tgt χ = X.tgt ψ₂ := X.tgt_comp _ _ hc
  obtain ⟨g', hg'⟩ := (𝒰.nbhd x').exists_Γ_eq (φ := χ) (hχs ▸ h₁.2) (hχt ▸ h₂.2)
  refine ⟨g', ?_⟩
  change EpGroupoid.biact (𝒰.nbhd x) (𝒰.nbhd x') g' ψ₁ 1 = ψ₂
  rw [EpGroupoid.biact_one_right h₁, ← hχs, hg', X.comp_assoc _ _ _ hc (X.src_inv ψ₁),
    X.inv_comp, GroupoidStr.comp_unit_of_eq (hs.symm)]

/-- **Components with overlapping target sets differ by the right action**: if
`t(ψ₁) = t(ψ₂)` then `1 ∗ ψ₁ ∗ g = ψ₂` for some `g ∈ G_x`. -/
theorem exists_biact_right_of_tgt {x x' : Obj} {ψ₁ ψ₂ : Mor} (h₁ : ψ₁ ∈ 𝒰.mor x x')
    (h₂ : ψ₂ ∈ 𝒰.mor x x') (ht : X.tgt ψ₁ = X.tgt ψ₂) :
    ∃ g : X.Isotropy x, 𝒰.biact x x' 1 ψ₁ g = ψ₂ := by
  set χ := X.comp (X.inv ψ₁) ψ₂
  have hc : X.src (X.inv ψ₁) = X.tgt ψ₂ := by rw [X.src_inv, ht]
  have hχs : X.src χ = X.src ψ₂ := X.src_comp _ _ hc
  have hχt : X.tgt χ = X.src ψ₁ := by rw [X.tgt_comp _ _ hc, X.tgt_inv]
  obtain ⟨g, hg⟩ := (𝒰.nbhd x).exists_Γ_eq (φ := χ) (hχs ▸ h₂.1) (hχt ▸ h₁.1)
  have hy : (𝒰.nbhd x).rep.Φ g⁻¹ (X.src ψ₁) = X.src ψ₂ := by
    have h1 : (𝒰.nbhd x).rep.Φ g (X.src χ) = X.src ψ₁ := by
      rw [← (𝒰.nbhd x).tgt_Γ g (hχs ▸ h₂.1), hg, hχt]
    rw [← h1, (𝒰.nbhd x).Φ_inv_Φ g (hχs ▸ h₂.1), hχs]
  refine ⟨g, ?_⟩
  change EpGroupoid.biact (𝒰.nbhd x) (𝒰.nbhd x') 1 ψ₁ g = ψ₂
  rw [EpGroupoid.biact_one_left h₁, hy, ← hχs, hg,
    ← X.comp_assoc _ _ _ (X.tgt_inv ψ₁).symm hc, X.comp_inv,
    GroupoidStr.unit_comp_of_eq ht.symm]

/-! ### The set of components and inversion -/

variable (𝒰) in
/-- The connected components of `𝒰(x, x')`. -/
def components (x x' : Obj) : Set (Set Mor) := {C | ∃ φ ∈ 𝒰.mor x x', 𝒰.comp x x' φ = C}

theorem comp_mem_components {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') :
    𝒰.comp x x' φ ∈ 𝒰.components x x' := ⟨φ, hφ, rfl⟩

/-- The components cover `𝒰(x, x')`. -/
theorem sUnion_components (x x' : Obj) : ⋃₀ 𝒰.components x x' = 𝒰.mor x x' := by
  refine subset_antisymm ?_ fun φ hφ => ⟨_, comp_mem_components hφ, 𝒰.mem_comp hφ⟩
  rintro ψ ⟨_, ⟨φ, -, rfl⟩, hψ⟩
  exact 𝒰.comp_subset x x' φ hψ

/-- Distinct components are disjoint. -/
theorem pairwiseDisjoint_components (x x' : Obj) :
    (𝒰.components x x').PairwiseDisjoint id := by
  rintro _ ⟨φ, -, rfl⟩ _ ⟨ψ, -, rfl⟩ hne
  refine Set.disjoint_left.2 fun χ h₁ h₂ => hne ?_
  rw [← 𝒰.comp_eq h₁, 𝒰.comp_eq h₂]

/-- **Inversion carries components to components**: `Σ⁻¹ = {φ⁻¹ | φ ∈ Σ}` is the component of
`φ⁻¹` in `𝒰(x', x)`. -/
theorem image_inv_comp {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') :
    X.inv '' 𝒰.comp x x' φ = 𝒰.comp x' x (X.inv φ) := by
  have hinvM : ∀ {a b : Obj} {ψ : Mor}, ψ ∈ 𝒰.mor a b → X.inv ψ ∈ 𝒰.mor b a :=
    fun hψ => ⟨by rw [X.src_inv]; exact hψ.2, by rw [X.tgt_inv]; exact hψ.1⟩
  have hsub : ∀ {a b : Obj} {ψ : Mor}, ψ ∈ 𝒰.mor a b →
      X.inv '' 𝒰.comp a b ψ ⊆ 𝒰.comp b a (X.inv ψ) := fun {a b ψ} hψ =>
    ((𝒰.isConnected_comp hψ).isPreconnected.image _
      X.continuous_inv.continuousOn).subset_connectedComponentIn
      ⟨ψ, 𝒰.mem_comp hψ, rfl⟩ (by
        rintro _ ⟨χ, hχ, rfl⟩
        exact hinvM (𝒰.comp_subset a b ψ hχ))
  refine (hsub hφ).antisymm fun ψ hψ => ⟨X.inv ψ, ?_, GroupoidStr.inv_inv ψ⟩
  have h := hsub (hinvM hφ) ⟨ψ, hψ, rfl⟩
  rwa [GroupoidStr.inv_inv] at h

/-! ### Lemma 13.1.6 -/

/-- **Lemma 13.1.6 (1), pointwise**: if `ψ ∈ Σ` and `g' ∗ ψ ∈ Σ`, then `g' = 1`. -/
theorem eq_one_of_biact_left_mem {x x' : Obj} {φ ψ : Mor} (hφ : φ ∈ 𝒰.mor x x')
    (hψ : ψ ∈ 𝒰.comp x x' φ) {g' : X.Isotropy x'} (h : 𝒰.biact x x' g' ψ 1 ∈ 𝒰.comp x x' φ) :
    g' = 1 := by
  have hψM := 𝒰.comp_subset x x' φ hψ
  have hs : X.src (𝒰.biact x x' g' ψ 1) = X.src ψ := by
    rw [src_biact hψM, inv_one, (𝒰.nbhd x).Φ_one hψM.1]
  have he := 𝒰.injOn_src_comp hφ h hψ hs
  have he' : 𝒰.biact x x' g' ψ 1 = 𝒰.biact x x' 1 ψ 1 := by
    rw [he]
    exact (EpGroupoid.biact_one_one hψM).symm
  exact EpGroupoid.biact_left_cancel hψM he'

/-- **Lemma 13.1.6 (2), pointwise**: if `ψ ∈ Σ` and `ψ ∗ g ∈ Σ`, then `g = 1`. -/
theorem eq_one_of_biact_right_mem {x x' : Obj} {φ ψ : Mor} (hφ : φ ∈ 𝒰.mor x x')
    (hψ : ψ ∈ 𝒰.comp x x' φ) {g : X.Isotropy x} (h : 𝒰.biact x x' 1 ψ g ∈ 𝒰.comp x x' φ) :
    g = 1 := by
  have hψM := 𝒰.comp_subset x x' φ hψ
  have ht : X.tgt (𝒰.biact x x' 1 ψ g) = X.tgt ψ := by
    rw [tgt_biact hψM, (𝒰.nbhd x').Φ_one hψM.2]
  have he := 𝒰.injOn_tgt_comp hφ h hψ ht
  have he' : 𝒰.biact x x' 1 ψ g = 𝒰.biact x x' 1 ψ 1 := by
    rw [he]
    exact (EpGroupoid.biact_one_one hψM).symm
  exact EpGroupoid.biact_right_cancel hψM he'

/-- **Lemma 13.1.6 (1) (p. 602; 2017: Lemma 13.2)**: if `g' ∗ Σ = Σ` then `g' = 1_{x'}`. -/
theorem lemma_13_1_6_one {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') {g' : X.Isotropy x'}
    (h : (fun ψ => 𝒰.biact x x' g' ψ 1) '' 𝒰.comp x x' φ = 𝒰.comp x x' φ) : g' = 1 :=
  eq_one_of_biact_left_mem hφ (𝒰.mem_comp hφ) (h ▸ mem_image_of_mem _ (𝒰.mem_comp hφ))

/-- **Lemma 13.1.6 (2)**: if `Σ ∗ g = Σ` then `g = 1_x`. -/
theorem lemma_13_1_6_two {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') {g : X.Isotropy x}
    (h : (fun ψ => 𝒰.biact x x' 1 ψ g) '' 𝒰.comp x x' φ = 𝒰.comp x x' φ) : g = 1 :=
  eq_one_of_biact_right_mem hφ (𝒰.mem_comp hφ) (h ▸ mem_image_of_mem _ (𝒰.mem_comp hφ))

/-- **Lemma 13.1.6 (3), for `s`**: the source sets of two connected components of `𝒰(x, x')`
are equal or disjoint. -/
theorem lemma_13_1_6_three_src {x x' : Obj} (φ₁ φ₂ : Mor) :
    X.src '' 𝒰.comp x x' φ₁ = X.src '' 𝒰.comp x x' φ₂ ∨
      Disjoint (X.src '' 𝒰.comp x x' φ₁) (X.src '' 𝒰.comp x x' φ₂) := by
  rw [or_iff_not_imp_right, not_disjoint_iff]
  rintro ⟨_, ⟨ψ₁, hψ₁, rfl⟩, ψ₂, hψ₂, hs⟩
  have hψ₁M := 𝒰.comp_subset x x' φ₁ hψ₁
  obtain ⟨g', hg'⟩ := exists_biact_left_of_src hψ₁M (𝒰.comp_subset x x' φ₂ hψ₂) hs.symm
  have himg : (fun ψ => 𝒰.biact x x' g' ψ 1) '' 𝒰.comp x x' φ₁ = 𝒰.comp x x' φ₂ := by
    rw [← 𝒰.comp_eq hψ₁, image_biact_comp hψ₁M, hg', 𝒰.comp_eq hψ₂]
  rw [← himg, image_image]
  refine image_congr fun ψ hψ => ?_
  rw [src_biact (𝒰.comp_subset x x' φ₁ hψ), inv_one,
    (𝒰.nbhd x).Φ_one (𝒰.comp_subset x x' φ₁ hψ).1]

/-- **Lemma 13.1.6 (3), for `t`**: the target sets of two connected components of `𝒰(x, x')`
are equal or disjoint. -/
theorem lemma_13_1_6_three_tgt {x x' : Obj} (φ₁ φ₂ : Mor) :
    X.tgt '' 𝒰.comp x x' φ₁ = X.tgt '' 𝒰.comp x x' φ₂ ∨
      Disjoint (X.tgt '' 𝒰.comp x x' φ₁) (X.tgt '' 𝒰.comp x x' φ₂) := by
  rw [or_iff_not_imp_right, not_disjoint_iff]
  rintro ⟨_, ⟨ψ₁, hψ₁, rfl⟩, ψ₂, hψ₂, ht⟩
  have hψ₁M := 𝒰.comp_subset x x' φ₁ hψ₁
  obtain ⟨g, hg⟩ := exists_biact_right_of_tgt hψ₁M (𝒰.comp_subset x x' φ₂ hψ₂) ht.symm
  have himg : (fun ψ => 𝒰.biact x x' 1 ψ g) '' 𝒰.comp x x' φ₁ = 𝒰.comp x x' φ₂ := by
    rw [← 𝒰.comp_eq hψ₁, image_biact_comp hψ₁M, hg, 𝒰.comp_eq hψ₂]
  rw [← himg, image_image]
  refine image_congr fun ψ hψ => ?_
  rw [tgt_biact (𝒰.comp_subset x x' φ₁ hψ), (𝒰.nbhd x').Φ_one (𝒰.comp_subset x x' φ₁ hψ).2]

/-! ### Proposition 13.1.9 -/

variable (𝒰)

/-- **`G_{x,Σ}`** (p. 606): the `g ∈ G_x` with `g ∗ s(Σ) = s(Σ)`. -/
def stabSrc (x x' : Obj) (φ : Mor) : Subgroup (X.Isotropy x) where
  carrier := {g | (𝒰.nbhd x).rep.Φ g '' (X.src '' 𝒰.comp x x' φ) = X.src '' 𝒰.comp x x' φ}
  one_mem' := by
    refine (image_congr fun z hz => ?_).trans (image_id _)
    exact (𝒰.nbhd x).Φ_one (𝒰.src_comp_subset x x' φ hz)
  mul_mem' {g h} hg hh := by
    change _ '' _ = _ at hg hh ⊢
    calc (𝒰.nbhd x).rep.Φ (g * h) '' (X.src '' 𝒰.comp x x' φ)
        = (𝒰.nbhd x).rep.Φ g '' ((𝒰.nbhd x).rep.Φ h '' (X.src '' 𝒰.comp x x' φ)) :=
          (image_congr fun z hz => (𝒰.nbhd x).Φ_mul g h
            (𝒰.src_comp_subset x x' φ hz)).trans (image_comp _ _ _)
      _ = X.src '' 𝒰.comp x x' φ := by rw [hh, hg]
  inv_mem' {g} hg := by
    change _ '' _ = _ at hg ⊢
    conv_lhs => rw [← hg]
    rw [image_image]
    refine (image_congr fun z hz => ?_).trans (image_id _)
    exact (𝒰.nbhd x).Φ_inv_Φ g (𝒰.src_comp_subset x x' φ hz)

/-- **`G_{x',Σ}`** (p. 606): the `g' ∈ G_{x'}` with `g' ∗ t(Σ) = t(Σ)`. -/
def stabTgt (x x' : Obj) (φ : Mor) : Subgroup (X.Isotropy x') where
  carrier := {g | (𝒰.nbhd x').rep.Φ g '' (X.tgt '' 𝒰.comp x x' φ) = X.tgt '' 𝒰.comp x x' φ}
  one_mem' := by
    refine (image_congr fun z hz => ?_).trans (image_id _)
    exact (𝒰.nbhd x').Φ_one (𝒰.tgt_comp_subset x x' φ hz)
  mul_mem' {g h} hg hh := by
    change _ '' _ = _ at hg hh ⊢
    calc (𝒰.nbhd x').rep.Φ (g * h) '' (X.tgt '' 𝒰.comp x x' φ)
        = (𝒰.nbhd x').rep.Φ g '' ((𝒰.nbhd x').rep.Φ h '' (X.tgt '' 𝒰.comp x x' φ)) :=
          (image_congr fun z hz => (𝒰.nbhd x').Φ_mul g h
            (𝒰.tgt_comp_subset x x' φ hz)).trans (image_comp _ _ _)
      _ = X.tgt '' 𝒰.comp x x' φ := by rw [hh, hg]
  inv_mem' {g} hg := by
    change _ '' _ = _ at hg ⊢
    conv_lhs => rw [← hg]
    rw [image_image]
    refine (image_congr fun z hz => ?_).trans (image_id _)
    exact (𝒰.nbhd x').Φ_inv_Φ g (𝒰.tgt_comp_subset x x' φ hz)

/-- **`D_Σ = t ∘ (s|Σ)⁻¹ : s(Σ) → t(Σ)`** (p. 606). -/
def D (x x' : Obj) (φ : Mor) (z : Obj) : Obj := X.tgt (𝒰.srcInv x x' φ z)

variable {𝒰}

/-- **`D_Σ : s(Σ) → t(Σ)` is an sc-diffeomorphism** (p. 606), with inverse `s ∘ (t|Σ)⁻¹`. -/
theorem isScDiffeoOn_D {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') :
    X.PObj.IsScDiffeoOn X.PObj (𝒰.D x x' φ) (fun z => X.src (𝒰.tgtInv x x' φ z))
      (X.src '' 𝒰.comp x x' φ) (X.tgt '' 𝒰.comp x x' φ) :=
  (𝒰.isScDiffeoOn_tgt_comp hφ).comp (𝒰.isScDiffeoOn_src_comp hφ).symm

section Prop1319

variable {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x')
include hφ

/-- For `g ∈ G_{x,Σ}` there is `g'` with `g' ∗ Σ ∗ g⁻¹ = Σ`. -/
theorem exists_biact_mem_of_stabSrc (g : 𝒰.stabSrc x x' φ) :
    ∃ g' : X.Isotropy x', 𝒰.biact x x' g' φ (g : X.Isotropy x)⁻¹ ∈ 𝒰.comp x x' φ := by
  have hφM := hφ
  have h1 : 𝒰.biact x x' 1 φ (g : X.Isotropy x)⁻¹ ∈ 𝒰.mor x x' := biact_mem hφ 1 _
  have hs : X.src (𝒰.biact x x' 1 φ (g : X.Isotropy x)⁻¹) ∈ X.src '' 𝒰.comp x x' φ := by
    rw [src_biact hφ, inv_inv, ← g.2]
    exact mem_image_of_mem _ (mem_image_of_mem _ (𝒰.mem_comp hφ))
  obtain ⟨ψ, hψ, hψs⟩ := hs
  obtain ⟨g', hg'⟩ := exists_biact_left_of_src h1 (𝒰.comp_subset x x' φ hψ) hψs.symm
  refine ⟨g', ?_⟩
  have := EpGroupoid.biact_biact hφM (N := 𝒰.nbhd x) (N' := 𝒰.nbhd x') g' 1
    (g : X.Isotropy x)⁻¹ 1
  rw [mul_one, mul_one] at this
  change EpGroupoid.biact _ _ g' φ _ ∈ _
  rw [← this]
  change 𝒰.biact x x' g' (𝒰.biact x x' 1 φ _) 1 ∈ _
  rw [hg']
  exact hψ

/-- The left partner is unique: `a ∗ ψ ∗ b ∈ Σ` and `a' ∗ ψ ∗ b ∈ Σ` for `ψ ∈ Σ` force
`a = a'`. -/
theorem left_unique {ψ : Mor} (hψ : ψ ∈ 𝒰.comp x x' φ) {a a' : X.Isotropy x'}
    {b : X.Isotropy x} (ha : 𝒰.biact x x' a ψ b ∈ 𝒰.comp x x' φ)
    (ha' : 𝒰.biact x x' a' ψ b ∈ 𝒰.comp x x' φ) : a = a' := by
  have hψM := 𝒰.comp_subset x x' φ hψ
  refine EpGroupoid.biact_left_cancel hψM (𝒰.injOn_src_comp hφ ha ha' ?_)
  rw [src_biact hψM a b]
  exact (src_biact hψM a' b).symm

/-- The right partner is unique: `a ∗ ψ ∗ b ∈ Σ` and `a ∗ ψ ∗ b' ∈ Σ` for `ψ ∈ Σ` force
`b = b'`. -/
theorem right_unique {ψ : Mor} (hψ : ψ ∈ 𝒰.comp x x' φ) {a : X.Isotropy x'}
    {b b' : X.Isotropy x} (hb : 𝒰.biact x x' a ψ b ∈ 𝒰.comp x x' φ)
    (hb' : 𝒰.biact x x' a ψ b' ∈ 𝒰.comp x x' φ) : b = b' := by
  have hψM := 𝒰.comp_subset x x' φ hψ
  refine EpGroupoid.biact_right_cancel hψM (𝒰.injOn_tgt_comp hφ hb hb' ?_)
  rw [tgt_biact hψM a b]
  exact (tgt_biact hψM a b').symm

/-- `g' ∗ Σ ∗ g ⊆ Σ` as soon as `g' ∗ φ ∗ g ∈ Σ`. -/
theorem biact_mem_comp_of {ψ : Mor} (hψ : ψ ∈ 𝒰.comp x x' φ) {a : X.Isotropy x'}
    {b : X.Isotropy x} (h : 𝒰.biact x x' a φ b ∈ 𝒰.comp x x' φ) :
    𝒰.biact x x' a ψ b ∈ 𝒰.comp x x' φ := by
  rw [← image_biact_comp_of_mem (𝒰.mem_comp hφ) h]
  exact mem_image_of_mem _ hψ

/-- The partner `g'(g)` of `g ∈ G_{x,Σ}`. -/
def partner (g : 𝒰.stabSrc x x' φ) : X.Isotropy x' :=
  (exists_biact_mem_of_stabSrc hφ g).choose

theorem partner_spec (g : 𝒰.stabSrc x x' φ) :
    𝒰.biact x x' (partner hφ g) φ (g : X.Isotropy x)⁻¹ ∈ 𝒰.comp x x' φ :=
  (exists_biact_mem_of_stabSrc hφ g).choose_spec

theorem partner_mem_stabTgt (g : 𝒰.stabSrc x x' φ) : partner hφ g ∈ 𝒰.stabTgt x x' φ := by
  have himg := image_biact_comp_of_mem (𝒰.mem_comp hφ) (partner_spec hφ g)
  change _ '' _ = _
  calc (𝒰.nbhd x').rep.Φ (partner hφ g) '' (X.tgt '' 𝒰.comp x x' φ)
      = X.tgt '' ((fun χ => 𝒰.biact x x' (partner hφ g) χ (g : X.Isotropy x)⁻¹) ''
          𝒰.comp x x' φ) := by
        rw [image_image, image_image]
        exact image_congr fun ψ hψ =>
          (tgt_biact (𝒰.comp_subset x x' φ hψ) (partner hφ g) (g : X.Isotropy x)⁻¹).symm
    _ = X.tgt '' 𝒰.comp x x' φ := by rw [himg]

/-- `g'(g) ∗ ψ ∗ g⁻¹ = ψ'` with the unique `ψ' ∈ Σ` over `g ∗ s(ψ)`. -/
theorem partner_identity (g : 𝒰.stabSrc x x' φ) {z : Obj} (hz : z ∈ X.src '' 𝒰.comp x x' φ) :
    𝒰.srcInv x x' φ ((𝒰.nbhd x).rep.Φ g z) =
      𝒰.biact x x' (partner hφ g) (𝒰.srcInv x x' φ z) (g : X.Isotropy x)⁻¹ := by
  have hψ := 𝒰.srcInv_mem hφ hz
  have hψM := 𝒰.comp_subset x x' φ hψ
  have hgz : (𝒰.nbhd x).rep.Φ g z ∈ X.src '' 𝒰.comp x x' φ := by
    rw [← g.2]; exact mem_image_of_mem _ hz
  refine 𝒰.injOn_src_comp hφ (𝒰.srcInv_mem hφ hgz)
    (biact_mem_comp_of hφ hψ (partner_spec hφ g)) ?_
  rw [𝒰.src_srcInv hφ hgz, src_biact hψM, inv_inv, 𝒰.src_srcInv hφ hz]

/-- `g ↦ g'(g)` as a monoid homomorphism `G_{x,Σ} → G_{x',Σ}`. -/
def partnerHom : 𝒰.stabSrc x x' φ →* 𝒰.stabTgt x x' φ where
  toFun g := ⟨partner hφ g, partner_mem_stabTgt hφ g⟩
  map_one' := by
    refine Subtype.ext (left_unique hφ (𝒰.mem_comp hφ) (partner_spec hφ 1) ?_)
    change 𝒰.biact x x' 1 φ (1 : X.Isotropy x)⁻¹ ∈ _
    rw [inv_one]
    change EpGroupoid.biact _ _ 1 φ 1 ∈ _
    rw [EpGroupoid.biact_one_one hφ]
    exact 𝒰.mem_comp hφ
  map_mul' g h := by
    refine Subtype.ext (left_unique hφ (𝒰.mem_comp hφ) (partner_spec hφ (g * h)) ?_)
    change 𝒰.biact x x' (partner hφ g * partner hφ h) φ ((g : X.Isotropy x) * h)⁻¹ ∈ _
    have hb := EpGroupoid.biact_biact hφ (N := 𝒰.nbhd x) (N' := 𝒰.nbhd x') (partner hφ g)
      (partner hφ h) (h : X.Isotropy x)⁻¹ (g : X.Isotropy x)⁻¹
    rw [mul_inv_rev]
    change _ = EpGroupoid.biact _ _ _ φ _ at hb
    change EpGroupoid.biact _ _ _ φ _ ∈ _
    rw [← hb]
    exact biact_mem_comp_of hφ (partner_spec hφ h) (partner_spec hφ g)

/-- For `g' ∈ G_{x',Σ}` there is `g ∈ G_{x,Σ}` with `g' ∗ Σ ∗ g⁻¹ = Σ`. -/
theorem exists_stabSrc_of_stabTgt (g' : 𝒰.stabTgt x x' φ) :
    ∃ g : 𝒰.stabSrc x x' φ, 𝒰.biact x x' (g' : X.Isotropy x') φ (g : X.Isotropy x)⁻¹ ∈
      𝒰.comp x x' φ := by
  have h1 : 𝒰.biact x x' (g' : X.Isotropy x') φ 1 ∈ 𝒰.mor x x' := biact_mem hφ _ 1
  have ht : X.tgt (𝒰.biact x x' (g' : X.Isotropy x') φ 1) ∈ X.tgt '' 𝒰.comp x x' φ := by
    rw [tgt_biact hφ, ← g'.2]
    exact mem_image_of_mem _ (mem_image_of_mem _ (𝒰.mem_comp hφ))
  obtain ⟨ψ, hψ, hψt⟩ := ht
  obtain ⟨k, hk⟩ := exists_biact_right_of_tgt h1 (𝒰.comp_subset x x' φ hψ) hψt.symm
  have hmem : 𝒰.biact x x' (g' : X.Isotropy x') φ k ∈ 𝒰.comp x x' φ := by
    have := EpGroupoid.biact_biact hφ (N := 𝒰.nbhd x) (N' := 𝒰.nbhd x') 1
      (g' : X.Isotropy x') 1 k
    rw [one_mul, one_mul] at this
    change EpGroupoid.biact _ _ _ φ k ∈ _
    rw [← this]
    change 𝒰.biact x x' 1 (𝒰.biact x x' _ φ 1) k ∈ _
    rw [hk]
    exact hψ
  -- `k⁻¹ ∈ G_{x,Σ}`
  have himg := image_biact_comp_of_mem (𝒰.mem_comp hφ) hmem
  have hk' : k⁻¹ ∈ 𝒰.stabSrc x x' φ := by
    change _ '' _ = _
    conv_rhs => rw [← himg]
    rw [image_image, image_image]
    refine image_congr fun ψ hψ => ?_
    rw [src_biact (𝒰.comp_subset x x' φ hψ)]
  exact ⟨⟨k⁻¹, hk'⟩, by simpa using hmem⟩

end Prop1319

/-- **Proposition 13.1.9 (p. 607; 2017: Proposition 13.2)**: for a connected component
`Σ ∋ φ` of `𝒰(x, x')` there is a group isomorphism `f : G_{x,Σ} → G_{x',Σ}` with
`(s|Σ)⁻¹(g ∗ z) = f(g) ∗ (s|Σ)⁻¹(z) ∗ g⁻¹` for all `z ∈ s(Σ)`, and it is the only map
`G_{x,Σ} → G_{x',Σ}` with this property. -/
theorem proposition_13_1_9 {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') :
    ∃ f : 𝒰.stabSrc x x' φ ≃* 𝒰.stabTgt x x' φ,
      (∀ g : 𝒰.stabSrc x x' φ, ∀ z ∈ X.src '' 𝒰.comp x x' φ,
        𝒰.srcInv x x' φ ((𝒰.nbhd x).rep.Φ g z) =
          𝒰.biact x x' ((f g : 𝒰.stabTgt x x' φ) : X.Isotropy x') (𝒰.srcInv x x' φ z)
            (g : X.Isotropy x)⁻¹) ∧
      ∀ f' : 𝒰.stabSrc x x' φ → 𝒰.stabTgt x x' φ,
        (∀ g : 𝒰.stabSrc x x' φ, ∀ z ∈ X.src '' 𝒰.comp x x' φ,
          𝒰.srcInv x x' φ ((𝒰.nbhd x).rep.Φ g z) =
            𝒰.biact x x' ((f' g : 𝒰.stabTgt x x' φ) : X.Isotropy x') (𝒰.srcInv x x' φ z)
              (g : X.Isotropy x)⁻¹) → ∀ g, f' g = f g := by
  have hz₀ : X.src φ ∈ X.src '' 𝒰.comp x x' φ := mem_image_of_mem _ (𝒰.mem_comp hφ)
  have hψ₀ : 𝒰.srcInv x x' φ (X.src φ) = φ := 𝒰.srcInv_src hφ (𝒰.mem_comp hφ)
  have hbij : Function.Bijective (partnerHom hφ) := by
    constructor
    · intro g h hgh
      have hgh' : partner hφ g = partner hφ h := congrArg Subtype.val hgh
      have h1 := partner_spec hφ g
      have h2 := partner_spec hφ h
      rw [hgh'] at h1
      exact Subtype.ext (inv_injective (right_unique hφ (𝒰.mem_comp hφ) h1 h2))
    · intro g'
      obtain ⟨g, hg⟩ := exists_stabSrc_of_stabTgt hφ g'
      exact ⟨g, Subtype.ext (left_unique hφ (𝒰.mem_comp hφ) (partner_spec hφ g) hg)⟩
  refine ⟨MulEquiv.ofBijective (partnerHom hφ) hbij, fun g z hz => partner_identity hφ g hz,
    fun f' hf' g => Subtype.ext ?_⟩
  have h1 := hf' g (X.src φ) hz₀
  have hgz : (𝒰.nbhd x).rep.Φ g (X.src φ) ∈ X.src '' 𝒰.comp x x' φ := by
    rw [← g.2]; exact mem_image_of_mem _ hz₀
  have hmem : 𝒰.biact x x' ((f' g : 𝒰.stabTgt x x' φ) : X.Isotropy x') φ (g : X.Isotropy x)⁻¹ ∈
      𝒰.comp x x' φ := by
    have e : 𝒰.biact x x' ((f' g : 𝒰.stabTgt x x' φ) : X.Isotropy x') φ (g : X.Isotropy x)⁻¹ =
        𝒰.srcInv x x' φ ((𝒰.nbhd x).rep.Φ g (X.src φ)) := by
      rw [h1, hψ₀]
    rw [e]
    exact 𝒰.srcInv_mem hφ hgz
  exact left_unique hφ (𝒰.mem_comp hφ) hmem (partner_spec hφ g)

/-- **The discussion before Proposition 13.1.9 (p. 606)**: with `D_Σ = t ∘ (s|Σ)⁻¹`, the
isomorphism `g ↦ g'(g)` of Proposition 13.1.9 satisfies `g'(g) ∗ D_Σ(z) = D_Σ(g ∗ z)` for
`z ∈ s(Σ)`. -/
theorem proposition_13_1_9_D {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x')
    (g : 𝒰.stabSrc x x' φ) {z : Obj} (hz : z ∈ X.src '' 𝒰.comp x x' φ) :
    (𝒰.nbhd x').rep.Φ (partner hφ g) (𝒰.D x x' φ z) = 𝒰.D x x' φ ((𝒰.nbhd x).rep.Φ g z) := by
  rw [D, D, partner_identity hφ g hz,
    tgt_biact (𝒰.comp_subset x x' φ (𝒰.srcInv_mem hφ hz))]

end GoodSystem

end EpGroupoid

end Polyfold
