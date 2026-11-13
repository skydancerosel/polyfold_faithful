import Polyfold.Chapter15.CylinderGlue
import Polyfold.Chapter13.StrongBundlePullMap
import Polyfold.Chapter13.TightMultisection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Corollary 15.3.10 (3)**, pp. 699–700: the symmetric sc⁺-section structures of `Λⁱ` on `X`
lifted to `[0, 1] × X` along the projection (gap TY-2 (a), first part).

# Lifting symmetric structures to the cylinder

## The text, paraphrased

The proof of (3) applies Theorem 15.3.9 on `[0, 1] × X` to the multisection over
`∂([0, 1] × X) = {0, 1} × X` that is `Λⁱ` over `{i} × X`, and treats it as structurable over the
boundary because the `Λⁱ` are structurable.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `cubeLiftSec s`: the section `(q, y) ↦ ((q, y), s(y))` of `W̃ → [0, 1] × X`;
  `cubeVal_fibAct`: the action of `W̃` is `μ̃((q, φ), ((q, y), w)) = ((q, t(φ)), μ(φ, w))`.
* `cubeIso z : G_z → G_{z₂}`, `(q, g) ↦ g` (the isotropy of `[0, 1] × X`).
* **`cube_Γ_snd`**: for a natural neighbourhood `V` of `z` in `[0, 1] × X` with `V` connected
  and lying over the domain of a natural neighbourhood `N` of `z₂` in `X`, the `X`-part of
  `Γ_V(g, y)` is `Γ_N(g₂, y₂)` on all of `V` (both are continuous lifts through `s`, agree at `z`,
  and `V` is connected); `cube_Φ_eq`: `Φ_V(g)(y) = (y₁, Φ_N(g₂)(y₂))`.
* **`liftStructure`**: a symmetric sc⁺-section structure (Definition 13.2.5) of `Λ` on `N`
  gives a symmetric structure over the boundary (Definition 14.1.3) of any `Λ̃` with
  `Λ̃(w) = Λ(w₂)` over `V ∩ ∂([0, 1] × X)`, with `I_z = I_{z₂}` and `G_z` acting through
  `cubeIso`, given that the lifted sections satisfy (1) of Definition 14.1.3.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold EpGroupoid SEP

variable {A : SEP.{u}}

/-! ### Sections and the action on `W̃` -/

theorem cubeVal_injective {n : ℕ} : Injective (cubeVal (A := A) (n := n)) :=
  fun _ _ h => Subtype.ext h

open Classical in
/-- `s` where it lies over the point, the zero of the fibre elsewhere (a section of `W → X`). -/
def fixSec (s : A.Obj → A.W) (y : A.Obj) : A.W :=
  if A.P (s y) = y then s y else fiberZero A.P y

theorem isSection_fixSec (s : A.Obj → A.W) : IsSection A.P (fixSec s) := fun y => by
  unfold fixSec
  split_ifs with h
  · exact h
  · exact proj_fiberZero A.P y

theorem fixSec_of {s : A.Obj → A.W} {y : A.Obj} (h : A.P (s y) = y) : fixSec s y = s y := by
  unfold fixSec
  rw [if_pos h]

/-- **The lift of a section** `s` of `W → X` to `W̃ → [0, 1] × X`: `(q, y) ↦ ((q, y), s(y))`
where `s(y)` lies over `y` (the zero of the fibre otherwise). -/
def cubeLiftSec (s : A.Obj → A.W) : (A.cubeSEP 1).Obj → (A.cubeSEP 1).W :=
  cubeLiftEp (n := 1) (fixSec s) (isSection_fixSec s)

theorem cubeVal_cubeLiftSec {s : A.Obj → A.W} {p : (A.cubeSEP 1).Obj} (h : A.P (s p.2) = p.2) :
    cubeVal (cubeLiftSec s p) = (p, s p.2) := by
  unfold cubeLiftSec
  rw [cubeLiftEp_val, fixSec_of h]

theorem P_cubeLiftSec (s : A.Obj → A.W) (p : (A.cubeSEP 1).Obj) :
    (A.cubeSEP 1).P (cubeLiftSec s p) = p :=
  isSection_cubeLiftEp (isSection_fixSec s) p

/-- `cubeLiftSec s (p) = w` iff `s(p₂) = w₂`, for `w` over `p` and `s(p₂)` over `p₂`. -/
theorem cubeLiftSec_eq_iff {s : A.Obj → A.W} {p : (A.cubeSEP 1).Obj} (h : A.P (s p.2) = p.2)
    {w : (A.cubeSEP 1).W} (hw : (A.cubeSEP 1).P w = p) :
    cubeLiftSec s p = w ↔ s p.2 = (cubeVal w).2 := by
  constructor
  · rintro rfl; rw [cubeVal_cubeLiftSec h]
  · intro e
    apply cubeVal_injective
    rw [cubeVal_cubeLiftSec h, e]
    exact Prod.ext hw.symm rfl

theorem cubeSEP_src (ψ : (A.cubeSEP 1).Mor) :
    (A.cubeSEP 1).X.src ψ = (ψ.1, A.X.src ψ.2) := rfl

theorem cubeSEP_tgt (ψ : (A.cubeSEP 1).Mor) :
    (A.cubeSEP 1).X.tgt ψ = (ψ.1, A.X.tgt ψ.2) := rfl

/-- **The action of `W̃`**: `μ̃((q, φ), ((q, y), w)) = ((q, t(φ)), μ(φ, w))`. -/
theorem cubeVal_fibAct {ψ : (A.cubeSEP 1).Mor} {v : (A.cubeSEP 1).W}
    (h : (A.cubeSEP 1).P v = (A.cubeSEP 1).X.src ψ) :
    cubeVal (fibAct ψ v) = ((A.cubeSEP 1).X.tgt ψ, fibAct ψ.2 (cubeVal v).2) := by
  have h' : A.P (cubeVal v).2 = A.X.src ψ.2 := by
    rw [P_cubeVal_snd]
    exact congrArg Prod.snd h
  rw [fibAct_of h, fibAct_of h']
  rfl

/-! ### The isotropy of `[0, 1] × X` -/

/-- `G_z → G_{z₂}`, `(q, g) ↦ g` (the isotropy homomorphism of the projection). -/
def cubeIso (z : (A.cubeSEP 1).Obj) : (A.cubeSEP 1).X.Isotropy z →* A.X.Isotropy z.2 where
  toFun g := ⟨g.val.2, congrArg Prod.snd g.src_val, congrArg Prod.snd g.tgt_val⟩
  map_one' := GroupoidStr.Isotropy.ext rfl
  map_mul' _ _ := GroupoidStr.Isotropy.ext rfl

@[simp] theorem cubeIso_val (z : (A.cubeSEP 1).Obj) (g : (A.cubeSEP 1).X.Isotropy z) :
    (cubeIso z g).val = g.val.2 := rfl

section Gamma

variable {z : (A.cubeSEP 1).Obj} (V : (A.cubeSEP 1).X.NatNbhd z) (hV : IsPreconnected V.U)
  (N : A.X.NatNbhd z.2) (hVN : ∀ y ∈ V.U, y.2 ∈ N.U)

include hV hVN in
/-- **The `X`-part of `Γ_V(g, y)` is `Γ_N(g₂, y₂)`** on a connected `V` over `N`. -/
theorem cube_Γ_snd (g : (A.cubeSEP 1).X.Isotropy z) {y : (A.cubeSEP 1).Obj} (hy : y ∈ V.U) :
    (V.rep.Γ g y).2 = N.rep.Γ (cubeIso z g) y.2 := by
  set a : (A.cubeSEP 1).Obj → A.Mor := fun p => (V.rep.Γ g p).2
  set b : (A.cubeSEP 1).Obj → A.Mor := fun p => N.rep.Γ (cubeIso z g) p.2
  have ha : ContinuousOn a V.U :=
    continuous_snd.comp_continuousOn
      (((V.rep.isScSmoothOn_Γ g).continuousOn).mono V.U_subset)
  have hb : ContinuousOn b V.U :=
    ((N.rep.isScSmoothOn_Γ (cubeIso z g)).continuousOn).comp continuous_snd.continuousOn
      fun p hp => N.mem_rep_U (hVN p hp)
  have hab : ∀ p ∈ V.U, A.X.src (a p) = A.X.src (b p) := fun p hp => by
    have h1 : (A.cubeSEP 1).X.src (V.rep.Γ g p) = p := V.src_Γ g hp
    have h2 : A.X.src (N.rep.Γ (cubeIso z g) p.2) = p.2 := N.src_Γ _ (hVN p hp)
    exact (congrArg Prod.snd h1).trans h2.symm
  have hE := A.X.isOpen_setOf_eq_of_src V.isOpen_U ha hb hab
  have hE' : IsOpen (V.U ∩ (fun p => (a p, b p)) ⁻¹' (Set.diagonal A.Mor)ᶜ) :=
    (ha.prodMk hb).isOpen_inter_preimage V.isOpen_U isClosed_diagonal.isOpen_compl
  have hsub : V.U ⊆ {p | p ∈ V.U ∧ a p = b p} ∪
      (V.U ∩ (fun p => (a p, b p)) ⁻¹' (Set.diagonal A.Mor)ᶜ) := fun p hp => by
    by_cases e : a p = b p
    · exact Or.inl ⟨hp, e⟩
    · exact Or.inr ⟨hp, e⟩
  have hdisj : Disjoint {p | p ∈ V.U ∧ a p = b p}
      (V.U ∩ (fun p => (a p, b p)) ⁻¹' (Set.diagonal A.Mor)ᶜ) :=
    Set.disjoint_left.2 fun p hp hp' => hp'.2 hp.2
  have hz : z ∈ V.U ∩ {p | p ∈ V.U ∧ a p = b p} := by
    refine ⟨V.mem_U, V.mem_U, ?_⟩
    change (V.rep.Γ g z).2 = N.rep.Γ (cubeIso z g) z.2
    rw [V.rep.Γ_self g, N.rep.Γ_self]
    rfl
  exact (hV.subset_left_of_subset_union hE hE' hdisj hsub ⟨z, hz⟩ hy).2

include hV hVN in
/-- **`Φ_V(g)(y) = (y₁, Φ_N(g₂)(y₂))`** on a connected `V` over `N`. -/
theorem cube_Φ_eq (g : (A.cubeSEP 1).X.Isotropy z) {y : (A.cubeSEP 1).Obj} (hy : y ∈ V.U) :
    V.rep.Φ g y = (y.1, N.rep.Φ (cubeIso z g) y.2) := by
  rw [← V.tgt_Γ g hy, cubeSEP_tgt, cube_Γ_snd V hV N hVN g hy, N.tgt_Γ _ (hVN y hy)]
  have h1 : (A.cubeSEP 1).X.src (V.rep.Γ g y) = y := V.src_Γ g hy
  have h2 : (V.rep.Γ g y).1 = y.1 := congrArg Prod.fst h1
  exact Prod.ext h2 rfl

end Gamma

/-! ### The lifted structure -/

/-- **A symmetric sc⁺-section structure of `Λ` on `N ⊆ X` lifted to `V ⊆ [0, 1] × X`**
(Definition 14.1.3 for `W̃`): `I_z = I_{z₂}` with `G_z` acting through `cubeIso`, sections
`(q, y) ↦ ((q, y), sᵢ(y))`, for any `Λ̃` with `Λ̃(w) = Λ(w₂)` over `V ∩ ∂([0, 1] × X)`, given
condition (1) of Definition 14.1.3 for the lifted sections (`hface`). -/
def liftStructure {Λc : (A.cubeSEP 1).W → ℚ≥0} {Λ : A.W → ℚ≥0} {z : (A.cubeSEP 1).Obj}
    (V : (A.cubeSEP 1).X.NatNbhd z) (hV : IsPreconnected V.U) {N : A.X.NatNbhd z.2}
    (S : SymmetricStructureOn A Λ N) (hVN : ∀ y ∈ V.U, y.2 ∈ N.U)
    (hface : ∀ i, IsFaceScPlusSectionOn (A.cubeSEP 1) (cubeLiftSec (S.s i)) V.bdry)
    (hrep : ∀ w, (A.cubeSEP 1).P w ∈ V.bdry → Λc w = Λ (cubeVal w).2) :
    BoundarySymmetricStructure (A.cubeSEP 1) Λc V where
  I := S.I
  mulAction := MulAction.compHom S.I (cubeIso z)
  s i := cubeLiftSec (S.s i)
  isFaceScPlus := hface
  equivariant g i y hy := by
    have hy2 : y.2 ∈ N.U := hVN y hy.1
    have hΦ := cube_Φ_eq V hV N hVN g hy.1
    have hΦ2 : (V.rep.Φ g y).2 = N.rep.Φ (cubeIso z g) y.2 := by rw [hΦ]
    have hsrc : (A.cubeSEP 1).P (cubeLiftSec (S.s i) y) = (A.cubeSEP 1).X.src (V.rep.Γ g y) := by
      rw [P_cubeLiftSec, V.src_Γ g hy.1]
    have hP1 : A.P (S.s (cubeIso z g • i) (V.rep.Φ g y).2) = (V.rep.Φ g y).2 := by
      rw [hΦ2]; exact S.P_s _ (N.Φ_mem _ hy2)
    apply cubeVal_injective
    rw [cubeVal_fibAct hsrc]
    change cubeVal (cubeLiftSec (S.s (cubeIso z g • i)) (V.rep.Φ g y)) = _
    rw [cubeVal_cubeLiftSec hP1, cubeVal_cubeLiftSec (S.P_s i hy2)]
    refine Prod.ext (V.tgt_Γ g hy.1).symm ?_
    change S.s (cubeIso z g • i) (V.rep.Φ g y).2 = fibAct (V.rep.Γ g y).2 (S.s i y.2)
    rw [hΦ2, cube_Γ_snd V hV N hVN g hy.1]
    exact S.equivariant _ i y.2 hy2
  rep w hw := by
    classical
    have hw2 : A.P (cubeVal w).2 ∈ N.U := by
      rw [P_cubeVal_snd]; exact hVN _ hw.1
    rw [hrep w hw, S.rep _ hw2]
    congr 3
    refine Finset.filter_congr fun i _ => ?_
    have hP : A.P (S.s i ((A.cubeSEP 1).P w).2) = ((A.cubeSEP 1).P w).2 :=
      S.P_s i (hVN _ hw.1)
    rw [cubeLiftSec_eq_iff hP rfl, P_cubeVal_snd]
    rfl

@[simp] theorem liftStructure_I {Λc : (A.cubeSEP 1).W → ℚ≥0} {Λ : A.W → ℚ≥0}
    {z : (A.cubeSEP 1).Obj} (V : (A.cubeSEP 1).X.NatNbhd z) (hV : IsPreconnected V.U)
    {N : A.X.NatNbhd z.2} (S : SymmetricStructureOn A Λ N) (hVN : ∀ y ∈ V.U, y.2 ∈ N.U)
    (hface : ∀ i, IsFaceScPlusSectionOn (A.cubeSEP 1) (cubeLiftSec (S.s i)) V.bdry)
    (hrep : ∀ w, (A.cubeSEP 1).P w ∈ V.bdry → Λc w = Λ (cubeVal w).2) :
    (liftStructure V hV S hVN hface hrep).I = S.I := rfl

end SBLocalization

end Polyfold
