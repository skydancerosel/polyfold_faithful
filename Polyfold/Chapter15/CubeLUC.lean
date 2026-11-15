import Polyfold.Chapter15.CubeEp
import Polyfold.Chapter13.StrongBundlePullMap
import Polyfold.Chapter7.ReducedCriterion

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Corollary 15.4.4,
effective version (p. 703), on the cylinder `[0, 1] × X`: **the local unique continuation
property (Definition 7.2.18) passes from `X` to `[0, 1]ⁿ × X`**.

# The local unique continuation property on the cylinder

## The text, paraphrased

The effective version of Corollary 15.4.4 integrates over the cobordism `[0, 1] × X` with the
effective measures of Theorem 9.5.16, which presume the local unique continuation property of the
ep-groupoid; the text uses it on `[0, 1] × X` for `X` with it.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* `cubeIsotropyHom z : G_z → G_{z₂}`, `(q, g) ↦ g`, for `z = (q, x)` in `[0, 1]ⁿ × X`.
* **`cubeProd_Γ_snd`**: for natural representations `V` of `z` in `[0, 1]ⁿ × X` and `N` of `z₂`
  in `X` with `V.U` lying over `N.U`, the `X`-part of `Γ_V(g, y)` is `Γ_N(g₂, y₂)` (both are
  continuous lifts through the source map, which is a local homeomorphism; they agree at `z`, and
  `V.U` is connected); `cubeProd_Φ_eq`: `Φ_V(g)(y) = (y₁, Φ_N(g₂)(y₂))`.
* **`isLUC_cubeProd`**: `X` has LUC ⇒ `[0, 1]ⁿ × X` has LUC.  If `Φ_V(g)` is the identity on a
  non-empty open `W ⊆ V.U`, then `Φ_N(g₂)` is the identity on the open set `pr₂(W) ⊆ N.U`, hence
  on `N.U` (LUC of `X`, for every natural representation, `isLUC_iff_forall_naturalRep`), hence
  `Φ_V(g)` is the identity on `V.U`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  (n : ℕ) [ParacompactSpace ((Fin n → unitInterval) × Obj)]
  [ParacompactSpace ((Fin n → unitInterval) × Mor)]

/-- `G_z → G_{z₂}`, `(q, g) ↦ g`: the isotropy homomorphism of the projection `[0, 1]ⁿ × X → X`. -/
def cubeIsotropyHom (z : (Fin n → unitInterval) × Obj) :
    (X.cubeProd n).Isotropy z →* X.Isotropy z.2 where
  toFun g := ⟨g.val.2, congrArg Prod.snd g.src_val, congrArg Prod.snd g.tgt_val⟩
  map_one' := GroupoidStr.Isotropy.ext rfl
  map_mul' _ _ := GroupoidStr.Isotropy.ext rfl

@[simp] theorem cubeIsotropyHom_val (z : (Fin n → unitInterval) × Obj)
    (g : (X.cubeProd n).Isotropy z) : (X.cubeIsotropyHom n z g).val = g.val.2 := rfl

section Gamma

variable {X n} {z : (Fin n → unitInterval) × Obj} (V : (X.cubeProd n).NaturalRep z)
  (N : X.NaturalRep z.2) (hVN : ∀ y ∈ V.U, y.2 ∈ N.U)

include hVN in
/-- **The `X`-part of `Γ_V(g, y)` is `Γ_N(g₂, y₂)`** on `V.U`. -/
theorem cubeProd_Γ_snd (g : (X.cubeProd n).Isotropy z) {y : (Fin n → unitInterval) × Obj}
    (hy : y ∈ V.U) : (V.Γ g y).2 = N.Γ (X.cubeIsotropyHom n z g) y.2 := by
  set a : (Fin n → unitInterval) × Obj → Mor := fun p => (V.Γ g p).2
  set b : (Fin n → unitInterval) × Obj → Mor := fun p => N.Γ (X.cubeIsotropyHom n z g) p.2
  have ha : ContinuousOn a V.U :=
    continuous_snd.comp_continuousOn (V.isScSmoothOn_Γ g).continuousOn
  have hb : ContinuousOn b V.U :=
    ((N.isScSmoothOn_Γ (X.cubeIsotropyHom n z g)).continuousOn).comp
      continuous_snd.continuousOn fun p hp => hVN p hp
  have hab : ∀ p ∈ V.U, X.src (a p) = X.src (b p) := fun p hp => by
    have h1 : (X.cubeProd n).src (V.Γ g p) = p := V.src_Γ g p hp
    have h2 : X.src (N.Γ (X.cubeIsotropyHom n z g) p.2) = p.2 := N.src_Γ _ p.2 (hVN p hp)
    exact (congrArg Prod.snd h1).trans h2.symm
  have hE := X.isOpen_setOf_eq_of_src V.isOpen_U ha hb hab
  have hE' : IsOpen (V.U ∩ (fun p => (a p, b p)) ⁻¹' (Set.diagonal Mor)ᶜ) :=
    (ha.prodMk hb).isOpen_inter_preimage V.isOpen_U isClosed_diagonal.isOpen_compl
  have hsub : V.U ⊆ {p | p ∈ V.U ∧ a p = b p} ∪
      (V.U ∩ (fun p => (a p, b p)) ⁻¹' (Set.diagonal Mor)ᶜ) := fun p hp => by
    by_cases e : a p = b p
    · exact Or.inl ⟨hp, e⟩
    · exact Or.inr ⟨hp, e⟩
  have hdisj : Disjoint {p | p ∈ V.U ∧ a p = b p}
      (V.U ∩ (fun p => (a p, b p)) ⁻¹' (Set.diagonal Mor)ᶜ) :=
    Set.disjoint_left.2 fun p hp hp' => hp'.2 hp.2
  have hz : z ∈ V.U ∩ {p | p ∈ V.U ∧ a p = b p} := by
    refine ⟨V.mem_U, V.mem_U, ?_⟩
    change (V.Γ g z).2 = N.Γ (X.cubeIsotropyHom n z g) z.2
    rw [V.Γ_self g, N.Γ_self]
    rfl
  exact (V.isConnected_U.isPreconnected.subset_left_of_subset_union hE hE' hdisj hsub
    ⟨z, hz⟩ hy).2

include hVN in
/-- **`Φ_V(g)(y) = (y₁, Φ_N(g₂)(y₂))`** on `V.U`. -/
theorem cubeProd_Φ_eq (g : (X.cubeProd n).Isotropy z) {y : (Fin n → unitInterval) × Obj}
    (hy : y ∈ V.U) : V.Φ g y = (y.1, N.Φ (X.cubeIsotropyHom n z g) y.2) := by
  rw [← V.tgt_Γ g y hy, cubeProd_tgt, cubeProd_Γ_snd V N hVN g hy, N.tgt_Γ _ y.2 (hVN y hy)]
  have h1 : (X.cubeProd n).src (V.Γ g y) = y := V.src_Γ g y hy
  have h2 : (V.Γ g y).1 = y.1 := congrArg Prod.fst h1
  exact Prod.ext h2 rfl

include hVN in
/-- **A natural representation of `z` lying over one of `z₂` has LUC** if the latter has. -/
theorem hasLUC_of_cubeProd (hN : N.HasLUC) : V.HasLUC := by
  intro g W hW hWne hWV hid y hy
  have hid₂ : ∀ y' ∈ Prod.snd '' W, N.Φ (X.cubeIsotropyHom n z g) y' = y' := by
    rintro _ ⟨p, hp, rfl⟩
    have h := hid p hp
    rw [cubeProd_Φ_eq V N hVN g (hWV hp)] at h
    exact congrArg Prod.snd h
  have hall := hN (X.cubeIsotropyHom n z g) (Prod.snd '' W) (isOpenMap_snd W hW) (hWne.image _)
    (fun _ ⟨p, hp, e⟩ => e ▸ hVN p (hWV hp)) hid₂
  rw [cubeProd_Φ_eq V N hVN g hy, hall y.2 (hVN y hy)]

end Gamma

/-- **`[0, 1]ⁿ × X` has the local unique continuation property if `X` has it** (Definition
7.2.18 on the cylinder of Corollary 15.4.4). -/
theorem isLUC_cubeProd (h : X.IsLUC) : (X.cubeProd n).IsLUC := fun z => by
  obtain ⟨N, -⟩ := X.theorem_7_1_13 z.2 isOpen_univ (mem_univ _)
  have hN : N.HasLUC := (X.isLUC_iff_forall_naturalRep.1 h) z.2 N
  obtain ⟨V, hV⟩ := (X.cubeProd n).theorem_7_1_13 z (N.isOpen_U.preimage continuous_snd) N.mem_U
  exact ⟨V, hasLUC_of_cubeProd V N (fun y hy => hV hy) hN⟩

end EpGroupoid

end Polyfold
