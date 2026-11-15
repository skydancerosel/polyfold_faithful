import Polyfold.Chapter15.CubeLiftScPlus
import Polyfold.Chapter13.StructuredExtension

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Corollary 15.3.10 (3)**, pp. 699–700: the pull-back `pr^*Λ` of a structurable sc⁺-multisection
`Λ` of `W → X` to the strong bundle `W̃ = [0, 1] × W → [0, 1] × X` is structurable
(Definition 13.3.6).

# Structurability of `pr^*Λ` on the cylinder

## The text, paraphrased

The proof of (3) pulls the strong bundle back to `[0, 1] × X` ("the fiber over `(t, x)` is
`W_x`") and uses structurable sc⁺-multisections there; it does not spell out the structure.
The projection `[0, 1] × X → X` is not a local sc-diffeomorphism, so Theorem 13.4.1 does not
apply; the structure is lifted directly.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `cubePullMult Λ`: `pr^*Λ(w) = Λ(w₂)`; `isWFunctor_cubePullMult`.
* `exists_cubeGoodSystem`: a good system of `[0, 1] × X` (Definition 13.1.2) with connected
  neighbourhoods `Ũ(z) ⊆ [0, 1] × U(z₂)` for a given good system `𝒰` of `X` (Theorem 13.1.8,
  then the connected component of `z`, invariant since the natural action fixes `z`).
* `liftSymmetric`: the symmetric structure `(sᵢ)_{i ∈ I_{z₂}}` of `Λ` on `U(z₂)` lifted to
  `Ũ(z)`: sections `(q, y) ↦ ((q, y), sᵢ(y))`, `G_z` acting through `G_z → G_{z₂}`.
* `cubePullDec`, `cubePullTau`: the decoration and the correspondences
  `τ̃_{z,z'}(φ) = τ_{z₂,z'₂}(φ₂)`.
* **`isStructurable_cubePullMult`**: `pr^*Λ` is structurable for structurable `Λ`, when `|X|` is
  paracompact.
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

/-! ### The pulled-back functor -/

/-- **`pr^*Λ`** on `W̃ → [0, 1] × X`: `pr^*Λ(w) = Λ(w₂)`. -/
def cubePullMult (Λ : A.W → ℚ≥0) (w : (A.cubeSEP 1).W) : ℚ≥0 := Λ (cubeVal w).2

theorem cubePullMult_apply (Λ : A.W → ℚ≥0) (w : (A.cubeSEP 1).W) :
    cubePullMult Λ w = Λ (cubeVal w).2 := rfl

/-- `pr^*Λ` is a functor if `Λ` is one. -/
theorem isWFunctor_cubePullMult {Λ : A.W → ℚ≥0} (h : IsWFunctor A Λ) :
    IsWFunctor (A.cubeSEP 1) (cubePullMult Λ) := by
  rintro ⟨⟨ψ, v⟩, hv⟩
  change (A.cubeSEP 1).P v = (A.cubeSEP 1).X.src ψ at hv
  have hμ : (A.cubeSEP 1).E.μ ⟨(ψ, v), hv⟩ = fibAct ψ v := (fibAct_of hv).symm
  have h' : A.P (cubeVal v).2 = A.X.src ψ.2 := by
    rw [P_cubeVal_snd]; exact congrArg Prod.snd hv
  change cubePullMult Λ ((A.cubeSEP 1).E.μ ⟨(ψ, v), hv⟩) = cubePullMult Λ v
  rw [hμ, cubePullMult_apply, cubePullMult_apply, cubeVal_fibAct hv, fibAct_of h']
  exact h ⟨(ψ.2, (cubeVal v).2), h'⟩

/-! ### A connected good system on the cylinder -/

/-- **A good system of `[0, 1] × X` over a good system of `X`**: for `|X|` paracompact and a good
system `𝒰` of `X`, there is a good system `𝒲` of `[0, 1] × X` with `W(z) ⊆ [0, 1] × U(z₂)` and
every `W(z)` connected. -/
theorem exists_cubeGoodSystem (hpara : A.X.HasParacompactOrbitSpace) (𝒰 : A.X.GoodSystem) :
    ∃ 𝒲 : (A.cubeSEP 1).X.GoodSystem,
      ∀ z, 𝒲.U z ⊆ {p | p.2 ∈ 𝒰.U z.2} ∧ IsPreconnected (𝒲.U z) := by
  have hparaC : (A.cubeSEP 1).X.HasParacompactOrbitSpace :=
    A.X.hasParacompactOrbitSpace_cubeProd 1 hpara
  obtain ⟨𝒲₀, h𝒲₀⟩ := (A.cubeSEP 1).X.theorem_13_1_8 hparaC
    (fun z : (A.cubeSEP 1).Obj => {p : (A.cubeSEP 1).Obj | p.2 ∈ 𝒰.U z.2})
    (fun z => (𝒰.isOpen_U z.2).preimage continuous_snd) (fun z => 𝒰.mem_U z.2)
  set C : (A.cubeSEP 1).Obj → Set (A.cubeSEP 1).Obj :=
    fun z => connectedComponentIn (𝒲₀.U z) z with hC
  have hCo : ∀ z, IsOpen (C z) := fun z =>
    MPolyfold.isOpen_connectedComponentIn (A.cubeSEP 1).X.PObj (𝒲₀.isOpen_U z) z
  have hCz : ∀ z, z ∈ C z := fun z => mem_connectedComponentIn (𝒲₀.mem_U z)
  have hCU : ∀ z, C z ⊆ 𝒲₀.U z := fun z => connectedComponentIn_subset _ _
  have hinv : ∀ z g, MapsTo ((𝒲₀.nbhd z).rep.Φ g) (C z) (C z) := by
    intro z g
    set N := 𝒲₀.nbhd z
    have hcont : ContinuousOn (N.rep.Φ g) (C z) :=
      ((N.rep.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn.mono N.U_subset).mono (hCU z)
    have himg : N.rep.Φ g '' C z ⊆ C z :=
      (isPreconnected_connectedComponentIn.image _ hcont).subset_connectedComponentIn
        ⟨z, hCz z, N.rep.Φ_self g⟩ (image_subset_iff.2 fun y hy => N.mapsTo_Φ g (hCU z hy))
    exact fun y hy => himg (mem_image_of_mem _ hy)
  refine ⟨𝒲₀.restrict C hCo hCz hCU hinv, fun z => ⟨fun y hy => h𝒲₀ z (hCU z hy), ?_⟩⟩
  exact isPreconnected_connectedComponentIn

/-! ### The lifted symmetric structures -/

/-- **A symmetric sc⁺-section structure of `Λ` on `N ⊆ X` lifted to a connected `V ⊆ [0, 1] × X`
over `N`** (Definition 13.2.5 for `pr^*Λ`): `I_z = I_{z₂}` with `G_z` acting through `cubeIso`,
sections `(q, y) ↦ ((q, y), sᵢ(y))`. -/
def liftSymmetric {Λ : A.W → ℚ≥0} {z : (A.cubeSEP 1).Obj}
    (V : (A.cubeSEP 1).X.NatNbhd z) (hV : IsPreconnected V.U) {N : A.X.NatNbhd z.2}
    (S : SymmetricStructureOn A Λ N) (hVN : ∀ y ∈ V.U, y.2 ∈ N.U) :
    SymmetricStructureOn (A.cubeSEP 1) (cubePullMult Λ) V where
  I := S.I
  mulAction := MulAction.compHom S.I (cubeIso z)
  s i := cubeLiftSec (S.s i)
  isScPlusSectionOn i :=
    (isScPlusSectionOn_cubeLiftSec (S.isScPlusSectionOn i) N.isOpen_U).mono V.isOpen_U hVN
  equivariant g i y hy := by
    have hy2 : y.2 ∈ N.U := hVN y hy
    have hΦ := cube_Φ_eq V hV N hVN g hy
    have hΦ2 : (V.rep.Φ g y).2 = N.rep.Φ (cubeIso z g) y.2 := by rw [hΦ]
    have hsrc : (A.cubeSEP 1).P (cubeLiftSec (S.s i) y) = (A.cubeSEP 1).X.src (V.rep.Γ g y) := by
      rw [P_cubeLiftSec, V.src_Γ g hy]
    have hP1 : A.P (S.s (cubeIso z g • i) (V.rep.Φ g y).2) = (V.rep.Φ g y).2 := by
      rw [hΦ2]; exact S.P_s _ (N.Φ_mem _ hy2)
    apply cubeVal_injective
    rw [cubeVal_fibAct hsrc]
    change cubeVal (cubeLiftSec (S.s (cubeIso z g • i)) (V.rep.Φ g y)) = _
    rw [cubeVal_cubeLiftSec hP1, cubeVal_cubeLiftSec (S.P_s i hy2)]
    refine Prod.ext (V.tgt_Γ g hy).symm ?_
    change S.s (cubeIso z g • i) (V.rep.Φ g y).2 = fibAct (V.rep.Γ g y).2 (S.s i y.2)
    rw [hΦ2, cube_Γ_snd V hV N hVN g hy]
    exact S.equivariant _ i y.2 hy2
  rep w hw := by
    classical
    have hw2 : A.P (cubeVal w).2 ∈ N.U := by
      rw [P_cubeVal_snd]; exact hVN _ hw
    rw [cubePullMult_apply, S.rep _ hw2]
    congr 3
    refine Finset.filter_congr fun i _ => ?_
    have hP : A.P (S.s i ((A.cubeSEP 1).P w).2) = ((A.cubeSEP 1).P w).2 :=
      S.P_s i (hVN _ hw)
    rw [cubeLiftSec_eq_iff hP rfl, P_cubeVal_snd]
    rfl

/-! ### The decoration and the correspondences -/

section Pull

variable {Λ : A.W → ℚ≥0} (D : Decoration A Λ) (𝒲 : (A.cubeSEP 1).X.GoodSystem)
  (h𝒲 : ∀ z, 𝒲.U z ⊆ {p | p.2 ∈ D.𝒰.U z.2}) (hc : ∀ z, IsPreconnected (𝒲.U z))

/-- **The decoration of `pr^*Λ`**: the good system `𝒲` and the lifted structures. -/
def cubePullDec : Decoration (A.cubeSEP 1) (cubePullMult Λ) :=
  ⟨𝒲, fun z => liftSymmetric (𝒲.nbhd z) (hc z) (D.S z.2) (fun _ hy => h𝒲 z hy)⟩

variable {D 𝒲}

include h𝒲 in
/-- A morphism of `𝒲(z, z')` has its `X`-part in `𝒰(z₂, z'₂)`. -/
theorem mor_snd_of_cubeGoodSystem {z z' : (A.cubeSEP 1).Obj} {φ : (A.cubeSEP 1).Mor}
    (hφ : φ ∈ 𝒲.mor z z') : φ.2 ∈ D.𝒰.mor z.2 z'.2 :=
  ⟨h𝒲 z hφ.1, h𝒲 z' hφ.2⟩

include h𝒲 in
/-- The component of `φ` in `𝒲(z, z')` lies over the component of `φ₂` in `𝒰(z₂, z'₂)`. -/
theorem comp_snd_of_cubeGoodSystem {z z' : (A.cubeSEP 1).Obj} {φ ψ : (A.cubeSEP 1).Mor}
    (hφ : φ ∈ 𝒲.mor z z') (hψ : ψ ∈ 𝒲.comp z z' φ) : ψ.2 ∈ D.𝒰.comp z.2 z'.2 φ.2 := by
  have h : Prod.snd '' 𝒲.comp z z' φ ⊆ D.𝒰.comp z.2 z'.2 φ.2 :=
    (isPreconnected_connectedComponentIn.image _
      continuous_snd.continuousOn).subset_connectedComponentIn
      ⟨φ, mem_connectedComponentIn hφ, rfl⟩
      (image_subset_iff.2 fun χ hχ => mor_snd_of_cubeGoodSystem h𝒲
        (connectedComponentIn_subset _ _ hχ))
  exact h (mem_image_of_mem _ hψ)

variable (t : D.Tau)

/-- **The correspondences of `pr^*Λ`**: `τ̃_{z,z'}(φ) = τ_{z₂,z'₂}(φ₂)` (Definitions 13.3.4 and
13.3.6 from those of `Λ`). -/
def cubePullTau : (cubePullDec D 𝒲 h𝒲 hc).Tau where
  τ z z' φ := t.τ z.2 z'.2 φ.2
  isCorrespondence z z' :=
    { locallyConstant := fun φ hφ =>
        (continuous_snd.tendsto φ).eventually
          ((t.isCorrespondence z.2 z'.2).locallyConstant φ.2 (mor_snd_of_cubeGoodSystem h𝒲 hφ))
      finite := ((t.isCorrespondence z.2 z'.2).finite).subset (by
        rintro _ ⟨φ, hφ, rfl⟩
        exact ⟨φ.2, mor_snd_of_cubeGoodSystem h𝒲 hφ, rfl⟩)
      biact := fun φ hφ g' g => by
        change t.τ z.2 z'.2 (EpGroupoid.biact (𝒲.nbhd z) (𝒲.nbhd z') g' φ g).2 = _
        rw [cube_biact_snd (𝒲.nbhd z) (𝒲.nbhd z') (hc z) (hc z') _ _
          (fun _ hy => h𝒲 z hy) (fun _ hy => h𝒲 z' hy) hφ.1 hφ.2 g' g]
        refine ((t.isCorrespondence z.2 z'.2).biact φ.2 (mor_snd_of_cubeGoodSystem h𝒲 hφ)
          (cubeIso _ g') (cubeIso _ g)).trans ?_
        exact (IndexCorr.biact_compHom (cubeIso _) (cubeIso _) _ g' g).symm
      compat := fun φ hφ => by
        refine IndexCorr.sat_mono (fun i j H ψ hψ => ?_)
          ((t.isCorrespondence z.2 z'.2).compat φ.2 (mor_snd_of_cubeGoodSystem h𝒲 hφ))
        have hψm := connectedComponentIn_subset _ _ hψ
        have hs : A.X.src ψ.2 ∈ D.𝒰.U z.2 := h𝒲 z hψm.1
        have ht : A.X.tgt ψ.2 ∈ D.𝒰.U z'.2 := h𝒲 z' hψm.2
        exact cubeLiftSec_compat ((D.S _).P_s i hs) ((D.S _).P_s j ht)
          (H ψ.2 (comp_snd_of_cubeGoodSystem h𝒲 hφ hψ)) }
  diag z g y hy := by
    have hy2 : y.2 ∈ D.𝒰.U z.2 := h𝒲 z hy
    change t.τ z.2 z.2 ((𝒲.nbhd z).rep.Γ g y).2 = _
    rw [cube_Γ_snd (𝒲.nbhd z) (hc z) _ (fun _ hy => h𝒲 z hy) g hy]
    exact t.diag _ (cubeIso _ g) y.2 hy2
  swap z z' φ hφ := t.swap z.2 z'.2 φ.2 (mor_snd_of_cubeGoodSystem h𝒲 hφ)

end Pull

/-! ### Structurability -/

/-- **`pr^*Λ` is structurable** (Definition 13.3.6) on `W̃ → [0, 1] × X` for a structurable `Λ`,
when `|X|` is paracompact. -/
theorem isStructurable_cubePullMult (hpara : A.X.HasParacompactOrbitSpace) {Λ : A.W → ℚ≥0}
    (h : IsStructurable A Λ) : IsStructurable (A.cubeSEP 1) (cubePullMult Λ) := by
  obtain ⟨hΛ, D, ⟨t⟩⟩ := h
  obtain ⟨𝒲, h𝒲⟩ := exists_cubeGoodSystem hpara D.𝒰
  have hsub : ∀ z, 𝒲.U z ⊆ {p | p.2 ∈ D.𝒰.U z.2} := fun z => (h𝒲 z).1
  have hc : ∀ z, IsPreconnected (𝒲.U z) := fun z => (h𝒲 z).2
  refine ⟨⟨isWFunctor_cubePullMult hΛ.1, fun z => ?_⟩, cubePullDec D 𝒲 hsub hc,
    ⟨cubePullTau hsub hc t⟩⟩
  have : Nonempty ((cubePullDec D 𝒲 hsub hc).S z).I := D.nonempty_I hΛ z.2
  exact hasLocalSectionStructure_of_symmetricOn ((cubePullDec D 𝒲 hsub hc).S z)

end SBLocalization

end Polyfold
