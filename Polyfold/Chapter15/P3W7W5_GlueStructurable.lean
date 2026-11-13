import Polyfold.Chapter15.P3W7W5_CubeLift
import Polyfold.Chapter14.P3W4GL_Criterion
import Polyfold.Chapter13.P3W3C_AtomicStructurable
import Polyfold.Chapter15.P3W7W5_CylinderPartitions
import Polyfold.Chapter5.P3W5TY_DegZeroTame

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Corollary 15.3.10 (3)**, pp. 699–700: the multisection over `∂([0, 1] × X)` that is `Λⁱ` over
`{i} × X` is structurable over the boundary (Definition 14.1.7) when `Λ⁰`, `Λ¹` are structurable
(Definition 13.3.6) (gap TY-2 (a)).

# Structurability of the glued multisection

## The text, paraphrased

The proof of (3) considers `[0, 1] × X` with the multisection over its boundary
`{0, 1} × X` given by `Λ⁰` and `Λ¹`, and applies Theorem 15.3.9 to it; it does not spell out
the structure over the boundary.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `CubeLiftFace A` (added hypothesis): a lift `(q, y) ↦ ((q, y), s(y))` of an sc⁺-section `s` on
  an open `U ⊆ X` satisfies (1) of Definition 14.1.3 on `([0, 1] × U) ∩ ∂([0, 1] × X)`.
* `cubeSide z` (`t(z) > 1/2`), `sideSet b` (open), `glueO D z`: the open set
  `{t ≷ 1/2} × U_{D}(z₂)` on which the structure at `z` is lifted from `Λ^{side z}`.
* `glueτ'`: the correspondences of `Λ^b` (the full correspondence between different sides, where
  `𝒰̃(z, z')` is empty); `glueTau`: the correspondences `τ̃_{z,z'}(φ) = τ^b_{z₂,z'₂}(φ₂)`, with
  (a), (b), (c), (4) of Definition 14.1.7 from those of Definition 13.3.6 (`cube_Γ_snd`).
* **`isBoundaryStructurable_of_sides`**: a multisection `Λ̃` over `∂([0, 1] × X)` with
  `Λ̃(w) = Λ^{side}(w₂)` is structurable over the boundary if `Λ^false`, `Λ^true` are structurable.
* **`isBoundaryStructurable_cubeGlue_w5`**: TY's `cubeGlue Λ⁰ Λ¹` is structurable over the
  boundary; **`corollary_15_3_10_3_struct_w5`**: Corollary 15.3.10 (3) with TY's added
  hypothesis `hbs` replaced by `CubeLiftFace A`.
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

/-! ### The face hypothesis -/

variable (A) in
/-- **(1) of Definition 14.1.3 for lifted sections** (added hypothesis): for an sc⁺-section `s`
on an open `U ⊆ X`, the section `(q, y) ↦ ((q, y), s(y))` of `W̃ → [0, 1] × X` is sc⁺ on the
local faces through the points of `([0, 1] × U) ∩ ∂([0, 1] × X)`. -/
def CubeLiftFace : Prop :=
  ∀ (s : A.Obj → A.W) (U : Set A.Obj), IsOpen U → IsScPlusSectionOn A s U →
    IsFaceScPlusSectionOn (A.cubeSEP 1) (cubeLiftSec s)
      ({p : (A.cubeSEP 1).Obj | p.2 ∈ U} ∩ (A.cubeSEP 1).X.PObj.boundary)

/-! ### The two sides of `[0, 1] × X` -/

/-- The `[0, 1]`-coordinate of a point of `[0, 1] × X`. -/
def cubeT (p : (A.cubeSEP 1).Obj) : ℝ := (p.1 0 : ℝ)

theorem continuous_cubeT : Continuous (cubeT (A := A)) := by
  change Continuous fun p : (Fin 1 → unitInterval) × A.Obj => (p.1 0 : ℝ)
  exact continuous_subtype_val.comp ((continuous_apply 0).comp continuous_fst)

/-- The side of `p`: `true` iff `t(p) > 1/2`. -/
def cubeSide (p : (A.cubeSEP 1).Obj) : Bool := decide ((1 : ℝ) / 2 < cubeT p)

/-- `{t > 1/2}` for `true`, `{t < 1/2}` for `false` (open). -/
def sideSet : Bool → Set (A.cubeSEP 1).Obj
  | true => {p | (1 : ℝ) / 2 < cubeT p}
  | false => {p | cubeT p < (1 : ℝ) / 2}

theorem isOpen_sideSet (b : Bool) : IsOpen (sideSet (A := A) b) := by
  cases b
  · exact isOpen_lt continuous_cubeT continuous_const
  · exact isOpen_lt continuous_const continuous_cubeT

theorem cubeSide_of_mem {b : Bool} {p : (A.cubeSEP 1).Obj} (h : p ∈ sideSet b) :
    cubeSide p = b := by
  cases b
  · exact decide_eq_false (not_lt.2 (le_of_lt h))
  · exact decide_eq_true h

theorem mem_sideSet_cubeSide (hX : A.X.IsTame) (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {z : (A.cubeSEP 1).Obj} (hz : z ∈ (A.cubeSEP 1).X.PObj.boundary) :
    z ∈ sideSet (cubeSide z) := by
  rcases (mem_boundary_cubeSEP_iff hX hd z).1 hz with h | h
  · have h0 : cubeT z = 0 := h
    have hs : cubeSide z = false := decide_eq_false (by rw [h0]; norm_num)
    rw [hs]
    change cubeT z < 1 / 2
    rw [h0]; norm_num
  · have h1 : cubeT z = 1 := h
    have hs : cubeSide z = true := decide_eq_true (by rw [h1]; norm_num)
    rw [hs]
    change 1 / 2 < cubeT z
    rw [h1]; norm_num

theorem cubeSide_src (ψ : (A.cubeSEP 1).Mor) :
    cubeSide ((A.cubeSEP 1).X.src ψ) = cubeSide ((A.cubeSEP 1).X.tgt ψ) := rfl

/-- On the boundary, `cubeGlue Λ₀ Λ₁` is `Λ^{side}` (`Λ^false = Λ₀`, `Λ^true = Λ₁`). -/
theorem cubeGlue_eq_side (hX : A.X.IsTame) (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (Λ₀ Λ₁ : A.W → ℚ≥0) {w : (A.cubeSEP 1).W}
    (hw : (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary) :
    cubeGlue Λ₀ Λ₁ w = cond (cubeSide ((A.cubeSEP 1).P w)) Λ₁ Λ₀ (cubeVal w).2 := by
  rcases (mem_boundary_cubeSEP_iff hX hd _).1 hw with h | h
  · have h0 : cubeT ((A.cubeSEP 1).P w) = 0 := h
    have hs : cubeSide ((A.cubeSEP 1).P w) = false := decide_eq_false (by rw [h0]; norm_num)
    rw [hs, cubeGlue_of_zero h]
    rfl
  · have h1 : cubeT ((A.cubeSEP 1).P w) = 1 := h
    have hs : cubeSide ((A.cubeSEP 1).P w) = true := decide_eq_true (by rw [h1]; norm_num)
    rw [hs, cubeGlue_of_one h]
    rfl

/-! ### The correspondences of the two sides -/

section Sides

variable {Λ : Bool → A.W → ℚ≥0} {D : ∀ b, Decoration A (Λ b)} (t : ∀ b, (D b).Tau)
  (hne : ∀ b x, Nonempty ((D b).S x).I)

/-- `τ^b_{x,x'}` on one side, the full correspondence between different sides. -/
def glueτ' : (b b' : Bool) → (x x' : A.Obj) → A.Mor → IndexCorr ((D b).S x).I ((D b').S x').I
  | true, true, x, x', φ => (t true).τ x x' φ
  | false, false, x, x', φ => (t false).τ x x' φ
  | true, false, x, x', _ =>
    haveI := hne true x; haveI := hne false x'; IndexCorr.full _ _
  | false, true, x, x', _ =>
    haveI := hne false x; haveI := hne true x'; IndexCorr.full _ _

theorem glueτ'_self (b : Bool) (x x' : A.Obj) (φ : A.Mor) :
    glueτ' t hne b b x x' φ = (t b).τ x x' φ := by
  cases b <;> rfl

variable {t hne} {b b' : Bool} {x x' : A.Obj} {φ : A.Mor}

theorem glueτ'_eventually (hb : b = b') (hφ : φ ∈ (D b).𝒰.mor x x') :
    ∀ᶠ ψ in 𝓝 φ, glueτ' t hne b b' x x' ψ = glueτ' t hne b b' x x' φ := by
  subst hb
  simp only [glueτ'_self]
  exact ((t b).isCorrespondence x x').locallyConstant φ hφ

theorem glueτ'_finite (hb : b = b') :
    (glueτ' t hne b b' x x' '' (D b).𝒰.mor x x').Finite := by
  subst hb
  rw [show glueτ' t hne b b x x' = (t b).τ x x' from funext fun φ => glueτ'_self t hne b x x' φ]
  exact ((t b).isCorrespondence x x').finite

theorem glueτ'_swap (hb : b = b') (hφ : φ ∈ (D b).𝒰.mor x x') :
    glueτ' t hne b' b x' x (A.X.inv φ) = (glueτ' t hne b b' x x' φ).swap := by
  subst hb
  rw [glueτ'_self, glueτ'_self, (t b).swap x' x φ hφ, IndexCorr.swap_swap]

theorem glueτ'_biact (hb : b = b') (hφ : φ ∈ (D b).𝒰.mor x x') (g' : A.X.Isotropy x')
    (g : A.X.Isotropy x) :
    glueτ' t hne b b' x x' (EpGroupoid.biact ((D b).𝒰.nbhd x) ((D b').𝒰.nbhd x') g' φ g) =
      IndexCorr.biact g' (glueτ' t hne b b' x x' φ) g := by
  subst hb
  rw [glueτ'_self, glueτ'_self]
  exact ((t b).isCorrespondence x x').biact φ hφ g' g

theorem glueτ'_compat (hb : b = b') (hφ : φ ∈ (D b).𝒰.mor x x') :
    (glueτ' t hne b b' x x' φ).Sat fun i j =>
      ((D b').S x').s j (A.X.tgt φ) = fibAct φ (((D b).S x).s i (A.X.src φ)) := by
  subst hb
  rw [glueτ'_self]
  exact IndexCorr.sat_mono (fun i j h => h φ (mem_connectedComponentIn hφ))
    (((t b).isCorrespondence x x').compat φ hφ)

end Sides

/-! ### Morphisms of `[0, 1] × X` -/

/-- `(g' ∗ φ ∗ g)₂ = g'₂ ∗ φ₂ ∗ g₂` for connected `V, V'` over `N, N'`. -/
theorem cube_biact_snd {z z' : (A.cubeSEP 1).Obj} (V : (A.cubeSEP 1).X.NatNbhd z)
    (V' : (A.cubeSEP 1).X.NatNbhd z') (hV : IsPreconnected V.U) (hV' : IsPreconnected V'.U)
    (N : A.X.NatNbhd z.2) (N' : A.X.NatNbhd z'.2) (hVN : ∀ y ∈ V.U, y.2 ∈ N.U)
    (hVN' : ∀ y ∈ V'.U, y.2 ∈ N'.U) {φ : (A.cubeSEP 1).Mor}
    (hs : (A.cubeSEP 1).X.src φ ∈ V.U) (ht : (A.cubeSEP 1).X.tgt φ ∈ V'.U)
    (g' : (A.cubeSEP 1).X.Isotropy z') (g : (A.cubeSEP 1).X.Isotropy z) :
    (EpGroupoid.biact V V' g' φ g).2 =
      EpGroupoid.biact N N' (cubeIso z' g') φ.2 (cubeIso z g) := by
  have hΦ : V.rep.Φ g⁻¹ ((A.cubeSEP 1).X.src φ) ∈ V.U := V.Φ_mem _ hs
  have h1 : (V'.rep.Γ g' ((A.cubeSEP 1).X.tgt φ)).2 = N'.rep.Γ (cubeIso z' g') (A.X.tgt φ.2) :=
    cube_Γ_snd V' hV' N' hVN' g' ht
  have h2 : (V.rep.Γ g (V.rep.Φ g⁻¹ ((A.cubeSEP 1).X.src φ))).2 =
      N.rep.Γ (cubeIso z g) (N.rep.Φ (cubeIso z g)⁻¹ (A.X.src φ.2)) := by
    rw [cube_Γ_snd V hV N hVN g hΦ, cube_Φ_eq V hV N hVN g⁻¹ hs, map_inv]
    rfl
  change A.X.comp (V'.rep.Γ g' ((A.cubeSEP 1).X.tgt φ)).2
      (A.X.comp φ.2 (V.rep.Γ g (V.rep.Φ g⁻¹ ((A.cubeSEP 1).X.src φ))).2) = _
  rw [h1, h2]
  rfl

/-- `μ̃(φ, s̃(s(φ))) = s̃'(t(φ))` from `μ(φ₂, s(s(φ₂))) = s'(t(φ₂))`. -/
theorem cubeLiftSec_compat {s s' : A.Obj → A.W} {φ : (A.cubeSEP 1).Mor}
    (hs : A.P (s (A.X.src φ.2)) = A.X.src φ.2) (hs' : A.P (s' (A.X.tgt φ.2)) = A.X.tgt φ.2)
    (h : s' (A.X.tgt φ.2) = fibAct φ.2 (s (A.X.src φ.2))) :
    cubeLiftSec s' ((A.cubeSEP 1).X.tgt φ) =
      fibAct φ (cubeLiftSec s ((A.cubeSEP 1).X.src φ)) := by
  apply cubeVal_injective
  rw [cubeVal_fibAct (P_cubeLiftSec s _), cubeVal_cubeLiftSec hs', cubeVal_cubeLiftSec hs]
  exact Prod.ext rfl h

/-- **`Λ̃` is a functor over `∂([0, 1] × X)`** if `Λ̃(w) = Λ^{side}(w₂)` there and the `Λ^b` are
functors. -/
theorem isBoundaryWFunctor_of_sides (hX : A.X.IsTame) (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {Λ : Bool → A.W → ℚ≥0} (hfun : ∀ b, IsWFunctor A (Λ b)) {Λc : (A.cubeSEP 1).W → ℚ≥0}
    (hΛc : ∀ w, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
      Λc w = Λ (cubeSide ((A.cubeSEP 1).P w)) (cubeVal w).2) :
    IsBoundaryWFunctor (A.cubeSEP 1) Λc := by
  rintro ⟨⟨ψ, v⟩, hv⟩ hq
  change (A.cubeSEP 1).X.src ψ ∈ _ at hq
  change (A.cubeSEP 1).P v = (A.cubeSEP 1).X.src ψ at hv
  have hμ : (A.cubeSEP 1).E.μ ⟨(ψ, v), hv⟩ = fibAct ψ v := (fibAct_of hv).symm
  have hvb : (A.cubeSEP 1).P v ∈ (A.cubeSEP 1).X.PObj.boundary := hv ▸ hq
  have htb : (A.cubeSEP 1).X.tgt ψ ∈ (A.cubeSEP 1).X.PObj.boundary :=
    (mem_boundary_cubeSEP_iff hX hd ((A.cubeSEP 1).X.tgt ψ)).2
      ((mem_boundary_cubeSEP_iff hX hd ((A.cubeSEP 1).X.src ψ)).1 hq)
  have hμb : (A.cubeSEP 1).P (fibAct ψ v) ∈ (A.cubeSEP 1).X.PObj.boundary := by
    rw [P_fibAct hv]; exact htb
  have h' : A.P (cubeVal v).2 = A.X.src ψ.2 := by
    rw [P_cubeVal_snd]; exact congrArg Prod.snd hv
  change Λc ((A.cubeSEP 1).E.μ ⟨(ψ, v), hv⟩) = Λc v
  rw [hμ, hΛc _ hμb, hΛc _ hvb, P_fibAct hv, cubeVal_fibAct hv, hv, cubeSide_src,
    fibAct_of h']
  exact hfun _ ⟨(ψ.2, (cubeVal v).2), h'⟩

/-! ### The glued structure -/

section Glue

variable {Λ : Bool → A.W → ℚ≥0} (D : ∀ b, Decoration A (Λ b))

/-- The open set on which the structure at `z` is lifted: `{t ≷ 1/2} × U_{D^{side z}}(z₂)`. -/
def glueO (z : (A.cubeSEP 1).Obj) : Set (A.cubeSEP 1).Obj :=
  sideSet (cubeSide z) ∩ {p | p.2 ∈ ((D (cubeSide z)).𝒰.nbhd z.2).U}

theorem isOpen_glueO (z : (A.cubeSEP 1).Obj) : IsOpen (glueO D z) :=
  (isOpen_sideSet _).inter (((D _).𝒰.nbhd _).isOpen_U.preimage continuous_snd)

theorem mem_glueO (hX : A.X.IsTame) (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {z : (A.cubeSEP 1).Obj} (hz : z ∈ (A.cubeSEP 1).X.PObj.boundary) : z ∈ glueO D z :=
  ⟨mem_sideSet_cubeSide hX hd hz, ((D _).𝒰.nbhd _).mem_U⟩

variable {D} (𝒰 : (A.cubeSEP 1).X.BoundaryGoodSystem) (h𝒰 : ∀ z, (𝒰.nbhd z).U ⊆ glueO D z)

include h𝒰 in
/-- A morphism of `𝒰̃(z, z')` stays on one side, and its `X`-part lies in `𝒰^b(z₂, z'₂)`. -/
theorem mor_glue {z z' : (A.cubeSEP 1).X.PObj.boundary} {φ : (A.cubeSEP 1).Mor}
    (hφ : φ ∈ 𝒰.mor z z') :
    cubeSide (z : (A.cubeSEP 1).Obj) = cubeSide (z' : (A.cubeSEP 1).Obj) ∧
      φ.2 ∈ (D (cubeSide (z : (A.cubeSEP 1).Obj))).𝒰.mor (z : (A.cubeSEP 1).Obj).2
        (z' : (A.cubeSEP 1).Obj).2 := by
  obtain ⟨hs, ht⟩ := hφ
  have hs' := h𝒰 z hs.1
  have ht' := h𝒰 z' ht.1
  have hb : cubeSide (z : (A.cubeSEP 1).Obj) = cubeSide (z' : (A.cubeSEP 1).Obj) :=
    (cubeSide_of_mem hs'.1).symm.trans ((cubeSide_src φ).trans (cubeSide_of_mem ht'.1))
  refine ⟨hb, hs'.2, ?_⟩
  have h2 := ht'.2
  rw [← hb] at h2
  exact h2

theorem isPreconnected_glue (z : (A.cubeSEP 1).X.PObj.boundary) : IsPreconnected (𝒰.nbhd z).U :=
  (𝒰.isGood z).isConnected.isPreconnected

include h𝒰 in
theorem mem_glue_snd (z : (A.cubeSEP 1).X.PObj.boundary) :
    ∀ y ∈ (𝒰.nbhd z).U, y.2 ∈ ((D (cubeSide (z : (A.cubeSEP 1).Obj))).𝒰.nbhd
      (z : (A.cubeSEP 1).Obj).2).U :=
  fun _ hy => (h𝒰 z hy).2

variable {𝒰} {Λc : (A.cubeSEP 1).W → ℚ≥0}
  (hΛc : ∀ w, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
    Λc w = Λ (cubeSide ((A.cubeSEP 1).P w)) (cubeVal w).2)
  (hF : CubeLiftFace A)

include h𝒰 hF in
theorem glue_face (z : (A.cubeSEP 1).X.PObj.boundary)
    (i : ((D (cubeSide (z : (A.cubeSEP 1).Obj))).S (z : (A.cubeSEP 1).Obj).2).I) :
    IsFaceScPlusSectionOn (A.cubeSEP 1)
      (cubeLiftSec (((D (cubeSide (z : (A.cubeSEP 1).Obj))).S (z : (A.cubeSEP 1).Obj).2).s i))
      (𝒰.nbhd z).bdry :=
  (hF _ _ ((D _).𝒰.nbhd _).isOpen_U (((D _).S _).isScPlusSectionOn i)).mono
    fun _ hy => ⟨(h𝒰 z hy.1).2, hy.2⟩

include h𝒰 hΛc in
theorem glue_rep (z : (A.cubeSEP 1).X.PObj.boundary) :
    ∀ w, (A.cubeSEP 1).P w ∈ (𝒰.nbhd z).bdry →
      Λc w = Λ (cubeSide (z : (A.cubeSEP 1).Obj)) (cubeVal w).2 := fun w hw => by
  rw [hΛc w hw.2, cubeSide_of_mem (h𝒰 z hw.1).1]

/-- **The structure at `z ∈ ∂([0, 1] × X)`**: the structure of `Λ^{side z}` at `z₂`, lifted. -/
def glueS (z : (A.cubeSEP 1).X.PObj.boundary) :
    BoundarySymmetricStructure (A.cubeSEP 1) Λc (𝒰.nbhd z) :=
  liftStructure (𝒰.nbhd z) (isPreconnected_glue 𝒰 z)
    ((D (cubeSide (z : (A.cubeSEP 1).Obj))).S (z : (A.cubeSEP 1).Obj).2)
    (mem_glue_snd 𝒰 h𝒰 z) (glue_face h𝒰 hF z) (glue_rep h𝒰 hΛc z)

/-- `(𝒰̃, S̃)`. -/
def glueDec : BoundaryDecoration (A.cubeSEP 1) Λc :=
  ⟨𝒰, glueS h𝒰 hΛc hF⟩

variable (t : ∀ b, (D b).Tau) (hne : ∀ b x, Nonempty ((D b).S x).I)

/-- **The correspondences over `∂([0, 1] × X)`**: `τ̃_{z,z'}(φ) = τ^b_{z₂,z'₂}(φ₂)`. -/
def glueTau : (glueDec h𝒰 hΛc hF).Tau where
  τ z z' φ := glueτ' t hne (cubeSide (z : (A.cubeSEP 1).Obj)) (cubeSide (z' : (A.cubeSEP 1).Obj))
    (z : (A.cubeSEP 1).Obj).2 (z' : (A.cubeSEP 1).Obj).2 φ.2
  locallyConstant z z' φ hφ := by
    obtain ⟨hb, hφ2⟩ := mor_glue 𝒰 h𝒰 hφ
    exact nhdsWithin_le_nhds
      ((continuous_snd.tendsto φ).eventually (glueτ'_eventually hb hφ2))
  finite z z' := by
    by_cases h : (𝒰.mor z z').Nonempty
    · obtain ⟨φ₀, hφ₀⟩ := h
      obtain ⟨hb, -⟩ := mor_glue 𝒰 h𝒰 hφ₀
      refine (glueτ'_finite (t := t) (hne := hne) (x := (z : (A.cubeSEP 1).Obj).2)
        (x' := (z' : (A.cubeSEP 1).Obj).2) hb).subset ?_
      rintro _ ⟨φ, hφ, rfl⟩
      exact ⟨φ.2, (mor_glue 𝒰 h𝒰 hφ).2, rfl⟩
    · change (_ '' 𝒰.mor z z').Finite
      rw [Set.not_nonempty_iff_eq_empty.1 h]
      exact Set.finite_empty.image _
  swap z z' φ hφ := by
    obtain ⟨hb, hφ2⟩ := mor_glue 𝒰 h𝒰 hφ
    exact glueτ'_swap hb hφ2
  diag z g y hy := by
    have hy2 := mem_glue_snd 𝒰 h𝒰 z y hy.1
    change glueτ' t hne (cubeSide (z : (A.cubeSEP 1).Obj)) (cubeSide (z : (A.cubeSEP 1).Obj))
      (z : (A.cubeSEP 1).Obj).2 (z : (A.cubeSEP 1).Obj).2 ((𝒰.nbhd z).rep.Γ g y).2 = _
    rw [glueτ'_self, cube_Γ_snd (𝒰.nbhd z) (isPreconnected_glue 𝒰 z) _ (mem_glue_snd 𝒰 h𝒰 z) g
      hy.1]
    exact (t _).diag _ (cubeIso _ g) y.2 hy2
  biact z z' φ hφ g' g := by
    obtain ⟨hb, hφ2⟩ := mor_glue 𝒰 h𝒰 hφ
    change glueτ' t hne (cubeSide (z : (A.cubeSEP 1).Obj)) (cubeSide (z' : (A.cubeSEP 1).Obj))
      (z : (A.cubeSEP 1).Obj).2 (z' : (A.cubeSEP 1).Obj).2
      (EpGroupoid.biact (𝒰.nbhd z) (𝒰.nbhd z') g' φ g).2 = _
    rw [cube_biact_snd (𝒰.nbhd z) (𝒰.nbhd z') (isPreconnected_glue 𝒰 z)
      (isPreconnected_glue 𝒰 z') _ _ (mem_glue_snd 𝒰 h𝒰 z) (mem_glue_snd 𝒰 h𝒰 z') hφ.1.1
      hφ.2.1 g' g]
    refine (glueτ'_biact hb hφ2 (cubeIso _ g') (cubeIso _ g)).trans ?_
    exact (IndexCorr.biact_compHom_gl (cubeIso _) (cubeIso _) _ g' g).symm
  compat z z' φ hφ := by
    obtain ⟨hb, hφ2⟩ := mor_glue 𝒰 h𝒰 hφ
    refine IndexCorr.sat_mono (fun i j h => ?_) (glueτ'_compat hb hφ2)
    have hs := (h𝒰 z hφ.1.1).2
    have ht := (h𝒰 z' hφ.2.1).2
    exact cubeLiftSec_compat (((D _).S _).P_s i hs) (((D _).S _).P_s j ht) h

end Glue

/-! ### Structurability -/

/-- **A multisection over `∂([0, 1] × X)` that is `Λ^{side}` there is structurable over the
boundary** (Definition 14.1.7) if `Λ^false`, `Λ^true` are structurable (Definition 13.3.6), for
tame `X` with `d_X ≡ 0` and paracompact `|X|`, given `CubeLiftFace A`. -/
theorem isBoundaryStructurable_of_sides (hX : A.X.IsTame) (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hpara : A.X.HasParacompactOrbitSpace) (hF : CubeLiftFace A) {Λ : Bool → A.W → ℚ≥0}
    (hΛ : ∀ b, IsStructurable A (Λ b)) {Λc : (A.cubeSEP 1).W → ℚ≥0}
    (hΛc : ∀ w, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
      Λc w = Λ (cubeSide ((A.cubeSEP 1).P w)) (cubeVal w).2) :
    IsBoundaryStructurable (A.cubeSEP 1) Λc := by
  choose D ht using fun b => (hΛ b).2
  have t : ∀ b, (D b).Tau := fun b => (ht b).some
  have hne : ∀ b x, Nonempty ((D b).S x).I := fun b x => (D b).nonempty_I (hΛ b).1 x
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hparaC : (A.cubeSEP 1).X.HasParacompactOrbitSpace :=
    A.X.hasParacompactOrbitSpace_cubeProd 1 hpara
  obtain ⟨𝒰, h𝒰⟩ := (A.cubeSEP 1).X.theorem_14_1_6_hyp hXC hparaC
    (fun z => glueO D (z : (A.cubeSEP 1).Obj)) (fun z => isOpen_glueO D _)
    (fun z => mem_glueO D hX hd z.2)
  have h𝒰' : ∀ z, (𝒰.nbhd z).U ⊆ glueO D (z : (A.cubeSEP 1).Obj) := fun z => (h𝒰 z).1
  refine ⟨⟨isBoundaryWFunctor_of_sides hX hd (fun b => (hΛ b).1.1) hΛc, fun z hz =>
    ⟨𝒰.nbhd ⟨z, hz⟩, 𝒰.isGood _, ⟨glueS h𝒰' hΛc hF ⟨z, hz⟩⟩⟩⟩,
    glueDec h𝒰' hΛc hF, ⟨glueTau h𝒰' hΛc hF t hne⟩⟩

/-- **The glued multisection of Corollary 15.3.10 (3) is structurable over the boundary**:
TY's `cubeGlue Λ₀ Λ₁` (`Λ¹` over `t = 1`, `Λ⁰` elsewhere) for structurable `Λ₀`, `Λ₁`, tame `X`
with `d_X ≡ 0` and paracompact `|X|`, given `CubeLiftFace A`. -/
theorem isBoundaryStructurable_cubeGlue_w5 (hX : A.X.IsTame)
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hF : CubeLiftFace A) {Λ₀ Λ₁ : A.W → ℚ≥0} (h₀ : IsStructurable A Λ₀)
    (h₁ : IsStructurable A Λ₁) : IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue Λ₀ Λ₁) :=
  isBoundaryStructurable_of_sides (Λ := fun b => cond b Λ₁ Λ₀) hX hd hpara hF
    (fun b => by cases b; exacts [h₀, h₁]) fun _ hw => cubeGlue_eq_side hX hd Λ₀ Λ₁ hw

/-- **Corollary 15.3.10 (3), p. 699, for two structurable regular perturbations**, with
structurability of the glued data proved: `corollary_15_3_10_3_glue_w5` with its added hypothesis
`hbs` replaced by `CubeLiftFace A` (`X` is tame as `d_X ≡ 0`, TY); the face condition `hbonto` and
Theorem 15.3.9 on `[0, 1] × X` (`h159`) remain added hypotheses. -/
theorem corollary_15_3_10_3_struct_w5 (h159 : theorem_15_3_9_statement (A.cubeSEP 1))
    (hF : CubeLiftFace A) (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    {Λ₀ Λ₁ : A.W → ℚ≥0} (hr₀ : IsRegularPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsRegularPerturbation A f N₁ U₁ Λ₁)
    (hbonto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁)) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (interpAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
      (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ∧
      (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) :=
  corollary_15_3_10_3_glue_w5 h159 hd hpara hPU hf hft hS hr₀ hr₁
    (isBoundaryStructurable_cubeGlue_w5 (A.X.isTame_of_degIndex_eq_zero hd) hd hpara hF hr₀.2.1
      hr₁.2.1) hbonto

end SBLocalization

end Polyfold
