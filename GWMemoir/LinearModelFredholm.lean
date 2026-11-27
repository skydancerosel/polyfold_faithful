import GWMemoir.LinearModel
import GWMemoir.LinearCRSphereFredholm
import GWMemoir.ChartChangeDensity

/-!
# The local model at a constant map from the three-pointed sphere

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, Propositions 4.7 (p. 102),
4.8 (p. 104), 4.23 (p. 118), 4.25 (p. 121), in the case without gluing and without moduli of
the domain: the surface `sphere3` (stable, no automorphisms, no nodes, no Deligne–Mumford
parameters) and a constant map `u ≡ q`.  This tests the Fredholm statements of Chapter 4 on an
honest infinite-dimensional base.  On the constant maps alone (`GWMemoir.ConstantBase`) the base
is finite-dimensional and the propositions have no instance; here the base is the whole section
space.

## The model

For the target `Q = E` with a constant complex structure `J ≡ J₀`, every map of class `(3, δ₀)`
near `u` is `q + ξ` with `ξ` in the section space, and `∂̄_J(q + ξ) = ½ (dξ + J₀ ∘ dξ ∘ j) = Dξ`
(`dbar_const_add`, `isFormRep_dbar_const_add`).  The uniformizer at `u` is then
`O = H^{3,δ₀}_c(S², u*TQ)` with its sc-structure `H^{3+m,δ_m}` (`secSc`), the strong bundle
`O ◁ F` with fibre the forms of class `(2+m, δ_m)` (`fibSc`), and the section `ξ ↦ Dξ`.  The
operator `D` depends on `J` only through `J(q)`, so it is stated for any target.

## What is formalized

* `linOpL`: `D` on every level, `H^{3+m,δ_m} → H^{2+m,δ_m}` on the blocks, from the same
  derivatives and coefficients; `toBase_linOpL`: it agrees with `D` along the inclusions.
* `crBase` (`D` on level `0`), `crBase_isFredholm` (from `linCR_isFredholm_sphere3`),
  `crBase_isScOperator` (`D` preserves the levels; continuity on each level by the closed graph
  theorem, `isScOperator_of_mapsTo`), `crSc` (the sc-operator).
* `LevelRegularity`: elliptic regularity of `D` from level `n` to level `n + 1`, a named
  proposition (the one input not formalized; on level `0` the estimate and the vanishing of the
  cokernel are proved).  `crSc_isScFredholm`: with it, `D` is sc-Fredholm, Fredholm on every level
  with kernel the constants.
* `memoir_proposition_4_7_sphere3`, `memoir_proposition_4_23_sphere3`,
  `memoir_proposition_4_25_sphere3` (no hypothesis), `memoir_proposition_4_8_sphere3`, and
  **`isScFredholmGerm2021_sphere3`**: `∂̄_J` is an sc-Fredholm germ at `u` in this local model.
* `localModel_witness_E2`: the data exist for `Q = ℝ²` with its standard complex structure.

## Readings

* The neighbourhood `O` of `0` is taken to be the whole section space: the section is linear,
  and every open `U ∋ 0` gives the same statements (`GWMemoir.LinearModel` is stated for any
  open `U`).
* Proposition 4.23 is read with no `(a, v)` coordinates (`A = 0`) and `H` the section space.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Set Function Topology Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The derivatives on different levels -/

section Deriv

variable {k k' : ℕ} {d d' : ℝ} {hd : 0 ≤ d} {hd' : 0 ≤ d'}

lemma val_dsH_eq (u : H (k + 1) hd) (u' : H (k' + 1) hd') (h : H.val u = H.val u') :
    H.val (dsH k hd u) = H.val (dsH k' hd' u') := by
  apply Lp.ext
  refine (coeFn_dsH u).trans ((dv_unique (H.toSub u) (idxS k) ?_
    (dv_memLp (H.toSub u') (idxS k'))).trans (coeFn_dsH u').symm)
  have h' : (H.toSub u : Lp ℝ 2 cyl) = H.toSub u' := h
  rw [h']
  exact (dv_spec (H.toSub u') (idxS k')).1

lemma val_dtH_eq (u : H (k + 1) hd) (u' : H (k' + 1) hd') (h : H.val u = H.val u') :
    H.val (dtH k hd u) = H.val (dtH k' hd' u') := by
  apply Lp.ext
  refine (coeFn_dtH u).trans ((dv_unique (H.toSub u) (idxT k) ?_
    (dv_memLp (H.toSub u') (idxT k'))).trans (coeFn_dtH u').symm)
  have h' : (H.toSub u : Lp ℝ 2 cyl) = H.toSub u' := h
  rw [h']
  exact (dv_spec (H.toSub u') (idxT k')).1

end Deriv

/-! ## 2. The operator `D` on every level -/

section Operators

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {u : X.S → Q}
  {A : SectionAtlas (E := E) X u} (G : GlueData A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The block `(j, k)` of a level-`n` section tuple, in `H^{3+n,δ_n}`. -/
def secProjL (n : ℕ) (jk : Fin A.nd × Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) n →L[ℝ] H (3 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (ContinuousLinearMap.proj jk).comp (ContinuousLinearMap.fst ℝ _ _)

/-- `∂_d : H^{3+n,δ_n} → H^{2+n,δ_n}`. -/
def dHL (n : ℕ) (d : Fin 2) :
    H (3 + n) (Neck.δ_nonneg δ h0 hmono n) →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (![dsH (2 + n) (Neck.δ_nonneg δ h0 hmono n), dtH (2 + n) (Neck.δ_nonneg δ h0 hmono n)] d).comp
    (inclH _ _ (by omega : 2 + n + 1 ≤ 3 + n) le_rfl)

include hT in
/-- The zeroth-order term `Z` on level `n`. -/
def zBlockL (n : ℕ) (o : Ix A) :
    (blocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  ∑ j, ((G.D o.1 j).op (2 + n) (Neck.δ_nonneg δ h0 hmono n) (G.hcZ hT o.2.1 o.1 j)
      (G.hsZ hT o.2.1 o.1 j) (Neck.δ_nonneg δ h0 hmono n)).comp
        ((inclH _ _ (by omega : 2 + n ≤ 3 + n) le_rfl).comp (secProjL δ h0 hmono n (j, o.2.2)))

include hT in
/-- The disc block `(i, d, k)` of `R` on level `n`. -/
def rBlockL (n : ℕ) (o : Ix A) :
    (blocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (A.ε o.1)⁻¹ • ((dHL δ h0 hmono n o.2.1).comp (secProjL δ h0 hmono n (o.1, o.2.2)) -
    zBlockL hT G δ h0 hmono n o)

include hT in
/-- `R` on level `n`: section blocks of class `(3+n, δ_n)` to fibre blocks of class `(2+n, δ_n)`. -/
def rOpL (n : ℕ) : (blocks A δ h0 hmono) n →L[ℝ] (fibreBlocks A δ h0 hmono) n :=
  (ContinuousLinearMap.pi fun o => rBlockL hT G δ h0 hmono n o).prod 0

include hT in
/-- **`D = ½ (R + P R)` on level `n`**: `H^{3+n,δ_n} → H^{2+n,δ_n}` on the blocks. -/
def linOpL (n : ℕ) (J₀ : E →L[ℝ] E) :
    (blocks A δ h0 hmono) n →L[ℝ] (fibreBlocks A δ h0 hmono) n :=
  (1 / 2 : ℝ) • (rOpL hT G δ h0 hmono n + (fOp δ h0 hmono (fun _ _ => idCC) (aPI A J₀)
    (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _) (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A)
      n).comp (rOpL hT G δ h0 hmono n))

lemma val_zBlockL (n : ℕ) (o : Ix A) (v : (blocks A δ h0 hmono) n) :
    H.val (zBlockL hT G δ h0 hmono n o v) = ∑ j, (G.D o.1 j).compMul
      (coefZ o.2.1 (G.ρ j) (A.center o.1) (A.ε o.1) (A.center j) (A.ε j))
        (H.val (v.1 (j, o.2.2))) := by
  rw [zBlockL, _root_.sum_apply]
  refine (map_sum (valCLM (2 + n) (Neck.δ_nonneg δ h0 hmono n)) _ _).trans
    (Finset.sum_congr rfl fun j _ => ?_)
  exact ChartChange.val_op (G.hcZ hT o.2.1 o.1 j) (G.hsZ hT o.2.1 o.1 j)
    (Neck.δ_nonneg δ h0 hmono n) _

lemma val_zBlock (o : Ix A) (v : (blocks A δ h0 hmono) 0) :
    H.val (zBlock hT G δ h0 hmono o v) = ∑ j, (G.D o.1 j).compMul
      (coefZ o.2.1 (G.ρ j) (A.center o.1) (A.ε o.1) (A.center j) (A.ε j))
        (H.val (v.1 (j, o.2.2))) := by
  rw [zBlock, _root_.sum_apply]
  refine (map_sum (valCLM 2 (Neck.δ_nonneg δ h0 hmono 0)) _ _).trans
    (Finset.sum_congr rfl fun j _ => ?_)
  exact ChartChange.val_op (G.hcZ hT o.2.1 o.1 j) (G.hsZ hT o.2.1 o.1 j)
    (Neck.δ_nonneg δ h0 hmono 0) _

lemma val_dHL (n : ℕ) (d : Fin 2) (w : H (3 + n) (Neck.δ_nonneg δ h0 hmono n))
    (w' : H 3 (Neck.δ_nonneg δ h0 hmono 0)) (h : H.val w = H.val w') :
    H.val (dHL δ h0 hmono n d w) = H.val (dH δ h0 hmono d w') := by
  fin_cases d
  · exact val_dsH_eq _ _ h
  · exact val_dtH_eq _ _ h

/-- `R` on level `n` agrees with `R` on level `0` along the inclusions. -/
lemma toBase_rOpL (hnn : IsEmpty (Fin A.nn)) (n : ℕ) (v : (blocks A δ h0 hmono) n) :
    (fibreBlocks A δ h0 hmono).toBase n (rOpL hT G δ h0 hmono n v) =
      rOp hT G δ h0 hmono ((blocks A δ h0 hmono).toBase n v) := by
  refine Prod.ext (funext fun o => ?_) (funext fun jk => isEmptyElim jk.1)
  apply valCLM_injective (m := 2) (hδ := Neck.δ_nonneg δ h0 hmono 0)
  refine (val_fibre_toBase n _ o).trans ?_
  change valCLM _ _ (rBlockL hT G δ h0 hmono n o v) =
    valCLM _ _ (rBlock hT G δ h0 hmono o ((blocks A δ h0 hmono).toBase n v))
  rw [rBlockL, rBlock, smul_apply, smul_apply, map_smul,
    map_smul, sub_apply, sub_apply, map_sub, map_sub]
  congr 2
  · exact val_dHL δ h0 hmono n _ _ _ (val_blocks_toBase n v (o.1, o.2.2)).symm
  · exact (val_zBlockL hT G δ h0 hmono n o v).trans ((Finset.sum_congr rfl fun j _ => by
      rw [val_blocks_toBase]).trans (val_zBlock hT G δ h0 hmono o _).symm)

/-- **`D` on level `n` agrees with `D` on level `0` along the inclusions.** -/
lemma toBase_linOpL (hnn : IsEmpty (Fin A.nn)) (n : ℕ) (J₀ : E →L[ℝ] E)
    (v : (blocks A δ h0 hmono) n) :
    (fibreBlocks A δ h0 hmono).toBase n (linOpL hT G δ h0 hmono n J₀ v) =
      linOp hT G δ h0 hmono J₀ ((blocks A δ h0 hmono).toBase n v) := by
  rw [linOpL, linOp, smul_apply, smul_apply, map_smul,
    add_apply, add_apply, map_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    toBase_fOp (fun _ _ => idCC) (aPI A J₀)
      (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _) (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A)
      hnn n,
    toBase_rOpL hT G δ h0 hmono hnn]

end Operators

/-! ## 3. Levels of an sc-subspace -/

lemma mem_range_toBase_ofSubspace (E : ScBanach) {B : Submodule ℝ (E 0)}
    (h : E.IsScSubspace B) (m : ℕ) (x : (E.ofSubspace h) 0) :
    x ∈ range ((E.ofSubspace h).toBase m) ↔ x.1 ∈ range (E.toBase m) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, (E.ofSubspaceScale_coe_toBase h.isClosed m y).symm⟩
  · rintro ⟨y, hy⟩
    have hyB : y ∈ E.levelSub B m := by rw [ScBanach.mem_levelSub, hy]; exact x.2
    exact ⟨⟨y, hyB⟩, Subtype.ext ((E.ofSubspaceScale_coe_toBase h.isClosed m ⟨y, hyB⟩).trans hy)⟩

/-! ## 4. The local model at a constant map from `sphere3` -/

section Sphere

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (G : GlueData A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

variable (A) in
/-- **The base of the local model**: `H^{3,δ₀}_c(S², u*TQ)` with its sc-structure, levels
`H^{3+m,δ_m}` (`sectionSc`, the scale `scaleGW` on each block). -/
abbrev secSc : ScBanach := sectionSc A δ h0 hmono (sphere3_sectionsDense q A δ h0 hmono)

variable (A) in
/-- **The fibre of the local model**: the `(0,1)`-forms of class `(2+m, δ_m)` along `u`
(`fibreSc`, the scale `scaleGWOff 2` on each block). -/
abbrev fibSc : ScBanach := fibreSc J A δ h0 hmono (sphere3_formsDense J q A δ h0 hmono)

/-- `D : H^{3,δ₀}_c(S², u*TQ) → H^{2,δ₀}` on level `0` of the sc-structures. -/
def crBase : (secSc A δ h0 hmono) 0 →L[ℝ] (fibSc J A δ h0 hmono) 0 :=
  ((linOp sphere3_chartsOnto G δ h0 hmono (J.J q)).comp
    ((blocks A δ h0 hmono).levelSub (sectionSpace A δ h0 hmono) 0).subtypeL).codRestrict _
    fun w => linOp_mem rfl sphere3_chartsOnto (fun _ => rfl) G J w.2

lemma crBase_apply (w : (secSc A δ h0 hmono) 0) :
    (crBase J G δ h0 hmono w).1 = linOp sphere3_chartsOnto G δ h0 hmono (J.J q) w.1 := rfl

/-- `D` is onto on level `0` (`cokernelVanishes_sphere3_of_pos`). -/
theorem crBase_surjective (hδ : 0 < δ 0) : Surjective (crBase J G δ h0 hmono) := by
  intro y
  obtain ⟨w, hw⟩ := cokernelVanishes_sphere3_of_pos J G δ h0 hmono hδ ⟨y.1, y.2⟩
  exact ⟨⟨w.1, w.2⟩, Subtype.ext (congrArg Subtype.val hw)⟩

/-- `D` is Fredholm on level `0` (`linCR_isFredholm_sphere3`). -/
theorem crBase_isFredholm (hδ : 0 < δ 0) : (crBase J G δ h0 hmono).IsFredholm := by
  have htop : (crBase J G δ h0 hmono).range = ⊤ :=
    LinearMap.range_eq_top.2 (crBase_surjective J G δ h0 hmono hδ)
  refine isFredholm_of_banach _ ?_ (by rw [htop]; exact isClosed_univ)
    (by rw [htop]; exact Submodule.CoFG.top)
  let f : (crBase J G δ h0 hmono).ker →ₗ[ℝ] (linCR3 J G δ h0 hmono).ker :=
    { toFun := fun x => ⟨⟨x.1.1, x.1.2⟩, by
        have hx : crBase J G δ h0 hmono x.1 = 0 := x.2
        exact Subtype.ext (congrArg Subtype.val hx)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective f fun x y hxy => ?_
  exact Subtype.ext (Subtype.ext (congrArg (fun z : (linCR3 J G δ h0 hmono).ker =>
    ((z : sectionSpace A δ h0 hmono) : (blocks A δ h0 hmono) 0)) hxy))

/-- **`D` preserves the levels**: a section of class `(3+n, δ_n)` is sent to a form of class
`(2+n, δ_n)` (by `linOpL`, built from the same derivatives and coefficients on level `n`). -/
theorem crBase_isScOperator : IsScOperator (crBase J G δ h0 hmono) := by
  refine isScOperator_of_mapsTo fun n x => ?_
  have hnn : IsEmpty (Fin A.nn) := isEmpty_neck_of_nodes_empty rfl A
  have hx : (blocks A δ h0 hmono).toBase n x.1 ∈ sectionSpace A δ h0 hmono := x.2
  have hb : ((secSc A δ h0 hmono).toBase n x).1 = (blocks A δ h0 hmono).toBase n x.1 :=
    (blocks A δ h0 hmono).ofSubspaceScale_coe_toBase (isClosed_sectionSpace A δ h0 hmono) n x
  have hmem : linOpL sphere3_chartsOnto G δ h0 hmono n (J.J q) x.1 ∈
      (fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) n := by
    rw [ScBanach.mem_levelSub, toBase_linOpL sphere3_chartsOnto G δ h0 hmono hnn]
    exact linOp_mem rfl sphere3_chartsOnto (fun _ => rfl) G J hx
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  refine ((fibreBlocks A δ h0 hmono).ofSubspaceScale_coe_toBase
    (isClosed_fibreSpace J A δ h0 hmono) n ⟨_, hmem⟩).trans ?_
  rw [crBase_apply, hb]
  exact toBase_linOpL sphere3_chartsOnto G δ h0 hmono hnn n (J.J q) x.1

/-- **The linearized Cauchy–Riemann operator at `u ≡ q` as an sc-operator**
`H^{3,δ₀}_c(S², u*TQ) → H^{2,δ₀}` (levels `H^{3+m,δ_m} → H^{2+m,δ_m}`). -/
def crSc : ScOperator (secSc A δ h0 hmono) (fibSc J A δ h0 hmono) :=
  (crBase_isScOperator J G δ h0 hmono).toScOperator

@[simp] lemma crSc_zero : crSc J G δ h0 hmono 0 = crBase J G δ h0 hmono :=
  IsScOperator.toScOperator_zero _

/-- **Elliptic regularity of `D` from level `n` to level `n + 1`**, the input of this file which
is not formalized: a section of class `(3+n, δ_n)` whose image `Dξ` is of class
`(3+n, δ_{n+1})` is of class `(4+n, δ_{n+1})`.  On level `0` the corresponding facts (the
estimate and the vanishing of the cokernel) are proved (`ellipticEstimate_sphere3`,
`cokernelVanishes_sphere3_of_pos`). -/
def LevelRegularity : Prop :=
  ∀ (n : ℕ) (v : (blocks A δ h0 hmono) n),
    (blocks A δ h0 hmono).toBase n v ∈ sectionSpace A δ h0 hmono →
    linOp sphere3_chartsOnto G δ h0 hmono (J.J q) ((blocks A δ h0 hmono).toBase n v) ∈
      range ((fibreBlocks A δ h0 hmono).toBase (n + 1)) →
    (blocks A δ h0 hmono).toBase n v ∈ range ((blocks A δ h0 hmono).toBase (n + 1))

/-- `LevelRegularity` makes `D` regularizing (Proposition 1.1.10 of the book, as a property). -/
theorem crSc_isRegularizing (hreg : LevelRegularity J G δ h0 hmono) :
    (crSc J G δ h0 hmono).IsRegularizing := by
  intro m
  induction m with
  | zero => exact fun e _ => ⟨e, rfl⟩
  | succ m ih =>
    intro e he
    obtain ⟨v, hv⟩ := (mem_range_toBase_ofSubspace (blocks A δ h0 hmono)
      (sphere3_sectionsDense q A δ h0 hmono) m e).1
      (ih e ((fibSc J A δ h0 hmono).range_toBase_succ_le m he))
    have hD := (mem_range_toBase_ofSubspace (fibreBlocks A δ h0 hmono)
      (sphere3_formsDense J q A δ h0 hmono) (m + 1) _).1 he
    rw [crSc_zero, crBase_apply, ← hv] at hD
    have := hreg m v (by rw [hv]; exact e.2) hD
    rw [hv] at this
    exact (mem_range_toBase_ofSubspace (blocks A δ h0 hmono)
      (sphere3_sectionsDense q A δ h0 hmono) (m + 1) e).2 this

/-- **`D` is sc-Fredholm** (Definition 1.1.9 of the book) at a constant map from `sphere3`, given
`LevelRegularity`: Fredholm on level `0` (proved) and regularizing (the criterion
`isScFredholm_of_isRegularizing`); every level map `H^{3+m,δ_m} → H^{2+m,δ_m}` is then Fredholm
with the same kernel (the constants). -/
theorem crSc_isScFredholm (hδ : 0 < δ 0) (hreg : LevelRegularity J G δ h0 hmono) :
    IsScFredholm (crSc J G δ h0 hmono) :=
  isScFredholm_of_isRegularizing (by rw [crSc_zero]; exact crBase_isFredholm J G δ h0 hmono hδ)
    (crSc_isRegularizing J G δ h0 hmono hreg)

/-! ### Propositions 4.7, 4.23, 4.25 and the sc-Fredholm germ -/

/-- **Memoir Proposition 4.7, p. 102, in the local model at `u ≡ q`**: `ξ ↦ Dξ` is sc-smooth and
regularizing on `O = H^{3,δ₀}_c(S², u*TQ)`. -/
theorem memoir_proposition_4_7_sphere3 (hreg : LevelRegularity J G δ h0 hmono) :
    Prop_4_7 univ (crSc J G δ h0 hmono 0) :=
  prop_4_7_scOperator _ isOpen_univ (crSc_isRegularizing J G δ h0 hmono hreg)

/-- **Memoir Proposition 4.23, p. 118, in the local model at `u ≡ q`**, with no `(a, v)`
coordinates (`A = 0`: no gluing parameters, no Deligne–Mumford parameters) and `H` the whole
section space. -/
theorem memoir_proposition_4_23_sphere3 (hδ : 0 < δ 0) (hreg : LevelRegularity J G δ h0 hmono) :
    Prop_4_23 univ (crSc J G δ h0 hmono 0) ⊥ ⊤
      ((crSc J G δ h0 hmono).isScSmooth (relOpen_of_isOpen isOpen_univ).isScDomain) :=
  prop_4_23_scOperator _ isOpen_univ (crSc_isScFredholm J G δ h0 hmono hδ hreg)

/-- **Memoir Proposition 4.25, p. 121, in the local model at `u ≡ q`**: the derivative does not
depend on the point (no hypothesis beyond the level property of `D`). -/
theorem memoir_proposition_4_25_sphere3 : Prop_4_25 univ (crSc J G δ h0 hmono 0) ⊥ ⊤ :=
  prop_4_25_scOperator _ isOpen_univ ⊥ ⊤

/-- **Memoir Proposition 4.8, p. 104, in the local model at `u ≡ q`**, from Propositions 4.7,
4.23, 4.25 (`memoir_proposition_4_8_of_4_23`, with `B = ker D` the constants). -/
theorem memoir_proposition_4_8_sphere3 (hδ : 0 < δ 0) (hreg : LevelRegularity J G δ h0 hmono) :
    Prop_4_8 univ (crSc J G δ h0 hmono 0) :=
  prop_4_8_scOperator _ isOpen_univ (mem_univ _) (crSc_isScFredholm J G δ h0 hmono hδ hreg)

/-- **`∂̄_J` is an sc-Fredholm germ at `u ≡ q`** in the local model `O ◁ F → O`, `O` the section
space and `F` the forms, with the section `ξ ↦ Dξ` (Definition 3.1.11 of the book, 2021 p. 96,
through `isScFredholmGerm2021_of_prop_4_23`). -/
theorem isScFredholmGerm2021_sphere3 (hδ : 0 < δ 0) (hreg : LevelRegularity J G δ h0 hmono) :
    (LocalBundle.bundle (fibSc J A δ h0 hmono)
      (relOpen_of_isOpen (E := secSc A δ h0 hmono) isOpen_univ) lmPt).IsScFredholmGerm2021
        (LocalBundle.sec (crSc J G δ h0 hmono 0)) lmPt :=
  isScFredholmGerm2021_scOperator _ (crSc_isScFredholm J G δ h0 hmono hδ hreg)

end Sphere

/-! ## 5. The section is `∂̄_J` near `u` for a linear target -/

section Linear

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ} {X : NodalSurface m}

/-- `d(c + f) = df`. -/
theorem mfderiv_const_add' (f : X.S → E) (c : E) (x : X.S) :
    mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) (fun y => c + f y) x = mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) f x := by
  by_cases hf : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) f x
  · have h := ((hasMFDerivAt_const (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E)) c x).add
      hf.hasMFDerivAt).mfderiv
    exact h.trans (zero_add _)
  · have hg : ¬ MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) (fun y => c + f y) x := fun hg => hf (by
      have := (mdifferentiableAt_const (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E)) (c := -c) (x := x)).add hg
      convert this using 1
      funext y
      simp)
    rw [mfderiv_zero_of_not_mdifferentiableAt hf, mfderiv_zero_of_not_mdifferentiableAt hg]
    rfl

/-- **`∂̄_J(q + η) = ½ (dη + J₀ ∘ dη ∘ j)`** for the target `Q = E` with a constant complex
structure `J ≡ J₀`: near a constant map, `∂̄_J` is the linear operator `D`. -/
theorem dbar_const_add {J : AlmostComplexStructure E E} {J₀ : E →L[ℝ] E} (hJ : ∀ y, J.J y = J₀)
    (q : E) (η : Section E X) : X.dbar J (fun x => q + η x) = projF J₀ (dForm η) := by
  funext x
  simp only [NodalSurface.dbar, NodalSurface.Tu, projF, twist, dForm, hJ, mfderiv_const_add',
    Pi.smul_apply, Pi.add_apply]

variable {q : E} {J : AlmostComplexStructure E E} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (G : GlueData A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- **The section of the local model is `∂̄_J`**: for `Q = E`, `J ≡ J₀`, and a section `η`
represented by `v`, `Dv` represents `∂̄_J(q + η)`. -/
theorem isFormRep_dbar_const_add {J₀ : E →L[ℝ] E} (hJ : ∀ y, J.J y = J₀) {η : Section E sphere3}
    {v : (blocks A δ h0 hmono) 0} (hc : IsContSection (fun _ => q) η) (hr : IsRep η v) :
    IsFormRep (sphere3.dbar J (fun x => q + η x))
      (linOp sphere3_chartsOnto G δ h0 hmono (J.J q) v) := by
  rw [dbar_const_add hJ, hJ q]
  exact isFormRep_linOp rfl sphere3_chartsOnto (fun _ => rfl) G hc hr J₀

end Linear

/-! ## 6. Witness: `ℝ²` with its standard complex structure -/

/-- **The data of the local model exist** for `Q = ℝ²`, `J` the standard complex structure
(constant), `u ≡ 0`: an atlas, gluing data and the weights `δ_n = n + 1`.  The hypotheses of
`isScFredholmGerm2021_sphere3` other than `LevelRegularity` hold there. -/
theorem localModel_witness_E2 :
    ∃ (A : SectionAtlas (E := E2) sphere3 (fun _ => (0 : E2))) (_ : GlueData A),
      (∀ y, jE2.J y = J0) ∧ 0 < ((fun n : ℕ => (n : ℝ) + 1) 0) ∧
        StrictMono (fun n : ℕ => (n : ℝ) + 1) := by
  obtain ⟨A⟩ := sphere3_sectionAtlas (E := E2) (0 : E2)
  obtain ⟨G⟩ := exists_glueData sphere3_chartsOnto A rfl
  exact ⟨A, G, fun _ => rfl, by norm_num, fun a b h => by simpa using h⟩

end GWMemoir
