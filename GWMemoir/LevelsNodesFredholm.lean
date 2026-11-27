import GWMemoir.LevelsNodesOnto

/-!
# `D` with nodes is sc-Fredholm: Propositions 4.7, 4.23, 4.25, 4.8

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, Propositions 4.7 (p. 102),
4.8 (p. 104), 4.23 (p. 118), 4.25 (p. 121), at a constant map `u ≡ q` from two spheres joined at a
node (`twoSpheres`), for weights `0 < δ₀ < δ₁ < ⋯` with `δ_m < 2π` for all `m`.

* `sectionsDense_twoSpheres`, `formsDense_twoSpheres`: the smooth points are dense in every level
  of the section space and of the fibre, so both are sc-Banach spaces (`secScN`, `fibScN`).
* `crScN`: `D` as an sc-operator `H^{3,δ₀}_c → H^{2,δ₀}` with levels `H^{3+m,δ_m} → H^{2+m,δ_m}`.
* `crScN_isRegularizing`, **`crScN_isScFredholm`**, `crScN_isFredholm_lvl`.
* `memoir_proposition_4_7_twoSpheres`, `memoir_proposition_4_23_twoSpheres`,
  `memoir_proposition_4_25_twoSpheres`, `memoir_proposition_4_8_twoSpheres`,
  **`isScFredholmGerm2021_twoSpheres`**: through the sc-operator lemmas of `GWMemoir.LinearModel`,
  which use only that `D` is an sc-Fredholm operator.
* **`twoSpheres_levels_uncond`**: for all such weights there are an atlas and gluing data on which
  all of the above hold; `nodeWeights` (`δ_m = π - 1/(m+2)`) satisfies the hypotheses
  (`nodeWeights_spec`, `twoSpheres_levels_nodeWeights`).
* `isFormRep_dbar_const_add_twoSpheres`: for the target `Q = E` with a constant complex structure,
  `D v` represents `∂̄_J(q + η)`, so the section of the local model is `∂̄_J` near `u`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology NNReal
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

section Fredholm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)} (hsm : NeckSmooth A) (G : GlueDataN A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
  (hA : IsStdNeck A) (hδ : ∀ m, δ m < 2 * Real.pi) (hδ0 : 0 < δ 0) (hG : GlueCharts A)

include J hsm G hA hδ hδ0 hG

/-! ## 1. Density of the smooth points -/

/-- **The smooth sections are dense in every level** of `H^{3,δ₀}_c` (Definition 1.1.6 of the
book): `ξ ∈ X_k` is the limit of `ξ + x_j = w_j - c_j`, `w_j` smooth with `D w_j → D ξ`
(`denseNL`), `D x_j = D w_j - D ξ`, `x_j → 0` (open mapping theorem), `c_j` constant. -/
theorem sectionsDense_twoSpheres : SectionsDense A δ h0 hmono := by
  refine (sectionsDense_iff A δ h0 hmono).2 fun k x hx => ?_
  let xv : (sectionScale A δ h0 hmono) k := ⟨x, hx⟩
  set D := crLvN J hsm G δ h0 hmono k with hDdef
  obtain ⟨z, hzS, hz⟩ :=
    mem_closure_iff_seq_limit.1 (denseNL J δ h0 hmono hsm G hA hG hδ k (D xv).1 (D xv).2)
  choose w hws hwsec hwz using hzS
  let wv : ℕ → (sectionScale A δ h0 hmono) k := fun j => ⟨w j, hwsec j⟩
  have hDw : Tendsto (fun j => ‖D (wv j) - D xv‖) atTop (𝓝 0) := by
    have e1 : (fun j => ‖D (wv j) - D xv‖) = fun j => ‖z j - (D xv).1‖ :=
      funext fun j => by rw [← hwz j]; rfl
    rw [e1]
    exact tendsto_iff_norm_sub_tendsto_zero.1 hz
  obtain ⟨C, -, hpre⟩ := D.exists_preimage_norm_le
    (crLvN_surjective J hsm G δ h0 hmono hA hδ hδ0 hG k)
  choose xs hxs hxsn using fun j => hpre (D (wv j) - D xv)
  have hxs0 : Tendsto (fun j => ‖xs j‖) atTop (𝓝 0) := by
    have h := hDw.const_mul C
    rw [mul_zero] at h
    exact squeeze_zero (fun j => norm_nonneg _) hxsn h
  have hker : ∀ j, D (wv j - xs j - xv) = 0 := fun j => by
    rw [map_sub, map_sub, hxs j]
    abel
  choose e he using fun j => crLvN_ker J hsm G δ h0 hmono hA hδ k _ (hker j)
  have ha : ∀ j, xv + xs j = wv j - cstLvN δ h0 hmono hA hδ k (e j) := fun j => by
    rw [← he j]
    abel
  have hlim : Tendsto (fun j => (xv + xs j).1) atTop (𝓝 x) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have e1 : (fun j => ‖(xv + xs j).1 - x‖) = fun j => ‖xs j‖ :=
      funext fun j => by
        change ‖(x + (xs j).1) - x‖ = ‖(xs j).1‖
        rw [add_sub_cancel_left]
    rw [e1]
    exact hxs0
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun j => ⟨(xv + xs j).2, ?_⟩)
  rw [show (xv + xs j).1 = w j - (cstLvN δ h0 hmono hA hδ k (e j)).1 from
    congrArg Subtype.val (ha j)]
  exact (blocks A δ h0 hmono).smoothLvl_submodule_closed_sub (hws j)
    (cstLvN_mem_smoothLvl δ h0 hmono hA hδ k (e j))

/-- **The smooth forms are dense in every level** of the fibre: `D_k` is onto and maps smooth
points to smooth points. -/
theorem formsDense_twoSpheres : FormsDense J A δ h0 hmono := by
  refine (formsDense_iff A δ h0 hmono J).2 fun k y hy => ?_
  obtain ⟨xv, hxv⟩ := crLvN_surjective J hsm G δ h0 hmono hA hδ hδ0 hG k ⟨y, hy⟩
  have hx := (sectionsDense_iff A δ h0 hmono).1
    (sectionsDense_twoSpheres J hsm G δ h0 hmono hA hδ hδ0 hG) k xv.2
  have hyx : linOpNL twoSpheres_chartsOnto G δ h0 hmono k (J.J q) xv.1 = y :=
    congrArg Subtype.val hxv
  rw [← hyx]
  refine map_mem_closure (linOpNL twoSpheres_chartsOnto G δ h0 hmono k (J.J q)).continuous hx
    fun w hw => ⟨linOpNL_mem J hsm G δ h0 hmono k hw.1, ?_⟩
  refine (fibreBlocks A δ h0 hmono).mem_smoothLvl_iff.2 fun j => ?_
  obtain ⟨w', hw'⟩ := (blocks A δ h0 hmono).mem_smoothLvl_iff.1 hw.2 j
  exact ⟨linOpNL twoSpheres_chartsOnto G δ h0 hmono j (J.J q) w', by
    rw [toBase_linOpNL, toBase_linOpNL, hw']⟩

/-! ## 2. `D` as an sc-operator -/

/-- **`H^{3,δ₀}_c(S, u*TQ)`** for two spheres joined at a node, with its sc-structure (levels
`H^{3+m,δ_m}`). -/
abbrev secScN : ScBanach :=
  sectionSc A δ h0 hmono (sectionsDense_twoSpheres J hsm G δ h0 hmono hA hδ hδ0 hG)

/-- **The fibre**: the `(0,1)`-forms of class `(2+m, δ_m)` along `u`, with its sc-structure. -/
abbrev fibScN : ScBanach :=
  fibreSc J A δ h0 hmono (formsDense_twoSpheres J hsm G δ h0 hmono hA hδ hδ0 hG)

/-- **The linearized Cauchy–Riemann operator at `u ≡ q` as an sc-operator**
`H^{3,δ₀}_c → H^{2,δ₀}`, levels `H^{3+m,δ_m} → H^{2+m,δ_m}` (`crLvN`). -/
def crScN : ScOperator (secScN J hsm G δ h0 hmono hA hδ hδ0 hG)
    (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) where
  lvl m := crLvN J hsm G δ h0 hmono m
  incl_comm m x := crLvN_incl J hsm G δ h0 hmono m x

lemma crScN_lvl (m : ℕ) : crScN J hsm G δ h0 hmono hA hδ hδ0 hG m = crLvN J hsm G δ h0 hmono m :=
  rfl

/-! ## 3. Fredholm on level `0`, regularizing, sc-Fredholm -/

/-- `D` is Fredholm on level `0` (`linCRN_isFredholm_twoSpheres_of_glueCharts`). -/
theorem crLvN_zero_isFredholm : (crLvN J hsm G δ h0 hmono 0).IsFredholm := by
  obtain ⟨hF, -, -⟩ :=
    linCRN_isFredholm_twoSpheres_of_glueCharts J δ h0 hmono hsm G hA hG hδ0 (hδ 0)
  have : FiniteDimensional ℝ (linCRN2 J hsm G δ h0 hmono).ker := hF.finite_ker
  have htop : (crLvN J hsm G δ h0 hmono 0).range = ⊤ :=
    LinearMap.range_eq_top.2 (crLvN_zero_surjective J hsm G δ h0 hmono hA hδ hδ0 hG)
  refine isFredholm_of_banach _ ?_ (by rw [htop]; exact isClosed_univ)
    (by rw [htop]; exact Submodule.CoFG.top)
  let f : (crLvN J hsm G δ h0 hmono 0).ker →ₗ[ℝ] (linCRN2 J hsm G δ h0 hmono).ker :=
    { toFun := fun x => ⟨⟨x.1.1, x.1.2⟩, by
        have hx : crLvN J hsm G δ h0 hmono 0 x.1 = 0 := x.2
        exact Subtype.ext ((linOpNL_zero J G δ h0 hmono x.1.1).symm.trans
          (congrArg Subtype.val hx))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective f fun x y hxy => ?_
  exact Subtype.ext (Subtype.ext (congrArg (fun z : (linCRN2 J hsm G δ h0 hmono).ker =>
    ((z : sectionSpace A δ h0 hmono) : (blocks A δ h0 hmono) 0)) hxy))

/-- On the blocks: a section of class `(3, δ₀)` whose image is of class `(2+m, δ_m)` is of class
`(3+m, δ_m)` (surjectivity on level `m`, and the kernel is the constants). -/
theorem regularizing_blocksN (m : ℕ) (v : (blocks A δ h0 hmono) 0)
    (hv : v ∈ sectionSpace A δ h0 hmono)
    (h : linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v ∈
      range ((fibreBlocks A δ h0 hmono).toBase m)) :
    v ∈ range ((blocks A δ h0 hmono).toBase m) := by
  obtain ⟨y, hy⟩ := h
  have hyF : y ∈ (fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) m := by
    rw [ScBanach.mem_levelSub, hy]; exact linOpN_mem twoSpheres_chartsOnto hsm G J hv
  obtain ⟨x, hx⟩ := crLvN_surjective J hsm G δ h0 hmono hA hδ hδ0 hG m ⟨y, hyF⟩
  have hxm : (blocks A δ h0 hmono).toBase m x.1 ∈ sectionSpace A δ h0 hmono := x.2
  have hk : linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q)
      (v - (blocks A δ h0 hmono).toBase m x.1) = 0 := by
    rw [map_sub, ← toBase_linOpNL, ← crLvN_val J hsm G, hx]
    exact sub_eq_zero.2 hy.symm
  obtain ⟨e, he⟩ := (linOpN_eq_zero_iff J hsm G δ h0 hmono (sub_mem hv hxm)).1 hk
  refine ⟨x.1 + (cstLvN δ h0 hmono hA hδ m e).1, ?_⟩
  rw [map_add, toBase_cstLvN]
  change (blocks A δ h0 hmono).toBase m x.1 + constBlocksN A δ h0 hmono e = v
  rw [he]
  abel

/-- **`D` is regularizing** (Proposition 1.1.10 of the book, as a property): if `Dξ` is of class
`(2+m, δ_m)`, then `ξ` is of class `(3+m, δ_m)`. -/
theorem crScN_isRegularizing : (crScN J hsm G δ h0 hmono hA hδ hδ0 hG).IsRegularizing := by
  intro m e he
  have hD := (mem_range_toBase_ofSubspace (fibreBlocks A δ h0 hmono)
    (formsDense_twoSpheres J hsm G δ h0 hmono hA hδ hδ0 hG) m _).1 he
  refine (mem_range_toBase_ofSubspace (blocks A δ h0 hmono)
    (sectionsDense_twoSpheres J hsm G δ h0 hmono hA hδ hδ0 hG) m e).2 ?_
  refine regularizing_blocksN J hsm G δ h0 hmono hA hδ hδ0 hG m e.1 e.2 ?_
  rw [← linOpNL_zero J G δ h0 hmono]
  exact hD

/-- **`D` is sc-Fredholm** at a constant map from two spheres joined at a node (Definition 1.1.9
of the book): Fredholm on level `0` and regularizing. -/
theorem crScN_isScFredholm : IsScFredholm (crScN J hsm G δ h0 hmono hA hδ hδ0 hG) :=
  isScFredholm_of_isRegularizing (crLvN_zero_isFredholm J hsm G δ h0 hmono hA hδ hδ0 hG)
    (crScN_isRegularizing J hsm G δ h0 hmono hA hδ hδ0 hG)

/-- Every level map `H^{3+m,δ_m} → H^{2+m,δ_m}` is Fredholm and onto, with the index of level
`0`. -/
theorem crScN_isFredholm_lvl (m : ℕ) :
    (crScN J hsm G δ h0 hmono hA hδ hδ0 hG m).IsFredholm ∧
      Surjective (crScN J hsm G δ h0 hmono hA hδ hδ0 hG m) ∧
      fredholmIndex (crScN J hsm G δ h0 hmono hA hδ hδ0 hG m) =
        fredholmIndex (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0) := by
  obtain ⟨-, h⟩ := isScFredholm_of_isRegularizing_index
    (crLvN_zero_isFredholm J hsm G δ h0 hmono hA hδ hδ0 hG)
    (crScN_isRegularizing J hsm G δ h0 hmono hA hδ hδ0 hG)
  exact ⟨(h m).1, crLvN_surjective J hsm G δ h0 hmono hA hδ hδ0 hG m, (h m).2⟩

/-! ## 4. Propositions 4.7, 4.23, 4.25, 4.8 and the sc-Fredholm germ -/

/-- **Memoir Proposition 4.7, p. 102, at a constant map from two spheres joined at a node**:
`ξ ↦ Dξ` is sc-smooth and regularizing on `O = H^{3,δ₀}_c(S, u*TQ)`. -/
theorem memoir_proposition_4_7_twoSpheres :
    Prop_4_7 univ (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0) :=
  prop_4_7_scOperator _ isOpen_univ (crScN_isRegularizing J hsm G δ h0 hmono hA hδ hδ0 hG)

/-- **Memoir Proposition 4.23, p. 118, at a constant map from two spheres joined at a node**,
with no `(a, v)` coordinates and `H` the whole section space. -/
theorem memoir_proposition_4_23_twoSpheres :
    Prop_4_23 univ (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0) ⊥ ⊤
      ((crScN J hsm G δ h0 hmono hA hδ hδ0 hG).isScSmooth
        (relOpen_of_isOpen isOpen_univ).isScDomain) :=
  prop_4_23_scOperator _ isOpen_univ (crScN_isScFredholm J hsm G δ h0 hmono hA hδ hδ0 hG)

/-- **Memoir Proposition 4.25, p. 121, at a constant map from two spheres joined at a node**:
the derivative does not depend on the point. -/
theorem memoir_proposition_4_25_twoSpheres :
    Prop_4_25 univ (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0) ⊥ ⊤ :=
  prop_4_25_scOperator _ isOpen_univ ⊥ ⊤

/-- **Memoir Proposition 4.8, p. 104, at a constant map from two spheres joined at a node.** -/
theorem memoir_proposition_4_8_twoSpheres :
    Prop_4_8 univ (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0) :=
  prop_4_8_scOperator _ isOpen_univ (mem_univ _)
    (crScN_isScFredholm J hsm G δ h0 hmono hA hδ hδ0 hG)

/-- **`∂̄_J` is an sc-Fredholm germ at `u ≡ q`** for two spheres joined at a node, in the local
model `O ◁ F → O` with the section `ξ ↦ Dξ` (Definition 3.1.11 of the book, 2021 p. 96). -/
theorem isScFredholmGerm2021_twoSpheres :
    (LocalBundle.bundle (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG)
      (relOpen_of_isOpen (E := secScN J hsm G δ h0 hmono hA hδ hδ0 hG) isOpen_univ)
        lmPt).IsScFredholmGerm2021
      (LocalBundle.sec (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0)) lmPt :=
  isScFredholmGerm2021_scOperator _ (crScN_isScFredholm J hsm G δ h0 hmono hA hδ hδ0 hG)

end Fredholm

/-! ## 5. Existence of the data -/

section Uncond

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) (q : Q)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- **`D` at a constant map from two spheres joined at a node, on every level** (Memoir
Propositions 4.7, 4.23, 4.25, 4.8): for every `J`, `q` and weights `0 < δ₀ < δ₁ < ⋯` with
`δ_m < 2π` for all `m`, there are an atlas with the standard neck charts and gluing data on which
`D` is an sc-Fredholm operator, onto on every level, and `∂̄_J` is an sc-Fredholm germ at `u ≡ q`
in the local model. -/
theorem twoSpheres_levels_uncond (hδ0 : 0 < δ 0) (hδ : ∀ m, δ m < 2 * Real.pi) :
    ∃ (A : SectionAtlas (E := E) twoSpheres (fun _ => q)) (hsm : NeckSmooth A)
      (G : GlueDataN A) (hA : IsStdNeck A) (hG : GlueCharts A),
        IsScFredholm (crScN J hsm G δ h0 hmono hA hδ hδ0 hG) ∧
        (∀ m, Surjective (crScN J hsm G δ h0 hmono hA hδ hδ0 hG m)) ∧
        Prop_4_7 univ (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0) ∧
        Prop_4_23 univ (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0) ⊥ ⊤
          ((crScN J hsm G δ h0 hmono hA hδ hδ0 hG).isScSmooth
            (relOpen_of_isOpen isOpen_univ).isScDomain) ∧
        Prop_4_25 univ (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0) ⊥ ⊤ ∧
        Prop_4_8 univ (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0) ∧
        (LocalBundle.bundle (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG)
          (relOpen_of_isOpen (E := secScN J hsm G δ h0 hmono hA hδ hδ0 hG) isOpen_univ)
            lmPt).IsScFredholmGerm2021
          (LocalBundle.sec (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0)) lmPt := by
  obtain ⟨A, hA, hG, hsm, ⟨G⟩, -⟩ := exists_glueAtlas_twoSpheres (E := E) q
  exact ⟨A, hsm, G, hA, hG, crScN_isScFredholm J hsm G δ h0 hmono hA hδ hδ0 hG,
    crLvN_surjective J hsm G δ h0 hmono hA hδ hδ0 hG,
    memoir_proposition_4_7_twoSpheres J hsm G δ h0 hmono hA hδ hδ0 hG,
    memoir_proposition_4_23_twoSpheres J hsm G δ h0 hmono hA hδ hδ0 hG,
    memoir_proposition_4_25_twoSpheres J hsm G δ h0 hmono hA hδ hδ0 hG,
    memoir_proposition_4_8_twoSpheres J hsm G δ h0 hmono hA hδ hδ0 hG,
    isScFredholmGerm2021_twoSpheres J hsm G δ h0 hmono hA hδ hδ0 hG⟩

end Uncond

/-- The weights `δ_m = π - 1/(m+2)`. -/
def nodeWeights (m : ℕ) : ℝ := Real.pi - 1 / ((m : ℝ) + 2)

/-- `nodeWeights` satisfies the hypotheses: `0 < δ₀`, strictly increasing, `δ_m < 2π`. -/
theorem nodeWeights_spec : 0 < nodeWeights 0 ∧ StrictMono nodeWeights ∧
    ∀ m, nodeWeights m < 2 * Real.pi := by
  have hπ := Real.pi_gt_three
  refine ⟨?_, fun a b hab => ?_, fun m => ?_⟩
  · simp only [nodeWeights, Nat.cast_zero, zero_add]
    linarith
  · simp only [nodeWeights]
    have hab' : (a : ℝ) < b := Nat.cast_lt.2 hab
    have : 1 / ((b : ℝ) + 2) < 1 / ((a : ℝ) + 2) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  · simp only [nodeWeights]
    have : 0 < 1 / ((m : ℝ) + 2) := by positivity
    linarith

section Witness

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-- **`∂̄_J` is an sc-Fredholm germ at a constant map from two spheres joined at a node**, for
the weights `δ_m = π - 1/(m+2)`: for every `J` and `q` there are an atlas and gluing data on which
`D` is sc-Fredholm and onto on every level. -/
theorem twoSpheres_levels_nodeWeights (J : AlmostComplexStructure E Q) (q : Q) :
    ∃ (A : SectionAtlas (E := E) twoSpheres (fun _ => q)) (hsm : NeckSmooth A)
      (G : GlueDataN A) (hA : IsStdNeck A) (hG : GlueCharts A),
        IsScFredholm (crScN J hsm G nodeWeights nodeWeights_spec.1.le nodeWeights_spec.2.1 hA
          nodeWeights_spec.2.2 nodeWeights_spec.1 hG) ∧
        (∀ m, Surjective (crScN J hsm G nodeWeights nodeWeights_spec.1.le nodeWeights_spec.2.1
          hA nodeWeights_spec.2.2 nodeWeights_spec.1 hG m)) ∧
        (LocalBundle.bundle (fibScN J hsm G nodeWeights nodeWeights_spec.1.le
            nodeWeights_spec.2.1 hA nodeWeights_spec.2.2 nodeWeights_spec.1 hG)
          (relOpen_of_isOpen (E := secScN J hsm G nodeWeights nodeWeights_spec.1.le
            nodeWeights_spec.2.1 hA nodeWeights_spec.2.2 nodeWeights_spec.1 hG) isOpen_univ)
            lmPt).IsScFredholmGerm2021
          (LocalBundle.sec (crScN J hsm G nodeWeights nodeWeights_spec.1.le nodeWeights_spec.2.1
            hA nodeWeights_spec.2.2 nodeWeights_spec.1 hG 0)) lmPt := by
  obtain ⟨A, hsm, G, hA, hG, h1, h2, -, -, -, -, h7⟩ := twoSpheres_levels_uncond J q nodeWeights
    nodeWeights_spec.1.le nodeWeights_spec.2.1 nodeWeights_spec.1 nodeWeights_spec.2.2
  exact ⟨A, hsm, G, hA, hG, h1, h2, h7⟩

end Witness

/-! ## 6. The section is `∂̄_J` near `u` for a linear target -/

section Linear

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {q : E} {J : AlmostComplexStructure E E} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (hsm : NeckSmooth A) (G : GlueDataN A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

include hsm in
/-- **The section of the local model is `∂̄_J`** for two spheres joined at a node: for `Q = E`,
`J ≡ J₀`, and a section `η` represented by `v`, `Dv` represents `∂̄_J(q + η)`. -/
theorem isFormRep_dbar_const_add_twoSpheres {J₀ : E →L[ℝ] E} (hJ : ∀ y, J.J y = J₀)
    {η : Section E twoSpheres} {v : (blocks A δ h0 hmono) 0}
    (hc : IsContSection (fun _ => q) η) (hr : IsRep η v) :
    IsFormRep (twoSpheres.dbar J (fun x => q + η x))
      (linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v) := by
  rw [dbar_const_add hJ, hJ q]
  exact isFormRep_linOpN twoSpheres_chartsOnto hsm G hc hr J₀

end Linear

end GWMemoir
