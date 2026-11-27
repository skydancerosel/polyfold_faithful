import GWMemoir.GlueFilledK

/-!
# The filled section at the nodal constant map, `a ≠ 0`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4.2–§4.3: the filled
section (4.4)–(4.6) (pp. 103–104) and the equations (4.18) (p. 116), at the constant map `u ≡ q`
from two spheres joined at a node (`twoSpheres`), with weights `0 < δ₀ < δ₁ < ⋯ < 2π`.

* `glNodeX`, `glNodeY`: the necks at the nodal points `inl e₂`, `inr e₂`; `nodePairE`,
  `nodePairF`: the node pair `(c, r⁺, r⁻)` of a section and `(ξ⁺, ξ⁻)` of a form, on the
  half-cylinders of the memoir (pp. 13, 49).
* `glA0`: the smallness `a₀`.  For `0 < |a| < a₀` the gluing length `R = φ(|a|)` satisfies
  `σ + 2 < R/2 + s₀` for a `σ` beyond every closed disc of the atlas (`FarBound`), so the gluing
  changes the blocks only where they are free of the discs (`glA0_spec`).
* `glueK a`: the commutator term `K_a h = ½ ⊡̂_a⁻¹(β_a'(r⁺ - τr⁻), β_a'(r⁺ + τr⁻ - 2c'))`, an
  sc⁺-operator, supported in `|s - R/2| ≤ 2` (`β_a'` vanishes off `|s - R/2| ≤ 1`).
* `hatScale a = 1 + (1 - π̂_a)` on the node pair, an sc-isomorphism (inverse `1 - ½(1 - π̂_a)`).
* `filledOp a = hatScale a ∘ (D + K_a)`; `filledOp_glue`, `filledOp_antiGlue`: its hat gluing and
  anti-gluing parts on the node pair, the equations (4.18) with the commutator written out.
* **`filledOp_isScFredholm`**: for `0 < |a| < a₀`, `filledOp a` is sc-Fredholm of index
  `dim E`, on every level Fredholm of index `dim E`, and the constants lie in its kernel.

**Readings.**
* pp. 103, 117: the glued equation carries `½`, "`½[∂_s(v_a + h_a) + …]`", the anti-glued one
  `∂̄₀ = ∂_s + J(0)∂_t`; `D` carries `½` on the necks (`linOpNL`).  We take both as printed;
  the resulting factor `2` on the anti-glued part is `hatScale a`.  The kernel, the index and the
  filler do not depend on it.
* p. 117: "`h_a = ⊕̂_a(h⁺, h⁻)`" is read as `⊕_a` (`h` carries a constant), and `∂̄₀(h_a)` after
  (4.21) as `∂̄₀(⊖_a(h))`.

**What (4.18) adds.**  `filledOp_glue` and `filledOp_antiGlue` read
`⊕̂_a(ξ) = ⊕̂_a(D h) + ½ β_a'(r⁺ - τr⁻)` and `⊖̂_a(ξ) = 2 ⊖̂_a(D h) + β_a'(r⁺ + τr⁻ - 2c')`.
They become (4.18), `⊕̂_a ξ = ½ ∂̄₀ ⊕_a(h)` and `⊖̂_a ξ = ∂̄₀ ⊖_a(h)`, given two statements not
formalized here: `D = ½(∂_s + J₀∂_t)` on the node pair for `s ≥ σ` (the chart-change terms of
`neckRowN` live near `s₀`), and the Leibniz rule
`∂̄₀(β_a r⁺ + (1 - β_a)τr⁻) = ⊕̂_a(∂̄₀ r) + β_a'(r⁺ - τr⁻)` on `H^{3,δ₀}(ℝ × S¹)`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology NNReal
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

open Neck (βa F3 F4 IsCutoff shH reflH glLength glTwist stdCutoff isCutoff_stdCutoff)

/-! ## 1. The node pair and the smallness -/

section Pair

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {q : Q} (A : SectionAtlas (E := E) twoSpheres (fun _ => q))

theorem SectionAtlas.exists_node_inr : ∃ j, A.node j = Sum.inr (pt 2) :=
  A.nodal_node _ rfl _ (Sym2.mem_mk_right _ _)

/-- The neck at the nodal point `inl e₂`. -/
def glNodeX : Fin A.nn := A.exists_node_inl.choose

/-- The neck at the nodal point `inr e₂`. -/
def glNodeY : Fin A.nn := (SectionAtlas.exists_node_inr A).choose

theorem glNodeX_ne_glNodeY : glNodeX A ≠ glNodeY A := fun h =>
  Sum.inl_ne_inr (A.exists_node_inl.choose_spec.symm.trans
    ((congrArg A.node h).trans (SectionAtlas.exists_node_inr A).choose_spec))

variable {A} (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (n : ℕ)
  (k : Fin (Module.finrank ℝ E))

/-- **The node pair of a section**, level `n`, coordinate `k`: the common constant `c` and the
remainders `r⁺ = w_{x,k}` on `ℝ⁺ × S¹`, `r⁻(s', t') = w_{y,k}(-s', -t')` on `ℝ⁻ × S¹` (Memoir
pp. 13, 49; block coordinate `= s`). -/
def nodePairE : (blocks A δ h0 hmono) n →L[ℝ]
    ℝ × (Neck.scHalfPosOff 3 δ h0 hmono) n × (Neck.scHalfNegOff 3 δ h0 hmono) n :=
  (neckCL δ h0 hmono n (glNodeX A, k)).prod
    (((Neck.qPo 3 δ h0 hmono n).comp (neckWL δ h0 hmono n (glNodeX A, k))).prod
      ((Neck.qNo 3 δ h0 hmono n).comp ((reflH 0 0).comp (neckWL δ h0 hmono n (glNodeY A, k)))))

/-- **The node pair of a form**, level `n`, coordinate `k`: `ξ⁺(s, t) = G_{x,k}(s + s₀, t)` on
`ℝ⁺ × S¹`, `ξ⁻(s', t') = -G_{y,k}(s₀ - s', -t')` on `ℝ⁻ × S¹` (the reflection reverses `ds`),
an element of `F` (`scFHat 2`, Memoir p. 51). -/
def nodePairF : (fibreBlocks A δ h0 hmono) n →L[ℝ] (Neck.scFHat 2 δ h0 hmono) n :=
  ((Neck.qPo 2 δ h0 hmono n).comp (glP δ h0 hmono (glNodeX A) n k)).prod
    ((Neck.qNo 2 δ h0 hmono n).comp (-((reflH (A.s0 (glNodeY A)) 0).comp
      (glFibNeck δ h0 hmono n (glNodeY A, k)))))

/-! ### Smallness -/

/-- `min(½, 1/log(|ρ| + e + 1))`: below it the gluing length exceeds `ρ`. -/
def glSmall (ρ : ℝ) : ℝ := min (1 / 2) (Real.log (|ρ| + Real.exp 1 + 1))⁻¹

theorem glSmall_pos (ρ : ℝ) : 0 < glSmall ρ := by
  have h1 : 1 < |ρ| + Real.exp 1 + 1 := by linarith [abs_nonneg ρ, Real.exp_pos 1]
  exact lt_min (by norm_num) (inv_pos.2 (Real.log_pos h1))

theorem lt_glLength {ρ : ℝ} {a : ℂ} (ha : a ≠ 0) (h : ‖a‖ < glSmall ρ) : ρ < glLength a := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  have h1 : 1 < |ρ| + Real.exp 1 + 1 := by linarith [abs_nonneg ρ, Real.exp_pos 1]
  have hl := Real.log_pos h1
  have h2 : Real.log (|ρ| + Real.exp 1 + 1) < ‖a‖⁻¹ := by
    have := lt_of_lt_of_le h (min_le_right _ _)
    rw [lt_inv_comm₀ hpos hl] at this
    exact this
  have h3 : |ρ| + Real.exp 1 + 1 < Real.exp ‖a‖⁻¹ := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < |ρ| + Real.exp 1 + 1)]
    exact Real.exp_lt_exp.2 h2
  unfold glLength Neck.expProfile
  linarith [le_abs_self ρ]

variable (hG : GlueCharts A)

/-- A `σ` beyond every closed disc of the atlas (`exists_farBound`). -/
def glSigma : ℝ := (exists_farBound hG).choose

lemma glSigma_spec : FarBound A (glSigma hG) := (exists_farBound hG).choose_spec

/-- **The smallness `a₀`.** -/
def glA0 : ℝ := glSmall (2 * (glSigma hG + ∑ j, |A.s0 j| + 3))

theorem glA0_pos : 0 < glA0 hG := glSmall_pos _

theorem glA0_le_half : glA0 hG ≤ 1 / 2 := min_le_left _ _

/-- **For `0 < |a| < a₀` the gluing happens where the blocks are free of the discs**:
`σ + 2 < R/2 + s₀` in every neck. -/
theorem glA0_spec {a : ℂ} (ha : a ≠ 0) (ha0 : ‖a‖ < glA0 hG) (j : Fin A.nn) :
    glSigma hG + 2 < glLength a / 2 + A.s0 j := by
  have h := lt_glLength ha ha0
  have hj : |A.s0 j| ≤ ∑ j, |A.s0 j| :=
    Finset.single_le_sum (f := fun j => |A.s0 j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  linarith [neg_abs_le (A.s0 j)]

end Pair

/-! ## 2. Sc⁺-operators and sc-isomorphisms carried by the far part of the necks -/

section Far

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)} (hsm : NeckSmooth A) (G : GlueDataN A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
  (hA : IsStdNeck A) (hδ : ∀ m, δ m < 2 * Real.pi) (hδ0 : 0 < δ 0) (hG : GlueCharts A)

/-- Level maps from the section blocks to the next fibre level, compatible with the inclusions and
carried by the far part of the necks, form an **sc⁺-operator** `H^{3,δ₀}_c → H^{2,δ₀}`. -/
def scPlusOfFar (L : ∀ n, (blocks A δ h0 hmono) n →L[ℝ] (fibreBlocks A δ h0 hmono) (n + 1))
    (hL : ∀ n v, (fibreBlocks A δ h0 hmono).toBase (n + 1) (L n v) =
      (fibreBlocks A δ h0 hmono).toBase 1 (L 0 ((blocks A δ h0 hmono).toBase n v)))
    {σ : ℝ} (hσ : FarBound A σ)
    (hfar : ∀ v, IsFar σ ((fibreBlocks A δ h0 hmono).toBase 1 (L 0 v))) :
    ScPlus (secScN J hsm G δ h0 hmono hA hδ hδ0 hG) (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) where
  lvl m := ((L m).comp ((blocks A δ h0 hmono).levelSub (sectionSpace A δ h0 hmono) m).subtypeL).codRestrict
    ((fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) (m + 1)) fun w => by
      rw [ScBanach.mem_levelSub]
      change (fibreBlocks A δ h0 hmono).toBase (m + 1) (L m w.1) ∈ _
      rw [hL]
      exact mem_fibreSpace_of_isFar J hG hσ (hfar _)
  incl_comm m x := by
    apply Subtype.ext
    apply (fibreBlocks A δ h0 hmono).toBase_injective (m + 1)
    change (fibreBlocks A δ h0 hmono).toBase (m + 1 + 1) (L (m + 1) x.1) =
      (fibreBlocks A δ h0 hmono).toBase (m + 1) (L m ((blocks A δ h0 hmono).incl m x.1))
    rw [hL (m + 1), hL m]
    rfl

lemma scPlusOfFar_val (L : ∀ n, (blocks A δ h0 hmono) n →L[ℝ] (fibreBlocks A δ h0 hmono) (n + 1))
    (hL : ∀ n v, (fibreBlocks A δ h0 hmono).toBase (n + 1) (L n v) =
      (fibreBlocks A δ h0 hmono).toBase 1 (L 0 ((blocks A δ h0 hmono).toBase n v)))
    {σ : ℝ} (hσ : FarBound A σ)
    (hfar : ∀ v, IsFar σ ((fibreBlocks A δ h0 hmono).toBase 1 (L 0 v))) (m : ℕ)
    (x : (secScN J hsm G δ h0 hmono hA hδ hδ0 hG) m) :
    (scPlusOfFar J hsm G δ h0 hmono hA hδ hδ0 hG L hL hσ hfar m x).1 = L m x.1 := rfl

variable (Θ : ∀ n, (fibreBlocks A δ h0 hmono) n →L[ℝ] (fibreBlocks A δ h0 hmono) n)
  (hΘ : ∀ n y, (fibreBlocks A δ h0 hmono).toBase n (Θ n y) =
    Θ 0 ((fibreBlocks A δ h0 hmono).toBase n y))
  {σ : ℝ} (hσ : FarBound A σ) (hfar : ∀ y, IsFar σ (Θ 0 y))

/-- `1 + c Θ` on level `m` of the fibre. -/
def scLvlOfFar (c : ℝ) (m : ℕ) :
    (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) m →L[ℝ] (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) m :=
  ((ContinuousLinearMap.id ℝ _ + c • Θ m).comp
    ((fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) m).subtypeL).codRestrict
    ((fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) m) fun w => by
      rw [ScBanach.mem_levelSub]
      change (fibreBlocks A δ h0 hmono).toBase m (w.1 + c • Θ m w.1) ∈ _
      rw [map_add, map_smul, hΘ]
      exact add_mem w.2 (Submodule.smul_mem _ c (mem_fibreSpace_of_isFar J hG hσ (hfar _)))

lemma scLvlOfFar_val (c : ℝ) (m : ℕ) (x : (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) m) :
    (scLvlOfFar J hsm G δ h0 hmono hA hδ hδ0 hG Θ hΘ hσ hfar c m x).1 = x.1 + c • Θ m x.1 := rfl

include hΘ in
lemma incl_of_far (m : ℕ) (y : (fibreBlocks A δ h0 hmono) (m + 1)) :
    (fibreBlocks A δ h0 hmono).incl m (Θ (m + 1) y) = Θ m ((fibreBlocks A δ h0 hmono).incl m y) := by
  apply (fibreBlocks A δ h0 hmono).toBase_injective m
  change (fibreBlocks A δ h0 hmono).toBase (m + 1) (Θ (m + 1) y) = _
  rw [hΘ, hΘ]
  rfl

/-- An idempotent `Θ` compatible with the inclusions and carried by the far part of the necks
gives the **sc-isomorphism** `1 + Θ` of the fibre, with inverse `1 - ½Θ`. -/
def scIsoOfIdem (hidem : ∀ n y, Θ n (Θ n y) = Θ n y) :
    ScIso (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) where
  lvl m := ContinuousLinearEquiv.equivOfInverse
    (scLvlOfFar J hsm G δ h0 hmono hA hδ hδ0 hG Θ hΘ hσ hfar 1 m)
    (scLvlOfFar J hsm G δ h0 hmono hA hδ hδ0 hG Θ hΘ hσ hfar (-(1 / 2)) m)
    (fun x => Subtype.ext (by
      rw [scLvlOfFar_val, scLvlOfFar_val, map_add, map_smul, hidem]
      module))
    (fun x => Subtype.ext (by
      rw [scLvlOfFar_val, scLvlOfFar_val, map_add, map_smul, hidem]
      module))
  incl_comm m x := Subtype.ext (by
    change (fibreBlocks A δ h0 hmono).incl m (x.1 + (1 : ℝ) • Θ (m + 1) x.1) =
      (fibreBlocks A δ h0 hmono).incl m x.1 + (1 : ℝ) • Θ m ((fibreBlocks A δ h0 hmono).incl m x.1)
    rw [map_add, map_smul, incl_of_far δ h0 hmono Θ hΘ])

lemma scIsoOfIdem_val (hidem : ∀ n y, Θ n (Θ n y) = Θ n y) (m : ℕ)
    (x : (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) m) :
    (scIsoOfIdem J hsm G δ h0 hmono hA hδ hδ0 hG Θ hΘ hσ hfar hidem m x).1 =
      x.1 + (1 : ℝ) • Θ m x.1 := rfl

end Far

/-! ## 3. `K_a`, `hatScale a`, `filledOp a` -/

section Filled

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)} (hsm : NeckSmooth A) (G : GlueDataN A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
  (hA : IsStdNeck A) (hδ : ∀ m, δ m < 2 * Real.pi) (hδ0 : 0 < δ 0) (hG : GlueCharts A)
  {a : ℂ} (ha : a ≠ 0) (ha0 : ‖a‖ < glA0 hG)

/-- **The commutator term `K_a`** as an sc⁺-operator `H^{3,δ₀}_c → H^{2,δ₀}` (levels
`H^{3+m,δ_m} → H^{2+m+1,δ_{m+1}}`), `0 < |a| < a₀`, with the cut-off `stdCutoff` of (2.1). -/
def glueK : ScPlus (secScN J hsm G δ h0 hmono hA hδ hδ0 hG) (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) :=
  scPlusOfFar J hsm G δ h0 hmono hA hδ hδ0 hG
    (fun n => glKL δ h0 hmono isCutoff_stdCutoff (glLength a) (glTwist a) (glNodeX A) (glNodeY A) n)
    (fun _ v => toBase_glKL (glNodeX_ne_glNodeY A) v) (glSigma_spec hG)
    (fun v => isFar_glKL (glNodeX_ne_glNodeY A) (glA0_spec hG ha ha0) v)

/-- **`hatScale a = 1 + (1 - π̂_a)` on the node pair**, an sc-isomorphism of the fibre: it
doubles the hat anti-gluing part and keeps the hat gluing part (`glHat_add_theta`,
`glAnti_add_theta`). -/
def hatScale : ScIso (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) :=
  scIsoOfIdem J hsm G δ h0 hmono hA hδ hδ0 hG
    (fun n => glTheta δ h0 hmono isCutoff_stdCutoff (glLength a) (glTwist a) (glNodeX A) (glNodeY A) n)
    (fun _ y => toBase_glTheta (glNodeX_ne_glNodeY A) y) (glSigma_spec hG)
    (fun y => isFar_glTheta (glNodeX_ne_glNodeY A) (glA0_spec hG ha ha0) y)
    (fun _ y => glTheta_idem (glNodeX_ne_glNodeY A) y)

/-- **The linearization of the filled section at `(a, 0)`**, `ξ = hatScale a (D h + K_a h)`
((4.4)–(4.6), (4.18)): on the node pair its hat gluing part is `½ ∂̄₀ ⊕_a(h)` and its hat
anti-gluing part `∂̄₀ ⊖_a(h)` (`filledOp_glue`, `filledOp_antiGlue`); elsewhere it is `D h`. -/
def filledOp : ScOperator (secScN J hsm G δ h0 hmono hA hδ hδ0 hG) (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) :=
  (hatScale J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0).toScOperator.comp
    (crScN J hsm G δ h0 hmono hA hδ hδ0 hG + (glueK J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0).toScOperator)

lemma filledOp_val (h : (secScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0) :
    (filledOp J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0 0 h).1 =
      ((crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0 h).1 +
        (fibreBlocks A δ h0 hmono).incl 0 (glKL δ h0 hmono isCutoff_stdCutoff (glLength a)
          (glTwist a) (glNodeX A) (glNodeY A) 0 h.1)) +
      (1 : ℝ) • glTheta δ h0 hmono isCutoff_stdCutoff (glLength a) (glTwist a) (glNodeX A)
        (glNodeY A) 0 ((crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0 h).1 +
          (fibreBlocks A δ h0 hmono).incl 0 (glKL δ h0 hmono isCutoff_stdCutoff (glLength a)
            (glTwist a) (glNodeX A) (glNodeY A) 0 h.1)) := rfl

/-- **(4.18), hat gluing part**: `⊕̂_a(ξ) = ⊕̂_a(D h) + ½ β_a'(r⁺ - τr⁻)` on the node pair,
in every coordinate `k`. -/
theorem filledOp_glue (h : (secScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0)
    (k : Fin (Module.finrank ℝ E)) :
    glHat δ h0 hmono isCutoff_stdCutoff (glLength a) (glTwist a) (glNodeX A) (glNodeY A) 0 k
        (filledOp J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0 0 h).1 =
      glHat δ h0 hmono isCutoff_stdCutoff (glLength a) (glTwist a) (glNodeX A) (glNodeY A) 0 k
          (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0 h).1 +
        (1 / 2 : ℝ) • glComP δ h0 hmono isCutoff_stdCutoff (glLength a) (glTwist a) (glNodeX A)
          (glNodeY A) 0 k h.1 := by
  rw [filledOp_val, one_smul, glHat_add_theta (glNodeX_ne_glNodeY A), map_add,
    glHat_K (glNodeX_ne_glNodeY A)]

/-- **(4.18), hat anti-gluing part**: `⊖̂_a(ξ) = 2 ⊖̂_a(D h) + β_a'(r⁺ + τr⁻ - 2c')` on the node
pair, in every coordinate `k`. -/
theorem filledOp_antiGlue (h : (secScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0)
    (k : Fin (Module.finrank ℝ E)) :
    glAnti δ h0 hmono isCutoff_stdCutoff (glLength a) (glTwist a) (glNodeX A) (glNodeY A) 0 k
        (filledOp J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0 0 h).1 =
      (2 : ℝ) • glAnti δ h0 hmono isCutoff_stdCutoff (glLength a) (glTwist a) (glNodeX A)
          (glNodeY A) 0 k (crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0 h).1 +
        glComM δ h0 hmono isCutoff_stdCutoff (glLength a) (glTwist a) (glNodeX A)
          (glNodeY A) 0 k h.1 := by
  rw [filledOp_val, one_smul, glAnti_add_theta (glNodeX_ne_glNodeY A), map_add,
    glAnti_K (glNodeX_ne_glNodeY A), smul_add, smul_smul]
  norm_num

/-- `K_a` vanishes on the constants. -/
theorem glueK_const (e : E) :
    (glueK J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0).toScOperator 0
      (cstScN J hsm G δ h0 hmono hA hδ hδ0 hG e) = 0 := by
  apply Subtype.ext
  change (fibreBlocks A δ h0 hmono).incl 0 (glKL δ h0 hmono isCutoff_stdCutoff (glLength a)
    (glTwist a) (glNodeX A) (glNodeY A) 0 (constBlocksN A δ h0 hmono e)) = 0
  rw [glKL_const, map_zero]

/-- **Target (i)**: for `0 < |a| < a₀`, `filledOp a = hatScale a ∘ (D + K_a)` is sc-Fredholm of
index `dim E`; every level map is Fredholm of index `dim E`; the constants lie in its kernel.
(`D` is sc-Fredholm of index `dim E`, `twoSpheres_levels_uncond`; `K_a` is sc⁺, Proposition
1.1.11 of the book; `hatScale a` is an sc-isomorphism.) -/
theorem filledOp_isScFredholm :
    IsScFredholm (filledOp J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0) ∧
      scIndex (filledOp J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0) = Module.finrank ℝ E ∧
      (∀ m, ((filledOp J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0) m).IsFredholm ∧
        fredholmIndex ((filledOp J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0) m) =
          Module.finrank ℝ E) ∧
      ∀ e, filledOp J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0 0
        (cstScN J hsm G δ h0 hmono hA hδ hδ0 hG e) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := isScFredholm_filled_of J hsm G δ h0 hmono hA hδ hδ0 hG
    (glueK J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0) (hatScale J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0)
  exact ⟨h1, h2, h3, h4 (glueK_const J hsm G δ h0 hmono hA hδ hδ0 hG ha ha0)⟩

end Filled

end GWMemoir
