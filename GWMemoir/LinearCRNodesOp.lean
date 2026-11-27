import GWMemoir.LinearCRNodesKernel
import GWMemoir.CompletenessNodes
import GWMemoir.CokernelSphere

/-!
# The linearized Cauchy–Riemann operator at a constant map, with nodes: the operator

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Proposition 4.23,
p. 118, level `0`, `a = 0`): at the constant map `u ≡ q` the linearization
`D η = ½ (dη + J(q) ∘ dη ∘ j)` as a bounded operator from the section blocks of
`GWMemoir.SectionSpaces` to the fibre blocks of `GWMemoir.Fibres`, on a surface with nodal pairs.

* `GlueDataN A`: functions `ρ_i` on the discs and `χ_j(s)` of `s` alone on the necks with
  `∑ ρ_i + ∑ χ_j = 1`, the changes of disc charts on the pieces of the `ρ_i`, and changes of
  charts between the discs and the necks, cut along `t` into two pieces, one of them rotated by
  `θ` (`ChartChange` needs a compact set in the open strip).
* `zBlockN`, `rBlockN`: the disc rows `ε_i⁻¹ (∂_d v_{i,k} - ∂_d β · η_k)`, with `∂_d β · η_k` read
  from the disc blocks through `ρ_i` and from the neck blocks through `χ_j`.
* `neckRowN`: the neck rows
  `½ (∂_s + J(q) ∂_t) v_j(s - s₀, t) - ½ β'(s - s₀) (v⁺ - c)`, with `β'(s - s₀) (v⁺ - c)` read
  through `ρ_i` from the disc blocks, through the multiplier `β'(s - s₀) χ(s) / β(s - s₀)` from
  the shifted neck block, and the constant `c` with `β'(s - s₀)(1 - χ(s))`.
* **`linOpN`**: the disc rows `½ (R + P R)` as in `linOp`, and the neck rows: a bounded operator
  from the level-`0` section blocks to the level-`0` fibre blocks.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Gluing data with necks -/

section Glue

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q} (A : SectionAtlas (E := E) X (fun _ => q))

/-- `β'`, the derivative of the cut-off `β = smoothTransition` of the neck blocks. -/
abbrev dTr : ℝ → ℝ := deriv Real.smoothTransition

/-- **Gluing data with necks**: functions `ρ_i` on the discs and `χ_j` on the necks, the latter
depending on `s` alone, with `∑ ρ_i + ∑ χ_j = 1`; the changes of disc charts on the pieces of the
`ρ_i`; the changes of charts from the discs to the necks (`Dn`, coefficients `cN`) and from the
necks to the discs (`Dd`, coefficients `cD`), each in two pieces, the piece `a` being read in
the neck rotated by `θ a`. -/
structure GlueDataN where
  ρ : Fin A.nd → C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯
  hρ : ∀ i, tsupport (ρ i) ⊆ discSet (A.center i) (A.ε i)
  D : Fin A.nd → Fin A.nd → ChartChange
  hDK : ∀ i j, (D i j).K = pieceK (ρ j) (A.center i) (A.ε i)
  hDψ : ∀ i j, ∀ p ∈ (D i j).K,
    (D i j).ψ p = dtrans (A.center i) (A.ε i) (A.center j) (A.ε j) p
  χ : Fin A.nn → ℝ → ℝ
  χ_smooth : ∀ j, ContDiff ℝ ∞ (χ j)
  χ_zero : ∀ j s, s ≤ A.s0 j + 1 / 2 → χ j s = 0
  χ_one : ∀ j s, A.s0 j + 1 ≤ s → χ j s = 1
  χS : Fin A.nn → C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯
  χS_polar : ∀ j j' (p : ℝ × ℝ), A.s0 j ≤ p.1 → p.1 ≤ A.s0 j + 1 →
    χS j' (X.polar (A.hol j) p) = if j' = j then χ j p.1 else 0
  sum_one : ∀ y, ∑ i, ρ i y + ∑ j, χS j y = 1
  θ : Fin 2 → ℝ
  Dn : Fin A.nd → Fin A.nn → Fin 2 → ChartChange
  cN : Fin 2 → Fin A.nd → Fin A.nn → Fin 2 → ℝ × ℝ → ℝ
  cN_smooth : ∀ d i j a, ContDiff ℝ ∞ (cN d i j a)
  cN_supp : ∀ d i j a, tsupport (cN d i j a) ⊆ (Dn i j a).K
  Dn_pt : ∀ i j a, ∀ p ∈ (Dn i j a).K,
    X.polar (A.hol j) (((Dn i j a).ψ p).1 + A.s0 j, ((Dn i j a).ψ p).2 - θ a) =
      X.discPt (A.center i) (A.ε i) p
  cN_sum : ∀ d i j p, ∑ a, cN d i j a p * Real.smoothTransition ((Dn i j a).ψ p).1 =
    dCut d p * χS j (X.discPt (A.center i) (A.ε i) p)
  Dd : Fin A.nn → Fin A.nd → Fin 2 → ChartChange
  cD : Fin A.nn → Fin A.nd → Fin 2 → ℝ × ℝ → ℝ
  cD_smooth : ∀ j i a, ContDiff ℝ ∞ (cD j i a)
  cD_supp : ∀ j i a, tsupport (cD j i a) ⊆ (Dd j i a).K
  Dd_pt : ∀ j i a, ∀ p ∈ (Dd j i a).K,
    X.discPt (A.center i) (A.ε i) ((Dd j i a).ψ p) = X.polar (A.hol j) (p.1, p.2 + θ a)
  cD_sum : ∀ j i (x : ℝ × ℝ), ∑ a, cD j i a (Neck.shT 0 (θ a) x) *
      discCut ((Dd j i a).ψ (Neck.shT 0 (θ a) x)) =
    dTr (x.1 - A.s0 j) * ρ i (X.polar (A.hol j) x)

end Glue

/-! ## 2. The pieces of the operator -/

section Pieces

lemma dTr_eq_zero_of_neg {x : ℝ} (hx : x < 0) : dTr x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hx] with y hy using
      Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  rw [dTr, h.deriv_eq, deriv_const]

lemma dTr_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) : dTr x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using
      Real.smoothTransition.one_of_one_le (le_of_lt hy)
  rw [dTr, h.deriv_eq, deriv_const]

lemma contDiff_dTr : ContDiff ℝ ∞ dTr :=
  (contDiff_infty_iff_deriv.1 Real.smoothTransition.contDiff).2

variable {s₀ : ℝ} {χ : ℝ → ℝ}

/-- The multiplier `β'(s - s₀) χ(s) / β(s - s₀)` of the neck rows. -/
def mulN (s₀ : ℝ) (χ : ℝ → ℝ) (s : ℝ) : ℝ :=
  dTr (s - s₀) * χ s / Real.smoothTransition (s - s₀)

lemma mulN_eq_zero (hz : ∀ s, s ≤ s₀ + 1 / 2 → χ s = 0) {s : ℝ}
    (hs : s ∉ Icc s₀ (s₀ + 2)) : mulN s₀ χ s = 0 := by
  rcases not_and_or.1 hs with h | h
  · rw [mulN, hz s (by linarith [not_le.1 h]), mul_zero, zero_div]
  · rw [mulN, dTr_eq_zero_of_one_lt (by linarith [not_le.1 h]), zero_mul, zero_div]

lemma contDiff_mulN (hχ : ContDiff ℝ ∞ χ) (hz : ∀ s, s ≤ s₀ + 1 / 2 → χ s = 0) :
    ContDiff ℝ ∞ (mulN s₀ χ) := by
  refine contDiff_iff_contDiffAt.2 fun s => ?_
  rcases lt_or_ge s₀ s with h | h
  · have hpos : 0 < Real.smoothTransition (s - s₀) :=
      Real.smoothTransition.pos_of_pos (by linarith)
    exact ((contDiff_dTr.comp (contDiff_id.sub contDiff_const)).contDiffAt.mul
      hχ.contDiffAt).div
      ((Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt)
      hpos.ne'
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (show s < s₀ + 1 / 2 by linarith)] with y hy
    rw [mulN, hz y (le_of_lt hy), mul_zero, zero_div]

lemma hasCompactSupport_mulN (hz : ∀ s, s ≤ s₀ + 1 / 2 → χ s = 0) :
    HasCompactSupport (mulN s₀ χ) :=
  HasCompactSupport.intro isCompact_Icc fun _ hs => mulN_eq_zero hz hs

lemma mult_mulN (hχ : ContDiff ℝ ∞ χ) (hz : ∀ s, s ≤ s₀ + 1 / 2 → χ s = 0) (k : ℕ) :
    Mult k (mulN s₀ χ) := by
  obtain ⟨C, hC⟩ := (contDiff_mulN hχ hz).continuous.bounded_above_of_compact_support
    (hasCompactSupport_mulN hz)
  refine Neck.mult_of_deriv (contDiff_mulN hχ hz) (C := C) (fun s => ?_)
    (hasCompactSupport_mulN hz).deriv k
  simpa [Real.norm_eq_abs] using hC s

/-- The coefficient `β'(s - s₀)(1 - χ(s))` of the neck constant in the neck rows. -/
def cstN (s₀ : ℝ) (χ : ℝ → ℝ) (x : ℝ × ℝ) : ℝ := dTr (x.1 - s₀) * (1 - χ x.1)

lemma isTest_cstN (hχ : ContDiff ℝ ∞ χ) : IsTest (cstN s₀ χ) where
  smooth := ((contDiff_dTr.comp (contDiff_fst.sub contDiff_const)).mul
    (contDiff_const.sub (hχ.comp contDiff_fst)))
  periodic _ _ := rfl
  bddSupp := ⟨|s₀| + 2, fun s t hs => by
    simp only [cstN]
    rcases le_or_gt 0 s with h | h
    · rw [abs_of_nonneg h] at hs
      rw [dTr_eq_zero_of_one_lt (by linarith [le_abs_self s₀]), zero_mul]
    · rw [abs_of_neg h] at hs
      rw [dTr_eq_zero_of_neg (by linarith [neg_abs_le s₀]), zero_mul]⟩

end Pieces

/-! ## 3. The operator -/

section Operators

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {q : Q}
  {A : SectionAtlas (E := E) X (fun _ => q)} (G : GlueDataN A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The remainder of the neck block `(j, k)` of a level-`0` section tuple, in `H³`. -/
def neckW (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) 0 →L[ℝ] H 3 (Neck.δ_nonneg δ h0 hmono 0) :=
  (ContinuousLinearMap.snd ℝ ℝ _).comp
    ((ContinuousLinearMap.proj jk).comp (ContinuousLinearMap.snd ℝ _ _))

/-- The constant of the neck block `(j, k)`. -/
def neckC (jk : Fin A.nn × Fin (Module.finrank ℝ E)) : (blocks A δ h0 hmono) 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ _).comp
    ((ContinuousLinearMap.proj jk).comp (ContinuousLinearMap.snd ℝ _ _))

lemma neckW_apply (v : (blocks A δ h0 hmono) 0) (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    neckW δ h0 hmono jk v = (neckBlock v jk.1 jk.2).2 := rfl

lemma neckC_apply (v : (blocks A δ h0 hmono) 0) (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    neckC δ h0 hmono jk v = (neckBlock v jk.1 jk.2).1 := rfl

/-- The coefficient `∂_d β · (χ_j ∘ discPt_i)` of the neck constants in the disc rows. -/
def cstD (d : Fin 2) (i : Fin A.nd) (j : Fin A.nn) (p : ℝ × ℝ) : ℝ :=
  dCut d p * G.χS j (X.discPt (A.center i) (A.ε i) p)

include hT in
lemma contDiff_cstD (d : Fin 2) (i : Fin A.nd) (j : Fin A.nn) : ContDiff ℝ ∞ (cstD G d i j) :=
  (contDiff_dCut d).mul (contDiff_comp_discPt hT (G.χS j) _ _)

lemma tsupport_cstD (d : Fin 2) (i : Fin A.nd) (j : Fin A.nn) :
    tsupport (cstD G d i j) ⊆ closedDisc :=
  (tsupport_mul_subset_left (f := dCut d)).trans
    ((ChartChange.tsupport_dir_subset _ _).trans tsupport_discCut)

include hT in
lemma GlueDataN.hsZ (d : Fin 2) (i j : Fin A.nd) :
    tsupport (coefZ d (G.ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j)) ⊆ (G.D i j).K :=
  (G.hDK i j).symm ▸ tsupport_coefZ_sub hT d _ _ _ _ _

include hT in
/-- The disc block `(i, d, k)` of the zeroth-order term: `∂_d β · η_k` read through the disc
blocks (`ρ_{i'}`), the neck blocks (`χ_j`) and the neck constants. -/
def zBlockN (o : Ix A) : (blocks A δ h0 hmono) 0 →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0) :=
  ∑ i', ((G.D o.1 i').op 2 (Neck.δ_nonneg δ h0 hmono 0)
      (contDiff_coefZ hT o.2.1 (G.ρ i') _ _ _ _ (G.hρ i')) (G.hsZ hT o.2.1 o.1 i')
      (Neck.δ_nonneg δ h0 hmono 0)).comp
        ((incl32 δ h0 hmono).comp (secProj δ h0 hmono (i', o.2.2))) +
  ∑ j, ∑ a, ((G.Dn o.1 j a).op 2 (Neck.δ_nonneg δ h0 hmono 0) (G.cN_smooth o.2.1 o.1 j a)
      (G.cN_supp o.2.1 o.1 j a) (Neck.δ_nonneg δ h0 hmono 0)).comp
        ((Neck.shH 0 (G.θ a)).comp ((incl32 δ h0 hmono).comp (neckW δ h0 hmono (j, o.2.2)))) +
  ∑ j, (neckC δ h0 hmono (j, o.2.2)).smulRight
    (toHdisc (contDiff_cstD hT G o.2.1 o.1 j) (tsupport_cstD G o.2.1 o.1 j) 2
      (Neck.δ_nonneg δ h0 hmono 0))

include hT in
/-- The disc block `(i, d, k)` of `R`: `ε_i⁻¹ (∂_d v_{i,k} - (Zv)_{i,d,k})`. -/
def rBlockN (o : Ix A) : (blocks A δ h0 hmono) 0 →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0) :=
  (A.ε o.1)⁻¹ • ((dH δ h0 hmono o.2.1).comp (secProj δ h0 hmono (o.1, o.2.2)) -
    zBlockN hT G δ h0 hmono o)

include hT in
/-- `R` on the disc blocks, `0` on the neck blocks. -/
def rOpN : (blocks A δ h0 hmono) 0 →L[ℝ] (fibreBlocks A δ h0 hmono) 0 :=
  (ContinuousLinearMap.pi fun o => rBlockN hT G δ h0 hmono o).prod 0

include hT in
/-- `½ (R + P R)`, whose disc blocks are the disc rows of `D`. -/
def discPartN (J₀ : E →L[ℝ] E) : (blocks A δ h0 hmono) 0 →L[ℝ] (fibreBlocks A δ h0 hmono) 0 :=
  (1 / 2 : ℝ) • (rOpN hT G δ h0 hmono + (fOp δ h0 hmono (fun _ _ => idCC) (aPI A J₀)
    (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _) (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A)
      0).comp (rOpN hT G δ h0 hmono))

/-- The matrix of `J₀` in the fixed basis of `E`. -/
def Jm (J₀ : E →L[ℝ] E) (k l : Fin (Module.finrank ℝ E)) : ℝ :=
  crd k (J₀ (Module.finBasis ℝ E l))

/-- **The neck row `(j, k)`**: `½ (∂_s + J₀ ∂_t) v_j (s - s₀, t)`, minus `½ β'(s - s₀)(v⁺ - c)`
read through the disc blocks, the shifted neck block and the neck constant. -/
def neckRowN (J₀ : E →L[ℝ] E) (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) 0 →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0) :=
  (1 / 2 : ℝ) • ((Neck.shH (A.s0 jk.1) 0).comp
      ((dsH 2 (Neck.δ_nonneg δ h0 hmono 0)).comp (neckW δ h0 hmono jk)) +
    ∑ l, Jm J₀ jk.2 l • (Neck.shH (A.s0 jk.1) 0).comp
      ((dtH 2 (Neck.δ_nonneg δ h0 hmono 0)).comp (neckW δ h0 hmono (jk.1, l)))) -
  (1 / 2 : ℝ) • (∑ i, ∑ a, (Neck.shH 0 (G.θ a)).comp
      (((G.Dd jk.1 i a).op 2 (Neck.δ_nonneg δ h0 hmono 0) (G.cD_smooth jk.1 i a)
        (G.cD_supp jk.1 i a) (Neck.δ_nonneg δ h0 hmono 0)).comp
          ((incl32 δ h0 hmono).comp (secProj δ h0 hmono (i, jk.2)))) +
    (Neck.mulHL (mulN (A.s0 jk.1) (G.χ jk.1))
      (mult_mulN (G.χ_smooth jk.1) (G.χ_zero jk.1) 2)).comp
        ((Neck.shH (A.s0 jk.1) 0).comp ((incl32 δ h0 hmono).comp (neckW δ h0 hmono jk))) -
    (neckC δ h0 hmono jk).smulRight
      (toH 2 (Neck.δ_nonneg δ h0 hmono 0) (isTest_cstN (s₀ := A.s0 jk.1) (G.χ_smooth jk.1))))

include hT in
/-- **The linearization `D` at a constant map, with nodes** (`J₀ = J(q)`): the disc rows
`½ (R + P R)` and the neck rows `neckRowN`, a bounded operator from the level-`0` section blocks
to the level-`0` fibre blocks. -/
def linOpN (J₀ : E →L[ℝ] E) : (blocks A δ h0 hmono) 0 →L[ℝ] (fibreBlocks A δ h0 hmono) 0 :=
  ((ContinuousLinearMap.fst ℝ _ _).comp (discPartN hT G δ h0 hmono J₀)).prod
    (ContinuousLinearMap.pi fun jk => neckRowN G δ h0 hmono J₀ jk)

end Operators

/-! ## 4. The disc rows on representatives -/

section DiscRep

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {q : Q}
  {A : SectionAtlas (E := E) X (fun _ => q)} (G : GlueDataN A)
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

lemma coeFn_sumH {k : ℕ} {d : ℝ} {hd : 0 ≤ d} {ι : Type*} (s : Finset ι) (f : ι → H k hd) :
    (H.val (∑ i ∈ s, f i) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => ∑ i ∈ s, H.val (f i) x := by
  have e : H.val (∑ i ∈ s, f i) = ∑ i ∈ s, H.val (f i) := map_sum (valCLM k hd) _ _
  rw [e]; exact Lp.coeFn_fun_finsetSum s _

lemma neckRep_shT (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) (η : Section E X) (θ : ℝ)
    (z : ℝ × ℝ) : neckRep A j k η (Neck.shT 0 θ z) = Real.smoothTransition z.1 *
      (crd k (η (X.polar (A.hol j) (z.1 + A.s0 j, z.2 - θ))) - neckConst A j k η) := by
  obtain ⟨n, hn⟩ := Neck.rot_int θ z.2
  have e : Neck.shT 0 θ z = (z.1, (z.2 - θ) + n) := by
    simp only [Neck.shT, sub_zero, hn]
  rw [e, neckRep_add_int]
  simp only [neckRep, tcc_const]

include hT in
/-- One piece of the zeroth-order term from the disc blocks. -/
lemma termZN_rep_eq (d : Fin 2) {i j : Fin A.nd} (kk : Fin (Module.finrank ℝ E))
    (η : Section E X) (p : ℝ × ℝ) :
    coefZ d (G.ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j) p *
        discRep A j kk η ((G.D i j).ψ p) =
      dCut d p * G.ρ j (X.discPt (A.center i) (A.ε i) p) *
        crd kk (η (X.discPt (A.center i) (A.ε i) p)) := by
  by_cases hp : p ∈ pieceK (G.ρ j) (A.center i) (A.ε i)
  · have hpD := pieceK_sub (G.hρ j) hp
    rw [G.hDψ i j p (G.hDK i j ▸ hp), discRep_const (fun _ => rfl),
      discPt_trans (A.ε_pos j).ne' (pieceDom_sub hpD).1]
    have hne := (discCut_pos (pieceDom_sub hpD).2).ne'
    rw [coefZ]
    field_simp
  · have h0 : coefZ d (G.ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j) p = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hp (tsupport_coefZ_sub hT d _ _ _ _ _ h)
    rw [h0, zero_mul, pieceZ_zero d hp, zero_mul]

variable {η : Section E X} {v : (blocks A δ h0 hmono) 0}

/-- The neck pieces of the zeroth-order term in the disc `i`, on a representative. -/
lemma neckZ_rep (hr : IsRep η v) (d : Fin 2) (i : Fin A.nd) (j : Fin A.nn)
    (k : Fin (Module.finrank ℝ E)) :
    (fun x => ∑ a, G.cN d i j a x * H.val (Neck.shH 0 (G.θ a)
        (incl32 δ h0 hmono (neckW δ h0 hmono (j, k) v))) ((G.Dn i j a).ψ x)) =ᵐ[cyl]
      fun x => dCut d x * G.χS j (X.discPt (A.center i) (A.ε i) x) *
        (crd k (η (X.discPt (A.center i) (A.ε i) x)) - neckConst A j k η) := by
  have h1 : ∀ a, (H.val (Neck.shH 0 (G.θ a) (incl32 δ h0 hmono (neckW δ h0 hmono (j, k) v))) :
      ℝ × ℝ → ℝ) =ᵐ[cyl] fun z => neckRep A j k η (Neck.shT 0 (G.θ a) z) := fun a =>
    (Neck.val_shH 0 (G.θ a) _).trans
      ((Neck.measurePreserving_shT 0 (G.θ a)).quasiMeasurePreserving.ae_eq_comp (hr.2 j k).2)
  have h2 := fun a => (G.Dn i j a).comp_congr (G.cN_supp d i j a) (h1 a)
  filter_upwards [ae_all_iff.2 h2] with x hx
  rw [Finset.sum_congr rfl fun a _ => hx a]
  have e : ∀ a, G.cN d i j a x * neckRep A j k η (Neck.shT 0 (G.θ a) ((G.Dn i j a).ψ x)) =
      G.cN d i j a x * Real.smoothTransition ((G.Dn i j a).ψ x).1 *
        (crd k (η (X.discPt (A.center i) (A.ε i) x)) - neckConst A j k η) := by
    intro a
    by_cases hK : x ∈ (G.Dn i j a).K
    · rw [neckRep_shT, G.Dn_pt i j a x hK]; ring
    · rw [(G.Dn i j a).eq_zero_off (G.cN_supp d i j a) hK]; ring
  rw [Finset.sum_congr rfl fun a _ => e a, ← Finset.sum_mul, G.cN_sum]

include hT in
/-- **The zeroth-order term on a representative**: `(Zv)_{i,d,k} = ∂_d β · η_k` in the disc. -/
lemma coeFn_zBlockN (hr : IsRep η v) (o : Ix A) :
    (H.val (zBlockN hT G δ h0 hmono o v) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x =>
      dCut o.2.1 x * crd o.2.2 (η (X.discPt (A.center o.1) (A.ε o.1) x)) := by
  obtain ⟨i, d, k⟩ := o
  set y : ℝ × ℝ → X.S := X.discPt (A.center i) (A.ε i)
  have e : zBlockN hT G δ h0 hmono (i, d, k) v =
      (∑ i', (G.D i i').op 2 (Neck.δ_nonneg δ h0 hmono 0)
        (contDiff_coefZ hT d (G.ρ i') _ _ _ _ (G.hρ i')) (G.hsZ hT d i i')
          (Neck.δ_nonneg δ h0 hmono 0) (incl32 δ h0 hmono (secProj δ h0 hmono (i', k) v))) +
      (∑ j, ∑ a, (G.Dn i j a).op 2 (Neck.δ_nonneg δ h0 hmono 0) (G.cN_smooth d i j a)
        (G.cN_supp d i j a) (Neck.δ_nonneg δ h0 hmono 0)
          (Neck.shH 0 (G.θ a) (incl32 δ h0 hmono (neckW δ h0 hmono (j, k) v)))) +
      ∑ j, neckC δ h0 hmono (j, k) v • toHdisc (contDiff_cstD hT G d i j)
        (tsupport_cstD G d i j) 2 (Neck.δ_nonneg δ h0 hmono 0) := by
    simp only [zBlockN, add_apply, sum_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  rw [e]
  have h1 : ∀ i', (H.val ((G.D i i').op 2 (Neck.δ_nonneg δ h0 hmono 0)
      (contDiff_coefZ hT d (G.ρ i') _ _ _ _ (G.hρ i')) (G.hsZ hT d i i')
        (Neck.δ_nonneg δ h0 hmono 0) (incl32 δ h0 hmono (secProj δ h0 hmono (i', k) v))) :
          ℝ × ℝ → ℝ) =ᵐ[cyl] fun x =>
        dCut d x * G.ρ i' (y x) * crd k (η (y x)) := by
    intro i'
    refine (ChartChange.coeFn_op _ _ _ _).trans ?_
    refine ((G.D i i').comp_congr (G.hsZ hT d i i') (hr.1 i' k)).trans
      (Eventually.of_forall fun x => ?_)
    exact termZN_rep_eq hT G d k η x
  have h2 : ∀ j, (H.val (∑ a, (G.Dn i j a).op 2 (Neck.δ_nonneg δ h0 hmono 0)
      (G.cN_smooth d i j a) (G.cN_supp d i j a) (Neck.δ_nonneg δ h0 hmono 0)
        (Neck.shH 0 (G.θ a) (incl32 δ h0 hmono (neckW δ h0 hmono (j, k) v)))) :
          ℝ × ℝ → ℝ) =ᵐ[cyl] fun x =>
        dCut d x * G.χS j (y x) * (crd k (η (y x)) - neckConst A j k η) := by
    intro j
    refine (coeFn_sumH _ _).trans ?_
    filter_upwards [ae_all_iff.2 fun a => ChartChange.coeFn_op (G.cN_smooth d i j a)
      (G.cN_supp d i j a) (Neck.δ_nonneg δ h0 hmono 0)
        (Neck.shH 0 (G.θ a) (incl32 δ h0 hmono (neckW δ h0 hmono (j, k) v))),
      neckZ_rep G hr d i j k] with x hx hx'
    rw [Finset.sum_congr rfl fun a _ => hx a]
    exact hx'
  have h3 : ∀ j, (H.val (neckC δ h0 hmono (j, k) v • toHdisc (contDiff_cstD hT G d i j)
      (tsupport_cstD G d i j) 2 (Neck.δ_nonneg δ h0 hmono 0)) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x =>
        neckConst A j k η * (dCut d x * G.χS j (y x)) := by
    intro j
    refine (val_smul_ae _ _).trans ?_
    filter_upwards [val_toHdisc (contDiff_cstD hT G d i j) (tsupport_cstD G d i j) 2
      (Neck.δ_nonneg δ h0 hmono 0)] with x hx
    rw [hx, neckC_apply, (hr.2 j k).1, smul_eq_mul]
    rfl
  filter_upwards [val_add_ae (k := 2) _ _, val_add_ae (k := 2) _ _, coeFn_sumH _ _,
    coeFn_sumH _ _, coeFn_sumH _ _, ae_all_iff.2 h1, ae_all_iff.2 h2, ae_all_iff.2 h3]
    with x e1 e2 e3 e4 e5 f1 f2 f3
  rw [e1, e2, e3, e4, e5, Finset.sum_congr rfl fun i' _ => f1 i',
    Finset.sum_congr rfl fun j _ => f2 j, Finset.sum_congr rfl fun j _ => f3 j]
  have hs := G.sum_one (y x)
  calc ∑ i', dCut d x * G.ρ i' (y x) * crd k (η (y x)) +
        ∑ j, dCut d x * G.χS j (y x) * (crd k (η (y x)) - neckConst A j k η) +
        ∑ j, neckConst A j k η * (dCut d x * G.χS j (y x))
      = dCut d x * crd k (η (y x)) * (∑ i', G.ρ i' (y x) + ∑ j, G.χS j (y x)) := by
        rw [add_assoc, ← Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun _ _ => by ring
        · exact Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [hs, mul_one]

include hT in
/-- **`R v` is the representative of `dη` on the discs.** -/
lemma rBlockN_rep (hc : IsContSection (fun _ => q) η) (hr : IsRep η v) (i : Fin A.nd)
    (d : Fin 2) (k : Fin (Module.finrank ℝ E)) :
    (H.val (rBlockN hT G δ h0 hmono (i, d, k) v) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      formDiscRep A i d k (dForm η) := by
  have hu : ∀ x, (fun _ : X.S => q) x = q := fun _ => rfl
  have hηc := continuous_of_isContSection hu hc
  have D := fun k => (exists_discC1 hT hu hηc hr i k).some
  have e : rBlockN hT G δ h0 hmono (i, d, k) v = (A.ε i)⁻¹ • (dH δ h0 hmono d (v.1 (i, k)) -
      zBlockN hT G δ h0 hmono (i, d, k) v) := rfl
  rw [e]
  filter_upwards [val_smul_ae (A.ε i)⁻¹ (dH δ h0 hmono d (v.1 (i, k)) -
      zBlockN hT G δ h0 hmono (i, d, k) v), val_sub_ae (dH δ h0 hmono d (v.1 (i, k)))
      (zBlockN hT G δ h0 hmono (i, d, k) v), coeFn_zBlockN hT G hr (i, d, k), (D k).ae_gd d,
      ae_disc_or_ext] with x h1 h2 h3 h4 h5
  rw [h1, smul_eq_mul, h2, h3, h4]
  rcases h5 with ⟨hxS, hxD | hxE⟩
  · rw [(formDiscRep_dForm hT hu D hxD).2 d k]; rfl
  · have hcl := not_mem_closedDisc_of_extD hxE
    rw [(D k).gd_eq_zero hT hxS hxE d, dCut_eq_zero d hcl, formDiscRep, discCut_eq_zero hcl]
    ring

include hT in
/-- **The disc rows of `linOpN` are the representatives of `½ (dη + J₀ ∘ dη ∘ j)`.** -/
lemma linOpN_disc_rep (hc : IsContSection (fun _ => q) η) (hr : IsRep η v) (J₀ : E →L[ℝ] E)
    (i : Fin A.nd) (d : Fin 2) (k : Fin (Module.finrank ℝ E)) :
    (H.val ((linOpN hT G δ h0 hmono J₀ v).1 (i, d, k)) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      formDiscRep A i d k (projF J₀ (dForm η)) := by
  have hu : ∀ x, (fun _ : X.S => q) x = q := fun _ => rfl
  have e : (linOpN hT G δ h0 hmono J₀ v).1 (i, d, k) = (1 / 2 : ℝ) •
      (rBlockN hT G δ h0 hmono (i, d, k) v + fDiscBlock (fOp δ h0 hmono (fun _ _ => idCC)
        (aPI A J₀) (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _)
          (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A) 0 (rOpN hT G δ h0 hmono v)) i d k) :=
    rfl
  rw [e, projF, formDiscRep_smul, formDiscRep_add]
  have hP := coeFn_fOp (fun _ _ => idCC) (aPI A J₀) (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _)
    (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A) (rOpN hT G δ h0 hmono v) (i, d, k)
  filter_upwards [val_smul_ae (k := 2) (1 / 2 : ℝ) _, val_add_ae (k := 2) _ _,
    rBlockN_rep hT G hc hr i d k, hP,
    ae_all_iff.2 fun t : Fin 2 × Fin (Module.finrank ℝ E) => rBlockN_rep hT G hc hr i t.1 t.2]
    with x h1 h2 h3 h4 h5
  rw [h1, h2, h3]
  erw [h4]
  rw [Pi.smul_apply, Pi.add_apply, formDiscRep_twist hT hu A]
  congr 2
  exact Finset.sum_congr rfl fun t _ => congrArg (aPI A J₀ (i, d, k) t x * ·) (h5 t)

end DiscRep

end GWMemoir
