import GWMemoir.GlueFilledOps

/-!
# The filled section at the nodal constant map: the commutator term `K_a`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, (4.18) (p. 116).  Commuting
`∂_s + J₀∂_t` past the gluing `⊕_a(h) = β_a h⁺ + (1 - β_a) τh⁻` and the anti-gluing
`⊖_a(h) = -(1 - β_a)(h⁺ - c') + β_a(τh⁻ - c')` produces the terms `β_a'(r⁺ - τr⁻)` and
`β_a'(r⁺ + τr⁻ - 2c')` (`glComP`, `glComM`).  `K_a h = ½ ⊡̂_a⁻¹(β_a'(r⁺ - τr⁻), β_a'(r⁺ + τr⁻ - 2c'))`
(`glKL`) is the pair with these hat gluing and anti-gluing parts:
* `glHat_K`: `⊕̂_a(K_a h) = ½ β_a'(r⁺ - τr⁻)`;
* `glAnti_K`: `⊖̂_a(K_a h) = ½ β_a'(r⁺ + τr⁻ - 2c')`.

`K_a` is multiplication by functions supported in `|s - R/2| ≤ 2`, so it maps `H^{3+n,δ_n}` to
`H^{3+n,δ_{n+1}} ⊂ H^{2+(n+1),δ_{n+1}}`: it raises the level (`glKL` lands in the level-`(n+1)`
fibre blocks), agrees with level `0` along the inclusions (`toBase_glKL`) and is carried by the
far part of the necks (`isFar_glKL`).  It vanishes on the constants (`glKL_const`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology NNReal
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

open Neck (βa F3 F4 multβ IsCutoff shH reflH mulHL trH Van van_shH van_reflH kq)

/-! ## 1. Vanishing of multiplications and of test functions -/

section VanMore

variable {m : ℕ} {d d' : ℝ} {hd : 0 ≤ d} {hd' : 0 ≤ d'}

lemma van_mulHW {I : Set ℝ} {χ : ℝ → ℝ} (h : Mult m χ) (hc : HasCompactSupport χ)
    (hχ : ∀ s ∈ I, χ s = 0) (u : H m hd) :
    Van I (valCLM m hd' (mulHW (hδ := hd) (hδ' := hd') χ h hc u)) := by
  rw [val_mulHW]
  exact Neck.van_of_ae (coeFn_mulχ χ h _) fun x hx => by rw [hχ _ hx, zero_mul]

lemma van_toH_s {I : Set ℝ} {χ : ℝ → ℝ} (hφ : IsTest fun x : ℝ × ℝ => χ x.1)
    (hχ : ∀ s ∈ I, χ s = 0) : Van I (valCLM m hd (toH m hd hφ)) :=
  Neck.van_of_ae (val_toH (m := m) (hδ := hd) hφ) fun _ hx => hχ _ hx

end VanMore

/-! ## 2. The commutator term on the blocks -/

section Kernel

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
  {β : ℝ → ℝ} (hβ : IsCutoff β) (R ϑ : ℝ) (jx jy : Fin A.nn) (n : ℕ)

/-- `r⁺ = w_{jx,k}` (block coordinate `=` the memoir's `s`). -/
def glWP (k : Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) n →L[ℝ] H (3 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  neckWL δ h0 hmono n (jx, k)

/-- `τr⁻ = w_{jy,k}(R - s, ϑ - t)`. -/
def glWN (k : Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) n →L[ℝ] H (3 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (reflH R ϑ).comp (neckWL δ h0 hmono n (jy, k))

/-- `c' = ½([r⁺]_{R/2} + [τr⁻]_{R/2})`. -/
def glC (k : Fin (Module.finrank ℝ E)) : (blocks A δ h0 hmono) n →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ((trH (Neck.hm3 n) (R / 2)).comp (glWP δ h0 hmono jx n k) +
    (trH (Neck.hm3 n) (R / 2)).comp (glWN δ h0 hmono R ϑ jy n k))

/-- Multiplication by `F(β_a) β_a'`, `H^{3+n,δ_n} → H^{3+n,δ_{n+1}}`. -/
abbrev glMulW (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) :
    H (3 + n) (Neck.δ_nonneg δ h0 hmono n) →L[ℝ] H (3 + n) (Neck.δ_nonneg δ h0 hmono (n + 1)) :=
  mulHW (kq β R F) (Neck.mult_kq hβ hF (3 + n)) (Neck.hasCompactSupport_kq hβ)

/-- `F(β_a) β_a'` as an element of `H^{3+n,δ_{n+1}}`. -/
abbrev glTestW (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) : H (3 + n) (Neck.δ_nonneg δ h0 hmono (n + 1)) :=
  toH (3 + n) (Neck.δ_nonneg δ h0 hmono (n + 1)) (Neck.isTest_kq (R := R) hβ hF)

/-- The `+` component `½ ξ⁺` of `K_a h`, `ξ⁺ = F₃P - F₄M`. -/
def glKP (k : Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) n →L[ℝ] H (3 + n) (Neck.δ_nonneg δ h0 hmono (n + 1)) :=
  (glMulW δ h0 hmono hβ R n Neck.kG1 Neck.contDiff_kG1).comp (glWP δ h0 hmono jx n k) +
    (glMulW δ h0 hmono hβ R n Neck.kG2 Neck.contDiff_kG2).comp (glWN δ h0 hmono R ϑ jy n k) +
    (glC δ h0 hmono R ϑ jx jy n k).smulRight (glTestW δ h0 hmono hβ R n F4 Neck.contDiff_F4)

/-- The `τ(·)⁻` component `½ τξ⁻` of `K_a h`, `τξ⁻ = F₄P + F₃M`. -/
def glKN (k : Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) n →L[ℝ] H (3 + n) (Neck.δ_nonneg δ h0 hmono (n + 1)) :=
  (glMulW δ h0 hmono hβ R n Neck.kG4 Neck.contDiff_kG4).comp (glWP δ h0 hmono jx n k) +
    (glMulW δ h0 hmono hβ R n Neck.kG1 Neck.contDiff_kG1).comp (glWN δ h0 hmono R ϑ jy n k) +
    (glC δ h0 hmono R ϑ jx jy n k).smulRight (glTestW δ h0 hmono hβ R n Neck.kG6 Neck.contDiff_kG6)

/-- `H^{3+n,δ_{n+1}} = H^{2+(n+1),δ_{n+1}}`. -/
abbrev glCast :
    H (3 + n) (Neck.δ_nonneg δ h0 hmono (n + 1)) →L[ℝ]
      H (2 + (n + 1)) (Neck.δ_nonneg δ h0 hmono (n + 1)) :=
  inclH _ _ (by omega) le_rfl

/-- The neck block `(j, k)` of `K_a`. -/
def glKBlk (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) n →L[ℝ] H (2 + (n + 1)) (Neck.δ_nonneg δ h0 hmono (n + 1)) :=
  if jk.1 = jx then
    (shH (A.s0 jx) 0).comp ((glCast δ h0 hmono n).comp (glKP δ h0 hmono hβ R ϑ jx jy n jk.2))
  else if jk.1 = jy then
    -((reflH (R + A.s0 jy) ϑ).comp
      ((glCast δ h0 hmono n).comp (glKN δ h0 hmono hβ R ϑ jx jy n jk.2)))
  else 0

/-- **The commutator term `K_a`** from the level-`n` section blocks to the level-`(n+1)` fibre
blocks: `0` on the disc blocks and the other necks, `½(ξ⁺, ξ⁻)` on the node pair. -/
def glKL : (blocks A δ h0 hmono) n →L[ℝ] (fibreBlocks A δ h0 hmono) (n + 1) :=
  (0 : (blocks A δ h0 hmono) n →L[ℝ] _).prod
    (ContinuousLinearMap.pi fun jk => glKBlk δ h0 hmono hβ R ϑ jx jy n jk)

/-- `β_a'(r⁺ - τr⁻)` on level `n`. -/
def glComP (k : Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (mulHL (kq β R fun _ => 1) (Neck.mult_kq (F := fun _ => (1 : ℝ)) hβ contDiff_const (2 + n))).comp
    ((incl32L δ h0 hmono n).comp (glWP δ h0 hmono jx n k - glWN δ h0 hmono R ϑ jy n k))

/-- `β_a'(r⁺ + τr⁻ - 2c')` on level `n`. -/
def glComM (k : Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (mulHL (kq β R fun _ => 1) (Neck.mult_kq (F := fun _ => (1 : ℝ)) hβ contDiff_const (2 + n))).comp
    ((incl32L δ h0 hmono n).comp (glWP δ h0 hmono jx n k + glWN δ h0 hmono R ϑ jy n k)) -
  (2 : ℝ) • (glC δ h0 hmono R ϑ jx jy n k).smulRight
    (toH (2 + n) (Neck.δ_nonneg δ h0 hmono n) (Neck.isTest_kq (R := R) (F := fun _ => (1 : ℝ)) hβ contDiff_const))

variable {δ h0 hmono hβ R ϑ jx jy n}

lemma glKL_fst (v : (blocks A δ h0 hmono) n) : (glKL δ h0 hmono hβ R ϑ jx jy n v).1 = 0 := rfl

lemma glKL_x (v : (blocks A δ h0 hmono) n) (k : Fin (Module.finrank ℝ E)) :
    (glKL δ h0 hmono hβ R ϑ jx jy n v).2 (jx, k) =
      shH (A.s0 jx) 0 (glCast δ h0 hmono n (glKP δ h0 hmono hβ R ϑ jx jy n k v)) := by
  change glKBlk δ h0 hmono hβ R ϑ jx jy n (jx, k) v = _
  rw [glKBlk, if_pos rfl]; rfl

lemma glKL_y (hxy : jx ≠ jy) (v : (blocks A δ h0 hmono) n) (k : Fin (Module.finrank ℝ E)) :
    (glKL δ h0 hmono hβ R ϑ jx jy n v).2 (jy, k) =
      -reflH (R + A.s0 jy) ϑ (glCast δ h0 hmono n (glKN δ h0 hmono hβ R ϑ jx jy n k v)) := by
  change glKBlk δ h0 hmono hβ R ϑ jx jy n (jy, k) v = _
  rw [glKBlk, if_neg (Ne.symm hxy), if_pos rfl]; rfl

lemma glKL_other {j : Fin A.nn} (hx : j ≠ jx) (hy : j ≠ jy) (v : (blocks A δ h0 hmono) n)
    (k : Fin (Module.finrank ℝ E)) : (glKL δ h0 hmono hβ R ϑ jx jy n v).2 (j, k) = 0 := by
  change glKBlk δ h0 hmono hβ R ϑ jx jy n (j, k) v = _
  rw [glKBlk, if_neg hx, if_neg hy]; rfl

/-! ### Along the inclusions -/

lemma valEqB_glWP (k : Fin (Module.finrank ℝ E)) :
    ValEqB n (glWP δ h0 hmono jx n k) (glWP δ h0 hmono jx 0 k) :=
  fun v => (val_neck_toBase δ h0 hmono n v (jx, k)).symm

lemma valEqB_glWN (k : Fin (Module.finrank ℝ E)) :
    ValEqB n (glWN δ h0 hmono R ϑ jy n k) (glWN δ h0 hmono R ϑ jy 0 k) :=
  (valEq_reflH _ _).compB fun v => (val_neck_toBase δ h0 hmono n v (jy, k)).symm

lemma glC_toBase (k : Fin (Module.finrank ℝ E)) (v : (blocks A δ h0 hmono) n) :
    glC δ h0 hmono R ϑ jx jy n k v =
      glC δ h0 hmono R ϑ jx jy 0 k ((blocks A δ h0 hmono).toBase n v) := by
  change (1 / 2 : ℝ) • (trH (Neck.hm3 n) (R / 2) (glWP δ h0 hmono jx n k v) +
      trH (Neck.hm3 n) (R / 2) (glWN δ h0 hmono R ϑ jy n k v)) =
    (1 / 2 : ℝ) • (trH (Neck.hm3 0) (R / 2) (glWP δ h0 hmono jx 0 k _) +
      trH (Neck.hm3 0) (R / 2) (glWN δ h0 hmono R ϑ jy 0 k _))
  rw [Neck.trH_eq_of_val (Neck.hm3 n) (Neck.hm3 0) (R / 2) (valEqB_glWP k v),
    Neck.trH_eq_of_val (Neck.hm3 n) (Neck.hm3 0) (R / 2) (valEqB_glWN k v)]

lemma valEqB_glKP (k : Fin (Module.finrank ℝ E)) :
    ValEqB n (glKP δ h0 hmono hβ R ϑ jx jy n k) (glKP δ h0 hmono hβ R ϑ jx jy 0 k) :=
  (((valEq_mulHW _ _ _).compB (valEqB_glWP k)).add ((valEq_mulHW _ _ _).compB (valEqB_glWN k))).add
    (valEqB_smulRight (glC_toBase k) (val_toH_eq _))

lemma valEqB_glKN (k : Fin (Module.finrank ℝ E)) :
    ValEqB n (glKN δ h0 hmono hβ R ϑ jx jy n k) (glKN δ h0 hmono hβ R ϑ jx jy 0 k) :=
  (((valEq_mulHW _ _ _).compB (valEqB_glWP k)).add ((valEq_mulHW _ _ _).compB (valEqB_glWN k))).add
    (valEqB_smulRight (glC_toBase k) (val_toH_eq _))

/-- `K_a` on level `n` agrees with `K_a` on level `0` along the inclusions. -/
theorem toBase_glKL (hxy : jx ≠ jy) (v : (blocks A δ h0 hmono) n) :
    (fibreBlocks A δ h0 hmono).toBase (n + 1) (glKL δ h0 hmono hβ R ϑ jx jy n v) =
      (fibreBlocks A δ h0 hmono).toBase 1
        (glKL δ h0 hmono hβ R ϑ jx jy 0 ((blocks A δ h0 hmono).toBase n v)) := by
  refine fibre_ext_val δ h0 hmono (fun o => ?_) (fun ⟨j, k⟩ => ?_)
  · rw [fibre_toBase_fst, fibre_toBase_fst]
    exact (map_zero (valCLM (2 + (n + 1)) (Neck.δ_nonneg δ h0 hmono (n + 1)))).trans
      (map_zero (valCLM (2 + 1) (Neck.δ_nonneg δ h0 hmono 1))).symm
  rw [val_fibreNeck_toBase, val_fibreNeck_toBase]
  by_cases hx : j = jx
  · subst hx
    rw [glKL_x, glKL_x]
    exact valEq_shH _ _ _ _ (valEqB_glKP k v)
  by_cases hy : j = jy
  · subst hy
    rw [glKL_y hxy, glKL_y hxy]
    change valCLM _ _ (-_) = valCLM _ _ (-_)
    rw [map_neg, map_neg]
    exact congrArg Neg.neg (valEq_reflH (R + A.s0 j) ϑ
      (glCast δ h0 hmono n (glKN δ h0 hmono hβ R ϑ jx j n k v))
      (glCast δ h0 hmono 0 (glKN δ h0 hmono hβ R ϑ jx j 0 k ((blocks A δ h0 hmono).toBase n v)))
      (valEqB_glKN k v))
  · rw [glKL_other hx hy, glKL_other hx hy]
    exact (map_zero (valCLM (2 + (n + 1)) (Neck.δ_nonneg δ h0 hmono (n + 1)))).trans
      (map_zero (valCLM (2 + 1) (Neck.δ_nonneg δ h0 hmono 1))).symm

/-! ### Pointwise formulas -/

lemma glKP_apply (k : Fin (Module.finrank ℝ E)) (v : (blocks A δ h0 hmono) n) :
    glKP δ h0 hmono hβ R ϑ jx jy n k v =
      glMulW δ h0 hmono hβ R n Neck.kG1 Neck.contDiff_kG1 (glWP δ h0 hmono jx n k v) +
        glMulW δ h0 hmono hβ R n Neck.kG2 Neck.contDiff_kG2 (glWN δ h0 hmono R ϑ jy n k v) +
        glC δ h0 hmono R ϑ jx jy n k v • glTestW δ h0 hmono hβ R n F4 Neck.contDiff_F4 := rfl

lemma glKN_apply (k : Fin (Module.finrank ℝ E)) (v : (blocks A δ h0 hmono) n) :
    glKN δ h0 hmono hβ R ϑ jx jy n k v =
      glMulW δ h0 hmono hβ R n Neck.kG4 Neck.contDiff_kG4 (glWP δ h0 hmono jx n k v) +
        glMulW δ h0 hmono hβ R n Neck.kG1 Neck.contDiff_kG1 (glWN δ h0 hmono R ϑ jy n k v) +
        glC δ h0 hmono R ϑ jx jy n k v • glTestW δ h0 hmono hβ R n Neck.kG6 Neck.contDiff_kG6 := rfl

lemma val_glMulW_add (F F' G' : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hF' : ContDiff ℝ ∞ F')
    (hG' : ContDiff ℝ ∞ G') (u u' : H (3 + n) (Neck.δ_nonneg δ h0 hmono n)) (c : ℝ) :
    (valCLM _ _ (glMulW δ h0 hmono hβ R n F hF u + glMulW δ h0 hmono hβ R n F' hF' u' +
        c • glTestW δ h0 hmono hβ R n G' hG') : ℝ × ℝ → ℝ) =ᵐ[cyl]
      fun x => kq β R F x.1 * valCLM _ _ u x + kq β R F' x.1 * valCLM _ _ u' x +
        c * kq β R G' x.1 := by
  rw [map_add, map_add, map_smul, val_mulHW, val_mulHW]
  filter_upwards [Lp.coeFn_add (mulχ (kq β R F) (Neck.mult_kq hβ hF (3 + n)) (valCLM _ _ u) +
      mulχ (kq β R F') (Neck.mult_kq hβ hF' (3 + n)) (valCLM _ _ u'))
      (c • valCLM _ _ (glTestW δ h0 hmono hβ R n G' hG')),
    Lp.coeFn_add (mulχ (kq β R F) (Neck.mult_kq hβ hF (3 + n)) (valCLM _ _ u))
      (mulχ (kq β R F') (Neck.mult_kq hβ hF' (3 + n)) (valCLM _ _ u')),
    Lp.coeFn_smul c (valCLM _ _ (glTestW δ h0 hmono hβ R n G' hG')),
    coeFn_mulχ (kq β R F) (Neck.mult_kq hβ hF (3 + n)) (valCLM _ _ u),
    coeFn_mulχ (kq β R F') (Neck.mult_kq hβ hF' (3 + n)) (valCLM _ _ u'),
    val_toH (m := 3 + n) (hδ := Neck.δ_nonneg δ h0 hmono (n + 1))
      (Neck.isTest_kq (R := R) hβ hG')] with x h1 h2 h3 h4 h5 h6
  have h6' : (valCLM _ _ (glTestW δ h0 hmono hβ R n G' hG') : ℝ × ℝ → ℝ) x = kq β R G' x.1 := h6
  rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, Pi.smul_apply, h4, h5, h6', smul_eq_mul]

lemma val_glComP (k : Fin (Module.finrank ℝ E)) (v : (blocks A δ h0 hmono) n) :
    (valCLM _ _ (glComP δ h0 hmono hβ R ϑ jx jy n k v) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      fun x => kq β R (fun _ => 1) x.1 * (valCLM _ _ (glWP δ h0 hmono jx n k v) x -
        valCLM _ _ (glWN δ h0 hmono R ϑ jy n k v) x) := by
  filter_upwards [Neck.val_mulHL (kq β R fun _ => 1)
      (Neck.mult_kq (F := fun _ => (1 : ℝ)) hβ contDiff_const (2 + n))
      (incl32L δ h0 hmono n (glWP δ h0 hmono jx n k v - glWN δ h0 hmono R ϑ jy n k v)),
    Lp.coeFn_sub (valCLM _ _ (glWP δ h0 hmono jx n k v))
      (valCLM _ _ (glWN δ h0 hmono R ϑ jy n k v))] with x h1 h2
  rw [show glComP δ h0 hmono hβ R ϑ jx jy n k v = mulHL _
      (Neck.mult_kq (F := fun _ => (1 : ℝ)) hβ contDiff_const (2 + n))
      (incl32L δ h0 hmono n (glWP δ h0 hmono jx n k v - glWN δ h0 hmono R ϑ jy n k v)) from rfl,
    h1]
  change _ * (valCLM (3 + n) _ (glWP δ h0 hmono jx n k v - glWN δ h0 hmono R ϑ jy n k v) :
    ℝ × ℝ → ℝ) x = _
  rw [map_sub, h2]; rfl

lemma val_glComM (k : Fin (Module.finrank ℝ E)) (v : (blocks A δ h0 hmono) n) :
    (valCLM _ _ (glComM δ h0 hmono hβ R ϑ jx jy n k v) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      fun x => kq β R (fun _ => 1) x.1 * (valCLM _ _ (glWP δ h0 hmono jx n k v) x +
        valCLM _ _ (glWN δ h0 hmono R ϑ jy n k v) x) -
        2 * (glC δ h0 hmono R ϑ jx jy n k v * kq β R (fun _ => 1) x.1) := by
  set T := toH (2 + n) (Neck.δ_nonneg δ h0 hmono n)
    (Neck.isTest_kq (R := R) (F := fun _ => (1 : ℝ)) hβ contDiff_const)
  set W := mulHL (kq β R fun _ => 1)
      (Neck.mult_kq (F := fun _ => (1 : ℝ)) hβ contDiff_const (2 + n)) (hδ := Neck.δ_nonneg δ h0 hmono n)
      (incl32L δ h0 hmono n (glWP δ h0 hmono jx n k v + glWN δ h0 hmono R ϑ jy n k v))
  have e : glComM δ h0 hmono hβ R ϑ jx jy n k v =
      W - (2 : ℝ) • (glC δ h0 hmono R ϑ jx jy n k v • T) := rfl
  rw [e, map_sub, map_smul, map_smul]
  filter_upwards [Lp.coeFn_sub (valCLM _ _ W) ((2 : ℝ) • glC δ h0 hmono R ϑ jx jy n k v • valCLM _ _ T),
    Lp.coeFn_smul (2 : ℝ) (glC δ h0 hmono R ϑ jx jy n k v • valCLM _ _ T),
    Lp.coeFn_smul (glC δ h0 hmono R ϑ jx jy n k v) (valCLM _ _ T),
    Neck.val_mulHL (kq β R fun _ => 1)
      (Neck.mult_kq (F := fun _ => (1 : ℝ)) hβ contDiff_const (2 + n))
      (incl32L δ h0 hmono n (glWP δ h0 hmono jx n k v + glWN δ h0 hmono R ϑ jy n k v)),
    Lp.coeFn_add (valCLM _ _ (glWP δ h0 hmono jx n k v))
      (valCLM _ _ (glWN δ h0 hmono R ϑ jy n k v)),
    val_toH (m := 2 + n) (hδ := Neck.δ_nonneg δ h0 hmono n)
      (Neck.isTest_kq (R := R) (F := fun _ => (1 : ℝ)) hβ contDiff_const)] with x h1 h2 h3 h4 h5 h6
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, Pi.smul_apply, h4, smul_eq_mul, smul_eq_mul]
  change _ * (valCLM (3 + n) _ (glWP δ h0 hmono jx n k v + glWN δ h0 hmono R ϑ jy n k v) :
    ℝ × ℝ → ℝ) x - _ = _
  have h6' : (valCLM _ _ T : ℝ × ℝ → ℝ) x = kq β R (fun _ => 1) x.1 := h6
  rw [map_add, h5, h6']; rfl

/-! ### Far, constants -/

lemma van_glKP (v : (blocks A δ h0 hmono) n) (k : Fin (Module.finrank ℝ E)) :
    Van (Iio (R / 2 - 2)) (valCLM _ _ (glKP δ h0 hmono hβ R ϑ jx jy n k v)) := by
  have hz : ∀ F : ℝ → ℝ, ∀ s ∈ Iio (R / 2 - 2), kq β R F s = 0 := fun F s hs =>
    Neck.kq_eq_zero hβ fun h => by simp only [mem_Iio] at hs; linarith [h.1]
  rw [glKP_apply, map_add, map_add, map_smul]
  exact Neck.van_add (Neck.van_add (van_mulHW _ _ (hz _) _) (van_mulHW _ _ (hz _) _))
    (Neck.van_smul _ (van_toH_s _ (hz _)))

lemma van_glKN (v : (blocks A δ h0 hmono) n) (k : Fin (Module.finrank ℝ E)) :
    Van (Ioi (R / 2 + 2)) (valCLM _ _ (glKN δ h0 hmono hβ R ϑ jx jy n k v)) := by
  have hz : ∀ F : ℝ → ℝ, ∀ s ∈ Ioi (R / 2 + 2), kq β R F s = 0 := fun F s hs =>
    Neck.kq_eq_zero hβ fun h => by simp only [mem_Ioi] at hs; linarith [h.2]
  rw [glKN_apply, map_add, map_add, map_smul]
  exact Neck.van_add (Neck.van_add (van_mulHW _ _ (hz _) _) (van_mulHW _ _ (hz _) _))
    (Neck.van_smul _ (van_toH_s _ (hz _)))

/-- **`K_a` is carried by the far part of the necks** (`|s - R/2| ≤ 2` in the memoir's
coordinate). -/
theorem isFar_glKL (hxy : jx ≠ jy) {σ : ℝ} (hσ : ∀ j, σ + 2 < R / 2 + A.s0 j)
    (v : (blocks A δ h0 hmono) 0) :
    IsFar σ ((fibreBlocks A δ h0 hmono).toBase 1 (glKL δ h0 hmono hβ R ϑ jx jy 0 v)) := by
  refine ⟨funext fun o => valCLM_injective ?_, fun ⟨j, k⟩ => ?_⟩
  · exact (fibre_toBase_fst (δ := δ) (h0 := h0) (hmono := hmono) (n := 1) _ o).trans
      ((map_zero (valCLM (2 + 1) (Neck.δ_nonneg δ h0 hmono 1))).trans
        (map_zero (valCLM (2 + 0) (Neck.δ_nonneg δ h0 hmono 0))).symm)
  change Van _ (H.val (((fibreBlocks A δ h0 hmono).toBase 1 _).2 (j, k)))
  rw [val_fibreNeck_toBase]
  by_cases hx : j = jx
  · subst hx
    rw [glKL_x]
    have h1 : Van (Iio (R / 2 - 2)) (valCLM _ _ (glCast δ h0 hmono 0
        (glKP δ h0 hmono hβ R ϑ j jy 0 k v))) := van_glKP v k
    exact van_shH h1 _ 0 fun s hs => by
      simp only [mem_Iic] at hs; simp only [mem_Iio]; linarith [hσ j]
  by_cases hy : j = jy
  · subst hy
    rw [glKL_y hxy]
    have h1 : Van (Ioi (R / 2 + 2)) (valCLM _ _ (glCast δ h0 hmono 0
        (glKN δ h0 hmono hβ R ϑ jx j 0 k v))) := van_glKN v k
    change Van _ (valCLM _ _ (-_))
    rw [map_neg]
    exact Neck.van_neg (van_reflH h1 _ _ fun s hs => by
      simp only [mem_Iic] at hs; simp only [mem_Ioi]; linarith [hσ j])
  · rw [glKL_other hx hy]
    change Van _ (valCLM (2 + (0 + 1)) (Neck.δ_nonneg δ h0 hmono (0 + 1)) 0)
    rw [map_zero]
    exact Neck.van_zero _

/-- **`K_a` vanishes on the constants**: their neck remainders are `0`. -/
theorem glKL_const (e : E) :
    glKL δ h0 hmono hβ R ϑ jx jy 0 (constBlocksN A δ h0 hmono e) = 0 := by
  have hP : ∀ k, glWP δ h0 hmono jx 0 k (constBlocksN A δ h0 hmono e) = 0 := fun k => rfl
  have hN : ∀ k, glWN δ h0 hmono R ϑ jy 0 k (constBlocksN A δ h0 hmono e) = 0 := fun k =>
    map_zero (reflH (m := 3 + 0) (hδ := Neck.δ_nonneg δ h0 hmono 0) R ϑ)
  have hC : ∀ k, glC δ h0 hmono R ϑ jx jy 0 k (constBlocksN A δ h0 hmono e) = 0 := fun k => by
    change (1 / 2 : ℝ) • (trH (Neck.hm3 0) (R / 2) (glWP δ h0 hmono jx 0 k _) +
      trH (Neck.hm3 0) (R / 2) (glWN δ h0 hmono R ϑ jy 0 k _)) = 0
    rw [hP, hN, map_zero, add_zero, smul_zero]
  have hKP : ∀ k, glKP δ h0 hmono hβ R ϑ jx jy 0 k (constBlocksN A δ h0 hmono e) = 0 := fun k => by
    rw [glKP_apply, hP, hN, hC, map_zero, map_zero, zero_smul]; simp only [add_zero]
  have hKN : ∀ k, glKN δ h0 hmono hβ R ϑ jx jy 0 k (constBlocksN A δ h0 hmono e) = 0 := fun k => by
    rw [glKN_apply, hP, hN, hC, map_zero, map_zero, zero_smul]; simp only [add_zero]
  refine Prod.ext rfl (funext fun ⟨j, k⟩ => ?_)
  by_cases hx : j = jx
  · subst hx
    rw [glKL_x, hKP, map_zero, map_zero]; rfl
  by_cases hy : j = jy
  · subst hy
    by_cases hxy : jx = j
    · subst hxy
      rw [glKL_x, hKP, map_zero, map_zero]; rfl
    rw [glKL_y hxy, hKN, map_zero, map_zero, neg_zero]; rfl
  · rw [glKL_other hx hy]; rfl

/-! ### The hat gluing and anti-gluing parts of `K_a` -/

lemma val_glP_K (v : (blocks A δ h0 hmono) 0) (k : Fin (Module.finrank ℝ E)) :
    valCLM _ _ (glP δ h0 hmono jx 0 k
        ((fibreBlocks A δ h0 hmono).incl 0 (glKL δ h0 hmono hβ R ϑ jx jy 0 v))) =
      valCLM (3 + 0) (Neck.δ_nonneg δ h0 hmono 1) (glKP δ h0 hmono hβ R ϑ jx jy 0 k v) := by
  set X := glKL δ h0 hmono hβ R ϑ jx jy 0 v
  have e1 : valCLM (2 + 0) (Neck.δ_nonneg δ h0 hmono 0)
      (((fibreBlocks A δ h0 hmono).incl 0 X).2 (jx, k)) =
        valCLM (2 + 1) (Neck.δ_nonneg δ h0 hmono 1) (X.2 (jx, k)) :=
    val_fibreNeck_toBase δ h0 hmono 1 X (jx, k)
  change Neck.shLp (-A.s0 jx) 0 (valCLM _ _ (((fibreBlocks A δ h0 hmono).incl 0 X).2 (jx, k))) = _
  rw [e1, glKL_x]
  have := Neck.shLp_shLp (A.s0 jx) 0 (valCLM (3 + 0) (Neck.δ_nonneg δ h0 hmono 1)
    (glKP δ h0 hmono hβ R ϑ jx jy 0 k v))
  rw [neg_zero] at this
  exact this

lemma val_glN_apply (Y : (fibreBlocks A δ h0 hmono) 0) (k : Fin (Module.finrank ℝ E)) :
    valCLM _ _ (glN δ h0 hmono R ϑ jy 0 k Y) =
      -(Neck.rfLp (R + A.s0 jy) ϑ (valCLM (2 + 0) (Neck.δ_nonneg δ h0 hmono 0) (Y.2 (jy, k)))) := by
  change valCLM _ _ (-(reflH (R + A.s0 jy) ϑ (glFibNeck δ h0 hmono 0 (jy, k) Y))) = _
  rw [map_neg]; rfl

lemma val_glN_K (hxy : jx ≠ jy) (v : (blocks A δ h0 hmono) 0) (k : Fin (Module.finrank ℝ E)) :
    valCLM _ _ (glN δ h0 hmono R ϑ jy 0 k
        ((fibreBlocks A δ h0 hmono).incl 0 (glKL δ h0 hmono hβ R ϑ jx jy 0 v))) =
      valCLM (3 + 0) (Neck.δ_nonneg δ h0 hmono 1) (glKN δ h0 hmono hβ R ϑ jx jy 0 k v) := by
  set X := glKL δ h0 hmono hβ R ϑ jx jy 0 v
  have e1 : valCLM (2 + 0) (Neck.δ_nonneg δ h0 hmono 0)
      (((fibreBlocks A δ h0 hmono).incl 0 X).2 (jy, k)) =
        valCLM (2 + 1) (Neck.δ_nonneg δ h0 hmono 1) (X.2 (jy, k)) :=
    val_fibreNeck_toBase δ h0 hmono 1 X (jy, k)
  rw [val_glN_apply, e1, glKL_y hxy, map_neg, Neck.valCLM_reflH, map_neg, Neck.rfLp_rfLp, neg_neg]
  rfl

/-- **`⊕̂_a(K_a h) = ½ β_a'(r⁺ - τr⁻)`.** -/
theorem glHat_K (hxy : jx ≠ jy) (v : (blocks A δ h0 hmono) 0) (k : Fin (Module.finrank ℝ E)) :
    glHat δ h0 hmono hβ R ϑ jx jy 0 k
        ((fibreBlocks A δ h0 hmono).incl 0 (glKL δ h0 hmono hβ R ϑ jx jy 0 v)) =
      (1 / 2 : ℝ) • glComP δ h0 hmono hβ R ϑ jx jy 0 k v := by
  set Y := (fibreBlocks A δ h0 hmono).incl 0 (glKL δ h0 hmono hβ R ϑ jx jy 0 v)
  apply valCLM_injective
  apply Lp.ext
  rw [map_smul]
  filter_upwards [Neck.val_mulHL_add (Neck.m1 hβ R (2 + 0)) (Neck.m2 hβ R (2 + 0))
      (glP δ h0 hmono jx 0 k Y) (glN δ h0 hmono R ϑ jy 0 k Y),
    val_glMulW_add (hβ := hβ) (R := R) _ _ _ Neck.contDiff_kG1 Neck.contDiff_kG2 Neck.contDiff_F4
      (glWP δ h0 hmono jx 0 k v) (glWN δ h0 hmono R ϑ jy 0 k v) (glC δ h0 hmono R ϑ jx jy 0 k v),
    val_glMulW_add (hβ := hβ) (R := R) _ _ _ Neck.contDiff_kG4 Neck.contDiff_kG1 Neck.contDiff_kG6
      (glWP δ h0 hmono jx 0 k v) (glWN δ h0 hmono R ϑ jy 0 k v) (glC δ h0 hmono R ϑ jx jy 0 k v),
    Lp.coeFn_smul (1 / 2 : ℝ) (valCLM _ _ (glComP δ h0 hmono hβ R ϑ jx jy 0 k v)),
    val_glComP (hβ := hβ) (ϑ := ϑ) (jy := jy) k v] with x h1 h2 h3 h4 h5
  change (valCLM _ _ (mulHL _ (Neck.m1 hβ R (2 + 0)) (glP δ h0 hmono jx 0 k Y) +
    mulHL _ (Neck.m2 hβ R (2 + 0)) (glN δ h0 hmono R ϑ jy 0 k Y)) : ℝ × ℝ → ℝ) x = _
  rw [h1, val_glP_K, val_glN_K hxy, glKP_apply, glKN_apply, h2, h3, h4, Pi.smul_apply, h5,
    smul_eq_mul]
  have e := (Neck.kG_glue (βa β R x.1)).1
  simp only [kq]
  linear_combination
    (Neck.dβa β R x.1 * valCLM _ _ (glWP δ h0 hmono jx 0 k v) x) * e.1 +
    (Neck.dβa β R x.1 * valCLM _ _ (glWN δ h0 hmono R ϑ jy 0 k v) x) * e.2.1 +
    (glC δ h0 hmono R ϑ jx jy 0 k v * Neck.dβa β R x.1) * e.2.2

/-- **`⊖̂_a(K_a h) = ½ β_a'(r⁺ + τr⁻ - 2c')`.** -/
theorem glAnti_K (hxy : jx ≠ jy) (v : (blocks A δ h0 hmono) 0) (k : Fin (Module.finrank ℝ E)) :
    glAnti δ h0 hmono hβ R ϑ jx jy 0 k
        ((fibreBlocks A δ h0 hmono).incl 0 (glKL δ h0 hmono hβ R ϑ jx jy 0 v)) =
      (1 / 2 : ℝ) • glComM δ h0 hmono hβ R ϑ jx jy 0 k v := by
  set Y := (fibreBlocks A δ h0 hmono).incl 0 (glKL δ h0 hmono hβ R ϑ jx jy 0 v)
  apply valCLM_injective
  apply Lp.ext
  rw [map_smul]
  filter_upwards [Neck.val_mulHL_add (Neck.m5 hβ R (2 + 0)) (Neck.m1 hβ R (2 + 0))
      (glP δ h0 hmono jx 0 k Y) (glN δ h0 hmono R ϑ jy 0 k Y),
    val_glMulW_add (hβ := hβ) (R := R) _ _ _ Neck.contDiff_kG1 Neck.contDiff_kG2 Neck.contDiff_F4
      (glWP δ h0 hmono jx 0 k v) (glWN δ h0 hmono R ϑ jy 0 k v) (glC δ h0 hmono R ϑ jx jy 0 k v),
    val_glMulW_add (hβ := hβ) (R := R) _ _ _ Neck.contDiff_kG4 Neck.contDiff_kG1 Neck.contDiff_kG6
      (glWP δ h0 hmono jx 0 k v) (glWN δ h0 hmono R ϑ jy 0 k v) (glC δ h0 hmono R ϑ jx jy 0 k v),
    Lp.coeFn_smul (1 / 2 : ℝ) (valCLM _ _ (glComM δ h0 hmono hβ R ϑ jx jy 0 k v)),
    val_glComM (hβ := hβ) (ϑ := ϑ) (jy := jy) k v] with x h1 h2 h3 h4 h5
  change (valCLM _ _ (mulHL _ (Neck.m5 hβ R (2 + 0)) (glP δ h0 hmono jx 0 k Y) +
    mulHL _ (Neck.m1 hβ R (2 + 0)) (glN δ h0 hmono R ϑ jy 0 k Y)) : ℝ × ℝ → ℝ) x = _
  rw [h1, val_glP_K, val_glN_K hxy, glKP_apply, glKN_apply, h2, h3, h4, Pi.smul_apply, h5,
    smul_eq_mul]
  have e := (Neck.kG_glue (βa β R x.1)).2
  simp only [kq]
  linear_combination
    (Neck.dβa β R x.1 * valCLM _ _ (glWP δ h0 hmono jx 0 k v) x) * e.1 +
    (Neck.dβa β R x.1 * valCLM _ _ (glWN δ h0 hmono R ϑ jy 0 k v) x) * e.2.1 +
    (glC δ h0 hmono R ϑ jx jy 0 k v * Neck.dβa β R x.1) * e.2.2

end Kernel

end GWMemoir
