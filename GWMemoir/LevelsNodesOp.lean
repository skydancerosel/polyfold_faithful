import GWMemoir.NeckTestForms
import GWMemoir.LevelRegularitySphere

/-!
# The linearized Cauchy–Riemann operator with nodes on every level

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Propositions 4.7,
4.23, pp. 102–118): the operator `D = linOpN` of `GWMemoir.LinearCRNodesOp` at a constant map,
on the level `n` of the sc-structures, `H^{3+n,δ_n} → H^{2+n,δ_n}` on the blocks.

* `ValEq`, `ValEqB`, `ValEqF`: two bounded operators, on two levels, which agree on the `L²`
  classes; they are closed under sums, scalar multiples and composition, and the building blocks
  (inclusions, derivatives, shifts, multipliers, changes of charts) have this property.
* `zBlockNL`, `rBlockNL`, `rOpNL`, `discPartNL`, `neckRowNL`, **`linOpNL`**: the operator on
  level `n`, from the same derivatives and coefficients as on level `0`.
* **`toBase_linOpNL`**: it agrees with `linOpN` along the inclusions into level `0`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Operators that agree on the `L²` classes -/

section ValEq

variable {k k' l l' p p' : ℕ} {d d' e e' f f' : ℝ} {hd : 0 ≤ d} {hd' : 0 ≤ d'} {he : 0 ≤ e}
  {he' : 0 ≤ e'} {hf : 0 ≤ f} {hf' : 0 ≤ f'}

/-- `T` and `T₀` agree on the `L²` classes. -/
def ValEq (T : H k hd →L[ℝ] H k' hd') (T0 : H l he →L[ℝ] H l' he') : Prop :=
  ∀ u u0, valCLM k hd u = valCLM l he u0 → valCLM k' hd' (T u) = valCLM l' he' (T0 u0)

lemma ValEq.comp {S : H k' hd' →L[ℝ] H p hf} {S0 : H l' he' →L[ℝ] H p' hf'}
    {T : H k hd →L[ℝ] H k' hd'} {T0 : H l he →L[ℝ] H l' he'} (hS : ValEq S S0) (hT : ValEq T T0) :
    ValEq (S.comp T) (S0.comp T0) := fun u u0 h => hS _ _ (hT u u0 h)

lemma valEq_inclH {m m' : ℕ} (hm : m ≤ k) (hm' : m' ≤ l) (hdd : d' ≤ d) (hee : e' ≤ e) :
    ValEq (inclH hd' hd hm hdd : H k hd →L[ℝ] H m hd')
      (inclH he' he hm' hee : H l he →L[ℝ] H m' he') :=
  fun _ _ h => by rw [valCLM_inclH, valCLM_inclH]; exact h

lemma valEq_shH (R ϑ : ℝ) :
    ValEq (Neck.shH R ϑ : H k hd →L[ℝ] H k hd) (Neck.shH R ϑ : H l he →L[ℝ] H l he) :=
  fun _ _ h => by
    change Neck.shLp R ϑ (valCLM k hd _) = Neck.shLp R ϑ (valCLM l he _)
    rw [h]

lemma valEq_op (D : ChartChange) {a : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (haK : tsupport a ⊆ D.K) :
    ValEq (D.op k hd ha haK hd') (D.op l he ha haK he') := fun _ _ h => by
  rw [valCLM_op, valCLM_op, h]

lemma valEq_mulHL {χ : ℝ → ℝ} (h1 : Mult k χ) (h2 : Mult l χ) :
    ValEq (Neck.mulHL χ h1 : H k hd →L[ℝ] H k hd) (Neck.mulHL χ h2 : H l he →L[ℝ] H l he) :=
  fun u u0 h => Lp.ext ((Neck.val_mulHL χ h1 u).trans (by
    rw [h]; exact (Neck.val_mulHL χ h2 u0).symm))

lemma valEq_dsH : ValEq (dsH k hd) (dsH l he) := fun u u0 h => val_dsH_eq u u0 h

lemma valEq_dtH : ValEq (dtH k hd) (dtH l he) := fun u u0 h => val_dtH_eq u u0 h

lemma val_toH_eq {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    valCLM k hd (toH k hd hφ) = valCLM l he (toH l he hφ) :=
  Lp.ext ((val_toH (m := k) (hδ := hd) hφ).trans (val_toH (m := l) (hδ := he) hφ).symm)

lemma val_toHdisc_eq {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hFK : tsupport F ⊆ closedDisc) :
    valCLM k hd (toHdisc hF hFK k hd) = valCLM l he (toHdisc hF hFK l he) :=
  Lp.ext ((val_toHdisc hF hFK k hd).trans (val_toHdisc hF hFK l he).symm)

end ValEq

section ValEqB

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q} {A : SectionAtlas (E := E) X u}
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}
variable {k l : ℕ} {d e : ℝ} {hd : 0 ≤ d} {he : 0 ≤ e} (n : ℕ)

/-- `T` on the level-`n` section blocks and `T₀` on the level-`0` section blocks agree on the
`L²` classes along the inclusion. -/
def ValEqB (T : (blocks A δ h0 hmono) n →L[ℝ] H k hd)
    (T0 : (blocks A δ h0 hmono) 0 →L[ℝ] H l he) : Prop :=
  ∀ v, valCLM k hd (T v) = valCLM l he (T0 ((blocks A δ h0 hmono).toBase n v))

/-- The same on the fibre blocks. -/
def ValEqF (T : (fibreBlocks A δ h0 hmono) n →L[ℝ] H k hd)
    (T0 : (fibreBlocks A δ h0 hmono) 0 →L[ℝ] H l he) : Prop :=
  ∀ v, valCLM k hd (T v) = valCLM l he (T0 ((fibreBlocks A δ h0 hmono).toBase n v))

variable {n}

lemma ValEqB.add {T T' : (blocks A δ h0 hmono) n →L[ℝ] H k hd}
    {T0 T0' : (blocks A δ h0 hmono) 0 →L[ℝ] H l he} (h : ValEqB n T T0) (h' : ValEqB n T' T0') :
    ValEqB n (T + T') (T0 + T0') := fun v => by
  rw [add_apply, add_apply, map_add, map_add, h v, h' v]

lemma ValEqB.sub {T T' : (blocks A δ h0 hmono) n →L[ℝ] H k hd}
    {T0 T0' : (blocks A δ h0 hmono) 0 →L[ℝ] H l he} (h : ValEqB n T T0) (h' : ValEqB n T' T0') :
    ValEqB n (T - T') (T0 - T0') := fun v => by
  rw [sub_apply, sub_apply, map_sub, map_sub, h v, h' v]

lemma ValEqB.smul (c : ℝ) {T : (blocks A δ h0 hmono) n →L[ℝ] H k hd}
    {T0 : (blocks A δ h0 hmono) 0 →L[ℝ] H l he} (h : ValEqB n T T0) :
    ValEqB n (c • T) (c • T0) := fun v => by
  rw [smul_apply, smul_apply, map_smul, map_smul, h v]

lemma ValEqB.sum {ι : Type*} (s : Finset ι) {T : ι → (blocks A δ h0 hmono) n →L[ℝ] H k hd}
    {T0 : ι → (blocks A δ h0 hmono) 0 →L[ℝ] H l he} (h : ∀ i, ValEqB n (T i) (T0 i)) :
    ValEqB n (∑ i ∈ s, T i) (∑ i ∈ s, T0 i) := fun v => by
  rw [_root_.sum_apply, _root_.sum_apply, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => h i v

lemma ValEq.compB {k' l' : ℕ} {d' e' : ℝ} {hd' : 0 ≤ d'} {he' : 0 ≤ e'}
    {S : H k hd →L[ℝ] H k' hd'} {S0 : H l he →L[ℝ] H l' he'}
    {T : (blocks A δ h0 hmono) n →L[ℝ] H k hd} {T0 : (blocks A δ h0 hmono) 0 →L[ℝ] H l he}
    (hS : ValEq S S0) (hT : ValEqB n T T0) : ValEqB n (S.comp T) (S0.comp T0) :=
  fun v => hS _ _ (hT v)

lemma valEqB_smulRight {c : (blocks A δ h0 hmono) n →L[ℝ] ℝ} {c0 : (blocks A δ h0 hmono) 0 →L[ℝ] ℝ}
    (hc : ∀ v, c v = c0 ((blocks A δ h0 hmono).toBase n v)) {x : H k hd} {x0 : H l he}
    (hx : valCLM k hd x = valCLM l he x0) : ValEqB n (c.smulRight x) (c0.smulRight x0) :=
  fun v => by
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply, map_smul,
      map_smul, hc v, hx]

lemma ValEqF.add {T T' : (fibreBlocks A δ h0 hmono) n →L[ℝ] H k hd}
    {T0 T0' : (fibreBlocks A δ h0 hmono) 0 →L[ℝ] H l he} (h : ValEqF n T T0)
    (h' : ValEqF n T' T0') : ValEqF n (T + T') (T0 + T0') := fun v => by
  rw [add_apply, add_apply, map_add, map_add, h v, h' v]

lemma ValEqF.sum {ι : Type*} (s : Finset ι) {T : ι → (fibreBlocks A δ h0 hmono) n →L[ℝ] H k hd}
    {T0 : ι → (fibreBlocks A δ h0 hmono) 0 →L[ℝ] H l he} (h : ∀ i, ValEqF n (T i) (T0 i)) :
    ValEqF n (∑ i ∈ s, T i) (∑ i ∈ s, T0 i) := fun v => by
  rw [_root_.sum_apply, _root_.sum_apply, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => h i v

lemma ValEq.compF {k' l' : ℕ} {d' e' : ℝ} {hd' : 0 ≤ d'} {he' : 0 ≤ e'}
    {S : H k hd →L[ℝ] H k' hd'} {S0 : H l he →L[ℝ] H l' he'}
    {T : (fibreBlocks A δ h0 hmono) n →L[ℝ] H k hd}
    {T0 : (fibreBlocks A δ h0 hmono) 0 →L[ℝ] H l he}
    (hS : ValEq S S0) (hT : ValEqF n T T0) : ValEqF n (S.comp T) (S0.comp T0) :=
  fun v => hS _ _ (hT v)

end ValEqB

/-! ## 2. The blocks along the inclusions -/

section Blocks

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q} {A : SectionAtlas (E := E) X (fun _ => q)}
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

lemma neck_blocks_toBase (n : ℕ) (w : (blocks A δ h0 hmono) n)
    (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    ((blocks A δ h0 hmono).toBase n w).2 jk =
      ((w.2 jk).1, (Neck.scCyl δ h0 hmono).toBase n (w.2 jk).2) := by
  have e1 := ScBanach.prod_toBase
    (finPiSc fun _ : Fin A.nd × Fin (Module.finrank ℝ E) => Neck.scCyl δ h0 hmono)
    (finPiSc fun _ : Fin A.nn × Fin (Module.finrank ℝ E) => Neck.scCylC δ h0 hmono) n w
  have e2 := finPiScale_toBase
    (fun _ : Fin A.nn × Fin (Module.finrank ℝ E) => (Neck.scCylC δ h0 hmono).toScScale) n w.2
  have e3 : ((blocks A δ h0 hmono).toBase n w).2 jk =
      (Neck.scCylC δ h0 hmono).toBase n (w.2 jk) := by
    change (((finPiSc _).prod (finPiSc _)).toBase n w).2 jk = _
    rw [e1]
    exact congrFun e2 jk
  rw [e3]
  refine (ScBanach.prod_toBase (ScBanach.const ℝ) (Neck.scCyl δ h0 hmono) n (w.2 jk)).trans ?_
  rw [ScBanach.const_toBase]

lemma val_neck_toBase (n : ℕ) (w : (blocks A δ h0 hmono) n)
    (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    H.val (((blocks A δ h0 hmono).toBase n w).2 jk).2 = H.val (w.2 jk).2 := by
  rw [neck_blocks_toBase]
  exact Neck.val_toBase δ h0 hmono n _

lemma const_neck_toBase (n : ℕ) (w : (blocks A δ h0 hmono) n)
    (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (((blocks A δ h0 hmono).toBase n w).2 jk).1 = (w.2 jk).1 := by
  rw [neck_blocks_toBase]

lemma fibre_toBase_snd (n : ℕ) (w : (fibreBlocks A δ h0 hmono) n)
    (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    ((fibreBlocks A δ h0 hmono).toBase n w).2 jk =
      (Neck.scCylOff 2 δ h0 hmono).toBase n (w.2 jk) := by
  have e1 := ScBanach.prod_toBase
    (finPiSc fun _ : Ix A => Neck.scCylOff 2 δ h0 hmono)
    (finPiSc fun _ : Fin A.nn × Fin (Module.finrank ℝ E) => Neck.scCylOff 2 δ h0 hmono) n w
  have e2 := finPiScale_toBase
    (fun _ : Fin A.nn × Fin (Module.finrank ℝ E) => (Neck.scCylOff 2 δ h0 hmono).toScScale) n w.2
  change (((finPiSc _).prod (finPiSc _)).toBase n w).2 jk = _
  rw [e1]
  exact congrFun e2 jk

lemma val_fibreNeck_toBase (n : ℕ) (w : (fibreBlocks A δ h0 hmono) n)
    (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    H.val (((fibreBlocks A δ h0 hmono).toBase n w).2 jk) = H.val (w.2 jk) := by
  rw [fibre_toBase_snd]
  exact Neck.val_toBaseOff 2 δ h0 hmono n _

/-- Two level-`0` fibre tuples with the same `L²` classes are equal. -/
lemma fibre_ext_val {y y' : (fibreBlocks A δ h0 hmono) 0}
    (h1 : ∀ o, H.val (y.1 o) = H.val (y'.1 o)) (h2 : ∀ jk, H.val (y.2 jk) = H.val (y'.2 jk)) :
    y = y' :=
  Prod.ext (funext fun o => valCLM_injective (h1 o)) (funext fun jk => valCLM_injective (h2 jk))

/-- The neck remainder `(j, k)` on level `n`, in `H^{3+n,δ_n}`. -/
def neckWL (n : ℕ) (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) n →L[ℝ] H (3 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (ContinuousLinearMap.snd ℝ ℝ _).comp
    ((ContinuousLinearMap.proj jk).comp (ContinuousLinearMap.snd ℝ _ _))

/-- The neck constant `(j, k)` on level `n`. -/
def neckCL (n : ℕ) (jk : Fin A.nn × Fin (Module.finrank ℝ E)) : (blocks A δ h0 hmono) n →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ _).comp
    ((ContinuousLinearMap.proj jk).comp (ContinuousLinearMap.snd ℝ _ _))

/-- `H^{3+n,δ_n} → H^{2+n,δ_n}`. -/
abbrev incl32L (n : ℕ) :
    H (3 + n) (Neck.δ_nonneg δ h0 hmono n) →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  inclH _ _ (by omega : 2 + n ≤ 3 + n) le_rfl

lemma valEqB_secProjL (n : ℕ) (ik : Fin A.nd × Fin (Module.finrank ℝ E)) :
    ValEqB n (secProjL δ h0 hmono n ik) (secProj δ h0 hmono ik) :=
  fun v => (val_blocks_toBase n v ik).symm

lemma valEqB_neckWL (n : ℕ) (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    ValEqB n (neckWL δ h0 hmono n jk) (neckW δ h0 hmono jk) :=
  fun v => (val_neck_toBase δ h0 hmono n v jk).symm

lemma neckCL_eq (n : ℕ) (jk : Fin A.nn × Fin (Module.finrank ℝ E)) (v : (blocks A δ h0 hmono) n) :
    neckCL δ h0 hmono n jk v = neckC δ h0 hmono jk ((blocks A δ h0 hmono).toBase n v) :=
  (const_neck_toBase δ h0 hmono n v jk).symm

lemma valEq_incl32L (n : ℕ) :
    ValEq (incl32L δ h0 hmono n) (incl32 δ h0 hmono) := valEq_inclH _ _ le_rfl le_rfl

lemma valEq_dHL (n : ℕ) (d : Fin 2) : ValEq (dHL δ h0 hmono n d) (dH δ h0 hmono d) :=
  fun w w' h => val_dHL δ h0 hmono n d w w' h

end Blocks

/-! ## 3. The operator on level `n` -/

section Operators

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {q : Q}
  {A : SectionAtlas (E := E) X (fun _ => q)} (G : GlueDataN A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (n : ℕ)

include hT in
/-- The zeroth-order term `zBlockN` on level `n`. -/
def zBlockNL (o : Ix A) :
    (blocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  ∑ i', ((G.D o.1 i').op (2 + n) (Neck.δ_nonneg δ h0 hmono n)
      (contDiff_coefZ hT o.2.1 (G.ρ i') _ _ _ _ (G.hρ i')) (G.hsZ hT o.2.1 o.1 i')
      (Neck.δ_nonneg δ h0 hmono n)).comp
        ((incl32L δ h0 hmono n).comp (secProjL δ h0 hmono n (i', o.2.2))) +
  ∑ j, ∑ a, ((G.Dn o.1 j a).op (2 + n) (Neck.δ_nonneg δ h0 hmono n) (G.cN_smooth o.2.1 o.1 j a)
      (G.cN_supp o.2.1 o.1 j a) (Neck.δ_nonneg δ h0 hmono n)).comp
        ((Neck.shH 0 (G.θ a)).comp ((incl32L δ h0 hmono n).comp (neckWL δ h0 hmono n (j, o.2.2)))) +
  ∑ j, (neckCL δ h0 hmono n (j, o.2.2)).smulRight
    (toHdisc (contDiff_cstD hT G o.2.1 o.1 j) (tsupport_cstD G o.2.1 o.1 j) (2 + n)
      (Neck.δ_nonneg δ h0 hmono n))

include hT in
/-- The disc block `(i, d, k)` of `R` on level `n`. -/
def rBlockNL (o : Ix A) :
    (blocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (A.ε o.1)⁻¹ • ((dHL δ h0 hmono n o.2.1).comp (secProjL δ h0 hmono n (o.1, o.2.2)) -
    zBlockNL hT G δ h0 hmono n o)

include hT in
/-- `R` on level `n`. -/
def rOpNL : (blocks A δ h0 hmono) n →L[ℝ] (fibreBlocks A δ h0 hmono) n :=
  (ContinuousLinearMap.pi fun o => rBlockNL hT G δ h0 hmono n o).prod 0

include hT in
/-- `½ (R + P R)` on level `n`. -/
def discPartNL (J₀ : E →L[ℝ] E) : (blocks A δ h0 hmono) n →L[ℝ] (fibreBlocks A δ h0 hmono) n :=
  (1 / 2 : ℝ) • (rOpNL hT G δ h0 hmono n + (fOp δ h0 hmono (fun _ _ => idCC) (aPI A J₀)
    (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _) (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A)
      n).comp (rOpNL hT G δ h0 hmono n))

/-- The neck row `(j, k)` on level `n`. -/
def neckRowNL (J₀ : E →L[ℝ] E) (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (1 / 2 : ℝ) • ((Neck.shH (A.s0 jk.1) 0).comp
      ((dHL δ h0 hmono n 0).comp (neckWL δ h0 hmono n jk)) +
    ∑ l, Jm J₀ jk.2 l • (Neck.shH (A.s0 jk.1) 0).comp
      ((dHL δ h0 hmono n 1).comp (neckWL δ h0 hmono n (jk.1, l)))) -
  (1 / 2 : ℝ) • (∑ i, ∑ a, (Neck.shH 0 (G.θ a)).comp
      (((G.Dd jk.1 i a).op (2 + n) (Neck.δ_nonneg δ h0 hmono n) (G.cD_smooth jk.1 i a)
        (G.cD_supp jk.1 i a) (Neck.δ_nonneg δ h0 hmono n)).comp
          ((incl32L δ h0 hmono n).comp (secProjL δ h0 hmono n (i, jk.2)))) +
    (Neck.mulHL (mulN (A.s0 jk.1) (G.χ jk.1))
      (mult_mulN (G.χ_smooth jk.1) (G.χ_zero jk.1) (2 + n))).comp
        ((Neck.shH (A.s0 jk.1) 0).comp ((incl32L δ h0 hmono n).comp (neckWL δ h0 hmono n jk))) -
    (neckCL δ h0 hmono n jk).smulRight
      (toH (2 + n) (Neck.δ_nonneg δ h0 hmono n) (isTest_cstN (s₀ := A.s0 jk.1) (G.χ_smooth jk.1))))

include hT in
/-- **`D` on level `n`**: `H^{3+n,δ_n} → H^{2+n,δ_n}` on the blocks, the disc rows `½ (R + P R)`
and the neck rows `neckRowNL`. -/
def linOpNL (J₀ : E →L[ℝ] E) : (blocks A δ h0 hmono) n →L[ℝ] (fibreBlocks A δ h0 hmono) n :=
  ((ContinuousLinearMap.fst ℝ _ _).comp (discPartNL hT G δ h0 hmono n J₀)).prod
    (ContinuousLinearMap.pi fun jk => neckRowNL G δ h0 hmono n J₀ jk)

/-! ### Agreement with level `0` -/

lemma valEqB_zBlockNL (o : Ix A) :
    ValEqB n (zBlockNL hT G δ h0 hmono n o) (zBlockN hT G δ h0 hmono o) := by
  refine ((ValEqB.sum _ fun i' => ?_).add (ValEqB.sum _ fun j => ValEqB.sum _ fun a => ?_)).add
    (ValEqB.sum _ fun j => ?_)
  · exact (valEq_op _ _ _).compB
      ((valEq_incl32L δ h0 hmono n).compB (valEqB_secProjL δ h0 hmono n _))
  · exact (valEq_op _ _ _).compB ((valEq_shH _ _).compB
      ((valEq_incl32L δ h0 hmono n).compB (valEqB_neckWL δ h0 hmono n _)))
  · exact valEqB_smulRight (neckCL_eq δ h0 hmono n _) (val_toHdisc_eq _ _)

lemma valEqB_rBlockNL (o : Ix A) :
    ValEqB n (rBlockNL hT G δ h0 hmono n o) (rBlockN hT G δ h0 hmono o) :=
  ((((valEq_dHL δ h0 hmono n o.2.1).compB (valEqB_secProjL δ h0 hmono n _)).sub
    (valEqB_zBlockNL hT G δ h0 hmono n o))).smul _

lemma fibre_toBase_fst (w : (fibreBlocks A δ h0 hmono) n) (o : Ix A) :
    H.val (((fibreBlocks A δ h0 hmono).toBase n w).1 o) = H.val (w.1 o) :=
  val_fibre_toBase n w o

lemma toBase_rOpNL (v : (blocks A δ h0 hmono) n) :
    (fibreBlocks A δ h0 hmono).toBase n (rOpNL hT G δ h0 hmono n v) =
      rOpN hT G δ h0 hmono ((blocks A δ h0 hmono).toBase n v) := by
  refine fibre_ext_val δ h0 hmono (fun o => ?_) (fun jk => ?_)
  · rw [fibre_toBase_fst]
    exact valEqB_rBlockNL hT G δ h0 hmono n o v
  · rw [val_fibreNeck_toBase]
    exact (map_zero (valCLM (2 + n) (Neck.δ_nonneg δ h0 hmono n))).trans
      (map_zero (valCLM 2 (Neck.δ_nonneg δ h0 hmono 0))).symm

/-- `fOp` on level `n` agrees with `fOp` on level `0`, with or without nodes. -/
lemma toBase_fOpN {T : Type} [Fintype T] {D : Ix A → T → ChartChange}
    {a : Ix A → T → ℝ × ℝ → ℝ}
    (hc : ∀ o t, ContDiff ℝ ∞ (a o t)) (hs : ∀ o t, tsupport (a o t) ⊆ (D o t).K)
    (src : Ix A → T → Ix A) (w : (fibreBlocks A δ h0 hmono) n) :
    (fibreBlocks A δ h0 hmono).toBase n (fOp δ h0 hmono D a hc hs src n w) =
      fOp δ h0 hmono D a hc hs src 0 ((fibreBlocks A δ h0 hmono).toBase n w) := by
  refine fibre_ext_val δ h0 hmono (fun o => ?_) (fun jk => ?_)
  · rw [fibre_toBase_fst, val_fOp, val_fOp]
    exact Finset.sum_congr rfl fun t _ => by rw [fibre_toBase_fst]
  · rw [val_fibreNeck_toBase]
    exact (map_zero (valCLM (2 + n) (Neck.δ_nonneg δ h0 hmono n))).trans
      (map_zero (valCLM 2 (Neck.δ_nonneg δ h0 hmono 0))).symm

lemma toBase_discPartNL (J₀ : E →L[ℝ] E) (v : (blocks A δ h0 hmono) n) :
    (fibreBlocks A δ h0 hmono).toBase n (discPartNL hT G δ h0 hmono n J₀ v) =
      discPartN hT G δ h0 hmono J₀ ((blocks A δ h0 hmono).toBase n v) := by
  have e : discPartNL hT G δ h0 hmono n J₀ v = (1 / 2 : ℝ) • (rOpNL hT G δ h0 hmono n v +
      fOp δ h0 hmono (fun _ _ => idCC) (aPI A J₀) (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _)
        (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A) n (rOpNL hT G δ h0 hmono n v)) := rfl
  have e0 : discPartN hT G δ h0 hmono J₀ ((blocks A δ h0 hmono).toBase n v) =
      (1 / 2 : ℝ) • (rOpN hT G δ h0 hmono ((blocks A δ h0 hmono).toBase n v) +
      fOp δ h0 hmono (fun _ _ => idCC) (aPI A J₀) (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _)
        (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A) 0
          (rOpN hT G δ h0 hmono ((blocks A δ h0 hmono).toBase n v))) := rfl
  have h1 := toBase_fOpN δ h0 hmono n (D := fun _ _ => idCC) (a := aPI A J₀)
    (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _) (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A)
    (rOpNL hT G δ h0 hmono n v)
  rw [e, e0, map_smul, map_add, h1, toBase_rOpNL]

lemma valEqB_neckRowNL (J₀ : E →L[ℝ] E) (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    ValEqB n (neckRowNL G δ h0 hmono n J₀ jk) (neckRowN G δ h0 hmono J₀ jk) := by
  refine (((valEq_shH _ _).compB ((valEq_dHL δ h0 hmono n 0).compB
    (valEqB_neckWL δ h0 hmono n jk))).add (ValEqB.sum _ fun l => ((valEq_shH _ _).compB
      ((valEq_dHL δ h0 hmono n 1).compB (valEqB_neckWL δ h0 hmono n _))).smul _)).smul _ |>.sub
    ((((ValEqB.sum _ fun i => ValEqB.sum _ fun a => (valEq_shH _ _).compB ((valEq_op _ _ _).compB
      ((valEq_incl32L δ h0 hmono n).compB (valEqB_secProjL δ h0 hmono n _)))).add
      ((valEq_mulHL _ _).compB ((valEq_shH _ _).compB ((valEq_incl32L δ h0 hmono n).compB
        (valEqB_neckWL δ h0 hmono n jk))))).sub
      (valEqB_smulRight (neckCL_eq δ h0 hmono n jk) (val_toH_eq _))).smul _)

/-- **`D` on level `n` agrees with `D` on level `0` along the inclusions.** -/
theorem toBase_linOpNL (J₀ : E →L[ℝ] E) (v : (blocks A δ h0 hmono) n) :
    (fibreBlocks A δ h0 hmono).toBase n (linOpNL hT G δ h0 hmono n J₀ v) =
      linOpN hT G δ h0 hmono J₀ ((blocks A δ h0 hmono).toBase n v) := by
  refine fibre_ext_val δ h0 hmono (fun o => ?_) (fun jk => ?_)
  · rw [fibre_toBase_fst]
    have h := congrArg (fun y : (fibreBlocks A δ h0 hmono) 0 => H.val (y.1 o))
      (toBase_discPartNL hT G δ h0 hmono n J₀ v)
    rw [fibre_toBase_fst] at h
    exact h
  · rw [val_fibreNeck_toBase]
    exact valEqB_neckRowNL G δ h0 hmono n J₀ jk v

end Operators

end GWMemoir
