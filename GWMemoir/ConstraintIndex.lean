import GWMemoir.CokernelSphere
import GWMemoir.LinearCRSphereFredholm

/-!
# The index of `D` under point constraints on the three-pointed sphere

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §3.1 (the space `E_u`,
p. 68) and §4.2 (Theorem 4.6, p. 101; the constrained space `E`, p. 103).  At the constant map
`u ≡ q` from `sphere3`, `D = linCR3` on `H^{3,δ₀}_c(S², u*TQ)`:

* **`evalAt`**, **`evalAtL`**: the evaluation `ξ ↦ ξ(z)` at a point of `S²`, a continuous linear
  map `H^{3,δ₀}_c → E` (`H³ ⊂ C⁰`: each element represents a unique continuous section; the
  kernel of every coordinate of the evaluation is a constraint space, closed by
  `constraintsClosed_of_nodes_empty`);
* **`exists_smooth_interp`**: smooth sections with prescribed values at finitely many distinct
  points, `ξ(x) = ∑_l ∏_{m ≠ l} ‖x - z_m‖² / ‖z_l - z_m‖² · a_l`;
* **`evalC`**, **`conSub`**: for constraints `ξ(z_l) ∈ H_l` (`LinearConstraints`), the map
  `ξ ↦ (ξ(z_l) mod H_l)_l` and its kernel, which is `E_u` (`mem_conSub_iff`);
  **`evalC_surjective`** for distinct points, and **`finrank_quotient_conSub`**: the codimension
  of `E_u` is `∑_l codim H_l`;
* **`constraint_isFredholm_index`**: `D|_{E_u}` is Fredholm of index `dim E - ∑_l codim H_l`;
* **`ev3`**: the evaluation at the three marked points, a continuous linear surjection onto `E³`
  (`ev3_surjective`) with kernel `E_u` for `H = 0` (`ker_ev3`), of codimension `3 dim E`
  (`finrank_quotient_ker_ev3`);
* **`three_points_index`**: `D` on that kernel is Fredholm, injective, of index `-2 dim E`, with
  a cokernel of dimension `2 dim E`.

## Readings

* The memoir's constraints (Definition 3.6 (4), p. 65; p. 68) sit at the points of a
  stabilization set `Σ`, disjoint from the marked points, and `H_{u(z)} = T_{u(z)} M_{u(z)}` has
  codimension `2`.  With `c_l = 2` the general formula gives `dim E - 2 |Σ|`; the `2 |Σ|` is the
  dimension of the positions of the points of `Σ` in the parameters `v` of the domain.
* At a constant map `T u(z) = 0`, so the transversality in Definition 3.6 (4), (7) holds for no
  `z`, and `Σ = ∅`: `E_u` is the whole section space and `D` has index `dim E = 2n`
  (`linCR_isFredholm_sphere3`).  This is Theorem 4.6, `2n(1 - g) + 2c₁(A) + 6g - 6 + 2k`, at
  `g = 0`, `A = 0`, `k = 3`.  The constraints `H = 0` at the three marked points are not the
  memoir's constraints; their index `-2 dim E` is not an instance of Theorem 4.6.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Point evaluation -/

section Eval

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

lemma exists_sec (w : sectionSpace A δ h0 hmono) :
    ∃ η : Section E sphere3, IsContSection (fun _ => q) η ∧
      IsRep η (w : (blocks A δ h0 hmono) 0) := by
  have hw : (w : (blocks A δ h0 hmono) 0) ∈ sectionsSub A δ h0 hmono := by
    rw [← sectionSpace_eq_of_nodes_empty continuous_const rfl A δ h0 hmono]; exact w.2
  obtain ⟨η, hc, -, hr⟩ := hw
  exact ⟨η, hc, hr⟩

/-- The continuous section represented by an element of `H^{3,δ₀}_c(S², u*TQ)`. -/
def secW (w : sectionSpace A δ h0 hmono) : Section E sphere3 := (exists_sec δ h0 hmono w).choose

lemma secW_spec (w : sectionSpace A δ h0 hmono) :
    IsContSection (fun _ => q) (secW δ h0 hmono w) ∧
      IsRep (secW δ h0 hmono w) (w : (blocks A δ h0 hmono) 0) :=
  (exists_sec δ h0 hmono w).choose_spec

lemma secW_eq {w : sectionSpace A δ h0 hmono} {η : Section E sphere3}
    (hc : IsContSection (fun _ => q) η) (hr : IsRep η (w : (blocks A δ h0 hmono) 0)) :
    secW δ h0 hmono w = η :=
  eq_of_isRep rfl (fun _ => rfl) (secW_spec δ h0 hmono w).1 hc (secW_spec δ h0 hmono w).2 hr

/-- **The evaluation `ξ ↦ ξ(z)`** on `H^{3,δ₀}_c(S², u*TQ)`. -/
def evalAt (z : sphere3.S) : sectionSpace A δ h0 hmono →ₗ[ℝ] E where
  toFun w := secW δ h0 hmono w z
  map_add' w w' := by
    have hr : IsRep (secW δ h0 hmono w + secW δ h0 hmono w')
        ((w + w' : sectionSpace A δ h0 hmono) : (blocks A δ h0 hmono) 0) := by
      rw [Submodule.coe_add]
      exact (secW_spec δ h0 hmono w).2.add (secW_spec δ h0 hmono w').2
    rw [secW_eq δ h0 hmono ((secW_spec δ h0 hmono w).1.add (secW_spec δ h0 hmono w').1) hr,
      Pi.add_apply]
  map_smul' c w := by
    have hr : IsRep (c • secW δ h0 hmono w)
        ((c • w : sectionSpace A δ h0 hmono) : (blocks A δ h0 hmono) 0) := by
      rw [Submodule.coe_smul]
      exact (secW_spec δ h0 hmono w).2.smul c
    rw [secW_eq δ h0 hmono ((secW_spec δ h0 hmono w).1.smul c) hr, Pi.smul_apply,
      RingHom.id_apply]

lemma evalAt_eq {w : sectionSpace A δ h0 hmono} {η : Section E sphere3}
    (hc : IsContSection (fun _ => q) η) (hr : IsRep η (w : (blocks A δ h0 hmono) 0))
    (z : sphere3.S) : evalAt δ h0 hmono z w = η z := by
  change secW δ h0 hmono w z = η z
  rw [secW_eq δ h0 hmono hc hr]

/-- Membership in the constraint space is the constraint on the evaluations. -/
lemma mem_constraintsSub_iff (C : LinearConstraints sphere3 E) (w : sectionSpace A δ h0 hmono) :
    (w : (blocks A δ h0 hmono) 0) ∈ constraintsSub A δ h0 hmono C ↔
      ∀ l, evalAt δ h0 hmono (C.pt l) w ∈ C.H l := by
  constructor
  · rintro ⟨η, hc, -, hr, hH⟩ l
    rw [evalAt_eq δ h0 hmono hc hr]; exact hH l
  · intro h
    exact ⟨secW δ h0 hmono w, (secW_spec δ h0 hmono w).1, fun x y hxy => absurd hxy
      (notMem_empty _), (secW_spec δ h0 hmono w).2, h⟩

lemma isClosed_constraints (C : LinearConstraints sphere3 E) :
    IsClosed {w : sectionSpace A δ h0 hmono | ∀ l, evalAt δ h0 hmono (C.pt l) w ∈ C.H l} := by
  have : {w : sectionSpace A δ h0 hmono | ∀ l, evalAt δ h0 hmono (C.pt l) w ∈ C.H l} =
      Subtype.val ⁻¹' (constraintsSub A δ h0 hmono C : Set ((blocks A δ h0 hmono) 0)) := by
    ext w; exact (mem_constraintsSub_iff δ h0 hmono C w).symm
  rw [this]
  exact (constraintsClosed_of_nodes_empty continuous_const rfl A δ h0 hmono C).preimage
    continuous_subtype_val

/-- **`H³ ⊂ C⁰`: the evaluation at a point is continuous.** -/
theorem continuous_evalAt (z : sphere3.S) : Continuous (evalAt (A := A) δ h0 hmono z) := by
  set b := Module.finBasis ℝ E
  have hk : ∀ k, Continuous ((crd k).comp (evalAt (A := A) δ h0 hmono z)) := by
    intro k
    refine LinearMap.continuous_of_isClosed_ker _ ?_
    have := isClosed_constraints (A := A) δ h0 hmono
      (⟨1, fun _ => z, fun _ => LinearMap.ker (crd k)⟩ : LinearConstraints sphere3 E)
    convert this using 1
    ext w
    simp
  have he : ⇑(evalAt (A := A) δ h0 hmono z) =
      fun w => ∑ k, crd k (evalAt δ h0 hmono z w) • b k := by
    funext w
    simp only [crd, Module.Basis.coord_apply]
    exact (b.sum_repr _).symm
  rw [he]
  exact continuous_finsetSum _ fun k _ => (hk k).smul continuous_const

/-- The evaluation at `z` as a continuous linear map. -/
def evalAtL (z : sphere3.S) : sectionSpace A δ h0 hmono →L[ℝ] E :=
  ⟨evalAt δ h0 hmono z, continuous_evalAt (A := A) δ h0 hmono z⟩

end Eval

/-! ## 2. Smooth sections with prescribed values -/

section Interp

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The weight `∏_{m ≠ l} ‖x - z_m‖² / ‖z_l - z_m‖²`: `1` at `z_l`, `0` at the other `z_m`. -/
def lagW {n : ℕ} (z : Fin n → E3) (l : Fin n) (x : E3) : ℝ :=
  ∏ m ∈ Finset.univ.erase l, ‖x - z m‖ ^ 2 / ‖z l - z m‖ ^ 2

lemma contDiff_lagW {n : ℕ} (z : Fin n → E3) (l : Fin n) : ContDiff ℝ ∞ (lagW z l) :=
  contDiff_prod fun _ _ =>
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _

lemma lagW_self {n : ℕ} {z : Fin n → E3} (hz : Injective z) (l : Fin n) : lagW z l (z l) = 1 :=
  Finset.prod_eq_one fun _ hm => div_self (pow_ne_zero 2 (norm_ne_zero_iff.2
    (sub_ne_zero.2 (hz.ne (Finset.ne_of_mem_erase hm).symm))))

lemma lagW_ne {n : ℕ} (z : Fin n → E3) {l j : Fin n} (h : j ≠ l) : lagW z l (z j) = 0 :=
  Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩) (by simp)

/-- **Smooth sections with prescribed values at distinct points of `S²`.** -/
theorem exists_smooth_interp {n : ℕ} {y : Fin n → S2} (hy : Injective y) (a : Fin n → E) :
    ∃ ξ : S2 → E, ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ ∧ ∀ l, ξ (y l) = a l := by
  set z : Fin n → E3 := fun l => (y l : E3)
  have hz : Injective z := Subtype.val_injective.comp hy
  set F : E3 → E := fun x => ∑ l, lagW z l x • a l
  have hF : ContDiff ℝ ∞ F :=
    ContDiff.sum fun l _ => (contDiff_lagW z l).smul contDiff_const
  refine ⟨F ∘ Subtype.val, hF.contMDiff.comp (contMDiff_coe_sphere (n := 2)), fun j => ?_⟩
  change ∑ l, lagW z l (z j) • a l = a j
  rw [Finset.sum_eq_single j (fun l _ hl => by rw [lagW_ne z (Ne.symm hl), zero_smul])
    (fun h => absurd (Finset.mem_univ j) h), lagW_self hz, one_smul]

end Interp

/-! ## 3. The constraint spaces and their codimension -/

section Constraints

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The section space element of a smooth section. -/
def smoothW {ξ : S2 → E} (hξ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ) : sectionSpace A δ h0 hmono :=
  ⟨smoothBlocks A δ h0 hmono hξ, smoothBlocks_mem A δ h0 hmono hξ⟩

lemma evalAt_smoothW {ξ : S2 → E} (hξ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ) (z : sphere3.S) :
    evalAt δ h0 hmono z (smoothW (A := A) δ h0 hmono hξ) = ξ z := by
  have hc : IsContSection (fun _ : sphere3.S => q) (ξ : Section E sphere3) :=
    isContSection_of_const (u := fun _ : sphere3.S => q) (fun _ => rfl) hξ.continuous
  have hr : IsRep (ξ : Section E sphere3)
      ((smoothW (A := A) δ h0 hmono hξ : sectionSpace A δ h0 hmono) : (blocks A δ h0 hmono) 0) :=
    isRep_smoothBlocks A δ h0 hmono hξ
  exact evalAt_eq δ h0 hmono hc hr z

/-- The map `ξ ↦ (ξ(z_l) mod H_l)_l` of the constraints `ξ(z_l) ∈ H_l`. -/
def evalC (C : LinearConstraints sphere3 E) :
    sectionSpace A δ h0 hmono →ₗ[ℝ] (∀ l, E ⧸ C.H l) :=
  LinearMap.pi fun l => (C.H l).mkQ ∘ₗ evalAt δ h0 hmono (C.pt l)

/-- The kernel of `evalC`, inside `H^{3,δ₀}_c(S², u*TQ)`. -/
def conSub (C : LinearConstraints sphere3 E) : Submodule ℝ (sectionSpace A δ h0 hmono) :=
  LinearMap.ker (evalC δ h0 hmono C)

lemma mem_conSub_iff' (C : LinearConstraints sphere3 E) (w : sectionSpace A δ h0 hmono) :
    w ∈ conSub δ h0 hmono C ↔ ∀ l, evalAt δ h0 hmono (C.pt l) w ∈ C.H l := by
  simp only [conSub, evalC, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply,
    LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]

/-- **The kernel of `evalC` is `E_u`** (Memoir p. 68). -/
theorem mem_conSub_iff (C : LinearConstraints sphere3 E) (w : sectionSpace A δ h0 hmono) :
    w ∈ conSub δ h0 hmono C ↔ (w : (blocks A δ h0 hmono) 0) ∈ uSpace A δ h0 hmono C := by
  rw [uSpace_eq A δ h0 hmono C (constraintsClosed_of_nodes_empty continuous_const rfl A δ h0
    hmono C), mem_constraintsSub_iff, mem_conSub_iff']

theorem isClosed_conSub (C : LinearConstraints sphere3 E) :
    IsClosed (conSub (A := A) δ h0 hmono C : Set (sectionSpace A δ h0 hmono)) := by
  convert isClosed_constraints (A := A) δ h0 hmono C using 1
  ext w; exact mem_conSub_iff' δ h0 hmono C w

instance (C : LinearConstraints sphere3 E) :
    FiniteDimensional ℝ (sectionSpace A δ h0 hmono ⧸ conSub δ h0 hmono C) :=
  LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange (evalC δ h0 hmono C)).symm

/-- **The constraints at distinct points are independent**: `evalC` is onto. -/
theorem evalC_surjective (C : LinearConstraints sphere3 E) (hC : Injective C.pt) :
    Surjective (evalC (A := A) δ h0 hmono C) := by
  intro x
  choose a ha using fun l => Submodule.Quotient.mk_surjective (C.H l) (x l)
  obtain ⟨ξ, hξ, hξa⟩ := exists_smooth_interp (y := C.pt) hC a
  refine ⟨smoothW δ h0 hmono hξ, funext fun l => ?_⟩
  simp only [evalC, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    evalAt_smoothW, hξa, ha]

/-- **The codimension of `E_u` is `∑_l codim H_l`.** -/
theorem finrank_quotient_conSub (C : LinearConstraints sphere3 E) (hC : Injective C.pt) :
    Module.finrank ℝ (sectionSpace A δ h0 hmono ⧸ conSub δ h0 hmono C) =
      ∑ l, Module.finrank ℝ (E ⧸ C.H l) := by
  rw [conSub, (LinearMap.quotKerEquivOfSurjective _ (evalC_surjective δ h0 hmono C hC)).finrank_eq,
    Module.finrank_pi_fintype]

/-- **The evaluation at the three marked points**, `ξ ↦ (ξ(e₀), ξ(e₁), ξ(e₂))`. -/
def ev3 : sectionSpace A δ h0 hmono →L[ℝ] (Fin 3 → E) :=
  ContinuousLinearMap.pi fun l => evalAtL δ h0 hmono (pt l)

theorem ev3_apply (w : sectionSpace A δ h0 hmono) (l : Fin 3) :
    ev3 δ h0 hmono w l = evalAt δ h0 hmono (pt l) w := rfl

/-- **`ev3` is onto `E³`** (smooth sections with prescribed values at `e₀, e₁, e₂`). -/
theorem ev3_surjective : Surjective (ev3 (A := A) δ h0 hmono) := by
  intro a
  obtain ⟨ξ, hξ, hξa⟩ := exists_smooth_interp pt_injective a
  exact ⟨smoothW δ h0 hmono hξ, funext fun l => (evalAt_smoothW δ h0 hmono hξ (pt l)).trans
    (hξa l)⟩

/-- **The kernel of `ev3` is `E_u` for the constraints `H = 0` at `e₀, e₁, e₂`.** -/
theorem ker_ev3 :
    LinearMap.ker (ev3 (A := A) δ h0 hmono : sectionSpace A δ h0 hmono →ₗ[ℝ] (Fin 3 → E)) =
      conSub δ h0 hmono threePoints := by
  ext w
  rw [mem_conSub_iff', LinearMap.mem_ker, funext_iff]
  simp only [ContinuousLinearMap.coe_coe, ev3_apply, Pi.zero_apply]
  exact forall_congr' fun l => (Submodule.mem_bot ℝ).symm

/-- **The codimension of `ker ev3` is `3 · dim E`.** -/
theorem finrank_quotient_ker_ev3 :
    Module.finrank ℝ (sectionSpace A δ h0 hmono ⧸
      LinearMap.ker (ev3 (A := A) δ h0 hmono : sectionSpace A δ h0 hmono →ₗ[ℝ] (Fin 3 → E))) =
      3 * Module.finrank ℝ E := by
  rw [(LinearMap.quotKerEquivOfSurjective _ (ev3_surjective (A := A) δ h0 hmono)).finrank_eq,
    Module.finrank_pi_fintype]
  simp

end Constraints

/-! ## 4. The index under the constraints -/

section Index

/-- The image of a closed subspace under a surjection with finite-dimensional kernel between
Banach spaces is closed (`M ⊔ ker T` is closed and saturated; `T` is open). -/
theorem isClosed_map_of_surjective {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (T : X →L[ℝ] Y) (hT : Surjective T) [FiniteDimensional ℝ (LinearMap.ker (T : X →ₗ[ℝ] Y))]
    (M : Submodule ℝ X) (hM : IsClosed (M : Set X)) :
    IsClosed ((M.map (T : X →ₗ[ℝ] Y) : Submodule ℝ Y) : Set Y) := by
  set K := M ⊔ LinearMap.ker (T : X →ₗ[ℝ] Y)
  have hK : IsClosed (K : Set X) := Submodule.isClosed_sup_finiteDimensional _ _ hM
  have hmap : M.map (T : X →ₗ[ℝ] Y) = K.map (T : X →ₗ[ℝ] Y) := by
    rw [Submodule.map_sup]
    have : (LinearMap.ker (T : X →ₗ[ℝ] Y)).map (T : X →ₗ[ℝ] Y) = ⊥ :=
      (Submodule.eq_bot_iff _).2 fun _ ⟨_, hx, he⟩ => he ▸ hx
    rw [this, sup_bot_eq]
  rw [hmap, ← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨x, rfl⟩ := hT y
  have hx : x ∉ K := fun h => hy ⟨x, h, rfl⟩
  refine Filter.mem_of_superset ((T.isOpenMap hT).image_mem_nhds (hK.isOpen_compl.mem_nhds hx))
    ?_
  rintro _ ⟨x', hx', rfl⟩ ⟨k, hk, he⟩
  apply hx'
  have h1 : x' - k ∈ LinearMap.ker (T : X →ₗ[ℝ] Y) := by
    rw [LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.2 he.symm
  have h2 := K.add_mem hk (Submodule.mem_sup_right h1 : x' - k ∈ K)
  rwa [add_sub_cancel] at h2

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (G : GlueData A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- `D` restricted to `E_u`. -/
abbrev linCRC (C : LinearConstraints sphere3 E) :
    conSub (A := A) δ h0 hmono C →L[ℝ] fibreSpace J A δ h0 hmono :=
  (linCR3 J G δ h0 hmono).comp (conSub δ h0 hmono C).subtypeL

/-- **`D` on `E_u` is Fredholm of index `dim E - ∑_l codim H_l`** (Memoir p. 68 and p. 103, the
constraints `ξ(z_l) ∈ H_l` at distinct points `z_l`; the index of a composition,
`linIndex_comp`). -/
theorem constraint_isFredholm_index (hδ : 0 < δ 0) (C : LinearConstraints sphere3 E)
    (hC : Injective C.pt) :
    (linCRC J G δ h0 hmono C).IsFredholm ∧
      fredholmIndex (linCRC J G δ h0 hmono C) =
        Module.finrank ℝ E - ∑ l, (Module.finrank ℝ (E ⧸ C.H l) : ℤ) := by
  have hCV := cokernelVanishes_sphere3_of_pos J G δ h0 hmono hδ
  obtain ⟨hfin, hind⟩ := linCR_index_restrict J G δ h0 hmono hCV (conSub δ h0 hmono C)
  have : CompleteSpace (conSub (A := A) δ h0 hmono C) :=
    (isClosed_conSub δ h0 hmono C).completeSpace_coe
  refine ⟨isFredholm_of_banach _ hfin.finite_ker ?_ hfin.finite_coker, ?_⟩
  · change IsClosed ((LinearMap.range ((linCR3 J G δ h0 hmono : sectionSpace A δ h0 hmono →ₗ[ℝ]
      fibreSpace J A δ h0 hmono) ∘ₗ (conSub δ h0 hmono C).subtype) :
        Submodule ℝ (fibreSpace J A δ h0 hmono)) : Set (fibreSpace J A δ h0 hmono))
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact isClosed_map_of_surjective _ hCV _ (isClosed_conSub δ h0 hmono C)
  · change linIndex ((linCR3 J G δ h0 hmono).toLinearMap ∘ₗ (conSub δ h0 hmono C).subtype) = _
    rw [hind, finrank_quotient_conSub δ h0 hmono C hC]
    push_cast; rfl

lemma finrank_quotient_bot' : Module.finrank ℝ (E ⧸ (⊥ : Submodule ℝ E)) = Module.finrank ℝ E :=
  (Submodule.quotEquivOfEqBot ⊥ rfl).finrank_eq

/-- **The three point constraints `H = 0` at `e₀, e₁, e₂`**: `D` on `ker ev3` is Fredholm,
injective, of index `dim E - 3 dim E = -2 dim E`, with a cokernel of dimension `2 dim E`. -/
theorem three_points_index (hδ : 0 < δ 0) :
    (linCRC J G δ h0 hmono threePoints).IsFredholm ∧
      Injective (linCRC J G δ h0 hmono threePoints) ∧
      fredholmIndex (linCRC J G δ h0 hmono threePoints) = -2 * Module.finrank ℝ E ∧
      Module.finrank ℝ (fibreSpace J A δ h0 hmono ⧸
        LinearMap.range (linCRC J G δ h0 hmono threePoints :
          conSub (A := A) δ h0 hmono threePoints →ₗ[ℝ] fibreSpace J A δ h0 hmono)) =
        2 * Module.finrank ℝ E := by
  obtain ⟨hF, hind⟩ := constraint_isFredholm_index J G δ h0 hmono hδ threePoints pt_injective
  have hsum : ∑ l, (Module.finrank ℝ (E ⧸ (threePoints (E := E)).H l) : ℤ) =
      3 * Module.finrank ℝ E := by
    change ∑ _l : Fin 3, (Module.finrank ℝ (E ⧸ (⊥ : Submodule ℝ E)) : ℤ) = _
    rw [finrank_quotient_bot']
    simp
  rw [hsum] at hind
  have hinj : Injective (linCRC J G δ h0 hmono threePoints) := by
    have hk : LinearMap.ker (linCRC J G δ h0 hmono threePoints :
        conSub (A := A) δ h0 hmono threePoints →ₗ[ℝ] fibreSpace J A δ h0 hmono) = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 ?_
      rintro ⟨w, hw⟩ hD
      have hD' : linCR3 J G δ h0 hmono w = 0 := hD
      have h1 : linOp sphere3_chartsOnto G δ h0 hmono (J.J q)
          (w : (blocks A δ h0 hmono) 0) = 0 := by
        rw [← linCR_apply rfl sphere3_chartsOnto (fun _ => rfl) G J w]
        exact congrArg Subtype.val hD'
      have h2 := (linCR_ker_three_points J G δ h0 hmono
        ((mem_conSub_iff δ h0 hmono _ w).1 hw)).1 h1
      exact Subtype.ext (Subtype.ext h2)
    exact LinearMap.ker_eq_bot.1 hk
  have hker : Module.finrank ℝ (LinearMap.ker (linCRC J G δ h0 hmono threePoints :
      conSub (A := A) δ h0 hmono threePoints →ₗ[ℝ] fibreSpace J A δ h0 hmono)) = 0 := by
    rw [LinearMap.ker_eq_bot.2 hinj, finrank_bot]
  refine ⟨hF, hinj, by rw [hind]; ring, ?_⟩
  have h := hind
  rw [fredholmIndex, linIndex, hker] at h
  omega

end Index

end GWMemoir
