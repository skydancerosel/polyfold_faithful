import Polyfold.Chapter2.TameRetracts
import Polyfold.Chapter2.StrongBundlePullback

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.4,
**Proposition 2.43** (the tame part), **Proposition 2.44** (first sentence) and **Theorem 2.45**
(the remaining statements): faces of tame M-polyfolds are tame.

# Faces of tame M-polyfolds

## The text, paraphrased

(Proposition 2.43) A face `F` of a tame retract `O` is a sub-M-polyfold of `O`; it is tame and
`d_F(x) = d_O(x) − 1`.  (Proposition 2.44) In a tame M-polyfold every point `x` has exactly
`d_X(x)` local faces, each a tame M-polyfold with `d_F(x) = d_X(x) − 1`; for a set `σ` of face
germs at `x`, `F^σ_x` is the germ of a tame sub-M-polyfold of codimension `#σ`.  (Theorem 2.45)
For a face `F = closure(G)` of a tame M-polyfold, `G` (the interior of the face) is a
sub-M-polyfold; if `X` is face-structured, every face is a sub-M-polyfold, tame in the induced
structure, and `d_X(i(x)) = d_F(x) + 1`.

## What is formalized

* `Polyfold.minimalSubspaceWith_eq`: `E_x` does not depend on the presentation of `C` (the
  argument of Lemma 1.24), so `ScRetraction.IsTameWith.isTame`: tameness for one presentation is
  tameness (Definition 2.34 is presentation independent).  `ScRetraction.IsTameWith.restrict`.
* The extended face as a model space: `insertCoordL`, `removeCoordL`, the sc-operators
  `faceIncl T i : ℝᵏ ⊕ W → E` (`ι`, onto `f_i`) and `faceProj T i : E → ℝᵏ ⊕ W` (`π`), with
  `π ∘ ι = 1`, `ι ∘ π = 1` on `f_i`, `ι(C') ⊆ C`, `π(C) ⊆ C'` and
  `degIndexWith_eq_quadrantDeg_faceProj_add_one` (`d_C = d_{C'} ∘ π + 1` on `f_i`).
  `ScOperator.scDeriv_eq` (`DL = L`), `scDeriv_comp_apply_of_isScDomain` (chain rule at a point).
* `Polyfold.proposition_2_43_tameModel` (**Proposition 2.43**, the tame model): `r' = π ∘ r ∘ ι`
  is a tame sc-smooth retraction of `C' = [0,∞)ᵏ ⊕ W` onto `π(F)`, and
  `d_{C'}(π y) + 1 = d_C(y)` on `F`.
* `MPolyfold.faceChart` (the chart `π ∘ φ : A ∩ V₁ → π(φ(A ∩ V₁))`),
  `MPolyfold.faceChart_compatible_subChart`, `MPolyfold.isChart_subPolyfold_of_compatible`,
  `MPolyfold.isTame_of_forall_exists_chart`.
* `LocalModel.proposition_2_43_isTame` (**Proposition 2.43**, last statements): a face `F` of a
  tame retract `O`, with its sub-M-polyfold structure, is tame and `d_F(x) + 1 = d_O(x)`.
* `MPolyfold.proposition_2_44` (**Proposition 2.44**, first sentence).
* `MPolyfold.isSubMPolyfold_of_local` (a local criterion for sub-M-polyfolds: `φ(A)` agrees near
  each point with an sc-smooth retract), `MPolyfold.theorem_2_45_isSubMPolyfold_interior`
  (**Theorem 2.45**: the interior `G` of a face is a sub-M-polyfold),
  `MPolyfold.exists_localFace_of_isFaceStructured` (in the face-structured case, a face agrees near
  each of its points with a local face of a tame chart),
  `MPolyfold.theorem_2_45_isSubMPolyfold_face` and `MPolyfold.theorem_2_45_isTame_face`
  (**Theorem 2.45**, face-structured case: every face is a tame sub-M-polyfold with
  `d_X(i(x)) = d_F(x) + 1`).  The local and global face counts of
  Theorem 2.45 are `proposition_2_42` and the definition of face-structured.

## What the text leaves implicit, and the choices made

* The text's model `(F, C ∩ f_1, f_1)` uses the sc-subspace `f_1 = E_1` of `E`; here the
  extended face is represented by `ℝᵏ ⊕ W` itself through `ι = T⁻¹ ∘ (insert 0 at i)` and
  `π = (delete i) ∘ T`, so that `C' = [0,∞)ᵏ ⊕ W` comes with its standard presentation; the
  retraction is `r' = π ∘ r ∘ ι` on `ι⁻¹(U*)`, not the restriction `r|_{U* ∩ f_1}` (they
  correspond under `ι`).
* Tameness (2) of `r'` is proved with `A' = (1 − Dr'(x))E'` (Proposition 2.35 for `r` gives
  `λ_{j'} ∘ Dr(ιx) = λ_{j'}`, hence `(1 − Dr'(x))E' ⊆ E'_x`), not by intersecting the
  complement `A` of `T_xO` with `f_1` as in the exposition.
* "`F` is tame" is read as Definition 2.37 for the sub-M-polyfold structure of Proposition 2.21
  (`subPolyfold`); its paracompactness holds because faces are closed.  `d_F = d_O − 1` is stated
  as `d_F + 1 = d_O` (it includes `d_O ≥ 1` on `F`).
* In Theorem 2.45 (face-structured case) the identification "each global face through `x`
  contains exactly one local face" is the counting argument: the map from `I(φ x)` to the faces
  through `x` is onto, and face-structuredness makes it injective (`Finset.card_image_iff`).

## Elsewhere

* Proposition 2.44, second sentence (the germs `F^σ_x` of codimension `#σ`), is in
  `Polyfold.Chapter2.CornerGerms`.
* Proposition 2.46 (fibred products) is in `Polyfold.Chapter2.FibredProduct`.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

variable {E : ScBanach}

/-! ### `E_x` does not depend on the presentation; tameness does not either -/

section Independence

variable {C : Set (E 0)} {n n' : ℕ} {W W' : ScBanach}

/-- `x + tv ∈ C` for `|t|` small, when `v ∈ E_x` (two-sided). -/
lemma eventually_add_smul_mem_of_minimalSubspace
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    {x : E 0} (hx : x ∈ C) {v : E 0} (hv : v ∈ minimalSubspaceWith T x) :
    ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ C := by
  rw [mem_minimalSubspaceWith] at hv
  have h : ∀ l : Fin n, ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ (T 0 (x + t • v)).1 l := by
    intro l
    have heq : ∀ t : ℝ, (T 0 (x + t • v)).1 l = (T 0 x).1 l + t * (T 0 v).1 l := fun t => by
      simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
    by_cases hl : (T 0 x).1 l = 0
    · exact Eventually.of_forall fun t => by rw [heq, hl, hv l hl, mul_zero, add_zero]
    · have hpos : 0 < (T 0 x).1 l := lt_of_le_of_ne (coord_nonneg hT hx l) (Ne.symm hl)
      have hc : Tendsto (fun t : ℝ => (T 0 x).1 l + t * (T 0 v).1 l) (𝓝 0)
          (𝓝 ((T 0 x).1 l)) := by
        have := (by fun_prop : Continuous fun t : ℝ =>
          (T 0 x).1 l + t * (T 0 v).1 l).tendsto (0 : ℝ)
        simpa using this
      exact (hc.eventually (lt_mem_nhds hpos)).mono fun t ht => by rw [heq]; exact ht.le
  filter_upwards [eventually_all.2 h] with t ht
  rw [hT]; exact fun l => ht l

/-- The minimal subspace `E_x` does not depend on the presentation of `C` (the argument of
Lemma 1.24, `S(E_x) ⊆ E'_{Sx}`). -/
theorem minimalSubspaceWith_le (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) (T' : ScIso E ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : C = T' 0 ⁻¹' quadrant n' W' 0) {x : E 0} (hx : x ∈ C) :
    minimalSubspaceWith T x ≤ minimalSubspaceWith T' x := by
  intro v hv
  rw [mem_minimalSubspaceWith]
  intro j hj
  have hev := eventually_add_smul_mem_of_minimalSubspace T hT hx hv
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hlin : ∀ t : ℝ, (T' 0 (x + t • v)).1 j = t * (T' 0 v).1 j := fun t => by
    simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hj, zero_add]
  have h1 := coord_nonneg hT' (hball (show dist (δ / 2) 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; exact half_lt_self hδ)) j
  have h2 := coord_nonneg hT' (hball (show dist (-(δ / 2)) 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hδ)]; exact half_lt_self hδ)) j
  rw [hlin] at h1 h2
  have hδ2 : 0 < δ / 2 := half_pos hδ
  nlinarith

theorem minimalSubspaceWith_eq (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) (T' : ScIso E ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : C = T' 0 ⁻¹' quadrant n' W' 0) {x : E 0} (hx : x ∈ C) :
    minimalSubspaceWith T x = minimalSubspaceWith T' x :=
  le_antisymm (minimalSubspaceWith_le T hT T' hT' hx) (minimalSubspaceWith_le T' hT' T hT hx)

/-- **Definition 2.34 does not depend on the presentation**: a retraction tame with respect to one
presentation of `C` is tame (with respect to all of them). -/
theorem ScRetraction.IsTameWith.isTame {R : ScRetraction E C}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    (h : R.IsTameWith T) : R.IsTame := by
  intro n'' W'' T'' hT''
  refine ⟨h.degIndex_apply, fun x hx hs => ?_⟩
  obtain ⟨A, hA, hAE⟩ := h.exists_complement x hx hs
  refine ⟨A, hA, ?_⟩
  rw [← minimalSubspaceWith_eq T hT T'' hT'' (R.retract_subset_C hx)]
  exact hAE

/-- The restriction of a tame retraction to `U ∩ r⁻¹(V)`, `V` open, is tame. -/
theorem ScRetraction.IsTameWith.restrict {R : ScRetraction E C}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (h : R.IsTameWith T) {V : Set (E 0)}
    (hV : IsOpen V) : (R.restrict hV).IsTameWith T where
  degIndex_apply x hx := h.degIndex_apply x hx.1
  exists_complement x hx hs := by
    have hx' : x ∈ E.lvlSet R.retract 1 := by
      have : E.toBase 1 x ∈ (R.restrict hV).retract := hx
      rw [R.restrict_retract] at this; exact this.1
    rw [R.scDeriv_restrict hV ((R.restrict hV).lvlSet_retract_subset 1 hx)]
    exact h.exists_complement x hx' hs

end Independence

/-! ### The derivative of an sc-operator -/

/-- The derivative of an sc-operator `L` on a domain with unique differentiability is `L₀`. -/
theorem ScOperator.scDeriv_eq {F : ScBanach} (L : ScOperator E F) {U : Set (E 0)}
    (hU : IsScDomain E U) {x : E 1} (hx : x ∈ E.lvlSet U 1) : scDeriv U (L 0) x = L 0 := by
  have h1 := ((L.isScSmooth hU).isSc1.isSc1With_scDeriv).hasFDerivWithinAt x hx
  have h2 : HasFDerivWithinAt (L 0 ∘ E.toBase 1) ((L 0).comp (E.toBase 1)) (E.lvlSet U 1) x :=
    ((L 0).comp (E.toBase 1)).hasFDerivWithinAt
  have h := (hU.uniqueDiffWithinAt_one x hx).eq h1 h2
  have hd : Dense (Submodule.span ℝ (range (E.toBase 1)) : Set (E 0)) :=
    Dense.mono Submodule.subset_span (E.denseRange_inclK 0 1)
  refine ContinuousLinearMap.ext_on hd ?_
  rintro _ ⟨y, rfl⟩
  exact congrArg (fun L' : E 1 →L[ℝ] F 0 => L' y) h

/-! ### The extended face `f_i ≅ ℝᵏ ⊕ W` -/

section FaceModel

variable {k : ℕ} {W : ScBanach}

/-- `b ↦ (b₁, …, 0_i, …, b_k)`, inserting a zero coordinate at position `i`: `ℝᵏ → ℝᵏ⁺¹`. -/
def insertCoordL (i : Fin (k + 1)) : (Fin k → ℝ) →L[ℝ] (Fin (k + 1) → ℝ) :=
  ContinuousLinearMap.pi fun l =>
    Fin.insertNth (α := fun _ => (Fin k → ℝ) →L[ℝ] ℝ) i 0 (fun j => ContinuousLinearMap.proj j) l

lemma insertCoordL_apply_self (i : Fin (k + 1)) (b : Fin k → ℝ) : insertCoordL i b i = 0 := by
  simp [insertCoordL]

lemma insertCoordL_apply_succAbove (i : Fin (k + 1)) (b : Fin k → ℝ) (j : Fin k) :
    insertCoordL i b (i.succAbove j) = b j := by
  simp [insertCoordL]

/-- `a ↦ (a_l)_{l ≠ i}`, deleting the `i`-th coordinate: `ℝᵏ⁺¹ → ℝᵏ`. -/
def removeCoordL (i : Fin (k + 1)) : (Fin (k + 1) → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (i.succAbove j)

@[simp] lemma removeCoordL_apply (i : Fin (k + 1)) (a : Fin (k + 1) → ℝ) (j : Fin k) :
    removeCoordL i a j = a (i.succAbove j) := rfl

/-- The sc-operator `(b, w) ↦ (insert 0 at i in b, w)`, `ℝᵏ ⊕ W → ℝᵏ⁺¹ ⊕ W`. -/
def insertCoordModel (W : ScBanach) (i : Fin (k + 1)) :
    ScOperator ((ScBanach.const (Fin k → ℝ)).prod W)
      ((ScBanach.const (Fin (k + 1) → ℝ)).prod W) where
  lvl m := (insertCoordL i).prodMap (ContinuousLinearMap.id ℝ (W m))
  incl_comm _ _ := rfl

/-- The sc-operator `(a, w) ↦ ((a_l)_{l ≠ i}, w)`, `ℝᵏ⁺¹ ⊕ W → ℝᵏ ⊕ W`. -/
def removeCoordModel (W : ScBanach) (i : Fin (k + 1)) :
    ScOperator ((ScBanach.const (Fin (k + 1) → ℝ)).prod W)
      ((ScBanach.const (Fin k → ℝ)).prod W) where
  lvl m := (removeCoordL i).prodMap (ContinuousLinearMap.id ℝ (W m))
  incl_comm _ _ := rfl

variable (T : ScIso E ((ScBanach.const (Fin (k + 1) → ℝ)).prod W)) (i : Fin (k + 1))

/-- The inclusion `ι : ℝᵏ ⊕ W ≅ f_i ⊆ E` of the extended face `f_i = {λ_i = 0}`, an sc-operator
(the text's identification `f_1 = E_1 ≅ ℝᵏ⁻¹ ⊕ W` in the proof of Proposition 2.43). -/
def faceIncl : ScOperator ((ScBanach.const (Fin k → ℝ)).prod W) E :=
  T.symm.toScOperator.comp (insertCoordModel W i)

/-- The projection `π : E → ℝᵏ ⊕ W`, `π = ι⁻¹ ∘ P_i`, an sc-operator. -/
def faceProj : ScOperator E ((ScBanach.const (Fin k → ℝ)).prod W) :=
  (removeCoordModel W i).comp T.toScOperator

lemma faceIncl_apply (z : ((ScBanach.const (Fin k → ℝ)).prod W) 0) :
    faceIncl T i 0 z = (T 0).symm (insertCoordL i z.1, z.2) := rfl

lemma faceProj_apply (y : E 0) : faceProj T i 0 y = (removeCoordL i (T 0 y).1, (T 0 y).2) := rfl

lemma coord_faceIncl_self (z : ((ScBanach.const (Fin k → ℝ)).prod W) 0) :
    (T 0 (faceIncl T i 0 z)).1 i = 0 := by
  rw [faceIncl_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact insertCoordL_apply_self i z.1

lemma coord_faceIncl_succAbove (z : ((ScBanach.const (Fin k → ℝ)).prod W) 0) (j : Fin k) :
    (T 0 (faceIncl T i 0 z)).1 (i.succAbove j) = z.1 j := by
  rw [faceIncl_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact insertCoordL_apply_succAbove i z.1 j

lemma faceProj_faceIncl (z : ((ScBanach.const (Fin k → ℝ)).prod W) 0) :
    faceProj T i 0 (faceIncl T i 0 z) = z := by
  rw [faceProj_apply]
  refine Prod.ext (funext fun j => ?_) ?_
  · exact coord_faceIncl_succAbove T i z j
  · change (T 0 ((T 0).symm (insertCoordL i z.1, z.2))).2 = z.2
    rw [ContinuousLinearEquiv.apply_symm_apply]

lemma faceIncl_faceProj {y : E 0} (hy : (T 0 y).1 i = 0) :
    faceIncl T i 0 (faceProj T i 0 y) = y := by
  apply (T 0).injective
  rw [faceIncl_apply, ContinuousLinearEquiv.apply_symm_apply]
  refine Prod.ext (funext fun l => ?_) rfl
  change insertCoordL i (removeCoordL i (T 0 y).1) l = (T 0 y).1 l
  refine Fin.succAboveCases i ?_ (fun j => ?_) l
  · rw [insertCoordL_apply_self, hy]
  · rw [insertCoordL_apply_succAbove, removeCoordL_apply]

variable {C : Set (E 0)}

lemma faceIncl_mem (hT : C = T 0 ⁻¹' quadrant (k + 1) W 0)
    {z : ((ScBanach.const (Fin k → ℝ)).prod W) 0} (hz : z ∈ quadrant k W 0) :
    faceIncl T i 0 z ∈ C := by
  rw [hT]; intro l
  change 0 ≤ (T 0 (faceIncl T i 0 z)).1 l
  refine Fin.succAboveCases i ?_ (fun j => ?_) l
  · rw [coord_faceIncl_self]
  · rw [coord_faceIncl_succAbove]; exact hz j

lemma faceProj_mem (hT : C = T 0 ⁻¹' quadrant (k + 1) W 0) {y : E 0} (hy : y ∈ C) :
    faceProj T i 0 y ∈ quadrant k W 0 := fun j => coord_nonneg hT hy (i.succAbove j)

/-- On `f_i`, `d_C(y) = d_{C'}(π y) + 1` (the extended faces of `C' = [0,∞)ᵏ ⊕ W` are the
`f_j ∩ f_i`, `j ≠ i`). -/
lemma degIndexWith_eq_quadrantDeg_faceProj_add_one {y : E 0} (hy : (T 0 y).1 i = 0) :
    degIndexWith T y = quadrantDeg (faceProj T i 0 y) + 1 := by
  classical
  rw [degIndexWith, quadrantDeg, quadrantDeg, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_succAbove _ i, if_pos hy, add_comm]
  rfl

end FaceModel

/-- The chain rule at a level-`1` point, for sc¹ maps between arbitrary sc-domains. -/
lemma scDeriv_comp_apply_of_isScDomain {F G : ScBanach} {U : Set (E 0)} {V : Set (F 0)}
    {f : E 0 → F 0} {g : F 0 → G 0} (hU : IsScDomain E U) (hV : IsScDomain F V) (hf : IsSc1 U f)
    (hg : IsSc1 V g) (hfV : MapsTo f U V) {x : E 1} (hx : x ∈ E.lvlSet U 1) (h : E 0) :
    scDeriv V g (levelMap f 1 x) (scDeriv U f x h) = scDeriv U (g ∘ f) x h := by
  obtain ⟨_, hchain⟩ := theorem_1_21' hU hV hf hg hfV
  have := hchain (show ((x, h) : E.tangent 0) ∈ E.tangentSet U from hx)
  exact (congrArg Prod.snd this).symm

/-! ### Proposition 2.43: the tame model `(F, C ∩ f_i, f_i)` of a face -/

section Prop243Tame

variable {k : ℕ} {W : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}
  {T : ScIso E ((ScBanach.const (Fin (k + 1) → ℝ)).prod W)}

/-- **Proposition 2.43**, the tame model of a face: let `r : U → U` be a tame retraction onto `O`
and `F ⊆ f_i` a face of `O`.  With `E' = f_i ≅ ℝᵏ ⊕ W` (through `ι = faceIncl T i`,
`π = faceProj T i`) and `C' = C ∩ f_i ≅ [0,∞)ᵏ ⊕ W`, the map `r' = π ∘ r ∘ ι` on
`U' = ι⁻¹(U*)` (`U*` the neighbourhood of `F` of `proposition_2_43`) is a **tame** sc-smooth
retraction onto `π(F)`.

*Proof* (exposition §4.3).  `r'` is a retraction onto `π(F)` since `r ∘ ι` maps `U'` into
`F ⊆ f_i`, where `ι ∘ π = 1`.  Tameness (1): `d_C = d_{C'} ∘ π + 1` on `f_i` and `d_C ∘ r = d_C`.
Tameness (2): `λ'_j ∘ Dr'(x) = λ_{j'} ∘ Dr(ι x) ∘ ι = λ_{j'} ∘ ι = λ'_j` for `j ∈ I'(x)`, where
`j' = i.succAbove j ∈ I(ι x)`, by Proposition 2.35 (`coord_scDeriv_eq`); so
`(1 − Dr'(x))E' ⊆ E'_x` is an sc-complement of `T_x O'`. -/
theorem proposition_2_43_tameModel (hT : C = T 0 ⁻¹' quadrant (k + 1) W 0) (hR : R.IsTameWith T)
    {F : Set (E 0)} (hF : R.IsRetractFace F) :
    ∃ i : Fin (k + 1), F ⊆ coordHyper T i ∧
      ∃ R' : ScRetraction ((ScBanach.const (Fin k → ℝ)).prod W) (quadrant k W 0),
        R'.IsTameWith (ScIso.refl _) ∧ R'.retract = faceProj T i 0 '' F ∧
        ∀ y ∈ F, degIndex _ (quadrant k W 0) (faceProj T i 0 y) + 1 = degIndex E C y := by
  classical
  have hFO : F ⊆ R.retract := by obtain ⟨_, _, rfl⟩ := hF; exact inter_subset_right
  obtain ⟨i, hFi, S, hFS, hSU, hSret, hSeq⟩ := proposition_2_43 hT hR hF
  refine ⟨i, hFi, ?_⟩
  obtain ⟨W₀, hW₀, hSW⟩ := S.relOpen.relOpen
  set E' := (ScBanach.const (Fin k → ℝ)).prod W with hE'
  set ι := faceIncl T i with hι
  set π := faceProj T i with hπ
  have hT' : quadrant k W 0 = (ScIso.refl E') 0 ⁻¹' quadrant k W 0 := by ext; rfl
  have hιC : ∀ z ∈ quadrant k W 0, ι 0 z ∈ C := fun z hz => faceIncl_mem T i hT hz
  have hPι : ∀ z, killCoord T i 0 (ι 0 z) = ι 0 z := fun z =>
    killCoord_eq_self (coord_faceIncl_self T i z)
  set U' : Set (E' 0) := ι 0 ⁻¹' W₀ ∩ quadrant k W 0 with hU'
  have hιU : ∀ z ∈ U', ι 0 z ∈ S.U := fun z hz => by rw [hSW]; exact ⟨hz.1, hιC z hz.2⟩
  have hmapsR : MapsTo (ι 0) U' R.U := fun z hz => hSU (hιU z hz)
  have hRιF : ∀ z ∈ U', R (ι 0 z) ∈ F := fun z hz => by
    have := S.apply_mem_retract (hιU z hz)
    rwa [hSret, hSeq (hιU z hz), Function.comp_apply, hPι] at this
  have hιπ : ∀ y ∈ F, ι 0 (π 0 y) = y := fun y hy => faceIncl_faceProj T i (hFi hy)
  have hFU' : ∀ y ∈ F, π 0 y ∈ U' := fun y hy => by
    have hyS := hFS hy
    rw [hSW] at hyS
    refine ⟨?_, faceProj_mem T i hT hyS.2⟩
    rw [mem_preimage, hιπ y hy]; exact hyS.1
  have hU'rel : IsRelOpenInQuadrant E' (quadrant k W 0) U' :=
    ⟨⟨k, W, ScIso.refl E', hT'⟩, ι 0 ⁻¹' W₀, hW₀.preimage (ι 0).continuous, rfl⟩
  have hsm : IsScSmooth U' (π 0 ∘ (R ∘ ι 0)) :=
    IsScSmooth.comp hU'rel.isScDomain (isScDomain_univ _) (π.isScSmooth (isScDomain_univ _))
      (IsScSmooth.comp hU'rel.isScDomain R.isScDomain R.isScSmooth
        (ι.isScSmooth hU'rel.isScDomain) hmapsR) (mapsTo_univ _ _)
  let R' : ScRetraction E' (quadrant k W 0) :=
    { U := U'
      toFun := fun z => π 0 (R (ι 0 z))
      relOpen := hU'rel
      mapsTo := fun z hz => hFU' _ (hRιF z hz)
      isScSmooth := hsm
      idem := fun z hz => by
        change π 0 (R (ι 0 (π 0 (R (ι 0 z))))) = π 0 (R (ι 0 z))
        rw [hιπ _ (hRιF z hz), R.apply_eq_self_of_mem_retract (hFO (hRιF z hz))] }
  have hR'ret : R'.retract = π 0 '' F := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩; exact ⟨_, hRιF z hz, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨π 0 y, hFU' y hy, ?_⟩
      change π 0 (R (ι 0 (π 0 y))) = π 0 y
      rw [hιπ y hy, R.apply_eq_self_of_mem_retract (hFO hy)]
  have hιret : ∀ w ∈ R'.retract, ι 0 w ∈ F := by
    rw [hR'ret]; rintro _ ⟨y, hy, rfl⟩; rw [hιπ y hy]; exact hy
  refine ⟨R', ⟨fun z hz => ?_, fun x hx hs => ?_⟩, hR'ret, fun y hy => ?_⟩
  · -- tameness (1)
    have hzq : z ∈ quadrant k W 0 := hz.2
    have hz'q : R' z ∈ quadrant k W 0 := (R'.mapsTo hz).2
    rw [degIndex_eq (ScIso.refl E') hT' hz'q, degIndex_eq (ScIso.refl E') hT' hzq]
    change quadrantDeg (π 0 (R (ι 0 z))) = quadrantDeg z
    have h1 := degIndexWith_eq_quadrantDeg_faceProj_add_one T i (hFi (hRιF z hz))
    have h2 := degIndexWith_eq_quadrantDeg_faceProj_add_one T i (coord_faceIncl_self T i z)
    rw [faceProj_faceIncl] at h2
    have h3 := hR.degIndex_apply _ (hmapsR hz)
    rw [degIndex_eq T hT (R.retract_subset_C (hFO (hRιF z hz))),
      degIndex_eq T hT (hιC z hzq)] at h3
    exact Nat.add_right_cancel (h1.symm.trans (h3.trans h2))
  · -- tameness (2)
    set D := scDeriv R'.U R' x with hD
    have hx1U : x ∈ E'.lvlSet U' 1 := R'.lvlSet_retract_subset 1 hx
    have hy : ι 1 x ∈ E.lvlSet R.retract 1 := by
      rw [ScBanach.mem_lvlSet, ι.toBase_comm]; exact hFO (hιret _ hx)
    have hys : ι 1 x ∈ E.smoothLvl 1 := ι.mapsTo_smoothLvl 1 hs
    have hyU : ι 1 x ∈ E.lvlSet R.U 1 := R.lvlSet_retract_subset 1 hy
    have hDv : ∀ v, D v = π 0 (scDeriv R.U R (ι 1 x) (ι 0 v)) := fun v => by
      have c1 := scDeriv_comp_apply_of_isScDomain hU'rel.isScDomain R.isScDomain
        (ι.isScSmooth hU'rel.isScDomain).isSc1
        (IsScSmooth.comp R.isScDomain (isScDomain_univ _) (π.isScSmooth (isScDomain_univ _))
          R.isScSmooth (mapsTo_univ _ _)).isSc1 hmapsR hx1U v
      have c2 := scDeriv_comp_apply_of_isScDomain R.isScDomain (isScDomain_univ _) R.isSc1
        (π.isScSmooth (isScDomain_univ _)).isSc1 (mapsTo_univ _ _) hyU (ι 0 v)
      rw [ι.scDeriv_eq hU'rel.isScDomain hx1U, ι.levelMap_eq] at c1
      rw [π.scDeriv_eq (isScDomain_univ _) (mem_univ _)] at c2
      change scDeriv U' ((π 0 ∘ R) ∘ ι 0) x v = _
      rw [← c1, ← c2]
    refine ⟨_, R'.isScSplitting_range_scDeriv hx hs, ?_⟩
    rintro _ ⟨v, rfl⟩
    rw [mem_minimalSubspaceWith]
    intro j hj
    change (v - D v).1 j = 0
    have hj' : (T 0 (E.toBase 1 (ι 1 x))).1 (i.succAbove j) = 0 := by
      rw [ι.toBase_comm, hι, coord_faceIncl_succAbove]; exact hj
    have key := coord_scDeriv_eq hT hR hy hys hj' (ι 0 v)
    rw [hι, coord_faceIncl_succAbove] at key
    rw [Prod.fst_sub, Pi.sub_apply, hDv v, hπ, faceProj_apply]
    change v.1 j - (T 0 (scDeriv R.U R (faceIncl T i 1 x) (faceIncl T i 0 v))).1 (i.succAbove j) = 0
    rw [key, sub_self]
  · -- `d_F = d_O − 1`
    have hyC := R.retract_subset_C (hFO hy)
    rw [degIndex_eq (ScIso.refl E') hT' (faceProj_mem T i hT hyC), degIndex_eq T hT hyC,
      degIndexWith_eq_quadrantDeg_faceProj_add_one T i (hFi hy)]
    rfl

end Prop243Tame

/-! ### The chart `π ∘ φ : A ∩ V₁ → π(φ(A ∩ V₁))` of a face -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

section FaceChart

variable {A : Set X} (x₀ : A) (φ : MChart X) (V₁ : Set X) {E' : ScBanach} (C' : Set (E' 0))
  (ι : ScOperator E' φ.model.E) (π : ScOperator φ.model.E E')

open scoped Classical in
/-- The inverse `π(φ(A ∩ V₁)) → A` of the chart of a face, with the junk value `x₀`. -/
def faceChartInv (z : E' 0) : A :=
  if h : ∃ y : A, (y : X) ∈ V₁ ∧ φ y = ι 0 z then h.choose else x₀

omit [T2Space X] [ParacompactSpace X] in
lemma faceChartInv_spec (hιπ : ∀ y ∈ φ '' (A ∩ V₁), ι 0 (π 0 y) = y) {z : E' 0}
    (hz : z ∈ π 0 '' (φ '' (A ∩ V₁))) :
    ((faceChartInv x₀ φ V₁ ι z : A) : X) ∈ V₁ ∧ φ (faceChartInv x₀ φ V₁ ι z : X) = ι 0 z := by
  obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hz
  have h : ∃ y' : A, (y' : X) ∈ V₁ ∧ φ y' = ι 0 (π 0 (φ y)) :=
    ⟨⟨y, hy.1⟩, hy.2, (hιπ _ ⟨y, hy, rfl⟩).symm⟩
  unfold faceChartInv
  rw [dif_pos h]; exact h.choose_spec

/-- The chart `π ∘ φ : A ∩ V₁ → π(φ(A ∩ V₁)) ⊆ E'` of a subset `A ⊆ X`, for a chart `φ` of `X`,
an open `V₁ ⊆ V` and sc-operators `ι, π` with `ι ∘ π = 1` on `φ(A ∩ V₁)` and `π ∘ ι = 1` (the
text's chart `(F, id, (F, C', E'))` in the proof of Proposition 2.43, transported by `φ`). -/
def faceChart (hV₁ : IsOpen V₁) (hV₁φ : V₁ ⊆ φ.source)
    (hιπ : ∀ y ∈ φ '' (A ∩ V₁), ι 0 (π 0 y) = y) (hπι : ∀ z, π 0 (ι 0 z) = z)
    (hret : IsScRetract E' C' (π 0 '' (φ '' (A ∩ V₁)))) : MChart A where
  model := ⟨E', C', π 0 '' (φ '' (A ∩ V₁)), hret⟩
  toPartialEquiv :=
    { toFun := fun y => π 0 (φ y)
      invFun := faceChartInv x₀ φ V₁ ι
      source := {y | (y : X) ∈ V₁}
      target := π 0 '' (φ '' (A ∩ V₁))
      map_source' := fun y hy => ⟨φ y, ⟨y, ⟨y.2, hy⟩, rfl⟩, rfl⟩
      map_target' := fun _ hz => (faceChartInv_spec x₀ φ V₁ ι π hιπ hz).1
      left_inv' := fun y hy => by
        have hz : π 0 (φ y) ∈ π 0 '' (φ '' (A ∩ V₁)) := ⟨φ y, ⟨y, ⟨y.2, hy⟩, rfl⟩, rfl⟩
        obtain ⟨h1, h2⟩ := faceChartInv_spec x₀ φ V₁ ι π hιπ hz
        rw [hιπ _ ⟨y, ⟨y.2, hy⟩, rfl⟩] at h2
        apply Subtype.ext
        have := congrArg φ.symm h2
        rwa [φ.symm_apply_apply (hV₁φ h1), φ.symm_apply_apply (hV₁φ hy)] at this
      right_inv' := fun z hz => by
        change π 0 (φ (faceChartInv x₀ φ V₁ ι z : X)) = z
        rw [(faceChartInv_spec x₀ φ V₁ ι π hιπ hz).2]
        obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hz
        rw [hπι] }
  isOpen_source := hV₁.preimage continuous_subtype_val
  target_eq := rfl
  continuousOn_toFun := (π 0).continuous.comp_continuousOn
    (φ.continuousOn_toFun.comp continuous_subtype_val.continuousOn fun _ hy => hV₁φ hy)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hO : MapsTo (ι 0) (π 0 '' (φ '' (A ∩ V₁))) φ.model.O := fun z hz => by
      rw [← (faceChartInv_spec x₀ φ V₁ ι π hιπ hz).2]
      exact φ.mapsTo_model _ (hV₁φ (faceChartInv_spec x₀ φ V₁ ι π hιπ hz).1)
    refine (φ.continuousOn_invFun.comp (ι 0).continuous.continuousOn hO).congr fun z hz => ?_
    obtain ⟨h1, h2⟩ := faceChartInv_spec x₀ φ V₁ ι π hιπ hz
    change (faceChartInv x₀ φ V₁ ι z : X) = φ.symm (ι 0 z)
    rw [← h2, φ.symm_apply_apply (hV₁φ h1)]

variable {x₀ φ V₁ C' ι π}

/-- The chart of a face is compatible with the sub-charts of `A` built on `φ` (Proposition 2.21):
the transition maps are the sc-operators `ι` and `π`. -/
theorem faceChart_compatible_subChart (hφ : P.IsChart φ) (hV₁ : IsOpen V₁) (hV₁φ : V₁ ⊆ φ.source)
    (hιπ : ∀ y ∈ φ '' (A ∩ V₁), ι 0 (π 0 y) = y) (hπι : ∀ z, π 0 (ι 0 z) = z)
    (hret : IsScRetract E' C' (π 0 '' (φ '' (A ∩ V₁)))) (d : P.SubData A) (b₀ : A) :
    (faceChart x₀ φ V₁ C' ι π hV₁ hV₁φ hιπ hπι hret).Compatible (subChart d hφ b₀) := by
  set χ := faceChart x₀ φ V₁ C' ι π hV₁ hV₁φ hιπ hπι hret with hχdef
  set τ := subChart d hφ b₀
  have hτ : ∀ y : A, τ y = φ y := fun _ => rfl
  have hχ : ∀ y : A, χ y = π 0 (φ y) := fun _ => rfl
  have hιχ : ∀ y : A, y ∈ χ.source → ι 0 (χ y) = τ y := fun y hy => by
    rw [hχ, hτ, hιπ _ ⟨y, ⟨y.2, hy⟩, rfl⟩]
  constructor
  · refine (ι.isScSmoothRetractMap (χ.isScRetract_overlap τ) ?_).congr ?_
    · rintro _ ⟨y, hy, rfl⟩
      rw [hιχ y hy.1]; exact ⟨y, ⟨hy.2, hy.1⟩, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [χ.transition_apply τ hy.1, hιχ y hy.1]
  · refine (π.isScSmoothRetractMap (τ.isScRetract_overlap χ) ?_).congr ?_
    · rintro _ ⟨y, hy, rfl⟩
      rw [hτ, ← hχ]; exact ⟨y, ⟨hy.2, hy.1⟩, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [τ.transition_apply χ hy.1, hτ, hχ]

end FaceChart

/-- A chart of a sub-M-polyfold `A` that is compatible with the sub-charts built on one chart `φ`
of `X` (whose domain contains the chart's) is a chart of the induced structure (locality of
compatibility). -/
theorem isChart_subPolyfold_of_compatible {A : Set X} [ParacompactSpace A]
    (hA : P.IsSubMPolyfold A) {χ : MChart A} {φ : MChart X} (hφ : P.IsChart φ)
    (hsrc : ∀ y ∈ χ.source, (y : X) ∈ φ.source)
    (h : ∀ (d : P.SubData A) (b₀ : A), χ.Compatible (subChart d hφ b₀)) :
    (subPolyfold hA).IsChart χ := by
  rintro _ ⟨d, ψ, hψ, a₀, rfl⟩
  refine MChart.compatible_of_locally _ _
    {τ | ∃ (d' : P.SubData A) (b₀ : A), τ = subChart d' hφ b₀} ?_ ?_ ?_
  · rintro _ ⟨d', b₀, rfl⟩; exact h d' b₀
  · rintro _ ⟨d', b₀, rfl⟩; exact subChart_compatible d' hφ b₀ d hψ a₀
  · intro y hy
    exact ⟨_, ⟨hA.data y.2, y, rfl⟩,
      (hA.data y.2).mem_shrink φ y.2 (hA.mem_data_V y.2) (hsrc y hy.1)⟩

variable (P) in
/-- `X` is tame (Definition 2.37) as soon as every point lies in the domain of a chart of the
structure modelled on a tame retract (the atlas of all such charts is equivalent). -/
theorem isTame_of_forall_exists_chart (h : ∀ x : X, ∃ φ : MChart X, P.IsChart φ ∧
    x ∈ φ.source ∧ IsTameRetract φ.model.E φ.model.C φ.model.O) : P.IsTame := by
  let A : MAtlas X :=
    { charts := {φ | P.IsChart φ ∧ IsTameRetract φ.model.E φ.model.C φ.model.O}
      compatible := fun φ hφ ψ hψ => IsChart.compatible P hφ.1 hψ.1
      cover := fun x => by
        obtain ⟨φ, hφ, hx, ht⟩ := h x
        exact ⟨φ, ⟨hφ, ht⟩, hx⟩ }
  exact ⟨A, (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => hφ.1 ψ hψ, fun φ hφ => hφ.2⟩

end MPolyfold

/-! ### Proposition 2.43: a face is a tame M-polyfold with `d_F = d_O − 1` -/

namespace LocalModel

variable (M : LocalModel) (hne : M.O.Nonempty) {n : ℕ} {W : ScBanach}
  (R : ScRetraction M.E M.C) (hRM : R.retract = M.O)
  {T : ScIso M.E ((ScBanach.const (Fin n → ℝ)).prod W)}

include hRM in
/-- **Proposition 2.43**, last statements: a face `F` of a tame retract `O`, with the M-polyfold
structure of a sub-M-polyfold (Proposition 2.21, via `isSubMPolyfold_of_isFace`), is **tame**, and
`d_F(x) = d_O(x) − 1` for all `x ∈ F` (stated as `d_F(x) + 1 = d_O(x)`).

*Proof.* The chart `π : F → π(F)` (`MPolyfold.faceChart`, with `φ = id`) onto the tame retract
`(π(F), C', E')` of `proposition_2_43_tameModel` is compatible with the sub-charts of `F` built on
the identity chart of `O` (its transition maps are the sc-operators `ι`, `π`), hence it is a chart
of the induced structure; its model is tame.  The tame chart realizes `d_F`
(`degIndex_eq_chartDegIndex_of_isTameWith`), and `d_{C'}(π y) + 1 = d_C(y) = d_O(y)` (equation
(4.2) twice).  Paracompactness of `F` (needed for Proposition 2.21) holds since faces are
closed. -/
theorem proposition_2_43_isTame (hT : M.C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T)
    {F : Set M.O} (hF : (M.toMPolyfold hne).IsFace F) :
    haveI : ParacompactSpace F :=
      MPolyfold.paracompactSpace_of_isClosed (MPolyfold.IsFace.isClosed _ hF)
    (MPolyfold.subPolyfold (M.isSubMPolyfold_of_isFace hne R hRM hT hR hF)).IsTame ∧
      ∀ x : F, (MPolyfold.subPolyfold (M.isSubMPolyfold_of_isFace hne R hRM hT hR hF)).degIndex x
        + 1 = (M.toMPolyfold hne).degIndex x.1 := by
  classical
  have : ParacompactSpace F :=
    MPolyfold.paracompactSpace_of_isClosed (MPolyfold.IsFace.isClosed _ hF)
  have hG := (M.isFace_toMPolyfold_iff hne R hRM hT hR F).1 hF
  obtain ⟨i₀, -⟩ := proposition_2_43 hT hR hG
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := i₀.pos; omega⟩
  obtain ⟨i, hFi, R', hR'tame, hR'ret, hdeg⟩ := proposition_2_43_tameModel hT hR hG
  have hsub := M.isSubMPolyfold_of_isFace hne R hRM hT hR hF
  have hT' : quadrant k W 0 = (ScIso.refl ((ScBanach.const (Fin k → ℝ)).prod W)) 0 ⁻¹'
      quadrant k W 0 := by ext; rfl
  obtain ⟨x₀⟩ : Nonempty F := by
    obtain ⟨x, hx1, hFeq⟩ := hF
    exact ⟨⟨x, hFeq ▸ subset_closure (mem_connectedComponentIn hx1)⟩⟩
  set σ := M.selfChart hne
  have hιπ : ∀ y ∈ σ '' (F ∩ univ), faceIncl T i 0 (faceProj T i 0 y) = y := by
    rintro _ ⟨x, hx, rfl⟩; exact faceIncl_faceProj T i (hFi ⟨x, hx.1, rfl⟩)
  have hπι := faceProj_faceIncl T i
  have hR'O' : R'.retract = faceProj T i 0 '' (σ '' (F ∩ univ)) := by
    rw [hR'ret, inter_univ]; rfl
  have hret : IsScRetract _ (quadrant k W 0) (faceProj T i 0 '' (σ '' (F ∩ univ))) :=
    ⟨R', hR'O'⟩
  have hσ := (M.toMPolyfold hne).isChart_of_mem (mem_singleton σ)
  set χ := MPolyfold.faceChart x₀ σ univ (quadrant k W 0) (faceIncl T i) (faceProj T i)
    isOpen_univ (fun _ _ => mem_univ _) hιπ hπι hret with hχ
  have hχQ : (MPolyfold.subPolyfold hsub).IsChart χ :=
    MPolyfold.isChart_subPolyfold_of_compatible hsub hσ (fun _ _ => mem_univ _) fun d b₀ =>
      MPolyfold.faceChart_compatible_subChart hσ isOpen_univ (fun _ _ => mem_univ _) hιπ hπι
        hret d b₀
  have hR'O : R'.retract = χ.model.O := hR'O'
  refine ⟨MPolyfold.isTame_of_forall_exists_chart _ fun x =>
    ⟨χ, hχQ, mem_univ (x : M.O), ⟨R', hR'O, hR'tame.isTame hT'⟩⟩, fun x => ?_⟩
  rw [(MPolyfold.subPolyfold hsub).degIndex_eq_chartDegIndex_of_isTameWith hχQ R' hR'O hT'
      hR'tame (mem_univ (x : M.O)), M.degIndex_toMPolyfold_of_isTameWith hne R hRM hT hR x.1]
  exact hdeg _ ⟨x.1, x.2, rfl⟩

end LocalModel

/-! ### A local criterion for sub-M-polyfolds -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **A local criterion for sub-M-polyfolds** (the argument of Theorem 2.45, "transport by
`φ⁻¹`"): if near every `a ∈ A`, in a chart `φ : V → O`, the image `φ(A ∩ V)` agrees on an open
set `B ∋ φ(a)` with an sc-smooth retract `s(U_s) ⊆ O` of `C`, then `A` is a sub-M-polyfold of `X`
(Definition 2.20), with the retraction `φ⁻¹ ∘ s ∘ φ` near `a`. -/
theorem isSubMPolyfold_of_local {A : Set X}
    (h : ∀ a ∈ A, ∃ φ : MChart X, P.IsChart φ ∧ a ∈ φ.source ∧
      ∃ (S : ScRetraction φ.model.E φ.model.C) (B : Set (φ.model.E 0)), IsOpen B ∧ φ a ∈ B ∧
        S.retract ⊆ φ.model.O ∧ S.retract ∩ B = φ '' (A ∩ φ.source) ∩ B) :
    P.IsSubMPolyfold A := by
  classical
  intro a haA
  obtain ⟨φ, hφ, haφ, S, B, hB, haB, hSO, hSA⟩ := h a haA
  obtain ⟨W₀, hW₀, hSW⟩ := S.relOpen.relOpen
  obtain ⟨Ws, hWs, hWseq⟩ := continuousOn_iff'.1 S.isSc1.isSc0.continuousOn_base B hB
  set W₁ := B ∩ W₀ ∩ Ws with hW₁def
  have hW₁ : IsOpen W₁ := (hB.inter hW₀).inter hWs
  have hOC : φ.model.O ⊆ φ.model.C := φ.model.O_subset_C
  have hU : ∀ z ∈ φ.model.O, z ∈ W₀ → z ∈ S.U := fun z hz hzW => by
    rw [hSW]; exact ⟨hzW, hOC hz⟩
  set V' := φ.source ∩ φ ⁻¹' W₁ with hV'def
  have hV' : IsOpen V' := φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source hW₁
  -- the basic facts at a point of `V'`
  have hφU : ∀ x ∈ V', φ x ∈ S.U := fun x hx =>
    hU _ (φ.mapsTo_model x hx.1) hx.2.1.2
  have hSB : ∀ x ∈ V', S (φ x) ∈ B := fun x hx => by
    have : φ x ∈ S ⁻¹' B ∩ S.U := by rw [hWseq]; exact ⟨hx.2.2, hφU x hx⟩
    exact this.1
  have hSret : ∀ x ∈ V', S (φ x) ∈ S.retract := fun x hx => S.apply_mem_retract (hφU x hx)
  have hSW₁ : ∀ x ∈ V', S (φ x) ∈ W₁ := fun x hx => by
    have hUs : S (φ x) ∈ S.U := S.retract_subset (hSret x hx)
    have hSW0 : S (φ x) ∈ W₀ := by
      have := hUs; rw [hSW] at this; exact this.1
    have hfix : S (S (φ x)) = S (φ x) := S.apply_eq_self_of_mem_retract (hSret x hx)
    have hWs' : S (φ x) ∈ S ⁻¹' B ∩ S.U := ⟨by rw [mem_preimage, hfix]; exact hSB x hx, hUs⟩
    rw [hWseq] at hWs'
    exact ⟨⟨hSB x hx, hSW0⟩, hWs'.1⟩
  let r : X → X := fun x => if x ∈ V' then φ.symm (S (φ x)) else x
  have hr : ∀ x ∈ V', r x = φ.symm (S (φ x)) := fun x hx => by simp only [r, if_pos hx]
  have hφr : ∀ x ∈ V', φ (r x) = S (φ x) := fun x hx => by
    rw [hr x hx, φ.apply_symm_apply (hSO (hSret x hx))]
  have hrV : ∀ x ∈ V', r x ∈ V' := fun x hx => by
    refine ⟨?_, ?_⟩
    · rw [hr x hx]; exact φ.symm_mapsTo (hSO (hSret x hx))
    · rw [mem_preimage, hφr x hx]; exact hSW₁ x hx
  have haV : a ∈ V' := by
    have hmem : φ a ∈ S.retract ∩ B := by rw [hSA]; exact ⟨⟨a, ⟨haA, haφ⟩, rfl⟩, haB⟩
    have hUa := S.retract_subset hmem.1
    have hW0a : φ a ∈ W₀ := by have := hUa; rw [hSW] at this; exact this.1
    have hWsa : φ a ∈ S ⁻¹' B ∩ S.U := ⟨by
      rw [mem_preimage, S.apply_eq_self_of_mem_retract hmem.1]; exact haB, hUa⟩
    rw [hWseq] at hWsa
    exact ⟨haφ, ⟨haB, hW0a⟩, hWsa.1⟩
  refine ⟨V', hV', haV, r, fun x hx => hrV x hx, ?_, fun x hx => ?_, ?_⟩
  · -- sc-smoothness, in the chart `φ`
    have hcont : ContinuousOn r V' := by
      have h1 : ContinuousOn (fun x => φ.symm (S (φ x))) V' :=
        φ.continuousOn_invFun.comp (S.isSc1.isSc0.continuousOn_base.comp
          (φ.continuousOn_toFun.mono fun x hx => hx.1) fun x hx => hφU x hx)
          fun x hx => hSO (hSret x hx)
      exact h1.congr fun x hx => hr x hx
    refine IsScSmoothOn.of_exists_charts hV' hcont fun x hx => ?_
    refine ⟨φ, φ, V', hφ, hφ, hV', hx, fun z hz => ⟨hz, hz.1⟩, fun z hz => (hrV z hz).1, ?_⟩
    obtain ⟨R, hR⟩ := φ.model.isScRetract
    have himV : φ '' V' = R.retract ∩ W₁ := by
      rw [hR]
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨φ.mapsTo_model w hw.1, hw.2⟩
      · rintro ⟨hzO, hzW⟩
        exact ⟨φ.symm z, ⟨φ.symm_mapsTo hzO, by
          rw [mem_preimage, φ.apply_symm_apply hzO]; exact hzW⟩, φ.apply_symm_apply hzO⟩
    rw [himV]
    have hret : IsScRetract φ.model.E φ.model.C (R.retract ∩ W₁) :=
      ⟨R.restrict hW₁, R.restrict_retract hW₁⟩
    have heq : ∀ z ∈ R.retract ∩ W₁, (φ ∘ r ∘ φ.symm) z = S z := fun z hz => by
      have hzO : z ∈ φ.model.O := by rw [← hR]; exact hz.1
      have hzV : φ.symm z ∈ V' := ⟨φ.symm_mapsTo hzO, by
        rw [mem_preimage, φ.apply_symm_apply hzO]; exact hz.2⟩
      simp only [Function.comp_apply]
      rw [hφr _ hzV, φ.apply_symm_apply hzO]
    have hUz : ∀ z ∈ R.retract ∩ W₁, z ∈ S.U := fun z hz =>
      hU z (by rw [← hR]; exact hz.1) hz.2.1.2
    refine (isScSmoothRetractMap_iff_exists hret).2
      ⟨fun z hz => ?_, R.restrict hW₁, R.restrict_retract hW₁, ?_⟩
    · rw [heq z hz]; exact hSO (S.apply_mem_retract (hUz z hz))
    · have hmaps : MapsTo (R.restrict hW₁) (R.restrict hW₁).U S.U := fun w hw => by
        have := (R.restrict hW₁).apply_mem_retract hw
        rw [R.restrict_retract hW₁] at this
        exact hUz _ this
      have h1 : IsScSmooth (R.restrict hW₁).U (S ∘ R.restrict hW₁) :=
        IsScSmooth.comp (R.restrict hW₁).isScDomain S.isScDomain S.isScSmooth
          (R.restrict hW₁).isScSmooth hmaps
      refine h1.congr (R.restrict hW₁).isScDomain fun w hw => ?_
      have := (R.restrict hW₁).apply_mem_retract hw
      rw [R.restrict_retract hW₁] at this
      exact (heq _ this).symm
  · -- `r ∘ r = r`
    rw [hr _ (hrV x hx), hφr x hx, S.apply_eq_self_of_mem_retract (hSret x hx), ← hr x hx]
  · -- `r(V') = A ∩ V'`
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, hrV x hx⟩
      have hmem : S (φ x) ∈ S.retract ∩ B := ⟨hSret x hx, hSB x hx⟩
      rw [hSA] at hmem
      obtain ⟨⟨a', ⟨ha'A, ha'φ⟩, ha'⟩, -⟩ := hmem
      rw [hr x hx, ← ha', φ.symm_apply_apply ha'φ]; exact ha'A
    · rintro ⟨hyA, hyV⟩
      refine ⟨y, hyV, ?_⟩
      have hmem : φ y ∈ φ '' (A ∩ φ.source) ∩ B := ⟨⟨y, ⟨hyA, hyV.1⟩, rfl⟩, hyV.2.1.1⟩
      rw [← hSA] at hmem
      rw [hr y hyV, S.apply_eq_self_of_mem_retract hmem.1, φ.symm_apply_apply hyV.1]

/-- **Theorem 2.45**, the interior of a face is a sub-M-polyfold: in a tame M-polyfold, a
connected component `G` of `{d_X = 1}` is a sub-M-polyfold of `X`.

*Proof.* At `y ∈ G`, in a tame chart `φ` with `I(φ y) = {i}`, Lemma 4.C gives a ball `B` around
`φ(y)` and the component `F̂` of `S` with: points of `O ∩ B` with `d_C = 1` lie in `F̂`, and
`φ⁻¹(F̂) ⊆ G`.  Hence `F_loc ∩ B = φ(G ∩ V) ∩ B` for the local face `F_loc = closure(F̂) ∩ O`
(both are `F̂ ∩ B`: points of `F_loc ∩ B` lie in `f_i` and have `I ⊆ {i}`), and Proposition 2.43
gives a retraction onto `F_loc`; conclude by `isSubMPolyfold_of_local`. -/
theorem theorem_2_45_isSubMPolyfold_interior (hP : P.IsTame) (y₀ : X) :
    P.IsSubMPolyfold (connectedComponentIn {y | P.degIndex y = 1} y₀) := by
  classical
  set G := connectedComponentIn {y | P.degIndex y = 1} y₀ with hG
  refine P.isSubMPolyfold_of_local fun y hyG => ?_
  have hy1 : P.degIndex y = 1 := connectedComponentIn_subset {y | P.degIndex y = 1} y₀ hyG
  obtain ⟨φ, hφ, hyV, htame⟩ := IsTame.exists_chart P hP y
  obtain ⟨R, hRO, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hR := hRt n W T hT
  have hdeg : ∀ z ∈ φ.source, P.degIndex z = degIndexWith T (φ z) := fun z hz => by
    rw [P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hz, chartDegIndex,
      degIndex_eq T hT (φ.apply_mem_C hz)]
  set o := φ y with ho
  have hoO : o ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model y hyV
  obtain ⟨i, hi⟩ := Finset.card_eq_one.1
    ((degIndexWith_eq_card_zeroSet T o).symm.trans ((hdeg y hyV).symm.trans hy1))
  have hoi : (T 0 o).1 i = 0 := by rw [← mem_zeroSet T, hi]; exact Finset.mem_singleton_self i
  obtain ⟨ε, hε, p, hpS, hpi, -, hBI, -, hB, -⟩ := local_face_structure hT hR hoO hoi
  -- points of `S` near `o` lie in `F̂ = cc S p`
  have hnear : ∀ z ∈ Metric.ball o ε ∩ R.retract, zeroSet T z = {i} →
      z ∈ connectedComponentIn R.faceStratum p := by
    rintro z ⟨hzB, hzO⟩ hzI
    have := hB z ⟨hzB, R.retract_subset_C hzO⟩ hzI
    rwa [R.apply_eq_self_of_mem_retract hzO] at this
  have hzI_of : ∀ z ∈ Metric.ball o ε ∩ R.retract, (T 0 z).1 i = 0 → zeroSet T z = {i} := by
    rintro z ⟨hzB, hzO⟩ hzi
    refine Finset.Subset.antisymm (hi ▸ hBI z ⟨hzB, R.retract_subset_C hzO⟩) ?_
    rw [Finset.singleton_subset_iff, mem_zeroSet]; exact hzi
  have hoK : o ∈ connectedComponentIn R.faceStratum p :=
    hnear o ⟨Metric.mem_ball_self hε, hoO⟩ (hzI_of o ⟨Metric.mem_ball_self hε, hoO⟩ hoi)
  have hsub : connectedComponentIn R.faceStratum p ⊆ φ.model.O := fun z hz => by
    rw [← hRO]; exact (connectedComponentIn_subset _ _ hz).1
  have hKpre : IsPreconnected (φ.symm '' connectedComponentIn R.faceStratum p) :=
    isPreconnected_connectedComponentIn.image _ (φ.continuousOn_invFun.mono hsub)
  have hKd : φ.symm '' connectedComponentIn R.faceStratum p ⊆ {y | P.degIndex y = 1} := by
    rintro _ ⟨z, hz, rfl⟩
    have hzS := connectedComponentIn_subset _ _ hz
    change P.degIndex (φ.symm z) = 1
    rw [hdeg _ (φ.symm_mapsTo (hsub hz)), φ.apply_symm_apply (hsub hz)]
    exact faceStratum_degIndexWith hT hzS
  have hyK : y ∈ φ.symm '' connectedComponentIn R.faceStratum p :=
    ⟨o, hoK, φ.symm_apply_apply hyV⟩
  have hKG : φ.symm '' connectedComponentIn R.faceStratum p ⊆ G := by
    rw [hG, connectedComponentIn_eq hyG]
    exact hKpre.subset_connectedComponentIn hyK hKd
  -- the local face and its retraction
  have hFloc : R.IsRetractFace (closure (connectedComponentIn R.faceStratum p) ∩ R.retract) :=
    ⟨p, hpS, rfl⟩
  obtain ⟨-, -, S', -, -, hS'ret, -⟩ := proposition_2_43 hT hR hFloc
  have hcl : closure (connectedComponentIn R.faceStratum p) ⊆ coordHyper T i :=
    (isClosed_coordHyper T i).closure_subset_iff.2 (connectedComponentIn_faceStratum_subset hT hpi)
  refine ⟨φ, hφ, hyV, S', Metric.ball o ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_, ?_⟩
  · rw [hS'ret, ← hRO]; exact inter_subset_right
  · rw [hS'ret]
    apply Subset.antisymm
    · rintro z ⟨⟨hzcl, hzO⟩, hzB⟩
      have hzK := hnear z ⟨hzB, hzO⟩ (hzI_of z ⟨hzB, hzO⟩ (hcl hzcl))
      have hzO' : z ∈ φ.model.O := by rw [← hRO]; exact hzO
      exact ⟨⟨φ.symm z, ⟨hKG ⟨z, hzK, rfl⟩, φ.symm_mapsTo hzO'⟩, φ.apply_symm_apply hzO'⟩, hzB⟩
    · rintro _ ⟨⟨g, ⟨hgG, hgV⟩, rfl⟩, hzB⟩
      have hgO : φ g ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model g hgV
      have hg1 : degIndexWith T (φ g) = 1 :=
        (hdeg g hgV).symm.trans (connectedComponentIn_subset {y | P.degIndex y = 1} y₀ hgG)
      have hgI : zeroSet T (φ g) = {i} := by
        refine Finset.eq_of_subset_of_card_le (hi ▸ hBI _ ⟨hzB, R.retract_subset_C hgO⟩) ?_
        rw [← degIndexWith_eq_card_zeroSet, hg1, Finset.card_singleton]
      exact ⟨⟨subset_closure (hnear _ ⟨hzB, hgO⟩ hgI), hgO⟩, hzB⟩

/-- **Theorem 2.45**, the local shape of a face of a face-structured tame M-polyfold: near each
of its points `x`, in a tame chart `φ : V → O`, the image `φ(F ∩ V)` agrees on a ball `B` around
`φ(x)` with a face `F_loc` of the retract `O`.

*Proof* (exposition).  By Lemma 4.C, for each `i ∈ I(φ x)` there is a component `F̂_i` of `S`
whose closure contains `φ(x)` and which contains all points `z ∈ O` near `φ(x)` with `I(z) = {i}`;
`φ⁻¹(F̂_i)` is connected in `{d_X = 1}`, so `i ↦ F_i = closure(component of φ⁻¹(F̂_i))` maps
`I(φ x)` onto the faces through `x` (every face through `x` meets some `φ⁻¹(F̂_i)` near `x`).
Face-structuredness says there are exactly `d_X(x) = #I(φ x)` such faces, so `i ↦ F_i` is
injective; hence the points of `G` near `x` all lie in `φ⁻¹(F̂_j)` for the one `j` with
`F = F_j`, and `φ(F) ∩ B = closure(F̂_j) ∩ O ∩ B` (closures computed inside the open set
`φ⁻¹(B)`). -/
theorem exists_localFace_of_isFaceStructured (hP : P.IsTame) (hfs : P.IsFaceStructured)
    {F : Set X} (hF : P.IsFace F) {x : X} (hxF : x ∈ F) :
    ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧
      ∃ R : ScRetraction φ.model.E φ.model.C, R.retract = φ.model.O ∧
      ∃ (n : ℕ) (W : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
        φ.model.C = T 0 ⁻¹' quadrant n W 0 ∧ R.IsTameWith T ∧
      ∃ Floc : Set (φ.model.E 0), R.IsRetractFace Floc ∧
      ∃ B : Set (φ.model.E 0), IsOpen B ∧ φ x ∈ B ∧ φ '' (F ∩ φ.source) ∩ B = Floc ∩ B := by
  classical
  obtain ⟨y₀, -, hFeq⟩ := id hF
  set D := {y | P.degIndex y = 1} with hD
  set G := connectedComponentIn D y₀ with hG
  obtain ⟨φ, hφ, hx, htame⟩ := IsTame.exists_chart P hP x
  obtain ⟨R, hRO, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hR := hRt n W T hT
  refine ⟨φ, hφ, hx, R, hRO, n, W, T, hT, hR, ?_⟩
  have hdeg : ∀ y ∈ φ.source, P.degIndex y = degIndexWith T (φ y) := fun y hy => by
    rw [P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hy, chartDegIndex,
      degIndex_eq T hT (φ.apply_mem_C hy)]
  set o := φ x with ho
  have hoO' : o ∈ φ.model.O := φ.mapsTo_model x hx
  have hoO : o ∈ R.retract := by rw [hRO]; exact hoO'
  have hsubO : ∀ q, connectedComponentIn R.faceStratum q ⊆ φ.model.O := fun q z hz => by
    rw [← hRO]; exact (connectedComponentIn_subset _ _ hz).1
  have hφc : ContinuousAt φ x := φ.continuousOn_toFun.continuousAt (φ.isOpen_source.mem_nhds hx)
  set J := zeroSet T o with hJ
  -- `J` is nonempty: points of `G` near `x` have `I = {i} ⊆ J`
  have hJne : ∃ i, i ∈ J := by
    obtain ⟨y, ⟨hyV, hysub⟩, hyG⟩ := mem_closure_iff_nhds.1 (hFeq ▸ hxF) _
      ((show ∀ᶠ y in 𝓝 x, y ∈ φ.source from φ.isOpen_source.mem_nhds hx).and
        (hφc.eventually (eventually_zeroSet_subset T o)))
    have hy1 : degIndexWith T (φ y) = 1 :=
      (hdeg y hyV).symm.trans (connectedComponentIn_subset D y₀ hyG)
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 ((degIndexWith_eq_card_zeroSet T _).symm.trans hy1)
    exact ⟨i, hysub (by rw [hi]; exact Finset.mem_singleton_self i)⟩
  have : Nonempty (Fin n) := ⟨hJne.choose⟩
  -- the components `F̂_i` of Lemma 4.C at `o`
  have key : ∀ i : Fin n, (T 0 o).1 i = 0 → ∃ p ∈ R.faceStratum,
      o ∈ closure (connectedComponentIn R.faceStratum p) ∧ ∀ᶠ z in 𝓝 o, z ∈ φ.model.C →
        zeroSet T z = {i} → R z ∈ connectedComponentIn R.faceStratum p := by
    intro i hi
    obtain ⟨ε, hε, p, hpS, -, -, -, -, hB, hcl⟩ := local_face_structure hT hR hoO hi
    refine ⟨p, hpS, ?_, Filter.mem_of_superset (Metric.ball_mem_nhds o hε) fun z hz hzC hzI =>
      hB z ⟨hz, hzC⟩ hzI⟩
    have := hcl o ⟨Metric.mem_ball_self hε, R.retract_subset_C hoO⟩ hi
    rwa [R.apply_eq_self_of_mem_retract hoO] at this
  choose! p hpS hpcl hp using key
  have hev : ∀ᶠ z in 𝓝 o, zeroSet T z ⊆ J ∧ ∀ i ∈ J, z ∈ φ.model.C →
      zeroSet T z = {i} → R z ∈ connectedComponentIn R.faceStratum (p i) :=
    (eventually_zeroSet_subset T o).and
      ((Filter.eventually_all_finset _).2 fun i hi => hp i ((mem_zeroSet T).1 hi))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hev
  -- `K_i = φ⁻¹(F̂_i)`
  set K : Fin n → Set X := fun i => φ.symm '' connectedComponentIn R.faceStratum (p i) with hKdef
  have hK : ∀ i ∈ J, IsPreconnected (K i) ∧ K i ⊆ D ∧ φ.symm (p i) ∈ K i := by
    intro i hi
    have hpi := hpS i ((mem_zeroSet T).1 hi)
    refine ⟨isPreconnected_connectedComponentIn.image _ (φ.continuousOn_invFun.mono (hsubO _)),
      ?_, ⟨p i, mem_connectedComponentIn hpi, rfl⟩⟩
    rintro _ ⟨z, hz, rfl⟩
    have hzS := connectedComponentIn_subset _ _ hz
    change P.degIndex (φ.symm z) = 1
    rw [hdeg _ (φ.symm_mapsTo (hsubO _ hz)), φ.apply_symm_apply (hsubO _ hz)]
    exact faceStratum_degIndexWith hT hzS
  have hKc : ∀ i ∈ J, K i ⊆ connectedComponentIn D (φ.symm (p i)) := fun i hi =>
    (hK i hi).1.subset_connectedComponentIn (hK i hi).2.2 (hK i hi).2.1
  set f : Fin n → Set X := fun i => closure (connectedComponentIn D (φ.symm (p i))) with hfdef
  -- every component of `D` whose closure contains `x` is one of the `cc(φ⁻¹ p_i)`
  have hsurj : ∀ y₁, x ∈ closure (connectedComponentIn D y₁) →
      ∃ i ∈ J, connectedComponentIn D y₁ = connectedComponentIn D (φ.symm (p i)) := by
    intro y₁ hx₁
    obtain ⟨y, ⟨hyV, hyB⟩, hyG⟩ := mem_closure_iff_nhds.1 hx₁ _
      ((show ∀ᶠ y in 𝓝 x, y ∈ φ.source from φ.isOpen_source.mem_nhds hx).and
        (hφc.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))))
    obtain ⟨hysub, hyR⟩ := hball hyB
    have hy1 : degIndexWith T (φ y) = 1 :=
      (hdeg y hyV).symm.trans (connectedComponentIn_subset D y₁ hyG)
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 ((degIndexWith_eq_card_zeroSet T _).symm.trans hy1)
    have hiJ : i ∈ J := hysub (by rw [hi]; exact Finset.mem_singleton_self i)
    have hφyO : φ y ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model y hyV
    have hRy := hyR i hiJ (φ.apply_mem_C hyV) hi
    rw [R.apply_eq_self_of_mem_retract hφyO] at hRy
    have hyK : y ∈ K i := ⟨φ y, hRy, φ.symm_apply_apply hyV⟩
    refine ⟨i, hiJ, ?_⟩
    rw [connectedComponentIn_eq hyG, connectedComponentIn_eq (hKc i hiJ hyK)]
  -- the faces through `x` are the `f i`, and there are `#J` of them
  have hFx : {F' | P.IsFace F' ∧ x ∈ F'} = f '' (J : Set (Fin n)) := by
    ext F'
    constructor
    · rintro ⟨⟨y₁, -, rfl⟩, hx₁⟩
      obtain ⟨i, hiJ, hi⟩ := hsurj y₁ hx₁
      exact ⟨i, hiJ, congrArg closure hi.symm⟩
    · rintro ⟨i, hiJ, rfl⟩
      refine ⟨⟨φ.symm (p i), (hK i hiJ).2.1 (hK i hiJ).2.2, rfl⟩, ?_⟩
      have hcw : ContinuousWithinAt φ.symm (connectedComponentIn R.faceStratum (p i)) o :=
        (φ.continuousOn_invFun o hoO').mono (hsubO _)
      have := hcw.mem_closure_image (hpcl i ((mem_zeroSet T).1 hiJ))
      rw [show φ.symm o = x from φ.symm_apply_apply hx] at this
      exact closure_mono (hKc i hiJ) this
  have hinj : Set.InjOn f (J : Set (Fin n)) := by
    have hcard := hfs x
    rw [hFx, ← Finset.coe_image, Set.encard_coe_eq_coe_finsetCard, hdeg x hx,
      degIndexWith_eq_card_zeroSet] at hcard
    exact Finset.card_image_iff.1 (by exact_mod_cast hcard)
  -- our face is `f j`
  obtain ⟨j, hjJ, hGj⟩ := hsurj y₀ (hFeq ▸ hxF)
  have hK' : ∀ g ∈ G, g ∈ φ.source → φ g ∈ Metric.ball o δ →
      φ g ∈ connectedComponentIn R.faceStratum (p j) := by
    intro g hgG hgV hgB
    obtain ⟨hgsub, hgR⟩ := hball hgB
    have hg1 : degIndexWith T (φ g) = 1 :=
      (hdeg g hgV).symm.trans (connectedComponentIn_subset D y₀ hgG)
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 ((degIndexWith_eq_card_zeroSet T _).symm.trans hg1)
    have hiJ : i ∈ J := hgsub (by rw [hi]; exact Finset.mem_singleton_self i)
    have hφgO : φ g ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model g hgV
    have hRg := hgR i hiJ (φ.apply_mem_C hgV) hi
    rw [R.apply_eq_self_of_mem_retract hφgO] at hRg
    have hgK : g ∈ K i := ⟨φ g, hRg, φ.symm_apply_apply hgV⟩
    have hij : i = j := by
      apply hinj hiJ hjJ
      simp only [hfdef]
      rw [connectedComponentIn_eq (hKc i hiJ hgK), ← hGj, ← connectedComponentIn_eq hgG]
    rw [← hij]; exact hRg
  refine ⟨closure (connectedComponentIn R.faceStratum (p j)) ∩ R.retract,
    ⟨p j, hpS j ((mem_zeroSet T).1 hjJ), rfl⟩, Metric.ball o δ, Metric.isOpen_ball,
    Metric.mem_ball_self hδ, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨⟨g, ⟨hgF, hgV⟩, rfl⟩, hgB⟩
    set U₀ := φ.source ∩ φ ⁻¹' Metric.ball o δ with hU₀
    have hU₀o : IsOpen U₀ :=
      φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source Metric.isOpen_ball
    have hgcl : g ∈ closure (U₀ ∩ G) := hU₀o.inter_closure ⟨⟨hgV, hgB⟩, hFeq ▸ hgF⟩
    have hcw : ContinuousWithinAt φ (U₀ ∩ G) g :=
      (φ.continuousOn_toFun g hgV).mono fun z hz => hz.1.1
    have h1 := hcw.mem_closure_image hgcl
    refine ⟨⟨closure_mono ?_ h1, by rw [hRO]; exact φ.mapsTo_model g hgV⟩, hgB⟩
    rintro _ ⟨g', ⟨⟨hg'V, hg'B⟩, hg'G⟩, rfl⟩
    exact hK' g' hg'G hg'V hg'B
  · rintro z ⟨⟨hzcl, hzO⟩, hzB⟩
    have hzO' : z ∈ φ.model.O := by rw [← hRO]; exact hzO
    have hcw : ContinuousWithinAt φ.symm (connectedComponentIn R.faceStratum (p j)) z :=
      (φ.continuousOn_invFun z hzO').mono (hsubO _)
    have h1 := hcw.mem_closure_image hzcl
    have hFj : φ.symm z ∈ F := by
      rw [hFeq, hG, hGj]; exact closure_mono (hKc j hjJ) h1
    exact ⟨⟨φ.symm z, ⟨hFj, φ.symm_mapsTo hzO'⟩, φ.apply_symm_apply hzO'⟩, hzB⟩

/-- **Theorem 2.45**: in a face-structured tame M-polyfold every face `F` is a sub-M-polyfold
of `X` (`exists_localFace_of_isFaceStructured`, Proposition 2.43's retraction onto the local face,
and `isSubMPolyfold_of_local`). -/
theorem theorem_2_45_isSubMPolyfold_face (hP : P.IsTame) (hfs : P.IsFaceStructured) {F : Set X}
    (hF : P.IsFace F) : P.IsSubMPolyfold F := by
  refine P.isSubMPolyfold_of_local fun x hxF => ?_
  obtain ⟨φ, hφ, hx, R, hRO, n, W, T, hT, hR, Floc, hFloc, B, hB, hxB, hEq⟩ :=
    exists_localFace_of_isFaceStructured P hP hfs hF hxF
  have hFlocO : Floc ⊆ R.retract := by
    obtain ⟨_, _, h⟩ := hFloc; rw [h]; exact inter_subset_right
  obtain ⟨-, -, S', -, -, hS'ret, -⟩ := proposition_2_43 hT hR hFloc
  refine ⟨φ, hφ, hx, S', B, hB, hxB, ?_, ?_⟩
  · rw [hS'ret, ← hRO]; exact hFlocO
  · rw [hS'ret, hEq]

/-- **Theorem 2.45**, the face-structured case: every face `F` of a face-structured tame
M-polyfold, with the structure of a sub-M-polyfold (Proposition 2.21), is **tame**, and the
inclusion satisfies `d_X(i(x)) = d_F(x) + 1`.

*Proof.* Near `x ∈ F`, `φ(F) ∩ B = F_loc ∩ B` for a face `F_loc ⊆ f_i` of a tame chart
(`exists_localFace_of_isFaceStructured`); the chart `π ∘ φ` of `F` (`faceChart`) onto
`π(F_loc ∩ B)`, the retract of the restriction of the tame retraction `r'` of
`proposition_2_43_tameModel`, is a chart of the induced structure modelled on a tame retract, and
it realizes `d_F(x) = d_{C'}(π φ x) = d_C(φ x) − 1 = d_X(x) − 1`.  Paracompactness of `F` holds
since faces are closed. -/
theorem theorem_2_45_isTame_face (hP : P.IsTame) (hfs : P.IsFaceStructured) {F : Set X}
    (hF : P.IsFace F) :
    haveI : ParacompactSpace F := paracompactSpace_of_isClosed (IsFace.isClosed P hF)
    (subPolyfold (theorem_2_45_isSubMPolyfold_face P hP hfs hF)).IsTame ∧
      ∀ x : F, P.degIndex x =
        (subPolyfold (theorem_2_45_isSubMPolyfold_face P hP hfs hF)).degIndex x + 1 := by
  classical
  have : ParacompactSpace F := paracompactSpace_of_isClosed (IsFace.isClosed P hF)
  have hsub := theorem_2_45_isSubMPolyfold_face P hP hfs hF
  suffices key : ∀ x : F, ∃ χ : MChart F, (subPolyfold hsub).IsChart χ ∧ x ∈ χ.source ∧
      IsTameRetract χ.model.E χ.model.C χ.model.O ∧
      P.degIndex x = (subPolyfold hsub).degIndex x + 1 by
    refine ⟨isTame_of_forall_exists_chart _ fun x => ?_, fun x => (key x).choose_spec.2.2.2⟩
    obtain ⟨χ, h1, h2, h3, -⟩ := key x
    exact ⟨χ, h1, h2, h3⟩
  intro x
  obtain ⟨φ, hφ, hx, R, hRO, n, W, T, hT, hR, Floc, hFloc, B, hB, hxB, hEq⟩ :=
    exists_localFace_of_isFaceStructured P hP hfs hF x.2
  obtain ⟨i₀, -⟩ := proposition_2_43 hT hR hFloc
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := i₀.pos; omega⟩
  obtain ⟨i, hFi, R', hR'tame, hR'ret, hdeg'⟩ := proposition_2_43_tameModel hT hR hFloc
  have hT' : quadrant k W 0 = (ScIso.refl ((ScBanach.const (Fin k → ℝ)).prod W)) 0 ⁻¹'
      quadrant k W 0 := by ext; rfl
  set V₁ := φ.source ∩ φ ⁻¹' B with hV₁def
  have hV₁ : IsOpen V₁ := φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source hB
  have hFV : φ '' (F ∩ V₁) = Floc ∩ B := by
    rw [← hEq]
    ext z
    constructor
    · rintro ⟨y, ⟨hyF, hyV, hyB⟩, rfl⟩; exact ⟨⟨y, ⟨hyF, hyV⟩, rfl⟩, hyB⟩
    · rintro ⟨⟨y, ⟨hyF, hyV⟩, rfl⟩, hyB⟩; exact ⟨y, ⟨hyF, hyV, hyB⟩, rfl⟩
  set ι := faceIncl T i with hι
  set π := faceProj T i with hπ
  have hιπ : ∀ y ∈ φ '' (F ∩ V₁), ι 0 (π 0 y) = y := fun y hy => by
    rw [hFV] at hy; exact faceIncl_faceProj T i (hFi hy.1)
  have hπι : ∀ z, π 0 (ι 0 z) = z := faceProj_faceIncl T i
  set Wι := ι 0 ⁻¹' B with hWι
  have hWι : IsOpen Wι := hB.preimage (ι 0).continuous
  have hret_eq : (R'.restrict hWι).retract = π 0 '' (φ '' (F ∩ V₁)) := by
    rw [R'.restrict_retract, hR'ret, hFV]
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hyB⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      have : ι 0 (π 0 y) = y := faceIncl_faceProj T i (hFi hy)
      rw [← this]; exact hyB
    · rintro ⟨y, ⟨hy, hyB⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      change ι 0 (π 0 y) ∈ B
      rw [faceIncl_faceProj T i (hFi hy)]; exact hyB
  have hret : IsScRetract _ (quadrant k W 0) (π 0 '' (φ '' (F ∩ V₁))) :=
    ⟨R'.restrict hWι, hret_eq⟩
  set χ := faceChart x φ V₁ (quadrant k W 0) ι π hV₁ (fun _ h => h.1) hιπ hπι hret with hχ
  have hχQ : (subPolyfold hsub).IsChart χ :=
    isChart_subPolyfold_of_compatible hsub hφ (fun _ hy => hy.1) fun d b₀ =>
      faceChart_compatible_subChart hφ hV₁ (fun _ h => h.1) hιπ hπι hret d b₀
  have hxχ : x ∈ χ.source := show (x : X) ∈ V₁ from ⟨hx, hxB⟩
  have htame' := hR'tame.restrict hWι
  refine ⟨χ, hχQ, hxχ, ⟨R'.restrict hWι, hret_eq, htame'.isTame hT'⟩, ?_⟩
  rw [(subPolyfold hsub).degIndex_eq_chartDegIndex_of_isTameWith hχQ (R'.restrict hWι) hret_eq
      hT' htame' hxχ, P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hx]
  have hxF : φ x ∈ Floc := by
    have : φ x ∈ φ '' (F ∩ V₁) := ⟨x, ⟨x.2, hx, hxB⟩, rfl⟩
    rw [hFV] at this; exact this.1
  exact (hdeg' _ hxF).symm

/-- **Proposition 2.44**, first sentence: in a tame M-polyfold every point `x` has exactly
`d_X(x)` local faces, each a tame M-polyfold `F` with `d_F(x) = d_X(x) − 1`.  "Local faces" are
the faces of the M-polyfold `O ≅ V` of a tame chart `φ : V → O` around `x` (as in
`proposition_2_42`), with the sub-M-polyfold structure of Proposition 2.21. -/
theorem proposition_2_44 (hP : P.IsTame) (x : X) :
    ∃ φ : MChart X, P.IsChart φ ∧ ∃ hx : x ∈ φ.source,
      {F | (φ.model.toMPolyfold ⟨_, φ.mapsTo_model x hx⟩).IsFace F ∧
        (⟨φ x, φ.mapsTo_model x hx⟩ : φ.model.O) ∈ F}.encard = (P.degIndex x : ℕ∞) ∧
      ∀ (F : Set φ.model.O) (hF : (φ.model.toMPolyfold ⟨_, φ.mapsTo_model x hx⟩).IsFace F),
        haveI : ParacompactSpace F := paracompactSpace_of_isClosed (IsFace.isClosed _ hF)
        ∃ hsub : (φ.model.toMPolyfold ⟨_, φ.mapsTo_model x hx⟩).IsSubMPolyfold F,
          (subPolyfold hsub).IsTame ∧ ∀ hxF : (⟨φ x, φ.mapsTo_model x hx⟩ : φ.model.O) ∈ F,
            (subPolyfold hsub).degIndex ⟨_, hxF⟩ + 1 = P.degIndex x := by
  obtain ⟨φ, hφ, hx, htame⟩ := IsTame.exists_chart P hP x
  obtain ⟨R, hRO, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hR := hRt n W T hT
  set hne : φ.model.O.Nonempty := ⟨_, φ.mapsTo_model x hx⟩
  have hdx : (φ.model.toMPolyfold hne).degIndex ⟨φ x, φ.mapsTo_model x hx⟩ = P.degIndex x :=
    (φ.model.degIndex_toMPolyfold_of_isTameWith hne R hRO hT hR _).trans
      (P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hx).symm
  refine ⟨φ, hφ, hx, ?_, fun F hF => ?_⟩
  · rw [φ.model.isFaceStructured_toMPolyfold hne R hRO hT hR, hdx]
  · have : ParacompactSpace F := paracompactSpace_of_isClosed (IsFace.isClosed _ hF)
    obtain ⟨h1, h2⟩ := φ.model.proposition_2_43_isTame hne R hRO hT hR hF
    exact ⟨_, h1, fun hxF => (h2 ⟨_, hxF⟩).trans hdx⟩

end MPolyfold

end Polyfold
