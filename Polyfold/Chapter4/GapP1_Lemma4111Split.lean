import Polyfold.Chapter2.PartialCone
import Polyfold.Chapter3.BasicClassComposition
import Polyfold.Chapter3.Book2021Germs
import Polyfold.Chapter3.TangentGerm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.1, the linear
algebra in the proof of **Lemma 4.1.11** (pp. 179–181).

# The splitting `E = (T₀O ⊕ B) ⊕ W` and the basic germ `(a + b, w) ↦ b + w`

## The text

"In general, the good complement `Y` in the decomposition `E = T₀O ⊕ Y` is not a subset of `C`.
However, we claim that there exists a finite-dimensional sc-Banach space `B` and an sc-Banach space
`W` contained in `C`, such that `Y = B ⊕ W`" … "`C = (C ∩ (T₀O ⊕ B)) ⊕ W`" … "the set
`C ∩ (T₀O ⊕ B)` is a partial quadrant in `T₀O ⊕ B`" … "`P(g − s)(a + b + w) = P(1 − p)(a + b + w)
= P(b + w) = w`" … "`g − s` is a basic germ, whose contraction part happens to be identically
zero."

## What is formalized

* `isPartialQuadrant_preimage_quadrant`: for a surjective linear `M : P → ℝᵏ` on a
  finite-dimensional `P`, `{a | M(a) ≥ 0}` is a partial quadrant of `P`.
* `ScBanach.topIso`: `E ≅ E.ofSubspace ⊤`.
* `exists_splitData`: for an sc-subspace `Y` and a continuous `L : E₀ → ℝᵏ` there are smooth
  `e_1, …, e_d ∈ Y` and functionals `ℓ_1, …, ℓ_d` dual to them, with `ℓ_j(v) = 0 ∀ j ⇔ L v = 0`
  on `Y` (`B = span(e_j)`, `W = Y ∩ ker L`); `isScSubspace_splitW`: `W` is an sc-subspace.
* `isConjugateToBasicGerm_projection` (**the last step of the proof of Lemma 4.1.11**): for an
  sc-splitting `E = N ⊕ Y` with `N` finite-dimensional and smooth, the projection `p` onto `N`
  along `Y`, and any relatively open `U ∋ 0` in any partial quadrant `C` of `E`, the principal part
  `v ↦ (1 − p)v ∈ Y` of a section of `U ◁ Y` is conjugated to a basic germ (Definition 3.1.11):
  `Ψ(v, y) = (S v, S_Y y)` with `S : E ≅ ℝ^{dim N + d} ⊕ W`, `S_Y : Y ≅ ℝᵈ ⊕ W`, and the basic
  germ `h(a, w) = (a_B, w)` with contraction part `0`.

## What the text leaves implicit, and the choices made

* `W = Y ∩ ⋂_{i ≤ k} ker λ_i` for the coordinate functionals `λ_i` of a presentation of `C`, and
  `B` is spanned by smooth vectors of `Y` (the decomposition must be an sc-splitting, so `B` must
  lie in `Y_∞`; such vectors exist because `L(Y ∩ E_∞) = L(Y)`, the image being finite-dimensional
  and `Y ∩ E_∞` dense in `Y`).
* The text gets "`C ∩ (T₀O ⊕ B)` is a partial quadrant" from good position (Proposition 3.1.25).
  Here it follows from the surjectivity of `(λ_i)_i` on `T₀O ⊕ B` (they vanish on `W`), and the
  good position of `T₀O` is not used.
-/

open Set Filter Topology Function Module Metric

noncomputable section

namespace Polyfold

/-! ### A partial quadrant from a surjective linear map -/

section Quadrant

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {k : ℕ}

/-- **`{a | M(a) ≥ 0}` is a partial quadrant** for a surjective linear `M : P → ℝᵏ`: with a right
inverse `σ` of `M`, `P ≅ ℝᵏ ⊕ ker M`, `a ↦ (M a, a − σ(M a))`. -/
theorem isPartialQuadrant_preimage_quadrant (M : P →ₗ[ℝ] (Fin k → ℝ)) (hM : Surjective M) :
    IsPartialQuadrant (ScBanach.const P) {a | ∀ i, 0 ≤ M a i} := by
  obtain ⟨σ, hσ⟩ := M.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hM)
  have hMσ : ∀ b, M (σ b) = b := fun b => LinearMap.congr_fun hσ b
  let K := LinearMap.ker M
  have hmem : ∀ a : P, a - σ (M a) ∈ K := fun a => by
    rw [LinearMap.mem_ker, map_sub, hMσ, sub_self]
  let eL : P ≃ₗ[ℝ] (Fin k → ℝ) × K :=
    { toFun := fun a => (M a, ⟨a - σ (M a), hmem a⟩)
      map_add' := fun a b => by
        refine Prod.ext (map_add M a b) (Subtype.ext ?_)
        simp only [map_add, Submodule.coe_add, Prod.snd_add]
        abel
      map_smul' := fun c a => by
        refine Prod.ext (map_smul M c a) (Subtype.ext ?_)
        simp only [map_smul, RingHom.id_apply, Prod.smul_snd, SetLike.val_smul, smul_sub]
      invFun := fun q => σ q.1 + q.2
      left_inv := fun a => by simp
      right_inv := fun q => by
        have hq : M q.2 = 0 := q.2.2
        refine Prod.ext ?_ (Subtype.ext ?_)
        · simp only [map_add, hMσ, hq, add_zero]
        · simp only [map_add, hMσ, hq, add_zero]
          abel }
  let e : P ≃L[ℝ] (Fin k → ℝ) × K := eL.toContinuousLinearEquiv
  let T : ScIso (ScBanach.const P) ((ScBanach.const (Fin k → ℝ)).prod (ScBanach.const K)) :=
    { lvl := fun _ => e
      incl_comm := fun _ _ => rfl }
  exact ⟨k, ScBanach.const K, T, by ext a; rfl⟩

end Quadrant

/-! ### `E ≅ E.ofSubspace ⊤` -/

namespace ScBanach

variable (E : ScBanach)

/-- The level map `E_m ≃ (⊤)_m`. -/
def topLvl (m : ℕ) : E m ≃L[ℝ] E.levelSub ⊤ m where
  toLinearEquiv := (LinearEquiv.ofTop _ (E.levelSub_top m)).symm
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

/-- **`E ≅ E.ofSubspace ⊤`**. -/
def topIso : ScIso E (E.ofSubspace E.isScSubspace_top) where
  lvl m := E.topLvl m
  incl_comm _ _ := rfl

@[simp] lemma topLvl_val (m : ℕ) (x : E m) : ((E.topLvl m x : E.levelSub ⊤ m) : E m) = x := rfl

end ScBanach

/-! ### Splitting data: `Y = B ⊕ W` with `B` smooth and `W = Y ∩ ker L` -/

section SplitData

variable {E : ScBanach} {Y : Submodule ℝ (E 0)} {k : ℕ}

/-- `L(Y ∩ E_∞) = L(Y)` for a continuous `L : E₀ → ℝᵏ` and an sc-subspace `Y`: the image of the
dense `Y ∩ E_∞` is a finite-dimensional, hence closed, subspace of `L(Y)`. -/
lemma map_le_map_smooth (hY : E.IsScSubspace Y) (L : E 0 →L[ℝ] (Fin k → ℝ)) :
    Y.map (L : E 0 →ₗ[ℝ] (Fin k → ℝ)) ≤ (Y ⊓ E.smooth).map (L : E 0 →ₗ[ℝ] (Fin k → ℝ)) := by
  rintro _ ⟨v, hv, rfl⟩
  have hcl : IsClosed (((Y ⊓ E.smooth).map (L : E 0 →ₗ[ℝ] (Fin k → ℝ)) :
      Submodule ℝ (Fin k → ℝ)) : Set (Fin k → ℝ)) := Submodule.closed_of_finiteDimensional _
  have hv' : v ∈ closure ((Y ⊓ E.smooth : Submodule ℝ (E 0)) : Set (E 0)) := by
    have h := hY.2 0 (show v ∈ (E.levelSub Y 0 : Set (E 0)) by rw [E.levelSub_zero]; exact hv)
    refine closure_mono ?_ h
    rintro y ⟨hy1, hy2⟩
    rw [SetLike.mem_coe, E.levelSub_zero] at hy1
    exact ⟨hy1, hy2⟩
  have := mem_closure_image L.continuous.continuousAt hv'
  refine hcl.closure_subset (closure_mono ?_ this)
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hy, rfl⟩

/-- **Splitting data** for an sc-subspace `Y` and a continuous `L : E₀ → ℝᵏ`: smooth `e_j ∈ Y` and
continuous functionals `ℓ_j` with `ℓ_i(e_j) = δ_ij` and, on `Y`, `ℓ_j(v) = 0 ∀ j ⇔ L v = 0`. -/
theorem exists_splitData (hY : E.IsScSubspace Y) (L : E 0 →L[ℝ] (Fin k → ℝ)) :
    ∃ (d : ℕ) (ℓ : Fin d → E 0 →L[ℝ] ℝ) (e : Fin d → E 0), (∀ j, e j ∈ E.smooth) ∧
      (∀ j, e j ∈ Y) ∧ (∀ i j, ℓ i (e j) = if i = j then 1 else 0) ∧
      ∀ v ∈ Y, ((∀ j, ℓ j v = 0) ↔ L v = 0) := by
  set V := Y.map (L : E 0 →ₗ[ℝ] (Fin k → ℝ)) with hVdef
  let b := Module.finBasis ℝ V
  have hb : ∀ j, ∃ y, y ∈ Y ⊓ E.smooth ∧ L y = (b j : Fin k → ℝ) := fun j =>
    map_le_map_smooth hY L (b j).2
  choose e he hLe using hb
  obtain ⟨π, hπ⟩ := V.subtype.exists_leftInverse_of_injective V.ker_subtype
  have hπV : ∀ w : V, π (w : Fin k → ℝ) = w := fun w => LinearMap.congr_fun hπ w
  let ℓ : Fin (finrank ℝ V) → E 0 →L[ℝ] ℝ := fun j =>
    (LinearMap.toContinuousLinearMap ((b.coord j).comp π)).comp L
  have hℓ : ∀ j v, ℓ j v = b.coord j (π (L v)) := fun _ _ => rfl
  refine ⟨finrank ℝ V, ℓ, e, fun j => (he j).2, fun j => (he j).1, fun i j => ?_, fun v hv => ?_⟩
  · rw [hℓ, hLe, hπV, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · have hw : L v ∈ V := ⟨v, hv, rfl⟩
    have h1 : π (L v) = ⟨L v, hw⟩ := hπV ⟨L v, hw⟩
    simp only [hℓ, h1]
    constructor
    · intro h
      have : (⟨L v, hw⟩ : V) = 0 := b.forall_coord_eq_zero_iff.1 h
      exact congrArg Subtype.val this
    · intro h j
      have : (⟨L v, hw⟩ : V) = 0 := Subtype.ext h
      rw [this, map_zero]

variable {d : ℕ} (ℓ : Fin d → E 0 →L[ℝ] ℝ) (e : Fin d → E 0)

/-- `W = Y ∩ ⋂_j ker ℓ_j`. -/
def splitW (Y : Submodule ℝ (E 0)) : Submodule ℝ (E 0) :=
  Y ⊓ LinearMap.ker ((ContinuousLinearMap.pi ℓ : E 0 →L[ℝ] (Fin d → ℝ)) : E 0 →ₗ[ℝ] (Fin d → ℝ))

lemma mem_splitW {v : E 0} : v ∈ splitW ℓ Y ↔ v ∈ Y ∧ ∀ j, ℓ j v = 0 := by
  rw [splitW, Submodule.mem_inf, LinearMap.mem_ker]
  refine and_congr Iff.rfl ⟨fun h j => congrFun h j, fun h => funext h⟩

variable (hes : ∀ j, e j ∈ E.smooth) (heY : ∀ j, e j ∈ Y)
  (hℓe : ∀ i j, ℓ i (e j) = if i = j then 1 else 0)

include heY hℓe in
lemma sub_sum_mem_splitW {v : E 0} (hv : v ∈ Y) : v - ∑ j, ℓ j v • e j ∈ splitW ℓ Y := by
  rw [mem_splitW]
  refine ⟨Y.sub_mem hv (Y.sum_mem fun j _ => Y.smul_mem _ (heY j)), fun i => ?_⟩
  rw [map_sub, map_sum]
  simp only [map_smul, hℓe, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, sub_self]

include hes heY hℓe in
/-- **`W = Y ∩ ⋂ ker ℓ_j` is an sc-subspace**: the continuous projection
`Π_m(y) = y − Σ_j ℓ_j(y) e_j` of `E_m` fixes `W_m` and maps the smooth points of `Y_m` into
`W_m ∩ E_∞`. -/
theorem isScSubspace_splitW (hY : E.IsScSubspace Y) : E.IsScSubspace (splitW ℓ Y) := by
  refine ⟨?_, fun m z hz => ?_⟩
  · exact hY.1.inter (ContinuousLinearMap.isClosed_ker _)
  have hz' : E.toBase m z ∈ splitW ℓ Y := hz
  have hzY : z ∈ closure ((E.levelSub Y m : Set (E m)) ∩ E.smoothLvl m) :=
    hY.2 m ((mem_splitW ℓ).1 hz').1
  let Pr : E m →L[ℝ] E m := ContinuousLinearMap.id ℝ (E m) -
    ∑ j, ((ℓ j).comp (E.toBase m)).smulRight (smoothLift e hes m j)
  have hPr : ∀ y : E m, E.toBase m (Pr y) = E.toBase m y - ∑ j, ℓ j (E.toBase m y) • e j := by
    intro y
    simp only [Pr, sub_apply, ContinuousLinearMap.id_apply,
      FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, map_sub, map_sum, map_smul, toBase_smoothLift]
  have hPrz : Pr z = z := by
    apply E.toBase_injective m
    have h0 := ((mem_splitW ℓ).1 hz').2
    rw [hPr]
    simp only [h0, zero_smul, Finset.sum_const_zero, sub_zero]
  rw [← hPrz]
  have := mem_closure_image Pr.continuous.continuousAt hzY
  refine closure_mono ?_ this
  rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · change E.toBase m (Pr y) ∈ splitW ℓ Y
    rw [hPr]
    exact sub_sum_mem_splitW ℓ e heY hℓe hy1
  · change E.toBase m (Pr y) ∈ (E.smooth : Set (E 0))
    rw [hPr]
    exact E.smooth.sub_mem hy2 (E.smooth.sum_mem fun j _ => E.smooth.smul_mem _ (hes j))

end SplitData

/-! ### The projection `1 − p : E → Y` as an sc-operator -/

section Projection

variable {E : ScBanach} {N Y : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
  (hNs : N ≤ E.smooth) (hY : E.IsScSubspace Y) (hcompl : IsCompl N Y)
  (p : E 0 →L[ℝ] N) (hpN : ∀ n : N, p n = n) (hpY : ∀ y ∈ Y, p y = 0)

omit [FiniteDimensional ℝ N] in
include hcompl hpN hpY in
/-- `p x = 0 ⟹ x ∈ Y` for the projection `p` onto `N` along `Y`. -/
lemma mem_of_p_eq_zero {x : E 0} (hx : p x = 0) : x ∈ Y := by
  have hsup : x ∈ N ⊔ Y := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨n, hn, y, hy, rfl⟩ := Submodule.mem_sup.1 hsup
  have h1 : p n = 0 := by
    have := hx; rwa [map_add, hpY y hy, add_zero] at this
  have h2 : p n = ⟨n, hn⟩ := hpN ⟨n, hn⟩
  have h3 : n = 0 := by
    have := congrArg (fun z : N => (z : E 0)) (h2.symm.trans h1)
    simpa using this
  rw [h3, zero_add]; exact hy

omit [FiniteDimensional ℝ N] in
include hcompl hpN hpY in
lemma sub_p_mem (x : E 0) : x - p x ∈ Y :=
  mem_of_p_eq_zero hcompl p hpN hpY (by rw [map_sub, hpN, sub_self])

/-- The level-`m` map `v ↦ v − p v` of `1 − p : E_m → Y_m` (`p v ∈ N ⊆ E_∞` lifted to `E_m`). -/
def qLvl (m : ℕ) : E m →L[ℝ] E.levelSub Y m :=
  ContinuousLinearMap.codRestrict (ContinuousLinearMap.id ℝ (E m) -
      (LinearMap.toContinuousLinearMap (finSmoothLift hNs m)).comp (p.comp (E.toBase m)))
    (E.levelSub Y m) fun v => by
      change E.toBase m _ ∈ Y
      simp only [sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
        LinearMap.coe_toContinuousLinearMap', map_sub, toBase_finSmoothLift]
      exact sub_p_mem hcompl p hpN hpY _

lemma qLvl_val (m : ℕ) (v : E m) :
    ((qLvl hNs hcompl p hpN hpY m v : E.levelSub Y m) : E m) =
      v - finSmoothLift hNs m (p (E.toBase m v)) := rfl

/-- **`1 − p : E → Y` as an sc-operator** (the principal part `u ↦ (1 − p)u` of the text). -/
def qOp : ScOperator E (E.ofSubspace hY) where
  lvl m := qLvl hNs hcompl p hpN hpY m
  incl_comm m x := by
    apply Subtype.ext
    change E.incl m ((qLvl hNs hcompl p hpN hpY (m + 1) x : E.levelSub Y (m + 1)) : E (m + 1)) =
      ((qLvl hNs hcompl p hpN hpY m (E.incl m x) : E.levelSub Y m) : E m)
    rw [qLvl_val, qLvl_val, map_sub]
    congr 1
    apply E.toBase_injective m
    rw [← E.toBase_succ, toBase_finSmoothLift, toBase_finSmoothLift, E.toBase_succ]

lemma qOp_zero_val (v : E 0) :
    (qOp hNs hY hcompl p hpN hpY 0 v).1 = v - p v := by
  change v - finSmoothLift hNs 0 (p v) = v - p v
  congr 1
  have := toBase_finSmoothLift hNs 0 (p v)
  rwa [E.toBase_zero] at this

end Projection

/-! ### The principal part `v ↦ (1 − p)v` is conjugated to a basic germ -/

section Conjugation

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- A continuous linear map of finite-dimensional spaces as an sc-operator of the constant
structures. -/
def constOp (A : P →L[ℝ] Q) : ScOperator (ScBanach.const P) (ScBanach.const Q) where
  lvl _ := A
  incl_comm _ _ := rfl

end Conjugation

section Conj

variable {E : ScBanach} {N Y : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
  (hNs : N ≤ E.smooth) (hY : E.IsScSubspace Y) (hcompl : IsCompl N Y)
  (p : E 0 →L[ℝ] N) (hpN : ∀ n : N, p n = n) (hpY : ∀ y ∈ Y, p y = 0)

include hNs hcompl hpN hpY in
/-- **The last step of the proof of Lemma 4.1.11** (2021, pp. 180–181): for an sc-splitting
`E = N ⊕ Y` with `N` finite-dimensional and smooth and `p` the projection onto `N` along `Y`, the
principal part `v ↦ (1 − p)v` of a section of `U ◁ Y`, on a relatively open `U ∋ 0` of a partial
quadrant `C`, is conjugated to a basic germ whose contraction part is `0`
(`Y = B ⊕ W`, `W ⊆ C`, `E = (N ⊕ B) ⊕ W`, `h(a + b, w) = (b, w)`). -/
theorem isConjugateToBasicGerm_qOp {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) :
    IsConjugateToBasicGerm (F := E.ofSubspace hY) U (qOp hNs hY hcompl p hpN hpY 0) := by
  classical
  obtain ⟨k, W', T', hT'⟩ := hU.isPartialQuadrant
  obtain ⟨O, hO, hUO⟩ := hU.relOpen
  let L : E 0 →L[ℝ] (Fin k → ℝ) :=
    (ContinuousLinearMap.fst ℝ (Fin k → ℝ) (W' 0)).comp (T' 0 : E 0 →L[ℝ] _)
  have hL : ∀ v, L v = (T' 0 v).1 := fun _ => rfl
  have hC : ∀ v, v ∈ C ↔ ∀ i, 0 ≤ L v i := fun v => by rw [hT']; exact Iff.rfl
  obtain ⟨d, ℓ, e, hes, heY, hℓe, hiff⟩ := exists_splitData hY L
  have hW : E.IsScSubspace (splitW ℓ Y) := isScSubspace_splitW ℓ e hes heY hℓe hY
  have hWL : ∀ w ∈ splitW ℓ Y, L w = 0 := fun w hw =>
    (hiff w ((mem_splitW ℓ).1 hw).1).1 ((mem_splitW ℓ).1 hw).2
  -- the fibre isomorphism `Y ≅ ℝᵈ ⊕ W`
  let TF := splitIso hY hW ℓ e hes heY hℓe fun v => mem_splitW ℓ
  -- the base isomorphism `E ≅ ℝ^{dim N + d} ⊕ W`
  let bN := Module.finBasis ℝ N
  let dN := finrank ℝ N
  let lam : Fin (dN + d) → E 0 →L[ℝ] ℝ := Fin.append
    (fun i => (LinearMap.toContinuousLinearMap (bN.coord i)).comp p)
    (fun j => (ℓ j).comp (ContinuousLinearMap.id ℝ (E 0) - N.subtypeL.comp p))
  let vec : Fin (dN + d) → E 0 := Fin.append (fun i => (bN i : E 0)) e
  have hlamL : ∀ i v, lam (Fin.castAdd d i) v = bN.coord i (p v) := fun i v => by
    simp [lam]
  have hlamR : ∀ j v, lam (Fin.natAdd dN j) v = ℓ j (v - p v) := fun j v => by
    simp [lam]
  have hvecL : ∀ i, vec (Fin.castAdd d i) = (bN i : E 0) := fun i => by simp [vec]
  have hvecR : ∀ j, vec (Fin.natAdd dN j) = e j := fun j => by simp [vec]
  have hvecs : ∀ b, vec b ∈ E.smooth := fun b => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) b
    · rw [hvecL]; exact hNs (bN i).2
    · rw [hvecR]; exact hes j
  have hpe : ∀ j, p (e j) = 0 := fun j => hpY _ (heY j)
  have hlamvec : ∀ a b, lam a (vec b) = if a = b then 1 else 0 := by
    intro a b
    refine Fin.addCases (fun i => ?_) (fun j => ?_) a <;>
      refine Fin.addCases (fun i' => ?_) (fun j' => ?_) b
    · rw [hlamL, hvecL, hpN ⟨_, (bN i').2⟩, Basis.coord_apply, Basis.repr_self,
        Finsupp.single_apply]
      simp only [Fin.castAdd_inj, eq_comm]
    · rw [hlamL, hvecR, hpe, map_zero, if_neg]
      intro h; have := congrArg Fin.val h; simp at this; omega
    · rw [hlamR, hvecL, hpN ⟨_, (bN i').2⟩, sub_self, map_zero, if_neg]
      intro h; have := congrArg Fin.val h; simp at this; omega
    · rw [hlamR, hvecR, hpe, Submodule.coe_zero, sub_zero, hℓe]
      simp only [Fin.natAdd_inj]
  have hpzero : ∀ v, (∀ i, bN.coord i (p v) = 0) → p v = 0 := fun v h =>
    bN.forall_coord_eq_zero_iff.1 h
  have hBiffE : ∀ v, v ∈ splitW ℓ Y ↔ v ∈ (⊤ : Submodule ℝ (E 0)) ∧ ∀ b, lam b v = 0 := by
    intro v
    rw [mem_splitW]
    constructor
    · rintro ⟨hvY, hv⟩
      refine ⟨Submodule.mem_top, fun b => Fin.addCases (fun i => ?_) (fun j => ?_) b⟩
      · rw [hlamL, hpY v hvY, map_zero]
      · rw [hlamR, hpY v hvY, Submodule.coe_zero, sub_zero]; exact hv j
    · rintro ⟨-, hv⟩
      have hp0 : p v = 0 := hpzero v fun i => by rw [← hlamL]; exact hv _
      refine ⟨mem_of_p_eq_zero hcompl p hpN hpY hp0, fun j => ?_⟩
      have := hv (Fin.natAdd dN j)
      rwa [hlamR, hp0, Submodule.coe_zero, sub_zero] at this
  let TE := E.topIso.trans (splitIso E.isScSubspace_top hW lam vec hvecs
    (fun _ => Submodule.mem_top) hlamvec hBiffE)
  have hTE1 : ∀ v b, (TE 0 v).1 b = lam b v := fun _ _ => rfl
  have hsl : ∀ {A : Submodule ℝ (E 0)} {dd : ℕ} (f : Fin dd → E 0) (hf : ∀ j, f j ∈ E.smooth)
      (j : Fin dd), smoothLift f hf 0 j = f j := fun f hf j => by
    have := toBase_smoothLift f hf 0 j
    rwa [E.toBase_zero] at this
  have hTE2 : ∀ v, (TE 0 v).2.1 = v - ∑ b, lam b v • vec b := by
    intro v
    change (splitFwd lam vec hvecs (fun _ => Submodule.mem_top) hlamvec hBiffE 0
      (E.topLvl 0 v)).2.1 = _
    rw [splitFwd_snd]
    simp only [ScBanach.topLvl_val, E.toBase_zero, hsl (A := ⊤)]
  have hTF1 : ∀ (y : (E.ofSubspace hY) 0) j, (TF 0 y).1 j = ℓ j y.1 := fun _ _ => rfl
  have hTF2 : ∀ y : (E.ofSubspace hY) 0, (TF 0 y).2.1 = y.1 - ∑ j, ℓ j y.1 • e j := by
    intro y
    have := splitFwd_snd ℓ e hes heY hℓe (fun v => mem_splitW ℓ) 0 y
    simp only [E.toBase_zero, hsl (A := Y)] at this
    exact this
  -- the two `W`-components agree, and the `B`-components are coordinates of the base
  have hsumN : ∀ v, ∑ i, bN.coord i (p v) • (bN i : E 0) = p v := fun v => by
    have h := congrArg Subtype.val (bN.sum_repr (p v))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Basis.coord_apply] using h
  have hkey : ∀ v, (TE 0 v).2.1 = (TF 0 (qOp hNs hY hcompl p hpN hpY 0 v)).2.1 := by
    intro v
    rw [hTE2, hTF2, qOp_zero_val, Fin.sum_univ_add]
    simp only [hlamL, hlamR, hvecL, hvecR]
    rw [hsumN]
    abel
  have hkey1 : ∀ v j,
      (TF 0 (qOp hNs hY hcompl p hpN hpY 0 v)).1 j = (TE 0 v).1 (Fin.natAdd dN j) := by
    intro v j
    rw [hTF1, hTE1, hlamR, qOp_zero_val]
  -- the parameter quadrant `C̃ = {a | M(a) ≥ 0}`
  let M : (Fin (dN + d) → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
    { toFun := fun a => L (∑ b, a b • vec b)
      map_add' := fun a a' => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul,
          RingHom.id_apply] }
  have hLM : ∀ v, L v = M (TE 0 v).1 := by
    intro v
    have hw0 : L (TE 0 v).2.1 = 0 := hWL _ (TE 0 v).2.2
    rw [hTE2, map_sub] at hw0
    refine (sub_eq_zero.1 hw0).trans ?_
    change L (∑ b, lam b v • vec b) = L (∑ b, (TE 0 v).1 b • vec b)
    simp only [hTE1]
  have hMsurj : Surjective M := fun c =>
    ⟨(TE 0 ((T' 0).symm (c, 0))).1, by rw [← hLM, hL, ContinuousLinearEquiv.apply_symm_apply]⟩
  let Ct : Set (Fin (dN + d) → ℝ) := {a | ∀ i, 0 ≤ M a i}
  have hCt : IsPartialQuadrant (ScBanach.const (Fin (dN + d) → ℝ)) Ct :=
    isPartialQuadrant_preimage_quadrant M hMsurj
  have hCiff : ∀ v, v ∈ C ↔ (TE 0 v).1 ∈ Ct := fun v => by
    rw [hC]; simp only [hLM]; rfl
  -- the domain `U' = S(U)`
  let U' : Set ((ScBanach.paramProd (Fin (dN + d) → ℝ) (E.ofSubspace hW)) 0) :=
    (fun x => (TE 0).symm x) ⁻¹' O ∩ (Ct ×ˢ univ)
  have hU' : IsRelOpenInQuadrant (ScBanach.paramProd (Fin (dN + d) → ℝ) (E.ofSubspace hW))
      (Ct ×ˢ univ) U' :=
    ⟨hCt.prod_univ _, _, hO.preimage (TE 0).symm.continuous, rfl⟩
  have hTEU : MapsTo (TE.toScOperator 0) U U' := by
    intro u hu
    rw [hUO] at hu
    refine ⟨?_, (hCiff u).1 hu.2, mem_univ _⟩
    change (TE 0).symm (TE 0 u) ∈ O
    rw [ContinuousLinearEquiv.symm_apply_apply]; exact hu.1
  have hTEU' : MapsTo (TE.symm.toScOperator 0) U' U := by
    intro x hx
    rw [hUO]
    refine ⟨hx.1, (hCiff _).2 ?_⟩
    change (TE 0 ((TE 0).symm x)).1 ∈ Ct
    rw [ContinuousLinearEquiv.apply_symm_apply]; exact hx.2.1
  have hΨ := ScOperator.isStrongBundleIso_prodMap hU hU' TE.toScOperator TE.symm.toScOperator
    TF.toScOperator TF.symm.toScOperator hTEU hTEU'
    (fun u _ => (TE 0).symm_apply_apply u) (fun u _ => (TE 0).apply_symm_apply u)
    (fun y => (TF 0).symm_apply_apply y) (fun y => (TF 0).apply_symm_apply y)
  have h0' : (0 : (ScBanach.paramProd (Fin (dN + d) → ℝ) (E.ofSubspace hW)) 0) ∈ U' := by
    refine ⟨?_, ?_, mem_univ _⟩
    · change (TE 0).symm 0 ∈ O
      rw [map_zero]; rw [hUO] at h0; exact h0.1
    · intro i; change (0 : ℝ) ≤ M 0 i; rw [map_zero]; exact le_rfl
  -- the basic germ `h(a, w) = (a_B, w)` with contraction part `0`
  let πL : (Fin (dN + d) → ℝ) →L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.natAdd dN j)
  let hOp := (constOp πL).prodMap (ScOperator.id (E.ofSubspace hW))
  have hQ := (hCt.prod_univ (E.ofSubspace hW)).isQuadrantLike
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hO.preimage (TE 0).symm.continuous) 0
    (by change (TE 0).symm 0 ∈ O; rw [map_zero]; rw [hUO] at h0; exact h0.1)
  refine ⟨Fin (dN + d) → ℝ, Fin d → ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, E.ofSubspace hW, Ct, U', _, _, ScNbhdGerm.ofSet hU'.relOpen h0',
    hOp 0, fun _ => 0, hCt, hU', hΨ, map_zero _, fun x hx => hx, ?_, ?_⟩
  · refine ⟨IsScSmooth.isScSmoothGerm hQ hU'.relOpen h0' (hOp.isScSmooth hU'.isScDomain),
      map_zero _, fun x _ => (sub_zero _).symm, ?_, rfl, fun ε hε m => ?_⟩
    · exact IsScSmooth.isScSmoothGerm hQ hU'.relOpen h0'
        ((ScOperator.zeroOp _ (E.ofSubspace hW)).isScSmooth hU'.isScDomain) 0
    · set c := ‖(E.ofSubspace hW).toBase m‖
      refine ⟨ρ / (c + 1), by positivity, fun a ha har w w' hw _ => ⟨?_, ?_⟩⟩
      · change (ScBanach.paramProd (Fin (dN + d) → ℝ) (E.ofSubspace hW)).toBase m (a, w) ∈ U'
        rw [ScBanach.paramProd_toBase]
        refine ⟨hball ?_, ha, mem_univ _⟩
        rw [mem_ball_zero_iff, Prod.norm_def]
        have hc : 0 ≤ c := norm_nonneg _
        have hr : ρ / (c + 1) ≤ ρ := div_le_self hρ.le (by linarith)
        have hw' : ‖(E.ofSubspace hW).toBase m w‖ < ρ := by
          calc ‖(E.ofSubspace hW).toBase m w‖ ≤ c * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ c * (ρ / (c + 1)) := mul_le_mul_of_nonneg_left hw.le hc
            _ < (c + 1) * (ρ / (c + 1)) := by
                have : 0 < ρ / (c + 1) := by positivity
                nlinarith
            _ = ρ := by field_simp
        exact max_lt (har.trans_le hr) hw'
      · have : levelB (fun _ : (Fin (dN + d) → ℝ) × (E.ofSubspace hW) 0 =>
            (0 : (E.ofSubspace hW) 0)) m (a, w) =
            levelB (fun _ : (Fin (dN + d) → ℝ) × (E.ofSubspace hW) 0 =>
              (0 : (E.ofSubspace hW) 0)) m (a, w') := rfl
        rw [this, sub_self, norm_zero]
        exact mul_nonneg hε.le (norm_nonneg _)
  · refine Eventually.of_forall fun u _ => Prod.ext (funext fun j => ?_) (Subtype.ext ?_)
    · exact hkey1 u j
    · exact (hkey u).symm

end Conj

end Polyfold
