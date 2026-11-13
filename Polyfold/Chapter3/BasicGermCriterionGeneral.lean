import Polyfold.Chapter3.ScIsoConjugation
import Polyfold.Chapter3.BasicGermCriterionSplit
import Polyfold.Chapter3.BasicGermCriterionTransport
import Polyfold.Chapter3.BasicGermCriterionIndex

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Theorem 3.7.1** (Basic
Germ Criterion, preprint 3.58), p. 140, for a general sc-splitting (row V3.89).

# The basic germ criterion in the text's form

`Polyfold.theorem_3_7_1` is stated in the coordinates `E = ℝⁿ ⊕ X`, `C = C̃ ⊕ X`, `F = ℝᴺ ⊕ Y` of
the text's proof.  Here the theorem is stated as printed: `U` is a relatively open neighbourhood of
`0` in a partial quadrant `C ⊆ E`, `f : U → F` is sc-smooth, and

1. at every smooth point `x ∈ U`, `Df(x)` is sc-Fredholm, with index independent of `x`
   (`derivOpAt`);
2. there is an sc-splitting `E = B ⊕ X` with `B` finite-dimensional, `ker Df(0) ⊆ B` and `X ⊆ C`,
   with the compactness property `CompactnessCondition371`;
3. the estimate `DerivCondition371` for the derivative along `X`.

Then `f − f(0)` is conjugated near `0` to a basic germ (**`theorem_3_7_1_general`**).

The proof is the reduction to `theorem_3_7_1`:

* `exists_targetSplitting371`: as in the text's proof, `Y = Df(0)X` has the finite-dimensional
  complement `A = C₀ ⊕ Df(0)B ⊆ F_∞` (`C₀` the cokernel of the sc-Fredholm `Df(0)`), and `A` has an
  sc-complement `Y'` (Proposition 1.1.7);
* the coordinates `S : E ≅ B ⊕ X`, `T : F ≅ A ⊕ Y'` (`ScBanach.splitScIso`) and the conjugate
  `g = T ∘ f ∘ S⁻¹` (`scIsoConjMap`); conditions (1)–(3) for `f` give the hypotheses of
  `theorem_3_7_1` for `g`;
* `IsConjugateToBasicGerm.of_scIso` moves the conclusion back.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-- An sc-operator maps smooth points to smooth points. -/
lemma ScOperator.map_smooth {E F : ScBanach} (L : ScOperator E F) {v : E 0} (hv : v ∈ E.smooth) :
    L 0 v ∈ F.smooth := by
  rw [ScScale.mem_smooth_iff] at hv ⊢
  intro m
  obtain ⟨u, hu⟩ := hv m
  exact ⟨L m u, by rw [L.toBase_comm, hu]⟩

section Defs

variable {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0}

/-- **The linearization `Df(x) : E → F` at a smooth point `x ∈ U` as an sc-operator** (the
remark after Proposition 1.2.1). -/
def derivOpAt (hf : IsScSmooth U f) {x : E 1} (hx : x ∈ E.lvlSet U 1) (hs : x ∈ E.smoothLvl 1) :
    ScOperator E F :=
  (hf.isSc1.isSc1With_scDeriv.scOperator_deriv hx hs).toScOperator

lemma derivOpAt_zero (hf : IsScSmooth U f) {x : E 1} (hx : x ∈ E.lvlSet U 1)
    (hs : x ∈ E.smoothLvl 1) : derivOpAt hf hx hs 0 = scDeriv U f x :=
  IsScOperator.toScOperator_zero _

variable (B X : Submodule ℝ (E 0)) (U f)

/-- **Condition (2) of Theorem 3.7.1, the compactness property**, for an sc-splitting
`E = B ⊕ X`: there is `r > 0` such that for every level `m`, if `b_j → b` in `B ∩ U` with
`|b| < r`, `(η_j) ⊆ X_m` is bounded on level `m` and `Df(b_j)η_j = y_j + z_j` with `y_j → 0` in
`F_m` and `(z_j)` bounded in `F_{m+1}`, then `(η_j)` has a convergent subsequence in `E_m`. -/
def CompactnessCondition371 : Prop :=
  ∃ r > 0, ∀ m : ℕ, ∀ (b : ℕ → E (m + 1)) (b₀ : E 0) (η : ℕ → E m) (y : ℕ → F m)
    (z : ℕ → F (m + 1)),
    (∀ j, E.toBase (m + 1) (b j) ∈ B ∧ b j ∈ E.lvlSet U (m + 1)) → b₀ ∈ B → b₀ ∈ U → ‖b₀‖ < r →
    Tendsto (fun j => E.toBase (m + 1) (b j)) atTop (𝓝 b₀) →
    (∀ j, η j ∈ E.levelSub X m) → (∃ M : ℝ, ∀ j, ‖η j‖ ≤ M) →
    (∀ j, levelDeriv (scDeriv U f) m (b j) (η j) = y j + F.incl m (z j)) →
    Tendsto y atTop (𝓝 0) → (∃ M : ℝ, ∀ j, ‖z j‖ ≤ M) →
    ∃ (η₀ : E m) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (η ∘ φ) atTop (𝓝 η₀)

/-- **Condition (3) of Theorem 3.7.1**: for every `m` and `ε > 0`,
`|[D₂f(b, 0) − D₂f(b, x)]h|_m ≤ ε|h|_m` for `h ∈ X_m`, `b ∈ B` small and `x ∈ X_{m+1}` with
`|x|_m` small (`D₂` the derivative along `X`, `(b, x) = b + x`). -/
def DerivCondition371 : Prop :=
  ∀ m : ℕ, ∀ ε > 0, ∃ r > 0, ∀ b : E (m + 1), E.toBase (m + 1) b ∈ B →
    ‖E.toBase (m + 1) b‖ < r → ∀ x : E (m + 1), x ∈ E.levelSub X (m + 1) →
    b ∈ E.lvlSet U (m + 1) → b + x ∈ E.lvlSet U (m + 1) → ‖E.incl m x‖ < r →
    ∀ h : E m, h ∈ E.levelSub X m →
      ‖levelDeriv (scDeriv U f) m b h - levelDeriv (scDeriv U f) m (b + x) h‖ ≤ ε * ‖h‖

end Defs

/-! ### The target splitting `F = A ⊕ Y'` of the proof -/

section Target

variable {E F : ScBanach} {B X : Submodule ℝ (E 0)}

/-- **The splitting of the target** (the text's proof: `Y = Df(0)X`, `F = Y ⊕ A`): for an
sc-Fredholm `D : E → F` with `ker D ⊆ B`, `E = B ⊕ X` and `B ⊆ E_∞` finite-dimensional, the
finite-dimensional `A = C₀ ⊕ D(B) ⊆ F_∞` is an algebraic complement of `D(X)`. -/
theorem exists_targetSplitting371 (hBX : E.IsScSplitting B X) [FiniteDimensional ℝ B]
    (hBs : B ≤ E.smooth) (D : ScOperator E F) (hD : IsScFredholm D)
    (hker : LinearMap.ker (D 0 : E 0 →ₗ[ℝ] F 0) ≤ B) :
    ∃ A : Submodule ℝ (F 0), FiniteDimensional ℝ A ∧ A ≤ F.smooth ∧
      (∀ x ∈ X, D 0 x ∈ A → x = 0) ∧ ∀ w : F 0, ∃ a ∈ A, ∃ x ∈ X, w = a + D 0 x := by
  obtain ⟨s⟩ := hD
  have := s.finite_C
  have hBX0 := hBX.isCompl_zero
  have hCY : IsCompl s.C s.Y := by
    have := s.splitF.2.2 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  set Dl : E 0 →ₗ[ℝ] F 0 := (D 0 : E 0 →ₗ[ℝ] F 0)
  refine ⟨s.C ⊔ B.map Dl, inferInstance, ?_, ?_, ?_⟩
  · refine sup_le ((F.proposition_1_1_7_iff s.C).1 s.splitF.1) ?_
    rintro _ ⟨b, hb, rfl⟩
    exact D.map_smooth (hBs hb)
  · intro x hx hDx
    obtain ⟨c, hc, _, ⟨b, hb, rfl⟩, hcb⟩ := Submodule.mem_sup.1 hDx
    -- `c = D(x − b)` lies in `C₀ ∩ range D = 0`
    have hcY : c ∈ s.Y := by
      rw [s.range_eq]
      exact ⟨x - b, by
        change D 0 (x - b) = c
        rw [map_sub, ← hcb]
        change c + D 0 b - D 0 b = c
        abel⟩
    have hc0 : c = 0 := (Submodule.disjoint_def.1 hCY.disjoint) c hc hcY
    have hxb : x - b ∈ LinearMap.ker Dl := by
      rw [LinearMap.mem_ker, map_sub]
      change D 0 x - D 0 b = 0
      rw [← hcb, hc0, zero_add]; exact sub_self _
    have hxB : x ∈ B := by
      have := B.add_mem (hker hxb) hb
      rwa [sub_add_cancel] at this
    exact (Submodule.disjoint_def.1 hBX0.disjoint) x hxB hx
  · intro w
    obtain ⟨c, hc, y, hy, rfl⟩ :=
      Submodule.mem_sup.1 (hCY.sup_eq_top ▸ Submodule.mem_top : w ∈ s.C ⊔ s.Y)
    rw [s.range_eq] at hy
    obtain ⟨e, rfl⟩ := hy
    obtain ⟨b, hb, x, hx, rfl⟩ :=
      Submodule.mem_sup.1 (hBX0.sup_eq_top ▸ Submodule.mem_top : e ∈ B ⊔ X)
    refine ⟨c + D 0 b, Submodule.add_mem_sup hc ⟨b, hb, rfl⟩, x, hx, ?_⟩
    change c + D 0 (b + x) = c + D 0 b + D 0 x
    rw [map_add, add_assoc]

variable {A Y : Submodule ℝ (F 0)}

/-- **`P ∘ D|X : X → Y'` is bijective** for a complement `A` of `D(X)` as above and the coordinates
`T : F ≅ A ⊕ Y'` of an sc-splitting `F = A ⊕ Y'`. -/
theorem bijective_splitScIso_snd (hAY : F.IsScSplitting A Y) [FiniteDimensional ℝ A]
    (hAs : A ≤ F.smooth) (D : E 0 →L[ℝ] F 0) (hinj : ∀ x ∈ X, D x ∈ A → x = 0)
    (hsurj : ∀ w : F 0, ∃ a ∈ A, ∃ x ∈ X, w = a + D x) :
    Bijective fun h : E.levelSub X 0 => (ScBanach.splitScIso hAs hAY 0 (D h)).2 := by
  have hsnd : ∀ v : F 0, (show F.levelSub Y 0 from (ScBanach.splitScIso hAs hAY 0 v).2).1 =
      v - (ScBanach.splitProjB hAY v : F 0) := ScBanach.splitScIso_zero_snd hAs hAY
  constructor
  · intro h h' hh
    have hv := congrArg Subtype.val hh
    change (show F.levelSub Y 0 from (ScBanach.splitScIso hAs hAY 0 (D h)).2).1 =
      (show F.levelSub Y 0 from (ScBanach.splitScIso hAs hAY 0 (D h')).2).1 at hv
    rw [hsnd, hsnd] at hv
    have hmem : D ((h : E 0) - h') ∈ A := by
      have : D ((h : E 0) - h') = (ScBanach.splitProjB hAY (D h) : F 0) -
          ScBanach.splitProjB hAY (D h') := by
        rw [map_sub]; exact sub_eq_sub_iff_sub_eq_sub.1 hv
      rw [this]
      exact A.sub_mem (ScBanach.splitProjB hAY _).2 (ScBanach.splitProjB hAY _).2
    have h0 := hinj _ (X.sub_mem h.2 h'.2) hmem
    exact Subtype.ext (sub_eq_zero.1 h0)
  · rintro ⟨y, hy⟩
    obtain ⟨a, ha, x, hx, hyax⟩ := hsurj y
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change (show F.levelSub Y 0 from (ScBanach.splitScIso hAs hAY 0 (D x)).2).1 = y
    rw [hsnd]
    have hy0 : ScBanach.splitProjB hAY y = 0 := ScBanach.splitProjB_apply_right hAY hy
    have hDx : D x = y - a := by rw [hyax]; abel
    rw [hDx, map_sub, hy0, zero_sub, ScBanach.splitProjB_apply_left hAY ⟨a, ha⟩]
    simp

end Target

/-! ### Moving conditions (1)–(3) into the coordinates -/

section Transport

variable {E F : ScBanach} {C U : Set (E 0)} {f : E 0 → F 0} {B X : Submodule ℝ (E 0)}
  {A Y : Submodule ℝ (F 0)} (hBX : E.IsScSplitting B X) [FiniteDimensional ℝ B]
  (hBs : B ≤ E.smooth) (hAY : F.IsScSplitting A Y) [FiniteDimensional ℝ A] (hAs : A ≤ F.smooth)

lemma liftB_zero_eq (b : B) : ScBanach.liftB hBs 0 b = b := by
  have := ScBanach.toBase_liftB hBs 0 b
  rwa [E.toBase_zero] at this

lemma splitScIso_symm_param (m : ℕ) (b : B) :
    (ScBanach.splitScIso hBs hBX m).symm
      ((b, 0) : ((ScBanach.const B).prod (E.ofSubspace hBX.2.1)) m) =
      ScBanach.liftB hBs m b := by
  change ScBanach.liftB hBs m b + (0 : E m) = _
  rw [add_zero]

lemma splitScIso_symm_fiber (m : ℕ) (x : (E.ofSubspace hBX.2.1) m) :
    (ScBanach.splitScIso hBs hBX m).symm
      (((0 : B), x) : ((ScBanach.const B).prod (E.ofSubspace hBX.2.1)) m) =
      (show E.levelSub X m from x).1 := by
  change ScBanach.liftB hBs m 0 + _ = _
  rw [map_zero, zero_add]
  rfl

omit [FiniteDimensional ℝ A] in
lemma mem_lvlSet_symm {E' : ScBanach} (S : ScIso E E') {k : ℕ} {p : E' k}
    (hp : p ∈ E'.lvlSet ((S 0).symm ⁻¹' U) k) : (S k).symm p ∈ E.lvlSet U k := by
  rw [ScBanach.mem_lvlSet, ScIso.symm_toBase_comm]; exact hp

include hBX hBs in
/-- `C` in the coordinates: `(S⁻¹)⁻¹(C) = (C ∩ B) ⊕ X`. -/
lemma symm_preimage_C (hC : IsPartialQuadrant E C) (hXC : (X : Set (E 0)) ⊆ C) :
    (ScBanach.splitScIso hBs hBX 0).symm ⁻¹' C =
      (Subtype.val ⁻¹' C : Set B) ×ˢ (univ : Set ((E.ofSubspace hBX.2.1) 0)) := by
  have h := splitScIso_preimage hC hBX hBs hXC
  ext p
  change (ScBanach.splitScIso hBs hBX 0).symm p ∈ C ↔ _
  conv_lhs => rw [← h]
  rw [mem_preimage, ContinuousLinearEquiv.apply_symm_apply]

include hBX hBs in
/-- `U` in the coordinates is relatively open in `(C ∩ B) ⊕ X`. -/
theorem isRelOpenInQuadrant_symm_preimage (hU : IsRelOpenInQuadrant E C U)
    (hXC : (X : Set (E 0)) ⊆ C) :
    IsRelOpenInQuadrant ((ScBanach.const B).prod (E.ofSubspace hBX.2.1))
      ((Subtype.val ⁻¹' C : Set B) ×ˢ (univ : Set ((E.ofSubspace hBX.2.1) 0)))
      ((ScBanach.splitScIso hBs hBX 0).symm ⁻¹' U) := by
  obtain ⟨O, hO, hUO⟩ := hU.relOpen
  refine ⟨isPartialQuadrant_split hU.isPartialQuadrant hBX hXC,
    (ScBanach.splitScIso hBs hBX 0).symm ⁻¹' O,
    hO.preimage (ScBanach.splitScIso hBs hBX 0).symm.continuous, ?_⟩
  rw [hUO, preimage_inter, symm_preimage_C hBX hBs hU.isPartialQuadrant hXC]

/-- **Condition (2) in the coordinates**: `CompactnessCondition371` for `f` gives the coordinate
`CompactnessCondition` for `g = T ∘ f ∘ S⁻¹`. -/
theorem compactnessCondition_conj (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    (hU' : IsScDomain ((ScBanach.const B).prod (E.ofSubspace hBX.2.1))
      ((ScBanach.splitScIso hBs hBX 0).symm ⁻¹' U)) (hf : IsScSmooth U f)
    (h2 : CompactnessCondition371 U f B X) :
    CompactnessCondition (Subtype.val ⁻¹' C : Set B)
      ((ScBanach.splitScIso hBs hBX 0).symm ⁻¹' U)
      (scIsoConjMap (ScBanach.splitScIso hBs hBX) (ScBanach.splitScIso hAs hAY) f) := by
  set S := ScBanach.splitScIso hBs hBX
  set T := ScBanach.splitScIso hAs hAY
  obtain ⟨r, hr, H⟩ := h2
  obtain ⟨O, hO, hUO⟩ := hU.relOpen
  have h0O : (0 : E 0) ∈ O := (hUO ▸ h0).1
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hO 0 h0O
  refine ⟨min r δ, lt_min hr hδ, fun m b b₀ η y z hb hb₀ hb₀r htend hηb hD hy hz => ?_⟩
  have hbU : ∀ j, ((b j, 0) : ((ScBanach.const B).prod (E.ofSubspace hBX.2.1)) (m + 1)) ∈
      ((ScBanach.const B).prod (E.ofSubspace hBX.2.1)).lvlSet ((S.lvl 0).symm ⁻¹' U) (m + 1) :=
    fun j => mem_lvlSet_param (hb j).2 (m + 1)
  have hmem : ∀ j, ScBanach.liftB hBs (m + 1) (b j) ∈ E.lvlSet U (m + 1) := fun j => by
    have := mem_lvlSet_symm S (hbU j)
    rwa [splitScIso_symm_param] at this
  have hb₀U : (b₀ : E 0) ∈ U := by
    rw [hUO]
    refine ⟨hball (mem_ball_zero_iff.2 ?_), hb₀⟩
    exact lt_of_lt_of_le hb₀r (min_le_right _ _)
  have hD' : ∀ j, levelDeriv (scDeriv U f) m (ScBanach.liftB hBs (m + 1) (b j))
      (show E.levelSub X m from η j).1 =
      (T m).symm (y j) + F.incl m ((T (m + 1)).symm (z j)) := fun j => by
    have h := hD j
    rw [levelDeriv_conjMap S T hU.isScDomain hU' hf m (hbU j), splitScIso_symm_param,
      splitScIso_symm_fiber] at h
    have h' := congrArg (T m).symm h
    rw [ContinuousLinearEquiv.symm_apply_apply, map_add] at h'
    rw [h']
    congr 1
    exact (T.symm.incl_comm m (z j)).symm
  obtain ⟨Mη, hMη⟩ := hηb
  obtain ⟨Mz, hMz⟩ := hz
  obtain ⟨η₀, φ, hφ, hconv⟩ := H m (fun j => ScBanach.liftB hBs (m + 1) (b j)) b₀
    (fun j => (show E.levelSub X m from η j).1) (fun j => (T m).symm (y j))
    (fun j => (T (m + 1)).symm (z j))
    (fun j => ⟨by rw [ScBanach.toBase_liftB]; exact (b j).2, hmem j⟩) b₀.2 hb₀U
    (lt_of_lt_of_le hb₀r (min_le_left _ _))
    (by
      simp only [ScBanach.toBase_liftB]
      exact (continuous_subtype_val.tendsto _).comp htend)
    (fun j => (η j).2) ⟨Mη, hMη⟩ hD'
    (by
      have := ((T m).symm.continuous.tendsto 0).comp hy
      rwa [map_zero] at this)
    ⟨‖(T (m + 1)).symm.toContinuousLinearMap‖ * Mz, fun j =>
      ((T (m + 1)).symm.toContinuousLinearMap.le_opNorm (z j)).trans
        (mul_le_mul_of_nonneg_left (hMz j) (norm_nonneg _))⟩
  have hη₀ : η₀ ∈ E.levelSub X m :=
    (E.isClosed_levelSub hBX.2.1.1 m).mem_of_tendsto hconv
      (Eventually.of_forall fun j => (η (φ j)).2)
  exact ⟨(⟨η₀, hη₀⟩ : E.levelSub X m), φ, hφ, tendsto_subtype_rng.2 hconv⟩

/-- **Condition (3) in the coordinates**: `DerivCondition371` for `f` gives the coordinate
`DerivCondition` for `g = T ∘ f ∘ S⁻¹`, with `ε` rescaled by `‖T_m‖ + 1`. -/
theorem derivCondition_conj (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsScDomain ((ScBanach.const B).prod (E.ofSubspace hBX.2.1))
      ((ScBanach.splitScIso hBs hBX 0).symm ⁻¹' U)) (hf : IsScSmooth U f)
    (h3 : DerivCondition371 U f B X) :
    DerivCondition (Subtype.val ⁻¹' C : Set B)
      ((ScBanach.splitScIso hBs hBX 0).symm ⁻¹' U)
      (scIsoConjMap (ScBanach.splitScIso hBs hBX) (ScBanach.splitScIso hAs hAY) f) := by
  set S := ScBanach.splitScIso hBs hBX
  set T := ScBanach.splitScIso hAs hAY
  intro m ε hε
  set c := ‖(T m).toContinuousLinearMap‖
  have hc : 0 ≤ c := norm_nonneg _
  obtain ⟨r, hr, H⟩ := h3 m (ε / (c + 1)) (div_pos hε (by positivity))
  refine ⟨r, hr, fun b _ hbr x hb0 hbx hxr h => ?_⟩
  set x' : E (m + 1) := (show E.levelSub X (m + 1) from x).1 with hx'
  set h' : E m := (show E.levelSub X m from h).1 with hh'
  have hsx : (S (m + 1)).symm
      ((b, x) : ((ScBanach.const B).prod (E.ofSubspace hBX.2.1)) (m + 1)) =
      ScBanach.liftB hBs (m + 1) b + x' := rfl
  have hbx' := mem_lvlSet_symm S hbx
  have hb0' := mem_lvlSet_symm S hb0
  rw [splitScIso_symm_param] at hb0'
  rw [hsx] at hbx'
  rw [levelDeriv_conjMap S T hU.isScDomain hU' hf m hb0,
    levelDeriv_conjMap S T hU.isScDomain hU' hf m hbx, ← map_sub, splitScIso_symm_param,
    splitScIso_symm_fiber, hsx]
  have hH := H (ScBanach.liftB hBs (m + 1) b) (by rw [ScBanach.toBase_liftB]; exact b.2)
    (by rw [ScBanach.toBase_liftB]; exact hbr) x' (show E.levelSub X (m + 1) from x).2 hb0' hbx'
    hxr h' (show E.levelSub X m from h).2
  calc ‖(T m) (levelDeriv (scDeriv U f) m (ScBanach.liftB hBs (m + 1) b) h' -
        levelDeriv (scDeriv U f) m (ScBanach.liftB hBs (m + 1) b + x') h')‖
      ≤ c * ‖levelDeriv (scDeriv U f) m (ScBanach.liftB hBs (m + 1) b) h' -
        levelDeriv (scDeriv U f) m (ScBanach.liftB hBs (m + 1) b + x') h'‖ :=
        (T m).toContinuousLinearMap.le_opNorm _
    _ ≤ c * (ε / (c + 1) * ‖h'‖) := mul_le_mul_of_nonneg_left hH hc
    _ ≤ ε * ‖h‖ := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

end Transport


/-! ### Theorem 3.7.1 for a general sc-splitting -/

section Main

variable {E F : ScBanach} {C U : Set (E 0)} {f : E 0 → F 0} {B X : Submodule ℝ (E 0)}

/-- **Theorem 3.7.1 (preprint 3.58) (Basic Germ Criterion)**, 2021 p. 140, in the text's form: let
`U` be a relatively open neighbourhood of `0` in a partial quadrant `C ⊆ E` and `f : U → F`
sc-smooth such that

1. at every smooth point `x ∈ U`, `Df(x)` is sc-Fredholm (`h1F`) with index independent of `x`
   (`h1I`);
2. there is an sc-splitting `E = B ⊕ X` with `B` finite-dimensional, `ker Df(0) ⊆ B` and `X ⊆ C`,
   with the compactness property (`CompactnessCondition371`);
3. the estimate for `D₂f` (`DerivCondition371`).

Then `f − s`, `s = f(0)`, is conjugated near `0` to a basic germ: on `U ∩ V` for an open `V ∋ 0`.
Proof: the reduction to the coordinates of the text's proof (`theorem_3_7_1`), with
`S : E ≅ B ⊕ X`, `T : F ≅ A ⊕ Y'` and `g = T ∘ f ∘ S⁻¹`. -/
theorem theorem_3_7_1_general (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    (hf : IsScSmooth U f)
    (h1F : ∀ (x : E 1) (hx : x ∈ E.lvlSet U 1) (hs : x ∈ E.smoothLvl 1),
      IsScFredholm (derivOpAt hf hx hs))
    (h1I : ∀ (x : E 1) (hx : x ∈ E.lvlSet U 1) (hs : x ∈ E.smoothLvl 1)
      (x' : E 1) (hx' : x' ∈ E.lvlSet U 1) (hs' : x' ∈ E.smoothLvl 1),
      scIndex (derivOpAt hf hx hs) = scIndex (derivOpAt hf hx' hs'))
    (hBX : E.IsScSplitting B X) [FiniteDimensional ℝ B]
    (hker : LinearMap.ker (scDeriv U f 0 : E 0 →ₗ[ℝ] F 0) ≤ B) (hXC : (X : Set (E 0)) ⊆ C)
    (h2 : CompactnessCondition371 U f B X) (h3 : DerivCondition371 U f B X) :
    ∃ V : Set (E 0), IsOpen V ∧ (0 : E 0) ∈ V ∧
      IsConjugateToBasicGerm (U ∩ V) fun u => f u - f 0 := by
  have hBs : B ≤ E.smooth := (E.proposition_1_1_7_iff B).1 hBX.1
  -- the point `0` and `Df(0)`
  have hx0 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have hs0 : (0 : E 1) ∈ E.smoothLvl 1 := by
    change E.toBase 1 0 ∈ E.smooth
    rw [map_zero]; exact E.smooth.zero_mem
  set D := derivOpAt hf hx0 hs0
  have hD0 : D 0 = scDeriv U f 0 := derivOpAt_zero hf hx0 hs0
  obtain ⟨A, hAfin, hAs, hinj, hsurj⟩ := exists_targetSplitting371 hBX hBs D (h1F _ hx0 hs0)
    (by rw [hD0]; exact hker)
  obtain ⟨Y, hAY⟩ := F.proposition_1_1_7 A hAs
  -- the coordinates
  set S := ScBanach.splitScIso hBs hBX
  set T := ScBanach.splitScIso hAs hAY
  set Ct : Set B := Subtype.val ⁻¹' C
  have hC' : IsPartialQuadrant (ScBanach.const B) Ct :=
    isPartialQuadrant_of_isScSplitting hU.isPartialQuadrant hBX hXC
  have hU' := isRelOpenInQuadrant_symm_preimage hBX hBs hU hXC
  have h0' : (0 : ((ScBanach.const B).prod (E.ofSubspace hBX.2.1)) 0) ∈ (S 0).symm ⁻¹' U := by
    change (S 0).symm 0 ∈ U
    rw [map_zero]; exact h0
  have hg := isScSmooth_conjMap S T hU.isScDomain hU'.isScDomain hf
  -- condition (1) in the coordinates
  have hfred : ∀ (b : B)
      (hb : ((b, 0) : (ScBanach.paramProd B (E.ofSubspace hBX.2.1)) 0) ∈ (S 0).symm ⁻¹' U),
      ∃ (x : E 1) (hx : x ∈ E.lvlSet U 1) (hs : x ∈ E.smoothLvl 1),
        IsScFredholm (derivParamOp hg b hb) ∧
          scIndex (derivParamOp hg b hb) = scIndex (derivOpAt hf hx hs) := by
    intro b hb
    have hp := mem_lvlSet_param hb 1
    have hx := mem_lvlSet_symm S hp
    have hs : (S 1).symm ((b, 0) : ((ScBanach.const B).prod (E.ofSubspace hBX.2.1)) 1) ∈
        E.smoothLvl 1 := by
      change E.toBase 1 _ ∈ E.smooth
      rw [ScIso.symm_toBase_comm, ScBanach.paramProd_toBase, map_zero, splitScIso_symm_param,
        liftB_zero_eq]
      exact hBs b.2
    refine ⟨_, hx, hs, isScFredholm_of_conj S T (fun v => ?_) (h1F _ hx hs)⟩
    rw [derivParamOp_zero, derivOpAt_zero,
      scDeriv_conjMap S T hU.isScDomain hU'.isScDomain hf hp]
  have h1' : ∀ b ∈ Ct, ∀ hb : ((b, 0) : (ScBanach.paramProd B (E.ofSubspace hBX.2.1)) 0) ∈
      (S 0).symm ⁻¹' U, IsScFredholm (derivParamOp hg b hb) ∧
        scIndex (derivParamOp hg b hb) = scIndex (derivParamOp hg 0 h0') := by
    intro b _ hb
    obtain ⟨x, hx, hs, hF, hI⟩ := hfred b hb
    obtain ⟨x', hx', hs', -, hI'⟩ := hfred 0 h0'
    exact ⟨hF, by rw [hI, hI', h1I x hx hs x' hx' hs']⟩
  -- condition (2): `P ∘ Dg(0)|X` is bijective
  have hz : (0 : ((ScBanach.const B).prod (E.ofSubspace hBX.2.1)) 1) ∈
      ((ScBanach.const B).prod (E.ofSubspace hBX.2.1)).lvlSet ((S 0).symm ⁻¹' U) 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0'
  have h2bij : Bijective fun h : (E.ofSubspace hBX.2.1) 0 =>
      (scDeriv (E := ScBanach.paramProd B (E.ofSubspace hBX.2.1))
        (F := ScBanach.paramProd A (F.ofSubspace hAY.2.1)) ((S 0).symm ⁻¹' U) (scIsoConjMap S T f) 0
        ((0 : B), h)).2 := by
    have : (fun h : (E.ofSubspace hBX.2.1) 0 =>
        (scDeriv (E := ScBanach.paramProd B (E.ofSubspace hBX.2.1))
          (F := ScBanach.paramProd A (F.ofSubspace hAY.2.1)) ((S 0).symm ⁻¹' U)
          (scIsoConjMap S T f) 0 ((0 : B), h)).2) =
        fun h : E.levelSub X 0 => (T 0 (scDeriv U f 0 h)).2 := by
      funext h
      rw [scDeriv_conjMap S T hU.isScDomain hU'.isScDomain hf hz, map_zero,
        splitScIso_symm_fiber]
    rw [this]
    exact bijective_splitScIso_snd hAY hAs (scDeriv U f 0) (by rw [← hD0]; exact hinj)
      (by rw [← hD0]; exact hsurj)
  have h2cpt := compactnessCondition_conj hBX hBs hAY hAs hU h0 hU'.isScDomain hf h2
  have h3' := derivCondition_conj hBX hBs hAY hAs hU hU'.isScDomain hf h3
  obtain ⟨Vo, hVo, hVo0, L, -, -, -, hconj⟩ := theorem_3_7_1 hC' hU' h0' hg h1' h2bij h2cpt h3'
  -- back through `S`, `T`
  set V := (S 0) ⁻¹' (Vo ×ˢ (univ : Set ((E.ofSubspace hBX.2.1) 0))) with hVdef
  have hVo' : IsOpen V := (hVo.prod isOpen_univ).preimage (S 0).continuous
  have hV0 : (0 : E 0) ∈ V := by
    rw [hVdef, mem_preimage, map_zero]; exact ⟨hVo0, mem_univ _⟩
  refine ⟨V, hVo', hV0, ?_⟩
  have himg : S 0 '' (U ∩ V) = (S 0).symm ⁻¹' U ∩ Vo ×ˢ univ := by
    rw [ContinuousLinearEquiv.image_eq_preimage_symm, preimage_inter]
    congr 1
    ext p
    simp only [hVdef, mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
  refine IsConjugateToBasicGerm.of_scIso (hU.inter_isOpen hVo') S T
    (by rw [himg]; exact hU'.inter_isOpen (hVo.prod isOpen_univ)) ?_
  rw [himg]
  refine hconj.congr fun u _ => ?_
  simp only [shiftedGerm, scIsoConjMap, map_zero, map_sub]

end Main

end Polyfold
