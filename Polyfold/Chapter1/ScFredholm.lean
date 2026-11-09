import Polyfold.Chapter1.ScBanach
import Polyfold.Chapter1.FredholmPerturbation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.1,
Definition 1.1.9 (preprint 1.8), Propositions 1.1.10 and 1.1.11 (preprint 1.9 and 1.10), with the proof of Appendix §1.4.1.

# Sc-Fredholm operators

## The text, paraphrased

(Definition 1.1.9 (preprint 1.8)) An sc-operator `T : E → F` is sc-Fredholm if there are sc-splittings
`E = K ⊕ X`, `F = C ⊕ Y` with (1) `K = ker T` finite-dimensional, (2) `C` finite-dimensional and
`Y = T(E)`, (3) `T : X → Y` an sc-isomorphism.  Then `K ⊆ E_∞`, `T(X_m) = Y_m`,
`E_m = K ⊕ X_m`, `F = C ⊕ T(E_m)`, and `ind T = dim K − dim C`.  (Proposition 1.1.10 (preprint 1.9)) `T` is
regularizing: `T e ∈ F_m` implies `e ∈ E_m`.  (Proposition 1.1.11 (preprint 1.10)) If `T` is sc-Fredholm and `S` is
an sc⁺-operator then `T + S` is sc-Fredholm.  (§1.4.1) *Proof*: `T + S : E_m → F_m` is Fredholm
on every level (compact perturbation); the kernels `K_m` of these operators all coincide
(`x ∈ K_m` gives `T x = −S x ∈ F_{m+1}`, so `x ∈ E_{m+1}` by Proposition 1.1.10 (preprint 1.9)), so `K := K₀` is a
finite-dimensional subspace of `E_∞` and splits `E` by Proposition 1.1.7 (preprint 1.6).  `Y := (T+S)(E)` is closed,
and `Y_∞` is dense in `Y_m` (for `y = (T+S)e ∈ Y_m`, `e ∈ E_m` by regularity, and `e_n → e` with
`e_n ∈ E_∞` gives `(T+S)e_n → y`).  Finally the projection `p : F → F/Y` onto a finite-dimensional
space maps the dense `F_∞` onto `F/Y`, so a basis of `F/Y` lifts to `F_∞`; its span `C` gives
`F_m = Y_m ⊕ C`.

## What is formalized

* `Polyfold.ScFredholmSplitting T` (the data of **Definition 1.1.9 (preprint 1.8)**): `K`, `X`, `C`, `Y` with the
  two sc-splittings, `K = ker T₀`, `Y = range T₀`, `K`, `C` finite-dimensional, and `T_m` a
  bijection `X_m → Y_m` for every `m`;
  `Polyfold.IsScFredholm T := Nonempty (ScFredholmSplitting T)`;
  `ScFredholmSplitting.index`, and `Polyfold.scIndex T = dim ker T₀ − dim (F₀/range T₀)`, which
  equals the index of every splitting (`ScFredholmSplitting.index_eq`).
* `ScFredholmSplitting.K_le_smooth` (`K ⊆ E_∞`), `ScFredholmSplitting.isFredholm` (`T_m` is
  Fredholm on every level, the fact used at the start of §1.4.1).
* `Polyfold.proposition_1_1_10` (**Proposition 1.1.10 (preprint 1.9)**, regularizing).
* `Polyfold.proposition_1_1_11_preprint` (**Proposition 1.1.11 (preprint 1.10)**, compact perturbation), with the proof of
  §1.4.1 on top of `Polyfold.isFredholm_add_isCompactOperator`.

## What the text leaves implicit, and the choices made

* "`T : X → Y` is an sc-isomorphism" is taken as: `T_m` restricts to a bijection `X_m → Y_m` for
  every `m` (`Set.BijOn`).  The continuity of the inverses is automatic (open mapping theorem on
  the closed subspaces `X_m`, `Y_m`), so nothing is lost.
* The classical fact "a compact perturbation of a Fredholm operator is Fredholm", invoked in the
  first line of §1.4.1, is not in Mathlib; it is proved in `FredholmPerturbation.lean`.
* §1.4.1 writes "if `y ∈ Y_m` then `y = (T+S)(e)` ... since `T` is regularizing, `e ∈ E_m`".
  This needs a bootstrap: `S e ∈ F₁` only, so `T e = y − S e ∈ F₁`, hence `e ∈ E₁`, hence
  `S e ∈ F₂`, …, and `e ∈ E_m` after `m` steps (`ScPlus.regularizing_add`).  The same bootstrap
  is behind `K_m = K_{m+1}`.
* The complement `C` is built from a linear right inverse of `F₀ → F₀/Y` taking values in the
  smooth points (`LinearMap.exists_rightInverse_of_surjective`) instead of a lifted basis.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### Level kernels and ranges of sc-operators -/

namespace ScOperator

variable (T : ScOperator E F)

/-- The kernel of `T_m` is the level-`m` part of the kernel of `T₀`. -/
lemma ker_lvl (m : ℕ) : LinearMap.ker (T m : E m →ₗ[ℝ] F m) =
    E.levelSub (LinearMap.ker (T 0 : E 0 →ₗ[ℝ] F 0)) m := by
  ext x
  rw [LinearMap.mem_ker, ScBanach.mem_levelSub, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_coe, ← T.toBase_comm]
  constructor
  · intro h; rw [h, map_zero]
  · intro h; exact F.toBase_injective m (by rw [h, map_zero])

/-- `T_m` maps `E_m` into the level-`m` part of the range of `T₀`. -/
lemma range_lvl_le (m : ℕ) : LinearMap.range (T m : E m →ₗ[ℝ] F m) ≤
    F.levelSub (LinearMap.range (T 0 : E 0 →ₗ[ℝ] F 0)) m := by
  rintro _ ⟨x, rfl⟩
  rw [ScBanach.mem_levelSub, ContinuousLinearMap.coe_coe, T.toBase_comm]
  exact LinearMap.mem_range_self _ _

end ScOperator

/-- An sc⁺-operator raises the level: if `x ∈ E_m` then `S x ∈ F_{m+1}`. -/
lemma ScPlus.toScOperator_mem_range_toBase_succ (S : ScPlus E F) {m : ℕ} {x : E 0}
    (hx : x ∈ range (E.toBase m)) : S.toScOperator 0 x ∈ range (F.toBase (m + 1)) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨S m y, ?_⟩
  rw [ScPlus.toScOperator_apply, ← S.toBase_comm m y, F.shift_toBase]
  rfl

lemma ScBanach.range_toBase_succ_le (E : ScBanach) (m : ℕ) :
    range (E.toBase (m + 1)) ⊆ range (E.toBase m) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨E.incl m x, rfl⟩

/-! ### Definition 1.1.9 (preprint 1.8) -/

/-- The data of **Definition 1.1.9 (preprint 1.8)**: sc-splittings `E = K ⊕ X`, `F = C ⊕ Y` with `K = ker T`
finite-dimensional, `C` finite-dimensional, `Y = T(E)`, and `T : X_m → Y_m` bijective for every
`m` (an sc-isomorphism `X → Y`; the continuity of the inverses is automatic). -/
structure ScFredholmSplitting (T : ScOperator E F) where
  /-- The kernel `K`. -/
  K : Submodule ℝ (E 0)
  /-- The sc-complement `X` of the kernel. -/
  X : Submodule ℝ (E 0)
  /-- The finite-dimensional complement `C` of the range. -/
  C : Submodule ℝ (F 0)
  /-- The range `Y`. -/
  Y : Submodule ℝ (F 0)
  splitE : E.IsScSplitting K X
  splitF : F.IsScSplitting C Y
  ker_eq : K = LinearMap.ker (T 0 : E 0 →ₗ[ℝ] F 0)
  finite_K : FiniteDimensional ℝ K
  finite_C : FiniteDimensional ℝ C
  range_eq : Y = LinearMap.range (T 0 : E 0 →ₗ[ℝ] F 0)
  bijOn : ∀ m, BijOn (T m) (E.levelSub X m) (F.levelSub Y m)

/-- An sc-operator is **sc-Fredholm** (Definition 1.1.9 (preprint 1.8)) if it admits an `ScFredholmSplitting`. -/
def IsScFredholm (T : ScOperator E F) : Prop := Nonempty (ScFredholmSplitting T)

/-- The index `dim K − dim C` of an sc-Fredholm splitting. -/
def ScFredholmSplitting.index {T : ScOperator E F} (s : ScFredholmSplitting T) : ℤ :=
  (finrank ℝ s.K : ℤ) - finrank ℝ s.C

/-- The index of an sc-operator, `dim ker T₀ − dim (F₀ / range T₀)`. -/
def scIndex (T : ScOperator E F) : ℤ :=
  (finrank ℝ (LinearMap.ker (T 0 : E 0 →ₗ[ℝ] F 0)) : ℤ) -
    finrank ℝ (F 0 ⧸ LinearMap.range (T 0 : E 0 →ₗ[ℝ] F 0))

namespace ScFredholmSplitting

variable {T : ScOperator E F} (s : ScFredholmSplitting T)

/-- The index does not depend on the splitting. -/
lemma index_eq : s.index = scIndex T := by
  unfold index scIndex
  have h := (s.splitF.2.2 0).symm
  rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at h
  rw [s.ker_eq, ← s.range_eq, (Submodule.quotientEquivOfIsCompl _ _ h).finrank_eq]

/-- The kernel of an sc-Fredholm operator consists of smooth points (the remark after
Definition 1.1.9 (preprint 1.8), by Proposition 1.1.7 (preprint 1.6)). -/
lemma K_le_smooth : s.K ≤ E.smooth :=
  haveI := s.finite_K
  (E.proposition_1_1_7_iff s.K).1 s.splitE.1

lemma ker_lvl (m : ℕ) : LinearMap.ker (T m : E m →ₗ[ℝ] F m) = E.levelSub s.K m := by
  rw [T.ker_lvl, s.ker_eq]

lemma range_lvl (m : ℕ) : LinearMap.range (T m : E m →ₗ[ℝ] F m) = F.levelSub s.Y m := by
  refine le_antisymm (s.range_eq ▸ T.range_lvl_le m) fun y hy => ?_
  obtain ⟨x, -, rfl⟩ := (s.bijOn m).surjOn hy
  exact LinearMap.mem_range_self _ _

/-- `T_m : E_m → F_m` is a Fredholm operator for every `m` (the first line of §1.4.1). -/
lemma isFredholm (s : ScFredholmSplitting T) (m : ℕ) : (T m).IsFredholm := by
  have := s.finite_K
  have := s.finite_C
  refine isFredholm_of_banach (T m) ?_ ?_ ?_
  · rw [s.ker_lvl m]
    exact FiniteDimensional.of_injective ((E.toBase m : E m →ₗ[ℝ] E 0).restrict
      (p := E.levelSub s.K m) (q := s.K) fun _ hx => hx)
      fun x y hxy => Subtype.ext (E.toBase_injective m (congrArg Subtype.val hxy))
  · rw [s.range_lvl m]
    exact F.isClosed_levelSub s.splitF.2.1.1 m
  · rw [s.range_lvl m]
    have hfin : FiniteDimensional ℝ (F.levelSub s.C m) :=
      FiniteDimensional.of_injective ((F.toBase m : F m →ₗ[ℝ] F 0).restrict
        (p := F.levelSub s.C m) (q := s.C) fun _ hx => hx)
        fun x y hxy => Subtype.ext (F.toBase_injective m (congrArg Subtype.val hxy))
    exact Submodule.FG.cofg_of_isCompl (s.splitF.2.2 m)
      ((Submodule.fg_iff_finiteDimensional _).2 hfin)

end ScFredholmSplitting

/-! ### Proposition 1.1.10 (preprint 1.9) -/

/-- **Proposition 1.1.10 (preprint 1.9)**: an sc-Fredholm operator is regularizing: if `T e ∈ F_m` then `e ∈ E_m`. -/
theorem proposition_1_1_10 {T : ScOperator E F} (s : ScFredholmSplitting T) {e : E 0} {m : ℕ}
    (he : T 0 e ∈ range (F.toBase m)) : e ∈ range (E.toBase m) := by
  obtain ⟨y, hy⟩ := he
  -- `y = c_m + T_m x'` with `c_m ∈ C_m`, `x' ∈ X_m`
  obtain ⟨c, hc, y', hy', rfl⟩ := Submodule.mem_sup.1
    ((s.splitF.2.2 m).sup_eq_top ▸ Submodule.mem_top (x := y))
  obtain ⟨x', hx', rfl⟩ := (s.bijOn m).surjOn hy'
  -- `T (e - x') = c ∈ C ∩ Y = 0`
  have h1 : T 0 (e - E.toBase m x') = F.toBase m c := by
    rw [map_sub, ← T.toBase_comm, ← hy, map_add, add_sub_cancel_right]
  have hcC : F.toBase m c ∈ s.C := hc
  have hcY : F.toBase m c ∈ s.Y := by
    rw [s.range_eq, ← h1]; exact LinearMap.mem_range_self _ _
  have hc0 : F.toBase m c = 0 := (Submodule.disjoint_def.1 (s.splitF.2.2 0).disjoint) _ hcC hcY
  -- hence `e - x' ∈ K ⊆ E_∞`
  have hK : e - E.toBase m x' ∈ s.K := by
    rw [s.ker_eq, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, h1, hc0]
  obtain ⟨z, hz⟩ := (ScScale.mem_smooth_iff _).1 (s.K_le_smooth hK) m
  exact ⟨z + x', by rw [map_add, hz, sub_add_cancel]⟩

/-! ### Proposition 1.1.11 (preprint 1.10) -/

/-- The bootstrap behind §1.4.1: if `T` is sc-Fredholm and `S` is sc⁺, then `T + S` is
regularizing. -/
lemma ScPlus.regularizing_add {T : ScOperator E F} (s : ScFredholmSplitting T) (S : ScPlus E F)
    {e : E 0} : ∀ {m : ℕ}, (T + S.toScOperator) 0 e ∈ range (F.toBase m) → e ∈ range (E.toBase m)
  | 0, _ => ⟨e, rfl⟩
  | m + 1, he => by
    have he' : e ∈ range (E.toBase m) :=
      ScPlus.regularizing_add s S (F.range_toBase_succ_le m he)
    have hS : S.toScOperator 0 e ∈ range (F.toBase (m + 1)) :=
      S.toScOperator_mem_range_toBase_succ he'
    have hT : T 0 e ∈ range (F.toBase (m + 1)) := by
      have : T 0 e = (T + S.toScOperator) 0 e - S.toScOperator 0 e := by
        rw [ScOperator.add_apply, add_sub_cancel_right]
      obtain ⟨a, ha⟩ := he
      obtain ⟨b, hb⟩ := hS
      exact ⟨a - b, by rw [this, map_sub, ha, hb]⟩
    exact proposition_1_1_10 s hT

/-- **Proposition 1.1.11 (preprint 1.10) (Compact Perturbation)**: if `T : E → F` is sc-Fredholm and `S : E → F` is
an sc⁺-operator, then `T + S` is sc-Fredholm. -/
theorem proposition_1_1_11_preprint {T : ScOperator E F} (hT : IsScFredholm T) (S : ScPlus E F) :
    IsScFredholm (T + S.toScOperator) := by
  obtain ⟨s⟩ := hT
  set T' := T + S.toScOperator with hT'
  -- `T' + S : E_m → F_m` is Fredholm for every `m`
  have hFred : ∀ m, (T' m).IsFredholm := fun m => by
    have : T' m = T m + S.toScOperator m := rfl
    rw [this]
    exact isFredholm_add_isCompactOperator (s.isFredholm m) (S.isCompactOperator m)
  -- the kernel `K'` is finite-dimensional and consists of smooth points
  set K' := LinearMap.ker (T' 0 : E 0 →ₗ[ℝ] F 0) with hK'
  have hK'fin : FiniteDimensional ℝ K' := (hFred 0).finite_ker
  have hK'smooth : K' ≤ E.smooth := by
    intro x hx
    rw [ScScale.mem_smooth_iff]
    intro m
    have hx0 : T' 0 x = 0 := hx
    exact ScPlus.regularizing_add s S (m := m) (e := x) (by rw [hx0]; exact ⟨0, map_zero _⟩)
  obtain ⟨X', hX'⟩ := E.proposition_1_1_7 K' hK'smooth
  -- the range `Y'` is closed and its smooth points are dense on every level
  set Y' := LinearMap.range (T' 0 : E 0 →ₗ[ℝ] F 0) with hY'
  have hY'cl : IsClosed (Y' : Set (F 0)) := (hFred 0).isClosed_range
  have hY'lvl : ∀ m, LinearMap.range (T' m : E m →ₗ[ℝ] F m) = F.levelSub Y' m := by
    intro m
    refine le_antisymm (T'.range_lvl_le m) fun y hy => ?_
    rw [ScBanach.mem_levelSub] at hy
    obtain ⟨e, he⟩ := hy
    obtain ⟨e', rfl⟩ := ScPlus.regularizing_add s S (m := m) (e := e) ⟨y, he.symm⟩
    refine ⟨e', F.toBase_injective m ?_⟩
    rw [ContinuousLinearMap.coe_coe, T'.toBase_comm]
    exact he
  have hY'sc : F.IsScSubspace Y' := by
    refine ⟨hY'cl, fun m y hy => ?_⟩
    rw [SetLike.mem_coe, ← hY'lvl m] at hy
    obtain ⟨e, rfl⟩ := hy
    have hcl : e ∈ closure (E.smoothLvl m) := by
      rw [(E.dense_smooth m).closure_eq]; exact mem_univ _
    refine closure_mono ?_ (image_closure_subset_closure_image (T' m).continuous ⟨e, hcl, rfl⟩)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨?_, T'.mapsTo_smoothLvl m hz⟩
    rw [SetLike.mem_coe, ← hY'lvl m]
    exact LinearMap.mem_range_self _ _
  -- the complement `C'`: a right inverse of `F₀ → F₀/Y'` with values in the smooth points
  have hQfin : FiniteDimensional ℝ (F 0 ⧸ Y') := (hFred 0).finite_coker
  set p := Y'.mkQ with hp
  have hpsurj : LinearMap.range (p.domRestrict F.smooth) = ⊤ := by
    -- `p(F_∞)` is a dense subspace of the finite-dimensional `F₀/Y'`
    have hdense : Dense ((LinearMap.range (p.domRestrict F.smooth) : Submodule ℝ (F 0 ⧸ Y')) :
        Set (F 0 ⧸ Y')) := by
      have h1 : DenseRange Y'.mkQL := (Submodule.mkQ_surjective _).denseRange
      have h2 : Dense (Y'.mkQL '' (F.smooth : Set (F 0))) :=
        h1.dense_image Y'.mkQL.continuous (by rw [← ScScale.smoothLvl_zero]; exact F.dense_smooth 0)
      refine h2.mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hcl : IsClosed ((LinearMap.range (p.domRestrict F.smooth) : Submodule ℝ (F 0 ⧸ Y')) :
        Set (F 0 ⧸ Y')) := Submodule.closed_of_finiteDimensional _
    rw [← Submodule.coe_eq_univ, ← hcl.closure_eq, hdense.closure_eq]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective (p.domRestrict F.smooth) hpsurj
  set σ : (F 0 ⧸ Y') →ₗ[ℝ] F 0 := F.smooth.subtype ∘ₗ g with hσ
  have hpσ : ∀ q, p (σ q) = q := fun q => by
    have := LinearMap.congr_fun hg q
    simpa [σ] using this
  set C' := LinearMap.range σ with hC'
  have hC'smooth : C' ≤ F.smooth := by
    rintro _ ⟨q, rfl⟩
    exact (g q).2
  have hC'fin : FiniteDimensional ℝ C' := inferInstance
  -- `F₀ = Y' ⊕ C'` and `F_m = Y'_m ⊕ C'_m`
  have hcompl : ∀ m, IsCompl (F.levelSub Y' m) (F.levelSub C' m) := by
    intro m
    refine ⟨Submodule.disjoint_def.2 fun x hx hx' => ?_,
      Submodule.codisjoint_iff_exists_add_eq.2 fun z => ?_⟩
    · rw [ScBanach.mem_levelSub] at hx hx'
      obtain ⟨q, hq⟩ := hx'
      have h0 : (Submodule.Quotient.mk (F.toBase m x) : F 0 ⧸ Y') = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hx
      have : q = 0 := by rw [← hpσ q, hq]; exact h0
      apply F.toBase_injective m
      rw [← hq, this, map_zero, map_zero]
    · obtain ⟨c, hc⟩ := (ScScale.mem_smooth_iff _).1 (hC'smooth (LinearMap.mem_range_self σ
        (Submodule.Quotient.mk (F.toBase m z)))) m
      refine ⟨z - c, c, ?_, ?_, sub_add_cancel z c⟩
      · rw [ScBanach.mem_levelSub, map_sub, hc, ← Submodule.Quotient.mk_eq_zero (p := Y'),
          Submodule.Quotient.mk_sub]
        have : (Submodule.Quotient.mk (σ (Submodule.Quotient.mk (F.toBase m z))) : F 0 ⧸ Y') =
            Submodule.Quotient.mk (F.toBase m z) := hpσ _
        rw [this, sub_self]
      · rw [ScBanach.mem_levelSub, hc]
        exact LinearMap.mem_range_self σ _
  have hsplitF : F.IsScSplitting C' Y' :=
    ⟨(F.proposition_1_1_7_iff C').2 hC'smooth, hY'sc, fun m => (hcompl m).symm⟩
  -- the bijections `X'_m → Y'_m`
  refine ⟨⟨K', X', C', Y', hX', hsplitF, rfl, hK'fin, hC'fin, rfl, fun m => ⟨?_, ?_, ?_⟩⟩⟩
  · intro x _
    rw [SetLike.mem_coe, ScBanach.mem_levelSub, T'.toBase_comm]
    exact LinearMap.mem_range_self _ _
  · intro x hx x' hx' hxx'
    have hker : x - x' ∈ LinearMap.ker (T' m : E m →ₗ[ℝ] F m) := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hxx', sub_self]
    rw [T'.ker_lvl] at hker
    have hX : x - x' ∈ E.levelSub X' m := Submodule.sub_mem _ hx hx'
    have := (Submodule.disjoint_def.1 (hX'.2.2 m).disjoint) _ hker hX
    exact sub_eq_zero.1 this
  · intro y hy
    rw [← hY'lvl m] at hy
    obtain ⟨e, rfl⟩ := hy
    obtain ⟨k, hk, x, hx, rfl⟩ := Submodule.mem_sup.1
      ((hX'.2.2 m).sup_eq_top ▸ Submodule.mem_top (x := e))
    refine ⟨x, hx, ?_⟩
    have hk0 : T' m k = 0 := by
      have : k ∈ LinearMap.ker (T' m : E m →ₗ[ℝ] F m) := by rw [T'.ker_lvl]; exact hk
      exact this
    rw [ContinuousLinearMap.coe_coe, map_add, hk0, zero_add]

end Polyfold
