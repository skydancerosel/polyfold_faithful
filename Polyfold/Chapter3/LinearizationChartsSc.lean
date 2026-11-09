import Polyfold.Chapter3.FredholmGermLinearizationSc
import Polyfold.Chapter3.LinearizationCharts
import Polyfold.Chapter3.GlobalIFTIndex

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and §3.6:
**condition (3) of a filler on every level at a zero**, **the converse of Proposition 3.1.5 (preprint 3.5) in sc
form**, and **the linearization of an sc-Fredholm section at a zero is sc-Fredholm in every strong
bundle chart** (Proposition 3.6.5 (preprint 3.52) and Theorem 3.1.22 (preprint 3.19) in the chart-intrinsic form of the round-trip
statements V3.46 and V3.96, and the index `IndexAt` of V3.98).  Findings, Chapter 3, items
237–239.

# sc-Fredholm linearizations in every chart

## The text, paraphrased

(Definition 3.1.4 (preprint 3.4) (3)) For a filler `g` of `f : O → K` the linearization of `y ↦ [1 − ρ(r(y))]g(y)`
at `0`, restricted to `ker Dr(0)`, is a topological linear isomorphism onto `ker ρ(0)`.
(Proposition 3.1.5 (preprint 3.5)) `Tf(0)` is Fredholm iff `Dg(0)` is, with the same index.  (Proposition 3.6.5 (preprint 3.52))
At a zero `x` of an sc-Fredholm section, `Tf(x) : T_xX → Y_x` is an sc-Fredholm operator.
(Theorem 3.1.22 (preprint 3.19)) "`f'(x₀)` is an sc-Fredholm operator".  The text defines `f'(x)` in the chart of the
germ, centred at `x`, and treats the linearization as independent of the chart.

## What is formalized

* Level arithmetic (`ScBanach.add_mem_range_toBase`, `ScBanach.sub_mem_range_toBase`,
  `ScBanach.neg_mem_range_toBase_iff`, `IsScOperator.mem_range_toBase`).
  `Polyfold.ScOperator.exists_sub_mem_smooth`: if `T₀` is Fredholm, every `w ∈ F₀` is
  `T₀e + c` with `c` smooth (the range of `T₀` has a complement spanned by smooth points);
  `ScOperator.IsRegularizing.bijective` and `Polyfold.ScIso.ofBijective` (a regularizing
  sc-operator bijective on level `0` is an sc-isomorphism);
  `Polyfold.ScOperator.isFredholm_restrict_zero_iff` (the level-`0` map of
  `ScOperator.restrict` is Fredholm iff the underlying bounded operator `A → B` is, with the same
  index).
* `StrongRetr.isScSubspace_ker_scDeriv_r`, `StrongRetr.isScSubspace_ker_ρCLM`: `ker Dr(0)` and
  `ker ρ(0)` are sc-subspaces (the complements of the sc-projections `Dr(0)`, `ρ(0)`, Lemma 2.B);
  at any smooth point `z` of the retract: `StrongRetr.isScOperator_ρCLM_of_mem_smooth`,
  `StrongRetr.isScSubspace_range_ρCLM_of_mem_smooth` (`K_z = ρ(z)F`),
  `StrongRetr.isScOperator_scDeriv_r_at`, `StrongRetr.isScSubspace_range_scDeriv_r_at`
  (`T_zO = Dr(z)E`); `StrongRetr.rangeS_ρCLM_congr`.
* **Condition (3) of the filler on every level at a zero** (Findings item 237):
  `Polyfold.IsFillerOf.mem_range_toBase_of_scDeriv_r_eq_zero` (`v ∈ ker Dr(0)` and
  `(1 − ρ(0))Dg(0)v ∈ F_m` imply `v ∈ E_m`, when `g(0) = 0` and `Dg(0)` is sc-Fredholm) and
  `Polyfold.IsFillerOf.filler_condition_three_sc`: `(1 − ρ(0))Dg(0) : ker Dr(0) → ker ρ(0)` is an
  **sc-isomorphism** between the induced sc-Banach spaces.
* **The converse of Proposition 3.1.5 (preprint 3.5) in sc form** (item 238):
  `Polyfold.IsFillerOf.proposition_3_1_5_sc_converse`: if `Tf(0) : T₀O → K₀` is sc-Fredholm and
  condition (3) holds on every level (the level-`m` maps of `(1 − ρ(0))Dg(0)|_{ker Dr(0)}` are
  onto `ker ρ(0) ∩ F_m`), then `Dg(0)` is sc-Fredholm, with the index of `Tf(0)` on every level;
  `Polyfold.IsFillerOf.proposition_3_1_5_sc_iff`: `Dg(0)` is sc-Fredholm iff `Tf(0)` is
  sc-Fredholm and condition (3) holds on every level.
* **The transport between charts** (item 239): `Polyfold.linAt_chart_change_sc`, the operators of
  `linAt_chart_change` on the ambient spaces — `a = D(τ ∘ r)(z)`, its inverse `a'` on the
  tangent spaces, the fibre transition `γ = Γ(z)` and its inverse `γ'` on the fibres, with
  `D(f̂' ∘ r')(z') ∘ a = γ ∘ D(f̂ ∘ r)(z)` — and their level preservation at smooth points
  (`a`, `γ` sc-operators when `z` is smooth, `a'` when `z'` is).
* **`Lin(z)` is sc-Fredholm in every chart** (item 239): `Polyfold.StrongBundle.linAt_sc_of_germ_wholeChart`
  (the transport from a germ datum: level-`0` Fredholm with the germ's index, regularizing) and
  `Polyfold.StrongBundle.linAt_isScFredholm_wholeChart`:
  for an sc-Fredholm section `f`, a zero `y` and **any** strong bundle chart `c` of `P` around `y`,
  with `z` the level-`1` point over `φ(y)` (a smooth point), `T_zO` and `K_z` are sc-subspaces,
  `D(f̂ ∘ r)(z)` is an sc-operator mapping `T_zO` into `K_z`, and the restriction
  `Lin(z) : T_zO → K_z` (`ScOperator.restrict`, whose level-`0` map is `linAt`) is an
  **sc-Fredholm operator**, Fredholm on every level of index `dim d.Pn − dim d.Q` for every germ
  datum of Definition 3.1.11 (preprint 3.11) at `y` and every conjugation `d` in it.
  `Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex_wholeChart` and
  `Polyfold.theorem_3_6_8_index_locally_constant_sc_wholeChart`: the sc form of
  `theorem_3_6_8_index_locally_constant_wholeChart` (at the zeros near `x₀`, in every chart, `Lin(z)` is
  sc-Fredholm, onto on every level, of index `d` on every level).

## What the text leaves implicit, and the choices made (the findings)

* **Condition (3) on the higher levels at a zero is a consequence, not a hypothesis**, when
  `Dg(0)` is sc-Fredholm: for `v ∈ ker Dr(0)` with `(1 − ρ(0))Dg(0)v ∈ F_m`, write
  `ρ(0)Dg(0)v = Dg(0)t + c` with `t ∈ T₀O` and `c ∈ K₀` smooth (the range of the sc-Fredholm
  `Tf(0)` has a complement of smooth points); then `Dg(0)(v − t) ∈ F_m`, so `v − t ∈ E_m`
  (regularity of `Dg(0)`), `t = −Dr(0)(v − t) ∈ E_m` and `v ∈ E_m`.
* **The converse of Proposition 3.1.5 (preprint 3.5) in sc form needs condition (3) on every level**; condition (3)
  on level `0` (Definition 3.1.4 (preprint 3.4) as stated) does not suffice.  Counterexample (not formalized; it
  needs an sc-structure on a weighted `ℓ²`): `E = F` the sc-space `E_m = ℓ²` with weights
  `2^{nm}`, `r ≡ 0`, `ρ ≡ 0` (so `O = {0}`, `K = {(0, 0)}`, `T₀O = K₀ = 0` and `Tf(0) : 0 → 0`
  is sc-Fredholm), and `g = 1 + λS` with `S` the forward shift and `0 < λ < 1`: `g` is a filler
  (condition (3) on level `0` is the invertibility of `1 + λS` on `ℓ²`), but on a level `m` with
  `λ2^m > 1` the operator `1 + λS` is injective with range of codimension `1`, so `Dg(0)` is not
  sc-Fredholm (and condition (3) fails on that level).
* **Chart independence on all levels.**  The level-`0` conjugation `Γ ∘ Lin(z) = Lin'(z') ∘ A` of
  `linAt_chart_change` is realised by bounded operators on the ambient spaces that preserve the
  levels at smooth points: `A = D(τ ∘ r)(z)|_{T_zO}` with inverse `D(τ' ∘ r')(z')|_{T_{z'}O'}`
  (derivatives of sc-smooth maps at smooth points, Proposition 1.2.1 (preprint 1.16)'s remark), and `Γ = Γ(z)` the
  fibre part of the transition `Θ = Φ' ∘ Φ⁻¹`, which maps `F_m` into `F'_m` at the smooth point `z`
  because `Θ` is sc⁰ on `[0]` (the double filtration of `Y[0]`).  So the regularity transfers
  from the chart of the germ (Proposition 3.6.5 (preprint 3.52) there) to any chart: `Lin(z)e ∈ F_m` gives
  `Lin₁(0)(Ae) = Γ Lin(z)e ∈ F₁_m`, `Ae ∈ E₁_m`, `e = A⁻¹(Ae) ∈ E_m`.  Only the transition
  `c → c₁` (towards the chart of the germ) and the base transition back are used.
* The point `z` is smooth because a zero of an sc-Fredholm section is smooth
  (`IsScFredholmSectionWholeChart.mem_smoothSet_of_isZeroAt`) and smoothness is read in any chart.
  Tameness is not used.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

universe u v

variable {E F : ScBanach}

/-! ### Level arithmetic and sc-operators -/

/-- `E_m` (as a subset of `E₀`) is closed under addition. -/
lemma ScBanach.add_mem_range_toBase {E : ScBanach} {m : ℕ} {x y : E 0}
    (hx : x ∈ range (E.toBase m)) (hy : y ∈ range (E.toBase m)) : x + y ∈ range (E.toBase m) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, map_add _ _ _⟩

/-- `E_m` (as a subset of `E₀`) is closed under subtraction. -/
lemma ScBanach.sub_mem_range_toBase {E : ScBanach} {m : ℕ} {x y : E 0}
    (hx : x ∈ range (E.toBase m)) (hy : y ∈ range (E.toBase m)) : x - y ∈ range (E.toBase m) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, map_sub _ _ _⟩

/-- `-x ∈ E_m` iff `x ∈ E_m`. -/
lemma ScBanach.neg_mem_range_toBase_iff {E : ScBanach} {m : ℕ} {x : E 0} :
    -x ∈ range (E.toBase m) ↔ x ∈ range (E.toBase m) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨-a, by rw [map_neg, ha, neg_neg]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨-a, map_neg _ _⟩

/-- An sc-operator maps `E_m` into `F_m`. -/
lemma IsScOperator.mem_range_toBase {T₀ : E 0 →L[ℝ] F 0} (h : IsScOperator T₀) {m : ℕ}
    {x : E 0} (hx : x ∈ range (E.toBase m)) : T₀ x ∈ range (F.toBase m) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨Tm, hTm⟩ := h m
  exact ⟨Tm a, hTm a⟩

/-- **The range of a Fredholm `T₀` has a complement of smooth points**: every `w ∈ F₀` is
`T₀e + c` with `c ∈ F_∞` (`F_∞` is dense in `F₀` and `F₀ / T₀(E₀)` is finite-dimensional; the
argument of `isScFredholm_of_isRegularizing`). -/
theorem ScOperator.exists_sub_mem_smooth {T : ScOperator E F} (hF : (T 0).IsFredholm) (w : F 0) :
    ∃ e : E 0, w - T 0 e ∈ F.smooth := by
  set Y := LinearMap.range (T 0 : E 0 →ₗ[ℝ] F 0) with hY
  have hYcl : IsClosed (Y : Set (F 0)) := hF.isClosed_range
  have hQfin : FiniteDimensional ℝ (F 0 ⧸ Y) := hF.finite_coker
  set p := Y.mkQ with hp
  have hpsurj : LinearMap.range (p.domRestrict F.smooth) = ⊤ := by
    have hdense : Dense ((LinearMap.range (p.domRestrict F.smooth) : Submodule ℝ (F 0 ⧸ Y)) :
        Set (F 0 ⧸ Y)) := by
      have h1 : DenseRange Y.mkQL := (Submodule.mkQ_surjective _).denseRange
      have h2 : Dense (Y.mkQL '' (F.smooth : Set (F 0))) :=
        h1.dense_image Y.mkQL.continuous (by rw [← ScScale.smoothLvl_zero]; exact F.dense_smooth 0)
      refine h2.mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hcl : IsClosed ((LinearMap.range (p.domRestrict F.smooth) : Submodule ℝ (F 0 ⧸ Y)) :
        Set (F 0 ⧸ Y)) := Submodule.closed_of_finiteDimensional _
    rw [← Submodule.coe_eq_univ, ← hcl.closure_eq, hdense.closure_eq]
  obtain ⟨s, hs⟩ := LinearMap.range_eq_top.1 hpsurj (p w)
  have hs' : (Submodule.Quotient.mk (s : F 0) : F 0 ⧸ Y) = Submodule.Quotient.mk w := hs
  rw [Submodule.Quotient.eq] at hs'
  obtain ⟨e, he⟩ := hs'
  refine ⟨-e, ?_⟩
  have : w - T 0 (-e) = s := by
    rw [map_neg, sub_neg_eq_add]
    have he' : T 0 e = (s : F 0) - w := he
    rw [he']; abel
  rw [this]
  exact s.2

namespace ScOperator

/-- **A regularizing sc-operator bijective on level `0` is bijective on every level.** -/
theorem IsRegularizing.bijective {T : ScOperator E F} (h : T.IsRegularizing)
    (h0 : Bijective (T 0)) (m : ℕ) : Bijective (T m) := by
  refine ⟨fun x y hxy => E.toBase_injective m (h0.1 ?_), h.surjective h0.2 m⟩
  rw [← T.toBase_comm, ← T.toBase_comm, hxy]

/-- **The level-`0` map of a restriction is Fredholm iff the underlying operator is**: for
`L : A → B` with `L x = T x`, the level-`0` map of `T.restrict` is `L` read through `A₀ = A`,
`B₀ = B`; so they are Fredholm together, with the same index. -/
theorem isFredholm_restrict_zero_iff (T : ScOperator E F) {A : Submodule ℝ (E 0)}
    {B : Submodule ℝ (F 0)} (hA : E.IsScSubspace A) (hB : F.IsScSubspace B)
    (hAB : ∀ x ∈ A, T 0 x ∈ B) {L : ↥A →L[ℝ] ↥B} (hL : ∀ x : A, (L x : F 0) = T 0 x) :
    ((T.restrict hA hB hAB 0).IsFredholm ↔ L.IsFredholm) ∧
      ((T.restrict hA hB hAB 0).IsFredholm →
        fredholmIndex L = fredholmIndex (T.restrict hA hB hAB 0)) := by
  have : CompleteSpace A := hA.isClosed.completeSpace_coe
  have : CompleteSpace B := hB.isClosed.completeSpace_coe
  set e₁ : (E.ofSubspace hA) 0 ≃L[ℝ] A := E.levelSubZeroEquiv A with he₁
  set e₂ : (F.ofSubspace hB) 0 ≃L[ℝ] B := F.levelSubZeroEquiv B with he₂
  have hconj : ∀ x, L (e₁ x) = e₂ (T.restrict hA hB hAB 0 x) := fun x =>
    Subtype.ext (by rw [hL]; rfl)
  exact isFredholm_iff_of_conj hconj

end ScOperator

/-- **An sc-operator bijective on every level is an sc-isomorphism** (the level inverses are
bounded by the open mapping theorem). -/
def ScIso.ofBijective (T : ScOperator E F) (h : ∀ m, Bijective (T m)) : ScIso E F where
  lvl m := ContinuousLinearEquiv.ofBijective (T m) (LinearMap.ker_eq_bot.2 (h m).1)
    (LinearMap.range_eq_top.2 (h m).2)
  incl_comm m x := T.incl_comm m x

@[simp] lemma ScIso.ofBijective_apply (T : ScOperator E F) (h : ∀ m, Bijective (T m)) (m : ℕ)
    (x : E m) : ScIso.ofBijective T h m x = T m x := rfl

/-! ### `ker Dr(0)`, `ker ρ(0)`, `T_zO`, `K_z` as sc-subspaces -/

namespace StrongRetr

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} (hU : IsRelOpenInQuadrant E C U)
  (hR : IsStrongBundleRetraction U R)

include hU hR in
/-- **`ker Dr(0)` is an sc-subspace** (`0 ∈ O`): the complement of the sc-projection `Dr(0)`
(Lemma 2.B). -/
theorem isScSubspace_ker_scDeriv_r (h0O : (0 : E 0) ∈ r R '' U) :
    E.IsScSubspace (LinearMap.ker (scDeriv U (r R) 0 : E 0 →ₗ[ℝ] E 0)) := by
  have hop := isScOperator_scDeriv_r hU hR (mem_U_of_mem_O hR h0O)
  have hidem : ∀ x, hop.toScOperator 0 (hop.toScOperator 0 x) = hop.toScOperator 0 x := by
    rw [hop.toScOperator_zero]; exact scDeriv_r_idem hU hR h0O
  have h := ScBanach.isScSplitting_of_idem hop.toScOperator hidem
  rw [hop.toScOperator_zero] at h
  exact h.2.1

include hR in
/-- **`ker ρ(0)` is an sc-subspace** (`0 ∈ O`): the complement of the sc-projection `ρ(0)`. -/
theorem isScSubspace_ker_ρCLM (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U) :
    F.IsScSubspace (LinearMap.ker (ρCLM hR h0 : F 0 →ₗ[ℝ] F 0)) := by
  have hop := isScOperator_ρCLM hR h0
  have hidem : ∀ x, hop.toScOperator 0 (hop.toScOperator 0 x) = hop.toScOperator 0 x := by
    rw [hop.toScOperator_zero]; exact ρCLM_idem hR h0 h0O
  have h := ScBanach.isScSplitting_of_idem hop.toScOperator hidem
  rw [hop.toScOperator_zero] at h
  exact h.2.1

include hR in
/-- **`ρ(u)` is an sc-operator at a smooth point `u`**: it maps `F_m` into `F_m` (the filtration
condition of Definition 2.6.1 (preprint 2.47) at `u ∈ E_m`), bounded by the closed graph theorem. -/
theorem isScOperator_ρCLM_of_mem_smooth {u : E 0} (hu : u ∈ U) (hus : u ∈ E.smooth) :
    IsScOperator (ρCLM hR hu) :=
  isScOperator_of_mapsTo fun m x =>
    (hR.preserves_filtration m m (Nat.le_succ m) u hu ((ScScale.mem_smooth_iff _).1 hus m)
      (F.toBase m x) ⟨x, rfl⟩).2

include hR in
/-- **`K_u = ρ(u)F` is an sc-subspace** at a smooth point `u ∈ O`. -/
theorem isScSubspace_range_ρCLM_of_mem_smooth {u : E 0} (hu : u ∈ U) (huO : u ∈ r R '' U)
    (hus : u ∈ E.smooth) : F.IsScSubspace (rangeS (ρCLM hR hu)) := by
  have hop := isScOperator_ρCLM_of_mem_smooth hR hu hus
  have hidem : ∀ x, hop.toScOperator 0 (hop.toScOperator 0 x) = hop.toScOperator 0 x := by
    rw [hop.toScOperator_zero]; exact fun k => ρ_ρ hR huO k
  have h := ScBanach.isScSplitting_of_idem hop.toScOperator hidem
  rw [hop.toScOperator_zero] at h
  exact h.1

include hU hR in
/-- `Dr(z)` is an sc-operator at a smooth point `z` of `U`. -/
theorem isScOperator_scDeriv_r_at {z : E 1} (hzU : E.toBase 1 z ∈ U)
    (hzs : z ∈ E.smoothLvl 1) : IsScOperator (scDeriv U (r R) z) :=
  (r_isScSmooth hU hR).isSc1.isSc1With_scDeriv.scOperator_deriv hzU hzs

include hU hR in
/-- **`T_zO = Dr(z)E` is an sc-subspace** at a smooth point `z` of the retract. -/
theorem isScSubspace_range_scDeriv_r_at {z : E 1} (hzO : E.toBase 1 z ∈ r R '' U)
    (hzs : z ∈ E.smoothLvl 1) : E.IsScSubspace (rangeS (scDeriv U (r R) z)) := by
  have hop := isScOperator_scDeriv_r_at hU hR (mem_U_of_mem_O hR hzO) hzs
  have hidem : ∀ x, hop.toScOperator 0 (hop.toScOperator 0 x) = hop.toScOperator 0 x := by
    rw [hop.toScOperator_zero]; exact scDeriv_r_idem_at hU hR hzO
  have h := ScBanach.isScSplitting_of_idem hop.toScOperator hidem
  rw [hop.toScOperator_zero] at h
  exact h.1

include hR in
/-- `ρCLM` depends on the point only (for `rangeS`). -/
lemma rangeS_ρCLM_congr {u u' : E 0} (h : u = u') (hu : u ∈ U) (hu' : u' ∈ U) :
    rangeS (ρCLM hR hu) = rangeS (ρCLM hR hu') := by
  subst h; rfl

end StrongRetr

open StrongRetr

/-! ### Condition (3) of the filler on every level, and the converse of Proposition 3.1.5 (preprint 3.5) -/

namespace IsFillerOf

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {hU : IsRelOpenInQuadrant E C U}
  {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {fb g : E 0 → F 0}
  (hfg : IsFillerOf hU hR h0 fb g)

include hfg in
/-- **Condition (3) of the filler on every level at a zero** (the remark of Findings item 234;
Definition 3.1.4 (preprint 3.4) (3)): let `g` fill `f` with `g(0) = 0` and `Dg(0)` sc-Fredholm.  If `v ∈ ker Dr(0)`
and `(1 − ρ(0))Dg(0)v ∈ F_m`, then `v ∈ E_m`.  Proof: `ρ(0)Dg(0)v = Dg(0)t + c` with `t ∈ T₀O` and
`c ∈ K₀` smooth (`Tf(0)` is sc-Fredholm, `IsFillerOf.proposition_3_1_5_sc`, and its range has a
complement of smooth points, `ScOperator.exists_sub_mem_smooth`); `Dg(0)(v − t) ∈ F_m`, so
`v − t ∈ E_m` (Proposition 1.1.10 (preprint 1.9) for `Dg(0)`), and `t = −Dr(0)(v − t) ∈ E_m`. -/
theorem mem_range_toBase_of_scDeriv_r_eq_zero (hg : IsScSmooth U g) (hg0 : g 0 = 0)
    (h0O : (0 : E 0) ∈ r R '' U) (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    (hDg : IsScOperator (scDeriv U g 0)) (hDgF : IsScFredholm hDg.toScOperator) {m : ℕ}
    {v : E 0} (hv : scDeriv U (r R) 0 v = 0)
    (hy : scDeriv U g 0 v - ρCLM hR h0 (scDeriv U g 0 v) ∈ range (F.toBase m)) :
    v ∈ range (E.toBase m) := by
  obtain ⟨hT, hK, hTK, hTF, happ, -⟩ := hfg.proposition_3_1_5_sc hg hg0 h0O hfK hDg hDgF
  have hS0 : (hDg.toScOperator.restrict hT hK hTK 0).IsFredholm := by
    obtain ⟨s⟩ := hTF; exact s.isFredholm 0
  set w := ρCLM hR h0 (scDeriv U g 0 v) with hw
  have hwK : w ∈ rangeS (ρCLM hR h0) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ := ScOperator.exists_sub_mem_smooth hS0 (⟨w, hwK⟩ : (F.ofSubspace hK) 0)
  -- `c = w − Dg(0)t` is smooth, `t = e ∈ T₀O`
  have hc : w - scDeriv U g 0 e.1 ∈ range (F.toBase m) := by
    obtain ⟨c, hc⟩ := (ScScale.mem_smooth_iff _).1 he m
    have hmem := (ScBanach.ofSubspace_mem_range_toBase_iff hK).1 ⟨c, hc⟩
    convert hmem using 1
    change w - scDeriv U g 0 e.1 = w - (hDg.toScOperator.restrict hT hK hTK 0 e).1
    rw [happ]
  have hDgv : scDeriv U g 0 (v - e.1) ∈ range (F.toBase m) := by
    have : scDeriv U g 0 (v - e.1) =
        (scDeriv U g 0 v - w) + (w - scDeriv U g 0 e.1) := by rw [map_sub]; abel
    rw [this]
    exact ScBanach.add_mem_range_toBase hy hc
  have hreg : v - e.1 ∈ range (E.toBase m) :=
    hDgF.isRegularizing m (v - e.1) (by rw [hDg.toScOperator_zero]; exact hDgv)
  have hDr := isScOperator_scDeriv_r hU hR h0
  have he1 : scDeriv U (r R) 0 e.1 = e.1 := by
    have he2 : (e.1 : E 0) ∈ rangeS (scDeriv U (r R) 0) := e.2
    obtain ⟨w', hw'⟩ := he2
    rw [ContinuousLinearMap.coe_coe] at hw'
    rw [← hw']
    exact scDeriv_r_idem hU hR h0O w'
  have h2 : scDeriv U (r R) 0 (v - e.1) = -e.1 := by rw [map_sub, hv, he1, zero_sub]
  have h3 : e.1 ∈ range (E.toBase m) := by
    rw [← ScBanach.neg_mem_range_toBase_iff, ← h2]
    exact hDr.mem_range_toBase hreg
  have : v = (v - e.1) + e.1 := by abel
  rw [this]
  exact ScBanach.add_mem_range_toBase hreg h3

include hfg in
/-- **Condition (3) of the filler on every level at a zero, as an sc-isomorphism** (Definition 3.1.4 (preprint 3.4)
(3); Findings item 237): let `g` fill `f` with `g(0) = 0` and `Dg(0)` sc-Fredholm.  Then
`ker Dr(0)` and `ker ρ(0)` are sc-subspaces, and `(1 − ρ(0))Dg(0)` restricts to an
**sc-isomorphism** `ker Dr(0) → ker ρ(0)` between the induced sc-Banach spaces (on level `0` it is
the isomorphism of condition (3); it maps level `m` onto level `m` for every `m`). -/
theorem filler_condition_three_sc (hg : IsScSmooth U g) (hg0 : g 0 = 0)
    (h0O : (0 : E 0) ∈ r R '' U) (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    (hDg : IsScOperator (scDeriv U g 0)) (hDgF : IsScFredholm hDg.toScOperator) :
    ∃ (hN : E.IsScSubspace (LinearMap.ker (scDeriv U (r R) 0 : E 0 →ₗ[ℝ] E 0)))
      (hM : F.IsScSubspace (LinearMap.ker (ρCLM hR h0 : F 0 →ₗ[ℝ] F 0)))
      (Φ : ScIso (E.ofSubspace hN) (F.ofSubspace hM)),
      ∀ v : (E.ofSubspace hN) 0, ((Φ 0 v).1 : F 0) =
        scDeriv U g 0 v.1 - ρCLM hR h0 (scDeriv U g 0 v.1) := by
  have hN := isScSubspace_ker_scDeriv_r hU hR h0O
  have hM := isScSubspace_ker_ρCLM hR h0 h0O
  have hρ := isScOperator_ρCLM hR h0
  -- `(1 − ρ(0))Dg(0)` is an sc-operator
  have hC : IsScOperator (scDeriv U g 0 - (ρCLM hR h0).comp (scDeriv U g 0)) :=
    isScOperator_of_mapsTo fun m x => by
      have h1 := hDg.mem_range_toBase (⟨x, rfl⟩ : E.toBase m x ∈ range (E.toBase m))
      rw [sub_apply, ContinuousLinearMap.comp_apply]
      exact ScBanach.sub_mem_range_toBase h1 (hρ.mem_range_toBase h1)
  have hNM : ∀ x ∈ LinearMap.ker (scDeriv U (r R) 0 : E 0 →ₗ[ℝ] E 0),
      hC.toScOperator 0 x ∈ LinearMap.ker (ρCLM hR h0 : F 0 →ₗ[ℝ] F 0) := by
    intro x _
    rw [hC.toScOperator_zero, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      sub_apply, ContinuousLinearMap.comp_apply, map_sub, ρCLM_idem hR h0 h0O,
      sub_self]
  set Cop := hC.toScOperator.restrict hN hM hNM with hCop
  obtain ⟨Φ, hΦ⟩ := hfg.exists_kerEquiv hg hg0 h0O
  have hCapp : ∀ x : (E.ofSubspace hN) 0, ((Cop 0 x).1 : F 0) =
      scDeriv U g 0 x.1 - ρCLM hR h0 (scDeriv U g 0 x.1) := by
    intro x
    change hC.toScOperator 0 x.1 = _
    rw [hC.toScOperator_zero]
    rfl
  have hbij0 : Bijective (Cop 0) := by
    constructor
    · intro x x' hxx'
      have h2 := congrArg Subtype.val hxx'
      rw [hCapp, hCapp] at h2
      have h1 : Φ ⟨x.1, x.2⟩ = Φ ⟨x'.1, x'.2⟩ := Subtype.ext (by rw [hΦ, hΦ]; exact h2)
      exact Subtype.ext (congrArg Subtype.val (Φ.injective h1))
    · intro y
      set v := Φ.symm ⟨y.1, y.2⟩ with hv
      refine ⟨⟨v.1, v.2⟩, Subtype.ext ((hCapp _).trans ?_)⟩
      change scDeriv U g 0 v.1 - ρCLM hR h0 (scDeriv U g 0 v.1) = y.1
      rw [← hΦ, hv, Φ.apply_symm_apply]
  have hreg : Cop.IsRegularizing := by
    intro m x hx
    rw [ScBanach.ofSubspace_mem_range_toBase_iff] at hx ⊢
    rw [hCapp] at hx
    exact hfg.mem_range_toBase_of_scDeriv_r_eq_zero hg hg0 h0O hfK hDg hDgF x.2 hx
  exact ⟨hN, hM, ScIso.ofBijective Cop (hreg.bijective hbij0), hCapp⟩

include hfg in
/-- **The converse of Proposition 3.1.5 (preprint 3.5), sc form** (Findings item 238): let `g` fill `f` with
`g(0) = 0`, `Dg(0)` an sc-operator, `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀` (`ScOperator.restrict`)
sc-Fredholm, and condition (3) of Definition 3.1.4 (preprint 3.4) on every level: for every `m`, the level-`m` map
of `(1 − ρ(0))Dg(0)|_{ker Dr(0)}` is onto `ker ρ(0) ∩ F_m`.  Then `Dg(0)` is sc-Fredholm, and every
level map of `Dg(0)` is Fredholm with the index of `Tf(0)`.  Proof: Fredholm on level `0` by
Proposition 3.1.5 (preprint 3.5); regularizing from the triangular form: for `Dg(0)e ∈ F_m`, the `ker Dr(0)`-part
`v = e − Dr(0)e` has `(1 − ρ(0))Dg(0)v = (1 − ρ(0))Dg(0)e ∈ F_m`, so `v ∈ E_m` (condition (3) on
level `m` and the injectivity on level `0`); then `Tf(0)Dr(0)e = Dg(0)e − Dg(0)v ∈ F_m` and
`Dr(0)e ∈ E_m` (`Tf(0)` regularizing).  The hypothesis on the higher levels is needed (module
docstring). -/
theorem proposition_3_1_5_sc_converse (hg : IsScSmooth U g) (hg0 : g 0 = 0)
    (h0O : (0 : E 0) ∈ r R '' U) (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    (hDg : IsScOperator (scDeriv U g 0)) (hT : E.IsScSubspace (rangeS (scDeriv U (r R) 0)))
    (hK : F.IsScSubspace (rangeS (ρCLM hR h0)))
    (hTK : ∀ x ∈ rangeS (scDeriv U (r R) 0), hDg.toScOperator 0 x ∈ rangeS (ρCLM hR h0))
    (hTF : IsScFredholm (hDg.toScOperator.restrict hT hK hTK))
    (h3 : ∀ (m : ℕ) (y : F 0), ρCLM hR h0 y = 0 → y ∈ range (F.toBase m) →
      ∃ v ∈ range (E.toBase m), scDeriv U (r R) 0 v = 0 ∧
        scDeriv U g 0 v - ρCLM hR h0 (scDeriv U g 0 v) = y) :
    IsScFredholm hDg.toScOperator ∧ ∀ m, (hDg.toScOperator m).IsFredholm ∧
      fredholmIndex (hDg.toScOperator m) =
        fredholmIndex (hDg.toScOperator.restrict hT hK hTK 0) := by
  obtain ⟨h1, -, hFiff, hindeq⟩ := hfg.proposition_3_1_5 hg hg0 h0O hfK
  obtain ⟨Φ, hΦ⟩ := hfg.exists_kerEquiv hg hg0 h0O
  have hρ := isScOperator_ρCLM hR h0
  have hS0F : (hDg.toScOperator.restrict hT hK hTK 0).IsFredholm := by
    obtain ⟨s⟩ := hTF; exact s.isFredholm 0
  obtain ⟨hiff, hind⟩ := hDg.toScOperator.isFredholm_restrict_zero_iff hT hK hTK
    (L := fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1)
    (fun x => by rw [fillerRestrict_apply, hDg.toScOperator_zero])
  have hDgF0 : (scDeriv U g 0).IsFredholm := hFiff.1 (hiff.1 hS0F)
  have hreg : hDg.toScOperator.IsRegularizing := by
    intro m e he
    rw [hDg.toScOperator_zero] at he
    set t := scDeriv U (r R) 0 e with ht
    set v := e - t with hv
    have hv0 : scDeriv U (r R) 0 v = 0 := by
      rw [hv, map_sub, ht, scDeriv_r_idem hU hR h0O, sub_self]
    have ht0 : scDeriv U g 0 t - ρCLM hR h0 (scDeriv U g 0 t) = 0 :=
      hfg.deriv_comp_r_eq_zero hg hg0 h0O hfK e
    have hy : scDeriv U g 0 v - ρCLM hR h0 (scDeriv U g 0 v) =
        scDeriv U g 0 e - ρCLM hR h0 (scDeriv U g 0 e) := by
      have : scDeriv U g 0 v - ρCLM hR h0 (scDeriv U g 0 v) =
          (scDeriv U g 0 e - ρCLM hR h0 (scDeriv U g 0 e)) -
            (scDeriv U g 0 t - ρCLM hR h0 (scDeriv U g 0 t)) := by
        rw [hv, map_sub, map_sub]; abel
      rw [this, ht0, sub_zero]
    have hρy : ρCLM hR h0 (scDeriv U g 0 v - ρCLM hR h0 (scDeriv U g 0 v)) = 0 := by
      rw [hy, map_sub, ρCLM_idem hR h0 h0O, sub_self]
    have hym : scDeriv U g 0 v - ρCLM hR h0 (scDeriv U g 0 v) ∈ range (F.toBase m) := by
      rw [hy]; exact ScBanach.sub_mem_range_toBase he (hρ.mem_range_toBase he)
    obtain ⟨v', hv'm, hv'0, hv'y⟩ := h3 m _ hρy hym
    have hvv' : v' = v := by
      have h4 : Φ ⟨v', hv'0⟩ = Φ ⟨v, hv0⟩ := Subtype.ext (by rw [hΦ, hΦ, hv'y])
      exact congrArg Subtype.val (Φ.injective h4)
    have hvm : v ∈ range (E.toBase m) := hvv' ▸ hv'm
    have htm : scDeriv U g 0 t ∈ range (F.toBase m) := by
      have : scDeriv U g 0 t = scDeriv U g 0 e - scDeriv U g 0 v := by rw [hv, map_sub]; abel
      rw [this]
      exact ScBanach.sub_mem_range_toBase he (hDg.mem_range_toBase hvm)
    have htT : t ∈ rangeS (scDeriv U (r R) 0) := ⟨e, rfl⟩
    have htlev := (ScBanach.ofSubspace_mem_range_toBase_iff hT).1
      (hTF.isRegularizing m ⟨t, htT⟩ ((ScBanach.ofSubspace_mem_range_toBase_iff hK).2 (by
        change hDg.toScOperator 0 t ∈ _
        rw [hDg.toScOperator_zero]; exact htm)))
    have he' : e = t + v := by rw [hv]; abel
    rw [he']
    exact ScBanach.add_mem_range_toBase htlev hvm
  have hF0 : (hDg.toScOperator 0).IsFredholm := by rw [hDg.toScOperator_zero]; exact hDgF0
  obtain ⟨hsc, hlvl⟩ := isScFredholm_of_isRegularizing_index hF0 hreg
  refine ⟨hsc, fun m => ⟨(hlvl m).1, ?_⟩⟩
  rw [(hlvl m).2, hDg.toScOperator_zero, ← hindeq, hind hS0F]

include hfg in
/-- **Proposition 3.1.5 (preprint 3.5), sc form, both directions** (Findings items 237–238): for a filler `g` with
`g(0) = 0` and `Dg(0)` an sc-operator, `Dg(0)` is sc-Fredholm **iff** `Tf(0) : T₀O → K₀` is
sc-Fredholm **and** condition (3) of Definition 3.1.4 (preprint 3.4) holds on every level.  (⟹:
`proposition_3_1_5_sc` and `mem_range_toBase_of_scDeriv_r_eq_zero`; ⟸:
`proposition_3_1_5_sc_converse`.) -/
theorem proposition_3_1_5_sc_iff (hg : IsScSmooth U g) (hg0 : g 0 = 0)
    (h0O : (0 : E 0) ∈ r R '' U) (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    (hDg : IsScOperator (scDeriv U g 0)) (hT : E.IsScSubspace (rangeS (scDeriv U (r R) 0)))
    (hK : F.IsScSubspace (rangeS (ρCLM hR h0)))
    (hTK : ∀ x ∈ rangeS (scDeriv U (r R) 0), hDg.toScOperator 0 x ∈ rangeS (ρCLM hR h0)) :
    IsScFredholm hDg.toScOperator ↔ IsScFredholm (hDg.toScOperator.restrict hT hK hTK) ∧
      ∀ (m : ℕ) (y : F 0), ρCLM hR h0 y = 0 → y ∈ range (F.toBase m) →
        ∃ v ∈ range (E.toBase m), scDeriv U (r R) 0 v = 0 ∧
          scDeriv U g 0 v - ρCLM hR h0 (scDeriv U g 0 v) = y := by
  constructor
  · intro hDgF
    obtain ⟨hT', hK', hTK', hsc, -⟩ := hfg.proposition_3_1_5_sc hg hg0 h0O hfK hDg hDgF
    refine ⟨hsc, fun m y hy hym => ?_⟩
    obtain ⟨Φ, hΦ⟩ := hfg.exists_kerEquiv hg hg0 h0O
    have hyk : y ∈ LinearMap.ker (ρCLM hR h0 : F 0 →ₗ[ℝ] F 0) := hy
    set v := Φ.symm ⟨y, hyk⟩ with hv
    have hvy : scDeriv U g 0 v - ρCLM hR h0 (scDeriv U g 0 v) = y := by
      rw [← hΦ, hv, Φ.apply_symm_apply]
    exact ⟨v, hfg.mem_range_toBase_of_scDeriv_r_eq_zero hg hg0 h0O hfK hDg hDgF v.2
      (hvy ▸ hym), v.2, hvy⟩
  · rintro ⟨hTF, h3⟩
    exact (hfg.proposition_3_1_5_sc_converse hg hg0 h0O hfK hDg hT hK hTK hTF h3).1

end IsFillerOf


/-! ### The transport of `Lin(z)` between charts, on the ambient spaces -/

section ChartChange

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {f : X → Y}

/-- **The chart change of the linearization at a zero, by level-preserving operators** (the
operators behind `linAt_chart_change`; Findings item 239).  For strong bundle charts `c`, `c'`
whose transition `Θ = Φ' ∘ Φ⁻¹` is sc-smooth on `[0]`, a section with sc-smooth principal parts in
both, a zero `y` and level-`1` points `z`, `z'` over `φ(y)`, `φ'(y)`, there are bounded operators
`a = D(τ ∘ r)(z) : E → E'`, `a' = D(τ' ∘ r')(z') : E' → E` (`τ = φ' ∘ φ⁻¹`), inverse to each other
between `T_zO = Dr(z)E` and `T_{z'}O' = Dr'(z')E'`, and `γ = Γ(z) : F → F'` (the fibre part of
`Θ` over `z`), `γ' = Γ'(z')`, inverse to each other between `K_z = ρ(z)F` and `K'_{z'} = ρ'(z')F'`,
with `D(f̂' ∘ r')(z') ∘ a = γ ∘ D(f̂ ∘ r)(z)` on `E`.  At smooth points they preserve the levels:
`a` and `γ` are sc-operators if `z` is smooth (`γ` because `Θ` is sc⁰ on `[0]`, so maps
`E_m ⊕ F_m` into `E'_m ⊕ F'_m`), `a'` is one if `z'` is smooth (derivatives of sc-smooth maps at
smooth points).  The proof is that of `linAt_chart_change` without the cone part. -/
theorem linAt_chart_change_sc (c c' : StrongBundleChart PX P) (hf : IsSection P f)
    (hΘ : IsScSmoothRetractMap (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) (c.overlap c')
      (c'.φ.model.E.prod c'.F) (c'.φ.model.C ×ˢ univ) (c'.overlap c) (c.transition c'))
    (hfc : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal f z)))
    (hfc' : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O
      (c'.φ.model.E.prod c'.F) (c'.φ.model.C ×ˢ univ) c'.K (fun z => (z, c'.principal f z)))
    {y : X} (hyV : y ∈ c.φ.source) (hyV' : y ∈ c'.φ.source) (hy0 : IsZeroAt P f y)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {z' : c'.φ.model.E 1} (hz' : c'.φ.model.E.toBase 1 z' = c'.φ y)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U) (hzU' : c'.φ.model.E.toBase 1 z' ∈ c'.U) :
    ∃ (a : c.φ.model.E 0 →L[ℝ] c'.φ.model.E 0) (a' : c'.φ.model.E 0 →L[ℝ] c.φ.model.E 0)
      (γ : c.F 0 →L[ℝ] c'.F 0) (γ' : c'.F 0 →L[ℝ] c.F 0),
      (∀ v ∈ rangeS (scDeriv c.U (r c.R) z), a v ∈ rangeS (scDeriv c'.U (r c'.R) z')) ∧
      (∀ w ∈ rangeS (scDeriv c'.U (r c'.R) z'), a' w ∈ rangeS (scDeriv c.U (r c.R) z)) ∧
      (∀ v ∈ rangeS (scDeriv c.U (r c.R) z), a' (a v) = v) ∧
      (∀ w ∈ rangeS (scDeriv c'.U (r c'.R) z'), a (a' w) = w) ∧
      (∀ k ∈ rangeS (ρCLM c.isRetraction hzU), γ k ∈ rangeS (ρCLM c'.isRetraction hzU')) ∧
      (∀ k ∈ rangeS (ρCLM c'.isRetraction hzU'), γ' k ∈ rangeS (ρCLM c.isRetraction hzU)) ∧
      (∀ k ∈ rangeS (ρCLM c.isRetraction hzU), γ' (γ k) = k) ∧
      (∀ k ∈ rangeS (ρCLM c'.isRetraction hzU'), γ (γ' k) = k) ∧
      (∀ v, scDeriv c'.U (c'.principal f ∘ r c'.R) z' (a v) =
        γ (scDeriv c.U (c.principal f ∘ r c.R) z v)) ∧
      (z ∈ c.φ.model.E.smoothLvl 1 → IsScOperator a ∧ IsScOperator γ) ∧
      (z' ∈ c'.φ.model.E.smoothLvl 1 → IsScOperator a') := by
  classical
  -- the base charts are compatible (both are charts of `X`)
  have hbase : c.φ.Compatible c'.φ := c.isChart.compatible c'.isChart (P := PX)
  obtain ⟨W, hWo, hW⟩ := c.φ.exists_isOpen_image_eq (s := c.φ.source ∩ c'.φ.source)
    inter_subset_left (c.φ.isOpen_source.inter c'.φ.isOpen_source)
  obtain ⟨W', hWo', hW'⟩ := c'.φ.exists_isOpen_image_eq (s := c'.φ.source ∩ c.φ.source)
    inter_subset_left (c'.φ.isOpen_source.inter c.φ.isOpen_source)
  set Rb := c.isRetraction.baseRetraction c.relOpen with hRb
  set Rb' := c'.isRetraction.baseRetraction c'.relOpen with hRb'
  set Rw := Rb.restrict hWo with hRwdef
  set Rw' := Rb'.restrict hWo' with hRw'def
  have hRw : Rw.retract = c.φ.overlap c'.φ := by
    rw [ScRetraction.restrict_retract, c.base_retract]; exact hW.symm
  have hRw' : Rw'.retract = c'.φ.overlap c.φ := by
    rw [ScRetraction.restrict_retract, c'.base_retract]; exact hW'.symm
  set τ := c.φ.transition c'.φ with hτdef
  set τ' := c'.φ.transition c.φ with hτ'def
  have hdiff : Rw.IsDiffeoGerm Rw' τ τ' :=
    { isSc1 := (hbase.1.comp_isScSmooth Rw hRw).isSc1
      isSc1_inv := (hbase.2.comp_isScSmooth Rw' hRw').isSc1
      mapsTo := by rw [hRw, hRw']; exact c.φ.transition_mapsTo c'.φ
      mapsTo_inv := by rw [hRw, hRw']; exact c'.φ.transition_mapsTo c.φ
      left_inv := by
        rw [hRw]; rintro _ ⟨y₁, hy₁, rfl⟩
        rw [hτdef, hτ'def, c.φ.transition_apply c'.φ hy₁.1, c'.φ.transition_apply c.φ hy₁.2]
      right_inv := by
        rw [hRw']; rintro _ ⟨y₁, hy₁, rfl⟩
        rw [hτdef, hτ'def, c'.φ.transition_apply c.φ hy₁.1, c.φ.transition_apply c'.φ hy₁.2] }
  -- the points
  have hyO : c.φ y ∈ c.φ.overlap c'.φ := c.φ.mem_overlap c'.φ hyV hyV'
  have hyO' : c'.φ y ∈ c'.φ.overlap c.φ := c'.φ.mem_overlap c.φ hyV' hyV
  have hx : z ∈ c.φ.model.E.lvlSet Rw.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hRw]; exact hyO
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [hz, c.r_image]; exact c.φ.mapsTo_model y hyV
  have hzO' : c'.φ.model.E.toBase 1 z' ∈ r c'.R '' c'.U := by
    rw [hz', c'.r_image]; exact c'.φ.mapsTo_model y hyV'
  have hzOO : c.φ.model.E.toBase 1 z ∈ c.φ.model.O := by rw [hz]; exact c.φ.mapsTo_model y hyV
  have hzOO' : c'.φ.model.E.toBase 1 z' ∈ c'.φ.model.O := by
    rw [hz']; exact c'.φ.mapsTo_model y hyV'
  have hzV' : c.φ.symm (c.φ.model.E.toBase 1 z) ∈ c'.φ.source := by
    rw [hz, c.φ.symm_apply_apply hyV]; exact hyV'
  have hzV : c'.φ.symm (c'.φ.model.E.toBase 1 z') ∈ c.φ.source := by
    rw [hz', c'.φ.symm_apply_apply hyV']; exact hyV
  have hτz : τ (c.φ.model.E.toBase 1 z) = c'.φ.model.E.toBase 1 z' := by
    rw [hz, hτdef, c.φ.transition_apply c'.φ hyV, hz']
  have hτz' : τ' (c'.φ.model.E.toBase 1 z') = c.φ.model.E.toBase 1 z := by
    rw [hz', hτ'def, c'.φ.transition_apply c.φ hyV', hz]
  have hlev : levelMap (τ ∘ Rw) 1 z = z' := by
    apply levelMap_eq_of_toBase_eq
    change c'.φ.model.E.toBase 1 z' = τ (r c.R (c.φ.model.E.toBase 1 z))
    rw [r_eq_self c.isRetraction hzO, hτz]
  have hz1 : z ∈ c.φ.model.E.lvlSet Rw.U 1 := Rw.lvlSet_retract_subset 1 hx
  have hRwU : Rw.U ⊆ c.U := inter_subset_left
  have hRwU' : Rw'.U ⊆ c'.U := inter_subset_left
  have hx' : z' ∈ c'.φ.model.E.lvlSet Rw'.retract 1 := by rw [← hlev]; exact hdiff.image_mem hx
  have hz1' : z' ∈ c'.φ.model.E.lvlSet Rw'.U 1 := Rw'.lvlSet_retract_subset 1 hx'
  -- derivatives of `r`, `f̂ ∘ r` on the restricted domains
  have hr1 : IsSc1 c.U (r c.R) := (r_isScSmooth c.relOpen c.isRetraction).isSc1
  have hr1' : IsSc1 c'.U (r c'.R) := (r_isScSmooth c'.relOpen c'.isRetraction).isSc1
  have hDr : scDeriv Rw.U Rw z = scDeriv c.U (r c.R) z :=
    scDeriv_eq_of_eqOn_relOpen Rw.relOpen Rw.isSc1 hr1 subset_rfl hRwU (fun _ _ => rfl) hz1
  have hDr' : scDeriv Rw'.U Rw' z' = scDeriv c'.U (r c'.R) z' :=
    scDeriv_eq_of_eqOn_relOpen Rw'.relOpen Rw'.isSc1 hr1' subset_rfl hRwU' (fun _ _ => rfl) hz1'
  have hσsm : IsScSmooth c.U (scPair (r c.R) (c.principal f ∘ r c.R)) :=
    (hfc.comp_isScSmooth Rb c.base_retract).congr c.relOpen.isScDomain fun _ _ => rfl
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) :=
    ((hσsm.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl).isSc1
  have hσsm' : IsScSmooth c'.U (scPair (r c'.R) (c'.principal f ∘ r c'.R)) :=
    (hfc'.comp_isScSmooth Rb' c'.base_retract).congr c'.relOpen.isScDomain fun _ _ => rfl
  have hfr' : IsSc1 c'.U (c'.principal f ∘ r c'.R) :=
    ((hσsm'.snd c'.relOpen.isScDomain).congr c'.relOpen.isScDomain fun _ _ => rfl).isSc1
  have hrRw : IsSc1 Rw.U (r c.R) := hr1.of_subset hRwU
  have hfrRw : IsSc1 Rw.U (c.principal f ∘ r c.R) := hfr.of_subset hRwU
  have hDfr : scDeriv Rw.U (c.principal f ∘ r c.R) z = scDeriv c.U (c.principal f ∘ r c.R) z :=
    scDeriv_eq_of_eqOn_relOpen Rw.relOpen hfrRw hfr subset_rfl hRwU (fun _ _ => rfl) hz1
  -- the retraction onto the overlap of `K` and the transition `Θ`
  set RK := (c.isRetraction.toScRetraction c.relOpen).restrict (hWo.prod isOpen_univ) with hRKdef
  have hRK : RK.retract = c.overlap c' := by
    rw [ScRetraction.restrict_retract]; exact (c.overlap_eq_inter_prod c' hW).symm
  have hRKapp : ∀ p, RK p = c.R p := fun _ => rfl
  have hΘs : IsScSmooth (F := c'.φ.model.E.prod c'.F) RK.U (c.transition c' ∘ RK) :=
    hΘ.comp_isScSmooth RK hRK
  set Φ : (c.φ.model.E.prod c.F) 0 → c'.F 0 := fun p => ((c.transition c' ∘ RK) p).2 with hΦdef
  have hΦ : IsSc1 RK.U Φ := (hΘs.snd RK.isScDomain).isSc1
  -- the fibre operator `Γ(z)` and the vanishing of `Φ` on the zero section
  set Γt := c.transitionFiberCLM c' hzOO hzV' with hΓt
  have hzW : c.φ.model.E.toBase 1 z ∈ W := by
    have : c.φ.model.E.toBase 1 z ∈ c.φ.model.O ∩ W := by rw [← hW, hz]; exact hyO
    exact this.2
  have hRz : ∀ k, c.R (c.φ.model.E.toBase 1 z, k) =
      (c.φ.model.E.toBase 1 z, ρ c.R (c.φ.model.E.toBase 1 z) k) := fun k => by
    rw [apply_eq c.isRetraction hzU, r_eq_self c.isRetraction hzO]
  have hzD : ∀ k : c.F 0, ((c.φ.model.E.toBase 1 z, k) : (c.φ.model.E.prod c.F) 0) ∈ RK.U :=
    fun k => ⟨⟨hzU, mem_univ _⟩, by
      change c.R (c.φ.model.E.toBase 1 z, k) ∈ W ×ˢ univ
      rw [hRz]; exact ⟨hzW, mem_univ _⟩⟩
  have hSD : ∀ u ∈ Rw.U, ((u, 0) : (c.φ.model.E.prod c.F) 0) ∈ RK.U := fun u hu =>
    ⟨⟨hu.1, mem_univ _⟩, ⟨hu.2, mem_univ _⟩⟩
  have hΓ : ∀ k, Φ (c.φ.model.E.toBase 1 z, k) = Γt k := fun k => by
    rw [hΓt, StrongBundleChart.transitionFiberCLM_apply]
    change (c.transition c' (c.R (c.φ.model.E.toBase 1 z, k))).2 = _
    rw [hRz]
  have hzero : ∀ u ∈ Rw.U, Φ (u, 0) = 0 := by
    intro u hu
    have hru : r c.R u ∈ c.φ.overlap c'.φ := by rw [← hRw]; exact Rw.apply_mem_retract hu
    have hR0 : c.R (u, 0) = (r c.R u, 0) := by
      rw [apply_eq c.isRetraction hu.1, (ρ_isLinear c.isRetraction hu.1).map_zero]
    have hK0 : (r c.R u, (0 : c.F 0)) ∈ c.K := by
      rw [← hR0]; exact ⟨(u, 0), ⟨hu.1, mem_univ _⟩, rfl⟩
    change (c.transition c' (c.R (u, 0))).2 = 0
    rw [hR0]
    exact c.transition_snd_zero c' hK0 (c.φ.symm_mem_of_mem_overlap c'.φ hru)
  -- the section in the chart and the main identity
  set σ := scPair (r c.R) (c.principal f ∘ r c.R) with hσdef
  have hσmem : ∀ u ∈ Rw.U, ∃ y₁, y₁ ∈ c.φ.source ∧ y₁ ∈ c'.φ.source ∧ r c.R u = c.φ y₁ ∧
      σ u = c (f y₁) ∧ σ u ∈ RK.retract := by
    intro u hu
    have hru : r c.R u ∈ c.φ.overlap c'.φ := by rw [← hRw]; exact Rw.apply_mem_retract hu
    obtain ⟨y₁, ⟨hy₁, hy₁'⟩, hy₁u⟩ := hru
    have hσu : σ u = c (f y₁) := by
      change (r c.R u, c.principal f (r c.R u)) = c (f y₁)
      rw [← hy₁u, c.apply_section' hf hy₁]
    refine ⟨y₁, hy₁, hy₁', hy₁u.symm, hσu, ?_⟩
    rw [hRK, hσu]
    exact ⟨f y₁, ⟨c.mem_source_of_proj (by rw [hf]; exact hy₁),
      c'.mem_source_of_proj (by rw [hf]; exact hy₁')⟩, rfl⟩
  have hmapsσ : MapsTo σ Rw.U RK.U := fun u hu => by
    obtain ⟨-, -, -, -, -, h⟩ := hσmem u hu
    exact RK.retract_subset h
  have hσ1 : IsSc1 Rw.U σ := (hσsm.of_subset Rw.isScDomain hRwU).isSc1
  have hEq : EqOn ((c'.principal f ∘ r c'.R) ∘ (τ ∘ Rw)) (Φ ∘ σ) Rw.U := by
    intro u hu
    obtain ⟨y₁, hy₁, hy₁', hru, hσu, hσK⟩ := hσmem u hu
    have hτu : τ (r c.R u) = c'.φ y₁ := by rw [hru, hτdef, c.φ.transition_apply c'.φ hy₁]
    have hr' : r c'.R (c'.φ y₁) = c'.φ y₁ :=
      r_eq_self c'.isRetraction (by rw [c'.r_image]; exact c'.φ.mapsTo_model y₁ hy₁')
    change c'.principal f (r c'.R (τ (r c.R u))) = (c.transition c' (RK (σ u))).2
    rw [RK.apply_eq_self_of_mem_retract hσK, hσu]
    change _ = (c' (c.toPartialEquiv.symm (c (f y₁)))).2
    rw [c.toPartialEquiv.left_inv (c.mem_source_of_proj (by rw [hf]; exact hy₁)),
      c'.apply_section' hf hy₁', hτu, hr']
  have hmapsτ : MapsTo (τ ∘ Rw) Rw.U c'.U := fun u hu => (hdiff.mapsTo_U hu).1
  have hℓ : IsSc1 Rw.U ((c'.principal f ∘ r c'.R) ∘ (τ ∘ Rw)) :=
    (theorem_1_3_1' Rw.isScDomain c'.relOpen.isScDomain hdiff.isSc1 hfr' hmapsτ).1
  have hΦσ : IsSc1 Rw.U (Φ ∘ σ) :=
    (theorem_1_3_1' Rw.isScDomain RK.isScDomain hσ1 hΦ hmapsσ).1
  have hDeq : scDeriv Rw.U ((c'.principal f ∘ r c'.R) ∘ (τ ∘ Rw)) z = scDeriv Rw.U (Φ ∘ σ) z :=
    scDeriv_eq_of_eqOn_relOpen Rw.relOpen hℓ hΦσ subset_rfl subset_rfl hEq hz1
  have hfz : c.principal f (c.φ.model.E.toBase 1 z) = 0 := by
    rw [hz]; exact (c.isZeroAt_iff hf hyV).1 hy0
  have hlevσ : levelMap σ 1 z = ((z, 0) : (c.φ.model.E.prod c.F) 1) := by
    apply levelMap_eq_of_toBase_eq
    rw [ScBanach.prod_toBase, map_zero]
    change (c.φ.model.E.toBase 1 z, (0 : c.F 0)) =
      (r c.R (c.φ.model.E.toBase 1 z), c.principal f (r c.R (c.φ.model.E.toBase 1 z)))
    rw [r_eq_self c.isRetraction hzO, hfz]
  have key : ∀ v, scDeriv c'.U (c'.principal f ∘ r c'.R) z' (scDeriv Rw.U (τ ∘ Rw) z v) =
      Γt (scDeriv c.U (c.principal f ∘ r c.R) z v) := by
    intro v
    have h1 := scDeriv_comp_apply' Rw.relOpen c'.relOpen hdiff.isSc1 hfr' hmapsτ hz1 v
    rw [hlev] at h1
    have h2 := scDeriv_comp_apply' Rw.relOpen RK.relOpen hσ1 hΦ hmapsσ hz1 v
    rw [hlevσ, hσdef, scDeriv_scPair Rw.relOpen hrRw hfrRw hz1, ContinuousLinearMap.prod_apply,
      scDeriv_fiber_of_vanishing Rw.relOpen hΦ hz1 hSD hzD hzero Γt hΓ] at h2
    rw [h1, hDeq, ← h2, hDfr]
  -- the isomorphism `A` of the tangent spaces (Proposition 2.4.10 (preprint 2.30))
  set A₀ := scDeriv Rw.U (τ ∘ Rw) z with hA₀
  set A₀' := scDeriv Rw'.U (τ' ∘ Rw') z' with hA₀'
  have hTA : ∀ v ∈ rangeS (scDeriv c.U (r c.R) z), A₀ v ∈ rangeS (scDeriv c'.U (r c'.R) z') := by
    rintro _ ⟨w, rfl⟩
    have := hdiff.deriv_mem_range hx (v := scDeriv c.U (r c.R) z w) (by rw [hDr]; exact ⟨w, rfl⟩)
    rw [hlev, hDr'] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨u, hu⟩
  have himg : levelMap (τ' ∘ Rw') 1 z' = z := by rw [← hlev]; exact hdiff.image_image hx
  have hTA' : ∀ w ∈ rangeS (scDeriv c'.U (r c'.R) z'), A₀' w ∈ rangeS (scDeriv c.U (r c.R) z) := by
    rintro _ ⟨u, rfl⟩
    have := hdiff.symm.deriv_mem_range hx' (v := scDeriv c'.U (r c'.R) z' u)
      (by rw [hDr']; exact ⟨u, rfl⟩)
    rw [himg, hDr] at this
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩
  have hinv1 : ∀ v ∈ rangeS (scDeriv c.U (r c.R) z), A₀' (A₀ v) = v := by
    rintro _ ⟨w, rfl⟩
    have := hdiff.deriv_inv_deriv hx (scDeriv c.U (r c.R) z w)
    rw [hlev, hDr] at this
    change A₀' (A₀ (scDeriv c.U (r c.R) z w)) = _
    rw [this]
    exact scDeriv_r_idem_at c.relOpen c.isRetraction hzO w
  have hinv2 : ∀ w ∈ rangeS (scDeriv c'.U (r c'.R) z'), A₀ (A₀' w) = w := by
    rintro _ ⟨u, rfl⟩
    have := hdiff.deriv_deriv_inv hx (scDeriv c'.U (r c'.R) z' u)
    rw [hlev, hDr'] at this
    change A₀ (A₀' (scDeriv c'.U (r c'.R) z' u)) = _
    rw [this]
    exact scDeriv_r_idem_at c'.relOpen c'.isRetraction hzO' u
  -- the isomorphism `Γ` of the fibres
  set Γt' := c'.transitionFiberCLM c hzOO' hzV with hΓt'
  have hKz : ∀ k ∈ rangeS (ρCLM c.isRetraction hzU), (c.φ.model.E.toBase 1 z, k) ∈ c.K := by
    rintro _ ⟨k₀, rfl⟩
    exact c.mem_K_ρ hzOO k₀
  have hKz' : ∀ k ∈ rangeS (ρCLM c'.isRetraction hzU'), (c'.φ.model.E.toBase 1 z', k) ∈ c'.K := by
    rintro _ ⟨k₀, rfl⟩
    exact c'.mem_K_ρ hzOO' k₀
  have hΘz : ∀ k, (c.φ.model.E.toBase 1 z, k) ∈ c.K →
      c.transition c' (c.φ.model.E.toBase 1 z, k) =
        (c'.φ.model.E.toBase 1 z', (c.transition c' (c.φ.model.E.toBase 1 z, k)).2) := by
    intro k hk
    refine Prod.ext ?_ rfl
    rw [c.transition_fst c' hk hzV']
    exact hτz
  have hΘz' : ∀ k, (c'.φ.model.E.toBase 1 z', k) ∈ c'.K →
      c'.transition c (c'.φ.model.E.toBase 1 z', k) =
        (c.φ.model.E.toBase 1 z, (c'.transition c (c'.φ.model.E.toBase 1 z', k)).2) := by
    intro k hk
    refine Prod.ext ?_ rfl
    rw [c'.transition_fst c hk hzV]
    exact hτz'
  have hΓK : ∀ k ∈ rangeS (ρCLM c.isRetraction hzU),
      (c'.φ.model.E.toBase 1 z', Γt k) ∈ c'.K := by
    intro k hk
    rw [hΓt, c.transitionFiberCLM_apply_of_mem c' hzOO hzV' (hKz k hk), ← hΘz k (hKz k hk)]
    exact c.transition_mem_K c' (hKz k hk) hzV'
  have hΓK' : ∀ k ∈ rangeS (ρCLM c'.isRetraction hzU'),
      (c.φ.model.E.toBase 1 z, Γt' k) ∈ c.K := by
    intro k hk
    rw [hΓt', c'.transitionFiberCLM_apply_of_mem c hzOO' hzV (hKz' k hk), ← hΘz' k (hKz' k hk)]
    exact c'.transition_mem_K c (hKz' k hk) hzV
  have hΓmem : ∀ k ∈ rangeS (ρCLM c.isRetraction hzU), Γt k ∈ rangeS (ρCLM c'.isRetraction hzU') :=
    fun k hk => ⟨Γt k, ρ_eq_self_of_mem_K c'.isRetraction hzU' (hΓK k hk)⟩
  have hΓmem' : ∀ k ∈ rangeS (ρCLM c'.isRetraction hzU'),
      Γt' k ∈ rangeS (ρCLM c.isRetraction hzU) :=
    fun k hk => ⟨Γt' k, ρ_eq_self_of_mem_K c.isRetraction hzU (hΓK' k hk)⟩
  have hΓinv1 : ∀ k ∈ rangeS (ρCLM c.isRetraction hzU), Γt' (Γt k) = k := by
    intro k hk
    rw [hΓt', c'.transitionFiberCLM_apply_of_mem c hzOO' hzV (hΓK k hk), hΓt,
      c.transitionFiberCLM_apply_of_mem c' hzOO hzV' (hKz k hk), ← hΘz k (hKz k hk),
      c.transition_transition c' (hKz k hk) hzV']
  have hΓinv2 : ∀ k ∈ rangeS (ρCLM c'.isRetraction hzU'), Γt (Γt' k) = k := by
    intro k hk
    rw [hΓt, c.transitionFiberCLM_apply_of_mem c' hzOO hzV' (hΓK' k hk), hΓt',
      c'.transitionFiberCLM_apply_of_mem c hzOO' hzV (hKz' k hk), ← hΘz' k (hKz' k hk),
      c'.transition_transition c (hKz' k hk) hzV]
  refine ⟨A₀, A₀', Γt, Γt', hTA, hTA', hinv1, hinv2, hΓmem, hΓmem', hΓinv1, hΓinv2, key,
    fun hzs => ⟨?_, ?_⟩, fun hzs' => ?_⟩
  · exact hdiff.isSc1.isSc1With_scDeriv.scOperator_deriv hz1 hzs
  · -- `Γ(z)` preserves the levels: `Θ` is sc⁰ on `[0]` and `z` is smooth
    refine isScOperator_of_mapsTo fun m x => ?_
    obtain ⟨zm, hzm⟩ := (c.φ.model.E.mem_smoothLvl_iff).1 hzs m
    have hpm : (c.φ.model.E.prod c.F).toBase m ((zm, x) : (c.φ.model.E.prod c.F) m) =
        ((c.φ.model.E.toBase 1 z, c.F.toBase m x) : (c.φ.model.E.prod c.F) 0) := by
      rw [ScBanach.prod_toBase, hzm]
    have hp : ((zm, x) : (c.φ.model.E.prod c.F) m) ∈ (c.φ.model.E.prod c.F).lvlSet RK.U m := by
      rw [ScBanach.mem_lvlSet, hpm]; exact hzD _
    obtain ⟨q, hq⟩ := hΘs.isSc1.isSc0.mem_range m _ hp
    rw [hpm] at hq
    have h2 := congrArg Prod.snd hq
    rw [ScBanach.prod_toBase] at h2
    exact ⟨q.2, by rw [← hΓ]; exact h2⟩
  · exact hdiff.isSc1_inv.isSc1With_scDeriv.scOperator_deriv hz1' hzs'

end ChartChange


/-! ### `Lin(z)` is sc-Fredholm in every chart -/

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **`Lin(z)` from a germ datum at `y`** (the transport step of `linAt_isScFredholm_wholeChart`): let `f` be
sc-smooth, `y` a zero, `c` a strong bundle chart of `P` around `y` with the smooth level-`1` point
`z` over `φ(y)`, and `D(f̂ ∘ r)(z)` an sc-operator restricting to `Lin(z) : T_zO → K_z`
(`ScOperator.restrict`).  Given a datum of Definition 3.1.11 (preprint 3.11) at `y` (a chart `c₁` centred at `y`, a
filled version `g₁`, `s₁` with `s₁(0) = g₁(0)`, a conjugation `d` of `g₁ − s₁` to a basic germ),
the level-`0` map of `Lin(z)` is Fredholm of index `dim d.Pn − dim d.Q`, and `Lin(z)` is
regularizing.  Proof: in `c₁`, `Dg₁(0)` is sc-Fredholm and `Tf₁(0)` is Fredholm of that index
(`proposition_3_6_5_local_sc_wholeChart`, Proposition 3.1.5 (preprint 3.5)); `Lin₁(0) ∘ a = γ ∘ Lin(z)` with level-preserving
`a`, `a'`, `γ` (`linAt_chart_change_sc`). -/
theorem StrongBundle.linAt_sc_of_germ_wholeChart (hf : B.IsScSmoothSection f) {y : X}
    (hy0 : IsZeroAt P f y) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyV : y ∈ c.φ.source) {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U) (hzs : z ∈ c.φ.model.E.smoothLvl 1)
    (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
    (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
    (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
    (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
      hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU))
    {c₁ : StrongBundleChart PX P} (hc₁ : B.IsChart c₁) (hyV₁ : y ∈ c₁.φ.source)
    (hφ₁ : c₁.φ y = 0) (h0₁ : (0 : c₁.φ.model.E 0) ∈ c₁.U) {g₁ : c₁.φ.model.E 0 → c₁.F 0}
    {s₁ : c₁.φ.model.E 0 → c₁.F 1}
    (hfill₁ : IsFilledVersion c₁.relOpen c₁.isRetraction h0₁ (c₁.principal f) g₁)
    (hs₁ : IsScSmooth (F := c₁.F.shift) c₁.U s₁) (hs0₁ : c₁.F.toBase 1 (s₁ 0) = g₁ 0)
    (d : ConjugationData c₁.U fun u => g₁ u - c₁.F.toBase 1 (s₁ u)) :
    (hD.toScOperator.restrict hT hK hTK 0).IsFredholm ∧
      fredholmIndex (hD.toScOperator.restrict hT hK hTK 0) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
      (hD.toScOperator.restrict hT hK hTK).IsRegularizing := by
  have hfs : IsSection P f := hf.1
  have hfr : ∀ {d' : StrongBundleChart PX P}, B.IsChart d' →
      IsSc1 d'.U (d'.principal f ∘ r d'.R) := fun {d'} hd' => by
    have h1 := (hf.isScSmoothRetractMap hd').comp_isScSmooth
      (d'.isRetraction.baseRetraction d'.relOpen) d'.base_retract
    exact ((h1.snd d'.relOpen.isScDomain).congr d'.relOpen.isScDomain fun _ _ => rfl).isSc1
  -- the chart of the germ: `Dg₁(0)` sc-Fredholm, `Tf₁(0)` Fredholm
  have h0O₁ : (0 : c₁.φ.model.E 0) ∈ r c₁.R '' c₁.U := by
    rw [c₁.r_image, ← hφ₁]; exact c₁.φ.mapsTo_model y hyV₁
  have hfb0 : c₁.principal f 0 = 0 := by
    have := (c₁.isZeroAt_iff hfs hyV₁).1 hy0
    rwa [hφ₁] at this
  have hfK₁ : ∀ x ∈ r c₁.R '' c₁.U, (x, c₁.principal f x) ∈ c₁.R '' (c₁.U ×ˢ univ) :=
    fun x hx => c₁.principal_mem_K hfs (c₁.r_image ▸ hx)
  obtain ⟨hDg₁, hT₁, hK₁, hTK₁, hDgF₁, hTF₁, happ₁, hlvl₁⟩ :=
    proposition_3_6_5_local_sc_wholeChart c₁.relOpen c₁.isRetraction h0₁ h0O₁ hfill₁ hfb0 hfK₁ hs₁ hs0₁ d
  have hg0₁ : g₁ 0 = 0 := by rw [← hfill₁.filler.eq_on.self_of_nhds h0O₁, hfb0]
  obtain ⟨h1₁, -, hFiff₁, hindeq₁⟩ :=
    hfill₁.filler.proposition_3_1_5 hfill₁.isScSmooth hg0₁ h0O₁ hfK₁
  have hDg₁F : (scDeriv c₁.U g₁ 0).IsFredholm := by
    have := (hlvl₁ 0).1; rwa [hDg₁.toScOperator_zero] at this
  have hDg₁ind : fredholmIndex (scDeriv c₁.U g₁ 0) = finrank ℝ d.Pn - finrank ℝ d.Q := by
    have := (hlvl₁ 0).2.1; rwa [hDg₁.toScOperator_zero] at this
  have hL₁F := hFiff₁.2 hDg₁F
  -- on `T₀O₁`, `Dg₁(0) = D(f̂₁ ∘ r₁)(0)`
  have hL₁app : ∀ w ∈ rangeS (scDeriv c₁.U (r c₁.R) 0),
      scDeriv c₁.U g₁ 0 w = scDeriv c₁.U (c₁.principal f ∘ r c₁.R) 0 w := fun w hw => by
    have := IsFilledVersion.fillerRestrict_eq_linAt c₁.relOpen c₁.isRetraction h0O₁ hfill₁
      (hfr hc₁) h1₁ ⟨w, hw⟩
    rwa [fillerRestrict_apply, linAt_apply] at this
  -- the transport `c → c₁`
  have hz₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) = c₁.φ y := by rw [map_zero, hφ₁]
  have hzU₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) ∈ c₁.U := by rw [map_zero]; exact h0₁
  obtain ⟨a, a', γ, γ', hTA, hTA', hinv1, hinv2, hΓmem, hΓmem', hΓinv1, hΓinv2, key, hsm, hsm'⟩ :=
    linAt_chart_change_sc c c₁ hfs (StrongBundle.IsChart.transition_isScSmoothRetractMap hc hc₁)
      (hf.isScSmoothRetractMap hc) (hf.isScSmoothRetractMap hc₁) hyV hyV₁ hy0 hz hz₁ hzU hzU₁
  have hρeq := rangeS_ρCLM_congr c₁.isRetraction (map_zero _) hzU₁ h0₁
  rw [hρeq] at hΓmem hΓmem' hΓinv2
  obtain ⟨-, hγ⟩ := hsm hzs
  have ha' := hsm' c₁.φ.model.E.zero_mem_smoothLvl_one
  -- the conjugation on level `0`
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x => by
    have := hTK x x.2
    rwa [hD.toScOperator_zero] at this
  have : CompleteSpace ↥(rangeS (scDeriv c.U (r c.R) z)) := hT.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c.isRetraction hzU)) := hK.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (scDeriv c₁.U (r c₁.R) 0)) := hT₁.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c₁.isRetraction h0₁)) := hK₁.isClosed.completeSpace_coe
  have hLL : ∀ x, fillerRestrict (scDeriv c₁.U (r c₁.R) 0) (ρCLM c₁.isRetraction h0₁)
      (scDeriv c₁.U g₁ 0) h1₁ (restrictEquiv _ _ a a' hTA hTA' hinv1 hinv2 x) =
      restrictEquiv _ _ γ γ' hΓmem hΓmem' hΓinv1 hΓinv2
        ((linAt c.U c.R (c.principal f) z).codRestrict _ hmem x) := fun x => by
    apply Subtype.ext
    change scDeriv c₁.U g₁ 0 (a x) = γ (scDeriv c.U (c.principal f ∘ r c.R) z x)
    rw [hL₁app _ (hTA x x.2)]
    exact key x
  obtain ⟨hFiffc, hindc⟩ := isFredholm_iff_of_conj hLL
  have hLzF := hFiffc.2 hL₁F
  obtain ⟨hF0, hind0⟩ := hD.toScOperator.isFredholm_restrict_zero hT hK hTK
    (L := (linAt c.U c.R (c.principal f) z).codRestrict _ hmem)
    (fun x => by rw [hD.toScOperator_zero]; rfl) hLzF
  refine ⟨hF0, ?_, ?_⟩
  · rw [hind0, ← hindc hLzF, hindeq₁, hDg₁ind]
  · -- the regularity: `Lin(z)x ∈ F_m ⟹ Lin₁(0)(ax) = γ Lin(z)x ∈ F₁_m ⟹ ax ∈ E₁_m ⟹ x ∈ E_m`
    intro m x hx
    have hx' := (ScBanach.ofSubspace_mem_range_toBase_iff hK).1 hx
    apply (ScBanach.ofSubspace_mem_range_toBase_iff hT).2
    have h6 : scDeriv c.U (c.principal f ∘ r c.R) z x.1 ∈ range (c.F.toBase m) := by
      have h5 : ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
          scDeriv c.U (c.principal f ∘ r c.R) z x.1 := by
        change hD.toScOperator 0 x.1 = _
        rw [hD.toScOperator_zero]
      rwa [h5] at hx'
    have h7 := hγ.mem_range_toBase h6
    rw [← key, ← hL₁app _ (hTA x.1 x.2)] at h7
    have h8 := hDgF₁.isRegularizing m (a x.1) (by rw [hDg₁.toScOperator_zero]; exact h7)
    have h9 := ha'.mem_range_toBase h8
    rwa [hinv1 x.1 x.2] at h9

/-- **The linearization of an sc-Fredholm section at a zero is sc-Fredholm in every chart**
(Proposition 3.6.5 (preprint 3.52) and Theorem 3.1.22 (preprint 3.19), "`f'(x)` is sc-Fredholm", in the chart-intrinsic form of the
round-trip statements V3.46, V3.96 and of V3.98's index; Findings item 239).  Let `f` be an
sc-Fredholm section, `y` a zero, `c` **any** strong bundle chart of `P` around `y`, `z` the
level-`1` point over `φ(y)` (it is smooth: zeros of `f` are smooth points).  Then `D(f̂ ∘ r)(z)`
is an sc-operator,
`T_zO = Dr(z)E` and `K_z = ρ(z)F` are sc-subspaces, `D(f̂ ∘ r)(z)` maps `T_zO` into `K_z`, and the
restriction `Lin(z) : T_zO → K_z` (`ScOperator.restrict`, whose level-`0` map is
`linAt U R f̂ z`) is an **sc-Fredholm operator**; every level map is Fredholm with the level-`0`
index, which is `dim d.Pn − dim d.Q` for **every** datum of Definition 3.1.11 (preprint 3.11) at `y` (chart `c₁`
centred at `y`, filled version `g₁`, `s₁`, conjugation `d` of `g₁ − s₁` to a basic germ). -/
theorem StrongBundle.linAt_isScFredholm_wholeChart (hf : B.IsScFredholmSectionWholeChart f) {y : X}
    (hy0 : IsZeroAt P f y) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyV : y ∈ c.φ.source) {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U) :
    ∃ (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
      (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
      (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
      (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
        hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU)),
      (∀ x : (c.φ.model.E.ofSubspace hT) 0, ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
        linAt c.U c.R (c.principal f) z ⟨x.1, x.2⟩) ∧
      IsScFredholm (hD.toScOperator.restrict hT hK hTK) ∧
      ∀ m, ((hD.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
        fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) =
          fredholmIndex (hD.toScOperator.restrict hT hK hTK 0) ∧
        ∀ (c₁ : StrongBundleChart PX P) (_ : B.IsChart c₁) (_ : y ∈ c₁.φ.source) (_ : c₁.φ y = 0)
          (h0₁ : (0 : c₁.φ.model.E 0) ∈ c₁.U) (g₁ : c₁.φ.model.E 0 → c₁.F 0)
          (s₁ : c₁.φ.model.E 0 → c₁.F 1)
          (_ : IsFilledVersion c₁.relOpen c₁.isRetraction h0₁ (c₁.principal f) g₁)
          (_ : IsScSmooth (F := c₁.F.shift) c₁.U s₁) (_ : c₁.F.toBase 1 (s₁ 0) = g₁ 0)
          (d : ConjugationData c₁.U fun u => g₁ u - c₁.F.toBase 1 (s₁ u)),
          fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) =
            finrank ℝ d.Pn - finrank ℝ d.Q := by
  have hfs := hf.isScSmooth
  have hys : y ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hy0
  have hzs : z ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 z ∈ c.φ.model.E.smooth
    rw [hz, ScScale.mem_smooth_iff]
    intro m
    exact (PX.mem_levelSet_iff c.isChart hyV).1 (Set.mem_iInter.1 hys m)
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model y hyV
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := by
    have h1 := (hfs.isScSmoothRetractMap hc).comp_isScSmooth
      (c.isRetraction.baseRetraction c.relOpen) c.base_retract
    exact ((h1.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl).isSc1
  have hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z) :=
    hfr.isSc1With_scDeriv.scOperator_deriv hzU hzs
  have hT := isScSubspace_range_scDeriv_r_at c.relOpen c.isRetraction hzO hzs
  have hK := isScSubspace_range_ρCLM_of_mem_smooth c.isRetraction hzU hzO hzs
  have hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
      hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x _ => by
    rw [hD.toScOperator_zero]
    exact ⟨_, rho_scDeriv_comp_r c.relOpen c.isRetraction hfr
      (fun x hx => c.principal_mem_K hfs.1 (c.r_image ▸ hx)) hzO
      (by rw [hz]; exact (c.isZeroAt_iff hfs.1 hyV).1 hy0) x⟩
  obtain ⟨-, c₁, hc₁, hyV₁, hφ₁, h0₁, g₁, s₁, hfill₁, hs₁, hs0₁, hconj₁⟩ := hf.germ y hys
  obtain ⟨d₁⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj₁
  obtain ⟨hF0, -, hreg⟩ := StrongBundle.linAt_sc_of_germ_wholeChart hfs hy0 hc hyV hz hzU hzs hD hT hK hTK
    hc₁ hyV₁ hφ₁ h0₁ hfill₁ hs₁ hs0₁ d₁
  obtain ⟨hsc, hlvl⟩ := isScFredholm_of_isRegularizing_index hF0 hreg
  refine ⟨hD, hT, hK, hTK, fun x => ?_, hsc, fun m => ⟨(hlvl m).1, (hlvl m).2, ?_⟩⟩
  · change hD.toScOperator 0 x.1 = _
    rw [hD.toScOperator_zero]
    rfl
  · intro c₂ hc₂ hyV₂ hφ₂ h0₂ g₂ s₂ hfill₂ hs₂ hs0₂ d
    obtain ⟨-, hind, -⟩ := StrongBundle.linAt_sc_of_germ_wholeChart hfs hy0 hc hyV hz hzU hzs hD hT hK hTK
      hc₂ hyV₂ hφ₂ h0₂ hfill₂ hs₂ hs0₂ d
    rw [(hlvl m).2, hind]

/-- **At a zero where `f'(y)` is onto of index `d`** (`IsSurjLinOfIndex`), in every chart:
`Lin(z) : T_zO → K_z` is sc-Fredholm, **onto on every level** (regularizing and onto on level
`0`) and of index `d` on every level (Theorem 3.1.22 (preprint 3.19)'s "`f'(x₀)` is sc-Fredholm and onto", at a
zero with the hypothesis of `IsSurjLinOfIndex`; round-trip item V3.96). -/
theorem StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex_wholeChart (hf : B.IsScFredholmSectionWholeChart f)
    {y : X} (hy0 : IsZeroAt P f y) {d : ℕ} (hd : B.IsSurjLinOfIndex f y d)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U) :
    ∃ (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
      (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
      (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
      (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
        hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU)),
      (∀ x : (c.φ.model.E.ofSubspace hT) 0, ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
        linAt c.U c.R (c.principal f) z ⟨x.1, x.2⟩) ∧
      IsScFredholm (hD.toScOperator.restrict hT hK hTK) ∧
      ∀ m, Surjective ((hD.toScOperator.restrict hT hK hTK) m) ∧
        ((hD.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
        fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) = d := by
  obtain ⟨hD, hT, hK, hTK, happ, hsc, hlvl⟩ := StrongBundle.linAt_isScFredholm_wholeChart hf hy0 hc hyV hz hzU
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x => by
    have := hTK x x.2
    rwa [hD.toScOperator_zero] at this
  obtain ⟨hLs, hLF, hLind, -⟩ := hd c hc hyV z hz hzU
    ((linAt c.U c.R (c.principal f) z).codRestrict _ hmem) fun _ => rfl
  obtain ⟨-, hind0⟩ := hD.toScOperator.isFredholm_restrict_zero hT hK hTK
    (L := (linAt c.U c.R (c.principal f) z).codRestrict _ hmem)
    (fun x => by rw [hD.toScOperator_zero]; rfl) hLF
  have hsurj0 : Surjective (hD.toScOperator.restrict hT hK hTK 0) := by
    intro k
    obtain ⟨x, hx⟩ := hLs ⟨k.1, k.2⟩
    exact ⟨⟨x.1, x.2⟩, Subtype.ext ((happ _).trans (congrArg Subtype.val hx))⟩
  refine ⟨hD, hT, hK, hTK, happ, hsc, fun m => ⟨hsc.isRegularizing.surjective hsurj0 m,
    (hlvl m).1, ?_⟩⟩
  rw [(hlvl m).2.1, hind0, hLind]

/-- **The index is locally constant along the solution set, sc form**
(`theorem_3_6_8_index_locally_constant_wholeChart` with "sc-Fredholm" in every chart; Theorem 3.6.8 (preprint 3.54) and
Proposition 6.2.2 (preprint 6.2) in the setting of `theorem_3_6_8_index_locally_constant_wholeChart`, towards round-trip item
V3.98 (b); Findings item 239): for an sc-Fredholm section with tame germ data, `f(x₀) = 0` and
`(f, x₀)` in good position in a tame chart, there are an open `Vx ∋ x₀` and `d` such that at every
zero `y ∈ Vx`, in **every** strong bundle chart `c` of `P` around `y`, at the level-`1` point `z`
over `φ(y)`, the linearization `Lin(z) : T_zO → K_z` is an sc-Fredholm operator, onto on every
level, of index `d` on every level. -/
theorem theorem_3_6_8_index_locally_constant_sc_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∀ y ∈ Vx, IsZeroAt P f y → ∀ (c : StrongBundleChart PX P) (_ : B.IsChart c)
        (_ : y ∈ c.φ.source) (z : c.φ.model.E 1) (_ : c.φ.model.E.toBase 1 z = c.φ y)
        (hzU : c.φ.model.E.toBase 1 z ∈ c.U),
        ∃ (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
          (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
          (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
          (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
            hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU)),
          (∀ x : (c.φ.model.E.ofSubspace hT) 0,
            ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
              linAt c.U c.R (c.principal f) z ⟨x.1, x.2⟩) ∧
          IsScFredholm (hD.toScOperator.restrict hT hK hTK) ∧
          ∀ m, Surjective ((hD.toScOperator.restrict hT hK hTK) m) ∧
            ((hD.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
            fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) = d := by
  obtain ⟨Vx, d, hVo, hx₀V, hall⟩ := theorem_3_6_8_index_locally_constant_wholeChart hf hg hx₀
  exact ⟨Vx, d, hVo, hx₀V, fun y hy hy0 c hc hyV z hz hzU =>
    StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex_wholeChart hf.toIsScFredholmSectionWholeChart hy0
      (hall y hy hy0) hc hyV hz hzU⟩

end Bundle

end Polyfold
