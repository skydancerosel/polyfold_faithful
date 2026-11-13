import Polyfold.Chapter4.FamiliesLocal
import Polyfold.Chapter3.ParamPerturbation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §4.3,
Theorem 4.3.1 (preprint 4.23) *(book 2017: Theorem 4.4; see `BookConcordance.md`, not checked against the 2017
text)*.

# Families and an application of Sard's theorem

## The text, paraphrased

For a tame M-polyfold `X`, `Z = ℝᵐ ⊕ X` is a tame M-polyfold (product charts), `P(λ, x) = λ`.
(Theorem 4.3.1 (preprint 4.23)) Let `A ⊆ Z` be a smooth submanifold whose induced M-polyfold structure is tame,
with compact closure, `p = P|_A`, and `ε > 0` such that (1) for `|λ| ≤ ε` the set `p⁻¹(λ)` is
compact and non-empty, (2) `A` is in general position (misprinted: "there exists a sc-complement
`T_zA` in `T_zZ` which is contained in `T_z^R Z`").  Then there is a set `Σ ⊆ {|λ| < ε}` of full
measure of regular values of `p` such that for `λ ∈ Σ`, `A_λ = {x | (λ, x) ∈ A}` is a smooth
compact manifold with boundary with corners whose tangent space `T_xA_λ` has in `T_xX` an
sc-complement contained in `T_x^R X`.  *Proof*: at `z ∈ A`, Theorem 4.2.11 (preprint 4.22) ("By Theorem 4.23", a
slip) gives `U(z)` with `d = d_X(z)` local faces; `A ∩ F_σ` is a submanifold of dimension
`dim A − #σ`; cover `{|p| ≤ ε}` by finitely many `U(z_i)`; in each, Sard's theorem gives full
measure sets `Σ_σ` of regular values of `p_σ : A ∩ F_σ° → ℝᵐ`, `Σ = ⋂_σ Σ_σ`; for `λ ∈ Σ`,
`T_{z'}(A ∩ F_σ°) = T_{z'}(({λ} × A_λ) ∩ F_σ°) ⊕ ξ_{z'}` with `Tp_σ(z')` mapping `ξ_{z'}` onto
`ℝᵐ`, and with (2) `T_{z'}({λ} × A_λ)` has an sc-complement in `T_{z'}^R X`; intersect over the
`z_i`.

## What is formalized

* `theorem_4_3_1_preprint`: the statement, on the M-polyfold `ℝᵐ × X = (rnPolyfold m).prod PX` (tame by
  `prod_rn_isTame`), with `|λ|² = Σ λ_i²`, hypothesis (2) read as general position at every point
  (Definition 4.2.10 (preprint 4.21)), and the conclusions: `Σ ⊆ {|λ| < ε}` with `{|λ| < ε} ∖ Σ` Lebesgue-null,
  every `λ ∈ Σ` a **stratified regular value** (`IsStratRegularValue`), `A_λ` **compact**, a
  **smooth finite-dimensional submanifold** of `X` (Definition 4.2.1 (preprint 4.13)) **in general position** at
  each point, and with its induced structure **a manifold with boundary with corners**
  (Definition 4.1.1 (preprint 4.1), `HasCornerStructure`) and tame.  `theorem_4_3_1_of_subset` is the same for an
  arbitrary parameter set `S` in place of the ball.
* `IsStratRegularPoint`, `IsStratRegularValue`: the text's "regular value of the `p_σ`" at a point
  of the open stratum through it — in a product chart, the projection to `ℝᵐ` maps
  `T_zA ∩ E_z` (the tangent space of the stratum) onto `ℝᵐ`.
* `exists_local_family`, the local step: in the product chart `(r ↦ r − λ₀) × φ` centred at `z₀`
  (`φ` a re-centred tame chart of `X`), Theorem 4.2.11 (preprint 4.22) in the chart (`theorem_4_2_11_chart`) gives the
  graph map `Γ` over `V ⊆ T₀A ∩ C`; `f = P ∘ χ⁻¹ ∘ Γ` is `C^∞`, its stratified critical values form
  a null set (`measure_image_stratCritSet`, Sard on the strata), and over every other value the
  fibre has the properties of the theorem near the point.
* `exists_slice_retraction`: the **sc⁺-retraction onto the fibre** `A_λ` in the model of `X`,
  `τ(e) = (Γ(ρ(p(t(c, e)))))₂`, with `ρ` the `C^∞` retraction onto the fibre of `f`
  (`exists_fibre_retraction`) and its tangent space at the point;
  `isGeneralPositionRetractAt_slice`: **general position of the fibre** from general position of
  `A` and stratified regularity.
* The slice `e ↦ (c, e)` (`isScSmooth_slice`, `scDeriv_slice`), `ScBanach.prodInrOp`, `rnPres`
  (`ℝᵐ` as a partial quadrant without half-line coordinates).

## What the text leaves implicit, and the choices made

* **"Regular value" must be read in the stratified sense** of the proof (regular for every
  `p_σ`); with `Dp(z) : T_zA → ℝᵐ` onto only, the theorem is false (Findings).  It is stated in a
  chart, for some chart (as Definitions 4.2.5, 4.2.10 (preprint 4.16, 4.21)); its chart
  independence is `isStratRegularPoint_iff_forall` (`StratifiedRegularValues.lean`).
* **The covering step is repaired**: `{z ∈ A | |p(z)| ≤ ε}` need not be compact (Findings), so
  no finite subcover is available; `A` is second countable (its closure is compact in the
  metrizable `ℝᵐ × X`, Theorem 2.3.10 (preprint 2.16)), and a countable subcover suffices for the measure statement.
* "`A_λ` is a smooth submanifold" needs an **sc⁺-retraction onto `A_λ`** (Definition 4.2.1 (preprint 4.13)), which
  the text does not construct (`exists_slice_retraction`), and "manifold with corners" needs the
  implicit function theorem at corner points with the kernel in good position (Lemma 5.26's
  argument, `exists_goodComplement_stratSub`, and Theorem 3.8.22 (preprint 3.78) in `C^∞` form); the corner
  structure of `A_λ` is then Theorem 4.2.7 (preprint 4.18), good position following from general position.
* Hypothesis (1) is used only for the compactness of `A_λ`; its non-emptiness, `ε > 0` and the
  tameness of the induced structure of `A` are not used.
* No hypothesis is added.  `[ParacompactSpace A]` is the instance argument of the induced
  structure (`subPolyfold`), `[ParacompactSpace (ℝᵐ × X)]` that of the product M-polyfold, as in
  `ParamPerturbation.lean`.
-/

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### The slice `e ↦ (c, e)` of `ℝᵐ ⊕ E` -/

section Slice

variable {m : ℕ} {EX : ScBanach}

/-- The inclusion `F → E ⊕ F`, `h ↦ (0, h)`, as an sc-operator. -/
def ScBanach.prodInrOp (E F : ScBanach) : ScOperator F (E.prod F) where
  lvl k := ContinuousLinearMap.inr ℝ (E k) (F k)
  incl_comm k _ := Prod.ext (map_zero (E.incl k)) rfl

/-- `(c, 0)` is a smooth point of `ℝᵐ ⊕ E`. -/
lemma mem_smooth_rn_zero (c : Fin m → ℝ) :
    ((c, 0) : ((rnSc m).prod EX) 0) ∈ ((rnSc m).prod EX).smooth := by
  refine ((rnSc m).prod EX).mem_smooth_iff.2 fun k => ?_
  refine ⟨((c : Fin m → ℝ), (0 : EX k)), ?_⟩
  rw [ScBanach.prod_toBase, map_zero]
  exact Prod.ext (ScBanach.const_toBase _ k c) rfl

/-- **The slice `e ↦ (c, e)` is sc-smooth** (the inclusion `h ↦ (0, h)` followed by the
translation by the smooth vector `(c, 0)`). -/
theorem isScSmooth_slice (c : Fin m → ℝ) {U : Set (EX 0)} (hU : IsScDomain EX U) :
    IsScSmooth (E := EX) (F := (rnSc m).prod EX) U (fun e => ((c, e) : ((rnSc m).prod EX) 0)) := by
  have h1 := (ScBanach.prodInrOp (rnSc m) EX).isScSmooth hU
  have h2 := isScSmooth_add_const (E := (rnSc m).prod EX) (mem_smooth_rn_zero c)
    (isScDomain_univ ((rnSc m).prod EX))
  have := IsScSmooth.comp hU (isScDomain_univ _) h2 h1 (mapsTo_univ _ _)
  refine this.congr hU fun e _ => ?_
  change (0, e) + ((c, 0) : ((rnSc m).prod EX) 0) = (c, e)
  simp

/-- The derivative of the slice `e ↦ (c, e)` at a level-`1` point is `h ↦ (0, h)`. -/
theorem scDeriv_slice (c : Fin m → ℝ) {C U : Set (EX 0)} (hU : IsRelOpenInQuadrant EX C U)
    {y : EX 1} (hy : y ∈ EX.lvlSet U 1) :
    scDeriv (E := EX) (F := (rnSc m).prod EX) U (fun e => ((c, e) : ((rnSc m).prod EX) 0)) y =
      ContinuousLinearMap.inr ℝ (Fin m → ℝ) (EX 0) := by
  apply ContinuousLinearMap.ext_of_comp_toBase_one (E := EX)
  have d₁ := ((isScSmooth_slice c hU.isScDomain).isSc1.isSc1With_scDeriv).hasFDerivWithinAt y hy
  have d₂ : HasFDerivWithinAt
      ((fun e => ((c, e) : ((rnSc m).prod EX) 0)) ∘ EX.toBase 1)
      ((ContinuousLinearMap.inr ℝ (Fin m → ℝ) (EX 0)).comp (EX.toBase 1)) (EX.lvlSet U 1) y := by
    have := ((hasFDerivAt_const c y).prodMk (EX.toBase 1).hasFDerivAt).hasFDerivWithinAt
      (s := EX.lvlSet U 1)
    refine this.congr_fderiv ?_
    ext x <;> simp
  exact (hU.isScDomain.uniqueDiffWithinAt 1 y hy).eq d₁ d₂

/-- On a subset of a finite-dimensional space with the constant sc-structure, the sc-derivative of
a map into any sc-Banach space is the classical derivative within the set (as
`hasFDerivWithinAt_scDeriv_const`, for a source which is not a subspace of the target). -/
theorem hasFDerivWithinAt_scDeriv_const' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {F : ScBanach} {U : Set V} {f : V → F 0}
    (hf : IsSc1 (E := ScBanach.const V) (F := F) U f) {v : V} (hv : v ∈ U) :
    HasFDerivWithinAt f (scDeriv (E := ScBanach.const V) U f v) U v := by
  have hv' : (v : (ScBanach.const V) 1) ∈ (ScBanach.const V).lvlSet U 1 := by
    rw [ScBanach.lvlSet_const]; exact hv
  have h1 := hf.isSc1With_scDeriv.hasFDerivWithinAt _ hv'
  rw [ScBanach.lvlSet_const] at h1
  have e1 : (f ∘ ⇑((ScBanach.const V).toBase 1)) = f :=
    funext fun x => congrArg f (ScBanach.const_toBase V 1 x)
  have e2 : (scDeriv (E := ScBanach.const V) U f v).comp ((ScBanach.const V).toBase 1) =
      scDeriv (E := ScBanach.const V) U f v := by
    ext x; exact congrArg _ (ScBanach.const_toBase V 1 x)
  rw [e1, e2] at h1
  exact h1

end Slice

/-! ### The sc⁺-retraction onto the slice of `A` over a regular value, in a product chart -/

section SliceRetraction

variable {m : ℕ} {EX : ScBanach} {CX : Set (EX 0)}

/-- **The sc⁺-retraction onto the fibre `A_c`, in a product chart** (the step "`A_λ ∩ U(z)` is a
smooth submanifold of `X`", which needs an sc⁺-retraction the text does not construct).  In the
model `ℝᵐ ⊕ E` with the partial quadrant `ℝᵐ × C`, let `t` be an sc⁺-retraction (the chart model
of `A`), described near a point as the graph `Γ : V → t(U) ∩ W` over a relatively open `V` in the
partial quadrant `N ∩ (ℝᵐ × C)` with inverse `p` (Proposition 4.1.9 (preprint 4.9)), and let `ρ` be a `C^∞`
retraction of `O' ∩ (ℝᵐ × C) ⊆ V` (in `N`) onto the points `v` with `(Γ v)₁ = c` (the fibre of
`P ∘ Γ` over `c`, `exists_fibre_retraction`).  Then `τ(e) = (Γ(ρ(p(t(c, e)))))₂` is an
**sc⁺-retraction** of `E` (partial quadrant `C`) onto `{e | (c, e) ∈ t(U) ∩ W, p(c, e) ∈ O'}`.
**Its tangent space**: if `v₀` lies on the fibre and `Dρ(v₀) = 1` on the vectors `h` with
`(DΓ(v₀)h)₁ = 0` (the kernel of `D(P ∘ Γ)(v₀)`), then at the level-`1` point `y` over `Γ(v₀)₂` the
tangent space `T_yτ(U)` contains `(DΓ(v₀)h)₂` for all such `h`: `Dτ(y)` maps it to itself by the
chain rule `Dτ(y)w = (DΓ(v₀) Dρ(v₀) p Dt(c, y)(0, w))₂`, `Dt` fixing `T(t(U)) = DΓ(v₀)N` and
`p ∘ DΓ(v₀) = 1`. -/
theorem exists_slice_retraction (hCX : IsPartialQuadrant EX CX)
    (t : ScRetraction ((rnSc m).prod EX) (univ ×ˢ CX)) (ht : t.IsScPlus)
    {N : Submodule ℝ (((rnSc m).prod EX) 0)} [FiniteDimensional ℝ N]
    {p : ((rnSc m).prod EX) 0 →L[ℝ] N} {W : Set (((rnSc m).prod EX) 0)} (hW : IsOpen W)
    {V : Set N}
    (hV : IsRelOpenInQuadrant (ScBanach.const N) (Subtype.val ⁻¹' (univ ×ˢ CX)) V)
    {Γ : N → ((rnSc m).prod EX) 0}
    (hΓs : IsScSmooth (E := ScBanach.const N) (F := (rnSc m).prod EX) V Γ)
    (hpΓ : ∀ a ∈ V, p (Γ a) = a) (hΓp : ∀ u ∈ t.retract ∩ W, Γ (p u) = u)
    (hpmap : IsScSmoothRetractMap ((rnSc m).prod EX) (univ ×ˢ CX) (t.retract ∩ W)
      (ScBanach.const N) (Subtype.val ⁻¹' (univ ×ˢ CX)) V p)
    (hΓmap : IsScSmoothRetractMap (ScBanach.const N) (Subtype.val ⁻¹' (univ ×ˢ CX)) V
      ((rnSc m).prod EX) (univ ×ˢ CX) (t.retract ∩ W) Γ)
    {O' : Set N} (hO' : IsOpen O') (hO'V : O' ∩ Subtype.val ⁻¹' (univ ×ˢ CX) ⊆ V) {ρ : N → N}
    (hρs : ContDiffOn ℝ ∞ ρ (O' ∩ Subtype.val ⁻¹' (univ ×ˢ CX)))
    (hρmap : MapsTo ρ (O' ∩ Subtype.val ⁻¹' (univ ×ˢ CX)) (O' ∩ Subtype.val ⁻¹' (univ ×ˢ CX)))
    (c : Fin m → ℝ) (hρc : ∀ v ∈ O' ∩ Subtype.val ⁻¹' (univ ×ˢ CX), (Γ (ρ v)).1 = c)
    (hρfix : ∀ v ∈ O' ∩ Subtype.val ⁻¹' (univ ×ˢ CX), (Γ v).1 = c → ρ v = v)
    {v₀ : N} (hv₀ : v₀ ∈ O' ∩ Subtype.val ⁻¹' (univ ×ˢ CX)) (hv₀c : (Γ v₀).1 = c)
    (hDρ : ∀ h : N, (scDeriv (E := ScBanach.const N) V Γ v₀ h).1 = 0 →
      fderivWithin ℝ ρ (O' ∩ Subtype.val ⁻¹' (univ ×ˢ CX)) v₀ h = h) :
    ∃ τ : ScRetraction EX CX, τ.IsScPlus ∧
      (∀ e, e ∈ τ.retract ↔
        ((c, e) : ((rnSc m).prod EX) 0) ∈ t.retract ∩ W ∧ p (c, e) ∈ O') ∧
      τ.U = {e | ((c, e) : ((rnSc m).prod EX) 0) ∈ t.U ∧ t (c, e) ∈ W ∧ p (t (c, e)) ∈ O'} ∧
      (∀ e ∈ τ.U, τ e = (Γ (ρ (p (t (c, e))))).2) ∧
      ∀ y : EX 1, EX.toBase 1 y = (Γ v₀).2 → y ∈ EX.lvlSet τ.retract 1 ∧
        ∀ h : N, (scDeriv (E := ScBanach.const N) V Γ v₀ h).1 = 0 →
          (scDeriv (E := ScBanach.const N) V Γ v₀ h).2 ∈ tangentSpace EX CX τ.retract y := by
  classical
  set D : Set N := O' ∩ Subtype.val ⁻¹' (univ ×ˢ CX) with hD
  have hVC : V ⊆ Subtype.val ⁻¹' (univ ×ˢ CX) := fun a ha => by
    obtain ⟨O'', -, hO''⟩ := hV.relOpen
    rw [hO''] at ha; exact ha.2
  -- the open set `G = W ∩ p⁻¹(O')` and the restriction of `t`
  set G : Set (((rnSc m).prod EX) 0) := W ∩ p ⁻¹' O' with hG
  have hGo : IsOpen G := hW.inter (hO'.preimage p.continuous)
  set R₁ := t.restrict hGo with hR₁
  have hkey : ∀ u ∈ R₁.U, ρ (p (t u)) ∈ D ∧ Γ (ρ (p (t u))) ∈ t.retract ∩ W ∧
      (Γ (ρ (p (t u)))).1 = c ∧ Γ (ρ (p (t u))) ∈ R₁.U := by
    intro u hu
    have htu : t u ∈ t.retract ∩ W := ⟨t.apply_mem_retract hu.1, hu.2.1⟩
    have hptV : p (t u) ∈ V := hpmap.mapsTo htu
    have hptD : p (t u) ∈ D := ⟨hu.2.2, hVC hptV⟩
    have hwD := hρmap hptD
    have hΓw := hΓmap.mapsTo (hO'V hwD)
    refine ⟨hwD, hΓw, hρc _ hptD, t.retract_subset hΓw.1, ?_⟩
    change t (Γ (ρ (p (t u)))) ∈ G
    rw [t.apply_eq_self_of_mem_retract hΓw.1]
    exact ⟨hΓw.2, by rw [mem_preimage, hpΓ _ (hO'V hwD)]; exact hwD.1⟩
  -- the slice
  set S : EX 0 → ((rnSc m).prod EX) 0 := fun e => (c, e) with hS
  have hSc : Continuous S := continuous_const.prodMk continuous_id
  set UX : Set (EX 0) := S ⁻¹' R₁.U with hUX
  have hUXrel : IsRelOpenInQuadrant EX CX UX := by
    obtain ⟨O'', hO'', hR₁eq⟩ := R₁.relOpen.relOpen
    refine ⟨hCX, S ⁻¹' O'', hO''.preimage hSc, ?_⟩
    ext e
    simp only [hUX, mem_preimage, hR₁eq, mem_inter_iff, hS, mem_prod, mem_univ, true_and]
  -- `g = ρ ∘ p ∘ t` and `T₁ = Γ ∘ g`
  set g : ((rnSc m).prod EX) 0 → N := fun u => ρ (p (t u)) with hg
  have hDrel : IsRelOpenInQuadrant (ScBanach.const N) (Subtype.val ⁻¹' (univ ×ˢ CX)) D :=
    ⟨hV.isPartialQuadrant, O', hO', rfl⟩
  have hρsc : IsScSmooth (E := ScBanach.const N) (F := ScBanach.const N) D ρ :=
    IsScSmooth.of_contDiffOn_finiteDimensional hDrel.isScDomain hρs
  set op : ScOperator ((rnSc m).prod EX) (ScBanach.const N) := opToConst p with hop
  have hpt : IsScSmooth (F := ScBanach.const N) R₁.U (fun u => p (t u)) :=
    IsScSmooth.comp R₁.isScDomain (isScDomain_univ _) (op.isScSmooth (isScDomain_univ _))
      R₁.isScSmooth (mapsTo_univ _ _)
  have hptD : MapsTo (fun u => p (t u)) R₁.U D := fun u hu =>
    ⟨hu.2.2, hVC (hpmap.mapsTo ⟨t.apply_mem_retract hu.1, hu.2.1⟩)⟩
  have hgs : IsScSmooth (F := ScBanach.const N) R₁.U g :=
    IsScSmooth.comp R₁.isScDomain hDrel.isScDomain hρsc hpt hptD
  have hgV : MapsTo g R₁.U V := fun u hu => hO'V (hkey u hu).1
  have hT₁ : IsScSmooth R₁.U (fun u => Γ (g u)) :=
    IsScSmooth.comp R₁.isScDomain hV.isScDomain hΓs hgs hgV
  have hT₁p : IsScPlus R₁.U (fun u => Γ (g u)) := by
    have h1 := IsScPlus.comp_isScSmooth R₁.isScDomain t.isScDomain ht hT₁
      fun u hu => t.retract_subset (hkey u hu).2.1.1
    exact h1.congr R₁.isScDomain fun u hu => t.apply_eq_self_of_mem_retract (hkey u hu).2.1.1
  have hSmap : MapsTo S UX R₁.U := fun e he => he
  have hSs : IsScSmooth (E := EX) (F := (rnSc m).prod EX) UX S :=
    isScSmooth_slice c hUXrel.isScDomain
  -- the retraction
  have hSτ : ∀ e ∈ UX, S (Γ (g (S e))).2 = Γ (g (S e)) := fun e he => by
    have := (hkey (S e) he).2.2.1
    exact Prod.ext this.symm rfl
  let τ : ScRetraction EX CX :=
    { U := UX
      toFun := fun e => (Γ (g (S e))).2
      relOpen := hUXrel
      mapsTo := fun e he => by
        change S (Γ (g (S e))).2 ∈ R₁.U
        rw [hSτ e he]
        exact (hkey (S e) he).2.2.2
      isScSmooth := by
        have h1 := IsScSmooth.comp hUXrel.isScDomain R₁.isScDomain hT₁ hSs hSmap
        exact IsScSmooth.comp hUXrel.isScDomain (isScDomain_univ _)
          ((ScBanach.prodSndOp (rnSc m) EX).isScSmooth (isScDomain_univ _)) h1 (mapsTo_univ _ _)
      idem := fun e he => by
        rw [hSτ e he]
        obtain ⟨hwD, hΓw, hc1, -⟩ := hkey (S e) he
        change (Γ (ρ (p (t (Γ (ρ (p (t (S e))))))))).2 = (Γ (ρ (p (t (S e))))).2
        rw [t.apply_eq_self_of_mem_retract hΓw.1, hpΓ _ (hO'V hwD), hρfix _ hwD hc1] }
  have hplus : τ.IsScPlus := by
    have h1 : IsScPlus UX ((fun u => Γ (g u)) ∘ S) :=
      IsScPlus.comp_isScSmooth hUXrel.isScDomain R₁.isScDomain hT₁p hSs hSmap
    have h2 := IsScSmooth.comp_isScPlus hUXrel.isScDomain (isScDomain_univ _)
      ((ScBanach.prodSndOp (rnSc m) EX).isScSmooth (isScDomain_univ _)) h1 (mapsTo_univ _ _)
    exact h2.congr hUXrel.isScDomain fun _ _ => rfl
  have hret : ∀ e, e ∈ τ.retract ↔
      ((c, e) : ((rnSc m).prod EX) 0) ∈ t.retract ∩ W ∧ p (c, e) ∈ O' := by
    intro e
    constructor
    · rintro ⟨e', he', rfl⟩
      obtain ⟨hwD, hΓw, -, -⟩ := hkey (S e') he'
      have hSe : S (Γ (g (S e'))).2 = Γ (g (S e')) := hSτ e' he'
      refine ⟨?_, ?_⟩
      · change S (Γ (g (S e'))).2 ∈ t.retract ∩ W
        rw [hSe]; exact hΓw
      · change p (S (Γ (g (S e'))).2) ∈ O'
        rw [hSe, hpΓ _ (hO'V hwD)]; exact hwD.1
    · rintro ⟨hu, hpu⟩
      have heU : e ∈ UX := by
        refine ⟨t.retract_subset hu.1, ?_⟩
        change t (S e) ∈ G
        rw [t.apply_eq_self_of_mem_retract hu.1]; exact ⟨hu.2, hpu⟩
      refine ⟨e, heU, ?_⟩
      change (Γ (ρ (p (t (S e))))).2 = e
      have hpuV : p (S e) ∈ V := hpmap.mapsTo hu
      have hΓpu : Γ (p (S e)) = S e := hΓp _ hu
      rw [t.apply_eq_self_of_mem_retract hu.1, hρfix _ ⟨hpu, hVC hpuV⟩ (by rw [hΓpu]), hΓpu]
  -- the tangent space at the point over `Γ(v₀)`
  have htan : ∀ y : EX 1, EX.toBase 1 y = (Γ v₀).2 → y ∈ EX.lvlSet τ.retract 1 ∧
      ∀ h : N, (scDeriv (E := ScBanach.const N) V Γ v₀ h).1 = 0 →
        (scDeriv (E := ScBanach.const N) V Γ v₀ h).2 ∈ tangentSpace EX CX τ.retract y := by
    intro y hy
    have hv₀V : v₀ ∈ V := hO'V hv₀
    have hΓv₀ : Γ v₀ ∈ t.retract ∩ W := hΓmap.mapsTo hv₀V
    have hSy : S (EX.toBase 1 y) = Γ v₀ := by rw [hy]; exact Prod.ext hv₀c.symm rfl
    have he₀ : EX.toBase 1 y ∈ τ.retract :=
      (hret _).2 ⟨by change S (EX.toBase 1 y) ∈ t.retract ∩ W; rw [hSy]; exact hΓv₀,
        by change p (S (EX.toBase 1 y)) ∈ O'; rw [hSy, hpΓ _ hv₀V]; exact hv₀.1⟩
    refine ⟨he₀, fun h hh => ?_⟩
    have hyU : y ∈ EX.lvlSet UX 1 := τ.retract_subset he₀
    -- the level-`1` point `z` over `Γ(v₀)`
    set z : ((rnSc m).prod EX) 1 := (c, y) with hzdef
    have hz : ((rnSc m).prod EX).toBase 1 z = Γ v₀ := by
      rw [ScBanach.prod_toBase, ScBanach.const_toBase, hy]; exact Prod.ext hv₀c.symm rfl
    have hΓG : Γ v₀ ∈ G := ⟨hΓv₀.2, by rw [mem_preimage, hpΓ _ hv₀V]; exact hv₀.1⟩
    have hzR₁ : z ∈ ((rnSc m).prod EX).lvlSet R₁.U 1 := by
      rw [ScBanach.mem_lvlSet, hz]
      refine ⟨t.retract_subset hΓv₀.1, ?_⟩
      change t (Γ v₀) ∈ G
      rw [t.apply_eq_self_of_mem_retract hΓv₀.1]; exact hΓG
    have hSlev : levelMap S 1 y = z := levelMap_eq_of_toBase_eq (by rw [hz, hSy])
    have hρv₀ : ρ v₀ = v₀ := hρfix v₀ hv₀ hv₀c
    have hptlev : levelMap (F := ScBanach.const N) (fun u => p (t u)) 1 z = v₀ :=
      levelMap_eq_of_toBase_eq (by
        rw [ScBanach.const_toBase, hz, t.apply_eq_self_of_mem_retract hΓv₀.1, hpΓ _ hv₀V])
    have hglev : levelMap (F := ScBanach.const N) g 1 z = v₀ :=
      levelMap_eq_of_toBase_eq (by
        rw [ScBanach.const_toBase, hz]
        change v₀ = ρ (p (t (Γ v₀)))
        rw [t.apply_eq_self_of_mem_retract hΓv₀.1, hpΓ _ hv₀V, hρv₀])
    -- the tangent space of `t(U)` at `z` is `DΓ(v₀)N`, and `p ∘ DΓ(v₀) = 1`
    have hQW := proposition_2_3_1_one t.isScRetract hW
    obtain ⟨-, hTz, hpD⟩ := tangentSpace_eq_range_graph hQW hV hpmap hΓmap hΓp hpΓ hv₀V hz
    rw [tangentSpace_inter_isOpen t.isScRetract hW (by rw [hz]; exact hΓv₀)] at hTz
    set DΓ := scDeriv (E := ScBanach.const N) V Γ v₀ with hDΓ
    have hzt : z ∈ ((rnSc m).prod EX).lvlSet t.retract 1 := by
      rw [ScBanach.mem_lvlSet, hz]; exact hΓv₀.1
    have hDt : scDeriv t.U t z (DΓ h) = DΓ h := by
      have hmem : DΓ h ∈ tangentSpace _ (univ ×ˢ CX) t.retract z := by rw [hTz]; exact ⟨h, rfl⟩
      rw [tangentSpace_eq_range t hzt] at hmem
      obtain ⟨b, hb⟩ := hmem
      rw [← hb]
      exact congrArg (fun L : ((rnSc m).prod EX) 0 →L[ℝ] ((rnSc m).prod EX) 0 => L b)
        (t.scDeriv_comp_self hzt)
    have hDt1 : scDeriv R₁.U R₁ z = scDeriv t.U t z :=
      scDeriv_eq_of_eqOn_relOpen R₁.relOpen R₁.isSc1 t.isSc1 subset_rfl (fun u hu => hu.1)
        (fun _ _ => rfl) hzR₁
    -- `Dρ(v₀)` as an sc-derivative
    have hρd : scDeriv (E := ScBanach.const N) (F := ScBanach.const N) D ρ v₀ =
        fderivWithin ℝ ρ D v₀ := by
      have h1 := hasFDerivWithinAt_scDeriv_const' (F := ScBanach.const N) hρsc.isSc1 hv₀
      have hUD : UniqueDiffWithinAt ℝ D v₀ := by
        have := hDrel.isScDomain.uniqueDiffWithinAt 0 v₀ (by rw [ScBanach.lvlSet_const]; exact hv₀)
        rwa [ScBanach.lvlSet_const] at this
      exact (h1.fderivWithin hUD).symm
    -- the chain rule
    have c5 := scDeriv_comp_apply_of_isScDomain R₁.isScDomain (isScDomain_univ _) R₁.isSc1
      (op.isScSmooth (isScDomain_univ _)).isSc1 (mapsTo_univ _ _) hzR₁ (DΓ h)
    rw [op.scDeriv_eq (isScDomain_univ _) (mem_univ _), hDt1, hDt] at c5
    have c4 := scDeriv_comp_apply_of_isScDomain R₁.isScDomain hDrel.isScDomain hpt.isSc1
      hρsc.isSc1 hptD hzR₁ (DΓ h)
    rw [hptlev] at c4
    have c3 := scDeriv_comp_apply_of_isScDomain R₁.isScDomain hV.isScDomain hgs.isSc1
      hΓs.isSc1 hgV hzR₁ (DΓ h)
    rw [hglev] at c3
    have c2 := scDeriv_comp_apply_of_isScDomain hUXrel.isScDomain R₁.isScDomain hSs.isSc1
      hT₁.isSc1 hSmap hyU (DΓ h).2
    rw [hSlev] at c2
    have c1 := scDeriv_comp_apply_of_isScDomain hUXrel.isScDomain (isScDomain_univ _)
      (IsScSmooth.comp hUXrel.isScDomain R₁.isScDomain hT₁ hSs hSmap).isSc1
      ((ScBanach.prodSndOp (rnSc m) EX).isScSmooth (isScDomain_univ _)).isSc1
      (mapsTo_univ _ _) hyU (DΓ h).2
    rw [(ScBanach.prodSndOp (rnSc m) EX).scDeriv_eq (isScDomain_univ _) (mem_univ _)] at c1
    -- `DS(y)w = (0, w) = DΓ(v₀)h`
    have hdS : scDeriv UX S y (DΓ h).2 = DΓ h := by
      rw [scDeriv_slice c hUXrel hyU]
      exact Prod.ext hh.symm rfl
    have hpDh : p (DΓ h) = h := hpD h
    have hρh : scDeriv (E := ScBanach.const N) (F := ScBanach.const N) D ρ v₀ h = h := by
      rw [hρd]; exact hDρ h hh
    rw [tangentSpace_eq_range τ (by rw [ScBanach.mem_lvlSet]; exact he₀)]
    refine ⟨(DΓ h).2, ?_⟩
    change scDeriv UX ((ScBanach.prodSndOp (rnSc m) EX) 0 ∘ ((fun u => Γ (g u)) ∘ S)) y
      (DΓ h).2 = (DΓ h).2
    rw [← c1, ← c2, hdS]
    change (scDeriv R₁.U (Γ ∘ g) z (DΓ h)).2 = (DΓ h).2
    rw [← c3]
    change (DΓ (scDeriv (F := ScBanach.const N) R₁.U (ρ ∘ fun u => p (t u)) z (DΓ h))).2 =
      (DΓ h).2
    rw [← c4]
    change (DΓ (scDeriv (E := ScBanach.const N) (F := ScBanach.const N) D ρ v₀
      (scDeriv (F := ScBanach.const N) R₁.U ((opToConst p) 0 ∘ R₁) z (DΓ h)))).2 = (DΓ h).2
    rw [← c5]
    change (DΓ (scDeriv (E := ScBanach.const N) (F := ScBanach.const N) D ρ v₀ (p (DΓ h)))).2 =
      (DΓ h).2
    rw [hpDh, hρh]
  exact ⟨τ, hplus, hret, rfl, fun e _ => rfl, htan⟩

end SliceRetraction


/-! ### General position of the slice -/

section SliceGeneralPosition

variable {m : ℕ} {EX : ScBanach} {CX : Set (EX 0)} {nX : ℕ} {WX : ScBanach}
  {TX : ScIso EX ((ScBanach.const (Fin nX → ℝ)).prod WX)} {nR : ℕ} {WR : ScBanach}
  {TR : ScIso (rnSc m) ((ScBanach.const (Fin nR → ℝ)).prod WR)}

/-- **The fibre over a regular value is in general position** (the text: "From our discussion we
conclude, in view of the assumption (2) of the theorem, ... that the tangent space
`T_{z'}({λ} × A_λ)` has a sc-complement in `T^R_{z'}X`"), in a product chart: let `t` be a
retraction onto the chart model of `A ⊆ ℝᵐ × X`, in general position at `z = (c, y)` (with respect
to the tame retraction `id × r` and the presentation `T_R × T_X`), and **regular at `z`**: the
first projection maps `T_z A ∩ E_z` (the tangent space of the stratum through `z`) onto `ℝᵐ`.  Let
`τ` be an sc⁺-retraction of `E` onto `Q ⊆ O` whose tangent space at `y` contains the second
components of the vectors of `T_zA` with vanishing first component (the tangent space of the
fibre).  Then `Q` is in general position at `y`: `T_yQ` has in `T_yO` an sc-complement contained
in `T_y^R O`.  *Proof*: for `w ∈ T_yO`, write `(0, w) = a + b` with `a ∈ T_zA`, `b ∈ T_z^R`
(general position of `A`); correct `a` by `a₂ ∈ T_zA ∩ E_z` with the same first component
(regularity): `w = (a − a₂)₂ + (b + a₂)₂ ∈ T_yQ + T_y^R O`; then `exists_scComplement_le`. -/
theorem isGeneralPositionRetractAt_slice (hTX : CX = TX 0 ⁻¹' quadrant nX WX 0)
    {RX : ScRetraction EX CX} (hRX : RX.IsTameWith TX)
    (t : ScRetraction ((rnSc m).prod EX) (univ ×ˢ CX))
    (htR : t.retract ⊆ ((ScRetraction.id (rn_relOpen_univ m)).prod RX).retract)
    {z : ((rnSc m).prod EX) 1} (hzt : z ∈ ((rnSc m).prod EX).lvlSet t.retract 1)
    (hgp : IsGeneralPositionRetractAt ((rnSc m).prod EX) (univ ×ˢ CX)
      ((ScRetraction.id (rn_relOpen_univ m)).prod RX).retract t.retract (prodPresentation TR TX) z)
    (hreg : ∀ μ : Fin m → ℝ, ∃ a ∈ tangentSpace ((rnSc m).prod EX) (univ ×ˢ CX) t.retract z,
      a ∈ minimalSubspaceWith (prodPresentation TR TX) (((rnSc m).prod EX).toBase 1 z) ∧ a.1 = μ)
    (τ : ScRetraction EX CX) (hτ : τ.IsScPlus) (hτR : τ.retract ⊆ RX.retract)
    (hyτ : z.2 ∈ EX.lvlSet τ.retract 1) (hys : z.2 ∈ EX.smoothLvl 1)
    (hTQ : ∀ a ∈ tangentSpace ((rnSc m).prod EX) (univ ×ˢ CX) t.retract z, a.1 = 0 →
      a.2 ∈ tangentSpace EX CX τ.retract z.2) :
    IsGeneralPositionRetractAt EX CX RX.retract τ.retract TX z.2 := by
  set y := z.2 with hydef
  set RZ := (ScRetraction.id (rn_relOpen_univ m)).prod RX with hRZ
  have hyR : y ∈ EX.lvlSet RX.retract 1 := hτR hyτ
  set MX : Submodule ℝ (EX 0) := LinearMap.range (scDeriv RX.U RX y : EX 0 →ₗ[ℝ] EX 0) with hMX
  have hM : (MX : Set (EX 0)) = tangentSpace EX CX RX.retract y :=
    (tangentSpace_eq_coe_submodule RX hyR).symm
  set Nτ : Submodule ℝ (EX 0) := LinearMap.range (scDeriv τ.U τ y : EX 0 →ₗ[ℝ] EX 0) with hNτdef
  have : FiniteDimensional ℝ Nτ := lemma_4_1_7_ii hτ hyτ
  have hNτ : (Nτ : Set (EX 0)) = tangentSpace EX CX τ.retract y :=
    (tangentSpace_eq_coe_submodule τ hyτ).symm
  have hNτs : Nτ ≤ EX.smooth :=
    (EX.proposition_1_1_7_iff Nτ).1 (τ.isScSplitting_range_scDeriv hyτ hys).1
  have hNM : Nτ ≤ MX := fun v hv => by
    have hv' : v ∈ tangentSpace EX CX τ.retract y := by rw [← hNτ]; exact hv
    have := tangentSpace_subset_of_subset RX τ.isScRetract hτR hyτ hv'
    rw [← hM] at this; exact this
  obtain ⟨-, hTRsc, -⟩ := proposition_2_5_6_partialCone hTX hRX hyR hys
  -- `T_zO_Z = ℝᵐ × T_yO`
  have hzRZ : z ∈ ((rnSc m).prod EX).lvlSet RZ.retract 1 := htR hzt
  have hzU : z ∈ ((rnSc m).prod EX).lvlSet (univ ×ˢ RX.U) 1 := RZ.lvlSet_retract_subset 1 hzRZ
  have hDRZ : scDeriv RZ.U RZ z = (scDeriv (E := rnSc m) (F := rnSc m) univ id z.1).prodMap
      (scDeriv RX.U RX z.2) :=
    scDeriv_prodMap (rn_relOpen_univ m) RX.relOpen (isScSmooth_id (isScDomain_univ _))
      RX.isScSmooth hzU
  obtain ⟨NZ, MZ, B, hNZ, hMZ, hBM, -, hsplit⟩ := hgp
  have hsplit0 := (hsplit 0).2
  rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero, ScBanach.levelSub_zero] at hsplit0
  have hMZeq : (MZ : Set _) = range (scDeriv RZ.U RZ z) := by
    rw [hMZ, tangentSpace_eq_range RZ hzRZ]
  have hNZM : NZ ≤ MZ := by rw [← hsplit0]; exact le_sup_left
  have hMeq : MX = Nτ ⊔ reducedTangentSpaceWith RX TX y := by
    refine le_antisymm (fun w hw => ?_) (sup_le hNM inf_le_left)
    obtain ⟨w', rfl⟩ := hw
    -- `(0, w) ∈ T_zO_Z`
    have h0w : ((0, scDeriv RX.U RX y w') : ((rnSc m).prod EX) 0) ∈ MZ := by
      rw [← SetLike.mem_coe, hMZeq]
      refine ⟨(0, w'), ?_⟩
      rw [hDRZ, ContinuousLinearMap.coe_prodMap', Prod.map_apply, map_zero]
    rw [← hsplit0] at h0w
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h0w
    have haT : a ∈ tangentSpace ((rnSc m).prod EX) (univ ×ˢ CX) t.retract z := by
      rw [← hNZ]; exact ha
    obtain ⟨a₂, ha₂T, ha₂E, ha₂1⟩ := hreg a.1
    have ha₂N : a₂ ∈ NZ := by rw [← SetLike.mem_coe, hNZ]; exact ha₂T
    -- `(a − a₂)₂ ∈ T_yQ`
    have h1 : (a - a₂).2 ∈ Nτ := by
      rw [← SetLike.mem_coe, hNτ]
      refine hTQ _ ?_ (by rw [Prod.fst_sub, ha₂1, sub_self])
      rw [← hNZ]; exact NZ.sub_mem ha ha₂N
    -- `(b + a₂)₂ ∈ T_y^R O`
    have hbE := (hBM hb).2
    have hr : b + a₂ ∈ MZ ⊓ minimalSubspaceWith (prodPresentation TR TX)
        (((rnSc m).prod EX).toBase 1 z) :=
      ⟨MZ.add_mem (hBM hb).1 (hNZM ha₂N), Submodule.add_mem _ hbE ha₂E⟩
    have h2 : (b + a₂).2 ∈ reducedTangentSpaceWith RX TX y := by
      refine ⟨?_, ?_⟩
      · have := hr.1
        rw [hMZeq, hDRZ] at this
        obtain ⟨u, hu⟩ := this
        exact ⟨u.2, by rw [← hu]; rfl⟩
      · have := hr.2
        rw [minimalSubspaceWith_prodPresentation, SetLike.mem_coe, Submodule.mem_prod] at this
        have h3 := this.2
        rw [ScBanach.prod_toBase] at h3
        exact h3
    have : scDeriv RX.U RX y w' = (a - a₂).2 + (b + a₂).2 := by
      have := congrArg Prod.snd hab
      simp only [Prod.snd_add] at this
      rw [Prod.snd_sub, Prod.snd_add]
      rw [← this]
      abel
    change scDeriv RX.U RX y w' ∈ _
    rw [this]
    exact Submodule.add_mem_sup h1 h2
  obtain ⟨B', hB'TR, hB', hsplit'⟩ := exists_scComplement_le hNτs hTRsc hMeq
  exact ⟨Nτ, MX, B', hNτ, hM, hB'TR, hB', hsplit'⟩

end SliceGeneralPosition


/-! ### The M-polyfold `ℝᵐ × X`: fibres and stratified regular points -/

section Family

universe u

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} [ParacompactSpace ((Fin m → ℝ) × X)]

/-- The fibre `A_λ = {x ∈ X | (λ, x) ∈ A}` of `A ⊆ ℝᵐ × X` over `λ`. -/
def fibreSet (A : Set ((Fin m → ℝ) × X)) (lam : Fin m → ℝ) : Set X := {x | (lam, x) ∈ A}

variable (m) in
/-- The presentation of `ℝᵐ` (the partial quadrant `ℝᵐ` of `ℝᵐ`) with no half-line coordinate. -/
def rnPres :
    ScIso (rnSc m) ((ScBanach.const (Fin 0 → ℝ)).prod (ScBanach.const (Fin m → ℝ))) :=
  scIsoOfLinearEquiv (LinearEquiv.uniqueProd (R := ℝ) (M := Fin m → ℝ) (M₂ := Fin 0 → ℝ)).symm

lemma rnPres_eq :
    (univ : Set ((rnSc m) 0)) = rnPres m 0 ⁻¹' quadrant 0 (ScBanach.const (Fin m → ℝ)) 0 := by
  ext x
  simp only [mem_univ, mem_preimage, true_iff]
  intro i
  exact i.elim0

variable (PX) in
/-- **Stratified regular point of the projection `p = P|_A : A → ℝᵐ`** (the text's "regular value
of `p_σ`" at a point of the open stratum `A ∩ F_σ°`, `σ` the set of local faces through the
point): in a product chart `(r ↦ r − a) × φ` of `ℝᵐ × X`, with the data `d` of Definition 4.2.1 (preprint 4.13) of
`A`, a presentation `T` of the partial quadrant of `φ` and the level-`1` point `y` over the image
of `z`, the projection to `ℝᵐ` (the derivative of `P` in the chart) maps `T_zA ∩ E_z` onto `ℝᵐ`;
`T_zA ∩ E_z` is the tangent space of the stratum through `z` (`E_z = ℝᵐ × (E_X)_{φ(z₂)}`, the
vectors whose coordinates vanish where those of `φ(z₂)` do).  Stated for some choice of data,
chart, presentation and lift, as Definitions 4.2.5 and 4.2.10 (preprint 4.16 and 4.21). -/
def IsStratRegularPoint (A : Set ((Fin m → ℝ) × X)) (z : (Fin m → ℝ) × X) : Prop :=
  z ∈ A ∧ ∃ (d : ((rnPolyfold m).prod PX).SubmanifoldData A) (a : Fin m → ℝ) (φ : MChart X)
    (n : ℕ) (Wq : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (y : ((rnSc m).prod φ.model.E) 1),
    z ∈ d.V ∧ PX.IsChart φ ∧ z.2 ∈ φ.source ∧ φ.model.C = T 0 ⁻¹' quadrant n Wq 0 ∧
    ((rnSc m).prod φ.model.E).toBase 1 y = ((rnChart m a).prod φ) z ∧
    ∀ μ : Fin m → ℝ, ∃ v ∈ tangentSpace ((rnSc m).prod φ.model.E) (univ ×ˢ φ.model.C)
      (((rnChart m a).prod φ) '' (d.toSubData.shrink ((rnChart m a).prod φ) ∩ A)) y,
      v.2 ∈ minimalSubspaceWith T (φ.model.E.toBase 1 y.2) ∧ v.1 = μ

variable (PX) in
/-- **Regular value** of `p = P|_A`, in the stratified sense of the proof of Theorem 4.3.1 (preprint 4.23): every
point of `A` over `λ` is a stratified regular point. -/
def IsStratRegularValue (A : Set ((Fin m → ℝ) × X)) (lam : Fin m → ℝ) : Prop :=
  ∀ z ∈ A, z.1 = lam → IsStratRegularPoint PX A z

variable (PX) in
/-- The conclusions of Theorem 4.3.1 (preprint 4.23) at one point `z = (λ, x)` of `A`: `z` is a stratified regular
point, `A_λ` is near `x` the image of an sc⁺-retraction (Definition 4.2.1 (preprint 4.13)), and `A_λ` is in
general position (Definition 4.2.10 (preprint 4.21)) and in good position (Definition 4.2.5 (preprint 4.16)) at `x`. -/
def FibreLocal (A : Set ((Fin m → ℝ) × X)) (z : (Fin m → ℝ) × X) : Prop :=
  IsStratRegularPoint PX A z ∧
    (∃ V : Set X, IsOpen V ∧ z.2 ∈ V ∧ ∃ s : X → X, PX.IsScPlusRetractionOn s V ∧
      s '' V = fibreSet A z.1 ∩ V) ∧
    PX.IsGeneralPositionAt (fibreSet A z.1) z.2 ∧ PX.IsGoodPositionAt (fibreSet A z.1) z.2

/-- **The local step of the proof of Theorem 4.3.1 (preprint 4.23)** (in the chart of Theorem 4.22 at `z₀`): for
`X` tame and `A ⊆ ℝᵐ × X` a smooth finite-dimensional submanifold in general position at every
point, every `z₀ ∈ A` has an open neighbourhood `U` and a **null set `CV ⊆ ℝᵐ`** (Lebesgue measure)
such that at every `z ∈ A ∩ U` with `z₁ ∉ CV` the conclusions of Theorem 4.3.1 (preprint 4.23) hold
(`FibreLocal`).  *Proof*: the product chart `(r ↦ r − λ₀) × φ`, `φ` a tame chart of `X` centred at
`x₀` (re-centring), is a tame chart of `ℝᵐ × X` centred at `z₀`; in it Theorem 4.2.11 (preprint 4.22)
(`theorem_4_2_11_chart`) describes `A` as the graph `Γ(V)` over a relatively open `V` of the partial
quadrant `N ∩ C` of `N = T₀A` (`C = {ℓ ≥ 0}` for the coordinates `ℓ` of the chart, onto `ℝⁿ`).
`f = P ∘ χ⁻¹ ∘ Γ` is `C^∞` on `V`, and `CV = f(stratCritSet)` is null by Sard's theorem on the
strata (`measure_image_stratCritSet`).  At `z ∈ A ∩ U` with `z₁ ∉ CV`, `v₀ = p(χ z)` is
stratified-regular, `exists_fibre_retraction` gives the retraction `ρ` onto the fibre of `f`,
`exists_slice_retraction` the sc⁺-retraction `τ` of the model of `X` onto the chart image of
`A_{z₁}`, `isScPlusRetractionOn_of_chart` the sc⁺-retraction on an open subset of `X`, and
`isGeneralPositionRetractAt_slice` general position (good position by
`IsGeneralPositionRetractAt.isGoodPositionRetractAt`). -/
theorem exists_local_family (hX : PX.IsTame) {A : Set ((Fin m → ℝ) × X)}
    (hA : ((rnPolyfold m).prod PX).IsSmoothSubmanifold A)
    (hgp : ∀ z ∈ A, ((rnPolyfold m).prod PX).IsGeneralPositionAt A z)
    {z₀ : (Fin m → ℝ) × X} (hz₀ : z₀ ∈ A) :
    ∃ U : Set ((Fin m → ℝ) × X), IsOpen U ∧ z₀ ∈ U ∧ ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
      ∀ z ∈ A ∩ U, z.1 ∉ CV → FibreLocal PX A z := by
  classical
  -- the tame chart `φ` of `X` centred at `x₀`
  have hx₀s : z₀.2 ∈ PX.smoothSet := prod_rn_mem_smoothSet_iff.1 (hA.subset_smoothSet hz₀)
  obtain ⟨φ, hφ, hx₀φ, hφ0, htame⟩ := hX.exists_centredChart hx₀s
  obtain ⟨RX, hRX, hRXt⟩ := htame
  obtain ⟨nX, WX, TX, hTX⟩ := φ.model.isPartialQuadrant
  have hRXT := hRXt nX WX TX hTX
  -- the product chart `χ = (r ↦ r − λ₀) × φ`, centred at `z₀`
  set χ := (rnChart m z₀.1).prod φ with hχdef
  have hχ : ((rnPolyfold m).prod PX).IsChart χ :=
    MPolyfold.IsChart.prod (isChart_rnChart z₀.1) hφ
  have hz₀χ : z₀ ∈ χ.source := ⟨mem_univ _, hx₀φ⟩
  have hχ0 : χ z₀ = 0 := Prod.ext (sub_self _) hφ0
  set RZ := (ScRetraction.id (rn_relOpen_univ m)).prod RX with hRZdef
  have hRZ : RZ.retract = χ.model.O := by
    rw [hRZdef, ScRetraction.prod_retract, hRX]
    change (id '' univ) ×ˢ φ.model.O = univ ×ˢ φ.model.O
    rw [image_id]
  set TZ := prodPresentation (rnPres m) TX with hTZdef
  have hTZ : χ.model.C =
      TZ 0 ⁻¹' quadrant (0 + nX) ((ScBanach.const (Fin m → ℝ)).prod WX) 0 :=
    prod_eq_prodPresentation (rnPres m) TX rnPres_eq hTX
  have hRZT : RZ.IsTameWith TZ := ScRetraction.IsTameWith.prod rnPres_eq hTX
    (ScRetraction.id_isTame (rn_relOpen_univ m) 0 _ (rnPres m) rnPres_eq) hRXT
  -- the chart retraction `t` of `A` in `χ` and Theorem 4.2.11 (preprint 4.22) in the chart
  set d := hA.data hz₀ with hd
  have hz₀d : z₀ ∈ d.V := hA.mem_data_V hz₀
  have hz₀W : z₀ ∈ d.toSubData.shrink χ := d.toSubData.mem_shrink χ hz₀ hz₀d hz₀χ
  obtain ⟨t, ht, htp, -, -, Gd, -, htU, hGdimg⟩ :
      ∃ t : ScRetraction ((rnSc m).prod φ.model.E) (univ ×ˢ φ.model.C),
        t.retract = χ '' (d.toSubData.shrink χ ∩ A) ∧ t.IsScPlus ∧ t.U ⊆ RZ.U ∧
        (∀ u ∈ t.U, t u = (χ ∘ d.s ∘ χ.symm) (RZ u)) ∧
        ∃ G : Set (((rnSc m).prod φ.model.E) 0), IsOpen G ∧ t.U = RZ.U ∩ RZ ⁻¹' G ∧
          χ '' d.toSubData.shrink χ = χ.model.O ∩ G :=
    d.exists_chartRetraction hχ
      (((rnPolyfold m).prod PX).levelMk 1 z₀ (hA.mem_levelSet_one hz₀)) RZ hRZ
  have htR : t.retract ⊆ RZ.retract := by
    rw [ht, hRZ]; exact χ.image_subset_model fun _ hy => d.toSubData.shrink_subset_source χ hy.1
  have h0 : (0 : χ.model.E 0) ∈ t.retract := by rw [ht, ← hχ0]; exact ⟨z₀, ⟨hz₀W, hz₀⟩, rfl⟩
  have h0O : (0 : χ.model.E 0) ∈ RZ.retract := htR h0
  have h01 : χ.model.E.toBase 1 (0 : χ.model.E 1) ∈ t.retract := by rw [map_zero]; exact h0
  set N : Submodule ℝ (((rnSc m).prod φ.model.E) 0) :=
    LinearMap.range (scDeriv t.U t 0 :
      ((rnSc m).prod φ.model.E) 0 →ₗ[ℝ] ((rnSc m).prod φ.model.E) 0) with hNdef
  have : FiniteDimensional ℝ N := lemma_4_1_7_ii htp h01
  have hN : (N : Set (((rnSc m).prod φ.model.E) 0)) =
      tangentSpace ((rnSc m).prod φ.model.E) (univ ×ˢ φ.model.C) t.retract 0 :=
    (tangentSpace_eq_coe_submodule t h01).symm
  have hz0 : χ.model.E.toBase 1 0 = χ z₀ := by rw [map_zero, hχ0]
  have hgp0 : IsGeneralPositionRetractAt χ.model.E χ.model.C RZ.retract t.retract TZ 0 := by
    have h1 := (hgp z₀ hz₀).isGeneralPositionChart d hχ TZ hTZ hz₀d hz₀χ hz0
    have h2 : IsGeneralPositionRetractAt χ.model.E χ.model.C χ.model.O
        (χ '' (d.toSubData.shrink χ ∩ A)) TZ 0 := h1
    rw [← hRZ, ← ht] at h2
    exact h2
  obtain ⟨hsup, -, Y, p, W, V, Γ, hYE, -, -, hpN, -, hker, hW, h0W, hV, -, hΓs, hpΓ, -, -, hΓp, -,
    hpmap, hΓmap, -, hgen⟩ := theorem_4_2_11_chart TZ hTZ hRZT h0O t htp htR h0 hN hgp0
  -- the finite-dimensional data: coordinates `ℓ`, the relatively open `V`, `f = P ∘ χ⁻¹ ∘ Γ`
  set ℓ := coordsOn TZ N with hℓdef
  have hℓ : Surjective ℓ := coordsOn_surjective TZ hsup
  have hquad : (Subtype.val ⁻¹' χ.model.C : Set N) = quadC ℓ := by rw [hTZ]; rfl
  obtain ⟨OV, hOV, hVeq⟩ := hV.relOpen
  have hV' : V = OV ∩ quadC ℓ := by rw [hVeq, hquad]
  set f : N → (Fin m → ℝ) := fun v => (Γ v).1 + z₀.1 with hfdef
  have hfV : ContDiffOn ℝ ∞ f V := by
    have h1 : IsScSmooth (E := ScBanach.const N) (F := rnSc m) V (fun v => (Γ v).1) :=
      IsScSmooth.comp hV.isScDomain (isScDomain_univ _)
        ((ScBanach.prodFstOp (rnSc m) φ.model.E).isScSmooth (isScDomain_univ _)) hΓs
        (mapsTo_univ _ _)
    exact ((isScSmooth_iff_contDiffOn_const hV.isScDomain _).1 h1).add contDiffOn_const
  have hfV' : ContDiffOn ℝ ∞ f (OV ∩ quadC ℓ) := by rw [← hV']; exact hfV
  -- the neighbourhood `U` and the critical values
  set U : Set ((Fin m → ℝ) × X) := d.toSubData.shrink χ ∩ χ ⁻¹' W with hUdef
  have hUo : IsOpen U :=
    (χ.continuousOn_toFun.mono (d.toSubData.shrink_subset_source χ)).isOpen_inter_preimage
      (d.toSubData.isOpen_shrink χ) hW
  have hz₀U : z₀ ∈ U := ⟨hz₀W, by change χ z₀ ∈ W; rw [hχ0]; exact h0W⟩
  refine ⟨U, hUo, hz₀U, f '' stratCritSet ℓ f (OV ∩ quadC ℓ),
    measure_image_stratCritSet ℓ volume hOV hfV', fun z hz hzCV => ?_⟩
  -- the point `z ∈ A ∩ U` and `v₀ = p(χ z)`
  obtain ⟨hzA, hzS, hzW⟩ := hz
  have hzχ : z ∈ χ.source := d.toSubData.shrink_subset_source χ hzS
  have hχzt : χ z ∈ t.retract := by rw [ht]; exact ⟨z, ⟨hzS, hzA⟩, rfl⟩
  have hχzQW : χ z ∈ t.retract ∩ W := ⟨hχzt, hzW⟩
  set v₀ := p (χ z) with hv₀def
  have hv₀V : v₀ ∈ V := hpmap.mapsTo hχzQW
  have hΓv₀ : Γ v₀ = χ z := hΓp _ hχzQW
  have hΓv₀1 : (Γ v₀).1 = z.1 - z₀.1 := by rw [hΓv₀]; rfl
  have hΓv₀2 : (Γ v₀).2 = φ z.2 := by rw [hΓv₀]; rfl
  have hfv₀ : f v₀ = z.1 := by
    change (Γ v₀).1 + z₀.1 = z.1
    rw [hΓv₀1, sub_add_cancel]
  have hv₀U : v₀ ∈ OV ∩ quadC ℓ := by rw [← hV']; exact hv₀V
  have hreg : v₀ ∉ stratCritSet ℓ f (OV ∩ quadC ℓ) := fun h => hzCV ⟨v₀, h, hfv₀⟩
  have hregs : Surjective ((fderivWithin ℝ f (OV ∩ quadC ℓ) v₀).comp
      (stratSub ℓ (zeroSetOf ℓ v₀)).subtypeL) := by
    by_contra h; exact hreg ⟨hv₀U, h⟩
  obtain ⟨O', ρ, hO', hv₀O', hO'OV, hρcd, hρmap, hρf, hρfix, -, hDρfix⟩ :=
    exists_fibre_retraction ℓ hℓ hOV hfV' hv₀U hreg
  -- the derivative of `f` at `v₀` is `(DΓ(v₀) ·)₁`
  set DΓ := scDeriv (E := ScBanach.const N) V Γ v₀ with hDΓdef
  have hΓd : HasFDerivWithinAt Γ DΓ V v₀ := hasFDerivWithinAt_scDeriv_const hΓs.isSc1 hv₀V
  have hfd : HasFDerivWithinAt f
      ((ContinuousLinearMap.fst ℝ (Fin m → ℝ) (φ.model.E 0)).comp DΓ) V v₀ :=
    ((ContinuousLinearMap.fst ℝ (Fin m → ℝ) (φ.model.E 0)).hasFDerivAt.comp_hasFDerivWithinAt v₀
      hΓd).add_const z₀.1
  have hUDV : UniqueDiffWithinAt ℝ (OV ∩ quadC ℓ) v₀ :=
    uniqueDiffWithinAt_quadC ℓ hℓ hOV hv₀U
  have hDf : fderivWithin ℝ f (OV ∩ quadC ℓ) v₀ =
      (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (φ.model.E 0)).comp DΓ := by
    rw [hV'] at hfd; exact hfd.fderivWithin hUDV
  -- the tangent space of `t(U)` along the graph
  have hQW : IsScRetract ((rnSc m).prod φ.model.E) (univ ×ˢ φ.model.C) (t.retract ∩ W) :=
    proposition_2_3_1_one t.isScRetract hW
  -- the fibre in `N`: `f v = f v₀` iff `(Γ v)₁ = (Γ v₀)₁`
  have hfeq : ∀ v, f v = f v₀ ↔ (Γ v).1 = (Γ v₀).1 := fun v => by
    change (Γ v).1 + z₀.1 = (Γ v₀).1 + z₀.1 ↔ _
    exact add_left_inj _
  have hquad' : (Subtype.val ⁻¹' (univ ×ˢ φ.model.C) : Set N) = quadC ℓ := hquad
  have hO'V : O' ∩ Subtype.val ⁻¹' (univ ×ˢ φ.model.C) ⊆ V := by
    rw [hquad', hV']; exact fun v hv => ⟨hO'OV hv.1, hv.2⟩
  -- the sc⁺-retraction `τ` onto the chart image of `A_{z₁}`
  obtain ⟨τ, hτp, hτret, hτU, -, htan⟩ := exists_slice_retraction φ.model.isPartialQuadrant t htp
    hW hV hΓs hpΓ hΓp hpmap hΓmap hO' hO'V (by rw [hquad']; exact hρcd)
    (by rw [hquad']; exact hρmap) (Γ v₀).1
    (by rw [hquad']; exact fun v hv => (hfeq (ρ v)).1 (hρf v hv))
    (by rw [hquad']; exact fun v hv hv1 => hρfix v hv ((hfeq v).2 hv1))
    (by rw [hquad']; exact ⟨hv₀O', hv₀U.2⟩) rfl
    (by
      rw [hquad']
      intro h hh
      refine hDρfix h ?_
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hDf]
      exact hh)
  have hτO : τ.retract ⊆ φ.model.O := fun e he => by
    have h1 := htR ((hτret e).1 he).1.1
    rw [hRZ] at h1
    exact h1.2
  have hτR : τ.retract ⊆ RX.retract := by rw [hRX]; exact hτO
  -- the image of `z₂` and the open set `V_X` of `X`
  have hχz' : (((Γ v₀).1, φ z.2) : ((rnSc m).prod φ.model.E) 0) = Γ v₀ :=
    Prod.ext rfl hΓv₀2.symm
  have hxτ : φ z.2 ∈ τ.retract := (hτret _).2 ⟨by rw [hχz']; exact hΓmap.mapsTo hv₀V,
    by rw [hχz', hpΓ _ hv₀V]; exact hv₀O'⟩
  obtain ⟨hVXo, hs, himg⟩ := MPolyfold.isScPlusRetractionOn_of_chart hφ τ hτp hτO
  set VX := φ.source ∩ φ ⁻¹' τ.U with hVX
  have hxVX : z.2 ∈ VX := ⟨hzχ.2, τ.retract_subset hxτ⟩
  -- `φ⁻¹(τ(U)) = A_{z₁} ∩ V_X`
  have hχx : ∀ x' ∈ φ.source, χ (z.1, x') = (((Γ v₀).1, φ x') : ((rnSc m).prod φ.model.E) 0) :=
    fun x' _ => Prod.ext hΓv₀1.symm rfl
  have hfib : φ.source ∩ φ ⁻¹' τ.retract = fibreSet A z.1 ∩ VX := by
    ext x'
    constructor
    · rintro ⟨hx', hτx'⟩
      have h1 := (hτret (φ x')).1 hτx'
      have h2 : χ (z.1, x') ∈ t.retract := by rw [hχx x' hx']; exact h1.1.1
      rw [ht] at h2
      obtain ⟨w, ⟨hwS, hwA⟩, hw⟩ := h2
      have hwx : w = (z.1, x') := χ.toPartialEquiv.injOn
        (d.toSubData.shrink_subset_source χ hwS) ⟨mem_univ _, hx'⟩ hw
      refine ⟨?_, hx', τ.retract_subset hτx'⟩
      change (z.1, x') ∈ A
      rw [← hwx]; exact hwA
    · rintro ⟨hx'A, hx'φ, hx'τU⟩
      refine ⟨hx'φ, ?_⟩
      have hx'U : φ x' ∈ τ.U := hx'τU
      rw [hτU] at hx'U
      obtain ⟨hU1, hU2, hU3⟩ := hx'U
      have hx'O : φ x' ∈ φ.model.O := φ.mapsTo_model x' hx'φ
      have hRZx : RZ ((Γ v₀).1, φ x') = ((Γ v₀).1, φ x') :=
        RZ.apply_eq_self_of_mem_retract (by rw [hRZ]; exact ⟨mem_univ _, hx'O⟩)
      have hU1' := hU1
      rw [htU] at hU1'
      have hGx : (((Γ v₀).1, φ x') : ((rnSc m).prod φ.model.E) 0) ∈
          χ '' d.toSubData.shrink χ := by
        rw [hGdimg]
        refine ⟨⟨mem_univ _, hx'O⟩, ?_⟩
        have := hU1'.2
        change RZ ((Γ v₀).1, φ x') ∈ Gd at this
        rwa [hRZx] at this
      obtain ⟨w, hwS, hw⟩ := hGx
      have hwx : w = (z.1, x') := χ.toPartialEquiv.injOn
        (d.toSubData.shrink_subset_source χ hwS) ⟨mem_univ _, hx'φ⟩ (hw.trans (hχx x' hx'φ).symm)
      have hct : (((Γ v₀).1, φ x') : ((rnSc m).prod φ.model.E) 0) ∈ t.retract := by
        rw [ht]
        refine ⟨w, ⟨hwS, ?_⟩, hw⟩
        rw [hwx]; exact hx'A
      refine (hτret (φ x')).2 ⟨⟨hct, ?_⟩, ?_⟩
      · rwa [t.apply_eq_self_of_mem_retract hct] at hU2
      · rwa [t.apply_eq_self_of_mem_retract hct] at hU3
  -- the data of Definition 4.2.1 (preprint 4.13) for `A_{z₁}` at `z₂`
  let d' : PX.SubmanifoldData (fibreSet A z.1) :=
    ⟨VX, φ.symm ∘ τ ∘ φ, hVXo, hs, himg.trans hfib⟩
  have hshrink : φ '' (d'.toSubData.shrink φ ∩ fibreSet A z.1) = τ.retract := by
    have hsh : d'.toSubData.shrink φ = VX := by
      ext x'
      constructor
      · rintro ⟨⟨hx'V, -⟩, -⟩; exact hx'V
      · intro hx'
        exact ⟨⟨hx', hx'.1⟩, hs.mapsTo hx', (hs.mapsTo hx').1⟩
    rw [hsh, inter_comm, ← hfib]
    ext e
    constructor
    · rintro ⟨x', ⟨-, hx'⟩, rfl⟩; exact hx'
    · intro he
      exact ⟨φ.symm e, ⟨φ.symm_mapsTo (hτO he), by
        rw [mem_preimage, φ.apply_symm_apply (hτO he)]; exact he⟩,
        φ.apply_symm_apply (hτO he)⟩
  -- the level-`1` points over `φ(z₂)` and `χ(z)`
  obtain ⟨yX, hyX, hyXs⟩ := exists_smoothLvl_one_of_mem_smooth (lemma_4_1_7_i hτp hxτ)
  set yZ : ((rnSc m).prod φ.model.E) 1 := ((Γ v₀).1, yX) with hyZdef
  have hyZ : ((rnSc m).prod φ.model.E).toBase 1 yZ = Γ v₀ := by
    rw [ScBanach.prod_toBase, ScBanach.const_toBase, hyX]
    exact hχz'
  have hyZt : yZ ∈ ((rnSc m).prod φ.model.E).lvlSet t.retract 1 := by
    change ((rnSc m).prod φ.model.E).toBase 1 yZ ∈ t.retract
    rw [hyZ]; exact (hΓmap.mapsTo hv₀V).1
  have hyXτ : yX ∈ φ.model.E.lvlSet τ.retract 1 := by rw [ScBanach.mem_lvlSet, hyX]; exact hxτ
  -- `T_{yZ}(t(U)) = DΓ(v₀)N`, `p ∘ DΓ(v₀) = 1`
  obtain ⟨-, hTz, hpD⟩ := tangentSpace_eq_range_graph hQW hV hpmap hΓmap hΓp hpΓ hv₀V hyZ
  have hTinter : tangentSpace ((rnSc m).prod φ.model.E) (univ ×ˢ φ.model.C) (t.retract ∩ W) yZ =
      tangentSpace ((rnSc m).prod φ.model.E) (univ ×ˢ φ.model.C) t.retract yZ :=
    tangentSpace_inter_isOpen t.isScRetract hW (by rw [hyZ]; exact hΓmap.mapsTo hv₀V)
  rw [hTinter] at hTz
  -- regularity at `yZ`: `T_zA ∩ E_z` is mapped onto `ℝᵐ`
  have hcoord : ∀ i, (TZ 0 (Γ v₀)).1 i = (TZ 0 (v₀ : ((rnSc m).prod φ.model.E) 0)).1 i :=
    fun i => by
      have hY0 : Γ v₀ - v₀ ∈ minimalSubspaceWith TZ 0 :=
        hYE (hker _ (by rw [map_sub, hpΓ _ hv₀V, hpN, sub_self]))
      have := coord_add_of_mem_zero TZ (x := (v₀ : ((rnSc m).prod φ.model.E) 0)) hY0 i
      rwa [add_sub_cancel] at this
  have hreg' : ∀ μ : Fin m → ℝ, ∃ a ∈ tangentSpace ((rnSc m).prod φ.model.E)
      (univ ×ˢ φ.model.C) t.retract yZ,
      a ∈ minimalSubspaceWith TZ (((rnSc m).prod φ.model.E).toBase 1 yZ) ∧ a.1 = μ := by
    intro μ
    obtain ⟨h, hh⟩ := hregs μ
    refine ⟨DΓ h, by rw [hTz]; exact ⟨h, rfl⟩, ?_, ?_⟩
    · rw [hyZ]
      have hdiff : DΓ h - h ∈ minimalSubspaceWith TZ 0 :=
        hYE (hker _ (by rw [map_sub, hpD, hpN, sub_self]))
      have hh0 : (h : ((rnSc m).prod φ.model.E) 0) ∈ minimalSubspaceWith TZ (Γ v₀) := by
        rw [mem_minimalSubspaceWith]
        intro i hi
        rw [hcoord i] at hi
        exact h.2 i ((mem_zeroSetOf ℓ).2 hi)
      have : DΓ h = (h : ((rnSc m).prod φ.model.E) 0) + (DΓ h - h) := by abel
      rw [this]
      exact Submodule.add_mem _ hh0 (minimalSubspaceWith_zero_le TZ _ hdiff)
    · have := hh
      rw [ContinuousLinearMap.comp_apply, hDf] at this
      exact this
  -- general position of the slice, in the chart `φ`
  have hgpX : IsGeneralPositionRetractAt φ.model.E φ.model.C RX.retract τ.retract TX yX :=
    isGeneralPositionRetractAt_slice hTX hRXT t htR hyZt
      (hgen (Γ v₀) (hΓmap.mapsTo hv₀V) yZ hyZ) hreg' τ hτp hτR hyXτ hyXs
      (fun a ha ha1 => by
        rw [hTz] at ha
        obtain ⟨h, rfl⟩ := ha
        exact (htan yX (hyX.trans hΓv₀2.symm)).2 h ha1)
  have hyXR : yX ∈ φ.model.E.lvlSet RX.retract 1 := hτR hyXτ
  have hx : z.2 ∈ fibreSet A z.1 := hzA
  refine ⟨⟨hzA, d, z₀.1, φ, nX, WX, TX, yZ, hzS.1.1, hφ, hzχ.2, hTX, by rw [hyZ, hΓv₀], ?_⟩,
    ⟨VX, hVXo, hxVX, φ.symm ∘ τ ∘ φ, hs, himg.trans hfib⟩,
    ⟨hx, d', φ, nX, WX, TX, yX, hxVX, hφ, hzχ.2, hTX, hyX, ?_⟩,
    ⟨hx, d', φ, nX, WX, TX, yX, hxVX, hφ, hzχ.2, hTX, hyX, ?_⟩⟩
  · -- the stratified regularity in the chart `χ`
    intro μ
    obtain ⟨a, haT, haE, ha1⟩ := hreg' μ
    refine ⟨a, by rw [ht] at haT; exact haT, ?_, ha1⟩
    rw [minimalSubspaceWith_prodPresentation, Submodule.mem_prod, ScBanach.prod_toBase] at haE
    exact haE.2
  · change IsGeneralPositionRetractAt φ.model.E φ.model.C φ.model.O
      (φ '' (d'.toSubData.shrink φ ∩ fibreSet A z.1)) TX yX
    rw [hshrink, ← hRX]
    exact hgpX
  · change IsGoodPositionRetractAt φ.model.E φ.model.C φ.model.O
      (φ '' (d'.toSubData.shrink φ ∩ fibreSet A z.1)) TX yX
    rw [hshrink, ← hRX]
    exact hgpX.isGoodPositionRetractAt TX hRXT hyXR hyXs


/-- **Theorem 4.3.1 (preprint 4.23), for an arbitrary set of parameters**: for `X` tame and `A ⊆ ℝᵐ × X` a smooth
finite-dimensional submanifold with compact closure, in general position at every point, and any
`S ⊆ ℝᵐ`, there is `Σ ⊆ S` with `S ∖ Σ` a Lebesgue null set such that every `λ ∈ Σ` is a
(stratified) regular value of `p = P|_A` and the conclusions of the theorem hold at every point of
`A_λ` (`FibreLocal`).  *Proof*: `exists_local_family` at every point of `A`; `A` is second
countable (`cl(A)` is compact in the metrizable `ℝᵐ × X`, Theorem 2.3.10 (preprint 2.16)), so countably many of the
neighbourhoods `U(z_i)` cover `A` — the text's finite cover of `{|p| ≤ ε}` does not exist in
general (Findings) — and `Σ = S ∖ ⋃_i CV(z_i)`. -/
theorem theorem_4_3_1_of_subset (hX : PX.IsTame) {A : Set ((Fin m → ℝ) × X)}
    (hA : ((rnPolyfold m).prod PX).IsSmoothSubmanifold A) (hcl : IsCompact (closure A))
    (h2 : ∀ z ∈ A, ((rnPolyfold m).prod PX).IsGeneralPositionAt A z) (S : Set (Fin m → ℝ)) :
    ∃ Sig ⊆ S, volume (S \ Sig) = 0 ∧ ∀ lam ∈ Sig, IsStratRegularValue PX A lam ∧
      ∀ x ∈ fibreSet A lam, FibreLocal PX A (lam, x) := by
  classical
  have hloc : ∀ z : A, ∃ U : Set ((Fin m → ℝ) × X), IsOpen U ∧ (z : (Fin m → ℝ) × X) ∈ U ∧
      ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧ ∀ w ∈ A ∩ U, w.1 ∉ CV → FibreLocal PX A w :=
    fun z => exists_local_family hX hA h2 z.2
  choose U hUo hzU CV hCV hfl using hloc
  -- `A` is second countable: a countable subcover
  have := ((rnPolyfold m).prod PX).metrizableSpace
  have hsep : TopologicalSpace.IsSeparable A := hcl.isSeparable.mono subset_closure
  have := hsep.secondCountableTopology
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (α := A)
    (fun z : A => Subtype.val ⁻¹' U z) (fun z => (hUo z).preimage continuous_subtype_val)
  have hcov : ∀ w ∈ A, ∃ z ∈ T, w ∈ U z := by
    intro w hw
    have : (⟨w, hw⟩ : A) ∈ ⋃ z, (Subtype.val ⁻¹' U z : Set A) :=
      mem_iUnion.2 ⟨⟨w, hw⟩, hzU _⟩
    rw [← hTU] at this
    obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.1 this
    exact ⟨z, hz, hwz⟩
  have hBad : volume (⋃ z ∈ T, CV z) = 0 := (measure_biUnion_null_iff hTc).2 fun z _ => hCV z
  refine ⟨S \ ⋃ z ∈ T, CV z, sdiff_subset, ?_, fun lam hlam => ?_⟩
  · refine measure_mono_null (fun x hx => ?_) hBad
    by_contra h
    exact hx.2 ⟨hx.1, h⟩
  · have key : ∀ w ∈ A, w.1 = lam → FibreLocal PX A w := by
      intro w hw hwl
      obtain ⟨z, hzT, hwz⟩ := hcov w hw
      refine hfl z w ⟨hw, hwz⟩ ?_
      rw [hwl]
      intro hc
      exact hlam.2 (mem_iUnion₂.2 ⟨z, hzT, hc⟩)
    exact ⟨fun w hw hwl => (key w hw hwl).1, fun x hx => key (lam, x) hx rfl⟩

/-- **Theorem 4.3.1 (preprint 4.23) (families and Sard's theorem).**  Let `X` be a tame M-polyfold and
`A ⊆ ℝᵐ × X` a smooth finite-dimensional submanifold of the tame M-polyfold `ℝᵐ × X` (Definition
4.13), whose induced M-polyfold structure is tame and whose closure is compact.  Let `ε > 0` with
(1) for `|λ| ≤ ε` the fibre `p⁻¹(λ) = A ∩ P⁻¹(λ)` of `p = P|_A` is compact and non-empty, and
(2) `A` is in general position at every point (Definition 4.2.10 (preprint 4.21); the text's hypothesis (2) is
misprinted).  Then there is a set `Σ ⊆ {|λ| < ε}` of full Lebesgue measure in `{|λ| < ε}`
(`|λ|² = Σ λ_i²`) consisting of **regular values** of `p` (stratified: `IsStratRegularValue`),
such that for `λ ∈ Σ` the fibre `A_λ = {x | (λ, x) ∈ A}` is **compact**, a **smooth
finite-dimensional submanifold** of `X`, in **general position** at each of its points, and with
its induced structure **a manifold with boundary with corners** (Definition 4.1.1 (preprint 4.1),
`HasCornerStructure`) and tame.
*Proof*: `theorem_4_3_1_of_subset` for the open ball; compactness from (1) (`A_λ` is the image of
`p⁻¹(λ)` under the projection to `X`); the corner structure is Theorem 4.2.7 (preprint 4.18) for `A_λ`, good
position following from general position.  The hypotheses "the induced structure on `A` is tame"
and "`p⁻¹(λ)` non-empty" are not used (Findings). -/
theorem theorem_4_3_1_preprint (hX : PX.IsTame) {A : Set ((Fin m → ℝ) × X)}
    (hA : ((rnPolyfold m).prod PX).IsSmoothSubmanifold A) [ParacompactSpace A]
    (_hAt : ((rnPolyfold m).prod PX).IsTameSubmanifold A) (hcl : IsCompact (closure A))
    {ε : ℝ} (_hε : 0 < ε)
    (h1 : ∀ lam : Fin m → ℝ, ∑ i, lam i ^ 2 ≤ ε ^ 2 →
      IsCompact (A ∩ Prod.fst ⁻¹' {lam}) ∧ (A ∩ Prod.fst ⁻¹' {lam}).Nonempty)
    (h2 : ∀ z ∈ A, ((rnPolyfold m).prod PX).IsGeneralPositionAt A z) :
    ∃ Sig ⊆ {lam : Fin m → ℝ | ∑ i, lam i ^ 2 < ε ^ 2},
      volume ({lam : Fin m → ℝ | ∑ i, lam i ^ 2 < ε ^ 2} \ Sig) = 0 ∧
      ∀ lam ∈ Sig, IsStratRegularValue PX A lam ∧ IsCompact (fibreSet A lam) ∧
        ∃ hF : PX.IsSmoothSubmanifold (fibreSet A lam),
          (∀ x ∈ fibreSet A lam, PX.IsGeneralPositionAt (fibreSet A lam) x) ∧
          haveI := PX.paracompactSpace_subtype (fibreSet A lam)
          (MPolyfold.subPolyfold hF.isSubMPolyfold).HasCornerStructure ∧
            PX.IsTameSubmanifold (fibreSet A lam) := by
  obtain ⟨Sig, hSig, hnull, hprop⟩ :=
    theorem_4_3_1_of_subset hX hA hcl h2 {lam : Fin m → ℝ | ∑ i, lam i ^ 2 < ε ^ 2}
  refine ⟨Sig, hSig, hnull, fun lam hlam => ?_⟩
  obtain ⟨hreg, hloc⟩ := hprop lam hlam
  have hlamε : ∑ i, lam i ^ 2 ≤ ε ^ 2 := (hSig hlam).le
  have hcpt : IsCompact (fibreSet A lam) := by
    have := (h1 lam hlamε).1.image continuous_snd
    convert this using 1
    ext x
    constructor
    · intro hx
      exact ⟨(lam, x), ⟨hx, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨hw, hw1⟩, rfl⟩
      have hw1' : w.1 = lam := hw1
      change (lam, w.2) ∈ A
      rw [← hw1']
      exact hw
  have hF : PX.IsSmoothSubmanifold (fibreSet A lam) := fun x hx => by
    obtain ⟨-, ⟨V, hV, hxV, s, hs, himg⟩, -, -⟩ := hloc x hx
    exact ⟨V, hV, hxV, s, hs, himg⟩
  have := PX.paracompactSpace_subtype (fibreSet A lam)
  have hgpF : ∀ x ∈ fibreSet A lam, PX.IsGeneralPositionAt (fibreSet A lam) x :=
    fun x hx => (hloc x hx).2.2.1
  have hgoodF : ∀ x ∈ fibreSet A lam, PX.IsGoodPositionAt (fibreSet A lam) x :=
    fun x hx => (hloc x hx).2.2.2
  obtain ⟨hcs, htameF⟩ := MPolyfold.theorem_4_2_7 hX hF hgoodF
  exact ⟨hreg, hcpt, hF, hgpF, hcs, htameF⟩

end Family

end Polyfold
