import Polyfold.Chapter3.IndexAlongPathsLocal
import Polyfold.Chapter5.GeneralPosition
import Polyfold.Chapter5.PartitionsOfUnity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 219–221: **Proposition 6.28** (a neighbourhood of a smooth point on which orientations can be
propagated) *(book 2017: Proposition 6.12; see `BookConcordance.md`)*.

# Neighbourhoods for the propagation of orientations

## The text, paraphrased

(Proposition 6.28) If `f` is an sc-Fredholm section of `P : Y → X`, every smooth point `x` has an
open neighbourhood `U` with: (1) `U` is sc-smoothly contractible; (2) `{y ∈ cl_X(U) | f(y) = 0}`
is compact; (3) for every sc-smooth path `φ : [0, 1] → U` there is an sc⁺-section
`s : U × [0, 1] → Y` with `s(φ(t), t) = f(φ(t))`; (4) for `t₀ ∈ [0, 1]`, `y₀ ∈ U_∞` and a smooth
`e₀ ∈ Y_{y₀}` there is an sc⁺-section `q` of `U × [0, 1] → Y` with `q(y₀, t₀) = e₀`.  *Proof*: in
coordinates `P : K → O`, `O = r(V)`, `x = 0`, assume `V` convex; then `r̂(t, y) = r(ty)` contracts
`O`; choose a convex `V' ∋ 0` with `U = r(V')` contractible and `f | cl(U)` with compact solution
set (local compactness); `s(y, t) = R(y, f(φ(t)))` and `q(y, t) = R(y, e₀)`.

## What is formalized

* `IsScHomotopyRel γ₀ γ₁ Φ`: an sc-smooth `Φ : ℝ² → X` from `γ₀` to `γ₁` fixing the end points
  (`Φ(0, t) = γ₀(t)`, `Φ(1, t) = γ₁(t)` for `t ∈ [0, 1]`, `Φ(τ, 0) = γ₀(0)`, `Φ(τ, 1) = γ₀(1)` for
  `τ ∈ [0, 1]`).
* `exists_isScPlusSection_pullback_of_family` (property (3) for families `Φ : ℝⁿ → X`, as used for
  paths and for the homotopies of Theorem 6.35): with sc-smooth bump functions, for `Φ([0,1]ⁿ)`
  in the domain of a chart there is an sc⁺-section `S` of `ℝⁿ × X → Y` with `(f + S)(q, Φ(q)) = 0`
  for `q` near `[0, 1]ⁿ`, and for `q ∈ [0, 1]ⁿ`, `S(q, ·)` depends on `q` only through `Φ(q)`.
* `hasScPlusSectionsThrough_pullback_rn_of_bump` (property (4)).
* `proposition_6_28`: every smooth `x` has open `U ⊆ W` in the domain of one chart with (1′) any
  two sc-smooth paths in `U` with the same end points are sc-smoothly homotopic in `W` with end
  points fixed, (2) the solution set in `cl(U)` is compact, (3) and (4).
* The tools: `exists_contDiff_eq_id_near_Icc_mapsTo` (a `C^∞` self-map of `ℝⁿ` equal to the
  identity near `[0, 1]ⁿ` with values in a given open neighbourhood of `[0, 1]ⁿ`),
  `exists_isScSmoothMap_eq_one_nhdsSet` (with bump functions, an sc-smooth cut-off equal to `1`
  near a compact set), `exists_isScPlusSection_pullback_of_mapsTo_of_bump` (the construction of
  `exists_isScPlusSection_pullback_of_path_of_bump` for a family with values in a chart domain,
  with its dependence on the parameter), `isScSmoothMap_rn_chart_symm` and `isScSmooth_chart_comp`
  (maps `ℝᵐ → X` in a chart), `exists_nhds_isCompact_zeros` (local compactness of the solution
  set: Theorem 5.6 at a zero, closedness of the solution set elsewhere).

## Reading

Paths are on `ℝ` and only `[0, 1]` matters (decision D2).  The text assumes sc-smooth partitions
of unity from §6.2 on (p. 203); here the sections of (3) and (4) are global sc⁺-sections of
`ℝⁿ × X → Y`, made with bump functions, in place of sections over `U × [0, 1]` after "assuming
`X = U`".  Property (1): the contraction `r̂(t, y) = r(ty)` contracts `O = r(V)` for a convex `V`,
but for `U = r(V')` it needs `r(V') ⊆ V'`, which is not stated, and a convex domain of the
retraction is not available in general; as we read it, (1) is not established for `U` itself.
What the proof of Theorem 6.35 uses is that two paths in `U` with the same end points are
sc-smoothly homotopic with fixed end points in a region where (3) holds; that is (1′), proved
with `W = O ∩ B_δ`, `U = O ∩ B_{δ'}` and `r(B_{δ'}) ⊆ B_δ` (continuity of `r` at level `0`):
`Φ(τ, t) = r((1 − ρ(τ)) φ(γ₀(t)) + ρ(τ) φ(γ₁(t)))` in the chart.  The construction does not use
that `x` is smooth (at a zero of `f` it is automatic, and Theorem 5.6 applies).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### Reparametrizations near the cube -/

/-- A `C^∞` map `ℝᵐ → ℝⁿ` is an sc-smooth map of the M-polyfolds `ℝᵐ → ℝⁿ`. -/
theorem isScSmoothMap_rn_rn_of_contDiff {m n : ℕ} {σ : (Fin m → ℝ) → Fin n → ℝ}
    (hσ : ContDiff ℝ ∞ σ) : (rnPolyfold m).IsScSmoothMap (rnPolyfold n) σ := by
  refine MPolyfold.isScSmoothMap_of_local fun x => ⟨rnChart m 0, rnChart n 0, univ,
    isChart_rnChart 0, isChart_rnChart 0, isOpen_univ, mem_univ x, subset_univ _,
    mapsTo_univ _ _, ?_⟩
  have himg : rnChart m 0 '' univ = univ :=
    eq_univ_of_forall fun (r : Fin m → ℝ) => ⟨r, mem_univ _, show r - 0 = r from sub_zero r⟩
  rw [himg, rnChart_model_O]
  change IsScSmoothRetractMap (rnSc m) univ univ (rnSc n) univ univ (fun r => σ (r + 0) - 0)
  exact isScSmoothRetractMap_const_of_contDiff (V := Fin m → ℝ) (V' := Fin n → ℝ)
    ((hσ.comp (contDiff_id.add contDiff_const)).sub contDiff_const)

/-- A smooth clamp: for `δ > 0` a `C^∞` map `h : ℝ → [−2δ, 1 + 2δ]` equal to the identity on
`[−δ, 1 + δ]`. -/
lemma exists_contDiff_clamp {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ (∀ s ∈ Icc (-δ) (1 + δ), h s = s) ∧
      ∀ s, h s ∈ Icc (-2 * δ) (1 + 2 * δ) := by
  set u : ℝ → ℝ := fun x => x * Real.smoothTransition x with hudef
  have hu : ContDiff ℝ ∞ u := contDiff_id.mul Real.smoothTransition.contDiff
  have hu1 : ∀ x, 1 ≤ x → u x = x := fun x hx => by
    simp [hudef, Real.smoothTransition.one_of_one_le hx]
  have hu0 : ∀ x, 0 ≤ u x := fun x => by
    rcases le_or_gt x 0 with hx | hx
    · simp [hudef, Real.smoothTransition.zero_of_nonpos hx]
    · exact mul_nonneg hx.le (Real.smoothTransition.nonneg x)
  have hult : ∀ x, x < 1 → u x < 1 := fun x hx => by
    rcases le_or_gt x 0 with hx0 | hx0
    · simp [hudef, Real.smoothTransition.zero_of_nonpos hx0]
    · calc u x ≤ x * 1 := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one x) hx0.le
        _ < 1 := by linarith
  set g₁ : ℝ → ℝ := fun s => -2 * δ + δ * u ((s + 2 * δ) / δ) with hg₁
  set g₂ : ℝ → ℝ := fun s => 1 + 2 * δ - δ * u ((1 + 2 * δ - s) / δ) with hg₂
  have hg₁s : ∀ s, -δ ≤ s → g₁ s = s := fun s hs => by
    simp only [hg₁]
    rw [hu1 _ (by rw [le_div_iff₀ hδ]; linarith)]
    field_simp
    ring
  have hg₂s : ∀ s, s ≤ 1 + δ → g₂ s = s := fun s hs => by
    simp only [hg₂]
    rw [hu1 _ (by rw [le_div_iff₀ hδ]; linarith)]
    field_simp
    ring
  refine ⟨g₂ ∘ g₁, ?_, fun s hs => ?_, fun s => ?_⟩
  · exact (contDiff_const.sub (contDiff_const.mul (hu.comp
      ((contDiff_const.sub contDiff_id).div_const δ)))).comp
      (contDiff_const.add (contDiff_const.mul (hu.comp
        ((contDiff_id.add contDiff_const).div_const δ))))
  · simp only [Function.comp_apply, hg₁s s hs.1, hg₂s s hs.2]
  · have h1 : -2 * δ ≤ g₁ s := by
      have := mul_nonneg hδ.le (hu0 ((s + 2 * δ) / δ))
      simp only [hg₁]; linarith
    have h2 : ∀ t, g₂ t ≤ 1 + 2 * δ := fun t => by
      have := mul_nonneg hδ.le (hu0 ((1 + 2 * δ - t) / δ))
      simp only [hg₂]; linarith
    refine ⟨?_, h2 _⟩
    simp only [Function.comp_apply]
    by_cases ht : g₁ s ≤ 1 + δ
    · rw [hg₂s _ ht]; exact h1
    · rw [not_le] at ht
      have hlt : (1 + 2 * δ - g₁ s) / δ < 1 := by rw [div_lt_one hδ]; linarith
      have := hult _ hlt
      have h3 : δ * u ((1 + 2 * δ - g₁ s) / δ) < δ * 1 := mul_lt_mul_of_pos_left this hδ
      change -2 * δ ≤ 1 + 2 * δ - δ * u ((1 + 2 * δ - g₁ s) / δ)
      linarith

/-- **A smooth reparametrization near the cube**: for an open `A ⊆ ℝⁿ` containing `[0, 1]ⁿ` there
is a `C^∞` map `σ : ℝⁿ → A` equal to the identity near `[0, 1]ⁿ` (coordinatewise a smooth clamp
onto an interval slightly larger than `[0, 1]`). -/
theorem exists_contDiff_eq_id_near_Icc_mapsTo {n : ℕ} {A : Set (Fin n → ℝ)} (hA : IsOpen A)
    (hIA : Icc (0 : Fin n → ℝ) 1 ⊆ A) :
    ∃ σ : (Fin n → ℝ) → Fin n → ℝ, ContDiff ℝ ∞ σ ∧
      (∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), σ q = q) ∧ ∀ q, σ q ∈ A := by
  obtain ⟨ε, hε, hεA⟩ := isCompact_Icc.exists_thickening_subset_open hA hIA
  obtain ⟨h, hh, hhid, hhr⟩ := exists_contDiff_clamp (δ := ε / 4) (by positivity)
  refine ⟨fun q i => h (q i), contDiff_pi.2 fun i => hh.comp (contDiff_apply ℝ ℝ i), ?_,
    fun q => hεA ?_⟩
  · have hO : IsOpen (Set.pi univ fun _ : Fin n => Ioo (-(ε / 4)) (1 + ε / 4)) :=
      isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
    have hsub : Icc (0 : Fin n → ℝ) 1 ⊆ Set.pi univ fun _ => Ioo (-(ε / 4)) (1 + ε / 4) :=
      fun q hq i _ => by
        have h0 : (0 : ℝ) ≤ q i := hq.1 i
        have h1 : q i ≤ 1 := hq.2 i
        exact ⟨by linarith, by linarith⟩
    filter_upwards [hO.mem_nhdsSet.2 hsub] with q hq
    funext i
    exact hhid _ (Ioo_subset_Icc_self (hq i (mem_univ _)))
  · rw [Metric.mem_thickening_iff]
    refine ⟨fun i => max 0 (min 1 (h (q i))), ⟨fun i => le_max_left _ _,
      fun i => max_le zero_le_one (min_le_left _ _)⟩, ?_⟩
    rw [dist_pi_lt_iff hε]
    intro i
    have := hhr (q i)
    rw [Real.dist_eq, abs_lt]
    rcases max_cases (0 : ℝ) (min 1 (h (q i))) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases min_cases (1 : ℝ) (h (q i)) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      constructor <;> linarith [this.1, this.2]

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### Cut-offs, maps read in charts, local compactness -/

/-- **A cut-off equal to `1` near a compact set**: with sc-smooth bump functions, for a compact
`K` in an open `V` there is an sc-smooth `β : X → ℝ` with `supp β ⊆ V` and `β = 1` near `K`
(`β = 1 − ∏ᵢ (1 − βᵢ)` for finitely many bumps `βᵢ` of Proposition 5.30). -/
theorem exists_isScSmoothMap_eq_one_nhdsSet (hbump : PX.AdmitsBumpFunctions) {K V : Set X}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ β : X → ℝ, PX.IsScSmoothMap realPolyfold β ∧ tsupport β ⊆ V ∧
      ∀ᶠ y in 𝓝ˢ K, β y = 1 := by
  classical
  have h : ∀ x, ∃ b : X → ℝ, PX.IsScSmoothMap realPolyfold b ∧ tsupport b ⊆ V ∧
      (x ∈ K → ∀ᶠ y in 𝓝 x, b y = 1) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨b, hb, -, -, hbs, hb1⟩ := proposition_5_30 hbump hV (hKV hx)
      exact ⟨b, hb, hbs, fun _ => hb1⟩
    · refine ⟨fun _ => 0, isScSmoothMap_real_const 0, ?_, fun h => absurd h hx⟩
      rw [show (fun _ : X => (0 : ℝ)) = 0 from rfl, tsupport_zero]
      exact empty_subset _
  choose b hb hbs hb1 using h
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover (fun x => interior {y | b x y = 1})
    fun x hx => interior_mem_nhds.2 (hb1 x hx)
  refine ⟨fun y => 1 - ∏ x ∈ t, (1 - b x y), ?_, ?_, ?_⟩
  · exact (isScSmoothMap_real_const 1).real_sub
      (isScSmoothMap_real_finsetProd t fun x _ => (isScSmoothMap_real_const 1).real_sub (hb x))
  · refine (closure_minimal (fun y hy => ?_)
      (isClosed_biUnion_finset (s := t) fun x _ => isClosed_tsupport (b x))).trans
      (iUnion₂_subset fun x _ => hbs x)
    by_contra hne
    simp only [mem_iUnion, not_exists] at hne
    apply hy
    have h0 : ∀ x ∈ t, b x y = 0 := fun x hx => image_eq_zero_of_notMem_tsupport (hne x hx)
    simp only
    rw [Finset.prod_eq_one fun x hx => by rw [h0 x hx, sub_zero], sub_self]
  · rw [eventually_nhdsSet_iff_forall]
    intro x hx
    obtain ⟨x', hx't, hxx'⟩ := mem_iUnion₂.1 (hKt hx)
    filter_upwards [mem_interior_iff_mem_nhds.1 hxx'] with y hy
    rw [Finset.prod_eq_zero hx't (by rw [show b x' y = 1 from hy, sub_self]), sub_zero]

/-- **An sc-smooth map `ℝᵐ → X` given in a chart**: for a chart `φ` of `X` and an sc-smooth
`G : ℝᵐ → E` with values in the model `O` of `φ`, `φ⁻¹ ∘ G` is sc-smooth. -/
theorem isScSmoothMap_rn_chart_symm {m : ℕ} {φ : MChart X} (hφ : PX.IsChart φ)
    {G : (Fin m → ℝ) → φ.model.E 0} (hG : IsScSmooth (E := rnSc m) (F := φ.model.E) univ G)
    (hGO : ∀ a, G a ∈ φ.model.O) : (rnPolyfold m).IsScSmoothMap PX fun a => φ.symm (G a) := by
  refine MPolyfold.isScSmoothMap_of_local fun a => ⟨rnChart m 0, φ, univ, isChart_rnChart 0, hφ,
    isOpen_univ, mem_univ a, subset_univ _, fun b _ => φ.symm_mapsTo (hGO b), ?_⟩
  have himg : rnChart m 0 '' univ = univ :=
    eq_univ_of_forall fun (r : Fin m → ℝ) => ⟨r, mem_univ _, show r - 0 = r from sub_zero r⟩
  rw [himg]
  refine (isScSmoothRetractMap_iff_exists (rn_relOpen_univ m).isScRetract).2
    ⟨fun b _ => ?_, ScRetraction.id (rn_relOpen_univ m), image_id _, ?_⟩
  · change φ (φ.symm (G (b + 0))) ∈ φ.model.O
    rw [φ.apply_symm_apply (hGO _)]
    exact hGO _
  · refine hG.congr (isScDomain_univ _) fun b _ => ?_
    change G b = φ (φ.symm (G (b + 0)))
    rw [add_zero, φ.apply_symm_apply (hGO _)]

/-- **An sc-smooth map `ℝᵐ → X` read in a chart**: if `Γ` is sc-smooth with values in the domain
of a chart `φ`, then `φ ∘ Γ : ℝᵐ → E` is sc-smooth. -/
theorem isScSmooth_chart_comp {m : ℕ} {Γ : (Fin m → ℝ) → X}
    (hΓ : (rnPolyfold m).IsScSmoothMap PX Γ) {φ : MChart X} (hφ : PX.IsChart φ)
    (hΓφ : ∀ a, Γ a ∈ φ.source) :
    IsScSmooth (E := rnSc m) (F := φ.model.E) univ fun a => φ (Γ a) := by
  have h1 := hΓ.smooth (rnChart m 0) φ (isChart_rnChart 0) hφ univ isOpen_univ
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩) (fun t _ => hΓφ t)
  rw [← rnChart_source 0, (rnChart m 0).image_source, rnChart_model_O] at h1
  have hg : IsScSmooth (E := rnSc m) (F := φ.model.E) univ fun a => φ (Γ (a + 0)) :=
    h1.comp_isScSmooth (ScRetraction.id (rn_relOpen_univ m)) (image_id _)
  exact hg.congr (isScDomain_univ _) fun a _ => by simp only [add_zero]

/-- **Local compactness of the solution set** (Theorem 5.6 at a zero, closedness of the solution
set elsewhere): every point `x` has a neighbourhood `N` such that `{y ∈ A | f(y) = 0}` is compact
for every closed `A ⊆ N`. -/
theorem exists_nhds_isCompact_zeros (hf : B.IsScFredholmSection f) (x : X) :
    ∃ N ∈ 𝓝 x, ∀ A : Set X, IsClosed A → A ⊆ N → IsCompact {y ∈ A | IsZeroAt P f y} := by
  have hZ : IsClosed (solutionSet P f) := isClosed_solutionSet hf.isScSmooth
  by_cases hx : IsZeroAt P f x
  · obtain ⟨O, hO, hxO, -, hK⟩ := theorem_5_6 hf hx
    obtain ⟨K, hK, hKeq⟩ := hK 0
    have hc : IsCompact (closure {y ∈ O 0 | IsZeroAt P f y}) :=
      hKeq ▸ hK.image (PX.continuous_levelVal 0)
    refine ⟨O 0, (hO 0).mem_nhds (hxO 0), fun A hA hAN => hc.of_isClosed_subset (hA.inter hZ) ?_⟩
    rintro y ⟨hyA, hy0⟩
    exact subset_closure ⟨hAN hyA, hy0⟩
  · refine ⟨(solutionSet P f)ᶜ, hZ.isOpen_compl.mem_nhds hx, fun A _ hAN => ?_⟩
    convert isCompact_empty
    refine eq_empty_of_forall_notMem fun y hy => hAN hy.1 hy.2

/-! ### Paths and homotopies with fixed end points -/

/-- The point `t` of `ℝ¹ = Fin 1 → ℝ`. -/
def pt1 (t : ℝ) : Fin 1 → ℝ := fun _ => t

/-- The point `(τ, t)` of `ℝ² = Fin 2 → ℝ`. -/
def pt2 (τ t : ℝ) : Fin 2 → ℝ := ![τ, t]

variable (PX) in
/-- **An sc-smooth homotopy from `γ₀` to `γ₁` with end points fixed** (for parameters in
`[0, 1]`): `Φ : ℝ² → X` sc-smooth with `Φ(0, t) = γ₀(t)` and `Φ(1, t) = γ₁(t)` for `t ∈ [0, 1]`,
and `Φ(τ, 0) = γ₀(0)`, `Φ(τ, 1) = γ₀(1)` for `τ ∈ [0, 1]`. -/
structure IsScHomotopyRel (γ₀ γ₁ : (Fin 1 → ℝ) → X) (Φ : (Fin 2 → ℝ) → X) : Prop where
  isScSmoothMap : (rnPolyfold 2).IsScSmoothMap PX Φ
  zero : ∀ t ∈ Icc (0 : ℝ) 1, Φ (pt2 0 t) = γ₀ (pt1 t)
  one : ∀ t ∈ Icc (0 : ℝ) 1, Φ (pt2 1 t) = γ₁ (pt1 t)
  start : ∀ τ ∈ Icc (0 : ℝ) 1, Φ (pt2 τ 0) = γ₀ (pt1 0)
  finish : ∀ τ ∈ Icc (0 : ℝ) 1, Φ (pt2 τ 1) = γ₀ (pt1 1)

/-! ### Properties (3) and (4): sections along families -/

section Sections

variable {n : ℕ} [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **The text's sc⁺-section along a family, with the chart and the cut-off as data**
(`exists_isScPlusSection_pullback_of_path_of_bump` for a family `ψ : ℝⁿ → dom φ_c`, keeping
track of the dependence on the parameter): for an sc-smooth section `f`, an sc-smooth
`ψ : ℝⁿ → X` with values in the domain of a chart `c` of the atlas and an sc-smooth `β₂`
supported in `dom φ_c`, the section `S = cutoffSection pc β τ`, `τ(a, u) = −R[1](u, ê₁(a + t₀))₂`
with `ê₁(a)` the lift of `Φ(f(ψ(a)))₂` to `F¹`, is an sc⁺-section of `π*P` with `f̃ + S = 0` at
`(t, ψ(t))` where `β₂(ψ(t)) = 1`, and `S(t, ·)` depends on `t` only through `ψ(t)`. -/
theorem exists_isScPlusSection_pullback_of_mapsTo_of_bump
    (hf : B.IsScSmoothSection f) {ψ : (Fin n → ℝ) → X}
    (hψ : (rnPolyfold n).IsScSmoothMap PX ψ) (t₀ : Fin n → ℝ) {c : StrongBundleChart PX P}
    (hc : c ∈ B.atlas.charts) (hψc : ∀ t, ψ t ∈ c.φ.source) {β₂ : X → ℝ}
    (hβ₂ : PX.IsScSmoothMap realPolyfold β₂) (hβ₂s : tsupport β₂ ⊆ c.φ.source) :
    ∃ S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X),
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S ∧
      (∀ t, β₂ (ψ t) = 1 → IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.1) S) (t, ψ t)) ∧
      ∀ t t', ψ t = ψ t' → ∀ y, (S (t, y)).1.2 = (S (t', y)).1.2 := by
  classical
  have hfs : IsSection P f := hf.1
  -- the curve `g(a) = Φ(f(ψ(a)))` is sc-smooth into `E ⊕ F`, hence into `E¹ ⊕ F¹`
  have hfψ : (rnPolyfold n).IsScSmoothMap B.toMPolyfold0 (f ∘ ψ) := hf.2.comp hψ
  have h1 := hfψ.smooth (rnChart n 0) (c.toMChart B.continuous) (isChart_rnChart 0)
    (B.isChart_toMChart hc) univ isOpen_univ (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
    (fun t _ => c.mem_source_of_proj (by rw [Function.comp_apply, hfs]; exact hψc t))
  rw [← rnChart_source 0, (rnChart n 0).image_source, rnChart_model_O] at h1
  set g : (Fin n → ℝ) → (c.φ.model.E.prod c.F) 0 := fun a => c (f (ψ (a + 0))) with hgdef
  have hg : IsScSmooth (E := rnSc n) (F := c.φ.model.E.prod c.F) univ g :=
    h1.comp_isScSmooth (ScRetraction.id (rn_relOpen_univ n)) (image_id _)
  have hg1 := hg.shift (isScDomain_univ _)
  have hlv : (rnSc n).lvlSet (univ : Set ((rnSc n) 0)) 1 = univ := by
    ext a; exact ⟨fun _ => mem_univ _, fun _ => mem_univ _⟩
  rw [hlv] at hg1
  have hg1' : IsScSmooth (E := rnSc n) (F := c.φ.model.E.shift.prod c.F.shift) univ
      (fun a => levelMap (E := rnSc n) (F := c.φ.model.E.prod c.F) g 1 a) := hg1
  set ê₁ : (Fin n → ℝ) → c.F 1 :=
    fun a => (levelMap (E := rnSc n) (F := c.φ.model.E.prod c.F) g 1 a).2 with hê₁def
  have hê₁ : IsScSmooth (E := rnSc n) (F := c.F.shift) univ ê₁ := hg1'.snd (isScDomain_univ _)
  have hê₁base : ∀ a, c.F.toBase 1 (ê₁ a) = (c (f (ψ a))).2 := fun a => by
    have h := IsSc0.toBase_levelMap (hg 0) (m := 1) (x := a)
      (by rw [ScBanach.mem_lvlSet]; exact mem_univ _)
    rw [ScBanach.prod_toBase, ScBanach.const_toBase] at h
    have h2 := congrArg Prod.snd h
    exact h2.trans (by simp only [hgdef, add_zero])
  -- the product chart at `t₀` over `c`
  set d := PullbackChartData.ofProd c t₀ with hd
  set q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X) := paramLift f hfs (t₀, ψ t₀)
    with hq₀
  set pc := d.toChart q₀ with hpc
  have hpcmem : pc ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).atlas.charts :=
    ⟨d, q₀, hc, rfl⟩
  -- the local section `τ(a, u) = −R[1](u, ê₁(a + t₀))₂`
  set τ : ((rnSc n).prod c.φ.model.E) 0 → c.F 1 :=
    fun z => -(shiftFiber c.R (z.2, ê₁ (z.1 + t₀))).2 with hτdef
  have hRfib : ∀ u ∈ c.U, ∀ b, (c.R (u, c.F.toBase 1 (ê₁ b))).2 ∈ range (c.F.toBase 1) :=
    fun u hu b => (c.isRetraction.preserves_filtration 0 1 (by norm_num) u hu ⟨u, rfl⟩ _
      ⟨ê₁ b, rfl⟩).2
  have hτbase : ∀ z : ((rnSc n).prod c.φ.model.E) 0, z.2 ∈ c.U →
      c.F.toBase 1 (τ z) = -(c.R (z.2, c.F.toBase 1 (ê₁ (z.1 + t₀)))).2 := fun z hz => by
    simp only [hτdef, map_neg, shiftFiber]
    rw [Function.invFun_eq (hRfib z.2 hz _)]
  -- `(z, τ(z)) ∈ K[1]` for `z ∈ ℝⁿ × O`
  have hτK : ∀ z : ((rnSc n).prod c.φ.model.E) 0, z ∈ univ ×ˢ c.φ.model.O →
      (z, c.F.toBase 1 (τ z)) ∈ pc.K := fun z hz => by
    have hz2 : z.2 ∈ c.φ.model.O := hz.2
    have hzU : z.2 ∈ c.U := StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ hz2)
    change _ ∈ pullbackRetraction d.c.R d.RZ d.g '' (d.RZ.U ×ˢ univ)
    rw [d.image_eq_Kg]
    refine ⟨by rw [d.RZ_retract]; exact hz, ?_⟩
    have hgz : d.g z = z.2 := by
      change c.φ (c.φ.symm z.2) = z.2
      exact c.φ.apply_symm_apply hz2
    rw [hgz, hτbase z hzU]
    set h := c.F.toBase 1 (ê₁ (z.1 + t₀)) with hh
    have hR : c.R (z.2, h) ∈ c.K := ⟨_, ⟨hzU, mem_univ _⟩, rfl⟩
    have hr : (c.R (z.2, h)).1 = z.2 :=
      (c.isRetraction.fst_independent z.2 hzU h 0).trans
        (StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ hz2))
    have hmem : (z.2, (c.R (z.2, h)).2) ∈ c.K := by
      have : (z.2, (c.R (z.2, h)).2) = c.R (z.2, h) := Prod.ext hr.symm rfl
      rw [this]; exact hR
    have := c.smul_mem_K hmem (-1)
    rwa [neg_one_smul] at this
  have hτ : IsScSmoothRetractMap pc.φ.model.E pc.φ.model.C pc.φ.model.O
      (pc.φ.model.E.prod pc.F.shift) (pc.φ.model.C ×ˢ univ) (strongShiftOne pc.K)
      (fun z => (z, τ z)) := by
    refine ⟨fun z hz => hτK z hz, fun R hR => ?_⟩
    · have hU := R.isScDomain
      set R' : pc.φ.model.E 0 → ((rnSc n).prod c.φ.model.E) 0 := fun w => R w with hR'def
      have hRO : ∀ w ∈ R.U, R' w ∈ univ ×ˢ c.φ.model.O := fun w hw => by
        change R w ∈ pc.φ.model.O
        rw [← hR]; exact R.apply_mem_retract hw
      have hRsm : IsScSmooth (E := pc.φ.model.E) (F := (rnSc n).prod c.φ.model.E) R.U R' :=
        R.isScSmooth
      have hadd : IsScSmooth (E := pc.φ.model.E) (F := rnSc n) R.U
          (fun w => (R' w).1 + t₀) :=
        (hRsm.fst hU).add hU (isScSmooth_const_of_mem_smooth hU
          ((rnSc n).mem_smooth_iff.2 fun m => ⟨t₀, ScBanach.const_toBase _ m _⟩))
      have hpair : IsScSmooth (E := pc.φ.model.E) (F := c.φ.model.E.prod c.F.shift) R.U
          (fun w => ((R' w).2, ê₁ ((R' w).1 + t₀))) :=
        IsScSmooth.scPair hU (hRsm.snd hU)
          (IsScSmooth.comp hU (isScDomain_univ _) hê₁ hadd (mapsTo_univ _ _))
      have hmaps : MapsTo (fun w => ((R' w).2, ê₁ ((R' w).1 + t₀))) R.U (c.U ×ˢ univ) :=
        fun w hw => ⟨StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ (hRO w hw).2),
          mem_univ _⟩
      have hsf := IsScSmooth.comp hU (c.relOpen.prod_univ c.F.shift).isScDomain
        c.isRetraction.isScSmooth_one hpair hmaps
      have hτR : IsScSmooth (E := pc.φ.model.E) (F := c.F.shift) R.U (τ ∘ R) :=
        ((hsf.snd hU).neg hU).congr hU fun _ _ => rfl
      exact (R.isScSmooth.scPair hU hτR).congr hU fun _ _ => rfl
  -- the bump `β(t, x) = β₂(x)`
  set β : (Fin n → ℝ) × X → ℝ := fun p => β₂ p.2 with hβdef
  have hβ : ((rnPolyfold n).prod PX).IsScSmoothMap realPolyfold β :=
    hβ₂.comp (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)
  have hβs : tsupport β ⊆ pc.φ.source := by
    have : tsupport β ⊆ Prod.snd ⁻¹' tsupport β₂ :=
      closure_minimal (fun p hp => subset_closure (show β₂ p.2 ≠ 0 from hp))
        (isClosed_closure.preimage continuous_snd)
    exact fun p hp => ⟨mem_univ _, hβ₂s (this hp)⟩
  set S := StrongBundle.cutoffSection pc β τ with hSdef
  have hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S :=
    StrongBundle.isScPlusSection_cutoffSection hpcmem hβ hβs hτ
  refine ⟨S, hS, ?_, ?_⟩
  · intro t hβt
    have hGs : IsSection (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := n) f hfs) S) :=
      (isSection_pullbackLift _).sectionAdd hS.1
    have hxt : ψ t ∈ c.φ.source := hψc t
    rw [isZeroAt_pullback_iff_pullbackSlice hGs t (ψ t),
      pullbackSlice_sectionAdd_paramLift hfs hS.1 t]
    have hsl : IsSection P (Polyfold.pullbackSlice S t) := hS.1.pullbackSlice t
    refine (c.isZeroAt_iff (hfs.sectionAdd hsl) hxt).2 ?_
    change (c (sectionAdd P f (Polyfold.pullbackSlice S t) (c.φ.symm (c.φ (ψ t))))).2 = 0
    rw [c.φ.symm_apply_apply hxt, sectionAdd_apply hfs hsl, c.snd_add hxt]
    -- the fibre component of the slice at `ψ(t)`
    have hty : (t, ψ t) ∈ pc.φ.source := ⟨mem_univ _, hxt⟩
    have hSval : (c (Polyfold.pullbackSlice S t (ψ t))).2 =
        c.F.toBase 1 (β (t, ψ t) • τ (pc.φ (t, ψ t))) :=
      congrArg Prod.snd (StrongBundle.apply_cutoffSection hτ.mapsTo hty)
    change (c (f (ψ t))).2 + (c (Polyfold.pullbackSlice S t (ψ t))).2 = 0
    rw [hSval, show β (t, ψ t) = 1 from hβt, one_smul]
    have hpcφ : pc.φ (t, ψ t) = (t - t₀, c.φ (ψ t)) := rfl
    rw [hpcφ, hτbase _ (StrongRetr.mem_U_of_mem_O c.isRetraction
      (c.r_image ▸ c.φ.mapsTo_model _ hxt))]
    change (c (f (ψ t))).2 + -(c.R (c.φ (ψ t), c.F.toBase 1 (ê₁ (t - t₀ + t₀)))).2 = 0
    rw [sub_add_cancel, hê₁base t]
    have hK : (c.φ (ψ t), (c (f (ψ t))).2) ∈ c.R '' (c.U ×ˢ univ) := by
      have h := c.toPartialEquiv.map_source (c.mem_source_of_proj (by rw [hfs]; exact hxt))
      rw [c.target_eq] at h
      have e : c (f (ψ t)) = (c.φ (ψ t), (c (f (ψ t))).2) :=
        Prod.ext (by rw [c.fst_apply (by rw [hfs]; exact hxt), hfs]) rfl
      exact e ▸ h
    have hρ := StrongRetr.ρ_eq_self_of_mem_K c.isRetraction
      (StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ c.φ.mapsTo_model _ hxt)) hK
    change (c.R (c.φ (ψ t), (c (f (ψ t))).2)).2 = (c (f (ψ t))).2 at hρ
    rw [hρ]
    exact add_neg_cancel _
  · -- the dependence on the parameter: through `ê₁(t)`, i.e. through `ψ(t)`
    intro t t' htt' y
    by_cases hy : y ∈ c.φ.source
    · have hval : ∀ s, c (S (s, y)).1.2 = (c.φ y, c.F.toBase 1 (β₂ y • τ (s - t₀, c.φ y))) := by
        intro s
        have hsy : (s, y) ∈ pc.φ.source := ⟨mem_univ _, hy⟩
        have h := StrongBundle.apply_cutoffSection (β := β) hτ.mapsTo hsy
        have hP : P (S (s, y)).1.2 = y := by
          rw [(S (s, y)).2]
          exact congrArg Prod.snd (hS.1 (s, y))
        have h2 : (c (S (s, y)).1.2).2 = c.F.toBase 1 (β (s, y) • τ (pc.φ (s, y))) :=
          congrArg Prod.snd h
        refine Prod.ext ?_ h2
        rw [c.fst_apply (by rw [hP]; exact hy), hP]
      have hê : ê₁ t = ê₁ t' := c.F.toBase_injective 1 (by rw [hê₁base, hê₁base, htt'])
      have hPs : ∀ s, P (S (s, y)).1.2 ∈ c.φ.source := fun s => by
        rw [(S (s, y)).2]
        rw [show (S (s, y)).1.1 = (s, y) from hS.1 (s, y)]
        exact hy
      refine c.toPartialEquiv.injOn (c.mem_source_of_proj (hPs t)) (c.mem_source_of_proj (hPs t'))
        ?_
      change c (S (t, y)).1.2 = c (S (t', y)).1.2
      rw [hval t, hval t']
      simp only [hτdef, sub_add_cancel, hê]
    · have hty : ∀ s, (s, y) ∉ pc.φ.source := fun s h => hy h.2
      simp only [hSdef, StrongBundle.cutoffSection, if_neg (hty t), if_neg (hty t')]
      rfl

/-- **Property (3) for families**: with sc-smooth bump functions, if `Φ : ℝⁿ → X` is sc-smooth
with `Φ([0, 1]ⁿ)` in the domain of a chart `c`, there is an sc⁺-section `S` of `ℝⁿ × X → Y`
with `(f + S)(q, Φ(q)) = 0` for `q` near `[0, 1]ⁿ` (the text's `s(y, t) = R(y, f(φ(t)))` with the
sign of `sectionAdd`, times a cut-off), and for `q ∈ [0, 1]ⁿ`, `S(q, ·)` depends on `q` only
through `Φ(q)`. -/
theorem exists_isScPlusSection_pullback_of_family (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScSmoothSection f) {Φ : (Fin n → ℝ) → X} (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ)
    {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts)
    (hΦc : ∀ q ∈ Icc (0 : Fin n → ℝ) 1, Φ q ∈ c.φ.source) :
    ∃ S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X),
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S ∧
      (∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.1) S) (q, Φ q)) ∧
      ∀ q ∈ Icc (0 : Fin n → ℝ) 1, ∀ q' ∈ Icc (0 : Fin n → ℝ) 1, Φ q = Φ q' →
        ∀ y, (S (q, y)).1.2 = (S (q', y)).1.2 := by
  have hΦcont : Continuous Φ := continuousOn_univ.1 hΦ.continuousOn
  obtain ⟨σ, hσ, hσid, hσA⟩ := exists_contDiff_eq_id_near_Icc_mapsTo
    (c.φ.isOpen_source.preimage hΦcont) hΦc
  obtain ⟨β₂, hβ₂, hβ₂s, hβ₂1⟩ := exists_isScSmoothMap_eq_one_nhdsSet hbump
    (isCompact_Icc.image hΦcont) c.φ.isOpen_source (image_subset_iff.2 hΦc)
  set ψ : (Fin n → ℝ) → X := Φ ∘ σ with hψdef
  have hψ : (rnPolyfold n).IsScSmoothMap PX ψ := hΦ.comp (isScSmoothMap_rn_of_contDiff hσ)
  obtain ⟨S, hS, hz, hdep⟩ := exists_isScPlusSection_pullback_of_mapsTo_of_bump hf hψ 0 hc
    (fun t => hσA t) hβ₂ hβ₂s
  have hσI : ∀ q ∈ Icc (0 : Fin n → ℝ) 1, σ q = q := fun q hq => hσid.self_of_nhdsSet q hq
  refine ⟨S, hS, ?_, fun q hq q' hq' hqq' y => hdep q q' ?_ y⟩
  · obtain ⟨N, hNo, hKN, hN1⟩ := mem_nhdsSet_iff_exists.1 hβ₂1
    have hev : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), Φ q ∈ N :=
      (hNo.preimage hΦcont).mem_nhdsSet.2 fun q hq => hKN (mem_image_of_mem Φ hq)
    filter_upwards [hσid, hev] with q hσq hNq
    have hψq : ψ q = Φ q := by simp only [hψdef, Function.comp_apply, hσq]
    have := hz q (by rw [hψq]; exact hN1 hNq)
    rwa [hψq] at this
  · simp only [hψdef, Function.comp_apply, hσI q hq, hσI q' hq', hqq']

/-- **Property (4)**: with sc-smooth bump functions, `ℝⁿ × X → Y` has sc⁺-sections through every
smooth point of a fibre over a smooth point. -/
theorem hasScPlusSectionsThrough_pullback_rn_of_bump (hbump : PX.AdmitsBumpFunctions) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).HasScPlusSectionsThrough :=
  MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough
    (MPolyfold.admitsBumpFunctions_prod_rn hbump)

end Sections

/-! ### Proposition 6.28 -/

-- `x ∈ X_∞` is the text's hypothesis; the construction does not use it
set_option linter.unusedVariables false in
/-- **Proposition 6.28** (with sc-smooth bump functions, the text's standing assumption from
§6.2 on): every smooth point `x` has open neighbourhoods `U ⊆ W` in the domain of one chart `c`
of the atlas with (1′) any two sc-smooth paths in `U` with the same end points are sc-smoothly
homotopic in `W` with end points fixed; (2) `{y ∈ cl(U) | f(y) = 0}` is compact; (3) along every
sc-smooth family `Φ : ℝⁿ → X` with `Φ([0, 1]ⁿ) ⊆ W` there is an sc⁺-section `S` with
`(f + S)(q, Φ(q)) = 0` near `[0, 1]ⁿ`, depending on `q ∈ [0, 1]ⁿ` only through `Φ(q)`;
(4) `ℝⁿ × X → Y` has sc⁺-sections through all smooth fibre points. -/
theorem proposition_6_28 (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSection f) {x : X}
    (hx : x ∈ PX.smoothSet) :
    ∃ (U W : Set X) (c : StrongBundleChart PX P), IsOpen U ∧ IsOpen W ∧ x ∈ U ∧ U ⊆ W ∧
      c ∈ B.atlas.charts ∧ W ⊆ c.φ.source ∧
      (∀ γ₀ γ₁ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ₀ →
        (rnPolyfold 1).IsScSmoothMap PX γ₁ → (∀ t ∈ Icc (0 : ℝ) 1, γ₀ (pt1 t) ∈ U) →
        (∀ t ∈ Icc (0 : ℝ) 1, γ₁ (pt1 t) ∈ U) → γ₀ (pt1 0) = γ₁ (pt1 0) →
        γ₀ (pt1 1) = γ₁ (pt1 1) →
        ∃ Φ, IsScHomotopyRel PX γ₀ γ₁ Φ ∧ ∀ τ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          Φ (pt2 τ t) ∈ W) ∧
      IsCompact {y ∈ closure U | IsZeroAt P f y} ∧
      (∀ (n : ℕ) [ParacompactSpace ((Fin n → ℝ) × X)]
        [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
        (Φ : (Fin n → ℝ) → X), (rnPolyfold n).IsScSmoothMap PX Φ →
        (∀ q ∈ Icc (0 : Fin n → ℝ) 1, Φ q ∈ W) →
        ∃ S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X),
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S ∧
          (∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
            (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q)) ∧
          ∀ q ∈ Icc (0 : Fin n → ℝ) 1, ∀ q' ∈ Icc (0 : Fin n → ℝ) 1, Φ q = Φ q' →
            ∀ y, (S (q, y)).1.2 = (S (q', y)).1.2) ∧
      ∀ (n : ℕ) [ParacompactSpace ((Fin n → ℝ) × X)]
        [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))],
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).HasScPlusSectionsThrough := by
  classical
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B x
  set u₀ := c.φ x with hu₀
  set r := StrongRetr.r c.R with hr
  have hu₀O : u₀ ∈ c.φ.model.O := c.φ.mapsTo_model x hxc
  have hOU : ∀ {u}, u ∈ c.φ.model.O → u ∈ c.U := fun hu =>
    StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ hu)
  have hrO : ∀ {u}, u ∈ c.U → r u ∈ c.φ.model.O := fun hu => c.r_mem_O hu
  have hrfix : ∀ {u}, u ∈ c.φ.model.O → r u = u := fun hu =>
    StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ hu)
  have hCconv : Convex ℝ c.φ.model.C := c.relOpen.isPartialQuadrant.convex
  obtain ⟨O', hO'o, hO'⟩ := c.relOpen.relOpen
  have hUC : c.U ⊆ c.φ.model.C := by rw [hO']; exact inter_subset_right
  -- `B_δ ∩ C ⊆ U` (the domain of the retraction)
  obtain ⟨δ, hδ, hδO'⟩ := Metric.isOpen_iff.1 hO'o u₀ (by
    have := hOU hu₀O
    rw [hO'] at this
    exact this.1)
  have hballU : ∀ {u}, u ∈ Metric.ball u₀ δ → u ∈ c.φ.model.C → u ∈ c.U := fun h1 h2 => by
    rw [hO']; exact ⟨hδO' h1, h2⟩
  -- `r(B_{δ₂} ∩ U) ⊆ B_δ` (continuity of `r` at level `0`)
  have hrcont : ContinuousOn r c.U :=
    (c.isRetraction.baseRetraction c.relOpen).isScSmooth.isSc1.isSc0.continuousOn_base
  obtain ⟨δ₂, hδ₂, hδ₂r⟩ := Metric.mem_nhdsWithin_iff.1
    ((hrcont u₀ (hOU hu₀O)).preimage_mem_nhdsWithin
      (by rw [hrfix hu₀O]; exact Metric.ball_mem_nhds u₀ hδ))
  -- a closed neighbourhood `T` of `x` on which the solution set is compact
  obtain ⟨N, hN, hNcpt⟩ := exists_nhds_isCompact_zeros hf x
  obtain ⟨T, hT, hTc, hTN⟩ := exists_mem_nhds_isClosed_subset hN
  obtain ⟨δ₃, hδ₃, hδ₃T⟩ := Metric.mem_nhdsWithin_iff.1
    ((c.φ.continuousOn_invFun u₀ hu₀O).preimage_mem_nhdsWithin
      (by rw [show c.φ.toPartialEquiv.symm u₀ = x from c.φ.symm_apply_apply hxc]; exact hT))
  set δ' := min δ (min δ₂ δ₃) with hδ'def
  have hδ' : 0 < δ' := lt_min hδ (lt_min hδ₂ hδ₃)
  set W : Set X := c.φ.source ∩ c.φ ⁻¹' Metric.ball u₀ δ with hWdef
  set U : Set X := c.φ.source ∩ c.φ ⁻¹' Metric.ball u₀ δ' with hUdef
  have hWo : IsOpen W :=
    c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source Metric.isOpen_ball
  have hUo : IsOpen U :=
    c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source Metric.isOpen_ball
  have hxU : x ∈ U := ⟨hxc, Metric.mem_ball_self hδ'⟩
  have hUW : U ⊆ W := fun y hy => ⟨hy.1, Metric.ball_subset_ball (min_le_left _ _) hy.2⟩
  have hUT : U ⊆ T := fun y hy => by
    have := hδ₃T ⟨Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hy.2,
      c.φ.mapsTo_model y hy.1⟩
    rwa [mem_preimage, show c.φ.toPartialEquiv.symm (c.φ y) = y from
      c.φ.symm_apply_apply hy.1] at this
  refine ⟨U, W, c, hUo, hWo, hxU, hUW, hc, inter_subset_left, ?_, ?_, ?_, ?_⟩
  · -- (1′): the straight-line homotopy in the chart, followed by `r`
    intro γ₀ γ₁ hγ₀ hγ₁ hγ₀U hγ₁U h0 h1
    have hγ₀c : Continuous γ₀ := continuousOn_univ.1 hγ₀.continuousOn
    have hγ₁c : Continuous γ₁ := continuousOn_univ.1 hγ₁.continuousOn
    -- a reparametrization keeping both paths in `U`
    set A : Set (Fin 1 → ℝ) := γ₀ ⁻¹' U ∩ γ₁ ⁻¹' U with hAdef
    have hAo : IsOpen A := (hUo.preimage hγ₀c).inter (hUo.preimage hγ₁c)
    have hpt1 : ∀ p : Fin 1 → ℝ, pt1 (p 0) = p := fun p =>
      funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl
    have hIA : Icc (0 : Fin 1 → ℝ) 1 ⊆ A := fun p hp => by
      have hp0 : p 0 ∈ Icc (0 : ℝ) 1 := ⟨hp.1 0, hp.2 0⟩
      rw [← hpt1 p]
      exact ⟨hγ₀U _ hp0, hγ₁U _ hp0⟩
    obtain ⟨σ, hσ, hσid, hσA⟩ := exists_contDiff_eq_id_near_Icc_mapsTo hAo hIA
    have hσI : ∀ t ∈ Icc (0 : ℝ) 1, σ (pt1 t) = pt1 t := fun t ht =>
      hσid.self_of_nhdsSet _ ⟨fun _ => ht.1, fun _ => ht.2⟩
    -- the homotopy
    set ρ : ℝ → ℝ := Real.smoothTransition with hρdef
    set k : (Fin 2 → ℝ) → Fin 1 → ℝ := fun p => σ (pt1 (p 1)) with hkdef
    have hk : ContDiff ℝ ∞ k := hσ.comp (contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ (1 : Fin 2))
    set v₀ : (Fin 2 → ℝ) → c.φ.model.E 0 := fun p => c.φ (γ₀ (k p)) with hv₀def
    set v₁ : (Fin 2 → ℝ) → c.φ.model.E 0 := fun p => c.φ (γ₁ (k p)) with hv₁def
    set G₀ : (Fin 2 → ℝ) → c.φ.model.E 0 := fun p => (1 - ρ (p 0)) • v₀ p + ρ (p 0) • v₁ p
      with hG₀def
    set Φ : (Fin 2 → ℝ) → X := fun p => c.φ.symm (r (G₀ p)) with hΦdef
    have hkU₀ : ∀ p, γ₀ (k p) ∈ U := fun p => (hσA _).1
    have hkU₁ : ∀ p, γ₁ (k p) ∈ U := fun p => (hσA _).2
    have hvB : ∀ {y}, y ∈ U → c.φ y ∈ Metric.ball u₀ δ' ∩ c.φ.model.C := fun hy =>
      ⟨hy.2, hUC (hOU (c.φ.mapsTo_model _ hy.1))⟩
    have hG₀B : ∀ p, G₀ p ∈ Metric.ball u₀ δ' ∩ c.φ.model.C := fun p =>
      ((convex_ball u₀ δ').inter hCconv) (hvB (hkU₀ p)) (hvB (hkU₁ p))
        (sub_nonneg.2 (Real.smoothTransition.le_one _)) (Real.smoothTransition.nonneg _)
        (sub_add_cancel 1 _)
    have hG₀U : ∀ p, G₀ p ∈ c.U := fun p =>
      hballU (Metric.ball_subset_ball (min_le_left _ _) (hG₀B p).1) (hG₀B p).2
    have hrG₀ : ∀ p, r (G₀ p) ∈ Metric.ball u₀ δ := fun p =>
      hδ₂r ⟨Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) (hG₀B p).1,
        hG₀U p⟩
    have hfix : ∀ y ∈ c.φ.source, c.φ.symm (r (c.φ y)) = y := fun y hy => by
      rw [hrfix (c.φ.mapsTo_model y hy), c.φ.symm_apply_apply hy]
    have hΦapp : ∀ τ t, Φ (pt2 τ t) = c.φ.symm (r ((1 - ρ τ) • c.φ (γ₀ (σ (pt1 t))) +
        ρ τ • c.φ (γ₁ (σ (pt1 t))))) := fun _ _ => rfl
    have hρ₀ : ρ 0 = 0 := Real.smoothTransition.zero
    have hρ₁ : ρ 1 = 1 := Real.smoothTransition.one
    have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    refine ⟨Φ, ⟨?_, fun t ht => ?_, fun t ht => ?_, fun τ _ => ?_, fun τ _ => ?_⟩,
      fun τ _ t _ => ?_⟩
    · -- sc-smoothness, read in the chart
      have hU2 := isScDomain_univ (rnSc 2)
      have hv₀ : IsScSmooth (E := rnSc 2) (F := c.φ.model.E) univ v₀ :=
        isScSmooth_chart_comp (hγ₀.comp (isScSmoothMap_rn_rn_of_contDiff hk)) c.isChart
          fun p => (hkU₀ p).1
      have hv₁ : IsScSmooth (E := rnSc 2) (F := c.φ.model.E) univ v₁ :=
        isScSmooth_chart_comp (hγ₁.comp (isScSmoothMap_rn_rn_of_contDiff hk)) c.isChart
          fun p => (hkU₁ p).1
      have hρ0 : IsScSmooth (E := rnSc 2) (F := ScBanach.const ℝ) univ
          fun p : Fin 2 → ℝ => ρ (p 0) :=
        IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) hU2
          ((Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 2))).contDiffOn)
      have hρ1 : IsScSmooth (E := rnSc 2) (F := ScBanach.const ℝ) univ
          fun p : Fin 2 → ℝ => 1 - ρ (p 0) :=
        IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) hU2 ((contDiff_const.sub
          (Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 2)))).contDiffOn)
      have hG₀ : IsScSmooth (E := rnSc 2) (F := c.φ.model.E) univ G₀ :=
        (hρ1.smul hU2 hv₀).add hU2 (hρ0.smul hU2 hv₁)
      have hrG : IsScSmooth (E := rnSc 2) (F := c.φ.model.E) univ fun p => r (G₀ p) :=
        IsScSmooth.comp hU2 c.relOpen.isScDomain
          (c.isRetraction.baseRetraction c.relOpen).isScSmooth hG₀ fun p _ => hG₀U p
      exact isScSmoothMap_rn_chart_symm c.isChart hrG fun p => hrO (hG₀U p)
    · rw [hΦapp, hσI t ht, hρ₀, sub_zero, one_smul, zero_smul, add_zero]
      exact hfix _ (hγ₀U t ht).1
    · rw [hΦapp, hσI t ht, hρ₁, sub_self, zero_smul, one_smul, zero_add]
      exact hfix _ (hγ₁U t ht).1
    · rw [hΦapp, hσI 0 h0I, ← h0, ← add_smul, sub_add_cancel, one_smul]
      exact hfix _ (hγ₀U 0 h0I).1
    · rw [hΦapp, hσI 1 h1I, ← h1, ← add_smul, sub_add_cancel, one_smul]
      exact hfix _ (hγ₀U 1 h1I).1
    · refine ⟨c.φ.symm_mapsTo (hrO (hG₀U _)), ?_⟩
      change c.φ (c.φ.symm (r (G₀ (pt2 τ t)))) ∈ Metric.ball u₀ δ
      rw [c.φ.apply_symm_apply (hrO (hG₀U _))]
      exact hrG₀ _
  · -- (2): `cl(U) ⊆ T ⊆ N`
    exact hNcpt _ isClosed_closure ((closure_minimal hUT hTc).trans hTN)
  · -- (3)
    intro n _ _ Φ hΦ hΦW
    exact exists_isScPlusSection_pullback_of_family hbump hf.isScSmooth hΦ hc
      fun q hq => (hΦW q hq).1
  · -- (4)
    intro n _ _
    exact hasScPlusSectionsThrough_pullback_rn_of_bump hbump

end Polyfold
