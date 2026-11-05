import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_36

/-! **Refresh 2026-11-02** (HEAD after the germ reading of Definition 3.11 and the notions built
on it).
A's parametrized-section theorems (general position of F, existence of sections with (i)–(ii)) now
carry germ-reading hypotheses; B is chart-level linear algebra that does not use those notions and
is still proved outright. Result unchanged: A ⇒ B vacuous, B ⇒ A fails (B never mentions F, its
general position, or the existence of the sections).
-/

namespace RoundTrip.V5_36
open Polyfold

/-- The project's statement: the conjunction of the four theorems of the decls (universes at `0`;
`IsParamGP` is vocabulary): adding sections keeps (i)–(ii) (`IsParamGP.comp`), (i)–(ii) in a tame
chart centred at a zero give general position of the parametrized section `F` at `(0, y)` and
conversely, and sections with (i)–(ii) exist (bump functions, auxiliary norm, tame germ data). -/
def A : Prop :=
  (type_of% @Polyfold.StrongBundleChart.IsParamGP.comp.{0, 0}) ∧
  (type_of% @Polyfold.isGeneralPositionGerm_paramSection_of_isParamGP.{0, 0}) ∧
  (type_of% @Polyfold.isParamGP_of_isGeneralPositionGerm.{0, 0}) ∧
  (type_of% @Polyfold.exists_sections_isParamGP.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundleChart.IsParamGP.comp.{0, 0},
    @Polyfold.isGeneralPositionGerm_paramSection_of_isParamGP.{0, 0},
    @Polyfold.isParamGP_of_isGeneralPositionGerm.{0, 0},
    @Polyfold.exists_sections_isParamGP.{0, 0}⟩

set_option linter.unusedSectionVars false

section Glue
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- `F'(0, x)` for an appended family and appended coefficients. -/
theorem DF_append (c : StrongBundleChart PX P) (g : X → Y) {m k : ℕ} (t : Fin m → X → Y)
    (s : Fin k → X → Y) (x : X) (z : c.φ.model.E.lvl 1) (a₁ : Fin m → ℝ) (a₂ : Fin k → ℝ)
    (u : c.φ.model.E.lvl 0) :
    DF c g (Fin.append t s) x z (Fin.append a₁ a₂) u =
      DF c g t x z a₁ u + ∑ j, a₂ j • c.principal (s j) (c.φ.toPartialEquiv x) := by
  simp only [DF, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  abel

/-- (i) survives appending sections (with zero coefficients). -/
theorem propI_append (c : StrongBundleChart PX P) (g : X → Y) {m k : ℕ} (t : Fin m → X → Y)
    (s : Fin k → X → Y) (x : X) (z : c.φ.model.E.lvl 1) (h : PropI c g t x z) :
    PropI c g (Fin.append t s) x z := by
  intro w hw
  obtain ⟨a, u, hu, hDF⟩ := h w hw
  refine ⟨Fin.append a 0, u, hu, ?_⟩
  rw [DF_append, hDF]
  simp

/-- (ii) survives appending sections. -/
theorem propII_append (c : StrongBundleChart PX P) (g : X → Y) {m k : ℕ} (t : Fin m → X → Y)
    (s : Fin k → X → Y) (x : X) (z : c.φ.model.E.lvl 1) {n : ℕ} {W : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) (h : PropII c g t x z T) :
    PropII c g (Fin.append t s) x z T := by
  intro b w hw
  obtain ⟨a, u, hu, hDF, -, r, hr, -, hwr⟩ := h (fun i => b (Fin.castAdd k i)) w hw
  refine ⟨Fin.append a 0, u, hu, ?_, b - Fin.append a 0, r, hr, by abel, hwr⟩
  rw [DF_append, hDF]
  simp

/-- **(1) The definition agrees**: in a chart centred at `y`, `IsParamGP` is B's (i)–(ii). -/
theorem isParamGP_iff (c : StrongBundleChart PX P) (g : X → Y) (y : X)
    (hφ0 : c.φ.toPartialEquiv y = 0) {m : ℕ} (t : Fin m → X → Y) {n : ℕ} {W : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    c.IsParamGP g t T ↔ ParamGPB c g t T y := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨0, by rw [map_zero, hφ0], fun k hk => ?_, fun b w hw => ?_⟩
    · rw [hφ0] at hk
      obtain ⟨u, a, hua⟩ := h1 k hk
      refine ⟨a, u.1, u.2, ?_⟩
      simp only [DF, hφ0]
      exact hua
    · obtain ⟨u, a, hua, hwu⟩ := h2 ⟨w, hw⟩
      refine ⟨a, u.1, u.2, ?_, b - a, w - u.1, ⟨Submodule.sub_mem _ hw u.2, ?_⟩, by abel,
        by abel⟩
      · simp only [DF, hφ0]
        exact hua
      · rw [hφ0]; exact hwu
  · rintro ⟨z, hz, h1, h2⟩
    have hz0 : z = 0 := by
      apply c.φ.model.E.toBase_injective 1
      rw [hz, hφ0, map_zero]
    subst hz0
    refine ⟨fun k hk => ?_, fun w => ?_⟩
    · rw [← hφ0] at hk
      obtain ⟨a, u, hu, hDF⟩ := h1 k hk
      refine ⟨⟨u, hu⟩, a, ?_⟩
      simp only [DF, hφ0] at hDF
      exact hDF
    · obtain ⟨a, u, hu, hDF, -, r, hr, -, hwr⟩ := h2 0 w w.2
      refine ⟨⟨u, hu⟩, a, ?_, ?_⟩
      · simp only [DF, hφ0] at hDF
        exact hDF
      · have : (w : c.φ.model.E.lvl 0) - u = r := by rw [hwr]; abel
        rw [this, ← hφ0]
        exact hr.2

/-- **(3)** a finite-dimensional complement of `T^R` in `T_zO` (`T^R` has finite codimension:
it is the kernel of the coordinates `λ_{I(x)}` on `T_zO`). -/
theorem exists_complement (c : StrongBundleChart PX P) (z : c.φ.model.E.lvl 1) (x : X)
    {n : ℕ} {W : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    ∃ L : Submodule ℝ (c.φ.model.E.lvl 0), IsComplementTR c z x T L ∧ FiniteDimensional ℝ L := by
  set Q := TO c z with hQ
  set R' : Submodule ℝ Q := (TR c z x T).comap Q.subtype with hR'
  obtain ⟨L₀, hL₀⟩ := Submodule.exists_isCompl R'
  set L := L₀.map Q.subtype with hL
  have hLQ : L ≤ Q := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  have hdisj : Disjoint L (TR c z x T) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro _ ⟨⟨v, hv, rfl⟩, hvR⟩
    have h1 : v ∈ R' ⊓ L₀ := ⟨hvR, hv⟩
    rw [hL₀.inf_eq_bot, Submodule.mem_bot] at h1
    rw [h1]
    exact Submodule.zero_mem _
  refine ⟨L, ⟨hLQ, hdisj, ?_⟩, ?_⟩
  · apply le_antisymm
    · exact sup_le hLQ inf_le_left
    · intro v hv
      have h1 : (⟨v, hv⟩ : Q) ∈ R' ⊔ L₀ := by rw [hL₀.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
      have h2 : v = (b : c.φ.model.E.lvl 0) + a := by
        have := congrArg Subtype.val hab
        simp only [Submodule.coe_add] at this
        rw [← this, add_comm]
      rw [h2]
      exact Submodule.add_mem_sup ⟨b, hb, rfl⟩ ha
  · -- the coordinates `λ_{I(x)}` are injective on `L`
    set p := c.φ.toPartialEquiv x
    set κ : L →ₗ[ℝ] ({i : Fin n // (T 0 p).1 i = 0} → ℝ) :=
      (coordMapL T p).toLinearMap ∘ₗ L.subtype with hκ
    have hinj : Function.Injective κ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      rintro ⟨v, hv⟩ hκv
      have hvM : v ∈ minimalSubspaceWith T p := hκv
      have hvR : v ∈ TR c z x T := ⟨hLQ hv, hvM⟩
      have h0 : v ∈ L ⊓ TR c z x T := ⟨hv, hvR⟩
      rw [hdisj.eq_bot, Submodule.mem_bot] at h0
      rw [Submodule.mem_bot]
      exact Subtype.ext h0
    exact Module.Finite.of_injective κ hinj

/-- **(4)** adding to a family with (i) sections which at `x` span `f'(x)L` gives (i)–(ii). -/
theorem paramGP_of_span (c : StrongBundleChart PX P) (g : X → Y) (x : X)
    (z : c.φ.model.E.lvl 1) (hz : c.φ.model.E.toBase 1 z = c.φ.toPartialEquiv x)
    {n : ℕ} {W : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    {m k : ℕ} (t : Fin m → X → Y) (s : Fin k → X → Y) (L : Submodule ℝ (c.φ.model.E.lvl 0))
    (hI : PropI c g t x z) (hL : IsComplementTR c z x T L)
    (hspan : Submodule.span ℝ (Set.range fun j => c.principal (s j) (c.φ.toPartialEquiv x)) =
      L.map (Dg c g z).toLinearMap) :
    ParamGPB c g (Fin.append t s) T x := by
  refine ⟨z, hz, propI_append c g t s x z hI, fun b w hw => ?_⟩
  have hw' : w ∈ L ⊔ TR c z x T := by rw [hL.2.2]; exact hw
  obtain ⟨l, hl, r, hr, hlr⟩ := Submodule.mem_sup.1 hw'
  have hDl : Dg c g z l ∈ Submodule.span ℝ
      (Set.range fun j => c.principal (s j) (c.φ.toPartialEquiv x)) := by
    rw [hspan]; exact ⟨l, hl, rfl⟩
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hDl
  refine ⟨Fin.append 0 (-d), l, hL.1 hl, ?_, b - Fin.append 0 (-d), r, hr, by abel, hlr.symm⟩
  rw [DF_append]
  simp only [DF, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, Pi.neg_apply,
    neg_smul, Finset.sum_neg_distrib, hd]
  exact add_neg_cancel _

end Glue

/-- **B holds outright**: (1) by `isParamGP_iff`, (2) by `propI_append`/`propII_append`, (3) by
`exists_complement`, (4) by `paramGP_of_span`.  None of A's theorems is needed. -/
theorem B_holds : B := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd
  refine ⟨fun g y c _ _ hφ0 _ m t n W T _ => isParamGP_iff c g y hφ0 t T, ?_, ?_, ?_⟩
  · intro g x c _ _ m k t s n W T _ h
    obtain ⟨z, hz, h1, h2⟩ := h
    exact ⟨z, hz, propI_append c g t s x z h1, propII_append c g t s x z T h2⟩
  · intro x c _ _ z _ n W T _
    exact exists_complement c z x T
  · intro g x c _ _ _ z hz n W T _ m k t s L hI hL hspan
    exact paramGP_of_span c g x z hz T t s L hI hL hspan

/-- `A ⇒ B`: vacuous (B is proved outright). -/
theorem A_to_B : A → B := fun _ => B_holds

/-! `B ⇒ A` is not proved.  B is the pointwise linear algebra of properties (i)–(ii) in one chart
(the definition, monotonicity, a complement `L`, and "sections spanning `f'(x)L` give (ii)").  A's
second and third conjuncts identify (i)–(ii) with the general position (Definition 5.17) of the
parametrized section `F(λ, y) = g(y) + Σ λᵢ tᵢ(y)` on `ℝᵐ × X` at `(0, y)`, in the tame product
chart (via `T_{(0,y)}S̃ = ker F'(0, y)` and the sc-complement inside `T^R`): B never mentions `F`,
the product bundle or Definition 5.17.  A's fourth conjunct is the existence of allowable
sc⁺-sections with (i)–(ii) (bump functions, Lemma 5.11, an auxiliary norm, the density of smooth
vectors): B only says what such sections achieve, not that they exist.  `IsParamGP.comp` (A's first
conjunct) is for an arbitrary reindexing `ι`, no zero and no compatible-chart hypothesis; B gives
monotonicity only for `Fin.append` and the definition only at zeros of charts of the atlas. -/

#rt_check RoundTrip.V5_36.A_to_B [Polyfold.StrongBundleChart.IsParamGP.comp,
  Polyfold.isGeneralPositionGerm_paramSection_of_isParamGP,
  Polyfold.isParamGP_of_isGeneralPositionGerm, Polyfold.exists_sections_isParamGP]

end RoundTrip.V5_36
