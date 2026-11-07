import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_50

/-! Round trip for V6_50 (§6.5, the paragraph after Theorem 6.35 and Definition 6.36, p. 227).

* `A`: the types of `exists_two_isContinuousOrientation`, `exists_orientableNbhd`,
  `exists_isOrientableNbhd` (universes at `0`); `IsContinuousOrientation`, `IsOrientableNbhd`
  are vocabulary.
* `B`: (1) path independence and `ψ_*o_{y₁} = o_{y₂}` in an orientable neighbourhood, (2) the
  project's `IsContinuousOrientation` (with `V = U`) is B's `IsContOrB`, (3) an orientable
  neighbourhood (`IsOrNbhdB`: open, sc-smoothly contractible, local propagation) has precisely
  two continuous orientations.
* (1) and (2) need nothing from `A`: (1a) is the field `HasLocalPropagation.eq`, (1b) is
  `HasLocalPropagation.eq_trans` (not an item theorem), (2) is `Iff.rfl`.
* (3) from `A` (`A_to_ThreeSec`): `exists_two_isContinuousOrientation` with `V = U`, the paths
  `hpath` built from the contraction (`concatPath` of `t ↦ H(κ(t), y₁)` and
  `t ↦ H(κ(1 − t), y₂)`, with values in `U` for all `t`), and the hypothesis
  `B.HasScPlusSectionsThrough`, which `B` does not give.
* That hypothesis is only used, in the project's proof, for `Lin(f, x) ≠ ∅`.  In an orientable
  neighbourhood it is redundant: the push-forward datum along the constant path at `x` (which
  `HasLocalPropagation.exists_isPush` provides) contains an sc⁺-section `S` of the pulled-back
  bundle with `f + S(0, ·)` vanishing at `x`, whose slice puts `(f + S(0, ·))'(x)` in `Lin(f, x)`
  (`linSet_nonempty_of_localPropagation`).  With it `three_outright` proves (3) without the
  hypothesis (the argument of `exists_two_isContinuousOrientation`, re-run), so `B` holds
  outright and `A_to_B` is vacuous.
* `B ⇒ A` is not proved: `B` has no existence statement (`exists_orientableNbhd`,
  `exists_isOrientableNbhd` are Theorem 6.35 + `exists_nhds_scPath`), and its (3) is only for
  `V = U` sc-smoothly contractible and open, while `exists_two_isContinuousOrientation` is for
  any pair `V ⊆ U` whose smooth points are joined by paths in `U`.
-/

namespace RoundTrip.V6_50
open Polyfold Set Filter Topology
open scoped ContDiff

local notation "κ" => Real.smoothTransition

/-- The project's statement: the item's theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.exists_two_isContinuousOrientation.{0, 0} ∧
  type_of% @Polyfold.exists_orientableNbhd.{0, 0} ∧
  type_of% @Polyfold.exists_isOrientableNbhd.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.exists_two_isContinuousOrientation.{0, 0}, @Polyfold.exists_orientableNbhd.{0, 0},
    @Polyfold.exists_isOrientableNbhd.{0, 0}⟩

/-- Conjunct (3) of `B`, in `B`'s setting. -/
def Three : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
    PX.IsTame →
    ∀ (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (U : Set X) (x : X)
      (hU : U ⊆ c.φ.source), IsOrNbhdB f hf c hc U x → x ∈ PX.smoothSet →
      ∃ o₁ o₂ : (∀ (y : X) (hy : y ∈ U) (hys : y ∈ PX.smoothSet),
          ChartPoint.Or f (chartPtOf c hc (hU hy) hys) hf),
        o₁ ≠ o₂ ∧ IsContOrB f hf c hc U hU o₁ ∧ IsContOrB f hf c hc U hU o₂ ∧
        ∀ o, IsContOrB f hf c hc U hU o → o = o₁ ∨ o = o₂

/-- Conjunct (3) of `B` with the extra hypothesis `Bd.HasScPlusSectionsThrough` of `A`. -/
def ThreeSec : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
    PX.IsTame → Bd.HasScPlusSectionsThrough →
    ∀ (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (U : Set X) (x : X)
      (hU : U ⊆ c.φ.source), IsOrNbhdB f hf c hc U x → x ∈ PX.smoothSet →
      ∃ o₁ o₂ : (∀ (y : X) (hy : y ∈ U) (hys : y ∈ PX.smoothSet),
          ChartPoint.Or f (chartPtOf c hc (hU hy) hys) hf),
        o₁ ≠ o₂ ∧ IsContOrB f hf c hc U hU o₁ ∧ IsContOrB f hf c hc U hU o₂ ∧
        ∀ o, IsContOrB f hf c hc U hU o → o = o₁ ∨ o = o₂

section Paths

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]

/-- **Paths in a contractible `U`**: any two smooth points of an sc-smoothly contractible `U` are
joined by an sc-smooth path with values in `U` for all `t` (the hypothesis `hpath` of
`exists_two_isContinuousOrientation`). -/
theorem paths_of_contractible {U : Set X} (hU : IsScContractibleB PX U) :
    ∀ y₁ ∈ U, ∀ y₂ ∈ U, y₁ ∈ PX.smoothSet → y₂ ∈ PX.smoothSet →
      ∃ γ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ ∧ γ (pt1 0) = y₁ ∧
        γ (pt1 1) = y₂ ∧ ∀ t, γ t ∈ U := by
  intro y₁ hy₁ y₂ hy₂ hs₁ hs₂
  obtain ⟨H, hHs, hHU, hH0, p, hpU, hH1⟩ := hU
  have hκI : ∀ t, pt1 (κ t) ∈ Icc (0 : Fin 1 → ℝ) 1 := fun t =>
    pt1_mem_Icc ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hpath : ∀ {u : X}, u ∈ U → u ∈ PX.smoothSet → ∀ {σ : ℝ → ℝ}, ContDiff ℝ ∞ σ →
      (rnPolyfold 1).IsScSmoothMap PX fun t => H (pt1 (κ (σ (t 0))), u) := by
    intro u hu hus σ hσ
    have hpair : (rnPolyfold 1).IsScSmoothOn ((rnPolyfold 1).prod PX)
        (fun t : Fin 1 → ℝ => (pt1 (κ (σ (t 0))), u)) univ :=
      MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_rn_rn_of_contDiff
          (contDiff_pt1_comp (Real.smoothTransition.contDiff.comp hσ)))
        (isScSmoothMap_const_of_mem_smoothSet hus)
    exact MPolyfold.IsScSmoothOn.comp hHs hpair fun t _ => ⟨mem_univ _, hu⟩
  set γ₁ : (Fin 1 → ℝ) → X := fun t => H (pt1 (κ (t 0)), y₁) with hγ₁
  set γ₂ : (Fin 1 → ℝ) → X := fun t => H (pt1 (κ (1 - t 0)), y₂) with hγ₂
  have hγ₁s : (rnPolyfold 1).IsScSmoothMap PX γ₁ := hpath hy₁ hs₁ contDiff_id
  have hγ₂s : (rnPolyfold 1).IsScSmoothMap PX γ₂ :=
    hpath hy₂ hs₂ (σ := fun t => 1 - t) (contDiff_const.sub contDiff_id)
  have e10 : γ₁ (pt1 0) = y₁ := by
    simp only [hγ₁, pt1_apply, Real.smoothTransition.zero]; exact hH0 y₁ hy₁
  have e11 : γ₁ (pt1 1) = p := by
    simp only [hγ₁, pt1_apply, Real.smoothTransition.one]; exact hH1 y₁ hy₁
  have e20 : γ₂ (pt1 0) = p := by
    simp only [hγ₂, pt1_apply, sub_zero, Real.smoothTransition.one]; exact hH1 y₂ hy₂
  have e21 : γ₂ (pt1 1) = y₂ := by
    simp only [hγ₂, pt1_apply, sub_self, Real.smoothTransition.zero]; exact hH0 y₂ hy₂
  refine ⟨concatPath γ₁ γ₂, isScSmoothMap_concatPath hγ₁s hγ₂s (e11.trans e20.symm),
    concatPath_zero.trans e10, concatPath_one.trans e21, fun q => ?_⟩
  rcases le_or_gt (q 0) (1 / 2) with h | h
  · rw [concatPath_of_le h]; exact hHU _ (hκI _) y₁ hy₁
  · rw [concatPath_of_gt h]; exact hHU _ (hκI _) y₂ hy₂

end Paths

/-! ### (1) and (2) need nothing from `A` -/

/-- `B` from its conjunct (3): (1a) is `HasLocalPropagation.eq`, (1b) is
`HasLocalPropagation.eq_trans`, (2) is definitional. -/
theorem B_of_Three (h3 : Three) : B := by
  intro X _ _ _ PX Y _ _ _ P _ _ _ _ Bd f hf hT
  refine ⟨fun c hc U x hN hU hx hxc ox => ⟨?_, ?_⟩, fun c hc U hU o => Iff.rfl,
    fun c hc U x hU hN hx => h3 PX P Bd f hf hT c hc U x hU hN hx⟩
  · intro y hy hyc φ φ' hφ hφ' hφU hφ'U e e' he he'
    rw [hN.2.2.2.eq φ φ' hφ.1 hφ'.1 hφU hφ'U hφ.2.1 hφ.2.2 hφ'.2.1 hφ'.2.2 hxc hyc hx hy e e'
      he he']
  · intro y₁ y₂ hy₁ hy₂ hy₁c hy₂c φ₁ φ₂ ψ hφ₁ hφ₂ hψ hφ₁U hφ₂U hψU e₁ e₂ e he₁ he₂ he
    have h := hN.2.2.2.eq_trans hφ₂.1 hφ₁.1 hψ.1 hφ₂U hφ₁U hψU hφ₂.2.1 hφ₂.2.2 hφ₁.2.1 hφ₁.2.2
      hψ.2.1 hψ.2.2 hxc hy₁c hy₂c hx hy₁ hy₂ he₂ he₁ he
    rw [h]
    rfl

/-! ### (3) from `A`, with the sections hypothesis -/

theorem A_to_ThreeSec (hA : A) : ThreeSec := by
  intro X _ _ _ PX Y _ _ _ P _ _ _ _ Bd f hf _ hsec c hc U x hU hN hx
  obtain ⟨-, hxU, hcon, hLP⟩ := hN
  obtain ⟨o₁, o₂, h₁, h₂, hne, hall⟩ :=
    hA.1 hLP (Subset.refl U) hxU hx (paths_of_contractible hcon) hsec
  exact ⟨o₁, o₂, hne, h₁, h₂, hall⟩

/-! ### The sections hypothesis is redundant in an orientable neighbourhood -/

section Redundant

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  {Bd : StrongBundle PX P} {f : X → Y}

/-- **`Lin(f, x) ≠ ∅` at a smooth point of a set with the local propagation property**: the
push-forward datum along the constant path at `x` has an sc⁺-section `S` of `π*Y` with
`(f + S)(0, x) = 0`; its slice `s = S(0, ·)` is an sc⁺-section with `(f + s)(x) = 0`, so
`(f + s)'(x) ∈ Lin(f, x)`. -/
theorem linSet_nonempty_of_localPropagation {hf : Bd.IsScFredholmSection f}
    {c : StrongBundleChart PX P} {hc : Bd.IsChart c} {U : Set X}
    (hLP : HasLocalPropagation f hf c hc U) {x : X} (hxU : x ∈ U) (hx : x ∈ PX.smoothSet) :
    ((chartPtOf c hc (hLP.subset hxU) hx).linSet f).Nonempty := by
  have hxc := hLP.subset hxU
  obtain ⟨e, S, hS, hz, -⟩ := hLP.exists_isPush (fun _ => x)
    (isScSmoothMap_const_of_mem_smoothSet hx) (fun _ _ => hxU) rfl rfl hxc hxc hx hx
  have hfs : IsSection P f := hf.isScSmooth.1
  have hz0 := hz.self_of_nhdsSet (pt1 0) (pt1_mem_Icc (left_mem_Icc.2 zero_le_one))
  rw [isZeroAt_pullback_iff_pullbackSlice ((isSection_pullbackLift _).sectionAdd hS.1),
    pullbackSlice_sectionAdd_paramLift hfs hS.1] at hz0
  set p := chartPtOf c hc hxc hx
  set s := pullbackSlice S (pt1 0) with hsdef
  have hs : Bd.IsScPlusSection s := hS.pullbackSlice (pt1 0)
  have hg := hf.isScSmooth.sectionAdd hs
  let L : ↥p.T →L[ℝ] ↥p.K :=
    (linAt p.c.U p.c.R (p.c.principal (sectionAdd P f s)) p.z).codRestrict p.K
      fun v => p.scDeriv_mem_K hg hz0 v
  refine ⟨L, s, hs, hz0, 0, p.isScPlusOp_zero hx, fun v => ?_⟩
  rw [zero_apply, Submodule.coe_zero, add_zero]
  rfl

/-- `exists_two_isContinuousOrientation` for `V = U` without the sections hypothesis (its proof,
with `Lin(f, x) ≠ ∅` from `linSet_nonempty_of_localPropagation`). -/
theorem exists_two_of_localPropagation {hf : Bd.IsScFredholmSection f}
    {c : StrongBundleChart PX P} {hc : Bd.IsChart c} {U : Set X}
    (hU : HasLocalPropagation f hf c hc U) {x : X} (hxV : x ∈ U) (hxs : x ∈ PX.smoothSet)
    (hpath : ∀ y₁ ∈ U, ∀ y₂ ∈ U, y₁ ∈ PX.smoothSet → y₂ ∈ PX.smoothSet →
      ∃ γ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ ∧ γ (pt1 0) = y₁ ∧
        γ (pt1 1) = y₂ ∧ ∀ t, γ t ∈ U) :
    ∃ o₁ o₂ : ∀ y (hy : y ∈ U) (hys : y ∈ PX.smoothSet),
        (chartPtOf c hc (hU.subset hy) hys).Or f hf,
      o₁ ≠ o₂ ∧ IsContOrB f hf c hc U hU.subset o₁ ∧ IsContOrB f hf c hc U hU.subset o₂ ∧
      ∀ o, IsContOrB f hf c hc U hU.subset o → o = o₁ ∨ o = o₂ := by
  choose γ hγs hγ0 hγ1 hγU using fun y (hy : y ∈ U) (hys : y ∈ PX.smoothSet) =>
    hpath x hxV y hy hxs hys
  choose E hE using fun y (hy : y ∈ U) (hys : y ∈ PX.smoothSet) =>
    hU.exists_isPush (γ y hy hys) (hγs y hy hys) (fun q _ => hγU y hy hys q) (hγ0 y hy hys)
      (hγ1 y hy hys) (hU.subset hxV) (hU.subset hy) hxs hys
  have key : ∀ δ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX δ →
      ∀ (hδ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, δ q ∈ U) {y₁ y₂ : X} (hy₁ : y₁ ∈ U) (hy₂ : y₂ ∈ U)
        (hs₁ : y₁ ∈ PX.smoothSet) (hs₂ : y₂ ∈ PX.smoothSet) (h₀ : δ (pt1 0) = y₁)
        (h₁ : δ (pt1 1) = y₂) (e : (chartPtOf c hc (hU.subset hy₁) hs₁).Or f hf ≃
          (chartPtOf c hc (hU.subset hy₂) hs₂).Or f hf),
        IsPush f hf c hc δ (fun q hq => hU.subset (hδ q hq)) h₀ h₁ (hU.subset hy₁)
          (hU.subset hy₂) hs₁ hs₂ e →
        ∀ o, e (E y₁ hy₁ hs₁ o) = E y₂ hy₂ hs₂ o := by
    intro δ hδs hδ y₁ y₂ hy₁ hy₂ hs₁ hs₂ h₀ h₁ e he o
    have h := hU.eq_trans (hγs y₂ hy₂ hs₂) (hγs y₁ hy₁ hs₁) hδs (fun q _ => hγU y₂ hy₂ hs₂ q)
      (fun q _ => hγU y₁ hy₁ hs₁ q) hδ (hγ0 y₂ hy₂ hs₂) (hγ1 y₂ hy₂ hs₂) (hγ0 y₁ hy₁ hs₁)
      (hγ1 y₁ hy₁ hs₁) h₀ h₁ (hU.subset hxV) (hU.subset hy₁) (hU.subset hy₂)
      hxs hs₁ hs₂ (hE y₂ hy₂ hs₂) (hE y₁ hy₁ hs₁) he
    exact (congrArg (fun F => F o) h).symm
  obtain ⟨a, b, hab, hall⟩ := (proposition_6_26
    ((chartPtOf c hc (hU.subset hxV) hxs).convex_linSet hf)
    (linSet_nonempty_of_localPropagation hU hxV hxs)
    ((chartPtOf c hc (hU.subset hxV) hxs).isFredholm_of_mem_linSet hf)).2
  have hcont : ∀ o', IsContOrB f hf c hc U hU.subset (fun y hy hys => E y hy hys o') :=
    fun o' δ hδs hδ _ _ hy₁ hy₂ hs₁ hs₂ h₀ h₁ e he => key δ hδs hδ hy₁ hy₂ hs₁ hs₂ h₀ h₁ e he o'
  refine ⟨fun y hy hys => E y hy hys a, fun y hy hys => E y hy hys b, ?_, hcont a, hcont b, ?_⟩
  · intro h
    exact hab ((E x hxV hxs).injective (congrFun (congrFun (congrFun h x) hxV) hxs))
  · intro o ho
    have hoE : ∀ y hy hys, o y hy hys = E y hy hys (o x hxV hxs) := fun y hy hys =>
      (ho (γ y hy hys) (hγs y hy hys) (fun q _ => hγU y hy hys q) hxV hy hxs hys
        (hγ0 y hy hys) (hγ1 y hy hys) (E y hy hys) (hE y hy hys)).symm
    rcases hall (o x hxV hxs) with h | h
    · exact Or.inl (funext fun y => funext fun hy => funext fun hys =>
        (hoE y hy hys).trans (congrArg _ h))
    · exact Or.inr (funext fun y => funext fun hy => funext fun hys =>
        (hoE y hy hys).trans (congrArg _ h))

end Redundant

/-- **(3) holds outright** (no sections hypothesis, no `A`). -/
theorem three_outright : Three := by
  intro X _ _ _ PX Y _ _ _ P _ _ _ _ Bd f hf _ c hc U x hU hN hx
  obtain ⟨-, hxU, hcon, hLP⟩ := hN
  exact exists_two_of_localPropagation hLP hxU hx (paths_of_contractible hcon)

/-- `B` is true; `A ⇒ B` is therefore vacuous (the hypothesis is not used). -/
theorem B_outright : B := B_of_Three three_outright

theorem A_to_B : A → B := fun _ => B_outright

#rt_check RoundTrip.V6_50.A_to_B [Polyfold.exists_two_isContinuousOrientation,
  Polyfold.exists_orientableNbhd, Polyfold.exists_isOrientableNbhd]
#rt_check RoundTrip.V6_50.A_to_ThreeSec [Polyfold.exists_two_isContinuousOrientation,
  Polyfold.exists_orientableNbhd, Polyfold.exists_isOrientableNbhd]

end RoundTrip.V6_50
