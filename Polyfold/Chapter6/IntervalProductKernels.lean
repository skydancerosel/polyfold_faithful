import Polyfold.Chapter6.IntervalProductPoint

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230) over the M-polyfold with boundary `[0, 1] × X`:
"this convention is compatible with the choices which have to be made during the construction".

# The lift of push-forward data from `X` to `[0, 1] × X`

## What is formalized

* `wedgeExtLeft_smul_single`, `SubspaceFamily.prodLineWedgeEquivS`: the map
  `w ↦ (a ê) ∧ J(w)` of the family `ℝ × Λ` for a scalar `a ≠ 0` (the sign of the chart of
  `[0, 1]`); it carries continuous orientations to continuous orientations
  (`isLineOrientation_prodLineS`) and commutes with the continuation (`cont_prodLineS`).
* `ChartPoint.ivOrFirst`, `ivOrFirst₀`: the orientation `e ∧ o` of `DET(f̂, (t, x))` at a point
  of `[0, 1] × X`, `e` the standard direction of `[0, 1]`, read in the product chart point.
* `IsStabKernels.ivLift`: the stabilized kernels of `f̃` along `q ↦ (τ(q), y(q))` in a product
  chart of `[0, 1] × X` are `ℝ × Λ`.
* `IsPush.ivLift`: a push-forward of `f` along `γ` lifts to a push-forward of `f̃` along
  `(τ, γ)`, `τ` with values in the domain of one chart of `[0, 1]`, which carries `e ∧ o` to
  `e ∧` (push-forward of `o`).
-/

open Module TensorProduct Bundle Topology Set Filter

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

/-! ### The map `w ↦ (a ê) ∧ J(w)` -/

section SignedWedge

variable {K K' : Type*} [AddCommGroup K] [Module ℝ K] [AddCommGroup K'] [Module ℝ K']

/-- `wedgeExtLeft` is linear in the single new vector. -/
theorem wedgeExtLeft_smul_single [FiniteDimensional ℝ K] (M : K →ₗ[ℝ] K') (a : ℝ) (e : K')
    (h : 1 + finrank ℝ K = finrank ℝ K') :
    wedgeExtLeft M ![a • e] h = a • wedgeExtLeft M ![e] h := by
  apply maxPow_linearMap_ext (Module.finBasis ℝ K) rfl
  rw [LinearMap.smul_apply, wedgeExtLeft_wedge, wedgeExtLeft_wedge]
  apply Subtype.ext
  set v : Fin (1 + finrank ℝ K) → K' := Fin.append ![e] (M ∘ ⇑(Module.finBasis ℝ K)) with hv
  set i₀ : Fin (1 + finrank ℝ K) := Fin.castAdd (finrank ℝ K) (0 : Fin 1) with hi₀
  have h1 : Fin.append ![a • e] (M ∘ ⇑(Module.finBasis ℝ K)) =
      Function.update v i₀ (a • v i₀) := by
    funext i
    by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self]
      simp [hv, hi₀]
    · rw [Function.update_of_ne hi]
      induction i using Fin.addCases with
      | left i =>
        fin_cases i
        exact absurd rfl hi
      | right j => simp only [hv, Fin.append_right]
  change ExteriorAlgebra.ιMulti ℝ _ _ = a • ExteriorAlgebra.ιMulti ℝ _ _
  rw [h1, AlternatingMap.map_update_smul, Function.update_eq_self]

end SignedWedge

namespace SubspaceFamily

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
  {Q : Type*} [TopologicalSpace Q] (Λ : SubspaceFamily Q (V × (Fin k → ℝ)))

/-- **`λ(Λ_q) → λ((ℝ × Λ)_q)`, `w ↦ (a ê) ∧ J(w)`**, for a scalar `a ≠ 0`. -/
def prodLineWedgeEquivS (a : ℝ) (ha : a ≠ 0) (q : Q) :
    maxPow (Λ.L q) ≃ₗ[ℝ] maxPow (Λ.prodLine.L q) :=
  (Λ.prodLineWedgeEquiv q).trans (LinearEquiv.smulOfNeZero ℝ _ a ha)

theorem prodLineWedgeEquivS_apply (a : ℝ) (ha : a ≠ 0) (q : Q) (w : maxPow (Λ.L q)) :
    Λ.prodLineWedgeEquivS a ha q w = a • Λ.prodLineWedge q w := rfl

/-- **`w ↦ (a ê) ∧ J(w)` carries continuous orientations of `λ(Λ)` to continuous orientations
of `λ(ℝ × Λ)`.** -/
theorem isLineOrientation_prodLineS (a : ℝ) (ha : a ≠ 0) (o : LineOrientation Λ.det) :
    IsLineOrientation Λ.prodLine.det
      fun q => Module.Ray.map (Λ.prodLineWedgeEquivS a ha q) (o q) := by
  intro q₀
  obtain ⟨U, hU, σ, hσ, hσo⟩ := o.2 q₀
  refine ⟨U, hU, fun q => a • Λ.prodLineWedge q (σ q), fun q hq => ?_, fun q hq => ?_⟩
  · set ε := Λ.frameAt q
    have hqε : q ∈ ε.U := Λ.mem_frameAt q
    have hkey : ∀ b ∈ ε.U, Λ.prodLineWedge b (σ b) = ε.coord b (σ b) • ε.prodLine.wedgeAt b := by
      intro b hb
      have h1 := ε.coord_smul_wedgeAt hb (σ b)
      calc Λ.prodLineWedge b (σ b) = Λ.prodLineWedge b (ε.coord b (σ b) • ε.wedgeAt b) := by
            rw [h1]
        _ = ε.coord b (σ b) • Λ.prodLineWedge b (ε.wedgeAt b) := LinearMap.map_smul _ _ _
        _ = _ := congrArg (ε.coord b (σ b) • ·) (Λ.prodLineWedge_wedgeAt ε hb)
    have hc : ∀ b ∈ ε.U, ε.prodLine.coord b (a • Λ.prodLineWedge b (σ b)) =
        a • ε.coord b (σ b) := by
      intro b hb
      have h0 : ε.prodLine.coord b (Λ.prodLineWedge b (σ b)) = ε.coord b (σ b) := by
        rw [hkey b hb, map_smul, ε.prodLine.coord_wedgeAt hb, smul_eq_mul, mul_one]
      exact ((ε.prodLine.coord b).map_smul a _).trans (congrArg (a • ·) h0)
    refine (Λ.prodLine.continuousWithinAt_section_iff ε.prodLine hqε).2 ?_
    refine (((Λ.continuousWithinAt_section_iff ε hqε).1 (hσ q hq)).const_smul a
      ).congr_of_eventuallyEq ?_ ?_
    · exact eventually_nhdsWithin_of_eventually_nhds (Filter.eventually_of_mem
        (ε.isOpen.mem_nhds hqε) fun b hb => hc b hb)
    · exact hc q hqε
  · obtain ⟨h0, hoq⟩ := hσo q hq
    exact ⟨(Λ.prodLineWedgeEquivS a ha q).map_ne_zero_iff.2 h0,
      (congrArg (Module.Ray.map (Λ.prodLineWedgeEquivS a ha q)) hoq).trans
        (Module.Ray.map_apply _ _ _)⟩

/-- **Continuation commutes with `w ↦ (a ê) ∧ J(w)`.** -/
theorem cont_prodLineS [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q] (a : ℝ)
    (ha : a ≠ 0) (q₀ q₁ : Q) (r : Module.Ray ℝ (Λ.det q₀)) :
    Λ.prodLine.cont q₀ q₁ (Module.Ray.map (Λ.prodLineWedgeEquivS a ha q₀) r) =
      Module.Ray.map (Λ.prodLineWedgeEquivS a ha q₁) (Λ.cont q₀ q₁ r) := by
  obtain ⟨o, rfl⟩ := exists_lineOrientation_apply_eq (L := Λ.det) q₀ r
  let o' : LineOrientation Λ.prodLine.det := ⟨_, Λ.isLineOrientation_prodLineS a ha o⟩
  exact (Λ.prodLine.cont_eq o' q₀ q₁).trans
    (congrArg (Module.Ray.map (Λ.prodLineWedgeEquivS a ha q₁)) (Λ.cont_eq o q₀ q₁)).symm

end SubspaceFamily

section SignedCompat

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
  {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  {Q : Type*} [TopologicalSpace Q]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- **The map `w ↦ (a ê) ∧ J(w)` of the family `ℝ × Λ` is `extStabWedge` read through the
identifications of the kernels**, for inclusions `j`, `j' = (a · pr₂ A, j pr₁ A)`. -/
theorem prodLineWedgeEquivS_compat (a : ℝ) (ha : a ≠ 0) (A : E' ≃L[ℝ] E × (Fin 1 → ℝ))
    (Γ : F' ≃L[ℝ] F) {T : E →L[ℝ] F} (hT : T.IsFredholm) {φ : (Fin k → ℝ) →L[ℝ] F}
    {φ' : (Fin k → ℝ) →L[ℝ] F'} (hφφ : ∀ μ, φ μ = Γ (φ' μ))
    (j : E →L[ℝ] V) (hj : Function.Injective j) (j' : E' →L[ℝ] (Fin 1 → ℝ) × V)
    (hj' : Function.Injective j') (hjj : ∀ v, j' v = (a • (A v).2, j (A v).1))
    (Λ : SubspaceFamily Q (V × (Fin k → ℝ))) (q : Q)
    (hL : Λ.L q = (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
        E × (Fin k → ℝ) →ₗ[ℝ] F)).map
      ((j.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : E × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ)))
    (hL' : Λ.prodLine.L q = (LinearMap.ker (((extConjOp A Γ T).coprod φ' :
        E' × (Fin k → ℝ) →L[ℝ] F') : E' × (Fin k → ℝ) →ₗ[ℝ] F')).map
      ((j'.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E' × (Fin k → ℝ) →L[ℝ] ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) :
          E' × (Fin k → ℝ) →ₗ[ℝ] ((Fin 1 → ℝ) × V) × (Fin k → ℝ)))
    (w : maxPow (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F))) :
    Λ.prodLineWedgeEquivS a ha q (maxPowEquiv (kerEquivMap j hj hL) w) =
      maxPowEquiv ((extConjKerEquiv A Γ hφφ).symm.trans (kerEquivMap j' hj' hL'))
        (extStabWedge hT w) := by
  have := hT.finite_ker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  have hfin : FiniteDimensional ℝ (Λ.L q) := Λ.finiteDimensional q
  have hrank : 1 + finrank ℝ (Λ.L q) = finrank ℝ (Λ.prodLine.L q) := by
    rw [Λ.finrank_eq, Λ.prodLine.finrank_eq]; rfl
  have key := wedgeExtLeft_maxPowEquiv_eq hT (kerEquivMap j hj hL)
    ((extConjKerEquiv A Γ hφφ).symm.trans (kerEquivMap j' hj' hL')) (Λ.prodLineJr q)
    (a • Λ.prodLineEr q) hrank ?_ (fun x => ?_) w
  · rw [← key, wedgeExtLeft_smul_single]
    rfl
  · apply Subtype.ext
    change ((j' (A.symm (0, fun _ => 1)), (0 : Fin k → ℝ)) :
      ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) = a • prodLineE V k
    rw [hjj, A.apply_symm_apply]
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext i
      simp [prodLineE]
    · simp [prodLineE]
    · simp [prodLineE]
  · apply Subtype.ext
    change ((j' (A.symm ((x : E × (Fin k → ℝ)).1, 0)), (x : E × (Fin k → ℝ)).2) :
      ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) =
        ((0, j (x : E × (Fin k → ℝ)).1), (x : E × (Fin k → ℝ)).2)
    rw [hjj, A.apply_symm_apply, smul_zero]

end SignedCompat

/-! ### The orientation `e ∧ o` at a point of `[0, 1] × X` -/

/-- A shortcut for the action of `ℝˣ` on the rays of a real module. -/
local instance (priority := 10000) rayUnitsMulActionIv {M : Type*} [AddCommMonoid M]
    [Module ℝ M] : MulAction ℝˣ (Module.Ray ℝ M) := inferInstance

section IvOr

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (b : Fin 1 → Bool) {t : Fin 1 → unitInterval}
  (ht : t ∈ (chart b).source)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

/-- **2021 Remark 6.6.19: the natural orientation of `f̂ = f̃ + S`** at `(t, x)`, with the 2021
convention `h̃ = e ∧ h`, `e` the standard direction of `[0, 1]`, read in the product chart
point `ivPt` at a point `(t, x)` of `[0, 1] × X`.  For an sc-Fredholm `f`, an
sc⁺-section `S` of `π*P` over `[0, 1] × X`, a smooth point `x` with `Lin(f, x)` nonempty and an
orientation `o` of `DET(f, x)`, there is exactly one orientation `ô` of `DET(f̂, (t, x))` with
`ô(L̂) = extConjDetFirst(o(L))` for **every** `L ∈ Lin(f, x)`: the orientation `h̃ = e ∧ h` of
`det(L̂)` orients `DET(f̂, (t, x))`, independently of the choice of `L`. -/
theorem existsUnique_ivOrFirst (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
        (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) :
    ∃! ô : (p.ivPt b ht q₀).Or
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)
        (theorem_3_1_18_preprint hfc hS),
      ∀ (L : ↥p.T →L[ℝ] ↥p.K) (hL : L ∈ p.linSet f),
        ô ⟨p.ivLin b ht q₀ L, p.ivLin_mem_linSet b ht q₀ hf hx hS hL⟩ =
          Module.Ray.map (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀)
            (p.isFredholm_of_mem_linSet hf L hL)
            ((p.ivPt b ht q₀).isFredholm_of_mem_linSet (theorem_3_1_18_preprint hfc hS) _
              (p.ivLin_mem_linSet b ht q₀ hf hx hS hL))) (o ⟨L, hL⟩) := by
  obtain ⟨L₀, hL₀⟩ := hne
  have : PreconnectedSpace (p.linSet f) :=
    isPreconnected_iff_preconnectedSpace.1 (p.convex_linSet hf).isPreconnected
  have : ContractibleSpace ((p.ivPt b ht q₀).linSet
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :=
    ((p.ivPt b ht q₀).convex_linSet (theorem_3_1_18_preprint hfc hS)).contractibleSpace
      ⟨_, p.ivLin_mem_linSet b ht q₀ hf hx hS hL₀⟩
  have : LocallyPathConnectedSpace ((p.ivPt b ht q₀).linSet
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :=
    ((p.ivPt b ht q₀).convex_linSet (theorem_3_1_18_preprint hfc hS)).locallyPathConnectedSpace
  exact existsUnique_extConjOrFirst (p.ivT b ht q₀) (p.ivK b ht q₀) (p.isFredholm_of_mem_linSet hf)
    ((p.ivPt b ht q₀).isFredholm_of_mem_linSet (theorem_3_1_18_preprint hfc hS))
    (fun L hL => p.ivLin_mem_linSet b ht q₀ hf hx hS hL) ⟨L₀, hL₀⟩ o

/-- **The product orientation of 2021 Remark 6.6.19** at `(t, x)` (`e` first): the orientation
`ô` of `DET(f̂, (t, x))` determined by `o` (`existsUnique_ivOrFirst`). -/
def ivOrFirst (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
        (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) :
    (p.ivPt b ht q₀).Or (sectionAdd (pullbackProj P Prod.snd) (cubeLift
        (n := 1) f hf.isScSmooth.1) S)
      (theorem_3_1_18_preprint hfc hS) :=
  (p.existsUnique_ivOrFirst b ht q₀ hf hfc hx hS hne o).exists.choose

/-- **`ivOrFirst` at `L̂`** is `h ↦ h̃ = e ∧ h` (`extConjDetFirst`) of `o(L)`, for every
`L ∈ Lin(f, x)`. -/
theorem ivOrFirst_apply (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
        (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) (L : ↥p.T →L[ℝ] ↥p.K)
    (hL : L ∈ p.linSet f) :
    p.ivOrFirst b ht q₀ hf hfc hx hS hne o
        ⟨p.ivLin b ht q₀ L, p.ivLin_mem_linSet b ht q₀ hf hx hS hL⟩ =
      Module.Ray.map (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀)
        (p.isFredholm_of_mem_linSet hf L hL)
        ((p.ivPt b ht q₀).isFredholm_of_mem_linSet (theorem_3_1_18_preprint hfc hS) _
          (p.ivLin_mem_linSet b ht q₀ hf hx hS hL))) (o ⟨L, hL⟩) :=
  (p.existsUnique_ivOrFirst b ht q₀ hf hfc hx hS hne o).exists.choose_spec L hL


/-- `Lin(f̃ + 0, (t, x)) = Lin(f̃, (t, x))`. -/
theorem linSet_cubeLift_add_zero (hf : B.IsScFredholmSection f) :
    (p.ivPt b ht q₀).linSet (sectionAdd (pullbackProj P Prod.snd)
        (cubeLift (n := 1) f hf.isScSmooth.1) (fiberZero (pullbackProj P Prod.snd))) =
      (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1) :=
  (p.ivPt b ht q₀).linSet_sectionAdd (isSection_pullbackLift _)
    (StrongBundle.isScPlusSection_fiberZero (B := ivBundle B))

/-- **`L̂ ∈ Lin(f̃, (t, x))`** for `L ∈ Lin(f, x)`. -/
theorem ivLin_mem_linSet_cubeLift (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) :
    p.ivLin b ht q₀ L ∈ (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1) :=
  p.linSet_cubeLift_add_zero b ht q₀ hf ▸ p.ivLin_mem_linSet b ht q₀ hf hx
    (StrongBundle.isScPlusSection_fiberZero (B := ivBundle B)) hL

/-- **The product orientation of `f̃(t, x) = f(x)`** at `(t, x)` (2021 Remark 6.6.19 for `s = 0`):
`ivOrFirst` for the zero section, read as an orientation of `DET(f̃, (t, x))`
(`Lin(f̃ + 0) = Lin(f̃)`). -/
def ivOrFirst₀ (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
        (hx : x ∈ PX.smoothSet)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) :
    (p.ivPt b ht q₀).Or (cubeLift (n := 1) f hf.isScSmooth.1) hfc :=
  (p.ivPt b ht q₀).orCongr (theorem_3_1_18_preprint hfc
      (StrongBundle.isScPlusSection_fiberZero (B := ivBundle B))) hfc
    (p.linSet_cubeLift_add_zero b ht q₀ hf)
    (p.ivOrFirst b ht q₀ hf hfc hx (StrongBundle.isScPlusSection_fiberZero (B := ivBundle B)) hne o)

/-- **`ivOrFirst₀` at `L̂`** is `h ↦ e ∧ h` of `o(L)`, for every `L ∈ Lin(f, x)`. -/
theorem ivOrFirst₀_apply (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
        (hx : x ∈ PX.smoothSet)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) (L : ↥p.T →L[ℝ] ↥p.K)
    (hL : L ∈ p.linSet f) :
    p.ivOrFirst₀ b ht q₀ hf hfc hx hne o
        ⟨p.ivLin b ht q₀ L, p.ivLin_mem_linSet_cubeLift b ht q₀ hf hx hL⟩ =
      Module.Ray.map (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀)
        (p.isFredholm_of_mem_linSet hf L hL)
        ((p.ivPt b ht q₀).isFredholm_of_mem_linSet hfc _
          (p.ivLin_mem_linSet_cubeLift b ht q₀ hf hx hL))) (o ⟨L, hL⟩) :=
  ((p.ivPt b ht q₀).orCongr_apply _ hfc (p.linSet_cubeLift_add_zero b ht q₀ hf) _
    (p.ivLin_mem_linSet_cubeLift b ht q₀ hf hx hL)).trans
    (p.ivOrFirst_apply b ht q₀ hf hfc hx
      (StrongBundle.isScPlusSection_fiberZero (B := ivBundle B)) hne o L hL)

/-- `(f̃ + S̃)'(t, x) = ((f + S)'(x))^`. -/
theorem stabT_ivPt (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1)) {S : X → Y}
        (hS : B.IsScPlusSection S)
    (hx0 : IsZeroAt P (sectionAdd P f S) x)
    (hS' : (ivBundle B).IsScPlusSection (cubeLift (n := 1) S hS.1))
    (hx0' : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) (cubeLift (n := 1) S hS.1)) (t, x)) :
    (p.ivPt b ht q₀).stabT hfc hS' hx0' = p.ivLin b ht q₀ (p.stabT hf hS hx0) := by
  refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
  rw [coe_stabT, sectionAdd_cubeLift]
  exact (p.linAt_ivPt_cubeLift b ht q₀ (hf.isScSmooth.sectionAdd hS) v).trans
    ((p.coe_stabT hf hS hx0 _).symm.trans
      (p.coe_ivLin_apply b ht q₀ (p.stabT hf hS hx0) v).symm)

/-- `φ̂` of the `t`-constant lifts is `ivStab φ`. -/
theorem stabPhi_ivPt {k : ℕ} (s : Fin k → X → Y) (hs : ∀ i, IsSection P (s i))
    (hs' : ∀ i, IsSection (pullbackProj P Prod.snd) (cubeLift (n := 1) (s i) (hs i))) :
    (p.ivPt b ht q₀).stabPhi (fun i => cubeLift (n := 1) (s i) (hs i)) hs' =
      p.ivStab b ht q₀ (p.stabPhi s hs) := by
  refine ContinuousLinearMap.ext fun μ => Subtype.ext ?_
  rw [coe_stabPhi]
  change _ = ((p.stabPhi s hs μ : ↥p.K) : p.c.F 0)
  rw [p.coe_stabPhi]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← p.principal_ivPt_cubeLift b ht q₀ (hs i)]
  rfl

/-- The inclusion `T_{(t, z)} → ℝ¹ × E₀`, with its target written as a product. -/
abbrev ivIncl : ↥(p.ivPt b ht q₀).T →L[ℝ] (Fin 1 → ℝ) × p.c.φ.model.E 0 :=
  (p.ivPt b ht q₀).T.subtypeL

theorem ivIncl_injective : Function.Injective (p.ivIncl b ht q₀) := Subtype.val_injective

/-- **The product orientation read in the stabilized kernels**: for `L ∈ Lin(f, x)` with a
stabilization `L ⊕ φ` onto and kernels `Λ_q`, `(ℝ × Λ)_q`, reading `ivOrFirst₀ o` at
`L̂ ⊕ φ̂` is `w ↦ ê ∧ J(w)` of reading `o` at `L ⊕ φ` (`stabRayEquiv_extConjDetFirst`,
`prodLineWedgeEquiv_compat`). The operators `T₁ = L̂`, `φ₁ = φ̂` enter through equations. -/
theorem stabRay_ivOrFirst₀_aux (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
        (hx : x ∈ PX.smoothSet)
    (o : p.Or f hf) {T : ↥p.T →L[ℝ] ↥p.K} (hT : T ∈ p.linSet f) {k : ℕ}
    (φ : (Fin k → ℝ) →L[ℝ] ↥p.K) (hs : Function.Surjective (T.coprod φ))
    {Q : Type*} [TopologicalSpace Q] (Λ : SubspaceFamily Q (p.c.φ.model.E 0 × (Fin k → ℝ)))
    (q : Q)
    (hL : Λ.L q = (LinearMap.ker ((T.coprod φ : _ →L[ℝ] ↥p.K) :
          ↥p.T × (Fin k → ℝ) →ₗ[ℝ] ↥p.K)).map
        (((p.T.subtypeL.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ))) :
          ↥p.T × (Fin k → ℝ) →L[ℝ] p.c.φ.model.E 0 × (Fin k → ℝ)) :
            ↥p.T × (Fin k → ℝ) →ₗ[ℝ] p.c.φ.model.E 0 × (Fin k → ℝ)))
    {T₁ : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K} (hT₁e : T₁ = p.ivLin b ht q₀ T)
    (hT₁ : T₁ ∈ (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    {φ₁ : (Fin k → ℝ) →L[ℝ] ↥(p.ivPt b ht q₀).K} (hφ₁e : φ₁ = p.ivStab b ht q₀ φ)
    (hs₁ : Function.Surjective (T₁.coprod φ₁))
    (hL' : Λ.prodLine.L q = (LinearMap.ker ((T₁.coprod φ₁ : _ →L[ℝ] ↥(p.ivPt b ht q₀).K) :
          ↥(p.ivPt b ht q₀).T × (Fin k → ℝ) →ₗ[ℝ] ↥(p.ivPt b ht q₀).K)).map
        ((((p.ivIncl b ht q₀).prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ))) :
          ↥(p.ivPt b ht q₀).T × (Fin k → ℝ) →L[ℝ]
            ((Fin 1 → ℝ) × p.c.φ.model.E 0) × (Fin k → ℝ)) :
            ↥(p.ivPt b ht q₀).T × (Fin k → ℝ) →ₗ[ℝ]
              ((Fin 1 → ℝ) × p.c.φ.model.E 0) × (Fin k → ℝ))) :
    ((((p.ivPt b ht q₀).orEquivRay hfc hT₁).trans (MulAction.toPerm (stabSign T₁))).trans
        (stabRayEquiv ((p.ivPt b ht q₀).isFredholm_of_mem_linSet hfc _ hT₁) hs₁
          (kerEquivMap (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hL')))
        (p.ivOrFirst₀ b ht q₀ hf hfc hx ⟨T, hT⟩ o) =
      Module.Ray.map (Λ.prodLineWedgeEquivS (ivSign b) (ivSign_ne_zero b) q)
        ((((p.orEquivRay hf hT).trans (MulAction.toPerm (stabSign T))).trans
          (stabRayEquiv (p.isFredholm_of_mem_linSet hf _ hT) hs
            (kerEquivMap p.T.subtypeL Subtype.val_injective hL))) o) := by
  subst hT₁e hφ₁e
  have hFr := p.isFredholm_of_mem_linSet hf _ hT
  have hFr' := (p.ivPt b ht q₀).isFredholm_of_mem_linSet hfc _ hT₁
  exact ray_trans_map_aux (p.orEquivRay hf hT) ((p.ivPt b ht q₀).orEquivRay hfc hT₁)
    (p.ivOrFirst₀ b ht q₀ hf hfc hx ⟨T, hT⟩)
    (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀) hFr hFr') (stabSign T)
    (stabSign (p.ivLin b ht q₀ T))
    (stabRayEquiv hFr hs (kerEquivMap p.T.subtypeL Subtype.val_injective hL))
    (stabRayEquiv hFr' hs₁ (kerEquivMap (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hL'))
    (Λ.prodLineWedgeEquivS (ivSign b) (ivSign_ne_zero b) q)
    (fun o' => p.ivOrFirst₀_apply b ht q₀ hf hfc hx ⟨T, hT⟩ o' T hT)
    (p.stabSign_ivLin b ht q₀ T)
    (stabRayEquiv_extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀)
      (p.ivStab_conj b ht q₀ φ) hFr hFr' hs hs₁
      (kerEquivMap p.T.subtypeL Subtype.val_injective hL)
      (kerEquivMap (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hL')
      (Λ.prodLineWedgeEquivS (ivSign b) (ivSign_ne_zero b) q)
      (prodLineWedgeEquivS_compat (ivSign b) (ivSign_ne_zero b) (p.ivT b ht q₀) (p.ivK b ht q₀) hFr
          (p.ivStab_conj b ht q₀ φ)
        p.T.subtypeL Subtype.val_injective (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀)
        (fun v => Prod.ext (by
          have h : ivSign b • ivSign b • Prod.fst (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) v.1 =
              Prod.fst (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) v.1 := by
            rw [smul_smul, ivSign_mul_self, one_smul]
          exact h.symm) rfl) Λ q hL hL')) o

end ChartPoint

end IvOr

/-! ### The stabilized kernels of `f̃` along a path of `[0, 1] × X` -/

section SignedKer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
  {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- **`ker(L̂ ⊕ φ̂)` read in `(ℝ¹ × V) × ℝᵏ`** is `{((σ, v), μ) | (v, μ) ∈ ker(L ⊕ φ)}`, for
inclusions `j' = (a · pr₂ A, j pr₁ A)` with a scalar `a ≠ 0` (`map_ker_extConjOp_eq` for
`a = 1`). -/
theorem map_ker_extConjOp_eq_of_smul (a : ℝ) (ha : a ≠ 0) (A : E' ≃L[ℝ] E × (Fin 1 → ℝ))
    (Γ : F' ≃L[ℝ] F) (T : E →L[ℝ] F)
    (φ : (Fin k → ℝ) →L[ℝ] F) (φ' : (Fin k → ℝ) →L[ℝ] F') (hφφ : ∀ μ, φ μ = Γ (φ' μ))
    (j : E →L[ℝ] V) (j' : E' →L[ℝ] (Fin 1 → ℝ) × V)
    (hj' : ∀ v, j' v = (a • (A v).2, j (A v).1)) :
    ((LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
        E × (Fin k → ℝ) →ₗ[ℝ] F)).map
      ((j.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : E × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ))).comap
        (prodLinePr V k : ((Fin 1 → ℝ) × V) × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ)) =
      (LinearMap.ker (((extConjOp A Γ T).coprod φ' : E' × (Fin k → ℝ) →L[ℝ] F') :
        E' × (Fin k → ℝ) →ₗ[ℝ] F')).map
      ((j'.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E' × (Fin k → ℝ) →L[ℝ] ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) :
          E' × (Fin k → ℝ) →ₗ[ℝ] ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) := by
  have hconj : ∀ u : E' × (Fin k → ℝ),
      Γ ((extConjOp A Γ T).coprod φ' u) = T (A u.1).1 + φ u.2 := fun u => by
    rw [ContinuousLinearMap.coprod_apply, map_add, ← extConjOp_conj, ← hφφ, extOp_apply]
  refine Submodule.ext fun w => ?_
  constructor
  · rintro ⟨u, hu, hue⟩
    have hu' : T u.1 + φ u.2 = 0 := hu
    have h1 : j u.1 = w.1.2 := congrArg Prod.fst hue
    have h2 : u.2 = w.2 := congrArg Prod.snd hue
    refine ⟨(A.symm (u.1, a⁻¹ • w.1.1), u.2), ?_, ?_⟩
    · change (extConjOp A Γ T).coprod φ' (A.symm (u.1, a⁻¹ • w.1.1), u.2) = 0
      apply Γ.injective
      rw [hconj, map_zero, A.apply_symm_apply]
      exact hu'
    · change ((j' (A.symm (u.1, a⁻¹ • w.1.1)), u.2) : ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) = w
      rw [hj', A.apply_symm_apply]
      refine Prod.ext (Prod.ext ?_ h1) h2
      change a • a⁻¹ • w.1.1 = w.1.1
      rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
  · rintro ⟨u, hu, rfl⟩
    have hu' : (extConjOp A Γ T).coprod φ' u = 0 := hu
    refine ⟨((A u.1).1, u.2), ?_, ?_⟩
    · change T (A u.1).1 + φ u.2 = 0
      rw [← hconj, hu', map_zero]
    · change ((j (A u.1).1, u.2) : V × (Fin k → ℝ)) = ((j' u.1).2, u.2)
      rw [hj']

end SignedKer

section IvKernels

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- The level-`1` point `(χ_b(t), z)` lifts the image of `(t, x)` in the product chart. -/
theorem ivChart_toBase (b : Fin 1 → Bool) {c : StrongBundleChart PX P} {x : X}
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (t : Fin 1 → unitInterval)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) :
    (ivChart b c q₀).φ.model.E.toBase 1 ((chart b t : Fin 1 → ℝ), z) =
      (ivChart b c q₀).φ (t, x) := by
  change ((rnSc 1).prod c.φ.model.E).toBase 1 ((chart b t : Fin 1 → ℝ), z) =
    (((chart b t : Fin 1 → ℝ), c.φ x) : (Fin 1 → ℝ) × c.φ.model.E 0)
  rw [ScBanach.prod_toBase, ScBanach.const_toBase, hz]

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- A level-`1` lift of a point of the product chart is `(χ_b(t), z)` for a lift `z` in `c`. -/
theorem ivChart_lift_eq (b : Fin 1 → Bool) {c : StrongBundleChart PX P} {x : X}
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (t : Fin 1 → unitInterval)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (z' : (ivChart b c q₀).φ.model.E 1)
    (hz' : (ivChart b c q₀).φ.model.E.toBase 1 z' = (ivChart b c q₀).φ (t, x)) :
    z' = ((chart b t : Fin 1 → ℝ), z) :=
  (ivChart b c q₀).φ.model.E.toBase_injective 1 (hz'.trans (ivChart_toBase b z hz t q₀).symm)

namespace IsStabKernels

variable {Q : Type*} [TopologicalSpace Q] {c : StrongBundleChart PX P} {hc : B.IsChart c}
  {y : Q → X} {hy : ∀ q, y q ∈ c.φ.source} {S : Q → X → Y} {k : ℕ} {s : Fin k → Q → X → Y}
  {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}

set_option maxHeartbeats 1600000 in
-- the chart point of the product chart at `(τ(q), y(q))` is unfolded in every field
/-- **The stabilized kernels of `f̃` along `q ↦ (τ(q), y(q))`**, `τ` with values in the domain
of the chart `χ_b` of `[0, 1]`, are `ℝ × Λ` in the product chart `χ_b × φ_c`, for the
`t`-constant lifts of the sections. -/
theorem ivLift (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f)
    (b : Fin 1 → Bool) (τ : Q → (Fin 1 → unitInterval)) (hτ : ∀ q, τ q ∈ (chart b).source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) :
    IsStabKernels (B := ivBundle B) (cubeLift (n := 1) f hf.isScSmooth.1)
      (ivChart b c q₀) (isChart_ivChart b hc q₀)
      (fun q => (τ q, y q)) (fun q => mem_ivChart_source q₀ (hy q) (hτ q))
      (fun q => cubeLift (n := 1) (S q) (hΛ.isScPlusSection q).1)
      (fun i q => cubeLift (n := 1) (s i q) (hΛ.isSection i q)) Λ.prodLine where
  isScPlusSection q := isScPlusSection_cubeLift (n := 1) (hΛ.isScPlusSection q)
  zero q := by
    rw [sectionAdd_cubeLift]
    exact (isZeroAt_iff_prodSlice (isSection_pullbackLift _) (τ q) (y q)).2 (hΛ.zero q)
  isSection i q := isSection_pullbackLift _
  exists_lift q := by
    obtain ⟨z, hz⟩ := hΛ.exists_lift q
    exact ⟨((chart b (τ q) : Fin 1 → ℝ), z), ivChart_toBase b z hz (τ q) q₀⟩
  spec q x hq hxc z' hz' T' hT' φ' hφ' := by
    subst hq
    obtain ⟨z, hz⟩ := hΛ.exists_lift q
    obtain rfl := ivChart_lift_eq b z hz (τ q) q₀ z' hz'
    let p := chartPt c hc (hy q) z hz
    set T := p.stabT hf (hΛ.isScPlusSection q) (hΛ.zero q) with hTdef
    set φ := p.stabPhi (fun i => s i q) (fun i => hΛ.isSection i q) with hφdef
    have hsp := hΛ.spec q rfl (hy q) z hz T (fun _ => rfl) φ (fun μ => p.coe_stabPhi _ _ μ)
    have hTeq : T' = p.ivLin b (hτ q) q₀ T := by
      refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
      refine (hT' v).trans ?_
      rw [sectionAdd_cubeLift]
      refine (p.linAt_ivPt_cubeLift b (hτ q) q₀
        (hf.isScSmooth.sectionAdd (hΛ.isScPlusSection q)) v).trans ?_
      exact (p.coe_ivLin_apply b (hτ q) q₀ T v).symm
    have hφeq : φ' = p.ivStab b (hτ q) q₀ φ := by
      refine ContinuousLinearMap.ext fun μ => Subtype.ext ?_
      refine (hφ' μ).trans ?_
      change _ = ((φ μ : ↥p.K) : c.F 0)
      rw [p.coe_stabPhi]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← p.principal_ivPt_cubeLift b (hτ q) q₀ (hΛ.isSection i q)]
      rfl
    subst hTeq hφeq
    refine ⟨p.surjective_coprod_ivLin b (hτ q) q₀ hsp.1, ?_⟩
    exact (congrArg (Submodule.comap (prodLinePr (c.φ.model.E 0) k :
        ((Fin 1 → ℝ) × c.φ.model.E 0) × (Fin k → ℝ) →ₗ[ℝ] c.φ.model.E 0 × (Fin k → ℝ)))
      hsp.2).trans (map_ker_extConjOp_eq_of_smul (ivSign b) (ivSign_ne_zero b)
        (p.ivT b (hτ q) q₀) (p.ivK b (hτ q) q₀) T φ
        (p.ivStab b (hτ q) q₀ φ) (p.ivStab_conj b (hτ q) q₀ φ) p.T.subtypeL
        (p.ivPt b (hτ q) q₀).T.subtypeL (fun v => Prod.ext (by
          have h : ivSign b • ivSign b • Prod.fst (α := Fin 1 → ℝ) (β := c.φ.model.E 0) v.1 =
              Prod.fst (α := Fin 1 → ℝ) (β := c.φ.model.E 0) v.1 := by
            rw [smul_smul, ivSign_mul_self, one_smul]
          exact h.symm) rfl))

end IsStabKernels

/-- **The orientation `e ∧ o` in the chart point of the product chart with a given lift**
`z' = (χ_b(t), z)`: `ivOrFirst₀` over `chartPt c hc hx z hz`. -/
def ivOrLift (b : Fin 1 → Bool) {c : StrongBundleChart PX P} (hc : B.IsChart c) {x : X}
    (hx : x ∈ c.φ.source) (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x)
    {t : Fin 1 → unitInterval} (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hxc : ((t, x) : (Fin 1 → unitInterval) × X) ∈ (ivChart b c q₀).φ.source)
    (z' : (ivChart b c q₀).φ.model.E 1)
    (hz' : (ivChart b c q₀).φ.model.E.toBase 1 z' = (ivChart b c q₀).φ (t, x))
    (hzz : z' = ((chart b t : Fin 1 → ℝ), z)) (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet)
    (hne : ((chartPt c hc hx z hz).linSet f).Nonempty) (o : (chartPt c hc hx z hz).Or f hf) :
    (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z' hz').Or
      (cubeLift (n := 1) f hf.isScSmooth.1) hfc := by
  subst hzz
  exact (chartPt c hc hx z hz).ivOrFirst₀ b ht q₀ hf hfc hxs hne o

namespace IsStabKernels

variable {Q : Type*} [TopologicalSpace Q] {c : StrongBundleChart PX P} {hc : B.IsChart c}
  {y : Q → X} {hy : ∀ q, y q ∈ c.φ.source} {S : Q → X → Y} {k : ℕ} {s : Fin k → Q → X → Y}
  {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}

/-- **The orientation `e ∧ o` read in `λ((ℝ × Λ)_q)`** is `w ↦ (± ê) ∧ J(w)` of the orientation
read in `λ(Λ_q)`, the sign that of the chart of `[0, 1]`. -/
theorem orRay_ivLift (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (b : Fin 1 → Bool) (τ : Q → (Fin 1 → unitInterval)) (hτ : ∀ q, τ q ∈ (chart b).source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) (q : Q)
    {x : X} (hq : y q = x) (hx : x ∈ PX.smoothSet) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ x) {t : Fin 1 → unitInterval} (hτt : τ q = t)
    (ht : t ∈ (chart b).source)
    (hq' : ((τ q, y q) : (Fin 1 → unitInterval) × X) = (t, x))
    (hx' : ((t, x) : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet)
    (z' : (ivChart b c q₀).φ.model.E 1)
    (hz' : (ivChart b c q₀).φ.model.E.toBase 1 z' = (ivChart b c q₀).φ (t, x))
    (hzz : z' = ((chart b t : Fin 1 → ℝ), z))
    (hne : ((chartPt c hc (hq ▸ hy q) z hz).linSet f).Nonempty)
    (o : (chartPt c hc (hq ▸ hy q) z hz).Or f hf) :
    (hΛ.ivLift hf b τ hτ q₀).orRay hfc q hq' hx' z' hz'
        (ivOrLift b hc (hq ▸ hy q) z hz ht q₀ (mem_ivChart_source q₀ (hq ▸ hy q) ht) z' hz' hzz
          hf hfc hx hne o) =
      Module.Ray.map (Λ.prodLineWedgeEquivS (ivSign b) (ivSign_ne_zero b) q)
        (hΛ.orRay hf q hq hx z hz o) := by
  subst hq hτt hzz
  let p := chartPt c hc (hy q) z hz
  have h0 : IsZeroAt P (sectionAdd P f (S q)) (y q) := hΛ.zero q
  have hT := p.stabT_mem_linSet hf (hΛ.isScPlusSection q) h0 hx
  have hsq := hΛ.spec q rfl (hy q) z hz (p.stabT hf (hΛ.isScPlusSection q) h0) (fun _ => rfl)
    (p.stabPhi (fun i => s i q) (fun i => hΛ.isSection i q)) (fun μ => p.coe_stabPhi _ _ μ)
  have hΛ' := hΛ.ivLift hf b τ hτ q₀
  have h0' := hΛ'.zero q
  have hT' := (p.ivPt b (hτ q) q₀).stabT_mem_linSet hfc (hΛ'.isScPlusSection q) h0' hx'
  have hsq' := hΛ'.spec q rfl (mem_ivChart_source q₀ (hy q) (hτ q))
    ((chart b (τ q) : Fin 1 → ℝ), z) hz'
    ((p.ivPt b (hτ q) q₀).stabT hfc (hΛ'.isScPlusSection q) h0') (fun _ => rfl)
    ((p.ivPt b (hτ q) q₀).stabPhi (fun i => cubeLift (n := 1) (s i q) (hΛ.isSection i q))
      (fun i => hΛ'.isSection i q)) (fun μ => (p.ivPt b (hτ q) q₀).coe_stabPhi _ _ μ)
  exact p.stabRay_ivOrFirst₀_aux b (hτ q) q₀ hf hfc hx o hT
    (p.stabPhi (fun i => s i q) (fun i => hΛ.isSection i q)) hsq.1 Λ q hsq.2
    (p.stabT_ivPt b (hτ q) q₀ hf hfc (hΛ.isScPlusSection q) h0 (hΛ'.isScPlusSection q) h0') hT'
    (p.stabPhi_ivPt b (hτ q) q₀ (fun i => s i q) (fun i => hΛ.isSection i q)
      (fun i => hΛ'.isSection i q)) hsq'.1 hsq'.2

end IsStabKernels

end IvKernels

/-! ### The lift of a push-forward -/

section IvPush

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] {f : X → Y}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]
  [∀ k : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin 1 → unitInterval) × X))]
  [∀ k : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P
    (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin 1 → unitInterval) × X) → (Fin 1 → unitInterval) × X))]

/-- **The orientation `e ∧ o` of `f̃` at `(t, x) ∈ [0, 1] × X`, read in the product chart**
`χ_b × φ_c` over a chart `c` of `P` at the smooth point `x`, `e` the standard direction of
`[0, 1]`. -/
def ivOrOf (b : Fin 1 → Bool) {c : StrongBundleChart PX P} (hc : B.IsChart c) {x : X}
    (hx : x ∈ c.φ.source) (hs : x ∈ PX.smoothSet) {t : Fin 1 → unitInterval}
    (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hne : ((chartPtOf c hc hx hs).linSet f).Nonempty) (o : (chartPtOf c hc hx hs).Or f hf) :
    (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
      (mem_ivChart_source q₀ hx ht) (prod_cube_mem_smoothSet_iff.2 hs)).Or
      (cubeLift (n := 1) f hf.isScSmooth.1) hfc :=
  ivOrLift b hc hx _ (exists_lift_of_smooth c hx hs).choose_spec ht q₀ _ _
    (exists_lift_of_smooth (ivChart b c q₀) (mem_ivChart_source q₀ hx ht)
      (prod_cube_mem_smoothSet_iff.2 hs)).choose_spec
    (ivChart_lift_eq b _ (exists_lift_of_smooth c hx hs).choose_spec t q₀ _
      (exists_lift_of_smooth (ivChart b c q₀) (mem_ivChart_source q₀ hx ht)
        (prod_cube_mem_smoothSet_iff.2 hs)).choose_spec) hf hfc hs hne o

/-- **A push-forward of `f` along `γ` lifts to a push-forward of `f̃` along `(τ, γ)`** in the
product chart `χ_b × φ_c` of `[0, 1] × X`, for `τ` with values in the domain of `χ_b` (the
boundary point included), and the lift carries `e ∧ o` to `e ∧` (push-forward of `o`) (2021
Remark 6.6.19: the convention is compatible with the choices made in the construction).  The
data are the lifts `cubeLiftProd` of the sections and the kernels `ℝ × Λ`; the sign of the
chart enters both ends in the same way. -/
theorem IsPush.ivLift {hf : B.IsScFredholmSection f}
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    {c : StrongBundleChart PX P}
    {hc : B.IsChart c} {γ : (Fin 1 → ℝ) → X}
    {hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source} {x₀ x₁ : X} {h₀ : γ (pt1 0) = x₀}
    {h₁ : γ (pt1 1) = x₁} {hx₀ : x₀ ∈ c.φ.source} {hx₁ : x₁ ∈ c.φ.source}
    {hs₀ : x₀ ∈ PX.smoothSet} {hs₁ : x₁ ∈ PX.smoothSet}
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf}
    (he : IsPush f hf c hc γ hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁ e) (b : Fin 1 → Bool)
    (τ : (Fin 1 → ℝ) → (Fin 1 → unitInterval))
    (hτ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, τ q ∈ (chart b).source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    {t₀ t₁ : Fin 1 → unitInterval}
    (ht₀ : τ (pt1 0) = t₀) (ht₁ : τ (pt1 1) = t₁)
    (hb₀ : t₀ ∈ (chart b).source) (hb₁ : t₁ ∈ (chart b).source)
    (hne₀ : ((chartPtOf c hc hx₀ hs₀).linSet f).Nonempty)
    (hne₁ : ((chartPtOf c hc hx₁ hs₁).linSet f).Nonempty) :
    ∃ e' : (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
          (mem_ivChart_source q₀ hx₀ hb₀) (prod_cube_mem_smoothSet_iff.2 hs₀)).Or
          (cubeLift (n := 1) f hf.isScSmooth.1) hfc ≃
        (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
          (mem_ivChart_source q₀ hx₁ hb₁) (prod_cube_mem_smoothSet_iff.2 hs₁)).Or
          (cubeLift (n := 1) f hf.isScSmooth.1) hfc,
      IsPush (B := ivBundle B) (cubeLift (n := 1) f hf.isScSmooth.1) hfc
        (ivChart b c q₀) (isChart_ivChart b hc q₀) (fun q => (τ q, γ q))
        (fun q hq => mem_ivChart_source q₀ (hγ q hq) (hτ q hq))
        (Prod.ext ht₀ h₀ : ((τ (pt1 0), γ (pt1 0)) : (Fin 1 → unitInterval) × X) = (t₀, x₀))
        (Prod.ext ht₁ h₁ : ((τ (pt1 1), γ (pt1 1)) : (Fin 1 → unitInterval) × X) = (t₁, x₁))
        (mem_ivChart_source q₀ hx₀ hb₀) (mem_ivChart_source q₀ hx₁ hb₁)
        (prod_cube_mem_smoothSet_iff.2 hs₀) (prod_cube_mem_smoothSet_iff.2 hs₁) e' ∧
      ∀ o, e' (ivOrOf b hc hx₀ hs₀ hb₀ q₀ hf hfc hne₀ o) =
        ivOrOf b hc hx₁ hs₁ hb₁ q₀ hf hfc hne₁ (e o) := by
  obtain ⟨S, hS, hz, k, s, hs, Λ, hΛ, rfl⟩ := he
  have hΛ' := hΛ.ivLift hf b (fun q : Icc (0 : Fin 1 → ℝ) 1 => τ q) (fun q => hτ q q.2) q₀
  have hx₀' : ((t₀, x₀) : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    prod_cube_mem_smoothSet_iff.2 hs₀
  have hx₁' : ((t₁, x₁) : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    prod_cube_mem_smoothSet_iff.2 hs₁
  have hl₀ := (exists_lift_of_smooth c hx₀ hs₀).choose_spec
  have hl₁ := (exists_lift_of_smooth c hx₁ hs₁).choose_spec
  have hl₀' := (exists_lift_of_smooth (ivChart b c q₀) (mem_ivChart_source q₀ hx₀ hb₀)
    hx₀').choose_spec
  have hl₁' := (exists_lift_of_smooth (ivChart b c q₀) (mem_ivChart_source q₀ hx₁ hb₁)
    hx₁').choose_spec
  refine ⟨hΛ'.push hfc iccZero iccOne (Prod.ext ht₀ h₀) (Prod.ext ht₁ h₁) hx₀' hx₁' _ hl₀'
      _ hl₁',
    ⟨cubeLiftProd (n := 1) S hS.1, isScPlusSection_cubeLiftProd hS, ?_, k,
      fun i => cubeLiftProd (n := 1) (s i) (hs i).1,
      fun i => isScPlusSection_cubeLiftProd (hs i), Λ.prodLine, hΛ', rfl⟩, fun o => ?_⟩
  · refine hz.mono fun q hq => ?_
    have h1 := (isZeroAt_pullback_iff_pullbackSlice
      ((isSection_pullbackLift _).sectionAdd hS.1) q (γ q)).1 hq
    rw [pullbackSlice_sectionAdd_paramLift hf.isScSmooth.1 hS.1] at h1
    refine (isZeroAt_pullback_iff_pullbackSlice
      ((isSection_pullbackLift _).sectionAdd (isSection_cubeLiftProd S hS.1)) q (τ q, γ q)).2 ?_
    rw [pullbackSlice_sectionAdd_paramLift (isSection_pullbackLift _)
      (isSection_cubeLiftProd S hS.1), pullbackSlice_cubeLiftProd,
      sectionAdd_cubeLift hf.isScSmooth.1 (hS.1.pullbackSlice q)]
    exact (isZeroAt_iff_prodSlice (isSection_pullbackLift _) (τ q) (γ q)).2 h1
  · have ha := hΛ.orRay_ivLift hf hfc b (fun q : Icc (0 : Fin 1 → ℝ) 1 => τ q)
      (fun q => hτ q q.2) q₀ iccZero h₀ hs₀
      _ hl₀ ht₀ hb₀ (Prod.ext ht₀ h₀) hx₀' _ hl₀' (ivChart_lift_eq b _ hl₀ t₀ q₀ _ hl₀') hne₀ o
    have hb := hΛ.orRay_ivLift hf hfc b (fun q : Icc (0 : Fin 1 → ℝ) 1 => τ q)
      (fun q => hτ q q.2) q₀ iccOne h₁ hs₁
      _ hl₁ ht₁ hb₁ (Prod.ext ht₁ h₁) hx₁' _ hl₁' (ivChart_lift_eq b _ hl₁ t₁ q₀ _ hl₁') hne₁
      (hΛ.push hf iccZero iccOne h₀ h₁ hs₀ hs₁ _ hl₀ _ hl₁ o)
    have hcont := equiv_trans_trans_symm_apply
      (DFunLike.congr_fun (hΛ.push_eq_orRay hf iccZero iccOne h₀ h₁ hs₀ hs₁ _ hl₀ _ hl₁) o).symm
    have key : Λ.prodLine.contEquiv iccZero iccOne
        ((hΛ'.orRay hfc iccZero (Prod.ext ht₀ h₀) hx₀' _ hl₀')
          (ivOrOf b hc hx₀ hs₀ hb₀ q₀ hf hfc hne₀ o)) =
        (hΛ'.orRay hfc iccOne (Prod.ext ht₁ h₁) hx₁' _ hl₁')
          (ivOrOf b hc hx₁ hs₁ hb₁ q₀ hf hfc hne₁
            (hΛ.push hf iccZero iccOne h₀ h₁ hs₀ hs₁ _ hl₀ _ hl₁ o)) :=
      ((congrArg (Λ.prodLine.cont iccZero iccOne) ha).trans
        (Λ.cont_prodLineS (ivSign b) (ivSign_ne_zero b) iccZero iccOne _)).trans
        ((congrArg (Module.Ray.map
          (Λ.prodLineWedgeEquivS (ivSign b) (ivSign_ne_zero b) iccOne)) hcont).trans hb.symm)
    have hp := hΛ'.push_eq_orRay hfc iccZero iccOne (Prod.ext ht₀ h₀)
      (Prod.ext ht₁ h₁) hx₀' hx₁' _ hl₀' _ hl₁'
    rw [hp]
    exact equiv_trans_trans_symm_apply_of key

end IvPush

end Polyfold
