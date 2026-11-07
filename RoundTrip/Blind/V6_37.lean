import Polyfold
/-! Blind formalization of V6_37 (the text's §6.5: `F`, p. 221; `F_t`, `L_t` and (96),
pp. 222–223).

Text: `F_t(y, λ) = F(t, y, λ)` on `X × ℝᵏ`, `L_t = ker F_t'(φ(t), 0)`, and the exact sequence
(96) relates `ker((f − s(·,t))'(φ(t)))`, `ker F_t'(φ(t), 0)`, `ℝᵏ` and
`Y_{φ(t)}/R((f − s(·,t))'(φ(t)))`.

Choices:
- The item is mostly definitions (`F_t`, `L_t`); the exactness of (96) is the item V6_38.  What
  (96) presupposes, and what B states, is the description of `F_t'(φ(t), 0)` in the product chart:
  on `T_{(0,z)}(ℝᵏ × O) = ℝᵏ × T_zO` it is `(λ, v) ↦ (f − s(·,t))'(φ(t)) v + Σ λᵢ sᵢ(φ(t), t)`.
  This is what makes `j(v) = (v, 0)` and `p(v, λ) = λ` maps into and out of
  `L_t = ker F_t'(φ(t), 0)`, so `L_t` is then the kernel of `T ⊕ Φ` as used in V6_38.
- Setting, context and encodings as in `RoundTrip/Blind/V6_33.lean` (prelude of
  `RoundTrip/Blind/V6_32.lean` copied): `X Y : Type`, `Bd : StrongBundle PX P`, `f` an
  sc-Fredholm section (`IsSection P f` added, as in V6_33); `U` as in Proposition 6.28, `φ` an
  sc-smooth path in `U`, `s` as in 6.28 (3), `s₁, …, s_k` any sc⁺-sections over `[0, 1] × U` (the
  formula does not use (P)); `t ∈ [0, 1] ⊆ ℝ¹`.  `F_t` is `Ft` of V6_33 (the project's
  `paramSection` of `f − s(·, t)` and the slices `sᵢ(·, t)`, a section of `π*P → ℝᵏ × X`;
  `F(t, ·) = F_t` holds by definition there, so it is not restated).
- Charts: B quantifies over all chart points `p : ChartPoint Bd (φ(t))` (chart of the atlas,
  level-`1` lift `z` of `φ(φ(t))`).  The product chart of `π*P` at `(0, φ(t))` is the project's
  `(PullbackChartData.ofProd p.c 0).toChart q₀` (vocabulary: `ψ = (r ↦ r − r₀) × φ` with
  retraction `1 × r`; `q₀` only the junk value of the inverse, quantified over), with the lift
  `(0, z)` (its level-`1` model space is `ℝᵏ × E₁` by definition).
- Linearizations are the project's `linAt` (`D(ĝ ∘ r)(z)` on `T_zO = rangeS(Dr(z))`):
  `T = (f − s(·,t))'(φ(t))` in the chart of `p`, `F_t'(φ(t), 0)` in the product chart, and
  `Φ(λ) = Σ λᵢ sᵢ(φ(t), t)` is the project's `ChartPoint.stabPhi` (checked with `#print`:
  `Σ λᵢ ŝᵢ(φ(x))`), included into `F`.
- "`T(ℝᵏ × O) = ℝᵏ × T_zO`": B asserts a topological linear isomorphism `e` from the tangent
  space of the product chart onto `ℝᵏ × T_zO` which is the identity on coordinates, and the
  formula `F_t'(w) = T (e w).2 + Φ (e w).1`.
- Nothing looks false to me.
-/
namespace RoundTrip.V6_37
open Polyfold

/-- `[0, 1] ⊆ ℝ¹`. -/
def I1 : Set (Fin 1 → ℝ) := Set.Icc 0 1

section
variable {X : Type} {Y : Type} {P : Y → X}

/-- The slice `s(·, t)` of a section of `π*P → ℝⁿ × X` is a section of `P`. -/
theorem isSection_slice {n : ℕ}
    (s : (Fin n → ℝ) × X → ↥(pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)))
    (hs : IsSection (pullbackProj P Prod.snd) s) (t : Fin n → ℝ) :
    IsSection P (pullbackSlice s t) := by
  intro y
  have h1 : P (s (t, y)).1.2 = (s (t, y)).1.1.2 := (s (t, y)).2
  have h2 : (s (t, y)).1.1 = (t, y) := hs (t, y)
  change P (s (t, y)).1.2 = y
  rw [h1, h2]

/-- `f − g` is a section if `f` and `g` are. -/
theorem isSection_sectionDiff [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {f g : X → Y} (hf : IsSection P f) (hg : IsSection P g) :
    IsSection P (sectionDiff P f g) := by
  intro y
  have hg' : P (sectionSmul P (fun _ => (-1 : ℝ)) g y) = y := by
    unfold sectionSmul
    rw [dif_pos (hg y)]
    exact ((-1 : ℝ) • (⟨g y, hg y⟩ : ↥(P ⁻¹' {y}))).2
  unfold sectionDiff sectionAdd
  rw [dif_pos (And.intro (hf y) hg')]
  exact ((⟨f y, hf y⟩ : ↥(P ⁻¹' {y})) + ⟨_, hg'⟩).2

end

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace ↥W]
  [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace
    ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
      (Subtype.val : W → (Fin 1 → ℝ) × X))]

/-- A (set-theoretic) section candidate of `π*P → ℝ¹ × X`. -/
abbrev Sec1 (P : Y → X) : Type :=
  (Fin 1 → ℝ) × X → ↥(pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- `s` is a section of `π*P` which is an sc⁺-section over the open set `W ⊆ ℝ¹ × X`. -/
def IsScPlusOn (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (W : Set ((Fin 1 → ℝ) × X))
    (s : Sec1 P) : Prop :=
  ∃ (hW : IsOpen W) (hne : Nonempty ↥W) (hs : IsSection (pullbackProj P Prod.snd) s),
    letI := hne
    ((Bd.pullback hπ).restrictOpen hW).IsScPlusSection
      (restrictSection (pullbackProj P Prod.snd) W s hs)

/-- `s` is an sc⁺-section over (an open neighbourhood of) `A ⊆ ℝ¹ × X`. -/
def IsScPlusNear (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (A : Set ((Fin 1 → ℝ) × X))
    (s : Sec1 P) : Prop :=
  ∃ W, A ⊆ W ∧ IsScPlusOn Bd hπ W s

/-- `φ : ℝ¹ → X` is an sc-smooth path on `[0, 1]`. -/
def IsScPathOn (PX : MPolyfold X) (φ : (Fin 1 → ℝ) → X) : Prop :=
  ∃ V, I1 ⊆ V ∧ (rnPolyfold 1).IsScSmoothOn PX φ V

/-- (1) `U` is sc-smoothly contractible. -/
def IsScContractible (PX : MPolyfold X) (U : Set X) : Prop :=
  ∃ (H : (Fin 1 → ℝ) × X → X) (y₀ : X),
    (∃ W, I1 ×ˢ U ⊆ W ∧ ((rnPolyfold 1).prod PX).IsScSmoothOn PX H W) ∧
    (∀ t ∈ I1, ∀ y ∈ U, H (t, y) ∈ U) ∧ (∀ y ∈ U, H (pt1 1, y) = y) ∧
    (∀ y ∈ U, H (pt1 0, y) = y₀)

/-- (3) along every sc-smooth path in `U` there is an sc⁺-section `s` with
`s(φ(t), t) = f(φ(t))`. -/
def HasPathSections (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (f : X → Y) (U : Set X) : Prop :=
  ∀ φ : (Fin 1 → ℝ) → X, IsScPathOn PX φ → (∀ t ∈ I1, φ t ∈ U) →
    ∃ s : Sec1 P, IsScPlusNear Bd hπ (I1 ×ˢ U) s ∧ ∀ t ∈ I1, pullbackSlice s t (φ t) = f (φ t)

/-- (4) sc⁺-sections over `[0, 1] × U` through every smooth fibre point over `[0, 1] × U_∞`. -/
def HasPointSections (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (U : Set X) : Prop :=
  ∀ t₀ ∈ I1, ∀ y₀ ∈ U ∩ PX.smoothSet, ∀ e₀ ∈ Bd.toMPolyfold0.smoothSet, P e₀ = y₀ →
    ∃ q : Sec1 P, IsScPlusNear Bd hπ (I1 ×ˢ U) q ∧ pullbackSlice q t₀ y₀ = e₀

/-- The properties (1)–(4) of Proposition 6.28 for the open neighbourhood `U` of `x`. -/
def IsNbhd628 (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (f : X → Y) (x : X)
    (U : Set X) : Prop :=
  IsOpen U ∧ x ∈ U ∧ IsScContractible PX U ∧
    IsCompact {y | y ∈ closure U ∧ IsZeroAt P f y} ∧
    HasPathSections Bd hπ f U ∧ HasPointSections Bd hπ U

/-- `F_t(λ, y) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)`, a section of `π*P → ℝᵏ × X`. -/
noncomputable def Ft {k : ℕ} (f : X → Y) (hf : IsSection P f) (s : Sec1 P)
    (hs : IsSection (pullbackProj P Prod.snd) s) (σ : Fin k → Sec1 P)
    (hσ : ∀ i, IsSection (pullbackProj P Prod.snd) (σ i)) (t : Fin 1 → ℝ) :
    (Fin k → ℝ) × X → ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X)) :=
  paramSection (sectionDiff P f (pullbackSlice s t))
    (isSection_sectionDiff hf (isSection_slice s hs t))
    (fun i => pullbackSlice (σ i) t) (fun i => isSection_slice (σ i) (hσ i) t)

/-- The product chart `(λ, y) ↦ (λ, φ(y))` of `π*P → ℝᵏ × X` at `(0, x)`, built from the strong
bundle chart of `p` (the project's `PullbackChartData.ofProd` centred at `r₀ = 0`; `q₀` is the
junk value of its inverse). -/
noncomputable abbrev prodChart {Bd : StrongBundle PX P} {x : X} (p : ChartPoint Bd x) (k : ℕ)
    (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))) :
    StrongBundleChart ((rnPolyfold k).prod PX) (pullbackProj P Prod.snd) :=
  (PullbackChartData.ofProd (n := k) p.c 0).toChart q₀

/-- The level-`1` lift `(0, z)` of `(0, φ(x))` in the product chart. -/
def zProd {Bd : StrongBundle PX P} {x : X} (p : ChartPoint Bd x) (k : ℕ)
    (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))) :
    (prodChart p k q₀).φ.model.E.lvl 1 :=
  show (Fin k → ℝ) × p.c.φ.model.E.lvl 1 from ((0 : Fin k → ℝ), p.z)

/-- The tangent space `T_{(0,z)}(ℝᵏ × O)` of the product chart. -/
noncomputable abbrev TProd {Bd : StrongBundle PX P} {x : X} (p : ChartPoint Bd x) (k : ℕ)
    (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))) :
    Submodule ℝ ((prodChart p k q₀).φ.model.E.lvl 0) :=
  rangeS (scDeriv (prodChart p k q₀).U (StrongRetr.r (prodChart p k q₀).R) (zProd p k q₀))

end

/-- §6.5: `F_t(λ, y) = F(t, λ, y)`, and in the product chart its linearization at `(0, φ(t))` is
`(λ, v) ↦ (f − s(·, t))'(φ(t)) v + Σ λᵢ sᵢ(φ(t), t)` on `T(ℝᵏ × O) = ℝᵏ × T_zO`, so that
`L_t = ker F_t'(0, φ(t))` is the middle term of (96). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace ↥W]
    [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace
      ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (Subtype.val : W → (Fin 1 → ℝ) × X))]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : IsSection P f), Bd.IsScFredholmSection f →
    ∀ (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd),
    -- `U` as in Proposition 6.28, `φ` an sc-smooth path in `U`, `s` as in (3), `sᵢ` sc⁺
    ∀ (x : X) (U : Set X), x ∈ PX.smoothSet → IsNbhd628 Bd hπ f x U →
    ∀ φ : (Fin 1 → ℝ) → X, IsScPathOn PX φ → (∀ t ∈ I1, φ t ∈ U) →
    ∀ (s : Sec1 P) (hs : IsSection (pullbackProj P Prod.snd) s),
      IsScPlusNear Bd hπ (I1 ×ˢ U) s → (∀ t ∈ I1, pullbackSlice s t (φ t) = f (φ t)) →
    ∀ (k : ℕ) (σ : Fin k → Sec1 P) (hσ : ∀ i, IsSection (pullbackProj P Prod.snd) (σ i)),
      (∀ i, IsScPlusNear Bd hπ (I1 ×ˢ U) (σ i)) →
    -- at `t ∈ [0, 1]`, in a chart point `p` at `φ(t)` and the product chart built from it
    ∀ t ∈ I1, ∀ (p : ChartPoint Bd (φ t))
      (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))),
      let T : ↥p.T →L[ℝ] p.c.F.lvl 0 :=
        linAt p.c.U p.c.R (p.c.principal (sectionDiff P f (pullbackSlice s t))) p.z
      let Φ : (Fin k → ℝ) →L[ℝ] p.c.F.lvl 0 :=
        p.K.subtypeL ∘L p.stabPhi (fun i => pullbackSlice (σ i) t)
          (fun i => isSection_slice (σ i) (hσ i) t)
      let c' := prodChart p k q₀
      let Lt : ↥(TProd p k q₀) →L[ℝ] p.c.F.lvl 0 :=
        linAt c'.U c'.R (c'.principal (Ft f hf s hs σ hσ t)) (zProd p k q₀)
      ∃ e : ↥(TProd p k q₀) ≃L[ℝ] (Fin k → ℝ) × ↥p.T,
        -- `e` is the coordinate identification `T(ℝᵏ × O) = ℝᵏ × T_zO`
        (∀ w : ↥(TProd p k q₀),
          (e w).1 = Prod.fst (α := Fin k → ℝ) (β := p.c.φ.model.E.lvl 0)
            (w : c'.φ.model.E.lvl 0) ∧
          ((e w).2 : p.c.φ.model.E.lvl 0) = Prod.snd (α := Fin k → ℝ)
            (β := p.c.φ.model.E.lvl 0) (w : c'.φ.model.E.lvl 0)) ∧
        -- `F_t'(0, φ(t)) (λ, v) = (f − s(·, t))'(φ(t)) v + Σ λᵢ sᵢ(φ(t), t)`
        ∀ w : ↥(TProd p k q₀), Lt w = T (e w).2 + Φ (e w).1

end RoundTrip.V6_37
