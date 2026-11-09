import Polyfold.Chapter6.StabKernelsExist
import Polyfold.Chapter6.FamilySections
import Polyfold.Chapter6.ScPaths

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 222–224: the **push-forward `o ↦ φ_* o` along an sc-smooth path** with its choices (the
sections `s(·, t)` and `s₁, …, s_k` with property (P)) *(book 2017: §6.5, after Lemma 6.14; see
`BookConcordance.md`)*.

# Push-forward data along paths

## The text, paraphrased

Along an sc-smooth path `φ` choose an sc⁺-section `s(·, t)` with `s(φ(t), t) = f(φ(t))` and
sc⁺-sections `s₁, …, s_k` with property (P) of Lemma 6.6.4 (preprint 6.29); the kernels `L_t` form a vector bundle
over `[0, 1]`, and `o₁ = φ_* o₀` is obtained from `Φ_{E₀}`, continuation and `Φ_{E₁}⁻¹`.

## What is formalized

* `chartPtOf c hc hx hxs`: the chart point of `c` at a smooth `x` (the level-`1` lift of `φ(x)` is
  unique); the cube `[0, 1]ⁿ` is contractible and locally path-connected.
* `IsPush f hf c hc γ … e`: **`e` is a push-forward along `γ`**: there are global sc⁺-sections
  `S`, `s₁, …, s_k` of `ℝ × X → Y` with `(f + S)(t, γ(t)) = 0` near `[0, 1]` and a family `Λ` of
  stabilized kernels for their slices along `γ` (`IsStabKernels`) with `e = Λ.push`.
* `IsPush.split`: a push-forward along `γ` is the composite of push-forwards along the two halves.
* `exists_isPush`: along every sc-smooth path in a set `W` with property (3) of Proposition 6.6.3 (preprint 6.28)
  there is a push-forward (Lemma 6.6.4 (preprint 6.29) and `exists_isStabKernels`).
* Helpers for `IsPush.split`: `isZeroAt_sectionAdd_reparamSection` (the zeros of `f̃ + S(g(·), ·)`),
  `IsStabKernels.push_eq_of_eq` (the push-forward depends on the end parameters only as points)
  and `isPush_reparam` (a datum along `γ` restricts along an affine `g` of `ℝ¹` with
  `g([0, 1]) ⊆ [0, 1]` to one along `γ ∘ g`, with the push-forward from `g(0)` to `g(1)`).

## Reading

The sections of the text, over `U × [0, 1]`, are global sc⁺-sections of the pull-back bundle over
`ℝ × X` (as in Proposition 6.6.3 (preprint 6.28)); the text's `f − s` is `f + S`.  Property (P) is used only to
construct a push-forward (`exists_isPush`); a datum of `IsPush` carries the family `Λ` of kernels
instead, which is what the construction uses.  Push-forwards are read in one chart `c` (`Or` of
`chartPtOf`).
-/

open Module Bundle Topology Set Filter

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### The cube -/

instance (n : ℕ) : ContractibleSpace (Icc (0 : Fin n → ℝ) 1) :=
  (convex_Icc (0 : Fin n → ℝ) 1).contractibleSpace ⟨0, left_mem_Icc.2 zero_le_one⟩

instance (n : ℕ) : LocallyPathConnectedSpace (Icc (0 : Fin n → ℝ) 1) :=
  (convex_Icc (0 : Fin n → ℝ) 1).locallyPathConnectedSpace

theorem pt1_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : pt1 t ∈ Icc (0 : Fin 1 → ℝ) 1 :=
  ⟨fun _ => ht.1, fun _ => ht.2⟩

/-! ### Chart points at smooth points -/

-- the statement keeps the instances of the section; the proof does not use those of `Y`
set_option linter.unusedSectionVars false in
/-- A smooth point in the domain of a chart has a level-`1` lift of its image. -/
theorem exists_lift_of_smooth (c : StrongBundleChart PX P) {x : X} (hx : x ∈ c.φ.source)
    (hxs : x ∈ PX.smoothSet) : ∃ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ x :=
  (PX.mem_levelSet_iff c.isChart hx).1 (mem_iInter.1 hxs 1)

/-- **The chart point of `c` at a smooth point `x`**, with the level-`1` lift of `φ(x)` (unique,
`E₁ → E₀` being injective). -/
def chartPtOf (c : StrongBundleChart PX P) (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source)
    (hxs : x ∈ PX.smoothSet) : ChartPoint B x :=
  chartPt c hc hx (exists_lift_of_smooth c hx hxs).choose
    (exists_lift_of_smooth c hx hxs).choose_spec

/-! ### Restriction of the data along affine maps -/

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The zeros of `f̃ + S(g(·), ·)` are those of `f̃ + S` moved by `g`. -/
theorem isZeroAt_sectionAdd_reparamSection (hf : IsSection P f) {m n : ℕ}
    (g : (Fin m → ℝ) → (Fin n → ℝ))
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (q : Fin m → ℝ) (y : X) :
    IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf) (reparamSection g S hS)) (q, y) ↔
      IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf) S) (g q, y) := by
  have h₁ : IsSection (pullbackProj P Prod.snd) (reparamSection g S hS) :=
    isSection_pullbackLift _
  have hL₁ : IsSection (pullbackProj P (Prod.snd : (Fin m → ℝ) × X → X)) (paramLift f hf) :=
    isSection_pullbackLift _
  have hL₂ : IsSection (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) (paramLift f hf) :=
    isSection_pullbackLift _
  rw [isZeroAt_pullback_iff_pullbackSlice (hL₁.sectionAdd h₁),
    isZeroAt_pullback_iff_pullbackSlice (hL₂.sectionAdd hS),
    pullbackSlice_sectionAdd_paramLift hf h₁, pullbackSlice_sectionAdd_paramLift hf hS]
  rfl

namespace IsStabKernels

variable {Q : Type*} [TopologicalSpace Q] [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]
  {c : StrongBundleChart PX P} {hc : B.IsChart c} {y : Q → X} {hy : ∀ q, y q ∈ c.φ.source}
  {S : Q → X → Y} {k : ℕ} {s : Fin k → Q → X → Y}
  {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}

/-- The push-forward from `a` to `b` depends on the parameters `a`, `b` only as points. -/
theorem push_eq_of_eq (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f)
    {a a' b b' : Q} (haa : a = a') (hbb : b = b') {x₀ x₁ : X} (ha : y a = x₀) (hb : y b = x₁)
    (ha' : y a' = x₀) (hb' : y b' = x₁) (hx₀ : x₀ ∈ PX.smoothSet) (hx₁ : x₁ ∈ PX.smoothSet)
    (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁) :
    hΛ.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ =
      hΛ.push hf a' b' ha' hb' hx₀ hx₁ z₀ hz₀ z₁ hz₁ := by
  subst haa hbb
  rfl

end IsStabKernels

/-! ### Push-forwards along paths -/

section Push

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

variable (f) in
/-- **`e` is a push-forward along `γ`** (pp. 222–224): there are global sc⁺-sections `S` and
`s₁, …, s_k` of `ℝ × X → Y` with `(f + S)(t, γ(t)) = 0` for `t` near `[0, 1]` (the text's
`f − s(·, t)`), and a family `Λ` of stabilized kernels of the slices `S(t, ·)`, `sᵢ(t, ·)` along
`γ`, read in the chart `c`, with `e = Λ.push` from `t = 0` to `t = 1`. -/
def IsPush (hf : B.IsScFredholmSection f) (c : StrongBundleChart PX P) (hc : B.IsChart c)
    (γ : (Fin 1 → ℝ) → X) (hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet)
    (e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf) : Prop :=
  ∃ (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (_ : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (_ : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin 1 → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, γ q))
    (k : ℕ) (s : Fin k → (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (_ : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection (s i))
    (Λ : SubspaceFamily (Icc (0 : Fin 1 → ℝ) 1) (c.φ.model.E 0 × (Fin k → ℝ)))
    (hΛ : IsStabKernels f c hc (fun q : Icc (0 : Fin 1 → ℝ) 1 => γ q) (fun q => hγ q q.2)
      (fun q => pullbackSlice S q) (fun i q => pullbackSlice (s i) q) Λ),
    e = hΛ.push hf ⟨pt1 0, pt1_mem_Icc (left_mem_Icc.2 zero_le_one)⟩
      ⟨pt1 1, pt1_mem_Icc (right_mem_Icc.2 zero_le_one)⟩ h₀ h₁ hs₀ hs₁
      (exists_lift_of_smooth c hx₀ hs₀).choose (exists_lift_of_smooth c hx₀ hs₀).choose_spec
      (exists_lift_of_smooth c hx₁ hs₁).choose (exists_lift_of_smooth c hx₁ hs₁).choose_spec

/-- **Restriction of a push-forward datum along an affine map** `g` of `ℝ¹` with
`g([0, 1]) ⊆ [0, 1]`: the push-forward along `γ` from `g(0)` to `g(1)` is a push-forward along
`γ ∘ g` (`reparamSection`, `IsScPlusSection.reparam`, `IsStabKernels.comp`, `push_comp`). -/
theorem isPush_reparam {hf : B.IsScFredholmSection f} {c : StrongBundleChart PX P}
    {hc : B.IsChart c} {γ : (Fin 1 → ℝ) → X} {hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source}
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin 1 → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, γ q))
    {k : ℕ} {s : Fin k → (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection (s i))
    {Λ : SubspaceFamily (Icc (0 : Fin 1 → ℝ) 1) (c.φ.model.E 0 × (Fin k → ℝ))}
    (hΛ : IsStabKernels f c hc (fun q : Icc (0 : Fin 1 → ℝ) 1 => γ q) (fun q => hγ q q.2)
      (fun q => pullbackSlice S q) (fun i q => pullbackSlice (s i) q) Λ)
    (g : (Fin 1 → ℝ) → (Fin 1 → ℝ)) (A : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ)) (b : Fin 1 → ℝ)
    (hgA : ∀ q, g q = A q + b) (hg : MapsTo g (Icc 0 1) (Icc 0 1))
    (hγ' : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ (g q) ∈ c.φ.source) {x₀ x₁ : X}
    (h₀ : γ (g (pt1 0)) = x₀) (h₁ : γ (g (pt1 1)) = x₁) (hx₀ : x₀ ∈ c.φ.source)
    (hx₁ : x₁ ∈ c.φ.source) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    IsPush f hf c hc (fun q => γ (g q)) hγ' h₀ h₁ hx₀ hx₁ hs₀ hs₁
      (hΛ.push hf ⟨g (pt1 0), hg (pt1_mem_Icc (left_mem_Icc.2 zero_le_one))⟩
        ⟨g (pt1 1), hg (pt1_mem_Icc (right_mem_Icc.2 zero_le_one))⟩ h₀ h₁ hs₀ hs₁
        (exists_lift_of_smooth c hx₀ hs₀).choose (exists_lift_of_smooth c hx₀ hs₀).choose_spec
        (exists_lift_of_smooth c hx₁ hs₁).choose
        (exists_lift_of_smooth c hx₁ hs₁).choose_spec) := by
  have hgc : Continuous g := (A.continuous.add continuous_const).congr fun q => (hgA q).symm
  have hgfun : (fun q => A q + b) = g := funext fun q => (hgA q).symm
  let g' : C(Icc (0 : Fin 1 → ℝ) 1, Icc (0 : Fin 1 → ℝ) 1) :=
    ⟨fun q => ⟨g q, hg q.2⟩, (hgc.comp continuous_subtype_val).subtype_mk _⟩
  have hrep : ∀ {T : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
      (hT : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection T),
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection
        (reparamSection g T hT.1) := fun {T} hT => by
    rw [← hgfun]; exact hT.reparam A b
  refine ⟨reparamSection g S hS.1, hrep hS, ?_, k, fun i => reparamSection g (s i) (hs i).1,
    fun i => hrep (hs i), Λ.comp g', hΛ.comp g',
    (hΛ.push_comp g' hf ⟨pt1 0, pt1_mem_Icc (left_mem_Icc.2 zero_le_one)⟩
      ⟨pt1 1, pt1_mem_Icc (right_mem_Icc.2 zero_le_one)⟩ h₀ h₁ hs₀ hs₁ _ _ _ _).symm⟩
  exact ((hgc.tendsto_nhdsSet hg).eventually hz).mono fun q hq =>
    (isZeroAt_sectionAdd_reparamSection _ g hS.1 q _).2 hq

/-- **A push-forward along `γ` is the composite of push-forwards along its halves**
`s ↦ γ(s/2)` and `s ↦ γ((1 + s)/2)`, for a smooth midpoint `γ(1/2)` (restriction of the data along
the affine maps, `IsScPlusSection.reparam`, `IsStabKernels.comp`, `push_comp`, `push_trans`). -/
theorem IsPush.split {hf : B.IsScFredholmSection f} {c : StrongBundleChart PX P}
    {hc : B.IsChart c} {γ : (Fin 1 → ℝ) → X} {hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source}
    {x₀ x₂ : X} {h₀ : γ (pt1 0) = x₀} {h₂ : γ (pt1 1) = x₂} {hx₀ : x₀ ∈ c.φ.source}
    {hx₂ : x₂ ∈ c.φ.source} {hs₀ : x₀ ∈ PX.smoothSet} {hs₂ : x₂ ∈ PX.smoothSet}
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₂ hs₂).Or f hf}
    (he : IsPush f hf c hc γ hγ h₀ h₂ hx₀ hx₂ hs₀ hs₂ e) {x₁ : X}
    (hx₁ : x₁ ∈ c.φ.source) (hs₁ : x₁ ∈ PX.smoothSet)
    (hγ₁ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ (pt1 (q 0 / 2)) ∈ c.φ.source)
    (hγ₂ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ (pt1 ((1 + q 0) / 2)) ∈ c.φ.source)
    (h₀' : γ (pt1 ((pt1 0 : Fin 1 → ℝ) 0 / 2)) = x₀)
    (h₁' : γ (pt1 ((pt1 1 : Fin 1 → ℝ) 0 / 2)) = x₁)
    (h₁'' : γ (pt1 ((1 + (pt1 0 : Fin 1 → ℝ) 0) / 2)) = x₁)
    (h₂' : γ (pt1 ((1 + (pt1 1 : Fin 1 → ℝ) 0) / 2)) = x₂) :
    ∃ (e₁ : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf)
      (e₂ : (chartPtOf c hc hx₁ hs₁).Or f hf ≃ (chartPtOf c hc hx₂ hs₂).Or f hf),
      IsPush f hf c hc (fun q => γ (pt1 (q 0 / 2))) hγ₁ h₀' h₁' hx₀ hx₁ hs₀ hs₁ e₁ ∧
      IsPush f hf c hc (fun q => γ (pt1 ((1 + q 0) / 2))) hγ₂ h₁'' h₂' hx₁ hx₂ hs₁ hs₂ e₂ ∧
      e = e₁.trans e₂ := by
  obtain ⟨S, hS, hz, k, s, hs, Λ, hΛ, rfl⟩ := he
  set A : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) := (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ _ with hA
  have hA₁ : ∀ q : Fin 1 → ℝ, pt1 (q 0 / 2) = A q + 0 := fun q => funext fun i => by
    rw [Subsingleton.elim i 0]; simp [hA]; ring
  have hA₂ : ∀ q : Fin 1 → ℝ, pt1 ((1 + q 0) / 2) = A q + pt1 (1 / 2) := fun q =>
    funext fun i => by rw [Subsingleton.elim i 0]; simp [hA]; ring
  have hg₁ : MapsTo (fun q : Fin 1 → ℝ => pt1 (q 0 / 2)) (Icc 0 1) (Icc 0 1) := fun q hq => by
    have h0 : (0 : ℝ) ≤ q 0 := hq.1 0
    have h1 : q 0 ≤ 1 := hq.2 0
    exact pt1_mem_Icc ⟨by linarith, by linarith⟩
  have hg₂ : MapsTo (fun q : Fin 1 → ℝ => pt1 ((1 + q 0) / 2)) (Icc 0 1) (Icc 0 1) :=
    fun q hq => by
    have h0 : (0 : ℝ) ≤ q 0 := hq.1 0
    have h1 : q 0 ≤ 1 := hq.2 0
    exact pt1_mem_Icc ⟨by linarith, by linarith⟩
  refine ⟨?e₁, ?e₂, ?h₁, ?h₂, ?_⟩
  case h₁ =>
    exact isPush_reparam (hγ := hγ) hS hz hs hΛ (fun q => pt1 (q 0 / 2)) A 0 hA₁ hg₁ hγ₁ h₀' h₁'
      hx₀ hx₁ hs₀ hs₁
  case h₂ =>
    exact isPush_reparam (hγ := hγ) hS hz hs hΛ (fun q => pt1 ((1 + q 0) / 2)) A (pt1 (1 / 2))
      hA₂ hg₂ hγ₂ h₁'' h₂' hx₁ hx₂ hs₁ hs₂
  refine (hΛ.push_trans hf _
    ⟨_, hg₁ (pt1_mem_Icc (right_mem_Icc.2 zero_le_one))⟩ _ h₀ h₁' h₂ hs₀ hs₁ hs₂ _ _
    (exists_lift_of_smooth c hx₁ hs₁).choose (exists_lift_of_smooth c hx₁ hs₁).choose_spec
    _ _).trans (congrArg₂ Equiv.trans ?_ ?_)
  · exact hΛ.push_eq_of_eq hf (Subtype.ext (by simp)) rfl _ _ _ _ _ _ _ _ _ _
  · exact hΛ.push_eq_of_eq hf (Subtype.ext (by norm_num)) (Subtype.ext (by norm_num)) _ _ _ _
      _ _ _ _ _ _

variable [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

/-- **Existence of push-forwards**: along an sc-smooth path in a set `W` of the domain of a chart
for which property (3) of Proposition 6.6.3 (preprint 6.28) holds (for paths), there is a push-forward
(Lemma 6.6.4 (preprint 6.29), `exists_isStabKernels`). -/
theorem exists_isPush (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    {W : Set X} (hW : W ⊆ c.φ.source)
    (h3 : ∀ Φ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX Φ →
      (∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, Φ q ∈ W) →
      ∃ S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X),
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S ∧
        ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin 1 → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q))
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγW : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ W) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    ∃ e, IsPush f hf.toIsScFredholmSection c hc γ (fun q hq => hW (hγW q hq)) h₀ h₁ hx₀ hx₁ hs₀ hs₁
      e := by
  obtain ⟨S, hS, hz⟩ := h3 γ hγs hγW
  obtain ⟨k, s, hs, hP⟩ := lemma_6_6_4 hX hbump hf hγs hS hz
  obtain ⟨Λ, hΛ⟩ := exists_isStabKernels hf hγs hc (fun q hq => hW (hγW q hq)) hS hz hs hP
  exact ⟨_, S, hS, hz, k, s, hs, Λ, hΛ, rfl⟩

end Push

end Polyfold
