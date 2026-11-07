import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_46

/-! Round trip for V6_46 (sections over parameter families, pp. 224–226; Theorem 5.18's "adding
more sections, the properties will still hold").

A is the conjunction of the types of `pullbackSlice_reparamSection`,
`StrongBundle.isScPlusSection_of_local`, `StrongBundle.IsScPlusSection.reparam` (affine
reparametrization keeps sc⁺) and `StrongBundle.isGeneralPositionGerm_paramSection_of_comp`
(adding sections keeps general position), universes at `0`.  B is the conjunction of (1) linear
reparametrization keeps sc⁺, (2) slices of sc⁺-sections are sc⁺, (3) the convex combination over
the square is sc⁺, (4) appending sections keeps general position at `(0, x)`.

`A ⇒ (1) ∧ (2) ∧ (3)` is proved below (`A_to_B123`; (2) is the project lemma
`IsScPlusSection.pullbackSlice`, not part of A).  `A ⇒ (4)` fails: A's
`isGeneralPositionGerm_paramSection_of_comp` assumes `B.IsScFredholmSectionTame g` (Definition
3.51: germ data in a tame chart), B's (4) only `B.IsScFredholmSection g` (Definition 3.14) and
`PX.IsTame`; the project has no theorem deriving tame germ data from a tame `X`.
-/

namespace RoundTrip.V6_46
open Polyfold

/-- The project's statement: the theorems of the item, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.pullbackSlice_reparamSection.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.isScPlusSection_of_local.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.IsScPlusSection.reparam.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.isGeneralPositionGerm_paramSection_of_comp.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.pullbackSlice_reparamSection.{0, 0},
    @Polyfold.StrongBundle.isScPlusSection_of_local.{0, 0},
    @Polyfold.StrongBundle.IsScPlusSection.reparam.{0, 0},
    @Polyfold.StrongBundle.isGeneralPositionGerm_paramSection_of_comp.{0, 0}⟩

/-- The conjuncts (1)–(3) of B (B without the general-position clause (4)). -/
def B123 : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (B : StrongBundle PX P) (hπ : SndSmooth PX),
    (∀ (m n : ℕ) (g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
      (S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)),
      (B.pullback (hπ n)).IsScPlusSection S →
        (B.pullback (hπ m)).IsScPlusSection (reparam g S)) ∧
    (∀ (n : ℕ) (S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
      (q : Fin n → ℝ),
      (B.pullback (hπ n)).IsScPlusSection S → B.IsScPlusSection (pullbackSlice S q)) ∧
    (∀ s₀ s₁ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X),
      (B.pullback (hπ 1)).IsScPlusSection s₀ → (B.pullback (hπ 1)).IsScPlusSection s₁ →
        (B.pullback (hπ 2)).IsScPlusSection (convSq s₀ s₁))

/-- Sanity check: `B123` is the projection of B to its first three conjuncts. -/
theorem B_to_B123 : B → B123 := fun h _X _ _ _ PX _Y _ _ _ P _ _ _ _ B hπ =>
  ⟨(h PX P B hπ).1, (h PX P B hπ).2.1, (h PX P B hπ).2.2.1⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- B's `reparam` is the project's `reparamSection` along `q ↦ g q + 0`. -/
theorem reparam_eq {m n : ℕ} (g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) :
    reparam g S = reparamSection (fun q => g q + 0) S hS := by
  funext w
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change ((fv (P := P) (pullbackSlice S (g w.1)) w.2 : P ⁻¹' {w.2}) : Y) =
    pullbackSlice S (g w.1 + 0) w.2
  rw [add_zero, fv, dif_pos (hS.pullbackSlice _ w.2)]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- Two sections of `π*P` with the same slices are equal. -/
theorem eq_of_slices {n : ℕ}
    {S₁ S₂ : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (h₁ : IsSection (pullbackProj P Prod.snd) S₁) (h₂ : IsSection (pullbackProj P Prod.snd) S₂)
    (h : ∀ q y, pullbackSlice S₁ q y = pullbackSlice S₂ q y) : S₁ = S₂ := by
  funext w
  exact Subtype.ext (Prod.ext ((h₁ w).trans (h₂ w).symm) (h w.1 w.2))

/-- The projection `(τ, t) ↦ t`, `ℝ² → ℝ¹`. -/
noncomputable def projT : (Fin 2 → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj 1

theorem projT_apply (q : Fin 2 → ℝ) : projT q + 0 = pt1 (q 1) := by
  funext i; simp [projT, pt1]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- B's convex combination over the square, as `τ·(s¹ ∘ pr) + (1 − τ)·(s⁰ ∘ pr)`. -/
theorem convSq_eq (s₀ s₁ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (h₀ : IsSection (pullbackProj P Prod.snd) s₀) (h₁ : IsSection (pullbackProj P Prod.snd) s₁) :
    convSq s₀ s₁ = sectionAdd (pullbackProj P Prod.snd)
      (sectionSmul (pullbackProj P Prod.snd) (fun w : (Fin 2 → ℝ) × X => w.1 0)
        (reparamSection (fun q => projT q + 0) s₁ h₁))
      (sectionSmul (pullbackProj P Prod.snd) (fun w : (Fin 2 → ℝ) × X => 1 - w.1 0)
        (reparamSection (fun q => projT q + 0) s₀ h₀)) := by
  have hr₀ : IsSection (pullbackProj P (Prod.snd : (Fin 2 → ℝ) × X → X))
      (reparamSection (fun q => projT q + 0) s₀ h₀) := isSection_pullbackLift _
  have hr₁ : IsSection (pullbackProj P (Prod.snd : (Fin 2 → ℝ) × X → X))
      (reparamSection (fun q => projT q + 0) s₁ h₁) := isSection_pullbackLift _
  refine eq_of_slices (fun _ => rfl) (hr₁.sectionSmul.sectionAdd hr₀.sectionSmul) fun q y => ?_
  rw [pullbackSlice_sectionAdd hr₁.sectionSmul hr₀.sectionSmul, pullbackSlice_sectionSmul hr₁,
    pullbackSlice_sectionSmul hr₀]
  have e₀ : pullbackSlice (reparamSection (fun q => projT q + 0) s₀ h₀) q =
      pullbackSlice s₀ (pt1 (q 1)) := by
    change pullbackSlice s₀ (projT q + 0) = _; rw [projT_apply]
  have e₁ : pullbackSlice (reparamSection (fun q => projT q + 0) s₁ h₁) q =
      pullbackSlice s₁ (pt1 (q 1)) := by
    change pullbackSlice s₁ (projT q + 0) = _; rw [projT_apply]
  rw [e₀, e₁, sectionAdd_apply ((h₁.pullbackSlice _).sectionSmul)
      ((h₀.pullbackSlice _).sectionSmul), mk_sectionSmul (h₁.pullbackSlice _),
    mk_sectionSmul (h₀.pullbackSlice _)]
  change ((q 0 • fv (P := P) (pullbackSlice s₁ (pt1 (q 1))) y +
      (1 - q 0) • fv (P := P) (pullbackSlice s₀ (pt1 (q 1))) y : P ⁻¹' {y}) : Y) = _
  rw [fv, dif_pos (h₁.pullbackSlice _ y), fv, dif_pos (h₀.pullbackSlice _ y)]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- B's `Fgen` is the project's `paramSection` (Theorem 3.18's `g(y) + Σ λᵢ σᵢ(y)`). -/
theorem Fgen_eq {k : ℕ} (g : X → Y) (hg : IsSection P g) (σ : Fin k → X → Y)
    (hσ : ∀ i, IsSection P (σ i)) : Fgen g σ = paramSection g hg σ hσ := by
  funext w
  apply Subtype.ext
  refine Prod.ext rfl ?_
  have e : ∀ i, fv (P := P) (σ i) w.2 = ⟨σ i w.2, hσ i w.2⟩ := fun i => by
    rw [fv, dif_pos (hσ i w.2)]
  change ((fv (P := P) g w.2 + ∑ i, w.1 i • fv (P := P) (σ i) w.2 : P ⁻¹' {w.2}) : Y) = _
  rw [fv, dif_pos (hg w.2)]
  simp only [e]
  rfl

end Glue

/-- `A ⇒ (1) ∧ (2) ∧ (3)`: (1) is A's affine reparametrization with `b = 0`, (3) is A's
reparametrization along `(τ, t) ↦ t` followed by the product rule and the sum of sc⁺-sections;
(2) is the project lemma `IsScPlusSection.pullbackSlice`. -/
theorem A_to_B123 : A → B123 := by
  intro hA
  obtain ⟨-, -, hrep, -⟩ := hA
  intro X _ _ _ PX Y _ _ _ P _ _ _ _ B hπ
  refine ⟨?_, ?_, ?_⟩
  · intro m n g S hS
    rw [reparam_eq g hS.1]
    exact hrep hS g 0
  · intro n S q hS
    exact StrongBundle.IsScPlusSection.pullbackSlice hS q
  · intro s₀ s₁ h₀ h₁
    rw [convSq_eq s₀ s₁ h₀.1 h₁.1]
    have hβ : ((rnPolyfold 2).prod PX).IsScSmoothMap realPolyfold
        (fun w : (Fin 2 → ℝ) × X => w.1 0) :=
      (isScSmoothMap_rn_real_of_contDiff (contDiff_apply ℝ ℝ (0 : Fin 2))).comp
        (MPolyfold.isScSmoothMap_fst (rnPolyfold 2) PX)
    have hβ' : ((rnPolyfold 2).prod PX).IsScSmoothMap realPolyfold
        (fun w : (Fin 2 → ℝ) × X => 1 - w.1 0) :=
      (isScSmoothMap_rn_real_of_contDiff (contDiff_const.sub (contDiff_apply ℝ ℝ (0 : Fin 2)))).comp
        (MPolyfold.isScSmoothMap_fst (rnPolyfold 2) PX)
    exact ((hrep h₁ projT 0).smul_left hβ).add ((hrep h₀ projT 0).smul_left hβ')

/-- `A ⇒ (4)` **for tame germ data**: B's clause (4) with `B.IsScFredholmSectionTame g` in place
of `B.IsScFredholmSection g` follows from A's `isGeneralPositionGerm_paramSection_of_comp`
(`ι = Fin.castAdd l`).  This isolates the gap of (4) to the tameness of the germ data. -/
theorem A_to_B4_tame (hA : A) {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (B : StrongBundle PX P) (hπ : SndSmooth PX) (hX : PX.IsTame) (k l : ℕ) (g : X → Y)
    (σ : Fin k → X → Y) (sb : Fin l → X → Y) (x : X) (hg : B.IsScFredholmSectionTame g)
    (hσ : ∀ i, B.IsScPlusSection (σ i)) (hsb : ∀ j, B.IsScPlusSection (sb j))
    (hx : IsZeroAt P g x) (h : (B.pullback (hπ k)).IsGeneralPositionGerm (Fgen g σ) (0, x)) :
    (B.pullback (hπ (k + l))).IsGeneralPositionGerm (Fgen g (Fin.append σ sb)) (0, x) := by
  obtain ⟨-, -, -, hcomp⟩ := hA
  have ht : ∀ j, B.IsScPlusSection (Fin.append σ sb j) := fun j =>
    Fin.addCases (motive := fun j => B.IsScPlusSection (Fin.append σ sb j))
      (fun i => by simpa using hσ i) (fun i => by simpa using hsb i) j
  rw [Fgen_eq g hg.isScSmooth.1 σ fun i => (hσ i).1] at h
  rw [Fgen_eq g hg.isScSmooth.1 (Fin.append σ sb) fun j => (ht j).1]
  exact hcomp hX hg hσ ht (Fin.castAdd l) (fun i => (Fin.append_left σ sb i).symm) hx h

/-! `A ⇒ B` is not proved: the conjunct (4) of B.  A's
`isGeneralPositionGerm_paramSection_of_comp` needs `B.IsScFredholmSectionTame g` (germ data in a
tame chart, Definition 3.51), while B's (4) assumes `B.IsScFredholmSection g` (Definition 3.14)
with `PX.IsTame`.  The project has no theorem `PX.IsTame → IsScFredholmSection → IsScFredholmSectionTame`
(its Chapter 6 always assumes the tame form).  B's `Fgen` is the project's `paramSection` (both
compute `g(y) + Σ λᵢ σᵢ(y)` in the fibre), so the tameness of the germ data is the only gap in (4).

`B ⇒ A` is not proved: A has the general locality lemma `isScPlusSection_of_local`, affine (not
only linear) reparametrizations, and general position for any reindexing `ι : Fin k → Fin m`
with `sᵢ = t_{ι(i)}` (B: only appending, `ι = Fin.castAdd`); none of these follows from B. -/

#rt_check RoundTrip.V6_46.A_to_B123 [Polyfold.pullbackSlice_reparamSection,
  Polyfold.StrongBundle.isScPlusSection_of_local, Polyfold.StrongBundle.IsScPlusSection.reparam,
  Polyfold.StrongBundle.isGeneralPositionGerm_paramSection_of_comp]
#rt_check RoundTrip.V6_46.A_to_B4_tame [Polyfold.pullbackSlice_reparamSection,
  Polyfold.StrongBundle.isScPlusSection_of_local, Polyfold.StrongBundle.IsScPlusSection.reparam,
  Polyfold.StrongBundle.isGeneralPositionGerm_paramSection_of_comp]

end RoundTrip.V6_46
