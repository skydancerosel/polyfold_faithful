import Polyfold.Chapter14.AssemblyInputInstance
import Polyfold.Chapter14.FaceAssembly

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
**Theorem 14.1.9** (∂-Extension Theorem, p. 646, proof pp. 656–678; 2017: Theorem 14.2) and the
extension part of **Theorem 14.6.3** (p. 682; 2017: Theorem 14.4), proved.

# Theorem 14.1.9

## What is formalized

* `theorem_14_1_9_charged_statement A`: B1's `theorem_14_1_9_statement` with two readings made
  explicit: the strong bundle has tame strong bundle charts around every object (the text's
  standing assumption of Chapter 14, as in LX's and Z5's Proposition 14.4.14), and `Λ` charges every
  fibre over `∂X` (`ChargesBoundary`, i.e. `I_x ≠ ∅` in Definition 14.1.3 (3), which divides by
  `|I_x|`).  Without the second, B1's statement does not hold as we read it when `∂X ≠ ∅`
  (`not_theorem_14_1_9_statement_a6`, file `EmptyIndex`); the condition is also necessary
  for the conclusion (`chargesBoundary_of_structurable_eq_a6`).
* `sizeControl_a6`: GL's size-control step (`theorem_14_1_9_hyp`) for one `Λ`: from extensions
  of `Λ` with `dom-supp` in any saturated open `Ũ' ⊇ dom-supp(Λ)` to the conclusion of Theorem
  14.1.9 with `N(Λ') ≤ f`.  (The proof is GL's, specialized to one `Λ`.)
* **`theorem_14_1_9_charged_a6`**: Theorem 14.1.9 with no hypothesis beyond the text's (read as
  above): Proposition 14.2.3, Proposition 14.3.8 (S3), Proposition 14.4.14 (LX, Z4, Z5),
  Lemma 14.5.1 (B2), Proposition 14.5.4 and the assembly (T9), Theorem 14.5.5 (GL), size control.
* `theorem_14_1_9_iff_a6`: for structurable `Λ` over `∂X`, an extension as in Theorem 14.1.9
  exists iff `Λ` charges every boundary fibre.
* **`CompatibleFaceData.theorem_14_6_3_extension_a6`**: F6's extension part of Theorem 14.6.3 with
  Theorem 14.1.9 proved (F6's `theorem_14_6_3_extension_hyp` took B1's statement as hypothesis).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-- **2021 Theorem 14.1.9 (∂-Extension Theorem), p. 646 (2017: Theorem 14.2)**, as a statement
with the readings named: B1's `theorem_14_1_9_statement` plus tame strong bundle charts (`hB`, the
standing assumption) and `ChargesBoundary Λ` (`I_x ≠ ∅`). -/
def theorem_14_1_9_charged_statement (A : SEP.{u}) : Prop :=
  A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
  (∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source) →
  ∀ Λ : A.W → ℚ≥0, IsBoundaryStructurable A Λ → ChargesBoundary Λ →
  ∀ N : A.B.One → ℝ, A.E.IsAuxNorm N →
  ∀ Ũ : Set A.Obj, IsOpen Ũ → A.X.IsSaturated Ũ → boundaryDomSupp Λ ⊆ Ũ →
  ∀ f : A.Obj → ℝ, Continuous f → (∀ x, 0 ≤ f x) → (∀ φ, f (A.X.tgt φ) = f (A.X.src φ)) →
    tsupport f ⊆ Ũ → (∀ x ∈ boundaryDomSupp Λ, pointwiseNorm N Λ x < f x) →
  ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ x, pointwiseNorm N Λ' x ≤ f x) ∧
    domSupp Λ' ⊆ Ũ ∧ ∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w

/-- **Size control for one `Λ`** (GL's `theorem_14_1_9_hyp`, with the extension asked only for
the given `Λ`): extensions with domain support in every saturated open neighbourhood of
`dom-supp(Λ)` give an extension with `N(Λ') ≤ f` and `dom-supp(Λ') ⊆ Ũ`. -/
theorem sizeControl_a6 (hpara : A.X.HasParacompactOrbitSpace)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {Λ : A.W → ℚ≥0}
    (hext : ∀ U' : Set A.Obj, IsOpen U' → A.X.IsSaturated U' → boundaryDomSupp Λ ⊆ U' →
      ∃ Λ'' : A.W → ℚ≥0, IsStructurable A Λ'' ∧ domSupp Λ'' ⊆ U' ∧
        ∀ w, A.P w ∈ A.X.PObj.boundary → Λ'' w = Λ w)
    {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N) {Ũ : Set A.Obj}
    {f : A.Obj → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfinv : ∀ φ, f (A.X.tgt φ) = f (A.X.src φ)) (htsupp : tsupport f ⊆ Ũ)
    (hlt : ∀ x ∈ boundaryDomSupp Λ, pointwiseNorm N Λ x < f x) :
    ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ x, pointwiseNorm N Λ' x ≤ f x) ∧
      domSupp Λ' ⊆ Ũ ∧ ∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w := by
  have hN1 : A.B.IsAuxNorm N := hN.isAuxNorm
  set U' : Set A.Obj := {x | 0 < f x} with hU'
  have hU'o : IsOpen U' := isOpen_lt continuous_const hf
  have hU'sat : A.X.IsSaturated U' := A.X.isSaturated_iff.2 fun φ h => by
    change 0 < f _
    rw [hfinv]
    exact h
  have hsub' : boundaryDomSupp Λ ⊆ U' := fun x hx =>
    lt_of_le_of_lt (pointwiseNorm_nonneg hN1 Λ x) (hlt x hx)
  have hU'Ũ : U' ⊆ Ũ := fun x hx => htsupp (subset_tsupport f (ne_of_gt hx))
  obtain ⟨Λ'', hΛ'', hdom, hres⟩ := hext U' hU'o hU'sat hsub'
  set h : A.Obj → ℝ := pointwiseNorm N Λ'' with hh
  have hh0 : ∀ x, 0 ≤ h x := pointwiseNorm_nonneg hN1 Λ''
  set K := domSupp Λ'' with hK
  have hKeq : K = closure {x | 0 < h x} := hΛ''.1.domSupp_eq_closure_pointwiseNorm hN1
  have hhK : ∀ x, x ∉ K → h x = 0 := fun x hx =>
    le_antisymm (not_lt.1 fun hpos => hx (by rw [hKeq]; exact subset_closure hpos)) (hh0 x)
  have hhinv : ∀ φ, h (A.X.tgt φ) = h (A.X.src φ) := pointwiseNorm_tgt hN hΛ''.1
  set G : Set A.Obj := {x | h x < f x} ∪ Kᶜ with hG
  have hGo : IsOpen G :=
    (isOpen_pointwiseNorm_lt hN1 hΛ''.1 hf).union
      (by rw [hK, domSupp]; exact isClosed_closure.isOpen_compl)
  have hGsat : A.X.IsSaturated G := by
    refine isSaturated_union_gl (A.X.isSaturated_iff.2 fun φ hφ => ?_) (A.X.isSaturated_compl ?_)
    · change h _ < f _
      rw [hhinv, hfinv]
      exact hφ
    · rw [hKeq]
      exact isSaturated_closure_gl (A.X.isSaturated_iff.2 fun φ hφ => by
        change 0 < h _
        rw [hhinv]
        exact hφ)
  have hbG : A.X.PObj.boundary ⊆ G := by
    intro x hx
    by_cases hxK : x ∈ K
    swap
    · exact Or.inr hxK
    left
    change h x < f x
    have hsupp : suppAt Λ'' x = suppAt Λ x := by
      ext w
      constructor
      · rintro ⟨hw, hpos⟩
        refine ⟨hw, ?_⟩
        rw [← hres w (by rw [hw]; exact hx)]
        exact hpos
      · rintro ⟨hw, hpos⟩
        refine ⟨hw, ?_⟩
        rw [hres w (by rw [hw]; exact hx)]
        exact hpos
    by_cases hxb : x ∈ boundaryDomSupp Λ
    · have := hlt x hxb
      rw [hh, pointwiseNorm, hsupp]
      exact this
    · have hfx : 0 < f x := hdom hxK
      have hle : h x ≤ 0 := by
        refine csSup_le ((hΛ''.1.suppAt_nonempty x).image _) ?_
        rintro _ ⟨w, hws, rfl⟩
        have hw0 : w = fiberZero A.P x := by
          by_contra hne
          rw [hsupp] at hws
          exact hxb (subset_closure ⟨hx, w, hws.1, hws.1 ▸ hne, hws.2⟩)
        rw [hw0, normW_fiberZero hN1]
      linarith
  have hbcl : IsClosed (A.X.π '' A.X.PObj.boundary) :=
    A.X.isClosed_π_image_of_isSaturated isSaturated_boundary_gl A.X.PObj.isClosed_boundary
  have hGcl : IsClosed (A.X.π '' Gᶜ) :=
    A.X.isClosed_π_image_of_isSaturated (A.X.isSaturated_compl hGsat) hGo.isClosed_compl
  have hdisj : Disjoint (A.X.π '' Gᶜ) (A.X.π '' A.X.PObj.boundary) := by
    rw [disjoint_iff_forall_ne]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, hab⟩ e
    have : a ∈ A.X.PObj.boundary := by
      rw [← isSaturated_boundary_gl]
      exact ⟨b, hb, hab.trans e.symm⟩
    exact ha (hbG this)
  obtain ⟨F, hFs, hF0, hF1, hFI⟩ :=
    A.X.exists_isScSmoothMap_orbit_urysohn hpara hpu hGcl hbcl hdisj
  set σ : A.Obj → ℝ := F ∘ A.X.π with hσ
  have hσinv : ∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ) := fun φ => by
    simp only [hσ, comp_apply]
    rw [A.X.π_eq_π_iff.2 ⟨φ, rfl, rfl⟩]
  have hσ01 : ∀ x, σ x ∈ Icc (0 : ℝ) 1 := fun x => hFI _
  have hσG : ∀ x, x ∉ G → σ x = 0 := fun x hx => hF0 (mem_image_of_mem _ hx)
  have hσb : ∀ x ∈ A.X.PObj.boundary, σ x = 1 := fun x hx => hF1 (mem_image_of_mem _ hx)
  have hΛ' := lemma_13_3_14_fun hΛ'' hσinv hFs
  have hbound : ∀ x, pointwiseNorm N (multisectionSmulFun σ Λ'') x ≤ σ x * h x := fun x => by
    have := pointwiseNorm_smulFun_le hN1 hΛ''.1 hΛ'.1 x
    rwa [abs_of_nonneg (hσ01 x).1] at this
  refine ⟨multisectionSmulFun σ Λ'', hΛ', fun x => ?_, ?_, fun w hw => ?_⟩
  · refine (hbound x).trans ?_
    by_cases hxG : x ∈ G
    · rcases hxG with hlt' | hxK
      · have : σ x * h x ≤ h x := mul_le_of_le_one_left (hh0 x) (hσ01 x).2
        exact this.trans (le_of_lt hlt')
      · rw [hhK x hxK, mul_zero]; exact hf0 x
    · rw [hσG x hxG, zero_mul]; exact hf0 x
  · rw [hΛ'.1.domSupp_eq_closure_pointwiseNorm hN1]
    refine (closure_mono fun x hx => ?_).trans (hKeq ▸ hdom.trans hU'Ũ)
    change 0 < h x
    have := lt_of_lt_of_le hx (hbound x)
    by_contra hn
    rw [le_antisymm (not_lt.1 hn) (hh0 x), mul_zero] at this
    exact lt_irrefl _ this
  · rw [multisectionSmulFun_of_eq_one (hσb _ hw)]
    exact hres w hw

/-- **2021 Theorem 14.1.9 (∂-Extension Theorem), p. 646 (2017: Theorem 14.2)**, proved: over a
tame ep-groupoid with paracompact orbit space whose object M-polyfold admits sc-smooth partitions
of unity, with tame strong bundle charts, every structurable `Λ` over `∂X` with non-empty index
sets (`ChargesBoundary`), auxiliary norm `N`, saturated open `Ũ ⊇ dom-supp(Λ)` and continuous
functor `f ≥ 0` with `tsupport f ⊆ Ũ` and `N(Λ) < f` on `dom-supp(Λ)` has a structurable
extension `Λ'` with `N(Λ') ≤ f`, `dom-supp(Λ') ⊆ Ũ` and `Λ' = Λ` over `∂X`. -/
theorem theorem_14_1_9_charged_a6 : theorem_14_1_9_charged_statement A := by
  intro hX hpara hpu hB Λ hΛ hch N hN Ũ _ _ _ f hf hf0 hfinv htsupp hlt
  obtain ⟨D⟩ := exists_assemblyInput_a6 hX hpara hpu hB hΛ hch
  exact sizeControl_a6 hpara hpu (fun _ hUo hUs hsub => D.extension hpara hpu hUo hUs hsub) hN
    hf hf0 hfinv htsupp hlt

/-- **Theorem 14.1.9 with the condition named exactly**: under the hypotheses of Theorem 14.1.9
(with tame strong bundle charts), a structurable `Λ` over `∂X` has an extension as in the theorem
iff it charges every fibre over `∂X`. -/
theorem theorem_14_1_9_iff_a6 (hX : A.X.IsTame) (hpara : A.X.HasParacompactOrbitSpace)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity)
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧
      x ∈ c.φ.source)
    {Λ : A.W → ℚ≥0} (hΛ : IsBoundaryStructurable A Λ) {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N)
    {Ũ : Set A.Obj} (hUo : IsOpen Ũ) (hUs : A.X.IsSaturated Ũ) (hsub : boundaryDomSupp Λ ⊆ Ũ)
    {f : A.Obj → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfinv : ∀ φ, f (A.X.tgt φ) = f (A.X.src φ)) (htsupp : tsupport f ⊆ Ũ)
    (hlt : ∀ x ∈ boundaryDomSupp Λ, pointwiseNorm N Λ x < f x) :
    (∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ x, pointwiseNorm N Λ' x ≤ f x) ∧
      domSupp Λ' ⊆ Ũ ∧ ∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w) ↔ ChargesBoundary Λ :=
  ⟨fun ⟨_, h1, _, _, h4⟩ => chargesBoundary_of_structurable_eq_a6 h1 h4, fun hch =>
    theorem_14_1_9_charged_a6 hX hpara hpu hB Λ hΛ hch N hN Ũ hUo hUs hsub f hf hf0 hfinv
      htsupp hlt⟩

/-- **B1's `theorem_14_1_9_statement` holds when `∂X = ∅`** (and fails otherwise,
`not_theorem_14_1_9_statement_a6`). -/
theorem theorem_14_1_9_statement_of_boundary_eq_empty_a6 (hb : A.X.PObj.boundary = ∅) :
    theorem_14_1_9_statement A :=
  theorem_14_1_9_of_assembly (assemblyHyp_of_boundary_eq_empty hb)

/-- **T9's `AssemblyHyp` holds only when `∂X = ∅`** (for tame `X` with paracompact `|X|` and
partitions of unity): it implies B1's statement (`theorem_14_1_9_of_assembly`), which does not
hold as we read it when `∂X ≠ ∅`.  `exists_assemblyInput_a6` is the form with `ChargesBoundary`. -/
theorem boundary_eq_empty_of_assemblyHyp_a6 (hX : A.X.IsTame)
    (hpara : A.X.HasParacompactOrbitSpace) (hpu : A.X.PObj.AdmitsScPartitionsOfUnity)
    (h : AssemblyHyp A) : A.X.PObj.boundary = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx =>
    not_theorem_14_1_9_statement_a6 hX hpara hpu hx (theorem_14_1_9_of_assembly h)

/-! ### Theorem 14.6.3, the extension part -/

namespace CompatibleFaceData

/-- **2021 Theorem 14.6.3, p. 682 (2017: Theorem 14.4)**, the extension part, with Theorem 14.1.9
proved: over a tame face-structured ep-groupoid with paracompact orbit space, sc-smooth partitions
of unity and tame strong bundle charts, the glued `Λ` of compatible face data (with non-empty
index sets, `ChargesBoundary`) extends to a structurable `Λ'` on `W` with `N(Λ') ≤ f`,
`dom-supp(Λ') ⊆ Ũ` and `Λ' = Λ_F` over every face `F`. -/
theorem theorem_14_6_3_extension_a6 (D : CompatibleFaceData A) (hX : A.X.IsEpFaceStructured)
    (hpara : A.X.HasParacompactOrbitSpace) (hpart : A.X.PObj.AdmitsScPartitionsOfUnity)
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧
      x ∈ c.φ.source)
    (hch : ChargesBoundary D.Λg) (N : A.B.One → ℝ) (hN : A.E.IsAuxNorm N)
    (Ũ : Set A.Obj) (hŨ : IsOpen Ũ) (hŨs : A.X.IsSaturated Ũ) (hdom : boundaryDomSupp D.Λg ⊆ Ũ)
    (f : A.Obj → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hff : ∀ φ, f (A.X.tgt φ) = f (A.X.src φ)) (hfU : tsupport f ⊆ Ũ)
    (hfN : ∀ x ∈ boundaryDomSupp D.Λg, pointwiseNorm N D.Λg x < f x) :
    ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ x, pointwiseNorm N Λ' x ≤ f x) ∧
      domSupp Λ' ⊆ Ũ ∧ ∀ F (hF : A.X.IsEpFace F) w, A.P w ∈ F → Λ' w = (D.T F hF).Λ w := by
  obtain ⟨Λ', h1, h2, h3, h4⟩ := theorem_14_1_9_charged_a6 hX.1 hpara hpart hB D.Λg
    (D.theorem_14_6_3_hyp hX hpara).1 hch N hN Ũ hŨ hŨs hdom f hf hf0 hff hfU hfN
  exact ⟨Λ', h1, h2, h3, fun F hF w hw =>
    (h4 w (IsEpFace.subset_boundary hF hw)).trans (D.Λg_eq hF hw)⟩

end CompatibleFaceData

end SBLocalization

end Polyfold
