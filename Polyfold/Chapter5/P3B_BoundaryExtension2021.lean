import Polyfold.Chapter12.P3B_LocalBoundaryExtension
import Polyfold.Chapter3.IndexAlongPathsLocalBump
import Polyfold.Chapter3.GapP1_UntamedBundleTheorem
import Polyfold.Chapter5.PartitionsOfUnity
import Polyfold.Chapter5.Transversality
import Polyfold.Chapter7.Discrete
import Polyfold.Chapter2.StrongBundleRestrict
import Polyfold.Chapter2.TameRetracts
import Polyfold.Chapter2.Boundary

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §5.4, p. 228:
**Definition 5.4.1** and **Theorem 5.4.2** (the ∂-Extension Theorem)
(2017: Definition 5.11 and Theorem 5.9).

# Extension of sc⁺-sections from the boundary

## The text, paraphrased

For a strong bundle `P : W → X` over a tame M-polyfold, a section `s` of `W|∂X → ∂X` is an
**sc⁺-section over `∂X`** (Definition 5.4.1) if for every `x ∈ ∂X` its restrictions to the local
faces at `x` are sc⁺-sections.  (Theorem 5.4.2) If `X` admits sc-smooth partitions of unity, `s`
is an sc⁺-section over `∂X`, `N` an auxiliary norm, `Ũ` an open neighbourhood of `supp(s)` and
`f : X → [0, ∞)` continuous, supported in `Ũ`, with `N(s(x)) < f(x)` on `supp(s)`, then there is an
sc⁺-section `s̃` of `P` with (1) `N(s̃) ≤ f`, (2) `supp(s̃) ⊆ Ũ`, (3) `s̃|∂X = s`.  The text gives
a sketch: Proposition 12.3.7 in tame local coordinates, glued by an sc-smooth partition of unity.

## What is formalized

* **Definition 5.4.1**: `StrongBundle.IsBoundaryScPlusSection`, read in every tame strong bundle
  chart `Φ` and every tame presentation `T` of its corner `C`: at `φ(x)`, `x ∈ ∂X`, the local
  representative `Φ[1] ∘ s ∘ φ⁻¹` is an sc⁺-section on each local face germ `O ∩ {t_i = 0}`,
  `i ∈ I(φ(x))` (`IsScPlusOnFaceNear`, `P3B_LocalBoundaryExtension.lean`).  **Nonvacuity**:
  `isBoundaryScPlusSection_fiberZero` (the zero section).
* `boundarySupport`: the text's `supp(s)` for a section over `∂X`.
* **The local step** `exists_local_extension`: in a tame chart at `x ∈ ∂X`, Proposition 12.3.7
  (`proposition_12_3_7_of_faces_at`) on the restricted chart, cut off by a bump function equal to
  `1` near `x`, gives a global sc⁺-section agreeing with `s` on `∂X` near `x`.
* **Theorem 5.4.2**: `theorem_5_4_2`.

## Reading

* "A strong bundle over a tame M-polyfold" is `StrongBundle.IsTameBundle` (every point lies in a
  tame strong bundle chart), the project's reading of the phrase (Chapter 3).
* The section `s` is a map `X → W` of which only the values on `∂X` are used: `P(s(x)) = x` and
  `s(x) ∈ W_{0,1}` for `x ∈ ∂X` are part of Definition 5.4.1 (for `x ∈ ∂X` lying on a face germ
  this follows from the face condition; it is stated so that the norm `N(s(x))` of the theorem is
  defined on all of `∂X`).
* `supp(s)` is the closure of `{x ∈ ∂X | s(x) ≠ 0_x}` (closed in `∂X` and in `X`).
* "`f` supported in `Ũ`" is `tsupport f ⊆ Ũ`; `N` takes values in `[0, ∞)` (Definition 5.1.1).
* The open neighbourhood `Ũ` of `supp(s)` is kept as in the text; the proof only uses
  `tsupport f ⊆ Ũ`.
-/

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u v

/-! ### Two local helpers -/

section Helpers

variable {E F : ScBanach}

/-- Sc⁺-sections of a local strong bundle are stable under change on `O`-agreement. -/
lemma isScPlusSection_congr_p3b {C Q : Set (E 0)} {K : Set (E 0 × F 0)}
    {f g : E 0 → E 0 × F 1} (hf : IsScPlusSection C Q K f) (h : EqOn f g Q) :
    IsScPlusSection C Q K g :=
  ⟨fun x hx => by rw [← h hx]; exact hf.fst_eq x hx, hf.isScSmooth.congr h⟩

end Helpers

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundle

/-! ### Definition 5.4.1 -/

variable (B : StrongBundle PX P)

/-- **Definition 5.4.1** (2021, p. 228; 2017: Definition 5.11): `s` is an **sc⁺-section over
`∂X`**: on `∂X` it is a section with values in `W_{0,1}`, and for every `x ∈ ∂X`, every tame
strong bundle chart `Φ` around `x` and every tame presentation `T` of the corner `C` of its
model, the restriction of the local representative `Φ[1] ∘ s ∘ φ⁻¹` to each local face germ
`O ∩ {t_i = 0}` at `φ(x)` (`i ∈ I(φ(x))`) is an sc⁺-section of `K → O` near `φ(x)`. -/
def IsBoundaryScPlusSection (s : X → Y) : Prop :=
  (∀ x ∈ PX.boundary, P (s x) = x ∧ s x ∈ B.oneSet) ∧
  ∀ c : StrongBundleChart PX P, B.IsTameChart c →
    ∀ (n : ℕ) (W : ScBanach) (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
      c.φ.model.C = T 0 ⁻¹' quadrant n W 0 →
      ∀ x ∈ PX.boundary ∩ c.φ.source, ∀ i ∈ zeroSet T (c.φ x),
        IsScPlusOnFaceNear T c.φ.model.C c.φ.model.O c.K (localRepOne c s) (c.φ x) i

variable (PX P) in
/-- The text's `supp(s)` for a section over `∂X`: the closure of `{x ∈ ∂X | s(x) ≠ 0_x}`. -/
def boundarySupport (s : X → Y) : Set X :=
  closure {x | x ∈ PX.boundary ∧ s x ≠ fiberZero P x}

variable {B}

omit [T2Space Y] [ParacompactSpace Y] in
lemma localRepOne_fiberZero {c : StrongBundleChart PX P} {z : c.φ.model.E 0}
    (hz : z ∈ c.φ.model.O) : localRepOne c (fiberZero P) z = (z, 0) := by
  change c.liftOne (fiberZero P (c.φ.symm z)) = _
  rw [liftOne_fiberZero (c.φ.symm_mapsTo hz), c.φ.apply_symm_apply hz]

/-- **Nonvacuity of Definition 5.4.1**: the zero section is an sc⁺-section over `∂X` (for every
strong bundle; the face germs are sc-retracts by `corner_retraction`). -/
theorem isBoundaryScPlusSection_fiberZero : B.IsBoundaryScPlusSection (fiberZero P) := by
  refine ⟨fun x _ => ⟨proj_fiberZero P x, B.fiberZero_mem_oneSet x⟩, ?_⟩
  intro c hc n W T hT x hx i hi
  have hO := c.base_retract
  have hD : ({c.φ x} : Set (c.φ.model.E 0)) ⊆
      (c.isRetraction.baseRetraction c.relOpen).retract := by
    rw [hO]; rintro _ rfl; exact c.φ.mapsTo_model x hx.2
  have h := isBoundaryScPlusSectionOn_zero T hT c.relOpen c.isRetraction (hc.2 n W T hT) hD
    (c.φ x) rfl i hi
  rw [hO] at h
  obtain ⟨V, hV, hxV, hret, hsec⟩ := h
  exact ⟨V, hV, hxV, hret,
    isScPlusSection_congr_p3b hsec fun z hz => (localRepOne_fiberZero hz.1.1).symm⟩

/-! ### The local step -/

/-- A boundary point lies in `∂O` in every tame chart. -/
lemma degIndex_ne_zero_of_mem_boundary {c : StrongBundleChart PX P} (hc : B.IsTameChart c)
    {y : X} (hy : y ∈ c.φ.source) (hyb : y ∈ PX.boundary) :
    Polyfold.degIndex c.φ.model.E c.φ.model.C (c.φ y) ≠ 0 := by
  have htr : IsTameRetract c.φ.model.E c.φ.model.C c.φ.model.O :=
    ⟨_, c.base_retract, hc.2⟩
  have h := PX.degIndex_eq_chartDegIndex_of_isTameRetract c.isChart htr hy
  change 1 ≤ PX.degIndex y at hyb
  rw [h, MPolyfold.chartDegIndex] at hyb
  omega

/-- **The local step of Theorem 5.4.2**: near a boundary point `x` in a tame strong bundle chart,
the extension of Proposition 12.3.7, cut off by a bump function equal to `1` near `x`, is a
global sc⁺-section agreeing with `s` on `∂X` near `x`. -/
theorem exists_local_extension (hbump : PX.AdmitsBumpFunctions) {c : StrongBundleChart PX P}
    (hc : B.IsTameChart c) {x : X} (hx : x ∈ c.φ.source) (hxb : x ∈ PX.boundary) {s : X → Y}
    (hs : B.IsBoundaryScPlusSection s) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ σ : X → Y, B.IsScPlusSection σ ∧
      ∀ y ∈ U ∩ PX.boundary, σ y = s y := by
  classical
  obtain ⟨n, W, T, hT⟩ := c.φ.model.isPartialQuadrant
  have htame := hc.2 n W T hT
  have hx₀ : c.φ x ∈ (c.isRetraction.baseRetraction c.relOpen).retract := by
    rw [c.base_retract]; exact c.φ.mapsTo_model x hx
  obtain ⟨V, hV, hxV, -, hext, hagree⟩ := proposition_12_3_7_of_faces_at T hT c.relOpen
    c.isRetraction htame hx₀ (s := localRepOne c s) (by
      intro i hi; rw [c.base_retract]; exact hs.2 c hc n W T hT x ⟨hxb, hx⟩ i hi)
  rw [c.base_retract] at hext hagree
  set e := boundaryExtension T c.R (zeroSet T (c.φ x)) (localRepOne c s) with he
  -- the restricted chart on `S = dom φ ∩ φ⁻¹(V)`
  set S := c.φ.source ∩ c.φ ⁻¹' V with hSdef
  have hSo : IsOpen S := c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source hV
  have hSs : S ⊆ c.φ.source := inter_subset_left
  set c' := c.restrict hSs hSo with hc'def
  have hc' : B.IsChart c' := fun c'' hc'' => (hc.1 c'' hc'').restrict_left hSs hSo
  have hO' : c.φ '' S = c.φ.model.O ∩ V := by
    rw [hSdef, Set.image_inter_preimage, c.φ.image_source]
  have hτ : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O
      (c'.φ.model.E.prod c'.F.shift) (c'.φ.model.C ×ˢ univ) (strongShiftOne c'.K)
      (fun z => (z, (e z).2)) := by
    change IsScSmoothRetractMap c.φ.model.E c.φ.model.C (c.φ '' S)
      (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c'.K)
      (fun z => (z, (e z).2))
    rw [hO']
    refine (hext.isScSmooth.congr (f' := fun z => (z, (e z).2))
      fun z hz => Prod.ext (hext.fst_eq z hz) rfl).mono_target
      fun z hz => ?_
    change (z, c.F.toBase 1 (e z).2) ∈ c'.K
    rw [c.restrict_K hSs hSo]
    refine ⟨?_, by rw [hO']; exact hz⟩
    have := hext.mem hz
    rwa [hext.fst_eq z hz] at this
  -- the bump function
  obtain ⟨β, hβ, -, -, hβS, hβev⟩ := proposition_5_5_3 hbump hSo ⟨hx, hxV⟩
  refine ⟨interior {y | β y = 1} ∩ S, isOpen_interior.inter hSo,
    ⟨mem_interior_iff_mem_nhds.2 hβev, hx, hxV⟩, cutoffSection c' β (fun z => (e z).2),
    isScPlusSection_cutoffSection_of_isChart hc' hβ hβS hτ, ?_⟩
  rintro y ⟨⟨hy1, hyS⟩, hyb⟩
  have hβy : β y = 1 := interior_subset (s := {y | β y = 1}) hy1
  have hsy := hs.1 y hyb
  have hys : s y ∈ c.toPartialEquiv.source := by rw [c.source_eq, mem_preimage, hsy.1]; exact hyS.1
  have hcut := cutoffSection_mem_source (β := β) hτ.mapsTo hyS
  have hcut' : cutoffSection c' β (fun z => (e z).2) y ∈ c.toPartialEquiv.source := by
    rw [c.source_eq]; exact hSs hcut
  refine c.toPartialEquiv.injOn hcut' hys ?_
  have h1 := apply_cutoffSection (β := β) hτ.mapsTo hyS
  change c (cutoffSection c' β (fun z => (e z).2) y) = c (s y)
  rw [show c (cutoffSection c' β (fun z => (e z).2) y) =
    c' (cutoffSection c' β (fun z => (e z).2) y) from rfl, h1, hβy]
  have hφy : c.φ y ∈ retractBoundary c.φ.model.E c.φ.model.C c.φ.model.O ∩ V :=
    ⟨⟨c.φ.mapsTo_model y hyS.1, degIndex_ne_zero_of_mem_boundary hc hyS.1 hyb⟩, hyS.2⟩
  have hey := hagree _ hφy
  refine Prod.ext ?_ ?_
  · change c.φ y = (c (s y)).1
    rw [c.covers _ hys, hsy.1]
  · change c.F.toBase 1 ((1 : ℝ) • (e (c.φ y)).2) = (c (s y)).2
    rw [one_smul, hey]
    change c.F.toBase 1 (Function.invFun (c.F.toBase 1) (c (s (c.φ.symm (c.φ y)))).2) = _
    rw [c.φ.symm_apply_apply hyS.1]
    exact Function.invFun_eq ((mem_oneSet_iff_of_isChart hc.1 hys).1 hsy.2)

/-! ### Local data with the bound `N ≤ f` -/

lemma aux_fiberZero {N : B.One → ℝ} (hN : B.IsAuxNorm N) (y : X)
    (h : fiberZero P y ∈ B.oneSet) : N (B.oneMk (fiberZero P y) h) = 0 :=
  (hN.fiber y).map_zero

/-- **Sc⁺ is local** (as `isScPlusSection_of_locally` of `P3S_ScPlusSectionFunctor.lean`): a
section which near every point agrees with an sc-smooth map into `Y[1]` is an sc⁺-section. -/
theorem isScPlusSection_of_locally_p3b {σ : X → Y} (hσ : IsSection P σ)
    (h : ∀ y₀, ∃ N : Set X, IsOpen N ∧ y₀ ∈ N ∧ ∃ G : X → B.One,
      PX.IsScSmoothOn B.toMPolyfold1 G N ∧ ∀ y ∈ N, B.oneVal (G y) = σ y) :
    B.IsScPlusSection σ := by
  choose N hN hyN G hG hGeq using h
  have hmem : ∀ z, σ z ∈ B.oneSet := fun z => hGeq z z (hyN z) ▸ B.oneVal_mem (G z z)
  refine (B.isScPlusSection_iff _).2 ⟨hσ, fun z => B.oneMk _ (hmem z),
    funext fun z => B.oneVal_oneMk _ (hmem z), ?_⟩
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x _ =>
    ⟨N x, hN x, hyN x, subset_univ _, (hG x).congr fun z hz => ?_⟩
  apply B.oneVal_injective
  rw [hGeq x z hz, B.oneVal_oneMk]

/-- **Local data for Theorem 5.4.2**: every point `x` has an open neighbourhood `U` and an
sc⁺-section `σ` with `N(σ) ≤ f` on `U` and `σ = s` on `∂X ∩ U` (`σ = 0` off `∂X` and off
`supp(s)`; the local step and continuity of `N ∘ σ` at points of `supp(s)`). -/
theorem exists_local_bounded (hB : ∀ x : X, ∃ c : StrongBundleChart PX P, B.IsTameChart c ∧
      x ∈ c.φ.source)
    (hbump : PX.AdmitsBumpFunctions) {s : X → Y} (hs : B.IsBoundaryScPlusSection s)
    {N : B.One → ℝ} (hN : B.IsAuxNorm N) {f : X → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hNf : ∀ x ∈ boundarySupport PX P s, ∀ h : s x ∈ B.oneSet, N (B.oneMk (s x) h) < f x)
    (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ σ : X → Y, B.IsScPlusSection σ ∧
      (∀ y ∈ U, ∀ h : σ y ∈ B.oneSet, N (B.oneMk (σ y) h) ≤ f y) ∧
      ∀ y ∈ U ∩ PX.boundary, σ y = s y := by
  have hzero : ∀ y (h : fiberZero P y ∈ B.oneSet), N (B.oneMk (fiberZero P y) h) ≤ f y :=
    fun y h => (aux_fiberZero hN y h).le.trans (hf0 y)
  by_cases hxb : x ∈ PX.boundary
  swap
  · exact ⟨PX.boundaryᶜ, PX.isClosed_boundary.isOpen_compl, hxb, fiberZero P,
      isScPlusSection_fiberZero, fun y _ => hzero y, fun y hy => absurd hy.2 hy.1⟩
  by_cases hxs : x ∈ boundarySupport PX P s
  swap
  · refine ⟨(boundarySupport PX P s)ᶜ, isClosed_closure.isOpen_compl, hxs, fiberZero P,
      isScPlusSection_fiberZero, fun y _ => hzero y, fun y hy => ?_⟩
    by_contra hne
    exact hy.1 (subset_closure ⟨hy.2, fun h => hne h.symm⟩)
  obtain ⟨c, hc, hxc⟩ := hB x
  obtain ⟨U₁, hU₁, hxU₁, σ, hσ, hagree⟩ := exists_local_extension hbump hc hxc hxb hs
  obtain ⟨-, g, hg, hgs⟩ := (B.isScPlusSection_iff σ).1 hσ
  have hgc : Continuous g := continuousOn_univ.1 hgs.continuousOn
  have hgσ : ∀ y (h : σ y ∈ B.oneSet), g y = B.oneMk (σ y) h := fun y h =>
    B.oneVal_injective (congrFun hg y)
  refine ⟨U₁ ∩ {y | N (g y) < f y}, hU₁.inter (isOpen_lt (hN.continuous.comp hgc) hf),
    ⟨hxU₁, ?_⟩, σ, hσ, fun y hy h => ?_, fun y hy => hagree y ⟨hy.1.1, hy.2⟩⟩
  · have hσx : σ x = s x := hagree x ⟨hxU₁, hxb⟩
    have h1 := (hs.1 x hxb).2
    have : g x = B.oneMk (s x) h1 := B.oneVal_injective ((congrFun hg x).trans hσx)
    change N (g x) < f x
    rw [this]; exact hNf x hxs h1
  · rw [← hgσ y h]; exact hy.2.le

/-! ### Theorem 5.4.2 -/

/-- **Theorem 5.4.2** (the ∂-Extension Theorem; 2021, p. 228; 2017: Theorem 5.9), for a strong
bundle every point of whose base lies in a tame strong bundle chart (the form used by
`theorem_5_4_2`): the local extensions of `exists_local_bounded`, glued by an sc-smooth
partition of unity. -/
theorem exists_boundary_extension (hB : ∀ x : X, ∃ c : StrongBundleChart PX P,
      B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : PX.AdmitsScPartitionsOfUnity) {s : X → Y} (hs : B.IsBoundaryScPlusSection s)
    {N : B.One → ℝ} (hN : B.IsAuxNorm N) {Ũ : Set X} {f : X → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (hfU : tsupport f ⊆ Ũ)
    (hNf : ∀ x ∈ boundarySupport PX P s, ∀ h : s x ∈ B.oneSet, N (B.oneMk (s x) h) < f x) :
    ∃ s' : X → Y, B.IsScPlusSection s' ∧
      (∀ x (h : s' x ∈ B.oneSet), N (B.oneMk (s' x) h) ≤ f x) ∧
      sectionSupport P s' ⊆ Ũ ∧ ∀ x ∈ PX.boundary, s' x = s x := by
  classical
  choose U hU hxU σ hσ hσN hσs using
    exists_local_bounded hB hpu.admitsBumpFunctions hs hN hf hf0 hNf
  obtain ⟨ρ, hρsub, hρsm⟩ := hpu X U hU (iUnion_eq_univ_iff.2 fun x => ⟨x, hxU x⟩)
  have hsec : ∀ i, IsSection P (σ i) := fun i => (hσ i).1
  -- the glued section `s'(y) = Σᵢ ρᵢ(y) σᵢ(y)`
  set s' : X → Y := fun y =>
    ((∑ᶠ i, ρ i y • (⟨σ i y, hsec i y⟩ : P ⁻¹' {y}) : P ⁻¹' {y}) : Y) with hs'def
  have hs'sec : IsSection P s' := fun y => (∑ᶠ i, ρ i y • (⟨σ i y, hsec i y⟩ : P ⁻¹' {y})).2
  -- on a finite set `I` containing the support of `(ρᵢ(y))ᵢ`, `s'(y)` is a finite sum
  have hfin : ∀ y (I : Finset X), support (ρ · y) ⊆ I →
      (∑ᶠ i, ρ i y • (⟨σ i y, hsec i y⟩ : P ⁻¹' {y})) =
        ∑ i ∈ I, ρ i y • (⟨σ i y, hsec i y⟩ : P ⁻¹' {y}) := fun y I hI =>
    finsum_eq_sum_of_support_subset _ fun i hi => hI fun h => hi (by
      have h' : ρ i y = 0 := h
      simp only [h', zero_smul])
  have hloc : ∀ y (I : Finset X), support (ρ · y) ⊆ I →
      s' y = sectionSum P I (fun i => sectionSmul P (ρ i) (σ i)) y := fun y I hI => by
    rw [sectionSum_apply (fun i => (hsec i).sectionSmul)]
    change ((∑ᶠ i, ρ i y • (⟨σ i y, hsec i y⟩ : P ⁻¹' {y}) : P ⁻¹' {y}) : Y) = _
    rw [hfin y I hI]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Subtype.ext ?_
    exact (sectionSmul_apply (hsec i) y).symm
  -- (0) `s'` is an sc⁺-section
  have hs'plus : B.IsScPlusSection s' := by
    refine isScPlusSection_of_locally_p3b hs'sec fun y₀ => ?_
    obtain ⟨I, hI⟩ := ρ.exists_finset_nhds y₀
    obtain ⟨t, ht, hto, hy₀t⟩ := eventually_nhds_iff.1 hI
    have hsum : B.IsScPlusSection (sectionSum P I fun i => sectionSmul P (ρ i) (σ i)) :=
      isScPlusSection_sectionSum I fun i => (hσ i).smul_left (hρsm i)
    obtain ⟨-, G, hG, hGs⟩ := (B.isScPlusSection_iff _).1 hsum
    exact ⟨t, hto, hy₀t, G, hGs.mono hto (subset_univ _), fun y hy =>
      (congrFun hG y).trans (hloc y I (ht y hy).2).symm⟩
  -- (1) the bound
  have hbound : ∀ y (h : s' y ∈ B.oneSet), N (B.oneMk (s' y) h) ≤ f y := by
    intro y h
    obtain ⟨I, hI⟩ := ρ.exists_finset_nhds y
    obtain ⟨hI1, hIs⟩ := hI.self_of_nhds
    have hmem : ∀ i, σ i y ∈ B.oneSet := fun i => (hσ i).mem_oneSet y
    set w : X → B.oneFiber y := fun i => ⟨⟨σ i y, hsec i y⟩, hmem i⟩ with hw
    have hrep : B.oneMk (s' y) h = B.toOne (∑ i ∈ I, ρ i y • w i) := by
      apply B.oneVal_injective
      rw [oneVal_oneMk, oneVal_toOne]
      change ((∑ᶠ i, ρ i y • (⟨σ i y, hsec i y⟩ : P ⁻¹' {y}) : P ⁻¹' {y}) : Y) = _
      rw [hfin y I hIs, Submodule.coe_sum]
      rfl
    have hterm : ∀ i ∈ I, N (B.toOne (ρ i y • w i)) ≤ ρ i y * f y := by
      intro i _
      rw [hN.smul, abs_of_nonneg (ρ.nonneg i y)]
      by_cases hρ : ρ i y = 0
      · rw [hρ, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (hσN i y (hρsub i (subset_tsupport _ hρ)) (hmem i))
          (ρ.nonneg i y)
    rw [hrep]
    calc N (B.toOne (∑ i ∈ I, ρ i y • w i)) ≤ ∑ i ∈ I, N (B.toOne (ρ i y • w i)) :=
          hN.toOne_sum_le I _
      _ ≤ ∑ i ∈ I, ρ i y * f y := Finset.sum_le_sum hterm
      _ = f y := by rw [← Finset.sum_mul, hI1, one_mul]
  refine ⟨s', hs'plus, hbound, ?_, ?_⟩
  -- (2) the support
  · refine (closure_mono fun y hy => ?_).trans hfU
    intro hfy
    apply hy
    have hm := hs'plus.mem_oneSet y
    have hle := hbound y hm
    rw [hfy] at hle
    have h0 : N (B.toOne (⟨⟨s' y, hs'sec y⟩, hm⟩ : B.oneFiber y)) = 0 :=
      le_antisymm hle (hN.nonneg _)
    have := congrArg (fun v : B.oneFiber y => ((v : P ⁻¹' {y}) : Y)) ((hN.fiber y).eq_zero _ h0)
    exact this
  -- (3) `s' = s` on `∂X`
  · intro y hyb
    obtain ⟨I, hI⟩ := ρ.exists_finset_nhds y
    obtain ⟨hI1, hIs⟩ := hI.self_of_nhds
    have hsy := (hs.1 y hyb).1
    change ((∑ᶠ i, ρ i y • (⟨σ i y, hsec i y⟩ : P ⁻¹' {y}) : P ⁻¹' {y}) : Y) = s y
    rw [hfin y I hIs]
    have : ∑ i ∈ I, ρ i y • (⟨σ i y, hsec i y⟩ : P ⁻¹' {y}) =
        ∑ i ∈ I, ρ i y • (⟨s y, hsy⟩ : P ⁻¹' {y}) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hρ : ρ i y = 0
      · rw [hρ, zero_smul, zero_smul]
      · congr 2
        exact hσs i y ⟨hρsub i (subset_tsupport _ hρ), hyb⟩
    rw [this, ← Finset.sum_smul, hI1, one_smul]

end StrongBundle

/-- **Theorem 5.4.2** (the ∂-Extension Theorem; 2021, p. 228; 2017: Theorem 5.9): for a strong
bundle `P : W → X` over a tame M-polyfold admitting sc-smooth partitions of unity, an
sc⁺-section `s` over `∂X` (Definition 5.4.1), an auxiliary norm `N`, an open neighbourhood `Ũ`
of `supp(s)` and a continuous `f : X → [0, ∞)` supported in `Ũ` with `N(s(x)) < f(x)` on
`supp(s)`, there is an sc⁺-section `s̃` of `P` with (1) `N(s̃) ≤ f`, (2) `supp(s̃) ⊆ Ũ`,
(3) `s̃|∂X = s`. -/
theorem theorem_5_4_2 {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {B : StrongBundle PX P} (hB : B.IsTameBundle) (hpu : PX.AdmitsScPartitionsOfUnity)
    {s : X → Y} (hs : B.IsBoundaryScPlusSection s) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    {Ũ : Set X} (_hŨ : IsOpen Ũ) (_hsupp : StrongBundle.boundarySupport PX P s ⊆ Ũ) {f : X → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (hfU : tsupport f ⊆ Ũ)
    (hNf : ∀ x ∈ StrongBundle.boundarySupport PX P s, ∀ h : s x ∈ B.oneSet,
      N (B.oneMk (s x) h) < f x) :
    ∃ s' : X → Y, B.IsScPlusSection s' ∧
      (∀ x (h : s' x ∈ B.oneSet), N (B.oneMk (s' x) h) ≤ f x) ∧
      sectionSupport P s' ⊆ Ũ ∧ ∀ x ∈ PX.boundary, s' x = s x :=
  StrongBundle.exists_boundary_extension hB.2 hpu hs hN hf hf0 hfU hNf

end Polyfold
