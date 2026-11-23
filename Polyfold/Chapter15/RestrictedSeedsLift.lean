import Polyfold.Chapter15.RestrictedSeedsCompare2
import Polyfold.Chapter15.RestrictedSeedsNatRep
import Polyfold.Chapter15.RestrictedSeedsAtomic
import Polyfold.Chapter15.RestrictedSeedsCut
import Polyfold.Chapter15.RestrictedSeedsTransfer
import Polyfold.Chapter15.AdmissibleRelativeStep

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (Transversal Extension Theorem), steps (c)–(d), pp. 698–699, on the cylinder
of the restriction of a strong bundle to a saturated open subset (Proposition 7.1.22, p. 250;
Corollary 15.3.10 (3), p. 699).

# The local family of one centre on the cylinder of a restriction

## The text, paraphrased

At a point `x` of `supp(Λ₀ ∘ f)` off the boundary the proof takes a neighbourhood `U(x)` with the
natural action of `G_x`, an invariant open `V(x)` with `cl V(x) ⊆ U(x)`, and finitely many small
sc⁺-sections supported in `V(x)` which, together with the operators of `T(f, Λ₀)`, span the
fibres near `x`; the symmetrized sections give a family of sc⁺-multisections.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `exists_seeds_of_function_of_lt`: the seeds `s_j = (ε / M) · ψ(β) · S_j` of
  `exists_seeds_of_function` for a given bound `M` of the `N(S_j)` on the support of `β`.
* **`exists_relGPFamily_centre`**: the data `(U(x), V(x), S_j, W)` are given on the cylinder
  `[0, 1] × X`, and the function `β` is sc-smooth on `[0, 1] × V` only.  The family is built on
  `[0, 1] × (X|V)` with the component `U'` of the centre in `U(x) ∩ ([0, 1] × V)`, the set
  `V(x) ∩ U'`, the function `β` cut off to `U'`, and the sections `S_j` read on the restriction.
  Its domain contains the points of `U'` at which `β ≠ 0` and which lie in `W`, along their
  `G_x`-orbits.

## Reading

`U(x) ∩ ([0, 1] × V)` need not be connected, so the family of this centre covers the points of
the component `U'` only.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

section Seeds

variable {A : SEP.{u}}

/-- **Seeds from one function, with a given bound** (steps (c)–(d) of the proof of
Theorem 15.3.9, 2021 pp. 698–699).  For global sc⁺-sections `S_j`, an auxiliary norm `N`,
`ε > 0`, `M > 0` and an sc-smooth `β : X → ℝ` with support in `O ∩ {N(S_j) < M ∀ j}`, the
sc⁺-sections `s_j = (ε / M) · ψ(β) · S_j` have support in `O`, `N(s_j) ≤ ε`, and at every
`y ∈ X₁` with `β(y) ≠ 0`, (15.1) relative to `Λ₀` with the `S_j(y)` gives (15.1) with the
`s_j(y)`. -/
theorem exists_seeds_of_function_of_lt (f : A.Obj → A.W) (Λ₀ : A.W → ℚ≥0) {N : A.B.One → ℝ}
    (hN : A.B.IsAuxNorm N) {ℓ : ℕ} {S : Fin ℓ → A.Obj → A.W}
    (hS : ∀ j, A.B.IsScPlusSection (S j)) {O : Set A.Obj} {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)
    {β : A.Obj → ℝ} (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hsupp : tsupport β ⊆ O ∩ ⋂ j, {y | normW N (S j y) < M}) :
    ∃ (s : Fin ℓ → A.Obj → A.W) (hs : ∀ j, A.B.IsScPlusSection (s j)),
      (∀ j, sectionSupport A.P (s j) ⊆ O) ∧ (∀ j y, normW N (s j y) ≤ ε) ∧
      ∀ y : A.X.PObj.Level 1, β (A.X.PObj.levelVal 1 y) ≠ 0 →
        IsParamOntoVecRel f Λ₀ y
          (fun j => ⟨S j (A.X.PObj.levelVal 1 y), (hS j).1 _⟩) →
        IsParamOntoVecRel f Λ₀ y
          (fun j => ⟨s j (A.X.PObj.levelVal 1 y), (hs j).1 _⟩) := by
  classical
  set g : A.Obj → ℝ := fun y => ε / M * cutProfile (β y) with hg
  have hgsm : A.X.PObj.IsScSmoothMap realPolyfold g := by
    have h1 : A.X.PObj.IsScSmoothMap realPolyfold (cutProfile ∘ β) :=
      hβ.comp_contDiff contDiff_cutProfile
    have h2 : A.X.PObj.IsScSmoothMap realPolyfold
        ((fun t : ℝ => ε / M * t) ∘ (cutProfile ∘ β)) :=
      h1.comp_contDiff (contDiff_const.mul contDiff_id)
    exact h2
  have hg0 : ∀ y, β y = 0 → g y = 0 := fun y hy => by
    rw [hg]; dsimp only; rw [hy, cutProfile_zero, mul_zero]
  have hgne : ∀ y, β y ≠ 0 → g y ≠ 0 := fun y hy =>
    mul_ne_zero (div_pos hε hM).ne' (cutProfile_ne_zero hy)
  have hgle : ∀ y, |g y| ≤ ε / M := fun y => by
    rw [hg]; dsimp only
    rw [abs_mul, abs_of_pos (div_pos hε hM)]
    exact mul_le_of_le_one_right (div_pos hε hM).le (abs_cutProfile_le_one _)
  have hsec : ∀ j, IsSection A.P (S j) := fun j => (hS j).1
  refine ⟨fun j => Polyfold.sectionSmul A.P g (S j), fun j => (hS j).smul_left hgsm,
    fun j => ?_, fun j y => ?_, fun y hy H => ?_⟩
  · refine (closure_mono fun y hy => ?_).trans (hsupp.trans inter_subset_left)
    intro h0
    apply hy
    change Polyfold.sectionSmul A.P g (S j) y = fiberZero A.P y
    rw [sectionSmul_apply (hsec j), hg0 y h0, zero_smul]
    rfl
  · rw [normW_sectionSmul hN (hsec j) g ((hS j).mem_oneSet y)]
    by_cases hy : β y = 0
    · rw [hg0 y hy, abs_zero, zero_mul]; exact hε.le
    · have hyO : y ∈ O ∩ ⋂ j, {y | normW N (S j y) < M} := hsupp (subset_tsupport β hy)
      have hlt : normW N (S j y) < M := mem_iInter.1 hyO.2 j
      calc |g y| * normW N (S j y) ≤ ε / M * M :=
            mul_le_mul (hgle y) hlt.le (normW_nonneg hN _) (div_pos hε hM).le
        _ = ε := div_mul_cancel₀ ε hM.ne'
  · refine H.smul (a := fun _ => g (A.X.PObj.levelVal 1 y)) (fun _ => hgne _ hy) fun j => ?_
    exact Subtype.ext (sectionSmul_apply (hsec j) _)

end Seeds

section Centre

variable {A : SEP.{u}} {f : A.Obj → A.W} {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
  {Λ₀ Λ₁ : A.W → ℚ≥0} {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V)

set_option maxHeartbeats 1600000 in
-- the restricted bundle and its cylinder are unfolded in the hypotheses
/-- **The local family of one centre on the cylinder of a restriction** (steps (c)–(d) of the
proof of Theorem 15.3.9, 2021 pp. 698–699, for the explicit extension of Corollary 15.3.10 (3),
p. 699).  Let `V` be open and saturated and contain the saturated closures of the sets cut out by
the two controlling pairs.  On the cylinder `[0, 1] × X` let a centre `ϕ(x')` be given with a
natural representation on `U(x)` with the properness property, an invariant open `V(x)` with
`cl V(x) ⊆ U(x)`, a constant `c > 0` below `h − Ñ(Λ̃)` on `U(x)`, `U(x)` inside the interpolated
set and off the boundary, global sc⁺-sections `S_j` for which (15.1) relative to `Λ̃` holds at
the points of `supp(Λ̃ ∘ f̃)` in an open `W`, and a function `β`, sc-smooth on `[0, 1] × V`,
vanishing off a closed subset of `V(x) ∩ {Ñ(S_j) < M ∀ j}`.  Then the cylinder `[0, 1] × (X|V)`
carries a relative family for the restricted data on a saturated open `Q'` which contains every
`y'` with `ϕ(y')` in the component of `ϕ(x')` in `U(x) ∩ ([0, 1] × V)` such that the points
`g ∗ ϕ(y')`, `g ∈ G_x`, lie in `W` and `β` does not vanish at them. -/
theorem exists_relGPFamily_centre (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hpara : A.X.HasParacompactOrbitSpace)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ Λ₀) (hr₁ : IsTransversalPerturbation A f N₁ U₁ Λ₁)
    (hVo : IsOpen V)
    (hK₀ : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U₀ | A.B.AuxLe N₀ (f x) 1}) ⊆ V)
    (hK₁ : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U₁ | A.B.AuxLe N₁ (f x) 1}) ⊆ V)
    (x' : ((A.restr hV).cubeSEP 1).Obj) (R : (A.cubeSEP 1).X.NaturalRep (cubeRestrObj hV x'))
    (hprop : (A.cubeSEP 1).X.HasPropernessProperty R.U)
    {Vat : Set (A.cubeSEP 1).Obj} (hVat : IsOpen Vat) (hxVat : cubeRestrBase hV x' ∈ Vat)
    (hVinv : ∀ g, MapsTo (R.Φ g) Vat Vat) (hVcl : closure Vat ⊆ R.U)
    {c : ℝ} (hc : 0 < c)
    (hch : ∀ y ∈ R.U, c ≤ (1 + (collarCut₀ (cubeT y) + collarCut₁ (cubeT y))) / 2 -
      pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension Λ₀ Λ₁) y)
    (hRU : R.U ⊆ interpSet A U₀ U₁ ∩ (A.cubeSEP 1).X.PObj.boundaryᶜ)
    {ℓ : ℕ} {S : Fin ℓ → (A.cubeSEP 1).Obj → (A.cubeSEP 1).W}
    (hS : ∀ j, (A.cubeSEP 1).B.IsScPlusSection (S j)) {M : ℝ} (hM : 0 < M)
    {Wpre : Set (A.cubeSEP 1).Obj} (hWpre : IsOpen Wpre)
    (hon : ∀ y : (A.cubeSEP 1).X.PObj.Level 1, (A.cubeSEP 1).X.PObj.levelVal 1 y ∈ Wpre →
      0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1
        ((A.cubeSEP 1).X.PObj.levelVal 1 y)) →
      IsParamOntoVecRel (cubeLiftEp (n := 1) f hf.1.1.1) (cylExtension Λ₀ Λ₁) y
        (fun j => ⟨S j ((A.cubeSEP 1).X.PObj.levelVal 1 y), (hS j).1 _⟩))
    {β : (A.cubeSEP 1).Obj → ℝ}
    (hβ : (A.cubeSEP 1).X.PObj.IsScSmoothOn realPolyfold β
      ((univ : Set (Fin 1 → unitInterval)) ×ˢ V))
    {Cs : Set (A.cubeSEP 1).Obj} (hCs : IsClosed Cs) (hβCs : Function.support β ⊆ Cs)
    (hCsV : Cs ⊆ Vat ∩ {y | ∀ j, normW (collarAuxNorm A N₀ N₁) (S j y) < M}) :
    ∃ Q' : Set ((A.restr hV).cubeSEP 1).Obj, IsOpen Q' ∧
      ((A.restr hV).cubeSEP 1).X.IsSaturated Q' ∧
      Nonempty (RelGPFamily ((A.restr hV).cubeSEP 1)
        (cubeLiftEp (n := 1) (restrSec hV f hf.1.1.1) (isSection_restrSec hV hf.1.1.1))
        (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁))
        (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁))
        (interpSet (A.restr hV) (restrBase hV ⁻¹' U₀) (restrBase hV ⁻¹' U₁) ∩
          ((A.restr hV).cubeSEP 1).X.PObj.boundaryᶜ)
        (fun z => (1 + (collarCut₀ (cubeT z) + collarCut₁ (cubeT z))) / 2 -
          pointwiseNorm (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁))
            (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)) z) Q') ∧
      ∀ y' : ((A.restr hV).cubeSEP 1).Obj,
        cubeRestrBase hV y' ∈ connectedComponentIn (R.U ∩ Prod.snd ⁻¹' V)
          (cubeRestrBase hV x') →
        (∀ g, R.Φ g (cubeRestrBase hV y') ∈ Wpre ∧ β (R.Φ g (cubeRestrBase hV y')) ≠ 0) →
          y' ∈ Q' := by
  classical
  -- the restricted data
  have hF₁ := isScFredholmSectionFunctor_restrSec hV hVo hf
  have hft₁ := isScFredholmSectionTame_restrSec hV hVo hf.1 hft
  have hpara₁ := hasParacompactOrbitSpace_restr hV hVo hpara
  have hr₀' := isTransversalPerturbation_restr hV hVo hf hr₀ hK₀
  have hr₁' := isTransversalPerturbation_restr hV hVo hf hr₁ hK₁
  have hcc' := controlsCompactness_collar hF₁.1.1.1 hr₀'.1 hr₁'.1
  have hfB := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hF₁ hft₁
  have hfC := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  have h𝒰 : Nonempty ((A.restr hV).cubeSEP 1).X.GoodSystem := by
    obtain ⟨-, D, -⟩ := isStructurable_zeroMultisection (A := (A.restr hV).cubeSEP 1)
      ((A.restr hV).X.hasParacompactOrbitSpace_cubeProd (n := 1) hpara₁)
    exact ⟨D.𝒰⟩
  have hE' := isScPlusMultisection_cylExtension hr₀'.2.1 hr₁'.2.1
  have hE := isScPlusMultisection_cylExtension hr₀.2.1 hr₁.2.1
  have hEN' := pointwiseNorm_cylExtension_le hr₀'.1.1 hr₁'.1.1 hr₀'.2.1 hr₁'.2.1 hr₀'.2.2.2.1
    hr₁'.2.2.2.1
  have hNB := hcc'.1.isAuxNorm
  -- the component of the centre
  have hϕc : Continuous (cubeRestrBase hV) := continuous_cubeRestrBase hV
  have hGo : IsOpen (Prod.snd ⁻¹' V : Set (A.cubeSEP 1).Obj) := hVo.preimage continuous_snd
  have hGs : (A.cubeSEP 1).X.IsSaturated (Prod.snd ⁻¹' V : Set (A.cubeSEP 1).Obj) :=
    (cubeRestrInclusion hV hVo x'.2).isSaturated
  have hxG : cubeRestrBase hV x' ∈ (Prod.snd ⁻¹' V : Set (A.cubeSEP 1).Obj) :=
    cubeRestrBase_mem hV x'
  obtain ⟨R₁, hR₁U, hR₁Φ, hR₁Γ⟩ := (A.cubeSEP 1).X.exists_naturalRep_component R hGo hGs hxG
  generalize hUc : connectedComponentIn (R.U ∩ Prod.snd ⁻¹' V) (cubeRestrBase hV x') = Uc
  have hUc' : R₁.U = Uc := hR₁U.trans hUc
  have hUcsub : Uc ⊆ R.U ∩ Prod.snd ⁻¹' V := hUc ▸ connectedComponentIn_subset _ _
  have hUco : IsOpen Uc := hUc' ▸ R₁.isOpen_U
  have hxUc : cubeRestrBase hV x' ∈ Uc := hUc ▸ mem_connectedComponentIn ⟨R.mem_U, hxG⟩
  have hUcinv : ∀ g, MapsTo (R.Φ g) Uc Uc := fun g => by
    have := R₁.mapsTo_Φ g
    rwa [hUc', hR₁Φ] at this
  have hprop₁ : (A.cubeSEP 1).X.HasPropernessProperty R₁.U :=
    hprop.mono R₁.isOpen_U (hUc'.symm ▸ hUcsub.trans inter_subset_left)
  obtain ⟨R', hR'U, hprop', hR'Φ⟩ := exists_naturalRep_cubeRestr hV hVo x' R₁
    (hUc'.symm ▸ hUcsub.trans inter_subset_right) hprop₁
  have hR'mem : ∀ y, y ∈ R'.U ↔ cubeRestrBase hV y ∈ Uc := fun y => by
    rw [hR'U, hUc']; rfl
  have hΦ : ∀ g', ∃ g, ∀ y ∈ R'.U, cubeRestrBase hV (R'.Φ g' y) = R.Φ g (cubeRestrBase hV y) :=
    fun g' => by
      obtain ⟨g, hg⟩ := hR'Φ g'
      refine ⟨g, fun y hy => ?_⟩
      have := hg y hy
      rw [hR₁Φ] at this
      exact this
  -- the invariant set
  have hV'o : IsOpen (cubeRestrBase hV ⁻¹' (Vat ∩ Uc)) := (hVat.inter hUco).preimage hϕc
  have hV'inv : ∀ g, MapsTo (R'.Φ g) (cubeRestrBase hV ⁻¹' (Vat ∩ Uc))
      (cubeRestrBase hV ⁻¹' (Vat ∩ Uc)) := fun g' y hy => by
    obtain ⟨g, hg⟩ := hΦ g'
    have hyU : y ∈ R'.U := (hR'mem y).2 hy.2
    change cubeRestrBase hV (R'.Φ g' y) ∈ Vat ∩ Uc
    rw [hg y hyU]
    exact ⟨hVinv g hy.1, hUcinv g hy.2⟩
  have hV'cl : closure (cubeRestrBase hV ⁻¹' (Vat ∩ Uc)) ⊆ R'.U := fun y hy => by
    rw [hR'mem]
    have h1 : cubeRestrBase hV y ∈ closure (Vat ∩ Uc) := hϕc.closure_preimage_subset _ hy
    have := (A.cubeSEP 1).X.closure_inter_component_subset R hGo hVcl
      (x := cubeRestrObj hV x')
    rw [← hUc]
    exact this ⟨hUc ▸ h1, cubeRestrBase_mem hV y⟩
  -- the function
  have hCsU : Cs ⊆ R.U := fun y hy => hVcl (subset_closure (hCsV hy).1)
  have hβG : (A.cubeSEP 1).X.PObj.IsScSmoothOn realPolyfold β
      (Prod.snd ⁻¹' V : Set (A.cubeSEP 1).Obj) := by
    have h := hβ
    rw [univ_prod] at h
    exact h
  have hβ₁ : (A.cubeSEP 1).X.PObj.IsScSmoothOn realPolyfold (Uc.indicator β)
      ((univ : Set (Fin 1 → unitInterval)) ×ˢ V) := by
    rw [univ_prod, ← hUc]
    exact (A.cubeSEP 1).X.isScSmoothOn_indicator_component R hGo hβG hCs hβCs hCsU
  have hβ' := isScSmoothMap_comp_cubeRestrBase hV hβ₁
  have hβ'c : Continuous (Uc.indicator β ∘ cubeRestrBase hV) :=
    continuousOn_univ.1 hβ'.continuousOn
  have hsuppβ' : tsupport (Uc.indicator β ∘ cubeRestrBase hV) ⊆
      cubeRestrBase hV ⁻¹' (Cs ∩ Uc) := by
    intro y hy
    have h0 : Function.support (Uc.indicator β ∘ cubeRestrBase hV) ⊆
        cubeRestrBase hV ⁻¹' (Cs ∩ Uc) := fun z hz => by
      have hzU : cubeRestrBase hV z ∈ Uc := by
        by_contra h
        exact hz (indicator_of_notMem h β)
      refine ⟨hβCs fun h => hz ?_, hzU⟩
      change Uc.indicator β (cubeRestrBase hV z) = 0
      rw [indicator_of_mem hzU]
      exact h
    have h1 : cubeRestrBase hV y ∈ closure (Cs ∩ Uc) :=
      hϕc.closure_preimage_subset _ (closure_mono h0 hy)
    have hyCs : cubeRestrBase hV y ∈ Cs :=
      hCs.closure_subset (closure_mono inter_subset_left h1)
    refine ⟨hyCs, ?_⟩
    have h2 : cubeRestrBase hV y ∈ closure Uc := closure_mono inter_subset_right h1
    rw [← hUc] at h2 ⊢
    exact (A.cubeSEP 1).X.mem_component_of_mem_closure (R.isOpen_U.inter hGo)
      ⟨hCsU hyCs, cubeRestrBase_mem hV y⟩ h2
  -- the sections
  have hS' : ∀ j, ((A.restr hV).cubeSEP 1).B.IsScPlusSection
      (isoSec (cubeRestrIso hV hVo x') (S j)) :=
    fun j => isScPlusSection_isoSec_cubeRestrIso hV hVo x' (hS j)
  have hnS' : ∀ j z, normW (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁))
      (isoSec (cubeRestrIso hV hVo x') (S j) z) =
        normW (collarAuxNorm A N₀ N₁) (S j (cubeRestrBase hV z)) := fun j z => by
    rw [normW_collarAuxNorm_restr, cubeRestrFib_isoSec hV hVo x' (hS j).1]
  obtain ⟨s, hs, hsV, hsN, hsP⟩ := exists_seeds_of_function_of_lt
    (cubeLiftEp (n := 1) (restrSec hV f hf.1.1.1) (isSection_restrSec hV hf.1.1.1))
    (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)) hNB hS' hc hM hβ'
    (O := cubeRestrBase hV ⁻¹' (Vat ∩ Uc)) (fun y hy => by
      have h := hsuppβ' hy
      refine ⟨⟨(hCsV h.1).1, h.2⟩, mem_iInter.2 fun j => ?_⟩
      change normW _ _ < M
      rw [hnS']
      exact (hCsV h.1).2 j)
  -- (15.1) on the restriction
  have hW : ∀ y : ((A.restr hV).cubeSEP 1).X.PObj.Level 1,
      ((A.restr hV).cubeSEP 1).X.PObj.levelVal 1 y ∈
        cubeRestrBase hV ⁻¹' Wpre ∩ {z | (Uc.indicator β ∘ cubeRestrBase hV) z ≠ 0} →
      0 < cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)
        (cubeLiftEp (n := 1) (restrSec hV f hf.1.1.1) (isSection_restrSec hV hf.1.1.1)
          (((A.restr hV).cubeSEP 1).X.PObj.levelVal 1 y)) →
      IsParamOntoVecRel
        (cubeLiftEp (n := 1) (restrSec hV f hf.1.1.1) (isSection_restrSec hV hf.1.1.1))
        (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)) y
        (fun j => ⟨s j (((A.restr hV).cubeSEP 1).X.PObj.levelVal 1 y), (hs j).1 _⟩) := by
    intro y hyW hpos
    refine hsP y hyW.2 ?_
    have hl : cubeRestrBase hV (((A.restr hV).cubeSEP 1).X.PObj.levelVal 1 y) ∈
        (A.cubeSEP 1).X.PObj.levelSet 1 :=
      (mem_levelSet_cubeRestr_iff hV hVo _ 1).1 (levelVal_mem y)
    have hy₁ : (A.cubeSEP 1).X.PObj.levelVal 1 ((A.cubeSEP 1).X.PObj.levelMk 1 _ hl) =
        cubeRestrBase hV (((A.restr hV).cubeSEP 1).X.PObj.levelVal 1 y) :=
      (A.cubeSEP 1).X.PObj.levelVal_levelMk _ _ _
    have hpos₁ : 0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1
        ((A.cubeSEP 1).X.PObj.levelVal 1 ((A.cubeSEP 1).X.PObj.levelMk 1 _ hl))) := by
      rw [hy₁, ← cubeRestrFib_cubeLiftEp hV hf.1.1.1, ← cylExtension_restrMult hV hVo]
      exact hpos
    have H := hon ((A.cubeSEP 1).X.PObj.levelMk 1 _ hl) (by rw [hy₁]; exact hyW.1) hpos₁
    refine isParamOntoVecRel_localIso (cubeRestrIso hV hVo x') hfB hfC hE
      (eqOn_cubeLiftEp_restrSec hV hVo hf.1.1.1 x')
      (fun w _ => cylExtension_restrMult hV hVo Λ₀ Λ₁ w) (mem_univ _) hy₁.symm (fun j => ?_) H
    change cubeRestrFib hV (isoSec (cubeRestrIso hV hVo x') (S j) _) = S j _
    rw [cubeRestrFib_isoSec hV hVo x' (hS j).1, hy₁]
  -- the seed data and the family
  let SD : SeedData ((A.restr hV).cubeSEP 1) :=
    ⟨x', R', hprop', cubeRestrBase hV ⁻¹' (Vat ∩ Uc), hV'o, ⟨hxVat, hxUc⟩, hV'inv, hV'cl, ℓ, s,
      hs, hsV⟩
  have hch' : ∀ y ∈ ((A.restr hV).cubeSEP 1).X.saturation SD.R.U,
      c ≤ (1 + (collarCut₀ (cubeT y) + collarCut₁ (cubeT y))) / 2 -
        pointwiseNorm (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁))
          (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)) y := by
    rintro y ⟨a, haU, hay⟩
    obtain ⟨φ, hφs, hφt⟩ := ((A.restr hV).cubeSEP 1).X.π_eq_π_iff.1 hay
    have e1 : cubeT y = cubeT a := by rw [← hφt, ← hφs]; rfl
    have e2 : pointwiseNorm (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁))
        (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)) y =
        pointwiseNorm (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁))
          (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)) a := by
      rw [← hφt, ← hφs]; exact pointwiseNorm_tgt hcc'.1 hE' φ
    rw [e1, e2, pointwiseNorm_collarAuxNorm_cylExtension_restr hV hVo,
      ← cubeT_cubeRestrBase hV a]
    exact hch _ (hUcsub ((hR'mem a).1 haU)).1
  have hg0 : ∀ y : ((A.restr hV).cubeSEP 1).Obj,
      0 ≤ (1 + (collarCut₀ (cubeT y) + collarCut₁ (cubeT y))) / 2 -
        pointwiseNorm (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁))
          (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)) y := fun y => by
    have := collarCut_add_le_one (cubeT y)
    have := hEN' y
    linarith
  have hUsat : ((A.restr hV).cubeSEP 1).X.saturation SD.R.U ⊆
      interpSet (A.restr hV) (restrBase hV ⁻¹' U₀) (restrBase hV ⁻¹' U₁) ∩
        ((A.restr hV).cubeSEP 1).X.PObj.boundaryᶜ := by
    refine EpGroupoid.saturation_subset_of_isSaturated (X := ((A.restr hV).cubeSEP 1).X)
      (isSaturated_inter_boundary_compl hcc'.2.2.1) fun a ha => ?_
    have h := hRU (hUcsub ((hR'mem a).1 ha)).1
    exact ⟨(mem_interpSet_cubeRestr_iff hV U₀ U₁ a).2 h.1,
      fun hb => h.2 ((mem_boundary_cubeRestr_iff hV hVo a).1 hb)⟩
  have hWo : IsOpen (cubeRestrBase hV ⁻¹' Wpre ∩
      {z | (Uc.indicator β ∘ cubeRestrBase hV) z ≠ 0}) :=
    (hWpre.preimage hϕc).inter (isOpen_ne_fun hβ'c continuous_const)
  have hQo : IsOpen (⋂ k, SD.R.U ∩ SD.R.Φ k ⁻¹' (cubeRestrBase hV ⁻¹' Wpre ∩
      {z | (Uc.indicator β ∘ cubeRestrBase hV) z ≠ 0})) := isOpen_iInter_of_finite fun k =>
    (SD.R.continuousOn_Φ k).isOpen_inter_preimage SD.R.isOpen_U hWo
  refine ⟨((A.restr hV).cubeSEP 1).X.saturation (⋂ k, SD.R.U ∩ SD.R.Φ k ⁻¹'
      (cubeRestrBase hV ⁻¹' Wpre ∩ {z | (Uc.indicator β ∘ cubeRestrBase hV) z ≠ 0})),
    EpGroupoid.isOpen_saturation_of_isOpen _ hQo, EpGroupoid.isSaturated_saturation _ _,
    ⟨(SD.relGPFamily h𝒰 hfB hE' hcc'.1 hc.le hsN hch' hg0 hUsat hW).saturate hfB hE'⟩,
    fun y' hy' hall =>
      ((A.restr hV).cubeSEP 1).X.subset_saturation _ (mem_iInter.2 fun k => ?_)⟩
  have hyU : y' ∈ R'.U := (hR'mem y').2 hy'
  obtain ⟨g, hg⟩ := hΦ k
  have e := hg y' hyU
  refine ⟨hyU, ?_, ?_⟩
  · change cubeRestrBase hV (R'.Φ k y') ∈ Wpre
    rw [e]
    exact (hall g).1
  · change Uc.indicator β (cubeRestrBase hV (R'.Φ k y')) ≠ 0
    rw [e, indicator_of_mem (hUcinv g hy')]
    exact (hall g).2

end Centre

end SBLocalization

end Polyfold
