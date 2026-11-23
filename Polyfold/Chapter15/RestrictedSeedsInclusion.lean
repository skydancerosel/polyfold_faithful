import Polyfold.Chapter15.RestrictedSeedsLocal
import Polyfold.Chapter15.RestrictedSeedsNatRep
import Polyfold.Chapter15.RestrictedSeedsTransfer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (Transversal Extension Theorem), steps (c)–(d), pp. 698–699, on an open
saturated part of an ep-groupoid (Proposition 7.1.22, p. 250).

# The local family of one centre on an open saturated part

## The text, paraphrased

At a point `x` of `supp(Λ₀ ∘ f)` the proof forms, from sc⁺-sections supported near `x`, the
symmetric atomic family `Λ^x_t`, and uses that the surjectivity (15.1) persists at the points of
`supp(Λ₀ ∘ f)` near `x` and, by equivariance, on a saturated open neighbourhood.

## What is formalized (namespace `Polyfold.SBLocalization`)

Let `B → C` be an inclusion of strong bundles over ep-groupoids onto the part of `C` over an
open saturated set `W` (`EpGroupoid.OpenInclusion` on the bases, a local strong bundle
isomorphism on the bundles), with sections, multisections and auxiliary norms that correspond.

* `isScPlusSection_isoSec_univ`: a global sc⁺-section of `C` gives one of `B`.
* **`exists_relGPFamily_of_openInclusion`**: from the data of one centre on `C`
  (`exists_seedCentre`) and one function `β` on `C` which is sc-smooth on `W`, has support in
  `G₀` and is non-zero at the points of `supp(Λ ∘ f) ∩ N' ∩ W`, all of which lie in the
  component of the centre in `U(x) ∩ W`: a saturated open `Q` of `B` containing every point of
  `supp(Λ' ∘ f')` over the saturation of `N'`, with a family relative to `Λ'` on `Q`.

## Reading

`U(x) ∩ W` need not be connected; the natural representation of `B` is taken on the preimage of
the component of the centre (`exists_naturalRep_component`, `OpenInclusion.pullRep`), and the
function is cut off to that component (`isScSmoothOn_indicator_component`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {B C : SEP.{u}} {W : Set C.Obj}

/-- **A global sc⁺-section of `C` gives a global sc⁺-section of `B`** along a local strong
bundle isomorphism from `B` (over all of its base) onto the part of `C` over `W`:
`z ↦ Ψ(S(ϕ z))`. -/
theorem isScPlusSection_isoSec_univ (L : StrongBundle.LocalIso B.B C.B univ W)
    {S : C.Obj → C.W} (hS : C.B.IsScPlusSection S) : B.B.IsScPlusSection (isoSec L S) := by
  have hWo : IsOpen W := L.isOpen_U'
  have hon := isScPlusSectionOn_isoSec L hWo subset_rfl
    (IsScPlusSectionOn.of_isScPlusSection hS hWo)
  obtain ⟨hP, G, hG, hGs⟩ := hon
  have huniv : ∀ y : B.Obj, y ∈ isoSet L W :=
    fun y => ⟨mem_univ _, L.base.mapsTo (mem_univ y)⟩
  exact StrongBundle.isScPlusSection_of_locally (fun p => hP p (huniv p)) fun y₀ =>
    ⟨_, isOpen_isoSet L hWo, huniv y₀, G, hGs, fun y hy => hG y hy⟩

set_option maxHeartbeats 1600000 in
-- the seed data of the atomic family on `B` are assembled from those on `C`
/-- **The local family of one centre on an open saturated part** (steps (c)–(d) of the proof of
Theorem 15.3.9, 2021 pp. 698–699).  Let `F : B.X → C.X` be the inclusion onto the open saturated
`W`, `L` the local strong bundle isomorphism over it, and let `f' = Ψ ∘ f ∘ ϕ`, `Λ' = Λ ∘ Φ`,
`N' = N ∘ Φ`.  Let `(R, V(x), S_j, M, G₀, N₁)` be the data of a centre `ϕ(x')` on `C`, with
`c ≤ g'` and `U'` over `U(x)`, and let `β` be sc-smooth on `W` with support in a closed subset
of `G₀`, non-zero at the points of `supp(Λ ∘ f) ∩ N₁ ∩ W`, which lie in the component of
`ϕ(x')` in `U(x) ∩ W`.  Then there is a saturated open `Q` of `B`, containing the points of
`supp(Λ' ∘ f')` over the saturation of `N₁`, with a family relative to `Λ'` on `Q` with domain
support in `U'` and size `≤ |t|₁ g'`. -/
theorem exists_relGPFamily_of_openInclusion (F : EpGroupoid.OpenInclusion B.X C.X W)
    (L : StrongBundle.LocalIso B.B C.B univ W) (hLF : L.ϕ = F.ϕ)
    {f' : B.Obj → B.W} {f : C.Obj → C.W} (hf' : B.E.IsScFredholmSectionFunctor f')
    (hf : C.E.IsScFredholmSectionFunctor f) {Λ' : B.W → ℚ≥0} {Λ : C.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection B Λ') (hΛ : IsScPlusMultisection C Λ)
    (hfL : EqOn f' (L.Ψ ∘ f ∘ L.ϕ) univ) (hΛL : ∀ w, Λ' w = Λ (L.Φ w))
    {N' : B.B.One → ℝ} {N : C.B.One → ℝ} (hN' : B.E.IsAuxNorm N')
    (hNL : ∀ w, normW N' w = normW N (L.Φ w)) (h𝒰 : Nonempty B.X.GoodSystem)
    {U' : Set B.Obj} (hU's : B.X.IsSaturated U') {g' : B.Obj → ℝ} (hg'0 : ∀ y, 0 ≤ g' y)
    (hg'φ : ∀ φ, g' (B.X.src φ) = g' (B.X.tgt φ))
    (x' : B.Obj) (R : C.X.NaturalRep (F.ϕ x')) (hprop : C.X.HasPropernessProperty R.U)
    {Vat G₀ N₁ : Set C.Obj} (hVo : IsOpen Vat) (hxV : F.ϕ x' ∈ Vat)
    (hVinv : ∀ g, MapsTo (R.Φ g) Vat Vat) (hVcl : closure Vat ⊆ R.U)
    {ℓ : ℕ} {S : Fin ℓ → C.Obj → C.W} (hS : ∀ j, C.B.IsScPlusSection (S j)) {M c : ℝ}
    (hM : 0 < M) (hc : 0 < c) (hG₀V : G₀ ⊆ Vat) (hG₀M : ∀ y ∈ G₀, ∀ j, normW N (S j y) < M)
    (hG₀on : ∀ y : C.X.PObj.Level 1, C.X.PObj.levelVal 1 y ∈ G₀ →
      0 < Λ (f (C.X.PObj.levelVal 1 y)) →
        IsParamOntoVecRel f Λ y (fun j => ⟨S j (C.X.PObj.levelVal 1 y), (hS j).1 _⟩))
    (hN₁o : IsOpen N₁) (hN₁G : N₁ ⊆ G₀) (hN₁inv : ∀ g, MapsTo (R.Φ g) N₁ N₁)
    (hRU' : ∀ y', F.ϕ y' ∈ R.U → y' ∈ U') (hRg : ∀ y', F.ϕ y' ∈ R.U → c ≤ g' y')
    {β : C.Obj → ℝ} (hβ : C.X.PObj.IsScSmoothOn realPolyfold β W) {Cβ : Set C.Obj}
    (hCβ : IsClosed Cβ) (hβC : support β ⊆ Cβ) (hCβG : Cβ ⊆ G₀)
    (hpos : ∀ y ∈ N₁, y ∈ W → 0 < Λ (f y) →
      y ∈ connectedComponentIn (R.U ∩ W) (F.ϕ x') ∧ β y ≠ 0) :
    ∃ Q : Set B.Obj, IsOpen Q ∧ B.X.IsSaturated Q ∧
      (∀ y', F.ϕ y' ∈ C.X.saturation N₁ → 0 < Λ' (f' y') → y' ∈ Q) ∧
      Nonempty (RelGPFamily B f' Λ' N' U' g' Q) := by
  classical
  have hLFa : ∀ z, L.ϕ z = F.ϕ z := congrFun hLF
  have hWo : IsOpen W := F.isOpen_W
  have hsecf : IsSection C.P f := hf.1.1.1
  -- `Λ' ∘ f' = Λ ∘ f ∘ ϕ`
  have hΦΨ : ∀ (v : C.W), C.P v ∈ W → L.Φ (L.Ψ v) = v := fun v hv => L.zero.right_inv v hv
  have hΛf : ∀ y, Λ' (f' y) = Λ (f (F.ϕ y)) := fun y => by
    rw [hΛL, hfL (mem_univ y)]
    simp only [Function.comp_apply]
    rw [hΦΨ _ (by rw [hsecf]; exact L.base.mapsTo (mem_univ y)), hLFa]
  -- the component of the centre and its natural representation
  set cc : Set C.Obj := connectedComponentIn (R.U ∩ W) (F.ϕ x') with hccdef
  obtain ⟨Rc, hRcU, hRcΦ, hRcΓ⟩ :=
    C.X.exists_naturalRep_component R hWo F.isSaturated (F.ϕ_mem x')
  have hccRW : cc ⊆ R.U ∩ W := connectedComponentIn_subset _ _
  have hRcW : Rc.U ⊆ W := by rw [hRcU]; exact hccRW.trans inter_subset_right
  have hRcR : Rc.U ⊆ R.U := by rw [hRcU]; exact hccRW.trans inter_subset_left
  set R' : B.X.NaturalRep x' := F.pullRep Rc hRcW with hR'def
  have hR'U : R'.U = F.ϕ ⁻¹' cc := by rw [hR'def, EpGroupoid.OpenInclusion.pullRep_U, hRcU]
  have hprop' : B.X.HasPropernessProperty R'.U :=
    F.hasPropernessProperty_preimage (hprop.mono Rc.isOpen_U hRcR)
  have hϕΦ : ∀ (k : B.X.Isotropy x') (y : B.Obj), y ∈ R'.U →
      F.ϕ (R'.Φ k y) = R.Φ (F.iso k) (F.ϕ y) := fun k y hy => by
    rw [hR'def, F.ϕ_pullRep_Φ Rc hRcW k hy, hRcΦ]
  have hccinv : ∀ (k : B.X.Isotropy x') (y : B.Obj), y ∈ R'.U → F.ϕ (R'.Φ k y) ∈ cc :=
    fun k y hy => by
      have h := R'.mapsTo_Φ k hy
      rw [hR'U] at h
      exact h
  -- the set `V(x)` on `B`
  set V' : Set B.Obj := F.ϕ ⁻¹' (Vat ∩ cc) with hV'def
  have hcco : IsOpen cc := by rw [hccdef, ← hRcU]; exact Rc.isOpen_U
  have hV'o : IsOpen V' := (hVo.inter hcco).preimage F.continuous_ϕ
  have hx'cc : F.ϕ x' ∈ cc := mem_connectedComponentIn ⟨R.mem_U, F.ϕ_mem x'⟩
  have hx'V' : x' ∈ V' := ⟨hxV, hx'cc⟩
  have hV'R' : V' ⊆ R'.U := fun y hy => by rw [hR'U]; exact hy.2
  have hV'inv : ∀ k, MapsTo (R'.Φ k) V' V' := fun k y hy => by
    refine ⟨?_, hccinv k y (hV'R' hy)⟩
    change F.ϕ (R'.Φ k y) ∈ Vat
    rw [hϕΦ k y (hV'R' hy)]
    exact hVinv _ hy.1
  have hV'cl : closure V' ⊆ R'.U := fun y hy => by
    rw [hR'U]
    have h1 : F.ϕ y ∈ closure (Vat ∩ cc) :=
      F.continuous_ϕ.closure_preimage_subset _ hy
    exact C.X.closure_inter_component_subset R hWo hVcl ⟨h1, F.ϕ_mem y⟩
  -- the sections and the function on `B`
  have hS' : ∀ j, B.B.IsScPlusSection (isoSec L (S j)) :=
    fun j => isScPlusSection_isoSec_univ L (hS j)
  have hCβU : Cβ ⊆ R.U := fun y hy => hVcl (subset_closure (hG₀V (hCβG hy)))
  have hind := C.X.isScSmoothOn_indicator_component R hWo hβ hCβ hβC hCβU
  set β' : B.Obj → ℝ := fun y => cc.indicator β (F.ϕ y) with hβ'def
  have hβ' : B.X.PObj.IsScSmoothMap realPolyfold β' :=
    MPolyfold.IsScSmoothOn.comp hind F.obj.isScSmoothOn fun y _ => F.ϕ_mem y
  have hβ'ne : ∀ y, β' y ≠ 0 → F.ϕ y ∈ cc ∧ β (F.ϕ y) ≠ 0 := fun y hy => by
    by_cases h : F.ϕ y ∈ cc
    · refine ⟨h, ?_⟩
      have e : β' y = β (F.ϕ y) := indicator_of_mem h β
      rwa [e] at hy
    · exact absurd (indicator_of_notMem h β) hy
  have hSΦ : ∀ j y, L.Φ (isoSec L (S j) y) = S j (F.ϕ y) := fun j y => by
    change L.Φ (L.Ψ (S j (L.ϕ y))) = _
    rw [hΦΨ _ (by rw [(hS j).1]; exact L.base.mapsTo (mem_univ y)), hLFa]
  have hβ'M : ∀ y, β' y ≠ 0 → ∀ j, normW N' (isoSec L (S j) y) < M := fun y hy j => by
    rw [hNL, hSΦ]
    exact hG₀M _ (hCβG (hβC (hβ'ne y hy).2)) j
  obtain ⟨s, hs, hs0, hsN, hon⟩ :=
    exists_seeds_of_function_bounded f' Λ' hN'.isAuxNorm hS' hM hc hβ' hβ'M
  have hsupp : ∀ j, sectionSupport B.P (s j) ⊆ V' := fun j y hy => by
    have h0 : {z | s j z ≠ fiberZero B.P z} ⊆ F.ϕ ⁻¹' (Cβ ∩ cc) :=
      fun z hz => ⟨hβC (hβ'ne z (hs0 j z hz)).2, (hβ'ne z (hs0 j z hz)).1⟩
    have h1 : y ∈ closure (F.ϕ ⁻¹' (Cβ ∩ cc)) := closure_mono h0 hy
    have h2 : F.ϕ y ∈ closure (Cβ ∩ cc) := F.continuous_ϕ.closure_preimage_subset _ h1
    have h3 : F.ϕ y ∈ Cβ := hCβ.closure_subset_iff.2 inter_subset_left h2
    refine ⟨hG₀V (hCβG h3), ?_⟩
    exact C.X.mem_component_of_mem_closure (R.isOpen_U.inter hWo) ⟨hCβU h3, F.ϕ_mem y⟩
      (closure_mono inter_subset_right h2)
  let Sd : SeedData B := ⟨x', R', hprop', V', hV'o, hx'V', hV'inv, hV'cl, ℓ, s, hs, hsupp⟩
  -- the bounds on the saturation of `U(x')`
  have hR'RU : ∀ y ∈ R'.U, F.ϕ y ∈ R.U := fun y hy => by
    rw [hR'U] at hy
    exact (hccRW hy).1
  have hch : ∀ y ∈ B.X.saturation Sd.R.U, c ≤ g' y := by
    rintro y ⟨a, haU, hay⟩
    obtain ⟨φ, hφs, hφt⟩ := B.X.π_eq_π_iff.1 hay
    have e1 : g' y = g' a := by rw [← hφt, ← hφs, hg'φ φ]
    rw [e1]
    exact hRg a (hR'RU a haU)
  have hUsat : B.X.saturation Sd.R.U ⊆ U' :=
    EpGroupoid.saturation_subset_of_isSaturated (X := B.X) hU's
      fun y hy => hRU' y (hR'RU y hy)
  -- (15.1) on `ϕ⁻¹(N₁)`
  set Ws : Set B.Obj := F.ϕ ⁻¹' N₁ with hWsdef
  have hWso : IsOpen Ws := hN₁o.preimage F.continuous_ϕ
  have hW : ∀ y : B.X.PObj.Level 1, B.X.PObj.levelVal 1 y ∈ Ws →
      0 < Λ' (f' (B.X.PObj.levelVal 1 y)) →
        IsParamOntoVecRel f' Λ' y
          (fun j => ⟨Sd.s j (B.X.PObj.levelVal 1 y), (Sd.isScPlusSection j).1 _⟩) := by
    intro y hyW hypos
    set q : C.Obj := F.ϕ (B.X.PObj.levelVal 1 y) with hq
    have hqN : q ∈ N₁ := hyW
    have hqpos : 0 < Λ (f q) := by rw [hq, ← hΛf]; exact hypos
    obtain ⟨hqcc, hqβ⟩ := hpos q hqN (F.ϕ_mem _) hqpos
    have hβy : β' (B.X.PObj.levelVal 1 y) ≠ 0 := by
      have e : β' (B.X.PObj.levelVal 1 y) = β q := indicator_of_mem hqcc β
      rw [e]; exact hqβ
    have hq1 : q ∈ C.X.PObj.levelSet 1 := by
      have h := (L.base.mem_levelSet_iff (mem_univ (B.X.PObj.levelVal 1 y)) 1).2
        (B.X.PObj.levelVal_mem y)
      rwa [hLFa] at h
    have hlv : C.X.PObj.levelVal 1 (C.X.PObj.levelMk 1 q hq1) = q :=
      C.X.PObj.levelVal_levelMk 1 q hq1
    have H := hG₀on (C.X.PObj.levelMk 1 q hq1) (by rw [hlv]; exact hN₁G hqN)
      (by rw [hlv]; exact hqpos)
    have H' : IsParamOntoVecRel f' Λ' y
        (fun j => ⟨isoSec L (S j) (B.X.PObj.levelVal 1 y), (hS' j).1 _⟩) :=
      isParamOntoVecRel_localIso L hf' hf hΛ hfL (fun w _ => hΛL w) (mem_univ _)
        (by rw [hlv, hLFa]) (fun j => by
          change L.Φ (isoSec L (S j) (B.X.PObj.levelVal 1 y)) =
            S j (C.X.PObj.levelVal 1 (C.X.PObj.levelMk 1 q hq1))
          rw [hSΦ, hlv]) H
    exact hon y hβy H'
  have hQo : IsOpen (⋂ k, Sd.R.U ∩ Sd.R.Φ k ⁻¹' Ws) := isOpen_iInter_of_finite fun k =>
    (Sd.R.continuousOn_Φ k).isOpen_inter_preimage Sd.R.isOpen_U hWso
  refine ⟨B.X.saturation (⋂ k, Sd.R.U ∩ Sd.R.Φ k ⁻¹' Ws),
    EpGroupoid.isOpen_saturation_of_isOpen B.X hQo, EpGroupoid.isSaturated_saturation B.X _,
    fun y' hy' hypos => ?_,
    ⟨(Sd.relGPFamily h𝒰 hf' hΛ' hN' hc.le hsN hch hg'0 hUsat hW).saturate hf' hΛ'⟩⟩
  -- the points over the saturation of `N₁`
  obtain ⟨q, hqN, hqy⟩ := hy'
  obtain ⟨φ, hφs, hφt⟩ := C.X.π_eq_π_iff.1 hqy
  have hqW : q ∈ W := by
    have h := C.X.isSaturated_iff.1 F.isSaturated (C.X.inv φ)
      (by rw [C.X.src_inv, hφt]; exact F.ϕ_mem y')
    rwa [C.X.tgt_inv, hφs] at h
  have hqpos : 0 < Λ (f q) := by
    have h := comp_tgt_eq_src hf hΛ φ
    rw [hφs, hφt] at h
    rw [← h, ← hΛf]; exact hypos
  obtain ⟨hqcc, -⟩ := hpos q hqN hqW hqpos
  have hq' : F.ϕ (F.ψ q) = q := F.ϕ_ψ hqW
  have hmem : F.ψ q ∈ ⋂ k, Sd.R.U ∩ Sd.R.Φ k ⁻¹' Ws := by
    have hU : F.ψ q ∈ R'.U := by rw [hR'U, mem_preimage, hq']; exact hqcc
    refine mem_iInter.2 fun k => ⟨hU, ?_⟩
    change F.ϕ (R'.Φ k (F.ψ q)) ∈ N₁
    rw [hϕΦ k _ hU, hq']
    exact hN₁inv _ hqN
  exact ⟨F.ψ q, hmem, (F.π_eq_π_iff _ _).2 (by rw [hq']; exact hqy)⟩

end SBLocalization

end Polyfold
