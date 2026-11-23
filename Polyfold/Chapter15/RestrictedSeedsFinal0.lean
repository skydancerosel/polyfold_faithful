import Polyfold.Chapter15.RestrictedSeedsCentre
import Polyfold.Chapter15.RestrictedSeedsLift
import Polyfold.Chapter15.RestrictedSeedsBump
import Polyfold.Chapter15.RestrictedCobordism
import Polyfold.Chapter15.RelativeStepFamilies

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (Transversal Extension Theorem), steps (c)–(d), pp. 698–699, and
**Corollary 15.3.10 (3)**, p. 699, on the cylinder of the restriction of a strong bundle to a
saturated open subset.

# The local families on the cylinder of a restriction: the two kinds of centres

## The text, paraphrased

The proof covers the compact set `supp(Λ₀ ∘ f)` by finitely many saturated open sets which carry
local parameter families of sc⁺-multisections filling the cokernels; near the boundary, where
`(f, Λ₀)` is already in general position, no perturbation is needed.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `CentreData A f Λ₀ N U h x`: the data of `exists_centreData` at one interior point `x` of
  `supp(Λ₀ ∘ f)`, as a structure; `nonempty_centreData`.
* `CentreData.isCompact_closure_inter`, `CentreData.exists_connected`: the part of `cl N'` over
  a compact subset of `|X|` is compact and lies in a compact connected subset of `U(x)` through
  the centre.
* **`exists_relGPFamily_of_centreData`**: on the cylinder of the restriction `X|V`, the family of
  one centre covers the points over `|N'|` of the given compact set.
* **`nonempty_relGPFamily_preimage`**: the preimage of a saturated open set of the cylinder on
  which the reduced linearizations are onto carries the family with no parameters.

## Reading

The data of a centre are chosen on the cylinder `[0, 1] × X` before the set `V`; the function of
the centre is sc-smooth on `[0, 1] × V` only.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

section Data

variable {A : SEP.{u}}

/-- **The data at one interior point `x` of `supp(Λ₀ ∘ f)`** (steps (c)–(d) of the proof of
Theorem 15.3.9, 2021 pp. 698–699): the conclusion of `exists_centreData`. -/
structure CentreData (A : SEP.{u}) (f : A.Obj → A.W) (Λ₀ : A.W → ℚ≥0) (N : A.B.One → ℝ)
    (U : Set A.Obj) (h : A.Obj → ℝ) (x : A.Obj) where
  /-- the natural representation on `U(x)` -/
  R : A.X.NaturalRep x
  /-- the invariant set `V(x)` -/
  Vat : Set A.Obj
  /-- the lower bound of `h - N(Λ₀)` on `U(x)` -/
  c : ℝ
  /-- the number of sections -/
  ℓ : ℕ
  /-- the sc⁺-sections -/
  S : Fin ℓ → A.Obj → A.W
  hS : ∀ j, A.B.IsScPlusSection (S j)
  /-- the bound of the sections -/
  M : ℝ
  /-- the set on which (15.1) holds -/
  Wpre : Set A.Obj
  /-- the cover set -/
  N' : Set A.Obj
  hprop : A.X.HasPropernessProperty R.U
  hVat : IsOpen Vat
  hxVat : x ∈ Vat
  hVinv : ∀ g, MapsTo (R.Φ g) Vat Vat
  hVcl : closure Vat ⊆ R.U
  hc : 0 < c
  hch : ∀ y ∈ R.U, c ≤ h y - pointwiseNorm N Λ₀ y
  hRU : R.U ⊆ U ∩ A.X.PObj.boundaryᶜ
  hM : 0 < M
  hWpre : IsOpen Wpre
  hon : ∀ y : A.X.PObj.Level 1, A.X.PObj.levelVal 1 y ∈ Wpre →
    0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) →
    IsParamOntoVecRel f Λ₀ y (fun j => ⟨S j (A.X.PObj.levelVal 1 y), (hS j).1 _⟩)
  hN' : IsOpen N'
  hxN' : x ∈ N'
  hNinv : ∀ g, MapsTo (R.Φ g) N' N'
  hNcl : closure N' ⊆ Vat ∩ Wpre ∩ {y | ∀ j, normW N (S j y) < M}
  hconn : ∀ K : Set A.Obj, IsCompact K → K ⊆ closure N' →
    ∃ Z : Set A.Obj, IsCompact Z ∧ IsPreconnected Z ∧ K ⊆ Z ∧ x ∈ Z ∧ Z ⊆ R.U
  hBopen : IsOpen {y | ∀ j, normW N (S j y) < M}

variable {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {N : A.B.One → ℝ} {U : Set A.Obj}

/-- The data exist at every interior point of `supp(Λ₀ ∘ f)` at which `N(Λ₀) < h`. -/
theorem nonempty_centreData (hX : A.X.IsTame) (hsec : A.B.HasScPlusSectionsThrough)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hcc : ControlsCompactness A f N U) (hΛ₀ : IsScPlusMultisection A Λ₀)
    {h : A.Obj → ℝ} (hhc : Continuous h)
    {x : A.Obj} (hxU : x ∈ U) (hxb : x ∉ A.X.PObj.boundary) (hx : 0 < Λ₀ (f x))
    (hlt : pointwiseNorm N Λ₀ x < h x) : Nonempty (CentreData A f Λ₀ N U h x) := by
  obtain ⟨R, Vat, c, ℓ, S, hS, M, Wpre, N', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16⟩ := exists_centreData hX hsec hf hft hcc hΛ₀ hhc hxU hxb hx hlt
  have hB : IsOpen {y | ∀ j, normW N (S j y) < M} := by
    have e : {y | ∀ j, normW N (S j y) < M} = ⋂ j, {y | normW N (S j y) < M} := by
      ext y; simp
    rw [e]; exact isOpen_iInter_of_finite fun j => isOpen_normW_lt hcc.1.isAuxNorm (hS j) M
  exact ⟨⟨R, Vat, c, ℓ, S, hS, M, Wpre, N', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, hB⟩⟩

/-- `|Φ(g)(y)| = |y|` for `y ∈ U(x)`. -/
theorem π_natRep_Φ {x : A.Obj} (R : A.X.NaturalRep x) (g : A.X.Isotropy x) {y : A.Obj}
    (hy : y ∈ R.U) : A.X.π (R.Φ g y) = A.X.π y := by
  rw [← R.tgt_Γ g y hy, ← A.X.π_src_eq_π_tgt, R.src_Γ g y hy]

namespace CentreData

variable {h : A.Obj → ℝ} {x : A.Obj} (D : CentreData A f Λ₀ N U h x)

theorem N'_subset_U : D.N' ⊆ D.R.U := fun y hy =>
  D.hVcl (subset_closure (D.hNcl (subset_closure hy)).1.1)

/-- The part of `cl N'` over a compact subset of the orbit space is compact. -/
theorem isCompact_closure_inter {T : Set A.X.OrbitSpace} (hT : IsCompact T) :
    IsCompact (closure D.N' ∩ A.X.π ⁻¹' T) :=
  LocalPart.isCompact_inter_preimage_π
    (D.hprop.2.of_subset (closure_mono D.N'_subset_U) isClosed_closure) hT

/-- The part of `cl N'` over a compact subset of the orbit space lies in a compact connected
subset of `U(x)` through `x`. -/
theorem exists_connected {T : Set A.X.OrbitSpace} (hT : IsCompact T) :
    ∃ Z : Set A.Obj, IsCompact Z ∧ IsPreconnected Z ∧ closure D.N' ∩ A.X.π ⁻¹' T ⊆ Z ∧ x ∈ Z ∧
      Z ⊆ D.R.U :=
  D.hconn _ (D.isCompact_closure_inter hT) inter_subset_left

end CentreData

end Data

section Cylinder

variable {A : SEP.{u}} {f : A.Obj → A.W} {V : Set A.Obj}
  {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj} {Λ₀ Λ₁ : A.W → ℚ≥0}

set_option maxHeartbeats 1600000 in
-- the cylinder of the restriction is unfolded in the hypotheses
/-- **The family of one centre covers the points over `|N'|`** (steps (c)–(d) of the proof of
Theorem 15.3.9, 2021 pp. 698–699, on the cylinder of `X|V`).  Let the data of a centre `z` be
given on `[0, 1] × X`, let `Z ⊆ U(z) ∩ ([0, 1] × V)` be connected, contain `z` and the part of
`cl N'` over `T`, and let `β > 0` there be sc-smooth on `[0, 1] × V` and vanish off a closed
subset of `V(z) ∩ W ∩ {N(S_j) < M}`.  Then a saturated open set of the cylinder of `X|V`
carries a local family and contains every point lying over `T` and over `|N'|`. -/
theorem exists_relGPFamily_of_centreData (hV : A.X.IsEpSubgroupoid V)
    (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hpara : A.X.HasParacompactOrbitSpace)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ Λ₀) (hr₁ : IsTransversalPerturbation A f N₁ U₁ Λ₁)
    (hVo : IsOpen V)
    (hK₀ : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U₀ | A.B.AuxLe N₀ (f x) 1}) ⊆ V)
    (hK₁ : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U₁ | A.B.AuxLe N₁ (f x) 1}) ⊆ V)
    {z : (A.cubeSEP 1).Obj}
    (D : CentreData (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) (cylExtension Λ₀ Λ₁)
      (collarAuxNorm A N₀ N₁) (interpSet A U₀ U₁)
      (fun z => (1 + (collarCut₀ (cubeT z) + collarCut₁ (cubeT z))) / 2) z)
    {T : Set (A.cubeSEP 1).X.OrbitSpace}
    {Z : Set (A.cubeSEP 1).Obj} (hZc : IsPreconnected Z)
    (hKZ : closure D.N' ∩ (A.cubeSEP 1).X.π ⁻¹' T ⊆ Z) (hzZ : z ∈ Z) (hZU : Z ⊆ D.R.U)
    (hZV : Z ⊆ Prod.snd ⁻¹' V)
    {β : (A.cubeSEP 1).Obj → ℝ}
    (hβ : (A.cubeSEP 1).X.PObj.IsScSmoothOn realPolyfold β
      ((univ : Set (Fin 1 → unitInterval)) ×ˢ V))
    (hβpos : ∀ y ∈ closure D.N' ∩ (A.cubeSEP 1).X.π ⁻¹' T, 0 < β y)
    {Cs : Set (A.cubeSEP 1).Obj} (hCs : IsClosed Cs) (hβCs : Function.support β ⊆ Cs)
    (hCsN : Cs ⊆ D.Vat ∩ D.Wpre ∩ {y | ∀ j, normW (collarAuxNorm A N₀ N₁) (D.S j y) < D.M}) :
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
      ∀ x' : ((A.restr hV).cubeSEP 1).Obj,
        (A.cubeSEP 1).X.π (cubeRestrBase hV x') ∈ T →
        (A.cubeSEP 1).X.π (cubeRestrBase hV x') ∈ (A.cubeSEP 1).X.π '' D.N' → x' ∈ Q' := by
  obtain ⟨x₀, rfl⟩ : ∃ x₀, cubeRestrBase hV x₀ = z := by
    have hz : z ∈ range (cubeRestrBase hV) := by rw [range_cubeRestrBase]; exact hZV hzZ
    exact hz
  obtain ⟨Q', hQo, hQs, hfam, hcov⟩ := exists_relGPFamily_centre hV hd hpara hf hft hr₀ hr₁ hVo
    hK₀ hK₁ x₀ D.R D.hprop D.hVat D.hxVat D.hVinv D.hVcl D.hc D.hch D.hRU D.hS D.hM D.hWpre D.hon
    hβ hCs hβCs (fun y hy => ⟨(hCsN hy).1.1, (hCsN hy).2⟩)
  refine ⟨Q', hQo, hQs, hfam, fun x' hT hN => ?_⟩
  obtain ⟨y, hyN, hy⟩ := hN
  have hyK : y ∈ closure D.N' ∩ (A.cubeSEP 1).X.π ⁻¹' T :=
    ⟨subset_closure hyN, by rw [mem_preimage, hy]; exact hT⟩
  have hyZ : y ∈ Z := hKZ hyK
  obtain ⟨y', rfl⟩ : ∃ y', cubeRestrBase hV y' = y := by
    have hz : y ∈ range (cubeRestrBase hV) := by rw [range_cubeRestrBase]; exact hZV hyZ
    exact hz
  have hy'Q : y' ∈ Q' := by
    refine hcov y' (hZc.subset_connectedComponentIn hzZ (subset_inter hZU hZV) hyZ) fun g => ?_
    have hgN : D.R.Φ g (cubeRestrBase hV y') ∈ D.N' := D.hNinv g hyN
    refine ⟨(D.hNcl (subset_closure hgN)).1.2, (hβpos _ ⟨subset_closure hgN, ?_⟩).ne'⟩
    rw [mem_preimage, π_natRep_Φ D.R g (hZU hyZ), hy]
    exact hT
  have hπ : ((A.restr hV).cubeSEP 1).X.π y' = ((A.restr hV).cubeSEP 1).X.π x' :=
    (cubeRestr_π_eq_π_iff hV y' x').2 hy
  rw [← hQs]
  exact ⟨y', hy'Q, hπ⟩

set_option maxHeartbeats 1600000 in
-- the cylinder of the restriction is unfolded in the hypotheses
/-- **The family with no parameters near the boundary** (Theorem 15.3.9, 2021 pp. 698–699, on
the cylinder of `X|V`).  If the reduced linearizations of the explicit extension on `[0, 1] × X`
are onto at the points of `supp` in a saturated open `P`, then the preimage of `P` in the
cylinder of `X|V` is open, saturated, and carries the family with no parameters. -/
theorem nonempty_relGPFamily_preimage (hV : A.X.IsEpSubgroupoid V)
    (hpara : A.X.HasParacompactOrbitSpace)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ Λ₀) (hr₁ : IsTransversalPerturbation A f N₁ U₁ Λ₁)
    (hVo : IsOpen V)
    (hK₀ : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U₀ | A.B.AuxLe N₀ (f x) 1}) ⊆ V)
    (hK₁ : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U₁ | A.B.AuxLe N₁ (f x) 1}) ⊆ V)
    {P : Set (A.cubeSEP 1).Obj} (hPo : IsOpen P) (hPs : (A.cubeSEP 1).X.IsSaturated P)
    (hP : ∀ y : (A.cubeSEP 1).X.PObj.Level 1, (A.cubeSEP 1).X.PObj.levelVal 1 y ∈ P →
      0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1
        ((A.cubeSEP 1).X.PObj.levelVal 1 y)) →
      IsReducedOntoAtPt (cubeLiftEp (n := 1) f hf.1.1.1) (cylExtension Λ₀ Λ₁) y)
    (U' : Set ((A.restr hV).cubeSEP 1).Obj) (g : ((A.restr hV).cubeSEP 1).Obj → ℝ) :
    IsOpen (cubeRestrBase hV ⁻¹' P) ∧
      ((A.restr hV).cubeSEP 1).X.IsSaturated (cubeRestrBase hV ⁻¹' P) ∧
      Nonempty (RelGPFamily ((A.restr hV).cubeSEP 1)
        (cubeLiftEp (n := 1) (restrSec hV f hf.1.1.1) (isSection_restrSec hV hf.1.1.1))
        (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁))
        (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁)) U' g
        (cubeRestrBase hV ⁻¹' P)) := by
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
  have hE := isScPlusMultisection_cylExtension hr₀.2.1 hr₁.2.1
  have hNB := hcc'.1.isAuxNorm
  refine ⟨hPo.preimage (continuous_cubeRestrBase hV), isSaturated_preimage_cubeRestrBase hV hPs,
    ⟨RelGPFamily.zeroOn h𝒰 hNB fun x hx hpos => ?_⟩⟩
  set a := ((A.restr hV).cubeSEP 1).X.PObj.levelVal 1 x with ha
  have hl : cubeRestrBase hV a ∈ (A.cubeSEP 1).X.PObj.levelSet 1 :=
    (mem_levelSet_cubeRestr_iff hV hVo _ 1).1 (levelVal_mem x)
  have hy₁ : (A.cubeSEP 1).X.PObj.levelVal 1 ((A.cubeSEP 1).X.PObj.levelMk 1 _ hl) =
      cubeRestrBase hV a := (A.cubeSEP 1).X.PObj.levelVal_levelMk _ _ _
  have hpos₁ : 0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1
      ((A.cubeSEP 1).X.PObj.levelVal 1 ((A.cubeSEP 1).X.PObj.levelMk 1 _ hl))) := by
    rw [hy₁, ← cubeRestrFib_cubeLiftEp hV hf.1.1.1, ← cylExtension_restrMult hV hVo]
    exact hpos
  have H := hP ((A.cubeSEP 1).X.PObj.levelMk 1 _ hl) (by rw [hy₁]; exact hx) hpos₁
  exact (isReducedOntoAtLevel_localIso_iff (cubeRestrIso hV hVo a) hfB hfC hE
    (eqOn_cubeLiftEp_restrSec hV hVo hf.1.1.1 a)
    (fun w _ => cylExtension_restrMult hV hVo Λ₀ Λ₁ w) (mem_univ _) hy₁.symm).2 H

end Cylinder

end SBLocalization

end Polyfold
