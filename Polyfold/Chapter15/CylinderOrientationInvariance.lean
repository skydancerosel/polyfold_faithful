import Polyfold.Chapter15.CylinderCanonicalOrientation
import Polyfold.Chapter12.IntervalProductLocalIso
import Polyfold.Chapter6.OrientationBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2), with Definition 12.5.4 (p. 594) and Remark 6.6.19.

# The orientation `õ = e ∧ o` of `f̃` is invariant under the morphisms of `[0, 1] × X`

## The text, paraphrased

An orientation of an sc-Fredholm section functor `f` is a continuous family `o` of orientations
of `DET(f, x)` with `φ_* o_{s(φ)} = o_{t(φ)}` for all morphisms `φ` (Definition 12.5.4).  On
`[0, 1] × X` the functor `f̃(t, x) = (t, f(x))` is oriented by the standard orientation of
`[0, 1]` and `o` (p. 703).

## What is formalized (namespace `Polyfold.SBLocalization`)

The morphisms of `[0, 1] × X` are the pairs `(t, φ)`, `φ` a morphism of `X`.

* `EpGroupoid.cubeProd_tgtInv_eq_near`: near `t(σ)` the local inverse of the target map on the
  chosen sheet of `σ = (t, φ)` is `(s, y) ↦ (s, τ_φ(y))`, `τ_φ` the local inverse on the chosen
  sheet of `φ`.
* `isIntervalProductAt_morIso_cubeSEP`: the local strong bundle isomorphism of the morphism
  `(t, φ)` is `id × (the local isomorphism of φ)` near `(t, t(φ))`.
* **`isOrInvariant_cubeOrientation`**: if `φ_* o_{s(φ)} = o_{t(φ)}` for all morphisms of `X`,
  then `(t, φ)_* õ_{(t, s(φ))} = õ_{(t, t(φ))}` for all morphisms of `[0, 1] × X`.
* **`corollary_15_4_4_oriented`**, **`corollary_15_4_4_eff_oriented`**: Corollary 15.4.4 for the
  canonical orientations of Definition 15.4.2, for `(f, o)` oriented in the sense of Definition
  12.5.4 (`o` an orientation of `f` invariant under the morphisms of `X`);
  `corollary_15_4_4_of_definition_12_5_4`: the same with `definition_12_5_4` as one hypothesis.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Module

noncomputable section

namespace Polyfold

universe u

/-! ### The sheets of `[0, 1]ⁿ × X` -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  (n : ℕ) [ParacompactSpace ((Fin n → unitInterval) × Obj)]
  [ParacompactSpace ((Fin n → unitInterval) × Mor)]

/-- **The local inverse of the target map of `[0, 1]ⁿ × X` near `t(σ)`, `σ = (q, φ)`**: on an
open neighbourhood of `t(σ)` the inverse of `t` on the chosen sheet of `σ` is
`(s, y) ↦ (s, τ_φ(y))`, `τ_φ` the inverse of `t` on the chosen sheet of `φ` (`t` is injective
on a sheet). -/
theorem cubeProd_tgtInv_eq_near (σ : (Fin n → unitInterval) × Mor) :
    ∃ N : Set ((Fin n → unitInterval) × Obj), IsOpen N ∧ (X.cubeProd n).tgt σ ∈ N ∧
      N ⊆ ((X.cubeProd n).sheetAt σ).tgtSet ∧ (∀ y ∈ N, y.2 ∈ (X.sheetAt σ.2).tgtSet) ∧
      ∀ y ∈ N, ((X.cubeProd n).sheetAt σ).tgtInv y = (y.1, (X.sheetAt σ.2).tgtInv y.2) := by
  set S := (X.cubeProd n).sheetAt σ with hS
  set S₀ := X.sheetAt σ.2 with hS₀
  have ht := S.isScDiffeoOn_tgt
  have ht₀ := S₀.isScDiffeoOn_tgt
  set τ' : (Fin n → unitInterval) × Obj → (Fin n → unitInterval) × Mor :=
    fun y => (y.1, S₀.tgtInv y.2) with hτ'
  have hopen₀ : IsOpen ((univ : Set (Fin n → unitInterval)) ×ˢ S₀.tgtSet) :=
    isOpen_univ.prod ht₀.isScSmoothOn_inv.isOpen
  have hτc : ContinuousOn τ' ((univ : Set (Fin n → unitInterval)) ×ˢ S₀.tgtSet) :=
    continuous_fst.continuousOn.prodMk
      (ht₀.isScSmoothOn_inv.continuousOn.comp continuous_snd.continuousOn fun y hy => hy.2)
  have hσ₀ : S₀.tgtInv (X.tgt σ.2) = σ.2 := ht₀.left_inv σ.2 (X.mem_sheetAt σ.2)
  refine ⟨(univ : Set (Fin n → unitInterval)) ×ˢ S₀.tgtSet ∩ τ' ⁻¹' S.carrier ∩ S.tgtSet,
    (hτc.isOpen_inter_preimage hopen₀ ht.isScSmoothOn.isOpen).inter ht.isScSmoothOn_inv.isOpen,
    ⟨⟨⟨mem_univ _, ht₀.mapsTo (X.mem_sheetAt σ.2)⟩, ?_⟩,
      ht.mapsTo ((X.cubeProd n).mem_sheetAt σ)⟩,
    fun y hy => hy.2, fun y hy => hy.1.1.2, fun y hy => ?_⟩
  · change (σ.1, S₀.tgtInv (X.tgt σ.2)) ∈ S.carrier
    rw [hσ₀]
    exact (X.cubeProd n).mem_sheetAt σ
  · have h1 : (X.cubeProd n).tgt (τ' y) = y := by
      change (y.1, X.tgt (S₀.tgtInv y.2)) = y
      rw [ht₀.right_inv y.2 hy.1.1.2]
    calc S.tgtInv y = S.tgtInv ((X.cubeProd n).tgt (τ' y)) := by rw [h1]
      _ = τ' y := ht.left_inv _ hy.1.2

end EpGroupoid

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP UnitCube

variable {A : SEP.{u}} {f : A.Obj → A.W}

/-! ### The local isomorphism of a morphism `(t, φ)` -/

/-- **The local strong bundle isomorphism of the morphism `(t, φ)` of `[0, 1] × X` is
`id × (the local isomorphism of φ)` near `(t, t(φ))`**: the base maps agree near the point
(`cubeProd_tgtInv_eq_near`) and on the fibre over it both bundle maps are `μ(φ⁻¹, ·)`
(`morIso_Φ_eq`; `μ̃((t, ψ), (t, w)) = (t, μ(ψ, w))`). -/
theorem isIntervalProductAt_morIso_cubeSEP (σ : (A.cubeSEP 1).Mor) :
    haveI := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
    haveI := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
      (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
    StrongBundle.LocalIso.IsIntervalProductAt (B := A.B) ((A.cubeSEP 1).E.morIso σ)
      (A.E.morIso σ.2) (σ.1, A.X.tgt σ.2) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  obtain ⟨N, hNo, hσN, hNS, hNS₀, hτ⟩ := A.X.cubeProd_tgtInv_eq_near 1 σ
  refine ⟨⟨N, hNo, hσN, hNS, hNS₀, fun y hy => ?_⟩, fun w hw => ?_⟩
  · change (A.X.cubeProd 1).src (((A.X.cubeProd 1).sheetAt σ).tgtInv y) = _
    rw [hτ y hy]
    rfl
  · have hw' : (A.cubeSEP 1).P w = (A.cubeSEP 1).X.tgt σ := hw
    have hw₂ : A.P w.1.2 = A.X.tgt σ.2 := w.2.trans (congrArg Prod.snd hw)
    rw [(A.cubeSEP 1).E.morIso_Φ_eq σ hw', A.E.morIso_Φ_eq σ.2 hw₂]
    rfl

/-! ### The invariance of `õ` -/

/-- **`õ = e ∧ o` is invariant under the morphisms of `[0, 1] × X`** (the second clause of
Definition 12.5.4 for `õ`; 2021 p. 703): if `φ_* o_{s(φ)} = o_{t(φ)}` for every morphism `φ` of
`X` between smooth objects, then `(t, φ)_* õ_{(t, s(φ))} = õ_{(t, t(φ))}` for every morphism
`(t, φ)` of `[0, 1] × X`.  The local isomorphism of `(t, φ)` is `id × (that of φ)` near the
point (`isIntervalProductAt_morIso_cubeSEP`), and such an isomorphism carries `e ∧ o` to
`e ∧ φ_* o` (`StrongBundle.LocalIso.orVia_ivFirstFun`). -/
theorem isOrInvariant_cubeOrientation (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (hinv : A.E.IsOrInvariant hf hsec o) :
    (A.cubeSEP 1).E.IsOrInvariant (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft) hsec'
      (cubeOrientation hf hft hsec o) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_prod ((cubePolyfold 1).prod A.X.PObj)
  have := paracompactSpace_rn_pullback (ivBundle A.B)
  intro σ z z' hz hz' hs hs'
  obtain ⟨t, φ⟩ := σ
  subst hz hz'
  have hxs : A.X.src φ ∈ A.X.PObj.smoothSet := prod_cube_mem_smoothSet_iff.1 hs
  have hx's : A.X.tgt φ ∈ A.X.PObj.smoothSet := prod_cube_mem_smoothSet_iff.1 hs'
  exact StrongBundle.LocalIso.orVia_ivFirstFun (B := A.B)
    (isIntervalProductAt_morIso_cubeSEP (A := A) (t, φ)) hf.2
    (hft.paramCube (n := 1)).toIsScFredholmSection hsec o _ _ _ _ _
    (restrPt A.B (A.X.src φ) (EpStrongBundle.isOpen_srcSet φ) (EpStrongBundle.mem_srcSet rfl)
      hxs) (restrPt_sub _ _ _ _) (EpStrongBundle.mem_tgtSet rfl) (A.E.morIso_ϕ_eq rfl rfl)
    (A.E.linSet_pullPt_mor hf hsec φ rfl rfl _ _ hxs hx's) hxs hx's
    (hinv φ rfl rfl hxs hx's)

/-! ### Corollary 15.4.4 for an oriented sc-Fredholm section functor -/

section Corollary

variable (hd : ∀ x, A.X.PObj.degIndex x = 0)
  (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
  (ho : haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    IsSectionOrientation f hf.2 o)
  (hinv : A.E.IsOrInvariant hf hsec o)
  {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))

include hd hft hsec' ho hinv hidx in
/-- **Corollary 15.4.4 (2021 p. 703; 2017: Corollary 15.2).**  Let `d_X ≡ 0`, `|X|` paracompact,
`X` with sc-smooth partitions of unity (also on `[0, 1] × X`; they are used for Stokes), and let
`(f, o)` be an oriented sc-Fredholm section functor (Definition 12.5.4: `o` is an orientation
of `f` with `φ_* o_{s(φ)} = o_{t(φ)}`) with compact solution set, tame germ data and index
`m + 1`.  Then exact forms integrate to `0` over every regular perturbation with the canonical
orientation of `(f, o)` (Definition 15.4.2), and a closed form has the same integral over any
two of them.  The cobordism `[0, 1] × X` is oriented by `õ = e ∧ o`, which is invariant under
its morphisms (`isOrInvariant_cubeOrientation`). -/
theorem corollary_15_4_4_oriented (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    (hS : A.E.HasCompactSolutionSetEp f) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_canonicalOrientation hd hf hft hsec hsec' o ho
    (isOrInvariant_cubeOrientation hf hft hsec hsec' o hinv) hidx hpara hPU hPUC hS

include hd hft hsec' ho hinv hidx in
/-- **Corollary 15.4.4, effective version (p. 703)**, for an oriented sc-Fredholm section
functor `(f, o)` (Definition 12.5.4), with the local unique continuation property on `X` and on
`[0, 1] × X`. -/
theorem corollary_15_4_4_eff_oriented (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    (hS : A.E.HasCompactSolutionSetEp f) :
    corollary_15_4_4_eff_statement A f m hLUC (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_eff_canonicalOrientation hd hf hft hsec hsec' o ho
    (isOrInvariant_cubeOrientation hf hft hsec hsec' o hinv) hidx hpara hPU hLUC hPUC hLUCC hS

end Corollary

/-- **Corollary 15.4.4 (2021 p. 703) for an orientation in the sense of Definition 12.5.4**
(p. 594): the form of `corollary_15_4_4_oriented` in which "`(f, o)` is oriented" is the single
hypothesis `definition_12_5_4` (`o` is a continuous section of `σ : O_f → X_∞`, for the topology
of Theorem 12.5.3 given by Part I's local transports, and `φ_* o_{s(φ)} = o_{t(φ)}`). -/
theorem corollary_15_4_4_of_definition_12_5_4 {A : SEP.{u}} {f : A.Obj → A.W}
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (hdef : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      haveI := paracompactSpace_rn_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_rn_pullback A.B
      A.E.definition_12_5_4 hf hsec (orTopology (orLocalTransport hX hbump hft hsec)) o)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (hpara : A.X.HasParacompactOrbitSpace) (hPU : A.X.HasScPartitionsOfUnity)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    (hS : A.E.HasCompactSolutionSetEp f) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) := by
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_rn_prod A.X.PObj
  have := paracompactSpace_rn_rn_pullback A.B
  exact corollary_15_4_4_oriented hd hf hft hsec hsec' o
    ((isSectionOrientation_iff_continuous hX hbump hft hsec o).2 hdef.1) hdef.2 hidx hpara hPU
    hPUC hS

end SBLocalization

end Polyfold
