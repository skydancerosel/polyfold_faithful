import Polyfold.Chapter10.GapP2_GBundleLR

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10: **Proposition 10.4.7** (§10.4, pp. 501–502, new in the 2021 edition), with
the identity on the bundles, and Definition 8.4.2 read as `EpStrongBundle.IsLRLocal`.  Numbers
and pages are the 2021 text's.

# The local families of Proposition 10.4.7 on the bundles

## The text, paraphrased

(Proposition 10.4.7) Let `Φ, Ψ : (P : V → X, μ) → (Q : W → Y, ν)` be strong bundle equivalences
between strong bundles with the local regularity property, `|Φ| = |Ψ|`.  Then every `x ∈ X` has
a connected open neighbourhood `U(x)` with the natural `G_x`-action and an sc-smooth
`U(x) → 𝐘`, `z ↦ α_z`, such that `ν(α_z, Φ(v)) = Ψ(v)` for `v ∈ V|U(x)`, `P(v) = z`.  *Proof*
(text): a modification of that of Proposition 10.1.10 (1).

## What is formalized

* **`EpStrongBundle.proposition_10_4_7`**: the statement, with the local regularity property for
  the target only, and `U(x)` a natural representation inside any given neighbourhood of `x`.
  `proposition_10_4_7'` states it with the text's hypotheses on both bundles.
* `SEP.exists_family_of_isLRLocal` (`LocalizationLRBundleBase.lean`) is the base part; this file
  adds the identity `ν(α_z, Φ(v)) = Ψ(v)` on the bundles (written with `lrAct`, which is `ν` on
  composable pairs, `lrAct_eq`).
* Witness: `GapP2_GBundleFamilyExamples.proposition_10_4_7_hypotheses` (`Φ = Ψ = 1` on
  `ℝⁿ × ℝᵏ → ℝⁿ`).

## The proof

With `ψ₀ : ψ(x) → ϕ(x)`, the chart `Q = ψ̂₀ ∘ ψ` and the transport `H(v) = ν(ψ_{P(v)}, Ψ(v))`
(`IsStrongBundleEquivalence.exists_transport`), the map `B = H ∘ Φ⁻¹` is a strong bundle
isomorphism of `W|U(ϕ(x))` covering `γ = Q ∘ ϕ⁻¹` (Lemma 7.4.20 gives `γ(U) = U`), with
`|B(w)| = |w|` since `|Φ| = |Ψ|`.  Definition 8.4.2 gives `B = k ∗ ·`, so
`ν(ψ_z, Ψ(v)) = ν(Γ(k, ϕ(z)), Φ(v))`, and `α_z = ψ_z⁻¹ ∘ Γ(k, ϕ(z))`.  This is the proof of
`SEP.exists_family_of_isLRLocal` with the local isomorphism API of `GapP2_GLocalIso.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

section Family

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {Y : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle Y.PObj P'}
  [ParacompactSpace (pullbackSpace P' Y.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle Y B'}

namespace EpStrongBundle

/-- `|Φ| = |Ψ|` gives `|ϕ(z)| = |ψ(z)|` for the covered functors (through the zero vector). -/
theorem π_base_eq_of_orbitMap_eq {ϕ ψ : EpFunctor X Y}
    {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (hΦ : E.IsStrongBundleFunctor E' ϕ Φ)
    (hΨ : E.IsStrongBundleFunctor E' ψ Ψ) (hΦΨ : Φ.orbitMap = Ψ.orbitMap) (z : Obj) :
    Y.π (ϕ.obj z) = Y.π (ψ.obj z) := by
  have hw := congrArg E'.projFunctor.orbitMap (congrFun hΦΨ (E.toEpGroupoid.π (fiberZero P z)))
  rw [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π,
    GroupoidFunctor.orbitMap_π] at hw
  change Y.π (P' (Φ.obj (fiberZero P z))) = Y.π (P' (Ψ.obj (fiberZero P z))) at hw
  rwa [hΦ.isStrongBundleMap_obj.covers, hΨ.isStrongBundleMap_obj.covers,
    isSection_fiberZero (P := P) z] at hw

/-- `|Φ| = |Ψ|` gives `|Φ(v)| = |Ψ(v)|`. -/
theorem π_obj_eq_of_orbitMap_eq {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (hΦΨ : Φ.orbitMap = Ψ.orbitMap) (v : W) :
    E'.toGroupoidStr.π (Φ.obj v) = E'.toGroupoidStr.π (Ψ.obj v) := by
  have := congrFun hΦΨ (E.toEpGroupoid.π v)
  rwa [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π] at this

/-- **2021 Proposition 10.4.7, pp. 501–502 (new in the 2021 edition)**, with Definition 8.4.2
read as `IsLRLocal` and assumed for the target only: if `Φ, Ψ : (P, μ) → (P', ν)` are strong
bundle equivalences covering `ϕ, ψ` with `|Φ| = |Ψ|`, every `x` has natural representations
`U(x)` inside any neighbourhood `O`, with an sc-smooth `U(x) → 𝐘`, `z ↦ α_z : ϕ(z) → ψ(z)`, such
that `ν(α_z, Φ(v)) = Ψ(v)` for `P(v) = z ∈ U(x)`. -/
theorem proposition_10_4_7 {ϕ ψ : EpFunctor X Y}
    {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (hΦ : E.IsStrongBundleEquivalence E' ϕ Φ)
    (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ) (hΦΨ : Φ.orbitMap = Ψ.orbitMap)
    (hE' : E'.IsLRLocal) (x : Obj) {O : Set Obj} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ R : X.NaturalRep x, R.U ⊆ O ∧ ∃ α : Obj → Mor', X.PObj.IsScSmoothOn Y.PMor α R.U ∧
      ∀ z ∈ R.U, Y.src (α z) = ϕ.obj z ∧ Y.tgt (α z) = ψ.obj z ∧
        ∀ v, P v = z → E'.lrAct (α z) (Φ.obj v) = Ψ.obj v := by
  have hπb := π_base_eq_of_orbitMap_eq hΦ.isStrongBundleFunctor hΨ.isStrongBundleFunctor hΦΨ
  -- the chart `Q = ψ̂₀ ∘ ψ` along `ψ₀ : ψ(x) → ϕ(x)`, and the transport `H = H_ψ̂₀ ∘ Ψ`
  obtain ⟨ψ₀, hs₀, ht₀⟩ := Y.π_eq_π_iff.1 (hπb x).symm
  obtain ⟨T, -⟩ := EpFunctor.exists_transportChart hΨ.isEquivalence_base.isLocalScDiffeo_obj
    hs₀ ht₀
  obtain ⟨S, hSo, hxS, hSW, HG', hHG⟩ := hΨ.exists_transport T
  -- `Φ` near `x`
  obtain ⟨UF, UF', hxF, hiF⟩ := hΦ.isLocalStrongBundleIso_obj x
  obtain ⟨gF, ΨF, hF⟩ := hiF.exists_isLocalIso₂
  have hU₀o : IsOpen (UF ∩ S ∩ O) := (hF.base.isOpen_source.inter hSo).inter hO
  have hxU₀ : x ∈ UF ∩ S ∩ O := ⟨⟨hxF, hxS⟩, hxO⟩
  have hF₀ := hF.restrict hU₀o fun u hu => hu.1.1
  have hG₀ := hHG.restrict_image hU₀o fun u hu => hu.1.2
  -- `B = H ∘ Φ⁻¹` on `D = U_F' ∩ g_F⁻¹(U₀)`, covering `γ = Q ∘ g_F`
  have hC := hG₀.comp hF₀.symm
  have hDo : IsOpen (UF' ∩ gF ⁻¹' (UF ∩ S ∩ O)) := hF₀.base.isOpen_target
  have hxD : ϕ.obj x ∈ UF' ∩ gF ⁻¹' (UF ∩ S ∩ O) :=
    ⟨hF.base.mapsTo hxF, by rw [mem_preimage, hF.base.left_inv x hxF]; exact hxU₀⟩
  obtain ⟨R', hR'D, hR'⟩ := hE' _ _ hDo hxD
  have hCR := hC.restrict_image R'.isOpen_U hR'D
  have hγx : (T.Q ∘ gF) (ϕ.obj x) = ϕ.obj x := by
    rw [Function.comp_apply, hF.base.left_inv x hxF, T.Q_self]
  have hγπ : ∀ y ∈ R'.U, Y.π ((T.Q ∘ gF) y) = Y.π y := fun y hy => by
    have hy' := hR'D hy
    rw [Function.comp_apply, T.π_Q (hSW hy'.2.1.2), ← hπb, hF.base.right_inv y hy'.1]
  obtain ⟨himg, -⟩ := Y.lemma_7_4_20 R' hCR.base hγx hγπ
  rw [himg] at hCR
  -- `|B(w)| = |w|`
  have hπB : ∀ w, P' w ∈ R'.U → E'.toGroupoidStr.π ((fun v => E'.lrAct (T.ψ (P v)) (Ψ.obj v))
      (ΨF w)) = E'.toGroupoidStr.π w := fun w hw => by
    have hw' := hR'D hw
    have h1 : P (ΨF w) ∈ UF ∩ S ∩ O := hF₀.symm.mapsTo hw'
    rw [π_lrAct (by rw [hΨ.covers, T.src_ψ _ (hSW h1.1.2)]), ← π_obj_eq_of_orbitMap_eq hΦΨ,
      hF.right_inv hw'.1]
  -- Definition 8.4.2: `B = k ∗ ·`
  obtain ⟨k, hk⟩ := hR' _ _ hCR.isLocalIsoOn hπB
  -- the family `α_z = ψ_z⁻¹ ∘ Γ(k, ϕ(z))` on `V₀ = U₀ ∩ ϕ⁻¹(U(ϕ(x)))`
  have hV₀o : IsOpen ((UF ∩ S ∩ O) ∩ ϕ.obj ⁻¹' R'.U) :=
    (hF.base.isScSmoothOn.continuousOn.mono fun u hu => hu.1.1).isOpen_inter_preimage hU₀o
      R'.isOpen_U
  have hkey : ∀ z ∈ (UF ∩ S ∩ O) ∩ ϕ.obj ⁻¹' R'.U, ∀ v, P v = z →
      E'.lrAct (T.ψ z) (Ψ.obj v) = E'.lrAct (R'.Γ k (ϕ.obj z)) (Φ.obj v) := by
    intro z hz v hv
    have hvU : P v ∈ UF := hv ▸ hz.1.1.1
    have hΦv : P' (Φ.obj v) ∈ R'.U := by rw [hΦ.covers, hv]; exact hz.2
    have h1 := hk (Φ.obj v) hΦv
    simp only [Function.comp_apply, hF.left_inv hvU] at h1
    rw [natLift_eq_lrAct, hΦ.covers, hv] at h1
    exact h1
  have hQz : ∀ z ∈ (UF ∩ S ∩ O) ∩ ϕ.obj ⁻¹' R'.U, R'.Φ k (ϕ.obj z) = T.Q z := fun z hz => by
    have h1 := congrArg P' (hkey z hz (fiberZero P z) (isSection_fiberZero (P := P) z))
    rw [P_lrAct (E := E') (by rw [hΨ.covers, isSection_fiberZero (P := P) z, T.src_ψ _ (hSW hz.1.1.2)]),
      T.tgt_ψ _ (hSW hz.1.1.2),
      P_lrAct (E := E') (by rw [hΦ.covers, isSection_fiberZero (P := P) z, R'.src_Γ k _ hz.2]),
      R'.tgt_Γ k _ hz.2] at h1
    exact h1.symm
  have hc : ∀ z ∈ (UF ∩ S ∩ O) ∩ ϕ.obj ⁻¹' R'.U,
      Y.src (Y.inv (T.ψ z)) = Y.tgt (R'.Γ k (ϕ.obj z)) := fun z hz => by
    rw [Y.src_inv, T.tgt_ψ z (hSW hz.1.1.2), R'.tgt_Γ k _ hz.2, hQz z hz]
  have hαs : X.PObj.IsScSmoothOn Y.PMor (fun z => Y.comp (Y.inv (T.ψ z)) (R'.Γ k (ϕ.obj z)))
      ((UF ∩ S ∩ O) ∩ ϕ.obj ⁻¹' R'.U) :=
    Y.isScSmoothOn_comp_of
      (MPolyfold.IsScSmoothOn.comp Y.isScSmoothMap_inv
        (T.isScSmoothOn_ψ.mono hV₀o fun z hz => hSW hz.1.1.2) (mapsTo_univ _ _))
      (MPolyfold.IsScSmoothOn.comp (R'.isScSmoothOn_Γ k)
        (ϕ.isScSmoothMap_obj.mono hV₀o (subset_univ _)) fun z hz => hz.2) hc
  obtain ⟨R, hRV⟩ := X.theorem_7_1_13 x hV₀o ⟨hxU₀, R'.mem_U⟩
  refine ⟨R, fun u hu => (hRV hu).1.2, _, hαs.mono R.isOpen_U hRV, fun z hz => ?_⟩
  have hz' := hRV hz
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · rw [Y.src_comp _ _ (hc z hz'), R'.src_Γ k _ hz'.2]
  · rw [Y.tgt_comp _ _ (hc z hz'), Y.tgt_inv, T.src_ψ z (hSW hz'.1.1.2)]
  · have hΦv : P' (Φ.obj v) = Y.src (R'.Γ k (ϕ.obj z)) := by
      rw [hΦ.covers, hv, R'.src_Γ k _ hz'.2]
    have hΨv : P' (Ψ.obj v) = Y.src (T.ψ z) := by
      rw [hΨ.covers, hv, T.src_ψ z (hSW hz'.1.1.2)]
    rw [lrAct_comp hΦv (hc z hz'), ← hkey z hz' v hv, lrAct_inv_lrAct hΨv]

/-- **Proposition 10.4.7 with the text's hypotheses**: both strong bundles have the local
regularity property (only that of the target is used). -/
theorem proposition_10_4_7' {ϕ ψ : EpFunctor X Y}
    {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (hΦ : E.IsStrongBundleEquivalence E' ϕ Φ)
    (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ) (_hE : E.IsLRLocal) (hE' : E'.IsLRLocal)
    (hΦΨ : Φ.orbitMap = Ψ.orbitMap) (x : Obj) :
    ∃ R : X.NaturalRep x, ∃ α : Obj → Mor', X.PObj.IsScSmoothOn Y.PMor α R.U ∧
      ∀ z ∈ R.U, Y.src (α z) = ϕ.obj z ∧ Y.tgt (α z) = ψ.obj z ∧
        ∀ v, P v = z → E'.lrAct (α z) (Φ.obj v) = Ψ.obj v :=
  let ⟨R, _, h⟩ := proposition_10_4_7 hΦ hΨ hΦΨ hE' x isOpen_univ (mem_univ x)
  ⟨R, h⟩

end EpStrongBundle

end Family

/-! ### Witness -/

namespace GapP2_GBundleFamilyExamples

open StrongBundleEquivalenceExamples StrongBundleLocalizationExamples

/-- **Witness** for `EpStrongBundle.proposition_10_4_7` (and its primed form): on
`ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ` (`epSEP n k`), the bundle has the local
regularity property (`IsLRLocal`), and `Φ = Ψ = 1` is a strong bundle equivalence with
`|Φ| = |Ψ|`. -/
theorem proposition_10_4_7_hypotheses (n k : ℕ) :
    (epSEP n k).E.IsLRLocal ∧
      (epSEP n k).E.IsStrongBundleEquivalence (epSEP n k).E (EpFunctor.id _) (EpFunctor.id _) ∧
      (EpFunctor.id (epSEP n k).E.toEpGroupoid).orbitMap =
        (EpFunctor.id (epSEP n k).E.toEpGroupoid).orbitMap :=
  ⟨EpStrongBundle.isLRLocal_trivial _, EpStrongBundle.isStrongBundleEquivalence_id _, rfl⟩

end GapP2_GBundleFamilyExamples

end Polyfold
