import Polyfold.Chapter16.P3W4SM_SuppNaturality
import Polyfold.Chapter11.GapP2_HFaceIso
import Polyfold.Chapter9.GapP2_CProp919

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.4, **Proposition
16.4.3** (p. 730; 2017: Proposition 16.4): the structure on `supp θ` does not depend on the
representative.  Numbers and pages are the 2021 text's.

# Naturality of the structure on `supp θ`

## The text, paraphrased

(Proposition 16.4.3) For a branched suborbifold `θ = [(Θ, (X, α))]` of manifold type, `supp θ`
carries the manifold structure induced through `α` from `|supp Θ|` (Proposition 9.1.9 (1)), and
this structure does not depend on the representative.

## What is formalized

* `BranchedSuborbifold.suppTransition_orbitSuppProj`: for a generalized isomorphism
  `[X ←F A →Φ X']` relating two representatives (`α' ∘ |f| = α`, `f^*Θ' = Θ`), the transition
  `|supp Θ| → |supp Θ'|` sends `|F(b)|` to `|Φ(b)|` for every `b ∈ supp(Φ^*Θ')`.
* `BranchedSuborbifold.isScSmoothOn_suppTransition`: for **any** structures `PZ`, `PZ'` induced in
  the sense of Proposition 9.1.9 (1) (`IsInducedSuppStructure`) the transition is sc-smooth.
  Near `|F(b)|` it is `p' ∘ Φ|supp ∘ (F|supp)⁻¹ ∘ p⁻¹`, where `F|supp`, `Φ|supp` are the
  restrictions of the equivalences to the sub-ep-groupoids on the supports
  (`EpFunctor.IsEquivalence.restrictSub`, Proposition 11.1.6's argument) and `p`, `p'` the local
  sc-diffeomorphisms `a ↦ |a|`.  Only `Θ'` of orbifold type is used (for the sub-ep-groupoid on
  `supp(Φ^*Θ')`).
* `BranchedSuborbifold.proposition_16_4_3_naturality_all`: for any induced `PZ`, `PZ'`, the
  transition is an sc-diffeomorphism `PZ → PZ'`.
* **`BranchedSuborbifold.proposition_16_4_3_naturality`**: SM's statement
  `proposition_16_4_3_naturality_statement c` holds for every polyfold `(Z, c)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace PolyfoldClass

open EpGroupoid MPolyfold EPLocalization EPLocalization.EPLoc

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z}

namespace BranchedSuborbifold

/-- **The transition on the supports through a representative diagram**: if
`f = [X ←F A →Φ X']` relates the representatives `a`, `a'`, then for `b ∈ supp(Φ^*Θ')` the
transition sends `|F(b)|` to `|Φ(b)|`. -/
theorem suppTransition_orbitSuppProj (a a' : BranchedRep c)
    (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧) (f : EPLoc.of a.p.X ⟶ EPLoc.of a'.p.X)
    (hβ : ⇑a.p.β = ⇑a'.p.β ∘ orbitMap f) (b : (rep f).A.Obj)
    (hb : (rep f).F.obj b ∈ EpGroupoid.supp a.Θ) (hb' : (rep f).Φ.obj b ∈ EpGroupoid.supp a'.Θ) :
    suppTransition a a' h (a.p.X.X.orbitSuppProj a.Θ ⟨_, hb⟩) =
      a'.p.X.X.orbitSuppProj a'.Θ ⟨_, hb'⟩ := by
  refine (suppTransition_eq_iff a a' h _ _).2 ?_
  change a'.p.β (a'.p.X.X.π ((rep f).Φ.obj b)) = a.p.β (a.p.X.X.π ((rep f).F.obj b))
  have ho : orbitMap f = (rep f).orbitMap := by rw [← orbitMap_homMk, homMk_rep]
  rw [hβ, Function.comp_apply, ho]
  exact congrArg a'.p.β ((rep f).orbitMap_orbitMap_F ((rep f).A.X.π b)).symm

/-- **The transition between the supports is sc-smooth** for any structures `PZ`, `PZ'` induced
as in Proposition 9.1.9 (1) (2021 Proposition 16.4.3, p. 730), when `Θ'` is of orbifold type. -/
theorem isScSmoothOn_suppTransition (a a' : BranchedRep c)
    (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧) (ho' : EpGroupoid.IsOrbifoldType a'.Θ)
    [ParacompactSpace (a.p.X.X.orbitSupp a.Θ)] [T2Space (a.p.X.X.orbitSupp a.Θ)]
    [ParacompactSpace (a'.p.X.X.orbitSupp a'.Θ)] [T2Space (a'.p.X.X.orbitSupp a'.Θ)]
    {PZ : MPolyfold (a.p.X.X.orbitSupp a.Θ)} {PZ' : MPolyfold (a'.p.X.X.orbitSupp a'.Θ)}
    (hPZ : IsInducedSuppStructure a PZ) (hPZ' : IsInducedSuppStructure a' PZ') :
    PZ.IsScSmoothOn PZ' (suppTransition a a' h) univ := by
  classical
  obtain ⟨f, hf, hβ, hΘ⟩ := Quotient.exact h
  obtain ⟨hA, -, hloc⟩ := hPZ
  obtain ⟨hA', -, hloc'⟩ := hPZ'
  have := a.p.X.X.PObj.paracompactSpace_subtype (EpGroupoid.supp a.Θ)
  have := a'.p.X.X.PObj.paracompactSpace_subtype (EpGroupoid.supp a'.Θ)
  set d := rep f with hddef
  have hF := d.isEquivalence_F
  have hΦ := isEquivalence_rep_Φ hf
  set ΘA := d.Φ.pullbackTheta a'.Θ with hΘAdef
  have hΘA := EpFunctor.isBranchedEpSubgroupoid_pullbackTheta hΦ a'.isBranched
  have hoA : EpGroupoid.IsOrbifoldType ΘA := fun x => ho' (d.Φ.obj x)
  have hSA := isEpSubgroupoid_supp_of_isOrbifoldType hΘA hoA
  have := d.A.X.PObj.paracompactSpace_subtype (EpGroupoid.supp ΘA)
  have hΘeq : d.F.pushforwardTheta ΘA = a.Θ := hΘ
  have hmemF : ∀ b, b ∈ EpGroupoid.supp ΘA ↔ d.F.obj b ∈ EpGroupoid.supp a.Θ := fun b => by
    change 0 < ΘA b ↔ 0 < a.Θ (d.F.obj b)
    rw [← hΘeq, EpFunctor.pushforwardTheta_obj hF.full hΘA.isFunctorial]
  have hmemΦ : ∀ b, b ∈ EpGroupoid.supp ΘA ↔ d.Φ.obj b ∈ EpGroupoid.supp a'.Θ := fun _ => Iff.rfl
  set Fs := d.F.restrictSub hSA hA hmemF with hFsdef
  set Φs := d.Φ.restrictSub hSA hA' hmemΦ with hΦsdef
  have hFs := (hF.restrictSub hSA hA hmemF).isLocalScDiffeo_obj
  have hΦs := Φs.isScSmoothMap_obj
  have key : ∀ b : EpGroupoid.supp ΘA,
      suppTransition a a' h (a.p.X.X.orbitSuppProj a.Θ (Fs.obj b)) =
      a'.p.X.X.orbitSuppProj a'.Θ (Φs.obj b) := fun b =>
    suppTransition_orbitSuppProj a a' h f hβ b.1 ((hmemF b.1).1 b.2) ((hmemΦ b.1).1 b.2)
  refine IsScSmoothOn.of_locally isOpen_univ fun q _ => ?_
  -- `q = |F(b)|`
  obtain ⟨b, rfl⟩ : ∃ b : EpGroupoid.supp ΘA, a.p.X.X.orbitSuppProj a.Θ (Fs.obj b) = q := by
    obtain ⟨_, x, hx, rfl⟩ := q
    obtain ⟨y, ψ, hs, ht⟩ := hF.exists_iso x
    have hψs : a.p.X.X.src ψ ∈ EpGroupoid.supp a.Θ :=
      src_mem_of_tgt_mem_of_isSaturated hA.isSaturated (by rw [ht]; exact hx)
    have hy : y ∈ EpGroupoid.supp ΘA := (hmemF y).2 (hs ▸ hψs)
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change a.p.X.X.π (d.F.obj y) = a.p.X.X.π x
    exact (GroupoidStr.π_eq_π_iff _).2 ⟨ψ, hs, ht⟩
  -- local inverses of `p` and of `F|supp`
  obtain ⟨U₁, V₁, g₁, hU₁, hd₁⟩ := hloc (Fs.obj b)
  obtain ⟨U₂, V₂, g₂, hU₂, hd₂⟩ := hFs b
  set V := V₁ ∩ g₁ ⁻¹' V₂ with hVdef
  have hV : IsOpen V := hd₁.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage
    hd₁.isScSmoothOn_inv.isOpen hd₂.isScSmoothOn_inv.isOpen
  have hqV : a.p.X.X.orbitSuppProj a.Θ (Fs.obj b) ∈ V := by
    refine ⟨hd₁.mapsTo hU₁, ?_⟩
    change g₁ _ ∈ V₂
    rw [hd₁.left_inv _ hU₁]
    exact hd₂.mapsTo hU₂
  refine ⟨V, hV, hqV, subset_univ _, ?_⟩
  have hg₁ : PZ.IsScSmoothOn (subEpGroupoid hA).PObj g₁ V :=
    hd₁.isScSmoothOn_inv.mono hV inter_subset_left
  have hg₂ := IsScSmoothOn.comp hd₂.isScSmoothOn_inv hg₁ fun z hz => hz.2
  have hΦg := IsScSmoothOn.comp hΦs hg₂ (mapsTo_univ _ _)
  have hG := IsScSmoothOn.comp (hloc'.isScSmoothMap) hΦg (mapsTo_univ _ _)
  refine hG.congr fun z hz => ?_
  have h1 : g₁ z ∈ U₁ := hd₁.mapsTo_inv hz.1
  have h2 : a.p.X.X.orbitSuppProj a.Θ (g₁ z) = z := hd₁.right_inv z hz.1
  have h3 : Fs.obj (g₂ (g₁ z)) = g₁ z := hd₂.right_inv _ hz.2
  change a'.p.X.X.orbitSuppProj a'.Θ (Φs.obj (g₂ (g₁ z))) = suppTransition a a' h z
  rw [← key, h3, h2]

/-- **2021 Proposition 16.4.3, p. 730, independence of the representative, for all induced
structures**: for two representatives `a`, `a'` of one `θ` with `Θ`, `Θ'` of orbifold type and
any M-polyfold structures `PZ`, `PZ'` induced as in Proposition 9.1.9 (1), the transition
`|supp Θ| ≃ₜ |supp Θ'|` is an sc-diffeomorphism. -/
theorem proposition_16_4_3_naturality_all (a a' : BranchedRep c)
    (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧) (ho : EpGroupoid.IsOrbifoldType a.Θ)
    (ho' : EpGroupoid.IsOrbifoldType a'.Θ)
    [ParacompactSpace (a.p.X.X.orbitSupp a.Θ)] [T2Space (a.p.X.X.orbitSupp a.Θ)]
    [ParacompactSpace (a'.p.X.X.orbitSupp a'.Θ)] [T2Space (a'.p.X.X.orbitSupp a'.Θ)]
    {PZ : MPolyfold (a.p.X.X.orbitSupp a.Θ)} {PZ' : MPolyfold (a'.p.X.X.orbitSupp a'.Θ)}
    (hPZ : IsInducedSuppStructure a PZ) (hPZ' : IsInducedSuppStructure a' PZ') :
    PZ.IsScDiffeoOn PZ' (suppTransition a a' h) (suppTransition a' a h.symm) univ univ where
  isScSmoothOn := isScSmoothOn_suppTransition a a' h ho' hPZ hPZ'
  isScSmoothOn_inv := isScSmoothOn_suppTransition a' a h.symm ho hPZ' hPZ
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv q _ := suppTransition_symm a a' h q
  right_inv q _ := suppTransition_symm a' a h.symm q

/-- **2021 Proposition 16.4.3, p. 730 (2017: Proposition 16.4), independence of the
representative (manifold type)**: SM's statement holds.  The structures are those of
Proposition 9.1.9 (1); by `proposition_16_4_3_naturality_all` any induced structures would do. -/
theorem proposition_16_4_3_naturality (c : PolyfoldClass Z) :
    proposition_16_4_3_naturality_statement c := by
  intro a a' h hm hm'
  have := a.isBranched.paracompactSpace_orbitSupp
  have := a'.isBranched.paracompactSpace_orbitSupp
  obtain ⟨hA, hsub, PZ, hPZ⟩ := a.p.X.X.proposition_9_1_9_one a.isBranched hm
  obtain ⟨hA', hsub', PZ', hPZ'⟩ := a'.p.X.X.proposition_9_1_9_one a'.isBranched hm'
  exact ⟨PZ, PZ', ⟨hA, hsub, hPZ⟩, ⟨hA', hsub', hPZ'⟩,
    proposition_16_4_3_naturality_all a a' h hm.1 hm'.1 ⟨hA, hsub, hPZ⟩ ⟨hA', hsub', hPZ'⟩⟩

end BranchedSuborbifold

end PolyfoldClass

end Polyfold
