import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_24

set_option maxSynthPendingDepth 3

/-! Round trip for V16_24 (2021 Proposition 16.4.3, p. 730; 2017: Proposition 16.6: the structure
on `supp θ`).

`A` is the conjunction of the types of the item's thirteen theorems, at universe `0`:
`proposition_16_4_3_supp` (`supp ⟦a⟧ = α(|supp Θ|)`), `_manifold`, `_orbifold` (Proposition
9.1.9 (1)/(2) on each representative, with `|supp Θ| ≃ₜ supp θ`), the transition lemmas
(`β_suppTransition`, `suppTransition_eq_iff/_self/_trans/_symm`, `suppTransition_orbitSuppProj`),
`isScSmoothOn_suppTransition`, `proposition_16_4_3_naturality_self/_all` (any induced structures,
orbifold-type representatives) and `proposition_16_4_3_naturality` (manifold type, some induced
structures).

* `A_to_B`: (0) from `_supp`; (M1) from `_manifold` (with `definition_16_4_2_manifold`);
  (M2) from `_naturality_all`, after identifying `B`'s `e, g` with `suppTransition`
  (`suppTransition_eq_iff`); (O1), (O2) from `_orbifold` (with `definition_16_4_2_orbifold`),
  composing with `|supp Θ| ≃ₜ supp θ` built from `_supp`.  **(O3) is not in `A`**: `A` says
  nothing about the orbifold structures of two representatives being equivalent.  It is proved
  here outright (`o3`) from non-item machinery: the restriction `X|supp Θ ← A|supp Θ_A →
  X'|supp Θ'` of a representative diagram (`EpFunctor.restrictSub`,
  `IsEquivalence.restrictSub`, `theorem_10_3_10`), as in the project's proof of
  `isScSmoothOn_suppTransition`.
* `B_to_A`: `_supp`, `_manifold`, `_orbifold`, `_naturality_self` and `_naturality` from `B`
  ((0), (M1), (O1), (O2), (M2)); the transition lemmas, `isScSmoothOn_suppTransition` and
  `_naturality_all` are re-proved outright (the project's proofs, copied): the last two are
  stated for orbifold-type representatives with arbitrary induced structures, beyond `B`'s
  manifold-type hypothesis.

**Harness note.** `A` mentions `suppTransition`, built from the definition
`proposition_16_4_3_homeomorph`, whose abstracted proof field is the banned
`proposition_16_4_3_supp`; plain `#rt_check` fails (recorded with `#guard_msgs`) and
`#rt_check_soft` passes. -/

namespace RoundTrip.V16_24
open Polyfold Polyfold.PolyfoldClass Polyfold.PolyfoldClass.BranchedSuborbifold
open Set Function Topology CategoryTheory
open Polyfold.EpGroupoid Polyfold.MPolyfold Polyfold.EPLocalization Polyfold.EPLocalization.EPLoc

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_manifold.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_orbifold.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.β_suppTransition.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_eq_iff.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_self.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_trans.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_symm.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_self.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_orbitSuppProj.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.isScSmoothOn_suppTransition.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality.{0})

theorem A_holds : A :=
  ⟨@Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp.{0},
    @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_manifold.{0},
    @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_orbifold.{0},
    @Polyfold.PolyfoldClass.BranchedSuborbifold.β_suppTransition.{0},
    @Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_eq_iff.{0},
    @Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_self.{0},
    @Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_trans.{0},
    @Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_symm.{0},
    @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_self.{0},
    @Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_orbitSuppProj.{0},
    @Polyfold.PolyfoldClass.BranchedSuborbifold.isScSmoothOn_suppTransition.{0},
    @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_all.{0},
    @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality.{0}⟩

/-! ### The equivalence of the orbifold structures (`B`'s (O3)), from the project's machinery -/

section O3
variable {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z}

theorem o3 (a a' : BranchedRep c) (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧)
    (ho' : EpGroupoid.IsOrbifoldType a'.Θ)
    (hA : a.p.X.X.IsEpSubgroupoid (EpGroupoid.supp a.Θ))
    (hA' : a'.p.X.X.IsEpSubgroupoid (EpGroupoid.supp a'.Θ)) :
    ∃ 𝔥 : ({ toEP := a.p.X.sub hA } : EPLocalization.EPLoc) ⟶ { toEP := a'.p.X.sub hA' },
      EPLocalization.EPLoc.IsGeneralizedIso 𝔥 ∧
      ∀ (x : (a.p.X.sub hA).Obj) (y : (a'.p.X.sub hA').Obj),
        EPLocalization.EPLoc.orbitMap 𝔥 (Quotient.mk _ x) = Quotient.mk _ y →
          a'.p.β (Quotient.mk _ y.1) = a.p.β (Quotient.mk _ x.1) := by
  classical
  obtain ⟨f, hf, hβ, hΘ⟩ := Quotient.exact h
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
  let D : Diagram (a.p.X.sub hA) (a'.p.X.sub hA') :=
    { A := d.A.sub hSA
      F := d.F.restrictSub hSA hA hmemF
      isEquivalence_F := hF.restrictSub hSA hA hmemF
      Φ := d.Φ.restrictSub hSA hA' hmemΦ }
  have hDΦ : D.Φ.IsEquivalence := hΦ.restrictSub hSA hA' hmemΦ
  refine ⟨homMk D, (theorem_10_3_10 D).1.2 hDΦ, fun x y hxy => ?_⟩
  rw [orbitMap_homMk] at hxy
  -- `|x| = |F|supp (b)|`
  obtain ⟨y0, ψ, hs, ht⟩ := D.isEquivalence_F.exists_iso x
  have hx : D.F.orbitMap (D.A.X.π y0) = (a.p.X.sub hA).X.π x := by
    rw [GroupoidFunctor.orbitMap_π]
    exact (GroupoidStr.π_eq_π_iff _).2 ⟨ψ, hs, ht⟩
  have h1 := D.orbitMap_orbitMap_F (D.A.X.π y0)
  rw [hx] at h1
  change D.orbitMap (Quotient.mk _ x) = _ at h1
  rw [hxy, GroupoidFunctor.orbitMap_π] at h1
  -- project to `X'` and `X`
  have hy : (Quotient.mk _ y.1 : a'.p.X.X.OrbitSpace) = a'.p.X.X.π (d.Φ.obj y0.1) :=
    congrArg (EP.subFunctor _ hA').orbitMap h1
  have hx' : (Quotient.mk _ x.1 : a.p.X.X.OrbitSpace) = a.p.X.X.π (d.F.obj y0.1) :=
    (congrArg (EP.subFunctor _ hA).orbitMap hx).symm
  rw [hy, hx']
  have ho : orbitMap f = (rep f).orbitMap := by rw [← orbitMap_homMk, homMk_rep]
  rw [hβ, Function.comp_apply, ho]
  exact congrArg a'.p.β ((rep f).orbitMap_orbitMap_F ((rep f).A.X.π y0.1)).symm

end O3


/-- `|supp Θ| ≃ₜ supp θ` through `α`, from a given `supp ⟦a⟧ = α(|supp Θ|)`. -/
noncomputable def homOf {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z} (a : BranchedRep c)
    (hS : supp ⟦a⟧ = a.p.β '' a.p.X.X.orbitSupp a.Θ) :
    a.p.X.X.orbitSupp a.Θ ≃ₜ supp ⟦a⟧ :=
  (a.p.β.image _).trans (Homeomorph.setCongr hS.symm)

theorem A_to_B : A → B := by
  rintro ⟨hsupp, hman, horb, -, heqiff, -, -, -, -, -, -, hall, -⟩
  intro Z _ c θ
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    subst ha
    exact (hsupp a).symm
  · intro hθ
    have hθ' := (definition_16_4_2_manifold θ).1 hθ
    refine ⟨?_, ?_⟩
    · intro a ha _ _
      obtain ⟨-, hA, hsub, PZ, hPZ⟩ := hman a (hθ' a ha)
      exact ⟨PZ, hA, hsub, hPZ⟩
    · intro a a' ha ha' _ _ _ _ PZ PZ' hPZ hPZ' e g he hg
      have h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧ := ha.trans ha'.symm
      have hee : e = suppTransition a a' h :=
        funext fun x => ((heqiff a a' h x (e x)).2 (he x)).symm
      have hgg : g = suppTransition a' a h.symm :=
        funext fun y => ((heqiff a' a h.symm y (g y)).2 (hg y)).symm
      subst hee hgg
      exact hall a a' h (hθ' a ha).1 (hθ' a' ha').1 hPZ hPZ'
  · intro hθ
    have hθ' := (definition_16_4_2_orbifold θ).1 hθ
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨-, hA, hsub, -⟩ := horb a (hθ' a ha)
      exact ⟨hA, hsub⟩
    · intro a ha hA
      subst ha
      obtain ⟨-, hA0, -, e, he⟩ := horb a (hθ' a rfl)
      exact ⟨e.trans (homOf a (hsupp a)), fun x => congrArg a.p.β (he x)⟩
    · intro a a' ha ha' hA hA'
      exact o3 a a' (ha.trans ha'.symm) (hθ' a' ha') hA hA'

/-! ### Copies of the project's proofs of the elementary transition lemmas and of the
sc-smoothness of the transition (for orbifold-type representatives), used in `B_to_A` -/

section Copies
variable {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z}

theorem β_suppTransition' (a a' : BranchedRep c) (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧)
    (q : a.p.X.X.orbitSupp a.Θ) :
    a'.p.β (suppTransition a a' h q : a'.p.X.X.OrbitSpace) = a.p.β q := by
  rw [← proposition_16_4_3_homeomorph_apply a', suppTransition, Homeomorph.trans_apply,
    Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  rfl

theorem suppTransition_eq_iff' (a a' : BranchedRep c) (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧)
    (q : a.p.X.X.orbitSupp a.Θ) (q' : a'.p.X.X.orbitSupp a'.Θ) :
    suppTransition a a' h q = q' ↔ a'.p.β q' = a.p.β q := by
  constructor
  · rintro rfl; exact β_suppTransition' a a' h q
  · intro hq
    exact Subtype.ext (a'.p.β.injective ((β_suppTransition' a a' h q).trans hq.symm))

theorem suppTransition_self' (a : BranchedRep c) (q : a.p.X.X.orbitSupp a.Θ) :
    suppTransition a a rfl q = q :=
  (suppTransition_eq_iff' a a rfl q q).2 rfl

theorem suppTransition_trans' (a a' a'' : BranchedRep c)
    (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧) (h' : (⟦a'⟧ : BranchedSuborbifold c) = ⟦a''⟧)
    (q : a.p.X.X.orbitSupp a.Θ) :
    suppTransition a' a'' h' (suppTransition a a' h q) = suppTransition a a'' (h.trans h') q :=
  (suppTransition_eq_iff' _ _ _ _ _).2 <| by
    rw [β_suppTransition', β_suppTransition']

theorem suppTransition_symm' (a a' : BranchedRep c) (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧)
    (q : a.p.X.X.orbitSupp a.Θ) : suppTransition a' a h.symm (suppTransition a a' h q) = q :=
  (suppTransition_trans' a a' a h h.symm q).trans (suppTransition_self' a q)

theorem suppTransition_orbitSuppProj' (a a' : BranchedRep c)
    (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧) (f : EPLoc.of a.p.X ⟶ EPLoc.of a'.p.X)
    (hβ : ⇑a.p.β = ⇑a'.p.β ∘ orbitMap f) (b : (rep f).A.Obj)
    (hb : (rep f).F.obj b ∈ EpGroupoid.supp a.Θ) (hb' : (rep f).Φ.obj b ∈ EpGroupoid.supp a'.Θ) :
    suppTransition a a' h (a.p.X.X.orbitSuppProj a.Θ ⟨_, hb⟩) =
      a'.p.X.X.orbitSuppProj a'.Θ ⟨_, hb'⟩ := by
  refine (suppTransition_eq_iff' a a' h _ _).2 ?_
  change a'.p.β (a'.p.X.X.π ((rep f).Φ.obj b)) = a.p.β (a.p.X.X.π ((rep f).F.obj b))
  have ho : orbitMap f = (rep f).orbitMap := by rw [← orbitMap_homMk, homMk_rep]
  rw [hβ, Function.comp_apply, ho]
  exact congrArg a'.p.β ((rep f).orbitMap_orbitMap_F ((rep f).A.X.π b)).symm

theorem isScSmoothOn_suppTransition' (a a' : BranchedRep c)
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
    suppTransition_orbitSuppProj' a a' h f hβ b.1 ((hmemF b.1).1 b.2) ((hmemΦ b.1).1 b.2)
  refine IsScSmoothOn.of_locally isOpen_univ fun q _ => ?_
  obtain ⟨b, rfl⟩ : ∃ b : EpGroupoid.supp ΘA, a.p.X.X.orbitSuppProj a.Θ (Fs.obj b) = q := by
    obtain ⟨_, x, hx, rfl⟩ := q
    obtain ⟨y, ψ, hs, ht⟩ := hF.exists_iso x
    have hψs : a.p.X.X.src ψ ∈ EpGroupoid.supp a.Θ :=
      src_mem_of_tgt_mem_of_isSaturated hA.isSaturated (by rw [ht]; exact hx)
    have hy : y ∈ EpGroupoid.supp ΘA := (hmemF y).2 (hs ▸ hψs)
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change a.p.X.X.π (d.F.obj y) = a.p.X.X.π x
    exact (GroupoidStr.π_eq_π_iff _).2 ⟨ψ, hs, ht⟩
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

theorem proposition_16_4_3_naturality_all' (a a' : BranchedRep c)
    (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧) (ho : EpGroupoid.IsOrbifoldType a.Θ)
    (ho' : EpGroupoid.IsOrbifoldType a'.Θ)
    [ParacompactSpace (a.p.X.X.orbitSupp a.Θ)] [T2Space (a.p.X.X.orbitSupp a.Θ)]
    [ParacompactSpace (a'.p.X.X.orbitSupp a'.Θ)] [T2Space (a'.p.X.X.orbitSupp a'.Θ)]
    {PZ : MPolyfold (a.p.X.X.orbitSupp a.Θ)} {PZ' : MPolyfold (a'.p.X.X.orbitSupp a'.Θ)}
    (hPZ : IsInducedSuppStructure a PZ) (hPZ' : IsInducedSuppStructure a' PZ') :
    PZ.IsScDiffeoOn PZ' (suppTransition a a' h) (suppTransition a' a h.symm) univ univ where
  isScSmoothOn := isScSmoothOn_suppTransition' a a' h ho' hPZ hPZ'
  isScSmoothOn_inv := isScSmoothOn_suppTransition' a' a h.symm ho hPZ' hPZ
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv q _ := suppTransition_symm' a a' h q
  right_inv q _ := suppTransition_symm' a' a h.symm q

end Copies

theorem B_to_A : B → A := by
  intro hB
  have hS : ∀ {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z} (a : BranchedRep c),
      supp ⟦a⟧ = a.p.β '' a.p.X.X.orbitSupp a.Θ :=
    fun a => ((hB _ _ ⟦a⟧).1 a rfl).symm
  -- `B`'s (M1): the induced structure on every manifold-type representative
  have hM1 : ∀ {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z} (a : BranchedRep c),
      a.p.X.X.IsManifoldType a.Θ →
      ∀ [ParacompactSpace ↑(a.p.X.X.orbitSupp a.Θ)] [T2Space ↑(a.p.X.X.orbitSupp a.Θ)],
        ∃ PZ : MPolyfold ↑(a.p.X.X.orbitSupp a.Θ), IsInducedSuppStructure a PZ :=
    fun a hm => ((hB _ _ ⟦a⟧).2.1 ⟨a, rfl, hm⟩).1 a rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z _ c a; exact hS a
  · intro Z _ c a hm
    have := a.isBranched.paracompactSpace_orbitSupp
    obtain ⟨PZ, hA, hsub, hloc⟩ := hM1 a hm
    exact ⟨⟨homOf a (hS a)⟩, hA, hsub, PZ, hloc⟩
  · intro Z _ c a ho
    have hθ : BranchedSuborbifold.IsOrbifoldType (⟦a⟧ : BranchedSuborbifold c) := ⟨a, rfl, ho⟩
    obtain ⟨hA, hsub⟩ := ((hB _ _ ⟦a⟧).2.2 hθ).1 a rfl
    obtain ⟨e, he⟩ := ((hB _ _ ⟦a⟧).2.2 hθ).2.1 a rfl hA
    refine ⟨⟨homOf a (hS a)⟩, hA, hsub, e.trans (homOf a (hS a)).symm, fun x => ?_⟩
    have := a.p.X.X.PObj.paracompactSpace_subtype (EpGroupoid.supp a.Θ)
    have hmem : a.p.X.X.π x.1 ∈ a.p.X.X.orbitSupp a.Θ := ⟨x.1, x.2, rfl⟩
    have h1 : e ((subEpGroupoid hA).π x) = homOf a (hS a) ⟨_, hmem⟩ :=
      Subtype.ext (he x)
    change (((homOf a (hS a)).symm (e ((subEpGroupoid hA).π x)) : _) : a.p.X.X.OrbitSpace) = _
    rw [h1, Homeomorph.symm_apply_apply]
  · intro Z _ c a a' h q; exact β_suppTransition' a a' h q
  · intro Z _ c a a' h q q'; exact suppTransition_eq_iff' a a' h q q'
  · intro Z _ c a q; exact suppTransition_self' a q
  · intro Z _ c a a' a'' h h' q; exact suppTransition_trans' a a' a'' h h' q
  · intro Z _ c a a' h q; exact suppTransition_symm' a a' h q
  · intro Z _ c a hm
    have := a.isBranched.paracompactSpace_orbitSupp
    obtain ⟨PZ, hPZ⟩ := hM1 a hm
    refine ⟨PZ, hPZ, ?_⟩
    exact ((MPolyfold.isScDiffeoOn_id isOpen_univ).congr_left
      fun q _ => (suppTransition_self' a q).symm).congr_right
      fun q _ => (suppTransition_self' a q).symm
  · intro Z _ c a a' h f hβ b hb hb'; exact suppTransition_orbitSuppProj' a a' h f hβ b hb hb'
  · intro Z _ c a a' h ho' _ _ _ _ PZ PZ' hPZ hPZ'
    exact isScSmoothOn_suppTransition' a a' h ho' hPZ hPZ'
  · intro Z _ c a a' h ho ho' _ _ _ _ PZ PZ' hPZ hPZ'
    exact proposition_16_4_3_naturality_all' a a' h ho ho' hPZ hPZ'
  · intro Z _ c a a' h hm hm'
    have := a.isBranched.paracompactSpace_orbitSupp
    have := a'.isBranched.paracompactSpace_orbitSupp
    obtain ⟨PZ, hPZ⟩ := hM1 a hm
    obtain ⟨PZ', hPZ'⟩ := hM1 a' hm'
    refine ⟨PZ, PZ', hPZ, hPZ', ?_⟩
    exact ((hB _ _ ⟦a⟧).2.1 ⟨a, rfl, hm⟩).2 a a' rfl h.symm PZ PZ' hPZ hPZ'
      (suppTransition a a' h) (suppTransition a' a h.symm)
      (β_suppTransition' a a' h) (β_suppTransition' a' a h.symm)

/-- The text's claim, as stated by the project: the set, the manifold- and orbifold-type
structures on each representative, and the independence of the representative
(`proposition_16_4_3_naturality`). -/
def Amain : Prop :=
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_manifold.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_orbifold.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality.{0})

theorem main_B_to_A : B → Amain := fun h =>
  let hA := B_to_A h
  ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.2.2.2.2.2.2.2.2.2⟩

/--
error: rt_check FAIL: RoundTrip.V16_24.A_to_B uses [Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V16_24.A_to_B [Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_manifold, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_orbifold, Polyfold.PolyfoldClass.BranchedSuborbifold.β_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_eq_iff, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_trans, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_symm, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_orbitSuppProj, Polyfold.PolyfoldClass.BranchedSuborbifold.isScSmoothOn_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_all, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality]
/--
error: rt_check FAIL: RoundTrip.V16_24.B_to_A uses [Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V16_24.B_to_A [Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_manifold, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_orbifold, Polyfold.PolyfoldClass.BranchedSuborbifold.β_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_eq_iff, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_trans, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_symm, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_orbitSuppProj, Polyfold.PolyfoldClass.BranchedSuborbifold.isScSmoothOn_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_all, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality]
/--
error: rt_check FAIL: RoundTrip.V16_24.main_B_to_A uses [Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V16_24.main_B_to_A [Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_manifold, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_orbifold, Polyfold.PolyfoldClass.BranchedSuborbifold.β_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_eq_iff, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_trans, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_symm, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_orbitSuppProj, Polyfold.PolyfoldClass.BranchedSuborbifold.isScSmoothOn_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_all, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality]
#rt_check_soft RoundTrip.V16_24.A_to_B [Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_manifold, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_orbifold, Polyfold.PolyfoldClass.BranchedSuborbifold.β_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_eq_iff, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_trans, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_symm, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_orbitSuppProj, Polyfold.PolyfoldClass.BranchedSuborbifold.isScSmoothOn_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_all, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality]
#rt_check_soft RoundTrip.V16_24.B_to_A [Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_manifold, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_orbifold, Polyfold.PolyfoldClass.BranchedSuborbifold.β_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_eq_iff, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_trans, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_symm, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_orbitSuppProj, Polyfold.PolyfoldClass.BranchedSuborbifold.isScSmoothOn_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_all, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality]
#rt_check_soft RoundTrip.V16_24.main_B_to_A [Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_manifold, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_orbifold, Polyfold.PolyfoldClass.BranchedSuborbifold.β_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_eq_iff, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_trans, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_symm, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_orbitSuppProj, Polyfold.PolyfoldClass.BranchedSuborbifold.isScSmoothOn_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_all, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality]
#rt_overlap RoundTrip.V16_24.B_to_A [Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_supp, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_manifold, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_orbifold, Polyfold.PolyfoldClass.BranchedSuborbifold.β_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_eq_iff, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_trans, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_symm, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_self, Polyfold.PolyfoldClass.BranchedSuborbifold.suppTransition_orbitSuppProj, Polyfold.PolyfoldClass.BranchedSuborbifold.isScSmoothOn_suppTransition, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality_all, Polyfold.PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality]

end RoundTrip.V16_24
