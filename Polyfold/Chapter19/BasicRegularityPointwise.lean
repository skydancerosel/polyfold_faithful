import Polyfold.Chapter19.PolyfoldStructureExamples
import Polyfold.Chapter10.EpFormsFunctor

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.5 (p. 890): **Proposition 19.5.9** ((LUC) and (SLUC) of a basic construction pass to the
polyfold `(S, F, M)`).  Numbers and pages are the 2021 text's.

# (LUC) and (SLUC) from the basic construction to the polyfold

## The text, paraphrased

(Proposition 19.5.9) Let `(F, 𝓕)` be a basic construction with metrizable natural topology `T`
and `(F, M)` the associated polyfold structure.  Then the polyfold `S = (S, F, M)` satisfies
(LUC), (SLUC) respectively, provided the basic construction satisfies (LUC), (SLUC)
respectively.  No proof is given.

## What is formalized

Pointwise (LUC) for ep-groupoids (namespace `Polyfold.EpGroupoid`):
* `IsLUCAt X x` (a natural representation at `x` with the property of Definition 7.2.18),
  `isLUC_iff_forall_isLUCAt`;
* `NaturalRep.HasLUC.of_subset` (the property passes to a shrinking with the same action);
* **`isLUCAt_tgt`**: (LUC) at `s(φ)` gives (LUC) at `t(φ)` (Chapter 7's `transportRep` along a
  sheet of `φ`, `φ̂ ∘ Φ(γ⁻¹hγ) ∘ φ̂⁻¹`), `isLUCAt_of_isomorphic`.

Along functors (namespace `Polyfold.EpFunctor`):
* **`isLUCAt_obj`**: for a full functor `F` which is a local sc-diffeomorphism on objects, (LUC)
  at `x` gives (LUC) at `F(x)` (`Φ_{F(x)}(F φ) = F ∘ Φ_x(φ) ∘ F⁻¹` near `F(x)`, by uniqueness of
  sections of `s` over connected sets);
* `full_liftOne` (the lift `F¹` of a full functor is full).

Raised ep-groupoids (namespace `Polyfold.EP`; `liftFunctor F i : Xⁱ → Yⁱ` is Chapter 10's):
`isLocalScDiffeo_liftFunctor`, `full_liftFunctor`, `liftVal_liftFunctor_obj`;
`liftVal_mem_levelSet` (the point under a point of `Xⁱ` has level `i`), `exists_liftMor` (a
morphism between the points under two points of `Xⁱ` lifts to `Xⁱ`), `isGenIsoInvariant_isLUC_lift`
((LUC) of `Xⁱ` is invariant under generalized isomorphisms, Proposition 10.1.16 for the lifts).

For a basic construction (namespace `Polyfold.GroupoidalCategory.BasicConstruction`):
`exists_isLUC_lift_model` (under (LUC) for `(Fⁱ, 𝓕ⁱ)`, the `i`-th lift of the model of the family
of the uniformizers `Ψ_z` has (LUC)), `isLUCLevel_zero_of_isLUC`, **`proposition_19_5_9`**.

Witnesses: `reflectionBasic_proposition_19_5_9` (the reflection `ℤ/2 ⋉ ℝ`, isotropy `ℤ/2` at `0`:
the polyfold satisfies (LUC)), `z3Basic_proposition_19_5_9` (`ℤ/3 ⋉ ℝ` with the trivial action,
isotropy `ℤ/3` everywhere: the polyfold satisfies (SLUC)).

## Readings

* (LUC) and (SLUC) for `(F, 𝓕)` are those of `BasicRegularity.lean` (`IsLUC`, `IsSLUC`; the group
  `G` read as the stabilizer `G_ō`, the levels `(Fⁱ, 𝓕ⁱ)` read through the raised `(G ⋉ O)ⁱ`);
  for the polyfold they are Definition 17.1.22 ((LUC), (SLUC) of some model `X_Ψ`).
* The proof the text omits: every object of the model of the family `(Ψ_z)_{z ∈ |S|}` is
  isomorphic to the point `ō_z` of the piece of `Ψ_z` (Lemma 17.1.15), the piece functor
  `G ⋉ O → X_Ψ` is full and a local sc-diffeomorphism on objects, and (LUC) at a point passes
  along both.  For (SLUC) the same argument on every lift `X_Ψⁱ`, with one family for each `i`;
  the comparison maps `f_{Ψ,Ψ'}` (Theorem 17.1.18) are generalized isomorphisms, under which
  (LUC) of `Xⁱ` is invariant, so one model has (LUC) on all lifts.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

/-! ### (LUC) at a point -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **(LUC) at a point `x`** (Definition 7.2.18 at `x`): some natural representation of `G_x`
has the local unique continuation property. -/
def IsLUCAt (x : Obj) : Prop := ∃ R : X.NaturalRep x, R.HasLUC

theorem isLUC_iff_forall_isLUCAt : X.IsLUC ↔ ∀ x, X.IsLUCAt x := Iff.rfl

variable {X}

/-- The local unique continuation property passes to a natural representation on a smaller
neighbourhood with the same action. -/
theorem NaturalRep.HasLUC.of_subset {x : Obj} {R R' : X.NaturalRep x} (h : R.HasLUC)
    (hU : R'.U ⊆ R.U) (hΦ : R'.Φ = R.Φ) : R'.HasLUC := by
  intro g V hVo hVne hVU hV y hy
  rw [hΦ] at hV ⊢
  exact h g V hVo hVne (hVU.trans hU) hV y (hU hy)

/-- **(LUC) passes along morphisms**: (LUC) at `s(φ)` gives (LUC) at `t(φ)`.  The natural
representation transported along a sheet `𝐒` of `φ` (`transportRep`) acts by
`φ̂ ∘ Φ(γ⁻¹ h γ) ∘ φ̂⁻¹`, so the property passes through the sc-diffeomorphism `φ̂`. -/
theorem isLUCAt_tgt {φ : Mor} (h : X.IsLUCAt (X.src φ)) : X.IsLUCAt (X.tgt φ) := by
  obtain ⟨R₀, hR₀⟩ := h
  obtain ⟨R, S, hRU, hRΦ, -, -, hS, hy⟩ := NatRepFinite.exists_spoke R₀ rfl
  have hR : R.HasLUC := hR₀.of_subset hRU hRΦ
  have hD := NatRepFinite.isScDiffeoOn_hat_transportSet hS
  refine ⟨NatRepFinite.transportRep hS hy, fun k V hVo hVne hVU hV z hz => ?_⟩
  set g := NatRepFinite.transportConj hS hy k
  have hΦ : ∀ w, (NatRepFinite.transportRep hS hy).Φ k w =
      S.hat (R.Φ g (NatRepFinite.back S w)) := fun w => rfl
  have hV'o : IsOpen (R.U ∩ S.hat ⁻¹' V) :=
    hD.isScSmoothOn.continuousOn.isOpen_inter_preimage R.isOpen_U hVo
  have hV'ne : (R.U ∩ S.hat ⁻¹' V).Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    have hvT : v ∈ NatRepFinite.transportSet R S := hVU hv
    refine ⟨NatRepFinite.back S v, NatRepFinite.back_mem hS hvT, ?_⟩
    change S.hat (NatRepFinite.back S v) ∈ V
    rw [NatRepFinite.hat_back hS hvT]
    exact hv
  have hall := hR g _ hV'o hV'ne inter_subset_left fun u hu => by
    have e := hV (S.hat u) hu.2
    rw [hΦ, NatRepFinite.back_hat hS hu.1] at e
    have e' := congrArg (NatRepFinite.back S) e
    rwa [NatRepFinite.back_hat hS (R.mapsTo_Φ g hu.1), NatRepFinite.back_hat hS hu.1] at e'
  have hzT : z ∈ NatRepFinite.transportSet R S := hz
  rw [hΦ, hall _ (NatRepFinite.back_mem hS hzT), NatRepFinite.hat_back hS hzT]

/-- (LUC) is a property of the isomorphism class. -/
theorem isLUCAt_of_isomorphic {φ : Mor} {x y : Obj} (hs : X.src φ = x) (ht : X.tgt φ = y)
    (h : X.IsLUCAt x) : X.IsLUCAt y := by
  subst hs ht
  exact isLUCAt_tgt h

end EpGroupoid

/-! ### (LUC) along full functors which are local sc-diffeomorphisms on objects -/

namespace EpFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y)

/-- **(LUC) passes along a full functor which is a local sc-diffeomorphism on objects**: (LUC) at
`x` gives (LUC) at `F(x)`.  On a natural representation `U(F(x)) ⊆ F(U(x))` (with `F|U(x)` an
sc-diffeomorphism), `Γ_{F(x)}(F φ, ·) = F ∘ Γ_x(φ, ·) ∘ F⁻¹` (both are sections of `s` over a
connected set, equal at `F(x)`), so `Φ_{F(x)}(F φ) = F ∘ Φ_x(φ) ∘ F⁻¹`; every element of
`G_{F(x)}` is some `F φ` since `F` is full. -/
theorem isLUCAt_obj (hd : X.PObj.IsLocalScDiffeo Y.PObj F.obj) (hfull : F.toFunctor.Full)
    {x : Obj} (h : X.IsLUCAt x) : Y.IsLUCAt (F.obj x) := by
  obtain ⟨R₀, hR₀⟩ := h
  obtain ⟨W, W', σ, hxW, hD₀⟩ := hd x
  obtain ⟨R, hRU, hRΦ, -⟩ := X.exists_naturalRep_shrink R₀ hD₀.isOpen_source hxW
  have hR : R.HasLUC := hR₀.of_subset (fun y hy => (hRU hy).2) hRΦ
  have hRW : R.U ⊆ W := fun y hy => (hRU hy).1
  have hD := hD₀.restrict R.isOpen_U hRW
  rw [← hD.image_eq] at hD
  obtain ⟨RY, hRY⟩ := Y.theorem_7_1_13 (F.obj x) hD.isOpen_target (mem_image_of_mem _ R.mem_U)
  refine ⟨RY, fun k V hVo hVne hVU hV w hw => ?_⟩
  obtain ⟨φ, hφs, hφt, hφe⟩ := (F.full_iff.1 hfull) x x k.val k.src_val k.tgt_val
  let g : X.Isotropy x := ⟨φ, hφs, hφt⟩
  have hσ : ∀ w ∈ RY.U, σ w ∈ R.U := fun w hw => hD.mapsTo_inv (hRY hw)
  have hsec : EqOn (RY.Γ k) (fun w => F.mor (R.Γ g (σ w))) RY.U := by
    refine eqOn_sections_of_isPreconnected Y.isLocalScDiffeo_src.isLocallyInjective
      RY.isConnected_U.isPreconnected (RY.isScSmoothOn_Γ k).continuousOn ?_
      (fun z hz => RY.src_Γ k z hz) (fun z hz => ?_) RY.mem_U ?_
    · exact (continuousOn_univ.1 F.isScSmoothMap_mor.continuousOn).comp_continuousOn
        ((R.isScSmoothOn_Γ g).continuousOn.comp
          (hD.isScSmoothOn_inv.continuousOn.mono hRY) fun z hz => hσ z hz)
    · rw [F.src_mor, R.src_Γ g _ (hσ z hz), hD.right_inv z (hRY hz)]
    · rw [RY.Γ_self, hD.left_inv x R.mem_U, R.Γ_self]
      exact hφe.symm
  have hΦY : ∀ w ∈ RY.U, RY.Φ k w = F.obj (R.Φ g (σ w)) := fun w hw => by
    rw [← RY.tgt_Γ k w hw, hsec hw, F.tgt_mor, R.tgt_Γ g _ (hσ w hw)]
  have hV'o : IsOpen (R.U ∩ F.obj ⁻¹' V) := R.isOpen_U.inter (hVo.preimage hd.continuous)
  have hV'ne : (R.U ∩ F.obj ⁻¹' V).Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    obtain ⟨u, hu, rfl⟩ := hRY (hVU hv)
    exact ⟨u, hu, hv⟩
  have hall := hR g _ hV'o hV'ne inter_subset_left fun u hu => by
    have e := hV (F.obj u) hu.2
    rw [hΦY _ (hVU hu.2), hD.left_inv u hu.1] at e
    have e' := congrArg σ e
    rwa [hD.left_inv _ (R.mapsTo_Φ g hu.1), hD.left_inv u hu.1] at e'
  rw [hΦY w hw, hall _ (hσ w hw), hD.right_inv w (hRY hw)]

variable {F}

/-- **The lift `F¹ : X¹ → Y¹` of a full functor is full** (the argument of
`IsEquivalence.liftOne`). -/
theorem full_liftOne (hfull : F.toFunctor.Full) : F.liftOne.toFunctor.Full := by
  refine (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => ?_
  have hs' : Y.src (Y.PMor.levelVal 1 ψ) = F.obj (X.PObj.levelVal 1 x) :=
    congrArg (Y.PObj.levelVal 1) hs
  have ht' : Y.tgt (Y.PMor.levelVal 1 ψ) = F.obj (X.PObj.levelVal 1 x') :=
    congrArg (Y.PObj.levelVal 1) ht
  obtain ⟨φ, hφs, hφt, hφ⟩ := (F.full_iff.1 hfull) _ _ _ hs' ht'
  have hφ1 : φ ∈ X.PMor.levelSet 1 :=
    (X.mem_levelSet_src_iff φ 1).1 (hφs ▸ MPolyfold.levelVal_mem x)
  refine ⟨X.PMor.levelMk 1 φ hφ1, MPolyfold.level_ext ?_, MPolyfold.level_ext ?_,
    MPolyfold.level_ext ?_⟩
  · rw [X.liftOne_src_val, MPolyfold.levelVal_levelMk, hφs]
  · rw [X.liftOne_tgt_val, MPolyfold.levelVal_levelMk, hφt]
  · change F.mor (X.PMor.levelVal 1 (X.PMor.levelMk 1 φ hφ1)) = _
    rw [MPolyfold.levelVal_levelMk, hφ]

end EpFunctor

/-! ### Raised ep-groupoids: lifted functors, levels, lifted morphisms -/

namespace EP

variable {A B : EP.{u}} {F : EpFunctor A.X B.X}

theorem isLocalScDiffeo_liftFunctor (hd : A.X.PObj.IsLocalScDiffeo B.X.PObj F.obj) :
    ∀ i, (A.lift i).X.PObj.IsLocalScDiffeo (B.lift i).X.PObj (liftFunctor F i).obj
  | 0 => hd
  | i + 1 => (isLocalScDiffeo_liftFunctor hd i).levelOne

theorem full_liftFunctor (hfull : F.toFunctor.Full) :
    ∀ i, (liftFunctor F i).toFunctor.Full
  | 0 => hfull
  | i + 1 => EpFunctor.full_liftOne (full_liftFunctor hfull i)

/-- `Fⁱ` lies over `F`. -/
theorem liftVal_liftFunctor_obj (F : EpFunctor A.X B.X) :
    ∀ (i : ℕ) (p : (A.lift i).Obj), B.liftVal i ((liftFunctor F i).obj p) = F.obj (A.liftVal i p)
  | 0, _ => rfl
  | i + 1, p => liftVal_liftFunctor_obj F i ((A.lift i).X.PObj.levelVal 1 p)

/-- **The point under a point of `(Xⁱ)_m` has level `i + m`.** -/
theorem liftVal_mem_levelSet (A : EP.{u}) :
    ∀ (i m : ℕ) (p : (A.lift i).Obj), p ∈ (A.lift i).X.PObj.levelSet m →
      A.liftVal i p ∈ A.X.PObj.levelSet (i + m)
  | 0, m, p, hp => by rw [Nat.zero_add]; exact hp
  | i + 1, m, p, hp => by
    have h := A.liftVal_mem_levelSet i (m + 1) ((A.lift i).X.PObj.levelVal 1 p)
      ((MPolyfold.mem_shift_levelSet_iff p).1 hp)
    rwa [show i + (m + 1) = i + 1 + m by omega] at h

/-- The point under a point of `Xⁱ` has level `i`. -/
theorem liftVal_mem_levelSet_self (A : EP.{u}) (i : ℕ) (p : (A.lift i).Obj) :
    A.liftVal i p ∈ A.X.PObj.levelSet i := by
  have := A.liftVal_mem_levelSet i 0 p (by rw [MPolyfold.levelSet_zero]; exact mem_univ p)
  rwa [Nat.add_zero] at this

/-- **Morphisms lift to `Xⁱ`**: a morphism of `X` between the points under `p, p'` of `Xⁱ` lifts
to a morphism `p → p'` of `Xⁱ` (its source has level `i`, hence so has the morphism). -/
theorem exists_liftMor (A : EP.{u}) :
    ∀ (i : ℕ) (p p' : (A.lift i).Obj) (ψ : A.Mor), A.X.src ψ = A.liftVal i p →
      A.X.tgt ψ = A.liftVal i p' →
      ∃ ψ' : (A.lift i).Mor, (A.lift i).X.src ψ' = p ∧ (A.lift i).X.tgt ψ' = p'
  | 0, _, _, ψ, hs, ht => ⟨ψ, hs, ht⟩
  | i + 1, p, p', ψ, hs, ht => by
    obtain ⟨ψ'', hs'', ht''⟩ := A.exists_liftMor i ((A.lift i).X.PObj.levelVal 1 p)
      ((A.lift i).X.PObj.levelVal 1 p') ψ hs ht
    have h1 : ψ'' ∈ (A.lift i).X.PMor.levelSet 1 :=
      ((A.lift i).X.mem_levelSet_src_iff ψ'' 1).1 (hs'' ▸ MPolyfold.levelVal_mem p)
    refine ⟨(A.lift i).X.PMor.levelMk 1 ψ'' h1, ?_, ?_⟩
    · change (A.lift i).X.liftOne.src ((A.lift i).X.PMor.levelMk 1 ψ'' h1) = p
      refine MPolyfold.level_ext ?_
      rw [(A.lift i).X.liftOne_src_val, MPolyfold.levelVal_levelMk, hs'']
    · change (A.lift i).X.liftOne.tgt ((A.lift i).X.PMor.levelMk 1 ψ'' h1) = p'
      refine MPolyfold.level_ext ?_
      rw [(A.lift i).X.liftOne_tgt_val, MPolyfold.levelVal_levelMk, ht'']

open EPLocalization EPLocalization.EPLoc in
/-- **(LUC) of `Xⁱ` is invariant under generalized isomorphisms** (Proposition 10.1.16 applied to
the lifts of an equivalence, as in Proposition 10.1.18). -/
theorem isGenIsoInvariant_isLUC_lift (i : ℕ) :
    GCT.PolyfoldConstruction.IsGenIsoInvariant fun A : EP.{u} => (A.lift i).X.IsLUC :=
  fun hf => iff_of_isGeneralizedIso (fun A : EP.{u} => (A.lift i).X.IsLUC)
    (fun _ hF => by
      obtain ⟨G, hG⟩ := EP.exists_isEquivalence_lift hF i
      exact EpFunctor.proposition_10_1_16 hG) hf

end EP

/-! ### Proposition 19.5.9 -/

namespace GroupoidalCategory.BasicConstruction

open EpGroupoid.Examples GCT.PolyfoldConstruction

variable {C : GroupoidalCategory.{u}} {B : C.BasicConstruction} {hB : B.U.HasClassUniformizers}
  (hm : @MetrizableSpace C.OrbitSpace (B.natTop hB))

/-- **(LUC) for `(Fⁱ, 𝓕ⁱ)` gives (LUC) of the `i`-th lift of a model**: for the covering family
of the uniformizers `Ψ_z` (`z ∈ |S|`) of (LUC) for `(Fⁱ, 𝓕ⁱ)`, every object of `X_Ψⁱ` is
isomorphic to the image of the point `ōⁱ_z` under the lifted piece functor `(G ⋉ O)ⁱ → X_Ψⁱ`. -/
theorem exists_isLUC_lift_model (i : ℕ) (h : B.IsLUCLevel i) :
    ∃ c : (toPolyfoldConstruction hm).CoveringFamily,
      (((toPolyfoldConstruction hm).modelEP c.Ψ).lift i).X.IsLUC := by
  set S := toPolyfoldConstruction hm
  have key : ∀ z : C.OrbitSpace, ∃ (α : C.Obj) (Ψ : C.Uniformizer) (_ : Ψ ∈ B.U.F α),
      C.π α = z ∧ (B.IsLevelClass i z → ∃ p : (Ψ.toEP.lift i).Obj,
        Ψ.obj (Ψ.toEP.liftVal i p) = α ∧ (Ψ.toEP.lift i).X.IsLUCAt p) := by
    intro z
    by_cases hz : B.IsLevelClass i z
    · obtain ⟨α, Ψ, hΨ, p, hα, hp, hL⟩ := h z hz
      exact ⟨α, Ψ, hΨ, hα, fun _ => ⟨p, hp, hL⟩⟩
    · obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
      exact ⟨α, Ψ, hΨ, hα, fun h' => absurd h' hz⟩
  choose α Ψ hΨ hα hy using key
  let Φ : C.OrbitSpace → S.Unif := fun z => ⟨toLocalUniformizer hm (hΨ z), α z, hΨ z⟩
  have hcov : ⋃ z, (Φ z).1.footprint = univ := eq_univ_of_forall fun z => mem_iUnion.2
    ⟨z, by
      obtain ⟨-, hz⟩ := B.theorem_19_2_2_three hB (hΨ z)
      rw [hα z] at hz
      exact hz⟩
  refine ⟨⟨C.OrbitSpace, Φ, hcov⟩, fun p' => ?_⟩
  change (((S.modelEP Φ).lift i).X).IsLUCAt p'
  have hmem := (S.modelEP Φ).liftVal_mem_levelSet_self i p'
  rcases hyv : (S.modelEP Φ).liftVal i p' with ⟨j, q⟩
  rw [hyv] at hmem
  have hq : q ∈ (Ψ j).P.levelSet i :=
    ((MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (Φ i).1.P) j).mem_levelSet_iff q i).1 hmem
  have hz : B.IsLevelClass i (C.π ((Ψ j).obj q)) := ⟨⟨Ψ j, α j, hΨ j⟩, q, hq, rfl⟩
  set z := C.π ((Ψ j).obj q) with hzdef
  obtain ⟨p, hpo, hL⟩ := hy z hz
  have hc := continuous_hat hm (Φ z)
  let F : EpFunctor (Ψ z).toEP.X (S.modelEP Φ).X := pieceFunctor Φ z hc
  have hLF : ((S.modelEP Φ).lift i).X.IsLUCAt ((EP.liftFunctor F i).obj p) :=
    (EP.liftFunctor F i).isLUCAt_obj
      (EP.isLocalScDiffeo_liftFunctor (isLocalScDiffeo_pieceFunctor_obj Φ z hc) i)
      (EP.full_liftFunctor (full_pieceFunctor Φ z hc) i) hL
  obtain ⟨φ, hφs, hφt⟩ := C.π_eq_π_iff.1
    (show C.π ((Ψ z).obj ((Ψ z).toEP.liftVal i p)) = C.π ((Ψ j).obj q) by rw [hpo, hα z])
  let ψ : S.ModelMor Φ := ⟨(z, j), ⟨(Ψ z).toEP.liftVal i p, φ, q, hφs, hφt⟩⟩
  obtain ⟨ψ', hs', ht'⟩ := (S.modelEP Φ).exists_liftMor i ((EP.liftFunctor F i).obj p) p' ψ
    (by rw [EP.liftVal_liftFunctor_obj]; rfl) (by rw [hyv]; rfl)
  exact EpGroupoid.isLUCAt_of_isomorphic hs' ht' hLF

/-- The printed (LUC) of a basic construction is (LUC) for `(F⁰, 𝓕⁰)`. -/
theorem isLUCLevel_zero_of_isLUC (h : B.IsLUC) : B.IsLUCLevel 0 := fun z _ => by
  obtain ⟨α, Ψ, hΨ, o, hα, ho, hL⟩ := h z
  exact ⟨α, Ψ, hΨ, o, hα, ho, (Ψ.isLUCAt_iff o).1 hL⟩

/-- **2021 Proposition 19.5.9, p. 890**: if `T` is metrizable, the polyfold `(S, F, M)` satisfies
(LUC), resp. (SLUC) (Definition 17.1.22), provided the basic construction `(F, 𝓕)` satisfies
(LUC), resp. (SLUC) (Definition 19.5.8).  For (SLUC) the models of the families of each level are
compared with one model through the generalized isomorphisms `f_{Ψ,Ψ'}` (Theorem 17.1.18). -/
theorem proposition_19_5_9 :
    (B.IsLUC → (toPolyfoldConstruction hm).IsLUC) ∧
      (B.IsSLUC → (toPolyfoldConstruction hm).IsSLUC) := by
  refine ⟨fun h => exists_isLUC_lift_model hm 0 (isLUCLevel_zero_of_isLUC h), fun h => ?_⟩
  choose c hc using fun i => exists_isLUC_lift_model hm i (h i)
  exact ⟨c 0, fun i => (EP.isGenIsoInvariant_isLUC_lift i
    ((toPolyfoldConstruction hm).isGeneralizedIso_comparison (c i) (c 0))).1 (hc i)⟩

end GroupoidalCategory.BasicConstruction

/-! ### Witnesses -/

namespace GroupoidalCategory

/-- **Proposition 19.5.9 for (LUC) in a non-degenerate case**: the reflection `ℤ/2 ⋉ ℝ` (isotropy
`ℤ/2` at the fixed point `0`) satisfies the basic (LUC), so its polyfold satisfies (LUC). -/
theorem reflectionBasic_proposition_19_5_9 :
    reflectionBasic.IsLUC ∧
      (BasicConstruction.toPolyfoldConstruction (hB := reflectionBasic_hB)
        reflectionBasic_metrizableSpace).IsLUC :=
  ⟨reflectionBasic_isLUC,
    (BasicConstruction.proposition_19_5_9 reflectionBasic_metrizableSpace).1 reflectionBasic_isLUC⟩

/-- **Proposition 19.5.9 for (SLUC) in a non-degenerate case**: `z3Basic` (`ℤ/3 ⋉ ℝ` with the
trivial action, isotropy `ℤ/3` at every point) satisfies the basic (SLUC) (Proposition 19.5.11),
so its polyfold satisfies (SLUC). -/
theorem z3Basic_proposition_19_5_9 :
    z3Basic.IsSLUC ∧
      (BasicConstruction.toPolyfoldConstruction (hB := z3Basic_hB)
        z3Basic_metrizableSpace).IsSLUC :=
  ⟨z3Basic_proposition_19_5_11.1,
    (BasicConstruction.proposition_19_5_9 z3Basic_metrizableSpace).2 z3Basic_proposition_19_5_11.1⟩

end GroupoidalCategory

end Polyfold
