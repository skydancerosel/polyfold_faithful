import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_20

/-!
Round trip for V11_20 (2021 Lemma 11.3.4 with (11.8), (11.9), pp. 538–539: section functors of
`Gr̂` along equivalences and generalized isomorphisms).

The item lists the definitions `IsGrHatSection`, `GrHatSections`, `fibreInv`,
`EpFunctor.pushSection`, `EpFunctor.pullSection`, `Diagram.push/pullSection`,
`EPLoc.push/pullSection` (vocabulary) and twenty theorems.  `A` is the conjunction of the types of
the theorems, universes at `0` (`Obj Mor … : Type`, `X Y Z : EP.{0}`).

`B = EquivPartB ∧ GenIsoPartB`: (11.8) for every `x`, `ψ : F(x) → y`; (11.9) literally
(`TF(x) (F^*h')(x) = h'(F(x))` on `X_∞`); `F_*`, `F^*` map `Γ` to `Γ` for an equivalence `F`; and
for generalized isomorphisms, on every choice of representatives: `f_*`, `f^*` are well-defined
maps `Γ → Γ`, `(f⁻¹)_* = f^*`, `(g ∘ f)_* = g_* ∘ f_*`, `(g ∘ f)^* = f^* ∘ g^*`.

* `A ⇒ B` (`A_to_B`): (11.8) is `pushSection_eq`; membership in `Γ` is
  `isGrHatSection_push/pullSection` plus the non-item `push/pullSection_of_not_mem` (vanishing off
  the smooth points, by definition); the generalized-isomorphism part is `lemma_11_3_4` (whose
  4th and 5th conjuncts are `f_* = d.pushSection`, `f^* = d.pullSection` for every
  representative `d`), `EPLoc.pushSection_inv`, `EPLoc.pushSection_comp`,
  `EPLoc.pullSection_comp`.  (11.9) is not stated in `A` (it is the defining property of
  `pullSection`): it is proved from the definition, the non-item `pullSection_of_mem`,
  `mapDomain_map_map`, `mapDomain_map_id` and `fibreInv_spec_tangent` (`TF ∘ TF(x)⁻¹ = id` on
  `T_{F(x)}Y`).
* `B ⇒ A` fails for a genuine reason (`A` is more general): `isGrHatSection_pullSection`,
  `pullSection_eq_of_natTrans`, `pullSection_comp` hold for every functor that is a local
  sc-diffeomorphism on objects (not only equivalences); `pushSection_eq_of_natTrans` (naturally
  equivalent equivalences), `pullSection_pushSection`, `pushSection_pullSection` and the
  composition laws for equivalences of ep-groupoids, the base change in the weak fibred product
  (`WeakFibredProduct.pushSection_projRight/Left_pullSection`) and
  `IsOrientation.isGrHatSection` are not stated in `B`; and `A` takes sections satisfying
  `IsGrHatSection` (any values off `X_∞`), `B` sections in `Γ` (vanishing off `X_∞`).
-/

namespace RoundTrip.V11_20
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.IsOrientation.isGrHatSection.{0} ∧
  type_of% @Polyfold.EpFunctor.pushSection_eq.{0} ∧
  type_of% @Polyfold.EpFunctor.isGrHatSection_pushSection.{0} ∧
  type_of% @Polyfold.EpFunctor.isGrHatSection_pullSection.{0} ∧
  type_of% @Polyfold.EpFunctor.pullSection_pushSection.{0} ∧
  type_of% @Polyfold.EpFunctor.pushSection_pullSection.{0} ∧
  type_of% @Polyfold.EpFunctor.pushSection_eq_of_natTrans.{0} ∧
  type_of% @Polyfold.EpFunctor.pullSection_eq_of_natTrans.{0} ∧
  type_of% @Polyfold.EpFunctor.pushSection_comp.{0} ∧
  type_of% @Polyfold.EpFunctor.pullSection_comp.{0} ∧
  type_of% @Polyfold.WeakFibredProduct.pushSection_projRight_pullSection.{0} ∧
  type_of% @Polyfold.WeakFibredProduct.pushSection_projLeft_pullSection.{0} ∧
  type_of% @Polyfold.EPLocalization.Diagram.pushSection_eq_of_equiv.{0} ∧
  type_of% @Polyfold.EPLocalization.Diagram.pullSection_eq_of_equiv.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.pushSection_homMk.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.pullSection_homMk.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.pushSection_comp.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.pullSection_comp.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.pushSection_inv.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.lemma_11_3_4.{0}

theorem A_holds : A :=
  ⟨@EpGroupoid.IsOrientation.isGrHatSection, @EpFunctor.pushSection_eq,
    @EpFunctor.isGrHatSection_pushSection, @EpFunctor.isGrHatSection_pullSection,
    @EpFunctor.pullSection_pushSection, @EpFunctor.pushSection_pullSection,
    @EpFunctor.pushSection_eq_of_natTrans, @EpFunctor.pullSection_eq_of_natTrans,
    @EpFunctor.pushSection_comp, @EpFunctor.pullSection_comp,
    @WeakFibredProduct.pushSection_projRight_pullSection,
    @WeakFibredProduct.pushSection_projLeft_pullSection,
    @Diagram.pushSection_eq_of_equiv, @Diagram.pullSection_eq_of_equiv,
    @EPLoc.pushSection_homMk, @EPLoc.pullSection_homMk, @EPLoc.pushSection_comp,
    @EPLoc.pullSection_comp, @EPLoc.pushSection_inv, @EPLoc.lemma_11_3_4⟩

/-- `(g ∘ f)` of two generalized isomorphisms is one. -/
theorem isGeneralizedIso_comp {X Y Z : EP.{0}} {f : EPLoc.of X ⟶ EPLoc.of Y}
    {g : EPLoc.of Y ⟶ EPLoc.of Z} (hf : EPLoc.IsGeneralizedIso f) (hg : EPLoc.IsGeneralizedIso g) :
    EPLoc.IsGeneralizedIso (f ≫ g) := by
  rw [EPLoc.isGeneralizedIso_iff_isIso] at hf hg ⊢
  infer_instance

theorem A_to_B : A → B := by
  rintro ⟨-, hpushEq, hpushMem, hpullMem, -, -, -, -, -, -, -, -, -, -, -, -, hpushComp,
    hpullComp, hpushInv, hlem⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the equivalence part
    intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (11.8)
      intro h hh y hy x ψ hs ht
      subst ht
      exact hpushEq hF hh.1 hs hy
    · -- (11.9), from the definition of `pullSection`
      intro h' hh' x hx
      have hFx : F.obj x ∈ Y.PObj.smoothSet :=
        (hF.isLocalScDiffeo_obj.mem_smoothSet_iff x).2 hx
      rw [EpFunctor.pullSection_of_mem hx, EpGroupoid.mapDomain_map_map]
      exact EpGroupoid.mapDomain_map_id (X := Y) (hh'.1.mem _ hFx) fun β hβ =>
        (EpFunctor.fibreInv_spec_tangent hF.isLocalScDiffeo_obj hβ).2
    · intro h hh
      exact ⟨hpushMem hF hh.1, fun y hy => EpFunctor.pushSection_of_not_mem hy⟩
    · intro h' hh'
      exact ⟨hpullMem hF.isLocalScDiffeo_obj hh'.1, fun x hx => EpFunctor.pullSection_of_not_mem hx⟩
  · -- well-defined maps `Γ → Γ`
    intro X Y f hf d d' hd hd'
    have e1 := (hlem hf).2.2.2.1
    have e2 := (hlem hf).2.2.2.2
    refine ⟨fun h hh => ?_, fun h' hh' => ?_⟩
    · have k1 : d.pushSection h = EPLoc.pushSection f h := (e1 d hd h hh.1).symm
      have k2 : d'.pushSection h = EPLoc.pushSection f h := (e1 d' hd' h hh.1).symm
      rw [k1, k2]
      exact ⟨(hlem hf).1 h hh.1, rfl⟩
    · have k1 : d.pullSection h' = EPLoc.pullSection f h' := (e2 d hd h' hh'.1).symm
      have k2 : d'.pullSection h' = EPLoc.pullSection f h' := (e2 d' hd' h' hh'.1).symm
      rw [k1, k2]
      exact ⟨(hlem hf).2.1 h' hh'.1, rfl⟩
  · -- `(f⁻¹)_* = f^*`
    intro X Y f g h₁ h₂ d e hd he h' hh'
    have hf : EPLoc.IsGeneralizedIso f := ⟨g, h₁, h₂⟩
    have hg : EPLoc.IsGeneralizedIso g := ⟨f, h₂, h₁⟩
    have k1 : e.pushSection h' = EPLoc.pushSection g h' := ((hlem hg).2.2.2.1 e he h' hh'.1).symm
    have k2 : d.pullSection h' = EPLoc.pullSection f h' := ((hlem hf).2.2.2.2 d hd h' hh'.1).symm
    rw [k1, k2]
    exact hpushInv hf h₁ h₂ hh'.1
  · -- the composition laws
    intro X Y Z f g hf hg d e c hd he hc
    have hfg := isGeneralizedIso_comp hf hg
    refine ⟨fun h hh => ?_, fun h'' hh'' => ?_⟩
    · have k1 : c.pushSection h = EPLoc.pushSection (f ≫ g) h :=
        ((hlem hfg).2.2.2.1 c hc h hh.1).symm
      have k2 : d.pushSection h = EPLoc.pushSection f h := ((hlem hf).2.2.2.1 d hd h hh.1).symm
      have hm := (hlem hf).1 h hh.1
      have k3 : e.pushSection (EPLoc.pushSection f h) =
          EPLoc.pushSection g (EPLoc.pushSection f h) :=
        ((hlem hg).2.2.2.1 e he _ hm.1).symm
      rw [k1, k2, k3]
      exact hpushComp hf hg hh.1
    · have k1 : c.pullSection h'' = EPLoc.pullSection (f ≫ g) h'' :=
        ((hlem hfg).2.2.2.2 c hc h'' hh''.1).symm
      have k2 : e.pullSection h'' = EPLoc.pullSection g h'' :=
        ((hlem hg).2.2.2.2 e he h'' hh''.1).symm
      have hm := (hlem hg).2.1 h'' hh''.1
      have k3 : d.pullSection (EPLoc.pullSection g h'') =
          EPLoc.pullSection f (EPLoc.pullSection g h'') :=
        ((hlem hf).2.2.2.2 d hd _ hm.1).symm
      rw [k1, k2, k3]
      exact hpullComp hf hg hh''.1

#rt_check RoundTrip.V11_20.A_to_B [Polyfold.EpGroupoid.IsOrientation.isGrHatSection,
  Polyfold.EpFunctor.pushSection_eq, Polyfold.EpFunctor.isGrHatSection_pushSection,
  Polyfold.EpFunctor.isGrHatSection_pullSection, Polyfold.EpFunctor.pullSection_pushSection,
  Polyfold.EpFunctor.pushSection_pullSection, Polyfold.EpFunctor.pushSection_eq_of_natTrans,
  Polyfold.EpFunctor.pullSection_eq_of_natTrans, Polyfold.EpFunctor.pushSection_comp,
  Polyfold.EpFunctor.pullSection_comp,
  Polyfold.WeakFibredProduct.pushSection_projRight_pullSection,
  Polyfold.WeakFibredProduct.pushSection_projLeft_pullSection,
  Polyfold.EPLocalization.Diagram.pushSection_eq_of_equiv,
  Polyfold.EPLocalization.Diagram.pullSection_eq_of_equiv,
  Polyfold.EPLocalization.EPLoc.pushSection_homMk, Polyfold.EPLocalization.EPLoc.pullSection_homMk,
  Polyfold.EPLocalization.EPLoc.pushSection_comp, Polyfold.EPLocalization.EPLoc.pullSection_comp,
  Polyfold.EPLocalization.EPLoc.pushSection_inv, Polyfold.EPLocalization.EPLoc.lemma_11_3_4]
#rt_overlap RoundTrip.V11_20.A_to_B [Polyfold.EpGroupoid.IsOrientation.isGrHatSection,
  Polyfold.EpFunctor.pushSection_eq, Polyfold.EpFunctor.isGrHatSection_pushSection,
  Polyfold.EpFunctor.isGrHatSection_pullSection, Polyfold.EpFunctor.pullSection_pushSection,
  Polyfold.EpFunctor.pushSection_pullSection, Polyfold.EpFunctor.pushSection_eq_of_natTrans,
  Polyfold.EpFunctor.pullSection_eq_of_natTrans, Polyfold.EpFunctor.pushSection_comp,
  Polyfold.EpFunctor.pullSection_comp,
  Polyfold.WeakFibredProduct.pushSection_projRight_pullSection,
  Polyfold.WeakFibredProduct.pushSection_projLeft_pullSection,
  Polyfold.EPLocalization.Diagram.pushSection_eq_of_equiv,
  Polyfold.EPLocalization.Diagram.pullSection_eq_of_equiv,
  Polyfold.EPLocalization.EPLoc.pushSection_homMk, Polyfold.EPLocalization.EPLoc.pullSection_homMk,
  Polyfold.EPLocalization.EPLoc.pushSection_comp, Polyfold.EPLocalization.EPLoc.pullSection_comp,
  Polyfold.EPLocalization.EPLoc.pushSection_inv, Polyfold.EPLocalization.EPLoc.lemma_11_3_4]

end RoundTrip.V11_20
