import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V18_13

set_option maxSynthPendingDepth 3

/-! Round trip for V18_13 (2021 Theorem 18.1.5, p. 846; 2017: Theorem 18.1: the implicit
function theorem for sc-Fredholm section functors).

`A` is the conjunction of the types of the item's nine theorems (`zeroIndicator` is vocabulary),
the general ones at universe `0`.

* Neither direction is proved.  `A`'s theorems all assume tame germ data
  `Q.IsScFredholmSectionFunctorTame f` (`hft`) and no tameness of `S`; `B` assumes `S.IsTame`
  and `Q.IsScFredholmSectionFunctor f` only, and the project has no lemma producing `hft` from
  these.  `A`'s conclusions are in the model `X_Ψ` (a natural representation `U(x₀)`, model good
  position at the zeros), `B`'s on `C_U`.
* `A_to_Bpart`: `A` together with `hft` gives `B`'s conclusions (1) (branched, tame,
  orbifold-type on `C_U`) and the Note, for the same `U`; `B`'s clause (2) is omitted (see JSON).
-/
namespace RoundTrip.V18_13
open Polyfold GCT.VectorBundle GCT.VectorBundle.StrongPolyfoldBundleConstruction

def A : Prop :=
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5.{0} ∧
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_subcategory.{0} ∧
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_model.{0} ∧
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_note.{0} ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_hyp_witness ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_hyp_applies ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_subcategory_hyp_applies ∧
  type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_5_intrinsic_hyp_witness ∧
  type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_5_intrinsic_hyp_applies

theorem A_holds : A :=
  ⟨@theorem_18_1_5.{0}, @theorem_18_1_5_subcategory.{0}, @theorem_18_1_5_model.{0},
   @theorem_18_1_5_note.{0},
   @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_hyp_witness,
   @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_hyp_applies,
   @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_subcategory_hyp_applies,
   @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_5_intrinsic_hyp_witness,
   @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_5_intrinsic_hyp_applies⟩

/-- `B` with the tame germ data `hft` added to its hypotheses and its clause (2) omitted. -/
def Bpart : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S) (f : V.SectionFunctor),
    S.IsTame → Q.IsScFredholmSectionFunctor f → Q.IsScFredholmSectionFunctorTame f →
    ∀ (hs : Q.IsScSmoothSectionFunctor f)
    (α : C.Obj) [Fact (S.TangentObj α)] (h0 : f.toFun α = V.objMk α 0)
    (hne : (Q.F α).Nonempty),
    Function.Surjective (Q.linearization f hs α h0 hne) →
    Q.IsKernelInGoodPosition f hs α h0 hne →
    ∃ (U : Set C.toGroupoidStr.OrbitSpace) (hU : IsOpen U), C.toGroupoidStr.π α ∈ U ∧
      (S.openSubConstruction hU).IsBranchedSubcategory (GCT.restrictTheta U f.zeroIndicator) ∧
      (S.openSubConstruction hU).IsTameSubcategory (GCT.restrictTheta U f.zeroIndicator) ∧
      (C.openSub U).IsOrbifoldTypeBranched (GCT.restrictTheta U f.zeroIndicator) ∧
      (∀ c : (S.openSubConstruction hU).CoveringFamily,
        ((S.openSubConstruction hU).modelEP c.Ψ).X.PObj.IsSmoothSubmanifold
          (EpGroupoid.supp
            ((S.openSubConstruction hU).modelPull c.Ψ (GCT.restrictTheta U f.zeroIndicator))))

theorem A_to_Bpart : A → Bpart := by
  rintro ⟨-, hsub, -, hnote, -⟩ C S V Q f _ hf hft hs α _ h0 hne hsurj hker
  let Ψb : PUnit.{1} → Q.Unif := fun _ => Q.refBundleUnif hne
  have hα : S.HasRegularity 1 α := (Fact.out : S.TangentObj α).1
  let x := Q.refBundlePoint hα hne
  have hx : (Ψb PUnit.unit).1.base.obj ((Ψb PUnit.unit).1.base.P.levelVal 1 x) = α :=
    Q.obj_refBundlePoint hα hne
  have hgp := (Q.isGoodPositionGermTame_localRep_iff hs hft α h0 hne
    (Q.refBundleUnif_mem hne) x hx).2 ⟨hsurj, hker⟩
  have e : (S.modelFunctor (Q.modelBase Ψb)).obj
      ⟨PUnit.unit, (Ψb PUnit.unit).1.base.P.levelVal 1 x⟩ = α := hx
  have h0' : (S.modelFunctor (Q.modelBase Ψb)).obj
      ⟨PUnit.unit, (Ψb PUnit.unit).1.base.P.levelVal 1 x⟩ ∈ f.zeroSet := by
    rw [e]; exact h0
  obtain ⟨-, U, hU, -, hmem, hbr, ho, htm, -, -⟩ := hsub Q (Ψb := Ψb) hf hft h0' hgp
  refine ⟨U, hU, e ▸ hmem, hbr, htm, ho, fun c => ?_⟩
  obtain ⟨-, h, -⟩ := hnote hU hbr c
  exact h

/-- The main conjunct (`theorem_18_1_5_subcategory`) alone gives `Bpart` up to the Note. -/
theorem main_to_Bpart_noNote :
    type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_subcategory.{0} →
    ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
      (Q : V.StrongPolyfoldBundleConstruction S) (f : V.SectionFunctor),
      Q.IsScFredholmSectionFunctor f → Q.IsScFredholmSectionFunctorTame f →
      ∀ (hs : Q.IsScSmoothSectionFunctor f)
      (α : C.Obj) [Fact (S.TangentObj α)] (h0 : f.toFun α = V.objMk α 0)
      (hne : (Q.F α).Nonempty),
      Function.Surjective (Q.linearization f hs α h0 hne) →
      Q.IsKernelInGoodPosition f hs α h0 hne →
      ∃ (U : Set C.toGroupoidStr.OrbitSpace) (hU : IsOpen U), C.toGroupoidStr.π α ∈ U ∧
        (S.openSubConstruction hU).IsBranchedSubcategory (GCT.restrictTheta U f.zeroIndicator) ∧
        (S.openSubConstruction hU).IsTameSubcategory (GCT.restrictTheta U f.zeroIndicator) ∧
        (C.openSub U).IsOrbifoldTypeBranched (GCT.restrictTheta U f.zeroIndicator) := by
  intro hsub C S V Q f hf hft hs α _ h0 hne hsurj hker
  let Ψb : PUnit.{1} → Q.Unif := fun _ => Q.refBundleUnif hne
  have hα : S.HasRegularity 1 α := (Fact.out : S.TangentObj α).1
  let x := Q.refBundlePoint hα hne
  have hx : (Ψb PUnit.unit).1.base.obj ((Ψb PUnit.unit).1.base.P.levelVal 1 x) = α :=
    Q.obj_refBundlePoint hα hne
  have hgp := (Q.isGoodPositionGermTame_localRep_iff hs hft α h0 hne
    (Q.refBundleUnif_mem hne) x hx).2 ⟨hsurj, hker⟩
  have e : (S.modelFunctor (Q.modelBase Ψb)).obj
      ⟨PUnit.unit, (Ψb PUnit.unit).1.base.P.levelVal 1 x⟩ = α := hx
  have h0' : (S.modelFunctor (Q.modelBase Ψb)).obj
      ⟨PUnit.unit, (Ψb PUnit.unit).1.base.P.levelVal 1 x⟩ ∈ f.zeroSet := by
    rw [e]; exact h0
  obtain ⟨-, U, hU, -, hmem, hbr, ho, htm, -, -⟩ := hsub Q (Ψb := Ψb) hf hft h0' hgp
  exact ⟨U, hU, e ▸ hmem, hbr, htm, ho⟩

#rt_check RoundTrip.V18_13.A_to_Bpart [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_subcategory, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_model, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_note, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_hyp_witness, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_hyp_applies, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_subcategory_hyp_applies, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_5_intrinsic_hyp_witness, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_5_intrinsic_hyp_applies]
#rt_check RoundTrip.V18_13.main_to_Bpart_noNote [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_subcategory, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_model, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_note, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_hyp_witness, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_hyp_applies, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_subcategory_hyp_applies, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_5_intrinsic_hyp_witness, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_5_intrinsic_hyp_applies]
#rt_overlap RoundTrip.V18_13.A_to_Bpart [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_subcategory, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_model, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_note, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_hyp_witness, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_hyp_applies, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_1_5_subcategory_hyp_applies, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_5_intrinsic_hyp_witness, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_5_intrinsic_hyp_applies]

end RoundTrip.V18_13
