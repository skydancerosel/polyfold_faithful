import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_31

set_option maxSynthPendingDepth 3

/-! Round trip for V19_31 (2021 Theorem 19.5.1, p. 886).  Universes at `0`.

* `A_to_B` (through the main conjunct `theorem_19_5_1` only): for a representative `F` of `𝓕`,
  `T^F_{Ψ,Ψ'} = T_{Ψ,Ψ'}` (Lemma 19.3.1), so the structure `B.transPolyfold` of `B.M Ψ Ψ'` (topology
  of `B.rep`) is moved to `F.Tr Ψ Ψ'` along this equality (`good_congr`); `s`, `t` stay local
  sc-diffeomorphisms; `B`'s naturality (each `F_h` an sc-diffeomorphism onto its open image) follows
  for ANY structure in which `s` is a local sc-diffeomorphism (`isScDiffeoOn_of_section`, since
  `s ∘ F_h = id` and `F_h` is continuous).  `B`'s metrizability of `M(Ψ, Ψ')` is the project's
  instance `TransitionData.metrizableSpace` (it holds without `T` metrizable).
* `B_to_A`: `A` speaks of the specific structure `transPolyfold` (a definition); its statements
  are re-proved outright from non-item lemmas (descent along `(h, q) ↦ F_h(q)`), `B` is NOT used. -/

namespace RoundTrip.V19_31
open Polyfold Polyfold.GroupoidalCategory Set
open Polyfold.GroupoidalCategory.UniformizerConstruction

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1_natural.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_src.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_tgt.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_map.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_hatHomeomorph.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_of_equiv.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1_natural.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_src.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_tgt.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_map.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_hatHomeomorph.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_of_equiv.{0}⟩

/-- A continuous section `f` of a local sc-diffeomorphism `s` over an open `V`, with open image,
is an sc-diffeomorphism `V → f(V)` with inverse `s`. -/
theorem isScDiffeoOn_of_section {X Y : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {PX : MPolyfold X} {PY : MPolyfold Y}
    {s : Y → X} (hs : PY.IsLocalScDiffeo PX s) {f : X → Y} {V : Set X} (hV : IsOpen V)
    (hf : ContinuousOn f V) (hW : IsOpen (f '' V)) (hsf : ∀ q ∈ V, s (f q) = q) :
    PX.IsScDiffeoOn PY f s V (f '' V) := by
  refine ⟨?_, ?_, fun q hq => mem_image_of_mem _ hq, ?_, hsf, ?_⟩
  · refine MPolyfold.IsScSmoothOn.of_locally hV fun x hx => ?_
    obtain ⟨W, V', g, hxW, hd⟩ := hs (f x)
    have hNo : IsOpen (V ∩ f ⁻¹' W) := hf.isOpen_inter_preimage hV hd.isScSmoothOn.isOpen
    have hN' : IsOpen ((V ∩ f ⁻¹' W) ∩ V') := hNo.inter hd.isScSmoothOn_inv.isOpen
    have hxV' : x ∈ V' := by
      have := hd.mapsTo hxW
      rwa [hsf x hx] at this
    refine ⟨(V ∩ f ⁻¹' W) ∩ V', hN', ⟨⟨hx, hxW⟩, hxV'⟩, fun y hy => hy.1.1, ?_⟩
    refine (hd.isScSmoothOn_inv.mono hN' inter_subset_right).congr fun y hy => ?_
    have := hd.left_inv (f y) hy.1.2
    rwa [hsf y hy.1.1] at this
  · exact (hs.isScSmoothMap.mono hW (subset_univ _))
  · rintro _ ⟨q, hq, rfl⟩
    rw [hsf q hq]; exact hq
  · rintro _ ⟨q, hq, rfl⟩
    rw [hsf q hq]


/-- An M-polyfold structure on `X` (for the topology `t`) for which `s` and `t'` are local
sc-diffeomorphisms. -/
def Good {X Y Z : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (PY : MPolyfold Y) (PZ : MPolyfold Z)
    (s : X → Y) (t' : X → Z) (t : TopologicalSpace X) : Prop :=
  letI := t
  ∃ (_ : T2Space X) (_ : ParacompactSpace X) (P : MPolyfold X),
    P.IsLocalScDiffeo PY s ∧ P.IsLocalScDiffeo PZ t'

theorem good_congr {X Y Z : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PY : MPolyfold Y} {PZ : MPolyfold Z}
    {s : X → Y} {t' : X → Z} {t₁ t₂ : TopologicalSpace X} (h : t₁ = t₂)
    (h₂ : Good PY PZ s t' t₂) : Good PY PZ s t' t₁ := h ▸ h₂

/-- The main conjunct (Theorem 19.5.1 for the fixed representative) gives `B`. -/
theorem main_A_to_B
    (hA : type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1.{0}) : B := by
  intro C B F hB hF _hm Ψ Ψ'
  refine ⟨inferInstance, ?_⟩
  -- the structure of `B.M Ψ Ψ'` (topology of `B.rep`), moved to the equal topology of `F`
  have hT : F.topology Ψ Ψ' = B.rep.topology Ψ Ψ' :=
    TopologicalSpace.ext (TransitionData.lemma_19_3_1
      (Quotient.exact (hF.trans B.mk_rep.symm)) Ψ Ψ')
  have hgood : Good (Ψ : C.Uniformizer).P (Ψ' : C.Uniformizer).P
      (fun a : Ψ.1.Trans Ψ'.1 => a.src) (fun a : Ψ.1.Trans Ψ'.1 => a.tgt) (F.topology Ψ Ψ') := by
    refine good_congr hT ?_
    obtain ⟨h1, h2, -, -⟩ := hA B hB (by
      have : B.natTop hB = natT B.U :=
        (TopologicalSpace.generateFrom_setOfPred_isOpen (B.natTop hB)).symm
      rw [this]; exact _hm) Ψ Ψ'
    exact ⟨(inferInstance : T2Space (B.M Ψ Ψ')), (inferInstance : ParacompactSpace (B.M Ψ Ψ')),
      B.transPolyfold Ψ Ψ', h1, h2⟩
  obtain ⟨i, j, P, hs, ht⟩ := hgood
  refine ⟨i, j, P, fun h => ?_, hs, ht⟩
  have hV := F.isOpen_dom Ψ Ψ' h
  have hW : IsOpen (germ F Ψ Ψ' h '' F.dom Ψ Ψ' h) := F.isOpen_image_map Ψ Ψ' h hV subset_rfl
  exact ⟨hW, _, isScDiffeoOn_of_section (Y := F.Tr Ψ Ψ') hs hV (F.continuousOn_map Ψ Ψ' h) hW
    fun q hq => F.src_map Ψ Ψ' h q hq⟩

theorem A_to_B : A → B := fun hA => main_A_to_B hA.1


/-! ### `B ⇒ A`: `A` speaks of the specific structure `transPolyfold`; its statements are
re-proved outright from non-item lemmas (the descent along `(h, q) ↦ F_h(q)`), `B` is not used. -/

section Copies
open Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData
variable {C : GroupoidalCategory.{0}} {U : C.UniformizerConstruction} (F : U.TransitionData)

theorem src' (Ψ Ψ' : U.Unif) :
    (F.transPolyfold Ψ Ψ').IsLocalScDiffeo Ψ.1.P fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src :=
  (F.isLocalScDiffeo_sheetMap Ψ Ψ').of_comp_surjective (F.surjective_sheetMap Ψ Ψ') <| by
    have : (fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) ∘ F.sheetMap Ψ Ψ' =
        fun x : F.SheetSpace Ψ Ψ' => x.2.1 := funext (F.src_sheetMap Ψ Ψ')
    rw [this]; exact F.isLocalScDiffeo_sheetSrc Ψ Ψ'

theorem tgt' (Ψ Ψ' : U.Unif) :
    (F.transPolyfold Ψ Ψ').IsLocalScDiffeo Ψ'.1.P fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).tgt :=
  (F.isLocalScDiffeo_sheetMap Ψ Ψ').of_comp_surjective (F.surjective_sheetMap Ψ Ψ')
    (F.isLocalScDiffeo_sheetTgt Ψ Ψ')

theorem map' (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) :
    Ψ.1.P.IsScDiffeoOn (F.transPolyfold Ψ Ψ') (fun q => F.toTr (F.map Ψ Ψ' h q))
      (fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) (F.dom Ψ Ψ' h)
      (F.map Ψ Ψ' h '' F.dom Ψ Ψ' h) :=
  isScDiffeoOn_of_section (Y := F.Tr Ψ Ψ') (src' F Ψ Ψ') (F.isOpen_dom Ψ Ψ' h)
    (F.continuousOn_map Ψ Ψ' h) (F.isOpen_image_map Ψ Ψ' h (F.isOpen_dom Ψ Ψ' h) subset_rfl)
    fun q hq => F.src_map Ψ Ψ' h q hq

theorem srcComp' (Ψ Ψ' : U.Unif) {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] {Q : MPolyfold Z} (Θ : Z ≃ₜ F.Tr Ψ Ψ')
    (hs : Q.IsLocalScDiffeo Ψ.1.P fun z => (Θ z : Ψ.1.Trans Ψ'.1).src) :
    Q.IsScDiffeoOn (F.transPolyfold Ψ Ψ') Θ Θ.symm univ univ :=
  (MPolyfold.isLocalScDiffeo_of_comp_eq hs (src' F Ψ Ψ') Θ.continuous
    fun _ => rfl).isScDiffeoOn_of_bijective Θ.toEquiv fun _ => rfl

theorem hat' (Ψ : U.Unif) :
    Ψ.1.ep.PMor.IsScDiffeoOn (F.transPolyfold Ψ Ψ) (F.hatHomeomorph Ψ) (F.hatHomeomorph Ψ).symm
      univ univ :=
  srcComp' F Ψ Ψ (F.hatHomeomorph Ψ) Ψ.1.ep.isLocalScDiffeo_src

theorem equiv' {F₁ F₂ : U.TransitionData} (e : F₁.Equiv F₂) (Ψ Ψ' : U.Unif) :
    (F₁.transPolyfold Ψ Ψ').IsScDiffeoOn (F₂.transPolyfold Ψ Ψ') (equivHomeomorph e Ψ Ψ')
      (equivHomeomorph e Ψ Ψ').symm univ univ :=
  srcComp' F₂ Ψ Ψ' (equivHomeomorph e Ψ Ψ') (src' F₁ Ψ Ψ')

end Copies

theorem B_to_A (_hB : B) : A := by
  refine ⟨fun B hB _ Ψ Ψ' => ⟨src' B.rep Ψ Ψ', tgt' B.rep Ψ Ψ', map' B.rep Ψ Ψ', hat' B.rep Ψ⟩,
    fun B Ψ Ψ' => ⟨fun Q hQ => srcComp' B.rep Ψ Ψ' (Homeomorph.refl _) hQ, fun {F} hF =>
      srcComp' B.rep Ψ Ψ' (B.trHomeomorph hF Ψ Ψ') (src' F Ψ Ψ')⟩,
    @src', @tgt', @map', @hat', @equiv'⟩

/-- The main conjunct from `B` (outright, like `B_to_A`). -/
theorem main_B_to_A (hB : B) :
    type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1.{0} := (B_to_A hB).1

#rt_check RoundTrip.V19_31.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1_natural,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_src,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_tgt,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_hatHomeomorph,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_of_equiv]
#rt_check RoundTrip.V19_31.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1_natural,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_src,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_tgt,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_hatHomeomorph,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_of_equiv]
#rt_check RoundTrip.V19_31.main_A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1_natural,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_src,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_tgt,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_hatHomeomorph,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_of_equiv]
#rt_check RoundTrip.V19_31.main_B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1_natural,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_src,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_tgt,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_hatHomeomorph,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_of_equiv]
#rt_overlap RoundTrip.V19_31.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1_natural,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_src,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_tgt,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_hatHomeomorph,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_of_equiv]
#rt_overlap RoundTrip.V19_31.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1_natural,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_src,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalScDiffeo_tgt,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_hatHomeomorph,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScDiffeoOn_of_equiv]

end RoundTrip.V19_31
