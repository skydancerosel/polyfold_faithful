import Polyfold.Chapter12.LocalOrientationSpace
import Polyfold.Chapter12.LocalOrientationMorphisms
import Polyfold.Chapter12.OrientationFromSection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
Definition 12.5.2 (p. 593), Theorem 12.5.3 (p. 594), Definition 12.5.4 (p. 594).

# The orientation bundle of an sc-Fredholm section functor, with local sc⁺-sections

## The text, paraphrased

`(P : W → X, μ)` is a strong bundle over a tame ep-groupoid and `f` an sc-Fredholm section
functor.  Definition 12.5.2: `O_f` is the set of pairs `(x, o)` of a smooth object `x` and an
orientation `o` of `DET(f, x)`, with the projection `σ : O_f → X_∞`; a morphism `φ : x → x'`
acts by `φ_*`.  Theorem 12.5.3: `O_f` has a natural topology for which `σ` is a local
homeomorphism, as in Part I's Theorem 6.6.17, and for a morphism `φ` the associated local
isomorphism `Φ̂` pushes a continuous local section forward to a continuous local section.
Definition 12.5.4: an orientation of `f` is a continuous section of `σ` which is invariant
under the morphisms.

## What is formalized

`Lin(f, x)` is made with local sc⁺-sections as in the text (`OrxLoc`, the orientations of
`DET(f|W, x)` for an open subset `W` of the base domain of a chart).  The hypotheses are a tame
object M-polyfold and tame germ data of `f` only; no sc-smooth bump functions and no
sc⁺-sections over all of the object space are assumed.

* `definition_12_5_2_loc`: **Definition 12.5.2**, the set `O_f` (`OrSpaceLoc`), with the
  projection `LocalTransport.proj`; `orProj_two_loc`: `σ` is surjective and `(2 : 1)`;
  `exists_other_orLoc`: the other orientation.  The action of the morphisms is
  `EpStrongBundle.orMorLoc`.
* `theorem_12_5_3_loc`: **Theorem 12.5.3**, the topological part: `O_f` has exactly one topology
  with the properties of Theorem 6.6.17, and the fibres of `σ` have two points.
* `theorem_12_5_3_push_loc`: **Theorem 12.5.3**, the last sentence: for a morphism
  `σ : x → x'` between smooth objects, a continuous orientation `o` over an open `V ∋ x` is
  carried to a continuous orientation `o'` over an open `V' ∋ x'` inside the target of the
  sheet of `σ`, and `o'_{t(τ)} = τ_* o_{s(τ)}` for every morphism `τ` of the sheet ending in
  `V'`; in particular `o'_{x'} = σ_* o_x`.
* `definition_12_5_4_loc`: **Definition 12.5.4**, an orientation of `f`;
  `definition_12_5_4_loc_iff`: the continuity read as invariance under the transport along all
  sc-smooth paths.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v u' v'

section Carried

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

/-- **The carried section at a point `a` with `ϕ(a) = x`**, for an isomorphism defined on all
of the base: `pullOrx o' a` is the orientation map at `a` applied to `o'_x`. -/
theorem StrongBundle.LocalIso.pullOrx_univ_eq_orxViaAt {U' : Set X'}
    (L : StrongBundle.LocalIso B B' univ U') (hf : B.IsScFredholmSection f)
    (hf' : B'.IsScFredholmSection f') (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) univ)
    (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)
    (o' : ∀ y (hy : y ∈ PX'.smoothSet), Orx f' hf' y hy) (a : X) (has : a ∈ PX.smoothSet)
    {x : X'} (hϕ : L.ϕ a = x) :
    L.pullOrx hf hf' hfL hsec hsec' o' a has =
      L.orxViaAt hf hf' hfL hsec hsec' (mem_univ a) has hϕ
        (o' x (L.mem_smoothSet_of_ϕ_eq (mem_univ a) has hϕ)) := by
  subst hϕ
  exact L.pullOrx_apply_univ hf hf' hfL hsec hsec' o' a has

end Carried

section Fibres

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **`σ : O_f → X_∞` is surjective and `(2 : 1)`** (Definition 12.5.2, p. 594), for the local
orientation sets. -/
theorem orProj_two_loc (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    (x : PX.SmoothLevel) :
    ∃ p q : OrSpaceLoc hX hf, p ≠ q ∧ (orLocalTransportLoc hX hf).proj p = x ∧
      (orLocalTransportLoc hX hf).proj q = x ∧
      ∀ r, (orLocalTransportLoc hX hf).proj r = x → r = p ∨ r = q := by
  obtain ⟨o₁, o₂, hne, hall⟩ := exists_two_orxLoc hf (PX.smoothVal_mem x)
  refine ⟨⟨x, o₁⟩, ⟨x, o₂⟩, fun h => hne (eq_of_heq (Sigma.mk.inj_iff.1 h).2), rfl, rfl, ?_⟩
  rintro ⟨y, ω⟩ hr
  change y = x at hr
  subst hr
  rcases hall ω with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The other orientation: the local orientation set `Or_x^f` has exactly two elements. -/
theorem exists_other_orLoc (hf : B.IsScFredholmSectionTame f) {x : X}
    (hs : x ∈ PX.smoothSet) (o : OrxLoc hf x hs) :
    ∃ o' : OrxLoc hf x hs, o' ≠ o ∧ ∀ o'', o'' = o ∨ o'' = o' := by
  obtain ⟨o₁, o₂, hne, hall⟩ := exists_two_orxLoc hf hs
  rcases hall o with rfl | rfl
  · exact ⟨o₂, hne.symm, hall⟩
  · exact ⟨o₁, hne, fun o'' => (hall o'').symm⟩

end Fibres

section Mor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}

/-! ### Definition 12.5.2 -/

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- **Definition 12.5.2**, p. 593, with `Lin(f, x)` made with local sc⁺-sections: the
orientation bundle `O_f` of an sc-Fredholm section functor with tame germ data over a tame
ep-groupoid, the pairs `(x, o)` of a smooth object `x` and an orientation `o` of `DET(f, x)`.
Its projection `σ` is `LocalTransport.proj`, its topology that of `theorem_12_5_3_loc`, and a
morphism acts by `orMorLoc`. -/
abbrev definition_12_5_2_loc (hX : X.PObj.IsTame) (hfT : B.IsScFredholmSectionTame f) :
    Type _ :=
  OrSpaceLoc hX hfT

/-! ### Theorem 12.5.3 -/

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- **Theorem 12.5.3**, p. 594, the topological part, with `Lin(f, x)` made with local
sc⁺-sections, for a tame object M-polyfold and a section with tame germ data: `O_f` carries
exactly one topology with the properties of Theorem 6.6.17 (Hausdorff, `σ` a local
homeomorphism, exactly two continuous local sections near each point, the propagation
property), and every fibre of `σ` has two points.  The action of the morphisms is `orMorLoc`
(`orMorLoc_comp`, `orMorLoc_unit`, `orMorLoc_inv`). -/
theorem theorem_12_5_3_loc (hX : X.PObj.IsTame) (hfT : B.IsScFredholmSectionTame f) :
    (∃! t : TopologicalSpace (OrSpaceLoc hX hfT),
      (orLocalTransportLoc hX hfT).IsOrientationTopology t) ∧
    ∀ x : X.PObj.SmoothLevel, ∃ p q : OrSpaceLoc hX hfT, p ≠ q ∧
      (orLocalTransportLoc hX hfT).proj p = x ∧ (orLocalTransportLoc hX hfT).proj q = x ∧
      ∀ r, (orLocalTransportLoc hX hfT).proj r = x → r = p ∨ r = q :=
  ⟨theorem_6_6_17_loc hX hfT, orProj_two_loc hX hfT⟩

/-- **Theorem 12.5.3, last sentence**, p. 594, with `Lin(f, x)` made with local sc⁺-sections,
for a tame object M-polyfold and a section functor with tame germ data: for a morphism
`σ : x → x'` between smooth objects and a continuous orientation `o` over an open `V ∋ x`,
there are an open neighbourhood `V'` of `x'` inside the target of the sheet of `σ` and a
continuous orientation `o'` over `V'` such that for every morphism `τ : y → y'` of the sheet of
`σ` with `y' ∈ V'` one has `y ∈ V` and `o'_{y'} = τ_* o_y`; in particular `o'_{x'} = σ_* o_x`.
The section `o'` is the one carried by the local strong bundle isomorphism of `σ`, read in
an open subset of a chart domain at `x'` which the isomorphism maps into a chart domain at
`x` and into `V`. -/
theorem theorem_12_5_3_push_loc (hX : X.PObj.IsTame) (hF : E.IsScFredholmSectionFunctor f)
    (hfT : B.IsScFredholmSectionTame f) (σ : Mor) {x x' : Obj} (hx : X.src σ = x)
    (hx' : X.tgt σ = x') (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet)
    {V : Set Obj} {o : ∀ y (hy : y ∈ X.PObj.smoothSet), OrxLoc hfT y hy}
    (ho : (orLocalTransportLoc hX hfT).IsContOn V o) (hxV : x ∈ V) :
    ∃ (V' : Set Obj) (o' : ∀ y (hy : y ∈ X.PObj.smoothSet), OrxLoc hfT y hy),
      x' ∈ V' ∧ V' ⊆ (X.sheetAt σ).tgtSet ∧ (orLocalTransportLoc hX hfT).IsContOn V' o' ∧
      o' x' hs' = E.orMorLoc hF hfT σ hx hx' hs hs' (o x hs) ∧
      ∀ τ : Mor, τ ∈ (X.sheetAt σ).carrier → ∀ {y y' : Obj} (hy : X.src τ = y)
        (hy' : X.tgt τ = y') (hys : y ∈ X.PObj.smoothSet) (hys' : y' ∈ X.PObj.smoothSet),
        y' ∈ V' → y ∈ V ∧ o' y' hys' = E.orMorLoc hF hfT τ hy hy' hys hys' (o y hys) := by
  classical
  set D : B.Dom := B.domAt x with hD
  have hDV : IsOpen (D.carrier ∩ V) := D.isOpen.inter ho.1
  have hWo : IsOpen ((X.sheetAt σ).tgtSet ∩ (E.morIso σ).ϕ ⁻¹' (D.carrier ∩ V)) :=
    (E.morIso σ).base.isScSmoothOn.continuousOn.isOpen_inter_preimage (E.morIso σ).isOpen_U hDV
  have hxW : x' ∈ (X.sheetAt σ).tgtSet ∩ (E.morIso σ).ϕ ⁻¹' (D.carrier ∩ V) :=
    ⟨mem_tgtSet hx', by rw [mem_preimage, E.morIso_ϕ_eq hx hx']; exact ⟨B.mem_domAt x, hxV⟩⟩
  set D' : B.Dom := (B.domAt x').restrict hWo ⟨x', B.mem_domAt x', hxW⟩ with hD'
  have hset : E.morIsoDomSet σ D D' = univ :=
    eq_univ_of_forall fun w => ⟨w.2.2.1, w.2.2.2.1⟩
  set Lu : StrongBundle.LocalIso D'.bundle D.bundle univ (E.morIsoDomTarget σ D D') :=
    (E.morIsoDom σ D D').ofEq hset rfl with hLu
  have hmemS : ∀ w : D'.carrier, w ∈ E.morIsoDomSet σ D D' := fun w => hset ▸ mem_univ w
  have hfL : EqOn (D'.sec f hfT.isScSmooth.1)
      (Lu.Ψ ∘ D.sec f hfT.isScSmooth.1 ∘ Lu.ϕ) univ :=
    fun w _ => E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 σ D D' (hmemS w)
  have hϕ : ∀ w : D'.carrier, Lu.ϕ w = ⟨(E.morIso σ).ϕ w.1, (hmemS w).2⟩ :=
    fun w => E.morIsoDom_ϕ_of_mem (hmemS w)
  -- the given orientation read in the domain `D`
  have hoD := (D.isContOn_iff hX hfT hDV inter_subset_left o).1 (ho.mono hDV inter_subset_right)
  have hpull := Lu.isContOrOn_pullOrx_of_chart (D'.isTame hX) D'.exists_chart_univ
    (D'.isFredholm hfT) D'.hasSections (D.isTame hX) D.exists_chart_univ (D.isFredholm hfT)
    D.hasSections hfL hoD
  have hpre : Lu.ϕ ⁻¹' (Subtype.val ⁻¹' (D.carrier ∩ V)) = univ :=
    eq_univ_of_forall fun w => by
      rw [mem_preimage, hϕ w]
      exact w.2.2.2
  rw [hpre] at hpull
  set pull := Lu.pullOrx (D'.isFredholm hfT).toIsScFredholmSection
    (D.isFredholm hfT).toIsScFredholmSection hfL D'.hasSections D.hasSections
    (D.pushLoc hfT o) with hpulldef
  -- the carried section as a family of local orientations
  set o' : ∀ y (hy : y ∈ X.PObj.smoothSet), OrxLoc hfT y hy := fun y hy =>
    if hyD : y ∈ D'.carrier then
      (D'.toLoc hfT y hyD hy).symm (pull ⟨y, hyD⟩ (StrongBundle.Dom.mem_smoothSet hyD hy))
    else o y hy with ho'
  have ho'D : ∀ (y : Obj) (hyD : y ∈ D'.carrier) (hy : y ∈ X.PObj.smoothSet), o' y hy =
      (D'.toLoc hfT y hyD hy).symm (pull ⟨y, hyD⟩ (StrongBundle.Dom.mem_smoothSet hyD hy)) :=
    fun y hyD hy => dif_pos hyD
  have hpush : D'.pushLoc hfT o' = pull := by
    funext w hw
    have hws := (MPolyfold.mem_smoothSet_restrictOpen_iff D'.isOpen w).1 hw
    exact (congrArg (D'.toLoc hfT w.1 w.2 hws) (ho'D w.1 w.2 hws)).trans
      ((D'.toLoc hfT w.1 w.2 hws).apply_symm_apply _)
  have hcont : (orLocalTransportLoc hX hfT).IsContOn D'.carrier o' :=
    (D'.isContOn_carrier_iff hX hfT o').2 (hpush ▸ hpull)
  -- the values of the carried section
  have hval : ∀ τ : Mor, τ ∈ (X.sheetAt σ).carrier → ∀ {y y' : Obj} (hy : X.src τ = y)
      (hy' : X.tgt τ = y') (hys : y ∈ X.PObj.smoothSet) (hys' : y' ∈ X.PObj.smoothSet),
      y' ∈ D'.carrier → y ∈ V ∧ o' y' hys' = E.orMorLoc hF hfT τ hy hy' hys hys' (o y hys) := by
    intro τ hτ y y' hy hy' hys hys' hyD'
    have hϕy : (E.morIso σ).ϕ y' = y := E.morIso_ϕ_of_mem_sheet σ hτ hy hy'
    have hyDV : y ∈ D.carrier ∩ V := hϕy ▸ hyD'.2.2
    refine ⟨hyDV.2, ?_⟩
    have hϕ' : Lu.ϕ ⟨y', hyD'⟩ = ⟨y, hyDV.1⟩ :=
      E.morIsoDom_ϕ_mk_of_mem_sheet σ hτ hy hy' hyDV.1 hyD'
    have e₁ := Lu.pullOrx_univ_eq_orxViaAt (D'.isFredholm hfT).toIsScFredholmSection
      (D.isFredholm hfT).toIsScFredholmSection hfL D'.hasSections D.hasSections
      (D.pushLoc hfT o) ⟨y', hyD'⟩ (StrongBundle.Dom.mem_smoothSet hyD' hys') hϕ'
    have e₂ := StrongBundle.LocalIso.orxViaAt_germ (L := Lu) (L₃ := E.morIsoDom σ D D')
      (D'.isFredholm hfT).toIsScFredholmSection (D.isFredholm hfT).toIsScFredholmSection hfL
      (E.sec_eqOn_morIsoDom hF hfT.isScSmooth.1 σ D D') D'.hasSections D.hasSections
      (mem_univ _) (E.mem_morIsoDomSet_of_mem_sheet σ hτ hy hy' hyDV.1 hyD')
      (StrongBundle.Dom.mem_smoothSet hyD' hys') hϕ' hϕ'
      ⟨⟨univ, isOpen_univ, mem_univ _, subset_rfl, fun w _ => hmemS w, fun _ _ => rfl,
        fun _ _ => rfl⟩⟩
    have e₃ := DFunLike.congr_fun (E.orMorLoc_eq_orxViaAt_sheet hF hfT σ hτ hy hy' D D' hyDV.1
      hyD' hys hys') (o y hys)
    refine (ho'D y' hyD' hys').trans ((congrArg (D'.toLoc hfT y' hyD' hys').symm ?_).trans e₃)
    exact e₁.trans (DFunLike.congr_fun e₂ _)
  exact ⟨D'.carrier, o', ⟨B.mem_domAt x', hxW⟩, fun y hy => hy.2.1, hcont,
    (hval σ (X.mem_sheetAt σ) hx hx' hs hs' ⟨B.mem_domAt x', hxW⟩).2, hval⟩

/-! ### Definition 12.5.4 -/

/-- **Definition 12.5.4**, p. 594, with `Lin(f, x)` made with local sc⁺-sections: an orientation
of the sc-Fredholm section functor `f`, a global section `x ↦ o_x` of `σ : O_f → X_∞` which is
continuous for the topology of Theorem 12.5.3 and satisfies `φ_* o_x = o_{x'}` for every
morphism `φ : x → x'` between smooth objects. -/
def definition_12_5_4_loc (hX : X.PObj.IsTame) (hF : E.IsScFredholmSectionFunctor f)
    (hfT : B.IsScFredholmSectionTame f)
    (o : ∀ x (hs : x ∈ X.PObj.smoothSet), OrxLoc hfT x hs) : Prop :=
  @Continuous _ _ _ (orTopologyLoc hX hfT) ((orLocalTransportLoc hX hfT).sec o) ∧
    ∀ (φ : Mor) {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
      (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet),
      E.orMorLoc hF hfT φ hx hx' hs hs' (o x hs) = o x' hs'

/-- **Definition 12.5.4 with the continuity read along paths**: `o` is an orientation of `f`
iff the transport of orientations along every sc-smooth path of smooth objects takes `o` at
its start to `o` at its end, and `o` is invariant under the morphisms. -/
theorem definition_12_5_4_loc_iff (hX : X.PObj.IsTame) (hF : E.IsScFredholmSectionFunctor f)
    (hfT : B.IsScFredholmSectionTame f)
    (o : ∀ x (hs : x ∈ X.PObj.smoothSet), OrxLoc hfT x hs) :
    E.definition_12_5_4_loc hX hF hfT o ↔
      (orLocalTransportLoc hX hfT).IsContOn univ o ∧
        ∀ (φ : Mor) {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
          (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet),
          E.orMorLoc hF hfT φ hx hx' hs hs' (o x hs) = o x' hs' :=
  and_congr_left fun _ => (orLocalTransportLoc hX hfT).isContOn_univ_iff_continuous_sec
    fun _ hy => exists_two_orxLoc hfT hy

end EpStrongBundle

end Mor

end Polyfold
