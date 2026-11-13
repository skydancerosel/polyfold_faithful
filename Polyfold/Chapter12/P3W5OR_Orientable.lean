import Polyfold.Chapter12.P3W5OR_Germ
import Polyfold.Chapter7.NaturalRep

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 595: **Proposition 12.5.6 (⇐)** (2017: Proposition 12.4), with the continuity of the
orientation.

# A continuous section of `|σ|` gives a continuous orientation

If `|σ| : |O_f| → |X_∞|` is `(2 : 1)` and has a continuous global section `s`, the invariant
section `o` of `σ` with `|(x, o_x)| = s(|x|)` (`proposition_12_5_6_mpr_invariant`) is continuous
for Part I's topology on `O_f`, so `o` is an orientation in the sense of Definition 12.5.4.

The proof, near a smooth `x₀`:
* a continuous orientation `ô` over an open `U₀ ∋ x₀` with `ô_{x₀} = o_{x₀}`
  (`exists_isContOrOn`);
* `orMor_isotropy_of_isTwoToOne`: since `|σ|` is `(2 : 1)`, every `g ∈ G_{x₀}` fixes `ô_{x₀}`;
* `exists_nhds_orMor_eq_hyp`: by the natural representation of `G_{x₀}` (Theorem 7.1.13) and the
  last sentence of Theorem 12.5.3 for the morphisms `g` (`theorem_12_5_3_push_hyp`,
  `pullOrx_morIso_eq_orMor`), there is an open `V ∋ x₀` such that every morphism `φ : z → y`
  between points of `V` maps `ô_z` to `ô_y`;
* `isOpen_orSat_hyp`: the saturation of `{(z, ô_z) | z ∈ V}` is open in `O_f` (again by
  Theorem 12.5.3, last sentence), so its image in `|O_f|` is open;
* the continuity of `s` then gives `o_y = ô_y` for `y` near `x₀`.

* `EpStrongBundle.proposition_12_5_6_mpr_hyp`: with Part I's hypotheses (tame `X`, bump functions,
  tame germ data), as `theorem_12_5_3_hyp`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

section Orientable

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}
  (hF : E.IsScFredholmSectionFunctor f) (hsec : B.HasScPlusSectionsThrough)

/-- **Over a `(2 : 1)` `|σ|`, two orientations at `x` in the same class are equal.** -/
theorem eq_of_quot_eq_of_isTwoToOne (h₂ : E.IsTwoToOne hF hsec) {x : X.PObj.SmoothLevel}
    {ω₁ ω₂ : Orx f hF.2 _ (X.PObj.smoothVal_mem x)}
    (h : Quot.mk (E.OrRel hF hsec) ⟨x, ω₁⟩ = Quot.mk (E.OrRel hF hsec) ⟨x, ω₂⟩) : ω₁ = ω₂ := by
  by_contra hne
  obtain ⟨d₁, d₂, hd, hp₁, hp₂, -⟩ := h₂ (Quot.mk _ x)
  obtain ⟨b, -, hall⟩ := exists_other_or hF.2 hsec (X.PObj.smoothVal_mem x) ω₁
  have key : ∀ d, E.orbitProj hF hsec d = Quot.mk _ x →
      d = Quot.mk (E.OrRel hF hsec) ⟨x, ω₁⟩ := by
    intro d hd'
    induction d using Quot.ind with
    | mk p =>
      obtain ⟨y, ω⟩ := p
      change Quot.mk X.SmoothRel y = Quot.mk X.SmoothRel x at hd'
      obtain ⟨φ, hy, hx⟩ := EpGroupoid.smoothRel_of_quot_eq hd'
      rw [show Quot.mk (E.OrRel hF hsec) ⟨y, ω⟩ =
        Quot.mk (E.OrRel hF hsec) ⟨x, E.orMor hF hsec φ hy hx _ _ ω⟩ from
          Quot.sound ⟨φ, hy, hx, rfl⟩]
      rcases hall (E.orMor hF hsec φ hy hx _ _ ω) with h' | h'
      · rw [h']
      · rcases hall ω₂ with h'' | h''
        · exact absurd h''.symm hne
        · rw [h', ← h'']
          exact h.symm
  exact hd ((key d₁ hp₁).trans (key d₂ hp₂).symm)

/-- **Over a `(2 : 1)` `|σ|`, the isotropy acts trivially on orientations.** -/
theorem orMor_isotropy_of_isTwoToOne (h₂ : E.IsTwoToOne hF hsec) {x : Obj}
    (hs : x ∈ X.PObj.smoothSet) (g : X.Isotropy x) (ω : Orx f hF.2 x hs) :
    E.orMor hF hsec g.val g.src_val g.tgt_val hs hs ω = ω :=
  (E.eq_of_quot_eq_of_isTwoToOne hF hsec h₂ (x := X.PObj.smoothMk x hs)
    (Quot.sound ⟨g.val, g.src_val, g.tgt_val, rfl⟩)).symm

/-- `σ_* o_x` depends only on `σ` (with the source read off `σ`). -/
theorem orMor_eq_of_eq {σ σ' : Mor} (hσ : σ = σ') {x x₁ x' : Obj} (hx : X.src σ = x)
    (hx₁ : X.src σ' = x₁) (hx' : X.tgt σ = x') (hx'' : X.tgt σ' = x')
    (hs : x ∈ X.PObj.smoothSet) (hs₁ : x₁ ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet)
    (o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy) :
    E.orMor hF hsec σ hx hx' hs hs' (o x hs) = E.orMor hF hsec σ' hx₁ hx'' hs₁ hs' (o x₁ hs₁) := by
  subst hσ hx hx₁
  rfl

section Push

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
  (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (hfT : B.IsScFredholmSectionTame f)

/-- **Near `x₀`, a continuous orientation agreeing with the isotropy is invariant under all
morphisms**: if `|σ|` is `(2 : 1)` and `ô` is a continuous orientation over an open `U₀ ∋ x₀`,
there is an open `V ∋ x₀` in `U₀` such that `φ_* ô_z = ô_y` for every morphism `φ : z → y` between
smooth points of `V`.  By the natural representation (Theorem 7.1.13) such a `φ` is `Γ(g, z)` for
a `g ∈ G_{x₀}`, and lies in the sheet of `g`; the section carried by the isomorphism of `g` is
continuous (Theorem 12.5.3, last sentence), equal to `g_* ô_{x₀} = ô_{x₀}` at `x₀`, hence to `ô`
near `x₀`, and at `y` it is `φ_* ô_z` (`pullOrx_morIso_eq_orMor`). -/
theorem exists_nhds_orMor_eq_hyp (h₂ : E.IsTwoToOne hF hsec) {x₀ : Obj}
    (hs₀ : x₀ ∈ X.PObj.smoothSet) {U₀ : Set Obj}
    {ô : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy}
    (hô : IsContOrOn (orLocalTransport hX hbump hfT hsec) U₀ ô) (hx₀ : x₀ ∈ U₀) :
    ∃ V : Set Obj, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U₀ ∧ ∀ (φ : Mor) {z y : Obj} (hz : X.src φ = z)
      (hy : X.tgt φ = y) (hzs : z ∈ X.PObj.smoothSet) (hys : y ∈ X.PObj.smoothSet), z ∈ V →
        y ∈ V → E.orMor hF hsec φ hz hy hzs hys (ô z hzs) = ô y hys := by
  obtain ⟨R, hRU⟩ := EpGroupoid.theorem_7_1_13 X x₀ hô.1 hx₀
  have hg : ∀ g : X.Isotropy x₀, ∃ N : Set Obj, IsOpen N ∧ x₀ ∈ N ∧
      ∀ y ∈ N, ∀ hys : y ∈ X.PObj.smoothSet,
        (E.morIso g.val).pullOrx hF.2 hF.2 (E.eqOn_morIso_of_functor hF g.val) hsec hsec ô y
          hys = ô y hys := by
    intro g
    obtain ⟨hC, hmem, hval⟩ := E.theorem_12_5_3_push_hyp hF hsec hX hbump hfT g.val g.src_val
      g.tgt_val hs₀ hs₀ hô
    obtain ⟨N, hNo, hxN, hNW, hpath⟩ :=
      exists_nhds_scPath_of_isOpen B (hC.1.inter hô.1) ⟨hmem hx₀, hx₀⟩
    refine ⟨N, hNo, hxN, fun y hy hys => ?_⟩
    obtain ⟨γ, hγ, h₀, h₁, hγW⟩ := hpath _ hxN _ hy hs₀ hys
    rw [← hC.2 γ hγ (fun s _ => (hγW _).1) h₀ h₁ hs₀ hys,
      ← hô.2 γ hγ (fun s _ => (hγW _).2) h₀ h₁ hs₀ hys, hval,
      E.orMor_isotropy_of_isTwoToOne hF hsec h₂ hs₀ g]
  choose N hNo hxN hN using hg
  let M : X.Isotropy x₀ → Set Obj := fun g => R.U ∩ R.Γ g ⁻¹' (X.sheetAt g.val).carrier
  have hMo : ∀ g, IsOpen (M g) := fun g =>
    (R.isScSmoothOn_Γ g).continuousOn.isOpen_inter_preimage R.isOpen_U
      (X.sheetAt g.val).isScDiffeoOn_tgt.isScSmoothOn.isOpen
  have hxM : ∀ g, x₀ ∈ M g := fun g =>
    ⟨R.mem_U, by rw [mem_preimage, R.Γ_self]; exact X.mem_sheetAt _⟩
  refine ⟨R.U ∩ ⋂ g, (N g ∩ M g), R.isOpen_U.inter (isOpen_iInter_of_finite fun g =>
    (hNo g).inter (hMo g)), ⟨R.mem_U, mem_iInter.2 fun g => ⟨hxN g, hxM g⟩⟩,
    fun y hy => hRU hy.1, ?_⟩
  intro φ z y hz hy hzs hys hzV hyV
  obtain ⟨g, hg, -⟩ := R.existsUnique_Γ φ (hz ▸ hzV.1) (hy ▸ hyV.1)
  have hzM : R.Γ g z ∈ (X.sheetAt g.val).carrier := (mem_iInter.1 hzV.2 g).2.2
  have hyN : y ∈ N g := (mem_iInter.1 hyV.2 g).1
  rw [hz] at hg
  have hφS : φ ∈ (X.sheetAt g.val).carrier := hg ▸ hzM
  have hyT : y ∈ (X.sheetAt g.val).tgtSet := hy ▸ (X.sheetAt g.val).isScDiffeoOn_tgt.mapsTo hφS
  have hinv : (X.sheetAt g.val).tgtInv y = φ :=
    hy ▸ (X.sheetAt g.val).isScDiffeoOn_tgt.left_inv φ hφS
  have hϕz : (E.morIso g.val).ϕ y = z := by rw [morIso_ϕ, hinv, hz]
  have e := E.pullOrx_morIso_eq_orMor hF hsec g.val hyT (hϕz ▸ hzs) hys ô
  rw [hN g y hyN hys] at e
  exact (E.orMor_eq_of_eq hF hsec hinv.symm hz _ hy _ hzs _ hys ô).trans e.symm

/-- **The saturation of `{(z, ô_z) | z ∈ V}` is open in `O_f`** (Part I's topology): the set of
`(y, φ_* ô_z)` for the morphisms `φ : z → y` with `z ∈ V`.  Near such a point the section carried
by the isomorphism of `φ` is continuous (Theorem 12.5.3, last sentence), and its points are of the
same form (`pullOrx_morIso_eq_orMor`). -/
theorem isOpen_orSat_hyp {V : Set Obj} {ô : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy}
    (hô : IsContOrOn (orLocalTransport hX hbump hfT hsec) V ô) :
    IsOpen[orTopology (orLocalTransport hX hbump hfT hsec)]
      (Quot.mk (E.OrRel hF hsec) ⁻¹' {d | ∃ w : X.PObj.SmoothLevel, X.PObj.smoothVal w ∈ V ∧
        Quot.mk (E.OrRel hF hsec) ⟨w, ô _ (X.PObj.smoothVal_mem w)⟩ = d}) := by
  let := orTopology (orLocalTransport hX hbump hfT hsec)
  refine isOpen_iff_forall_mem_open.2 fun p ⟨w, hwV, hwp⟩ => ?_
  obtain ⟨φ, hz, hy, hφ⟩ := E.orRel_of_quot_eq hF hsec hwp
  obtain ⟨hC, hmem, hval⟩ := E.theorem_12_5_3_push_hyp hF hsec hX hbump hfT φ hz hy
    (X.PObj.smoothVal_mem w) (X.PObj.smoothVal_mem p.1) hô
  refine ⟨orBasic _ ((E.morIso φ).pullOrx hF.2 hF.2 (E.eqOn_morIso_of_functor hF φ) hsec hsec ô),
    fun q hq => ?_, isOpen_orBasic hC, hmem hwV, (hval.trans hφ).symm⟩
  have hqT : X.PObj.smoothVal q.1 ∈ (X.sheetAt φ).tgtSet := hq.1.1
  have hqs : (E.morIso φ).ϕ (X.PObj.smoothVal q.1) ∈ X.PObj.smoothSet :=
    ((E.morIso φ).mem_smoothSet_iff hqT).1 (X.PObj.smoothVal_mem q.1)
  refine ⟨X.PObj.smoothMk _ hqs, hq.1.2, Quot.sound ⟨(X.sheetAt φ).tgtInv _, rfl,
    (X.sheetAt φ).isScDiffeoOn_tgt.right_inv _ hqT, ?_⟩⟩
  exact (E.pullOrx_morIso_eq_orMor hF hsec φ hqT hqs (X.PObj.smoothVal_mem q.1) ô).symm.trans
    hq.2.symm

/-- **Proposition 12.5.6 (⇐)**, p. 595 (2017: Proposition 12.4), with Part I's topology and the
instance arguments of Part I's transport: if `|σ|` is `(2 : 1)` and has a continuous global
section `s`, then `f` has an orientation `o` (Definition 12.5.4: continuous for Part I's topology
and invariant under morphisms) with `|(x, o_x)| = s(|x|)`. -/
theorem proposition_12_5_6_mpr_hyp' (h₂ : E.IsTwoToOne hF hsec)
    {s : Quot X.SmoothRel → Quot (E.OrRel hF hsec)} (hs : ∀ c, E.orbitProj hF hsec (s c) = c) :
    letI : TopologicalSpace (OrSpace f hF.2) := orTopology (orLocalTransport hX hbump hfT hsec)
    Continuous s → ∃ o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs,
      E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hfT hsec)) o ∧
        ∀ x : X.PObj.SmoothLevel, Quot.mk (E.OrRel hF hsec) (orSec o x) = s (Quot.mk _ x) := by
  let : TopologicalSpace (OrSpace f hF.2) := orTopology (orLocalTransport hX hbump hfT hsec)
  intro hsc
  obtain ⟨o, hinv, hos⟩ := E.proposition_12_5_6_mpr_invariant hF hsec h₂ hs
  refine ⟨o, ⟨continuous_iff_continuousAt.2 fun y₀ => ?_, hinv⟩, hos⟩
  have hs₀ := X.PObj.smoothVal_mem y₀
  obtain ⟨U₀, ô, hô, -, hmem⟩ := exists_isContOrOn (orLocalTransport hX hbump hfT hsec)
    (⟨y₀, o _ hs₀⟩ : OrSpace f hF.2)
  obtain ⟨V, hVo, hx₀V, hVU, hsign⟩ :=
    E.exists_nhds_orMor_eq_hyp hF hsec hX hbump hfT h₂ hs₀ hô hmem.1
  have hôV := hô.mono_or hVo hVU
  set A : Set (Quot (E.OrRel hF hsec)) := {d | ∃ w : X.PObj.SmoothLevel,
    X.PObj.smoothVal w ∈ V ∧ Quot.mk (E.OrRel hF hsec) ⟨w, ô _ (X.PObj.smoothVal_mem w)⟩ = d}
  have hA : IsOpen A := E.isOpen_orSat_hyp hF hsec hX hbump hfT hôV
  have hG : IsOpen (Quot.mk X.SmoothRel ⁻¹' (s ⁻¹' A)) :=
    (hA.preimage hsc).preimage continuous_quot_mk
  have hy₀G : y₀ ∈ Quot.mk X.SmoothRel ⁻¹' (s ⁻¹' A) := by
    simp only [A, mem_preimage, mem_ofPred_eq]
    refine ⟨y₀, hx₀V, ?_⟩
    have e : o _ hs₀ = ô _ hs₀ := hmem.2
    rw [← hos y₀, orSec, e]
  have hVs : IsOpen (X.PObj.smoothVal ⁻¹' V) := hVo.preimage X.PObj.continuous_smoothVal
  have hc : ContinuousAt (orSec ô) y₀ :=
    (continuousOn_orSec hôV).continuousAt (hVs.mem_nhds hx₀V)
  refine hc.congr ?_
  filter_upwards [hG.mem_nhds hy₀G, hVs.mem_nhds hx₀V] with y hyG hyV
  obtain ⟨w, hwV, hw⟩ := hyG
  rw [← hos y] at hw
  obtain ⟨φ, hz, hy, hφ⟩ := E.orRel_of_quot_eq hF hsec hw
  change orSec ô y = orSec o y
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact (hsign φ hz hy _ _ hwV hyV).symm.trans hφ

end Push

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- **Proposition 12.5.6 (⇐)**, p. 595 (2017: Proposition 12.4), with Part I's hypotheses (tame
`X`, bump functions, tame germ data, as `theorem_12_5_3_hyp`) and Part I's topology on `O_f`:
if `|σ| : |O_f| → |X_∞|` is `(2 : 1)` and has a continuous global section `s`, then `f` is
orientable, by an orientation `o` with `|(x, o_x)| = s(|x|)`. -/
theorem proposition_12_5_6_mpr_hyp [ParacompactSpace (pullbackSpace P X.src)]
    (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions)
    (hfT : B.IsScFredholmSectionTame f) (hF : E.IsScFredholmSectionFunctor f)
    (h₂ : E.IsTwoToOne hF hbump.hasScPlusSectionsThrough)
    {s : Quot X.SmoothRel → Quot (E.OrRel hF hbump.hasScPlusSectionsThrough)}
    (hs : ∀ c, E.orbitProj hF hbump.hasScPlusSectionsThrough (s c) = c) :
    haveI := paracompactSpace_rn_prod X.PObj
    haveI := paracompactSpace_rn_pullback B
    haveI := paracompactSpace_rn_rn_prod X.PObj
    haveI := paracompactSpace_rn_rn_pullback B
    letI : TopologicalSpace (OrSpace f hF.2) :=
      orTopology (orLocalTransport hX hbump hfT hbump.hasScPlusSectionsThrough)
    Continuous s → ∃ o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs,
      E.definition_12_5_4 hF hbump.hasScPlusSectionsThrough
        (orTopology (orLocalTransport hX hbump hfT hbump.hasScPlusSectionsThrough)) o ∧
      ∀ x : X.PObj.SmoothLevel, Quot.mk (E.OrRel hF hbump.hasScPlusSectionsThrough) (orSec o x) =
        s (Quot.mk _ x) := by
  have := paracompactSpace_rn_prod X.PObj
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod X.PObj
  have := paracompactSpace_rn_rn_pullback B
  exact E.proposition_12_5_6_mpr_hyp' hF hbump.hasScPlusSectionsThrough hX hbump hfT h₂ hs

end EpStrongBundle

end Orientable

end Polyfold
