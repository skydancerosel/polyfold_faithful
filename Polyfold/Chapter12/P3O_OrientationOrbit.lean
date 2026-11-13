import Polyfold.Chapter12.P3O_OrientationBundleEp

/-!
# §12.5 The orientation bundle `O_f`, orientations, and orbit spaces

HWZ 2021, §12.5, pp. 593–595 (2017: §12.5).  `(P : W → X, μ)` is a strong bundle over an
ep-groupoid and `f` an sc-Fredholm section functor (`EpStrongBundle.IsScFredholmSectionFunctor`).

* `definition_12_5_2`: **Definition 12.5.2**, p. 593: `O_f` is Part I's orientation space of `f`
  as a section of the object bundle (`OrSpace`), with `σ = orProj : O_f → X_∞`.  `σ` is
  surjective and `(2 : 1)` (`orProj_two`), and a morphism `φ : x → x'` acts by
  `φ_* = EpStrongBundle.orMor` (functorial: `orMor_comp`, `orMor_unit`, `orMor_inv`).
  `OrRel` is the relation `(x, o) ~ (x', φ_* o)`; it is an equivalence (`orRel_equivalence`).
* `theorem_12_5_3_hyp`: **Theorem 12.5.3**, p. 594, the topological part: there is exactly one
  topology on `O_f` with the properties of Part I's Theorem 6.6.17 (Hausdorff, `σ` a local
  homeomorphism, two continuous local sections near each point, propagation), and the fibres of
  `σ` have two points.  The hypotheses are Part I's (`hX` tame, `hbump`, tame germ data in
  `IsScFredholmSectionTame`); the text assumes only a tame `X`.  The last sentence of the theorem
  (the local push-forward `Φ̂` of a morphism keeps local sections continuous) is not formalized
  here.
* `definition_12_5_4`: **Definition 12.5.4**, p. 594: an orientation is a continuous global section
  `x ↦ o_x` of `σ` with `φ_* o_{s(φ)} = o_{t(φ)}` for every smooth morphism.
* **Remark 12.5.5**, p. 595, is prose; the oriented solution sets it describes are those of
  Chapter 9/15 (`OrientedBranched`) and are not restated here.
* `proposition_12_5_6_mp`: **Proposition 12.5.6 (⇒)**, p. 595: if `f` is oriented, then
  `|σ| : |O_f| → |X_∞|` is `(2 : 1)` and has a continuous global section.
  `proposition_12_5_6_mpr_invariant`: (⇐) up to continuity: a `(2 : 1)` map `|σ|` with a global
  section gives a functorial section `o` of `σ` that lifts it.

The orbit spaces are the quotients `Quot X.SmoothRel` and `Quot (E.OrRel hF hsec)` with the quotient
topologies (the text does not define them).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

section Mor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpGroupoid

variable (X) in
/-- Two smooth objects are isomorphic: `|X_∞|` is the quotient by this relation. -/
def SmoothRel (a b : X.PObj.SmoothLevel) : Prop :=
  ∃ φ : Mor, X.src φ = X.PObj.smoothVal a ∧ X.tgt φ = X.PObj.smoothVal b

theorem smoothRel_equivalence : Equivalence X.SmoothRel :=
  ⟨fun _ => ⟨X.unit _, X.src_unit _, X.tgt_unit _⟩,
    fun ⟨φ, h1, h2⟩ => ⟨X.inv φ, (X.src_inv φ).trans h2, (X.tgt_inv φ).trans h1⟩,
    fun ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩ => ⟨X.comp ψ φ, (X.src_comp ψ φ (h3.trans h2.symm)).trans h1,
      (X.tgt_comp ψ φ (h3.trans h2.symm)).trans h4⟩⟩

theorem smoothRel_of_quot_eq {a b : X.PObj.SmoothLevel}
    (h : Quot.mk X.SmoothRel a = Quot.mk X.SmoothRel b) : X.SmoothRel a b :=
  smoothRel_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact h)

end EpGroupoid

/-! ### The fibres of `σ` -/

/-- **`σ : O_f → X_∞` is surjective and `(2 : 1)`** (Definition 12.5.2, p. 594). -/
theorem orProj_two {f : Obj → W} (hf : B.IsScFredholmSection f)
    (hsec : B.HasScPlusSectionsThrough) (x : X.PObj.SmoothLevel) :
    ∃ p q : OrSpace f hf, p ≠ q ∧ orProj f hf p = x ∧ orProj f hf q = x ∧
      ∀ r, orProj f hf r = x → r = p ∨ r = q := by
  obtain ⟨o₁, o₂, hne, hall⟩ := (orPt B _ (X.PObj.smoothVal_mem x)).exists_two_or hf
    (X.PObj.smoothVal_mem x) hsec
  refine ⟨⟨x, o₁⟩, ⟨x, o₂⟩, fun h => hne (eq_of_heq (Sigma.mk.inj_iff.1 h).2), rfl, rfl, ?_⟩
  rintro ⟨y, ω⟩ hr
  change y = x at hr
  subst hr
  rcases hall ω with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The other orientation: `Or_x^f` has exactly two elements. -/
theorem exists_other_or {f : Obj → W} (hf : B.IsScFredholmSection f)
    (hsec : B.HasScPlusSectionsThrough) {x : Obj} (hs : x ∈ X.PObj.smoothSet)
    (o : Orx f hf x hs) : ∃ o' : Orx f hf x hs, o' ≠ o ∧ ∀ o'', o'' = o ∨ o'' = o' := by
  obtain ⟨o₁, o₂, hne, hall⟩ := (orPt B x hs).exists_two_or hf hs hsec
  rcases hall o with rfl | rfl
  · exact ⟨o₂, hne.symm, hall⟩
  · exact ⟨o₁, hne, fun o'' => (hall o'').symm⟩

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}
  (hF : E.IsScFredholmSectionFunctor f) (hsec : B.HasScPlusSectionsThrough)

/-! ### Definition 12.5.2 -/

/-- **Definition 12.5.2**, p. 593 (2017: Definition 12.11): the orientation bundle `O_f` of an
sc-Fredholm section functor, the pairs `(x, o)` of a smooth object `x` and an orientation `o` of
`DET(f, x)`, i.e. Part I's `OrSpace` of `f` as a section of the object bundle.  Its projection
is `orProj`, its topology Part I's (`theorem_12_5_3_hyp`), and a morphism acts by `orMor`. -/
abbrev definition_12_5_2 : Type _ := OrSpace f hF.2

/-- **`(x, o) ~ (x', φ_* o)`**: the relation on `O_f` given by the morphisms. -/
def OrRel (p q : OrSpace f hF.2) : Prop :=
  ∃ (φ : Mor) (hx : X.src φ = X.PObj.smoothVal p.1) (hx' : X.tgt φ = X.PObj.smoothVal q.1),
    E.orMor hF hsec φ hx hx' (X.PObj.smoothVal_mem _) (X.PObj.smoothVal_mem _) p.2 = q.2

/-- `~` is an equivalence relation (units, inverses and composites act functorially). -/
theorem orRel_equivalence : Equivalence (E.OrRel hF hsec) :=
  ⟨fun p => ⟨X.unit _, X.src_unit _, X.tgt_unit _, by rw [E.orMor_unit hF hsec rfl]; rfl⟩,
    fun ⟨φ, hx, hx', h⟩ => ⟨X.inv φ, (X.src_inv φ).trans hx', (X.tgt_inv φ).trans hx, by
      rw [E.orMor_inv hF hsec hx hx', ← h, Equiv.symm_apply_apply]⟩,
    fun ⟨φ, hx, hx', h₁⟩ ⟨ψ, hy, hy', h₂⟩ => ⟨X.comp ψ φ, src_comp_eq hx hx' hy,
      tgt_comp_eq hx' hy hy', by
        rw [← E.orMor_comp hF hsec hx hx' hy hy' (X.PObj.smoothVal_mem _) (X.PObj.smoothVal_mem _)
          (X.PObj.smoothVal_mem _), Equiv.trans_apply, h₁, h₂]⟩⟩

theorem orRel_of_quot_eq {p q : OrSpace f hF.2}
    (h : Quot.mk (E.OrRel hF hsec) p = Quot.mk (E.OrRel hF hsec) q) : E.OrRel hF hsec p q :=
  (E.orRel_equivalence hF hsec).eqvGen_iff.1 (Quot.eqvGen_exact h)

/-- **`|σ| : |O_f| → |X_∞|`**. -/
def orbitProj : Quot (E.OrRel hF hsec) → Quot X.SmoothRel :=
  Quot.map (orProj f hF.2) fun _ _ ⟨φ, hx, hx', _⟩ => ⟨φ, hx, hx'⟩

/-! ### Theorem 12.5.3 -/

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- **Theorem 12.5.3**, p. 594 (2017: Theorem 12.11), the topological part, with Part I's
hypotheses: for a tame object M-polyfold with bump functions and an sc-Fredholm section with
tame germ data, `O_f` carries exactly one topology with the properties of Theorem 6.6.17
(`σ` a local homeomorphism, Hausdorff, exactly two continuous local sections near each point,
the propagation property), and every fibre of `σ` has two points.  The morphism action is
`orMor` (`orMor_comp`, `orMor_unit`, `orMor_inv`). -/
theorem theorem_12_5_3_hyp (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions)
    (hfT : B.IsScFredholmSectionTame f) :
    haveI := paracompactSpace_rn_prod X.PObj
    haveI := paracompactSpace_rn_pullback B
    (∃! t : TopologicalSpace (OrSpace f hfT.toIsScFredholmSection),
      IsOrientationTopology f hfT.toIsScFredholmSection t) ∧
    ∀ x : X.PObj.SmoothLevel, ∃ p q : OrSpace f hfT.toIsScFredholmSection, p ≠ q ∧
      orProj f _ p = x ∧ orProj f _ q = x ∧ ∀ r, orProj f _ r = x → r = p ∨ r = q :=
  ⟨theorem_6_6_17 hX hbump hfT,
    orProj_two _ (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump)⟩

/-! ### Definition 12.5.4 -/

/-- **Definition 12.5.4**, p. 594 (2017: Definition 12.12): an orientation of `f` for a topology
`t` on `O_f`: a global section `x ↦ o_x` of `σ`, continuous for `t`, with `φ_* o_x = o_{x'}`
for every morphism `φ : x → x'` between smooth objects. -/
def definition_12_5_4 (t : TopologicalSpace (OrSpace f hF.2))
    (o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs) : Prop :=
  @Continuous _ _ _ t (orSec o) ∧
    ∀ (φ : Mor) {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
      (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet),
      E.orMor hF hsec φ hx hx' hs hs' (o x hs) = o x' hs'

/-! ### Proposition 12.5.6 -/

section Orbit

variable [t : TopologicalSpace (OrSpace f hF.2)]

/-- `|σ|` is `(2 : 1)`: over every class `|x|` lie exactly two classes. -/
def IsTwoToOne : Prop :=
  ∀ c : Quot X.SmoothRel, ∃ d₁ d₂ : Quot (E.OrRel hF hsec), d₁ ≠ d₂ ∧
    E.orbitProj hF hsec d₁ = c ∧ E.orbitProj hF hsec d₂ = c ∧
      ∀ d, E.orbitProj hF hsec d = c → d = d₁ ∨ d = d₂

/-- **Proposition 12.5.6 (⇒)**, p. 595 (2017: Proposition 12.4): if `f` has an orientation `o`
(Definition 12.5.4), then `|σ| : |O_f| → |X_∞|` is `(2 : 1)` and has a continuous global
section, `|x| ↦ |(x, o_x)|`. -/
theorem proposition_12_5_6_mp {o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs}
    (ho : E.definition_12_5_4 hF hsec t o) :
    E.IsTwoToOne hF hsec ∧ ∃ s : Quot X.SmoothRel → Quot (E.OrRel hF hsec),
      Continuous s ∧ ∀ c, E.orbitProj hF hsec (s c) = c := by
  refine ⟨fun c => ?_, ?_⟩
  · induction c using Quot.ind with
    | mk x =>
      obtain ⟨b, hb, hall⟩ := exists_other_or hF.2 hsec (X.PObj.smoothVal_mem x)
        (o _ (X.PObj.smoothVal_mem x))
      refine ⟨Quot.mk _ ⟨x, o _ (X.PObj.smoothVal_mem x)⟩, Quot.mk _ ⟨x, b⟩, fun h => ?_, rfl,
        rfl, fun d hd => ?_⟩
      · obtain ⟨φ, hx, hx', hφ⟩ := E.orRel_of_quot_eq hF hsec h
        exact hb (hφ.symm.trans (ho.2 φ hx hx' _ _))
      · induction d using Quot.ind with
        | mk p =>
          obtain ⟨y, ω⟩ := p
          change Quot.mk X.SmoothRel y = Quot.mk X.SmoothRel x at hd
          obtain ⟨φ, hy, hx⟩ := EpGroupoid.smoothRel_of_quot_eq hd
          obtain ⟨b', hb', hall'⟩ := exists_other_or hF.2 hsec (X.PObj.smoothVal_mem y)
            (o _ (X.PObj.smoothVal_mem y))
          have hs₀ := X.PObj.smoothVal_mem x
          have hs₁ := X.PObj.smoothVal_mem y
          have hinv := ho.2 φ hy hx hs₁ hs₀
          rcases hall' ω with h | h
          · refine Or.inl (Quot.sound ⟨φ, hy, hx, ?_⟩)
            exact (congrArg (E.orMor hF hsec φ hy hx hs₁ hs₀) h).trans hinv
          · refine Or.inr (Quot.sound ⟨φ, hy, hx, ?_⟩)
            rcases hall (E.orMor hF hsec φ hy hx hs₁ hs₀ ω) with h' | h'
            · exact absurd (h.symm.trans ((E.orMor hF hsec φ hy hx hs₁ hs₀).injective
                (h'.trans hinv.symm))) hb'
            · exact h'
  · refine ⟨Quot.lift (fun x => Quot.mk (E.OrRel hF hsec) (orSec o x))
      (fun a b ⟨φ, ha, hb⟩ => Quot.sound ⟨φ, ha, hb, ho.2 φ ha hb _ _⟩),
      continuous_quot_lift _ (continuous_quot_mk.comp ho.1), fun c => ?_⟩
    induction c using Quot.ind with
    | mk x => rfl

omit t in
/-- **Proposition 12.5.6 (⇐), without continuity**, p. 595 (2017: Proposition 12.4): if
`|σ|` is `(2 : 1)` and has a global section `s`, then there is a section `x ↦ o_x` of `σ` with
`φ_* o_x = o_{x'}` for every morphism `φ : x → x'` and `|(x, o_x)| = s(|x|)`.  The continuity
of `o` for Part I's topology needs the push-forward clause of Theorem 12.5.3 (not formalized). -/
theorem proposition_12_5_6_mpr_invariant (h₁ : E.IsTwoToOne hF hsec)
    {s : Quot X.SmoothRel → Quot (E.OrRel hF hsec)} (hs : ∀ c, E.orbitProj hF hsec (s c) = c) :
    ∃ o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs,
      (∀ (φ : Mor) {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
        (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet),
        E.orMor hF hsec φ hx hx' hs hs' (o x hs) = o x' hs') ∧
      ∀ x : X.PObj.SmoothLevel, Quot.mk (E.OrRel hF hsec) (orSec o x) = s (Quot.mk _ x) := by
  have hex : ∀ x : X.PObj.SmoothLevel, ∃ ω : Orx f hF.2 _ (X.PObj.smoothVal_mem x),
      Quot.mk (E.OrRel hF hsec) ⟨x, ω⟩ = s (Quot.mk _ x) := by
    intro x
    obtain ⟨⟨y, ω⟩, hyω⟩ := Quot.exists_rep (s (Quot.mk _ x))
    have hp := hs (Quot.mk _ x)
    rw [← hyω] at hp
    change Quot.mk X.SmoothRel y = Quot.mk X.SmoothRel x at hp
    obtain ⟨φ, hy, hx⟩ := EpGroupoid.smoothRel_of_quot_eq hp
    exact ⟨E.orMor hF hsec φ hy hx _ _ ω, (Quot.sound ⟨φ, hy, hx, rfl⟩).symm.trans hyω⟩
  have huniq : ∀ (x : X.PObj.SmoothLevel) (ω₁ ω₂ : Orx f hF.2 _ (X.PObj.smoothVal_mem x)),
      Quot.mk (E.OrRel hF hsec) ⟨x, ω₁⟩ = s (Quot.mk _ x) →
      Quot.mk (E.OrRel hF hsec) ⟨x, ω₂⟩ = s (Quot.mk _ x) → ω₁ = ω₂ := by
    intro x ω₁ ω₂ e₁ e₂
    by_contra hne
    obtain ⟨d₁, d₂, hd, hp₁, hp₂, -⟩ := h₁ (Quot.mk _ x)
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
        rcases hall (E.orMor hF hsec φ hy hx _ _ ω) with h | h
        · rw [h]
        · rcases hall ω₂ with h' | h'
          · exact absurd h'.symm hne
          · rw [h, ← h', e₂, ← e₁]
    exact hd ((key d₁ hp₁).trans (key d₂ hp₂).symm)
  choose ω hω using hex
  refine ⟨fun x hs => ω (X.PObj.smoothMk x hs), fun φ x x' hx hx' hs hs' => ?_, fun x => hω x⟩
  refine huniq (X.PObj.smoothMk x' hs') _ _ ?_ (hω _)
  have e₁ : Quot.mk (E.OrRel hF hsec) ⟨X.PObj.smoothMk x' hs',
      E.orMor hF hsec φ hx hx' hs hs' (ω (X.PObj.smoothMk x hs))⟩ =
      Quot.mk (E.OrRel hF hsec) ⟨X.PObj.smoothMk x hs, ω (X.PObj.smoothMk x hs)⟩ :=
    (Quot.sound ⟨φ, hx, hx', rfl⟩).symm
  have e₂ : Quot.mk X.SmoothRel (X.PObj.smoothMk x hs) = Quot.mk _ (X.PObj.smoothMk x' hs') :=
    Quot.sound ⟨φ, hx, hx'⟩
  rw [e₁, hω, e₂]

end Orbit

end EpStrongBundle

end Mor

end Polyfold
