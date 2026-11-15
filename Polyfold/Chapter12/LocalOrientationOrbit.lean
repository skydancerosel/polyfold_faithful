import Polyfold.Chapter12.LocalOrientationBundleEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
Proposition 12.5.6 (p. 595), with Definition 12.5.2 (p. 593), Theorem 12.5.3 (p. 594) and
Definition 12.5.4 (p. 594).

# Orientations and the orbit space of the orientation bundle, with local sc⁺-sections

## The text, paraphrased

`(P : W → X, μ)` is a strong bundle over a tame ep-groupoid and `f` an sc-Fredholm section
functor.  The morphisms act on the orientation bundle `σ : O_f → X_∞`, and passing to orbit
spaces gives `|σ| : |O_f| → |X_∞|`.  Proposition 12.5.6: `f` is orientable if and only if
`|σ|` is `(2 : 1)` and admits a continuous global section.

## What is formalized

`Lin(f, x)` is made with local sc⁺-sections as in the text (`OrxLoc`); the hypotheses are a
tame object M-polyfold and tame germ data of `f` only.  The orbit spaces are the quotients
`Quot X.SmoothRel` and `Quot (E.OrRelLoc hX hF hfT)` with the quotient topologies of `X_∞` and
of the topology of Theorem 12.5.3 on `O_f` (the text does not define them).

* `OrRelLoc`: the relation `(x, o) ~ (x', φ_* o)` on `O_f`, an equivalence relation
  (`orRelLoc_equivalence`); `orbitProjLoc`: the map `|σ|`; `IsTwoToOneLoc`: `|σ|` is `(2 : 1)`.
* `proposition_12_5_6_mp_loc`: **Proposition 12.5.6 (⇒)**: an orientation `o` of `f`
  (Definition 12.5.4) gives that `|σ|` is `(2 : 1)`, with the continuous section
  `|x| ↦ |(x, o_x)|`.
* `proposition_12_5_6_mpr_invariant_loc`: a `(2 : 1)` map `|σ|` with a section `s` gives an
  invariant section `o` of `σ` with `|(x, o_x)| = s(|x|)`.
* `proposition_12_5_6_mpr_loc`: **Proposition 12.5.6 (⇐)**: if moreover `s` is continuous, `o`
  is continuous, hence an orientation of `f`.  Near a smooth `x₀`: a continuous orientation `ô`
  over an open `U₀ ∋ x₀` with `ô_{x₀} = o_{x₀}`; the isotropy group fixes `ô_{x₀}`
  (`orMorLoc_isotropy_of_isTwoToOneLoc`); by the natural representation of `G_{x₀}`
  (Theorem 7.1.13) and the last sentence of Theorem 12.5.3 there is an open `V ∋ x₀` such that
  every morphism between points of `V` maps `ô` to `ô` (`exists_nhds_orMorLoc_eq`); the
  saturation of `{(z, ô_z) | z ∈ V}` is open (`isOpen_orSatLoc`); the continuity of `s` gives
  `o = ô` near `x₀`.
* `proposition_12_5_6_loc`: **Proposition 12.5.6**, the equivalence as printed.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

section Mor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}
  (hX : X.PObj.IsTame) (hF : E.IsScFredholmSectionFunctor f)
  (hfT : B.IsScFredholmSectionTame f)

/-! ### The orbit space of the orientation bundle -/

/-- **`(x, o) ~ (x', φ_* o)`**: the relation on `O_f` given by the morphisms, for the local
orientation sets. -/
def OrRelLoc (p q : OrSpaceLoc hX hfT) : Prop :=
  ∃ (φ : Mor) (hx : X.src φ = X.PObj.smoothVal p.1) (hx' : X.tgt φ = X.PObj.smoothVal q.1),
    E.orMorLoc hF hfT φ hx hx' (X.PObj.smoothVal_mem _) (X.PObj.smoothVal_mem _) p.2 = q.2

/-- `~` is an equivalence relation (units, inverses and composites act functorially). -/
theorem orRelLoc_equivalence : Equivalence (E.OrRelLoc hX hF hfT) :=
  ⟨fun p => ⟨X.unit _, X.src_unit _, X.tgt_unit _,
      DFunLike.congr_fun (E.orMorLoc_unit hF hfT rfl _ _ _) p.2⟩,
    fun {p q} ⟨φ, hx, hx', h⟩ => ⟨X.inv φ, (X.src_inv φ).trans hx', (X.tgt_inv φ).trans hx, by
      have e := DFunLike.congr_fun (E.orMorLoc_inv hF hfT hx hx' (X.PObj.smoothVal_mem p.1)
        (X.PObj.smoothVal_mem q.1)) q.2
      exact e.trans ((Equiv.symm_apply_eq _).2 h.symm)⟩,
    fun {p q r} ⟨φ, hx, hx', h₁⟩ ⟨ψ, hy, hy', h₂⟩ => ⟨X.comp ψ φ, src_comp_eq hx hx' hy,
      tgt_comp_eq hx' hy hy', by
        have e := DFunLike.congr_fun (E.orMorLoc_comp hF hfT hx hx' hy hy'
          (X.PObj.smoothVal_mem p.1) (X.PObj.smoothVal_mem q.1) (X.PObj.smoothVal_mem r.1)) p.2
        exact e.symm.trans ((congrArg _ h₁).trans h₂)⟩⟩

theorem orRelLoc_of_quot_eq {p q : OrSpaceLoc hX hfT}
    (h : Quot.mk (E.OrRelLoc hX hF hfT) p = Quot.mk (E.OrRelLoc hX hF hfT) q) :
    E.OrRelLoc hX hF hfT p q :=
  (E.orRelLoc_equivalence hX hF hfT).eqvGen_iff.1 (Quot.eqvGen_exact h)

/-- **`|σ| : |O_f| → |X_∞|`** for the local orientation sets. -/
def orbitProjLoc : Quot (E.OrRelLoc hX hF hfT) → Quot X.SmoothRel :=
  Quot.map (orLocalTransportLoc hX hfT).proj fun _ _ ⟨φ, hx, hx', _⟩ => ⟨φ, hx, hx'⟩

/-- `|σ|` is `(2 : 1)`: over every class `|x|` lie exactly two classes. -/
def IsTwoToOneLoc : Prop :=
  ∀ c : Quot X.SmoothRel, ∃ d₁ d₂ : Quot (E.OrRelLoc hX hF hfT), d₁ ≠ d₂ ∧
    E.orbitProjLoc hX hF hfT d₁ = c ∧ E.orbitProjLoc hX hF hfT d₂ = c ∧
      ∀ d, E.orbitProjLoc hX hF hfT d = c → d = d₁ ∨ d = d₂

/-! ### Proposition 12.5.6 (⇒) -/

/-- **Proposition 12.5.6 (⇒)**, p. 595, with `Lin(f, x)` made with local sc⁺-sections, for a
tame object M-polyfold and a section functor with tame germ data: if `f` has an orientation `o`
(Definition 12.5.4), then `|σ| : |O_f| → |X_∞|` is `(2 : 1)` and has a continuous global
section, `|x| ↦ |(x, o_x)|`.  The orbit spaces carry the quotient topologies. -/
theorem proposition_12_5_6_mp_loc {o : ∀ x (hs : x ∈ X.PObj.smoothSet), OrxLoc hfT x hs}
    (ho : E.definition_12_5_4_loc hX hF hfT o) :
    letI : TopologicalSpace (OrSpaceLoc hX hfT) := orTopologyLoc hX hfT
    E.IsTwoToOneLoc hX hF hfT ∧ ∃ s : Quot X.SmoothRel → Quot (E.OrRelLoc hX hF hfT),
      Continuous s ∧ (∀ c, E.orbitProjLoc hX hF hfT (s c) = c) ∧
      ∀ x : X.PObj.SmoothLevel, s (Quot.mk _ x) =
        Quot.mk (E.OrRelLoc hX hF hfT) ((orLocalTransportLoc hX hfT).sec o x) := by
  let : TopologicalSpace (OrSpaceLoc hX hfT) := orTopologyLoc hX hfT
  refine ⟨fun c => ?_, ?_⟩
  · induction c using Quot.ind with
    | mk x =>
      obtain ⟨b, hb, hall⟩ := exists_other_orLoc hfT (X.PObj.smoothVal_mem x)
        (o _ (X.PObj.smoothVal_mem x))
      refine ⟨Quot.mk _ ⟨x, o _ (X.PObj.smoothVal_mem x)⟩, Quot.mk _ ⟨x, b⟩, fun h => ?_, rfl,
        rfl, fun d hd => ?_⟩
      · obtain ⟨φ, hx, hx', hφ⟩ := E.orRelLoc_of_quot_eq hX hF hfT h
        exact hb (hφ.symm.trans (ho.2 φ hx hx' _ _))
      · induction d using Quot.ind with
        | mk p =>
          obtain ⟨y, ω⟩ := p
          change Quot.mk X.SmoothRel y = Quot.mk X.SmoothRel x at hd
          obtain ⟨φ, hy, hx⟩ := EpGroupoid.smoothRel_of_quot_eq hd
          obtain ⟨b', hb', hall'⟩ := exists_other_orLoc hfT (X.PObj.smoothVal_mem y)
            (o _ (X.PObj.smoothVal_mem y))
          have hs₀ := X.PObj.smoothVal_mem x
          have hs₁ := X.PObj.smoothVal_mem y
          have hinv := ho.2 φ hy hx hs₁ hs₀
          rcases hall' ω with h | h
          · refine Or.inl (Quot.sound ⟨φ, hy, hx, ?_⟩)
            exact (congrArg (E.orMorLoc hF hfT φ hy hx hs₁ hs₀) h).trans hinv
          · refine Or.inr (Quot.sound ⟨φ, hy, hx, ?_⟩)
            rcases hall (E.orMorLoc hF hfT φ hy hx hs₁ hs₀ ω) with h' | h'
            · exact absurd (h.symm.trans ((E.orMorLoc hF hfT φ hy hx hs₁ hs₀).injective
                (h'.trans hinv.symm))) hb'
            · exact h'
  · refine ⟨Quot.lift (fun x => Quot.mk (E.OrRelLoc hX hF hfT)
        ((orLocalTransportLoc hX hfT).sec o x))
      (fun a b ⟨φ, ha, hb⟩ => Quot.sound ⟨φ, ha, hb, ho.2 φ ha hb _ _⟩),
      continuous_quot_lift _ (continuous_quot_mk.comp ho.1), fun c => ?_, fun _ => rfl⟩
    induction c using Quot.ind with
    | mk x => rfl

/-! ### Proposition 12.5.6 (⇐) -/

/-- **Over a `(2 : 1)` `|σ|`, two orientations at `x` in the same class are equal.** -/
theorem eq_of_quot_eq_of_isTwoToOneLoc (h₂ : E.IsTwoToOneLoc hX hF hfT)
    {x : X.PObj.SmoothLevel} {ω₁ ω₂ : OrxLoc hfT _ (X.PObj.smoothVal_mem x)}
    (h : Quot.mk (E.OrRelLoc hX hF hfT) ⟨x, ω₁⟩ = Quot.mk (E.OrRelLoc hX hF hfT) ⟨x, ω₂⟩) :
    ω₁ = ω₂ := by
  by_contra hne
  obtain ⟨d₁, d₂, hd, hp₁, hp₂, -⟩ := h₂ (Quot.mk _ x)
  obtain ⟨b, -, hall⟩ := exists_other_orLoc hfT (X.PObj.smoothVal_mem x) ω₁
  have key : ∀ d, E.orbitProjLoc hX hF hfT d = Quot.mk _ x →
      d = Quot.mk (E.OrRelLoc hX hF hfT) ⟨x, ω₁⟩ := by
    intro d hd'
    induction d using Quot.ind with
    | mk p =>
      obtain ⟨y, ω⟩ := p
      change Quot.mk X.SmoothRel y = Quot.mk X.SmoothRel x at hd'
      obtain ⟨φ, hy, hx⟩ := EpGroupoid.smoothRel_of_quot_eq hd'
      have e : Quot.mk (E.OrRelLoc hX hF hfT) ⟨y, ω⟩ =
          Quot.mk (E.OrRelLoc hX hF hfT) ⟨x, E.orMorLoc hF hfT φ hy hx _ _ ω⟩ :=
        Quot.sound ⟨φ, hy, hx, rfl⟩
      rcases hall (E.orMorLoc hF hfT φ hy hx _ _ ω) with h' | h'
      · exact e.trans (congrArg (fun ω' => Quot.mk (E.OrRelLoc hX hF hfT) ⟨x, ω'⟩) h')
      · rcases hall ω₂ with h'' | h''
        · exact absurd h''.symm hne
        · exact e.trans ((congrArg (fun ω' => Quot.mk (E.OrRelLoc hX hF hfT) ⟨x, ω'⟩)
            (h'.trans h''.symm)).trans h.symm)
  exact hd ((key d₁ hp₁).trans (key d₂ hp₂).symm)

/-- **Proposition 12.5.6 (⇐), without continuity**, p. 595, for the local orientation sets: if
`|σ|` is `(2 : 1)` and has a global section `s`, then there is a section `x ↦ o_x` of `σ` with
`φ_* o_x = o_{x'}` for every morphism `φ : x → x'` and `|(x, o_x)| = s(|x|)`. -/
theorem proposition_12_5_6_mpr_invariant_loc (h₂ : E.IsTwoToOneLoc hX hF hfT)
    {s : Quot X.SmoothRel → Quot (E.OrRelLoc hX hF hfT)}
    (hs : ∀ c, E.orbitProjLoc hX hF hfT (s c) = c) :
    ∃ o : ∀ x (hs : x ∈ X.PObj.smoothSet), OrxLoc hfT x hs,
      (∀ (φ : Mor) {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
        (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet),
        E.orMorLoc hF hfT φ hx hx' hs hs' (o x hs) = o x' hs') ∧
      ∀ x : X.PObj.SmoothLevel, Quot.mk (E.OrRelLoc hX hF hfT)
        ((orLocalTransportLoc hX hfT).sec o x) = s (Quot.mk _ x) := by
  have hex : ∀ x : X.PObj.SmoothLevel, ∃ ω : OrxLoc hfT _ (X.PObj.smoothVal_mem x),
      Quot.mk (E.OrRelLoc hX hF hfT) ⟨x, ω⟩ = s (Quot.mk _ x) := by
    intro x
    obtain ⟨⟨y, ω⟩, hyω⟩ := Quot.exists_rep (s (Quot.mk _ x))
    have hp := hs (Quot.mk _ x)
    rw [← hyω] at hp
    change Quot.mk X.SmoothRel y = Quot.mk X.SmoothRel x at hp
    obtain ⟨φ, hy, hx⟩ := EpGroupoid.smoothRel_of_quot_eq hp
    exact ⟨E.orMorLoc hF hfT φ hy hx _ _ ω, (Quot.sound ⟨φ, hy, hx, rfl⟩).symm.trans hyω⟩
  choose ω hω using hex
  refine ⟨fun x hs => ω (X.PObj.smoothMk x hs), fun φ x x' hx hx' hs hs' => ?_, fun x => hω x⟩
  refine E.eq_of_quot_eq_of_isTwoToOneLoc hX hF hfT h₂ (x := X.PObj.smoothMk x' hs') ?_
  have e₁ : Quot.mk (E.OrRelLoc hX hF hfT) ⟨X.PObj.smoothMk x' hs',
      E.orMorLoc hF hfT φ hx hx' hs hs' (ω (X.PObj.smoothMk x hs))⟩ =
      Quot.mk (E.OrRelLoc hX hF hfT) ⟨X.PObj.smoothMk x hs, ω (X.PObj.smoothMk x hs)⟩ :=
    (Quot.sound ⟨φ, hx, hx', rfl⟩).symm
  have e₂ : Quot.mk X.SmoothRel (X.PObj.smoothMk x hs) = Quot.mk _ (X.PObj.smoothMk x' hs') :=
    Quot.sound ⟨φ, hx, hx'⟩
  exact e₁.trans ((hω _).trans ((congrArg s e₂).trans (hω _).symm))

/-- **Over a `(2 : 1)` `|σ|`, the isotropy acts trivially on orientations.** -/
theorem orMorLoc_isotropy_of_isTwoToOneLoc (h₂ : E.IsTwoToOneLoc hX hF hfT) {x : Obj}
    (hs : x ∈ X.PObj.smoothSet) (g : X.Isotropy x) (ω : OrxLoc hfT x hs) :
    E.orMorLoc hF hfT g.val g.src_val g.tgt_val hs hs ω = ω :=
  (E.eq_of_quot_eq_of_isTwoToOneLoc hX hF hfT h₂ (x := X.PObj.smoothMk x hs)
    (Quot.sound ⟨g.val, g.src_val, g.tgt_val, rfl⟩)).symm

/-- **Near `x₀`, a continuous orientation fixed by the isotropy is invariant under all
morphisms**: if `|σ|` is `(2 : 1)` and `ô` is a continuous orientation over an open `U₀ ∋ x₀`,
there is an open `V ∋ x₀` in `U₀` such that `φ_* ô_z = ô_y` for every morphism `φ : z → y`
between smooth points of `V`.  By the natural representation (Theorem 7.1.13) such a `φ` lies
in the sheet of a `g ∈ G_{x₀}`; the section carried by the isomorphism of `g` is continuous
(Theorem 12.5.3, last sentence), equal to `g_* ô_{x₀} = ô_{x₀}` at `x₀`, hence to `ô` near
`x₀`, and at `y` it is `φ_* ô_z`. -/
theorem exists_nhds_orMorLoc_eq (h₂ : E.IsTwoToOneLoc hX hF hfT) {x₀ : Obj}
    (hs₀ : x₀ ∈ X.PObj.smoothSet) {U₀ : Set Obj}
    {ô : ∀ y (hy : y ∈ X.PObj.smoothSet), OrxLoc hfT y hy}
    (hô : (orLocalTransportLoc hX hfT).IsContOn U₀ ô) (hx₀ : x₀ ∈ U₀) :
    ∃ V : Set Obj, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U₀ ∧ ∀ (φ : Mor) {z y : Obj} (hz : X.src φ = z)
      (hy : X.tgt φ = y) (hzs : z ∈ X.PObj.smoothSet) (hys : y ∈ X.PObj.smoothSet), z ∈ V →
        y ∈ V → E.orMorLoc hF hfT φ hz hy hzs hys (ô z hzs) = ô y hys := by
  obtain ⟨R, hRU⟩ := EpGroupoid.theorem_7_1_13 X x₀ hô.1 hx₀
  have hg : ∀ g : X.Isotropy x₀, ∃ N : Set Obj, IsOpen N ∧ x₀ ∈ N ∧
      ∀ τ : Mor, τ ∈ (X.sheetAt g.val).carrier → ∀ (z y : Obj) (hz : X.src τ = z)
        (hy : X.tgt τ = y) (hzs : z ∈ X.PObj.smoothSet) (hys : y ∈ X.PObj.smoothSet),
        y ∈ N → E.orMorLoc hF hfT τ hz hy hzs hys (ô z hzs) = ô y hys := by
    intro g
    obtain ⟨V', o', hxV', -, hC, hval, hτ⟩ := E.theorem_12_5_3_push_loc hX hF hfT g.val
      g.src_val g.tgt_val hs₀ hs₀ hô hx₀
    obtain ⟨N, hNo, hxN, hNW, hpath⟩ :=
      exists_nhds_scPath_of_isOpen B (hC.1.inter hô.1) ⟨hxV', hx₀⟩
    refine ⟨N, hNo, hxN, fun τ hτS z y hz hy hzs hys hyN => ?_⟩
    obtain ⟨γ, hγ, h₀, h₁, hγW⟩ := hpath _ hxN _ hyN hs₀ hys
    have e₁ := hC.2 γ hγ (fun s _ => (hγW _).1) h₀ h₁ hs₀ hys
    have e₂ := hô.2 γ hγ (fun s _ => (hγW _).2) h₀ h₁ hs₀ hys
    have e₀ : o' x₀ hs₀ = ô x₀ hs₀ :=
      hval.trans (E.orMorLoc_isotropy_of_isTwoToOneLoc hX hF hfT h₂ hs₀ g _)
    exact (hτ τ hτS hz hy hzs hys (hNW hyN).1).2.symm.trans
      (e₁.symm.trans ((congrArg _ e₀).trans e₂))
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
  exact hN g φ hφS z y hz hy hzs hys hyN

/-- **The saturation of `{(z, ô_z) | z ∈ V}` is open in `O_f`**: the set of `(y, φ_* ô_z)` for
the morphisms `φ : z → y` with `z ∈ V`.  Near such a point the section carried by the
isomorphism of `φ` is continuous (Theorem 12.5.3, last sentence), and its points are of the
same form. -/
theorem isOpen_orSatLoc {V : Set Obj} {ô : ∀ y (hy : y ∈ X.PObj.smoothSet), OrxLoc hfT y hy}
    (hô : (orLocalTransportLoc hX hfT).IsContOn V ô) :
    IsOpen[orTopologyLoc hX hfT]
      (Quot.mk (E.OrRelLoc hX hF hfT) ⁻¹' {d | ∃ w : X.PObj.SmoothLevel,
        X.PObj.smoothVal w ∈ V ∧
        Quot.mk (E.OrRelLoc hX hF hfT) ⟨w, ô _ (X.PObj.smoothVal_mem w)⟩ = d}) := by
  let : TopologicalSpace (OrSpaceLoc hX hfT) := orTopologyLoc hX hfT
  refine isOpen_iff_forall_mem_open.2 fun p ⟨w, hwV, hwp⟩ => ?_
  obtain ⟨φ, hz, hy, hφ⟩ := E.orRelLoc_of_quot_eq hX hF hfT hwp
  obtain ⟨V', o', hpV', hV'T, hC, hval, hτ⟩ := E.theorem_12_5_3_push_loc hX hF hfT φ hz hy
    (X.PObj.smoothVal_mem w) (X.PObj.smoothVal_mem p.1) hô hwV
  refine ⟨(orLocalTransportLoc hX hfT).basic V' o', fun q hq => ?_,
    LocalTransport.isOpen_basic hC, ⟨hpV', (hval.trans hφ).symm⟩⟩
  have hqT : X.PObj.smoothVal q.1 ∈ (X.sheetAt φ).tgtSet := hV'T hq.1
  have hτS : (X.sheetAt φ).tgtInv (X.PObj.smoothVal q.1) ∈ (X.sheetAt φ).carrier :=
    (X.sheetAt φ).isScDiffeoOn_tgt.mapsTo_inv hqT
  have htgt : X.tgt ((X.sheetAt φ).tgtInv (X.PObj.smoothVal q.1)) = X.PObj.smoothVal q.1 :=
    (X.sheetAt φ).isScDiffeoOn_tgt.right_inv _ hqT
  have hqs : X.src ((X.sheetAt φ).tgtInv (X.PObj.smoothVal q.1)) ∈ X.PObj.smoothSet :=
    ((E.morIso φ).mem_smoothSet_iff hqT).1 (X.PObj.smoothVal_mem q.1)
  obtain ⟨hV, e⟩ := hτ _ hτS rfl htgt hqs (X.PObj.smoothVal_mem q.1) hq.1
  exact ⟨X.PObj.smoothMk _ hqs, hV, Quot.sound ⟨_, rfl, htgt, e.symm.trans hq.2.symm⟩⟩

/-- **Proposition 12.5.6 (⇐)**, p. 595, with `Lin(f, x)` made with local sc⁺-sections, for a
tame object M-polyfold and a section functor with tame germ data: if `|σ| : |O_f| → |X_∞|` is
`(2 : 1)` and has a continuous global section `s`, then `f` has an orientation `o`
(Definition 12.5.4: continuous for the topology of Theorem 12.5.3 and invariant under the
morphisms) with `|(x, o_x)| = s(|x|)`. -/
theorem proposition_12_5_6_mpr_loc (h₂ : E.IsTwoToOneLoc hX hF hfT)
    {s : Quot X.SmoothRel → Quot (E.OrRelLoc hX hF hfT)}
    (hs : ∀ c, E.orbitProjLoc hX hF hfT (s c) = c) :
    letI : TopologicalSpace (OrSpaceLoc hX hfT) := orTopologyLoc hX hfT
    Continuous s → ∃ o : ∀ x (hs : x ∈ X.PObj.smoothSet), OrxLoc hfT x hs,
      E.definition_12_5_4_loc hX hF hfT o ∧
        ∀ x : X.PObj.SmoothLevel, Quot.mk (E.OrRelLoc hX hF hfT)
          ((orLocalTransportLoc hX hfT).sec o x) = s (Quot.mk _ x) := by
  let : TopologicalSpace (OrSpaceLoc hX hfT) := orTopologyLoc hX hfT
  intro hsc
  obtain ⟨o, hinv, hos⟩ := E.proposition_12_5_6_mpr_invariant_loc hX hF hfT h₂ hs
  refine ⟨o, ⟨continuous_iff_continuousAt.2 fun y₀ => ?_, hinv⟩, hos⟩
  have hs₀ := X.PObj.smoothVal_mem y₀
  obtain ⟨U₀, ô, hô, -, hmem⟩ := (orLocalTransportLoc hX hfT).exists_isContOn
    (⟨y₀, o _ hs₀⟩ : OrSpaceLoc hX hfT)
  obtain ⟨V, hVo, hx₀V, hVU, hsign⟩ :=
    E.exists_nhds_orMorLoc_eq hX hF hfT h₂ hs₀ hô hmem.1
  have hôV := hô.mono hVo hVU
  set A : Set (Quot (E.OrRelLoc hX hF hfT)) := {d | ∃ w : X.PObj.SmoothLevel,
    X.PObj.smoothVal w ∈ V ∧
      Quot.mk (E.OrRelLoc hX hF hfT) ⟨w, ô _ (X.PObj.smoothVal_mem w)⟩ = d} with hAdef
  have hA : IsOpen A := E.isOpen_orSatLoc hX hF hfT hôV
  have hG : IsOpen (Quot.mk X.SmoothRel ⁻¹' (s ⁻¹' A)) :=
    (hA.preimage hsc).preimage continuous_quot_mk
  have hy₀G : y₀ ∈ Quot.mk X.SmoothRel ⁻¹' (s ⁻¹' A) := by
    refine ⟨y₀, hx₀V, ?_⟩
    have e : o _ hs₀ = ô _ hs₀ := hmem.2
    exact (congrArg (fun ω => Quot.mk (E.OrRelLoc hX hF hfT) ⟨y₀, ω⟩) e).symm.trans (hos y₀)
  have hVs : IsOpen (X.PObj.smoothVal ⁻¹' V) := hVo.preimage X.PObj.continuous_smoothVal
  have hc : ContinuousAt ((orLocalTransportLoc hX hfT).sec ô) y₀ :=
    (LocalTransport.continuousOn_sec hôV).continuousAt (hVs.mem_nhds hx₀V)
  refine hc.congr ?_
  filter_upwards [hG.mem_nhds hy₀G, hVs.mem_nhds hx₀V] with y hyG hyV
  obtain ⟨w, hwV, hw⟩ := hyG
  rw [← hos y] at hw
  obtain ⟨φ, hz, hy, hφ⟩ := E.orRelLoc_of_quot_eq hX hF hfT hw
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact (hsign φ hz hy _ _ hwV hyV).symm.trans hφ

/-! ### Proposition 12.5.6 -/

/-- **Proposition 12.5.6**, p. 595, with `Lin(f, x)` made with local sc⁺-sections, for a strong
bundle over an ep-groupoid with tame object M-polyfold and an sc-Fredholm section functor `f`
with tame germ data: `f` is orientable (Definition 12.5.4) if and only if
`|σ| : |O_f| → |X_∞|` is `(2 : 1)` and admits a continuous global section.  The orbit spaces
carry the quotient topologies of `X_∞` and of the topology of Theorem 12.5.3 on `O_f`. -/
theorem proposition_12_5_6_loc :
    letI : TopologicalSpace (OrSpaceLoc hX hfT) := orTopologyLoc hX hfT
    (∃ o : ∀ x (hs : x ∈ X.PObj.smoothSet), OrxLoc hfT x hs,
        E.definition_12_5_4_loc hX hF hfT o) ↔
      E.IsTwoToOneLoc hX hF hfT ∧ ∃ s : Quot X.SmoothRel → Quot (E.OrRelLoc hX hF hfT),
        Continuous s ∧ ∀ c, E.orbitProjLoc hX hF hfT (s c) = c := by
  let : TopologicalSpace (OrSpaceLoc hX hfT) := orTopologyLoc hX hfT
  constructor
  · rintro ⟨o, ho⟩
    obtain ⟨h₂, s, hsc, hs, -⟩ := E.proposition_12_5_6_mp_loc hX hF hfT ho
    exact ⟨h₂, s, hsc, hs⟩
  · rintro ⟨h₂, s, hsc, hs⟩
    obtain ⟨o, ho, -⟩ := E.proposition_12_5_6_mpr_loc hX hF hfT h₂ hs hsc
    exact ⟨o, ho⟩

end EpStrongBundle

end Mor

end Polyfold
