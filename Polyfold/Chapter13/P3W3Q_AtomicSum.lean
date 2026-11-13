import Polyfold.Chapter13.P3W3Q_Commensurable
import Polyfold.Chapter13.P3A_Atomic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.5, p. 635: **Theorem 13.5.7** (a structurable sc⁺-multisection is a locally finite
commensurable sum of atomic ones) (2017: Theorem 13.10).

# Structurable sc⁺-multisections as sums of atomic ones

## The text, paraphrased

(Theorem 13.5.7) Let `|X|` be paracompact and let `X` admit sc-smooth partitions of unity.  For a
structurable `Λ` there is a locally finite family of commensurable structured
`([Λⱼ, 𝒰, Sⱼ, τ])_{j ∈ J}`, each `Λⱼ` atomic, with `[Λ, 𝒰, S, τ] = ⊕^c_j [Λⱼ, 𝒰, Sⱼ, τ]`.  Proof:
for a structured lift `(Λ, 𝒰, S, τ)` take a locally finite refinement `(Vⱼ)` of `(|U(x)|)` with
`cl(Vⱼ) ⊆ |U(xⱼ)|` and a subordinate partition of unity `(βⱼ)`; `Sⱼ = (βⱼ·sˣᵢ)` defines `Λⱼ`,
which is atomic at `xⱼ` because `βⱼ` vanishes off `π⁻¹(Vⱼ) ∩ U(xⱼ)`, whose closure lies in
`U(xⱼ)` by Lemma 13.1.1.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `AtomicDataOn`, `IsAtomicOn`: Definition 13.5.1 with `U(x)` an open neighbourhood carrying the
  natural `G_x`-action and the properness property (a `NatNbhd`, as in the good systems of §13.1).
  `IsAtomic.isAtomicOn`: `IsAtomic` of `P3A_Atomic`, where `U(x)` is the (connected) domain of
  a natural representation, is a special case.
* **Theorem 13.5.7**: `theorem_13_5_7` for every structured tuple `T = (Λ, 𝒰, S, τ)` (the text's
  "a structured lift"), with `J = X` (the points `xⱼ`): the family `Λⱼ = βⱼ ⊙ Λ` over the data of
  `T`, locally finite, each `IsAtomicOn`, with the commensurable sum equal to `Λ`, with the same
  sections on every `U(x)`, and the same structured class.  `theorem_13_5_7_book`: the statement for
  a structurable `Λ`.

## Reading

The atomic `Λⱼ` live on `U(xⱼ)` of the good system, which carries the natural action and the
properness property but need not be connected; `IsAtomic` (`P3A_Atomic`) asks `U(x)` to be
the domain of a natural representation with the properness property, which the good system
does not provide.  So the theorem is proved with `IsAtomicOn` (Definition 13.5.1 read with the
`U(x)` of §13.1).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### Definition 13.5.1 on a neighbourhood with the natural action -/

/-- **The data of 2021 Definition 13.5.1 (1)–(2), p. 629, on a neighbourhood with the natural
action**: a point `x`, an open neighbourhood `U(x)` with the natural `G_x`-action (`NatNbhd`) and
`t : s⁻¹(cl U(x)) → X` proper, an open `G_x`-invariant `V(x) ∋ x` with `cl V(x) ⊆ U(x)`, and a
symmetric family `(sᵢ)_{i ∈ I}` of sc⁺-sections on `U(x)` vanishing on `U(x) ∖ V(x)`. -/
structure AtomicDataOn (A : SEP.{u}) where
  /-- The point `x`. -/
  x : A.Obj
  /-- `U(x)` with the natural action. -/
  N : A.X.NatNbhd x
  isProperSubset_closure : A.X.IsProperSubset (closure N.U)
  /-- The neighbourhood `V(x)`. -/
  V : Set A.Obj
  isOpen_V : IsOpen V
  mem_V : x ∈ V
  mapsTo_V : ∀ g, MapsTo (N.rep.Φ g) V V
  closure_V_subset : closure V ⊆ N.U
  /-- The index set `I_x`. -/
  I : Type u
  [fintype : Fintype I]
  [mulAction : MulAction (A.X.Isotropy x) I]
  /-- The sections `sᵢ`. -/
  s : I → A.Obj → A.W
  isScPlusSectionOn : ∀ i, IsScPlusSectionOn A (s i) N.U
  /-- `s_{g(i)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))`. -/
  equivariant : ∀ (g : A.X.Isotropy x) (i : I), ∀ y ∈ N.U,
    s (g • i) (N.rep.Φ g y) = fibAct (N.rep.Γ g y) (s i y)
  /-- The sections vanish on `U(x) ∖ V(x)`. -/
  vanish : ∀ i, ∀ y ∈ N.U, y ∉ V → s i y = fiberZero A.P y

attribute [instance] AtomicDataOn.fintype AtomicDataOn.mulAction

namespace AtomicDataOn

variable (D : AtomicDataOn A)

/-- `|I_x|⁻¹·#{i ∈ I_x | sᵢ(P(w)) = w}`. -/
def count (w : A.W) : ℚ≥0 :=
  (Fintype.card D.I : ℚ≥0)⁻¹ * ((Finset.univ.filter fun i => D.s i (A.P w) = w).card : ℚ≥0)

/-- Some morphism joins `y` to a point of `U(x)`. -/
def Reach (y : A.Obj) : Prop := ∃ φ : A.Mor, A.X.src φ = y ∧ A.X.tgt φ ∈ D.N.U

/-- **Condition (3) of Definition 13.5.1** on `U(x)`. -/
def IsRelated (Λ : A.W → ℚ≥0) : Prop :=
  (∀ (w : A.W) (φ : A.Mor) (h : A.P w = A.X.src φ), A.X.tgt φ ∈ D.N.U →
    Λ w = D.count (A.E.μ ⟨(φ, w), h⟩)) ∧
  ∀ w, ¬ D.Reach (A.P w) → Λ w = zeroMultisection A w

end AtomicDataOn

/-- **2021 Definition 13.5.1, p. 629 (2017: Definition 13.23), with `U(x)` a neighbourhood
carrying the natural `G_x`-action**: `Λ` is an sc⁺-multisection related to the data of an
`AtomicDataOn`. -/
def IsAtomicOn (A : SEP.{u}) (Λ : A.W → ℚ≥0) : Prop :=
  IsScPlusMultisection A Λ ∧ ∃ D : AtomicDataOn A, D.IsRelated Λ

/-- The data of `AtomicData` (`P3A_Atomic`) (on the domain of a natural representation). -/
def AtomicData.toOn (D : AtomicData A) : AtomicDataOn A where
  x := D.x
  N := NatNbhd.ofRep D.R
  isProperSubset_closure := D.hasPropernessProperty.2
  V := D.V
  isOpen_V := D.isOpen_V
  mem_V := D.mem_V
  mapsTo_V := D.mapsTo_V
  closure_V_subset := D.closure_V_subset
  I := D.I
  s := D.s
  isScPlusSectionOn := D.isScPlusSectionOn
  equivariant g i y hy := (D.equivariant g i y hy).trans (fibAct_of _).symm
  vanish := D.vanish

/-- **Atomic in the sense of `IsAtomic` (domain of a natural representation) is atomic on a
neighbourhood with the natural action.** -/
theorem IsAtomic.isAtomicOn {Λ : A.W → ℚ≥0} (h : IsAtomic A Λ) : IsAtomicOn A Λ := by
  obtain ⟨hΛ, D, h1, h2⟩ := h
  exact ⟨hΛ, D.toOn, h1, h2⟩

/-! ### Theorem 13.5.7 -/

namespace CommData

/-- **The data `(βⱼ·sˣᵢ)`** over the data of a structured tuple (Lemma 13.3.14 for `β`). -/
def smulFunOver (T : StructuredTuple A) {β : A.Obj → ℝ}
    (hβ : ∀ φ : A.Mor, β (A.X.tgt φ) = β (A.X.src φ))
    (hβs : A.X.PObj.IsScSmoothMap realPolyfold β) :
    (ofTuple T).Over (multisectionSmulFun β T.Λ) where
  s x i := SymmetricStructureOn.smulSection (T.dec.𝒰.U x) β ((T.dec.S x).s i)
  isScPlusSectionOn x := ((T.dec.S x).smulFun T.isScPlusMultisection hβ hβs).isScPlusSectionOn
  equivariant x := ((T.dec.S x).smulFun T.isScPlusMultisection hβ hβs).equivariant
  rep x := ((T.dec.S x).smulFun T.isScPlusMultisection hβ hβs).rep
  compat x x' := ((T.tau.smulFun T.isScPlusMultisection hβ hβs).isCorrespondence x x').compat

end CommData

/-- `β ⊙ Λ` is trivial where `β = 0`. -/
theorem multisectionSmulFun_of_eq_zero {β : A.Obj → ℝ} {Λ : A.W → ℚ≥0} {w : A.W}
    (h : β (A.P w) = 0) : multisectionSmulFun β Λ w = zeroMultisection A w := by
  unfold multisectionSmulFun
  rw [h, multisectionSmul_zero]

/-- The open sets `O_x ∋ |x|` of `|X|` with `cl(O_x) ⊆ |U(x)|` (regularity of `|X|`, Lemma
7.3.5). -/
theorem exists_orbit_nbhd (𝒰 : A.X.GoodSystem) (x : A.Obj) :
    ∃ O : Set A.X.OrbitSpace, IsOpen O ∧ A.X.π x ∈ O ∧ closure O ⊆ A.X.π '' 𝒰.U x := by
  have hU : A.X.π '' 𝒰.U x ∈ 𝓝 (A.X.π x) :=
    (A.X.proposition_7_1_8 _ (𝒰.isOpen_U x)).mem_nhds (mem_image_of_mem _ (𝒰.mem_U x))
  obtain ⟨C, hC, hCc, hCU⟩ := exists_mem_nhds_isClosed_subset hU
  obtain ⟨O, hOC, hO, hxO⟩ := mem_nhds_iff.1 hC
  exact ⟨O, hO, hxO, (closure_minimal hOC hCc).trans hCU⟩

/-- **2021 Theorem 13.5.7, p. 635 (2017: Theorem 13.10)**, for every structured tuple
`T = (Λ, 𝒰, S, τ)`: if `|X|` is paracompact and `X` admits sc-smooth partitions of unity, there is
a locally finite family `(Λⱼ)_{j ∈ X}` with structures `[Λⱼ, 𝒰, Sⱼ, τ]` over the data `c` of `T`,
each `Λⱼ` atomic (on `U(xⱼ)`, `xⱼ = j`), whose commensurable sum `⊕^c_j Λⱼ` is `Λ`, with the same
sections `sˣᵢ` on every `U(x)` and the same structured class `[Λ, 𝒰, S, τ]`. -/
theorem theorem_13_5_7 (hpu : A.X.HasScPartitionsOfUnity) (T : StructuredTuple A) :
    ∃ (Λf : A.Obj → A.W → ℚ≥0) (o : ∀ j, (CommData.ofTuple T).Over (Λf j))
      (hlf : IsLocallyFiniteFamily Λf),
      (∀ j, IsAtomicOn A (Λf j)) ∧ CommData.lfSum o hlf = T.Λ ∧
      (∀ x (i : (CommData.ofTuple T).I x), ∀ y ∈ T.dec.𝒰.U x,
        (CommData.Over.lfSum o hlf).s x i y = (T.dec.S x).s i y) ∧
      (CommData.Over.lfSum o hlf).toStructured = Quotient.mk _ T := by
  set 𝒰 := T.dec.𝒰 with h𝒰
  have hΛ := T.isScPlusMultisection
  -- the shrunken cover `π⁻¹(O_x)` and a subordinate partition of unity
  choose O hOo hxO hOcl using exists_orbit_nbhd (A := A) 𝒰
  obtain ⟨β, hsub, hβs, hlfβ, hβinv⟩ := hpu A.Obj (fun x => A.X.π ⁻¹' O x)
    (fun x => (hOo x).preimage A.X.continuous_π)
    (fun x => A.X.isSaturated_iff.2 fun φ hφ => by
      change A.X.π (A.X.tgt φ) ∈ O x
      rw [← A.X.π_src_eq_π_tgt φ]; exact hφ)
    (eq_univ_of_forall fun y => mem_iUnion.2 ⟨y, hxO y⟩)
  have hβ : ∀ j (φ : A.Mor), β j (A.X.tgt φ) = β j (A.X.src φ) := fun j φ => (hβinv j φ).symm
  let Λf : A.Obj → A.W → ℚ≥0 := fun j => multisectionSmulFun (β j) T.Λ
  let o : ∀ j, (CommData.ofTuple T).Over (Λf j) := fun j => CommData.smulFunOver T (hβ j) (hβs j)
  -- local finiteness
  have hlf : IsLocallyFiniteFamily Λf := fun y => by
    obtain ⟨W, hWo, hWs, hyW, hWf⟩ := hlfβ y
    refine ⟨W, hWo, hWs, hyW, hWf.subset fun j ⟨w, hw, hw0, hpos⟩ => ?_⟩
    by_contra hne
    have h0 : β j (A.P w) = 0 := by
      by_contra h0
      exact hne ⟨A.P w, hw, subset_tsupport _ h0⟩
    have : Λf j w = zeroMultisection A w := multisectionSmulFun_of_eq_zero h0
    rw [this] at hpos
    unfold zeroMultisection at hpos
    rw [if_neg hw0] at hpos
    exact lt_irrefl _ hpos
  -- the sections of the sum are the original ones
  have hsec : ∀ x (i : (CommData.ofTuple T).I x), ∀ y ∈ 𝒰.U x,
      (CommData.Over.lfSum o hlf).s x i y = (T.dec.S x).s i y := fun x i y hy => by
    rw [(CommData.definition_13_4_5_lf o hlf).2.1 x i y hy]
    have hP : A.P ((T.dec.S x).s i y) = y := (T.dec.S x).P_s i hy
    have e : ∀ j, (⟨(o j).s x i y, ((o j).isScPlusSectionOn x i).1 y hy⟩ : A.P ⁻¹' {y}) =
        β j y • (⟨(T.dec.S x).s i y, hP⟩ : A.P ⁻¹' {y}) := fun j =>
      Subtype.ext (SymmetricStructureOn.smulSection_apply hy hP)
    rw [finsum_congr e, ← finsum_smul' (β.locallyFinite.point_finite y),
      β.sum_eq_one (mem_univ y), one_smul]
  -- the functors agree
  have hmult : CommData.lfSum o hlf = T.Λ := by
    funext w
    have hw : A.P w ∈ 𝒰.U (A.P w) := 𝒰.mem_U _
    rw [(CommData.Over.lfSum o hlf).rep (A.P w) w hw, (CommData.Over.ofTuple T).rep (A.P w) w hw]
    unfold CommData.countAt
    congr 3
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hsec _ i _ hw]
    rfl
  refine ⟨Λf, o, hlf, fun j => ?_, hmult, hsec, ?_⟩
  · -- `Λⱼ` is atomic at `j`
    refine ⟨(o j).isScPlusMultisection, ?_⟩
    set N := 𝒰.nbhd j
    set V := 𝒰.U j ∩ A.X.π ⁻¹' O j
    have hVo : IsOpen V := (𝒰.isOpen_U j).inter ((hOo j).preimage A.X.continuous_π)
    have hVcl : closure V ⊆ N.U := by
      refine (A.X.lemma_13_1_1 N (𝒰.isProperSubset_closure j) inter_subset_left).2 ?_
      exact (closure_mono (image_subset_iff.2 fun y hy => hy.2)).trans (hOcl j)
    let D : AtomicDataOn A :=
      { x := j
        N := N
        isProperSubset_closure := 𝒰.isProperSubset_closure j
        V := V
        isOpen_V := hVo
        mem_V := ⟨𝒰.mem_U j, hxO j⟩
        mapsTo_V := fun g y hy => ⟨N.Φ_mem g hy.1, by
          change A.X.π _ ∈ O j
          rw [N.π_Φ g (N.mem_rep_U hy.1)]; exact hy.2⟩
        closure_V_subset := hVcl
        I := (CommData.ofTuple T).I j
        s := (o j).s j
        isScPlusSectionOn := (o j).isScPlusSectionOn j
        equivariant := (o j).equivariant j
        vanish := fun i y hy hyV => by
          have h0 : β j y = 0 := by
            by_contra h0
            exact hyV ⟨hy, hsub j (subset_tsupport _ h0)⟩
          have hP : A.P ((T.dec.S j).s i y) = y := (T.dec.S j).P_s i hy
          have e := SymmetricStructureOn.smulSection_apply (U := T.dec.𝒰.U j) (c := ⇑(β j))
            (s₁ := (T.dec.S j).s i) hy hP
          rw [h0, zero_smul] at e
          exact e }
    refine ⟨D, fun w φ h ht => ?_, fun w hw => ?_⟩
    · have e1 : Λf j w = Λf j (A.E.μ ⟨(φ, w), h⟩) :=
        ((o j).isScPlusMultisection.1 ⟨(φ, w), h⟩).symm
      rw [e1, (o j).rep j _ (by rw [A.E.P_μ]; exact ht)]
      rfl
    · refine multisectionSmulFun_of_eq_zero ?_
      by_contra h0
      have hmem := hsub j (subset_tsupport _ h0)
      obtain ⟨z, hz, hzw⟩ : A.X.π (A.P w) ∈ A.X.π '' 𝒰.U j := hOcl j (subset_closure hmem)
      obtain ⟨φ, hφs, hφt⟩ := (A.X.π_eq_π_iff).1 hzw.symm
      exact hw ⟨φ, hφs, hφt ▸ hz⟩
  · -- the structured classes agree
    refine Quotient.sound ⟨hmult, 𝒰, fun x => subset_inter subset_rfl subset_rfl, fun x => rfl,
      fun x x' φ _ => (IndexCorr.map_cast_rfl _).symm⟩

/-- **2021 Theorem 13.5.7, p. 635, for a structurable `Λ`**: `Λ` has a structured lift
`[Λ, 𝒰, S, τ]` which is the commensurable sum of a locally finite family of atomic
`[Λⱼ, 𝒰, Sⱼ, τ]`.  (`|X|` paracompact is the text's hypothesis; it is used only through the
existence of structured lifts and partitions of unity, which are hypotheses here.) -/
theorem theorem_13_5_7_book (_hpara : A.X.HasParacompactOrbitSpace)
    (hpu : A.X.HasScPartitionsOfUnity) {Λ : A.W → ℚ≥0} (hΛ : IsStructurable A Λ) :
    ∃ (T : StructuredTuple A) (Λf : A.Obj → A.W → ℚ≥0)
      (o : ∀ j, (CommData.ofTuple T).Over (Λf j)) (hlf : IsLocallyFiniteFamily Λf),
      T.Λ = Λ ∧ (∀ j, IsAtomicOn A (Λf j)) ∧ CommData.lfSum o hlf = Λ ∧
      (CommData.Over.lfSum o hlf).toStructured = Quotient.mk _ T := by
  obtain ⟨hΛ', D, ⟨t⟩⟩ := hΛ
  obtain ⟨Λf, o, hlf, hat, hsum, -, hcl⟩ := theorem_13_5_7 hpu ⟨⟨Λ, hΛ', D⟩, t⟩
  exact ⟨_, Λf, o, hlf, rfl, hat, hsum, hcl⟩

end SBLocalization

end Polyfold
