import Polyfold.Chapter13.AtomicSum

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.5, p. 635: **Theorem 13.5.7** with atomic summands in the sense of Definition 13.5.1 as
formalized by `IsAtomic` (2017: Theorem 13.10).

# Theorem 13.5.7 with `IsAtomic` summands

## The text, paraphrased

(Theorem 13.5.7, 2021 p. 635) Let `|X|` be paracompact and let `X` admit sc-smooth partitions of
unity.  For a structurable `Λ` there is a locally finite family of commensurable structured
`([Λⱼ, 𝒰, Sⱼ, τ])_{j ∈ J}`, each `Λⱼ` atomic, with `[Λ, 𝒰, S, τ] = ⊕^c_j [Λⱼ, 𝒰, Sⱼ, τ]`.

## What is formalized (namespace `Polyfold.SBLocalization`)

`theorem_13_5_7` (`AtomicSum`) gives summands which are atomic on the neighbourhoods `U(xⱼ)` of
the good system (`IsAtomicOn`); these need not be connected.  Here the construction of the proof
is rerun with the partition of unity subordinate to smaller sets, so that every `Λⱼ` is atomic on
the connected domain of a natural representation with the properness property (`IsAtomic`,
Definition 13.5.1 as formalized in `AtomicMultisection`).

* `connRep N`: the natural representation on the connected component of `x` in `U(x)`, with the
  same `Φ` and `Γ` (`NatRepConstruction.restrict`); `connRep_U_subset`,
  `hasPropernessProperty_connRep` (the properness property, from that of `cl U(x)`).
* `exists_orbit_nbhd_of_isOpen`: open `O ∋ |x|` in `|X|` with `cl(O) ⊆ |U|` for an open `U ∋ x`.
* **`theorem_13_5_7_isAtomic`**: Theorem 13.5.7 for every structured tuple `T = (Λ, 𝒰, S, τ)`,
  indexed by `X`, over the data of `T`, each `Λⱼ` `IsAtomic`, with the commensurable sum equal to
  `Λ`, the same sections `sˣᵢ` on every `U(x)` and the same structured class.
* **`theorem_13_5_7_isAtomic_book`**: the statement for a structurable `Λ`, with the structured
  lift `T`.
* **`theorem_13_5_7_isAtomic_sum`**: the statement in the form of the text: some common data `c`,
  a structure `o` of `Λ` over it and a family indexed by a type `J`.

## Reading

The sets `Vⱼ` of the proof are taken as `Uᶜ(xⱼ) ∩ π⁻¹(Oⱼ)`, where `Uᶜ(xⱼ)` is the connected
component of `xⱼ` in `U(xⱼ)` and `cl(Oⱼ) ⊆ |Uᶜ(xⱼ)|`; Lemma 13.1.1 for `Uᶜ(xⱼ)` gives
`cl(Vⱼ) ⊆ Uᶜ(xⱼ)`.  The sections `βⱼ·sˣᵢ` on `Uᶜ(xⱼ)` are the restrictions of those on `U(xⱼ)`.
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

/-! ### The connected component of `U(x)` -/

/-- The connected component of `x` in a neighbourhood with the natural action is invariant. -/
theorem mapsTo_Φ_connectedComponentIn {x : A.Obj} (N : A.X.NatNbhd x)
    (g : A.X.Isotropy x) :
    MapsTo (N.rep.Φ g) (connectedComponentIn N.U x) (connectedComponentIn N.U x) := by
  intro y hy
  have hCW : connectedComponentIn N.U x ⊆ N.U := connectedComponentIn_subset _ _
  have hpre : IsPreconnected (N.rep.Φ g '' connectedComponentIn N.U x) :=
    isPreconnected_connectedComponentIn.image _
      ((N.rep.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn.mono (hCW.trans N.U_subset))
  exact hpre.subset_connectedComponentIn ⟨x, mem_connectedComponentIn N.mem_U, N.rep.Φ_self g⟩
    ((N.mapsTo_Φ g).mono_left hCW).image_subset ⟨y, hy, rfl⟩

/-- **The natural representation on the connected component of `x` in `U(x)`**, with the `Φ`
and `Γ` of `U(x)`. -/
def connRep {x : A.Obj} (N : A.X.NatNbhd x) : A.X.NaturalRep x :=
  NatRepConstruction.restrict A.X N.rep (connectedComponentIn N.U x)
    (A.X.PObj.isOpen_connectedComponentIn N.isOpen_U x)
    (isConnected_connectedComponentIn_iff.2 N.mem_U) (mem_connectedComponentIn N.mem_U)
    ((connectedComponentIn_subset _ _).trans N.U_subset) (mapsTo_Φ_connectedComponentIn N)

theorem connRep_U_subset {x : A.Obj} (N : A.X.NatNbhd x) : (connRep N).U ⊆ N.U :=
  connectedComponentIn_subset _ _

/-- `connRep N` has the properness property if `cl U(x)` is proper. -/
theorem hasPropernessProperty_connRep {x : A.Obj} (N : A.X.NatNbhd x)
    (hN : A.X.IsProperSubset (closure N.U)) : A.X.HasPropernessProperty (connRep N).U :=
  ⟨(connRep N).isOpen_U, hN.of_subset (closure_mono (connRep_U_subset N)) isClosed_closure⟩

/-- Open sets `O ∋ |x|` of `|X|` with `cl(O) ⊆ |U|`, for an open `U ∋ x` (regularity of `|X|`,
Lemma 7.3.5). -/
theorem exists_orbit_nbhd_of_isOpen {U : Set A.Obj} (hUo : IsOpen U) {x : A.Obj} (hx : x ∈ U) :
    ∃ O : Set A.X.OrbitSpace, IsOpen O ∧ A.X.π x ∈ O ∧ closure O ⊆ A.X.π '' U := by
  have hU : A.X.π '' U ∈ 𝓝 (A.X.π x) :=
    (A.X.proposition_7_1_8 _ hUo).mem_nhds (mem_image_of_mem _ hx)
  obtain ⟨C, hC, hCc, hCU⟩ := exists_mem_nhds_isClosed_subset hU
  obtain ⟨O, hOC, hO, hxO⟩ := mem_nhds_iff.1 hC
  exact ⟨O, hO, hxO, (closure_minimal hOC hCc).trans hCU⟩

/-! ### Theorem 13.5.7 -/

/-- **2021 Theorem 13.5.7, p. 635 (2017: Theorem 13.10), with `IsAtomic` summands**, for every
structured tuple `T = (Λ, 𝒰, S, τ)`: if `X` admits sc-smooth partitions of unity, there is a
locally finite family `(Λⱼ)_{j ∈ X}` with structures `[Λⱼ, 𝒰, Sⱼ, τ]` over the data of `T`, each
`Λⱼ` atomic (Definition 13.5.1, on the connected domain of a natural representation at `xⱼ = j`
with the properness property), whose commensurable sum `⊕^c_j Λⱼ` is `Λ`, with the same
sections `sˣᵢ` on every `U(x)` and the same structured class `[Λ, 𝒰, S, τ]`. -/
theorem theorem_13_5_7_isAtomic (hpu : A.X.HasScPartitionsOfUnity) (T : StructuredTuple A) :
    ∃ (Λf : A.Obj → A.W → ℚ≥0) (o : ∀ j, (CommData.ofTuple T).Over (Λf j))
      (hlf : IsLocallyFiniteFamily Λf),
      (∀ j, IsAtomic A (Λf j)) ∧ CommData.lfSum o hlf = T.Λ ∧
      (∀ x (i : (CommData.ofTuple T).I x), ∀ y ∈ T.dec.𝒰.U x,
        (CommData.Over.lfSum o hlf).s x i y = (T.dec.S x).s i y) ∧
      (CommData.Over.lfSum o hlf).toStructured = Quotient.mk _ T := by
  set 𝒰 := T.dec.𝒰 with h𝒰
  have hΛ := T.isScPlusMultisection
  -- the connected domains `Uᶜ(x)` and the shrunken cover `π⁻¹(O_x)`, `cl(O_x) ⊆ |Uᶜ(x)|`
  let R : ∀ x, A.X.NaturalRep x := fun x => connRep (𝒰.nbhd x)
  have hRU : ∀ x, (R x).U ⊆ 𝒰.U x := fun x => connRep_U_subset (𝒰.nbhd x)
  choose O hOo hxO hOcl using fun x => exists_orbit_nbhd_of_isOpen (R x).isOpen_U (R x).mem_U
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
  · -- `Λⱼ` is atomic at `j`, on `Uᶜ(j)`
    refine ⟨(o j).isScPlusMultisection, ?_⟩
    have hprop : A.X.HasPropernessProperty (R j).U :=
      hasPropernessProperty_connRep (𝒰.nbhd j) (𝒰.isProperSubset_closure j)
    set V := (R j).U ∩ A.X.π ⁻¹' O j
    have hVo : IsOpen V := (R j).isOpen_U.inter ((hOo j).preimage A.X.continuous_π)
    have hVcl : closure V ⊆ (R j).U := by
      refine (A.X.lemma_13_1_1 (NatNbhd.ofRep (R j)) hprop.2 inter_subset_left).2 ?_
      exact (closure_mono (image_subset_iff.2 fun y hy => hy.2)).trans (hOcl j)
    let D : AtomicData A :=
      { x := j
        R := R j
        hasPropernessProperty := hprop
        V := V
        isOpen_V := hVo
        mem_V := ⟨(R j).mem_U, hxO j⟩
        mapsTo_V := fun g y hy => ⟨(R j).mapsTo_Φ g hy.1, by
          change A.X.π _ ∈ O j
          rw [show A.X.π ((R j).Φ g y) = A.X.π y from (NatNbhd.ofRep (R j)).π_Φ g hy.1]
          exact hy.2⟩
        closure_V_subset := hVcl
        I := (CommData.ofTuple T).I j
        s := (o j).s j
        isScPlusSectionOn := fun i => ((o j).isScPlusSectionOn j i).mono (R j).isOpen_U (hRU j)
        equivariant := fun g i y hy =>
          ((o j).equivariant j g i y (hRU j hy)).trans (fibAct_of _)
        vanish := fun i y hy hyV => by
          have hy' : y ∈ T.dec.𝒰.U j := hRU j hy
          have h0 : β j y = 0 := by
            by_contra h0
            exact hyV ⟨hy, hsub j (subset_tsupport _ h0)⟩
          have hP : A.P ((T.dec.S j).s i y) = y := (T.dec.S j).P_s i hy'
          have e := SymmetricStructureOn.smulSection_apply (U := T.dec.𝒰.U j) (c := ⇑(β j))
            (s₁ := (T.dec.S j).s i) hy' hP
          rw [h0, zero_smul] at e
          exact e }
    refine ⟨D, fun w φ h ht => ?_, fun w hw => ?_⟩
    · have e1 : Λf j w = Λf j (A.E.μ ⟨(φ, w), h⟩) :=
        ((o j).isScPlusMultisection.1 ⟨(φ, w), h⟩).symm
      rw [e1, (o j).rep j _ (by rw [A.E.P_μ]; exact hRU j ht)]
      rfl
    · refine multisectionSmulFun_of_eq_zero ?_
      by_contra h0
      have hmem := hsub j (subset_tsupport _ h0)
      obtain ⟨z, hz, hzw⟩ : A.X.π (A.P w) ∈ A.X.π '' (R j).U := hOcl j (subset_closure hmem)
      obtain ⟨φ, hφs, hφt⟩ := (A.X.π_eq_π_iff).1 hzw.symm
      exact hw ⟨φ, hφs, hφt ▸ hz⟩
  · -- the structured classes agree
    refine Quotient.sound ⟨hmult, 𝒰, fun x => subset_inter subset_rfl subset_rfl, fun x => rfl,
      fun x x' φ _ => (IndexCorr.map_cast_rfl _).symm⟩

/-- **2021 Theorem 13.5.7, p. 635, for a structurable `Λ`, with `IsAtomic` summands**: `Λ` has
a structured lift `[Λ, 𝒰, S, τ]` which is the commensurable sum of a locally finite family of
atomic `[Λⱼ, 𝒰, Sⱼ, τ]`.  (`|X|` paracompact is the text's hypothesis; it is used only through
the existence of structured lifts and partitions of unity, which are hypotheses here.) -/
theorem theorem_13_5_7_isAtomic_book (_hpara : A.X.HasParacompactOrbitSpace)
    (hpu : A.X.HasScPartitionsOfUnity) {Λ : A.W → ℚ≥0} (hΛ : IsStructurable A Λ) :
    ∃ (T : StructuredTuple A) (Λf : A.Obj → A.W → ℚ≥0)
      (o : ∀ j, (CommData.ofTuple T).Over (Λf j)) (hlf : IsLocallyFiniteFamily Λf),
      T.Λ = Λ ∧ (∀ j, IsAtomic A (Λf j)) ∧ CommData.lfSum o hlf = Λ ∧
      (CommData.Over.lfSum o hlf).toStructured = Quotient.mk _ T := by
  obtain ⟨hΛ', D, ⟨t⟩⟩ := hΛ
  obtain ⟨Λf, o, hlf, hat, hsum, -, hcl⟩ := theorem_13_5_7_isAtomic hpu ⟨⟨Λ, hΛ', D⟩, t⟩
  exact ⟨_, Λf, o, hlf, rfl, hat, hsum, hcl⟩

/-- **2021 Theorem 13.5.7, p. 635, in the form of the text**: for a structurable `Λ` there are
common data `c = (𝒰, I_x, τ)`, a structure `[Λ, 𝒰, S, τ]` over `c` and a locally finite family
`([Λⱼ, 𝒰, Sⱼ, τ])_{j ∈ J}` over `c`, each `Λⱼ` atomic, with `⊕^c_j Λⱼ = Λ` and
`⊕^c_j [Λⱼ, 𝒰, Sⱼ, τ] = [Λ, 𝒰, S, τ]`. -/
theorem theorem_13_5_7_isAtomic_sum (hpara : A.X.HasParacompactOrbitSpace)
    (hpu : A.X.HasScPartitionsOfUnity) {Λ : A.W → ℚ≥0} (hΛ : IsStructurable A Λ) :
    ∃ (c : CommData A) (o : c.Over Λ) (J : Type u) (Λj : J → A.W → ℚ≥0)
      (oj : ∀ j, c.Over (Λj j)) (hlf : IsLocallyFiniteFamily Λj),
      (∀ j, IsAtomic A (Λj j)) ∧ CommData.lfSum oj hlf = Λ ∧
      (CommData.Over.lfSum oj hlf).toStructured = o.toStructured := by
  obtain ⟨T, Λf, o, hlf, hT, hat, hsum, hcl⟩ := theorem_13_5_7_isAtomic_book hpara hpu hΛ
  subst hT
  exact ⟨_, CommData.Over.ofTuple T, A.Obj, Λf, o, hlf, hat, hsum, hcl⟩

end SBLocalization

end Polyfold
