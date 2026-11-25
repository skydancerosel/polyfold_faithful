import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V13_59

set_option maxSynthPendingDepth 3

/-! Round trip for V13_59 (2021 Proposition 13.4.2, pp. 623–625; 2017: Proposition 13.6: the
extension of a structured sc⁺-multisection from `V` with `|V| = |X|`).

The item lists eight definitions (vocabulary: `IsWFunctorOn`, `IsScPlusMultisectionOn`,
`StructuredOn`, `StructuredTuple.toStructuredOn`, `extendMult`, `unitChart`, `ExtChart`,
`extTuple`) and seven theorems; `A` is the conjunction of their types at universe `0` (`B` is on
`SEP.{0}`).

* `A_to_B`: `|V| = |X|` is `π '' V = univ` (`π_eq_π_iff`); (1) is `proposition_13_4_2` (1)
  verbatim; for (2), `B`'s `O` (given for `x ∉ V`) is extended by `univ` on `V`, and `A`'s
  equalities of index types `hI` give the bijections `e q := Equiv.cast (hI q)`, under which the
  correspondences agree by `map_cast_symm`.  `B`'s extra hypothesis `IsWFunctorOn A V L.Λ` is not
  used (it is part of `StructuredOn`).
* `B_to_A`: (1): `B`'s `Λ̄` is `extendMult V L.Λ` by `B`'s uniqueness (applied to `extendMult`,
  a functor extending `Λ`).  (2): `B` identifies `I_q` with `I^L_q` by bijections `e q`, `A` asks
  an **equality** of the index types.  `B`'s tuple `T` is relabelled: `I'_x := I^L_x` for
  `x ∈ V`, `I_x` otherwise, the sections `s'_κ = s_{e(κ)}` (`SymmetricStructureOn.reindex`),
  `τ' = τ.map e⁻¹ e'⁻¹`, with the transported `G_x`-action; the conditions of Definitions
  13.3.4/13.3.6 go over by `sat_map`, `map_biact`, `map_ofPerm`, `map_swap`.  The helper
  conjuncts (`isWFunctor_extendMult`, `extendMult_eq`, `eq_extendMult`, `isPushNbhd_unit`,
  `isScPlusMultisection_extendMult`, the structurability corollary) are re-proved outright by
  copying the project's proofs (suffix `'`); `eq_extendMult` and
  `isScPlusMultisection_extendMult` are stated for an arbitrary `Λ` / an arbitrary family of charts
  and do not follow from `B`.

**Harness note.**  `A`'s statement mentions no definition with banned proof fields, but the copy
of `isScPlusMultisection_extendMult` uses `ExtChart.sym`, whose proof fields use the banned
`isWFunctor_extendMult` and `extendMult_eq`; so `B_to_A` is checked with `#rt_check_soft`.
-/

namespace RoundTrip.V13_59
open Polyfold Polyfold.SBLocalization Set
open scoped Classical

/-- The project's statement at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.isWFunctor_extendMult.{0}) ∧
  (type_of% @Polyfold.SBLocalization.extendMult_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.eq_extendMult.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isPushNbhd_unit.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isScPlusMultisection_extendMult.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_13_4_2.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_13_4_2_structurable.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.isWFunctor_extendMult.{0},
    @Polyfold.SBLocalization.extendMult_eq.{0},
    @Polyfold.SBLocalization.eq_extendMult.{0},
    @Polyfold.SBLocalization.isPushNbhd_unit.{0},
    @Polyfold.SBLocalization.isScPlusMultisection_extendMult.{0},
    @Polyfold.SBLocalization.proposition_13_4_2.{0},
    @Polyfold.SBLocalization.proposition_13_4_2_structurable.{0}⟩

/-! ### `A ⇒ B` -/

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, -, -, hP, -⟩
  intro A V hV hiso L _
  have hπV : A.X.π '' V = univ := eq_univ_of_forall fun o => by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep o
    obtain ⟨q, hq, h⟩ := hiso x
    exact ⟨q, hq, (A.X.π_eq_π_iff.2 h).symm⟩
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP hV hπV L
  refine ⟨extendMult V L.Λ, h1, h2, h3, fun O hO => ?_⟩
  let O' : A.Obj → Set A.Obj := fun x => if x ∈ V then univ else O x
  obtain ⟨T, hT, hnb, hU, hI, hg, hs, hτ⟩ := h4 O'
    (fun x => by
      by_cases hx : x ∈ V
      · simp only [O', if_pos hx]; exact isOpen_univ
      · simp only [O', if_neg hx]; exact (hO x hx).1)
    (fun x => by
      by_cases hx : x ∈ V
      · simp only [O', if_pos hx]; exact mem_univ _
      · simp only [O', if_neg hx]; exact (hO x hx).2)
  refine ⟨T, hT, fun x hx => by simpa only [O', if_neg hx] using hU x hx,
    fun q => hnb q q.2, fun q => Equiv.cast (hI q q.2), fun q g i => hg q q.2 g i,
    fun q i y hy => hs q q.2 i y hy, fun q q' φ hφ => ?_⟩
  rw [hτ q q.2 q' q'.2 φ hφ]
  exact Polyfold.SBLocalization.IndexCorr.map_cast_symm (hI q q.2).symm (hI q' q'.2).symm _

/-! ### `B ⇒ A`: relabelling a structured tuple on `V` -/

noncomputable section Reindex

variable {A : SEP.{0}} {V : Set A.Obj} (L : StructuredOn A V) (T : StructuredTuple A)
  (e : ∀ q : V, (T.dec.S q).I ≃ (L.S q).I)

/-- The new index sets: `I^L_x` for `x ∈ V`, `I_x` otherwise. -/
def J (x : A.Obj) : Type := if h : x ∈ V then (L.S ⟨x, h⟩).I else (T.dec.S x).I

theorem J_pos {x : A.Obj} (h : x ∈ V) : J L T x = (L.S ⟨x, h⟩).I := dif_pos h

theorem J_neg {x : A.Obj} (h : x ∉ V) : J L T x = (T.dec.S x).I := dif_neg h

/-- The bijection `J x ≃ I_x`. -/
def eJ (x : A.Obj) : J L T x ≃ (T.dec.S x).I :=
  if h : x ∈ V then (Equiv.cast (J_pos L T h)).trans (e ⟨x, h⟩).symm
  else Equiv.cast (J_neg L T h)

theorem eJ_pos {x : A.Obj} (h : x ∈ V) :
    eJ L T e x = (Equiv.cast (J_pos L T h)).trans (e ⟨x, h⟩).symm := dif_pos h

/-- The relabelled symmetric structure at `x` (transported finiteness and `G_x`-action). -/
def symR (x : A.Obj) : SymmetricStructureOn A T.Λ (T.dec.𝒰.nbhd x) :=
  letI : Fintype (J L T x) := Fintype.ofEquiv _ (eJ L T e x).symm
  letI : MulAction (A.X.Isotropy x) (J L T x) := (eJ L T e x).mulAction _
  (T.dec.S x).reindex (J L T x) (eJ L T e x) fun _ _ => (eJ L T e x).apply_symm_apply _

/-- The relabelled decoration. -/
def decR : Decoration A T.Λ := ⟨T.dec.𝒰, symR L T e⟩

/-- `eJ` with the index type of the relabelled structure. -/
def eR (x : A.Obj) : ((decR L T e).S x).I ≃ (T.dec.S x).I := eJ L T e x

theorem eR_pos {x : A.Obj} (h : x ∈ V) :
    eR L T e x = (Equiv.cast (J_pos L T h)).trans (e ⟨x, h⟩).symm := dif_pos h

theorem eR_symm_smul (x : A.Obj) (g : A.X.Isotropy x) (a : (T.dec.S x).I) :
    (eR L T e x).symm (g • a) = g • (eR L T e x).symm a := by
  show _ = (eR L T e x).symm (g • (eR L T e x) ((eR L T e x).symm a))
  rw [Equiv.apply_symm_apply]

theorem eR_smul (x : A.Obj) (g : A.X.Isotropy x) (κ : ((decR L T e).S x).I) :
    eR L T e x (g • κ) = g • eR L T e x κ :=
  (eR L T e x).apply_symm_apply _

/-- The relabelled correspondences `τ' = τ.map e⁻¹ e'⁻¹`. -/
def tauR : (decR L T e).Tau where
  τ x x' φ := (T.tau.τ x x' φ).map (eR L T e x).symm (eR L T e x').symm
  isCorrespondence x x' :=
    { locallyConstant := fun φ hφ =>
        ((T.tau.isCorrespondence x x').locallyConstant φ hφ).mono fun ψ hψ => by
          rw [hψ]
      finite := (((T.tau.isCorrespondence x x').finite).image
          (Polyfold.SBLocalization.IndexCorr.map (eR L T e x).symm (eR L T e x').symm)).subset
          (by
            rintro _ ⟨φ, hφ, rfl⟩
            exact ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩)
      biact := fun φ hφ g' g => by
        change (T.tau.τ x x' (T.dec.𝒰.biact x x' g' φ g)).map _ _ = _
        rw [(T.tau.isCorrespondence x x').biact φ hφ g' g]
        exact Polyfold.SBLocalization.IndexCorr.map_biact _ _ (eR_symm_smul L T e x)
          (eR_symm_smul L T e x') g' _ g
      compat := fun φ hφ =>
        Polyfold.SBLocalization.IndexCorr.sat_map _ _ (fun i j H ψ hψ => by
          show (T.dec.S x').s ((eR L T e x') ((eR L T e x').symm j)) (A.X.tgt ψ) =
            fibAct ψ ((T.dec.S x).s ((eR L T e x) ((eR L T e x).symm i)) (A.X.src ψ))
          rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          exact H ψ hψ) ((T.tau.isCorrespondence x x').compat φ hφ) }
  diag x g y hy := by
    change (T.tau.τ x x ((T.dec.𝒰.nbhd x).rep.Γ g y)).map _ _ = _
    rw [T.tau.diag x g y hy]
    exact Polyfold.SBLocalization.IndexCorr.map_ofPerm _ (eR_symm_smul L T e x) g
  swap x x' φ hφ := by
    rw [T.tau.swap x x' φ hφ]
    exact (Polyfold.SBLocalization.IndexCorr.map_swap _ _ _).symm

/-- The relabelled structured tuple. -/
def TR : StructuredTuple A := ⟨⟨T.Λ, T.isScPlusMultisection, decR L T e⟩, tauR L T e⟩

theorem cast_eq_e {q : A.Obj} (hq : q ∈ V) (h : ((TR L T e).dec.S q).I = (L.S ⟨q, hq⟩).I)
    (i : ((TR L T e).dec.S q).I) : cast h i = e ⟨q, hq⟩ (eR L T e q i) := by
  rw [eR_pos L T e hq]
  exact ((e ⟨q, hq⟩).apply_symm_apply (cast (J_pos L T hq) i)).symm

theorem eR_symm_eq {q : A.Obj} (hq : q ∈ V) (h : ((TR L T e).dec.S q).I = (L.S ⟨q, hq⟩).I) :
    (eR L T e q).symm = (e ⟨q, hq⟩).trans (Equiv.cast h.symm) := by
  rw [eR_pos L T e hq]
  rfl

end Reindex

/-! ### `B ⇒ A`: the helper conjuncts, re-proved (the project's proofs) -/

theorem isWFunctor_extendMult' : type_of% @Polyfold.SBLocalization.isWFunctor_extendMult.{0} := by
  intro A V Λ q
  exact extendMult_congr (A.E.toEpGroupoid.π_src_eq_π_tgt q).symm

theorem extendMult_eq' : type_of% @Polyfold.SBLocalization.extendMult_eq.{0} := by
  intro A V Λ hΛ w hw
  have h : ∃ w₀, A.P w₀ ∈ V ∧ A.E.toEpGroupoid.π w₀ = A.E.toEpGroupoid.π w := ⟨w, hw, rfl⟩
  rw [extendMult, dif_pos h]
  exact hΛ.eq_of_π_eq h.choose_spec.1 hw h.choose_spec.2

theorem eq_extendMult' : type_of% @Polyfold.SBLocalization.eq_extendMult.{0} := by
  intro A V Λ hπV hΛ Λ' hΛ' h
  funext w
  obtain ⟨w₀, hw₀, hπ⟩ := exists_mem_of_π_image hπV w
  rw [← hΛ'.eq_of_π_eq hπ, h w₀ hw₀, ← extendMult_eq' hΛ hw₀, extendMult_congr hπ]

theorem isPushNbhd_unit' : type_of% @Polyfold.SBLocalization.isPushNbhd_unit.{0} := by
  intro A x N
  exact
    { subset_W' := subset_rfl
      Qinv_mem := fun hz => hz
      Φ_mem_W := fun z hz g => N.Φ_mem g hz
      Γ_eq := fun g z hz => by
        rw [unitChart_conj]
        change N.rep.Γ g z =
          A.X.comp (A.X.comp (A.X.unit (N.rep.Φ g z)) (N.rep.Γ g z)) (A.X.inv (A.X.unit z))
        rw [A.X.inv_unit, A.X.unit_comp_of_eq (N.tgt_Γ g hz), A.X.comp_unit_of_eq (N.src_Γ g hz)] }

theorem isScPlusMultisection_extendMult' :
    type_of% @Polyfold.SBLocalization.isScPlusMultisection_extendMult.{0} := by
  intro A V L ch
  exact ⟨isWFunctor_extendMult', fun x => hasLocalSectionStructure_of_symmetricOn (ch x).sym⟩

/-! ### `B ⇒ A` -/

theorem B_to_A : B → A := by
  intro hB
  have main : type_of% @Polyfold.SBLocalization.proposition_13_4_2.{0} := by
    intro A V hV hπV L
    have hiso : ∀ x : A.Obj, ∃ q ∈ V, A.X.Isomorphic x q := fun x => by
      obtain ⟨q, hq, h⟩ : A.X.π x ∈ A.X.π '' V := hπV ▸ mem_univ _
      exact ⟨q, hq, A.X.π_eq_π_iff.1 h.symm⟩
    obtain ⟨Λbar, hsc, -, huniq, h2⟩ := hB A V hV hiso L L.isScPlusMultisectionOn.1
    have hΛ : extendMult V L.Λ = Λbar := huniq _ isWFunctor_extendMult'
      fun w hw => extendMult_eq' L.isScPlusMultisectionOn.1 hw
    refine ⟨⟨hΛ ▸ hsc, fun w hw => extendMult_eq' L.isScPlusMultisectionOn.1 hw,
      fun Λ' hΛ' h => (huniq Λ' hΛ' h).trans hΛ.symm⟩, fun O hO hxO => ?_⟩
    obtain ⟨T, hTΛ, hTU, hnb, e, he, hs, hτ⟩ := h2 O fun x _ => ⟨hO x, hxO x⟩
    refine ⟨TR L T e, hTΛ.trans hΛ.symm, fun q hq => hnb ⟨q, hq⟩, hTU,
      fun q hq => J_pos L T hq, fun q hq g i => ?_, fun q hq i z hz => ?_,
      fun q hq q' hq' φ hφ => ?_⟩
    · exact (cast_eq_e L T e hq _ _).trans (((congrArg (e ⟨q, hq⟩) (eR_smul L T e q g i)).trans
        (he ⟨q, hq⟩ g _)).trans (congrArg (g • ·) (cast_eq_e L T e hq _ i).symm))
    · exact (hs ⟨q, hq⟩ (eR L T e q i) z hz).trans
        (congrArg (fun k => (L.S ⟨q, hq⟩).s k z) (cast_eq_e L T e hq _ i).symm)
    · change (T.tau.τ q q' φ).map (eR L T e q).symm (eR L T e q').symm = _
      rw [← hτ ⟨q, hq⟩ ⟨q', hq'⟩ φ hφ, Polyfold.SBLocalization.IndexCorr.map_map,
        eR_symm_eq L T e hq (J_pos L T hq), eR_symm_eq L T e hq' (J_pos L T hq')]
      rfl
  refine ⟨isWFunctor_extendMult', extendMult_eq', eq_extendMult', isPushNbhd_unit',
    isScPlusMultisection_extendMult', main, ?_⟩
  intro A V hV hπV L
  obtain ⟨T, hT, -⟩ := (main hV hπV L).2 (fun _ => univ) (fun _ => isOpen_univ)
    fun _ => mem_univ _
  exact hT ▸ ⟨T.isScPlusMultisection, T.dec, ⟨T.tau⟩⟩

#rt_check RoundTrip.V13_59.A_to_B [Polyfold.SBLocalization.isWFunctor_extendMult,
  Polyfold.SBLocalization.extendMult_eq, Polyfold.SBLocalization.eq_extendMult,
  Polyfold.SBLocalization.isPushNbhd_unit, Polyfold.SBLocalization.isScPlusMultisection_extendMult,
  Polyfold.SBLocalization.proposition_13_4_2,
  Polyfold.SBLocalization.proposition_13_4_2_structurable]
/--
error: rt_check FAIL: RoundTrip.V13_59.B_to_A uses [Polyfold.SBLocalization.isWFunctor_extendMult,
 Polyfold.SBLocalization.extendMult_eq]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V13_59.B_to_A [Polyfold.SBLocalization.isWFunctor_extendMult,
  Polyfold.SBLocalization.extendMult_eq, Polyfold.SBLocalization.eq_extendMult,
  Polyfold.SBLocalization.isPushNbhd_unit, Polyfold.SBLocalization.isScPlusMultisection_extendMult,
  Polyfold.SBLocalization.proposition_13_4_2,
  Polyfold.SBLocalization.proposition_13_4_2_structurable]
#rt_check_soft RoundTrip.V13_59.B_to_A [Polyfold.SBLocalization.isWFunctor_extendMult,
  Polyfold.SBLocalization.extendMult_eq, Polyfold.SBLocalization.eq_extendMult,
  Polyfold.SBLocalization.isPushNbhd_unit, Polyfold.SBLocalization.isScPlusMultisection_extendMult,
  Polyfold.SBLocalization.proposition_13_4_2,
  Polyfold.SBLocalization.proposition_13_4_2_structurable]
#rt_overlap RoundTrip.V13_59.B_to_A [Polyfold.SBLocalization.isWFunctor_extendMult,
  Polyfold.SBLocalization.extendMult_eq, Polyfold.SBLocalization.eq_extendMult,
  Polyfold.SBLocalization.isPushNbhd_unit, Polyfold.SBLocalization.isScPlusMultisection_extendMult,
  Polyfold.SBLocalization.proposition_13_4_2,
  Polyfold.SBLocalization.proposition_13_4_2_structurable]

end RoundTrip.V13_59
