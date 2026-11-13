import Polyfold.Chapter13.P3W5FM_ExtensionData

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.4, pp. 623–625: **Proposition 13.4.2** (2017: Proposition 13.6), the extension of a
structured sc⁺-multisection from an open `V ⊆ X` with `|V| = |X|`.

# Extension of structured sc⁺-multisections from `V` to `X`

## The text, paraphrased

See `P3W5FM_ExtensionData`.  The structure at `x ∉ V` is `I_x = I_{q_x}`,
`sˣᵢ(D_x(q)) = μ((s|O(ψ_x))⁻¹(q), s^{q_x}ᵢ(q))`, and the correspondences are
`τ_{q,x} = τ_{q,q_x} ∘ A`, `τ_{x,q}` (its pseudo-inverse) and `τ_{x,y} = τ_{q_x,q_y} ∘ C`.

## What is formalized (namespace `Polyfold.SBLocalization`)

The three cases (i)–(iii) of the text at once: every `x ∈ X` has a chart `ExtChart L x` (the unit
chart for `x ∈ V`), and `τ_{x,x'}(φ) = τ_{q_x,q_{x'}}(liftMor φ)`, where FN's `liftMor` for the
identity is the text's `C` (`A` when `x ∈ V`, its inverse when `x' ∈ V`).  The push machinery of
`P3W4FN_PushChart`/`_Pushforward` is used with `F = 𝟙 A`.
* `ExtChart.sym` (the structure at `x`, `I_x = I_{q_x}`), `ExtChart.tau`,
  `ExtChart.isDiffeoComponent` (condition (3) of good systems from that of `(U(q))_{q ∈ V}`).
* `extGood`, `extDecoration`, `extTau`, `extTuple` for any family of charts;
  `isScPlusMultisection_extendMult`.
* The data at `q ∈ V` are the given ones: `extSym_smul_of_eq`, `extSym_s_of_eq`, `extTau_of_eq`.
* **`proposition_13_4_2`**: (1) and (2) as printed.  Hypotheses: `V` open, `|V| = |X|`, and a
  structured sc⁺-multisection functor on `W|V` (`StructuredOn A V`); nothing else.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid PushChart

variable {A : SEP.{u}} {V : Set A.Obj} {L : StructuredOn A V}

/-- A symmetric structure with a non-empty index set is a local section structure. -/
theorem hasLocalSectionStructure_of_symmetricOn {Λ : A.W → ℚ≥0} {x : A.Obj}
    {N : A.X.NatNbhd x} (S : SymmetricStructureOn A Λ N) [Nonempty S.I] :
    HasLocalSectionStructure A Λ x := by
  have hc : (Fintype.card S.I : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine hasLocalSectionStructure_of_isLocalRepOn N.isOpen_U N.mem_U
    (isLocalRepOn_of_fintype (K := S.I) S.s (fun _ => (Fintype.card S.I : ℚ≥0)⁻¹)
      (fun _ => inv_pos.2 (pos_iff_ne_zero.2 hc)) S.isScPlusSectionOn ?_ fun w hw => ?_)
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hc]
  · rw [S.rep w hw, Finset.natCast_card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : S.s i (A.P w) = w
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg fun e => h e.symm, mul_zero]

namespace ExtChart

variable {x x' : A.Obj} (c : ExtChart L x) (c' : ExtChart L x')

/-- **The structure at `x`**: `I_x = I_{q_x}`, `sˣᵢ(z) = μ(ψ_u, s^{q_x}ᵢ(u))`, `u = Q⁻¹(z)`,
representing `Λ̄`. -/
def sym : SymmetricStructureOn A (extendMult V L.Λ) c.N :=
  (pushStructure (equivalences_id_sep A) c.isPush isWFunctor_extendMult
    ((L.S c.q).congr fun _ hw => extendMult_eq L.isScPlusMultisectionOn.1 (L.subset c.q hw))).congr
    fun w _ => (pushMult_id isWFunctor_extendMult w).symm

instance : Nonempty c.sym.I := L.nonempty_I c.q

/-- **The correspondence** `τ_{x,x'}(φ) = τ_{q_x,q_{x'}}(C(φ))`, `C = liftMor`. -/
def tau (φ : A.Mor) : IndexCorr c.sym.I c'.sym.I := L.τ c.q c'.q (liftMor c.T c'.T φ)

/-- **Condition (3) of good systems at `(x, x')`**: a component of `𝒰(x, x')` goes by the
(continuous, injective) lift into a component of `𝒰(q_x, q_{x'})`, where `s` and `t` are
injective. -/
theorem isDiffeoComponent {φ : A.Mor} (hφ : φ ∈ A.X.morBetween c.N.U c'.N.U) :
    A.X.IsDiffeoComponent (connectedComponentIn (A.X.morBetween c.N.U c'.N.U) φ) := by
  have hid := equivalences_id_sep A
  have hsubD := morBetween_subset_Dom c.isPush c'.isPush
  have hmaps : MapsTo (liftMor c.T c'.T) (connectedComponentIn (A.X.morBetween c.N.U c'.N.U) φ)
      (connectedComponentIn (A.X.morBetween (L.nbhd c.q).U (L.nbhd c'.q).U)
        (liftMor c.T c'.T φ)) :=
    mapsTo_connectedComponentIn ((continuousOn_liftMor hid).mono hsubD)
      (fun _ hψ => liftMor_mem hid c.isPush c'.isPush hψ) hφ
  have hL := liftMor_mem hid c.isPush c'.isPush hφ
  have hD := L.isGoodIn.isDiffeoComponent c.q c.q.2 c'.q c'.q.2 _ hL
  have hsub : ∀ {ψ}, ψ ∈ connectedComponentIn (A.X.morBetween c.N.U c'.N.U) φ →
      ψ ∈ Dom c.T c'.T := fun hψ => hsubD (connectedComponentIn_subset _ _ hψ)
  refine (isDiffeoComponent_iff_injOn (isOpen_connectedComponentIn_mor A.X
    (isOpen_morBetween c.N.isOpen_U c'.N.isOpen_U) φ)).2
    ⟨fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_, fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_⟩
  · refine injOn_liftMor hid (hsub hψ₁) (hsub hψ₂) (hD.injOn_src (hmaps hψ₁) (hmaps hψ₂) ?_)
    rw [src_liftMor hid (hsub hψ₁), src_liftMor hid (hsub hψ₂), e]
  · refine injOn_liftMor hid (hsub hψ₁) (hsub hψ₂) (hD.injOn_tgt (hmaps hψ₁) (hmaps hψ₂) ?_)
    rw [tgt_liftMor hid (hsub hψ₁), tgt_liftMor hid (hsub hψ₂), e]

end ExtChart

/-! ### The extended good system, decoration and correspondences -/

/-- **The extended good system** `(U(x))_{x ∈ X}` for a family of charts. -/
def extGood (ch : ∀ x, ExtChart L x) : A.X.GoodSystem where
  nbhd x := (ch x).N
  isProperSubset_closure x := (ch x).isProper
  isDiffeoComponent _ _ _ hφ := (ch _).isDiffeoComponent (ch _) hφ

/-- **The extended decoration** `(𝒰, S)` of `Λ̄`. -/
def extDecoration (ch : ∀ x, ExtChart L x) : Decoration A (extendMult V L.Λ) :=
  ⟨extGood ch, fun x => (ch x).sym⟩

/-- **The extended correspondences** `τ_{x,x'}(φ) = τ_{q_x,q_{x'}}(C(φ))` (the text's cases
(i)–(iii) at once). -/
def extTau (ch : ∀ x, ExtChart L x) : (extDecoration ch).Tau where
  τ x x' φ := (ch x).tau (ch x') φ
  isCorrespondence x x' :=
    have hid := equivalences_id_sep A
    have h := (ch x).isPush
    have h' := (ch x').isPush
    { locallyConstant := fun φ hφ =>
        ((continuousOn_liftMor hid).continuousAt ((isOpen_Dom _ _).mem_nhds
          (morBetween_subset_Dom h h' hφ))).eventually
          (L.locallyConstant _ _ _ (liftMor_mem hid h h' hφ))
      finite := (L.finite _ _).subset (by
        rintro _ ⟨φ, hφ, rfl⟩
        exact ⟨_, liftMor_mem hid h h' hφ, rfl⟩)
      biact := fun φ hφ g' g => by
        obtain ⟨k, rfl⟩ := (conjEquiv hid (ch x).T).surjective g
        obtain ⟨k', rfl⟩ := (conjEquiv hid (ch x').T).surjective g'
        change L.τ _ _ (liftMor _ _ (EpGroupoid.biact (ch x).N (ch x').N
          ((ch x').T.conj k') φ ((ch x).T.conj k))) = _
        rw [liftMor_biact hid h h' hφ k' k]
        have hb := L.biact _ _ _ (liftMor_mem hid h h' hφ) k' k
        have e := PullMap.biact_compHom (conjEquiv hid (ch x).T).symm.toMonoidHom
          (conjEquiv hid (ch x').T).symm.toMonoidHom (conjEquiv hid (ch x').T k')
          (L.τ (ch x).q (ch x').q (liftMor (ch x).T (ch x').T φ)) (conjEquiv hid (ch x).T k)
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at e
        exact hb.trans e.symm
      compat := fun φ hφ => IndexCorr.sat_mono (fun i j H ψ hψ => by
          have hψm : ψ ∈ A.X.morBetween (ch x).N.U (ch x').N.U :=
            connectedComponentIn_subset _ _ hψ
          have hmaps := mapsTo_connectedComponentIn
            ((continuousOn_liftMor hid).mono (morBetween_subset_Dom h h'))
            (fun _ hψ => liftMor_mem hid h h' hψ) hφ
          exact pushSec_compat hid h h' (fun u hu => (L.S _).P_s i hu)
            (fun u hu => (L.S _).P_s j hu) hψm (H _ (hmaps hψ)))
        (L.compat _ _ _ (liftMor_mem hid h h' hφ)) }
  diag x g z hz := by
    have hid := equivalences_id_sep A
    have h := (ch x).isPush
    obtain ⟨k, rfl⟩ := (conjEquiv hid (ch x).T).surjective g
    change L.τ _ _ (liftMor _ _ ((ch x).N.rep.Γ ((ch x).T.conj k) z)) = _
    rw [liftMor_Γ hid h k hz, L.diag _ k _ (h.Qinv_mem hz)]
    have e := PullMap.ofPerm_compHom (α := (L.S (ch x).q).I)
      (conjEquiv hid (ch x).T).symm.toMonoidHom (conjEquiv hid (ch x).T k)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at e
    exact e.symm
  swap x x' φ hφ := by
    have hid := equivalences_id_sep A
    have hD := morBetween_subset_Dom (ch x').isPush (ch x).isPush hφ
    change L.τ _ _ (liftMor _ _ φ) = (L.τ _ _ (liftMor _ _ (A.X.inv φ))).swap
    rw [liftMor_inv hid _ _ hD]
    exact L.swap _ _ _ (liftMor_mem hid (ch x').isPush (ch x).isPush hφ)

/-- **`Λ̄` is an sc⁺-multisection functor** (Proposition 13.4.2 (1)): at every `x` the pushed
structure is a local section structure. -/
theorem isScPlusMultisection_extendMult (ch : ∀ x, ExtChart L x) :
    IsScPlusMultisection A (extendMult V L.Λ) :=
  ⟨isWFunctor_extendMult, fun x => hasLocalSectionStructure_of_symmetricOn (ch x).sym⟩

/-- **The extended structured tuple** `(Λ̄, 𝒰, S, τ)`. -/
def extTuple (ch : ∀ x, ExtChart L x) : StructuredTuple A :=
  ⟨⟨extendMult V L.Λ, isScPlusMultisection_extendMult ch, extDecoration ch⟩, extTau ch⟩

/-! ### On `V` the data are the given ones -/

section OnV

variable (E : ExtSetup L) {q q' : A.Obj} (hq : q ∈ V) (hq' : q' ∈ V)

theorem extSym_smul_of_eq {c : ExtChart L q} (hc : c = unitExt E hq)
    (h : c.sym.I = (L.S ⟨q, hq⟩).I) (g : A.X.Isotropy q) (i : c.sym.I) :
    cast h (g • i) = g • cast h i := by
  subst hc
  rw [show cast h (g • i) = g • i from cast_eq h _, show cast h i = i from cast_eq h i]
  change (conjEquiv (equivalences_id_sep A) (unitChart (L.nbhd q))).symm g •
    (show (L.S ⟨q, hq⟩).I from i) = g • (show (L.S ⟨q, hq⟩).I from i)
  rw [show (conjEquiv (equivalences_id_sep A) (unitChart (L.nbhd q))).symm g = g from
    (MulEquiv.symm_apply_eq _).2 (unitChart_conj _ g).symm]

theorem extSym_s_of_eq {c : ExtChart L q} (hc : c = unitExt E hq)
    (h : c.sym.I = (L.S ⟨q, hq⟩).I) (i : c.sym.I) {z : A.Obj} (hz : z ∈ (L.nbhd q).U) :
    c.sym.s i z = (L.S ⟨q, hq⟩).s (cast h i) z := by
  subst hc
  exact pushSec_unit (L.nbhd q) (fun u hu => (L.S _).P_s _ hu) hz

theorem extTau_of_eq {c : ExtChart L q} {c' : ExtChart L q'} (hc : c = unitExt E hq)
    (hc' : c' = unitExt E hq') (h : c.sym.I = (L.S ⟨q, hq⟩).I)
    (h' : c'.sym.I = (L.S ⟨q', hq'⟩).I) {φ : A.Mor}
    (hφ : φ ∈ A.X.morBetween (L.nbhd q).U (L.nbhd q').U) :
    c.tau c' φ = (L.τ ⟨q, hq⟩ ⟨q', hq'⟩ φ).map (_root_.Equiv.cast h.symm)
      (_root_.Equiv.cast h'.symm) := by
  subst hc hc'
  change L.τ _ _ (liftMor (unitChart (L.nbhd q)) (unitChart (L.nbhd q')) φ) = _
  rw [liftMor_unit _ _ hφ]
  exact (IndexCorr.map_cast_rfl _).symm

end OnV

/-! ### Proposition 13.4.2 -/

/-- **2021 Proposition 13.4.2, p. 623 (2017: Proposition 13.6)**: let `V ⊆ X` be open with
`|V| = |X|` and `Λ : W|V → ℚ⁺` a structured sc⁺-multisection functor on the ep-groupoid `V`
(`StructuredOn A V`).
(1) `Λ̄ = extendMult V Λ` is an sc⁺-multisection functor on `W` extending `Λ`, and it is the only
functor on `W` extending `Λ` (canonical).
(2) For open `O(x) ∋ x` there is a structured `(Λ̄, 𝒰, S, τ)` whose data on `V` are the given
ones (`U(q)`, `I_q` with its `G_q`-action, the sections on `U(q)`, `τ_{q,q'}` on `𝒰(q, q')`) and
with `U(x) ⊆ O(x)` for `x ∉ V`.  As printed, no added hypothesis. -/
theorem proposition_13_4_2 (hV : IsOpen V) (hπV : A.X.π '' V = univ) (L : StructuredOn A V) :
    (IsScPlusMultisection A (extendMult V L.Λ) ∧
      (∀ w, A.P w ∈ V → extendMult V L.Λ w = L.Λ w) ∧
      ∀ Λ' : A.W → ℚ≥0, IsWFunctor A Λ' → (∀ w, A.P w ∈ V → Λ' w = L.Λ w) →
        Λ' = extendMult V L.Λ) ∧
    ∀ (O : A.Obj → Set A.Obj), (∀ x, IsOpen (O x)) → (∀ x, x ∈ O x) →
      ∃ T : StructuredTuple A, T.Λ = extendMult V L.Λ ∧
        (∀ q ∈ V, T.dec.𝒰.nbhd q = L.nbhd q) ∧ (∀ x ∉ V, T.dec.𝒰.U x ⊆ O x) ∧
        ∃ hI : ∀ q (hq : q ∈ V), (T.dec.S q).I = (L.S ⟨q, hq⟩).I,
          (∀ q (hq : q ∈ V) (g : A.X.Isotropy q) (i : (T.dec.S q).I),
            cast (hI q hq) (g • i) = g • cast (hI q hq) i) ∧
          (∀ q (hq : q ∈ V) (i : (T.dec.S q).I), ∀ z ∈ (L.nbhd q).U,
            (T.dec.S q).s i z = (L.S ⟨q, hq⟩).s (cast (hI q hq) i) z) ∧
          ∀ q (hq : q ∈ V) q' (hq' : q' ∈ V),
            ∀ φ ∈ A.X.morBetween (L.nbhd q).U (L.nbhd q').U,
              T.tau.τ q q' φ = (L.τ ⟨q, hq⟩ ⟨q', hq'⟩ φ).map
                (_root_.Equiv.cast (hI q hq).symm) (_root_.Equiv.cast (hI q' hq').symm) := by
  have E₀ : ExtSetup L := ⟨hV, hπV, fun _ => univ, fun _ => isOpen_univ, fun _ => mem_univ _⟩
  refine ⟨⟨isScPlusMultisection_extendMult (extChart E₀),
    fun w hw => extendMult_eq L.isScPlusMultisectionOn.1 hw,
    fun Λ' hΛ' h => eq_extendMult hπV L.isScPlusMultisectionOn.1 hΛ' h⟩, fun O hO hxO => ?_⟩
  let E : ExtSetup L := ⟨hV, hπV, O, hO, hxO⟩
  have hI : ∀ q (hq : q ∈ V), ((extTuple (extChart E)).dec.S q).I = (L.S ⟨q, hq⟩).I :=
    fun q hq => by
      change (extChart E q).sym.I = _
      rw [extChart_of_mem E hq]
      rfl
  refine ⟨extTuple (extChart E), rfl, fun q hq => ?_, fun x hx => extChart_subset E hx, hI,
    fun q hq g i => extSym_smul_of_eq E hq (extChart_of_mem E hq) (hI q hq) g i,
    fun q hq i z hz => extSym_s_of_eq E hq (extChart_of_mem E hq) (hI q hq) i hz,
    fun q hq q' hq' φ hφ => extTau_of_eq E hq hq' (extChart_of_mem E hq) (extChart_of_mem E hq')
      (hI q hq) (hI q' hq') hφ⟩
  change (extChart E q).N = _
  rw [extChart_of_mem E hq]
  rfl

/-- **Proposition 13.4.2, structurability form**: the extension of a structured sc⁺-multisection
functor on `W|V` is structurable on `W`. -/
theorem proposition_13_4_2_structurable (hV : IsOpen V) (hπV : A.X.π '' V = univ)
    (L : StructuredOn A V) : IsStructurable A (extendMult V L.Λ) := by
  obtain ⟨T, hT, -⟩ := (proposition_13_4_2 hV hπV L).2 (fun _ => univ) (fun _ => isOpen_univ)
    fun _ => mem_univ _
  exact hT ▸ ⟨T.isScPlusMultisection, T.dec, ⟨T.tau⟩⟩

end SBLocalization

end Polyfold
