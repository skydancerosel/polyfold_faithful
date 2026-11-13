import Polyfold.Chapter13.P3W4FN_Pushforward
import Polyfold.Chapter13.P3E_GoodSystemRelative

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.4, pp. 623–625: the data of **Proposition 13.4.2** (2017: Proposition 13.6), the extension
of a structured sc⁺-multisection from an open `V ⊆ X` with `|V| = |X|`.

# Structured multisections on `W|V` and their extension functor

## The text, paraphrased

(Proposition 13.4.2) `V ⊆ X` is open with `|V| = |X|`, viewed as an ep-groupoid, and
`Λ : W|V → ℚ⁺` is a structured sc⁺-multisection functor.  (1) `Λ̄(w) = Λ(w₀)` for `w₀ ∈ W|V` and
`φ : P(w₀) → P(w)` with `μ(φ, w₀) = w` is a well-defined sc⁺-multisection functor on `W`.
(2) The structure is extended: every `x ∉ V` is reached by `ψ_x : q_x → x`, `q_x ∈ V`; the
sections at `x` are moved by `D_x = t ∘ (s|U(ψ_x))⁻¹` and `μ`, and the correspondences by the
maps `A` and `C` (`φ ↦ (t|O(ψ_y))⁻¹(t φ)⁻¹ ∘ φ ∘ (t|O(ψ_x))⁻¹(s φ)`).

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IsWFunctorOn A V Λ`, `IsScPlusMultisectionOn A V Λ`: Definition 13.2.1 for the full
  subcategory `W|V` (natural representations of `V` are those of `X` with domain inside `V`).
* `StructuredOn A V`: Definitions 13.3.4, 13.3.6 for the ep-groupoid `V`: a good system
  `(U(q))_{q ∈ V}` for `V` (E's `IsGoodIn`, Theorem 13.1.7 as printed), symmetric structures
  `S_q`, `q ∈ V`, and correspondences `τ_{q,q'}`, `q, q' ∈ V`, with (1)–(3) of 13.3.4 and
  (1)–(2) of 13.3.6.
* `extendMult V Λ` (the text's `Λ̄`): `isWFunctor_extendMult`, `extendMult_eq` (it extends `Λ`),
  `eq_extendMult` (uniqueness: every functor on `W` extending `Λ` is `Λ̄`; this is "canonical").
* The unit chart `unitChart N` (`Q = id`, `ψ = 1`) of the identity strong bundle equivalence
  `𝟙 A`, `isPushNbhd_unit`, `liftMor_unit`, `pushSec_unit`.
* `ExtChart L x`: a point `q_x ∈ V`, the chart `Q = t ∘ (s|U(ψ_x))⁻¹` of `𝟙 A` along
  `ψ_x : q_x → x` (Chapter 10's `TransportChart`), and an adapted `U(x)` (FN's `IsPushNbhd`)
  with the properness property; `unitExt` (for `x ∈ V`), `exists_extChart` (inside any open
  `O ∋ x`), `ExtSetup`, `extChart` (the choice, `extChart_of_mem`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### Multisection functors on `W|V` -/

/-- **A functor on `W|V`**: `Λ(μ(φ, w)) = Λ(w)` for the morphisms `φ` of `V` (source and target
in `V`). -/
def IsWFunctorOn (A : SEP.{u}) (V : Set A.Obj) (Λ : A.W → ℚ≥0) : Prop :=
  ∀ q : pullbackSpace A.P A.X.src, A.P (q : A.Mor × A.W).2 ∈ V → A.P (A.E.μ q) ∈ V →
    Λ (A.E.μ q) = Λ (q : A.Mor × A.W).2

/-- **2021 Definition 13.2.1 for the ep-groupoid `V`**: a functor on `W|V` with a local section
structure around every `q ∈ V` on the domain of a natural representation inside `V`. -/
def IsScPlusMultisectionOn (A : SEP.{u}) (V : Set A.Obj) (Λ : A.W → ℚ≥0) : Prop :=
  IsWFunctorOn A V Λ ∧ ∀ q ∈ V, ∃ R : A.X.NaturalRep q, R.U ⊆ V ∧
    ∃ (k : ℕ) (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0), IsLocalRepOn A Λ R.U s σ

theorem IsWFunctorOn.eq_of_π_eq {V : Set A.Obj} {Λ : A.W → ℚ≥0} (h : IsWFunctorOn A V Λ)
    {a b : A.W} (ha : A.P a ∈ V) (hb : A.P b ∈ V)
    (hab : A.E.toEpGroupoid.π a = A.E.toEpGroupoid.π b) : Λ a = Λ b := by
  obtain ⟨q, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hab
  have hs' : (q : A.Mor × A.W).2 = a := hs
  have ht' : A.E.μ q = b := ht
  rw [← hs', ← ht', h q (hs' ▸ ha) (ht' ▸ hb)]

/-- **2021 Definitions 13.3.4, 13.3.6 for the ep-groupoid `V`**: a structured sc⁺-multisection
functor `Λ : W|V → ℚ⁺`: a good system `(U(q))_{q ∈ V}` for `V`, symmetric sc⁺-section structures
`S_q` on `U(q)` representing `Λ`, and correspondences `τ_{q,q'} : 𝒰(q, q') → J(q, q')` with
(13.3.4) (1) locally constant, finitely many values, (2) bi-equivariant, (3) compatible with the
sections, and (13.3.6) (1) `τ_{q,q}(Γ(g, y)) = [I_q ← I_q → I_q]_{(Id, g)}`,
(2) `τ_{q',q}(φ) = τ_{q,q'}(φ⁻¹)♯`. -/
structure StructuredOn (A : SEP.{u}) (V : Set A.Obj) where
  /-- The functor `Λ` (only its values over `V` matter). -/
  Λ : A.W → ℚ≥0
  isScPlusMultisectionOn : IsScPlusMultisectionOn A V Λ
  /-- The neighbourhoods `U(q)` with their natural actions (only `q ∈ V` matter). -/
  nbhd : ∀ x : A.Obj, A.X.NatNbhd x
  isGoodIn : A.X.IsGoodIn nbhd V
  /-- The symmetric structures `S_q`, `q ∈ V`. -/
  S : ∀ q : V, SymmetricStructureOn A Λ (nbhd q)
  /-- The correspondences `τ_{q,q'}`. -/
  τ : ∀ q q' : V, A.Mor → IndexCorr (S q).I (S q').I
  locallyConstant : ∀ q q' : V, ∀ φ ∈ A.X.morBetween (nbhd q).U (nbhd q').U,
    ∀ᶠ ψ in 𝓝 φ, τ q q' ψ = τ q q' φ
  finite : ∀ q q' : V, (τ q q' '' A.X.morBetween (nbhd q).U (nbhd q').U).Finite
  biact : ∀ q q' : V, ∀ φ ∈ A.X.morBetween (nbhd q).U (nbhd q').U,
    ∀ (g' : A.X.Isotropy (q' : A.Obj)) (g : A.X.Isotropy (q : A.Obj)),
      τ q q' (EpGroupoid.biact (nbhd q) (nbhd q') g' φ g) = IndexCorr.biact g' (τ q q' φ) g
  compat : ∀ q q' : V, ∀ φ ∈ A.X.morBetween (nbhd q).U (nbhd q').U, (τ q q' φ).Sat fun i j =>
    ∀ ψ ∈ connectedComponentIn (A.X.morBetween (nbhd q).U (nbhd q').U) φ,
      (S q').s j (A.X.tgt ψ) = fibAct ψ ((S q).s i (A.X.src ψ))
  diag : ∀ (q : V) (g : A.X.Isotropy (q : A.Obj)), ∀ y ∈ (nbhd q).U,
    τ q q ((nbhd q).rep.Γ g y) = IndexCorr.ofPerm (α := (S q).I) g
  swap : ∀ q q' : V, ∀ φ ∈ A.X.morBetween (nbhd q').U (nbhd q).U,
    τ q' q φ = (τ q q' (A.X.inv φ)).swap

namespace StructuredOn

variable {V : Set A.Obj} (L : StructuredOn A V)

theorem subset (q : V) : (L.nbhd q).U ⊆ V := L.isGoodIn.subset q q.2

/-- The index sets of the structures are not empty (`Λ` has a local representation at `q`). -/
theorem nonempty_I (q : V) : Nonempty (L.S q).I := by
  obtain ⟨R, -, k, s, σ, hpos, hs, hsum, hrep⟩ := L.isScPlusMultisectionOn.2 q q.2
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hsum
    · exact h
  set i₀ : Fin k := ⟨0, hk⟩
  set w := s i₀ q
  have hPw : A.P w = q := (hs i₀).1 q R.mem_U
  have hpos' : 0 < L.Λ w := by
    rw [hrep w (by rw [hPw]; exact R.mem_U)]
    refine lt_of_lt_of_le (hpos i₀) (le_trans (le_of_eq ?_)
      (Finset.single_le_sum (f := fun i => if w = s i (A.P w) then σ i else 0)
        (fun i _ => by positivity) (Finset.mem_univ i₀)))
    exact (if_pos (by rw [hPw])).symm
  by_contra hne
  rw [not_nonempty_iff] at hne
  rw [(L.S q).rep w (by rw [hPw]; exact (L.nbhd q).mem_U), Fintype.card_eq_zero, Nat.cast_zero,
    inv_zero, zero_mul] at hpos'
  exact lt_irrefl _ hpos'

end StructuredOn

/-- **Witness for `StructuredOn`**: a structured tuple on `X` is a structured sc⁺-multisection
on `W|V` for `V = X` (so the hypothesis of Proposition 13.4.2 is satisfiable, for instance by
the zero multisection, `isStructurable_zeroMultisection`). -/
def StructuredTuple.toStructuredOn (T : StructuredTuple A) : StructuredOn A univ where
  Λ := T.Λ
  isScPlusMultisectionOn := ⟨fun q _ _ => T.isScPlusMultisection.1 q, fun x _ => by
    obtain ⟨R, k, s, σ, h⟩ := T.isScPlusMultisection.2 x
    exact ⟨R, subset_univ _, k, s, σ, h⟩⟩
  nbhd := T.dec.𝒰.nbhd
  isGoodIn := T.dec.𝒰.isGoodIn_univ
  S q := T.dec.S q
  τ q q' := T.tau.τ q q'
  locallyConstant q q' := (T.tau.isCorrespondence q q').locallyConstant
  finite q q' := (T.tau.isCorrespondence q q').finite
  biact q q' := (T.tau.isCorrespondence q q').biact
  compat q q' := (T.tau.isCorrespondence q q').compat
  diag q := T.tau.diag q
  swap q q' := T.tau.swap q q'

/-! ### The extension functor `Λ̄` -/

/-- **The extension `Λ̄`** (Proposition 13.4.2 (1)): `Λ̄(w) = Λ(w₀)` for some `w₀` over `V` in the
orbit of `w` (and `0` if there is none; with `|V| = |X|` there always is one). -/
def extendMult (V : Set A.Obj) (Λ : A.W → ℚ≥0) (w : A.W) : ℚ≥0 :=
  if h : ∃ w₀, A.P w₀ ∈ V ∧ A.E.toEpGroupoid.π w₀ = A.E.toEpGroupoid.π w then Λ h.choose else 0

variable {V : Set A.Obj} {Λ : A.W → ℚ≥0}

theorem extendMult_congr {a b : A.W} (h : A.E.toEpGroupoid.π a = A.E.toEpGroupoid.π b) :
    extendMult V Λ a = extendMult V Λ b := by
  unfold extendMult; rw [h]

/-- **`Λ̄` is a functor on `W`.** -/
theorem isWFunctor_extendMult : IsWFunctor A (extendMult V Λ) := fun q =>
  extendMult_congr (A.E.toEpGroupoid.π_src_eq_π_tgt q).symm

/-- **`Λ̄` extends `Λ`** (`Λ` a functor on `W|V`). -/
theorem extendMult_eq (hΛ : IsWFunctorOn A V Λ) {w : A.W} (hw : A.P w ∈ V) :
    extendMult V Λ w = Λ w := by
  have h : ∃ w₀, A.P w₀ ∈ V ∧ A.E.toEpGroupoid.π w₀ = A.E.toEpGroupoid.π w := ⟨w, hw, rfl⟩
  rw [extendMult, dif_pos h]
  exact hΛ.eq_of_π_eq h.choose_spec.1 hw h.choose_spec.2

/-- Every `w` is isomorphic to some `w₀` over `V` when `|V| = |X|`. -/
theorem exists_mem_of_π_image (hπV : A.X.π '' V = univ) (w : A.W) :
    ∃ w₀, A.P w₀ ∈ V ∧ A.E.toEpGroupoid.π w₀ = A.E.toEpGroupoid.π w := by
  obtain ⟨q, hq, hqx⟩ : A.X.π (A.P w) ∈ A.X.π '' V := hπV ▸ mem_univ _
  obtain ⟨φ, hs, ht⟩ := (A.X.π_eq_π_iff).1 hqx
  have hw : A.P w = A.X.src (A.X.inv φ) := by rw [A.X.src_inv, ht]
  refine ⟨fibAct (A.X.inv φ) w, ?_, PushChart.π_fibAct hw⟩
  rw [P_fibAct hw, A.X.tgt_inv, hs]; exact hq

/-- **`Λ̄` is the only functor on `W` extending `Λ`** ("canonical", Proposition 13.4.2 (1)). -/
theorem eq_extendMult (hπV : A.X.π '' V = univ) (hΛ : IsWFunctorOn A V Λ) {Λ' : A.W → ℚ≥0}
    (hΛ' : IsWFunctor A Λ') (h : ∀ w, A.P w ∈ V → Λ' w = Λ w) : Λ' = extendMult V Λ := by
  funext w
  obtain ⟨w₀, hw₀, hπ⟩ := exists_mem_of_π_image hπV w
  rw [← hΛ'.eq_of_π_eq hπ, h w₀ hw₀, ← extendMult_eq hΛ hw₀, extendMult_congr hπ]

/-! ### The unit chart of the identity -/

/-- The identity strong bundle equivalence. -/
theorem equivalences_id_sep (A : SEP.{u}) : SEP.equivalences (𝟙 A) := SEP.equivalences.id_mem A

/-- `Φ_*Λ = Λ` for the identity and a functor `Λ`. -/
theorem pushMult_id {Λ : A.W → ℚ≥0} (hΛ : IsWFunctor A Λ) (w : A.W) :
    pushMult (𝟙 A) (equivalences_id_sep A) Λ w = Λ w :=
  pushMult_eq (equivalences_id_sep A) hΛ rfl

/-- **The unit chart** of `𝟙 A` on `U`: `Q = id`, `ψ_u = 1_u`. -/
def unitChart {x : A.Obj} (N : A.X.NatNbhd x) : (SEP.Hom.ϕ (𝟙 A)).TransportChart x x where
  ψ₀ := A.X.unit x
  src_ψ₀ := A.X.src_unit x
  tgt_ψ₀ := A.X.tgt_unit x
  W := N.U
  W' := N.U
  Q := id
  Qinv := id
  ψ := A.X.unit
  mem_W := N.mem_U
  isScDiffeoOn_Q := MPolyfold.isScDiffeoOn_id N.isOpen_U
  isScSmoothOn_ψ := A.X.isScSmoothMap_unit.mono N.isOpen_U (subset_univ _)
  src_ψ u _ := A.X.src_unit u
  tgt_ψ u _ := A.X.tgt_unit u
  ψ_self := rfl

theorem unitChart_conj {x : A.Obj} (N : A.X.NatNbhd x) (g : A.X.Isotropy x) :
    (unitChart N).conj g = g := by
  refine GroupoidStr.Isotropy.ext ?_
  rw [EpFunctor.TransportChart.conj_val]
  change A.X.comp (A.X.comp (A.X.unit x) g.val) (A.X.inv (A.X.unit x)) = g.val
  rw [A.X.inv_unit, A.X.unit_comp_of_eq g.tgt_val, A.X.comp_unit_of_eq g.src_val]

/-- **The unit chart is adapted to `U` itself.** -/
theorem isPushNbhd_unit {x : A.Obj} (N : A.X.NatNbhd x) :
    IsPushNbhd (F := 𝟙 A) (unitChart N) N N where
  subset_W' := subset_rfl
  Qinv_mem hz := hz
  Φ_mem_W z hz g := N.Φ_mem g hz
  Γ_eq g z hz := by
    rw [unitChart_conj]
    change N.rep.Γ g z =
      A.X.comp (A.X.comp (A.X.unit (N.rep.Φ g z)) (N.rep.Γ g z)) (A.X.inv (A.X.unit z))
    rw [A.X.inv_unit, A.X.unit_comp_of_eq (N.tgt_Γ g hz), A.X.comp_unit_of_eq (N.src_Γ g hz)]

/-- The pushed section along the unit chart is the section itself on `U`. -/
theorem pushSec_unit {x : A.Obj} (N : A.X.NatNbhd x) {s : A.Obj → A.W}
    (hs : ∀ u ∈ N.U, A.P (s u) = u) {z : A.Obj} (hz : z ∈ N.U) :
    pushSec (unitChart N) s z = s z := by
  rw [(isPushNbhd_unit N).pushSec_eq (equivalences_id_sep A) hs hz]
  exact PushChart.fibAct_unit (hs z hz)

/-- The lift along two unit charts is the identity. -/
theorem liftMor_unit {x x' : A.Obj} (N : A.X.NatNbhd x) (N' : A.X.NatNbhd x') {φ : A.Mor}
    (hφ : φ ∈ A.X.morBetween N.U N'.U) :
    PushChart.liftMor (unitChart N) (unitChart N') φ = φ :=
  PushChart.liftMor_eq_of_comp (equivalences_id_sep A) hφ rfl rfl (by
    change A.X.comp (A.X.unit (A.X.tgt φ)) φ = A.X.comp φ (A.X.unit (A.X.src φ))
    rw [A.X.unit_comp_of_eq rfl, A.X.comp_unit_of_eq rfl])

/-- An adapted neighbourhood stays adapted after shrinking with the same action. -/
theorem IsPushNbhd.of_le {F : A ⟶ A} {x y : A.Obj} {T : (SEP.Hom.ϕ F).TransportChart x y}
    {N : A.X.NatNbhd x} {N₀ N' : A.X.NatNbhd y} (h : IsPushNbhd T N N₀) (hrep : N'.rep = N₀.rep)
    (hsub : N'.U ⊆ N₀.U) : IsPushNbhd T N N' where
  subset_W' := hsub.trans h.subset_W'
  Qinv_mem hz := h.Qinv_mem (hsub hz)
  Φ_mem_W z hz := h.Φ_mem_W z (hsub hz)
  Γ_eq g z hz := by rw [hrep]; exact h.Γ_eq g z (hsub hz)

/-! ### Charts at the points of `X` -/

/-- **A chart at `x`** for the extension (proof of Proposition 13.4.2 (2)): a point `q_x ∈ V`, the
chart `Q = t ∘ (s|U(ψ_x))⁻¹` of `𝟙 A` along `ψ_x : q_x → x` (the text's `D_x`), and a
neighbourhood `U(x)` with the natural action adapted to `U(q_x)`, with the properness
property. -/
structure ExtChart (L : StructuredOn A V) (x : A.Obj) where
  /-- The point `q_x ∈ V`. -/
  q : V
  /-- The chart along `ψ_x : q_x → x`. -/
  T : (SEP.Hom.ϕ (𝟙 A)).TransportChart (q : A.Obj) x
  /-- The neighbourhood `U(x)`. -/
  N : A.X.NatNbhd x
  isPush : IsPushNbhd T (L.nbhd q) N
  isProper : A.X.IsProperSubset (closure N.U)

/-- **The data `V`, `|V| = |X|` and the sets `O(x)` of Proposition 13.4.2.** -/
structure ExtSetup (L : StructuredOn A V) where
  isOpen : IsOpen V
  π_image : A.X.π '' V = univ
  /-- The open neighbourhoods `O(x)` (only `x ∉ V` matter). -/
  O : A.Obj → Set A.Obj
  isOpen_O : ∀ x, IsOpen (O x)
  mem_O : ∀ x, x ∈ O x

variable {L : StructuredOn A V}

/-- **The unit chart at `q ∈ V`**: `q_x = q`, `Q = id`, `U(q)` the given one. -/
def unitExt (E : ExtSetup L) {x : A.Obj} (hx : x ∈ V) : ExtChart L x where
  q := ⟨x, hx⟩
  T := unitChart (L.nbhd x)
  N := L.nbhd x
  isPush := isPushNbhd_unit (L.nbhd x)
  isProper := (L.isGoodIn.isGoodOn E.isOpen E.π_image).isProperSubset_closure x hx

/-- **Charts exist at every `x`, with `U(x)` inside any open `O ∋ x`.** -/
theorem exists_extChart (L : StructuredOn A V) (hπV : A.X.π '' V = univ) (x : A.Obj)
    {O : Set A.Obj} (hO : IsOpen O) (hxO : x ∈ O) : ∃ c : ExtChart L x, c.N.U ⊆ O := by
  obtain ⟨q, hq, hqx⟩ : A.X.π x ∈ A.X.π '' V := hπV ▸ mem_univ _
  obtain ⟨ψ₀, hs, ht⟩ := (A.X.π_eq_π_iff).1 hqx
  have hloc := (sbe (equivalences_id_sep A)).isEquivalence_base.isLocalScDiffeo_obj
  obtain ⟨T, -⟩ := (SEP.Hom.ϕ (𝟙 A)).exists_transportChart hloc (x := q) hs ht
  obtain ⟨N₀, hpush, hprop⟩ := exists_isPushNbhd T (L.nbhd (⟨q, hq⟩ : V))
  obtain ⟨N', hrep, hsub⟩ := N₀.exists_restrict_subset hO hxO
  exact ⟨⟨⟨q, hq⟩, T, N', hpush.of_le hrep fun z hz => (hsub hz).1,
    isProperMap_domRestrict_of_subset_of_isClosed A.X.continuous_src hprop
      (closure_mono fun z hz => (hsub hz).1) isClosed_closure⟩, fun z hz => (hsub hz).2⟩

/-- **The chosen charts**: the unit chart at `x ∈ V`, a chart with `U(x) ⊆ O(x)` at `x ∉ V`. -/
def extChart (E : ExtSetup L) (x : A.Obj) : ExtChart L x :=
  if hx : x ∈ V then unitExt E hx
  else (exists_extChart L E.π_image x (E.isOpen_O x) (E.mem_O x)).choose

theorem extChart_of_mem (E : ExtSetup L) {x : A.Obj} (hx : x ∈ V) :
    extChart E x = unitExt E hx := dif_pos hx

theorem extChart_subset (E : ExtSetup L) {x : A.Obj} (hx : x ∉ V) :
    (extChart E x).N.U ⊆ E.O x := by
  rw [extChart, dif_neg hx]
  exact (exists_extChart L E.π_image x (E.isOpen_O x) (E.mem_O x)).choose_spec

end SBLocalization

end Polyfold
