import Polyfold.Chapter17.TameBoundaryUniformizer
import Polyfold.Chapter17.Subpolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.4 (pp. 798–800): **Lemma 17.4.13**, the set `M(Ψ, Ψ')*_{θ,θ'}` and the bijection (17.71).

For good open neighbourhoods `U(ō)`, `U'(ō')` and faces `θ`, `θ'`, `M(Ψ, Ψ')*_{θ,θ'}` (Definition
17.4.12) consists of the `h = (x, φ, x')` with `x ∈ θ`, `x' ∈ θ'` and `h_*θ = θ'`.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `GoodNbhd.exists_nhds_germLift`: face germs are carried along locally constantly (if `h`
  carries the germ of `θ` at `x` to that of `θ'` at `x'`, then near `x` every `T.srcInv y`,
  `y ∈ θ`, carries the germ of `θ` at `y` to that of `θ'` at `f(y)`).
* `GoodNbhd.exists_isOpen_inter_eq` (`M(Ψ, Ψ')*_{θ,θ'} = 𝒪 ∩ s⁻¹(θ)` with `𝒪` open),
  `isSubMPolyfold_transFaceSet`, `exists_sheet_transFaceSet` (the sheets `s : U → N` carrying
  `U ∩ M(Ψ, Ψ')*_{θ,θ'}` onto `N ∩ θ`, the map `R` of (17.73)), `degIndex_tr`
  (`d_{M(Ψ, Ψ')} = d_O ∘ s`), `one_le_degIndex_of_mem_transFaceSet`.
* `faceTrToTr_injective`, `faceTrEquiv` (**(17.71)**, `M(Ψ_θ, Ψ'_{θ'}) ≃ M(Ψ, Ψ')*_{θ,θ'}`).
* **Lemma 17.4.13** without the tameness clause (`lemma_17_4_13_subMPolyfold`); the full form as
  we read it, with the tameness of the induced structure (Definition 2.5.18), is `lemma_17_4_13`
  in `TameBoundaryTame.lean`.  `lemma_17_4_13_literal`, `lemma_17_4_13_literal_quadrant`: the
  letter of the pointer to Definition 2.5.19, under which no face qualifies.
* General facts: `MPolyfold.IsSubMPolyfold.inter_isOpen`,
  `MPolyfold.not_isTameSubMPolyfold_of_mem_closure` (a subset of `{d ≥ 1}` meeting the closure of
  `{d = 0}` is not a tame sub-M-polyfold), `MPolyfold.IsLocalScDiffeo.mem_closure_degIndex_eq_zero`,
  `TameBoundaryExample.corner_mem_closure_dq_eq_zero`.

## Readings

* **"Tame sub-M-polyfold".** We read the faces in the sense of Definition 2.5.18, the sense the
  book itself gives faces (Proposition 2.5.15 – Theorem 2.5.17): `M(Ψ, Ψ')*_{θ,θ'}` is a
  sub-M-polyfold of `M(Ψ, Ψ')`, near each element `s` is an sc-diffeomorphism carrying it onto an
  open piece of the face `θ` (with its structure as a sub-M-polyfold of `O`, Theorem 2.5.17), and
  its induced structure is tame (`lemma_17_4_13`, `TameBoundaryTame.lean`).  The proof in the
  text uses the retraction `r` onto the face `θ` with `d_θ` in place of `d_O`.  The text points to
  Definition 2.5.19 before the lemma; taken literally, (2) of that definition asks a retraction
  with `d(r(x)) = d(x)`, while `M(Ψ, Ψ')*_{θ,θ'}` lies in `{d ≥ 1}` (`d = d_O ∘ s`, `θ ⊆ ∂O`) and
  near the unit at a corner meets the closure of `{d = 0}`, so no such `r` exists
  (`lemma_17_4_13_literal_quadrant`); under Definition 2.5.19 no face of positive codimension
  qualifies.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

universe u

namespace Polyfold

open TameBoundary

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {hT : S.IsTame}

namespace GoodNbhd

variable {Ψ Ψ' : S.Unif} {o : Ψ.1.O} {o' : Ψ'.1.O} (V : S.GoodNbhd Ψ o) (V' : S.GoodNbhd Ψ' o')

/-- **Face germs are transported locally constantly.** -/
theorem exists_nhds_germLift {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) {a : S.Tr Ψ Ψ'} (T : S.AdmissibleTriple a) (hx : a.src ∈ θ)
    (hx' : a.tgt ∈ θ')
    (hl : S.GermLift hT a (V.faceGerm hT hθ a.src hx) (V'.faceGerm hT hθ' a.tgt hx')) :
    ∃ N : Set Ψ.1.O, IsOpen N ∧ a.src ∈ N ∧ N ⊆ T.srcSet ∧ ∀ y (hy : y ∈ θ), y ∈ N →
      ∃ hy' : T.germMap y ∈ θ', S.GermLift hT (T.srcInv y) (V.faceGerm hT hθ y hy)
        (V'.faceGerm hT hθ' (T.germMap y) hy') := by
  classical
  set d := S.hdU hT Ψ
  set d' := S.hdU hT Ψ'
  obtain ⟨-, hlT⟩ := germLift_iff_forall.1 hl
  obtain ⟨W, hf, t, htW, htp, htq⟩ := hlT T
  obtain ⟨s, hs, hsx, hsm, hse⟩ := V.faceGerm_mem_uSet (hT := hT) hθ a.src hx
  obtain ⟨s', hs', hsx', hsm', hse'⟩ := V'.faceGerm_mem_uSet (hT := hT) hθ' a.tgt hx'
  have hsa : s.x = a.src := by
    have := congrArg (bMap d) hs
    rwa [bMap_cls, bMap_faceGerm] at this
  have hsa' : s'.x = a.tgt := by
    have := congrArg (bMap d') hs'
    rwa [bMap_cls, bMap_faceGerm] at this
  have hta : t.x = a.src := by
    have := congrArg (bMap d) htp
    rwa [bMap_cls, bMap_faceGerm] at this
  set N₀ : Set Ψ.1.O := s.V ∩ (W ∩ T.germMap ⁻¹' s'.V) ∩ T.srcSet with hN₀
  have hN₀o : IsOpen N₀ :=
    (s.mem.1.1.1.inter (hf.continuousOn.isOpen_inter_preimage hf.isOpen s'.mem.1.1.1)).inter
      T.isOpen_srcSet
  have haN₀ : a.src ∈ N₀ := by
    refine ⟨⟨hsa ▸ s.mem.2.1, ?_, ?_⟩, T.src_mem⟩
    · rw [← hta]; exact htW t.mem.2.1
    · change T.germMap a.src ∈ s'.V
      rw [T.germMap_src, ← hsa']; exact s'.mem.2.1
  obtain ⟨t', ht'p, ht'N, hcent, -⟩ := exists_rep_centered d (V.faceGerm hT hθ a.src hx) hN₀o
    (by rw [bMap_faceGerm]; exact haN₀) isOpen_univ (mem_univ _)
  have ht'a : t'.x = a.src := by
    have := congrArg (bMap d) ht'p
    rwa [bMap_cls, bMap_faceGerm] at this
  have ht's : t'.V ⊆ s.V := fun z hz => (ht'N hz).1.1
  have ht'W : t'.V ⊆ W := fun z hz => (ht'N hz).1.2.1
  have ht'f : ∀ z ∈ t'.V, T.germMap z ∈ s'.V := fun z hz => (ht'N hz).1.2.2
  have ht'T : t'.V ⊆ T.srcSet := fun z hz => (ht'N hz).2
  have ht'U : t'.V ⊆ V.1.U := ht's.trans hsm.1
  -- Claim A: `U(t') ⊆ U(ō, U(ō), θ)`.
  have hA : uSet d t' ⊆ uSet d (V.triple hT hθ) := by
    have hm1 : IsMor Ψ.1.P.degIndex t'.x t'.V s.x s.V := by
      rw [ht'a, ← hsa]; exact isMor_of_subset ht's s.mem
    have hm : IsMor Ψ.1.P.degIndex t'.x t'.V o V.1.U :=
      IsMor.trans d t'.mem.2.1 s.mem.1.1.1 V.isFaceStructuredOpen hm1 hsm
    have he1 : faceExt Ψ.1.P.degIndex s.V t'.θ = s.θ :=
      (cls_eq_iff_faceExt d (ht'a.trans hsa.symm) ht's).1 (ht'p.trans hs.symm)
    have he : faceExt Ψ.1.P.degIndex V.1.U t'.θ = θ := by
      rw [← faceExt_faceExt d s.mem.1.1.1 V.isOpen ht's hsm.1 t'.mem_faces.1, he1]
      exact hse
    exact uSet_subset d hm he
  -- Claim B: `U(f(t')) ⊆ U(ō', U'(ō'), θ')`.
  have hmapcls : (t'.map d' hf ht'W).cls = V'.faceGerm hT hθ' a.tgt hx' := by
    rw [← htq]
    exact map_cls_eq d d' hf hf ht'W htW (ht'p.trans htp.symm) isOpen_univ (mem_univ _)
      fun _ _ => rfl
  have hsub' : (t'.map d' hf ht'W).V ⊆ s'.V := image_subset_iff.2 ht'f
  have hmx : (t'.map d' hf ht'W).x = s'.x := by
    change T.germMap t'.x = s'.x
    rw [ht'a, T.germMap_src, hsa']
  have hB : uSet d' (t'.map d' hf ht'W) ⊆ uSet d' (V'.triple hT hθ') := by
    have hm1 : IsMor Ψ'.1.P.degIndex (t'.map d' hf ht'W).x (t'.map d' hf ht'W).V s'.x s'.V := by
      rw [hmx]; exact isMor_of_subset hsub' s'.mem
    have hm : IsMor Ψ'.1.P.degIndex (t'.map d' hf ht'W).x (t'.map d' hf ht'W).V o' V'.1.U :=
      IsMor.trans d' (t'.map d' hf ht'W).mem.2.1 s'.mem.1.1.1 V'.isFaceStructuredOpen hm1 hsm'
    have he1 : faceExt Ψ'.1.P.degIndex s'.V (t'.map d' hf ht'W).θ = s'.θ :=
      (cls_eq_iff_faceExt d' hmx hsub').1 (hmapcls.trans hs'.symm)
    have he : faceExt Ψ'.1.P.degIndex V'.1.U (t'.map d' hf ht'W).θ = θ' := by
      rw [← faceExt_faceExt d' s'.mem.1.1.1 V'.isOpen hsub' hsm'.1
        (t'.map d' hf ht'W).mem_faces.1, he1]
      exact hse'
    exact uSet_subset d' hm he
  -- Claim C: `θ ∩ V(t') ⊆ θ(t')`.
  have hC : ∀ y ∈ θ, y ∈ t'.V → y ∈ t'.θ := by
    intro y hyθ hyV
    obtain ⟨γ, hγ, hγe⟩ := exists_faceExt_eq d t'.mem.1.1.1 V.isOpen ht'U hyV
      (θ' := θ) ⟨hθ, hyθ⟩
    have hγx : γ ∈ facesThrough Ψ.1.P.degIndex t'.V t'.x := ⟨hγ.1, hcent γ hγ.1⟩
    have hinj := faceExt_injOn d t'.mem.1.1.1 V.isOpen ht'U t'.mem.2.1
      (V.isFaceStructuredOpen.2 t'.x (ht'U t'.mem.2.1))
    have he1 : faceExt Ψ.1.P.degIndex s.V t'.θ = s.θ :=
      (cls_eq_iff_faceExt d (ht'a.trans hsa.symm) ht's).1 (ht'p.trans hs.symm)
    have he : faceExt Ψ.1.P.degIndex V.1.U t'.θ = θ := by
      rw [← faceExt_faceExt d s.mem.1.1.1 V.isOpen ht's hsm.1 t'.mem_faces.1, he1]
      exact hse
    have : γ = t'.θ := hinj hγx t'.mem_faces (hγe.trans he.symm)
    rw [← this]; exact hγ.2
  refine ⟨t'.V, t'.mem.1.1.1, ht'a ▸ t'.mem.2.1, ht'T, fun y hy hyN => ?_⟩
  have hyt : y ∈ t'.θ := hC y hy hyN
  rw [← bMap_image_uSet_of_isCenteredAt d hcent] at hyt
  obtain ⟨q, hq, hqy⟩ := hyt
  have hqe : V.faceGerm hT hθ y hy = q := V.faceGerm_eq_of_mem hθ hy (hA hq) hqy
  obtain ⟨q', hq', hqq'⟩ := exists_isLiftOf_mem_uSet d d' hf ht'W hq
  have hq'b : bMap d' q' = T.germMap y := by rw [hqq'.bMap_eq, hqy]
  have hy' : T.germMap y ∈ θ' := by
    rw [← hq'b]; exact bMap_mem_of_mem_uSet d' (hB hq')
  have hq'e : V'.faceGerm hT hθ' (T.germMap y) hy' = q' :=
    V'.faceGerm_eq_of_mem hθ' hy' (hB hq') hq'b
  refine ⟨hy', ?_⟩
  rw [hqe, hq'e]
  have hyT : y ∈ T.srcSet := ht'T hyN
  exact germLift_of_mem_carrier T (T.srcInv_mem hyT) (by rw [hqy, T.src_srcInv hyT]) hqq'

end GoodNbhd

end GCT.PolyfoldConstruction


namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- A sub-M-polyfold meets an open set in a sub-M-polyfold. -/
theorem IsSubMPolyfold.inter_isOpen {A O : Set X} (hA : P.IsSubMPolyfold A) (hO : IsOpen O) :
    P.IsSubMPolyfold (A ∩ O) := by
  rintro a ⟨haA, haO⟩
  obtain ⟨V, hV, haV, r, hrV, hr, hidem, himg⟩ := hA a haA
  have hra : r a = a := by
    have : a ∈ r '' V := by rw [himg]; exact ⟨haA, haV⟩
    obtain ⟨b, hb, rfl⟩ := this
    exact hidem b hb
  set V' := V ∩ r ⁻¹' O
  have hV' : IsOpen V' := hr.continuousOn.isOpen_inter_preimage hV hO
  have hrV' : MapsTo r V' V' := fun x hx =>
    ⟨hrV hx.1, by change r (r x) ∈ O; rw [hidem x hx.1]; exact hx.2⟩
  refine ⟨V', hV', ⟨haV, by change r a ∈ O; rw [hra]; exact haO⟩, r, hrV',
    hr.mono hV' inter_subset_left, fun x hx => hidem x hx.1, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hy : r x ∈ A ∩ V := by rw [← himg]; exact ⟨x, hx.1, rfl⟩
    exact ⟨⟨hy.1, hx.2⟩, hrV' hx⟩
  · rintro ⟨⟨hyA, -⟩, hyV'⟩
    refine ⟨y, hyV', ?_⟩
    have : y ∈ r '' V := by rw [himg]; exact ⟨hyA, hyV'.1⟩
    obtain ⟨b, hb, rfl⟩ := this
    exact hidem b hb

/-- **A subset of `∂X` which meets the closure of `{d_X = 0}` is not a tame sub-M-polyfold**
(2021 Definition 2.5.19 (2): a tame retraction `r` onto `Y ∩ V` satisfies `d_X(r(x)) = d_X(x)`,
so it cannot map a point of index `0` into `Y`). -/
theorem not_isTameSubMPolyfold_of_mem_closure {Y : Set X} (hY : ∀ y ∈ Y, 1 ≤ P.degIndex y)
    {y : X} (hy : y ∈ Y) (hcl : y ∈ closure {x | P.degIndex x = 0}) :
    ¬ P.IsTameSubMPolyfold Y := by
  rintro ⟨-, h⟩
  obtain ⟨d, hyd⟩ := h y hy
  obtain ⟨x, hxV, hx0⟩ := mem_closure_iff.1 hcl d.V d.isOpen hyd
  have hrx : d.r x ∈ Y := d.toSubData.apply_mem hxV
  have h1 := hY _ hrx
  rw [d.degIndex_apply x hxV] at h1
  rw [show P.degIndex x = 0 from hx0] at h1
  exact absurd h1 (by norm_num)

end MPolyfold

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {hT : S.IsTame}

/-- **`d_{M(Ψ,Ψ')} = d_O ∘ s`** (`s` is a local sc-diffeomorphism). -/
theorem degIndex_tr {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') :
    (S.transPolyfold Ψ Ψ').degIndex a = Ψ.1.P.degIndex a.src := by
  obtain ⟨W, haW, hW⟩ := (S.isLocalScDiffeo_trSrc Ψ Ψ').isDLocalHomeo a
  exact (hW.deg_eq a haW).symm

namespace GoodNbhd

variable {Ψ Ψ' : S.Unif} {o : Ψ.1.O} {o' : Ψ'.1.O} (V : S.GoodNbhd Ψ o) (V' : S.GoodNbhd Ψ' o')

/-- **`M(Ψ, Ψ')*_{θ,θ'}` is open in `s⁻¹(θ)`**: near an element, every transition element over
`θ` lies in it. -/
theorem exists_isOpen_transFaceSet {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) {a : S.Tr Ψ Ψ'} (ha : a ∈ V.transFaceSet hT V' hθ hθ') :
    ∃ (T : S.AdmissibleTriple a) (N : Set Ψ.1.O), IsOpen N ∧ a.src ∈ N ∧ N ⊆ T.srcSet ∧
      ∀ b ∈ T.carrier, b.src ∈ N → b.src ∈ θ → b ∈ V.transFaceSet hT V' hθ hθ' := by
  obtain ⟨hx, hx', hl⟩ := ha
  let T := (S.exists_admissibleTriple a).some
  obtain ⟨N, hNo, haN, hNT, hN⟩ := V.exists_nhds_germLift V' hθ hθ' T hx hx' hl
  refine ⟨T, N, hNo, haN, hNT, fun b hb hbN hbθ => ?_⟩
  obtain ⟨hy', hl'⟩ := hN b.src hbθ hbN
  have hbe : T.srcInv b.src = b := T.srcInv_eq hb
  have hbt : T.germMap b.src = b.tgt := T.germMap_eq hb
  refine ⟨hbθ, hbt ▸ hy', ?_⟩
  rw [hbe] at hl'
  convert hl' using 2
  exact hbt.symm

/-- `M(Ψ, Ψ')*_{θ,θ'} = 𝒪 ∩ s⁻¹(θ)` for an open `𝒪 ⊆ M(Ψ, Ψ')`. -/
theorem exists_isOpen_inter_eq {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    ∃ 𝒪 : Set (S.Tr Ψ Ψ'), IsOpen 𝒪 ∧
      V.transFaceSet hT V' hθ hθ' = 𝒪 ∩ (fun b : S.Tr Ψ Ψ' => b.src) ⁻¹' θ := by
  classical
  have hex : ∀ a : S.Tr Ψ Ψ', ∃ (T : S.AdmissibleTriple a) (N : Set Ψ.1.O),
      a ∈ V.transFaceSet hT V' hθ hθ' → IsOpen N ∧ a.src ∈ N ∧ N ⊆ T.srcSet ∧
        ∀ b ∈ T.carrier, b.src ∈ N → b.src ∈ θ → b ∈ V.transFaceSet hT V' hθ hθ' := by
    intro a
    by_cases ha : a ∈ V.transFaceSet hT V' hθ hθ'
    · obtain ⟨T, N, h⟩ := V.exists_isOpen_transFaceSet V' hθ hθ' ha
      exact ⟨T, N, fun _ => h⟩
    · exact ⟨(S.exists_admissibleTriple a).some, ∅, fun h => absurd h ha⟩
  choose T N hTN using hex
  refine ⟨⋃ a ∈ V.transFaceSet hT V' hθ hθ',
    (T a).carrier ∩ (fun b : S.Tr Ψ Ψ' => b.src) ⁻¹' N a, ?_, ?_⟩
  · refine isOpen_biUnion fun a ha => ?_
    exact (T a).isOpen_carrier.inter ((hTN a ha).1.preimage (S.continuous_trSrc Ψ Ψ'))
  · ext b
    constructor
    · intro hb
      exact ⟨mem_biUnion hb ⟨(T b).mem_carrier, (hTN b hb).2.1⟩, hb.1⟩
    · rintro ⟨hb, hbθ⟩
      obtain ⟨a, ha, hbc, hbN⟩ := mem_iUnion₂.1 hb
      exact (hTN a ha).2.2.2 b hbc hbN hbθ

/-- A face of a good neighbourhood is a sub-M-polyfold of `O` (2021 Theorem 2.5.17). -/
theorem isSubMPolyfold_face (hT : S.IsTame) {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    Ψ.1.P.IsSubMPolyfold θ :=
  Ψ.1.P.isSubMPolyfold_of_isFaceIn (S.isTame_unif hT Ψ) V.isFaceStructuredOpen hθ

/-- **`M(Ψ, Ψ')*_{θ,θ'}` is a sub-M-polyfold of `M(Ψ, Ψ')`** (the first assertion of Lemma 17.4.13
without "tame"). -/
theorem isSubMPolyfold_transFaceSet {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    (S.transPolyfold Ψ Ψ').IsSubMPolyfold (V.transFaceSet hT V' hθ hθ') := by
  obtain ⟨𝒪, h𝒪, he⟩ := V.exists_isOpen_inter_eq (hT := hT) V' hθ hθ'
  rw [he, inter_comm]
  exact ((S.isLocalScDiffeo_trSrc Ψ Ψ').isSubMPolyfold_preimage
    (V.isSubMPolyfold_face hT hθ)).inter_isOpen h𝒪

/-- **The sheets of `M(Ψ, Ψ')*_{θ,θ'}`** (the retraction `R = (s|W(h₀))⁻¹ ∘ r ∘ s` of the proof of
Lemma 17.4.13): near every element `s` is an sc-diffeomorphism `U → N` carrying
`U ∩ M(Ψ, Ψ')*_{θ,θ'}` onto `N ∩ θ`. -/
theorem exists_sheet_transFaceSet {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) {a : S.Tr Ψ Ψ'} (ha : a ∈ V.transFaceSet hT V' hθ hθ') :
    ∃ (U : Set (S.Tr Ψ Ψ')) (N : Set Ψ.1.O) (g : Ψ.1.O → S.Tr Ψ Ψ'), a ∈ U ∧
      (S.transPolyfold Ψ Ψ').IsScDiffeoOn Ψ.1.P (fun b : S.Tr Ψ Ψ' => b.src) g U N ∧
      (fun b : S.Tr Ψ Ψ' => b.src) '' (U ∩ V.transFaceSet hT V' hθ hθ') = N ∩ θ := by
  obtain ⟨T, N, hNo, haN, hNT, hN⟩ := V.exists_isOpen_transFaceSet V' hθ hθ' ha
  set U := T.carrier ∩ (fun b : S.Tr Ψ Ψ' => b.src) ⁻¹' N
  have hU : IsOpen U := T.isOpen_carrier.inter (hNo.preimage (S.continuous_trSrc Ψ Ψ'))
  have hd := T.isScDiffeoOn_src.restrict hU inter_subset_left
  have hUN : T.srcSet ∩ T.srcInv ⁻¹' U = N := by
    ext y
    constructor
    · rintro ⟨hyT, -, hy⟩; change (T.srcInv y).src ∈ N at hy
      rwa [T.src_srcInv hyT] at hy
    · intro hy
      refine ⟨hNT hy, T.srcInv_mem (hNT hy), ?_⟩
      change (T.srcInv y).src ∈ N
      rwa [T.src_srcInv (hNT hy)]
  rw [hUN] at hd
  refine ⟨U, N, T.srcInv, ⟨T.mem_carrier, haN⟩, hd, ?_⟩
  ext y
  constructor
  · rintro ⟨b, ⟨⟨-, hbN⟩, hb⟩, rfl⟩
    exact ⟨hbN, hb.1⟩
  · rintro ⟨hyN, hyθ⟩
    refine ⟨T.srcInv y, ⟨hd.mapsTo_inv hyN, ?_⟩, T.src_srcInv (hNT hyN)⟩
    exact hN _ (T.srcInv_mem (hNT hyN)) (by rwa [T.src_srcInv (hNT hyN)])
      (by rwa [T.src_srcInv (hNT hyN)])

/-- On `M(Ψ, Ψ')*_{θ,θ'}` the degeneracy index of `M(Ψ, Ψ')` is at least `1`. -/
theorem one_le_degIndex_of_mem_transFaceSet {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O}
    (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) {a : S.Tr Ψ Ψ'}
    (ha : a ∈ V.transFaceSet hT V' hθ hθ') : 1 ≤ (S.transPolyfold Ψ Ψ').degIndex a := by
  rw [degIndex_tr]
  obtain ⟨hx, -, -⟩ := ha
  exact (V.subset_bdry hθ hx).2

end GoodNbhd

end GCT.PolyfoldConstruction

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- **A local sc-diffeomorphism `f` pulls back the closure of `{d = 0}`**: if `f(x)` lies in the
closure of `{d_Y = 0}`, then `x` lies in the closure of `{d_X = 0}`. -/
theorem IsLocalScDiffeo.mem_closure_degIndex_eq_zero {f : X → Y} (hf : P.IsLocalScDiffeo Q f)
    {x : X} (hx : f x ∈ closure {y | Q.degIndex y = 0}) :
    x ∈ closure {x | P.degIndex x = 0} := by
  rw [mem_closure_iff_nhds] at hx ⊢
  intro O hO
  obtain ⟨U, N, g, hxU, hd⟩ := hf x
  have hxN : f x ∈ N := hd.mapsTo hxU
  have hc : ContinuousAt g (f x) :=
    hd.isScSmoothOn_inv.continuousOn.continuousAt (hd.isOpen_target.mem_nhds hxN)
  have hm : g ⁻¹' O ∩ N ∈ 𝓝 (f x) :=
    inter_mem (hc.preimage_mem_nhds (by rwa [hd.left_inv x hxU])) (hd.isOpen_target.mem_nhds hxN)
  obtain ⟨y, ⟨hyO, hyN⟩, hy0⟩ := hx _ hm
  refine ⟨g y, hyO, ?_⟩
  change P.degIndex (g y) = 0
  rw [← hf.degIndex_eq, hd.right_inv y hyN]
  exact hy0

end MPolyfold

namespace TameBoundaryExample

open MPolyfold

variable {n : ℕ} {W : ScBanach}

/-- **The corner of `[0,∞)ⁿ ⊕ W` is a limit of interior points**: `0` lies in the closure of
`{d = 0}` (the points `(t, …, t; 0)`, `t > 0`). -/
theorem corner_mem_closure_dq_eq_zero :
    (⟨0, zero_mem_quadrant n W⟩ : quadrant n W 0) ∈ closure {p | dq n W p = 0} := by
  let γ : ℝ → quadrant n W 0 := fun t =>
    ⟨(((fun _ => max t 0 : Fin n → ℝ), (0 : W 0)) : (Fin n → ℝ) × W 0), fun _ => le_max_right _ _⟩
  have hγ : Continuous γ :=
    ((continuous_pi fun _ => continuous_id.max continuous_const).prodMk
      continuous_const).subtype_mk _
  have h0 : γ 0 = ⟨0, zero_mem_quadrant n W⟩ := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    funext i; simp [γ]
  have hpos : ∀ t : ℝ, 0 < t → dq n W (γ t) = 0 := by
    intro t ht
    rw [dq_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    change max t 0 ≠ 0
    rw [max_eq_left ht.le]; exact ht.ne'
  rw [← h0]
  have hl : Tendsto γ (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (γ 0)) :=
    (hγ.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hl ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  exact hpos t ht

end TameBoundaryExample

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {hT : S.IsTame} {hS : S.HasUniformizers}

namespace GoodNbhd

variable {Ψ Ψ' : S.Unif} {o : Ψ.1.O} {o' : Ψ'.1.O} (V : S.GoodNbhd Ψ o) (V' : S.GoodNbhd Ψ' o')

/-- `h̄ ↦ h` is injective. -/
theorem faceTrToTr_injective {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    Injective (V.faceTrToTr V' (hT := hT) (hS := hS) (hθ := hθ) (hθ' := hθ')) := by
  intro h₁ h₂ he
  have hs : h₁.src = h₂.src := Subtype.ext (congrArg (fun a : S.Tr Ψ Ψ' => a.src) he)
  have ht : h₁.tgt = h₂.tgt := Subtype.ext (congrArg (fun a : S.Tr Ψ Ψ' => a.tgt) he)
  have hm : h₁.mor = h₂.mor := by
    refine BMor.ext_of_src ?_ (congrArg (fun a : S.Tr Ψ Ψ' => a.mor) he)
    exact h₁.src_mor.trans (hs ▸ h₂.src_mor.symm)
  exact GroupoidStr.TransitionSet.ext hs hm ht

/-- **2021 (17.71), p. 798**: the bijection `M(Ψ_θ, Ψ'_{θ'}) ≃ M(Ψ, Ψ')*_{θ,θ'}`,
`(x, Φ, x') ↦ (x, φ, x')`. -/
def faceTrEquiv {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) :
    V.FaceTr hT hS V' hθ hθ' ≃ V.transFaceSet hT V' hθ hθ' :=
  (Equiv.ofInjective _ (V.faceTrToTr_injective V' hθ hθ')).trans
    (Equiv.setCongr ((V.definition_17_4_12 V' (hS := hS) hθ).2.2.2 hθ'))

@[simp]
theorem faceTrEquiv_apply {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) (h : V.FaceTr hT hS V' hθ hθ') :
    (V.faceTrEquiv V' hθ hθ' h : S.Tr Ψ Ψ') = V.faceTrToTr V' h := rfl

/-- **2021 Lemma 17.4.13, p. 798**, all assertions except the tameness of the induced structure
(the full form is `lemma_17_4_13`, `TameBoundaryTame.lean`): `M(Ψ, Ψ')*_{θ,θ'}` is a
sub-M-polyfold of `M(Ψ, Ψ')` (the open part `𝒪 ∩ s⁻¹(θ)` of the preimage of the sub-M-polyfold
`θ` under the local sc-diffeomorphism `s`); near every element `s` is an sc-diffeomorphism
`U → N` carrying `U ∩ M(Ψ, Ψ')*_{θ,θ'}` onto `N ∩ θ` (the retraction `R = (s|W(h₀))⁻¹ ∘ r ∘ s` of
(17.73)); `d_{M(Ψ, Ψ')} = d_O ∘ s ≥ 1` on it; and (17.71) `(x, Φ, x') ↦ (x, φ, x')` is a bijection
`M(Ψ_θ, Ψ'_{θ'}) → M(Ψ, Ψ')*_{θ,θ'}`. -/
theorem lemma_17_4_13_subMPolyfold {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    (S.transPolyfold Ψ Ψ').IsSubMPolyfold (V.transFaceSet hT V' hθ hθ') ∧
    (∃ 𝒪 : Set (S.Tr Ψ Ψ'), IsOpen 𝒪 ∧
      V.transFaceSet hT V' hθ hθ' = 𝒪 ∩ (fun b : S.Tr Ψ Ψ' => b.src) ⁻¹' θ) ∧
    (∀ a ∈ V.transFaceSet hT V' hθ hθ', ∃ (U : Set (S.Tr Ψ Ψ')) (N : Set Ψ.1.O)
      (g : Ψ.1.O → S.Tr Ψ Ψ'), a ∈ U ∧
      (S.transPolyfold Ψ Ψ').IsScDiffeoOn Ψ.1.P (fun b : S.Tr Ψ Ψ' => b.src) g U N ∧
      (fun b : S.Tr Ψ Ψ' => b.src) '' (U ∩ V.transFaceSet hT V' hθ hθ') = N ∩ θ) ∧
    (∀ a ∈ V.transFaceSet hT V' hθ hθ',
      (S.transPolyfold Ψ Ψ').degIndex a = Ψ.1.P.degIndex a.src ∧
        1 ≤ (S.transPolyfold Ψ Ψ').degIndex a) ∧
    Injective (V.faceTrToTr V' (hT := hT) (hS := hS) (hθ := hθ) (hθ' := hθ')) ∧
    range (V.faceTrToTr V' (hT := hT) (hS := hS) (hθ := hθ) (hθ' := hθ')) =
      V.transFaceSet hT V' hθ hθ' :=
  ⟨V.isSubMPolyfold_transFaceSet V' hθ hθ', V.exists_isOpen_inter_eq V' hθ hθ',
    fun _ ha => V.exists_sheet_transFaceSet V' hθ hθ' ha,
    fun a ha => ⟨degIndex_tr a, V.one_le_degIndex_of_mem_transFaceSet V' hθ hθ' ha⟩,
    V.faceTrToTr_injective V' hθ hθ', (V.definition_17_4_12 V' (hS := hS) hθ).2.2.2 hθ'⟩

end GoodNbhd

/-! ### Lemma 17.4.13 under Definition 2.5.19 -/

section NotLemma

open MPolyfold TameBoundaryExample

variable (W : ScBanach)

attribute [local instance] quadrantTrivialAction

/-- **2021 Lemma 17.4.13 (first assertion), with "tame sub-M-polyfold" taken literally** in the
sense of 2021 Definition 2.5.19 (2) (we read it in the sense of Definition 2.5.18,
`lemma_17_4_13`): for the quadrant polyfold
`[0,∞)² ⊕ W`, a good neighbourhood `U` of the corner and either face `θ` of `U`, the unit
`1_0 = (0, 1, 0)` lies in `M(Ψ, Ψ)*_{θ,θ}`, which is contained in `∂M(Ψ, Ψ)`, while `1_0` is a limit
of points of index `0`; a tame retraction (`d(r(x)) = d(x)`) onto it cannot exist. -/
theorem lemma_17_4_13_literal_quadrant :
    ∃ (hT : (quadrantConstruction W).IsTame)
      (V : (quadrantConstruction W).GoodNbhd (quadrantUnif W) (quadrantCorner W))
      (θ : Set (quadrantUnif W).1.O) (hθ : θ ∈ V.faces),
      ¬ ((quadrantConstruction W).transPolyfold (quadrantUnif W)
        (quadrantUnif W)).IsTameSubMPolyfold (V.transFaceSet hT V hθ hθ) := by
  obtain ⟨hT, -, -, -, -, V, hV⟩ := quadrant_tameBoundaryUniformizer_witness W
  have hne : V.faces.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h; rw [h, encard_empty] at hV; exact absurd hV (by decide)
  obtain ⟨θ, hθ⟩ := hne
  refine ⟨hT, V, θ, hθ, ?_⟩
  let a : (quadrantConstruction W).Tr (quadrantUnif W) (quadrantUnif W) :=
    (quadrantConstruction W).toTr (GroupoidStr.TransitionSet.unit (quadrantCorner W))
  have ho : quadrantCorner W ∈ θ := V.mem_of_mem_faces hθ
  have ha : a ∈ V.transFaceSet hT V hθ hθ :=
    ⟨ho, ho, germLift_unit (V.bMap_faceGerm hθ _ ho)⟩
  refine not_isTameSubMPolyfold_of_mem_closure
    (fun b hb => V.one_le_degIndex_of_mem_transFaceSet V hθ hθ hb) ha ?_
  exact ((quadrantConstruction W).isLocalScDiffeo_trSrc (quadrantUnif W)
    (quadrantUnif W)).mem_closure_degIndex_eq_zero
    (corner_mem_closure_dq_eq_zero (n := 2) (W := W))

/-- **2021 Lemma 17.4.13 with the pointer to Definition 2.5.19 taken literally**: not every
`M(Ψ, Ψ')*_{θ,θ'}` of a tame polyfold construction is a tame sub-M-polyfold of `M(Ψ, Ψ')` in the
sense of Definition 2.5.19 (2).  We read the faces in the sense of Definition 2.5.18
(`lemma_17_4_13`); under Definition 2.5.19 no face of positive codimension qualifies. -/
theorem lemma_17_4_13_literal :
    ¬ ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hT : S.IsTame) (Ψ Ψ' : S.Unif)
      (o : Ψ.1.O) (o' : Ψ'.1.O) (V : S.GoodNbhd Ψ o) (V' : S.GoodNbhd Ψ' o')
      (θ : Set Ψ.1.O) (θ' : Set Ψ'.1.O) (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces),
      (S.transPolyfold Ψ Ψ').IsTameSubMPolyfold (V.transFaceSet hT V' hθ hθ') := by
  intro h
  obtain ⟨hT, V, θ, hθ, hn⟩ := lemma_17_4_13_literal_quadrant (ScBanach.const (Fin 0 → ℝ))
  exact hn (h _ _ hT _ _ _ _ V V θ θ hθ hθ)

end NotLemma

end GCT.PolyfoldConstruction

end Polyfold
