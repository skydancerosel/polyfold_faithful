import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_18

/-! Round trip for V2_18 (Definition 2.17: tangent vectors in a chart, the equivalence `∼`).

`A` is the conjunction of the types of the listed theorems
`Polyfold.MPolyfold.TangentPre.transport_self`, `.transport_mem`, `.transport_transport`,
`.Rel.symm`, `.Rel.trans`, all instantiated at universe `0` (B lives in `Type`).  `TangentPre`,
`transport`, `Rel` and `setoid` are definitions (vocabulary), compared with B's notions below.

Comparison of the definitions:
* `T_xO`: the project's `tangentSpace E C O x₁ = {h | (x₁, h) ∈ TO}` is B's `TxOB R x₁` and the range
  of `Dr(x₁)` (`TOB_eq : TOB R = R.tangent`, then `retractTangent_eq`,
  `mem_tangent_iff_mem_range`).
* Tuples: the fields of `TangentPre` (`x ∈ X₁`, `φ` a chart around `x`,
  `(φ(x), h) ∈ TO`) are B's `IsTupleB` (`isTupleB_iff`).
* `∼`: the project's `Rel p q` is `T(ψ ∘ φ⁻¹)(φ(x), h) = (ψ(x), h')` (vector of `p` moved to the
  chart of `q`); B's `RelB p q` is the text's `T(φ ∘ ψ⁻¹)(ψ(x)) h' = h` (vector of `q` moved to
  the chart of `p`, derivative component only).  `relB_iff : RelB p q ↔ Rel q p` (the base-point
  component is automatic, `transport_fst`); so `Rel ↔ RelB` is exactly the symmetry of `Rel`. -/

namespace RoundTrip.V2_18
open Polyfold Set MPolyfold

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.TangentPre.transport_self.{0}) ∧
    (type_of% @Polyfold.MPolyfold.TangentPre.transport_mem.{0}) ∧
    (type_of% @Polyfold.MPolyfold.TangentPre.transport_transport.{0}) ∧
    (type_of% @Polyfold.MPolyfold.TangentPre.Rel.symm.{0}) ∧
    (type_of% @Polyfold.MPolyfold.TangentPre.Rel.trans.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.TangentPre.transport_self.{0},
    @Polyfold.MPolyfold.TangentPre.transport_mem.{0},
    @Polyfold.MPolyfold.TangentPre.transport_transport.{0},
    @Polyfold.MPolyfold.TangentPre.Rel.symm.{0}, @Polyfold.MPolyfold.TangentPre.Rel.trans.{0}⟩

section Glue

/-- B's `TO = {(r(x), Dr(x)h)}` is the project's `Tr(TU)`. -/
theorem TOB_eq {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C) : TOB R = R.tangent := by
  ext p
  rw [R.mem_tangent_iff_exists]
  constructor
  · rintro ⟨x₁, hx₁, h, h1, h2⟩
    refine ⟨x₁, hx₁, h, Prod.ext ?_ h2⟩
    apply E.toBase_injective 1
    change E.toBase 1 p.1 = E.toBase 1 (levelMap R.toFun 1 x₁)
    rw [R.isSc1.isSc0.toBase_levelMap (m := 1) (x := x₁) hx₁]; exact h1
  · rintro ⟨x, hx, h, rfl⟩
    exact ⟨x, hx, h, R.isSc1.isSc0.toBase_levelMap hx, rfl⟩

theorem mem_TxOB_iff {E : ScBanach} {C O : Set (E 0)} (R : ScRetraction E C) (hR : R.retract = O)
    (x₁ : E 1) (h : E 0) :
    h ∈ TxOB R x₁ ↔ ((x₁, h) : E.tangent 0) ∈ retractTangent E C O := by
  change ((x₁, h) : E.tangent 0) ∈ TOB R ↔ _
  rw [TOB_eq, ← hR, retractTangent_eq]

/-- The first part of B (no M-polyfold). -/
theorem part1 (E : ScBanach) (C O : Set (E 0)) (_ : IsScRetract E C O) (x₁ : E 1)
    (hx₁ : E.toBase 1 x₁ ∈ O) (R : ScRetraction E C) (hR : R.retract = O) :
    tangentSpace E C O x₁ = TxOB R x₁ ∧ TxOB R x₁ = range (scDeriv R.U R.toFun x₁) := by
  have h1 : tangentSpace E C O x₁ = TxOB R x₁ := by
    ext h; exact (mem_TxOB_iff R hR x₁ h).symm
  refine ⟨h1, ?_⟩
  rw [← h1, ← hR]
  exact tangentSpace_eq_range R (by rw [ScBanach.mem_lvlSet, hR]; exact hx₁)

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

theorem levelSetB_eq (P' : MPolyfold X) (m : ℕ) : levelSetB P' m = P'.levelSet m := by
  ext x
  constructor
  · rintro ⟨φ, hφ, hx, z, -, hz⟩
    exact ⟨φ, hφ, hx, z, hz⟩
  · rintro ⟨φ, hφ, hx, z, hz⟩
    refine ⟨φ, hφ, hx, z, ?_, hz⟩
    rw [ScBanach.mem_lvlSet, hz]; exact φ.mapsTo_model x hx

theorem isTupleB_of (p : P.TangentPre) : IsTupleB P p.x p.φ p.h := by
  refine ⟨by rw [levelSetB_eq]; exact p.mem_level, p.isChart, p.mem_source,
    levelLift p.φ 1 p.x, P.toBase_levelLift p.isChart p.mem_source p.mem_level, ?_⟩
  intro R hR
  exact (mem_TxOB_iff R hR _ _).2 p.mem_tangent

theorem exists_of_isTupleB (x : X) (φ : MChart X) (h : φ.model.E 0) (ht : IsTupleB P x φ h) :
    ∃ p : P.TangentPre, p.x = x ∧ p.φ = φ ∧ HEq p.h h := by
  obtain ⟨hlev, hφ, hx, x₁, hx₁, hall⟩ := ht
  rw [levelSetB_eq] at hlev
  have hlift : levelLift φ 1 x = x₁ := by
    apply φ.model.E.toBase_injective 1
    rw [P.toBase_levelLift hφ hx hlev, hx₁]
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  have hmem : ((levelLift φ 1 x, h) : φ.model.E.tangent 0) ∈
      retractTangent φ.model.E φ.model.C φ.model.O := by
    rw [hlift]; exact (mem_TxOB_iff R hR x₁ h).1 (hall R hR)
  exact ⟨⟨x, φ, h, hφ, hx, hlev, hmem⟩, rfl, rfl, HEq.rfl⟩

/-- B's relation `RelB p q` is the project's `Rel q p`. -/
theorem relB_iff (p q : P.TangentPre) : RelB p q ↔ q.Rel p := by
  have hcomp (hx : p.x = q.x) := (q.isChart.compatible p.isChart (P := P)).1
  have hmem (hx : p.x = q.x) : q.vec ∈
      retractTangent q.φ.model.E q.φ.model.C (q.φ.overlap p.φ) :=
    q.vec_mem_image inter_subset_left (q.φ.isOpen_source.inter p.φ.isOpen_source)
      ⟨q.mem_source, hx ▸ p.mem_source⟩
  constructor
  · rintro ⟨hx, R, hR, y₁, hy₁, hD⟩
    refine ⟨hx.symm, ?_⟩
    have hy : q.vec.1 = y₁ := by
      apply q.φ.model.E.toBase_injective 1
      rw [q.toBase_vec_fst, hy₁]
    refine Prod.ext ?_ ?_
    · rw [q.transport_fst p.isChart (hx ▸ p.mem_source), ← hx]; rfl
    · change (retractTangentMap _ _ (q.φ.overlap p.φ) (q.φ.transition p.φ) q.vec).2 = p.h
      rw [retractTangentMap_apply (hcomp hx) R hR (hmem hx)]
      change scDeriv R.U (q.φ.transition p.φ ∘ R) q.vec.1 q.h = p.h
      rw [hy]; exact hD
  · rintro ⟨hx, hT⟩
    obtain ⟨R, hR⟩ := q.φ.isScRetract_overlap p.φ
    refine ⟨hx.symm, R, hR, levelLift q.φ 1 q.x, q.toBase_vec_fst, ?_⟩
    have := congrArg Prod.snd hT
    change (retractTangentMap _ _ (q.φ.overlap p.φ) (q.φ.transition p.φ) q.vec).2 = p.h at this
    rw [retractTangentMap_apply (hcomp hx.symm) R hR (hmem hx.symm)] at this
    exact this

/-- `Tf` maps `TO` into `TO'` (re-proved, Proposition 2.6 (3)). -/
theorem transport_mem' (p : P.TangentPre) {ψ : MChart X} (hψ : P.IsChart ψ)
    (hx : p.x ∈ ψ.source) : p.transport ψ ∈ retractTangent ψ.model.E ψ.model.C ψ.model.O := by
  have h := (p.isChart.compatible hψ (P := P)).1.tangentMap_mapsTo (p.φ.isScRetract_overlap ψ)
    (ψ.isScRetract_overlap p.φ)
    (p.vec_mem_image inter_subset_left (p.φ.isOpen_source.inter ψ.isOpen_source)
      ⟨p.mem_source, hx⟩)
  exact (TangentPre.mem_retractTangent_image_iff inter_subset_left
    (ψ.isOpen_source.inter p.φ.isOpen_source)
    (retractTangent_fst_mem (ψ.isScRetract_overlap p.φ) h)).1 h

/-- The tuple `(x, ψ, h')` with `(ψ(x), h') = T(ψ ∘ φ⁻¹)(φ(x), h)`. -/
noncomputable def moved (p : P.TangentPre) {ψ : MChart X} (hψ : P.IsChart ψ) (hx : p.x ∈ ψ.source) :
    P.TangentPre where
  x := p.x
  φ := ψ
  h := (p.transport ψ).2
  isChart := hψ
  mem_source := hx
  mem_level := p.mem_level
  mem_tangent := by
    have h := transport_mem' p hψ hx
    rw [← p.transport_fst hψ hx]
    exact h

theorem moved_vec (p : P.TangentPre) {ψ : MChart X} (hψ : P.IsChart ψ) (hx : p.x ∈ ψ.source) :
    (moved p hψ hx).vec = p.transport ψ :=
  Prod.ext (p.transport_fst hψ hx).symm rfl

theorem rel_moved (p : P.TangentPre) {ψ : MChart X} (hψ : P.IsChart ψ) (hx : p.x ∈ ψ.source) :
    p.Rel (moved p hψ hx) :=
  ⟨rfl, (moved_vec p hψ hx).symm⟩

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hself, -, -, hsymm, htrans⟩
  refine ⟨part1, ?_⟩
  intro X _ _ _ P
  have hiff : ∀ p q : P.TangentPre, p.Rel q ↔ RelB p q := fun p q => by
    rw [relB_iff]; exact ⟨hsymm, hsymm⟩
  refine ⟨isTupleB_of, exists_of_isTupleB, hiff, ?_⟩
  refine ⟨fun p => (hiff p p).1 ⟨rfl, hself p⟩, fun {p q} h => ?_, fun {p q r} h₁ h₂ => ?_⟩
  · exact (relB_iff q p).2 (hsymm ((relB_iff p q).1 h))
  · exact (relB_iff p r).2 (htrans ((relB_iff q r).1 h₂) ((relB_iff p q).1 h₁))

theorem B_to_A : B → A := by
  intro hB
  -- the project's relation is an equivalence, from B
  have hrel : ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
      {P : MPolyfold X}, Equivalence (fun p q : P.TangentPre => p.Rel q) := by
    intro X _ _ _ P
    obtain ⟨-, -, hiff, heq⟩ := hB.2 X P
    exact ⟨fun p => (hiff p p).2 (heq.refl p),
      fun h => (hiff _ _).2 (heq.symm ((hiff _ _).1 h)),
      fun h₁ h₂ => (hiff _ _).2 (heq.trans ((hiff _ _).1 h₁) ((hiff _ _).1 h₂))⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ _ P p
    exact (hrel.refl p).2
  · intro X _ _ _ P p ψ hψ hx
    exact transport_mem' p hψ hx
  · intro X _ _ _ P p ψ χ hψ hχ hxψ hxχ
    -- `q = (x, ψ, ·)` and `r = (x, χ, ·)` are both equivalent to `p`, hence to each other
    have h1 := rel_moved p hψ hxψ
    have h2 := rel_moved p hχ hxχ
    have h3 : (moved p hψ hxψ).Rel (moved p hχ hxχ) := hrel.trans (hrel.symm h1) h2
    have h4 := h3.2
    rw [moved_vec] at h4
    rw [← h4, ← moved_vec p hψ hxψ]
    rfl
  · intro X _ _ _ P p q h
    exact hrel.symm h
  · intro X _ _ _ P p q r h₁ h₂
    exact hrel.trans h₁ h₂

#rt_check RoundTrip.V2_18.A_to_B [Polyfold.MPolyfold.TangentPre.transport_self,
  Polyfold.MPolyfold.TangentPre.transport_mem, Polyfold.MPolyfold.TangentPre.transport_transport,
  Polyfold.MPolyfold.TangentPre.Rel.symm, Polyfold.MPolyfold.TangentPre.Rel.trans]
#rt_check RoundTrip.V2_18.B_to_A [Polyfold.MPolyfold.TangentPre.transport_self,
  Polyfold.MPolyfold.TangentPre.transport_mem, Polyfold.MPolyfold.TangentPre.transport_transport,
  Polyfold.MPolyfold.TangentPre.Rel.symm, Polyfold.MPolyfold.TangentPre.Rel.trans]
#rt_overlap RoundTrip.V2_18.B_to_A [Polyfold.MPolyfold.TangentPre.transport_self,
  Polyfold.MPolyfold.TangentPre.transport_mem, Polyfold.MPolyfold.TangentPre.transport_transport,
  Polyfold.MPolyfold.TangentPre.Rel.symm, Polyfold.MPolyfold.TangentPre.Rel.trans]

end RoundTrip.V2_18
