import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_5

/-! Round trip for V7_5 (Definition 7.4: the local sc-diffeomorphism `φ̂` and the tangent `Tφ`).

The listed definitions are `EpGroupoid.Sheet`, `Sheet.hat`, `sheetAt`, `hat`, `tangentMor`; the
listed theorems are `Sheet.isScDiffeoOn_hat`, `exists_sheet`, `mem_sheetAt`, `isScDiffeoOn_hat`,
`hat_src` (one universe each), so `A` is the conjunction of their types, universes at `0`.

* `A → B`: **not proved.**  B (1)–(3) follow from `A` (`A_to_B_sheets` below: (1) from
  `exists_sheet`, (2) from `Sheet.isScDiffeoOn_hat` applied to the sheet assembled from B's data,
  (3) from `mem_sheetAt` and the definition of `hat`).  B (4)–(7) are claims about the tangent
  `Tφ = tangentMor φ` (that it is `Tφ̂(x)` on `T_xX`, a bijection `T_xX → T_yX`, a bounded linear
  isomorphism in charts, an sc-isomorphism for smooth `φ`); `A` contains **no theorem about
  `tangentMor`** at all (it is only defined, as `Tt ∘ (Ts|T_φ𝐗)⁻¹` via choice).  Proving them needs
  tangent-bundle facts the project does not have: injectivity of `Ts` on the fibre `T_φ𝐗` (the
  project's docstring defers it to Chapter 8), locality of `MPolyfold.tangentMap` (`Tf = Tg` on
  `T_xX` when `f = g` near `x`), the identification `T_xU ≅ T_xX` for the open-subset
  M-polyfold `restrictOpen`, and linearity of chart representations of tangent maps.  We believe
  (4)–(7) hold for the project's `tangentMor` (with `φ ∈ 𝐗₁`, `Ts|T_φ𝐗` is a bijection onto
  `T_{sφ}X` since `s` is a local sc-diffeomorphism, so `tangentMor φ = T(t ∘ σ)` there), so this is
  proof effort, but substantial.
* `B → A`: `exists_sheet` is B (1); `Sheet.isScDiffeoOn_hat` is B (2) for sheets with a point
  (a sheet with empty carrier has `U(x) = U(y) = ∅`, where the claim is trivial); `mem_sheetAt` is
  `Exists.choose_spec` of B's existence proof (proof irrelevance identifies it with the project's
  `sheetAt`); `isScDiffeoOn_hat`, `hat_src` follow. -/

namespace RoundTrip.V7_5
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.Sheet.isScDiffeoOn_hat.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.exists_sheet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.mem_sheetAt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScDiffeoOn_hat.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.hat_src.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.Sheet.isScDiffeoOn_hat.{0}, @Polyfold.EpGroupoid.exists_sheet.{0},
    @Polyfold.EpGroupoid.mem_sheetAt.{0}, @Polyfold.EpGroupoid.isScDiffeoOn_hat.{0},
    @Polyfold.EpGroupoid.hat_src.{0}⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- A project sheet containing `φ` is a sheet at `φ` in B's sense. -/
theorem isSheetAtB_of (S : X.Sheet) {φ : Mor} (hφ : φ ∈ S.carrier) :
    IsSheetAtB X φ S.carrier S.srcSet S.tgtSet S.srcInv S.tgtInv :=
  ⟨S.isScDiffeoOn_src.isScSmoothOn.isOpen, S.isScDiffeoOn_src.isScSmoothOn_inv.isOpen,
    S.isScDiffeoOn_tgt.isScSmoothOn_inv.isOpen, hφ, S.isScDiffeoOn_src, S.isScDiffeoOn_tgt⟩

/-- B's sheet data as a project sheet. -/
def sheetOf {φ : Mor} {W : Set Mor} {Ux Uy : Set Obj} {σ τ : Obj → Mor}
    (h : IsSheetAtB X φ W Ux Uy σ τ) : X.Sheet :=
  ⟨W, Ux, Uy, σ, τ, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- An sc-diffeomorphism between empty sets. -/
theorem isScDiffeoOn_empty (P : MPolyfold Obj) (f g : Obj → Obj) : P.IsScDiffeoOn P f g ∅ ∅ :=
  ⟨(MPolyfold.isScSmoothMap_id.mono isOpen_empty (empty_subset _)).congr fun _ h => h.elim,
    (MPolyfold.isScSmoothMap_id.mono isOpen_empty (empty_subset _)).congr fun _ h => h.elim,
    mapsTo_empty _ _, mapsTo_empty _ _, fun _ h => h.elim, fun _ h => h.elim⟩

end

/-! ### `A → B`, the part that holds: (1)–(3) -/

theorem A_to_B_sheets (hA : A) (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) :
    (∀ φ : Mor, ∃ (W : Set Mor) (Ux Uy : Set Obj) (σ τ : Obj → Mor),
      IsSheetAtB X φ W Ux Uy σ τ) ∧
    (∀ (φ : Mor) (W : Set Mor) (Ux Uy : Set Obj) (σ τ : Obj → Mor),
      IsSheetAtB X φ W Ux Uy σ τ →
        X.src φ ∈ Ux ∧ X.tgt φ ∈ Uy ∧ X.tgt (σ (X.src φ)) = X.tgt φ ∧
        X.PObj.IsScDiffeoOn X.PObj (fun z => X.tgt (σ z)) (fun z => X.src (τ z)) Ux Uy) ∧
    (∀ φ : Mor, ∃ (W : Set Mor) (Ux Uy : Set Obj) (σ τ : Obj → Mor),
      IsSheetAtB X φ W Ux Uy σ τ ∧ Set.EqOn (X.hat φ) (fun z => X.tgt (σ z)) Ux) := by
  refine ⟨fun φ => ?_, fun φ W Ux Uy σ τ h => ?_, fun φ => ?_⟩
  · obtain ⟨S, hS⟩ := hA.2.1 X φ
    exact ⟨_, _, _, _, _, isSheetAtB_of X S hS⟩
  · have hd := hA.1 (sheetOf X h)
    refine ⟨h.2.2.2.2.1.mapsTo h.2.2.2.1, h.2.2.2.2.2.mapsTo h.2.2.2.1, ?_, hd⟩
    rw [h.2.2.2.2.1.left_inv φ h.2.2.2.1]
  · exact ⟨_, _, _, _, _, isSheetAtB_of X (X.sheetAt φ) (hA.2.2.1 X φ), fun _ _ => rfl⟩

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  intro hB
  -- every morphism lies in a project sheet, from B (1)
  have hex : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (φ : Mor), ∃ S : X.Sheet, φ ∈ S.carrier := by
    intro Obj Mor _ _ _ _ _ _ X φ
    obtain ⟨W, Ux, Uy, σ, τ, h⟩ := (hB Obj Mor X).1 φ
    exact ⟨sheetOf X h, h.2.2.2.1⟩
  have hmem : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (φ : Mor), φ ∈ (X.sheetAt φ).carrier := fun X φ => (hex X φ).choose_spec
  -- `φ̂` of every sheet is an sc-diffeomorphism, from B (2)
  have hhat : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
      (S : X.Sheet), X.PObj.IsScDiffeoOn X.PObj S.hat (fun z => X.src (S.tgtInv z)) S.srcSet
        S.tgtSet := by
    intro Obj Mor _ _ _ _ _ _ X S
    by_cases hne : S.carrier.Nonempty
    · obtain ⟨φ, hφ⟩ := hne
      exact ((hB Obj Mor X).2.1 φ _ _ _ _ _ (isSheetAtB_of X S hφ)).2.2.2
    · have hc : S.carrier = ∅ := not_nonempty_iff_eq_empty.1 hne
      have h1 : S.srcSet = ∅ := eq_empty_of_forall_notMem fun y hy => by
        have := S.isScDiffeoOn_src.mapsTo_inv hy
        rw [hc] at this; exact this
      have h2 : S.tgtSet = ∅ := eq_empty_of_forall_notMem fun y hy => by
        have := S.isScDiffeoOn_tgt.mapsTo_inv hy
        rw [hc] at this; exact this
      rw [h1, h2]
      exact isScDiffeoOn_empty X.PObj _ _
  refine ⟨fun S => hhat S, fun X φ => hex X φ, fun X φ => hmem X φ, fun X φ => hhat _,
    fun {Obj Mor} _ _ _ _ _ _ X φ => ?_⟩
  change X.tgt ((X.sheetAt φ).srcInv (X.src φ)) = X.tgt φ
  rw [(X.sheetAt φ).isScDiffeoOn_src.left_inv φ (hmem X φ)]

/-! ### The no-peeking check

`#rt_check` cannot pass for any proof about this item: the *definition* `sheetAt` (vocabulary of
`A`'s own statement: `mem_sheetAt`, `isScDiffeoOn_hat`, `hat_src` mention it) is
`sheetAt φ := (exists_sheet φ).choose`, so the banned `exists_sheet` is reached through the body of
a definition that every statement of `A` (and `B`, through `hat`) contains.  Lean did not
abstract this proof argument into a `sheetAt._proof_N`, so `#rt_check_soft` does not exempt it
either.  `#rt_check_opaque` below is `#rt_check` (same traversal as `RoundTrip.Check`'s
`rtCollect`) except that the *value* of each listed definition is not followed (its type is); it
confirms that `B_to_A` reaches no banned theorem other than through `sheetAt := choose
(exists_sheet …)`.  (`B_to_A` proves `mem_sheetAt` as `Exists.choose_spec` of its own existence
proof from B (1), identified with `exists_sheet φ` by proof irrelevance.) -/

open Lean Elab Command in
/-- `rtCollect`, except that the values of the constants in `opq` are not traversed. -/
partial def rtCollectOpaque (env : Environment) (opq : List Name) (todo : List Name)
    (seen : NameSet) : NameSet := Id.run do
  let mut todo := todo
  let mut seen := seen
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      let inProject := match env.getModuleIdxFor? n with
        | none => true
        | some i =>
          let m := env.header.moduleNames[i.toNat]!
          (`Polyfold).isPrefixOf m || (`RoundTrip).isPrefixOf m
      unless inProject do continue
      let vals := if opq.contains n then #[] else ((rtValue? ci).map (·.getUsedConstants)).getD #[]
      todo := (ci.type.getUsedConstants ++ vals).toList ++ todo
  return seen

open Lean Elab Command in
elab "#rt_check_opaque " t:ident " [" bs:ident,* "]" " opaque " " [" os:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let opq := os.getElems.toList.map (·.getId)
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let used := rtCollectOpaque env opq roots.toList {}
  if used.contains ``sorryAx then throwError "rt_check_opaque FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  if bad.isEmpty then
    logInfo m!"rt_check_opaque OK: {t.getId} avoids the banned declarations (values of {opq} not followed)"
  else throwError "rt_check_opaque FAIL: {t.getId} uses {bad}"

#rt_check_opaque RoundTrip.V7_5.B_to_A [Polyfold.EpGroupoid.Sheet.isScDiffeoOn_hat, Polyfold.EpGroupoid.exists_sheet, Polyfold.EpGroupoid.mem_sheetAt, Polyfold.EpGroupoid.isScDiffeoOn_hat, Polyfold.EpGroupoid.hat_src] opaque [Polyfold.EpGroupoid.sheetAt]
#rt_check_opaque RoundTrip.V7_5.A_to_B_sheets [Polyfold.EpGroupoid.Sheet.isScDiffeoOn_hat, Polyfold.EpGroupoid.exists_sheet, Polyfold.EpGroupoid.mem_sheetAt, Polyfold.EpGroupoid.isScDiffeoOn_hat, Polyfold.EpGroupoid.hat_src] opaque [Polyfold.EpGroupoid.sheetAt]
#rt_overlap RoundTrip.V7_5.B_to_A [Polyfold.EpGroupoid.Sheet.isScDiffeoOn_hat, Polyfold.EpGroupoid.exists_sheet, Polyfold.EpGroupoid.mem_sheetAt, Polyfold.EpGroupoid.isScDiffeoOn_hat, Polyfold.EpGroupoid.hat_src]

end RoundTrip.V7_5
