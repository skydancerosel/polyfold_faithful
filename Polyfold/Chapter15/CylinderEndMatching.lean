import Polyfold.Chapter15.CylinderEndBranching
import Polyfold.Chapter15.CylinderEndOrientationSign

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2), the step "`∂Θ̃ = Θ₁ ⊔ −Θ₀`" of its proof, with
Definitions 9.3.6, 9.3.8, 9.3.10.

# Matched oriented structures on the ends of the cylinder

## The text, paraphrased

Near `(i, x)`, `x ∈ supp Θᵢ`, the sheets `M̃ⱼ` of `Θ̃` have the boundaries `{i} × Mⱼ`, with `Mⱼ`
the sheets of `Θᵢ` near `x`, and the same weights.  With the canonical orientations, in which
the `[0, 1]`-direction comes first, the boundary orientation of `{i} × Mⱼ` is `(−1)^{i+1}` times
the orientation of `Mⱼ`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`areMatchedAt_of_equiv`**: oriented tame structures `C` at `x` and `C̃` at `(q, x)` with a
  bijection of the index sets, equal weights, `∂₁M̃ⱼ = {q} × M_{e j}`, `{q} × U ⊆ Ũ` and the
  sign clause are matched (`AreMatchedAt`).
* `areMatchedAt_of_equiv_timeFirst`: the same with the frame convention "`t` first" in place
  of the sign clause, with the sign `+1` at `t = 1` and `−1` at `t = 0`.
* `HasMatchedOrientations`: for a local branching structure `K̃` of `Θ̃` at `(q, x)` described by
  kernels and its slice structure `B` of `Θ` at `x`: all sheets of `K̃` have dimension `m + 2`,
  all sheets of `B` dimension `m + 1`, and there are orientations of the sheets that describe
  the given orientations `T̃` and `T` and satisfy the convention "`t` first".
* **`exists_areMatchedAt_of_orientations`**: if the matching structures of
  `exists_matched_branching_of_class` have such orientations, every point of `supp Θᵢ` has
  matched oriented structures with sign `(−1)^{i+1}`, the one of `Θᵢ` with sheets in the class
  of the integration: the hypothesis of `isLocalEndIdentity_of_matched`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

section Equiv

variable {m : ℕ} {Θ : A.Obj → ℚ} {x : A.Obj} {q : Fin 1 → unitInterval}
  (C : A.X.OrientedTameStructure (m + 1) Θ x) {Θ' : (A.cubeSEP 1).Obj → ℚ}
  {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
  (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' (q, x))
  (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ') (hCT' : C'.Represents T')
  (hS : ∀ i, C.M i ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets)

/-- If `∂₁M̃ⱼ = {q} × M_{e j}` for a bijection `e` of the index sets, every boundary sheet of
`C̃` is nonempty (it contains `(q, x)`). -/
theorem boundarySheet_nonempty_of_equiv (e : C'.ι ≃ C.ι)
    (hM : ∀ j, C'.boundarySheet j = (cubeFaceIncl A q).obj '' C.M (e j)) (j : C'.ι) :
    (C'.boundarySheet j).Nonempty := by
  rw [hM j]
  exact ⟨_, x, C.mem_M (e j), rfl⟩

/-- **Matched structures from a bijection of the index sets** (proof of Corollary 15.4.4,
p. 703): oriented tame structures `C` of `Θ` at `x` and `C̃` of `Θ̃` at `(q, x)` with a bijection
`e` of the index sets such that the weights agree, `∂₁M̃ⱼ = {q} × M_{e j}`, `{q} × U ⊆ Ũ`, and
the boundary orientation of `∂₁M̃ⱼ` is `ε` times the orientation of `M_{e j}` moved to the
slice. -/
theorem areMatchedAt_of_equiv (ε : ℝ) (e : C'.ι ≃ C.ι) (hσ : ∀ j, C'.σ j = C.σ (e j))
    (hM : ∀ j, C'.boundarySheet j = (cubeFaceIncl A q).obj '' C.M (e j))
    (hU : ∀ y ∈ C.U, (q, y) ∈ C'.U)
    (hε : (ε = 1 ∧ ∀ j, ∀ y ∈ C.M (e j),
        (C'.boundaryOrient j).tangent ((cubeFaceIncl A q).obj y) =
          (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent ((cubeFaceIncl A q).obj y)) ∨
      (ε = -1 ∧ ∀ j, ∀ y ∈ C.M (e j),
        (C'.boundaryOrient j).tangent ((cubeFaceIncl A q).obj y) ≠
          (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent ((cubeFaceIncl A q).obj y))) :
    AreMatchedAt q C C' hΘ' hCT' hS ε := by
  refine ⟨fun j => e j.1, fun a b h => Subtype.ext (e.injective h), fun i hi => ?_,
    fun j => hσ j.1, fun j => hM j.1, hU, ?_⟩
  · exact absurd ⟨⟨e.symm i, boundarySheet_nonempty_of_equiv C C' e hM _⟩,
      e.apply_symm_apply i⟩ hi
  · exact hε.imp (fun h => ⟨h.1, fun j => h.2 j.1⟩) (fun h => ⟨h.1, fun j => h.2 j.1⟩)

/-- **Matched structures from a bijection of the index sets and the convention "`t` first"**:
the sign is `+1` at `t = 1` and `−1` at `t = 0`. -/
theorem areMatchedAt_of_equiv_timeFirst {ε : ℝ}
    (hq : ((q 0 : ℝ) = 0 ∧ ε = -1) ∨ ((q 0 : ℝ) = 1 ∧ ε = 1)) (e : C'.ι ≃ C.ι)
    (hσ : ∀ j, C'.σ j = C.σ (e j))
    (hM : ∀ j, C'.boundarySheet j = (cubeFaceIncl A q).obj '' C.M (e j))
    (hU : ∀ y ∈ C.U, (q, y) ∈ C'.U)
    (hconv : HasTimeFirstFrames q C C' (fun j : C'.ι => j) e) :
    AreMatchedAt q C C' hΘ' hCT' hS ε := by
  have he : Injective fun j : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι => e j.1 :=
    fun a b h => Subtype.ext (e.injective h)
  have hrange : ∀ i, i ∉ range (fun j : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι => e j.1) →
      C.M i = ∅ := fun i hi =>
    absurd ⟨⟨e.symm i, boundarySheet_nonempty_of_equiv C C' e hM _⟩, e.apply_symm_apply i⟩ hi
  have hconv' : HasTimeFirstFrames q C C'
      (fun j : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι => j.1) (fun j => e j.1) :=
    fun j => hconv j.1
  rcases hq with ⟨hq, rfl⟩ | ⟨hq, rfl⟩
  · exact areMatchedAt_of_timeFirstFrames_zero C C' hΘ' hCT' hS hq _ he hrange
      (fun j => hσ j.1) (fun j => hM j.1) hU hconv'
  · exact areMatchedAt_of_timeFirstFrames_one C C' hΘ' hCT' hS hq _ he hrange
      (fun j => hσ j.1) (fun j => hM j.1) hU hconv'

end Equiv

/-! ### Orientations of the matching structures -/

/-- **Orientations of a matching pair** (Theorem 15.4.1 on `X` and on the cylinder, and the
convention of Remark 6.6.19): for a local branching structure `K̃` of `Θ̃` at `(q, x)` described
by kernels, a tame local branching structure `B` of `Θ` at `x` and a bijection `e` of the index
sets, the sheets of `K̃` have dimension `m + 2`, those of `B` dimension `m + 1`, and there are
orientations of the sheets such that the oriented structures describe `T̃` and `T` and satisfy
the convention "`t` first" along the slices. -/
def HasMatchedOrientations (m : ℕ) {f : A.Obj → A.W} (hsec : IsSection A.P f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ : A.W → ℚ≥0} (T : A.Obj → A.X.PObj.OrTangent →₀ ℚ)
    (T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ) (q : Fin 1 → unitInterval)
    {x : A.Obj} (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hsec) Λ' (q, x))
    (B : A.X.TameBranchingStructure (fun z => (Λ (f z) : ℚ)) x) (e : K'.ι ≃ B.ι) : Prop :=
  ∃ (hn' : ∀ j, (A.cubeSEP 1).X.PObj.IsSubmanifoldOfDim (K'.M j) (m + 1 + 1))
    (o' : ∀ j, (A.cubeSEP 1).X.PObj.SubmanifoldOrientation (K'.M j) (m + 1 + 1))
    (hn : ∀ j, A.X.PObj.IsSubmanifoldOfDim (B.M j) (m + 1))
    (o : ∀ j, A.X.PObj.SubmanifoldOrientation (B.M j) (m + 1)),
    (EpGroupoid.OrientedTameStructure.mk K'.toTameBranchingStructure hn' o').Represents T' ∧
      (EpGroupoid.OrientedTameStructure.mk B hn o).Represents T ∧
      HasTimeFirstFrames q (EpGroupoid.OrientedTameStructure.mk B hn o)
        (EpGroupoid.OrientedTameStructure.mk K'.toTameBranchingStructure hn' o')
        (fun j : K'.ι => j) e

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
/-- **Matched oriented structures at the points of `supp Θᵢ`** (proof of Corollary 15.4.4,
p. 703).  Let `d_X ≡ 0`, `f` sc-Fredholm with tame germ data, `P` an oriented regular
perturbation of `f`, `Λ̃` an sc⁺-multisection on `[0, 1] × X` with `Λ̃ = Λⁱ` over `t = i`,
`Λ̃ = Λ_P` over the end `i ∈ {0, 1}`, the face condition of Theorem 15.3.9 for the glued data,
and `ε = (−1)^{i+1}`.  If every pair `(K̃, B)` of a local branching structure of `Θ̃` at
`(i, x)` described by kernels and its slice structure of `Θ = Λ_P ∘ f` at `x` has orientations
describing `T̃` and `T_P` with the convention "`t` first" (`HasMatchedOrientations`), then every
`x ∈ supp Θ` has oriented tame structures `C` of `Θ` at `x`, with sheets in the class of the
integration and describing `T_P`, and `C̃` of `Θ̃` at `(i, x)` describing `T̃`, matched with
sign `ε`. -/
theorem exists_areMatchedAt_of_orientations (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {m : ℕ} (P : OrientedRegularPerturbation A f m)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {i : unitInterval} {ε : ℝ} (hi : ((i : ℝ) = 0 ∧ ε = -1) ∨ ((i : ℝ) = 1 ∧ ε = 1))
    (hΛi : ∀ w, ((cubeVal w).1.1 0 : ℝ) = i → Λ' w = P.Λ (cubeVal w).2)
    {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)))
    (hor : ∀ x, 0 < P.Λ (f x) → ∀ (K' : KernelBranching (A.cubeSEP 1)
        (cubeLiftEp (n := 1) f hf.1.1.1) Λ' ((fun _ => i), x))
      (B : A.X.TameBranchingStructure (fun z => (P.Λ (f z) : ℚ)) x) (e : K'.ι ≃ B.ι),
      (∀ j, K'.σ j = B.σ (e j)) →
      (∀ y, y ∈ B.U ↔ (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.U) →
      (∀ p ∈ K'.U, p ∈ (A.cubeSEP 1).X.PObj.boundary → p.1 = fun _ => i) →
      (∀ j, B.M (e j) = {y | (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.M j}) →
      (∀ j, (A.cubeSEP 1).X.PObj.boundaryStratum (K'.M j) =
        (cubeFaceIncl A (fun _ => i)).obj '' B.M (e j)) →
      (∀ j, A.X.PObj.IsSubmanifoldOfDim (B.M (e j)) (K'.dim j - 1)) →
      HasMatchedOrientations m hf.1.1.1 P.T T' (fun _ => i) K' B e) :
    ∀ x ∈ EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P.Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1)
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ((fun _ => i), x))
        (hCT' : C'.Represents T') (hS : ∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets),
        C.Represents P.T ∧ AreMatchedAt (fun _ => i) C C' hΘ' hCT' hS ε := by
  classical
  intro x hx
  have hpos : 0 < P.Λ (f x) := by
    have h : (0 : ℚ) < (P.Λ (f x) : ℚ) := hx
    exact_mod_cast h
  have hi' : (i : ℝ) = 0 ∨ (i : ℝ) = 1 := hi.imp (fun h => h.1) (fun h => h.1)
  -- the class of sheets: in dimension `m + 1`, the class of the integration
  let S : ℕ → Set (Set A.Obj) := fun d =>
    {N | d = m + 1 → N ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets}
  have hS₁ : ∀ d N, A.X.PObj.IsSubmanifoldOfDim N d → x ∈ N →
      ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ N ∩ V ∈ S d := fun d N hN hxN => by
    by_cases hdm : d = m + 1
    · subst hdm
      obtain ⟨V, hV, hxV, hNV⟩ :=
        EpGroupoid.FormEval.exists_mem_sheets (F := A.baseEP.epFormsInftyEval (m + 1)) hN hxN
      exact ⟨V, hV, hxV, fun _ => hNV⟩
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h => absurd h hdm⟩
  have hS₂ : ∀ d N V, N ∈ S d → IsOpen V → N ∩ V ∈ S d := fun d N V hN hV hdm =>
    EpGroupoid.FormEval.inter_mem_sheets (hN hdm) hV
  obtain ⟨K', B, e, hσ, hU, hKb, hM, hstr, hdim, hcls⟩ :=
    exists_matched_branching_of_class hd hf hft hΛ' h0 h1 honto hi' hΛi hpos S hS₁ hS₂
  obtain ⟨hn', o', hn, o, hT', hT, hconv⟩ := hor x hpos K' B e hσ hU hKb hM hstr hdim
  have hSh : ∀ j, B.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets := fun j => by
    obtain ⟨j', rfl⟩ := e.surjective j
    exact hcls j' (((hdim j').2 x (B.mem_M _)).unique ((hn (e j')).2 x (B.mem_M _)))
  refine ⟨EpGroupoid.OrientedTameStructure.mk B hn o,
    EpGroupoid.OrientedTameStructure.mk K'.toTameBranchingStructure hn' o', hT', hSh, hT, ?_⟩
  exact areMatchedAt_of_equiv_timeFirst _ _ hΘ' hT' hSh
    (hi.imp (fun h => ⟨h.1, h.2⟩) (fun h => ⟨h.1, h.2⟩)) e hσ hstr
    (fun y hy => (hU y).1 hy) hconv

end SBLocalization

end Polyfold
