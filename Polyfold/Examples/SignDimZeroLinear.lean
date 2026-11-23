import Polyfold.Chapter6.SolutionSetOrientation

/-!
# The orientation of a zero-dimensional kernel: the ray of the empty wedge

Linear algebra for the sign of an oriented sc-Fredholm section at a solution of dimension `0`
(Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory*, Springer 2021, §6.6, pp. 268–275, and
§15.4, pp. 701–702).

## What is formalized (namespace `Polyfold`)

* `emptyRay M h`: for a space `M` of dimension `0`, the ray of the empty wedge in `λ(M) = Λ⁰M`,
  the positive orientation of the point.
* `ray_map_maxPowEquiv_emptyRay`: `λ(Φ)` maps the ray of the empty wedge to the ray of the
  empty wedge, for a linear isomorphism `Φ`.
* `SubspaceFamily.emptyOr`, **`SubspaceFamily.cont_emptyRay`**: in a family of subspaces of rank
  `0` over a simply connected, locally path-connected base, the rays of the empty wedge form an
  orientation of `λ(L)`, so the continuation `Λ.cont a b` maps the ray of the empty wedge at `a`
  to the one at `b`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Module Bundle Topology Set

noncomputable section

namespace Polyfold

section EmptyRay

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M] [AddCommGroup N]
  [Module ℝ N] [FiniteDimensional ℝ N]

variable (M) in
/-- **The ray of the empty wedge** of a space of dimension `0`: the positive orientation of
`λ(M) = Λ⁰M`. -/
def emptyRay (h : finrank ℝ M = 0) : Module.Ray ℝ (maxPow M) :=
  rayOfNeZero ℝ (emptyWedge M h) (emptyWedge_ne_zero M h)

/-- `λ(Φ)` maps the empty wedge to the empty wedge. -/
theorem maxPowEquiv_emptyWedge (Φ : M ≃ₗ[ℝ] N) (h : finrank ℝ M = 0) (h' : finrank ℝ N = 0) :
    maxPowEquiv Φ (emptyWedge M h) = emptyWedge N h' := by
  unfold emptyWedge
  rw [maxPowEquiv_wedge]
  congr 1
  exact funext fun i => i.elim0

/-- **`λ(Φ)` maps the ray of the empty wedge to the ray of the empty wedge.** -/
theorem ray_map_maxPowEquiv_emptyRay (Φ : M ≃ₗ[ℝ] N) (h : finrank ℝ M = 0)
    (h' : finrank ℝ N = 0) :
    Module.Ray.map (maxPowEquiv Φ) (emptyRay M h) = emptyRay N h' := by
  unfold emptyRay
  rw [Module.Ray.map_apply]
  exact rayOfNeZero_congr (maxPowEquiv_emptyWedge Φ h h') _ _

/-- The wedge of a family indexed by `Fin k` with `k = 0` is the empty wedge. -/
theorem wedge_eq_emptyWedge {k : ℕ} (hk0 : k = 0) (v : Fin k → M) (hk : k = finrank ℝ M) :
    wedge v hk = emptyWedge M (hk.symm.trans hk0) := by
  subst hk0
  unfold emptyWedge
  congr 1
  exact funext fun i => i.elim0

end EmptyRay

namespace SubspaceFamily

variable {Q : Type*} [TopologicalSpace Q] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (Λ : SubspaceFamily Q W)

/-- The ray of the empty wedge of `λ(L_q)` in a family of rank `0`. -/
def emptyRayAt (hn : Λ.n = 0) (q : Q) : Module.Ray ℝ (Λ.det q) :=
  emptyRay (Λ.L q) ((Λ.finrank_eq q).trans hn)

/-- **The rays of the empty wedge are an orientation of `λ(L)`** in a family of rank `0`. -/
theorem isLineOrientation_emptyRayAt (hn : Λ.n = 0) :
    IsLineOrientation Λ.det (Λ.emptyRayAt hn) := by
  intro b₀
  refine ⟨(Λ.frameAt b₀).U, (Λ.frameAt b₀).isOpen.mem_nhds (Λ.mem_frameAt b₀),
    (Λ.frameAt b₀).wedgeAt, (Λ.frameAt b₀).continuousOn_wedgeAt, fun b hb => ?_⟩
  refine ⟨(Λ.frameAt b₀).wedgeAt_ne_zero hb, ?_⟩
  unfold emptyRayAt emptyRay
  exact rayOfNeZero_congr (((Λ.frameAt b₀).wedgeAt_of_mem hb).trans
    (wedge_eq_emptyWedge hn _ _)).symm _ _

/-- The orientation of `λ(L)` by the rays of the empty wedge, in a family of rank `0`. -/
def emptyOr (hn : Λ.n = 0) : LineOrientation Λ.det :=
  ⟨Λ.emptyRayAt hn, Λ.isLineOrientation_emptyRayAt hn⟩

/-- **Continuation in a family of rank `0` fixes the ray of the empty wedge.** -/
theorem cont_emptyRay [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q] (hn : Λ.n = 0)
    (a b : Q) : Λ.cont a b (Λ.emptyRayAt hn a) = Λ.emptyRayAt hn b :=
  Λ.cont_eq (Λ.emptyOr hn) a b

end SubspaceFamily

end Polyfold
