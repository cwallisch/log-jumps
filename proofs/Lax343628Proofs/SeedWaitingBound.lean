import Lax343628Proofs.SeedCount
import Lax343628Proofs.SeedWait

namespace Lax343628Proofs.SeedWaitingBound

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.SeedGeometry
open Lax343628Proofs.ColumnKernels Lax343628Proofs.SeedIdeal Lax343628Proofs.SeedMutation
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteComparison
open Lax343628Proofs.Deletion Lax343628Proofs.TaggedDynamics Lax343628Proofs.PlateauDynamics
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+} {i : Fin n}

lemma bound (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n) (pc : ℝ) (hpc : 0 < pc ∧ pc ≤ 1)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r)
    (M : ℕ) (theta : ℝ) (htheta : 0 ≤ theta) (A : Set (Population n mu))
    (hplateau : ∀ P ∈ A, ∀ u, (zeros (P u)).card = r + 1)
    (hcount : ∀ P ∈ A, SeedCount.count (r := r) C i P < M)
    (hflat : ∀ P ∈ A, ∀ j, j ∉ C → ClassChannels.fraction j 0 P ≤ theta)
    (hrho : ∀ P ∈ A, rho C P ≤ 1 / 4)
    (hcost : ∀ P ∈ A,
      2 * (r + 1 : ℝ) * theta + 2 * rho C P + 256 * (r + 1 : ℝ) ^ 2 / n + 1 / n ≤
        Real.exp (-1) / (64 * (r + 1 : ℝ) ^ 2))
    (hmutation : (r + 1 : ℝ) / n ≤ pc * Real.exp (-1) / (128 * (r + 1 : ℝ) ^ 2))
    (p : PMF (Population n mu)) :
    (∑' t, (law (stopped (auxiliaryStep (r + 1) pc) A) p t).toOuterMeasure A) ≤
      ENNReal.ofReal ((M : ℝ) / (pc * (1 / 4 : ℝ) ^ (r + 1) / (64 * n)) +
        (mu : ℕ) * M / (pc * Real.exp (-1) / (256 * (r + 1 : ℝ) ^ 2))) := by
  let ψ := liftClass (familyClass (r := r) (i := i) C)
  let X : Population n mu → ℝ := total ψ
  let beta := pc * Real.exp (-1) / (256 * (r + 1 : ℝ) ^ 2)
  let root := pc * (1 / 4 : ℝ) ^ (r + 1) / (64 * n)
  have hmupos : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hpc' : 0 ≤ pc ∧ pc ≤ 1 := ⟨hpc.1.le, hpc.2⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpcpos := hpc.1
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hroot : 0 < root := by dsimp [root]; positivity
  have hkn : r + 1 ≤ n := by omega
  have hpP (P : Population n mu) (hP : P ∈ A) : plateauPopulation (r + 1) P :=
    fun u ↦ PlateauKernelApproximation.plateau_of_zero_card hkn _ (hplateau P hP u)
  have hmean (P : Population n mu) (hP : P ∈ A) :
      mean (auxiliaryStep (r + 1) pc P) (fun Q ↦ X Q - X P) =
        mean (eventLaw pc P) (ClassIncrements.change (r + 1) ψ P) := by
    rw [← eventLaw_next hkn pc P (hpP P hP), mean_map]
    rfl
  apply SeedWait.runtime_from_drift (auxiliaryStep (r + 1) pc) A X M (mu : ℕ) beta root
    (by positivity) hmupos hbeta hroot (SeedCount.total_nonneg C) (fun P _ ↦ SeedCount.total_discrete C P)
  · intro P hP
    change total ψ P ≤ M
    rw [SeedCount.total_eq]
    exact_mod_cast (hcount P hP).le
  · intro P hP Q hQ
    rw [← eventLaw_next hkn pc P (hpP P hP)] at hQ
    obtain ⟨E, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hQ
    exact SeedCount.next_le C M P (hcount P hP) E
  · intro P hP hz
    have hphi : phi C i P = 0 := by
      have heq := SeedCount.total_phi (i := i) C P (hplateau P hP)
      change total ψ P = 0 at hz
      change total ψ P = (mu : ℕ) * phi C i P at heq
      rw [hz] at heq
      exact (mul_eq_zero.mp heq.symm).resolve_left (ne_of_gt hmupos)
    rw [hmean P hP]
    exact SeedFounding.zero_drift (by omega) (by omega) pc hpc' C hi P (hplateau P hP) (hrho P hP) hphi
  · intro P hP _
    rw [hmean P hP]
    have hd := SeedDrift.family_drift hr hn pc hpc' C hi hC P (hplateau P hP)
      theta htheta (hflat P hP) (hrho P hP) (hcost P hP) hmutation
    change phi C i P * beta ≤ _ at hd
    apply le_trans _ hd
    apply le_of_eq
    dsimp [X]
    rw [SeedCount.total_phi C P (hplateau P hP)]
    field_simp

end
end Lax343628Proofs.SeedWaitingBound
