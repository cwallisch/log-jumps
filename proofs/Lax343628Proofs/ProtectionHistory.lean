import Lax343628Proofs.ProtectionCrossings

namespace Lax343628Proofs.ProtectionHistory

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ColumnBlock Lax343628Proofs.ColumnBudget Lax343628Proofs.ProtectionWindows
open Lax343628Proofs.Trajectories Lax343628Proofs.FiniteEvents
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r R J ell : ℕ} {mu rs : ℕ+}

def failure (J k : ℕ) (i : Fin n) (u theta omega : ℝ) : Set (Fin (J + 1) → State n mu) :=
  {h | ∃ b t : Fin (J + 1), b ≤ t ∧ fraction i 0 (h b).1 < u ∧ theta ≤ fraction i 0 (h t).1 ∧
    (∀ j, j ≤ t → ∀ v, (Sampling.zeros ((h j).1 v)).card = k) ∧
    (∀ j, j ≤ t → cap omega (h j).1)}

lemma bound (hr : 1 ≤ r) (pc a u theta omega L : ℝ)
    (hu : 0 < u) (huquarter : u ≤ 1 / 4) (hutheta : u ≤ theta)
    (htheta : theta = 16 * (3 : ℝ) ^ (r + 1) * u) (hstep : 1 / (mu : ℕ) ≤ u) (i : Fin n)
    (hb : ∀ S : State n mu, S ∈ starts (r + 1) i u →
      Budget n (r + 1) R ell mu rs pc a
        (Odds.lowerMass (Odds.value i S.1 / (4 * (3 : ℝ) ^ (r + 1))))
        (Odds.upperMass (8 * Odds.value i S.1))
        (Odds.lowerMass (8 * Odds.value i S.1)) omega L 8)
    (p : PMF (State n mu)) :
    (pathLaw (driver (r + 1) pc) p J).toOuterMeasure (failure J (r + 1) i u theta omega) ≤
      ENNReal.ofReal (((J : ℝ) + 1) *
        ((4 * (Fintype.card (Net n (r + 1) R (count R ell) rs) : ℝ) *
          ((R : ℝ) + 1) + 1) * Real.exp (-L))) := by
  rw [← pathLaw_before (driver (r + 1) pc) p (J + R) J (Nat.le_add_right J R),
    PMF.toOuterMeasure_map_apply]
  apply le_trans _ (ProtectionWindows.union_bound hr pc a u omega L hu huquarter i hb p)
  apply event_mono_on_support
  intro h hh hbad
  obtain ⟨b, t, hbt, hb0, htbad, hplateau, hcap⟩ := hbad
  let b' : Fin (J + R + 1) := ⟨b.val, by have := b.isLt; omega⟩
  let t' : Fin (J + R + 1) := ⟨t.val, by have := t.isLt; omega⟩
  have hprev : ∃ c ≤ t', fraction i 0 (h c).1 < u :=
    ⟨b', Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hbt), hb0⟩
  have hpl (j : Fin (J + R + 1)) (hj : j ≤ t') : ∀ v, (Sampling.zeros ((h j).1 v)).card = r + 1 := by
    let j' : Fin (J + 1) := ⟨j.val, by have := Fin.le_iff_val_le_val.mp hj; have := t.isLt; dsimp [t'] at *; omega⟩
    exact hplateau j' (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hj))
  have hc (j : Fin (J + R + 1)) (hj : j ≤ t') : cap omega (h j).1 := by
    let j' : Fin (J + 1) := ⟨j.val, by have := Fin.le_iff_val_le_val.mp hj; have := t.isLt; dsimp [t'] at *; omega⟩
    exact hcap j' (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hj))
  apply ProtectionCrossings.charge_after i u theta omega hu huquarter hutheta htheta h _ t'
    (by have := t.isLt; dsimp [t']; omega) hprev htbad hpl hc
  intro s t hst
  have hs : s.val < J + R := by have := t.isLt; omega
  let q : Fin (J + R) := ⟨s.val, hs⟩
  have hsupp := path_step_support (driver (r + 1) pc) p h hh q
  have hse : q.castSucc = s := Fin.ext rfl
  have hte : q.succ = t := Fin.ext hst.symm
  rw [hse, hte] at hsupp
  obtain ⟨E, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hsupp
  have hpop : (h t).1 = TaggedDynamics.next (r + 1) (h s).1 E := (congrArg Prod.fst heq).symm
  rw [hpop]
  exact (RunBoundary.fraction_step (k := r + 1) (h s).1 E i 0).trans hstep

end
end Lax343628Proofs.ProtectionHistory
