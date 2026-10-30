import Lax343628Proofs.ProtectionWindows

namespace Lax343628Proofs.ProtectionCrossings

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ColumnBlock Lax343628Proofs.ProtectionWindows Lax343628Proofs.PathWindows
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R J : ℕ} {mu : ℕ+}

lemma charge_after (i : Fin n) (u theta omega : ℝ) (hu : 0 < u) (huquarter : u ≤ 1 / 4)
    (hutheta : u ≤ theta) (htheta : theta = 16 * (3 : ℝ) ^ k * u)
    (h : Fin (J + R + 1) → State n mu)
    (hstep : ∀ s t : Fin (J + R + 1), t.val = s.val + 1 →
      |fraction i 0 (h t).1 - fraction i 0 (h s).1| ≤ u)
    (t : Fin (J + R + 1)) (htJ : t.val ≤ J)
    (hprevious : ∃ b ≤ t, fraction i 0 (h b).1 < u)
    (hbad : theta ≤ fraction i 0 (h t).1)
    (hplateau : ∀ j, j ≤ t → ∀ v, (Sampling.zeros ((h j).1 v)).card = k)
    (hcap : ∀ j, j ≤ t → cap omega (h j).1) :
    ∃ c : Fin (J + 1), h ∈ windowFailure J R k i u omega c := by
  have htA : h t ∈ {S : State n mu | u ≤ fraction i 0 S.1} := hutheta.trans hbad
  have hprev : ∃ j ≤ t, h j ∉ {S : State n mu | u ≤ fraction i 0 S.1} := by
    obtain ⟨b, hbt, hb⟩ := hprevious
    exact ⟨b, hbt, not_le_of_gt hb⟩
  obtain ⟨s, hst, hs, hbetween⟩ := LastExit.last_outside h
    {S : State n mu | u ≤ fraction i 0 S.1} t htA hprev
  let c : Fin (J + 1) := ⟨s.val + 1, by have hh := Fin.lt_def.mp hst; omega⟩
  let c' : Fin (J + R + 1) := ⟨c.val, by have := c.isLt; omega⟩
  have hsltc : s < c' := Fin.lt_def.mpr (by dsimp [c', c]; omega)
  have hct : c' ≤ t := Fin.le_iff_val_le_val.mpr (by have := Fin.lt_def.mp hst; dsimp [c', c]; omega)
  have hcband : u ≤ fraction i 0 (h c').1 := hbetween c' hsltc hct
  have hcupper : fraction i 0 (h c').1 ≤ 2 * u := by
    have hstep' := (abs_le.mp (hstep s c' rfl)).2
    have hs' : fraction i 0 (h s).1 < u := lt_of_not_ge hs
    linarith
  let w := window (J + R) R c.val (by have := c.isLt; omega) h
  have hw0 : w 0 = h c' := rfl
  have hwb (j : Fin (R + 1)) (hj : c.val + j.val ≤ t.val) : u ≤ fraction i 0 (w j).1 := by
    apply hbetween ⟨c.val + j.val, by have := c.isLt; have := j.isLt; omega⟩
    · exact Fin.lt_def.mpr (by dsimp [c]; omega)
    · exact Fin.le_iff_val_le_val.mpr hj
  have hwp (j : Fin (R + 1)) (hj : c.val + j.val ≤ t.val) :
      ∀ v, (Sampling.zeros ((w j).1 v)).card = k :=
    hplateau ⟨c.val + j.val, by have := c.isLt; have := j.isLt; omega⟩ (Fin.le_iff_val_le_val.mpr hj)
  have hwc (j : Fin (R + 1)) (hj : c.val + j.val ≤ t.val) : cap omega (w j).1 :=
    hcap ⟨c.val + j.val, by have := c.isLt; have := j.isLt; omega⟩ (Fin.le_iff_val_le_val.mpr hj)
  refine ⟨c, ?_⟩
  change w 0 ∈ starts k i u ∧ w ∈ blockFailure (R := R) k i omega (w 0)
  refine ⟨?_, ?_⟩
  · rw [hw0]
    exact ⟨hplateau c' hct, hcband, hcupper⟩
  · by_cases hshort : t.val - c.val ≤ R
    · let v : Fin (R + 1) := ⟨t.val - c.val, by omega⟩
      have hsum : c.val + v.val = t.val := by have := Fin.le_iff_val_le_val.mp hct; dsimp [v, c'] at *; omega
      have hwt : w v = h t := by
        change h ⟨c.val + v.val, _⟩ = h t
        congr 1
        exact Fin.ext hsum
      exact ProtectionGeometry.crossing_failure i u theta ((3 : ℝ) ^ k) omega hu huquarter rfl htheta w v
        (by rw [hw0]; exact hcupper)
        (fun j hj ↦ hwb j (by have := Fin.le_iff_val_le_val.mp hj; omega))
        (fun j hj ↦ hwp j (by have := Fin.le_iff_val_le_val.mp hj; omega))
        (fun j hj ↦ hwc j (by have := Fin.le_iff_val_le_val.mp hj; omega))
        (by rw [hwt]; exact hbad)
    · exact ProtectionGeometry.stay_above_failure i u theta ((3 : ℝ) ^ k) omega hu huquarter
        (by positivity) htheta w (by rw [hw0]; exact hcupper)
        (fun j ↦ hwb j (by have := j.isLt; omega))
        (fun j ↦ hwc j (by have := j.isLt; omega))

end
end Lax343628Proofs.ProtectionCrossings
