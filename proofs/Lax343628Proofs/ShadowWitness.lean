import Lax343628Proofs.ShadowComparison

namespace Lax343628Proofs.ShadowWitness

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.Sampling Lax343628Proofs.PhysicalShadow Lax343628Proofs.ReproductiveValues
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {i : Fin n}

lemma exists_resident (x : ColumnClass n (r + 1) i 1) : ∃ y, Related x y := by
  have hc := NormalizedPrivate.mutant_private_size x
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < ((zeros x.val).erase i).card by omega)
  let Z := ((zeros x.val).erase i).erase e
  have hZ : Z.card = ClassTest.size (r + 1) 0 := by
    dsimp [Z]
    rw [Finset.card_erase_of_mem he, hc]
    simp only [ClassTest.size, if_true, Nat.add_sub_cancel]
  have hi : i ∉ Z := by dsimp [Z]; exact fun hh ↦ Finset.notMem_erase i _ (Finset.mem_of_mem_erase hh)
  refine ⟨ClassTest.encode (by omega : 1 ≤ r + 1) Z hZ hi, ?_⟩
  unfold Related
  rw [ClassTest.encode_private]
  exact Finset.erase_subset _ _

lemma arbitrary_values (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (partners : ℕ → PMF (BitString n))
    (hp : ∀ s u, u ∈ (partners s).support → (zeros u).card = r + 1)
    (omega : ℝ) (homega : 0 ≤ omega)
    (hcap : ∀ s (y : ColumnClass n (r + 1) i 0), (partners s y.val).toReal ≤ 1 - omega)
    {a : ℝ} (ha : 0 ≤ a) (H : ℕ)
    (horizon : H * a * ReproductiveAdmissibility.error n (r + 1) ≤ 1)
    (hsmall : a * (128 * (r + 1 : ℝ) ^ 2 / n) * (3 : ℝ) ^ (r + 1) ≤ 1)
    (hdim : (128 * (r + 1 : ℝ) ^ 2 / n) * (3 : ℝ) ^ (r + 1) * (1 + (3 : ℝ) ^ (r + 1)) ≤
      ShadowGaps.delta (r + 1) * omega / 2)
    (s : ℕ) (x : ColumnClass n (r + 1) i 1) (y : ColumnClass n (r + 1) i 0) :
    (1 + a * (ShadowGaps.delta (r + 1) * omega) /
        (2 * (1 + a) * (3 : ℝ) ^ (r + 1))) ^ H * value (fun t ↦ mixedKernel (partners t)) a s H y ≤
      (3 : ℝ) ^ (r + 1) * value (fun t ↦ mixedKernel (partners t)) a s H x := by
  obtain ⟨w, hxw⟩ := exists_resident x
  have hc := ShadowComparison.value_comparison hr hn partners hp omega homega hcap ha H horizon hsmall hdim s x w hxw
  have hrw := ReproductiveAdmissibility.value_ratio (by omega : 2 ≤ r + 1) hn partners hp ha H horizon s w y
  have hscale := mul_le_mul_of_nonneg_left hrw
    (show 0 ≤ (1 + a * (ShadowGaps.delta (r + 1) * omega) / (2 * (1 + a) * (3 : ℝ) ^ (r + 1))) ^ H by
      apply pow_nonneg
      have heps := (ShadowGaps.delta_pos (by omega : 1 ≤ r + 1)).le
      positivity)
  have hscale' := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 3 ^ (r + 1) by positivity)
  nlinarith

end
end Lax343628Proofs.ShadowWitness
