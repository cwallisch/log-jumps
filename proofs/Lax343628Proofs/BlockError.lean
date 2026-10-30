import Lax343628Proofs.EntropyBounds

namespace Lax343628Proofs.BlockError

open Lax343628Proofs.BlockParameters Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open Lax343628Proofs.EntropyLedger
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n k : ℕ) (mu : ℕ+)
    (hk : k ≤ n) (hn : 1 ≤ n) (hkS : k ≤ (S : ℕ)) (hmu : (S : ℕ) ^ 40 ≤ (mu : ℕ))
    (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1) :
    (4 * (Fintype.card (Net n k (horizon (S : ℕ) mu)
        (count (horizon (S : ℕ) mu) (groupSize (S : ℕ) mu)) (samples S)) : ℝ) *
        ((horizon (S : ℕ) mu : ℝ) + 1) + 1) *
      Real.exp (-(((S : ℕ) : ℝ) ^ 184 * logarithms n mu delta)) ≤ delta := by
  let s : ℝ := (S : ℕ)
  let R := horizon (S : ℕ) mu
  let J := count R (groupSize (S : ℕ) mu)
  let C := Fintype.card (Net n k R J (samples S))
  let W := logarithms n mu delta
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hS2 : 2 ≤ (S : ℕ) := by omega
  have hb := logarithms_bounds n mu delta hd
  have hW : 1 ≤ W := hb.1
  have hlogR : Real.log ((R : ℝ) + 1) ≤ s ^ 2 * W := horizon_log S hS n mu delta hd
  have hlogn : Real.log (n : ℝ) ≤ W := by
    apply le_trans _ hb.2.1
    apply Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
    linarith
  have hJ : (J : ℝ) ≤ s ^ 54 := by
    dsimp [s, J, R]
    exact_mod_cast group_count (S : ℕ) hS2 mu hmu
  have hrs : ((samples S : ℕ) : ℝ) ≤ s ^ 120 := by
    change (((S : ℕ) ^ 120 : ℕ) : ℝ) ≤ s ^ 120
    simp only [Nat.cast_pow, s, le_refl]
  have hkSR : (k : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hkS
  have hlogC : Real.log (C : ℝ) ≤ s ^ 176 * W :=
    EntropyBounds.net n k R J (samples S) hk hn s W hs hW hkSR hJ hrs hlogn hlogR
  have hC : 1 ≤ C := by
    dsimp [C]
    rw [net_card]
    have hchoose : 0 < n.choose k := Nat.choose_pos hk
    have hh : 0 < (R + 1) * (n.choose k) ^ (J * (samples S : ℕ)) := by positivity
    omega
  have hcoef := EntropyBounds.coefficient C R s W hC hs hW hlogC hlogR
  exact EntropyBounds.error C R s W delta hC hs hW hd.1 hb.2.2.2 hcoef

end
end Lax343628Proofs.BlockError
