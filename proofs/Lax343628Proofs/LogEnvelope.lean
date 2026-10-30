import Lax343628Proofs.AsymptoticLedger

namespace Lax343628Proofs.LogEnvelope

open Filter Lax343628Proofs.AsymptoticLedger Lax343628Proofs.EntropyLedger
open Lax343628.Runtime
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma apply_bound (A : ℕ+) (hA : 16777216 ≤ (A : ℕ)) (n k : ℕ) (mu : ℕ+)
    (hk : 1 ≤ k) (pc : ℝ) (hp : 0 < pc ∧ pc ≤ 1)
    (hpc : 1 / ((A : ℕ) : ℝ) ≤ pc)
    (hmu : ((scale A k : ℕ) : ℝ) ^ 300 * logarithms n mu (AttemptError.delta n mu) ≤ (mu : ℕ))
    (hn : ((scale A k : ℕ) : ℝ) ^ 300 * logarithms n mu (AttemptError.delta n mu) ≤ n) :
    expectedRuntime n k mu pc ≤ ENNReal.ofReal ((268435456 / pc) * (mu : ℕ) * (n : ℝ)) := by
  obtain ⟨hs, hks, hD, hpcs⟩ := scale_facts A hA k pc hpc
  have hdim := (PhaseConditions.of_size (scale A k) hs n k mu (AttemptError.delta n mu)
    hk hks hD (AttemptError.delta_bounds n mu) hmu hn).dimension
  exact CommonRuntime.bound (scale A k) hs hk (by omega) hks hD pc ⟨hpcs, hp.2⟩ hmu hn

lemma logarithmic (pc eps a : ℝ) (hp : 0 < pc ∧ pc ≤ 1) (he : 0 < eps) (ha : eps ≤ a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ (k : ℕ) (mu : ℕ+),
      1 ≤ k → (k : ℝ) ≤ c * Real.log (n : ℝ) →
      (n : ℝ) ^ eps ≤ (mu : ℕ) → (mu : ℕ) ≤ (n : ℝ) ^ a →
      expectedRuntime n k mu pc ≤ ENNReal.ofReal ((268435456 / pc) * (mu : ℕ) * (n : ℝ)) := by
  obtain ⟨A, hA, hpc⟩ := choose_scale pc hp.1
  let t : ℝ := min eps 1 / 2
  let H : ℝ := 100 * (a + 1)
  let D : ℝ := ((A : ℕ) : ℝ) ^ 300 * H
  have ht : 0 < t := by dsimp [t]; exact div_pos (lt_min he (by norm_num)) (by norm_num)
  have ha0 : 0 < a := he.trans_le ha
  have hH : 0 < H := by dsimp [H]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨t / (300 * Real.log 3), by positivity, ?_⟩
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_log_absorb D t hD ht, hlog,
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually_ge_atTop 1]
      with n hnD hnlog hn1
  intro k mu hk hkl hml hmu
  have hnp : (0 : ℝ) < n := by linarith
  have hs := scale_bound A k n t hnp hkl
  have hW := logarithms_upper n mu a ha0 hn1 hnlog hmu
  have hW0 := (logarithms_bounds n mu (AttemptError.delta n mu) (AttemptError.delta_bounds n mu)).1
  have hbudget : ((scale A k : ℕ) : ℝ) ^ 300 * logarithms n mu (AttemptError.delta n mu) ≤
      (n : ℝ) ^ (t + t) := by
    calc
      _ ≤ (((A : ℕ) : ℝ) ^ 300 * (n : ℝ) ^ t) * (H * Real.log (n : ℝ)) :=
        mul_le_mul hs hW (by linarith) (by positivity)
      _ = (n : ℝ) ^ t * (D * Real.log (n : ℝ)) := by dsimp [D]; ring
      _ ≤ (n : ℝ) ^ t * (n : ℝ) ^ t := mul_le_mul_of_nonneg_left hnD (by positivity)
      _ = _ := (Real.rpow_add hnp t t).symm
  have hte : t + t ≤ eps := by dsimp [t]; linarith [min_le_left eps (1 : ℝ)]
  have ht1 : t + t ≤ 1 := by dsimp [t]; linarith [min_le_right eps (1 : ℝ)]
  exact apply_bound A hA n k mu hk pc hp hpc
    (hbudget.trans ((Real.rpow_le_rpow_of_exponent_le hn1 hte).trans hml))
    (hbudget.trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 ht1))

lemma doubly_logarithmic (pc a : ℝ) (hp : 0 < pc ∧ pc ≤ 1) (ha : 0 < a) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ (k : ℕ) (mu : ℕ+),
      1 ≤ k → (k : ℝ) ≤ c * Real.log (Real.log (n : ℝ)) →
      C * (k : ℝ) * Real.log (n : ℝ) ^ 2 ≤ (mu : ℕ) → (mu : ℕ) ≤ (n : ℝ) ^ a →
      expectedRuntime n k mu pc ≤ ENNReal.ofReal ((268435456 / pc) * (mu : ℕ) * (n : ℝ)) := by
  obtain ⟨A, hA, hpc⟩ := choose_scale pc hp.1
  let H : ℝ := 100 * (a + 1)
  let D : ℝ := ((A : ℕ) : ℝ) ^ 300 * H
  have hH : 0 < H := by dsimp [H]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨1 / (300 * Real.log 3), D, by positivity, hD, ?_⟩
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_log_square D hD, hlog,
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually_ge_atTop 1]
      with n hnD hnlog hn1
  intro k mu hk hkl hml hmu
  have hlp : 0 < Real.log (n : ℝ) := by linarith
  have hs := scale_bound A k (Real.log (n : ℝ)) 1 hlp hkl
  rw [Real.rpow_one] at hs
  have hW := logarithms_upper n mu a ha hn1 hnlog hmu
  have hW0 := (logarithms_bounds n mu (AttemptError.delta n mu) (AttemptError.delta_bounds n mu)).1
  have hbudget : ((scale A k : ℕ) : ℝ) ^ 300 * logarithms n mu (AttemptError.delta n mu) ≤
      D * Real.log (n : ℝ) ^ 2 := by
    calc
      _ ≤ (((A : ℕ) : ℝ) ^ 300 * Real.log (n : ℝ)) * (H * Real.log (n : ℝ)) :=
        mul_le_mul hs hW (by linarith) (by positivity)
      _ = _ := by dsimp [D]; ring
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hmass : D * Real.log (n : ℝ) ^ 2 ≤ (mu : ℕ) := by
    have hh := mul_le_mul_of_nonneg_right hkR (show 0 ≤ D * Real.log (n : ℝ) ^ 2 by positivity)
    nlinarith
  exact apply_bound A hA n k mu hk pc hp hpc (hbudget.trans hmass) (hbudget.trans hnD)

end
end Lax343628Proofs.LogEnvelope
