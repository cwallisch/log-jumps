import Lax343628Proofs.TaggedDynamics
import Lax343628Proofs.ColumnKernels

namespace Lax343628Proofs.ClassChannels

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.TaggedDynamics Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.EmpiricalKernels
open Lax343628Proofs.Deletion Lax343628Proofs.PhysicalOffspring
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {μ : ℕ+}

def fraction (i : Fin n) (b : Fin 2) (P : Population n μ) : ℝ :=
  mean (PMF.uniformOfFintype (Fin (μ : ℕ))) (fun u ↦ if P u i = b then 1 else 0)

def parentsHave (i : Fin n) (b : Fin 2) (P : Population n μ) (uv : Fin (μ : ℕ) × Fin (μ : ℕ)) : Prop :=
  P uv.1 i = b ∨ P uv.2 i = b

def deletedHave (i : Fin n) (b : Fin 2) (P : Population n μ) (d : Fin ((μ : ℕ) + 1)) : Prop :=
  ∃ u : Fin (μ : ℕ), d = u.castSucc ∧ P u i = b

def channel (i : Fin n) (b : Fin 2) (P : Population n μ) (E : Event n μ) : Prop :=
  parentsHave i b P E.1 ∨ deletedHave i b P E.2.2

lemma deletedHave_cast (i : Fin n) (b : Fin 2) (P : Population n μ) (u : Fin (μ : ℕ)) :
    deletedHave i b P u.castSucc ↔ P u i = b := by
  constructor
  · rintro ⟨v, hv, hb⟩
    have heq : u = v := Fin.ext (congrArg (fun d : Fin ((μ : ℕ) + 1) ↦ d.val) hv)
    exact heq.symm ▸ hb
  · intro hb; exact ⟨u, rfl, hb⟩

lemma deletedHave_last (i : Fin n) (b : Fin 2) (P : Population n μ) :
    ¬deletedHave i b P (Fin.last (μ : ℕ)) := by
  rintro ⟨u, hu, _⟩
  have hval := congrArg Fin.val hu
  have := u.isLt
  simp only [Fin.val_last, Fin.val_castSucc] at hval
  omega

lemma deleted_mean (i : Fin n) (b : Fin 2) (P : Population n μ) :
    mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))) (fun d ↦ if deletedHave i b P d then 1 else 0) =
      (μ : ℕ) / ((μ : ℕ) + 1 : ℝ) * fraction i b P := by
  rw [uniform_mean, Fin.sum_univ_castSucc]
  simp only [deletedHave_last, if_false, deletedHave_cast, add_zero, Fintype.card_fin]
  unfold fraction
  rw [uniform_mean, Fintype.card_fin]
  have hm : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have heq : (((μ : ℕ) + 1 : ℕ) : ℝ) = (μ : ℕ) + 1 := by norm_num
  rw [heq]
  field_simp

lemma fraction_bounds (i : Fin n) (b : Fin 2) (P : Population n μ) :
    0 ≤ fraction i b P ∧ fraction i b P ≤ 1 := by
  constructor
  · exact mean_nonneg _ (fun u ↦ by split_ifs <;> norm_num)
  · exact (mean_mono _ (fun u ↦ show (if P u i = b then (1 : ℝ) else 0) ≤ 1 by
      split_ifs <;> norm_num)).trans_eq (mean_const _ 1)

lemma mean_eventLaw (pc : ℝ) (P : Population n μ) (f : Event n μ → ℝ) :
    mean (eventLaw pc P) f = mean (parentLaw μ pc) (fun uv ↦
      mean (pairMutation (P uv.1) (P uv.2) (1 / n)) (fun z ↦
        mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))) (fun d ↦ f (uv, z, d)))) := by
  simp only [eventLaw, Bind.bind, Pure.pure, mean_bind, mean_pure]

lemma mean_parent (pc : ℝ) (P : Population n μ) (f : Fin (μ : ℕ) × Fin (μ : ℕ) → ℝ) :
    mean (eventLaw pc P) (fun E ↦ f E.1) = mean (parentLaw μ pc) f := by
  rw [mean_eventLaw]
  simp only [mean_const]

lemma mean_deleted (pc : ℝ) (P : Population n μ) (f : Fin ((μ : ℕ) + 1) → ℝ) :
    mean (eventLaw pc P) (fun E ↦ f E.2.2) = mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))) f := by
  rw [mean_eventLaw]
  simp only [mean_const]

lemma parent_first (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (f : Fin (μ : ℕ) → ℝ) :
    mean (parentLaw μ pc) (fun uv ↦ f uv.1) = mean (PMF.uniformOfFintype (Fin (μ : ℕ))) f := by
  rw [mean_parentLaw pc hpc]
  rw [mean_uniform_pair (fun u v ↦ f u)]
  simp only [mean_const]
  ring

lemma parent_second (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (f : Fin (μ : ℕ) → ℝ) :
    mean (parentLaw μ pc) (fun uv ↦ f uv.2) = mean (PMF.uniformOfFintype (Fin (μ : ℕ))) f := by
  rw [mean_parentLaw pc hpc]
  rw [mean_uniform_pair (fun u v ↦ f v)]
  simp only [mean_const]
  ring

lemma parents_bound (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (i : Fin n) (b : Fin 2) (P : Population n μ) :
    mean (parentLaw μ pc) (fun uv ↦ if parentsHave i b P uv then 1 else 0) ≤ 2 * fraction i b P := by
  have hh := mean_mono (parentLaw μ pc) (fun uv ↦
    show (if parentsHave i b P uv then (1 : ℝ) else 0) ≤
      (if P uv.1 i = b then 1 else 0) + (if P uv.2 i = b then 1 else 0) by
      unfold parentsHave; split_ifs <;> norm_num; tauto)
  rw [mean_add, parent_first pc hpc (fun u ↦ if P u i = b then 1 else 0),
    parent_second pc hpc (fun u ↦ if P u i = b then 1 else 0)] at hh
  exact hh.trans_eq (by unfold fraction; ring)

lemma deleted_bound (i : Fin n) (b : Fin 2) (P : Population n μ) :
    mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))) (fun d ↦ if deletedHave i b P d then 1 else 0) ≤
      fraction i b P := by
  have hcast (u : Fin (μ : ℕ)) : deletedHave i b P u.castSucc ↔ P u i = b := by
    constructor
    · rintro ⟨v, hv, hb⟩
      have heq : u = v := Fin.ext (congrArg (fun d : Fin ((μ : ℕ) + 1) ↦ d.val) hv)
      exact heq.symm ▸ hb
    · intro hb; exact ⟨u, rfl, hb⟩
  have hlast : ¬deletedHave i b P (Fin.last (μ : ℕ)) := by
    rintro ⟨u, hu, _⟩
    have hval := congrArg Fin.val hu
    have := u.isLt
    simp only [Fin.val_last, Fin.val_castSucc] at hval
    omega
  rw [uniform_mean, Fin.sum_univ_castSucc]
  simp only [hlast, if_false, hcast, add_zero, Fintype.card_fin]
  unfold fraction
  rw [uniform_mean, Fintype.card_fin]
  have hm : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have hsum : 0 ≤ ∑ u : Fin (μ : ℕ), if P u i = b then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun u _ ↦ by split_ifs <;> norm_num)
  apply div_le_div_of_nonneg_left hsum hm
  norm_num

lemma channel_bound (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (i : Fin n) (b : Fin 2) (P : Population n μ) :
    mean (eventLaw pc P) (fun E ↦ if channel i b P E then 1 else 0) ≤ 3 * fraction i b P := by
  have hh := mean_mono (eventLaw pc P) (fun E ↦
    show (if channel i b P E then (1 : ℝ) else 0) ≤
      (if parentsHave i b P E.1 then 1 else 0) + (if deletedHave i b P E.2.2 then 1 else 0) by
      unfold channel; split_ifs <;> norm_num; tauto)
  rw [mean_add, mean_parent pc P (fun uv ↦ if parentsHave i b P uv then 1 else 0),
    mean_deleted pc P (fun d ↦ if deletedHave i b P d then 1 else 0)] at hh
  linarith [parents_bound pc hpc i b P, deleted_bound i b P]

def rare (i : Fin n) (b c : Fin 2) (P : Population n μ) (E : Event n μ) : Prop :=
  P E.1.1 i = c ∧ P E.1.2 i = c ∧ E.2.1 i = b

lemma rare_bound (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (i : Fin n) (b c : Fin 2)
    (hbc : b ≠ c) (P : Population n μ) :
    mean (eventLaw pc P) (fun E ↦ if rare i b c P E then 1 else 0) ≤ fraction i c P / n := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) ≤ 1 / n ∧ 1 / (n : ℝ) ≤ 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr hnR⟩
  have heq : mean (eventLaw pc P) (fun E ↦ if rare i b c P E then 1 else 0) =
      mean (parentLaw μ pc) (fun uv ↦ if P uv.1 i = c ∧ P uv.2 i = c then 1 / n else 0) := by
    rw [mean_eventLaw]
    congr 1
    funext uv
    by_cases huv : P uv.1 i = c ∧ P uv.2 i = c
    · have htest : (fun z : BitString n ↦
          mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1)))
            (fun d ↦ if rare i b c P (uv, z, d) then (1 : ℝ) else 0)) =
          (fun z ↦ if z i = b then 1 else 0) := by
        funext z
        simp only [rare, huv.1, huv.2, true_and, mean_const]
      rw [htest, if_pos huv, ColumnKernels.pairMutation_class_mass _ _ _ hp,
        huv.1, huv.2, siteLaw_apply _ _ _ _ hp]
      simp only [siteProbability, if_neg hbc, ite_true, ENNReal.toReal_ofReal hp.1]
    · have htest : (fun z : BitString n ↦
          mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1)))
            (fun d ↦ if rare i b c P (uv, z, d) then (1 : ℝ) else 0)) = fun _ ↦ 0 := by
        funext z
        have hh : ¬rare i b c P (uv, z, Fin.last (μ : ℕ)) := by
          intro h; exact huv ⟨h.1, h.2.1⟩
        have hn' (d : Fin ((μ : ℕ) + 1)) : ¬rare i b c P (uv, z, d) := hh
        simp only [hn', if_false, mean_const]
      rw [htest, mean_const, if_neg huv]
  rw [heq]
  have ht := mean_mono (parentLaw μ pc) (fun uv ↦
    show (if P uv.1 i = c ∧ P uv.2 i = c then (1 / n : ℝ) else 0) ≤
      (1 / n) * (if P uv.1 i = c then 1 else 0) by
      split_ifs <;> simp_all)
  rw [mean_mul, parent_first pc hpc (fun u ↦ if P u i = c then 1 else 0)] at ht
  exact ht.trans_eq (by unfold fraction; ring)

def residentChannel (i : Fin n) (P : Population n μ) (E : Event n μ) : Prop :=
  channel i 0 P E ∨ rare i 0 1 P E

lemma resident_channel_bound (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (i : Fin n) (P : Population n μ) :
    mean (eventLaw pc P) (fun E ↦ if residentChannel i P E then 1 else 0) ≤
      3 * fraction i 0 P + fraction i 1 P / n := by
  have ht := mean_mono (eventLaw pc P) (fun E ↦
    show (if residentChannel i P E then (1 : ℝ) else 0) ≤
      (if channel i 0 P E then 1 else 0) + (if rare i 0 1 P E then 1 else 0) by
      unfold residentChannel
      split_ifs <;> norm_num; tauto)
  rw [mean_add] at ht
  linarith [channel_bound pc hpc i 0 P, rare_bound pc hpc i 0 1 (by decide) P]

end
end Lax343628Proofs.ClassChannels
