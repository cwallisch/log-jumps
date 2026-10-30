import Lax343628Proofs.FiniteProduct
import Lax343628Proofs.MaskCounts

namespace Lax343628Proofs.PartitionCounts

open Lax343628.Algorithm Lax343628Proofs.BitProduct Lax343628Proofs.FiniteProduct
open Lax343628Proofs.MaskCounts
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def toFinMask {ι : Type*} [Fintype ι] (mask : ι → Fin 2) : BitString (Fintype.card ι) :=
  fun j ↦ mask ((Fintype.equivFin ι).symm j)

lemma bits_toFinMask (ι : Type*) [Fintype ι] (p : ℝ) :
    (bits ι p).map toFinMask = independentBits (Fintype.card ι) p := by
  have h := reindex_bits p (Fintype.equivFin ι)
  rw [bits_fin] at h
  convert h using 1
  congr 1

def toFinCount {ι : Type*} [Fintype ι] (mask : ι → Fin 2) : Fin (Fintype.card ι + 1) :=
  ⟨ones (toFinMask mask), Nat.lt_succ_of_le (ones_le_length (toFinMask mask))⟩

lemma bits_count (ι : Type*) [Fintype ι] (p : ℝ) :
    (bits ι p).map toFinCount = weightLaw (Fintype.card ι) p := by
  rw [weightLaw, ← bits_toFinMask ι p, PMF.map_comp]
  congr 1

def counts {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (c : ι → κ)
    (mask : ι → Fin 2) (r : κ) : Fin (Fintype.card {i // c i = r} + 1) :=
  toFinCount (fun i : {i // c i = r} ↦ mask i)

lemma partition_counts {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (rate : κ → ℝ) :
    (product ι (fun i ↦ coin (rate (c i)))).map (counts c) =
      distribution (fun r : κ ↦ weightLaw (Fintype.card {i // c i = r}) (rate r)) := by
  have h1 := partition_constant_rates c rate
  have h2 := map_distribution (fun r : κ ↦ bits {i // c i = r} (rate r))
    (fun _ ↦ toFinCount)
  rw [← h1, PMF.map_comp] at h2
  simp_rw [bits_count] at h2
  convert h2 using 1
  congr 1

lemma toFinCount_eq_sum {ι : Type*} [Fintype ι] (mask : ι → Fin 2) :
    (toFinCount mask).val = ∑ i, (mask i : ℕ) := by
  change (∑ j : Fin (Fintype.card ι), (mask ((Fintype.equivFin ι).symm j) : ℕ)) = _
  exact (Fintype.equivFin ι).symm.sum_comp (fun i ↦ (mask i : ℕ))

lemma counts_eq_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (mask : ι → Fin 2) (r : κ) :
    (counts c mask r).val = ∑ i : {i // c i = r}, (mask i : ℕ) :=
  toFinCount_eq_sum _

def rawCount {ι κ : Type*} [Fintype ι] [DecidableEq κ] (c : ι → κ) (mask : ι → Fin 2)
    (r : κ) : ℕ := ∑ i ∈ Finset.univ.filter (fun i ↦ c i = r), (mask i : ℕ)

lemma counts_eq_rawCount {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (mask : ι → Fin 2) (r : κ) : (counts c mask r).val = rawCount c mask r := by
  rw [counts_eq_sum]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i ↦ c i = r))
    (by intro i; simp) (fun i ↦ (mask i : ℕ))).symm

lemma sum_region_weights {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (mask : ι → Fin 2) (a : κ → ℕ) :
    (∑ i, a (c i) * (mask i : ℕ)) = ∑ r, a r * (counts c mask r).val := by
  rw [← Fintype.sum_fiberwise c (fun i ↦ a (c i) * (mask i : ℕ))]
  apply Finset.sum_congr rfl
  intro r _
  rw [counts_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [i.property]

end
end Lax343628Proofs.PartitionCounts
