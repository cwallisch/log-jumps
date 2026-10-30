import Lax343628Proofs.ColumnKernels
import Lax343628Proofs.SubsetGeometry

namespace Lax343628Proofs.PrivateColumns

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.Genotypes
open Lax343628Proofs.UniformSubsets Lax343628Proofs.ColumnKernels
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

abbrev Private (n : ℕ) (i : Fin n) (r : ℕ) := Rank {j : Fin n // j ≠ i} r

def named {n r : ℕ} {i : Fin n} (X : Private n i r) : Finset (Fin n) :=
  X.val.map (Function.Embedding.subtype _)

lemma named_card {n r : ℕ} {i : Fin n} (X : Private n i r) : (named X).card = r := by
  simp only [named, Finset.card_map, X.property]

lemma column_not_named {n r : ℕ} {i : Fin n} (X : Private n i r) : i ∉ named X :=
  Finset.notMem_map_subtype_of_not_property X.val (by simp)

def restrict {n r : ℕ} {i : Fin n} (S : Finset (Fin n)) (hS : S.card = r) (hi : i ∉ S) :
    Private n i r :=
  ⟨S.subtype (fun j ↦ j ≠ i), by
    rw [Finset.card_subtype, Finset.filter_true_of_mem (fun j hj ↦ by
      intro h; subst j; exact hi hj), hS]⟩

lemma named_restrict {n r : ℕ} {i : Fin n} (S : Finset (Fin n)) (hS : S.card = r) (hi : i ∉ S) :
    named (restrict S hS hi) = S := by
  apply Finset.subtype_map_of_mem
  intro j hj hji
  subst j
  exact hi hj

def resident (n r : ℕ) (i : Fin n) : Private n i r → ColumnClass n (r + 1) i 0 :=
  fun X ↦ ⟨Genotypes.toString ⟨insert i (named X), by
    rw [Finset.card_insert_of_notMem (column_not_named X), named_card]⟩,
    by rw [zeros_toString]; rw [Finset.card_insert_of_notMem (column_not_named X), named_card],
    by simp [Genotypes.toString]⟩

def mutant (n r : ℕ) (i : Fin n) : Private n i r → ColumnClass n r i 1 :=
  fun X ↦ ⟨Genotypes.toString ⟨named X, named_card X⟩,
    by rw [zeros_toString, named_card], by simp [Genotypes.toString, column_not_named]⟩

lemma resident_zeros {n r : ℕ} {i : Fin n} (X : Private n i r) :
    zeros (resident n r i X).val = insert i (named X) := zeros_toString _

lemma mutant_zeros {n r : ℕ} {i : Fin n} (X : Private n i r) :
    zeros (mutant n r i X).val = named X := zeros_toString _

def residentPrivate {n r : ℕ} {i : Fin n} (x : ColumnClass n (r + 1) i 0) : Private n i r :=
  restrict ((zeros x.val).erase i) (by
    rw [Finset.card_erase_of_mem (by rw [mem_zeros]; exact x.property.2), x.property.1]
    omega) (Finset.notMem_erase _ _)

def mutantPrivate {n r : ℕ} {i : Fin n} (x : ColumnClass n r i 1) : Private n i r :=
  restrict (zeros x.val) x.property.1 (by rw [mem_zeros, x.property.2]; decide)

lemma resident_residentPrivate {n r : ℕ} {i : Fin n} (x : ColumnClass n (r + 1) i 0) :
    resident n r i (residentPrivate x) = x := by
  apply Subtype.ext
  have hz : insert i (named (residentPrivate x)) = zeros x.val := by
    unfold residentPrivate
    rw [named_restrict, Finset.insert_erase (by rw [mem_zeros]; exact x.property.2)]
  have heq : (⟨insert i (named (residentPrivate x)), by
      rw [Finset.card_insert_of_notMem (column_not_named _), named_card]⟩ : Genotype n (r + 1)) =
      ofString x.val x.property.1 := Subtype.ext hz
  exact (congrArg Genotypes.toString heq).trans (toString_ofString x.val x.property.1)

lemma mutant_mutantPrivate {n r : ℕ} {i : Fin n} (x : ColumnClass n r i 1) :
    mutant n r i (mutantPrivate x) = x := by
  apply Subtype.ext
  have heq : (⟨named (mutantPrivate x), named_card _⟩ : Genotype n r) =
      ofString x.val x.property.1 := Subtype.ext (named_restrict _ _ _)
  exact (congrArg Genotypes.toString heq).trans (toString_ofString x.val x.property.1)

def classDistance {n k : ℕ} {i : Fin n} {b : Fin 2}
    (x y : ColumnClass n k i b) : ℕ := (zeros x.val \ zeros y.val).card

lemma named_distance {n r : ℕ} {i : Fin n} (X Y : Private n i r) :
    (named X \ named Y).card = SubsetGeometry.distance X Y := by
  rw [named, named, ← Finset.map_sdiff, Finset.card_map]
  rfl

lemma resident_distance {n r : ℕ} {i : Fin n} (X Y : Private n i r) :
    classDistance (resident n r i X) (resident n r i Y) = SubsetGeometry.distance X Y := by
  unfold classDistance
  rw [resident_zeros, resident_zeros]
  have heq : insert i (named X) \ insert i (named Y) = named X \ named Y := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [column_not_named]
    · simp [hji]
  rw [heq, named_distance]

lemma mutant_distance {n r : ℕ} {i : Fin n} (X Y : Private n i r) :
    classDistance (mutant n r i X) (mutant n r i Y) = SubsetGeometry.distance X Y := by
  rw [classDistance, mutant_zeros, mutant_zeros, named_distance]

lemma resident_ratio {n r : ℕ} {i : Fin n} {rho : ℝ} (hrho : 1 ≤ rho)
    (h : ColumnClass n (r + 1) i 0 → ℝ) (hnonneg : ∀ x, 0 ≤ h x)
    (hadj : ∀ x y, classDistance x y = 1 → h y ≤ rho * h x)
    (x y : ColumnClass n (r + 1) i 0) : h y ≤ rho ^ r * h x := by
  have hp := SubsetGeometry.cone_global rho hrho (fun X : Private n i r ↦ h (resident n r i X))
    (fun X ↦ hnonneg _) (fun X Y hXY ↦ hadj _ _ (by rwa [resident_distance]))
    (residentPrivate x) (residentPrivate y)
  simpa only [resident_residentPrivate] using hp

lemma mutant_ratio {n r : ℕ} {i : Fin n} {rho : ℝ} (hrho : 1 ≤ rho)
    (h : ColumnClass n r i 1 → ℝ) (hnonneg : ∀ x, 0 ≤ h x)
    (hadj : ∀ x y, classDistance x y = 1 → h y ≤ rho * h x)
    (x y : ColumnClass n r i 1) : h y ≤ rho ^ r * h x := by
  have hp := SubsetGeometry.cone_global rho hrho (fun X : Private n i r ↦ h (mutant n r i X))
    (fun X ↦ hnonneg _) (fun X Y hXY ↦ hadj _ _ (by rwa [mutant_distance]))
    (mutantPrivate x) (mutantPrivate y)
  simpa only [mutant_mutantPrivate] using hp

end
end Lax343628Proofs.PrivateColumns
