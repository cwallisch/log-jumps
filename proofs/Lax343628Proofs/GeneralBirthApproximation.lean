import Lax343628Proofs.SplitBirth

namespace Lax343628Proofs.GeneralBirthApproximation

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.BitProduct Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.MutationCoupling Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.SplitBirth
open Lax343628Proofs.UniformMutation Lax343628Proofs.MaskCounts
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma mean_comm {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (q : PMF β)
    (f : α → β → ℝ) :
    mean p (fun a ↦ mean q (fun b ↦ f a b)) = mean q (fun b ↦ mean p (fun a ↦ f a b)) := by
  unfold mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

def freshChild {n : ℕ} (R : Finset (Fin n)) (outside : {j : Fin n // j ∉ R} → Fin 2)
    (mask : BitString R.card) : BitString n :=
  join (fun j ↦ j ∈ R) (fun j ↦ 1 - mask (R.equivFin j)) outside

lemma suppressed_mean_fresh {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (f : BitString n → ℝ) :
    mean (suppressedPair (protectedSites R x y) x y p) f =
      mean (outsideLaw R x y) (fun outside ↦
        mean (independentBits R.card p) (fun mask ↦ f (freshChild R outside mask))) := by
  rw [suppressed_split_mean R x y hR p hp f, mean_comm]
  have hreindex := reindex_bits p R.equivFin.symm
  have hr : (bits (Fin R.card) p).map (fun mask (j : R) ↦ mask (R.equivFin j)) = bits R p := by
    simpa only [Equiv.symm_symm] using hreindex
  apply congrArg (mean (outsideLaw R x y))
  funext outside
  have hm := mean_map (bits (Fin R.card) p) (fun mask (j : R) ↦ mask (R.equivFin j))
    (fun fresh ↦ f (join (fun j ↦ j ∈ R) (fun j ↦ 1 - fresh j) outside))
  rw [hr] at hm
  exact hm

lemma fresh_ones_le_zeros {n : ℕ} (R : Finset (Fin n))
    (outside : {j : Fin n // j ∉ R} → Fin 2) (mask : BitString R.card) :
    ones mask ≤ (zeros (freshChild R outside mask)).card := by
  let e : Fin R.card → Fin n := fun j ↦ (R.equivFin.symm j).val
  have he : Function.Injective e := fun a b hab ↦
    R.equivFin.symm.injective (Subtype.ext hab)
  have hsub : (onesSet mask).image e ⊆ zeros (freshChild R outside mask) := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    have hbit : mask a = 1 := (Finset.mem_filter.mp ha).2
    have heR : e a ∈ R := (R.equivFin.symm a).property
    simp only [mem_zeros, freshChild, join, dif_pos heR]
    have harg : (⟨e a, heR⟩ : R) = R.equivFin.symm a := rfl
    rw [harg, R.equivFin.apply_symm_apply, hbit]
    rfl
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ he, card_onesSet] at hcard
  exact hcard

def idealBirthMean {n : ℕ} (k : ℕ) (R : Finset (Fin n)) (x y : BitString n)
    (f : BitString n → ℝ) : ℝ :=
  mean (outsideLaw R x y) (fun outside ↦
    poissonPlacement k R.card (fun mask ↦ f (freshChild R outside mask)))

lemma suppressed_poisson_error {n k : ℕ} (hn : 2 ≤ n) (R : Finset (Fin n)) (hk : k ≤ R.card)
    (x y : BitString n) (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1)
    (f : BitString n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ child, |f child| ≤ M)
    (hsupport : ∀ child, k < (zeros child).card → f child = 0) :
    |mean (suppressedPair (protectedSites R x y) x y (1 / n)) f - idealBirthMean k R x y f| ≤
      3 * M * ((k : ℝ) + 2) * (((n - R.card + k : ℕ) : ℝ) + 1) / n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (1 : ℝ) / n ∧ (1 : ℝ) / n ≤ 1 := ⟨by positivity, by
    exact (div_le_one (by linarith : (0 : ℝ) < n)).mpr (by linarith)⟩
  rw [suppressed_mean_fresh R x y hR (1 / n) hp f, idealBirthMean, ← mean_sub]
  apply (abs_mean_le _ _).trans
  apply (mean_mono _ (fun outside ↦ ?_)).trans_eq (mean_const _ _)
  exact mutation_poisson_placement hn (by simpa using Finset.card_le_univ R) hk
    (fun mask ↦ f (freshChild R outside mask)) M hM (fun mask ↦ hf _)
    (fun mask hmask ↦ hsupport _ (hmask.trans_le (fresh_ones_le_zeros R outside mask)))

lemma physical_poisson_error {n k : ℕ} (hn : 2 ≤ n) (R : Finset (Fin n)) (hk : k ≤ R.card)
    (x y : BitString n) (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1)
    (f : BitString n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ child, |f child| ≤ M)
    (hsupport : ∀ child, k < (zeros child).card → f child = 0) :
    |mean (pairMutation x y (1 / n)) f - idealBirthMean k R x y f| ≤
      2 * M * (protectedSites R x y).card / n +
      3 * M * ((k : ℝ) + 2) * (((n - R.card + k : ℕ) : ℝ) + 1) / n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (1 : ℝ) / n ∧ (1 : ℝ) / n ≤ 1 := ⟨by positivity, by
    exact (div_le_one (by linarith : (0 : ℝ) < n)).mpr (by linarith)⟩
  have hfirst := pair_suppression_comparison (protectedSites R x y) x y (1 / n) hp f M hf
  have hsecond := suppressed_poisson_error hn R hk x y hR f M hM hf hsupport
  have htriangle := abs_sub_le (mean (pairMutation x y (1 / n)) f)
    (mean (suppressedPair (protectedSites R x y) x y (1 / n)) f) (idealBirthMean k R x y f)
  have hbound := add_le_add hfirst hsecond
  exact htriangle.trans (hbound.trans_eq (by ring))

def freshSet {n : ℕ} (S : Finset (Fin n)) : Finset (Fin n) := Finset.univ \ S

lemma freshSet_card {n : ℕ} (S : Finset (Fin n)) : (freshSet S).card = n - S.card := by
  rw [freshSet, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]

lemma freshSet_common_ones {n : ℕ} (S : Finset (Fin n)) (x y : BitString n)
    (hx : zeros x ⊆ S) (hy : zeros y ⊆ S) :
    ∀ j ∈ freshSet S, x j = 1 ∧ y j = 1 := by
  intro j hj
  have hjS : j ∉ S := (Finset.mem_sdiff.mp hj).2
  have hx0 : x j ≠ 0 := by intro hz; exact hjS (hx (by simpa only [mem_zeros] using hz))
  have hy0 : y j ≠ 0 := by intro hz; exact hjS (hy (by simpa only [mem_zeros] using hz))
  constructor <;> have h1 := (x j).isLt <;> have h2 := (y j).isLt <;> omega

lemma protectedSites_card {n : ℕ} (S : Finset (Fin n)) (x y : BitString n) :
    (protectedSites (freshSet S) x y).card ≤ S.card := by
  apply Finset.card_le_card
  intro j hj
  have hnot := (Finset.mem_filter.mp hj).2.1
  simpa only [freshSet, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hnot

lemma named_physical_error {n k : ℕ} (hk : 1 ≤ k) (hn : 4 * k ≤ n)
    (S : Finset (Fin n)) (hS : S.card ≤ 3 * k) (x y : BitString n)
    (hx : zeros x ⊆ S) (hy : zeros y ⊆ S)
    (f : BitString n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ child, |f child| ≤ M)
    (hsupport : ∀ child, k < (zeros child).card → f child = 0) :
    |mean (pairMutation x y (1 / n)) f - idealBirthMean k (freshSet S) x y f| ≤
      64 * M * (k : ℝ) ^ 2 / n := by
  have hScard : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hRcard : k ≤ (freshSet S).card := by rw [freshSet_card]; omega
  have h := physical_poisson_error (show 2 ≤ n by omega) (freshSet S) hRcard x y
    (freshSet_common_ones S x y hx hy) f M hM hf hsupport
  have hF : ((protectedSites (freshSet S) x y).card : ℝ) ≤ 3 * k := by
    exact_mod_cast (protectedSites_card S x y).trans hS
  have hNr : n - (freshSet S).card + k + 1 ≤ 5 * k := by rw [freshSet_card]; omega
  have hN : (((n - (freshSet S).card + k : ℕ) : ℝ) + 1) ≤ 5 * k := by exact_mod_cast hNr
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply h.trans
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ hnR.le
  calc
    _ ≤ 2 * M * (3 * k) + 3 * M * (3 * k) * (5 * k) := by
      gcongr
      linarith
    _ = 6 * M * k + 45 * M * (k : ℝ) ^ 2 := by ring
    _ ≤ _ := by nlinarith [mul_nonneg hM (show 0 ≤ (k : ℝ) ^ 2 - k by nlinarith)]

end
end Lax343628Proofs.GeneralBirthApproximation
