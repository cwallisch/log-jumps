import Lax343628Proofs.MutationDrift

namespace Lax343628Proofs.SpeciesEnvelope

open Lax343628Proofs.Genotypes Lax343628Proofs.Weights
open Lax343628Proofs.Species Lax343628Proofs.FiniteDrift
open Lax343628Proofs.ActualBirthKernels Lax343628Proofs.MutationDrift
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def farMass {n k : ℕ} (B : Genotype n k) (p : Genotype n k → ℝ) : ℝ :=
  offSum B (fun x ↦ if 2 ≤ distance B x then p x else 0)

lemma farMass_nonneg {n k : ℕ} (B : Genotype n k) (p : Genotype n k → ℝ)
    (hp : ∀ x, 0 ≤ p x) : 0 ≤ farMass B p := by
  apply offSum_nonneg
  intro x
  split_ifs
  · exact hp x
  · exact le_rfl

lemma off_mass_split {n k : ℕ} (B : Genotype n k) (p : Genotype n k → ℝ) :
    massOne B p + farMass B p = offSum B p := by
  rw [massOne, farMass, ← offSum_add]
  apply Finset.sum_congr rfl
  intro x hx
  have hxB := (Finset.mem_erase.mp hx).1
  have hpos := distance_pos B x hxB
  by_cases h1 : distance B x = 1
  · simp only [if_pos h1, show ¬2 ≤ distance B x by omega, if_false, add_zero]
  · simp only [if_neg h1, show 2 ≤ distance B x by omega, if_true, zero_add]

lemma mass_split {n k : ℕ} (B : Genotype n k) (p : PMF (Genotype n k)) :
    massOne B (fun x ↦ (p x).toReal) + farMass B (fun x ↦ (p x).toReal) = 1 - (p B).toReal := by
  rw [off_mass_split]
  have h := sum_mass p
  rw [sum_split B] at h
  linarith

lemma farCloud_lower {n k : ℕ} (B : Genotype n k) (p : Genotype n k → ℝ)
    (hp : ∀ x, 0 ≤ p x) : (4 : ℝ)⁻¹ ^ k * farMass B p ≤ farCloud B p := by
  rw [farMass, farCloud, ← offSum_mul]
  apply offSum_mono
  intro x _
  by_cases hx : 2 ≤ distance B x
  · simp only [if_pos hx]
    have h := mul_le_mul_of_nonneg_left
      (uniform_weight_lower (by omega : 1 ≤ distance B x) (distance_le B x)) (hp x)
    nlinarith
  · simp only [if_neg hx, mul_zero, le_refl]

lemma numerical_quadratic_gain (p p0 w m h F : ℝ)
    (hp0 : 0 ≤ p0) (hp : p0 ≤ p) (hw : 0 ≤ w) (hp0w : p0 * w ≤ 1)
    (hm : 0 ≤ m) (hh : 0 ≤ h) (hsum : m + h ≤ 1) (hF : w * h ≤ F) :
    (p0 * w / 100) * (m + h) ^ 2 ≤ 34 / 1000 * p * F + 135 / 1000 * m ^ 2 := by
  have hppos : 0 ≤ p := hp0.trans hp
  have hprod : p0 * w * h ≤ p * F := by
    have h1 := mul_le_mul_of_nonneg_left hF hppos
    have h2 := mul_le_mul_of_nonneg_right hp (mul_nonneg hw hh)
    nlinarith
  have hh1 : h ≤ 1 := by linarith
  have hh2 : h ^ 2 ≤ h := by nlinarith
  have hsq : (m + h) ^ 2 ≤ 2 * m ^ 2 + 2 * h := by nlinarith [sq_nonneg (m - h)]
  have hscale := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ p0 * w / 100 by positivity)
  have hmcoef := mul_le_mul_of_nonneg_right hp0w (sq_nonneg m)
  have hwh : 0 ≤ p0 * w * h := by positivity
  nlinarith

lemma otherPair_nonneg {n k : ℕ} (B : Genotype n k) (p : Genotype n k → ℝ)
    (hp : ∀ x, 0 ≤ p x) : 0 ≤ otherPair B p := by
  apply offSum_nonneg
  intro x
  apply offSum_nonneg
  intro y
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg (hp x) (hp y)) (weightedKernel_nonneg B x y)

lemma ideal_quadratic_drift {n k : ℕ} (B : Genotype n k) (p : PMF (Genotype n k))
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hp01 : p0 ≤ 1) (hpB : 0 < (p B).toReal)
    (hpmin : p0 ≤ (p B).toReal)
    (hiso : cloud B (fun x ↦ (p x).toReal) / (p B).toReal ≤ 1 / 25) :
    (p0 * (4 : ℝ)⁻¹ ^ k / 100) * (1 - (p B).toReal) ^ 2 ≤
      pairValue (fun x ↦ (p x).toReal) (weightedKernel B) -
        (cloud B (fun x ↦ (p x).toReal) / (p B).toReal) *
          pairValue (fun x ↦ (p x).toReal) (cloneKernel B) := by
  let f : Genotype n k → ℝ := fun x ↦ (p x).toReal
  have hf : ∀ x, 0 ≤ f x := fun _ ↦ ENNReal.toReal_nonneg
  have hmass := mass_split B p
  have hw1 : (4 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp0w : p0 * (4 : ℝ)⁻¹ ^ k ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left hw1 hp0).trans (by simpa using hp01)
  have hnum := numerical_quadratic_gain (f B) p0 ((4 : ℝ)⁻¹ ^ k)
    (massOne B f) (farMass B f) (farCloud B f) hp0 hpmin (by positivity) hp0w
    (massOne_nonneg B f hf) (farMass_nonneg B f hf)
    (by change massOne B (fun x ↦ (p x).toReal) + farMass B (fun x ↦ (p x).toReal) ≤ 1
        rw [hmass]
        linarith [show 0 ≤ (p B).toReal from ENNReal.toReal_nonneg])
    (farCloud_lower B f hf)
  change massOne B f + farMass B f = 1 - f B at hmass
  rw [hmass] at hnum
  have hid := ideal_drift B f hf hpB hiso
  have hother := otherPair_nonneg B f hf
  linarith

end
end Lax343628Proofs.SpeciesEnvelope
