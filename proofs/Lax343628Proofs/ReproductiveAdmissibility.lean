import Lax343628Proofs.PhysicalCone

namespace Lax343628Proofs.ReproductiveAdmissibility

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.ColumnKernels Lax343628Proofs.PrivateColumns
open Lax343628Proofs.PhysicalCone Lax343628Proofs.FiniteDrift
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {i : Fin n} {b : Fin 2}

def error (n k : ℕ) : ℝ := 512 * (3 : ℝ) ^ k * (k : ℝ) ^ 2 / n

lemma error_nonneg (n k : ℕ) : 0 ≤ error n k := by unfold error; positivity

lemma mixed_relative (hk : 2 ≤ k) (hn : 4 * k ≤ n) (partners : PMF (BitString n))
    (hp : ∀ u ∈ partners.support, (zeros u).card = k)
    (rho : ℝ) (hrho : 2 ≤ rho) (hrho' : rho ≤ 3) (h : ColumnClass n k i b → ℝ)
    (hh : ∀ z, 0 ≤ h z) (hc : ∀ z w, classDistance z w = 1 → h w ≤ rho * h z)
    (x y : ColumnClass n k i b) (hxy : classDistance x y = 1) :
    ReproductiveValues.action (mixedKernel partners) h y ≤
      rho * ReproductiveValues.action (mixedKernel partners) h x + error n k * h x := by
  rw [mixed_action, mixed_action]
  calc
    _ ≤ mean partners (fun u ↦ rho * action u h x + error n k * h x) :=
      mean_mono_on_support partners (fun u hu ↦
        action_relative hk hn x y u (hp u hu) hxy rho hrho hrho' h hh hc)
    _ = _ := by rw [mean_add, mean_mul, mean_const]

lemma value_cone (hk : 2 ≤ k) (hn : 4 * k ≤ n) (partners : ℕ → PMF (BitString n))
    (hp : ∀ s u, u ∈ (partners s).support → (zeros u).card = k)
    {a : ℝ} (ha : 0 ≤ a) (R : ℕ) (horizon : R * a * error n k ≤ 1) (s : ℕ) :
    ReproductiveValues.Cone (fun x y : ColumnClass n k i b ↦ classDistance x y = 1)
      (2 + R * a * error n k)
      (ReproductiveValues.value (fun t ↦ mixedKernel (partners t)) a s R) := by
  apply ReproductiveValues.value_cone (rhoMax := 3) _ _ ha (error_nonneg n k) (by norm_num : (1 : ℝ) ≤ 2)
    R (by linarith) _ s
  intro t rho h hlo hhi hh hc x y hxy
  exact mixed_relative hk hn (partners t) (hp t) rho hlo hhi h hh hc x y hxy

lemma value_ratio (hk : 2 ≤ k) (hn : 4 * k ≤ n) (partners : ℕ → PMF (BitString n))
    (hp : ∀ s u, u ∈ (partners s).support → (zeros u).card = k)
    {a : ℝ} (ha : 0 ≤ a) (R : ℕ) (horizon : R * a * error n k ≤ 1) (s : ℕ)
    (x y : ColumnClass n k i b) :
    ReproductiveValues.value (fun t ↦ mixedKernel (partners t)) a s R y ≤
      (3 : ℝ) ^ k * ReproductiveValues.value (fun t ↦ mixedKernel (partners t)) a s R x := by
  have hc := value_cone hk hn partners hp ha R horizon s (b := b) (i := i)
  have hlo : 1 ≤ 2 + R * a * error n k := by
    have := mul_nonneg (mul_nonneg (Nat.cast_nonneg R) ha) (error_nonneg n k)
    linarith
  have hhi : 2 + R * a * error n k ≤ 3 := by linarith
  have hh := ReproductiveValues.value_nonneg (fun t ↦ mixedKernel (k := k) (i := i) (b := b) (partners t)) ha s R
  have hg := global_ratio (by omega) _ hlo _ hh hc x y
  exact hg.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by linarith) hhi k) (hh x))

end
end Lax343628Proofs.ReproductiveAdmissibility
