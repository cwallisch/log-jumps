import Lax343628Proofs.ReproductiveValues

namespace Lax343628Proofs.ReproductiveComparison

open Lax343628Proofs.ReproductiveValues
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma comparison_step {m g Am Ag L c a D eps err : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hD : 0 < D) (heps : 0 ≤ eps) (herr : 0 ≤ err)
    (hL : 0 ≤ L) (hdom : c * g ≤ m) (hg : g ≤ D * L)
    (hbirth : c * (Ag + eps * L - err * D * L) - err * D * m ≤ Am)
    (hupper : g + a * Ag ≤ (1 + a) * D * L)
    (hsmall : a * err * D ≤ 1) (hdim : err * D * (1 + D) ≤ eps / 2) :
    c * (1 + a * eps / (2 * (1 + a) * D)) * (g + a * Ag) ≤ m + a * Am := by
  have hscaled := mul_le_mul_of_nonneg_left hbirth ha
  have hcomp := mul_le_mul_of_nonneg_left hdom
    (show 0 ≤ 1 - a * err * D by linarith)
  have hgscaled := mul_le_mul_of_nonneg_left hg
    (mul_nonneg (mul_nonneg ha hc) (mul_nonneg herr hD.le))
  have hdimscaled := mul_le_mul_of_nonneg_left hdim
    (mul_nonneg (mul_nonneg ha hc) hL)
  have ha1 : 0 < 1 + a := by linarith
  have hgain : c * (a * eps / (2 * (1 + a) * D)) * (g + a * Ag) ≤
      a * c * (eps / 2) * L := by
    calc
      _ ≤ c * (a * eps / (2 * (1 + a) * D)) * ((1 + a) * D * L) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = _ := by field_simp
  nlinarith

variable {M R : Type*} [Fintype M] [Fintype R]

def BirthComparison (rel : M → R → Prop) (A : Kernel M) (B : Kernel R) (eps err : ℝ) : Prop :=
  ∀ (m : M → ℝ) (g : R → ℝ) (c : ℝ),
    0 ≤ c → (∀ x, 0 ≤ m x) → (∀ y, 0 ≤ g y) →
    (∀ x y, rel x y → c * g y ≤ m x) →
    ∀ (L U V : ℝ), 0 ≤ L → (∀ y, L ≤ g y) → (∀ x, m x ≤ U) → (∀ y, g y ≤ V) →
    ∀ x y, rel x y →
      c * (action B g y + eps * L - err * V) - err * U ≤ action A m x

lemma value_comparison (rel : M → R → Prop) (A : ℕ → Kernel M) (B : ℕ → Kernel R)
    {a D eps err : ℝ} (ha : 0 ≤ a) (hD : 1 ≤ D) (heps : 0 ≤ eps) (herr : 0 ≤ err)
    (hsmall : a * err * D ≤ 1) (hdim : err * D * (1 + D) ≤ eps / 2)
    (Hmax : ℕ) (hbirth : ∀ s, BirthComparison rel (A s) (B s) eps err)
    (hratioM : ∀ s H, H ≤ Hmax → ∀ x y, value A a s H y ≤ D * value A a s H x)
    (hratioR : ∀ s H, H ≤ Hmax → ∀ x y, value B a s H y ≤ D * value B a s H x)
    (s H : ℕ) (hH : H ≤ Hmax) (x : M) (y : R) (hxy : rel x y) :
    (1 + a * eps / (2 * (1 + a) * D)) ^ H * value B a s H y ≤ value A a s H x := by
  have hDpos : 0 < D := by linarith
  have hbase : 0 ≤ 1 + a * eps / (2 * (1 + a) * D) := by positivity
  induction H generalizing s x y with
  | zero => simp [value]
  | succ H ih =>
    let m := value A a (s + 1) H
    let g := value B a (s + 1) H
    let c := (1 + a * eps / (2 * (1 + a) * D)) ^ H
    obtain ⟨z, _, hz⟩ := Finset.exists_min_image (Finset.univ : Finset R) g
      ⟨y, Finset.mem_univ y⟩
    have hmin : ∀ w, g z ≤ g w := fun w ↦ hz w (Finset.mem_univ w)
    have hM : ∀ w, m w ≤ D * m x := fun w ↦ hratioM (s + 1) H (by omega) x w
    have hG : ∀ w, g w ≤ D * g z := fun w ↦ hratioR (s + 1) H (by omega) z w
    have hmn : ∀ w, 0 ≤ m w := value_nonneg A ha (s + 1) H
    have hgn : ∀ w, 0 ≤ g w := value_nonneg B ha (s + 1) H
    have hc : 0 ≤ c := pow_nonneg hbase H
    have hdom : ∀ u v, rel u v → c * g v ≤ m u := fun u v huv ↦ ih (s + 1) (by omega) u v huv
    have hstep := hbirth s m g c hc hmn hgn hdom (g z) (D * m x) (D * g z)
      (hgn z) hmin hM hG x y hxy
    have hact := action_le (B s) g (D * g z) (mul_nonneg hDpos.le (hgn z)) hG y
    have hupper : g y + a * action (B s) g y ≤ (1 + a) * D * g z := by
      nlinarith [mul_le_mul_of_nonneg_left hact ha, hG y]
    have hresult := comparison_step hc ha hDpos heps herr (hgn z) (hdom x y hxy) (hG y)
      (by simpa only [mul_assoc] using hstep) hupper hsmall hdim
    change _ ≤ m x + a * action (A s) m x
    calc
      _ = c * (1 + a * eps / (2 * (1 + a) * D)) *
          (g y + a * action (B s) g y) := by rw [pow_succ]; rfl
      _ ≤ _ := hresult

end
end Lax343628Proofs.ReproductiveComparison
