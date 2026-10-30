import Lax343628Proofs.MutationCoupling
import Lax343628Proofs.UniformMutation

namespace Lax343628Proofs.SplitBirth

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.BitProduct Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.MutationCoupling Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def join {ι : Type*} (R : ι → Prop) [DecidablePred R]
    (a : {j // R j} → Fin 2) (b : {j // ¬R j} → Fin 2) : ι → Fin 2 :=
  fun j ↦ if hj : R j then a ⟨j, hj⟩ else b ⟨j, hj⟩

lemma product_pure {ι : Type*} [Fintype ι] (f : ι → Fin 2) :
    product ι (fun j ↦ PMF.pure (f j)) = PMF.pure f := by
  ext mask
  by_cases hm : mask = f
  · subst mask
    simp only [product_apply, PMF.pure_apply_self, Finset.prod_const_one]
  · obtain ⟨j, hj⟩ : ∃ j, mask j ≠ f j := by
      simpa only [funext_iff, not_forall] using hm
    rw [product_apply, PMF.pure_apply_of_ne f mask hm]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (PMF.pure_apply_of_ne _ _ hj)

lemma product_split_mean {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → PMF (Fin 2))
    (R : ι → Prop) [DecidablePred R] (f : (ι → Fin 2) → ℝ) :
    mean (product ι p) f =
      mean (product {j // R j} (fun j ↦ p j)) (fun a ↦
        mean (product {j // ¬R j} (fun j ↦ p j)) (fun b ↦ f (join R a b))) := by
  unfold mean
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd R (fun _ : ι ↦ Fin 2)).symm,
    Fintype.sum_prod_type]
  simp only [product_apply, ENNReal.toReal_prod, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hprod := Fintype.prod_subtype_mul_prod_subtype R
    (fun j ↦ (p j (join R a b j)).toReal)
  have hR : (∏ j : {j // R j}, (p j (join R a b j)).toReal) =
      ∏ j : {j // R j}, (p j (a j)).toReal := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [join, dif_pos j.property]
  have hnotR : (∏ j : {j // ¬R j}, (p j (join R a b j)).toReal) =
      ∏ j : {j // ¬R j}, (p j (b j)).toReal := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [join, dif_neg j.property]
  rw [hR, hnotR] at hprod
  change (∏ j, (p j (join R a b j)).toReal) * f (join R a b) = _
  rw [← hprod]
  ring

def protectedSites {n : ℕ} (R : Finset (Fin n)) (x y : BitString n) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ j ∉ R ∧ x j = y j)

lemma protectedSites_common {n : ℕ} (R : Finset (Fin n)) (x y : BitString n) :
    ∀ j ∈ protectedSites R x y, x j = y j := fun _ hj ↦ (Finset.mem_filter.mp hj).2.2

def outsideLaw {n : ℕ} (R : Finset (Fin n)) (x y : BitString n) :
    PMF ({j : Fin n // j ∉ R} → Fin 2) :=
  product {j : Fin n // j ∉ R} (fun j ↦ if x j = y j then PMF.pure (x j) else coin (1 / 2))

lemma siteLaw_one (p : ℝ) : siteLaw 1 1 p = (coin p).map (fun b ↦ 1 - b) := by
  rw [siteLaw_common]
  congr 1
  funext b
  fin_cases b <;> rfl

lemma suppressed_split_mean {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (f : BitString n → ℝ) :
    mean (suppressedPair (protectedSites R x y) x y p) f =
      mean (bits R p) (fun fresh ↦ mean (outsideLaw R x y) (fun outside ↦
        f (join (fun j ↦ j ∈ R) (fun j ↦ 1 - fresh j) outside))) := by
  rw [suppressed_product _ x y p hp (protectedSites_common R x y)]
  have hsplit := product_split_mean
    (fun j : Fin n ↦ if j ∈ protectedSites R x y then PMF.pure (x j) else siteLaw (x j) (y j) p)
    (fun j ↦ j ∈ R) f
  refine hsplit.trans ?_
  have hI : (Subtype.fintype (fun j : Fin n ↦ j ∈ R)) = (inferInstance : Fintype R) :=
    Subsingleton.elim _ _
  rw [hI]
  have hi : (fun j : R ↦ if j.val ∈ protectedSites R x y then PMF.pure (x j) else siteLaw (x j) (y j) p) =
      (fun _ : R ↦ siteLaw 1 1 p) := by
    funext j
    have hnot : j.val ∉ protectedSites R x y := by simp [protectedSites, j.property]
    rw [if_neg hnot, (hR j j.property).1, (hR j j.property).2]
  have ho : (fun j : {j : Fin n // j ∉ R} ↦
      if j.val ∈ protectedSites R x y then PMF.pure (x j) else siteLaw (x j) (y j) p) =
      (fun j : {j : Fin n // j ∉ R} ↦ if x j = y j then PMF.pure (x j) else coin (1 / 2)) := by
    funext j
    by_cases hxy : x j = y j
    · simp [protectedSites, j.property, hxy]
    · have hnot : j.val ∉ protectedSites R x y := by simp [protectedSites, hxy]
      rw [if_neg hnot, if_neg hxy, siteLaw_different _ _ hxy _ hp]
  rw [hi, ho]
  have hm := map_product R (fun _ ↦ coin p) (fun _ b ↦ 1 - b)
  simp_rw [← siteLaw_one] at hm
  have hmean := congrArg (fun q : PMF (R → Fin 2) ↦ mean q (fun a ↦
    mean (outsideLaw R x y) (fun outside ↦ f (join (fun j ↦ j ∈ R) a outside)))) hm.symm
  calc
    _ = mean ((product R (fun _ ↦ coin p)).map (fun mask j ↦ 1 - mask j)) (fun a ↦
        mean (outsideLaw R x y) (fun outside ↦ f (join (fun j ↦ j ∈ R) a outside))) := by
      exact hmean
    _ = _ := by rw [mean_map]; rfl

end
end Lax343628Proofs.SplitBirth
