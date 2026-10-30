import Lax343628Proofs.Sampling
import Mathlib.MeasureTheory.Constructions.Pi

namespace Lax343628Proofs.BitProduct

open Lax343628.Algorithm MeasureTheory
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def joint {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (q : PMF β) : PMF (α × β) :=
  PMF.ofFintype (fun ab ↦ p ab.1 * q ab.2) (by
    have hp : (∑ a, p a) = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    have hq : (∑ b, q b) = 1 := by simpa only [tsum_fintype] using q.tsum_coe
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hq, mul_one]
    exact hp)

lemma joint_apply {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (q : PMF β) (a : α) (b : β) :
    joint p q (a, b) = p a * q b := rfl

lemma joint_bind {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (q : PMF β) :
    joint p q = p.bind (fun a ↦ q.bind (fun b ↦ PMF.pure (a, b))) := by
  ext ⟨a, b⟩
  simp [joint_apply, PMF.bind_apply, PMF.pure_apply, Prod.ext_iff, mul_ite, ite_and]

def product (ι : Type*) [Fintype ι] (p : ι → PMF (Fin 2)) : PMF (ι → Fin 2) :=
  PMF.ofFintype (fun mask ↦ ∏ j, p j (mask j)) (by
    have h : ∀ j, (∑ b : Fin 2, p j b) = 1 := fun j ↦ by
      simpa only [tsum_fintype] using (p j).tsum_coe
    rw [← Fintype.prod_sum]
    simp only [h, Finset.prod_const_one])

lemma product_apply {ι : Type*} [Fintype ι] (p : ι → PMF (Fin 2)) (mask : ι → Fin 2) :
    product ι p mask = ∏ j, p j (mask j) := rfl

lemma toMeasure_product (ι : Type*) [Fintype ι] (p : ι → PMF (Fin 2)) :
    (product ι p).toMeasure = Measure.pi (fun j : ι ↦ (p j).toMeasure) := by
  apply Measure.ext_of_singleton
  intro mask
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton mask), Measure.pi_singleton,
    product_apply]
  apply Finset.prod_congr rfl
  intro j _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

lemma product_eval (ι : Type*) [Fintype ι] (p : ι → PMF (Fin 2)) (i : ι) :
    (product ι p).map (fun x ↦ x i) = p i := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun x : ι → Fin 2 ↦ x i) (product ι p) (by fun_prop),
    toMeasure_product]
  exact (measurePreserving_eval (μ := fun j ↦ (p j).toMeasure) i).map_eq

lemma map_product (ι : Type*) [Fintype ι] (p : ι → PMF (Fin 2)) (f : ι → Fin 2 → Fin 2) :
    (product ι p).map (fun mask j ↦ f j (mask j)) = product ι (fun j ↦ (p j).map (f j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun mask : ι → Fin 2 ↦ fun j ↦ f j (mask j)) (product ι p)
    (by fun_prop), toMeasure_product, toMeasure_product]
  have h := Measure.pi_map_pi (μ := fun j : ι ↦ (p j).toMeasure) (f := f) (fun _ ↦ by fun_prop)
  have hm (j : ι) : (p j).toMeasure.map (f j) = ((p j).map (f j)).toMeasure :=
    PMF.toMeasure_map (f j) (p j) (by fun_prop)
  simp_rw [hm] at h
  exact h

def bits (ι : Type*) [Fintype ι] (p : ℝ) : PMF (ι → Fin 2) :=
  PMF.ofFintype (fun mask ↦ ∏ j, coin p (mask j)) (by
    have h := (coin p).tsum_coe
    rw [tsum_fintype] at h
    rw [← Fintype.prod_sum]
    simp [h])

lemma product_coin (ι : Type*) [Fintype ι] (p : ℝ) :
    product ι (fun _ ↦ coin p) = bits ι p := rfl

lemma bits_apply {ι : Type*} [Fintype ι] (p : ℝ) (mask : ι → Fin 2) :
    bits ι p mask = ∏ j, coin p (mask j) := rfl

lemma bits_fin (n : ℕ) (p : ℝ) : bits (Fin n) p = independentBits n p := rfl

lemma toMeasure_bits (ι : Type*) [Fintype ι] (p : ℝ) :
    (bits ι p).toMeasure = Measure.pi (fun _ : ι ↦ (coin p).toMeasure) := by
  apply Measure.ext_of_singleton
  intro mask
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton mask), Measure.pi_singleton,
    bits_apply]
  apply Finset.prod_congr rfl
  intro j _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

lemma restrict_bits (ι : Type*) [Fintype ι] (p : ℝ) (q : ι → Prop) [DecidablePred q] :
    (bits ι p).map (fun mask (j : Subtype q) ↦ mask j) = bits (Subtype q) p := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun mask : ι → Fin 2 ↦ fun j : Subtype q ↦ mask j)
    (bits ι p) (by fun_prop), toMeasure_bits, toMeasure_bits]
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (α := fun _ : ι ↦ Fin 2) (fun _ : ι ↦ (coin p).toMeasure) q
  have hfst := measurePreserving_fst
    (μ := Measure.pi (fun _ : Subtype q ↦ (coin p).toMeasure))
    (ν := Measure.pi (fun _ : {i // ¬q i} ↦ (coin p).toMeasure))
  exact (hfst.comp hsplit).map_eq

lemma reindex_bits {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ℝ) (e : ι ≃ κ) :
    (bits ι p).map (fun mask j ↦ mask (e.symm j)) = bits κ p := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun mask : ι → Fin 2 ↦ fun j : κ ↦ mask (e.symm j))
    (bits ι p) (by fun_prop), toMeasure_bits, toMeasure_bits]
  have h := (measurePreserving_piCongrLeft (α := fun _ : κ ↦ Fin 2)
    (fun _ : κ ↦ (coin p).toMeasure) e).map_eq
  have hfun : (MeasurableEquiv.piCongrLeft (fun _ : κ ↦ Fin 2) e :
      (ι → Fin 2) → (κ → Fin 2)) = (fun mask j ↦ mask (e.symm j)) := by
    funext mask j
    simpa only [e.apply_symm_apply] using
      MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ : κ ↦ Fin 2) mask (e.symm j)
  rw [hfun] at h
  exact h

def restrictToFin {n : ℕ} (S : Finset (Fin n)) (mask : BitString n) : BitString S.card :=
  fun j ↦ mask (S.equivFin.symm j)

lemma independentBits_restrict {n : ℕ} (S : Finset (Fin n)) (p : ℝ) :
    (independentBits n p).map (restrictToFin S) = independentBits S.card p := by
  have h1 := restrict_bits (Fin n) p (fun j ↦ j ∈ S)
  have h2 := reindex_bits p S.equivFin
  have h1' : (bits (Fin n) p).map (fun mask (j : S) ↦ mask j) = bits S p := by
    convert h1 using 1
    congr 1
    exact Subsingleton.elim _ _
  rw [← h1', PMF.map_comp] at h2
  simp only [bits_fin, Function.comp_def] at h2
  convert h2 using 1
  congr 1

end
end Lax343628Proofs.BitProduct
