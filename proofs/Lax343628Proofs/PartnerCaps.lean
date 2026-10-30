import Lax343628Proofs.EmpiricalCap
import Lax343628Proofs.RunPartnerLaws

namespace Lax343628Proofs.PartnerCaps

open Lax343628.Algorithm Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open Lax343628Proofs.ClassBirthEstimates Lax343628Proofs.RunEnvironment Lax343628Proofs.RunPartnerLaws
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison Lax343628Proofs.Genotypes
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu rs : ℕ+}

lemma empirical_atom_mean (P : Population n mu) (z : BitString n) :
    average P (EmpiricalCap.atomTest z) = EmpiricalKernels.frequency P z := by
  change mean (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun u ↦ EmpiricalCap.atomTest z (P u)) = _
  rw [← mean_map]
  exact EmpiricalCap.atom_mean _ z

lemma groupLaw_cap (G : Finset ℕ) [Nonempty G] (P : ℕ → Population n mu)
    (hP : ∀ t ∈ G, ∀ u, (Sampling.zeros (P t u)).card = k) (omega : ℝ)
    (hcap : ∀ t ∈ G, ∀ z : BitString n, EmpiricalKernels.frequency (P t) z ≤ 1 - omega)
    (u : Genotype n k) : (groupLaw G P hP u).toReal ≤ 1 - omega := by
  rw [← EmpiricalCap.atom_mean]
  have heq : EmpiricalCap.atomTest u = (fun v ↦ EmpiricalCap.atomTest (toString u) (toString v)) := by
    funext v
    simp only [EmpiricalCap.atomTest, toString_eq_iff]
  rw [heq, ← mean_map, groupLaw_mean]
  have hh := mean_mono (PMF.uniformOfFintype G) (fun t ↦ show average (P t.val) (EmpiricalCap.atomTest (toString u)) ≤ 1 - omega by
    rw [empirical_atom_mean]
    exact hcap t.val t.property (toString u))
  exact hh.trans_eq (mean_const _ _)

lemma laws_cap [Nonempty (Genotype n k)]
    (H : Fin (R + 1)) (P : ℕ → Population n mu)
    (hP : ∀ t, t < H.val → ∀ u, (Sampling.zeros (P t u)).card = k) (omega : ℝ)
    (hcap : ∀ t, t < H.val → ∀ z : BitString n, EmpiricalKernels.frequency (P t) z ≤ 1 - omega)
    (j : Fin (count R ell)) (hj : (group H.val ell j.val).Nonempty) (u : Genotype n k) :
    (laws H P hP j u).toReal ≤ 1 - omega := by
  let : Nonempty (group H.val ell j.val) := ⟨⟨Classical.choose hj, Classical.choose_spec hj⟩⟩
  rw [laws_nonempty H P hP j]
  exact groupLaw_cap _ P _ omega (fun t ht ↦ hcap t (member_time ht)) u

lemma bad_lists_mean [Nonempty (Genotype n k)]
    (H : Fin (R + 1)) (P : ℕ → Population n mu)
    (hP : ∀ t, t < H.val → ∀ u, (Sampling.zeros (P t u)).card = k) (omega : ℝ) (homega : 0 < omega)
    (hcap : ∀ t, t < H.val → ∀ z : BitString n, EmpiricalKernels.frequency (P t) z ≤ 1 - omega) :
    mean (FiniteProduct.distribution (fun j : Fin (count R ell) ↦ EmpiricalSampling.samples (laws H P hP j) (rs : ℕ)))
      (fun env ↦ if ∀ j : Fin (count R ell), (group H.val ell j.val).Nonempty →
        ∀ u, EmpiricalCap.frequency (env j) u < 1 - omega / 2 then 0 else 1) ≤
      (count R ell : ℝ) * (4 / ((rs : ℕ) * omega ^ 2)) := by
  have hh := EmpiricalCap.selected_lists_bad_mean (laws H P hP) (show 1 ≤ (rs : ℕ) from rs.pos)
    omega homega (fun j : Fin (count R ell) ↦ (group H.val ell j.val).Nonempty)
    (fun j hj u ↦ laws_cap H P hP omega hcap j hj u)
  simp only [Fintype.card_fin] at hh
  convert hh using 1
  congr 1
  funext env
  split_ifs <;> rfl

lemma partner_atom (xs : Fin (rs : ℕ) → Genotype n k) (u : Genotype n k) :
    (partnerLaw xs (toString u)).toReal = EmpiricalCap.frequency xs u := by
  rw [← EmpiricalCap.atom_mean, partner_mean]
  unfold EmpiricalCap.frequency EmpiricalSampling.sampleMean EmpiricalSampling.sampleSum
  simp only [EmpiricalCap.atomTest, toString_eq_iff]

lemma path_cap (H : Fin (R + 1)) (env : Lists n k (count R ell) rs) (omega : ℝ)
    (hgood : ∀ j : Fin (count R ell), (group H.val ell j.val).Nonempty →
      ∀ u, EmpiricalCap.frequency (env j) u < 1 - omega / 2)
    (t : ℕ) (ht : t < H.val) (z : BitString n) (hz : (Sampling.zeros z).card = k) :
    (path (H, env) t z).toReal ≤ 1 - omega / 2 := by
  let j := index R H.val ell t (by have := H.isLt; omega)
  have htj : t ∈ group H.val ell j.val := mem_index_group R H.val ell t (by have := H.isLt; omega) ht
  have hb := (hgood j ⟨t, htj⟩ (ofString z hz)).le
  have heq : (partnerLaw (env j) z).toReal = EmpiricalCap.frequency (env j) (ofString z hz) := by
    simpa only [toString_ofString] using partner_atom (env j) (ofString z hz)
  change (partnerLaw (env j) z).toReal ≤ _
  rw [heq]
  exact hb

end
end Lax343628Proofs.PartnerCaps
