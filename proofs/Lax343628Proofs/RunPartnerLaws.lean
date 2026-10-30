import Lax343628Proofs.RunEnvironment

namespace Lax343628Proofs.RunPartnerLaws

open Lax343628.Algorithm Lax343628Proofs.Genotypes
open Lax343628Proofs.RunEnvironment Lax343628Proofs.SparseGroups
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu : ℕ+}

lemma member_time {H j t : ℕ} (ht : t ∈ group H ell j) : t < H :=
  Finset.mem_range.mp (Finset.mem_filter.mp ht).1

def laws [Nonempty (Genotype n k)] (H : Fin (R + 1)) (P : ℕ → Population n mu)
    (hP : ∀ t, t < H.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (j : Fin (count R ell)) : PMF (Genotype n k) :=
  if hG : (group H.val ell j.val).Nonempty then
    letI : Nonempty (group H.val ell j.val) := ⟨⟨Classical.choose hG, Classical.choose_spec hG⟩⟩
    groupLaw (group H.val ell j.val) P (fun t ht u ↦ hP t (member_time ht) u)
  else PMF.pure (Classical.choice inferInstance)

lemma laws_nonempty [Nonempty (Genotype n k)] (H : Fin (R + 1)) (P : ℕ → Population n mu)
    (hP : ∀ t, t < H.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (j : Fin (count R ell)) [Nonempty (group H.val ell j.val)] :
    laws H P hP j = groupLaw (group H.val ell j.val) P (fun t ht u ↦ hP t (member_time ht) u) := by
  have hG : (group H.val ell j.val).Nonempty := by
    obtain ⟨t⟩ := (inferInstance : Nonempty (group H.val ell j.val))
    exact ⟨t.val, t.property⟩
  simp only [laws, dif_pos hG]

end
end Lax343628Proofs.RunPartnerLaws
