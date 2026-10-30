import Lax343628Proofs.ClassIncrements
import Lax343628Proofs.ChannelNoise

namespace Lax343628Proofs.ClassNoise

open Lax343628.Algorithm Lax343628Proofs.TaggedDynamics
open Lax343628Proofs.ClassChannels Lax343628Proofs.ClassIncrements
open Lax343628Proofs.ChannelNoise Lax343628Proofs.FiniteDrift
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

lemma mutant_noise (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (i : Fin n)
    (ψ : BitString n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hh : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ M)
    (hψ : ∀ x, x i ≠ 1 → ψ x = 0) (P : Population n μ) :
    (∀ E, |centered (eventLaw pc P) (nonImmChange k i ψ P) E| ≤
      M * ((if channel i 1 P E then 1 else 0) + 3 * fraction i 1 P)) ∧
    mean (eventLaw pc P) (fun E ↦ centered (eventLaw pc P) (nonImmChange k i ψ P) E ^ 2) ≤
      M ^ 2 * (3 * fraction i 1 P) := by
  constructor
  · intro E
    exact centered_channel_bound (eventLaw pc P) {E | channel i 1 P E}
      (nonImmChange k i ψ P) M _ hM (nonImm_abs i ψ M hh P)
      (mutant_off_channel i ψ hψ P) (channel_bound pc hpc i 1 P) E
  · exact centered_variance_bound (eventLaw pc P) {E | channel i 1 P E}
      (nonImmChange k i ψ P) M _ hM (nonImm_abs i ψ M hh P)
      (mutant_off_channel i ψ hψ P) (channel_bound pc hpc i 1 P)

end
end Lax343628Proofs.ClassNoise
