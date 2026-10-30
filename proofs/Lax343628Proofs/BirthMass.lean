import Lax343628Proofs.ShadowParent

namespace Lax343628Proofs.BirthMass

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.NamedBirth
open Lax343628Proofs.BirthGeometry Lax343628Proofs.BirthOn Lax343628Proofs.FiniteDrift
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] [DecidableEq α] {n k : ℕ}

def plateauTest (k : ℕ) (x : BitString n) : ℝ := if (zeros x).card = k then 1 else 0

end
end Lax343628Proofs.BirthMass
