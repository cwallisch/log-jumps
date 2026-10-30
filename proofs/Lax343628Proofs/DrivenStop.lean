import Lax343628Proofs.RunBoundary

namespace Lax343628Proofs.DrivenStop

open Lax343628.Algorithm Lax343628Proofs.DrivenNoise Lax343628Proofs.DrivenPaths
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n R : ℕ} {mu : ℕ+}

def qualifies (active : Population n mu → Prop) (h : Fin (R + 1) → State n mu) (t : ℕ) : Prop :=
  t ≤ R ∧ (t = R ∨ ¬active (population h t))

lemma exists_stop (active : Population n mu → Prop) (h : Fin (R + 1) → State n mu) :
    ∃ t, qualifies active h t := ⟨R, le_rfl, Or.inl rfl⟩

def time (active : Population n mu → Prop) (h : Fin (R + 1) → State n mu) : Fin (R + 1) :=
  ⟨Nat.find (exists_stop active h), Nat.lt_succ_of_le (Nat.find_spec (exists_stop active h)).1⟩

lemma before_active (active : Population n mu → Prop) (h : Fin (R + 1) → State n mu)
    (t : ℕ) (ht : t < (time active h).val) : active (population h t) := by
  by_contra hn
  have hmin := Nat.find_min (exists_stop active h) ht
  have htime := (time active h).isLt
  exact hmin ⟨by omega, Or.inr hn⟩

lemma time_spec (active : Population n mu → Prop) (h : Fin (R + 1) → State n mu) :
    (time active h).val = R ∨ ¬active (population h (time active h).val) :=
  (Nat.find_spec (exists_stop active h)).2

end
end Lax343628Proofs.DrivenStop
