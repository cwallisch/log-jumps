import Lax343628Proofs.FiniteComparison
import Mathlib.Data.Fin.Tuple.Basic

namespace Lax343628Proofs.Trajectories

open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*}

def pathLaw (K : α → PMF α) (p : PMF α) : (t : ℕ) → PMF (Fin (t + 1) → α)
  | 0 => p.map (fun x _ ↦ x)
  | t + 1 => (pathLaw K p t).bind (fun h ↦ (K (h (Fin.last t))).map (Fin.snoc h))

lemma pathLaw_last (K : α → PMF α) (p : PMF α) (t : ℕ) :
    (pathLaw K p t).map (fun h ↦ h (Fin.last t)) = law K p t := by
  induction t with
  | zero =>
    simp only [pathLaw, PMF.map_comp, Function.comp_def, law_zero]
    exact PMF.map_id p
  | succ t ih =>
    simp only [pathLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, Fin.snoc_last]
    have hmap (h : Fin (t + 1) → α) : (K (h (Fin.last t))).map (fun x ↦ x) = K (h (Fin.last t)) :=
      PMF.map_id _
    simp_rw [hmap]
    rw [law_succ, ← ih, PMF.bind_map]
    rfl

def frozen (A : Set α) : {t : ℕ} → (Fin (t + 1) → α) → α
  | 0, h => h 0
  | t + 1, h => if frozen A (Fin.init h) ∈ A then h (Fin.last (t + 1)) else frozen A (Fin.init h)

lemma frozen_snoc (A : Set α) {t : ℕ} (h : Fin (t + 1) → α) (x : α) :
    frozen A (Fin.snoc h x) = if frozen A h ∈ A then x else frozen A h := by
  simp only [frozen, Fin.init_snoc, Fin.snoc_last]

lemma frozen_active_last (A : Set α) {t : ℕ} (h : Fin (t + 1) → α)
    (hactive : frozen A h ∈ A) : frozen A h = h (Fin.last t) := by
  cases t with
  | zero => rfl
  | succ t =>
    change (if frozen A (Fin.init h) ∈ A then h (Fin.last (t + 1)) else frozen A (Fin.init h)) ∈ A at hactive
    change (if frozen A (Fin.init h) ∈ A then h (Fin.last (t + 1)) else frozen A (Fin.init h)) = _
    by_cases hp : frozen A (Fin.init h) ∈ A
    · rw [if_pos hp]
    · rw [if_neg hp] at hactive
      exact False.elim (hp hactive)

lemma frozen_active_iff (A : Set α) {t : ℕ} (h : Fin (t + 1) → α) :
    frozen A h ∈ A ↔ ∀ i, h i ∈ A := by
  induction t with
  | zero =>
    simp only [frozen]
    constructor
    · intro hh i
      have hi : i = 0 := by apply Fin.ext; have h := i.isLt; omega
      simpa only [hi] using hh
    · intro hh
      exact hh 0
  | succ t ih =>
    constructor
    · intro hh
      have hprev : frozen A (Fin.init h) ∈ A := by
        by_contra hn
        have hh' : frozen A (Fin.init h) ∈ A := by simpa only [frozen, if_neg hn] using hh
        exact hn hh'
      have hlast : h (Fin.last (t + 1)) ∈ A := by
        simpa only [frozen, if_pos hprev] using hh
      have hprefix := (ih (Fin.init h)).mp hprev
      intro i
      exact Fin.lastCases hlast (fun j ↦ hprefix j) i
    · intro hh
      have hprev : frozen A (Fin.init h) ∈ A := (ih (Fin.init h)).mpr
        (fun j ↦ hh j.castSucc)
      simpa only [frozen, if_pos hprev] using hh (Fin.last (t + 1))

lemma frozen_next_law (K : α → PMF α) (A : Set α) {t : ℕ} (h : Fin (t + 1) → α) :
    (K (h (Fin.last t))).map (fun x ↦ frozen A (Fin.snoc h x)) = stopped K A (frozen A h) := by
  simp only [frozen_snoc]
  by_cases ha : frozen A h ∈ A
  · simp only [stopped, if_pos ha]
    rw [frozen_active_last A h ha]
    exact PMF.map_id _
  · simp only [if_neg ha, stopped]
    exact PMF.map_const _ _

lemma frozen_pathLaw (K : α → PMF α) (A : Set α) (p : PMF α) (t : ℕ) :
    (pathLaw K p t).map (frozen A) = law (stopped K A) p t := by
  induction t with
  | zero =>
    simp only [pathLaw, PMF.map_comp, Function.comp_def, frozen, law_zero]
    exact PMF.map_id _
  | succ t ih =>
    simp only [pathLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
    simp_rw [frozen_next_law]
    rw [law_succ, ← ih, PMF.bind_map]
    rfl

lemma stay_probability (K : α → PMF α) (A : Set α) (p : PMF α) (t : ℕ) :
    (pathLaw K p t).toOuterMeasure {h | ∀ i, h i ∈ A} =
      (law (stopped K A) p t).toOuterMeasure A := by
  rw [← frozen_pathLaw, PMF.toOuterMeasure_map_apply]
  congr 1
  ext h
  exact (frozen_active_iff A h).symm

lemma pathLaw_first (K : α → PMF α) (p : PMF α) (t : ℕ) :
    (pathLaw K p t).map (fun h ↦ h 0) = p := by
  induction t with
  | zero =>
    simp only [pathLaw, PMF.map_comp, Function.comp_def]
    exact PMF.map_id _
  | succ t ih =>
    simp only [pathLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, Fin.snoc_apply_zero]
    have hmap (h : Fin (t + 1) → α) : (K (h (Fin.last t))).map (fun _ ↦ h 0) = PMF.pure (h 0) :=
      PMF.map_const _ _
    simp_rw [hmap]
    exact ih

lemma path_pure_start (K : α → PMF α) (x : α) {t : ℕ} (h : Fin (t + 1) → α)
    (hh : h ∈ (pathLaw K (PMF.pure x) t).support) : h 0 = x := by
  have hmap : h 0 ∈ ((pathLaw K (PMF.pure x) t).map (fun h ↦ h 0)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨h, hh, rfl⟩
  rw [pathLaw_first] at hmap
  exact (PMF.mem_support_pure_iff x (h 0)).mp hmap

def segment (s t : ℕ) (h : Fin (s + t + 1) → α) : Fin (t + 1) → α :=
  fun j ↦ h ⟨s + j.val, by omega⟩

lemma segment_snoc (s t : ℕ) (h : Fin (s + t + 1) → α) (x : α) :
    segment s (t + 1) (Fin.snoc h x) = Fin.snoc (segment s t h) x := by
  funext j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [segment, Fin.snoc_last]
    convert Fin.snoc_last (α := fun _ : Fin (s + t + 2) ↦ α) x h using 1
    congr 1
  · simp only [Fin.snoc_castSucc, segment]
    have hlt : s + i.val < s + (t + 1) := by have h := i.isLt; omega
    simp only [Fin.snoc, Fin.val_castSucc, dif_pos hlt]
    rfl

lemma pathLaw_segment (K : α → PMF α) (p : PMF α) (s t : ℕ) :
    (pathLaw K p (s + t)).map (segment s t) =
      (law K p s).bind (fun x ↦ pathLaw K (PMF.pure x) t) := by
  induction t with
  | zero =>
    have hseg : segment s 0 = (fun h : Fin (s + 1) → α ↦ fun _ : Fin 1 ↦ h (Fin.last s)) := by
      funext h j
      have hj : j = 0 := by apply Fin.ext; have h := j.isLt; omega
      rw [hj]
      rfl
    simp only [Nat.add_zero, hseg, pathLaw, PMF.pure_map]
    have h := congrArg (fun q : PMF α ↦ q.map (fun (x : α) (_ : Fin 1) ↦ x)) (pathLaw_last K p s)
    rw [PMF.map_comp] at h
    exact h
  | succ t ih =>
    simp only [Nat.add_succ, pathLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, segment_snoc]
    have hbind : ((pathLaw K p (s + t)).bind fun h ↦
        (K (h (Fin.last (s + t)))).map (fun x ↦ Fin.snoc (segment s t h) x)) =
        ((pathLaw K p (s + t)).map (segment s t)).bind
          (fun h : Fin (t + 1) → α ↦ (K (h (Fin.last t))).map
            (fun x ↦ Fin.snoc (α := fun _ : Fin (t + 2) ↦ α) h x)) := by
      rw [PMF.bind_map]
      rfl
    exact hbind.trans (by rw [ih, PMF.bind_bind])

lemma frozen_mem_range (A : Set α) {t : ℕ} (h : Fin (t + 1) → α) :
    ∃ i, frozen A h = h i := by
  induction t with
  | zero => exact ⟨0, rfl⟩
  | succ t ih =>
    change ∃ i, (if frozen A (Fin.init h) ∈ A then h (Fin.last (t + 1)) else frozen A (Fin.init h)) = h i
    by_cases hp : frozen A (Fin.init h) ∈ A
    · exact ⟨Fin.last (t + 1), by rw [if_pos hp]⟩
    · obtain ⟨i, hi⟩ := ih (Fin.init h)
      exact ⟨i.castSucc, by rw [if_neg hp]; exact hi⟩

lemma frozen_exit (A C target : Set α) {t : ℕ} (h : Fin (t + 1) → α)
    (hC : ∀ i, h i ∈ C) (hlast : h (Fin.last t) ∉ A) (hexit : C \ A ⊆ target) :
    frozen A h ∈ target := by
  obtain ⟨i, hi⟩ := frozen_mem_range A h
  apply hexit
  constructor
  · rw [hi]
    exact hC i
  · intro ha
    have hall := (frozen_active_iff A h).mp ha
    exact hlast (hall (Fin.last t))

lemma path_step_support (K : α → PMF α) (p : PMF α) {t : ℕ} (h : Fin (t + 1) → α)
    (hh : h ∈ (pathLaw K p t).support) (i : Fin t) : h i.succ ∈ (K (h i.castSucc)).support := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    obtain ⟨hist0, hpref, hmap⟩ := (PMF.mem_support_bind_iff _ _ h).mp hh
    obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
      exact hx
    · rw [show j.castSucc.succ = j.succ.castSucc by apply Fin.ext; rfl]
      simp only [Fin.snoc_castSucc]
      exact ih hist0 hpref j

lemma path_start_support (K : α → PMF α) (p : PMF α) {t : ℕ} (h : Fin (t + 1) → α)
    (hh : h ∈ (pathLaw K p t).support) : h 0 ∈ p.support := by
  have hmap : h 0 ∈ ((pathLaw K p t).map (fun h ↦ h 0)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨h, hh, rfl⟩
  rwa [pathLaw_first] at hmap

lemma path_invariant (K : α → PMF α) (p : PMF α) (A : Set α)
    (hp : ∀ x ∈ p.support, x ∈ A) (hK : ∀ x ∈ A, ∀ y ∈ (K x).support, y ∈ A)
    {t : ℕ} (h : Fin (t + 1) → α) (hh : h ∈ (pathLaw K p t).support) : ∀ i, h i ∈ A := by
  intro i
  refine Fin.induction ?_ (fun j hj ↦ ?_) i
  · exact hp (h 0) (path_start_support K p h hh)
  · exact hK _ hj _ (path_step_support K p h hh j)

def suffix (T s t : ℕ) (hst : s + t = T) (h : Fin (T + 1) → α) : Fin (t + 1) → α :=
  fun j ↦ h ⟨s + j.val, by omega⟩

lemma pathLaw_suffix (K : α → PMF α) (p : PMF α) (T s t : ℕ) (hst : s + t = T) :
    (pathLaw K p T).map (suffix T s t hst) =
      (law K p s).bind (fun x ↦ pathLaw K (PMF.pure x) t) := by
  subst T
  exact pathLaw_segment K p s t

def initialSegment (T u : ℕ) (h : Fin (T + u + 1) → α) : Fin (T + 1) → α :=
  fun j ↦ h ⟨j.val, by omega⟩

lemma initialSegment_snoc (T u : ℕ) (h : Fin (T + u + 1) → α) (x : α) :
    initialSegment T (u + 1) (Fin.snoc h x) = initialSegment T u h := by
  funext j
  unfold initialSegment
  have hlt : j.val < T + (u + 1) := by have h := j.isLt; omega
  simp only [Fin.snoc, dif_pos hlt]
  rfl

lemma pathLaw_initialSegment (K : α → PMF α) (p : PMF α) (T u : ℕ) :
    (pathLaw K p (T + u)).map (initialSegment T u) = pathLaw K p T := by
  induction u with
  | zero =>
    have hi : initialSegment T 0 = (id : (Fin (T + 1) → α) → (Fin (T + 1) → α)) := rfl
    rw [hi, PMF.map_id]
    rfl
  | succ u ih =>
    simp only [Nat.add_succ, pathLaw, PMF.map_bind, PMF.map_comp, Function.comp_def,
      initialSegment_snoc]
    calc
      _ = (pathLaw K p (T + u)).bind (fun h ↦ PMF.pure (initialSegment T u h)) := by
        congr 1
        funext h
        exact PMF.map_const _ _
      _ = _ := ih

def before (H T : ℕ) (hT : T ≤ H) (h : Fin (H + 1) → α) : Fin (T + 1) → α :=
  fun i ↦ h ⟨i.val, by omega⟩

lemma pathLaw_before (K : α → PMF α) (p : PMF α) (H T : ℕ) (hT : T ≤ H) :
    (pathLaw K p H).map (before H T hT) = pathLaw K p T := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hT
  exact pathLaw_initialSegment K p T u

lemma before_last (H : ℕ) (T : Fin (H + 1)) (h : Fin (H + 1) → α) :
    before H T.val (Nat.le_of_lt_succ T.isLt) h (Fin.last T.val) = h T := rfl

end
end Lax343628Proofs.Trajectories
