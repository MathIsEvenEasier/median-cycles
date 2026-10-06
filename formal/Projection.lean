import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
namespace MedianCycles

def encode (B : ℤ) : {d : ℕ} → (Fin d → ℤ) → ℤ
  | 0, _ => 0
  | _+1, v => v 0 + B * encode B (fun j => v j.succ)

@[simp] theorem encode_zero (B : ℤ) (d : ℕ) : encode B (0 : Fin d → ℤ) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change 0+B*encode B (0 : Fin d→ℤ)=0
    rw [ih]; ring

@[simp] theorem encode_add (B : ℤ) {d : ℕ} (u v : Fin d → ℤ) :
    encode B (u+v) = encode B u + encode B v := by
  induction d with
  | zero => simp [encode]
  | succ d ih =>
    have ht := ih (fun j => u j.succ) (fun j => v j.succ)
    change encode B (fun j => u j.succ+v j.succ) = _ at ht
    simp only [encode, Pi.add_apply]
    rw [ht]; ring

@[simp] theorem encode_neg (B : ℤ) {d : ℕ} (u : Fin d → ℤ) :
    encode B (-u) = -encode B u := by
  have h := encode_add B u (-u)
  simp only [add_neg_cancel, encode_zero] at h
  linarith

/-- Balanced-base digits bounded by M are unique. -/
theorem encode_injective_box (M : ℕ) {d : ℕ} (u v : Fin d → ℤ)
    (hu : ∀ j, |u j| ≤ M) (hv : ∀ j, |v j| ≤ M)
    (he : encode (2*M+1) u = encode (2*M+1) v) : u=v := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    have hd : (2*(M:ℤ)+1) ∣ u 0-v 0 := by
      use encode (2*M+1) (fun j => v j.succ)-encode (2*M+1) (fun j => u j.succ)
      simp only [encode] at he
      linear_combination he
    have hr : |u 0-v 0| < 2*(M:ℤ)+1 := by
      have ha := (abs_le.mp (hu 0)); have hb := (abs_le.mp (hv 0))
      rw [abs_lt]; constructor <;> omega
    have hz : u 0-v 0=0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by
      have hpos : 0<2*(M:ℤ)+1 := by omega
      have hb : |u 0-v 0| < |2*(M:ℤ)+1| := by rw [abs_of_pos hpos]; exact hr
      rw [← Int.natCast_natAbs, ← Int.natCast_natAbs] at hb
      exact_mod_cast hb)
    have hhead : u 0=v 0 := sub_eq_zero.mp hz
    have htail : (fun j : Fin d => u j.succ)=(fun j : Fin d => v j.succ) := by
      apply ih _ _ (fun j => hu j.succ) (fun j => hv j.succ)
      simp only [encode] at he
      nlinarith
    funext j
    refine Fin.cases hhead (fun k => congrFun htail k) j
end MedianCycles
