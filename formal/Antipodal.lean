import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MedianCycles
open scoped BigOperators

def spin (b : Bool) : ℤ := if b then 1 else -1
@[simp] theorem spin_not (b : Bool) : spin (!b) = -spin b := by cases b <;> rfl
@[simp] theorem spin_sq (b : Bool) : spin b * spin b = 1 := by cases b <;> norm_num [spin]

abbrev Anti {G : Type*} [Add G] (h : G) := {y : G → Bool // ∀ t, y (t+h) = !y t}

section Group
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable (h : G)

abbrev pair (v t : G) : Prop := t=v ∨ t=v+h

omit [Fintype G] [DecidableEq G] in
lemma pair_add (hh : h+h=0) (v t : G) : pair h v (t+h) ↔ pair h v t := by
  dsimp [pair]
  constructor
  · rintro (ha|ha)
    · right; calc t = (t+h)+h := by rw [add_assoc, hh, add_zero]
                 _ = v+h := by rw [ha]
    · left; exact add_right_cancel ha
  · rintro (rfl|rfl)
    · exact Or.inr rfl
    · left; simp [add_assoc,hh]

noncomputable def flip (hh : h+h=0) (y : Anti h) (v : G) : Anti h := by
  classical
  refine ⟨fun t => if pair h v t then !y.val t else y.val t, ?_⟩
  intro t
  simp only [pair_add h hh, y.property]
  split_ifs <;> simp

omit [Fintype G] in
lemma spin_flip (hh : h+h=0) (y : Anti h) (v t : G) :
    spin ((flip h hh y v).val t) = if pair h v t then -spin (y.val t) else spin (y.val t) := by
  classical
  simp only [flip]; split_ifs <;> simp

omit [Fintype G] [DecidableEq G] in
lemma pair_no_edge (hh : h+h=0) (q : G) (hq : q≠0) (hqh : q≠h) (v t : G) :
    ¬ (pair h v t ∧ pair h v (t+q)) := by
  rintro ⟨(rfl|rfl),(hb|hb)⟩
  · exact hq (add_left_cancel (hb.trans (add_zero _).symm))
  · exact hqh (add_left_cancel hb)
  · have : q=h := by calc
      q = (v+h+q)-v-h := by abel
      _ = -h := by rw [hb]; abel
      _ = h := by exact (eq_neg_of_add_eq_zero_left hh).symm
    exact hqh this
  · exact hq (add_left_cancel (hb.trans (add_zero (v+h)).symm))

lemma sum_pair (hn : h≠0) (f : G → ℤ) (v : G) :
    (∑ t, if pair h v t then f t else 0) = f v + f (v+h) := by
  classical
  have hv : v≠v+h := by intro he; exact hn (add_left_cancel (show v+0=v+h by simpa using he)).symm
  have he : ∀ t, (if pair h v t then f t else 0) =
      (if t=v then f t else 0)+(if t=v+h then f t else 0) := by
    intro t; dsimp [pair]; split_ifs <;> grind
  simp_rw [he]
  simp [Finset.sum_add_distrib]

noncomputable def energy (y : Anti h) (q : G) : ℤ :=
  ∑ t, spin (y.val t) * spin (y.val (t+q))

lemma energy_flip (hh : h+h=0) (hn : h≠0) (y : Anti h) (v q : G) (hq : q≠0) (hqh : q≠h) :
    energy h (flip h hh y v) q - energy h y q =
      -4 * spin (y.val v) * (spin (y.val (v+q))+spin (y.val (v-q))) := by
  classical
  let f : G → ℤ := fun t => spin (y.val t)*spin (y.val (t+q))
  have point (t : G) :
      spin ((flip h hh y v).val t)*spin ((flip h hh y v).val (t+q))-f t =
      -2*(if pair h v t then f t else 0)-2*(if pair h v (t+q) then f t else 0) := by
    rw [spin_flip,spin_flip]
    have hno := pair_no_edge h hh q hq hqh v t
    dsimp [f]; split_ifs <;> first | (exfalso; apply hno; constructor <;> assumption) | ring
  have shift : (∑ t, if pair h v (t+q) then f t else 0) =
      ∑ u, if pair h v u then f (u-q) else 0 := by
    apply Fintype.sum_equiv (Equiv.addRight q)
    intro t; simp
  have two (t : G) : f (t+h) = f t := by
    dsimp [f]
    rw [y.property, show t+h+q=(t+q)+h by abel, y.property]
    simp
  have shifted : f (v+h-q)=f (v-q) := by
    rw [show v+h-q=(v-q)+h by abel, two]
  change (∑ t, spin ((flip h hh y v).val t)*spin ((flip h hh y v).val (t+q))) - (∑ t, f t) = _
  rw [← Finset.sum_sub_distrib]
  simp_rw [point]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, shift,
    sum_pair h hn f v, sum_pair h hn (fun u => f (u-q)) v, two, shifted]
  dsimp [f]
  rw [sub_add_cancel]
  ring

/-- A finite energy minimum supplies all remaining-neighbor inequalities at once. -/
theorem exists_local_min (hh : h+h=0) (hn : h≠0) {I : Type*} (S : Finset I) (q : I → G)
    (hzero : ∀ i ∈ S, q i ≠ 0) (hanti : ∀ i ∈ S, q i ≠ h) (y₀ : Anti h) :
    ∃ y : Anti h, ∀ v,
      spin (y.val v) * (∑ i ∈ S, (spin (y.val (v+q i))+spin (y.val (v-q i)))) ≤ 0 := by
  classical
  have : Nonempty (Anti h) := ⟨y₀⟩
  obtain ⟨y, hy⟩ := Finite.exists_min (fun y : Anti h => ∑ i ∈ S, energy h y (q i))
  refine ⟨y, fun v => ?_⟩
  have hm := hy (flip h hh y v)
  have hd : (∑ i ∈ S, energy h (flip h hh y v) (q i)) - (∑ i ∈ S, energy h y (q i)) =
      -4 * (spin (y.val v) * (∑ i ∈ S, (spin (y.val (v+q i))+spin (y.val (v-q i))))) := by
    rw [← Finset.sum_sub_distrib]
    apply Eq.trans (Finset.sum_congr rfl (fun i hi => energy_flip h hh hn y v _ (hzero i hi) (hanti i hi)))
    rw [← Finset.mul_sum]; ring
  nlinarith
end Group
end MedianCycles
