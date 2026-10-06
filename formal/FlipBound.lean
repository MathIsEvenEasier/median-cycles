import Cyclic
namespace MedianCycles
open scoped BigOperators
section FiniteGroup
variable {G I : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable (h : G) (S : Finset I) (q : I→G)

noncomputable def totalEnergy (y : Anti h) : ℤ := ∑ i ∈ S, energy h y (q i)

/-- Number of remaining samples that disagree with the center, with multiplicity. -/
def cross (y : Anti h) (v : G) : ℕ :=
  ∑ i ∈ S, ((if y.val v ≠ y.val (v+q i) then 1 else 0) +
    (if y.val v ≠ y.val (v-q i) then 1 else 0))

omit [Fintype G] [DecidableEq G] in
lemma local_cross (y : Anti h) (v : G) :
    spin (y.val v)*(∑ i ∈ S, (spin (y.val (v+q i))+spin (y.val (v-q i)))) =
      2*(S.card:ℤ)-2*(cross h S q y v:ℤ) := by
  have point (i : I) : spin (y.val v)*(spin (y.val (v+q i))+spin (y.val (v-q i))) =
      2-2*((if y.val v ≠ y.val (v+q i) then (1:ℕ) else 0)+
        (if y.val v ≠ y.val (v-q i) then 1 else 0) : ℕ) := by
    cases y.val v <;> cases y.val (v+q i) <;> cases y.val (v-q i) <;> norm_num [spin]
  rw [Finset.mul_sum]
  simp_rw [point]
  simp [cross, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

lemma total_flip (hh : h+h=0) (hn : h≠0)
    (hzero : ∀ i ∈ S, q i≠0) (hanti : ∀ i ∈ S, q i≠h) (y : Anti h) (v : G) :
    totalEnergy h S q (flip h hh y v)-totalEnergy h S q y =
      -8*((S.card:ℤ)-(cross h S q y v:ℤ)) := by
  have hd : totalEnergy h S q (flip h hh y v)-totalEnergy h S q y =
      -4*(spin (y.val v)*(∑ i ∈ S, (spin (y.val (v+q i))+spin (y.val (v-q i))))) := by
    unfold totalEnergy
    rw [← Finset.sum_sub_distrib]
    apply Eq.trans (Finset.sum_congr rfl (fun i hi => energy_flip h hh hn y v _ (hzero i hi) (hanti i hi)))
    rw [← Finset.mul_sum]; ring
  rw [hd, local_cross]
  ring

lemma improving_drop (hh : h+h=0) (hn : h≠0)
    (hzero : ∀ i ∈ S, q i≠0) (hanti : ∀ i ∈ S, q i≠h) (y : Anti h) (v : G)
    (himprove : cross h S q y v<S.card) :
    totalEnergy h S q (flip h hh y v) ≤ totalEnergy h S q y-8 := by
  have hd := total_flip h S q hh hn hzero hanti y v
  have hc : (cross h S q y v:ℤ)<(S.card:ℤ) := by exact_mod_cast himprove
  omega

omit [DecidableEq G] in
lemma energy_bounds (y : Anti h) (z : G) :
    -(Fintype.card G:ℤ)≤energy h y z ∧ energy h y z≤(Fintype.card G:ℤ) := by
  have hpoint (t : G) : (-1:ℤ)≤spin (y.val t)*spin (y.val (t+z)) ∧
      spin (y.val t)*spin (y.val (t+z))≤1 := by
    cases y.val t <;> cases y.val (t+z) <;> norm_num [spin]
  constructor
  · have hb := Finset.sum_le_sum (s := Finset.univ) (fun t _ => (hpoint t).1)
    simpa [energy] using hb
  · have hb := Finset.sum_le_sum (s := Finset.univ) (fun t _ => (hpoint t).2)
    simpa [energy] using hb

omit [DecidableEq G] in
lemma total_bounds (y : Anti h) :
    -((S.card:ℤ)*(Fintype.card G:ℤ))≤totalEnergy h S q y ∧
      totalEnergy h S q y≤(S.card:ℤ)*(Fintype.card G:ℤ) := by
  constructor
  · have hb := Finset.sum_le_sum (s := S) (fun i _ => (energy_bounds h y (q i)).1)
    simpa [totalEnergy, nsmul_eq_mul] using hb
  · have hb := Finset.sum_le_sum (s := S) (fun i _ => (energy_bounds h y (q i)).2)
    simpa [totalEnergy, nsmul_eq_mul] using hb
end FiniteGroup

lemma telescoping_drop (E : ℕ→ℤ) (n : ℕ) (hstep : ∀ j<n, E (j+1)≤E j-8) :
    E n≤E 0-8*(n:ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb := ih (fun j hj => hstep j (by omega))
    have hs := hstep n (by omega)
    push_cast
    omega

/-- Any actual sequence of improving antipodal flips has at most floor(p*k/2)
steps, where k is the number of remaining offset pairs. -/
theorem cyclic_improving_flip_bound {I : Type*} (p : ℕ) (hp : 0<p)
    (S : Finset I) (q : I→ZMod (2*p))
    (hzero : ∀ i ∈ S, q i≠0) (hanti : ∀ i ∈ S, q i≠(p : ZMod (2*p)))
    (y : ℕ→Anti (p : ZMod (2*p))) (v : ℕ→ZMod (2*p)) (n : ℕ)
    (hstep : ∀ j<n, y (j+1)=flip (p : ZMod (2*p)) (half_twice p) (y j) (v j))
    (himprove : ∀ j<n, cross (p : ZMod (2*p)) S q (y j) (v j)<S.card) :
    n≤p*S.card/2 := by
  have : NeZero (2*p) := ⟨by omega⟩
  have hs : ∀ j<n, totalEnergy (p : ZMod (2*p)) S q (y (j+1))≤
      totalEnergy (p : ZMod (2*p)) S q (y j)-8 := by
    intro j hj
    rw [hstep j hj]
    exact improving_drop _ S q (half_twice p) (half_nonzero p hp) hzero hanti _ _ (himprove j hj)
  have hd := telescoping_drop (fun j => totalEnergy (p : ZMod (2*p)) S q (y j)) n hs
  have hlo := (total_bounds (p : ZMod (2*p)) S q (y n)).1
  have hhi := (total_bounds (p : ZMod (2*p)) S q (y 0)).2
  have hcard : Fintype.card (ZMod (2*p))=2*p := ZMod.card (2*p)
  rw [hcard] at hlo hhi
  have hb : 2*(n:ℤ)≤(p:ℤ)*(S.card:ℤ) := by push_cast at hlo hhi; nlinarith
  have hb' : 2*n≤p*S.card := by exact_mod_cast hb
  omega
end MedianCycles
