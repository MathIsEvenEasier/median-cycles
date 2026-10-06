import Antipodal
namespace MedianCycles
open scoped BigOperators

lemma half_nonzero (p : ℕ) (hp : 0<p) : (p : ZMod (2*p))≠0 := by
  have : NeZero (2*p) := ⟨by omega⟩
  intro he
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt (by omega)] at hv
  have : p=0 := by simpa using hv
  omega

lemma half_twice (p : ℕ) : (p : ZMod (2*p))+(p : ZMod (2*p))=0 := by
  rw [← Nat.cast_add, show p+p=2*p by omega]
  exact ZMod.natCast_self _

noncomputable def initial (p : ℕ) (hp : 0<p) : Anti (p : ZMod (2*p)) := by
  have : NeZero (2*p) := ⟨by omega⟩
  refine ⟨fun t => decide (t.val<p), ?_⟩
  intro t
  have ht := ZMod.val_lt t
  have hv : (p : ZMod (2*p)).val=p := ZMod.val_natCast_of_lt (by omega)
  simp only [ZMod.val_add, hv]
  by_cases hl : t.val<p
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp [hl, show ¬t.val+p<p by omega]
  · have he : (t.val+p) % (2*p) = t.val-p := by
      rw [Nat.mod_eq_sub_mod (show 2*p≤t.val+p by omega)]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [he]; simp [hl, show t.val-p<p by omega]

/-- Binary median of the center and a finite family of opposite offset pairs.
Offsets are sampled with multiplicity, including after reduction modulo a period. -/
noncomputable def field {G I : Type*} [AddGroup G] [Fintype I]
    (q : I → G) (y : G → Bool) (v : G) : ℤ :=
  spin (y v) + ∑ i, (spin (y (v+q i))+spin (y (v-q i)))
noncomputable def median {G I : Type*} [AddGroup G] [Fintype I]
    (q : I → G) (y : G → Bool) (v : G) : Bool := decide (0<field q y v)

lemma field_not {G I : Type*} [AddGroup G] [Fintype I] (q : I→G) (y : G→Bool) (v : G) :
    field q (fun t => !y t) v = -field q y v := by
  simp only [field, spin_not, ← neg_add, Finset.sum_neg_distrib]

lemma strict_flip (b : Bool) (s : ℤ) (hs : spin b*s<0) :
    decide (0<s)=!b ∧ decide (0< -s)=b := by
  cases b <;> simp_all [spin] <;> omega

/-- The cyclic construction includes the actual shifts and the majority update. -/
theorem cyclic_two_cycle {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℕ) (hp : 0<p) (q : I→ZMod (2*p)) (e : I)
    (he : q e=(p : ZMod (2*p)))
    (hq : ∀ i, i≠e → q i≠0 ∧ q i≠(p : ZMod (2*p))) :
    ∃ y : ZMod (2*p)→Bool,
      (∀ v, median q y v = !y v) ∧
      (∀ v, median q (fun t => !y t) v=y v) := by
  classical
  have : NeZero (2*p) := ⟨by omega⟩
  let h : ZMod (2*p) := p
  have hh := half_twice p
  obtain ⟨y,hy⟩ := exists_local_min h hh (half_nonzero p hp)
    (Finset.univ.erase e) q
    (fun i hi => (hq i (Finset.mem_erase.mp hi).1).1)
    (fun i hi => (hq i (Finset.mem_erase.mp hi).1).2) (initial p hp)
  have hn : -h=h := by exact (eq_neg_of_add_eq_zero_left hh).symm
  have hf (v) : spin (y.val v)*field q y.val v<0 := by
    have hs := hy v
    have hpairs : spin (y.val (v+q e))+spin (y.val (v-q e)) = -2*spin (y.val v) := by
      rw [he, sub_eq_add_neg, hn, y.property, spin_not]
      ring
    have hsum := Finset.sum_erase_add Finset.univ (fun i => spin (y.val (v+q i))+spin (y.val (v-q i))) (Finset.mem_univ e)
    rw [hpairs] at hsum
    have hsq := spin_sq (y.val v)
    dsimp [field]
    rw [← hsum]
    nlinarith
  refine ⟨y.val, ?_, ?_⟩
  · intro v; exact (strict_flip _ _ (hf v)).1
  · intro v; dsimp [median]; rw [field_not]; exact (strict_flip _ _ (hf v)).2
end MedianCycles
