import Projection
import Cyclic
namespace MedianCycles
open scoped BigOperators

noncomputable def encoding (B : ℤ) (d : ℕ) : (Fin d→ℤ) →+ ℤ where
  toFun := encode B
  map_zero' := encode_zero B d
  map_add' := encode_add B

lemma cast_small_nonzero (p : ℕ) (hp : 0<p) (z : ℤ) (hz : z≠0) (hbound : z.natAbs<p) :
    (z : ZMod (2*p))≠0 ∧ (z : ZMod (2*p))≠(p : ZMod (2*p)) := by
  constructor
  · intro he
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd z (2*p)).mp he
    have hb : z.natAbs < ((2*p : ℕ) : ℤ).natAbs := by simp; omega
    exact hz (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hb)
  · intro he
    have hd : (2*p : ℤ) ∣ (p : ℤ)-z := by
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub z (p:ℤ) (2*p)).mp (by simpa using he)
    have ha : |z| < (p : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hbound
    have hz0 := Int.eq_zero_of_dvd_of_nonneg_of_lt
      (show 0≤(p:ℤ)-z by have := le_abs_self z; omega)
      (show (p:ℤ)-z<2*(p:ℤ) by have := neg_abs_le z; omega) hd
    have := le_abs_self z
    omega

lemma cast_extreme (p : ℕ) (z : ℤ) (hz : z.natAbs=p) :
    (z : ZMod (2*p))=(p : ZMod (2*p)) := by
  have ha : |z|=(p:ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hz
  rcases eq_or_eq_neg_of_abs_eq ha with he|he
  · rw [he]; simp
  · rw [he, Int.cast_neg, Int.cast_natCast]
    have hh := half_twice p
    linear_combination -hh

/-- Every family of nonzero lattice offsets distinct up to sign has a periodic
configuration that changes every pixel at each synchronous binary median step. -/
theorem lattice_two_cycle_bounded {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (a : I→(Fin d→ℤ)) (M : ℕ) (hM : ∀ i j, |a i j|≤M)
    (ha : ∀ i, a i≠0)
    (hsep : ∀ i j, i≠j → a i≠a j ∧ a i≠ -a j) :
    ∃ (N : ℕ) (x : (Fin d→ℤ)→Bool), 2≤N ∧ N≤(2*M+1)^d-1 ∧
      (∀ v w, x (v+N • w)=x v) ∧
      (∀ v, median a x v = !x v) ∧
      (∀ v, median a (fun t => !x t) v = x v) := by
  classical
  let L := encoding (2*(M:ℤ)+1) d
  let z : I→ℤ := fun i => L (a i)
  have hz (i) : z i≠0 := by
    intro he
    apply ha i
    exact encode_injective_box M (a i) 0 (hM i) (by simp) (by simpa [z,L,encoding] using he)
  have hdistinct (i j) (hij : i≠j) : (z i).natAbs≠(z j).natAbs := by
    intro he
    have hab : |z i|=|z j| := by rw [← Int.natCast_natAbs, ← Int.natCast_natAbs]; exact_mod_cast he
    rcases abs_eq_abs.mp hab with hs|hs
    · apply (hsep i j hij).1
      exact encode_injective_box M _ _ (hM i) (hM j) hs
    · apply (hsep i j hij).2
      apply encode_injective_box M _ _ (hM i) (by intro k; simpa using hM j k)
      rw [encode_neg]
      exact hs
  obtain ⟨e, he⟩ := Finite.exists_max (fun i => (z i).natAbs)
  let p := (z e).natAbs
  have hp : 0<p := Int.natAbs_pos.mpr (hz e)
  let Q : (Fin d→ℤ) →+ ZMod (2*p) := (Int.castAddHom (ZMod (2*p))).comp L
  let q : I→ZMod (2*p) := fun i => Q (a i)
  have hqe : q e=(p : ZMod (2*p)) := cast_extreme p (z e) rfl
  have hq i (hie : i≠e) : q i≠0 ∧ q i≠(p : ZMod (2*p)) := by
    apply cast_small_nonzero p hp (z i) (hz i)
    exact lt_of_le_of_ne (he i) (hdistinct i e hie)
  obtain ⟨y,hy,hy'⟩ := cyclic_two_cycle p hp q e hqe hq
  let x : (Fin d→ℤ)→Bool := fun v => y (Q v)
  have pull (v) : field a x v = field q y (Q v) := by
    simp [field,x,q,map_add,map_sub]
  have pull' (v) : field a (fun t => !x t) v = field q (fun t => !y t) (Q v) := by
    simp [field,x,q,map_add,map_sub]
  have hbound : 2*p≤(2*M+1)^d-1 := by
    have hb := encode_bound M (a e) (hM e)
    have hab : |encode (2*(M:ℤ)+1) (a e)|=(p:ℤ) := by
      rw [← Int.natCast_natAbs]; rfl
    rw [hab] at hb
    have hb' : (2*p+1 : ℕ) ≤ (2*M+1)^d := by
      have hi : (2*(p:ℤ)+1)≤(2*(M:ℤ)+1)^d := by linarith
      exact_mod_cast hi
    omega
  refine ⟨2*p,x,by omega,hbound,?_,?_,?_⟩
  · intro v w
    dsimp [x]
    rw [map_add,map_nsmul]
    have hperiod : (2*p) • Q w=0 := by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hperiod,add_zero]
  · intro v; simpa only [median, pull] using hy (Q v)
  · intro v; simpa only [median, pull'] using hy' (Q v)

/-- Existence without requiring a coordinate bound as input. -/
theorem lattice_two_cycle {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (a : I→(Fin d→ℤ)) (ha : ∀ i, a i≠0)
    (hsep : ∀ i j, i≠j → a i≠a j ∧ a i≠ -a j) :
    ∃ (N : ℕ) (x : (Fin d→ℤ)→Bool), 0<N ∧
      (∀ v w, x (v+N • w)=x v) ∧
      (∀ v, median a x v = !x v) ∧
      (∀ v, median a (fun t => !x t) v = x v) := by
  classical
  let M : ℕ := (Finset.univ.product Finset.univ).sup (fun ij : I×Fin d => (a ij.1 ij.2).natAbs)
  have hM (i : I) (j : Fin d) : |a i j| ≤ (M:ℤ) := by
    have hb : (a i j).natAbs ≤ M := Finset.le_sup (s := Finset.univ.product Finset.univ) (b := (i,j)) (f := fun ij : I×Fin d => (a ij.1 ij.2).natAbs) (Finset.mem_product.mpr ⟨Finset.mem_univ i,Finset.mem_univ j⟩)
    rw [← Int.natCast_natAbs]
    exact_mod_cast hb
  obtain ⟨N,x,hN,_,hper,hflip,hback⟩ := lattice_two_cycle_bounded a M hM ha hsep
  exact ⟨N,x,by omega,hper,hflip,hback⟩

/-- The two configurations in the theorem are different. -/
theorem complement_ne {d : ℕ} (x : (Fin d→ℤ)→Bool) : (fun v => !x v)≠x := by
  intro h
  have he := congrFun h 0
  cases x 0 <;> simp_all
end MedianCycles
