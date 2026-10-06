import Lattice
namespace MedianCycles
/-- End-to-end result: a genuine periodic two-cycle of the lattice median operator. -/
theorem periodic_median_two_cycle {d : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I]
    (a : I→(Fin d→ℤ)) (ha : ∀ i, a i≠0)
    (hsep : ∀ i j, i≠j → a i≠a j ∧ a i≠ -a j) :
    ∃ (N : ℕ) (x : (Fin d→ℤ)→Bool), 0<N ∧
      (∀ v w, x (v+N • w)=x v) ∧
      median a x≠x ∧ median a (median a x)=x ∧ median a x=(fun v => !x v) := by
  obtain ⟨N,x,hN,hper,hflip,hback⟩ := lattice_two_cycle a ha hsep
  have he : median a x=(fun v => !x v) := funext hflip
  refine ⟨N,x,hN,hper,?_,?_,he⟩
  · rw [he]; exact complement_ne x
  · rw [he]; exact funext hback
end MedianCycles
