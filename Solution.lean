module
public import HardyScore
public import HardySpectator

@[expose] public section
namespace HardyFive

/-- The unnormalized terminal Hardy success after maximizing the other settings,
in terms of the three compressed matrices X* D^k X at k=2,6,10. -/
noncomputable def terminalSuccess (d : Weights) (X : Frame) : ℝ :=
  let A := fun k : ℕ => X.conjTranspose * Matrix.diagonal (fun i => ((d i^k : ℝ) : ℂ)) * X
  ((A 2).trace - ((A 10)⁻¹ * (A 6)^2).trace).re

theorem planar_decomposition (x : Rows) (hc : centered x) :
    ∃ l r : Rows, ∃ t : ℝ, 0<t ∧ t<1 ∧ planar l ∧ planar r ∧ centered l ∧ centered r ∧
      (∀ i, gram l i i = gram x i i ∧ gram r i i = gram x i i) ∧
      ∀ i j, gram x i j = t * gram l i j + (1-t) * gram r i j :=
  five_planar_gram_split x hc

theorem real_endpoints_all_spectra (X : Frame) (hX : X.conjTranspose * X = 1) :
    ∃ L R : RealFrame,
      (complexify L).conjTranspose * complexify L = 1 ∧
      (complexify R).conjTranspose * complexify R = 1 ∧
      rowWeight (complexify L) = rowWeight X ∧ rowWeight (complexify R) = rowWeight X ∧
      ∀ d : Weights, (∀ i, 0 < d i) →
        min (terminalSuccess d (complexify L)) (terminalSuccess d (complexify R)) ≤ terminalSuccess d X ∧
        terminalSuccess d X ≤ max (terminalSuccess d (complexify L)) (terminalSuccess d (complexify R)) := by
  simpa only [success,terminalSuccess,compression_matrix] using universal_real_endpoints X hX

namespace Spectator

noncomputable def endpointProbabilities (s : ℝ) : Set ℝ :=
  {p | ∃ m n : ℕ, ∃ a : Fin m → State, ∃ b : Fin n → State,
    Orthonormal ℂ a ∧ Orthonormal ℂ b ∧
    (∀ i j, inner ℂ (weighted (shape s) 5 (a i)) (b j) = 0) ∧
    p = endpointScore (shape s) a b / (54+s^2)}

theorem spectator_curve_maximum {s : ℝ} (hs : 0 < s) (hs' : s ≤ 2) :
    IsGreatest (endpointProbabilities s) ((196784800/21446161)/(54+s^2)) := by
  obtain ⟨ha,hb,hz,hw⟩ := spectator_witness s
  refine ⟨⟨2,2,witness 1,witness (-1),ha,hb,hz,by rw [hw]⟩,?_⟩
  rintro _ ⟨m,n,a,b,hA,hB,hZ,rfl⟩
  exact div_le_div_of_nonneg_right (all_ranks hs hs' a b hA hB hZ) (by positivity)

end Spectator

end HardyFive
#print axioms HardyFive.planar_decomposition
#print axioms HardyFive.real_endpoints_all_spectra

#print axioms HardyFive.Spectator.spectator_curve_maximum
