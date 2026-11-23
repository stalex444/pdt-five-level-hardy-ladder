module
public import Mathlib

@[expose] public section
namespace HardyFive
open Finset
abbrev Rows := Matrix (Fin 5) (Fin 3) ℝ
abbrev Frame := Matrix (Fin 5) (Fin 2) ℂ
abbrev RealFrame := Matrix (Fin 5) (Fin 2) ℝ
abbrev Weights := Fin 5 → ℝ
def gram (x : Rows) (i j : Fin 5) : ℝ := ∑ k, x i k * x j k
def planar (x : Rows) : Prop := ∃ k, ∀ i, x i k = 0
def centered (x : Rows) : Prop := ∀ k, ∑ i, x i k = 0
def rowWeight (X : Frame) (i : Fin 5) := Complex.normSq (X i 0) + Complex.normSq (X i 1)
def complexify (Y : RealFrame) : Frame := fun i j => (Y i j : ℂ)

/-- The unnormalized terminal Hardy success after maximizing the other settings,
in terms of the three compressed matrices X* D^k X at k=2,6,10. -/
noncomputable def terminalSuccess (d : Weights) (X : Frame) : ℝ :=
  let A := fun k : ℕ => X.conjTranspose * Matrix.diagonal (fun i => ((d i^k : ℝ) : ℂ)) * X
  ((A 2).trace - ((A 10)⁻¹ * (A 6)^2).trace).re

theorem planar_decomposition (x : Rows) (hc : centered x) :
    ∃ l r : Rows, ∃ t : ℝ, 0<t ∧ t<1 ∧ planar l ∧ planar r ∧ centered l ∧ centered r ∧
      (∀ i, gram l i i = gram x i i ∧ gram r i i = gram x i i) ∧
      ∀ i j, gram x i j = t * gram l i j + (1-t) * gram r i j := by sorry

theorem real_endpoints_all_spectra (X : Frame) (hX : X.conjTranspose * X = 1) :
    ∃ L R : RealFrame,
      (complexify L).conjTranspose * complexify L = 1 ∧
      (complexify R).conjTranspose * complexify R = 1 ∧
      rowWeight (complexify L) = rowWeight X ∧ rowWeight (complexify R) = rowWeight X ∧
      ∀ d : Weights, (∀ i, 0 < d i) →
        min (terminalSuccess d (complexify L)) (terminalSuccess d (complexify R)) ≤ terminalSuccess d X ∧
        terminalSuccess d X ≤ max (terminalSuccess d (complexify L)) (terminalSuccess d (complexify R)) := by sorry

namespace Spectator
variable {ι : Type*} [Fintype ι]
noncomputable section
def weighted (d : ι → ℝ) (k : ℕ) (u : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun i => (d i ^ k : ℝ) * u i

/-- Probability summed over orthonormal bases of both outcome-one endpoint spaces. -/
def endpointScore {r s : ℕ} (d : ι → ℝ) (a : Fin r → EuclideanSpace ℂ ι)
    (b : Fin s → EuclideanSpace ℂ ι) : ℝ :=
  ∑ i, ∑ j, ‖inner ℂ (weighted d 1 (a i)) (b j)‖ ^ 2
def shape (s : ℝ) : Fin 5 → ℝ := ![s,2,3,4,5]
abbrev State := EuclideanSpace ℂ (Fin 5)
noncomputable def endpointProbabilities (s : ℝ) : Set ℝ :=
  {p | ∃ m n : ℕ, ∃ a : Fin m → State, ∃ b : Fin n → State,
    Orthonormal ℂ a ∧ Orthonormal ℂ b ∧
    (∀ i j, inner ℂ (weighted (shape s) 5 (a i)) (b j) = 0) ∧
    p = endpointScore (shape s) a b / (54+s^2)}

theorem spectator_curve_maximum {s : ℝ} (hs : 0 < s) (hs' : s ≤ 2) :
    IsGreatest (endpointProbabilities s) ((196784800/21446161)/(54+s^2)) := by sorry
end
end Spectator

end HardyFive
