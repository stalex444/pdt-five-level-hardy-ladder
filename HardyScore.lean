module
public import HardyFrames

@[expose] public section
namespace HardyFive
open Matrix Finset
abbrev Two := Matrix (Fin 2) (Fin 2) ℂ

/-- Rank-one contribution of a single Schmidt coordinate. -/
def block (X : Frame) (i : Fin 5) : Two := fun a b => star (X i a) * X i b

/-- Weighted row sum, equivalently the compression X* D^k X. -/
def compressed (X : Frame) (d : Weights) (k : ℕ) : Two :=
  ∑ i, ((d i^k : ℝ) : ℂ) • block X i

theorem compression_matrix (X : Frame) (d : Weights) (k : ℕ) :
    compressed X d k = X.conjTranspose * Matrix.diagonal (fun i => ((d i^k : ℝ) : ℂ)) * X := by
  ext a b
  change (∑ i, ((d i ^ k : ℝ) : ℂ) • block X i) a b = ∑ i, _ * X i b
  simp only [Matrix.sum_apply, Matrix.smul_apply,smul_eq_mul,Matrix.mul_diagonal,
    Matrix.conjTranspose_apply,block]
  apply Finset.sum_congr rfl
  intro i _
  ring

def mixed (A B : Two) : ℂ := A 0 0 * B 1 1 + A 1 1 * B 0 0 - A 0 1 * B 1 0 - A 1 0 * B 0 1

theorem mixed_sum_left (f : Fin 5 → Two) (b : Two) : mixed (∑ i, f i) b = ∑ i, mixed (f i) b := by
  simp [mixed,Matrix.sum_apply,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_mul]

theorem mixed_sum_right (a : Two) (f : Fin 5 → Two) : mixed a (∑ i, f i) = ∑ i, mixed a (f i) := by
  simp [mixed,Matrix.sum_apply,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.mul_sum]

theorem mixed_scale (a b : ℂ) (A B : Two) : mixed (a • A) (b • B) = a*b*mixed A B := by
  simp [mixed]; ring

theorem mixed_block (X : Frame) (i j : Fin 5) :
    mixed (block X i) (block X j) =
      ((deficit (rowWeight X) (bloch X) i j : ℝ) : ℂ) / 2 := by
  apply (eq_div_iff (by norm_num)).mpr
  apply Complex.ext <;>
    simp [mixed,block,deficit,gram,bloch,rowWeight,Fin.sum_univ_succ,Complex.normSq_apply,
      Complex.mul_re,Complex.mul_im] <;> ring

theorem moment_mixed (X : Frame) (d : Weights) (a b : ℕ) :
    mixed (compressed X d a) (compressed X d b) =
      ((moment (rowWeight X) d (bloch X) a b : ℝ) : ℂ) / 2 := by
  unfold compressed moment
  simp only [mixed_sum_left,mixed_sum_right,mixed_scale,mixed_block,Complex.ofReal_sum,
    Complex.ofReal_mul,Finset.sum_div]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem moment_det (X : Frame) (d : Weights) (a : ℕ) :
    (compressed X d a).det = ((moment (rowWeight X) d (bloch X) a a : ℝ) : ℂ)/4 := by
  have h := moment_mixed X d a a
  simp only [mixed,Matrix.det_fin_two] at *
  linear_combination h/2

theorem moment_trace (X : Frame) (d : Weights) (k : ℕ) :
    (compressed X d k).trace = ((trMoment (rowWeight X) d k : ℝ) : ℂ) := by
  simp only [compressed,Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul,trMoment,
    Complex.ofReal_sum,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]
  congr 1
  apply Complex.ext <;>
    simp [Matrix.trace_fin_two,block,rowWeight,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem trace_adj_square (A B : Two) :
    (A.adjugate * B^2).trace = B.trace * mixed A B - B.det * A.trace := by
  simp only [Matrix.adjugate_fin_two,Matrix.det_fin_two,sq,Matrix.trace_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two,mixed]
  simp
  ring

/-- The unnormalized subspace success using the five-zero Hardy compressions. -/
noncomputable def success (d : Weights) (X : Frame) : ℝ :=
  ((compressed X d 2).trace - ((compressed X d 10)⁻¹ * (compressed X d 6)^2).trace).re

theorem success_eq_score (X : Frame) (hX : X.conjTranspose * X = 1) (d : Weights) (hd : ∀ i, 0<d i) :
    success d X = frameScore d X := by
  let p := rowWeight X
  let x := bloch X
  have hp := moment_pos (bloch_admissible X hX) hd 10 10
  have hn : ((moment p d x 10 10 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have inv : (compressed X d 10)⁻¹ = (compressed X d 10).det⁻¹ • (compressed X d 10).adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  have hcomplex : (compressed X d 2).trace - ((compressed X d 10)⁻¹ * (compressed X d 6)^2).trace =
      ((frameScore d X : ℝ) : ℂ) := by
    rw [inv,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,trace_adj_square]
    simp only [moment_trace,moment_det,moment_mixed,frameScore,hardy,numerator,
      Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
    change _ = (_ : ℂ) / ((moment p d x 10 10 : ℝ) : ℂ)
    change _ - (((moment p d x 10 10 : ℝ) : ℂ)/4)⁻¹ * _ = _
    field_simp [hn]; ring
  exact congrArg Complex.re hcomplex

/-- The two real competitors may be chosen once for all positive Schmidt
spectra. The order of their two scores is allowed to depend on the spectrum. -/
theorem universal_real_endpoints (X : Frame) (hX : X.conjTranspose * X = 1) :
    ∃ L R : RealFrame,
      (complexify L).conjTranspose * complexify L = 1 ∧
      (complexify R).conjTranspose * complexify R = 1 ∧
      rowWeight (complexify L) = rowWeight X ∧ rowWeight (complexify R) = rowWeight X ∧
      ∀ d : Weights, (∀ i, 0 < d i) →
        min (success d (complexify L)) (success d (complexify R)) ≤ success d X ∧
        success d X ≤ max (success d (complexify L)) (success d (complexify R)) := by
  have hx := bloch_admissible X hX
  obtain ⟨l,r,t,ht,ht',hl,hr,hcl,hcr,hn,hm⟩ := five_planar_gram_split _ hx.1
  have al : admissible (rowWeight X) l :=
    ⟨hcl,hx.2.1,hx.2.2.1,fun i => (hn i).1.trans (hx.2.2.2 i)⟩
  have ar : admissible (rowWeight X) r :=
    ⟨hcr,hx.2.1,hx.2.2.1,fun i => (hn i).2.trans (hx.2.2.2 i)⟩
  obtain ⟨L,hL,wL,gL⟩ := realize_planar _ l al hl
  obtain ⟨R,hR,wR,gR⟩ := realize_planar _ r ar hr
  refine ⟨L,R,hL,hR,wL,wR,fun d hd => ?_⟩
  simp only [success_eq_score _ hL d hd,success_eq_score _ hR d hd,success_eq_score _ hX d hd,
    frameScore,wL,wR,hardy_of_same_gram _ d _ l gL,hardy_of_same_gram _ d _ r gR]
  exact score_on_segment _ d _ l r t ht.le ht'.le al ar hd hm

end HardyFive
