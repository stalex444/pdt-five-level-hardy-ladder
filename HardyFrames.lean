module
public import HardyFive

@[expose] public section
namespace HardyFive
open Finset
abbrev Frame := Matrix (Fin 5) (Fin 2) ℂ
abbrev RealFrame := Matrix (Fin 5) (Fin 2) ℝ

def rowWeight (X : Frame) (i : Fin 5) := Complex.normSq (X i 0) + Complex.normSq (X i 1)

def bloch (X : Frame) : Rows := fun i => ![
  2*((X i 0).re*(X i 1).re + (X i 0).im*(X i 1).im),
  2*((X i 0).re*(X i 1).im - (X i 0).im*(X i 1).re),
  Complex.normSq (X i 0) - Complex.normSq (X i 1)]

def complexify (Y : RealFrame) : Frame := fun i j => (Y i j : ℂ)

noncomputable def frameScore (d : Weights) (X : Frame) := hardy (rowWeight X) d (bloch X)

theorem bloch_admissible (X : Frame) (h : X.conjTranspose * X = 1) :
    admissible (rowWeight X) (bloch X) := by
  have entry (a b : Fin 2) := congrFun (congrFun h a) b
  have colNorm (a : Fin 2) : ∑ i, Complex.normSq (X i a) = 1 := by
    have hh := congrArg Complex.re (entry a a)
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.normSq_apply,
      Complex.mul_re, Matrix.one_apply] using hh
  have crossRe := congrArg Complex.re (entry 0 1)
  have crossIm := congrArg Complex.im (entry 0 1)
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im] at crossRe crossIm
  refine ⟨?_, fun i => add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _), ?_, ?_⟩
  · intro k
    fin_cases k
    · simp [bloch, ← Finset.mul_sum, crossRe]
    · simp [bloch, ← Finset.mul_sum, sub_eq_add_neg, crossIm]
    · simp [bloch,Finset.sum_sub_distrib,colNorm]
  · simp [rowWeight,Finset.sum_add_distrib,colNorm]
    norm_num
  · intro i
    simp [gram,bloch,rowWeight,Fin.sum_univ_succ,Complex.normSq_apply]
    ring

/-- Real factorization of one planar Bloch vector, including poles and zero rows. -/
theorem real_factor {p u v : ℝ} (hp : 0 ≤ p) (h : u^2 + v^2 = p^2) :
    ∃ a b : ℝ, a^2+b^2=p ∧ 2*a*b=u ∧ a^2-b^2=v := by
  have hLo : -p ≤ v := by nlinarith [sq_nonneg u, sq_nonneg (v+p)]
  have hHi : v ≤ p := by nlinarith [sq_nonneg u, sq_nonneg (v-p)]
  by_cases hpos : 0 < p+v
  · let a := Real.sqrt ((p+v)/2)
    let b := u/(2*a)
    have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
    have ha2 : a^2=(p+v)/2 := Real.sq_sqrt (by linarith)
    have hab : 2*a*b = u := by dsimp [b]; field_simp
    have hb2 : b^2=(p-v)/2 := by
      apply (mul_left_cancel₀ (show 4*a^2 ≠ 0 by positivity))
      calc
        4*a^2*b^2 = (2*a*b)^2 := by ring
        _ = u^2 := by rw [hab]
        _ = 4*a^2*((p-v)/2) := by rw [ha2]; nlinarith
    exact ⟨a,b,by linarith,hab,by linarith⟩
  · have hv : v = -p := by linarith
    have hu : u = 0 := by rw [hv] at h; nlinarith [sq_nonneg u]
    exact ⟨0,Real.sqrt p,by simp [Real.sq_sqrt hp],by simp [hu],
      by simp [Real.sq_sqrt hp,hv]⟩

def orient (z : Rows) (s : Equiv.Perm (Fin 3)) : Rows := fun i k => z i (s k)

theorem gram_orient (z : Rows) (s : Equiv.Perm (Fin 3)) (i j : Fin 5) :
    gram (orient z s) i j = gram z i j := Equiv.sum_comp s (fun k => z i k * z j k)

theorem realize_planar (p : Weights) (y : Rows) (hy : admissible p y) (hp : planar y) :
    ∃ Y : RealFrame, (complexify Y).conjTranspose * complexify Y = 1 ∧
      rowWeight (complexify Y) = p ∧
      ∀ i j, gram (bloch (complexify Y)) i j = gram y i j := by
  obtain ⟨k,hk⟩ := hp
  let s := Equiv.swap (1 : Fin 3) k
  let z := orient y s
  have h1 (i : Fin 5) : z i 1 = 0 := by simp [z,orient,s,hk]
  have hz : centered z := fun j => hy.1 (s j)
  have norms (i : Fin 5) : (z i 0)^2 + (z i 2)^2 = (p i)^2 := by
    have hh := (gram_orient y s i i).trans (hy.2.2.2 i)
    change gram z i i = _ at hh
    simpa [gram,Fin.sum_univ_succ,h1,sq] using hh
  choose a b hn hx hv using fun i => real_factor (hy.2.1 i) (norms i)
  let Y : RealFrame := fun i => ![a i,b i]
  have weights : rowWeight (complexify Y) = p := by
    funext i
    simpa [rowWeight,complexify,Y,Complex.normSq_apply,sq] using hn i
  have vectors : bloch (complexify Y) = z := by
    ext i j
    fin_cases j
    · simpa [bloch,complexify,Y,mul_assoc] using hx i
    · simp [bloch,complexify,Y,h1]
    · simpa [bloch,complexify,Y,Complex.normSq_apply,sq] using hv i
  have plus : (∑ i, a i^2) + (∑ i, b i^2) = 2 := by
    simpa only [← Finset.sum_add_distrib,hn] using hy.2.2.1
  have minus : (∑ i, a i^2) - (∑ i, b i^2) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simp only [hv,hz 2]
  have cross : (∑ i, a i*b i) = 0 := by
    have aux : (2:ℝ) * ∑ i, a i*b i = 0 := by
      rw [Finset.mul_sum]
      simpa only [← mul_assoc,hx] using hz 0
    linarith
  have ha : ∑ i, a i^2 = 1 := by linarith
  have hb : ∑ i, b i^2 = 1 := by linarith
  refine ⟨Y,?_,weights, fun i j => by rw [vectors]; exact gram_orient y s i j⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,complexify,Y,
      ← Complex.ofReal_mul,← Complex.ofReal_sum,← sq,← Complex.ofReal_pow,ha,hb,cross,mul_comm]

theorem hardy_of_same_gram (p d : Weights) (x y : Rows)
    (hg : ∀ i j, gram x i j = gram y i j) : hardy p d x = hardy p d y := by
  simp only [hardy,numerator,moment,deficit,hg]

end HardyFive
