module
public import Mathlib

@[expose] public section
namespace HardyFive
open Finset
abbrev Row := Fin 3 → ℝ
abbrev Coeff := Fin 6 → ℝ

/-- Coefficients of a symmetric quadratic form at one real three-vector. -/
def monomials (x : Row) : Coeff :=
  ![x 0*x 0, x 1*x 1, x 2*x 2, 2*x 0*x 1, 2*x 0*x 2, 2*x 1*x 2]

def quad (c : Coeff) (x : Row) : ℝ := ∑ k, c k * monomials x k

/-- Five row lengths impose at most five linear conditions on six coefficients. -/
theorem five_constraints (x : Fin 5 → Row) :
    ∃ c : Coeff, c ≠ 0 ∧ ∀ i, quad c (x i) = 0 := by
  let f : Coeff →ₗ[ℝ] (Fin 5 → ℝ) :=
    { toFun := fun c i => quad c (x i)
      map_add' := by intro a b; ext i; simp [quad,add_mul,Finset.sum_add_distrib]
      map_smul' := by intro a b; ext i; simp [quad,Finset.mul_sum,mul_assoc] }
  have hk : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    simp)
  obtain ⟨c, hc, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨c,hn,fun i => congrFun (LinearMap.mem_ker.mp hc) i⟩

/-- Once the perturbation is diagonalized, these are the two endpoint
metrics. Each is positive semidefinite and has a zero eigenvalue. The
identity is a strict convex combination of them. -/
theorem boundary_metrics (eigen : Row) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (lower : ∀ k, a ≤ eigen k) (upper : ∀ k, eigen k ≤ b)
    (amin : ∃ k, eigen k = a) (bmax : ∃ k, eigen k = b) :
    let L := fun k => 1-eigen k/b
    let R := fun k => 1-eigen k/a
    let θ := b/(b-a)
    (0<θ ∧ θ<1) ∧ (∀ k, 0 ≤ L k ∧ 0 ≤ R k) ∧
      (∃ k, L k=0) ∧ (∃ k, R k=0) ∧ ∀ k, θ*L k+(1-θ)*R k=1 := by
  dsimp only
  have hba : 0 < b-a := by linarith
  refine ⟨⟨div_pos hb hba,(div_lt_one hba).2 (by linarith)⟩,?_,?_,?_,?_⟩
  · intro k
    exact ⟨sub_nonneg.mpr ((div_le_one hb).mpr (upper k)),
      sub_nonneg.mpr ((div_le_iff_of_neg ha).mpr (by simpa using lower k))⟩
  · obtain ⟨k,h⟩ := bmax
    exact ⟨k,by rw [h,div_self hb.ne',sub_self]⟩
  · obtain ⟨k,h⟩ := amin
    exact ⟨k,by rw [h,div_self ha.ne,sub_self]⟩
  · intro k; field_simp [ne_of_lt ha, ne_of_gt hb, ne_of_gt hba]; ring

/-- Each endpoint metric preserves the squared norm of each constrained row. -/
theorem lengths_preserved (eigen z : Row) (hz : ∑ k, eigen k * z k^2 = 0) (t : ℝ) :
    ∑ k, (1+t*eigen k)*z k^2 = ∑ k, z k^2 := by
  simp_rw [add_mul,one_mul,mul_assoc]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,hz,mul_zero,add_zero]

/-- Endpoint maximum for a linear-fractional score with positive denominators. -/
theorem score_between {t n₀ n₁ b₀ b₁ : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) :
    (t*n₀ + (1-t)*n₁)/(t*b₀+(1-t)*b₁) ≤ max (n₀/b₀) (n₁/b₁) := by
  have h : 0 < t*b₀+(1-t)*b₁ := by
    by_cases ht : t=0
    · simpa [ht] using hb₁
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne h0 (Ne.symm ht)) hb₀)
        (mul_nonneg (sub_nonneg.mpr h1) hb₁.le)
  apply (div_le_iff₀ h).mpr
  have ha := (div_le_iff₀ hb₀).mp (le_max_left (n₀/b₀) (n₁/b₁))
  have hb := (div_le_iff₀ hb₁).mp (le_max_right (n₀/b₀) (n₁/b₁))
  nlinarith only [mul_le_mul_of_nonneg_left ha h0,
    mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr h1)]


abbrev Rows := Matrix (Fin 5) (Fin 3) ℝ

/-- The Gram entry of two row vectors. -/
def gram (x : Rows) (i j : Fin 5) : ℝ := ∑ k, x i k * x j k

/-- In the chosen orthonormal coordinates one coordinate vanishes on every row. -/
def planar (x : Rows) : Prop := ∃ k, ∀ i, x i k = 0

def centered (x : Rows) : Prop := ∀ k, ∑ i, x i k = 0

noncomputable def rescale (f : Row) (z : Rows) : Rows := fun i k => Real.sqrt (f k) * z i k

theorem gram_rescale (f : Row) (hf : ∀ k, 0 ≤ f k) (z : Rows) (i j : Fin 5) :
    gram (rescale f z) i j = ∑ k, f k * (z i k * z j k) := by
  apply Finset.sum_congr rfl
  intro k _
  dsimp [rescale]
  rw [mul_mul_mul_comm, Real.mul_self_sqrt (hf k)]

theorem centered_rescale (z : Rows) (hz : centered z) (f : Row) : centered (rescale f z) := by
  intro k
  simp only [rescale, ← Finset.mul_sum, hz k, mul_zero]

/-- The endpoint factors have a vanishing coordinate, the same individual
row norms, and their full Gram matrices interpolate to the original one. -/
theorem split_mixed (z : Rows) (e : Row) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (lo : ∀ k, a ≤ e k) (hi : ∀ k, e k ≤ b)
    (amin : ∃ k, e k = a) (bmax : ∃ k, e k = b)
    (hz : ∀ i, ∑ k, e k * (z i k)^2 = 0) (hc : centered z) :
    ∃ l r : Rows, ∃ t : ℝ, 0<t ∧ t<1 ∧ planar l ∧ planar r ∧ centered l ∧ centered r ∧
      (∀ i, gram l i i = gram z i i ∧ gram r i i = gram z i i) ∧
      ∀ i j, gram z i j = t * gram l i j + (1-t) * gram r i j := by
  let L : Row := fun k => 1-e k/b
  let R : Row := fun k => 1-e k/a
  let t := b/(b-a)
  obtain ⟨ht, pos, ⟨kL,hL⟩, ⟨kR,hR⟩, mix⟩ := boundary_metrics e ha hb lo hi amin bmax
  refine ⟨rescale L z, rescale R z, t, ht.1, ht.2,
    ⟨kL, fun i => by simp [rescale,L,hL]⟩, ⟨kR, fun i => by simp [rescale,R,hR]⟩,
    centered_rescale z hc L, centered_rescale z hc R, ?_, ?_⟩
  · intro i
    have norm (s : ℝ) : ∑ k, (1-e k/s)*(z i k * z i k) = gram z i i := by
      convert lengths_preserved e (z i) (hz i) (-s⁻¹) using 1 <;>
        simp [gram, sq, div_eq_mul_inv, sub_eq_add_neg, mul_comm]
    exact ⟨(gram_rescale _ (fun k => (pos k).1) _ _ _).trans (norm b),
      (gram_rescale _ (fun k => (pos k).2) _ _ _).trans (norm a)⟩
  · intro i j
    rw [gram_rescale L (fun k => (pos k).1), gram_rescale R (fun k => (pos k).2)]
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have h : t * L k + (1-t) * R k = 1 := mix k
    linear_combination -(z i k * z j k) * h

/-- Real symmetric matrix corresponding to the six free coefficients. -/
def metric (c : Coeff) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![c 0,c 3,c 4; c 3,c 1,c 5; c 4,c 5,c 2]

theorem metric_hermitian (c : Coeff) : (metric c).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem metric_nonzero {c : Coeff} (hc : c ≠ 0) : metric c ≠ 0 := by
  intro h
  apply hc
  have f (i j : Fin 3) := congrFun (congrFun h i) j
  funext k
  fin_cases k
  · exact f 0 0
  · exact f 1 1
  · exact f 2 2
  · exact f 0 1
  · exact f 0 2
  · exact f 1 2

theorem metric_eval (z : Rows) (i : Fin 5) (c : Coeff) :
    (z * metric c * z.transpose) i i = quad c (z i) := by
  simp [quad, metric, monomials, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_succ]; ring

/-- A real change to an eigenbasis diagonalizes a nonzero form annihilating
all five row squares, while preserving the centered Gram matrix. -/
theorem diagonalize_five (x : Rows) (hc : centered x) :
    ∃ z : Rows, ∃ e : Row, e ≠ 0 ∧ centered z ∧
      (∀ i j, gram z i j = gram x i j) ∧ ∀ i, ∑ k, e k * (z i k)^2 = 0 := by
  obtain ⟨c,hn,hq⟩ := five_constraints x
  let H := metric_hermitian c
  let U : Matrix (Fin 3) (Fin 3) ℝ := H.eigenvectorUnitary
  let e : Row := H.eigenvalues
  let z := x * U
  have starU : (star H.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ) = U.transpose := by
    exact Matrix.conjTranspose_eq_transpose_of_trivial U
  have hu : U * U.transpose = 1 := by
    rw [← starU]
    exact Unitary.coe_mul_star_self H.eigenvectorUnitary
  have he : metric c = U * Matrix.diagonal e * U.transpose := by
    simpa only [Unitary.conjStarAlgAut_apply,starU, RCLike.ofReal_real_eq_id,Function.id_comp]
      using H.spectral_theorem
  have hg : z * z.transpose = x * x.transpose := by
    dsimp only [z]
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hu, Matrix.one_mul]
  have hform : z * Matrix.diagonal e * z.transpose = x * metric c * x.transpose := by
    dsimp only [z]
    rw [he, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  refine ⟨z,e, fun h => metric_nonzero hn (H.eigenvalues_eq_zero_iff.mp h),?_,?_,?_⟩
  · intro k
    change (∑ i, ∑ j, x i j * U j k) = 0
    rw [Finset.sum_comm]
    have rowSums : ∀ j, ∑ i, x i j = 0 := hc
    simp only [← Finset.sum_mul, rowSums, zero_mul, Finset.sum_const_zero]
  · intro i j
    exact congrFun (congrFun hg i) j
  · intro i
    have hx := (congrFun (congrFun hform i) i).trans ((metric_eval x i c).trans (hq i))
    change ∑ k, (z * Matrix.diagonal e) i k * z i k = 0 at hx
    simp only [Matrix.mul_diagonal] at hx
    convert hx using 1
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- If all signed eigenvalues are nonnegative, any strictly positive
coefficient forces that entire coordinate of the configuration to vanish. -/
theorem planar_of_nonneg (z : Rows) (e : Row) (he : e ≠ 0) (hn : ∀ k, 0 ≤ e k)
    (hz : ∀ i, ∑ k, e k * (z i k)^2 = 0) : planar z := by
  obtain ⟨k,hk⟩ : ∃ k, e k ≠ 0 := by
    by_contra! h
    exact he (funext h)
  refine ⟨k,fun i => ?_⟩
  have h := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) => mul_nonneg (hn j) (sq_nonneg (z i j)))).mp (hz i) k (by simp)
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left hk)

/-- Every centered system of five real three-vectors is a strict convex
mixture in Gram coordinates of two centered planar systems having exactly
the same individual row lengths as the input. -/
theorem five_planar_gram_split (x : Rows) (hc : centered x) :
    ∃ l r : Rows, ∃ t : ℝ, 0<t ∧ t<1 ∧ planar l ∧ planar r ∧ centered l ∧ centered r ∧
      (∀ i, gram l i i = gram x i i ∧ gram r i i = gram x i i) ∧
      ∀ i j, gram x i j = t * gram l i j + (1-t) * gram r i j := by
  obtain ⟨z,e,he,hc',hg,hz⟩ := diagonalize_five x hc
  have already (h : planar z) : ∃ l r : Rows, ∃ t : ℝ, 0<t ∧ t<1 ∧ planar l ∧ planar r ∧
      centered l ∧ centered r ∧ (∀ i, gram l i i = gram x i i ∧ gram r i i = gram x i i) ∧
      ∀ i j, gram x i j = t * gram l i j + (1-t) * gram r i j := by
    refine ⟨z,z,1/2,by norm_num,by norm_num,h,h,hc',hc',fun i => ⟨hg i i,hg i i⟩,?_⟩
    intro i j
    rw [hg]
    ring
  obtain ⟨a,_,lo⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  obtain ⟨b,_,hi⟩ := Finset.exists_max_image Finset.univ e Finset.univ_nonempty
  by_cases ha : e a < 0
  · by_cases hb : 0 < e b
    · obtain ⟨l,r,t,ht,ht',hl,hr,hcl,hcr,hd,hm⟩ := split_mixed z e ha hb
        (fun k => lo k (by simp)) (fun k => hi k (by simp)) ⟨a,rfl⟩ ⟨b,rfl⟩ hz hc'
      exact ⟨l,r,t,ht,ht',hl,hr,hcl,hcr,fun i => ⟨(hd i).1.trans (hg i i),(hd i).2.trans (hg i i)⟩,
        fun i j => (hg i j).symm.trans (hm i j)⟩
    · apply already (planar_of_nonneg z (-e) (neg_ne_zero.mpr he) ?_ ?_)
      · intro k
        exact neg_nonneg.mpr ((hi k (by simp)).trans (le_of_not_gt hb))
      · intro i
        simpa only [Pi.neg_apply,neg_mul,Finset.sum_neg_distrib,neg_zero] using congrArg Neg.neg (hz i)
  · exact already (planar_of_nonneg z e he (fun k => (le_of_not_gt ha).trans (lo k (by simp))) hz)

abbrev Weights := Fin 5 → ℝ

/-- Twice the pair weight in the polarized Bloch determinant (the fixed
factor is incorporated into the moments below). -/
def deficit (p : Weights) (x : Rows) (i j : Fin 5) : ℝ := p i*p j - gram x i j

def admissible (p : Weights) (x : Rows) : Prop :=
  centered x ∧ (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 2 ∧ ∀ i, gram x i i = p i^2

def moment (p d : Weights) (x : Rows) (a b : ℕ) : ℝ :=
  ∑ i, ∑ j, d i^a * d j^b * deficit p x i j

def trMoment (p d : Weights) (a : ℕ) : ℝ := ∑ i, p i * d i^a

/-- Both numerator and denominator are scaled by four. -/
def numerator (p d : Weights) (x : Rows) : ℝ :=
  trMoment p d 2 * moment p d x 10 10 - 2*trMoment p d 6 * moment p d x 10 6
    + trMoment p d 10 * moment p d x 6 6

noncomputable def hardy (p d : Weights) (x : Rows) : ℝ := numerator p d x / moment p d x 10 10

theorem deficit_nonneg {p : Weights} {x : Rows} (hx : admissible p x) (i j : Fin 5) :
    0 ≤ deficit p x i j := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (x i) (x j)
  have norm (k : Fin 5) : ∑ n, (x k n)^2 = (p k)^2 := by
    simpa only [sq, gram] using hx.2.2.2 k
  rw [norm i,norm j,Real.sqrt_sq (hx.2.1 i),Real.sqrt_sq (hx.2.1 j)] at h
  exact sub_nonneg.mpr h

/-- Strict positivity includes configurations with zero rows and all spectra
with positive coordinates, including repeated values. -/
theorem moment_pos {p d : Weights} {x : Rows} (hx : admissible p x) (hd : ∀ i, 0 < d i)
    (a b : ℕ) : 0 < moment p d x a b := by
  have hsum (i : Fin 5) : ∑ j, gram x i j = 0 := by
    unfold gram
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hx.1 _, mul_zero, Finset.sum_const_zero]
  have hmass : ∑ i, ∑ j, deficit p x i j = 4 := by
    simp only [deficit, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, sub_zero, hx.2.2.1,
      ← Finset.sum_mul]
    norm_num
  have piece (i j : Fin 5) : 0 ≤ d i^a * d j^b * deficit p x i j :=
    mul_nonneg (mul_nonneg (pow_nonneg (hd i).le _) (pow_nonneg (hd j).le _)) (deficit_nonneg hx i j)
  by_contra! h
  have zero : moment p d x a b = 0 := le_antisymm h
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => piece i j)
  have rowZero := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_nonneg fun j _ => piece i j)).mp zero
  have each (i j : Fin 5) : deficit p x i j = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => piece i j)).mp
      (rowZero i (by simp)) j (by simp)
    exact (mul_eq_zero.mp h).resolve_left (mul_pos (pow_pos (hd i) _) (pow_pos (hd j) _)).ne'
  simp only [each,Finset.sum_const_zero] at hmass
  norm_num at hmass

theorem moment_mix (p d : Weights) (x l r : Rows) (t : ℝ)
    (h : ∀ i j, gram x i j = t * gram l i j + (1-t) * gram r i j) (a b : ℕ) :
    moment p d x a b = t * moment p d l a b + (1-t)*moment p d r a b := by
  unfold moment
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [deficit,h i j]
  ring

theorem score_on_segment (p d : Weights) (x l r : Rows) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (al : admissible p l) (ar : admissible p r) (hd : ∀ i, 0 < d i)
    (hm : ∀ i j, gram x i j = t * gram l i j + (1-t) * gram r i j) :
    min (hardy p d l) (hardy p d r) ≤ hardy p d x ∧
    hardy p d x ≤ max (hardy p d l) (hardy p d r) := by
  have mix := moment_mix p d x l r t hm
  have num : numerator p d x = t * numerator p d l + (1-t) * numerator p d r := by
    simp only [numerator, mix]
    ring
  have bound : hardy p d x ≤ max (hardy p d l) (hardy p d r) := by
    unfold hardy
    rw [num,mix]
    exact score_between ht ht' (moment_pos al hd _ _) (moment_pos ar hd _ _)
  have lower : min (hardy p d l) (hardy p d r) ≤ hardy p d x := by
    have negBound := score_between (n₀ := -numerator p d l) (n₁ := -numerator p d r)
      ht ht' (moment_pos al hd 10 10) (moment_pos ar hd 10 10)
    have negScore : -(hardy p d x) ≤ max (-(hardy p d l)) (-(hardy p d r)) := by
      unfold hardy
      rw [num,mix]
      simpa only [mul_neg,← neg_add,neg_div] using negBound
    rcases le_total (hardy p d l) (hardy p d r) with h | h
    · simpa only [min_eq_left h,max_eq_left (neg_le_neg h),neg_le_neg_iff] using negScore
    · simpa only [min_eq_right h,max_eq_right (neg_le_neg h),neg_le_neg_iff] using negScore
  exact ⟨lower,bound⟩

end HardyFive
