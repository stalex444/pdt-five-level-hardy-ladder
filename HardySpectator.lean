module
public import Mathlib
@[expose] public section
noncomputable section
namespace HardyFive.Spectator
open Finset
open scoped ComplexConjugate
variable {ι : Type*} [Fintype ι]

-- The row fit and coordinate deletion below are adapted from the PDT canon's
-- HardyRankOne and HardyDeletion. The spectator interval and equality are new here.
/-- The diagonal operator with real entries `d i ^ k`, applied to a complex vector. -/
def weighted (d : ι → ℝ) (k : ℕ) (u : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun i => (d i ^ k : ℝ) * u i

/-- Probability summed over orthonormal bases of both outcome-one endpoint spaces. -/
def endpointScore {r s : ℕ} (d : ι → ℝ) (a : Fin r → EuclideanSpace ℂ ι)
    (b : Fin s → EuclideanSpace ℂ ι) : ℝ :=
  ∑ i, ∑ j, ‖inner ℂ (weighted d 1 (a i)) (b j)‖ ^ 2

/-- Measurement amplitudes against a real diagonal Schmidt operator are unchanged
when the operator is moved to the opposite side of the complex inner product. -/
theorem weighted_selfadjoint (d : ι → ℝ) (k : ℕ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ (weighted d k x) y = inner ℂ x (weighted d k y) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  change y i * star (((d i^k:ℝ):ℂ) * x i) = (((d i^k:ℝ):ℂ) * y i) * star (x i)
  rw [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

private def diagonalMap (d : ι → ℝ) (k : ℕ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun := weighted d k
  map_add' x y := by
    ext i
    change ((d i ^ k:ℝ):ℂ) * (x i + y i) = _
    exact mul_add _ _ _
  map_smul' c x := by
    ext i
    change ((d i ^ k:ℝ):ℂ) * (c * x i) = c * (((d i ^ k:ℝ):ℂ)*x i)
    ring

/-- The Hardy orthogonality constraints limit the sum of the two endpoint ranks. -/
theorem endpoint_rank_sum {r s : ℕ} {d : ι → ℝ} (hd : ∀ i, 0 < d i)
    (a : Fin r → EuclideanSpace ℂ ι) (b : Fin s → EuclideanSpace ℂ ι)
    (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hz : ∀ i j, inner ℂ (weighted d 5 (a i)) (b j) = 0) :
    r + s ≤ Fintype.card ι := by
  classical
  let T := diagonalMap d 5
  have hinj : Function.Injective T := by
    intro v w he
    ext i
    have hi := congrArg (fun (z : EuclideanSpace ℂ ι) => z i) he
    change ((d i ^ 5 : ℝ):ℂ) * v i = ((d i ^ 5 : ℝ):ℂ) * w i at hi
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (pow_pos (hd i) 5).ne') hi
  have hli : LinearIndependent ℂ (T ∘ a) := ha.linearIndependent.map' T
    (LinearMap.ker_eq_bot.mpr hinj)
  have horth : Submodule.IsOrtho (Submodule.span ℂ (Set.range (T ∘ a)))
      (Submodule.span ℂ (Set.range b)) := by
    apply Submodule.isOrtho_span.mpr
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact hz i j
  have hdim := Submodule.finrank_add_finrank_le_of_disjoint horth.disjoint
  simpa [finrank_span_eq_card hli,finrank_span_eq_card hb.linearIndependent,
    finrank_euclideanSpace] using hdim

/-- On the support of a unit terminal row, any uniform fit controls its entire
Born row against an orthonormal endpoint orthogonal to its fifth-power image. -/
theorem row_le_fit {s : ℕ} {d : ι → ℝ} {u : EuclideanSpace ℂ ι}
    (hu : ‖u‖ = 1) (b : Fin s → EuclideanSpace ℂ ι) (hb : Orthonormal ℂ b)
    (hz : ∀ j, inner ℂ (weighted d 5 u) (b j) = 0)
    {t e : ℝ} (hfit : ∀ i, u i ≠ 0 → |d i - t*d i^5| ≤ e) :
    ∑ j, ‖inner ℂ (weighted d 1 u) (b j)‖^2 ≤ e^2 := by
  let r := weighted d 1 u - (t:ℂ) • weighted d 5 u
  have hrow (j : Fin s) : ‖inner ℂ (weighted d 1 u) (b j)‖ = ‖inner ℂ (b j) r‖ := by
    rw [norm_inner_symm (b j) r]
    simp only [r,inner_sub_left,inner_smul_left,hz,mul_zero,sub_zero]
  simp_rw [hrow]
  refine (hb.sum_inner_products_le r).trans ?_
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ i, e^2 * ‖u i‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi : r i = ((d i - t*d i^5 : ℝ):ℂ) * u i := by
        change ((d i ^ 1 : ℝ):ℂ)*u i - (t:ℂ)*(((d i ^ 5 : ℝ):ℂ)*u i) = _
        push_cast; ring
      rw [hi,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs]
      by_cases h : u i = 0
      · simp [h]
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hfit i h) 2)
          (sq_nonneg _)
    _ = e^2 := by rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, hu]; ring

private theorem exists_mix_zero (x y : ℂ) :
    ∃ p q : ℂ, ‖p‖^2 + ‖q‖^2 = 1 ∧ p*x + q*y = 0 := by
  by_cases h : ‖x‖^2 + ‖y‖^2 = 0
  · have hx : x = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖y‖])
    exact ⟨1,0,by simp,by simp [hx]⟩
  let r := Real.sqrt (‖x‖^2 + ‖y‖^2)
  have hp : 0 < ‖x‖^2 + ‖y‖^2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
  have hr : 0 < r := Real.sqrt_pos.mpr hp
  have hr2 : r^2 = ‖x‖^2 + ‖y‖^2 := Real.sq_sqrt hp.le
  refine ⟨y/(r:ℂ),-x/(r:ℂ),?_,by ring⟩
  rw [norm_div,norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,div_pow,div_pow]
  field_simp
  linarith

private theorem orthonormal_mix_norm (a : Fin 2 → EuclideanSpace ℂ ι)
    (ha : Orthonormal ℂ a) (p q : ℂ) (h : ‖p‖^2 + ‖q‖^2 = 1) :
    ‖p • a 0 + q • a 1‖ = 1 := by
  have ho : inner ℂ (p • a 0) (q • a 1) = 0 := by
    simp only [inner_smul_left,inner_smul_right,ha.inner_eq_zero (show (0:Fin 2) ≠ 1 by decide),mul_zero]
  have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
  simp only [norm_smul,ha.norm_eq_one,mul_one] at hs
  nlinarith [norm_nonneg (p • a 0 + q • a 1)]

private theorem mix_isometry (p q z w : ℂ) (h : ‖p‖^2+‖q‖^2=1) :
    ‖conj p*z+conj q*w‖^2 + ‖-q*z+p*w‖^2 = ‖z‖^2+‖w‖^2 := by
  simp only [Complex.sq_norm] at h ⊢
  apply Complex.ofReal_injective
  have h' := congrArg Complex.ofReal h
  simp only [Complex.ofReal_add,Complex.ofReal_one,Complex.normSq_eq_conj_mul_self] at h' ⊢
  simp only [map_add,map_mul,map_neg,Complex.conj_conj]
  linear_combination (conj z*z + conj w*w)*h'

omit [Fintype ι] in
private theorem weighted_mix (d : ι → ℝ) (k : ℕ) (u v : EuclideanSpace ℂ ι) (p q : ℂ) :
    weighted d k (p • u + q • v) = p • weighted d k u + q • weighted d k v := by
  ext i
  change ((d i ^ k : ℝ):ℂ)*(p*u i+q*v i) = p*(((d i ^ k : ℝ):ℂ)*u i)+q*(((d i ^ k : ℝ):ℂ)*v i)
  ring

/-- A rank-two endpoint admits a basis in which one row omits any prescribed
coordinate. The endpoint success is consequently bounded by the squared errors
of one fit on the remaining coordinates and another fit on the full spectrum.
The original endpoint bases may be arbitrary, and zero Schmidt values are allowed. -/
theorem endpoint_deletion_bound {s : ℕ} (d : ι → ℝ)
    (a : Fin 2 → EuclideanSpace ℂ ι) (b : Fin s → EuclideanSpace ℂ ι)
    (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hz : ∀ i j, inner ℂ (weighted d 5 (a i)) (b j) = 0)
    (k : ι) {t₀ t₁ e₀ e₁ : ℝ}
    (h₀ : ∀ i, i ≠ k → |d i - t₀*d i^5| ≤ e₀)
    (h₁ : ∀ i, |d i - t₁*d i^5| ≤ e₁) :
    endpointScore d a b ≤ e₀^2 + e₁^2 := by
  obtain ⟨p,q,hn,hk⟩ := exists_mix_zero (a 0 k) (a 1 k)
  let u := p • a 0 + q • a 1
  let v := -conj q • a 0 + conj p • a 1
  have hu : ‖u‖ = 1 := orthonormal_mix_norm a ha p q hn
  have hv : ‖v‖ = 1 := orthonormal_mix_norm a ha _ _ (by
    simpa [add_comm] using hn)
  have hzero : u k = 0 := hk
  have hu5 (j : Fin s) : inner ℂ (weighted d 5 u) (b j) = 0 := by
    simp only [u,weighted_mix,inner_add_left,inner_smul_left,hz,mul_zero,add_zero]
  have hv5 (j : Fin s) : inner ℂ (weighted d 5 v) (b j) = 0 := by
    simp only [v,weighted_mix,inner_add_left,inner_smul_left,hz,mul_zero,add_zero]
  have hru := row_le_fit hu b hb hu5 (t:=t₀) (e:=e₀)
    (fun i hi => h₀ i (fun e => hi (e ▸ hzero)))
  have hrv := row_le_fit hv b hb hv5 (t:=t₁) (e:=e₁) (fun i _ => h₁ i)
  calc
    endpointScore d a b =
        (∑ j, ‖inner ℂ (weighted d 1 u) (b j)‖^2) +
        ∑ j, ‖inner ℂ (weighted d 1 v) (b j)‖^2 := by
      rw [endpointScore,Fin.sum_univ_two,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [u,v,weighted_mix,inner_add_left,inner_smul_left,
        map_neg,Complex.conj_conj]
      exact (mix_isometry p q _ _ hn).symm
    _ ≤ _ := add_le_add hru hrv


def shape (s : ℝ) : Fin 5 → ℝ := ![s,2,3,4,5]

private theorem fits {s : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) :
    |s - s^5 / 176| ≤ 20/11 ∧ |s-s^5/421| ≤ 1020/421 := by
  have h4 := pow_le_pow_left₀ h0 h2 4
  have h3 := pow_le_pow_left₀ h0 h2 3
  have hs2 := pow_le_pow_left₀ h0 h2 2
  have hfit : 0 ≤ (2-s)*(176-(s^4+2*s^3+4*s^2+8*s+16)) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have hlow := mul_nonneg h0 (show 0 ≤ 176-s^4 by nlinarith)
  have hlow' := mul_nonneg h0 (show 0 ≤ 421-s^4 by nlinarith)
  rw [abs_le,abs_le]
  constructor <;> constructor <;> nlinarith [pow_nonneg h0 5]

/-- One endpoint has dimension two. The other can have arbitrary dimension. -/
theorem spectator_upper {s : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) {n : ℕ}
    (a : Fin 2 → EuclideanSpace ℂ (Fin 5)) (b : Fin n → EuclideanSpace ℂ (Fin 5))
    (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hz : ∀ i j, inner ℂ (weighted (shape s) 5 (a i)) (b j) = 0) :
    endpointScore (shape s) a b ≤ 196784800/21446161 := by
  calc
    _ ≤ (20/11:ℝ)^2 + (1020/421)^2 := by
      apply endpoint_deletion_bound (shape s) a b ha hb hz 4 (t₀:=1/176) (t₁:=1/421)
      · intro i hi
        fin_cases i <;> first | exact False.elim (hi rfl) | norm_num [shape]
        simpa [shape,div_eq_mul_inv,mul_comm] using (fits h0 h2).1
      · intro i
        fin_cases i <;> norm_num [shape]
        simpa [shape,div_eq_mul_inv,mul_comm] using (fits h0 h2).2
    _ = _ := by norm_num

abbrev State := EuclideanSpace ℂ (Fin 5)

def witness (sign : ℝ) : Fin 2 → State :=
  ![WithLp.toLp 2 ![0, (Real.sqrt (32/33) : ℝ), 0, ((sign * Real.sqrt (1/33) : ℝ) : ℂ), 0],
    WithLp.toLp 2 ![0, 0, (Real.sqrt (3125/3368) : ℝ), 0, ((sign * Real.sqrt (243/3368) : ℝ) : ℂ)]]

private theorem amp (s t u : ℝ) (k : ℕ) (i j : Fin 2) :
    inner ℂ (weighted (shape s) k (witness t i)) (witness u j) =
      if i = j then
        if i = 0 then ((2^k*(32/33) + 4^k*(t*u)*(1/33) : ℝ) : ℂ)
        else ((3^k*(3125/3368) + 5^k*(t*u)*(243/3368) : ℝ) : ℂ)
      else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_succ,weighted,
      shape,witness] <;>
    ring_nf <;> norm_num [← Complex.ofReal_pow] <;> ring

private theorem weighted_zero (s : ℝ) (x : State) : weighted (shape s) 0 x = x := by
  ext i
  change ((shape s i ^ 0 : ℝ) : ℂ) * x i = x i
  simp

private theorem witness_orth {t : ℝ} (ht : t^2=1) : Orthonormal ℂ (witness t) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := amp 1 t t 0 i j
  rw [weighted_zero] at h
  rw [h]
  split_ifs <;> norm_num [←sq,ht]

/-- The two explicit pairs attain the upper bound. -/
theorem spectator_witness (s : ℝ) :
    Orthonormal ℂ (witness 1) ∧ Orthonormal ℂ (witness (-1)) ∧
    (∀ i j, inner ℂ (weighted (shape s) 5 (witness 1 i)) (witness (-1) j) = 0) ∧
    endpointScore (shape s) (witness 1) (witness (-1)) = 196784800/21446161 := by
  refine ⟨witness_orth (by norm_num),witness_orth (by norm_num),?_,?_⟩
  · intro i j
    rw [amp]
    split_ifs <;> norm_num
  · simp only [endpointScore,Fin.sum_univ_two,amp]
    norm_num [Complex.norm_real,Real.norm_eq_abs]

private theorem small_side {s : ℝ} (h0 : 0 < s) (h2 : s ≤ 2) {m n : ℕ} (hm : m ≤ 2)
    (a : Fin m → State) (b : Fin n → State) (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hz : ∀ i j, inner ℂ (weighted (shape s) 5 (a i)) (b j) = 0) :
    endpointScore (shape s) a b ≤ 196784800/21446161 := by
  obtain h | h | h : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  · subst m; simp [endpointScore]; norm_num
  · subst m
    simp only [endpointScore, Fin.sum_univ_one]
    apply le_trans (row_le_fit (ha.norm_eq_one 0) b hb (hz 0) (t:=1/421) (e:=1020/421) ?_) (by norm_num)
    intro i _
    fin_cases i <;> norm_num [shape]
    simpa [shape,mul_comm,div_eq_mul_inv] using (fits h0.le h2).2
  · subst m; exact spectator_upper h0.le h2 a b ha hb hz

theorem all_ranks {s : ℝ} (h0 : 0 < s) (h2 : s ≤ 2) {m n : ℕ}
    (a : Fin m → State) (b : Fin n → State) (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hz : ∀ i j, inner ℂ (weighted (shape s) 5 (a i)) (b j) = 0) :
    endpointScore (shape s) a b ≤ 196784800/21446161 := by
  have hd (i : Fin 5) : 0 < shape s i := by fin_cases i <;> simp [shape,h0]
  have dim : m+n ≤ 5 := by simpa using endpoint_rank_sum hd a b ha hb hz
  by_cases hm : m ≤ 2
  · exact small_side h0 h2 hm a b ha hb hz
  · have hz' (j i) : inner ℂ (weighted (shape s) 5 (b j)) (a i) = 0 := by
      rw [weighted_selfadjoint,inner_eq_zero_symm]
      exact hz i j
    have equ : endpointScore (shape s) a b = endpointScore (shape s) b a := by
      unfold endpointScore
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro i _
      rw [weighted_selfadjoint,norm_inner_symm]
    rw [equ]
    exact small_side h0 h2 (by omega) b a hb ha hz'

end HardyFive.Spectator
end
