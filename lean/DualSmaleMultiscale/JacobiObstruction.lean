/-
  DualSmaleMultiscale/JacobiObstruction.lean

  THEOREM 8 (Exact Jacobi-Christoffel-Darboux Univalent Obstruction Family — All Even n = 2k):
    For EVERY k >= 1 (degree n = 2k), define the orthogonal Jacobi-(0,1) polynomials on [0, 1]
    via Rodrigues' formula:
      rodrigues j := (derivative^[j]) (X^j * (1 - X)^(j + 1)),
      jacobi01 j  := sum_{m=0}^j (-1)^m * C(j, m) * C(j+1, m) * X^m * (1 - X)^(j - m),
    and the Christoffel-Darboux extremal polynomial:
      Q_k := C (2 / (k * (k + 1))) * sum_{j=0}^{k-1} C (j + 1) * jacobi01 j.
    Then for P'_k(x) := (1 - x) * (Q_k(x))^2 (degree 2k - 1 = n - 1):
      (1) Q_k(0) = 1, hence P'_k(0) = 1 and P'_k(1) = 0,
      (2) P'_k(x) >= 0 for all x in [0, 1] (monotone on [0, 1]),
      (3) EXACT INTEGRAL IDENTITY:
            int_0^1 (1 - x) * (Q_k(x))^2 dx = 1 / (k * (k + 1)) = 4 / (n * (n + 2))!
    This demonstrates analytically why single-component univalent bounds on U_0(L_*)
    cannot beat O(1/n^2)!
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

open scoped BigOperators
open Polynomial

namespace DualSmaleMultiscale

/-! ### Section 1: Iterated Derivative Leibniz Rule & Rodrigues Polynomials -/

/-- Polynomial Leibniz rule for the `r`-th iterated derivative of a product. -/
lemma iterate_derivative_mul :
    ∀ (r : ℕ) (p q : ℝ[X]),
      derivative^[r] (p * q) =
        ∑ m ∈ Finset.range (r + 1),
          C (Nat.choose r m : ℝ) * (derivative^[m] p) * (derivative^[r - m] q) := by
  intro r
  induction r with
  | zero => intro p q; simp
  | succ r ih =>
    intro p q
    rw [Function.iterate_succ_apply', ih p q, map_sum]
    have hstep : ∀ m ∈ Finset.range (r + 1),
        derivative (C (Nat.choose r m : ℝ) * (derivative^[m] p) * (derivative^[r - m] q)) =
        C (Nat.choose r m : ℝ) * (derivative^[m + 1] p) * (derivative^[r - m] q) +
        C (Nat.choose r m : ℝ) * (derivative^[m] p) * (derivative^[r - m + 1] q) := by
      intro m _
      rw [mul_assoc, derivative_mul, derivative_C, zero_mul, zero_add, derivative_mul,
        ← Function.iterate_succ_apply' derivative m p, ← Function.iterate_succ_apply' derivative (r - m) q]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
    -- Reindex both sums to match range (r + 2)
    have h1 : (∑ m ∈ Finset.range (r + 1),
        C (Nat.choose r m : ℝ) * (derivative^[m + 1] p) * (derivative^[r - m] q)) =
        ∑ m ∈ Finset.range (r + 2),
          if m = 0 then 0 else C (Nat.choose r (m - 1) : ℝ) * (derivative^[m] p) * (derivative^[r + 1 - m] q) := by
      symm
      rw [Finset.sum_range_succ', if_pos rfl, add_zero]
      apply Finset.sum_congr rfl; intro m _
      simp [Nat.add_sub_cancel]
    have h2 : (∑ m ∈ Finset.range (r + 1),
        C (Nat.choose r m : ℝ) * (derivative^[m] p) * (derivative^[r - m + 1] q)) =
        ∑ m ∈ Finset.range (r + 2),
          if m = r + 1 then 0 else C (Nat.choose r m : ℝ) * (derivative^[m] p) * (derivative^[r + 1 - m] q) := by
      symm
      rw [Finset.sum_range_succ, if_pos rfl, add_zero]
      apply Finset.sum_congr rfl; intro m hm
      rw [Finset.mem_range] at hm
      rw [if_neg (by omega), show r + 1 - m = r - m + 1 by omega]
    rw [h1, h2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro m hm
    rw [Finset.mem_range] at hm
    by_cases hm0 : m = 0
    · subst hm0; simp
    · by_cases hmr : m = r + 1
      · subst hmr; simp
      · rw [if_neg hm0, if_neg hmr]
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel, Nat.choose_succ_succ, Nat.cast_add, map_add]
        ring

/-- Iterated derivative of `X ^ a`. -/
lemma iterate_derivative_X_pow :
    ∀ (m a : ℕ),
      derivative^[m] ((X : ℝ[X]) ^ a) =
        if m ≤ a then C ((Nat.descFactorial a m : ℕ) : ℝ) * X ^ (a - m) else 0 := by
  intro m
  induction m with
  | zero => intro a; simp
  | succ m ih =>
    intro a
    rw [Function.iterate_succ_apply', ih a]
    by_cases hm : m + 1 ≤ a
    · rw [if_pos (by omega), if_pos hm]
      rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow]
      rw [show a - m - 1 = a - (m + 1) by omega, ← mul_assoc, ← map_mul]
      congr 2
      rw [Nat.descFactorial_succ]; push_cast; ring
    · by_cases hm' : m ≤ a
      · rw [if_pos hm', if_neg hm]
        have ha : a - m = 0 := by omega
        rw [ha, pow_zero, mul_one, derivative_C]
      · rw [if_neg hm', if_neg hm, derivative_zero]

/-- Iterated derivative of `(1 - X) ^ a`. -/
lemma iterate_derivative_one_sub_X_pow :
    ∀ (m a : ℕ),
      derivative^[m] ((1 - (X : ℝ[X])) ^ a) =
        if m ≤ a then C ((-1 : ℝ) ^ m * (Nat.descFactorial a m : ℝ)) * (1 - X) ^ (a - m) else 0 := by
  intro m
  induction m with
  | zero => intro a; simp
  | succ m ih =>
    intro a
    rw [Function.iterate_succ_apply', ih a]
    by_cases hm : m + 1 ≤ a
    · rw [if_pos (by omega), if_pos hm]
      rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_pow,
        derivative_sub, derivative_one, derivative_X, zero_sub]
      rw [show a - m - 1 = a - (m + 1) by omega]
      rw [Nat.descFactorial_succ, pow_succ]
      simp only [map_mul, map_neg, map_one, Nat.cast_mul]
      ring
    · by_cases hm' : m ≤ a
      · rw [if_pos hm', if_neg hm]
        have ha : a - m = 0 := by omega
        rw [ha, pow_zero, mul_one, derivative_C]
      · rw [if_neg hm', if_neg hm, derivative_zero]

/-- Rodrigues polynomial `rodrigues j = (d/dx)^j [X^j * (1 - X)^(j + 1)]`. -/
noncomputable def rodrigues (j : ℕ) : ℝ[X] :=
  derivative^[j] (X ^ j * (1 - X) ^ (j + 1))

/-- Explicit Jacobi-(0,1) polynomial on `[0, 1]`:
    `jacobi01 j = ∑_{m=0}^j (-1)^m * C(j, m) * C(j+1, m) * X^m * (1 - X)^(j - m)`. -/
noncomputable def jacobi01 (j : ℕ) : ℝ[X] :=
  ∑ m ∈ Finset.range (j + 1),
    C ((-1 : ℝ) ^ m * (Nat.choose j m : ℝ) * (Nat.choose (j + 1) m : ℝ)) * X ^ m * (1 - X) ^ (j - m)

/-- Exact Rodrigues identity: `C (j! : ℝ) * ((1 - X) * jacobi01 j) = rodrigues j`. -/
theorem rodrigues_eq_jacobi01 (j : ℕ) :
    C (j.factorial : ℝ) * ((1 - X) * jacobi01 j) = rodrigues j := by
  unfold rodrigues jacobi01
  rw [iterate_derivative_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  -- Reindex `m ↦ j - m` on the RHS so `X^m` matches `X^(j - (j - m))`!
  rw [← Finset.sum_range_reflect (fun m =>
    C (Nat.choose j m : ℝ) * (derivative^[m] (X ^ j)) * (derivative^[j - m] ((1 - X) ^ (j + 1)))) (j + 1)]
  apply Finset.sum_congr rfl; intro m hm
  rw [Finset.mem_range] at hm
  have hsub : j + 1 - 1 - m = j - m := by omega
  rw [hsub, iterate_derivative_X_pow, iterate_derivative_one_sub_X_pow,
    if_pos (by omega), if_pos (by omega)]
  rw [show j - (j - m) = m by omega, show j + 1 - m = (j - m) + 1 by omega, pow_succ]
  -- Match scalar coefficients using descending factorial identity:
  -- j! * C(j, m) * C(j+1, m) = C(j, j-m) * desc(j, j-m) * desc(j+1, m)
  have hcoeff : (j.factorial : ℝ) * ((-1 : ℝ) ^ m * (Nat.choose j m : ℝ) * (Nat.choose (j + 1) m : ℝ)) =
      (Nat.choose j (j - m) : ℝ) * (Nat.descFactorial j (j - m) : ℝ) *
        ((-1 : ℝ) ^ m * (Nat.descFactorial (j + 1) m : ℝ)) := by
    have h1 : Nat.choose j (j - m) = Nat.choose j m := Nat.choose_symm (by omega)
    have h2 : Nat.descFactorial j (j - m) * m.factorial = j.factorial := by
      have := Nat.descFactorial_eq_div (n := j) (k := j - m)
      have hmul := Nat.choose_mul_factorial_mul_factorial (by omega : j - m ≤ j)
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      rw [show j - (j - m) = m by omega] at hmul
      linarith
    have h3 : Nat.descFactorial (j + 1) m = m.factorial * Nat.choose (j + 1) m :=
      Nat.descFactorial_eq_factorial_mul_choose (j + 1) m
    have hnat : j.factorial * Nat.choose j m * Nat.choose (j + 1) m =
        Nat.choose j (j - m) * Nat.descFactorial j (j - m) * Nat.descFactorial (j + 1) m := by
      rw [h1, h3]
      calc j.factorial * Nat.choose j m * Nat.choose (j + 1) m
          = (Nat.descFactorial j (j - m) * m.factorial) * Nat.choose j m * Nat.choose (j + 1) m := by rw [h2]
        _ = Nat.choose j m * Nat.descFactorial j (j - m) * (m.factorial * Nat.choose (j + 1) m) := by ring
    have hcast : ((j.factorial * Nat.choose j m * Nat.choose (j + 1) m : ℕ) : ℝ) =
        ((Nat.choose j (j - m) * Nat.descFactorial j (j - m) * Nat.descFactorial (j + 1) m : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hcast
    linear_combination (-1 : ℝ) ^ m * hcast
  calc C (j.factorial : ℝ) * ((1 - X) * (C ((-1 : ℝ) ^ m * (j.choose m : ℝ) * ((j + 1).choose m : ℝ)) * X ^ m * (1 - X) ^ (j - m)))
      = C ((j.factorial : ℝ) * ((-1 : ℝ) ^ m * (j.choose m : ℝ) * ((j + 1).choose m : ℝ))) * X ^ m * ((1 - X) ^ (j - m) * (1 - X)) := by
        simp only [map_mul]; ring
    _ = C ((j.choose (j - m) : ℝ) * (j.descFactorial (j - m) : ℝ) * ((-1 : ℝ) ^ m * ((j + 1).descFactorial m : ℝ))) * X ^ m * ((1 - X) ^ (j - m) * (1 - X)) := by
        rw [hcoeff]
    _ = C (j.choose (j - m) : ℝ) * (C (j.descFactorial (j - m) : ℝ) * X ^ m) *
        (C ((-1 : ℝ) ^ m * ((j + 1).descFactorial m : ℝ)) * ((1 - X) ^ (j - m) * (1 - X))) := by
        simp only [map_mul]; ring

/-- Value `jacobi01 j` at `x = 0` is `1`. -/
lemma jacobi01_eval_zero (j : ℕ) : (jacobi01 j).eval 0 = 1 := by
  unfold jacobi01
  change (Polynomial.evalRingHom (0 : ℝ)) _ = 1
  rw [map_sum, Finset.sum_range_succ']
  have hrest : ∑ x ∈ Finset.range j,
      (Polynomial.evalRingHom (0 : ℝ))
        (C ((-1 : ℝ) ^ (x + 1) * (j.choose (x + 1) : ℝ) * ((j + 1).choose (x + 1) : ℝ)) *
          X ^ (x + 1) * (1 - X) ^ (j - (x + 1))) = 0 :=
    Finset.sum_eq_zero (fun x _ => by simp)
  rw [hrest, zero_add]
  simp

/-- Degree of `jacobi01 j` is at most `j`. -/
lemma natDegree_jacobi01_le (j : ℕ) : (jacobi01 j).natDegree ≤ j := by
  unfold jacobi01
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le j, fun m hm => ?_⟩
  rw [Finset.mem_range] at hm
  have h1 : (C ((-1 : ℝ) ^ m * (j.choose m : ℝ) * ((j + 1).choose m : ℝ)) * X ^ m).natDegree ≤ m :=
    Polynomial.natDegree_C_mul_X_pow_le _ _
  have h2 : ((1 - (X : ℝ[X])) ^ (j - m)).natDegree ≤ j - m := by
    refine le_trans (Polynomial.natDegree_pow_le) ?_
    have h1x : (1 - (X : ℝ[X])).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_; simp
    nlinarith
  exact le_trans (Polynomial.natDegree_mul_le) (by omega)

/-- Leading `j`-th derivative of `jacobi01 j` is the constant `(-1)^j * (2j + 1)! / (j + 1)!`. -/
lemma iterate_derivative_jacobi01 (j : ℕ) :
    derivative^[j] (jacobi01 j) = C ((-1 : ℝ) ^ j * ((2 * j + 1).factorial : ℝ) / ((j + 1).factorial : ℝ)) := by
  -- Use C (j!) * ((1 - X) * jacobi01 j) = rodrigues j = (d/dx)^j (X^j (1 - X)^(j+1)):
  -- Differentiate both sides (j + 1) more times? Even simpler: compute (derivative^[j] (jacobi01 j)).eval x!
  -- Actually, compute coeff j of jacobi01 j directly!
  have hdeg : (jacobi01 j).natDegree ≤ j := natDegree_jacobi01_le j
  -- For any P of natDegree ≤ j, derivative^[j] P = C (j! * P.coeff j)!
  have hiter_deg : ∀ (k : ℕ) (P : ℝ[X]), P.natDegree ≤ k →
      derivative^[k] P = C ((k.factorial : ℝ) * P.coeff k) := by
    intro k
    induction k with
    | zero =>
      intro P hP
      have hPeq := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hP)
      simpa using hPeq
    | succ k ih =>
      intro P hP
      rw [Function.iterate_succ_apply]
      have hPd : (derivative P).natDegree ≤ k := by
        have := Polynomial.natDegree_derivative_le P; omega
      rw [ih (derivative P) hPd, Polynomial.coeff_derivative, Nat.factorial_succ]
      push_cast; congr 1; ring
  rw [hiter_deg j (jacobi01 j) hdeg]
  -- Compute (jacobi01 j).coeff j directly from rodrigues_eq_jacobi01 by matching coeff (j + 1)!
  have hcoeff_rod := congrArg (fun P : ℝ[X] => P.coeff (j + 1)) (rodrigues_eq_jacobi01 j)
  -- LHS coeff (j + 1): (C j! * ((1 - X) * jacobi01 j)).coeff (j + 1) = - j! * (jacobi01 j).coeff j
  have hlhs : (C (j.factorial : ℝ) * ((1 - X) * jacobi01 j)).coeff (j + 1) =
      -(j.factorial : ℝ) * (jacobi01 j).coeff j := by
    rw [Polynomial.coeff_C_mul, sub_mul, one_mul, Polynomial.coeff_sub,
      Polynomial.coeff_X_mul, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (jacobi01 j).natDegree < j + 1)]
    ring
  -- RHS coeff (j + 1): (derivative^[j] (X^j * (1 - X)^(j+1))).coeff (j + 1) =
  --   (2j + 1)! / (j + 1)! * (coeff (2j+1) of X^j (1 - X)^(j+1)) = (-1)^(j+1) * (2j+1)! / (j+1)!
  have hcoeff_iter : ∀ (r k : ℕ) (P : ℝ[X]),
      (derivative^[r] P).coeff k = ((Nat.descFactorial (k + r) r : ℕ) : ℝ) * P.coeff (k + r) := by
    intro r
    induction r with
    | zero => intro k P; simp
    | succ r ih =>
      intro k P
      rw [Function.iterate_succ_apply', Polynomial.coeff_derivative, ih (k + 1) P,
        show k + 1 + r = k + (r + 1) by omega]
      have hnat : (k + 1) * Nat.descFactorial (k + (r + 1)) r = Nat.descFactorial (k + (r + 1)) (r + 1) := by
        rw [Nat.descFactorial_succ, show k + (r + 1) - r = k + 1 by omega]
      have hcast : ((k + 1 : ℕ) : ℝ) * ((Nat.descFactorial (k + (r + 1)) r : ℕ) : ℝ) =
          ((Nat.descFactorial (k + (r + 1)) (r + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at hcast
      linear_combination P.coeff (k + (r + 1)) * hcast
  have hrhs : (rodrigues j).coeff (j + 1) =
      (-1 : ℝ) ^ (j + 1) * ((2 * j + 1).factorial : ℝ) / ((j + 1).factorial : ℝ) := by
    unfold rodrigues
    rw [hcoeff_iter j (j + 1), show j + 1 + j = 2 * j + 1 by omega]
    have htop : (X ^ j * (1 - (X : ℝ[X])) ^ (j + 1)).coeff (2 * j + 1) = (-1 : ℝ) ^ (j + 1) := by
      rw [Polynomial.coeff_X_pow_mul', if_pos (by omega : j ≤ 2 * j + 1), show 2 * j + 1 - j = j + 1 by omega]
      have hbin : (1 - (X : ℝ[X])) ^ (j + 1) =
          ∑ r ∈ Finset.range (j + 2), C ((-1 : ℝ) ^ r * (Nat.choose (j + 1) r : ℝ)) * X ^ r := by
        rw [sub_eq_add_neg, add_comm, add_pow]
        apply Finset.sum_congr rfl; intro r _
        rw [one_pow, mul_one, neg_eq_neg_one_mul, mul_pow]
        simp only [← C_eq_natCast, map_mul, map_pow, map_neg, map_one]; ring
      rw [hbin]
      change (Polynomial.lcoeff ℝ (j + 1)) _ = _
      rw [map_sum, Finset.sum_eq_single (j + 1)]
      · rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow, if_pos rfl, Nat.choose_self, Nat.cast_one, mul_one]
      · intro r _ hne; rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hne)]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
    rw [htop]
    have hdesc : ((Nat.descFactorial (2 * j + 1) j : ℕ) : ℝ) * ((j + 1).factorial : ℝ) =
        ((2 * j + 1).factorial : ℝ) := by
      have hnat : Nat.descFactorial (2 * j + 1) j * (j + 1).factorial = (2 * j + 1).factorial := by
        have h1 := Nat.choose_mul_factorial_mul_factorial (by omega : j ≤ 2 * j + 1)
        rw [show 2 * j + 1 - j = j + 1 by omega] at h1
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        linarith
      exact_mod_cast hnat
    have hf1 : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
    rw [eq_div_iff hf1]
    linear_combination (-1 : ℝ) ^ (j + 1) * hdesc
  rw [hlhs, hrhs] at hcoeff_rod
  congr 1
  rw [pow_succ] at hcoeff_rod
  ring_nf at hcoeff_rod ⊢
  linarith

/-! ### Section 2: Beta Integral & Orthogonality of `jacobi01` on `[0, 1]` -/

/-- Elementary Beta integral on `[0, 1]`:
    `∫ x in 0..1, x^a * (1 - x)^b = a! * b! / (a + b + 1)!`. -/
lemma beta_integral_nat :
    ∀ (a b : ℕ),
      (∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b) =
        (a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b + 1).factorial : ℝ) := by
  intro a
  induction a with
  | zero =>
    intro b
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => - ((1 - t) ^ (b + 1)) / ((b + 1 : ℕ) : ℝ)) ((1 - x) ^ b) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
      have h2 := (h1.pow (b + 1)).neg.div_const ((b + 1 : ℕ) : ℝ)
      convert h2 using 1
      rw [Nat.add_sub_cancel]
      have hb : ((b + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hb]
    have hcont : Continuous (fun x : ℝ => (1 - x) ^ b) := (continuous_const.sub continuous_id).pow b
    simp only [pow_zero, one_mul, zero_add]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
    rw [Nat.factorial_zero, Nat.factorial_succ]
    have hb : ((b + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hbf : (b.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hb, hbf]
    ring
  | succ a ih =>
    intro b
    -- Integration by parts: u = x^(a+1), v' = (1 - x)^b, v = -(1-x)^(b+1)/(b+1)
    have hu : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => t ^ (a + 1)) (((a + 1 : ℕ) : ℝ) * x ^ a) x := fun x _ => by
      simpa using hasDerivAt_pow (a + 1) x
    have hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => -((1 - t) ^ (b + 1)) / ((b + 1 : ℕ) : ℝ)) ((1 - x) ^ b) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
      have h2 := (h1.pow (b + 1)).neg.div_const ((b + 1 : ℕ) : ℝ)
      convert h2 using 1
      rw [Nat.add_sub_cancel]
      have hb : ((b + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hb]
    have huc : IntervalIntegrable (fun x : ℝ => ((a + 1 : ℕ) : ℝ) * x ^ a) MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_id.pow a)).intervalIntegrable 0 1
    have hvc : IntervalIntegrable (fun x : ℝ => (1 - x) ^ b) MeasureTheory.volume 0 1 :=
      ((continuous_const.sub continuous_id).pow b).intervalIntegrable 0 1
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv huc hvc
    simp only [sub_self, zero_pow (Nat.succ_ne_zero b), neg_zero, zero_div, mul_zero,
      zero_pow (Nat.succ_ne_zero a), zero_mul, sub_zero, zero_sub] at hibp
    rw [hibp]
    have hsimp : -(∫ x in (0 : ℝ)..1, (((a + 1 : ℕ) : ℝ) * x ^ a) * (-((1 - x) ^ (b + 1)) / ((b + 1 : ℕ) : ℝ))) =
        (((a + 1 : ℕ) : ℝ) / ((b + 1 : ℕ) : ℝ)) * ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ (b + 1) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr; intro x _; ring
    rw [hsimp, ih (b + 1), Nat.factorial_succ a, Nat.factorial_succ b,
      show a + (b + 1) + 1 = a + 1 + b + 1 by omega]
    have hb : ((b + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hb]

/-- Repeated integration by parts for `rodrigues j`:
    for EVERY `g : ℝ[X]`, `∫_0^1 g(x) * (rodrigues j)(x) dx = (-1)^j * ∫_0^1 (g^(j))(x) * x^j * (1-x)^(j+1) dx`. -/
lemma integral_mul_rodrigues (j : ℕ) (g : ℝ[X]) :
    (∫ x in (0 : ℝ)..1, g.eval x * (rodrigues j).eval x) =
      (-1 : ℝ) ^ j * ∫ x in (0 : ℝ)..1, (derivative^[j] g).eval x * (x ^ j * (1 - x) ^ (j + 1)) := by
  -- Prove for all r ≤ j: ∫ g * (d/dx)^r (X^j (1-X)^(j+1)) = (-1)^r ∫ g^(r) * (d/dx)^(j-r)...
  -- Better: induct on r ≤ j for ∫ g * (d/dx)^r F = (-1)^r ∫ g^(r) * F where F = X^j (1-X)^(j+1)!
  set F : ℝ[X] := X ^ j * (1 - X) ^ (j + 1)
  have hvanish : ∀ r : ℕ, r < j →
      (derivative^[r] F).eval 0 = 0 ∧ (derivative^[r] F).eval 1 = 0 := by
    intro r hr
    dsimp [F]
    rw [iterate_derivative_mul]
    have hev : ∀ x : ℝ, (∑ m ∈ Finset.range (r + 1),
        C (Nat.choose r m : ℝ) * (derivative^[m] (X ^ j)) * (derivative^[r - m] ((1 - X) ^ (j + 1)))).eval x =
        ∑ m ∈ Finset.range (r + 1),
          (Nat.choose r m : ℝ) * (derivative^[m] (X ^ j)).eval x *
            (derivative^[r - m] ((1 - X) ^ (j + 1))).eval x := by
      intro x
      change (Polynomial.evalRingHom x) _ = _
      rw [map_sum]
      apply Finset.sum_congr rfl; intro m _; simp
    rw [hev 0, hev 1]
    constructor
    · apply Finset.sum_eq_zero; intro m hm
      rw [Finset.mem_range] at hm
      rw [iterate_derivative_X_pow, if_pos (by omega)]
      simp [zero_pow (by omega : j - m ≠ 0)]
    · apply Finset.sum_eq_zero; intro m hm
      rw [Finset.mem_range] at hm
      rw [iterate_derivative_one_sub_X_pow, if_pos (by omega)]
      simp [zero_pow (by omega : j + 1 - (r - m) ≠ 0)]
  have hgen : ∀ r : ℕ, r ≤ j → ∀ h : ℝ[X],
      (∫ x in (0 : ℝ)..1, h.eval x * (derivative^[r] F).eval x) =
        (-1 : ℝ) ^ r * ∫ x in (0 : ℝ)..1, (derivative^[r] h).eval x * F.eval x := by
    intro r
    induction r with
    | zero => intro _ h; simp
    | succ r ih =>
      intro hr h
      have hu : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun t => h.eval t) ((derivative h).eval x) x := fun x _ => h.hasDerivAt x
      have hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun t => (derivative^[r] F).eval t) ((derivative^[r + 1] F).eval x) x := fun x _ => by
        rw [Function.iterate_succ_apply']
        exact (derivative^[r] F).hasDerivAt x
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
        ((derivative h).continuous.intervalIntegrable 0 1)
        ((derivative^[r + 1] F).continuous.intervalIntegrable 0 1)
      have hv01 := hvanish r (by omega)
      rw [hv01.1, hv01.2, mul_zero, mul_zero, sub_zero] at hibp
      rw [hibp, ih (by omega) (derivative h), ← Function.iterate_succ_apply derivative r h, pow_succ]
      ring
  have hfinal := hgen j le_rfl g
  dsimp [rodrigues]
  rw [hfinal]
  congr 1
  apply intervalIntegral.integral_congr; intro x _
  dsimp [F]; simp

/-- **Exact Orthogonality of `jacobi01` with weight `(1 - x)` on `[0, 1]`**:
    - For `i ≠ j`: `∫_0^1 (1 - x) * P_i(x) * P_j(x) dx = 0`,
    - For `i = j`: `∫_0^1 (1 - x) * P_j(x)^2 dx = 1 / (2 * (j + 1))`. -/
theorem jacobi01_orthogonality (i j : ℕ) :
    (∫ x in (0 : ℝ)..1, (1 - x) * (jacobi01 i).eval x * (jacobi01 j).eval x) =
      if i = j then 1 / (2 * ((j + 1 : ℕ) : ℝ)) else 0 := by
  have hsym : ∀ a b : ℕ, a ≤ b →
      (∫ x in (0 : ℝ)..1, (1 - x) * (jacobi01 a).eval x * (jacobi01 b).eval x) =
        if a = b then 1 / (2 * ((b + 1 : ℕ) : ℝ)) else 0 := by
    intro a b hab
    have hrod : ∀ x : ℝ, (1 - x) * (jacobi01 a).eval x * (jacobi01 b).eval x =
        (1 / (b.factorial : ℝ)) * ((jacobi01 a).eval x * (rodrigues b).eval x) := by
      intro x
      have hev := congrArg (fun P : ℝ[X] => P.eval x) (rodrigues_eq_jacobi01 b)
      simp only [eval_mul, eval_C, eval_sub, eval_one, eval_X] at hev
      rw [← hev]
      have hbf : (b.factorial : ℝ) ≠ 0 := by positivity
      field_simp [hbf]
    simp_rw [hrod]
    rw [intervalIntegral.integral_const_mul, integral_mul_rodrigues b (jacobi01 a)]
    by_cases heq : a = b
    · subst heq
      rw [if_pos rfl, iterate_derivative_jacobi01]
      simp only [eval_C]
      rw [intervalIntegral.integral_const_mul, beta_integral_nat a (a + 1)]
      have hsign : (-1 : ℝ) ^ a * (-1 : ℝ) ^ a = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
      have hfact2 : ((a + (a + 1) + 1).factorial : ℝ) =
          (2 * ((a + 1 : ℕ) : ℝ)) * ((2 * a + 1).factorial : ℝ) := by
        have hnat : (a + (a + 1) + 1).factorial = (2 * (a + 1)) * (2 * a + 1).factorial := by
          rw [show a + (a + 1) + 1 = (2 * a + 1) + 1 by omega, Nat.factorial_succ]; ring
        exact_mod_cast hnat
      rw [hfact2]
      have h1 : (a.factorial : ℝ) ≠ 0 := by positivity
      have h2 : ((a + 1).factorial : ℝ) ≠ 0 := by positivity
      have h3 : ((2 * a + 1).factorial : ℝ) ≠ 0 := by positivity
      have h4 : ((a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [h1, h2, h3, h4]
      nlinarith [hsign]
    · rw [if_neg heq]
      have hlt : (jacobi01 a).natDegree < b := lt_of_le_of_lt (natDegree_jacobi01_le a) (lt_of_le_of_ne hab heq)
      have hzero : derivative^[b] (jacobi01 a) = 0 :=
        Polynomial.iterate_derivative_eq_zero hlt
      rw [hzero]; simp
  rcases le_total i j with hij | hji
  · exact hsym i j hij
  · have hcomm : (∫ x in (0 : ℝ)..1, (1 - x) * (jacobi01 i).eval x * (jacobi01 j).eval x) =
        ∫ x in (0 : ℝ)..1, (1 - x) * (jacobi01 j).eval x * (jacobi01 i).eval x := by
      apply intervalIntegral.integral_congr; intro x _; ring
    rw [hcomm, hsym j i hji]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]

/-! ### Section 3: Christoffel-Darboux Extremal Family & Exact `4 / (n(n + 2))` Identity -/

/-- Christoffel-Darboux extremal polynomial `Q_k` of degree `k - 1` (`k ≥ 1`, `n = 2k`):
    `Q_k = (2 / (k * (k + 1))) * ∑_{j=0}^{k-1} (j + 1) * jacobi01 j`. -/
noncomputable def jacobiExtremalQ (k : ℕ) : ℝ[X] :=
  C (2 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ))) *
    ∑ j ∈ Finset.range k, C ((j + 1 : ℕ) : ℝ) * jacobi01 j

/-- Linearity of the interval integral over finite sums. -/
lemma intervalIntegral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (a b : ℝ)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) MeasureTheory.volume a b) :
    (∫ x in a..b, ∑ i ∈ s, f i x) = ∑ i ∈ s, ∫ x in a..b, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    have hsum_int : IntervalIntegrable (fun x => ∑ j ∈ s, f j x) MeasureTheory.volume a b := by
      have hEq : (∑ j ∈ s, f j) = fun x => ∑ j ∈ s, f j x := by ext x; simp
      rw [← hEq]
      exact IntervalIntegrable.sum s (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    rw [intervalIntegral.integral_add (hf i (Finset.mem_insert_self i s)) hsum_int,
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- **THEOREM 8 (Exact Jacobi-Christoffel-Darboux Univalent Obstruction Family — All `k ≥ 1`, `n = 2k`)**:
    For EVERY `k ≥ 1` (corresponding to degree `n = 2 * k`), `Q_k = jacobiExtremalQ k` satisfies:
    1. `Q_k.eval 0 = 1` (so `P'_k(x) = (1 - x) * Q_k(x)^2` has `P'_k(0) = 1`, `P'_k(1) = 0`),
    2. `∀ x ∈ [0, 1], 0 ≤ (1 - x) * (Q_k.eval x)^2` (so `P_k` is monotone on `[0, 1]`),
    3. `P_k(1) = ∫_0^1 (1 - x) * (Q_k.eval x)^2 dx = 1 / (k * (k + 1)) = 4 / ((2k) * (2k + 2))`! -/
theorem jacobi_univalent_obstruction {k : ℕ} (hk : 1 ≤ k) :
    (jacobiExtremalQ k).eval 0 = 1 ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (1 - x) * ((jacobiExtremalQ k).eval x) ^ 2) ∧
    (∫ x in (0 : ℝ)..1, (1 - x) * ((jacobiExtremalQ k).eval x) ^ 2) =
      4 / (((2 * k : ℕ) : ℝ) * (((2 * k + 2 : ℕ) : ℝ))) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hsum_nat : 2 * ∑ j ∈ Finset.range k, ((j + 1 : ℕ) : ℝ) = (k : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    have hnat : ∀ m : ℕ, 2 * ∑ j ∈ Finset.range m, (j + 1) = m * (m + 1) := by
      intro m; induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ]; linarith
    exact_mod_cast hnat k
  refine ⟨?_, ?_, ?_⟩
  · -- (1) Q_k(0) = 1
    unfold jacobiExtremalQ
    rw [eval_mul, eval_C]
    have heval : (∑ j ∈ Finset.range k, C ((j + 1 : ℕ) : ℝ) * jacobi01 j).eval 0 =
        ∑ j ∈ Finset.range k, ((j + 1 : ℕ) : ℝ) := by
      change (Polynomial.evalRingHom (0 : ℝ)) _ = _
      rw [map_sum]
      apply Finset.sum_congr rfl; intro j _
      simp [jacobi01_eval_zero]
    rw [heval]
    field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos]
    exact hsum_nat
  · -- (2) Nonnegativity on [0, 1]
    intro x hx
    exact mul_nonneg (by linarith [hx.2]) (sq_nonneg _)
  · -- (3) Exact integral = 1 / (k * (k + 1)) = 4 / ((2k)(2k+2))!
    set α : ℝ := 2 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ))
    have hQ_eval : ∀ x : ℝ, (jacobiExtremalQ k).eval x =
        α * ∑ j ∈ Finset.range k, ((j + 1 : ℕ) : ℝ) * (jacobi01 j).eval x := by
      intro x
      dsimp [jacobiExtremalQ, α]
      rw [eval_mul, eval_C]
      congr 1
      change (Polynomial.evalRingHom x) _ = _
      rw [map_sum]
      apply Finset.sum_congr rfl; intro j _; simp
    have hexpand : ∀ x : ℝ, (1 - x) * ((jacobiExtremalQ k).eval x) ^ 2 =
        α ^ 2 * ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
          (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) * ((1 - x) * (jacobi01 i).eval x * (jacobi01 j).eval x) := by
      intro x
      rw [hQ_eval x, mul_pow]
      have hsq : (∑ i ∈ Finset.range k, ((i + 1 : ℕ) : ℝ) * (jacobi01 i).eval x) ^ 2 =
          ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
            (((i + 1 : ℕ) : ℝ) * (jacobi01 i).eval x) * (((j + 1 : ℕ) : ℝ) * (jacobi01 j).eval x) := by
        rw [sq, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
      rw [hsq, ← mul_assoc, mul_comm (1 - x) (α ^ 2), mul_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    simp_rw [hexpand]
    rw [intervalIntegral.integral_const_mul, intervalIntegral_finset_sum]
    · have hinner : ∀ i ∈ Finset.range k,
          (∫ x in (0 : ℝ)..1, ∑ j ∈ Finset.range k,
            (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) * ((1 - x) * (jacobi01 i).eval x * (jacobi01 j).eval x)) =
          ((i + 1 : ℕ) : ℝ) / 2 := by
        intro i hi
        rw [intervalIntegral_finset_sum]
        · have hterm : ∀ j ∈ Finset.range k,
              (∫ x in (0 : ℝ)..1, (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
                ((1 - x) * (jacobi01 i).eval x * (jacobi01 j).eval x)) =
              if j = i then ((i + 1 : ℕ) : ℝ) / 2 else 0 := by
            intro j _
            rw [intervalIntegral.integral_const_mul, jacobi01_orthogonality i j]
            by_cases hji : j = i
            · subst hji
              rw [if_pos rfl, if_pos rfl]
              have hj1 : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
              field_simp [hj1]
            · rw [if_neg hji, if_neg (Ne.symm hji), mul_zero]
          rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range k) i, if_pos hi]
        · intro j _
          exact (continuous_const.mul
            (((continuous_const.sub continuous_id).mul (jacobi01 i).continuous).mul
              (jacobi01 j).continuous)).intervalIntegrable 0 1
      rw [Finset.sum_congr rfl hinner, ← Finset.sum_div]
      dsimp [α]
      have hcast : ((2 * k : ℕ) : ℝ) * ((2 * k + 2 : ℕ) : ℝ) =
          4 * ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) := by push_cast; ring
      rw [hcast]
      field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos]
      nlinarith [hsum_nat]
    · intro i _
      have hc : Continuous (fun x : ℝ => ∑ j ∈ Finset.range k,
          (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) * ((1 - x) * (jacobi01 i).eval x * (jacobi01 j).eval x)) := by
        fun_prop
      exact hc.intervalIntegrable 0 1

end DualSmaleMultiscale
