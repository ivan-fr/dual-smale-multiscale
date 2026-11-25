/-
  DualSmale/PolynomialReduction.lean

  Exact all-n algebraic formulation of the Dual Smale Mean Value Conjecture and
  closed-form identities for the diagonal polynomial G_n(w) and its reciprocal
  Enestrom-Kakeya form R_n(u) = sum_{j=0}^{n-2} (n - 1 - j) u^j.
-/

import DualSmaleMultiscale.GraceWalshSzego

open scoped BigOperators
open Polynomial Complex

namespace DualSmale

private lemma eval_finset_sum_c {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) (z : ℂ) :
    (∑ i ∈ s, f i).eval z = ∑ i ∈ s, (f i).eval z := by
  change (Polynomial.evalRingHom z) (∑ i ∈ s, f i) = ∑ i ∈ s, (Polynomial.evalRingHom z) (f i)
  exact map_sum (Polynomial.evalRingHom z) f s

/-- Normalized critical-point divided difference `P(zeta_j) / zeta_j` expressed purely
    in terms of the inverse critical points `w : Fin (n - 1) → ℂ` (where `w_k = 1 / zeta_k`),
    so `P'(z) = ∏_{k} (1 - w_k z)` and `P(z)/z = ∑_{m=0}^{n-1} (-1)^m e_m(w) z^m / (m + 1)`. -/
noncomputable def dualSmaleQuotient (n : ℕ) (w : Fin (n - 1) → ℂ) (j : Fin (n - 1)) : ℂ :=
  ∑ m ∈ Finset.range n, ((-1 : ℂ) ^ m / ((m + 1 : ℕ) : ℂ)) * elemSym (n - 1) (fun k => w k / w j) m

/-- Polynomial `P_w(z) = ∑_{m=0}^{n-1} (-1)^m e_m(w) z^{m+1} / (m + 1)`. -/
noncomputable def polyFromInvCrits (n : ℕ) (w : Fin (n - 1) → ℂ) : ℂ[X] :=
  ∑ m ∈ Finset.range n, C (((-1 : ℂ) ^ m / ((m + 1 : ℕ) : ℂ)) * elemSym (n - 1) w m) * X ^ (m + 1)

theorem polyFromInvCrits_eval_zero (n : ℕ) (w : Fin (n - 1) → ℂ) :
    (polyFromInvCrits n w).eval 0 = 0 := by
  unfold polyFromInvCrits
  rw [eval_finset_sum_c]
  apply Finset.sum_eq_zero
  intro m _; simp

theorem derivative_polyFromInvCrits (n : ℕ) (w : Fin (n - 1) → ℂ) :
    derivative (polyFromInvCrits n w) =
      ∑ m ∈ Finset.range n, C ((-1 : ℂ) ^ m * elemSym (n - 1) w m) * X ^ m := by
  unfold polyFromInvCrits
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow]
  have hm : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  rw [Nat.add_sub_cancel, ← mul_assoc, ← map_mul]
  congr 2
  field_simp [hm]

theorem derivative_polyFromInvCrits_eval_zero {n : ℕ} (hn : 1 ≤ n) (w : Fin (n - 1) → ℂ) :
    (derivative (polyFromInvCrits n w)).eval 0 = 1 := by
  rw [derivative_polyFromInvCrits, eval_finset_sum_c]
  cases n with
  | zero => omega
  | succ k =>
    rw [Finset.sum_range_succ']
    have hrest : ∑ x ∈ Finset.range k,
        (C ((-1 : ℂ) ^ (x + 1) * elemSym (k + 1 - 1) w (x + 1)) * X ^ (x + 1)).eval 0 = 0 := by
      apply Finset.sum_eq_zero; intro x _; simp
    rw [hrest, zero_add]
    have he0 : elemSym (k + 1 - 1) w 0 = 1 := by cases k <;> rfl
    simp [eval_C]; exact he0

lemma elemSym_eq_zero_of_lt : ∀ (n : ℕ) (v : Fin n → ℂ) (k : ℕ), n < k → elemSym n v k = 0 := by
  intro n
  induction n with
  | zero => intro v k hk; cases k with | zero => omega | succ k => simp [elemSym]
  | succ n ihn =>
    intro v k hk
    cases k with
    | zero => omega
    | succ k =>
      simp only [elemSym]
      rw [ihn _ (k + 1) (by omega), ihn _ k (by omega), mul_zero, add_zero]

lemma elemSym_mul_scale (m : ℕ) (u : Fin m → ℂ) (c : ℂ) (d : ℕ) :
    elemSym m (fun i => u i * c) d = elemSym m u d * c ^ d := by
  induction m generalizing d with
  | zero => cases d <;> simp [elemSym]
  | succ m ih =>
    cases d with
    | zero => simp [elemSym]
    | succ d => simp only [elemSym, ih]; ring

theorem prod_one_sub_eq_sum_elemSym :
    ∀ (m : ℕ) (w : Fin m → ℂ) (z : ℂ),
      (∏ k : Fin m, (1 - w k * z)) = ∑ d ∈ Finset.range (m + 1), (-1 : ℂ) ^ d * elemSym m w d * z ^ d := by
  intro m
  induction m with
  | zero => intro w z; simp [elemSym]
  | succ m ih =>
    intro w z
    rw [Fin.prod_univ_castSucc, ih (fun i => w i.castSucc) z]
    have hlast : elemSym m (fun i => w i.castSucc) (m + 1) = 0 :=
      elemSym_eq_zero_of_lt m _ (m + 1) (by omega)
    symm
    rw [Finset.sum_range_succ']
    have he0_succ : elemSym (m + 1) w 0 = 1 := rfl
    rw [he0_succ]; simp only [pow_zero, mul_one]
    have hsplit : ∑ d ∈ Finset.range (m + 1),
        (-1 : ℂ) ^ (d + 1) * elemSym (m + 1) w (d + 1) * z ^ (d + 1) =
        (∑ d ∈ Finset.range (m + 1), (-1 : ℂ) ^ (d + 1) * elemSym m (fun i => w i.castSucc) (d + 1) * z ^ (d + 1)) -
        (w (Fin.last m) * z) * (∑ d ∈ Finset.range (m + 1), (-1 : ℂ) ^ d * elemSym m (fun i => w i.castSucc) d * z ^ d) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro d _; dsimp only [elemSym]; ring
    rw [hsplit]
    have h1 : (∑ d ∈ Finset.range (m + 1),
        (-1 : ℂ) ^ (d + 1) * elemSym m (fun i => w i.castSucc) (d + 1) * z ^ (d + 1)) + 1 =
        ∑ d ∈ Finset.range (m + 1), (-1 : ℂ) ^ d * elemSym m (fun i => w i.castSucc) d * z ^ d := by
      rw [Finset.sum_range_succ, hlast, mul_zero, zero_mul, add_zero]
      rw [Finset.sum_range_succ']
      have he0 : elemSym m (fun i => w i.castSucc) 0 = 1 := by cases m <;> rfl
      simp [he0]
    linear_combination h1

/-- Elementary symmetric polynomials are invariant under any permutation of coordinates. -/
theorem elemSym_comp_equiv (m : ℕ) (w : Fin m → ℂ) (σ : Equiv.Perm (Fin m)) (d : ℕ) :
    elemSym m (fun i => w (σ i)) d = elemSym m w d := by
  by_cases hd : m < d
  · rw [elemSym_eq_zero_of_lt m _ d hd, elemSym_eq_zero_of_lt m _ d hd]
  · -- Compare polynomial coefficients of ∑ (-1)^k e_k(w ∘ σ) X^k = ∑ (-1)^k e_k(w) X^k
    set P₁ : ℂ[X] := ∑ k ∈ Finset.range (m + 1), C ((-1 : ℂ) ^ k * elemSym m (fun i => w (σ i)) k) * X ^ k
    set P₂ : ℂ[X] := ∑ k ∈ Finset.range (m + 1), C ((-1 : ℂ) ^ k * elemSym m w k) * X ^ k
    have heval : ∀ z : ℂ, P₁.eval z = P₂.eval z := by
      intro z
      have h1 : P₁.eval z = ∏ k : Fin m, (1 - w (σ k) * z) := by
        dsimp [P₁]; rw [eval_finset_sum_c, prod_one_sub_eq_sum_elemSym]
        apply Finset.sum_congr rfl; intro k _; simp
      have h2 : P₂.eval z = ∏ k : Fin m, (1 - w k * z) := by
        dsimp [P₂]; rw [eval_finset_sum_c, prod_one_sub_eq_sum_elemSym]
        apply Finset.sum_congr rfl; intro k _; simp
      rw [h1, h2]
      exact Equiv.prod_comp σ (fun k => 1 - w k * z)
    have hPeq : P₁ = P₂ := Polynomial.funext heval
    have hcoeff := congrArg (fun P => P.coeff d) hPeq
    have hc1 : P₁.coeff d = (-1 : ℂ) ^ d * elemSym m (fun i => w (σ i)) d := by
      dsimp [P₁]
      change (Polynomial.lcoeff ℂ d) (∑ k ∈ Finset.range (m + 1), _) = _
      rw [map_sum, Finset.sum_eq_single d]
      · rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]; simp
      · intro b _ hbd; rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]; simp [Ne.symm hbd]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
    have hc2 : P₂.coeff d = (-1 : ℂ) ^ d * elemSym m w d := by
      dsimp [P₂]
      change (Polynomial.lcoeff ℂ d) (∑ k ∈ Finset.range (m + 1), _) = _
      rw [map_sum, Finset.sum_eq_single d]
      · rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]; simp
      · intro b _ hbd; rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]; simp [Ne.symm hbd]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
    rw [hc1, hc2] at hcoeff
    exact mul_left_cancel₀ (pow_ne_zero d (by norm_num : (-1 : ℂ) ≠ 0)) hcoeff

theorem is_critical_point_inv {n : ℕ} (hn : 1 ≤ n) (w : Fin (n - 1) → ℂ)
    (j : Fin (n - 1)) (hwj : w j ≠ 0) :
    (derivative (polyFromInvCrits n w)).eval (w j)⁻¹ = 0 := by
  rw [derivative_polyFromInvCrits, eval_finset_sum_c]
  have h1 : ∑ m ∈ Finset.range n,
      (C ((-1 : ℂ) ^ m * elemSym (n - 1) w m) * X ^ m).eval (w j)⁻¹ =
      ∑ m ∈ Finset.range ((n - 1) + 1), (-1 : ℂ) ^ m * elemSym (n - 1) w m * ((w j)⁻¹) ^ m := by
    have hnn : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    rw [hnn]
    apply Finset.sum_congr rfl; intro m _; simp
  rw [h1, ← prod_one_sub_eq_sum_elemSym]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [mul_inv_cancel₀ hwj, sub_self]

theorem eval_div_eq_dualSmaleQuotient {n : ℕ} (w : Fin (n - 1) → ℂ)
    (j : Fin (n - 1)) (hwj : w j ≠ 0) :
    (polyFromInvCrits n w).eval (w j)⁻¹ / (w j)⁻¹ = dualSmaleQuotient n w j := by
  unfold polyFromInvCrits dualSmaleQuotient
  rw [eval_finset_sum_c, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  simp only [eval_mul, eval_C, eval_pow, eval_X, div_eq_mul_inv]
  rw [elemSym_mul_scale]
  field_simp [hwj]
  rw [pow_succ']
  have h1 : w j * (1 / w j) = 1 := mul_one_div_cancel hwj
  linear_combination (elemSym (n - 1) w m * (1 / w j) ^ m) * h1

/-- Evaluation of `polyFromInvCrits n w` at any `z` expressed as `z * symMultiaffine (n - 1) c (w_k * z)`. -/
theorem polyFromInvCrits_eval_eq_mul_symMultiaffine {n : ℕ} (hn : 1 ≤ n)
    (w : Fin (n - 1) → ℂ) (z : ℂ) :
    (polyFromInvCrits n w).eval z =
      z * symMultiaffine (n - 1) (fun m => (-1 : ℂ) ^ m / ((m + 1 : ℕ) : ℂ)) (fun k => w k * z) := by
  unfold polyFromInvCrits symMultiaffine
  rw [eval_finset_sum_c, Finset.mul_sum]
  have hnn : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  rw [hnn]
  apply Finset.sum_congr rfl
  intro m _
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [elemSym_mul_scale, pow_succ]
  ring

/-- Elementary binomial absorption: `(a + 1) * C(a, b) = (b + 1) * C(a + 1, b + 1)`. -/
lemma mul_choose_succ_eq (a b : ℕ) : (a + 1) * Nat.choose a b = (b + 1) * Nat.choose (a + 1) (b + 1) := by
  by_cases h : b ≤ a
  · have h1 := Nat.choose_mul_factorial_mul_factorial h
    have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.succ_le_succ h)
    have hsub : (a + 1) - (b + 1) = a - b := by omega
    rw [hsub, Nat.factorial_succ a, Nat.factorial_succ b] at h2
    have hfac_pos : 0 < Nat.factorial b * Nat.factorial (a - b) := by positivity
    apply Nat.eq_of_mul_eq_mul_right hfac_pos
    calc (a + 1) * Nat.choose a b * (Nat.factorial b * Nat.factorial (a - b))
        = (a + 1) * (Nat.choose a b * Nat.factorial b * Nat.factorial (a - b)) := by ring
      _ = (a + 1) * Nat.factorial a := by rw [h1]
      _ = Nat.choose (a + 1) (b + 1) * ((b + 1) * Nat.factorial b) * Nat.factorial (a - b) := h2.symm
      _ = (b + 1) * Nat.choose (a + 1) (b + 1) * (Nat.factorial b * Nat.factorial (a - b)) := by ring
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- Diagonal polynomial `F_n(v) = symMultiaffine (n - 1) (fun m => (-1)^m / (m + 1)) (fun _ => v)`
    satisfies `n * v * F_n(v) = 1 - (1 - v)^n` for ALL `n ≥ 1` and `v : ℂ`. -/
theorem diag_polyFromInvCrits_closed_form {n : ℕ} (hn : 1 ≤ n) (v : ℂ) :
    (n : ℂ) * v *
      symMultiaffine (n - 1) (fun m => (-1 : ℂ) ^ m / ((m + 1 : ℕ) : ℂ)) (fun _ => v) =
      1 - (1 - v) ^ n := by
  unfold symMultiaffine
  have hnn : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  rw [hnn, Finset.mul_sum]
  -- Expand (1 - v)^n by binomial theorem
  have hbin : (1 - v) ^ n = ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * v ^ k := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [one_pow, mul_one, show (-v) ^ k = (-1 : ℂ) ^ k * v ^ k by rw [neg_eq_neg_one_mul, mul_pow]]
    ring
  rw [hbin]
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [show (1 : ℂ) - ((∑ k ∈ Finset.range n, (-1 : ℂ) ^ (k + 1) * (Nat.choose n (k + 1) : ℂ) * v ^ (k + 1)) + 1) =
      -(∑ k ∈ Finset.range n, (-1 : ℂ) ^ (k + 1) * (Nat.choose n (k + 1) : ℂ) * v ^ (k + 1)) by ring]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [elemSym_const]
  have hm1_ne : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have habs : (n : ℂ) * (Nat.choose (n - 1) m : ℂ) = ((m + 1 : ℕ) : ℂ) * (Nat.choose n (m + 1) : ℂ) := by
    have hnat : n * Nat.choose (n - 1) m = (m + 1) * Nat.choose n (m + 1) := by
      have h1 := mul_choose_succ_eq (n - 1) m
      rw [Nat.sub_add_cancel hn] at h1
      exact h1
    exact_mod_cast hnat
  have hpow : (-1 : ℂ) ^ (m + 1) = -((-1 : ℂ) ^ m) := by rw [pow_succ]; ring
  rw [hpow, pow_succ]
  field_simp [hm1_ne]
  linear_combination (v ^ m * v) * habs

/-- Symmetric multiaffine form `P1Form n w_rest = ∑_{m=0}^{n-2} (-1)^m e_m(w_rest) / ((m + 1)(m + 2))`. -/
noncomputable def P1Form (n : ℕ) (w_rest : Fin (n - 2) → ℂ) : ℂ :=
  symMultiaffine (n - 2) (fun m => (-1 : ℂ) ^ m / (((m + 1) * (m + 2) : ℕ) : ℂ)) w_rest

/-- Diagonal polynomial `G_n(w) = ∑_{m=0}^{n-2} (-1)^m C(n-2, m) w^m / ((m+1)(m+2))`. -/
noncomputable def GnPoly (n : ℕ) (w : ℂ) : ℂ :=
  P1Form n (fun _ => w)

theorem dualSmaleQuotient_at_one (n : ℕ) (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (hlast : w ⟨n - 2, by omega⟩ = 1) :
    dualSmaleQuotient n w ⟨n - 2, by omega⟩ =
      P1Form n (fun i => w ⟨i.val, by omega⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold dualSmaleQuotient P1Form symMultiaffine
  have hdiv : (fun k : Fin (m + 1) => w k / w (Fin.last m)) = w := by
    ext k; have hl : w (Fin.last m) = 1 := hlast; rw [hl, div_one]
  change (∑ k ∈ Finset.range (m + 2), ((-1 : ℂ) ^ k / ((k + 1 : ℕ) : ℂ)) *
      elemSym (m + 1) (fun k => w k / w (Fin.last m)) k) =
      ∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ k / (((k + 1) * (k + 2) : ℕ) : ℂ)) *
        elemSym m (fun i => w i.castSucc) k
  rw [hdiv]
  have hvlast : w (Fin.last m) = 1 := hlast
  have hgt : elemSym m (fun i => w i.castSucc) (m + 1) = 0 :=
    elemSym_eq_zero_of_lt m _ (m + 1) (by omega)
  rw [Finset.sum_range_succ']
  have he0_succ : elemSym (m + 1) w 0 = 1 := rfl
  rw [he0_succ]
  simp only [pow_zero, Nat.cast_one, div_one, mul_one, zero_add]
  have hsplit : ∑ j ∈ Finset.range (m + 1),
      ((-1 : ℂ) ^ (j + 1) / ((j + 2 : ℕ) : ℂ)) * elemSym (m + 1) w (j + 1) =
      (∑ j ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (j + 1) / ((j + 2 : ℕ) : ℂ)) * elemSym m (fun i => w i.castSucc) (j + 1)) +
      (∑ j ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (j + 1) / ((j + 2 : ℕ) : ℂ)) * elemSym m (fun i => w i.castSucc) j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp only [elemSym, hvlast, one_mul]; ring
  rw [hsplit]
  have hshift : (∑ j ∈ Finset.range (m + 1),
        ((-1 : ℂ) ^ (j + 1) / ((j + 2 : ℕ) : ℂ)) * elemSym m (fun i => w i.castSucc) (j + 1)) + 1 =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℂ) ^ j / ((j + 1 : ℕ) : ℂ)) * elemSym m (fun i => w i.castSucc) j := by
    rw [Finset.sum_range_succ, hgt, mul_zero, add_zero]
    rw [Finset.sum_range_succ']
    have he0 : elemSym m (fun i => w i.castSucc) 0 = 1 := by cases m <;> rfl
    simp only [he0, pow_zero, zero_add, Nat.cast_one, div_one, mul_one]
  have hsum : (∑ j ∈ Finset.range (m + 1),
        ((-1 : ℂ) ^ (j + 1) / ((j + 2 : ℕ) : ℂ)) * elemSym m (fun i => w i.castSucc) (j + 1)) +
      (∑ j ∈ Finset.range (m + 1),
        ((-1 : ℂ) ^ (j + 1) / ((j + 2 : ℕ) : ℂ)) * elemSym m (fun i => w i.castSucc) j) + 1 =
      (∑ j ∈ Finset.range (m + 1), ((-1 : ℂ) ^ j / ((j + 1 : ℕ) : ℂ)) * elemSym m (fun i => w i.castSucc) j) +
      (∑ j ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (j + 1) / ((j + 2 : ℕ) : ℂ)) * elemSym m (fun i => w i.castSucc) j) := by
    linear_combination hshift
  rw [hsum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : ((j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : ((j + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : (((j + 1) * (j + 2) : ℕ) : ℂ) = ((j + 1 : ℕ) : ℂ) * ((j + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast]
  have hcast2 : ((j + 2 : ℕ) : ℂ) = ((j + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
  field_simp [h1, h2]; rw [hcast2]; ring

/-- **Exact Closed Form of `G_n(w)` for ALL `n ≥ 2`**:
    `n * (n - 1) * w^2 * G_n(w) = n * w - 1 + (1 - w)^n`. -/
theorem GnPoly_closed_form {n : ℕ} (hn : 2 ≤ n) (w : ℂ) :
    (n : ℂ) * ((n - 1 : ℕ) : ℂ) * w ^ 2 * GnPoly n w =
      (n : ℂ) * w - 1 + (1 - w) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold GnPoly P1Form symMultiaffine
  simp only [show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega]
  rw [Finset.mul_sum]
  -- Expand (1 - w)^(m+2) = 1 - (m+2) w + ∑_{k=0}^m (-1)^(k+2) C(m+2, k+2) w^(k+2)
  have hbin : (1 - w) ^ (m + 2) =
      ∑ j ∈ Finset.range (m + 3), (-1 : ℂ) ^ j * (Nat.choose (m + 2) j : ℂ) * w ^ j := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    rw [one_pow, mul_one, show (-w) ^ j = (-1 : ℂ) ^ j * w ^ j by rw [neg_eq_neg_one_mul, mul_pow]]
    ring
  rw [hbin]
  conv_rhs => rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pow_zero, zero_add, pow_one, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_one, mul_one]
  have hcancel : ((m + 2 : ℕ) : ℂ) * w - 1 +
      ((∑ x ∈ Finset.range (m + 1),
          (-1 : ℂ) ^ (x + 1 + 1) * (Nat.choose (m + 2) (x + 1 + 1) : ℂ) * w ^ (x + 1 + 1)) +
        (-1 : ℂ) * ((m + 2 : ℕ) : ℂ) * w + 1) =
      ∑ x ∈ Finset.range (m + 1),
        (-1 : ℂ) ^ x * (Nat.choose (m + 2) (x + 2) : ℂ) * w ^ (x + 2) := by
    have hsum_eq : ∑ x ∈ Finset.range (m + 1),
          (-1 : ℂ) ^ (x + 1 + 1) * (Nat.choose (m + 2) (x + 1 + 1) : ℂ) * w ^ (x + 1 + 1) =
        ∑ x ∈ Finset.range (m + 1),
          (-1 : ℂ) ^ x * (Nat.choose (m + 2) (x + 2) : ℂ) * w ^ (x + 2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [show x + 1 + 1 = x + 2 by omega, pow_add]
      norm_num
    rw [hsum_eq]; ring
  rw [hcancel]
  apply Finset.sum_congr rfl
  intro k _
  rw [elemSym_const]
  simp only [show m + 2 - 2 = m by omega]
  have hden : (((k + 1) * (k + 2) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
  have habs : ((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) * (Nat.choose m k : ℂ) =
      (((k + 1) * (k + 2) : ℕ) : ℂ) * (Nat.choose (m + 2) (k + 2) : ℂ) := by
    have h1 := mul_choose_succ_eq m k
    have h2 := mul_choose_succ_eq (m + 1) (k + 1)
    have hnat : (m + 2) * (m + 1) * Nat.choose m k = ((k + 1) * (k + 2)) * Nat.choose (m + 2) (k + 2) := by
      calc (m + 2) * (m + 1) * Nat.choose m k
          = (m + 2) * ((m + 1) * Nat.choose m k) := by ring
        _ = (m + 2) * ((k + 1) * Nat.choose (m + 1) (k + 1)) := by rw [h1]
        _ = (k + 1) * ((m + 2) * Nat.choose (m + 1) (k + 1)) := by ring
        _ = (k + 1) * ((k + 2) * Nat.choose (m + 2) (k + 2)) := by rw [h2]
        _ = ((k + 1) * (k + 2)) * Nat.choose (m + 2) (k + 2) := by ring
    exact_mod_cast hnat
  rw [pow_add]
  field_simp [hden]
  linear_combination (w ^ k * w ^ 2) * habs

/-- Enestrom-Kakeya form `R_n(u) = ∑_{j=0}^{n-2} (n - 1 - j) u^j` (strictly decreasing positive
    coefficients `n-1, n-2, ..., 1`). -/
noncomputable def RnPoly (n : ℕ) (u : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n - 1), ((n - 1 - j : ℕ) : ℂ) * u ^ j

/-- Telescoping identity: `(1 - u) * R_n(u) = (n - 1) - ∑_{k=1}^{n-1} u^k`. -/
theorem one_sub_mul_RnPoly {n : ℕ} (hn : 2 ≤ n) (u : ℂ) :
    (1 - u) * RnPoly n u = ((n - 1 : ℕ) : ℂ) - ∑ k ∈ Finset.range (n - 1), u ^ (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  clear hn
  unfold RnPoly
  simp only [show m + 2 - 1 = m + 1 by omega]
  induction m with
  | zero => simp
  | succ m ih =>
    conv_lhs => rw [Finset.sum_range_succ']
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [Nat.sub_zero, pow_zero, mul_one]
    have hshift : ∑ x ∈ Finset.range (m + 1), ((m + 1 + 1 - (x + 1) : ℕ) : ℂ) * u ^ (x + 1) =
        u * ∑ x ∈ Finset.range (m + 1), ((m + 1 - x : ℕ) : ℂ) * u ^ x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [show m + 1 + 1 - (x + 1) = m + 1 - x by omega, pow_succ]
      ring
    rw [hshift, mul_add]
    have hmul : (1 - u) * (u * ∑ x ∈ Finset.range (m + 1), ((m + 1 - x : ℕ) : ℂ) * u ^ x) =
        u * ((1 - u) * ∑ x ∈ Finset.range (m + 1), ((m + 1 - x : ℕ) : ℂ) * u ^ x) := by ring
    rw [hmul, ih]
    have hu_sum : u * ∑ k ∈ Finset.range (m + 1), u ^ (k + 1) =
        ∑ k ∈ Finset.range (m + 1), u ^ (k + 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; rw [pow_succ]; ring
    have hshift2 : ∑ k ∈ Finset.range (m + 1), u ^ (k + 1) + u ^ (m + 1 + 1) =
        u + ∑ k ∈ Finset.range (m + 1), u ^ (k + 2) := by
      rw [← Finset.sum_range_succ (fun k => u ^ (k + 1)) (m + 1),
          Finset.sum_range_succ' (fun k => u ^ (k + 1)) (m + 1)]
      simp only [zero_add, pow_one]
      rw [add_comm]
    have hcast : ((m + 1 + 1 : ℕ) : ℂ) = ((m + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
    rw [hcast]
    linear_combination -hu_sum + hshift2

/-- **Second Telescoping Identity**: `(1 - u)^2 * R_n(u) = n*(1 - u) - 1 + u^n`. -/
theorem one_sub_sq_mul_RnPoly {n : ℕ} (hn : 2 ≤ n) (u : ℂ) :
    (1 - u) ^ 2 * RnPoly n u = (n : ℂ) * (1 - u) - 1 + u ^ n := by
  have h1 : (1 - u) ^ 2 * RnPoly n u = (1 - u) * ((1 - u) * RnPoly n u) := by ring
  rw [h1, one_sub_mul_RnPoly hn u, mul_sub]
  have hgeom : (1 - u) * ∑ k ∈ Finset.range (n - 1), u ^ (k + 1) = u - u ^ n := by
    have hpull : ∑ k ∈ Finset.range (n - 1), u ^ (k + 1) = u * ∑ k ∈ Finset.range (n - 1), u ^ k := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; rw [pow_succ]; ring
    rw [hpull]
    have hg := mul_geom_sum u (n - 1)
    -- (u - 1) * ∑ u^k = u^(n-1) - 1 => (1 - u) * ∑ u^k = 1 - u^(n-1)
    have hnn : (n - 1) + 1 = n := by omega
    calc (1 - u) * (u * ∑ k ∈ Finset.range (n - 1), u ^ k)
        = -u * ((u - 1) * ∑ k ∈ Finset.range (n - 1), u ^ k) := by ring
      _ = -u * (u ^ (n - 1) - 1) := by rw [hg]
      _ = u - u ^ ((n - 1) + 1) := by rw [pow_succ]; ring
      _ = u - u ^ n := by rw [hnn]
  rw [hgeom]
  have hcast : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
    have : n = (n - 1) + 1 := by omega
    conv_rhs => rw [this]
    push_cast; ring
  rw [hcast]; ring

/-- **Exact Reciprocal Identity for `G_n(w)` (ALL `n ≥ 2`, ALL `w : ℂ`, including `w = 0`)**:
    `n * (n - 1) * G_n(w) = R_n(1 - w) = ∑_{j=0}^{n-2} (n - 1 - j) (1 - w)^j`! -/
theorem GnPoly_eq_RnPoly {n : ℕ} (hn : 2 ≤ n) (w : ℂ) :
    (n : ℂ) * ((n - 1 : ℕ) : ℂ) * GnPoly n w = RnPoly n (1 - w) := by
  by_cases hw : w = 0
  · subst hw
    simp only [sub_zero]
    -- At w = 0: G_n(0) = 1/2 and R_n(1) = ∑_{j=0}^{n-2} (n - 1 - j) = n*(n-1)/2
    have hG0 : GnPoly n 0 = 1 / 2 := by
      unfold GnPoly P1Form symMultiaffine
      cases m : n - 2 with
      | zero => simp [elemSym]
      | succ k =>
        rw [Finset.sum_range_succ']
        have hzero : ∑ x ∈ Finset.range (k + 1),
            ((-1 : ℂ) ^ (x + 1) / (((x + 1 + 1) * (x + 1 + 2) : ℕ) : ℂ)) *
              elemSym (k + 1) (fun _ => (0 : ℂ)) (x + 1) = 0 := by
          apply Finset.sum_eq_zero
          intro x _
          rw [elemSym_const, zero_pow (Nat.succ_ne_zero x), mul_zero, mul_zero]
        rw [hzero, zero_add]
        have he0 : elemSym (k + 1) (fun _ => (0 : ℂ)) 0 = 1 := rfl
        rw [he0]; norm_num
    have hR1 : 2 * RnPoly n 1 = (n : ℂ) * ((n - 1 : ℕ) : ℂ) := by
      unfold RnPoly
      simp only [one_pow, mul_one]
      have hnat : ∀ m : ℕ, 2 * ∑ j ∈ Finset.range (m + 1), (m + 1 - j) = (m + 2) * (m + 1) := by
        intro m
        induction m with
        | zero => decide
        | succ m ih =>
          rw [Finset.sum_range_succ']
          simp only [Nat.sub_zero, show ∀ x, m + 1 + 1 - (x + 1) = m + 1 - x by intro x; omega]
          linarith
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      simp only [show m + 2 - 1 = m + 1 by omega]
      exact_mod_cast hnat m
    rw [hG0]
    linear_combination -hR1 / 2
  · have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
    apply mul_left_cancel₀ hw2
    have h1 : w ^ 2 * ((n : ℂ) * ((n - 1 : ℕ) : ℂ) * GnPoly n w) =
        (n : ℂ) * ((n - 1 : ℕ) : ℂ) * w ^ 2 * GnPoly n w := by ring
    rw [h1, GnPoly_closed_form hn w]
    have h2 := one_sub_sq_mul_RnPoly hn (1 - w)
    rw [show (1 : ℂ) - (1 - w) = w by ring] at h2
    rw [h2]

/-- Value of `G_n(1) = 1 / n` for all `n ≥ 2`. -/
theorem GnPoly_at_one {n : ℕ} (hn : 2 ≤ n) : GnPoly n 1 = 1 / (n : ℂ) := by
  have h := GnPoly_eq_RnPoly hn 1
  simp only [sub_self] at h
  have hR0 : RnPoly n 0 = ((n - 1 : ℕ) : ℂ) := by
    unfold RnPoly
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [show m + 2 - 1 = m + 1 by omega]
    rw [Finset.sum_range_succ']
    have hrest : ∑ x ∈ Finset.range m, ((m + 1 - (x + 1) : ℕ) : ℂ) * (0 : ℂ) ^ (x + 1) = 0 := by
      apply Finset.sum_eq_zero; intro x _; simp
    rw [hrest, zero_add, Nat.sub_zero, pow_zero, mul_one]
  rw [hR0] at h
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm_ne : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn_ne]
  apply mul_right_cancel₀ hm_ne
  linear_combination h

/-- `G_n(w)` is the evaluation of `diagPoly (n - 2) c` where `c m = (-1)^m / ((m+1)(m+2))`. -/
noncomputable def GnCoeff (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m / (((m + 1) * (m + 2) : ℕ) : ℂ)

lemma eval_diagPoly_GnCoeff (n : ℕ) (w : ℂ) :
    (diagPoly (n - 2) GnCoeff).eval w = GnPoly n w := by
  rw [eval_diagPoly]; rfl

/-- Exact polynomial derivative of `G_n` at `w = 1` is `-(n - 2) / (n * (n - 1)) ≠ 0` for `n ≥ 3`. -/
theorem derivative_GnPoly_at_one_ne_zero {n : ℕ} (hn : 3 ≤ n) :
    (derivative (diagPoly (n - 2) GnCoeff)).eval 1 ≠ 0 := by
  -- Express diagPoly (n - 2) GnCoeff in terms of R_n(1 - X) / (n*(n-1))
  set Rpoly : ℂ[X] := ∑ j ∈ Finset.range (n - 1), C (((n - 1 - j : ℕ) : ℂ)) * (1 - X) ^ j
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm_ne : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpoly_eq : C ((n : ℂ) * ((n - 1 : ℕ) : ℂ)) * diagPoly (n - 2) GnCoeff = Rpoly := by
    apply Polynomial.funext
    intro w
    rw [eval_mul, eval_C, eval_diagPoly_GnCoeff, GnPoly_eq_RnPoly (by omega) w]
    dsimp [Rpoly, RnPoly]
    rw [eval_finset_sum_c]
    apply Finset.sum_congr rfl; intro j _; simp
  have hderiv := congrArg (fun P => (derivative P).eval 1) hpoly_eq
  rw [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C] at hderiv
  -- Compute (derivative Rpoly).eval 1 = -((n - 2) : ℂ)
  have hRderiv : (derivative Rpoly).eval 1 = -((n - 2 : ℕ) : ℂ) := by
    dsimp [Rpoly]
    rw [map_sum, eval_finset_sum_c]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hrest : ∑ x ∈ Finset.range k,
        (derivative (C ((k + 2 - (x + 1 + 1) : ℕ) : ℂ) * (1 - X) ^ (x + 1 + 1))).eval 1 = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_pow]
      simp [eval_mul, eval_pow, eval_sub, eval_one, eval_X]
    rw [hrest, zero_add]
    simp [derivative_mul, derivative_C, derivative_sub, derivative_one, derivative_X]
  rw [hRderiv] at hderiv
  intro h0
  rw [h0, mul_zero] at hderiv
  have hne : -((n - 2 : ℕ) : ℂ) ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
  exact hne hderiv.symm

end DualSmale
