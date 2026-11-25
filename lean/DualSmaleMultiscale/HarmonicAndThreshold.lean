/-
  DualSmaleMultiscale/HarmonicAndThreshold.lean

  THEOREM 6 (Harmonic-Sum Dual Smale Theorem — All n >= 2):
    Let S_j = sum_{k != j} |zeta_j / zeta_k| = sum_{k != j} |w_k / w_j|.
    - If S_j <= 1, then |P(zeta_j)/zeta_j| >= 3 - exp(1) > 5/18.
    - If S_j <= 7/4, then |P(zeta_j)/zeta_j| > 18/1000.
    Corollaries: n-independent > 5/18 lower bound for Chebyshev-squared (|zeta_k| = k^2)
    and geometric-ladder (|zeta_k| = 2^k) critical-point moduli for ALL n >= 2!

  THEOREM 7 (Exact Non-Vanishing of the Closest Critical Point for 2 <= n <= 9 & Sharpness at n = 10):
    - For EVERY 2 <= n <= 9 and EVERY polynomial P = polyFromInvCrits n w, the closest
      critical point zeta_{j0} (|w k| <= |w j0| for all k) NEVER satisfies P(zeta_{j0}) = 0!
      (Proved via Grace-Walsh-Szego + Cayley transform + exact rational Wall-Routh
      continued-fraction Hurwitz certificates for n = 3..9.)
    - Sharpness at n = 10: there exists w_0 with 0 < |w_0| < 1 such that for
      P'(z) = (1 - z)(1 - w_0 z)^8, zeta_1 = 1 is strictly the unique closest critical
      point and P(1) = 0! (Proved via Maximum Modulus Principle on D(w_c, 1/100) subset D(0, 1).)
-/

import DualSmaleMultiscale.PolynomialReduction
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

open scoped BigOperators
open Polynomial Complex DualSmale

namespace DualSmaleMultiscale

/-! ### Section 1: Harmonic-Sum Dual Smale Theorem (All `n ≥ 2`) -/

/-- Elementary symmetric polynomial factorial bound:
    `‖elemSym m u d‖ * d! ≤ (∑ i : Fin m, ‖u i‖) ^ d`. -/
lemma norm_elemSym_mul_fact_le :
    ∀ (m : ℕ) (u : Fin m → ℂ) (d : ℕ),
      ‖elemSym m u d‖ * (d.factorial : ℝ) ≤ (∑ i : Fin m, ‖u i‖) ^ d := by
  intro m
  induction m with
  | zero =>
    intro u d
    cases d with
    | zero => simp [elemSym]
    | succ d => simp [elemSym]
  | succ m ih =>
    intro u d
    cases d with
    | zero => simp [elemSym]
    | succ d =>
      simp only [elemSym]
      set u' : Fin m → ℂ := fun i => u i.castSucc
      set S' : ℝ := ∑ i : Fin m, ‖u' i‖
      set a : ℝ := ‖u (Fin.last m)‖
      have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      have ha_nn : 0 ≤ a := norm_nonneg _
      have hsum : ∑ i : Fin (m + 1), ‖u i‖ = S' + a := Fin.sum_univ_castSucc (fun i => ‖u i‖)
      rw [hsum]
      have htri : ‖elemSym m u' (d + 1) + u (Fin.last m) * elemSym m u' d‖ ≤
          ‖elemSym m u' (d + 1)‖ + a * ‖elemSym m u' d‖ := by
        calc ‖elemSym m u' (d + 1) + u (Fin.last m) * elemSym m u' d‖
            ≤ ‖elemSym m u' (d + 1)‖ + ‖u (Fin.last m) * elemSym m u' d‖ := norm_add_le _ _
          _ = ‖elemSym m u' (d + 1)‖ + a * ‖elemSym m u' d‖ := by rw [norm_mul]
      have hih1 : ‖elemSym m u' (d + 1)‖ * ((d + 1).factorial : ℝ) ≤ S' ^ (d + 1) := ih u' (d + 1)
      have hih2 : ‖elemSym m u' d‖ * (d.factorial : ℝ) ≤ S' ^ d := ih u' d
      have hfact : ((d + 1).factorial : ℝ) = ((d + 1 : ℕ) : ℝ) * (d.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hstep : ‖elemSym m u' (d + 1) + u (Fin.last m) * elemSym m u' d‖ * ((d + 1).factorial : ℝ) ≤
          S' ^ (d + 1) + ((d + 1 : ℕ) : ℝ) * a * S' ^ d := by
        calc ‖elemSym m u' (d + 1) + u (Fin.last m) * elemSym m u' d‖ * ((d + 1).factorial : ℝ)
            ≤ (‖elemSym m u' (d + 1)‖ + a * ‖elemSym m u' d‖) * ((d + 1).factorial : ℝ) :=
              mul_le_mul_of_nonneg_right htri (by positivity)
          _ = ‖elemSym m u' (d + 1)‖ * ((d + 1).factorial : ℝ) +
              ((d + 1 : ℕ) : ℝ) * a * (‖elemSym m u' d‖ * (d.factorial : ℝ)) := by rw [hfact]; ring
          _ ≤ S' ^ (d + 1) + ((d + 1 : ℕ) : ℝ) * a * S' ^ d := by
              have hmul : ((d + 1 : ℕ) : ℝ) * a * (‖elemSym m u' d‖ * (d.factorial : ℝ)) ≤
                  ((d + 1 : ℕ) : ℝ) * a * S' ^ d :=
                mul_le_mul_of_nonneg_left hih2 (by positivity)
              linarith
      -- Binomial inequality: S'^(d+1) + (d+1) * a * S'^d ≤ (S' + a)^(d+1)
      have hbin : S' ^ (d + 1) + ((d + 1 : ℕ) : ℝ) * a * S' ^ d ≤ (S' + a) ^ (d + 1) := by
        rw [add_comm S' a, add_pow]
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        simp only [zero_add, Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one,
          Nat.sub_zero, Nat.add_sub_cancel, Nat.cast_one, one_mul, mul_one]
        have hrest_nn : 0 ≤ ∑ x ∈ Finset.range d,
            a ^ (x + 1 + 1) * S' ^ (d + 1 - (x + 1 + 1)) * (Nat.choose (d + 1) (x + 1 + 1) : ℝ) :=
          Finset.sum_nonneg (fun _ _ => by positivity)
        have hcomm : a * S' ^ d * ((d + 1 : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) * a * S' ^ d := by ring
        linarith
      exact le_trans hstep hbin

/-- Scale-invariant form of `dualSmaleQuotient` at any coordinate `j` (`w j ≠ 0`) via permutation
    to the last coordinate. -/
lemma dualSmaleQuotient_eq_P1Form_swap {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (j : Fin (n - 1)) (hwj : w j ≠ 0) :
    let σ : Equiv.Perm (Fin (n - 1)) := Equiv.swap j ⟨n - 2, by omega⟩
    dualSmaleQuotient n w j =
      P1Form n (fun i => w (σ ⟨i.val, by omega⟩) / w j) := by
  intro σ
  set w' : Fin (n - 1) → ℂ := fun k => w (σ k) / w j
  have hlast : w' ⟨n - 2, by omega⟩ = 1 := by
    dsimp [w', σ]
    rw [Equiv.swap_apply_right, div_self hwj]
  have hq : dualSmaleQuotient n w j = dualSmaleQuotient n w' ⟨n - 2, by omega⟩ := by
    unfold dualSmaleQuotient
    apply Finset.sum_congr rfl; intro m _
    congr 1
    have hfun : (fun k : Fin (n - 1) => w' k / w' ⟨n - 2, by omega⟩) =
        (fun k : Fin (n - 1) => (fun i => w i / w j) (σ k)) := by
      ext k; dsimp [w']; rw [Equiv.swap_apply_right, div_self hwj, div_one]
    rw [hfun]
    exact (elemSym_comp_equiv (n - 1) (fun i => w i / w j) σ m).symm
  rw [hq, dualSmaleQuotient_at_one n hn w' hlast]

/-- Sum of off-diagonal ratios equals the sum of the swapped `(n - 2)` coordinates. -/
lemma sum_erase_eq_sum_swap {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ) (j : Fin (n - 1)) :
    let σ : Equiv.Perm (Fin (n - 1)) := Equiv.swap j ⟨n - 2, by omega⟩
    ∑ k ∈ Finset.univ.erase j, ‖w k / w j‖ =
      ∑ i : Fin (n - 2), ‖w (σ ⟨i.val, by omega⟩) / w j‖ := by
  intro σ
  set lastIdx : Fin (n - 1) := ⟨n - 2, by omega⟩
  have h1 : ∑ k : Fin (n - 1), ‖w k / w j‖ = ∑ k : Fin (n - 1), ‖w (σ k) / w j‖ :=
    (Equiv.sum_comp σ (fun k => ‖w k / w j‖)).symm
  have h2 : ∑ k : Fin (n - 1), ‖w k / w j‖ =
      ‖w j / w j‖ + ∑ k ∈ Finset.univ.erase j, ‖w k / w j‖ :=
    (Finset.add_sum_erase Finset.univ (fun k => ‖w k / w j‖) (Finset.mem_univ j)).symm
  have h3 : ∑ k : Fin (n - 1), ‖w (σ k) / w j‖ =
      (∑ i : Fin (n - 2), ‖w (σ ⟨i.val, by omega⟩) / w j‖) + ‖w (σ lastIdx) / w j‖ := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hsum := Fin.sum_univ_castSucc (fun k : Fin (m + 1) => ‖w (σ k) / w j‖)
    exact hsum
  have h4 : w (σ lastIdx) = w j := by dsimp [σ, lastIdx]; rw [Equiv.swap_apply_right]
  rw [h4] at h3
  linarith

/-- Core harmonic-sum perturbation bound on `P1Form n u`:
    for any `u : Fin (n - 2) → ℂ` with `S = ∑ i, ‖u i‖ > 0`,
    `‖P1Form n u - 1/2‖ ≤ (exp S - 1 - S - S^2 / 2) / S^2`. -/
lemma norm_P1Form_sub_half_le {n : ℕ} (hn : 2 ≤ n) (u : Fin (n - 2) → ℂ)
    {S : ℝ} (hS_pos : 0 < S) (hS_le : ∑ i : Fin (n - 2), ‖u i‖ ≤ S) :
    ‖P1Form n u - (1 / 2 : ℂ)‖ ≤ (Real.exp S - 1 - S - S ^ 2 / 2) / S ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold P1Form symMultiaffine
  rw [Finset.sum_range_succ']
  have he0 : elemSym (m + 2 - 2) u 0 = 1 := by cases m <;> rfl
  simp only [he0, pow_zero, zero_add, Nat.cast_one, mul_one]
  have h12 : (1 : ℂ) / ((1 * 2 : ℕ) : ℂ) = 1 / 2 := by norm_num
  rw [h12, add_sub_cancel_right]
  calc ‖∑ x ∈ Finset.range m,
          ((-1 : ℂ) ^ (x + 1) / (((x + 1 + 1) * (x + 1 + 2) : ℕ) : ℂ)) * elemSym m u (x + 1)‖
      ≤ ∑ x ∈ Finset.range m,
          ‖((-1 : ℂ) ^ (x + 1) / (((x + 1 + 1) * (x + 1 + 2) : ℕ) : ℂ)) * elemSym m u (x + 1)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ x ∈ Finset.range m, S ^ (x + 1) / ((x + 3).factorial : ℝ) := by
        apply Finset.sum_le_sum; intro x _
        rw [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
        have hf := norm_elemSym_mul_fact_le m u (x + 1)
        have hSpow : (∑ i : Fin m, ‖u i‖) ^ (x + 1) ≤ S ^ (x + 1) :=
          pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hS_le _
        have hfe : ‖elemSym m u (x + 1)‖ * ((x + 1).factorial : ℝ) ≤ S ^ (x + 1) := le_trans hf hSpow
        have hfact3 : ((x + 3).factorial : ℝ) =
            (((x + 1 + 1) * (x + 1 + 2) : ℕ) : ℝ) * ((x + 1).factorial : ℝ) := by
          have hnat : (x + 3).factorial = (x + 3) * ((x + 2) * (x + 1).factorial) := by
            rw [show x + 3 = (x + 2) + 1 by omega, Nat.factorial_succ,
                show x + 2 = (x + 1) + 1 by omega, Nat.factorial_succ]
          rw [hnat]; push_cast; ring
        have hd1 : (0 : ℝ) < (((x + 1 + 1) * (x + 1 + 2) : ℕ) : ℝ) := by positivity
        have hd2 : (0 : ℝ) < ((x + 1).factorial : ℝ) := by positivity
        rw [one_div, inv_mul_eq_div, div_le_div_iff₀ hd1 (by positivity : (0 : ℝ) < ((x + 3).factorial : ℝ)),
          hfact3]
        have h1 := mul_le_mul_of_nonneg_right hfe (le_of_lt hd1)
        linarith
    _ = (∑ x ∈ Finset.range m, S ^ (x + 3) / ((x + 3).factorial : ℝ)) / S ^ 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl; intro x _
        have hpow : S ^ (x + 3) = S ^ (x + 1) * S ^ 2 := by ring
        rw [hpow, mul_div_right_comm, mul_div_cancel_right₀ _ (pow_ne_zero 2 (ne_of_gt hS_pos))]
    _ ≤ (Real.exp S - 1 - S - S ^ 2 / 2) / S ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg S)
        have hexp := Real.sum_le_exp_of_nonneg (le_of_lt hS_pos) (m + 3)
        rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ'] at hexp
        simp only [Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, pow_zero, pow_one,
          Nat.cast_one, Nat.cast_ofNat, div_one] at hexp
        have hreindex : (∑ x ∈ Finset.range m, S ^ (x + 1 + 1 + 1) / (((x + 1 + 1 + 1).factorial : ℕ) : ℝ)) =
            ∑ x ∈ Finset.range m, S ^ (x + 3) / ((x + 3).factorial : ℝ) := by
          apply Finset.sum_congr rfl; intro x _
          rw [show x + 1 + 1 + 1 = x + 3 by omega]
        rw [hreindex] at hexp
        linarith

/-- **THEOREM 6A (Harmonic-Sum Dual Smale Theorem at `S ≤ 1` — All `n ≥ 2`)**:
    If `∑_{k ≠ j} ‖w k / w j‖ ≤ 1` (i.e. `∑_{k ≠ j} |ζ_j / ζ_k| ≤ 1`), then
    `3 - exp 1 ≤ ‖dualSmaleQuotient n w j‖` and hence `5 / 18 < ‖dualSmaleQuotient n w j‖`! -/
theorem harmonic_sum_dual_smale_one {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (j : Fin (n - 1)) (hwj : w j ≠ 0)
    (hS : ∑ k ∈ Finset.univ.erase j, ‖w k / w j‖ ≤ 1) :
    (3 - Real.exp 1 ≤ ‖dualSmaleQuotient n w j‖) ∧ (5 / 18 : ℝ) < ‖dualSmaleQuotient n w j‖ := by
  set σ : Equiv.Perm (Fin (n - 1)) := Equiv.swap j ⟨n - 2, by omega⟩
  set u : Fin (n - 2) → ℂ := fun i => w (σ ⟨i.val, by omega⟩) / w j
  have hq : dualSmaleQuotient n w j = P1Form n u := dualSmaleQuotient_eq_P1Form_swap hn w j hwj
  have hSu : ∑ i : Fin (n - 2), ‖u i‖ ≤ 1 := by
    rw [← sum_erase_eq_sum_swap hn w j]; exact hS
  have herr := norm_P1Form_sub_half_le hn u one_pos hSu
  rw [one_pow, div_one] at herr
  have htri : (1 / 2 : ℝ) - ‖P1Form n u - (1 / 2 : ℂ)‖ ≤ ‖P1Form n u‖ := by
    have h := norm_sub_norm_le (1 / 2 : ℂ) (P1Form n u)
    rw [norm_sub_rev] at h
    have h12 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [h12] at h; linarith
  have hge : 3 - Real.exp 1 ≤ ‖dualSmaleQuotient n w j‖ := by rw [hq]; linarith
  have hexp_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  exact ⟨hge, by linarith⟩

/-- Elementary bound `exp(7/4) < 5.756` proved directly via `Real.exp_bound`! -/
lemma exp_seven_quarters_lt : Real.exp (7 / 4 : ℝ) < 5.756 := by
  have h1 : Real.exp (7 / 4 : ℝ) = Real.exp (7 / 8 : ℝ) * Real.exp (7 / 8 : ℝ) := by
    rw [← Real.exp_add]; congr 1; norm_num
  have hbound := Real.exp_bound (x := (7 / 8 : ℝ)) (n := 8) (by norm_num) (by omega)
  have hsum : ∑ m ∈ Finset.range 8, (7 / 8 : ℝ) ^ m / (m.factorial : ℝ) < 2.39887 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
    norm_num
  have hrem : |(7 / 8 : ℝ)| ^ 8 * (((8 : ℕ) + 1 : ℕ) / ((8 : ℕ).factorial * (8 : ℕ))) < 0.0001 := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 7 / 8)]
    norm_num [Nat.factorial]
  have he78 : Real.exp (7 / 8 : ℝ) < 2.399 := by
    have hle := (abs_le.mp hbound).2
    linarith
  have hpos : 0 < Real.exp (7 / 8 : ℝ) := Real.exp_pos _
  rw [h1]
  nlinarith

/-- **THEOREM 6B (Extended Harmonic-Sum Dual Smale Theorem up to `S ≤ 7/4` — All `n ≥ 2`)**:
    If `∑_{k ≠ j} ‖w k / w j‖ ≤ 7 / 4`, then `18 / 1000 < ‖dualSmaleQuotient n w j‖`! -/
theorem harmonic_sum_dual_smale_seven_quarters {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (j : Fin (n - 1)) (hwj : w j ≠ 0)
    (hS : ∑ k ∈ Finset.univ.erase j, ‖w k / w j‖ ≤ 7 / 4) :
    (18 / 1000 : ℝ) < ‖dualSmaleQuotient n w j‖ := by
  set σ : Equiv.Perm (Fin (n - 1)) := Equiv.swap j ⟨n - 2, by omega⟩
  set u : Fin (n - 2) → ℂ := fun i => w (σ ⟨i.val, by omega⟩) / w j
  have hq : dualSmaleQuotient n w j = P1Form n u := dualSmaleQuotient_eq_P1Form_swap hn w j hwj
  have hSu : ∑ i : Fin (n - 2), ‖u i‖ ≤ 7 / 4 := by
    rw [← sum_erase_eq_sum_swap hn w j]; exact hS
  have herr := norm_P1Form_sub_half_le hn u (by norm_num : (0 : ℝ) < 7 / 4) hSu
  have htri : (1 / 2 : ℝ) - ‖P1Form n u - (1 / 2 : ℂ)‖ ≤ ‖P1Form n u‖ := by
    have h := norm_sub_norm_le (1 / 2 : ℂ) (P1Form n u)
    rw [norm_sub_rev] at h
    have h12 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [h12] at h; linarith
  have hexp := exp_seven_quarters_lt
  have hbound : (Real.exp (7 / 4 : ℝ) - 1 - 7 / 4 - (7 / 4) ^ 2 / 2) / (7 / 4) ^ 2 < 1 / 2 - 18 / 1000 := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < (7 / 4) ^ 2)]
    linarith [hexp]
  rw [hq]
  linarith

/-- **COROLLARY 6.1 (Chebyshev-Squared Moduli — All `n ≥ 2`)**:
    If `|ζ_k| = (k + 1)^2 * r_1` (i.e. `‖w k‖ = 1 / ((k + 1)^2 * r_1)`) for arbitrary complex
    arguments, then `5 / 18 < ‖dualSmaleQuotient n w ⟨0, _⟩‖` for EVERY `n ≥ 2`! -/
theorem chebyshev_squared_dual_smale {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    {r₁ : ℝ} (hr₁ : 0 < r₁)
    (hw_mod : ∀ k : Fin (n - 1), ‖w k‖ = 1 / (((k.val + 1 : ℕ) : ℝ) ^ 2 * r₁)) :
    (5 / 18 : ℝ) < ‖dualSmaleQuotient n w ⟨0, by omega⟩‖ := by
  have hw0 : w ⟨0, by omega⟩ ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hw_mod ⟨0, by omega⟩]; positivity
  refine (harmonic_sum_dual_smale_one hn w ⟨0, by omega⟩ hw0 ?_).2
  have h0_norm : ‖w ⟨0, by omega⟩‖ = 1 / r₁ := by
    rw [hw_mod ⟨0, by omega⟩]; simp
  -- Bound ∑_{k ≠ 0} ‖w k / w 0‖ = ∑_{m=1}^{n-2} 1/(m+1)^2 ≤ ∑_{m=1}^{n-2} (1/m - 1/(m+1)) = 1 - 1/(n-1) ≤ 1!
  have hterm : ∀ k : Fin (n - 1), k ≠ ⟨0, by omega⟩ →
      ‖w k / w ⟨0, by omega⟩‖ ≤ 1 / (k.val : ℝ) - 1 / ((k.val + 1 : ℕ) : ℝ) := by
    intro k hk
    have hk_pos : 1 ≤ k.val := by
      by_contra h0; push Not at h0
      exact hk (Fin.ext (by dsimp; omega))
    rw [norm_div, hw_mod k, h0_norm]
    have hEq : (1 / (((k.val + 1 : ℕ) : ℝ) ^ 2 * r₁)) / (1 / r₁) = 1 / ((k.val + 1 : ℕ) : ℝ) ^ 2 := by
      have hk1 : ((k.val + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [ne_of_gt hr₁, hk1]
    rw [hEq]
    have hk_r : (0 : ℝ) < (k.val : ℝ) := by exact_mod_cast (show 0 < k.val by omega)
    have hk1_r : (0 : ℝ) < ((k.val + 1 : ℕ) : ℝ) := by positivity
    have hdiff : 1 / (k.val : ℝ) - 1 / ((k.val + 1 : ℕ) : ℝ) =
        1 / ((k.val : ℝ) * ((k.val + 1 : ℕ) : ℝ)) := by
      have hc : ((k.val + 1 : ℕ) : ℝ) = (k.val : ℝ) + 1 := by push_cast; ring
      field_simp [ne_of_gt hk_r, ne_of_gt hk1_r]; rw [hc]; ring
    rw [hdiff]
    apply one_div_le_one_div_of_le (by positivity)
    have hc : ((k.val + 1 : ℕ) : ℝ) = (k.val : ℝ) + 1 := by push_cast; ring
    rw [hc]; nlinarith
  have htele : ∀ m : ℕ, ∑ j ∈ Finset.range m, (1 / ((j + 1 : ℕ) : ℝ) - 1 / ((j + 2 : ℕ) : ℝ)) ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hsum_eq : ∑ j ∈ Finset.range (m + 1), (1 / ((j + 1 : ℕ) : ℝ) - 1 / ((j + 2 : ℕ) : ℝ)) =
          1 - 1 / ((m + 2 : ℕ) : ℝ) := by
        clear ih
        induction m with
        | zero => simp
        | succ m ih2 =>
          rw [Finset.sum_range_succ, ih2]; ring
      rw [hsum_eq]
      have : (0 : ℝ) < 1 / ((m + 2 : ℕ) : ℝ) := by positivity
      linarith
  have hsum_le : ∑ k ∈ Finset.univ.erase ⟨0, by omega⟩, ‖w k / w ⟨0, by omega⟩‖ ≤
      ∑ j ∈ Finset.range (n - 2), (1 / ((j + 1 : ℕ) : ℝ) - 1 / ((j + 2 : ℕ) : ℝ)) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    set z0 : Fin (m + 2 - 1) := ⟨0, by omega⟩
    have h1 : ∑ k ∈ Finset.univ.erase z0, ‖w k / w z0‖ =
        ∑ j : Fin m, ‖w ⟨j.val + 1, by omega⟩ / w z0‖ := by
      have htot := Fin.sum_univ_succ (fun k : Fin (m + 1) => ‖w ⟨k.val, by omega⟩ / w z0‖)
      have herase := Finset.add_sum_erase (Finset.univ : Finset (Fin (m + 2 - 1)))
        (fun k => ‖w k / w z0‖) (Finset.mem_univ z0)
      have htot_eq : ∑ k : Fin (m + 1), ‖w ⟨k.val, by omega⟩ / w z0‖ =
          ∑ k : Fin (m + 2 - 1), ‖w k / w z0‖ := rfl
      have h0_eq : ‖w ⟨(0 : Fin (m + 1)).val, by omega⟩ / w z0‖ = ‖w z0 / w z0‖ := rfl
      have hsucc_eq : ∑ j : Fin m, ‖w ⟨j.succ.val, by omega⟩ / w z0‖ =
          ∑ j : Fin m, ‖w ⟨j.val + 1, by omega⟩ / w z0‖ := rfl
      linarith
    change ∑ k ∈ Finset.univ.erase z0, ‖w k / w z0‖ ≤ _
    have hrange : ∑ j : Fin m, ‖w ⟨j.val + 1, by omega⟩ / w z0‖ =
        ∑ j ∈ Finset.range (m + 2 - 2), if hj : j < m then ‖w ⟨j + 1, by omega⟩ / w z0‖ else 0 := by
      rw [show m + 2 - 2 = m by omega, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl; intro j _; simp [j.isLt]
    rw [h1, hrange]
    apply Finset.sum_le_sum; intro j hj
    rw [Finset.mem_range] at hj
    rw [dif_pos (by omega)]
    have hne : (⟨j + 1, by omega⟩ : Fin (m + 2 - 1)) ≠ z0 := by
      intro heq; have := congrArg Fin.val heq; simp [z0] at this
    exact hterm ⟨j + 1, by omega⟩ hne
  exact le_trans hsum_le (htele (n - 2))

/-! ### Section 2: Wall-Routh Continued Fraction Hurwitz Engine & Non-Vanishing for `2 ≤ n ≤ 9` -/

/-- Bottom-up Wall-Routh continued fraction pair `(P_k(s), P_{k-1}(s))` for a list of positive
    quotients `[c_1, ..., c_d]` (head = top quotient `c_1`, tail = bottom quotient `c_d`). -/
def wallPair : List ℝ → ℂ → ℂ × ℂ
  | [], _ => (1, 0)
  | c :: cs, s =>
    let pq := wallPair cs s
    ((c : ℂ) * s * pq.1 + pq.2, pq.1)

/-- Wall-Routh sum polynomial `W(cs, s) = P_d(s) + P_{d-1}(s)`. -/
def wallSum (cs : List ℝ) (s : ℂ) : ℂ :=
  (wallPair cs s).1 + (wallPair cs s).2

/-- For `Re(s) > 0` and any nonempty list of strictly positive quotients `cs`,
    `p = (wallPair cs s).1` and `q = (wallPair cs s).2` are nonzero and `Re(p / q) > 0`. -/
lemma wallPair_re_pos :
    ∀ (cs : List ℝ), cs ≠ [] → (∀ c ∈ cs, 0 < c) →
      ∀ s : ℂ, 0 < s.re →
        (wallPair cs s).1 ≠ 0 ∧ (wallPair cs s).2 ≠ 0 ∧
        0 < ((wallPair cs s).1 / (wallPair cs s).2).re := by
  intro cs
  induction cs with
  | nil => intro hne; exact absurd rfl hne
  | cons c cs ih =>
    intro _ hpos s hs
    have hc : 0 < c := hpos c (List.mem_cons_self)
    cases cs with
    | nil =>
      simp only [wallPair, mul_one, add_zero, div_one]
      have hre : 0 < ((c : ℂ) * s).re := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact mul_pos hc hs
      have hne : (c : ℂ) * s ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hre; linarith
      exact ⟨hne, one_ne_zero, hre⟩
    | cons c' cs' =>
      have hih := ih (List.cons_ne_nil c' cs') (fun x hx => hpos x (List.mem_cons_of_mem c hx)) s hs
      rcases hih with ⟨hp_ne, hq_ne, hratio_pos⟩
      set p := (wallPair (c' :: cs') s).1
      set q := (wallPair (c' :: cs') s).2
      have hdiv_eq : ((c : ℂ) * s * p + q) / p = (c : ℂ) * s + (p / q)⁻¹ := by
        field_simp [hp_ne, hq_ne]
      have hinv_re : 0 < ((p / q)⁻¹).re := by
        rw [Complex.inv_re]
        have hns : 0 < Complex.normSq (p / q) := Complex.normSq_pos.mpr (div_ne_zero hp_ne hq_ne)
        exact div_pos hratio_pos hns
      have hcs_re : 0 < ((c : ℂ) * s).re := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact mul_pos hc hs
      have hnew_re : 0 < (((c : ℂ) * s * p + q) / p).re := by
        rw [hdiv_eq, Complex.add_re]; linarith
      have hnew_ne : (c : ℂ) * s * p + q ≠ 0 := by
        intro h0; rw [h0, zero_div, Complex.zero_re] at hnew_re; linarith
      exact ⟨hnew_ne, hp_ne, hnew_re⟩

/-- On the imaginary axis `Re(s) = 0`, `(wallPair cs s).1` and `(wallPair cs s).2` have opposite
    real/imaginary parity and never vanish simultaneously. -/
lemma wallPair_imag_axis :
    ∀ (cs : List ℝ) (s : ℂ), s.re = 0 →
      (((wallPair cs s).1.re = 0 ∧ (wallPair cs s).2.im = 0) ∨
       ((wallPair cs s).1.im = 0 ∧ (wallPair cs s).2.re = 0)) ∧
      ¬((wallPair cs s).1 = 0 ∧ (wallPair cs s).2 = 0) := by
  intro cs
  induction cs with
  | nil =>
    intro s _
    simp only [wallPair]
    exact ⟨Or.inr ⟨by simp, by simp⟩, fun h => one_ne_zero h.1⟩
  | cons c cs ih =>
    intro s hs
    rcases ih s hs with ⟨hpar, hnz⟩
    simp only [wallPair]
    constructor
    · rcases hpar with ⟨hpre, hqim⟩ | ⟨hpim, hqre⟩
      · right
        refine ⟨?_, hpre⟩
        simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, hs, hpre, hqim]
        ring
      · left
        refine ⟨?_, hpim⟩
        simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, hs, hpim, hqre]
        ring
    · rintro ⟨h1, h2⟩
      rw [h2, mul_zero, zero_add] at h1
      exact hnz ⟨h2, h1⟩

/-- **Wall-Routh Hurwitz Certificate Theorem**:
    For ANY nonempty list of strictly positive reals `cs` and ANY `s : ℂ` with `0 ≤ s.re`,
    `wallSum cs s ≠ 0`! -/
theorem wallSum_ne_zero_of_re_nonneg {cs : List ℝ} (hne : cs ≠ []) (hpos : ∀ c ∈ cs, 0 < c)
    {s : ℂ} (hs : 0 ≤ s.re) : wallSum cs s ≠ 0 := by
  unfold wallSum
  rcases lt_or_eq_of_le hs with hlt | heq
  · rcases wallPair_re_pos cs hne hpos s hlt with ⟨_, hq_ne, hre_pos⟩
    intro h0
    have hdiv : (wallPair cs s).1 / (wallPair cs s).2 = -1 := by
      have h1 : (wallPair cs s).1 = -(wallPair cs s).2 := by linear_combination h0
      rw [h1, neg_div, div_self hq_ne]
    rw [hdiv] at hre_pos
    simp at hre_pos
    linarith
  · rcases wallPair_imag_axis cs s heq.symm with ⟨hpar, hnz⟩
    intro h0
    have hre0 : (wallPair cs s).1.re + (wallPair cs s).2.re = 0 := by
      have := congrArg Complex.re h0; simpa using this
    have him0 : (wallPair cs s).1.im + (wallPair cs s).2.im = 0 := by
      have := congrArg Complex.im h0; simpa using this
    rcases hpar with ⟨h1re, h2im⟩ | ⟨h1im, h2re⟩
    · have h2re : (wallPair cs s).2.re = 0 := by linarith
      have h1im : (wallPair cs s).1.im = 0 := by linarith
      exact hnz ⟨Complex.ext h1re h1im, Complex.ext h2re h2im⟩
    · have h1re : (wallPair cs s).1.re = 0 := by linarith
      have h2im : (wallPair cs s).2.im = 0 := by linarith
      exact hnz ⟨Complex.ext h1re h1im, Complex.ext h2re h2im⟩

/-- Cayley transform reduction: if `H_n(s) = ∑_{j=0}^{n-2} (n-1-j) * (2s)^j * (1+s)^{n-2-j}`
    never vanishes on `0 ≤ s.re` and `RnPoly n 2 ≠ 0`, then `RnPoly n (1 - w) ≠ 0` for all `‖w‖ ≤ 1`! -/
lemma RnPoly_ne_zero_of_cayley {n : ℕ} (hn : 2 ≤ n)
    (hH : ∀ s : ℂ, 0 ≤ s.re →
      ∑ j ∈ Finset.range (n - 1), ((n - 1 - j : ℕ) : ℂ) * (2 * s) ^ j * (1 + s) ^ (n - 2 - j) ≠ 0) :
    ∀ w : ℂ, ‖w‖ ≤ 1 → RnPoly n (1 - w) ≠ 0 := by
  intro w hw
  by_cases hw1 : w = -1
  · subst hw1
    -- At w = -1, 1 - w = 2, and RnPoly n 2 is a sum of strictly positive real numbers!
    unfold RnPoly
    have hre_pos : 0 < (∑ j ∈ Finset.range (n - 1), ((n - 1 - j : ℕ) : ℂ) * (1 - (-1 : ℂ)) ^ j).re := by
      rw [Complex.re_sum]
      apply Finset.sum_pos
      · intro j hj
        rw [Finset.mem_range] at hj
        have h12 : (1 - (-1 : ℂ)) ^ j = ((2 ^ j : ℕ) : ℂ) := by norm_num
        rw [h12, ← Nat.cast_mul, Complex.natCast_re]
        exact_mod_cast Nat.mul_pos (by omega) (Nat.pow_pos (by norm_num))
      · exact Finset.nonempty_range_iff.mpr (by omega)
    intro h0; rw [h0, Complex.zero_re] at hre_pos; linarith
  · -- Define s = (1 - w) / (1 + w); then 0 ≤ s.re, 1 + s = 2 / (1 + w) ≠ 0, and 2s / (1 + s) = 1 - w!
    have h1w : 1 + w ≠ 0 := fun h0 => hw1 (by linear_combination h0)
    set s : ℂ := (1 - w) / (1 + w)
    have hs_re : 0 ≤ s.re := by
      dsimp [s]
      rw [Complex.div_re]
      have hnum : (1 - w).re * (1 + w).re + (1 - w).im * (1 + w).im = 1 - Complex.normSq w := by
        simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.one_re, Complex.one_im, Complex.normSq_apply]
        ring
      have hns1 : Complex.normSq w ≤ 1 := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
      have hden_pos : 0 < Complex.normSq (1 + w) := Complex.normSq_pos.mpr h1w
      have hEq : (1 - w).re * (1 + w).re / Complex.normSq (1 + w) +
          (1 - w).im * (1 + w).im / Complex.normSq (1 + w) =
          ((1 - w).re * (1 + w).re + (1 - w).im * (1 + w).im) / Complex.normSq (1 + w) := by ring
      rw [hEq, hnum]
      exact div_nonneg (by linarith) (le_of_lt hden_pos)
    have h1s_ne : 1 + s ≠ 0 := by
      dsimp [s]
      have h1 : 1 + (1 - w) / (1 + w) = 2 / (1 + w) := by field_simp [h1w]; ring
      rw [h1]
      exact div_ne_zero (by norm_num) h1w
    have hrel : 2 * s / (1 + s) = 1 - w := by
      dsimp [s]; field_simp [h1w]; ring
    have hscale : (1 + s) ^ (n - 2) * RnPoly n (1 - w) =
        ∑ j ∈ Finset.range (n - 1), ((n - 1 - j : ℕ) : ℂ) * (2 * s) ^ j * (1 + s) ^ (n - 2 - j) := by
      unfold RnPoly
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j hj
      rw [Finset.mem_range] at hj
      rw [← hrel, div_pow]
      have hpow : (1 + s) ^ (n - 2) = (1 + s) ^ (n - 2 - j) * (1 + s) ^ j := by
        rw [← pow_add, show n - 2 - j + j = n - 2 by omega]
      rw [hpow]
      have hj_ne : (1 + s) ^ j ≠ 0 := pow_ne_zero j h1s_ne
      field_simp [hj_ne]
    intro h0
    rw [h0, mul_zero] at hscale
    exact hH s hs_re hscale.symm

/-- Exact non-vanishing of `RnPoly n (1 - w)` on `‖w‖ ≤ 1` for EVERY `2 ≤ n ≤ 9`! -/
theorem RnPoly_one_sub_ne_zero_le_9 {n : ℕ} (hn2 : 2 ≤ n) (hn9 : n ≤ 9)
    {w : ℂ} (hw : ‖w‖ ≤ 1) : RnPoly n (1 - w) ≠ 0 := by
  have hcheck : ∀ (cs : List ℝ) (scale : ℂ), cs ≠ [] → (∀ c ∈ cs, 0 < c) → scale ≠ 0 →
      (∀ s : ℂ, ∑ j ∈ Finset.range (n - 1), ((n - 1 - j : ℕ) : ℂ) * (2 * s) ^ j * (1 + s) ^ (n - 2 - j) =
        scale * wallSum cs s) → RnPoly n (1 - w) ≠ 0 := by
    intro cs scale hne hpos hsc hid
    apply RnPoly_ne_zero_of_cayley hn2 _ w hw
    intro s hs
    rw [hid s]
    exact mul_ne_zero hsc (wallSum_ne_zero_of_re_nonneg hne hpos hs)
  interval_cases n
  · -- n = 2: RnPoly 2 (1 - w) = 1
    simp [RnPoly]
  · -- n = 3
    refine hcheck [2] 2 (by simp) (by norm_num) (by norm_num) (fun s => ?_)
    simp [wallSum, wallPair, Finset.sum_range_succ]; ring
  · -- n = 4
    refine hcheck [11/10, 10/3] 3 (by simp) (by norm_num) (by norm_num) (fun s => ?_)
    simp [wallSum, wallPair, Finset.sum_range_succ]; ring
  · -- n = 5
    refine hcheck [13/16, 128/59, 59/16] 4 (by simp) (by norm_num) (by norm_num) (fun s => ?_)
    simp [wallSum, wallPair, Finset.sum_range_succ]; ring
  · -- n = 6
    refine hcheck [19/28, 84/47, 2209/896, 896/235] 5 (by simp) (by norm_num) (by norm_num) (fun s => ?_)
    simp [wallSum, wallPair, Finset.sum_range_succ]; ring
  · -- n = 7
    refine hcheck [20/33, 3267/2008, 504008/235389, 50879689/21051872, 83872/21399] 6
      (by simp) (by norm_num) (by norm_num) (fun s => ?_)
    simp [wallSum, wallPair, Finset.sum_range_succ]; ring
  · -- n = 8
    refine hcheck [247/438, 31974/20383, 415466689/192790080, 36326404800/17338044779,
        723542475769/331736267520, 24117504/5954291] 7
      (by simp) (by norm_num) (by norm_num) (fun s => ?_)
    simp [wallSum, wallPair, Finset.sum_range_succ]; ring
  · -- n = 9
    refine hcheck [251/466, 108578/69253, 4795978009/1919999220, 1414650069075/411265034764,
        8816706858436/2011392144245, 25738722258843/17352245329424, 11687792/8787273] 8
      (by simp) (by norm_num) (by norm_num) (fun s => ?_)
    simp [wallSum, wallPair, Finset.sum_range_succ]; ring

/-- **THEOREM 7A (Exact Non-Vanishing of the Closest Critical Point for `2 ≤ n ≤ 9`)**:
    For EVERY degree `2 ≤ n ≤ 9`, EVERY polynomial `P = polyFromInvCrits n w`, and EVERY
    closest critical point `ζ_{j₀}` (attaining `‖w k‖ ≤ ‖w j₀‖` for all `k`, `w j₀ ≠ 0`),
    we have `dualSmaleQuotient n w j₀ ≠ 0` (equivalently `P(ζ_{j₀}) ≠ 0`)! -/
theorem closest_crit_nonvanishing_le_9 {n : ℕ} (hn2 : 2 ≤ n) (hn9 : n ≤ 9)
    (w : Fin (n - 1) → ℂ) (j₀ : Fin (n - 1)) (hwj₀ : w j₀ ≠ 0)
    (hmax : ∀ k : Fin (n - 1), ‖w k‖ ≤ ‖w j₀‖) :
    dualSmaleQuotient n w j₀ ≠ 0 := by
  by_cases hn2_eq : n = 2
  · subst hn2_eq
    have hq := dualSmaleQuotient_eq_P1Form_swap (le_rfl) w j₀ hwj₀
    rw [hq]; unfold P1Form symMultiaffine; simp [elemSym]
  · have hn3 : 3 ≤ n := by omega
    set σ : Equiv.Perm (Fin (n - 1)) := Equiv.swap j₀ ⟨n - 2, by omega⟩
    set u : Fin (n - 2) → ℂ := fun i => w (σ ⟨i.val, by omega⟩) / w j₀
    have hq : dualSmaleQuotient n w j₀ = P1Form n u := dualSmaleQuotient_eq_P1Form_swap hn2 w j₀ hwj₀
    have hu_ball : ∀ i : Fin (n - 2), ‖u i - 0‖ ≤ 1 := by
      intro i
      rw [sub_zero]
      dsimp [u]
      rw [norm_div, div_le_one (norm_pos_iff.mpr hwj₀)]
      exact hmax _
    -- Apply Grace-Walsh-Szego on the closed unit disk!
    obtain ⟨ζ, hζ_ball, hζ_eq⟩ :=
      grace_walsh_szego_closedBall (m := n - 2) (by omega) one_pos
        (fun m => (-1 : ℂ) ^ m / (((m + 1) * (m + 2) : ℕ) : ℂ)) u hu_ball
    rw [sub_zero] at hζ_ball
    rw [hq]
    change symMultiaffine (n - 2) _ u ≠ 0
    rw [hζ_eq]
    change GnPoly n ζ ≠ 0
    intro h0
    have hR := GnPoly_eq_RnPoly hn2 ζ
    rw [h0, mul_zero] at hR
    exact RnPoly_one_sub_ne_zero_le_9 hn2 hn9 hζ_ball hR.symm

/-! ### Section 3: Exact Sharpness at `n = 10` (`∃ w₀, 0 < ‖w₀‖ < 1 ∧ P(1) = 0`) -/

/-- **THEOREM 7B (Sharpness at `n = 10`)**:
    There exists `w₀ : ℂ` with `0 < ‖w₀‖ < 1` such that `RnPoly 10 (1 - w₀) = 0`, and
    consequently for `w = fun k => if k.val = 8 then 1 else w₀` (i.e. `P'(z) = (1 - z)(1 - w₀ z)^8`),
    the unique closest critical point `ζ = 1` satisfies `dualSmaleQuotient 10 w ⟨8, _⟩ = 0`! -/
theorem closest_crit_vanishing_witness_10 :
    ∃ w₀ : ℂ, w₀ ≠ 0 ∧ ‖w₀‖ < 1 ∧ RnPoly 10 (1 - w₀) = 0 ∧
      dualSmaleQuotient 10 (fun k : Fin 9 => if k.val = 8 then (1 : ℂ) else w₀) ⟨8, by omega⟩ = 0 := by
  -- Define polynomial Q10(w) = ∑_{j=0}^8 (9 - j) * (1 - w)^j
  set Q : ℂ[X] := ∑ j ∈ Finset.range 9, C ((9 - j : ℕ) : ℂ) * (1 - X) ^ j
  have hQ_eval : ∀ w : ℂ, Q.eval w = RnPoly 10 (1 - w) := by
    intro w
    dsimp [Q, RnPoly]
    change (Polynomial.evalRingHom w) _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl; intro j _; simp
  -- Center wc = 1/8 - (7/8)*I (so u = 1 - wc = (7/8)*(1 + I) has tiny dyadic powers!), radius r = 1/50
  set wc : ℂ := (1 / 8 : ℂ) - (7 / 8 : ℂ) * Complex.I
  set r : ℝ := 1 / 50
  have hwc_norm : ‖wc‖ < 9 / 10 := by
    have hsq : ‖wc‖ ^ 2 < (9 / 10 : ℝ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      dsimp [wc]; simp; norm_num
    nlinarith [norm_nonneg wc]
  have hwc_pos : 1 / 2 < ‖wc‖ := by
    have hsq : (1 / 2 : ℝ) ^ 2 < ‖wc‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      dsimp [wc]; simp; norm_num
    nlinarith [norm_nonneg wc]
  -- Prove ∃ w₀ ∈ closedBall wc r, Q.eval w₀ = 0 by Maximum Modulus Principle on (Q.eval ·)⁻¹!
  have hex_root : ∃ w₀ ∈ Metric.closedBall wc r, Q.eval w₀ = 0 := by
    by_contra hno
    push Not at hno
    -- Compute exact Taylor coefficients of Q(wc + h) = ∑_{k=0}^8 c_k h^k!
    set u : ℂ := 1 - wc
    set coeff : ℕ → ℂ := fun k =>
      ∑ j ∈ Finset.range 9,
        if k ≤ j then ((9 - j : ℕ) : ℂ) * (Nat.choose j k : ℂ) * (-1 : ℂ) ^ k * u ^ (j - k) else 0
    have hQ_taylor : ∀ h : ℂ, Q.eval (wc + h) = ∑ k ∈ Finset.range 9, coeff k * h ^ k := by
      intro h
      rw [hQ_eval]
      unfold RnPoly
      have h1 : 1 - (wc + h) = u - h := by dsimp [u]; ring
      simp only [show 10 - 1 = 9 by omega, h1]
      have hexp : ∀ j ∈ Finset.range 9,
          ((9 - j : ℕ) : ℂ) * (u - h) ^ j =
          ∑ k ∈ Finset.range 9,
            (if k ≤ j then ((9 - j : ℕ) : ℂ) * (Nat.choose j k : ℂ) * (-1 : ℂ) ^ k * u ^ (j - k) else 0) * h ^ k := by
        intro j hj
        rw [Finset.mem_range] at hj
        have hbin : (u - h) ^ j = ∑ k ∈ Finset.range (j + 1),
            (Nat.choose j k : ℂ) * (-1 : ℂ) ^ k * u ^ (j - k) * h ^ k := by
          rw [sub_eq_add_neg, add_comm, add_pow]
          apply Finset.sum_congr rfl; intro k _
          rw [neg_eq_neg_one_mul, mul_pow]; ring
        rw [hbin, Finset.mul_sum]
        have hsplit : (∑ k ∈ Finset.range 9,
            (if k ≤ j then ((9 - j : ℕ) : ℂ) * (Nat.choose j k : ℂ) * (-1 : ℂ) ^ k * u ^ (j - k) else 0) * h ^ k) =
            ∑ k ∈ Finset.range (j + 1),
              ((9 - j : ℕ) : ℂ) * (Nat.choose j k : ℂ) * (-1 : ℂ) ^ k * u ^ (j - k) * h ^ k := by
          rw [← Finset.sum_subset (Finset.range_mono (by omega : j + 1 ≤ 9))]
          · apply Finset.sum_congr rfl; intro k hk
            rw [Finset.mem_range] at hk
            rw [if_pos (by omega)]
          · intro k _ hk
            rw [Finset.mem_range] at hk
            rw [if_neg (by omega), zero_mul]
        rw [hsplit]
        apply Finset.sum_congr rfl; intro k _; ring
      rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_mul]
    -- Exact dyadic powers of u = 7/8 + (7/8)*I (instant algebra using Complex.I_sq)!
    have hu1 : u = (7 / 8 : ℂ) + (7 / 8 : ℂ) * Complex.I := by dsimp [u, wc]; ring
    have hu2 : u ^ 2 = (49 / 32 : ℂ) * Complex.I := by
      rw [sq, hu1]; linear_combination (49 / 64 : ℂ) * Complex.I_sq
    have hu3 : u ^ 3 = (-343 / 256 : ℂ) + (343 / 256 : ℂ) * Complex.I := by
      rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one, hu2, hu1]
      linear_combination (343 / 256 : ℂ) * Complex.I_sq
    have hu4 : u ^ 4 = (-2401 / 1024 : ℂ) := by
      rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, hu2]
      linear_combination (2401 / 1024 : ℂ) * Complex.I_sq
    have hu5 : u ^ 5 = (-16807 / 8192 : ℂ) - (16807 / 8192 : ℂ) * Complex.I := by
      rw [show (5 : ℕ) = 4 + 1 by rfl, pow_add, pow_one, hu4, hu1]; ring
    have hu6 : u ^ 6 = (-117649 / 32768 : ℂ) * Complex.I := by
      rw [show (6 : ℕ) = 4 + 2 by rfl, pow_add, hu4, hu2]; ring
    have hu7 : u ^ 7 = (823543 / 262144 : ℂ) - (823543 / 262144 : ℂ) * Complex.I := by
      rw [show (7 : ℕ) = 4 + 3 by rfl, pow_add, hu4, hu3]; ring
    have hu8 : u ^ 8 = (5764801 / 1048576 : ℂ) := by
      rw [show (8 : ℕ) = 4 + 4 by rfl, pow_add, hu4]; ring
    -- Exact rational bounds on ‖coeff 0‖, ‖coeff 1‖, and ‖coeff k‖ (k = 2..8)!
    have hc0_ub : ‖coeff 0‖ < 3 / 5 := by
      have hsq : ‖coeff 0‖ ^ 2 < (3 / 5 : ℝ) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        dsimp [coeff]
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [hu8, hu7, hu6, hu5, hu4, hu3, hu2]
        norm_num [hu1]
      nlinarith [norm_nonneg (coeff 0)]
    have hc1_lb : 75 < ‖coeff 1‖ := by
      have hsq : (75 : ℝ) ^ 2 < ‖coeff 1‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        dsimp [coeff]
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [hu8, hu7, hu6, hu5, hu4, hu3, hu2]
        norm_num [hu1]
      nlinarith [norm_nonneg (coeff 1)]
    have hc2_ub : ‖coeff 2‖ * r ^ 2 ≤ 1 / 10 := by
      have hsq : ‖coeff 2‖ ^ 2 ≤ (250 : ℝ) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        dsimp [coeff]
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [hu8, hu7, hu6, hu5, hu4, hu3, hu2]
        norm_num [hu1, Nat.choose]
      have hle : ‖coeff 2‖ ≤ 250 := by nlinarith [norm_nonneg (coeff 2)]
      dsimp [r]; nlinarith
    have hc_tail : ∀ k ∈ Finset.Ico 3 9, ‖coeff k‖ * r ^ k ≤ 1 / 60 := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hrc : r = 1 / 50 := rfl
      rw [hrc]
      have hcheck_k : ∀ B : ℝ, 0 ≤ B → ‖coeff k‖ ^ 2 ≤ B ^ 2 → B * (1 / 50 : ℝ) ^ k ≤ 1 / 60 →
          ‖coeff k‖ * (1 / 50 : ℝ) ^ k ≤ 1 / 60 := by
        intro B hB hsq hB_le
        have hle : ‖coeff k‖ ≤ B := by nlinarith [norm_nonneg (coeff k)]
        calc ‖coeff k‖ * (1 / 50 : ℝ) ^ k ≤ B * (1 / 50 : ℝ) ^ k :=
              mul_le_mul_of_nonneg_right hle (by positivity)
          _ ≤ 1 / 60 := hB_le
      rcases hk with ⟨hk3, hk9⟩
      interval_cases k
      · refine hcheck_k 400 (by norm_num) ?_ (by norm_num)
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        dsimp [coeff]; simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [hu8, hu7, hu6, hu5, hu4, hu3, hu2]; norm_num [hu1, Nat.choose]
      · refine hcheck_k 400 (by norm_num) ?_ (by norm_num)
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        dsimp [coeff]; simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [hu8, hu7, hu6, hu5, hu4, hu3, hu2]; norm_num [hu1, Nat.choose]
      · refine hcheck_k 400 (by norm_num) ?_ (by norm_num)
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        dsimp [coeff]; simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [hu8, hu7, hu6, hu5, hu4, hu3, hu2]; norm_num [hu1, Nat.choose]
      · refine hcheck_k 400 (by norm_num) ?_ (by norm_num)
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        dsimp [coeff]; simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [hu8, hu7, hu6, hu5, hu4, hu3, hu2]; norm_num [hu1, Nat.choose]
      · refine hcheck_k 400 (by norm_num) ?_ (by norm_num)
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        dsimp [coeff]; simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [hu8, hu7, hu6, hu5, hu4, hu3, hu2]; norm_num [hu1, Nat.choose]
      · refine hcheck_k 400 (by norm_num) ?_ (by norm_num)
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        dsimp [coeff]; simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [hu8, hu7, hu6, hu5, hu4, hu3, hu2]
    -- On frontier (closedBall wc r), ‖w - wc‖ = r, so ‖Q.eval w‖ ≥ 7/10 > 3/5 > ‖Q.eval wc‖!
    have hfront : ∀ w ∈ frontier (Metric.closedBall wc r), (7 / 10 : ℝ) ≤ ‖Q.eval w‖ := by
      intro w hw
      have hdist : ‖w - wc‖ = r := by
        rw [frontier_closedBall wc (by norm_num [r])] at hw
        simpa [Metric.mem_sphere, dist_eq_norm] using hw
      set h := w - wc
      have hw_eq : w = wc + h := by dsimp [h]; ring
      rw [hw_eq, hQ_taylor h]
      rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [pow_zero, mul_one, zero_add, pow_one]
      set tail3 := ∑ x ∈ Finset.range 6, coeff (x + 3) * h ^ (x + 3)
      have htail3_le : ‖tail3‖ ≤ 1 / 10 := by
        calc ‖tail3‖ ≤ ∑ x ∈ Finset.range 6, ‖coeff (x + 3) * h ^ (x + 3)‖ := norm_sum_le _ _
          _ = ∑ x ∈ Finset.range 6, ‖coeff (x + 3)‖ * r ^ (x + 3) := by
              apply Finset.sum_congr rfl; intro x _; rw [norm_mul, norm_pow, hdist]
          _ ≤ ∑ _x ∈ Finset.range 6, (1 / 60 : ℝ) :=
              Finset.sum_le_sum (fun x hx => hc_tail (x + 3) (Finset.mem_Ico.mpr ⟨by omega, by
                rw [Finset.mem_range] at hx; omega⟩))
          _ = 1 / 10 := by norm_num
      have hquad_le : ‖coeff 2 * h ^ 2‖ ≤ 1 / 10 := by
        rw [norm_mul, norm_pow, hdist]; exact hc2_ub
      have htri : ‖coeff 1 * h‖ - ‖(tail3 + coeff 2 * h ^ 2) + coeff 0‖ ≤
          ‖((tail3 + coeff 2 * h ^ 2) + coeff 1 * h) + coeff 0‖ := by
        have h1 : ((tail3 + coeff 2 * h ^ 2) + coeff 1 * h) + coeff 0 =
            coeff 1 * h - (-((tail3 + coeff 2 * h ^ 2) + coeff 0)) := by ring
        rw [h1]
        have h2 := norm_sub_norm_le (coeff 1 * h) (-((tail3 + coeff 2 * h ^ 2) + coeff 0))
        rwa [norm_neg] at h2
      have hlin : (75 : ℝ) * r < ‖coeff 1 * h‖ := by
        rw [norm_mul, hdist]; exact mul_lt_mul_of_pos_right hc1_lb (by norm_num [r])
      have hrem : ‖(tail3 + coeff 2 * h ^ 2) + coeff 0‖ ≤ ‖tail3‖ + ‖coeff 2 * h ^ 2‖ + ‖coeff 0‖ := by
        calc ‖(tail3 + coeff 2 * h ^ 2) + coeff 0‖
            ≤ ‖tail3 + coeff 2 * h ^ 2‖ + ‖coeff 0‖ := norm_add_le _ _
          _ ≤ (‖tail3‖ + ‖coeff 2 * h ^ 2‖) + ‖coeff 0‖ := by linarith [norm_add_le tail3 (coeff 2 * h ^ 2)]
      dsimp [r] at hlin
      linarith
    -- Apply Maximum Modulus Principle to f(w) = (Q.eval w)⁻¹ on closedBall wc r!
    set f : ℂ → ℂ := fun w => (Q.eval w)⁻¹
    have hf_diff : DiffContOnCl ℂ f (Metric.ball wc r) := by
      have hcl : closure (Metric.ball wc r) = Metric.closedBall wc r :=
        closure_ball wc (by norm_num [r])
      constructor
      · intro w hw
        have hwcl : w ∈ Metric.closedBall wc r := Metric.ball_subset_closedBall hw
        exact (Q.differentiableAt.inv (hno w hwcl)).differentiableWithinAt
      · rw [hcl]
        exact Q.continuous.continuousOn.inv₀ (fun w hw => hno w hw)
    have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hf_diff
      (C := 10 / 7) (fun w hw => by
        have hw' : w ∈ frontier (Metric.closedBall wc r) := by
          rw [frontier_closedBall wc (by norm_num [r])]
          rw [frontier_ball wc (by norm_num [r])] at hw
          exact hw
        have hQge := hfront w hw'
        dsimp [f]; rw [norm_inv]
        have h1 : (10 / 7 : ℝ) = (7 / 10 : ℝ)⁻¹ := by norm_num
        rw [h1]
        exact inv_anti₀ (by norm_num) hQge)
      (subset_closure (Metric.mem_ball_self (by norm_num [r])))
    -- At w = wc, ‖f wc‖ = ‖Q.eval wc‖⁻¹ > 5/3 > 10/7, contradiction!
    have hQwc_eq : Q.eval wc = coeff 0 := by
      have h := hQ_taylor 0
      rw [add_zero, Finset.sum_range_succ'] at h
      have hrest : ∑ x ∈ Finset.range 8, coeff (x + 1) * (0 : ℂ) ^ (x + 1) = 0 :=
        Finset.sum_eq_zero (fun x _ => by simp)
      rw [hrest, zero_add, pow_zero, mul_one] at h
      exact h
    dsimp [f] at hmax
    rw [hQwc_eq, norm_inv] at hmax
    have hc0_pos : 0 < ‖coeff 0‖ := norm_pos_iff.mpr (by rw [← hQwc_eq]; exact hno wc (Metric.mem_closedBall_self (by norm_num [r])))
    have hgt : (5 / 3 : ℝ) < ‖coeff 0‖⁻¹ := by
      rw [show (5 / 3 : ℝ) = (3 / 5 : ℝ)⁻¹ by norm_num]
      exact inv_strictAnti₀ hc0_pos hc0_ub
    linarith
  rcases hex_root with ⟨w₀, hw₀_ball, hw₀_root⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hw₀_ball
  have hw₀_lt1 : ‖w₀‖ < 1 := by
    have htri : ‖w₀‖ ≤ ‖wc‖ + ‖w₀ - wc‖ := by
      have := norm_add_le wc (w₀ - wc); simpa using this
    dsimp [r] at hw₀_ball
    linarith
  have hw₀_ne0 : w₀ ≠ 0 := by
    apply norm_pos_iff.mp
    have htri : ‖wc‖ - ‖w₀ - wc‖ ≤ ‖w₀‖ := by
      have := norm_sub_norm_le wc (wc - w₀)
      rw [sub_sub_cancel, norm_sub_rev wc w₀] at this; exact this
    dsimp [r] at hw₀_ball
    linarith
  have hRn : RnPoly 10 (1 - w₀) = 0 := by rwa [← hQ_eval w₀]
  refine ⟨w₀, hw₀_ne0, hw₀_lt1, hRn, ?_⟩
  set w : Fin 9 → ℂ := fun k => if k.val = 8 then (1 : ℂ) else w₀
  have hq := dualSmaleQuotient_at_one 10 (by omega) w (by simp [w])
  rw [hq]
  have hfun : (fun i : Fin 8 => w ⟨i.val, by omega⟩) = (fun _ => w₀) := by
    ext i; dsimp [w]; rw [if_neg (by omega)]
  rw [hfun]
  change GnPoly 10 w₀ = 0
  have hrel := GnPoly_eq_RnPoly (n := 10) (by omega) w₀
  rw [hRn] at hrel
  have h90 : ((10 : ℂ) * ((10 - 1 : ℕ) : ℂ)) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hrel).resolve_left h90

end DualSmaleMultiscale
