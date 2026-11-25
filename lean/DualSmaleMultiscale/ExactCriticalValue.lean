/-
  DualSmaleMultiscale/ExactCriticalValue.lean

  EXACT ALL-n RADIAL-INTEGRAL MASTER THEOREM & COROLLARIES:
  For EVERY degree n >= 2 and EVERY complex polynomial P(z) = z + a_2 z^2 + ... + a_n z^n
  with critical points zeta_1, ..., zeta_{n-1} (inverse critical points w_k = 1 / zeta_k)
  and r_1 = min_k |zeta_k| > 0:

  1. `exact_radial_integral_critical_value`:
       ∃ j, ∫_0^{r_1} ∏_k (1 - |w_k| r) dr ≤ |P(zeta_j)|.
  2. `exact_harmonic_critical_value`:
       ∃ j, 1 / (1/r_1 + ∑_k |w_k|) ≤ |P(zeta_j)|.
  3. `exact_rmin_div_n_critical_value`:
       ∃ j, r_1 / n ≤ |P(zeta_j)|  (sharp constant 1/n, upgrading 49/(50 n)).
  4. `exact_equal_modulus_dual_smale`:
       |zeta_1| = ... = |zeta_{n-1}| = R => ∃ j, 1/n ≤ |P(zeta_j)/zeta_j|.
  5. `equal_modulus_quantitative_stability` & `equal_modulus_strict_uniqueness`:
       |zeta_1| = ... = |zeta_{n-1}| = R =>
         ∃ j, 1/n + ‖u_i - u_j‖^2 / (16 n (n - 1)) ≤ |P(zeta_j)/zeta_j|  (u_k = R / zeta_k),
       hence equality max_j |P(zeta_j)/zeta_j| = 1/n holds IFF all critical points coincide!
  6. `exact_bounded_spread_dual_smale`:
       r_1 ≤ |zeta_k| ≤ κ * r_1 => ∃ j, 1 / (κ * n) ≤ |P(zeta_j)/zeta_j|.
  7. `exact_closest_crit_dichotomy`:
       Either |P(zeta_1)/zeta_1| ≥ 1/n, or |P(zeta_1)| < 1/(1/r_1 + ∑ |w_k|) while
       some critical point achieves |P(zeta_j)| ≥ 1/(1/r_1 + ∑ |w_k|).
-/

import DualSmaleMultiscale.PolynomialReduction
import DualSmaleMultiscale.RadialLift
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped BigOperators
open Polynomial Complex DualSmale

namespace DualSmaleMultiscale

/-! ### Section 1: Relating `polyFromInvCrits` to `RadialLift` hypotheses -/

/-- Elementary product monotonicity on `ℝ` for nonnegative factors. -/
lemma finset_prod_le_prod_real {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hfga : f a ≤ g a := hfg a (Finset.mem_insert_self a s)
    have hfs : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hih := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul hfga hih hfs (le_trans hfa hfga)

/-- Top elementary symmetric polynomial equals the product of all entries. -/
lemma elemSym_top : ∀ (m : ℕ) (w : Fin m → ℂ), elemSym m w m = ∏ k : Fin m, w k
  | 0, _ => by simp [elemSym]
  | m + 1, w => by
    rw [Fin.prod_univ_castSucc]
    simp only [elemSym]
    rw [elemSym_eq_zero_of_lt m _ (m + 1) (by omega), zero_add, elemSym_top m]
    ring

/-- Degree of `polyFromInvCrits n w` is `n` whenever all `w_k ≠ 0` and `n ≥ 1`. -/
lemma natDegree_polyFromInvCrits {n : ℕ} (hn : 1 ≤ n) (w : Fin (n - 1) → ℂ)
    (hw : ∀ k, w k ≠ 0) :
    (polyFromInvCrits n w).natDegree = n := by
  have hle : (polyFromInvCrits n w).natDegree ≤ n := by
    unfold polyFromInvCrits
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le n, fun m hm => ?_⟩
    rw [Finset.mem_range] at hm
    refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) (by omega)
  have hcoeff : (polyFromInvCrits n w).coeff n ≠ 0 := by
    unfold polyFromInvCrits
    change (Polynomial.lcoeff ℂ n) _ ≠ 0
    rw [map_sum]
    have hmem : n - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single (n - 1)]
    · rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow, if_pos (by omega)]
      rw [elemSym_top (n - 1) w]
      have hprod_ne : (∏ k : Fin (n - 1), w k) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hw k)
      have hsign_ne : (-1 : ℂ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hden_ne : ((n - 1 + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      exact mul_ne_zero (div_ne_zero hsign_ne hden_ne) hprod_ne
    · intro m hm hne
      rw [Finset.mem_range] at hm
      rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
    · intro hnot; exact absurd hmem hnot
  exact le_antisymm hle (Polynomial.le_natDegree_of_ne_zero hcoeff)

/-- Derivative evaluation formula: `P'(z) = ∏_k (1 - w_k z)`. -/
lemma derivative_polyFromInvCrits_eval_prod {n : ℕ} (hn : 1 ≤ n) (w : Fin (n - 1) → ℂ) (z : ℂ) :
    (derivative (polyFromInvCrits n w)).eval z = ∏ k : Fin (n - 1), (1 - w k * z) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [derivative_polyFromInvCrits]
  change (Polynomial.evalRingHom z) _ = _
  rw [map_sum]
  have heval : ∑ k ∈ Finset.range (m + 1),
      (Polynomial.evalRingHom z) (C ((-1 : ℂ) ^ k * elemSym (m + 1 - 1) w k) * X ^ k) =
      ∑ k ∈ Finset.range (m + 1), (-1 : ℂ) ^ k * elemSym m w k * z ^ k := by
    apply Finset.sum_congr rfl; intro k _; simp
  rw [heval]
  exact (prod_one_sub_eq_sum_elemSym m w z).symm

/-- Every root `ζ` of `derivative (polyFromInvCrits n w)` equals `(w j)⁻¹` for some `j`. -/
lemma crit_point_eq_inv_w {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (hw : ∀ k, w k ≠ 0) {ζ : ℂ} (hζ : (derivative (polyFromInvCrits n w)).eval ζ = 0) :
    ∃ j : Fin (n - 1), ζ = (w j)⁻¹ := by
  rw [derivative_polyFromInvCrits_eval_prod (by omega) w ζ, Finset.prod_eq_zero_iff] at hζ
  rcases hζ with ⟨j, _, hj⟩
  refine ⟨j, ?_⟩
  have h1 : w j * ζ = 1 := by linear_combination -hj
  exact eq_inv_of_mul_eq_one_right h1

/-- Lower bound `∏_k (1 - ‖w k‖ * ‖z‖) ≤ ‖P'(z)‖` whenever `‖w k‖ * ‖z‖ ≤ 1` for all `k`. -/
lemma norm_derivative_polyFromInvCrits_ge_prod {n : ℕ} (hn : 1 ≤ n) (w : Fin (n - 1) → ℂ)
    {z : ℂ} (hball : ∀ k, ‖w k‖ * ‖z‖ ≤ 1) :
    ∏ k : Fin (n - 1), (1 - ‖w k‖ * ‖z‖) ≤ ‖(derivative (polyFromInvCrits n w)).eval z‖ := by
  rw [derivative_polyFromInvCrits_eval_prod hn w z, norm_prod]
  apply finset_prod_le_prod_real
  · intro k _; linarith [hball k]
  · intro k _
    have h1 := norm_sub_norm_le (1 : ℂ) (w k * z)
    rw [norm_one, norm_mul] at h1
    exact h1

/-- Exact identity `P((w j)⁻¹) / (w j)⁻¹ = dualSmaleQuotient n w j`. -/
lemma polyFromInvCrits_div_eq_quotient {n : ℕ} (hn : 1 ≤ n) (w : Fin (n - 1) → ℂ)
    (j : Fin (n - 1)) (hwj : w j ≠ 0) :
    (polyFromInvCrits n w).eval (w j)⁻¹ / (w j)⁻¹ = dualSmaleQuotient n w j := by
  unfold polyFromInvCrits dualSmaleQuotient
  have heval : (∑ m ∈ Finset.range n,
      C (((-1 : ℂ) ^ m / ((m + 1 : ℕ) : ℂ)) * elemSym (n - 1) w m) * X ^ (m + 1)).eval (w j)⁻¹ =
      ∑ m ∈ Finset.range n,
        (((-1 : ℂ) ^ m / ((m + 1 : ℕ) : ℂ)) * elemSym (n - 1) w m) * ((w j)⁻¹) ^ (m + 1) := by
    change (Polynomial.evalRingHom (w j)⁻¹) _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl; intro m _; simp
  rw [heval, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  have hsc : elemSym (n - 1) (fun k => w k / w j) m = elemSym (n - 1) w m * ((w j)⁻¹) ^ m := by
    have hfun : (fun k => w k / w j) = (fun k => w k * (w j)⁻¹) := by ext k; ring
    rw [hfun, elemSym_mul_scale]
  rw [hsc, pow_succ, ← mul_assoc, mul_div_cancel_right₀ _ (inv_ne_zero hwj)]
  ring

/-! ### Section 2: Exact Radial-Integral Master Theorem -/

/-- **THEOREM 1 (Exact Radial-Integral Critical Value Theorem — All `n ≥ 2`)**:
    For every `n ≥ 2` and every `P = polyFromInvCrits n w` with `0 < r₁` and
    `∀ k, w k ≠ 0 ∧ ‖w k‖ ≤ 1 / r₁` (equivalently `r₁ ≤ ‖ζ k‖` for all critical points `ζ k = (w k)⁻¹`),
    there exists a critical point `ζ_j = (w j)⁻¹` such that
    `∫ r in 0..r₁, ∏ k, (1 - ‖w k‖ * r) ≤ ‖P(ζ_j)‖`. -/
theorem exact_radial_integral_critical_value {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (hw : ∀ k, w k ≠ 0) {r₁ : ℝ} (hr₁ : 0 < r₁) (hr₁_le : ∀ k, ‖w k‖ ≤ 1 / r₁) :
    ∃ j : Fin (n - 1),
      (∫ r in (0 : ℝ)..r₁, ∏ k : Fin (n - 1), (1 - ‖w k‖ * r)) ≤
        ‖(polyFromInvCrits n w).eval (w j)⁻¹‖ := by
  set P := polyFromInvCrits n w
  set φ : ℝ → ℝ := fun r => ∏ k : Fin (n - 1), (1 - ‖w k‖ * r)
  set Φ : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, φ r
  have hφ_cont : Continuous φ := by dsimp [φ]; fun_prop
  have hΦ0 : Φ 0 = 0 := intervalIntegral.integral_same
  have hΦ_deriv : ∀ r ∈ Set.Ico (0 : ℝ) r₁, HasDerivAt Φ (φ r) r := fun r _ =>
    intervalIntegral.integral_hasDerivAt_right (hφ_cont.intervalIntegrable 0 r)
      (hφ_cont.stronglyMeasurableAtFilter _ _) hφ_cont.continuousAt
  have hΦ_cont : ContinuousOn Φ (Set.Icc 0 r₁) :=
    (intervalIntegral.continuous_primitive (fun a b => hφ_cont.intervalIntegrable a b) 0).continuousOn
  have hφ_pos : ∀ r ∈ Set.Ico (0 : ℝ) r₁, 0 < φ r := by
    intro r hr
    apply Finset.prod_pos
    intro k _
    have hk : ‖w k‖ * r < 1 := by
      calc ‖w k‖ * r ≤ (1 / r₁) * r := mul_le_mul_of_nonneg_right (hr₁_le k) hr.1
        _ = r / r₁ := by ring
        _ < 1 := (div_lt_one hr₁).mpr hr.2
    linarith
  have hP'_lb : ∀ z : ℂ, ‖z‖ < r₁ → φ ‖z‖ ≤ ‖(derivative P).eval z‖ := by
    intro z hz
    apply norm_derivative_polyFromInvCrits_ge_prod (by omega) w
    intro k
    calc ‖w k‖ * ‖z‖ ≤ (1 / r₁) * r₁ :=
          mul_le_mul (hr₁_le k) (le_of_lt hz) (norm_nonneg z) (by positivity)
      _ = 1 := one_div_mul_cancel (ne_of_gt hr₁)
  have hdeg : 2 ≤ P.natDegree := by rw [natDegree_polyFromInvCrits (by omega) w hw]; exact hn
  obtain ⟨ζ, hζ0, hζv⟩ := radial_lift_critical_value_ge P hdeg (polyFromInvCrits_eval_zero n w)
    (derivative_polyFromInvCrits_eval_zero (by omega) w) hr₁ hΦ0 hΦ_cont hΦ_deriv hφ_pos hP'_lb
  obtain ⟨j, rfl⟩ := crit_point_eq_inv_w hn w hw hζ0
  exact ⟨j, hζv⟩

/-! ### Section 3: Exact Harmonic-Mean Master Inequality `1 / (1/r₁ + ∑ ‖w k‖)` -/

/-- Concavity of `log(1 - t)`: for `0 ≤ t < 1` and `0 ≤ u ≤ 1`, `(1 - t) ^ u ≤ 1 - u * t`. -/
lemma one_sub_rpow_le_one_sub_mul {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - t) ^ u ≤ 1 - u * t := by
  have h1t : 0 < 1 - t := by linarith
  have h1ut : 0 < 1 - u * t := by nlinarith
  -- Show h(s) = log(1 - u * s) - u * log(1 - s) is monotone on [0, t]
  set h : ℝ → ℝ := fun s => Real.log (1 - u * s) - u * Real.log (1 - s)
  have hderiv : ∀ s ∈ Set.Icc 0 t,
      HasDerivAt h ((-u) / (1 - u * s) - u * ((-1) / (1 - s))) s := by
    intro s hs
    have hs1 : 0 < 1 - s := by linarith [hs.2, ht1]
    have hsu : 0 < 1 - u * s := by
      have : u * s ≤ s := mul_le_of_le_one_left hs.1 hu1
      linarith [hs.2, ht1]
    have h1 : HasDerivAt (fun x : ℝ => 1 - u * x) (-u) s := by
      simpa using ((hasDerivAt_id s).const_mul u).const_sub (1 : ℝ)
    have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (1 : ℝ)
    exact (h1.log (ne_of_gt hsu)).sub ((h2.log (ne_of_gt hs1)).const_mul u)
  have hcont : ContinuousOn h (Set.Icc 0 t) := fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
  have hmono : MonotoneOn h (Set.Icc 0 t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) hcont
    · intro s hs; exact (hderiv s (interior_subset hs)).hasDerivWithinAt
    · intro s hs
      have hsm : s ∈ Set.Icc 0 t := interior_subset hs
      have hs1 : 0 < 1 - s := by linarith [hsm.2, ht1]
      have hsu : 0 < 1 - u * s := by
        have : u * s ≤ s := mul_le_of_le_one_left hsm.1 hu1
        linarith [hsm.2, ht1]
      have hnum : 0 ≤ u * (1 - u) * s := mul_nonneg (mul_nonneg hu0 (by linarith)) hsm.1
      have hEq : (-u) / (1 - u * s) - u * ((-1) / (1 - s)) =
          u * (1 - u) * s / ((1 - u * s) * (1 - s)) := by
        field_simp [ne_of_gt hsu, ne_of_gt hs1]; ring
      rw [hEq]
      exact div_nonneg hnum (mul_nonneg (le_of_lt hsu) (le_of_lt hs1))
  have hge := hmono ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
  have hh0 : h 0 = 0 := by simp [h]
  rw [hh0] at hge
  dsimp [h] at hge
  rw [Real.rpow_def_of_pos h1t]
  have hlog : Real.log (1 - t) * u ≤ Real.log (1 - u * t) := by linarith
  calc Real.exp (Real.log (1 - t) * u) ≤ Real.exp (Real.log (1 - u * t)) := Real.exp_le_exp.mpr hlog
    _ = 1 - u * t := Real.exp_log h1ut

/-- Product lower bound `(1 - r / r₁) ^ (r₁ * ∑ ‖w k‖) ≤ ∏ (1 - ‖w k‖ * r)` for `0 ≤ r < r₁`. -/
lemma prod_one_sub_ge_rpow {m : ℕ} (w : Fin m → ℂ) {r₁ r : ℝ}
    (hr₁ : 0 < r₁) (hw_le : ∀ k, ‖w k‖ ≤ 1 / r₁) (hr0 : 0 ≤ r) (hr1 : r < r₁) :
    (1 - r / r₁) ^ (r₁ * ∑ k : Fin m, ‖w k‖) ≤ ∏ k : Fin m, (1 - ‖w k‖ * r) := by
  have ht0 : 0 ≤ r / r₁ := div_nonneg hr0 (le_of_lt hr₁)
  have ht1 : r / r₁ < 1 := (div_lt_one hr₁).mpr hr1
  have h1t : 0 < 1 - r / r₁ := by linarith
  rw [Finset.mul_sum, Real.rpow_sum_of_pos h1t]
  apply finset_prod_le_prod_real
  · intro k _; exact Real.rpow_nonneg (le_of_lt h1t) _
  · intro k _
    have hu0 : 0 ≤ r₁ * ‖w k‖ := mul_nonneg (le_of_lt hr₁) (norm_nonneg _)
    have hu1 : r₁ * ‖w k‖ ≤ 1 := by
      calc r₁ * ‖w k‖ ≤ r₁ * (1 / r₁) := mul_le_mul_of_nonneg_left (hw_le k) (le_of_lt hr₁)
        _ = 1 := mul_one_div_cancel (ne_of_gt hr₁)
    have h := one_sub_rpow_le_one_sub_mul ht0 ht1 hu0 hu1
    have heq : r₁ * ‖w k‖ * (r / r₁) = ‖w k‖ * r := by field_simp [ne_of_gt hr₁]
    rwa [heq] at h

/-- Closed-form radial comparison function `Φ_K(r) = (r₁ / (K + 1)) * (1 - (1 - r / r₁)^(K + 1))`:
    its value at `0` is `0`, its derivative on `[0, r₁)` is `(1 - r / r₁)^K > 0`, and its value at
    `r₁` is `r₁ / (K + 1)`. -/
lemma rpow_antideriv_props {r₁ K : ℝ} (hr₁ : 0 < r₁) (hK : 0 ≤ K) :
    let Φ : ℝ → ℝ := fun r => (r₁ / (K + 1)) * (1 - (1 - r / r₁) ^ (K + 1))
    let φ : ℝ → ℝ := fun r => (1 - r / r₁) ^ K
    Φ 0 = 0 ∧
    Φ r₁ = r₁ / (K + 1) ∧
    ContinuousOn Φ (Set.Icc 0 r₁) ∧
    (∀ r ∈ Set.Ico 0 r₁, HasDerivAt Φ (φ r) r) ∧
    (∀ r ∈ Set.Ico 0 r₁, 0 < φ r) := by
  intro Φ φ
  have hK1 : 0 < K + 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [Φ]; simp [Real.one_rpow]
  · dsimp [Φ]; rw [div_self (ne_of_gt hr₁), sub_self, Real.zero_rpow (ne_of_gt hK1)]; ring
  · dsimp [Φ]
    have hcont_inner : ContinuousOn (fun r : ℝ => 1 - r / r₁) (Set.Icc 0 r₁) :=
      (continuous_const.sub (continuous_id.div_const r₁)).continuousOn
    have hcont_rpow : ContinuousOn (fun r : ℝ => (1 - r / r₁) ^ (K + 1)) (Set.Icc 0 r₁) :=
      ContinuousOn.rpow_const hcont_inner (fun r _ => Or.inr (le_of_lt hK1))
    exact continuousOn_const.mul (continuousOn_const.sub hcont_rpow)
  · intro r hr
    have h1t : 0 < 1 - r / r₁ := by have := (div_lt_one hr₁).mpr hr.2; linarith
    have hinner : HasDerivAt (fun x : ℝ => 1 - x / r₁) (- (1 / r₁)) r := by
      have h1 : HasDerivAt (fun x : ℝ => x / r₁) (1 / r₁) r := by
        simpa using (hasDerivAt_id r).div_const r₁
      have h2 := (hasDerivAt_const r (1 : ℝ)).sub h1
      convert h2 using 1; ring
    have hrp : HasDerivAt (fun x : ℝ => (1 - x / r₁) ^ (K + 1))
        ((- (1 / r₁)) * (K + 1) * (1 - r / r₁) ^ ((K + 1) - 1)) r :=
      HasDerivAt.rpow_const hinner (Or.inl (ne_of_gt h1t))
    have hfull := ((hasDerivAt_const r (1 : ℝ)).sub hrp).const_mul (r₁ / (K + 1))
    convert hfull using 1
    dsimp [φ]
    rw [show (K + 1) - 1 = K by ring]
    field_simp [ne_of_gt hr₁, ne_of_gt hK1]
    ring
  · intro r hr
    have h1t : 0 < 1 - r / r₁ := by have := (div_lt_one hr₁).mpr hr.2; linarith
    exact Real.rpow_pos_of_pos h1t K

/-- **THEOREM 2 (Exact Harmonic-Mean Critical Value Theorem — All `n ≥ 2`)**:
    For EVERY `n ≥ 2` and EVERY `P = polyFromInvCrits n w` with `∀ k, w k ≠ 0 ∧ ‖w k‖ ≤ 1 / r₁`:
    `∃ j, 1 / (1 / r₁ + ∑ k, ‖w k‖) ≤ ‖P(ζ_j)‖`. -/
theorem exact_harmonic_critical_value {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (hw : ∀ k, w k ≠ 0) {r₁ : ℝ} (hr₁ : 0 < r₁) (hr₁_le : ∀ k, ‖w k‖ ≤ 1 / r₁) :
    ∃ j : Fin (n - 1),
      1 / (1 / r₁ + ∑ k : Fin (n - 1), ‖w k‖) ≤ ‖(polyFromInvCrits n w).eval (w j)⁻¹‖ := by
  set P := polyFromInvCrits n w
  set K : ℝ := r₁ * ∑ k : Fin (n - 1), ‖w k‖
  have hK : 0 ≤ K := mul_nonneg (le_of_lt hr₁) (Finset.sum_nonneg (fun k _ => norm_nonneg _))
  obtain ⟨hΦ0, hΦr₁, hΦ_cont, hΦ_deriv, hφ_pos⟩ := rpow_antideriv_props hr₁ hK
  have hP'_lb : ∀ z : ℂ, ‖z‖ < r₁ → (1 - ‖z‖ / r₁) ^ K ≤ ‖(derivative P).eval z‖ := by
    intro z hz
    calc (1 - ‖z‖ / r₁) ^ K
        ≤ ∏ k : Fin (n - 1), (1 - ‖w k‖ * ‖z‖) :=
          prod_one_sub_ge_rpow w hr₁ hr₁_le (norm_nonneg z) hz
      _ ≤ ‖(derivative P).eval z‖ := by
          apply norm_derivative_polyFromInvCrits_ge_prod (by omega) w
          intro k
          calc ‖w k‖ * ‖z‖ ≤ (1 / r₁) * r₁ :=
                mul_le_mul (hr₁_le k) (le_of_lt hz) (norm_nonneg z) (by positivity)
            _ = 1 := one_div_mul_cancel (ne_of_gt hr₁)
  have hdeg : 2 ≤ P.natDegree := by rw [natDegree_polyFromInvCrits (by omega) w hw]; exact hn
  obtain ⟨ζ, hζ0, hζv⟩ := radial_lift_critical_value_ge P hdeg (polyFromInvCrits_eval_zero n w)
    (derivative_polyFromInvCrits_eval_zero (by omega) w) hr₁ hΦ0 hΦ_cont hΦ_deriv hφ_pos hP'_lb
  obtain ⟨j, rfl⟩ := crit_point_eq_inv_w hn w hw hζ0
  refine ⟨j, ?_⟩
  change (fun r => r₁ / (K + 1) * (1 - (1 - r / r₁) ^ (K + 1))) r₁ ≤ _ at hζv
  rw [hΦr₁] at hζv
  have hEq : r₁ / (K + 1) = 1 / (1 / r₁ + ∑ k : Fin (n - 1), ‖w k‖) := by
    dsimp [K]
    have hden : 1 / r₁ + ∑ k : Fin (n - 1), ‖w k‖ ≠ 0 := by
      have : 0 ≤ ∑ k : Fin (n - 1), ‖w k‖ := Finset.sum_nonneg (fun k _ => norm_nonneg _)
      positivity
    field_simp [ne_of_gt hr₁, hden]
    ring
  rwa [hEq] at hζv

/-- **COROLLARY 2.1 (Sharp `r₁ / n` Critical Value Bound — All `n ≥ 2`)**:
    Upgrades `49 / (50 * n) * r₁` to the **exact sharp constant `r₁ / n`**! -/
theorem exact_rmin_div_n_critical_value {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (hw : ∀ k, w k ≠ 0) {r₁ : ℝ} (hr₁ : 0 < r₁) (hr₁_le : ∀ k, ‖w k‖ ≤ 1 / r₁) :
    ∃ j : Fin (n - 1), r₁ / (n : ℝ) ≤ ‖(polyFromInvCrits n w).eval (w j)⁻¹‖ := by
  obtain ⟨j, hj⟩ := exact_harmonic_critical_value hn w hw hr₁ hr₁_le
  refine ⟨j, le_trans ?_ hj⟩
  have hsum : ∑ k : Fin (n - 1), ‖w k‖ ≤ ((n - 1 : ℕ) : ℝ) / r₁ := by
    calc ∑ k : Fin (n - 1), ‖w k‖ ≤ ∑ _k : Fin (n - 1), (1 / r₁) :=
          Finset.sum_le_sum (fun k _ => hr₁_le k)
      _ = ((n - 1 : ℕ) : ℝ) * (1 / r₁) := by simp
      _ = ((n - 1 : ℕ) : ℝ) / r₁ := by ring
  have htot : 1 / r₁ + ∑ k : Fin (n - 1), ‖w k‖ ≤ (n : ℝ) / r₁ := by
    have hnat : (1 : ℝ) + ((n - 1 : ℕ) : ℝ) = (n : ℝ) := by
      have : 1 + (n - 1) = n := by omega
      exact_mod_cast this
    calc 1 / r₁ + ∑ k : Fin (n - 1), ‖w k‖
        ≤ 1 / r₁ + ((n - 1 : ℕ) : ℝ) / r₁ := by linarith
      _ = (1 + ((n - 1 : ℕ) : ℝ)) / r₁ := by ring
      _ = (n : ℝ) / r₁ := by rw [hnat]
  have hpos : 0 < 1 / r₁ + ∑ k : Fin (n - 1), ‖w k‖ := by
    have : 0 ≤ ∑ k : Fin (n - 1), ‖w k‖ := Finset.sum_nonneg (fun k _ => norm_nonneg _)
    positivity
  have h1 : r₁ / (n : ℝ) = 1 / ((n : ℝ) / r₁) := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hn0, ne_of_gt hr₁]
  rw [h1]
  exact one_div_le_one_div_of_le hpos htot

/-- **COROLLARY 2.2 (Exact `1 / (2 S₀)` Harmonic-Mean Bound — All `n ≥ 2`)**:
    If `r₁ = min_k ‖ζ k‖` is attained at some `j₀` (`‖w j₀‖ = 1 / r₁`), then
    `∃ j, 1 / (2 * ∑ k, ‖w k‖) ≤ ‖P(ζ_j)‖`. -/
theorem exact_harmonic_mean_half {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (hw : ∀ k, w k ≠ 0) {r₁ : ℝ} (hr₁ : 0 < r₁) (hr₁_le : ∀ k, ‖w k‖ ≤ 1 / r₁)
    (j₀ : Fin (n - 1)) (hj₀ : ‖w j₀‖ = 1 / r₁) :
    ∃ j : Fin (n - 1),
      1 / (2 * ∑ k : Fin (n - 1), ‖w k‖) ≤ ‖(polyFromInvCrits n w).eval (w j)⁻¹‖ := by
  obtain ⟨j, hj⟩ := exact_harmonic_critical_value hn w hw hr₁ hr₁_le
  refine ⟨j, le_trans ?_ hj⟩
  have hle_sum : 1 / r₁ ≤ ∑ k : Fin (n - 1), ‖w k‖ := by
    rw [← hj₀]
    exact Finset.single_le_sum (fun k _ => norm_nonneg (w k)) (Finset.mem_univ j₀)
  have hpos : 0 < 1 / r₁ + ∑ k : Fin (n - 1), ‖w k‖ := by positivity
  exact one_div_le_one_div_of_le hpos (by linarith)

/-- **COROLLARY 2.3 (Exact Bounded-Spread Dual Smale Bound — All `n ≥ 2`)**:
    If `r₁ ≤ ‖ζ_k‖ ≤ κ * r₁` for all `k` (equivalently `1 / (κ * r₁) ≤ ‖w k‖ ≤ 1 / r₁`), then
    `∃ j, 1 / (κ * n) ≤ ‖dualSmaleQuotient n w j‖`. -/
theorem exact_bounded_spread_dual_smale {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    {r₁ κ : ℝ} (hr₁ : 0 < r₁) (hκ : 0 < κ)
    (hlo : ∀ k, 1 / (κ * r₁) ≤ ‖w k‖) (hhi : ∀ k, ‖w k‖ ≤ 1 / r₁) :
    ∃ j : Fin (n - 1), 1 / (κ * (n : ℝ)) ≤ ‖dualSmaleQuotient n w j‖ := by
  have hw : ∀ k, w k ≠ 0 := fun k => norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hlo k))
  obtain ⟨j, hj⟩ := exact_rmin_div_n_critical_value hn w hw hr₁ hhi
  refine ⟨j, ?_⟩
  rw [← polyFromInvCrits_div_eq_quotient (by omega) w j (hw j), norm_div, norm_inv]
  have h1 : 1 / (κ * r₁) ≤ ‖w j‖ := hlo j
  have hinv_le : ‖w j‖⁻¹ ≤ κ * r₁ := by
    have hpos : 0 < 1 / (κ * r₁) := by positivity
    calc ‖w j‖⁻¹ ≤ (1 / (κ * r₁))⁻¹ := inv_anti₀ hpos h1
      _ = κ * r₁ := by simp
  have hpos_j : 0 < ‖w j‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (hw j))
  calc 1 / (κ * (n : ℝ))
      = (r₁ / (n : ℝ)) / (κ * r₁) := by
        have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp [hn0, ne_of_gt hr₁, ne_of_gt hκ]
    _ ≤ ‖(polyFromInvCrits n w).eval (w j)⁻¹‖ / ‖w j‖⁻¹ :=
        div_le_div₀ (norm_nonneg _) hj hpos_j hinv_le

/-- **COROLLARY 2.4 (Exact `1 / n` Closest-Critical-Point Dichotomy — All `n ≥ 2`)**:
    Let `j₀` attain the minimum critical-point modulus `r₁ = ‖ζ_{j₀}‖ = min_k ‖ζ_k‖`.
    Then EITHER the closest critical point itself satisfies the **exact Dual Smale Conjecture**
    `1 / n ≤ ‖dualSmaleQuotient n w j₀‖`, OR `‖P(ζ_{j₀})‖ < 1 / (1/r₁ + ∑ ‖w k‖)` while
    another critical point `ζ_j` achieves `1 / (1/r₁ + ∑ ‖w k‖) ≤ ‖P(ζ_j)‖`. -/
theorem exact_closest_crit_dichotomy {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (hw : ∀ k, w k ≠ 0) (j₀ : Fin (n - 1)) (hmax : ∀ k, ‖w k‖ ≤ ‖w j₀‖) :
    (1 / (n : ℝ) ≤ ‖dualSmaleQuotient n w j₀‖) ∨
    (‖(polyFromInvCrits n w).eval (w j₀)⁻¹‖ < 1 / (‖w j₀‖ + ∑ k : Fin (n - 1), ‖w k‖) ∧
     ∃ j : Fin (n - 1), 1 / (‖w j₀‖ + ∑ k : Fin (n - 1), ‖w k‖) ≤ ‖(polyFromInvCrits n w).eval (w j)⁻¹‖) := by
  have hwj₀_pos : 0 < ‖w j₀‖ := norm_pos_iff.mpr (hw j₀)
  set r₁ : ℝ := (‖w j₀‖)⁻¹
  have hr₁ : 0 < r₁ := inv_pos.mpr hwj₀_pos
  have hr₁_inv : 1 / r₁ = ‖w j₀‖ := by dsimp [r₁]; simp
  have hr₁_le : ∀ k, ‖w k‖ ≤ 1 / r₁ := fun k => by rw [hr₁_inv]; exact hmax k
  set L_low : ℝ := 1 / (‖w j₀‖ + ∑ k : Fin (n - 1), ‖w k‖)
  by_cases hge : L_low ≤ ‖(polyFromInvCrits n w).eval (w j₀)⁻¹‖
  · left
    rw [← polyFromInvCrits_div_eq_quotient (by omega) w j₀ (hw j₀), norm_div, norm_inv]
    have hsum : ∑ k : Fin (n - 1), ‖w k‖ ≤ ((n - 1 : ℕ) : ℝ) * ‖w j₀‖ := by
      calc ∑ k : Fin (n - 1), ‖w k‖ ≤ ∑ _k : Fin (n - 1), ‖w j₀‖ := Finset.sum_le_sum (fun k _ => hmax k)
        _ = ((n - 1 : ℕ) : ℝ) * ‖w j₀‖ := by simp
    have hnat : (1 : ℝ) + ((n - 1 : ℕ) : ℝ) = (n : ℝ) := by
      have : 1 + (n - 1) = n := by omega
      exact_mod_cast this
    have hden_le : ‖w j₀‖ + ∑ k : Fin (n - 1), ‖w k‖ ≤ (n : ℝ) * ‖w j₀‖ := by
      calc ‖w j₀‖ + ∑ k : Fin (n - 1), ‖w k‖ ≤ ‖w j₀‖ + ((n - 1 : ℕ) : ℝ) * ‖w j₀‖ := by linarith
        _ = (1 + ((n - 1 : ℕ) : ℝ)) * ‖w j₀‖ := by ring
        _ = (n : ℝ) * ‖w j₀‖ := by rw [hnat]
    have hL_ge : 1 / ((n : ℝ) * ‖w j₀‖) ≤ L_low :=
      one_div_le_one_div_of_le (by positivity) hden_le
    have hP_ge : 1 / ((n : ℝ) * ‖w j₀‖) ≤ ‖(polyFromInvCrits n w).eval (w j₀)⁻¹‖ := le_trans hL_ge hge
    rw [div_inv_eq_mul]
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    calc 1 / (n : ℝ) = (1 / ((n : ℝ) * ‖w j₀‖)) * ‖w j₀‖ := by field_simp [ne_of_gt hn_pos, ne_of_gt hwj₀_pos]
      _ ≤ ‖(polyFromInvCrits n w).eval (w j₀)⁻¹‖ * ‖w j₀‖ :=
          mul_le_mul_of_nonneg_right hP_ge (le_of_lt hwj₀_pos)
  · right
    push Not at hge
    obtain ⟨j, hj⟩ := exact_harmonic_critical_value hn w hw hr₁ hr₁_le
    rw [hr₁_inv] at hj
    exact ⟨hge, j, hj⟩

/-! ### Section 4: Exact Equal-Modulus Dual Smale + Quantitative Stability + Strict Uniqueness -/

/-- Pure-algebraic two-factor stability lower bound on the unit circle:
    if `‖u‖ = 1`, `‖v‖ = 1`, and `c = 1 - ‖u + v‖ / 2`, then for ALL `z` with `‖z‖ ≤ 1`:
    `(1 - ‖z‖)^2 + (c / 2) * ‖z‖ * (1 - ‖z‖) ≤ ‖1 - u * z‖ * ‖1 - v * z‖`. -/
lemma two_unit_factor_stability {u v z : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hz : ‖z‖ ≤ 1) :
    let c := 1 - ‖u + v‖ / 2
    (1 - ‖z‖) ^ 2 + (c / 2) * ‖z‖ * (1 - ‖z‖) ≤ ‖1 - u * z‖ * ‖1 - v * z‖ := by
  intro c
  set r := ‖z‖
  have hr0 : 0 ≤ r := norm_nonneg z
  have hr1 : 0 ≤ 1 - r := by linarith
  have hc0 : 0 ≤ c := by
    have htri : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
    dsimp [c]; linarith
  have hc1 : c ≤ 1 := by dsimp [c]; linarith [norm_nonneg (u + v)]
  -- By Re((u + v) * z) ≤ ‖u + v‖ * r = 2 * (1 - c) * r, either Re(u * z) ≤ (1 - c) * r or Re(v * z) ≤ (1 - c) * r!
  have hsum_re : (u * z).re + (v * z).re ≤ 2 * (1 - c) * r := by
    have h1 : (u * z).re + (v * z).re = ((u + v) * z).re := by simp [add_mul]
    rw [h1]
    have h2 : ((u + v) * z).re ≤ ‖(u + v) * z‖ := Complex.re_le_norm _
    rw [norm_mul] at h2
    have h2c : 2 * (1 - c) = ‖u + v‖ := by dsimp [c]; ring
    rw [h2c]
    exact h2
  -- Helper: if ‖w‖ = 1 and (w * z).re ≤ (1 - c) * r, then (1 - r) + (c / 2) * r ≤ ‖1 - w * z‖!
  have hsingle : ∀ w : ℂ, ‖w‖ = 1 → (w * z).re ≤ (1 - c) * r →
      (1 - r) + (c / 2) * r ≤ ‖1 - w * z‖ := by
    intro w hw hre
    have hns : ‖1 - w * z‖ ^ 2 = 1 - 2 * (w * z).re + r ^ 2 := by
      have h1 : ‖w * z‖ ^ 2 = r ^ 2 := by rw [norm_mul, hw, one_mul]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have h2 : (w * z).re ^ 2 + (w * z).im ^ 2 = r ^ 2 := by
        rw [← h1, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      nlinarith
    have hc1 : c ≤ 1 := by dsimp [c]; linarith [norm_nonneg (u + v)]
    have hsq_le : ((1 - r) + (c / 2) * r) ^ 2 ≤ ‖1 - w * z‖ ^ 2 := by
      rw [hns]
      have h1 : c ^ 2 ≤ c := by nlinarith
      have h2 : c ^ 2 * r ^ 2 ≤ c * r ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg r)
      nlinarith [mul_nonneg hc0 (sq_nonneg r), mul_nonneg hc0 hr0]
    have hnn : 0 ≤ (1 - r) + (c / 2) * r := by nlinarith
    nlinarith [norm_nonneg (1 - w * z)]
  have hlb_u : 1 - r ≤ ‖1 - u * z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (u * z); rw [norm_one, norm_mul, hu, one_mul] at h; exact h
  have hlb_v : 1 - r ≤ ‖1 - v * z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (v * z); rw [norm_one, norm_mul, hv, one_mul] at h; exact h
  rcases le_total (u * z).re (v * z).re with hle | hle
  · have hreu : (u * z).re ≤ (1 - c) * r := by linarith
    have hu_strong := hsingle u hu hreu
    calc (1 - r) ^ 2 + (c / 2) * r * (1 - r)
        = ((1 - r) + (c / 2) * r) * (1 - r) := by ring
      _ ≤ ‖1 - u * z‖ * ‖1 - v * z‖ := mul_le_mul hu_strong hlb_v hr1 (norm_nonneg _)
  · have hrev : (v * z).re ≤ (1 - c) * r := by linarith
    have hv_strong := hsingle v hv hrev
    calc (1 - r) ^ 2 + (c / 2) * r * (1 - r)
        = (1 - r) * ((1 - r) + (c / 2) * r) := by ring
      _ ≤ ‖1 - u * z‖ * ‖1 - v * z‖ := mul_le_mul hlb_u hv_strong (by nlinarith) (norm_nonneg _)

/-- Parallelogram lower bound: for `‖u‖ = ‖v‖ = 1`, `‖u - v‖^2 / 8 ≤ 1 - ‖u + v‖ / 2`. -/
lemma unit_chord_sq_div_eight_le {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - v‖ ^ 2 / 8 ≤ 1 - ‖u + v‖ / 2 := by
  have hpar : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 4 := by
    have h1 := parallelogram_law_with_norm (𝕜 := ℝ) u v
    rw [hu, hv] at h1
    nlinarith
  have hle2 : ‖u + v‖ ≤ 2 := by
    have := norm_add_le u v; rw [hu, hv] at this; linarith
  have hnn : 0 ≤ ‖u + v‖ := norm_nonneg _
  -- 4 - ‖u + v‖^2 = (2 - ‖u + v‖) * (2 + ‖u + v‖) ≤ 4 * (2 - ‖u + v‖) = 8 * (1 - ‖u + v‖ / 2)!
  nlinarith

/-- **THEOREM 3 (Exact Equal-Modulus Dual Smale Conjecture — All `n ≥ 2`)**:
    If all critical points have equal modulus `‖ζ_k‖ = R` (`‖w k‖ = 1 / R`), then
    `∃ j, 1 / n ≤ ‖dualSmaleQuotient n w j‖`. -/
theorem exact_equal_modulus_dual_smale {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    {R : ℝ} (hR : 0 < R) (heq : ∀ k, ‖w k‖ = 1 / R) :
    ∃ j : Fin (n - 1), 1 / (n : ℝ) ≤ ‖dualSmaleQuotient n w j‖ := by
  simpa using exact_bounded_spread_dual_smale hn w hR one_pos
    (fun k => by rw [one_mul, heq k]) (fun k => le_of_eq (heq k))

/-- **THEOREM 4 (Quantitative Stability for Equal-Modulus Dual Smale — All `n ≥ 2`)**:
    If all critical points lie on the circle `‖ζ_k‖ = R` (`‖w k‖ = 1 / R`), then for ANY pair
    of indices `i₀, j₀ : Fin (n - 1)`, letting `u_k = R * w k` (unit vectors `‖u_k‖ = 1`):
    `∃ j, 1 / n + ‖u_{i₀} - u_{j₀}‖^2 / (16 * n * (n - 1)) ≤ ‖dualSmaleQuotient n w j‖`! -/
theorem equal_modulus_quantitative_stability {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    {R : ℝ} (hR : 0 < R) (heq : ∀ k, ‖w k‖ = 1 / R) (i₀ j₀ : Fin (n - 1)) :
    ∃ j : Fin (n - 1),
      1 / (n : ℝ) + ‖(R : ℂ) * w i₀ - (R : ℂ) * w j₀‖ ^ 2 / (16 * (n : ℝ) * ((n - 1 : ℕ) : ℝ)) ≤
        ‖dualSmaleQuotient n w j‖ := by
  by_cases hij : i₀ = j₀
  · subst hij
    simpa using exact_equal_modulus_dual_smale hn w hR heq
  · have hn3 : 3 ≤ n := by
      by_contra hlt; push Not at hlt
      have : i₀ = j₀ := Fin.ext (by omega)
      exact hij this
    have hw : ∀ k, w k ≠ 0 := fun k => norm_pos_iff.mp (by rw [heq k]; positivity)
    set u : Fin (n - 1) → ℂ := fun k => (R : ℂ) * w k
    have hu : ∀ k, ‖u k‖ = 1 := fun k => by
      dsimp [u]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hR), heq k]
      exact mul_one_div_cancel (ne_of_gt hR)
    set c : ℝ := 1 - ‖u i₀ + u j₀‖ / 2
    have hc0 : 0 ≤ c := by dsimp [c]; linarith [norm_add_le (u i₀) (u j₀), hu i₀, hu j₀]
    set P := polyFromInvCrits n w
    set φ : ℝ → ℝ := fun s =>
      (1 - s / R) ^ (n - 1) + (c / 2) * (s / R) * (1 - s / R) ^ (n - 2)
    set Φ : ℝ → ℝ := fun s =>
      R * ((1 - (1 - s / R) ^ n) / (n : ℝ) +
        (c / 2) * ((1 - (1 - s / R) ^ (n - 1)) / ((n - 1 : ℕ) : ℝ) -
                   (1 - (1 - s / R) ^ n) / (n : ℝ)))
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    have hΦ0 : Φ 0 = 0 := by dsimp [Φ]; simp
    have hΦR : Φ R = R * (1 / (n : ℝ) + c / (2 * (n : ℝ) * ((n - 1 : ℕ) : ℝ))) := by
      dsimp [Φ]
      rw [div_self (ne_of_gt hR), sub_self, zero_pow (by omega : n ≠ 0),
        zero_pow (by omega : n - 1 ≠ 0)]
      have hsub : (n : ℝ) - ((n - 1 : ℕ) : ℝ) = 1 := by
        have : (n - 1) + 1 = n := by omega
        have hcast : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by exact_mod_cast this
        linarith
      field_simp [ne_of_gt hn_pos, ne_of_gt hn1_pos]
      nlinarith
    have hΦ_deriv : ∀ s ∈ Set.Ico (0 : ℝ) R, HasDerivAt Φ (φ s) s := by
      intro s _
      have hinner : HasDerivAt (fun x : ℝ => 1 - x / R) (-(1 / R)) s := by
        have h1 : HasDerivAt (fun x : ℝ => x / R) (1 / R) s := by simpa using (hasDerivAt_id s).div_const R
        have h2 := (hasDerivAt_const s (1 : ℝ)).sub h1
        convert h2 using 1; ring
      have hpow_n : HasDerivAt (fun x : ℝ => (1 - x / R) ^ n)
          ((n : ℝ) * (1 - s / R) ^ (n - 1) * (-(1 / R))) s := hinner.pow n
      have hpow_n1 : HasDerivAt (fun x : ℝ => (1 - x / R) ^ (n - 1))
          (((n - 1 : ℕ) : ℝ) * (1 - s / R) ^ (n - 2) * (-(1 / R))) s := by
        have h := hinner.pow (n - 1)
        rwa [show n - 1 - 1 = n - 2 by omega] at h
      have hterm1 : HasDerivAt (fun x : ℝ => (1 - (1 - x / R) ^ n) / (n : ℝ))
          ((1 - s / R) ^ (n - 1) / R) s := by
        have h := ((hasDerivAt_const s (1 : ℝ)).sub hpow_n).div_const (n : ℝ)
        convert h using 1
        field_simp [ne_of_gt hn_pos, ne_of_gt hR]
        ring
      have hterm2 : HasDerivAt (fun x : ℝ => (1 - (1 - x / R) ^ (n - 1)) / ((n - 1 : ℕ) : ℝ))
          ((1 - s / R) ^ (n - 2) / R) s := by
        have h := ((hasDerivAt_const s (1 : ℝ)).sub hpow_n1).div_const ((n - 1 : ℕ) : ℝ)
        convert h using 1
        field_simp [ne_of_gt hn1_pos, ne_of_gt hR]
        ring
      have hfull := (hterm1.add ((hterm2.sub hterm1).const_mul (c / 2))).const_mul R
      convert hfull using 1
      dsimp [φ]
      have hexp : (1 - s / R) ^ (n - 1) = (1 - s / R) * (1 - s / R) ^ (n - 2) := by
        rw [← pow_succ', show (n - 2) + 1 = n - 1 by omega]
      rw [hexp]
      field_simp [ne_of_gt hR]
      ring
    have hΦ_cont : ContinuousOn Φ (Set.Icc 0 R) := by
      dsimp [Φ]
      fun_prop
    have hφ_pos : ∀ s ∈ Set.Ico (0 : ℝ) R, 0 < φ s := by
      intro s hs
      have h1 : 0 < 1 - s / R := by have := (div_lt_one hR).mpr hs.2; linarith
      have h2 : 0 ≤ (c / 2) * (s / R) * (1 - s / R) ^ (n - 2) := by
        have : 0 ≤ s / R := div_nonneg hs.1 (le_of_lt hR)
        positivity
      dsimp [φ]
      have h3 : 0 < (1 - s / R) ^ (n - 1) := pow_pos h1 _
      linarith
    have hP'_lb : ∀ z : ℂ, ‖z‖ < R → φ ‖z‖ ≤ ‖(derivative P).eval z‖ := by
      intro z hz
      rw [derivative_polyFromInvCrits_eval_prod (by omega) w z, norm_prod]
      set z' : ℂ := z / (R : ℂ)
      have hz'_norm : ‖z'‖ = ‖z‖ / R := by
        dsimp [z']; rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hR)]
      have hz'_le : ‖z'‖ ≤ 1 := by rw [hz'_norm]; exact le_of_lt ((div_lt_one hR).mpr hz)
      have hfac_eq : ∀ k : Fin (n - 1), 1 - w k * z = 1 - u k * z' := fun k => by
        dsimp [u, z']
        have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
        field_simp [hRc]
      simp_rw [hfac_eq]
      -- Split off the two distinct indices i₀, j₀ from Finset.univ!
      set rest : Finset (Fin (n - 1)) := (Finset.univ.erase i₀).erase j₀
      have hi₀_mem : i₀ ∈ (Finset.univ : Finset (Fin (n - 1))) := Finset.mem_univ i₀
      have hj₀_mem : j₀ ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j₀⟩
      have hsplit : ∏ k : Fin (n - 1), ‖1 - u k * z'‖ =
          (‖1 - u i₀ * z'‖ * ‖1 - u j₀ * z'‖) * ∏ k ∈ rest, ‖1 - u k * z'‖ := by
        rw [← Finset.mul_prod_erase Finset.univ (fun k => ‖1 - u k * z'‖) hi₀_mem,
            ← Finset.mul_prod_erase (Finset.univ.erase i₀) (fun k => ‖1 - u k * z'‖) hj₀_mem,
            ← mul_assoc]
      rw [hsplit]
      have hcard_rest : rest.card = n - 3 := by
        dsimp [rest]
        rw [Finset.card_erase_of_mem hj₀_mem, Finset.card_erase_of_mem hi₀_mem, Finset.card_fin]
        omega
      have hrest_lb : (1 - ‖z'‖) ^ (n - 3) ≤ ∏ k ∈ rest, ‖1 - u k * z'‖ := by
        calc (1 - ‖z'‖) ^ (n - 3) = ∏ _k ∈ rest, (1 - ‖z'‖) := by rw [Finset.prod_const, hcard_rest]
          _ ≤ ∏ k ∈ rest, ‖1 - u k * z'‖ := by
              apply finset_prod_le_prod_real
              · intro _ _; linarith
              · intro k _
                have h := norm_sub_norm_le (1 : ℂ) (u k * z')
                rw [norm_one, norm_mul, hu k, one_mul] at h; exact h
      have htwo := two_unit_factor_stability (hu i₀) (hu j₀) hz'_le
      have hnn1 : 0 ≤ (1 - ‖z'‖) ^ 2 + (c / 2) * ‖z'‖ * (1 - ‖z'‖) := by
        have : 0 ≤ 1 - ‖z'‖ := by linarith
        positivity
      have hnn2 : 0 ≤ (1 - ‖z'‖) ^ (n - 3) := pow_nonneg (by linarith) _
      have hmul := mul_le_mul htwo hrest_lb hnn2 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      have hpow_eq : ((1 - ‖z'‖) ^ 2 + (c / 2) * ‖z'‖ * (1 - ‖z'‖)) * (1 - ‖z'‖) ^ (n - 3) = φ ‖z‖ := by
        dsimp [φ]
        rw [hz'_norm]
        have hp1 : (1 - ‖z‖ / R) ^ 2 * (1 - ‖z‖ / R) ^ (n - 3) = (1 - ‖z‖ / R) ^ (n - 1) := by
          rw [← pow_add, show 2 + (n - 3) = n - 1 by omega]
        have hp2 : (1 - ‖z‖ / R) * (1 - ‖z‖ / R) ^ (n - 3) = (1 - ‖z‖ / R) ^ (n - 2) := by
          rw [← pow_succ', show (n - 3) + 1 = n - 2 by omega]
        calc ((1 - ‖z‖ / R) ^ 2 + c / 2 * (‖z‖ / R) * (1 - ‖z‖ / R)) * (1 - ‖z‖ / R) ^ (n - 3)
            = (1 - ‖z‖ / R) ^ 2 * (1 - ‖z‖ / R) ^ (n - 3) +
              c / 2 * (‖z‖ / R) * ((1 - ‖z‖ / R) * (1 - ‖z‖ / R) ^ (n - 3)) := by ring
          _ = (1 - ‖z‖ / R) ^ (n - 1) + c / 2 * (‖z‖ / R) * (1 - ‖z‖ / R) ^ (n - 2) := by rw [hp1, hp2]
      dsimp only [c] at hpow_eq
      linarith
    have hdeg : 2 ≤ P.natDegree := by rw [natDegree_polyFromInvCrits (by omega) w hw]; exact hn
    obtain ⟨ζ, hζ0, hζv⟩ := radial_lift_critical_value_ge P hdeg (polyFromInvCrits_eval_zero n w)
      (derivative_polyFromInvCrits_eval_zero (by omega) w) hR hΦ0 hΦ_cont hΦ_deriv hφ_pos hP'_lb
    obtain ⟨j, rfl⟩ := crit_point_eq_inv_w hn w hw hζ0
    refine ⟨j, ?_⟩
    rw [hΦR] at hζv
    rw [← polyFromInvCrits_div_eq_quotient (by omega) w j (hw j), norm_div, norm_inv, heq j]
    simp only [one_div, inv_inv]
    have hdiv : 1 / (n : ℝ) + c / (2 * (n : ℝ) * ((n - 1 : ℕ) : ℝ)) ≤
        ‖P.eval (w j)⁻¹‖ / R := by
      rw [le_div_iff₀ hR]; linarith
    have hchord : ‖u i₀ - u j₀‖ ^ 2 / 8 ≤ c := unit_chord_sq_div_eight_le (hu i₀) (hu j₀)
    have hgap : ‖u i₀ - u j₀‖ ^ 2 / (16 * (n : ℝ) * ((n - 1 : ℕ) : ℝ)) ≤
        c / (2 * (n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
      have hden_pos : 0 < 2 * (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by positivity
      calc ‖u i₀ - u j₀‖ ^ 2 / (16 * (n : ℝ) * ((n - 1 : ℕ) : ℝ))
          = (‖u i₀ - u j₀‖ ^ 2 / 8) / (2 * (n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by ring
        _ ≤ c / (2 * (n : ℝ) * ((n - 1 : ℕ) : ℝ)) :=
            div_le_div_of_nonneg_right hchord (le_of_lt hden_pos)
    rw [one_div] at hdiv
    dsimp only [P] at hdiv
    dsimp only [u] at hgap
    linarith

/-- **COROLLARY 4.1 (Strict Uniqueness of the Extremal Polynomial on Any Circle — All `n ≥ 2`)**:
    If all critical points have equal modulus `R > 0` (`‖w k‖ = 1 / R`) and every critical point
    satisfies `‖dualSmaleQuotient n w j‖ ≤ 1 / n`, then all critical points coincide:
    `∀ i j, w i = w j` (i.e., `P(z) = (ζ₀ / n) * (1 - (1 - z / ζ₀)^n)`). -/
theorem equal_modulus_strict_uniqueness {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    {R : ℝ} (hR : 0 < R) (heq : ∀ k, ‖w k‖ = 1 / R)
    (hmax : ∀ j : Fin (n - 1), ‖dualSmaleQuotient n w j‖ ≤ 1 / (n : ℝ)) :
    ∀ i j : Fin (n - 1), w i = w j := by
  intro i₀ j₀
  obtain ⟨j, hj⟩ := equal_modulus_quantitative_stability hn w hR heq i₀ j₀
  have hle := hmax j
  have hden_pos : 0 < 16 * (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
    have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have h2 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    positivity
  have hsq0 : ‖(R : ℂ) * w i₀ - (R : ℂ) * w j₀‖ ^ 2 ≤ 0 := by
    have hdiv0 : ‖(R : ℂ) * w i₀ - (R : ℂ) * w j₀‖ ^ 2 / (16 * (n : ℝ) * ((n - 1 : ℕ) : ℝ)) ≤ 0 := by
      linarith
    exact (div_nonpos_iff.mp hdiv0).resolve_left (fun hc => by linarith) |>.1
  have hnorm0 : ‖(R : ℂ) * w i₀ - (R : ℂ) * w j₀‖ = 0 := by
    nlinarith [norm_nonneg ((R : ℂ) * w i₀ - (R : ℂ) * w j₀), sq_nonneg ‖(R : ℂ) * w i₀ - (R : ℂ) * w j₀‖]
  have hsub0 : (R : ℂ) * w i₀ - (R : ℂ) * w j₀ = 0 := norm_eq_zero.mp hnorm0
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
  exact mul_left_cancel₀ hRc (sub_eq_zero.mp hsub0)

end DualSmaleMultiscale
