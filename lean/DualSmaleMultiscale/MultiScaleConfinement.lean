/-
  DualSmaleMultiscale/MultiScaleConfinement.lean

  THEOREM 5 (Multi-Scale Inner-Cluster Confinement Theorem — All n >= 2, All 1 <= m <= n - 1):
    Let P(z) = z + a_2 z^2 + ... + a_n z^n have critical points zeta_1, ..., zeta_{n-1}
    (w_k = 1 / zeta_k) and suppose a nonempty subset I of inner indices satisfies:
      - r_1 <= |zeta_k| <= r_m  for all k in I  (i.e. 1/r_m <= |w_k| <= 1/r_1),
      - r_m * sum_{k not in I} |w_k| <= 1/36  (constant threshold, independent of m and n!).
    Then:
      (1) |P(z)| > 6 * r_m everywhere on the circle |z| = 6 * r_m
          (proved via Grace-Walsh-Szego with an external holomorphic multiplier R_out(z*t)!),
      (2) The confined radial-lift theorem produces an INNER critical point zeta_j (j in I) with
            |P(zeta_j) / zeta_j| >= 1 / (r_m / r_1 + sum_{k in I} r_m * |w_k| + 1/36).
      (3) COROLLARY (Exact Dual Smale Conjecture for Separated Inner Clusters):
          Whenever r_m / r_1 + sum_{k in I} r_m * |w_k| <= n - 1/36
          (in particular, for ANY isolated equal-modulus inner cluster of size m <= n - 2),
          the EXACT Dual Smale Conjecture holds: exists j in I, 1/n <= |P(zeta_j)/zeta_j|!
-/

import DualSmaleMultiscale.ExactCriticalValue

open scoped BigOperators
open Polynomial Complex DualSmale

namespace DualSmaleMultiscale

/-! ### Section 1: Elementary Algebraic & Product-Perturbation Helpers -/

/-- Expansion `∏_{k : Fin m} (ζ_k + u) = ∑_{d=0}^m elemSym m ζ d * u^(m - d)`. -/
lemma prod_add_eq_sum_elemSym :
    ∀ (m : ℕ) (ζ : Fin m → ℂ) (u : ℂ),
      (∏ k : Fin m, (ζ k + u)) = ∑ d ∈ Finset.range (m + 1), elemSym m ζ d * u ^ (m - d) := by
  intro m
  induction m with
  | zero => intro ζ u; simp [elemSym]
  | succ m ih =>
    intro ζ u
    rw [Fin.prod_univ_castSucc, ih (fun i => ζ i.castSucc) u]
    have hlast : elemSym m (fun i => ζ i.castSucc) (m + 1) = 0 :=
      elemSym_eq_zero_of_lt m _ (m + 1) (by omega)
    symm
    rw [Finset.sum_range_succ']
    have he0 : elemSym (m + 1) ζ 0 = 1 := rfl
    rw [he0, one_mul, Nat.sub_zero]
    have hsplit : ∑ d ∈ Finset.range (m + 1), elemSym (m + 1) ζ (d + 1) * u ^ (m + 1 - (d + 1)) =
        (∑ d ∈ Finset.range (m + 1), elemSym m (fun i => ζ i.castSucc) (d + 1) * u ^ (m - d)) +
        ζ (Fin.last m) * (∑ d ∈ Finset.range (m + 1), elemSym m (fun i => ζ i.castSucc) d * u ^ (m - d)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro d _
      simp only [elemSym, Nat.add_sub_add_right]
      ring
    rw [hsplit]
    have hshift : (∑ d ∈ Finset.range (m + 1), elemSym m (fun i => ζ i.castSucc) (d + 1) * u ^ (m - d)) + u ^ (m + 1) =
        u * (∑ d ∈ Finset.range (m + 1), elemSym m (fun i => ζ i.castSucc) d * u ^ (m - d)) := by
      rw [Finset.mul_sum]
      symm
      rw [Finset.sum_range_succ']
      have he0' : elemSym m (fun i => ζ i.castSucc) 0 = 1 := by cases m <;> rfl
      rw [he0', one_mul, Nat.sub_zero, ← pow_succ']
      congr 1
      rw [Finset.sum_range_succ, hlast, zero_mul, add_zero]
      apply Finset.sum_congr rfl; intro d hd
      rw [Finset.mem_range] at hd
      have hpow : u * (elemSym m (fun i => ζ i.castSucc) (d + 1) * u ^ (m - (d + 1))) =
          elemSym m (fun i => ζ i.castSucc) (d + 1) * u ^ (m - d) := by
        have : m - d = (m - (d + 1)) + 1 := by omega
        rw [this, pow_succ']; ring
      exact hpow
    linear_combination hshift

/-- Product perturbation bound: `‖∏_{k ∈ s} (1 - u k) - 1‖ ≤ exp(∑_{k ∈ s} ‖u k‖) - 1`. -/
lemma norm_prod_one_sub_sub_one_le {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖(∏ k ∈ s, (1 - u k)) - 1‖ ≤ Real.exp (∑ k ∈ s, ‖u k‖) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    set P := ∏ k ∈ s, (1 - u k)
    set S := ∑ k ∈ s, ‖u k‖
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun k _ => norm_nonneg _)
    have hP_norm : ‖P‖ ≤ Real.exp S := by
      have h1 : ‖P‖ - 1 ≤ ‖P - 1‖ := by
        have := norm_sub_norm_le P 1; rwa [norm_one] at this
      linarith
    have hdecomp : (1 - u a) * P - 1 = (P - 1) - u a * P := by ring
    rw [hdecomp]
    have htri : ‖(P - 1) - u a * P‖ ≤ ‖P - 1‖ + ‖u a‖ * ‖P‖ := by
      calc ‖(P - 1) - u a * P‖ ≤ ‖P - 1‖ + ‖u a * P‖ := norm_sub_le _ _
        _ = ‖P - 1‖ + ‖u a‖ * ‖P‖ := by rw [norm_mul]
    have hexp_a : 1 + ‖u a‖ ≤ Real.exp ‖u a‖ := by linarith [Real.add_one_le_exp ‖u a‖]
    have hprod_exp : (Real.exp S - 1) + ‖u a‖ * Real.exp S ≤ Real.exp (‖u a‖ + S) - 1 := by
      rw [Real.exp_add]
      nlinarith [Real.exp_pos S]
    have hmul : ‖u a‖ * ‖P‖ ≤ ‖u a‖ * Real.exp S := mul_le_mul_of_nonneg_left hP_norm (norm_nonneg _)
    linarith

/-- Elementary bound `exp(1/6) - 1 ≤ 1/5`, proved directly from `Real.add_one_le_exp (-1/6)`. -/
lemma exp_one_sixth_sub_one_le : Real.exp (1 / 6 : ℝ) - 1 ≤ 1 / 5 := by
  have h1 : (5 / 6 : ℝ) ≤ Real.exp (-(1 / 6 : ℝ)) := by
    have := Real.add_one_le_exp (-(1 / 6 : ℝ)); linarith
  rw [Real.exp_neg] at h1
  have hpos : 0 < Real.exp (1 / 6 : ℝ) := Real.exp_pos _
  have h2 : Real.exp (1 / 6 : ℝ) ≤ 6 / 5 := by
    have hmul := mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
    rw [inv_mul_cancel₀ (ne_of_gt hpos)] at hmul
    linarith
  linarith

/-- Exact integral formula: `P_w(z) = z * ∫ t in 0..1, ∏ k, (1 - w k * (z * t))`. -/
lemma polyFromInvCrits_eq_integral {n : ℕ} (hn : 1 ≤ n) (w : Fin (n - 1) → ℂ) (z : ℂ) :
    (polyFromInvCrits n w).eval z =
      z * ∫ t in (0 : ℝ)..1, ∏ k : Fin (n - 1), (1 - w k * (z * (t : ℂ))) := by
  set P := polyFromInvCrits n w
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => P.eval (z * (s : ℂ)))
        ((derivative P).eval (z * (t : ℂ)) * z) t := by
    intro t _
    have hline : HasDerivAt (fun s : ℝ => z * (s : ℂ)) z t := by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      simpa using h1.const_mul z
    exact (P.hasDerivAt (z * (t : ℂ))).comp t hline
  have hcont : Continuous (fun t : ℝ => (derivative P).eval (z * (t : ℂ)) * z) :=
    ((derivative P).continuous.comp (continuous_const.mul Complex.continuous_ofReal)).mul continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, P, polyFromInvCrits_eval_zero,
    sub_zero] at hftc
  rw [← hftc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [derivative_polyFromInvCrits_eval_prod hn w (z * (t : ℂ)), mul_comm]

/-! ### Section 2: Circle Lower Bound `|P(z)| > 6 r_m` via GWS with External Multiplier -/

/-- Linearity of the complex interval integral over finite sums. -/
lemma intervalIntegral_finset_sum_complex {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (a b : ℝ)
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

/-- **GWS-with-External-Multiplier Circle Bound**:
    If `I` is a nonempty subset of `Fin (n - 1)` of size `m = I.card ≥ 1`, with
    `∀ k ∈ I, 1 / r_m ≤ ‖w k‖` (i.e. `‖ζ_k‖ ≤ r_m`) and
    `r_m * ∑ k ∈ Iᶜ, ‖w k‖ ≤ 1 / 36`, then for EVERY `z : ℂ` with `‖z‖ = 6 * r_m`:
    `6 * r_m < ‖(polyFromInvCrits n w).eval z‖`! -/
theorem circle_lower_bound_of_cluster_gap {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (I : Finset (Fin (n - 1))) (hI_ne : I.Nonempty)
    {r_m : ℝ} (hrm : 0 < r_m)
    (hI_in : ∀ k ∈ I, 1 / r_m ≤ ‖w k‖)
    (hI_gap : r_m * ∑ k ∈ Iᶜ, ‖w k‖ ≤ 1 / 36)
    {z : ℂ} (hz : ‖z‖ = 6 * r_m) :
    6 * r_m < ‖(polyFromInvCrits n w).eval z‖ := by
  classical
  set m : ℕ := I.card
  have hm : 1 ≤ m := Finset.Nonempty.card_pos hI_ne
  -- Index inner coordinates via an equivalence `e : Fin m ≃ I`
  let e : Fin m ≃ {k : Fin (n - 1) // k ∈ I} := (Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
  let w_in : Fin m → ℂ := fun i => w (e i).1
  have hw_in_ne : ∀ i : Fin m, w_in i ≠ 0 := fun i =>
    norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hI_in (e i).1 (e i).2))
  let ζ_in : Fin m → ℂ := fun i => (w_in i)⁻¹
  have hζ_norm : ∀ i : Fin m, ‖ζ_in i - 0‖ ≤ r_m := by
    intro i
    rw [sub_zero, norm_inv]
    have h1 : 1 / r_m ≤ ‖w_in i‖ := hI_in (e i).1 (e i).2
    calc ‖w_in i‖⁻¹ ≤ (1 / r_m)⁻¹ := inv_anti₀ (by positivity) h1
      _ = r_m := by simp
  -- Outer multiplier R_out(t) = ∏_{k ∈ Iᶜ} (1 - w k * (z * t))
  let R_out : ℝ → ℂ := fun t => ∏ k ∈ Iᶜ, (1 - w k * (z * (t : ℂ)))
  have hRout_cont : Continuous R_out := by dsimp [R_out]; fun_prop
  -- Factor P(z) as z * (∏ w_in) * ∫_0^1 (∏ (ζ_in i - z * t)) * R_out(t) dt
  have hP_factor : (polyFromInvCrits n w).eval z =
      z * (∏ i : Fin m, w_in i) *
        ∫ t in (0 : ℝ)..1, (∏ i : Fin m, (ζ_in i - z * (t : ℂ))) * R_out t := by
    rw [polyFromInvCrits_eq_integral (by omega) w z, mul_assoc]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    -- Split ∏_{k : Fin (n-1)} into (∏_{k ∈ I}) * (∏_{k ∈ Iᶜ})
    have hsplit : (∏ k : Fin (n - 1), (1 - w k * (z * (t : ℂ)))) =
        (∏ k ∈ I, (1 - w k * (z * (t : ℂ)))) * R_out t := by
      dsimp [R_out]
      rw [← Finset.prod_mul_prod_compl I]
    rw [hsplit]
    have hin : (∏ k ∈ I, (1 - w k * (z * (t : ℂ)))) =
        (∏ i : Fin m, w_in i) * (∏ i : Fin m, (ζ_in i - z * (t : ℂ))) := by
      rw [← Finset.prod_mul_distrib]
      have hcoe : (∏ k ∈ I, (1 - w k * (z * (t : ℂ)))) =
          ∏ x : {k : Fin (n - 1) // k ∈ I}, (1 - w x.1 * (z * (t : ℂ))) :=
        (Finset.prod_coe_sort I _).symm
      rw [hcoe, ← Equiv.prod_comp e]
      apply Finset.prod_congr rfl; intro i _
      dsimp [ζ_in, w_in]
      have hne := hw_in_ne i
      dsimp [w_in] at hne
      field_simp [hne]
    rw [hin]; ring
  -- Express the integral as `symMultiaffine m c ζ_in`!
  let c : ℕ → ℂ := fun d => ∫ t in (0 : ℝ)..1, (- (z * (t : ℂ))) ^ (m - d) * R_out t
  have hint_sym : (∫ t in (0 : ℝ)..1, (∏ i : Fin m, (ζ_in i - z * (t : ℂ))) * R_out t) =
      symMultiaffine m c ζ_in := by
    have hintegrand : ∀ t : ℝ, (∏ i : Fin m, (ζ_in i - z * (t : ℂ))) * R_out t =
        ∑ d ∈ Finset.range (m + 1), elemSym m ζ_in d * ((-(z * (t : ℂ))) ^ (m - d) * R_out t) := by
      intro t
      have h1 : (∏ i : Fin m, (ζ_in i - z * (t : ℂ))) =
          ∏ i : Fin m, (ζ_in i + (-(z * (t : ℂ)))) := by
        apply Finset.prod_congr rfl; intro i _; ring
      rw [h1, prod_add_eq_sum_elemSym, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro d _; ring
    simp_rw [hintegrand]
    rw [intervalIntegral_finset_sum_complex]
    · unfold symMultiaffine
      apply Finset.sum_congr rfl; intro d _
      rw [intervalIntegral.integral_const_mul]
      dsimp [c]; ring
    · intro d _
      have hcd : Continuous (fun t : ℝ => elemSym m ζ_in d * ((-(z * (t : ℂ))) ^ (m - d) * R_out t)) :=
        continuous_const.mul
          ((((continuous_const.mul Complex.continuous_ofReal).neg).pow (m - d)).mul hRout_cont)
      exact hcd.intervalIntegrable 0 1
  -- Apply Grace-Walsh-Szego on the closed ball ‖ζ - 0‖ ≤ r_m!
  obtain ⟨ζ₀, hζ₀_ball, hζ₀_eq⟩ :=
    grace_walsh_szego_closedBall hm hrm c ζ_in hζ_norm
  rw [sub_zero] at hζ₀_ball
  -- Rewrite symMultiaffine m c (fun _ => ζ₀) back into the 1-variable integral ∫_0^1 (ζ₀ - z t)^m R_out(t) dt!
  have hdiag_int : symMultiaffine m c (fun _ => ζ₀) =
      ∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m * R_out t := by
    have hintegrand : ∀ t : ℝ, (ζ₀ - z * (t : ℂ)) ^ m * R_out t =
        ∑ d ∈ Finset.range (m + 1), elemSym m (fun _ => ζ₀) d * ((-(z * (t : ℂ))) ^ (m - d) * R_out t) := by
      intro t
      have h1 : (ζ₀ - z * (t : ℂ)) ^ m = ∏ _i : Fin m, (ζ₀ + (-(z * (t : ℂ)))) := by
        rw [Finset.prod_const, Finset.card_fin, sub_eq_add_neg]
      rw [h1, prod_add_eq_sum_elemSym, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro d _; ring
    simp_rw [hintegrand]
    rw [intervalIntegral_finset_sum_complex]
    · unfold symMultiaffine
      apply Finset.sum_congr rfl; intro d _
      rw [intervalIntegral.integral_const_mul]
      dsimp [c]; ring
    · intro d _
      have hcd : Continuous (fun t : ℝ => elemSym m (fun _ => ζ₀) d * ((-(z * (t : ℂ))) ^ (m - d) * R_out t)) :=
        continuous_const.mul
          ((((continuous_const.mul Complex.continuous_ofReal).neg).pow (m - d)).mul hRout_cont)
      exact hcd.intervalIntegrable 0 1
  -- Now lower-bound ‖∫_0^1 (ζ₀ - z t)^m R_out(t) dt‖ using A = ‖ζ₀ - z‖ ≥ 5 r_m!
  set A : ℝ := ‖ζ₀ - z‖
  have hA_ge : 5 * r_m ≤ A := by
    have htri := norm_sub_norm_le z ζ₀
    rw [norm_sub_rev z ζ₀, hz] at htri
    dsimp [A]; linarith
  have hA_pos : 0 < A := by linarith
  have hζ₀_le_A : ‖ζ₀‖ ≤ A / 5 := by linarith
  have hR_le_A : 6 * r_m ≤ (6 / 5 : ℝ) * A := by linarith
  -- (a) Main term: ‖∫_0^1 (ζ₀ - z t)^m dt‖ ≥ (4 / 5) * A^m / (m + 1)
  have hz_ne : z ≠ 0 := norm_pos_iff.mp (by rw [hz]; linarith)
  have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hm1_c : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  have hmain_eq : (∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m) =
      (ζ₀ ^ (m + 1) - (ζ₀ - z) ^ (m + 1)) / (((m + 1 : ℕ) : ℂ) * z) := by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => - ((ζ₀ - z * (s : ℂ)) ^ (m + 1)) / (((m + 1 : ℕ) : ℂ) * z))
          ((ζ₀ - z * (t : ℂ)) ^ m) t := by
      intro t _
      have h1 : HasDerivAt (fun s : ℝ => ζ₀ - z * (s : ℂ)) (-z) t := by
        have hc : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
        simpa using (hc.const_mul z).const_sub ζ₀
      have h2 := (h1.pow (m + 1)).neg.div_const (((m + 1 : ℕ) : ℂ) * z)
      convert h2 using 1
      rw [Nat.add_sub_cancel]
      field_simp [hm1_c, hz_ne]
    have hcont : Continuous (fun t : ℝ => (ζ₀ - z * (t : ℂ)) ^ m) :=
      (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)).pow m
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, sub_zero]
    field_simp [hm1_c, hz_ne]
    ring
  have hmain_lb : (4 / 5 : ℝ) * A ^ m / ((m + 1 : ℕ) : ℝ) ≤ ‖∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m‖ := by
    rw [hmain_eq, norm_div, norm_mul, Complex.norm_natCast, hz]
    have hnum : (24 / 25 : ℝ) * A ^ (m + 1) ≤ ‖ζ₀ ^ (m + 1) - (ζ₀ - z) ^ (m + 1)‖ := by
      have htri := norm_sub_norm_le ((ζ₀ - z) ^ (m + 1)) (ζ₀ ^ (m + 1))
      rw [norm_sub_rev, norm_pow, norm_pow] at htri
      have hζpow : ‖ζ₀‖ ^ (m + 1) ≤ (1 / 25 : ℝ) * A ^ (m + 1) := by
        have h1 : ‖ζ₀‖ ^ (m + 1) ≤ (A / 5) ^ (m + 1) := pow_le_pow_left₀ (norm_nonneg _) hζ₀_le_A _
        rw [div_pow] at h1
        have h5 : (25 : ℝ) ≤ 5 ^ (m + 1) := by
          have : 5 ^ 2 ≤ 5 ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          exact_mod_cast this
        have hdiv : A ^ (m + 1) / 5 ^ (m + 1) ≤ A ^ (m + 1) / 25 :=
          div_le_div_of_nonneg_left (pow_nonneg (le_of_lt hA_pos) _) (by norm_num) h5
        linarith
      dsimp [A] at hζpow ⊢
      linarith
    have hden_pos : 0 < ((m + 1 : ℕ) : ℝ) * (6 * r_m) := by positivity
    rw [div_le_div_iff₀ hm1_pos hden_pos]
    calc (4 / 5 : ℝ) * A ^ m * (((m + 1 : ℕ) : ℝ) * (6 * r_m))
        ≤ (4 / 5 : ℝ) * A ^ m * (((m + 1 : ℕ) : ℝ) * ((6 / 5 : ℝ) * A)) := by
          gcongr
      _ = ((24 / 25 : ℝ) * A ^ (m + 1)) * ((m + 1 : ℕ) : ℝ) := by rw [pow_succ]; ring
      _ ≤ ‖ζ₀ ^ (m + 1) - (ζ₀ - z) ^ (m + 1)‖ * ((m + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hnum (le_of_lt hm1_pos)
  -- (b) Error term: ‖∫_0^1 (ζ₀ - z t)^m * (R_out(t) - 1) dt‖ ≤ (1 / 4) * A^m / (m + 1)
  have hRout_err : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖R_out t - 1‖ ≤ 1 / 5 := by
    intro t ht
    have h1 := norm_prod_one_sub_sub_one_le Iᶜ (fun k => w k * (z * (t : ℂ)))
    have hsum : ∑ k ∈ Iᶜ, ‖w k * (z * (t : ℂ))‖ ≤ 1 / 6 := by
      have hterm : ∀ k ∈ Iᶜ, ‖w k * (z * (t : ℂ))‖ ≤ (6 * r_m) * ‖w k‖ := by
        intro k _
        rw [norm_mul, norm_mul, hz, Complex.norm_real, Real.norm_of_nonneg ht.1]
        have : 6 * r_m * t ≤ 6 * r_m := by nlinarith [ht.2]
        nlinarith [norm_nonneg (w k)]
      calc ∑ k ∈ Iᶜ, ‖w k * (z * (t : ℂ))‖
          ≤ ∑ k ∈ Iᶜ, (6 * r_m) * ‖w k‖ := Finset.sum_le_sum hterm
        _ = 6 * (r_m * ∑ k ∈ Iᶜ, ‖w k‖) := by rw [← Finset.mul_sum]; ring
        _ ≤ 6 * (1 / 36) := by linarith
        _ = 1 / 6 := by norm_num
    have hexp : Real.exp (∑ k ∈ Iᶜ, ‖w k * (z * (t : ℂ))‖) - 1 ≤ Real.exp (1 / 6 : ℝ) - 1 := by
      linarith [Real.exp_le_exp.mpr hsum]
    exact le_trans (le_trans h1 hexp) exp_one_sixth_sub_one_le
  have herr_ub : ‖∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m * (R_out t - 1)‖ ≤
      (1 / 4 : ℝ) * A ^ m / ((m + 1 : ℕ) : ℝ) := by
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖(ζ₀ - z * (t : ℂ)) ^ m * (R_out t - 1)‖ ≤ (1 / 5 : ℝ) * (((1 + 4 * t) / 5) ^ m * A ^ m) := by
      intro t ht
      rw [norm_mul, norm_pow]
      have hseg : ‖ζ₀ - z * (t : ℂ)‖ ≤ ((1 + 4 * t) / 5) * A := by
        have hdecomp : ζ₀ - z * (t : ℂ) = ((1 - t : ℝ) : ℂ) * ζ₀ + (t : ℂ) * (ζ₀ - z) := by
          push_cast; ring
        rw [hdecomp]
        calc ‖((1 - t : ℝ) : ℂ) * ζ₀ + (t : ℂ) * (ζ₀ - z)‖
            ≤ ‖((1 - t : ℝ) : ℂ) * ζ₀‖ + ‖(t : ℂ) * (ζ₀ - z)‖ := norm_add_le _ _
          _ = (1 - t) * ‖ζ₀‖ + t * A := by
              rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
                Real.norm_of_nonneg (by linarith [ht.2]), Real.norm_of_nonneg ht.1]
          _ ≤ (1 - t) * (A / 5) + t * A := by nlinarith [ht.2]
          _ = ((1 + 4 * t) / 5) * A := by ring
      have hpow : ‖ζ₀ - z * (t : ℂ)‖ ^ m ≤ ((1 + 4 * t) / 5) ^ m * A ^ m := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hseg m
      have hR := hRout_err t ht
      have h14 : 0 ≤ (1 + 4 * t) / 5 := by linarith [ht.1]
      have hnn : 0 ≤ ((1 + 4 * t) / 5) ^ m * A ^ m := by positivity
      calc ‖ζ₀ - z * (t : ℂ)‖ ^ m * ‖R_out t - 1‖
          ≤ (((1 + 4 * t) / 5) ^ m * A ^ m) * (1 / 5 : ℝ) :=
            mul_le_mul hpow hR (norm_nonneg _) hnn
        _ = (1 / 5 : ℝ) * (((1 + 4 * t) / 5) ^ m * A ^ m) := by ring
    have hnorm_int : ‖∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m * (R_out t - 1)‖ ≤
        ∫ t in (0 : ℝ)..1, (1 / 5 : ℝ) * (((1 + 4 * t) / 5) ^ m * A ^ m) := by
      have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume) zero_le_one
        (f := fun t : ℝ => (ζ₀ - z * (t : ℂ)) ^ m * (R_out t - 1))
      refine le_trans h1 ?_
      apply intervalIntegral.integral_mono_on zero_le_one
      · exact (((continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)).pow m).mul
          (hRout_cont.sub continuous_const)).norm.intervalIntegrable 0 1
      · exact (continuous_const.mul
          ((((continuous_const.add (continuous_const.mul continuous_id)).div_const 5).pow m).mul
            continuous_const)).intervalIntegrable 0 1
      · exact hpt
    -- Compute the exact elementary integral ∫_0^1 ((1 + 4t)/5)^m dt = (5 / (4(m+1))) * (1 - (1/5)^(m+1))!
    have hint_exact : (∫ t in (0 : ℝ)..1, ((1 + 4 * t) / 5) ^ m) =
        (5 / (4 * ((m + 1 : ℕ) : ℝ))) * (1 - (1 / 5 : ℝ) ^ (m + 1)) := by
      have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun s : ℝ => (5 / (4 * ((m + 1 : ℕ) : ℝ))) * ((1 + 4 * s) / 5) ^ (m + 1))
            (((1 + 4 * t) / 5) ^ m) t := by
        intro t _
        have h1 : HasDerivAt (fun s : ℝ => (1 + 4 * s) / 5) (4 / 5 : ℝ) t := by
          simpa using ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).const_mul 4)).div_const 5
        have h2 := (h1.pow (m + 1)).const_mul (5 / (4 * ((m + 1 : ℕ) : ℝ)))
        convert h2 using 1
        rw [Nat.add_sub_cancel]
        field_simp [ne_of_gt hm1_pos]
      have hcont : Continuous (fun t : ℝ => ((1 + 4 * t) / 5) ^ m) :=
        ((continuous_const.add (continuous_const.mul continuous_id)).div_const 5).pow m
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
      norm_num; ring
    have hrhs : (∫ t in (0 : ℝ)..1, (1 / 5 : ℝ) * (((1 + 4 * t) / 5) ^ m * A ^ m)) ≤
        (1 / 4 : ℝ) * A ^ m / ((m + 1 : ℕ) : ℝ) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const, hint_exact]
      have hpow_nn : 0 ≤ (1 / 5 : ℝ) ^ (m + 1) := by positivity
      have hAm_nn : 0 ≤ A ^ m := by positivity
      have h1 : (1 / 5 : ℝ) * ((5 / (4 * ((m + 1 : ℕ) : ℝ))) * (1 - (1 / 5 : ℝ) ^ (m + 1)) * A ^ m) =
          ((1 / 4 : ℝ) * A ^ m / ((m + 1 : ℕ) : ℝ)) * (1 - (1 / 5 : ℝ) ^ (m + 1)) := by
        field_simp [ne_of_gt hm1_pos]
      rw [h1]
      nlinarith [div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) hAm_nn) (le_of_lt hm1_pos)]
    exact le_trans hnorm_int hrhs
  -- (c) Combine main term and error term!
  have hfull_int_lb : (11 / 20 : ℝ) * A ^ m / ((m + 1 : ℕ) : ℝ) ≤
      ‖∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m * R_out t‖ := by
    have hsplit_int : (∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m * R_out t) =
        (∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m) +
        (∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m * (R_out t - 1)) := by
      rw [← intervalIntegral.integral_add]
      · apply intervalIntegral.integral_congr; intro t _; ring
      · exact ((continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)).pow m).intervalIntegrable 0 1
      · exact (((continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)).pow m).mul
          (hRout_cont.sub continuous_const)).intervalIntegrable 0 1
    rw [hsplit_int]
    have htri : ‖∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m‖ -
        ‖∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m * (R_out t - 1)‖ ≤
        ‖(∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m) +
          (∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m * (R_out t - 1))‖ := by
      have h := norm_sub_norm_le
        (∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m)
        (-(∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m * (R_out t - 1)))
      rw [norm_neg, sub_neg_eq_add] at h
      exact h
    have hsub : (11 / 20 : ℝ) * A ^ m / ((m + 1 : ℕ) : ℝ) =
        (4 / 5 : ℝ) * A ^ m / ((m + 1 : ℕ) : ℝ) - (1 / 4 : ℝ) * A ^ m / ((m + 1 : ℕ) : ℝ) := by ring
    linarith
  -- (d) Multiply by ‖z‖ * ∏ ‖w_in i‖ ≥ (6 r_m) / r_m^m and use 5^m ≥ 2 (m + 1) for all m ≥ 1!
  rw [hP_factor, hint_sym, hζ₀_eq, hdiag_int, norm_mul, norm_mul, hz, norm_prod]
  have hprod_w : (1 / r_m) ^ m ≤ ∏ i : Fin m, ‖w_in i‖ := by
    calc (1 / r_m) ^ m = ∏ _i : Fin m, (1 / r_m) := by rw [Finset.prod_const, Finset.card_fin]
      _ ≤ ∏ i : Fin m, ‖w_in i‖ := finset_prod_le_prod_real _ _ _ (fun _ _ => by positivity) (fun i _ => hI_in (e i).1 (e i).2)
  have h5m : (2 * (m + 1) : ℝ) ≤ (5 : ℝ) ^ m := by
    have hnat : ∀ k : ℕ, 1 ≤ k → 2 * (k + 1) ≤ 5 ^ k := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        cases k with
        | zero => norm_num
        | succ k =>
          have hih := ih (by omega)
          calc 2 * (k + 1 + 1 + 1) ≤ 5 * (2 * (k + 1 + 1)) := by omega
            _ ≤ 5 * 5 ^ (k + 1) := Nat.mul_le_mul_left 5 hih
            _ = 5 ^ (k + 1 + 1) := by ring
    exact_mod_cast hnat m hm
  have hAm_ge : (5 : ℝ) ^ m * r_m ^ m ≤ A ^ m := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hA_ge m
  have hstep1 : (6 * r_m) * (1 / r_m) ^ m * ((11 / 20 : ℝ) * A ^ m / ((m + 1 : ℕ) : ℝ)) ≤
      6 * r_m * (∏ i : Fin m, ‖w_in i‖) * ‖∫ t in (0 : ℝ)..1, (ζ₀ - z * (t : ℂ)) ^ m * R_out t‖ := by
    have h1 : (6 * r_m) * (1 / r_m) ^ m ≤ (6 * r_m) * ∏ i : Fin m, ‖w_in i‖ :=
      mul_le_mul_of_nonneg_left hprod_w (by positivity)
    exact mul_le_mul h1 hfull_int_lb (by positivity) (by positivity)
  have hstep2 : (11 / 10 : ℝ) * (6 * r_m) ≤
      (6 * r_m) * (1 / r_m) ^ m * ((11 / 20 : ℝ) * A ^ m / ((m + 1 : ℕ) : ℝ)) := by
    have hdiv_r : (1 / r_m) ^ m * A ^ m ≥ (5 : ℝ) ^ m := by
      calc (1 / r_m) ^ m * A ^ m ≥ (1 / r_m) ^ m * ((5 : ℝ) ^ m * r_m ^ m) :=
            mul_le_mul_of_nonneg_left hAm_ge (by positivity)
        _ = (5 : ℝ) ^ m * ((1 / r_m) ^ m * r_m ^ m) := by ring
        _ = (5 : ℝ) ^ m * 1 := by rw [← mul_pow, one_div_mul_cancel (ne_of_gt hrm), one_pow]
        _ = (5 : ℝ) ^ m := mul_one _
    have hfrac : (11 / 10 : ℝ) ≤ (11 / 20 : ℝ) * (5 : ℝ) ^ m / ((m + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hm1_pos]
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast] at *
      linarith
    have hEq : (6 * r_m) * (1 / r_m) ^ m * ((11 / 20 : ℝ) * A ^ m / ((m + 1 : ℕ) : ℝ)) =
        (6 * r_m) * ((11 / 20 : ℝ) * ((1 / r_m) ^ m * A ^ m) / ((m + 1 : ℕ) : ℝ)) := by ring
    rw [hEq]
    have hmono : (11 / 20 : ℝ) * (5 : ℝ) ^ m / ((m + 1 : ℕ) : ℝ) ≤
        (11 / 20 : ℝ) * ((1 / r_m) ^ m * A ^ m) / ((m + 1 : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hm1_pos)
      exact mul_le_mul_of_nonneg_left hdiv_r (by norm_num)
    nlinarith
  linarith

/-! ### Section 3: Main Multi-Scale Inner-Cluster Confinement Theorem & Exact `1/n` Corollary -/

/-- **THEOREM 5 (Multi-Scale Inner-Cluster Confinement Theorem — All `n ≥ 2`)**:
    Suppose a nonempty inner cluster `I ⊆ Fin (n - 1)` satisfies:
    - `1 / r_m ≤ ‖w k‖ ≤ 1 / r_1` for all `k ∈ I` (i.e. `r_1 ≤ ‖ζ_k‖ ≤ r_m`),
    - `r_m * ∑ k ∈ Iᶜ, ‖w k‖ ≤ 1 / 36` (constant threshold, independent of `m` and `n`).
    Then there exists an INNER critical point `j ∈ I` satisfying:
      `1 / (r_m / r_1 + ∑ k ∈ I, r_m * ‖w k‖ + 1 / 36) ≤ ‖dualSmaleQuotient n w j‖`. -/
theorem multiscale_inner_cluster_confinement {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (hw : ∀ k, w k ≠ 0)
    (I : Finset (Fin (n - 1))) (hI_ne : I.Nonempty)
    {r₁ r_m : ℝ} (hr₁ : 0 < r₁) (hrm : r₁ ≤ r_m)
    (hI_lo : ∀ k ∈ I, 1 / r_m ≤ ‖w k‖)
    (hI_hi : ∀ k ∈ I, ‖w k‖ ≤ 1 / r₁)
    (hI_gap : r_m * ∑ k ∈ Iᶜ, ‖w k‖ ≤ 1 / 36) :
    ∃ j ∈ I,
      1 / (r_m / r₁ + (∑ k ∈ I, r_m * ‖w k‖) + 1 / 36) ≤ ‖dualSmaleQuotient n w j‖ := by
  have hrm_pos : 0 < r_m := lt_of_lt_of_le hr₁ hrm
  -- All critical points satisfy ‖w k‖ ≤ 1 / r₁ (outer points even satisfy ‖w k‖ ≤ 1 / (36 r_m) < 1 / (6 r_m)!)
  have hout_le : ∀ k ∈ Iᶜ, ‖w k‖ ≤ 1 / (36 * r_m) := by
    intro k hk
    have hsingle : ‖w k‖ ≤ ∑ i ∈ Iᶜ, ‖w i‖ :=
      Finset.single_le_sum (fun i _ => norm_nonneg (w i)) hk
    have hmul : r_m * ‖w k‖ ≤ 1 / 36 := le_trans (mul_le_mul_of_nonneg_left hsingle (le_of_lt hrm_pos)) hI_gap
    rw [le_div_iff₀ (by positivity : 0 < 36 * r_m)]
    linarith
  have hall_hi : ∀ k : Fin (n - 1), ‖w k‖ ≤ 1 / r₁ := by
    intro k
    by_cases hk : k ∈ I
    · exact hI_hi k hk
    · have h1 := hout_le k (Finset.mem_compl.mpr hk)
      have h2 : 1 / (36 * r_m) ≤ 1 / r₁ := one_div_le_one_div_of_le hr₁ (by linarith)
      exact le_trans h1 h2
  -- Set up the harmonic radial comparison function Φ_K on [0, r₁] and confine inside R = 6 r_m!
  set P := polyFromInvCrits n w
  set K : ℝ := r₁ * ∑ k : Fin (n - 1), ‖w k‖
  have hK : 0 ≤ K := mul_nonneg (le_of_lt hr₁) (Finset.sum_nonneg (fun k _ => norm_nonneg _))
  obtain ⟨hΦ0, hΦr₁, hΦ_cont, hΦ_deriv, hφ_pos⟩ := rpow_antideriv_props hr₁ hK
  have hP'_lb : ∀ z : ℂ, ‖z‖ < r₁ → (1 - ‖z‖ / r₁) ^ K ≤ ‖(derivative P).eval z‖ := by
    intro z hz
    calc (1 - ‖z‖ / r₁) ^ K
        ≤ ∏ k : Fin (n - 1), (1 - ‖w k‖ * ‖z‖) :=
          prod_one_sub_ge_rpow w hr₁ hall_hi (norm_nonneg z) hz
      _ ≤ ‖(derivative P).eval z‖ := by
          apply norm_derivative_polyFromInvCrits_ge_prod (by omega) w
          intro k
          calc ‖w k‖ * ‖z‖ ≤ (1 / r₁) * r₁ :=
                mul_le_mul (hall_hi k) (le_of_lt hz) (norm_nonneg z) (by positivity)
            _ = 1 := one_div_mul_cancel (ne_of_gt hr₁)
  have hΦ_lt_R : r₁ / (K + 1) < 6 * r_m := by
    have hle : r₁ / (K + 1) ≤ r₁ := div_le_self (le_of_lt hr₁) (by linarith)
    linarith
  have hcircle : ∀ z : ℂ, ‖z‖ = 6 * r_m → 6 * r_m < ‖P.eval z‖ :=
    fun z hz => circle_lower_bound_of_cluster_gap hn w I hI_ne hrm_pos hI_lo hI_gap hz
  obtain ⟨ζ, hζ_in_R, hζ0, hζv⟩ := radial_lift_confined_critical_value_ge P
    (polyFromInvCrits_eval_zero n w) (derivative_polyFromInvCrits_eval_zero (by omega) w)
    hr₁ (by linarith : r₁ < 6 * r_m) hΦ0 hΦ_cont hΦ_deriv hφ_pos hP'_lb
    (by change (fun r => r₁ / (K + 1) * (1 - (1 - r / r₁) ^ (K + 1))) r₁ < 6 * r_m; rw [hΦr₁]; exact hΦ_lt_R) hcircle
  obtain ⟨j, rfl⟩ := crit_point_eq_inv_w hn w hw hζ0
  -- Because ‖(w j)⁻¹‖ < 6 r_m while every outer point has ‖(w k)⁻¹‖ ≥ 36 r_m, j MUST lie in I!
  have hj_in : j ∈ I := by
    by_contra hj_out
    have h1 := hout_le j (Finset.mem_compl.mpr hj_out)
    have hj_pos : 0 < ‖w j‖ := norm_pos_iff.mpr (hw j)
    have hinv : 36 * r_m ≤ ‖(w j)⁻¹‖ := by
      rw [norm_inv]
      calc 36 * r_m = (1 / (36 * r_m))⁻¹ := by simp
        _ ≤ ‖w j‖⁻¹ := inv_anti₀ hj_pos h1
    linarith
  refine ⟨j, hj_in, ?_⟩
  rw [← polyFromInvCrits_div_eq_quotient (by omega) w j (hw j), norm_div, norm_inv]
  change (fun r => r₁ / (K + 1) * (1 - (1 - r / r₁) ^ (K + 1))) r₁ ≤ _ at hζv
  rw [hΦr₁] at hζv
  -- Since j ∈ I, ‖w j‖⁻¹ ≤ r_m, so ‖P(ζ_j)‖ / ‖ζ_j‖ ≥ (r₁ / (K + 1)) / r_m!
  have hinv_le : ‖w j‖⁻¹ ≤ r_m := by
    have h1 := hI_lo j hj_in
    calc ‖w j‖⁻¹ ≤ (1 / r_m)⁻¹ := inv_anti₀ (by positivity) h1
      _ = r_m := by simp
  have hpos_j : 0 < ‖w j‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (hw j))
  have hsplit_sum : ∑ k : Fin (n - 1), ‖w k‖ = (∑ k ∈ I, ‖w k‖) + ∑ k ∈ Iᶜ, ‖w k‖ :=
    (Finset.sum_add_sum_compl I (fun k => ‖w k‖)).symm
  have hden_le : r_m / r₁ + r_m * ∑ k : Fin (n - 1), ‖w k‖ ≤
      r_m / r₁ + (∑ k ∈ I, r_m * ‖w k‖) + 1 / 36 := by
    rw [hsplit_sum, mul_add, Finset.mul_sum]
    linarith
  have hden_pos : 0 < r_m / r₁ + r_m * ∑ k : Fin (n - 1), ‖w k‖ := by
    have : 0 ≤ ∑ k : Fin (n - 1), ‖w k‖ := Finset.sum_nonneg (fun k _ => norm_nonneg _)
    positivity
  have hEq : (r₁ / (K + 1)) / r_m = 1 / (r_m / r₁ + r_m * ∑ k : Fin (n - 1), ‖w k‖) := by
    dsimp [K]
    field_simp [ne_of_gt hr₁, ne_of_gt hrm_pos, ne_of_gt hden_pos]
    ring
  calc 1 / (r_m / r₁ + (∑ k ∈ I, r_m * ‖w k‖) + 1 / 36)
      ≤ 1 / (r_m / r₁ + r_m * ∑ k : Fin (n - 1), ‖w k‖) := one_div_le_one_div_of_le hden_pos hden_le
    _ = (r₁ / (K + 1)) / r_m := hEq.symm
    _ ≤ ‖P.eval (w j)⁻¹‖ / ‖w j‖⁻¹ := div_le_div₀ (norm_nonneg _) hζv hpos_j hinv_le

/-- **COROLLARY 5.1 (Exact Dual Smale Conjecture `≥ 1/n` for Isolated Equal-Modulus Inner Clusters)**:
    If a nonempty inner cluster `I ⊆ Fin (n - 1)` of size `m = I.card ≤ n - 2` lies on a circle
    `‖ζ_k‖ = R` (`‖w k‖ = 1 / R` for all `k ∈ I`) and is separated from the outer critical points
    by `R * ∑_{k ∉ I} ‖w k‖ ≤ 1 / 36`, then the **exact Dual Smale Conjecture** holds:
    `∃ j ∈ I, 1 / n ≤ ‖dualSmaleQuotient n w j‖`! -/
theorem multiscale_exact_dual_smale_cluster {n : ℕ} (hn : 3 ≤ n) (w : Fin (n - 1) → ℂ)
    (hw : ∀ k, w k ≠ 0)
    (I : Finset (Fin (n - 1))) (hI_ne : I.Nonempty) (hI_card : I.card ≤ n - 2)
    {R : ℝ} (hR : 0 < R)
    (hI_eq : ∀ k ∈ I, ‖w k‖ = 1 / R)
    (hI_gap : R * ∑ k ∈ Iᶜ, ‖w k‖ ≤ 1 / 36) :
    ∃ j ∈ I, 1 / (n : ℝ) ≤ ‖dualSmaleQuotient n w j‖ := by
  obtain ⟨j, hjI, hj⟩ := multiscale_inner_cluster_confinement (by omega) w hw I hI_ne hR le_rfl
    (fun k hk => le_of_eq (hI_eq k hk).symm) (fun k hk => le_of_eq (hI_eq k hk)) hI_gap
  refine ⟨j, hjI, le_trans ?_ hj⟩
  have hsum : ∑ k ∈ I, R * ‖w k‖ = (I.card : ℝ) := by
    have h1 : ∀ k ∈ I, R * ‖w k‖ = 1 := fun k hk => by rw [hI_eq k hk]; exact mul_one_div_cancel (ne_of_gt hR)
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [div_self (ne_of_gt hR), hsum]
  have hcard_le : (I.card : ℝ) ≤ (n : ℝ) - 2 := by
    have : I.card + 2 ≤ n := by omega
    have hcast : (I.card : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  have hpos : 0 < 1 + (I.card : ℝ) + 1 / 36 := by positivity
  exact one_div_le_one_div_of_le hpos (by linarith)

end DualSmaleMultiscale
