/-
  DualSmaleMultiscale/RadialLift.lean

  Self-contained Lean 4 radial-lift continuation engine for complex polynomials.
  Given P ∈ ℂ[X] with P(0) = 0, P'(0) = 1, and a C^1 radial comparison function
  Φ : [0, r₁] → ℝ with Φ(0) = 0, Φ'(r) > 0 on [0, r₁), and Φ'(‖z‖) ≤ ‖P'(z)‖
  for all ‖z‖ < r₁, we prove BOTH:

  1. `radial_lift_critical_value_ge` (Global):
     For deg P ≥ 2, there exists a critical point ζ of P with Φ(r₁) ≤ ‖P(ζ)‖.
  2. `radial_lift_confined_critical_value_ge` (Confined to a disk D(0, R)):
     If R > r₁, Φ(r₁) < R, and R < ‖P(z)‖ on ‖z‖ = R, then there exists a
     critical point ζ with ‖ζ‖ < R and Φ(r₁) ≤ ‖P(ζ)‖.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open scoped BigOperators
open Polynomial Complex

namespace DualSmaleMultiscale

/-! ### Section 1: Polynomial Taylor bound and elementary calculus helpers -/

/-- Second-order Taylor bound for a complex polynomial on a bounded ball:
    there exists `C > 0` such that for all `‖z‖ ≤ R` and `‖h‖ ≤ 1`,
    `‖P(z + h) - P(z) - P'(z) * h‖ ≤ C * ‖h‖^2`. -/
lemma poly_taylor_bound (P : ℂ[X]) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ z h : ℂ, ‖z‖ ≤ R → ‖h‖ ≤ 1 →
      ‖P.eval (z + h) - P.eval z - (derivative P).eval z * h‖ ≤ C * ‖h‖ ^ 2 := by
  induction P using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rcases ihp with ⟨Cp, hCp, hp⟩
    rcases ihq with ⟨Cq, hCq, hq⟩
    refine ⟨Cp + Cq, by linarith, fun z h hz hh => ?_⟩
    have hEq : (p + q).eval (z + h) - (p + q).eval z - (derivative (p + q)).eval z * h =
        (p.eval (z + h) - p.eval z - (derivative p).eval z * h) +
        (q.eval (z + h) - q.eval z - (derivative q).eval z * h) := by
      simp [derivative_add, eval_add]; ring
    rw [hEq]
    calc ‖(p.eval (z + h) - p.eval z - (derivative p).eval z * h) +
          (q.eval (z + h) - q.eval z - (derivative q).eval z * h)‖
        ≤ ‖p.eval (z + h) - p.eval z - (derivative p).eval z * h‖ +
          ‖q.eval (z + h) - q.eval z - (derivative q).eval z * h‖ := norm_add_le _ _
      _ ≤ Cp * ‖h‖ ^ 2 + Cq * ‖h‖ ^ 2 := add_le_add (hp z h hz hh) (hq z h hz hh)
      _ = (Cp + Cq) * ‖h‖ ^ 2 := by ring
  | monomial n a =>
    cases n with
    | zero =>
      refine ⟨1, one_pos, fun z h _ _ => ?_⟩
      simp [derivative_C]
    | succ k =>
      cases k with
      | zero =>
        refine ⟨1, one_pos, fun z h _ _ => ?_⟩
        simp only [Polynomial.derivative_monomial, Polynomial.eval_monomial, zero_add,
          Nat.cast_one, one_mul, pow_zero, pow_one, mul_one, Nat.sub_self]
        have h0 : a * (z + h) - a * z - a * h = 0 := by ring
        rw [h0, norm_zero]
        positivity
      | succ m =>
        set C0 : ℝ := ‖a‖ * (R + 1) ^ m * (2 : ℝ) ^ (m + 2) + 1
        refine ⟨C0, by positivity, fun z h hz hh => ?_⟩
        have hbin : (z + h) ^ (m + 2) - z ^ (m + 2) - ((m + 2 : ℕ) : ℂ) * z ^ (m + 1) * h =
            h ^ 2 * ∑ j ∈ Finset.range (m + 1),
              ((Nat.choose (m + 2) (j + 2) : ℕ) : ℂ) * z ^ (m - j) * h ^ j := by
          have hexp : (z + h) ^ (m + 2) =
              ∑ j ∈ Finset.range (m + 3),
                ((Nat.choose (m + 2) j : ℕ) : ℂ) * h ^ j * z ^ (m + 2 - j) := by
            rw [add_comm, add_pow]
            apply Finset.sum_congr rfl; intro j _; ring
          rw [hexp, Finset.sum_range_succ', Finset.sum_range_succ']
          simp only [zero_add, Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one,
            Nat.sub_zero, Nat.cast_one, one_mul, mul_one]
          have hsub1 : m + 2 - 1 = m + 1 := by omega
          rw [hsub1]
          have htail : ∑ x ∈ Finset.range (m + 1),
              ((Nat.choose (m + 2) (x + 1 + 1) : ℕ) : ℂ) * h ^ (x + 1 + 1) * z ^ (m + 2 - (x + 1 + 1)) =
              h ^ 2 * ∑ j ∈ Finset.range (m + 1),
                ((Nat.choose (m + 2) (j + 2) : ℕ) : ℂ) * z ^ (m - j) * h ^ j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j _
            have hsub : m + 2 - (j + 1 + 1) = m - j := by omega
            rw [hsub]
            have hpow : h ^ (j + 1 + 1) = h ^ 2 * h ^ j := by ring
            rw [hpow]; ring
          rw [htail]; ring
        have hval : (Polynomial.monomial (m + 2) a).eval (z + h) -
            (Polynomial.monomial (m + 2) a).eval z -
            (derivative (Polynomial.monomial (m + 2) a)).eval z * h =
            a * ((z + h) ^ (m + 2) - z ^ (m + 2) - ((m + 2 : ℕ) : ℂ) * z ^ (m + 1) * h) := by
          rw [Polynomial.derivative_monomial]
          simp only [Polynomial.eval_monomial]
          push_cast; ring
        rw [hval, hbin, norm_mul, norm_mul, norm_pow]
        have hsum_le : ‖∑ j ∈ Finset.range (m + 1),
            ((Nat.choose (m + 2) (j + 2) : ℕ) : ℂ) * z ^ (m - j) * h ^ j‖ ≤
            (R + 1) ^ m * (2 : ℝ) ^ (m + 2) := by
          calc ‖∑ j ∈ Finset.range (m + 1),
                ((Nat.choose (m + 2) (j + 2) : ℕ) : ℂ) * z ^ (m - j) * h ^ j‖
              ≤ ∑ j ∈ Finset.range (m + 1),
                  ‖((Nat.choose (m + 2) (j + 2) : ℕ) : ℂ) * z ^ (m - j) * h ^ j‖ := norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.range (m + 1),
                  (Nat.choose (m + 2) (j + 2) : ℝ) * (R + 1) ^ m := by
                apply Finset.sum_le_sum; intro j _
                rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, norm_pow]
                have hzn : ‖z‖ ^ (m - j) ≤ (R + 1) ^ m := by
                  have h1 : ‖z‖ ≤ R + 1 := by linarith
                  have h2 : ‖z‖ ^ (m - j) ≤ (R + 1) ^ (m - j) := pow_le_pow_left₀ (norm_nonneg z) h1 _
                  have h3 : (R + 1) ^ (m - j) ≤ (R + 1) ^ m :=
                    pow_le_pow_right₀ (by linarith) (Nat.sub_le m j)
                  exact le_trans h2 h3
                have hhn : ‖h‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg h) hh
                calc (Nat.choose (m + 2) (j + 2) : ℝ) * ‖z‖ ^ (m - j) * ‖h‖ ^ j
                    ≤ (Nat.choose (m + 2) (j + 2) : ℝ) * (R + 1) ^ m * 1 := by gcongr
                  _ = (Nat.choose (m + 2) (j + 2) : ℝ) * (R + 1) ^ m := mul_one _
            _ = (R + 1) ^ m * ∑ j ∈ Finset.range (m + 1), (Nat.choose (m + 2) (j + 2) : ℝ) := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
            _ ≤ (R + 1) ^ m * (2 : ℝ) ^ (m + 2) := by
                gcongr
                have hsub : ∑ j ∈ Finset.range (m + 1), Nat.choose (m + 2) (j + 2) ≤
                    ∑ j ∈ Finset.range (m + 3), Nat.choose (m + 2) j := by
                  have h1 : ∑ j ∈ Finset.range (m + 3), Nat.choose (m + 2) j =
                      (∑ j ∈ Finset.range (m + 1), Nat.choose (m + 2) (j + 2)) +
                        Nat.choose (m + 2) 1 + Nat.choose (m + 2) 0 := by
                    rw [Finset.sum_range_succ' (fun j => Nat.choose (m + 2) j) (m + 2),
                        Finset.sum_range_succ' (fun j => Nat.choose (m + 2) (j + 1)) (m + 1)]
                  omega
                have h2 := Nat.sum_range_choose (m + 2)
                exact_mod_cast le_trans hsub (le_of_eq h2)
        have hstep : ‖a‖ * (‖h‖ ^ 2 * ‖∑ j ∈ Finset.range (m + 1),
            ((Nat.choose (m + 2) (j + 2) : ℕ) : ℂ) * z ^ (m - j) * h ^ j‖) ≤
            (‖a‖ * ((R + 1) ^ m * (2 : ℝ) ^ (m + 2))) * ‖h‖ ^ 2 := by
          have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_le (sq_nonneg ‖h‖)) (norm_nonneg a)
          linarith
        have hC0 : ‖a‖ * ((R + 1) ^ m * (2 : ℝ) ^ (m + 2)) ≤ C0 := by dsimp [C0]; linarith
        nlinarith [sq_nonneg ‖h‖]

/-- Derivative of `t ↦ ‖γ t‖` for a complex-valued curve at a nonzero point. -/
lemma hasDerivAt_norm_complex {γ : ℝ → ℂ} {v : ℂ} {s : ℝ}
    (hγ : HasDerivAt γ v s) (hne : γ s ≠ 0) :
    HasDerivAt (fun t => ‖γ t‖) (((γ s).re * v.re + (γ s).im * v.im) / ‖γ s‖) s := by
  have hre : HasDerivAt (fun t => (γ t).re) v.re s :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hγ
  have him : HasDerivAt (fun t => (γ t).im) v.im s :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hγ
  have hsq : HasDerivAt (fun t => (γ t).re ^ 2 + (γ t).im ^ 2)
      (2 * (γ s).re * v.re + 2 * (γ s).im * v.im) s := by
    have h1 := hre.pow 2
    have h2 := him.pow 2
    convert h1.add h2 using 1
    ring
  have hns_pos : (γ s).re ^ 2 + (γ s).im ^ 2 ≠ 0 := by
    have h := Complex.normSq_pos.mpr hne
    rw [Complex.normSq_apply] at h
    nlinarith
  have hsqrt := (Real.hasDerivAt_sqrt hns_pos).comp s hsq
  have hfun : (fun t => Real.sqrt ((γ t).re ^ 2 + (γ t).im ^ 2)) = (fun t => ‖γ t‖) := by
    ext t
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1; ring
  rw [show (Real.sqrt ∘ fun t => (γ t).re ^ 2 + (γ t).im ^ 2) = (fun t => ‖γ t‖) from hfun] at hsqrt
  have hnorm_eq : Real.sqrt ((γ s).re ^ 2 + (γ s).im ^ 2) = ‖γ s‖ := congrFun hfun s
  rw [hnorm_eq] at hsqrt
  convert hsqrt using 1
  have hn0 : ‖γ s‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  field_simp [hn0]

/-- 2D Cauchy-Schwarz inequality: `(z.re * v.re + z.im * v.im) / ‖z‖ ≤ ‖v‖`. -/
lemma re_im_dot_div_norm_le {z v : ℂ} (hz : z ≠ 0) :
    (z.re * v.re + z.im * v.im) / ‖z‖ ≤ ‖v‖ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [div_le_iff₀ hzn]
  have hsq : (z.re * v.re + z.im * v.im) ^ 2 ≤ (‖v‖ * ‖z‖) ^ 2 := by
    have hz2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have hv2 : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [mul_pow, hz2, hv2]
    nlinarith [sq_nonneg (z.re * v.im - z.im * v.re)]
  have hnn : 0 ≤ ‖v‖ * ‖z‖ := mul_nonneg (norm_nonneg v) (le_of_lt hzn)
  nlinarith

/-! ### Section 2: Key A Priori Radial Bound along a Lifted Segment -/

/-- Along a C^1 radial lift `P(γ s) = s * w` staying inside `‖γ s‖ < r₁`,
    if `Φ ‖γ a‖ ≤ a * ‖w‖` and `Φ'(r) ≤ ‖P'(z)‖` for `‖z‖ = r < r₁`, then
    `Φ ‖γ s‖ ≤ s * ‖w‖` on the entire interval `[a, b]`. -/
lemma phi_norm_le_along_lift (P : ℂ[X]) {r₁ : ℝ} {Φ φ : ℝ → ℝ}
    (hΦ0 : Φ 0 = 0)
    (hΦ_deriv : ∀ r ∈ Set.Ico 0 r₁, HasDerivAt Φ (φ r) r)
    (hφ_pos : ∀ r ∈ Set.Ico 0 r₁, 0 < φ r)
    (hP'_lb : ∀ z : ℂ, ‖z‖ < r₁ → φ ‖z‖ ≤ ‖(derivative P).eval z‖)
    {w : ℂ} {γ : ℝ → ℂ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hderiv : ∀ s ∈ Set.Ioo a b, HasDerivAt γ (w / (derivative P).eval (γ s)) s)
    (hball : ∀ s ∈ Set.Icc a b, ‖γ s‖ < r₁)
    (hstart : Φ ‖γ a‖ ≤ a * ‖w‖) :
    ∀ t ∈ Set.Icc a b, Φ ‖γ t‖ ≤ t * ‖w‖ := by
  intro t ht
  by_cases hγt : γ t = 0
  · rw [hγt, norm_zero, hΦ0]
    exact mul_nonneg (le_trans ha ht.1) (norm_nonneg w)
  · set g : ℝ → ℝ := fun s => Φ ‖γ s‖ - s * ‖w‖
    set Z : Set ℝ := {s ∈ Set.Icc a t | γ s = 0}
    have hstep : ∀ c ∈ Set.Icc a t, (∀ s ∈ Set.Ioo c t, γ s ≠ 0) → g c ≤ 0 → g t ≤ 0 := by
      intro c hc hnz hgc
      have hct : c ≤ t := hc.2
      have hsub_ct : Set.Icc c t ⊆ Set.Icc a b := fun s hs => ⟨le_trans hc.1 hs.1, le_trans hs.2 ht.2⟩
      have hΦ_cont_on : ContinuousOn (fun s => Φ ‖γ s‖) (Set.Icc c t) := by
        intro s hs
        have hns : ‖γ s‖ ∈ Set.Ico 0 r₁ := ⟨norm_nonneg _, hball s (hsub_ct hs)⟩
        have hΦc : ContinuousAt Φ ‖γ s‖ := (hΦ_deriv _ hns).continuousAt
        have hnc : ContinuousWithinAt (fun x => ‖γ x‖) (Set.Icc c t) s :=
          ContinuousWithinAt.norm (hcont.mono hsub_ct s hs)
        exact ContinuousAt.comp_continuousWithinAt (g := Φ) hΦc hnc
      have hg_cont : ContinuousOn g (Set.Icc c t) :=
        hΦ_cont_on.sub (continuousOn_id.mul continuousOn_const)
      have hanti : AntitoneOn g (Set.Icc c t) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc c t) hg_cont
        · intro s hs
          rw [interior_Icc] at hs
          have hs_ab : s ∈ Set.Ioo a b := ⟨lt_of_le_of_lt hc.1 hs.1, lt_of_lt_of_le hs.2 ht.2⟩
          have hγs_ne : γ s ≠ 0 := hnz s hs
          have hγs_lt : ‖γ s‖ < r₁ := hball s (Set.Ioo_subset_Icc_self hs_ab)
          have hγs_d : HasDerivAt γ (w / (derivative P).eval (γ s)) s := hderiv s hs_ab
          have hnorm_d := hasDerivAt_norm_complex hγs_d hγs_ne
          have hΦ_d := (hΦ_deriv ‖γ s‖ ⟨norm_nonneg _, hγs_lt⟩).comp s hnorm_d
          have hlin_d : HasDerivAt (fun x : ℝ => x * ‖w‖) ‖w‖ s := by
            simpa using (hasDerivAt_id s).mul_const ‖w‖
          exact (hΦ_d.sub hlin_d).hasDerivWithinAt
        · intro s hs
          rw [interior_Icc] at hs
          have hs_ab : s ∈ Set.Ioo a b := ⟨lt_of_le_of_lt hc.1 hs.1, lt_of_lt_of_le hs.2 ht.2⟩
          have hγs_ne : γ s ≠ 0 := hnz s hs
          have hγs_lt : ‖γ s‖ < r₁ := hball s (Set.Ioo_subset_Icc_self hs_ab)
          have hφ_p : 0 < φ ‖γ s‖ := hφ_pos ‖γ s‖ ⟨norm_nonneg _, hγs_lt⟩
          have hP'_ge : φ ‖γ s‖ ≤ ‖(derivative P).eval (γ s)‖ := hP'_lb (γ s) hγs_lt
          have hP'_pos : 0 < ‖(derivative P).eval (γ s)‖ := lt_of_lt_of_le hφ_p hP'_ge
          have hcs : ((γ s).re * (w / (derivative P).eval (γ s)).re +
              (γ s).im * (w / (derivative P).eval (γ s)).im) / ‖γ s‖ ≤
              ‖w / (derivative P).eval (γ s)‖ := re_im_dot_div_norm_le hγs_ne
          have hbound : φ ‖γ s‖ * (((γ s).re * (w / (derivative P).eval (γ s)).re +
              (γ s).im * (w / (derivative P).eval (γ s)).im) / ‖γ s‖) ≤ ‖w‖ := by
            calc φ ‖γ s‖ * (((γ s).re * (w / (derivative P).eval (γ s)).re +
                    (γ s).im * (w / (derivative P).eval (γ s)).im) / ‖γ s‖)
                ≤ φ ‖γ s‖ * ‖w / (derivative P).eval (γ s)‖ :=
                  mul_le_mul_of_nonneg_left hcs (le_of_lt hφ_p)
              _ = φ ‖γ s‖ * (‖w‖ / ‖(derivative P).eval (γ s)‖) := by rw [norm_div]
              _ = (φ ‖γ s‖ / ‖(derivative P).eval (γ s)‖) * ‖w‖ := by ring
              _ ≤ 1 * ‖w‖ := by
                  apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
                  rw [div_le_one hP'_pos]; exact hP'_ge
              _ = ‖w‖ := one_mul _
          linarith
      have hle := hanti ⟨le_rfl, hct⟩ ⟨hct, le_rfl⟩ hct
      linarith
    by_cases hZ : Z.Nonempty
    · have hZ_closed : IsClosed Z := by
        have hsub : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc_right ht.2
        exact (hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
      have hZ_comp : IsCompact Z := isCompact_Icc.of_isClosed_subset hZ_closed (fun s hs => hs.1)
      obtain ⟨s₀, hs₀Z, hs₀max⟩ := hZ_comp.exists_isMaxOn hZ continuousOn_id
      have hnz : ∀ s ∈ Set.Ioo s₀ t, γ s ≠ 0 := by
        intro s hs h0
        have hsZ : s ∈ Z := ⟨⟨le_trans hs₀Z.1.1 (le_of_lt hs.1), le_of_lt hs.2⟩, h0⟩
        have hle : s ≤ s₀ := hs₀max hsZ
        linarith [hs.1]
      have hgs₀ : g s₀ ≤ 0 := by
        dsimp [g]; rw [hs₀Z.2, norm_zero, hΦ0]
        have hs₀_nn : 0 ≤ s₀ := le_trans ha hs₀Z.1.1
        nlinarith [norm_nonneg w]
      have hgt := hstep s₀ hs₀Z.1 hnz hgs₀
      dsimp [g] at hgt; linarith
    · rw [Set.not_nonempty_iff_eq_empty] at hZ
      have hnz : ∀ s ∈ Set.Ioo a t, γ s ≠ 0 := by
        intro s hs h0
        have hsZ : s ∈ Z := ⟨Set.Ioo_subset_Icc_self hs, h0⟩
        rw [hZ] at hsZ; exact hsZ
      have hga : g a ≤ 0 := by dsimp [g]; linarith
      have hgt := hstep a ⟨le_rfl, ht.1⟩ hnz hga
      dsimp [g] at hgt; linarith

/-! ### Section 3: Local Uniqueness & Differentiability of Radial Lifts -/

/-- Two continuous lifts of the same ray `[0, t] ↦ s * w` starting at `0` and avoiding
    critical points must agree identically on `[0, t]`. -/
lemma lift_unique (P : ℂ[X]) {w : ℂ} {t : ℝ} (ht : 0 ≤ t) {γ₁ γ₂ : ℝ → ℂ}
    (hc₁ : ContinuousOn γ₁ (Set.Icc 0 t)) (hc₂ : ContinuousOn γ₂ (Set.Icc 0 t))
    (h0₁ : γ₁ 0 = 0) (h0₂ : γ₂ 0 = 0)
    (hP₁ : ∀ s ∈ Set.Icc 0 t, P.eval (γ₁ s) = (s : ℂ) * w)
    (hP₂ : ∀ s ∈ Set.Icc 0 t, P.eval (γ₂ s) = (s : ℂ) * w)
    (hnd₁ : ∀ s ∈ Set.Icc 0 t, (derivative P).eval (γ₁ s) ≠ 0) :
    ∀ s ∈ Set.Icc 0 t, γ₁ s = γ₂ s := by
  set E : Set ℝ := {s ∈ Set.Icc 0 t | γ₁ s = γ₂ s}
  have hE_closed : IsClosed E := by
    have hdiff : ContinuousOn (fun s => γ₁ s - γ₂ s) (Set.Icc 0 t) := hc₁.sub hc₂
    have h1 : IsClosed (Set.Icc 0 t ∩ (fun s => γ₁ s - γ₂ s) ⁻¹' {(0 : ℂ)}) :=
      hdiff.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    convert h1 using 1
    ext s; simp [E, sub_eq_zero]
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨s₁, hs₁, hne₁⟩
  set E₁ : Set ℝ := E ∩ Set.Icc 0 s₁
  have hE₁_ne : E₁.Nonempty := ⟨0, ⟨⟨le_rfl, ht⟩, by rw [h0₁, h0₂]⟩, ⟨le_rfl, hs₁.1⟩⟩
  have hE₁_comp : IsCompact E₁ :=
    isCompact_Icc.of_isClosed_subset (hE_closed.inter isClosed_Icc) (fun _ h => h.2)
  obtain ⟨s₀, hs₀, hs₀_max⟩ := hE₁_comp.exists_isMaxOn hE₁_ne continuousOn_id
  have hs₀_lt : s₀ < s₁ := lt_of_le_of_ne hs₀.2.2 (fun heq => hne₁ (heq ▸ hs₀.1.2))
  set z₀ := γ₁ s₀
  have hP'z₀ : (derivative P).eval z₀ ≠ 0 := hnd₁ s₀ hs₀.1.1
  have hsd : HasStrictDerivAt (fun z => P.eval z) ((derivative P).eval z₀) z₀ := P.hasStrictDerivAt z₀
  have hli := hsd.eventually_left_inverse hP'z₀
  rw [Metric.eventually_nhds_iff] at hli
  rcases hli with ⟨ρ, hρ_pos, hρ⟩
  have h1c : ContinuousWithinAt γ₁ (Set.Icc 0 t) s₀ := hc₁ s₀ hs₀.1.1
  have h2c : ContinuousWithinAt γ₂ (Set.Icc 0 t) s₀ := hc₂ s₀ hs₀.1.1
  have hev1 : ∀ᶠ s in nhdsWithin s₀ (Set.Icc 0 t), dist (γ₁ s) z₀ < ρ :=
    h1c.eventually (Metric.ball_mem_nhds z₀ hρ_pos)
  have hev2 : ∀ᶠ s in nhdsWithin s₀ (Set.Icc 0 t), dist (γ₂ s) z₀ < ρ := by
    have : γ₂ s₀ = z₀ := hs₀.1.2.symm
    rw [← this]
    exact h2c.eventually (Metric.ball_mem_nhds (γ₂ s₀) hρ_pos)
  have hev12 := hev1.and hev2
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev12
  rcases hev12 with ⟨δ, hδ_pos, hδ⟩
  set s' := min s₁ (s₀ + δ / 2)
  have hs'_gt : s₀ < s' := lt_min hs₀_lt (by linarith)
  have hs'_mem : s' ∈ Set.Icc 0 t := ⟨le_trans hs₀.1.1.1 (le_of_lt hs'_gt), le_trans (min_le_left _ _) hs₁.2⟩
  have hs'_dist : dist s' s₀ < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hs'_gt)]
    linarith [min_le_right s₁ (s₀ + δ / 2)]
  have ⟨hd1, hd2⟩ := hδ hs'_dist hs'_mem
  have hinv1 := hρ hd1
  have hinv2 := hρ hd2
  have hPeq : P.eval (γ₁ s') = P.eval (γ₂ s') := by rw [hP₁ s' hs'_mem, hP₂ s' hs'_mem]
  have heq_s' : γ₁ s' = γ₂ s' := by rw [← hinv1, hPeq, hinv2]
  have hs'_in : s' ∈ E₁ := ⟨⟨hs'_mem, heq_s'⟩, ⟨hs'_mem.1, min_le_left _ _⟩⟩
  have hle : s' ≤ s₀ := hs₀_max hs'_in
  linarith

/-- If a continuous curve `γ` lifts `P(γ s) = s * w` near `s` and `P'(γ s) ≠ 0`,
    then `γ` is differentiable at `s` with `γ'(s) = w / P'(γ s)`. -/
lemma hasDerivAt_of_lift (P : ℂ[X]) {w : ℂ} {s : ℝ} {γ : ℝ → ℂ}
    (hcont : ContinuousAt γ s)
    (hev : ∀ᶠ u in nhds s, P.eval (γ u) = (u : ℂ) * w)
    (hnd : (derivative P).eval (γ s) ≠ 0) :
    HasDerivAt γ (w / (derivative P).eval (γ s)) s := by
  set z₀ := γ s
  have hsd : HasStrictDerivAt (fun z => P.eval z) ((derivative P).eval z₀) z₀ := P.hasStrictDerivAt z₀
  have hli := hsd.eventually_left_inverse hnd
  have hγ_li : ∀ᶠ u in nhds s,
      hsd.localInverse (fun z => P.eval z) ((derivative P).eval z₀) z₀ hnd (P.eval (γ u)) = γ u :=
    hcont.eventually hli
  have heq_ev : ∀ᶠ u in nhds s,
      γ u = hsd.localInverse (fun z => P.eval z) ((derivative P).eval z₀) z₀ hnd ((u : ℂ) * w) := by
    filter_upwards [hγ_li, hev] with u h1 h2
    rw [← h2, h1]
  have hloc_d : HasStrictDerivAt
      (hsd.localInverse (fun z => P.eval z) ((derivative P).eval z₀) z₀ hnd)
      (((derivative P).eval z₀)⁻¹) (P.eval z₀) := hsd.to_localInverse hnd
  have hPs : P.eval z₀ = (s : ℂ) * w := hev.self_of_nhds
  rw [hPs] at hloc_d
  have hray : HasDerivAt (fun u : ℝ => (u : ℂ) * w) w s := by
    have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
    simpa using h1.mul_const w
  have hcomp : HasDerivAt
      (fun u : ℝ => hsd.localInverse (fun z => P.eval z) ((derivative P).eval z₀) z₀ hnd ((u : ℂ) * w))
      (((derivative P).eval z₀)⁻¹ * w) s :=
    hloc_d.hasDerivAt.comp s hray
  have hfinal := hcomp.congr_of_eventuallyEq heq_ev
  convert hfinal using 1
  ring

/-- If `g : ℂ → ℂ` is continuous at `w₀`, satisfies `P(g w) = w` near `w₀`, and `P'(g w₀) ≠ 0`,
    then `g` is complex-differentiable at `w₀` with derivative `(P'(g w₀))⁻¹`. -/
lemma hasDerivAt_of_rightInverse (P : ℂ[X]) {g : ℂ → ℂ} {w₀ : ℂ}
    (hcont : ContinuousAt g w₀)
    (hev : ∀ᶠ w in nhds w₀, P.eval (g w) = w)
    (hnd : (derivative P).eval (g w₀) ≠ 0) :
    HasDerivAt g (((derivative P).eval (g w₀))⁻¹) w₀ := by
  set z₀ := g w₀
  have hsd : HasStrictDerivAt (fun z => P.eval z) ((derivative P).eval z₀) z₀ := P.hasStrictDerivAt z₀
  have hli := hsd.eventually_left_inverse hnd
  have hg_li : ∀ᶠ w in nhds w₀,
      hsd.localInverse (fun z => P.eval z) ((derivative P).eval z₀) z₀ hnd (P.eval (g w)) = g w :=
    hcont.eventually hli
  have heq_ev : ∀ᶠ w in nhds w₀,
      g w = hsd.localInverse (fun z => P.eval z) ((derivative P).eval z₀) z₀ hnd w := by
    filter_upwards [hg_li, hev] with w h1 h2
    calc g w = hsd.localInverse (fun z => P.eval z) ((derivative P).eval z₀) z₀ hnd (P.eval (g w)) := h1.symm
      _ = hsd.localInverse (fun z => P.eval z) ((derivative P).eval z₀) z₀ hnd w := by rw [h2]
  have hloc_d : HasStrictDerivAt
      (hsd.localInverse (fun z => P.eval z) ((derivative P).eval z₀) z₀ hnd)
      (((derivative P).eval z₀)⁻¹) (P.eval z₀) := hsd.to_localInverse hnd
  have hPw₀ : P.eval z₀ = w₀ := hev.self_of_nhds
  rw [hPw₀] at hloc_d
  have h1 : HasDerivAt (hsd.localInverse (fun z => P.eval z) ((derivative P).eval z₀) z₀ hnd)
      (((derivative P).eval z₀)⁻¹) w₀ := hloc_d.hasDerivAt
  exact h1.congr_of_eventuallyEq heq_ev

/-! ### Section 4: Master Unified Radial-Lift Obstruction Theorem -/

/-- **Unified Radial-Lift Obstruction Theorem**:
    Let `P ∈ ℂ[X]` satisfy `P(0) = 0`, `P'(0) = 1`, and suppose on an open set `U ⊇ ball 0 r₁`:
    - `Φ : [0, r₁] → ℝ` is continuous on `[0, r₁]`, differentiable on `[0, r₁)` with derivative `φ > 0`,
      `Φ 0 = 0`, and `φ ‖z‖ ≤ ‖P'(z)‖` for all `‖z‖ < r₁`.
    - `L_max > Φ r₁` and `0 < M_bound < L_max` satisfy:
      `closedBall 0 M_bound ⊆ U` and `∀ z ∈ U, ‖P z‖ < L_max → ‖z‖ ≤ M_bound`.
    Then there MUST exist a critical point `ζ ∈ U` of `P` with `Φ r₁ ≤ ‖P.eval ζ‖`! -/
theorem radial_lift_obstruction (P : ℂ[X])
    (hP0 : P.eval 0 = 0) (hP'0 : (derivative P).eval 0 = 1)
    {r₁ : ℝ} (hr₁ : 0 < r₁)
    {Φ φ : ℝ → ℝ} (hΦ0 : Φ 0 = 0)
    (hΦ_cont : ContinuousOn Φ (Set.Icc 0 r₁))
    (hΦ_deriv : ∀ r ∈ Set.Ico 0 r₁, HasDerivAt Φ (φ r) r)
    (hφ_pos : ∀ r ∈ Set.Ico 0 r₁, 0 < φ r)
    (hP'_lb : ∀ z : ℂ, ‖z‖ < r₁ → φ ‖z‖ ≤ ‖(derivative P).eval z‖)
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ball : Metric.ball 0 r₁ ⊆ U)
    {L_max M_bound : ℝ} (hL_gt : Φ r₁ < L_max) (hM_pos : 0 < M_bound) (hM_lt : M_bound < L_max)
    (hK_sub : Metric.closedBall 0 M_bound ⊆ U)
    (hPre_bound : ∀ z ∈ U, ‖P.eval z‖ < L_max → ‖z‖ ≤ M_bound) :
    ∃ ζ ∈ U, (derivative P).eval ζ = 0 ∧ Φ r₁ ≤ ‖P.eval ζ‖ := by
  have hΦ_strict : StrictMonoOn Φ (Set.Icc 0 r₁) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 r₁) hΦ_cont
    intro r hr
    rw [interior_Icc] at hr
    rw [(hΦ_deriv r ⟨le_of_lt hr.1, hr.2⟩).deriv]
    exact hφ_pos r ⟨le_of_lt hr.1, hr.2⟩
  have hΦr₁_pos : 0 < Φ r₁ := by
    have := hΦ_strict ⟨le_rfl, le_of_lt hr₁⟩ ⟨le_of_lt hr₁, le_rfl⟩ hr₁
    linarith
  have hL_pos : 0 < L_max := lt_trans hΦr₁_pos hL_gt
  have hP'ne : derivative P ≠ 0 := by intro h0; rw [h0, eval_zero] at hP'0; exact zero_ne_one hP'0
  -- Assume for contradiction that every critical point in U has ‖P(ζ)‖ < Φ r₁
  by_contra hno
  push Not at hno
  -- Step 1: Separate critical values in U from Φ r₁ by L_gap ∈ (M_crit, Φ r₁)
  have hex_gap : ∃ L_gap : ℝ, 0 < L_gap ∧ L_gap < Φ r₁ ∧
      ∀ ζ ∈ U, (derivative P).eval ζ = 0 → ‖P.eval ζ‖ < L_gap := by
    classical
    set S_roots : Finset ℂ := (derivative P).roots.toFinset.filter (fun ζ => ζ ∈ U)
    by_cases hne : S_roots.Nonempty
    · set M_c : ℝ := S_roots.sup' hne (fun ζ => ‖P.eval ζ‖)
      have hMc_lt : M_c < Φ r₁ := by
        rw [Finset.sup'_lt_iff]
        intro ζ hζ
        simp only [S_roots, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hP'ne] at hζ
        exact hno ζ hζ.2 hζ.1
      have hMc_nn : 0 ≤ M_c := by
        obtain ⟨ζ₀, hζ₀⟩ := hne
        exact le_trans (norm_nonneg _) (Finset.le_sup' (fun ζ => ‖P.eval ζ‖) hζ₀)
      refine ⟨(M_c + Φ r₁) / 2, by linarith, by linarith, fun ζ hζU hζ0 => ?_⟩
      have hmem : ζ ∈ S_roots := by
        simp only [S_roots, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hP'ne]
        exact ⟨hζ0, hζU⟩
      have hle : ‖P.eval ζ‖ ≤ M_c := Finset.le_sup' (fun z => ‖P.eval z‖) hmem
      linarith
    · refine ⟨Φ r₁ / 2, by linarith, by linarith, fun ζ hζU hζ0 => ?_⟩
      have hmem : ζ ∈ S_roots := by
        simp only [S_roots, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hP'ne]
        exact ⟨hζ0, hζU⟩
      exact absurd ⟨ζ, hmem⟩ hne
  rcases hex_gap with ⟨L_gap, hLg_pos, hLg_lt, hLg_crit⟩
  -- Step 2: Find r_gap ∈ (0, r₁) with Φ r_gap = L_gap
  have hmem_gap : L_gap ∈ Set.Icc (Φ 0) (Φ r₁) := by rw [hΦ0]; exact ⟨le_of_lt hLg_pos, le_of_lt hLg_lt⟩
  obtain ⟨r_gap, hr_gap_mem, hr_gap_eq⟩ := intermediate_value_Icc (le_of_lt hr₁) hΦ_cont hmem_gap
  have hr_gap_lt : r_gap < r₁ := by
    by_contra hge; push Not at hge
    have heq : r_gap = r₁ := le_antisymm hr_gap_mem.2 hge
    rw [heq] at hr_gap_eq
    linarith [hr_gap_eq, hLg_lt]
  -- Step 3: Compact safe region K_safe with uniform lower bound c > 0 on ‖P'(z)‖
  set K_safe : Set ℂ := Metric.closedBall 0 r_gap ∪
      (Metric.closedBall 0 M_bound ∩ {z : ℂ | L_gap ≤ ‖P.eval z‖})
  have hK_safe_comp : IsCompact K_safe := by
    apply (isCompact_closedBall (0 : ℂ) r_gap).union
    exact (isCompact_closedBall (0 : ℂ) M_bound).inter_right (isClosed_le continuous_const P.continuous.norm)
  have hK_safe_ne : K_safe.Nonempty := ⟨0, Or.inl (Metric.mem_closedBall_self hr_gap_mem.1)⟩
  have hK_safe_nd : ∀ z ∈ K_safe, (derivative P).eval z ≠ 0 := by
    intro z hz
    rcases hz with h1 | ⟨h2, h3⟩
    · rw [Metric.mem_closedBall, dist_zero_right] at h1
      have hlt : ‖z‖ < r₁ := lt_of_le_of_lt h1 hr_gap_lt
      have hpos : 0 < ‖(derivative P).eval z‖ :=
        lt_of_lt_of_le (hφ_pos ‖z‖ ⟨norm_nonneg z, hlt⟩) (hP'_lb z hlt)
      exact norm_pos_iff.mp hpos
    · intro h0
      have hzU : z ∈ U := hK_sub h2
      have hlt := hLg_crit z hzU h0
      change L_gap ≤ ‖P.eval z‖ at h3
      linarith
  obtain ⟨z_min, hz_min_mem, hz_min⟩ :=
    hK_safe_comp.exists_isMinOn hK_safe_ne (derivative P).continuous.norm.continuousOn
  set c : ℝ := ‖(derivative P).eval z_min‖
  have hc_pos : 0 < c := norm_pos_iff.mpr (hK_safe_nd z_min hz_min_mem)
  have hc_lb : ∀ z ∈ K_safe, c ≤ ‖(derivative P).eval z‖ := fun z hz => hz_min hz
  -- Step 4: For EVERY w ∈ Metric.ball 0 L_max, construct a continuous radial lift γ_w on [0, 1]
  have hex_lift : ∀ w ∈ Metric.ball (0 : ℂ) L_max,
      ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = 0 ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ U ∧ γ s ∈ K_safe ∧
          P.eval (γ s) = (s : ℂ) * w ∧ ‖γ s‖ ≤ M_bound) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    -- Good t: existence of a lift on [0, t]
    set Good : Set ℝ := {t ∈ Set.Icc (0 : ℝ) 1 | ∃ γ : ℝ → ℂ,
      ContinuousOn γ (Set.Icc 0 t) ∧ γ 0 = 0 ∧
      (∀ s ∈ Set.Icc 0 t, γ s ∈ U ∧ γ s ∈ K_safe ∧ P.eval (γ s) = (s : ℂ) * w ∧ ‖γ s‖ ≤ M_bound) ∧
      (∀ s ∈ Set.Icc 0 t, s * ‖w‖ ≤ L_gap → ‖γ s‖ ≤ r_gap ∧ Φ ‖γ s‖ ≤ s * ‖w‖)}
    have h0_good : (0 : ℝ) ∈ Good := by
      refine ⟨⟨le_rfl, zero_le_one⟩, fun _ => 0, continuousOn_const, rfl, fun s hs => ?_, fun s hs _ => ?_⟩
      · have hs0 : s = 0 := le_antisymm hs.2 hs.1
        subst hs0
        refine ⟨hU_ball (Metric.mem_ball_self hr₁), Or.inl (Metric.mem_closedBall_self hr_gap_mem.1),
          by simp [hP0], by simp [le_of_lt hM_pos]⟩
      · have hs0 : s = 0 := le_antisymm hs.2 hs.1
        subst hs0
        simp [hr_gap_mem.1, hΦ0]
    have hGood_bdd : BddAbove Good := ⟨1, fun t ht => ht.1.2⟩
    set t_star : ℝ := sSup Good
    have ht_star_mem : t_star ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_csSup hGood_bdd h0_good, csSup_le ⟨0, h0_good⟩ (fun t ht => ht.1.2)⟩
    -- Lipschitz bound on any lift staying in K_safe (prove on [a', b'] ⊂ (0, t), then pass to endpoints!)
    have hLip : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ γ : ℝ → ℂ,
        ContinuousOn γ (Set.Icc 0 t) →
        (∀ s ∈ Set.Icc 0 t, γ s ∈ K_safe ∧ P.eval (γ s) = (s : ℂ) * w) →
        ∀ a b : ℝ, a ∈ Set.Icc 0 t → b ∈ Set.Icc 0 t → a ≤ b →
        ‖γ b - γ a‖ ≤ (‖w‖ / c) * (b - a) := by
      intro t _ γ hγc hγP a b ha hb hab
      by_cases hab_eq : a = b
      · subst hab_eq; simp
      · have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
        -- On any strictly interior subinterval [u, v] with a < u ≤ v < b, γ has HasDerivAt everywhere on [u, v]!
        have hLip_int : ∀ u v : ℝ, a < u → u ≤ v → v < b → ‖γ v - γ u‖ ≤ (‖w‖ / c) * (v - u) := by
          intro u v hau huv hvb
          have hsub : Set.Icc u v ⊆ Set.Ioo 0 t := fun s hs =>
            ⟨lt_of_le_of_lt ha.1 (lt_of_lt_of_le hau hs.1), lt_of_le_of_lt hs.2 (lt_of_lt_of_le hvb hb.2)⟩
          have hderiv_uv : ∀ s ∈ Set.Icc u v,
              HasDerivWithinAt γ (w / (derivative P).eval (γ s)) (Set.Icc u v) s := by
            intro s hs
            have hs_mem := hsub hs
            have hnhds : Set.Icc 0 t ∈ nhds s := Icc_mem_nhds hs_mem.1 hs_mem.2
            have hca : ContinuousAt γ s := hγc.continuousAt hnhds
            have hev : ∀ᶠ x in nhds s, P.eval (γ x) = (x : ℂ) * w :=
              Filter.mem_of_superset hnhds (fun x hx => (hγP x hx).2)
            have hnd : (derivative P).eval (γ s) ≠ 0 :=
              hK_safe_nd (γ s) (hγP s (Set.Ioo_subset_Icc_self hs_mem)).1
            exact (hasDerivAt_of_lift P hca hev hnd).hasDerivWithinAt
          have hbound_uv : ∀ s ∈ Set.Icc u v, ‖w / (derivative P).eval (γ s)‖ ≤ ‖w‖ / c := by
            intro s hs
            have hs_mem : s ∈ Set.Icc 0 t := Set.Ioo_subset_Icc_self (hsub hs)
            rw [norm_div]
            exact div_le_div_of_nonneg_left (norm_nonneg w) hc_pos (hc_lb (γ s) (hγP s hs_mem).1)
          have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
            hderiv_uv hbound_uv (convex_Icc u v) ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩
          rwa [Real.norm_of_nonneg (sub_nonneg.mpr huv)] at hmv
        -- Pass to the limit u_n = a + (b-a)/(n+3) → a⁺, v_n = b - (b-a)/(n+3) → b⁻!
        let un : ℕ → ℝ := fun n => a + (b - a) / ((n + 3 : ℕ) : ℝ)
        let vn : ℕ → ℝ := fun n => b - (b - a) / ((n + 3 : ℕ) : ℝ)
        have hba : 0 < b - a := sub_pos.mpr hab_lt
        have hun_mem : ∀ n : ℕ, a < un n ∧ un n ≤ vn n ∧ vn n < b := by
          intro n
          have hn3 : (3 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ n + 3 by omega)
          have hpos : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by linarith
          have hd_pos : 0 < (b - a) / ((n + 3 : ℕ) : ℝ) := div_pos hba hpos
          have hd_le : (b - a) / ((n + 3 : ℕ) : ℝ) ≤ (b - a) / 3 :=
            div_le_div_of_nonneg_left (le_of_lt hba) (by norm_num) hn3
          dsimp [un, vn]; constructor; linarith; constructor <;> linarith
        have hinv0 : Filter.Tendsto (fun n : ℕ => (b - a) / ((n + 3 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
          have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have h2 := h1.comp (Filter.tendsto_add_atTop_nat 2)
          have h3 : (fun n : ℕ => (b - a) * ((1 : ℝ) / (((n + 2 : ℕ) : ℝ) + 1))) =
              (fun n : ℕ => (b - a) / ((n + 3 : ℕ) : ℝ)) := by
            ext n; push_cast; ring
          rw [← h3]
          simpa using tendsto_const_nhds.mul h2
        have hun_lim : Filter.Tendsto un Filter.atTop (nhdsWithin a (Set.Icc 0 t)) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨by simpa [un] using tendsto_const_nhds.add hinv0, Filter.Eventually.of_forall fun n => ?_⟩
          have hm := hun_mem n
          exact ⟨le_trans ha.1 (le_of_lt hm.1), le_trans (le_trans hm.2.1 (le_of_lt hm.2.2)) hb.2⟩
        have hvn_lim : Filter.Tendsto vn Filter.atTop (nhdsWithin b (Set.Icc 0 t)) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨by simpa [vn] using tendsto_const_nhds.sub hinv0, Filter.Eventually.of_forall fun n => ?_⟩
          have hm := hun_mem n
          exact ⟨le_trans ha.1 (le_of_lt (lt_of_lt_of_le hm.1 hm.2.1)), le_trans (le_of_lt hm.2.2) hb.2⟩
        have hγu : Filter.Tendsto (fun n => γ (un n)) Filter.atTop (nhds (γ a)) := (hγc a ha).tendsto.comp hun_lim
        have hγv : Filter.Tendsto (fun n => γ (vn n)) Filter.atTop (nhds (γ b)) := (hγc b hb).tendsto.comp hvn_lim
        have hlim_l : Filter.Tendsto (fun n => ‖γ (vn n) - γ (un n)‖) Filter.atTop (nhds ‖γ b - γ a‖) :=
          (hγv.sub hγu).norm
        have hlim_r : Filter.Tendsto (fun n => (‖w‖ / c) * (vn n - un n)) Filter.atTop
            (nhds ((‖w‖ / c) * (b - a))) := by
          have hun_r : Filter.Tendsto un Filter.atTop (nhds a) := by simpa [un] using tendsto_const_nhds.add hinv0
          have hvn_r : Filter.Tendsto vn Filter.atTop (nhds b) := by simpa [vn] using tendsto_const_nhds.sub hinv0
          exact tendsto_const_nhds.mul (hvn_r.sub hun_r)
        exact le_of_tendsto_of_tendsto hlim_l hlim_r (Filter.Eventually.of_forall fun n =>
          hLip_int (un n) (vn n) (hun_mem n).1 (hun_mem n).2.1 (hun_mem n).2.2)
    -- Closedness: t_star ∈ Good!
    have ht_star_good : t_star ∈ Good := by
      by_cases ht0 : t_star = 0
      · rw [ht0]; exact h0_good
      · have ht_pos : 0 < t_star := lt_of_le_of_ne ht_star_mem.1 (Ne.symm ht0)
        -- For every s ∈ [0, t_star), there exists t ∈ Good with s < t ≤ t_star, hence a unique value Γ s!
        have hex_lt : ∀ s : ℝ, 0 ≤ s → s < t_star → ∃ t ∈ Good, s < t := by
          intro s _ hs
          rcases exists_lt_of_lt_csSup ⟨0, h0_good⟩ hs with ⟨t, htG, hst⟩
          exact ⟨t, htG, hst⟩
        -- Choose a canonical lift γ_t for each t ∈ Good
        classical
        -- Define Γ(s) for s < t_star using Classical.choose from hex_lt
        let pick_t : ∀ s : ℝ, (0 ≤ s ∧ s < t_star) → ℝ := fun s hs => (hex_lt s hs.1 hs.2).choose
        have hpick_mem : ∀ s (hs : 0 ≤ s ∧ s < t_star), pick_t s hs ∈ Good :=
          fun s hs => (hex_lt s hs.1 hs.2).choose_spec.1
        have hpick_gt : ∀ s (hs : 0 ≤ s ∧ s < t_star), s < pick_t s hs :=
          fun s hs => (hex_lt s hs.1 hs.2).choose_spec.2
        let γ_of : ∀ t ∈ Good, ℝ → ℂ := fun t ht => ht.2.choose
        have hγ_spec : ∀ t (ht : t ∈ Good),
            ContinuousOn (γ_of t ht) (Set.Icc 0 t) ∧ (γ_of t ht) 0 = 0 ∧
            (∀ s ∈ Set.Icc 0 t, (γ_of t ht) s ∈ U ∧ (γ_of t ht) s ∈ K_safe ∧
              P.eval ((γ_of t ht) s) = (s : ℂ) * w ∧ ‖(γ_of t ht) s‖ ≤ M_bound) ∧
            (∀ s ∈ Set.Icc 0 t, s * ‖w‖ ≤ L_gap → ‖(γ_of t ht) s‖ ≤ r_gap ∧ Φ ‖(γ_of t ht) s‖ ≤ s * ‖w‖) :=
          fun t ht => ht.2.choose_spec
        -- Any two lifts agree on their common domain
        have hagree : ∀ t₁ (ht₁ : t₁ ∈ Good) t₂ (ht₂ : t₂ ∈ Good),
            ∀ s ∈ Set.Icc 0 (min t₁ t₂), γ_of t₁ ht₁ s = γ_of t₂ ht₂ s := by
          intro t₁ ht₁ t₂ ht₂ s hs
          have hm_nn : 0 ≤ min t₁ t₂ := le_min ht₁.1.1 ht₂.1.1
          have hsub1 : Set.Icc 0 (min t₁ t₂) ⊆ Set.Icc 0 t₁ := Set.Icc_subset_Icc_right (min_le_left _ _)
          have hsub2 : Set.Icc 0 (min t₁ t₂) ⊆ Set.Icc 0 t₂ := Set.Icc_subset_Icc_right (min_le_right _ _)
          exact lift_unique P hm_nn ((hγ_spec t₁ ht₁).1.mono hsub1) ((hγ_spec t₂ ht₂).1.mono hsub2)
            (hγ_spec t₁ ht₁).2.1 (hγ_spec t₂ ht₂).2.1
            (fun u hu => ((hγ_spec t₁ ht₁).2.2.1 u (hsub1 hu)).2.2.1)
            (fun u hu => ((hγ_spec t₂ ht₂).2.2.1 u (hsub2 hu)).2.2.1)
            (fun u hu => hK_safe_nd _ ((hγ_spec t₁ ht₁).2.2.1 u (hsub1 hu)).2.1) s hs
        -- Define Γ₀ on [0, t_star)
        let Γ₀ : ℝ → ℂ := fun s =>
          if hs : 0 ≤ s ∧ s < t_star then γ_of (pick_t s hs) (hpick_mem s hs) s else 0
        -- Γ₀ agrees with γ_of t ht on [0, t] for any t ∈ Good with t < t_star (and on [0, t) for t ≤ t_star)
        have hΓ₀_eq : ∀ t (ht : t ∈ Good), ∀ s : ℝ, 0 ≤ s → s ≤ t → s < t_star → Γ₀ s = γ_of t ht s := by
          intro t ht s hs0 hst hslt
          have hcond : 0 ≤ s ∧ s < t_star := ⟨hs0, hslt⟩
          simp only [Γ₀, dif_pos hcond]
          exact hagree (pick_t s hcond) (hpick_mem s hcond) t ht s ⟨hs0, le_min (le_of_lt (hpick_gt s hcond)) hst⟩
        -- Γ₀ is Lipschitz on [0, t_star) with constant ‖w‖ / c
        have hΓ₀_lip : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < t_star → ‖Γ₀ b - Γ₀ a‖ ≤ (‖w‖ / c) * (b - a) := by
          intro a b ha hab hblt
          have htb := hpick_mem b ⟨le_trans ha hab, hblt⟩
          have hb_lt_t : b < pick_t b ⟨le_trans ha hab, hblt⟩ := hpick_gt b ⟨le_trans ha hab, hblt⟩
          rw [hΓ₀_eq _ htb b (le_trans ha hab) (le_of_lt hb_lt_t) hblt,
              hΓ₀_eq _ htb a ha (le_trans hab (le_of_lt hb_lt_t)) (lt_of_le_of_lt hab hblt)]
          exact hLip _ htb.1 _ (hγ_spec _ htb).1
            (fun s hs => ⟨((hγ_spec _ htb).2.2.1 s hs).2.1, ((hγ_spec _ htb).2.2.1 s hs).2.2.1⟩)
            a b ⟨ha, le_trans hab (le_of_lt hb_lt_t)⟩ ⟨le_trans ha hab, le_of_lt hb_lt_t⟩ hab
        -- Define sequence s_n = t_star * (1 - 1/(n+2)) → t_star⁻; Γ₀(s_n) is Cauchy, hence converges to z_star!
        let seq : ℕ → ℝ := fun n => t_star * (1 - 1 / ((n + 2 : ℕ) : ℝ))
        have hseq_mem : ∀ n : ℕ, 0 ≤ seq n ∧ seq n < t_star := by
          intro n
          have hn2 : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n + 2 by omega)
          have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by linarith
          have h1 : 1 / ((n + 2 : ℕ) : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
          have h2 : 0 < 1 / ((n + 2 : ℕ) : ℝ) := one_div_pos.mpr hpos
          dsimp [seq]
          constructor <;> nlinarith
        have hseq_tendsto : Filter.Tendsto seq Filter.atTop (nhds t_star) := by
          have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
            have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
              tendsto_one_div_add_atTop_nhds_zero_nat
            have h2 := h1.comp (Filter.tendsto_add_atTop_nat 1)
            exact h2.congr (fun n => by dsimp [Function.comp]; push_cast; ring)
          have h1 : Filter.Tendsto (fun n : ℕ => t_star * (1 - 1 / ((n + 2 : ℕ) : ℝ))) Filter.atTop
              (nhds (t_star * (1 - 0))) := tendsto_const_nhds.mul (tendsto_const_nhds.sub h0)
          simpa [seq] using h1
        have hCauchy : CauchySeq (fun n => Γ₀ (seq n)) := by
          rw [Metric.cauchySeq_iff]
          intro ε hε
          have hseq_cauchy := hseq_tendsto.cauchySeq
          rw [Metric.cauchySeq_iff] at hseq_cauchy
          set Llip : ℝ := ‖w‖ / c + 1
          have hLlip_pos : 0 < Llip := by positivity
          rcases hseq_cauchy (ε / Llip) (div_pos hε hLlip_pos) with ⟨N, hN⟩
          refine ⟨N, fun m hm n hn => ?_⟩
          rw [dist_eq_norm]
          have hdist := hN m hm n hn
          rw [Real.dist_eq] at hdist
          rcases le_total (seq m) (seq n) with hle | hle
          · have h1 := hΓ₀_lip (seq m) (seq n) (hseq_mem m).1 hle (hseq_mem n).2
            rw [norm_sub_rev] at h1
            have h2 : seq n - seq m ≤ |seq m - seq n| := by rw [abs_sub_comm]; exact le_abs_self _
            calc ‖Γ₀ (seq m) - Γ₀ (seq n)‖ ≤ (‖w‖ / c) * (seq n - seq m) := h1
              _ ≤ Llip * |seq m - seq n| := by
                  have : ‖w‖ / c ≤ Llip := by dsimp [Llip]; linarith
                  nlinarith [abs_nonneg (seq m - seq n)]
              _ < Llip * (ε / Llip) := mul_lt_mul_of_pos_left hdist hLlip_pos
              _ = ε := mul_div_cancel₀ ε (ne_of_gt hLlip_pos)
          · have h1 := hΓ₀_lip (seq n) (seq m) (hseq_mem n).1 hle (hseq_mem m).2
            have h2 : seq m - seq n ≤ |seq m - seq n| := le_abs_self _
            calc ‖Γ₀ (seq m) - Γ₀ (seq n)‖ ≤ (‖w‖ / c) * (seq m - seq n) := h1
              _ ≤ Llip * |seq m - seq n| := by
                  have : ‖w‖ / c ≤ Llip := by dsimp [Llip]; linarith
                  nlinarith [abs_nonneg (seq m - seq n)]
              _ < Llip * (ε / Llip) := mul_lt_mul_of_pos_left hdist hLlip_pos
              _ = ε := mul_div_cancel₀ ε (ne_of_gt hLlip_pos)
        obtain ⟨z_star, hz_star⟩ := cauchySeq_tendsto_of_complete hCauchy
        -- Define Γ on [0, t_star] by extending Γ₀ with z_star at t_star
        let Γ : ℝ → ℂ := fun s => if s < t_star then Γ₀ s else z_star
        -- Prove Γ is Lipschitz on ALL of [0, t_star] with constant ‖w‖ / c!
        have hΓ_lip : ∀ a b : ℝ, a ∈ Set.Icc 0 t_star → b ∈ Set.Icc 0 t_star → a ≤ b →
            ‖Γ b - Γ a‖ ≤ (‖w‖ / c) * (b - a) := by
          intro a b ha hb hab
          by_cases hblt : b < t_star
          · have halt : a < t_star := lt_of_le_of_lt hab hblt
            simp only [Γ, if_pos hblt, if_pos halt]
            exact hΓ₀_lip a b ha.1 hab hblt
          · have hbeq : b = t_star := le_antisymm hb.2 (not_lt.mp hblt)
            by_cases halt : a < t_star
            · simp only [Γ, if_neg (not_lt.mpr (le_of_eq hbeq.symm)), if_pos halt]
              -- Pass to the limit in ‖Γ₀ (seq n) - Γ₀ a‖ ≤ (‖w‖ / c) * (seq n - a)
              have hev : ∀ᶠ n in Filter.atTop, a ≤ seq n :=
                hseq_tendsto.eventually (Ioi_mem_nhds halt) |>.mono (fun _ h => le_of_lt h)
              have hlim_lhs : Filter.Tendsto (fun n => ‖Γ₀ (seq n) - Γ₀ a‖) Filter.atTop (nhds ‖z_star - Γ₀ a‖) :=
                (hz_star.sub tendsto_const_nhds).norm
              have hlim_rhs : Filter.Tendsto (fun n => (‖w‖ / c) * (seq n - a)) Filter.atTop
                  (nhds ((‖w‖ / c) * (t_star - a))) :=
                tendsto_const_nhds.mul (hseq_tendsto.sub tendsto_const_nhds)
              rw [hbeq]
              exact le_of_tendsto_of_tendsto hlim_lhs hlim_rhs
                (hev.mono fun n han => hΓ₀_lip a (seq n) ha.1 han (hseq_mem n).2)
            · have haeq : a = t_star := le_antisymm ha.2 (not_lt.mp halt)
              simp only [Γ, haeq, hbeq, lt_irrefl, ↓reduceIte, sub_self, norm_zero, mul_zero, le_rfl]
        have hΓ_cont : ContinuousOn Γ (Set.Icc 0 t_star) := by
          rw [Metric.continuousOn_iff]
          intro a ha ε hε
          set Llip : ℝ := ‖w‖ / c + 1
          have hLlip_pos : 0 < Llip := by positivity
          refine ⟨ε / Llip, div_pos hε hLlip_pos, fun b hb hdist => ?_⟩
          rw [dist_eq_norm]
          rw [Real.dist_eq] at hdist
          rcases le_total a b with hle | hle
          · have h1 := hΓ_lip a b ha hb hle
            have h2 : b - a ≤ |b - a| := le_abs_self _
            calc ‖Γ b - Γ a‖ ≤ (‖w‖ / c) * (b - a) := h1
              _ ≤ Llip * |b - a| := by
                  have : ‖w‖ / c ≤ Llip := by dsimp [Llip]; linarith
                  nlinarith [abs_nonneg (b - a)]
              _ < Llip * (ε / Llip) := mul_lt_mul_of_pos_left hdist hLlip_pos
              _ = ε := mul_div_cancel₀ ε (ne_of_gt hLlip_pos)
          · have h1 := hΓ_lip b a hb ha hle
            rw [norm_sub_rev] at h1
            have h2 : a - b ≤ |b - a| := by rw [abs_sub_comm]; exact le_abs_self _
            calc ‖Γ b - Γ a‖ ≤ (‖w‖ / c) * (a - b) := h1
              _ ≤ Llip * |b - a| := by
                  have : ‖w‖ / c ≤ Llip := by dsimp [Llip]; linarith
                  nlinarith [abs_nonneg (b - a)]
              _ < Llip * (ε / Llip) := mul_lt_mul_of_pos_left hdist hLlip_pos
              _ = ε := mul_div_cancel₀ ε (ne_of_gt hLlip_pos)
        have hΓ_0 : Γ 0 = 0 := by
          simp only [Γ, if_pos ht_pos]
          have h0c : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) < t_star := ⟨le_rfl, ht_pos⟩
          rw [hΓ₀_eq (pick_t 0 h0c) (hpick_mem 0 h0c) 0 le_rfl (le_of_lt (hpick_gt 0 h0c)) ht_pos]
          exact (hγ_spec _ (hpick_mem 0 h0c)).2.1
        -- Properties of Γ at every s < t_star
        have hΓ_lt_props : ∀ s : ℝ, 0 ≤ s → s < t_star →
            Γ s ∈ U ∧ Γ s ∈ K_safe ∧ P.eval (Γ s) = (s : ℂ) * w ∧ ‖Γ s‖ ≤ M_bound ∧
            (s * ‖w‖ ≤ L_gap → ‖Γ s‖ ≤ r_gap ∧ Φ ‖Γ s‖ ≤ s * ‖w‖) := by
          intro s hs0 hslt
          simp only [Γ, if_pos hslt]
          have hcond : 0 ≤ s ∧ s < t_star := ⟨hs0, hslt⟩
          have htm := hpick_mem s hcond
          have hsle : s ≤ pick_t s hcond := le_of_lt (hpick_gt s hcond)
          rw [hΓ₀_eq _ htm s hs0 hsle hslt]
          have h1 := (hγ_spec _ htm).2.2.1 s ⟨hs0, hsle⟩
          have h2 := (hγ_spec _ htm).2.2.2 s ⟨hs0, hsle⟩
          exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2⟩
        -- Properties at t_star by limit along seq n → t_star!
        have hPz_star : P.eval z_star = (t_star : ℂ) * w := by
          have hlim1 : Filter.Tendsto (fun n => P.eval (Γ₀ (seq n))) Filter.atTop (nhds (P.eval z_star)) :=
            P.continuous.continuousAt.tendsto.comp hz_star
          have hlim2 : Filter.Tendsto (fun n => (seq n : ℂ) * w) Filter.atTop (nhds ((t_star : ℂ) * w)) :=
            (Complex.continuous_ofReal.continuousAt.tendsto.comp hseq_tendsto).mul tendsto_const_nhds
          have heq_n : ∀ n : ℕ, P.eval (Γ₀ (seq n)) = (seq n : ℂ) * w := fun n => by
            have h := (hΓ_lt_props (seq n) (hseq_mem n).1 (hseq_mem n).2).2.2.1
            simpa [Γ, if_pos (hseq_mem n).2] using h
          exact tendsto_nhds_unique (by simpa only [heq_n] using hlim1) hlim2
        have hz_star_K : z_star ∈ K_safe := by
          have hmem_n : ∀ n : ℕ, Γ₀ (seq n) ∈ K_safe := fun n => by
            have h := (hΓ_lt_props (seq n) (hseq_mem n).1 (hseq_mem n).2).2.1
            simpa [Γ, if_pos (hseq_mem n).2] using h
          exact hK_safe_comp.isClosed.mem_of_tendsto hz_star (Filter.Eventually.of_forall hmem_n)
        have hz_star_M : ‖z_star‖ ≤ M_bound := by
          have hle_n : ∀ n : ℕ, ‖Γ₀ (seq n)‖ ≤ M_bound := fun n => by
            have h := (hΓ_lt_props (seq n) (hseq_mem n).1 (hseq_mem n).2).2.2.2.1
            simpa [Γ, if_pos (hseq_mem n).2] using h
          exact le_of_tendsto hz_star.norm (Filter.Eventually.of_forall hle_n)
        have hz_star_U : z_star ∈ U :=
          hK_sub (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz_star_M)
        have hz_star_phi : t_star * ‖w‖ ≤ L_gap → ‖z_star‖ ≤ r_gap ∧ Φ ‖z_star‖ ≤ t_star * ‖w‖ := by
          intro htg
          have hle_r : ∀ n : ℕ, ‖Γ₀ (seq n)‖ ≤ r_gap := fun n => by
            have hsn : seq n * ‖w‖ ≤ L_gap := by
              have hlt := (hseq_mem n).2
              nlinarith [norm_nonneg w]
            have h := ((hΓ_lt_props (seq n) (hseq_mem n).1 (hseq_mem n).2).2.2.2.2 hsn).1
            simpa [Γ, if_pos (hseq_mem n).2] using h
          have hzr : ‖z_star‖ ≤ r_gap := le_of_tendsto hz_star.norm (Filter.Eventually.of_forall hle_r)
          refine ⟨hzr, ?_⟩
          have hΦ_n : ∀ n : ℕ, Φ ‖Γ₀ (seq n)‖ ≤ seq n * ‖w‖ := fun n => by
            have hsn : seq n * ‖w‖ ≤ L_gap := by
              have hlt := (hseq_mem n).2
              nlinarith [norm_nonneg w]
            have h := ((hΓ_lt_props (seq n) (hseq_mem n).1 (hseq_mem n).2).2.2.2.2 hsn).2
            simpa [Γ, if_pos (hseq_mem n).2] using h
          have hΦ_ca : ContinuousAt Φ ‖z_star‖ :=
            (hΦ_deriv ‖z_star‖ ⟨norm_nonneg _, lt_of_le_of_lt hzr hr_gap_lt⟩).continuousAt
          have hlim_l : Filter.Tendsto (fun n => Φ ‖Γ₀ (seq n)‖) Filter.atTop (nhds (Φ ‖z_star‖)) :=
            hΦ_ca.tendsto.comp hz_star.norm
          have hlim_r : Filter.Tendsto (fun n => seq n * ‖w‖) Filter.atTop (nhds (t_star * ‖w‖)) :=
            hseq_tendsto.mul tendsto_const_nhds
          exact le_of_tendsto_of_tendsto hlim_l hlim_r (Filter.Eventually.of_forall hΦ_n)
        refine ⟨ht_star_mem, Γ, hΓ_cont, hΓ_0, fun s hs => ?_, fun s hs hsg => ?_⟩
        · by_cases hslt : s < t_star
          · have hp := hΓ_lt_props s hs.1 hslt
            exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
          · have hseq : s = t_star := le_antisymm hs.2 (not_lt.mp hslt)
            subst hseq
            simp only [Γ, lt_irrefl, ↓reduceIte]
            exact ⟨hz_star_U, hz_star_K, hPz_star, hz_star_M⟩
        · by_cases hslt : s < t_star
          · exact (hΓ_lt_props s hs.1 hslt).2.2.2.2 hsg
          · have hseq : s = t_star := le_antisymm hs.2 (not_lt.mp hslt)
            subst hseq
            simp only [Γ, lt_irrefl, ↓reduceIte]
            exact hz_star_phi hsg
    -- Openness: if t_star < 1, extend past t_star to obtain a contradiction!
    have ht_star_eq1 : t_star = 1 := by
      by_contra hne1
      have ht_lt1 : t_star < 1 := lt_of_le_of_ne ht_star_mem.2 hne1
      rcases ht_star_good with ⟨ht_mem, γ, hγc, hγ0, hγ_all, hγ_phi⟩
      set z_t := γ t_star
      have hzt_mem := hγ_all t_star ⟨ht_mem.1, le_rfl⟩
      have hP'zt : (derivative P).eval z_t ≠ 0 := hK_safe_nd z_t hzt_mem.2.1
      have hsd := P.hasStrictDerivAt z_t
      set e := (hsd.hasStrictFDerivAt_equiv hP'zt).toOpenPartialHomeomorph (fun z => P.eval z)
      have he_coe : (e : ℂ → ℂ) = fun z => P.eval z :=
        (hsd.hasStrictFDerivAt_equiv hP'zt).toOpenPartialHomeomorph_coe
      have hzt_src : z_t ∈ e.source :=
        (hsd.hasStrictFDerivAt_equiv hP'zt).mem_toOpenPartialHomeomorph_source
      have hPt_tgt : P.eval z_t ∈ e.target :=
        (hsd.hasStrictFDerivAt_equiv hP'zt).image_mem_toOpenPartialHomeomorph_target
      have hPt_eq : P.eval z_t = (t_star : ℂ) * w := hzt_mem.2.2.1
      have hsymm_t : e.symm ((t_star : ℂ) * w) = z_t := by
        rw [← hPt_eq]
        have := e.left_inv hzt_src
        rwa [he_coe] at this
      have hsymm_ca : ContinuousAt e.symm ((t_star : ℂ) * w) :=
        e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (by rwa [← hPt_eq]))
      have hray_c : Continuous (fun s : ℝ => (s : ℂ) * w) :=
        Complex.continuous_ofReal.mul continuous_const
      have hcomp_ca : ContinuousAt (fun s : ℝ => e.symm ((s : ℂ) * w)) t_star :=
        ContinuousAt.comp hsymm_ca (hray_c.continuousAt (x := t_star))
      -- Choose δ > 0 so that for |s - t_star| < δ:
      -- (a) s * w ∈ e.target, (b) e.symm (s * w) ∈ U, (c) P'(e.symm (s * w)) ≠ 0,
      -- (d) if t_star * ‖w‖ ≤ L_gap then ‖e.symm (s * w)‖ < r₁!
      have hev_tgt : ∀ᶠ (s : ℝ) in nhds t_star, (s : ℂ) * w ∈ e.target :=
        (hray_c.continuousAt (x := t_star)).eventually
          (e.open_target.mem_nhds (show (t_star : ℂ) * w ∈ e.target by rwa [← hPt_eq]))
      have hev_U : ∀ᶠ (s : ℝ) in nhds t_star, e.symm ((s : ℂ) * w) ∈ U :=
        hcomp_ca.eventually (hU_open.mem_nhds (show e.symm ((t_star : ℂ) * w) ∈ U by rw [hsymm_t]; exact hzt_mem.1))
      have hev_nd : ∀ᶠ (s : ℝ) in nhds t_star, (derivative P).eval (e.symm ((s : ℂ) * w)) ≠ 0 := by
        have hc_nd : ContinuousAt (fun s : ℝ => (derivative P).eval (e.symm ((s : ℂ) * w))) t_star :=
          ContinuousAt.comp (g := fun z => (derivative P).eval z) (derivative P).continuous.continuousAt hcomp_ca
        exact hc_nd.eventually_ne (show (derivative P).eval (e.symm ((t_star : ℂ) * w)) ≠ 0 by rw [hsymm_t]; exact hP'zt)
      have hev_ball : ∀ᶠ (s : ℝ) in nhds t_star, t_star * ‖w‖ ≤ L_gap → ‖e.symm ((s : ℂ) * w)‖ < r₁ := by
        by_cases htg : t_star * ‖w‖ ≤ L_gap
        · have hzt_lt : ‖z_t‖ < r₁ := lt_of_le_of_lt (hγ_phi t_star ⟨ht_mem.1, le_rfl⟩ htg).1 hr_gap_lt
          have h1 := hcomp_ca.eventually (Metric.isOpen_ball.mem_nhds
            (show e.symm ((t_star : ℂ) * w) ∈ Metric.ball (0 : ℂ) r₁ by
              rw [hsymm_t, Metric.mem_ball, dist_zero_right]; exact hzt_lt))
          filter_upwards [h1] with s hs _
          simpa [Metric.mem_ball, dist_zero_right] using hs
        · exact Filter.Eventually.of_forall (fun _ h => absurd h htg)
      have hev_comb := ((hev_tgt.and hev_U).and hev_nd).and hev_ball
      rw [Metric.eventually_nhds_iff] at hev_comb
      rcases hev_comb with ⟨δ, hδ_pos, hδ⟩
      -- Pick t' ∈ (t_star, 1] with t' - t_star < δ; if t_star * ‖w‖ < L_gap, also keep t' * ‖w‖ ≤ L_gap!
      set δ_gap : ℝ := if t_star * ‖w‖ < L_gap ∧ 0 < ‖w‖ then (L_gap - t_star * ‖w‖) / ‖w‖ else 1
      have hδ_gap_pos : 0 < δ_gap := by
        dsimp [δ_gap]
        split_ifs with h
        · exact div_pos (by linarith [h.1]) h.2
        · exact one_pos
      set t' : ℝ := min 1 (t_star + min (δ / 2) (δ_gap / 2))
      have ht'_gt : t_star < t' := by
        apply lt_min ht_lt1
        have : 0 < min (δ / 2) (δ_gap / 2) := lt_min (by linarith) (by linarith)
        linarith
      have ht'_le1 : t' ≤ 1 := min_le_left _ _
      have ht'_dist : ∀ s ∈ Set.Icc t_star t', dist s t_star < δ := by
        intro s hs
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
        have h1 : t' - t_star ≤ δ / 2 := by
          have := min_le_right (1 : ℝ) (t_star + min (δ / 2) (δ_gap / 2))
          linarith [min_le_left (δ / 2) (δ_gap / 2)]
        linarith [hs.2]
      -- Define extended lift γ' on [0, t']
      let γ' : ℝ → ℂ := fun s => if s ≤ t_star then γ s else e.symm ((s : ℂ) * w)
      have hγ'_eq_left : ∀ s ∈ Set.Icc 0 t_star, γ' s = γ s := fun s hs => if_pos hs.2
      have hγ'_eq_right : ∀ s ∈ Set.Icc t_star t', γ' s = e.symm ((s : ℂ) * w) := by
        intro s hs
        by_cases hle : s ≤ t_star
        · have heq : s = t_star := le_antisymm hle hs.1
          subst heq
          simp only [γ', le_rfl, ↓reduceIte, hsymm_t]; rfl
        · exact if_neg hle
      have hγ'_cont_right : ContinuousOn (fun s : ℝ => e.symm ((s : ℂ) * w)) (Set.Icc t_star t') := by
        apply e.continuousOn_symm.comp hray_c.continuousOn
        intro s hs
        exact (hδ (ht'_dist s hs)).1.1.1
      have hγ'_cont : ContinuousOn γ' (Set.Icc 0 t') := by
        have h1 : ContinuousOn γ' (Set.Icc 0 t_star) := hγc.congr hγ'_eq_left
        have h2 : ContinuousOn γ' (Set.Icc t_star t') := hγ'_cont_right.congr hγ'_eq_right
        have hunion : Set.Icc 0 t' = Set.Icc 0 t_star ∪ Set.Icc t_star t' :=
          (Set.Icc_union_Icc_eq_Icc ht_mem.1 (le_of_lt ht'_gt)).symm
        rw [hunion]
        exact h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
      have hγ'_0 : γ' 0 = 0 := by rw [hγ'_eq_left 0 ⟨le_rfl, ht_mem.1⟩, hγ0]
      have hγ'_P : ∀ s ∈ Set.Icc 0 t', P.eval (γ' s) = (s : ℂ) * w := by
        intro s hs
        by_cases hle : s ≤ t_star
        · rw [hγ'_eq_left s ⟨hs.1, hle⟩]; exact (hγ_all s ⟨hs.1, hle⟩).2.2.1
        · have hs' : s ∈ Set.Icc t_star t' := ⟨le_of_lt (not_le.mp hle), hs.2⟩
          rw [hγ'_eq_right s hs']
          have htgt := (hδ (ht'_dist s hs')).1.1.1
          have := e.right_inv htgt
          rwa [he_coe] at this
      have hγ'_U : ∀ s ∈ Set.Icc 0 t', γ' s ∈ U := by
        intro s hs
        by_cases hle : s ≤ t_star
        · rw [hγ'_eq_left s ⟨hs.1, hle⟩]; exact (hγ_all s ⟨hs.1, hle⟩).1
        · have hs' : s ∈ Set.Icc t_star t' := ⟨le_of_lt (not_le.mp hle), hs.2⟩
          rw [hγ'_eq_right s hs']
          exact (hδ (ht'_dist s hs')).1.1.2
      have hγ'_M : ∀ s ∈ Set.Icc 0 t', ‖γ' s‖ ≤ M_bound := by
        intro s hs
        apply hPre_bound (γ' s) (hγ'_U s hs)
        rw [hγ'_P s hs, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]
        have hs1 : s ≤ 1 := le_trans hs.2 ht'_le1
        have hw_nn : 0 ≤ ‖w‖ := norm_nonneg w
        nlinarith
      -- Check the Φ bound on [0, t'] for s * ‖w‖ ≤ L_gap!
      have hγ'_phi : ∀ s ∈ Set.Icc 0 t', s * ‖w‖ ≤ L_gap → ‖γ' s‖ ≤ r_gap ∧ Φ ‖γ' s‖ ≤ s * ‖w‖ := by
        intro s hs hsg
        by_cases hle : s ≤ t_star
        · rw [hγ'_eq_left s ⟨hs.1, hle⟩]
          exact hγ_phi s ⟨hs.1, hle⟩ hsg
        · have hs_gt : t_star < s := not_le.mp hle
          have htg : t_star * ‖w‖ ≤ L_gap := by nlinarith [norm_nonneg w]
          -- On [t_star, t'], apply phi_norm_le_along_lift!
          have hball_r : ∀ u ∈ Set.Icc t_star t', ‖γ' u‖ < r₁ := by
            intro u hu
            rw [hγ'_eq_right u hu]
            exact (hδ (ht'_dist u hu)).2 htg
          have hderiv_r : ∀ u ∈ Set.Ioo t_star t', HasDerivAt γ' (w / (derivative P).eval (γ' u)) u := by
            intro u hu
            have hnhds : Set.Icc t_star t' ∈ nhds u := Icc_mem_nhds hu.1 hu.2
            have hca : ContinuousAt γ' u := (hγ'_cont_right.congr hγ'_eq_right).continuousAt hnhds
            have hev : ∀ᶠ v in nhds u, P.eval (γ' v) = (v : ℂ) * w :=
              Filter.mem_of_superset hnhds (fun v hv => hγ'_P v ⟨le_trans ht_mem.1 hv.1, hv.2⟩)
            have hnd : (derivative P).eval (γ' u) ≠ 0 := by
              rw [hγ'_eq_right u (Set.Ioo_subset_Icc_self hu)]
              exact (hδ (ht'_dist u (Set.Ioo_subset_Icc_self hu))).1.2
            exact hasDerivAt_of_lift P hca hev hnd
          have hstart : Φ ‖γ' t_star‖ ≤ t_star * ‖w‖ := by
            rw [hγ'_eq_left t_star ⟨ht_mem.1, le_rfl⟩]
            exact (hγ_phi t_star ⟨ht_mem.1, le_rfl⟩ htg).2
          have hΦ_s := phi_norm_le_along_lift P hΦ0 hΦ_deriv hφ_pos hP'_lb ht_mem.1 (le_of_lt ht'_gt)
            (hγ'_cont_right.congr hγ'_eq_right) hderiv_r hball_r hstart s ⟨le_of_lt hs_gt, hs.2⟩
          have hle_rg : ‖γ' s‖ ≤ r_gap := by
            by_contra hgt; push Not at hgt
            have hlt_r₁ := hball_r s ⟨le_of_lt hs_gt, hs.2⟩
            have hΦ_gt := hΦ_strict ⟨hr_gap_mem.1, hr_gap_mem.2⟩ ⟨norm_nonneg _, le_of_lt hlt_r₁⟩ hgt
            linarith [hr_gap_eq]
          exact ⟨hle_rg, hΦ_s⟩
      have hγ'_K : ∀ s ∈ Set.Icc 0 t', γ' s ∈ K_safe := by
        intro s hs
        by_cases hsg : s * ‖w‖ ≤ L_gap
        · exact Or.inl (by rw [Metric.mem_closedBall, dist_zero_right]; exact (hγ'_phi s hs hsg).1)
        · push Not at hsg
          refine Or.inr ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hγ'_M s hs, ?_⟩
          rw [Set.mem_setOf_eq, hγ'_P s hs, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]
          exact le_of_lt hsg
      have ht'_good : t' ∈ Good :=
        ⟨⟨le_trans ht_mem.1 (le_of_lt ht'_gt), ht'_le1⟩, γ', hγ'_cont, hγ'_0,
          fun s hs => ⟨hγ'_U s hs, hγ'_K s hs, hγ'_P s hs, hγ'_M s hs⟩, hγ'_phi⟩
      have hle_sup : t' ≤ t_star := le_csSup hGood_bdd ht'_good
      linarith
    -- Since t_star = 1 ∈ Good, extract the lift on [0, 1]!
    rw [ht_star_eq1] at ht_star_good
    rcases ht_star_good with ⟨_, γ, hγc, hγ0, hγ_all, _⟩
    exact ⟨γ, hγc, hγ0, hγ_all⟩
  -- Step 5: Define g : ℂ → ℂ on ball 0 L_max via g w = γ_w 1, prove Lipschitz continuity,
  -- holomorphicity, and apply Cauchy's estimate to get 1 ≤ M_bound / L_max < 1!
  classical
  let g : ℂ → ℂ := fun w =>
    if hw : w ∈ Metric.ball (0 : ℂ) L_max then (hex_lift w hw).choose 1 else 0
  have hg_props : ∀ w (hw : w ∈ Metric.ball (0 : ℂ) L_max),
      g w ∈ U ∧ g w ∈ K_safe ∧ P.eval (g w) = w ∧ ‖g w‖ ≤ M_bound := by
    intro w hw
    simp only [g, dif_pos hw]
    have hspec := (hex_lift w hw).choose_spec.2.2 1 ⟨zero_le_one, le_rfl⟩
    simpa using hspec
  have hg0 : g 0 = 0 := by
    have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) L_max := Metric.mem_ball_self hL_pos
    simp only [g, dif_pos h0mem]
    set γ₀ := (hex_lift 0 h0mem).choose
    have hspec := (hex_lift 0 h0mem).choose_spec
    have heq := lift_unique P (w := 0) zero_le_one hspec.1 continuousOn_const hspec.2.1 rfl
      (fun s hs => by simpa using (hspec.2.2 s hs).2.2.1)
      (fun s _ => by simp [hP0])
      (fun s hs => hK_safe_nd _ (hspec.2.2 s hs).2.1) 1 ⟨zero_le_one, le_rfl⟩
    exact heq
  -- Taylor bound on closedBall 0 M_bound gives local Lipschitz continuity of g!
  rcases poly_taylor_bound P M_bound (le_of_lt hM_pos) with ⟨C_t, hCt_pos, hTaylor⟩
  set ρ : ℝ := min 1 (c / (2 * C_t))
  have hρ_pos : 0 < ρ := lt_min one_pos (by positivity)
  have hρ_le1 : ρ ≤ 1 := min_le_left _ _
  have hρ_C : C_t * ρ ≤ c / 2 := by
    have h1 : ρ ≤ c / (2 * C_t) := min_le_right _ _
    have h2 : 0 < 2 * C_t := by positivity
    calc C_t * ρ ≤ C_t * (c / (2 * C_t)) := mul_le_mul_of_nonneg_left h1 (le_of_lt hCt_pos)
      _ = c / 2 := by field_simp [ne_of_gt hCt_pos]
  -- Core Taylor lower bound: if z₁ ∈ K_safe, ‖z₁‖ ≤ M_bound, ‖z₂ - z₁‖ ≤ ρ, then (c/2) * ‖z₂ - z₁‖ ≤ ‖P z₂ - P z₁‖
  have hP_lip_lb : ∀ z₁ z₂ : ℂ, z₁ ∈ K_safe → ‖z₁‖ ≤ M_bound → ‖z₂ - z₁‖ ≤ ρ →
      (c / 2) * ‖z₂ - z₁‖ ≤ ‖P.eval z₂ - P.eval z₁‖ := by
    intro z₁ z₂ hz₁K hz₁M hdiff
    set h := z₂ - z₁
    have hh1 : ‖h‖ ≤ 1 := le_trans hdiff hρ_le1
    have htay := hTaylor z₁ h hz₁M hh1
    have hz₂ : z₁ + h = z₂ := by dsimp [h]; ring
    rw [hz₂] at htay
    have hP'ge : c ≤ ‖(derivative P).eval z₁‖ := hc_lb z₁ hz₁K
    have hlin : c * ‖h‖ ≤ ‖(derivative P).eval z₁ * h‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right hP'ge (norm_nonneg h)
    have hquad : C_t * ‖h‖ ^ 2 ≤ (c / 2) * ‖h‖ := by
      have : C_t * ‖h‖ ≤ c / 2 := le_trans (mul_le_mul_of_nonneg_left hdiff (le_of_lt hCt_pos)) hρ_C
      nlinarith [norm_nonneg h]
    have htri : ‖(derivative P).eval z₁ * h‖ - ‖P.eval z₂ - P.eval z₁‖ ≤
        ‖P.eval z₂ - P.eval z₁ - (derivative P).eval z₁ * h‖ := by
      have := norm_sub_norm_le ((derivative P).eval z₁ * h) (P.eval z₂ - P.eval z₁)
      rw [norm_sub_rev ((derivative P).eval z₁ * h) (P.eval z₂ - P.eval z₁)] at this
      exact this
    linarith
  -- Prove g is continuous at every w₀ ∈ Metric.ball 0 L_max!
  have hg_cont : ∀ w₀ ∈ Metric.ball (0 : ℂ) L_max, ContinuousAt g w₀ := by
    intro w₀ hw₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hball_nhds : Metric.ball (0 : ℂ) L_max ∈ nhds w₀ := Metric.isOpen_ball.mem_nhds hw₀
    rw [Metric.mem_nhds_iff] at hball_nhds
    rcases hball_nhds with ⟨δ₁, hδ₁_pos, hδ₁_sub⟩
    set δ := min δ₁ (min ((c / 4) * ρ) ((c / 2) * ε))
    have hδ_pos : 0 < δ := lt_min hδ₁_pos (lt_min (by positivity) (by positivity))
    refine ⟨δ, hδ_pos, fun w hdist => ?_⟩
    have hw_ball : w ∈ Metric.ball (0 : ℂ) L_max :=
      hδ₁_sub (lt_of_lt_of_le hdist (min_le_left _ _))
    have hw_small : ‖w - w₀‖ < (c / 4) * ρ := by
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_left _ _))
    have hw_eps : ‖w - w₀‖ < (c / 2) * ε := by
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_right _ _))
    -- Compare γ_w and γ_{w₀} along s ∈ [0, 1] via IVT!
    set γ₀ := (hex_lift w₀ hw₀).choose
    set γ₁ := (hex_lift w hw_ball).choose
    have h0spec := (hex_lift w₀ hw₀).choose_spec
    have h1spec := (hex_lift w hw_ball).choose_spec
    have hd_cont : ContinuousOn (fun s => ‖γ₁ s - γ₀ s‖) (Set.Icc 0 1) :=
      (h1spec.1.sub h0spec.1).norm
    have hd_bound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖γ₁ s - γ₀ s‖ ≤ ρ →
        ‖γ₁ s - γ₀ s‖ ≤ (2 / c) * ‖w - w₀‖ := by
      intro s hs hle
      have h0s := h0spec.2.2 s hs
      have h1s := h1spec.2.2 s hs
      have hlb := hP_lip_lb (γ₀ s) (γ₁ s) h0s.2.1 h0s.2.2.2 hle
      rw [h1s.2.2.1, h0s.2.2.1, ← mul_sub, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hs.1] at hlb
      have hs1 : s * ‖w - w₀‖ ≤ ‖w - w₀‖ := by nlinarith [hs.2, norm_nonneg (w - w₀)]
      have hlb2 : (c / 2) * ‖γ₁ s - γ₀ s‖ ≤ ‖w - w₀‖ := le_trans hlb hs1
      have h2c : (2 / c) * ((c / 2) * ‖γ₁ s - γ₀ s‖) = ‖γ₁ s - γ₀ s‖ := by
        field_simp [ne_of_gt hc_pos]
      rw [← h2c]
      exact mul_le_mul_of_nonneg_left hlb2 (by positivity)
    have hall_le_ρ : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖γ₁ s - γ₀ s‖ ≤ ρ := by
      intro s hs
      by_contra hgt; push Not at hgt
      have hd0 : ‖γ₁ 0 - γ₀ 0‖ = 0 := by dsimp [γ₁, γ₀]; rw [h1spec.2.1, h0spec.2.1, sub_self, norm_zero]
      have hmem : ρ ∈ Set.Icc ‖γ₁ 0 - γ₀ 0‖ ‖γ₁ s - γ₀ s‖ := ⟨by linarith, le_of_lt hgt⟩
      obtain ⟨s', hs', hds'⟩ :=
        intermediate_value_Icc hs.1 (hd_cont.mono (Set.Icc_subset_Icc_right hs.2)) hmem
      have hle_half := hd_bound s' ⟨hs'.1, le_trans hs'.2 hs.2⟩ (le_of_eq hds')
      have hlt_half : (2 / c) * ‖w - w₀‖ < ρ / 2 := by
        have h1 : (2 / c) * ((c / 4) * ρ) = ρ / 2 := by field_simp [ne_of_gt hc_pos]; ring
        rw [← h1]
        exact mul_lt_mul_of_pos_left hw_small (by positivity)
      linarith
    have h1_bound := hd_bound 1 ⟨zero_le_one, le_rfl⟩ (hall_le_ρ 1 ⟨zero_le_one, le_rfl⟩)
    rw [dist_eq_norm]
    simp only [g, dif_pos hw_ball, dif_pos hw₀]
    have hlt_eps : (2 / c) * ‖w - w₀‖ < ε := by
      have h1 : (2 / c) * ((c / 2) * ε) = ε := by field_simp [ne_of_gt hc_pos]
      rw [← h1]
      exact mul_lt_mul_of_pos_left hw_eps (by positivity)
    exact lt_of_le_of_lt h1_bound hlt_eps
  -- Step 6: g is holomorphic on Metric.ball 0 L_max with g'(0) = 1!
  have hg_deriv : ∀ w₀ ∈ Metric.ball (0 : ℂ) L_max,
      HasDerivAt g (((derivative P).eval (g w₀))⁻¹) w₀ := by
    intro w₀ hw₀
    apply hasDerivAt_of_rightInverse P (hg_cont w₀ hw₀)
    · filter_upwards [Metric.isOpen_ball.mem_nhds hw₀] with w hw
      exact (hg_props w hw).2.2.1
    · exact hK_safe_nd (g w₀) (hg_props w₀ hw₀).2.1
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 L_max) :=
    fun w hw => (hg_deriv w hw).differentiableAt.differentiableWithinAt
  have hg_maps : Set.MapsTo g (Metric.ball 0 L_max) (Metric.closedBall (g 0) M_bound) := by
    intro w hw
    rw [Metric.mem_closedBall, hg0, dist_zero_right]
    exact (hg_props w hw).2.2.2
  have hcauchy := Complex.norm_deriv_le_div_of_mapsTo_ball hg_diff hg_maps hL_pos
  have hg'0 : deriv g 0 = 1 := by
    have h := (hg_deriv 0 (Metric.mem_ball_self hL_pos)).deriv
    rw [hg0, hP'0, inv_one] at h
    exact h
  rw [hg'0, norm_one] at hcauchy
  have hlt1 : M_bound / L_max < 1 := (div_lt_one hL_pos).mpr hM_lt
  linarith

/-! ### Section 5: Global & Confined Corollaries -/

/-- **Global Radial-Lift Critical Value Theorem**:
    For any polynomial `P ∈ ℂ[X]` of degree `≥ 2` with `P(0) = 0`, `P'(0) = 1`, and any
    C^1 radial comparison function `Φ` on `[0, r₁]` with `Φ 0 = 0`, `Φ' = φ > 0` on `[0, r₁)`,
    and `φ ‖z‖ ≤ ‖P'(z)‖` for `‖z‖ < r₁`, there exists a critical point `ζ` of `P` with
    `Φ r₁ ≤ ‖P.eval ζ‖`. -/
theorem radial_lift_critical_value_ge (P : ℂ[X])
    (hdeg : 2 ≤ P.natDegree)
    (hP0 : P.eval 0 = 0) (hP'0 : (derivative P).eval 0 = 1)
    {r₁ : ℝ} (hr₁ : 0 < r₁)
    {Φ φ : ℝ → ℝ} (hΦ0 : Φ 0 = 0)
    (hΦ_cont : ContinuousOn Φ (Set.Icc 0 r₁))
    (hΦ_deriv : ∀ r ∈ Set.Ico 0 r₁, HasDerivAt Φ (φ r) r)
    (hφ_pos : ∀ r ∈ Set.Ico 0 r₁, 0 < φ r)
    (hP'_lb : ∀ z : ℂ, ‖z‖ < r₁ → φ ‖z‖ ≤ ‖(derivative P).eval z‖) :
    ∃ ζ : ℂ, (derivative P).eval ζ = 0 ∧ Φ r₁ ≤ ‖P.eval ζ‖ := by
  -- Since deg P ≥ 2, P = X * Q with deg Q ≥ 1, so ‖Q z‖ → ∞ as ‖z‖ → ∞.
  -- Hence ∃ M₀ > 0 such that ∀ z, M₀ ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖P z‖!
  have hXdvd : X ∣ P := Polynomial.X_dvd_iff.mpr (by simpa [Polynomial.coeff_zero_eq_eval_zero] using hP0)
  rcases hXdvd with ⟨Q, hPQ⟩
  have hQne : Q ≠ 0 := by intro h0; rw [h0, mul_zero] at hPQ; rw [hPQ] at hdeg; simp at hdeg
  have hQdeg : 0 < Q.degree := by
    have h1 : P.natDegree = 1 + Q.natDegree := by
      rw [hPQ, Polynomial.natDegree_mul X_ne_zero hQne, Polynomial.natDegree_X]
    rw [Polynomial.degree_eq_natDegree hQne]
    exact_mod_cast (show 0 < Q.natDegree by omega)
  have hQlim : Filter.Tendsto (fun z : ℂ => ‖Q.eval z‖) (Filter.cocompact ℂ) Filter.atTop :=
    Polynomial.tendsto_norm_atTop Q hQdeg (tendsto_norm_cocompact_atTop (E := ℂ))
  have hev := hQlim.eventually (Filter.eventually_ge_atTop (2 : ℝ))
  rcases (Filter.hasBasis_cocompact.eventually_iff).mp hev with ⟨s, hs_comp, hs_out⟩
  rcases hs_comp.isBounded.subset_closedBall (0 : ℂ) with ⟨R0, hR0⟩
  set M₀ : ℝ := max (max R0 1) (|Φ r₁| + 1)
  have hM₀_pos : 0 < M₀ := lt_of_lt_of_le one_pos (le_trans (le_max_right R0 1) (le_max_left _ _))
  set L_max : ℝ := 2 * M₀
  have hL_gt : Φ r₁ < L_max := by
    have h1 : |Φ r₁| + 1 ≤ M₀ := le_max_right _ _
    have h2 : Φ r₁ ≤ |Φ r₁| := le_abs_self _
    linarith
  have hPre : ∀ z ∈ (Set.univ : Set ℂ), ‖P.eval z‖ < L_max → ‖z‖ ≤ M₀ := by
    intro z _ hPz
    by_contra hgt; push Not at hgt
    have hz_not_s : z ∉ s := by
      intro hzs
      have h1 := hR0 hzs
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      have h2 : R0 ≤ M₀ := le_trans (le_max_left R0 1) (le_max_left _ _)
      linarith
    have hQz : 2 ≤ ‖Q.eval z‖ := hs_out hz_not_s
    have hPeq : ‖P.eval z‖ = ‖z‖ * ‖Q.eval z‖ := by rw [hPQ, eval_mul, eval_X, norm_mul]
    rw [hPeq] at hPz
    nlinarith [norm_nonneg z]
  obtain ⟨ζ, _, hζ0, hζv⟩ := radial_lift_obstruction P hP0 hP'0 hr₁ hΦ0 hΦ_cont hΦ_deriv hφ_pos
    hP'_lb isOpen_univ (Set.subset_univ _) hL_gt hM₀_pos (by dsimp [L_max]; linarith)
    (Set.subset_univ _) hPre
  exact ⟨ζ, hζ0, hζv⟩

/-- **Confined Radial-Lift Critical Value Theorem**:
    If `r₁ < R`, `Φ r₁ < R`, and `R < ‖P.eval z‖` everywhere on the circle `‖z‖ = R`,
    then there exists a critical point `ζ` strictly INSIDE `‖ζ‖ < R` with `Φ r₁ ≤ ‖P.eval ζ‖`! -/
theorem radial_lift_confined_critical_value_ge (P : ℂ[X])
    (hP0 : P.eval 0 = 0) (hP'0 : (derivative P).eval 0 = 1)
    {r₁ R : ℝ} (hr₁ : 0 < r₁) (hr₁R : r₁ < R)
    {Φ φ : ℝ → ℝ} (hΦ0 : Φ 0 = 0)
    (hΦ_cont : ContinuousOn Φ (Set.Icc 0 r₁))
    (hΦ_deriv : ∀ r ∈ Set.Ico 0 r₁, HasDerivAt Φ (φ r) r)
    (hφ_pos : ∀ r ∈ Set.Ico 0 r₁, 0 < φ r)
    (hP'_lb : ∀ z : ℂ, ‖z‖ < r₁ → φ ‖z‖ ≤ ‖(derivative P).eval z‖)
    (hΦ_lt_R : Φ r₁ < R)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → R < ‖P.eval z‖) :
    ∃ ζ : ℂ, ‖ζ‖ < R ∧ (derivative P).eval ζ = 0 ∧ Φ r₁ ≤ ‖P.eval ζ‖ := by
  have hR_pos : 0 < R := lt_trans hr₁ hr₁R
  -- Compactness of the circle {z | ‖z‖ = R} gives L₀ = min_{‖z‖ = R} ‖P z‖ > R!
  have hsph_comp : IsCompact (Metric.sphere (0 : ℂ) R) := isCompact_sphere 0 R
  have hsph_ne : (Metric.sphere (0 : ℂ) R).Nonempty :=
    ⟨(R : ℂ), by rw [Metric.mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hR_pos)]⟩
  obtain ⟨z_sph, hz_sph_mem, hz_sph_min⟩ :=
    hsph_comp.exists_isMinOn hsph_ne P.continuous.norm.continuousOn
  set L₀ : ℝ := ‖P.eval z_sph‖
  have hL₀_gt : R < L₀ := hcircle z_sph (by simpa [Metric.mem_sphere, dist_zero_right] using hz_sph_mem)
  set L_max : ℝ := (R + L₀) / 2
  have hL_gt_R : R < L_max := by dsimp [L_max]; linarith
  have hL_lt_L₀ : L_max < L₀ := by dsimp [L_max]; linarith
  -- Compactness of {z ∈ closedBall 0 R | ‖P z‖ ≤ L_max}: it is disjoint from sphere 0 R,
  -- hence attains a maximum modulus M_bound < R!
  set S_in : Set ℂ := Metric.closedBall 0 R ∩ {z : ℂ | ‖P.eval z‖ ≤ L_max}
  have hSin_comp : IsCompact S_in :=
    (isCompact_closedBall (0 : ℂ) R).inter_right (isClosed_le P.continuous.norm continuous_const)
  have hSin_ne : S_in.Nonempty :=
    ⟨0, Metric.mem_closedBall_self (le_of_lt hR_pos), by simp [hP0]; linarith⟩
  obtain ⟨z_max, hz_max_mem, hz_max⟩ := hSin_comp.exists_isMaxOn hSin_ne continuous_norm.continuousOn
  have hz_max_lt : ‖z_max‖ < R := by
    have hle : ‖z_max‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hz_max_mem.1
    refine lt_of_le_of_ne hle (fun heq => ?_)
    have hmem_sph : z_max ∈ Metric.sphere (0 : ℂ) R := by
      rw [Metric.mem_sphere, dist_zero_right]; exact heq
    have hge : L₀ ≤ ‖P.eval z_max‖ := hz_sph_min hmem_sph
    have hle2 : ‖P.eval z_max‖ ≤ L_max := hz_max_mem.2
    linarith
  set M_bound : ℝ := max ‖z_max‖ (R / 2)
  have hM_pos : 0 < M_bound := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hM_lt_R : M_bound < R := max_lt hz_max_lt (by linarith)
  have hK_sub : Metric.closedBall (0 : ℂ) M_bound ⊆ Metric.ball (0 : ℂ) R := fun z hz => by
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz hM_lt_R
  have hPre : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖P.eval z‖ < L_max → ‖z‖ ≤ M_bound := by
    intro z hz hPz
    have hz_in : z ∈ S_in :=
      ⟨Metric.ball_subset_closedBall hz, le_of_lt hPz⟩
    exact le_trans (hz_max hz_in) (le_max_left _ _)
  obtain ⟨ζ, hζU, hζ0, hζv⟩ := radial_lift_obstruction P hP0 hP'0 hr₁ hΦ0 hΦ_cont hΦ_deriv hφ_pos
    hP'_lb Metric.isOpen_ball (Metric.ball_subset_ball (le_of_lt hr₁R))
    (lt_trans hΦ_lt_R hL_gt_R) hM_pos (lt_trans hM_lt_R hL_gt_R) hK_sub hPre
  exact ⟨ζ, by simpa [Metric.mem_ball, dist_zero_right] using hζU, hζ0, hζv⟩

end DualSmaleMultiscale

