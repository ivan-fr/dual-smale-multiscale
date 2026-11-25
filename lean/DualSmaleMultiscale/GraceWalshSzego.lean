/-
  DualSmale/GraceWalshSzego.lean

  Self-contained Lean 4 proof of Laguerre's Polar Derivative Theorem and the
  Grace-Walsh-Szego Coincidence Theorem on the closed unit disk `|z| <= 1`
  (including the two-block corollary used in the degree-8 Dual Smale proof).
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators
open Polynomial Complex

namespace DualSmale

/-- Key algebraic identity for Laguerre's polar derivative theorem on the closed unit disk:
    for any `a, w, z : ℂ` with `a ≠ z`, letting `t = (a - w) / (a - z)`, we have
    `2 * Re((1 - z * conj w) * t) = (1 - ‖z‖^2) * ‖t‖^2 + (1 - ‖w‖^2) + (‖a‖^2 - 1) * ‖z - w‖^2 / ‖a - z‖^2`. -/
lemma mobius_re_pos_of_norm_gt {a w z : ℂ} (ha : 1 < ‖a‖) (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (hwz : w ≠ z) :
    0 < ((1 - z * starRingEnd ℂ w) * ((a - w) / (a - z))).re := by
  have haz : a - z ≠ 0 := by
    intro h
    have h1 : a = z := sub_eq_zero.mp h
    rw [h1] at ha
    linarith
  set t : ℂ := (a - w) / (a - z)
  have ht1 : t - 1 = (z - w) / (a - z) := by
    dsimp [t]
    field_simp [haz]
    ring
  have htz : t * z - w = a * ((z - w) / (a - z)) := by
    dsimp [t]
    field_simp [haz]
    ring
  -- Use Complex.normSq identity: normSq(t*z - w) - normSq(t - 1) = (normSq a - 1) * normSq((z - w)/(a - z))
  have h_ns : Complex.normSq (t * z - w) - Complex.normSq (t - 1) =
      (Complex.normSq a - 1) * Complex.normSq ((z - w) / (a - z)) := by
    rw [htz, ht1, map_mul]
    ring
  -- Direct expansion of the LHS in terms of real and imaginary parts
  have h_exp : Complex.normSq (t * z - w) - Complex.normSq (t - 1) =
      2 * ((1 - z * starRingEnd ℂ w) * t).re -
      (1 - Complex.normSq z) * Complex.normSq t - (1 - Complex.normSq w) := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]
    ring
  have ha2 : 1 < Complex.normSq a := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hw2 : Complex.normSq w ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hz2 : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hzw : z - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hwz)
  have hfrac_pos : 0 < Complex.normSq ((z - w) / (a - z)) :=
    Complex.normSq_pos.mpr (div_ne_zero hzw haz)
  have ht_nonneg : 0 ≤ Complex.normSq t := Complex.normSq_nonneg t
  nlinarith

/-- For `‖z‖ ≤ 1`, `‖w‖ ≤ 1`, `w ≠ z`, we have `0 < (1 - z * conj w).re`. -/
lemma one_sub_mul_conj_re_pos {w z : ℂ} (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1) (hwz : w ≠ z) :
    0 < (1 - z * starRingEnd ℂ w).re := by
  have h_id : 2 * (1 - z * starRingEnd ℂ w).re =
      (1 - Complex.normSq z) + (1 - Complex.normSq w) + Complex.normSq (z - w) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.one_re, Complex.conj_re, Complex.conj_im]
    ring
  have hw2 : Complex.normSq w ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have hz2 : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hzw : 0 < Complex.normSq (z - w) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hwz))
  linarith

/-- Polar derivative of a polynomial `P` of formal degree `m` with respect to pole `w`. -/
noncomputable def polarDeriv (m : ℕ) (w : ℂ) (P : ℂ[X]) : ℂ[X] :=
  C (m : ℂ) * P + (C w - X) * derivative P

/-- Evaluation of `polarDeriv m w P` on a factored polynomial `C c * ∏ (X - C a_i)` at `z`
    when `P.eval z ≠ 0`. -/
lemma eval_polarDeriv_factored (m : ℕ) (w z c : ℂ) (roots : Multiset ℂ)
    (hz_ne : ∀ a ∈ roots, z - a ≠ 0) :
    (polarDeriv m w (C c * (roots.map (fun a => X - C a)).prod)).eval z =
      c * (roots.map (fun a => z - a)).prod *
        (((m : ℂ) - (roots.card : ℂ)) + (roots.map (fun a => (a - w) / (a - z))).sum) := by
  classical
  -- Induct on `roots` as a Multiset
  induction roots using Multiset.induction_on with
  | empty =>
    simp [polarDeriv]; ring
  | cons a s ih =>
    have ha_ne : z - a ≠ 0 := hz_ne a (Multiset.mem_cons_self a s)
    have hs_ne : ∀ b ∈ s, z - b ≠ 0 := fun b hb => hz_ne b (Multiset.mem_cons_of_mem hb)
    have h_ih := ih hs_ne
    set Q : ℂ[X] := C c * (s.map (fun b => X - C b)).prod
    have hPQ : C c * ((a ::ₘ s).map (fun b => X - C b)).prod = (X - C a) * Q := by
      simp [Q, Multiset.map_cons, Multiset.prod_cons]
      ring
    have h_pd : polarDeriv m w ((X - C a) * Q) =
        (X - C a) * polarDeriv m w Q + (C w - X) * Q := by
      unfold polarDeriv
      rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
      ring
    rw [hPQ, h_pd, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_mul, eval_sub,
      eval_C, eval_X, h_ih]
    have hQeval : Q.eval z = c * (s.map (fun b => z - b)).prod := by
      simp [Q, eval_mul, eval_C, Polynomial.eval_multiset_prod, Multiset.map_map]
    rw [hQeval, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons,
      Multiset.map_cons, Multiset.sum_cons]
    have haz : a - z ≠ 0 := fun h => ha_ne (by linear_combination -h)
    push_cast
    field_simp [haz]
    ring

/-- **Laguerre's Polar Derivative Theorem on the Closed Unit Disk**:
    If `P ∈ ℂ[X]` has `P.natDegree ≤ m` (`m ≥ 1`) and no root in `{z : ℂ | ‖z‖ ≤ 1}`,
    then for every `w` with `‖w‖ ≤ 1`, `polarDeriv m w P` has no root in `{z : ℂ | ‖z‖ ≤ 1}`. -/
theorem laguerre_polar_outside_closedUnitDisk {m : ℕ} (hm : 1 ≤ m) {P : ℂ[X]}
    (hdeg : P.natDegree ≤ m) (hno : ∀ z : ℂ, ‖z‖ ≤ 1 → P.eval z ≠ 0)
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → (polarDeriv m w P).eval z ≠ 0 := by
  intro z hz hzero
  have hP0 : P ≠ 0 := by
    intro h; exact hno 0 (by simp) (by simp [h])
  -- Factor P over ℂ using algebraic closedness
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hcard : P.roots.card = P.natDegree := hsplit.natDegree_eq_card_roots.symm
  have hfac : C P.leadingCoeff * (P.roots.map fun a => X - C a).prod = P :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  -- Every root of P has norm > 1
  have hroots_gt : ∀ a ∈ P.roots, 1 < ‖a‖ := by
    intro a ha
    by_contra hle
    push Not at hle
    have h0 : P.eval a = 0 := (Polynomial.mem_roots hP0).mp ha
    exact hno a hle h0
  have hz_ne : ∀ a ∈ P.roots, z - a ≠ 0 := by
    intro a ha hza
    have h1 : a = z := (sub_eq_zero.mp hza).symm
    have hgt := hroots_gt a ha
    rw [h1] at hgt
    linarith
  -- Apply factored evaluation formula
  have h_eval := eval_polarDeriv_factored m w z P.leadingCoeff P.roots hz_ne
  rw [hfac] at h_eval
  rw [h_eval] at hzero
  have hprod_ne : (P.roots.map (fun a => z - a)).prod ≠ 0 := by
    intro hp
    rw [Multiset.prod_eq_zero_iff] at hp
    rcases Multiset.mem_map.mp hp with ⟨a, ha, hza⟩
    exact hz_ne a ha hza
  have hsum_zero : ((m : ℂ) - (P.roots.card : ℂ)) +
      (P.roots.map (fun a => (a - w) / (a - z))).sum = 0 := by
    have hmul_ne : P.leadingCoeff * (P.roots.map (fun a => z - a)).prod ≠ 0 :=
      mul_ne_zero hlc hprod_ne
    exact (mul_eq_zero.mp hzero).resolve_left hmul_ne
  -- Case 1: w = z
  by_cases hwz : w = z
  · subst hwz
    have hmap : P.roots.map (fun a => (a - w) / (a - w)) = Multiset.replicate P.roots.card (1 : ℂ) := by
      apply Multiset.eq_replicate.mpr
      refine ⟨by simp, fun x hx => ?_⟩
      rcases Multiset.mem_map.mp hx with ⟨a, ha, rfl⟩
      have haz : a - w ≠ 0 := fun h => hz_ne a ha (by linear_combination -h)
      exact div_self haz
    rw [hmap, Multiset.sum_replicate, nsmul_eq_mul, mul_one] at hsum_zero
    have hm_zero : (m : ℂ) = 0 := by linear_combination hsum_zero
    have hm0 : m = 0 := Nat.cast_eq_zero.mp hm_zero
    omega
  -- Case 2: w ≠ z -> multiply by (1 - z * conj w) and take real part > 0!
  · set u : ℂ := 1 - z * starRingEnd ℂ w
    have hu_re_pos : 0 < u.re := one_sub_mul_conj_re_pos hw hz hwz
    have hmul0 : (u * (((m : ℂ) - (P.roots.card : ℂ)) +
        (P.roots.map (fun a => (a - w) / (a - z))).sum)).re = 0 := by
      rw [hsum_zero, mul_zero, Complex.zero_re]
    have h_term1 : 0 ≤ (u * ((m : ℂ) - (P.roots.card : ℂ))).re := by
      have hcard_le : P.roots.card ≤ m := hcard ▸ hdeg
      have hsub : ((m : ℂ) - (P.roots.card : ℂ)) = ((m - P.roots.card : ℕ) : ℂ) := by
        rw [Nat.cast_sub hcard_le]
      rw [hsub]
      simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
      exact mul_nonneg (le_of_lt hu_re_pos) (Nat.cast_nonneg _)
    -- Helper: sum of real parts of u * ((a - w)/(a - z)) is >= 0, and > 0 if P.roots is nonempty
    have h_sum_re : ∀ s : Multiset ℂ, (∀ a ∈ s, 1 < ‖a‖) →
        0 ≤ (u * (s.map (fun a => (a - w) / (a - z))).sum).re ∧
        (s ≠ 0 → 0 < (u * (s.map (fun a => (a - w) / (a - z))).sum).re) := by
      intro s
      induction s using Multiset.induction_on with
      | empty =>
        intro _
        exact ⟨by simp, fun h => (h rfl).elim⟩
      | cons a s ih =>
        intro hall
        have ha : 1 < ‖a‖ := hall a (Multiset.mem_cons_self a s)
        have hs : ∀ b ∈ s, 1 < ‖b‖ := fun b hb => hall b (Multiset.mem_cons_of_mem hb)
        have hpos_a : 0 < (u * ((a - w) / (a - z))).re := mobius_re_pos_of_norm_gt ha hw hz hwz
        have hge_s := (ih hs).1
        rw [Multiset.map_cons, Multiset.sum_cons, mul_add, Complex.add_re]
        exact ⟨by linarith, fun _ => by linarith⟩
    have h_re := h_sum_re P.roots hroots_gt
    rw [mul_add, Complex.add_re] at hmul0
    by_cases hne : P.roots = 0
    · have hcard0 : P.roots.card = 0 := by rw [hne]; rfl
      have hpos1 : 0 < (u * ((m : ℂ) - (P.roots.card : ℂ))).re := by
        rw [hcard0, Nat.cast_zero, sub_zero]
        simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
        have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
        exact mul_pos hu_re_pos hm_pos
      linarith [h_re.1]
    · linarith [h_re.2 hne]

/-- Elementary symmetric polynomial `e_k(z_0, ..., z_{m-1})` of degree `k` in `m` variables. -/
noncomputable def elemSym : (m : ℕ) → (Fin m → ℂ) → ℕ → ℂ
  | 0, _, 0 => 1
  | 0, _, _ + 1 => 0
  | _ + 1, _, 0 => 1
  | m + 1, z, k + 1 =>
      elemSym m (fun i => z i.castSucc) (k + 1) +
      z (Fin.last m) * elemSym m (fun i => z i.castSucc) k

lemma elemSym_const (m : ℕ) (ζ : ℂ) : ∀ k, elemSym m (fun _ => ζ) k = (Nat.choose m k : ℂ) * ζ ^ k := by
  induction m with
  | zero =>
    intro k
    cases k <;> simp [elemSym]
  | succ m ih =>
    intro k
    cases k with
    | zero => simp [elemSym]
    | succ k =>
      simp only [elemSym, ih, Nat.choose_succ_succ, Nat.cast_add]
      ring

/-- Symmetric multiaffine form `F_m(c; z) = ∑_{k=0}^m c_k * e_k(z)`. -/
noncomputable def symMultiaffine (m : ℕ) (c : ℕ → ℂ) (z : Fin m → ℂ) : ℂ :=
  ∑ k ∈ Finset.range (m + 1), c k * elemSym m z k

/-- Diagonal polynomial `P_m(c)(X) = ∑_{k=0}^m C(m, k) * c_k * X^k`. -/
noncomputable def diagPoly (m : ℕ) (c : ℕ → ℂ) : ℂ[X] :=
  ∑ k ∈ Finset.range (m + 1), C ((Nat.choose m k : ℂ) * c k) * X ^ k

lemma eval_diagPoly (m : ℕ) (c : ℕ → ℂ) (ζ : ℂ) :
    (diagPoly m c).eval ζ = symMultiaffine m c (fun _ => ζ) := by
  unfold diagPoly symMultiaffine
  change (Polynomial.evalRingHom ζ) _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (C ((Nat.choose m k : ℂ) * c k) * X ^ k).eval ζ = _
  rw [eval_mul, eval_C, eval_pow, eval_X, elemSym_const]
  ring

lemma natDegree_diagPoly_le (m : ℕ) (c : ℕ → ℂ) : (diagPoly m c).natDegree ≤ m := by
  unfold diagPoly
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le m, fun k hk => ?_⟩
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) hkm

/-- Splitting off the last variable `z (Fin.last m)` from `symMultiaffine (m + 1)`. -/
lemma symMultiaffine_succ (m : ℕ) (c : ℕ → ℂ) (z : Fin (m + 1) → ℂ) :
    symMultiaffine (m + 1) c z =
      symMultiaffine m (fun k => c k + z (Fin.last m) * c (k + 1)) (fun i => z i.castSucc) := by
  unfold symMultiaffine
  have h_zero : elemSym m (fun i => z i.castSucc) (m + 1) = 0 := by
    clear c
    induction m with
    | zero => simp [elemSym]
    | succ m ih =>
      -- General helper: elemSym n v k = 0 for k > n
      have hgt : ∀ (n : ℕ) (v : Fin n → ℂ) (k : ℕ), n < k → elemSym n v k = 0 := by
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
      exact hgt (m + 1) _ (m + 2) (by omega)
  -- Split off k = 0 and k = m + 1
  rw [Finset.sum_range_succ']
  simp only [elemSym, mul_one]
  -- Now LHS = ∑_{k=0}^m c (k+1) * (e_{k+1} + w * e_k) + c 0
  have hsplit : ∑ k ∈ Finset.range (m + 1),
      c (k + 1) * (elemSym m (fun i => z i.castSucc) (k + 1) +
        z (Fin.last m) * elemSym m (fun i => z i.castSucc) k) =
      (∑ k ∈ Finset.range (m + 1), c (k + 1) * elemSym m (fun i => z i.castSucc) (k + 1)) +
      (∑ k ∈ Finset.range (m + 1), z (Fin.last m) * c (k + 1) * elemSym m (fun i => z i.castSucc) k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [hsplit]
  have hshift : (∑ k ∈ Finset.range (m + 1), c (k + 1) * elemSym m (fun i => z i.castSucc) (k + 1)) + c 0 =
      ∑ k ∈ Finset.range (m + 1), c k * elemSym m (fun i => z i.castSucc) k := by
    rw [Finset.sum_range_succ, h_zero, mul_zero, add_zero]
    rw [Finset.sum_range_succ']
    have he0 : elemSym m (fun i => z i.castSucc) 0 = 1 := by cases m <;> rfl
    rw [he0, mul_one]
  calc
    (∑ k ∈ Finset.range (m + 1), c (k + 1) * elemSym m (fun i => z i.castSucc) (k + 1)) +
        (∑ k ∈ Finset.range (m + 1), z (Fin.last m) * c (k + 1) * elemSym m (fun i => z i.castSucc) k) + c 0
      = ((∑ k ∈ Finset.range (m + 1), c (k + 1) * elemSym m (fun i => z i.castSucc) (k + 1)) + c 0) +
        (∑ k ∈ Finset.range (m + 1), z (Fin.last m) * c (k + 1) * elemSym m (fun i => z i.castSucc) k) := by ring
    _ = (∑ k ∈ Finset.range (m + 1), c k * elemSym m (fun i => z i.castSucc) k) +
        (∑ k ∈ Finset.range (m + 1), z (Fin.last m) * c (k + 1) * elemSym m (fun i => z i.castSucc) k) := by rw [hshift]
    _ = ∑ k ∈ Finset.range (m + 1), (c k + z (Fin.last m) * c (k + 1)) * elemSym m (fun i => z i.castSucc) k := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring

/-- Exact identity connecting `polarDeriv (m + 1) w (diagPoly (m + 1) c)` to `diagPoly m`! -/
lemma polarDeriv_diagPoly_succ (m : ℕ) (w : ℂ) (c : ℕ → ℂ) :
    polarDeriv (m + 1) w (diagPoly (m + 1) c) =
      C ((m + 1 : ℕ) : ℂ) * diagPoly m (fun k => c k + w * c (k + 1)) := by
  apply Polynomial.funext
  intro ζ
  -- Evaluate both sides at ζ directly!
  have h_deriv : (derivative (diagPoly (m + 1) c)).eval ζ =
      ∑ k ∈ Finset.range (m + 1),
        ((Nat.choose (m + 1) (k + 1) : ℂ) * c (k + 1) * ((k + 1 : ℕ) : ℂ)) * ζ ^ k := by
    unfold diagPoly
    rw [map_sum]
    change (Polynomial.evalRingHom ζ) _ = _
    rw [map_sum, Finset.sum_range_succ']
    simp only [Polynomial.coe_evalRingHom, pow_zero, mul_one, derivative_C, eval_zero, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow]
    simp only [eval_mul, eval_C, eval_pow, eval_X, Nat.add_sub_cancel]
    ring
  simp only [polarDeriv, eval_add, eval_mul, eval_C, eval_sub, eval_X, h_deriv]
  rw [eval_diagPoly, eval_diagPoly]
  unfold symMultiaffine
  simp only [elemSym_const]
  -- Expand LHS and compare coefficient of ζ^k term by term
  have h1 : ((m + 1 : ℕ) : ℂ) * (∑ k ∈ Finset.range (m + 2), c k * ((Nat.choose (m + 1) k : ℂ) * ζ ^ k)) -
      ζ * (∑ k ∈ Finset.range (m + 1), ((Nat.choose (m + 1) (k + 1) : ℂ) * c (k + 1) * ((k + 1 : ℕ) : ℂ)) * ζ ^ k) =
      ∑ k ∈ Finset.range (m + 1), ((m + 1 : ℕ) : ℂ) * ((Nat.choose m k : ℂ) * c k * ζ ^ k) := by
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul, mul_add]
    rw [Finset.mul_sum]
    have hshift : ζ * (∑ k ∈ Finset.range (m + 1),
        ((Nat.choose (m + 1) (k + 1) : ℂ) * c (k + 1) * ((k + 1 : ℕ) : ℂ)) * ζ ^ k) =
        (∑ k ∈ Finset.range (m + 1), ((k : ℂ) * (Nat.choose (m + 1) k : ℂ) * c k) * ζ ^ k) +
        (((m + 1 : ℕ) : ℂ) * c (m + 1) * ζ ^ (m + 1)) := by
      rw [Finset.mul_sum]
      have hterm : ∀ k, ζ * (((Nat.choose (m + 1) (k + 1) : ℂ) * c (k + 1) * ((k + 1 : ℕ) : ℂ)) * ζ ^ k) =
          (((k + 1 : ℕ) : ℂ) * (Nat.choose (m + 1) (k + 1) : ℂ) * c (k + 1)) * ζ ^ (k + 1) := by
        intro k; ring
      simp_rw [hterm]
      rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one]
      have h0 : ∑ k ∈ Finset.range (m + 1), ((k : ℂ) * (Nat.choose (m + 1) k : ℂ) * c k) * ζ ^ k =
          ∑ k ∈ Finset.range m, (((k + 1 : ℕ) : ℂ) * (Nat.choose (m + 1) (k + 1) : ℂ) * c (k + 1)) * ζ ^ (k + 1) := by
        rw [Finset.sum_range_succ']; simp
      rw [h0]
    rw [hshift]
    have hsub : (∑ k ∈ Finset.range (m + 1), ((m + 1 : ℕ) : ℂ) * (c k * ((Nat.choose (m + 1) k : ℂ) * ζ ^ k))) +
        ((m + 1 : ℕ) : ℂ) * (c (m + 1) * ζ ^ (m + 1)) -
        ((∑ k ∈ Finset.range (m + 1), ((k : ℂ) * (Nat.choose (m + 1) k : ℂ) * c k) * ζ ^ k) +
          ((m + 1 : ℕ) : ℂ) * c (m + 1) * ζ ^ (m + 1)) =
        ∑ k ∈ Finset.range (m + 1),
          (((m + 1 : ℕ) : ℂ) - (k : ℂ)) * (Nat.choose (m + 1) k : ℂ) * c k * ζ ^ k := by
      have hcancel : ∀ A B C : ℂ, A + C - (B + C) = A - B := fun _ _ _ => by ring
      have hC : ((m + 1 : ℕ) : ℂ) * (c (m + 1) * ζ ^ (m + 1)) = ((m + 1 : ℕ) : ℂ) * c (m + 1) * ζ ^ (m + 1) := by ring
      rw [hC, hcancel, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _; ring
    rw [hsub]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    -- Combinatorial identity: (m + 1 - k) * C(m + 1, k) = (m + 1) * C(m, k)
    have hcomb : (m + 1 - k) * Nat.choose (m + 1) k = (m + 1) * Nat.choose m k := by
      have h1 := Nat.choose_mul_succ_eq m k
      -- Wait: C(m+1, k) * (m + 1 - k) = (m + 1) * C(m, k) via symmetry!
      have hsym1 : Nat.choose (m + 1) k = Nat.choose (m + 1) (m + 1 - k) :=
        (Nat.choose_symm (by omega)).symm
      have hsym2 : Nat.choose m k = Nat.choose m (m - k) := (Nat.choose_symm hkm).symm
      rw [hsym1, hsym2]
      have hsucc : m + 1 - k = (m - k) + 1 := by omega
      rw [hsucc]
      have hrec := Nat.add_one_mul_choose_eq m (m - k)
      linarith
    have hcombC : (((m + 1 : ℕ) : ℂ) - (k : ℂ)) * (Nat.choose (m + 1) k : ℂ) =
        ((m + 1 : ℕ) : ℂ) * (Nat.choose m k : ℂ) := by
      have hsub_nat : (((m + 1 : ℕ) : ℂ) - (k : ℂ)) = ((m + 1 - k : ℕ) : ℂ) := by
        rw [Nat.cast_sub (by omega)]
      rw [hsub_nat]
      exact_mod_cast hcomb
    calc
      (((m + 1 : ℕ) : ℂ) - (k : ℂ)) * (Nat.choose (m + 1) k : ℂ) * c k * ζ ^ k
        = (((m + 1 : ℕ) : ℂ) * (Nat.choose m k : ℂ)) * c k * ζ ^ k := by rw [hcombC]
      _ = ((m + 1 : ℕ) : ℂ) * ((Nat.choose m k : ℂ) * c k * ζ ^ k) := by ring
  have h2 : w * (∑ k ∈ Finset.range (m + 1),
        ((Nat.choose (m + 1) (k + 1) : ℂ) * c (k + 1) * ((k + 1 : ℕ) : ℂ)) * ζ ^ k) =
      ∑ k ∈ Finset.range (m + 1),
        ((m + 1 : ℕ) : ℂ) * ((Nat.choose m k : ℂ) * (w * c (k + 1)) * ζ ^ k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hcomb : Nat.choose (m + 1) (k + 1) * (k + 1) = (m + 1) * Nat.choose m k := by
      have := Nat.add_one_mul_choose_eq m k
      linarith
    have hcombC : (Nat.choose (m + 1) (k + 1) : ℂ) * ((k + 1 : ℕ) : ℂ) =
        ((m + 1 : ℕ) : ℂ) * (Nat.choose m k : ℂ) := by exact_mod_cast hcomb
    calc
      w * (((Nat.choose (m + 1) (k + 1) : ℂ) * c (k + 1) * ((k + 1 : ℕ) : ℂ)) * ζ ^ k)
        = w * c (k + 1) * ((Nat.choose (m + 1) (k + 1) : ℂ) * ((k + 1 : ℕ) : ℂ)) * ζ ^ k := by ring
      _ = w * c (k + 1) * (((m + 1 : ℕ) : ℂ) * (Nat.choose m k : ℂ)) * ζ ^ k := by rw [hcombC]
      _ = ((m + 1 : ℕ) : ℂ) * ((Nat.choose m k : ℂ) * (w * c (k + 1)) * ζ ^ k) := by ring
  calc
    ((m + 1 : ℕ) : ℂ) * (∑ k ∈ Finset.range (m + 2), c k * ((Nat.choose (m + 1) k : ℂ) * ζ ^ k)) +
        (w - ζ) * (∑ k ∈ Finset.range (m + 1), ((Nat.choose (m + 1) (k + 1) : ℂ) * c (k + 1) * ((k + 1 : ℕ) : ℂ)) * ζ ^ k)
      = (((m + 1 : ℕ) : ℂ) * (∑ k ∈ Finset.range (m + 2), c k * ((Nat.choose (m + 1) k : ℂ) * ζ ^ k)) -
          ζ * (∑ k ∈ Finset.range (m + 1), ((Nat.choose (m + 1) (k + 1) : ℂ) * c (k + 1) * ((k + 1 : ℕ) : ℂ)) * ζ ^ k)) +
        w * (∑ k ∈ Finset.range (m + 1), ((Nat.choose (m + 1) (k + 1) : ℂ) * c (k + 1) * ((k + 1 : ℕ) : ℂ)) * ζ ^ k) := by ring
    _ = (∑ k ∈ Finset.range (m + 1), ((m + 1 : ℕ) : ℂ) * ((Nat.choose m k : ℂ) * c k * ζ ^ k)) +
        (∑ k ∈ Finset.range (m + 1), ((m + 1 : ℕ) : ℂ) * ((Nat.choose m k : ℂ) * (w * c (k + 1)) * ζ ^ k)) := by rw [h1, h2]
    _ = ((m + 1 : ℕ) : ℂ) * ∑ k ∈ Finset.range (m + 1), (c k + w * c (k + 1)) * ((Nat.choose m k : ℂ) * ζ ^ k) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _; ring

/-- **Grace-Walsh-Szego Coincidence Theorem on the Closed Unit Disk**:
    For every symmetric multiaffine form `F_m(c; z_1, ..., z_m)` (`m ≥ 1`) and any
    `z_1, ..., z_m` in the closed unit disk `‖z_i‖ ≤ 1`, there exists a single point
    `ζ` in the closed unit disk `‖ζ‖ ≤ 1` such that `F_m(c; z) = F_m(c; ζ, ..., ζ)`. -/
theorem grace_walsh_szego_unitDisk :
    ∀ (m : ℕ) (_hm : 1 ≤ m) (c : ℕ → ℂ) (z : Fin m → ℂ),
      (∀ i, ‖z i‖ ≤ 1) →
      ∃ ζ : ℂ, ‖ζ‖ ≤ 1 ∧ symMultiaffine m c z = symMultiaffine m c (fun _ => ζ) := by
  intro m hm
  -- First prove the zero-avoidance form by induction on m ≥ 1:
  have h_zero : ∀ (n : ℕ), 1 ≤ n → ∀ (c : ℕ → ℂ) (z : Fin n → ℂ),
      (∀ i, ‖z i‖ ≤ 1) →
      (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → (diagPoly n c).eval ζ ≠ 0) →
      symMultiaffine n c z ≠ 0 := by
    intro n
    induction n with
    | zero => intro h0; omega
    | succ n ih =>
      intro _ c z hz hno
      cases n with
      | zero =>
        -- n + 1 = 1: symMultiaffine 1 c z = diagPoly 1 c evaluated at z 0!
        have h_eq : symMultiaffine 1 c z = (diagPoly 1 c).eval (z 0) := by
          rw [eval_diagPoly]
          congr 1
          ext i
          fin_cases i; rfl
        rw [h_eq]
        exact hno (z 0) (hz 0)
      | succ k =>
        -- Step from k + 1 to k + 2 using Laguerre's Polar Derivative Theorem!
        rw [symMultiaffine_succ]
        set w := z (Fin.last (k + 1))
        have hw : ‖w‖ ≤ 1 := hz (Fin.last (k + 1))
        set c' : ℕ → ℂ := fun j => c j + w * c (j + 1)
        apply ih (by omega) c' (fun i => z i.castSucc) (fun i => hz i.castSucc)
        intro ζ hζ h0
        have hpd := laguerre_polar_outside_closedUnitDisk (m := k + 2) (by omega)
          (natDegree_diagPoly_le (k + 2) c) hno hw ζ hζ
        rw [polarDeriv_diagPoly_succ (k + 1) w c, eval_mul, eval_C] at hpd
        exact hpd (by rw [h0, mul_zero])
  -- Now apply h_zero to c_shifted(0) = c(0) - symMultiaffine m c z, c_shifted(k) = c(k) for k ≥ 1!
  intro c z hz
  by_contra h_none
  push Not at h_none
  set val := symMultiaffine m c z
  set c' : ℕ → ℂ := fun k => if k = 0 then c 0 - val else c k
  have hshift_eq : ∀ v : Fin m → ℂ, symMultiaffine m c' v = symMultiaffine m c v - val := by
    intro v
    unfold symMultiaffine
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have he0 : elemSym m v 0 = 1 := by cases m <;> rfl
    have hrest : ∑ k ∈ Finset.range m, c' (k + 1) * elemSym m v (k + 1) =
        ∑ k ∈ Finset.range m, c (k + 1) * elemSym m v (k + 1) := by
      apply Finset.sum_congr rfl
      intro k _; simp [c']
    rw [hrest, he0]
    simp [c']
    ring
  have hno : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → (diagPoly m c').eval ζ ≠ 0 := by
    intro ζ hζ h0
    rw [eval_diagPoly, hshift_eq] at h0
    exact h_none ζ hζ (sub_eq_zero.mp h0).symm
  have hne := h_zero m hm c' z hz hno
  rw [hshift_eq] at hne
  exact hne (sub_self val)

/-- Scaled closed disk version of Grace-Walsh-Szego: for any `r > 0` and `‖z_i‖ ≤ r`,
    there exists `ζ` with `‖ζ‖ ≤ r` such that `symMultiaffine m c z = symMultiaffine m c (fun _ => ζ)`. -/
theorem grace_walsh_szego_disk {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr : 0 < r)
    (c : ℕ → ℂ) (z : Fin m → ℂ) (hz : ∀ i, ‖z i‖ ≤ r) :
    ∃ ζ : ℂ, ‖ζ‖ ≤ r ∧ symMultiaffine m c z = symMultiaffine m c (fun _ => ζ) := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  set u : Fin m → ℂ := fun i => z i / (r : ℂ)
  have hu : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    dsimp [u]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
    exact (div_le_one hr).mpr (hz i)
  have he_scale : ∀ (n : ℕ) (v : Fin n → ℂ) (k : ℕ),
      elemSym n (fun i => (r : ℂ) * v i) k = (r : ℂ) ^ k * elemSym n v k := by
    intro n
    induction n with
    | zero => intro v k; cases k <;> simp [elemSym]
    | succ n ih =>
      intro v k
      cases k with
      | zero => simp [elemSym]
      | succ k =>
        simp only [elemSym, ih]
        ring
  set c_r : ℕ → ℂ := fun k => c k * (r : ℂ) ^ k
  have hform : ∀ v : Fin m → ℂ, symMultiaffine m c (fun i => (r : ℂ) * v i) = symMultiaffine m c_r v := by
    intro v
    unfold symMultiaffine
    apply Finset.sum_congr rfl
    intro k _
    rw [he_scale]
    dsimp [c_r]; ring
  rcases grace_walsh_szego_unitDisk m hm c_r u hu with ⟨ξ, hξ, heq⟩
  refine ⟨(r : ℂ) * ξ, ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
    nlinarith
  · have hz_eq : z = fun i => (r : ℂ) * u i := by
      ext i; dsimp [u]; exact (mul_div_cancel₀ _ hrC).symm
    rw [hz_eq, hform, heq, ← hform]

/-- Affine invariance of `polarDeriv`: shifting and scaling `P` via `X ↦ c + r * X`
    commutes with taking the polar derivative. -/
lemma eval_polarDeriv_comp_affine (m : ℕ) (center r w z : ℂ) (P : ℂ[X]) :
    (polarDeriv m w (P.comp (C center + C r * X))).eval z =
      (polarDeriv m (center + r * w) P).eval (center + r * z) := by
  unfold polarDeriv
  simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, eval_comp]
  rw [derivative_comp, derivative_add, derivative_C, zero_add,
    derivative_mul, derivative_C, zero_mul, zero_add, derivative_X, mul_one]
  simp only [eval_mul, eval_comp, eval_add, eval_C, eval_X]
  ring

/-- `natDegree` does not increase under composition with a linear polynomial `c + r * X`. -/
lemma natDegree_comp_affine_le (center r : ℂ) (P : ℂ[X]) :
    (P.comp (C center + C r * X)).natDegree ≤ P.natDegree := by
  calc (P.comp (C center + C r * X)).natDegree
      ≤ P.natDegree * (C center + C r * X).natDegree := Polynomial.natDegree_comp_le
    _ ≤ P.natDegree * 1 := by
        apply Nat.mul_le_mul_left
        exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp)
          (le_trans (Polynomial.natDegree_mul_le) (by simp)))
    _ = P.natDegree := mul_one _

/-- Laguerre's Polar Derivative Theorem on any closed disk `‖z - center‖ ≤ r` (`r > 0`). -/
theorem laguerre_polar_outside_closedBall {m : ℕ} (hm : 1 ≤ m) {center : ℂ} {r : ℝ} (hr : 0 < r)
    {P : ℂ[X]} (hdeg : P.natDegree ≤ m)
    (hno : ∀ z : ℂ, ‖z - center‖ ≤ r → P.eval z ≠ 0)
    {w : ℂ} (hw : ‖w - center‖ ≤ r) :
    ∀ z : ℂ, ‖z - center‖ ≤ r → (polarDeriv m w P).eval z ≠ 0 := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  set Q : ℂ[X] := P.comp (C center + C (r : ℂ) * X)
  have hQdeg : Q.natDegree ≤ m := le_trans (natDegree_comp_affine_le center (r : ℂ) P) hdeg
  have hQno : ∀ u : ℂ, ‖u‖ ≤ 1 → Q.eval u ≠ 0 := by
    intro u hu
    rw [show Q.eval u = P.eval (center + (r : ℂ) * u) by simp [Q]]
    apply hno
    rw [show center + (r : ℂ) * u - center = (r : ℂ) * u by ring,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
    nlinarith
  have hw' : ‖(w - center) / (r : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
    exact (div_le_one hr).mpr hw
  intro z hz
  have hz' : ‖(z - center) / (r : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
    exact (div_le_one hr).mpr hz
  have hpd := laguerre_polar_outside_closedUnitDisk hm hQdeg hQno hw' ((z - center) / (r : ℂ)) hz'
  rw [eval_polarDeriv_comp_affine] at hpd
  have h1 : center + (r : ℂ) * ((w - center) / (r : ℂ)) = w := by field_simp [hrC]; ring
  have h2 : center + (r : ℂ) * ((z - center) / (r : ℂ)) = z := by field_simp [hrC]; ring
  rw [h1, h2] at hpd
  exact hpd

/-- Boundary-root refinement of `mobius_re_pos_of_norm_gt`: for `‖a‖ = 1`, `‖w‖ ≤ 1`, `‖z‖ ≤ 1`,
    `a ≠ z`, the same real part is non-negative. -/
lemma mobius_re_nonneg_of_norm_ge {a w z : ℂ} (ha : 1 ≤ ‖a‖) (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (haz : a ≠ z) :
    0 ≤ ((1 - z * starRingEnd ℂ w) * ((a - w) / (a - z))).re := by
  have haz0 : a - z ≠ 0 := sub_ne_zero.mpr haz
  set t : ℂ := (a - w) / (a - z)
  have ht1 : t - 1 = (z - w) / (a - z) := by dsimp [t]; field_simp [haz0]; ring
  have htz : t * z - w = a * ((z - w) / (a - z)) := by dsimp [t]; field_simp [haz0]; ring
  have h_ns : Complex.normSq (t * z - w) - Complex.normSq (t - 1) =
      (Complex.normSq a - 1) * Complex.normSq ((z - w) / (a - z)) := by
    rw [htz, ht1, map_mul]; ring
  have h_exp : Complex.normSq (t * z - w) - Complex.normSq (t - 1) =
      2 * ((1 - z * starRingEnd ℂ w) * t).re -
      (1 - Complex.normSq z) * Complex.normSq t - (1 - Complex.normSq w) := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]
    ring
  have ha2 : 1 ≤ Complex.normSq a := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hw2 : Complex.normSq w ≤ 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have hz2 : Complex.normSq z ≤ 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hfrac_nn : 0 ≤ Complex.normSq ((z - w) / (a - z)) := Complex.normSq_nonneg _
  have ht_nn : 0 ≤ Complex.normSq t := Complex.normSq_nonneg t
  nlinarith

/-- **Strict Boundary-Root Laguerre Polar Derivative Theorem (Unit Disk)**:
    Suppose `P` has `natDegree P ≤ m` (`2 ≤ m`), `P(1) = 0`, `P'(1) ≠ 0` (so `1` is a simple root),
    and `P` has NO other root in the closed unit disk `‖z‖ ≤ 1`.
    Then for ANY `w` with `‖w‖ ≤ 1` and `w ≠ 1`, `polarDeriv m w P` has NO roots AT ALL
    in the closed unit disk `‖z‖ ≤ 1`! -/
theorem laguerre_polar_strict_unique_boundary_unitDisk {m : ℕ} (hm : 2 ≤ m) {P : ℂ[X]}
    (hdeg : P.natDegree ≤ m) (hP1 : P.eval 1 = 0) (hP'1 : (derivative P).eval 1 ≠ 0)
    (hno : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → P.eval z ≠ 0)
    {w : ℂ} (hw : ‖w‖ ≤ 1) (hw1 : w ≠ 1) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → (polarDeriv m w P).eval z ≠ 0 := by
  have hPne : P ≠ 0 := by
    intro h0; rw [h0, derivative_zero, eval_zero] at hP'1; exact hP'1 rfl
  intro z hz
  -- Case 1: z = 1 => polarDeriv m w P at 1 is (w - 1) * P'(1) ≠ 0
  by_cases hz1 : z = 1
  · subst hz1
    unfold polarDeriv
    simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, hP1, mul_zero, zero_add]
    exact mul_ne_zero (sub_ne_zero.mpr hw1) hP'1
  -- Case 2: z = w => polarDeriv m w P at w is m * P(w) ≠ 0 (since w ≠ 1)
  by_cases hzw : z = w
  · subst hzw
    unfold polarDeriv
    simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (hno z hz hz1)
  -- Case 3: z ≠ 1 and z ≠ w. Factor P = C lc * ∏ (X - C a).
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hcard_eq_deg : P.roots.card = P.natDegree := hsplit.natDegree_eq_card_roots.symm
  have hfact : P = C P.leadingCoeff * (P.roots.map fun a => X - C a).prod :=
    (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard_eq_deg).symm
  set c := P.leadingCoeff
  set roots := P.roots
  have hc_ne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hcard : roots.card ≤ m := le_trans (Polynomial.card_roots' P) hdeg
  have hPz_ne : P.eval z ≠ 0 := hno z hz hz1
  have hz_ne : ∀ a ∈ roots, z - a ≠ 0 := by
    intro a ha heq
    have haz : a = z := (sub_eq_zero.mp heq).symm
    rw [haz] at ha
    exact hPz_ne ((Polynomial.mem_roots hPne).mp ha)
  have hprod_ne : (roots.map (fun a => z - a)).prod ≠ 0 :=
    Multiset.prod_ne_zero (fun h => by
      rcases Multiset.mem_map.mp h with ⟨a, ha, h0⟩; exact hz_ne a ha h0)
  have hpd_eq : (polarDeriv m w P).eval z =
      c * (roots.map (fun a => z - a)).prod *
        (((m : ℂ) - (roots.card : ℂ)) + (roots.map (fun a => (a - w) / (a - z))).sum) := by
    conv_lhs => rw [hfact]
    exact eval_polarDeriv_factored m w z c roots hz_ne
  rw [hpd_eq]
  apply mul_ne_zero (mul_ne_zero hc_ne hprod_ne)
  -- Show the inner sum S has Re((1 - z * conj w) * S) > 0!
  -- Every root a ∈ roots satisfies either a = 1 (with multiplicity 1, since P'(1) ≠ 0) or ‖a‖ > 1.
  have hroot_ge : ∀ a ∈ roots, 1 ≤ ‖a‖ := by
    intro a ha
    by_contra hlt
    push Not at hlt
    have ha1 : a ≠ 1 := by intro h; rw [h, norm_one] at hlt; linarith
    exact hno a (le_of_lt hlt) ha1 ((Polynomial.mem_roots hPne).mp ha)
  have h1_mem : (1 : ℂ) ∈ roots := (Polynomial.mem_roots hPne).mpr hP1
  -- Multiplicity of 1 in roots is exactly 1 (since P'(1) ≠ 0)
  have h1_count : Multiset.count (1 : ℂ) roots = 1 := by
    have hpos : 1 ≤ Multiset.count (1 : ℂ) roots := Multiset.one_le_count_iff_mem.mpr h1_mem
    by_contra hne1
    have hge2 : 2 ≤ Multiset.count (1 : ℂ) roots := by omega
    have hdvd : (X - C (1 : ℂ)) ^ 2 ∣ P := by
      have hrm : 2 ≤ P.rootMultiplicity 1 := by
        rw [Polynomial.count_roots] at hge2; exact hge2
      exact (pow_dvd_pow (X - C (1 : ℂ)) hrm).trans (Polynomial.pow_rootMultiplicity_dvd P 1)
    rcases hdvd with ⟨Q, hQ⟩
    rw [hQ, derivative_mul, derivative_pow] at hP'1
    simp [eval_mul, eval_add, eval_pow, eval_sub, eval_X, eval_C] at hP'1
  set α : ℂ := 1 - z * starRingEnd ℂ w
  have hα_re : 0 < α.re := one_sub_mul_conj_re_pos hw hz (Ne.symm hzw)
  intro hS0
  have hmul0 : (α * (((m : ℂ) - (roots.card : ℂ)) + (roots.map (fun a => (a - w) / (a - z))).sum)).re = 0 := by
    rw [hS0, mul_zero, Complex.zero_re]
  have hsum_re : (α * (((m : ℂ) - (roots.card : ℂ)) + (roots.map (fun a => (a - w) / (a - z))).sum)).re =
      ((m : ℝ) - (roots.card : ℝ)) * α.re +
        (roots.map (fun a => (α * ((a - w) / (a - z))).re)).sum := by
    rw [mul_add, Complex.add_re]
    congr 1
    · have hreal : ((m : ℂ) - (roots.card : ℂ)) = (((m : ℝ) - (roots.card : ℝ) : ℝ) : ℂ) := by
        push_cast; ring
      rw [hreal, mul_comm, Complex.re_ofReal_mul]
    · clear hmul0 hS0 h1_count h1_mem hroot_ge hpd_eq hprod_ne hz_ne hcard hfact hcard_eq_deg hsplit
      induction roots using Multiset.induction_on with
      | empty => simp
      | cons a s ih => simp [mul_add, ih]
  have hterm_nn : ∀ a ∈ roots, 0 ≤ (α * ((a - w) / (a - z))).re := by
    intro a ha
    have haz : a ≠ z := fun h => hz_ne a ha (by rw [h, sub_self])
    exact mobius_re_nonneg_of_norm_ge (hroot_ge a ha) hw hz haz
  have hpos : 0 < ((m : ℝ) - (roots.card : ℝ)) * α.re +
      (roots.map (fun a => (α * ((a - w) / (a - z))).re)).sum := by
    by_cases hlt : roots.card < m
    · have hltR : (roots.card : ℝ) < (m : ℝ) := by exact_mod_cast hlt
      have h1 : 0 < ((m : ℝ) - (roots.card : ℝ)) * α.re := mul_pos (sub_pos.mpr hltR) hα_re
      have h2 : 0 ≤ (roots.map (fun a => (α * ((a - w) / (a - z))).re)).sum :=
        Multiset.sum_nonneg (fun x hx => by
          rcases Multiset.mem_map.mp hx with ⟨a, ha, rfl⟩; exact hterm_nn a ha)
      linarith
    · -- roots.card = m ≥ 2, and count 1 roots = 1, so there is a root a₀ ∈ roots with a₀ ≠ 1!
      have hcard_eq : roots.card = m := by omega
      have hex : ∃ a₀ ∈ roots, a₀ ≠ 1 := by
        by_contra hall
        push Not at hall
        have hcnt : Multiset.count (1 : ℂ) roots = (Multiset.filter (fun y => 1 = y) roots).card :=
          Multiset.count_eq_card_filter_eq roots 1
        have hf2 : Multiset.filter (fun y => 1 = y) roots = roots :=
          Multiset.filter_eq_self.mpr (fun y hy => (hall y hy).symm)
        rw [hf2] at hcnt
        omega
      rcases hex with ⟨a₀, ha₀_mem, ha₀_ne1⟩
      have ha₀_gt : 1 < ‖a₀‖ := by
        by_contra hle
        push Not at hle
        exact hno a₀ hle ha₀_ne1 ((Polynomial.mem_roots hPne).mp ha₀_mem)
      have ha₀_pos : 0 < (α * ((a₀ - w) / (a₀ - z))).re :=
        mobius_re_pos_of_norm_gt ha₀_gt hw hz (Ne.symm hzw)
      obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem ha₀_mem
      have hsum_pos : 0 < (roots.map (fun a => (α * ((a - w) / (a - z))).re)).sum := by
        rw [hs, Multiset.map_cons, Multiset.sum_cons]
        have hs_nn : 0 ≤ (s.map (fun a => (α * ((a - w) / (a - z))).re)).sum :=
          Multiset.sum_nonneg (fun x hx => by
            rcases Multiset.mem_map.mp hx with ⟨a, ha, rfl⟩
            exact hterm_nn a (by rw [hs]; exact Multiset.mem_cons_of_mem ha))
        linarith
      have hfirst : ((m : ℝ) - (roots.card : ℝ)) * α.re = 0 := by rw [hcard_eq]; ring
      linarith
  linarith

/-- **Strict Boundary-Root Laguerre Polar Derivative Theorem on any Closed Ball `‖z - center‖ ≤ r`**,
    with boundary point `b = center + r` (e.g. `center = 1/2, r = 1/2, b = 1`). -/
theorem laguerre_polar_strict_unique_boundary_closedBall {m : ℕ} (hm : 2 ≤ m)
    {center : ℂ} {r : ℝ} (hr : 0 < r) {P : ℂ[X]} (hdeg : P.natDegree ≤ m)
    (hPb : P.eval (center + (r : ℂ)) = 0)
    (hP'b : (derivative P).eval (center + (r : ℂ)) ≠ 0)
    (hno : ∀ z : ℂ, ‖z - center‖ ≤ r → z ≠ center + (r : ℂ) → P.eval z ≠ 0)
    {w : ℂ} (hw : ‖w - center‖ ≤ r) (hwb : w ≠ center + (r : ℂ)) :
    ∀ z : ℂ, ‖z - center‖ ≤ r → (polarDeriv m w P).eval z ≠ 0 := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  set Q : ℂ[X] := P.comp (C center + C (r : ℂ) * X)
  have hQdeg : Q.natDegree ≤ m := le_trans (natDegree_comp_affine_le center (r : ℂ) P) hdeg
  have hQ1 : Q.eval 1 = 0 := by simpa [Q] using hPb
  have hQ'1 : (derivative Q).eval 1 ≠ 0 := by
    have hderiv : derivative Q = (derivative P).comp (C center + C (r : ℂ) * X) * C (r : ℂ) := by
      dsimp [Q]
      rw [derivative_comp, derivative_add, derivative_C, zero_add,
        derivative_mul, derivative_C, zero_mul, zero_add, derivative_X, mul_one, mul_comm]
    rw [hderiv, eval_mul, eval_comp, eval_C]
    simp only [eval_add, eval_C, eval_mul, eval_X, mul_one]
    exact mul_ne_zero hP'b hrC
  have hQno : ∀ u : ℂ, ‖u‖ ≤ 1 → u ≠ 1 → Q.eval u ≠ 0 := by
    intro u hu hu1
    rw [show Q.eval u = P.eval (center + (r : ℂ) * u) by simp [Q]]
    apply hno
    · rw [show center + (r : ℂ) * u - center = (r : ℂ) * u by ring,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
      nlinarith
    · intro heq
      apply hu1
      have h1 : (r : ℂ) * u = (r : ℂ) * 1 := by linear_combination heq
      exact mul_left_cancel₀ hrC h1
  have hw' : ‖(w - center) / (r : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
    exact (div_le_one hr).mpr hw
  have hw1 : (w - center) / (r : ℂ) ≠ 1 := by
    intro heq
    apply hwb
    have := (div_eq_iff hrC).mp heq
    linear_combination this
  intro z hz
  have hz' : ‖(z - center) / (r : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
    exact (div_le_one hr).mpr hz
  have hpd := laguerre_polar_strict_unique_boundary_unitDisk hm hQdeg hQ1 hQ'1 hQno hw' hw1
    ((z - center) / (r : ℂ)) hz'
  rw [eval_polarDeriv_comp_affine] at hpd
  have h1 : center + (r : ℂ) * ((w - center) / (r : ℂ)) = w := by field_simp [hrC]; ring
  have h2 : center + (r : ℂ) * ((z - center) / (r : ℂ)) = z := by field_simp [hrC]; ring
  rw [h1, h2] at hpd
  exact hpd

/-- **Grace-Walsh-Szego Coincidence Theorem on ANY Closed Disk `‖z - center‖ ≤ r`** (`r > 0`). -/
theorem grace_walsh_szego_closedBall {m : ℕ} (hm : 1 ≤ m) {center : ℂ} {r : ℝ} (hr : 0 < r)
    (c : ℕ → ℂ) (z : Fin m → ℂ) (hz : ∀ i, ‖z i - center‖ ≤ r) :
    ∃ ζ : ℂ, ‖ζ - center‖ ≤ r ∧ symMultiaffine m c z = symMultiaffine m c (fun _ => ζ) := by
  have h_zero : ∀ (n : ℕ), 1 ≤ n → ∀ (c : ℕ → ℂ) (z : Fin n → ℂ),
      (∀ i, ‖z i - center‖ ≤ r) →
      (∀ ζ : ℂ, ‖ζ - center‖ ≤ r → (diagPoly n c).eval ζ ≠ 0) →
      symMultiaffine n c z ≠ 0 := by
    intro n
    induction n with
    | zero => intro h0; omega
    | succ n ih =>
      intro _ c z hz hno
      cases n with
      | zero =>
        have h_eq : symMultiaffine 1 c z = (diagPoly 1 c).eval (z 0) := by
          rw [eval_diagPoly]; congr 1; ext i; fin_cases i; rfl
        rw [h_eq]; exact hno (z 0) (hz 0)
      | succ k =>
        rw [symMultiaffine_succ]
        set w := z (Fin.last (k + 1))
        have hw : ‖w - center‖ ≤ r := hz (Fin.last (k + 1))
        set c' : ℕ → ℂ := fun j => c j + w * c (j + 1)
        apply ih (by omega) c' (fun i => z i.castSucc) (fun i => hz i.castSucc)
        intro ζ hζ h0
        have hpd := laguerre_polar_outside_closedBall (m := k + 2) (by omega) hr
          (natDegree_diagPoly_le (k + 2) c) hno hw ζ hζ
        rw [polarDeriv_diagPoly_succ (k + 1) w c, eval_mul, eval_C] at hpd
        exact hpd (by rw [h0, mul_zero])
  by_contra h_none
  push Not at h_none
  set val := symMultiaffine m c z
  set c' : ℕ → ℂ := fun k => if k = 0 then c 0 - val else c k
  have hshift_eq : ∀ v : Fin m → ℂ, symMultiaffine m c' v = symMultiaffine m c v - val := by
    intro v
    unfold symMultiaffine
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have he0 : elemSym m v 0 = 1 := by cases m <;> rfl
    have hrest : ∑ k ∈ Finset.range m, c' (k + 1) * elemSym m v (k + 1) =
        ∑ k ∈ Finset.range m, c (k + 1) * elemSym m v (k + 1) := by
      apply Finset.sum_congr rfl; intro k _; simp [c']
    rw [hrest, he0]; simp [c']; ring
  have hno : ∀ ζ : ℂ, ‖ζ - center‖ ≤ r → (diagPoly m c').eval ζ ≠ 0 := by
    intro ζ hζ h0
    rw [eval_diagPoly, hshift_eq] at h0
    exact h_none ζ hζ (sub_eq_zero.mp h0).symm
  have hne := h_zero m hm c' z hz hno
  rw [hshift_eq] at hne
  exact hne (sub_self val)

/-- Helper: `elemSym n v k = 0` when `n < k`. -/
lemma elemSym_eq_zero_of_lt' : ∀ (n : ℕ) (v : Fin n → ℂ) (k : ℕ), n < k → elemSym n v k = 0 := by
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

/-- Helper: `∏_{k} (1 - w_k * z) = ∑_{d=0}^m (-1)^d e_d(w) z^d`. -/
lemma prod_one_sub_eq_sum_elemSym' :
    ∀ (m : ℕ) (w : Fin m → ℂ) (z : ℂ),
      (∏ k : Fin m, (1 - w k * z)) = ∑ d ∈ Finset.range (m + 1), (-1 : ℂ) ^ d * elemSym m w d * z ^ d := by
  intro m
  induction m with
  | zero => intro w z; simp [elemSym]
  | succ m ih =>
    intro w z
    rw [Fin.prod_univ_castSucc, ih (fun i => w i.castSucc) z]
    have hlast : elemSym m (fun i => w i.castSucc) (m + 1) = 0 :=
      elemSym_eq_zero_of_lt' m _ (m + 1) (by omega)
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

/-- `elemSym` is invariant under any permutation of coordinates. -/
lemma elemSym_perm (m : ℕ) (w : Fin m → ℂ) (σ : Equiv.Perm (Fin m)) (d : ℕ) :
    elemSym m (fun i => w (σ i)) d = elemSym m w d := by
  by_cases hd : m < d
  · rw [elemSym_eq_zero_of_lt' m _ d hd, elemSym_eq_zero_of_lt' m _ d hd]
  · set P₁ : ℂ[X] := ∑ k ∈ Finset.range (m + 1), C ((-1 : ℂ) ^ k * elemSym m (fun i => w (σ i)) k) * X ^ k
    set P₂ : ℂ[X] := ∑ k ∈ Finset.range (m + 1), C ((-1 : ℂ) ^ k * elemSym m w k) * X ^ k
    have heval_sum : ∀ (f : ℕ → ℂ[X]) (z : ℂ), (∑ k ∈ Finset.range (m + 1), f k).eval z =
        ∑ k ∈ Finset.range (m + 1), (f k).eval z := fun f z =>
      map_sum (Polynomial.evalRingHom z) f (Finset.range (m + 1))
    have heval : ∀ z : ℂ, P₁.eval z = P₂.eval z := by
      intro z
      have h1 : P₁.eval z = ∏ k : Fin m, (1 - w (σ k) * z) := by
        dsimp [P₁]; rw [heval_sum, prod_one_sub_eq_sum_elemSym']
        apply Finset.sum_congr rfl; intro k _; simp
      have h2 : P₂.eval z = ∏ k : Fin m, (1 - w k * z) := by
        dsimp [P₂]; rw [heval_sum, prod_one_sub_eq_sum_elemSym']
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

/-- **Strict Uniqueness for Grace-Walsh-Szego on a Closed Ball**:
    Suppose `m ≥ 2`, `diagPoly m c` has a SIMPLE root at `b = center + r` and NO other root in
    `‖ζ - center‖ ≤ r`. If `‖z i - center‖ ≤ r` for all `i` and at least one coordinate
    satisfies `z i₀ ≠ b`, then `symMultiaffine m c z ≠ 0`! -/
theorem grace_walsh_szego_closedBall_unique_boundary {m : ℕ} (hm : 2 ≤ m)
    {center : ℂ} {r : ℝ} (hr : 0 < r) (c : ℕ → ℂ) (z : Fin m → ℂ)
    (hz : ∀ i, ‖z i - center‖ ≤ r)
    (hPb : (diagPoly m c).eval (center + (r : ℂ)) = 0)
    (hP'b : (derivative (diagPoly m c)).eval (center + (r : ℂ)) ≠ 0)
    (hno : ∀ ζ : ℂ, ‖ζ - center‖ ≤ r → ζ ≠ center + (r : ℂ) → (diagPoly m c).eval ζ ≠ 0)
    (hne : ∃ i₀ : Fin m, z i₀ ≠ center + (r : ℂ)) :
    symMultiaffine m c z ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rcases hne with ⟨i₀, hi₀⟩
  -- Swap i₀ with Fin.last (k + 1) using symmetry of symMultiaffine!
  set σ : Equiv.Perm (Fin (k + 2)) := Equiv.swap i₀ (Fin.last (k + 1))
  set z' : Fin (k + 2) → ℂ := fun i => z (σ i)
  have hz'_sym : symMultiaffine (k + 2) c z = symMultiaffine (k + 2) c z' := by
    unfold symMultiaffine
    apply Finset.sum_congr rfl
    intro d _
    rw [elemSym_perm (k + 2) z σ d]
  rw [hz'_sym, symMultiaffine_succ]
  set w := z' (Fin.last (k + 1))
  have hw_eq : w = z i₀ := by dsimp [w, z', σ]; rw [Equiv.swap_apply_right]
  have hw : ‖w - center‖ ≤ r := by rw [hw_eq]; exact hz i₀
  have hwb : w ≠ center + (r : ℂ) := by rw [hw_eq]; exact hi₀
  set c' : ℕ → ℂ := fun j => c j + w * c (j + 1)
  -- After ONE polar derivative with respect to w ≠ b, diagPoly (k + 1) c' has NO roots AT ALL
  -- in the closed ball ‖ζ - center‖ ≤ r!
  have hno' : ∀ ζ : ℂ, ‖ζ - center‖ ≤ r → (diagPoly (k + 1) c').eval ζ ≠ 0 := by
    intro ζ hζ h0
    have hpd := laguerre_polar_strict_unique_boundary_closedBall (m := k + 2) (by omega) hr
      (natDegree_diagPoly_le (k + 2) c) hPb hP'b hno hw hwb ζ hζ
    rw [polarDeriv_diagPoly_succ (k + 1) w c, eval_mul, eval_C] at hpd
    exact hpd (by rw [h0, mul_zero])
  -- Now apply standard Grace-Walsh-Szego on the remaining k + 1 ≥ 1 variables!
  rcases grace_walsh_szego_closedBall (m := k + 1) (by omega) hr c'
      (fun i => z' i.castSucc) (fun i => hz (σ i.castSucc)) with ⟨ζ, hζ, heq⟩
  rw [heq, ← eval_diagPoly]
  exact hno' ζ hζ

end DualSmale
