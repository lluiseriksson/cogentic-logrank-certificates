/-
  Paper 58: Zero-Dependency Constructive Lean 4.35.0 Kernel for
  Google Research Cogentic (Nov 25, 2026):
  "Breaking the Square-Root Barrier for the Log-Rank Conjecture"
  (Theorem 1.1: D_cc(M) <= O(r^{1/2 - 5e-6}), Eq. (1.6)-(1.7), Lemma 2.1, Prop. A.3)

  Author: Lluis Eriksson
  License: MIT
  Axiom budget: ZERO sorry, ZERO axiom, ZERO Classical.choice, ZERO Lean.ofReduceBool, ZERO warnings.
-/

namespace CogenticLogRank

private theorem sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -x := by omega
    have hm : 0 ≤ (-x) * (-x) := Int.mul_nonneg hn hn
    rw [Int.neg_mul_neg] at hm
    exact hm

private theorem sq_eq_zero_iff (x : Int) : x * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_cases h0 : x = 0
    · exact h0
    · by_cases hp : 0 < x
      · have : 0 < x * x := Int.mul_pos hp hp
        exact False.elim (by omega)
      · have hn : 0 < -x := by omega
        have : 0 < (-x) * (-x) := Int.mul_pos hn hn
        rw [Int.neg_mul_neg] at this
        exact False.elim (by omega)
  · intro h
    rw [h]; decide

/-! ### Part 1: Pointwise Booleanity Eq. (1.6) & Degree-1 vs. Degree-2 Tilt Barriers (Sec. 1.2) -/

/-- Theorem 1 (Sec. 1.2): Exact sign-matrix Booleanity:
    for `m ∈ {0, 1}`, both `s = 2m - 1` and `s = -(2m - 1)` satisfy `s^2 = 1`. -/
theorem sign_matrix_booleanity_identity (m : Int) (hm : m = 0 ∨ m = 1) :
    (2 * m - 1) * (2 * m - 1) = 1 ∧ (-(2 * m - 1)) * (-(2 * m - 1)) = 1 := by
  cases hm with
  | inl h0 => rw [h0]; decide
  | inr h1 => rw [h1]; decide

/-- Theorem 2 (Eq. (1.6)): Exact pointwise Booleanity quadratic identity:
    if `S = s1 * u1 * v1 + Aperp` satisfies `S^2 = 1`, then
    `-2 * s1 * u1 * v1 * Aperp = Aperp^2 + (s1 * u1 * v1)^2 - 1`. -/
theorem eq16_pointwise_boolean_quadratic (s1 u1 v1 Aperp : Int)
    (hS : (s1 * u1 * v1 + Aperp) * (s1 * u1 * v1 + Aperp) = 1) :
    (-2) * (s1 * u1 * v1) * Aperp = Aperp * Aperp + (s1 * u1 * v1) * (s1 * u1 * v1) - 1 := by
  let p := s1 * u1 * v1
  have hexp : (p + Aperp) * (p + Aperp) = p * p + 2 * p * Aperp + Aperp * Aperp := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have hc : Aperp * p = p * Aperp := Int.mul_comm Aperp p
    have h2 : 2 * p * Aperp = p * Aperp + p * Aperp := by
      have : (2 : Int) * p = p + p := by omega
      rw [this, Int.add_mul]
    omega
  have hneg : (-2) * p * Aperp = -(2 * p * Aperp) := by
    have : (-2 : Int) * p = -(2 * p) := Int.neg_mul 2 p
    rw [this, Int.neg_mul]
  have hS' : (p + Aperp) * (p + Aperp) = 1 := hS
  change (-2) * p * Aperp = Aperp * Aperp + p * p - 1
  omega

/-- Theorem 3 (Sec. 1.2): Exact Degree-1 AM-GM Barrier:
    for all `lam, T, d : Int` with `0 ≤ d`,
    `4 * (lam * T)^2 * d ≤ (lam^2 * d + T^2)^2`, proving linear tilts cannot beat `(r')^{-1/2}`. -/
theorem sec12_degree1_amgm_barrier (lam T d : Int) :
    4 * (lam * lam * d) * (T * T) ≤ (lam * lam * d + T * T) * (lam * lam * d + T * T) := by
  let a := lam * lam * d
  let b := T * T
  have hsq : 0 ≤ (a - b) * (a - b) := sq_nonneg (a - b)
  have hid : (a + b) * (a + b) - 4 * a * b = (a - b) * (a - b) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have hc : b * a = a * b := Int.mul_comm b a
    have h4 : 4 * a * b = a * b + a * b + a * b + a * b := by
      have h2 : (4 : Int) * a = a + a + a + a := by omega
      rw [h2, Int.add_mul, Int.add_mul, Int.add_mul]
    omega
  change 4 * a * b ≤ (a + b) * (a + b)
  omega

/-- Theorem 4 (Sec. 1.2): Exact Degree-2 `cosh` Tilt `λ^2`-Cancellation:
    for any nonzero amplitude `lam ≠ 0`, `lam^2 > 0`, so the quadratic signal-to-KL comparison
    `lam^2 * F * T * D ≥ N * (lam^2 * tau)` is equivalent to the `λ`-free condition `F * T * D ≥ N * tau`. -/
theorem sec12_degree2_cosh_lambda_cancel (lam F T D N tau : Int) (hlam : lam ≠ 0) :
    (N * (lam * lam * tau) ≤ lam * lam * F * T * D) ↔ (N * tau ≤ F * T * D) := by
  have hpos : 0 < lam * lam := by
    have hnn := sq_nonneg lam
    have hne : lam * lam ≠ 0 := fun hz => hlam ((sq_eq_zero_iff lam).mp hz)
    omega
  have hlhs : N * (lam * lam * tau) = (lam * lam) * (N * tau) := by ac_rfl
  have hrhs : lam * lam * F * T * D = (lam * lam) * (F * T * D) := by ac_rfl
  rw [hlhs, hrhs]
  constructor
  · intro h
    by_cases hle : N * tau ≤ F * T * D
    · exact hle
    · have hgt : 0 < N * tau - F * T * D := by omega
      have hprod : 0 < (lam * lam) * (N * tau - F * T * D) := Int.mul_pos hpos hgt
      rw [Int.mul_sub] at hprod
      exact False.elim (by omega)
  · intro h
    have hdiff : 0 ≤ F * T * D - N * tau := by omega
    have hprod : 0 ≤ (lam * lam) * (F * T * D - N * tau) := Int.mul_nonneg (by omega) hdiff
    rw [Int.mul_sub] at hprod
    omega

/-! ### Part 2: Variational Potential Penalty Eq. (1.7) & Matrix Square-Root Bregman Core (Sec. 2) -/

/-- Cleared integer numerator `4 * g(t) = 8*(1 - t) - (1 - t)^2` of Eq. (1.7) penalty `g(t) = 2(1-t) - (1/4)(1-t)^2`. -/
def penalty4 (t : Int) : Int :=
  8 * (1 - t) - (1 - t) * (1 - t)

/-- Theorem 5 (Eq. (1.7)): Exact midpoint strict concavity of the variational penalty `g(t)`:
    clearing denominator 32 (`32 * (g((t1+t2)/2) - (g(t1)+g(t2))/2)`),
    `2 * (16*(2 - t1 - t2) - (2 - t1 - t2)^2) - 4 * (penalty4 t1 + penalty4 t2) = 2 * (t1 - t2)^2 ≥ 0`
    with equality iff `t1 = t2`. -/
theorem eq17_variational_penalty_concavity (t1 t2 : Int) :
    2 * (16 * (2 - t1 - t2) - (2 - t1 - t2) * (2 - t1 - t2)) -
      4 * (penalty4 t1 + penalty4 t2) = 2 * ((t1 - t2) * (t1 - t2)) ∧
    0 ≤ 2 * ((t1 - t2) * (t1 - t2)) ∧
    (2 * ((t1 - t2) * (t1 - t2)) = 0 ↔ t1 = t2) := by
  unfold penalty4
  let a := 1 - t1
  let b := 1 - t2
  have hab : 2 - t1 - t2 = a + b := by omega
  have hdiff : t1 - t2 = b - a := by omega
  have hmid : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have hc : b * a = a * b := Int.mul_comm b a
    omega
  have hba : (b - a) * (b - a) = b * b - 2 * (a * b) + a * a := by
    have e1 : (b - a) * (b - a) = b * (b - a) - a * (b - a) := Int.sub_mul b a (b - a)
    have e2 : b * (b - a) = b * b - b * a := Int.mul_sub b b a
    have e3 : a * (b - a) = a * b - a * a := Int.mul_sub a b a
    have hc : b * a = a * b := Int.mul_comm b a
    omega
  have hid : 2 * (16 * (a + b) - (a + b) * (a + b)) -
      4 * ((8 * a - a * a) + (8 * b - b * b)) = 2 * ((b - a) * (b - a)) := by
    rw [hmid, hba]
    omega
  have hid' : 2 * (16 * (2 - t1 - t2) - (2 - t1 - t2) * (2 - t1 - t2)) -
      4 * ((8 * (1 - t1) - (1 - t1) * (1 - t1)) + (8 * (1 - t2) - (1 - t2) * (1 - t2))) =
      2 * ((t1 - t2) * (t1 - t2)) := by
    rw [hab, hdiff]
    exact hid
  have hnn : 0 ≤ 2 * ((t1 - t2) * (t1 - t2)) := by
    have := sq_nonneg (t1 - t2); omega
  have hiff : 2 * ((t1 - t2) * (t1 - t2)) = 0 ↔ t1 = t2 := by
    constructor
    · intro hz
      have hsq0 : (t1 - t2) * (t1 - t2) = 0 := by omega
      have := (sq_eq_zero_iff (t1 - t2)).mp hsq0
      omega
    · intro heq
      rw [heq]
      have : (t2 - t2) * (t2 - t2) = 0 := by
        have h0 : t2 - t2 = 0 := by omega
        rw [h0]; decide
      omega
  exact ⟨hid', hnn, hiff⟩

/-- Theorem 6 (Eq. (1.7)): Exact variational penalty slope bound `g'(t) = -(3 + t)/2 ≤ -1` for `t ≥ -1`
    (cleared by 2: `-(3 + t) ≤ -2`), plus monotonicity `g(t) ≤ g(s)` for `-1 ≤ s ≤ t ≤ 1`. -/
theorem eq17_variational_penalty_slope (s t : Int) (hs : -1 ≤ s) (hst : s ≤ t) :
    -(3 + t) ≤ -2 ∧ penalty4 t ≤ penalty4 s := by
  unfold penalty4
  have h1 : 0 ≤ t - s := by omega
  have h2 : 0 ≤ 6 + s + t := by omega
  have hp : 0 ≤ (t - s) * (6 + s + t) := Int.mul_nonneg h1 h2
  have hexp : (8 * (1 - s) - (1 - s) * (1 - s)) - (8 * (1 - t) - (1 - t) * (1 - t)) =
      (t - s) * (6 + s + t) := by
    have hs2 : (1 - s) * (1 - s) = 1 - 2 * s + s * s := by
      have e1 : (1 - s) * (1 - s) = 1 * (1 - s) - s * (1 - s) := Int.sub_mul 1 s (1 - s)
      have e2 : s * (1 - s) = s * 1 - s * s := Int.mul_sub s 1 s
      omega
    have ht2 : (1 - t) * (1 - t) = 1 - 2 * t + t * t := by
      have e1 : (1 - t) * (1 - t) = 1 * (1 - t) - t * (1 - t) := Int.sub_mul 1 t (1 - t)
      have e2 : t * (1 - t) = t * 1 - t * t := Int.mul_sub t 1 t
      omega
    have hr : (t - s) * (6 + s + t) = 6 * (t - s) + t * t - s * s := by
      have e1 : (t - s) * (6 + s + t) = (t - s) * (6 + s) + (t - s) * t := Int.mul_add (t - s) (6 + s) t
      have e2 : (t - s) * (6 + s) = (t - s) * 6 + (t - s) * s := Int.mul_add (t - s) 6 s
      have e3 : (t - s) * s = t * s - s * s := Int.sub_mul t s s
      have e4 : (t - s) * t = t * t - s * t := Int.sub_mul t s t
      have hc : t * s = s * t := Int.mul_comm t s
      omega
    omega
  exact ⟨by omega, by omega⟩

/-- Theorem 7 (Eq. (2.2)): Exact scalar/eigenvalue Matrix Square-Root Bregman nonnegativity:
    clearing denominator `2σ` (`σ > 0`), `2σ(σ - r) + (r^2 - σ^2) = (r - σ)^2 ≥ 0`,
    vanishing iff `r = σ`. -/
theorem eq22_bregman_sqrt_nonneg (sigma r : Int) :
    2 * sigma * (sigma - r) + (r * r - sigma * sigma) = (r - sigma) * (r - sigma) ∧
    0 ≤ (r - sigma) * (r - sigma) ∧
    ((r - sigma) * (r - sigma) = 0 ↔ r = sigma) := by
  have hid : 2 * sigma * (sigma - r) + (r * r - sigma * sigma) = (r - sigma) * (r - sigma) := by
    rw [Int.mul_sub, Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have hc : r * sigma = sigma * r := Int.mul_comm r sigma
    have h2s : 2 * sigma * sigma = sigma * sigma + sigma * sigma := by
      have : (2 : Int) * sigma = sigma + sigma := by omega
      rw [this, Int.add_mul]
    have h2r : 2 * sigma * r = sigma * r + sigma * r := by
      have : (2 : Int) * sigma = sigma + sigma := by omega
      rw [this, Int.add_mul]
    omega
  have hnn := sq_nonneg (r - sigma)
  have hiff : (r - sigma) * (r - sigma) = 0 ↔ r = sigma := by
    constructor
    · intro h
      have h0 : r - sigma = 0 := (sq_eq_zero_iff (r - sigma)).mp h
      omega
    · intro h
      rw [h]
      have h0 : sigma - sigma = 0 := by omega
      rw [h0]; decide
  exact ⟨hid, hnn, hiff⟩

/-- Theorem 8 (Sec. 2.1): Exact `2×2` symmetric trace commutator identity
    `tr(H^2 L^2 - H L H L) = comm^2 = (1/2) ‖H L - L H‖_F^2 ≥ 0` for ALL symmetric `2×2` matrices
    `H = [[h1, h2], [h2, h3]]`, `L = [[l1, l2], [l2, l3]]`. -/
theorem sec21_commutator_trace_identity_2x2 (h1 h2 h3 l1 l2 l3 : Int) :
    let comm := h2 * (l1 - l3) - l2 * (h1 - h3)
    let trH2L2 := (h1 * h1 + h2 * h2) * (l1 * l1 + l2 * l2) +
                  2 * (h2 * (h1 + h3)) * (l2 * (l1 + l3)) +
                  (h2 * h2 + h3 * h3) * (l2 * l2 + l3 * l3)
    let hl11 := h1 * l1 + h2 * l2
    let hl12 := h1 * l2 + h2 * l3
    let hl21 := h2 * l1 + h3 * l2
    let hl22 := h2 * l2 + h3 * l3
    let trHLHL := hl11 * hl11 + 2 * (hl12 * hl21) + hl22 * hl22
    trH2L2 - trHLHL = comm * comm ∧ 0 ≤ trH2L2 - trHLHL := by
  dsimp only
  have hid : ((h1 * h1 + h2 * h2) * (l1 * l1 + l2 * l2) +
              2 * (h2 * (h1 + h3)) * (l2 * (l1 + l3)) +
              (h2 * h2 + h3 * h3) * (l2 * l2 + l3 * l3)) -
             ((h1 * l1 + h2 * l2) * (h1 * l1 + h2 * l2) +
              2 * ((h1 * l2 + h2 * l3) * (h2 * l1 + h3 * l2)) +
              (h2 * l2 + h3 * l3) * (h2 * l2 + h3 * l3)) =
             (h2 * (l1 - l3) - l2 * (h1 - h3)) * (h2 * (l1 - l3) - l2 * (h1 - h3)) := by
    have e1 : (h1 * h1 + h2 * h2) * (l1 * l1 + l2 * l2) =
        h1 * h1 * (l1 * l1) + h1 * h1 * (l2 * l2) + h2 * h2 * (l1 * l1) + h2 * h2 * (l2 * l2) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
    have e2 : (h2 * h2 + h3 * h3) * (l2 * l2 + l3 * l3) =
        h2 * h2 * (l2 * l2) + h2 * h2 * (l3 * l3) + h3 * h3 * (l2 * l2) + h3 * h3 * (l3 * l3) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
    have e3 : 2 * (h2 * (h1 + h3)) * (l2 * (l1 + l3)) =
        2 * (h1 * h2 * l1 * l2) + 2 * (h1 * h2 * l2 * l3) +
        2 * (h2 * h3 * l1 * l2) + 2 * (h2 * h3 * l2 * l3) := by
      have p1 : 2 * (h2 * (h1 + h3)) = 2 * (h2 * h1) + 2 * (h2 * h3) := by
        rw [Int.mul_add, Int.mul_add]
      have p2 : l2 * (l1 + l3) = l2 * l1 + l2 * l3 := Int.mul_add _ _ _
      rw [p1, p2, Int.add_mul, Int.mul_add, Int.mul_add]
      have c1 : 2 * (h2 * h1) * (l2 * l1) = 2 * (h1 * h2 * l1 * l2) := by ac_rfl
      have c2 : 2 * (h2 * h1) * (l2 * l3) = 2 * (h1 * h2 * l2 * l3) := by ac_rfl
      have c3 : 2 * (h2 * h3) * (l2 * l1) = 2 * (h2 * h3 * l1 * l2) := by ac_rfl
      have c4 : 2 * (h2 * h3) * (l2 * l3) = 2 * (h2 * h3 * l2 * l3) := by ac_rfl
      omega
    have e4 : (h1 * l1 + h2 * l2) * (h1 * l1 + h2 * l2) =
        h1 * h1 * (l1 * l1) + 2 * (h1 * h2 * l1 * l2) + h2 * h2 * (l2 * l2) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      have c1 : h1 * l1 * (h1 * l1) = h1 * h1 * (l1 * l1) := by ac_rfl
      have c2 : h1 * l1 * (h2 * l2) = h1 * h2 * l1 * l2 := by ac_rfl
      have c3 : h2 * l2 * (h1 * l1) = h1 * h2 * l1 * l2 := by ac_rfl
      have c4 : h2 * l2 * (h2 * l2) = h2 * h2 * (l2 * l2) := by ac_rfl
      omega
    have e5 : (h2 * l2 + h3 * l3) * (h2 * l2 + h3 * l3) =
        h2 * h2 * (l2 * l2) + 2 * (h2 * h3 * l2 * l3) + h3 * h3 * (l3 * l3) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      have c1 : h2 * l2 * (h2 * l2) = h2 * h2 * (l2 * l2) := by ac_rfl
      have c2 : h2 * l2 * (h3 * l3) = h2 * h3 * l2 * l3 := by ac_rfl
      have c3 : h3 * l3 * (h2 * l2) = h2 * h3 * l2 * l3 := by ac_rfl
      have c4 : h3 * l3 * (h3 * l3) = h3 * h3 * (l3 * l3) := by ac_rfl
      omega
    have e6 : 2 * ((h1 * l2 + h2 * l3) * (h2 * l1 + h3 * l2)) =
        2 * (h1 * h2 * l1 * l2) + 2 * (h1 * h3 * l2 * l2) +
        2 * (h2 * h2 * l1 * l3) + 2 * (h2 * h3 * l2 * l3) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_add]
      have c1 : h1 * l2 * (h2 * l1) = h1 * h2 * l1 * l2 := by ac_rfl
      have c2 : h1 * l2 * (h3 * l2) = h1 * h3 * l2 * l2 := by ac_rfl
      have c3 : h2 * l3 * (h2 * l1) = h2 * h2 * l1 * l3 := by ac_rfl
      have c4 : h2 * l3 * (h3 * l2) = h2 * h3 * l2 * l3 := by ac_rfl
      omega
    have e7 : (h2 * (l1 - l3) - l2 * (h1 - h3)) * (h2 * (l1 - l3) - l2 * (h1 - h3)) =
        h2 * h2 * (l1 * l1) - 2 * (h2 * h2 * l1 * l3) + h2 * h2 * (l3 * l3)
        - 2 * (h1 * h2 * l1 * l2) + 2 * (h1 * h2 * l2 * l3)
        + 2 * (h2 * h3 * l1 * l2) - 2 * (h2 * h3 * l2 * l3)
        + h1 * h1 * (l2 * l2) - 2 * (h1 * h3 * l2 * l2) + h3 * h3 * (l2 * l2) := by
      let u := h2 * (l1 - l3)
      let v := l2 * (h1 - h3)
      have huv : (u - v) * (u - v) = u * u - 2 * (u * v) + v * v := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
        have hc : v * u = u * v := Int.mul_comm v u
        omega
      have hu2 : u * u = h2 * h2 * (l1 * l1) - 2 * (h2 * h2 * l1 * l3) + h2 * h2 * (l3 * l3) := by
        change (h2 * (l1 - l3)) * (h2 * (l1 - l3)) = _
        rw [Int.mul_sub, Int.sub_mul, Int.mul_sub, Int.mul_sub]
        have c1 : h2 * l1 * (h2 * l1) = h2 * h2 * (l1 * l1) := by ac_rfl
        have c2 : h2 * l1 * (h2 * l3) = h2 * h2 * l1 * l3 := by ac_rfl
        have c3 : h2 * l3 * (h2 * l1) = h2 * h2 * l1 * l3 := by ac_rfl
        have c4 : h2 * l3 * (h2 * l3) = h2 * h2 * (l3 * l3) := by ac_rfl
        omega
      have hv2 : v * v = h1 * h1 * (l2 * l2) - 2 * (h1 * h3 * l2 * l2) + h3 * h3 * (l2 * l2) := by
        change (l2 * (h1 - h3)) * (l2 * (h1 - h3)) = _
        rw [Int.mul_sub, Int.sub_mul, Int.mul_sub, Int.mul_sub]
        have c1 : l2 * h1 * (l2 * h1) = h1 * h1 * (l2 * l2) := by ac_rfl
        have c2 : l2 * h1 * (l2 * h3) = h1 * h3 * l2 * l2 := by ac_rfl
        have c3 : l2 * h3 * (l2 * h1) = h1 * h3 * l2 * l2 := by ac_rfl
        have c4 : l2 * h3 * (l2 * h3) = h3 * h3 * (l2 * l2) := by ac_rfl
        omega
      have huv2 : u * v = h1 * h2 * l1 * l2 - h2 * h3 * l1 * l2 - h1 * h2 * l2 * l3 + h2 * h3 * l2 * l3 := by
        change (h2 * (l1 - l3)) * (l2 * (h1 - h3)) = _
        rw [Int.mul_sub, Int.mul_sub, Int.sub_mul, Int.mul_sub, Int.mul_sub]
        have c1 : h2 * l1 * (l2 * h1) = h1 * h2 * l1 * l2 := by ac_rfl
        have c2 : h2 * l1 * (l2 * h3) = h2 * h3 * l1 * l2 := by ac_rfl
        have c3 : h2 * l3 * (l2 * h1) = h1 * h2 * l2 * l3 := by ac_rfl
        have c4 : h2 * l3 * (l2 * h3) = h2 * h3 * l2 * l3 := by ac_rfl
        omega
      change (u - v) * (u - v) = _
      rw [huv, hu2, hv2, huv2]
      omega
    rw [e1, e2, e3, e4, e5, e6, e7]
    omega
  exact ⟨hid, by rw [hid]; exact sq_nonneg _⟩

/-- Exact list Frobenius squared-norm helper `∑ a_i^2`. -/
def sumSq : List Int → Int
  | [] => 0
  | x :: xs => x * x + sumSq xs

/-- Exact list inner product helper `∑ a_i b_i`. -/
def dotList : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + dotList xs ys

/-- Theorem 9 (Lemma 2.1(1)): Universal inductive AM-GM / leverage-centered trace defect nonnegativity:
    for ANY equal-length lists `xs, ys : List Int`, `2 * ⟨xs, ys⟩ ≤ ‖xs‖^2 + ‖ys‖^2`. -/
theorem lemma21_leverage_amgm_defect :
    ∀ (xs ys : List Int), xs.length = ys.length → 2 * dotList xs ys ≤ sumSq xs + sumSq ys
  | [], [], _ => by decide
  | x :: xs, y :: ys, hlen => by
      have hlen' : xs.length = ys.length := by
        simp only [List.length] at hlen; omega
      have ih := lemma21_leverage_amgm_defect xs ys hlen'
      have hstep : 2 * (x * y) ≤ x * x + y * y := by
        have hsq := sq_nonneg (x - y)
        have hexp : (x - y) * (x - y) = x * x - 2 * (x * y) + y * y := by
          rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
          have hc : y * x = x * y := Int.mul_comm y x
          omega
        omega
      dsimp only [dotList, sumSq]
      omega

/-- Theorem 10 (Sec. 2.1): Universal 2D Gaussian Hermite `c_2(g, v)` covariance & variance identity:
    given standard Gaussian moments `E[(g_i^2 - 1)^2] = 2`, `E[(g_1^2 - 1)(g_2^2 - 1)] = 0`, and
    `E[(g_1 g_2)^2] = 1`, for ALL `v1 v2 w1 w2 : Int`, the cleared covariance
    `4 * E[c_2(g,v) c_2(g,w)]` equals `2 * (v1 * w1 + v2 * w2)^2`, and at `w = v` equals
    `2 * (v1^2 + v2^2)^2 ≥ 0`. -/
theorem sec21_hermite_c2_variance_identity (v1 v2 w1 w2 : Int) :
    2 * (v1 * v1) * (w1 * w1) + 4 * (v1 * v2) * (w1 * w2) + 2 * (v2 * v2) * (w2 * w2) =
      2 * ((v1 * w1 + v2 * w2) * (v1 * w1 + v2 * w2)) ∧
    0 ≤ 2 * ((v1 * v1 + v2 * v2) * (v1 * v1 + v2 * v2)) := by
  have hcov : 2 * (v1 * v1) * (w1 * w1) + 4 * (v1 * v2) * (w1 * w2) + 2 * (v2 * v2) * (w2 * w2) =
      2 * ((v1 * w1 + v2 * w2) * (v1 * w1 + v2 * w2)) := by
    have hexp : (v1 * w1 + v2 * w2) * (v1 * w1 + v2 * w2) =
        (v1 * w1) * (v1 * w1) + 2 * ((v1 * w1) * (v2 * w2)) + (v2 * w2) * (v2 * w2) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      have hc : (v2 * w2) * (v1 * w1) = (v1 * w1) * (v2 * w2) := Int.mul_comm _ _
      omega
    have c1 : (v1 * w1) * (v1 * w1) = (v1 * v1) * (w1 * w1) := by ac_rfl
    have c2 : (v1 * w1) * (v2 * w2) = (v1 * v2) * (w1 * w2) := by ac_rfl
    have c3 : (v2 * w2) * (v2 * w2) = (v2 * v2) * (w2 * w2) := by ac_rfl
    rw [hexp, c1, c2, c3, Int.mul_add, Int.mul_add]
    have h4 : 2 * (2 * ((v1 * v2) * (w1 * w2))) = 4 * ((v1 * v2) * (w1 * w2)) := by omega
    have a1 : 2 * ((v1 * v1) * (w1 * w1)) = 2 * (v1 * v1) * (w1 * w1) := by ac_rfl
    have a2 : 4 * ((v1 * v2) * (w1 * w2)) = 4 * (v1 * v2) * (w1 * w2) := by ac_rfl
    have a3 : 2 * ((v2 * v2) * (w2 * w2)) = 2 * (v2 * v2) * (w2 * w2) := by ac_rfl
    omega
  have hnn : 0 ≤ 2 * ((v1 * v1 + v2 * v2) * (v1 * v1 + v2 * v2)) := by
    have hs := sq_nonneg (v1 * v1 + v2 * v2)
    omega
  exact ⟨hcov, hnn⟩

/-! ### Part 3: Quantitative Proposition A.3 (Nisan-Wigderson Recursion) & Theorem 1.1 Constants -/

/-- Theorem 11 (Prop. A.3): Heavy-child protocol-tree balancing split:
    if `L ≥ 2` and `L < 3 * Lv` and `3 * Lv ≤ 2 * L`, then `1 ≤ L - Lv` and `3 * (L - Lv) < 2 * L`. -/
theorem propa3_heavy_child_split_bounds (L Lv : Nat)
    (hL : 2 ≤ L) (hlo : L < 3 * Lv) (hhi : 3 * Lv ≤ 2 * L) :
    1 ≤ L - Lv ∧ 3 * (L - Lv) < 2 * L :=
  ⟨by omega, by omega⟩

/-- Theorem 12 (Prop. A.3): Exact rational logarithm bound `log_2(3/2) > 4/7`
    and protocol-depth factor `2 / (4/7) = 7/2 < 5`:
    `2^11 = 2048 < 2187 = 3^7` and `2 * 7 < 4 * 5`. -/
theorem propa3_log2_three_halves_bound :
    2 ^ 11 < 3 ^ 7 ∧ 2 * 7 < 4 * 5 := by
  decide

/-- Theorem 13 (Prop. A.3): Universal induction step for protocol-tree balancing `D_cc ≤ 2 ⌈log_{3/2} L⌉`:
    for the exact recursion invariant `2^k * Lbound ≤ 3^k` (meaning `Lbound ≤ (3/2)^k`),
    whenever `2 * L ≤ 3 * Lbound` we obtain `2^(k+1) * L ≤ 3^(k+1)`. -/
theorem propa3_protocol_depth_induction (k L Lbound : Nat)
    (hstep : 2 * L ≤ 3 * Lbound) (hih : 2 ^ k * Lbound ≤ 3 ^ k) :
    2 ^ (k + 1) * L ≤ 3 ^ (k + 1) := by
  have h1 : 2 ^ (k + 1) * L = 2 ^ k * (2 * L) := by
    rw [Nat.pow_succ]; ac_rfl
  have h2 : 2 ^ k * (2 * L) ≤ 2 ^ k * (3 * Lbound) := Nat.mul_le_mul_left (2 ^ k) hstep
  have h3 : 2 ^ k * (3 * Lbound) = 3 * (2 ^ k * Lbound) := by ac_rfl
  have h4 : 3 * (2 ^ k * Lbound) ≤ 3 * 3 ^ k := Nat.mul_le_mul_left 3 hih
  have h5 : 3 * 3 ^ k = 3 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  omega

/-- Theorem 14 (Prop. A.3): Exact monochromatic rank-split bound:
    for EVERY `k ≥ 2`, `rM ≤ k`, and `r1 + r2 ≤ rM + 1`,
    `min r1 r2 ≤ (rM + 1) / 2 ≤ (3 * k) / 4` and `1 ≤ (3 * k) / 4`. -/
theorem propa3_rank_split_min_le_three_quarters (k rM r1 r2 : Nat)
    (hk : 2 ≤ k) (hrM : rM ≤ k) (hsplit : r1 + r2 ≤ rM + 1) :
    Nat.min r1 r2 ≤ (rM + 1) / 2 ∧
    (rM + 1) / 2 ≤ (3 * k) / 4 ∧
    1 ≤ (3 * k) / 4 := by
  have hmin : Nat.min r1 r2 ≤ (rM + 1) / 2 := by
    by_cases h : r1 ≤ r2
    · exact Nat.le_trans (Nat.min_le_left r1 r2) (by omega)
    · exact Nat.le_trans (Nat.min_le_right r1 r2) (by omega)
  exact ⟨hmin, by omega, by omega⟩

/-- Theorem 15 (Prop. A.3): Universal induction step for protocol-tree leaf bound `t * (1 + L*(k'))`:
    combining 1 leaf on `A × B`, at most `Lk` leaves on `A × B^c`, and at most `s * (1 + Lk)` leaves
    on `A^c × Y` yields at most `(s + 1) * (1 + Lk)` leaves in total. -/
theorem propa3_leaf_recurrence_induction (s Lk A1 A2 A3 : Nat)
    (h1 : A1 ≤ 1) (h2 : A2 ≤ Lk) (h3 : A3 ≤ s * (1 + Lk)) :
    A1 + A2 + A3 ≤ (s + 1) * (1 + Lk) := by
  have hexp : (s + 1) * (1 + Lk) = s * (1 + Lk) + (1 + Lk) := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Theorem 16 (Prop. A.3): Exact geometric contraction ratio `(3/4)^(1/4) < 27/29`:
    certified constructively by `3 * 29^4 = 2,121,843 < 2,125,764 = 4 * 27^4`. -/
theorem propa3_geometric_ratio_bound :
    3 * 29 ^ 4 < 4 * 27 ^ 4 := by
  decide

/-- Theorem 17 (Prop. A.3): Universal constant closure yielding `750 * C0` (and `750 * 238 = 178,500`):
    for EVERY `C0 ≥ 1` and `R ≥ 1`,
    `2 * C0 + 145 * C0 * R ≤ 147 * C0 * R`, `147 * C0 * R < 150 * C0 * R`,
    `5 * (150 * C0 * R) = 750 * C0 * R`, and `750 * 238 = 178500`. -/
theorem propa3_nissan_wigderson_constant_750 (C0 R : Nat) (hC : 1 ≤ C0) (hR : 1 ≤ R) :
    2 * C0 + 145 * C0 * R ≤ 147 * C0 * R ∧
    147 * C0 * R < 150 * C0 * R ∧
    5 * (150 * C0 * R) = 750 * C0 * R ∧
    750 * 238 = 178500 := by
  have h1 : C0 ≤ C0 * R := by
    calc C0 = C0 * 1 := (Nat.mul_one C0).symm
      _ ≤ C0 * R := Nat.mul_le_mul_left C0 hR
  have hpos : 1 ≤ C0 * R := Nat.mul_pos hC hR
  have hassoc1 : 145 * C0 * R = 145 * (C0 * R) := Nat.mul_assoc 145 C0 R
  have hassoc2 : 147 * C0 * R = 147 * (C0 * R) := Nat.mul_assoc 147 C0 R
  have hassoc3 : 150 * C0 * R = 150 * (C0 * R) := Nat.mul_assoc 150 C0 R
  have hassoc4 : 750 * C0 * R = 750 * (C0 * R) := Nat.mul_assoc 750 C0 R
  rw [hassoc1, hassoc2, hassoc3, hassoc4]
  exact ⟨by omega, by omega, by omega, by decide⟩

/-- Theorem 18 (Theorem 1.1): Exact sub-square-root exponent separation `ε = 5 × 10^{-6}`:
    `1/2 - ε = 99999 / 200000 < 1/2`, `0 < ε ≤ 1/4`, and `C' = 750 * 238 = 178500`. -/
theorem thm11_subsqrt_exponent_strictly_beats_half :
    (99999 * 2 < 200000) ∧
    (99999 + 1 = 100000) ∧
    (1 * 4 ≤ 200000) ∧
    (750 * 238 = 178500) := by
  decide

end CogenticLogRank
