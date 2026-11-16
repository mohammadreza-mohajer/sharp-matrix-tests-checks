import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Weighted monic division

The general algebraic lemma behind Lemma 8.5 and the ramified lower bound
in Theorem 8.6 of "Sharp matrix tests and integral gluing over affine p-adic
groups". All parameters are quantified. The coefficient ring is arbitrary.

The proof first reduces the monic relation to a quadratic relation for x^k.
Only the first two levels of the stated coefficient filtration are needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SharpMatrix

section Quadratic

variable {R : Type*} [CommRing R]

/-- A quadratic relation with coefficients of weights one and two gives
weighted formulas for every power. -/
theorem weighted_power_formula (x π b c : R)
    (h : x ^ 2 = π * b * x + π ^ 2 * c) (m : ℕ) :
    ∃ B C : R, x ^ (m + 1) = π ^ m * B * x + π ^ (m + 1) * C := by
  induction m with
  | zero =>
      refine ⟨1, 0, ?_⟩
      simp
  | succ m ih =>
      obtain ⟨B, C, hBC⟩ := ih
      refine ⟨B * b + C, B * c, ?_⟩
      have hxx : x * x = π * b * x + π ^ 2 * c := by
        simpa only [pow_two] using h
      calc
        x ^ (m + 1 + 1) = (π ^ m * B * x + π ^ (m + 1) * C) * x := by
          rw [pow_succ, hBC]
        _ = π ^ m * B * (x * x) + π ^ (m + 1) * C * x := by ring
        _ = π ^ (m + 1) * (B * b + C) * x + π ^ (m + 1 + 1) * (B * c) := by
          rw [hxx]
          simp only [pow_succ]
          ring

/-- Nilpotence follows from the weighted quadratic relation. -/
theorem weighted_quadratic_nilpotent (x π b c : R) (r : ℕ)
    (h : x ^ 2 = π * b * x + π ^ 2 * c) (hπ : π ^ r = 0) :
    x ^ (r + 1) = 0 := by
  obtain ⟨B, C, hBC⟩ := weighted_power_formula x π b c h r
  rw [hBC, hπ, pow_succ, hπ]
  ring

end Quadratic

section WeightedRelation

variable {R : Type*} [CommRing R]

/-- The two coefficient divisibilities implied by the weighted hypothesis. -/
def TwoLevelCoefficients (π : R) (n k : ℕ) (a : Fin n → R) : Prop :=
  ∀ i, if n ≤ i.val + k then π ∣ a i else π ^ 2 ∣ a i

/-- A coefficient dropping degree by s has at least the ceiling of s/k
factors of π. The existential formulation avoids rounding conventions. -/
def WeightedCoefficients (π : R) (n k : ℕ) (a : Fin n → R) : Prop :=
  ∀ i, ∃ q : ℕ, π ^ q ∣ a i ∧ n ≤ i.val + k * q

theorem weighted_implies_two_level (π : R) (n k : ℕ) (a : Fin n → R)
    (ha : WeightedCoefficients π n k a) : TwoLevelCoefficients π n k a := by
  intro i
  obtain ⟨q, hdiv, hweight⟩ := ha i
  split_ifs with hi
  · have hq : 1 ≤ q := by
      by_contra hq
      have : q = 0 := by omega
      simp [this] at hweight
      omega
    exact dvd_trans (by simpa using (pow_dvd_pow π hq)) hdiv
  · have hq : 2 ≤ q := by
      by_contra hq
      have hcases : q = 0 ∨ q = 1 := by omega
      rcases hcases with hzero | hone
      · simp [hzero] at hweight
        omega
      · simp [hone] at hweight
        exact hi hweight
    exact dvd_trans (pow_dvd_pow π hq) hdiv

/-- A monic relation of degree at most 2k gives the required quadratic
relation for the kth power. -/
theorem monic_relation_to_quadratic (x π : R) (n k : ℕ) (a : Fin n → R)
    (hn : n ≤ 2 * k) (ha : TwoLevelCoefficients π n k a)
    (hroot : x ^ n + ∑ i : Fin n, a i * x ^ i.val = 0) :
    ∃ b c : R, (x ^ k) ^ 2 = π * b * x ^ k + π ^ 2 * c := by
  classical
  have hterm (i : Fin n) : ∃ b c : R,
      a i * x ^ (2 * k - n + i.val) = π * b * x ^ k + π ^ 2 * c := by
    by_cases hi : n ≤ i.val + k
    · obtain ⟨u, hu⟩ := by simpa [TwoLevelCoefficients, hi] using ha i
      have hexp : k ≤ 2 * k - n + i.val := by omega
      refine ⟨u * x ^ (2 * k - n + i.val - k), 0, ?_⟩
      rw [hu]
      have hp : x ^ (2 * k - n + i.val) =
          x ^ (2 * k - n + i.val - k) * x ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hexp]
      rw [hp]
      ring
    · obtain ⟨u, hu⟩ := by simpa [TwoLevelCoefficients, hi] using ha i
      refine ⟨0, u * x ^ (2 * k - n + i.val), ?_⟩
      rw [hu]
      ring
  choose b c hbc using hterm
  have hpower : x ^ (2 * k) + ∑ i : Fin n, a i * x ^ (2 * k - n + i.val) = 0 := by
    calc
      _ = x ^ (2 * k - n) * (x ^ n + ∑ i : Fin n, a i * x ^ i.val) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · rw [← pow_add, Nat.sub_add_cancel hn]
        · apply Finset.sum_congr rfl
          intro i _
          rw [pow_add]
          ring
      _ = 0 := by rw [hroot, mul_zero]
  refine ⟨-(∑ i, b i), -(∑ i, c i), ?_⟩
  rw [show (x ^ k) ^ 2 = x ^ (2 * k) by rw [← pow_mul]; congr 1; omega]
  have hx : x ^ (2 * k) = -(∑ i : Fin n, a i * x ^ (2 * k - n + i.val)) := by
    exact eq_neg_of_add_eq_zero_left hpower
  rw [hx]
  simp_rw [hbc]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- General weighted nilpotence for a root of a monic relation. -/
theorem weighted_relation_nilpotent (x π : R) (n k p : ℕ) (a : Fin n → R)
    (hp : 1 ≤ p) (hn : n ≤ 2 * k)
    (ha : WeightedCoefficients π n k a)
    (hroot : x ^ n + ∑ i : Fin n, a i * x ^ i.val = 0)
    (hπ : π ^ (p - 1) = 0) : x ^ (p * k) = 0 := by
  obtain ⟨b, c, hquad⟩ := monic_relation_to_quadratic x π n k a hn
    (weighted_implies_two_level π n k a ha) hroot
  have hnil := weighted_quadratic_nilpotent (x ^ k) π b c (p - 1) hquad hπ
  simpa only [Nat.sub_add_cancel hp, ← pow_mul, Nat.mul_comm k p] using hnil

end WeightedRelation

section PolynomialDivision

variable {R : Type*} [CommRing R]
open Polynomial

/-- The monic polynomial encoded by its lower n coefficients. -/
noncomputable def monicPresentation (n : ℕ) (a : Fin n → R) : R[X] :=
  X ^ n + ∑ i : Fin n, C (a i) * X ^ i.val

/-- Lemma 8.5, in a form independent of discrete valuation rings:
the displayed monic polynomial divides X^(pk) over every ring in which
π^(p-1)=0 and its coefficients satisfy the stated weight bounds. -/
theorem weighted_monic_division (π : R) (n k p : ℕ) (a : Fin n → R)
    (hp : 1 ≤ p) (hn : n ≤ 2 * k)
    (ha : WeightedCoefficients π n k a) (hπ : π ^ (p - 1) = 0) :
    monicPresentation n a ∣ (X : R[X]) ^ (p * k) := by
  let F := monicPresentation n a
  let I : Ideal R[X] := Ideal.span {F}
  let q : R[X] →+* R[X] ⧸ I := Ideal.Quotient.mk I
  let x := q X
  let π' := q (C π)
  let a' : Fin n → R[X] ⧸ I := fun i => q (C (a i))
  have hzero : q F = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  have hroot : x ^ n + ∑ i : Fin n, a' i * x ^ i.val = 0 := by
    simpa only [F, monicPresentation, map_add, map_sum, map_mul, map_pow] using hzero
  have hweight : WeightedCoefficients π' n k a' := by
    intro i
    obtain ⟨r, ⟨u, hu⟩, hr⟩ := ha i
    refine ⟨r, ⟨q (C u), ?_⟩, hr⟩
    change q (C (a i)) = q (C π) ^ r * q (C u)
    rw [hu, map_mul, map_pow, map_mul, map_pow]
  have hπ' : π' ^ (p - 1) = 0 := by
    change q (C π) ^ (p - 1) = 0
    rw [← map_pow, ← map_pow, hπ, map_zero, map_zero]
  have hnil := weighted_relation_nilpotent x π' n k p a' hp hn hweight hroot hπ'
  have hmem : (X : R[X]) ^ (p * k) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_pow] using hnil
  exact Ideal.mem_span_singleton.mp hmem

end PolynomialDivision

end SharpMatrix
