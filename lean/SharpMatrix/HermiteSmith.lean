import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Hermite coordinates and the nontrivial Smith block

General symbolic identities used in Theorem 8.3 and Proposition 7.1.
The Smith calculation proves an explicit unimodular equivalence over every
commutative ring. Interpreting it as invariant factors uses the DVR input
specified in the manuscript.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SharpMatrix

section Hermite

open Polynomial
variable {R : Type*} [CommRing R]

noncomputable def hermitePolynomial (k : ℕ) (ζ c : R) (a b : R[X]) : R[X] :=
  a + (X ^ k - C ζ) * b + C c * (X ^ k - C ζ) ^ 2

theorem hermite_value (k : ℕ) (ζ c ξ : R) (a b : R[X]) (hξ : ξ ^ k = ζ) :
    (hermitePolynomial k ζ c a b).eval ξ = a.eval ξ := by
  simp [hermitePolynomial, hξ]

theorem hermite_value_at_one (k : ℕ) (ζ c : R) (a b : R[X]) :
    (hermitePolynomial k ζ c a b).eval 1 =
      a.eval 1 + (1 - ζ) * b.eval 1 + (1 - ζ) ^ 2 * c := by
  simp [hermitePolynomial]
  ring

theorem normalized_derivative_factor (k : ℕ) (hk : 1 ≤ k) (ζ ξ : R)
    (hξ : ξ ^ k = ζ) :
    ξ * ((X ^ k - C ζ : R[X]).derivative.eval ξ) = (k : R) * ζ := by
  have hp : ξ * ξ ^ (k - 1) = ζ := by
    rw [← pow_succ', Nat.sub_add_cancel hk, hξ]
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero,
    eval_mul, eval_C, eval_pow, eval_X]
  calc
    ξ * ((k : R) * ξ ^ (k - 1)) = (k : R) * (ξ * ξ ^ (k - 1)) := by ring
    _ = (k : R) * ζ := by rw [hp]

theorem hermite_normalized_derivative (k : ℕ) (hk : 1 ≤ k) (ζ c ξ : R)
    (a b : R[X]) (hξ : ξ ^ k = ζ) :
    ξ * ((hermitePolynomial k ζ c a b).derivative.eval ξ) =
      ξ * (a.derivative.eval ξ) + (k : R) * ζ * b.eval ξ := by
  have hzero : (X ^ k - C ζ : R[X]).eval ξ = 0 := by simp [hξ]
  have hfactor := normalized_derivative_factor k hk ζ ξ hξ
  simp only [hermitePolynomial, derivative_add, derivative_mul, derivative_pow,
    derivative_C, zero_mul, zero_add, eval_add, eval_mul, eval_pow, eval_C,
    hzero, mul_zero, zero_add, add_zero, pow_one]
  norm_num only [Nat.reduceSub, zero_pow, mul_zero, zero_mul, add_zero]
  calc
    ξ * (a.derivative.eval ξ + (X ^ k - C ζ : R[X]).derivative.eval ξ * b.eval ξ) =
      ξ * a.derivative.eval ξ +
        (ξ * (X ^ k - C ζ : R[X]).derivative.eval ξ) * b.eval ξ := by ring
    _ = _ := by rw [hfactor]

end Hermite

section Smith

variable {R : Type*} [CommRing R]

def smithBlock (π u : R) : Matrix (Fin 2) (Fin 2) R := !![π * u, 0; π, π ^ 2]
def smithLeft (u : R) : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, u]
def smithLeftInv (u : R) : Matrix (Fin 2) (Fin 2) R := !![u, -1; 1, 0]
def smithRight (π : R) : Matrix (Fin 2) (Fin 2) R := !![1, -π; 0, 1]
def smithRightInv (π : R) : Matrix (Fin 2) (Fin 2) R := !![1, π; 0, 1]

theorem smith_block_reduction (π u : R) :
    smithLeft u * smithBlock π u * smithRight π =
      Matrix.diagonal (![π, π ^ 2 * u]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [smithLeft, smithBlock, smithRight, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem smith_left_inverse (u : R) :
    smithLeftInv u * smithLeft u = 1 ∧ smithLeft u * smithLeftInv u = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [smithLeftInv, smithLeft, Matrix.mul_apply, Fin.sum_univ_two]

theorem smith_right_inverse (π : R) :
    smithRightInv π * smithRight π = 1 ∧ smithRight π * smithRightInv π = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [smithRightInv, smithRight, Matrix.mul_apply, Fin.sum_univ_two]

theorem smith_change_determinants (π u : R) :
    (smithLeft u).det = 1 ∧ (smithRight π).det = 1 := by
  simp [smithLeft, smithRight, Matrix.det_fin_two]

theorem smith_diagonal_divisibility (π u : R) : π ∣ π ^ 2 * u := by
  exact ⟨π * u, by ring⟩

/-- The rank-three coefficient pairing in equation (7.5). -/
def coefficientGram (s b : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1; 0, 1, s; 1, s, s ^ 2 - b]

theorem coefficient_gram_determinant (s b : R) : (coefficientGram s b).det = -1 := by
  simp [coefficientGram, Matrix.det_fin_three]

end Smith

end SharpMatrix
