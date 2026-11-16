import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Symbolic period and dual identities

The coefficient field and all entries are arbitrary. These are the algebraic
identities in Theorems 7.5, 8.7, and 8.10. No period ring or Galois action is
postulated as a new axiom. The actual period-ring elements and their
transformation laws are supplied by the written arguments in the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SharpMatrix

variable {K : Type*} [Field K]

def kummerAction (a b : K) : Matrix (Fin 2) (Fin 2) K := !![1, 0; b, a]
def kummerPeriod (u t : K) : Matrix (Fin 2) (Fin 2) K := !![1, 0; -u / t, t⁻¹]

theorem kummer_period_invariance (a b u t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    kummerAction a b * kummerPeriod (u + b * t) (a * t) = kummerPeriod u t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kummerAction, kummerPeriod, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

theorem kummer_period_determinant (u t : K) : (kummerPeriod u t).det = t⁻¹ := by
  simp [kummerPeriod, Matrix.det_fin_two]

def ellipticAction (a ψ : K) : Matrix (Fin 2) (Fin 2) K := !![ψ, 0; 0, a / ψ]
def ellipticPeriod (Ω t : K) : Matrix (Fin 2) (Fin 2) K := !![Ω, 0; 0, (t * Ω)⁻¹]

theorem elliptic_period_invariance (a ψ Ω t : K)
    (ha : a ≠ 0) (hψ : ψ ≠ 0) (hΩ : Ω ≠ 0) (ht : t ≠ 0) :
    ellipticAction a ψ * ellipticPeriod (Ω / ψ) (a * t) = ellipticPeriod Ω t := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [ellipticAction, ellipticPeriod, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring

theorem elliptic_period_determinant (Ω t : K) (hΩ : Ω ≠ 0) :
    (ellipticPeriod Ω t).det = t⁻¹ := by
  simp [ellipticPeriod, Matrix.det_fin_two]
  by_cases ht : t = 0
  · simp [ht]
  · field_simp [hΩ, ht]

/-- Tensoring the two proved transformation identities gives the mixed
elliptic-Kummer identity, without sampling any entries. -/
theorem mixed_tensor_period_invariance (a b u t ψ Ω : K)
    (ha : a ≠ 0) (ht : t ≠ 0) (hψ : ψ ≠ 0) (hΩ : Ω ≠ 0) :
    Matrix.kroneckerMap (fun x y => x * y) (kummerAction a b) (ellipticAction a ψ) *
      Matrix.kroneckerMap (fun x y => x * y)
        (kummerPeriod (u + b * t) (a * t)) (ellipticPeriod (Ω / ψ) (a * t)) =
      Matrix.kroneckerMap (fun x y => x * y) (kummerPeriod u t) (ellipticPeriod Ω t) := by
  rw [← Matrix.mul_kronecker_mul]
  rw [kummer_period_invariance a b u t ha ht,
    elliptic_period_invariance a ψ Ω t ha hψ hΩ ht]

/-- Evaluation with the inverse-transpose Tate-dual matrix in every rank. -/
theorem tate_dual_evaluation {n : ℕ} (P : Matrix (Fin n) (Fin n) K) (t : K)
    (hP : P.det ≠ 0) :
    P.transpose * (t⁻¹ • P⁻¹.transpose) = t⁻¹ • (1 : Matrix (Fin n) (Fin n) K) := by
  rw [Matrix.mul_smul, ← Matrix.transpose_mul]
  rw [Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP), Matrix.transpose_one]

/-- An arbitrary weighted inverse-node Vandermonde matrix. -/
def artinPeriodMatrix (n : ℕ) (α : K) (a : Fin n → ℕ) (nodes : Fin n → K) :
    Matrix (Fin n) (Fin n) K :=
  fun r i => (α ^ a i)⁻¹ * (nodes i)⁻¹ ^ r.val

theorem artin_matrix_factorization (n : ℕ) (α : K) (a : Fin n → ℕ) (nodes : Fin n → K) :
    artinPeriodMatrix n α a nodes =
      (Matrix.vandermonde (fun i => (nodes i)⁻¹)).transpose *
        Matrix.diagonal (fun i => (α ^ a i)⁻¹) := by
  ext r i
  simp [artinPeriodMatrix, Matrix.mul_diagonal, Matrix.vandermonde_apply, mul_comm]

/-- The algebraic Artin matrix in (8.12) is invertible whenever its nodes
are distinct and its common scalar is nonzero, in arbitrary rank. -/
theorem artin_matrix_determinant_ne_zero (n : ℕ) (α : K) (a : Fin n → ℕ)
    (nodes : Fin n → K) (hα : α ≠ 0) (hnodes : Function.Injective nodes) :
    (artinPeriodMatrix n α a nodes).det ≠ 0 := by
  have hinv : Function.Injective (fun i => (nodes i)⁻¹) := by
    intro i j hij
    exact hnodes (inv_injective hij)
  rw [artin_matrix_factorization, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal]
  apply mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hinv)
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => inv_ne_zero (pow_ne_zero _ hα))

end SharpMatrix
