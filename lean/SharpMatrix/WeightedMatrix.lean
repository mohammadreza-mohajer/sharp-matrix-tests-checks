import SharpMatrix.WeightedDivision
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Matrix consequence of weighted division

Cayley-Hamilton is used here as an actual library theorem. The result
establishes the characteristic-p matrix step in Theorem 8.6. The spectral
classification and its application to p-adic representations are outside
this formalization and are identified explicitly in the scope document.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SharpMatrix

open Polynomial

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_nilpotent_of_weighted_annihilator
    (U : Matrix ι ι R) (π : R) (n k p : ℕ) (a : Fin n → R)
    (hp : 1 ≤ p) (hn : n ≤ 2 * k)
    (ha : WeightedCoefficients π n k a) (hπ : π ^ (p - 1) = 0)
    (hann : aeval U (monicPresentation n a) = 0) : U ^ (p * k) = 0 := by
  obtain ⟨Q, hQ⟩ := weighted_monic_division π n k p a hp hn ha hπ
  calc
    U ^ (p * k) = aeval U ((X : R[X]) ^ (p * k)) := by simp
    _ = aeval U (monicPresentation n a * Q) := by rw [hQ]
    _ = 0 := by rw [map_mul, hann, zero_mul]

theorem matrix_nilpotent_of_weighted_charpoly
    (U : Matrix ι ι R) (π : R) (n k p : ℕ) (a : Fin n → R)
    (hp : 1 ≤ p) (hn : n ≤ 2 * k)
    (ha : WeightedCoefficients π n k a) (hπ : π ^ (p - 1) = 0)
    (hchar : U.charpoly = monicPresentation n a) : U ^ (p * k) = 0 := by
  apply matrix_nilpotent_of_weighted_annihilator U π n k p a hp hn ha hπ
  rw [← hchar]
  exact Matrix.aeval_self_charpoly U

/-- The characteristic-p translation congruence in the ramified lower
bound, with every matrix and coefficient hypothesis displayed. -/
theorem matrix_translation_power (p j : ℕ) [Fact (Nat.Prime p)] [CharP R p]
    (U : Matrix ι ι R) (π : R) (n : ℕ) (a : Fin n → R)
    (hn : n ≤ 2 * p ^ j)
    (ha : WeightedCoefficients π n (p ^ j) a)
    (hπ : π ^ (p - 1) = 0)
    (hchar : (U - 1).charpoly = monicPresentation n a) :
    U ^ (p ^ (j + 1)) = 1 := by
  have hp : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hnil := matrix_nilpotent_of_weighted_charpoly
    (U - 1) π n (p ^ j) p a hp hn ha hπ hchar
  have hexp : p * p ^ j = p ^ (j + 1) := by rw [pow_succ, Nat.mul_comm]
  rw [hexp] at hnil
  have hpoly : (X - 1 : R[X]) ^ (p ^ (j + 1)) = X ^ (p ^ (j + 1)) - 1 := by
    simpa using (sub_pow_char_pow (X : R[X]) 1 (j + 1) (p := p))
  have hmatrix : (U - 1) ^ (p ^ (j + 1)) = U ^ (p ^ (j + 1)) - 1 := by
    simpa using congrArg (aeval U) hpoly
  exact sub_eq_zero.mp (hmatrix.symm.trans hnil)

end SharpMatrix
