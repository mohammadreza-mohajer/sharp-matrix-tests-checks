import Mathlib.Tactic
import Mathlib.Data.Matrix.Block

/-!
# Sylvester basis change

The general rectangular-block calculation in Proposition 5.2. All blocks
have arbitrary finite sizes over a commutative ring.
-/

set_option autoImplicit false

namespace SharpMatrix

section Sylvester

variable {R : Type*} [CommRing R]
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def upperShear (X : Matrix n m R) : Matrix (n ⊕ m) (n ⊕ m) R :=
  Matrix.fromBlocks 1 X 0 1

theorem upper_shear_inverse (X : Matrix n m R) :
    upperShear X * upperShear (-X) = 1 ∧
      upperShear (-X) * upperShear X = 1 := by
  constructor <;>
    simp [upperShear, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem sylvester_block_change (A : Matrix n n R) (B : Matrix m m R)
    (C X : Matrix n m R) :
    upperShear X * Matrix.fromBlocks A C 0 B * upperShear (-X) =
      Matrix.fromBlocks A (C - (A * X - X * B)) 0 B := by
  simp [upperShear, Matrix.fromBlocks_multiply, Matrix.mul_neg,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

theorem sylvester_splits_extension (A : Matrix n n R) (B : Matrix m m R)
    (C X : Matrix n m R) (h : A * X - X * B = C) :
    upperShear X * Matrix.fromBlocks A C 0 B * upperShear (-X) =
      Matrix.fromBlocks A 0 0 B := by
  rw [sylvester_block_change, h, sub_self]

end Sylvester

end SharpMatrix
