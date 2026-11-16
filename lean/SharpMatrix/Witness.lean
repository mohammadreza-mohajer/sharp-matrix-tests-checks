import Mathlib.Tactic

/-!
# The detecting polynomial on the double cyclotomic block

The nilpotent binomial calculation in the proof of Theorem 8.6, with
arbitrary exponent. The Chinese-remainder and valuation identifications
in the paper are separate from these field-algebra identities.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SharpMatrix

section DualNumbers

variable {R : Type*} [CommRing R]

/-- The exact binomial formula at an arbitrary square-zero element. -/
theorem square_zero_power (ζ ε : R) (hε : ε ^ 2 = 0) (m : ℕ) :
    (ζ + ε) ^ (m + 1) = ζ ^ (m + 1) + (m + 1 : R) * ζ ^ m * ε := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih]
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      calc
        _ = ζ ^ m * ζ * ζ + ((m : R) + 1 + 1) * ζ ^ m * ζ * ε +
            ((m : R) + 1) * ζ ^ m * ε ^ 2 := by ring
        _ = _ := by rw [hε]; ring

end DualNumbers

section Witness

variable {R : Type*} [CommRing R]

/-- The closed witness formula in an arbitrary ring with square-zero
elements. The three inverse witnesses exist in the rational coefficient
algebra used in the paper. No field assumption is imposed on this ring. -/
theorem detecting_witness_double_root (ζ ζInv δ η ε : R) (m : ℕ)
    (hε : ε ^ 2 = 0) (hζInv : ζ * ζInv = 1)
    (hδ : (ζ - 1) * δ = 1) (hη : (m + 1 : R) * η = 1)
    (hpow : ζ ^ (m + 1) = 1) :
    η * ((ζ + ε) ^ (m + 1) - 1) = ζInv * δ * ε * (ζ + ε - 1) := by
  have hpred : ζ ^ m = ζInv := by
    calc
      ζ ^ m = ζ ^ m * (ζ * ζInv) := by rw [hζInv, mul_one]
      _ = (ζ ^ m * ζ) * ζInv := by ring
      _ = ζInv := by rw [← pow_succ, hpow, one_mul]
  rw [square_zero_power ζ ε hε m, hpow, hpred]
  calc
    η * (1 + (m + 1 : R) * ζInv * ε - 1) =
        ((m + 1 : R) * η) * ζInv * ε := by ring
    _ = ζInv * ε := by rw [hη, one_mul]
    _ = ζInv * (((ζ - 1) * δ) * ε) + ζInv * δ * ε ^ 2 := by
      rw [hδ, hε]
      ring
    _ = ζInv * δ * ε * (ζ + ε - 1) := by ring

/-- The same closed witness vanishes on the fixed root. -/
theorem detecting_witness_fixed_root (ζ coefficient : R) :
    coefficient * ((1 : R) - ζ) * ((1 : R) - 1) = 0 := by ring

end Witness

end SharpMatrix
