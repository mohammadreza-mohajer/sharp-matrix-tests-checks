#!/usr/bin/env python3
"""Exact symbolic checks of the rank-three lattice and period formulas."""

import hashlib
import json
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

import sympy as sp
import mpmath

from verification_context import paper_reference

ROOT = Path(__file__).resolve().parent
COUNTS = {}
z, s, a, b, eta, alpha, t, u = sp.symbols("z s a b eta alpha t u", nonzero=True)
relation = (z - s) ** 2 * (z - 1)
C = sp.Matrix([[1, s, s ** 2], [0, 1, 2 * s], [1, 1, 1]])
Cinv = C.inv()


def check(condition, category):
    if not condition:
        raise AssertionError(category)
    COUNTS[category] = COUNTS.get(category, 0) + 1


def equal(left, right, p=None):
    difference = sp.cancel(left - right)
    if p is None:
        return difference == 0
    numerator = sp.fraction(difference)[0]
    return sp.rem(numerator, sp.cyclotomic_poly(p, s), s) == 0


def check_matrix(left, right, category, p=None):
    check(left.shape == right.shape, category + "_shape")
    for i in range(left.rows):
        for j in range(left.cols):
            check(equal(left[i, j], right[i, j], p), category)


def reduce_z(polynomial):
    return sp.rem(sp.expand(polynomial), relation, z)


def multiplication(polynomial):
    return sp.Matrix(3, 3, lambda i, j: sp.expand(reduce_z(polynomial * z ** j)).coeff(z, i))


def theta(parameter):
    image = z + (parameter - 1) / (s - 1) * (z - s) * (z - 1)
    return sp.Matrix(3, 3, lambda i, j: sp.expand(reduce_z(image ** j)).coeff(z, i))


def cyclotomic_normal_form(expression, p):
    numerator, denominator = sp.fraction(sp.cancel(expression))
    cyclotomic = sp.cyclotomic_poly(p, s)
    inverse = sp.invert(denominator, cyclotomic, s)
    return sp.Poly(sp.rem(numerator * inverse, cyclotomic, s), s)


def integral_coefficients(expression, p):
    for coefficient in cyclotomic_normal_form(expression, p).all_coeffs():
        rational = Fraction(int(sp.numer(coefficient)), int(sp.denom(coefficient)))
        if rational.denominator % p == 0:
            return False
    return True


def run_checks():
    H = sp.Matrix([[0, 0, 1], [0, 1, 2 * s + 1],
                   [1, 2 * s + 1, (2 * s + 1) ** 2 - (s ** 2 + 2 * s)]])
    computed = sp.Matrix(3, 3, lambda i, j: sp.expand(reduce_z(z ** (i + j))).coeff(z, 2))
    check_matrix(computed, H, "coefficient_gram_matrix")
    check(equal(H.det(), -1), "perfect_integral_gram_determinant")
    check(equal(C.det(), (1 - s) ** 2), "exact_hermite_index")
    check(equal(C[:2, :2].det(), 1), "unit_minor_hermite_cokernel")
    v0, v1, w = sp.symbols("v0 v1 w")
    coefficients = Cinv * sp.Matrix([v0, v1, w])
    check(equal(coefficients[2], (w - v0 - (1 - s) * v1) / (1 - s) ** 2),
          "exact_lattice_congruence_functional")
    check_matrix(C * theta(a) * Cinv, sp.diag(1, a, 1), "dilation_hermite_coordinates")
    check_matrix(theta(a) * theta(b), theta(a * b), "dilation_automorphism_identity")

    for p in (3, 5, 7):
        tau1 = multiplication(z) * theta(1 + p)
        tau2 = multiplication(z ** 2) * theta(1 + 2 * p)
        product = multiplication(z ** (1 + 2 * (1 + p))) * theta((1 + p) * (1 + 2 * p))
        check_matrix(tau1 * tau2, product, "integral_affine_representation_identity", p)
        for entry in tau1:
            check(integral_coefficients(entry, p), "cyclotomic_integral_matrix_entries")
        expected = sp.Matrix([[s, 0, 0], [1, (1 + p) * s, 0], [0, 0, 1]])
        check_matrix(C * tau1 * Cinv, expected, "affine_block_matrix", p)
        witness = reduce_z((z ** p - 1) / p)
        proposed = s ** (-1) / (s - 1) * (z - s) * (z - 1)
        for i in range(3):
            check(equal(sp.expand(witness).coeff(z, i), sp.expand(proposed).coeff(z, i), p),
                  "ramified_detecting_polynomial")
        check(not integral_coefficients(s ** (-1) / (s - 1), p), "nonintegral_detecting_entry")
        check(integral_coefficients(s ** (-1), p), "clearing_detecting_denominator")

    block_action = sp.Matrix([[eta, 0, 0], [eta * b / s, eta * a, 0], [0, 0, 1]])
    block_period = sp.Matrix([[1 / alpha, 0, 0], [-u / (alpha * s * t), 1 / (alpha * t), 0], [0, 0, 1]])
    transformed_period = block_period.xreplace({alpha: eta * alpha, t: a * t, u: u + b * t})
    check_matrix(block_action * transformed_period, block_period, "galois_invariance_block_period")
    action = Cinv * block_action * C
    period = Cinv * block_period
    check_matrix(action * Cinv * transformed_period, period, "galois_invariance_integral_basis_period")
    check(equal(period.det(), 1 / ((1 - s) ** 2 * alpha ** 2 * t)), "period_determinant")
    dual_period = sp.simplify(period.inv().T / t)
    transformed_dual = dual_period.xreplace({alpha: eta * alpha, t: a * t, u: u + b * t})
    check_matrix(a * action.inv().T * transformed_dual, dual_period, "galois_invariance_tate_dual_period")
    check_matrix(period.T * dual_period, sp.eye(3) / t, "identity_tate_evaluation_pairing")


def main():
    started = datetime.now(timezone.utc).isoformat()
    try:
        run_checks()
        status, error = "passed", None
    except Exception as exception:
        status, error = "failed", repr(exception)
    result = {
        "status": status, "started_utc": started, "finished_utc": datetime.now(timezone.utc).isoformat(),
        "method": "Exact polynomial and rational-function arithmetic in SymPy",
        "sympy_version": sp.__version__, "mpmath_version": mpmath.__version__, "checks_by_category": COUNTS, "check_count": sum(COUNTS.values()),
        "paper_reference": paper_reference(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Checks displayed algebraic identities. Does not formalize period rings, convergence, or arithmetic regulator construction.",
        "error": error,
    }
    (ROOT / "period_check_results.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": status, "check_count": sum(COUNTS.values()), "categories": COUNTS, "error": error}))
    return 0 if status == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
