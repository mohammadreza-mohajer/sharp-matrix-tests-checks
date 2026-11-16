#!/usr/bin/env python3
"""Exact finite checks for the affine-moment research draft; not a proof checker."""

import hashlib
import itertools
import json
import math
from datetime import datetime, timezone
from fractions import Fraction as Q
from pathlib import Path

from verification_context import paper_reference

ROOT = Path(__file__).resolve().parent
COUNTS = {}


def check(condition, category):
    if not condition:
        raise AssertionError(category)
    COUNTS[category] = COUNTS.get(category, 0) + 1


def choose(x, n):
    value = Q(1)
    for k in range(n):
        value *= Q(x - k, k + 1)
    return value


def basis_value(point, index):
    value = Q(1)
    for x, n in zip(point, index):
        value *= choose(x, n)
    return value


def indices(dimension, degree):
    return sorted(
        (n for n in itertools.product(range(degree + 1), repeat=dimension) if sum(n) <= degree),
        key=lambda n: (sum(n), tuple(-k for k in n)),
    )


def product(g, h, q):
    return tuple(g[i] + (1 + q * g[-1]) * h[i] for i in range(len(g) - 1)) + (
        g[-1] + h[-1] + q * g[-1] * h[-1],
    )


def difference(function, index):
    total = Q(0)
    for point in itertools.product(*(range(n + 1) for n in index)):
        weight = (-1) ** (sum(index) - sum(point))
        for n, k in zip(index, point):
            weight *= math.comb(n, k)
        total += weight * function(point)
    return total


def translation(g, q, degree, side="right"):
    basis = indices(len(g), degree)
    columns = []
    for beta in basis:
        def translated(h):
            point = product(h, g, q) if side == "right" else product(g, h, q)
            return basis_value(point, beta)
        columns.append([difference(translated, alpha) for alpha in basis])
    return [[columns[j][i] for j in range(len(basis))] for i in range(len(basis))]


def matmul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), Q(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def inverse(a):
    n = len(a)
    work = [[Q(x) for x in row] + [Q(i == j) for j in range(n)] for i, row in enumerate(a)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if work[i][j])
        work[j], work[pivot] = work[pivot], work[j]
        scale = work[j][j]
        work[j] = [x / scale for x in work[j]]
        for i in range(n):
            if i != j:
                scale = work[i][j]
                work[i] = [x - scale * y for x, y in zip(work[i], work[j])]
    return [row[n:] for row in work]


def matrix_power(a, exponent):
    result = [[Q(i == j) for j in range(len(a))] for i in range(len(a))]
    while exponent:
        if exponent % 2:
            result = matmul(result, a)
        a = matmul(a, a)
        exponent //= 2
    return result


def optimal_representation(x, u, q, degree):
    dilation = Q(1 + q * u)
    return [[difference(lambda point: choose((Q(point[0]) - x) / dilation, j), (i,))
             for j in range(degree + 1)] for i in range(degree + 1)]


def determinant(a):
    if not a:
        return Q(1)
    return sum(((-1) ** j * a[0][j] * determinant([row[:j] + row[j + 1:] for row in a[1:]])
                for j in range(len(a))), Q(0))


def valuation(value, p):
    value = Q(value)
    if not value:
        return math.inf
    numerator, denominator = abs(value.numerator), value.denominator
    exponent = 0
    while numerator % p == 0:
        numerator //= p
        exponent += 1
    while denominator % p == 0:
        denominator //= p
        exponent -= 1
    return exponent


def signed_stirling(n):
    coefficients = [1]
    for k in range(n):
        new = [0] * (len(coefficients) + 1)
        for i, value in enumerate(coefficients):
            new[i] -= k * value
            new[i + 1] += value
        coefficients = new
    return coefficients


def run_checks():
    for q in (3, 5, 9):
        for dimension in (2, 3):
            g = tuple(range(1, dimension + 1))
            h = tuple(-1 if i % 2 == 0 else 1 for i in range(dimension))
            for degree in range(4):
                rg = translation(g, q, degree)
                rh = translation(h, q, degree)
                rgh = translation(product(g, h, q), q, degree)
                lg = translation(g, q, degree, "left")
                check(matmul(rg, rh) == rgh, "translation_representation_identity")
                check(matmul(lg, rh) == matmul(rh, lg), "left_right_commutation")
                check(all(x.denominator == 1 for row in rg for x in row), "integral_translation_matrices")
    check(translation((2, 1), 3, 1) == [[1, 2, 1], [0, 1, 0], [0, 6, 4]], "displayed_degree_one_matrix")

    for p, c in ((3, 1), (3, 2), (5, 1)):
        q = p ** c
        g, h = (2, 1), (-1, -1)
        gh = product(g, h, q)
        for degree in range(6):
            sg = optimal_representation(*g, q, degree)
            sh = optimal_representation(*h, q, degree)
            check(matmul(sg, sh) == optimal_representation(*gh, q, degree), "optimal_representation_identity")
            check(all(valuation(entry, p) >= 0 for row in sg for entry in row), "optimal_representation_integral_lattice")
    for p in (3, 5):
        for n in range(1, 10):
            k = 0
            while p ** k < n:
                k += 1
            unipotent = [[Q(i == j or j == i + 1) for j in range(n)] for i in range(n)]
            for d in range(k, k + 2):
                power = matrix_power(unipotent, p ** d)
                check(all(valuation(power[i][j] - Q(i == j), p) >= d - k + 1
                          for i in range(n) for j in range(n)), "matrix_power_dimension_bound")

    q = 3
    for nu in indices(2, 2):
        basis = indices(2, sum(nu))
        coefficients = {}
        for alpha in basis:
            for beta in basis:
                def value(point):
                    return basis_value(product(point[:2], point[2:], q), nu)
                coefficient = difference(value, alpha + beta)
                check(coefficient.denominator == 1, "integral_coproduct_coefficients")
                if coefficient:
                    coefficients[alpha, beta] = coefficient
        for g, h in [((1, 2), (2, 1)), ((-1, 1), (3, -1))]:
            reconstructed = sum((value * basis_value(g, alpha) * basis_value(h, beta)
                                 for (alpha, beta), value in coefficients.items()), Q(0))
            check(reconstructed == basis_value(product(g, h, q), nu), "coproduct_reconstruction")

    atoms = [((0, 0), Q(-1, 9)), ((3, 1), Q(2, 9)), ((-1, 2), Q(1, 3))]
    for nu in indices(2, 7):
        stirling = [signed_stirling(n) for n in nu]
        converted = Q(0)
        for kappa in itertools.product(*(range(n + 1) for n in nu)):
            ordinary = sum((weight * point[0] ** kappa[0] * point[1] ** kappa[1] for point, weight in atoms), Q(0))
            converted += stirling[0][kappa[0]] * stirling[1][kappa[1]] * ordinary
        converted /= math.factorial(nu[0]) * math.factorial(nu[1])
        direct = sum((weight * basis_value(point, nu) for point, weight in atoms), Q(0))
        check(converted == direct, "ordinary_to_binomial_moments")

    for p in (3, 5, 7):
        for a in range(1, 5):
            for s in range(1, 4):
                sylvester = [[Q(-p ** s if i == j else 1 if j == i + 1 else 0)
                              for j in range(a)] for i in range(a)]
                inv = inverse(sylvester)
                vector = [row[-1] for row in inv]
                expected = [Q(-1, p ** (s * (a - i))) for i in range(a)]
                check(vector == expected, "jordan_inverse_formula")
                check(determinant(sylvester) == (-p ** s) ** a, "jordan_resultant")
                minor = [row[1:] for row in sylvester[:-1]]
                check(determinant(minor) == 1, "unit_minor_for_smith_cokernel")
                check(min(valuation(x, p) for x in vector) == -a * s, "optimal_jordan_denominator")
                check(vector[0] == Q(-1, p ** (a * s)), "linking_generator_value")

    for p, max_d in ((3, 5), (5, 3), (7, 2)):
        for d in range(1, max_d + 1):
            for n in range(1, p ** d + 1):
                check(valuation(math.comb(p ** d, n), p) == d - valuation(n, p), "binomial_valuation_formula")
                check(valuation(choose(-p ** d, n), p) == d - valuation(n, p), "negative_binomial_valuation_formula")

    table = []
    for a, s, d in [(1, 1, 1), (1, 1, 2), (2, 1, 1), (2, 1, 2), (2, 1, 3), (3, 1, 3), (2, 2, 4)]:
        e = a * s
        values = [Q(-math.comb(3 ** d, n), 3 ** e) for n in range(1, 3 ** d + 1)]
        first_bad = next(n for n, value in enumerate(values, 1) if valuation(value, 3) < 0)
        predicted = 3 ** max(0, d - e + 1)
        check(first_bad == predicted, "displayed_detection_table")
        check(min(valuation(value, 3) for value in values) == -e, "table_optimal_denominators")
        witness = Q(-1, 3 ** e) * choose(-3 ** d, predicted)
        check(valuation(witness, 3) < 0, "optimal_dimension_detecting_entry")
        if predicted <= 9:
            matrix = optimal_representation(3 ** d, 0, 3, predicted)
            check(valuation(matrix[0][-1] / 3 ** e, 3) < 0, "optimal_dimension_full_matrix")
        table.append({"p": 3, "c": 1, "a": a, "s": s, "d": d, "denominator_exponent": e,
                      "denominator": 3 ** e, "first_nonintegral_degree": first_bad,
                      "minimum_detecting_matrix_dimension": first_bad + 1})
    for p in (3, 5):
        for a, s, d in itertools.product(range(1, 4), range(1, 3), range(1, 4)):
            e = a * s
            first_bad = next(n for n in range(1, p ** d + 1)
                             if valuation(Q(math.comb(p ** d, n), p ** e), p) < 0)
            check(first_bad == p ** max(0, d - e + 1), "delayed_detection_family")
            if d >= e:
                check(all(valuation(Q(p ** (d * k), p ** e), p) >= 0 for k in range(1, 13)),
                      "integral_ordinary_moments_samples")

    for p, c, m in itertools.product((3, 5), (1, 2), range(1, 4)):
        q = p ** c
        polynomial = [0] + [math.comb(q, n) for n in range(1, q + 1)]
        power = [1]
        for _ in range(m):
            new = [0] * (len(power) + q)
            for i, x in enumerate(power):
                for j, y in enumerate(polynomial):
                    new[i + j] += x * y
            power = new
        first_bad = next(n for n, value in enumerate(power) if value % p)
        check(first_bad == m * q, "convolution_power_detection")
        check(power[-1] == 1, "convolution_power_optimal_denominator")

    return table


def main():
    started = datetime.now(timezone.utc).isoformat()
    try:
        table = run_checks()
        status, error = "passed", None
    except Exception as exception:
        table = []
        status, error = "failed", repr(exception)
    record = {
        "status": status, "started_utc": started, "finished_utc": datetime.now(timezone.utc).isoformat(),
        "method": "Python standard library; exact integers and rational arithmetic",
        "checks_by_category": COUNTS, "check_count": sum(COUNTS.values()), "example_table": table,
        "paper_reference": paper_reference(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Finite examples only. No formal proof checking, analytic growth verification, or novelty certification.",
        "error": error,
    }
    (ROOT / "finite_check_results.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": status, "check_count": sum(COUNTS.values()), "categories": COUNTS, "error": error}))
    return 0 if status == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
